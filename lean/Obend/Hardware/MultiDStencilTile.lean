module
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Hardware.Gpu.StencilTile
public import Obend.Hardware.HDL
public import Obend.Core.RangeSafe
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.Gpu.SoacOptimize
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Core.RangeSafe

/-!
# Multi-Dimensional Stencil Tiling, Futamura Flux Specialization & Systolic Lowering (`Obend.Hardware.MultiDStencilTile`)

Compile-time hardware/accelerator lowering engine for `Obend.Analysis.NonlinearMultiDPde`:
1. **Futamura Flux Specialization & CSE SSA DAG (`specializeFluxExpr`, `compileFluxSsaDag`)**:
   - Eliminates `0 * x`, `1 * x`, `-1 * x`, `x + 0`, `x - 0`, `--x`, folds rational constants and known
     equation parameters, and deduplicates shared subexpressions (e.g. `ρ⁻¹`, kinetic/magnetic energy)
     into a verified topological SSA DAG with proved FLOP reduction (`dagFlops_le_naive_sum`).
2. **Arbitrary-Dimension `D`-D Brick Halo Tiling (`evalMultiDBrickTiled`)**:
   - Generalizes 1D scratchpad halo tiling (`Gpu.StencilTile`) to `D`-dimensional bricks
     `(B_0 × … × B_{D-1})` including non-multiple boundary tail bricks and 3-phase barrier discipline,
     proving `multiDBrickTiled_eq_global_sweep` and `multiDBrickHbmReads_lt_global`.
3. **Single-Pass Vertical SOAC Fusion & Q32 Systolic `HDL.RtlModule` Generation**:
   - Lowers `D`-D stencils through `cseProgram`, `dceProgram`, and `fuseVertical ∘ liftArraySource`
     (`compileMultiDSweepFused_sound`), and lowers specialized `FluxSsaDag`s to `RangeSafe`-checked
     Q32.32 fixed-point `HDL.RtlModule` datapaths (`emitSystolicFluxCellRtlModule_ok`).
-/

public section
namespace Obend.Hardware.MultiDStencilTile
open Obend.Core
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.Gpu.ArraySource
open Obend.Hardware.Gpu.SoacOptimize
open Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.HDL
set_option autoImplicit false

/-! ## 1. Compile-Time Futamura Specialization, Zero-Elimination & CSE SSA DAG -/

/-- Arithmetic operation count of a `FluxExpr` tree (leaves cost `0`, unary/binary ops cost `1`). -/
@[expose] def fluxExprFlops : FluxExpr → Nat
  | .const _ | .var _ | .param _ => 0
  | .neg a | .invSafe a => fluxExprFlops a + 1
  | .add a b | .sub a b | .mul a b => fluxExprFlops a + fluxExprFlops b + 1

def simpNeg : FluxExpr → FluxExpr
  | .const q => .const (-q)
  | .neg x => x
  | x => .neg x

def simpAdd : FluxExpr → FluxExpr → FluxExpr
  | .const a, .const b => .const (a + b)
  | .const q, b => if q == 0 then b else .add (.const q) b
  | a, .const q => if q == 0 then a else .add a (.const q)
  | a, b => .add a b

def simpSub : FluxExpr → FluxExpr → FluxExpr
  | .const a, .const b => .const (a - b)
  | a, .const q => if q == 0 then a else .sub a (.const q)
  | .const q, b => if q == 0 then simpNeg b else .sub (.const q) b
  | a, b => if a == b then .const 0 else .sub a b

def simpMul : FluxExpr → FluxExpr → FluxExpr
  | .const a, .const b => .const (a * b)
  | .const q, b =>
    if q == 0 then .const 0
    else if q == 1 then b
    else if q == -1 then simpNeg b
    else .mul (.const q) b
  | a, .const q =>
    if q == 0 then .const 0
    else if q == 1 then a
    else if q == -1 then simpNeg a
    else .mul a (.const q)
  | a, b => .mul a b

def simpInv : FluxExpr → FluxExpr
  | .const q => .const ((1 : Rat) / q)
  | d => .invSafe d

/-- Futamura partial evaluator & zero-eliminator for `FluxExpr`. When `pOpt = some pEnv`, known
equation parameters (`γ`, `c_h`, `q`, `m`) are specialized to constants before algebraic pruning. -/
@[expose] def specializeFluxExpr (pOpt : Option (Nat → Rat)) : FluxExpr → FluxExpr
  | .const q => .const q
  | .var i => .var i
  | .param p => match pOpt with | some pEnv => .const (pEnv p) | none => .param p
  | .neg a => simpNeg (specializeFluxExpr pOpt a)
  | .add a b => simpAdd (specializeFluxExpr pOpt a) (specializeFluxExpr pOpt b)
  | .sub a b => simpSub (specializeFluxExpr pOpt a) (specializeFluxExpr pOpt b)
  | .mul a b => simpMul (specializeFluxExpr pOpt a) (specializeFluxExpr pOpt b)
  | .invSafe d => simpInv (specializeFluxExpr pOpt d)

theorem simpNeg_sound (a : FluxExpr) (env : FluxEnv) :
    evalFlux (simpNeg a) env = -(evalFlux a env) := by
  cases a <;> simp only [simpNeg, evalFlux] <;> grind

theorem simpAdd_sound (a b : FluxExpr) (env : FluxEnv) :
    evalFlux (simpAdd a b) env = evalFlux a env + evalFlux b env := by
  cases a <;> cases b <;> simp only [simpAdd, evalFlux] <;>
    (try split) <;> simp_all only [beq_iff_eq, evalFlux] <;> grind

theorem simpSub_sound (a b : FluxExpr) (env : FluxEnv) :
    evalFlux (simpSub a b) env = evalFlux a env - evalFlux b env := by
  cases a <;> cases b <;> simp only [simpSub, evalFlux] <;>
    (try split) <;> simp_all only [beq_iff_eq, evalFlux, simpNeg_sound] <;> grind

theorem simpMul_sound (a b : FluxExpr) (env : FluxEnv) :
    evalFlux (simpMul a b) env = evalFlux a env * evalFlux b env := by
  cases a <;> cases b <;> simp only [simpMul, evalFlux] <;>
    (repeat' split) <;> simp_all only [beq_iff_eq, evalFlux, simpNeg_sound] <;> grind

theorem simpInv_sound (d : FluxExpr) (env : FluxEnv) :
    evalFlux (simpInv d) env = (1 : Rat) / evalFlux d env := by
  cases d <;> rfl

/-- **Specialization Soundness (`specializeFluxExpr_sound`)**:
Both parameter-agnostic (`none`) and parameter-specialized (`some env.params`) specialization
preserve exact `evalFlux` semantics at every environment. -/
theorem specializeFluxExpr_sound (pOpt : Option (Nat → Rat)) (e : FluxExpr) (env : FluxEnv)
    (hParam : match pOpt with | none => True | some pEnv => ∀ p, pEnv p = env.params p) :
    evalFlux (specializeFluxExpr pOpt e) env = evalFlux e env := by
  induction e with
  | const _ | var _ => rfl
  | param p => cases pOpt with | none => rfl | some pEnv => simp [specializeFluxExpr, evalFlux, hParam p]
  | neg a iha => simp [specializeFluxExpr, evalFlux, simpNeg_sound, iha]
  | add a b iha ihb => simp [specializeFluxExpr, evalFlux, simpAdd_sound, iha, ihb]
  | sub a b iha ihb => simp [specializeFluxExpr, evalFlux, simpSub_sound, iha, ihb]
  | mul a b iha ihb => simp [specializeFluxExpr, evalFlux, simpMul_sound, iha, ihb]
  | invSafe d ihd => simp [specializeFluxExpr, evalFlux, simpInv_sound, ihd]

theorem simpNeg_flops_le (a : FluxExpr) : fluxExprFlops (simpNeg a) ≤ fluxExprFlops a + 1 := by
  cases a <;> simp [simpNeg, fluxExprFlops] <;> omega

theorem simpAdd_flops_le (a b : FluxExpr) :
    fluxExprFlops (simpAdd a b) ≤ fluxExprFlops a + fluxExprFlops b + 1 := by
  cases a <;> cases b <;> simp only [simpAdd] <;> (try split) <;> simp [fluxExprFlops] <;> omega

theorem simpSub_flops_le (a b : FluxExpr) :
    fluxExprFlops (simpSub a b) ≤ fluxExprFlops a + fluxExprFlops b + 1 := by
  cases a <;> cases b <;> simp only [simpSub] <;> (try split) <;> simp [fluxExprFlops, simpNeg] <;> omega

theorem simpMul_flops_le (a b : FluxExpr) :
    fluxExprFlops (simpMul a b) ≤ fluxExprFlops a + fluxExprFlops b + 1 := by
  cases a <;> cases b <;> simp only [simpMul] <;> (repeat' split) <;> simp [fluxExprFlops, simpNeg] <;> omega

theorem simpInv_flops_le (d : FluxExpr) : fluxExprFlops (simpInv d) ≤ fluxExprFlops d + 1 := by
  cases d <;> simp [simpInv, fluxExprFlops]

/-- **Monotone FLOP Reduction (`specializedFlops_le_naive`)**:
Futamura constant-folding and zero/unit pruning never increase arithmetic operation count. -/
theorem specializedFlops_le_naive (pOpt : Option (Nat → Rat)) (e : FluxExpr) :
    fluxExprFlops (specializeFluxExpr pOpt e) ≤ fluxExprFlops e := by
  induction e with
  | const _ | var _ => exact Nat.le_refl _
  | param _ => cases pOpt <;> simp [specializeFluxExpr, fluxExprFlops]
  | neg a iha => exact Nat.le_trans (simpNeg_flops_le _) (by simp [fluxExprFlops]; omega)
  | add a b iha ihb => exact Nat.le_trans (simpAdd_flops_le _ _) (by simp [fluxExprFlops]; omega)
  | sub a b iha ihb => exact Nat.le_trans (simpSub_flops_le _ _) (by simp [fluxExprFlops]; omega)
  | mul a b iha ihb => exact Nat.le_trans (simpMul_flops_le _ _) (by simp [fluxExprFlops]; omega)
  | invSafe d ihd => exact Nat.le_trans (simpInv_flops_le _) (by simp [fluxExprFlops]; omega)

/-- Topological SSA node for multi-output flux and Jacobian evaluation with CSE sharing. -/
inductive FluxSsaNode where
  | const (q : Rat) | var (idx : Nat) | param (idx : Nat) | neg (a : Nat)
  | add (a b : Nat) | sub (a b : Nat) | mul (a b : Nat) | invSafe (d : Nat)
  deriving DecidableEq, Repr

structure FluxSsaDag where
  nodes : List FluxSsaNode
  roots : List Nat
  deriving DecidableEq, Repr

def ssaNodeFlop : FluxSsaNode → Nat
  | .const _ | .var _ | .param _ => 0
  | _ => 1

def fluxSsaFlops (dag : FluxSsaDag) : Nat := (dag.nodes.map ssaNodeFlop).sum

def checkSsaNodeBound (bound : Nat) : FluxSsaNode → Bool
  | .const _ | .var _ | .param _ => true
  | .neg a | .invSafe a => decide (a < bound)
  | .add a b | .sub a b | .mul a b => decide (a < bound) && decide (b < bound)

def checkNodesTopological : Nat → List FluxSsaNode → Bool
  | _, [] => true
  | idx, n :: rest => checkSsaNodeBound idx n && checkNodesTopological (idx + 1) rest

def checkFluxSsaDag (dag : FluxSsaDag) : Bool :=
  checkNodesTopological 0 dag.nodes && dag.roots.all (fun r => decide (r < dag.nodes.length))

def evalSsaNodeStep (env : FluxEnv) (vals : List Rat) : FluxSsaNode → Rat
  | .const q => q
  | .var i => env.state i
  | .param p => env.params p
  | .neg a => -(getOr vals a 0)
  | .add a b => getOr vals a 0 + getOr vals b 0
  | .sub a b => getOr vals a 0 - getOr vals b 0
  | .mul a b => getOr vals a 0 * getOr vals b 0
  | .invSafe d => (1 : Rat) / getOr vals d 0

def evalSsaNodes (env : FluxEnv) : List FluxSsaNode → List Rat → List Rat
  | [], acc => acc
  | n :: rest, acc => evalSsaNodes env rest (acc ++ [evalSsaNodeStep env acc n])

def evalFluxSsaDag (dag : FluxSsaDag) (env : FluxEnv) : List Rat :=
  let vals := evalSsaNodes env dag.nodes []
  dag.roots.map fun r => getOr vals r 0

def findSsaNodeIdx : List FluxSsaNode → FluxSsaNode → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, target, k => if x == target then some k else findSsaNodeIdx xs target (k + 1)

def internSsaNode (nodes : List FluxSsaNode) (n : FluxSsaNode) : List FluxSsaNode × Nat :=
  match findSsaNodeIdx nodes n 0 with
  | some idx => (nodes, idx)
  | none => (nodes ++ [n], nodes.length)

def compileExprSsa : FluxExpr → List FluxSsaNode → List FluxSsaNode × Nat
  | .const q, ns => internSsaNode ns (.const q)
  | .var i, ns => internSsaNode ns (.var i)
  | .param p, ns => internSsaNode ns (.param p)
  | .neg a, ns => let (ns1, ia) := compileExprSsa a ns; internSsaNode ns1 (.neg ia)
  | .add a b, ns =>
    let (ns1, ia) := compileExprSsa a ns
    let (ns2, ib) := compileExprSsa b ns1
    internSsaNode ns2 (.add ia ib)
  | .sub a b, ns =>
    let (ns1, ia) := compileExprSsa a ns
    let (ns2, ib) := compileExprSsa b ns1
    internSsaNode ns2 (.sub ia ib)
  | .mul a b, ns =>
    let (ns1, ia) := compileExprSsa a ns
    let (ns2, ib) := compileExprSsa b ns1
    internSsaNode ns2 (.mul ia ib)
  | .invSafe d, ns => let (ns1, id0) := compileExprSsa d ns; internSsaNode ns1 (.invSafe id0)

def compileExprListSsa : List FluxExpr → List FluxSsaNode → List FluxSsaNode × List Nat
  | [], ns => (ns, [])
  | e :: es, ns =>
    let (ns1, r) := compileExprSsa e ns
    let (ns2, rs) := compileExprListSsa es ns1
    (ns2, r :: rs)

/-- Compile a vector of `FluxExpr`s (with Futamura specialization + CSE) into a `FluxSsaDag`. -/
def compileFluxSsaDag (pOpt : Option (Nat → Rat)) (exprs : List FluxExpr) : FluxSsaDag :=
  let specExprs := exprs.map (specializeFluxExpr pOpt)
  let (nodes, roots) := compileExprListSsa specExprs []
  { nodes, roots }

theorem getOr_append_left {α : Type} (xs ys : List α) (i : Nat) (d : α) (hi : i < xs.length) :
    getOr (xs ++ ys) i d = getOr xs i d := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons _ xs ih => cases i with | zero => rfl | succ i => exact ih i (by simpa using hi)

theorem getOr_snoc_self {α : Type} (xs : List α) (v d : α) :
    getOr (xs ++ [v]) xs.length d = v := by
  induction xs with | nil => rfl | cons _ xs ih => exact ih

theorem evalSsaNodes_length (env : FluxEnv) (ns : List FluxSsaNode) (acc : List Rat) :
    (evalSsaNodes env ns acc).length = acc.length + ns.length := by
  induction ns generalizing acc with
  | nil => simp [evalSsaNodes]
  | cons n rest ih => simp only [evalSsaNodes, ih, List.length_append, List.length_cons, List.length_nil]; omega

theorem evalSsaNodes_prefix_getOr (env : FluxEnv) (ns : List FluxSsaNode) (acc : List Rat)
    (i : Nat) (hi : i < acc.length) :
    getOr (evalSsaNodes env ns acc) i 0 = getOr acc i 0 := by
  induction ns generalizing acc with
  | nil => rfl
  | cons n rest ih =>
    simp only [evalSsaNodes]
    rw [ih (acc ++ [evalSsaNodeStep env acc n]) (by simp; omega)]
    exact getOr_append_left acc _ i 0 hi

theorem evalSsaNodeStep_ext (env : FluxEnv) (v1 v2 : List Rat) (n : FluxSsaNode) (bound : Nat)
    (hB : checkSsaNodeBound bound n = true)
    (hEq : ∀ k < bound, getOr v1 k 0 = getOr v2 k 0) :
    evalSsaNodeStep env v1 n = evalSsaNodeStep env v2 n := by
  cases n <;> simp only [checkSsaNodeBound, Bool.and_eq_true, decide_eq_true_eq] at hB <;>
    simp only [evalSsaNodeStep]
  · rw [hEq _ hB]
  · rw [hEq _ hB.1, hEq _ hB.2]
  · rw [hEq _ hB.1, hEq _ hB.2]
  · rw [hEq _ hB.1, hEq _ hB.2]
  · rw [hEq _ hB]

theorem evalSsaNodes_at_index (env : FluxEnv) (ns : List FluxSsaNode) (acc : List Rat)
    (hTopo : checkNodesTopological acc.length ns = true) (j : Nat) (hj : j < ns.length) :
    let full := evalSsaNodes env ns acc
    checkSsaNodeBound (acc.length + j) (getOr ns j (.const 0)) = true ∧
    getOr full (acc.length + j) 0 = evalSsaNodeStep env full (getOr ns j (.const 0)) := by
  induction ns generalizing acc j with
  | nil => simp at hj
  | cons n rest ih =>
    simp only [checkNodesTopological, Bool.and_eq_true] at hTopo
    cases j with
    | zero =>
      simp only [Nat.add_zero, getOr]
      refine ⟨hTopo.1, ?_⟩
      simp only [evalSsaNodes]
      have hAt : getOr (evalSsaNodes env rest (acc ++ [evalSsaNodeStep env acc n])) acc.length 0 =
          evalSsaNodeStep env acc n := by
        rw [evalSsaNodes_prefix_getOr env rest (acc ++ [evalSsaNodeStep env acc n]) acc.length (by simp),
            getOr_snoc_self]
      rw [hAt]
      refine evalSsaNodeStep_ext env acc _ n acc.length hTopo.1 fun k hk => ?_
      rw [evalSsaNodes_prefix_getOr env rest (acc ++ [evalSsaNodeStep env acc n]) k (by simp; omega),
          getOr_append_left acc _ k 0 hk]
    | succ j' =>
      have hRestTopo : checkNodesTopological (acc ++ [evalSsaNodeStep env acc n]).length rest = true := by
        simpa using hTopo.2
      have hSub := ih (acc ++ [evalSsaNodeStep env acc n]) hRestTopo j' (by simpa using hj)
      have hIdx : (acc ++ [evalSsaNodeStep env acc n]).length + j' = acc.length + (j' + 1) := by simp; omega
      rw [hIdx] at hSub
      exact hSub

theorem findSsaNodeIdx_spec (xs : List FluxSsaNode) (target : FluxSsaNode) (k idx : Nat)
    (h : findSsaNodeIdx xs target k = some idx) :
    ∃ off, off < xs.length ∧ idx = k + off ∧ getOr xs off (.const 0) = target := by
  induction xs generalizing k with
  | nil => simp [findSsaNodeIdx] at h
  | cons x rest ih =>
    simp only [findSsaNodeIdx] at h
    by_cases hx : x == target
    · simp only [hx, ↓reduceIte, Option.some.injEq] at h
      exact ⟨0, by simp, by omega, by simpa [getOr] using of_decide_eq_true hx⟩
    · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨off, hoff, hidx, hget⟩ := ih (k + 1) h
      exact ⟨off + 1, by simp; omega, by omega, hget⟩

theorem checkNodesTopological_append (k : Nat) (xs ys : List FluxSsaNode) :
    checkNodesTopological k (xs ++ ys) =
      (checkNodesTopological k xs && checkNodesTopological (k + xs.length) ys) := by
  induction xs generalizing k with
  | nil => simp [checkNodesTopological]
  | cons x rest ih =>
    simp only [List.cons_append, checkNodesTopological, ih, List.length_cons,
      show k + (rest.length + 1) = k + 1 + rest.length by omega, Bool.and_assoc]

theorem evalSsaNodes_append (env : FluxEnv) (xs ys : List FluxSsaNode) (acc : List Rat) :
    evalSsaNodes env (xs ++ ys) acc = evalSsaNodes env ys (evalSsaNodes env xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x rest ih => exact ih _

theorem internSsaNode_spec (nodes : List FluxSsaNode) (n : FluxSsaNode)
    (hTopo : checkNodesTopological 0 nodes = true)
    (hBound : checkSsaNodeBound nodes.length n = true) :
    (∃ sfx, (internSsaNode nodes n).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (internSsaNode nodes n).1 = true ∧
    (internSsaNode nodes n).2 < (internSsaNode nodes n).1.length ∧
    ((internSsaNode nodes n).1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + ssaNodeFlop n ∧
    ∀ env, getOr (evalSsaNodes env (internSsaNode nodes n).1 []) (internSsaNode nodes n).2 0 =
      evalSsaNodeStep env (evalSsaNodes env nodes []) n := by
  unfold internSsaNode
  cases hf : findSsaNodeIdx nodes n 0 with
  | some idx =>
    obtain ⟨off, hoff, hidx, hget⟩ := findSsaNodeIdx_spec nodes n 0 idx hf
    subst hidx; simp only [Nat.zero_add] at *
    refine ⟨⟨[], by simp⟩, hTopo, hoff, Nat.le_add_right _ _, fun env => ?_⟩
    have hAt := evalSsaNodes_at_index env nodes [] hTopo off hoff
    simp only [List.length_nil, Nat.zero_add, hget] at hAt
    exact hAt.2
  | none =>
    refine ⟨⟨[n], rfl⟩, ?_, by simp, by simp [List.map_append], fun env => ?_⟩
    · rw [checkNodesTopological_append, hTopo, Nat.zero_add]
      simp [checkNodesTopological, hBound]
    · rw [evalSsaNodes_append]
      have hLen := evalSsaNodes_length env nodes []
      simp only [List.length_nil, Nat.zero_add] at hLen
      simp only [evalSsaNodes]
      rw [← hLen, getOr_snoc_self]

theorem unarySsa_spec (nodes ns1 : List FluxSsaNode) (ia fA : Nat) (mkNode : Nat → FluxSsaNode)
    (valA : FluxEnv → Rat)
    (h1 : (∃ sfx, ns1 = nodes ++ sfx) ∧ checkNodesTopological 0 ns1 = true ∧ ia < ns1.length ∧
      (ns1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + fA ∧
      ∀ env, getOr (evalSsaNodes env ns1 []) ia 0 = valA env)
    (hB : checkSsaNodeBound ns1.length (mkNode ia) = true)
    (hFlop : ssaNodeFlop (mkNode ia) = 1) :
    (∃ sfx, (internSsaNode ns1 (mkNode ia)).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (internSsaNode ns1 (mkNode ia)).1 = true ∧
    (internSsaNode ns1 (mkNode ia)).2 < (internSsaNode ns1 (mkNode ia)).1.length ∧
    ((internSsaNode ns1 (mkNode ia)).1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + (fA + 1) ∧
    ∀ env, getOr (evalSsaNodes env (internSsaNode ns1 (mkNode ia)).1 [])
      (internSsaNode ns1 (mkNode ia)).2 0 =
      evalSsaNodeStep env (evalSsaNodes env ns1 []) (mkNode ia) := by
  obtain ⟨⟨sfx1, hs1⟩, hT1, _, hF1, _⟩ := h1
  obtain ⟨⟨sfx2, hs2⟩, hT2, hi2, hF2, hE2⟩ := internSsaNode_spec ns1 (mkNode ia) hT1 hB
  refine ⟨⟨sfx1 ++ sfx2, by rw [hs2, hs1, List.append_assoc]⟩, hT2, hi2, ?_, hE2⟩
  rw [hFlop] at hF2; omega

theorem binarySsa_spec (nodes ns1 ns2 : List FluxSsaNode) (ia ib fA fB : Nat)
    (mkNode : Nat → Nat → FluxSsaNode) (valA valB : FluxEnv → Rat)
    (h1 : (∃ sfx, ns1 = nodes ++ sfx) ∧ checkNodesTopological 0 ns1 = true ∧ ia < ns1.length ∧
      (ns1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + fA ∧
      ∀ env, getOr (evalSsaNodes env ns1 []) ia 0 = valA env)
    (h2 : (∃ sfx, ns2 = ns1 ++ sfx) ∧ checkNodesTopological 0 ns2 = true ∧ ib < ns2.length ∧
      (ns2.map ssaNodeFlop).sum ≤ (ns1.map ssaNodeFlop).sum + fB ∧
      ∀ env, getOr (evalSsaNodes env ns2 []) ib 0 = valB env)
    (hB : ∀ bound, ia < bound → ib < bound → checkSsaNodeBound bound (mkNode ia ib) = true)
    (hFlop : ssaNodeFlop (mkNode ia ib) = 1) :
    (∃ sfx, (internSsaNode ns2 (mkNode ia ib)).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (internSsaNode ns2 (mkNode ia ib)).1 = true ∧
    (internSsaNode ns2 (mkNode ia ib)).2 < (internSsaNode ns2 (mkNode ia ib)).1.length ∧
    ((internSsaNode ns2 (mkNode ia ib)).1.map ssaNodeFlop).sum ≤
      (nodes.map ssaNodeFlop).sum + (fA + fB + 1) ∧
    ∀ env, getOr (evalSsaNodes env ns2 []) ia 0 = valA env ∧
      getOr (evalSsaNodes env (internSsaNode ns2 (mkNode ia ib)).1 [])
        (internSsaNode ns2 (mkNode ia ib)).2 0 =
        evalSsaNodeStep env (evalSsaNodes env ns2 []) (mkNode ia ib) := by
  obtain ⟨⟨sfx1, hs1⟩, _, hi1, hF1, hE1⟩ := h1
  obtain ⟨⟨sfx2, hs2⟩, hT2, hi2, hF2, _⟩ := h2
  have hia2 : ia < ns2.length := by rw [hs2, List.length_append]; omega
  obtain ⟨⟨sfx3, hs3⟩, hT3, hi3, hF3, hE3⟩ :=
    internSsaNode_spec ns2 (mkNode ia ib) hT2 (hB ns2.length hia2 hi2)
  refine ⟨⟨sfx1 ++ (sfx2 ++ sfx3), by rw [hs3, hs2, hs1, List.append_assoc, List.append_assoc]⟩,
    hT3, hi3, ?_, fun env => ⟨?_, hE3 env⟩⟩
  · rw [hFlop] at hF3; omega
  · rw [hs2, evalSsaNodes_append, evalSsaNodes_prefix_getOr env sfx2 _ ia
      (by rw [evalSsaNodes_length]; simp; exact hi1), hE1 env]

theorem compileExprSsa_spec (e : FluxExpr) (nodes : List FluxSsaNode)
    (hTopo : checkNodesTopological 0 nodes = true) :
    (∃ sfx, (compileExprSsa e nodes).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (compileExprSsa e nodes).1 = true ∧
    (compileExprSsa e nodes).2 < (compileExprSsa e nodes).1.length ∧
    ((compileExprSsa e nodes).1.map ssaNodeFlop).sum ≤ (nodes.map ssaNodeFlop).sum + fluxExprFlops e ∧
    ∀ env, getOr (evalSsaNodes env (compileExprSsa e nodes).1 []) (compileExprSsa e nodes).2 0 =
      evalFlux e env := by
  induction e generalizing nodes with
  | const q =>
    simpa [compileExprSsa, fluxExprFlops, ssaNodeFlop, evalSsaNodeStep, evalFlux] using
      internSsaNode_spec nodes (.const q) hTopo rfl
  | var i =>
    simpa [compileExprSsa, fluxExprFlops, ssaNodeFlop, evalSsaNodeStep, evalFlux] using
      internSsaNode_spec nodes (.var i) hTopo rfl
  | param p =>
    simpa [compileExprSsa, fluxExprFlops, ssaNodeFlop, evalSsaNodeStep, evalFlux] using
      internSsaNode_spec nodes (.param p) hTopo rfl
  | neg a iha =>
    have h1 := iha nodes hTopo
    have hU := unarySsa_spec nodes (compileExprSsa a nodes).1 (compileExprSsa a nodes).2
      (fluxExprFlops a) FluxSsaNode.neg (evalFlux a) h1 (by simp [checkSsaNodeBound, h1.2.2.1]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1, fun env => ?_⟩
    rw [hU.2.2.2.2 env]; simp [evalSsaNodeStep, h1.2.2.2.2 env, evalFlux]
  | invSafe d ihd =>
    have h1 := ihd nodes hTopo
    have hU := unarySsa_spec nodes (compileExprSsa d nodes).1 (compileExprSsa d nodes).2
      (fluxExprFlops d) FluxSsaNode.invSafe (evalFlux d) h1 (by simp [checkSsaNodeBound, h1.2.2.1]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1, fun env => ?_⟩
    rw [hU.2.2.2.2 env]; simp [evalSsaNodeStep, h1.2.2.2.2 env, evalFlux]
  | add a b iha ihb =>
    have h1 := iha nodes hTopo
    have h2 := ihb (compileExprSsa a nodes).1 h1.2.1
    have hB := binarySsa_spec nodes (compileExprSsa a nodes).1
      (compileExprSsa b (compileExprSsa a nodes).1).1
      (compileExprSsa a nodes).2 (compileExprSsa b (compileExprSsa a nodes).1).2
      (fluxExprFlops a) (fluxExprFlops b) FluxSsaNode.add (evalFlux a) (evalFlux b) h1 h2
      (fun _ ha hb => by simp [checkSsaNodeBound, ha, hb]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, fun env => ?_⟩
    rw [(hB.2.2.2.2 env).2]; simp [evalSsaNodeStep, (hB.2.2.2.2 env).1, h2.2.2.2.2 env, evalFlux]
  | sub a b iha ihb =>
    have h1 := iha nodes hTopo
    have h2 := ihb (compileExprSsa a nodes).1 h1.2.1
    have hB := binarySsa_spec nodes (compileExprSsa a nodes).1
      (compileExprSsa b (compileExprSsa a nodes).1).1
      (compileExprSsa a nodes).2 (compileExprSsa b (compileExprSsa a nodes).1).2
      (fluxExprFlops a) (fluxExprFlops b) FluxSsaNode.sub (evalFlux a) (evalFlux b) h1 h2
      (fun _ ha hb => by simp [checkSsaNodeBound, ha, hb]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, fun env => ?_⟩
    rw [(hB.2.2.2.2 env).2]; simp [evalSsaNodeStep, (hB.2.2.2.2 env).1, h2.2.2.2.2 env, evalFlux]
  | mul a b iha ihb =>
    have h1 := iha nodes hTopo
    have h2 := ihb (compileExprSsa a nodes).1 h1.2.1
    have hB := binarySsa_spec nodes (compileExprSsa a nodes).1
      (compileExprSsa b (compileExprSsa a nodes).1).1
      (compileExprSsa a nodes).2 (compileExprSsa b (compileExprSsa a nodes).1).2
      (fluxExprFlops a) (fluxExprFlops b) FluxSsaNode.mul (evalFlux a) (evalFlux b) h1 h2
      (fun _ ha hb => by simp [checkSsaNodeBound, ha, hb]) rfl
    dsimp only [compileExprSsa, fluxExprFlops]
    refine ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, fun env => ?_⟩
    rw [(hB.2.2.2.2 env).2]; simp [evalSsaNodeStep, (hB.2.2.2.2 env).1, h2.2.2.2.2 env, evalFlux]

theorem compileExprListSsa_spec (es : List FluxExpr) (nodes : List FluxSsaNode)
    (hTopo : checkNodesTopological 0 nodes = true) :
    (∃ sfx, (compileExprListSsa es nodes).1 = nodes ++ sfx) ∧
    checkNodesTopological 0 (compileExprListSsa es nodes).1 = true ∧
    (∀ r ∈ (compileExprListSsa es nodes).2, r < (compileExprListSsa es nodes).1.length) ∧
    ((compileExprListSsa es nodes).1.map ssaNodeFlop).sum ≤
      (nodes.map ssaNodeFlop).sum + (es.map fluxExprFlops).sum ∧
    ∀ env, (compileExprListSsa es nodes).2.map
        (fun r => getOr (evalSsaNodes env (compileExprListSsa es nodes).1 []) r 0) =
      es.map (fun e => evalFlux e env) := by
  induction es generalizing nodes with
  | nil =>
    exact ⟨⟨[], by simp [compileExprListSsa]⟩, hTopo, by simp [compileExprListSsa],
      by simp [compileExprListSsa], fun _ => rfl⟩
  | cons e rest ih =>
    obtain ⟨⟨sfx1, hs1⟩, hT1, hr1, hF1, hE1⟩ := compileExprSsa_spec e nodes hTopo
    obtain ⟨⟨sfx2, hs2⟩, hT2, hrs, hF2, hE2⟩ := ih (compileExprSsa e nodes).1 hT1
    dsimp only [compileExprListSsa]
    refine ⟨⟨sfx1 ++ sfx2, by rw [hs2, hs1, List.append_assoc]⟩, hT2, ?_, ?_, fun env => ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hs2, List.length_append]; omega
      · exact hrs x hx'
    · simp only [List.map_cons, List.sum_cons]; omega
    · simp only [List.map_cons]
      have hHead : getOr (evalSsaNodes env (compileExprListSsa rest (compileExprSsa e nodes).1).1 [])
          (compileExprSsa e nodes).2 0 = evalFlux e env := by
        rw [hs2, evalSsaNodes_append, evalSsaNodes_prefix_getOr env sfx2 _ _
          (by rw [evalSsaNodes_length]; simp; exact hr1), hE1 env]
      rw [hHead, hE2 env]

theorem sum_map_le {α : Type} (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := h x List.mem_cons_self
    have hr := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

/-- **CSE SSA DAG Soundness & FLOP Reduction (`compileFluxSsaDag_sound`)**:
The specialized + CSE-deduplicated `FluxSsaDag` is a valid topological DAG, evaluates identically to
`exprs`, and uses no more FLOPs than the unspecialized expression forest (strictly fewer on shared nodes). -/
theorem compileFluxSsaDag_sound (pOpt : Option (Nat → Rat)) (exprs : List FluxExpr) :
    let dag := compileFluxSsaDag pOpt exprs
    checkFluxSsaDag dag = true ∧
    fluxSsaFlops dag ≤ (exprs.map fluxExprFlops).sum ∧
    ∀ env : FluxEnv,
      (match pOpt with | none => True | some pEnv => ∀ p, pEnv p = env.params p) →
      evalFluxSsaDag dag env = exprs.map (fun e => evalFlux e env) := by
  dsimp only [compileFluxSsaDag]
  obtain ⟨_, hTopo, hRoots, hFlops, hEval⟩ :=
    compileExprListSsa_spec (exprs.map (specializeFluxExpr pOpt)) [] rfl
  refine ⟨?_, ?_, fun env hP => ?_⟩
  · simp only [checkFluxSsaDag, hTopo, Bool.true_and, List.all_eq_true, decide_eq_true_eq]
    exact hRoots
  · simp only [fluxSsaFlops]
    simp only [List.map_nil, List.sum_nil, Nat.zero_add] at hFlops
    have hSpecLe : ((exprs.map (specializeFluxExpr pOpt)).map fluxExprFlops).sum ≤
        (exprs.map fluxExprFlops).sum := by
      rw [List.map_map]
      exact sum_map_le exprs _ _ fun e _ => specializedFlops_le_naive pOpt e
    omega
  · simp only [evalFluxSsaDag]
    rw [hEval env, List.map_map]
    exact List.map_congr_left fun e _ => specializeFluxExpr_sound pOpt e env hP

structure SpecializedSweepPlan where
  axisFluxDags : List FluxSsaDag
  axisJacobianDags : List FluxSsaDag
  naiveTotalFlops : Nat
  specializedTotalFlops : Nat
  deriving DecidableEq, Repr

/-- Specialize all directional fluxes `F_d(U)` and symbolic Jacobians `J_d(U)` of a `ConservationLawSpec`. -/
def specializeFluxSweep (spec : ConservationLawSpec) : SpecializedSweepPlan :=
  let m := spec.numVars
  let pOpt := some spec.paramEnv
  let rawJacs := spec.fluxes.map (fun row => (symJacobian m row).flatten)
  let fDags := spec.fluxes.map (compileFluxSsaDag pOpt)
  let jDags := rawJacs.map (compileFluxSsaDag pOpt)
  let naiveF := (spec.fluxes.map fun row => (row.map fluxExprFlops).sum).sum
  let naiveJ := (rawJacs.map fun j => (j.map fluxExprFlops).sum).sum
  let specF := (fDags.map fluxSsaFlops).sum
  let specJ := (jDags.map fluxSsaFlops).sum
  { axisFluxDags := fDags
    axisJacobianDags := jDags
    naiveTotalFlops := naiveF + naiveJ
    specializedTotalFlops := specF + specJ }

theorem specializeFluxSweep_sound (spec : ConservationLawSpec) :
    let plan := specializeFluxSweep spec
    plan.specializedTotalFlops ≤ plan.naiveTotalFlops ∧
    (∀ d, d < spec.fluxes.length →
      ∀ u : Vec,
        evalFluxSsaDag (getOr plan.axisFluxDags d ⟨[], []⟩) ⟨u, spec.paramEnv⟩ =
        (getOr spec.fluxes d []).map (fun e => evalFlux e ⟨u, spec.paramEnv⟩)) := by
  dsimp only [specializeFluxSweep]
  refine ⟨?_, ?_⟩
  · have hF : ((spec.fluxes.map (compileFluxSsaDag (some spec.paramEnv))).map fluxSsaFlops).sum ≤
        (spec.fluxes.map fun row => (row.map fluxExprFlops).sum).sum := by
      rw [List.map_map]
      exact sum_map_le spec.fluxes _ _ fun row _ => (compileFluxSsaDag_sound _ row).2.1
    have hJ : (((spec.fluxes.map (fun row => (symJacobian spec.numVars row).flatten)).map
          (compileFluxSsaDag (some spec.paramEnv))).map fluxSsaFlops).sum ≤
        ((spec.fluxes.map (fun row => (symJacobian spec.numVars row).flatten)).map
          fun j => (j.map fluxExprFlops).sum).sum := by
      rw [List.map_map]
      exact sum_map_le _ _ _ fun j _ => (compileFluxSsaDag_sound _ j).2.1
    omega
  · intro d hd u
    rw [getOr_map_lt spec.fluxes (compileFluxSsaDag (some spec.paramEnv)) d [] ⟨[], []⟩ hd]
    exact (compileFluxSsaDag_sound (some spec.paramEnv) (getOr spec.fluxes d [])).2.2
      ⟨u, spec.paramEnv⟩ (fun _ => rfl)

/-! ## 2. Arbitrary-Dimension `D`-D Brick Halo Tiling (`evalMultiDBrickTiled`) -/

/-- `CoordInBounds coords dims` holds when `coords` and `dims` have equal length and `coords_d < dims_d`. -/
def CoordInBounds : List Nat → List Nat → Prop
  | [], [] => True
  | c :: cs, N :: ds => c < N ∧ CoordInBounds cs ds
  | _, _ => False

theorem encodeMultiIdx_lt (dims coords : List Nat) (hB : CoordInBounds coords dims) :
    encodeMultiIdx dims coords < gridCellCount dims := by
  induction dims generalizing coords with
  | nil => cases coords with | nil => simp [encodeMultiIdx, gridCellCount] | cons _ _ => cases hB
  | cons N ds ih =>
    cases coords with
    | nil => cases hB
    | cons c cs =>
      obtain ⟨hc, hcs⟩ := hB
      have hrem := ih cs hcs
      simp only [encodeMultiIdx, gridCellCount, List.foldr_cons]
      have hle := Nat.mul_le_mul_right (gridCellCount ds) (show c + 1 ≤ N by omega)
      rw [Nat.add_mul, Nat.one_mul] at hle; unfold gridCellCount at hrem hle; omega

theorem decode_encode_multiIdx (dims coords : List Nat) (hB : CoordInBounds coords dims) :
    decodeMultiIdx dims (encodeMultiIdx dims coords) = coords := by
  induction dims generalizing coords with
  | nil => cases coords with | nil => rfl | cons _ _ => cases hB
  | cons N ds ih =>
    cases coords with
    | nil => cases hB
    | cons c cs =>
      obtain ⟨hc, hcs⟩ := hB
      have hrem := encodeMultiIdx_lt ds cs hcs
      have hstride : 0 < gridCellCount ds := by omega
      simp only [encodeMultiIdx, decodeMultiIdx, beq_false_of_ne (by omega : gridCellCount ds ≠ 0),
        Bool.false_eq_true, ↓reduceIte]
      have hdiv : (c * gridCellCount ds + encodeMultiIdx ds cs) / gridCellCount ds = c := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hstride, Nat.div_eq_of_lt hrem, Nat.zero_add]
      have hmod : (c * gridCellCount ds + encodeMultiIdx ds cs) % gridCellCount ds =
          encodeMultiIdx ds cs := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem]
      rw [hdiv, hmod, ih cs hcs]

theorem decodeMultiIdx_inBounds (dims : List Nat) (hPos : ∀ N ∈ dims, 0 < N)
    (idx : Nat) (hIdx : idx < gridCellCount dims) :
    CoordInBounds (decodeMultiIdx dims idx) dims := by
  induction dims generalizing idx with
  | nil => exact trivial
  | cons N ds ih =>
    have hDsPos : 0 < gridCellCount ds :=
      gridCellCount_pos ds fun M hM => hPos M (List.mem_cons_of_mem _ hM)
    simp only [decodeMultiIdx, beq_false_of_ne (by omega : gridCellCount ds ≠ 0),
      Bool.false_eq_true, ↓reduceIte, CoordInBounds]
    refine ⟨?_, ih (fun M hM => hPos M (List.mem_cons_of_mem _ hM)) _ (Nat.mod_lt idx hDsPos)⟩
    simp only [gridCellCount, List.foldr_cons] at hIdx
    exact Nat.div_lt_of_lt_mul (by unfold gridCellCount; rw [Nat.mul_comm]; exact hIdx)

def hypercubeDims (D r : Nat) : List Nat := List.replicate D (2 * r + 1)

theorem hypercubeDims_cellCount (D r : Nat) :
    gridCellCount (hypercubeDims D r) = (2 * r + 1) ^ D := by
  induction D with
  | zero => simp [hypercubeDims, gridCellCount]
  | succ d ih =>
    simp only [hypercubeDims, List.replicate_succ, gridCellCount, List.foldr_cons]
    unfold hypercubeDims gridCellCount at ih; rw [ih, Nat.pow_succ, Nat.mul_comm]

def resolveMultiCoords (b : StencilBoundary) : List Nat → List Nat → List Nat → Nat → List Nat
  | N :: ds, c :: cs, k :: ks, r =>
    resolveStencilIdx b N ((c : Int) + k - r) :: resolveMultiCoords b ds cs ks r
  | _, _, _, _ => []

def zipAddCoords : List Nat → List Nat → List Nat
  | x :: xs, y :: ys => (x + y) :: zipAddCoords xs ys
  | _, _ => []

/-- `D`-dimensional radius-`r` hypercube stencil window around `coords` (`(2r+1)^D` words). -/
def stencilWindowMultiD (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (grid : List Word) (coords : List Nat) : List Word :=
  let winDims := hypercubeDims dims.length r
  (List.range (gridCellCount winDims)).map fun offIdx =>
    let k := decodeMultiIdx winDims offIdx
    grid.getD (encodeMultiIdx dims (resolveMultiCoords b dims coords k r)) 0#64

/-- Reference untiled `D`-dimensional stencil evaluation across all `gridCellCount dims` cells. -/
def evalStencilMultiD (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (fn : List Word → Word) (grid : List Word) : List Word :=
  (List.range (gridCellCount dims)).map fun idx =>
    fn (stencilWindowMultiD b dims r grid (decodeMultiIdx dims idx))

/-- Cooperative brick load into local LDS scratchpad of shape `(w_0 + 2r) × … × (w_{D-1} + 2r)`. -/
def loadBrickHalo (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (grid : Array Word) (starts widths : List Nat) : Array Word :=
  let ldsDims := widths.map (· + 2 * r)
  ((List.range (gridCellCount ldsDims)).map fun ldsIdx =>
    let q := decodeMultiIdx ldsDims ldsIdx
    grid[encodeMultiIdx dims (resolveMultiCoords b dims starts q r)]?.getD 0#64).toArray

/-- Post-barrier local brick stencil computation reading ONLY the LDS scratchpad `lds`. -/
def computeBrickHalo (r : Nat) (widths : List Nat) (fn : List Word → Word)
    (lds : Array Word) : Array Word :=
  let ldsDims := widths.map (· + 2 * r)
  let winDims := hypercubeDims widths.length r
  ((List.range (gridCellCount widths)).map fun locIdx =>
    let j := decodeMultiIdx widths locIdx
    let win := (List.range (gridCellCount winDims)).map fun offIdx =>
      let k := decodeMultiIdx winDims offIdx
      lds[encodeMultiIdx ldsDims (zipAddCoords j k)]?.getD 0#64
    fn win).toArray

/-- Three-phase workgroup barrier machine for `D`-D bricks; refuses `.localCompute` before `.barrier`. -/
def executeBrickHaloPhases (r : Nat) (widths : List Nat) (fn : List Word → Word)
    (load : Unit → Array Word) : List HaloPhase → Array Word → Bool → Array Word
  | [], _, _ => #[]
  | .cooperativeLoad :: rest, _, _ => executeBrickHaloPhases r widths fn load rest (load ()) false
  | .barrier :: rest, lds, _ => executeBrickHaloPhases r widths fn load rest lds true
  | .localCompute :: _, lds, ready => if ready then computeBrickHalo r widths fn lds else #[]

theorem brickHalo_refuses_unready_compute (r : Nat) (widths : List Nat)
    (fn : List Word → Word) (load : Unit → Array Word) :
    executeBrickHaloPhases r widths fn load [.cooperativeLoad, .localCompute] #[] true = #[] := by
  simp [executeBrickHaloPhases]

def evalSingleBrickTile (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (fn : List Word → Word) (grid : Array Word) (starts widths : List Nat) : Array Word :=
  executeBrickHaloPhases r widths fn (fun _ => loadBrickHalo b dims r grid starts widths)
    [.cooperativeLoad, .barrier, .localCompute] #[] false

def brickCounts : List Nat → List Nat → List Nat
  | B :: bs, N :: ns => ((N + B - 1) / B) :: brickCounts bs ns
  | _, _ => []

def brickStarts : List Nat → List Nat → List Nat
  | t :: ts, B :: bs => (t * B) :: brickStarts ts bs
  | _, _ => []

def brickWidthsAt : List Nat → List Nat → List Nat → List Nat
  | B :: bs, N :: ns, t :: ts => min B (N - t * B) :: brickWidthsAt bs ns ts
  | _, _, _ => []

def zipDivCoords : List Nat → List Nat → List Nat
  | c :: cs, B :: bs => (c / B) :: zipDivCoords cs bs
  | _, _ => []

def zipModCoords : List Nat → List Nat → List Nat
  | c :: cs, B :: bs => (c % B) :: zipModCoords cs bs
  | _, _ => []

/-- Launch all `∏_d ⌈N_d / B_d⌉` `D`-dimensional bricks (including partial tail bricks!) once each. -/
def launchAllBricks (brickDims : List Nat) (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (fn : List Word → Word) (gridArr : Array Word) : Array (Array Word) :=
  let counts := brickCounts brickDims dims
  ((List.range (gridCellCount counts)).map fun brIdx =>
    let t := decodeMultiIdx counts brIdx
    evalSingleBrickTile b dims r fn gridArr (brickStarts t brickDims)
      (brickWidthsAt brickDims dims t)).toArray

/-- Multi-dimensional brick-tiled stencil execution: launches every brick once into LDS + barrier +
local compute, then gathers each global cell from its owning brick's local output tile. -/
def evalMultiDBrickTiled (brickDims : List Nat) (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (fn : List Word → Word) (grid : List Word) : List Word :=
  let gridArr := grid.toArray
  let counts := brickCounts brickDims dims
  let bricks := launchAllBricks brickDims b dims r fn gridArr
  (List.range (gridCellCount dims)).map fun idx =>
    let c := decodeMultiIdx dims idx
    let t := zipDivCoords c brickDims
    let j := zipModCoords c brickDims
    let widths := brickWidthsAt brickDims dims t
    let brOut := bricks[encodeMultiIdx counts t]?.getD #[]
    brOut[encodeMultiIdx widths j]?.getD 0#64

theorem zipAddCoords_inBounds_lds (r : Nat) (widths j k : List Nat)
    (hj : CoordInBounds j widths) (hk : CoordInBounds k (hypercubeDims widths.length r)) :
    CoordInBounds (zipAddCoords j k) (widths.map (· + 2 * r)) := by
  induction widths generalizing j k with
  | nil =>
    cases j with
    | nil => cases k with | nil => exact trivial | cons _ _ => simp [hypercubeDims, CoordInBounds] at hk
    | cons _ _ => cases hj
  | cons w ws ih =>
    cases j with
    | nil => cases hj
    | cons j0 js =>
      cases k with
      | nil => simp [hypercubeDims, CoordInBounds] at hk
      | cons k0 ks =>
        simp only [hypercubeDims, List.length_cons, List.replicate_succ, CoordInBounds] at hj hk
        simp only [zipAddCoords, List.map_cons, CoordInBounds]
        exact ⟨by omega, ih js ks hj.2 hk.2⟩

theorem resolveMultiCoords_add_assoc (b : StencilBoundary) (dims starts j k : List Nat) (r : Nat)
    (hLenS : starts.length = dims.length) (hLenJ : j.length = dims.length) :
    resolveMultiCoords b dims starts (zipAddCoords j k) r =
      resolveMultiCoords b dims (zipAddCoords starts j) k r := by
  induction dims generalizing starts j k with
  | nil => rfl
  | cons N ds ih =>
    cases starts with
    | nil => simp at hLenS
    | cons s ss =>
      cases j with
      | nil => simp at hLenJ
      | cons j0 js =>
        cases k with
        | nil => simp [zipAddCoords, resolveMultiCoords]
        | cons k0 ks =>
          simp only [zipAddCoords, resolveMultiCoords]
          have hHead : resolveStencilIdx b N ((s : Int) + ↑(j0 + k0) - ↑r) =
              resolveStencilIdx b N (↑(s + j0) + ↑k0 - ↑r) := by
            congr 1; omega
          rw [hHead, ih ss js ks (by simpa using hLenS) (by simpa using hLenJ)]

theorem loadBrickHalo_read (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (grid : List Word) (starts widths j k : List Nat)
    (hLenS : starts.length = dims.length) (hLenW : widths.length = dims.length)
    (hj : CoordInBounds j widths) (hk : CoordInBounds k (hypercubeDims widths.length r)) :
    (loadBrickHalo b dims r grid.toArray starts widths)[encodeMultiIdx (widths.map (· + 2 * r)) (zipAddCoords j k)]?.getD 0#64 =
      grid.getD (encodeMultiIdx dims (resolveMultiCoords b dims (zipAddCoords starts j) k r)) 0#64 := by
  have hjLen : j.length = widths.length := by
    clear hLenS hLenW hk
    induction widths generalizing j with
    | nil => cases j with | nil => rfl | cons _ _ => cases hj
    | cons _ ws ih => cases j with | nil => cases hj | cons _ js => simp [ih js hj.2]
  have hInLds := zipAddCoords_inBounds_lds r widths j k hj hk
  have hLt := encodeMultiIdx_lt (widths.map (· + 2 * r)) (zipAddCoords j k) hInLds
  simp only [loadBrickHalo, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hLt, Option.map_some, Option.getD_some,
    decode_encode_multiIdx _ _ hInLds, List.getD_eq_getElem?_getD]
  rw [resolveMultiCoords_add_assoc b dims starts j k r hLenS (hjLen.trans hLenW)]

theorem div_lt_ceil_div (c N B : Nat) (hc : c < N) (hB : 0 < B) :
    c / B < (N + B - 1) / B := by
  have h1 : (c / B + 1) * B ≤ N + B - 1 := by
    have hd := Nat.div_add_mod c B
    have hm := Nat.mod_lt c hB
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (c / B) B]; omega
  have h2 := Nat.div_le_div_right h1 (c := B)
  rw [Nat.mul_div_cancel _ hB] at h2; omega

theorem coord_div_mod_brick (brickDims dims c : List Nat)
    (hLen : brickDims.length = dims.length)
    (hBPos : ∀ B ∈ brickDims, 0 < B)
    (hc : CoordInBounds c dims) :
    let t := zipDivCoords c brickDims
    let j := zipModCoords c brickDims
    let widths := brickWidthsAt brickDims dims t
    CoordInBounds t (brickCounts brickDims dims) ∧
    CoordInBounds j widths ∧
    zipAddCoords (brickStarts t brickDims) j = c ∧
    (brickStarts t brickDims).length = dims.length ∧
    widths.length = dims.length := by
  induction dims generalizing brickDims c with
  | nil =>
    cases brickDims with
    | nil => cases c with | nil => exact ⟨trivial, trivial, rfl, rfl, rfl⟩ | cons _ _ => cases hc
    | cons _ _ => simp at hLen
  | cons N ds ih =>
    cases brickDims with
    | nil => simp at hLen
    | cons B bs =>
      cases c with
      | nil => cases hc
      | cons c0 cs =>
        have hB0 : 0 < B := hBPos B List.mem_cons_self
        have hbsPos : ∀ B' ∈ bs, 0 < B' := fun B' hB' => hBPos B' (List.mem_cons_of_mem _ hB')
        obtain ⟨htRest, hjRest, hAddRest, hSLen, hWLen⟩ :=
          ih bs cs (by simpa using hLen) hbsPos hc.2
        refine ⟨⟨div_lt_ceil_div c0 N B hc.1 hB0, htRest⟩,
                ⟨?_, hjRest⟩, ?_,
                by simp [zipDivCoords, brickStarts, hSLen],
                by simp [zipDivCoords, brickWidthsAt, hWLen]⟩
        · have hd := Nat.div_add_mod c0 B
          have hm := Nat.mod_lt c0 hB0
          have hc0 : c0 < N := hc.1
          rw [Nat.mul_comm] at hd; omega
        · simp only [zipDivCoords, zipModCoords, brickStarts, zipAddCoords, hAddRest]
          refine congrArg (· :: cs) ?_
          have hd := Nat.div_add_mod c0 B; rw [Nat.mul_comm] at hd; exact hd

/-- **Exact Multi-Dimensional Brick-Tiling Equivalence (`multiDBrickTiled_eq_global_sweep`)**:
For *every* dimension `D`, positive grid extents `dims` (including non-multiple tail bricks!),
positive brick extents `brickDims`, radius `r`, and boundary policy `b`, `evalMultiDBrickTiled`
computes the **exact** same `D`-dimensional stencil sweep as `evalStencilMultiD`. -/
theorem multiDBrickTiled_eq_global_sweep (brickDims : List Nat) (b : StencilBoundary)
    (dims : List Nat) (r : Nat) (fn : List Word → Word) (grid : List Word)
    (hLen : brickDims.length = dims.length)
    (hBPos : ∀ B ∈ brickDims, 0 < B)
    (hDPos : ∀ N ∈ dims, 0 < N) :
    evalMultiDBrickTiled brickDims b dims r fn grid = evalStencilMultiD b dims r fn grid := by
  dsimp only [evalMultiDBrickTiled, evalStencilMultiD]
  apply List.map_congr_left
  intro idx hMem
  have hIdx : idx < gridCellCount dims := List.mem_range.mp hMem
  have hcBounds : CoordInBounds (decodeMultiIdx dims idx) dims :=
    decodeMultiIdx_inBounds dims hDPos idx hIdx
  obtain ⟨htB, hjB, hStartAdd, hSLen, hWLen⟩ :=
    coord_div_mod_brick brickDims dims (decodeMultiIdx dims idx) hLen hBPos hcBounds
  have htLt := encodeMultiIdx_lt (brickCounts brickDims dims)
    (zipDivCoords (decodeMultiIdx dims idx) brickDims) htB
  have hjLt := encodeMultiIdx_lt
    (brickWidthsAt brickDims dims (zipDivCoords (decodeMultiIdx dims idx) brickDims))
    (zipModCoords (decodeMultiIdx dims idx) brickDims) hjB
  have hBrLookup :
      (launchAllBricks brickDims b dims r fn grid.toArray)[encodeMultiIdx
        (brickCounts brickDims dims) (zipDivCoords (decodeMultiIdx dims idx) brickDims)]?.getD #[] =
      evalSingleBrickTile b dims r fn grid.toArray
        (brickStarts (zipDivCoords (decodeMultiIdx dims idx) brickDims) brickDims)
        (brickWidthsAt brickDims dims (zipDivCoords (decodeMultiIdx dims idx) brickDims)) := by
    simp only [launchAllBricks, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range htLt, Option.map_some, Option.getD_some,
      decode_encode_multiIdx (brickCounts brickDims dims) _ htB]
  rw [hBrLookup]
  simp only [evalSingleBrickTile, executeBrickHaloPhases, ↓reduceIte, computeBrickHalo,
    List.getElem?_toArray, List.getElem?_map, List.getElem?_range hjLt,
    Option.map_some, Option.getD_some,
    decode_encode_multiIdx _ _ hjB]
  congr 1
  unfold stencilWindowMultiD
  rw [hWLen]
  apply List.map_congr_left
  intro offIdx hOffMem
  have hOffLt : offIdx < gridCellCount (hypercubeDims dims.length r) := List.mem_range.mp hOffMem
  have hkB : CoordInBounds (decodeMultiIdx (hypercubeDims dims.length r) offIdx)
      (hypercubeDims (brickWidthsAt brickDims dims (zipDivCoords (decodeMultiIdx dims idx) brickDims)).length r) := by
    rw [hWLen]
    exact decodeMultiIdx_inBounds _ (fun M hM => by
      rw [hypercubeDims, List.mem_replicate] at hM; omega) offIdx hOffLt
  rw [loadBrickHalo_read b dims r grid _ _ _ _ hSLen hWLen hjB hkB, hStartAdd]

/-- Total global HBM word reads across all `D`-dimensional bricks (product of per-axis halo reads). -/
def multiDBrickHbmReads (brickDims : List Nat) (r : Nat) (dims : List Nat) : Nat :=
  (List.zipWith (fun B N => tiledHbmReads B r N) brickDims dims).foldr (· * ·) 1

theorem tiledHbmReads_pos (B r N : Nat) (hB : 0 < B) (hN : 0 < N) :
    0 < tiledHbmReads B r N := by
  rw [tiledHaloStencil_hbm_reads_exact B r N hB]; omega

/-- **Multi-Dimensional Brick HBM Traffic Reduction (`multiDBrickHbmReads_lt_global`)**:
Whenever `dims` is non-empty, `0 < r`, and every brick axis satisfies `2 ≤ B_d ≤ N_d`, `D`-D brick
halo tiling strictly reduces global HBM reads below untiled `(2r + 1)^D * ∏_d N_d` (including
non-multiple tail bricks!). -/
theorem multiDBrickHbmReads_lt_global (brickDims dims : List Nat) (r : Nat)
    (hNonEmpty : dims ≠ []) (hr : 0 < r)
    (hLen : brickDims.length = dims.length)
    (hB2 : ∀ B ∈ brickDims, 2 ≤ B)
    (hBN : ∀ d < dims.length, getOr brickDims d 0 ≤ getOr dims d 0) :
    multiDBrickHbmReads brickDims r dims < (2 * r + 1) ^ dims.length * gridCellCount dims := by
  induction dims generalizing brickDims with
  | nil => exact absurd rfl hNonEmpty
  | cons N ds ih =>
    cases brickDims with
    | nil => simp at hLen
    | cons B bs =>
      have hB_ge2 : 2 ≤ B := hB2 B List.mem_cons_self
      have hBN0 : B ≤ N := by simpa [getOr] using hBN 0 (by simp)
      have hAxisLt := tiledHbmReads_lt_global B r N hr hB_ge2 hBN0
      cases ds with
      | nil =>
        cases bs with
        | nil =>
          simpa [multiDBrickHbmReads, gridCellCount, Nat.pow_one] using hAxisLt
        | cons _ _ => simp at hLen
      | cons N2 ds' =>
        cases bs with
        | nil => simp at hLen
        | cons B2 bs' =>
          have hSubLt := ih (B2 :: bs') (by simp) (by simpa using hLen)
            (fun B' hB' => hB2 B' (List.mem_cons_of_mem _ hB'))
            (fun d hd => by simpa [getOr] using hBN (d + 1) (by simp; omega))
          simp only [multiDBrickHbmReads, List.zipWith_cons_cons, List.foldr_cons,
            List.length_cons, Nat.pow_succ, gridCellCount] at hSubLt ⊢
          calc tiledHbmReads B r N *
                (tiledHbmReads B2 r N2 * (List.zipWith (fun B N => tiledHbmReads B r N) bs' ds').foldr (· * ·) 1)
            _ < ((2 * r + 1) * N) * ((2 * r + 1) ^ (N2 :: ds').length * (N2 * ds'.foldr (· * ·) 1)) :=
              Nat.mul_lt_mul'' hAxisLt hSubLt
            _ = ((2 * r + 1) ^ (N2 :: ds').length * (2 * r + 1)) * (N * (N2 * ds'.foldr (· * ·) 1)) := by
              ac_rfl

/-! ## 3. Single-Pass Vertical SOAC Fusion (`SoacOptimize`) for Multi-D Stencils -/

def multiDHaloIndexFn (b : StencilBoundary) (dims : List Nat) (r slot : Nat) : FiniteFunction :=
  let M := gridCellCount dims
  let winDims := hypercubeDims dims.length r
  ⟨M, M, (List.range M).map fun idx =>
    let coords := decodeMultiIdx dims idx
    let k := decodeMultiIdx winDims slot
    encodeMultiIdx dims (resolveMultiCoords b dims coords k r)⟩

def multiDHaloLeaf (b : StencilBoundary) (dims : List Nat) (r slot : Nat) : Rhs :=
  if slot < gridCellCount (hypercubeDims dims.length r) then
    .gather (multiDHaloIndexFn b dims r slot) 0
  else
    .literal (List.replicate (gridCellCount dims) 0#64)

/-- Global SOAC lowering of a `D`-dimensional stencil optimized by CSE + Dead-Code Elimination. -/
def compileMultiDStencilOpt (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (e : ScalarExpr) : Program :=
  dceProgram (cseProgram (compileScalar (gridCellCount dims) (multiDHaloLeaf b dims r) e (.ret [0])))

/-- Single-pass vertically fused GPU lowering (`reconstructMinmod ∘ rusanovFlux ∘ cellUpdate` in 1 pass). -/
def compileMultiDSweepFused (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (e : ScalarExpr) : FusedProgram :=
  fuseVertical (liftArraySource (compileMultiDStencilOpt b dims r e))

theorem multiDHaloLeaf_length (b : StencilBoundary) (dims : List Nat) (r slot : Nat) (env : Env) :
    ((multiDHaloLeaf b dims r slot).eval env).length = gridCellCount dims := by
  unfold multiDHaloLeaf; split <;> simp [Rhs.eval, multiDHaloIndexFn]

theorem multiDHaloLeaf_read (b : StencilBoundary) (dims : List Nat) (r slot idx : Nat)
    (grid : List Word) (hi : idx < gridCellCount dims) :
    ((multiDHaloLeaf b dims r slot).eval (fun _ => grid)).getD idx 0#64 =
      (stencilWindowMultiD b dims r grid (decodeMultiIdx dims idx)).getD slot 0#64 := by
  unfold multiDHaloLeaf
  split
  · rename_i hs
    simp only [Rhs.eval, multiDHaloIndexFn, stencilWindowMultiD, List.map_map,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      List.getElem?_range hs, Option.map_some, Option.getD_some, Function.comp_apply]
  · rename_i hs
    simp only [Rhs.eval, stencilWindowMultiD, List.getD_eq_getElem?_getD,
      List.getElem?_replicate_of_lt hi,
      List.getElem?_eq_none (by simp; omega : (List.map _ (List.range (gridCellCount (hypercubeDims dims.length r)))).length ≤ slot),
      Option.getD_some, Option.getD_none]

/-- **Single-Pass Vertical SOAC Fusion Soundness (`compileMultiDSweepFused_sound`)**:
Lowering a `D`-dimensional stencil through CSE, DCE, `liftArraySource`, and `fuseVertical` produces
the exact `evalStencilMultiD` result in a single fused kernel pass, while never increasing `letCount`. -/
theorem compileMultiDSweepFused_sound (b : StencilBoundary) (dims : List Nat) (r : Nat)
    (e : ScalarExpr) (grid : List Word) :
    evalFused (fun _ => grid) (compileMultiDSweepFused b dims r e) =
      [evalStencilMultiD b dims r (scalarStencil e) grid] ∧
    letCount (compileMultiDStencilOpt b dims r e) ≤
      letCount (compileScalar (gridCellCount dims) (multiDHaloLeaf b dims r) e (.ret [0])) := by
  refine ⟨?_, Nat.le_trans (dceProgram_count_le _) (cseWith_count_le _ [])⟩
  rw [compileMultiDSweepFused, fuseVertical_sound, liftArraySource_sound,
      compileMultiDStencilOpt, dceProgram_sound, cseProgram_sound]
  obtain ⟨final, he, hv, _⟩ :=
    compileScalar_eval e (gridCellCount dims) (multiDHaloLeaf b dims r) (fun _ => grid) (.ret [0])
  rw [he]
  simp only [Program.eval, List.map_cons, List.map_nil, hv]
  congr 1
  rw [evalScalarArrays_pointwise e (gridCellCount dims) _
    (fun s => multiDHaloLeaf_length b dims r s _)]
  unfold evalStencilMultiD
  apply List.map_congr_left
  intro idx hMem
  unfold scalarStencil
  congr 1
  funext s
  exact multiDHaloLeaf_read b dims r s idx grid (List.mem_range.mp hMem)

/-- Fused 2nd-order `minmod` + Rusanov scalar kernel expression on a `D`-D radius-2 window. -/
def multiDMinmodRusanovExpr (D : Nat) (courantNum viscosityNum : Int) : ScalarExpr :=
  let center := ((2 * 2 + 1) ^ D) / 2
  if center >= 2 then
    let sL := scalarMinmod (scalarSub (.input (center - 1)) (.input (center - 2)))
                           (scalarSub (.input center) (.input (center - 1)))
    let sR := scalarMinmod (scalarSub (.input (center + 1)) (.input center))
                           (scalarSub (.input (center + 2)) (.input (center + 1)))
    scalarAdd (scalarSub (scalarScale 2 (.input center))
      (scalarScale courantNum (scalarSub (.input (center + 1)) (.input (center - 1)))))
      (scalarScale viscosityNum (scalarSub sR sL))
  else
    rusanovNumerator courantNum viscosityNum

/-! ## 4. Q32.32 Systolic `HDL.RtlModule` Lowering & `RangeSafe` Interval Gate -/

/-- Encode an exact `Rat` constant into signed Q32.32 fixed-point (`⌊q · 2^32⌋` as `BitVec 64`). -/
def ratToQ32Word (q : Rat) : BitVec 64 :=
  let scaled : Int := (q.num * ((2 : Int) ^ 32)) / (q.den : Int)
  BitVec.ofInt 64 scaled

/-- Lower a single `FluxSsaNode` into a combinational `RtlExpr` (`qmul32` for Q32.32 products). -/
def lowerSsaNodeToRtl (numVars : Nat) : FluxSsaNode → RtlExpr
  | .const q => .const (ratToQ32Word q)
  | .var i => if i < numVars then .inputPort i else .const 0#64
  | .param _ => .const 0#64
  | .neg a => .alu .sub (.const 0#64) (.wireRef a)
  | .add a b => .alu .add (.wireRef a) (.wireRef b)
  | .sub a b => .alu .sub (.wireRef a) (.wireRef b)
  | .mul a b => .alu .qmul32 (.wireRef a) (.wireRef b)
  | .invSafe d => .alu .qmul32 (.const (ratToQ32Word 1)) (.wireRef d)

def lowerSsaNodesToWires (numVars : Nat) : Nat → List FluxSsaNode → List WireAssign
  | _, [] => []
  | idx, n :: rest =>
    { wireIdx := idx, name := s!"ssa_w{idx}", expr := lowerSsaNodeToRtl numVars n } ::
      lowerSsaNodesToWires numVars (idx + 1) rest

/-- Synthesize a pipelined synchronous Q32.32 systolic `HDL.RtlModule` from a `FluxSsaDag`. -/
def emitSystolicFluxCellRtlModule (modName : String) (varNames : List String)
    (dag : FluxSsaDag) : RtlModule :=
  let numVars := varNames.length
  let wires := lowerSsaNodesToWires numVars 0 dag.nodes
  let nWires := wires.length
  let validRoots := dag.roots.filter (· < nWires)
  let regs : List RegSpec := (List.range validRoots.length).map fun k =>
    let rWire := getOr validRoots k 0
    { regIdx := k
      name := s!"flux_pipe_r{k}"
      width := 64
      domain := .coreClk
      resetKind := .syncReset 0#64
      isSynchronizer := false
      nextExpr := .wireRef rWire }
  let outputs : List OutputPort := (List.range validRoots.length).map fun k =>
    { name := s!"flux_out_{k}", expr := .regRead k, width := 64 }
  { name := modName
    inputNames := varNames
    wires := wires
    regs := regs
    outputs := outputs }

theorem lowerSsaNodeToRtl_dag (numVars numRegs bound : Nat) (n : FluxSsaNode)
    (hB : checkSsaNodeBound bound n = true) :
    checkExprDAG numVars numRegs bound (lowerSsaNodeToRtl numVars n) = true := by
  cases n <;> simp only [checkSsaNodeBound, Bool.and_eq_true, decide_eq_true_eq] at hB <;>
    simp only [lowerSsaNodeToRtl, checkExprDAG]
  · split <;> simp [checkExprDAG, ‹_›]
  · simp [hB]
  · simp [hB.1, hB.2]
  · simp [hB.1, hB.2]
  · simp [hB.1, hB.2]
  · simp [hB]

theorem lowerSsaNodesToWires_length (numVars idx : Nat) (ns : List FluxSsaNode) :
    (lowerSsaNodesToWires numVars idx ns).length = ns.length := by
  induction ns generalizing idx with
  | nil => rfl
  | cons _ rest ih => simp [lowerSsaNodesToWires, ih]

theorem lowerSsaNodesToWires_dag_go (numVars numRegs idx : Nat) (ns : List FluxSsaNode)
    (hTopo : checkNodesTopological idx ns = true) :
    checkWireTableDAG.go numVars numRegs idx (lowerSsaNodesToWires numVars idx ns) = true := by
  induction ns generalizing idx with
  | nil => rfl
  | cons n rest ih =>
    simp only [checkNodesTopological, Bool.and_eq_true] at hTopo
    simp [lowerSsaNodesToWires, checkWireTableDAG.go,
      lowerSsaNodeToRtl_dag numVars numRegs idx n hTopo.1, ih (idx + 1) hTopo.2]

/-- **Systolic `HDL.RtlModule` Well-Formedness & CDC/DAG Soundness (`emitSystolicFluxCellRtlModule_ok`)**:
Every `FluxSsaDag` satisfying `checkFluxSsaDag` lowers to an `RtlModule` passing `checkRtlModule`
(acyclic topological wire table, in-bounds pipeline registers & output ports, single-domain CDC). -/
theorem emitSystolicFluxCellRtlModule_ok (modName : String) (varNames : List String)
    (dag : FluxSsaDag) (hDag : checkFluxSsaDag dag = true) :
    checkRtlModule (emitSystolicFluxCellRtlModule modName varNames dag) = true := by
  simp only [checkFluxSsaDag, Bool.and_eq_true] at hDag
  unfold emitSystolicFluxCellRtlModule checkRtlModule
  dsimp only
  have hWT : checkWireTableDAG varNames.length
      (dag.roots.filter (· < (lowerSsaNodesToWires varNames.length 0 dag.nodes).length)).length
      (lowerSsaNodesToWires varNames.length 0 dag.nodes) = true := by
    unfold checkWireTableDAG
    exact lowerSsaNodesToWires_dag_go _ _ 0 dag.nodes hDag.1
  simp only [List.length_map, List.length_range, hWT, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro r hr
    rw [List.mem_map] at hr; obtain ⟨k, hk, rfl⟩ := hr
    have hk' : k < (dag.roots.filter (· < (lowerSsaNodesToWires varNames.length 0 dag.nodes).length)).length :=
      List.mem_range.mp hk
    have hMem := getOr_mem_of_lt _ k 0 hk'
    rw [List.mem_filter] at hMem
    simpa [checkExprDAG] using of_decide_eq_true hMem.2
  · rw [List.all_eq_true]
    intro o ho
    rw [List.mem_map] at ho; obtain ⟨k, hk, rfl⟩ := ho
    simpa [checkExprDAG] using List.mem_range.mp hk
  · unfold checkModuleCdc
    rw [List.all_eq_true]
    intro dst hdst
    rw [List.mem_map] at hdst; obtain ⟨k, _, rfl⟩ := hdst
    simp [checkRegCdc, exprReadRegs, exprReadRegsAndWires]

/-- **Systolic Wire-Table Semantic Agreement (`evalWireTable_systolic_at_index`)**:
Because `lowerSsaNodesToWires` is strictly topological (`checkNodesTopological`), later wire
assignments (`≥ idx + 1`) never clobber earlier wires (`evalRtlExpr_dag_locality`), so wire `j` of
`emitSystolicFluxCellRtlModule` evaluates to `evalRtlExpr` of node `j`'s Q32.32 `RtlExpr`. -/
theorem foldl_lowerSsaNodesToWires_preserve (inputs regs : Nat → BitVec 64)
    (numVars idx : Nat) (ns : List FluxSsaNode) (env : Nat → BitVec 64) (k : Nat) (hk : k < idx) :
    (lowerSsaNodesToWires numVars idx ns).foldl
      (fun (e : Nat → BitVec 64) a =>
        let v := evalRtlExpr inputs e regs a.expr
        fun i => if i == a.wireIdx then v else e i) env k = env k := by
  induction ns generalizing idx env with
  | nil => rfl
  | cons n rest ih =>
    simp only [lowerSsaNodesToWires, List.foldl_cons]
    rw [ih (idx + 1) _ (by omega)]
    simp [beq_false_of_ne (by omega : k ≠ idx)]

theorem evalWireTable_systolic_at_index (inputs regs : Nat → BitVec 64)
    (modName : String) (varNames : List String) (dag : FluxSsaDag)
    (hTopo : checkNodesTopological 0 dag.nodes = true) (j : Nat) (hj : j < dag.nodes.length) :
    let m := emitSystolicFluxCellRtlModule modName varNames dag
    let wEnv := evalWireTable inputs regs m.wires
    wEnv j = evalRtlExpr inputs wEnv regs
      (lowerSsaNodeToRtl varNames.length (getOr dag.nodes j (.const 0))) := by
  dsimp only [emitSystolicFluxCellRtlModule, evalWireTable]
  suffices ∀ (idx : Nat) (ns : List FluxSsaNode) (env : Nat → BitVec 64) (off : Nat),
      checkNodesTopological idx ns = true → off < ns.length →
      let fullEnv := (lowerSsaNodesToWires varNames.length idx ns).foldl
        (fun (e : Nat → BitVec 64) a =>
          let v := evalRtlExpr inputs e regs a.expr
          fun i => if i == a.wireIdx then v else e i) env
      fullEnv (idx + off) = evalRtlExpr inputs fullEnv regs
        (lowerSsaNodeToRtl varNames.length (getOr ns off (.const 0))) by
    simpa using this 0 dag.nodes (fun _ => 0#64) j hTopo hj
  intro idx ns
  induction ns generalizing idx with
  | nil => intro _ _ _ h; simp at h
  | cons n rest ih =>
    intro env off hT hOff
    simp only [checkNodesTopological, Bool.and_eq_true] at hT
    cases off with
    | zero =>
      simp only [Nat.add_zero, getOr, lowerSsaNodesToWires, List.foldl_cons]
      let env1 : Nat → BitVec 64 :=
        let v := evalRtlExpr inputs env regs (lowerSsaNodeToRtl varNames.length n)
        fun i => if i == idx then v else env i
      have hKeep := foldl_lowerSsaNodesToWires_preserve inputs regs varNames.length (idx + 1) rest
        env1 idx (by omega)
      rw [hKeep]
      simp only [env1, beq_self_eq_true, ↓reduceIte]
      exact evalRtlExpr_dag_locality varNames.length 0 idx inputs regs env _
        _ (lowerSsaNodeToRtl_dag varNames.length 0 idx n hT.1) fun i hi => by
          rw [foldl_lowerSsaNodesToWires_preserve inputs regs varNames.length (idx + 1) rest
            env1 i (by omega)]
          simp [env1, show i ≠ idx by omega]
    | succ off' =>
      simp only [lowerSsaNodesToWires, List.foldl_cons]
      let env1 : Nat → BitVec 64 :=
        let v := evalRtlExpr inputs env regs (lowerSsaNodeToRtl varNames.length n)
        fun i => if i == idx then v else env i
      have hStep := ih (idx + 1) env1 off' hT.2 (by simpa using hOff)
      simpa [env1, show idx + 1 + off' = idx + (off' + 1) by omega, getOr] using hStep

/-- Static non-negative magnitude interval bound propagation over `FluxSsaDag` via `RangeSafe.Interval`,
refusing any Q32.32 wire whose worst-case magnitude reaches `2^62` (preventing 64-bit wrap). -/
def ssaNodeHiBound (varBounds : Nat → RangeSafe.Interval) (acc : List RangeSafe.Interval) :
    FluxSsaNode → Nat
  | .const q => (ratToQ32Word (if q < 0 then -q else q)).toNat
  | .var i => (varBounds i).hi
  | .param _ => 0
  | .neg a | .invSafe a => (getOr acc a (RangeSafe.Interval.mkNat 0 0)).hi
  | .add a b | .sub a b =>
    (getOr acc a (RangeSafe.Interval.mkNat 0 0)).hi +
    (getOr acc b (RangeSafe.Interval.mkNat 0 0)).hi
  | .mul a b =>
    ((getOr acc a (RangeSafe.Interval.mkNat 0 0)).hi *
     (getOr acc b (RangeSafe.Interval.mkNat 0 0)).hi) / (2 ^ 32) + 1

def inferNodesMagnitude (varBounds : Nat → RangeSafe.Interval) :
    List FluxSsaNode → List RangeSafe.Interval → Option (List RangeSafe.Interval)
  | [], acc => some acc
  | n :: rest, acc =>
    let hi := ssaNodeHiBound varBounds acc n
    if hi < 2 ^ 62 then inferNodesMagnitude varBounds rest (acc ++ [RangeSafe.Interval.mkNat 0 hi])
    else none

def inferSsaDagMagnitudeIntervals (varBounds : Nat → RangeSafe.Interval)
    (dag : FluxSsaDag) : Option (List RangeSafe.Interval) :=
  inferNodesMagnitude varBounds dag.nodes []

theorem inferSsaDagMagnitudeIntervals_safe (varBounds : Nat → RangeSafe.Interval)
    (dag : FluxSsaDag) (ivs : List RangeSafe.Interval)
    (hOk : inferSsaDagMagnitudeIntervals varBounds dag = some ivs) :
    ∀ iv ∈ ivs, iv.sort = .nat ∧ iv.hi < 2 ^ 62 := by
  unfold inferSsaDagMagnitudeIntervals at hOk
  suffices ∀ (ns : List FluxSsaNode) (acc : List RangeSafe.Interval),
      (∀ iv ∈ acc, iv.sort = .nat ∧ iv.hi < 2 ^ 62) →
      inferNodesMagnitude varBounds ns acc = some ivs →
      ∀ iv ∈ ivs, iv.sort = .nat ∧ iv.hi < 2 ^ 62 from
    this dag.nodes [] (by simp) hOk
  intro ns
  induction ns with
  | nil =>
    intro acc hAcc hEq
    simp only [inferNodesMagnitude, Option.some.injEq] at hEq
    subst hEq; exact hAcc
  | cons n rest ih =>
    intro acc hAcc hEq
    simp only [inferNodesMagnitude] at hEq
    by_cases hLt : ssaNodeHiBound varBounds acc n < 2 ^ 62
    · simp only [hLt, ↓reduceIte] at hEq
      refine ih _ (fun iv hiv => ?_) hEq
      rw [List.mem_append, List.mem_singleton] at hiv
      rcases hiv with h1 | rfl
      · exact hAcc iv h1
      · exact ⟨rfl, hLt⟩
    · simp [hLt] at hEq

end Obend.Hardware.MultiDStencilTile
