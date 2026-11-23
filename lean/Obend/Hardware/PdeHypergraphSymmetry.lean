module
public import Obend.Hardware.PdeSolvers
public import Obend.Hardware.MultiDStencilCorrect
public import Obend.Hardware.OpenHypergraph
public import Obend.Analysis.Equitable
import all Init.Data.ToString.Basic
import all Init.Data.Repr
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Hardware.HDL
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.MultiDStencilCorrect
import all Obend.Hardware.PdeSolvers
import all Obend.Hardware.OpenHypergraph
import all Obend.Analysis.Equitable
import all Obend.Tactic.SymDiffAndFlux

/-!
# PDE Axis Symmetry, Zero-Extra-Silicon Systolic Reuse & Open-Hypergraph Equitable Quotienting

1. Exact 3D cyclic axis equivariance for `EulerGas3D.spec` (`euler3d_cyclic_axis_equivariance`).
2. Exact planar `(x ↔ y)` reflection equivariance for `IdealMhd8Wave.spec` (`mhd8wave_planar_axis_equivariance`).
3. Bit-exact Q32.32 SSA equivariance and zero-extra-silicon systolic RTL axis reuse
   (`euler3d_single_systolic_cell_serves_all_3_axes`, `mhd8wave_single_systolic_cell_serves_both_axes`).
4. Open-hypergraph lowering of `FluxSsaDag` (`fluxSsaDagToOpenHypergraph`,
   `fluxSsaDagToOpenHypergraph_wf`, `fluxSsaDagToOpenHypergraph_sound`), $S_3$-invariant quadratic
   energy sub-DAGs, and `Analysis.Equitable` quotient intertwining with anisotropic negative witnesses.
-/

public section
namespace Obend.Hardware.PdeHypergraphSymmetry

open Obend.Analysis Obend.Analysis.HyperbolicPde Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.HDL Obend.Hardware.MultiDStencilTile Obend.Hardware.MultiDStencilCorrect
open Obend.Hardware.PdeSolvers Obend.Hardware.OpenHypergraph Obend.Tactic.SymDiffAndFlux

set_option autoImplicit false

/-! ## 1. Structural AC Equivalence Checker for Rational & Q32.32 `FluxExpr`s -/

/-- Substitute state variable indices in a `FluxExpr` via `f : Nat → Nat`. -/
def substFluxVars (f : Nat → Nat) : FluxExpr → FluxExpr
  | .const q => .const q | .var i => .var (f i) | .param p => .param p
  | .neg a => .neg (substFluxVars f a) | .invSafe d => .invSafe (substFluxVars f d)
  | .add a b => .add (substFluxVars f a) (substFluxVars f b)
  | .sub a b => .sub (substFluxVars f a) (substFluxVars f b)
  | .mul a b => .mul (substFluxVars f a) (substFluxVars f b)

/-- Pointwise Q32.32 semantics of a `FluxExpr` tree (matching `evalFluxSsaNodeQ32`). -/
def evalFluxExprQ32 (inputs : Nat → Word) (paramEnv : Nat → Rat) : FluxExpr → Word
  | .const q => ratToQ32Word q | .var i => inputs i | .param p => ratToQ32Word (paramEnv p)
  | .neg a => -(evalFluxExprQ32 inputs paramEnv a)
  | .add a b => evalFluxExprQ32 inputs paramEnv a + evalFluxExprQ32 inputs paramEnv b
  | .sub a b => evalFluxExprQ32 inputs paramEnv a - evalFluxExprQ32 inputs paramEnv b
  | .mul a b => evalAluOp .qmul32 (evalFluxExprQ32 inputs paramEnv a) (evalFluxExprQ32 inputs paramEnv b)
  | .invSafe d => evalQ32Reciprocal (evalFluxExprQ32 inputs paramEnv d)

/-- Sound syntactic equivalence checker up to 2- or 3-term `+` AC rearrangement and `*` commutativity. -/
def checkFluxAcEquiv : FluxExpr → FluxExpr → Bool
  | .const q1, .const q2 => q1 == q2 | .var i1, .var i2 => i1 == i2 | .param p1, .param p2 => p1 == p2
  | .neg a1, .neg a2 => checkFluxAcEquiv a1 a2 | .invSafe a1, .invSafe a2 => checkFluxAcEquiv a1 a2
  | .sub a1 b1, .sub a2 b2 => checkFluxAcEquiv a1 a2 && checkFluxAcEquiv b1 b2
  | .mul a1 b1, .mul a2 b2 =>
    (checkFluxAcEquiv a1 a2 && checkFluxAcEquiv b1 b2) || (checkFluxAcEquiv a1 b2 && checkFluxAcEquiv b1 a2)
  | .add x1 c1, .add x2 c2 =>
    ((checkFluxAcEquiv x1 x2 && checkFluxAcEquiv c1 c2) || (checkFluxAcEquiv x1 c2 && checkFluxAcEquiv c1 x2)) ||
    match x1, x2 with
    | .add a1 b1, .add a2 b2 =>
      (checkFluxAcEquiv a1 b2 && checkFluxAcEquiv b1 c2 && checkFluxAcEquiv c1 a2) ||
      (checkFluxAcEquiv a1 c2 && checkFluxAcEquiv b1 a2 && checkFluxAcEquiv c1 b2)
    | _, _ => false
  | _, _ => false

theorem qmul32_comm (a b : Word) : evalAluOp .qmul32 a b = evalAluOp .qmul32 b a := by
  rw [qmul32_eq_ofInt, qmul32_eq_ofInt, Int.mul_comm]

private def evalFluxAlg {α : Type} (c : Rat → α) (v p : Nat → α) (neg inv : α → α)
    (add sub mul : α → α → α) : FluxExpr → α
  | .const q => c q | .var i => v i | .param k => p k
  | .neg a => neg (evalFluxAlg c v p neg inv add sub mul a)
  | .invSafe a => inv (evalFluxAlg c v p neg inv add sub mul a)
  | .add a b => add (evalFluxAlg c v p neg inv add sub mul a) (evalFluxAlg c v p neg inv add sub mul b)
  | .sub a b => sub (evalFluxAlg c v p neg inv add sub mul a) (evalFluxAlg c v p neg inv add sub mul b)
  | .mul a b => mul (evalFluxAlg c v p neg inv add sub mul a) (evalFluxAlg c v p neg inv add sub mul b)

private theorem evalFluxAlg_subst {α : Type} (c : Rat → α) (v p : Nat → α) (neg inv : α → α)
    (add sub mul : α → α → α) (f : Nat → Nat) (e : FluxExpr) :
    evalFluxAlg c v p neg inv add sub mul (substFluxVars f e) =
      evalFluxAlg c (fun i => v (f i)) p neg inv add sub mul e := by
  induction e with
  | const _ | var _ | param _ => rfl
  | neg _ ih | invSafe _ ih => simp only [substFluxVars, evalFluxAlg, ih]
  | add _ _ iha ihb | sub _ _ iha ihb | mul _ _ iha ihb => simp only [substFluxVars, evalFluxAlg, iha, ihb]

private theorem checkFluxAcEquiv_sound_alg {α : Type} (c : Rat → α) (v p : Nat → α) (neg inv : α → α)
    (add sub mul : α → α → α)
    (hAddC : ∀ x y, add x y = add y x) (hAddA : ∀ x y z, add (add x y) z = add x (add y z))
    (hMulC : ∀ x y, mul x y = mul y x) :
    ∀ e1 e2 : FluxExpr, checkFluxAcEquiv e1 e2 = true →
      evalFluxAlg c v p neg inv add sub mul e1 = evalFluxAlg c v p neg inv add sub mul e2
  | .const q1, e2, h => by cases e2 <;> simp [checkFluxAcEquiv] at h; subst h; rfl
  | .var i1, e2, h => by cases e2 <;> simp [checkFluxAcEquiv] at h; subst h; rfl
  | .param p1, e2, h => by cases e2 <;> simp [checkFluxAcEquiv] at h; subst h; rfl
  | .neg a1, e2, h => by
    cases e2 with
    | neg a2 => exact congrArg neg (checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC a1 a2 h)
    | _ => simp [checkFluxAcEquiv] at h
  | .invSafe a1, e2, h => by
    cases e2 with
    | invSafe a2 => exact congrArg inv (checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC a1 a2 h)
    | _ => simp [checkFluxAcEquiv] at h
  | .sub a1 b1, e2, h => by
    cases e2 with
    | sub a2 b2 =>
      unfold checkFluxAcEquiv at h; simp only [Bool.and_eq_true] at h
      exact congrArg₂ sub (checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC a1 a2 h.1)
        (checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC b1 b2 h.2)
    | _ => simp [checkFluxAcEquiv] at h
  | .mul a1 b1, e2, h => by
    cases e2 with
    | mul a2 b2 =>
      unfold checkFluxAcEquiv at h; simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact congrArg₂ mul (checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC a1 a2 ha)
          (checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC b1 b2 hb)
      · simp only [evalFluxAlg, checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC a1 b2 ha,
          checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC b1 a2 hb, hMulC]
    | _ => simp [checkFluxAcEquiv] at h
  | .add x1 c1, e2, h => by
    cases e2 with
    | add x2 c2 =>
      unfold checkFluxAcEquiv at h; simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h3
      · exact congrArg₂ add (checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC x1 x2 h1)
          (checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC c1 c2 h2)
      · simp only [evalFluxAlg, checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC x1 c2 h1,
          checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC c1 x2 h2, hAddC]
      · cases x1 with
        | add a1 b1 =>
          cases x2 with
          | add a2 b2 =>
            simp only [Bool.or_eq_true, Bool.and_eq_true] at h3
            rcases h3 with ⟨⟨h1, h2⟩, h4⟩ | ⟨⟨h1, h2⟩, h4⟩
            · simp only [evalFluxAlg,
                checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC a1 b2 h1,
                checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC b1 c2 h2,
                checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC c1 a2 h4]
              rw [hAddC (add _ _), ← hAddA]
            · simp only [evalFluxAlg,
                checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC a1 c2 h1,
                checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC b1 a2 h2,
                checkFluxAcEquiv_sound_alg c v p neg inv add sub mul hAddC hAddA hMulC c1 b2 h4]
              rw [hAddC _ (evalFluxAlg _ _ _ _ _ _ _ _ a2), hAddA, hAddC _ (evalFluxAlg _ _ _ _ _ _ _ _ b2), ← hAddA]
          | _ => cases h3
        | _ => cases h3
    | _ => simp [checkFluxAcEquiv] at h
where
  congrArg₂ {β : Type} (f : β → β → β) {x₁ x₂ y₁ y₂ : β} (hx : x₁ = x₂) (hy : y₁ = y₂) : f x₁ y₁ = f x₂ y₂ := by
    subst hx hy; rfl

private theorem evalFlux_eq_alg (env : FluxEnv) (e : FluxExpr) :
    evalFlux e env = evalFluxAlg id env.state env.params (-·) ((1 : Rat) / ·) (· + ·) (· - ·) (· * ·) e := by
  induction e <;> simp [evalFlux, evalFluxAlg, *]
private theorem evalFluxExprQ32_eq_alg (ins : Nat → Word) (pEnv : Nat → Rat) (e : FluxExpr) :
    evalFluxExprQ32 ins pEnv e =
      evalFluxAlg ratToQ32Word ins (fun p => ratToQ32Word (pEnv p)) (-·) evalQ32Reciprocal (· + ·) (· - ·) (evalAluOp .qmul32) e := by
  induction e <;> simp [evalFluxExprQ32, evalFluxAlg, *]
theorem evalFlux_substFluxVars (f : Nat → Nat) (U : Vec) (pEnv : Nat → Rat) (e : FluxExpr) :
    evalFlux (substFluxVars f e) ⟨U, pEnv⟩ = evalFlux e ⟨fun i => U (f i), pEnv⟩ := by
  rw [evalFlux_eq_alg, evalFlux_eq_alg]; exact evalFluxAlg_subst _ _ _ _ _ _ _ _ f e
theorem evalFluxExprQ32_substFluxVars (f : Nat → Nat) (inputs : Nat → Word) (pEnv : Nat → Rat) (e : FluxExpr) :
    evalFluxExprQ32 inputs pEnv (substFluxVars f e) = evalFluxExprQ32 (fun i => inputs (f i)) pEnv e := by
  rw [evalFluxExprQ32_eq_alg, evalFluxExprQ32_eq_alg]; exact evalFluxAlg_subst _ _ _ _ _ _ _ _ f e
theorem checkFluxAcEquiv_sound_rat (e1 e2 : FluxExpr) (env : FluxEnv) (h : checkFluxAcEquiv e1 e2 = true) :
    evalFlux e1 env = evalFlux e2 env := by
  rw [evalFlux_eq_alg, evalFlux_eq_alg]
  exact checkFluxAcEquiv_sound_alg id env.state env.params (-·) ((1 : Rat) / ·) (· + ·) (· - ·) (· * ·)
    Rat.add_comm Rat.add_assoc Rat.mul_comm e1 e2 h
theorem checkFluxAcEquiv_sound_q32 (e1 e2 : FluxExpr) (inputs : Nat → Word) (pEnv : Nat → Rat)
    (h : checkFluxAcEquiv e1 e2 = true) : evalFluxExprQ32 inputs pEnv e1 = evalFluxExprQ32 inputs pEnv e2 := by
  rw [evalFluxExprQ32_eq_alg, evalFluxExprQ32_eq_alg]
  exact checkFluxAcEquiv_sound_alg ratToQ32Word inputs (fun p => ratToQ32Word (pEnv p)) (-·)
    evalQ32Reciprocal (· + ·) (· - ·) (evalAluOp .qmul32) BitVec.add_comm BitVec.add_assoc qmul32_comm e1 e2 h

/-! ## 2. Exact 3D Cyclic Axis Equivariance (`EulerGas3D.spec`) & Planar Reflection (`IdealMhd8Wave.spec`) -/

/-- Index action of $C_3$ on 3D Euler state indices `(rho, rhou, rhov, rhow, E)`. -/
def eulerVarPerm (shift i : Nat) : Nat :=
  let s := shift % 3
  if s == 1 then (if i == 1 then 2 else if i == 2 then 3 else if i == 3 then 1 else i)
  else if s == 2 then (if i == 1 then 3 else if i == 2 then 1 else if i == 3 then 2 else i) else i
@[expose] def permuteEulerVec (shift : Nat) (U : Vec) : Vec := fun i => U (eulerVarPerm shift i)
@[expose] def evalSpecAxisFlux (spec : ConservationLawSpec) (axis : Nat) (U : Vec) : Vec :=
  fun c => evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨U, spec.paramEnv⟩
theorem eulerVarPerm_add (s1 s2 i : Nat) : eulerVarPerm s2 (eulerVarPerm s1 i) = eulerVarPerm (s1 + s2) i := by
  have h1 : s1 % 3 = 0 ∨ s1 % 3 = 1 ∨ s1 % 3 = 2 := by omega
  have h2 : s2 % 3 = 0 ∨ s2 % 3 = 1 ∨ s2 % 3 = 2 := by omega
  have hadd : (s1 + s2) % 3 = (s1 % 3 + s2 % 3) % 3 := Nat.add_mod s1 s2 3
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    (by_cases hi1 : i = 1 <;> by_cases hi2 : i = 2 <;> by_cases hi3 : i = 3 <;> simp [eulerVarPerm, h1, h2, hadd, hi1, hi2, hi3])
theorem permuteEulerVec_zero (U : Vec) : permuteEulerVec 0 U = U := by funext i; simp [permuteEulerVec, eulerVarPerm]
theorem permuteEulerVec_comp (s1 s2 : Nat) (U : Vec) : permuteEulerVec s1 (permuteEulerVec s2 U) = permuteEulerVec (s1 + s2) U := by
  funext i; simp only [permuteEulerVec, eulerVarPerm_add]
theorem permuteEulerVec_inv_left (U : Vec) : permuteEulerVec 2 (permuteEulerVec 1 U) = U := by
  rw [permuteEulerVec_comp]; funext i; simp [permuteEulerVec, eulerVarPerm]
theorem permuteEulerVec_inv_right (U : Vec) : permuteEulerVec 1 (permuteEulerVec 2 U) = U := by
  rw [permuteEulerVec_comp]; funext i; simp [permuteEulerVec, eulerVarPerm]
theorem permuteEulerVec_domainValid (shift : Nat) (U : Vec) :
    DomainValid EulerGas3D.spec.domain ⟨permuteEulerVec shift U, EulerGas3D.spec.paramEnv⟩ ↔
      DomainValid EulerGas3D.spec.domain ⟨U, EulerGas3D.spec.paramEnv⟩ := by
  have h0 : permuteEulerVec shift U 0 = U 0 := by
    simp only [permuteEulerVec, eulerVarPerm]; have h : shift % 3 = 0 ∨ shift % 3 = 1 ∨ shift % 3 = 2 := by omega
    rcases h with h | h | h <;> simp [h]
  have hdom : EulerGas3D.spec.domain = [.stateVar 0] := by decide +kernel
  constructor <;> intro hDom t ht <;>
    (have ht' : t = .stateVar 0 := by rw [hdom] at ht; simpa using ht
     subst ht'; simpa [h0] using hDom (.stateVar 0) ht)
private theorem getOr_ge_len {α : Type} (xs : List α) (i : Nat) (d : α) (hi : xs.length ≤ i) : getOr xs i d = d := by
  induction xs generalizing i with | nil => rfl | cons _ rest ih => cases i with | zero => simp at hi | succ i' => exact ih i' (by simpa using hi)

private theorem euler3d_axis_pair_equiv (srcAxis dstAxis shift : Nat)
    (hCheck : (List.range 5).all (fun c =>
      checkFluxAcEquiv
        (substFluxVars (eulerVarPerm shift) (getOr (getOr EulerGas3D.spec.fluxes srcAxis []) c (.const 0)))
        (getOr (getOr EulerGas3D.spec.fluxes dstAxis []) (eulerVarPerm shift c) (.const 0))) = true)
    (hLenSrc : (getOr EulerGas3D.spec.fluxes srcAxis []).length = 5)
    (hLenDst : (getOr EulerGas3D.spec.fluxes dstAxis []).length = 5) (U : Vec) (c : Nat) :
    evalSpecAxisFlux EulerGas3D.spec srcAxis (permuteEulerVec shift U) c =
      permuteEulerVec shift (evalSpecAxisFlux EulerGas3D.spec dstAxis U) c := by
  by_cases hc : c < 5
  · have hSound := checkFluxAcEquiv_sound_rat _ _ ⟨U, EulerGas3D.spec.paramEnv⟩
      (List.all_eq_true.mp hCheck c (List.mem_range.mpr hc))
    rw [evalFlux_substFluxVars] at hSound; exact hSound
  · have hPermGe : 5 ≤ eulerVarPerm shift c := by
      simp only [eulerVarPerm]
      have hs : shift % 3 = 0 ∨ shift % 3 = 1 ∨ shift % 3 = 2 := by omega
      have h1 : (c == 1) = false := beq_false_of_ne (by omega)
      have h2 : (c == 2) = false := beq_false_of_ne (by omega)
      have h3 : (c == 3) = false := beq_false_of_ne (by omega)
      rcases hs with hs | hs | hs <;> simp [hs, h1, h2, h3] <;> omega
    have hg1 := getOr_ge_len (getOr EulerGas3D.spec.fluxes srcAxis []) c (.const 0) (by omega)
    have hg2 := getOr_ge_len (getOr EulerGas3D.spec.fluxes dstAxis []) (eulerVarPerm shift c) (.const 0) (by omega)
    simp only [evalSpecAxisFlux, permuteEulerVec, hg1, hg2]; rfl

/-- **Theorem (`euler3d_cyclic_axis_equivariance`)**:
Exact $C_3$ cyclic axis permutation equivariance for `EulerGas3D.spec`. -/
theorem euler3d_cyclic_axis_equivariance (U : Vec) (c : Nat) :
    evalSpecAxisFlux EulerGas3D.spec 0 (permuteEulerVec 1 U) c =
      permuteEulerVec 1 (evalSpecAxisFlux EulerGas3D.spec 1 U) c ∧
    evalSpecAxisFlux EulerGas3D.spec 1 (permuteEulerVec 2 U) c =
      permuteEulerVec 2 (evalSpecAxisFlux EulerGas3D.spec 0 U) c ∧
    evalSpecAxisFlux EulerGas3D.spec 1 (permuteEulerVec 1 U) c =
      permuteEulerVec 1 (evalSpecAxisFlux EulerGas3D.spec 2 U) c ∧
    evalSpecAxisFlux EulerGas3D.spec 2 (permuteEulerVec 1 U) c =
      permuteEulerVec 1 (evalSpecAxisFlux EulerGas3D.spec 0 U) c ∧
    ∀ axis : Fin 3,
      evalSpecAxisFlux EulerGas3D.spec axis.val U c =
        permuteEulerVec ((3 - axis.val) % 3)
          (evalSpecAxisFlux EulerGas3D.spec 0 (permuteEulerVec axis.val U)) c := by
  have h01 := euler3d_axis_pair_equiv 0 1 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) U
  have h10 := euler3d_axis_pair_equiv 1 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) U
  have h12 := euler3d_axis_pair_equiv 1 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) U
  have h20 := euler3d_axis_pair_equiv 2 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) U
  have h02 := euler3d_axis_pair_equiv 0 2 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) U
  refine ⟨h01 c, h10 c, h12 c, h20 c, fun axis => ?_⟩
  rcases axis with ⟨a, ha⟩
  match a, ha with
  | 0, _ => simp only [Nat.sub_zero, Nat.mod_self, permuteEulerVec_zero]
  | 1, _ =>
    have hInv := congrFun (permuteEulerVec_inv_left (evalSpecAxisFlux EulerGas3D.spec 1 U)) c
    dsimp only [permuteEulerVec] at hInv ⊢; rw [← hInv]; exact (h01 _).symm
  | 2, _ =>
    have hInv := congrFun (permuteEulerVec_inv_right (evalSpecAxisFlux EulerGas3D.spec 2 U)) c
    dsimp only [permuteEulerVec] at hInv ⊢; rw [← hInv]; exact (h02 _).symm

/-- Planar `(x ↔ y)` reflection on 8-wave MHD indices (`1 ↔ 2`, `4 ↔ 5`) and state vectors. -/
def mhdPlanarVarSwap (i : Nat) : Nat :=
  if i == 1 then 2 else if i == 2 then 1 else if i == 4 then 5 else if i == 5 then 4 else i
@[expose] def swapMhdPlanarVec (U : Vec) : Vec := fun i => U (mhdPlanarVarSwap i)
theorem mhdPlanarVarSwap_invol (i : Nat) : mhdPlanarVarSwap (mhdPlanarVarSwap i) = i := by
  by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;> by_cases h4 : i = 4 <;> by_cases h5 : i = 5 <;> simp [mhdPlanarVarSwap, h1, h2, h4, h5]
theorem swapMhdPlanarVec_invol (U : Vec) : swapMhdPlanarVec (swapMhdPlanarVec U) = U := by
  funext i; simp only [swapMhdPlanarVec, mhdPlanarVarSwap_invol]
theorem swapMhdPlanarVec_domainValid (U : Vec) :
    DomainValid IdealMhd8Wave.spec.domain ⟨swapMhdPlanarVec U, IdealMhd8Wave.spec.paramEnv⟩ ↔
      DomainValid IdealMhd8Wave.spec.domain ⟨U, IdealMhd8Wave.spec.paramEnv⟩ := by
  have hdom : IdealMhd8Wave.spec.domain = [.stateVar 0] := by decide +kernel
  constructor <;> intro hDom t ht <;>
    (have ht' : t = .stateVar 0 := by rw [hdom] at ht; simpa using ht
     subst ht'; simpa [swapMhdPlanarVec, mhdPlanarVarSwap] using hDom (.stateVar 0) ht)

/-- **Theorem (`mhd8wave_planar_axis_equivariance`)**:
Exact `(x ↔ y)` reflection equivariance for 9-component `IdealMhd8Wave.spec`. -/
theorem mhd8wave_planar_axis_equivariance (U : Vec) (c : Nat) :
    evalSpecAxisFlux IdealMhd8Wave.spec 1 (swapMhdPlanarVec U) c =
      swapMhdPlanarVec (evalSpecAxisFlux IdealMhd8Wave.spec 0 U) c ∧
    evalSpecAxisFlux IdealMhd8Wave.spec 1 U c =
      swapMhdPlanarVec (evalSpecAxisFlux IdealMhd8Wave.spec 0 (swapMhdPlanarVec U)) c := by
  have h10 : ∀ V : Vec, ∀ k : Nat,
      evalSpecAxisFlux IdealMhd8Wave.spec 1 (swapMhdPlanarVec V) k =
        swapMhdPlanarVec (evalSpecAxisFlux IdealMhd8Wave.spec 0 V) k := fun V k => by
    have hCheck : (List.range 9).all (fun i =>
        checkFluxAcEquiv
          (substFluxVars mhdPlanarVarSwap (getOr (getOr IdealMhd8Wave.spec.fluxes 1 []) i (.const 0)))
          (getOr (getOr IdealMhd8Wave.spec.fluxes 0 []) (mhdPlanarVarSwap i) (.const 0))) = true := by decide +kernel
    by_cases hk : k < 9
    · have hSound := checkFluxAcEquiv_sound_rat _ _ ⟨V, IdealMhd8Wave.spec.paramEnv⟩
        (List.all_eq_true.mp hCheck k (List.mem_range.mpr hk))
      rw [evalFlux_substFluxVars] at hSound; exact hSound
    · have hSwapGe : 9 ≤ mhdPlanarVarSwap k := by
        simp only [mhdPlanarVarSwap, beq_false_of_ne (by omega : k ≠ 1), beq_false_of_ne (by omega : k ≠ 2),
          beq_false_of_ne (by omega : k ≠ 4), beq_false_of_ne (by omega : k ≠ 5), Bool.false_eq_true, ↓reduceIte]; omega
      have hLen0 : (getOr IdealMhd8Wave.spec.fluxes 0 []).length = 9 := by decide +kernel
      have hLen1 : (getOr IdealMhd8Wave.spec.fluxes 1 []).length = 9 := by decide +kernel
      have hg1 := getOr_ge_len (getOr IdealMhd8Wave.spec.fluxes 1 []) k (.const 0) (by omega)
      have hg2 := getOr_ge_len (getOr IdealMhd8Wave.spec.fluxes 0 []) (mhdPlanarVarSwap k) (.const 0) (by omega)
      simp only [evalSpecAxisFlux, swapMhdPlanarVec, hg1, hg2]; rfl
  refine ⟨h10 U c, ?_⟩
  have hSwap := h10 (swapMhdPlanarVec U) c; rw [swapMhdPlanarVec_invol] at hSwap; exact hSwap

/-! ## 3. Bit-Exact Q32.32 SSA Equivariance & Zero-Extra-Silicon Systolic RTL Reuse -/

private def evalSsaNodesQ32 (ins : Nat → Word) (pEnv : Nat → Rat) (ns : List FluxSsaNode) (acc : Array Word) : Array Word :=
  ns.foldl (fun a n => a.push (evalFluxSsaNodeQ32 ins pEnv a n)) acc
private theorem evalSsaNodesQ32_size (ins : Nat → Word) (pEnv : Nat → Rat) (ns : List FluxSsaNode) (acc : Array Word) :
    (evalSsaNodesQ32 ins pEnv ns acc).size = acc.size + ns.length := by
  induction ns generalizing acc with
  | nil => simp [evalSsaNodesQ32]
  | cons n rest ih => change (evalSsaNodesQ32 ins pEnv rest (acc.push _)).size = _; rw [ih]; simp; omega
private theorem evalSsaNodesQ32_append (ins : Nat → Word) (pEnv : Nat → Rat) (xs ys : List FluxSsaNode) (acc : Array Word) :
    evalSsaNodesQ32 ins pEnv (xs ++ ys) acc = evalSsaNodesQ32 ins pEnv ys (evalSsaNodesQ32 ins pEnv xs acc) := by
  simp only [evalSsaNodesQ32, List.foldl_append]
private theorem evalSsaNodesQ32_prefix_getD (ins : Nat → Word) (pEnv : Nat → Rat) (ns : List FluxSsaNode)
    (acc : Array Word) (i : Nat) (hi : i < acc.size) : (evalSsaNodesQ32 ins pEnv ns acc).getD i 0#64 = acc.getD i 0#64 := by
  induction ns generalizing acc with
  | nil => rfl
  | cons n rest ih =>
    change (evalSsaNodesQ32 ins pEnv rest (acc.push _)).getD i 0#64 = _
    rw [ih _ (by simp; omega)]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, show i ≠ acc.size by omega, ↓reduceIte]
private theorem evalFluxSsaNodeQ32_ext (ins : Nat → Word) (pEnv : Nat → Rat) (a1 a2 : Array Word) (n : FluxSsaNode)
    (bound : Nat) (hB : checkSsaNodeBound bound n = true) (hEq : ∀ k < bound, a1.getD k 0#64 = a2.getD k 0#64) :
    evalFluxSsaNodeQ32 ins pEnv a1 n = evalFluxSsaNodeQ32 ins pEnv a2 n := by
  cases n <;> simp only [checkSsaNodeBound, Bool.and_eq_true, decide_eq_true_eq] at hB <;> simp only [evalFluxSsaNodeQ32]
  · rw [hEq _ hB]
  · rw [hEq _ hB.1, hEq _ hB.2]
  · rw [hEq _ hB.1, hEq _ hB.2]
  · rw [hEq _ hB.1, hEq _ hB.2]
  · rw [hEq _ hB]

private theorem evalSsaNodesQ32_at_index (ins : Nat → Word) (pEnv : Nat → Rat)
    (ns : List FluxSsaNode) (acc : Array Word)
    (hTopo : checkNodesTopological acc.size ns = true) (j : Nat) (hj : j < ns.length) :
    (evalSsaNodesQ32 ins pEnv ns acc).getD (acc.size + j) 0#64 =
      evalFluxSsaNodeQ32 ins pEnv (evalSsaNodesQ32 ins pEnv ns acc) (getOr ns j (.const 0)) := by
  induction ns generalizing acc j with
  | nil => simp at hj
  | cons n rest ih =>
    simp only [checkNodesTopological, Bool.and_eq_true] at hTopo
    cases j with
    | zero =>
      simp only [Nat.add_zero, getOr]
      have hPush : evalSsaNodesQ32 ins pEnv (n :: rest) acc =
          evalSsaNodesQ32 ins pEnv rest (acc.push (evalFluxSsaNodeQ32 ins pEnv acc n)) := rfl
      rw [hPush, evalSsaNodesQ32_prefix_getD ins pEnv rest _ acc.size (by simp)]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, ↓reduceIte, Option.getD_some]
      refine evalFluxSsaNodeQ32_ext ins pEnv acc _ n acc.size hTopo.1 fun k hk => ?_
      rw [evalSsaNodesQ32_prefix_getD ins pEnv rest _ k (by simp; omega)]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, show k ≠ acc.size by omega, ↓reduceIte]
    | succ j' =>
      have hSub := ih (acc.push (evalFluxSsaNodeQ32 ins pEnv acc n)) (by simpa using hTopo.2) j' (by simpa using hj)
      rw [show (acc.push (evalFluxSsaNodeQ32 ins pEnv acc n)).size + j' = acc.size + (j' + 1) by simp; omega] at hSub
      exact hSub

private theorem internSsaNode_q32_eval (ins : Nat → Word) (pEnv : Nat → Rat)
    (nodes : List FluxSsaNode) (n : FluxSsaNode) (hTopo : checkNodesTopological 0 nodes = true) :
    (evalSsaNodesQ32 ins pEnv (internSsaNode nodes n).1 #[]).getD (internSsaNode nodes n).2 0#64 =
      evalFluxSsaNodeQ32 ins pEnv (evalSsaNodesQ32 ins pEnv nodes #[]) n := by
  unfold internSsaNode
  cases hf : findSsaNodeIdx nodes n 0 with
  | some idx =>
    obtain ⟨off, hoff, hidx, hget⟩ := findSsaNodeIdx_spec nodes n 0 idx hf
    subst hidx; simp only [Nat.zero_add] at *
    simpa [hget] using evalSsaNodesQ32_at_index ins pEnv nodes #[] (by simpa using hTopo) off hoff
  | none =>
    dsimp only; rw [evalSsaNodesQ32_append]
    have hSz : (evalSsaNodesQ32 ins pEnv nodes #[]).size = nodes.length := by rw [evalSsaNodesQ32_size]; simp
    rw [← hSz]
    simp only [evalSsaNodesQ32, List.foldl_cons, List.foldl_nil, Array.getD_eq_getD_getElem?,
      Array.getElem?_push, ↓reduceIte, Option.getD_some]

private theorem compileExprSsa_q32_eval (ins : Nat → Word) (pEnv : Nat → Rat)
    (e : FluxExpr) (nodes : List FluxSsaNode) (hTopo : checkNodesTopological 0 nodes = true) :
    (evalSsaNodesQ32 ins pEnv (compileExprSsa e nodes).1 #[]).getD (compileExprSsa e nodes).2 0#64 =
      evalFluxExprQ32 ins pEnv e := by
  induction e generalizing nodes with
  | const q => simpa [compileExprSsa, evalFluxExprQ32, evalFluxSsaNodeQ32] using internSsaNode_q32_eval ins pEnv nodes (.const q) hTopo
  | var i => simpa [compileExprSsa, evalFluxExprQ32, evalFluxSsaNodeQ32] using internSsaNode_q32_eval ins pEnv nodes (.var i) hTopo
  | param p => simpa [compileExprSsa, evalFluxExprQ32, evalFluxSsaNodeQ32] using internSsaNode_q32_eval ins pEnv nodes (.param p) hTopo
  | neg a iha | invSafe a iha =>
    have h1 := compileExprSsa_spec a nodes hTopo
    dsimp only [compileExprSsa, evalFluxExprQ32]
    rw [internSsaNode_q32_eval ins pEnv _ _ h1.2.1]; simp only [evalFluxSsaNodeQ32, iha nodes hTopo]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
    have h1 := compileExprSsa_spec a nodes hTopo
    have h2 := compileExprSsa_spec b (compileExprSsa a nodes).1 h1.2.1
    obtain ⟨sfx, hsfx⟩ := h2.1
    dsimp only [compileExprSsa, evalFluxExprQ32]
    rw [internSsaNode_q32_eval ins pEnv _ _ h2.2.1]; simp only [evalFluxSsaNodeQ32, ihb _ h1.2.1]
    rw [hsfx, evalSsaNodesQ32_append,
      evalSsaNodesQ32_prefix_getD ins pEnv sfx _ _ (by rw [evalSsaNodesQ32_size]; simpa using h1.2.2.1),
      iha nodes hTopo]

private theorem compileExprListSsa_q32_eval (ins : Nat → Word) (pEnv : Nat → Rat)
    (es : List FluxExpr) (nodes : List FluxSsaNode) (hTopo : checkNodesTopological 0 nodes = true) :
    (compileExprListSsa es nodes).2.map
        (fun r => (evalSsaNodesQ32 ins pEnv (compileExprListSsa es nodes).1 #[]).getD r 0#64) =
      es.map (evalFluxExprQ32 ins pEnv) := by
  induction es generalizing nodes with
  | nil => rfl
  | cons e rest ih =>
    have h1 := compileExprSsa_spec e nodes hTopo
    obtain ⟨sfx, hsfx⟩ := (compileExprListSsa_spec rest (compileExprSsa e nodes).1 h1.2.1).1
    dsimp only [compileExprListSsa]; simp only [List.map_cons]
    have hHead : (evalSsaNodesQ32 ins pEnv (compileExprListSsa rest (compileExprSsa e nodes).1).1 #[]).getD
        (compileExprSsa e nodes).2 0#64 = evalFluxExprQ32 ins pEnv e := by
      rw [hsfx, evalSsaNodesQ32_append,
        evalSsaNodesQ32_prefix_getD ins pEnv sfx _ _ (by rw [evalSsaNodesQ32_size]; simpa using h1.2.2.1),
        compileExprSsa_q32_eval ins pEnv e nodes hTopo]
    rw [hHead, ih _ h1.2.1]

/-- **Universal CSE-to-Tree Q32.32 Equivalence (`evalFluxSsaDagQ32_compile`)**. -/
theorem evalFluxSsaDagQ32_compile (pOpt : Option (Nat → Rat)) (exprs : List FluxExpr)
    (inputs : Nat → Word) (paramEnv : Nat → Rat) :
    evalFluxSsaDagQ32 inputs paramEnv (compileFluxSsaDag pOpt exprs) =
      (exprs.map (specializeFluxExpr pOpt)).map (evalFluxExprQ32 inputs paramEnv) :=
  compileExprListSsa_q32_eval inputs paramEnv (exprs.map (specializeFluxExpr pOpt)) [] rfl

@[expose] def permuteEulerWords (shift : Nat) (inputs : Nat → Word) : Nat → Word :=
  fun i => inputs (eulerVarPerm shift i)

@[expose] def permuteEulerList {α : Type} (shift : Nat) (xs : List α) : List α :=
  match shift % 3, xs with
  | 1, [f0, f1, f2, f3, f4] => [f0, f2, f3, f1, f4]
  | 2, [f0, f1, f2, f3, f4] => [f0, f3, f1, f2, f4]
  | _, ys => ys

@[expose] def permuteEulerOutList (shift : Nat) (outs : List Word) : List Word := permuteEulerList shift outs
def swapMhdPlanarWords (inputs : Nat → Word) : Nat → Word := fun i => inputs (mhdPlanarVarSwap i)
def swapMhdPlanarList {α : Type} : List α → List α
  | [f0, f1, f2, f3, f4, f5, f6, f7, f8] => [f0, f2, f1, f3, f5, f4, f6, f7, f8]
  | xs => xs
def swapMhdPlanarOutList (outs : List Word) : List Word := swapMhdPlanarList outs
def permuteMhdWords (axis : Nat) (inputs : Nat → Word) : Nat → Word :=
  if axis % 2 == 1 then swapMhdPlanarWords inputs else inputs
def permuteMhdOutList (axis : Nat) (outs : List Word) : List Word :=
  if axis % 2 == 1 then swapMhdPlanarOutList outs else outs

private theorem permuteEulerList_map {α β : Type} (shift : Nat) (g : α → β) (xs : List α) :
    permuteEulerList shift (xs.map g) = (permuteEulerList shift xs).map g := by
  have hs : shift % 3 = 0 ∨ shift % 3 = 1 ∨ shift % 3 = 2 := by omega
  rcases hs with hs | hs | hs <;>
    (match xs with | [_, _, _, _, _] => simp [permuteEulerList, hs] | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ => simp [permuteEulerList, hs])

private theorem swapMhdPlanarList_map {α β : Type} (g : α → β) (xs : List α) :
    swapMhdPlanarList (xs.map g) = (swapMhdPlanarList xs).map g := by
  match xs with
  | [_, _, _, _, _, _, _, _, _] => rfl
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
  | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

private theorem map_evalFluxExprQ32_ac_eq (inputs : Nat → Word) (pEnv : Nat → Rat)
    (e1s e2s : List FluxExpr) (hLen : e1s.length = e2s.length)
    (hZip : (List.zipWith checkFluxAcEquiv e1s e2s).all id = true) :
    e1s.map (evalFluxExprQ32 inputs pEnv) = e2s.map (evalFluxExprQ32 inputs pEnv) := by
  induction e1s generalizing e2s with
  | nil => cases e2s with | nil => rfl | cons _ _ => simp at hLen
  | cons a as ih =>
    cases e2s with
    | nil => simp at hLen
    | cons b bs =>
      simp only [List.zipWith_cons_cons, List.all_cons, id_eq, Bool.and_eq_true] at hZip
      simp only [List.map_cons, checkFluxAcEquiv_sound_q32 a b inputs pEnv hZip.1, ih bs (by simpa using hLen) hZip.2]

private theorem map_subst_q32 (f : Nat → Nat) (inputs : Nat → Word) (pEnv : Nat → Rat) (es : List FluxExpr) :
    es.map (evalFluxExprQ32 (fun i => inputs (f i)) pEnv) =
      (es.map (substFluxVars f)).map (evalFluxExprQ32 inputs pEnv) := by
  rw [List.map_map]; exact List.map_congr_left fun e _ => (evalFluxExprQ32_substFluxVars f inputs pEnv e).symm

private theorem euler3d_q32_axis_equiv (axis : Fin 3) (inputs : Nat → Word) :
    permuteEulerOutList ((3 - axis.val) % 3)
      (evalFluxSsaDagQ32 (permuteEulerWords axis.val inputs) EulerGas3D.spec.paramEnv
        (getOr (specializeFluxSweep EulerGas3D.spec).axisFluxDags 0 ⟨[], []⟩)) =
      evalFluxSsaDagQ32 inputs EulerGas3D.spec.paramEnv
        (getOr (specializeFluxSweep EulerGas3D.spec).axisFluxDags axis.val ⟨[], []⟩) := by
  have hDagEq : ∀ d < 3, getOr (specializeFluxSweep EulerGas3D.spec).axisFluxDags d ⟨[], []⟩ =
      compileFluxSsaDag (some EulerGas3D.spec.paramEnv) (getOr EulerGas3D.spec.fluxes d []) := fun d hd => by
    have hLen : EulerGas3D.spec.fluxes.length = 3 := by decide +kernel
    exact getOr_map_lt EulerGas3D.spec.fluxes (compileFluxSsaDag (some EulerGas3D.spec.paramEnv)) d [] ⟨[], []⟩ (by omega)
  rcases axis with ⟨a, ha⟩
  match a, ha with
  | 0, _ =>
    have hw0 : permuteEulerWords 0 inputs = inputs := by funext i; simp [permuteEulerWords, eulerVarPerm]
    simp only [Nat.sub_zero, Nat.mod_self, permuteEulerOutList, permuteEulerList, hw0]
  | 1, _ =>
    rw [hDagEq 0 (by omega), hDagEq 1 (by omega), evalFluxSsaDagQ32_compile, evalFluxSsaDagQ32_compile]
    unfold permuteEulerOutList permuteEulerWords; rw [permuteEulerList_map, map_subst_q32 (eulerVarPerm 1)]
    refine map_evalFluxExprQ32_ac_eq inputs EulerGas3D.spec.paramEnv _ _ ?_ ?_ <;> (dsimp only; decide +kernel)
  | 2, _ =>
    rw [hDagEq 0 (by omega), hDagEq 2 (by omega), evalFluxSsaDagQ32_compile, evalFluxSsaDagQ32_compile]
    unfold permuteEulerOutList permuteEulerWords; rw [permuteEulerList_map, map_subst_q32 (eulerVarPerm 2)]
    refine map_evalFluxExprQ32_ac_eq inputs EulerGas3D.spec.paramEnv _ _ ?_ ?_ <;> (dsimp only; decide +kernel)

/-- **Theorem (`euler3d_single_systolic_cell_serves_all_3_axes`)**:
Zero-extra-silicon 3-axis systolic RTL reuse for `EulerGas3D`. -/
theorem euler3d_single_systolic_cell_serves_all_3_axes
    (axis : Fin 3) (inputs nextInputs regState : Nat → Word) :
    checkRtlModule (EulerGas3D.systolicRtl 0) = true ∧ (EulerGas3D.systolicRtl 0).name = "EulerGas3D_flux_axis0" ∧
    permuteEulerOutList ((3 - axis.val) % 3) ((evalModuleOutputs (EulerGas3D.systolicRtl 0) nextInputs
      (stepModuleRegs (EulerGas3D.systolicRtl 0) false (permuteEulerWords axis.val inputs) regState)).map Prod.snd) =
      evalFluxSsaDagQ32 inputs EulerGas3D.spec.paramEnv (getOr (specializeFluxSweep EulerGas3D.spec).axisFluxDags axis.val ⟨[], []⟩) ∧
    permuteEulerOutList ((3 - axis.val) % 3) ((evalModuleOutputs (EulerGas3D.systolicRtl 0) nextInputs
      (stepModuleRegs (EulerGas3D.systolicRtl 0) false (permuteEulerWords axis.val inputs) regState)).map Prod.snd) =
      (evalModuleOutputs (EulerGas3D.systolicRtl axis.val) nextInputs
        (stepModuleRegs (EulerGas3D.systolicRtl axis.val) false inputs regState)).map Prod.snd := by
  have hDims : EulerGas3D.spec.numDims = 3 := by decide +kernel
  have hR6_0 := EulerGas3D.endToEnd_certified.rung6_systolic_rtl_and_yosys_lec 0 (by omega)
  have hR6_a := EulerGas3D.endToEnd_certified.rung6_systolic_rtl_and_yosys_lec axis.val (by omega)
  have hEqQ32 : permuteEulerOutList ((3 - axis.val) % 3) ((evalModuleOutputs (EulerGas3D.systolicRtl 0) nextInputs
      (stepModuleRegs (EulerGas3D.systolicRtl 0) false (permuteEulerWords axis.val inputs) regState)).map Prod.snd) =
      evalFluxSsaDagQ32 inputs EulerGas3D.spec.paramEnv (getOr (specializeFluxSweep EulerGas3D.spec).axisFluxDags axis.val ⟨[], []⟩) := by
    change permuteEulerOutList ((3 - axis.val) % 3) ((evalModuleOutputs (buildSpecSystolicRtl EulerGas3D.spec 0) nextInputs
      (stepModuleRegs (buildSpecSystolicRtl EulerGas3D.spec 0) false (permuteEulerWords axis.val inputs) regState)).map Prod.snd) = _
    rw [hR6_0.2.2 (permuteEulerWords axis.val inputs) nextInputs regState]; exact euler3d_q32_axis_equiv axis inputs
  exact ⟨hR6_0.1, by decide +kernel, hEqQ32, hEqQ32.trans (hR6_a.2.2 inputs nextInputs regState).symm⟩

private theorem mhd8wave_q32_axis_equiv (axis : Fin 2) (inputs : Nat → Word) :
    permuteMhdOutList axis.val (evalFluxSsaDagQ32 (permuteMhdWords axis.val inputs) IdealMhd8Wave.spec.paramEnv
      (getOr (specializeFluxSweep IdealMhd8Wave.spec).axisFluxDags 0 ⟨[], []⟩)) =
      evalFluxSsaDagQ32 inputs IdealMhd8Wave.spec.paramEnv (getOr (specializeFluxSweep IdealMhd8Wave.spec).axisFluxDags axis.val ⟨[], []⟩) := by
  have hDagEq : ∀ d < 2, getOr (specializeFluxSweep IdealMhd8Wave.spec).axisFluxDags d ⟨[], []⟩ =
      compileFluxSsaDag (some IdealMhd8Wave.spec.paramEnv) (getOr IdealMhd8Wave.spec.fluxes d []) := fun d hd => by
    have hLen : IdealMhd8Wave.spec.fluxes.length = 2 := by decide +kernel
    exact getOr_map_lt IdealMhd8Wave.spec.fluxes (compileFluxSsaDag (some IdealMhd8Wave.spec.paramEnv)) d [] ⟨[], []⟩ (by omega)
  rcases axis with ⟨a, ha⟩
  match a, ha with
  | 0, _ => rfl
  | 1, _ =>
    rw [hDagEq 0 (by omega), hDagEq 1 (by omega), evalFluxSsaDagQ32_compile, evalFluxSsaDagQ32_compile]
    simp only [permuteMhdOutList, swapMhdPlanarOutList, permuteMhdWords, beq_self_eq_true, ↓reduceIte]
    unfold swapMhdPlanarWords; rw [swapMhdPlanarList_map, map_subst_q32 mhdPlanarVarSwap]
    refine map_evalFluxExprQ32_ac_eq inputs IdealMhd8Wave.spec.paramEnv _ _ ?_ ?_ <;> decide +kernel

/-- **Theorem (`mhd8wave_single_systolic_cell_serves_both_axes`)**:
Zero-extra-silicon 2-axis systolic RTL reuse for 9-component `IdealMhd8Wave`. -/
theorem mhd8wave_single_systolic_cell_serves_both_axes
    (axis : Fin 2) (inputs nextInputs regState : Nat → Word) :
    checkRtlModule (IdealMhd8Wave.systolicRtl 0) = true ∧ (IdealMhd8Wave.systolicRtl 0).name = "IdealMhd8Wave_flux_axis0" ∧
    permuteMhdOutList axis.val ((evalModuleOutputs (IdealMhd8Wave.systolicRtl 0) nextInputs
      (stepModuleRegs (IdealMhd8Wave.systolicRtl 0) false (permuteMhdWords axis.val inputs) regState)).map Prod.snd) =
      evalFluxSsaDagQ32 inputs IdealMhd8Wave.spec.paramEnv (getOr (specializeFluxSweep IdealMhd8Wave.spec).axisFluxDags axis.val ⟨[], []⟩) ∧
    permuteMhdOutList axis.val ((evalModuleOutputs (IdealMhd8Wave.systolicRtl 0) nextInputs
      (stepModuleRegs (IdealMhd8Wave.systolicRtl 0) false (permuteMhdWords axis.val inputs) regState)).map Prod.snd) =
      (evalModuleOutputs (IdealMhd8Wave.systolicRtl axis.val) nextInputs
        (stepModuleRegs (IdealMhd8Wave.systolicRtl axis.val) false inputs regState)).map Prod.snd := by
  have hDims : IdealMhd8Wave.spec.numDims = 2 := by decide +kernel
  have hR6_0 := IdealMhd8Wave.endToEnd_certified.rung6_systolic_rtl_and_yosys_lec 0 (by omega)
  have hR6_a := IdealMhd8Wave.endToEnd_certified.rung6_systolic_rtl_and_yosys_lec axis.val (by omega)
  have hEqQ32 : permuteMhdOutList axis.val ((evalModuleOutputs (IdealMhd8Wave.systolicRtl 0) nextInputs
      (stepModuleRegs (IdealMhd8Wave.systolicRtl 0) false (permuteMhdWords axis.val inputs) regState)).map Prod.snd) =
      evalFluxSsaDagQ32 inputs IdealMhd8Wave.spec.paramEnv (getOr (specializeFluxSweep IdealMhd8Wave.spec).axisFluxDags axis.val ⟨[], []⟩) := by
    change permuteMhdOutList axis.val ((evalModuleOutputs (buildSpecSystolicRtl IdealMhd8Wave.spec 0) nextInputs
      (stepModuleRegs (buildSpecSystolicRtl IdealMhd8Wave.spec 0) false (permuteMhdWords axis.val inputs) regState)).map Prod.snd) = _
    rw [hR6_0.2.2 (permuteMhdWords axis.val inputs) nextInputs regState]; exact mhd8wave_q32_axis_equiv axis inputs
  exact ⟨hR6_0.1, by decide +kernel, hEqQ32, hEqQ32.trans (hR6_a.2.2 inputs nextInputs regState).symm⟩

/-! ## 4. Open-Hypergraph Lowering of `FluxSsaDag` & `Analysis.Equitable` Invariant Sub-DAGs -/

def ssaNodeToHyperEdge (numVars idx : Nat) : FluxSsaNode → HyperEdge
  | .const q => { opIdx := idx, op := .const (q.num / (q.den : Int)), srcWires := [], dstWire := numVars + idx }
  | .var i => { opIdx := idx, op := .scale 1, srcWires := [i], dstWire := numVars + idx }
  | .neg a => { opIdx := idx, op := .scale (-1), srcWires := [numVars + a], dstWire := numVars + idx }
  | .add a b => { opIdx := idx, op := .add, srcWires := [numVars + a, numVars + b], dstWire := numVars + idx }
  | .sub a b => { opIdx := idx, op := .sub, srcWires := [numVars + a, numVars + b], dstWire := numVars + idx }
  | .mul a b => { opIdx := idx, op := .mul, srcWires := [numVars + a, numVars + b], dstWire := numVars + idx }
  | .param _ | .invSafe _ => { opIdx := idx, op := .const 0, srcWires := [], dstWire := numVars + idx }

def ssaNodesToHyperEdges (numVars : Nat) : Nat → List FluxSsaNode → List HyperEdge
  | _, [] => []
  | idx, n :: rest => ssaNodeToHyperEdge numVars idx n :: ssaNodesToHyperEdges numVars (idx + 1) rest

/-- Lower a `FluxSsaDag` over `numVars` state variables into a data-parallel `StrictOpenHypergraph`. -/
@[expose] def fluxSsaDagToOpenHypergraph (numVars : Nat) (dag : FluxSsaDag) : StrictOpenHypergraph :=
  mkStrictOpenHypergraph (numVars + dag.nodes.length) (List.range numVars)
    (dag.roots.map (fun r => numVars + r)) (ssaNodesToHyperEdges numVars 0 dag.nodes)

def isPolyFluxSsaNode : FluxSsaNode → Bool
  | .const q => q.den == 1 | .var _ | .neg _ | .add _ _ | .sub _ _ | .mul _ _ => true | .param _ | .invSafe _ => false

def isPolyFluxSsaDag (numVars : Nat) (dag : FluxSsaDag) : Bool :=
  checkFluxSsaDag dag &&
  dag.nodes.all fun n => isPolyFluxSsaNode n && match n with | .var i => decide (i < numVars) | _ => true

private theorem foldl_add_shift (init : Nat) (xs : List Nat) : xs.foldl (· + ·) init = init + xs.foldl (· + ·) 0 := by
  induction xs generalizing init with | nil => simp | cons x _ ih => simp only [List.foldl_cons, Nat.zero_add]; rw [ih (init + x), ih x]; omega
private theorem sumNatList_map_length (segs : List (List Nat)) : sumNatList (segs.map List.length) = segs.flatten.length := by
  induction segs with | nil => rfl | cons s _ ih =>
    simp only [sumNatList, List.map_cons, List.foldl_cons, Nat.zero_add, List.flatten_cons, List.length_append]; rw [foldl_add_shift]; exact congrArg (s.length + ·) ih
private theorem mem_flatten_len_le {α : Type} (segs : List (List α)) (s : List α) (hs : s ∈ segs) : s.length ≤ segs.flatten.length := by
  induction segs with | nil => cases hs | cons _ _ ih =>
    rcases List.mem_cons.mp hs with rfl | hmem <;> (try have := ih hmem) <;> simp only [List.flatten_cons, List.length_append] <;> omega
private theorem fromSegments_wf (numWires : Nat) (segs : List (List Nat))
    (hW : ∀ s ∈ segs, ∀ w ∈ s, w < numWires) : (IndexedCoproduct.fromSegments numWires segs).wf = true := by
  unfold IndexedCoproduct.wf IndexedCoproduct.fromSegments FiniteFunction.wf
  simp only [List.length_map, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, (sumNatList_map_length segs).symm⟩
  · intro _ hl; obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl; have := mem_flatten_len_le segs s hs; omega
  · intro w hw; obtain ⟨s, hs, hws⟩ := List.mem_flatten.mp hw; exact hW s hs w hws

private theorem ssaNodesToHyperEdges_bounds (numVars idx total : Nat) (ns : List FluxSsaNode)
    (hLen : idx + ns.length ≤ total) (hTopo : checkNodesTopological idx ns = true)
    (hVars : ∀ i, FluxSsaNode.var i ∈ ns → i < numVars) :
    ∀ e ∈ ssaNodesToHyperEdges numVars idx ns, e.dstWire < numVars + total ∧ ∀ w ∈ e.srcWires, w < numVars + total := by
  induction ns generalizing idx with
  | nil => intro _ he; cases he
  | cons n rest ih =>
    simp only [checkNodesTopological, Bool.and_eq_true] at hTopo
    intro e he
    rcases List.mem_cons.mp he with rfl | heRest
    · simp only [List.length_cons] at hLen
      cases n with
      | const _ | param _ | invSafe _ => simp only [ssaNodeToHyperEdge, List.not_mem_nil, false_implies, implies_true, and_true]; omega
      | var i => have hi := hVars i List.mem_cons_self; simp only [ssaNodeToHyperEdge, List.mem_singleton]; exact ⟨by omega, fun _ hw => by subst hw; omega⟩
      | neg a => simp only [checkSsaNodeBound, decide_eq_true_eq] at hTopo; simp only [ssaNodeToHyperEdge, List.mem_singleton]; exact ⟨by omega, fun _ hw => by subst hw; omega⟩
      | add a b | sub a b | mul a b =>
        simp only [checkSsaNodeBound, Bool.and_eq_true, decide_eq_true_eq] at hTopo
        simp only [ssaNodeToHyperEdge, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨by omega, fun _ hw => by rcases hw with rfl | rfl <;> omega⟩
    · exact ih (idx + 1) (by simp only [List.length_cons] at hLen; omega) hTopo.2 (fun i hi => hVars i (List.mem_cons_of_mem _ hi)) e heRest

/-- **Theorem (`fluxSsaDagToOpenHypergraph_wf`)**:
Every topological `FluxSsaDag` with `var` indices `< numVars` lowers to a well-formed `StrictOpenHypergraph`. -/
theorem fluxSsaDagToOpenHypergraph_wf (numVars : Nat) (dag : FluxSsaDag)
    (hDag : checkFluxSsaDag dag = true) (hVars : ∀ i, FluxSsaNode.var i ∈ dag.nodes → i < numVars) :
    (fluxSsaDagToOpenHypergraph numVars dag).wf = true := by
  simp only [checkFluxSsaDag, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hDag
  have hEdges := ssaNodesToHyperEdges_bounds numVars 0 dag.nodes.length dag.nodes (by omega) hDag.1 hVars
  have hSrcWf : (IndexedCoproduct.fromSegments (numVars + dag.nodes.length) ((ssaNodesToHyperEdges numVars 0 dag.nodes).map (·.srcWires))).wf = true :=
    fromSegments_wf _ _ fun _ hs w hw => by obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs; exact (hEdges e he).2 w hw
  have hTgtWf : (IndexedCoproduct.fromSegments (numVars + dag.nodes.length) ((ssaNodesToHyperEdges numVars 0 dag.nodes).map (fun e => [e.dstWire]))).wf = true :=
    fromSegments_wf _ _ fun _ hs w hw => by obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs; rw [List.mem_singleton] at hw; subst hw; exact (hEdges e he).1
  unfold fluxSsaDagToOpenHypergraph mkStrictOpenHypergraph StrictOpenHypergraph.wf; dsimp only; rw [hSrcWf, hTgtWf]
  simp only [Bool.true_and, Bool.and_eq_true, List.length_replicate, List.length_map, IndexedCoproduct.fromSegments, beq_self_eq_true, and_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold FiniteFunction.wf; simp only [List.length_range, beq_self_eq_true, Bool.true_and, List.all_eq_true, decide_eq_true_eq]
    intro _ hy; have := List.mem_range.mp hy; omega
  · simp only [List.all_eq_true, beq_iff_eq]; intro _ hl; obtain ⟨_, hs, rfl⟩ := List.mem_map.mp hl; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs; rfl
  · unfold FiniteFunction.wf; simp only [List.length_map, beq_self_eq_true, Bool.true_and, List.all_eq_true, decide_eq_true_eq]
    intro _ hy; obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy; have := hDag.2 r hr; omega

private theorem extractHyperEdgesAux_mk (idx : Nat) (edges : List HyperEdge)
    (hIdx : ∀ k, k < edges.length → (getOr edges k { opIdx := 0, op := .add, srcWires := [], dstWire := 0 }).opIdx = idx + k) :
    extractHyperEdgesAux idx (edges.map (·.op)) ((edges.map (·.srcWires)).map List.length)
      (edges.map (·.srcWires)).flatten (edges.map (fun e => [e.dstWire])).flatten = edges := by
  induction edges generalizing idx with
  | nil => rfl
  | cons e rest ih =>
    have h0 := hIdx 0 (by simp); simp only [getOr, Nat.add_zero] at h0
    simp only [List.map_cons, List.flatten_cons, List.singleton_append, extractHyperEdgesAux, List.take_left, List.drop_left]
    have heEq : { opIdx := idx, op := e.op, srcWires := e.srcWires, dstWire := e.dstWire : HyperEdge } = e := by
      cases e; simp only [HyperEdge.mk.injEq, and_true]; exact h0.symm
    rw [heEq]; refine congrArg (e :: ·) (ih (idx + 1) fun k hk => ?_)
    simpa [getOr, Nat.add_assoc, Nat.add_comm 1] using hIdx (k + 1) (by simp; omega)

private theorem ssaNodesToHyperEdges_opIdx (numVars idx : Nat) (ns : List FluxSsaNode) :
    ∀ k, k < (ssaNodesToHyperEdges numVars idx ns).length →
      (getOr (ssaNodesToHyperEdges numVars idx ns) k { opIdx := 0, op := .add, srcWires := [], dstWire := 0 }).opIdx = idx + k := by
  induction ns generalizing idx with
  | nil => intro _ hk; simp [ssaNodesToHyperEdges] at hk
  | cons n rest ih =>
    intro k hk; cases k with
    | zero => cases n <;> simp [ssaNodesToHyperEdges, ssaNodeToHyperEdge, getOr]
    | succ k' =>
      have hSub := ih (idx + 1) k' (by simpa [ssaNodesToHyperEdges] using hk)
      simpa [ssaNodesToHyperEdges, getOr, Nat.add_assoc, Nat.add_comm 1] using hSub

theorem extractHyperEdges_fluxSsaDag (numVars : Nat) (dag : FluxSsaDag) :
    extractHyperEdges (fluxSsaDagToOpenHypergraph numVars dag) = ssaNodesToHyperEdges numVars 0 dag.nodes := by
  unfold extractHyperEdges fluxSsaDagToOpenHypergraph mkStrictOpenHypergraph IndexedCoproduct.fromSegments
  exact extractHyperEdgesAux_mk 0 _ (ssaNodesToHyperEdges_opIdx numVars 0 dag.nodes)

private theorem rat_of_den_one (q : Rat) (h : q.den = 1) : ((q.num : Int) : Rat) = q := by
  cases q with | mk' num den den_nz reduced => simp only at h; subst h; rfl

private theorem evalHyperEdgesComb_ssa_step (numVars : Nat) (initEnv : Nat → Int) (pEnv : Nat → Rat)
    (ns : List FluxSsaNode) (env : Nat → Int) (acc : List Rat)
    (hTopo : checkNodesTopological acc.length ns = true)
    (hPoly : ns.all (fun n => isPolyFluxSsaNode n && match n with | .var i => decide (i < numVars) | _ => true) = true)
    (hIn : ∀ i < numVars, env i = initEnv i) (hAcc : ∀ j < acc.length, (env (numVars + j) : Rat) = getOr acc j 0) :
    let finalEnv := evalHyperEdgesComb env (ssaNodesToHyperEdges numVars acc.length ns)
    let finalVals := evalSsaNodes ⟨fun i => (initEnv i : Rat), pEnv⟩ ns acc
    (∀ i < numVars, finalEnv i = initEnv i) ∧ (∀ j < finalVals.length, (finalEnv (numVars + j) : Rat) = getOr finalVals j 0) := by
  induction ns generalizing env acc with
  | nil => exact ⟨hIn, hAcc⟩
  | cons n rest ih =>
    simp only [checkNodesTopological, List.all_cons, Bool.and_eq_true] at hTopo hPoly
    let e := ssaNodeToHyperEdge numVars acc.length n; let env' := stepHyperEdge env e
    let vRat := evalSsaNodeStep ⟨fun i => (initEnv i : Rat), pEnv⟩ acc n
    have hDst : e.dstWire = numVars + acc.length := by cases n <;> rfl
    have hStepVal : (env' (numVars + acc.length) : Rat) = vRat := by
      have hEvalAt : env' (numVars + acc.length) = evalHypergraphOp e.op (e.srcWires.map env) := by simp [env', stepHyperEdge, hDst]
      rw [hEvalAt]
      cases n with
      | const q =>
        have hDen : q.den = 1 := of_decide_eq_true hPoly.1.1
        have hDiv : q.num / (q.den : Int) = q.num := by rw [hDen]; exact Int.ediv_one _
        simp only [e, ssaNodeToHyperEdge, evalHypergraphOp, vRat, evalSsaNodeStep, hDiv]; exact rat_of_den_one q hDen
      | var i =>
        have hi : i < numVars := of_decide_eq_true hPoly.1.2
        simp only [e, ssaNodeToHyperEdge, List.map_cons, List.map_nil, evalHypergraphOp, List.getD_cons_zero, Int.one_mul, hIn i hi, vRat, evalSsaNodeStep]
      | neg a =>
        have ha : a < acc.length := of_decide_eq_true hTopo.1
        simp only [e, ssaNodeToHyperEdge, List.map_cons, List.map_nil, evalHypergraphOp, List.getD_cons_zero, Int.neg_mul, Int.one_mul, Rat.intCast_neg, hAcc a ha, vRat, evalSsaNodeStep]
      | add a b =>
        simp only [checkSsaNodeBound, Bool.and_eq_true, decide_eq_true_eq] at hTopo
        simp only [e, ssaNodeToHyperEdge, List.map_cons, List.map_nil, evalHypergraphOp, List.getD_cons_zero, List.getD_cons_succ, Rat.intCast_add, hAcc a hTopo.1.1, hAcc b hTopo.1.2, vRat, evalSsaNodeStep]
      | sub a b =>
        simp only [checkSsaNodeBound, Bool.and_eq_true, decide_eq_true_eq] at hTopo
        simp only [e, ssaNodeToHyperEdge, List.map_cons, List.map_nil, evalHypergraphOp, List.getD_cons_zero, List.getD_cons_succ, Rat.intCast_sub, hAcc a hTopo.1.1, hAcc b hTopo.1.2, vRat, evalSsaNodeStep]
      | mul a b =>
        simp only [checkSsaNodeBound, Bool.and_eq_true, decide_eq_true_eq] at hTopo
        simp only [e, ssaNodeToHyperEdge, List.map_cons, List.map_nil, evalHypergraphOp, List.getD_cons_zero, List.getD_cons_succ, Rat.intCast_mul, hAcc a hTopo.1.1, hAcc b hTopo.1.2, vRat, evalSsaNodeStep]
      | param _ | invSafe _ => simp [isPolyFluxSsaNode] at hPoly
    have hIn' : ∀ i < numVars, env' i = initEnv i := fun i hi => by
      simp only [env', stepHyperEdge, beq_false_of_ne (by omega : i ≠ e.dstWire), Bool.false_eq_true, ↓reduceIte, hIn i hi]
    have hAcc' : ∀ j < (acc ++ [vRat]).length, (env' (numVars + j) : Rat) = getOr (acc ++ [vRat]) j 0 := fun j hj => by
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < acc.length
      · simp only [env', stepHyperEdge, beq_false_of_ne (by omega : numVars + j ≠ e.dstWire), Bool.false_eq_true, ↓reduceIte, hAcc j hlt, getOr_append_left acc [vRat] j 0 hlt]
      · have hEq : j = acc.length := by omega
        subst hEq; rw [hStepVal, getOr_snoc_self]
    simpa [ssaNodesToHyperEdges, evalHyperEdgesComb, evalSsaNodes, e, env', vRat] using
      ih env' (acc ++ [vRat]) (by simpa using hTopo.2) hPoly.2 hIn' hAcc'

/-- **Theorem (`fluxSsaDagToOpenHypergraph_sound`)**:
For every integer-polynomial `FluxSsaDag`, its lowered `StrictOpenHypergraph` is well-formed,
conflict-free under `layerHypergraph`, satisfies `evalHypergraphLayeredSync = evalHypergraphComb`,
and agrees identically with `evalFluxSsaDag` over `Rat`. -/
theorem fluxSsaDagToOpenHypergraph_sound (numVars : Nat) (dag : FluxSsaDag)
    (hPoly : isPolyFluxSsaDag numVars dag = true) (initEnv : Nat → Int) (pEnv : Nat → Rat) :
    let g := fluxSsaDagToOpenHypergraph numVars dag
    g.wf = true ∧ (layerHypergraph g).all checkStageIndependent = true ∧
    evalHypergraphLayeredSync g initEnv = evalHypergraphComb g initEnv ∧
    (evalHypergraphLayeredSync g initEnv).map (fun z : Int => (z : Rat)) =
      evalFluxSsaDag dag ⟨fun i => (initEnv i : Rat), pEnv⟩ := by
  simp only [isPolyFluxSsaDag, Bool.and_eq_true] at hPoly
  obtain ⟨hDag, hNodesPoly⟩ := hPoly
  have hVars : ∀ i, FluxSsaNode.var i ∈ dag.nodes → i < numVars := fun i hi => by
    have hAll := List.all_eq_true.mp hNodesPoly (.var i) hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAll; exact hAll.2
  have hWf := fluxSsaDagToOpenHypergraph_wf numVars dag hDag hVars
  have hLayer := layerHypergraph_sound (fluxSsaDagToOpenHypergraph numVars dag) initEnv
  have hPipe := evalHypergraph_pipelined_eq_comb (fluxSsaDagToOpenHypergraph numVars dag) initEnv
  refine ⟨hWf, hLayer.1, hPipe.2, ?_⟩
  rw [hPipe.2]; unfold evalHypergraphComb evalFluxSsaDag; rw [extractHyperEdges_fluxSsaDag]
  simp only [checkFluxSsaDag, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hDag
  have hStep := evalHyperEdgesComb_ssa_step numVars initEnv pEnv dag.nodes initEnv []
    (by simpa using hDag.1) hNodesPoly (fun _ _ => rfl) (fun _ h => by simp at h)
  have hOut : (fluxSsaDagToOpenHypergraph numVars dag).boundaryOut.table = dag.roots.map (fun r => numVars + r) := rfl
  rw [hOut, List.map_map, List.map_map]
  refine List.map_congr_left fun r hr => hStep.2 r (by rw [evalSsaNodes_length]; simpa using hDag.2 r hr)

/-! ## 5. Shared $S_3$-Invariant Quadratic Sub-DAGs & `Analysis.Equitable` Quotient Intertwining -/

def quadNorm3Expr (a b c : Nat) : FluxExpr :=
  .add (.add (.mul (.var a) (.var a)) (.mul (.var b) (.var b))) (.mul (.var c) (.var c))

def momentumNormSqDag : FluxSsaDag := compileFluxSsaDag none [quadNorm3Expr 0 1 2]
def mhdMagneticNormSqDag : FluxSsaDag := compileFluxSsaDag none [quadNorm3Expr 4 5 6]
def mhdCombinedQuadEnergyDag : FluxSsaDag := compileFluxSsaDag none [.add (quadNorm3Expr 1 2 3) (quadNorm3Expr 4 5 6)]
def momentumNormSqHypergraph : StrictOpenHypergraph := fluxSsaDagToOpenHypergraph 3 momentumNormSqDag
def mhdMagneticNormSqHypergraph : StrictOpenHypergraph := fluxSsaDagToOpenHypergraph 9 mhdMagneticNormSqDag
def mhdCombinedQuadHypergraph : StrictOpenHypergraph := fluxSsaDagToOpenHypergraph 9 mhdCombinedQuadEnergyDag

/-- Action of all 6 elements of $S_3$ on `(u0, u1, u2)`. -/
def applyPerm3 (p : Fin 6) (u0 u1 u2 : Int) (i : Nat) : Int :=
  match p.val, i with
  | 0, 0 => u0 | 0, 1 => u1 | 0, 2 => u2
  | 1, 0 => u0 | 1, 1 => u2 | 1, 2 => u1
  | 2, 0 => u1 | 2, 1 => u0 | 2, 2 => u2
  | 3, 0 => u1 | 3, 1 => u2 | 3, 2 => u0
  | 4, 0 => u2 | 4, 1 => u0 | 4, 2 => u1
  | 5, 0 => u2 | 5, 1 => u1 | 5, 2 => u0
  | _, _ => 0

def embedPerm3At (off : Nat) (p : Fin 6) (u0 u1 u2 : Int) (base : Nat → Int) : Nat → Int :=
  fun i => if off ≤ i && i < off + 3 then applyPerm3 p u0 u1 u2 (i - off) else base i

private theorem list_int_eq_of_map_rat {xs ys : List Int}
    (h : xs.map (fun z : Int => (z : Rat)) = ys.map (fun z : Int => (z : Rat))) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp at h
  | cons _ _ ih => cases ys with | nil => simp at h | cons _ _ => simp only [List.map_cons, List.cons.injEq] at h; rw [Rat.intCast_inj.mp h.1, ih h.2]

private theorem quadNorm3_perm3_rat (p : Fin 6) (u0 u1 u2 : Int) :
    ((applyPerm3 p u0 u1 u2 0 : Rat) * (applyPerm3 p u0 u1 u2 0 : Rat) +
      (applyPerm3 p u0 u1 u2 1 : Rat) * (applyPerm3 p u0 u1 u2 1 : Rat)) +
      (applyPerm3 p u0 u1 u2 2 : Rat) * (applyPerm3 p u0 u1 u2 2 : Rat) =
    ((u0 * u0 + u1 * u1 + u2 * u2 : Int) : Rat) := by
  rcases p with ⟨k, hk⟩
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp only [applyPerm3, Rat.intCast_add, Rat.intCast_mul]; try grind

/-- **Theorem (`momentumNormSq_hypergraph_s3_invariant`)**:
Synchronous layered evaluation of the shared momentum-norm open hypergraph is well-formed,
conflict-free, and strictly $S_3$-invariant across all `(u0, u1, u2 : Int)`. -/
theorem momentumNormSq_hypergraph_s3_invariant (p : Fin 6) (u0 u1 u2 : Int) :
    momentumNormSqHypergraph.wf = true ∧
    (layerHypergraph momentumNormSqHypergraph).all checkStageIndependent = true ∧
    evalHypergraphLayeredSync momentumNormSqHypergraph (applyPerm3 p u0 u1 u2) = [u0 * u0 + u1 * u1 + u2 * u2] := by
  have hSound := fluxSsaDagToOpenHypergraph_sound 3 momentumNormSqDag (by decide +kernel) (applyPerm3 p u0 u1 u2) (fun _ => 0)
  refine ⟨hSound.1, hSound.2.1, list_int_eq_of_map_rat ?_⟩
  change (evalHypergraphLayeredSync (fluxSsaDagToOpenHypergraph 3 momentumNormSqDag) _).map _ = _
  rw [hSound.2.2.2]
  have hComp := (compileFluxSsaDag_sound none [quadNorm3Expr 0 1 2]).2.2 ⟨fun i => (applyPerm3 p u0 u1 u2 i : Rat), fun _ => 0⟩ trivial
  rw [show momentumNormSqDag = compileFluxSsaDag none [quadNorm3Expr 0 1 2] from rfl, hComp]
  simp only [List.map_cons, List.map_nil, quadNorm3Expr, evalFlux]
  exact congrArg (fun x => [x]) (quadNorm3_perm3_rat p u0 u1 u2)

/-- **Theorem (`mhd_quadratic_subdags_s3_invariant`)**:
Both `mhdMagneticNormSqHypergraph` and `mhdCombinedQuadHypergraph` are well-formed and invariant
under arbitrary $S_3 \times S_3$ permutations of momentum and magnetic field triples. -/
theorem mhd_quadratic_subdags_s3_invariant (pM pB : Fin 6) (rhou rhov rhow bx by_ bz : Int) :
    mhdMagneticNormSqHypergraph.wf = true ∧ mhdCombinedQuadHypergraph.wf = true ∧
    evalHypergraphLayeredSync mhdMagneticNormSqHypergraph (embedPerm3At 4 pB bx by_ bz (fun _ => 0)) =
      [bx * bx + by_ * by_ + bz * bz] ∧
    evalHypergraphLayeredSync mhdCombinedQuadHypergraph
      (embedPerm3At 4 pB bx by_ bz (embedPerm3At 1 pM rhou rhov rhow (fun _ => 0))) =
      [(rhou * rhou + rhov * rhov + rhow * rhow) + (bx * bx + by_ * by_ + bz * bz)] := by
  have hB := fluxSsaDagToOpenHypergraph_sound 9 mhdMagneticNormSqDag (by decide +kernel) (embedPerm3At 4 pB bx by_ bz (fun _ => 0)) (fun _ => 0)
  have hC := fluxSsaDagToOpenHypergraph_sound 9 mhdCombinedQuadEnergyDag (by decide +kernel)
    (embedPerm3At 4 pB bx by_ bz (embedPerm3At 1 pM rhou rhov rhow (fun _ => 0))) (fun _ => 0)
  refine ⟨hB.1, hC.1, list_int_eq_of_map_rat ?_, list_int_eq_of_map_rat ?_⟩
  · change (evalHypergraphLayeredSync (fluxSsaDagToOpenHypergraph 9 mhdMagneticNormSqDag) _).map _ = _
    rw [hB.2.2.2]
    have hComp := (compileFluxSsaDag_sound none [quadNorm3Expr 4 5 6]).2.2
      ⟨fun i => (embedPerm3At 4 pB bx by_ bz (fun _ => 0) i : Rat), fun _ => 0⟩ trivial
    rw [show mhdMagneticNormSqDag = compileFluxSsaDag none [quadNorm3Expr 4 5 6] from rfl, hComp]
    simp only [List.map_cons, List.map_nil, quadNorm3Expr, evalFlux, embedPerm3At]
    exact congrArg (fun x => [x]) (quadNorm3_perm3_rat pB bx by_ bz)
  · change (evalHypergraphLayeredSync (fluxSsaDagToOpenHypergraph 9 mhdCombinedQuadEnergyDag) _).map _ = _
    rw [hC.2.2.2]
    have hComp := (compileFluxSsaDag_sound none [.add (quadNorm3Expr 1 2 3) (quadNorm3Expr 4 5 6)]).2.2
      ⟨fun i => (embedPerm3At 4 pB bx by_ bz (embedPerm3At 1 pM rhou rhov rhow (fun _ => 0)) i : Rat), fun _ => 0⟩ trivial
    rw [show mhdCombinedQuadEnergyDag = compileFluxSsaDag none [.add (quadNorm3Expr 1 2 3) (quadNorm3Expr 4 5 6)] from rfl, hComp]
    simp only [List.map_cons, List.map_nil, quadNorm3Expr, evalFlux, embedPerm3At]
    refine congrArg (fun x => [x]) ?_
    rw [Rat.intCast_add, ← quadNorm3_perm3_rat pM rhou rhov rhow, ← quadNorm3_perm3_rat pB bx by_ bz]; rfl

/-- Symmetric 7×7 incidence `IntMatrix`: inputs `{0,1,2}`, squaring hyperedges `{3,4,5}`, sum root `{6}`. -/
def quadInvariantIncidenceMatrix : IntMatrix where
  dim := 7
  rows :=
    [ [0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0]
    , [2, 0, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1]
    , [0, 0, 0, 1, 1, 1, 0] ]

def quadOrbitPart (u : Nat) : Nat := if u < 3 then 0 else if u < 6 then 1 else 2

def quadOrbitQuotient (i j : Nat) : Int :=
  if i == 0 && j == 1 then 2 else if i == 1 && j == 0 then 2
  else if i == 1 && j == 2 then 1 else if i == 2 && j == 1 then 3 else 0

/-- **Theorem (`quadInvariant_equitable_quotient_intertwining`)**:
Certifies symmetry, equitable partition (`checkEquitablePartition`), 1-WL stability
(`checkWl1ColorRefinementStable`), handshake symmetrizability, and universal quotient intertwining. -/
theorem quadInvariant_equitable_quotient_intertwining (w : Nat → Int) (u : Nat) (hu : u < 7) :
    quadInvariantIncidenceMatrix.isSymmetric = true ∧
    checkEquitablePartition quadInvariantIncidenceMatrix 3 quadOrbitPart quadOrbitQuotient = true ∧
    checkWl1ColorRefinementStable quadInvariantIncidenceMatrix 3 quadOrbitPart = true ∧
    checkHandshakeIdentity 7 3 quadOrbitPart quadOrbitQuotient = true ∧
    matVec (List.range quadInvariantIncidenceMatrix.dim) quadInvariantIncidenceMatrix.entry
        (liftQuotientVec quadOrbitPart w) u =
      liftQuotientVec quadOrbitPart (quotientMatVec quadOrbitQuotient (List.range 3) w) u := by
  have hSym : quadInvariantIncidenceMatrix.isSymmetric = true := by decide +kernel
  have hEq : checkEquitablePartition quadInvariantIncidenceMatrix 3 quadOrbitPart quadOrbitQuotient = true := by decide +kernel
  have hWl1 : checkWl1ColorRefinementStable quadInvariantIncidenceMatrix 3 quadOrbitPart = true := by decide +kernel
  have hHs : checkHandshakeIdentity 7 3 quadOrbitPart quadOrbitQuotient = true := by decide +kernel
  exact ⟨hSym, hEq, hWl1, hHs,
    equitable_intertwining_step_unpartitioned quadInvariantIncidenceMatrix 3 quadOrbitPart quadOrbitQuotient w u hEq hu⟩

/-! ## 6. Anisotropic & Mismatched-Permutation Negative Witnesses (`#tooth` & `example`) -/

def anisoQuadExpr : FluxExpr :=
  .add (.add (.mul (.const 2) (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))

def anisoQuadIncidenceMatrix : IntMatrix where
  dim := 7
  rows :=
    [ [0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 0, 2, 0]
    , [2, 0, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1]
    , [0, 0, 0, 2, 1, 1, 0] ]

-- Negative witness 1: anisotropic weight breaks both `checkEquitablePartition` and 1-WL stability.
example :
    checkEquitablePartition anisoQuadIncidenceMatrix 3 quadOrbitPart quadOrbitQuotient = false ∧
    checkWl1ColorRefinementStable anisoQuadIncidenceMatrix 3 quadOrbitPart = false := by decide +kernel

-- Negative witness 2: anisotropic quadratic sub-DAG breaks $S_3$ invariance on `(1,0,0)` vs `(0,1,0)`.
example :
    let g := fluxSsaDagToOpenHypergraph 3 (compileFluxSsaDag none [anisoQuadExpr])
    evalHypergraphLayeredSync g (applyPerm3 ⟨0, by omega⟩ 1 0 0) ≠
      evalHypergraphLayeredSync g (applyPerm3 ⟨2, by omega⟩ 1 0 0) := by decide +kernel

-- Negative witness 3: mismatched output permutation breaks `EulerGas3D` rational equivariance (`0 ≠ 2`).
example :
    let U : Vec := fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | _ => 0
    evalSpecAxisFlux EulerGas3D.spec 1 U 1 ≠
      permuteEulerVec 1 (evalSpecAxisFlux EulerGas3D.spec 0 (permuteEulerVec 1 U)) 1 := by
  dsimp only
  simp [evalSpecAxisFlux, EulerGas3D.spec, permuteEulerVec, eulerVarPerm, getOr, evalFlux]
  grind

-- Negative witness 4: mismatched output permutation breaks `EulerGas3D` Q32 systolic reuse.
example :
    let ins : Nat → Word := fun | 0 => ratToQ32Word 1 | 1 => ratToQ32Word 1 | 4 => ratToQ32Word 2 | _ => 0#64
    let dag0 := getOr (specializeFluxSweep EulerGas3D.spec).axisFluxDags 0 ⟨[], []⟩
    let dag1 := getOr (specializeFluxSweep EulerGas3D.spec).axisFluxDags 1 ⟨[], []⟩
    permuteEulerOutList 1 (evalFluxSsaDagQ32 (permuteEulerWords 1 ins) EulerGas3D.spec.paramEnv dag0) ≠
      evalFluxSsaDagQ32 ins EulerGas3D.spec.paramEnv dag1 := by decide +kernel

-- `#tooth` mutation witnesses: mutating `eulerVarPerm` or `quadOrbitQuotient` breaks the stored kernel proofs.
#tooth permuteEulerVec_inv_left by mutation eulerVarPerm := fun _ i => i
#tooth quadInvariant_equitable_quotient_intertwining by mutation quadOrbitQuotient := fun _ _ => 0

private theorem isPolyFluxSsaDag_inhabited :
    ∃ (numVars : Nat) (dag : FluxSsaDag),
      0 < dag.nodes.length ∧ isPolyFluxSsaDag numVars dag = true :=
  ⟨3, momentumNormSqDag, by decide +kernel, by decide +kernel⟩

end Obend.Hardware.PdeHypergraphSymmetry
end
