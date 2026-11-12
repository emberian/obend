module
public import Obend.Hardware.Gpu.SoacOptimize
public import Obend.Hardware.Gpu.ArrayEmitCorrect
import all Obend.Hardware.Gpu.SoacOptimize
public section
namespace Obend.Hardware.Gpu.StencilTile
open Obend.Hardware.ArrayHypergraph Obend.Hardware.OpenHypergraph
open Obend.Hardware.Gpu.ArraySource Obend.Hardware.Gpu.SoacOptimize
set_option autoImplicit false

set_option genSizeOfSpec false in
inductive StencilBoundary where
  | periodic | clamp
  deriving DecidableEq, Repr

def resolveStencilIdx (b : StencilBoundary) (n : Nat) (i : Int) : Nat :=
  match b with
  | .periodic => (i % (n : Int)).toNat
  | .clamp => if i ≤ 0 then 0 else if (n - 1 : Nat) ≤ i then n - 1 else i.toNat

theorem resolveStencilIdx_lt (b : StencilBoundary) (n : Nat) (hn : 0 < n) (i : Int) :
    resolveStencilIdx b n i < n := by
  cases b with
  | periodic =>
    have h0 := Int.emod_nonneg i (by omega : (n : Int) ≠ 0)
    have h1 := Int.emod_lt_of_pos i (by omega : (0 : Int) < n)
    simp only [resolveStencilIdx]
    omega
  | clamp => simp only [resolveStencilIdx]; split <;> (try split) <;> omega

structure StencilKernel1D (radius : Nat) where
  stencilFn : Vec → Word

/-- Every offset uses signed arithmetic before the boundary rule is applied. -/
def stencilWindow (b : StencilBoundary) (r : Nat) (grid : Vec) (i : Nat) : Vec :=
  (List.range (2*r+1)).map fun (k : Nat) =>
    grid.getD (resolveStencilIdx b grid.length ((i : Int) + k - r)) 0#64

def evalStencil1D (b : StencilBoundary) (r : Nat) (fn : Vec → Word) (grid : Vec) : Vec :=
  (List.range grid.length).map fun i => fn (stencilWindow b r grid i)

/-- Structure-of-arrays component semantics, sharing the spatial boundary policy. -/
def evalStencilSoa (b : StencilBoundary) (r : Nat) (fn : Vec → Word)
    (components : List Vec) : List Vec := components.map (evalStencil1D b r fn)

def scalarStencil (e : ScalarExpr) (window : Vec) : Word := e.eval (fun i => window.getD i 0#64)

/-- Full tiles followed by at most one nonempty tail. Empty grids launch no tile. -/
def tileWidths (B N : Nat) : List Nat :=
  List.replicate (N / B) B ++ if N % B = 0 then [] else [N % B]

theorem tileWidths_sum (B N : Nat) : (tileWidths B N).sum = N := by
  have h := Nat.div_add_mod N B
  simp only [tileWidths, List.sum_append, List.sum_replicate_nat]
  split <;> simp_all [Nat.mul_comm]

theorem tileWidths_length (B N : Nat) (hB : 0 < B) :
    (tileWidths B N).length = (N+B-1)/B := by
  have hmod := Nat.mod_lt N hB
  have hd := Nat.div_add_mod N B
  simp only [tileWidths, List.length_append, List.length_replicate]
  split
  · rename_i h
    simp only [List.length_nil, Nat.add_zero]
    symm
    apply Nat.div_eq_of_lt_le <;> simp only [Nat.mul_comm _ B, Nat.mul_add, Nat.mul_one] <;> omega
  · rename_i h
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    symm
    apply Nat.div_eq_of_lt_le <;> simp only [Nat.mul_comm _ B, Nat.mul_add, Nat.mul_one] <;> omega

/-- Cooperative load into an actual random-access scratchpad. -/
def loadHalo (b : StencilBoundary) (r : Nat) (grid : Vec) (start width : Nat) : Array Word :=
  ((List.range (width+2*r)).map fun (k : Nat) =>
    grid.getD (resolveStencilIdx b grid.length ((start : Int)+k-r)) 0#64).toArray

/-- Computation after the workgroup barrier reads only the scratchpad. -/
def computeHalo (r width : Nat) (fn : Vec → Word) (lds : Array Word) : Vec :=
  (List.range width).map fun j =>
    fn ((List.range (2*r+1)).map fun (k : Nat) => lds[j+k]?.getD 0#64)

set_option genSizeOfSpec false in
inductive HaloPhase where
  | cooperativeLoad | barrier | localCompute
  deriving Repr, DecidableEq

structure TiledStencilPlan where
  workgroupSize : Nat
  radius : Nat
  gridLength : Nat
  boundary : StencilBoundary

def TiledStencilPlan.widths (p : TiledStencilPlan) : List Nat := tileWidths p.workgroupSize p.gridLength

def TiledStencilPlan.phases (_p : TiledStencilPlan) : List HaloPhase :=
  [.cooperativeLoad, .barrier, .localCompute]

/-- A compute phase before a barrier is refused. Loading invalidates the old
barrier receipt; the normal schedule is load, barrier, then local computation. -/
def executeHaloPhases (r width : Nat) (fn : Vec → Word) (load : Unit → Array Word) :
    List HaloPhase → Array Word → Bool → Vec
  | [], _, _ => []
  | .cooperativeLoad :: rest, _, _ => executeHaloPhases r width fn load rest (load ()) false
  | .barrier :: rest, lds, _ => executeHaloPhases r width fn load rest lds true
  | .localCompute :: _, lds, ready => if ready then computeHalo r width fn lds else []

def evalHaloTile (b : StencilBoundary) (r : Nat) (fn : Vec → Word)
    (grid : Vec) (start width : Nat) : Vec :=
  executeHaloPhases r width fn (fun _ => loadHalo b r grid start width)
    (TiledStencilPlan.phases ⟨width,r,grid.length,b⟩) #[] false

theorem loadHalo_read (b : StencilBoundary) (r : Nat) (grid : Vec)
    (start width j k : Nat) (hj : j < width) (hk : k < 2*r+1) :
    (loadHalo b r grid start width)[j+k]?.getD 0#64 =
      grid.getD (resolveStencilIdx b grid.length (((start+j : Nat) : Int)+k-r)) 0#64 := by
  have h : j+k < width+2*r := by omega
  simp only [loadHalo, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range h, Option.map_some, Option.getD_some]
  congr 2
  omega

theorem evalHaloTile_eq (b : StencilBoundary) (r : Nat) (fn : Vec → Word)
    (grid : Vec) (start width : Nat) :
    evalHaloTile b r fn grid start width =
      (List.range' start width).map (fun i => fn (stencilWindow b r grid i)) := by
  simp only [evalHaloTile, TiledStencilPlan.phases, executeHaloPhases, computeHalo,
    ite_true, List.range'_eq_map_range, List.map_map]
  apply List.map_congr_left
  intro j hj
  congr 1
  unfold stencilWindow
  apply List.map_congr_left
  intro k hk
  exact loadHalo_read b r grid start width j k (List.mem_range.mp hj) (List.mem_range.mp hk)

def evalHaloTiles (b : StencilBoundary) (r : Nat) (fn : Vec → Word) (grid : Vec) :
    Nat → List Nat → Vec
  | _, [] => []
  | start, width :: widths =>
    evalHaloTile b r fn grid start width ++ evalHaloTiles b r fn grid (start+width) widths

theorem evalHaloTiles_eq (b : StencilBoundary) (r : Nat) (fn : Vec → Word)
    (grid : Vec) (widths : List Nat) (start : Nat) :
    evalHaloTiles b r fn grid start widths =
      (List.range' start widths.sum).map (fun i => fn (stencilWindow b r grid i)) := by
  induction widths generalizing start with
  | nil => simp [evalHaloTiles]
  | cons w ws ih =>
    rw [evalHaloTiles, evalHaloTile_eq, ih]
    simp only [List.sum_cons, ← List.map_append, List.range'_append_1]

def evalTiledHaloStencil (B : Nat) (b : StencilBoundary) (r : Nat)
    (fn : Vec → Word) (grid : Vec) : Vec :=
  evalHaloTiles b r fn grid 0 (tileWidths B grid.length)

theorem tiledHaloStencil_eq_spec (B : Nat) (b : StencilBoundary)
    (r : Nat) (fn : Vec → Word) (grid : Vec) :
    evalTiledHaloStencil B b r fn grid = evalStencil1D b r fn grid := by
  rw [evalTiledHaloStencil, evalHaloTiles_eq, tileWidths_sum]
  simp [evalStencil1D, ← List.range_eq_range']

/-- One global fetch per cooperative load slot, including duplicate boundary values. -/
def tiledHbmReads (B r N : Nat) : Nat :=
  ((tileWidths B N).map (fun w => w+2*r)).sum

theorem haloLoadWords (widths : List Nat) (r : Nat) :
    (widths.map (fun w => w+2*r)).sum = widths.sum + 2*r*widths.length := by
  induction widths with
  | nil => simp
  | cons w ws ih => simp [ih, Nat.mul_add]; omega

theorem tiledHaloStencil_hbm_reads_exact (B r N : Nat) (hB : 0 < B) :
    tiledHbmReads B r N = N + 2*r*((N+B-1)/B) := by
  rw [tiledHbmReads, haloLoadWords, tileWidths_sum, tileWidths_length B N hB]

/-- The tile count is strictly below the cell count as soon as a full tile of
at least two cells exists. This includes the final partial tile. -/
theorem tileCount_lt (B N : Nat) (hB : 2 ≤ B) (hN : B ≤ N) :
    (N+B-1)/B < N := by
  have hdiv := Nat.div_add_mod (N+B-1) B
  have hmul : 2 * ((N+B-1)/B) ≤ B*((N+B-1)/B) := Nat.mul_le_mul_right _ hB
  have hpos : 0 < (N+B-1)/B := Nat.div_pos (by omega) (by omega)
  have hmore : B + ((N+B-1)/B) ≤ B*((N+B-1)/B)+1 := by
    have := Nat.mul_le_mul_left (B-1) hpos
    have he : B = (B-1)+1 := by omega
    have heq : B*((N+B-1)/B) = (B-1)*((N+B-1)/B) + ((N+B-1)/B) := by
      calc
        _ = ((B-1)+1)*((N+B-1)/B) := congrArg (fun x => x*((N+B-1)/B)) he
        _ = _ := by rw [Nat.add_mul, Nat.one_mul]
    omega
  omega

theorem tiledHbmReads_lt_global (B r N : Nat) (hr : 0 < r)
    (hB : 2 ≤ B) (hN : B ≤ N) : tiledHbmReads B r N < (2*r+1)*N := by
  rw [tiledHaloStencil_hbm_reads_exact B r N (by omega)]
  have h := Nat.mul_lt_mul_of_pos_left (tileCount_lt B N hB hN) (by omega : 0 < 2*r)
  rw [Nat.add_mul, Nat.one_mul]
  omega


/-- Every scalar node becomes one ANF binding in the unfused reference lowering. -/
def scalarBindings : ScalarExpr → Nat
  | .input _ | .const _ => 1
  | .prim _ a b c => scalarBindings a + scalarBindings b + scalarBindings c + 1

def evalScalarArrays (n : Nat) (leaf : Nat → Vec) : ScalarExpr → Vec
  | .input i => leaf i
  | .const w => List.replicate n w
  | .prim op a b c => (List.range n).map fun i => evalElemOp op
      [(evalScalarArrays n leaf a).getD i 0#64, (evalScalarArrays n leaf b).getD i 0#64,
        (evalScalarArrays n leaf c).getD i 0#64]

def shiftLeaves (amount : Nat) (leaf : Nat → Rhs) : Nat → Rhs :=
  fun i => renameRhs (amount+·) (leaf i)

def compileScalar (n : Nat) (leaf : Nat → Rhs) : ScalarExpr → Program → Program
  | .input i, tail => .letE (leaf i) tail
  | .const w, tail => .letE (.literal (List.replicate n w)) tail
  | .prim op a b c, tail =>
    compileScalar n leaf a
      (compileScalar n (shiftLeaves (scalarBindings a) leaf) b
        (compileScalar n (shiftLeaves (scalarBindings a + scalarBindings b) leaf) c
          (.letE (.map n op [scalarBindings b + scalarBindings c, scalarBindings c, 0]) tail)))

/-- The compiler retains every pre-existing variable at its exact shifted index. -/
def Extends (count : Nat) (before after : Env) : Prop := ∀ v, after (count+v) = before v

theorem shiftedLeaves_eval (count : Nat) (leaf : Nat → Rhs) (before after : Env)
    (h : Extends count before after) (i : Nat) :
    (shiftLeaves count leaf i).eval after = (leaf i).eval before := by
  rw [shiftLeaves, renameRhs_eval]
  have he : (fun v => after (count+v)) = before := funext h
  rw [he]

theorem compileScalar_eval (e : ScalarExpr) (n : Nat) (leaf : Nat → Rhs)
    (env : Env) (tail : Program) :
    ∃ final, (compileScalar n leaf e tail).eval env = tail.eval final ∧
      final 0 = evalScalarArrays n (fun i => (leaf i).eval env) e ∧
      Extends (scalarBindings e) env final := by
  induction e generalizing leaf env tail with
  | input i => exact ⟨push ((leaf i).eval env) env, rfl, rfl, by intro v; simp [scalarBindings, push, Nat.add_comm 1]⟩
  | const w => exact ⟨push (List.replicate n w) env, rfl, rfl, by intro v; simp [scalarBindings, push, Nat.add_comm 1]⟩
  | prim op a b c ha hb hc =>
    obtain ⟨ea, hca, hva, hsa⟩ := ha leaf env _
    obtain ⟨eb, hcb, hvb, hsb⟩ := hb (shiftLeaves (scalarBindings a) leaf) ea _
    have hsab : Extends (scalarBindings a + scalarBindings b) env eb := by
      intro v
      rw [show scalarBindings a + scalarBindings b + v = scalarBindings b + (scalarBindings a+v) by omega,
        hsb, hsa]
    obtain ⟨ec, hcc, hvc, hsc⟩ := hc (shiftLeaves (scalarBindings a+scalarBindings b) leaf) eb _
    let rhs : Rhs := .map n op [scalarBindings b+scalarBindings c, scalarBindings c, 0]
    refine ⟨push (rhs.eval ec) ec, ?_, ?_, ?_⟩
    · change (compileScalar n leaf a _).eval env = _
      rw [hca, hcb, hcc]
      rfl
    · change rhs.eval ec = _
      have hea : ec (scalarBindings b+scalarBindings c) = evalScalarArrays n (fun i => (leaf i).eval env) a := by
        rw [Nat.add_comm, hsc, ← Nat.add_zero (scalarBindings b), hsb, hva]
      have heb : ec (scalarBindings c) = evalScalarArrays n (fun i => (leaf i).eval env) b := by
        rw [← Nat.add_zero (scalarBindings c), hsc, hvb]
        simp only [shiftedLeaves_eval _ leaf env ea hsa]
      have hec : ec 0 = evalScalarArrays n (fun i => (leaf i).eval env) c := by
        rw [hvc]
        simp only [shiftedLeaves_eval _ leaf env eb hsab]
      simp only [rhs, Rhs.eval, List.map_cons, List.map_nil, hea, heb, hec, evalScalarArrays]
    · intro v
      rw [show scalarBindings (.prim op a b c)+v = (scalarBindings a+scalarBindings b+scalarBindings c+v)+1 by simp only [scalarBindings]; omega]
      change ec (scalarBindings a+scalarBindings b+scalarBindings c+v) = env v
      rw [show scalarBindings a+scalarBindings b+scalarBindings c+v =
        scalarBindings c+(scalarBindings a+scalarBindings b+v) by omega, hsc, hsab]

theorem evalScalarArrays_pointwise (e : ScalarExpr) (n : Nat) (leaf : Nat → Vec)
    (hl : ∀ i, (leaf i).length = n) :
    evalScalarArrays n leaf e = (List.range n).map fun i => e.eval (fun s => (leaf s).getD i 0#64) := by
  induction e with
  | input s =>
    apply List.ext_getElem
    · simp [evalScalarArrays, hl]
    · intro i hi hj
      simp only [evalScalarArrays, List.getElem_map, List.getElem_range, ScalarExpr.eval]
      have h : i < (leaf s).length := hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  | const w => simp only [evalScalarArrays, ScalarExpr.eval, List.map_const', List.length_range]
  | prim op a b c ha hb hc =>
    simp only [evalScalarArrays, ha, hb, hc]
    apply List.map_congr_left
    intro i hi
    have h := List.mem_range.mp hi
    simp only [getD_range_map n _ 0#64 i h, ScalarExpr.eval]

/-- Each leaf is a halo gather; slots outside the declared window are zeros.
Repeated leaves are subsequently removed by CSE. -/
def haloIndexFn (b : StencilBoundary) (r N slot : Nat) : FiniteFunction :=
  ⟨N,N,(List.range N).map fun (i : Nat) => resolveStencilIdx b N ((i : Int)+slot-r)⟩

def haloLeaf (b : StencilBoundary) (r N slot : Nat) : Rhs :=
  if slot < 2*r+1 then .gather (haloIndexFn b r N slot) 0 else .literal (List.replicate N 0#64)

def compileStencilGlobal (b : StencilBoundary) (r N : Nat) (e : ScalarExpr) : Program :=
  compileScalar N (haloLeaf b r N) e (.ret [0])

theorem haloLeaf_length (b : StencilBoundary) (r N slot : Nat) (env : Env) :
    ((haloLeaf b r N slot).eval env).length = N := by
  unfold haloLeaf
  split <;> simp [Rhs.eval, haloIndexFn]

theorem haloLeaf_read (b : StencilBoundary) (r N slot i : Nat) (grid : Vec)
    (hlen : grid.length = N) (hi : i < N) :
    ((haloLeaf b r N slot).eval (fun _ => grid)).getD i 0#64 =
      (stencilWindow b r grid i).getD slot 0#64 := by
  unfold haloLeaf
  split
  · rename_i hs
    simp only [Rhs.eval, haloIndexFn, List.map_map]
    rw [getD_range_map N _ 0#64 i hi]
    simp only [stencilWindow]
    rw [getD_range_map (2*r+1) _ 0#64 slot hs, hlen]
    rfl
  · rename_i hs
    simp only [Rhs.eval]
    rw [getD_of_le_length _ slot 0#64 (by simp [stencilWindow]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hi, Option.getD_some]

theorem compileStencilGlobal_eval_eq (b : StencilBoundary) (r N : Nat)
    (e : ScalarExpr) (grid : Vec) (hlen : grid.length = N) :
    (compileStencilGlobal b r N e).eval (fun _ => grid) =
      [evalStencil1D b r (scalarStencil e) grid] := by
  obtain ⟨final, he, hv, _⟩ := compileScalar_eval e N (haloLeaf b r N) (fun _ => grid) (.ret [0])
  rw [compileStencilGlobal, he]
  simp only [Program.eval, List.map_cons, List.map_nil, hv]
  congr 1
  rw [evalScalarArrays_pointwise e N _ (fun i => haloLeaf_length b r N i _)]
  simp only [evalStencil1D, hlen]
  apply List.map_congr_left
  intro i hi
  unfold scalarStencil
  congr 1
  funext s
  exact haloLeaf_read b r N s i grid hlen (List.mem_range.mp hi)

/-- Direct fused lowering shares the same halo leaves, now scalar pullbacks. -/
def compileStencilFused (b : StencilBoundary) (r N : Nat) (e : ScalarExpr) : FusedProgram :=
  fuseVertical (liftArraySource (compileStencilGlobal b r N e))

theorem compileStencilFused_eval_eq (b : StencilBoundary) (r N : Nat)
    (e : ScalarExpr) (grid : Vec) (hlen : grid.length = N) :
    evalFused (fun _ => grid) (compileStencilFused b r N e) =
      [evalStencil1D b r (scalarStencil e) grid] := by
  rw [compileStencilFused, fuseVertical_sound, liftArraySource_sound]
  exact compileStencilGlobal_eval_eq b r N e grid hlen


theorem scalarBindings_pos (e : ScalarExpr) : 0 < scalarBindings e := by cases e <;> simp [scalarBindings]

theorem shiftLeaves_scoped (leaf : Nat → Rhs) (d amount : Nat)
    (h : ∀ i, (leaf i).Scoped d) : ∀ i, (shiftLeaves amount leaf i).Scoped (d+amount) := by
  intro i v hv
  rw [shiftLeaves, renameRhs_vars] at hv
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
  have := h i j hj
  omega

theorem compileScalar_scoped (e : ScalarExpr) (n : Nat) (leaf : Nat → Rhs)
    (d : Nat) (tail : Program) (hl : ∀ i, (leaf i).Scoped d)
    (ht : tail.Scoped (d+scalarBindings e)) : (compileScalar n leaf e tail).Scoped d := by
  induction e generalizing leaf d tail with
  | input i => exact ⟨hl i, ht⟩
  | const w => exact ⟨by intro i hi; simp [Rhs.vars] at hi, ht⟩
  | prim op a b c ha hb hc =>
    apply ha leaf d _ hl
    apply hb _ (d+scalarBindings a) _ (shiftLeaves_scoped leaf d _ hl)
    apply hc _ (d+scalarBindings a+scalarBindings b)
    · simpa only [Nat.add_assoc] using shiftLeaves_scoped leaf d (scalarBindings a+scalarBindings b) hl
    · refine ⟨?_, ?_⟩
      · intro v hv
        have hapos := scalarBindings_pos a
        simp only [Rhs.vars, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega
      · simpa only [scalarBindings, Nat.add_assoc] using ht

theorem compileStencilGlobal_scoped (b : StencilBoundary) (r N : Nat) (e : ScalarExpr) :
    (compileStencilGlobal b r N e).Scoped 1 := by
  apply compileScalar_scoped
  · intro i
    unfold haloLeaf
    split <;> intro v hv <;> simp [Rhs.vars] at hv
    subst v
    omega
  · intro v hv
    simp at hv
    subst v
    omega

theorem compileStencilGlobal_sound (b : StencilBoundary) (r N : Nat) (e : ScalarExpr)
    (grid : Vec) (hlen : grid.length = N) (target : Env) (hinput : target 0 = grid) :
    evalGraph (ArraySource.compile [N] (compileStencilGlobal b r N e)) target =
      [evalStencil1D b r (scalarStencil e) grid] := by
  rw [ArraySource.compile_sound [N] _ (fun _ => grid) target (compileStencilGlobal_scoped b r N e)]
  · exact compileStencilGlobal_eval_eq b r N e grid hlen
  · intro i hi
    have : i = 0 := by simp at hi; omega
    subst i
    exact hinput

/-- Composition with the actual action emitter. The premises are its executable
admission checks and the standard physical-memory representation invariant. -/
theorem compileStencilGlobal_emitted_sound (b : StencilBoundary) (r N : Nat) (e : ScalarExpr)
    (grid : Vec) (hlen : grid.length = N) (target : Env) (hinput : target 0 = grid)
    (flat : BlockLower.FlatMemory) (schedule : ArrayEmit.Schedule)
    (hwf : (ArraySource.compile [N] (compileStencilGlobal b r N e)).wf = true)
    (hlayout : layoutOk (ArraySource.compile [N] (compileStencilGlobal b r N e)) = true)
    (hgood : Good (ArraySource.compile [N] (compileStencilGlobal b r N e)).lengths target)
    (hflat : Flat (ArraySource.compile [N] (compileStencilGlobal b r N e)).lengths
      (gpuLayout (ArraySource.compile [N] (compileStencilGlobal b r N e))).base
      (liveAt (layerGraph (fuseGraph (ArraySource.compile [N] (compileStencilGlobal b r N e))))
        (ArraySource.compile [N] (compileStencilGlobal b r N e)).outputs)
      target (fun a => flat (.device,a)))
    (hc : ArrayEmit.compile (lowerArrayToGpu (ArraySource.compile [N] (compileStencilGlobal b r N e))) = .ok schedule) :
    ArrayEmitCorrect.compiledOutputs
      (lowerArrayToGpu (ArraySource.compile [N] (compileStencilGlobal b r N e))) schedule flat =
        [evalStencil1D b r (scalarStencil e) grid] := by
  rw [ArrayEmitCorrect.compile_runProgram _ schedule hc flat,
    lowerArrayToGpu_sound _ hwf hlayout target _ hgood hflat]
  exact compileStencilGlobal_sound b r N e grid hlen target hinput


/-- Random-access execution: the global grid is converted once, outside the tile
loop. Both the global grid and LDS reads are then constant-time array accesses. -/
def loadHaloArray (b : StencilBoundary) (r : Nat) (grid : Array Word) (start width : Nat) : Array Word :=
  ((List.range (width+2*r)).map fun (k : Nat) =>
    grid[resolveStencilIdx b grid.size ((start : Int)+k-r)]?.getD 0#64).toArray

def evalHaloTilesExec (b : StencilBoundary) (r : Nat) (fn : Vec → Word) (grid : Array Word) :
    Nat → List Nat → Vec
  | _, [] => []
  | start, width::widths =>
    executeHaloPhases r width fn (fun _ => loadHaloArray b r grid start width)
      (TiledStencilPlan.phases ⟨width,r,grid.size,b⟩) #[] false ++
        evalHaloTilesExec b r fn grid (start+width) widths

def evalTiledHaloStencilExec (B : Nat) (b : StencilBoundary) (r : Nat)
    (fn : Vec → Word) (grid : Vec) : Vec :=
  evalHaloTilesExec b r fn grid.toArray 0 (tileWidths B grid.length)

theorem loadHaloArray_eq (b : StencilBoundary) (r : Nat) (grid : Vec) (start width : Nat) :
    loadHaloArray b r grid.toArray start width = loadHalo b r grid start width := by
  simp only [loadHaloArray, loadHalo, List.size_toArray, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem evalHaloTilesExec_eq (b : StencilBoundary) (r : Nat) (fn : Vec → Word)
    (grid : Vec) (widths : List Nat) (start : Nat) :
    evalHaloTilesExec b r fn grid.toArray start widths = evalHaloTiles b r fn grid start widths := by
  induction widths generalizing start with
  | nil => rfl
  | cons w ws ih => simp only [evalHaloTilesExec, evalHaloTiles, evalHaloTile, loadHaloArray_eq,
      List.size_toArray, ih]

theorem evalTiledHaloStencilExec_eq (B : Nat) (b : StencilBoundary) (r : Nat)
    (fn : Vec → Word) (grid : Vec) :
    evalTiledHaloStencilExec B b r fn grid = evalStencil1D b r fn grid := by
  rw [evalTiledHaloStencilExec, evalHaloTilesExec_eq, evalHaloTiles_eq, tileWidths_sum]
  simp only [← List.range_eq_range', evalStencil1D]

theorem tiledHbmReads_loads (B r : Nat) (b : StencilBoundary) (grid : Vec) :
    tiledHbmReads B r grid.length =
      ((tileWidths B grid.length).map (fun w => (loadHaloArray b r grid.toArray 0 w).size)).sum := by
  simp [tiledHbmReads, loadHaloArray]

/-- Scalar constructors for fixed-point stencil numerators. Arithmetic remains
modulo 2^64; these are compiler workloads, not real-valued stability claims. -/
def scalarAdd (a b : ScalarExpr) : ScalarExpr := .prim (.scalar .add) a b (.const 0#64)
def scalarSub (a b : ScalarExpr) : ScalarExpr := .prim (.scalar .sub) a b (.const 0#64)
def scalarScale (k : Int) (a : ScalarExpr) : ScalarExpr := .prim (.scalar (.scale k)) a (.const 0#64) (.const 0#64)
def scalarSelect (c a b : ScalarExpr) : ScalarExpr := .prim (.scalar .mux) c a b

def scalarLt (a b : ScalarExpr) : ScalarExpr := .prim .ult a b (.const 0#64)

/-- Signed two's-complement minmod, using comparisons and branchless selects. -/
def scalarMinmod (a b : ScalarExpr) : ScalarExpr :=
  let positiveA := scalarLt a (.const (BitVec.ofNat 64 (2^63)))
  let positiveB := scalarLt b (.const (BitVec.ofNat 64 (2^63)))
  let lesser := scalarSelect (scalarLt a b) a b
  let greater := scalarSelect (scalarLt a b) b a
  scalarSelect positiveA (scalarSelect positiveB lesser (.const 0#64))
    (scalarSelect positiveB (.const 0#64) greater)

/-- Integer numerator of a centered flux difference plus local dissipation:
2*u_i - c*(u_right-u_left) + viscosity*(u_left-2*u_i+u_right).
The caller supplies its fixed-point scaling and wave-speed bound. -/
def rusanovNumerator (c viscosity : Int) : ScalarExpr :=
  scalarAdd (scalarSub (scalarScale 2 (.input 1))
    (scalarScale c (scalarSub (.input 2) (.input 0))))
    (scalarScale viscosity (scalarAdd (scalarSub (.input 0) (scalarScale 2 (.input 1))) (.input 2)))

/-- Five-point slope-limited reconstruction, retaining both neighbor slopes. -/
def minmodTvdNumerator (c viscosity : Int) : ScalarExpr :=
  let leftSlope := scalarMinmod (scalarSub (.input 1) (.input 0)) (scalarSub (.input 2) (.input 1))
  let rightSlope := scalarMinmod (scalarSub (.input 3) (.input 2)) (scalarSub (.input 4) (.input 3))
  scalarAdd (scalarSub (scalarScale 2 (.input 2))
    (scalarScale c (scalarSub (.input 3) (.input 1))))
    (scalarScale viscosity (scalarSub rightSlope leftSlope))

end Obend.Hardware.Gpu.StencilTile
