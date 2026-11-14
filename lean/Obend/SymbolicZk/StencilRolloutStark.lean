module
public import Obend.Analysis.PdeSexprAndApprox
public import Obend.Core.RangeSafe
public import Obend.Hardware.Gpu.ArraySource
public import Obend.SymbolicZk.CompileToPiop
public import Obend.Crypto.DualSpine
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.Diff
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Core.RangeSafe
import all Obend.Hardware.Gpu.ArraySource
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.ArrayFold
import all Obend.Hardware.OpenHypergraph
import all Obend.SymbolicZk.CompileToPiop
import all Obend.SymbolicZk.CompileToPiopCore
import all Obend.Crypto.DualSpine
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.Multilinear
import all Obend.Crypto.PCS
import all Obend.Crypto.Transcript
/-!
Offset Q32 advection at CFL 1/2, its array-program lowering, rational error
estimate, and range-checked Goldilocks quotient/remainder constraints.
The cryptographic APIs below bind complete public statements and extract
concrete hash or lattice witnesses. The Maxwell receipt links the committed
initial state, every stencil row, sensor, and rational energy ceiling. Its PCS
commitments are succinct, but openings and traces are transparent: the historical
Zk API name does not imply statistical hiding or a zero-knowledge protocol.
-/
public section
namespace Obend.SymbolicZk.StencilRolloutStark
open Obend.Analysis Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox
open Obend.Hardware.ArrayHypergraph (Word)
open Obend.Hardware.Gpu.ArraySource
open Obend.Core.Term
open Obend.Core.RangeSafe
open Obend.Crypto
set_option autoImplicit false
set_option maxRecDepth 8192
abbrev WordGrid := List Word
def amplitudeLimit : Nat := 2^48
def offset : Nat := 2^47
def fixedScale : Nat := 2^32
def InRange (w : WordGrid) : Prop := ∀ x ∈ w, x.toNat < amplitudeLimit
def stencilNumerator : Term := .binary .add (.bound 0) (.bound 1)
def stencilBounds : List Obend.Core.RangeSafe.Interval :=
  [Obend.Core.RangeSafe.Interval.mkNat 0 (amplitudeLimit - 1),
   Obend.Core.RangeSafe.Interval.mkNat 0 (amplitudeLimit - 1)]
/-- All intermediate numerator operations are reconstructed as natural numbers.
The division is performed by a quotient/remainder relation, never field inversion. -/
theorem stencil_numerator_mod_exact (l r : Nat) (hl : l < amplitudeLimit) (hr : r < amplitudeLimit) :
    ∃ I v, inferRange stencilBounds stencilNumerator = some I ∧
      Evaluates (closeTerm [.nat l, .nat r] stencilNumerator) v ∧ ValueInInterval I v ∧
      scalarToNat v < Obend.Apps.ZkNtt.goldilocksPrime ∧
      evalMod Obend.Apps.ZkNtt.goldilocksPrime [l, r] stencilNumerator = some (scalarToNat v) := by
  have hlv : ValueInInterval (Obend.Core.RangeSafe.Interval.mkNat 0 (amplitudeLimit - 1)) (.nat l) :=
    ⟨l, rfl, Nat.zero_le _, by change _ ≤ amplitudeLimit - 1; unfold amplitudeLimit at *; omega⟩
  have hrv : ValueInInterval (Obend.Core.RangeSafe.Interval.mkNat 0 (amplitudeLimit - 1)) (.nat r) :=
    ⟨r, rfl, Nat.zero_le _, by change _ ≤ amplitudeLimit - 1; unfold amplitudeLimit at *; omega⟩
  have h := modEnvAgrees_cons (M := Obend.Apps.ZkNtt.goldilocksPrime)
    ⟨.refl _, .natural l⟩ hlv
    (modEnvAgrees_cons ⟨.refl _, .natural r⟩ hrv (modEnvAgrees_nil _))
  have hlp : l < Obend.Apps.ZkNtt.goldilocksPrime := by
    simp only [amplitudeLimit] at hl; change l < 18446744069414584321; omega
  have hrp : r < Obend.Apps.ZkNtt.goldilocksPrime := by
    simp only [amplitudeLimit] at hr; change r < 18446744069414584321; omega
  simp only [scalarToNat, Nat.mod_eq_of_lt hlp, Nat.mod_eq_of_lt hrp] at h
  exact evaluates_mod_prime_exact_of_rangeSafe _ stencilBounds [.nat l, .nat r] [l, r]
    stencilNumerator (by decide +kernel) h
/-- Q32 offset encoding of unit-speed advection at Courant number one half. -/
def q32StencilStep (w : WordGrid) : WordGrid :=
  (List.range w.length).map fun i => BitVec.ofNat 64
    (((w.getD (prevCell w.length i) 0#64).toNat + (w.getD i 0#64).toNat) / 2)
def q32StencilRollout : Nat → WordGrid → WordGrid
  | 0, w => w
  | k + 1, w => q32StencilStep (q32StencilRollout k w)
/-- Periodic halo gather, pointwise integer addition, then a logical shift. -/
def compileQ32StencilGpu (n : Nat) : Program :=
  .letE (.gather ⟨n, n, (List.range n).map (prevCell n)⟩ 0)
  (.letE (.map n (.scalar .add) [0, 1])
  (.letE (.literal (List.replicate n 1#64))
  (.letE (.map n .shr [1, 0]) (.ret [0]))))
def gridEnv (w : WordGrid) : Env := fun i => if i = 0 then w else []
theorem getD_inRange (w : WordGrid) (h : InRange w) (i : Nat) :
    (w.getD i 0#64).toNat < amplitudeLimit := by
  simp only [List.getD_eq_getElem?_getD]
  cases he : w[i]? with
  | none => change 0 < amplitudeLimit; decide
  | some x => exact h x (List.mem_of_getElem? he)
theorem word_half_sum_exact (x y : Word)
    (hx : x.toNat < amplitudeLimit) (hy : y.toNat < amplitudeLimit) :
    (x + y) >>> 1 = BitVec.ofNat 64 ((x.toNat + y.toNat) / 2) := by
  apply BitVec.eq_of_toNat_eq
  have hs : x.toNat + y.toNat < 2^64 := by unfold amplitudeLimit at *; omega
  have hq : (x.toNat + y.toNat) / 2 < 2^64 := by omega
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hq, Nat.shiftRight_eq_div_pow]
/-- The emitted array program evaluates the natural-number stencil exactly. -/
theorem q32Stencil_gpu_arraySource_sound (w : WordGrid) (h : InRange w) :
    (compileQ32StencilGpu w.length).eval (gridEnv w) = [q32StencilStep w] := by
  simp only [compileQ32StencilGpu, Program.eval, Rhs.eval, push, gridEnv, ↓reduceIte,
    List.map_cons, List.map_nil, Obend.Hardware.ArrayHypergraph.evalElemOp,
    Obend.Hardware.OpenHypergraph.evalHypergraphOpBv, List.getD_cons_zero,
    List.getD_cons_succ]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hin : i < w.length := List.mem_range.mp hi
  simp only [Obend.Hardware.ArrayHypergraph.getD_range_map _ _ _ _ hin]
  simp only [List.map_map, Function.comp_def,
    Obend.Hardware.ArrayHypergraph.getD_range_map _ _ _ _ hin]
  have hone : (List.replicate w.length 1#64).getD i 0#64 = 1#64 := by
    simp [List.getD_eq_getElem?_getD, hin]
  rw [hone, Obend.Hardware.ArrayHypergraph.wordShr_eq]
  exact word_half_sum_exact _ _ (getD_inRange w h _) (getD_inRange w h _)
/-- Integer truncation retains the exact conservation numerator and bounded remainder. -/
theorem q32_quotient_remainder (l r : Nat) :
    2 * ((l + r) / 2) + (l + r) % 2 = l + r ∧ (l + r) % 2 < 2 := by omega
@[simp] theorem q32StencilStep_length (w : WordGrid) : (q32StencilStep w).length = w.length := by
  simp [q32StencilStep]
theorem q32StencilStep_inRange (w : WordGrid) (h : InRange w) : InRange (q32StencilStep w) := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  have hl := getD_inRange w h (prevCell w.length i)
  have hr := getD_inRange w h i
  have hq : ((w.getD (prevCell w.length i) 0#64).toNat + (w.getD i 0#64).toNat) / 2 < amplitudeLimit := by
    unfold amplitudeLimit at *; omega
  have hq64 : ((w.getD (prevCell w.length i) 0#64).toNat + (w.getD i 0#64).toNat) / 2 < 2^64 := by
    unfold amplitudeLimit at hq; omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq64] using hq
theorem q32StencilRollout_inRange (w : WordGrid) (h : InRange w) (k : Nat) :
    InRange (q32StencilRollout k w) := by
  induction k with
  | zero => exact h
  | succ k ih => exact q32StencilStep_inRange _ ih
@[simp] theorem q32StencilRollout_length (w : WordGrid) (k : Nat) :
    (q32StencilRollout k w).length = w.length := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [q32StencilRollout] using ih
def gpuRollout : Nat → WordGrid → WordGrid
  | 0, w => w
  | k + 1, w =>
      let prev := gpuRollout k w
      ((compileQ32StencilGpu prev.length).eval (gridEnv prev)).getD 0 []
theorem gpuRollout_eq_q32 (w : WordGrid) (h : InRange w) (k : Nat) :
    gpuRollout k w = q32StencilRollout k w := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [gpuRollout, ih, q32Stencil_gpu_arraySource_sound _ (q32StencilRollout_inRange w h k),
        List.getD_cons_zero, q32StencilRollout]
def decodeNat (x : Nat) : Rat := ((x : Rat) - (offset : Rat)) / (fixedScale : Rat)
def decodeGrid (w : WordGrid) : Grid := fun i _ => decodeNat (w.getD i 0#64).toNat
def advectionSystem : HyperbolicSystem where
  vars := ["u"]
  flux := [.var "u"]
  state := [0]
  left := [0]
  right := [1]
  aMax := 1
  cfl := 1/2
def advectionCert : HyperbolicCert :=
  ⟨[[1]], [[1]], [1], [[1]], [1], [[1]]⟩
def rationalAdvection (n : Nat) : Grid → Grid := rusanovStep 1 (fun _ _ => 1) 1 (1/2) n
theorem rationalAdvection_cell (n : Nat) (u : Grid) (i : Nat) :
    rationalAdvection n u i 0 = (u (prevCell n i) 0 + u i 0) / 2 := by
  simp [rationalAdvection, rusanovStep, mulVec, sumTo]
  grind
theorem decode_half_defect (l r : Nat) :
    ratAbs (decodeNat ((l + r) / 2) - (decodeNat l + decodeNat r) / 2) ≤ 1 / (fixedScale : Rat) := by
  have h := congrArg (fun n : Nat => (n : Rat)) (q32_quotient_remainder l r).1
  have hm := (q32_quotient_remainder l r).2
  have hm' : (l + r) % 2 = 0 ∨ (l + r) % 2 = 1 := by omega
  rcases hm' with hm' | hm' <;> rw [hm'] at h <;>
    simp only [Rat.natCast_add, Rat.natCast_mul, Rat.natCast_ofNat] at h <;>
    change ratAbs ((↑((l + r) / 2) - 140737488355328) / 4294967296 -
      ((↑l - 140737488355328) / 4294967296 + (↑r - 140737488355328) / 4294967296) / 2) ≤ 1 / 4294967296 <;>
    unfold ratAbs <;> split <;> grind
theorem q32StencilStep_defect (w : WordGrid) (h : InRange w) (i : Nat) (hi : i < w.length) :
    ratAbs (decodeGrid (q32StencilStep w) i 0 - rationalAdvection w.length (decodeGrid w) i 0) ≤
      1 / (fixedScale : Rat) := by
  rw [rationalAdvection_cell]
  simp only [decodeGrid, q32StencilStep,
    Obend.Hardware.ArrayHypergraph.getD_range_map _ _ _ _ hi]
  have hl := getD_inRange w h (prevCell w.length i)
  have hr := getD_inRange w h i
  have hq : ((w.getD (prevCell w.length i) 0#64).toNat + (w.getD i 0#64).toNat) / 2 < 2^64 := by
    unfold amplitudeLimit at *; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  exact decode_half_defect _ _
def q32DecodedTrajectory (w : WordGrid) (k : Nat) : Grid := decodeGrid (q32StencilRollout k w)
def q32DefectBudget (n : Nat) : Rat := (n : Rat) * (1 / (fixedScale : Rat) * (1 / (fixedScale : Rat)))
theorem q32_defect_energy (w : WordGrid) (h : InRange w) (k : Nat) :
    discreteHEnergy 1 w.length (fun _ _ => 1)
      (stepDefect (rationalAdvection w.length) (q32DecodedTrajectory w) k) ≤ q32DefectBudget w.length := by
  have hc : ∀ i c, i < w.length → c < 1 →
      ratAbs (stepDefect (rationalAdvection w.length) (q32DecodedTrajectory w) k i c) ≤
        1 / (fixedScale : Rat) := by
    intro i c hi hc
    have ce : c = 0 := by omega
    subst ce
    have hk := q32StencilRollout_inRange w h k
    have hi' : i < (q32StencilRollout k w).length := by simpa using hi
    simpa only [stepDefect, gridSub, q32DecodedTrajectory, q32StencilRollout, q32StencilRollout_length] using
      q32StencilStep_defect (q32StencilRollout k w) hk i hi'
  have ht := discreteHEnergy_le_of_linf_bound 1 w.length (fun _ _ => 1)
    (stepDefect (rationalAdvection w.length) (q32DecodedTrajectory w) k)
    (1 / (fixedScale : Rat)) 1 (by decide +kernel) hc (by decide +kernel)
  simpa [q32DefectBudget] using ht
/-- End-to-end comparison of the actual array execution with the exact rational
finite-volume solution. This is a discrete reference error, not a continuum truncation theorem. -/
theorem q32Stencil_gpu_rollout_within_rational_pde_tube (w : WordGrid) (h : InRange w)
    (initial : Grid) (K : Nat) (η : Rat) (hη : 0 < η) :
    discreteHEnergy 1 w.length (fun _ _ => 1)
      (gridSub (decodeGrid (gpuRollout K w)) (exactTrajectory (rationalAdvection w.length) initial K)) ≤
      aprioriErrorTubeRec η (discreteHEnergy 1 w.length (fun _ _ => 1)
        (gridSub (decodeGrid w) initial)) (q32DefectBudget w.length) K := by
  rw [gpuRollout_eq_q32 w h K]
  have cert : Certified advectionSystem advectionCert := check_sound (by decide +kernel)
  have hs : ∀ x y, form 1 (fun _ _ => 1) x y = form 1 (fun _ _ => 1) y x := by
    intro x y; simp [form, dot, mulVec, sumTo]; grind
  have hp : ∀ x, 0 ≤ form 1 (fun _ _ => 1) x x := by
    intro x; have hh := Obend.Analysis.Interval.rat_sq_nonneg (x 0)
    simp only [form, dot, mulVec, sumTo]; grind
  have hc : ∀ u, discreteHEnergy 1 w.length (fun _ _ => 1) (rationalAdvection w.length u) ≤
      discreteHEnergy 1 w.length (fun _ _ => 1) u := by
    intro u
    have hh := certified_step_contracts advectionSystem advectionCert cert w.length u
    simpa [advectionSystem, advectionCert, HyperbolicSystem.dim, HyperbolicSystem.jacobian,
      matOf, getOr, envOf, rationalAdvection, discreteHEnergy, rusanovStep, mulVec, dot, sumTo,
      evalDualRat, DualRat.var] using hh
  exact accelerated_rusanov_apriori_error_tube 1 w.length (fun _ _ => 1) (fun _ _ => 1)
    1 (1/2) η (q32DefectBudget w.length) hη initial (q32DecodedTrajectory w) hs hp hc
    (q32_defect_energy w h) K
example : InRange [1#64, 2#64, 3#64] := by
  intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> decide +kernel
open Obend.SymbolicZk.CompileToPiop
/-- Cleared-denominator arithmetic row. The quotient and remainder are both
witness columns; replacing division by a field inverse would be unsound. -/
structure StencilRow where
  left : Nat
  center : Nat
  quotient : Nat
  remainder : Nat
  deriving DecidableEq, Repr
structure StencilRowBits where
  left : Array Goldilocks
  center : Array Goldilocks
  quotient : Array Goldilocks
  remainder : Array Goldilocks
def rangeConstraint (x : Nat) : BeforeConstraint := ⟨x, amplitudeLimit, 48⟩
def remainderConstraint (x : Nat) : BeforeConstraint := ⟨x, 2, 1⟩
def compileStencilRowBits (r : StencilRow) : StencilRowBits :=
  ⟨compileBeforeWitness (rangeConstraint r.left), compileBeforeWitness (rangeConstraint r.center),
    compileBeforeWitness (rangeConstraint r.quotient), compileBeforeWitness (remainderConstraint r.remainder)⟩
/-- Polynomial equality over Goldilocks, separate from the range constraints. -/
def stencilRowFieldEq (r : StencilRow) : Bool :=
  decide (Goldilocks.ofNat (2 * r.quotient + r.remainder) = Goldilocks.ofNat (r.left + r.center))
def checkStencilRow (r : StencilRow) (b : StencilRowBits) : Bool :=
  checkBeforePolyArray (rangeConstraint r.left) b.left &&
  checkBeforePolyArray (rangeConstraint r.center) b.center &&
  checkBeforePolyArray (rangeConstraint r.quotient) b.quotient &&
  checkBeforePolyArray (remainderConstraint r.remainder) b.remainder && stencilRowFieldEq r
def StencilRow.Valid (r : StencilRow) : Prop :=
  r.left < amplitudeLimit ∧ r.center < amplitudeLimit ∧ r.quotient < amplitudeLimit ∧
  r.remainder < 2 ∧ 2 * r.quotient + r.remainder = r.left + r.center
theorem checkStencilRow_sound (r : StencilRow) (b : StencilRowBits) (h : checkStencilRow r b = true) :
    r.Valid ∧ r.quotient = (r.left + r.center) / 2 := by
  simp only [checkStencilRow, Bool.and_eq_true] at h
  have hl := checkBeforePolyArray_sound h.1.1.1.1
  have hc := checkBeforePolyArray_sound h.1.1.1.2
  have hq := checkBeforePolyArray_sound h.1.1.2
  have hr := checkBeforePolyArray_sound h.1.2
  change r.left < amplitudeLimit at hl
  change r.center < amplitudeLimit at hc
  change r.quotient < amplitudeLimit at hq
  change r.remainder < 2 at hr
  have he := of_decide_eq_true h.2
  have hn := congrArg Goldilocks.val he
  have hsum : r.left + r.center < Obend.Apps.ZkNtt.goldilocksPrime := by
    unfold amplitudeLimit at *; change _ < 18446744069414584321; omega
  have hout : 2 * r.quotient + r.remainder < Obend.Apps.ZkNtt.goldilocksPrime := by
    unfold amplitudeLimit at *; change _ < 18446744069414584321; omega
  change (2 * r.quotient + r.remainder) % Obend.Apps.ZkNtt.goldilocksPrime =
    (r.left + r.center) % Obend.Apps.ZkNtt.goldilocksPrime at hn
  rw [Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt hout] at hn
  exact ⟨⟨hl, hc, hq, hr, hn⟩, by omega⟩
theorem checkStencilRow_complete (r : StencilRow) (h : r.Valid) :
    checkStencilRow r (compileStencilRowBits r) = true := by
  have hl := checkBeforePolyArray_complete (rangeConstraint r.left) (by change beforeWidthSafe 48 = true; decide +kernel)
    h.1 (Nat.le_refl _) h.1
  have hc := checkBeforePolyArray_complete (rangeConstraint r.center) (by change beforeWidthSafe 48 = true; decide +kernel)
    h.2.1 (Nat.le_refl _) h.2.1
  have hq := checkBeforePolyArray_complete (rangeConstraint r.quotient) (by change beforeWidthSafe 48 = true; decide +kernel)
    h.2.2.1 (Nat.le_refl _) h.2.2.1
  have hr := checkBeforePolyArray_complete (remainderConstraint r.remainder) (by change beforeWidthSafe 1 = true; decide +kernel)
    h.2.2.2.1 (Nat.le_refl _) h.2.2.2.1
  have he : stencilRowFieldEq r = true := by
    unfold stencilRowFieldEq
    rw [h.2.2.2.2]; exact decide_eq_true rfl
  simp only [checkStencilRow, compileStencilRowBits, hl, hc, hq, hr, he, Bool.and_self]
def stencilRow (w : WordGrid) (i : Nat) : StencilRow :=
  let l := (w.getD (prevCell w.length i) 0#64).toNat
  let c := (w.getD i 0#64).toNat
  ⟨l, c, (l + c) / 2, (l + c) % 2⟩
theorem stencilRow_valid (w : WordGrid) (h : InRange w) (i : Nat) : (stencilRow w i).Valid := by
  have hl := getD_inRange w h (prevCell w.length i)
  have hc := getD_inRange w h i
  refine ⟨hl, hc, ?_, (q32_quotient_remainder _ _).2, (q32_quotient_remainder _ _).1⟩
  change (_ + _) / 2 < amplitudeLimit
  unfold amplitudeLimit at *; omega
/-- Every cell at every time has accepted polynomial and Before range constraints. -/
theorem q32Rollout_arithmetization_complete (w : WordGrid) (h : InRange w) (k i : Nat) :
    checkStencilRow (stencilRow (q32StencilRollout k w) i)
      (compileStencilRowBits (stencilRow (q32StencilRollout k w) i)) = true :=
  checkStencilRow_complete _ (stencilRow_valid _ (q32StencilRollout_inRange w h k) i)
example : (StencilRow.mk 1 5 3 0).Valid := by unfold StencilRow.Valid; decide +kernel
abbrev PhysicsCommitment := CanopyCommitment × AjtaiCommitment
/-- Public fields are represented explicitly; both complete commitments, the
sensor index, step count, scaling convention, and energy ceiling enter Fiat–Shamir. -/
structure PhysicsStatement where
  cells : Nat
  steps : Nat
  sensor : Nat
  observation : Nat
  energyNumerator : Int
  energyDenominator : Nat
  initialCommitment : PhysicsCommitment
  traceCommitment : PhysicsCommitment
  residualCommitment : PhysicsCommitment
  deriving DecidableEq
def physicsStatementFields (s : PhysicsStatement) :=
  (s.cells, (s.steps, (s.sensor, (s.observation,
    ([s.energyNumerator, (s.energyDenominator : Int)], (s.initialCommitment, (s.traceCommitment, s.residualCommitment)))))))
/-- Existing transcript tuple serialization length-frames every field. -/
def physicsStatementBytes (s : PhysicsStatement) : ByteArray :=
  TranscriptEncode.encodeTranscriptBytes (physicsStatementFields s)
theorem physicsStatementBytes_injective (s t : PhysicsStatement)
    (h : physicsStatementBytes s = physicsStatementBytes t) : s = t := by
  have he := LawfulTranscriptEncode.encodeTranscriptBytes_injective h
  change physicsStatementFields s = physicsStatementFields t at he
  cases s; cases t
  simp only [physicsStatementFields, Prod.mk.injEq, List.cons.injEq, Int.ofNat_inj, and_true] at he
  rcases he with ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
  rfl
/-- The relation binds advection speed 1, CFL 1/2, denominator 2, Q32 scale,
offset and amplitude ceiling. These are not prover-selectable parameters. -/
def physicsRelationBytes : ByteArray :=
  encodeSignedIntBytes [1, 1, 2, 2, fixedScale, offset, amplitudeLimit]
def physicsProtocol : String := "pde-q32-rollout@1"
def physicsTranscript (s : PhysicsStatement) : Transcript .relationBound :=
  bindRelation physicsProtocol physicsRelationBytes (physicsStatementBytes s) (Transcript.newUnseeded ByteArray.empty)
def physicsProtocolBytes : ByteArray :=
  ⟨#[112, 100, 101, 45, 113, 51, 50, 45, 114, 111, 108, 108, 111, 117, 116, 64, 49]⟩
/-- A separate framed digest binds the relation and the complete public statement.
The hash is a parameter, so extraction does not import implementation proof axioms. -/
def physicsStatementPreimage (s : PhysicsStatement) : List UInt8 :=
  (TranscriptEncode.encodeTranscriptBytes
    (physicsProtocolBytes, (physicsRelationBytes, physicsStatementBytes s))).data.toList
def physicsStatementDigest (H : Hash32) (s : PhysicsStatement) : Digest32 :=
  evalDigest32 H (physicsStatementPreimage s)
theorem physicsStatementPreimage_injective (s t : PhysicsStatement)
    (h : physicsStatementPreimage s = physicsStatementPreimage t) : s = t := by
  have hb : TranscriptEncode.encodeTranscriptBytes
      (physicsProtocolBytes, (physicsRelationBytes, physicsStatementBytes s)) =
      TranscriptEncode.encodeTranscriptBytes
      (physicsProtocolBytes, (physicsRelationBytes, physicsStatementBytes t)) :=
    byteArray_eq_of_toList_eq h
  have he := LawfulTranscriptEncode.encodeTranscriptBytes_injective
    (ι := ByteArray × (ByteArray × ByteArray))
    (a := (physicsProtocolBytes, (physicsRelationBytes, physicsStatementBytes s)))
    (b := (physicsProtocolBytes, (physicsRelationBytes, physicsStatementBytes t))) hb
  exact physicsStatementBytes_injective s t (congrArg (fun p => p.2.2) he)
/-- Constructive full-width binding, using only decidable equality of byte lists. -/
def extractPhysicsStatementOrCollision (H : Hash32) (s t : PhysicsStatement)
    (h : physicsStatementDigest H s = physicsStatementDigest H t) :
    PSum (s = t)
      (Obend.Judge.Computational.HashCollisionWitness H.eval
        (max (physicsStatementPreimage s).length (physicsStatementPreimage t).length)) :=
  if he : physicsStatementPreimage s = physicsStatementPreimage t then
    .inl (physicsStatementPreimage_injective s t he)
  else
    .inr (extractEvalDigest32Collision H (Nat.le_max_left _ _) (Nat.le_max_right _ _) he h)
/-- Dual commitments to a complete multilinear table, using the existing 256-bit
Canopy and exact-dimension lattice primitives. -/
def commitPhysicsTable (H : Hash32) (pp : AjtaiParams) (v : Nat) (table : List Goldilocks) : PhysicsCommitment :=
  (canopyCommit H v table, ajtaiLatticeCommit pp v table)
/-- Constructive injectivity of the existing four-limb representation. -/
theorem physicsGadget_injective (a b : List Goldilocks)
    (he : gadgetDecomposeTable a = gadgetDecomposeTable b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => simp [gadgetDecomposeTable, gadgetDecomposeGoldilocks] at he
  | cons x xs ih =>
    cases b with
    | nil => simp [gadgetDecomposeTable, gadgetDecomposeGoldilocks] at he
    | cons y ys =>
      simp only [gadgetDecomposeTable, List.flatMap_cons, gadgetDecomposeGoldilocks,
        List.cons_append, List.nil_append, List.cons.injEq, Int.ofNat_inj] at he
      have hxy : x = y := by
        apply Goldilocks.ext
        have h0 := he.1
        have h1 := he.2.1
        have h2 := he.2.2.1
        have h3 := he.2.2.2.1
        omega
      have ht := ih ys he.2.2.2.2
      cases hxy; cases ht; rfl
/-- Two different tables with equal dual commitments give a concrete short
lattice-kernel vector. The construction uses the existing lattice arithmetic,
with a constructive proof of gadget injectivity. -/
def extractPhysicsCommitmentBreaks (H : Hash32) (pp : AjtaiParams) (v : Nat)
    (a b : List Goldilocks) (ha : a.length = 2^v) (hb : b.length = 2^v)
    (hc : pp.cols = 4 * 2^v) (hne : a ≠ b)
    (he : commitPhysicsTable H pp v a = commitPhysicsTable H pp v b) :
    Obend.Judge.Computational.SISShortVecWitness pp.modulus 131070 pp.matrix :=
  let la := gadgetDecomposeTable a
  let lb := gadgetDecomposeTable b
  have hla : la.length = pp.cols := by dsimp [la]; rw [gadgetDecomposeTable_length, ha, hc]
  have hlb : lb.length = pp.cols := by dsimp [lb]; rw [gadgetDecomposeTable_length, hb, hc]
  have hne' : la ≠ lb := fun hh => hne (physicsGadget_injective a b hh)
  have hsyn : ajtaiCommit pp la hla = ajtaiCommit pp lb hlb := by
    have hh := congrArg (fun p : PhysicsCommitment => p.2.syndrome) he
    simpa only [commitPhysicsTable, ajtaiLatticeCommit, la, lb, hla, hlb, ↓reduceDIte] using hh
  extractShortDiffSISWitness pp la lb hla hlb
    (gadgetDecomposeTable_short a) (gadgetDecomposeTable_short b) hne' hsyn
/-- Linear-time execution uses constant-time array halo reads. -/
def q32StencilStepExec (w : Array Word) : Array Word :=
  Array.ofFn fun i : Fin w.size => BitVec.ofNat 64
    ((((w[prevCell w.size i.val]?).getD 0#64).toNat + (w[i]).toNat) / 2)
theorem q32StencilStepExec_eq_spec (w : Array Word) :
    (q32StencilStepExec w).toList = q32StencilStep w.toList := by
  apply List.ext_getElem
  · simp [q32StencilStepExec, q32StencilStep]
  · intro i h1 _h2
    have hi : i < w.size := by simpa [q32StencilStepExec] using h1
    simp only [q32StencilStepExec, Array.toList_ofFn, List.getElem_ofFn,
      q32StencilStep, List.getElem_map, List.getElem_range]
    simp [List.getD_eq_getElem?_getD, Array.getElem?_eq_getElem hi]
/-- Cleared-denominator polynomial residual. Range proofs are checked separately. -/
def stencilResidual (r : StencilRow) : Goldilocks :=
  CommRingOps.sub (Goldilocks.ofNat (2 * r.quotient + r.remainder))
    (Goldilocks.ofNat (r.left + r.center))
theorem stencilResidual_zero (r : StencilRow) (h : r.Valid) : stencilResidual r = CommRingOps.zero := by
  unfold stencilResidual
  rw [h.2.2.2.2]
  exact LawfulCommRing.sub_self _
/-- This existing PCS opening is transparent: it is not a hiding proof. -/
structure StencilSumcheckProof where
  rounds : List (RoundPoly Goldilocks)
  opening : CanopyOpeningProof × AjtaiOpeningProof
/-- Multilinear sumcheck proof for the arithmetic residual table. The public
statement is absorbed before the residual-table commitment and round challenges. -/
def proveStencilResidualSumcheck (H : Hash32) (pp : AjtaiParams) (s : PhysicsStatement)
    (v : Nat) (rows : List StencilRow) : StencilSumcheckProof :=
  let tbl := rows.map stencilResidual
  let comm := commitPhysicsTable H pp v tbl
  let (rounds, claim, tr) := honestBoundSumcheckProver comm v tbl (physicsTranscript s)
  let (opening, _) := (canopyAjtaiDualPCS H pp).openEval ((), ()) v tbl claim tr
  ⟨rounds, opening⟩
def verifyStencilResidualSumcheck (H : Hash32) (pp : AjtaiParams) (s : PhysicsStatement)
    (v : Nat) (proof : StencilSumcheckProof) : Bool :=
  verifyDualSumcheckPIOP (canopyMerklePCS H) (ajtaiLatticePCS pp) ((), ())
    1 v s.residualCommitment CommRingOps.zero proof.rounds proof.opening (physicsTranscript s)
/-- Completeness connects the genuine stencil conservation rows to a dual-spine,
statement-bound zero-sum proof. This does not assert hiding or trace extraction. -/
theorem proveStencilResidualSumcheck_complete (H : Hash32) (pp : AjtaiParams) (s : PhysicsStatement)
    (v : Nat) (rows : List StencilRow) (hrows : rows.length = 2^v)
    (hvalid : ∀ row ∈ rows, row.Valid) (hcols : pp.cols = 4 * 2^v)
    (hcomm : s.residualCommitment = commitPhysicsTable H pp v (rows.map stencilResidual)) :
    verifyStencilResidualSumcheck H pp s v (proveStencilResidualSumcheck H pp s v rows) = true := by
  have hz : ∀ x ∈ rows.map stencilResidual, x = CommRingOps.zero := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact stencilResidual_zero r (hvalid r hr)
  have hsum : hypercubeSum v (rows.map stencilResidual) = CommRingOps.zero := by
    have sumZero : ∀ (xs ws : List Goldilocks),
        (∀ x ∈ xs, x = CommRingOps.zero) → innerProd xs ws = CommRingOps.zero := by
      intro xs
      induction xs with
      | nil => intro ws _; rfl
      | cons x xs ih =>
        intro ws hh
        cases ws with
        | nil => rfl
        | cons y ys =>
          simp only [innerProd, hh x List.mem_cons_self, LawfulCommRing.zero_mul,
            LawfulCommRing.zero_add]
          exact ih ys (fun z hz => hh z (List.mem_cons_of_mem x hz))
    exact sumZero _ _ hz
  have hc := verifyDualSumcheckPIOP_completeness
    (canopyMerklePCS H) (ajtaiLatticePCS pp) ((), ()) (by decide : 1 ≤ (1 : Nat))
    v (rows.map stencilResidual) (physicsTranscript s) ⟨True.intro, hcols⟩ (by simpa using hrows)
  rw [hsum] at hc
  simpa only [verifyStencilResidualSumcheck, proveStencilResidualSumcheck, hcomm,
    commitPhysicsTable, canopyAjtaiDualPCS, DualPCS, canopyMerklePCS, ajtaiLatticePCS] using hc
/-- Unit-speed two-component Maxwell system in physical coordinates. -/
def unitMaxwellSystem : HyperbolicSystem :=
  ⟨["Ey", "Bz"], [.var "Bz", .var "Ey"], [0, 0], [0, 0], [1, 1], 1, 1/2⟩
def unitMaxwellCert : HyperbolicCert :=
  ⟨[[0, 1], [1, 0]], [[1, -1], [1, 1]], [1, -1], [[1/2, 1/2], [-1/2, 1/2]], [2, 2], [[1, 0], [0, 1]]⟩
example : check unitMaxwellSystem unitMaxwellCert = .ok := by decide +kernel
def q32BackwardStep (w : WordGrid) : WordGrid :=
  (List.range w.length).map fun i => BitVec.ofNat 64
    (((w.getD (nextCell w.length i) 0#64).toNat + (w.getD i 0#64).toNat) / 2)
def q32MaxwellStep (p m : WordGrid) : WordGrid × WordGrid := (q32StencilStep p, q32BackwardStep m)
def q32MaxwellRollout : Nat → WordGrid → WordGrid → WordGrid × WordGrid
  | 0, p, m => (p, m)
  | k + 1, p, m => let w := q32MaxwellRollout k p m; q32MaxwellStep w.1 w.2
def maxwellEnv (p m : WordGrid) : Env := fun i => if i = 0 then p else if i = 1 then m else []
def compileQ32MaxwellGpu (n : Nat) : Program :=
  .letE (.gather ⟨n, n, (List.range n).map (prevCell n)⟩ 0)
  (.letE (.map n (.scalar .add) [0, 1])
  (.letE (.literal (List.replicate n 1#64))
  (.letE (.map n .shr [1, 0])
  (.letE (.gather ⟨n, n, (List.range n).map (nextCell n)⟩ 5)
  (.letE (.map n (.scalar .add) [0, 6])
  (.letE (.map n .shr [0, 3]) (.ret [3, 0])))))))
theorem q32Maxwell_gpu_arraySource_sound (p m : WordGrid) (hl : m.length = p.length)
    (hp : InRange p) (hm : InRange m) :
    (compileQ32MaxwellGpu p.length).eval (maxwellEnv p m) = [q32StencilStep p, q32BackwardStep m] := by
  simp only [compileQ32MaxwellGpu, Program.eval, Rhs.eval, push, maxwellEnv, ↓reduceIte,
    List.map_cons, List.map_nil, Obend.Hardware.ArrayHypergraph.evalElemOp,
    Obend.Hardware.OpenHypergraph.evalHypergraphOpBv, List.getD_cons_zero, List.getD_cons_succ, Nat.one_ne_zero]
  simp only [List.cons.injEq, and_true]
  constructor
  all_goals
    simp only [q32StencilStep, q32BackwardStep, hl]
    apply List.map_congr_left
    intro i hi
    have hin := List.mem_range.mp hi
    simp only [List.map_map, Function.comp_def,
      Obend.Hardware.ArrayHypergraph.getD_range_map _ _ _ _ hin]
    have hone : (List.replicate p.length 1#64).getD i 0#64 = 1#64 := by
      simp [List.getD_eq_getElem?_getD, hin]
    rw [hone, Obend.Hardware.ArrayHypergraph.wordShr_eq]
  · exact word_half_sum_exact _ _ (getD_inRange p hp _) (getD_inRange p hp _)
  · exact word_half_sum_exact _ _ (getD_inRange m hm _) (getD_inRange m hm _)
theorem q32BackwardStep_inRange (w : WordGrid) (h : InRange w) : InRange (q32BackwardStep w) := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  have hl := getD_inRange w h (nextCell w.length i)
  have hr := getD_inRange w h i
  have hq : ((w.getD (nextCell w.length i) 0#64).toNat + (w.getD i 0#64).toNat) / 2 < amplitudeLimit := by
    unfold amplitudeLimit at *; omega
  have hq64 : ((w.getD (nextCell w.length i) 0#64).toNat + (w.getD i 0#64).toNat) / 2 < 2^64 := by
    unfold amplitudeLimit at hq; omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq64] using hq
theorem q32MaxwellRollout_range_length (p m : WordGrid) (hp : InRange p) (hm : InRange m) (k : Nat) :
    InRange (q32MaxwellRollout k p m).1 ∧ InRange (q32MaxwellRollout k p m).2 ∧
    (q32MaxwellRollout k p m).1.length = p.length ∧ (q32MaxwellRollout k p m).2.length = m.length := by
  induction k with
  | zero => exact ⟨hp, hm, rfl, rfl⟩
  | succ k ih => exact ⟨q32StencilStep_inRange _ ih.1, q32BackwardStep_inRange _ ih.2.1,
      by simpa [q32MaxwellRollout, q32MaxwellStep] using ih.2.2.1,
      by simpa [q32MaxwellRollout, q32MaxwellStep, q32BackwardStep] using ih.2.2.2⟩
def decodeMaxwellGrid (p m : WordGrid) : Grid := fun i c =>
  if c = 0 then (decodeNat (p.getD i 0#64).toNat + decodeNat (m.getD i 0#64).toNat) / 2
  else if c = 1 then (decodeNat (p.getD i 0#64).toNat - decodeNat (m.getD i 0#64).toNat) / 2 else 0
def rationalMaxwell (n : Nat) : Grid → Grid := rusanovStep 2 unitMaxwellSystem.jacobian 1 (1/2) n
theorem q32BackwardStep_defect (w : WordGrid) (h : InRange w) (i : Nat) (hi : i < w.length) :
    ratAbs (decodeNat ((q32BackwardStep w).getD i 0#64).toNat -
      (decodeNat (w.getD (nextCell w.length i) 0#64).toNat + decodeNat (w.getD i 0#64).toNat) / 2) ≤
      1 / (fixedScale : Rat) := by
  simp only [q32BackwardStep, Obend.Hardware.ArrayHypergraph.getD_range_map _ _ _ _ hi]
  have hl := getD_inRange w h (nextCell w.length i)
  have hr := getD_inRange w h i
  have hq : ((w.getD (nextCell w.length i) 0#64).toNat + (w.getD i 0#64).toNat) / 2 < 2^64 := by
    unfold amplitudeLimit at *; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  exact decode_half_defect _ _
theorem q32MaxwellStep_defect (p m : WordGrid) (hl : m.length = p.length)
    (hp : InRange p) (hm : InRange m) (i c : Nat) (hi : i < p.length) (hc : c < 2) :
    ratAbs (decodeMaxwellGrid (q32MaxwellStep p m).1 (q32MaxwellStep p m).2 i c -
      rationalMaxwell p.length (decodeMaxwellGrid p m) i c) ≤ 1 / (fixedScale : Rat) := by
  have h1 := q32StencilStep_defect p hp i hi
  have h2 := q32BackwardStep_defect m hm i (by omega)
  rw [rationalAdvection_cell] at h1
  simp only [decodeGrid] at h1
  rw [hl] at h2
  have hcases : c = 0 ∨ c = 1 := by omega
  rcases hcases with rfl | rfl <;>
    simp [q32MaxwellStep, rationalMaxwell, rusanovStep, unitMaxwellSystem,
      HyperbolicSystem.jacobian, getOr, envOf, evalDualRat, DualRat.var,
      mulVec, sumTo, decodeMaxwellGrid] <;>
    unfold ratAbs at * <;> split at h1 <;> split at h2 <;> split <;> grind
def q32MaxwellTrajectory (p m : WordGrid) (k : Nat) : Grid :=
  let w := q32MaxwellRollout k p m; decodeMaxwellGrid w.1 w.2
def maxwellDefectBudget (n : Nat) : Rat := (n : Rat) * 2 * (1 / (fixedScale : Rat) * (1 / (fixedScale : Rat)))
theorem q32Maxwell_gpu_rollout_within_rational_pde_tube (p m : WordGrid) (hl : m.length = p.length)
    (hp : InRange p) (hm : InRange m) (initial : Grid) (K : Nat) (η : Rat) (hη : 0 < η) :
    discreteHEnergy 2 p.length (matOf unitMaxwellCert.sym)
      (gridSub (q32MaxwellTrajectory p m K) (exactTrajectory (rationalMaxwell p.length) initial K)) ≤
    aprioriErrorTubeRec η (discreteHEnergy 2 p.length (matOf unitMaxwellCert.sym)
      (gridSub (decodeMaxwellGrid p m) initial)) (maxwellDefectBudget p.length) K := by
  have cert : Certified unitMaxwellSystem unitMaxwellCert := check_sound (by decide +kernel)
  have hd : ∀ k, discreteHEnergy 2 p.length (matOf unitMaxwellCert.sym)
      (stepDefect (rationalMaxwell p.length) (q32MaxwellTrajectory p m) k) ≤ maxwellDefectBudget p.length := by
    intro k
    have hk := q32MaxwellRollout_range_length p m hp hm k
    apply discreteHEnergy_le_of_linf_bound 2 p.length (matOf unitMaxwellCert.sym) _
      (1 / (fixedScale : Rat)) 2 (by decide +kernel) ?_ (by decide +kernel)
    intro i c hi hc
    simpa only [stepDefect, gridSub, q32MaxwellTrajectory, q32MaxwellRollout, hk.2.2.1] using
      q32MaxwellStep_defect _ _ (by omega) hk.1 hk.2.1 i c (by omega) hc
  exact accelerated_rusanov_apriori_error_tube 2 p.length unitMaxwellSystem.jacobian
    (matOf unitMaxwellCert.sym) 1 (1/2) η (maxwellDefectBudget p.length) hη initial
    (q32MaxwellTrajectory p m) cert.symm (certified_psd _ _ cert)
    (certified_step_contracts _ _ cert p.length) hd K
theorem unitMaxwell_exact_energy_decay (n K : Nat) (U0 : Grid) :
    discreteHEnergy 2 n (matOf unitMaxwellCert.sym) (exactTrajectory (rationalMaxwell n) U0 K) ≤
      discreteHEnergy 2 n (matOf unitMaxwellCert.sym) U0 := by
  have cert : Certified unitMaxwellSystem unitMaxwellCert := check_sound (by decide +kernel)
  induction K with
  | zero => exact Rat.le_refl
  | succ k ih => exact Rat.le_trans (certified_step_contracts _ _ cert n _) ih
def waveStep (back : Bool) (w : WordGrid) : WordGrid := if back then q32BackwardStep w else q32StencilStep w
def waveRun (back : Bool) : Nat → WordGrid → WordGrid
  | 0, w => w
  | k + 1, w => waveRun back k (waveStep back w)
theorem waveRun_step (b : Bool) (k : Nat) (w : WordGrid) :
    waveRun b k (waveStep b w) = waveStep b (waveRun b k w) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih => exact ih _
theorem maxwellRollout_waves (k : Nat) (p m : WordGrid) :
    q32MaxwellRollout k p m = (waveRun false k p, waveRun true k m) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change q32MaxwellStep (q32MaxwellRollout k p m).1 (q32MaxwellRollout k p m).2 = _
      rw [ih]
      change _ = (waveRun false k (waveStep false p), waveRun true k (waveStep true m))
      rw [waveRun_step, waveRun_step]; rfl
def waveRow (b : Bool) (w : WordGrid) (i : Nat) : StencilRow :=
  let l := (w.getD ((if b then nextCell else prevCell) w.length i) 0#64).toNat
  let c := (w.getD i 0#64).toNat
  ⟨l, c, (l + c) / 2, (l + c) % 2⟩
abbrev WaveLayer := List (StencilRow × StencilRowBits)
def layerOutput (rows : WaveLayer) : WordGrid := rows.map fun r => BitVec.ofNat 64 r.1.quotient
/-- Halo and temporal links are field equalities; Before constraints prevent modular aliases. -/
def checkWaveLayer (b : Bool) (w : WordGrid) (rows : WaveLayer) : Bool :=
  rows.length == w.length && (rows.zipIdx.all fun (rb, i) =>
    checkStencilRow rb.1 rb.2 &&
    Goldilocks.ofNat rb.1.left == Goldilocks.ofNat (waveRow b w i).left &&
    Goldilocks.ofNat rb.1.center == Goldilocks.ofNat (waveRow b w i).center)
theorem amplitude_field_injective (a b : Nat) (ha : a < amplitudeLimit) (hb : b < amplitudeLimit)
    (he : Goldilocks.ofNat a = Goldilocks.ofNat b) : a = b := by
  have h := congrArg Goldilocks.val he
  have ha' : a < Obend.Apps.ZkNtt.goldilocksPrime := by unfold amplitudeLimit at ha; change a < 18446744069414584321; omega
  have hb' : b < Obend.Apps.ZkNtt.goldilocksPrime := by unfold amplitudeLimit at hb; change b < 18446744069414584321; omega
  exact (Nat.mod_eq_of_lt ha').symm.trans (h.trans (Nat.mod_eq_of_lt hb'))
theorem checkWaveLayer_sound (b : Bool) (w : WordGrid) (rows : WaveLayer) (hw : InRange w)
    (h : checkWaveLayer b w rows = true) : layerOutput rows = waveStep b w := by
  simp only [checkWaveLayer, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  apply List.ext_getElem
  · cases b <;> simp [layerOutput, waveStep, q32StencilStep, q32BackwardStep, h.1]
  · intro i hi hj
    have hi' : i < rows.length := by simpa [layerOutput] using hi
    have hc := h.2 (rows[i], i) (List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hi']))
    have hv := checkStencilRow_sound _ _ hc.1.1
    have hl := amplitude_field_injective _ _ hv.1.1 (getD_inRange w hw _) hc.1.2
    have hm := amplitude_field_injective _ _ hv.1.2.1 (getD_inRange w hw _) hc.2
    simp only [layerOutput, List.getElem_map]
    rw [hv.2, hl, hm]
    cases b <;> simp [waveStep, q32StencilStep, q32BackwardStep, List.getElem_map, List.getElem_range]
def proveWaveLayer (b : Bool) (w : WordGrid) : WaveLayer :=
  (List.range w.length).map fun i => let r := waveRow b w i; (r, compileStencilRowBits r)
theorem waveRow_valid (b : Bool) (w : WordGrid) (hw : InRange w) (i : Nat) : (waveRow b w i).Valid := by
  have hl := getD_inRange w hw ((if b then nextCell else prevCell) w.length i)
  have hc := getD_inRange w hw i
  refine ⟨hl, hc, ?_, (q32_quotient_remainder _ _).2, (q32_quotient_remainder _ _).1⟩
  change (_ + _) / 2 < amplitudeLimit
  unfold amplitudeLimit at *; omega
theorem proveWaveLayer_complete (b : Bool) (w : WordGrid) (hw : InRange w) :
    checkWaveLayer b w (proveWaveLayer b w) = true := by
  simp only [checkWaveLayer, proveWaveLayer, List.length_map, List.length_range, beq_self_eq_true, Bool.true_and]
  apply List.all_eq_true.mpr
  intro ri hri
  have he := List.mem_zipIdx_iff_getElem?.mp hri
  have hi : ri.2 < w.length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simpa using this
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq] at he
  rw [← he]
  simp [checkStencilRow_complete _ (waveRow_valid b w hw ri.2)]
def checkWaveTrace (b : Bool) : WordGrid → List WaveLayer → Option WordGrid
  | w, [] => some w
  | w, r :: rs => if checkWaveLayer b w r then checkWaveTrace b (layerOutput r) rs else none
def proveWaveTrace (b : Bool) : Nat → WordGrid → List WaveLayer
  | 0, _ => []
  | k + 1, w => proveWaveLayer b w :: proveWaveTrace b k (waveStep b w)
theorem waveStep_inRange (b : Bool) (w : WordGrid) (hw : InRange w) : InRange (waveStep b w) := by
  cases b
  · exact q32StencilStep_inRange w hw
  · exact q32BackwardStep_inRange w hw
theorem checkWaveTrace_sound (b : Bool) (rs : List WaveLayer) (w out : WordGrid) (hw : InRange w)
    (h : checkWaveTrace b w rs = some out) : out = waveRun b rs.length w := by
  induction rs generalizing w with
  | nil => exact (Option.some.inj h).symm
  | cons r rs ih =>
    simp only [checkWaveTrace] at h
    split at h
    · rename_i hc
      rw [checkWaveLayer_sound b w r hw hc] at h
      exact ih _ (waveStep_inRange b w hw) h
    · cases h
theorem proveWaveTrace_complete (b : Bool) (k : Nat) (w : WordGrid) (hw : InRange w) :
    (proveWaveTrace b k w).length = k ∧
    checkWaveTrace b w (proveWaveTrace b k w) = some (waveRun b k w) := by
  induction k generalizing w with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hc := proveWaveLayer_complete b w hw
    have ht := ih (waveStep b w) (waveStep_inRange b w hw)
    simp only [proveWaveTrace, List.length_cons, ht.1, checkWaveTrace, hc, ↓reduceIte,
      checkWaveLayer_sound b w _ hw hc, ht.2, waveRun, and_self]
structure ZkPdeRolloutStmt where
  gridVars : Nat
  steps : Nat
  sensorCell : Nat
  claimedPlus : Nat
  claimedMinus : Nat
  energyMaxNum : Int
  energyMaxDen : Nat
  initCommitment : PhysicsCommitment
  resVars : Nat
  residualCommitment : PhysicsCommitment
  deriving DecidableEq
def zkPdeRolloutStmtFields (s : ZkPdeRolloutStmt) :=
  (s.gridVars, (s.steps, (s.sensorCell, (s.claimedPlus, (s.claimedMinus,
    ([s.energyMaxNum, s.energyMaxDen], (s.initCommitment, (s.resVars, s.residualCommitment))))))))
def zkPdeRolloutStmtBytes (s : ZkPdeRolloutStmt) : ByteArray := TranscriptEncode.encodeTranscriptBytes (zkPdeRolloutStmtFields s)
theorem zkPdeRolloutStmtBytes_injective (s t : ZkPdeRolloutStmt) (h : zkPdeRolloutStmtBytes s = zkPdeRolloutStmtBytes t) : s = t := by
  have he := LawfulTranscriptEncode.encodeTranscriptBytes_injective h
  change zkPdeRolloutStmtFields s = zkPdeRolloutStmtFields t at he
  cases s; cases t
  simp only [zkPdeRolloutStmtFields, Prod.mk.injEq, List.cons.injEq, Int.ofNat_inj, and_true] at he
  rcases he with ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩; rfl
def zkPdeTranscript (s : ZkPdeRolloutStmt) : Transcript .relationBound :=
  bindRelation "maxwell-q32-rollout@1" physicsRelationBytes (zkPdeRolloutStmtBytes s) (Transcript.newUnseeded ByteArray.empty)
def zkPdeInitTranscript (s : ZkPdeRolloutStmt) : Transcript .instanceBound :=
  (bindInstance s.initCommitment (zkPdeTranscript s)).transcript
def initChallenges : Nat → Transcript .instanceBound → List Goldilocks
  | 0, _ => []
  | k + 1, tr => let (r, tr') := squeezeGoldilocks tr; r :: initChallenges k tr'
theorem initChallenges_length (k : Nat) (tr : Transcript .instanceBound) : (initChallenges k tr).length = k := by
  induction k generalizing tr with
  | zero => rfl
  | succ k ih => simp [initChallenges, ih]
def zkInitClaim (s : ZkPdeRolloutStmt) (value : Goldilocks) : EvalClaim Goldilocks (s.gridVars + 1) :=
  ⟨initChallenges (s.gridVars + 1) (zkPdeInitTranscript s), initChallenges_length _ _, value⟩
def encodeMaxwellInit (p m : WordGrid) : List Goldilocks := (p ++ m).map fun x => Goldilocks.ofNat x.toNat
/-- Succinct commitments with transparent openings: this backend is not statistically
hiding. The receipt exposes the initial table and range-checked arithmetic trace. -/
structure ZkPdeRolloutReceipt where
  initPlus : WordGrid
  initMinus : WordGrid
  initPlusBits : List (Array Goldilocks)
  initMinusBits : List (Array Goldilocks)
  initClaimVal : Goldilocks
  initOpening : CanopyOpeningProof × AjtaiOpeningProof
  stepRowsPlus : List WaveLayer
  stepRowsMinus : List WaveLayer
  residualPadding : List Goldilocks
  sumcheckProof : StencilSumcheckProof
def checkInitBits : WordGrid → List (Array Goldilocks) → Bool
  | [], [] => true
  | x :: xs, b :: bs => checkBeforePolyArray (rangeConstraint x.toNat) b && checkInitBits xs bs
  | _, _ => false
def proveInitBits (w : WordGrid) := w.map fun x => compileBeforeWitness (rangeConstraint x.toNat)
theorem checkInitBits_sound (w : WordGrid) (bs : List (Array Goldilocks)) (h : checkInitBits w bs = true) : InRange w := by
  induction w generalizing bs with
  | nil => intro x hx; cases hx
  | cons x xs ih =>
    cases bs with
    | nil => cases h
    | cons b bs =>
      have hc : checkBeforePolyArray (rangeConstraint x.toNat) b = true ∧ checkInitBits xs bs = true := by
        simpa only [checkInitBits, Bool.and_eq_true] using h
      have hr := checkBeforePolyArray_sound hc.1
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hr
      · exact ih bs hc.2 y hy
theorem proveInitBits_complete (w : WordGrid) (hw : InRange w) : checkInitBits w (proveInitBits w) = true := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    have hx := hw x List.mem_cons_self
    have hc := checkBeforePolyArray_complete (rangeConstraint x.toNat) (by change beforeWidthSafe 48 = true; decide +kernel) hx (Nat.le_refl _) hx
    simpa only [checkInitBits, proveInitBits, List.map_cons, hc, Bool.true_and] using
      ih (fun y hy => hw y (List.mem_cons_of_mem x hy))
def fieldDifference (a b : Nat) : Goldilocks := CommRingOps.sub (Goldilocks.ofNat a) (Goldilocks.ofNat b)
def waveResiduals (b : Bool) : WordGrid → List WaveLayer → List Goldilocks
  | _, [] => []
  | w, rs :: rest => (rs.zipIdx.flatMap fun (r, i) => [stencilResidual r.1,
      fieldDifference r.1.left (waveRow b w i).left, fieldDifference r.1.center (waveRow b w i).center]) ++
      waveResiduals b (layerOutput rs) rest
def traceLast (w : WordGrid) (rs : List WaveLayer) : WordGrid := rs.foldl (fun _ r => layerOutput r) w
def rolloutResiduals (s : ZkPdeRolloutStmt) (r : ZkPdeRolloutReceipt) : List Goldilocks :=
  (encodeMaxwellInit r.initPlus r.initMinus |>.zip (r.initOpening.1.entries.map Prod.fst) |>.map fun (a,b) => CommRingOps.sub a b) ++
  waveResiduals false r.initPlus r.stepRowsPlus ++ waveResiduals true r.initMinus r.stepRowsMinus ++
  [fieldDifference ((traceLast r.initPlus r.stepRowsPlus).getD s.sensorCell 0#64).toNat s.claimedPlus,
   fieldDifference ((traceLast r.initMinus r.stepRowsMinus).getD s.sensorCell 0#64).toNat s.claimedMinus]
def paddedResiduals (s : ZkPdeRolloutStmt) (r : ZkPdeRolloutReceipt) : List Goldilocks :=
  let raw := rolloutResiduals s r; raw ++ List.replicate (2^s.resVars - raw.length) CommRingOps.zero
def checkRolloutCore (s : ZkPdeRolloutStmt) (r : ZkPdeRolloutReceipt) : Bool :=
  decide (s.sensorCell < 2^s.gridVars ∧ 0 < s.energyMaxDen ∧ s.claimedPlus < amplitudeLimit ∧ s.claimedMinus < amplitudeLimit ∧
    r.initPlus.length = 2^s.gridVars ∧ r.initMinus.length = 2^s.gridVars ∧
    r.stepRowsPlus.length = s.steps ∧ r.stepRowsMinus.length = s.steps) &&
  checkInitBits r.initPlus r.initPlusBits && checkInitBits r.initMinus r.initMinusBits &&
  decide (encodeMaxwellInit r.initPlus r.initMinus = r.initOpening.1.entries.map Prod.fst) &&
  (checkWaveTrace false r.initPlus r.stepRowsPlus == some (traceLast r.initPlus r.stepRowsPlus)) &&
  (checkWaveTrace true r.initMinus r.stepRowsMinus == some (traceLast r.initMinus r.stepRowsMinus)) &&
  decide (((traceLast r.initPlus r.stepRowsPlus).getD s.sensorCell 0#64).toNat = s.claimedPlus ∧
    ((traceLast r.initMinus r.stepRowsMinus).getD s.sensorCell 0#64).toNat = s.claimedMinus) &&
  decide (discreteHEnergy 2 (2^s.gridVars) (matOf unitMaxwellCert.sym) (decodeMaxwellGrid r.initPlus r.initMinus) ≤
    (s.energyMaxNum : Rat) / (s.energyMaxDen : Rat))
/-- Every arithmetic, halo, initial, temporal, and sensor residual is checked;
the same padded table is committed and opened by the statement-bound dual PIOP. -/
def verifyZkPdeRolloutReceipt (H : Hash32) (ppInit ppRes : AjtaiParams) (s : ZkPdeRolloutStmt) (r : ZkPdeRolloutReceipt) : Bool :=
  checkRolloutCore s r &&
  decide (commitPhysicsTable H ppInit (s.gridVars + 1) (r.initOpening.1.entries.map Prod.fst) = s.initCommitment ∧
    r.initOpening.2.shortLimbs = gadgetDecomposeTable (r.initOpening.1.entries.map Prod.fst) ∧
    gadgetRecomposeTable r.initOpening.2.shortLimbs = some (r.initOpening.1.entries.map Prod.fst)) &&
  ((canopyAjtaiDualPCS H ppInit).verifyEval ((), ()) (s.gridVars + 1) s.initCommitment (zkInitClaim s r.initClaimVal) r.initOpening (zkPdeInitTranscript s)).1 &&
  decide ((rolloutResiduals s r).length ≤ 2^s.resVars) &&
  decide (r.residualPadding = paddedResiduals s r) && r.residualPadding.all (· == CommRingOps.zero) &&
  decide (commitPhysicsTable H ppRes s.resVars r.residualPadding = s.residualCommitment) &&
  decide (r.sumcheckProof.opening.1.entries.map Prod.fst = r.residualPadding ∧
    r.sumcheckProof.opening.2.shortLimbs = gadgetDecomposeTable r.residualPadding) &&
  verifyDualSumcheckPIOP (canopyMerklePCS H) (ajtaiLatticePCS ppRes) ((), ()) 1 s.resVars s.residualCommitment
    CommRingOps.zero r.sumcheckProof.rounds r.sumcheckProof.opening (zkPdeTranscript s)
theorem traceLast_of_check (b : Bool) (rs : List WaveLayer) (w out : WordGrid)
    (h : checkWaveTrace b w rs = some out) : traceLast w rs = out := by
  induction rs generalizing w with
  | nil => exact Option.some.inj h
  | cons r rs ih =>
    simp only [checkWaveTrace] at h
    split at h
    · exact ih _ h
    · cases h
theorem waveResiduals_zero (b : Bool) (rs : List WaveLayer) (w out : WordGrid)
    (h : checkWaveTrace b w rs = some out) : (waveResiduals b w rs).all (· == CommRingOps.zero) = true := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih =>
    simp only [checkWaveTrace] at h
    split at h
    · rename_i hc
      have hh := ih _ h
      simp only [waveResiduals, List.all_append, hh, Bool.and_true, List.all_flatMap, List.all_eq_true]
      intro ri hri
      simp only [checkWaveLayer, Bool.and_eq_true] at hc
      have hr := List.all_eq_true.mp hc.2 ri hri
      simp only [Bool.and_eq_true, beq_iff_eq] at hr
      have hz := stencilResidual_zero _ (checkStencilRow_sound _ _ hr.1.1).1
      simp [hz, fieldDifference, hr.1.2, hr.2, LawfulCommRing.sub_self]
    · cases h
theorem dualOpen_tables (H : Hash32) (pp : AjtaiParams) (v : Nat) (tbl : List Goldilocks)
    {phase : TranscriptPhase} [CanSqueezeTranscript phase] (claim : EvalClaim Goldilocks v) (tr : Transcript phase) :
    let op := ((canopyAjtaiDualPCS H pp).openEval ((), ()) v tbl claim tr).1
    op.1.entries.map Prod.fst = tbl ∧ op.2.shortLimbs = gadgetDecomposeTable tbl := by
  exact ⟨map_fst_honest_entries H tbl, rfl⟩
def rolloutReceiptData (H : Hash32) (pp : AjtaiParams) (s : ZkPdeRolloutStmt) (p m : WordGrid) : ZkPdeRolloutReceipt :=
  let tbl := encodeMaxwellInit p m
  let value := mleEval tbl (zkInitClaim s CommRingOps.zero).point
  let op := ((canopyAjtaiDualPCS H pp).openEval ((), ()) (s.gridVars+1) tbl (zkInitClaim s value) (zkPdeInitTranscript s)).1
  ⟨p, m, proveInitBits p, proveInitBits m, value, op, proveWaveTrace false s.steps p,
    proveWaveTrace true s.steps m, [], ⟨[], ⟨⟨[]⟩, ⟨[]⟩⟩⟩⟩
/-- Honest transparent rollout prover. The statement supplies the two public
commitments; completeness requires their canonical values and sufficient padding. -/
def proveZkPdeRolloutReceipt (H : Hash32) (ppInit ppRes : AjtaiParams) (s : ZkPdeRolloutStmt) (p m : WordGrid) : ZkPdeRolloutReceipt :=
  let r := rolloutReceiptData H ppInit s p m
  let tbl := paddedResiduals s r
  let (rounds, claim, tr) := honestBoundSumcheckProver (commitPhysicsTable H ppRes s.resVars tbl) s.resVars tbl (zkPdeTranscript s)
  let op := ((canopyAjtaiDualPCS H ppRes).openEval ((), ()) s.resVars tbl claim tr).1
  { r with residualPadding := tbl, sumcheckProof := ⟨rounds, op⟩ }
theorem checkRolloutCore_complete (H : Hash32) (pp : AjtaiParams) (s : ZkPdeRolloutStmt) (p m : WordGrid)
    (hp : InRange p) (hm : InRange m) (hlen : p.length = 2^s.gridVars ∧ m.length = 2^s.gridVars)
    (hs : s.sensorCell < 2^s.gridVars ∧ 0 < s.energyMaxDen)
    (hobs : ((q32MaxwellRollout s.steps p m).1.getD s.sensorCell 0#64).toNat = s.claimedPlus ∧
      ((q32MaxwellRollout s.steps p m).2.getD s.sensorCell 0#64).toNat = s.claimedMinus)
    (he : discreteHEnergy 2 (2^s.gridVars) (matOf unitMaxwellCert.sym) (decodeMaxwellGrid p m) ≤ (s.energyMaxNum : Rat) / (s.energyMaxDen : Rat)) :
    checkRolloutCore s (rolloutReceiptData H pp s p m) = true := by
  have hp' := proveWaveTrace_complete false s.steps p hp
  have hm' := proveWaveTrace_complete true s.steps m hm
  have lp := traceLast_of_check _ _ _ _ hp'.2
  have lm := traceLast_of_check _ _ _ _ hm'.2
  have hr := q32MaxwellRollout_range_length p m hp hm s.steps
  have bp := getD_inRange _ hr.1 s.sensorCell
  have bm := getD_inRange _ hr.2.1 s.sensorCell
  rw [hobs.1] at bp; rw [hobs.2] at bm
  rw [maxwellRollout_waves] at hobs
  simp only [checkRolloutCore, rolloutReceiptData, hp'.1, hm'.1, hp'.2, hm'.2, lp, lm,
    proveInitBits_complete p hp, proveInitBits_complete m hm, (dualOpen_tables H pp _ _ _ _).1,
    beq_self_eq_true, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [and_true]
  exact ⟨⟨⟨hs.1, hs.2, bp, bm, hlen.1, hlen.2⟩, hobs⟩, decide_eq_true he⟩
theorem rolloutResiduals_zero (s : ZkPdeRolloutStmt) (r : ZkPdeRolloutReceipt) (h : checkRolloutCore s r = true) :
    (rolloutResiduals s r).all (· == CommRingOps.zero) = true := by
  simp only [checkRolloutCore, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hi⟩, hp⟩, hm⟩, hs⟩, _⟩
  simp only [rolloutResiduals, ← hi, List.zip, List.zipWith_self, List.map_map, Function.comp_def,
    LawfulCommRing.sub_self, List.all_append, waveResiduals_zero _ _ _ _ hp,
    waveResiduals_zero _ _ _ _ hm, fieldDifference, hs.1, hs.2]
  simp
theorem zeroTable_eq (xs : List Goldilocks) (h : xs.all (· == CommRingOps.zero) = true) :
    xs = List.replicate xs.length CommRingOps.zero := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.length_cons, List.replicate_succ, List.cons.injEq]
    exact ⟨h.1, ih h.2⟩
theorem proveZkPdeRolloutReceipt_complete (H : Hash32) (ppInit ppRes : AjtaiParams) (s : ZkPdeRolloutStmt) (p m : WordGrid)
    (hp : InRange p) (hm : InRange m) (hlen : p.length = 2^s.gridVars ∧ m.length = 2^s.gridVars)
    (hs : s.sensorCell < 2^s.gridVars ∧ 0 < s.energyMaxDen)
    (hobs : ((q32MaxwellRollout s.steps p m).1.getD s.sensorCell 0#64).toNat = s.claimedPlus ∧
      ((q32MaxwellRollout s.steps p m).2.getD s.sensorCell 0#64).toNat = s.claimedMinus)
    (he : discreteHEnergy 2 (2^s.gridVars) (matOf unitMaxwellCert.sym) (decodeMaxwellGrid p m) ≤ (s.energyMaxNum : Rat) / (s.energyMaxDen : Rat))
    (hcols : ppInit.cols = 4*2^(s.gridVars+1) ∧ ppRes.cols = 4*2^s.resVars)
    (hi : s.initCommitment = commitPhysicsTable H ppInit (s.gridVars+1) (encodeMaxwellInit p m))
    (hcap : (rolloutResiduals s (rolloutReceiptData H ppInit s p m)).length ≤ 2^s.resVars)
    (hr : s.residualCommitment = commitPhysicsTable H ppRes s.resVars (List.replicate (2^s.resVars) CommRingOps.zero)) :
    verifyZkPdeRolloutReceipt H ppInit ppRes s (proveZkPdeRolloutReceipt H ppInit ppRes s p m) = true := by
  let r := rolloutReceiptData H ppInit s p m
  have hc := checkRolloutCore_complete H ppInit s p m hp hm hlen hs hobs he
  have hz := zeroTable_eq _ (rolloutResiduals_zero s r hc)
  have hpad : paddedResiduals s r = List.replicate (2^s.resVars) CommRingOps.zero := by
    unfold paddedResiduals
    rw [hz, List.replicate_append_replicate]
    simp only [List.length_replicate]
    congr 1
    have hcapa : (rolloutResiduals s r).length ≤ 2^s.resVars := hcap
    omega
  dsimp only [r] at hpad
  have htlen : (encodeMaxwellInit p m).length = 2^(s.gridVars+1) := by
    simp [encodeMaxwellInit, hlen.1, hlen.2, Nat.pow_succ, Nat.mul_two]
  have hop := (canopyAjtaiDualPCS H ppInit).completeness ((), ()) (s.gridVars+1) (encodeMaxwellInit p m)
    (zkInitClaim s CommRingOps.zero).point (zkInitClaim s CommRingOps.zero).point_len (zkPdeInitTranscript s) ⟨trivial, hcols.1⟩ htlen
  have hsum : hypercubeSum s.resVars (List.replicate (2^s.resVars) (CommRingOps.zero : Goldilocks)) = CommRingOps.zero := by
    unfold hypercubeSum
    generalize (hypercube s.resVars).map (fun _ => (CommRingOps.one : Goldilocks)) = ws
    induction (2^s.resVars) generalizing ws with
    | zero => rfl
    | succ n ih => cases ws <;> simp [List.replicate_succ, innerProd, LawfulCommRing.zero_mul, LawfulCommRing.zero_add, ih]
  have hsc := verifyDualSumcheckPIOP_completeness (canopyMerklePCS H) (ajtaiLatticePCS ppRes) ((), ())
    (by decide : 1 ≤ (1 : Nat)) s.resVars (List.replicate (2^s.resVars) CommRingOps.zero) (zkPdeTranscript s)
    ⟨trivial, hcols.2⟩ List.length_replicate
  rw [hsum] at hsc
  have hcore : checkRolloutCore s (proveZkPdeRolloutReceipt H ppInit ppRes s p m) = true := hc
  simp only [verifyZkPdeRolloutReceipt, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hcore, ?_⟩, ?_⟩, hcap⟩, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [proveZkPdeRolloutReceipt, rolloutReceiptData, (dualOpen_tables H ppInit _ _ _ _).1,
      (dualOpen_tables H ppInit _ _ _ _).2, gadgetRecomposeTable_decompose, and_true]
    exact hi.symm
  · simpa only [proveZkPdeRolloutReceipt, rolloutReceiptData, hi, zkInitClaim, commitPhysicsTable, canopyAjtaiDualPCS, DualPCS, canopyMerklePCS, ajtaiLatticePCS] using hop
  · change (paddedResiduals s r).all _ = true
    rw [hpad]; simp
  · change commitPhysicsTable H ppRes s.resVars (paddedResiduals s r) = _
    rw [hpad, hr]
  · dsimp only [proveZkPdeRolloutReceipt]
    exact dualOpen_tables H ppRes s.resVars (paddedResiduals s r) (phase := .instanceBound)
      (honestBoundSumcheckProver (commitPhysicsTable H ppRes s.resVars (paddedResiduals s r)) s.resVars (paddedResiduals s r) (zkPdeTranscript s)).2.1
      (honestBoundSumcheckProver (commitPhysicsTable H ppRes s.resVars (paddedResiduals s r)) s.resVars (paddedResiduals s r) (zkPdeTranscript s)).2.2
  · simpa only [proveZkPdeRolloutReceipt, hpad, hr, commitPhysicsTable, canopyAjtaiDualPCS, DualPCS, canopyMerklePCS, ajtaiLatticePCS] using hsc
/-- A semantic witness includes the complete dual commitment, exact rational
energy safety, and a uniform error tube for every rollout time and positive η. -/
structure ValidMaxwellRolloutWitness (H : Hash32) (ppInit : AjtaiParams) (s : ZkPdeRolloutStmt) where
  wPlus0 : WordGrid
  wMinus0 : WordGrid
  lengths : wPlus0.length = 2^s.gridVars ∧ wMinus0.length = 2^s.gridVars
  ranges : InRange wPlus0 ∧ InRange wMinus0
  committed : (commitPhysicsTable H ppInit (s.gridVars+1) (encodeMaxwellInit wPlus0 wMinus0) = s.initCommitment)
  sensor : ((q32MaxwellRollout s.steps wPlus0 wMinus0).1.getD s.sensorCell 0#64 = BitVec.ofNat 64 s.claimedPlus ∧
    (q32MaxwellRollout s.steps wPlus0 wMinus0).2.getD s.sensorCell 0#64 = BitVec.ofNat 64 s.claimedMinus)
  energy : (discreteHEnergy 2 (2^s.gridVars) (matOf unitMaxwellCert.sym)
    (exactTrajectory (rationalMaxwell (2^s.gridVars)) (decodeMaxwellGrid wPlus0 wMinus0) s.steps) ≤
      (s.energyMaxNum : Rat) / (s.energyMaxDen : Rat))
  tube : (∀ k η, 0 < η → discreteHEnergy 2 (2^s.gridVars) (matOf unitMaxwellCert.sym)
    (gridSub (q32MaxwellTrajectory wPlus0 wMinus0 k)
      (exactTrajectory (rationalMaxwell (2^s.gridVars)) (decodeMaxwellGrid wPlus0 wMinus0) k)) ≤
    aprioriErrorTubeRec η (discreteHEnergy 2 (2^s.gridVars) (matOf unitMaxwellCert.sym)
      (gridSub (decodeMaxwellGrid wPlus0 wMinus0) (decodeMaxwellGrid wPlus0 wMinus0))) (maxwellDefectBudget (2^s.gridVars)) k)

abbrev RolloutDualBreak (H : Hash32) (pp : AjtaiParams) (s : ZkPdeRolloutStmt) :=
  PSum (Obend.Judge.Computational.HashCollisionWitness H.eval (merkleMaxPreimageBytes (s.gridVars+1)))
    (Obend.Judge.Computational.SISShortVecWitness pp.modulus 131070 pp.matrix)
/-- Reconstruction uses only the checked, transparent witness columns. -/
def acceptedRolloutWitness (H : Hash32) (ppInit ppRes : AjtaiParams) (s : ZkPdeRolloutStmt) (r : ZkPdeRolloutReceipt)
    (h : verifyZkPdeRolloutReceipt H ppInit ppRes s r = true) : ValidMaxwellRolloutWitness H ppInit s := by
  simp only [verifyZkPdeRolloutReceipt, Bool.and_eq_true, decide_eq_true_eq] at h
  have hc := h.1.1.1.1.1.1.1.1
  have hcomm := h.1.1.1.1.1.1.1.2.1
  simp only [checkRolloutCore, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨shape, hp⟩, hm⟩, henc⟩, htp⟩, htm⟩, hobs⟩, he⟩
  rcases shape with ⟨_, _, _, _, lp, lm, sp, sm⟩
  have rp := checkInitBits_sound _ _ hp
  have rm := checkInitBits_sound _ _ hm
  have ep := checkWaveTrace_sound _ _ _ _ rp htp
  have em := checkWaveTrace_sound _ _ _ _ rm htm
  rw [sp] at ep; rw [sm] at em
  refine ⟨r.initPlus, r.initMinus, ⟨lp, lm⟩, ⟨rp, rm⟩, ?_, ?_, ?_, ?_⟩
  · rw [henc]; exact hcomm
  · rw [maxwellRollout_waves]
    constructor
    · rw [← ep, ← hobs.1]; simp
    · rw [← em, ← hobs.2]; simp
  · exact Rat.le_trans (unitMaxwell_exact_energy_decay _ _ _) he
  · intro k η hη
    simpa only [lp] using q32Maxwell_gpu_rollout_within_rational_pde_tube _ _ (lm.trans lp.symm) rp rm
      (decodeMaxwellGrid r.initPlus r.initMinus) k η hη
/-- Standalone acceptance reconstructs a table with exactly the public dual
commitment; no external committed table or cryptographic hardness is assumed. -/
def extractZkPdeRollout_or_dualBreak (H : Hash32) (ppInit ppRes : AjtaiParams) (s : ZkPdeRolloutStmt) (r : ZkPdeRolloutReceipt)
    (h : verifyZkPdeRolloutReceipt H ppInit ppRes s r = true) :
    PSum (ValidMaxwellRolloutWitness H ppInit s) (RolloutDualBreak H ppInit s) :=
  .inl (acceptedRolloutWitness H ppInit ppRes s r h)
/-- Against a different committed table both primitives have been broken. The
caller may select the Merkle or lattice certificate; both are constructed without choice. -/
def extractZkPdeRolloutAgainstCommitted_or_dualBreak (H : Hash32) (ppInit ppRes : AjtaiParams)
    (s : ZkPdeRolloutStmt) (r : ZkPdeRolloutReceipt) (committedInit : List Goldilocks)
    (hlen : committedInit.length = 2^(s.gridVars+1)) (hcols : ppInit.cols = 4*2^(s.gridVars+1))
    (hcomm : s.initCommitment = commitPhysicsTable H ppInit (s.gridVars+1) committedInit)
    (h : verifyZkPdeRolloutReceipt H ppInit ppRes s r = true) (latticeFirst : Bool := false) :
    PSum {w : ValidMaxwellRolloutWitness H ppInit s // encodeMaxwellInit w.wPlus0 w.wMinus0 = committedInit}
      (RolloutDualBreak H ppInit s) := by
  exact (
    let w := acceptedRolloutWitness H ppInit ppRes s r h
    if heq : encodeMaxwellInit w.wPlus0 w.wMinus0 = committedInit then .inl ⟨w, heq⟩ else
    have hwlen : (encodeMaxwellInit w.wPlus0 w.wMinus0).length = 2^(s.gridVars+1) := by
      simp [encodeMaxwellInit, w.lengths.1, w.lengths.2, Nat.pow_succ, Nat.mul_two]
    have hboth := w.committed.trans hcomm
    if latticeFirst then .inr (.inr (extractPhysicsCommitmentBreaks H ppInit _ _ _ hwlen hlen hcols heq hboth)) else
    have hacc : (canopyVerifyEval H (s.gridVars+1) (canopyCommit H (s.gridVars+1) committedInit)
        (zkInitClaim s r.initClaimVal) r.initOpening.1
        (absorbMsg dualTrack1Label ByteArray.empty (zkPdeInitTranscript s))).1 = true := by
      simp only [verifyZkPdeRolloutReceipt, Bool.and_eq_true, decide_eq_true_eq] at h
      have hd := h.1.1.1.1.1.1.2
      rw [hcomm] at hd
      exact (show _ ∧ _ from (by simpa [canopyAjtaiDualPCS, DualPCS, dualVerifyEval, canopyMerklePCS,
        ajtaiLatticePCS, dualVerdictJoin, Bool.and_eq_true, commitPhysicsTable] using hd)).1
    have hopen : encodeMaxwellInit w.wPlus0 w.wMinus0 = r.initOpening.1.entries.map Prod.fst := by
      simp only [verifyZkPdeRolloutReceipt, Bool.and_eq_true, decide_eq_true_eq] at h
      have hc := h.1.1.1.1.1.1.1.1
      simp only [checkRolloutCore, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact hc.1.1.1.1.2
    .inr (.inl (extractCanopyOpenMerkleCollision H committedInit hlen r.initOpening.1 _ hacc
      (fun he => heq (hopen.trans he))))
  )

theorem verifyZkPdeRolloutReceipt_sound_or_dualBreak (H : Hash32) (ppInit ppRes : AjtaiParams)
    (s : ZkPdeRolloutStmt) (r : ZkPdeRolloutReceipt) (h : verifyZkPdeRolloutReceipt H ppInit ppRes s r = true) :
    Nonempty (ValidMaxwellRolloutWitness H ppInit s) ∨ Nonempty (RolloutDualBreak H ppInit s) := by
  cases extractZkPdeRollout_or_dualBreak H ppInit ppRes s r h with
  | inl w => exact .inl ⟨w⟩
  | inr b => exact .inr ⟨b⟩
def gpuMaxwellRollout : Nat → WordGrid → WordGrid → WordGrid × WordGrid
  | 0, p, m => (p, m)
  | k + 1, p, m =>
      let w := gpuMaxwellRollout k p m
      let out := (compileQ32MaxwellGpu w.1.length).eval (maxwellEnv w.1 w.2)
      (out.getD 0 [], out.getD 1 [])
theorem gpuMaxwellRollout_eq_q32 (p m : WordGrid) (hl : m.length = p.length) (hp : InRange p) (hm : InRange m) (k : Nat) :
    gpuMaxwellRollout k p m = q32MaxwellRollout k p m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := q32MaxwellRollout_range_length p m hp hm k
    simp only [gpuMaxwellRollout, ih, q32Maxwell_gpu_arraySource_sound _ _ (by omega) hk.1 hk.2.1,
      List.getD_cons_zero, List.getD_cons_succ, q32MaxwellRollout, q32MaxwellStep]
theorem gpuMaxwellRollout_within_tube (p m : WordGrid) (hl : m.length = p.length) (hp : InRange p) (hm : InRange m)
    (initial : Grid) (K : Nat) (η : Rat) (hη : 0 < η) :
    let w := gpuMaxwellRollout K p m
    discreteHEnergy 2 p.length (matOf unitMaxwellCert.sym)
      (gridSub (decodeMaxwellGrid w.1 w.2) (exactTrajectory (rationalMaxwell p.length) initial K)) ≤
    aprioriErrorTubeRec η (discreteHEnergy 2 p.length (matOf unitMaxwellCert.sym)
      (gridSub (decodeMaxwellGrid p m) initial)) (maxwellDefectBudget p.length) K := by
  simpa only [gpuMaxwellRollout_eq_q32 p m hl hp hm K, q32MaxwellTrajectory] using
    q32Maxwell_gpu_rollout_within_rational_pde_tube p m hl hp hm initial K η hη
end Obend.SymbolicZk.StencilRolloutStark
