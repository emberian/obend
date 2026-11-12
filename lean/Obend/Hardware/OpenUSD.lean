module
/-
# Obend.Hardware.OpenUSD — Mechanized Metatheory of Apple/Pixar OpenUSD (`SdfPath`, `Pcp` `LIVERPS`, Affine Arithmetic SDF Enclosures & Inductive `timeSamples` Persistence)

Provides the first mechanized metatheory in Lean 4 for **Apple/Pixar OpenUSD (`Universal Scene
Description`)** specialized to **physical engineering parts, implicit `F-Rep`/`SDF` solids, and
causal temporal persistence**:

1. **Hierarchical `SdfPath` & Non-Destructive `Relocates` (`E` in `LIVERPS`)**:
   - Models OpenUSD scene-graph paths (`SdfPath := List String`) and non-destructive namespace
     relocation (`applyUsdRelocate srcPrefix dstPrefix path`),
   - Proves **`usd_relocate_roundtrip_exact`**: relocating a subtree from `srcPrefix` to `dstPrefix`
     and back restores every descendant `SdfPath` without loss or collision.
2. **Affine Arithmetic (`AffineForm1D`) for Correlation-Preserving SDF / F-Rep Enclosures**:
   - Models 1st-order Affine Arithmetic forms $\hat{x} = c_0 + c_1 \epsilon_1 + c_2 \epsilon_2$ over
     symbolic noise variables $\epsilon_1, \epsilon_2 \in [-1, 1]$,
   - Proves **`affine_sub_self_exact_zero`** and **`affine_to_interval_encloses_eval`**.
3. **Inductive Temporal Persistence Over OpenUSD `timeSamples` Tracks**:
   - Proves **`usd_lifecycle_invariant_preserved`**: if the initial raw billet at $t_0$ satisfies a
     physical part invariant $P$ and every transition step in the OpenUSD `timeSamples` track
     preserves $P$, then every manufactured/in-field state along the part's history satisfies $P$.
-/
public import Obend.Hardware.Kinematics
public import Obend.Law.Contract
public import Obend.Law.Proofs.Claim
public import Obend.Leaf.Flatten
@[expose] public section

namespace Obend.Hardware.OpenUSD
open Obend.Core.Term (Term Evaluates Value Step Steps)
open Obend.Core.Data (Data)
open Obend.Law (CellContract Holds Admits Narrows CellTrace cellContract_relaw_sound
  cellContract_trace_sound law3 guard okT andT falseT leNat natT lawEnv scons_zero scons_succ
  admits_iff guard_ok andT_true leNat_true natT_eval evaluates_self evaluates_step
  evaluates_steps evaluates_of_steps evaluates_ifBool)
open Obend.Hardware.Accelerators
open Obend.Hardware.GeometryCAM
set_option autoImplicit false

/-! ## 1. OpenUSD `SdfPath` Hierarchy & Non-Destructive `Relocates` (`E` in `LIVERPS`) -/

/-- An OpenUSD hierarchical scene path (e.g. `["Factory", "StatorAssy", "Slot_01", "Microchannel"]`). -/
abbrev SdfPath := List String

/-- Relocate an `SdfPath` by replacing prefix `src` with `dst` if `src` is a prefix of `p`. -/
def relocateSuffix (dst : SdfPath) : SdfPath → SdfPath → Option SdfPath
  | [], rest => some (dst ++ rest)
  | s :: srcRest, p :: pathRest =>
    if s == p then relocateSuffix dst srcRest pathRest else none
  | _ :: _, [] => none

/-- Apply a non-destructive OpenUSD `relocates` arc `(srcPrefix ↦ dstPrefix)` to `path`. -/
def applyUsdRelocate (srcPrefix dstPrefix path : SdfPath) : SdfPath :=
  match relocateSuffix dstPrefix srcPrefix path with
  | some relocated => relocated
  | none           => path

/-- Lemma: `relocateSuffix dst src (src ++ suffix) = some (dst ++ suffix)` for all `src, dst, suffix`. -/
theorem relocateSuffix_append_exact (src dst suffix : SdfPath) :
    relocateSuffix dst src (src ++ suffix) = some (dst ++ suffix) := by
  induction src with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.cons_append, relocateSuffix, beq_self_eq_true, ↓reduceIte, ih]

/-- **OpenUSD Non-Destructive `Relocates` Round-Trip Theorem (`usd_relocate_roundtrip_exact`)**. -/
theorem usd_relocate_roundtrip_exact (src dst suffix : SdfPath) :
    applyUsdRelocate dst src (applyUsdRelocate src dst (src ++ suffix)) = src ++ suffix := by
  unfold applyUsdRelocate
  rw [relocateSuffix_append_exact src dst suffix]
  dsimp only
  rw [relocateSuffix_append_exact dst src suffix]

/-! ## 2. Affine Arithmetic (`AffineForm1D` & Full 3D `AffineForm3D`) for Correlation-Preserving SDF / F-Rep Enclosures -/

/-- A 1st-order Affine Arithmetic form $\hat{x} = c_0 + c_1 \epsilon_1 + c_2 \epsilon_2$ over two
spatial noise symbols $\epsilon_1, \epsilon_2 \in [-1, 1]$. -/
structure AffineForm1D where
  c0 : Int
  c1 : Int
  c2 : Int
  deriving DecidableEq, Repr

/-- Evaluate an `AffineForm1D` at noise realization $(\epsilon_1, \epsilon_2) \in [-1, 1]^2$. -/
def AffineForm1D.eval (af : AffineForm1D) (eps1 eps2 : Int) : Int :=
  af.c0 + af.c1 * eps1 + af.c2 * eps2

/-- Integer absolute value $|z|$. -/
def intAbs (z : Int) : Int :=
  if 0 ≤ z then z else -z

/-- Total uncertainty radius $|c_1| + |c_2|$ of an `AffineForm1D`. -/
def AffineForm1D.radius (af : AffineForm1D) : Int :=
  intAbs af.c1 + intAbs af.c2

/-- Convert an `AffineForm1D` into its guaranteed bounding interval `[c0 - radius, c0 + radius]`. -/
def AffineForm1D.toInterval (af : AffineForm1D) : FloatInterval where
  lo := af.c0 - af.radius
  hi := af.c0 + af.radius

/-- Affine addition $\hat{a} + \hat{b}$. -/
def AffineForm1D.add (a b : AffineForm1D) : AffineForm1D where
  c0 := a.c0 + b.c0
  c1 := a.c1 + b.c1
  c2 := a.c2 + b.c2

/-- Affine subtraction $\hat{a} - \hat{b}$ (preserves noise-symbol correlations!). -/
def AffineForm1D.sub (a b : AffineForm1D) : AffineForm1D where
  c0 := a.c0 - b.c0
  c1 := a.c1 - b.c1
  c2 := a.c2 - b.c2

/-- **Affine Dependency Cancellation Theorem (`affine_sub_self_exact_zero`)**. -/
theorem affine_sub_self_exact_zero (a : AffineForm1D) :
    (AffineForm1D.sub a a).toInterval = { lo := 0, hi := 0 } := by
  dsimp only [AffineForm1D.sub, AffineForm1D.toInterval, AffineForm1D.radius, intAbs]
  have hSub0 : a.c0 - a.c0 = 0 := Int.sub_self a.c0
  have hSub1 : a.c1 - a.c1 = 0 := Int.sub_self a.c1
  have hSub2 : a.c2 - a.c2 = 0 := Int.sub_self a.c2
  rw [hSub0, hSub1, hSub2]
  rfl

/-- Lemma: For any `c : Int` and `eps : Int` with `-1 ≤ eps ∧ eps ≤ 1`,
`-(intAbs c) ≤ c * eps ∧ c * eps ≤ intAbs c`. -/
theorem mul_unit_noise_bounded (c eps : Int) (hEps : -1 ≤ eps ∧ eps ≤ 1) :
    -(intAbs c) ≤ c * eps ∧ c * eps ≤ intAbs c := by
  unfold intAbs
  split
  · rename_i hc
    have hLo : c * (-1) ≤ c * eps := int_mul_le_mul_of_nonneg_left (-1) eps c hEps.1 hc
    have hHi : c * eps ≤ c * 1 := int_mul_le_mul_of_nonneg_left eps 1 c hEps.2 hc
    omega
  · rename_i hc
    have hNegC : 0 ≤ -c := by omega
    have hLo : (-c) * (-1) ≤ (-c) * eps := int_mul_le_mul_of_nonneg_left (-1) eps (-c) hEps.1 hNegC
    have hHi : (-c) * eps ≤ (-c) * 1 := int_mul_le_mul_of_nonneg_left eps 1 (-c) hEps.2 hNegC
    rw [Int.neg_mul, Int.neg_mul] at hLo hHi
    omega

/-- **Universal Affine-to-Interval Enclosure Theorem (`affine_to_interval_encloses_eval`)**. -/
theorem affine_to_interval_encloses_eval
    (af : AffineForm1D) (eps1 eps2 : Int)
    (h1 : -1 ≤ eps1 ∧ eps1 ≤ 1)
    (h2 : -1 ≤ eps2 ∧ eps2 ≤ 1) :
    af.toInterval.contains (af.eval eps1 eps2) := by
  dsimp only [AffineForm1D.toInterval, AffineForm1D.radius, AffineForm1D.eval, FloatInterval.contains]
  have hb1 := mul_unit_noise_bounded af.c1 eps1 h1
  have hb2 := mul_unit_noise_bounded af.c2 eps2 h2
  omega

/-! ### 2B. Full 3D Affine Arithmetic (`AffineForm3D`) With Non-Affine Error Radius & Full `FRepExpr` Evaluation -/

/-- Full 3D 1st-order Affine Arithmetic form (`fidget-core` / Stolfi–de Figueiredo):
$$\hat{f}(\epsilon_x, \epsilon_y, \epsilon_z, \epsilon_e) = c_0 + c_x \epsilon_x + c_y \epsilon_y + c_z \epsilon_z + \text{err} \cdot \epsilon_e$$
where:
* `c0`: central value at the octree cell midpoint,
* `cx`, `cy`, `cz`: 1st-order spatial sensitivities with respect to $\epsilon_x, \epsilon_y, \epsilon_z \in [-1, 1]$,
* `err`: non-negative accumulated error radius bounding non-affine operations (`mul`, `sq`, `min`, `max`). -/
structure AffineForm3D where
  c0  : Int
  cx  : Int
  cy  : Int
  cz  : Int
  err : Nat
  deriving DecidableEq, Repr

/-- Homogeneous spatial linear offset $c_x \epsilon_x + c_y \epsilon_y + c_z \epsilon_z$. -/
def AffineForm3D.spatialOffset (af : AffineForm3D) (ex ey ez : Int) : Int :=
  af.cx * ex + af.cy * ey + af.cz * ez

/-- Linear spatial evaluation $c_0 + (c_x \epsilon_x + c_y \epsilon_y + c_z \epsilon_z)$. -/
def AffineForm3D.linearEval (af : AffineForm3D) (ex ey ez : Int) : Int :=
  af.c0 + af.spatialOffset ex ey ez

/-- Full evaluation of an `AffineForm3D` at spatial noise $(\epsilon_x, \epsilon_y, \epsilon_z) \in [-1, 1]^3$
and non-affine error symbol $\epsilon_e \in [-1, 1]$. -/
def AffineForm3D.eval (af : AffineForm3D) (ex ey ez ee : Int) : Int :=
  af.linearEval ex ey ez + Int.ofNat af.err * ee

/-- Total uncertainty radius $|c_x| + |c_y| + |c_z| + \text{err}$ of an `AffineForm3D`. -/
def AffineForm3D.radius (af : AffineForm3D) : Int :=
  intAbs af.cx + intAbs af.cy + intAbs af.cz + Int.ofNat af.err

/-- Convert an `AffineForm3D` into its guaranteed bounding interval `[c0 - radius, c0 + radius]`. -/
def AffineForm3D.toInterval (af : AffineForm3D) : FloatInterval where
  lo := af.c0 - af.radius
  hi := af.c0 + af.radius

/-- Predicate stating that concrete value `v : Int` lies within the non-affine error tube `±af.err`
around the linear spatial evaluation `af.linearEval ex ey ez`. -/
def AffineForm3D.enclosesAt (af : AffineForm3D) (ex ey ez v : Int) : Prop :=
  af.linearEval ex ey ez - Int.ofNat af.err ≤ v ∧
  v ≤ af.linearEval ex ey ez + Int.ofNat af.err

/-- Constant `AffineForm3D` with zero spatial sensitivity and zero error. -/
def AffineForm3D.const (c : Int) : AffineForm3D where
  c0  := c
  cx  := 0
  cy  := 0
  cz  := 0
  err := 0

/-- 3D affine addition $\hat{a} + \hat{b}$. -/
def AffineForm3D.add (a b : AffineForm3D) : AffineForm3D where
  c0  := a.c0 + b.c0
  cx  := a.cx + b.cx
  cy  := a.cy + b.cy
  cz  := a.cz + b.cz
  err := a.err + b.err

/-- 3D affine subtraction $\hat{a} - \hat{b}$ (preserves linear spatial correlations!). -/
def AffineForm3D.sub (a b : AffineForm3D) : AffineForm3D where
  c0  := a.c0 - b.c0
  cx  := a.cx - b.cx
  cy  := a.cy - b.cy
  cz  := a.cz - b.cz
  err := a.err + b.err

/-- 3D affine negation $-\hat{a}$. -/
def AffineForm3D.neg (a : AffineForm3D) : AffineForm3D where
  c0  := -a.c0
  cx  := -a.cx
  cy  := -a.cy
  cz  := -a.cz
  err := a.err

/-- 3D affine scaling by a non-negative integer `k : Nat`. -/
def AffineForm3D.scalePos (k : Nat) (a : AffineForm3D) : AffineForm3D where
  c0  := Int.ofNat k * a.c0
  cx  := Int.ofNat k * a.cx
  cy  := Int.ofNat k * a.cy
  cz  := Int.ofNat k * a.cz
  err := k * a.err

/-- 3D affine isotropic surface offset $\hat{a} - r$. -/
def AffineForm3D.offset (r : Int) (a : AffineForm3D) : AffineForm3D where
  c0  := a.c0 - r
  cx  := a.cx
  cy  := a.cy
  cz  := a.cz
  err := a.err

/-- Lift a `FloatInterval` into an `AffineForm3D` centred at `(lo + hi) / 2` whose error radius is
the half-width: the larger of the two distances from the centre to an end (they differ by one when
`lo + hi` is odd, because `/` floors). Before 2026-11-04 the radius was the sum of the two, the full
width, which doubled every crease that `min`/`max` falls back on. -/
def AffineForm3D.fromInterval (iv : FloatInterval) : AffineForm3D :=
  let mid := (iv.lo + iv.hi) / 2
  let rad := (Max.max (intAbs (iv.hi - mid)) (intAbs (mid - iv.lo))).toNat
  { c0 := mid, cx := 0, cy := 0, cz := 0, err := rad }

/-- 3D affine multiplication $\hat{a} \cdot \hat{b}$ (Stolfi & de Figueiredo 1997):
propagates the 1st-order bilinear sensitivities $b_0 c_{x,a} + a_0 c_{x,b}$ and bounds the
quadratic / cross error by $\text{rad}(a)\cdot\text{rad}(b) + |b_0|\,\text{err}_a + |a_0|\,\text{err}_b$. -/
def AffineForm3D.mul (a b : AffineForm3D) : AffineForm3D :=
  let radProd := a.radius * b.radius + intAbs b.c0 * Int.ofNat a.err + intAbs a.c0 * Int.ofNat b.err
  { c0  := a.c0 * b.c0
    cx  := b.c0 * a.cx + a.c0 * b.cx
    cy  := b.c0 * a.cy + a.c0 * b.cy
    cz  := b.c0 * a.cz + a.c0 * b.cz
    err := radProd.toNat }

/-- 3D affine squaring $\hat{a}^2 = \hat{a} \cdot \hat{a}$. -/
def AffineForm3D.sq (a : AffineForm3D) : AffineForm3D :=
  AffineForm3D.mul a a

/-- 3D affine `min` ($\min(\hat{a}, \hat{b})$ for CSG union):
uses `fidget`'s `ivMinChoice` to preserve the exact 3D affine form when one branch dominates,
and falls back to the tight interval intersection `fromInterval (ivMin ...)` on overlapping creases. -/
def AffineForm3D.min (a b : AffineForm3D) : AffineForm3D :=
  match ivMinChoice a.toInterval b.toInterval with
  | .left  => a
  | .right => b
  | _      => AffineForm3D.fromInterval (ivMin a.toInterval b.toInterval)

/-- 3D affine `max` ($\max(\hat{a}, \hat{b})$ for CSG intersection):
uses `fidget`'s `ivMaxChoice` to preserve the exact 3D affine form when one branch dominates,
and falls back to the tight interval enclosure `fromInterval (ivMax ...)` on overlapping creases. -/
def AffineForm3D.max (a b : AffineForm3D) : AffineForm3D :=
  match ivMaxChoice a.toInterval b.toInterval with
  | .left  => a
  | .right => b
  | _      => AffineForm3D.fromInterval (ivMax a.toInterval b.toInterval)

/-- Evaluate an arbitrary `FRepExpr` CSG tree over 3D affine coordinate forms `ax, ay, az : AffineForm3D`. -/
def evalFRepAffine3D (ax ay az : AffineForm3D) : FRepExpr → AffineForm3D
  | .const c      => AffineForm3D.const c
  | .varX         => ax
  | .varY         => ay
  | .varZ         => az
  | .add a b      => (evalFRepAffine3D ax ay az a).add (evalFRepAffine3D ax ay az b)
  | .sub a b      => (evalFRepAffine3D ax ay az a).sub (evalFRepAffine3D ax ay az b)
  | .scalePos k a => (evalFRepAffine3D ax ay az a).scalePos k
  | .sq a         => (evalFRepAffine3D ax ay az a).sq
  | .csgUnion a b => (evalFRepAffine3D ax ay az a).min (evalFRepAffine3D ax ay az b)
  | .csgInter a b => (evalFRepAffine3D ax ay az a).max (evalFRepAffine3D ax ay az b)
  | .csgDiff a b  => (evalFRepAffine3D ax ay az a).max (evalFRepAffine3D ax ay az b).neg
  | .offset r a   => (evalFRepAffine3D ax ay az a).offset r

/-- Basic properties of `intAbs`: `0 ≤ intAbs z`, `z ≤ intAbs z`, and `-z ≤ intAbs z`. -/
theorem le_intAbs_and_nonneg (z : Int) : 0 ≤ intAbs z ∧ z ≤ intAbs z ∧ -z ≤ intAbs z := by
  unfold intAbs
  omega

/-- Every `AffineForm3D` has a non-negative total uncertainty radius (`0 ≤ af.radius`). -/
theorem affine3d_radius_nonneg (af : AffineForm3D) : 0 ≤ af.radius := by
  dsimp only [AffineForm3D.radius]
  have hx := le_intAbs_and_nonneg af.cx
  have hy := le_intAbs_and_nonneg af.cy
  have hz := le_intAbs_and_nonneg af.cz
  have hErr : 0 ≤ Int.ofNat af.err := Int.natCast_nonneg af.err
  omega

/-- **3D Affine Dependency Cancellation Theorem (`affine3d_sub_self_zero_linear`)**:
Subtracting any 3D affine form `a` from itself cancels all three spatial noise sensitivities
(`cx = 0, cy = 0, cz = 0`) and nominal center (`c0 = 0`), and when `a.err = 0`, collapses the
bounding interval to the exact zero point `{ lo := 0, hi := 0 }`. -/
theorem affine3d_sub_self_zero_linear (a : AffineForm3D) (hErr : a.err = 0) :
    (a.sub a).c0 = 0 ∧
    (a.sub a).cx = 0 ∧
    (a.sub a).cy = 0 ∧
    (a.sub a).cz = 0 ∧
    (a.sub a).err = 0 ∧
    (a.sub a).toInterval = { lo := 0, hi := 0 } := by
  dsimp only [AffineForm3D.sub, AffineForm3D.toInterval, AffineForm3D.radius, intAbs]
  have h0 : a.c0 - a.c0 = 0 := Int.sub_self a.c0
  have hx : a.cx - a.cx = 0 := Int.sub_self a.cx
  have hy : a.cy - a.cy = 0 := Int.sub_self a.cy
  have hz : a.cz - a.cz = 0 := Int.sub_self a.cz
  rw [h0, hx, hy, hz, hErr]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Lemma: Any value `v` satisfying `af.enclosesAt ex ey ez v` for unit noise `(ex, ey, ez) ∈ [-1, 1]^3`
lies inside `af.toInterval`. -/
theorem affine3d_enclosesAt_to_interval
    (af : AffineForm3D) (ex ey ez v : Int)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (hEnc : af.enclosesAt ex ey ez v) :
    af.toInterval.contains v := by
  dsimp only [AffineForm3D.toInterval, AffineForm3D.radius, AffineForm3D.enclosesAt,
    AffineForm3D.linearEval, AffineForm3D.spatialOffset, FloatInterval.contains] at *
  have hbx := mul_unit_noise_bounded af.cx ex hEx
  have hby := mul_unit_noise_bounded af.cy ey hEy
  have hbz := mul_unit_noise_bounded af.cz ez hEz
  omega

/-- Lemma: Evaluating `af.eval ex ey ez ee` at any unit error symbol `ee ∈ [-1, 1]` satisfies
`af.enclosesAt ex ey ez (af.eval ex ey ez ee)`. -/
theorem affine3d_eval_enclosesAt
    (af : AffineForm3D) (ex ey ez ee : Int)
    (hEe : -1 ≤ ee ∧ ee ≤ 1) :
    af.enclosesAt ex ey ez (af.eval ex ey ez ee) := by
  dsimp only [AffineForm3D.enclosesAt, AffineForm3D.eval]
  have hbe := mul_unit_noise_bounded (Int.ofNat af.err) ee hEe
  have hErr : 0 ≤ Int.ofNat af.err := Int.natCast_nonneg af.err
  have hAbsErr : intAbs (Int.ofNat af.err) = Int.ofNat af.err := by
    unfold intAbs
    omega
  omega

/-- **Universal 3D Affine-to-Interval Enclosure Theorem (`affine3d_to_interval_encloses_eval`)**:
For every `af : AffineForm3D` and every realization of unit spatial and error symbols
$\epsilon_x, \epsilon_y, \epsilon_z, \epsilon_e \in [-1, 1]$, `af.toInterval` contains
`af.eval ex ey ez ee`. -/
theorem affine3d_to_interval_encloses_eval
    (af : AffineForm3D) (ex ey ez ee : Int)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1)
    (hEz : -1 ≤ ez ∧ ez ≤ 1) (hEe : -1 ≤ ee ∧ ee ≤ 1) :
    af.toInterval.contains (af.eval ex ey ez ee) :=
  affine3d_enclosesAt_to_interval af ex ey ez (af.eval ex ey ez ee)
    hEx hEy hEz (affine3d_eval_enclosesAt af ex ey ez ee hEe)

/-- Lemma: `AffineForm3D.const c` encloses `c` at every noise realization. -/
theorem affine3d_const_enclosesAt (c ex ey ez : Int) :
    (AffineForm3D.const c).enclosesAt ex ey ez c := by
  dsimp only [AffineForm3D.const, AffineForm3D.enclosesAt, AffineForm3D.linearEval,
    AffineForm3D.spatialOffset]
  simp only [Int.zero_mul, Int.add_zero]
  change _ - 0 ≤ c ∧ c ≤ _ + 0
  omega

/-- Lemma: `AffineForm3D.add` preserves `enclosesAt`. -/
theorem affine3d_add_enclosesAt (a b : AffineForm3D) (ex ey ez va vb : Int)
    (ha : a.enclosesAt ex ey ez va) (hb : b.enclosesAt ex ey ez vb) :
    (a.add b).enclosesAt ex ey ez (va + vb) := by
  dsimp only [AffineForm3D.add, AffineForm3D.enclosesAt, AffineForm3D.linearEval,
    AffineForm3D.spatialOffset] at *
  have hx : (a.cx + b.cx) * ex = a.cx * ex + b.cx * ex := Int.add_mul a.cx b.cx ex
  have hy : (a.cy + b.cy) * ey = a.cy * ey + b.cy * ey := Int.add_mul a.cy b.cy ey
  have hz : (a.cz + b.cz) * ez = a.cz * ez + b.cz * ez := Int.add_mul a.cz b.cz ez
  have hErr : Int.ofNat (a.err + b.err) = Int.ofNat a.err + Int.ofNat b.err := rfl
  omega

/-- Lemma: `AffineForm3D.sub` preserves `enclosesAt`. -/
theorem affine3d_sub_enclosesAt (a b : AffineForm3D) (ex ey ez va vb : Int)
    (ha : a.enclosesAt ex ey ez va) (hb : b.enclosesAt ex ey ez vb) :
    (a.sub b).enclosesAt ex ey ez (va - vb) := by
  dsimp only [AffineForm3D.sub, AffineForm3D.enclosesAt, AffineForm3D.linearEval,
    AffineForm3D.spatialOffset] at *
  have hx : (a.cx - b.cx) * ex = a.cx * ex - b.cx * ex := Int.sub_mul a.cx b.cx ex
  have hy : (a.cy - b.cy) * ey = a.cy * ey - b.cy * ey := Int.sub_mul a.cy b.cy ey
  have hz : (a.cz - b.cz) * ez = a.cz * ez - b.cz * ez := Int.sub_mul a.cz b.cz ez
  have hErr : Int.ofNat (a.err + b.err) = Int.ofNat a.err + Int.ofNat b.err := rfl
  omega

/-- Lemma: `AffineForm3D.neg` preserves `enclosesAt`. -/
theorem affine3d_neg_enclosesAt (a : AffineForm3D) (ex ey ez va : Int)
    (ha : a.enclosesAt ex ey ez va) :
    a.neg.enclosesAt ex ey ez (-va) := by
  dsimp only [AffineForm3D.neg, AffineForm3D.enclosesAt, AffineForm3D.linearEval,
    AffineForm3D.spatialOffset] at *
  have hx : (-a.cx) * ex = -(a.cx * ex) := Int.neg_mul a.cx ex
  have hy : (-a.cy) * ey = -(a.cy * ey) := Int.neg_mul a.cy ey
  have hz : (-a.cz) * ez = -(a.cz * ez) := Int.neg_mul a.cz ez
  omega

/-- Lemma: `AffineForm3D.offset` preserves `enclosesAt`. -/
theorem affine3d_offset_enclosesAt (r : Int) (a : AffineForm3D) (ex ey ez va : Int)
    (ha : a.enclosesAt ex ey ez va) :
    (a.offset r).enclosesAt ex ey ez (va - r) := by
  dsimp only [AffineForm3D.offset, AffineForm3D.enclosesAt, AffineForm3D.linearEval,
    AffineForm3D.spatialOffset] at *
  omega

/-- Lemma: `(a.scalePos k).linearEval ex ey ez = Int.ofNat k * a.linearEval ex ey ez`. -/
theorem scalePos_linearEval_eq (k : Nat) (a : AffineForm3D) (ex ey ez : Int) :
    (a.scalePos k).linearEval ex ey ez = Int.ofNat k * a.linearEval ex ey ez := by
  dsimp only [AffineForm3D.scalePos, AffineForm3D.linearEval, AffineForm3D.spatialOffset]
  have hx : Int.ofNat k * a.cx * ex = Int.ofNat k * (a.cx * ex) := Int.mul_assoc _ _ _
  have hy : Int.ofNat k * a.cy * ey = Int.ofNat k * (a.cy * ey) := Int.mul_assoc _ _ _
  have hz : Int.ofNat k * a.cz * ez = Int.ofNat k * (a.cz * ez) := Int.mul_assoc _ _ _
  have hAdd : Int.ofNat k * (a.c0 + (a.cx * ex + a.cy * ey + a.cz * ez)) =
      Int.ofNat k * a.c0 + Int.ofNat k * (a.cx * ex) + Int.ofNat k * (a.cy * ey) + Int.ofNat k * (a.cz * ez) := by
    rw [Int.mul_add, Int.mul_add, Int.mul_add]
    omega
  omega

/-- Lemma: `AffineForm3D.scalePos` preserves `enclosesAt`. -/
theorem affine3d_scalePos_enclosesAt (k : Nat) (a : AffineForm3D) (ex ey ez va : Int)
    (ha : a.enclosesAt ex ey ez va) :
    (a.scalePos k).enclosesAt ex ey ez (Int.ofNat k * va) := by
  unfold AffineForm3D.enclosesAt at *
  have hk : (0 : Int) ≤ Int.ofNat k := Int.natCast_nonneg k
  have hLin := scalePos_linearEval_eq k a ex ey ez
  have hErr : Int.ofNat (a.scalePos k).err = Int.ofNat k * Int.ofNat a.err := rfl
  have hLo := int_mul_le_mul_of_nonneg_left (a.linearEval ex ey ez - Int.ofNat a.err) va (Int.ofNat k) ha.1 hk
  have hHi := int_mul_le_mul_of_nonneg_left va (a.linearEval ex ey ez + Int.ofNat a.err) (Int.ofNat k) ha.2 hk
  rw [Int.mul_sub] at hLo
  rw [Int.mul_add] at hHi
  omega

/-- Lemma: `AffineForm3D.fromInterval iv` encloses any `v` contained in `iv`. -/
theorem affine3d_fromInterval_enclosesAt (iv : FloatInterval) (ex ey ez v : Int)
    (hIn : iv.contains v) :
    (AffineForm3D.fromInterval iv).enclosesAt ex ey ez v := by
  dsimp only [AffineForm3D.fromInterval, AffineForm3D.enclosesAt, AffineForm3D.linearEval,
    AffineForm3D.spatialOffset, FloatInterval.contains] at *
  simp only [Int.zero_mul, Int.add_zero]
  have h1 := le_intAbs_and_nonneg (iv.hi - (iv.lo + iv.hi) / 2)
  have h2 := le_intAbs_and_nonneg ((iv.lo + iv.hi) / 2 - iv.lo)
  have hRad : Int.ofNat (Max.max (intAbs (iv.hi - (iv.lo + iv.hi) / 2))
        (intAbs ((iv.lo + iv.hi) / 2 - iv.lo))).toNat =
      Max.max (intAbs (iv.hi - (iv.lo + iv.hi) / 2)) (intAbs ((iv.lo + iv.hi) / 2 - iv.lo)) :=
    Int.toNat_of_nonneg (by omega)
  omega

/-- Symmetric product bound: if `-r1 ≤ x ≤ r1` and `-r2 ≤ y ≤ r2` with `0 ≤ r1, 0 ≤ r2`,
then `-(r1 * r2) ≤ x * y ∧ x * y ≤ r1 * r2`. -/
theorem int_abs_mul_bound (x y r1 r2 : Int)
    (_hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hx : -r1 ≤ x ∧ x ≤ r1) (hy : -r2 ≤ y ∧ y ≤ r2) :
    -(r1 * r2) ≤ x * y ∧ x * y ≤ r1 * r2 := by
  by_cases hxPos : 0 ≤ x
  · have hPos1 : x * y ≤ x * r2 := int_mul_le_mul_of_nonneg_left y r2 x hy.2 hxPos
    have hPos2 : x * (-y) ≤ x * r2 := int_mul_le_mul_of_nonneg_left (-y) r2 x (by omega) hxPos
    have hPos3 : x * r2 ≤ r1 * r2 := int_mul_le_mul_of_nonneg_right x r1 r2 hx.2 hr2
    rw [Int.mul_neg x y] at hPos2
    omega
  · have hxNeg : 0 ≤ -x := by omega
    have hxLe : -x ≤ r1 := by omega
    have hNeg1 : (-x) * (-y) ≤ (-x) * r2 := int_mul_le_mul_of_nonneg_left (-y) r2 (-x) (by omega) hxNeg
    have hNeg2 : (-x) * y ≤ (-x) * r2 := int_mul_le_mul_of_nonneg_left y r2 (-x) hy.2 hxNeg
    have hNeg3 : (-x) * r2 ≤ r1 * r2 := int_mul_le_mul_of_nonneg_right (-x) r1 r2 hxLe hr2
    rw [Int.neg_mul_neg x y] at hNeg1
    rw [Int.neg_mul x y] at hNeg2
    omega

/-- Bilinear expansion of `(a.mul b).linearEval ex ey ez`. -/
theorem mul_linearEval_eq (a b : AffineForm3D) (ex ey ez : Int) :
    (a.mul b).linearEval ex ey ez =
      a.c0 * b.c0 +
      b.c0 * a.spatialOffset ex ey ez +
      a.c0 * b.spatialOffset ex ey ez := by
  dsimp only [AffineForm3D.mul, AffineForm3D.linearEval, AffineForm3D.spatialOffset]
  have hx : (b.c0 * a.cx + a.c0 * b.cx) * ex = b.c0 * (a.cx * ex) + a.c0 * (b.cx * ex) := by
    rw [Int.add_mul, Int.mul_assoc, Int.mul_assoc]
  have hy : (b.c0 * a.cy + a.c0 * b.cy) * ey = b.c0 * (a.cy * ey) + a.c0 * (b.cy * ey) := by
    rw [Int.add_mul, Int.mul_assoc, Int.mul_assoc]
  have hz : (b.c0 * a.cz + a.c0 * b.cz) * ez = b.c0 * (a.cz * ez) + a.c0 * (b.cz * ez) := by
    rw [Int.add_mul, Int.mul_assoc, Int.mul_assoc]
  have ha : b.c0 * (a.cx * ex + a.cy * ey + a.cz * ez) =
      b.c0 * (a.cx * ex) + b.c0 * (a.cy * ey) + b.c0 * (a.cz * ez) := by
    rw [Int.mul_add, Int.mul_add]
  have hb : a.c0 * (b.cx * ex + b.cy * ey + b.cz * ez) =
      a.c0 * (b.cx * ex) + a.c0 * (b.cy * ey) + a.c0 * (b.cz * ez) := by
    rw [Int.mul_add, Int.mul_add]
  omega

/-- Exact algebraic decomposition of the non-affine multiplication remainder:
$$v_a v_b - (a_0 b_0 + b_0 L_a + a_0 L_b) = (v_a - a_0)(v_b - b_0) + b_0(v_a - (a_0 + L_a)) + a_0(v_b - (b_0 + L_b)).$$ -/
theorem int_bilinear_error_decomp (a0 b0 La Lb va vb : Int) :
    va * vb - (a0 * b0 + b0 * La + a0 * Lb) =
      (va - a0) * (vb - b0) + b0 * (va - (a0 + La)) + a0 * (vb - (b0 + Lb)) := by
  have h1 : (va - a0) * (vb - b0) = va * vb - a0 * vb - b0 * va + a0 * b0 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm va b0]
    omega
  have h2 : b0 * (va - (a0 + La)) = b0 * va - a0 * b0 - b0 * La := by
    rw [Int.mul_sub, Int.mul_add, Int.mul_comm b0 a0]
    omega
  have h3 : a0 * (vb - (b0 + Lb)) = a0 * vb - a0 * b0 - a0 * Lb := by
    rw [Int.mul_sub, Int.mul_add]
    omega
  omega

/-- Lemma: `AffineForm3D.mul` preserves `enclosesAt` over $[-1, 1]^3$. -/
theorem affine3d_mul_enclosesAt
    (a b : AffineForm3D) (ex ey ez va vb : Int)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (ha : a.enclosesAt ex ey ez va) (hb : b.enclosesAt ex ey ez vb) :
    (a.mul b).enclosesAt ex ey ez (va * vb) := by
  have hIa := affine3d_enclosesAt_to_interval a ex ey ez va hEx hEy hEz ha
  have hIb := affine3d_enclosesAt_to_interval b ex ey ez vb hEx hEy hEz hb
  dsimp only [AffineForm3D.toInterval, FloatInterval.contains] at hIa hIb
  have hRadA := affine3d_radius_nonneg a
  have hRadB := affine3d_radius_nonneg b
  have hAbsA0 := le_intAbs_and_nonneg a.c0
  have hAbsB0 := le_intAbs_and_nonneg b.c0
  have hErrA : (0 : Int) ≤ Int.ofNat a.err := Int.natCast_nonneg a.err
  have hErrB : (0 : Int) ≤ Int.ofNat b.err := Int.natCast_nonneg b.err
  have hDa : -a.radius ≤ va - a.c0 ∧ va - a.c0 ≤ a.radius := by omega
  have hDb : -b.radius ≤ vb - b.c0 ∧ vb - b.c0 ≤ b.radius := by omega
  have hEa : -Int.ofNat a.err ≤ va - a.linearEval ex ey ez ∧ va - a.linearEval ex ey ez ≤ Int.ofNat a.err := by
    unfold AffineForm3D.enclosesAt at ha
    omega
  have hEb : -Int.ofNat b.err ≤ vb - b.linearEval ex ey ez ∧ vb - b.linearEval ex ey ez ≤ Int.ofNat b.err := by
    unfold AffineForm3D.enclosesAt at hb
    omega
  have hProd1 := int_abs_mul_bound (va - a.c0) (vb - b.c0) a.radius b.radius hRadA hRadB hDa hDb
  have hProd2 := int_abs_mul_bound b.c0 (va - a.linearEval ex ey ez) (intAbs b.c0) (Int.ofNat a.err)
    hAbsB0.1 hErrA (by omega) hEa
  have hProd3 := int_abs_mul_bound a.c0 (vb - b.linearEval ex ey ez) (intAbs a.c0) (Int.ofNat b.err)
    hAbsA0.1 hErrB (by omega) hEb
  have hNonneg1 := int_mul_nonneg a.radius b.radius hRadA hRadB
  have hNonneg2 := int_mul_nonneg (intAbs b.c0) (Int.ofNat a.err) hAbsB0.1 hErrA
  have hNonneg3 := int_mul_nonneg (intAbs a.c0) (Int.ofNat b.err) hAbsA0.1 hErrB
  have hErrEq :
      Int.ofNat (a.mul b).err =
        a.radius * b.radius + intAbs b.c0 * Int.ofNat a.err + intAbs a.c0 * Int.ofNat b.err := by
    dsimp only [AffineForm3D.mul]
    exact Int.toNat_of_nonneg (by omega)
  have hLin := mul_linearEval_eq a b ex ey ez
  have hDecomp :
      va * vb - (a.c0 * b.c0 + b.c0 * a.spatialOffset ex ey ez + a.c0 * b.spatialOffset ex ey ez) =
        (va - a.c0) * (vb - b.c0) + b.c0 * (va - a.linearEval ex ey ez) + a.c0 * (vb - b.linearEval ex ey ez) :=
    int_bilinear_error_decomp a.c0 b.c0 (a.spatialOffset ex ey ez) (b.spatialOffset ex ey ez) va vb
  unfold AffineForm3D.enclosesAt
  omega

/-- Lemma: `AffineForm3D.sq` preserves `enclosesAt` over $[-1, 1]^3$. -/
theorem affine3d_sq_enclosesAt
    (a : AffineForm3D) (ex ey ez va : Int)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (ha : a.enclosesAt ex ey ez va) :
    a.sq.enclosesAt ex ey ez (va * va) :=
  affine3d_mul_enclosesAt a a ex ey ez va va hEx hEy hEz ha ha

/-- Lemma: `AffineForm3D.min` preserves `enclosesAt` over $[-1, 1]^3$. -/
theorem affine3d_min_enclosesAt
    (a b : AffineForm3D) (ex ey ez va vb : Int)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (ha : a.enclosesAt ex ey ez va) (hb : b.enclosesAt ex ey ez vb) :
    (a.min b).enclosesAt ex ey ez (min va vb) := by
  unfold AffineForm3D.min
  have hIa := affine3d_enclosesAt_to_interval a ex ey ez va hEx hEy hEz ha
  have hIb := affine3d_enclosesAt_to_interval b ex ey ez vb hEx hEy hEz hb
  cases hC : ivMinChoice a.toInterval b.toInterval with
  | left =>
    dsimp only
    rw [ivMinChoice_left_sound _ _ _ _ hIa hIb hC]
    exact ha
  | right =>
    dsimp only
    rw [ivMinChoice_right_sound _ _ _ _ hIa hIb hC]
    exact hb
  | unknown =>
    dsimp only
    apply affine3d_fromInterval_enclosesAt
    dsimp only [ivMin, FloatInterval.contains] at hIa hIb ⊢
    omega
  | both =>
    dsimp only
    apply affine3d_fromInterval_enclosesAt
    dsimp only [ivMin, FloatInterval.contains] at hIa hIb ⊢
    omega

/-- Lemma: `AffineForm3D.max` preserves `enclosesAt` over $[-1, 1]^3$. -/
theorem affine3d_max_enclosesAt
    (a b : AffineForm3D) (ex ey ez va vb : Int)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (ha : a.enclosesAt ex ey ez va) (hb : b.enclosesAt ex ey ez vb) :
    (a.max b).enclosesAt ex ey ez (max va vb) := by
  unfold AffineForm3D.max
  have hIa := affine3d_enclosesAt_to_interval a ex ey ez va hEx hEy hEz ha
  have hIb := affine3d_enclosesAt_to_interval b ex ey ez vb hEx hEy hEz hb
  cases hC : ivMaxChoice a.toInterval b.toInterval with
  | left =>
    dsimp only
    rw [ivMaxChoice_left_sound _ _ _ _ hIa hIb hC]
    exact ha
  | right =>
    dsimp only
    rw [ivMaxChoice_right_sound _ _ _ _ hIa hIb hC]
    exact hb
  | unknown =>
    dsimp only
    apply affine3d_fromInterval_enclosesAt
    dsimp only [ivMax, FloatInterval.contains] at hIa hIb ⊢
    omega
  | both =>
    dsimp only
    apply affine3d_fromInterval_enclosesAt
    dsimp only [ivMax, FloatInterval.contains] at hIa hIb ⊢
    omega

/-- Inductive 3D Affine F-Rep / SDF Tube Enclosure Lemma (`evalFRepAffine3D_enclosesAt`):
For every `FRepExpr` CSG tree `e`, if `x, y, z` are enclosed by `ax, ay, az` at unit spatial
noise `(ex, ey, ez) ∈ [-1, 1]^3`, then `evalFRepPoint x y z e` is enclosed by
`evalFRepAffine3D ax ay az e` at `(ex, ey, ez)`. -/
theorem evalFRepAffine3D_enclosesAt
    (ax ay az : AffineForm3D) (ex ey ez x y z : Int) (e : FRepExpr)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (hAx : ax.enclosesAt ex ey ez x)
    (hAy : ay.enclosesAt ex ey ez y)
    (hAz : az.enclosesAt ex ey ez z) :
    (evalFRepAffine3D ax ay az e).enclosesAt ex ey ez (evalFRepPoint x y z e) := by
  induction e with
  | const c =>
    exact affine3d_const_enclosesAt c ex ey ez
  | varX =>
    exact hAx
  | varY =>
    exact hAy
  | varZ =>
    exact hAz
  | add a b iha ihb =>
    exact affine3d_add_enclosesAt _ _ ex ey ez _ _ iha ihb
  | sub a b iha ihb =>
    exact affine3d_sub_enclosesAt _ _ ex ey ez _ _ iha ihb
  | scalePos k a iha =>
    exact affine3d_scalePos_enclosesAt k _ ex ey ez _ iha
  | sq a iha =>
    exact affine3d_sq_enclosesAt _ ex ey ez _ hEx hEy hEz iha
  | csgUnion a b iha ihb =>
    exact affine3d_min_enclosesAt _ _ ex ey ez _ _ hEx hEy hEz iha ihb
  | csgInter a b iha ihb =>
    exact affine3d_max_enclosesAt _ _ ex ey ez _ _ hEx hEy hEz iha ihb
  | csgDiff a b iha ihb =>
    exact affine3d_max_enclosesAt _ _ ex ey ez _ _ hEx hEy hEz
      iha (affine3d_neg_enclosesAt _ ex ey ez _ ihb)
  | offset r a iha =>
    exact affine3d_offset_enclosesAt r _ ex ey ez _ iha

/-- **Universal 3D Affine F-Rep / CSG Point Enclosure Theorem (`evalFRepAffine3D_encloses_point`)**:
For any 3D affine coordinate forms `ax, ay, az : AffineForm3D`, any unit spatial noise realization
`(ex, ey, ez) ∈ [-1, 1]^3`, any point `(x, y, z)` enclosed at `(ex, ey, ez)`, and any constructive
solid geometry tree `e : FRepExpr`, the interval `(evalFRepAffine3D ax ay az e).toInterval`
is guaranteed to contain the exact point evaluation `evalFRepPoint x y z e`. -/
theorem evalFRepAffine3D_encloses_point
    (ax ay az : AffineForm3D) (ex ey ez x y z : Int) (e : FRepExpr)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (hAx : ax.enclosesAt ex ey ez x)
    (hAy : ay.enclosesAt ex ey ez y)
    (hAz : az.enclosesAt ex ey ez z) :
    (evalFRepAffine3D ax ay az e).toInterval.contains (evalFRepPoint x y z e) :=
  affine3d_enclosesAt_to_interval (evalFRepAffine3D ax ay az e) ex ey ez (evalFRepPoint x y z e)
    hEx hEy hEz (evalFRepAffine3D_enclosesAt ax ay az ex ey ez x y z e hEx hEy hEz hAx hAy hAz)

/-! ## 3. Inductive Temporal Persistence Over OpenUSD `timeSamples` Tracks & Forever-Crown `CellContract` Refinement -/

/-- A physical state of a manufactured part at a specific OpenUSD `timeCode`. -/
structure UsdPhysicalState where
  timeCode        : Nat
  wallThicknessUm : Int
  peakTempMilliC  : Int
  receiptDigest   : Nat
  deriving DecidableEq, Repr

/-- Physical safety invariant for a part across its OpenUSD lifecycle. -/
def checkPartLifecycleInvariant (minWallUm maxTempMilliC : Int) (st : UsdPhysicalState) : Bool :=
  decide (minWallUm ≤ st.wallThicknessUm ∧ st.peakTempMilliC ≤ maxTempMilliC)

/-- A 2-state OpenUSD temporal transition (`CellContract` step) from `oldSt` to `newSt`. -/
def checkUsdTransitionStep
    (minWallUm maxTempMilliC : Int) (oldSt newSt : UsdPhysicalState) : Bool :=
  decide (oldSt.timeCode < newSt.timeCode) &&
  decide (0 < newSt.receiptDigest) &&
  checkPartLifecycleInvariant minWallUm maxTempMilliC newSt

/-- Verify an entire OpenUSD `timeSamples` chain starting from `initSt`. -/
def checkUsdTimeSampleChain
    (minWallUm maxTempMilliC : Int) : UsdPhysicalState → List UsdPhysicalState → Bool
  | _, [] => true
  | cur, next :: rest =>
    checkUsdTransitionStep minWallUm maxTempMilliC cur next &&
    checkUsdTimeSampleChain minWallUm maxTempMilliC next rest

/-- Retrieve the final physical state at the end of a `timeSamples` chain. -/
def finalUsdState (initSt : UsdPhysicalState) : List UsdPhysicalState → UsdPhysicalState
  | []          => initSt
  | next :: rest => finalUsdState next rest

/-- **Inductive Temporal Persistence Theorem (`usd_lifecycle_invariant_preserved`)**. -/
theorem usd_lifecycle_invariant_preserved
    (minWallUm maxTempMilliC : Int)
    (initSt : UsdPhysicalState)
    (steps : List UsdPhysicalState)
    (hInit : checkPartLifecycleInvariant minWallUm maxTempMilliC initSt = true)
    (hChain : checkUsdTimeSampleChain minWallUm maxTempMilliC initSt steps = true) :
    checkPartLifecycleInvariant minWallUm maxTempMilliC (finalUsdState initSt steps) = true := by
  induction steps generalizing initSt with
  | nil => exact hInit
  | cons next rest ih =>
    dsimp only [checkUsdTimeSampleChain] at hChain
    simp only [Bool.and_eq_true] at hChain
    have hStep := hChain.1
    unfold checkUsdTransitionStep at hStep
    simp only [Bool.and_eq_true] at hStep
    exact ih next hStep.2 hChain.2

/-! ### 3B. Connecting OpenUSD Part Lifecycle Invariants to `Obend.Law.CellContract` & `Narrows` Forever-Crowns -/

theorem steps_binaryLeft_usd {p : Obend.Core.Term.Primitive} {l l' r : Term} (h : Steps l l') :
    Steps (.binary p l r) (.binary p l' r) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryLeft _ _ s) ih

theorem steps_binaryRight_usd {p : Obend.Core.Term.Primitive} {l r r' : Term} (hl : Value l) (h : Steps r r') :
    Steps (.binary p l r) (.binary p l r') := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryRight _ _ hl s) ih

/-- Core4 single-state predicate (`Term`) asserting that an OpenUSD physical part state record
satisfies both the minimum wall-thickness floor (`minWallUm ≤ wallThicknessUm`) and maximum
operating temperature ceiling (`peakTempMilliC ≤ maxTempMilliC`). -/
def usdPartInvariantTerm (minWallUm maxTempMilliC : Nat) : Term :=
  .lam
    (andT
      (leNat (natT minWallUm) (.get (.bound 0) "wallThicknessUm"))
      (leNat (.get (.bound 0) "peakTempMilliC") (natT maxTempMilliC)))

@[simp] theorem subst_usdPartInvariantTerm (minWallUm maxTempMilliC : Nat) (σ : Nat → Term) :
    (usdPartInvariantTerm minWallUm maxTempMilliC).substitute σ =
      usdPartInvariantTerm minWallUm maxTempMilliC := by
  simp [usdPartInvariantTerm, andT, leNat, natT, falseT, Term.substitute,
    Obend.Core.Term.liftSubstitution]

@[simp] theorem instantiate_usdPartInvariantBody (minWallUm maxTempMilliC : Nat) (arg : Term) :
    Obend.Core.Term.instantiate
      (andT
        (leNat (natT minWallUm) (.get (.bound 0) "wallThicknessUm"))
        (leNat (.get (.bound 0) "peakTempMilliC") (natT maxTempMilliC)))
      arg =
    andT
      (leNat (natT minWallUm) (.get arg "wallThicknessUm"))
      (leNat (.get arg "peakTempMilliC") (natT maxTempMilliC)) := by
  simp [Obend.Core.Term.instantiate, andT, leNat, natT, falseT, Term.substitute]

/-- Core4 transition law that admits an OpenUSD `timeSamples` state update `(old, new, req)`
iff `new` satisfies `usdPartInvariantTerm minWallUm maxTempMilliC`. -/
def usdPartTransitionLaw (minWallUm maxTempMilliC : Nat) : Term :=
  law3 (guard (.app (usdPartInvariantTerm minWallUm maxTempMilliC) (.bound 1)) "usd_lifecycle_violation" okT)

/-- Proof-carrying `Obend.Law.CellContract` for an OpenUSD physical part across its `timeSamples` lifecycle. -/
def usdPartCellContract (minWallUm maxTempMilliC : Nat) : CellContract where
  law       := usdPartTransitionLaw minWallUm maxTempMilliC
  invariant := usdPartInvariantTerm minWallUm maxTempMilliC
  stepRel   := usdPartTransitionLaw minWallUm maxTempMilliC
  inductive_preserves := by
    intro old new req _ hAdm
    unfold usdPartTransitionLaw at hAdm
    obtain ⟨w, hw⟩ := (admits_iff _ old new req).1 hAdm
    simp only [Obend.Law.subst_guard, Obend.Law.subst_app, Obend.Law.subst_bound,
      Obend.Law.subst_okT, Obend.Law.lawEnv, Obend.Law.scons_succ, Obend.Law.scons_zero,
      subst_usdPartInvariantTerm] at hw
    exact (guard_ok hw).1
  step_sound := fun _ _ _ _ hAdm => hAdm

/-- Monotonicity of `Holds (usdPartInvariantTerm minWallUm maxTempMilliC)` under tightening of
minimum wall thickness (`minWallUm ≤ minWallUm'`) and lowering of maximum operating temperature
(`maxTempMilliC' ≤ maxTempMilliC`). -/
theorem usdPartInvariantTerm_monotone
    (minWallUm minWallUm' maxTempMilliC maxTempMilliC' : Nat)
    (hWall : minWallUm ≤ minWallUm')
    (hTemp : maxTempMilliC' ≤ maxTempMilliC)
    (d : Data)
    (hHold : Holds (usdPartInvariantTerm minWallUm' maxTempMilliC') d) :
    Holds (usdPartInvariantTerm minWallUm maxTempMilliC) d := by
  unfold Holds usdPartInvariantTerm at hHold ⊢
  have hStepBeta' :
      Steps
        (.app (.lam (andT (leNat (natT minWallUm') (.get (.bound 0) "wallThicknessUm"))
                          (leNat (.get (.bound 0) "peakTempMilliC") (natT maxTempMilliC')))) d.term)
        (andT (leNat (natT minWallUm') (.get d.term "wallThicknessUm"))
              (leNat (.get d.term "peakTempMilliC") (natT maxTempMilliC'))) := by
    rw [← instantiate_usdPartInvariantBody minWallUm' maxTempMilliC' d.term]
    exact .next (.beta _ d.term) (.refl _)
  have hBody' := evaluates_of_steps hStepBeta' hHold
  obtain ⟨hW', hT'⟩ := andT_true hBody'
  obtain ⟨m1, wVal, hm1, hwVal, hLeW'⟩ := leNat_true hW'
  have hm1Eq : m1 = minWallUm' := natT_eval hm1
  have hLeW : minWallUm ≤ wVal := by omega
  obtain ⟨tVal, k2, htVal, hk2, hLeT'⟩ := leNat_true hT'
  have hk2Eq : k2 = maxTempMilliC' := natT_eval hk2
  have hLeT : tVal ≤ maxTempMilliC := by omega
  have hW : Evaluates (leNat (natT minWallUm) (.get d.term "wallThicknessUm")) (.boolean true) := by
    refine evaluates_steps (steps_binaryRight_usd (.natural minWallUm) hwVal.1) ?_
    exact evaluates_step
      (.primitive .lessEqual (.nat minWallUm) (.nat wVal) (.boolean true)
        (.natural minWallUm) (.natural wVal) (by simp [Obend.Core.Term.primitiveResult, hLeW]))
      (evaluates_self (.boolean true))
  have hT : Evaluates (leNat (.get d.term "peakTempMilliC") (natT maxTempMilliC)) (.boolean true) := by
    refine evaluates_steps (steps_binaryLeft_usd htVal.1) ?_
    exact evaluates_step
      (.primitive .lessEqual (.nat tVal) (.nat maxTempMilliC) (.boolean true)
        (.natural tVal) (.natural maxTempMilliC) (by simp [Obend.Core.Term.primitiveResult, hLeT]))
      (evaluates_self (.boolean true))
  have hBody :
      Evaluates
        (andT (leNat (natT minWallUm) (.get d.term "wallThicknessUm"))
              (leNat (.get d.term "peakTempMilliC") (natT maxTempMilliC)))
        (.boolean true) :=
    evaluates_ifBool hW hT
  rw [← instantiate_usdPartInvariantBody minWallUm maxTempMilliC d.term] at hBody
  exact evaluates_step (.beta _ d.term) hBody

/-- **OpenUSD Forever-Crown Lifecycle Contract Refinement Theorem (`usd_lifecycle_contract_narrows_sound`)**:
Tightening a physical part's minimum wall thickness (`minWallUm ≤ minWallUm'`) and lowering its
maximum operating temperature (`maxTempMilliC' ≤ maxTempMilliC`):
1. Refines the Boolean part lifecycle invariant (`checkPartLifecycleInvariant`) and transition step
   checker (`checkUsdTransitionStep`),
2. Satisfies the `Obend.Law.Narrows` forever-crown preorder on the Core4 transition laws
   (`Narrows (usdPartTransitionLaw minWallUm' maxTempMilliC') (usdPartTransitionLaw minWallUm maxTempMilliC)`), and
3. Guarantees via `cellContract_relaw_sound` and `cellContract_trace_sound` that any multi-step
   OpenUSD `CellTrace` governed by the tightened contract preserves the original safety invariant. -/
theorem usd_lifecycle_contract_narrows_sound
    (minWallUm minWallUm' maxTempMilliC maxTempMilliC' : Nat)
    (hWall : minWallUm ≤ minWallUm')
    (hTemp : maxTempMilliC' ≤ maxTempMilliC) :
    (∀ st : UsdPhysicalState,
      checkPartLifecycleInvariant (Int.ofNat minWallUm') (Int.ofNat maxTempMilliC') st = true →
      checkPartLifecycleInvariant (Int.ofNat minWallUm) (Int.ofNat maxTempMilliC) st = true) ∧
    (∀ oldSt newSt : UsdPhysicalState,
      checkUsdTransitionStep (Int.ofNat minWallUm') (Int.ofNat maxTempMilliC') oldSt newSt = true →
      checkUsdTransitionStep (Int.ofNat minWallUm) (Int.ofNat maxTempMilliC) oldSt newSt = true) ∧
    Narrows (usdPartTransitionLaw minWallUm' maxTempMilliC') (usdPartTransitionLaw minWallUm maxTempMilliC) := by
  refine ⟨?_, ?_, ?_⟩
  · intro st hInv'
    have hW : Int.ofNat minWallUm ≤ Int.ofNat minWallUm' := Int.ofNat_le.mpr hWall
    have hT : Int.ofNat maxTempMilliC' ≤ Int.ofNat maxTempMilliC := Int.ofNat_le.mpr hTemp
    unfold checkPartLifecycleInvariant at hInv' ⊢
    rw [decide_eq_true_iff] at hInv' ⊢
    omega
  · intro oldSt newSt hStep'
    have hW : Int.ofNat minWallUm ≤ Int.ofNat minWallUm' := Int.ofNat_le.mpr hWall
    have hT : Int.ofNat maxTempMilliC' ≤ Int.ofNat maxTempMilliC := Int.ofNat_le.mpr hTemp
    unfold checkUsdTransitionStep checkPartLifecycleInvariant at hStep' ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hStep' ⊢
    omega
  · intro old new req hAdm
    unfold usdPartTransitionLaw at hAdm ⊢
    obtain ⟨w, hw⟩ := (admits_iff _ old new req).1 hAdm
    simp only [Obend.Law.subst_guard, Obend.Law.subst_app, Obend.Law.subst_bound,
      Obend.Law.subst_okT, Obend.Law.lawEnv, Obend.Law.scons_succ, Obend.Law.scons_zero,
      subst_usdPartInvariantTerm] at hw
    have hHold' : Holds (usdPartInvariantTerm minWallUm' maxTempMilliC') new := (guard_ok hw).1
    have hHold : Holds (usdPartInvariantTerm minWallUm maxTempMilliC) new :=
      usdPartInvariantTerm_monotone minWallUm minWallUm' maxTempMilliC maxTempMilliC' hWall hTemp new hHold'
    refine (admits_iff _ old new req).2 ⟨.record [], ?_⟩
    simp only [Obend.Law.subst_guard, Obend.Law.subst_app, Obend.Law.subst_bound,
      Obend.Law.subst_okT, Obend.Law.lawEnv, Obend.Law.scons_succ, Obend.Law.scons_zero,
      subst_usdPartInvariantTerm]
    exact evaluates_ifBool hHold (evaluates_self (.inject "ok" (.record [])))

/-! ## 4. Unified OpenUSD `SdfLayer` / `PrimSpec` / `PcpPrimIndex` $\to$ `Core4` `Term.mix` / `Term.fix` & `Obend.Leaf.flatten` -/

/-- The 7 composition arc kinds of Apple/Pixar OpenUSD (`LIVERPS` strength ordering,
from strongest `localArc` to weakest `specializesArc`)). Strength here is a rank on authored
opinions for one attribute, which is what value resolution sees; Pcp builds a graph of arcs
(a reference points at another layer stack, inherits at a class path), and that graph is not
modelled. -/
inductive UsdArcKind where
  | localArc
  | inheritsArc
  | variantArc
  | relocatesArc
  | referencesArc
  | payloadArc
  | specializesArc
  deriving DecidableEq, Repr

/-- Numerical strength rank for `LIVERPS` (`7` = strongest `localArc`, `1` = weakest `specializesArc`). -/
def UsdArcKind.strength : UsdArcKind → Nat
  | .localArc       => 7
  | .inheritsArc    => 6
  | .variantArc     => 5
  | .relocatesArc   => 4
  | .referencesArc  => 3
  | .payloadArc     => 2
  | .specializesArc => 1


/-- An OpenUSD `PrimSpec` authoring attribute/method opinions `fields` at hierarchical path `path`
through LIVERPS composition arc `arc : UsdArcKind`. -/
structure PrimSpec where
  path   : SdfPath
  arc    : UsdArcKind
  fields : List (String × Term)
  deriving Repr

/-- An OpenUSD `SdfLayer` document containing a sequence of authored `PrimSpec`s. -/
structure SdfLayer where
  layerId : String
  prims   : List PrimSpec
  deriving Repr

/-- Empty default `Obend.Logic.Layer` used when no `PrimSpec` matches a target `SdfPath`. -/
def emptyUsdLayer : Obend.Logic.Layer :=
  { name := "emptyUsdPrim"
  , metadata := .record []
  , fields := []
  , flat := false }

/-- Lower a single OpenUSD `PrimSpec` to a `Core4` `Obend.Logic.Layer` (`λself. λsuper. extend super {fields}`). -/
def PrimSpec.toLayer (ps : PrimSpec) : Obend.Logic.Layer :=
  { name := String.intercalate "/" ps.path
  , metadata := .record []
  , fields := ps.fields
  , flat := false }

/-- Insert a `PrimSpec` into a list ordered from strongest LIVERPS arc (`localArc = 7`) to weakest
(`specializesArc = 1`). When two specs have equal LIVERPS strength, the newly inserted spec
takes precedence at the head. -/
def insertPrimByStrength (p : PrimSpec) : List PrimSpec → List PrimSpec
  | [] => [p]
  | q :: rest =>
    if q.arc.strength ≤ p.arc.strength then
      p :: q :: rest
    else
      q :: insertPrimByStrength p rest

/-- Sort a list of `PrimSpec`s into canonical LIVERPS strength order (`L > I > V > E > R > P > S`). -/
def sortPrimsByLiverps : List PrimSpec → List PrimSpec
  | [] => []
  | p :: rest => insertPrimByStrength p (sortPrimsByLiverps rest)

/-- Gather all `PrimSpec`s across `layers : List SdfLayer` targeting `target : SdfPath`. -/
def collectTargetPrims (layers : List SdfLayer) (target : SdfPath) : List PrimSpec :=
  (layers.flatMap (fun l => l.prims)).filter (fun ps => ps.path == target)

/-- Build the OpenUSD `PcpPrimIndex` for `target : SdfPath` by collecting matching `PrimSpec`s across
`layers` and sorting them by LIVERPS `UsdArcKind.strength`. -/
def buildPcpPrimIndex (layers : List SdfLayer) (target : SdfPath) : List PrimSpec :=
  sortPrimsByLiverps (collectTargetPrims layers target)

/-- Lower a list of `PrimSpec`s and `seedFields` into a `Core4` `Obend.Logic.Composition` sorted by
LIVERPS `UsdArcKind.strength`. -/
def primSpecsToComposition
    (specs : List PrimSpec) (seedFields : List (String × Term)) : Obend.Logic.Composition :=
  match sortPrimsByLiverps specs with
  | [] => { top := emptyUsdLayer, below := [], seed := seedFields }
  | topSpec :: belowSpecs =>
    { top := topSpec.toLayer
    , below := belowSpecs.map PrimSpec.toLayer
    , seed := seedFields }

/-- Lower a list of `PrimSpec`s and a `seed : Term` into a `Core4` `Term.fix (Term.mix ...)` object
sorted by LIVERPS `UsdArcKind.strength`. -/
def composePrimSpecsToTerm (specs : List PrimSpec) (seed : Term) : Term :=
  match sortPrimsByLiverps specs with
  | [] => .fix emptyUsdLayer.term seed
  | topSpec :: belowSpecs =>
    .fix (Obend.Logic.composeTerm topSpec.toLayer (belowSpecs.map PrimSpec.toLayer)) seed

/-- **Unified OpenUSD `SdfLayer` $\to$ `Core4` `Term.mix` / `Term.fix` Lowering (`composePrimToTerm`)**:
Sorts all `PrimSpec`s matching `target : SdfPath` across `layers : List SdfLayer` by LIVERPS
`UsdArcKind.strength` and folds `Term.mix` across their `Layer.term`s, closing the open `self`/`super`
recursion with `Term.fix ... seed`. -/
def composePrimToTerm (layers : List SdfLayer) (target : SdfPath) (seed : Term) : Term :=
  composePrimSpecsToTerm (collectTargetPrims layers target) seed

/-- Bridge theorem: when `seed = .record seedFields`, `composePrimToTerm` is definitionally equal
to `(primSpecsToComposition (collectTargetPrims layers target) seedFields).object`. -/
theorem composePrimToTerm_eq_composition_object
    (layers : List SdfLayer) (target : SdfPath) (seedFields : List (String × Term)) :
    composePrimToTerm layers target (.record seedFields) =
      (primSpecsToComposition (collectTargetPrims layers target) seedFields).object := by
  unfold composePrimToTerm composePrimSpecsToTerm primSpecsToComposition Obend.Logic.Composition.object
  cases sortPrimsByLiverps (collectTargetPrims layers target) <;> rfl

/-- Every `UsdArcKind` has LIVERPS strength at most `UsdArcKind.localArc.strength` (`= 7`). -/
theorem usdArcKind_strength_le_local (a : UsdArcKind) :
    a.strength ≤ UsdArcKind.localArc.strength := by
  cases a <;> decide

/-- Inserting a `.localArc` `PrimSpec` into any `PrimSpec` list always places it at the head (`top`). -/
theorem insertPrimByStrength_localArc_head
    (p : PrimSpec) (rest : List PrimSpec) (hLocal : p.arc = .localArc) :
    insertPrimByStrength p rest = p :: rest := by
  cases rest with
  | nil => rfl
  | cons q tail =>
    unfold insertPrimByStrength
    rw [hLocal]
    have hLe : q.arc.strength ≤ UsdArcKind.localArc.strength := usdArcKind_strength_le_local q.arc
    rw [if_pos hLe]

/-- **Formal LIVERPS $\leftrightarrow$ `Core4` `Term.mix` & `Obend.Leaf.flatten` Dominance Theorem
(`liverps_local_dominates_term`)**:
For any scene path `target : SdfPath`, any property name `m : String`, any `.localArc` opinion
`vLocal : Term`, any weaker-or-equal arc `weakArc : UsdArcKind` with opinion `vWeak : Term`, and
any `seedFields : List (String × Term)`:
When a scene `layers` authors `{ path := target, arc := .localArc, fields := [(m, vLocal)] }`
and `{ path := target, arc := weakArc, fields := [(m, vWeak)] }`:
1. The lowered `Core4` object `composePrimToTerm layers target (.record seedFields)` reduces in
   multi-step `Core4` operational semantics (`Steps`) on field projection `.get ... m` to the
   local opinion `resolvedLocal` (via `Obend.Logic.late_binding`),
2. Is behaviorally equivalent (`≈b`, `Obend.Equiv.BEquiv`) to `resolvedLocal`, and
3. Whenever the composition is closed (`C.closedB = true`), compiling/flattening the OpenUSD
   composition via `Obend.Leaf.flatten` eliminates all `Term.mix`/`super` indirections while
   preserving behavioral equivalence `.get C.flatten m ≈b resolvedLocal`! -/
theorem liverps_local_dominates_term
    (target : SdfPath) (m : String) (vLocal vWeak : Term)
    (weakArc : UsdArcKind) (seedFields : List (String × Term)) :
    let localSpec : PrimSpec := { path := target, arc := .localArc, fields := [(m, vLocal)] }
    let weakSpec  : PrimSpec := { path := target, arc := weakArc,   fields := [(m, vWeak)] }
    let layers : List SdfLayer :=
      [ { layerId := "localLayer", prims := [localSpec] }
      , { layerId := "weakLayer",  prims := [weakSpec] } ]
    let C := primSpecsToComposition (collectTargetPrims layers target) seedFields
    let resolvedLocal := Obend.Logic.openTerm vLocal C.object (C.superAt 0)
    Steps (.get (composePrimToTerm layers target (.record seedFields)) m) resolvedLocal ∧
    (.get (composePrimToTerm layers target (.record seedFields)) m ≈b resolvedLocal) ∧
    (C.closedB = true → (.get C.flatten m ≈b resolvedLocal)) := by
  dsimp only
  let localSpec : PrimSpec := { path := target, arc := .localArc, fields := [(m, vLocal)] }
  let weakSpec  : PrimSpec := { path := target, arc := weakArc,   fields := [(m, vWeak)] }
  let layers : List SdfLayer :=
    [ { layerId := "localLayer", prims := [localSpec] }
    , { layerId := "weakLayer",  prims := [weakSpec] } ]
  have hCollect : collectTargetPrims layers target = [localSpec, weakSpec] := by
    simp [collectTargetPrims, layers, localSpec, weakSpec]
  have hSort : sortPrimsByLiverps [localSpec, weakSpec] = [localSpec, weakSpec] := by
    dsimp only [sortPrimsByLiverps]
    exact insertPrimByStrength_localArc_head localSpec [weakSpec] rfl
  let C := primSpecsToComposition (collectTargetPrims layers target) seedFields
  have hCEq : C = { top := localSpec.toLayer, below := [weakSpec.toLayer], seed := seedFields } := by
    dsimp only [C, primSpecsToComposition]
    rw [hCollect, hSort]
    rfl
  have hProv : Obend.Logic.providesLast C.layers m = some 0 := by
    rw [hCEq]
    simp [Obend.Logic.providesLast, Obend.Logic.Composition.layers, PrimSpec.toLayer, localSpec,
      Obend.Logic.Layer.provides]
  have hBody : Obend.Logic.bodyAt C.layers 0 m = some vLocal := by
    rw [hCEq]
    simp [Obend.Logic.bodyAt, Obend.Logic.Composition.layers, PrimSpec.toLayer, localSpec,
      Obend.Logic.Layer.body]
  rw [composePrimToTerm_eq_composition_object layers target seedFields]
  have hSteps : Steps (.get C.object m) (Obend.Logic.openTerm vLocal C.object (C.superAt 0)) :=
    Obend.Logic.late_binding C m 0 vLocal hProv hBody
  have hBeq : (.get C.object m ≈b Obend.Logic.openTerm vLocal C.object (C.superAt 0)) :=
    Obend.Logic.late_binding_bequiv C m 0 vLocal hProv hBody
  refine ⟨hSteps, hBeq, ?_⟩
  intro hClosed
  exact Obend.Equiv.BEquiv.trans (Obend.Leaf.flatten_sound C hClosed m) hBeq

/-- Concrete `Evaluates` corollary of `liverps_local_dominates_term`: even when a weaker
`referencesArc` layer is listed *before* the stronger `localArc` layer in `layers`, LIVERPS sorting
in `composePrimToTerm` places `localArc` at the top of the `Term.mix` stack and evaluates `.get ... m`
to the `localArc` natural number attribute `.nat nLocal`! -/
theorem liverps_local_overrides_preceding_reference_eval
    (target : SdfPath) (m : String) (nLocal nRef : Nat) :
    let refLayer   : SdfLayer := { layerId := "vendorRef.usd", prims := [{ path := target, arc := .referencesArc, fields := [(m, .nat nRef)] }] }
    let localLayer : SdfLayer := { layerId := "sessionLocal.usd", prims := [{ path := target, arc := .localArc, fields := [(m, .nat nLocal)] }] }
    let layers := [refLayer, localLayer]
    let C := primSpecsToComposition (collectTargetPrims layers target) []
    Evaluates (.get (composePrimToTerm layers target (.record [])) m) (.nat nLocal) ∧
    (C.closedB = true → (.get C.flatten m ≈b .nat nLocal)) := by
  dsimp only
  let refSpec   : PrimSpec := { path := target, arc := .referencesArc, fields := [(m, .nat nRef)] }
  let localSpec : PrimSpec := { path := target, arc := .localArc,      fields := [(m, .nat nLocal)] }
  let layers : List SdfLayer :=
    [ { layerId := "vendorRef.usd",    prims := [refSpec] }
    , { layerId := "sessionLocal.usd", prims := [localSpec] } ]
  have hCollect : collectTargetPrims layers target = [refSpec, localSpec] := by
    simp [collectTargetPrims, layers, refSpec, localSpec]
  have hSort : sortPrimsByLiverps [refSpec, localSpec] = [localSpec, refSpec] := by
    rfl
  let C := primSpecsToComposition (collectTargetPrims layers target) []
  have hCEq : C = { top := localSpec.toLayer, below := [refSpec.toLayer], seed := [] } := by
    dsimp only [C, primSpecsToComposition]
    rw [hCollect, hSort]
    rfl
  have hProv : Obend.Logic.providesLast C.layers m = some 0 := by
    rw [hCEq]
    simp [Obend.Logic.providesLast, Obend.Logic.Composition.layers, PrimSpec.toLayer, localSpec,
      Obend.Logic.Layer.provides]
  have hBody : Obend.Logic.bodyAt C.layers 0 m = some (.nat nLocal) := by
    rw [hCEq]
    simp [Obend.Logic.bodyAt, Obend.Logic.Composition.layers, PrimSpec.toLayer, localSpec,
      Obend.Logic.Layer.body]
  have hRes : Obend.Logic.openTerm (.nat nLocal) C.object (C.superAt 0) = .nat nLocal := by
    simp [Obend.Logic.openTerm, Term.substitute]
  rw [composePrimToTerm_eq_composition_object layers target []]
  have hSteps := Obend.Logic.late_binding C m 0 (.nat nLocal) hProv hBody
  rw [hRes] at hSteps
  have hEvalObj : Evaluates (.get C.object m) (.nat nLocal) :=
    evaluates_steps hSteps ⟨.refl _, .natural nLocal⟩
  refine ⟨hEvalObj, ?_⟩
  intro hClosed
  have hFlatSound := Obend.Leaf.flatten_sound C hClosed m
  have hBeq := Obend.Logic.late_binding_bequiv C m 0 (.nat nLocal) hProv hBody
  rw [hRes] at hBeq
  exact Obend.Equiv.BEquiv.trans hFlatSound hBeq

/-- **Universal Two-Arc LIVERPS Dominance in Both Layer Orders (`liverps_stronger_arc_dominates_term`)**:
For *any* pair of OpenUSD composition arcs `strongArc, weakArc : UsdArcKind` with
`weakArc.strength < strongArc.strength`, in *both* layer stack orders (`[strongLayer, weakLayer]` and
`[weakLayer, strongLayer]`), lowering to `Core4` via `composePrimToTerm` places `strongArc` at the top of
the `Term.mix` stack, steps `.get ... m` to `resolvedStrong`, and preserves `≈b resolvedStrong` under
`Obend.Leaf.flatten`. -/
theorem liverps_stronger_arc_dominates_term
    (target : SdfPath) (m : String) (vStrong vWeak : Term)
    (strongArc weakArc : UsdArcKind) (seedFields : List (String × Term))
    (hLt : weakArc.strength < strongArc.strength) :
    let strongSpec : PrimSpec := { path := target, arc := strongArc, fields := [(m, vStrong)] }
    let weakSpec   : PrimSpec := { path := target, arc := weakArc,   fields := [(m, vWeak)] }
    let strongLayer : SdfLayer := { layerId := "strongLayer", prims := [strongSpec] }
    let weakLayer   : SdfLayer := { layerId := "weakLayer",   prims := [weakSpec] }
    let layersFwd := [strongLayer, weakLayer]
    let layersRev := [weakLayer, strongLayer]
    let CFwd := primSpecsToComposition (collectTargetPrims layersFwd target) seedFields
    let CRev := primSpecsToComposition (collectTargetPrims layersRev target) seedFields
    let resolvedFwd := Obend.Logic.openTerm vStrong CFwd.object (CFwd.superAt 0)
    let resolvedRev := Obend.Logic.openTerm vStrong CRev.object (CRev.superAt 0)
    Steps (.get (composePrimToTerm layersFwd target (.record seedFields)) m) resolvedFwd ∧
    Steps (.get (composePrimToTerm layersRev target (.record seedFields)) m) resolvedRev ∧
    (CFwd.closedB = true → (.get CFwd.flatten m ≈b resolvedFwd)) ∧
    (CRev.closedB = true → (.get CRev.flatten m ≈b resolvedRev)) := by
  dsimp only
  let strongSpec : PrimSpec := { path := target, arc := strongArc, fields := [(m, vStrong)] }
  let weakSpec   : PrimSpec := { path := target, arc := weakArc,   fields := [(m, vWeak)] }
  let strongLayer : SdfLayer := { layerId := "strongLayer", prims := [strongSpec] }
  let weakLayer   : SdfLayer := { layerId := "weakLayer",   prims := [weakSpec] }
  let layersFwd := [strongLayer, weakLayer]
  let layersRev := [weakLayer, strongLayer]
  have hColFwd : collectTargetPrims layersFwd target = [strongSpec, weakSpec] := by
    simp [collectTargetPrims, layersFwd, strongLayer, weakLayer, strongSpec, weakSpec]
  have hColRev : collectTargetPrims layersRev target = [weakSpec, strongSpec] := by
    simp [collectTargetPrims, layersRev, strongLayer, weakLayer, strongSpec, weakSpec]
  have hLe : weakSpec.arc.strength ≤ strongSpec.arc.strength := Nat.le_of_lt hLt
  have hNotLe : ¬ (strongSpec.arc.strength ≤ weakSpec.arc.strength) := Nat.not_le_of_gt hLt
  have hSortFwd : sortPrimsByLiverps [strongSpec, weakSpec] = [strongSpec, weakSpec] := by
    dsimp only [sortPrimsByLiverps, insertPrimByStrength]
    rw [if_pos hLe]
  have hSortRev : sortPrimsByLiverps [weakSpec, strongSpec] = [strongSpec, weakSpec] := by
    dsimp only [sortPrimsByLiverps, insertPrimByStrength]
    rw [if_neg hNotLe]
  let CFwd := primSpecsToComposition (collectTargetPrims layersFwd target) seedFields
  let CRev := primSpecsToComposition (collectTargetPrims layersRev target) seedFields
  have hCFwdEq : CFwd = { top := strongSpec.toLayer, below := [weakSpec.toLayer], seed := seedFields } := by
    dsimp only [CFwd, primSpecsToComposition]
    rw [hColFwd, hSortFwd]
    rfl
  have hCRevEq : CRev = { top := strongSpec.toLayer, below := [weakSpec.toLayer], seed := seedFields } := by
    dsimp only [CRev, primSpecsToComposition]
    rw [hColRev, hSortRev]
    rfl
  have hProvFwd : Obend.Logic.providesLast CFwd.layers m = some 0 := by
    rw [hCFwdEq]
    simp [Obend.Logic.providesLast, Obend.Logic.Composition.layers, PrimSpec.toLayer, strongSpec,
      Obend.Logic.Layer.provides]
  have hBodyFwd : Obend.Logic.bodyAt CFwd.layers 0 m = some vStrong := by
    rw [hCFwdEq]
    simp [Obend.Logic.bodyAt, Obend.Logic.Composition.layers, PrimSpec.toLayer, strongSpec,
      Obend.Logic.Layer.body]
  have hProvRev : Obend.Logic.providesLast CRev.layers m = some 0 := by
    rw [hCRevEq]
    simp [Obend.Logic.providesLast, Obend.Logic.Composition.layers, PrimSpec.toLayer, strongSpec,
      Obend.Logic.Layer.provides]
  have hBodyRev : Obend.Logic.bodyAt CRev.layers 0 m = some vStrong := by
    rw [hCRevEq]
    simp [Obend.Logic.bodyAt, Obend.Logic.Composition.layers, PrimSpec.toLayer, strongSpec,
      Obend.Logic.Layer.body]
  rw [composePrimToTerm_eq_composition_object layersFwd target seedFields,
      composePrimToTerm_eq_composition_object layersRev target seedFields]
  refine ⟨Obend.Logic.late_binding CFwd m 0 vStrong hProvFwd hBodyFwd,
          Obend.Logic.late_binding CRev m 0 vStrong hProvRev hBodyRev, ?_, ?_⟩
  · intro hClosed
    exact Obend.Equiv.BEquiv.trans (Obend.Leaf.flatten_sound CFwd hClosed m)
      (Obend.Logic.late_binding_bequiv CFwd m 0 vStrong hProvFwd hBodyFwd)
  · intro hClosed
    exact Obend.Equiv.BEquiv.trans (Obend.Leaf.flatten_sound CRev hClosed m)
      (Obend.Logic.late_binding_bequiv CRev m 0 vStrong hProvRev hBodyRev)

/-- **Same-Arc Sublayer Tie-Breaking Theorem (`liverps_sublayer_tiebreak_dominates_term`)**:
When two sublayers `subLayer0` and `subLayer1` in `layers = [subLayer0, subLayer1]` author opinions
`v0` and `v1` for the same property `m` under the *same* `UsdArcKind` (`arc`), stable LIVERPS
sorting preserves sublayer order so `subLayer0` dominates `subLayer1` in `Core4` `Steps`, `BEquiv`,
and `Obend.Leaf.flatten`. -/
theorem liverps_sublayer_tiebreak_dominates_term
    (target : SdfPath) (m : String) (v0 v1 : Term)
    (arc : UsdArcKind) (seedFields : List (String × Term)) :
    let spec0 : PrimSpec := { path := target, arc := arc, fields := [(m, v0)] }
    let spec1 : PrimSpec := { path := target, arc := arc, fields := [(m, v1)] }
    let layers : List SdfLayer :=
      [ { layerId := "subLayer0", prims := [spec0] }
      , { layerId := "subLayer1", prims := [spec1] } ]
    let C := primSpecsToComposition (collectTargetPrims layers target) seedFields
    let resolved0 := Obend.Logic.openTerm v0 C.object (C.superAt 0)
    Steps (.get (composePrimToTerm layers target (.record seedFields)) m) resolved0 ∧
    (.get (composePrimToTerm layers target (.record seedFields)) m ≈b resolved0) ∧
    (C.closedB = true → (.get C.flatten m ≈b resolved0)) := by
  dsimp only
  let spec0 : PrimSpec := { path := target, arc := arc, fields := [(m, v0)] }
  let spec1 : PrimSpec := { path := target, arc := arc, fields := [(m, v1)] }
  let layers : List SdfLayer :=
    [ { layerId := "subLayer0", prims := [spec0] }
    , { layerId := "subLayer1", prims := [spec1] } ]
  have hCol : collectTargetPrims layers target = [spec0, spec1] := by
    simp [collectTargetPrims, layers, spec0, spec1]
  have hLe : spec1.arc.strength ≤ spec0.arc.strength := Nat.le_refl _
  have hSort : sortPrimsByLiverps [spec0, spec1] = [spec0, spec1] := by
    dsimp only [sortPrimsByLiverps, insertPrimByStrength]
    rw [if_pos hLe]
  let C := primSpecsToComposition (collectTargetPrims layers target) seedFields
  have hCEq : C = { top := spec0.toLayer, below := [spec1.toLayer], seed := seedFields } := by
    dsimp only [C, primSpecsToComposition]
    rw [hCol, hSort]
    rfl
  have hProv : Obend.Logic.providesLast C.layers m = some 0 := by
    rw [hCEq]
    simp [Obend.Logic.providesLast, Obend.Logic.Composition.layers, PrimSpec.toLayer, spec0,
      Obend.Logic.Layer.provides]
  have hBody : Obend.Logic.bodyAt C.layers 0 m = some v0 := by
    rw [hCEq]
    simp [Obend.Logic.bodyAt, Obend.Logic.Composition.layers, PrimSpec.toLayer, spec0,
      Obend.Logic.Layer.body]
  rw [composePrimToTerm_eq_composition_object layers target seedFields]
  refine ⟨Obend.Logic.late_binding C m 0 v0 hProv hBody,
          Obend.Logic.late_binding_bequiv C m 0 v0 hProv hBody, ?_⟩
  intro hClosed
  exact Obend.Equiv.BEquiv.trans (Obend.Leaf.flatten_sound C hClosed m)
    (Obend.Logic.late_binding_bequiv C m 0 v0 hProv hBody)

/-! ## 5. 3D $SE(3)$ / Affine `XformOp3D` Transform Stack Over `FRepExpr` & `AffineForm3D` -/

/-- Elementary 3D OpenUSD `xformOp` spatial transformations:
- `translate dx dy dz`: translates the local frame by `(dx, dy, dz)` (pullback maps `(x, y, z) ↦ (x - dx, y - dy, z - dz)`)
- `rot90Z`: $90^\circ$ rotation about $+Z$ (pullback maps `(x, y, z) ↦ (y, -x, z)`)
- `rot90X`: $90^\circ$ rotation about $+X$ (pullback maps `(x, y, z) ↦ (x, z, -y)`)
- `rot90Y`: $90^\circ$ rotation about $+Y$ (pullback maps `(x, y, z) ↦ (-z, y, x)`)
- `scaleIso k`: uniform coordinate scaling `(x, y, z) ↦ (k * x, k * y, k * z)` -/
inductive XformOp3D where
  | translate (dx dy dz : Int)
  | rot90Z
  | rot90X
  | rot90Y
  | scalePos (k : Nat)
  deriving DecidableEq, Repr

/-- Apply a single `XformOp3D` pullback to a 3D point `(x, y, z)`. -/
def applyXformOpPoint (op : XformOp3D) (pt : Int × Int × Int) : Int × Int × Int :=
  let (x, y, z) := pt
  match op with
  | .translate dx dy dz => (x - dx, y - dy, z - dz)
  | .rot90Z             => (y, -x, z)
  | .rot90X             => (x, z, -y)
  | .rot90Y             => (-z, y, x)
  | .scalePos k         => (Int.ofNat k * x, Int.ofNat k * y, Int.ofNat k * z)

/-- Apply a sequence of OpenUSD `xformOpOrder` transforms `ops : List XformOp3D` to a 3D point `pt`. -/
def applyXformStackPoint (ops : List XformOp3D) (pt : Int × Int × Int) : Int × Int × Int :=
  ops.foldl (fun acc op => applyXformOpPoint op acc) pt

/-- Apply a single `XformOp3D` pullback to a triple of 3D Affine Arithmetic forms `(ax, ay, az)`. -/
def applyXformOpAffine3D
    (op : XformOp3D) (ax ay az : AffineForm3D) : AffineForm3D × AffineForm3D × AffineForm3D :=
  match op with
  | .translate dx dy dz =>
    ( AffineForm3D.sub ax (AffineForm3D.const dx)
    , AffineForm3D.sub ay (AffineForm3D.const dy)
    , AffineForm3D.sub az (AffineForm3D.const dz) )
  | .rot90Z =>
    ( ay, ax.neg, az )
  | .rot90X =>
    ( ax, az, ay.neg )
  | .rot90Y =>
    ( az.neg, ay, ax )
  | .scalePos k =>
    ( ax.scalePos k, ay.scalePos k, az.scalePos k )

/-- Apply an OpenUSD `xformOpOrder` stack `ops : List XformOp3D` to 3D Affine Arithmetic forms `(ax, ay, az)`. -/
def applyXformStackAffine3D
    (ops : List XformOp3D) (ax ay az : AffineForm3D) : AffineForm3D × AffineForm3D × AffineForm3D :=
  ops.foldl (fun (x, y, z) op => applyXformOpAffine3D op x y z) (ax, ay, az)

/-- Evaluate a 3D `FRepExpr` solid `e` under an OpenUSD `XformOp3D` transform stack `ops` at `(x, y, z)`. -/
def evalFRepPointXform (ops : List XformOp3D) (x y z : Int) (e : FRepExpr) : Int :=
  let (x', y', z') := applyXformStackPoint ops (x, y, z)
  evalFRepPoint x' y' z' e

/-- Evaluate a 3D `FRepExpr` solid `e` in 3D Affine Arithmetic under an OpenUSD `XformOp3D` stack `ops`. -/
def evalFRepAffine3DXform
    (ops : List XformOp3D) (ax ay az : AffineForm3D) (e : FRepExpr) : AffineForm3D :=
  let (ax', ay', az') := applyXformStackAffine3D ops ax ay az
  evalFRepAffine3D ax' ay' az' e

/-- **Exact Translation Inverse Identity (`xform_translate_inverse_exact`)**:
Applying `.translate dx dy dz` followed by `.translate (-dx) (-dy) (-dz)` restores any 3D point `(x, y, z)`. -/
theorem xform_translate_inverse_exact (dx dy dz x y z : Int) :
    applyXformStackPoint [.translate dx dy dz, .translate (-dx) (-dy) (-dz)] (x, y, z) = (x, y, z) := by
  dsimp only [applyXformStackPoint, List.foldl, applyXformOpPoint]
  have hx : x - dx - -dx = x := by omega
  have hy : y - dy - -dy = y := by omega
  have hz : z - dz - -dz = z := by omega
  rw [hx, hy, hz]

/-- **Exact Four-Fold $90^\circ$ Rotation Identity (`xform_rot90Z_fourfold_identity`)**:
Four successive $90^\circ$ rotations about $+Z$ (`[.rot90Z, .rot90Z, .rot90Z, .rot90Z]`) form the
exact identity on $\mathbb{Z}^3$. -/
theorem xform_rot90Z_fourfold_identity (x y z : Int) :
    applyXformStackPoint [.rot90Z, .rot90Z, .rot90Z, .rot90Z] (x, y, z) = (x, y, z) := by
  dsimp only [applyXformStackPoint, List.foldl, applyXformOpPoint]
  have hx : - -x = x := by omega
  have hy : - -y = y := by omega
  rw [hx, hy]

/-- Lemma: a single `applyXformOpAffine3D` preserves `enclosesAt`. -/
theorem applyXformOpAffine3D_enclosesAt
    (op : XformOp3D) (ax ay az : AffineForm3D) (x y z ex ey ez : Int)
    (hx : ax.enclosesAt ex ey ez x)
    (hy : ay.enclosesAt ex ey ez y)
    (hz : az.enclosesAt ex ey ez z) :
    let (ax', ay', az') := applyXformOpAffine3D op ax ay az
    let (x', y', z') := applyXformOpPoint op (x, y, z)
    ax'.enclosesAt ex ey ez x' ∧
    ay'.enclosesAt ex ey ez y' ∧
    az'.enclosesAt ex ey ez z' := by
  cases op with
  | translate dx dy dz =>
    dsimp only [applyXformOpAffine3D, applyXformOpPoint]
    refine ⟨?_, ?_, ?_⟩
    · exact affine3d_sub_enclosesAt ax (AffineForm3D.const dx) ex ey ez x dx hx
        (affine3d_const_enclosesAt dx ex ey ez)
    · exact affine3d_sub_enclosesAt ay (AffineForm3D.const dy) ex ey ez y dy hy
        (affine3d_const_enclosesAt dy ex ey ez)
    · exact affine3d_sub_enclosesAt az (AffineForm3D.const dz) ex ey ez z dz hz
        (affine3d_const_enclosesAt dz ex ey ez)
  | rot90Z =>
    dsimp only [applyXformOpAffine3D, applyXformOpPoint]
    exact ⟨hy, affine3d_neg_enclosesAt ax ex ey ez x hx, hz⟩
  | rot90X =>
    dsimp only [applyXformOpAffine3D, applyXformOpPoint]
    exact ⟨hx, hz, affine3d_neg_enclosesAt ay ex ey ez y hy⟩
  | rot90Y =>
    dsimp only [applyXformOpAffine3D, applyXformOpPoint]
    exact ⟨affine3d_neg_enclosesAt az ex ey ez z hz, hy, hx⟩
  | scalePos k =>
    dsimp only [applyXformOpAffine3D, applyXformOpPoint]
    exact ⟨ affine3d_scalePos_enclosesAt k ax ex ey ez x hx
          , affine3d_scalePos_enclosesAt k ay ex ey ez y hy
          , affine3d_scalePos_enclosesAt k az ex ey ez z hz ⟩

/-- Lemma: folding `applyXformStackAffine3D` preserves `enclosesAt` across any `ops : List XformOp3D`. -/
theorem applyXformStackAffine3D_enclosesAt
    (ops : List XformOp3D) (ax ay az : AffineForm3D) (x y z ex ey ez : Int)
    (hx : ax.enclosesAt ex ey ez x)
    (hy : ay.enclosesAt ex ey ez y)
    (hz : az.enclosesAt ex ey ez z) :
    let (ax', ay', az') := applyXformStackAffine3D ops ax ay az
    let (x', y', z') := applyXformStackPoint ops (x, y, z)
    ax'.enclosesAt ex ey ez x' ∧
    ay'.enclosesAt ex ey ez y' ∧
    az'.enclosesAt ex ey ez z' := by
  induction ops generalizing ax ay az x y z with
  | nil => exact ⟨hx, hy, hz⟩
  | cons op rest ih =>
    dsimp only [applyXformStackAffine3D, applyXformStackPoint, List.foldl]
    have hStep := applyXformOpAffine3D_enclosesAt op ax ay az x y z ex ey ez hx hy hz
    rcases hStep with ⟨hx', hy', hz'⟩
    exact ih (applyXformOpAffine3D op ax ay az).1
             (applyXformOpAffine3D op ax ay az).2.1
             (applyXformOpAffine3D op ax ay az).2.2
             (applyXformOpPoint op (x, y, z)).1
             (applyXformOpPoint op (x, y, z)).2.1
             (applyXformOpPoint op (x, y, z)).2.2
             hx' hy' hz'

/-- **3D `XformOp3D` Stack Affine Arithmetic Soundness (`evalFRepAffine3DXform_enclosesAt`)**:
For every transform stack `ops : List XformOp3D`, every 3D `FRepExpr` `e`, and every noise
realization `(ex, ey, ez) ∈ [-1, 1]^3`, the interval `.toInterval` of `evalFRepAffine3DXform ops ax ay az e`
conservatively encloses the transformed point evaluation `evalFRepPointXform ops x y z e`! -/
theorem evalFRepAffine3DXform_enclosesAt
    (ops : List XformOp3D) (ax ay az : AffineForm3D) (x y z ex ey ez : Int)
    (hEx : -1 ≤ ex ∧ ex ≤ 1) (hEy : -1 ≤ ey ∧ ey ≤ 1) (hEz : -1 ≤ ez ∧ ez ≤ 1)
    (hx : ax.enclosesAt ex ey ez x)
    (hy : ay.enclosesAt ex ey ez y)
    (hz : az.enclosesAt ex ey ez z)
    (e : FRepExpr) :
    (evalFRepAffine3DXform ops ax ay az e).toInterval.contains
      (evalFRepPointXform ops x y z e) := by
  unfold evalFRepAffine3DXform evalFRepPointXform
  have hStack := applyXformStackAffine3D_enclosesAt ops ax ay az x y z ex ey ez hx hy hz
  rcases hStack with ⟨hx', hy', hz'⟩
  have hFRep := evalFRepAffine3D_enclosesAt
    (applyXformStackAffine3D ops ax ay az).1
    (applyXformStackAffine3D ops ax ay az).2.1
    (applyXformStackAffine3D ops ax ay az).2.2
    ex ey ez
    (applyXformStackPoint ops (x, y, z)).1
    (applyXformStackPoint ops (x, y, z)).2.1
    (applyXformStackPoint ops (x, y, z)).2.2
    e hEx hEy hEz hx' hy' hz'
  exact affine3d_enclosesAt_to_interval _ ex ey ez _ hEx hEy hEz hFRep

/-! ## 6. Wall thickness is `Obend.Hardware.GeometryCAM.checkWall_sound`

Three probe-point wall-thickness functions stood here until 2026-11-04 (`computeShellWallThicknessUm`
with a caller's Lipschitz bound, its affine variant, and `computeCertifiedShellWallThicknessUm`),
each bounding the distance from one chosen point to the outer surface. A wall is a property of the
whole cavity, so the certificate is now a k-d region check in `GeometryCAM` (`wallLeaf`,
`checkWall_sound`): every lattice point within `t` of any cavity point of the box is material. -/

end Obend.Hardware.OpenUSD
end
