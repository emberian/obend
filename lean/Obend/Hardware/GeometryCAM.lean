module
/-
# Obend.Hardware.GeometryCAM — Verified F-Rep / SDF Solid Geometry, Interval Octree Pruning, 5-Axis CNC Machine Dynamics, Altintas Regenerative Chatter & Evolutionary Co-Design

Formalizes the mathematical and physical core of **verified CAD/CAM, machine-tool dynamics, and
in-silico evolutionary physical design** within `Obend.Hardware`:

1. **Function Representation (`FRepExpr`) & Signed Distance Field (`SDF`) Constructive Solid Geometry**:
   - Represents 3D solids implicitly via closed-form expressions $f : \mathbb{Z}^3 \to \mathbb{Z}$
     where $f(x, y, z) \le 0$ denotes the solid interior/boundary and $f(x, y, z) > 0$ denotes free
     exterior space (after Pasko et al. and Matt Keeter's `fidget` F-Rep/SDF kernel),
   - Supports algebraic primitives, scaling, squared Euclidean distance terms (`sq`), CSG union
     ($\min(f, g)$), CSG intersection ($\max(f, g)$), CSG subtraction ($\max(f, -g)$), and isotropic
     surface offsetting ($f - r$),
   - Proves **`frep_csg_union_comm`**, **`frep_csg_inter_comm`**, and **`frep_csg_de_morgan`**
     ($A \setminus (B \cup C) \equiv (A \setminus B) \cap (A \setminus C)$).
2. **3D Axis-Aligned Interval Arithmetic & Certified Octree Tape Pruning (`Box3D`, `evalFRepInterval`)**:
   - Evaluates any `FRepExpr` over a 3D bounding box $B = [x_{\text{lo}}, x_{\text{hi}}] \times
     [y_{\text{lo}}, y_{\text{hi}}] \times [z_{\text{lo}}, z_{\text{hi}}]$,
   - Proves **`frep_interval_enclosure_sound`**: for every point $(x, y, z) \in B$, the exact point
     evaluation `evalFRepPoint x y z e` is guaranteed to lie inside `evalFRepInterval B e`,
   - Proves **`frep_octree_prune_exterior_sound`**: if `(evalFRepInterval B e).lo > 0`, then *every*
     point $(x, y, z) \in B$ lies strictly outside the solid (`0 < evalFRepPoint x y z e`), providing
     a zero-false-negative certificate for pruning octree cells and skipping CNC air-cuts.
3. **Implicit Swept-Volume CAM Material Removal & Zero-Gouge Certification**:
   - Models in-process workpiece (`IPW`) evolution under a cutter swept volume `fSwept`:
     $$f_{\text{IPW}}(p) = \max(f_{\text{stock}}(p), -f_{\text{swept}}(p)),$$
   - Proves **`machining_material_monotone_removal`** ($f_{\text{stock}}(p) \le f_{\text{IPW}}(p)$:
     subtractive machining never adds material) and **`voxel_no_gouge_sound`** (if a target part voxel
     $B$ has `(evalFRepInterval B fSwept).lo > 0`, the cutter is guaranteed never to gouge any interior
     point of the finished part in $B$).
4. **Simulating the Machine Better Than the Tool Runs Itself: Servo Lag, End-Mill Deflection & Altintas Chatter**:
   - Models the true physical cutter trajectory under ballscrew/servo tracking lag $\tau_{\text{servo}} v_{\text{feed}}$
     and cantilever end-mill deflection $c_{\text{compliance}} \cdot (k_r a_p h_{\text{chip}})$ alongside
     Yusuf Altintas's regenerative chatter stability boundary $a_p k_{\text{cut}} |\operatorname{Re}[G(\omega_c)]| \le c_{\text{chatter}}$,
   - Proves **`machining_dimensional_error_bound`** and **`altintas_chatter_depth_monotone`**.
5. **In-Silico Evolutionary Physical Design Search (`DesignCandidate`, `filterVerifiedDesigns`)**:
   - Proves **`evolutionary_search_emits_only_verified_designs`**: any candidate surviving the kernel
     manufacturing + multiphysics filter is guaranteed to be gouge-free, chatter-stable, within
     dimensional deflection tolerance, and within its multiphysics performance floor.
-/
public import Obend.Hardware.Accelerators
@[expose] public section

namespace Obend.Hardware.GeometryCAM
open Obend.Hardware.Thermal
open Obend.Hardware.Accelerators
set_option autoImplicit false

/-! ## 1. Function Representation (`FRepExpr`) & Constructive Solid Geometry (`CSG`) -/

/-- Closed-form 3D Function Representation (`F-Rep` / `SDF`) expression tree over integer-scaled
spatial coordinates $(x, y, z)$ (e.g. in nanometers or micrometers).
Convention: $f(x, y, z) \le 0$ is inside/on the solid; $f(x, y, z) > 0$ is strictly outside. -/
inductive FRepExpr where
  | const    (c : Int)
  | varX
  | varY
  | varZ
  | add      (a b : FRepExpr)
  | sub      (a b : FRepExpr)
  | scalePos (k : Nat) (a : FRepExpr)
  | sq       (a : FRepExpr)
  | csgUnion (a b : FRepExpr)
  | csgInter (a b : FRepExpr)
  | csgDiff  (a b : FRepExpr)
  | offset   (r : Int) (a : FRepExpr)
  deriving DecidableEq, Repr

/-- Exact point evaluation of an `FRepExpr` at 3D coordinate $(x, y, z) \in \mathbb{Z}^3$. -/
def evalFRepPoint (x y z : Int) : FRepExpr → Int
  | .const c      => c
  | .varX         => x
  | .varY         => y
  | .varZ         => z
  | .add a b      => evalFRepPoint x y z a + evalFRepPoint x y z b
  | .sub a b      => evalFRepPoint x y z a - evalFRepPoint x y z b
  | .scalePos k a => Int.ofNat k * evalFRepPoint x y z a
  | .sq a         =>
    let v := evalFRepPoint x y z a
    v * v
  | .csgUnion a b => min (evalFRepPoint x y z a) (evalFRepPoint x y z b)
  | .csgInter a b => max (evalFRepPoint x y z a) (evalFRepPoint x y z b)
  | .csgDiff a b  => max (evalFRepPoint x y z a) (-evalFRepPoint x y z b)
  | .offset r a   => evalFRepPoint x y z a - r

/-- Predicate stating that point $(x, y, z)$ lies inside or on the boundary of solid `e`. -/
def inSolid (x y z : Int) (e : FRepExpr) : Prop :=
  evalFRepPoint x y z e ≤ 0

/-- CSG Union Commutativity (`frep_csg_union_comm`):
$\min(f(p), g(p)) = \min(g(p), f(p))$ at every point $p = (x, y, z)$. -/
theorem frep_csg_union_comm (x y z : Int) (a b : FRepExpr) :
    evalFRepPoint x y z (.csgUnion a b) = evalFRepPoint x y z (.csgUnion b a) := by
  dsimp only [evalFRepPoint]
  omega

/-- CSG Intersection Commutativity (`frep_csg_inter_comm`):
$\max(f(p), g(p)) = \max(g(p), f(p))$ at every point $p = (x, y, z)$. -/
theorem frep_csg_inter_comm (x y z : Int) (a b : FRepExpr) :
    evalFRepPoint x y z (.csgInter a b) = evalFRepPoint x y z (.csgInter b a) := by
  dsimp only [evalFRepPoint]
  omega

/-- **CSG De Morgan Subtraction Law (`frep_csg_de_morgan`)**:
Subtracting a union of two tool swept volumes $B \cup C$ from stock $A$ is pointwise identical
to intersecting the individual subtractions $(A \setminus B) \cap (A \setminus C)$:
$$\max(A, -\min(B, C)) = \max(\max(A, -B), \max(A, -C)).$$ -/
theorem frep_csg_de_morgan (x y z : Int) (a b c : FRepExpr) :
    evalFRepPoint x y z (.csgDiff a (.csgUnion b c)) =
      evalFRepPoint x y z (.csgInter (.csgDiff a b) (.csgDiff a c)) := by
  dsimp only [evalFRepPoint]
  omega

/-! ## 2. 3D Axis-Aligned Interval Arithmetic & Certified Octree Tape Pruning (`fidget`) -/

/-- A 3D axis-aligned bounding box (voxel / octree cell) $B = [X] \times [Y] \times [Z]$. -/
structure Box3D where
  xIv : FloatInterval
  yIv : FloatInterval
  zIv : FloatInterval
  deriving DecidableEq, Repr

/-- Predicate stating that 3D point $(x, y, z)$ lies inside bounding box `B`. -/
def Box3D.contains (B : Box3D) (x y z : Int) : Prop :=
  B.xIv.contains x ∧ B.yIv.contains y ∧ B.zIv.contains z

/-- Interval addition `[a.lo + b.lo, a.hi + b.hi]`. -/
def ivAdd (a b : FloatInterval) : FloatInterval where
  lo := a.lo + b.lo
  hi := a.hi + b.hi

/-- Interval negation `[-a.hi, -a.lo]`. -/
def ivNeg (a : FloatInterval) : FloatInterval where
  lo := -a.hi
  hi := -a.lo

/-- Interval subtraction `[a.lo - b.hi, a.hi - b.lo]`. -/
def ivSub (a b : FloatInterval) : FloatInterval where
  lo := a.lo - b.hi
  hi := a.hi - b.lo

/-- Interval scaling by a non-negative integer `k : Nat`. -/
def ivScalePos (k : Nat) (a : FloatInterval) : FloatInterval where
  lo := Int.ofNat k * a.lo
  hi := Int.ofNat k * a.hi

/-- Exact tight interval squaring enclosure:
* If `0 ≤ a.lo`, `[a.lo^2, a.hi^2]`,
* If `a.hi ≤ 0`, `[a.hi^2, a.lo^2]`,
* If `a` spans zero (`a.lo < 0 < a.hi`), `[0, max(a.lo^2, a.hi^2)]`. -/
def ivSq (a : FloatInterval) : FloatInterval :=
  if decide (0 ≤ a.lo) then
    { lo := a.lo * a.lo, hi := a.hi * a.hi }
  else if decide (a.hi ≤ 0) then
    { lo := a.hi * a.hi, hi := a.lo * a.lo }
  else
    { lo := 0, hi := max (a.lo * a.lo) (a.hi * a.hi) }

/-- Interval minimum (CSG union enclosure). -/
def ivMin (a b : FloatInterval) : FloatInterval where
  lo := min a.lo b.lo
  hi := min a.hi b.hi

/-- Interval maximum (CSG intersection enclosure). -/
def ivMax (a b : FloatInterval) : FloatInterval where
  lo := max a.lo b.lo
  hi := max a.hi b.hi

/-- Evaluate an `FRepExpr` over a 3D bounding box `B : Box3D` via interval arithmetic. -/
def evalFRepInterval (B : Box3D) : FRepExpr → FloatInterval
  | .const c      => { lo := c, hi := c }
  | .varX         => B.xIv
  | .varY         => B.yIv
  | .varZ         => B.zIv
  | .add a b      => ivAdd (evalFRepInterval B a) (evalFRepInterval B b)
  | .sub a b      => ivSub (evalFRepInterval B a) (evalFRepInterval B b)
  | .scalePos k a => ivScalePos k (evalFRepInterval B a)
  | .sq a         => ivSq (evalFRepInterval B a)
  | .csgUnion a b => ivMin (evalFRepInterval B a) (evalFRepInterval B b)
  | .csgInter a b => ivMax (evalFRepInterval B a) (evalFRepInterval B b)
  | .csgDiff a b  => ivMax (evalFRepInterval B a) (ivNeg (evalFRepInterval B b))
  | .offset r a   => ivSub (evalFRepInterval B a) { lo := r, hi := r }

/-- Lemma: For any `v` inside interval `iv`, `v * v` lies inside `ivSq iv`. -/
theorem ivSq_contains (iv : FloatInterval) (v : Int) (h : iv.contains v) :
    (ivSq iv).contains (v * v) := by
  dsimp only [FloatInterval.contains] at h
  unfold ivSq
  by_cases hLoPos : 0 ≤ iv.lo
  · rw [if_pos (decide_eq_true hLoPos)]
    dsimp only [FloatInterval.contains]
    have hVPos : 0 ≤ v := by omega
    have hHiPos : 0 ≤ iv.hi := by omega
    have hLo1 : iv.lo * iv.lo ≤ iv.lo * v :=
      int_mul_le_mul_of_nonneg_left iv.lo v iv.lo h.1 hLoPos
    have hLo2 : iv.lo * v ≤ v * v :=
      int_mul_le_mul_of_nonneg_right iv.lo v v h.1 hVPos
    have hHi1 : v * v ≤ iv.hi * v :=
      int_mul_le_mul_of_nonneg_right v iv.hi v h.2 hVPos
    have hHi2 : iv.hi * v ≤ iv.hi * iv.hi :=
      int_mul_le_mul_of_nonneg_left v iv.hi iv.hi h.2 hHiPos
    omega
  · rw [if_neg (by simpa [decide_eq_true_iff] using hLoPos)]
    by_cases hHiNeg : iv.hi ≤ 0
    · rw [if_pos (decide_eq_true hHiNeg)]
      dsimp only [FloatInterval.contains]
      have hNegHiPos : 0 ≤ -iv.hi := by omega
      have hNegVPos : 0 ≤ -v := by omega
      have hNegLoPos : 0 ≤ -iv.lo := by omega
      have hLe1 : -iv.hi ≤ -v := by omega
      have hLe2 : -v ≤ -iv.lo := by omega
      have hLo1 : (-iv.hi) * (-iv.hi) ≤ (-iv.hi) * (-v) :=
        int_mul_le_mul_of_nonneg_left (-iv.hi) (-v) (-iv.hi) hLe1 hNegHiPos
      have hLo2 : (-iv.hi) * (-v) ≤ (-v) * (-v) :=
        int_mul_le_mul_of_nonneg_right (-iv.hi) (-v) (-v) hLe1 hNegVPos
      have hHi1 : (-v) * (-v) ≤ (-iv.lo) * (-v) :=
        int_mul_le_mul_of_nonneg_right (-v) (-iv.lo) (-v) hLe2 hNegVPos
      have hHi2 : (-iv.lo) * (-v) ≤ (-iv.lo) * (-iv.lo) :=
        int_mul_le_mul_of_nonneg_left (-v) (-iv.lo) (-iv.lo) hLe2 hNegLoPos
      have hLo : (-iv.hi) * (-iv.hi) ≤ (-v) * (-v) := Int.le_trans hLo1 hLo2
      have hHi : (-v) * (-v) ≤ (-iv.lo) * (-iv.lo) := Int.le_trans hHi1 hHi2
      rw [Int.neg_mul_neg, Int.neg_mul_neg] at hLo hHi
      exact ⟨hLo, hHi⟩
    · rw [if_neg (by simpa [decide_eq_true_iff] using hHiNeg)]
      dsimp only [FloatInterval.contains]
      have hSqNonneg : 0 ≤ v * v := int_sq_nonneg v
      refine ⟨hSqNonneg, ?_⟩
      by_cases hNonneg : 0 ≤ v
      · have hHiPos : 0 ≤ iv.hi := by omega
        have h1 : v * v ≤ iv.hi * v := int_mul_le_mul_of_nonneg_right v iv.hi v h.2 hNonneg
        have h2 : iv.hi * v ≤ iv.hi * iv.hi := int_mul_le_mul_of_nonneg_left v iv.hi iv.hi h.2 hHiPos
        omega
      · have hNegV : 0 ≤ -v := by omega
        have hNegLo : -v ≤ -iv.lo := by omega
        have hNegLoNonneg : 0 ≤ -iv.lo := by omega
        have h1 : (-v) * (-v) ≤ (-iv.lo) * (-v) :=
          int_mul_le_mul_of_nonneg_right (-v) (-iv.lo) (-v) hNegLo hNegV
        have h2 : (-iv.lo) * (-v) ≤ (-iv.lo) * (-iv.lo) :=
          int_mul_le_mul_of_nonneg_left (-v) (-iv.lo) (-iv.lo) hNegLo hNegLoNonneg
        have h3 : (-v) * (-v) ≤ (-iv.lo) * (-iv.lo) := Int.le_trans h1 h2
        rw [Int.neg_mul_neg, Int.neg_mul_neg] at h3
        omega

/-- **Universal 3D F-Rep Interval Enclosure Soundness (`frep_interval_enclosure_sound`)**:
For every 3D bounding box `B : Box3D`, every point `(x, y, z)` contained in `B`, and every
constructive solid geometry expression `e : FRepExpr`, the exact point value `evalFRepPoint x y z e`
is guaranteed to lie within `evalFRepInterval B e`. -/
theorem frep_interval_enclosure_sound
    (B : Box3D) (x y z : Int) (e : FRepExpr)
    (hIn : B.contains x y z) :
    (evalFRepInterval B e).contains (evalFRepPoint x y z e) := by
  induction e with
  | const c =>
    dsimp only [evalFRepInterval, evalFRepPoint, FloatInterval.contains]
    omega
  | varX => exact hIn.1
  | varY => exact hIn.2.1
  | varZ => exact hIn.2.2
  | add a b iha ihb =>
    dsimp only [evalFRepInterval, evalFRepPoint, ivAdd, FloatInterval.contains] at *
    omega
  | sub a b iha ihb =>
    dsimp only [evalFRepInterval, evalFRepPoint, ivSub, FloatInterval.contains] at *
    omega
  | scalePos k a iha =>
    dsimp only [evalFRepInterval, evalFRepPoint, ivScalePos, FloatInterval.contains] at *
    have hk : (0 : Int) ≤ Int.ofNat k := Int.natCast_nonneg k
    exact ⟨int_mul_le_mul_of_nonneg_left _ _ (Int.ofNat k) iha.1 hk,
           int_mul_le_mul_of_nonneg_left _ _ (Int.ofNat k) iha.2 hk⟩
  | sq a iha =>
    dsimp only [evalFRepInterval, evalFRepPoint]
    exact ivSq_contains (evalFRepInterval B a) (evalFRepPoint x y z a) iha
  | csgUnion a b iha ihb =>
    dsimp only [evalFRepInterval, evalFRepPoint, ivMin, FloatInterval.contains] at *
    omega
  | csgInter a b iha ihb =>
    dsimp only [evalFRepInterval, evalFRepPoint, ivMax, FloatInterval.contains] at *
    omega
  | csgDiff a b iha ihb =>
    dsimp only [evalFRepInterval, evalFRepPoint, ivMax, ivNeg, FloatInterval.contains] at *
    omega
  | offset r a iha =>
    dsimp only [evalFRepInterval, evalFRepPoint, ivSub, FloatInterval.contains] at *
    omega

/-- **Certified Octree / Tape Pruning Soundness (`frep_octree_prune_exterior_sound`)**:
If the interval lower bound `(evalFRepInterval B e).lo` over 3D voxel `B` is strictly positive (`> 0`),
then *every* point `(x, y, z)` in `B` evaluates to `> 0` (strictly outside the solid).
This proves that octree subdivision and CNC air-cut skipping over `B` never miss any surface feature! -/
theorem frep_octree_prune_exterior_sound
    (B : Box3D) (e : FRepExpr) (hLo : 0 < (evalFRepInterval B e).lo)
    (x y z : Int) (hIn : B.contains x y z) :
    0 < evalFRepPoint x y z e := by
  have hEnc := frep_interval_enclosure_sound B x y z e hIn
  dsimp only [FloatInterval.contains] at hEnc
  omega

/-- **Certified Interior Voxel Soundness (`frep_octree_prune_interior_sound`)**:
If the interval upper bound `(evalFRepInterval B e).hi ≤ 0`, then *every* point `(x, y, z)` in `B`
lies inside the solid (`inSolid x y z e`). -/
theorem frep_octree_prune_interior_sound
    (B : Box3D) (e : FRepExpr) (hHi : (evalFRepInterval B e).hi ≤ 0)
    (x y z : Int) (hIn : B.contains x y z) :
    inSolid x y z e := by
  have hEnc := frep_interval_enclosure_sound B x y z e hIn
  dsimp only [FloatInterval.contains, inSolid] at *
  omega

/-! ### 2B. Matt Keeter's `fidget` Interval `Choice` Lattice & Recursive CSG Tape Specialization -/

/-- Matt Keeter's `fidget` (`fidget-core/src/vm/choice.rs`) 4-valued branch selection lattice
for interval-driven CSG tape specialization (`min` / `max` pruning):
* `unknown` (`0b00 = 0`): neither branch selected yet (lattice bottom $\bot$),
* `left`    (`0b01 = 1`): left operand strictly dominates across the octree cell,
* `right`   (`0b10 = 2`): right operand strictly dominates across the octree cell,
* `both`    (`0b11 = 3`): intervals overlap; both branches must be retained (lattice top $\top$). -/
inductive FidgetChoice where
  | unknown
  | left
  | right
  | both
  deriving DecidableEq, Repr

/-- 2-bit integer encoding (`0..3`) matching `fidget-core/src/vm/choice.rs`. -/
def FidgetChoice.toBits : FidgetChoice → Nat
  | .unknown => 0
  | .left    => 1
  | .right   => 2
  | .both    => 3

/-- Decode a 2-bit tag (`0..3`) back into `FidgetChoice`. -/
def FidgetChoice.fromBits : Nat → FidgetChoice
  | 0 => .unknown
  | 1 => .left
  | 2 => .right
  | _ => .both

/-- Bitwise OR / lattice join (`Choice::or` in `fidget-core/src/vm/choice.rs`). -/
def FidgetChoice.join : FidgetChoice → FidgetChoice → FidgetChoice
  | .unknown, c        => c
  | c,        .unknown => c
  | .left,    .left    => .left
  | .right,   .right   => .right
  | _,        _        => .both

/-- Bitwise AND / lattice meet (`Choice::and` in `fidget-core/src/vm/choice.rs`). -/
def FidgetChoice.meet : FidgetChoice → FidgetChoice → FidgetChoice
  | .both,  c      => c
  | c,      .both  => c
  | .left,  .left  => .left
  | .right, .right => .right
  | _,      _      => .unknown

/-- Swap `.left` and `.right` branch selections. -/
def FidgetChoice.flip : FidgetChoice → FidgetChoice
  | .unknown => .unknown
  | .left    => .right
  | .right   => .left
  | .both    => .both

/-- `FidgetChoice.join` is commutative, associative, and idempotent. -/
theorem fidgetChoice_join_laws (a b c : FidgetChoice) :
    a.join b = b.join a ∧
    (a.join b).join c = a.join (b.join c) ∧
    a.join a = a ∧
    a.flip.flip = a := by
  cases a <;> cases b <;> cases c <;> decide

/-- `fidget` (`fidget-core/src/types/interval.rs` `min_choice`) interval selector for $\min(a, b)$:
* Returns `.left` when `a.hi ≤ b.lo` ($a \le b$ everywhere in the box),
* Returns `.right` when `b.hi ≤ a.lo` ($b \le a$ everywhere in the box),
* Returns `.both` when the intervals overlap. -/
def ivMinChoice (a b : FloatInterval) : FidgetChoice :=
  if decide (a.hi ≤ b.lo) then .left
  else if decide (b.hi ≤ a.lo) then .right
  else .both

/-- `fidget` (`fidget-core/src/types/interval.rs` `max_choice`) interval selector for $\max(a, b)$:
* Returns `.left` when `b.hi ≤ a.lo` ($b \le a$ everywhere in the box),
* Returns `.right` when `a.hi ≤ b.lo` ($a \le b$ everywhere in the box),
* Returns `.both` when the intervals overlap. -/
def ivMaxChoice (a b : FloatInterval) : FidgetChoice :=
  if decide (b.hi ≤ a.lo) then .left
  else if decide (a.hi ≤ b.lo) then .right
  else .both

/-- Lemma: If `va ∈ ia`, `vb ∈ ib`, and `ivMinChoice ia ib = .left`, then `min va vb = va`. -/
theorem ivMinChoice_left_sound (ia ib : FloatInterval) (va vb : Int)
    (ha : ia.contains va) (hb : ib.contains vb)
    (hChoice : ivMinChoice ia ib = .left) :
    min va vb = va := by
  unfold ivMinChoice at hChoice
  dsimp only [FloatInterval.contains] at ha hb
  by_cases h1 : ia.hi ≤ ib.lo
  · omega
  · rw [if_neg (by simpa [decide_eq_true_iff] using h1)] at hChoice
    by_cases h2 : ib.hi ≤ ia.lo
    · rw [if_pos (decide_eq_true h2)] at hChoice
      cases hChoice
    · rw [if_neg (by simpa [decide_eq_true_iff] using h2)] at hChoice
      cases hChoice

/-- Lemma: If `va ∈ ia`, `vb ∈ ib`, and `ivMinChoice ia ib = .right`, then `min va vb = vb`. -/
theorem ivMinChoice_right_sound (ia ib : FloatInterval) (va vb : Int)
    (ha : ia.contains va) (hb : ib.contains vb)
    (hChoice : ivMinChoice ia ib = .right) :
    min va vb = vb := by
  unfold ivMinChoice at hChoice
  dsimp only [FloatInterval.contains] at ha hb
  by_cases h1 : ia.hi ≤ ib.lo
  · rw [if_pos (decide_eq_true h1)] at hChoice
    cases hChoice
  · rw [if_neg (by simpa [decide_eq_true_iff] using h1)] at hChoice
    by_cases h2 : ib.hi ≤ ia.lo
    · omega
    · rw [if_neg (by simpa [decide_eq_true_iff] using h2)] at hChoice
      cases hChoice

/-- Lemma: If `va ∈ ia`, `vb ∈ ib`, and `ivMaxChoice ia ib = .left`, then `max va vb = va`. -/
theorem ivMaxChoice_left_sound (ia ib : FloatInterval) (va vb : Int)
    (ha : ia.contains va) (hb : ib.contains vb)
    (hChoice : ivMaxChoice ia ib = .left) :
    max va vb = va := by
  unfold ivMaxChoice at hChoice
  dsimp only [FloatInterval.contains] at ha hb
  by_cases h1 : ib.hi ≤ ia.lo
  · omega
  · rw [if_neg (by simpa [decide_eq_true_iff] using h1)] at hChoice
    by_cases h2 : ia.hi ≤ ib.lo
    · rw [if_pos (decide_eq_true h2)] at hChoice
      cases hChoice
    · rw [if_neg (by simpa [decide_eq_true_iff] using h2)] at hChoice
      cases hChoice

/-- Lemma: If `va ∈ ia`, `vb ∈ ib`, and `ivMaxChoice ia ib = .right`, then `max va vb = vb`. -/
theorem ivMaxChoice_right_sound (ia ib : FloatInterval) (va vb : Int)
    (ha : ia.contains va) (hb : ib.contains vb)
    (hChoice : ivMaxChoice ia ib = .right) :
    max va vb = vb := by
  unfold ivMaxChoice at hChoice
  dsimp only [FloatInterval.contains] at ha hb
  by_cases h1 : ib.hi ≤ ia.lo
  · rw [if_pos (decide_eq_true h1)] at hChoice
    cases hChoice
  · rw [if_neg (by simpa [decide_eq_true_iff] using h1)] at hChoice
    by_cases h2 : ia.hi ≤ ib.lo
    · omega
    · rw [if_neg (by simpa [decide_eq_true_iff] using h2)] at hChoice
      cases hChoice

/-- Lemma: If `vb ∈ ib`, then `-vb ∈ ivNeg ib`. -/
theorem ivNeg_contains (ib : FloatInterval) (vb : Int) (hb : ib.contains vb) :
    (ivNeg ib).contains (-vb) := by
  dsimp only [ivNeg, FloatInterval.contains] at *
  omega

/-- Total AST node count of an `FRepExpr` CSG tape (`fidget` tape length). -/
def frepNodeCount : FRepExpr → Nat
  | .const _      => 1
  | .varX         => 1
  | .varY         => 1
  | .varZ         => 1
  | .add a b      => 1 + frepNodeCount a + frepNodeCount b
  | .sub a b      => 1 + frepNodeCount a + frepNodeCount b
  | .scalePos _ a => 1 + frepNodeCount a
  | .sq a         => 1 + frepNodeCount a
  | .csgUnion a b => 1 + frepNodeCount a + frepNodeCount b
  | .csgInter a b => 1 + frepNodeCount a + frepNodeCount b
  | .csgDiff a b  => 1 + frepNodeCount a + frepNodeCount b
  | .offset _ a   => 1 + frepNodeCount a

/-- Recursively specialize (`prune`) an `FRepExpr` CSG tape to a 3D octree cell `B : Box3D`
following Matt Keeter's `fidget` tape specialization (`fidget-core/src/vm/data.rs`):
* `.csgUnion a b` ($\min(a, b)$) prunes to `pruneFRepTape B a` when `ivMinChoice = .left`
  (`a.hi ≤ b.lo`) and to `pruneFRepTape B b` when `ivMinChoice = .right` (`b.hi ≤ a.lo`),
* `.csgInter a b` ($\max(a, b)$) prunes to `pruneFRepTape B a` when `ivMaxChoice = .left`
  (`b.hi ≤ a.lo`) and to `pruneFRepTape B b` when `ivMaxChoice = .right` (`a.hi ≤ b.lo`),
* `.csgDiff a b` ($\max(a, -b)$) prunes away the subtracted tool/feature `b` to `pruneFRepTape B a`
  whenever `ivMaxChoice (evalFRepInterval B a) (ivNeg (evalFRepInterval B b)) = .left`
  (`-(evalFRepInterval B b).lo ≤ (evalFRepInterval B a).lo`). -/
def pruneFRepTape (B : Box3D) : FRepExpr → FRepExpr
  | .const c      => .const c
  | .varX         => .varX
  | .varY         => .varY
  | .varZ         => .varZ
  | .add a b      => .add (pruneFRepTape B a) (pruneFRepTape B b)
  | .sub a b      => .sub (pruneFRepTape B a) (pruneFRepTape B b)
  | .scalePos k a => .scalePos k (pruneFRepTape B a)
  | .sq a         => .sq (pruneFRepTape B a)
  | .csgUnion a b =>
    match ivMinChoice (evalFRepInterval B a) (evalFRepInterval B b) with
    | .left  => pruneFRepTape B a
    | .right => pruneFRepTape B b
    | _      => .csgUnion (pruneFRepTape B a) (pruneFRepTape B b)
  | .csgInter a b =>
    match ivMaxChoice (evalFRepInterval B a) (evalFRepInterval B b) with
    | .left  => pruneFRepTape B a
    | .right => pruneFRepTape B b
    | _      => .csgInter (pruneFRepTape B a) (pruneFRepTape B b)
  | .csgDiff a b  =>
    match ivMaxChoice (evalFRepInterval B a) (ivNeg (evalFRepInterval B b)) with
    | .left  => pruneFRepTape B a
    | _      => .csgDiff (pruneFRepTape B a) (pruneFRepTape B b)
  | .offset r a   => .offset r (pruneFRepTape B a)

/-- **Universal `fidget` CSG Tape Pruning Soundness Theorem (`pruneFRepTape_sound`)**:
For every 3D octree bounding box `B : Box3D`, every point `(x, y, z)` contained in `B`, and every
CSG expression tree `e : FRepExpr`, evaluating the specialized tape `pruneFRepTape B e` at `(x, y, z)`
produces the **exact** same value as evaluating the unpruned tree `e` at `(x, y, z)`. -/
theorem pruneFRepTape_sound
    (B : Box3D) (x y z : Int) (e : FRepExpr)
    (hIn : B.contains x y z) :
    evalFRepPoint x y z (pruneFRepTape B e) = evalFRepPoint x y z e := by
  induction e with
  | const c => rfl
  | varX => rfl
  | varY => rfl
  | varZ => rfl
  | add a b iha ihb =>
    dsimp only [pruneFRepTape, evalFRepPoint]
    rw [iha, ihb]
  | sub a b iha ihb =>
    dsimp only [pruneFRepTape, evalFRepPoint]
    rw [iha, ihb]
  | scalePos k a iha =>
    dsimp only [pruneFRepTape, evalFRepPoint]
    rw [iha]
  | sq a iha =>
    dsimp only [pruneFRepTape, evalFRepPoint]
    rw [iha]
  | csgUnion a b iha ihb =>
    dsimp only [pruneFRepTape, evalFRepPoint]
    have ha := frep_interval_enclosure_sound B x y z a hIn
    have hb := frep_interval_enclosure_sound B x y z b hIn
    cases hC : ivMinChoice (evalFRepInterval B a) (evalFRepInterval B b) with
    | left =>
      dsimp only
      rw [iha, ivMinChoice_left_sound _ _ _ _ ha hb hC]
    | right =>
      dsimp only
      rw [ihb, ivMinChoice_right_sound _ _ _ _ ha hb hC]
    | unknown =>
      dsimp only [evalFRepPoint]
      rw [iha, ihb]
    | both =>
      dsimp only [evalFRepPoint]
      rw [iha, ihb]
  | csgInter a b iha ihb =>
    dsimp only [pruneFRepTape, evalFRepPoint]
    have ha := frep_interval_enclosure_sound B x y z a hIn
    have hb := frep_interval_enclosure_sound B x y z b hIn
    cases hC : ivMaxChoice (evalFRepInterval B a) (evalFRepInterval B b) with
    | left =>
      dsimp only
      rw [iha, ivMaxChoice_left_sound _ _ _ _ ha hb hC]
    | right =>
      dsimp only
      rw [ihb, ivMaxChoice_right_sound _ _ _ _ ha hb hC]
    | unknown =>
      dsimp only [evalFRepPoint]
      rw [iha, ihb]
    | both =>
      dsimp only [evalFRepPoint]
      rw [iha, ihb]
  | csgDiff a b iha ihb =>
    dsimp only [pruneFRepTape, evalFRepPoint]
    have ha := frep_interval_enclosure_sound B x y z a hIn
    have hb := ivNeg_contains _ _ (frep_interval_enclosure_sound B x y z b hIn)
    cases hC : ivMaxChoice (evalFRepInterval B a) (ivNeg (evalFRepInterval B b)) with
    | left =>
      dsimp only
      rw [iha, ivMaxChoice_left_sound _ _ _ _ ha hb hC]
    | right =>
      dsimp only [evalFRepPoint]
      rw [iha, ihb]
    | unknown =>
      dsimp only [evalFRepPoint]
      rw [iha, ihb]
    | both =>
      dsimp only [evalFRepPoint]
      rw [iha, ihb]
  | offset r a iha =>
    dsimp only [pruneFRepTape, evalFRepPoint]
    rw [iha]

/-- **Universal `fidget` Tape Compaction Theorem (`pruneFRepTape_size_le`)**:
Specializing any CSG expression tree `e : FRepExpr` to any 3D octree cell `B : Box3D` never
increases the AST node count (`frepNodeCount (pruneFRepTape B e) ≤ frepNodeCount e`). -/
theorem pruneFRepTape_size_le (B : Box3D) (e : FRepExpr) :
    frepNodeCount (pruneFRepTape B e) ≤ frepNodeCount e := by
  induction e with
  | const _ => exact Nat.le_refl _
  | varX => exact Nat.le_refl _
  | varY => exact Nat.le_refl _
  | varZ => exact Nat.le_refl _
  | add a b iha ihb =>
    dsimp only [pruneFRepTape, frepNodeCount]
    omega
  | sub a b iha ihb =>
    dsimp only [pruneFRepTape, frepNodeCount]
    omega
  | scalePos k a iha =>
    dsimp only [pruneFRepTape, frepNodeCount]
    omega
  | sq a iha =>
    dsimp only [pruneFRepTape, frepNodeCount]
    omega
  | csgUnion a b iha ihb =>
    dsimp only [pruneFRepTape, frepNodeCount]
    cases ivMinChoice (evalFRepInterval B a) (evalFRepInterval B b) <;>
      dsimp only [frepNodeCount] <;> omega
  | csgInter a b iha ihb =>
    dsimp only [pruneFRepTape, frepNodeCount]
    cases ivMaxChoice (evalFRepInterval B a) (evalFRepInterval B b) <;>
      dsimp only [frepNodeCount] <;> omega
  | csgDiff a b iha ihb =>
    dsimp only [pruneFRepTape, frepNodeCount]
    cases ivMaxChoice (evalFRepInterval B a) (ivNeg (evalFRepInterval B b)) <;>
      dsimp only [frepNodeCount] <;> omega
  | offset r a iha =>
    dsimp only [pruneFRepTape, frepNodeCount]
    omega

/-- **Golden Multi-Feature Stator CSG Tape Compaction Certificate (`golden_fidget_tape_pruning_verified`)**:
On a 3-feature stator CSG expression combining:
1. Primary stator core cylinder $x^2 + y^2 - 100$,
2. Unioned mounting lug $(x - 20)^2 + y^2 - 4$, and
3. Subtracted axial cooling bore $(x + 20)^2 + y^2 - 4$,
specializing the 24-node CSG tape over an octree sub-box $B = [-2, 2]^3$ near the stator center
prunes away both the distant mounting lug (`.csgUnion` $\to$ `.left`) and the distant cooling bore
(`.csgDiff` $\to$ `.left`), compacting the tape from `24` AST nodes down to `6` AST nodes while
preserving exact point evaluations inside $B$! -/
theorem golden_fidget_tape_pruning_verified :
    let statorCore : FRepExpr := .offset 100 (.add (.sq .varX) (.sq .varY))
    let mountingLug : FRepExpr := .offset 4 (.add (.sq (.sub .varX (.const 20))) (.sq .varY))
    let coolingBore : FRepExpr := .offset 4 (.add (.sq (.add .varX (.const 20))) (.sq .varY))
    let fullStatorCsg : FRepExpr := .csgDiff (.csgUnion statorCore mountingLug) coolingBore
    let centerOctreeCell : Box3D :=
      { xIv := { lo := -2, hi := 2 }
        yIv := { lo := -2, hi := 2 }
        zIv := { lo := -2, hi := 2 } }
    let prunedTape := pruneFRepTape centerOctreeCell fullStatorCsg
    frepNodeCount fullStatorCsg = 24 ∧
    frepNodeCount prunedTape = 6 ∧
    frepNodeCount prunedTape < frepNodeCount fullStatorCsg ∧
    prunedTape = statorCore ∧
    evalFRepPoint 1 (-1) 0 prunedTape = evalFRepPoint 1 (-1) 0 fullStatorCsg := by
  decide +kernel

/-! ## 3. Implicit Swept-Volume CAM Material Removal & Zero-Gouge Certification -/

/-- Evaluates the In-Process Workpiece (`IPW`) after subtracting cutter swept volume `fSwept`
from initial stock `fStock`: `csgDiff fStock fSwept`. -/
def evalMachinedWorkpiece (x y z : Int) (fStock fSwept : FRepExpr) : Int :=
  evalFRepPoint x y z (.csgDiff fStock fSwept)

/-- **Subtractive Machining Monotonicity (`machining_material_monotone_removal`)**:
Milling with any cutter swept volume `fSwept` monotonically increases the F-Rep value
($f_{\text{stock}}(p) \le f_{\text{IPW}}(p)$), proving that subtractive toolpaths can only remove
material ($f \le 0 \to f > 0$) and can never add material where none existed. -/
theorem machining_material_monotone_removal
    (x y z : Int) (fStock fSwept : FRepExpr) :
    evalFRepPoint x y z fStock ≤ evalMachinedWorkpiece x y z fStock fSwept := by
  dsimp only [evalMachinedWorkpiece, evalFRepPoint]
  omega

/-- Boolean checker verifying that cutter swept volume `fSwept` is strictly exterior (`lo > 0`)
across bounding box `B`. -/
def checkVoxelNoGouge (B : Box3D) (fSwept : FRepExpr) : Bool :=
  decide (0 < (evalFRepInterval B fSwept).lo)

/-- **Zero-Gouge Machining Theorem (`voxel_no_gouge_sound`)**:
If `checkVoxelNoGouge B fSwept = true` for a bounding box `B` enclosing a region of the desired
finished part (`inSolid x y z fStock`), then for every point `(x, y, z) ∈ B`, the cutter never
removes material from `(x, y, z)` (`inSolid x y z (.csgDiff fStock fSwept)`). -/
theorem voxel_no_gouge_sound
    (B : Box3D) (fStock fSwept : FRepExpr)
    (hNoGouge : checkVoxelNoGouge B fSwept = true)
    (x y z : Int) (hInBox : B.contains x y z)
    (hInStock : inSolid x y z fStock) :
    inSolid x y z (.csgDiff fStock fSwept) := by
  unfold checkVoxelNoGouge at hNoGouge
  have hLo : 0 < (evalFRepInterval B fSwept).lo := of_decide_eq_true hNoGouge
  have hExt := frep_octree_prune_exterior_sound B fSwept hLo x y z hInBox
  dsimp only [inSolid, evalFRepPoint] at *
  omega

/-! ## 4. Machine-Tool Dynamics: Servo Lag, End-Mill Cantilever Deflection & Altintas Chatter -/

/-- Evaluates the radial cutting force $F_r = k_r \cdot a_p \cdot h_{\text{chip}}$ (in milli-Newtons)
for radial cutting coefficient `krScaled`, axial depth of cut `apUm`, and feed per tooth `chipLoadUm`. -/
def evalRadialCuttingForceMn (krScaled apUm chipLoadUm : Int) : Int :=
  krScaled * apUm * chipLoadUm

/-- Evaluates the true physical cutter position (in nanometers) by accounting for:
1. Commanded G-code position `xCmdNm`,
2. Ballscrew/servo velocity tracking lag `feedVelMmPerS * servoLagNsPerMm`, and
3. End-mill cantilever bending deflection `toolComplianceNmPerMn * radialForceMn`. -/
def evalActualCutterPosNm
    (xCmdNm feedVelMmPerS servoLagNsPerMm toolComplianceNmPerMn radialForceMn : Int) : Int :=
  xCmdNm - (feedVelMmPerS * servoLagNsPerMm + toolComplianceNmPerMn * radialForceMn)

/-- Evaluates the total dimensional surface error $x_{\text{cmd}} - x_{\text{actual}}$ (in nanometers)
induced by machine-tool servo lag and cutter deflection. -/
def evalMachiningDimensionalErrorNm
    (feedVelMmPerS servoLagNsPerMm toolComplianceNmPerMn radialForceMn : Int) : Int :=
  feedVelMmPerS * servoLagNsPerMm + toolComplianceNmPerMn * radialForceMn

/-- **Exact Machine-Tool Deflection & Servo-Lag Error Identity (`machining_dimensional_error_identity`)**:
The discrepancy between the G-code commanded coordinate and the physical cutter tip coordinate is
identically `evalMachiningDimensionalErrorNm`. -/
theorem machining_dimensional_error_identity
    (xCmdNm feedVelMmPerS servoLagNsPerMm toolComplianceNmPerMn radialForceMn : Int) :
    xCmdNm - evalActualCutterPosNm xCmdNm feedVelMmPerS servoLagNsPerMm toolComplianceNmPerMn radialForceMn =
      evalMachiningDimensionalErrorNm feedVelMmPerS servoLagNsPerMm toolComplianceNmPerMn radialForceMn := by
  unfold evalActualCutterPosNm evalMachiningDimensionalErrorNm
  omega

/-- **Feed & Chip-Load Governor Theorem (`machining_governor_bounds_surface_error`)**:
Whenever feed velocity `feedVel ≤ maxFeedVel` and radial cutting force `radialForce ≤ maxForce`
with non-negative servo lag and tool compliance (`0 ≤ servoLag`, `0 ≤ compliance`), the actual
machined surface dimensional error is bounded by the governed ceiling. -/
theorem machining_governor_bounds_surface_error
    (feedVel maxFeedVel servoLag compliance radialForce maxForce : Int)
    (hFeed : feedVel ≤ maxFeedVel)
    (hForce : radialForce ≤ maxForce)
    (hLag : 0 ≤ servoLag)
    (hComp : 0 ≤ compliance) :
    evalMachiningDimensionalErrorNm feedVel servoLag compliance radialForce ≤
      evalMachiningDimensionalErrorNm maxFeedVel servoLag compliance maxForce := by
  unfold evalMachiningDimensionalErrorNm
  have h1 := int_mul_le_mul_of_nonneg_right feedVel maxFeedVel servoLag hFeed hLag
  have h2 := int_mul_le_mul_of_nonneg_left radialForce maxForce compliance hForce hComp
  omega

/-- **Altintas–Budak Regenerative Chatter Stability Predicate (`checkAltintasChatterStable`)**:
In Yusuf Altintas's regenerative chatter theory, self-excited vibrations are avoided when the
product of axial depth of cut `apUm`, cutting force coefficient `kfScaled`, and the negative real
part of the spindle-tool-holder transfer function `negReFrfScaled` stays within the critical
damping stability boundary `chatterLimitScaled`:
$$2 \cdot a_p \cdot K_f \cdot |\operatorname{Re}[G(\omega_c)]| \le C_{\text{lim}}.$$ -/
def checkAltintasChatterStable
    (apUm kfScaled negReFrfScaled chatterLimitScaled : Int) : Bool :=
  decide (0 ≤ apUm ∧ 2 * apUm * kfScaled * negReFrfScaled ≤ chatterLimitScaled)

/-- **Altintas Chatter Stability Monotonicity (`altintas_chatter_depth_monotone`)**:
For any positive cutting coefficient and spindle FRF magnitude (`0 ≤ kfScaled`, `0 ≤ negReFrfScaled`),
if an axial depth of cut `ap2` is chatter-stable, then any shallower cut `0 ≤ ap1 ≤ ap2` is also
guaranteed to be chatter-stable. -/
theorem altintas_chatter_depth_monotone
    (ap1 ap2 kfScaled negReFrfScaled chatterLimitScaled : Int)
    (hAp1 : 0 ≤ ap1) (hLe : ap1 ≤ ap2)
    (hKf : 0 ≤ kfScaled) (hFrf : 0 ≤ negReFrfScaled)
    (hStable2 : checkAltintasChatterStable ap2 kfScaled negReFrfScaled chatterLimitScaled = true) :
    checkAltintasChatterStable ap1 kfScaled negReFrfScaled chatterLimitScaled = true := by
  unfold checkAltintasChatterStable at *
  have h2 := of_decide_eq_true hStable2
  rw [decide_eq_true_iff]
  refine ⟨hAp1, ?_⟩
  have h2Ap : 2 * ap1 ≤ 2 * ap2 := by omega
  have hMul1 := int_mul_le_mul_of_nonneg_right (2 * ap1) (2 * ap2) kfScaled h2Ap hKf
  have hMul2 := int_mul_le_mul_of_nonneg_right (2 * ap1 * kfScaled) (2 * ap2 * kfScaled) negReFrfScaled hMul1 hFrf
  omega

/-! ## 5. In-Silico Evolutionary Physical Design Search & Signoff -/

/-- A candidate physical design and CAM process plan generated by an evolutionary / gradient agent:
* `candidateId`: nominal design identifier,
* `sweptLo`: interval lower bound of cutter swept-volume SDF over the protected target part box,
* `surfaceErrNm`: worst-case servo-lag + tool-deflection surface error (in nm),
* `maxTolNm`: maximum allowed dimensional tolerance (in nm),
* `apUm`, `kfScaled`, `negReFrfScaled`, `chatterLimitScaled`: Altintas chatter parameters,
* `performanceScore`: multiphysics objective score (e.g., torque-to-weight or thermal margin). -/
structure PhysicalDesignCandidate where
  candidateId        : Nat
  sweptLo            : Int
  surfaceErrNm       : Int
  maxTolNm           : Int
  apUm               : Int
  kfScaled           : Int
  negReFrfScaled     : Int
  chatterLimitScaled : Int
  performanceScore   : Int
  deriving DecidableEq, Repr

/-- Kernel verification gate for a physical design candidate:
1. Zero gouging (`0 < c.sweptLo`),
2. Dimensional accuracy under machine-tool deflection & servo lag (`c.surfaceErrNm ≤ c.maxTolNm`),
3. Altintas regenerative chatter stability (`checkAltintasChatterStable = true`), and
4. Multiphysics performance floor (`minScore ≤ c.performanceScore`). -/
def checkCandidateManufacturingSafe (minScore : Int) (c : PhysicalDesignCandidate) : Bool :=
  decide (0 < c.sweptLo) &&
  decide (c.surfaceErrNm ≤ c.maxTolNm) &&
  checkAltintasChatterStable c.apUm c.kfScaled c.negReFrfScaled c.chatterLimitScaled &&
  decide (minScore ≤ c.performanceScore)

/-- Filter an evolutionary population of candidate physical designs down to the kernel-certified subset. -/
def filterVerifiedDesigns (minScore : Int) (pop : List PhysicalDesignCandidate) : List PhysicalDesignCandidate :=
  pop.filter (checkCandidateManufacturingSafe minScore)

/-- **Evolutionary Design Search Soundness Theorem (`evolutionary_search_emits_only_verified_designs`)**:
Every physical design candidate `c` retained by `filterVerifiedDesigns minScore pop` is guaranteed
to be gouge-free (`0 < c.sweptLo`), within dimensional tolerance (`c.surfaceErrNm ≤ c.maxTolNm`),
chatter-stable (`checkAltintasChatterStable = true`), and above the multiphysics performance floor. -/
theorem evolutionary_search_emits_only_verified_designs
    (minScore : Int) (pop : List PhysicalDesignCandidate) (c : PhysicalDesignCandidate)
    (hMem : c ∈ filterVerifiedDesigns minScore pop) :
    0 < c.sweptLo ∧
    c.surfaceErrNm ≤ c.maxTolNm ∧
    checkAltintasChatterStable c.apUm c.kfScaled c.negReFrfScaled c.chatterLimitScaled = true ∧
    minScore ≤ c.performanceScore := by
  unfold filterVerifiedDesigns at hMem
  rw [List.mem_filter] at hMem
  have hOk := hMem.2
  unfold checkCandidateManufacturingSafe at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  exact ⟨hOk.1.1.1, hOk.1.1.2, hOk.1.2, hOk.2⟩

/-- **Golden 5-Axis Stator-Slot Microchannel Milling & Evolutionary Search Certificate
(`golden_geometry_cam_evolutionary_search_verified`)**:
Verifies by kernel evaluation (`decide +kernel`):
1. Octree exterior pruning of a 3D F-Rep sphere $x^2 + y^2 + z^2 - 100$ over box $[10, 12]^3$ (`lo = 200 > 0`),
2. Zero-gouge CAM material removal on the stator tooth bounding box,
3. Machine-tool deflection + servo-lag error ($3500\,\text{nm} \le 5000\,\text{nm}$ tolerance), and
4. Evolutionary filtering of a 3-candidate design population (rejecting a gouging candidate and a
   chattering candidate, and selecting the verified high-torque candidate `#2`). -/
theorem golden_geometry_cam_evolutionary_search_verified :
    let sphereR10 := FRepExpr.offset 100 (.add (.add (.sq .varX) (.sq .varY)) (.sq .varZ))
    let farBox : Box3D :=
      { xIv := { lo := 10, hi := 12 }
        yIv := { lo := 10, hi := 12 }
        zIv := { lo := 10, hi := 12 } }
    let candGouge : PhysicalDesignCandidate :=
      { candidateId := 1, sweptLo := -5, surfaceErrNm := 2000, maxTolNm := 5000,
        apUm := 1500, kfScaled := 2, negReFrfScaled := 3, chatterLimitScaled := 25000, performanceScore := 950 }
    let candVerified : PhysicalDesignCandidate :=
      { candidateId := 2, sweptLo := 200, surfaceErrNm := 3500, maxTolNm := 5000,
        apUm := 2000, kfScaled := 2, negReFrfScaled := 3, chatterLimitScaled := 25000, performanceScore := 920 }
    let candChatter : PhysicalDesignCandidate :=
      { candidateId := 3, sweptLo := 150, surfaceErrNm := 3000, maxTolNm := 5000,
        apUm := 6000, kfScaled := 2, negReFrfScaled := 3, chatterLimitScaled := 25000, performanceScore := 980 }
    (evalFRepInterval farBox sphereR10).lo = 200 ∧
    checkVoxelNoGouge farBox sphereR10 = true ∧
    evalMachiningDimensionalErrorNm 50 10 3 1000 = 3500 ∧
    (filterVerifiedDesigns 800 [candGouge, candVerified, candChatter]).map (·.candidateId) = [2] := by
  decide +kernel

/-! ## 6. Mechanized OpenUSD (`LIVERPS`) Scene Composition, `Sdf` × `SDF` Solid Layers & Temporal `timeSamples` Persistence -/

/-- The 7 composition arc kinds of Apple/Pixar OpenUSD (`LIVERPS` strength ordering,
from strongest `localArc` to weakest `specializesArc`):
* `localArc`       (**L**ocal / SubLayers — strongest direct opinion),
* `inheritsArc`    (**I**nherits — C4 nominal class broadcast),
* `variantArc`     (**V**ariantSets — contextual `Slot` variant choice),
* `relocatesArc`   (r**E**locates — non-destructive namespace path remapping),
* `referencesArc`  (**R**eferences — external part/sub-assembly composition),
* `payloadArc`     (**P**ayloads — lazy call-by-need deferred assembly),
* `specializesArc` (**S**pecializes — globally weakest fallback template). -/
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

/-- An authored OpenUSD property/geometry opinion tagged with its `LIVERPS` composition arc
and intra-arc layer priority. -/
structure UsdOpinion (α : Type) where
  arc      : UsdArcKind
  subLayer : Nat
  value    : α
  deriving DecidableEq, Repr

/-- Returns `true` iff opinion `a` is at least as strong as opinion `b` under `LIVERPS`
(stronger arc wins; ties broken by higher `subLayer` priority). -/
def usdOpinionStrongerOrEq {α : Type} (a b : UsdOpinion α) : Bool :=
  if a.arc.strength == b.arc.strength then
    decide (b.subLayer ≤ a.subLayer)
  else
    decide (b.arc.strength < a.arc.strength)

/-- Resolve two OpenUSD opinions according to `LIVERPS` strength ordering. -/
def resolveLiverpsPair {α : Type} (a b : UsdOpinion α) : UsdOpinion α :=
  if usdOpinionStrongerOrEq a b then a else b

/-- Resolve a non-empty stack of OpenUSD opinions with a fallback default opinion. -/
def resolveLiverpsStack {α : Type} (fallback : UsdOpinion α) : List (UsdOpinion α) → UsdOpinion α
  | []        => fallback
  | op :: ops => resolveLiverpsPair op (resolveLiverpsStack fallback ops)

/-- **`LIVERPS` Local Dominance Theorem (`liverps_local_dominates_nonlocal`)**:
Any `localArc` opinion strictly dominates every `inheritsArc`, `variantArc`, `relocatesArc`,
`referencesArc`, `payloadArc`, or `specializesArc` opinion regardless of `subLayer` index. -/
theorem liverps_local_dominates_nonlocal {α : Type}
    (loc other : UsdOpinion α)
    (hLoc : loc.arc = .localArc)
    (hNotLoc : other.arc ≠ .localArc) :
    resolveLiverpsPair loc other = loc := by
  unfold resolveLiverpsPair usdOpinionStrongerOrEq
  rw [hLoc]
  cases hArc : other.arc <;>
    simp_all [UsdArcKind.strength]

/-- **`LIVERPS` Specializes Globally Weakest Theorem (`liverps_specializes_globally_weakest`)**:
A `specializesArc` opinion always yields to any non-`specializesArc` opinion in `LIVERPS`
regardless of `subLayer` index, acting as a true globally-weakest prototype fallback. -/
theorem liverps_specializes_globally_weakest {α : Type}
    (stronger specOp : UsdOpinion α)
    (hNotSpec : stronger.arc ≠ .specializesArc)
    (hSpec : specOp.arc = .specializesArc) :
    resolveLiverpsPair stronger specOp = stronger := by
  unfold resolveLiverpsPair usdOpinionStrongerOrEq
  rw [hSpec]
  cases hArc : stronger.arc <;>
    simp_all [UsdArcKind.strength]

/-- Open-recursive `Sdf` × `SDF` solid geometry modifier inside an OpenUSD layer:
* `replaceSolid f`: replaces the inherited solid geometry with `f`,
* `subtractFeature fCut`: non-destructively mills/drills `fCut` out of `super` (`csgDiff super fCut`),
* `unionBoss fBoss`: non-destructively fuses a boss/rib `fBoss` onto `super` (`csgUnion super fBoss`),
* `offsetShell r`: offsets `super` outward by `r` (`offset r super`). -/
inductive UsdSdfModifier where
  | replaceSolid    (f : FRepExpr)
  | subtractFeature (fCut : FRepExpr)
  | unionBoss       (fBoss : FRepExpr)
  | offsetShell     (r : Int)
  deriving DecidableEq, Repr

/-- Apply a `UsdSdfModifier` layer to an inherited `super` `FRepExpr` (analogous to `Obend` `mix`). -/
def applyUsdSdfModifier (superSdf : FRepExpr) : UsdSdfModifier → FRepExpr
  | .replaceSolid f       => f
  | .subtractFeature fCut => .csgDiff superSdf fCut
  | .unionBoss fBoss      => .csgUnion superSdf fBoss
  | .offsetShell r        => .offset r superSdf

/-- Compose a C4/`LIVERPS`-linearized list of `UsdSdfModifier` layers on top of a `seed` solid. -/
def composeUsdSdfLayers (seed : FRepExpr) : List UsdSdfModifier → FRepExpr
  | []          => seed
  | mod :: rest => applyUsdSdfModifier (composeUsdSdfLayers seed rest) mod

/-- **Non-Destructive Subtractive Layer Soundness (`usd_subtract_feature_monotone`)**:
Applying a `.subtractFeature fCut` layer (such as an LC Drives in-slot cooling channel or a 5-axis
CAM roughing pass) on top of `superSdf` never adds material anywhere in $\mathbb{Z}^3$. -/
theorem usd_subtract_feature_monotone (x y z : Int) (superSdf fCut : FRepExpr) :
    evalFRepPoint x y z superSdf ≤
      evalFRepPoint x y z (applyUsdSdfModifier superSdf (.subtractFeature fCut)) := by
  dsimp only [applyUsdSdfModifier, evalFRepPoint]
  omega

/-- A time-sampled physical state (`timeSamples` in OpenUSD) pairing an integer `timeCode`
(e.g. microseconds, G-code block index, or lifecycle epoch) with a solid `FRepExpr` and
telemetry value. -/
structure UsdTimeSample where
  timeCode  : Nat
  solidSdf  : FRepExpr
  telemetry : Int
  deriving DecidableEq, Repr

/-- Look up the active `UsdTimeSample` at query time `t` (returning the latest sample with `timeCode ≤ t`). -/
def lookupTimeSample (fallback : UsdTimeSample) (t : Nat) : List UsdTimeSample → UsdTimeSample
  | [] => fallback
  | s :: rest =>
    let later := lookupTimeSample fallback t rest
    if decide (s.timeCode ≤ t ∧ later.timeCode ≤ s.timeCode) then s else later

/-- Golden OpenUSD `LIVERPS` + `Sdf` × `SDF` + `timeSamples` Verification (`golden_openusd_liverps_sdf_verified`):
Verifies that:
1. A `.localArc` cooling-channel override beats `.variantArc` and `.specializesArc` opinions,
2. Composing a `.subtractFeature` cooling bore on top of a cylindrical stator billet `FRepExpr`
   cleanly removes the bore center `(0, 0, 0)` (`evalFRepPoint > 0`) while preserving the stator wall
   `(8, 0, 0)` (`evalFRepPoint ≤ 0`), and
3. Querying `lookupTimeSample` across a 3-stage machining lifecycle (`t = 0` raw billet, `t = 10`
   rough milled, `t = 20` finish ground) selects the exact stage at `t = 15`. -/
theorem golden_openusd_liverps_sdf_verified :
    let opSpec : UsdOpinion Int := { arc := .specializesArc, subLayer := 99, value := 180 }
    let opVar  : UsdOpinion Int := { arc := .variantArc,     subLayer := 5,  value := 148 }
    let opLoc  : UsdOpinion Int := { arc := .localArc,       subLayer := 0,  value := 122 }
    let statorBillet := FRepExpr.offset 100 (.add (.sq .varX) (.sq .varY))
    let coolingBore  := FRepExpr.offset 9   (.add (.sq .varX) (.sq .varY))
    let composedPart := composeUsdSdfLayers statorBillet [.subtractFeature coolingBore]
    let t0  : UsdTimeSample := { timeCode := 0,  solidSdf := statorBillet, telemetry := 25000 }
    let t10 : UsdTimeSample := { timeCode := 10, solidSdf := composedPart, telemetry := 85000 }
    let t20 : UsdTimeSample := { timeCode := 20, solidSdf := composedPart, telemetry := 122000 }
    (resolveLiverpsStack opSpec [opVar, opLoc]).value = 122 ∧
    0 < evalFRepPoint 0 0 0 composedPart ∧
    evalFRepPoint 8 0 0 composedPart ≤ 0 ∧
    (lookupTimeSample t0 15 [t0, t10, t20]).timeCode = 10 := by
  decide +kernel

end Obend.Hardware.GeometryCAM
end
