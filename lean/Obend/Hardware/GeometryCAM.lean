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

/-- Every `FRepExpr` has at least one AST node (`1 ≤ frepNodeCount e`). -/
theorem frepNodeCount_pos (e : FRepExpr) : 1 ≤ frepNodeCount e := by
  cases e <;> dsimp only [frepNodeCount] <;> omega

/-- Recursively specialize (`prune`) an `FRepExpr` CSG tape to a 3D octree cell `B : Box3D`
following Matt Keeter's `fidget` tape specialization (`fidget-core/src/vm/data.rs`):
* `.csgUnion a b` ($\min(a, b)$) prunes to `pruneFRepTape B a` when `ivMinChoice = .left`
  (`a.hi ≤ b.lo`) and to `pruneFRepTape B b` when `ivMinChoice = .right` (`b.hi ≤ a.lo`),
* `.csgInter a b` ($\max(a, b)$) prunes to `pruneFRepTape B a` when `ivMaxChoice = .left`
  (`b.hi ≤ a.lo`) and to `pruneFRepTape B b` when `ivMaxChoice = .right` (`a.hi ≤ b.lo`),
* `.csgDiff a b` ($\max(a, -b)$) prunes away the subtracted tool/feature `b` to `pruneFRepTape B a`
  when `ivMaxChoice (evalFRepInterval B a) (ivNeg (evalFRepInterval B b)) = .left`
  (`-(evalFRepInterval B b).lo ≤ (evalFRepInterval B a).lo`), and prunes away the stock `a` to
  `.sub (.const 0) (pruneFRepTape B b)` when `ivMaxChoice = .right`
  (`(evalFRepInterval B a).hi ≤ -(evalFRepInterval B b).hi`, i.e., tool `b` completely removes the voxel cell). -/
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
    | .right => .sub (.const 0) (pruneFRepTape B b)
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
      have hRight := ivMaxChoice_right_sound _ _ _ _ ha hb hC
      rw [ihb]
      omega
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
    have haPos := frepNodeCount_pos a
    dsimp only [pruneFRepTape, frepNodeCount]
    cases ivMaxChoice (evalFRepInterval B a) (ivNeg (evalFRepInterval B b)) <;>
      dsimp only [frepNodeCount] <;> omega
  | offset r a iha =>
    dsimp only [pruneFRepTape, frepNodeCount]
    omega

/-- **Right-Branch `.csgDiff` Tool-Carveout Pruning Theorem (`csgDiff_right_branch_pruning_sound`)**:
When a subtracted tool/bore `b` completely removes the voxel cell `B` so that `-b` dominates stock `a`
(`ivMaxChoice (evalFRepInterval B a) (ivNeg (evalFRepInterval B b)) = .right`), `pruneFRepTape`
eliminates the stock expression `a` completely and specializes `.csgDiff a b` to
`.sub (.const 0) (pruneFRepTape B b)`. -/
theorem csgDiff_right_branch_pruning_sound
    (B : Box3D) (a b : FRepExpr)
    (hRight : ivMaxChoice (evalFRepInterval B a) (ivNeg (evalFRepInterval B b)) = .right) :
    pruneFRepTape B (.csgDiff a b) = .sub (.const 0) (pruneFRepTape B b) := by
  dsimp only [pruneFRepTape]
  rw [hRight]

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

/-! ### 2C. Canonical Linear SSA F-Rep Register Tape (`SsaTapeOp`), Interval Pruning & Backward-Liveness Compaction -/

/-- Instruction in a linear Single Static Assignment (`SSA`) 3D F-Rep register tape (`fidget` VM tape):
each instruction at list index `i` writes its result into SSA register `i` and reads previously
defined registers `r, r1, r2 : Nat`. -/
inductive SsaTapeOp where
  | const    (c : Int)
  | varX
  | varY
  | varZ
  | neg      (r : Nat)
  | add      (r1 r2 : Nat)
  | sub      (r1 r2 : Nat)
  | mul      (r1 r2 : Nat)
  | minUnion (r1 r2 : Nat)
  | maxInter (r1 r2 : Nat)
  deriving DecidableEq, Repr

/-- Default zero interval `{ lo := 0, hi := 0 }` for out-of-range SSA register lookups. -/
def defaultSsaIv : FloatInterval := { lo := 0, hi := 0 }

/-- Integer absolute value $|z|$ for symmetric interval product bounds. -/
def frepIntAbs (z : Int) : Int :=
  if 0 ≤ z then z else -z

theorem frepIntAbs_bounds (z : Int) :
    0 ≤ frepIntAbs z ∧ z ≤ frepIntAbs z ∧ -z ≤ frepIntAbs z := by
  unfold frepIntAbs
  omega

theorem frep_abs_mul_bound (x y r1 r2 : Int)
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

/-- Maximum absolute magnitude $\max(|a_{\text{lo}}|, |a_{\text{hi}}|)$ of a `FloatInterval`. -/
def ivAbsBound (a : FloatInterval) : Int :=
  max (frepIntAbs a.lo) (frepIntAbs a.hi)

/-- Conservative interval product enclosure for general `.mul r1 r2`. -/
def ivMulSym (a b : FloatInterval) : FloatInterval :=
  let rad := ivAbsBound a * ivAbsBound b
  { lo := -rad, hi := rad }

theorem ivMulSym_contains (a b : FloatInterval) (va vb : Int)
    (ha : a.contains va) (hb : b.contains vb) :
    (ivMulSym a b).contains (va * vb) := by
  dsimp only [ivMulSym, ivAbsBound, FloatInterval.contains] at *
  have halo := frepIntAbs_bounds a.lo
  have hahi := frepIntAbs_bounds a.hi
  have hblo := frepIntAbs_bounds b.lo
  have hbhi := frepIntAbs_bounds b.hi
  have hra : 0 ≤ max (frepIntAbs a.lo) (frepIntAbs a.hi) := by omega
  have hrb : 0 ≤ max (frepIntAbs b.lo) (frepIntAbs b.hi) := by omega
  have hva : -max (frepIntAbs a.lo) (frepIntAbs a.hi) ≤ va ∧ va ≤ max (frepIntAbs a.lo) (frepIntAbs a.hi) := by omega
  have hvb : -max (frepIntAbs b.lo) (frepIntAbs b.hi) ≤ vb ∧ vb ≤ max (frepIntAbs b.lo) (frepIntAbs b.hi) := by omega
  exact frep_abs_mul_bound va vb _ _ hra hrb hva hvb

/-- Evaluate a single `SsaTapeOp` at 3D point `(x, y, z)` given the current SSA register file `regs`. -/
def evalSsaOpPoint (x y z : Int) (regs : List Int) : SsaTapeOp → Int
  | .const c        => c
  | .varX           => x
  | .varY           => y
  | .varZ           => z
  | .neg r          => -(regs.getD r 0)
  | .add r1 r2      => regs.getD r1 0 + regs.getD r2 0
  | .sub r1 r2      => regs.getD r1 0 - regs.getD r2 0
  | .mul r1 r2      => regs.getD r1 0 * regs.getD r2 0
  | .minUnion r1 r2 => min (regs.getD r1 0) (regs.getD r2 0)
  | .maxInter r1 r2 => max (regs.getD r1 0) (regs.getD r2 0)

/-- Evaluate a single `SsaTapeOp` over 3D bounding box `B` given the current interval register file `ivRegs`.
Uses exact `ivSq` when squaring a register (`r1 == r2`) and `ivMulSym` for distinct operands. -/
def evalSsaOpInterval (B : Box3D) (ivRegs : List FloatInterval) : SsaTapeOp → FloatInterval
  | .const c        => { lo := c, hi := c }
  | .varX           => B.xIv
  | .varY           => B.yIv
  | .varZ           => B.zIv
  | .neg r          => ivNeg (ivRegs.getD r defaultSsaIv)
  | .add r1 r2      => ivAdd (ivRegs.getD r1 defaultSsaIv) (ivRegs.getD r2 defaultSsaIv)
  | .sub r1 r2      => ivSub (ivRegs.getD r1 defaultSsaIv) (ivRegs.getD r2 defaultSsaIv)
  | .mul r1 r2      =>
    if r1 == r2 then
      ivSq (ivRegs.getD r1 defaultSsaIv)
    else
      ivMulSym (ivRegs.getD r1 defaultSsaIv) (ivRegs.getD r2 defaultSsaIv)
  | .minUnion r1 r2 => ivMin (ivRegs.getD r1 defaultSsaIv) (ivRegs.getD r2 defaultSsaIv)
  | .maxInter r1 r2 => ivMax (ivRegs.getD r1 defaultSsaIv) (ivRegs.getD r2 defaultSsaIv)

/-- Stepwise execution of a linear SSA tape `List SsaTapeOp` from an initial register prefix `regs`. -/
def evalSsaTapeRegsAux (x y z : Int) : List Int → List SsaTapeOp → List Int
  | regs, [] => regs
  | regs, op :: rest =>
    let v := evalSsaOpPoint x y z regs op
    evalSsaTapeRegsAux x y z (regs ++ [v]) rest

/-- Execute a linear SSA tape `tape : List SsaTapeOp` at point `(x, y, z)`, returning all SSA registers. -/
def evalSsaTapeRegs (x y z : Int) (tape : List SsaTapeOp) : List Int :=
  evalSsaTapeRegsAux x y z [] tape

/-- Evaluate a linear SSA tape `tape : List SsaTapeOp` at 3D point `(x, y, z)` and read `rootReg`
(defaulting to the final instruction `tape.length - 1`). -/
def evalSsaTape (x y z : Int) (tape : List SsaTapeOp) (rootReg : Nat := tape.length - 1) : Int :=
  (evalSsaTapeRegs x y z tape).getD rootReg 0

/-- Specialize a single `SsaTapeOp` using the interval register bounds `ivRegs`:
rewrites `.minUnion r1 r2` and `.maxInter r1 r2` to single-input `(r1, r1)` or `(r2, r2)` whenever
`ivMinChoice` / `ivMaxChoice` proves one branch strictly dominates across `B`. -/
def pruneSsaOp (ivRegs : List FloatInterval) : SsaTapeOp → SsaTapeOp
  | .minUnion r1 r2 =>
    match ivMinChoice (ivRegs.getD r1 defaultSsaIv) (ivRegs.getD r2 defaultSsaIv) with
    | .left  => .minUnion r1 r1
    | .right => .minUnion r2 r2
    | _      => .minUnion r1 r2
  | .maxInter r1 r2 =>
    match ivMaxChoice (ivRegs.getD r1 defaultSsaIv) (ivRegs.getD r2 defaultSsaIv) with
    | .left  => .maxInter r1 r1
    | .right => .maxInter r2 r2
    | _      => .maxInter r1 r2
  | op => op

/-- Stepwise interval specialization of a linear SSA tape `List SsaTapeOp` over `B : Box3D`. -/
def pruneSsaTapeAux (B : Box3D) : List FloatInterval → List SsaTapeOp → List SsaTapeOp
  | _, [] => []
  | ivRegs, op :: rest =>
    let op' := pruneSsaOp ivRegs op
    let iv  := evalSsaOpInterval B ivRegs op
    op' :: pruneSsaTapeAux B (ivRegs ++ [iv]) rest

/-- Specialize (`prune`) a linear SSA tape `tape : List SsaTapeOp` over 3D bounding box `B : Box3D`. -/
def pruneSsaTapeForBox (B : Box3D) (tape : List SsaTapeOp) : List SsaTapeOp :=
  pruneSsaTapeAux B [] tape

/-- Input register dependencies of an `SsaTapeOp` (for backward liveness analysis). -/
def ssaOpDeps : SsaTapeOp → List Nat
  | .const _ | .varX | .varY | .varZ => []
  | .neg r => [r]
  | .add r1 r2 | .sub r1 r2 | .mul r1 r2 | .minUnion r1 r2 | .maxInter r1 r2 =>
    if r1 == r2 then [r1] else [r1, r2]

/-- Chase single-branch pruned `minUnion r r` / `maxInter r r` forwarding chains backward
from `reg` to the earliest dominating live root register `< reg`. -/
def resolveSsaLiveRoot (tape : List SsaTapeOp) : Nat → Nat → Nat
  | 0, reg => reg
  | fuel + 1, reg =>
    match tape[reg]? with
    | some (.minUnion r1 r2) =>
      if decide (r1 == r2 ∧ r1 < reg) then resolveSsaLiveRoot tape fuel r1 else reg
    | some (.maxInter r1 r2) =>
      if decide (r1 == r2 ∧ r1 < reg) then resolveSsaLiveRoot tape fuel r1 else reg
    | _ => reg

/-- Full backward-liveness register-set sweep from `rootReg` across `tape`. -/
def computeLiveSsaRegs (tape : List SsaTapeOp) (rootReg : Nat) : List Nat :=
  let liveRoot := resolveSsaLiveRoot tape tape.length rootReg
  ((tape.take (liveRoot + 1)).zipIdx.reverse).foldl (fun live (op, idx) =>
    if live.contains idx then
      (ssaOpDeps op).foldl (fun acc d => if acc.contains d then acc else d :: acc) live
    else
      live) [liveRoot]

/-- Check if an `SsaTapeOp` is a single-branch `.minUnion r1 r1` or `.maxInter r1 r1` that
can be aliased directly to an already-compacted register `cr`. -/
def tryAliasSsaOp (regMap : List (Option Nat)) : SsaTapeOp → Option Nat
  | .minUnion r1 r2 => if r1 == r2 then regMap.getD r1 none else none
  | .maxInter r1 r2 => if r1 == r2 then regMap.getD r1 none else none
  | _ => none

/-- Remap the input register indices of `op : SsaTapeOp` through `regMap : List (Option Nat)`. -/
def tryRemapSsaOp (regMap : List (Option Nat)) : SsaTapeOp → Option SsaTapeOp
  | .const c        => some (.const c)
  | .varX           => some .varX
  | .varY           => some .varY
  | .varZ           => some .varZ
  | .neg r          =>
    match regMap.getD r none with
    | some cr => some (.neg cr)
    | none    => none
  | .add r1 r2      =>
    match regMap.getD r1 none, regMap.getD r2 none with
    | some cr1, some cr2 => some (.add cr1 cr2)
    | _, _               => none
  | .sub r1 r2      =>
    match regMap.getD r1 none, regMap.getD r2 none with
    | some cr1, some cr2 => some (.sub cr1 cr2)
    | _, _               => none
  | .mul r1 r2      =>
    match regMap.getD r1 none, regMap.getD r2 none with
    | some cr1, some cr2 => some (.mul cr1 cr2)
    | _, _               => none
  | .minUnion r1 r2 =>
    match regMap.getD r1 none, regMap.getD r2 none with
    | some cr1, some cr2 => some (.minUnion cr1 cr2)
    | _, _               => none
  | .maxInter r1 r2 =>
    match regMap.getD r1 none, regMap.getD r2 none with
    | some cr1, some cr2 => some (.maxInter cr1 cr2)
    | _, _               => none

/-- Single forward-compaction step at instruction index `idx = regMap.length`:
eliminates dead instructions (`!live.contains idx`), forwards single-branch CSG aliases
(`tryAliasSsaOp`), and emits densely renumbered live instructions (`tryRemapSsaOp`). -/
def compactSsaStep
    (live : List Nat) (compacted : List SsaTapeOp) (regMap : List (Option Nat)) (op : SsaTapeOp) :
    List SsaTapeOp × List (Option Nat) :=
  let idx := regMap.length
  if live.contains idx then
    match tryAliasSsaOp regMap op with
    | some cr => (compacted, regMap ++ [some cr])
    | none =>
      match tryRemapSsaOp regMap op with
      | some op' => (compacted ++ [op'], regMap ++ [some compacted.length])
      | none     => (compacted, regMap ++ [none])
  else
    (compacted, regMap ++ [none])

/-- Forward register-remapping compaction pass over a list of SSA instructions. -/
def compactSsaLoop
    (live : List Nat) (compacted : List SsaTapeOp) (regMap : List (Option Nat)) :
    List SsaTapeOp → List SsaTapeOp × List (Option Nat)
  | [] => (compacted, regMap)
  | op :: rest =>
    let step := compactSsaStep live compacted regMap op
    compactSsaLoop live step.1 step.2 rest

/-- Backward-liveness dead-code compaction of a linear SSA tape `tape` from `rootReg`:
1. Resolves single-branch pruned CSG root chains to `liveRoot`,
2. Computes the backward-live register set `live` from `liveRoot`,
3. Eliminates all dead instructions (both before and after `liveRoot`) and single-branch
   `.minUnion r r` / `.maxInter r r` forwarding nodes while densely renumbering registers to
   `0 .. compacted.length - 1`. -/
def compactSsaTape (tape : List SsaTapeOp) (rootReg : Nat) : List SsaTapeOp :=
  let liveRoot := resolveSsaLiveRoot tape tape.length rootReg
  let live := computeLiveSsaRegs tape rootReg
  let prefixTape := tape.take (liveRoot + 1)
  let (compacted, regMap) := compactSsaLoop live [] [] prefixTape
  match regMap.getD liveRoot none with
  | some cr =>
    if decide (0 < compacted.length ∧ cr == compacted.length - 1) then
      compacted
    else
      prefixTape
  | none => prefixTape

/-- Alias for `compactSsaTape` preserving backward compatibility. -/
abbrev compactSsaTapeFull (tape : List SsaTapeOp) (rootReg : Nat) : List SsaTapeOp :=
  compactSsaTape tape rootReg

theorem compactSsaStep_length_le
    (live : List Nat) (compacted : List SsaTapeOp) (regMap : List (Option Nat)) (op : SsaTapeOp) :
    (compactSsaStep live compacted regMap op).1.length ≤ compacted.length + 1 := by
  unfold compactSsaStep
  dsimp only
  split
  · split
    · simp
    · split
      · simp
      · simp
  · simp

theorem compactSsaLoop_length_le
    (live : List Nat) (compacted : List SsaTapeOp) (regMap : List (Option Nat)) (ts : List SsaTapeOp) :
    (compactSsaLoop live compacted regMap ts).1.length ≤ compacted.length + ts.length := by
  induction ts generalizing compacted regMap with
  | nil =>
    dsimp only [compactSsaLoop]
    omega
  | cons op rest ih =>
    dsimp only [compactSsaLoop, List.length_cons]
    have hStep := compactSsaStep_length_le live compacted regMap op
    have hRest := ih (compactSsaStep live compacted regMap op).1 (compactSsaStep live compacted regMap op).2
    omega

/-- **Universal SSA Tape Compaction Length Bound (`compactSsaTape_length_le`)**:
Compacting any linear SSA tape `tape` from any `rootReg` never increases the instruction count. -/
theorem compactSsaTape_length_le (tape : List SsaTapeOp) (rootReg : Nat) :
    (compactSsaTape tape rootReg).length ≤ tape.length := by
  unfold compactSsaTape
  dsimp only
  have hLoop := compactSsaLoop_length_le
    (computeLiveSsaRegs tape rootReg) [] [] (tape.take (resolveSsaLiveRoot tape tape.length rootReg + 1))
  simp only [List.length_nil, Nat.zero_add, List.length_take] at hLoop
  split
  · split
    · omega
    · rw [List.length_take]; omega
  · rw [List.length_take]; omega

/-- **Universal Full Register-Remapping SSA Compaction Length Bound (`compactSsaTapeFull_length_le`)**. -/
theorem compactSsaTapeFull_length_le (tape : List SsaTapeOp) (rootReg : Nat) :
    (compactSsaTapeFull tape rootReg).length ≤ tape.length :=
  compactSsaTape_length_le tape rootReg

/-- Point-to-interval register file enclosure invariant: every register `r` in `regs` is contained
in the corresponding interval `ivRegs[r]`. -/
def SsaRegsEnclosed (regs : List Int) (ivRegs : List FloatInterval) : Prop :=
  ∀ r : Nat, (ivRegs.getD r defaultSsaIv).contains (regs.getD r 0)

theorem ssaRegsEnclosed_nil : SsaRegsEnclosed [] [] := by
  intro r
  simp [List.getD, defaultSsaIv, FloatInterval.contains]

theorem ssaRegsEnclosed_append
    (regs : List Int) (ivRegs : List FloatInterval) (v : Int) (iv : FloatInterval)
    (hLen : regs.length = ivRegs.length)
    (hEnc : SsaRegsEnclosed regs ivRegs)
    (hV : iv.contains v) :
    SsaRegsEnclosed (regs ++ [v]) (ivRegs ++ [iv]) := by
  induction regs generalizing ivRegs with
  | nil =>
    cases ivRegs with
    | nil =>
      intro r
      cases r with
      | zero => exact hV
      | succ r' => exact hEnc (r' + 1)
    | cons _ _ => cases hLen
  | cons a as ih =>
    cases ivRegs with
    | nil => cases hLen
    | cons b bs =>
      intro r
      cases r with
      | zero => exact hEnc 0
      | succ r' =>
        exact ih bs (Nat.succ.inj hLen) (fun k => hEnc (k + 1)) r'

theorem evalSsaOpInterval_contains
    (B : Box3D) (x y z : Int) (regs : List Int) (ivRegs : List FloatInterval) (op : SsaTapeOp)
    (hIn : B.contains x y z) (hEnc : SsaRegsEnclosed regs ivRegs) :
    (evalSsaOpInterval B ivRegs op).contains (evalSsaOpPoint x y z regs op) := by
  cases op with
  | const c =>
    dsimp only [evalSsaOpInterval, evalSsaOpPoint, FloatInterval.contains]
    omega
  | varX => exact hIn.1
  | varY => exact hIn.2.1
  | varZ => exact hIn.2.2
  | neg r =>
    dsimp only [evalSsaOpInterval, evalSsaOpPoint]
    exact ivNeg_contains _ _ (hEnc r)
  | add r1 r2 =>
    have h1 := hEnc r1
    have h2 := hEnc r2
    dsimp only [evalSsaOpInterval, evalSsaOpPoint, ivAdd, FloatInterval.contains] at *
    omega
  | sub r1 r2 =>
    have h1 := hEnc r1
    have h2 := hEnc r2
    dsimp only [evalSsaOpInterval, evalSsaOpPoint, ivSub, FloatInterval.contains] at *
    omega
  | mul r1 r2 =>
    dsimp only [evalSsaOpInterval, evalSsaOpPoint]
    by_cases hEq : r1 = r2
    · subst hEq
      simp only [beq_self_eq_true, ↓reduceIte]
      exact ivSq_contains _ _ (hEnc r1)
    · have hBeq : (r1 == r2) = false := beq_eq_false_iff_ne.mpr hEq
      rw [hBeq]
      exact ivMulSym_contains _ _ _ _ (hEnc r1) (hEnc r2)
  | minUnion r1 r2 =>
    have h1 := hEnc r1
    have h2 := hEnc r2
    dsimp only [evalSsaOpInterval, evalSsaOpPoint, ivMin, FloatInterval.contains] at *
    omega
  | maxInter r1 r2 =>
    have h1 := hEnc r1
    have h2 := hEnc r2
    dsimp only [evalSsaOpInterval, evalSsaOpPoint, ivMax, FloatInterval.contains] at *
    omega

theorem pruneSsaOp_sound
    (x y z : Int) (regs : List Int) (ivRegs : List FloatInterval) (op : SsaTapeOp)
    (hEnc : SsaRegsEnclosed regs ivRegs) :
    evalSsaOpPoint x y z regs (pruneSsaOp ivRegs op) = evalSsaOpPoint x y z regs op := by
  cases op with
  | const _ | varX | varY | varZ | neg _ | add _ _ | sub _ _ | mul _ _ => rfl
  | minUnion r1 r2 =>
    dsimp only [pruneSsaOp, evalSsaOpPoint]
    have h1 := hEnc r1
    have h2 := hEnc r2
    cases hC : ivMinChoice (ivRegs.getD r1 defaultSsaIv) (ivRegs.getD r2 defaultSsaIv) with
    | left =>
      dsimp only [evalSsaOpPoint]
      have hL := ivMinChoice_left_sound _ _ _ _ h1 h2 hC
      omega
    | right =>
      dsimp only [evalSsaOpPoint]
      have hR := ivMinChoice_right_sound _ _ _ _ h1 h2 hC
      omega
    | unknown => rfl
    | both => rfl
  | maxInter r1 r2 =>
    dsimp only [pruneSsaOp, evalSsaOpPoint]
    have h1 := hEnc r1
    have h2 := hEnc r2
    cases hC : ivMaxChoice (ivRegs.getD r1 defaultSsaIv) (ivRegs.getD r2 defaultSsaIv) with
    | left =>
      dsimp only [evalSsaOpPoint]
      have hL := ivMaxChoice_left_sound _ _ _ _ h1 h2 hC
      omega
    | right =>
      dsimp only [evalSsaOpPoint]
      have hR := ivMaxChoice_right_sound _ _ _ _ h1 h2 hC
      omega
    | unknown => rfl
    | both => rfl

theorem pruneSsaTapeAux_regs_eq
    (B : Box3D) (x y z : Int) (hIn : B.contains x y z)
    (tape : List SsaTapeOp) (regs : List Int) (ivRegs : List FloatInterval)
    (hLen : regs.length = ivRegs.length) (hEnc : SsaRegsEnclosed regs ivRegs) :
    evalSsaTapeRegsAux x y z regs (pruneSsaTapeAux B ivRegs tape) =
      evalSsaTapeRegsAux x y z regs tape := by
  induction tape generalizing regs ivRegs with
  | nil => rfl
  | cons op rest ih =>
    dsimp only [pruneSsaTapeAux, evalSsaTapeRegsAux]
    rw [pruneSsaOp_sound x y z regs ivRegs op hEnc]
    have hV := evalSsaOpInterval_contains B x y z regs ivRegs op hIn hEnc
    have hLen' : (regs ++ [evalSsaOpPoint x y z regs op]).length =
        (ivRegs ++ [evalSsaOpInterval B ivRegs op]).length := by
      simp [hLen]
    have hEnc' := ssaRegsEnclosed_append regs ivRegs _ _ hLen hEnc hV
    exact ih (regs ++ [evalSsaOpPoint x y z regs op]) (ivRegs ++ [evalSsaOpInterval B ivRegs op]) hLen' hEnc'

/-- **Universal Linear SSA Tape Interval Pruning Soundness (`pruneSsaTapeForBox_sound`)**:
For every 3D bounding box `B : Box3D`, every point `(x, y, z)` in `B`, every linear SSA tape
`tape : List SsaTapeOp`, and every register index `rootReg : Nat`, `pruneSsaTapeForBox B tape`
evaluates to the exact same value at `(x, y, z)` as `tape`. -/
theorem pruneSsaTapeForBox_sound
    (B : Box3D) (x y z : Int) (tape : List SsaTapeOp) (rootReg : Nat)
    (hIn : B.contains x y z) :
    evalSsaTape x y z (pruneSsaTapeForBox B tape) rootReg =
      evalSsaTape x y z tape rootReg := by
  unfold evalSsaTape evalSsaTapeRegs pruneSsaTapeForBox
  rw [pruneSsaTapeAux_regs_eq B x y z hIn tape [] [] rfl ssaRegsEnclosed_nil]

theorem pruneSsaTapeAux_length (B : Box3D) (ivRegs : List FloatInterval) (tape : List SsaTapeOp) :
    (pruneSsaTapeAux B ivRegs tape).length = tape.length := by
  induction tape generalizing ivRegs with
  | nil => rfl
  | cons op rest ih =>
    dsimp only [pruneSsaTapeAux, List.length_cons]
    rw [ih]

theorem pruneSsaTapeForBox_length (B : Box3D) (tape : List SsaTapeOp) :
    (pruneSsaTapeForBox B tape).length = tape.length :=
  pruneSsaTapeAux_length B [] tape

theorem getD_append_left_int (xs ys : List Int) (r : Nat) (h : r < xs.length) :
    (xs ++ ys).getD r 0 = xs.getD r 0 := by
  induction xs generalizing r with
  | nil => cases h
  | cons a as ih =>
    cases r with
    | zero => rfl
    | succ r' =>
      dsimp only [List.cons_append, List.getD]
      exact ih r' (Nat.lt_of_succ_lt_succ h)

theorem evalSsaTapeRegsAux_length (x y z : Int) (regs : List Int) (ts : List SsaTapeOp) :
    (evalSsaTapeRegsAux x y z regs ts).length = regs.length + ts.length := by
  induction ts generalizing regs with
  | nil => simp [evalSsaTapeRegsAux]
  | cons op rest ih =>
    dsimp only [evalSsaTapeRegsAux]
    rw [ih]
    simp [ Nat.add_assoc, Nat.add_comm 1 ]

theorem evalSsaTapeRegsAux_getD_prefix (x y z : Int) (regs : List Int) (ts : List SsaTapeOp)
    (r : Nat) (h : r < regs.length) :
    (evalSsaTapeRegsAux x y z regs ts).getD r 0 = regs.getD r 0 := by
  induction ts generalizing regs with
  | nil => rfl
  | cons op rest ih =>
    dsimp only [evalSsaTapeRegsAux]
    have h' : r < (regs ++ [evalSsaOpPoint x y z regs op]).length := by
      simp; omega
    rw [ih (regs ++ [evalSsaOpPoint x y z regs op]) h']
    exact getD_append_left_int regs [evalSsaOpPoint x y z regs op] r h

theorem evalSsaTapeRegsAux_take_getD (x y z : Int) (regs : List Int) (ts : List SsaTapeOp)
    (k r : Nat) (hr : r < regs.length + k) :
    (evalSsaTapeRegsAux x y z regs (ts.take k)).getD r 0 =
      (evalSsaTapeRegsAux x y z regs ts).getD r 0 := by
  induction ts generalizing regs k with
  | nil => simp
  | cons op rest ih =>
    cases k with
    | zero =>
      have hr0 : r < regs.length := by omega
      simp only [List.take]
      dsimp only [evalSsaTapeRegsAux]
      have h1 : r < (regs ++ [evalSsaOpPoint x y z regs op]).length := by simp; omega
      rw [evalSsaTapeRegsAux_getD_prefix x y z (regs ++ [evalSsaOpPoint x y z regs op]) rest r h1]
      exact (getD_append_left_int regs [evalSsaOpPoint x y z regs op] r hr0).symm
    | succ k' =>
      simp only [List.take]
      dsimp only [evalSsaTapeRegsAux]
      have hr' : r < (regs ++ [evalSsaOpPoint x y z regs op]).length + k' := by
        simp; omega
      exact ih (regs ++ [evalSsaOpPoint x y z regs op]) k' hr'

theorem getD_snoc_self (regs : List Int) (v : Int) :
    (regs ++ [v]).getD regs.length 0 = v := by
  induction regs with
  | nil => rfl
  | cons a as ih =>
    dsimp only [List.cons_append, List.length_cons, List.getD]
    exact ih

theorem evalSsaTapeRegsAux_getElem (x y z : Int) (regs : List Int) (ts : List SsaTapeOp)
    (idx : Nat) (op : SsaTapeOp) (hElem : ts[idx]? = some op) :
    (evalSsaTapeRegsAux x y z regs ts).getD (regs.length + idx) 0 =
      evalSsaOpPoint x y z (evalSsaTapeRegsAux x y z regs (ts.take idx)) op := by
  induction ts generalizing regs idx with
  | nil => cases hElem
  | cons hd tl ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hElem
      subst hElem
      simp only [List.take, Nat.add_zero]
      dsimp only [evalSsaTapeRegsAux]
      have hLt : regs.length < (regs ++ [evalSsaOpPoint x y z regs hd]).length := by simp
      rw [evalSsaTapeRegsAux_getD_prefix x y z (regs ++ [evalSsaOpPoint x y z regs hd]) tl regs.length hLt]
      exact getD_snoc_self regs (evalSsaOpPoint x y z regs hd)
    | succ idx' =>
      simp only [List.getElem?_cons_succ] at hElem
      simp only [List.take]
      dsimp only [evalSsaTapeRegsAux]
      have hAdd : regs.length + (idx' + 1) = (regs ++ [evalSsaOpPoint x y z regs hd]).length + idx' := by
        simp; omega
      rw [hAdd]
      exact ih (regs ++ [evalSsaOpPoint x y z regs hd]) idx' hElem

theorem resolveSsaLiveRoot_sound
    (x y z : Int) (tape : List SsaTapeOp) (fuel reg : Nat) (hReg : reg < tape.length) :
    let rStar := resolveSsaLiveRoot tape fuel reg
    rStar ≤ reg ∧ rStar < tape.length ∧
    evalSsaTape x y z tape rStar = evalSsaTape x y z tape reg := by
  induction fuel generalizing reg with
  | zero =>
    exact ⟨Nat.le_refl _, hReg, rfl⟩
  | succ f ih =>
    unfold resolveSsaLiveRoot
    cases hOp : tape[reg]? with
    | none =>
      exact ⟨Nat.le_refl _, hReg, rfl⟩
    | some op =>
      cases op with
      | const _ | varX | varY | varZ | neg _ | add _ _ | sub _ _ | mul _ _ =>
        exact ⟨Nat.le_refl _, hReg, rfl⟩
      | minUnion r1 r2 =>
        dsimp only
        by_cases hCond : r1 == r2 ∧ r1 < reg
        · rw [if_pos (decide_eq_true hCond)]
          have hEqR : r1 = r2 := eq_of_beq hCond.1
          have hLt : r1 < reg := hCond.2
          have hR1Lt : r1 < tape.length := Nat.lt_trans hLt hReg
          obtain ⟨hLe, hLtLen, hEval⟩ := ih r1 hR1Lt
          refine ⟨Nat.le_trans hLe (Nat.le_of_lt hLt), hLtLen, ?_⟩
          rw [hEval]
          unfold evalSsaTape evalSsaTapeRegs
          have hStep := evalSsaTapeRegsAux_getElem x y z [] tape reg (.minUnion r1 r2) hOp
          simp only [List.length_nil, Nat.zero_add] at hStep
          rw [hStep]
          dsimp only [evalSsaOpPoint]
          rw [← hEqR]
          have hTake := evalSsaTapeRegsAux_take_getD x y z [] tape reg r1 (by simp [hLt])
          rw [hTake]
          omega
        · rw [if_neg (by simpa [decide_eq_true_iff] using hCond)]
          exact ⟨Nat.le_refl _, hReg, rfl⟩
      | maxInter r1 r2 =>
        dsimp only
        by_cases hCond : r1 == r2 ∧ r1 < reg
        · rw [if_pos (decide_eq_true hCond)]
          have hEqR : r1 = r2 := eq_of_beq hCond.1
          have hLt : r1 < reg := hCond.2
          have hR1Lt : r1 < tape.length := Nat.lt_trans hLt hReg
          obtain ⟨hLe, hLtLen, hEval⟩ := ih r1 hR1Lt
          refine ⟨Nat.le_trans hLe (Nat.le_of_lt hLt), hLtLen, ?_⟩
          rw [hEval]
          unfold evalSsaTape evalSsaTapeRegs
          have hStep := evalSsaTapeRegsAux_getElem x y z [] tape reg (.maxInter r1 r2) hOp
          simp only [List.length_nil, Nat.zero_add] at hStep
          rw [hStep]
          dsimp only [evalSsaOpPoint]
          rw [← hEqR]
          have hTake := evalSsaTapeRegsAux_take_getD x y z [] tape reg r1 (by simp [hLt])
          rw [hTake]
          omega
        · rw [if_neg (by simpa [decide_eq_true_iff] using hCond)]
          exact ⟨Nat.le_refl _, hReg, rfl⟩

theorem evalSsaTapeRegsAux_append (x y z : Int) (regs : List Int) (ts1 ts2 : List SsaTapeOp) :
    evalSsaTapeRegsAux x y z regs (ts1 ++ ts2) =
      evalSsaTapeRegsAux x y z (evalSsaTapeRegsAux x y z regs ts1) ts2 := by
  induction ts1 generalizing regs with
  | nil => rfl
  | cons op rest ih =>
    dsimp only [List.cons_append, evalSsaTapeRegsAux]
    exact ih (regs ++ [evalSsaOpPoint x y z regs op])

theorem getD_append_none_some (regMap : List (Option Nat)) (r cr : Nat)
    (h : (regMap ++ [none]).getD r none = some cr) :
    regMap.getD r none = some cr := by
  induction regMap generalizing r with
  | nil =>
    cases r with
    | zero => cases h
    | succ r' => simp [List.getD] at h
  | cons a as ih =>
    cases r with
    | zero => exact h
    | succ r' =>
      dsimp only [List.cons_append, List.getD] at h ⊢
      exact ih r' h

theorem getD_append_some_iff (regMap : List (Option Nat)) (crNew r cr : Nat)
    (h : (regMap ++ [some crNew]).getD r none = some cr) :
    (r < regMap.length ∧ regMap.getD r none = some cr) ∨ (r = regMap.length ∧ cr = crNew) := by
  induction regMap generalizing r with
  | nil =>
    cases r with
    | zero =>
      change some crNew = some cr at h
      injection h with hEq
      exact Or.inr ⟨rfl, hEq.symm⟩
    | succ r' =>
      simp [List.getD] at h
  | cons a as ih =>
    cases r with
    | zero =>
      exact Or.inl ⟨Nat.zero_lt_succ _, h⟩
    | succ r' =>
      dsimp only [List.cons_append, List.getD, List.length_cons] at h ⊢
      rcases ih r' h with ⟨hLt, hEq⟩ | ⟨hLen, hCr⟩
      · exact Or.inl ⟨Nat.succ_lt_succ hLt, hEq⟩
      · exact Or.inr ⟨by omega, hCr⟩

/-- Simulation invariant relating the uncompacted register file `origRegs`, the compacted
register file `compRegs`, and the register remapping table `regMap`. -/
def SsaRemapValid (origRegs compRegs : List Int) (regMap : List (Option Nat)) : Prop :=
  regMap.length = origRegs.length ∧
  ∀ r cr : Nat, regMap.getD r none = some cr →
    r < origRegs.length ∧ cr < compRegs.length ∧ compRegs.getD cr 0 = origRegs.getD r 0

theorem ssaRemapValid_nil : SsaRemapValid [] [] [] :=
  ⟨rfl, fun r _ h => by simp [List.getD] at h⟩

theorem ssaRemapValid_append_none
    (origRegs compRegs : List Int) (regMap : List (Option Nat)) (v : Int)
    (hValid : SsaRemapValid origRegs compRegs regMap) :
    SsaRemapValid (origRegs ++ [v]) compRegs (regMap ++ [none]) := by
  refine ⟨by simp [hValid.1], fun r cr h => ?_⟩
  have hOld := getD_append_none_some regMap r cr h
  obtain ⟨hrLt, hcrLt, hVal⟩ := hValid.2 r cr hOld
  refine ⟨by simp; omega, hcrLt, ?_⟩
  rw [getD_append_left_int origRegs [v] r hrLt, hVal]

theorem ssaRemapValid_append_alias
    (origRegs compRegs : List Int) (regMap : List (Option Nat)) (v : Int) (crAlias : Nat)
    (hValid : SsaRemapValid origRegs compRegs regMap)
    (hCrLt : crAlias < compRegs.length)
    (hCrVal : compRegs.getD crAlias 0 = v) :
    SsaRemapValid (origRegs ++ [v]) compRegs (regMap ++ [some crAlias]) := by
  refine ⟨by simp [hValid.1], fun r cr h => ?_⟩
  rcases getD_append_some_iff regMap crAlias r cr h with ⟨_, hOld⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hrOrig, hcrLt, hVal⟩ := hValid.2 r cr hOld
    refine ⟨by simp; omega, hcrLt, ?_⟩
    rw [getD_append_left_int origRegs [v] r hrOrig, hVal]
  · rw [hValid.1]
    refine ⟨by simp, hCrLt, ?_⟩
    rw [getD_snoc_self origRegs v, hCrVal]

theorem ssaRemapValid_append_emit
    (origRegs compRegs : List Int) (regMap : List (Option Nat)) (v : Int)
    (hValid : SsaRemapValid origRegs compRegs regMap) :
    SsaRemapValid (origRegs ++ [v]) (compRegs ++ [v]) (regMap ++ [some compRegs.length]) := by
  refine ⟨by simp [hValid.1], fun r cr h => ?_⟩
  rcases getD_append_some_iff regMap compRegs.length r cr h with ⟨_, hOld⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hrOrig, hcrLt, hVal⟩ := hValid.2 r cr hOld
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    rw [getD_append_left_int compRegs [v] cr hcrLt, getD_append_left_int origRegs [v] r hrOrig, hVal]
  · rw [hValid.1]
    refine ⟨by simp, by simp, ?_⟩
    rw [getD_snoc_self compRegs v, getD_snoc_self origRegs v]

theorem tryAliasSsaOp_sound
    (x y z : Int) (origRegs compRegs : List Int) (regMap : List (Option Nat))
    (op : SsaTapeOp) (cr : Nat)
    (hValid : SsaRemapValid origRegs compRegs regMap)
    (hAlias : tryAliasSsaOp regMap op = some cr) :
    cr < compRegs.length ∧ compRegs.getD cr 0 = evalSsaOpPoint x y z origRegs op := by
  cases op with
  | const _ | varX | varY | varZ | neg _ | add _ _ | sub _ _ | mul _ _ =>
    cases hAlias
  | minUnion r1 r2 =>
    dsimp only [tryAliasSsaOp] at hAlias
    by_cases hEq : r1 == r2
    · rw [if_pos hEq] at hAlias
      have hEq' : r1 = r2 := eq_of_beq hEq
      subst hEq'
      obtain ⟨_, hcrLt, hVal⟩ := hValid.2 r1 cr hAlias
      refine ⟨hcrLt, ?_⟩
      dsimp only [evalSsaOpPoint]
      omega
    · rw [if_neg hEq] at hAlias
      cases hAlias
  | maxInter r1 r2 =>
    dsimp only [tryAliasSsaOp] at hAlias
    by_cases hEq : r1 == r2
    · rw [if_pos hEq] at hAlias
      have hEq' : r1 = r2 := eq_of_beq hEq
      subst hEq'
      obtain ⟨_, hcrLt, hVal⟩ := hValid.2 r1 cr hAlias
      refine ⟨hcrLt, ?_⟩
      dsimp only [evalSsaOpPoint]
      omega
    · rw [if_neg hEq] at hAlias
      cases hAlias

theorem tryRemapSsaOp_sound
    (x y z : Int) (origRegs compRegs : List Int) (regMap : List (Option Nat))
    (op op' : SsaTapeOp)
    (hValid : SsaRemapValid origRegs compRegs regMap)
    (hRemap : tryRemapSsaOp regMap op = some op') :
    evalSsaOpPoint x y z compRegs op' = evalSsaOpPoint x y z origRegs op := by
  cases op with
  | const c =>
    simp only [tryRemapSsaOp, Option.some.injEq] at hRemap
    subst hRemap; rfl
  | varX =>
    simp only [tryRemapSsaOp, Option.some.injEq] at hRemap
    subst hRemap; rfl
  | varY =>
    simp only [tryRemapSsaOp, Option.some.injEq] at hRemap
    subst hRemap; rfl
  | varZ =>
    simp only [tryRemapSsaOp, Option.some.injEq] at hRemap
    subst hRemap; rfl
  | neg r =>
    dsimp only [tryRemapSsaOp] at hRemap
    cases hR : regMap.getD r none with
    | none => rw [hR] at hRemap; cases hRemap
    | some cr =>
      rw [hR] at hRemap
      simp only [Option.some.injEq] at hRemap
      subst hRemap
      dsimp only [evalSsaOpPoint]
      rw [(hValid.2 r cr hR).2.2]
  | add r1 r2 =>
    dsimp only [tryRemapSsaOp] at hRemap
    cases hR1 : regMap.getD r1 none with
    | none => rw [hR1] at hRemap; cases hRemap
    | some cr1 =>
      cases hR2 : regMap.getD r2 none with
      | none => rw [hR1, hR2] at hRemap; cases hRemap
      | some cr2 =>
        rw [hR1, hR2] at hRemap
        simp only [Option.some.injEq] at hRemap
        subst hRemap
        dsimp only [evalSsaOpPoint]
        rw [(hValid.2 r1 cr1 hR1).2.2, (hValid.2 r2 cr2 hR2).2.2]
  | sub r1 r2 =>
    dsimp only [tryRemapSsaOp] at hRemap
    cases hR1 : regMap.getD r1 none with
    | none => rw [hR1] at hRemap; cases hRemap
    | some cr1 =>
      cases hR2 : regMap.getD r2 none with
      | none => rw [hR1, hR2] at hRemap; cases hRemap
      | some cr2 =>
        rw [hR1, hR2] at hRemap
        simp only [Option.some.injEq] at hRemap
        subst hRemap
        dsimp only [evalSsaOpPoint]
        rw [(hValid.2 r1 cr1 hR1).2.2, (hValid.2 r2 cr2 hR2).2.2]
  | mul r1 r2 =>
    dsimp only [tryRemapSsaOp] at hRemap
    cases hR1 : regMap.getD r1 none with
    | none => rw [hR1] at hRemap; cases hRemap
    | some cr1 =>
      cases hR2 : regMap.getD r2 none with
      | none => rw [hR1, hR2] at hRemap; cases hRemap
      | some cr2 =>
        rw [hR1, hR2] at hRemap
        simp only [Option.some.injEq] at hRemap
        subst hRemap
        dsimp only [evalSsaOpPoint]
        rw [(hValid.2 r1 cr1 hR1).2.2, (hValid.2 r2 cr2 hR2).2.2]
  | minUnion r1 r2 =>
    dsimp only [tryRemapSsaOp] at hRemap
    cases hR1 : regMap.getD r1 none with
    | none => rw [hR1] at hRemap; cases hRemap
    | some cr1 =>
      cases hR2 : regMap.getD r2 none with
      | none => rw [hR1, hR2] at hRemap; cases hRemap
      | some cr2 =>
        rw [hR1, hR2] at hRemap
        simp only [Option.some.injEq] at hRemap
        subst hRemap
        dsimp only [evalSsaOpPoint]
        rw [(hValid.2 r1 cr1 hR1).2.2, (hValid.2 r2 cr2 hR2).2.2]
  | maxInter r1 r2 =>
    dsimp only [tryRemapSsaOp] at hRemap
    cases hR1 : regMap.getD r1 none with
    | none => rw [hR1] at hRemap; cases hRemap
    | some cr1 =>
      cases hR2 : regMap.getD r2 none with
      | none => rw [hR1, hR2] at hRemap; cases hRemap
      | some cr2 =>
        rw [hR1, hR2] at hRemap
        simp only [Option.some.injEq] at hRemap
        subst hRemap
        dsimp only [evalSsaOpPoint]
        rw [(hValid.2 r1 cr1 hR1).2.2, (hValid.2 r2 cr2 hR2).2.2]

theorem compactSsaStep_sound
    (x y z : Int) (live : List Nat) (compacted : List SsaTapeOp)
    (origRegs : List Int) (regMap : List (Option Nat)) (op : SsaTapeOp)
    (hValid : SsaRemapValid origRegs (evalSsaTapeRegsAux x y z [] compacted) regMap) :
    SsaRemapValid
      (origRegs ++ [evalSsaOpPoint x y z origRegs op])
      (evalSsaTapeRegsAux x y z [] (compactSsaStep live compacted regMap op).1)
      (compactSsaStep live compacted regMap op).2 := by
  unfold compactSsaStep
  dsimp only
  split
  · cases hAlias : tryAliasSsaOp regMap op with
    | some cr =>
      dsimp only
      obtain ⟨hCrLt, hCrVal⟩ :=
        tryAliasSsaOp_sound x y z origRegs (evalSsaTapeRegsAux x y z [] compacted) regMap op cr hValid hAlias
      exact ssaRemapValid_append_alias
        origRegs (evalSsaTapeRegsAux x y z [] compacted) regMap
        (evalSsaOpPoint x y z origRegs op) cr hValid hCrLt hCrVal
    | none =>
      dsimp only
      cases hRemap : tryRemapSsaOp regMap op with
      | some op' =>
        dsimp only
        rw [evalSsaTapeRegsAux_append]
        dsimp only [evalSsaTapeRegsAux]
        rw [tryRemapSsaOp_sound x y z origRegs (evalSsaTapeRegsAux x y z [] compacted) regMap op op' hValid hRemap]
        have hLenComp : (evalSsaTapeRegsAux x y z [] compacted).length = compacted.length := by
          rw [evalSsaTapeRegsAux_length]; simp
        rw [← hLenComp]
        exact ssaRemapValid_append_emit
          origRegs (evalSsaTapeRegsAux x y z [] compacted) regMap
          (evalSsaOpPoint x y z origRegs op) hValid
      | none =>
        dsimp only
        exact ssaRemapValid_append_none
          origRegs (evalSsaTapeRegsAux x y z [] compacted) regMap
          (evalSsaOpPoint x y z origRegs op) hValid
  · exact ssaRemapValid_append_none
      origRegs (evalSsaTapeRegsAux x y z [] compacted) regMap
      (evalSsaOpPoint x y z origRegs op) hValid

theorem compactSsaLoop_sound
    (x y z : Int) (live : List Nat) (compacted : List SsaTapeOp)
    (origRegs : List Int) (regMap : List (Option Nat)) (ts : List SsaTapeOp)
    (hValid : SsaRemapValid origRegs (evalSsaTapeRegsAux x y z [] compacted) regMap) :
    SsaRemapValid
      (evalSsaTapeRegsAux x y z origRegs ts)
      (evalSsaTapeRegsAux x y z [] (compactSsaLoop live compacted regMap ts).1)
      (compactSsaLoop live compacted regMap ts).2 := by
  induction ts generalizing compacted origRegs regMap with
  | nil => exact hValid
  | cons op rest ih =>
    dsimp only [compactSsaLoop, evalSsaTapeRegsAux]
    exact ih
      (compactSsaStep live compacted regMap op).1
      (origRegs ++ [evalSsaOpPoint x y z origRegs op])
      (compactSsaStep live compacted regMap op).2
      (compactSsaStep_sound x y z live compacted origRegs regMap op hValid)

theorem compactSsaTape_eval_eq
    (x y z : Int) (tape : List SsaTapeOp) (rootReg : Nat) (hRoot : rootReg < tape.length) :
    let compacted := compactSsaTape tape rootReg
    evalSsaTape x y z compacted (compacted.length - 1) = evalSsaTape x y z tape rootReg := by
  dsimp only
  obtain ⟨_, hStarLt, hStarEval⟩ :=
    resolveSsaLiveRoot_sound x y z tape tape.length rootReg hRoot
  let rStar := resolveSsaLiveRoot tape tape.length rootReg
  let live := computeLiveSsaRegs tape rootReg
  let prefixTape := tape.take (rStar + 1)
  have hTakeEval : evalSsaTape x y z prefixTape (prefixTape.length - 1) = evalSsaTape x y z tape rootReg := by
    have hPreLen : prefixTape.length - 1 = rStar := by
      dsimp only [prefixTape]
      rw [List.length_take]
      omega
    rw [hPreLen]
    unfold evalSsaTape evalSsaTapeRegs
    dsimp only [prefixTape]
    rw [evalSsaTapeRegsAux_take_getD x y z [] tape (rStar + 1) rStar (by simp)]
    exact hStarEval
  have hLoop := compactSsaLoop_sound x y z live [] [] [] prefixTape ssaRemapValid_nil
  unfold compactSsaTape
  change evalSsaTape x y z
    (match (compactSsaLoop live [] [] prefixTape).2.getD rStar none with
     | some cr =>
       if decide (0 < (compactSsaLoop live [] [] prefixTape).1.length ∧
                  cr == (compactSsaLoop live [] [] prefixTape).1.length - 1) then
         (compactSsaLoop live [] [] prefixTape).1
       else
         prefixTape
     | none => prefixTape)
    ((match (compactSsaLoop live [] [] prefixTape).2.getD rStar none with
     | some cr =>
       if decide (0 < (compactSsaLoop live [] [] prefixTape).1.length ∧
                  cr == (compactSsaLoop live [] [] prefixTape).1.length - 1) then
         (compactSsaLoop live [] [] prefixTape).1
       else
         prefixTape
     | none => prefixTape).length - 1) = evalSsaTape x y z tape rootReg
  cases hGet : (compactSsaLoop live [] [] prefixTape).2.getD rStar none with
  | none =>
    dsimp only
    exact hTakeEval
  | some cr =>
    dsimp only
    by_cases hCond : 0 < (compactSsaLoop live [] [] prefixTape).1.length ∧
        cr == (compactSsaLoop live [] [] prefixTape).1.length - 1
    · rw [if_pos (decide_eq_true hCond)]
      have hCrEq : cr = (compactSsaLoop live [] [] prefixTape).1.length - 1 := eq_of_beq hCond.2
      rw [← hCrEq]
      obtain ⟨_, _, hValEq⟩ := hLoop.2 rStar cr hGet
      unfold evalSsaTape evalSsaTapeRegs
      rw [hValEq]
      dsimp only [prefixTape]
      rw [evalSsaTapeRegsAux_take_getD x y z [] tape (rStar + 1) rStar (by simp)]
      exact hStarEval
    · rw [if_neg (by simpa [decide_eq_true_iff] using hCond)]
      exact hTakeEval

/-- **Combined Linear SSA Tape Interval Pruning & Backward-Liveness Compaction Soundness
(`prune_and_compact_ssa_tape_sound`)**:
For every 3D bounding box `B : Box3D`, every point `(x, y, z)` in `B`, every linear SSA tape
`tape : List SsaTapeOp`, and every `rootReg < tape.length`:
1. Compacting the box-pruned tape `compacted := compactSsaTape (pruneSsaTapeForBox B tape) rootReg`
   never increases the instruction count (`compacted.length ≤ tape.length`), and
2. Evaluating `compacted` at its final output register `compacted.length - 1` produces the **exact**
   same value as evaluating the unpruned `tape` at `rootReg`! -/
theorem prune_and_compact_ssa_tape_sound
    (B : Box3D) (x y z : Int) (tape : List SsaTapeOp) (rootReg : Nat)
    (hIn : B.contains x y z) (hRoot : rootReg < tape.length) :
    let pruned := pruneSsaTapeForBox B tape
    let compacted := compactSsaTape pruned rootReg
    evalSsaTape x y z compacted (compacted.length - 1) = evalSsaTape x y z tape rootReg ∧
    compacted.length ≤ tape.length := by
  dsimp only
  have hLenPruned : (pruneSsaTapeForBox B tape).length = tape.length :=
    pruneSsaTapeForBox_length B tape
  have hRootPruned : rootReg < (pruneSsaTapeForBox B tape).length := by
    omega
  refine ⟨?_, ?_⟩
  · rw [compactSsaTape_eval_eq x y z (pruneSsaTapeForBox B tape) rootReg hRootPruned]
    exact pruneSsaTapeForBox_sound B x y z tape rootReg hIn
  · exact Nat.le_trans (compactSsaTape_length_le (pruneSsaTapeForBox B tape) rootReg) (by omega)

/-- Golden Linear SSA Tape Pruning & Compaction Verification (`golden_ssa_tape_prune_and_compact_verified`):
On a 20-instruction linear SSA stator CSG tape (7 ops for stator core cylinder + 6 ops for
mounting lug + 1 `minUnion` + 5 ops for cooling bore + 1 `maxInter`):
1. Specializing over the center octree box $B_{\text{center}} = [-2, 2]^3$ and running `compactSsaTape`
   compacts the SSA tape from `20` instructions down to `7` instructions,
2. Specializing over the mounting-lug box $B_{\text{lug}} = [14, 16] \times [-1, 1]^2$ (where the right
   branch `reg 12` of `.minUnion 6 12` dominates `reg 6`) eliminates the dead stator core instructions
   `[1, 4, 5, 6]` and dead bore instructions `[13..19]`, compacting from `20` down to `9` instructions, and
3. Specializing over the cooling-bore box $B_{\text{bore}} = [-16, -14] \times [-1, 1]^2$ on a radius-20
   stator housing (where the negated cooling bore `reg 18` in the right branch of `.maxInter 13 18`
   dominates `reg 13`) eliminates both the dead stator core and dead mounting lug branches,
   compacting from `20` down to `10` instructions! -/
theorem golden_ssa_tape_prune_and_compact_verified :
    let box : Box3D :=
      { xIv := { lo := -2, hi := 2 }
      , yIv := { lo := -2, hi := 2 }
      , zIv := { lo := -2, hi := 2 } }
    let ssaStatorTape : List SsaTapeOp :=
      [ -- 0..6: Stator core cylinder x^2 + y^2 - 100 (root at reg 6)
        .varX, .mul 0 0, .varY, .mul 2 2, .add 1 3, .const 100, .sub 4 5,
        -- 7..12: Mounting lug (x - 15)^2 + y^2 - 4 (root at reg 12)
        .const 15, .sub 0 7, .mul 8 8, .add 9 3, .const 4, .sub 10 11,
        -- 13: Union of core (6) and lug (12)
        .minUnion 6 12,
        -- 14..18: Negated cooling bore -((x + 15)^2 + y^2 - 4) (root at reg 18)
        .add 0 7, .mul 14 14, .add 15 3, .sub 16 11, .neg 17,
        -- 19: CSG difference maxInter 13 18
        .maxInter 13 18
      ]
    let pruned := pruneSsaTapeForBox box ssaStatorTape
    let compacted := compactSsaTape pruned 19
    let fullCompacted := compactSsaTapeFull pruned 19
    ssaStatorTape.length = 20 ∧
    compacted.length = 7 ∧
    fullCompacted.length = 7 ∧
    evalSsaTape 1 1 0 compacted (compacted.length - 1) = evalSsaTape 1 1 0 ssaStatorTape 19 := by
  decide +kernel

theorem golden_ssa_tape_right_branch_compaction_verified :
    let boxLug : Box3D :=
      { xIv := { lo := 14, hi := 16 }
      , yIv := { lo := -1, hi := 1 }
      , zIv := { lo := -1, hi := 1 } }
    let boxBore : Box3D :=
      { xIv := { lo := -16, hi := -14 }
      , yIv := { lo := -1, hi := 1 }
      , zIv := { lo := -1, hi := 1 } }
    let ssaStatorTape : List SsaTapeOp :=
      [ .varX, .mul 0 0, .varY, .mul 2 2, .add 1 3, .const 100, .sub 4 5,
        .const 15, .sub 0 7, .mul 8 8, .add 9 3, .const 4, .sub 10 11,
        .minUnion 6 12,
        .add 0 7, .mul 14 14, .add 15 3, .sub 16 11, .neg 17,
        .maxInter 13 18 ]
    let ssaBoreTape : List SsaTapeOp :=
      [ .varX, .mul 0 0, .varY, .mul 2 2, .add 1 3, .const 400, .sub 4 5,
        .const 15, .sub 0 7, .mul 8 8, .add 9 3, .const 4, .sub 10 11,
        .minUnion 6 12,
        .add 0 7, .mul 14 14, .add 15 3, .sub 16 11, .neg 17,
        .maxInter 13 18 ]
    let compactedLug  := compactSsaTape (pruneSsaTapeForBox boxLug ssaStatorTape) 19
    let compactedBore := compactSsaTape (pruneSsaTapeForBox boxBore ssaBoreTape) 19
    compactedLug.length = 9 ∧
    compactedBore.length = 10 ∧
    evalSsaTape 15 0 0 compactedLug (compactedLug.length - 1) = evalSsaTape 15 0 0 ssaStatorTape 19 ∧
    evalSsaTape (-15) 0 0 compactedBore (compactedBore.length - 1) = evalSsaTape (-15) 0 0 ssaBoreTape 19 := by
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

/-! ### 3B. Continuous-Time 5-Axis Swept-Volume Envelope Synthesis & Lipschitz No-Gouge Soundness -/

/-- Translate a 3D `FRepExpr` cutter profile `tool` to waypoint `(wx, wy, wz)` by mapping
$(x, y, z) \mapsto (x - w_x, y - w_y, z - w_z)$. -/
def translateFRep (wx wy wz : Int) : FRepExpr → FRepExpr
  | .const c      => .const c
  | .varX         => .sub .varX (.const wx)
  | .varY         => .sub .varY (.const wy)
  | .varZ         => .sub .varZ (.const wz)
  | .add a b      => .add (translateFRep wx wy wz a) (translateFRep wx wy wz b)
  | .sub a b      => .sub (translateFRep wx wy wz a) (translateFRep wx wy wz b)
  | .scalePos k a => .scalePos k (translateFRep wx wy wz a)
  | .sq a         => .sq (translateFRep wx wy wz a)
  | .csgUnion a b => .csgUnion (translateFRep wx wy wz a) (translateFRep wx wy wz b)
  | .csgInter a b => .csgInter (translateFRep wx wy wz a) (translateFRep wx wy wz b)
  | .csgDiff a b  => .csgDiff (translateFRep wx wy wz a) (translateFRep wx wy wz b)
  | .offset r a   => .offset r (translateFRep wx wy wz a)

/-- Exact pullback identity for `translateFRep`: evaluating `translateFRep wx wy wz tool` at `(x, y, z)`
equals evaluating `tool` at `(x - wx, y - wy, z - wz)`. -/
theorem evalFRepPoint_translateFRep (x y z wx wy wz : Int) (tool : FRepExpr) :
    evalFRepPoint x y z (translateFRep wx wy wz tool) =
      evalFRepPoint (x - wx) (y - wy) (z - wz) tool := by
  induction tool with
  | const _ | varX | varY | varZ => rfl
  | add a b iha ihb =>
    dsimp only [translateFRep, evalFRepPoint]; rw [iha, ihb]
  | sub a b iha ihb =>
    dsimp only [translateFRep, evalFRepPoint]; rw [iha, ihb]
  | scalePos k a iha =>
    dsimp only [translateFRep, evalFRepPoint]; rw [iha]
  | sq a iha =>
    dsimp only [translateFRep, evalFRepPoint]; rw [iha]
  | csgUnion a b iha ihb =>
    dsimp only [translateFRep, evalFRepPoint]; rw [iha, ihb]
  | csgInter a b iha ihb =>
    dsimp only [translateFRep, evalFRepPoint]; rw [iha, ihb]
  | csgDiff a b iha ihb =>
    dsimp only [translateFRep, evalFRepPoint]; rw [iha, ihb]
  | offset r a iha =>
    dsimp only [translateFRep, evalFRepPoint]; rw [iha]

/-- Synthesize a conservative continuous-time 5-axis cutter swept-volume `FRepExpr` from a
tool profile `tool`, a list of 5-axis trajectory waypoints `waypoints`, and inter-sample
Lipschitz segment padding `stepLipschitzPad`:
$$f_{\text{swept}}(p) = \min_{w \in \text{waypoints}} \bigl(f_{\text{tool}}(p - w) - \text{stepLipschitzPad}\bigr).$$ -/
def synthesizeSweptVolume
    (tool : FRepExpr) (waypoints : List (Int × Int × Int)) (stepLipschitzPad : Int) : FRepExpr :=
  match waypoints with
  | [] => .const 1
  | [(wx, wy, wz)] => .offset stepLipschitzPad (translateFRep wx wy wz tool)
  | (wx, wy, wz) :: rest =>
    .csgUnion
      (.offset stepLipschitzPad (translateFRep wx wy wz tool))
      (synthesizeSweptVolume tool rest stepLipschitzPad)

/-- Lemma: At every point `(x, y, z)`, `synthesizeSweptVolume tool waypoints stepLipschitzPad`
is bounded above by the padded tool evaluation at any waypoint `w ∈ waypoints`. -/
theorem evalFRepPoint_synthesizeSweptVolume_le_waypoint
    (x y z : Int) (tool : FRepExpr) (waypoints : List (Int × Int × Int))
    (stepLipschitzPad : Int) (wx wy wz : Int)
    (hMem : (wx, wy, wz) ∈ waypoints) :
    evalFRepPoint x y z (synthesizeSweptVolume tool waypoints stepLipschitzPad) ≤
      evalFRepPoint (x - wx) (y - wy) (z - wz) tool - stepLipschitzPad := by
  induction waypoints with
  | nil => cases hMem
  | cons hd tl ih =>
    rcases hd with ⟨hx, hy, hz⟩
    cases tl with
    | nil =>
      simp only [List.mem_singleton, Prod.mk.injEq] at hMem
      rcases hMem with ⟨rfl, rfl, rfl⟩
      dsimp only [synthesizeSweptVolume, evalFRepPoint]
      rw [evalFRepPoint_translateFRep]
      exact Int.le_refl _
    | cons hd2 tl2 =>
      dsimp only [synthesizeSweptVolume, evalFRepPoint]
      rw [evalFRepPoint_translateFRep]
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with ⟨rfl, rfl, rfl⟩ | hTail
      · omega
      · have hSub := ih (List.mem_cons.mpr hTail)
        omega

/-- **Continuous-Time 5-Axis Swept-Volume No-Gouge Theorem (`continuous_swept_volume_no_gouge_sound`)**:
For any continuous time sample $t \in [0, T]$ where the cutter tip is at `pt_t = (tx, ty, tz)`
within distance `stepDist` of a sampled trajectory waypoint `w = (wx, wy, wz) ∈ waypoints` under
spatial Lipschitz bound `L` (`stepDist * L ≤ stepLipschitzPad` and
`evalFRepPoint (x - wx) (y - wy) (z - wz) tool - evalFRepPoint (x - tx) (y - ty) (z - tz) tool ≤ stepDist * L`),
if the synthesized swept-volume envelope passes `checkVoxelNoGouge B (synthesizeSweptVolume tool waypoints stepLipschitzPad) = true`,
then for every point `(x, y, z) ∈ B`:
1. The continuous cutter at time $t$ is strictly outside `(x, y, z)` (`0 < evalFRepPoint x y z (translateFRep tx ty tz tool)`), and
2. Whenever `(x, y, z)` belongs to the target part (`inSolid x y z fStock`), the continuous cutter
   at time $t$ never gouges `(x, y, z)` (`inSolid x y z (.csgDiff fStock (translateFRep tx ty tz tool))`)! -/
theorem continuous_swept_volume_no_gouge_sound
    (B : Box3D) (fStock tool : FRepExpr)
    (waypoints : List (Int × Int × Int))
    (stepLipschitzPad stepDist L : Int)
    (wx wy wz tx ty tz x y z : Int)
    (hNoGouge : checkVoxelNoGouge B (synthesizeSweptVolume tool waypoints stepLipschitzPad) = true)
    (hInBox : B.contains x y z)
    (hWay : (wx, wy, wz) ∈ waypoints)
    (hPad : stepDist * L ≤ stepLipschitzPad)
    (hLip : evalFRepPoint (x - wx) (y - wy) (z - wz) tool -
              evalFRepPoint (x - tx) (y - ty) (z - tz) tool ≤ stepDist * L) :
    0 < evalFRepPoint x y z (translateFRep tx ty tz tool) ∧
    (inSolid x y z fStock → inSolid x y z (.csgDiff fStock (translateFRep tx ty tz tool))) := by
  unfold checkVoxelNoGouge at hNoGouge
  have hLo : 0 < (evalFRepInterval B (synthesizeSweptVolume tool waypoints stepLipschitzPad)).lo :=
    of_decide_eq_true hNoGouge
  have hSweptPos := frep_octree_prune_exterior_sound B
    (synthesizeSweptVolume tool waypoints stepLipschitzPad) hLo x y z hInBox
  have hWayLe := evalFRepPoint_synthesizeSweptVolume_le_waypoint
    x y z tool waypoints stepLipschitzPad wx wy wz hWay
  rw [evalFRepPoint_translateFRep]
  have hToolPos : 0 < evalFRepPoint (x - tx) (y - ty) (z - tz) tool := by omega
  refine ⟨hToolPos, ?_⟩
  intro hStock
  unfold inSolid at hStock ⊢
  dsimp only [evalFRepPoint]
  rw [evalFRepPoint_translateFRep]
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
