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
     dimensional deflection tolerance, and within its multiphysics performance floor.6. **One F-Rep (`FRepExpr.toTape`, `toTape_eval`)**: the tree compiles to the SSA tape the pruner, the
   compactor and the RTL compiler use, and the two agree at every point.
7. **Region certificates (`kdAll`, `kdAll_sound`)**: the gouge check (`checkDisjoint_sound`) and the
   wall check over a whole cavity (`checkWall_sound`).
8. **Cutters on integer tool axes (`frepBallEndMill`)**: ball and shank as polynomial F-Reps.
9. **Continuous motion (`frepQ_enclosure_sound`, `segment_in_hull`)** and **10. the motion
   certificate as a judge (`checkKdZ_sound`, `checkCamGouge_sound`, `camGougeFormat`)**.
-/
public import Obend.Hardware.Accelerators
public import Obend.Tactic.Tooth
public import Obend.Judge.Class
@[expose] public section

namespace Obend.Hardware.GeometryCAM
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
-- fixture kept (2026-11-04): would delete (a literal tape pruned and compared to its literal result) but cited by tests/metasystem/OpenUsdAndSsaTapeTest.lean:250
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

-- fixture kept (2026-11-04): would delete (a literal tape compacted and compared to its literal result) but cited by tests/metasystem/OpenUsdAndSsaTapeTest.lean:279, tests/metasystem/OpenUsdAndSsaTapeTest.lean:452
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

/-! ### 3C. Self-Certified Forward-Mode Dual-Interval Gradients (`evalFRepGradBox`) & Lipschitz Swept-Volume Synthesis -/

/-- Interval convex hull `[\min(a.lo, b.lo), \max(a.hi, b.hi)]` enclosing subgradients of CSG
`min` (`.csgUnion`) and `max` (`.csgInter`, `.csgDiff`) operations. -/
def ivHull (a b : FloatInterval) : FloatInterval where
  lo := min a.lo b.lo
  hi := max a.hi b.hi

/-- Minimum absolute magnitude $\min_{v \in [a_{\text{lo}}, a_{\text{hi}}]} |v|$ of a `FloatInterval`. -/
def ivMinAbs (a : FloatInterval) : Int :=
  if 0 ≤ a.lo then a.lo
  else if a.hi ≤ 0 then -a.hi
  else 0

/-- Forward-mode 3D dual-interval gradient evaluation (`evalFRepGradBox`):
computes tight interval enclosures $(g_x, g_y, g_z)$ over bounding box `B : Box3D` for the partial
derivatives / discrete secant differences $(\Delta_x e, \Delta_y e, \Delta_z e)$ of any `FRepExpr`. -/
def evalFRepGradBox (B : Box3D) : FRepExpr → FloatInterval × FloatInterval × FloatInterval
  | .const _ =>
    (defaultSsaIv, defaultSsaIv, defaultSsaIv)
  | .varX =>
    ({ lo := 1, hi := 1 }, defaultSsaIv, defaultSsaIv)
  | .varY =>
    (defaultSsaIv, { lo := 1, hi := 1 }, defaultSsaIv)
  | .varZ =>
    (defaultSsaIv, defaultSsaIv, { lo := 1, hi := 1 })
  | .add a b =>
    let ga := evalFRepGradBox B a
    let gb := evalFRepGradBox B b
    (ivAdd ga.1 gb.1, ivAdd ga.2.1 gb.2.1, ivAdd ga.2.2 gb.2.2)
  | .sub a b =>
    let ga := evalFRepGradBox B a
    let gb := evalFRepGradBox B b
    (ivSub ga.1 gb.1, ivSub ga.2.1 gb.2.1, ivSub ga.2.2 gb.2.2)
  | .scalePos k a =>
    let ga := evalFRepGradBox B a
    (ivScalePos k ga.1, ivScalePos k ga.2.1, ivScalePos k ga.2.2)
  | .sq a =>
    let ga := evalFRepGradBox B a
    let twoVal := ivScalePos 2 (evalFRepInterval B a)
    (ivMulSym twoVal ga.1, ivMulSym twoVal ga.2.1, ivMulSym twoVal ga.2.2)
  | .csgUnion a b =>
    let ga := evalFRepGradBox B a
    let gb := evalFRepGradBox B b
    (ivHull ga.1 gb.1, ivHull ga.2.1 gb.2.1, ivHull ga.2.2 gb.2.2)
  | .csgInter a b =>
    let ga := evalFRepGradBox B a
    let gb := evalFRepGradBox B b
    (ivHull ga.1 gb.1, ivHull ga.2.1 gb.2.1, ivHull ga.2.2 gb.2.2)
  | .csgDiff a b =>
    let ga := evalFRepGradBox B a
    let gb := evalFRepGradBox B b
    (ivHull ga.1 (ivNeg gb.1), ivHull ga.2.1 (ivNeg gb.2.1), ivHull ga.2.2 (ivNeg gb.2.2))
  | .offset _ a =>
    evalFRepGradBox B a

/-- Self-certified $L_\infty \to L_1$ Lipschitz upper bound $|g_x|_{\max} + |g_y|_{\max} + |g_z|_{\max}$
derived directly from `evalFRepGradBox B e` without any unchecked caller-supplied parameter. -/
def computeCertifiedLipschitzBox (B : Box3D) (e : FRepExpr) : Nat :=
  let g := evalFRepGradBox B e
  (ivAbsBound g.1 + ivAbsBound g.2.1 + ivAbsBound g.2.2).toNat

/-- Alias for `computeCertifiedLipschitzBox`. -/
abbrev computeCertifiedLipschitzBound (B : Box3D) (e : FRepExpr) : Nat :=
  computeCertifiedLipschitzBox B e

/-- Lower bound on the $L_1$ gradient magnitude $|g_x|_{\min} + |g_y|_{\min} + |g_z|_{\min}$ over `B`. -/
def computeCertifiedGradMinBox (B : Box3D) (e : FRepExpr) : Nat :=
  let g := evalFRepGradBox B e
  (ivMinAbs g.1 + ivMinAbs g.2.1 + ivMinAbs g.2.2).toNat

/-- 3D $L_\infty$ (Chebyshev) distance $\|p - q\|_\infty = \max(|x_1 - x_2|, |y_1 - y_2|, |z_1 - z_2|)$. -/
def linfDist3D (p q : Int × Int × Int) : Int :=
  let (x1, y1, z1) := p
  let (x2, y2, z2) := q
  max (max (frepIntAbs (x1 - x2)) (frepIntAbs (y1 - y2))) (frepIntAbs (z1 - z2))

theorem ivAbsBound_nonneg (a : FloatInterval) : 0 ≤ ivAbsBound a := by
  unfold ivAbsBound
  have h1 := (frepIntAbs_bounds a.lo).1
  have h2 := (frepIntAbs_bounds a.hi).1
  omega

theorem ivAbsBound_bounds (a : FloatInterval) :
    -ivAbsBound a ≤ a.lo ∧ a.lo ≤ ivAbsBound a ∧
    -ivAbsBound a ≤ a.hi ∧ a.hi ≤ ivAbsBound a := by
  unfold ivAbsBound
  have h1 := frepIntAbs_bounds a.lo
  have h2 := frepIntAbs_bounds a.hi
  omega

theorem ivAbsBound_of_contains (a : FloatInterval) (v : Int) (h : a.contains v) :
    -ivAbsBound a ≤ v ∧ v ≤ ivAbsBound a := by
  dsimp only [FloatInterval.contains] at h
  have hb := ivAbsBound_bounds a
  omega

theorem ivScalePos_two_contains_add (a : FloatInterval) (v1 v2 : Int)
    (h1 : a.contains v1) (h2 : a.contains v2) :
    (ivScalePos 2 a).contains (v1 + v2) := by
  dsimp only [ivScalePos, FloatInterval.contains] at *
  change 2 * a.lo ≤ v1 + v2 ∧ v1 + v2 ≤ 2 * a.hi
  omega

theorem int_sq_sub_sq (v1 v2 : Int) :
    v1 * v1 - v2 * v2 = (v1 + v2) * (v1 - v2) := by
  rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm v2 v1]
  omega

theorem ivAdd_secant_encloses (ga gb : FloatInterval) (dx dfa dfb : Int)
    (ha : ga.lo * dx ≤ dfa ∧ dfa ≤ ga.hi * dx)
    (hb : gb.lo * dx ≤ dfb ∧ dfb ≤ gb.hi * dx) :
    (ivAdd ga gb).lo * dx ≤ dfa + dfb ∧ dfa + dfb ≤ (ivAdd ga gb).hi * dx := by
  dsimp only [ivAdd]
  rw [Int.add_mul, Int.add_mul]
  omega

theorem ivSub_secant_encloses (ga gb : FloatInterval) (dx dfa dfb : Int)
    (ha : ga.lo * dx ≤ dfa ∧ dfa ≤ ga.hi * dx)
    (hb : gb.lo * dx ≤ dfb ∧ dfb ≤ gb.hi * dx) :
    (ivSub ga gb).lo * dx ≤ dfa - dfb ∧ dfa - dfb ≤ (ivSub ga gb).hi * dx := by
  dsimp only [ivSub]
  rw [Int.sub_mul, Int.sub_mul]
  omega

theorem ivScalePos_secant_encloses (k : Nat) (ga : FloatInterval) (dx dfa : Int)
    (ha : ga.lo * dx ≤ dfa ∧ dfa ≤ ga.hi * dx) :
    (ivScalePos k ga).lo * dx ≤ Int.ofNat k * dfa ∧
    Int.ofNat k * dfa ≤ (ivScalePos k ga).hi * dx := by
  dsimp only [ivScalePos]
  have hk : (0 : Int) ≤ Int.ofNat k := Int.natCast_nonneg k
  have hLo := int_mul_le_mul_of_nonneg_left (ga.lo * dx) dfa (Int.ofNat k) ha.1 hk
  have hHi := int_mul_le_mul_of_nonneg_left dfa (ga.hi * dx) (Int.ofNat k) ha.2 hk
  rw [← Int.mul_assoc (Int.ofNat k) ga.lo dx] at hLo
  rw [← Int.mul_assoc (Int.ofNat k) ga.hi dx] at hHi
  exact ⟨hLo, hHi⟩

theorem ivMulSym_secant_encloses
    (ivA ga : FloatInterval) (dx v1 v2 : Int)
    (hDx : 0 ≤ dx)
    (hv1 : ivA.contains v1) (hv2 : ivA.contains v2)
    (ha : ga.lo * dx ≤ v1 - v2 ∧ v1 - v2 ≤ ga.hi * dx) :
    (ivMulSym (ivScalePos 2 ivA) ga).lo * dx ≤ v1 * v1 - v2 * v2 ∧
    v1 * v1 - v2 * v2 ≤ (ivMulSym (ivScalePos 2 ivA) ga).hi * dx := by
  dsimp only [ivMulSym]
  have hSumIn := ivScalePos_two_contains_add ivA v1 v2 hv1 hv2
  have hSumBnd := ivAbsBound_of_contains (ivScalePos 2 ivA) (v1 + v2) hSumIn
  have hGaBnd := ivAbsBound_bounds ga
  have hLoMul : (-ivAbsBound ga) * dx ≤ ga.lo * dx :=
    int_mul_le_mul_of_nonneg_right (-ivAbsBound ga) ga.lo dx hGaBnd.1 hDx
  have hHiMul : ga.hi * dx ≤ ivAbsBound ga * dx :=
    int_mul_le_mul_of_nonneg_right ga.hi (ivAbsBound ga) dx hGaBnd.2.2.2 hDx
  rw [Int.neg_mul] at hLoMul
  have hDiffBnd : -(ivAbsBound ga * dx) ≤ v1 - v2 ∧ v1 - v2 ≤ ivAbsBound ga * dx := by omega
  have hR1 : 0 ≤ ivAbsBound (ivScalePos 2 ivA) := ivAbsBound_nonneg _
  have hR2 : 0 ≤ ivAbsBound ga * dx := by
    have := int_mul_le_mul_of_nonneg_right 0 (ivAbsBound ga) dx (ivAbsBound_nonneg ga) hDx
    omega
  have hProd := frep_abs_mul_bound (v1 + v2) (v1 - v2)
    (ivAbsBound (ivScalePos 2 ivA)) (ivAbsBound ga * dx) hR1 hR2 hSumBnd hDiffBnd
  rw [← int_sq_sub_sq v1 v2, ← Int.mul_assoc, ← Int.neg_mul] at hProd
  exact hProd

theorem ivHull_min_secant_encloses (ga gb : FloatInterval) (dx a1 a2 b1 b2 : Int)
    (hDx : 0 ≤ dx)
    (ha : ga.lo * dx ≤ a1 - a2 ∧ a1 - a2 ≤ ga.hi * dx)
    (hb : gb.lo * dx ≤ b1 - b2 ∧ b1 - b2 ≤ gb.hi * dx) :
    (ivHull ga gb).lo * dx ≤ min a1 b1 - min a2 b2 ∧
    min a1 b1 - min a2 b2 ≤ (ivHull ga gb).hi * dx := by
  dsimp only [ivHull]
  have hLoA : min ga.lo gb.lo * dx ≤ ga.lo * dx :=
    int_mul_le_mul_of_nonneg_right (min ga.lo gb.lo) ga.lo dx (by omega) hDx
  have hLoB : min ga.lo gb.lo * dx ≤ gb.lo * dx :=
    int_mul_le_mul_of_nonneg_right (min ga.lo gb.lo) gb.lo dx (by omega) hDx
  have hHiA : ga.hi * dx ≤ max ga.hi gb.hi * dx :=
    int_mul_le_mul_of_nonneg_right ga.hi (max ga.hi gb.hi) dx (by omega) hDx
  have hHiB : gb.hi * dx ≤ max ga.hi gb.hi * dx :=
    int_mul_le_mul_of_nonneg_right gb.hi (max ga.hi gb.hi) dx (by omega) hDx
  omega

theorem ivHull_max_secant_encloses (ga gb : FloatInterval) (dx a1 a2 b1 b2 : Int)
    (hDx : 0 ≤ dx)
    (ha : ga.lo * dx ≤ a1 - a2 ∧ a1 - a2 ≤ ga.hi * dx)
    (hb : gb.lo * dx ≤ b1 - b2 ∧ b1 - b2 ≤ gb.hi * dx) :
    (ivHull ga gb).lo * dx ≤ max a1 b1 - max a2 b2 ∧
    max a1 b1 - max a2 b2 ≤ (ivHull ga gb).hi * dx := by
  dsimp only [ivHull]
  have hLoA : min ga.lo gb.lo * dx ≤ ga.lo * dx :=
    int_mul_le_mul_of_nonneg_right (min ga.lo gb.lo) ga.lo dx (by omega) hDx
  have hLoB : min ga.lo gb.lo * dx ≤ gb.lo * dx :=
    int_mul_le_mul_of_nonneg_right (min ga.lo gb.lo) gb.lo dx (by omega) hDx
  have hHiA : ga.hi * dx ≤ max ga.hi gb.hi * dx :=
    int_mul_le_mul_of_nonneg_right ga.hi (max ga.hi gb.hi) dx (by omega) hDx
  have hHiB : gb.hi * dx ≤ max ga.hi gb.hi * dx :=
    int_mul_le_mul_of_nonneg_right gb.hi (max ga.hi gb.hi) dx (by omega) hDx
  omega

theorem ivNeg_secant_encloses (gb : FloatInterval) (dx b1 b2 : Int)
    (hb : gb.lo * dx ≤ b1 - b2 ∧ b1 - b2 ≤ gb.hi * dx) :
    (ivNeg gb).lo * dx ≤ (-b1) - (-b2) ∧ (-b1) - (-b2) ≤ (ivNeg gb).hi * dx := by
  dsimp only [ivNeg]
  rw [Int.neg_mul, Int.neg_mul]
  omega

/-- Directional secant enclosure along $X$ over bounding box `B`. -/
theorem evalFRepGradBox_secant_x
    (B : Box3D) (x1 x2 y z : Int) (e : FRepExpr)
    (hx1 : B.xIv.contains x1) (hx2 : B.xIv.contains x2)
    (hy : B.yIv.contains y) (hz : B.zIv.contains z)
    (hLe : x2 ≤ x1) :
    let gx := (evalFRepGradBox B e).1
    let df := evalFRepPoint x1 y z e - evalFRepPoint x2 y z e
    gx.lo * (x1 - x2) ≤ df ∧ df ≤ gx.hi * (x1 - x2) := by
  have hDx : 0 ≤ x1 - x2 := by omega
  induction e with
  | const c =>
    dsimp only [evalFRepGradBox, defaultSsaIv, evalFRepPoint]; omega
  | varX =>
    dsimp only [evalFRepGradBox, evalFRepPoint]; omega
  | varY =>
    dsimp only [evalFRepGradBox, defaultSsaIv, evalFRepPoint]; omega
  | varZ =>
    dsimp only [evalFRepGradBox, defaultSsaIv, evalFRepPoint]; omega
  | add a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    have h := ivAdd_secant_encloses _ _ (x1 - x2) _ _ iha ihb
    omega
  | sub a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    have h := ivSub_secant_encloses _ _ (x1 - x2) _ _ iha ihb
    omega
  | scalePos k a iha =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    rw [← Int.mul_sub]
    exact ivScalePos_secant_encloses k _ (x1 - x2) _ iha
  | sq a iha =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivMulSym_secant_encloses (evalFRepInterval B a) (evalFRepGradBox B a).1 (x1 - x2)
      (evalFRepPoint x1 y z a) (evalFRepPoint x2 y z a) hDx
      (frep_interval_enclosure_sound B x1 y z a ⟨hx1, hy, hz⟩)
      (frep_interval_enclosure_sound B x2 y z a ⟨hx2, hy, hz⟩) iha
  | csgUnion a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivHull_min_secant_encloses _ _ (x1 - x2) _ _ _ _ hDx iha ihb
  | csgInter a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivHull_max_secant_encloses _ _ (x1 - x2) _ _ _ _ hDx iha ihb
  | csgDiff a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivHull_max_secant_encloses _ _ (x1 - x2) _ _ _ _ hDx iha
      (ivNeg_secant_encloses _ (x1 - x2) _ _ ihb)
  | offset r a iha =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    omega

/-- Directional secant enclosure along $Y$ over bounding box `B`. -/
theorem evalFRepGradBox_secant_y
    (B : Box3D) (x y1 y2 z : Int) (e : FRepExpr)
    (hx : B.xIv.contains x)
    (hy1 : B.yIv.contains y1) (hy2 : B.yIv.contains y2)
    (hz : B.zIv.contains z)
    (hLe : y2 ≤ y1) :
    let gy := (evalFRepGradBox B e).2.1
    let df := evalFRepPoint x y1 z e - evalFRepPoint x y2 z e
    gy.lo * (y1 - y2) ≤ df ∧ df ≤ gy.hi * (y1 - y2) := by
  have hDy : 0 ≤ y1 - y2 := by omega
  induction e with
  | const c =>
    dsimp only [evalFRepGradBox, defaultSsaIv, evalFRepPoint]; omega
  | varX =>
    dsimp only [evalFRepGradBox, defaultSsaIv, evalFRepPoint]; omega
  | varY =>
    dsimp only [evalFRepGradBox, evalFRepPoint]; omega
  | varZ =>
    dsimp only [evalFRepGradBox, defaultSsaIv, evalFRepPoint]; omega
  | add a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    have h := ivAdd_secant_encloses (evalFRepGradBox B a).2.1 (evalFRepGradBox B b).2.1 (y1 - y2) _ _ iha ihb
    omega
  | sub a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    have h := ivSub_secant_encloses (evalFRepGradBox B a).2.1 (evalFRepGradBox B b).2.1 (y1 - y2) _ _ iha ihb
    omega
  | scalePos k a iha =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    rw [← Int.mul_sub]
    exact ivScalePos_secant_encloses k _ (y1 - y2) _ iha
  | sq a iha =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivMulSym_secant_encloses (evalFRepInterval B a) (evalFRepGradBox B a).2.1 (y1 - y2)
      (evalFRepPoint x y1 z a) (evalFRepPoint x y2 z a) hDy
      (frep_interval_enclosure_sound B x y1 z a ⟨hx, hy1, hz⟩)
      (frep_interval_enclosure_sound B x y2 z a ⟨hx, hy2, hz⟩) iha
  | csgUnion a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivHull_min_secant_encloses _ _ (y1 - y2) _ _ _ _ hDy iha ihb
  | csgInter a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivHull_max_secant_encloses _ _ (y1 - y2) _ _ _ _ hDy iha ihb
  | csgDiff a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivHull_max_secant_encloses _ _ (y1 - y2) _ _ _ _ hDy iha
      (ivNeg_secant_encloses _ (y1 - y2) _ _ ihb)
  | offset r a iha =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    omega

/-- Directional secant enclosure along $Z$ over bounding box `B`. -/
theorem evalFRepGradBox_secant_z
    (B : Box3D) (x y z1 z2 : Int) (e : FRepExpr)
    (hx : B.xIv.contains x) (hy : B.yIv.contains y)
    (hz1 : B.zIv.contains z1) (hz2 : B.zIv.contains z2)
    (hLe : z2 ≤ z1) :
    let gz := (evalFRepGradBox B e).2.2
    let df := evalFRepPoint x y z1 e - evalFRepPoint x y z2 e
    gz.lo * (z1 - z2) ≤ df ∧ df ≤ gz.hi * (z1 - z2) := by
  have hDz : 0 ≤ z1 - z2 := by omega
  induction e with
  | const c =>
    dsimp only [evalFRepGradBox, defaultSsaIv, evalFRepPoint]; omega
  | varX =>
    dsimp only [evalFRepGradBox, defaultSsaIv, evalFRepPoint]; omega
  | varY =>
    dsimp only [evalFRepGradBox, defaultSsaIv, evalFRepPoint]; omega
  | varZ =>
    dsimp only [evalFRepGradBox, evalFRepPoint]; omega
  | add a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    have h := ivAdd_secant_encloses (evalFRepGradBox B a).2.2 (evalFRepGradBox B b).2.2 (z1 - z2) _ _ iha ihb
    omega
  | sub a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    have h := ivSub_secant_encloses (evalFRepGradBox B a).2.2 (evalFRepGradBox B b).2.2 (z1 - z2) _ _ iha ihb
    omega
  | scalePos k a iha =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    rw [← Int.mul_sub]
    exact ivScalePos_secant_encloses k _ (z1 - z2) _ iha
  | sq a iha =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivMulSym_secant_encloses (evalFRepInterval B a) (evalFRepGradBox B a).2.2 (z1 - z2)
      (evalFRepPoint x y z1 a) (evalFRepPoint x y z2 a) hDz
      (frep_interval_enclosure_sound B x y z1 a ⟨hx, hy, hz1⟩)
      (frep_interval_enclosure_sound B x y z2 a ⟨hx, hy, hz2⟩) iha
  | csgUnion a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivHull_min_secant_encloses _ _ (z1 - z2) _ _ _ _ hDz iha ihb
  | csgInter a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivHull_max_secant_encloses _ _ (z1 - z2) _ _ _ _ hDz iha ihb
  | csgDiff a b iha ihb =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    exact ivHull_max_secant_encloses _ _ (z1 - z2) _ _ _ _ hDz iha
      (ivNeg_secant_encloses _ (z1 - z2) _ _ ihb)
  | offset r a iha =>
    dsimp only [evalFRepGradBox, evalFRepPoint]
    omega

theorem secant_to_abs_bound (g : FloatInterval) (d df : Int)
    (hDx : 0 ≤ d) (hSec : g.lo * d ≤ df ∧ df ≤ g.hi * d) :
    frepIntAbs df ≤ ivAbsBound g * d := by
  have hBnd := ivAbsBound_bounds g
  have hLo : (-ivAbsBound g) * d ≤ g.lo * d :=
    int_mul_le_mul_of_nonneg_right (-ivAbsBound g) g.lo d hBnd.1 hDx
  have hHi : g.hi * d ≤ ivAbsBound g * d :=
    int_mul_le_mul_of_nonneg_right g.hi (ivAbsBound g) d hBnd.2.2.2 hDx
  rw [Int.neg_mul] at hLo
  unfold frepIntAbs
  omega

theorem evalFRepGradBox_abs_x
    (B : Box3D) (x1 x2 y z : Int) (e : FRepExpr)
    (hx1 : B.xIv.contains x1) (hx2 : B.xIv.contains x2)
    (hy : B.yIv.contains y) (hz : B.zIv.contains z) :
    frepIntAbs (evalFRepPoint x1 y z e - evalFRepPoint x2 y z e) ≤
      ivAbsBound (evalFRepGradBox B e).1 * frepIntAbs (x1 - x2) := by
  by_cases hLe : x2 ≤ x1
  · have hSec := evalFRepGradBox_secant_x B x1 x2 y z e hx1 hx2 hy hz hLe
    have hAbs : frepIntAbs (x1 - x2) = x1 - x2 := by unfold frepIntAbs; omega
    rw [hAbs]
    exact secant_to_abs_bound (evalFRepGradBox B e).1 (x1 - x2) _ (by omega) hSec
  · have hLe' : x1 ≤ x2 := by omega
    have hSec := evalFRepGradBox_secant_x B x2 x1 y z e hx2 hx1 hy hz hLe'
    have hAbsD : frepIntAbs (x1 - x2) = x2 - x1 := by unfold frepIntAbs; omega
    have hAbsF : frepIntAbs (evalFRepPoint x1 y z e - evalFRepPoint x2 y z e) =
        frepIntAbs (evalFRepPoint x2 y z e - evalFRepPoint x1 y z e) := by
      unfold frepIntAbs; omega
    rw [hAbsD, hAbsF]
    exact secant_to_abs_bound (evalFRepGradBox B e).1 (x2 - x1) _ (by omega) hSec

theorem evalFRepGradBox_abs_y
    (B : Box3D) (x y1 y2 z : Int) (e : FRepExpr)
    (hx : B.xIv.contains x)
    (hy1 : B.yIv.contains y1) (hy2 : B.yIv.contains y2)
    (hz : B.zIv.contains z) :
    frepIntAbs (evalFRepPoint x y1 z e - evalFRepPoint x y2 z e) ≤
      ivAbsBound (evalFRepGradBox B e).2.1 * frepIntAbs (y1 - y2) := by
  by_cases hLe : y2 ≤ y1
  · have hSec := evalFRepGradBox_secant_y B x y1 y2 z e hx hy1 hy2 hz hLe
    have hAbs : frepIntAbs (y1 - y2) = y1 - y2 := by unfold frepIntAbs; omega
    rw [hAbs]
    exact secant_to_abs_bound (evalFRepGradBox B e).2.1 (y1 - y2) _ (by omega) hSec
  · have hLe' : y1 ≤ y2 := by omega
    have hSec := evalFRepGradBox_secant_y B x y2 y1 z e hx hy2 hy1 hz hLe'
    have hAbsD : frepIntAbs (y1 - y2) = y2 - y1 := by unfold frepIntAbs; omega
    have hAbsF : frepIntAbs (evalFRepPoint x y1 z e - evalFRepPoint x y2 z e) =
        frepIntAbs (evalFRepPoint x y2 z e - evalFRepPoint x y1 z e) := by
      unfold frepIntAbs; omega
    rw [hAbsD, hAbsF]
    exact secant_to_abs_bound (evalFRepGradBox B e).2.1 (y2 - y1) _ (by omega) hSec

theorem evalFRepGradBox_abs_z
    (B : Box3D) (x y z1 z2 : Int) (e : FRepExpr)
    (hx : B.xIv.contains x) (hy : B.yIv.contains y)
    (hz1 : B.zIv.contains z1) (hz2 : B.zIv.contains z2) :
    frepIntAbs (evalFRepPoint x y z1 e - evalFRepPoint x y z2 e) ≤
      ivAbsBound (evalFRepGradBox B e).2.2 * frepIntAbs (z1 - z2) := by
  by_cases hLe : z2 ≤ z1
  · have hSec := evalFRepGradBox_secant_z B x y z1 z2 e hx hy hz1 hz2 hLe
    have hAbs : frepIntAbs (z1 - z2) = z1 - z2 := by unfold frepIntAbs; omega
    rw [hAbs]
    exact secant_to_abs_bound (evalFRepGradBox B e).2.2 (z1 - z2) _ (by omega) hSec
  · have hLe' : z1 ≤ z2 := by omega
    have hSec := evalFRepGradBox_secant_z B x y z2 z1 e hx hy hz2 hz1 hLe'
    have hAbsD : frepIntAbs (z1 - z2) = z2 - z1 := by unfold frepIntAbs; omega
    have hAbsF : frepIntAbs (evalFRepPoint x y z1 e - evalFRepPoint x y z2 e) =
        frepIntAbs (evalFRepPoint x y z2 e - evalFRepPoint x y z1 e) := by
      unfold frepIntAbs; omega
    rw [hAbsD, hAbsF]
    exact secant_to_abs_bound (evalFRepGradBox B e).2.2 (z2 - z1) _ (by omega) hSec

/-- **Universal 3D F-Rep Dual-Interval Lipschitz Soundness (`evalFRepGradBox_lipschitz_sound`)**:
For every 3D bounding box `B : Box3D`, every `FRepExpr` `e` (including linear, affine, offset, CSG,
and quadratic `.sq` polynomials), and any two points $p = (x_1, y_1, z_1) \in B$ and
$q = (x_2, y_2, z_2) \in B$:
$$|e(p) - e(q)| \le \text{computeCertifiedLipschitzBox}(B, e) \cdot \|p - q\|_\infty.$$ -/
theorem evalFRepGradBox_lipschitz_sound
    (B : Box3D) (e : FRepExpr)
    (x1 y1 z1 x2 y2 z2 : Int)
    (hp : B.contains x1 y1 z1) (hq : B.contains x2 y2 z2) :
    frepIntAbs (evalFRepPoint x1 y1 z1 e - evalFRepPoint x2 y2 z2 e) ≤
      Int.ofNat (computeCertifiedLipschitzBox B e) * linfDist3D (x1, y1, z1) (x2, y2, z2) := by
  have hx := evalFRepGradBox_abs_x B x1 x2 y1 z1 e hp.1 hq.1 hp.2.1 hp.2.2
  have hy := evalFRepGradBox_abs_y B x2 y1 y2 z1 e hq.1 hp.2.1 hq.2.1 hp.2.2
  have hz := evalFRepGradBox_abs_z B x2 y2 z1 z2 e hq.1 hq.2.1 hp.2.2 hq.2.2
  have hGxPos : 0 ≤ ivAbsBound (evalFRepGradBox B e).1 := ivAbsBound_nonneg _
  have hGyPos : 0 ≤ ivAbsBound (evalFRepGradBox B e).2.1 := ivAbsBound_nonneg _
  have hGzPos : 0 ≤ ivAbsBound (evalFRepGradBox B e).2.2 := ivAbsBound_nonneg _
  have hDxLe : frepIntAbs (x1 - x2) ≤ linfDist3D (x1, y1, z1) (x2, y2, z2) := by
    dsimp [linfDist3D]; omega
  have hDyLe : frepIntAbs (y1 - y2) ≤ linfDist3D (x1, y1, z1) (x2, y2, z2) := by
    dsimp [linfDist3D]; omega
  have hDzLe : frepIntAbs (z1 - z2) ≤ linfDist3D (x1, y1, z1) (x2, y2, z2) := by
    dsimp [linfDist3D]; omega
  have hxInf : ivAbsBound (evalFRepGradBox B e).1 * frepIntAbs (x1 - x2) ≤
      ivAbsBound (evalFRepGradBox B e).1 * linfDist3D (x1, y1, z1) (x2, y2, z2) :=
    int_mul_le_mul_of_nonneg_left _ _ _ hDxLe hGxPos
  have hyInf : ivAbsBound (evalFRepGradBox B e).2.1 * frepIntAbs (y1 - y2) ≤
      ivAbsBound (evalFRepGradBox B e).2.1 * linfDist3D (x1, y1, z1) (x2, y2, z2) :=
    int_mul_le_mul_of_nonneg_left _ _ _ hDyLe hGyPos
  have hzInf : ivAbsBound (evalFRepGradBox B e).2.2 * frepIntAbs (z1 - z2) ≤
      ivAbsBound (evalFRepGradBox B e).2.2 * linfDist3D (x1, y1, z1) (x2, y2, z2) :=
    int_mul_le_mul_of_nonneg_left _ _ _ hDzLe hGzPos
  have hTri :
      frepIntAbs (evalFRepPoint x1 y1 z1 e - evalFRepPoint x2 y2 z2 e) ≤
        frepIntAbs (evalFRepPoint x1 y1 z1 e - evalFRepPoint x2 y1 z1 e) +
        frepIntAbs (evalFRepPoint x2 y1 z1 e - evalFRepPoint x2 y2 z1 e) +
        frepIntAbs (evalFRepPoint x2 y2 z1 e - evalFRepPoint x2 y2 z2 e) := by
    unfold frepIntAbs
    omega
  have hL :
      Int.ofNat (computeCertifiedLipschitzBox B e) =
        ivAbsBound (evalFRepGradBox B e).1 +
        ivAbsBound (evalFRepGradBox B e).2.1 +
        ivAbsBound (evalFRepGradBox B e).2.2 := by
    unfold computeCertifiedLipschitzBox
    dsimp only
    exact Int.toNat_of_nonneg (by omega)
  rw [hL, Int.add_mul, Int.add_mul]
  omega

/-- Broken `computeCertifiedLipschitzBox` returning a constant `0` Lipschitz bound. -/
def computeCertifiedLipschitzBoxBroken (_B : Box3D) (_e : FRepExpr) : Nat := 0

#tooth evalFRepGradBox_lipschitz_sound by mutation
  computeCertifiedLipschitzBox := computeCertifiedLipschitzBoxBroken

/-- Positive scaling homogeneity of `frepIntAbs`. -/
theorem frepIntAbs_scalePos (k : Nat) (z : Int) :
    frepIntAbs (Int.ofNat k * z) = Int.ofNat k * frepIntAbs z := by
  unfold frepIntAbs
  have hk : (0 : Int) ≤ Int.ofNat k := Int.natCast_nonneg k
  split
  · rename_i hkz
    split
    · rfl
    · rename_i hz
      have hNegZ : 1 ≤ -z := by omega
      have hMul := int_mul_le_mul_of_nonneg_left 0 (-z) (Int.ofNat k) (by omega) hk
      rw [Int.mul_neg] at hMul
      have hZero : Int.ofNat k * z = 0 := by omega
      by_cases hk0 : k = 0
      · subst hk0; simp
      · have hkPos : (1 : Int) ≤ Int.ofNat k := by
          change (1 : Int) ≤ (k : Int)
          omega
        have hProdPos := int_mul_le_mul_of_nonneg_left 1 (-z) (Int.ofNat k) hNegZ hk
        rw [Int.mul_neg] at hProdPos
        omega
  · rename_i hkz
    split
    · rename_i hz
      have hMul := int_mul_le_mul_of_nonneg_left 0 z (Int.ofNat k) hz hk
      omega
    · rw [Int.mul_neg]

/-- Positive scaling homogeneity of `ivAbsBound`. -/
theorem ivAbsBound_scalePos (k : Nat) (a : FloatInterval) :
    ivAbsBound (ivScalePos k a) = Int.ofNat k * ivAbsBound a := by
  dsimp only [ivAbsBound, ivScalePos]
  rw [frepIntAbs_scalePos, frepIntAbs_scalePos]
  have hk : (0 : Int) ≤ Int.ofNat k := Int.natCast_nonneg k
  by_cases hLe : frepIntAbs a.lo ≤ frepIntAbs a.hi
  · have hMulLe := int_mul_le_mul_of_nonneg_left _ _ (Int.ofNat k) hLe hk
    have hMax1 : max (Int.ofNat k * frepIntAbs a.lo) (Int.ofNat k * frepIntAbs a.hi) =
        Int.ofNat k * frepIntAbs a.hi := by omega
    have hMax2 : max (frepIntAbs a.lo) (frepIntAbs a.hi) = frepIntAbs a.hi := by omega
    rw [hMax1, hMax2]
  · have hLe' : frepIntAbs a.hi ≤ frepIntAbs a.lo := by omega
    have hMulLe := int_mul_le_mul_of_nonneg_left _ _ (Int.ofNat k) hLe' hk
    have hMax1 : max (Int.ofNat k * frepIntAbs a.lo) (Int.ofNat k * frepIntAbs a.hi) =
        Int.ofNat k * frepIntAbs a.lo := by omega
    have hMax2 : max (frepIntAbs a.lo) (frepIntAbs a.hi) = frepIntAbs a.lo := by omega
    rw [hMax1, hMax2]

/-- **Lipschitz Positive-Scaling Homogeneity (`computeCertifiedLipschitzBox_scalePos`)**:
Scaling any `FRepExpr` `e` by `k : Nat` (`.scalePos k e`) scales `computeCertifiedLipschitzBox B`
by `k`:
$$\text{computeCertifiedLipschitzBox}(B,\, k \cdot e) = k \cdot \text{computeCertifiedLipschitzBox}(B,\, e).$$ -/
theorem computeCertifiedLipschitzBox_scalePos (B : Box3D) (k : Nat) (e : FRepExpr) :
    computeCertifiedLipschitzBox B (.scalePos k e) =
      k * computeCertifiedLipschitzBox B e := by
  unfold computeCertifiedLipschitzBox
  dsimp only [evalFRepGradBox]
  rw [ivAbsBound_scalePos, ivAbsBound_scalePos, ivAbsBound_scalePos]
  have hGx : 0 ≤ ivAbsBound (evalFRepGradBox B e).1 := ivAbsBound_nonneg _
  have hGy : 0 ≤ ivAbsBound (evalFRepGradBox B e).2.1 := ivAbsBound_nonneg _
  have hGz : 0 ≤ ivAbsBound (evalFRepGradBox B e).2.2 := ivAbsBound_nonneg _
  have hSumNonneg :
      0 ≤ ivAbsBound (evalFRepGradBox B e).1 +
          ivAbsBound (evalFRepGradBox B e).2.1 +
          ivAbsBound (evalFRepGradBox B e).2.2 := by omega
  have hDist :
      Int.ofNat k * ivAbsBound (evalFRepGradBox B e).1 +
      Int.ofNat k * ivAbsBound (evalFRepGradBox B e).2.1 +
      Int.ofNat k * ivAbsBound (evalFRepGradBox B e).2.2 =
        Int.ofNat k * (ivAbsBound (evalFRepGradBox B e).1 +
                       ivAbsBound (evalFRepGradBox B e).2.1 +
                       ivAbsBound (evalFRepGradBox B e).2.2) := by
    rw [Int.mul_add, Int.mul_add]
  rw [hDist]
  have hMul := Int.toNat_mul (Int.natCast_nonneg k) hSumNonneg
  exact hMul

/-- Self-certified inter-waypoint safety padding derived directly from `computeCertifiedLipschitzBox`
and maximum waypoint step distance `stepDist : Nat`. -/
def computeCertifiedStepPad (B_local : Box3D) (tool : FRepExpr) (stepDist : Nat) : Int :=
  Int.ofNat (computeCertifiedLipschitzBox B_local tool) * Int.ofNat stepDist

/-- **Self-Certified 5-Axis Swept-Volume Envelope Synthesis (`synthesizeCertifiedSweptVolume`)**:
Computes the inter-waypoint Lipschitz safety pad automatically from `computeCertifiedLipschitzBox B_local tool`
and `stepDist : Nat` without accepting an unchecked caller `stepLipschitzPad`. -/
def synthesizeCertifiedSweptVolume
    (B_local : Box3D) (tool : FRepExpr)
    (waypoints : List (Int × Int × Int)) (stepDist : Nat) : FRepExpr :=
  synthesizeSweptVolume tool waypoints (computeCertifiedStepPad B_local tool stepDist)

/-- **Self-Certified Continuous-Time 5-Axis Swept-Volume No-Gouge Theorem
(`synthesizeCertifiedSweptVolume_no_gouge_sound`)**:
Unlike `continuous_swept_volume_no_gouge_sound`, requires **zero caller-supplied Lipschitz bound**
and **zero unproven Lipschitz assumption**: the spatial Lipschitz bound over `B_local` is derived
and certified automatically by `evalFRepGradBox_lipschitz_sound`! -/
theorem synthesizeCertifiedSweptVolume_no_gouge_sound
    (B B_local : Box3D) (fStock tool : FRepExpr)
    (waypoints : List (Int × Int × Int)) (stepDist : Nat)
    (wx wy wz tx ty tz x y z : Int)
    (hNoGouge : checkVoxelNoGouge B (synthesizeCertifiedSweptVolume B_local tool waypoints stepDist) = true)
    (hInBox : B.contains x y z)
    (hWay : (wx, wy, wz) ∈ waypoints)
    (hLocalW : B_local.contains (x - wx) (y - wy) (z - wz))
    (hLocalT : B_local.contains (x - tx) (y - ty) (z - tz))
    (hStep : linfDist3D (x - wx, y - wy, z - wz) (x - tx, y - ty, z - tz) ≤ Int.ofNat stepDist) :
    0 < evalFRepPoint x y z (translateFRep tx ty tz tool) ∧
    (inSolid x y z fStock → inSolid x y z (.csgDiff fStock (translateFRep tx ty tz tool))) := by
  have hLipAbs := evalFRepGradBox_lipschitz_sound B_local tool
    (x - wx) (y - wy) (z - wz) (x - tx) (y - ty) (z - tz) hLocalW hLocalT
  have hAbsBnd := frepIntAbs_bounds
    (evalFRepPoint (x - wx) (y - wy) (z - wz) tool - evalFRepPoint (x - tx) (y - ty) (z - tz) tool)
  have hLNonneg : (0 : Int) ≤ Int.ofNat (computeCertifiedLipschitzBox B_local tool) :=
    Int.natCast_nonneg _
  have hMulStep := int_mul_le_mul_of_nonneg_left
    (linfDist3D (x - wx, y - wy, z - wz) (x - tx, y - ty, z - tz))
    (Int.ofNat stepDist)
    (Int.ofNat (computeCertifiedLipschitzBox B_local tool))
    hStep hLNonneg
  have hComm :
      Int.ofNat (computeCertifiedLipschitzBox B_local tool) * Int.ofNat stepDist =
        Int.ofNat stepDist * Int.ofNat (computeCertifiedLipschitzBox B_local tool) :=
    Int.mul_comm _ _
  exact continuous_swept_volume_no_gouge_sound
    B fStock tool waypoints
    (computeCertifiedStepPad B_local tool stepDist)
    (Int.ofNat stepDist)
    (Int.ofNat (computeCertifiedLipschitzBox B_local tool))
    wx wy wz tx ty tz x y z
    hNoGouge hInBox hWay
    (by unfold computeCertifiedStepPad; omega)
    (by omega)

/-! ## 4. One F-Rep: the tree compiles to the tape (`FRepExpr.toTape`)

The tree (`FRepExpr`) carries the interval, gradient and swept-volume theorems; the tape (`SsaTapeOp`)
carries pruning, compaction and the RTL compiler. Until 2026-11-04 nothing related them, so every
caller wrote its tape by hand beside its tree. `toTapeFrom` is the compiler and `toTape_eval` its
soundness: evaluating the emitted tape at its last register is evaluating the tree. -/

/-- Compile `e` to SSA ops whose registers start at `base` (the length of the register file the ops
run after); the result is in the last register written. -/
def FRepExpr.toTapeFrom (base : Nat) : FRepExpr → List SsaTapeOp
  | .const c => [.const c]
  | .varX => [.varX]
  | .varY => [.varY]
  | .varZ => [.varZ]
  | .add a b =>
    let ta := toTapeFrom base a
    let tb := toTapeFrom (base + ta.length) b
    ta ++ tb ++ [.add (base + ta.length - 1) (base + ta.length + tb.length - 1)]
  | .sub a b =>
    let ta := toTapeFrom base a
    let tb := toTapeFrom (base + ta.length) b
    ta ++ tb ++ [.sub (base + ta.length - 1) (base + ta.length + tb.length - 1)]
  | .scalePos k a =>
    let ta := toTapeFrom base a
    ta ++ [.const (Int.ofNat k), .mul (base + ta.length) (base + ta.length - 1)]
  | .sq a =>
    let ta := toTapeFrom base a
    ta ++ [.mul (base + ta.length - 1) (base + ta.length - 1)]
  | .csgUnion a b =>
    let ta := toTapeFrom base a
    let tb := toTapeFrom (base + ta.length) b
    ta ++ tb ++ [.minUnion (base + ta.length - 1) (base + ta.length + tb.length - 1)]
  | .csgInter a b =>
    let ta := toTapeFrom base a
    let tb := toTapeFrom (base + ta.length) b
    ta ++ tb ++ [.maxInter (base + ta.length - 1) (base + ta.length + tb.length - 1)]
  | .csgDiff a b =>
    let ta := toTapeFrom base a
    let tb := toTapeFrom (base + ta.length) b
    ta ++ tb ++ [.neg (base + ta.length + tb.length - 1),
                 .maxInter (base + ta.length - 1) (base + ta.length + tb.length)]
  | .offset r a =>
    let ta := toTapeFrom base a
    ta ++ [.const r, .sub (base + ta.length - 1) (base + ta.length)]

/-- The tape of `e` on an empty register file. -/
def FRepExpr.toTape (e : FRepExpr) : List SsaTapeOp := e.toTapeFrom 0

theorem FRepExpr.toTapeFrom_length_pos (base : Nat) (e : FRepExpr) : 0 < (e.toTapeFrom base).length := by
  cases e <;> simp [FRepExpr.toTapeFrom] <;> omega

/-- One step of the register file: running `[op]` appends one value. -/
theorem evalSsaTapeRegsAux_singleton (x y z : Int) (regs : List Int) (op : SsaTapeOp) :
    evalSsaTapeRegsAux x y z regs [op] = regs ++ [evalSsaOpPoint x y z regs op] := rfl

/-- Invariant of `toTapeFrom`: run after a register file of length `base`, the ops keep that file
as a prefix, add exactly their own length, and leave `e`'s value in the last register. -/
theorem FRepExpr.toTapeFrom_spec (x y z : Int) (e : FRepExpr) :
    ∀ (regs : List Int),
      let out := evalSsaTapeRegsAux x y z regs (e.toTapeFrom regs.length)
      out.length = regs.length + (e.toTapeFrom regs.length).length ∧
      (∀ r, r < regs.length → out.getD r 0 = regs.getD r 0) ∧
      out.getD (out.length - 1) 0 = evalFRepPoint x y z e := by
  -- The binary cases share one shape: `ta ++ tb ++ tail`.
  have binary :
      ∀ (a b : FRepExpr)
        (iha : ∀ regs : List Int,
          let out := evalSsaTapeRegsAux x y z regs (a.toTapeFrom regs.length)
          out.length = regs.length + (a.toTapeFrom regs.length).length ∧
          (∀ r, r < regs.length → out.getD r 0 = regs.getD r 0) ∧
          out.getD (out.length - 1) 0 = evalFRepPoint x y z a)
        (ihb : ∀ regs : List Int,
          let out := evalSsaTapeRegsAux x y z regs (b.toTapeFrom regs.length)
          out.length = regs.length + (b.toTapeFrom regs.length).length ∧
          (∀ r, r < regs.length → out.getD r 0 = regs.getD r 0) ∧
          out.getD (out.length - 1) 0 = evalFRepPoint x y z b)
        (regs : List Int),
        let ta := a.toTapeFrom regs.length
        let outA := evalSsaTapeRegsAux x y z regs ta
        let tb := b.toTapeFrom (regs.length + ta.length)
        let outB := evalSsaTapeRegsAux x y z outA tb
        outA.length = regs.length + ta.length ∧
        outB.length = regs.length + ta.length + tb.length ∧
        (∀ r, r < regs.length → outB.getD r 0 = regs.getD r 0) ∧
        outB.getD (regs.length + ta.length - 1) 0 = evalFRepPoint x y z a ∧
        outB.getD (regs.length + ta.length + tb.length - 1) 0 = evalFRepPoint x y z b ∧
        0 < ta.length ∧ 0 < tb.length := by
    intro a b iha ihb regs
    dsimp only
    obtain ⟨hA1, hA2, hA3⟩ := iha regs
    have hTa := FRepExpr.toTapeFrom_length_pos regs.length a
    have hLenA : (evalSsaTapeRegsAux x y z regs (a.toTapeFrom regs.length)).length =
        regs.length + (a.toTapeFrom regs.length).length := hA1
    have ihb' := ihb (evalSsaTapeRegsAux x y z regs (a.toTapeFrom regs.length))
    rw [hLenA] at ihb'
    obtain ⟨hB1, hB2, hB3⟩ := ihb'
    have hTb := FRepExpr.toTapeFrom_length_pos (regs.length + (a.toTapeFrom regs.length).length) b
    refine ⟨hA1, ?_, ?_, ?_, ?_, hTa, hTb⟩
    · exact hB1
    · intro r hr
      rw [hB2 r (by omega)]
      exact hA2 r hr
    · rw [hB2 _ (by omega)]
      rw [hA1] at hA3
      exact hA3
    · rw [hB1] at hB3
      exact hB3
  intro regs
  induction e generalizing regs with
  | const c => exact ⟨by simp [FRepExpr.toTapeFrom, evalSsaTapeRegsAux],
      fun r hr => getD_append_left_int _ _ r hr,
      by simp only [FRepExpr.toTapeFrom, evalSsaTapeRegsAux_singleton, List.length_append,
                    List.length_singleton, Nat.add_sub_cancel]
         exact getD_snoc_self _ _⟩
  | varX => exact ⟨by simp [FRepExpr.toTapeFrom, evalSsaTapeRegsAux],
      fun r hr => getD_append_left_int _ _ r hr,
      by simp only [FRepExpr.toTapeFrom, evalSsaTapeRegsAux_singleton, List.length_append,
                    List.length_singleton, Nat.add_sub_cancel]
         exact getD_snoc_self _ _⟩
  | varY => exact ⟨by simp [FRepExpr.toTapeFrom, evalSsaTapeRegsAux],
      fun r hr => getD_append_left_int _ _ r hr,
      by simp only [FRepExpr.toTapeFrom, evalSsaTapeRegsAux_singleton, List.length_append,
                    List.length_singleton, Nat.add_sub_cancel]
         exact getD_snoc_self _ _⟩
  | varZ => exact ⟨by simp [FRepExpr.toTapeFrom, evalSsaTapeRegsAux],
      fun r hr => getD_append_left_int _ _ r hr,
      by simp only [FRepExpr.toTapeFrom, evalSsaTapeRegsAux_singleton, List.length_append,
                    List.length_singleton, Nat.add_sub_cancel]
         exact getD_snoc_self _ _⟩
  | add a b iha ihb | sub a b iha ihb | csgUnion a b iha ihb | csgInter a b iha ihb =>
    obtain ⟨hLA, hLB, hPre, hVa, hVb, hTa, hTb⟩ := binary a b iha ihb regs
    simp only [FRepExpr.toTapeFrom, evalSsaTapeRegsAux_append, evalSsaTapeRegsAux_singleton,
      List.length_append, List.length_singleton]
    refine ⟨by rw [hLB]; omega, fun r hr => ?_, ?_⟩
    · rw [getD_append_left_int _ _ r (by rw [hLB]; omega)]; exact hPre r hr
    · rw [hLB, show regs.length + (a.toTapeFrom regs.length).length +
            (b.toTapeFrom (regs.length + (a.toTapeFrom regs.length).length)).length + 1 - 1 =
          (evalSsaTapeRegsAux x y z (evalSsaTapeRegsAux x y z regs (a.toTapeFrom regs.length))
            (b.toTapeFrom (regs.length + (a.toTapeFrom regs.length).length))).length by rw [hLB]; omega,
          getD_snoc_self]
      simp only [evalSsaOpPoint, evalFRepPoint, hVa, hVb]
  | csgDiff a b iha ihb =>
    obtain ⟨hLA, hLB, hPre, hVa, hVb, hTa, hTb⟩ := binary a b iha ihb regs
    simp only [FRepExpr.toTapeFrom, evalSsaTapeRegsAux_append]
    simp only [show ∀ (rs : List Int) (o1 o2 : SsaTapeOp),
        evalSsaTapeRegsAux x y z rs [o1, o2] =
          (rs ++ [evalSsaOpPoint x y z rs o1]) ++
            [evalSsaOpPoint x y z (rs ++ [evalSsaOpPoint x y z rs o1]) o2] from fun _ _ _ => rfl,
      List.length_append, List.length_singleton, List.length_cons, List.length_nil]
    generalize hOB : evalSsaTapeRegsAux x y z (evalSsaTapeRegsAux x y z regs (a.toTapeFrom regs.length))
        (b.toTapeFrom (regs.length + (a.toTapeFrom regs.length).length)) = outB at *
    refine ⟨by omega, fun r hr => ?_, ?_⟩
    · rw [getD_append_left_int _ _ r (by simp; omega), getD_append_left_int _ _ r (by omega)]
      exact hPre r hr
    · rw [show outB.length + 1 + 1 - 1 = (outB ++ [evalSsaOpPoint x y z outB
            (.neg (regs.length + (a.toTapeFrom regs.length).length +
              (b.toTapeFrom (regs.length + (a.toTapeFrom regs.length).length)).length - 1))]).length by
            simp, getD_snoc_self]
      simp only [evalSsaOpPoint, evalFRepPoint]
      rw [getD_append_left_int _ _ _ (by omega), hVa,
          show regs.length + (a.toTapeFrom regs.length).length +
            (b.toTapeFrom (regs.length + (a.toTapeFrom regs.length).length)).length = outB.length by omega,
          getD_snoc_self]
      rw [show outB.getD (outB.length - 1) 0 = evalFRepPoint x y z b by rw [hLB]; exact hVb]
  | scalePos k a iha =>
    obtain ⟨hA1, hA2, hA3⟩ := iha regs
    simp only [FRepExpr.toTapeFrom, evalSsaTapeRegsAux_append]
    simp only [show ∀ (rs : List Int) (o1 o2 : SsaTapeOp),
        evalSsaTapeRegsAux x y z rs [o1, o2] =
          (rs ++ [evalSsaOpPoint x y z rs o1]) ++
            [evalSsaOpPoint x y z (rs ++ [evalSsaOpPoint x y z rs o1]) o2] from fun _ _ _ => rfl,
      List.length_append, List.length_cons, List.length_nil]
    have hTa := FRepExpr.toTapeFrom_length_pos regs.length a
    generalize hOA : evalSsaTapeRegsAux x y z regs (a.toTapeFrom regs.length) = outA at *
    refine ⟨by omega, fun r hr => ?_, ?_⟩
    · rw [getD_append_left_int _ _ r (by simp; omega), getD_append_left_int _ _ r (by omega)]
      exact hA2 r hr
    · rw [show outA.length + 1 + 1 - 1 = (outA ++ [evalSsaOpPoint x y z outA (.const (Int.ofNat k))]).length by
            simp, getD_snoc_self]
      simp only [evalSsaOpPoint, evalFRepPoint]
      rw [show regs.length + (a.toTapeFrom regs.length).length = outA.length by omega, getD_snoc_self,
          getD_append_left_int _ _ _ (by omega), hA3]
  | sq a iha =>
    obtain ⟨hA1, hA2, hA3⟩ := iha regs
    simp only [FRepExpr.toTapeFrom, evalSsaTapeRegsAux_append, evalSsaTapeRegsAux_singleton,
      List.length_append, List.length_singleton]
    have hTa := FRepExpr.toTapeFrom_length_pos regs.length a
    generalize hOA : evalSsaTapeRegsAux x y z regs (a.toTapeFrom regs.length) = outA at *
    refine ⟨by omega, fun r hr => ?_, ?_⟩
    · rw [getD_append_left_int _ _ r (by omega)]; exact hA2 r hr
    · rw [show outA.length + 1 - 1 = outA.length by omega, getD_snoc_self]
      simp only [evalSsaOpPoint, evalFRepPoint]
      rw [show regs.length + (a.toTapeFrom regs.length).length - 1 = outA.length - 1 by omega, hA3]
  | offset r0 a iha =>
    obtain ⟨hA1, hA2, hA3⟩ := iha regs
    simp only [FRepExpr.toTapeFrom, evalSsaTapeRegsAux_append]
    simp only [show ∀ (rs : List Int) (o1 o2 : SsaTapeOp),
        evalSsaTapeRegsAux x y z rs [o1, o2] =
          (rs ++ [evalSsaOpPoint x y z rs o1]) ++
            [evalSsaOpPoint x y z (rs ++ [evalSsaOpPoint x y z rs o1]) o2] from fun _ _ _ => rfl,
      List.length_append, List.length_cons, List.length_nil]
    have hTa := FRepExpr.toTapeFrom_length_pos regs.length a
    generalize hOA : evalSsaTapeRegsAux x y z regs (a.toTapeFrom regs.length) = outA at *
    refine ⟨by omega, fun r hr => ?_, ?_⟩
    · rw [getD_append_left_int _ _ r (by simp; omega), getD_append_left_int _ _ r (by omega)]
      exact hA2 r hr
    · rw [show outA.length + 1 + 1 - 1 = (outA ++ [evalSsaOpPoint x y z outA (.const r0)]).length by
            simp, getD_snoc_self]
      simp only [evalSsaOpPoint, evalFRepPoint]
      rw [getD_append_left_int _ _ _ (by omega),
          show regs.length + (a.toTapeFrom regs.length).length - 1 = outA.length - 1 by omega, hA3,
          show regs.length + (a.toTapeFrom regs.length).length = outA.length by omega, getD_snoc_self]

/-- **`toTape_eval`**: the compiled tape computes the tree, at every point. -/
theorem FRepExpr.toTape_eval (x y z : Int) (e : FRepExpr) :
    evalSsaTape x y z e.toTape = evalFRepPoint x y z e := by
  have h := FRepExpr.toTapeFrom_spec x y z e []
  dsimp only at h
  obtain ⟨hLen, _, hVal⟩ := h
  unfold evalSsaTape evalSsaTapeRegs FRepExpr.toTape
  simp only [List.length_nil, Nat.zero_add] at hLen
  rw [← hLen]
  exact hVal

/-- Pruning and compaction of a compiled tape keep the tree's value on every point of the box. -/
theorem FRepExpr.toTape_prune_compact_eval (B : Box3D) (x y z : Int) (e : FRepExpr)
    (hIn : B.contains x y z) :
    let compacted := compactSsaTape (pruneSsaTapeForBox B e.toTape) (e.toTape.length - 1)
    evalSsaTape x y z compacted (compacted.length - 1) = evalFRepPoint x y z e ∧
    compacted.length ≤ e.toTape.length := by
  have hPos := FRepExpr.toTapeFrom_length_pos 0 e
  have h := prune_and_compact_ssa_tape_sound B x y z e.toTape (e.toTape.length - 1) hIn
    (by unfold FRepExpr.toTape; omega)
  dsimp only at h ⊢
  refine ⟨?_, h.2⟩
  rw [h.1]
  exact FRepExpr.toTape_eval x y z e

/-! ## 7. Region certificates on a k-d tree of boxes (`kdAll`)

One recursion serves every "for all points of this region" question the CAM tier asks: split the
box across its widest axis until a leaf test settles each piece. `kdAll_sound` turns a leaf test
that is sound on one box into a statement about every lattice point of the root box. -/

/-- Split an interval at its floor midpoint into `[lo, mid]` and `[mid + 1, hi]`. -/
def ivHalves (iv : FloatInterval) : FloatInterval × FloatInterval :=
  let mid := (iv.lo + iv.hi) / 2
  ({ lo := iv.lo, hi := mid }, { lo := mid + 1, hi := iv.hi })

theorem ivHalves_cover (iv : FloatInterval) (v : Int) (h : iv.contains v) :
    (ivHalves iv).1.contains v ∨ (ivHalves iv).2.contains v := by
  unfold ivHalves FloatInterval.contains at *
  dsimp only
  omega

/-- Split a box across its widest axis. -/
def Box3D.halves (B : Box3D) : Box3D × Box3D :=
  let wx := B.xIv.hi - B.xIv.lo
  let wy := B.yIv.hi - B.yIv.lo
  let wz := B.zIv.hi - B.zIv.lo
  if decide (wy ≤ wx) && decide (wz ≤ wx) then
    ({ B with xIv := (ivHalves B.xIv).1 }, { B with xIv := (ivHalves B.xIv).2 })
  else if decide (wz ≤ wy) then
    ({ B with yIv := (ivHalves B.yIv).1 }, { B with yIv := (ivHalves B.yIv).2 })
  else
    ({ B with zIv := (ivHalves B.zIv).1 }, { B with zIv := (ivHalves B.zIv).2 })

theorem Box3D.halves_cover (B : Box3D) (x y z : Int) (h : B.contains x y z) :
    B.halves.1.contains x y z ∨ B.halves.2.contains x y z := by
  obtain ⟨hx, hy, hz⟩ := h
  unfold Box3D.halves
  dsimp only
  split
  · rcases ivHalves_cover B.xIv x hx with h | h
    · exact Or.inl ⟨h, hy, hz⟩
    · exact Or.inr ⟨h, hy, hz⟩
  · split
    · rcases ivHalves_cover B.yIv y hy with h | h
      · exact Or.inl ⟨hx, h, hz⟩
      · exact Or.inr ⟨hx, h, hz⟩
    · rcases ivHalves_cover B.zIv z hz with h | h
      · exact Or.inl ⟨hx, hy, h⟩
      · exact Or.inr ⟨hx, hy, h⟩

/-- A box with an inverted side contains no point. -/
def Box3D.isEmpty (B : Box3D) : Bool :=
  decide (B.xIv.hi < B.xIv.lo) || decide (B.yIv.hi < B.yIv.lo) || decide (B.zIv.hi < B.zIv.lo)

theorem Box3D.not_contains_of_isEmpty (B : Box3D) (h : B.isEmpty = true) (x y z : Int) :
    ¬ B.contains x y z := by
  intro ⟨hx, hy, hz⟩
  unfold FloatInterval.contains at hx hy hz
  simp only [Box3D.isEmpty, Bool.or_eq_true, decide_eq_true_eq] at h
  omega

/-- Decide `leaf` on `B`, or split and decide both halves, to depth `d`; empty boxes pass. -/
def kdAll (leaf : Box3D → Bool) : Nat → Box3D → Bool
  | 0, B => B.isEmpty || leaf B
  | d + 1, B => B.isEmpty || leaf B || (kdAll leaf d B.halves.1 && kdAll leaf d B.halves.2)

/-- **`kdAll_sound`**: a leaf test sound for a property on each box it accepts gives the property on
every lattice point of the root box. -/
theorem kdAll_sound (leaf : Box3D → Bool) (P : Int → Int → Int → Prop)
    (hLeaf : ∀ B x y z, leaf B = true → B.contains x y z → P x y z) :
    ∀ (d : Nat) (B : Box3D) (x y z : Int), kdAll leaf d B = true → B.contains x y z → P x y z := by
  intro d
  induction d with
  | zero =>
    intro B x y z h hIn
    simp only [kdAll, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd hIn (Box3D.not_contains_of_isEmpty B h x y z)
    · exact hLeaf B x y z h hIn
  | succ d ih =>
    intro B x y z h hIn
    simp only [kdAll, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (h | h) | ⟨h1, h2⟩
    · exact absurd hIn (Box3D.not_contains_of_isEmpty B h x y z)
    · exact hLeaf B x y z h hIn
    · rcases Box3D.halves_cover B x y z hIn with hc | hc
      · exact ih _ x y z h1 hc
      · exact ih _ x y z h2 hc

/-- Leaf test for disjointness: on `B`, one of the two solids is certainly absent. -/
def disjointLeaf (f g : FRepExpr) (B : Box3D) : Bool :=
  decide (0 < (evalFRepInterval B f).lo) || decide (0 < (evalFRepInterval B g).lo)

/-- **`checkDisjoint_sound`**: if `kdAll (disjointLeaf f g) d B` holds, no lattice point of `B` is in
both `f` and `g`. With `f` the finished part and `g` the cutter, this is the gouge check. -/
theorem checkDisjoint_sound (f g : FRepExpr) (d : Nat) (B : Box3D)
    (h : kdAll (disjointLeaf f g) d B = true) (x y z : Int) (hIn : B.contains x y z) :
    inSolid x y z f → 0 < evalFRepPoint x y z g := by
  refine kdAll_sound (disjointLeaf f g) (fun x y z => inSolid x y z f → 0 < evalFRepPoint x y z g)
    ?_ d B x y z h hIn
  intro b x y z hl hb hf
  simp only [disjointLeaf, Bool.or_eq_true, decide_eq_true_eq] at hl
  rcases hl with hl | hl
  · have := frep_octree_prune_exterior_sound b f hl x y z hb
    unfold inSolid at hf; omega
  · exact frep_octree_prune_exterior_sound b g hl x y z hb

/-- `B` grown by `tx`, `ty`, `tz` on the two sides of each axis. -/
def Box3D.grow (B : Box3D) (tx ty tz : Nat) : Box3D :=
  { xIv := { lo := B.xIv.lo - tx, hi := B.xIv.hi + tx }
  , yIv := { lo := B.yIv.lo - ty, hi := B.yIv.hi + ty }
  , zIv := { lo := B.zIv.lo - tz, hi := B.zIv.hi + tz } }

/-- `q` is within `tx`, `ty`, `tz` of `p`, axis by axis. -/
def WithinBox (tx ty tz : Nat) (px py pz qx qy qz : Int) : Prop :=
  frepIntAbs (px - qx) ≤ tx ∧ frepIntAbs (py - qy) ≤ ty ∧ frepIntAbs (pz - qz) ≤ tz

theorem Box3D.grow_contains (B : Box3D) (tx ty tz : Nat) (px py pz qx qy qz : Int)
    (hp : B.contains px py pz) (hd : WithinBox tx ty tz px py pz qx qy qz) :
    (B.grow tx ty tz).contains qx qy qz := by
  obtain ⟨hx, hy, hz⟩ := hp
  obtain ⟨h1, h2, h3⟩ := hd
  have hax := frepIntAbs_bounds (px - qx)
  have hay := frepIntAbs_bounds (py - qy)
  have haz := frepIntAbs_bounds (pz - qz)
  unfold FloatInterval.contains at hx hy hz
  unfold Box3D.grow Box3D.contains FloatInterval.contains
  dsimp only
  omega

/-- Leaf test for a wall of `tx`, `ty`, `tz`: on `B` either no cavity point exists, or the whole
box grown by those amounts is inside the outer solid. -/
def wallLeaf (outer inner : FRepExpr) (tx ty tz : Nat) (B : Box3D) : Bool :=
  decide (0 < (evalFRepInterval B inner).lo) ||
    decide ((evalFRepInterval (B.grow tx ty tz) outer).hi ≤ 0)

/-- **`checkWall_sound`**: if `kdAll (wallLeaf outer inner tx ty tz) d B` holds, every lattice point
within `(tx, ty, tz)` of a cavity point of `B` is inside the outer solid: the wall between the cavity
and the outer surface is at least that thick everywhere in `B`, not at one probe point. With
`tz = 0` it is the wall in the XY plane, which is the one a through-bore has. -/
theorem checkWall_sound (outer inner : FRepExpr) (tx ty tz d : Nat) (B : Box3D)
    (h : kdAll (wallLeaf outer inner tx ty tz) d B = true) (px py pz : Int)
    (hIn : B.contains px py pz) (hCav : inSolid px py pz inner) (qx qy qz : Int)
    (hq : WithinBox tx ty tz px py pz qx qy qz) :
    inSolid qx qy qz outer := by
  refine kdAll_sound (wallLeaf outer inner tx ty tz)
    (fun px py pz => inSolid px py pz inner → ∀ qx qy qz : Int,
      WithinBox tx ty tz px py pz qx qy qz → inSolid qx qy qz outer)
    ?_ d B px py pz h hIn hCav qx qy qz hq
  intro b px py pz hl hb hc qx qy qz hd
  simp only [wallLeaf, Bool.or_eq_true, decide_eq_true_eq] at hl
  rcases hl with hl | hl
  · have := frep_octree_prune_exterior_sound b inner hl px py pz hb
    unfold inSolid at hc; omega
  · exact frep_octree_prune_interior_sound (b.grow tx ty tz) outer hl qx qy qz
      (Box3D.grow_contains b tx ty tz px py pz qx qy qz hb hd)

/-- A wall test that ignores the growth: it accepts any box whose own points are inside `outer`. -/
def wallLeafBroken (outer inner : FRepExpr) (_tx _ty _tz : Nat) (B : Box3D) : Bool :=
  decide (0 < (evalFRepInterval B inner).lo) || decide ((evalFRepInterval B outer).hi ≤ 0)

#tooth checkWall_sound by mutation
  wallLeaf := wallLeafBroken

/-! ## 8. Cutters as solids: ball end mill with shank on an integer tool axis

A tool axis is an integer vector `(ux, uy, uz)` whose length `n` is an integer (`(0,0,1)`, `(3,0,4)`
and its quarter turns, …), so every cutter below is a polynomial F-Rep with integer coefficients and
no square roots. CL data in CAM is exactly this (a point and an `IJK` vector); the post turns the
vector into rotary angles for printing only. -/

/-- An integer tool axis with integer length `n` (`n * n = ux² + uy² + uz²`, checked by `valid`). -/
structure ToolAxis where
  ux : Int
  uy : Int
  uz : Int
  n  : Nat
  deriving DecidableEq, Repr

def ToolAxis.valid (u : ToolAxis) : Bool :=
  decide (0 < u.n) && decide ((u.n : Int) * u.n = u.ux * u.ux + u.uy * u.uy + u.uz * u.uz)

/-- `k * e` for any integer `k` (`scalePos` takes a `Nat`). -/
def frepScaleInt (k : Int) (e : FRepExpr) : FRepExpr :=
  if 0 ≤ k then .scalePos k.toNat e else .sub (.const 0) (.scalePos (-k).toNat e)

theorem evalFRepPoint_frepScaleInt (x y z k : Int) (e : FRepExpr) :
    evalFRepPoint x y z (frepScaleInt k e) = k * evalFRepPoint x y z e := by
  unfold frepScaleInt
  split
  · simp only [evalFRepPoint]
    rw [show (Int.ofNat k.toNat) = k from Int.toNat_of_nonneg (by omega)]
  · simp only [evalFRepPoint]
    rw [show (Int.ofNat (-k).toNat) = -k from Int.toNat_of_nonneg (by omega)]
    rw [Int.neg_mul, Int.zero_sub, Int.neg_neg]

/-- Squared distance to `(cx, cy, cz)` minus `r²`: a ball. -/
def frepBall (cx cy cz : Int) (r : Nat) : FRepExpr :=
  .offset ((r : Int) * r)
    (.add (.add (.sq (.sub .varX (.const cx))) (.sq (.sub .varY (.const cy)))) (.sq (.sub .varZ (.const cz))))

/-- `a·e₁ − b·e₂`, dropping a zero term. -/
def frepAxb (a : Int) (e₁ : FRepExpr) (b : Int) (e₂ : FRepExpr) : FRepExpr :=
  if b = 0 then frepScaleInt a e₁
  else if a = 0 then frepScaleInt (-b) e₂
  else .sub (frepScaleInt a e₁) (frepScaleInt b e₂)

/-- `(p - c) · u`, dropping zero terms. -/
def frepAxial (cx cy cz : Int) (u : ToolAxis) : FRepExpr :=
  let qx : FRepExpr := .sub .varX (.const cx)
  let qy : FRepExpr := .sub .varY (.const cy)
  let qz : FRepExpr := .sub .varZ (.const cz)
  if u.ux = 0 ∧ u.uy = 0 then frepScaleInt u.uz qz
  else .add (frepAxb u.ux qx (-u.uy) qy) (frepScaleInt u.uz qz)

/-- Cylinder of radius `r` on the axis through `c` along `u`, from `c` to `len` along the axis:
`|(p-c) × u|² ≤ n² r²` and `0 ≤ (p-c)·u ≤ n·len`. The cross-product form is Lagrange's identity
`|q × u|² = |q|²|u|² − (q·u)²`; it is a sum of squares of linear forms, which interval arithmetic
encloses without the cancellation the difference form suffers. -/
def frepShank (cx cy cz : Int) (u : ToolAxis) (r len : Nat) : FRepExpr :=
  let qx : FRepExpr := .sub .varX (.const cx)
  let qy : FRepExpr := .sub .varY (.const cy)
  let qz : FRepExpr := .sub .varZ (.const cz)
  let d := frepAxial cx cy cz u
  let n2 : Nat := u.n * u.n
  .csgInter
    (.offset ((n2 : Int) * r * r)
      (.add (.add (.sq (frepAxb u.uz qy u.uy qz)) (.sq (frepAxb u.ux qz u.uz qx)))
        (.sq (frepAxb u.uy qx u.ux qy))))
    (.csgInter (.sub (.const 0) d) (.offset ((u.n : Int) * len) d))

/-- Ball end mill of radius `r` with its tip at `(tx, ty, tz)` on axis `u` (ball centre `tip + r·u/n`,
which is an integer point when `n ∣ r·u`), with a straight shank of radius `r` and length `len`
above the centre; holder not modelled. -/
def frepBallEndMill (tx ty tz : Int) (u : ToolAxis) (r len : Nat) : FRepExpr :=
  let cx := tx + (r : Int) * u.ux / u.n
  let cy := ty + (r : Int) * u.uy / u.n
  let cz := tz + (r : Int) * u.uz / u.n
  .csgUnion (frepBall cx cy cz r) (frepShank cx cy cz u r len)

/-- A cutter location: tool tip and tool axis. -/
structure CLPoint where
  x : Int
  y : Int
  z : Int
  axis : ToolAxis
  deriving DecidableEq, Repr

/-- Points `p + round(i·(q - p)/k)` for `i = 1 … k`, `k` the $L_\infty$ distance: a lattice line from
`p` (excluded) to `q` (included) with unit steps. -/
def latticeSegment (p q : Int × Int × Int) : List (Int × Int × Int) :=
  let (px, py, pz) := p
  let (qx, qy, qz) := q
  let k := (linfDist3D p q).toNat
  let rd (a b : Int) (i : Nat) : Int :=
    a + ((2 * (i : Int) * (b - a) + k) / (2 * (k : Int)))
  (List.range k).map fun i => (rd px qx (i + 1), rd py qy (i + 1), rd pz qz (i + 1))

/-- Densify a polyline to unit lattice steps (`latticeSegment` between consecutive points). -/
def densifyPolyline : List (Int × Int × Int) → List (Int × Int × Int)
  | [] => []
  | [p] => [p]
  | p :: q :: rest => p :: (latticeSegment p q).dropLast ++ densifyPolyline (q :: rest)



/-! ## 9. Continuous motion: rational points and rational tool positions

Everything above is about lattice points. Here the solid is evaluated at rational points
(`evalFRepQ`) and enclosed over rational boxes (`frepQ_enclosure_sound`), so a certificate speaks of
every rational point of the part and every rational position of the cutter. A move between two
cutter locations is the segment `c₀ + t (c₁ - c₀)`, `t ∈ [0, 1]`; it lies in the box spanned by its
ends (`segment_in_hull`), and a k-d tree over a part box and a tool-position box (§10) checks
the cutter against the part over their Minkowski difference `B ⊖ H`. The interval of the cutter over `B ⊖ H` is a Lipschitz argument done by the arithmetic:
no gradient bound is supplied, and none is assumed. The reals are not in core Lean; rationals are
dense, and the statement is over every rational time. -/

structure QIv where
  lo : Rat
  hi : Rat
  deriving Repr

def QIv.contains (iv : QIv) (v : Rat) : Prop := iv.lo ≤ v ∧ v ≤ iv.hi

structure QBox where
  x : QIv
  y : QIv
  z : QIv
  deriving Repr

def QBox.contains (B : QBox) (x y z : Rat) : Prop :=
  B.x.contains x ∧ B.y.contains y ∧ B.z.contains z

/-- The solid at a rational point. -/
def evalFRepQ (x y z : Rat) : FRepExpr → Rat
  | .const c      => (c : Rat)
  | .varX         => x
  | .varY         => y
  | .varZ         => z
  | .add a b      => evalFRepQ x y z a + evalFRepQ x y z b
  | .sub a b      => evalFRepQ x y z a - evalFRepQ x y z b
  | .scalePos k a => (k : Rat) * evalFRepQ x y z a
  | .sq a         => evalFRepQ x y z a * evalFRepQ x y z a
  | .csgUnion a b => min (evalFRepQ x y z a) (evalFRepQ x y z b)
  | .csgInter a b => max (evalFRepQ x y z a) (evalFRepQ x y z b)
  | .csgDiff a b  => max (evalFRepQ x y z a) (-evalFRepQ x y z b)
  | .offset r a   => evalFRepQ x y z a - (r : Rat)

def qSq (a : QIv) : QIv :=
  if 0 ≤ a.lo then ⟨a.lo * a.lo, a.hi * a.hi⟩
  else if a.hi ≤ 0 then ⟨a.hi * a.hi, a.lo * a.lo⟩
  else ⟨0, max (a.lo * a.lo) (a.hi * a.hi)⟩

/-- The solid over a rational box, by interval arithmetic. -/
def evalFRepIntervalQ (B : QBox) : FRepExpr → QIv
  | .const c      => ⟨c, c⟩
  | .varX         => B.x
  | .varY         => B.y
  | .varZ         => B.z
  | .add a b      =>
    let ia := evalFRepIntervalQ B a; let ib := evalFRepIntervalQ B b
    ⟨ia.lo + ib.lo, ia.hi + ib.hi⟩
  | .sub a b      =>
    let ia := evalFRepIntervalQ B a; let ib := evalFRepIntervalQ B b
    ⟨ia.lo - ib.hi, ia.hi - ib.lo⟩
  | .scalePos k a =>
    let ia := evalFRepIntervalQ B a
    ⟨(k : Rat) * ia.lo, (k : Rat) * ia.hi⟩
  | .sq a         => qSq (evalFRepIntervalQ B a)
  | .csgUnion a b =>
    let ia := evalFRepIntervalQ B a; let ib := evalFRepIntervalQ B b
    ⟨min ia.lo ib.lo, min ia.hi ib.hi⟩
  | .csgInter a b =>
    let ia := evalFRepIntervalQ B a; let ib := evalFRepIntervalQ B b
    ⟨max ia.lo ib.lo, max ia.hi ib.hi⟩
  | .csgDiff a b  =>
    let ia := evalFRepIntervalQ B a; let ib := evalFRepIntervalQ B b
    ⟨max ia.lo (-ib.hi), max ia.hi (-ib.lo)⟩
  | .offset r a   =>
    let ia := evalFRepIntervalQ B a
    ⟨ia.lo - r, ia.hi - r⟩

theorem rat_sq_le_sq (a b : Rat) (ha : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b := by
  have h1 := Rat.mul_le_mul_of_nonneg_left h ha
  have h2 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_trans ha h)
  exact Rat.le_trans h1 h2

theorem rat_sq_nonneg' (a : Rat) : 0 ≤ a * a := by
  rcases @Rat.le_total 0 a with h | h
  · exact Rat.mul_nonneg h h
  · have := Rat.mul_nonneg (Rat.neg_le_neg h) (Rat.neg_le_neg h)
    rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this
    simpa using this

theorem rat_neg_sq (a : Rat) : (-a) * (-a) = a * a := by
  rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem qSq_contains (a : QIv) (v : Rat) (h : a.contains v) : (qSq a).contains (v * v) := by
  obtain ⟨h1, h2⟩ := h
  unfold qSq
  split
  · rename_i hlo
    exact ⟨rat_sq_le_sq _ _ hlo h1, rat_sq_le_sq _ _ (Rat.le_trans hlo h1) h2⟩
  · split
    · rename_i _ hhi
      have e1 := rat_sq_le_sq (-a.hi) (-v) (by grind) (Rat.neg_le_neg h2)
      have e2 := rat_sq_le_sq (-v) (-a.lo) (by grind) (Rat.neg_le_neg h1)
      rw [rat_neg_sq, rat_neg_sq] at e1 e2
      exact ⟨e1, e2⟩
    · refine ⟨rat_sq_nonneg' v, ?_⟩
      rcases @Rat.le_total 0 v with hv | hv
      · have := rat_sq_le_sq _ _ hv h2
        rw [Rat.max_def]; split <;> grind
      · have := rat_sq_le_sq (-v) (-a.lo) (by grind) (Rat.neg_le_neg h1)
        rw [rat_neg_sq, rat_neg_sq] at this
        rw [Rat.max_def]; split <;> grind

/-- **`frepQ_enclosure_sound`**: the rational interval of the solid over a box contains its value at
every rational point of the box. -/
theorem frepQ_enclosure_sound (B : QBox) (x y z : Rat) (hIn : B.contains x y z) (e : FRepExpr) :
    (evalFRepIntervalQ B e).contains (evalFRepQ x y z e) := by
  induction e with
  | const c => exact ⟨Rat.le_refl, Rat.le_refl⟩
  | varX => exact hIn.1
  | varY => exact hIn.2.1
  | varZ => exact hIn.2.2
  | add a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepQ, QIv.contains] at *; grind
  | sub a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepQ, QIv.contains] at *; grind
  | scalePos k a iha =>
    simp only [evalFRepIntervalQ, evalFRepQ, QIv.contains] at *
    have hk : (0 : Rat) ≤ (k : Rat) := by grind
    exact ⟨Rat.mul_le_mul_of_nonneg_left iha.1 hk, Rat.mul_le_mul_of_nonneg_left iha.2 hk⟩
  | sq a iha =>
    simp only [evalFRepIntervalQ, evalFRepQ]
    exact qSq_contains _ _ iha
  | csgUnion a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepQ, QIv.contains] at *
    rw [Rat.min_def, Rat.min_def, Rat.min_def]; split <;> split <;> split <;> grind
  | csgInter a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepQ, QIv.contains] at *
    rw [Rat.max_def, Rat.max_def, Rat.max_def]; split <;> split <;> split <;> grind
  | csgDiff a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepQ, QIv.contains] at *
    rw [Rat.max_def, Rat.max_def, Rat.max_def]; split <;> split <;> split <;> grind
  | offset r a iha =>
    simp only [evalFRepIntervalQ, evalFRepQ, QIv.contains] at *; grind

def QIv.halves (iv : QIv) : QIv × QIv :=
  let mid := (iv.lo + iv.hi) / 2
  (⟨iv.lo, mid⟩, ⟨mid, iv.hi⟩)

theorem QIv.halves_cover (iv : QIv) (v : Rat) (h : iv.contains v) :
    iv.halves.1.contains v ∨ iv.halves.2.contains v := by
  unfold QIv.halves QIv.contains at *
  dsimp only
  rcases @Rat.le_total v ((iv.lo + iv.hi) / 2) with hm | hm
  · exact Or.inl ⟨h.1, hm⟩
  · exact Or.inr ⟨hm, h.2⟩

def QIv.width (iv : QIv) : Rat := iv.hi - iv.lo

def QBox.width (B : QBox) : Rat := max B.x.width (max B.y.width B.z.width)

/-- Split a rational box across its widest axis. -/
def QBox.halves (B : QBox) : QBox × QBox :=
  if B.y.width ≤ B.x.width ∧ B.z.width ≤ B.x.width then
    ({ B with x := B.x.halves.1 }, { B with x := B.x.halves.2 })
  else if B.z.width ≤ B.y.width then
    ({ B with y := B.y.halves.1 }, { B with y := B.y.halves.2 })
  else
    ({ B with z := B.z.halves.1 }, { B with z := B.z.halves.2 })

theorem QBox.halves_cover (B : QBox) (x y z : Rat) (h : B.contains x y z) :
    B.halves.1.contains x y z ∨ B.halves.2.contains x y z := by
  obtain ⟨hx, hy, hz⟩ := h
  unfold QBox.halves
  split
  · rcases QIv.halves_cover _ _ hx with h | h
    · exact Or.inl ⟨h, hy, hz⟩
    · exact Or.inr ⟨h, hy, hz⟩
  · split
    · rcases QIv.halves_cover _ _ hy with h | h
      · exact Or.inl ⟨hx, h, hz⟩
      · exact Or.inr ⟨hx, h, hz⟩
    · rcases QIv.halves_cover _ _ hz with h | h
      · exact Or.inl ⟨hx, hy, h⟩
      · exact Or.inr ⟨hx, hy, h⟩

/-- `B ⊖ H`: every `p - c` with `p ∈ B`, `c ∈ H`. -/
def QBox.minus (B H : QBox) : QBox :=
  ⟨⟨B.x.lo - H.x.hi, B.x.hi - H.x.lo⟩, ⟨B.y.lo - H.y.hi, B.y.hi - H.y.lo⟩,
   ⟨B.z.lo - H.z.hi, B.z.hi - H.z.lo⟩⟩

theorem QBox.minus_contains (B H : QBox) (x y z cx cy cz : Rat) (hB : B.contains x y z)
    (hH : H.contains cx cy cz) : (B.minus H).contains (x - cx) (y - cy) (z - cz) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hB
  obtain ⟨⟨d1, d2⟩, ⟨e1, e2⟩, ⟨f1, f2⟩⟩ := hH
  unfold QBox.minus QBox.contains QIv.contains
  dsimp only
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> grind

/-- The box spanned by two lattice points. -/
def QBox.hull (p q : Int × Int × Int) : QBox :=
  ⟨⟨min (p.1 : Rat) q.1, max (p.1 : Rat) q.1⟩, ⟨min (p.2.1 : Rat) q.2.1, max (p.2.1 : Rat) q.2.1⟩,
   ⟨min (p.2.2 : Rat) q.2.2, max (p.2.2 : Rat) q.2.2⟩⟩

theorem segment_coord_in_hull (a b t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    min a b ≤ a + t * (b - a) ∧ a + t * (b - a) ≤ max a b := by
  rcases @Rat.le_total a b with hab | hab
  · have hd : 0 ≤ b - a := by grind
    have e1 := Rat.mul_nonneg h0 hd
    have e2 := Rat.mul_le_mul_of_nonneg_right h1 hd
    rw [Rat.min_def, Rat.max_def]; split <;> grind
  · have hd : 0 ≤ a - b := by grind
    have e1 := Rat.mul_nonneg h0 hd
    have e2 := Rat.mul_le_mul_of_nonneg_right h1 hd
    have e3 : t * (b - a) = -(t * (a - b)) := by grind
    rw [Rat.min_def, Rat.max_def, e3]; split <;> grind

/-- Every point of the segment from `p` to `q` lies in their hull. -/
theorem segment_in_hull (p q : Int × Int × Int) (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (QBox.hull p q).contains ((p.1 : Rat) + t * ((q.1 : Rat) - p.1))
      ((p.2.1 : Rat) + t * ((q.2.1 : Rat) - p.2.1)) ((p.2.2 : Rat) + t * ((q.2.2 : Rat) - p.2.2)) :=
  ⟨segment_coord_in_hull _ _ _ h0 h1, segment_coord_in_hull _ _ _ h0 h1,
   segment_coord_in_hull _ _ _ h0 h1⟩

/-- A lattice box as a rational box. -/
def Box3D.toQ (B : Box3D) : QBox :=
  ⟨⟨B.xIv.lo, B.xIv.hi⟩, ⟨B.yIv.lo, B.yIv.hi⟩, ⟨B.zIv.lo, B.zIv.hi⟩⟩

/-! ## 10. The motion certificate, checked rather than searched (`cam-gouge@1`)

Searching for a k-d subdivision at every build is the expensive part; the subdivision found is the
certificate. `KdCert` records it, `checkKdZ` replays it (one interval evaluation per leaf, no
search), and `checkKdZ_sound` says what a replayed tree establishes. Moves are grouped into chunks; a chunk's tool
positions are enclosed by the box of its moves' end points, which holds every point of every move
(`move_in_box`). `searchKdZ` produces certificates and is run once, outside the build
(`lean/tools/emitcam`). The judge and its wire format are `camGougeFormat`. -/

/-- A recorded k-d subdivision: a leaf says which test closes the box pair. -/
inductive KdCert where
  | part
  | tool
  | splitB (l r : KdCert)
  | splitH (l r : KdCert)
  deriving Repr, Inhabited

/-! ### Replaying in integers

The tree is replayed over integer boxes with the integer interval evaluator (`evalFRepInterval`),
which is exact integer arithmetic and an order of magnitude cheaper than `Rat`. On an integer box the
two evaluators agree up to the cast (`evalFRepInterval_toQ`), so a passing integer leaf is a passing
rational leaf, and the statement is still about every rational point. Halves overlap at the
midpoint (`[lo, m]`, `[m, hi]`) so that they cover the rationals between. -/

theorem intCast_min' (a b : Int) : ((min a b : Int) : Rat) = min (a : Rat) (b : Rat) := by
  rw [Int.min_def, Rat.min_def]
  by_cases h : a ≤ b
  · have h' : (a : Rat) ≤ b := by exact_mod_cast h
    simp [h, h']
  · have h' : ¬ (a : Rat) ≤ b := by exact_mod_cast h
    simp [h, h']

theorem intCast_max' (a b : Int) : ((max a b : Int) : Rat) = max (a : Rat) (b : Rat) := by
  rw [Int.max_def, Rat.max_def]
  by_cases h : a ≤ b
  · have h' : (a : Rat) ≤ b := by exact_mod_cast h
    simp [h, h']
  · have h' : ¬ (a : Rat) ≤ b := by exact_mod_cast h
    simp [h, h']

/-- An integer interval as a rational one. -/
def ivToQ (iv : FloatInterval) : QIv := ⟨iv.lo, iv.hi⟩

theorem ivSq_toQ (a : FloatInterval) : qSq (ivToQ a) = ivToQ (ivSq a) := by
  unfold qSq ivSq ivToQ
  dsimp only
  by_cases h1 : 0 ≤ a.lo
  · have h1' : (0 : Rat) ≤ a.lo := by exact_mod_cast h1
    simp [h1, h1', Rat.intCast_mul]
  · have h1' : ¬ (0 : Rat) ≤ a.lo := by exact_mod_cast h1
    by_cases h2 : a.hi ≤ 0
    · have h2' : (a.hi : Rat) ≤ 0 := by exact_mod_cast h2
      simp [h1, h1', h2, h2', Rat.intCast_mul]
    · have h2' : ¬ (a.hi : Rat) ≤ 0 := by exact_mod_cast h2
      simp [h1, h1', h2, h2', Rat.intCast_mul, intCast_max']

theorem natCast_intCast_rat (k : Nat) : (((k : Int)) : Rat) = (k : Rat) := by norm_cast

/-- On an integer box, the rational evaluator is the integer one, cast. -/
theorem evalFRepInterval_toQ (B : Box3D) (e : FRepExpr) :
    evalFRepIntervalQ B.toQ e = ivToQ (evalFRepInterval B e) := by
  induction e with
  | const c => rfl
  | varX => rfl
  | varY => rfl
  | varZ => rfl
  | add a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepInterval, iha, ihb, ivAdd, ivToQ, Rat.intCast_add]
  | sub a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepInterval, iha, ihb, ivSub, ivToQ, Rat.intCast_sub]
  | scalePos k a iha =>
    simp only [evalFRepIntervalQ, evalFRepInterval, iha, ivScalePos, ivToQ, Rat.intCast_mul]
    rw [show (Int.ofNat k : Int) = (k : Int) from rfl, natCast_intCast_rat]
  | sq a iha =>
    simp only [evalFRepIntervalQ, evalFRepInterval, iha, ivSq_toQ]
  | csgUnion a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepInterval, iha, ihb, ivMin, ivToQ, intCast_min']
  | csgInter a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepInterval, iha, ihb, ivMax, ivToQ, intCast_max']
  | csgDiff a b iha ihb =>
    simp only [evalFRepIntervalQ, evalFRepInterval, iha, ihb, ivMax, ivNeg, ivToQ,
      intCast_max', Rat.intCast_neg]
  | offset r a iha =>
    simp only [evalFRepIntervalQ, evalFRepInterval, iha, ivSub, ivToQ, Rat.intCast_sub]

/-- `B ⊖ H` on integer boxes. -/
def Box3D.minus (B H : Box3D) : Box3D :=
  ⟨⟨B.xIv.lo - H.xIv.hi, B.xIv.hi - H.xIv.lo⟩, ⟨B.yIv.lo - H.yIv.hi, B.yIv.hi - H.yIv.lo⟩,
   ⟨B.zIv.lo - H.zIv.hi, B.zIv.hi - H.zIv.lo⟩⟩

theorem Box3D.minus_toQ (B H : Box3D) : (B.minus H).toQ = B.toQ.minus H.toQ := by
  simp only [Box3D.minus, Box3D.toQ, QBox.minus, Rat.intCast_sub]

def ivHalvesO (iv : FloatInterval) : FloatInterval × FloatInterval :=
  let mid := (iv.lo + iv.hi) / 2
  (⟨iv.lo, mid⟩, ⟨mid, iv.hi⟩)

theorem ivHalvesO_cover (iv : FloatInterval) (v : Rat) (h : (ivToQ iv).contains v) :
    (ivToQ (ivHalvesO iv).1).contains v ∨ (ivToQ (ivHalvesO iv).2).contains v := by
  unfold ivHalvesO ivToQ QIv.contains at *
  dsimp only at *
  rcases @Rat.le_total v (((iv.lo + iv.hi) / 2 : Int) : Rat) with hm | hm
  · exact Or.inl ⟨h.1, hm⟩
  · exact Or.inr ⟨hm, h.2⟩

def Box3D.widthZ (B : Box3D) : Int :=
  max (B.xIv.hi - B.xIv.lo) (max (B.yIv.hi - B.yIv.lo) (B.zIv.hi - B.zIv.lo))

/-- Split an integer box across its widest axis into overlapping halves. -/
def Box3D.halvesO (B : Box3D) : Box3D × Box3D :=
  if B.yIv.hi - B.yIv.lo ≤ B.xIv.hi - B.xIv.lo ∧ B.zIv.hi - B.zIv.lo ≤ B.xIv.hi - B.xIv.lo then
    ({ B with xIv := (ivHalvesO B.xIv).1 }, { B with xIv := (ivHalvesO B.xIv).2 })
  else if B.zIv.hi - B.zIv.lo ≤ B.yIv.hi - B.yIv.lo then
    ({ B with yIv := (ivHalvesO B.yIv).1 }, { B with yIv := (ivHalvesO B.yIv).2 })
  else
    ({ B with zIv := (ivHalvesO B.zIv).1 }, { B with zIv := (ivHalvesO B.zIv).2 })

theorem Box3D.halvesO_cover (B : Box3D) (x y z : Rat) (h : B.toQ.contains x y z) :
    B.halvesO.1.toQ.contains x y z ∨ B.halvesO.2.toQ.contains x y z := by
  obtain ⟨hx, hy, hz⟩ := h
  have hx' : (ivToQ B.xIv).contains x := hx
  have hy' : (ivToQ B.yIv).contains y := hy
  have hz' : (ivToQ B.zIv).contains z := hz
  unfold Box3D.halvesO
  split
  · rcases ivHalvesO_cover _ _ hx' with h | h
    · exact Or.inl ⟨h, hy, hz⟩
    · exact Or.inr ⟨h, hy, hz⟩
  · split
    · rcases ivHalvesO_cover _ _ hy' with h | h
      · exact Or.inl ⟨hx, h, hz⟩
      · exact Or.inr ⟨hx, h, hz⟩
    · rcases ivHalvesO_cover _ _ hz' with h | h
      · exact Or.inl ⟨hx, hy, h⟩
      · exact Or.inr ⟨hx, hy, h⟩

def checkKdZ (part tool0 : FRepExpr) : KdCert → Box3D → Box3D → Bool
  | .part, B, _ => decide (0 < (evalFRepInterval B part).lo)
  | .tool, B, H => decide (0 < (evalFRepInterval (B.minus H) tool0).lo)
  | .splitB l r, B, H => checkKdZ part tool0 l B.halvesO.1 H && checkKdZ part tool0 r B.halvesO.2 H
  | .splitH l r, B, H => checkKdZ part tool0 l B H.halvesO.1 && checkKdZ part tool0 r B H.halvesO.2

/-- **`checkKdZ_sound`**: a tree replayed in integers clears every rational point of `B` from the
cutter at every rational position in `H`. -/
theorem checkKdZ_sound (part tool0 : FRepExpr) :
    ∀ (c : KdCert) (B H : Box3D), checkKdZ part tool0 c B H = true →
      ∀ x y z cx cy cz : Rat, B.toQ.contains x y z → H.toQ.contains cx cy cz →
        evalFRepQ x y z part ≤ 0 → 0 < evalFRepQ (x - cx) (y - cy) (z - cz) tool0 := by
  intro c
  induction c with
  | part =>
    intro B H h x y z cx cy cz hB _ hP
    have henc := (frepQ_enclosure_sound B.toQ x y z hB part).1
    rw [evalFRepInterval_toQ] at henc
    simp only [checkKdZ, decide_eq_true_eq] at h
    have h' : (0 : Rat) < ((evalFRepInterval B part).lo : Rat) := by exact_mod_cast h
    simp only [ivToQ] at henc
    exact absurd hP (by grind)
  | tool =>
    intro B H h x y z cx cy cz hB hH _
    have hm := QBox.minus_contains B.toQ H.toQ x y z cx cy cz hB hH
    rw [← Box3D.minus_toQ] at hm
    have henc := (frepQ_enclosure_sound _ _ _ _ hm tool0).1
    rw [evalFRepInterval_toQ] at henc
    simp only [checkKdZ, decide_eq_true_eq] at h
    have h' : (0 : Rat) < ((evalFRepInterval (B.minus H) tool0).lo : Rat) := by exact_mod_cast h
    simp only [ivToQ] at henc
    grind
  | splitB l r ihl ihr =>
    intro B H h x y z cx cy cz hB hH hP
    simp only [checkKdZ, Bool.and_eq_true] at h
    rcases Box3D.halvesO_cover B x y z hB with hc | hc
    · exact ihl _ _ h.1 x y z cx cy cz hc hH hP
    · exact ihr _ _ h.2 x y z cx cy cz hc hH hP
  | splitH l r ihl ihr =>
    intro B H h x y z cx cy cz hB hH hP
    simp only [checkKdZ, Bool.and_eq_true] at h
    rcases Box3D.halvesO_cover H cx cy cz hH with hc | hc
    · exact ihl _ _ h.1 x y z cx cy cz hB hc hP
    · exact ihr _ _ h.2 x y z cx cy cz hB hc hP

/-- Find a tree in integers; a box pair whose wider side is one unit is not split further. -/
def searchKdZ (part tool0 : FRepExpr) : Nat → Box3D → Box3D → Option KdCert
  | 0, B, H =>
    if 0 < (evalFRepInterval B part).lo then some .part
    else if 0 < (evalFRepInterval (B.minus H) tool0).lo then some .tool else none
  | d + 1, B, H =>
    if 0 < (evalFRepInterval B part).lo then some .part
    else if 0 < (evalFRepInterval (B.minus H) tool0).lo then some .tool
    else if max B.widthZ H.widthZ ≤ 1 then none
    else if H.widthZ ≤ B.widthZ then
      match searchKdZ part tool0 d B.halvesO.1 H with
      | none => none
      | some l => (searchKdZ part tool0 d B.halvesO.2 H).map (.splitB l)
    else
      match searchKdZ part tool0 d B H.halvesO.1 with
      | none => none
      | some l => (searchKdZ part tool0 d B H.halvesO.2).map (.splitH l)

abbrev Pt3 := Int × Int × Int

/-- Lower and upper bound of a list of integers, starting from `(lo, hi)`. -/
def intBounds : Int × Int → List Int → Int × Int
  | acc, [] => acc
  | (lo, hi), a :: rest => intBounds (min lo a, max hi a) rest

theorem intBounds_spec : ∀ (xs : List Int) (lo hi : Int),
    (intBounds (lo, hi) xs).1 ≤ lo ∧ hi ≤ (intBounds (lo, hi) xs).2 ∧
    ∀ a ∈ xs, (intBounds (lo, hi) xs).1 ≤ a ∧ a ≤ (intBounds (lo, hi) xs).2
  | [], lo, hi => ⟨Int.le_refl _, Int.le_refl _, fun _ h => by cases h⟩
  | a :: rest, lo, hi => by
    obtain ⟨h1, h2, h3⟩ := intBounds_spec rest (min lo a) (max hi a)
    simp only [intBounds]
    refine ⟨by omega, by omega, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · omega
    · exact h3 b hb

/-- The box of all end points of a list of moves. -/
def movesBoxZ (ms : List (Pt3 × Pt3)) : Box3D :=
  let pts := ms.flatMap fun m => [m.1, m.2]
  let d : Pt3 := (pts.headD (0, 0, 0))
  let bx := intBounds (d.1, d.1) (pts.map (·.1))
  let byy := intBounds (d.2.1, d.2.1) (pts.map (·.2.1))
  let bz := intBounds (d.2.2, d.2.2) (pts.map (·.2.2))
  ⟨⟨bx.1, bx.2⟩, ⟨byy.1, byy.2⟩, ⟨bz.1, bz.2⟩⟩

def movesBox (ms : List (Pt3 × Pt3)) : QBox := (movesBoxZ ms).toQ

theorem coord_between (lo hi a b t : Rat) (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : lo ≤ a + t * (b - a) ∧ a + t * (b - a) ≤ hi := by
  have := segment_coord_in_hull a b t h0 h1
  rw [Rat.min_def, Rat.max_def] at this
  split at this <;> grind

/-- Every point of every move lies in the moves' box. -/
theorem move_in_box (ms : List (Pt3 × Pt3)) (m : Pt3 × Pt3) (hm : m ∈ ms) (t : Rat) (h0 : 0 ≤ t)
    (h1 : t ≤ 1) :
    (movesBox ms).contains ((m.1.1 : Rat) + t * ((m.2.1 : Rat) - m.1.1))
      ((m.1.2.1 : Rat) + t * ((m.2.2.1 : Rat) - m.1.2.1))
      ((m.1.2.2 : Rat) + t * ((m.2.2.2 : Rat) - m.1.2.2)) := by
  have hp : m.1 ∈ ms.flatMap (fun m => [m.1, m.2]) := List.mem_flatMap.mpr ⟨m, hm, by simp⟩
  have hq : m.2 ∈ ms.flatMap (fun m => [m.1, m.2]) := List.mem_flatMap.mpr ⟨m, hm, by simp⟩
  unfold movesBox movesBoxZ Box3D.toQ QBox.contains QIv.contains
  dsimp only
  generalize ms.flatMap (fun m => [m.1, m.2]) = pts at hp hq
  have cast2 : ∀ (lo hi a : Int), lo ≤ a ∧ a ≤ hi → (lo : Rat) ≤ (a : Rat) ∧ (a : Rat) ≤ (hi : Rat) :=
    fun lo hi a h => ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have bx := (intBounds_spec (pts.map (·.1)) (pts.headD (0, 0, 0)).1 (pts.headD (0, 0, 0)).1).2.2
  have byy := (intBounds_spec (pts.map (·.2.1)) (pts.headD (0, 0, 0)).2.1 (pts.headD (0, 0, 0)).2.1).2.2
  have bz := (intBounds_spec (pts.map (·.2.2)) (pts.headD (0, 0, 0)).2.2 (pts.headD (0, 0, 0)).2.2).2.2
  refine ⟨coord_between _ _ _ _ t (cast2 _ _ _ (bx _ (List.mem_map_of_mem hp)))
      (cast2 _ _ _ (bx _ (List.mem_map_of_mem hq))) h0 h1,
    coord_between _ _ _ _ t (cast2 _ _ _ (byy _ (List.mem_map_of_mem hp)))
      (cast2 _ _ _ (byy _ (List.mem_map_of_mem hq))) h0 h1,
    coord_between _ _ _ _ t (cast2 _ _ _ (bz _ (List.mem_map_of_mem hp)))
      (cast2 _ _ _ (bz _ (List.mem_map_of_mem hq))) h0 h1⟩

/-- Moves on one tool axis (one pass). -/
structure CamChunk where
  axis  : ToolAxis
  moves : List (Pt3 × Pt3)
  deriving Repr

/-- The object: a part, a box holding it, a cutter (ball radius, shank length), and the moves of
each pass. -/
structure CamGougeObj where
  part     : FRepExpr
  box      : Box3D
  toolR    : Nat
  shankLen : Nat
  chunks   : List CamChunk
  deriving Repr

/-- The certificate of one pass: consecutive groups of moves (`k` moves each, in order), each with
the k-d tree for the box of its end points. How the moves are grouped is the producer's choice. -/
abbrev CamPassCert := List (Nat × KdCert)

def checkGroups (part tool0 : FRepExpr) (box : Box3D) : List (Pt3 × Pt3) → CamPassCert → Bool
  | [], _ => true
  | _ :: _, [] => false
  | ms@(_ :: _), (k, t) :: rest =>
    checkKdZ part tool0 t box (movesBoxZ (ms.take k)) && checkGroups part tool0 box (ms.drop k) rest

theorem checkGroups_mem (part tool0 : FRepExpr) (box : Box3D) :
    ∀ (gs : CamPassCert) (ms : List (Pt3 × Pt3)), checkGroups part tool0 box ms gs = true →
      ∀ m ∈ ms, ∃ g : List (Pt3 × Pt3), ∃ t : KdCert,
        checkKdZ part tool0 t box (movesBoxZ g) = true ∧ m ∈ g
  | [], ms, h, m, hm => by
    cases ms with
    | nil => cases hm
    | cons _ _ => simp [checkGroups] at h
  | (k, t) :: rest, ms, h, m, hm => by
    cases ms with
    | nil => cases hm
    | cons a as =>
      simp only [checkGroups, Bool.and_eq_true] at h
      rw [← List.take_append_drop k (a :: as)] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨_, t, h.1, hm⟩
      · exact checkGroups_mem part tool0 box rest _ h.2 m hm

inductive CamGougeClause where
  | chunkCount (expected got : Nat)
  | notCleared (chunk : Nat)
  deriving Repr, DecidableEq

def checkCamGouge (o : CamGougeObj) (c : List CamPassCert) : Judge.Verdict CamGougeClause :=
  if c.length != o.chunks.length then .refused (.chunkCount o.chunks.length c.length) []
  else
    match ((o.chunks.zip c).zipIdx.find? fun ((ch, gs), _) =>
        !checkGroups o.part (frepBallEndMill 0 0 0 ch.axis o.toolR o.shankLen) o.box ch.moves gs) with
    | some (_, i) => .refused (.notCleared i) []
    | none => .ok

/-- What an accepted certificate establishes: at every rational time of every move, the cutter at
its true size contains no rational point of the part inside the box. -/
def CamGougeMeaning (o : CamGougeObj) : Prop :=
  ∀ ch ∈ o.chunks, ∀ m ∈ ch.moves, ∀ t : Rat, 0 ≤ t → t ≤ 1 → ∀ x y z : Rat,
    o.box.toQ.contains x y z → evalFRepQ x y z o.part ≤ 0 →
    0 < evalFRepQ (x - ((m.1.1 : Rat) + t * ((m.2.1 : Rat) - m.1.1)))
      (y - ((m.1.2.1 : Rat) + t * ((m.2.2.1 : Rat) - m.1.2.1)))
      (z - ((m.1.2.2 : Rat) + t * ((m.2.2.2 : Rat) - m.1.2.2)))
      (frepBallEndMill 0 0 0 ch.axis o.toolR o.shankLen)

theorem checkCamGouge_sound (o : CamGougeObj) (c : List CamPassCert) (h : checkCamGouge o c = .ok) :
    CamGougeMeaning o := by
  unfold checkCamGouge at h
  split at h
  · cases h
  · rename_i hlen
    split at h
    · cases h
    · rename_i hnone
      intro ch hch m hm t h0 h1 x y z hB hP
      have hl : c.length = o.chunks.length := by simpa using hlen
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hch
      have hi' : i < c.length := by omega
      have hz : ((o.chunks[i], c[i]), i) ∈ (o.chunks.zip c).zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?]
        simp [List.getElem?_zip_eq_some, hi, hi']
      have hk := List.find?_eq_none.mp hnone _ hz
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hk
      obtain ⟨g, kt, hck, hmg⟩ := checkGroups_mem _ _ _ _ _ (by simpa using hk) m hm
      exact checkKdZ_sound _ _ _ _ _ hck x y z _ _ _ hB (move_in_box _ m hmg t h0 h1) hP

instance camGougeJudge : Obend.Judge CamGougeObj (List CamPassCert) where
  Clause := CamGougeClause
  Meaning o _ := CamGougeMeaning o
  check _ := checkCamGouge
  sound := fun {_ o c} h => checkCamGouge_sound o c h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ hRef; cases hRef
  Fragment _ := False
  complete := by intro _ h; exact h.elim
  mono := by intro _ _ _ _ _ _; rfl

/-! ### Wire format: whitespace-separated tokens -/

def FRepExpr.toTokens : FRepExpr → List String
  | .const c => ["c", toString c]
  | .varX => ["x"] | .varY => ["y"] | .varZ => ["z"]
  | .add a b => "+" :: a.toTokens ++ b.toTokens
  | .sub a b => "-" :: a.toTokens ++ b.toTokens
  | .scalePos k a => "k" :: toString k :: a.toTokens
  | .sq a => "q" :: a.toTokens
  | .csgUnion a b => "u" :: a.toTokens ++ b.toTokens
  | .csgInter a b => "i" :: a.toTokens ++ b.toTokens
  | .csgDiff a b => "d" :: a.toTokens ++ b.toTokens
  | .offset r a => "o" :: toString r :: a.toTokens

def FRepExpr.ofTokens : Nat → List String → Option (FRepExpr × List String)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, t :: ts =>
    let bin (f : FRepExpr → FRepExpr → FRepExpr) : Option (FRepExpr × List String) := do
      let (a, r1) ← FRepExpr.ofTokens fuel ts
      let (b, r2) ← FRepExpr.ofTokens fuel r1
      pure (f a b, r2)
    match t with
    | "c" => match ts with | n :: r => (n.toInt?).map fun v => (.const v, r) | [] => none
    | "x" => some (.varX, ts) | "y" => some (.varY, ts) | "z" => some (.varZ, ts)
    | "+" => bin .add | "-" => bin .sub | "u" => bin .csgUnion | "i" => bin .csgInter
    | "d" => bin .csgDiff
    | "k" => match ts with
      | n :: r => do let k ← n.toNat?; let (a, r') ← FRepExpr.ofTokens fuel r; pure (.scalePos k a, r')
      | [] => none
    | "q" => do let (a, r) ← FRepExpr.ofTokens fuel ts; pure (.sq a, r)
    | "o" => match ts with
      | n :: r => do let v ← n.toInt?; let (a, r') ← FRepExpr.ofTokens fuel r; pure (.offset v a, r')
      | [] => none
    | _ => none

/-- A tree as one character per node (`P`, `T`, `B`, `H`, prefix order). -/
def KdCert.toChars : KdCert → List Char
  | .part => ['P'] | .tool => ['T']
  | .splitB l r => 'B' :: l.toChars ++ r.toChars
  | .splitH l r => 'H' :: l.toChars ++ r.toChars

def KdCert.ofChars : Nat → List Char → Option (KdCert × List Char)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, ch :: cs =>
    match ch with
    | 'P' => some (.part, cs)
    | 'T' => some (.tool, cs)
    | 'B' => do
      let (l, r1) ← KdCert.ofChars fuel cs; let (r, r2) ← KdCert.ofChars fuel r1; pure (.splitB l r, r2)
    | 'H' => do
      let (l, r1) ← KdCert.ofChars fuel cs; let (r, r2) ← KdCert.ofChars fuel r1; pure (.splitH l r, r2)
    | _ => none

def wireTokens (s : String) : List String :=
  ((s.replace "\n" " ").splitOn " ").filter (· ≠ "")

/-- Certificate wire: one line per pass; on it, one `k:TREE` token per group of `k` moves. -/
def encodeCamCert (c : List CamPassCert) : String :=
  String.intercalate "\n" (c.map fun gs =>
    String.intercalate " " (gs.map fun (k, t) => s!"{k}:" ++ String.ofList t.toChars)) ++ "\n"

def decodeCamGroup (tok : String) : Except String (Nat × KdCert) :=
  match tok.splitOn ":" with
  | [k, tree] =>
    match k.toNat?, KdCert.ofChars (tree.length + 1) tree.toList with
    | some n, some (t, []) => .ok (n, t)
    | _, _ => .error "malformed group"
  | _ => .error "malformed group"

def decodeCamCert (s : String) : Except String (List CamPassCert) :=
  ((s.splitOn "\n").filter (· ≠ "")).mapM fun l => ((l.splitOn " ").filter (· ≠ "")).mapM decodeCamGroup

def pt3Tokens (p : Pt3) : List String := [toString p.1, toString p.2.1, toString p.2.2]

/-- Object wire: `part …`, `box …`, `tool r len`, then one `chunk ux uy uz n` line and its move
end points per chunk. -/
def encodeCamObj (o : CamGougeObj) : String :=
  let b := o.box
  let header :=
    [ "part " ++ String.intercalate " " o.part.toTokens
    , s!"box {b.xIv.lo} {b.xIv.hi} {b.yIv.lo} {b.yIv.hi} {b.zIv.lo} {b.zIv.hi}"
    , s!"tool {o.toolR} {o.shankLen}" ]
  let chunks := o.chunks.map fun ch =>
    String.intercalate " " (["chunk", toString ch.axis.ux, toString ch.axis.uy, toString ch.axis.uz,
      toString ch.axis.n] ++ ch.moves.flatMap fun m => pt3Tokens m.1 ++ pt3Tokens m.2)
  String.intercalate "\n" (header ++ chunks) ++ "\n"

def decodeMoves : List Int → Option (List (Pt3 × Pt3))
  | a :: b :: c :: d :: e :: f :: rest => (decodeMoves rest).map (((a, b, c), (d, e, f)) :: ·)
  | [] => some []
  | _ => none

def decodeCamObj (s : String) : Except String CamGougeObj := do
  let lines := (s.splitOn "\n").filter (· ≠ "")
  match lines with
  | pl :: bl :: tl :: cls =>
    let pt := wireTokens pl
    let some ("part", pts) := (match pt with | h :: r => some (h, r) | [] => none) | .error "part"
    let some (part, []) := FRepExpr.ofTokens (pts.length + 1) pts | .error "part expression"
    let some [x0, x1, y0, y1, z0, z1] := ((wireTokens bl).drop 1).mapM String.toInt? | .error "box"
    let some [r, len] := ((wireTokens tl).drop 1).mapM String.toNat? | .error "tool"
    let chunks ← cls.mapM fun l =>
      match ((wireTokens l).drop 1).mapM String.toInt? with
      | some (ux :: uy :: uz :: n :: rest) =>
        match decodeMoves rest with
        | some ms => .ok { axis := ⟨ux, uy, uz, n.toNat⟩, moves := ms }
        | none => .error "chunk moves"
      | _ => .error "chunk header"
    pure { part, box := ⟨⟨x0, x1⟩, ⟨y0, y1⟩, ⟨z0, z1⟩⟩, toolR := r, shankLen := len, chunks }
  | _ => .error "object needs part, box, tool lines"

/-- Planted bad object: a vertical ball end mill parked inside a unit cube. -/
def camGougeBad : CamGougeObj × List CamPassCert :=
  ({ part := .csgInter (.csgInter (.csgInter (.sub (.const 0) .varX) (.offset 4 .varX))
        (.csgInter (.sub (.const 0) .varY) (.offset 4 .varY)))
        (.csgInter (.sub (.const 0) .varZ) (.offset 4 .varZ))
     box := ⟨⟨0, 4⟩, ⟨0, 4⟩, ⟨0, 4⟩⟩, toolR := 1, shankLen := 2
     chunks := [{ axis := ⟨0, 0, 1, 1⟩, moves := [((2, 2, 1), (2, 2, 1))] }] }, [[(1, .tool)]])

theorem camGougeBad_refused : checkCamGouge camGougeBad.1 camGougeBad.2 = .refused (.notCleared 0) [] := by
  decide +kernel

def camGougeFormat : Obend.Judge.Format where
  name        := "cam-gouge"
  version     := "1"
  Obj         := CamGougeObj
  Cert        := List CamPassCert
  judge       := camGougeJudge
  decodeObj   := decodeCamObj
  decodeCert  := decodeCamCert
  trust       := .compiled
  regime      := .decidable
  bad         := camGougeBad
  badGrade    := 0
  bad_refused := ⟨_, _, camGougeBad_refused⟩

end Obend.Hardware.GeometryCAM
end
