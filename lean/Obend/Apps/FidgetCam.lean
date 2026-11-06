module
/-
# Obend.Apps.FidgetCam — the fidget part: `.obend` parameters, one solid, a certified tool path, a post

`apps/fidget-cam/*.obend` is four parameter records with overrides (hub, cooling bore, mounting lug,
process). This module builds one F-Rep solid from the composed values (`fidgetParams_eq_obend`),
certifies the bore wall over the whole bore (`fidget_bore_wall_sound`), generates Z-level contours
and 3+2 top-edge passes, states the moves as the object of the `cam-gouge@1` judge (whose committed
certificate `Obend.Apps.FidgetCamCert` checks), and posts the program with TCPM
(`impeller5AxisNgc`, rotary-safe by `Obend.Hardware.Kinematics.postMoves_rotarySafe`). The RTL voxel
evaluator is compiled from the solid's tape (`FRepExpr.toTape`), not written beside it.

What is not here: blades (the part is a hub, a lug and a bore), the holder, simultaneous five-axis
motion, and a theorem relating the RTL to `evalFRepPoint` for every input.
-/
public import Lean
public import Obend.Hardware.UserspacePhysical
public import Obend.Hardware.Synth
public import Obend.Hardware.GeometryCAM
public import Obend.Hardware.OpenUSD
public import Obend.Spec.CrossPackage
public import Obend.Leaf.Emit
public import Obend.Leaf.Flatten
public import Obend.Tactic.Tooth
public import Obend.Elab.Workbook
public meta import Lean
public meta import Obend.Hardware.UserspacePhysical
public meta import Obend.Elab.Workbook
public import Obend.Hardware.Kinematics
public meta import Obend.Hardware.GeometryCAM
public meta import Obend.Hardware.Kinematics
public import Obend.AssertCompiled
public section

namespace Obend.Apps.FidgetCam

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Lower
open Obend.Slot
open Obend.Slot.World
open Obend.Spec.CrossPackage
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
open Obend.Hardware.GeometryCAM
open Obend.Hardware.OpenUSD
open Obend.Hardware.UserspacePhysical
open Obend.Hardware.Kinematics

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! ## 0. `#import_obend` is `Obend.Elab.Workbook`'s (the one importer, 2026-11-04); this module
only consumes the constants it emits (`<def>_comp`, `<def>_book`, `<def>_val`, `claim_*_{obj,just,holds}`,
`laws_count`). -/

/-! ## 1. Compile-Time Elaboration of `apps/fidget-cam/*.obend` via `#import_obend` -/

#import_obend "apps/fidget-cam/BaseImpellerBody.obend" as FidgetBaseBody
#import_obend "apps/fidget-cam/CoolingChannelOverride.obend" as FidgetCoolingChannel
#import_obend "apps/fidget-cam/MountingBossAssembly.obend" as FidgetMountingBoss
#import_obend "apps/fidget-cam/ImpellerPartTop.obend" as FidgetImpellerTop

/-! ## 1a. The parameters the package carries

The four modules are parameter records with overrides (`apps/fidget-cam/*.obend`). Everything
below is built from the composed values; `fidgetParams_eq_obend` is the link, decided against the
constants the importer emitted. -/

/-- The natural number a reduced `.obend` value carries (`0` for anything else). -/
@[expose] def natOfTerm : Term → Nat
  | .nat n => n
  | _ => 0

/-- Part and process parameters, micrometres unless named otherwise. -/
structure FidgetParams where
  hubR : Nat
  hubH : Nat
  lugX : Nat
  lugR : Nat
  boreX : Nat
  boreR : Nat
  minWall : Nat
  unit : Nat
  toolR : Nat
  shankLen : Nat
  toolOffset : Nat
  clearAbove : Nat
  stepDown : Nat
  cutFeed : Nat
  plungeFeed : Nat
  rpm : Nat
  deriving DecidableEq, Repr

/-- The parameters as the importer reduced them from the composed `.obend` objects. -/
@[expose] def FidgetParams.ofObend : FidgetParams :=
  { hubR := natOfTerm FidgetBaseBody.hubRadius_val
  , hubH := natOfTerm FidgetBaseBody.hubHeight_val
  , lugX := natOfTerm FidgetMountingBoss.lugCentreX_val
  , lugR := natOfTerm FidgetMountingBoss.lugRadius_val
  , boreX := natOfTerm FidgetCoolingChannel.boreOffsetX_val
  , boreR := natOfTerm FidgetCoolingChannel.boreRadius_val
  , minWall := natOfTerm FidgetCoolingChannel.minWall_val
  , unit := natOfTerm FidgetImpellerTop.lattice_val
  , toolR := natOfTerm FidgetImpellerTop.toolRadius_val
  , shankLen := natOfTerm FidgetImpellerTop.shankLength_val
  , toolOffset := natOfTerm FidgetImpellerTop.toolOffset_val
  , clearAbove := natOfTerm FidgetImpellerTop.clearanceAboveTop_val
  , stepDown := natOfTerm FidgetImpellerTop.stepDown_val
  , cutFeed := natOfTerm FidgetImpellerTop.cutFeed_val
  , plungeFeed := natOfTerm FidgetImpellerTop.plungeFeed_val
  , rpm := natOfTerm FidgetImpellerTop.spindle_val }

/-- The same values as literals, for the compiled checks below (the importer's constants are not
compiled code). -/
@[expose] def fidgetParams : FidgetParams :=
  { hubR := 10000, hubH := 8000, lugX := 10000, lugR := 2500, boreX := 4000, boreR := 2000
  , minWall := 2000, unit := 100, toolR := 2000, shankLen := 12000, toolOffset := 2400
  , clearAbove := 5000, stepDown := 2000, cutFeed := 1200, plungeFeed := 300, rpm := 18000 }

/-- The literal parameters are the composed `.obend` values: the overrides (hub height 8 mm,
lug radius 2.5 mm, bore radius 2 mm, stock 0.4 mm) are what the CAM tier machines. -/
theorem fidgetParams_eq_obend : fidgetParams = FidgetParams.ofObend := by
  decide +kernel

/-- Every length is a whole number of lattice units. -/
@[expose] def FidgetParams.onLattice (p : FidgetParams) : Bool :=
  [p.hubR, p.hubH, p.lugX, p.lugR, p.boreX, p.boreR, p.minWall, p.toolR, p.shankLen,
    p.toolOffset, p.clearAbove, p.stepDown].all (fun v => v % p.unit == 0)

example : fidgetParams.onLattice = true := by decide +kernel

/-- Micrometres to lattice units. -/
@[expose] def FidgetParams.lat (p : FidgetParams) (um : Nat) : Nat := um / p.unit

/-! ## 2. Vtable flattening, `Leaf.Book` emission, cone survival -/

theorem fidgetCam_compositions_closed :
    FidgetBaseBody.shroudedImpellerBody_comp.closedB = true ∧
    FidgetCoolingChannel.conformalCoolingChannel_comp.closedB = true ∧
    FidgetMountingBoss.stiffenedMountingBoss_comp.closedB = true ∧
    FidgetImpellerTop.liverpsImpellerCamTop_comp.closedB = true := by
  decide +kernel

/-- For every member `m`, each composed parameter object is observationally equivalent (`≈b`) to
its flattened vtable and to its emitted `Leaf.Book`. -/
theorem fidgetCam_flatten_and_book_sound (m : String) :
    (.get FidgetBaseBody.shroudedImpellerBody_comp.flatten m ≈b
      .get FidgetBaseBody.shroudedImpellerBody_comp.object m) ∧
    (.get (emit FidgetBaseBody.shroudedImpellerBody_comp).link m ≈b
      .get FidgetBaseBody.shroudedImpellerBody_comp.object m) ∧
    (.get FidgetCoolingChannel.conformalCoolingChannel_comp.flatten m ≈b
      .get FidgetCoolingChannel.conformalCoolingChannel_comp.object m) ∧
    (.get (emit FidgetCoolingChannel.conformalCoolingChannel_comp).link m ≈b
      .get FidgetCoolingChannel.conformalCoolingChannel_comp.object m) ∧
    (.get FidgetMountingBoss.stiffenedMountingBoss_comp.flatten m ≈b
      .get FidgetMountingBoss.stiffenedMountingBoss_comp.object m) ∧
    (.get (emit FidgetMountingBoss.stiffenedMountingBoss_comp).link m ≈b
      .get FidgetMountingBoss.stiffenedMountingBoss_comp.object m) ∧
    (.get FidgetImpellerTop.liverpsImpellerCamTop_comp.flatten m ≈b
      .get FidgetImpellerTop.liverpsImpellerCamTop_comp.object m) ∧
    (.get (emit FidgetImpellerTop.liverpsImpellerCamTop_comp).link m ≈b
      .get FidgetImpellerTop.liverpsImpellerCamTop_comp.object m) := by
  have ⟨hc1, hc2, hc3, hc4⟩ := fidgetCam_compositions_closed
  exact ⟨flatten_sound _ hc1 m, book_sound _ hc1 m,
         flatten_sound _ hc2 m, book_sound _ hc2 m,
         flatten_sound _ hc3 m, book_sound _ hc3 m,
         flatten_sound _ hc4 m, book_sound _ hc4 m⟩

/-- Cone survival when the shroud override is linked onto the base body (it changes only
`hubHeightUm`). -/
theorem fidgetCam_cone_survives :
    coneSupports
      (linkComposition FidgetBaseBody.baseImpellerBody_comp FidgetBaseBody.shroudedImpellerBody_comp.top)
      ["hubRadiusUm", "hubCentreXUm"] =
      coneSupports FidgetBaseBody.baseImpellerBody_comp ["hubRadiusUm", "hubCentreXUm"] := by
  have hflat : FidgetBaseBody.shroudedImpellerBody_comp.top.flat = false := by decide +kernel
  have hdisj : ∀ m ∈ ["hubRadiusUm", "hubCentreXUm"],
      m ∉ overlayModifiedFields FidgetBaseBody.shroudedImpellerBody_comp.top := by
    decide +kernel
  exact coneSupports_linkComposition_of_disjoint
    FidgetBaseBody.baseImpellerBody_comp
    FidgetBaseBody.shroudedImpellerBody_comp.top
    ["hubRadiusUm", "hubCentreXUm"] hflat hdisj

/-! ## 3. The part as one solid, on a 100 µm lattice -/

/-- A Z-parallel cylinder of radius `r` on the axis through `(cx, cy)`, between `z0` and `z1`. -/
@[expose] def frepCylZ (cx cy : Int) (r : Nat) (z0 z1 : Int) : FRepExpr :=
  .csgInter (.offset ((r : Int) * r) (.add (.sq (.sub .varX (.const cx))) (.sq (.sub .varY (.const cy)))))
    (.csgInter (.sub (.const z0) .varZ) (.sub .varZ (.const z1)))

/-- The bounding box of `frepCylZ`. -/
@[expose] def cylBox (cx cy : Int) (r : Nat) (z0 z1 : Int) : Box3D :=
  { xIv := { lo := cx - r, hi := cx + r }, yIv := { lo := cy - r, hi := cy + r }, zIv := { lo := z0, hi := z1 } }

/-- Smallest box holding two boxes. -/
@[expose] def Box3D.hull (A B : Box3D) : Box3D :=
  { xIv := { lo := min A.xIv.lo B.xIv.lo, hi := max A.xIv.hi B.xIv.hi }
  , yIv := { lo := min A.yIv.lo B.yIv.lo, hi := max A.yIv.hi B.yIv.hi }
  , zIv := { lo := min A.zIv.lo B.zIv.lo, hi := max A.zIv.hi B.zIv.hi } }

theorem int_mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this

theorem abs_le_of_mul_self_le (a : Int) (r : Nat) (h : a * a ≤ (r : Int) * r) : -(r : Int) ≤ a ∧ a ≤ r := by
  have key : ∀ b : Int, (r : Int) + 1 ≤ b → (r : Int) * r < b * b := by
    intro b hb
    have h1 := Int.mul_le_mul hb hb (by omega) (by omega)
    have e : ((r : Int) + 1) * ((r : Int) + 1) = (r : Int) * r + 2 * r + 1 := by
      simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]; omega
    omega
  constructor
  · refine Int.not_lt.mp fun hlt => ?_
    have := key (-a) (by omega)
    rw [Int.neg_mul_neg] at this
    omega
  · refine Int.not_lt.mp fun hlt => ?_
    have := key a (by omega)
    omega

theorem frepCylZ_in_box (cx cy : Int) (r : Nat) (z0 z1 x y z : Int)
    (h : inSolid x y z (frepCylZ cx cy r z0 z1)) : (cylBox cx cy r z0 z1).contains x y z := by
  unfold inSolid frepCylZ at h
  simp only [evalFRepPoint, Int.max_le] at h
  obtain ⟨hr, hz0, hz1⟩ := h
  have hx2 := int_mul_self_nonneg (x - cx)
  have hy2 := int_mul_self_nonneg (y - cy)
  have bx := abs_le_of_mul_self_le (x - cx) r (by omega)
  have by' := abs_le_of_mul_self_le (y - cy) r (by omega)
  unfold cylBox Box3D.contains FloatInterval.contains
  dsimp only
  omega

theorem hull_contains_left (A B : Box3D) (x y z : Int) (h : A.contains x y z) :
    (Box3D.hull A B).contains x y z := by
  obtain ⟨hx, hy, hz⟩ := h
  unfold FloatInterval.contains at hx hy hz
  unfold Box3D.hull Box3D.contains FloatInterval.contains
  dsimp only
  omega

theorem hull_contains_right (A B : Box3D) (x y z : Int) (h : B.contains x y z) :
    (Box3D.hull A B).contains x y z := by
  obtain ⟨hx, hy, hz⟩ := h
  unfold FloatInterval.contains at hx hy hz
  unfold Box3D.hull Box3D.contains FloatInterval.contains
  dsimp only
  omega

/-- Hub ∪ lug, the envelope the bore is cut from. -/
@[expose] def FidgetParams.outer (p : FidgetParams) : FRepExpr :=
  .csgUnion (frepCylZ 0 0 (p.lat p.hubR) 0 (p.lat p.hubH))
    (frepCylZ (p.lat p.lugX) 0 (p.lat p.lugR) 0 (p.lat p.hubH))

/-- The cooling bore as a cavity of the part's height (for the wall), and as the cut (through). -/
@[expose] def FidgetParams.cavity (p : FidgetParams) : FRepExpr :=
  frepCylZ (-(p.lat p.boreX : Int)) 0 (p.lat p.boreR) 0 (p.lat p.hubH)

@[expose] def FidgetParams.part (p : FidgetParams) : FRepExpr :=
  .csgDiff p.outer (frepCylZ (-(p.lat p.boreX : Int)) 0 (p.lat p.boreR) (-1) (p.lat p.hubH + 1))

@[expose] def FidgetParams.partBox (p : FidgetParams) : Box3D :=
  Box3D.hull (cylBox 0 0 (p.lat p.hubR) 0 (p.lat p.hubH))
    (cylBox (p.lat p.lugX) 0 (p.lat p.lugR) 0 (p.lat p.hubH))

/-- Every point of the part lies in `partBox`, for any parameters. -/
theorem FidgetParams.part_in_box (p : FidgetParams) (x y z : Int) (h : inSolid x y z p.part) :
    p.partBox.contains x y z := by
  unfold FidgetParams.part inSolid at h
  simp only [evalFRepPoint, Int.max_le] at h
  have hu := h.1
  unfold FidgetParams.outer at hu
  simp only [evalFRepPoint] at hu
  unfold FidgetParams.partBox
  rcases Int.le_total
      (evalFRepPoint x y z (frepCylZ 0 0 (p.lat p.hubR) 0 (p.lat p.hubH)))
      (evalFRepPoint x y z (frepCylZ (p.lat p.lugX) 0 (p.lat p.lugR) 0 (p.lat p.hubH))) with hle | hle
  · rw [Int.min_eq_left hle] at hu
    exact hull_contains_left _ _ x y z (frepCylZ_in_box _ _ _ _ _ x y z hu)
  · rw [Int.min_eq_right hle] at hu
    exact hull_contains_right _ _ x y z (frepCylZ_in_box _ _ _ _ _ x y z hu)

/-- The part's tape is compiled from the solid, not written beside it. -/
@[expose] def impellerSsaTape : List SsaTapeOp := fidgetParams.part.toTape

theorem impellerSsaTape_eval (x y z : Int) :
    evalSsaTape x y z impellerSsaTape = evalFRepPoint x y z fidgetParams.part :=
  FRepExpr.toTape_eval x y z fidgetParams.part

/-! ## 4. The wall between the cooling bore and the outer surface -/

/-- **`fidget_bore_wall_sound`**: every lattice point within `minWall` (2.0 mm) of any point of the
cooling bore, in X and in Y, is material of the hub-and-lug envelope: the bore wall is at least the
minimum the `.obend` package states, everywhere along the bore. -/
theorem fidget_bore_wall_sound (px py pz : Int) (hCav : inSolid px py pz fidgetParams.cavity)
    (qx qy qz : Int)
    (hq : WithinBox (fidgetParams.lat fidgetParams.minWall) (fidgetParams.lat fidgetParams.minWall) 0
      px py pz qx qy qz) :
    inSolid qx qy qz fidgetParams.outer := by
  have hBox := frepCylZ_in_box _ _ _ _ _ px py pz hCav
  have hCheck : kdAll (wallLeaf fidgetParams.outer fidgetParams.cavity
      (fidgetParams.lat fidgetParams.minWall) (fidgetParams.lat fidgetParams.minWall) 0) 40
      (cylBox (-(fidgetParams.lat fidgetParams.boreX : Int)) 0 (fidgetParams.lat fidgetParams.boreR) 0
        (fidgetParams.lat fidgetParams.hubH)) = true := by
    native_decide
  exact checkWall_sound _ _ _ _ _ 40 _ hCheck px py pz hBox hCav qx qy qz hq

#assert_compiled fidget_bore_wall_sound

/-! ## 5. The tool path: generated, certified against the solid, posted

Generation is untrusted integer code: contours at the tool offset around hub ∪ lug for each
Z level (vertical axis), then four 3+2 passes over the top edge with the axis tilted 36.87°
outward, one per quadrant. Directions come from rational points of the unit circle, so no
trigonometry enters. The certificate is the gouge check over every lattice point of every
segment the control will interpolate, including plunges and retracts. -/

/-- Rational points on the unit circle, `((M²-k², 2kM), M²+k²)` for `k < M`, turned through the four
quadrants: `4M` exact directions in angular order. -/
@[expose] def circleDirs (M : Nat) : List (Int × Int × Int) :=
  let q0 := (List.range M).map fun (i : Nat) =>
    let m : Int := M
    let k : Int := i
    (m * m - k * k, 2 * k * m, m * m + k * k)
  let rot (d : Int × Int × Int) : Int × Int × Int := (-d.2.1, d.1, d.2.2)
  let q1 := q0.map rot
  let q2 := q1.map rot
  let q3 := q2.map rot
  q0 ++ q1 ++ q2 ++ q3

/-- `round(ρ·a/c)`. -/
@[expose] def roundMul (ρ a c : Int) : Int := (2 * ρ * a + c) / (2 * c)

/-- Smallest radius `ρ ≥ ρ0` along direction `d` whose point is at least `clear` from `(ox, oy)`. -/
@[expose] def searchRho (ox oy : Int) (clear : Nat) (d : Int × Int × Int) : Nat → Int → Int
  | 0, ρ => ρ
  | fuel + 1, ρ =>
    let px := roundMul ρ d.1 d.2.2
    let py := roundMul ρ d.2.1 d.2.2
    if (clear : Int) * clear ≤ (px - ox) * (px - ox) + (py - oy) * (py - oy) then ρ
    else searchRho ox oy clear d fuel (ρ + 1)

/-- The quadrant (0 … 3) whose axis `+X, +Y, -X, -Y` is nearest to direction `d`. -/
@[expose] def nearestQuadrant (d : Int × Int × Int) : Nat :=
  let a := d.1
  let b := d.2.1
  if (b.natAbs : Int) ≤ a then 0 else if (a.natAbs : Int) ≤ b then 1
  else if (b.natAbs : Int) ≤ -a then 2 else 3

/-- Tool axis tilted 36.87° (a 3-4-5 triangle) outward over quadrant `q`. -/
@[expose] def tiltAxis : Nat → ToolAxis
  | 0 => ⟨3, 0, 4, 5⟩
  | 1 => ⟨0, 3, 4, 5⟩
  | 2 => ⟨-3, 0, 4, 5⟩
  | _ => ⟨0, -3, 4, 5⟩

@[expose] def vertAxis : ToolAxis := ⟨0, 0, 1, 1⟩

@[expose] def FidgetParams.clearanceZ (p : FidgetParams) : Int := p.lat p.hubH + p.lat p.clearAbove

/-- The contour around hub ∪ lug at the tool offset (radius plus stock), closed. -/
@[expose] def FidgetParams.contour (p : FidgetParams) : List (Int × Int) :=
  let off := p.lat p.toolOffset
  let pts := (circleDirs 64).map fun d =>
    let ρ := searchRho (p.lat p.lugX) 0 (p.lat p.lugR + off) d 400 ((p.lat p.hubR : Int) + off)
    (roundMul ρ d.1 d.2.2, roundMul ρ d.2.1 d.2.2)
  pts ++ pts.take 1

/-- Tip heights of the Z-level passes, top down to the base. -/
@[expose] def FidgetParams.zLevels (p : FidgetParams) : List Int :=
  (List.range (p.hubH / p.stepDown)).map fun (i : Nat) =>
    (p.lat p.hubH : Int) - ((i : Int) + 1) * (p.lat p.stepDown : Int)

@[expose] def FidgetParams.zPass (p : FidgetParams) (z : Int) : CamPass :=
  { axis := vertAxis, pts := p.contour.map fun q => (q.1, q.2, z) }

/-- The top-edge pass over quadrant `q`: ball centre at the tool offset from the edge along the
tilted axis, pushed out radially where the lug is. -/
@[expose] def FidgetParams.tiltPass (p : FidgetParams) (q : Nat) : CamPass :=
  let all := circleDirs 64
  let src := if q == 0 then all.drop (3 * 64) ++ all.take (3 * 64) else all
  let u := tiltAxis q
  let off := p.lat p.toolOffset
  let r : Int := p.lat p.toolR
  let dirs := src.filter fun d => nearestQuadrant d == q
  { axis := u
  , pts := dirs.map fun d =>
      let ρc := searchRho (p.lat p.lugX) 0 (p.lat p.lugR + off) d 400 ((p.lat p.hubR : Int) + 3 * off / 5)
      let cx := roundMul ρc d.1 d.2.2
      let cy := roundMul ρc d.2.1 d.2.2
      let cz := (p.lat p.hubH : Int) + 4 * off / 5
      (cx - r * u.ux / u.n, cy - r * u.uy / u.n, cz - r * u.uz / u.n) }

@[expose] def FidgetParams.passes (p : FidgetParams) : List CamPass :=
  p.zLevels.map p.zPass ++ [p.tiltPass 0, p.tiltPass 1, p.tiltPass 2, p.tiltPass 3]

/-- Every lattice point the tip passes through in a pass under the post's moves: plunge from the
clearance plane, the cut polyline, retract to the clearance plane. -/
@[expose] def FidgetParams.certPath (p : FidgetParams) (pass : CamPass) : List CLPoint :=
  match pass.pts with
  | [] => []
  | q :: rest =>
    let l := (q :: rest).getLast (List.cons_ne_nil _ _)
    (densifyPolyline ((q.1, q.2.1, p.clearanceZ) :: q :: rest ++ [(l.1, l.2.1, p.clearanceZ)])).map
      fun t => ⟨t.1, t.2.1, t.2.2, pass.axis⟩

/-! ## 5b. The object the `cam-gouge@1` judge checks

The tool path's no-gouge statement is a certificate, not a search: the moves below are the
object, `apps/fidget-cam/cam/impeller_5axis.cert` (written once by `lean/tools/emitcam`) is the
certificate, and `Obend.Apps.FidgetCamCert` checks it. This module only states the object and the
facts the theorem there needs (the part lies in its box; every certified move carries its pass's
axis). -/

/-- A Z-cylinder's rational bounding box. -/
@[expose] def cylBoxQ (cx cy : Int) (r : Nat) (z0 z1 : Int) : QBox :=
  ⟨⟨(cx : Rat) - ((r : Int) : Rat), (cx : Rat) + ((r : Int) : Rat)⟩,
   ⟨(cy : Rat) - ((r : Int) : Rat), (cy : Rat) + ((r : Int) : Rat)⟩, ⟨(z0 : Rat), (z1 : Rat)⟩⟩

@[expose] def QBox.hullQ (A B : QBox) : QBox :=
  ⟨⟨min A.x.lo B.x.lo, max A.x.hi B.x.hi⟩, ⟨min A.y.lo B.y.lo, max A.y.hi B.y.hi⟩,
   ⟨min A.z.lo B.z.lo, max A.z.hi B.z.hi⟩⟩

theorem rat_abs_le_of_sq_le (a R : Rat) (hR : 0 ≤ R) (h : a * a ≤ R * R) : -R ≤ a ∧ a ≤ R := by
  have key : ∀ b : Rat, R < b → R * R < b * b := by
    intro b hb
    have h1 := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hb) hR
    have h2 := Rat.mul_lt_mul_of_pos_right hb (by grind : (0 : Rat) < b)
    grind
  constructor
  · refine Rat.not_lt.mp fun hlt => ?_
    have := key (-a) (by grind)
    rw [rat_neg_sq] at this
    grind
  · refine Rat.not_lt.mp fun hlt => ?_
    have := key a hlt
    grind

theorem frepCylZ_in_boxQ (cx cy : Int) (r : Nat) (z0 z1 : Int) (x y z : Rat)
    (h : evalFRepQ x y z (frepCylZ cx cy r z0 z1) ≤ 0) : (cylBoxQ cx cy r z0 z1).contains x y z := by
  unfold frepCylZ at h
  simp only [evalFRepQ] at h
  have hR : (0 : Rat) ≤ ((r : Int) : Rat) := by exact_mod_cast (Int.natCast_nonneg r)
  have hrr : ((((r : Int) * r : Int)) : Rat) = ((r : Int) : Rat) * ((r : Int) : Rat) := by grind
  rw [hrr] at h
  have hx2 := rat_sq_nonneg' (x - (cx : Rat))
  have hy2 := rat_sq_nonneg' (y - (cy : Rat))
  have hmax : (x - cx) * (x - cx) + (y - cy) * (y - cy) - ((r : Int) : Rat) * ((r : Int) : Rat) ≤ 0 ∧
      ((z0 : Rat) - z) ≤ 0 ∧ (z - (z1 : Rat)) ≤ 0 := by grind
  have bx := rat_abs_le_of_sq_le (x - cx) _ hR (by grind)
  have by' := rat_abs_le_of_sq_le (y - cy) _ hR (by grind)
  unfold cylBoxQ QBox.contains QIv.contains
  dsimp only
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> grind

theorem hullQ_left (A B : QBox) (x y z : Rat) (h : A.contains x y z) : (QBox.hullQ A B).contains x y z := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := h
  unfold QBox.hullQ QBox.contains QIv.contains
  dsimp only
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> grind

theorem hullQ_right (A B : QBox) (x y z : Rat) (h : B.contains x y z) : (QBox.hullQ A B).contains x y z := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := h
  unfold QBox.hullQ QBox.contains QIv.contains
  dsimp only
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> grind

@[expose] def FidgetParams.partBoxQ (p : FidgetParams) : QBox :=
  QBox.hullQ (cylBoxQ 0 0 (p.lat p.hubR) 0 (p.lat p.hubH))
    (cylBoxQ (p.lat p.lugX) 0 (p.lat p.lugR) 0 (p.lat p.hubH))

/-- Every rational point of the part lies in `partBoxQ`, for any parameters. -/
theorem FidgetParams.part_in_boxQ (p : FidgetParams) (x y z : Rat) (h : evalFRepQ x y z p.part ≤ 0) :
    p.partBoxQ.contains x y z := by
  unfold FidgetParams.part at h
  simp only [evalFRepQ] at h
  have hu : evalFRepQ x y z p.outer ≤ 0 := by grind
  unfold FidgetParams.outer at hu
  simp only [evalFRepQ] at hu
  unfold FidgetParams.partBoxQ
  have : evalFRepQ x y z (frepCylZ 0 0 (p.lat p.hubR) 0 (p.lat p.hubH)) ≤ 0 ∨
      evalFRepQ x y z (frepCylZ (p.lat p.lugX) 0 (p.lat p.lugR) 0 (p.lat p.hubH)) ≤ 0 := by grind
  rcases this with h1 | h1
  · exact hullQ_left _ _ x y z (frepCylZ_in_boxQ _ _ _ _ _ x y z h1)
  · exact hullQ_right _ _ x y z (frepCylZ_in_boxQ _ _ _ _ _ x y z h1)

/-- The moves of a pass the control interpolates: consecutive certified points. -/
@[expose] def FidgetParams.passMoves (p : FidgetParams) (pass : CamPass) : List (Pt3 × Pt3) :=
  ((p.certPath pass).zip (p.certPath pass).tail).map fun m => ((m.1.x, m.1.y, m.1.z), (m.2.x, m.2.y, m.2.z))

/-- The certificate's resolution: the same part on a 5 µm lattice, so the k-d boxes can shrink below
the 100 µm of the tool path without leaving the integers. -/
@[expose] def camParams : FidgetParams := { fidgetParams with unit := 5 }

/-- Tool-path lattice units (100 µm) to certificate units (5 µm). -/
@[expose] def camScale : Int := 20

@[expose] def scaleMove (m : Pt3 × Pt3) : Pt3 × Pt3 :=
  ((camScale * m.1.1, camScale * m.1.2.1, camScale * m.1.2.2),
   (camScale * m.2.1, camScale * m.2.2.1, camScale * m.2.2.2))

/-- The object of `cam-gouge@1` for the fidget program: each pass's moves on its axis, in 5 µm
units, against the part and the cutter at 5 µm. -/
@[expose] def fidgetCamObj : CamGougeObj :=
  { part := camParams.part
  , box := camParams.partBox
  , toolR := camParams.lat camParams.toolR
  , shankLen := camParams.lat camParams.shankLen
  , chunks := fidgetParams.passes.map fun pass =>
      { axis := pass.axis, moves := (fidgetParams.passMoves pass).map scaleMove } }

theorem FidgetParams.partBox_toQ (p : FidgetParams) : p.partBox.toQ = p.partBoxQ := by
  simp only [FidgetParams.partBox, FidgetParams.partBoxQ, Box3D.hull, QBox.hullQ, cylBox, cylBoxQ,
    Box3D.toQ, intCast_min', intCast_max', Rat.intCast_sub, Rat.intCast_add]

theorem FidgetParams.certPath_axis (p : FidgetParams) (pass : CamPass) (c : CLPoint)
    (h : c ∈ p.certPath pass) : c.axis = pass.axis := by
  unfold FidgetParams.certPath at h
  split at h
  · cases h
  · obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
    rfl

@[expose] def FidgetParams.postConfig (p : FidgetParams) : PostConfig :=
  { clearanceZ := p.clearanceZ, plungeFeed := p.plungeFeed, cutFeed := p.cutFeed
  , spindleRpm := p.rpm, tool := 1, unitMicron := p.unit }

/-- The program `apps/fidget-cam/build/impeller_5axis.ngc` is this string. -/
@[expose] def impeller5AxisNgc : String :=
  postNgc fidgetParams.postConfig "Objective Bend fidget part: Z-level contours and 3+2 top-edge passes"
    fidgetParams.passes

/-- The posted moves are rotary-safe (an instance of `postMoves_rotarySafe`, which holds for every
list of passes). -/
theorem fidget_post_rotarySafe :
    movesRotarySafe fidgetParams.postConfig.clearanceZ (postMoves fidgetParams.postConfig fidgetParams.passes) = true :=
  postMoves_rotarySafe _ _

/-! ## 6. OpenUSD `LIVERPS` over the same value the `.obend` override composes

The bore radius is authored twice: `2.0 mm` as a local opinion (`ConformalBoreLocalOverride`) and
`1.6 mm` through a reference (`HelicalChannelReferenceSpec`). Lowered through `composePrimToTerm`,
the local opinion wins in either layer order, and it is the value the `.obend` composition reduced. -/
/-- The cooling channel's prim, authoring the bore radius through arc `arc`. -/
@[expose] def boreLayer (name : String) (arc : UsdArcKind) (v : Term) : SdfLayer :=
  { layerId := name
  , prims := [{ path := ["Factory", "ImpellerAssy", "CoolingChannel"], arc := arc
              , fields := [("boreRadiusUm", v)] }] }

theorem fidgetCam_liverps_bore_radius :
    Steps (.get (composePrimToTerm
        [boreLayer "strongLayer" .localArc FidgetCoolingChannel.boreRadius_val,
         boreLayer "weakLayer" .referencesArc FidgetCoolingChannel.referenceBoreRadius_val]
        ["Factory", "ImpellerAssy", "CoolingChannel"] (.record [])) "boreRadiusUm")
      FidgetCoolingChannel.boreRadius_val ∧
    Steps (.get (composePrimToTerm
        [boreLayer "weakLayer" .referencesArc FidgetCoolingChannel.referenceBoreRadius_val,
         boreLayer "strongLayer" .localArc FidgetCoolingChannel.boreRadius_val]
        ["Factory", "ImpellerAssy", "CoolingChannel"] (.record [])) "boreRadiusUm")
      FidgetCoolingChannel.boreRadius_val ∧
    natOfTerm FidgetCoolingChannel.boreRadius_val = fidgetParams.boreR := by
  have hv : FidgetCoolingChannel.boreRadius_val = .nat 2000 := rfl
  have hr : FidgetCoolingChannel.referenceBoreRadius_val = .nat 1600 := rfl
  have hLt : UsdArcKind.referencesArc.strength < UsdArcKind.localArc.strength := by decide +kernel
  have hDom := liverps_stronger_arc_dominates_term
    ["Factory", "ImpellerAssy", "CoolingChannel"] "boreRadiusUm"
    (.nat 2000) (.nat 1600) UsdArcKind.localArc UsdArcKind.referencesArc [] hLt
  unfold boreLayer
  rw [hv, hr]
  refine ⟨?_, ?_, by decide +kernel⟩
  · simpa [Obend.Logic.openTerm, Obend.Core.Term.Term.substitute] using hDom.1
  · simpa [Obend.Logic.openTerm, Obend.Core.Term.Term.substitute] using hDom.2.1

/-! ## 7. RTL: the voxel evaluator compiled from the part's tape -/

/-- Compile a single `SsaTapeOp` into an `RtlExpr` reading `(in_x, in_y, in_z)` from ports `0, 1, 2`
and earlier SSA registers at `wireOffset + r`. -/
@[expose] def compileSsaOpToRtlExpr (wireOffset : Nat) : SsaTapeOp → RtlExpr
  | .const c        => .const (BitVec.ofInt 64 c)
  | .varX           => .inputPort 0
  | .varY           => .inputPort 1
  | .varZ           => .inputPort 2
  | .neg r          => .alu .sub (.const 0#64) (.wireRef (wireOffset + r))
  | .add r1 r2      => .alu .add (.wireRef (wireOffset + r1)) (.wireRef (wireOffset + r2))
  | .sub r1 r2      => .alu .sub (.wireRef (wireOffset + r1)) (.wireRef (wireOffset + r2))
  | .mul r1 r2      => .alu .mul (.wireRef (wireOffset + r1)) (.wireRef (wireOffset + r2))
  | .minUnion r1 r2 =>
    let w1 := RtlExpr.wireRef (wireOffset + r1)
    let w2 := RtlExpr.wireRef (wireOffset + r2)
    .mux (.alu .slt w2 w1) w2 w1
  | .maxInter r1 r2 =>
    let w1 := RtlExpr.wireRef (wireOffset + r1)
    let w2 := RtlExpr.wireRef (wireOffset + r2)
    .mux (.alu .slt w1 w2) w2 w1

@[expose] def compileSsaTapeToRtlWires (wireOffset : Nat) (tag : String) (tape : List SsaTapeOp) :
    List WireAssign :=
  tape.zipIdx.map fun (op, idx) =>
    { wireIdx := wireOffset + idx
    , name    := s!"{tag}_op_{idx}"
    , expr    := compileSsaOpToRtlExpr wireOffset op }

/-- A box inside the hub, one at the lug tip, one across the bore (lattice units). -/
@[expose] def impellerCenterBox : Box3D := { xIv := ⟨40, 60⟩, yIv := ⟨-10, 10⟩, zIv := ⟨30, 50⟩ }
@[expose] def impellerBossBox : Box3D := { xIv := ⟨112, 124⟩, yIv := ⟨-5, 5⟩, zIv := ⟨30, 50⟩ }
@[expose] def impellerBoreBox : Box3D := { xIv := ⟨-50, -30⟩, yIv := ⟨-8, 8⟩, zIv := ⟨30, 50⟩ }

@[expose] def compactFor (B : Box3D) : List SsaTapeOp :=
  compactSsaTape (pruneSsaTapeForBox B impellerSsaTape) (impellerSsaTape.length - 1)

@[expose] def impellerCenterCompactedTape : List SsaTapeOp := compactFor impellerCenterBox
@[expose] def impellerBossCompactedTape : List SsaTapeOp := compactFor impellerBossBox
@[expose] def impellerBoreCompactedTape : List SsaTapeOp := compactFor impellerBoreBox

/-- A pruned and compacted tape agrees with the solid on every point of its box. -/
theorem compactFor_sound (B : Box3D) (x y z : Int) (h : B.contains x y z) :
    evalSsaTape x y z (compactFor B) ((compactFor B).length - 1) = evalFRepPoint x y z fidgetParams.part := by
  unfold compactFor impellerSsaTape
  exact (FRepExpr.toTape_prune_compact_eval B x y z fidgetParams.part h).1

/-- The voxel evaluator: the full tape and the three compacted tapes, the inside test, and a gouge
flag for a vertical ball end mill of the certified grown radius with its tip at `(in_tx, in_ty,
in_tz)` (lattice units throughout). The proof is `Obend.Apps.FidgetCamCert`; this module is a
fast re-check of tool positions. -/
@[expose] def fidgetImpellerVoxelCamRtlModule : RtlModule :=
  let fullWires   := compileSsaTapeToRtlWires 0 "full" impellerSsaTape
  let off1        := fullWires.length
  let centerWires := compileSsaTapeToRtlWires off1 "center" impellerCenterCompactedTape
  let off2        := off1 + centerWires.length
  let bossWires   := compileSsaTapeToRtlWires off2 "boss" impellerBossCompactedTape
  let off3        := off2 + bossWires.length
  let boreWires   := compileSsaTapeToRtlWires off3 "bore" impellerBoreCompactedTape
  let b           := off3 + boreWires.length
  let rootFull    := off1 - 1
  let rootCenter  := off2 - 1
  let rootBoss    := off3 - 1
  let rootBore    := b - 1
  let r : Nat := fidgetParams.lat fidgetParams.toolR
  let rg : Nat := r + 1
  let camWires : List WireAssign :=
    [ { wireIdx := b + 0, name := "in_solid_3d",
        expr := .mux (.alu .slt (.const 0#64) (.wireRef rootFull)) (.const 0#64) (.const 1#64) }
    , { wireIdx := b + 1, name := "dx_tool", expr := .alu .sub (.inputPort 0) (.inputPort 3) }
    , { wireIdx := b + 2, name := "dy_tool", expr := .alu .sub (.inputPort 1) (.inputPort 4) }
    , { wireIdx := b + 3, name := "dz_tool",
        expr := .alu .sub (.alu .sub (.inputPort 2) (.inputPort 5)) (.const (BitVec.ofNat 64 r)) }
    , { wireIdx := b + 4, name := "tool_sdf",
        expr := .alu .sub
          (.alu .add (.alu .add (.alu .mul (.wireRef (b + 1)) (.wireRef (b + 1)))
                                (.alu .mul (.wireRef (b + 2)) (.wireRef (b + 2))))
                     (.alu .mul (.wireRef (b + 3)) (.wireRef (b + 3))))
          (.const (BitVec.ofNat 64 (rg * rg))) }
    , { wireIdx := b + 5, name := "tool_clear", expr := .alu .slt (.const 0#64) (.wireRef (b + 4)) }
    , { wireIdx := b + 6, name := "no_gouge_ok",
        expr := .mux (.wireRef (b + 0)) (.wireRef (b + 5)) (.const 1#64) } ]
  { name := "fidget_impeller_voxel_cam"
  , inputNames := [ "in_x", "in_y", "in_z", "in_tx", "in_ty", "in_tz" ]
  , wires := fullWires ++ centerWires ++ bossWires ++ boreWires ++ camWires
  , regs :=
      [ { regIdx := 0, name := "reg_voxel_eval_cycles", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .alu .add (.regRead 0) (.const 1#64) }
      , { regIdx := 1, name := "reg_solid_voxel_count", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .mux (.wireRef (b + 0)) (.alu .add (.regRead 1) (.const 1#64)) (.regRead 1) }
      , { regIdx := 2, name := "reg_gouge_violations", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .mux (.wireRef (b + 6)) (.regRead 2) (.alu .add (.regRead 2) (.const 1#64)) } ]
  , outputs :=
      [ { name := "out_frep_full",           expr := .wireRef rootFull }
      , { name := "out_frep_center_pruned",  expr := .wireRef rootCenter }
      , { name := "out_frep_boss_pruned",    expr := .wireRef rootBoss }
      , { name := "out_frep_bore_pruned",    expr := .wireRef rootBore }
      , { name := "out_in_solid_3d",         expr := .wireRef (b + 0) }
      , { name := "out_tool_sdf",            expr := .wireRef (b + 4) }
      , { name := "out_no_gouge_ok",         expr := .wireRef (b + 6) }
      , { name := "out_voxel_eval_cycles",   expr := .regRead 0 }
      , { name := "out_solid_voxel_count",   expr := .regRead 1 }
      , { name := "out_gouge_violations",    expr := .regRead 2 } ] }

@[expose] def mkFidgetCamRtlInputs (x y z tx ty tz : Int) : Nat → BitVec 64
  | 0 => BitVec.ofInt 64 x
  | 1 => BitVec.ofInt 64 y
  | 2 => BitVec.ofInt 64 z
  | 3 => BitVec.ofInt 64 tx
  | 4 => BitVec.ofInt 64 ty
  | 5 => BitVec.ofInt 64 tz
  | _ => 0#64

/-- The emitted module passes the RTL and BEL checks, agrees with the solid at a point in each box,
reports the bore as empty, and flags a tool tip placed inside the lug. Values the kernel computed
(an `example`): the theorem relating the RTL to `evalFRepPoint` for every input is not written. -/
example :
    checkRtlModule fidgetImpellerVoxelCamRtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels fidgetImpellerVoxelCamRtlModule) = true ∧
    (evalModuleOutputs fidgetImpellerVoxelCamRtlModule (mkFidgetCamRtlInputs 50 0 40 0 124 60)
        (fun _ => 0#64)).lookup "out_frep_full" =
      some (BitVec.ofInt 64 (evalFRepPoint 50 0 40 fidgetParams.part)) ∧
    (evalModuleOutputs fidgetImpellerVoxelCamRtlModule (mkFidgetCamRtlInputs 120 0 40 0 124 60)
        (fun _ => 0#64)).lookup "out_frep_boss_pruned" =
      some (BitVec.ofInt 64 (evalFRepPoint 120 0 40 fidgetParams.part)) ∧
    (evalModuleOutputs fidgetImpellerVoxelCamRtlModule (mkFidgetCamRtlInputs (-40) 0 40 0 124 60)
        (fun _ => 0#64)).lookup "out_in_solid_3d" = some 0#64 ∧
    (evalModuleOutputs fidgetImpellerVoxelCamRtlModule (mkFidgetCamRtlInputs 120 0 40 120 0 30)
        (fun _ => 0#64)).lookup "out_no_gouge_ok" = some 0#64 := by
  decide +kernel

/-! ## 8. The composed books through the generic RTL compiler -/

example :
    (match compileBookToRtl "fidget_impeller_cam_top" FidgetImpellerTop.liverpsImpellerCamTop_book,
           compileBookToRtl "fidget_mounting_boss" FidgetMountingBoss.stiffenedMountingBoss_book with
     | some mTop, some mBoss =>
       checkRtlModule mTop && checkRtlModule mBoss &&
       ((evalModuleOutputs mTop (fun _ => 1#64) (fun _ => 0#64)).lookup "out_toolOffsetUm" == some 2400#64) &&
       ((evalModuleOutputs mBoss (fun _ => 1#64) (fun _ => 0#64)).lookup "out_lugReachUm" == some 12500#64)
     | _, _ => false) = true := by
  decide +kernel

end Obend.Apps.FidgetCam
end
