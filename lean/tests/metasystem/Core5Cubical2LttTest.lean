import Obend.Core.Cubical2LTT
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/Core5Cubical2LttTest.lean` — Verification & `#tooth` Suite for `Obend.Core.Cubical2LTT`

End-to-end inhabitedness witnesses, refutations, cross-organ `Core5` welds, `#tooth` mutation kills,
and strict `0 Classical.choice` / `0 sorryAx` / `0` closed-theorem audit covering:
1. `CofibLUT16` (`BitVec 16`) Cavallo–Sattler 4-variable cofibration lattice, SWAR `revDim` / `substDim`,
   semantic completeness (`entails_iff_pointwise`), ternary interior `evalSubcube`, and
   `CofibSyntax4.boundary_ne_top_at_interior` (`∂𝕀 ≠ 𝕀` at `CubePt4.interior4`).
2. `Cube1`, `Cube2`, `OpenBox2`, `hcomLid`, `hcomFill2`, and `coeKan` instantiated across:
   - `TorsorPt` path groupoids (`KanGroupoid`),
   - `EnclosureVec2` 2D Lipschitz enclosure tubes (`evalAffineBox2`), and
   - `PackagedStepSys` quantitative `Simulates` machines (`hcomLid_stepSys_trace_safe`).
3. Realizability 2LTT (`StageGrade`, `realizer_stage_erases_zero_ghosts`) and quantitative
   bidirectional `AdapTT` adapters (`QuantAdapter`, `IsoAdapter`, `AdapterChain`, `fuseAdapters_sound`,
   `castAdapter_id_elim`, `castAdapter_inv_cancel`, `fuseAdapters_gradedTriple`).
4. Cross-organ `Core5` welds to `Obend.Category.Refines` (`adapter_induces_graded_refines`),
   `Obend.Logic.SuperRefines` (`adapter_superRefines_vertical_weld`), and
   `Obend.Repair.DeltaLensRenew` (`hcom_repairs_broken_commuting_square`).
5. Eight `#tooth` mutation kills + `#assert_axioms_tree` + strict `0 Classical.choice` audit.
-/

namespace Obend.Tests.Core5Cubical2LttTest

open Obend.Category
open Obend.Logic
open Obend.Repair
open Obend.Core.Cubical2LTT

set_option autoImplicit false

-- ============================================================================
-- 1. `CofibLUT16` Lattice, SWAR Operations & Interior Non-Collapse (`∂𝕀 ≠ 𝕀`)
-- ============================================================================

def openBoxCofib : CofibLUT16 :=
  ((CofibLUT16.dimEq0 0).join (CofibLUT16.dimEq1 0)).join (CofibLUT16.dimEq0 1)

def originVtx : Vertex4 := ⟨false, false, false, false⟩
def lidFreeVtx : Vertex4 := ⟨false, true, false, false⟩
def topRightVtx : Vertex4 := ⟨true, true, false, false⟩

#guard CofibLUT16.evalCofib openBoxCofib originVtx == true
#guard CofibLUT16.evalCofib openBoxCofib lidFreeVtx == true
#guard CofibLUT16.evalCofib openBoxCofib topRightVtx == true
-- Refutation: dim 0 = 0 does NOT entail dim 0 = 1, and open-box (i₀=0 ∨ i₁=0) misses (1, 1, 0, 0)
#guard (CofibLUT16.dimEq0 0).entails (CofibLUT16.dimEq1 0) == false
#guard CofibLUT16.evalCofib ((CofibLUT16.dimEq0 0).join (CofibLUT16.dimEq0 1)) topRightVtx == false

-- SWAR De Morgan reversal & substitution checks
#guard CofibLUT16.revDim 0 (CofibLUT16.dimEq0 0) == CofibLUT16.dimEq1 0
#guard CofibLUT16.revDim 2 (CofibLUT16.dimEq1 2) == CofibLUT16.dimEq0 2
#guard CofibLUT16.substDim 1 false (CofibLUT16.dimEq0 1) == CofibLUT16.top
#guard CofibLUT16.substDim 1 true (CofibLUT16.dimEq0 1) == CofibLUT16.bot

-- Interior face check: `dimEq0 0` holds on face `(0, *, *, *)`, fails at `(*, *, *, *)`
#guard CofibLUT16.evalSubcube (CofibLUT16.dimEq0 0) ⟨.ep0, .interior, .interior, .interior⟩ == true
#guard CofibLUT16.evalSubcube (CofibLUT16.dimEq0 0) CubePt4.interior4 == false
#guard (CofibSyntax4.join (.dim0 0) (.dim1 0)).evalCubePt CubePt4.interior4 == false
#guard CofibSyntax4.top.evalCubePt CubePt4.interior4 == true

example (φ ψ χ : CofibLUT16) (d : Fin 4) (pt : Vertex4) :
    φ.meet (ψ.join χ) = (φ.meet ψ).join (φ.meet χ) ∧
    φ.join (ψ.meet χ) = (φ.join ψ).meet (φ.join χ) ∧
    φ.meet (φ.join ψ) = φ ∧
    φ.entails φ = true ∧
    CofibLUT16.evalSubcube φ (CubePt4.ofVertex pt) = CofibLUT16.evalCofib φ pt ∧
    (CofibSyntax4.join (.dim0 d) (.dim1 d)).evalCubePt CubePt4.interior4 = false :=
  ⟨CofibLUT16.meet_distrib_join φ ψ χ,
   CofibLUT16.join_distrib_meet φ ψ χ,
   CofibLUT16.absorb_meet_join φ ψ,
   CofibLUT16.entails_refl φ,
   CofibLUT16.evalSubcube_ofVertex φ pt,
   (CofibSyntax4.boundary_ne_top_at_interior d).1⟩

example : (CofibLUT16.dimEq0 0).entails openBoxCofib = true :=
  (CofibLUT16.entails_iff_pointwise (CofibLUT16.dimEq0 0) openBoxCofib).mpr fun pt h => by
    rw [openBoxCofib, CofibLUT16.evalCofib_join, CofibLUT16.evalCofib_join, h,
        Bool.true_or, Bool.true_or]

-- ============================================================================
-- 2. Cubical Paths, 2-Cubes, Kan `hcom2` & `coeKan` Across 3 Concrete Carriers
-- ============================================================================

-- Carrier 1: `TorsorPt` groupoid open box (`10 -> 17` bottom `+7`, `10 -> 4` left `-6`, `17 -> 25` right `+8`)
def t00 : TorsorPt := ⟨10⟩
def t10 : TorsorPt := ⟨17⟩
def t01 : TorsorPt := ⟨4⟩
def t11 : TorsorPt := ⟨25⟩

def shiftBot : TorsorShift t00 t10 := ⟨7, rfl⟩
def shiftLeft : TorsorShift t00 t01 := ⟨-6, rfl⟩
def shiftRight : TorsorShift t10 t11 := ⟨8, rfl⟩

def torsorBox : OpenBox2 TorsorPt := ⟨t00, t10, t01, t11, shiftBot, shiftLeft, shiftRight⟩
def torsorSquare : Cube2 TorsorPt := hcomFill2 torsorBox

-- Missing top lid synthesized by `hcomLid` has exact shift `6 + 7 + 8 = 21` (`4 + 21 = 25`)
#guard (hcomLid torsorBox).ep0 == t01
#guard (hcomLid torsorBox).ep1 == t11
#guard (hcomLid torsorBox).path.delta == 21
#guard checkSquareCoherent torsorSquare.toBoundary2 == true

-- Refutation: mismatched corner endpoints rejected by `checkSquareCoherent` and `OpenBox2.ofWalls?`
def mismatchedBoundary : Boundary2 TorsorPt :=
  { top := Cube1.refl t00, bottom := torsorBox.bottom, left := torsorBox.left, right := torsorBox.right }

#guard checkSquareCoherent mismatchedBoundary == false
#guard (OpenBox2.ofWalls? torsorBox.bottom torsorBox.left torsorBox.right).isSome == true
#guard (OpenBox2.ofWalls? torsorBox.bottom (Cube1.refl t11) torsorBox.right).isSome == false

example :
    (hcomFill2 torsorBox).bottom = torsorBox.bottom ∧
    (hcomFill2 torsorBox).left = torsorBox.left ∧
    (hcomFill2 torsorBox).right = torsorBox.right ∧
    (hcomFill2 torsorBox).top = hcomLid torsorBox := by
  have h := hcomFill2_agrees_on_open_box_boundary torsorBox
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

def shiftStep3 : TorsorShift t11 ⟨28⟩ := ⟨3, rfl⟩

example :
    checkSquareCoherent
      (compPath_assoc_up_to_square (A := TorsorPt) shiftBot shiftRight shiftStep3).toBoundary2 = true ∧
    checkSquareCoherent (path_inv_cancel_square (A := TorsorPt) shiftBot).1.toBoundary2 = true ∧
    checkSquareCoherent (path_inv_cancel_square (A := TorsorPt) shiftBot).2.toBoundary2 = true :=
  ⟨Cube2.coherent_of_cube2 _, Cube2.coherent_of_cube2 _, Cube2.coherent_of_cube2 _⟩

-- Carrier 2: `EnclosureVec2` 2D Lipschitz enclosure tubes + `evalAffineBox2`
def enc00 : EnclosureVec2 := ⟨0, 0, 1⟩
def enc10 : EnclosureVec2 := ⟨6, 4, 2⟩
def enc01 : EnclosureVec2 := ⟨2, 5, 1⟩
def enc11 : EnclosureVec2 := ⟨8, 7, 3⟩

def tubeBot : EnclosureTube1 enc00 enc10 := ⟨EnclosureVec2.midpoint enc00 enc10, 12, 10, by decide⟩
def tubeLeft : EnclosureTube1 enc00 enc01 := ⟨EnclosureVec2.midpoint enc00 enc01, -5, 7, by decide⟩
def tubeRight : EnclosureTube1 enc10 enc11 := ⟨EnclosureVec2.midpoint enc10 enc11, 9, 6, by decide⟩

def encBox : OpenBox2 EnclosureVec2 := ⟨enc00, enc10, enc01, enc11, tubeBot, tubeLeft, tubeRight⟩
def encFilled : Cube2 EnclosureVec2 := hcomFill2 encBox

-- Lid work = `-(-5) + (12 + 9) = 26`, variation bound = `7 + (10 + 6) = 23`
#guard (hcomLid encBox).path.work == 26
#guard (hcomLid encBox).path.variationBound == 23
#guard encFilled.eval2 .interior .interior == encFilled.center

example (i j : Int) :
    let u0 := fun s : Int => 10 + 4 * s
    let w0 := fun s : Int => 10 - 2 * s
    let w1 := fun s : Int => 14 + 6 * s
    EnclosureVec2.evalAffineBox2 u0 w0 w1 i 0 = u0 i ∧
    EnclosureVec2.evalAffineBox2 u0 w0 w1 0 j = w0 j ∧
    EnclosureVec2.evalAffineBox2 u0 w0 w1 1 j = w1 j := by
  intro u0 w0 w1
  exact EnclosureVec2.evalAffineBox2_boundary (u0 := u0) (w0 := w0) (w1 := w1)
    (by decide) (by decide) i j

-- Carrier 3: `PackagedStepSys` quantitative `Simulates` open box (100% constructive `ScalarObs`)
structure ScalarObs where
  val : Int
  deriving DecidableEq, Repr

private theorem int_sub_triangle_eq (a b c : Int) : a - c = (a - b) + (b - c) := by
  calc a - c
    _ = (a + (-b + b)) + -c := by rw [Int.add_left_neg, Int.add_zero, ← Int.sub_eq_add_neg]
    _ = (a - b) + (b - c) := by
      rw [← Int.add_assoc a (-b) b, Int.add_assoc (a + -b) b (-c),
          ← Int.sub_eq_add_neg, ← Int.sub_eq_add_neg]

private theorem add_bias_sub_cancel (s b₁ b₂ : Int) : (s + b₁) - (s + b₂) = b₁ - b₂ := by
  calc (s + b₁) - (s + b₂)
    _ = (b₁ + s) + (-s + -b₂) := by rw [Int.sub_eq_add_neg, Int.neg_add, Int.add_comm s b₁]
    _ = b₁ + (s + -s) + -b₂ := by rw [← Int.add_assoc (b₁ + s) (-s) (-b₂), Int.add_assoc b₁ s (-s)]
    _ = b₁ - b₂ := by rw [Int.add_right_neg, Int.add_zero, ← Int.sub_eq_add_neg]

instance instObsMetricScalarObs : ObsMetric ScalarObs Nat where
  dist a b := (a.val - b.val).natAbs
  dist_self v := by rw [Int.sub_self]; exact Nat.le_refl 0
  dist_triangle u v w := by
    change (u.val - w.val).natAbs ≤ (u.val - v.val).natAbs + (v.val - w.val).natAbs
    rw [int_sub_triangle_eq u.val v.val w.val]
    exact Int.natAbs_add_le (u.val - v.val) (v.val - w.val)

instance instObsMetricIntNat : ObsMetric Int Nat where
  dist a b := (a - b).natAbs
  dist_self v := by rw [Int.sub_self]; exact Nat.le_refl 0
  dist_triangle u v w := by
    change (u - w).natAbs ≤ (u - v).natAbs + (v - w).natAbs
    rw [int_sub_triangle_eq u v w]
    exact Int.natAbs_add_le (u - v) (v - w)

instance instObsMetricBoolNat : ObsMetric Bool Nat where
  dist a b := match a == b with | true => 0 | false => 1
  dist_self v := by cases v <;> decide
  dist_triangle u v w := by cases u <;> cases v <;> cases w <;> decide

abbrev mkOffsetSys (bias : Int) : PackagedStepSys Nat ScalarObs Nat where
  State := Int
  init := 0
  sys :=
    { step := fun s act s' => s' = s + Int.ofNat act
      observe := fun s => ⟨s + bias⟩ }

def mkBiasSimPath (b₁ b₂ : Int) (ph : Int) :
    GradedSimPath (mkOffsetSys b₁) (mkOffsetSys b₂) where
  rel s₁ s₂ := s₁ = s₂
  init_rel := rfl
  fwdSlack := (b₁ - b₂).natAbs
  bwdSlack := (b₂ - b₁).natAbs
  phase := ph
  fwdSim :=
    { obs_bound := fun {s₁ s₂} h => by
        subst h
        change ((s₁ + b₁) - (s₁ + b₂)).natAbs ≤ (b₁ - b₂).natAbs
        rw [add_bias_sub_cancel s₁ b₁ b₂]; exact Nat.le_refl _
      step_sim := fun h hs => by subst h; exact ⟨_, hs, rfl⟩ }
  bwdSim :=
    { obs_bound := fun {s₁ _} h => by
        cases h
        change ((s₁ + b₂) - (s₁ + b₁)).natAbs ≤ (b₂ - b₁).natAbs
        rw [add_bias_sub_cancel s₁ b₂ b₁]; exact Nat.le_refl _
      step_sim := fun h hs => by cases h; exact ⟨_, hs, rfl⟩ }

abbrev sysBox : OpenBox2 (PackagedStepSys Nat ScalarObs Nat) :=
  { c00 := mkOffsetSys 0
    c10 := mkOffsetSys 2
    c01 := mkOffsetSys (-1)
    c11 := mkOffsetSys 5
    bottomPath := mkBiasSimPath 0 2 10
    leftPath := mkBiasSimPath 0 (-1) (-4)
    rightPath := mkBiasSimPath 2 5 7 }

example :
    let tr : List Nat := [2, 3, 4]
    ∃ s₁₁' : Int,
      StepTrace (mkOffsetSys 5).sys (0 : Int) tr s₁₁' ∧
      0 ≤ s₁₁' ∧
      ObsMetric.dist (ε := Nat) ((mkOffsetSys (-1)).sys.observe (9 : Int))
        ((mkOffsetSys 5).sys.observe s₁₁') ≤ 6 := by
  have hTr01 : StepTrace (mkOffsetSys (-1)).sys (0 : Int) [2, 3, 4] (9 : Int) :=
    .cons (s₂ := (2 : Int)) rfl (.cons (s₂ := (5 : Int)) rfl (.cons (s₂ := (9 : Int)) rfl (.nil (9 : Int))))
  have hInvStep : ∀ {s s' : Int} {a : Nat}, 0 ≤ s → s' = s + Int.ofNat a → 0 ≤ s' := by
    intro s s' a hs hstep; subst hstep
    exact Int.add_nonneg hs (Int.natCast_nonneg a)
  exact hcomLid_stepSys_trace_safe sysBox hInvStep (Int.le_refl 0) hTr01

-- Kan Coercion `coeKan` & `KanFiber` along `hcomFill2`
def intTorsorEquiv : AdapterEquiv Int TorsorPt where
  fwd n := ⟨n⟩
  bwd p := p.pos
  bwd_fwd _ := rfl
  fwd_bwd p := by cases p; rfl

def torsorAccumulatorFiber : KanFiber TorsorPt (fun _ => Int) where
  transport shift acc := acc + shift.delta
  transport_refl _ acc := Int.add_zero acc
  transport_square { _ _ _ _ b t l r } hSq acc := by
    have hDelta : b.delta + r.delta = l.delta + t.delta := congrArg TorsorShift.delta hSq
    rw [Int.add_assoc, hDelta, ← Int.add_assoc]

example (n : Int) :
    coeKan (AdapterEquiv.refl Int) n = n ∧
    coeKan intTorsorEquiv.symm (coeKan intTorsorEquiv n) = n ∧
    torsorAccumulatorFiber.transport (hcomLid torsorBox).path
      (torsorAccumulatorFiber.transport torsorBox.leftPath n) =
    torsorAccumulatorFiber.transport torsorBox.rightPath
      (torsorAccumulatorFiber.transport torsorBox.bottomPath n) :=
  ⟨coeKan_refl n, coeKan_symm_cancel intTorsorEquiv n,
   coeKan_along_hcomFill2 torsorAccumulatorFiber torsorBox n⟩

-- ============================================================================
-- 3. Realizability 2LTT (`StageGrade`) & `AdapTT` Multiscale Cast Fusion
-- ============================================================================

def wellStagedKernel : Expr2LTT :=
  .letZero (.addU64 (.varZero 0) (.litU64 99))
    (.withSpecAssert (.mulU64 (.varZero 0) (.varZero 1))
      (.letOne (.addU64 (.varOne 0) (.litU64 5))
        (.mulU64 (.varOne 0) (.litU64 3))))

def illStagedLeaky : Expr2LTT := .addU64 (.varOne 0) (.varZero 0)

#guard WellStaged .one wellStagedKernel == true
#guard WellStaged .one illStagedLeaky == false
#guard WellStaged .zero illStagedLeaky == true
#guard runStageOne [7] wellStagedKernel == 36
#guard evalTwoLevel [11, 22] [7] wellStagedKernel == 36
#guard evalTwoLevel [999999, 888888] [7] wellStagedKernel == 36
-- Refutation: ill-staged expression leaks `.zero`-stage ghost witness into output!
#guard evalTwoLevel [1] [7] illStagedLeaky != evalTwoLevel [2] [7] illStagedLeaky

example (rEnv gEnv₁ gEnv₂ : List UInt64) :
    runStageOne rEnv wellStagedKernel = evalTwoLevel gEnv₁ rEnv wellStagedKernel ∧
    evalTwoLevel gEnv₁ rEnv wellStagedKernel = evalTwoLevel gEnv₂ rEnv wellStagedKernel :=
  realizer_stage_erases_zero_ghosts wellStagedKernel rEnv gEnv₁ gEnv₂ rfl

-- Quantitative Adapter & Lossless IsoAdapter witnesses
def biasedExecAdapter : QuantAdapter ScalarObs (Int × Bool) Nat where
  project cb := ⟨cb.1⟩
  embed s := (s.val + 1, true)
  grade := 1
  roundtrip_dist s := by
    change ((s.val + 1) - s.val).natAbs ≤ 1
    have h1 : (s.val + 1) - s.val = 1 := by
      have h0 := add_bias_sub_cancel s.val 1 0
      rw [Int.add_zero, Int.sub_zero] at h0
      exact h0
    rw [h1]; decide

def shiftedIsoAdapter : IsoAdapter ScalarObs Int where
  project x := ⟨x + 5⟩
  embed s := s.val - 5
  project_inv s := by cases s; simp [Int.sub_add_cancel]
  embed_inv x := Int.add_sub_cancel x 5

example (s : ScalarObs) (cb : Int × Bool) :
    ((QuantAdapter.id ScalarObs Nat).comp biasedExecAdapter
      (fun _ _ => GradeMonoid.le_refl _)).project cb = biasedExecAdapter.project cb ∧
    shiftedIsoAdapter.inv.embed (shiftedIsoAdapter.embed s) = s := by
  have hid := castAdapter_id_elim biasedExecAdapter s cb
  have hinv := castAdapter_inv_cancel (ε := Nat) shiftedIsoAdapter
    (fun b₁ b₂ => by
      change ((b₁ + 5) - (b₂ + 5)).natAbs ≤ (b₁ - b₂).natAbs
      rw [Int.add_comm b₁ 5, Int.add_comm b₂ 5, add_bias_sub_cancel 5 b₁ b₂]
      exact Nat.le_refl _) s
  exact ⟨hid.2.2.1, hinv.1⟩

-- 6-step multiscale `AdapterChain` fusing into a single $O(1)$ pass `[.affine 12 5 3 5]`
def multiscaleChain : AdapterChain :=
  [ .idCast
  , .affine 4 2 1 5
  , .tagCast 2 .fwd
  , .idCast
  , .tagCast 2 .bwd
  , .affine 3 (-1) 2 7 ]

#guard fuseAdapters multiscaleChain == [.affine 12 5 3 5]
#guard evalChain (fuseAdapters multiscaleChain) 10 == evalChain multiscaleChain 10
#guard (chainGrade multiscaleChain).uses == 4
#guard (chainGrade (fuseAdapters multiscaleChain)).uses == 1
#guard (chainGrade multiscaleChain).cycles == 14
#guard (chainGrade (fuseAdapters multiscaleChain)).cycles == 5

example (x : Int) :
    evalChain (fuseAdapters multiscaleChain) x = evalChain multiscaleChain x ∧
    chainGrade (fuseAdapters multiscaleChain) ≤ chainGrade multiscaleChain ∧
    GradedTriple (fun v => 0 ≤ v) (runChainGradedM (fuseAdapters multiscaleChain))
      (chainGrade multiscaleChain) (fun _ s' => ∃ s₀ : Int, 0 ≤ s₀ ∧ s' = evalChain multiscaleChain s₀) :=
  ⟨(fuseAdapters_sound multiscaleChain x).1,
   (fuseAdapters_sound multiscaleChain x).2,
   fuseAdapters_gradedTriple multiscaleChain (fun v => 0 ≤ v)⟩

-- ============================================================================
-- 4. Cross-Organ `Core5` Welds (`Refines`, `SuperRefines`, `DeltaLensRenew`)
-- ============================================================================

-- Weld 1: `adapter_induces_graded_refines` (`QuantAdapter` -> `Simulates` + `GaloisRefinement`)
def specStepSys : StepSystem ScalarObs Nat ScalarObs where
  step s act s' := s' = ⟨s.val + Int.ofNat act⟩
  observe s := s

def execStepSys : StepSystem (Int × Bool) Nat ScalarObs where
  step cb act cb' := cb' = (cb.1 + Int.ofNat act, cb.2)
  observe cb := ⟨cb.1⟩

example :
    Simulates execStepSys specStepSys (adapterEmbedRel biasedExecAdapter) 1 ∧
    (∃ s' : ScalarObs,
      StepTrace specStepSys ⟨10⟩ [3, 4] s' ∧
      ObsMetric.dist (ε := Nat) (execStepSys.observe (18, true)) (specStepSys.observe s') ≤ 1) := by
  have hStep : ∀ {s : ScalarObs} {c' : Int × Bool} {a : Nat},
      execStepSys.step (biasedExecAdapter.embed s) a c' →
      ∃ s' : ScalarObs, specStepSys.step s a s' ∧ c' = biasedExecAdapter.embed s' := by
    intro s c' a hc
    refine ⟨⟨s.val + Int.ofNat a⟩, rfl, ?_⟩
    rw [hc]
    apply Prod.ext
    · change s.val + 1 + (a : Int) = s.val + (a : Int) + 1
      rw [Int.add_assoc, Int.add_comm 1, ← Int.add_assoc]
    · rfl
  have hw := adapter_induces_graded_refines biasedExecAdapter execStepSys specStepSys
    (fun _ => rfl) (fun _ => rfl) hStep
  have hExecTr : StepTrace execStepSys (biasedExecAdapter.embed ⟨10⟩) [3, 4] (18, true) :=
    .cons (s₂ := (14, true)) rfl (.cons (s₂ := (18, true)) rfl (.nil (18, true)))
  obtain ⟨s', hTrA, _, hDist⟩ := hw.2.2 (Inv := fun _ => True) (fun _ _ => trivial) trivial hExecTr
  exact ⟨hw.1, ⟨s', hTrA, hDist⟩⟩

-- Weld 2: `adapter_superRefines_vertical_weld` (`Obend.Logic.SuperRefines` + `fuseAdapters`)
example (x : Int) :
    superClaimCheck 15 { verticalOpenRecClaimObj with comp := wrappedVerticalComp, layer := 1 }
      verticalOpenRecSteps = .ok ∧
    claimMeaning { verticalOpenRecClaimObj with comp := wrappedVerticalComp, layer := 1 } ∧
    evalChain (fuseAdapters multiscaleChain) x = evalChain multiscaleChain x := by
  have hOk : superClaimCheck 15 verticalOpenRecClaimObj verticalOpenRecSteps = .ok :=
    verticalOpenRec_frame_transport_accepted.1
  have hSup : ∀ sp ∈ superSupports verticalOpenRecClaimObj verticalOpenRecSteps,
      SuperSupport.holds wrappedVerticalComp verticalOpenRecClaimObj.arity 1 sp = true := by
    have hall : (superSupports verticalOpenRecClaimObj verticalOpenRecSteps).all
        (SuperSupport.holds wrappedVerticalComp verticalOpenRecClaimObj.arity 1) = true := by
      decide +kernel
    exact List.all_eq_true.1 hall
  have hWf : ({ verticalOpenRecClaimObj with comp := wrappedVerticalComp, layer := 1 } : ClaimObj).wellFormed = true := by
    decide +kernel
  have hw := adapter_superRefines_vertical_weld superClaim_sound hOk hSup hWf multiscaleChain x
  exact ⟨hw.1, hw.2.1, hw.2.2.2.1⟩

-- Weld 3: `hcom_repairs_broken_commuting_square` (`hcom2` + `DeltaLensRenew` + `SuperRefines`)
def specEvolveDelta : TorsorShift t01 ⟨9⟩ := ⟨5, rfl⟩
def implEvolveDelta : TorsorShift t11 ⟨31⟩ := ⟨6, rfl⟩

example :
    let L_comp := DeltaLens.fst Composition TorsorPt
    let L_spec := DeltaLens.snd Composition TorsorPt
    let _hDisj : DisjointLenses L_comp L_spec := ⟨fun _ _ _ => rfl⟩
    let ω₁ : Composition × TorsorPt := (verticalComp, t01)
    let ω₂ := L_spec.put ω₁ ⟨9⟩
    L_spec.get ω₂ = ⟨9⟩ ∧
    L_comp.get ω₂ = verticalComp ∧
    superClaimCheck 15 { verticalOpenRecClaimObj with comp := L_comp.get ω₂ }
      verticalOpenRecSteps = .ok ∧
    claimMeaning { verticalOpenRecClaimObj with comp := L_comp.get ω₂ } := by
  have hOk : superClaimCheck 15
      { verticalOpenRecClaimObj with comp := (DeltaLens.fst Composition TorsorPt).get (verticalComp, t01) }
      verticalOpenRecSteps = .ok := verticalOpenRec_frame_transport_accepted.1
  have hRep := hcom_repairs_broken_commuting_square
    (DeltaLens.snd Composition TorsorPt)
    (DeltaLens.fst Composition TorsorPt)
    ⟨fun _ _ _ => rfl⟩
    (verticalComp, t01)
    torsorSquare
    rfl
    specEvolveDelta
    implEvolveDelta
    superClaim_sound
    hOk
  exact ⟨hRep.2.2.1.symm, hRep.2.2.2.2.1, hRep.2.2.2.2.2.1, hRep.2.2.2.2.2.2.1⟩

-- ============================================================================
-- 5. `#tooth` Mutation Kills Across All Subsystems (8 Kills ≥ 6 Required)
-- ============================================================================

-- Kill 1: Vacuously accepting `CofibLUT16.entails` breaks `entails_iff_pointwise`!
#tooth Obend.Core.Cubical2LTT.CofibLUT16.entails_iff_pointwise by mutation
  Obend.Core.Cubical2LTT.CofibLUT16.entails := fun _ _ => true

-- Kill 2: Dropping SWAR bit-reversal in `revDim` breaks `evalCofib_revDim`!
#tooth Obend.Core.Cubical2LTT.CofibLUT16.evalCofib_revDim by mutation
  Obend.Core.Cubical2LTT.CofibLUT16.revDim := fun _ φ => φ

-- Kill 3: Dropping SWAR endpoint restriction in `substDim` breaks `evalCofib_substDim`!
#tooth Obend.Core.Cubical2LTT.CofibLUT16.evalCofib_substDim by mutation
  Obend.Core.Cubical2LTT.CofibLUT16.substDim := fun _ _ φ => φ

-- Kill 4: Collapsing `CofibSyntax4.toLUT16` to `bot` breaks `toLUT16_agrees_on_vertices`!
#tooth Obend.Core.Cubical2LTT.CofibSyntax4.toLUT16_agrees_on_vertices by mutation
  Obend.Core.Cubical2LTT.CofibSyntax4.toLUT16 := fun _ => Obend.Core.Cubical2LTT.CofibLUT16.bot

-- Kill 5: Replacing `hcomLid` with a degenerate constant `refl` path breaks `hcomFill2_agrees_on_open_box_boundary`!
#tooth Obend.Core.Cubical2LTT.hcomFill2_agrees_on_open_box_boundary by mutation
  Obend.Core.Cubical2LTT.hcomLid := fun box => Obend.Core.Cubical2LTT.Cube1.refl box.c01

-- Kill 6: Admitting `.varZero` ghosts at `.one` stage in `WellStaged` breaks `realizer_stage_erases_zero_ghosts`!
#tooth Obend.Core.Cubical2LTT.realizer_stage_erases_zero_ghosts by mutation
  Obend.Core.Cubical2LTT.WellStaged := fun _ _ => true

-- Kill 7: Dropping adapter operations in `fuseStep` breaks `fuseAdapters_sound`!
#tooth Obend.Core.Cubical2LTT.fuseAdapters_sound by mutation
  Obend.Core.Cubical2LTT.fuseStep := fun _ _ => []

-- Kill 8: Skipping inverse cancellation in `fuseAdapters` breaks `castAdapter_inv_cancel_chain`!
#tooth Obend.Core.Cubical2LTT.castAdapter_inv_cancel_chain by mutation
  Obend.Core.Cubical2LTT.fuseAdapters := fun c => c

-- ============================================================================
-- 6. `#assert_axioms_tree`, Strict `0 Classical.choice` & `0` Closed-Theorem Audit
-- ============================================================================

#assert_axioms_tree

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checkedCount : Nat := 0
  let mut universalCount : Nat := 0
  let mut closedOffenders : Array Name := #[]
  let mut choiceOffenders : Array Name := #[]
  for (cName, info) in env.constants.map₁.toList do
    let some modIdx := env.getModuleIdxFor? cName | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    unless modName == `Obend.Core.Cubical2LTT do continue
    checkedCount := checkedCount + 1
    let axs ← liftCoreM <| collectAxioms cName
    for ax in axs do
      if ax == ``Classical.choice then
        choiceOffenders := choiceOffenders.push cName
      else unless ax == ``propext || ax == ``Quot.sound do
        throwError m!"Disallowed axiom {ax} found in {cName}"
    if let .thmInfo _ := info then
      if !cName.isInternal && !cName.isInternalDetail &&
         cName.components.getLast? != some `sizeOf_spec then
        if ← liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
          closedOffenders := closedOffenders.push cName
        else
          universalCount := universalCount + 1
  unless choiceOffenders.isEmpty do
    throwError m!"Classical.choice forbidden in Obend.Core.Cubical2LTT, found in: {choiceOffenders.toList}"
  if checkedCount == 0 then
    throwError "Zero constants inspected in Obend.Core.Cubical2LTT!"
  unless closedOffenders.isEmpty do
    throwError m!"Obend.Core.Cubical2LTT has closed theorems (must be 0): {closedOffenders.toList}"
  if universalCount == 0 then
    throwError "Obend.Core.Cubical2LTT reported 0 universal theorems!"
  logInfo m!"Obend.Core.Cubical2LTT verified: {checkedCount} constants (0 sorryAx, 0 custom axioms, 0 native_decide, 0 Classical.choice), {universalCount} universal theorems, 0 closed theorems"

end Obend.Tests.Core5Cubical2LttTest
