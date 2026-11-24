module
/-
# Obend.Apps.RelativityZ4cApp — Real-World Numerical Relativity 1+1 Bona–Massó / Z4c App

Connects the 3-layer `.obend` numerical relativity package in `apps/relativity-z4c/`:
1. `apps/relativity-z4c/BonaMassoSlicing.obend` (`BonaMassoSlicing`: harmonic slicing overridden by
   Bona–Massó 1+log shifted gauge `fBM = 2`, `beta = 1/5`, and certified state-box milli-bounds),
2. `apps/relativity-z4c/Z4cConstraintDamping.obend` (`Z4cConstraintDamping`: undamped ADM overridden
   by Bernuzzi–Hilditch Z4c constraint damping `kappa1 = 1/2`, `|Theta| <= 1/4`, `numVars = 6`),
3. `apps/relativity-z4c/RelativityZ4cTop.obend` (`RelativityZ4cTop`: Apples-with-Apples 1+1
   Gauge-Wave + Planted-`Theta` benchmark composition with `maxWavespeed = 9`, `cfl = 1/10`,
   `gridCells = 16`, `benchmarkSteps = 8`)

directly to the verified 1+1 Bona–Massó / Z4c PDE solver, balance-law accelerator bridge, and
nonlinear rollout CLI (`Obend.Hardware.PdeSolvers.BonaMassoZ4c1D`,
`Obend.Analysis.HyperbolicBalanceLaws`, `Obend.Analysis.NonlinearPdeCli`):
- Vtable flattening (`flatten_sound`), `Leaf.Book` emission (`book_sound`), disjoint-overlay cone
  survival (`coneSupports_linkComposition_of_disjoint`), and `compileBookToRtl` LEC,
- Exact parameter & state-box weld (`relativityZ4c_obend_welds_to_bonaMassoZ4c1D`) bundling
  `BonaMassoZ4c1D.endToEnd_certified`, `BonaMassoZ4c1D.balanceSystolicRtl_ok 0`,
  `BonaMassoZ4c1D.source_frechet_sound`, and periodic conservation of `Ax`/`Dx` integrals,
- Exponential Z4c constraint-damping contraction (`z4c_constraint_damping_contraction_sound`):
  under `BonaMassoZ4c1D.spec` (`kappa1 = 1/2`, `cfl = 1/10`) and any lapse `1/2 <= alpha0 <= 2`,
  the per-step damping multiplier lies in `[9/10, 39/40]` and `|Theta^k| <= (39/40)^k * |Theta^0|`,
- Executable `pdeNonlinear` acceptance, monotonic `||Theta^k||_inf` damping, tampered 256-bit
  receipt refusal, CFL-violation S-expr refusal, and `#tooth` mutation-sensitivity witness.
-/
public import Lean.Data.Json
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.PdeSolvers
public import Obend.Hardware.MultiDStencilCorrect
public import Obend.Hardware.BalanceLawLowering
public import Obend.Analysis.HyperbolicBalanceLaws
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Analysis.NonlinearPdeCli
public import Obend.Spec.CrossPackage
public import Obend.Leaf.Emit
public import Obend.Leaf.Flatten
public import Obend.Tactic.Tooth
public import Obend.Elab.Workbook
import all Obend.Hardware.Compiler
import all Obend.Hardware.HDL
import all Obend.Hardware.PdeSolvers
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.MultiDStencilCorrect
import all Obend.Hardware.BalanceLawLowering
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Analysis.NonlinearErrorTube
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.NonlinearPdeCli
import all Obend.Tactic.SymDiffAndFlux
import all Obend.Elab.PdeSolverElab
import all Obend.Receipt.Merkle
import all Obend.Digest.HashBytes
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Core.Digest
meta import Lean
meta import Obend.Elab.Workbook

public section

namespace Obend.Apps.RelativityZ4cApp

open Lean (Json toJson)
open Obend.Core.Term
open Obend.Equiv
open Obend.Leaf
open Obend.Lower
open Obend.Spec.CrossPackage
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.PdeSolvers
open Obend.Hardware.MultiDStencilCorrect
open Obend.Hardware.BalanceLawLowering
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.PdeSexprAndApprox
open Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws
open Obend.Analysis.NonlinearPdeCli

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! ## 1. Compile-Time Elaboration of `apps/relativity-z4c/*.obend` via `#import_obend` -/

#import_obend "apps/relativity-z4c/BonaMassoSlicing.obend" as BonaMassoSlicing
#import_obend "apps/relativity-z4c/Z4cConstraintDamping.obend" as Z4cConstraintDamping
#import_obend "apps/relativity-z4c/RelativityZ4cTop.obend" as RelativityZ4cTop

/-- Extract a natural number from a reduced `.obend` `Term` (`0` for non-natural terms). -/
def natOfTerm : Term → Nat
  | .nat n => n
  | _ => 0

/-- Composed 1+1 Bona–Massó / Z4c parameter record extracted from `apps/relativity-z4c/*.obend`. -/
structure RelativityZ4cConfig where
  fBM : Nat
  betaNum : Nat
  betaDen : Nat
  kappa1Num : Nat
  kappa1Den : Nat
  maxWavespeed : Nat
  cflNum : Nat
  cflDen : Nat
  gridCells : Nat
  benchmarkSteps : Nat
  numVars : Nat
  alphaMinMilli : Nat
  alphaMaxMilli : Nat
  gxxMinMilli : Nat
  gxxMaxMilli : Nat
  gradBoundMilli : Nat
  thetaBoundMilli : Nat
  deriving DecidableEq, Repr

/-- The exact parameter configuration reduced from the three composed `.obend` layers. -/
def RelativityZ4cConfig.ofObend : RelativityZ4cConfig :=
  { fBM := natOfTerm BonaMassoSlicing.fBM_val
  , betaNum := natOfTerm BonaMassoSlicing.betaNum_val
  , betaDen := natOfTerm BonaMassoSlicing.betaDen_val
  , kappa1Num := natOfTerm Z4cConstraintDamping.kappa1Num_val
  , kappa1Den := natOfTerm Z4cConstraintDamping.kappa1Den_val
  , maxWavespeed := natOfTerm RelativityZ4cTop.maxWavespeed_val
  , cflNum := natOfTerm RelativityZ4cTop.cflNum_val
  , cflDen := natOfTerm RelativityZ4cTop.cflDen_val
  , gridCells := natOfTerm RelativityZ4cTop.gridCells_val
  , benchmarkSteps := natOfTerm RelativityZ4cTop.benchmarkSteps_val
  , numVars := natOfTerm Z4cConstraintDamping.numVars_val
  , alphaMinMilli := natOfTerm BonaMassoSlicing.alphaMinMilli_val
  , alphaMaxMilli := natOfTerm BonaMassoSlicing.alphaMaxMilli_val
  , gxxMinMilli := natOfTerm BonaMassoSlicing.gxxMinMilli_val
  , gxxMaxMilli := natOfTerm BonaMassoSlicing.gxxMaxMilli_val
  , gradBoundMilli := natOfTerm BonaMassoSlicing.gradBoundMilli_val
  , thetaBoundMilli := natOfTerm Z4cConstraintDamping.thetaBoundMilli_val }

def RelativityZ4cConfig.fBMRat (c : RelativityZ4cConfig) : Rat := (c.fBM : Rat)
def RelativityZ4cConfig.betaRat (c : RelativityZ4cConfig) : Rat := (c.betaNum : Rat) / (c.betaDen : Rat)
def RelativityZ4cConfig.kappa1Rat (c : RelativityZ4cConfig) : Rat := (c.kappa1Num : Rat) / (c.kappa1Den : Rat)
def RelativityZ4cConfig.aMaxRat (c : RelativityZ4cConfig) : Rat := (c.maxWavespeed : Rat)
def RelativityZ4cConfig.cflRat (c : RelativityZ4cConfig) : Rat := (c.cflNum : Rat) / (c.cflDen : Rat)

def RelativityZ4cConfig.stateBoxRat (c : RelativityZ4cConfig) : List (Rat × Rat) :=
  [ ((c.alphaMinMilli : Rat) / 1000, (c.alphaMaxMilli : Rat) / 1000)
  , ((c.gxxMinMilli : Rat) / 1000, (c.gxxMaxMilli : Rat) / 1000)
  , (-((c.gradBoundMilli : Rat) / 1000), (c.gradBoundMilli : Rat) / 1000)
  , (-((c.gradBoundMilli : Rat) / 1000), (c.gradBoundMilli : Rat) / 1000)
  , (-((c.gradBoundMilli : Rat) / 1000), (c.gradBoundMilli : Rat) / 1000)
  , (-((c.thetaBoundMilli : Rat) / 1000), (c.thetaBoundMilli : Rat) / 1000) ]

/-- Concrete value verification of the elaborated 3-layer `.obend` workbooks. -/
example :
    RelativityZ4cTop.laws_count = 5 ∧
    BonaMassoSlicing.fBM_val = .nat 2 ∧
    BonaMassoSlicing.betaNum_val = .nat 1 ∧
    BonaMassoSlicing.betaDen_val = .nat 5 ∧
    BonaMassoSlicing.slicingConfigValid_val = .boolean true ∧
    Z4cConstraintDamping.kappa1Num_val = .nat 1 ∧
    Z4cConstraintDamping.kappa1Den_val = .nat 2 ∧
    Z4cConstraintDamping.numVars_val = .nat 6 ∧
    Z4cConstraintDamping.z4cDampingValid_val = .boolean true ∧
    RelativityZ4cTop.maxWavespeed_val = .nat 9 ∧
    RelativityZ4cTop.cflNum_val = .nat 1 ∧
    RelativityZ4cTop.cflDen_val = .nat 10 ∧
    RelativityZ4cTop.gridCells_val = .nat 16 ∧
    RelativityZ4cTop.benchmarkSteps_val = .nat 8 ∧
    RelativityZ4cTop.relativityZ4cEndToEndValid_val = .boolean true ∧
    RelativityZ4cTop.relativityZ4cSummary_val = .nat 189 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Vtable Flattening, `Leaf.Book` Emission, Cone Survival & `compileBookToRtl` LEC -/

/-- For every member `m`, each of the 3 composed `.obend` relativity objects is observationally
equivalent (`≈b`) to its flattened vtable and to its emitted `Leaf.Book`. -/
theorem relativityZ4c_flatten_and_book_sound (m : String) :
    (.get BonaMassoSlicing.bonaMassoShiftedSlicing_comp.flatten m ≈b
      .get BonaMassoSlicing.bonaMassoShiftedSlicing_comp.object m) ∧
    (.get (emit BonaMassoSlicing.bonaMassoShiftedSlicing_comp).link m ≈b
      .get BonaMassoSlicing.bonaMassoShiftedSlicing_comp.object m) ∧
    (.get Z4cConstraintDamping.bernuzziHilditchZ4c_comp.flatten m ≈b
      .get Z4cConstraintDamping.bernuzziHilditchZ4c_comp.object m) ∧
    (.get (emit Z4cConstraintDamping.bernuzziHilditchZ4c_comp).link m ≈b
      .get Z4cConstraintDamping.bernuzziHilditchZ4c_comp.object m) ∧
    (.get RelativityZ4cTop.applesWithApplesZ4cBenchmark_comp.flatten m ≈b
      .get RelativityZ4cTop.applesWithApplesZ4cBenchmark_comp.object m) ∧
    (.get (emit RelativityZ4cTop.applesWithApplesZ4cBenchmark_comp).link m ≈b
      .get RelativityZ4cTop.applesWithApplesZ4cBenchmark_comp.object m) := by
  have hc1 : BonaMassoSlicing.bonaMassoShiftedSlicing_comp.closedB = true := by decide +kernel
  have hc2 : Z4cConstraintDamping.bernuzziHilditchZ4c_comp.closedB = true := by decide +kernel
  have hc3 : RelativityZ4cTop.applesWithApplesZ4cBenchmark_comp.closedB = true := by decide +kernel
  exact ⟨flatten_sound _ hc1 m, book_sound _ hc1 m,
         flatten_sound _ hc2 m, book_sound _ hc2 m,
         flatten_sound _ hc3 m, book_sound _ hc3 m⟩

/-- Disjoint-overlay cone survival: any list of slicing fields disjoint from `OnePlusLogShiftedOverride`
(`fBM`, `betaNum`) keeps its exact cone support when linked onto `BaseHarmonicSlicingSpec`. -/
theorem relativityZ4c_cone_survives (fields : List String)
    (hDisj : ∀ m ∈ fields, m ∉ overlayModifiedFields BonaMassoSlicing.bonaMassoShiftedSlicing_comp.top) :
    coneSupports
      (linkComposition BonaMassoSlicing.baseHarmonicSlicing_comp
        BonaMassoSlicing.bonaMassoShiftedSlicing_comp.top) fields =
      coneSupports BonaMassoSlicing.baseHarmonicSlicing_comp fields := by
  have hflat : BonaMassoSlicing.bonaMassoShiftedSlicing_comp.top.flat = false := by decide +kernel
  exact coneSupports_linkComposition_of_disjoint
    BonaMassoSlicing.baseHarmonicSlicing_comp
    BonaMassoSlicing.bonaMassoShiftedSlicing_comp.top
    fields hflat hDisj

/-- Concrete cone-survival witness on the state-box & shift denominator fields. -/
example :
    coneSupports
      (linkComposition BonaMassoSlicing.baseHarmonicSlicing_comp
        BonaMassoSlicing.bonaMassoShiftedSlicing_comp.top)
      ["alphaMinMilli", "alphaMaxMilli", "gxxMinMilli", "gxxMaxMilli", "betaDen"] =
      coneSupports BonaMassoSlicing.baseHarmonicSlicing_comp
        ["alphaMinMilli", "alphaMaxMilli", "gxxMinMilli", "gxxMaxMilli", "betaDen"] :=
  relativityZ4c_cone_survives
    ["alphaMinMilli", "alphaMaxMilli", "gxxMinMilli", "gxxMaxMilli", "betaDen"]
    (by decide +kernel)

/-- Concrete `compileBookToRtl` LEC check across all three `.obend` books. -/
example :
    (match compileBookToRtl "bona_masso_slicing" BonaMassoSlicing.bonaMassoShiftedSlicing_book,
           compileBookToRtl "z4c_constraint_damping" Z4cConstraintDamping.bernuzziHilditchZ4c_book,
           compileBookToRtl "relativity_z4c_top" RelativityZ4cTop.applesWithApplesZ4cBenchmark_book with
     | some mSlice, some mDamp, some mTop =>
       checkRtlModule mSlice &&
       checkRtlModule mDamp &&
       checkRtlModule mTop &&
       ((evalModuleOutputs mSlice (fun _ => 1000#64) (fun _ => 0#64)).lookup "out_fBM" == some 2#64) &&
       ((evalModuleOutputs mSlice (fun _ => 1000#64) (fun _ => 0#64)).lookup "out_slicingSpeedNum" == some 2000#64) &&
       ((evalModuleOutputs mDamp (fun _ => 1000#64) (fun _ => 0#64)).lookup "out_kappa1Num" == some 1#64) &&
       ((evalModuleOutputs mDamp (fun _ => 1000#64) (fun _ => 0#64)).lookup "out_numVars" == some 6#64) &&
       ((evalModuleOutputs mTop (fun _ => 0#64) (fun _ => 0#64)).lookup "out_maxWavespeed" == some 9#64) &&
       ((evalModuleOutputs mTop (fun _ => 0#64) (fun _ => 0#64)).lookup "out_totalCellUpdates" == some 128#64)
     | _, _, _ => false) = true := by
  decide +kernel

/-! ## 3. Exact `.obend` → `BonaMassoZ4c1D` Weld & Certified Balance-Law Spine -/

/-- **`relativityZ4c_obend_welds_to_bonaMassoZ4c1D`**:
1. The rational parameters (`fBM = 2`, `beta = 1/5`, `kappa1 = 1/2`, `aMax = 9`, `cfl = 1/10`,
   `numVars = 6`, and full 6-variable `stateBox`) reduced from `apps/relativity-z4c/*.obend` match
   `Obend.Hardware.PdeSolvers.BonaMassoZ4c1D.spec` identically,
2. Bundles the full 6-rung `EndToEndPdeCert BonaMassoZ4c1D.spec` (`BonaMassoZ4c1D.endToEnd_certified`),
   the resize-free verified systolic RTL module (`BonaMassoZ4c1D.balanceSystolicRtl_ok 0`), and the
   exact multivariable source Fréchet Taylor theorem (`BonaMassoZ4c1D.source_frechet_sound`),
3. For any positive grid shape `dims`, multi-step periodic `rolloutRat` (Lie or Strang) exactly
   conserves the discrete grid integrals of both sourceless spatial derivatives `Ax` (index `2`)
   and `Dx` (index `3`). -/
theorem relativityZ4c_obend_welds_to_bonaMassoZ4c1D (dims : List Nat) :
    let cfg := RelativityZ4cConfig.ofObend
    cfg.fBMRat = BonaMassoZ4c1D.spec.paramEnv 0 ∧
    cfg.betaRat = BonaMassoZ4c1D.spec.paramEnv 1 ∧
    cfg.kappa1Rat = BonaMassoZ4c1D.spec.paramEnv 2 ∧
    cfg.aMaxRat = BonaMassoZ4c1D.spec.aMax ∧
    cfg.cflRat = BonaMassoZ4c1D.spec.cfl ∧
    cfg.numVars = BonaMassoZ4c1D.spec.numVars ∧
    cfg.stateBoxRat = BonaMassoZ4c1D.spec.stateBox ∧
    EndToEndPdeCert BonaMassoZ4c1D.spec ∧
    (checkRtlModule (BonaMassoZ4c1D.balanceSystolicRtl 0) = true ∧
      moduleResizeFree (BonaMassoZ4c1D.balanceSystolicRtl 0) = true) ∧
    (∀ (u V : Vec) (h : Rat),
      DomainValid BonaMassoZ4c1D.spec.domain ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩ →
      DomainValid BonaMassoZ4c1D.spec.domain
        (shiftVecEnv BonaMassoZ4c1D.spec.numVars ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩ h V) →
      ∀ (i : Nat), i < BonaMassoZ4c1D.spec.numVars →
        evalFlux (getOr BonaMassoZ4c1D.spec.sources i (.const 0))
            (shiftVecEnv BonaMassoZ4c1D.spec.numVars ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩ h V) -
          evalFlux (getOr BonaMassoZ4c1D.spec.sources i (.const 0)) ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩ =
          h * mulVec BonaMassoZ4c1D.spec.numVars
            (evalSymJacobianMat BonaMassoZ4c1D.sourceJacobian ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩) V i +
          (h * h) * symDirectionalRem BonaMassoZ4c1D.spec.numVars
            (getOr BonaMassoZ4c1D.spec.sources i (.const 0))
            ⟨u, BonaMassoZ4c1D.spec.paramEnv⟩ V h) ∧
    ((∀ N ∈ dims, 0 < N) → ∀ (useStrang : Bool) (steps : Nat) (G : RatGrid),
      totalGridIntegral dims (gridFn (rolloutRat BonaMassoZ4c1D.spec .periodic dims useStrang steps G)) 2 =
        totalGridIntegral dims (gridFn G) 2 ∧
      totalGridIntegral dims (gridFn (rolloutRat BonaMassoZ4c1D.spec .periodic dims useStrang steps G)) 3 =
        totalGridIntegral dims (gridFn G) 3) := by
  dsimp only
  have hParams :
      RelativityZ4cConfig.ofObend.fBMRat = BonaMassoZ4c1D.spec.paramEnv 0 ∧
      RelativityZ4cConfig.ofObend.betaRat = BonaMassoZ4c1D.spec.paramEnv 1 ∧
      RelativityZ4cConfig.ofObend.kappa1Rat = BonaMassoZ4c1D.spec.paramEnv 2 ∧
      RelativityZ4cConfig.ofObend.aMaxRat = BonaMassoZ4c1D.spec.aMax ∧
      RelativityZ4cConfig.ofObend.cflRat = BonaMassoZ4c1D.spec.cfl ∧
      RelativityZ4cConfig.ofObend.numVars = BonaMassoZ4c1D.spec.numVars ∧
      RelativityZ4cConfig.ofObend.stateBoxRat = BonaMassoZ4c1D.spec.stateBox := by
    decide +kernel
  obtain ⟨hf, hb, hk, ha, hc, hn, hbox⟩ := hParams
  refine ⟨hf, hb, hk, ha, hc, hn, hbox,
    BonaMassoZ4c1D.endToEnd_certified,
    BonaMassoZ4c1D.balanceSystolicRtl_ok 0,
    BonaMassoZ4c1D.source_frechet_sound,
    fun hPos useStrang steps G =>
      ⟨rolloutRat_periodic_conserves_integral BonaMassoZ4c1D.spec dims hPos useStrang steps G 2
          (by decide +kernel) (Or.inr (by decide +kernel)),
       rolloutRat_periodic_conserves_integral BonaMassoZ4c1D.spec dims hPos useStrang steps G 3
          (by decide +kernel) (Or.inr (by decide +kernel))⟩⟩

/-! ## 4. Exponential Z4c Constraint-Damping Contraction (`Theta`) -/

/-- Exact single-step Z4c constraint-damping update of component `5` (`Theta`) directly from
`BonaMassoZ4c1D.spec.sources[5]` at `dt = BonaMassoZ4c1D.spec.cfl = 1/10`. -/
def z4cThetaSourceStep (alpha theta : Rat) : Rat :=
  theta + BonaMassoZ4c1D.spec.cfl *
    evalFlux (getOr BonaMassoZ4c1D.spec.sources 5 (.const 0))
      ⟨fun c => if c = 0 then alpha else if c = 5 then theta else 0, BonaMassoZ4c1D.spec.paramEnv⟩

/-- Iterated `steps`-step Z4c `Theta` constraint-damping evolution at lapse `alpha`. -/
def z4cThetaAfter (alpha theta : Rat) : Nat → Rat
  | 0 => theta
  | k + 1 => z4cThetaSourceStep alpha (z4cThetaAfter alpha theta k)

private theorem z4cThetaSourceStep_eq (alpha theta : Rat) :
    z4cThetaSourceStep alpha theta =
      (1 - BonaMassoZ4c1D.spec.cfl * BonaMassoZ4c1D.spec.paramEnv 2 * alpha) * theta := by
  have hSrc : getOr BonaMassoZ4c1D.spec.sources 5 (.const 0) =
      .neg (.mul (.param 2) (.mul (.var 0) (.var 5))) := by decide +kernel
  have hCfl : BonaMassoZ4c1D.spec.cfl = (1 / 10 : Rat) := by decide +kernel
  have hK1 : BonaMassoZ4c1D.spec.paramEnv 2 = (1 / 2 : Rat) := by decide +kernel
  unfold z4cThetaSourceStep
  rw [hSrc]
  simp only [evalFlux, ↓reduceIte, show (5 : Nat) ≠ 0 by omega]
  rw [hCfl, hK1]
  grind

/-- Pointwise bridge: `sourceStepRat BonaMassoZ4c1D.spec` at component `5` (`Theta`) equals
`z4cThetaSourceStep` on every cell `idx < gridCellCount dims`. -/
theorem z4c_sourceStepRat_theta_eq (dims : List Nat) (G : RatGrid) (idx : Nat)
    (hIdx : idx < gridCellCount dims) :
    gridFn (sourceStepRat BonaMassoZ4c1D.spec dims BonaMassoZ4c1D.spec.cfl G) idx 5 =
      z4cThetaSourceStep (gridFn G idx 0) (gridFn G idx 5) := by
  have hNonEmpty : BonaMassoZ4c1D.spec.sources.isEmpty = false := by decide +kernel
  have hVars : 5 < BonaMassoZ4c1D.spec.numVars := by decide +kernel
  have hSrc : getOr BonaMassoZ4c1D.spec.sources 5 (.const 0) =
      .neg (.mul (.param 2) (.mul (.var 0) (.var 5))) := by decide +kernel
  unfold sourceStepRat
  rw [hNonEmpty]
  simp only [Bool.false_eq_true, ↓reduceIte, gridFn, tabulate, Array.getElem?_ofFn, hIdx,
    ↓reduceDIte, Option.getD_some, hVars]
  unfold z4cThetaSourceStep
  rw [hSrc]
  simp only [evalFlux, ↓reduceIte, show (5 : Nat) ≠ 0 by omega]
  rfl

/-- **`z4c_constraint_damping_contraction_sound`**:
Under `BonaMassoZ4c1D.spec` (`kappa1 = 1/2`, `cfl = 1/10`), for any lapse `alpha0 ∈ [1/2, 2]`,
any initial constraint violation `theta0 : Rat`, and any `steps : Nat`:
1. The per-step Z4c damping factor `1 - cfl * kappa1 * alpha0` lies strictly in `[9/10, 39/40]`,
2. After `steps` damping updates, `ratAbs (z4cThetaAfter alpha0 theta0 steps) ≤ (39/40)^steps * ratAbs theta0`,
3. Whenever `theta0 ≠ 0`, a single damping step strictly contracts `Theta²`. -/
theorem z4c_constraint_damping_contraction_sound (alpha0 theta0 : Rat) (steps : Nat)
    (hLo : (1 / 2 : Rat) ≤ alpha0) (hHi : alpha0 ≤ 2) :
    let factor := 1 - BonaMassoZ4c1D.spec.cfl * BonaMassoZ4c1D.spec.paramEnv 2 * alpha0
    ((9 / 10 : Rat) ≤ factor ∧ factor ≤ (39 / 40 : Rat)) ∧
    ratAbs (z4cThetaAfter alpha0 theta0 steps) ≤ ((39 / 40 : Rat) ^ steps) * ratAbs theta0 ∧
    (theta0 ≠ 0 →
      z4cThetaSourceStep alpha0 theta0 * z4cThetaSourceStep alpha0 theta0 < theta0 * theta0) := by
  have hCfl : BonaMassoZ4c1D.spec.cfl = (1 / 10 : Rat) := by decide +kernel
  have hK1 : BonaMassoZ4c1D.spec.paramEnv 2 = (1 / 2 : Rat) := by decide +kernel
  have hFac : (9 / 10 : Rat) ≤ 1 - BonaMassoZ4c1D.spec.cfl * BonaMassoZ4c1D.spec.paramEnv 2 * alpha0 ∧
      1 - BonaMassoZ4c1D.spec.cfl * BonaMassoZ4c1D.spec.paramEnv 2 * alpha0 ≤ (39 / 40 : Rat) := by
    rw [hCfl, hK1]; constructor <;> grind
  have hDecay : ∀ k : Nat,
      ratAbs (z4cThetaAfter alpha0 theta0 k) ≤ ((39 / 40 : Rat) ^ k) * ratAbs theta0 := by
    intro k
    induction k with
    | zero =>
      simp only [z4cThetaAfter, Rat.pow_zero, Rat.one_mul]
      exact Rat.le_refl
    | succ n ih =>
      simp only [z4cThetaAfter]
      rw [z4cThetaSourceStep_eq, ratAbs_mul,
          Obend.Analysis.NonlinearMultiDPde.ratAbs_of_nonneg (show 0 ≤ _ by grind),
          Rat.pow_succ]
      have hStep := rat_mul_le_mul (show 0 ≤ _ by grind) hFac.2 (ratAbs_nonneg _) ih
      have hAssoc : (39 / 40 : Rat) * ((39 / 40 : Rat) ^ n * ratAbs theta0) =
          (39 / 40 : Rat) ^ n * (39 / 40 : Rat) * ratAbs theta0 := by grind
      exact Rat.le_trans hStep (by rw [hAssoc]; exact Rat.le_refl)
  refine ⟨hFac, hDecay steps, fun hNe => ?_⟩
  have hStrict := z4c_theta_constraint_strict_damped theta0 BonaMassoZ4c1D.spec.cfl
    (BonaMassoZ4c1D.spec.paramEnv 2) alpha0
    (by rw [hCfl, hK1]; grind) (by rw [hCfl, hK1]; grind) hNe
  have hEq : z4cThetaSourceStep alpha0 theta0 =
      theta0 + BonaMassoZ4c1D.spec.cfl * -(BonaMassoZ4c1D.spec.paramEnv 2 * alpha0 * theta0) := by
    rw [z4cThetaSourceStep_eq]; grind
  rw [hEq]
  exact hStrict

/-! ## 5. Executable Admissibility Gate, `#tooth` Witness & `pdeNonlinear` CLI Checks -/

/-- Executable admissibility check on a `RelativityZ4cConfig` ensuring positive denominators,
non-empty state box, `numVars = 6`, active Z4c damping (`kappa1 > 0`), and CFL admissibility
`cflNum * maxWavespeed ≤ cflDen`. -/
def checkRelativityZ4cAdmissible (c : RelativityZ4cConfig) : Bool :=
  (0 < c.betaDen) && (0 < c.kappa1Den) && (0 < c.cflDen) &&
  (0 < c.fBM) && (0 < c.kappa1Num) && (c.numVars == 6) &&
  (0 < c.maxWavespeed) && (c.cflNum * c.maxWavespeed <= c.cflDen) &&
  (c.alphaMinMilli < c.alphaMaxMilli) && (c.gxxMinMilli < c.gxxMaxMilli) &&
  (0 < c.alphaMinMilli) && (0 < c.gxxMinMilli) && (0 < c.thetaBoundMilli)

/-- Soundness of `checkRelativityZ4cAdmissible`: every accepted configuration satisfies strict
CFL admissibility `c.cflRat * c.aMaxRat ≤ 1`, positive `kappa1Rat`, and positive lapse/metric box. -/
theorem checkRelativityZ4cAdmissible_sound (c : RelativityZ4cConfig)
    (hOk : checkRelativityZ4cAdmissible c = true) :
    0 < c.cflDen ∧ c.cflNum * c.maxWavespeed ≤ c.cflDen ∧
    0 < c.kappa1Num ∧ 0 < c.kappa1Den ∧ c.numVars = 6 ∧
    0 < c.alphaMinMilli ∧ c.alphaMinMilli < c.alphaMaxMilli := by
  unfold checkRelativityZ4cAdmissible at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hOk
  exact ⟨hOk.1.1.1.1.1.1.1.1.1.1.2, hOk.1.1.1.1.1.2, hOk.1.1.1.1.1.1.1.1.2,
         hOk.1.1.1.1.1.1.1.1.1.1.1.2, hOk.1.1.1.1.1.1.1.2, hOk.1.1.2, hOk.1.1.1.1.2⟩

example : checkRelativityZ4cAdmissible RelativityZ4cConfig.ofObend = true := by decide +kernel
example : checkRelativityZ4cAdmissible { RelativityZ4cConfig.ofObend with cflNum := 2 } = false := by
  decide +kernel

#tooth checkRelativityZ4cAdmissible_sound by mutation checkRelativityZ4cAdmissible := fun _ => true

private def mkRatObj (n : Int) (d : Nat) : Json :=
  Json.mkObj [("num", toJson n), ("den", toJson d)]

/-- Compact 4-cell periodic gauge-wave + planted-`Theta` request JSON for kernel `decide +kernel`
verification of `pdeNonlinear` on `BonaMassoZ4c1D`. -/
private def z4cMiniReq (backend : String) (steps : Nat) (compareQ32 : Bool) : Json :=
  let cell (s c : Int) : Json :=
    .arr #[mkRatObj (8 + s) 8, mkRatObj (8 + s) 4, mkRatObj c 8, mkRatObj c 8, mkRatObj c 16, mkRatObj c 8]
  Json.mkObj
    [ ("format", toJson "nonlinear-conservation@1")
    , ("solver", toJson "BonaMassoZ4c1D")
    , ("dims", toJson ([4] : List Nat))
    , ("steps", toJson steps)
    , ("backend", toJson backend)
    , ("boundary", toJson "periodic")
    , ("strang", toJson false)
    , ("recordTrajectory", toJson true)
    , ("compareQ32", toJson compareQ32)
    , ("initial", .arr #[cell 0 1, cell 1 0, cell 0 (-1), cell (-1) 0]) ]

private def thetaInfNormOfGridJson (grid : Json) : Rat :=
  match grid.getArr? with
  | .ok rows =>
    rows.toList.foldl (fun acc row =>
      match row.getArr? with
      | .ok cols =>
        match cols[5]? with
        | some j =>
          match rat j with
          | .ok q => let a := ratAbs q; if acc ≤ a then a else acc
          | .error _ => acc
        | none => acc
      | .error _ => acc) 0
  | .error _ => 0

private def checkThetaStrictlyDamped (out : Json) : Bool :=
  match out.getObjVal? "trajectory" >>= Json.getArr? with
  | .ok arr =>
    let norms := arr.toList.map thetaInfNormOfGridJson
    match norms with
    | [n0, n1, n2] => decide (n2 < n1) && decide (n1 < n0)
    | _ => false
  | .error _ => false

private def tamperReceiptHex (out : Json) : Json :=
  let bad := "0000000000000000000000000000000000000000000000000000000000000000"
  out.setObjVal! "receiptHex" (toJson bad)

private def cflViolatingZ4cSexpr : String :=
  "(conservation-law (name BadZ4cCfl) (coords x) (vars alpha gxx Ax Dx Kxx Theta) " ++
  "(params (fBM 2) (beta 1/5) (kappa1 1/2)) (domain (> alpha 0) (> gxx 0)) " ++
  "(fluxes (x (let ((trK (/ Kxx gxx)) (kHat (- trK (* 2 Theta)))) " ++
  "(- (* beta alpha)) (- (* beta gxx)) (+ (- (* beta Ax)) (* fBM (* alpha kHat))) " ++
  "(+ (- (* beta Dx)) (* alpha trK)) (+ (- (* beta Kxx)) (* alpha Ax)) (- (* beta Theta))))) " ++
  "(sources (- (* (sq alpha) fBM (- (/ Kxx gxx) (* 2 Theta)))) (- (* 2 alpha Kxx)) 0 0 " ++
  "(- (* alpha (- (* Ax Dx) (/ (sq Kxx) gxx))) (* kappa1 (* alpha Theta))) " ++
  "(- (* kappa1 (* alpha Theta)))) " ++
  "(max-wavespeed 9) (cfl 1/2) (limiter minmod))"

private def z4cKernelInit : List (List Rat) :=
  [ [5 / 4, 2, 0, 0, 0, 1 / 8]
  , [5 / 4, 2, 0, 0, 0, -(1 / 8)] ]

private def z4cKernelProbRat : PdeProblem :=
  { spec := BonaMassoZ4c1D.spec
  , law := "catalog:BonaMassoZ4c1D"
  , dims := [2]
  , steps := 2
  , q32 := false
  , policy := .periodic
  , useStrang := false
  , initial := z4cKernelInit }

private def z4cKernelProbQ32 : PdeProblem :=
  { z4cKernelProbRat with q32 := true }

private def thetaInfNormOfRatGrid (grid : List (List Rat)) : Rat :=
  grid.foldl (fun acc row =>
    match row[5]? with
    | some q => let a := ratAbs q; if acc ≤ a then a else acc
    | none => acc) 0

private def maxRatGridDiff (a b : List (List Rat)) : Rat :=
  (a.zip b).foldl (fun m rs =>
    (rs.1.zip rs.2).foldl (fun m xy => let d := ratAbs (xy.1 - xy.2); if m ≤ d then d else m) m) 0

/-- Kernel-decided (`decide +kernel`) witness on `BonaMassoZ4c1D`:
1. Both `"rat"` and `"q32"` rollouts strictly damp `||Theta^k||_inf` across `k = 0 -> 1 -> 2`,
2. `q32` vs `rat` final max-norm difference is `< 10^-6`,
3. 256-bit `pdeReceiptHex` has 64 hex digits and differs from a tampered 1-nibble digest,
4. CFL-violating Z4c S-expression (`aMax = 9`, `cfl = 1/2`) is rejected by `validatePdeSolverSexpr`. -/
example :
    (let trRat := z4cKernelProbRat.exactTrace
     let trQ32 := z4cKernelProbQ32.exactTrace
     let nRat := trRat.map thetaInfNormOfRatGrid
     let nQ32 := trQ32.map thetaInfNormOfRatGrid
     let dampOk := match nRat, nQ32 with
       | [r0, r1, r2], [q0, q1, q2] =>
         decide (r2 < r1) && decide (r1 < r0) && decide (q2 < q1) && decide (q1 < q0)
       | _, _ => false
     let diffOk := decide (maxRatGridDiff z4cKernelProbRat.exactFinal z4cKernelProbQ32.exactFinal < (1 / 1000000 : Rat))
     let rh := pdeReceiptHex (z4cKernelProbRat.statement z4cKernelProbRat.exactFinal)
     let badRh := "0000000000000000000000000000000000000000000000000000000000000000"
     let receiptOk := (rh.length == 64) && (rh != badRh)
     let cflBad := match Obend.Elab.PdeSolverElab.validatePdeSolverSexpr cflViolatingZ4cSexpr with
       | .error _ => true
       | .ok _ => false
     dampOk && diffOk && receiptOk && cflBad) = true := by
  -- Evaluate the receipt through the proved byte-array implementation of cSHAKE.
  simp only [pdeReceiptHex, pdeTrajectoryDigest, Obend.Core.Digest.deployed,
    Obend.Digest.Cshake256.cshake256Bytes_eq_native]
  decide +kernel

/-- End-to-end executable `pdeNonlinear` CLI checks on `BonaMassoZ4c1D` (accepted `"rat"` and `"q32"`
gauge-wave + planted-`Theta` solve/check, monotonic `||Theta^k||_inf` damping, `q32VsRatMaxDiff < 10^-6`,
tampered 256-bit `receiptHex` refused at stage `"receipt"`, and CFL-violating S-expr refused at
stage `"validate-pde-sexpr"`). -/
private def checkPdeNonlinearEndToEnd : Bool :=
  match pdeNonlinear true (z4cMiniReq "rat" 2 true),
        pdeNonlinear true (z4cMiniReq "q32" 2 false) with
  | .ok (0, outRat), .ok (0, outQ32) =>
    let receiptOk := (outRat.getObjValAs? String "receiptHex").toOption.any (fun s => s.length == 64)
    let diffOk := match outRat.getObjVal? "q32VsRatMaxDiff" >>= rat with
      | .ok d => decide (d < (1 / 1000000 : Rat))
      | .error _ => false
    let checkRatOk := match pdeNonlinear false outRat with
      | .ok (0, v) => (v.getObjValAs? Bool "ok").toOption == some true
      | _ => false
    let checkQ32Ok := match pdeNonlinear false outQ32 with
      | .ok (0, v) => (v.getObjValAs? Bool "ok").toOption == some true
      | _ => false
    let tamperRefused := match pdeNonlinear false (tamperReceiptHex outRat) with
      | .ok (3, v) => (v.getObjValAs? String "stage").toOption == some "receipt"
      | _ => false
    let cflBadReq := Json.mkObj
      [ ("format", toJson "nonlinear-conservation@1")
      , ("sexpr", toJson cflViolatingZ4cSexpr)
      , ("dims", toJson ([4] : List Nat))
      , ("steps", toJson (1 : Nat))
      , ("initial", (z4cMiniReq "rat" 1 false).getObjValD "initial") ]
    let cflRefused := match pdeNonlinear true cflBadReq with
      | .ok (1, v) => (v.getObjValAs? String "stage").toOption == some "validate-pde-sexpr"
      | _ => false
    receiptOk && diffOk && checkRatOk && checkQ32Ok &&
    checkThetaStrictlyDamped outRat && checkThetaStrictlyDamped outQ32 &&
    tamperRefused && cflRefused
  | _, _ => false

#guard checkPdeNonlinearEndToEnd == true

end Obend.Apps.RelativityZ4cApp
end
