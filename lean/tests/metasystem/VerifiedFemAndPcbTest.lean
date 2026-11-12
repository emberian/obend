module
/-
# Metasystem Verification Suite — Simplicial FEEC / Prager–Synge Continuum FEM, PCB Multiphysics & DFM Envelopes

End-to-end positive witnesses, planted-fault refusal & refutation witnesses, inhabitedness
certificates, `#tooth` mutation-killing probes (`≥ 6`, 10 total), and `#assert_axioms_tree`
soundness audit across:
1. `Obend.Analysis.VerifiedSimplicialFem`:
   - 2D triangular & 3D tetrahedral CAD-conforming meshes bridged to `GeometryCAM.FRepExpr`,
   - Whitney $W^0$ ($P_1$) stiffness matrix assembly & Dirichlet-connected SPD,
   - $H(\mathrm{div})$ Raviart–Thomas ($RT_0$) element-wise & global Green's identity,
   - Constant-free Prager–Synge hypercircle continuum error bound, Thomson–Dirichlet two-sided
     capacitance brackets, and total `Obend.Judge` instance `feecPragerSyngeJudge` (`"feec-prager-synge@1"`).
2. `Obend.Hardware.PCB`:
   - Preserved Hammerstad–Jensen / Bahl–Garg single-ended microstrip contracts,
   - PCB DFM & manufacturing tolerance envelopes (copper etch undercut, drill aspect ratio, via
     annular-ring registration, acute-angle acid-trap refusal, solder-mask sliver immunity,
     stackup copper-balance thieving),
   - FEM-bracketed coupled differential $(\mathbf{L}, \mathbf{C})$, DFM-propagated $Z_{\text{diff}}$
     & capacitive-imbalance mode-conversion bounds, split return-plane slot inductance penalty,
     $\lambda_{\min}/20$ stitching-via Faraday fence, and continuous-band 2D plane-pair PDN impedance.
-/
public import Obend.Analysis.VerifiedSimplicialFem
public import Obend.Hardware.PCB
public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
meta import all Obend.Analysis.VerifiedSimplicialFem
meta import all Obend.Hardware.PCB
meta import all Obend.Hardware.GeometryCAM
meta import all Obend.Hardware.Accelerators
meta import all Obend.Hardware.HDL
import all Obend.Hardware.PCB
import all Obend.Analysis.VerifiedSimplicialFem
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.Accelerators
import all Obend.Hardware.HDL
import all Obend.Judge.Class
import all Obend.Core.Term
import all Obend.Tactic.Tooth
import all Obend.AssertAxioms

namespace Obend.Tests.Metasystem.VerifiedFemAndPcbTest

open Obend.Hardware.GeometryCAM
open Obend.Analysis.VerifiedSimplicialFem
open Obend.Hardware.PCB

set_option autoImplicit false

/-! ## 1. CAD-Conforming 2D/3D Simplicial Meshes & `GeometryCAM.FRepExpr` Boundary Bridge -/

def unitTetMesh3D : SimplexMesh3D where
  verts := [⟨0, 0, 0⟩, ⟨2, 0, 0⟩, ⟨0, 3, 0⟩, ⟨0, 0, 1⟩]
  tets := [{ i0 := 0, i1 := 1, i2 := 2, i3 := 3, epsScalar := 4, sourceF := 0 }]

example : checkTetMeshOriented unitTetMesh3D = true := by decide +kernel
example : tetVolume3D ⟨0, 0, 0⟩ ⟨2, 0, 0⟩ ⟨0, 3, 0⟩ ⟨0, 0, 1⟩ = 1 := by decide +kernel

example (u0 u1 u2 u3 c : Rat) :
    p1TetGrad3D ⟨0, 0, 0⟩ ⟨2, 0, 0⟩ ⟨0, 3, 0⟩ ⟨0, 0, 1⟩ (u0 + c) (u1 + c) (u2 + c) (u3 + c) =
    p1TetGrad3D ⟨0, 0, 0⟩ ⟨2, 0, 0⟩ ⟨0, 3, 0⟩ ⟨0, 0, 1⟩ u0 u1 u2 u3 :=
  (tetMeshOriented_sound unitTetMesh3D (by decide +kernel) _ (List.mem_cons_self ..)).2 u0 u1 u2 u3 c

/-- 4-triangle inhomogeneous substrate/air cross-section mesh on $[0, 1] \times [0, 1]$ with center vertex `(1/2, 1/2)`
in `.interior` CAD role ($f(1/2, 1/2) = -1/2 \le 0$). -/
def fourTriCrossSectionMesh : SimplexMesh2D where
  verts := [⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1 / 2, 1 / 2⟩]
  vertRoles := [.outerBoundary, .outerBoundary, .conductorBoundary 1, .conductorBoundary 1, .interior]
  tris :=
    [ { i0 := 0, i1 := 1, i2 := 4, eps := Mat2Q.isotropic 4, sourceF := 0 }
    , { i0 := 1, i1 := 2, i2 := 4, eps := Mat2Q.isotropic 4, sourceF := 0 }
    , { i0 := 2, i1 := 3, i2 := 4, eps := Mat2Q.isotropic 2, sourceF := 0 }
    , { i0 := 3, i1 := 0, i2 := 4, eps := Mat2Q.isotropic 4, sourceF := 0 } ]
  dirichletEdges := [(0, 1), (2, 3)]
  neumannEdges := [(1, 2), (3, 0)]

example :
    checkMeshConformingAndCadValid fourTriCrossSectionMesh unitSquareCadFRep
      (.sub .varY (.const 1)) 0 (1 / 100) 20 = true := by decide +kernel

/-- Continuous barycentric point `(1/4, 1/4, 0)` inside triangle `0` is enclosed by `triBoundingQBox`. -/
example :
    (evalFRepIntervalQ (triBoundingQBox ⟨0, 0⟩ ⟨1, 0⟩ ⟨1 / 2, 1 / 2⟩ 0) unitSquareCadFRep).contains
      (evalFRepQ (1 / 4 * 0 + 1 / 4 * 1 + 1 / 2 * (1 / 2))
                 (1 / 4 * 0 + 1 / 4 * 0 + 1 / 2 * (1 / 2)) 0 unitSquareCadFRep) :=
  triBoundingQBox_frep_enclosure_sound ⟨0, 0⟩ ⟨1, 0⟩ ⟨1 / 2, 1 / 2⟩ 0 (1 / 4) (1 / 4) (1 / 2)
    unitSquareCadFRep (by grind) (by grind) (by grind) (by grind)

/-- Planted inverted triangle (`i1` and `i2` swapped, $\det J_T = -1 < 0$): refused by mesh checker and Judge! -/
def invertedTriMesh : SimplexMesh2D :=
  { unitSquareCapMesh with
      tris := [ { i0 := 0, i1 := 2, i2 := 1, eps := Mat2Q.isotropic 4, sourceF := 0 }
              , { i0 := 0, i1 := 2, i2 := 3, eps := Mat2Q.isotropic 4, sourceF := 0 } ] }

def invertedTriProblem : FeecPdeProblem2D := { unitSquareCapProblem with mesh := invertedTriMesh }

example :
    checkMeshConformingAndCadValid invertedTriMesh unitSquareCadFRep
      (.sub .varY (.const 1)) 0 (1 / 100) 10 = false := by decide +kernel

example :
    feecPragerSyngeJudge.check 0 invertedTriProblem unitSquareCapCert =
      .refused .invalidOrInvertedElement [] := by
  unfold Obend.Judge.check feecPragerSyngeJudge
  decide +kernel

/-- Universal refutation: NO certificate can satisfy `CertifiedFeecPde` on an inverted mesh. -/
example (cert' : FeecPragerSyngeCert2D) : ¬ CertifiedFeecPde invertedTriProblem cert' := by
  refine feecPragerSyngeJudge.refuted (r := 0) (o := invertedTriProblem) (c := unitSquareCapCert)
    (k := .invalidOrInvertedElement) (p := []) ?_ ?_ cert'
  · unfold Obend.Judge.check feecPragerSyngeJudge; decide +kernel
  · unfold Obend.Judge.refutes feecPragerSyngeJudge feecRefutes; rfl

/-- Planted hanging-node mesh (midpoint `(1/2, 0)` lying strictly inside boundary edge `(0, 1)`): refused! -/
def hangingNodeMesh : SimplexMesh2D :=
  { unitSquareCapMesh with
      verts := unitSquareCapMesh.verts ++ [⟨1 / 2, 0⟩]
      vertRoles := unitSquareCapMesh.vertRoles ++ [.outerBoundary] }

def hangingNodeProblem : FeecPdeProblem2D := { unitSquareCapProblem with mesh := hangingNodeMesh }

example :
    feecPragerSyngeJudge.check 0 hangingNodeProblem unitSquareCapCert =
      .refused .nonConformingMeshTopology [] := by
  unfold Obend.Judge.check feecPragerSyngeJudge
  decide +kernel

example (cert' : FeecPragerSyngeCert2D) : ¬ CertifiedFeecPde hangingNodeProblem cert' := by
  refine feecPragerSyngeJudge.refuted (r := 0) (o := hangingNodeProblem) (c := unitSquareCapCert)
    (k := .nonConformingMeshTopology) (p := []) ?_ ?_ cert'
  · unfold Obend.Judge.check feecPragerSyngeJudge; decide +kernel
  · unfold Obend.Judge.refutes feecPragerSyngeJudge feecRefutes; rfl

/-- Planted CAD violation (interior vertex placed at `(2, 2)` outside unit-square CAD solid): refused! -/
def cadOutlierProblem : FeecPdeProblem2D :=
  { unitSquareCapProblem with
      mesh := { fourTriCrossSectionMesh with
                  verts := [⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩]
                  tris := [ { i0 := 0, i1 := 1, i2 := 2, eps := Mat2Q.isotropic 4, sourceF := 0 }
                          , { i0 := 0, i1 := 2, i2 := 3, eps := Mat2Q.isotropic 4, sourceF := 0 } ] } }

example :
    feecPragerSyngeJudge.check 0 cadOutlierProblem unitSquareCapCert =
      .refused .cadBoundaryViolation [] := by
  unfold Obend.Judge.check feecPragerSyngeJudge
  decide +kernel

/-! ## 2. Whitney $P_1$, $RT_0$ Green's Identity, Prager–Synge Hypercircle & Thomson–Dirichlet Brackets -/

/-- Exact $3 \times 3$ element stiffness matrix assembly matches continuous bilinear form. -/
example :
    let fin3 : List (Fin 3) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
    let t := unitSquareCapMesh.tris.getD 0 { i0 := 0, i1 := 1, i2 := 2, eps := Mat2Q.isotropic 4, sourceF := 0 }
    sumList fin3 (fun a => sumList fin3 (fun b =>
      elemLocalDof [0, 0, 1, 1] t a * elemStiffnessEntry unitSquareCapMesh.verts t a b *
        elemLocalDof [0, 1 / 2, 1, 1 / 3] t b)) =
    elemStiffnessBilinear unitSquareCapMesh.verts t [0, 0, 1, 1] [0, 1 / 2, 1, 1 / 3] := by
  decide +kernel

/-- Global Poisson $RT_0$ equilibration with non-zero volumetric source $f_T = -4$ ($\operatorname{div}\sigma_h = 4$). -/
def poissonSourceMesh : SimplexMesh2D :=
  { unitSquareCapMesh with
      tris := [ { i0 := 0, i1 := 1, i2 := 2, eps := Mat2Q.isotropic 1, sourceF := -4 }
              , { i0 := 0, i1 := 2, i2 := 3, eps := Mat2Q.isotropic 1, sourceF := -4 } ]
      dirichletEdges := [(0, 1), (1, 2), (2, 3), (3, 0)]
      neumannEdges := [] }

def poissonSourceFlux : List Rt0ElementFlux2D := [⟨-1, -1, 2⟩, ⟨-1, -1, 2⟩]

example : checkRt0Equilibrated poissonSourceMesh poissonSourceFlux = true := by decide +kernel

/-- Concrete Thomson–Dirichlet two-sided brackets:
1. Inhomogeneous substrate/air cross-section (`fourTriCrossSectionMesh`): `[16/5, 7/2]` (`3.2 < 3.5`).
2. Homogeneous cross-section (`uniformFourTriMesh`) with suboptimal primal trial field: `4 < 5` and `η_PS² = 1`. -/
def inhomTrialUh : List Rat := [0, 0, 1, 1, 1 / 2]
def inhomTrialFlux : List Rt0ElementFlux2D := [⟨0, -1, 0⟩, ⟨0, -1, 0⟩, ⟨0, -1, 0⟩, ⟨0, -1, 0⟩]

example :
    checkRt0Equilibrated fourTriCrossSectionMesh inhomTrialFlux = true ∧
    capacitanceLowerBound fourTriCrossSectionMesh inhomTrialUh inhomTrialFlux = 16 / 5 ∧
    capacitanceUpperBound fourTriCrossSectionMesh inhomTrialUh = 7 / 2 ∧
    capacitanceLowerBound fourTriCrossSectionMesh inhomTrialUh inhomTrialFlux <
      capacitanceUpperBound fourTriCrossSectionMesh inhomTrialUh := by
  decide +kernel

def approxTrialUh : List Rat := [0, 0, 1, 1, 3 / 4]
def approxTrialFlux : List Rt0ElementFlux2D :=
  [⟨0, -4, 0⟩, ⟨0, -4, 0⟩, ⟨0, -4, 0⟩, ⟨0, -4, 0⟩]

def uniformFourTriMesh : SimplexMesh2D :=
  { fourTriCrossSectionMesh with
      tris :=
        [ { i0 := 0, i1 := 1, i2 := 4, eps := Mat2Q.isotropic 4, sourceF := 0 }
        , { i0 := 1, i1 := 2, i2 := 4, eps := Mat2Q.isotropic 4, sourceF := 0 }
        , { i0 := 2, i1 := 3, i2 := 4, eps := Mat2Q.isotropic 4, sourceF := 0 }
        , { i0 := 3, i1 := 0, i2 := 4, eps := Mat2Q.isotropic 4, sourceF := 0 } ] }

example : checkRt0Equilibrated uniformFourTriMesh approxTrialFlux = true := by decide +kernel
example :
    capacitanceLowerBound uniformFourTriMesh approxTrialUh approxTrialFlux = 4 ∧
    capacitanceUpperBound uniformFourTriMesh approxTrialUh = 5 ∧
    pragerSyngeEstimatorSq uniformFourTriMesh approxTrialUh approxTrialFlux = 1 := by
  decide +kernel

/-- Concrete instantiation of `pragerSynge_continuum_error_bound` & `thomsonDirichlet_capacitance_bracket`
on `meshContinuumEnergySpace` for `uniformFourTriMesh` against exact harmonic field $\nabla u = (0, 1)$. -/
def exactGradUField : MeshMidpointField := fun _ => (⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩)
def approxGradUhField : MeshMidpointField := fun k =>
  let t := uniformFourTriMesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
  let g := p1ElemGrad uniformFourTriMesh.verts t approxTrialUh
  (g, g, g)
def approxEpsInvSigmaField : MeshMidpointField := fun k =>
  let t := uniformFourTriMesh.tris.getD k { i0 := 0, i1 := 0, i2 := 0, eps := Mat2Q.isotropic 1, sourceF := 0 }
  let σ := approxTrialFlux.getD k ⟨0, 0, 0⟩
  let v0 := getVert2D uniformFourTriMesh.verts t.i0
  let v1 := getVert2D uniformFourTriMesh.verts t.i1
  let v2 := getVert2D uniformFourTriMesh.verts t.i2
  let inv := t.eps.inv
  (inv.mulVec (rt0Eval σ (mid2Q v0 v1)),
   inv.mulVec (rt0Eval σ (mid2Q v1 v2)),
   inv.mulVec (rt0Eval σ (mid2Q v2 v0)))

theorem uniformFourTriMesh_geom :
    ∀ t ∈ uniformFourTriMesh.tris,
      0 < twiceArea2D (getVert2D uniformFourTriMesh.verts t.i0)
            (getVert2D uniformFourTriMesh.verts t.i1)
            (getVert2D uniformFourTriMesh.verts t.i2) ∧
      t.eps.isSpd := by
  have hS := checkMeshConformingAndCadValid_sound uniformFourTriMesh unitSquareCadFRep
    (.sub .varY (.const 1)) 0 (1 / 100) 20 (by decide +kernel)
  intro t ht
  exact ⟨(hS.2.2.2.1 t ht).1, (hS.2.2.2.1 t ht).2.2.2⟩

example :
    let H := meshContinuumEnergySpace uniformFourTriMesh uniformFourTriMesh_geom
    H.normSq (H.sub exactGradUField approxGradUhField) ≤
      pragerSyngeEstimatorSq uniformFourTriMesh approxTrialUh approxTrialFlux ∧
    capacitanceLowerBound uniformFourTriMesh approxTrialUh approxTrialFlux ≤ 4 ∧
    (4 : Rat) ≤ capacitanceUpperBound uniformFourTriMesh approxTrialUh := by
  intro H
  refine ⟨pragerSynge_continuum_error_bound H uniformFourTriMesh approxTrialUh approxTrialFlux
            exactGradUField approxGradUhField approxEpsInvSigmaField
            (by decide +kernel) (by decide +kernel),
          thomsonDirichlet_capacitance_bracket H uniformFourTriMesh approxTrialUh approxTrialFlux
            exactGradUField approxGradUhField approxEpsInvSigmaField 4
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel)⟩

/-- Planted broken $RT_0$ normal-flux jump across interior edge `(0, 2)` and blown error budget refusals. -/
example :
    checkFeecPragerSynge unitSquareCapProblem
      { uh := [0, 0, 1, 1], flux := [⟨0, -4, 0⟩, ⟨2, -4, 0⟩] } =
      .refused .brokenRt0Equilibration [] := by decide +kernel

example :
    checkFeecPragerSynge
      { unitSquareCapProblem with mesh := uniformFourTriMesh, errorTolSq := 1 / 10 }
      { uh := approxTrialUh, flux := approxTrialFlux } =
      .refused .errorBudgetExceeded [] := by decide +kernel

/-- Judge `Fragment` & `.ok` inhabitedness witness (`feecFormatName = "feec-prager-synge@1"`). -/
example :
    feecFormatName = "feec-prager-synge@1" ∧
    ∃ prob cert, feecPragerSyngeJudge.Fragment prob ∧ feecPragerSyngeJudge.check 0 prob cert = .ok := by
  refine ⟨rfl, unitSquareCapProblem, unitSquareCapCert,
          feecFragment_inhabited_for_tol 0 (by grind), ?_⟩
  unfold Obend.Judge.check feecPragerSyngeJudge
  decide +kernel

/-! ## 3. PCB DFM Envelopes, Coupled Differential Multiphysics, Return Slot, Faraday Fence & PDN -/

/-- Backwards compatibility with legacy single-ended Hammerstad–Jensen microstrip contracts. -/
example :
    75 ≤ 330 ∧
    natAbsDiff 50000 50000 ≤ 3000 ∧
    natAbsDiff (microstripZ0MilliOhm 330 152 35 3480) 50000 ≤ 3000 :=
  singleEndedZ0_sound 330 152 35 3480 50000 50000 3000 (by decide +kernel)

/-- Planted PCB DFM fault refusals: acute $45^\circ$ acid trap, $30\,\mu\text{m}$ mask sliver, via breakout, copper warpage. -/
example :
    checkPcbDfmEnvelope ipcClass3RfFab { ipcClass3RfLayout with minTraceAngleDeg := 45 } = false ∧
    checkPcbDfmEnvelope ipcClass3RfFab { ipcClass3RfLayout with padPitchNm := 360000 } = false ∧
    checkPcbDfmEnvelope ipcClass3RfFab { ipcClass3RfLayout with viaPadRadiusNm := 180000 } = false ∧
    checkPcbDfmEnvelope ipcClass3RfFab
      { ipcClass3RfLayout with symLayerCopperPairsPermille := [(800, 300)] } = false := by
  decide +kernel

/-- Concrete manufactured corner inside `ipcClass3RfFab` (`dw1 = +12000 nm`, `dw2 = +6000 nm`, `dh = -8000 nm`):
`dfm_differential_zdiff_and_skew_sound` certifies `90 Ω ≤ Z_diff ≤ 110 Ω` and `|C_11 - C_22| < 1.5 pF/m`. -/
def concreteBoardCorner : PcbDiffPairCorner where
  dw1Nm := 12000
  dw2Nm := 6000
  dhNm := -8000
  cOddCornerAttoF := 100000000
  lOddCornerPicoH := 250000
  c11CornerAttoF := 80400000
  c22CornerAttoF := 79800000
  zDiffCornerMilliOhm := 100000

example :
    (sampleDiffSensitivity.zDiffMinMilliOhm : Rat) ≤ concreteBoardCorner.zDiffCornerMilliOhm ∧
    concreteBoardCorner.zDiffCornerMilliOhm ≤ (sampleDiffSensitivity.zDiffMaxMilliOhm : Rat) ∧
    ratAbs (concreteBoardCorner.c11CornerAttoF - concreteBoardCorner.c22CornerAttoF) <
      sampleDiffSensitivity.maxCapImbalanceAttoF :=
  dfm_differential_zdiff_and_skew_sound ipcClass3RfFab ipcClass3RfLayout
    coupledDiffSampleExtraction sampleDiffSensitivity (by decide +kernel) concreteBoardCorner
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
     by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Split return-plane slot refusal (unbridged or stitch span $> \lambda_{\min}/20$) & Faraday fence refusal. -/
example :
    checkHighSpeedReturnPathContinuity 200000 10000000 150000 16000000 false 600000 100 = false ∧
    checkHighSpeedReturnPathContinuity 200000 10000000 150000 16000000 true 1000000 100 = false ∧
    checkStitchingViaFaradayFence 1000000 200000 16000000 10 = false := by
  decide +kernel

/-- Continuous-band 2D PDN soundness evaluated at interior angular frequency $\omega = 5 \times 10^7\,\text{rad/s}$. -/
def resonantBandPdnSpec : PdnPlanePairSpec :=
  { sampleCorePdnSpec with planePlusDecapFarad := 1 / 250000, omegaMinRadPerSec := 25000000 }

example :
    2 * (50000000 : Rat) ≤ resonantBandPdnSpec.cavityFirstModeRadPerSec ∧
    pdnImpedanceMagSqOhmSq resonantBandPdnSpec 50000000 ≤
      pdnTargetImpedanceOhm resonantBandPdnSpec * pdnTargetImpedanceOhm resonantBandPdnSpec ∧
    (1 / 200 : Rat) ≤ pdnTargetImpedanceOhm resonantBandPdnSpec :=
  pdn_target_impedance_sound resonantBandPdnSpec (by decide +kernel) 50000000 (1 / 200)
    ⟨by decide +kernel, by decide +kernel⟩ (by grind) (by decide +kernel)

/-- Unified board-level multiphysics inhabitedness witness. -/
example :
    ∃ fab layout ext sens,
      checkPcbMultiphysicsBoard fab layout ext sens
        200000 10000000 150000 16000000 true 600000 100
        750000 200000 10 sampleCorePdnSpec = true :=
  ⟨ipcClass3RfFab, ipcClass3RfLayout, coupledDiffSampleExtraction, sampleDiffSensitivity,
   by decide +kernel⟩

/-! ## 4. `#tooth` Kernel Mutation Kills (10 Probes Across FEEC FEM & PCB Multiphysics) -/

/-- Tooth 1: Omitting strict orientation $\det J_T > 0$ breaks `checkMeshConformingAndCadValid_sound`. -/
def checkTriElementSkipOrientation (verts : List Point2Q) (maxAspectRatio : Rat) (t : TriElement2D) : Bool :=
  let v0 := getVert2D verts t.i0; let v1 := getVert2D verts t.i1; let v2 := getVert2D verts t.i2
  decide (t.i0 < verts.length) &&
  decide (sumEdgeLenSq2D v0 v1 v2 ≤ maxAspectRatio) &&
  t.eps.isSpdB
#tooth Obend.Analysis.VerifiedSimplicialFem.checkMeshConformingAndCadValid_sound by mutation
  Obend.Analysis.VerifiedSimplicialFem.checkTriElementValid := checkTriElementSkipOrientation

/-- Tooth 2: Omitting 3D tetrahedral positive-volume check breaks `tetMeshOriented_sound`. -/
def checkTetMeshSkipVolume (m : SimplexMesh3D) : Bool :=
  !m.tets.isEmpty && decide (0 < m.verts.length)
#tooth Obend.Analysis.VerifiedSimplicialFem.tetMeshOriented_sound by mutation
  Obend.Analysis.VerifiedSimplicialFem.checkTetMeshOriented := checkTetMeshSkipVolume

/-- Tooth 3: Breaking shared-edge affine weighting breaks `p1_shared_edge_trace_continuous`. -/
def p1EdgeTraceBiased (uh : List Rat) (a b : Nat) (s : Rat) : Rat :=
  (1 - s) * uh.getD a 0 + 2 * s * uh.getD b 0
#tooth Obend.Analysis.VerifiedSimplicialFem.p1_shared_edge_trace_continuous by mutation
  Obend.Analysis.VerifiedSimplicialFem.p1EdgeTrace := p1EdgeTraceBiased

/-- Tooth 4: Dropping spatial dimension factor `2` in $\operatorname{div}(a + b x) = 2b$ breaks Green's identity! -/
def rt0DivWrongDim (σ : Rt0ElementFlux2D) : Rat := σ.b
#tooth Obend.Analysis.VerifiedSimplicialFem.rt0_elem_greens_identity_p2 by mutation
  Obend.Analysis.VerifiedSimplicialFem.rt0Div := rt0DivWrongDim

/-- Tooth 5: Inflating dual capacitance lower bound by `+ 1` breaks `thomsonDirichlet_capacitance_bracket`. -/
def capacitanceLowerBoundInflated (mesh : SimplexMesh2D) (uh : List Rat) (flux : List Rt0ElementFlux2D) : Rat :=
  let q := dualNetElectrodeCharge mesh uh flux
  (q * q) / dualComplementaryEnergy mesh flux + 1
#tooth Obend.Analysis.VerifiedSimplicialFem.thomsonDirichlet_capacitance_bracket by mutation
  Obend.Analysis.VerifiedSimplicialFem.capacitanceLowerBound := capacitanceLowerBoundInflated

/-- Tooth 6: Omitting regional copper thieving balance check breaks `checkCopperDensityBalanced_sound`. -/
def checkCopperDensitySkipRegion (maxDeltaPermille : Nat) (symPairs : List (Nat × Nat)) (regionTiles : List Nat) : Bool :=
  !symPairs.isEmpty && !regionTiles.isEmpty &&
  symPairs.all (fun p => decide (natAbsDiff p.1 p.2 ≤ maxDeltaPermille))
#tooth Obend.Hardware.PCB.checkCopperDensityBalanced_sound by mutation
  Obend.Hardware.PCB.checkCopperDensityBalanced := checkCopperDensitySkipRegion

/-- Tooth 7: Omitting drill wander & layer registration shift in annular-ring check breaks `dfm_via_breakout_impossible`. -/
def checkPcbDfmSkipRegistration (fab : PcbFabCapabilities) (layout : PcbLayoutRules) : Bool :=
  decide (0 < layout.viaDrillRadiusNm) &&
  decide (layout.viaDrillRadiusNm + fab.minAnnularRingNm ≤ layout.viaPadRadiusNm)
#tooth Obend.Hardware.PCB.dfm_via_breakout_impossible by mutation
  Obend.Hardware.PCB.checkPcbDfmEnvelope := checkPcbDfmSkipRegistration

/-- Tooth 8: Omitting DFM corner capacitive-skew check breaks `dfm_differential_zdiff_and_skew_sound`. -/
def checkDfmDiffSkipSkew (fab : PcbFabCapabilities) (layout : PcbLayoutRules)
    (ext : CoupledFemExtraction2D) (sens : CoupledProcessSensitivity) : Bool :=
  checkPcbDfmEnvelope fab layout &&
  checkCoupledFemExtraction ext &&
  decide (sens.zDiffMinMilliOhm ≤ sens.zDiffMaxMilliOhm)
#tooth Obend.Hardware.PCB.dfm_differential_zdiff_and_skew_sound by mutation
  Obend.Hardware.PCB.checkDfmDiffImpedanceAndSkew := checkDfmDiffSkipSkew

/-- Tooth 9: Negating split return-plane slot inductance penalty breaks `slot_inductance_penalty_pos`. -/
def slotPenaltyFlippedSign (slotGapNm detourSpanNm traceHeightNm : Nat) : Rat :=
  -(((slotGapNm + detourSpanNm + traceHeightNm : Nat) : Rat))
#tooth Obend.Hardware.PCB.slot_inductance_penalty_pos by mutation
  Obend.Hardware.PCB.slotLoopInductancePenaltyPicoH := slotPenaltyFlippedSign

/-- Tooth 10: Checking PDN impedance only at $\omega_{\min}$ (omitting $\omega_{\max}$) breaks `pdn_target_impedance_sound`. -/
def checkPdnSkipMaxEndpoint (p : PdnPlanePairSpec) : Bool :=
  decide (pdnImpedanceMagSqOhmSq p p.omegaMinRadPerSec ≤
    pdnTargetImpedanceOhm p * pdnTargetImpedanceOhm p)
#tooth Obend.Hardware.PCB.pdn_target_impedance_sound by mutation
  Obend.Hardware.PCB.checkPdnTargetImpedance := checkPdnSkipMaxEndpoint

#assert_axioms_tree

end Obend.Tests.Metasystem.VerifiedFemAndPcbTest
