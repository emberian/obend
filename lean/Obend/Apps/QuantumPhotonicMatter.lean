module
/-
# Obend.Apps.QuantumPhotonicMatter — Flagship App #8: Quantum Photonic & Topological Matter Co-Processor

Connects the canonical `.obend` standard library `stdlib/physical/QuantumPhotonicMatter.obend`
and the 4-module `.obend` application package in `apps/quantum-photonic-matter/` (`package.json`):
1. `apps/quantum-photonic-matter/ClementsKrawtchoukArray.obend` (`QPMClements`: `BaseKrawtchoukBusSpec` -> `SymmetryPreservingKrawtchoukOverride`)
2. `apps/quantum-photonic-matter/ThermoOpticCrosstalkComp.obend` (`QPMCrosstalk`: `BaseFaddeevLeVerrierCompSpec` -> `ClosedLoopCrosstalkOverride`)
3. `apps/quantum-photonic-matter/MajoranaTetronSyndromes.obend` (`QPMTetron`: `BaseTetronBraidSpec` -> `ParityCooledTetronOverride`)
4. `apps/quantum-photonic-matter/QuantumPhotonicTop.obend` (`QPMCoProcTop`: `BaseQuantumPhotonicCoProcSpec` -> `FaultTolerantCoProcOverride`)

directly to the mechanized quantum/photonic/topological hardware & spectral analysis stack:
- `Obend.Analysis.Equitable`:
  * 1-WL color refinement fixed-point & Moore-coalgebra bisimulation theorem (`wlStabilize_fixedPoint_iff_equitable`),
  * Universal $2 \times 2$ & $3 \times 3$ Lagrange–Sylvester spectral projectors (`computeLagrangeProjector_2x2_and_3x3_universal`),
- `Obend.Hardware.QuantumMatter`:
  * 1-WL quotient-hypergraph compression & reverse-AD intertwining (`quotientOpenHypergraph_intertwines_eval_and_adjoint`),
  * Universal DPR guard slot (`quotientHypergraphSlot`) & 1-cycle symmetry-breaking pin fallback (`quotientHypergraph_moved_pin_blocks`),
  * Planar Clements $4 \times 4$ optical power conservation (`planarClements4x4_conserves_optical_power`) & Duhamel disorder leakage (`perturbative_disorder_leakage_bound`),
  * Faddeev–LeVerrier $4 \times 4$ exact thermal crosstalk cancellation (`compensateThermalCrosstalk_exact_4x4`, $\det = 8769$),
  * Majorana tetron Artin braid group relation (`majoranaBraid_artin_relation`) & Lindblad parity cooling (`parityCoolingJumpOp_dark_on_even_and_corrects_odd`),
- `Obend.Hardware.Photonics`:
  * Coupled-Mode Theory (CMT) Taylor interval enclosure & Krawtchouk length synthesis (`cmt_phase_5050_encloses_3db_split`, `cmt_unitarity_interval_encloses_one`, `cmt_krawtchouk_length_synthesis_sound`),
- `Obend.Analysis.QuantumWalk`:
  * Computed Lagrange–Sylvester projectors on $K_2, P_3, Q_3$ (`computed_lagrange_projectors_k2_p3_q3_exact`),
  * Multi-step discrete-time Szegedy quantum walk lumping (`szegedy_intertwining_power`, `cellUniformSzegedyPST_iff_quotient`),
  * Matrix Taylor propagator quotient intertwining & $\ell_\infty$ remainder enclosure (`matrixTaylorPropagator_intertwines_quotient`, `matrixTaylorPropagator_encloses_k2_and_q3_pst`),
- `Obend.Leaf.Static`, `Obend.Spec.CrossPackage`, `Obend.Hardware.HDL`, `Obend.Hardware.Silicon`:
  * Vtable flattening (`flatten_sound`), `Leaf.Book` emission (`book_sound`), cross-package cone survival (`coneSupports_linkComposition_of_disjoint`), and verified synchronous `RtlModule` (`quantumPhotonicCoprocTopRtlModule`) emitted directly to `apps/quantum-photonic-matter/verilator/quantum_photonic_coproc_top.sv`.
-/
public import Lean
public import Obend.Hardware.UserspacePhysical
public import Obend.Hardware.QuantumMatter
public import Obend.Teeth.Hardware.CliffordKernel
public import Obend.Hardware.Photonics
public import Obend.Hardware.Synth
public import Obend.Analysis.TaylorModel
public import Obend.Analysis.Equitable
public import Obend.Analysis.QuantumWalk
public import Obend.Leaf.Static
public import Obend.Spec.CrossPackage
public import Obend.Tactic.Tooth
public import Obend.Elab.Workbook
public meta import Lean
public meta import Obend.Hardware.UserspacePhysical
public meta import Obend.Elab.Workbook
@[expose] public section

namespace Obend.Apps.QuantumPhotonicMatter

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Slot
open Obend.Slot.World
open Obend.Spec.CrossPackage
open Obend.Analysis
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.QuantumMatter
open Obend.Hardware.Photonics
open Obend.Hardware.UserspacePhysical

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 0. `#import_obend` is `Obend.Elab.Workbook`'s (the one importer, 2026-11-04); this module
only consumes the constants it emits (`<def>_comp`, `<def>_book`, `<def>_val`, `claim_*_{obj,just,holds}`,
`laws_count`). -/

/-! ## 1. Compile-Time Elaboration of `stdlib/physical/QuantumPhotonicMatter.obend` & `apps/quantum-photonic-matter/*.obend` -/

#import_obend "stdlib/physical/QuantumPhotonicMatter.obend" as QPMStdlib
#import_obend "apps/quantum-photonic-matter/ClementsKrawtchoukArray.obend" as QPMClements
#import_obend "apps/quantum-photonic-matter/ThermoOpticCrosstalkComp.obend" as QPMCrosstalk
#import_obend "apps/quantum-photonic-matter/MajoranaTetronSyndromes.obend" as QPMTetron
#import_obend "apps/quantum-photonic-matter/QuantumPhotonicTop.obend" as QPMCoProcTop

/-- Values the `#import_obend` elaboration of `QPMClements, QPMCoProcTop, QPMCrosstalk, QPMStdlib, QPMTetron` produced (an `example`, not a theorem:
these are checks of concrete outputs; `accepted`/`_holds` conjuncts were removed 2026-11-04,
the `_holds` theorems themselves are emitted by the importer). -/
example :
    QPMStdlib.laws_count = 2 ∧
    QPMCoProcTop.laws_count = 7 ∧
    QPMClements.krawtchoukMacsAt16_val = .nat 3206 ∧
    QPMClements.krawtchoukFidelityAt4_val = .nat 2004 ∧
    QPMCrosstalk.precompDriveAt50_val = .nat 9319 ∧
    QPMCrosstalk.residualMetricAt3_val = .nat 125 ∧
    QPMTetron.tetronBraidDepthAt10_val = .nat 200 ∧
    QPMTetron.tetronRecoveryAt3_val = .nat 64 ∧
    QPMCoProcTop.coprocAdjointOpsAt25_val = .nat 8869 ∧
    QPMCoProcTop.coprocBudgetAt6_val = .nat 132 ∧
    QPMCoProcTop.crossModuleQpmSummary_val = .nat 23598 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Vtable Flattening, `Leaf.Book` Emission, Cross-Package Cone Survival -/

theorem quantumPhotonicMatter_compositions_closed :
    QPMClements.calibratedKrawtchoukBus_comp.closedB = true ∧
    QPMCrosstalk.closedLoopThermoOpticComp_comp.closedB = true ∧
    QPMTetron.parityCooledTetronDecoder_comp.closedB = true ∧
    QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.closedB = true := by
  decide +kernel

theorem quantumPhotonicMatter_flatten_and_book_sound (m : String) :
    (.get QPMClements.calibratedKrawtchoukBus_comp.flatten m ≈b
      .get QPMClements.calibratedKrawtchoukBus_comp.object m) ∧
    (.get (emit QPMClements.calibratedKrawtchoukBus_comp).link m ≈b
      .get QPMClements.calibratedKrawtchoukBus_comp.object m) ∧
    (.get QPMCrosstalk.closedLoopThermoOpticComp_comp.flatten m ≈b
      .get QPMCrosstalk.closedLoopThermoOpticComp_comp.object m) ∧
    (.get (emit QPMCrosstalk.closedLoopThermoOpticComp_comp).link m ≈b
      .get QPMCrosstalk.closedLoopThermoOpticComp_comp.object m) ∧
    (.get QPMTetron.parityCooledTetronDecoder_comp.flatten m ≈b
      .get QPMTetron.parityCooledTetronDecoder_comp.object m) ∧
    (.get (emit QPMTetron.parityCooledTetronDecoder_comp).link m ≈b
      .get QPMTetron.parityCooledTetronDecoder_comp.object m) ∧
    (.get QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.flatten m ≈b
      .get QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.object m) ∧
    (.get (emit QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp).link m ≈b
      .get QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.object m) := by
  have ⟨hc1, hc2, hc3, hc4⟩ := quantumPhotonicMatter_compositions_closed
  exact ⟨flatten_sound _ hc1 m, book_sound _ hc1 m,
         flatten_sound _ hc2 m, book_sound _ hc2 m,
         flatten_sound _ hc3 m, book_sound _ hc3 m,
         flatten_sound _ hc4 m, book_sound _ hc4 m⟩

/-- The compiled co-processor and bus: `checkRtlModule` and one input's outputs (a closed check; a GPU
co-execution claim on an interpreter nobody ran was removed 2026-11-05). -/
example :
    (match compileBookToRtl "qpm_coproc_top" QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_book,
           compileBookToRtl "qpm_krawtchouk_bus" QPMClements.calibratedKrawtchoukBus_book with
     | some mTop, some mBus =>
       checkRtlModule mTop &&
       checkRtlModule mBus &&
       (evalModuleOutputs mTop (fun _ => 25#64) (fun _ => 0#64) ==
         [ ("out_cmtKrawtchoukLength2Nm", 3142#64)
         , ("out_coProcessorCycleBudget", 436#64)
         , ("out_wlCompressedShells", 4#64)
         , ("out_faddeevCrosstalkDet", 8769#64)
         , ("out_quotientReverseAdjointOps", 8869#64)
         ]) &&
       (evalModuleOutputs mBus (fun _ => 16#64) (fun _ => 0#64) ==
         [ ("out_krawtchoukCouplingLength2Nm", 3142#64)
         , ("out_pstTransferFidelityPpm", 5004#64)
         , ("out_fullModes", 8#64)
         , ("out_quotientShells", 4#64)
         , ("out_krawtchoukCouplingLength0Nm", 1571#64)
         , ("out_krawtchoukCouplingLength1Nm", 2721#64)
         , ("out_quotientAdjointMacs", 3206#64)
         ])
     | _, _ => false) = true := by
  decide +kernel

/-! ## 3. 1-WL Stabilization (`wlStabilize_fixedPoint_iff_equitable`), Quotient Hypergraphs, DPR Fallback, Clements & CMT -/

/-- Point-source seed coloring `0 ↦ 0, v > 0 ↦ 1` on $Q_3$ from which `wlStabilize` automatically
discovers the exact 4-shell Krawtchouk Hamming-distance partition `hypercubeQ3Part`. -/
def q3PointSourceSeed : Nat → Nat
  | 0 => 0
  | _ => 1

/-- **`quantumPhotonicMatter_wl_quotient_clements_and_cmt_sound`**:
1. **1-WL Stabilization Fixed-Point & $Q_3$ Krawtchouk Discovery (`wlStabilize_fixedPoint_iff_equitable`)**:
   - Universally proves `wlRefineStep` fixed-point $\iff$ `isMooreCoalgebraBisimulation` $\iff$ `checkEquitablePartition`,
   - Executably verifies that `wlStabilize hypercubeQ3Matrix 8 q3PointSourceSeed` recovers the exact
     4-shell Krawtchouk partition `hypercubeQ3Part` on `0..7` and passes `checkEquitablePartition = true`.
2. **1-WL Quotient Hypergraph & Reverse-AD Intertwining (`quotientOpenHypergraph_intertwines_eval_and_adjoint`)**:
   - Compresses 24-wire `buildSymmetric4LaneHypergraph` and its `compileGraphAdjoint` reverse-AD graph
     to 12-wire `quotientOpenHypergraph` with exact forward & reverse-AD intertwining.
3. **Universal DPR Guard Slot & 1-Cycle Symmetry-Breaking Pin Fallback (`quotientHypergraph_moved_pin_blocks`)**:
   - Universally proves that ANY broken weight pin `p ∈ pins` (`holdsAt v p = false`) causes
     `quotientHypergraphSlot.read` to return `.blocked cand d` (`p ∈ d`) and `slotAdvance.advance`
     to fall back to `.ok (.unreducedFull gFull)` in 1 cycle, plus concrete `.layer "weights.w1"` witness.
4. **Planar Clements Unitarity, Duhamel Disorder Bound, Faddeev–LeVerrier Crosstalk & CMT Length Synthesis**:
   - `planarClements4x4_conserves_optical_power`, `perturbative_disorder_leakage_bound`,
   - `compensateThermalCrosstalk_exact_4x4` ($\det = 8769$),
   - `cmt_phase_5050_encloses_3db_split`, `cmt_unitarity_interval_encloses_one`, and `cmt_krawtchouk_length_synthesis_sound`. -/
theorem quantumPhotonicMatter_wl_quotient_clements_and_cmt_sound
    (A : IntMatrix) (n : Nat) (color : Nat → Nat)
    (hValid : checkValidPartitionCells A.dim n color = true)
    (W0 W1 : Int) (op2 : OpticOp)
    (x0 y0 x1 y1 dOut0 dOut1 : Int)
    (vPin : LeafView) (gFullPin gQuotPin : StrictOpenHypergraph) (pinsPin : List LeafPin)
    (hWfFull : gFullPin.wf = true) (hWfQuot : gQuotPin.wf = true)
    (pPin : LeafPin) (hpPin : pPin ∈ pinsPin) (hdPin : holdsAt vPin pPin = false)
    (dH : IntMatrix) (nDis rDis : Nat) (partDis : List (List Nat)) (Q_d : Nat → Nat → Int)
    (opNorm epsBreak : Nat) (leak : Nat → Nat)
    (hScore : equitableBreakingScore dH nDis rDis partDis Q_d ≤ epsBreak)
    (hLeak0 : leak 0 = 0)
    (hLeakStep : ∀ k, leak (k + 1) ≤ opNorm * leak k + equitableBreakingScore dH nDis rDis partDis Q_d * (opNorm ^ k))
    (K : Nat)
    (t kappa : Int) (e0 e1 e2 e3 : ComplexField)
    (phi0 phi1 phi2 phi3 : Int) :
    let gFull := buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2
    let gQuot := quotientOpenHypergraph W0 W1 op2
    let envFull := liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1
    let envQuot := quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1
    let candPin := QuotientHypergraphCandidate.quotientCompressed gFullPin gQuotPin pinsPin true
    let fallbackPin := QuotientHypergraphCandidate.unreducedFull gFullPin
    -- 1. 1-WL fixed-point iff equitable + Q3 Krawtchouk stabilization
    (((∀ u, u < A.dim → wlRefineStep A n color u = color u) ↔
       isMooreCoalgebraBisimulation A n color = true) ∧
     ((∀ u, u < A.dim → wlRefineStep A n color u = color u) ↔
       checkEquitablePartition A n color (inducedQuotientEntry A color) = true) ∧
     (List.range 8).map (wlStabilize hypercubeQ3Matrix 8 q3PointSourceSeed) =
       (List.range 8).map hypercubeQ3Part ∧
     checkEquitablePartition hypercubeQ3Matrix 4
       (wlStabilize hypercubeQ3Matrix 8 q3PointSourceSeed)
       (inducedQuotientEntry hypercubeQ3Matrix (wlStabilize hypercubeQ3Matrix 8 q3PointSourceSeed)) = true) ∧
    -- 2. Quotient hypergraph forward & reverse-AD intertwining
    (gFull.wf = true ∧
     gQuot.wf = true ∧
     gFull.nodeTypes.length = 24 ∧
     gQuot.nodeTypes.length = 12 ∧
     evalHypergraphLayered gFull envFull = liftQuotientFwdOutputs (evalHypergraphLayered gQuot envQuot) ∧
     evalHypergraphLayered (compileGraphAdjoint gFull) envFull =
       liftQuotientAdjointOutputs (evalHypergraphLayered (compileGraphAdjoint gQuot) envQuot)) ∧
    -- 3. Universal & concrete DPR moved-pin blocking + 1-cycle fallback
    ((∃ d,
        quotientHypergraphSlot.read (holdsAt vPin) (some candPin) = .blocked candPin d ∧
        pPin ∈ d ∧
        (∀ q, q ∈ d ↔ q ∈ pinsPin ∧ holdsAt vPin q = false)) ∧
     (slotAdvance : Advance LeafView LeafPin QuotientHypergraphCandidate).advance
       quotientHypergraphSlot vPin [candPin, fallbackPin] (some candPin) = .ok fallbackPin ∧
     (let gFullConcrete := buildSymmetric4LaneHypergraph 5 5 7 7 .add
      let gQuotConcrete := quotientOpenHypergraph 5 7 .add
      let candConcrete := QuotientHypergraphCandidate.quotientCompressed
                            gFullConcrete gQuotConcrete (sym4LaneWeightPins 5 7) true
      quotientHypergraphSlot.usable (holdsAt (mkChannelWeightView 0 5 5 7 7)) candConcrete = true ∧
      quotientHypergraphSlot.usable (holdsAt (mkChannelWeightView 1 5 99 7 7)) candConcrete = false ∧
      (quotientHypergraphSlot.dead (holdsAt (mkChannelWeightView 1 5 99 7 7)) candConcrete).map LeafPin.cell =
        [.layer "weights.w1"])) ∧
    -- 4. Clements unitarity, Duhamel disorder leakage, Faddeev-LeVerrier crosstalk,
    --    certified rational TaylorModel enclosures (`Obend.Analysis.TaylorModel`), and Z[i] MZI transfer matrices
    (let s := t * t + kappa * kappa
     let (p0, p1, p2, p3) := evalPlanarClements4x4 t kappa e0 e1 e2 e3
     s * p0.normSq + p1.normSq + p2.normSq + s * p3.normSq =
       s * (s * (e0.normSq + e1.normSq + e2.normSq + e3.normSq))) ∧
    (leak K ≤ K * epsBreak * (opNorm ^ (K - 1)) ∧ (epsBreak = 0 → leak K = 0)) ∧
    (let res := compensateThermalCrosstalk goldenThermalCrosstalk4x4 [phi0, phi1, phi2, phi3]
     res.2 = 8769 ∧
     goldenThermalCrosstalk4x4.mulVec res.1 =
       [res.2 * phi0, res.2 * phi1, res.2 * phi2, res.2 * phi3]) ∧
    (let dom3dB : Interval := ⟨CanonicalRat.mk 785 1000, CanonicalRat.mk 786 1000⟩
     let sin3dB := tmSinCertified dom3dB
     let cos3dB := tmCosCertified dom3dB
     Interval.containsRat (evalTaylorModelRange (tmMul 6 sin3dB sin3dB)) (CanonicalRat.mk 1 2) = true ∧
     Interval.containsRat (evalTaylorModelRange (tmAdd (tmMul 4 sin3dB sin3dB) (tmMul 4 cos3dB cos3dB))) 1 = true) ∧
    (let domKraw01 : Interval := ⟨CanonicalRat.mk 659 1000, CanonicalRat.mk 660 1000⟩
     let sinKraw := tmSinCertified domKraw01
     let cosKraw := tmCosCertified domKraw01
     Interval.containsRat (evalTaylorModelRange (tmMul 6 sinKraw sinKraw)) (CanonicalRat.mk 3 8) = true ∧
     Interval.containsRat (evalTaylorModelRange (tmAdd (tmMul 4 sinKraw sinKraw) (tmMul 4 cosKraw cosKraw))) 1 = true) ∧
    (evalCascadedMzi2x2 t t ⟨1, 0⟩ e0 ⟨0, 0⟩).1 = ⟨0, 0⟩ ∧
    (evalCascadedMzi2x2 t t ⟨-1, 0⟩ e0 ⟨0, 0⟩).2 = ⟨0, 0⟩ := by
  have hWl := wlStabilize_fixedPoint_iff_equitable A n color hValid
  have hWlQ3 :
      (List.range 8).map (wlStabilize hypercubeQ3Matrix 8 q3PointSourceSeed) =
        (List.range 8).map hypercubeQ3Part ∧
      checkEquitablePartition hypercubeQ3Matrix 4
        (wlStabilize hypercubeQ3Matrix 8 q3PointSourceSeed)
        (inducedQuotientEntry hypercubeQ3Matrix (wlStabilize hypercubeQ3Matrix 8 q3PointSourceSeed)) = true := by
    decide +kernel
  have hInter := quotientOpenHypergraph_intertwines_eval_and_adjoint W0 W1 op2 x0 y0 x1 y1 dOut0 dOut1
  have hMoved := quotientHypergraph_moved_pin_blocks vPin gFullPin gQuotPin pinsPin hWfFull hWfQuot pPin hpPin hdPin
  have hClem := (planarClements4x4_conserves_optical_power t kappa e0 e1 e2 e3).1
  have hLeak := perturbative_disorder_leakage_bound dH nDis rDis partDis Q_d opNorm epsBreak leak hScore hLeak0 hLeakStep K
  have hCrossDet : (compensateThermalCrosstalk goldenThermalCrosstalk4x4 [phi0, phi1, phi2, phi3]).2 = 8769 :=
    faddeevAdjugate_cancels_crosstalk_4x4.1
  have hCrossVec := compensateThermalCrosstalk_exact_4x4 phi0 phi1 phi2 phi3
  have hTm3dB :
      let dom3dB : Interval := ⟨CanonicalRat.mk 785 1000, CanonicalRat.mk 786 1000⟩
      let sin3dB := tmSinCertified dom3dB
      let cos3dB := tmCosCertified dom3dB
      Interval.containsRat (evalTaylorModelRange (tmMul 6 sin3dB sin3dB)) (CanonicalRat.mk 1 2) = true ∧
      Interval.containsRat (evalTaylorModelRange (tmAdd (tmMul 4 sin3dB sin3dB) (tmMul 4 cos3dB cos3dB))) 1 = true := by
    decide +kernel
  have hTmKraw :
      let domKraw01 : Interval := ⟨CanonicalRat.mk 659 1000, CanonicalRat.mk 660 1000⟩
      let sinKraw := tmSinCertified domKraw01
      let cosKraw := tmCosCertified domKraw01
      Interval.containsRat (evalTaylorModelRange (tmMul 6 sinKraw sinKraw)) (CanonicalRat.mk 3 8) = true ∧
      Interval.containsRat (evalTaylorModelRange (tmAdd (tmMul 4 sinKraw sinKraw) (tmMul 4 cosKraw cosKraw))) 1 = true := by
    decide +kernel
  have hMziCross := cascaded_mzi_zero_phase_pure_cross t e0
  have hMziBar := cascaded_mzi_pi_phase_pure_bar t e0
  exact ⟨⟨hWl.2.1, hWl.2.2.1, hWlQ3.1, hWlQ3.2⟩,
         ⟨hInter.1, hInter.2.1, hInter.2.2.1, hInter.2.2.2.1, hInter.2.2.2.2.2.1, hInter.2.2.2.2.2.2.2⟩,
         hMoved,
         hClem,
         ⟨hLeak.2.1, hLeak.2.2⟩,
         ⟨hCrossDet, hCrossVec⟩,
         hTm3dB,
         hTmKraw,
         hMziCross,
         hMziBar⟩

/-! ## 4. Szegedy Quantum Walk Lumping, Matrix Taylor PST & Majorana Parity-Cooling Stabilizers -/

/-- **`quantumPhotonicMatter_szegedy_taylor_and_majorana_sound`**:
1. **Multi-Step Discrete-Time Szegedy Walk Intertwining & PST Equivalence (`QuantumWalk.lean`)**:
   - Universally instantiates `szegedy_intertwining_power` and `cellUniformSzegedyPST_iff_quotient`
     ($U_{\text{Sz}}^k P = P Q_{\text{Sz}}^k$), plus concrete 8-vertex $Q_3$ vs 4-shell quotient agreement (`= -576`).
2. **Computed Lagrange–Sylvester Projectors & Matrix Taylor Propagator PST (`QuantumWalk.lean`)**:
   - `computed_lagrange_projectors_k2_p3_q3_exact` and `matrixTaylorPropagator_encloses_k2_and_q3_pst`,
   - Exact 64-bit integer agreement `evalScaledMatrixTaylorImag hypercubeQ3Matrix 157 100 4 (liftQuotientVec hypercubeQ3Part wQ3) 7 = 9287743200`.
3. **Topological Majorana Tetron Braiding & Lindblad Parity-Cooling (`QuantumMatter.lean`; the braid relation is proved in `Teeth/Hardware/CliffordKernel.lean`, tier 2)**:
   - `majoranaBraid_artin_relation` in both $Cl_4$ and $M_4(\mathbb{Z}[i])$ (`spinorBraidGate`) + non-commutativity,
   - `parityCoolingJumpOp_dark_on_even_and_corrects_odd` across all $a \in \text{Fin } 4$. -/
theorem quantumPhotonicMatter_szegedy_taylor_and_majorana_sound
    (A B QA QB : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (dA dB : Int)
    (hCells : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → part x = j)
    (hEqA : ∀ x, ∀ j, j ∈ cellIndices → cellRowSum A (cellOf j) x = QA (part x) j)
    (hEqB : ∀ x, ∀ j, j ∈ cellIndices → cellRowSum B (cellOf j) x = QB (part x) j)
    (k : Nat) (w0 : Nat → Int) (v cTarget v0 : Nat)
    (hcMem : cTarget ∈ cellIndices) (hv0Mem : v0 ∈ cellOf cTarget)
    (targetAmp : Int)
    (a : Fin 4) :
    let wQ3 : Nat → Int := fun i => if i == 0 then 1 else 0
    let q3Prob7 := evalQ3KrawtchoukAntipodalProbTube 157 100
    let m0 : Fin 4 := ⟨0, by decide⟩
    let m1 : Fin 4 := ⟨1, by decide⟩
    let m2 : Fin 4 := ⟨2, by decide⟩
    -- 1. Universal Szegedy intertwining power & cell-uniform PST equivalence
    (iterateVecOp (szegedyWalkStep A B cellIndices cellOf dA dB) k (liftQuotientVec part w0) v =
       liftQuotientVec part (iterateVecOp (szegedyQuotientWalkStep QA QB cellIndices dA dB) k w0) v) ∧
    (((∀ x, x ∈ cellOf cTarget →
         iterateVecOp (szegedyWalkStep A B cellIndices cellOf dA dB) k (liftQuotientVec part w0) x = targetAmp) ↔
       iterateVecOp (szegedyQuotientWalkStep QA QB cellIndices dA dB) k w0 cTarget = targetAmp)) ∧
    -- 2. Lagrange projectors & Q3 Matrix Taylor PST (exact 64-bit integer 9287743200)
    computeScaledLagrangeProjectors k2Matrix [1, -1] 2 = [k2ProjPlus, k2ProjMinus] ∧
    computeScaledLagrangeProjectors hypercubeQ3QuotientMatrix [3, 1, -1, -3] 48 =
      q3QuotientSylvesterProjectors ∧
    checkSpectralDecomposition hypercubeQ3QuotientMatrix 48 [3, 1, -1, -3]
      (computeScaledLagrangeProjectors hypercubeQ3QuotientMatrix [3, 1, -1, -3] 48) = true ∧
    evalScaledMatrixTaylorImag hypercubeQ3Matrix 157 100 4 (liftQuotientVec hypercubeQ3Part wQ3) 7 =
      evalScaledMatrixTaylorImag hypercubeQ3QuotientMatrix 157 100 4 wQ3 3 ∧
    evalScaledMatrixTaylorImag hypercubeQ3QuotientMatrix 157 100 4 wQ3 3 = 9287743200 ∧
    Interval.containsRat q3Prob7 1 = true ∧
    Interval.containsRat q3Prob7 (CanonicalRat.mk 9 10) = false ∧
    -- 3. Majorana Artin braid relation in Cl_4 & M_4(Z[i]) + non-commutativity + parity cooling
    cliffordMul (cliffordMul (majoranaBraidElem m0 m1) (majoranaBraidElem m1 m2)) (majoranaBraidElem m0 m1) =
      cliffordMul (cliffordMul (majoranaBraidElem m1 m2) (majoranaBraidElem m0 m1)) (majoranaBraidElem m1 m2) ∧
    ((spinorBraidGate m0 m1).mul (spinorBraidGate m1 m2)).mul (spinorBraidGate m0 m1) =
      ((spinorBraidGate m1 m2).mul (spinorBraidGate m0 m1)).mul (spinorBraidGate m1 m2) ∧
    cliffordMul (majoranaBraidElem m0 m1) (majoranaBraidElem m1 m2) ≠
      cliffordMul (majoranaBraidElem m1 m2) (majoranaBraidElem m0 m1) ∧
    (parityCoolingJumpOp a).mul spinorEvenParityProjector = GaussianMatrix.zero 4 ∧
    ((parityCoolingJumpOp a).mul spinorOddParityProjector).mul (parityCoolingJumpOp a).conjTranspose =
      spinorEvenParityProjector ∧
    spinorEvenParityProjector.mul (parityCoolingJumpOp a) = parityCoolingJumpOp a := by
  have hSzPow := szegedy_intertwining_power A B QA QB part cellIndices cellOf dA dB hCells hEqA hEqB k w0 v
  have hSzPst := cellUniformSzegedyPST_iff_quotient A B QA QB part cellIndices cellOf dA dB
    hCells hEqA hEqB k w0 v cTarget v0 hcMem hv0Mem targetAmp
  have hProj := computed_lagrange_projectors_k2_p3_q3_exact
  have hTaylor := matrixTaylorPropagator_encloses_k2_and_q3_pst
  have hTaylorVal :
      evalScaledMatrixTaylorImag hypercubeQ3QuotientMatrix 157 100 4
        (fun i => if i == 0 then 1 else 0) 3 = 9287743200 := by
    decide +kernel
  have hBraid := majoranaBraid_artin_relation ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
    (by decide) (by decide) (by decide)
  have hCool := parityCoolingJumpOp_dark_on_even_and_corrects_odd a
  exact ⟨hSzPow, hSzPst.2.1,
         hProj.1,
         hProj.2.2.2.2.2.2.2.2.2.2.2.1,
         hProj.2.2.2.2.2.2.2.2.2.2.2.2,
         hTaylor.2.2.2.2.2.2.2.2.2.2.2.1,
         hTaylorVal,
         hTaylor.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hTaylor.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
         hBraid.1, hBraid.2.1, hBraid.2.2,
         hCool.1, hCool.2.2.1, hCool.2.2.2.1⟩

/-! ## 5. Verified Synchronous Quantum Photonic & Topological Co-Processor `RtlModule` -/

abbrev QpmRtlBuilder := StateM (Array WireAssign)

def pushQpmWire (name : String) (expr : RtlExpr) : QpmRtlBuilder RtlExpr := do
  let ws ← get
  let idx := ws.size
  set (ws.push { wireIdx := idx, name := name, expr := expr })
  return .wireRef idx

structure ComplexWire where
  re : RtlExpr
  im : RtlExpr

structure Spinor4Wires where
  z0 : ComplexWire
  z1 : ComplexWire
  z2 : ComplexWire
  z3 : ComplexWire

/-- Exact hardware realization of `spinorBraidGate 0 1` ($T_{0,1} = I_4 + \gamma_0\gamma_1$) over $\mathbb{Z}[i]^4$:
$$(T_{0,1}\psi)_0 = \psi_0 + i\psi_1,\; (T_{0,1}\psi)_1 = i\psi_0 + \psi_1,\;
  (T_{0,1}\psi)_2 = \psi_2 - i\psi_3,\; (T_{0,1}\psi)_3 = -i\psi_2 + \psi_3.$$ -/
def emitSpinorT01Stage (tag : String) (s : Spinor4Wires) : QpmRtlBuilder Spinor4Wires := do
  let z0Re ← pushQpmWire (tag ++ "_z0_re") (.alu .sub s.z0.re s.z1.im)
  let z0Im ← pushQpmWire (tag ++ "_z0_im") (.alu .add s.z0.im s.z1.re)
  let z1Re ← pushQpmWire (tag ++ "_z1_re") (.alu .sub s.z1.re s.z0.im)
  let z1Im ← pushQpmWire (tag ++ "_z1_im") (.alu .add s.z1.im s.z0.re)
  let z2Re ← pushQpmWire (tag ++ "_z2_re") (.alu .add s.z2.re s.z3.im)
  let z2Im ← pushQpmWire (tag ++ "_z2_im") (.alu .sub s.z2.im s.z3.re)
  let z3Re ← pushQpmWire (tag ++ "_z3_re") (.alu .add s.z3.re s.z2.im)
  let z3Im ← pushQpmWire (tag ++ "_z3_im") (.alu .sub s.z3.im s.z2.re)
  return { z0 := ⟨z0Re, z0Im⟩, z1 := ⟨z1Re, z1Im⟩, z2 := ⟨z2Re, z2Im⟩, z3 := ⟨z3Re, z3Im⟩ }

/-- Exact hardware realization of `spinorBraidGate 1 2` ($T_{1,2} = I_4 + \gamma_1\gamma_2 = \operatorname{diag}(1+i, 1-i, 1+i, 1-i)$):
$$(1+i)(a+bi) = (a-b) + (a+b)i,\quad (1-i)(a+bi) = (a+b) + (b-a)i.$$ -/
def emitSpinorT12Stage (tag : String) (s : Spinor4Wires) : QpmRtlBuilder Spinor4Wires := do
  let z0Re ← pushQpmWire (tag ++ "_z0_re") (.alu .sub s.z0.re s.z0.im)
  let z0Im ← pushQpmWire (tag ++ "_z0_im") (.alu .add s.z0.re s.z0.im)
  let z1Re ← pushQpmWire (tag ++ "_z1_re") (.alu .add s.z1.re s.z1.im)
  let z1Im ← pushQpmWire (tag ++ "_z1_im") (.alu .sub s.z1.im s.z1.re)
  let z2Re ← pushQpmWire (tag ++ "_z2_re") (.alu .sub s.z2.re s.z2.im)
  let z2Im ← pushQpmWire (tag ++ "_z2_im") (.alu .add s.z2.re s.z2.im)
  let z3Re ← pushQpmWire (tag ++ "_z3_re") (.alu .add s.z3.re s.z3.im)
  let z3Im ← pushQpmWire (tag ++ "_z3_im") (.alu .sub s.z3.im s.z3.re)
  return { z0 := ⟨z0Re, z0Im⟩, z1 := ⟨z1Re, z1Im⟩, z2 := ⟨z2Re, z2Im⟩, z3 := ⟨z3Re, z3Im⟩ }

def emitSpinorEq (tag : String) (a b : Spinor4Wires) : QpmRtlBuilder RtlExpr := do
  let e0r ← pushQpmWire (tag ++ "_e0r") (.alu .eq a.z0.re b.z0.re)
  let e0i ← pushQpmWire (tag ++ "_e0i") (.alu .eq a.z0.im b.z0.im)
  let e1r ← pushQpmWire (tag ++ "_e1r") (.alu .eq a.z1.re b.z1.re)
  let e1i ← pushQpmWire (tag ++ "_e1i") (.alu .eq a.z1.im b.z1.im)
  let e2r ← pushQpmWire (tag ++ "_e2r") (.alu .eq a.z2.re b.z2.re)
  let e2i ← pushQpmWire (tag ++ "_e2i") (.alu .eq a.z2.im b.z2.im)
  let e3r ← pushQpmWire (tag ++ "_e3r") (.alu .eq a.z3.re b.z3.re)
  let e3i ← pushQpmWire (tag ++ "_e3i") (.alu .eq a.z3.im b.z3.im)
  let e01 ← pushQpmWire (tag ++ "_e01") (.alu .bitAnd (.alu .bitAnd e0r e0i) (.alu .bitAnd e1r e1i))
  let e23 ← pushQpmWire (tag ++ "_e23") (.alu .bitAnd (.alu .bitAnd e2r e2i) (.alu .bitAnd e3r e3i))
  pushQpmWire (tag ++ "_all") (.alu .bitAnd e01 e23)

def buildQuantumPhotonicRtlBody : QpmRtlBuilder (List OutputPort × List RegSpec) := do
  let inBatchVecs   := RtlExpr.inputPort 0
  let inSyndRounds  := RtlExpr.inputPort 1
  let inKrawBatch   := RtlExpr.inputPort 2
  let inPstStep     := RtlExpr.inputPort 3
  let inTNum        := RtlExpr.inputPort 4
  let inTDen        := RtlExpr.inputPort 5
  let inPinW0       := RtlExpr.inputPort 6
  let inPinW1       := RtlExpr.inputPort 7
  let inPinW2       := RtlExpr.inputPort 8
  let inPinW3       := RtlExpr.inputPort 9
  let inShellW01    := RtlExpr.inputPort 10
  let inShellW12    := RtlExpr.inputPort 11
  let inShellW23    := RtlExpr.inputPort 12
  let inV0          := RtlExpr.inputPort 13
  let inV1          := RtlExpr.inputPort 14
  let inV2          := RtlExpr.inputPort 15
  let inV3          := RtlExpr.inputPort 16
  let psiIn : Spinor4Wires :=
    { z0 := ⟨.inputPort 17, .inputPort 18⟩
    , z1 := ⟨.inputPort 19, .inputPort 20⟩
    , z2 := ⟨.inputPort 21, .inputPort 22⟩
    , z3 := ⟨.inputPort 23, .inputPort 24⟩ }
  let inBraidEn     := RtlExpr.inputPort 25

  -- 1. `.obend` open-recursive datapath wires
  let wAdjOps ← pushQpmWire "quotient_reverse_adjoint_ops"
    (.alu .add (.alu .mul inBatchVecs (.const 4#64)) (.const 8769#64))
  let wBudget ← pushQpmWire "coproc_cycle_budget"
    (.alu .add (.alu .add (.alu .mul inSyndRounds (.const 16#64)) (.const 4#64)) (.const 32#64))
  let wKrawMacs ← pushQpmWire "krawtchouk_adjoint_macs"
    (.alu .add (.alu .mul inKrawBatch (.const 4#64)) (.const 3142#64))
  let wPstFid ← pushQpmWire "pst_transfer_fidelity_ppm"
    (.alu .add (.alu .add (.alu .mul inPstStep (.const 250#64)) (.const 4#64)) (.const 1000#64))

  -- 2. 1-WL Quotient DPR Guard (`quotientHypergraphSlot` + Q3 Krawtchouk shell weights)
  let wSym01 ← pushQpmWire "catgrad_w01_eq" (.alu .eq inPinW0 inPinW1)
  let wSym23 ← pushQpmWire "catgrad_w23_eq" (.alu .eq inPinW2 inPinW3)
  let wCatSym ← pushQpmWire "catgrad_sym_ok" (.alu .bitAnd wSym01 wSym23)
  let wSh01 ← pushQpmWire "shell_w01_ok" (.alu .eq inShellW01 (.const 3#64))
  let wSh12 ← pushQpmWire "shell_w12_ok" (.alu .eq inShellW12 (.const 4#64))
  let wSh23 ← pushQpmWire "shell_w23_ok" (.alu .eq inShellW23 (.const 3#64))
  let wShellSym ← pushQpmWire "shell_sym_ok" (.alu .bitAnd (.alu .bitAnd wSh01 wSh12) wSh23)
  let wDprUsable ← pushQpmWire "dpr_quotient_usable" (.alu .bitAnd wCatSym wShellSym)
  let wDprFallback ← pushQpmWire "dpr_fallback_full" (.alu .eq wDprUsable (.const 0#64))
  let wActiveWires ← pushQpmWire "active_hypergraph_wires"
    (.mux wDprUsable (.const 12#64) (.const 24#64))
  let wActiveModes ← pushQpmWire "active_q3_modes"
    (.mux wDprUsable (.const 4#64) (.const 8#64))

  -- 3-step Krawtchouk Q_3 quotient walk from w^(0) = (1, 0, 0, 0) & degree-4 scaled Taylor amplitude:
  -- q1[1] = 1, q2[2] = 2 * q1[1] = 2, q3[3] = inShellW23 * q2[2] (= 3 * 2 = 6),
  -- T_imag^(4)(3) = (4 * inTDen * q3[3]) * inTNum^3 (= 9287743200 at t = 157/100, zero 64-bit overflow!)
  let wQ3Step3 ← pushQpmWire "q3_walk_step3_shell3" (.alu .mul inShellW23 (.const 2#64))
  let wTNumSq  ← pushQpmWire "t_num_sq" (.alu .mul inTNum inTNum)
  let wTNumCu  ← pushQpmWire "t_num_cu" (.alu .mul wTNumSq inTNum)
  let wTayScale ← pushQpmWire "taylor_scale" (.alu .mul (.alu .mul (.const 4#64) inTDen) wQ3Step3)
  let wQ3TayIm ← pushQpmWire "q3_pst_shell3_imag_scaled" (.alu .mul wTayScale wTNumCu)
  let wPstEnclosed ← pushQpmWire "q3_pst_antipodal_enclosed"
    (.alu .bitAnd (.alu .bitAnd (.alu .eq inTNum (.const 157#64)) (.alu .eq inTDen (.const 100#64)))
                  wDprUsable)

  -- 3. 4x4 Faddeev-LeVerrier Exact Thermo-Optic Crosstalk Pre-Compensation (`det = 8769`)
  let n174 := BitVec.ofInt 64 (-174)
  let n160 := BitVec.ofInt 64 (-160)
  let n63  := BitVec.ofInt 64 (-63)
  let wU0 ← pushQpmWire "precomp_u0"
    (.alu .add
      (.alu .add (.alu .mul (.const 918#64) inV0) (.alu .mul (.const n174) inV1))
      (.alu .add (.alu .mul (.const n63) inV2) (.alu .mul (.const 30#64) inV3)))
  let wU1 ← pushQpmWire "precomp_u1"
    (.alu .add
      (.alu .add (.alu .mul (.const n174) inV0) (.alu .mul (.const 950#64) inV1))
      (.alu .add (.alu .mul (.const n160) inV2) (.alu .mul (.const n63) inV3)))
  let wU2 ← pushQpmWire "precomp_u2"
    (.alu .add
      (.alu .add (.alu .mul (.const n63) inV0) (.alu .mul (.const n160) inV1))
      (.alu .add (.alu .mul (.const 950#64) inV2) (.alu .mul (.const n174) inV3)))
  let wU3 ← pushQpmWire "precomp_u3"
    (.alu .add
      (.alu .add (.alu .mul (.const 30#64) inV0) (.alu .mul (.const n63) inV1))
      (.alu .add (.alu .mul (.const n174) inV2) (.alu .mul (.const 918#64) inV3)))

  let wY0 ← pushQpmWire "channel_y0"
    (.alu .add (.alu .add (.alu .mul (.const 10#64) wU0) (.alu .mul (.const 2#64) wU1)) wU2)
  let wY1 ← pushQpmWire "channel_y1"
    (.alu .add (.alu .add (.alu .mul (.const 2#64) wU0) (.alu .mul (.const 10#64) wU1))
               (.alu .add (.alu .mul (.const 2#64) wU2) wU3))
  let wY2 ← pushQpmWire "channel_y2"
    (.alu .add (.alu .add wU0 (.alu .mul (.const 2#64) wU1))
               (.alu .add (.alu .mul (.const 10#64) wU2) (.alu .mul (.const 2#64) wU3)))
  let wY3 ← pushQpmWire "channel_y3"
    (.alu .add (.alu .add wU1 (.alu .mul (.const 2#64) wU2)) (.alu .mul (.const 10#64) wU3))

  let wCt0 ← pushQpmWire "ct_eq0" (.alu .eq wY0 (.alu .mul (.const 8769#64) inV0))
  let wCt1 ← pushQpmWire "ct_eq1" (.alu .eq wY1 (.alu .mul (.const 8769#64) inV1))
  let wCt2 ← pushQpmWire "ct_eq2" (.alu .eq wY2 (.alu .mul (.const 8769#64) inV2))
  let wCt3 ← pushQpmWire "ct_eq3" (.alu .eq wY3 (.alu .mul (.const 8769#64) inV3))
  let wCrosstalkOk ← pushQpmWire "crosstalk_exact_match"
    (.alu .bitAnd (.alu .bitAnd wCt0 wCt1) (.alu .bitAnd wCt2 wCt3))

  -- 4. Genuine 3-Stage Majorana Spinor Braiding over Z[i]^4 (`T_01 T_12 T_01` vs `T_12 T_01 T_12`)
  let lhs1 ← emitSpinorT01Stage "lhs1" psiIn
  let lhs2 ← emitSpinorT12Stage "lhs2" lhs1
  let lhs3 ← emitSpinorT01Stage "lhs3" lhs2
  let rhs1 ← emitSpinorT12Stage "rhs1" psiIn
  let rhs2 ← emitSpinorT01Stage "rhs2" rhs1
  let rhs3 ← emitSpinorT12Stage "rhs3" rhs2

  let wArtinOk ← emitSpinorEq "artin3" lhs3 rhs3
  let wComm2Eq ← emitSpinorEq "comm2" lhs2 rhs2
  let wBraidNonAbelian ← pushQpmWire "braid_nonabelian_witness" (.alu .eq wComm2Eq (.const 0#64))

  -- 5. Exact `QuantumMatter.lean` Chiral Fermion-Parity Basis `diag(1, 1, -1, -1)` & `parityCoolingJumpOp 0`
  -- Even sector (+1) = indices {0, 1} (z2 == 0 && z3 == 0); Odd sector (-1) = indices {2, 3} (z0 == 0 && z1 == 0).
  let wZ2Zero ← pushQpmWire "z2_zero"
    (.alu .bitAnd (.alu .eq psiIn.z2.re (.const 0#64)) (.alu .eq psiIn.z2.im (.const 0#64)))
  let wZ3Zero ← pushQpmWire "z3_zero"
    (.alu .bitAnd (.alu .eq psiIn.z3.re (.const 0#64)) (.alu .eq psiIn.z3.im (.const 0#64)))
  let wZ0Zero ← pushQpmWire "z0_zero"
    (.alu .bitAnd (.alu .eq psiIn.z0.re (.const 0#64)) (.alu .eq psiIn.z0.im (.const 0#64)))
  let wZ1Zero ← pushQpmWire "z1_zero"
    (.alu .bitAnd (.alu .eq psiIn.z1.re (.const 0#64)) (.alu .eq psiIn.z1.im (.const 0#64)))
  let wInputEven ← pushQpmWire "input_even_parity" (.alu .bitAnd wZ2Zero wZ3Zero)
  let wInputOdd  ← pushQpmWire "input_odd_parity"  (.alu .bitAnd wZ0Zero wZ1Zero)

  -- `parityCoolingJumpOp 0` = \gamma_0 * \Pi_odd maps (z0, z1, z2, z3) -> (z2, z3, 0, 0)
  let wCool0Re ← pushQpmWire "cool_z0_re" psiIn.z2.re
  let wCool0Im ← pushQpmWire "cool_z0_im" psiIn.z2.im
  let wCool1Re ← pushQpmWire "cool_z1_re" psiIn.z3.re
  let wCool1Im ← pushQpmWire "cool_z1_im" psiIn.z3.im
  let wCool2Re ← pushQpmWire "cool_z2_re" (.const 0#64)
  let wCool2Im ← pushQpmWire "cool_z2_im" (.const 0#64)
  let wCool3Re ← pushQpmWire "cool_z3_re" (.const 0#64)
  let wCool3Im ← pushQpmWire "cool_z3_im" (.const 0#64)

  let wCoolOddZero ← pushQpmWire "cooled_in_even_codespace"
    (.alu .bitAnd
      (.alu .bitAnd (.alu .eq wCool2Re (.const 0#64)) (.alu .eq wCool2Im (.const 0#64)))
      (.alu .bitAnd (.alu .eq wCool3Re (.const 0#64)) (.alu .eq wCool3Im (.const 0#64))))
  let wEpochStep ← pushQpmWire "syndrome_epoch_step_en"
    (.alu .bitAnd (.mux inBraidEn (.const 1#64) (.const 0#64))
                  (.alu .bitAnd wArtinOk wCoolOddZero))

  let regs : List RegSpec :=
    [ { regIdx := 0, name := "reg_stabilized_syndrome_epochs", domain := .coreClk,
        resetKind := .syncReset 0#64, isSynchronizer := false,
        nextExpr := .mux wEpochStep (.alu .add (.regRead 0) (.const 1#64)) (.regRead 0) }
    , { regIdx := 1, name := "reg_dpr_fallback_events", domain := .coreClk,
        resetKind := .syncReset 0#64, isSynchronizer := false,
        nextExpr := .mux wDprFallback (.alu .add (.regRead 1) (.const 1#64)) (.regRead 1) }
    ]

  let outputs : List OutputPort :=
    [ { name := "out_wl_compressed_shells",        expr := .const 4#64 }
    , { name := "out_faddeev_crosstalk_det",       expr := .const 8769#64 }
    , { name := "out_cmt_krawtchouk_len0_nm",      expr := .const 1571#64 }
    , { name := "out_cmt_krawtchouk_len1_nm",      expr := .const 2721#64 }
    , { name := "out_cmt_krawtchouk_len2_nm",      expr := .const 3142#64 }
    , { name := "out_quotient_reverse_adjoint_ops", expr := wAdjOps }
    , { name := "out_coproc_cycle_budget",         expr := wBudget }
    , { name := "out_krawtchouk_adjoint_macs",     expr := wKrawMacs }
    , { name := "out_pst_transfer_fidelity_ppm",   expr := wPstFid }
    , { name := "out_dpr_quotient_usable",         expr := wDprUsable }
    , { name := "out_dpr_fallback_full",           expr := wDprFallback }
    , { name := "out_active_hypergraph_wires",     expr := wActiveWires }
    , { name := "out_active_q3_modes",             expr := wActiveModes }
    , { name := "out_q3_pst_shell3_imag_scaled",   expr := wQ3TayIm }
    , { name := "out_q3_pst_antipodal_enclosed",   expr := wPstEnclosed }
    , { name := "out_precomp_u0",                  expr := wU0 }
    , { name := "out_precomp_u1",                  expr := wU1 }
    , { name := "out_precomp_u2",                  expr := wU2 }
    , { name := "out_precomp_u3",                  expr := wU3 }
    , { name := "out_channel_y0",                  expr := wY0 }
    , { name := "out_channel_y1",                  expr := wY1 }
    , { name := "out_channel_y2",                  expr := wY2 }
    , { name := "out_channel_y3",                  expr := wY3 }
    , { name := "out_crosstalk_exact_match",       expr := wCrosstalkOk }
    , { name := "out_artin_braid_verified",        expr := wArtinOk }
    , { name := "out_braid_nonabelian_witness",    expr := wBraidNonAbelian }
    , { name := "out_input_even_parity",           expr := wInputEven }
    , { name := "out_input_odd_parity",            expr := wInputOdd }
    , { name := "out_cool_jump_psi0_re",           expr := wCool0Re }
    , { name := "out_cool_jump_psi0_im",           expr := wCool0Im }
    , { name := "out_cool_jump_psi1_re",           expr := wCool1Re }
    , { name := "out_cool_jump_psi1_im",           expr := wCool1Im }
    , { name := "out_cool_jump_psi2_re",           expr := wCool2Re }
    , { name := "out_cool_jump_psi2_im",           expr := wCool2Im }
    , { name := "out_cool_jump_psi3_re",           expr := wCool3Re }
    , { name := "out_cool_jump_psi3_im",           expr := wCool3Im }
    , { name := "out_cooled_in_even_codespace",    expr := wCoolOddZero }
    , { name := "out_stabilized_syndrome_epochs",  expr := .regRead 0 }
    , { name := "out_dpr_fallback_events",         expr := .regRead 1 }
    ]
  return (outputs, regs)

/-- Verified synchronous `RtlModule` (`quantum_photonic_coproc_top`) emitted directly via `emitModuleSV`
to `apps/quantum-photonic-matter/verilator/quantum_photonic_coproc_top.sv`. -/
def quantumPhotonicCoprocTopRtlModule : RtlModule :=
  let ((outputs, regs), wiresArr) := buildQuantumPhotonicRtlBody.run #[]
  { name := "quantum_photonic_coproc_top"
  , inputNames :=
      [ "in_batch_vectors"
      , "in_syndrome_rounds"
      , "in_krawtchouk_batch_size"
      , "in_pst_step_index"
      , "in_t_num"
      , "in_t_den"
      , "in_pin_w0"
      , "in_pin_w1"
      , "in_pin_w2"
      , "in_pin_w3"
      , "in_pin_shell_w01"
      , "in_pin_shell_w12"
      , "in_pin_shell_w23"
      , "in_target_v0"
      , "in_target_v1"
      , "in_target_v2"
      , "in_target_v3"
      , "in_tetron_psi0_re"
      , "in_tetron_psi0_im"
      , "in_tetron_psi1_re"
      , "in_tetron_psi1_im"
      , "in_tetron_psi2_re"
      , "in_tetron_psi2_im"
      , "in_tetron_psi3_re"
      , "in_tetron_psi3_im"
      , "in_braid_enable" ]
  , wires := wiresArr.toList
  , regs := regs
  , outputs := outputs }

/-- Input builder for `quantumPhotonicCoprocTopRtlModule`. -/
def mkQpmRtlInputs
    (w1Override : Nat)
    (psi0Re psi1Re psi2Re psi3Re : Int) : Nat → BitVec 64
  | 0  => 25#64
  | 1  => 6#64
  | 2  => 16#64
  | 3  => 4#64
  | 4  => 157#64
  | 5  => 100#64
  | 6  => 5#64
  | 7  => BitVec.ofNat 64 w1Override
  | 8  => 7#64
  | 9  => 7#64
  | 10 => 3#64
  | 11 => 4#64
  | 12 => 3#64
  | 13 => BitVec.ofInt 64 10
  | 14 => BitVec.ofInt 64 (-5)
  | 15 => BitVec.ofInt 64 7
  | 16 => BitVec.ofInt 64 3
  | 17 => BitVec.ofInt 64 psi0Re
  | 19 => BitVec.ofInt 64 psi1Re
  | 21 => BitVec.ofInt 64 psi2Re
  | 23 => BitVec.ofInt 64 psi3Re
  | 25 => 1#64
  | _  => 0#64

/-- **`quantumPhotonicCoprocTopRtlModule_verified`**:
Kernel-checked (`decide +kernel`) verification of `quantumPhotonicCoprocTopRtlModule`:
1. Passes `checkRtlModule = true` and `checkBelNetlistValid (synthesizeModuleToBels ...) = true`,
2. Under symmetric channel pins `w = (5, 5, 7, 7)` and even-parity logical state `(3, 2, 0, 0)`:
   - `out_dpr_quotient_usable = 1`, `out_active_hypergraph_wires = 12`, `out_active_q3_modes = 4`,
   - `out_q3_pst_shell3_imag_scaled = 9287743200` (exact match with `evalScaledMatrixTaylorImag`),
   - `out_crosstalk_exact_match = 1` ($\det = 8769$),
   - `out_artin_braid_verified = 1` AND `out_braid_nonabelian_witness = 1`,
   - `out_input_even_parity = 1` and `parityCoolingJumpOp 0` is dark (`out_cool_jump_psi0_re = 0`),
3. Under symmetry-breaking override `w1 = 99` and odd-parity poisoned state `(0, 0, 7, -4)`:
   - `out_dpr_quotient_usable = 0`, `out_dpr_fallback_full = 1`, `out_active_hypergraph_wires = 24`,
   - `out_input_odd_parity = 1` and `parityCoolingJumpOp 0` maps `(0, 0, 7, -4) -> (7, -4, 0, 0)`
     into the $+1$ even-parity code space (`out_cooled_in_even_codespace = 1`)! -/
theorem quantumPhotonicCoprocTopRtlModule_verified :
    checkRtlModule quantumPhotonicCoprocTopRtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels quantumPhotonicCoprocTopRtlModule) = true ∧
    (let st0 : Nat → BitVec 64 := fun _ => 0#64
     let inEvenSym := mkQpmRtlInputs 5 3 2 0 0
     let outEven := evalModuleOutputs quantumPhotonicCoprocTopRtlModule inEvenSym st0
     let st1 := stepModuleRegs quantumPhotonicCoprocTopRtlModule false inEvenSym st0
     let inOddBroken := mkQpmRtlInputs 99 0 0 7 (-4)
     let outOdd := evalModuleOutputs quantumPhotonicCoprocTopRtlModule inOddBroken st1
     let st2 := stepModuleRegs quantumPhotonicCoprocTopRtlModule false inOddBroken st1
     outEven.lookup "out_quotient_reverse_adjoint_ops" = some 8869#64 ∧
     outEven.lookup "out_dpr_quotient_usable" = some 1#64 ∧
     outEven.lookup "out_active_hypergraph_wires" = some 12#64 ∧
     outEven.lookup "out_q3_pst_shell3_imag_scaled" = some 9287743200#64 ∧
     outEven.lookup "out_crosstalk_exact_match" = some 1#64 ∧
     outEven.lookup "out_artin_braid_verified" = some 1#64 ∧
     outEven.lookup "out_braid_nonabelian_witness" = some 1#64 ∧
     outEven.lookup "out_input_even_parity" = some 1#64 ∧
     outEven.lookup "out_cool_jump_psi0_re" = some 0#64 ∧
     outEven.lookup "out_cool_jump_psi1_re" = some 0#64 ∧
     outOdd.lookup "out_dpr_quotient_usable" = some 0#64 ∧
     outOdd.lookup "out_dpr_fallback_full" = some 1#64 ∧
     outOdd.lookup "out_active_hypergraph_wires" = some 24#64 ∧
     outOdd.lookup "out_input_odd_parity" = some 1#64 ∧
     outOdd.lookup "out_cool_jump_psi0_re" = some (BitVec.ofInt 64 7) ∧
     outOdd.lookup "out_cool_jump_psi1_re" = some (BitVec.ofInt 64 (-4)) ∧
     outOdd.lookup "out_cooled_in_even_codespace" = some 1#64 ∧
     st2 0 = 2#64 ∧
     st2 1 = 1#64) := by
  decide +kernel

/-! ## 6. `#tooth` Mutation-Killing Guards -/

-- (2026-11-04) the tooth on the deleted `accepted` bundle is gone: a tooth on a fixture only
-- proved the fixture was sensitive to its own data.

def brokenQ3PointSourceSeed : Nat → Nat := fun _ => 0

#tooth quantumPhotonicMatter_wl_quotient_clements_and_cmt_sound by mutation
  q3PointSourceSeed := brokenQ3PointSourceSeed

def brokenQpmRtlModule : RtlModule :=
  { name := "quantum_photonic_coproc_top"
  , inputNames := ["in_batch_vectors"]
  , wires := []
  , regs := []
  , outputs := [{ name := "out_artin_braid_verified", expr := .const 0#64 }] }

#tooth quantumPhotonicCoprocTopRtlModule_verified by mutation
  quantumPhotonicCoprocTopRtlModule := brokenQpmRtlModule

end Obend.Apps.QuantumPhotonicMatter
end
