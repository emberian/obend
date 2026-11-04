/-
# `Obend/Teeth/Lower/Fixtures.lean` — the closed fixtures that left tier 1 (2026-11-04)

Each `example` here was a `theorem` in a tier-1 module of `Obend/Lower/`: a closed statement, proved by
`decide +kernel` on literal data, that nothing cites. The triage of 2026-11-04 (`Obend/Census.lean`,
`review/DECISIONS-20261031.md`) keeps them as what they are, end-to-end runs worth doing before a
push and not on every library build. Each carries the module it came from and why it is kept. This
file is tier 2: `lake build Teeth`; a plain file, so it sees every definition with its body.
-/

import Obend.Lower.Proofs.Hardware
import Obend.Lower.Proofs.SelfAccelerate
import Obend.Lower.Proofs.SiliconKernel
import Obend.Lower.SiliconElabFabric

set_option autoImplicit false

-- from Obend/Lower/Proofs/Hardware.lean:165: end-to-end run on a fixture (15 lines); worth a pre-push run, not every library build
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Equiv Obend.Leaf
open Obend.Lower.Inductive
open Obend.Hardware.HDL Obend.Hardware.Compiler
/-- **4-Stage Verified Chain (`lean_double_to_book_to_rtl`)**:
1. `doubleLExpr` applied to `21` reduces in `SSteps` to `42`;
2. `lowerT` applied to `21` evaluates in `Core4` to `.nat 42`;
3. `emit (leanComposition "double" (lowerT doubleLExpr))` halts on `21` with `.natural 42`;
4. `compileBookToRtl` compiles that exact `Book` to a valid `RtlModule` (`checkRtlModule = true`)
   whose hardware output at `arg = 21#64` is `[("out_double", 42#64)]`. -/
example :
    let C := leanComposition "double" (lowerT doubleLExpr)
    let B := emit C
    SSteps (.app doubleLExpr (.lit 21)) (.lit 42) ∧
    Evaluates (.app (lowerT doubleLExpr) (.nat 21)) (.nat 42) ∧
    Halts (.app (.get B.link "double") (.nat 21)) (.natural 42) ∧
    (match compileBookToRtl "lean_double_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 21#64) (fun _ => 0#64) == [("out_double", 42#64)])
     | none => false) = true := by
  refine ⟨doubleLExpr_runs_21, ?_, ?_, ?_⟩
  · simpa [lowerT] using lower_sound_nat doubleLExpr_runs_21
  · exact lean_to_book "double" doubleLExpr 21 42 (by decide +kernel) doubleLExpr_runs_21
  · decide +kernel
end Obend.Lower

-- from Obend/Lower/Proofs/Hardware.lean:228: a 8-line closed evaluation; worth a pre-push run
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Equiv Obend.Leaf
open Obend.Lower.Inductive
open Obend.Hardware.HDL Obend.Hardware.Compiler
/-- **Wrapping `compileBookToRtl` Diverges on `smallUnderflowLExpr` at `n = 2`**:
Wrapping `compileBookToRtl` produces `2#64 - 3#64 + 1#64 = 0#64 ≠ 1#64`! -/
example :
    let C := leanComposition "small" (lowerT smallUnderflowLExpr)
    let B := emit C
    (match compileBookToRtl "lean_small_wrap_rtl" B with
     | some m =>
       evalModuleOutputs m (fun _ => 2#64) (fun _ => 0#64) == [("out_small", 1#64)]
     | none => true) = false := by
  decide +kernel
end Obend.Lower

-- from Obend/Lower/Proofs/Hardware.lean:242: end-to-end run on a fixture (23 lines); worth a pre-push run, not every library build
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Equiv Obend.Leaf
open Obend.Lower.Inductive
open Obend.Hardware.HDL Obend.Hardware.Compiler
/-- **4-Stage Saturating Verified Chain (`lean_small_to_book_to_rtl`)**:
Under `compileBookToRtlSat`, `smallUnderflowLExpr` (`if n ≤ 2 then (n - 3) + 1 else n - 3`) agrees
across all 4 stages (`SSteps`, `Core4.Evaluates`, `Leaf.Book.Halts`, and `compileBookToRtlSat`
hardware simulation) at both the underflowing input `n = 2` (`= 1`) and the non-underflowing input
`n = 10` (`= 7`), as well as `n = 0` (`= 1`) and `n = 3` (`= 0`)! -/
example :
    let C := leanComposition "small" (lowerT smallUnderflowLExpr)
    let B := emit C
    SSteps (.app smallUnderflowLExpr (.lit 2)) (.lit 1) ∧
    SSteps (.app smallUnderflowLExpr (.lit 10)) (.lit 7) ∧
    Evaluates (.app (lowerT smallUnderflowLExpr) (.nat 2)) (.nat 1) ∧
    Evaluates (.app (lowerT smallUnderflowLExpr) (.nat 10)) (.nat 7) ∧
    Halts (.app (.get B.link "small") (.nat 2)) (.natural 1) ∧
    Halts (.app (.get B.link "small") (.nat 10)) (.natural 7) ∧
    (match compileBookToRtlSat "lean_small_sat_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 0#64) (fun _ => 0#64) == [("out_small", 1#64)]) &&
       (evalModuleOutputs m (fun _ => 2#64) (fun _ => 0#64) == [("out_small", 1#64)]) &&
       (evalModuleOutputs m (fun _ => 3#64) (fun _ => 0#64) == [("out_small", 0#64)]) &&
       (evalModuleOutputs m (fun _ => 10#64) (fun _ => 0#64) == [("out_small", 7#64)])
     | none => false) = true := by
  refine ⟨smallUnderflow_runs_2, smallUnderflow_runs_10, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [lowerT] using lower_sound_nat smallUnderflow_runs_2
  · simpa [lowerT] using lower_sound_nat smallUnderflow_runs_10
  · exact lean_to_book "small" smallUnderflowLExpr 2 1 (by decide +kernel) smallUnderflow_runs_2
  · exact lean_to_book "small" smallUnderflowLExpr 10 7 (by decide +kernel) smallUnderflow_runs_10
  · decide +kernel
end Obend.Lower

-- from Obend/Lower/Proofs/SelfAccelerate.lean:508: end-to-end run on a fixture (19 lines); worth a pre-push run, not every library build
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Equiv Obend.Leaf
open Obend.Hardware.HDL Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
open Obend.Hardware.OpenHypergraph
open Obend.Analysis
/-- **6-Stage Reflexive Self-Acceleration of LC Drives Direct In-Slot Stator Thermal Kernel**:
Proves that `lcDrivesInSlotThermalLExpr` at $P_{\text{loss}} = 8\,\text{kW}$ evaluates to $122^\circ\text{C}$
identically across:
1. `Lean-lite` source semantics (`SSteps`),
2. `Obend.Core` `Core4` semantics (`Evaluates`),
3. `Obend.Leaf.Book` graph-reduction semantics (`Halts`),
4. Synthesized FPGA RTL (`compileBookToRtlSat` + `evalModuleOutputs`),
5. Compiled AMD `CDNA3` GPU Wavefront ISA (`evalCompiledAmdGpuModule`), and
6. TPU Systolic Array (`runSystolicMacChain`) & FPGA `DSP58` Cascade (`runDsp58Cascade`),
while matching `Obend.Hardware.FluidThermal.evalPeakWindingTempMilliC`! -/
example :
    let C := leanComposition "lcThermal" (lowerT lcDrivesInSlotThermalLExpr)
    let B := emit C
    SSteps (.app lcDrivesInSlotThermalLExpr (.lit 8)) (.lit 122) ∧
    Evaluates (.app (lowerT lcDrivesInSlotThermalLExpr) (.nat 8)) (.nat 122) ∧
    Halts (.app (.get B.link "lcThermal") (.nat 8)) (.natural 122) ∧
    (match compileBookToRtlSat "lean_lc_thermal_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 8#64) (fun _ => 0#64) == [("out_lcThermal", 122#64)]) &&
       (evalCompiledAmdGpuModule m 8 == some 122)
     | none => false) = true ∧
    runSystolicMacChain 50 [8, 8, 8] [2, 4, 3] = 122 ∧
    runDsp58Cascade 50 [(8, 2), (8, 4), (8, 3)] = 122 ∧
    Obend.Hardware.FluidThermal.evalPeakWindingTempMilliC 50 8 2 4 3 = 122 := by
  refine ⟨lcDrivesInSlotThermal_runs_8kw, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat lcDrivesInSlotThermal_runs_8kw
  · exact lean_to_book "lcThermal" lcDrivesInSlotThermalLExpr 8 122 (by decide +kernel) lcDrivesInSlotThermal_runs_8kw
  · decide +kernel
end Obend.Lower

-- from Obend/Lower/Proofs/SelfAccelerate.lean:562: end-to-end run on a fixture (24 lines); worth a pre-push run, not every library build
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Equiv Obend.Leaf
open Obend.Hardware.HDL Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
open Obend.Hardware.OpenHypergraph
open Obend.Analysis
/-- **6-Stage Reflexive Self-Acceleration of Mission Power `MS350` MPPT Kernel + Ozaki `FP4` Tensor Core**:
Proves that `ms350MpptExtractedPowerLExpr` at the Maximum Power Point $V^\star = 100 = (-4) + 13 \times 8$
evaluates to $10000$ identically across:
1. `Lean-lite` source semantics (`SSteps`),
2. `Obend.Core` `Core4` semantics (`Evaluates`),
3. `Obend.Leaf.Book` graph-reduction semantics (`Halts`),
4. Synthesized saturating FPGA RTL (`compileBookToRtlSat` + `evalModuleOutputs`),
5. Compiled AMD `CDNA3` GPU Wavefront ISA (`evalCompiledAmdGpuModule`), and
6. Ozaki Scheme Base-13 `FP4 (E2M1)` Tensor-Core limb multiplication (`evalOzakiBase13Product2 (-4) 8 (-4) 8 = 10000`,
   where both `-4` and `8` are exact doubled `FP4 (E2M1)` values in $S_{\text{E2M1}}$!),
while matching `Obend.Hardware.PowerElectronics.evalExtractedPower 200 1 100 = 10000`! -/
example :
    let C := leanComposition "ms350Mppt" (lowerT ms350MpptExtractedPowerLExpr)
    let B := emit C
    SSteps (.app ms350MpptExtractedPowerLExpr (.lit 100)) (.lit 10000) ∧
    Evaluates (.app (lowerT ms350MpptExtractedPowerLExpr) (.nat 100)) (.nat 10000) ∧
    Halts (.app (.get B.link "ms350Mppt") (.nat 100)) (.natural 10000) ∧
    (match compileBookToRtlSat "lean_ms350_mppt_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 100#64) (fun _ => 0#64) == [("out_ms350Mppt", 10000#64)]) &&
       (evalCompiledAmdGpuModule m 100 == some 10000) &&
       -- Also check off-MPP voltage V = 80 -> P(80) = 80 * 120 = 9600 < 10000 on both FPGA and AMD GPU!
       (evalModuleOutputs m (fun _ => 80#64) (fun _ => 0#64) == [("out_ms350Mppt", 9600#64)]) &&
       (evalCompiledAmdGpuModule m 80 == some 9600)
     | none => false) = true ∧
    isDoubledFp4E2M1 (-4) = true ∧
    isDoubledFp4E2M1 8 = true ∧
    evalBase13Limb2 (-4) 8 = 100 ∧
    evalOzakiBase13Product2 (-4) 8 (-4) 8 = 10000 ∧
    Obend.Hardware.PowerElectronics.evalExtractedPower 200 1 100 = 10000 := by
  refine ⟨ms350MpptExtractedPower_runs_100v, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat ms350MpptExtractedPower_runs_100v
  · exact lean_to_book "ms350Mppt" ms350MpptExtractedPowerLExpr 100 10000 (by decide +kernel) ms350MpptExtractedPower_runs_100v
  · decide +kernel
end Obend.Lower

-- from Obend/Lower/Proofs/SelfAccelerate.lean:650: end-to-end run on a fixture (18 lines); worth a pre-push run, not every library build
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Equiv Obend.Leaf
open Obend.Hardware.HDL Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
open Obend.Hardware.OpenHypergraph
open Obend.Analysis
/-- **6-Stage Reflexive Self-Acceleration of 2D FEMM Magnetic Energy Kernel**:
Proves that `femm2dElementEnergyLExpr` at $a_0 = 6$ evaluates to $125$ across:
1. `Lean-lite` source semantics (`SSteps`),
2. `Obend.Core` `Core4` semantics (`Evaluates`),
3. `Obend.Leaf.Book` graph-reduction semantics (`Halts`),
4. Synthesized saturating FPGA RTL (`compileBookToRtlSat` + `evalModuleOutputs`),
5. Compiled AMD `CDNA3` GPU Wavefront ISA (`evalCompiledAmdGpuModule`) AND single-instruction
   AMD Matrix-Core `vMfmaDot4` execution (`execAmdGpuInst`), and
6. `Obend.Hardware.Magnetics.evalElementMagneticEnergyScaled selfAccelFemmTriangle 6 3 2 = 125`! -/
example :
    let C := leanComposition "femmEnergy" (lowerT femm2dElementEnergyLExpr)
    let B := emit C
    SSteps (.app femm2dElementEnergyLExpr (.lit 6)) (.lit 125) ∧
    Evaluates (.app (lowerT femm2dElementEnergyLExpr) (.nat 6)) (.nat 125) ∧
    Halts (.app (.get B.link "femmEnergy") (.nat 6)) (.natural 125) ∧
    (match compileBookToRtlSat "lean_femm_energy_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 6#64) (fun _ => 0#64) == [("out_femmEnergy", 125#64)]) &&
       (evalCompiledAmdGpuModule m 6 == some 125)
     | none => false) = true ∧
    readVgpr (execAmdGpuInst [0, 20, 15, 0, 0, 4, 3, 0, 0] (.vMfmaDot4 0 1 5 0)) 0 = 125 ∧
    Obend.Hardware.Magnetics.evalElementMagneticEnergyScaled selfAccelFemmTriangle 6 3 2 = 125 := by
  refine ⟨femm2dElementEnergy_runs_6, ?_, ?_, ?_, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat femm2dElementEnergy_runs_6
  · exact lean_to_book "femmEnergy" femm2dElementEnergyLExpr 6 125 (by decide +kernel) femm2dElementEnergy_runs_6
  · decide +kernel
end Obend.Lower

-- from Obend/Lower/Proofs/SelfAccelerate.lean:1005: end-to-end run on a fixture (25 lines); worth a pre-push run, not every library build
namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Equiv Obend.Leaf
open Obend.Hardware.HDL Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
open Obend.Hardware.OpenHypergraph
open Obend.Analysis
/-- **6-Stage Reflexive Self-Acceleration of E-Graph-Optimized Adjoint `RtlModule` & Nested `AmdGpuVop64Inst`
(`eqSat_adjoint_nested_vop64_self_accelerates_6stage`)**:
Proves end-to-end 6-stage self-acceleration on a nested multi-operator adjoint datapath:
1. `Lean-lite` `SSteps` on `statorAdjointCurrentGradLExpr` at $I = 3$ evaluates to `36`,
2. `Obend.Core` `Evaluates` evaluates to `36`,
3. `Obend.Leaf.Book` `Halts` evaluates to `36`,
4. Synthesized saturating FPGA RTL (`compileBookToRtlSat`) AND pipelined E-Graph-optimized adjoint
   `RtlModule` (`compileHypergraphToRtlPipelined` on `optimizeAdjointHypergraph defaultRtlCostModel`),
5. Compiled 64-bit AMD `CDNA3` `AmdGpuVop64Inst` (`evalCompiledAmdGpuModule m 3 == some 36` AND
   `evalAmdGpuExpr` on `nestedMacAdjointExpr` = `36#64`), and
6. E-Graph-saturated adjoint hypergraph evaluation (`statorCoupledLoss_adjoint_eqSat_sound` producing
   `[95, 36, 14, 7, 4]`), TPU Systolic Array (`runSystolicMacChain 0 [3, 3] [6, 6] = 36`), and
   FPGA `DSP58` Cascade (`runDsp58Cascade 0 [(3, 6), (3, 6)] = 36`)! -/
example :
    let C := leanComposition "statorAdjGrad" (lowerT statorAdjointCurrentGradLExpr)
    let B := emit C
    SSteps (.app statorAdjointCurrentGradLExpr (.lit 3)) (.lit 36) ∧
    Evaluates (.app (lowerT statorAdjointCurrentGradLExpr) (.nat 3)) (.nat 36) ∧
    Halts (.app (.get B.link "statorAdjGrad") (.nat 3)) (.natural 36) ∧
    (match compileBookToRtlSat "lean_stator_adj_grad_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 3#64) (fun _ => 0#64) == [("out_statorAdjGrad", 36#64)]) &&
       (evalCompiledAmdGpuModule m 3 == some 36)
     | none => false) = true ∧
    evalAmdGpuExpr
      (fun u => BitVec.ofInt 64 (statorCoupledLossAdjointEnv 3 4 2 5 1 u))
      (fun _ => 0#64) (fun _ => 0#64) nestedMacAdjointExpr = 36#64 ∧
    evalHypergraphComb
      (optimizeAdjointHypergraph defaultRtlCostModel statorCoupledLossHypergraph)
      (statorCoupledLossAdjointEnv 3 4 2 5 1) = [95, 36, 14, 7, 4] ∧
    runSystolicMacChain 0 [3, 3] [6, 6] = 36 ∧
    runDsp58Cascade 0 [(3, 6), (3, 6)] = 36 := by
  refine ⟨statorAdjointCurrentGrad_runs_3, ?_, ?_, ?_, rfl, ?_, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat statorAdjointCurrentGrad_runs_3
  · exact lean_to_book "statorAdjGrad" statorAdjointCurrentGradLExpr 3 36 (by decide +kernel) statorAdjointCurrentGrad_runs_3
  · decide +kernel
  · decide +kernel
end Obend.Lower

-- from Obend/Lower/Proofs/SiliconKernel.lean:561: a 10-line closed evaluation; worth a pre-push run
namespace Obend.Lower.Proofs.SiliconKernel
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
/-- A closed check (it was the theorem `silicon_kernel_seq_rtl_fuel_sound` until 2026-11-04):
Proves that lowering `kernelFuelLoopLExpr` (`Nat.rec` fuel-bounded accumulator) through `Core4`
and `Leaf.Book` and synthesizing sequential multi-cycle RTL via `compileBookToSeqRtlSat`:
1. Produces a valid sequential `RtlModule` (`checkRtlModule m = true`),
2. Remains busy (`out_done = 0#64`) at cycle `4` when given fuel bound `5#64`, and
3. Asserts `out_done = 1#64` with the exact accumulated step counts (`0#64`, `15#64`, `36#64`)
   after `0`, `5`, and `8` clock cycles (`evalSeqModuleAfterCycles`). -/
example :
    (match compileBookToSeqRtlSat "silicon_kernel_fuel_seq_rtl" kernelFuelLoopBook with
     | some m =>
       checkRtlModule m &&
       (evalSeqModuleAfterCycles m 0#64 0 == [("out_kernelFuelLoop", 0#64), ("out_done", 1#64)]) &&
       (evalSeqModuleAfterCycles m 5#64 4 == [("out_kernelFuelLoop", 10#64), ("out_done", 0#64)]) &&
       (evalSeqModuleAfterCycles m 5#64 5 == [("out_kernelFuelLoop", 15#64), ("out_done", 1#64)]) &&
       (evalSeqModuleAfterCycles m 8#64 8 == [("out_kernelFuelLoop", 36#64), ("out_done", 1#64)])
     | none => false) = true := by
  decide +kernel
end Obend.Lower.Proofs.SiliconKernel

-- from Obend/Lower/Proofs/SiliconKernel.lean:690: end-to-end run on a fixture (31 lines); worth a pre-push run, not every library build
namespace Obend.Lower.Proofs.SiliconKernel
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
/-- **Theorem (`stepCamNodeWord_fragment_6stage_sound`)**:
Proves that the pure decidable hardware-word kernel transition functions (`stepCamWhnfNodeWord`,
`stepCamDefEqNodeWord`, `stepCamInferNodeWord`) agree with their lowered `LExpr` (`evalKernelStepLExpr`,
`stepCamDefEqNodeLExpr`, `inferTypeLExpr`), `Core4.Term` (`lowerT`), `Leaf.Book`, and synthesized
4-port `RtlModule` (`compileBookToRtlSat`) across WHNF $\beta/\iota/\zeta$, `isDefEq` handle identity
and `Nat.succ` bridging, and `inferType` arrow checking without host precomputation! -/
example :
    stepCamWhnfNodeWord 5 1 35 7 = 42 ∧
    stepCamWhnfNodeWord 5 2 41 0 = 42 ∧
    stepCamInferNodeWord 5 17 1 1 = 1 ∧
    stepCamInferNodeWord 5 17 3 1 = 0 ∧
    stepCamInferNodeWord 4 1 1 17 = 17 ∧
    stepCamDefEqNodeWord 1 42 1 42 = 1 ∧
    stepCamDefEqNodeWord 1 0 3 1 = 1 ∧
    stepCamDefEqNodeWord 1 5 5 4 = 1 ∧
    stepCamDefEqNodeWord 1 5 1 6 = 0 ∧
    SSteps (app4LExpr stepCamDefEqNodeLExpr 1 42 1 42) (.lit 1) ∧
    SSteps (app4LExpr stepCamDefEqNodeLExpr 1 0 3 1) (.lit 1) ∧
    SSteps (app4LExpr stepCamDefEqNodeLExpr 1 5 5 4) (.lit 1) ∧
    SSteps (app4LExpr stepCamDefEqNodeLExpr 1 5 1 6) (.lit 0) ∧
    Evaluates (lowerT (app4LExpr stepCamDefEqNodeLExpr 1 5 5 4)) (.nat 1) ∧
    evalLoweredDefEqNodeRtl (1, 42, 1, 42) = [("out_stepCamDefEqNode", 1#64)] ∧
    evalLoweredDefEqNodeRtl (1, 0, 3, 1) = [("out_stepCamDefEqNode", 1#64)] ∧
    evalLoweredDefEqNodeRtl (1, 5, 5, 4) = [("out_stepCamDefEqNode", 1#64)] ∧
    evalLoweredDefEqNodeRtl (1, 5, 1, 6) = [("out_stepCamDefEqNode", 0#64)] := by
  have sEq1 : SSteps (app4LExpr stepCamDefEqNodeLExpr 1 42 1 42) (.lit 1) :=
    runLExprSteps_sound 64 _ _ rfl
  have sEq2 : SSteps (app4LExpr stepCamDefEqNodeLExpr 1 0 3 1) (.lit 1) :=
    runLExprSteps_sound 64 _ _ rfl
  have sEq3 : SSteps (app4LExpr stepCamDefEqNodeLExpr 1 5 5 4) (.lit 1) :=
    runLExprSteps_sound 64 _ _ rfl
  have sEq4 : SSteps (app4LExpr stepCamDefEqNodeLExpr 1 5 1 6) (.lit 0) :=
    runLExprSteps_sound 64 _ _ rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          sEq1, sEq2, sEq3, sEq4,
          by simpa [lowerT] using lower_sound_nat sEq3,
          by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
end Obend.Lower.Proofs.SiliconKernel

-- from Obend/Lower/SiliconElabFabric.lean:2224: a 9-line closed evaluation; worth a pre-push run
namespace Obend.Lower.SiliconElabFabric
open Obend.Core.Term
open Obend.Core.Ty (Ty Quantity Reuse)
open Obend.Equiv
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
open Obend.Judge
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.ExprCAM
open Obend.Lower.MetaUnify
open Obend.Lower.DiscrTreeLUT
open Obend.Lower.Proofs.SiliconKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
open Obend.Hardware.Judge
/-- **Theorem (`emitSiliconElabFabricSV_five_modules_sound`)**:
Verifies that `emitSiliconElabFabricSVLines` emits all 5 Silicon Elaborator modules
(`obend_zone1_expr_cam`, `obend_zone2_noc_unifier`, `obend_zone3_discr_lut`,
`obend_zone4_kernel_fsm`, `silicon_elab_top`) together with the 2 hardware macro modules
(`obend_macro_noc_router_xy`, `obend_macro_icap_dpr_tile`). -/
example :
    emitSiliconElabFabricSVLines.contains "module obend_macro_noc_router_xy (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_macro_icap_dpr_tile (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_zone1_expr_cam (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_zone2_noc_unifier (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_zone3_discr_lut (" = true ∧
    emitSiliconElabFabricSVLines.contains "module obend_zone4_kernel_fsm (" = true ∧
    emitSiliconElabFabricSVLines.contains "module silicon_elab_top (" = true := by
  decide +kernel
end Obend.Lower.SiliconElabFabric
