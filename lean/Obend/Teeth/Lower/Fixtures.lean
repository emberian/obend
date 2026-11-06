/-
# `Obend/Teeth/Lower/Fixtures.lean` — the closed fixtures that left tier 1 (2026-11-04)

Each `example` here was a `theorem` in a tier-1 module of `Obend/Lower/`: a closed statement, proved by
`decide +kernel` on literal data, that nothing cites. The triage of 2026-11-04 (`Obend/Census.lean`,
`review/DECISIONS-20261031.md`) keeps them as what they are, end-to-end runs worth doing before a
push and not on every library build. Each carries the module it came from and why it is kept. This
file is tier 2: `lake build Teeth`; a plain file, so it sees every definition with its body.
-/

import Obend.Lower.Proofs.Hardware
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
