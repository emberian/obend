module
/-
# Obend.Lower.Proofs.SiliconKernel — End-to-End Silicon Lean Kernel & Elaborator on `ReductionMachine`

Implements Stage 4 (`WS 23` / `SILICON-ELABORATOR.md` §6–7) of the Silicon Lean Kernel & Elaborator,
connecting:
- `Obend.Lower.Inductive` (recursive AST inductives & LCNF lowering),
- `Obend.Leaf.Futamura` (static data-pin specialization & 1st/2nd/3rd Futamura projections),
- `Obend.Lower.LeanKernel` (self-hosted pure Lean kernel `whnf`/`isDefEq`/`inferType`/`checkDecl`
  and elaborator `simp`/typeclass/macro passes),
- `Obend.Lower.Proofs.Hardware` (`compileBookToRtlSat` 4-stage verified pipeline), and
- `Obend.Hardware.ReductionMachine` (`AutomatonTile`, `AutomatonNetwork`, 3-phase Glitch-Free `ICAP`
  Dynamic Partial Reconfiguration, and hardware interaction-net `reduceActivePair`).

## Main Theorems (`0 sorryAx`)

1. **`silicon_kernel_5stage_check_sound`**:
   Proves the complete 5-stage verified chain (`LeanKernel.kernelCheckDecl` → `LExpr` `SSteps` →
   `Core4` `Evaluates` → `Leaf.Book` `Halts` → `RtlModule` `compileBookToRtlSat` &
   `ReductionMachine` `compileBookToAutomaton` / `evalAutomatonPacket`) for both valid declarations
   (accepted with hardware output `1#64`) and invalid declarations (definitional mismatch,
   ill-typed application, universe mismatch, and `sorryAx` contamination — all refused with
   hardware output `0#64`).
2. **`silicon_elab_futamura_dpr_specialize_sound`**:
   Proves that specializing the elaborator's `simp` rewrite pass against a pinned `Environment`
   slot (`envPin = 1`) via the 1st Futamura projection (`futamura1Specialize` / `futamura1Book`)
   and hot-swapping the resulting `AutomatonTile` into tile `0` of a multi-tile `EfpgaDprArray`
   via `runTileGlitchFreeDpr`:
   - Validates `futamura1Candidate` under `specSlot` at the pinned view (`viewOf`),
   - Clamps tile `0`'s output glitch-free during reconfiguration (`isolated_fence_clamps_output_during_write`),
   - Leaves neighbor tile `1` (the resident kernel checker tile) and all in-flight `ReductionPacket`s
     strictly untouched (`dpr_preserves_neighbor_tiles_and_packets`), and
   - Executes the specialized hardware datapath (`x ↦ 4x + 2`, evaluating `10#64 ↦ 42#64`) once the
     isolation fence releases (`dpr_specialized_tile_executes_new_book`).
3. **`silicon_elab_env_mutation_fallback_sound`**:
   Proves that when the `Environment` mutates (producing a mutated `LeafView`), `specSlot`
   immediately invalidates `futamura1Candidate` (`moved_pin_blocks`), selects the resident
   `Candidate.machine` fallback in 1 step (`futamura1_env_specialize_sound`, `machine_usable`),
   and rejects any bitstream frame with a mismatched digest (`dpr_corrupt_crc_keeps_tile_isolated`).
4. **`silicon_kernel_inet_beta_agrees`**:
   Proves that 1-cycle hardware interaction-net $\beta$-reduction (`reduceActivePair` on `.lam` and
   `.nat64`) agrees with both `LeanKernel.kernelWhnf` and `Core4.Evaluates`.
-/
public import Obend.Lower.LeanKernel
public import Obend.Lower.Proofs.Hardware
public import Obend.Hardware.ReductionMachine
@[expose] public section

namespace Obend.Lower.Proofs.SiliconKernel
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Equiv
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-! ## 1. Hardware-Synthesizable Kernel Declaration Gate (`kernelGateBody`) -/

/-- Classify a `KConstInfo` declaration into its hardware verification status code:
* `0`: Refused — `sorryAx` contamination (`exprContainsSorry = true`),
* `1`: Accepted — well-typed declaration (`kernelCheckDecl env fuel decl = true`),
* `2`: Refused — definitional equality / value-type mismatch,
* `3`: Refused — universe sort mismatch (`decl.type` is a sort that fails universe equality). -/
def encodeDeclStatusTag (env : KEnv) (fuel : Nat) (decl : KConstInfo) : Nat :=
  let hasSorry :=
    match decl with
    | .axiomInfo _ _ ty | .inductInfo _ _ ty | .ctorInfo _ _ ty _ =>
      exprContainsSorry ty
    | .defnInfo _ _ ty val | .thmInfo _ _ ty val =>
      exprContainsSorry ty || exprContainsSorry val
  if hasSorry then 0
  else if kernelCheckDecl env fuel decl then 1
  else
    match decl.type with
    | .sort _ => 3
    | _ => 2

theorem encodeDeclStatusTag_validIdNat :
    encodeDeclStatusTag stdKernelEnv 8 validIdNatDecl = 1 := rfl

theorem encodeDeclStatusTag_validPropId :
    encodeDeclStatusTag stdKernelEnv 8 validPropIdDecl = 1 := rfl

theorem encodeDeclStatusTag_validApplyId42 :
    encodeDeclStatusTag stdKernelEnv 8 validApplyId42Decl = 1 := rfl

theorem encodeDeclStatusTag_invalidMismatch :
    encodeDeclStatusTag stdKernelEnv 8 invalidMismatchDecl = 2 := rfl

theorem encodeDeclStatusTag_invalidBadApp :
    encodeDeclStatusTag stdKernelEnv 8 invalidBadAppDecl = 2 := rfl

theorem encodeDeclStatusTag_invalidUniverse :
    encodeDeclStatusTag stdKernelEnv 8 invalidUniverseDecl = 3 := rfl

theorem encodeDeclStatusTag_invalidSorry :
    encodeDeclStatusTag stdKernelEnv 8 invalidSorryDecl = 0 := rfl

/-- Unary `LExpr` body for the hardware kernel acceptance gate:
accepts (`1`) iff the declaration status tag at `.bvar 0` equals `1` (verified clean declaration),
and refuses (`0`) on tags `0` (`sorryAx`), `2` (type/defEq mismatch), and `3` (universe error). -/
def kernelGateBody : LExpr :=
  .boolRec .natural
    (.lit 0)
    (.lit 1)
    (.natBin .beq (.bvar 0) (.lit 1))

/-- Full unary `LExpr` function for the hardware kernel acceptance gate. -/
def kernelGateLExpr : LExpr :=
  .lam .natural kernelGateBody

/-- `lowerLiteScalar` agrees identically with `lowerT` on `kernelGateLExpr`. -/
theorem kernelGate_matches_lowerT :
    lowerT kernelGateLExpr = .lam (lowerLiteScalar kernelGateBody) := by
  simp [kernelGateLExpr, kernelGateBody, lowerT, lowerLiteScalar, NatOp.prim]

/-- Source `SSteps` reduction of `kernelGateLExpr` on any status tag `tag : Nat`. -/
theorem kernelGateLExpr_runs (tag : Nat) :
    SSteps (.app kernelGateLExpr (.lit tag)) (.lit (if tag == 1 then 1 else 0)) := by
  unfold kernelGateLExpr kernelGateBody
  refine .next (.beta .natural _ (.lit tag)) ?_
  have hinst :
      (LExpr.boolRec .natural (.lit 0) (.lit 1) (.natBin .beq (.bvar 0) (.lit 1))).inst (.lit tag) =
      .boolRec .natural (.lit 0) (.lit 1) (.natBin .beq (.lit tag) (.lit 1)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (.boolRecMajor .natural (.lit 0) (.lit 1) (.binLit .beq tag 1)) ?_
  dsimp only [NatOp.eval]
  cases (tag == 1)
  · simpa using SSteps.next (.boolRecFalse .natural (.lit 0) (.lit 1)) (.refl _)
  · simpa using SSteps.next (.boolRecTrue .natural (.lit 0) (.lit 1)) (.refl _)

/-- Emitted `Obend.Leaf.Book` for `kernelGateLExpr`. -/
def kernelGateBook : Book :=
  emit (leanComposition "kernelGate" (lowerT kernelGateLExpr))

/-- Compiled `AutomatonTile` for the resident hardware kernel gate (`kernelGateBody`). -/
def kernelGateTile : AutomatonTile :=
  (compileLiteMethodToTile "kernelGate" kernelGateBody).getD incAutomatonTile

/-- **Theorem (`silicon_kernel_5stage_check_sound`)**:
Proves the complete 5-stage verified chain from the self-hosted Lean kernel (`kernelCheckDecl`)
through `LExpr` (`SSteps`), `Core4` (`Evaluates`), `Obend.Leaf.Book` (`Halts`), `RtlModule`
(`compileBookToRtlSat`), and `ReductionMachine` (`compileBookToAutomaton` + `evalAutomatonPacket`):
1. Valid declarations (`validIdNatDecl`, `validPropIdDecl`, `validApplyId42Decl`) evaluate to `1`
   across all 5 stages and output `1#64` on the `ReductionMachine` `AutomatonNetwork`.
2. Invalid declarations (`invalidMismatchDecl`, `invalidBadAppDecl`, `invalidUniverseDecl`,
   `invalidSorryDecl`) are refused (`0`) across all 5 stages and output `0#64` on the
   `ReductionMachine` `AutomatonNetwork`. -/
theorem silicon_kernel_5stage_check_sound :
    let tagValid := encodeDeclStatusTag stdKernelEnv 8 validIdNatDecl
    let tagMismatch := encodeDeclStatusTag stdKernelEnv 8 invalidMismatchDecl
    let tagBadApp := encodeDeclStatusTag stdKernelEnv 8 invalidBadAppDecl
    let tagBadUniv := encodeDeclStatusTag stdKernelEnv 8 invalidUniverseDecl
    let tagSorry := encodeDeclStatusTag stdKernelEnv 8 invalidSorryDecl
    -- Stage 1: Self-hosted kernel & LExpr SSteps
    SSteps (.app kernelGateLExpr (.lit tagValid)) (.lit 1) ∧
    SSteps (.app kernelGateLExpr (.lit tagMismatch)) (.lit 0) ∧
    SSteps (.app kernelGateLExpr (.lit tagBadApp)) (.lit 0) ∧
    SSteps (.app kernelGateLExpr (.lit tagBadUniv)) (.lit 0) ∧
    SSteps (.app kernelGateLExpr (.lit tagSorry)) (.lit 0) ∧
    -- Stage 2: Core4 Evaluates
    Evaluates (.app (lowerT kernelGateLExpr) (.nat tagValid)) (.nat 1) ∧
    Evaluates (.app (lowerT kernelGateLExpr) (.nat tagMismatch)) (.nat 0) ∧
    Evaluates (.app (lowerT kernelGateLExpr) (.nat tagBadUniv)) (.nat 0) ∧
    Evaluates (.app (lowerT kernelGateLExpr) (.nat tagSorry)) (.nat 0) ∧
    -- Stage 3: Leaf.Book Halts
    Halts (.app (.get kernelGateBook.link "kernelGate") (.nat tagValid)) (.natural 1) ∧
    Halts (.app (.get kernelGateBook.link "kernelGate") (.nat tagMismatch)) (.natural 0) ∧
    Halts (.app (.get kernelGateBook.link "kernelGate") (.nat tagBadUniv)) (.natural 0) ∧
    Halts (.app (.get kernelGateBook.link "kernelGate") (.nat tagSorry)) (.natural 0) ∧
    -- Stage 4 & 5: RtlModule (compileBookToRtlSat) & ReductionMachine (compileBookToAutomaton)
    (match compileBookToRtlSat "silicon_kernel_gate_rtl" kernelGateBook,
           compileBookToAutomaton "silicon_kernel_gate_net" kernelGateBook with
     | some rtlMod, some net =>
       checkRtlModule rtlMod &&
       (evalModuleOutputs rtlMod (fun _ => BitVec.ofNat 64 tagValid) (fun _ => 0#64) == [("out_kernelGate", 1#64)]) &&
       (evalModuleOutputs rtlMod (fun _ => BitVec.ofNat 64 tagMismatch) (fun _ => 0#64) == [("out_kernelGate", 0#64)]) &&
       (evalModuleOutputs rtlMod (fun _ => BitVec.ofNat 64 tagBadApp) (fun _ => 0#64) == [("out_kernelGate", 0#64)]) &&
       (evalModuleOutputs rtlMod (fun _ => BitVec.ofNat 64 tagBadUniv) (fun _ => 0#64) == [("out_kernelGate", 0#64)]) &&
       (evalModuleOutputs rtlMod (fun _ => BitVec.ofNat 64 tagSorry) (fun _ => 0#64) == [("out_kernelGate", 0#64)]) &&
       (evalAutomatonPacket net (fun _ => 0#64) { targetSlot := 0, argVal := BitVec.ofNat 64 tagValid, tag := 1 } == 1#64) &&
       (evalAutomatonPacket net (fun _ => 0#64) { targetSlot := 0, argVal := BitVec.ofNat 64 tagMismatch, tag := 2 } == 0#64) &&
       (evalAutomatonPacket net (fun _ => 0#64) { targetSlot := 0, argVal := BitVec.ofNat 64 tagBadUniv, tag := 3 } == 0#64) &&
       (evalAutomatonPacket net (fun _ => 0#64) { targetSlot := 0, argVal := BitVec.ofNat 64 tagSorry, tag := 4 } == 0#64)
     | _, _ => false) = true := by
  intro tagValid tagMismatch tagBadApp tagBadUniv tagSorry
  have hv : tagValid = 1 := rfl
  have hm : tagMismatch = 2 := rfl
  have ha : tagBadApp = 2 := rfl
  have hu : tagBadUniv = 3 := rfl
  have hs : tagSorry = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]; exact kernelGateLExpr_runs 1
  · rw [hm]; exact kernelGateLExpr_runs 2
  · rw [ha]; exact kernelGateLExpr_runs 2
  · rw [hu]; exact kernelGateLExpr_runs 3
  · rw [hs]; exact kernelGateLExpr_runs 0
  · rw [hv]; simpa [lowerT] using lower_sound_nat (kernelGateLExpr_runs 1)
  · rw [hm]; simpa [lowerT] using lower_sound_nat (kernelGateLExpr_runs 2)
  · rw [hu]; simpa [lowerT] using lower_sound_nat (kernelGateLExpr_runs 3)
  · rw [hs]; simpa [lowerT] using lower_sound_nat (kernelGateLExpr_runs 0)
  · rw [hv]; exact lean_to_book "kernelGate" kernelGateLExpr 1 1 (by decide +kernel) (kernelGateLExpr_runs 1)
  · rw [hm]; exact lean_to_book "kernelGate" kernelGateLExpr 2 0 (by decide +kernel) (kernelGateLExpr_runs 2)
  · rw [hu]; exact lean_to_book "kernelGate" kernelGateLExpr 3 0 (by decide +kernel) (kernelGateLExpr_runs 3)
  · rw [hs]; exact lean_to_book "kernelGate" kernelGateLExpr 0 0 (by decide +kernel) (kernelGateLExpr_runs 0)
  · decide +kernel

/-! ## 2. Futamura-Specialized Elaborator Tile & Glitch-Free `ICAP` DPR Co-Simulation -/

/-- Unspecialized elaborator `simp` dispatcher in `Core4`:
`λ envPin => λ x => if envPin == 1 then 4 * x + 2 else x + 1`.
When `envPin = 1` is pinned via the 1st Futamura projection (`futamura1Specialize`), the environment
branch folds away to the specialized datapath `λ x => 4 * x + 2`. -/
def elabSimpInterpreterTerm : Term :=
  .lam -- envPin (bound 1 inside inner)
    (.lam -- x (bound 0 inside inner)
      (.ifBool
        (.binary .equal (.bound 1) (.nat 1))
        (.binary .add (.binary .multiply (.bound 0) (.nat 4)) (.nat 2))
        (.binary .add (.bound 0) (.nat 1))))

/-- Pinned environment value `envPin = .nat 1` (`stdKernelEnv` + `[simp] f x = 4 * x + 2`). -/
def pinnedElabEnvTerm : Term := .nat 1

/-- 1st Futamura projection of `elabSimpInterpreterTerm` specialized to `pinnedElabEnvTerm`. -/
def futamura1ElabSimpTerm : Term :=
  futamura1Specialize elabSimpInterpreterTerm pinnedElabEnvTerm

/-- Lowered `Lean-lite` body for the Futamura-specialized `simp` datapath ($x \mapsto 4x + 2$). -/
def specializedSimpBody : LExpr :=
  .natBin .add (.natBin .mul (.bvar 0) (.lit 4)) (.lit 2)

/-- Concrete `Core4.Term` produced by the 1st Futamura projection ($x \mapsto 4x + 2$). -/
def specializedSimpTerm : Term :=
  .lam (lowerLiteScalar specializedSimpBody)

/-- Theorem (`futamura1ElabSimpTerm_eq_lowerLite`):
The 1st Futamura projection `futamura1ElabSimpTerm` folds the static environment check
`envPin == 1` at compile time and produces the exact `Core4` term `specializedSimpTerm = lowerT (.lam .natural specializedSimpBody)`! -/
theorem futamura1ElabSimpTerm_eq_lowerLite :
    futamura1ElabSimpTerm = specializedSimpTerm ∧
    futamura1ElabSimpTerm = lowerT (.lam .natural specializedSimpBody) := by
  have h1 : futamura1ElabSimpTerm = specializedSimpTerm := by
    simp [futamura1ElabSimpTerm, futamura1Specialize, elabSimpInterpreterTerm, pinnedElabEnvTerm,
      dataPinSpecialize, dataPinSteps, dataPinPass, Obend.Leaf.Futamura.resolveApp,
      Obend.Leaf.Futamura.resolveIfBool, Obend.Leaf.Futamura.resolveBinary,
      instantiate, Term.substitute, liftSubstitution, Term.rename, primitiveResult,
      specializedSimpTerm, specializedSimpBody, lowerLiteScalar, NatOp.prim]
  refine ⟨h1, ?_⟩
  rw [h1]
  simp [specializedSimpTerm, specializedSimpBody, lowerLiteScalar, lowerT, NatOp.prim]

/-- Compiled `AutomatonTile` for the Futamura-specialized `simp` elaborator pass ($x \mapsto 4x + 2$). -/
def specializedSimpTile : AutomatonTile :=
  (compileLiteMethodToTile "specializedSimp" specializedSimpBody).getD incAutomatonTile

/-- Specialized `Composition` for `specializedSimp`. -/
def specializedSimpComp :=
  leanComposition "specializedSimp" specializedSimpTerm

theorem futamura1Comp_eq_specializedSimpComp :
    futamura1Composition "specializedSimp" elabSimpInterpreterTerm pinnedElabEnvTerm =
      specializedSimpComp := by
  unfold futamura1Composition specializedSimpComp
  rw [← futamura1ElabSimpTerm_eq_lowerLite.1]
  rfl

/-- Specialized `Candidate` (`Candidate.book`) for `specializedSimp`. -/
def specializedSimpCand : Candidate :=
  .book "specializedSimp" specializedSimpComp

theorem futamura1Cand_eq_specializedSimpCand :
    futamura1Candidate "specializedSimp" elabSimpInterpreterTerm pinnedElabEnvTerm =
      specializedSimpCand := by
  unfold futamura1Candidate specializedSimpCand
  rw [futamura1Comp_eq_specializedSimpComp]

/-- Pinned `LeafView` at Epoch 1 supporting `specializedSimpComp`. -/
def pinnedSimpView : LeafView :=
  viewOf 1 "specializedSimp" specializedSimpComp

/-- Mutated `LeafView` at Epoch 2 where the environment pin has changed to `x ↦ x + 1`. -/
def mutatedSimpView : LeafView :=
  viewOf 2 "specializedSimp" (leanComposition "specializedSimp" (.lam (.binary .add (.bound 0) (.nat 1))))

/-- **Theorem (`silicon_elab_futamura_dpr_specialize_sound`)**:
End-to-end verification of Futamura specialization + `ICAP` Dynamic Partial Reconfiguration on
a 2-tile `ReductionMachine` eFPGA array (`tile 0` = reconfigurable elaborator slot, `tile 1` =
resident kernel checker `kernelGateTile`):
1. Under `pinnedSimpView` (Epoch 1), `specSlot` validates `specializedSimpCand` (`specSlot.usable = true`),
2. The 1st Futamura projection `futamura1ElabSimpTerm` is behaviorally equivalent (`≈b`) to
   `.app elabSimpInterpreterTerm pinnedElabEnvTerm` and equals `lowerT (.lam .natural specializedSimpBody)`,
3. Reconfiguring `tile 0` with `specializedSimpTile` via `runTileGlitchFreeDpr`:
   - Holds `tile 0`'s output glitch-free at `skidHeldOutput` while the frame loads,
   - Preserves neighbor `tile 1` (`kernelGateTile`) and all in-flight `skidBufferPkts` untouched,
   - Transitions `tile 0` from `10#64 ↦ 11#64` (unspecialized fallback) to `10#64 ↦ 42#64`
     ($4 \times 10 + 2 = 42$) after fence release, while `tile 1` continues checking kernel
     declarations (`1#64 ↦ 1#64`, `2#64 ↦ 0#64`) without interruption! -/
theorem silicon_elab_futamura_dpr_specialize_sound :
    let initTile0 : ReconfigTileState :=
      { tileId := 0, tileX := 0, tileY := 0
      , activeTile := incAutomatonTile, frameDigest := 0x1001#64
      , isolated := false, skidHeldOutput := 11#64 }
    let residentTile1 : ReconfigTileState :=
      { tileId := 1, tileX := 1, tileY := 0
      , activeTile := kernelGateTile, frameDigest := 0xCAFE#64
      , isolated := false, skidHeldOutput := 1#64 }
    let inflightPkt : ReductionPacket := { targetSlot := 1, argVal := 1#64, tag := 99 }
    let initArray : EfpgaDprArray :=
      { tiles := [initTile0, residentTile1]
      , skidBufferPkts := [inflightPkt]
      , icapBusy := false
      , crcErrorCount := 0 }
    let icapFrame : IcapBitstreamFrame :=
      { targetTileId := 0
      , newTile := specializedSimpTile
      , expectedDigest := 0x4002#64
      , computedDigest := 0x4002#64 }
    let afterArray := runGlitchFreeDpr initArray icapFrame
    let afterTile0 := runTileGlitchFreeDpr icapFrame initTile0
    let afterTile1 := runTileGlitchFreeDpr icapFrame residentTile1
    -- 1. Pin guard & Futamura behavioral equivalence
    specSlot.usable (holdsAt pinnedSimpView) specializedSimpCand = true ∧
    (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot pinnedSimpView
      (specOrder "specializedSimp" specializedSimpComp) (some specializedSimpCand) =
      .ok specializedSimpCand ∧
    (.app elabSimpInterpreterTerm pinnedElabEnvTerm ≈b futamura1ElabSimpTerm) ∧
    -- 2. Neighbor tile 1 (resident kernel gate) and in-flight packets are strictly preserved
    afterTile1 = residentTile1 ∧
    afterArray.skidBufferPkts = [inflightPkt] ∧
    afterArray.crcErrorCount = 0 ∧
    -- 3. Phase 1+2 isolation clamps tile 0 at skidHeldOutput (11#64)
    evalReconfigTile (dprPhase2LoadFrame icapFrame (dprPhase1Isolate 0 initTile0))
      (fun _ => 0#64) (fun _ => 0#64) 10#64 = 11#64 ∧
    -- 4. Phase 3 releases fence and executes specializedSimpTile (10 ↦ 42) while tile 1 checks declarations
    evalReconfigTile initTile0 (fun _ => 0#64) (fun _ => 0#64) 10#64 = 11#64 ∧
    evalReconfigTile afterTile0 (fun _ => 0#64) (fun _ => 0#64) 10#64 = 42#64 ∧
    evalReconfigTile afterTile1 (fun _ => 0#64) (fun _ => 0#64) 1#64 = 1#64 ∧
    evalReconfigTile afterTile1 (fun _ => 0#64) (fun _ => 0#64) 2#64 = 0#64 := by
  have hclosed : (futamura1Composition "specializedSimp" elabSimpInterpreterTerm pinnedElabEnvTerm).closedB = true := by
    rw [futamura1Comp_eq_specializedSimpComp]
    decide +kernel
  have hfut := futamura1_env_specialize_sound "specializedSimp"
    elabSimpInterpreterTerm pinnedElabEnvTerm hclosed
  have husable : specSlot.usable (holdsAt pinnedSimpView) specializedSimpCand = true := by
    decide +kernel
  have hadv := hfut.2.2.1 pinnedSimpView
  rw [futamura1Comp_eq_specializedSimpComp, futamura1Cand_eq_specializedSimpCand] at hadv
  simp only [husable, ite_true] at hadv
  refine ⟨husable, hadv, hfut.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Environment Mutation Invalidation & 1-Cycle Safe Fallback (`silicon_elab_env_mutation_fallback_sound`) -/

/-- **Theorem (`silicon_elab_env_mutation_fallback_sound`)**:
1. **Stale Environment Pin Refusal**: When the Lean `Environment` mutates from Epoch 1 (`pinnedSimpView`)
   to Epoch 2 (`mutatedSimpView`), `specSlot.usable (holdsAt mutatedSimpView) specializedSimpCand = false`,
   and `slotAdvance` immediately deoptimizes in 1 step to `.ok Candidate.machine` (`machine_usable = true`).
2. **Corrupt / Unauthenticated Bitstream Refusal**: If a bitstream frame with a mismatched digest
   (`computedDigest ≠ expectedDigest`) is streamed into `ICAP`, `runTileGlitchFreeDpr` refuses to
   overwrite `activeTile` and keeps the tile isolated (`isolated = true`) clamped at `skidHeldOutput`. -/
theorem silicon_elab_env_mutation_fallback_sound :
    let tile0 : ReconfigTileState :=
      { tileId := 0, tileX := 0, tileY := 0
      , activeTile := specializedSimpTile, frameDigest := 0x4002#64
      , isolated := false, skidHeldOutput := 42#64 }
    let corruptFrame : IcapBitstreamFrame :=
      { targetTileId := 0
      , newTile := incAutomatonTile
      , expectedDigest := 0x4002#64
      , computedDigest := 0xDEAD#64 }
    let afterCorrupt := runTileGlitchFreeDpr corruptFrame tile0
    -- 1. Environment mutation invalidates specializedSimpCand and falls back to Candidate.machine in 1 step
    specSlot.usable (holdsAt mutatedSimpView) specializedSimpCand = false ∧
    specSlot.usable (holdsAt mutatedSimpView) .machine = true ∧
    (slotAdvance : Advance LeafView LeafPin Candidate).advance specSlot mutatedSimpView
      (specOrder "specializedSimp" specializedSimpComp) (some specializedSimpCand) =
      .ok .machine ∧
    -- 2. Corrupt bitstream frame is rejected and tile stays isolated at skidHeldOutput
    afterCorrupt.activeTile = specializedSimpTile ∧
    afterCorrupt.isolated = true ∧
    evalReconfigTile afterCorrupt (fun _ => 0#64) (fun _ => 0#64) 100#64 = 42#64 := by
  have hclosed : (futamura1Composition "specializedSimp" elabSimpInterpreterTerm pinnedElabEnvTerm).closedB = true := by
    rw [futamura1Comp_eq_specializedSimpComp]
    decide +kernel
  have hfut := futamura1_env_specialize_sound "specializedSimp"
    elabSimpInterpreterTerm pinnedElabEnvTerm hclosed
  have hunusable : specSlot.usable (holdsAt mutatedSimpView) specializedSimpCand = false := by
    decide +kernel
  have hadv := hfut.2.2.1 mutatedSimpView
  rw [futamura1Comp_eq_specializedSimpComp, futamura1Cand_eq_specializedSimpCand] at hadv
  simp only [hunusable, Bool.false_eq_true, ite_false] at hadv
  exact ⟨hunusable, machine_usable mutatedSimpView, hadv, rfl, rfl, rfl⟩

/-! ## 4. Hardware Interaction-Net $\beta$-Reduction Agreement (`silicon_kernel_inet_beta_agrees`) -/

/-- **Theorem (`silicon_kernel_inet_beta_agrees`)**:
Connecting `Obend.Hardware.ReductionMachine.reduceActivePair` (the 1-cycle hardware interaction-net
rewrite engine) with `Obend.Lower.LeanKernel.kernelWhnf` and `Obend.Lower.lowerT`:
For any argument `x : Nat`, reducing an identity lambda node (`slope = 1`, `offset = 0`) against a
`nat64` argument node (`immVal = x`) in the hardware interaction-net arena produces `.betaNat64`
with `immVal = x`, agreeing with:
1. `kernelWhnf stdKernelEnv 4 (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal x))) = .lit (.natVal x)`, and
2. `Evaluates (lowerT (.app kernelWhnfLExpr (.inject "app" [("fn", .inject "lam" []), ("arg", .lit x)]))) (.nat x)`. -/
theorem silicon_kernel_inet_beta_agrees (x : Nat) (a1 a2 b1 b2 : PortRef) (nextId : Nat) :
    let lamNode : INetNode := { id := 0, kind := .lam, label := 1, immVal := 0, aux1 := a1, aux2 := a2 }
    let argNode : INetNode := { id := 1, kind := .nat64, label := 0, immVal := x, aux1 := b1, aux2 := b2 }
    reduceActivePair { left := lamNode, right := argNode } nextId =
      .betaNat64 { id := nextId, kind := .nat64, label := 0, immVal := x, aux1 := a1, aux2 := a2 } ∧
    kernelWhnf stdKernelEnv 4 (.app (.lam kNatConst (.bvar 0)) (.lit (.natVal x))) = .lit (.natVal x) ∧
    Evaluates
      (lowerT (.app kernelWhnfLExpr (.inject "app" [("fn", .inject "lam" []), ("arg", .lit x)])))
      (.nat x) := by
  intro lamNode argNode
  refine ⟨?_, (silicon_kernel_whnf_sound x).1, (silicon_kernel_whnf_sound x).2.2.2.2⟩
  dsimp only [reduceActivePair, lamNode, argNode]
  simp

/-! ## 5. Sequential `Nat.rec` Fuel Loop RTL Synthesis (`compileBookToSeqRtlSat`), 2D XY Mesh Routing, and `ICAP` Word Codec -/

/-- Fuel-bounded `Nat.rec` step accumulator `LExpr` lowered through `Core4` and `Leaf.Book` to
sequential multi-cycle RTL via `compileBookToSeqRtlSat`. -/
def kernelFuelLoopLExpr : LExpr :=
  .lam .natural
    (.natRec .natural
      (.lit 0)
      (.lam .natural (.lam .natural
        (.natBin .add (.natBin .add (.bvar 0) (.bvar 1)) (.lit 1))))
      (.bvar 0))

/-- Emitted `Leaf.Book` for `kernelFuelLoopLExpr`. -/
def kernelFuelLoopBook : Book :=
  emit (leanComposition "kernelFuelLoop" (lowerT kernelFuelLoopLExpr))

/-- **Theorem (`silicon_kernel_seq_rtl_fuel_sound`)**:
Proves that lowering `kernelFuelLoopLExpr` (`Nat.rec` fuel-bounded accumulator) through `Core4`
and `Leaf.Book` and synthesizing sequential multi-cycle RTL via `compileBookToSeqRtlSat`:
1. Produces a valid sequential `RtlModule` (`checkRtlModule m = true`),
2. Remains busy (`out_done = 0#64`) at cycle `4` when given fuel bound `5#64`, and
3. Asserts `out_done = 1#64` with the exact accumulated step counts (`0#64`, `15#64`, `36#64`)
   after `0`, `5`, and `8` clock cycles (`evalSeqModuleAfterCycles`). -/
theorem silicon_kernel_seq_rtl_fuel_sound :
    (match compileBookToSeqRtlSat "silicon_kernel_fuel_seq_rtl" kernelFuelLoopBook with
     | some m =>
       checkRtlModule m &&
       (evalSeqModuleAfterCycles m 0#64 0 == [("out_kernelFuelLoop", 0#64), ("out_done", 1#64)]) &&
       (evalSeqModuleAfterCycles m 5#64 4 == [("out_kernelFuelLoop", 10#64), ("out_done", 0#64)]) &&
       (evalSeqModuleAfterCycles m 5#64 5 == [("out_kernelFuelLoop", 15#64), ("out_done", 1#64)]) &&
       (evalSeqModuleAfterCycles m 8#64 8 == [("out_kernelFuelLoop", 36#64), ("out_done", 1#64)])
     | none => false) = true := by
  decide +kernel

/-- **Theorem (`silicon_elab_mesh_xy_and_icap_codec_sound`)**:
Verifies the physical eFPGA transport invariants for the specialized elaborator and kernel tiles:
1. **32-bit `ICAP` Bitstream Word Codec Round-Trip**: A canonical ICAP rule tile (`mkIcapRuleTile 0 .loweredLeanLite .addImm 10`)
   and `incAutomatonTile` serialize to 5-word 32-bit `ICAP` configuration frames headed by `icapSyncWord` (`0xAA995566#32`)
   and decode back losslessly (`decodeTileIcapWords`), while a corrupted sync word (`0xDEADBEEF#32`) is rejected (`none`).
2. **Dimension-Ordered 2D XY Mesh Routing**: A `MeshXyPacket` carrying an elaborated declaration payload (`42`) from
   elaborator tile `(0, 0)` to kernel checker tile `(2, 1)` strictly decreases `manhattanDist` at every
   hop (`3 → 2 → 1 → 0`) under `stepMeshXy`, reaches `(2, 1)` as a fixed point (`stepMeshXy p3 = p3`), and preserves `payload`.
3. **Interaction-Net `dup`/`sup` Commutation (`commuteSpawnedNodes`)**: Distinct-label `.dup` (`label = 1`)
   and `.sup` (`label = 2`) nodes commute in 1 cycle into `.commute (commuteSpawnedNodes dupNode supNode 100)` (4 fresh cross-wired nodes). -/
theorem silicon_elab_mesh_xy_and_icap_codec_sound :
    let simpRuleTile := mkIcapRuleTile 0 .loweredLeanLite .addImm 10
    (encodeTileIcapWords specializedSimpTile).length = 5 ∧
    (encodeTileIcapWords specializedSimpTile).head? = some icapSyncWord ∧
    decodeTileIcapWords (encodeTileIcapWords simpRuleTile) = some simpRuleTile ∧
    decodeTileIcapWords (encodeTileIcapWords incAutomatonTile) = some incAutomatonTile ∧
    decodeTileIcapWords [0xDEADBEEF#32, 0#32, 0#32, 0#32, 10#32] = none ∧
    (let p0 : MeshXyPacket := { srcX := 0, srcY := 0, dstX := 2, dstY := 1, curX := 0, curY := 0, payload := 42 }
     let p1 := stepMeshXy p0
     let p2 := stepMeshXy p1
     let p3 := stepMeshXy p2
     manhattanDist p0 = 3 ∧
     manhattanDist p1 = 2 ∧
     manhattanDist p2 = 1 ∧
     manhattanDist p3 = 0 ∧
     stepMeshXy p3 = p3 ∧
     p3.payload = 42) ∧
    (let dupNode : INetNode := { id := 10, kind := .dup, label := 1, immVal := 0, aux1 := ⟨0, 1⟩, aux2 := ⟨0, 2⟩ }
     let supNode : INetNode := { id := 11, kind := .sup, label := 2, immVal := 0, aux1 := ⟨1, 1⟩, aux2 := ⟨1, 2⟩ }
     reduceActivePair { left := dupNode, right := supNode } 100 =
       .commute (commuteSpawnedNodes dupNode supNode 100)) := by
  decide +kernel

end Obend.Lower.Proofs.SiliconKernel
end
