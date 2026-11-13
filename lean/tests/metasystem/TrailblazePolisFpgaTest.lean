import Obend.Trailblaze.StageBInstances
import Obend.AssertAxioms
import Obend.Tactic.Tooth

/-!
# `tests/metasystem/TrailblazePolisFpgaTest.lean` — Metasystem Regression & Verification Suite (Trailblazer T1: Organs O3 & O7)

Verifies end-to-end kernel elaboration, computational execution, named refusals, non-empty `Judge`
fragments, `#tooth` mutation sensitivity, and `#assert_axioms_tree` purity (`0 sorryAx`, `0` custom
`axiom`s, `0 native_decide`) across:
1. `Obend.Trailblaze.Obligations`:
   - `ObligationMeta`, `ObligationManifest`, `SilverWorkflow`, `SilverSound`, `SilverWorkflow.prod`,
   - `SilverWorkflow.toJudge` with non-empty `Fragment` (`∃ w, judge.Fragment w`) and genuine
     refutation (`judge.refutes _ = true`, `SilverWorkflow.rejected_refutes_spec`).
2. `Obend.Trailblaze.Polis`:
   - `PCA` (`S`-combinator saturation `S K K x = x`) & `PairedPCA`,
   - Choice-free `Assembly.trackedPullback` (`pbFst`, `pbSnd`, `trackedPullback_comm`, `pbLift`)
     and unconditional `regularCoveragePullbackStable`,
   - $O(N)$ `Array MemOp` single-pass checks + $O(N \log N)$ `sortMemOpsByAddrTime` +
     `verifyBlumMemoryFast_eq_verifyBlumMemory` + unconditional read/write `blumPermutationComplete`,
   - Unconditional `checkMicrokitIsolation_implies_capDlNonInterfering`, constructive
     `commitSaltedBid_binding`, `apex_polis_deos_turn_safe`, and `silverPolisSmoke`.
3. `Obend.Trailblaze.LeanFpga`:
   - `FaceIdeal3` (`BitVec 27` over ternary 3-cube $\{0, 1, *\}^3$), lattice & partial-order laws,
     unconditional `siliconSimpMeetImplies`, `varEq0_meet_varEq1`, and **`varEq0_join_varEq1_ne_top`** (`∂𝕀 ≠ 𝕀`),
   - Single-tile & lossless 27-bit dual-tile `FABulous` bitstream codecs and 27-point `evalDualFabulousCofib`,
   - Recursive `LeafExpr` / multi-def `Obend.Leaf.Book → DeltaNet` compiler (`compileLeafExprToDeltaNet`,
     `lowerLeafBookToDeltaNet`), `apex_lean_fpga_rung2_to_rung5`, and `silverLeanFpgaSmoke`.
-/

namespace Obend.Tests.TrailblazePolisFpgaTest

open Obend.Trailblaze
open Obend.Trailblaze.Polis
open Obend.Trailblaze.LeanFpga

-- ============================================================================
-- 0. Whole-Tree Axiom Purity Audit (`0 sorryAx`, `0` custom `axiom`s)
-- ============================================================================

#assert_axioms_tree

-- ============================================================================
-- 1. `Obligations`, Non-Empty `Judge.Fragment` & Genuine Refutation
-- ============================================================================

#check @silverWorkflow_satisfies_silverSound
#check @SilverWorkflow.prod
#check @SilverWorkflow.toJudge
#check @SilverWorkflow.admitted_in_judge_fragment
#check @SilverWorkflow.rejected_refutes_spec

instance jointPolisFpgaWorkflow : SilverWorkflow (ConcretePolisTurn × LeanFpgaTurn) :=
  SilverWorkflow.prod ConcretePolisTurn LeanFpgaTurn

@[instance_reducible] def polisJudge : Obend.Judge ConcretePolisTurn Unit :=
  SilverWorkflow.toJudge ConcretePolisTurn

@[instance_reducible] def fpgaJudge : Obend.Judge LeanFpgaTurn Unit :=
  SilverWorkflow.toJudge LeanFpgaTurn

@[instance_reducible] def jointJudge : Obend.Judge (ConcretePolisTurn × LeanFpgaTurn) Unit :=
  SilverWorkflow.toJudge (ConcretePolisTurn × LeanFpgaTurn)

-- Genuinely inhabited `Judge.Fragment` across O3, O7, and product `O3 × O7` workflows
example : ∃ w : ConcretePolisTurn, polisJudge.Fragment w :=
  ⟨sampleValidPolisTurn, SilverWorkflow.admitted_in_judge_fragment sampleValidPolisTurn (by decide)⟩

example : ∃ t : LeanFpgaTurn, fpgaJudge.Fragment t :=
  ⟨sampleValidFpgaTurn, SilverWorkflow.admitted_in_judge_fragment sampleValidFpgaTurn rfl⟩

example : ∃ p : ConcretePolisTurn × LeanFpgaTurn, jointJudge.Fragment p :=
  ⟨(sampleValidPolisTurn, sampleValidFpgaTurn),
   SilverWorkflow.admitted_in_judge_fragment (sampleValidPolisTurn, sampleValidFpgaTurn) (by decide)⟩

-- `refutes` returns `true` (not `false`) and rejected `CompleteOn` turns genuinely refute `Spec`
example : polisJudge.refutes "refused: foc-hil-watchdog-leak" = true := rfl
example : fpgaJudge.refutes "refused: delta-net-port-nonlinearity" = true := rfl

example : ¬ SilverWorkflow.Spec plantedWatchdogLeakTurn :=
  SilverWorkflow.rejected_refutes_spec plantedWatchdogLeakTurn (by decide) rfl

example : ¬ SilverWorkflow.Spec plantedForgedBlumTurn :=
  SilverWorkflow.rejected_refutes_spec plantedForgedBlumTurn (by decide) rfl

example : ¬ SilverWorkflow.Spec plantedNonlinearNetTurn :=
  SilverWorkflow.rejected_refutes_spec plantedNonlinearNetTurn rfl rfl

example : jointPolisFpgaWorkflow.runValid (sampleValidPolisTurn, sampleValidFpgaTurn) = true := by decide
example : jointPolisFpgaWorkflow.refuseInvalid (sampleValidPolisTurn, sampleValidFpgaTurn) = none := by decide
example :
    jointPolisFpgaWorkflow.refuseInvalid (plantedWatchdogLeakTurn, sampleValidFpgaTurn) =
      some "refused: foc-hil-watchdog-leak" := by decide
example :
    jointPolisFpgaWorkflow.refuseInvalid (sampleValidPolisTurn, plantedNonlinearNetTurn) =
      some "refused: delta-net-port-nonlinearity" := by decide

-- ============================================================================
-- 2. Organ O3 (`Polis`): `PairedPCA`, `Assembly.trackedPullback`, Fast Blum `UMem` & `seL4`
-- ============================================================================

#check @evalDeosCapApplyFuel_s2
#check @TrackedMorphism.id
#check @TrackedMorphism.comp
#check @TrackedMorphism.id_comp
#check @TrackedMorphism.comp_id
#check @TrackedMorphism.comp_assoc
#check @Assembly.trackedPullback
#check @Assembly.pbFst
#check @Assembly.pbSnd
#check @Assembly.trackedPullback_comm
#check @Assembly.pbLift
#check @Assembly.pbFst_comp_pbLift_map
#check @Assembly.pbSnd_comp_pbLift_map
#check @Assembly.pbLift_map_unique
#check @regularCoveragePullbackStable
#check @checkChronologicalLogExec_eq_spec
#check @checkAddrTimeSortedExec_eq_spec
#check @checkLocalReadWriteConsistencyExec_eq_spec
#check @sortMemOpsByAddrTime_perm
#check @sortMemOpsByAddrTime_sorted
#check @sortMemOpsByAddrTime_eq_implies_perm_and_counts
#check @verifyBlumMemoryFast_eq_verifyBlumMemory
#check @blumPermutationComplete
#check @blum_write_then_read_sound
#check @verifyBlumMemory_sound
#check @checkMicrokitIsolation_sound
#check @checkMicrokitIsolation_implies_capDlNonInterfering
#check @unpack_pack_saltedBidPreimage
#check @commitSaltedBid_binding
#check @apex_polis_deos_turn_safe
#check @polisSessionStep_skip_implies_violation
#check @polisSessionStep_complete
#check @apex_polis_deos_trace_safe

-- `S`-combinator saturation (`S K K x = x`) and `PairedPCA` projections execute directly
example : evalDeosCapApply (.s2 .k .k) (.capToken 5 1 99) = some (.capToken 5 1 99) := rfl
example : evalDeosCapApply .fst (.pair (.capToken 1 1 10) (.settledSeat 2 20)) = some (.capToken 1 1 10) := rfl
example : evalDeosCapApply .snd (.pair (.capToken 1 1 10) (.settledSeat 2 20)) = some (.settledSeat 2 20) := rfl

-- Choice-free `TrackedMorphism` composition & concrete `Assembly.trackedPullback` over `deosCapPairedPCA`
def doubleHopMorphism : TrackedMorphism custodyAssembly settledSeatAssembly :=
  ((TrackedMorphism.id settledSeatAssembly).comp (clearCustodyToSeat 500)).comp
    (TrackedMorphism.id custodyAssembly)

example : doubleHopMorphism.tracker (.capToken 7 1 42) = some (.settledSeat 7 542) := rfl
example : doubleHopMorphism.tracker (.capToken 7 0 42) = none := rfl

def seatPullback : Assembly deosCapPairedPCA.toPCA :=
  @Assembly.trackedPullback deosCapPairedPCA custodyAssembly custodyAssembly settledSeatAssembly
    (clearCustodyToSeat 100) (clearCustodyToSeat 100)

def diagonalSeatLift : TrackedMorphism custodyAssembly seatPullback :=
  @Assembly.pbLift deosCapPairedPCA custodyAssembly custodyAssembly custodyAssembly settledSeatAssembly
    (clearCustodyToSeat 100) (clearCustodyToSeat 100)
    (TrackedMorphism.id custodyAssembly) (TrackedMorphism.id custodyAssembly)
    (fun _ => rfl)

example :
    diagonalSeatLift.tracker (.capToken 4 1 12) =
      some (.pair (.capToken 4 1 12) (.capToken 4 1 12)) := rfl

example :
    ((@Assembly.pbFst deosCapPairedPCA _ _ _ (clearCustodyToSeat 100) (clearCustodyToSeat 100)).comp
      diagonalSeatLift).tracker (.capToken 4 1 12) =
      some (.capToken 4 1 12) := rfl

-- $O(N \log N)$ Blum `UMem` `sortMemOpsByAddrTime`, `verifyBlumMemoryFast`, and unconditional R/W completeness
#guard verifyBlumMemoryFast sampleOnlineMem.toArray sampleOfflineSortedMem.toArray == true
#guard verifyBlumMemory sampleOnlineMem sampleOfflineSortedMem == true
#guard verifyBlumMemoryFast plantedForgedBlumTurn.onlineMem.toArray plantedForgedBlumTurn.offlineSortedMem.toArray == false
#guard verifyBlumMemory sampleOfflineSortedMem sampleOfflineSortedMem == false

example :
    verifyBlumMemory sampleOnlineMem (sortMemOpsByAddrTime sampleOnlineMem) = true ∧
    verifyBlumMemoryFast sampleOnlineMem.toArray (sortMemOpsByAddrTime sampleOnlineMem).toArray = true ∧
    ∃ offline : List MemOp, verifyBlumMemory sampleOnlineMem offline = true :=
  blumPermutationComplete sampleOnlineMem (by decide)

-- `seL4` Microkit `Sel4CapDlNonInterfering` refinement & salted commitment binding
example : Sel4CapDlNonInterfering sampleValidPartition :=
  checkMicrokitIsolation_implies_capDlNonInterfering sampleValidPartition (by decide)

example : refuseMicrokitIsolation plantedWatchdogLeakTurn.partition = some "refused: foc-hil-watchdog-leak" := by decide
example : refuseMicrokitIsolation plantedSharedMmioTurn.partition = some "refused: shared-writable-mmio" := by decide
example : refuseMicrokitIsolation plantedCyclicCapTurn.partition = some "refused: cyclic-untyped-cap-authority" := by decide

def sampleOpeningA : SaltedBidOpening := ⟨7#64, 500#64, 0xDEAD_BEEF_CAFE_F00D#128⟩
def sampleOpeningB : SaltedBidOpening := ⟨7#64, 900#64, 0xDEAD_BEEF_CAFE_F00D#128⟩

example : unpackSaltedBidPreimage (packSaltedBidPreimage sampleOpeningA) = sampleOpeningA :=
  unpack_pack_saltedBidPreimage sampleOpeningA

example : packSaltedBidPreimage sampleOpeningA ≠ packSaltedBidPreimage sampleOpeningB := by decide

-- Stateful multi-turn `ValidTrace`, capability anti-replay, `Mandate` budget & `UMem` horizon checks
example :
    ValidTrace sampleInitSessionState sampleValidPolisTrace
      { revokedCodes  := [.capToken 3 1 40, .capToken 3 1 25, .capToken 3 1 9]
      , mandateBudget := 20
      , lastTimestamp := 12 } := by
  unfold ValidTrace
  decide

example :
    checkChronologicalLog (concatTraceOnlineMem sampleValidPolisTrace) = true := by decide

example :
    (match stepPolisSession sampleInitSessionState sampleValidPolisTurn with
     | some st₁ => refusePolisSessionStep st₁ sampleValidPolisTurn
     | none => none) = some "refused: revoked-or-replayed-cap" := by decide

example :
    refusePolisSessionStep { sampleInitSessionState with mandateBudget := 3 } sampleValidPolisTurn =
      some "refused: mandate-budget-exhausted" := by decide

example :
    refusePolisSessionStep { sampleInitSessionState with lastTimestamp := 5 } sampleValidPolisTurn =
      some "refused: umem-timestamp-regression" := by decide

-- End-to-end Organ O3 Silver smoke witness
example : silverPolisSmoke = true := by decide

-- ============================================================================
-- 3. Organ O7 (`LeanFpga`): `FaceIdeal3` (`∂𝕀 ≠ 𝕀`), Recursive `Leaf → DeltaNet` & Dual `FABulous`
-- ============================================================================

#check @FaceIdeal3.meet_comm
#check @FaceIdeal3.meet_assoc
#check @FaceIdeal3.join_distrib_meet
#check @FaceIdeal3.meet_distrib_join
#check @FaceIdeal3.implies_refl
#check @FaceIdeal3.implies_trans
#check @FaceIdeal3.implies_antisymm
#check @FaceIdeal3.siliconSimpMeetImplies
#check @FaceIdeal3.evalTernaryPoint_varEq0
#check @FaceIdeal3.evalTernaryPoint_varEq1
#check @FaceIdeal3.varEq0_meet_varEq1
#check @FaceIdeal3.varEq0_join_varEq1_ne_top
#check @lowerTermToLeafExpr
#check @compileLeafExprToDeltaNet
#check @lowerLeafBookToDeltaNet
#check @lowerLeafBookMemberToDeltaNet
#check @checkNetPortLinearity_sound
#check @decode_encode_fabulousFrame
#check @encode_decode_fabulousFrame
#check @decode_encode_dualFabulousFrames
#check @encode_decode_dualFabulousFrames
#check @extract_compile_faceIdeal
#check @evalDualFabulousCofib_eq_evalTernaryPoint
#check @dpr_isolated_clamps_output
#check @apex_lean_fpga_rung2_to_rung5

-- `FaceIdeal3` (`BitVec 27`) non-collapse of the cubical boundary (`∂𝕀 ≠ 𝕀` at `interiorPt = (2, 2, 2)`)
example : ∀ v : Fin 3, (FaceIdeal3.varEq0 v).meet (FaceIdeal3.varEq1 v) = FaceIdeal3.bot :=
  FaceIdeal3.varEq0_meet_varEq1

example : ∀ v : Fin 3, (FaceIdeal3.varEq0 v).join (FaceIdeal3.varEq1 v) ≠ FaceIdeal3.top :=
  FaceIdeal3.varEq0_join_varEq1_ne_top

example :
    ((FaceIdeal3.varEq0 ⟨1, by decide⟩).join (FaceIdeal3.varEq1 ⟨1, by decide⟩)).evalTernaryPoint
      FaceIdeal3.interiorPt = false := rfl

example : FaceIdeal3.top.evalTernaryPoint FaceIdeal3.interiorPt = true := rfl

-- Recursive `Leaf.Book` / `LeafExpr → DeltaNet` compilation & Salvadori sharing/erasure checks
#guard (emitHvmNetText sampleLinearDeltaNet).startsWith "@cofib_face_dispatch = "
#guard sampleLinearDeltaNet.nodes.length > 20
#guard checkNetPortLinearity sampleLinearDeltaNet == true
#guard checkNetPortLinearity sampleSharedLetNet == true
#guard checkNetPortLinearity sampleActiveBetaRedexNet == true
#guard (activePrincipalRedexes sampleActiveBetaRedexNet).length == 1
#guard checkNetPortLinearity plantedNonlinearNetTurn.deltaNet == false

-- Single-tile & dual-tile `FABulous` bitstream round-trip + 27-point ternary evaluation
def sampleSeqTile : FabulousTileConfig where
  lut4Truth := 0xCAFE#16
  ffEnable  := true
  pipMux    := ⟨6, by decide⟩

example : decodeBitstreamFrame (encodeBitstreamFrame sampleSeqTile) = sampleSeqTile := rfl
example : checkCanonicalFrame32 (encodeBitstreamFrame sampleSeqTile) = true := rfl
example :
    evalFabulousTile sampleSeqTile 0b0001#4 false (fun i => i.val == 6) =
      { belOut := false, nextFf := true, pipRouted := true } := rfl

def sampleDualTiles : FabulousDualTileConfig :=
  compileFaceIdealToDualTiles
    ((FaceIdeal3.varEq0 ⟨0, by decide⟩).meet (FaceIdeal3.varEq1 ⟨2, by decide⟩))
    ⟨2, by decide⟩ ⟨7, by decide⟩

example :
    decodeDualBitstreamFrames (encodeDualBitstreamFrames sampleDualTiles) = sampleDualTiles :=
  decode_encode_dualFabulousFrames sampleDualTiles

example :
    ∀ pt : TernaryPt3,
      evalDualFabulousCofib sampleDualTiles pt false false (fun _ => false) (fun _ => false) =
        ((FaceIdeal3.varEq0 ⟨0, by decide⟩).meet (FaceIdeal3.varEq1 ⟨2, by decide⟩)).evalTernaryPoint pt := by
  intro pt
  exact evalDualFabulousCofib_eq_evalTernaryPoint _ _ _ pt false false _ _

-- End-to-end Organ O7 Silver smoke witness
example : silverLeanFpgaSmoke = true := rfl

example : internSymbol [.symbol "x", .symbol "y"] (.symbol "x") ≠
    internSymbol [.symbol "x", .symbol "y"] (.symbol "y") := by decide
example : deltaTagBytes (.literal 32767) ≠ deltaTagBytes (.opcode 0) := by decide
example : deltaNetBytes (compileLeafExprToDeltaNet "symbol" (.proj (.symbol "x") (.lit 0))) ≠
    deltaNetBytes (compileLeafExprToDeltaNet "symbol" (.proj (.symbol "y") (.lit 0))) := by decide
#tooth internSymbol_injective by
  mutation internSymbol := fun _ _ => 0

def twoHopRoute (source : Nat) : PipRoute :=
  ⟨source, [⟨Array.replicate 8 source, 0, source + 1⟩,
    ⟨Array.replicate 8 (source + 1), 7, source + 2⟩]⟩
example : checkMultiNetPipDisjoint [twoHopRoute 0, twoHopRoute 3] = true := by decide
example : checkMultiNetPipDisjoint [twoHopRoute 0, twoHopRoute 1] = false := by decide
example : evalPipRoute (fun wire => wire == 3) (twoHopRoute 0) 2 = false ∧
    evalPipRoute (fun wire => wire == 3) (twoHopRoute 3) 5 = true := by decide
#tooth multiNetPip_routing_sound by
  mutation checkMultiNetPipDisjoint := fun _ => true

def literalMemberBook : Obend.Leaf.Book := ⟨[.static "answer" (.nat 42)]⟩
def memberReductionTrace : List (Nat × Nat) := [(7, 6), (8, 3), (8, 4), (3, 5)]
def reducedMemberNet : DeltaNet :=
  (runDeltaReductions (lowerLeafBookMemberToDeltaNet "member" literalMemberBook "answer")
    memberReductionTrace).getD (lowerLeafBookMemberToDeltaNet "member" literalMemberBook "answer")
example : runDeltaReductions (lowerLeafBookMemberToDeltaNet "member" literalMemberBook "answer")
    memberReductionTrace = some reducedMemberNet := by decide
example : checkDeltaNormalForm reducedMemberNet 42 = true := by decide
example : checkDeltaNormalForm reducedMemberNet 43 = false := by decide
example : DeltaNetSteps (lowerLeafBookMemberToDeltaNet "member" literalMemberBook "answer") reducedMemberNet :=
  runDeltaReductions_sound _ _ _ (by decide)
#tooth Obend.Trailblaze.StageB.stageB_leaf_book_deltanet_normal_form by
  mutation checkDeltaNormalForm := fun _ _ => true
#tooth lowerTermToLeafExpr_split_field_sensitive by
  mutation stringToDeltaTag := fun _ => .symbol ""

end Obend.Tests.TrailblazePolisFpgaTest
