module
/-
# `Obend.Teeth.Extracted.HardwareCryptoZkTeeth` — Crypto, Hardware, SymbolicZk & Trailblaze Mutation Teeth

On-demand Tier-2B `#tooth` mutation suite (39 mutation witnesses) extracted from
Tier-1 `Obend` modules so `lake build Obend` elaborates pure definitions and proofs without
mutation replay overhead. Uses `import all` to preserve `LAW-M1` `.olean.private` encapsulation.
-/
public import Obend.Tactic.Tooth
import all Obend.Analysis.Equitable
import all Obend.Analysis.Flowpipe
import all Obend.Analysis.Groebner
import all Obend.Analysis.Hybrid
import all Obend.Analysis.QuantumWalk
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.TaylorModel
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Core.Brand
import all Obend.Core.Code
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Crypto.FastRing
import all Obend.Crypto.Multilinear
import all Obend.Hardware.Accelerators
import all Obend.Hardware.Compiler
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.HDL
import all Obend.Hardware.Kinematics
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.Photonics
import all Obend.Hardware.QuantumMatter
import all Obend.Hardware.ReductionMachine
import all Obend.Hardware.Types
import all Obend.Judge.Class
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.Specialize
import all Obend.Leaf.UpTo
import all Obend.Lower.ExprCAM
import all Obend.Lower.Fragment
import all Obend.Lower.LeanKernel
import all Obend.Lower.Proofs.SiliconKernel
import all Obend.Polis.BlumRam
import all Obend.Reasons
import all Obend.Reasons.UnifiedEquilibrium
import all Obend.Slot.Selection
import all Obend.SymbolicZk.CamUnifyArith
import all Obend.SymbolicZk.RankedFixpointArith
import all Obend.SymbolicZk.SemiringDatalog
import all Obend.Trailblaze.StageBInstances

public section
end

namespace Obend.Teeth.Extracted.HardwareCryptoZkTeeth
/-! ## Extracted from `Obend.Crypto.FastRing` (3 teeth) -/
section Obend_Crypto_FastRing
open Obend.Crypto Obend.Crypto.Fast Obend.Crypto.Fast.FastGoldilocksRing

#tooth checkShort_iff by mutation checkShort := fun _ _ _ => true

#tooth wrapSign_high by mutation wrapSign := fun _ _ x => x

#tooth canonicalGoldilocksOfUInt64_injective by mutation canonicalGoldilocksOfUInt64 := fun _ => some Goldilocks.zero

end Obend_Crypto_FastRing

/-! ## Extracted from `Obend.Hardware.GeometryCAM` (2 teeth) -/
section Obend_Hardware_GeometryCAM
open Obend.Hardware.GeometryCAM
open Obend.Hardware.Accelerators

/-- Broken `computeCertifiedLipschitzBox` returning a constant `0` Lipschitz bound. -/
private def computeCertifiedLipschitzBoxBroken (_B : Box3D) (_e : FRepExpr) : Nat := 0

#tooth evalFRepGradBox_lipschitz_sound by mutation
  computeCertifiedLipschitzBox := computeCertifiedLipschitzBoxBroken

/-- A wall test that ignores the growth: it accepts any box whose own points are inside `outer`. -/
private def wallLeafBroken (outer inner : FRepExpr) (_tx _ty _tz : Nat) (B : Box3D) : Bool :=
  decide (0 < (evalFRepInterval B inner).lo) || decide ((evalFRepInterval B outer).hi ≤ 0)

#tooth checkWall_sound by mutation
  wallLeaf := wallLeafBroken

end Obend_Hardware_GeometryCAM

/-! ## Extracted from `Obend.Hardware.Kinematics` (1 teeth) -/
section Obend_Hardware_Kinematics
open Obend.Hardware.Kinematics
open Obend.Hardware.GeometryCAM (ToolAxis)

/-- A post that unwinds the rotaries at cutting depth: it re-orients on the plunge feed instead of on
the rapid above the first point. -/
private def passMovesBroken (cfg : PostConfig) (p : CamPass) : List NcMove :=
  match p.pts with
  | [] => []
  | q :: rest =>
    .rapid q.1 q.2.1 cfg.clearanceZ ⟨0, 0, 1, 1⟩ :: .feed q.1 q.2.1 q.2.2 p.axis cfg.plungeFeed ::
      (rest.map fun r => NcMove.feed r.1 r.2.1 r.2.2 p.axis cfg.cutFeed)

#tooth postMoves_rotarySafe by mutation
  passMoves := passMovesBroken

end Obend_Hardware_Kinematics

/-! ## Extracted from `Obend.Hardware.OpenHypergraph` (7 teeth) -/
section Obend_Hardware_OpenHypergraph
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.HDL Obend.Hardware.Compiler

/-- Broken `FiniteFunction.converse` that produces 0 segments. -/
private def converseEmptyBug (f : FiniteFunction) : IndexedCoproduct :=
  IndexedCoproduct.fromSegments f.source []

#tooth converse_wellFormed by mutation FiniteFunction.converse := converseEmptyBug

#tooth mem_converse_segment_iff by mutation FiniteFunction.converse := converseEmptyBug

#tooth operationAdjacencyCsr_sound by mutation FiniteFunction.converse := converseEmptyBug

/-- Broken `IndexedCoproduct.flatmap` that drops all sub-segments and returns empty segments. -/
private def flatmapDropSegmentsBug (c : IndexedCoproduct) (sub : IndexedCoproduct) : IndexedCoproduct :=
  IndexedCoproduct.fromSegments sub.values.target []

#tooth flatmap_numSegments by mutation IndexedCoproduct.flatmap := flatmapDropSegmentsBug

#tooth mem_flatmap_segment_iff by mutation IndexedCoproduct.flatmap := flatmapDropSegmentsBug

#tooth operationAdjacencyCsr_sound by mutation IndexedCoproduct.flatmap := flatmapDropSegmentsBug

/-- Broken `layerHypergraphCsr` that drops all wavefront stages. -/
private def layerHypergraphCsrEmptyBug (_g : StrictOpenHypergraph) : List (List HyperEdge) := []

#tooth layerHypergraphCsr_sound_and_agrees by mutation layerHypergraphCsr := layerHypergraphCsrEmptyBug

end Obend_Hardware_OpenHypergraph

/-! ## Extracted from `Obend.Hardware.QuantumMatter` (5 teeth) -/
section Obend_Hardware_QuantumMatter
open Obend.Hardware.QuantumMatter Obend.Hardware.QuantumMatter.CliffordElem
open Obend.Hardware.Photonics
open Obend.Hardware.OpenHypergraph
open Obend.Leaf
open Obend.Slot
open Obend.Slot.World
open Obend.Core.Term
open Obend.Analysis

/-- Broken `equitableBreakingScore` that always returns `0`. -/
private def equitableBreakingScoreConstZeroBug
    (_dH : IntMatrix) (_n _r : Nat) (_part : List (List Nat)) (_Q_d : Nat → Nat → Int) : Nat := 0

#tooth breakingScore_zero_iff_equitable by mutation equitableBreakingScore := equitableBreakingScoreConstZeroBug

/-- Broken `evalDuhamelLeakageRecurrence` that omits the previous step accumulation term `opNorm * E_k`. -/
private def evalDuhamelLeakageRecurrenceDropPrevBug (opNorm epsBreak : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => epsBreak * (opNorm ^ k)

#tooth perturbative_disorder_leakage_bound by mutation evalDuhamelLeakageRecurrence := evalDuhamelLeakageRecurrenceDropPrevBug

/-- Broken `evalPlanarClements4x4` that zeroes out mode 1 in the odd layer (violating power conservation). -/
private def evalPlanarClements4x4LossyBug
    (t kappa : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let (m0, _m1, m2, m3) := evalPhotonicArray4LayerEven t kappa t kappa e0 e1 e2 e3
  (m0, ⟨0, 0⟩, m2, m3)

#tooth planarClements4x4_conserves_optical_power by mutation evalPlanarClements4x4 := evalPlanarClements4x4LossyBug

/-- Broken `quotientOpenHypergraph` that swaps cell weights $W_0$ and $W_1$. -/
private def quotientOpenHypergraphSwapWeightsBug (W0 W1 : Int) (op2 : OpticOp) : StrictOpenHypergraph :=
  let cell0 := opticFwdHyperEdges (.scale W1) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5
  let cell1 := opticFwdHyperEdges (.scale W0) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11
  mkStrictOpenHypergraph 12
    [0, 1, 6, 7]
    [3, 9]
    (reindexHyperEdges (cell0 ++ cell1))

#tooth quotientOpenHypergraph_intertwines_eval_and_adjoint by mutation quotientOpenHypergraph := quotientOpenHypergraphSwapWeightsBug

/-- Broken `QuotientHypergraphCandidate.supports` that drops all channel weight pins (`[]`). -/
private def quotientSupportsDropPinsBug : QuotientHypergraphCandidate → List LeafPin
  | _ => []

#tooth quotientHypergraph_moved_pin_blocks by mutation QuotientHypergraphCandidate.supports := quotientSupportsDropPinsBug

end Obend_Hardware_QuantumMatter

/-! ## Extracted from `Obend.Hardware.ReductionMachine` (3 teeth) -/
section Obend_Hardware_ReductionMachine
open Obend.Hardware.ReductionMachine
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Logic
open Obend.Slot
open Obend.Slot.World
open Obend.Leaf
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler

/-- Broken `stepActivePair` that allocates a dummy BRAM slot on `CON-CON` annihilation. -/
private def stepActivePairBadAlloc (st : InteractionNetPeState) (_pair : ActivePair) : InteractionNetPeState :=
  { st with allocCount := st.allocCount + 1 }

#tooth interaction_net_annihilation_zero_alloc_and_involutive by mutation stepActivePair := stepActivePairBadAlloc

/-- Broken `stepActivePair` that spuriously increments `commutationCount` even on affine pairs. -/
private def stepActivePairSpuriousComm (st : InteractionNetPeState) (_pair : ActivePair) : InteractionNetPeState :=
  { st with commutationCount := st.commutationCount + 1 }

#tooth affine_bendtt_net_zero_commutations by mutation stepActivePair := stepActivePairSpuriousComm

/-- Broken `mkBookNocRequest` that routes to `(0, 0)` instead of `(1, 1)` (bypassing multi-hop XY routing). -/
private def mkBookNocRequestLocal (targetSlot : Nat) (argVal : BitVec 64) (flitId : Nat) : NocFlit where
  flitId     := flitId
  kind       := .request
  srcX       := 0
  srcY       := 0
  curX       := 0
  curY       := 0
  dstX       := 0
  dstY       := 0
  targetSlot := targetSlot
  payload    := argVal

#tooth nocFabric_simulates_book by mutation mkBookNocRequest := mkBookNocRequestLocal

end Obend_Hardware_ReductionMachine

/-! ## Extracted from `Obend.SymbolicZk.CamUnifyArith` (4 teeth) -/
section Obend_SymbolicZk_CamUnifyArith
open Obend.SymbolicZk.Cam
open Obend.Lower.ExprCAM Obend.Lower Obend.Lower.Inductive Obend.Lower.LeanKernel

#tooth topologicalHeight_forbids_cyclic_mvar by mutation strictHeight := fun a b => decide (b ≤ a)

#tooth checkProofForestExec_sound by mutation strictHeight := fun a b => decide (b ≤ a)

#tooth linmem_sound by mutation bornBefore := fun _ => true

#tooth ghostCycle_rejected_by_linMem by mutation bornBefore := fun _ => true

end Obend_SymbolicZk_CamUnifyArith

/-! ## Extracted from `Obend.SymbolicZk.RankedFixpointArith` (8 teeth) -/
section Obend_SymbolicZk_RankedFixpointArith
open Obend.SymbolicZk.Ranked
open Obend.Reasons

#tooth rankedGamma_sound by mutation earlier := fun a b => a ≤ b

#tooth rankedWFS_sound by mutation earlier := fun a b => a ≤ b

#tooth rankedWFS_sound by mutation noLater := fun _ _ => True

#tooth rankedWFS_sound by mutation lexEarlier := fun s r s' r' => s ≤ s' ∨ r ≤ r'

#tooth checkRankedWFS_sound by mutation earlier := fun a b => a ≤ b

#tooth quadraticFiresGate_sound by mutation quadraticFiresGate := fun _ _ _ _ => true

#tooth evenCycle_cheating_fixpoint_rejected by mutation earlier := fun a b => a ≤ b

#tooth evenCycle_cheating_fixpoint_rejected by mutation noLater := fun _ _ => True

end Obend_SymbolicZk_RankedFixpointArith

/-! ## Extracted from `Obend.SymbolicZk.SemiringDatalog` (3 teeth) -/
section Obend_SymbolicZk_SemiringDatalog
open Obend.SymbolicZk.Datalog
open Std
open ProvenanceSemiringOps

#tooth sumRows_merge by mutation mergeRows := fun xs _ => xs

#tooth buildSorted_sum by mutation buildSorted := fun _ => ⟨#[]⟩

#tooth gap_absent by mutation verifyGapCert := fun _ _ _ => true

end Obend_SymbolicZk_SemiringDatalog

/-! ## Extracted from `Obend.Trailblaze.LeanFpga` (2 teeth) -/
section Obend_Trailblaze_LeanFpga
open Obend.Trailblaze.LeanFpga Obend.Trailblaze.LeanFpga.FaceIdeal3
open Obend.Trailblaze

-- Mutation guard: replacing `FaceIdeal3.varEq1` with Boolean complementation `~~~(varEq0 v).mask`
-- collapses `∂𝕀 = 𝕀` and is caught by `FaceIdeal3.varEq0_join_varEq1_ne_top`.
#tooth FaceIdeal3.varEq0_join_varEq1_ne_top by
  mutation FaceIdeal3.varEq1 := fun v => ⟨~~~(FaceIdeal3.varEq0 v).mask⟩

/-- Broken `checkNetPortLinearity` mutant that omits the `countPort p eps == 1` degree-1 check. -/
private def checkNetPortLinearityMutantSkipDegree (net : DeltaNet) : Bool :=
  let decls := declaredPorts net
  let eps := wireEndpoints net.wires
  !net.netName.isEmpty &&
  checkDistinctDeltaNodeIds net.nodes &&
  decls.contains net.rootPort &&
  (countPort net.rootPort eps == 0) &&
  net.wires.all (fun w => w.lhs != w.rhs)

#tooth checkNetPortLinearity_sound by mutation checkNetPortLinearity := checkNetPortLinearityMutantSkipDegree

end Obend_Trailblaze_LeanFpga

/-! ## Extracted from `Obend.Trailblaze.PolisBlum` (1 teeth) -/
section Obend_Trailblaze_PolisBlum
open Obend.Trailblaze.Polis

/-- Broken `checkLocalRwStep` mutant that forgets to check `op.val == expected` on reads. -/
private def checkLocalRwStepMutantIgnoreReadVal (curAddr : Option Nat) (lastVal : BitVec 64) : List MemOp → Bool
  | [] => true
  | op :: rest =>
    if op.isWrite then
      checkLocalRwStepMutantIgnoreReadVal (some op.addr) op.val rest
    else
      let expected := if curAddr == some op.addr then lastVal else 0#64
      checkLocalRwStepMutantIgnoreReadVal (some op.addr) expected rest

#tooth blum_write_then_read_sound by mutation checkLocalRwStep := checkLocalRwStepMutantIgnoreReadVal

end Obend_Trailblaze_PolisBlum
end Obend.Teeth.Extracted.HardwareCryptoZkTeeth
