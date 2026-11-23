module
/-
# `Obend.Teeth.Extracted.AppsTeeth` — Apps Mutation Teeth

On-demand Tier-2B `#tooth` mutation suite (4 mutation witnesses) extracted from
`Obend.Apps` modules so `Obend.Apps.*` elaborates definitions and proofs without
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
import all Obend.Apps.SovereignDrex
import all Obend.Core.Digest
import all Obend.Receipt.Merkle
import all Obend.AssertCompiled
import all Obend.Consensus.Epistemic
import all Obend.Consensus.Finality
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
import all Obend.Consensus.SimplexTrace
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Elab.AutoCert
import all Obend.Elab.Workbook
import all Obend.Equiv.Clairvoyant
import all Obend.Fold.Collapse
import all Obend.Hardware.GeometryCAM
import all Obend.Hardware.HDL
import all Obend.Hardware.Kinematics
import all Obend.Hardware.OpenHypergraph
import all Obend.Hardware.OpenUSD
import all Obend.Hardware.Process
import all Obend.Hardware.QuantumMatter
import all Obend.Hardware.Silicon
import all Obend.Hardware.Compiler
import all Obend.Hardware.Synth
import all Obend.Hardware.Types
import all Obend.Judge.AutomataConfinement
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Netting
import all Obend.Judge.TranscriptPolicy
import all Obend.Law
import all Obend.Leaf.Emit
import all Obend.Leaf.Flatten
import all Obend.Leaf.Served
import all Obend.Leaf.Specialize
import all Obend.Leaf.Static
import all Obend.Leaf.UpTo
import all Obend.Ledger.Floors
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Rewrite
import all Obend.Lower.Fragment
import all Obend.Lower.Proofs.Book
import all Obend.Lower.Reflect
import all Obend.Lower.Transport
import all Obend.Run.Durable
import all Obend.Spec.Capture
import all Obend.Spec.CrossPackage
import all Obend.Spec.Elaborate
import all Obend.Spec.FrontEnd
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.Parse
import all Obend.Spec.Sha256
import all Obend.Spec.Syntax
import all Obend.Teeth.Hardware.CliffordKernel
import all Obend.Vault.CheckedCarry
import all Obend.Vault.Escrow
import all Obend.Vault.Hyperedge
import all Obend.Vault.IrreversibleOutbox
import all Obend.Vault.Mandate
import all Obend.Vault.Projection
import all Obend.Vault.Replay
import all Obend.Vault.UnifiedDeos

public section
end

namespace Obend.Teeth.Extracted.AppsTeeth
/-! ## Extracted from `Obend.Apps.SovereignDrex` (2 teeth) -/
section Obend_Apps_SovereignDrex
open Obend.Apps.SovereignDrex
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Lower
open Obend.Slot
open Obend.Slot.Protocol
open Obend.Run.Control
open Obend.Run.Shared
open Obend.Run.Durable
open Obend.Fold.Collapse
open Obend.Ledger
open Obend.Judge
open Obend.Vault
open Obend.Vault.CheckedCarry
open Obend.Vault.UnifiedDeos
open Obend.Consensus.Simplex
open Obend.Consensus.SimplexProtocol
open Obend.Consensus.SimplexTrace
open Obend.Consensus.Finality
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Compiler

private def brokenDrexRtlModule : RtlModule :=
  { name := "sovereign_drex_batch_top"
  , inputNames := ["in_lot_count"]
  , wires := []
  , regs := []
  , outputs := [{ name := "out_turn_admitted", expr := .const 1#64 }] }

#tooth sovereignDrexBatchTopRtlModule_epoch_replay_refused by mutation
  sovereignDrexBatchTopRtlModule := brokenDrexRtlModule

private def brokenDrexCommittee4 : List Nat := [0, 1, 2, 3, 4, 5]

#tooth sovereignDrex_engine_and_bft_finality_sound by mutation
  drexCommittee4 := brokenDrexCommittee4

/-! ### Gate `G12` (`S1–S4`) Mutation Teeth & Adversarial Counterexamples -/

-- S1 Tooth 1: Disabling Simplex `n - f` `FinCert` + tip check allows unfinalized fork capture (`S1`).
#tooth auditL1SettlementBatch_sound by mutation
  checkSettlementFinCert := fun _ _ _ _ => true

-- S1 Tooth 2: Truncating `2 × UInt128` root checks to only the high 128-bit limb breaks lossless 256-bit binding.
#tooth DigestLimbs2x128.checkLimbsEq_iff by mutation
  DigestLimbs2x128.checkLimbsEq := fun a b => a.hi == b.hi

-- S1 Tooth 3: Disabling `IrreversibleOutbox` `effectsRoot` verification breaks `auditL1SettlementBatch_sound`.
#tooth auditL1SettlementBatch_sound by mutation
  checkSettlementEffectsRoot := fun _ _ _ _ => true

-- S1 Counterexample (`n = 5, f = 1`): Legacy `2f + 1 = 3` votes fail `n - f = 4` quorum and are rejected!
theorem s1_counterexample_n5_f1_legacy_2f_plus_1_fork_rejected
    (H : Obend.Digest.HashBytes.Hash) (st : L1SettlementState)
    (b : L1SettlementBatch) (tip : Nat)
    (hForkCert : b.finCert = ⟨1, [.block 1 tip], [0, 1, 2]⟩) :
    let sentLegacy3 : Sent :=
      [ ⟨0, 1, .finalize, .block [.block 1 tip]⟩
      , ⟨1, 1, .finalize, .block [.block 1 tip]⟩
      , ⟨2, 1, .finalize, .block [.block 1 tip]⟩ ]
    stepL1SettlementBatch drexProtocol5 H sentLegacy3 st b = none := by
  intro sentLegacy3
  apply unfinalized_fork_rejected
  rw [hForkCert]
  simp [drexProtocol5, FinCert.checks, Protocol.quorum]

-- S2 Tooth: Collapsing `"dregg-pool-unlock-v2"` and `"dregg-escrow-release-v2"` onto one shared tag
-- (modeling `solana-lock` `processor.rs:409,740` `"dregg-solana-unlock-v1"` vault drain) is kernel-rejected!
#tooth poolUnlock_ne_escrowRelease_preimage by mutation
  L1VaultInstructionKind.domainTagBytes := fun _ => dreggPoolUnlockV2Tag

#tooth encodeL1InstructionPreimage_injective by mutation
  L1VaultInstructionKind.domainTagBytes := fun _ => dreggPoolUnlockV2Tag

-- S3 Tooth 1: Omitting `now ≤ tRelease` on release (modeling `DreggVault` / `cosmos-lock` / `solana-lock`
-- post-deadline release race) breaks `release_and_refund_mutually_exclusive`!
#tooth release_and_refund_mutually_exclusive by mutation
  checkReleaseWindow := fun _ _ => true

-- S3 Tooth 2: Collapsing `deltaFinality > 0` staggered timeout window to `tRelease ≤ now` (boundary overlap
-- at `now = tRelease`) breaks `release_and_refund_mutually_exclusive`!
#tooth release_and_refund_mutually_exclusive by mutation
  checkTimeoutRefundWindow := fun now tRelease _ => decide (tRelease ≤ now)

-- S4 Tooth 1: Collapsing `0x00` leaf tag onto `0x01` internal node tag enables 64B leaf/branch splices
-- and is kernel-rejected!
#tooth taggedLeaf_ne_taggedInternal_preimage by mutation
  merkleLeafTagByte := 0x01

-- S4 Tooth 2: Omitting `leafIndex < treeSize` bound breaks `verifyTaggedMerkleProof256_sound_or_collision`!
#tooth verifyTaggedMerkleProof256_sound_or_collision by mutation
  checkLeafIndexInBounds := fun _ _ => true

-- S4 Counterexample: Untagged 64-byte Merkle verifier accepts `left32 ‖ right32` as a depth-0 leaf
-- for EVERY hash `H`, whereas `verifyTaggedMerkleProof256` unconditionally rejects it (`= false`)!
private def untaggedNodeHash (H : Obend.Digest.HashBytes.Hash)
    (l r : Obend.Core.Digest.Digest256) : Obend.Core.Digest.Digest256 :=
  Obend.Receipt.Merkle.hashBytes256 H (spliced64Payload l r)

private def untaggedLeafVerify (H : Obend.Digest.HashBytes.Hash)
    (payload : List UInt8) (expectedRoot : Obend.Core.Digest.Digest256) : Bool :=
  Obend.Receipt.Merkle.hashBytes256 H payload == expectedRoot

theorem s4_counterexample_untagged_64byte_splice_vs_tagged_refusal
    (H : Obend.Digest.HashBytes.Hash)
    (p0 p1 : List UInt8) :
    let leaves := [p0, p1]
    let l0 := computeTaggedSubtree256 H 0 [p0]
    let l1 := computeTaggedSubtree256 H 1 [p1]
    let pay64 := spliced64Payload l0 l1
    pay64.length = 64 ∧
    untaggedLeafVerify H pay64 (untaggedNodeHash H l0 l1) = true ∧
    verifyTaggedMerkleProof256 H
      { treeSize := 2, leafIndex := 0, payload := pay64, tree := .openedLeaf 0 0#256 pay64 }
      (computeTaggedMerkleRoot256 H leaves) = false := by
  refine ⟨spliced64Payload_length _ _, ?_, ?_⟩
  · simp [untaggedLeafVerify, untaggedNodeHash]
  · exact (taggedMerkle_refutes_64byte_splice H [p0, p1] (Nat.le_refl 2) 0 _ _).1

end Obend_Apps_SovereignDrex
end Obend.Teeth.Extracted.AppsTeeth
