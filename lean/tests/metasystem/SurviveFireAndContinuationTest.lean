module
public import Obend.Vault.SurviveFirePor
public import Obend.Vault.PortableContinuation

-- Private proof bodies are required by the complete axiom census.
import Obend.AssertAxioms
import Obend.Tactic.Tooth
import all Obend.Analysis.Coverage
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Codec.DetCbor
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.CanonicalExtension
import all Obend.Core.Capacity
import all Obend.Core.Check
import all Obend.Core.Code
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.EquiRecursiveLookup
import all Obend.Core.FieldCongruence
import all Obend.Core.Fill
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.LegacyAgreement
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Nominal
import all Obend.Core.Proofs.Adequacy.Birth
import all Obend.Core.Proofs.Adequacy.CasesControl
import all Obend.Core.Proofs.Adequacy.CasesEval
import all Obend.Core.Proofs.Adequacy.CasesReturn
import all Obend.Core.Proofs.Adequacy.Defs
import all Obend.Core.Proofs.Adequacy.Graph
import all Obend.Core.Proofs.Adequacy.Meaning
import all Obend.Core.Proofs.Adequacy.Origins
import all Obend.Core.Proofs.Adequacy.Progress
import all Obend.Core.Proofs.Adequacy.Reach
import all Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Adequacy.Safety
import all Obend.Core.Proofs.Adequacy.SafetyRaw
import all Obend.Core.Proofs.Adequacy.Scoped
import all Obend.Core.Proofs.Adequacy.Sound
import all Obend.Core.Proofs.Adequacy.Source
import all Obend.Core.Proofs.Adequacy.StepRaw
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Proofs.Completeness
import all Obend.Core.Proofs.Conservation
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.FillTyping
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Focus
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.Preservation.Cases.Functions
import all Obend.Core.Proofs.Preservation.Cases.Records
import all Obend.Core.Proofs.Preservation.Cases.Sums
import all Obend.Core.Proofs.StepCases
import all Obend.Core.Proofs.SubjectReduction
import all Obend.Core.Proofs.SubjectReduction.Substitution
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
import all Obend.Core.RuntimeOrigins
import all Obend.Core.Term
import all Obend.Core.TermTraverse
import all Obend.Core.Traverse
import all Obend.Core.Ty
import all Obend.Core.TypeGraph
import all Obend.Core.TypeGraphAlias
import all Obend.Core.TypeGraphHead
import all Obend.Core.TypeGraphResource
import all Obend.Crypto.DualSpine
import all Obend.Crypto.Multilinear
import all Obend.Crypto.PCS
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Doc
import all Obend.Doc.Backlinks
import all Obend.Doc.Graph
import all Obend.Doc.Merge
import all Obend.Doc.Patch
import all Obend.Doc.Render
import all Obend.Doc.Section
import all Obend.Doc.Structured
import all Obend.Elab.Coerce
import all Obend.Elab.Work
import all Obend.Equiv.Ahead
import all Obend.Equiv.Behaviour
import all Obend.Equiv.Fields
import all Obend.Equiv.Quote
import all Obend.Equiv.Reduction
import all Obend.Equiv.Simulation
import all Obend.Fold
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Judge.Computational
import all Obend.Judge.Instances
import all Obend.Judge.Lrat
import all Obend.Kind
import all Obend.Kind.Proofs
import all Obend.Law.Claim
import all Obend.Law.Contract
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Fill
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Proofs.Typing
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Ledger.Book
import all Obend.Ledger.Commit
import all Obend.Ledger.Floors
import all Obend.Ledger.Json
import all Obend.Ledger.Register
import all Obend.Ledger.Report
import all Obend.Ledger.Seat
import all Obend.Ledger.Vault
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Receipt
import all Obend.Logic.Rewrite
import all Obend.Polis.CapTP
import all Obend.Polis.VerkleUmem
import all Obend.Reasons
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Receipt.Negotiation
import all Obend.Run.Control
import all Obend.Run.Core4
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.Negotiation
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Interpret
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Negotiation
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.LawDial
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.LawCompile
import all Obend.Tactic.Cases
import all Obend.Tactic.MonadicReduction
import all Obend.Tactic.Tooth
import all Obend.Vault.Affordance
import all Obend.Vault.Branch
import all Obend.Vault.ChunkedWorld
import all Obend.Vault.Cost
import all Obend.Vault.DecodeCache
import all Obend.Vault.Escrow
import all Obend.Vault.Form
import all Obend.Vault.FormCheck
import all Obend.Vault.FormCheckCache
import all Obend.Vault.Hyperedge
import all Obend.Vault.Index
import all Obend.Vault.Json
import all Obend.Vault.Law
import all Obend.Vault.Log
import all Obend.Vault.LogBytes
import all Obend.Vault.Lsafe
import all Obend.Vault.Mandate
import all Obend.Vault.Merge
import all Obend.Vault.Page
import all Obend.Vault.PortableContinuation
import all Obend.Vault.Rehydration
import all Obend.Vault.Replay
import all Obend.Vault.Retention
import all Obend.Vault.SegmentLog
import all Obend.Vault.Store
import all Obend.Vault.SurviveFirePor
import all Obend.Vault.Transport
import all Obend.Vault.VerkleSnapshotBridge
meta import all Obend.Vault.ChunkedWorld
meta import all Obend.Vault.PortableContinuation
meta import all Obend.Vault.SurviveFirePor

public section
namespace Obend.Tests.SurviveFireAndContinuation
open Obend.Vault Obend.Vault.SurviveFirePor Obend.Vault.PortableContinuation
set_option autoImplicit false
set_option pp.maxSteps 1000
deriving instance DecidableEq for Except

example : gfMul 0x57 0x83 = 0xc1 := by decide +kernel
example : gfInv 0 = 0 := by decide +kernel
example : gfMul 0x53 (gfInv 0x53) = 1 := by decide +kernel

example (cs : List GF256) (h : cs.length = 3) :
    lagrangeInterpolatePoly [1, 2, 4] (evalPolyGF256 cs) = cs :=
  lagrangeInterpolate_exact _ _ (by decide +kernel) h

example (bytes : List UInt8) :
    recoverShardBytes 3 bytes.length [1, 2, 4] (encodeShardBytes bytes 3) = bytes :=
  recoverShardBytes_exact bytes 3 _ (by decide) (by decide) (by decide) rfl

example (root salt : Digest256) (w : ChunkedWorld.World) :
    decodeWorldShards root salt 3 (encryptWorld root salt w).length [0, 2, 4]
      (encodeShardBytes (encryptWorld root salt w) 3) = some w :=
  resurrectWorldFromAuthenticShards_exact root salt w 3 _ (by decide) (by decide) (by decide) rfl

example (polys : SharingPolynomial) (hl : ∀ i, (polys i).length = 2) :
    shamirReconstruct [1, 2] (shamirShare polys) = shamirShare polys 0 :=
  shamirReconstruct_exact _ _ (by decide) hl

example (observed : GF256 → GF256) (s : GF256) :
    lastShareToSecret [1] observed 2 (secretToLastShare [1] observed 2 s) = s :=
  (interposer_t_minus_1_information_theoretic_secrecy [1] observed 2
    (by decide) (by decide) (by decide)).1 s

example : ((List.range 5).filter (fun i => !([0, 3] : List Nat).contains i)).length = 3 := by decide

#tooth verifyMerkleOpening_parts by mutation verifyMerkleOpening := fun _ _ _ _ => true
#tooth importHomeArchive_authentic by mutation importHomeArchive := fun _ _ _ r _ => .ok r
#tooth gfMul_one by mutation gfMul := fun _ _ => 0
#tooth gfMul_inv_cancel by mutation gfInv := fun _ => 0
#tooth lagrangeInterpolate_exact by mutation liftAt := fun _ y _ => [y]
#tooth recoverShardBytes_exact by mutation recoverShardBytes := fun _ _ _ _ => []
#tooth checkKernelTransitionReceipt_sound by mutation checkKernelTransitionReceipt := fun _ _ => true
#tooth decodeHomeArchiveCbor_encode by mutation archiveCbor := fun _ => .uint 0
#tooth import_replay_refused by mutation importHomeArchive := fun _ _ _ r _ => .ok r

private def rootKey : Digest256 := ⟨⟨(List.replicate 32 0x37).toArray⟩, by decide⟩
private def salt : Digest256 := ⟨⟨(List.replicate 32 0x82).toArray⟩, by decide⟩
private def genesisB : Digest256 := ⟨⟨(List.replicate 32 0x23).toArray⟩, by decide⟩

private def world : ChunkedWorld.World :=
  { store := {
      pages := [
        { name := "alpha", id := 1, history := [], seen := some "first page", authors := [], note := none },
        { name := "beta", id := 2, history := [], seen := some "second page", authors := [], note := none }]
      members := [⟨"member", 7, [("read", "*")]⟩] } }

private def must (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

-- Compiled execution checks supplement the universal kernel theorems above.
#eval show IO Unit from do
  let bytes := encryptWorld rootKey salt world
  let manifest := makeFireManifest rootKey salt world 3 5
  let allShards := (List.range 5).map (fun i => authenticatedShard bytes 3 5 (BitVec.ofNat 8 i)) |>.toArray
  let fallback := authenticatedShard bytes 3 5 0
  let supplied := fun x : GF256 => allShards[x.toNat]?.getD fallback
  must "3-of-5: providers 0 and 3 lost" (decide
    (resurrectWorldFromShards rootKey manifest [1, 2, 4] supplied = some world))
  must "3-of-5: alternate surviving subset" (decide
    (resurrectWorldFromShards rootKey manifest [0, 2, 4] supplied = some world))
  let s := supplied 1
  let block := treeOpening s.header.blockDepth (blockMessages s.bytes s.header.blockDepth) 0
  let por : PorResponse := ⟨s.header, s.siblings, block⟩
  must "honest PoR accepted" (verifyPorResponse manifest.shardTreeRoot 8 1 0 por)
  let stale : PorResponse := { por with block := { block with bytes := ⟨#[block.bytes[0]! ^^^ 1]⟩ } }
  must "corrupted block refused" (!verifyPorResponse manifest.shardTreeRoot 8 1 0 stale)
  let wrongPath : PorResponse := { por with shardSiblings := List.replicate 8 rootKey.val }
  must "wrong shard Merkle path refused" (!verifyPorResponse manifest.shardTreeRoot 8 1 0 wrongPath)
  IO.println "cloud-fire recovery and nested PoR adversaries passed"

private def secret : Secret32 := fun i => BitVec.ofNat 8 (i.val + 19)
private def polynomials : SharingPolynomial := fun i => [secret i, BitVec.ofNat 8 (i.val + 71)]

#eval show IO Unit from do
  let shares := shamirShare polynomials
  must "custodians 1,2 reconstruct" (decide (List.ofFn (shamirReconstruct [1, 2] shares) = List.ofFn secret))
  must "custodians 2,3 reconstruct" (decide (List.ofFn (shamirReconstruct [2, 3] shares) = List.ofFn secret))
  let observed := fun x => shares x ⟨0, by decide⟩
  must "every candidate secret has a distinct consistent last share" ((List.range 256).all fun i =>
    lastShareToSecret [1] observed 2 (secretToLastShare [1] observed 2 (BitVec.ofNat 8 i)) == BitVec.ofNat 8 i)
  let state : CustodyState := ⟨genesisB, salt, ⟨20, 3, 15⟩, 0, rootKey⟩
  let good := makeTransitionReceipt state 7
  must "kernel judged transfer accepted" (checkKernelTransitionReceipt state good)
  must "receipt replayed into another vault refused"
    (!checkKernelTransitionReceipt { state with vaultId := rootKey } good)
  must "receipt replayed under another mandate refused"
    (!checkKernelTransitionReceipt { state with mandateId := rootKey } good)
  must "relabelled receipt changes its commitment" (decide
    (transitionCommitment { good with vaultId := rootKey } ≠ good.commitment))
  let forged := { good with after := ⟨13, 1000, 8⟩ }
  must "forged enclave quotes do not admit minting" (decide
    (admitCustodyTurn state ⟨forged, List.replicate 3 salt⟩ = none))
  IO.println "threshold custody and compromised-quote refusal passed"

private def mandate : PortableMandate :=
  ⟨4, .root ⟨"member", 7⟩ "vault", ⟨"agent", 8⟩, "vault", [.read, .call], 30, [1, 2], 100, [9, 10]⟩
private def swissSecret : Digest256 := ⟨⟨(List.replicate 32 0x63).toArray⟩, by decide⟩
/-- Same leading eight bytes as `swissSecret` (same `swissLocator`), different remaining 24. -/
private def swissAlias : Digest256 :=
  ⟨⟨(List.replicate 8 (0x63 : UInt8) ++ List.replicate 24 0x00).toArray⟩, by decide⟩
private def home : SovereignHome :=
  ⟨world, [⟨swissSecret, mandate, 5, 100, false⟩], [mandate],
    [⟨.deposited, .deposited, 9, 4, 0, 0, 0, 0⟩], rootKey, [], rootKey⟩
private def initialRegistry : MigrationRegistry :=
  ⟨7, 0, some ⟨1, rootKey, 17, home⟩, none, [], []⟩

#eval show IO Unit from do
  let .ok (signed, frozen) := exportHomeArchive rootKey initialRegistry 2 1 salt
    | throw (IO.userError "export refused")
  let wire := encodeHomeArchiveCbor signed.archive
  must "canonical archive roundtrip" (decide (decodeHomeArchiveCbor wire = some signed.archive))
  let .ok imported := importHomeArchive rootKey genesisB 2 frozen signed
    | throw (IO.userError "import refused")
  must "all member data survives re-genesis" (decide (imported.active.map (·.home) = some home))
  must "source mutation after export refused" (decide (admitHomeMutation 1 0 frozen home = .error .tombstoned))
  must "replay on third host refused" (decide
    (importHomeArchive rootKey salt 3 imported signed = .error .nonceConsumed))
  must "stale epoch refused" (decide
    (importHomeArchive rootKey genesisB 2 { frozen with latestCommittedEpoch := 1 } signed = .error .staleEpoch))
  let tampered := { signed with archive := { signed.archive with home :=
    { home with escrows := [⟨.deposited, .deposited, 900, 4, 0, 0, 0, 0⟩] } } }
  must "tampered balance refused" (decide
    (importHomeArchive rootKey genesisB 2 frozen tampered = .error .badAuthentication))
  let .ok (next, frozenAgain) := exportHomeArchive rootKey imported 3 2 genesisB
    | throw (IO.userError "second export refused")
  let .ok third := importHomeArchive rootKey salt 3 frozenAgain next
    | throw (IO.userError "second import refused")
  must "arbitrary next hop preserves full home" (decide (third.active.map (·.home) = some home))
  must "old nonce remains consumed after another hop" (decide
    (importHomeArchive rootKey genesisB 2 third signed = .error .nonceConsumed))
  must "256-bit bearer secret survives two hops" (decide
    ((third.active.bind fun l => l.home.lookupMembrane swissSecret).isSome))
  must "locator alias of the bearer secret refused"
    (swissLocator swissAlias == swissLocator swissSecret &&
      decide (home.lookupMembrane swissAlias = none))
  must "cU64 refuses 5 + 2^64 on decode" (decide
    (cU64.dec (ChunkedWorld.cNat.enc (5 + 2 ^ 64)) = none))
  must "cU64 accepts 2^64 - 1" (decide
    (cU64.dec (ChunkedWorld.cNat.enc (2 ^ 64 - 1)) = some (UInt64.ofNat (2 ^ 64 - 1), [])))
  IO.println "canonical archive migration, re-genesis, replay and tampering checks passed"

/-- The finite transcript of an empty history contains no possible collision. -/
theorem empty_migration_has_no_collision (home : SovereignHome) (key : Digest256)
    (r : MigrationRegistry) : ¬ Obend.Digest.HashBytes.CollisionAmong archiveHash
      (fun x => x ∈ migrationPreimages home key r []) := by
  rintro ⟨a, b, ha, _⟩
  cases ha

#tooth verifyReceipt_binding_or_collision by mutation
  VaultTransitionReceipt.payload := fun r =>
    (r.previous, r.previous, r.previous, r.epoch, r.amount, r.after)
#tooth import_preserves_origin_or_collision by mutation
  importHomeArchive := fun _ _ _ r _ => .ok r
#print axioms extractImportOriginBreak
#print axioms archiveDigest_binding
#print axioms acceptedReceipt_binding
#print axioms verifyReceipt_binding_or_collision
#print axioms custodyReceipt_inhabited

#print axioms gfMul_inv_cancel
#print axioms lagrangeInterpolate_exact
#print axioms resurrectFromAnyKShards_exact
#print axioms verifyPorChallenge_sound_or_collision
#print axioms lazyHost_evasion_bound
#print axioms interposer_t_minus_1_information_theoretic_secrecy
#print axioms enclave_compromise_admits_zero_invalid_transitions
#print axioms decodeHomeArchiveCbor_encode
#print axioms migrateHome_preserves_pages_membranes_and_balances
#print axioms double_import_or_stale_epoch_refused
#print axioms tampered_homeArchive_refused_or_collision
#assert_axioms_tree
end Obend.Tests.SurviveFireAndContinuation
