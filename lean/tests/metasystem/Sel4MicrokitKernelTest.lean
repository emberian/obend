module
public import Obend.OS.Sel4MicrokitKernel
import all Obend.OS.Sel4MicrokitKernel
public meta import Obend.OS.Sel4MicrokitKernel
public meta import Obend.OS.Sel4MicrokitKernelCore
public meta import Obend.Digest.Cshake256.Seam
public meta import Obend.Polis.GrainPowerbox
import Obend.Tactic.Tooth
import Obend.AssertAxioms
-- The import cone of `Obend.OS.Sel4MicrokitKernel`, with bodies: `#assert_axioms_tree` at the end
-- of this file reads every package constant it can see, and a `module` sees a theorem whose body
-- is not imported as an axiom.
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Consensus.Finality
import all Obend.Consensus.Simplex
import all Obend.Consensus.SimplexProtocol
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
import all Obend.Core.Proofs.DataSoundness
import all Obend.Core.Proofs.GroundExecution
import all Obend.Core.Proofs.Preservation.Base.Heads
import all Obend.Core.Proofs.Preservation.Base.Insert
import all Obend.Core.Proofs.Preservation.Base.Reusable
import all Obend.Core.Proofs.Preservation.Base.Values
import all Obend.Core.Proofs.Preservation.Base.Weaken
import all Obend.Core.Proofs.StepCases
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
import all Obend.Crypto.Multilinear
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
import all Obend.Judge.Lrat
import all Obend.Kind
import all Obend.Law.Claim
import all Obend.Law.Contract
import all Obend.Law.Inherit
import all Obend.Law.Machine
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Machine
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Proofs.Typing
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Ledger.Book
import all Obend.Ledger.Floors
import all Obend.Ledger.Register
import all Obend.Ledger.Seat
import all Obend.Logic.Claim
import all Obend.Logic.Frame
import all Obend.Logic.Ground
import all Obend.Logic.LateBinding
import all Obend.Logic.Obligation
import all Obend.Logic.Program
import all Obend.Logic.Receipt
import all Obend.Logic.Rewrite
import all Obend.OS.Sel4MicrokitKernelCore
import all Obend.Polis.CapTP
import all Obend.Polis.EvidencedOcap
import all Obend.Polis.GrainPowerbox
import all Obend.Polis.VerkleUmem
import all Obend.Polis.ZkBiscuit
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
import all Obend.Run.Core4
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Core4
import all Obend.Slot.Integrity
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
import all Obend.Trailblaze.Obligations
import all Obend.Trailblaze.Polis
import all Obend.Trailblaze.PolisBlum
import all Obend.Vault.Affordance
import all Obend.Vault.Hyperedge
import all Obend.Vault.IrreversibleOutbox
import all Obend.Vault.Law
import all Obend.Vault.Mandate
import all Obend.Vault.Page
import all Obend.Vault.Rehydration

/-!
# The seL4 / Microkit capability kernel, end to end

Four protection domains boot with root capabilities: a monitor holding untyped memory and the
scheduling control, a client and a verifier with their address spaces (the verifier also with a
frame of its own, outside the untyped region), and a NIC driver with the SMMU stream of its
device. The `#guard`s run the compiled kernel on that image; the `example`s
are kernel-checked and hold for every capability space, scheduling context and trace; each
`#tooth` replaces one check of the kernel by a weaker one and requires the kernel to reject the
stored proof of the named theorem.
-/

public section
namespace Obend.Tests.Sel4MicrokitKernel
open Obend.OS.Sel4MicrokitKernel
open Obend.Consensus.SimplexProtocol
open Obend.Vault.IrreversibleOutbox
open Obend.Trailblaze.Polis (sampleValidPartition)
open Obend.Polis.GrainPowerbox (PowerboxHost stepPowerboxHost Accountable runPowerbox genesis)
open Obend.Digest.Cshake256.Native (bytesOfList)

set_option autoImplicit false

def full : Rights := ⟨true, true, true⟩
def rw : Rights := ⟨true, true, false⟩
def ro : Rights := ⟨true, false, false⟩

def monitor : PdId := 0
def client : PdId := 1
def verifier : PdId := 2
def driver : PdId := 3

def root (owner : PdId) (obj : CapObj) : Option CapNode := some ⟨owner, ⟨obj, full, 0⟩, none, true⟩
def frame (pfn : Nat) (r : Rights) : Cap := ⟨.frameCap pfn, r, 0⟩

/-- Slots 0-5. Frames 16..31 are untyped memory, frame 40 is the verifier's own; frames below 16
belong to the kernel and no capability names them. -/
def bootCs : CSpace := #[
  root monitor (.untypedCap 16 16),
  root client (.pageTableCap client),
  root verifier (.pageTableCap verifier),
  root driver (.smmuStreamCap 7),
  root monitor (.schedControlCap 0),
  root verifier (.frameCap 40)]

/-- Every domain: two ticks of budget every five. -/
def sc0 : SchedContext := ⟨2, 5, [⟨0, 2⟩]⟩

def boot : KState := ⟨bootCs, [], fun _ => 0, #[sc0, sc0, sc0, sc0], 0⟩

/-- The monitor hands out frames (slots 6-8): the ring frame 16 to the client read-write and to
the verifier read-only, frame 18 to the driver. Each domain maps its own: the ring at page 1, the
verifier's private frame 40 at page 2, the DMA buffer at I/O page 0 of stream 7. -/
def setup : List KEvent := [
  .syscall monitor (.mint 0 client (frame 16 rw)),
  .syscall monitor (.mint 0 verifier (frame 16 ro)),
  .syscall monitor (.mint 0 driver (frame 18 rw)),
  .syscall client (.map (.cpu client) 1 6 1 16 true),
  .syscall verifier (.map (.cpu verifier) 2 7 1 16 false),
  .syscall verifier (.map (.cpu verifier) 2 5 2 40 true),
  .syscall driver (.map (.dev 7) 3 8 0 18 true)]

def k₀ : KState := runK boot setup
def cfg : IngressCfg := ⟨verifier, 4096, 8192, 4⟩

def live (k : KState) : List Bool := (List.range k.cspace.size).map fun i => (capAt k.cspace i).isSome
def refused (k : KState) (pd : PdId) (call : Syscall) : Bool := (ksyscall k pd call).isNone
def bytes (k : KState) (pfn off len : Nat) : List UInt8 :=
  (List.range len).map fun i => k.mem (pfn * 4096 + off + i)
def reads (k : KState) (pd : PdId) (va len : Nat) : Option (List UInt8) :=
  (readVia k pd va len).map (·.data.toList)

/-! ## Capabilities: attenuation, deletion, transitive revocation -/

#guard live k₀ == [true, true, true, true, true, true, true, true, true]
#guard k₀.maps.length == 4
-- No amplification: not more rights, not another frame, not a wider untyped, not a new badge.
#guard refused k₀ verifier (.mint 7 verifier (frame 16 rw))
#guard refused k₀ client (.mint 6 client (frame 17 rw))
#guard refused k₀ monitor (.mint 0 monitor ⟨.untypedCap 8 24, full, 0⟩)
#guard refused k₀ monitor (.mint 0 client ⟨.pageTableCap verifier, full, 0⟩)
#guard !refused k₀ client (.mint 6 client ⟨.frameCap 16, ro, 9⟩)
#guard refused (kstep k₀ (.syscall client (.mint 6 client ⟨.frameCap 16, ro, 9⟩))) client
  (.mint 9 client ⟨.frameCap 16, ro, 4⟩)
-- A domain mints only from its own slots, and hands a capability on only with the grant right.
#guard refused k₀ client (.mint 0 client (frame 19 rw))
#guard refused k₀ client (.mint 6 driver (frame 16 ro))
#guard refused k₀ verifier (.revoke 0)

/-- The monitor carves a sub-untyped for the client (slot 9), the client retypes a frame out of it
(slot 10) and re-shares that frame read-only with itself (slot 11), then deletes slot 9. -/
def carved : KState := runK k₀ [
  .syscall monitor (.mint 0 client ⟨.untypedCap 20 4, full, 0⟩),
  .syscall client (.mint 9 client (frame 21 rw)),
  .syscall client (.mint 10 client (frame 21 ro)),
  .syscall client (.delete 9)]

-- Deleting the middle capability kills it alone; its descendants keep their lineage.
#guard live carved == [true, true, true, true, true, true, true, true, true, false, true, true]
#guard refused carved client (.mint 9 client (frame 22 rw))
-- Revoking slot 10 erases slot 11 only.
#guard live (kstep carved (.syscall client (.revoke 10))) ==
  [true, true, true, true, true, true, true, true, true, false, true, false]
-- The monitor revokes its untyped: every descendant at every depth, through the tombstone, in
-- every domain is gone, the roots are untouched, and every mapping they backed is torn down.
-- The verifier's mapping of its own root frame is the one that survives.
def revoked : KState := kstep carved (.syscall monitor (.revoke 0))
#guard live revoked ==
  [true, true, true, true, true, true, false, false, false, false, false, false]
#guard revoked.maps.map (·.pfn) == [40]
#guard (nodeAt revoked.cspace 11).isNone && (nodeAt revoked.cspace 0).isSome

/-! ## Translation and DMA confinement -/

-- Mapping needs the space's capability and a frame capability of the invoker's, with the right.
#guard refused k₀ client (.map (.cpu verifier) 1 6 3 16 true)
#guard refused k₀ verifier (.map (.cpu verifier) 2 7 3 16 true)
#guard refused k₀ driver (.map (.dev 7) 3 5 1 40 true)
#guard refused k₀ driver (.map (.dev 9) 3 8 1 18 true)
#guard refused k₀ driver (.map (.dev 7) 3 8 0 18 true)

/-- A hostile device: stores through its one mapped I/O page, and through pages it has not. -/
def burst : List (Nat × UInt8) :=
  [(5, 0xEE), (4096 + 5, 0xEE), (16 * 4096, 0xEE), (40 * 4096 + 1, 0xEE), (3 * 4096, 0xEE)]
def dmaed : KState := runK k₀ (dmaBurst 7 burst)

#guard bytes dmaed 18 5 1 == [0xEE]
#guard [0, 3, 16, 19, 40].all fun pfn => bytes dmaed pfn 0 8 == bytes k₀ pfn 0 8
-- Another stream has no table at all; after the revocation stream 7 has none either.
#guard bytes (runK k₀ (dmaBurst 9 burst)) 18 5 1 == [0]
#guard bytes (runK revoked (dmaBurst 7 burst)) 18 5 1 == [0]
-- A read-only page refuses a store; the client's writable ring page takes it.
#guard bytes (kstep k₀ (.pdWrite verifier 4096 7)) 16 0 1 == [0]
#guard bytes (kstep k₀ (.pdWrite client 4096 7)) 16 0 1 == [7]

/-! ## Scheduling contexts -/

def spin (p : PdId) (n : Nat) : List KEvent := List.replicate n (.tick (some p))

-- A domain that never yields gets its two ticks in five, and nobody else's.
#guard ranCount verifier k₀ (spin verifier 5) == 2
#guard ranCount verifier k₀ (spin verifier 20) == 8
#guard ranCount client k₀ (spin verifier 20) == 0
#guard ranCount client (runK k₀ (spin verifier 20)) (spin client 5) == 2
-- Only the scheduling control reconfigures a context, and never above full utilisation.
#guard refused k₀ client (.schedConfigure 6 client 5 5)
#guard refused k₀ monitor (.schedConfigure 4 client 6 5)
#guard ranCount client (kstep k₀ (.syscall monitor (.schedConfigure 4 client 4 5))) (spin client 10)
  == 8

/-! ## Copy before verify -/

/-- The client publishes `1 2 3 4` in the ring. -/
def publish : List KEvent := [
  .pdWrite client 4096 1, .pdWrite client 4097 2, .pdWrite client 4098 3, .pdWrite client 4099 4]
def published : KState := runK k₀ publish

/-- After the copy the client overwrites the ring, the device fires, and the client grabs more
address space. -/
def race : List KEvent := [
  .pdWrite client 4096 0xFF, .pdWrite client 4097 0xFF, .dma 7 0 0xEE, .pdWrite client 8192 0xFF,
  .syscall client (.mint 6 client (frame 16 ro)), .tick (some client)]

def dispatching : KState := runK (ingressCopy cfg published) race

#guard reads published verifier cfg.sharedV 4 == some [1, 2, 3, 4]
#guard reads dispatching verifier cfg.sharedV 4 == some [0xFF, 0xFF, 3, 4]
#guard reads dispatching verifier (dispatchVaddr cfg) 4 == some [1, 2, 3, 4]
-- If the monitor revokes the ring mid-turn the shared page faults, and the private copy stands.
#guard reads (runK (ingressCopy cfg published) [.syscall monitor (.revoke 0)]) verifier
  cfg.sharedV 4 == none
#guard reads (runK (ingressCopy cfg published) [.syscall monitor (.revoke 0)]) verifier
  (dispatchVaddr cfg) 4 == some [1, 2, 3, 4]
-- Privacy needs the frame out of every other domain's untyped memory: had the monitor's untyped
-- covered frame 40, the executable check would refuse it, as it refuses the ring frame.
#guard exclusiveB k₀ verifier 40
#guard !exclusiveB k₀ verifier 16
#guard !exclusiveB k₀ client 16

/-! ## The same stories for every capability space, context and trace -/

/-- A child and a grandchild minted under any live capability of any well-formed space, for any
owners and any attenuations: one revocation of the source erases both, and keeps the source. -/
example {cs : CSpace} (hInv : CdtInv cs) {src : SlotId} {n : CapNode}
    (hn : capAt cs src = some n) (d₁ d₂ : PdId) {c₁ c₂ : Cap} (h₁ : c₁.le n.cap = true)
    (h₂ : c₂.le c₁ = true) (cs₂ : CSpace)
    (hcs : cs₂ = mintCap (mintCap cs src d₁ c₁) cs.size d₂ c₂) :
    nodeAt (revokeCap cs₂ src) cs.size = none ∧ nodeAt (revokeCap cs₂ src) (cs.size + 1) = none ∧
      nodeAt (revokeCap cs₂ src) src = nodeAt cs₂ src := by
  have hsz : (mintCap cs src d₁ c₁).size = cs.size + 1 := by simp [mintCap]
  have hmid : nodeAt (mintCap cs src d₁ c₁) cs.size = some ⟨d₁, c₁, some src, true⟩ := by
    simp [mintCap, nodeAt_push]
  have hInv₁ := mintCap_cdtInv hInv hn d₁ h₁
  have hInv₂ : CdtInv cs₂ :=
    hcs ▸ mintCap_cdtInv hInv₁ (capAt_eq_some.mpr ⟨hmid, rfl⟩) d₂ h₂
  have hchild : nodeAt cs₂ cs.size = some ⟨d₁, c₁, some src, true⟩ := by
    rw [hcs]
    unfold mintCap at hsz hmid ⊢
    rw [nodeAt_push, hsz]
    simp only [show ¬ cs.size = cs.size + 1 by omega, ↓reduceIte]
    exact hmid
  have hgrand : nodeAt cs₂ (cs.size + 1) = some ⟨d₂, c₂, some cs.size, true⟩ := by
    rw [hcs]
    unfold mintCap at hsz ⊢
    rw [nodeAt_push, hsz]
    simp only [↓reduceIte]
  have hd₁ : Descends cs₂ src cs.size := .child hchild rfl
  have hd₂ : Descends cs₂ src (cs.size + 1) := .step hgrand rfl hd₁
  obtain ⟨hdead, hkeep, -⟩ := revokeCap_severs_all_descendants hInv₂ src
  exact ⟨hdead _ hd₁, hdead _ hd₂, hkeep _ (cdt_acyclic hInv₂ src)⟩

theorem ticksIn_spin (p : PdId) (n : Nat) : ticksIn (spin p n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ticksIn (spin p (n + 1)) = 1 + ticksIn (spin p n) := rfl
    rw [h, ih]; omega

/-- Any well-formed context, any budget and period: a domain offered the processor on every one of
`n` ticks, never yielding, runs at most `⌈n / period⌉ · budget + budget` of them. -/
example {k : KState} {p : PdId} {sc : SchedContext} (hsc : k.scs[p]? = some sc) (hok : SchedOk sc)
    (n : Nat) :
    ranCount p k (spin p n) ≤ (n + sc.period - 1) / sc.period * sc.budget + sc.budget := by
  have h := mcs_temporal_isolation_bound hsc hok (spin p n) (fun ev hev => by
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hev
    rfl)
  rwa [ticksIn_spin] at h

/-- A boot image of root capabilities is well formed, so every trace theorem applies to every
trace from it: in particular a frame no root capability names is never written. -/
example (cs : CSpace) (mem : Nat → UInt8) (scs : Array SchedContext)
    (hRoots : ∀ i n, nodeAt cs i = some n → n.parent = none) (f : Nat)
    (hKernel : ∀ j r, capAt cs j = some r → r.cap.obj.touches f = false)
    (evs : List KEvent) (a : Nat) (ha : a / pageSize = f) :
    (runK ⟨cs, [], mem, scs, 0⟩ evs).mem a = mem a :=
  unowned_frame_immutable (kinv_of_roots cs mem scs 0 hRoots) f
    (fun j r hr _ => hKernel j r hr) evs a ha

/-! ## The premises hold on the booted image -/

theorem boot_sched : KSched boot := by
  intro p sc h
  have hp : p < 4 := (Array.getElem?_eq_some_iff.mp h).1
  have hsc : sc = sc0 := by
    match p, hp, h with
    | 0, _, h => exact (Option.some.inj h).symm
    | 1, _, h => exact (Option.some.inj h).symm
    | 2, _, h => exact (Option.some.inj h).symm
    | 3, _, h => exact (Option.some.inj h).symm
    | p + 4, hp, _ => exact absurd hp (Nat.not_lt.mpr (Nat.le_add_left 4 p))
  rw [hsc]
  exact schedOk_fresh 2 5 0 (by decide)

theorem k₀_inv : KInv k₀ :=
  runK_inv (kinv_of_roots _ _ _ _ ((allRoots_iff _).mp (by decide))) setup

theorem k₀_sched : KSched k₀ := runK_ksched boot_sched setup

/-- Frame 40 is private to the verifier after setup: checked by the executable pass. -/
theorem k₀_exclusive : Exclusive k₀ verifier (40 * 4096 / pageSize) :=
  (exclusiveB_iff _ _ _).mp (by decide)

theorem k₀_priv : translate k₀.maps (.cpu cfg.vpd) cfg.privV true = some (40 * 4096) := by decide

/-- On the booted image, after the client publishes `1 2 3 4` and the verifier copies: whatever
any sequence of events not run by the verifier does (the client, the monitor, the device, the
timer, any system call, any store), if the verifier can still read its dispatch address then it
reads `1 2 3 4`. -/
example (mid : List KEvent) (hAdv : ∀ ev ∈ mid, ev.actor ≠ some verifier) (d : ByteArray)
    (hD : readVia (runK (ingressCopy cfg published) mid) verifier (dispatchVaddr cfg) cfg.len =
      some d) :
    d = bytesOfList [1, 2, 3, 4] := by
  have hPub : PrivInv k₀ verifier (40 * 4096 / pageSize) published :=
    (privInv_run publish k₀ ⟨k₀_inv, k₀_exclusive, fun _ he _ => he⟩ (by decide)).1
  have hRing : readVia published verifier cfg.sharedV cfg.len = some (bytesOfList [1, 2, 3, 4]) := by
    decide
  exact (copy_into_private_pd_frame_before_verify k₀_inv.2.2 k₀_priv hPub hRing (by decide) mid
    hAdv hD).1

/-! ## One turn of the verifier loop, against the real outbox and any accepting powerbox -/

def proto : Protocol := ⟨[0, 1, 2, 3], 1, (· == 3), by decide, by decide, by decide⟩
def outbox₀ : OutboxState := ⟨3, 0, 500, 0, [], 0, []⟩

/-- The request the gatekeeper is handed: the snapshot `1 2 3 4`, and the ring as the client left
it after the copy. -/
def readReq : OutboxEffectReq :=
  ⟨1, .idempotentRead, 1, [], none, none,
    ⟨0, bytesOfList [1, 2, 3, 4], bytesOfList [0xFF, 0xFF, 3, 4]⟩⟩

/-- The client publishes, the verifier copies, the client and the device race, grain 0 invokes
slot 0. -/
def turn : VerifierTurn := ⟨publish, race, bytesOfList [1, 2, 3, 4], ⟨[], readReq, none⟩, 0, 0, 1⟩

def outbox₁ : OutboxState :=
  (stepOutbox proto sampleValidPartition [] outbox₀ readReq).getD outbox₀

/-- The turn is a valid run of the loop from the booted image, for every powerbox host that
accepts the grain's invocation of the snapshot. -/
theorem turn_kernel :
    (∀ ev ∈ turn.pre, ev.actor ≠ some cfg.vpd) ∧ (∀ ev ∈ turn.mid, ev.actor ≠ some cfg.vpd) ∧
    readVia (copyState k₀ turn) cfg.vpd cfg.sharedV cfg.len = some turn.ringAtCopy ∧
    (translate (copyState k₀ turn).maps (.cpu cfg.vpd) cfg.privV true).isSome = true ∧
    readVia (dispatchState cfg k₀ turn) cfg.vpd (dispatchVaddr cfg) cfg.len =
      some turn.out.req.spsc.sharedRingBeforeCopy ∧
    readVia (dispatchState cfg k₀ turn) cfg.vpd cfg.sharedV cfg.len =
      some turn.out.req.spsc.sharedRingAfterVerify := by
  decide

theorem turn_outbox : stepOutbox proto sampleValidPartition [] outbox₀ readReq = some outbox₁ := by
  decide

theorem turn_valid (h h₁ : PowerboxHost) (hinv : stepPowerboxHost h (invokeOf turn) = some h₁) :
    ValidVerifierLoop proto sampleValidPartition cfg ⟨k₀, [], outbox₀, h⟩ [turn]
      ⟨dispatchState cfg k₀ turn, [], outbox₁, h₁⟩ :=
  ⟨turn_kernel.1, turn_kernel.2.1, turn_kernel.2.2.1, turn_kernel.2.2.2.1, turn_kernel.2.2.2.2.1,
    turn_kernel.2.2.2.2.2, Reach.nil, SentSteps.refl _, h₁, outbox₁, outbox₁, hinv, turn_outbox,
    rfl, rfl, Reach.nil, by decide⟩

/-- Every kernel and outbox premise of the loop theorem is discharged on that run. -/
example (h h₁ : PowerboxHost) (hAcc : Accountable h)
    (hinv : stepPowerboxHost h (invokeOf turn) = some h₁) :
    KInv (dispatchState cfg k₀ turn) ∧
      Exclusive (dispatchState cfg k₀ turn) verifier (40 * 4096 / pageSize) ∧ Accountable h₁ := by
  have hsafe := sel4_microkit_verifier_loop_safe k₀_inv k₀_sched k₀_priv k₀_exclusive rfl hAcc
    (turn_valid h h₁ hinv)
  exact ⟨hsafe.1.1, hsafe.1.2.1, hsafe.2.1⟩

-- Such a host exists: a powerbox user grants grain 0 a capability, and the compiled powerbox
-- accepts the grain's invocation of the snapshot bytes.
#guard (runPowerbox (genesis [1] fun _ => .unbound3) #[.spawn,
  .grant 1 0 "ring" ⟨0x7, .const true, "client".toUTF8, "ring".toUTF8⟩ none, invokeOf turn]).isSome

/-! ## Teeth -/

-- A pass that erases only the direct children leaves the grandchildren alive.
#tooth revokeCap_severs_all_descendants by mutation scanKeep :=
  fun s _ slot =>
    match slot with
    | none => none
    | some n => if n.parent == some s then none else some n

-- A mint that checks the owner but not the attenuation hands out any capability.
#tooth no_authority_amplification_across_syscalls by mutation mintOk :=
  fun n pd _ _ => n.owner == pd

-- A stream table that ignores the write bit lets a device store through a read-only page.
#tooth smmu_dma_write_confined_to_writable_pd_frames by mutation translate :=
  fun maps sp va _ =>
    (lookupMap maps sp (va / pageSize)).map fun e => e.pfn * pageSize + va % pageSize

-- A revocation that leaves the mappings in place lets stale translations outlive their frames.
#tooth trace_mem_confined by mutation teardown :=
  fun _ maps => maps

-- A context whose charged unit returns at once is no bound at all.
#tooth mcs_temporal_isolation_bound by mutation SchedContext.charge :=
  fun sc now =>
    match sc.refills with
    | [] => none
    | r :: rest =>
      if r.time ≤ now ∧ 0 < r.amount then
        some { sc with refills := pushRefill (decHead r rest) ⟨now, 1⟩ }
      else none

-- A dispatcher that fetches the shared ring a second time dispatches what the client wrote last.
#tooth copy_into_private_pd_frame_before_verify by mutation dispatchVaddr :=
  fun cfg => cfg.sharedV

-- A map call that does not ask who owns the frame lets any domain map the verifier's.
#tooth sel4_microkit_verifier_loop_safe by mutation mapOk :=
  fun a _ pd sp _ _ => a.owner == pd && a.cap.obj == sp.authObj

-- A mint that forgets the grant right serves a call the contract forbids.
#tooth ksyscall_skip_implies_contract_violation by mutation mintOk :=
  fun n pd _ cap => n.owner == pd && cap.le n.cap

#assert_axioms_tree

end Obend.Tests.Sel4MicrokitKernel

end
