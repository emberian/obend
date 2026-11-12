module
public import Obend.Polis.GrainPowerbox
import all Obend.Polis.GrainPowerbox
public meta import Obend.Polis.GrainPowerbox
import Obend.Tactic.Tooth
import Obend.AssertAxioms
-- The import cone of `Obend.Polis.GrainPowerbox`, with bodies: `#assert_axioms_tree` at the end of
-- this file reads every package constant it can see, and a `module` sees a theorem whose body is
-- not imported as an axiom.
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.AliasExposure
import all Obend.Core.Assumptions
import all Obend.Core.Bidirectional
import all Obend.Core.Brand
import all Obend.Core.CanonicalExtension
import all Obend.Core.Check
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.EquiRecursiveAgreement
import all Obend.Core.FieldCongruence
import all Obend.Core.FiniteBisimulation
import all Obend.Core.FinitePresentation
import all Obend.Core.FiniteRowLaws
import all Obend.Core.Invariant
import all Obend.Core.LegacyAgreement
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.MachineTyping
import all Obend.Core.Proofs.Substitution.Defs
import all Obend.Core.Proofs.Substitution.Uses
import all Obend.Core.Proofs.TypedSubstitution
import all Obend.Core.RecursiveAgreement
import all Obend.Core.RecursiveRows
import all Obend.Core.ResourceSemantics
import all Obend.Core.RowCongruence
import all Obend.Core.RowExposureInvariance
import all Obend.Core.RowHit
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
import all Obend.Intention
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Law.Claim
import all Obend.Law.Inherit
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Eval
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Std
import all Obend.Law.Proofs.Typing
import all Obend.Law.Run
import all Obend.Law.Std
import all Obend.Law.Syntax
import all Obend.Polis.CapTP
import all Obend.Polis.EvidencedOcap
import all Obend.Polis.VerkleUmem
import all Obend.Polis.ZkBiscuit
import all Obend.Run.Core4
import all Obend.Run.Runner
import all Obend.Slot
import all Obend.Slot.Integrity
import all Obend.Slot.Protocol
import all Obend.Slot.World
import all Obend.Spec.C4
import all Obend.Spec.DataWire
import all Obend.Spec.Law
import all Obend.Spec.LawCompile
import all Obend.Spec.LawDial
import all Obend.Spec.Proofs.C4
import all Obend.Spec.Proofs.LawCompile
import all Obend.Tactic.Cases
import all Obend.Tactic.Tooth
import all Obend.Vault.Affordance
import all Obend.Vault.Law
import all Obend.Vault.Mandate
import all Obend.Vault.Page
import all Obend.Vault.Rehydration

/-!
# Grain powerbox, caretaker membranes, blame and restart, end to end

Alice is the powerbox user. Bob, Carol and Dave are grains. The `#guard`s run the compiled step
with the real cSHAKE256 digests; the `example`s are kernel-checked and symbolic in every block and
host; each `#tooth` replaces one check of `Obend.Polis.GrainPowerbox` by a weaker one and requires
the kernel to reject the stored proof of the named theorem.
-/

public section
namespace Obend.Tests.GrainPowerboxMembrane
open Obend.Polis Obend.Polis.GrainPowerbox

def facts : Nat → KleenePred3 := fun _ => .unbound3
def blk (rights : UInt64) (holder channel : String) : Block :=
  ⟨rights, .const true, holder.toUTF8, channel.toUTF8⟩

def alice : Nat := 1
def bob : GrainId := 0
def carol : GrainId := 1
def dave : GrainId := 2
def mAB : MembraneId := 10
def mAD : MembraneId := 20
def mBC : MembraneId := 30

def docRoot : Block := blk 0x7 "bob" "alice-bob"
def calRoot : Block := blk 0x3 "dave" "alice-dave"
def readHop : Block := blk 0x1 "carol" "bob-carol"
def backHop : Block := blk 0x1 "bob" "carol-bob"
def act : ByteArray := "read page 1".toUTF8

def docCap : CapDescriptor := rootCap docRoot (some mAB)
def carolCap : CapDescriptor := docCap.extend readHop none

/-- Three grains; Alice grants Bob the document under `mAB` and Dave the calendar under `mAD`;
Bob introduces Carol to a read-only attenuation of the document. -/
def setup : Array PowerboxTurn := #[
  .spawn, .spawn, .spawn,
  .grant alice bob "alice-doc" docRoot (some mAB),
  .grant alice dave "alice-cal" calRoot (some mAD),
  .delegate bob 0 carol "bobs-doc" readHop none 77]

def run (turns : Array PowerboxTurn) : Option PowerboxHost :=
  runPowerbox (genesis [alice] facts) turns
def ok (turns : Array PowerboxTurn) : Bool := (run turns).isSome
def slotOf (turns : Array PowerboxTurn) (g : GrainId) (slot : Nat) : Option HeldCap :=
  (run turns).bind (heldAt · g slot)

/-! ## No ambient authority -/

#guard ok setup
-- A new grain holds nothing, and nothing but a grant or an introduction fills a slot.
#guard (slotOf #[.spawn] 0 0).isNone
#guard !ok #[.spawn, .invoke 0 0 0 act]
#guard (slotOf setup carol 1).isNone
#guard !ok (setup.push (.invoke carol 1 0x1 act))
-- Dave's slot 0 is his calendar, not Bob's document: slots are per grain.
#guard !ok (setup.push (.invoke dave 0 0x4 act))
#guard ok (setup.push (.invoke bob 0 0x4 act))
-- Only a powerbox user grants.
#guard !ok (setup.push (.grant 9 carol "forged" docRoot none))
-- Attenuation: Carol holds the read right only, and a hop cannot widen.
#guard ok (setup.push (.invoke carol 0 0x1 act))
#guard !ok (setup.push (.invoke carol 0 0x2 act))
#guard !ok (setup.push (.delegate bob 0 carol "wider" (blk 0xF "carol" "bob-carol") none 78))

/-! ## Petnames -/

#guard (slotOf setup bob 0).map (·.petname) == some "alice-doc"
#guard ((run setup).bind (·.grains[bob]?)).bind (·.resolvePetname "alice-doc") == some 0
#guard ((run setup).bind (·.grains[carol]?)).bind (·.resolvePetname "bobs-doc") == some 0
#guard ((run setup).bind (·.grains[carol]?)).bind (·.resolvePetname "alice-doc") == none
#guard !ok (setup.push (.grant alice bob "alice-doc" calRoot none))

/-! ## Membrane inheritance and blame -/

#guard (slotOf setup carol 0).map (·.cap.membranes) == some [mAB]
#guard (slotOf setup carol 0).map (·.via) == some (.grain bob)
#guard (slotOf setup carol 0).map (·.cap.digest) == some carolCap.digest
#guard (run (setup.push (.invoke carol 0 0x1 act))).map
    (·.audit.map fun e => (e.whoInvoked, e.viaWhichDelegator, e.capDigest)) ==
  some [(.grain carol, .grain bob, carolCap.digest)]
#guard (run (setup.push (.invoke bob 0 0x1 act))).map
    (·.audit.map fun e => (e.whoInvoked, e.viaWhichDelegator)) ==
  some [(.grain bob, .user alice)]
#guard (run setup).map (·.edges.map fun e => (e.delegator, e.delegatee, e.membraneLineage)) ==
  some [(.grain bob, .grain carol, [mAB]), (.user alice, .grain dave, [mAD]),
    (.user alice, .grain bob, [mAB])]
-- A gift is redeemed once.
#guard !ok (setup.push (.delegate bob 0 dave "again" readHop none 77))

/-! ## Revoking `mAB` -/

def revoked : Array PowerboxTurn := setup.push (.revokeMembrane (.user alice) mAB)

#guard ok revoked
#guard !ok (revoked.push (.invoke bob 0 0x1 act))
#guard !ok (revoked.push (.invoke carol 0 0x1 act))
#guard ok (revoked.push (.invoke dave 0 0x1 act))
#guard !ok (revoked.push (.delegate bob 0 dave "late" readHop none 78))
#guard !ok (revoked.push (.delegate carol 0 dave "late" backHop none 78))
#guard ok (revoked.push (.delegate dave 0 carol "daves-cal" (blk 0x1 "carol" "dave-carol") none 78))
-- No c-list was edited by the revocation.
#guard (slotOf revoked carol 0).map (·.cap.digest) == some carolCap.digest
-- Only the owner of a membrane revokes it.
#guard !ok (setup.push (.revokeMembrane (.grain bob) mAB))
#guard !ok (setup.push (.revokeMembrane (.user 9) mAB))
-- Nobody wraps under a membrane someone else owns.
#guard !ok (setup.push (.delegate bob 0 carol "sneak" readHop (some mAD) 78))

/-- Carol hands a result back to Bob across the membrane; it is enclosed by `mAB` as well. -/
def returned : Array PowerboxTurn :=
  setup.push (.delegate carol 0 bob "carols-result" backHop none 78)

#guard (slotOf returned bob 1).map (·.cap.membranes) == some [mAB]
#guard ok (returned.push (.invoke bob 1 0x1 act))
#guard !ok ((returned.push (.revokeMembrane (.user alice) mAB)).push (.invoke bob 1 0x1 act))

/-- Bob interposes his own caretaker `mBC` on what he gives Carol. -/
def interposed : Array PowerboxTurn := #[
  .spawn, .spawn,
  .grant alice bob "alice-doc" docRoot (some mAB),
  .delegate bob 0 carol "bobs-doc" readHop (some mBC) 5,
  .revokeMembrane (.grain bob) mBC]

#guard (slotOf interposed carol 0).map (·.cap.membranes) == some [mBC, mAB]
#guard !ok (interposed.push (.invoke carol 0 0x1 act))
#guard ok (interposed.push (.invoke bob 0 0x1 act))

/-! ## Checkpoint, crash, restart -/

def crashed : Array PowerboxTurn :=
  setup ++ (#[.checkpoint bob, .checkpoint dave, .revokeMembrane (.user alice) mAB,
    .restart bob, .restart dave] : Array PowerboxTurn)

#guard ok crashed
-- Dave's reference under `mAD` is rebound and works; Bob's under `mAB` is not resurrected.
#guard (slotOf crashed dave 0).map (·.petname) == some "alice-cal"
#guard ok (crashed.push (.invoke dave 0 0x1 act))
#guard (slotOf crashed bob 0).isNone
-- Without the revocation the same restart rebinds Bob's reference.
#guard ok ((setup.push (.checkpoint bob)).push (.restart bob) |>.push (.invoke bob 0 0x1 act))
-- A revoked root grant is not resurrected either.
#guard (slotOf (setup ++ (#[.checkpoint dave,
    .revokeLineage alice (credNul (rootLineage calRoot)), .restart dave] : Array PowerboxTurn))
  dave 0).isNone
-- What a grain acquired after its checkpoint is lost with the crash.
#guard (slotOf (#[.spawn, .spawn, .checkpoint bob,
    .grant alice bob "alice-doc" docRoot none, .restart bob]) bob 0).isNone
#guard !ok (setup.push (.restart carol))

def afterRevoke : Option PowerboxHost := run revoked
-- A snapshot the graph never committed, or whose commitment was altered, does not rebind.
#guard (afterRevoke.bind (thawRef · dave ⟨"cal", .user alice, rootCap calRoot (some mAD),
    (rootCap calRoot (some mAD)).digest⟩)).isSome
#guard (afterRevoke.bind (thawRef · dave ⟨"cal", .user alice, rootCap calRoot none,
    (rootCap calRoot none).digest⟩)).isNone
#guard (afterRevoke.bind (thawRef · dave ⟨"cal", .user alice, rootCap calRoot none,
    (rootCap calRoot (some mAD)).digest⟩)).isNone
#guard (afterRevoke.bind (thawRef · carol ⟨"cal", .user alice, rootCap calRoot (some mAD),
    (rootCap calRoot (some mAD)).digest⟩)).isNone

/-! ## The same story for every host and every block -/

/-- Alice grants under `m`, the grantee introduces a third grain by `hop`, then anything at all
happens before and after Alice's revocation. Whoever holds that delegated capability afterwards
cannot invoke it and cannot pass it on. -/
example {h₀ h₁ h₂ h₃ : PowerboxHost} {ts₁ ts₂ : List PowerboxTurn} {actor : PrincipalId}
    {m : MembraneId} (hacc : Accountable h₀) (t₁ : ValidPowerboxTrace h₀ ts₁ h₁)
    (hrev : stepPowerboxHost h₁ (.revokeMembrane actor m) = some h₂)
    (t₂ : ValidPowerboxTrace h₂ ts₂ h₃) {g : GrainId} {slot : Nat} {x : HeldCap}
    (hheld : HoldsAt h₃ g slot x) (root hop : Block) (wrap : Option MembraneId)
    (hx : x.cap = (rootCap root (some m)).extend hop wrap) (need : UInt64) (action : ByteArray)
    (dst : GrainId) (pet : String) (hop' : Block) (wrap' : Option MembraneId) (gift : UInt64) :
    stepPowerboxHost h₃ (.invoke g slot need action) = none ∧
      stepPowerboxHost h₃ (.delegate g slot dst pet hop' wrap' gift) = none := by
  obtain ⟨path, -, hself, hdead⟩ :=
    revokeMembrane_severs_all_transitive_descendants hacc t₁ hrev t₂ hheld
  have hm : m ∈ x.cap.membranes := by
    rw [hx]
    simp [CapDescriptor.extend, rootCap]
  obtain ⟨hinv, hdel⟩ := hdead ⟨_, hself, hm⟩
  exact ⟨hinv need action, hdel dst pet hop' wrap' gift⟩

/-- The runner and the trace relation agree, so every `#guard` above is about a
`ValidPowerboxTrace` from an accountable host. -/
example (turns : Array PowerboxTurn) (h : PowerboxHost) (hr : run turns = some h) :
    Accountable h :=
  trace_accountable (genesis_accountable [alice] facts) ((runPowerbox_iff _ _ _).mp hr)

/-- From the empty host, for every user, facts, rights mask and key material: spawn, grant, invoke
is a valid trace whose one log entry blames the granting user. Kernel-checked, and no hash is
evaluated: the revoked sets are empty, so no search reads a nullifier. -/
example (u : Nat) (facts : Nat → KleenePred3) (rights : UInt64) (holder channel action : ByteArray)
    (pet : String) :
    ∃ h, ValidPowerboxTrace (genesis [u] facts)
        [.spawn, .grant u 0 pet ⟨rights, .const true, holder, channel⟩ none,
          .invoke 0 0 0 action] h ∧
      h.audit.map (fun e => (e.whoInvoked, e.viaWhichDelegator)) = [(.grain 0, .user u)] := by
  generalize hroot : (⟨rights, .const true, holder, channel⟩ : Block) = root
  have hE : ∀ x, RevokedSet.empty.contains x = false := fun _ => rfl
  have hchain : ∀ h : PowerboxHost, h.revoked = .empty →
      chainAcc h (rootCap root none) =
        some ⟨rights, (Caveat.const true).eval h.facts, rootLineage root⟩ := by
    intro h hr
    subst hroot
    simp [chainAcc, foldChain, foldRoot, lineageLive, channelLive, hr, hE, rootCap]
  have hlive : ∀ h : PowerboxHost, h.revoked = .empty →
      capLive h (rootCap root none) 0 = true ∧ capAdmissible h (rootCap root none) = true := by
    intro h hr
    have hm : membranesLive h (rootCap root none) = true := rfl
    have hc := hchain h hr
    refine ⟨?_, ?_⟩
    · unfold capLive
      rw [hm, hc]
      simp [authorize, subMask, Caveat.eval, KleenePred3.accepts]
    · unfold capAdmissible
      rw [hm, hc]
      rfl
  let h₁ : PowerboxHost := { genesis [u] facts with grains := (#[] : Array GrainState).push ⟨#[]⟩ }
  let x : HeldCap := ⟨rootCap root none, .user u, pet⟩
  let h₂ : PowerboxHost :=
    addCap { h₁ with membraneOwners := [], edges := grantEdge u 0 (rootCap root none) :: h₁.edges }
      0 x
  have s₂ : stepPowerboxHost h₁ (.grant u 0 pet root none) = some h₂ := by
    have hf : petnameFresh h₁ 0 pet = true := by simp [petnameFresh, h₁]
    have hu : (genesis [u] facts).users.contains u = true := by simp [genesis]
    simp only [stepPowerboxHost, claimMembrane]
    rw [show h₁.users.contains u = true from hu, hf, (hlive h₁ rfl).2]
    rfl
  have hheld : heldAt h₂ 0 0 = some x :=
    heldAt_iff.mpr (holdsAt_addCap.mpr (.inr ⟨rfl, rfl, ⟨#[]⟩, by simp [h₁], rfl⟩))
  have s₃ : stepPowerboxHost h₂ (.invoke 0 0 0 action) =
      some { h₂ with audit := auditEntry 0 x action :: h₂.audit } := by
    simp only [stepPowerboxHost, hheld]
    rw [show capLive h₂ x.cap 0 = true from (hlive h₂ rfl).1]
    rfl
  exact ⟨_, ⟨h₁, rfl, h₂, s₂, _, s₃, rfl⟩, rfl⟩

/-! ## Teeth -/

#tooth revokeMembrane_severs_all_transitive_descendants by mutation CapDescriptor.extend :=
  fun c hop wrap => ⟨c.root, c.hops.push hop, wrap.toList⟩

#tooth revokeMembrane_severs_all_transitive_descendants by mutation membranesLive :=
  fun _ _ => true

#tooth revokeMembrane_preserves_independent_siblings by mutation membranesLive :=
  fun h _ => h.revokedMembranes.keys.isEmpty

#tooth thaw_never_resurrects_revoked_cap by mutation thawRef :=
  fun h g fr =>
    if fr.commitment == fr.cap.digest && committedTo h g fr then
      some ⟨fr.cap, fr.via, fr.petname⟩
    else none

#tooth thaw_never_resurrects_revoked_cap by mutation capAdmissible :=
  fun h c => (chainAcc h c).isSome

#tooth thaw_refuses_revoked_lineage by mutation capAdmissible :=
  fun h c => membranesLive h c

#tooth blameAttribution_sound by mutation delegatedEntry :=
  fun _ child pet => ⟨child, .grain 0, pet⟩

#tooth no_ambient_authority_in_grain by mutation heldAt :=
  fun h _ slot =>
    match h.grains[0]? with
    | some gs => gs.clist[slot]?
    | none => none

#tooth powerboxStep_skip_implies_violation by mutation claimMembrane :=
  fun owners _ _ => some owners

#tooth CapDescriptor.digest_binds by mutation CapDescriptor.preimage :=
  fun c => Obend.Crypto.encodeListField (lineageOf c.root c.hops.toList).data.toList

#assert_axioms_tree

end Obend.Tests.GrainPowerboxMembrane

end
