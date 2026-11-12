module
/-
# Obend.Polis.GrainPowerbox — grains with no ambient authority, a powerbox, caretaker membranes

A `PowerboxHost` runs isolated grains. A grain is a c-list: an array of held capabilities that the
grain can name only by slot. There is no other table a grain can read.

1. A capability is a `CapDescriptor`: an `Obend.Polis` attenuation chain (a root `Block` and its
   hops, checked by `foldChain`) together with the caretaker membranes that enclose it. Its
   256-bit `digest` frames the chain's provenance digest and the membrane list
   (`CapDescriptor.digest_binds`).
2. `stepPowerboxHost` has eight turns. A capability enters a c-list in two ways only: a powerbox
   user's `grant`, or a `delegate` from a slot the delegating grain holds. Both bind a petname that
   is fresh in the receiving grain. A `delegate` spends a gift nullifier (`Obend.Polis.CapTP`'s
   sorted set), so one introduction is redeemed at most once (`gift_never_redeemed_twice`).
3. `Provenance` is derivability in the committed edge graph. `no_ambient_authority_in_grain`: over
   any trace, every held capability has a provenance path that starts at a user's grant, and along
   that path membranes only accumulate and authority only narrows.
4. `revokeMembrane` is one insertion into a sorted set. `capLive` consults that set by binary
   search, so no c-list is touched. `revokeMembrane_severs_all_transitive_descendants` and
   `revokeMembrane_preserves_independent_siblings` are its two halves.
5. Every held capability remembers who handed it over. An invocation logs that delegator, and
   `blameAttribution_sound` finds the logged pair as an edge of the graph whose delegator was a
   powerbox user or held the parent.
6. `freezeGrain` and `thawGrain` snapshot and restore a c-list against the durable host, and the
   `checkpoint` and `restart` turns run them: a restart replaces a grain's c-list by the thaw of its
   last checkpoint, so the trace theorems hold across crashes.
   `thaw_never_resurrects_revoked_cap` characterises exactly which frozen references rebind, and
   `thaw_rehydrates_iff` reads that verdict as an `Obend.Vault.Rehydration` membrane viewer.
7. `powerboxStep_skip_implies_violation`: a turn is refused exactly when it violates the caller
   contract `PowerboxViolation`.

`ValidPowerboxTrace` is a recursive definition, not an inductive family, so that `#tooth` can
replay the trace theorems against a mutated step.
-/
public import Obend.Polis.ZkBiscuit
public import Obend.Polis.CapTP
public import Obend.Vault.Rehydration

public section
namespace Obend.Polis.GrainPowerbox

open Obend.Polis
open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Vault.Rehydration (MembraneViewer Sturdyref rehydrateSturdyref projectMembrane
  mem_projectMembrane membraneShows)
open Obend.Vault.Affordance (Auth CellAffordance)

set_option autoImplicit false

/-! ## 1. Identities, digests and capability descriptors -/

abbrev MembraneId := Nat
abbrev GrainId := Nat

/-- Who can be held responsible: a powerbox user or a grain. -/
inductive PrincipalId where
  | user (id : Nat)
  | grain (g : GrainId)
  deriving DecidableEq, Repr

/-- The big-endian reading of a 32-byte cSHAKE256 output as a 256-bit word. -/
def digest256 (customization pre : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (cshake256Bytes customization pre))

theorem digest256_binds (customization : List UInt8) {p₁ p₂ : List UInt8}
    (h : digest256 customization p₁ = digest256 customization p₂) :
    p₁ = p₂ ∨ CollisionAmong (cshake256Bytes customization) (fun x => x = p₁ ∨ x = p₂) := by
  by_cases hp : p₁ = p₂
  · exact .inl hp
  · refine .inr ⟨p₁, p₂, .inl rfl, .inr rfl, hp, ?_⟩
    have hn := congrArg BitVec.toNat h
    simp only [digest256, BitVec.toNat_ofNat] at hn
    have b₁ := ofBE_lt (cshake256Bytes customization p₁)
    have b₂ := ofBE_lt (cshake256Bytes customization p₂)
    rw [cshake256Bytes_length] at b₁ b₂
    have e : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
    rw [e] at b₁ b₂
    rw [Nat.mod_eq_of_lt b₁, Nat.mod_eq_of_lt b₂] at hn
    exact hn

/-- A capability: an attenuation chain and the caretaker membranes enclosing it, innermost
first. -/
structure CapDescriptor where
  root : Block
  hops : Array Block
  membranes : List MembraneId

def capCustomization : List UInt8 := "OBEND.POLIS.GRAIN.CAP/v1".toUTF8.data.toList
def actionCustomization : List UInt8 := "OBEND.POLIS.GRAIN.ACTION/v1".toUTF8.data.toList

/-- The hash a capability digest is a collision of when it fails to bind. -/
def capHash : Hash := cshake256Bytes capCustomization

/-- The chain's provenance digest, length-prefixed, then every membrane id, length-prefixed. -/
def CapDescriptor.preimage (c : CapDescriptor) : List UInt8 :=
  encodeListField (lineageOf c.root c.hops.toList).data.toList ++ encodeNats c.membranes

def CapDescriptor.digest (c : CapDescriptor) : BitVec 256 :=
  digest256 capCustomization c.preimage

def actionDigest (action : ByteArray) : BitVec 256 :=
  digest256 actionCustomization action.data.toList

/-- Equal digests name the same root grant, hops and membranes, or exhibit a collision of the
capability hash or of the provenance hash among the preimages that were hashed. -/
theorem CapDescriptor.digest_binds {c₁ c₂ : CapDescriptor} (h : c₁.digest = c₂.digest) :
    c₁ = c₂ ∨ CollisionAmong capHash (fun x => x = c₁.preimage ∨ x = c₂.preimage) ∨
      CollisionAmong lineageHash (fun x =>
        LineageHashed c₁.root c₁.hops.toList x ∨ LineageHashed c₂.root c₂.hops.toList x) := by
  rcases digest256_binds capCustomization h with hp | hc
  · obtain ⟨hl, hm⟩ := encodeListField_prefix_inj hp
    rcases lineageOf_binds (byteArray_eq_of_toList_eq hl) with ⟨hg, hh⟩ | hc
    · left
      obtain ⟨r₁, a₁, m₁⟩ := c₁
      obtain ⟨r₂, a₂, m₂⟩ := c₂
      have ha : a₁ = a₂ := Array.toList_inj.mp hh
      have hm' : m₁ = m₂ := encodeNats_injective hm
      cases hg
      cases ha
      cases hm'
      rfl
    · exact .inr (.inr hc)
  · exact .inr (.inl hc)

/-- One more hop, optionally under one more membrane. The parent's membranes are kept. -/
def CapDescriptor.extend (c : CapDescriptor) (hop : Block) (wrap : Option MembraneId) :
    CapDescriptor :=
  ⟨c.root, c.hops.push hop, wrap.toList ++ c.membranes⟩

/-- A capability a user grants: a root block with no hops. -/
def rootCap (root : Block) (wrap : Option MembraneId) : CapDescriptor := ⟨root, #[], wrap.toList⟩

/-- `child` is `parent` with one more hop, and every membrane of `parent` still encloses it. -/
def Extends (child parent : CapDescriptor) : Prop :=
  child.root = parent.root ∧ (∃ hop, child.hops = parent.hops.push hop) ∧
    ∃ wrap : List MembraneId, child.membranes = wrap ++ parent.membranes

theorem extend_extends (c : CapDescriptor) (hop : Block) (wrap : Option MembraneId) :
    Extends (c.extend hop wrap) c :=
  ⟨rfl, ⟨hop, rfl⟩, ⟨wrap.toList, rfl⟩⟩

/-! ## 2. The host -/

/-- A c-list entry: the capability, who handed it over, and the grain's own name for it. -/
structure HeldCap where
  cap : CapDescriptor
  via : PrincipalId
  petname : String

/-- A grain is its c-list. A new grain's is empty. -/
structure GrainState where
  clist : Array HeldCap

/-- An edge of the committed delegation graph. A user's grant has equal parent and child. -/
structure DelegationBlame where
  delegator : PrincipalId
  delegatee : PrincipalId
  parentCapDigest : BitVec 256
  childCapDigest : BitVec 256
  membraneLineage : List MembraneId
  deriving DecidableEq

/-- One logged invocation. -/
structure AuditAttributionEntry where
  whoInvoked : PrincipalId
  viaWhichDelegator : PrincipalId
  capDigest : BitVec 256
  actionDigest : BitVec 256
  deriving DecidableEq

/-- A frozen c-list entry and the commitment taken when it was frozen. -/
structure FrozenRef where
  petname : String
  via : PrincipalId
  cap : CapDescriptor
  commitment : BitVec 256

structure FrozenGrain where
  grain : GrainId
  refs : Array FrozenRef

structure PowerboxHost where
  users : List Nat
  facts : Nat → KleenePred3
  grains : Array GrainState
  revoked : RevokedSet
  revokedMembranes : RevokedSet
  membraneOwners : List (MembraneId × PrincipalId)
  giftsSpent : CapTP.NullifierSet
  edges : List DelegationBlame
  audit : List AuditAttributionEntry
  /-- Durable checkpoints, newest first. -/
  snapshots : List FrozenGrain

/-- No grains, nothing revoked, an empty graph. -/
def genesis (users : List Nat) (facts : Nat → KleenePred3) : PowerboxHost :=
  ⟨users, facts, #[], .empty, .empty, [], CapTP.SortedU64Set.empty, [], [], []⟩

/-- Grain `g` holds `x` in slot `slot`. -/
def HoldsAt (h : PowerboxHost) (g : GrainId) (slot : Nat) (x : HeldCap) : Prop :=
  ∃ gs, h.grains[g]? = some gs ∧ gs.clist[slot]? = some x

/-- The only lookup a turn performs: the acting grain's own slot. -/
def heldAt (h : PowerboxHost) (g : GrainId) (slot : Nat) : Option HeldCap :=
  match h.grains[g]? with
  | some gs => gs.clist[slot]?
  | none => none

theorem heldAt_iff {h : PowerboxHost} {g : GrainId} {slot : Nat} {x : HeldCap} :
    heldAt h g slot = some x ↔ HoldsAt h g slot x := by
  unfold heldAt HoldsAt
  cases h.grains[g]? with
  | none => simp
  | some gs => simp

/-- Append one entry to grain `g`'s c-list. -/
def addCap (h : PowerboxHost) (g : GrainId) (x : HeldCap) : PowerboxHost :=
  { h with grains := h.grains.modify g (fun gs => ⟨gs.clist.push x⟩) }

private theorem lt_of_getElem?_eq_some {α : Type} {xs : Array α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : i < xs.size := by
  by_cases hi : i < xs.size
  · exact hi
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi)] at h
    cases h

theorem holdsAt_addCap {h : PowerboxHost} {g g' : GrainId} {slot : Nat} {x y : HeldCap} :
    HoldsAt (addCap h g x) g' slot y ↔
      HoldsAt h g' slot y ∨
        (g' = g ∧ y = x ∧ ∃ gs, h.grains[g]? = some gs ∧ slot = gs.clist.size) := by
  unfold HoldsAt addCap
  simp only [Array.getElem?_modify]
  constructor
  · rintro ⟨gs', hgs', hs⟩
    by_cases hg : g = g'
    · subst hg
      simp only [↓reduceIte] at hgs'
      obtain ⟨gs, hgs, rfl⟩ := Option.map_eq_some_iff.mp hgs'
      simp only [Array.getElem?_push] at hs
      split at hs
      · rename_i hsz
        cases hs
        exact .inr ⟨rfl, rfl, gs, hgs, hsz⟩
      · exact .inl ⟨gs, hgs, hs⟩
    · simp only [hg, ↓reduceIte] at hgs'
      exact .inl ⟨gs', hgs', hs⟩
  · rintro (⟨gs, hgs, hs⟩ | ⟨rfl, rfl, gs, hgs, rfl⟩)
    · by_cases hg : g = g'
      · subst hg
        refine ⟨⟨gs.clist.push x⟩, by simp only [↓reduceIte, hgs, Option.map_some], ?_⟩
        have hlt := lt_of_getElem?_eq_some hs
        simp only [Array.getElem?_push, Nat.ne_of_lt hlt, ↓reduceIte]
        exact hs
      · exact ⟨gs, by simp only [hg, ↓reduceIte]; exact hgs, hs⟩
    · exact ⟨⟨gs.clist.push y⟩, by simp only [↓reduceIte, hgs, Option.map_some],
        by simp only [Array.getElem?_push, ↓reduceIte]⟩

/-! ## 3. Liveness checks -/

/-- The chain's accumulator under the host's revoked nullifiers and facts. -/
def chainAcc (h : PowerboxHost) (c : CapDescriptor) : Option CapAccumulator :=
  foldChain h.revoked h.facts c.root c.hops

/-- No enclosing membrane is revoked: one binary search per membrane. -/
def membranesLive (h : PowerboxHost) (c : CapDescriptor) : Bool :=
  c.membranes.all (fun m => !h.revokedMembranes.contains m)

/-- The search refines the list reading of the revoked-membrane set. -/
theorem membranesLive_iff (h : PowerboxHost) (c : CapDescriptor) :
    membranesLive h c = true ↔ ∀ m ∈ c.membranes, m ∉ h.revokedMembranes.keys.toList := by
  simp only [membranesLive, List.all_eq_true, Bool.not_eq_true']
  constructor
  · intro hall m hm hin
    have hf := hall m hm
    rw [(h.revokedMembranes.contains_iff m).mpr hin] at hf
    cases hf
  · intro hall m hm
    cases hc : h.revokedMembranes.contains m with
    | false => rfl
    | true => exact absurd ((h.revokedMembranes.contains_iff m).mp hc) (hall m hm)

/-- May be held, delegated and rebound: membranes live and the chain folds. -/
def capAdmissible (h : PowerboxHost) (c : CapDescriptor) : Bool :=
  membranesLive h c && (chainAcc h c).isSome

/-- May be invoked for the rights `need`. -/
def capLive (h : PowerboxHost) (c : CapDescriptor) (need : UInt64) : Bool :=
  membranesLive h c &&
    match chainAcc h c with
    | some acc => authorize acc need
    | none => false

theorem capAdmissible_iff {h : PowerboxHost} {c : CapDescriptor} :
    capAdmissible h c = true ↔
      (∀ m ∈ c.membranes, m ∉ h.revokedMembranes.keys.toList) ∧ (chainAcc h c).isSome = true := by
  simp only [capAdmissible, Bool.and_eq_true, membranesLive_iff]

theorem membranesLive_false_of_mem {h : PowerboxHost} {c : CapDescriptor} {m : MembraneId}
    (hm : m ∈ c.membranes) (hr : h.revokedMembranes.contains m = true) :
    membranesLive h c = false := by
  cases hl : membranesLive h c with
  | false => rfl
  | true =>
    exact absurd ((h.revokedMembranes.contains_iff m).mp hr) ((membranesLive_iff h c).mp hl m hm)

/-! ## 4. Freeze and thaw -/

def freezeGrain (h : PowerboxHost) (g : GrainId) : Option FrozenGrain :=
  match h.grains[g]? with
  | some gs => some ⟨g, gs.clist.map fun x => ⟨x.petname, x.via, x.cap, x.cap.digest⟩⟩
  | none => none

theorem freezeGrain_eq_some {h : PowerboxHost} {g : GrainId} {fz : FrozenGrain}
    (hf : freezeGrain h g = some fz) :
    ∃ gs, h.grains[g]? = some gs ∧
      fz = ⟨g, gs.clist.map fun x => ⟨x.petname, x.via, x.cap, x.cap.digest⟩⟩ := by
  unfold freezeGrain at hf
  split at hf
  · rename_i gs hgs
    cases hf
    exact ⟨gs, hgs, rfl⟩
  · cases hf

/-- The durable graph has an edge committing this capability to this grain from this delegator.
The snapshot is not trusted for it. -/
def committedTo (h : PowerboxHost) (g : GrainId) (fr : FrozenRef) : Bool :=
  h.edges.any fun e =>
    e.childCapDigest == fr.commitment && e.delegatee == .grain g && e.delegator == fr.via

theorem committedTo_iff {h : PowerboxHost} {g : GrainId} {fr : FrozenRef} :
    committedTo h g fr = true ↔
      ∃ e ∈ h.edges, e.childCapDigest = fr.commitment ∧ e.delegatee = .grain g ∧
        e.delegator = fr.via := by
  simp only [committedTo, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- Rebind one frozen reference against the host as it is now. -/
def thawRef (h : PowerboxHost) (g : GrainId) (fr : FrozenRef) : Option HeldCap :=
  if fr.commitment == fr.cap.digest && committedTo h g fr && capAdmissible h fr.cap then
    some ⟨fr.cap, fr.via, fr.petname⟩
  else none

def thawGrain (h : PowerboxHost) (fz : FrozenGrain) : GrainState :=
  ⟨fz.refs.filterMap (thawRef h fz.grain)⟩

theorem thawRef_eq_some {h : PowerboxHost} {g : GrainId} {fr : FrozenRef} {x : HeldCap} :
    thawRef h g fr = some x ↔
      x = ⟨fr.cap, fr.via, fr.petname⟩ ∧ fr.commitment = fr.cap.digest ∧
      (∃ e ∈ h.edges, e.childCapDigest = fr.commitment ∧ e.delegatee = .grain g ∧
        e.delegator = fr.via) ∧
      (chainAcc h fr.cap).isSome = true ∧
      ∀ m ∈ fr.cap.membranes, m ∉ h.revokedMembranes.keys.toList := by
  by_cases hc : (fr.commitment == fr.cap.digest && committedTo h g fr &&
      capAdmissible h fr.cap) = true
  · have hc' := hc
    simp only [Bool.and_eq_true, beq_iff_eq, committedTo_iff, capAdmissible_iff] at hc'
    simp only [thawRef, hc, ↓reduceIte, Option.some.injEq]
    constructor
    · intro e
      exact ⟨e.symm, hc'.1.1, hc'.1.2, hc'.2.2, hc'.2.1⟩
    · intro e
      exact e.1.symm
  · simp only [thawRef, hc]
    constructor
    · intro e
      cases e
    · rintro ⟨-, h1, h2, h3, h4⟩
      refine absurd ?_ hc
      simp only [Bool.and_eq_true, beq_iff_eq, committedTo_iff, capAdmissible_iff]
      exact ⟨⟨h1, h2⟩, h4, h3⟩

/-! ## 5. Turns and the step -/

inductive PowerboxTurn where
  /-- A new grain with an empty c-list. -/
  | spawn
  /-- A powerbox user hands grain `to` a root capability under a petname. -/
  | grant (user : Nat) (to : GrainId) (petname : String) (root : Block) (wrap : Option MembraneId)
  /-- Grain `src` introduces `dst` to an attenuation of its slot `slot`. Arguments and results
  cross a membrane the same way: the child keeps every membrane of the parent. -/
  | delegate (src : GrainId) (slot : Nat) (dst : GrainId) (petname : String) (hop : Block)
      (wrap : Option MembraneId) (gift : UInt64)
  | invoke (g : GrainId) (slot : Nat) (need : UInt64) (action : ByteArray)
  | revokeMembrane (actor : PrincipalId) (m : MembraneId)
  | revokeLineage (user : Nat) (nullifier : Nat)
  /-- Write grain `g`'s c-list to durable storage. -/
  | checkpoint (g : GrainId)
  /-- Grain `g` crashed: its c-list is rebuilt by thawing its last checkpoint. -/
  | restart (g : GrainId)

variable {h h' h₀ h₁ h₂ h₃ : PowerboxHost} {ts ts₁ ts₂ : List PowerboxTurn} {t : PowerboxTurn}
  {g g' src dst : GrainId} {slot u : Nat} {x y : HeldCap} {c : CapDescriptor} {m : MembraneId}
  {actor via : PrincipalId} {pet : String} {root hop : Block} {wrap : Option MembraneId}
  {gift need : UInt64} {action : ByteArray} {fz : FrozenGrain} {fr : FrozenRef}
  {path : List (GrainId × CapDescriptor)}

/-- A wrapping membrane is new, and then owned by `p`, or already owned by `p`. -/
def claimMembrane (owners : List (MembraneId × PrincipalId)) (p : PrincipalId) :
    Option MembraneId → Option (List (MembraneId × PrincipalId))
  | none => some owners
  | some m =>
    match owners.lookup m with
    | none => some ((m, p) :: owners)
    | some q => if q = p then some owners else none

/-- Grain `g` exists and has no entry named `pet`. -/
def petnameFresh (h : PowerboxHost) (g : GrainId) (pet : String) : Bool :=
  match h.grains[g]? with
  | some gs => gs.clist.all (fun x => x.petname != pet)
  | none => false

def grantEdge (u : Nat) (g : GrainId) (c : CapDescriptor) : DelegationBlame :=
  ⟨.user u, .grain g, c.digest, c.digest, c.membranes⟩

def delegationEdge (src dst : GrainId) (parent child : CapDescriptor) : DelegationBlame :=
  ⟨.grain src, .grain dst, parent.digest, child.digest, child.membranes⟩

/-- What the recipient of a delegation holds: the child, and the delegating grain as `via`. -/
def delegatedEntry (src : GrainId) (child : CapDescriptor) (pet : String) : HeldCap :=
  ⟨child, .grain src, pet⟩

def auditEntry (g : GrainId) (x : HeldCap) (action : ByteArray) : AuditAttributionEntry :=
  ⟨.grain g, x.via, x.cap.digest, actionDigest action⟩

def stepPowerboxHost (h : PowerboxHost) : PowerboxTurn → Option PowerboxHost
  | .spawn => some { h with grains := h.grains.push ⟨#[]⟩ }
  | .grant u g pet root wrap =>
    match claimMembrane h.membraneOwners (.user u) wrap with
    | none => none
    | some owners =>
      if h.users.contains u && petnameFresh h g pet && capAdmissible h (rootCap root wrap) then
        some (addCap { h with membraneOwners := owners,
                              edges := grantEdge u g (rootCap root wrap) :: h.edges }
          g ⟨rootCap root wrap, .user u, pet⟩)
      else none
  | .delegate src slot dst pet hop wrap gift =>
    match heldAt h src slot with
    | none => none
    | some x =>
      match claimMembrane h.membraneOwners (.grain src) wrap with
      | none => none
      | some owners =>
        if petnameFresh h dst pet && capAdmissible h (x.cap.extend hop wrap) &&
            !h.giftsSpent.contains gift then
          some (addCap
            { h with membraneOwners := owners,
                     giftsSpent := h.giftsSpent.insert gift,
                     edges := delegationEdge src dst x.cap (x.cap.extend hop wrap) :: h.edges }
            dst (delegatedEntry src (x.cap.extend hop wrap) pet))
        else none
  | .invoke g slot need action =>
    match heldAt h g slot with
    | none => none
    | some x =>
      if capLive h x.cap need then some { h with audit := auditEntry g x action :: h.audit }
      else none
  | .revokeMembrane actor m =>
    if h.membraneOwners.lookup m = some actor then
      some { h with revokedMembranes := h.revokedMembranes.insert m }
    else none
  | .revokeLineage u x =>
    if h.users.contains u then some { h with revoked := h.revoked.insert x } else none
  | .checkpoint g =>
    match freezeGrain h g with
    | none => none
    | some fz => some { h with snapshots := fz :: h.snapshots }
  | .restart g =>
    match h.snapshots.find? (fun fz => fz.grain == g) with
    | none => none
    | some fz => some { h with grains := h.grains.modify g (fun _ => thawGrain h fz) }

/-- `h'` is reached from `h` by the turns, in order. -/
def ValidPowerboxTrace : PowerboxHost → List PowerboxTurn → PowerboxHost → Prop
  | h, [], h' => h' = h
  | h, t :: ts, h' => ∃ h₁, stepPowerboxHost h t = some h₁ ∧ ValidPowerboxTrace h₁ ts h'

/-- The runner: one left fold over an array of turns. -/
def runPowerbox (h : PowerboxHost) (turns : Array PowerboxTurn) : Option PowerboxHost :=
  turns.foldlM stepPowerboxHost h

theorem runPowerbox_iff (h : PowerboxHost) (turns : Array PowerboxTurn) (h' : PowerboxHost) :
    runPowerbox h turns = some h' ↔ ValidPowerboxTrace h turns.toList h' := by
  unfold runPowerbox
  rw [← Array.foldlM_toList]
  generalize turns.toList = ts
  induction ts generalizing h with
  | nil =>
    simp only [List.foldlM_nil, ValidPowerboxTrace]
    constructor
    · intro e; cases e; rfl
    · intro e; rw [e]; rfl
  | cons t ts ih =>
    rw [foldlM_cons_some]
    simp only [ValidPowerboxTrace]
    constructor
    · rintro ⟨h₁, hs, hr⟩; exact ⟨h₁, hs, (ih h₁).mp hr⟩
    · rintro ⟨h₁, hs, hr⟩; exact ⟨h₁, hs, (ih h₁).mpr hr⟩

/-! ### What a successful turn did -/

theorem step_grant (hs : stepPowerboxHost h (.grant u g pet root wrap) = some h') :
    ∃ owners, claimMembrane h.membraneOwners (.user u) wrap = some owners ∧
      h.users.contains u = true ∧ petnameFresh h g pet = true ∧
      capAdmissible h (rootCap root wrap) = true ∧
      h' = addCap { h with membraneOwners := owners,
                           edges := grantEdge u g (rootCap root wrap) :: h.edges }
        g ⟨rootCap root wrap, .user u, pet⟩ := by
  simp only [stepPowerboxHost] at hs
  split at hs
  · cases hs
  · rename_i owners ho
    split at hs
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      cases hs
      exact ⟨owners, ho, hc.1.1, hc.1.2, hc.2, rfl⟩
    · cases hs

theorem step_delegate
    (hs : stepPowerboxHost h (.delegate src slot dst pet hop wrap gift) = some h') :
    ∃ x owners, HoldsAt h src slot x ∧
      claimMembrane h.membraneOwners (.grain src) wrap = some owners ∧
      petnameFresh h dst pet = true ∧ capAdmissible h (x.cap.extend hop wrap) = true ∧
      h.giftsSpent.contains gift = false ∧
      h' = addCap
        { h with membraneOwners := owners,
                 giftsSpent := h.giftsSpent.insert gift,
                 edges := delegationEdge src dst x.cap (x.cap.extend hop wrap) :: h.edges }
        dst (delegatedEntry src (x.cap.extend hop wrap) pet) := by
  simp only [stepPowerboxHost] at hs
  split at hs
  · cases hs
  · rename_i x hx
    split at hs
    · cases hs
    · rename_i owners ho
      split at hs
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        cases hs
        exact ⟨x, owners, heldAt_iff.mp hx, ho, hc.1.1, hc.1.2, hc.2, rfl⟩
      · cases hs

theorem step_invoke (hs : stepPowerboxHost h (.invoke g slot need action) = some h') :
    ∃ x, HoldsAt h g slot x ∧ capLive h x.cap need = true ∧
      h' = { h with audit := auditEntry g x action :: h.audit } := by
  simp only [stepPowerboxHost] at hs
  split at hs
  · cases hs
  · rename_i x hx
    split at hs
    · rename_i hc
      cases hs
      exact ⟨x, heldAt_iff.mp hx, hc, rfl⟩
    · cases hs

theorem step_revokeMembrane (hs : stepPowerboxHost h (.revokeMembrane actor m) = some h') :
    h.membraneOwners.lookup m = some actor ∧
      h' = { h with revokedMembranes := h.revokedMembranes.insert m } := by
  simp only [stepPowerboxHost] at hs
  split at hs
  · rename_i hc
    cases hs
    exact ⟨hc, rfl⟩
  · cases hs

theorem step_revokeLineage {u x : Nat}
    (hs : stepPowerboxHost h (.revokeLineage u x) = some h') :
    h.users.contains u = true ∧ h' = { h with revoked := h.revoked.insert x } := by
  simp only [stepPowerboxHost] at hs
  split at hs
  · rename_i hc
    cases hs
    exact ⟨hc, rfl⟩
  · cases hs

theorem step_checkpoint (hs : stepPowerboxHost h (.checkpoint g) = some h') :
    ∃ fz, freezeGrain h g = some fz ∧ h' = { h with snapshots := fz :: h.snapshots } := by
  simp only [stepPowerboxHost] at hs
  split at hs
  · cases hs
  · rename_i fz hf
    cases hs
    exact ⟨fz, hf, rfl⟩

theorem step_restart (hs : stepPowerboxHost h (.restart g) = some h') :
    ∃ fz, h.snapshots.find? (fun fz => fz.grain == g) = some fz ∧
      h' = { h with grains := h.grains.modify g (fun _ => thawGrain h fz) } := by
  simp only [stepPowerboxHost] at hs
  split at hs
  · cases hs
  · rename_i fz hf
    cases hs
    exact ⟨fz, hf, rfl⟩

theorem holdsAt_spawn :
    HoldsAt { h with grains := h.grains.push ⟨#[]⟩ } g slot x ↔ HoldsAt h g slot x := by
  unfold HoldsAt
  simp only [Array.getElem?_push]
  constructor
  · rintro ⟨gs, hgs, hx⟩
    split at hgs
    · cases hgs
      simp at hx
    · exact ⟨gs, hgs, hx⟩
  · rintro ⟨gs, hgs, hx⟩
    refine ⟨gs, ?_, hx⟩
    simp only [Nat.ne_of_lt (lt_of_getElem?_eq_some hgs), ↓reduceIte]
    exact hgs

/-! ## 6. What turns never undo -/

/-- `h'` extends `h`: same users, and nothing committed, logged, revoked or spent in `h`
is missing from `h'`. C-lists are not in this order: a restart can shrink one. -/
structure HostExt (h h' : PowerboxHost) : Prop where
  users : h'.users = h.users
  edges : ∀ e ∈ h.edges, e ∈ h'.edges
  membranes : ∀ m, h.revokedMembranes.contains m = true → h'.revokedMembranes.contains m = true
  revoked : ∀ x, h.revoked.contains x = true → h'.revoked.contains x = true
  gifts : ∀ k, h.giftsSpent.spec k → h'.giftsSpent.spec k
  audit : ∀ e ∈ h.audit, e ∈ h'.audit

theorem HostExt.refl (h : PowerboxHost) : HostExt h h :=
  ⟨rfl, fun _ he => he, fun _ hm => hm, fun _ hr => hr, fun _ hk => hk, fun _ he => he⟩

theorem HostExt.trans {a b c : PowerboxHost} (hab : HostExt a b) (hbc : HostExt b c) :
    HostExt a c :=
  ⟨hbc.users.trans hab.users,
    fun e he => hbc.edges e (hab.edges e he),
    fun m hm => hbc.membranes m (hab.membranes m hm),
    fun x hr => hbc.revoked x (hab.revoked x hr),
    fun k hk => hbc.gifts k (hab.gifts k hk),
    fun e he => hbc.audit e (hab.audit e he)⟩

theorem hostExt_addCap (h : PowerboxHost) (g : GrainId) (x : HeldCap) :
    HostExt h (addCap h g x) :=
  ⟨rfl, fun _ he => he, fun _ hm => hm, fun _ hr => hr, fun _ hk => hk, fun _ he => he⟩

theorem step_ext (hs : stepPowerboxHost h t = some h') : HostExt h h' := by
  cases t with
  | spawn =>
    simp only [stepPowerboxHost, Option.some.injEq] at hs
    subst hs
    exact ⟨rfl, fun _ he => he, fun _ hm => hm, fun _ hr => hr, fun _ hk => hk, fun _ he => he⟩
  | grant u g pet root wrap =>
    obtain ⟨owners, -, -, -, -, rfl⟩ := step_grant hs
    exact ⟨rfl, fun _ he => List.mem_cons_of_mem _ he, fun _ hm => hm, fun _ hr => hr,
      fun _ hk => hk, fun _ he => he⟩
  | delegate src slot dst pet hop wrap gift =>
    obtain ⟨x, owners, -, -, -, -, -, rfl⟩ := step_delegate hs
    exact ⟨rfl, fun _ he => List.mem_cons_of_mem _ he, fun _ hm => hm, fun _ hr => hr,
      fun k hk => (CapTP.SortedU64Set.spec_insert _ _ _).mpr (.inr hk), fun _ he => he⟩
  | invoke g slot need action =>
    obtain ⟨x, -, -, rfl⟩ := step_invoke hs
    exact ⟨rfl, fun _ he => he, fun _ hm => hm, fun _ hr => hr, fun _ hk => hk,
      fun _ he => List.mem_cons_of_mem _ he⟩
  | revokeMembrane actor m =>
    obtain ⟨-, rfl⟩ := step_revokeMembrane hs
    exact ⟨rfl, fun _ he => he, fun m' hm => (RevokedSet.contains_insert _ _ _).mpr (.inr hm),
      fun _ hr => hr, fun _ hk => hk, fun _ he => he⟩
  | revokeLineage u x =>
    obtain ⟨-, rfl⟩ := step_revokeLineage hs
    exact ⟨rfl, fun _ he => he, fun _ hm => hm,
      fun y hr => (RevokedSet.contains_insert _ _ _).mpr (.inr hr), fun _ hk => hk, fun _ he => he⟩
  | checkpoint g =>
    obtain ⟨fz, -, rfl⟩ := step_checkpoint hs
    exact ⟨rfl, fun _ he => he, fun _ hm => hm, fun _ hr => hr, fun _ hk => hk, fun _ he => he⟩
  | restart g =>
    obtain ⟨fz, -, rfl⟩ := step_restart hs
    exact ⟨rfl, fun _ he => he, fun _ hm => hm, fun _ hr => hr, fun _ hk => hk, fun _ he => he⟩

theorem trace_ext (ht : ValidPowerboxTrace h ts h') : HostExt h h' := by
  induction ts generalizing h with
  | nil =>
    simp only [ValidPowerboxTrace] at ht
    subst ht
    exact HostExt.refl _
  | cons t ts ih =>
    simp only [ValidPowerboxTrace] at ht
    obtain ⟨h₁, hs, hr⟩ := ht
    exact (step_ext hs).trans (ih hr)

/-! ## 7. Provenance and the accountability invariant -/

/-- Derivability in the committed graph. `Provenance h g c via path`: grain `g` came by `c` from
`via`, and `path` lists every holder and capability from `(g, c)` back to a user's grant. It reads
the users and the edges only, so it survives a restart. -/
inductive Provenance (h : PowerboxHost) :
    GrainId → CapDescriptor → PrincipalId → List (GrainId × CapDescriptor) → Prop where
  | granted {u : Nat} {g : GrainId} {c : CapDescriptor} :
      u ∈ h.users → c.hops = #[] →
      (⟨.user u, .grain g, c.digest, c.digest, c.membranes⟩ : DelegationBlame) ∈ h.edges →
      Provenance h g c (.user u) [(g, c)]
  | delegated {src dst : GrainId} {parent child : CapDescriptor} {via : PrincipalId}
      {path : List (GrainId × CapDescriptor)} :
      Provenance h src parent via path → Extends child parent →
      (⟨.grain src, .grain dst, parent.digest, child.digest, child.membranes⟩ :
        DelegationBlame) ∈ h.edges →
      Provenance h dst child (.grain src) ((dst, child) :: path)

theorem Provenance.mono (hp : Provenance h g c via path) (hu : h'.users = h.users)
    (he : ∀ e ∈ h.edges, e ∈ h'.edges) : Provenance h' g c via path := by
  induction hp with
  | granted hmem hh hin => exact .granted (hu ▸ hmem) hh (he _ hin)
  | delegated _ hext hin ih => exact .delegated ih hext (he _ hin)

/-- A path begins at the capability it is a path for. -/
theorem Provenance.head_mem (hp : Provenance h g c via path) : (g, c) ∈ path := by
  cases hp with
  | granted _ _ _ => exact List.mem_singleton.mpr rfl
  | delegated _ _ _ => exact List.mem_cons_self ..

/-- Membranes only accumulate along a path. -/
theorem Provenance.membranes (hp : Provenance h g c via path) :
    ∀ a ∈ path, ∀ m ∈ a.2.membranes, m ∈ c.membranes := by
  induction hp with
  | granted _ _ _ =>
    intro a ha m hm
    rw [List.mem_singleton.mp ha] at hm
    exact hm
  | delegated _ hext _ ih =>
    intro a ha m hm
    rcases List.mem_cons.mp ha with rfl | hin
    · exact hm
    · obtain ⟨-, -, wrap, hw⟩ := hext
      rw [hw]
      exact List.mem_append_right _ (ih a hin m hm)

/-- Every capability on a path is a prefix of the chain at its end. -/
theorem Provenance.chain_prefix (hp : Provenance h g c via path) :
    ∀ a ∈ path, a.2.root = c.root ∧ ∃ ext, c.hops = a.2.hops ++ ext := by
  induction hp with
  | granted _ _ _ =>
    intro a ha
    rw [List.mem_singleton.mp ha]
    exact ⟨rfl, #[], (Array.append_empty).symm⟩
  | delegated _ hext _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hin
    · exact ⟨rfl, #[], (Array.append_empty).symm⟩
    · obtain ⟨hroot, ⟨hop, hhops⟩, -⟩ := hext
      obtain ⟨hr, ext, he⟩ := ih a hin
      refine ⟨hr.trans hroot.symm, ext.push hop, ?_⟩
      rw [hhops, he, Array.push_eq_append, Array.push_eq_append, Array.append_assoc]

/-- A path starts at a root capability that a powerbox user granted. -/
theorem Provenance.grant_root (hp : Provenance h g c via path) :
    ∃ u g₀ c₀, u ∈ h.users ∧ (g₀, c₀) ∈ path ∧ c₀.hops = #[] ∧
      (⟨.user u, .grain g₀, c₀.digest, c₀.digest, c₀.membranes⟩ : DelegationBlame) ∈ h.edges := by
  induction hp with
  | granted hu hh he => exact ⟨_, _, _, hu, List.mem_singleton.mpr rfl, hh, he⟩
  | delegated _ _ _ ih =>
    obtain ⟨u, g₀, c₀, hu, hin, hh, he⟩ := ih
    exact ⟨u, g₀, c₀, hu, List.mem_cons_of_mem _ hin, hh, he⟩

/-- The last step of a path is an edge whose delegator is the recorded `via`, and that delegator
was a powerbox user or a grain with its own provenance for the edge's parent. -/
theorem Provenance.edge (hp : Provenance h g c via path) :
    ∃ e ∈ h.edges, e.delegator = via ∧ e.delegatee = .grain g ∧ e.childCapDigest = c.digest ∧
      e.membraneLineage = c.membranes ∧
      ((∃ u, via = .user u ∧ u ∈ h.users) ∨
        ∃ src parent via' path', via = .grain src ∧ Provenance h src parent via' path' ∧
          parent.digest = e.parentCapDigest) := by
  cases hp with
  | granted hu _ he => exact ⟨_, he, rfl, rfl, rfl, rfl, .inl ⟨_, rfl, hu⟩⟩
  | delegated hpar _ he => exact ⟨_, he, rfl, rfl, rfl, rfl, .inr ⟨_, _, _, _, rfl, hpar, rfl⟩⟩

/-- The invariant the trace theorems carry. -/
structure Accountable (h : PowerboxHost) : Prop where
  /-- Every held capability has a provenance path whose last delegator is its recorded `via`. -/
  grounded : ∀ g slot x, HoldsAt h g slot x → ∃ path, Provenance h g x.cap x.via path
  /-- Every logged invocation names an invoker, its delegator and a capability with provenance. -/
  audited : ∀ e ∈ h.audit, ∃ g c path, Provenance h g c e.viaWhichDelegator path ∧
    e.whoInvoked = .grain g ∧ e.capDigest = c.digest
  /-- Petnames are distinct within a grain. -/
  petnames : ∀ (g : GrainId) (gs : GrainState), h.grains[g]? = some gs →
    (gs.clist.toList.map (·.petname)).Nodup
  /-- Every checkpointed reference has provenance, and checkpointed petnames are distinct. -/
  frozen : ∀ fz ∈ h.snapshots, (∀ fr ∈ fz.refs, ∃ path, Provenance h fz.grain fr.cap fr.via path) ∧
    (fz.refs.toList.map (·.petname)).Nodup

theorem genesis_accountable (users : List Nat) (facts : Nat → KleenePred3) :
    Accountable (genesis users facts) := by
  refine ⟨fun g slot x hh => ?_, fun e he => ?_, fun g gs hg => ?_, fun fz hfz => ?_⟩
  · obtain ⟨gs, hgs, -⟩ := hh
    simp [genesis] at hgs
  · simp [genesis] at he
  · simp [genesis] at hg
  · simp [genesis] at hfz

theorem petnameFresh_iff :
    petnameFresh h g pet = true ↔
      ∃ gs, h.grains[g]? = some gs ∧ ∀ x ∈ gs.clist, x.petname ≠ pet := by
  unfold petnameFresh
  cases h.grains[g]? with
  | none => simp
  | some gs =>
    show gs.clist.all _ = true ↔ _
    constructor
    · intro hall
      exact ⟨gs, rfl, fun x hx => by simpa using Array.all_eq_true_iff_forall_mem.mp hall x hx⟩
    · rintro ⟨gs', hgs', hne⟩
      cases hgs'
      exact Array.all_eq_true_iff_forall_mem.mpr fun x hx => by simpa using hne x hx

/-- The invariant moves along an extension once the new holdings, log entries and checkpoints are
backed by provenance in the old host. -/
theorem Accountable.rebase (ha : Accountable h) (hx : HostExt h h')
    (hgr : ∀ g slot x, HoldsAt h' g slot x → ∃ path, Provenance h g x.cap x.via path)
    (haud : ∀ e ∈ h'.audit, e ∈ h.audit ∨ ∃ g c path, Provenance h g c e.viaWhichDelegator path ∧
      e.whoInvoked = .grain g ∧ e.capDigest = c.digest)
    (hpet : ∀ (g : GrainId) (gs : GrainState), h'.grains[g]? = some gs →
      (gs.clist.toList.map (·.petname)).Nodup)
    (hfz : ∀ fz ∈ h'.snapshots,
      (∀ fr ∈ fz.refs, ∃ path, Provenance h fz.grain fr.cap fr.via path) ∧
        (fz.refs.toList.map (·.petname)).Nodup) : Accountable h' := by
  refine ⟨fun g slot x hh => ?_, fun e he => ?_, hpet, fun fz hin => ?_⟩
  · exact (hgr g slot x hh).elim fun p hp => ⟨p, hp.mono hx.users hx.edges⟩
  · have hback : ∃ g c path, Provenance h g c e.viaWhichDelegator path ∧
        e.whoInvoked = .grain g ∧ e.capDigest = c.digest :=
      (haud e he).elim (ha.audited e) id
    obtain ⟨g, c, p, hp, r⟩ := hback
    exact ⟨g, c, p, hp.mono hx.users hx.edges, r⟩
  · obtain ⟨hpr, hnd⟩ := hfz fz hin
    exact ⟨fun fr hfr => (hpr fr hfr).elim fun p hp => ⟨p, hp.mono hx.users hx.edges⟩, hnd⟩

/-- Adding a provenanced entry under a fresh petname keeps the invariant. -/
theorem Accountable.addCap (ha : Accountable h) (hfresh : petnameFresh h g x.petname = true)
    (hprov : ∃ path, Provenance h g x.cap x.via path) :
    Accountable (GrainPowerbox.addCap h g x) := by
  refine ha.rebase (hostExt_addCap h g x) (fun g' slot y hh => ?_) (fun e he => .inl he)
    (fun g' gs' hg' => ?_) ha.frozen
  · rcases holdsAt_addCap.mp hh with hold | ⟨rfl, rfl, -⟩
    · exact ha.grounded g' slot y hold
    · exact hprov
  · obtain ⟨gs, hgs, hne⟩ := petnameFresh_iff.mp hfresh
    have hg'' : (h.grains.modify g (fun gs => ⟨gs.clist.push x⟩))[g']? = some gs' := hg'
    rw [Array.getElem?_modify] at hg''
    by_cases hgg : g = g'
    · subst hgg
      simp only [↓reduceIte, hgs, Option.map_some, Option.some.injEq] at hg''
      subst hg''
      simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr
        ⟨ha.petnames g gs hgs, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro a ha' b hb
      rw [List.mem_singleton.mp hb]
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha'
      exact hne y (Array.mem_toList_iff.mp hy)
    · simp only [hgg, ↓reduceIte] at hg''
      exact ha.petnames g' gs' hg''

/-- Thawing keeps a sublist of the frozen petnames. -/
theorem thaw_petnames_sublist (h : PowerboxHost) (g : GrainId) (refs : List FrozenRef) :
    ((refs.filterMap (thawRef h g)).map (·.petname)).Sublist (refs.map (·.petname)) := by
  induction refs with
  | nil => exact .slnil
  | cons fr rest ih =>
    simp only [List.filterMap_cons]
    cases hth : thawRef h g fr with
    | none => exact ih.cons _
    | some x =>
      have hx : x.petname = fr.petname := by rw [(thawRef_eq_some.mp hth).1]
      simp only [List.map_cons, hx]
      exact ih.cons_cons _

theorem step_accountable (ha : Accountable h) (hs : stepPowerboxHost h t = some h') :
    Accountable h' := by
  have hx := step_ext hs
  cases t with
  | spawn =>
    simp only [stepPowerboxHost, Option.some.injEq] at hs
    subst hs
    refine ha.rebase hx (fun g slot x hh => ha.grounded g slot x (holdsAt_spawn.mp hh))
      (fun e he => .inl he) (fun g gs hg => ?_) ha.frozen
    simp only [Array.getElem?_push] at hg
    split at hg
    · cases hg
      exact List.nodup_nil
    · exact ha.petnames g gs hg
  | grant u g pet root wrap =>
    obtain ⟨owners, -, hu, hfresh, -, rfl⟩ := step_grant hs
    have hx₁ : HostExt h
        { h with membraneOwners := owners,
                 edges := grantEdge u g (rootCap root wrap) :: h.edges } :=
      ⟨rfl, fun _ he => List.mem_cons_of_mem _ he, fun _ hm => hm, fun _ hr => hr,
        fun _ hk => hk, fun _ he => he⟩
    exact (ha.rebase hx₁ ha.grounded (fun e he => .inl he) ha.petnames ha.frozen).addCap
      (x := ⟨rootCap root wrap, .user u, pet⟩) hfresh
      ⟨_, .granted (List.contains_iff_mem.mp hu) rfl (List.mem_cons_self ..)⟩
  | delegate src slot dst pet hop wrap gift =>
    obtain ⟨x, owners, hheld, -, hfresh, -, -, rfl⟩ := step_delegate hs
    have hx₁ : HostExt h
        { h with membraneOwners := owners,
                 giftsSpent := h.giftsSpent.insert gift,
                 edges := delegationEdge src dst x.cap (x.cap.extend hop wrap) :: h.edges } :=
      ⟨rfl, fun _ he => List.mem_cons_of_mem _ he, fun _ hm => hm, fun _ hr => hr,
        fun k hk => (CapTP.SortedU64Set.spec_insert _ _ _).mpr (.inr hk), fun _ he => he⟩
    obtain ⟨p, hp⟩ := ha.grounded src slot x hheld
    exact (ha.rebase hx₁ ha.grounded (fun e he => .inl he) ha.petnames ha.frozen).addCap
      (x := delegatedEntry src (x.cap.extend hop wrap) pet) hfresh
      ⟨_, .delegated (hp.mono hx₁.users hx₁.edges) (extend_extends _ _ _) (List.mem_cons_self ..)⟩
  | invoke g slot need action =>
    obtain ⟨x, hheld, -, rfl⟩ := step_invoke hs
    refine ha.rebase hx ha.grounded (fun e he => ?_) ha.petnames ha.frozen
    rcases List.mem_cons.mp he with rfl | hin
    · exact (ha.grounded g slot x hheld).elim fun p hp => .inr ⟨g, x.cap, p, hp, rfl, rfl⟩
    · exact .inl hin
  | revokeMembrane actor m =>
    obtain ⟨-, rfl⟩ := step_revokeMembrane hs
    exact ha.rebase hx ha.grounded (fun e he => .inl he) ha.petnames ha.frozen
  | revokeLineage u x =>
    obtain ⟨-, rfl⟩ := step_revokeLineage hs
    exact ha.rebase hx ha.grounded (fun e he => .inl he) ha.petnames ha.frozen
  | checkpoint g =>
    obtain ⟨fz, hf, rfl⟩ := step_checkpoint hs
    obtain ⟨gs, hgs, rfl⟩ := freezeGrain_eq_some hf
    refine ha.rebase hx ha.grounded (fun e he => .inl he) ha.petnames fun fz hfz => ?_
    rcases List.mem_cons.mp hfz with rfl | hold
    · refine ⟨fun fr hfr => ?_, ?_⟩
      · obtain ⟨x, hxm, rfl⟩ := Array.mem_map.mp hfr
        obtain ⟨slot, hslot⟩ := Array.mem_iff_getElem?.mp hxm
        exact ha.grounded g slot x ⟨gs, hgs, hslot⟩
      · simp only [Array.toList_map, List.map_map]
        exact ha.petnames g gs hgs
    · exact ha.frozen fz hold
  | restart g =>
    obtain ⟨fz, hfind, rfl⟩ := step_restart hs
    have hgr : fz.grain = g := by simpa using List.find?_some hfind
    obtain ⟨hpr, hnd⟩ := ha.frozen fz (List.mem_of_find?_eq_some hfind)
    refine ha.rebase hx (fun g' slot x hh => ?_) (fun e he => .inl he) (fun g' gs' hg' => ?_)
      ha.frozen
    · obtain ⟨gs', hgs', hs'⟩ := hh
      have hgs'' : (h.grains.modify g (fun _ => thawGrain h fz))[g']? = some gs' := hgs'
      rw [Array.getElem?_modify] at hgs''
      by_cases hgg : g = g'
      · subst hgg
        simp only [↓reduceIte] at hgs''
        obtain ⟨gs, -, rfl⟩ := Option.map_eq_some_iff.mp hgs''
        obtain ⟨fr, hfr, hth⟩ := Array.mem_filterMap.mp (Array.mem_iff_getElem?.mpr ⟨slot, hs'⟩)
        obtain ⟨rfl, -⟩ := thawRef_eq_some.mp hth
        exact hgr ▸ hpr fr hfr
      · simp only [hgg, ↓reduceIte] at hgs''
        exact ha.grounded g' slot x ⟨gs', hgs'', hs'⟩
    · have hg'' : (h.grains.modify g (fun _ => thawGrain h fz))[g']? = some gs' := hg'
      rw [Array.getElem?_modify] at hg''
      by_cases hgg : g = g'
      · subst hgg
        simp only [↓reduceIte] at hg''
        obtain ⟨gs, -, rfl⟩ := Option.map_eq_some_iff.mp hg''
        simp only [thawGrain, Array.toList_filterMap]
        exact List.Pairwise.sublist (thaw_petnames_sublist h fz.grain fz.refs.toList) hnd
      · simp only [hgg, ↓reduceIte] at hg''
        exact ha.petnames g' gs' hg''

theorem trace_accountable (ha : Accountable h) (ht : ValidPowerboxTrace h ts h') :
    Accountable h' := by
  induction ts generalizing h with
  | nil =>
    simp only [ValidPowerboxTrace] at ht
    subst ht
    exact ha
  | cons t ts ih =>
    simp only [ValidPowerboxTrace] at ht
    obtain ⟨h₁, hs, hr⟩ := ht
    exact ih (step_accountable ha hs) hr

/-! ## 8. No ambient authority -/

/-- **No ambient authority.** Over any trace from an accountable host, a capability a grain holds
has a provenance path in the committed graph. The path starts at a root capability granted by a
powerbox user. Every capability `a` on it is an ancestor in two senses: each membrane of `a` still
encloses the held capability, and under any revoked set and facts, whenever the held chain folds,
`a`'s chain folds and authorizes everything the held one does. -/
theorem no_ambient_authority_in_grain (hacc : Accountable h₀) (ht : ValidPowerboxTrace h₀ ts h)
    (hheld : HoldsAt h g slot x) :
    ∃ path, Provenance h g x.cap x.via path ∧
      (∃ u g₀ c₀, u ∈ h.users ∧ (g₀, c₀) ∈ path ∧ c₀.hops = #[] ∧
        grantEdge u g₀ c₀ ∈ h.edges) ∧
      ∀ a ∈ path, (∀ m ∈ a.2.membranes, m ∈ x.cap.membranes) ∧
        ∀ (rs : RevokedSet) (env : Nat → KleenePred3) (acc : CapAccumulator),
          foldChain rs env x.cap.root x.cap.hops = some acc →
          ∃ accA, foldChain rs env a.2.root a.2.hops = some accA ∧
            ∀ need, authorize acc need = true → authorize accA need = true := by
  obtain ⟨path, hp⟩ := (trace_accountable hacc ht).grounded g slot x hheld
  refine ⟨path, hp, hp.grant_root, fun a ha => ⟨hp.membranes a ha, fun rs env acc hf => ?_⟩⟩
  obtain ⟨hroot, ext, hext⟩ := hp.chain_prefix a ha
  rw [← hroot, hext] at hf
  obtain ⟨accA, hA, hn, -⟩ := attenuate_monotone_rights rs env a.2.root a.2.hops ext acc hf
  exact ⟨accA, hA, hn⟩

/-! ## 9. Membrane revocation -/

theorem invoke_refused_of_severed (hheld : HoldsAt h g slot x)
    (hdead : membranesLive h x.cap = false) (need : UInt64) (action : ByteArray) :
    stepPowerboxHost h (.invoke g slot need action) = none := by
  simp only [stepPowerboxHost, heldAt_iff.mpr hheld, capLive, hdead, Bool.false_and]
  rfl

theorem delegate_refused_of_severed (hheld : HoldsAt h g slot x) (hm : m ∈ x.cap.membranes)
    (hr : h.revokedMembranes.contains m = true) (dst : GrainId) (pet : String) (hop : Block)
    (wrap : Option MembraneId) (gift : UInt64) :
    stepPowerboxHost h (.delegate g slot dst pet hop wrap gift) = none := by
  have hdead : membranesLive h (x.cap.extend hop wrap) = false :=
    membranesLive_false_of_mem
      ((extend_extends x.cap hop wrap).2.2.elim fun w hw => hw ▸ List.mem_append_right w hm) hr
  simp only [stepPowerboxHost, heldAt_iff.mpr hheld, capAdmissible, hdead, Bool.false_and,
    Bool.and_false]
  cases claimMembrane h.membraneOwners (.grain g) wrap <;> rfl

theorem revokeMembrane_persists (hrev : stepPowerboxHost h₁ (.revokeMembrane actor m) = some h₂)
    (ht : ValidPowerboxTrace h₂ ts h₃) : h₃.revokedMembranes.contains m = true := by
  obtain ⟨-, rfl⟩ := step_revokeMembrane hrev
  exact (trace_ext ht).membranes m (RevokedSet.contains_insert_self _ _)

/-- **One revocation severs the cone.** After `revokeMembrane m`, and after any further turns,
restarts included, take any capability any grain holds. It has a provenance path that begins at
itself, and if any capability on that path (itself, the capability it was delegated from, or any
ancestor at any depth and in any grain) was enclosed by `m`, then every invocation of it and every
delegation from it is refused. The revocation edited no c-list. -/
theorem revokeMembrane_severs_all_transitive_descendants (hacc : Accountable h₀)
    (t₁ : ValidPowerboxTrace h₀ ts₁ h₁)
    (hrev : stepPowerboxHost h₁ (.revokeMembrane actor m) = some h₂)
    (t₂ : ValidPowerboxTrace h₂ ts₂ h₃) (hheld : HoldsAt h₃ g slot x) :
    ∃ path, Provenance h₃ g x.cap x.via path ∧ (g, x.cap) ∈ path ∧
      ((∃ a ∈ path, m ∈ a.2.membranes) →
        (∀ need action, stepPowerboxHost h₃ (.invoke g slot need action) = none) ∧
        ∀ dst pet hop wrap gift,
          stepPowerboxHost h₃ (.delegate g slot dst pet hop wrap gift) = none) := by
  have hacc₃ : Accountable h₃ :=
    trace_accountable (step_accountable (trace_accountable hacc t₁) hrev) t₂
  obtain ⟨path, hp⟩ := hacc₃.grounded g slot x hheld
  refine ⟨path, hp, hp.head_mem, ?_⟩
  rintro ⟨a, ha, hma⟩
  have hm : m ∈ x.cap.membranes := hp.membranes a ha m hma
  have hr := revokeMembrane_persists hrev t₂
  exact ⟨fun need action =>
      invoke_refused_of_severed hheld (membranesLive_false_of_mem hm hr) need action,
    fun dst pet hop wrap gift => delegate_refused_of_severed hheld hm hr dst pet hop wrap gift⟩

private theorem not_mem_contains {ms : List MembraneId} (h : m ∉ ms) :
    ms.contains m = false := by
  cases hc : ms.contains m with
  | false => rfl
  | true => exact absurd (List.contains_iff_mem.mp hc) h

/-- Revoking `m` changes liveness of a capability by exactly the test `m ∈ membranes`. -/
theorem capLive_revokeMembrane (h : PowerboxHost) (m : MembraneId) (c : CapDescriptor)
    (need : UInt64) :
    capLive { h with revokedMembranes := h.revokedMembranes.insert m } c need =
      (capLive h c need && !c.membranes.contains m) := by
  have hml : membranesLive { h with revokedMembranes := h.revokedMembranes.insert m } c =
      (membranesLive h c && !c.membranes.contains m) := by
    by_cases hin : m ∈ c.membranes
    · rw [List.contains_iff_mem.mpr hin, Bool.not_true, Bool.and_false]
      exact membranesLive_false_of_mem hin (RevokedSet.contains_insert_self _ _)
    · rw [not_mem_contains hin, Bool.not_false, Bool.and_true]
      apply Bool.eq_iff_iff.mpr
      simp only [membranesLive, List.all_eq_true, Bool.not_eq_true']
      constructor
      · intro hall m' hm'
        cases hcm : h.revokedMembranes.contains m' with
        | false => rfl
        | true =>
          have hf := hall m' hm'
          rw [(RevokedSet.contains_insert _ _ _).mpr (.inr hcm)] at hf
          cases hf
      · intro hall m' hm'
        cases hcm : (h.revokedMembranes.insert m).contains m' with
        | false => rfl
        | true =>
          rcases (RevokedSet.contains_insert _ _ _).mp hcm with rfl | hold
          · exact absurd hm' hin
          · rw [hall m' hm'] at hold
            cases hold
  have hch : chainAcc { h with revokedMembranes := h.revokedMembranes.insert m } c =
      chainAcc h c := rfl
  simp only [capLive, hml, hch]
  cases membranesLive h c <;> cases c.membranes.contains m <;> simp

/-- **Siblings are untouched.** A capability with no enclosing `m` is invocable after
`revokeMembrane m` exactly when it was before. -/
theorem revokeMembrane_preserves_independent_siblings
    (hrev : stepPowerboxHost h (.revokeMembrane actor m) = some h')
    (hheld : HoldsAt h g slot x) (hm : m ∉ x.cap.membranes) (need : UInt64) (action : ByteArray) :
    (stepPowerboxHost h' (.invoke g slot need action)).isSome =
      (stepPowerboxHost h (.invoke g slot need action)).isSome := by
  obtain ⟨-, rfl⟩ := step_revokeMembrane hrev
  have hheld' : HoldsAt { h with revokedMembranes := h.revokedMembranes.insert m } g slot x :=
    hheld
  have hc : x.cap.membranes.contains m = false := not_mem_contains hm
  simp only [stepPowerboxHost, heldAt_iff.mpr hheld, heldAt_iff.mpr hheld',
    capLive_revokeMembrane, hc, Bool.not_false, Bool.and_true]
  cases capLive h x.cap need <;> rfl

/-! ## 10. Responsibility -/

/-- **Blame is sound.** Over any trace from an accountable host, a logged invocation
`(whoInvoked, viaWhichDelegator, capDigest)` is an edge of the committed graph from that delegator
to that invoker for that capability digest, and the delegator was involved: a powerbox user, or a
grain that itself has provenance for a capability whose digest is the edge's parent. -/
theorem blameAttribution_sound (hacc : Accountable h₀) (ht : ValidPowerboxTrace h₀ ts h)
    (e : AuditAttributionEntry) (he : e ∈ h.audit) :
    ∃ edge ∈ h.edges, edge.delegator = e.viaWhichDelegator ∧ edge.delegatee = e.whoInvoked ∧
      edge.childCapDigest = e.capDigest ∧
      ((∃ u, edge.delegator = .user u ∧ u ∈ h.users) ∨
        ∃ src parent via' path', edge.delegator = .grain src ∧
          Provenance h src parent via' path' ∧ parent.digest = edge.parentCapDigest) := by
  obtain ⟨g, c, path, hp, hw, hd⟩ := (trace_accountable hacc ht).audited e he
  obtain ⟨edge, hin, hdel, hto, hchild, -, hinv⟩ := hp.edge
  refine ⟨edge, hin, hdel, hto.trans hw.symm, hchild.trans hd.symm, ?_⟩
  rw [hdel]
  exact hinv

/-- A principal that is the delegator of no edge is blamed by no log entry. -/
theorem uninvolved_principal_never_blamed (hacc : Accountable h₀)
    (ht : ValidPowerboxTrace h₀ ts h) (p : PrincipalId)
    (hclean : ∀ edge ∈ h.edges, edge.delegator ≠ p) (e : AuditAttributionEntry)
    (he : e ∈ h.audit) : e.viaWhichDelegator ≠ p := by
  obtain ⟨edge, hin, hdel, -⟩ := blameAttribution_sound hacc ht e he
  exact hdel ▸ hclean edge hin

/-! ## 11. Gifts and petnames -/

/-- A gift nullifier spent by one introduction refuses every later introduction that presents
it. -/
theorem gift_never_redeemed_twice
    (hs : stepPowerboxHost h (.delegate src slot dst pet hop wrap gift) = some h₁)
    (ht : ValidPowerboxTrace h₁ ts h₂) (src' dst' : GrainId) (slot' : Nat) (pet' : String)
    (hop' : Block) (wrap' : Option MembraneId) :
    stepPowerboxHost h₂ (.delegate src' slot' dst' pet' hop' wrap' gift) = none := by
  have hspent : h₂.giftsSpent.contains gift = true := by
    obtain ⟨x, owners, -, -, -, -, -, rfl⟩ := step_delegate hs
    exact (h₂.giftsSpent.contains_eq_spec gift).mpr
      ((trace_ext ht).gifts gift ((CapTP.SortedU64Set.spec_insert _ _ _).mpr (.inl rfl)))
  cases hn : stepPowerboxHost h₂ (.delegate src' slot' dst' pet' hop' wrap' gift) with
  | none => rfl
  | some h₃ =>
    obtain ⟨-, -, -, -, -, -, hfree, -⟩ := step_delegate hn
    rw [hspent] at hfree
    cases hfree

/-- The slot a petname names. -/
def GrainState.resolvePetname (gs : GrainState) (pet : String) : Option Nat :=
  gs.clist.findIdx? (fun x => x.petname == pet)

/-- **Petnames and slots correspond.** In an accountable host a slot's petname resolves back to
that slot, and a resolved petname names an entry that carries it. -/
theorem petname_slot_bijection (ha : Accountable h) {gs : GrainState}
    (hg : h.grains[g]? = some gs) (slot : Nat) (pet : String) :
    gs.resolvePetname pet = some slot ↔ ∃ x, gs.clist[slot]? = some x ∧ x.petname = pet := by
  unfold GrainState.resolvePetname
  rw [Array.findIdx?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hlt, hp, -⟩
    exact ⟨gs.clist[slot], Array.getElem?_eq_getElem hlt, by simpa using hp⟩
  · rintro ⟨x, hx, rfl⟩
    have hlt := lt_of_getElem?_eq_some hx
    have hxe : gs.clist[slot] = x := by
      have := Array.getElem?_eq_getElem hlt
      rw [hx] at this
      exact (Option.some.inj this).symm
    refine ⟨hlt, by simp [hxe], fun j hj => ?_⟩
    have hnd := ha.petnames g gs hg
    have hpw := List.pairwise_iff_getElem.mp hnd j slot (by simp; omega) (by simpa using hlt) hj
    simp only [List.getElem_map, Array.getElem_toList, hxe] at hpw
    simpa using hpw

/-! ## 12. Thaw against the durable host -/

/-- **Thaw rebinds exactly the live, committed references.** An entry is in the thawed c-list if
and only if it is a frozen reference whose commitment matches its descriptor and an edge of the
durable graph, whose chain still folds under the host's revoked nullifiers (so neither its root
grant nor any hop has been revoked), and none of whose enclosing membranes is revoked. The host is
the one thaw runs against: every revocation before or during the outage is in it. -/
theorem thaw_never_resurrects_revoked_cap (h : PowerboxHost) (fz : FrozenGrain) (x : HeldCap) :
    x ∈ (thawGrain h fz).clist ↔
      ∃ fr ∈ fz.refs, x = ⟨fr.cap, fr.via, fr.petname⟩ ∧ fr.commitment = fr.cap.digest ∧
        (∃ e ∈ h.edges, e.childCapDigest = fr.commitment ∧ e.delegatee = .grain fz.grain ∧
          e.delegator = fr.via) ∧
        (chainAcc h fr.cap).isSome = true ∧
        ∀ m ∈ fr.cap.membranes, m ∉ h.revokedMembranes.keys.toList := by
  simp only [thawGrain, Array.mem_filterMap, thawRef_eq_some]

/-- A membrane revoked at any point before the thaw refuses every reference it encloses. -/
theorem thaw_refuses_revoked_membrane
    (hrev : stepPowerboxHost h₁ (.revokeMembrane actor m) = some h₂)
    (ht : ValidPowerboxTrace h₂ ts h₃) (g : GrainId) (fr : FrozenRef)
    (hm : m ∈ fr.cap.membranes) : thawRef h₃ g fr = none := by
  cases hth : thawRef h₃ g fr with
  | none => rfl
  | some x =>
    obtain ⟨-, -, -, -, hml⟩ := thawRef_eq_some.mp hth
    exact absurd ((h₃.revokedMembranes.contains_iff m).mp (revokeMembrane_persists hrev ht))
      (hml m hm)

/-- A revoked prefix of the chain, the root grant included (`pre = #[]`), refuses the thaw. -/
theorem thaw_refuses_revoked_lineage (g : GrainId) (fr : FrozenRef) (pre ext : Array Block)
    (hhops : fr.cap.hops = pre ++ ext)
    (hrev : stepPowerboxHost h₁
      (.revokeLineage u (credNul (lineageOf fr.cap.root pre.toList))) = some h₂)
    (ht : ValidPowerboxTrace h₂ ts h₃) : thawRef h₃ g fr = none := by
  cases hth : thawRef h₃ g fr with
  | none => rfl
  | some x =>
    obtain ⟨-, -, -, hch, -⟩ := thawRef_eq_some.mp hth
    obtain ⟨acc, hacc⟩ := Option.isSome_iff_exists.mp hch
    unfold chainAcc at hacc
    rw [hhops] at hacc
    have hlive := (foldChain_prefix_live _ _ _ pre ext acc hacc).1
    have hrv : h₃.revoked.contains (credNul (lineageOf fr.cap.root pre.toList)) = true := by
      obtain ⟨-, rfl⟩ := step_revokeLineage hrev
      exact (trace_ext ht).revoked _ (RevokedSet.contains_insert_self _ _)
    simp only [lineageLive, hrv, Bool.not_true] at hlive
    cases hlive

/-- **Freeze then thaw.** Freeze a grain of an accountable host, let the host move on, thaw: the
entries that come back are exactly the grain's entries that are still admissible. -/
theorem freeze_thaw_roundtrip {gs : GrainState} (ha : Accountable h) (hx : HostExt h h')
    (hg : h.grains[g]? = some gs)
    (hf : freezeGrain h g = some fz) (x : HeldCap) :
    x ∈ (thawGrain h' fz).clist ↔ x ∈ gs.clist ∧ capAdmissible h' x.cap = true := by
  obtain ⟨gs', hgs', rfl⟩ := freezeGrain_eq_some hf
  rw [hg] at hgs'
  cases hgs'
  simp only [thawGrain, Array.mem_filterMap, Array.mem_map]
  constructor
  · rintro ⟨fr, ⟨y, hy, rfl⟩, hth⟩
    obtain ⟨rfl, -, -, hch, hml⟩ := thawRef_eq_some.mp hth
    exact ⟨hy, capAdmissible_iff.mpr ⟨hml, hch⟩⟩
  · rintro ⟨hxm, hadm⟩
    obtain ⟨slot, hslot⟩ := Array.mem_iff_getElem?.mp hxm
    obtain ⟨p, hp⟩ := ha.grounded g slot x ⟨gs, hg, hslot⟩
    obtain ⟨e, he, hd, hde, hc, -, -⟩ := hp.edge
    obtain ⟨hml, hch⟩ := capAdmissible_iff.mp hadm
    exact ⟨_, ⟨x, hxm, rfl⟩,
      thawRef_eq_some.mpr ⟨rfl, rfl, ⟨e, hx.edges e he, hc, hde, hd⟩, hch, hml⟩⟩

/-- The thaw verdict as a rehydration membrane viewer: it permits every affordance name when the
reference rebinds and none when it does not. -/
def thawViewer (h : PowerboxHost) (g : GrainId) (fr : FrozenRef) (held : List Auth) :
    MembraneViewer :=
  { held := held, permits := fun _ => (thawRef h g fr).isSome, activeNames := [] }

/-- **The bridge to `Obend.Vault.Rehydration`.** Rehydrating any sturdyref through the thaw
viewer shows an affordance exactly when the frozen reference rebinds and the same viewer with an
open projection would show it. A refused thaw leaves the rehydrated surface empty. -/
theorem thaw_rehydrates_iff {φ : Type} (h : PowerboxHost) (g : GrainId) (fr : FrozenRef)
    (held : List Auth) (sr : Sturdyref φ) (aff : CellAffordance φ) :
    aff ∈ (rehydrateSturdyref sr (thawViewer h g fr held)).1 ↔
      (thawRef h g fr).isSome = true ∧
        aff ∈ (rehydrateSturdyref sr { held := held, permits := fun _ => true }).1 := by
  simp only [rehydrateSturdyref, mem_projectMembrane, membraneShows, thawViewer,
    Bool.and_eq_true, Bool.and_true]
  constructor
  · rintro ⟨hin, hg, hp⟩
    exact ⟨hp, hin, hg⟩
  · rintro ⟨hp, hin, hg⟩
    exact ⟨hin, hg, hp⟩

/-! ## 13. The caller contract -/

/-- A wrapping membrane that someone else owns. -/
def MembraneForeign (h : PowerboxHost) (p : PrincipalId) (wrap : Option MembraneId) : Prop :=
  ∃ m q, wrap = some m ∧ h.membraneOwners.lookup m = some q ∧ q ≠ p

/-- The receiving grain does not exist, or already uses the petname. -/
def PetnameUnavailable (h : PowerboxHost) (g : GrainId) (pet : String) : Prop :=
  ∀ gs, h.grains[g]? = some gs → ∃ x ∈ gs.clist, x.petname = pet

/-- An enclosing membrane is revoked, or the chain does not fold. -/
def CapSevered (h : PowerboxHost) (c : CapDescriptor) : Prop :=
  (∃ m ∈ c.membranes, m ∈ h.revokedMembranes.keys.toList) ∨ chainAcc h c = none

/-- What a refused turn did wrong, clause by clause. -/
def PowerboxViolation (h : PowerboxHost) : PowerboxTurn → Prop
  | .spawn => False
  | .grant u g pet root wrap =>
    MembraneForeign h (.user u) wrap ∨ u ∉ h.users ∨ PetnameUnavailable h g pet ∨
      CapSevered h (rootCap root wrap)
  | .delegate src slot dst pet hop wrap gift =>
    (∀ x, ¬HoldsAt h src slot x) ∨ MembraneForeign h (.grain src) wrap ∨
      PetnameUnavailable h dst pet ∨ h.giftsSpent.spec gift ∨
      ∃ x, HoldsAt h src slot x ∧ CapSevered h (x.cap.extend hop wrap)
  | .invoke g slot need _ =>
    (∀ x, ¬HoldsAt h g slot x) ∨
      ∃ x, HoldsAt h g slot x ∧
        (CapSevered h x.cap ∨ ∃ acc, chainAcc h x.cap = some acc ∧ authorize acc need = false)
  | .revokeMembrane actor m => h.membraneOwners.lookup m ≠ some actor
  | .revokeLineage u _ => u ∉ h.users
  | .checkpoint g => h.grains[g]? = none
  | .restart g => ∀ fz ∈ h.snapshots, fz.grain ≠ g

theorem claimMembrane_eq_none {p : PrincipalId} :
    claimMembrane h.membraneOwners p wrap = none ↔ MembraneForeign h p wrap := by
  unfold MembraneForeign
  cases wrap with
  | none => simp [claimMembrane]
  | some m =>
    simp only [claimMembrane]
    cases hl : h.membraneOwners.lookup m with
    | none =>
      constructor
      · intro e
        simp at e
      · rintro ⟨m', q, hm, hq, -⟩
        cases hm
        rw [hl] at hq
        cases hq
    | some q =>
      by_cases hq : q = p
      · constructor
        · intro e
          simp [hq] at e
        · rintro ⟨m', q', hm, hq', hne⟩
          cases hm
          rw [hl] at hq'
          cases hq'
          exact absurd hq hne
      · constructor
        · intro _
          exact ⟨m, q, rfl, hl, hq⟩
        · intro _
          simp [hq]

theorem petnameFresh_eq_false :
    petnameFresh h g pet = false ↔ PetnameUnavailable h g pet := by
  unfold PetnameUnavailable
  constructor
  · intro hf gs hgs
    apply Classical.byContradiction
    intro hno
    have : petnameFresh h g pet = true :=
      petnameFresh_iff.mpr ⟨gs, hgs, fun x hx hp => hno ⟨x, hx, hp⟩⟩
    rw [hf] at this
    cases this
  · intro hu
    cases hf : petnameFresh h g pet with
    | false => rfl
    | true =>
      obtain ⟨gs, hgs, hne⟩ := petnameFresh_iff.mp hf
      obtain ⟨x, hx, hp⟩ := hu gs hgs
      exact absurd hp (hne x hx)

theorem capAdmissible_eq_false :
    capAdmissible h c = false ↔ CapSevered h c := by
  unfold CapSevered
  constructor
  · intro hf
    cases hch : chainAcc h c with
    | none => exact .inr rfl
    | some acc =>
      left
      apply Classical.byContradiction
      intro hno
      have : capAdmissible h c = true :=
        capAdmissible_iff.mpr ⟨fun m hm hin => hno ⟨m, hm, hin⟩, by rw [hch]; rfl⟩
      rw [hf] at this
      cases this
  · intro hs
    cases hf : capAdmissible h c with
    | false => rfl
    | true =>
      obtain ⟨hml, hch⟩ := capAdmissible_iff.mp hf
      rcases hs with ⟨m, hm, hin⟩ | hnone
      · exact absurd hin (hml m hm)
      · rw [hnone] at hch
        cases hch

theorem capLive_eq_false :
    capLive h c need = false ↔
      CapSevered h c ∨ ∃ acc, chainAcc h c = some acc ∧ authorize acc need = false := by
  rw [← capAdmissible_eq_false]
  unfold capLive capAdmissible
  cases membranesLive h c <;> cases chainAcc h c <;> simp

/-- **A refused turn violates the contract, and only such a turn is refused.** The step skips
nothing it could have run. -/
theorem powerboxStep_skip_implies_violation (h : PowerboxHost) (t : PowerboxTurn) :
    stepPowerboxHost h t = none ↔ PowerboxViolation h t := by
  cases t with
  | spawn => simp [stepPowerboxHost, PowerboxViolation]
  | grant u g pet root wrap =>
    simp only [stepPowerboxHost, PowerboxViolation, ← claimMembrane_eq_none,
      ← petnameFresh_eq_false, ← capAdmissible_eq_false]
    cases claimMembrane h.membraneOwners (.user u) wrap with
    | none => simp
    | some owners =>
      cases hu : h.users.contains u <;> cases petnameFresh h g pet <;>
        cases capAdmissible h (rootCap root wrap) <;>
        simp_all
  | delegate src slot dst pet hop wrap gift =>
    simp only [stepPowerboxHost, PowerboxViolation, ← claimMembrane_eq_none,
      ← petnameFresh_eq_false, ← capAdmissible_eq_false, ← CapTP.SortedU64Set.contains_eq_spec]
    cases hh : heldAt h src slot with
    | none =>
      have hno : ∀ x, ¬HoldsAt h src slot x := fun x hx => by
        rw [heldAt_iff.mpr hx] at hh
        cases hh
      simp [hno]
    | some x =>
      have hx := heldAt_iff.mp hh
      have hone : ∀ y, HoldsAt h src slot y ↔ y = x := fun y =>
        ⟨fun hy => Option.some.inj ((heldAt_iff.mpr hy).symm.trans hh), fun e => e ▸ hx⟩
      have hsome : ¬∀ y, ¬HoldsAt h src slot y := fun hall => hall x hx
      cases claimMembrane h.membraneOwners (.grain src) wrap with
      | none => simp
      | some owners =>
        cases petnameFresh h dst pet <;> cases capAdmissible h (x.cap.extend hop wrap) <;>
          cases h.giftsSpent.contains gift <;> simp_all
  | invoke g slot need action =>
    simp only [stepPowerboxHost, PowerboxViolation]
    cases hh : heldAt h g slot with
    | none =>
      have hno : ∀ x, ¬HoldsAt h g slot x := fun x hx => by
        rw [heldAt_iff.mpr hx] at hh
        cases hh
      simp [hno]
    | some x =>
      have hx := heldAt_iff.mp hh
      have hone : ∀ y, HoldsAt h g slot y ↔ y = x := fun y =>
        ⟨fun hy => Option.some.inj ((heldAt_iff.mpr hy).symm.trans hh), fun e => e ▸ hx⟩
      simp only [hone, exists_eq_left, ← capLive_eq_false]
      cases capLive h x.cap need <;> simp
  | revokeMembrane actor m =>
    simp only [stepPowerboxHost, PowerboxViolation]
    by_cases hc : h.membraneOwners.lookup m = some actor
    · simp [hc]
    · simp [hc]
  | revokeLineage u x =>
    simp only [stepPowerboxHost, PowerboxViolation]
    cases hu : h.users.contains u <;> simp_all
  | checkpoint g =>
    simp only [stepPowerboxHost, PowerboxViolation, freezeGrain]
    cases h.grains[g]? <;> simp
  | restart g =>
    simp only [stepPowerboxHost, PowerboxViolation]
    cases hf : h.snapshots.find? (fun fz => fz.grain == g) with
    | none =>
      have hno := List.find?_eq_none.mp hf
      simp only [true_iff]
      exact fun fz hfz hg => hno fz hfz (by simp [hg])
    | some fz =>
      have hin := List.mem_of_find?_eq_some hf
      have hg : fz.grain = g := by simpa using List.find?_some hf
      simp only [reduceCtorEq, false_iff]
      exact fun hall => hall fz hin hg

/-! ## 14. The premises are inhabited -/

/-- A reachable accountable host with two isolated grains. -/
theorem accountable_trace_inhabited (users : List Nat) (facts : Nat → KleenePred3) :
    ∃ ts h', Accountable (genesis users facts) ∧
      ValidPowerboxTrace (genesis users facts) ts h' ∧ h'.grains.size = 2 :=
  ⟨[.spawn, .spawn], _, genesis_accountable users facts, ⟨_, rfl, _, rfl, rfl⟩, rfl⟩

/-- The contract is violated by some turn and met by another, in the same host. -/
theorem violation_inhabited (users : List Nat) (facts : Nat → KleenePred3) :
    ∃ t t', PowerboxViolation (genesis users facts) t ∧
      ∃ h', stepPowerboxHost (genesis users facts) t' = some h' :=
  ⟨.invoke 0 0 0 .empty, .spawn,
    .inl fun x hx => by
      obtain ⟨gs, hgs, -⟩ := hx
      simp [genesis] at hgs,
    _, rfl⟩

end Obend.Polis.GrainPowerbox

end
