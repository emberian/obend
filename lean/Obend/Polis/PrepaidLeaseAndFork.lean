module
public import Obend.Polis.VerkleUmem
public import Obend.Polis.GrainPowerbox

public section
namespace Obend.Polis.Custody
open Obend.Crypto Obend.Digest.Cshake256
set_option autoImplicit false

/-- Concrete, full-output collision; no collision-resistance axiom is assumed. -/
def CshakeCollision : Prop := ∃ domain a b : List UInt8,
  a ≠ b ∧ cshake32ByteArray domain a = cshake32ByteArray domain b

def hash (domain : String) (fields : List (List UInt8)) : ByteArray :=
  cshake32ByteArray domain.toUTF8.data.toList (encodeFields fields)

theorem hash_size (d : String) (xs : List (List UInt8)) : (hash d xs).size = 32 :=
  cshake32ByteArray_size _ _

theorem hash_binds (d : String) {xs ys : List (List UInt8)} (h : hash d xs = hash d ys) :
    xs = ys ∨ CshakeCollision := by
  by_cases hp : encodeFields xs = encodeFields ys
  · exact .inl (encodeFields_injective _ _ hp)
  · exact .inr ⟨d.toUTF8.data.toList, encodeFields xs, encodeFields ys, hp, h⟩

/-- Length-framed Merkle spine. Each node commits its payload and the complete tail root. -/
def merkle : List (List UInt8) → ByteArray
  | [] => hash "OBEND.CUSTODY.MERKLE.EMPTY/v1" []
  | x :: xs => hash "OBEND.CUSTODY.MERKLE.NODE/v1" [[1], x, (merkle xs).data.toList]

/-- Reverse array traversal is stack-bounded; the specification remains a Merkle list. -/
def merkleExec (xs : Array (List UInt8)) : ByteArray :=
  xs.foldr (fun x tail => hash "OBEND.CUSTODY.MERKLE.NODE/v1" [[1], x, tail.data.toList])
    (hash "OBEND.CUSTODY.MERKLE.EMPTY/v1" [])

theorem merkle_eq_foldr (xs : List (List UInt8)) :
    merkle xs = xs.foldr
      (fun x tail => hash "OBEND.CUSTODY.MERKLE.NODE/v1" [[1], x, tail.data.toList])
      (hash "OBEND.CUSTODY.MERKLE.EMPTY/v1" []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [merkle, List.foldr_cons, ih]

theorem merkle_exec_eq (xs : Array (List UInt8)) : merkleExec xs = merkle xs.toList := by
  rw [merkle_eq_foldr, Array.foldr_toList]
  rfl

def merkleFast (xs : List (List UInt8)) : ByteArray := merkleExec xs.toArray
@[csimp] theorem merkle_eq_fast : merkle = merkleFast := by
  funext xs
  simp only [merkleFast, merkle_exec_eq]

/-- The count is committed separately, so empty and nonempty shapes cannot alias unnoticed. -/
def merkleRoot (xs : List (List UInt8)) : ByteArray :=
  hash "OBEND.CUSTODY.MERKLE.ROOT/v1" [leb128 xs.length, (merkle xs).data.toList]

theorem natBytes_inj {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)).1

theorem merkle_binds (xs ys : List (List UInt8)) (hl : xs.length = ys.length)
    (h : merkle xs = merkle ys) : xs = ys ∨ CshakeCollision := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact .inl rfl
    | cons y ys => cases hl
  | cons x xs ih =>
    cases ys with
    | nil => cases hl
    | cons y ys =>
      rcases hash_binds "OBEND.CUSTODY.MERKLE.NODE/v1" h with hp | hc
      · have hp' : x = y ∧ (merkle xs).data.toList = (merkle ys).data.toList := by simpa using hp
        rcases ih ys (Nat.succ.inj hl) (byteArray_eq_of_toList_eq hp'.2) with he | hc
        · exact .inl (by rw [hp'.1, he])
        · exact .inr hc
      · exact .inr hc

theorem merkleRoot_binds {xs ys : List (List UInt8)} (h : merkleRoot xs = merkleRoot ys) :
    xs = ys ∨ CshakeCollision := by
  rcases hash_binds _ h with hp | hc
  · have hp' : leb128 xs.length = leb128 ys.length ∧
        (merkle xs).data.toList = (merkle ys).data.toList := by simpa using hp
    exact merkle_binds xs ys (natBytes_inj hp'.1) (byteArray_eq_of_toList_eq hp'.2)
  · exact .inr hc

structure PrepaidLease where
  leaseId : UInt64
  startPeriod : Nat
  nextDue : Nat
  rent : Nat
  initialBudget : Nat
  remaining : Nat
  drawn : Nat
  deriving DecidableEq, Repr

def openLease (id : UInt64) (start rent budget : Nat) : PrepaidLease :=
  ⟨id, start, start, rent, budget, budget, 0⟩

inductive LeaseRefusal where
  | replay | offSchedule | overDraw | insufficientBudget
  deriving DecidableEq, Repr

def advanceLease (l : PrepaidLease) : PrepaidLease :=
  { l with
    nextDue := l.nextDue + 1
    remaining := l.remaining - l.rent
    drawn := l.drawn + l.rent }

def dischargePeriod (l : PrepaidLease) (period requestedAmount : Nat) :
    Except LeaseRefusal PrepaidLease :=
  if period < l.nextDue then .error .replay
  else if period > l.nextDue then .error .offSchedule
  else if requestedAmount ≠ l.rent then .error .overDraw
  else if l.remaining < l.rent then .error .insufficientBudget
  else .ok (advanceLease l)

theorem dischargePeriod_success {l l' : PrepaidLease} {p a : Nat}
    (h : dischargePeriod l p a = .ok l') :
    p = l.nextDue ∧ a = l.rent ∧ l.rent ≤ l.remaining ∧ l' = advanceLease l := by
  unfold dischargePeriod at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> simp_all <;> omega

theorem replay_rejected (l : PrepaidLease) (p a : Nat) (h : p < l.nextDue) :
    dischargePeriod l p a = .error .replay := by simp [dischargePeriod, h]

theorem off_schedule_rejected (l : PrepaidLease) (p a : Nat) (h : p > l.nextDue) :
    dischargePeriod l p a = .error .offSchedule := by
  simp [dischargePeriod, h, show ¬ p < l.nextDue by omega]

theorem over_draw_rejected (l : PrepaidLease) (a : Nat) (h : a ≠ l.rent) :
    dischargePeriod l l.nextDue a = .error .overDraw := by simp [dischargePeriod, h]

theorem insufficient_budget_rejected (l : PrepaidLease) (h : l.remaining < l.rent) :
    dischargePeriod l l.nextDue l.rent = .error .insufficientBudget := by
  simp [dischargePeriod, h]

/-- Counts actual successful transitions, including arbitrary submitted periods and amounts. -/
inductive ReachableLease (id : UInt64) (start rent budget : Nat) : Nat → PrepaidLease → Prop
  | initial : ReachableLease id start rent budget 0 (openLease id start rent budget)
  | step {n l l' p a} : ReachableLease id start rent budget n l →
      dischargePeriod l p a = .ok l' → ReachableLease id start rent budget (n + 1) l'

theorem reachable_equations {id : UInt64} {start rent budget n : Nat} {l : PrepaidLease}
    (h : ReachableLease id start rent budget n l) :
    l.leaseId = id ∧ l.startPeriod = start ∧ l.rent = rent ∧ l.initialBudget = budget ∧
    l.nextDue = start + n ∧ l.drawn = n * rent ∧ l.remaining + l.drawn = budget := by
  induction h with
  | initial => simp [openLease]
  | @step n l l' p a _ hs ih =>
    obtain ⟨_, _, hc, rfl⟩ := dischargePeriod_success hs
    rcases ih with ⟨hi, ht, hr, hb, hn, hd, hsum⟩
    simp only [advanceLease]
    refine ⟨hi, ht, hr, hb, ?_, ?_, ?_⟩
    · omega
    · rw [hd, hr, Nat.add_mul]; simp
    · omega

theorem remainingAfter_eq {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : l.remaining = b - n * r := by
  have he := reachable_equations h; omega

theorem drawnAfter_eq {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : l.drawn = n * r :=
  (reachable_equations h).2.2.2.2.2.1

theorem budget_conserved {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : l.remaining + l.drawn = l.initialBudget := by
  have he := reachable_equations h; omega

theorem metered_equals_drawn {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : (l.nextDue - l.startPeriod) * l.rent = l.drawn := by
  rcases reachable_equations h with ⟨_, hs, hr, _, hn, hd, _⟩
  rw [hs, hr, hn, hd, Nat.add_sub_cancel_left]

theorem budget_never_overdrawn {id : UInt64} {s r b n : Nat} {l : PrepaidLease}
    (h : ReachableLease id s r b n l) : l.drawn ≤ l.initialBudget := by
  have := budget_conserved h; omega

theorem no_advance_without_draw_rejected (l l' : PrepaidLease) (p a : Nat)
    (h : l'.drawn ≠ l.drawn + l.rent) : dischargePeriod l p a ≠ .ok l' := by
  intro hs; obtain ⟨_, _, _, rfl⟩ := dischargePeriod_success hs
  exact h rfl

theorem no_draw_without_advance_rejected (l l' : PrepaidLease) (p a : Nat)
    (h : l'.nextDue ≠ l.nextDue + 1) : dischargePeriod l p a ≠ .ok l' := by
  intro hs; obtain ⟨_, _, _, rfl⟩ := dischargePeriod_success hs
  exact h rfl

def leaseFields (l : PrepaidLease) : List (List UInt8) :=
  [leb128 l.leaseId.toNat, leb128 l.startPeriod, leb128 l.nextDue, leb128 l.rent,
   leb128 l.initialBudget, leb128 l.remaining, leb128 l.drawn]

theorem leaseFields_inj {a b : PrepaidLease} (h : leaseFields a = leaseFields b) : a = b := by
  simp only [leaseFields, List.cons.injEq, and_true] at h
  rcases h with ⟨hi, hs, hn, hr, hb, hm, hd⟩
  have hi' := UInt64.toNat_inj.1 (natBytes_inj hi)
  have hs' := natBytes_inj hs; have hn' := natBytes_inj hn
  have hr' := natBytes_inj hr; have hb' := natBytes_inj hb
  have hm' := natBytes_inj hm; have hd' := natBytes_inj hd
  cases a; cases b; simp_all

def leaseStateRoot (l : PrepaidLease) : ByteArray := merkleRoot (leaseFields l)

theorem leaseStateRoot_size (l : PrepaidLease) : (leaseStateRoot l).size = 32 := by
  unfold leaseStateRoot merkleRoot
  exact hash_size "OBEND.CUSTODY.MERKLE.ROOT/v1" _

theorem equal_roots_bind_cursor_remaining_drawn_or_collision {a b : PrepaidLease}
    (h : leaseStateRoot a = leaseStateRoot b) : a = b ∨ CshakeCollision := by
  rcases merkleRoot_binds h with hp | hc
  · exact .inl (leaseFields_inj hp)
  · exact .inr hc

abbrev EgressDoor := String
/-- A custody capability is the frozen powerbox reference, not its integer slot name. -/
abbrev SessionCap := GrainPowerbox.FrozenRef

structure ConfinedSession where
  sessionId : UInt64
  lease : PrepaidLease
  mindRoot : ByteArray
  egressDoors : List EgressDoor
  caps : List UInt64
  receiptHead : ByteArray
  checkpointRoot : ByteArray
  frozenGrain : GrainPowerbox.FrozenGrain
  allowedReadSlots : List UInt64 := []
  allowedEmitSlots : List UInt64 := []
  allowHashDigest : Bool := false
  issuedIds : List UInt64 := []

/-- Integer wire names resolve only inside this session's frozen c-list and allowlist. -/
def resolveSessionCap (s : ConfinedSession) (slot : UInt64) : Option SessionCap :=
  if slot ∈ s.caps then s.frozenGrain.refs[slot.toNat]? else none

theorem ungranted_slot_refused (s : ConfinedSession) (slot : UInt64) (h : slot ∉ s.caps) :
    resolveSessionCap s slot = none := by simp [resolveSessionCap, h]

structure ForkChildSpec where
  id : UInt64
  budget : Nat
  doors : List EgressDoor
  caps : List UInt64
  allowedReadSlots : List UInt64 := []
  allowedEmitSlots : List UInt64 := []
  allowHashDigest : Bool := false
  deriving DecidableEq

structure ForkTwoSpec where
  left : ForkChildSpec
  right : ForkChildSpec
  deriving DecidableEq

inductive ForkRefusal where
  | duplicateIdentity | amplifiedAuthority | budgetOverdraw | namespaceCollision
  deriving DecidableEq, Repr

@[expose] def attenuates (p : ConfinedSession) (c : ForkChildSpec) : Prop :=
  ((∀ d ∈ c.doors, d ∈ p.egressDoors) ∧ (∀ k ∈ c.caps, k ∈ p.caps)) ∧
  (∀ k ∈ c.allowedReadSlots, k ∈ p.allowedReadSlots) ∧
  (∀ k ∈ c.allowedEmitSlots, k ∈ p.allowedEmitSlots) ∧
  (c.allowHashDigest = true → p.allowHashDigest = true)
instance (p : ConfinedSession) (c : ForkChildSpec) : Decidable (attenuates p c) := by
  unfold attenuates
  infer_instance

def canonicalU64 (xs : List UInt64) : List UInt64 :=
  (xs.mergeSort (fun a b => a.toNat ≤ b.toNat)).eraseReps

def authorityRoot (doors : List EgressDoor) (caps : List UInt64)
    (reads emits : List UInt64 := []) (allowHash : Bool := false) : ByteArray :=
  hash "OBEND.CUSTODY.AUTHORITY/v1"
    [encodeFields (((doors.map fun d => d.toUTF8.data.toList).mergeSort
        (fun a b => compare a b != .gt)).eraseReps),
     encodeFields ((canonicalU64 caps).map fun c => leb128 c.toNat),
     encodeFields ((canonicalU64 reads).map fun c => leb128 c.toNat),
     encodeFields ((canonicalU64 emits).map fun c => leb128 c.toNat),
     [if allowHash then 1 else 0]]

/-- Every frozen reference binds its descriptor opening, owner, name and full digest. -/
def frozenGrainRoot (g : GrainPowerbox.FrozenGrain) : ByteArray :=
  hash "OBEND.CUSTODY.FROZEN/v1" [leb128 g.grain, encodeFields (g.refs.toList.map fun r =>
    let (tag, id) := match r.via with | .user n => (0, n) | .grain n => (1, n)
    encodeFields [r.petname.toUTF8.data.toList, [UInt8.ofNat tag], leb128 id, r.cap.root.encode,
      encodeFields (r.cap.hops.toList.map fun b => b.encode),
      encodeFields (r.cap.membranes.map leb128), Obend.Digest.HashBytes.be 32 r.commitment.toNat])]

def sessionCheckpoint (s : ConfinedSession) : ByteArray :=
  hash "OBEND.CUSTODY.SESSION/v1" [leb128 s.sessionId.toNat, (leaseStateRoot s.lease).data.toList,
    s.mindRoot.data.toList, (authorityRoot s.egressDoors s.caps s.allowedReadSlots s.allowedEmitSlots s.allowHashDigest).data.toList, s.receiptHead.data.toList, (frozenGrainRoot s.frozenGrain).data.toList]

def childMind (p : ConfinedSession) (c : ForkChildSpec) : ByteArray :=
  hash "OBEND.CUSTODY.MIND/v1" [leb128 c.id.toNat, p.mindRoot.data.toList]

def forkGenesis (parent : ByteArray) (id : UInt64) (mind leaseRoot authority : ByteArray) : ByteArray :=
  hash "OBEND.CUSTODY.FORK/v1"
    [parent.data.toList, leb128 id.toNat, mind.data.toList, leaseRoot.data.toList, authority.data.toList]

def makeChild (p : ConfinedSession) (s : ForkChildSpec) (siblings : List UInt64 := []) : ConfinedSession :=
  let l := openLease s.id p.lease.nextDue p.lease.rent s.budget
  let m := childMind p s
  let head := forkGenesis p.checkpointRoot s.id m (leaseStateRoot l) (authorityRoot s.doors s.caps s.allowedReadSlots s.allowedEmitSlots s.allowHashDigest)
  let child : ConfinedSession := ⟨s.id, l, m, s.doors, s.caps, head, head, {p.frozenGrain with grain := s.id.toNat},
    s.allowedReadSlots, s.allowedEmitSlots, s.allowHashDigest,
    s.id :: p.sessionId :: (siblings ++ p.issuedIds)⟩
  {child with checkpointRoot := sessionCheckpoint child}

/-- A fork transfers principal, not rent. The retained tranche's initial allocation is
rebased by the transfer; its rent cursor and drawn accumulator remain unchanged. -/
def retainedParent (p : ConfinedSession) (s : ForkTwoSpec) : ConfinedSession :=
  let retained := { p with issuedIds := s.left.id :: s.right.id :: p.sessionId :: p.issuedIds, lease := { p.lease with
      initialBudget := p.lease.initialBudget - (s.left.budget + s.right.budget),
      remaining := p.lease.remaining - (s.left.budget + s.right.budget) } }
  {retained with checkpointRoot := sessionCheckpoint retained}

def forkTwo (p : ConfinedSession) (s : ForkTwoSpec) :
    Except ForkRefusal (ConfinedSession × ConfinedSession × ConfinedSession) :=
  if s.left.id = s.right.id ∨ s.left.id = p.lease.leaseId ∨ s.right.id = p.lease.leaseId then
    .error .duplicateIdentity
  else if s.left.id ∈ p.issuedIds ∨ s.right.id ∈ p.issuedIds then .error .duplicateIdentity
  else if ¬ (attenuates p s.left ∧ attenuates p s.right) then .error .amplifiedAuthority
  else if p.lease.remaining < s.left.budget + s.right.budget then .error .budgetOverdraw
  else if childMind p s.left = childMind p s.right then .error .namespaceCollision
  else .ok (retainedParent p s, makeChild p s.left [s.right.id], makeChild p s.right [s.left.id])

theorem forkTwo_success {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    s.left.id ≠ s.right.id ∧ s.left.id ≠ p.lease.leaseId ∧ s.right.id ≠ p.lease.leaseId ∧
    attenuates p s.left ∧ attenuates p s.right ∧
    s.left.budget + s.right.budget ≤ p.lease.remaining ∧
    childMind p s.left ≠ childMind p s.right ∧
    p' = retainedParent p s ∧ a = makeChild p s.left [s.right.id] ∧ b = makeChild p s.right [s.left.id] := by
  unfold forkTwo at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> simp_all

theorem issued_identity_rejected (p : ConfinedSession) (s : ForkTwoSpec)
    (h : s.left.id ∈ p.issuedIds ∨ s.right.id ∈ p.issuedIds) :
    forkTwo p s = .error .duplicateIdentity := by
  unfold forkTwo
  split <;> simp_all

theorem forkTwo_inherits_ids {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    ∀ id ∈ p.issuedIds, id ∈ p'.issuedIds ∧ id ∈ a.issuedIds ∧ id ∈ b.issuedIds := by
  rcases forkTwo_success h with ⟨_, _, _, _, _, _, _, rfl, rfl, rfl⟩
  intro id hi
  simp [retainedParent, makeChild, hi]

theorem forkTwo_sovereign_isolation {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    a.lease.leaseId ≠ b.lease.leaseId ∧ a.lease.leaseId ≠ p.lease.leaseId ∧
    b.lease.leaseId ≠ p.lease.leaseId ∧ a.mindRoot ≠ b.mindRoot := by
  rcases forkTwo_success h with ⟨hi, ha, hb, _, _, _, hm, _, rfl, rfl⟩
  exact ⟨hi, ha, hb, hm⟩

theorem forkTwo_attenuates_confinement {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    ((∀ d ∈ a.egressDoors, d ∈ p.egressDoors) ∧ (∀ k ∈ a.caps, k ∈ p.caps)) ∧
    ((∀ d ∈ b.egressDoors, d ∈ p.egressDoors) ∧ (∀ k ∈ b.caps, k ∈ p.caps)) := by
  rcases forkTwo_success h with ⟨_, _, _, ha, hb, _, _, _, rfl, rfl⟩
  exact ⟨ha.1, hb.1⟩

/-- The c-list is shared as a frozen value; only retained slot names can resolve. -/
theorem child_cap_resolves_in_parent (p : ConfinedSession) (c : ForkChildSpec)
    (ids : List UInt64) (slot : UInt64) (cap : SessionCap)
    (ha : attenuates p c) (h : resolveSessionCap (makeChild p c ids) slot = some cap) :
    resolveSessionCap p slot = some cap := by
  unfold resolveSessionCap at h ⊢
  simp only [makeChild] at h
  by_cases hs : slot ∈ c.caps
  · have hp := ha.1.2 slot hs
    simpa [hs, hp] using h
  · simp [hs] at h

theorem amplified_egress_or_cap_rejected (p : ConfinedSession) (s : ForkTwoSpec)
    (h : ¬ (attenuates p s.left ∧ attenuates p s.right)) :
    ∃ reason, forkTwo p s = .error reason := by
  unfold forkTwo
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · simp [h]

theorem duplicate_identity_rejected (p : ConfinedSession) (s : ForkTwoSpec)
    (h : s.left.id = s.right.id ∨ s.left.id = p.lease.leaseId ∨ s.right.id = p.lease.leaseId) :
    forkTwo p s = .error .duplicateIdentity := by simp [forkTwo, h]

theorem overdrawn_split_rejected (p : ConfinedSession) (s : ForkTwoSpec)
    (h : p.lease.remaining < s.left.budget + s.right.budget) :
    ∃ reason, forkTwo p s = .error reason := by
  cases he : forkTwo p s with
  | error r => exact ⟨r, rfl⟩
  | ok result =>
    rcases result with ⟨p', a, b⟩
    have hs := forkTwo_success he
    exfalso
    omega

theorem forkTwo_conserves_budget {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b)) :
    a.lease.initialBudget + b.lease.initialBudget + p'.lease.remaining = p.lease.remaining := by
  rcases forkTwo_success h with ⟨_, _, _, _, _, hc, _, rfl, rfl, rfl⟩
  simp only [makeChild, openLease, retainedParent]
  omega

theorem forkTwo_preserves_lease_balance {p p' a b : ConfinedSession} {s : ForkTwoSpec}
    (h : forkTwo p s = .ok (p', a, b))
    (hb : p.lease.remaining + p.lease.drawn = p.lease.initialBudget) :
    p'.lease.remaining + p'.lease.drawn = p'.lease.initialBudget := by
  rcases forkTwo_success h with ⟨_, _, _, _, _, hc, _, rfl, _, _⟩
  simp only [retainedParent]; omega

/-- An independent verifier supplies an alleged fork point; equality of the genesis
receipt binds it to the actual point, with a concrete collision on any substitution. -/
def verifyForkGenesis (p : ByteArray) (c : ConfinedSession) : Bool :=
  decide (forkGenesis p c.sessionId c.mindRoot (leaseStateRoot c.lease) (authorityRoot c.egressDoors c.caps c.allowedReadSlots c.allowedEmitSlots c.allowHashDigest) = c.receiptHead)

theorem genesis_binds {p q : ByteArray} {id : UInt64} {m l auth : ByteArray}
    (h : forkGenesis p id m l auth = forkGenesis q id m l auth) : p = q ∨ CshakeCollision := by
  rcases hash_binds _ h with hp | hc
  · have hp' : p.data.toList = q.data.toList := by simpa using hp
    exact .inl (byteArray_eq_of_toList_eq hp')
  · exact .inr hc

attribute [local irreducible] hash merkle merkleRoot leaseStateRoot childMind forkGenesis authorityRoot sessionCheckpoint

theorem forkTwo_anchors_receipt_chains_or_collision
    {p p' a b : ConfinedSession} {s : ForkTwoSpec} (h : forkTwo p s = .ok (p', a, b)) :
    verifyForkGenesis p.checkpointRoot a = true ∧ verifyForkGenesis p.checkpointRoot b = true ∧
    (∀ q, verifyForkGenesis q a = true → q = p.checkpointRoot ∨ CshakeCollision) ∧
    (∀ q, verifyForkGenesis q b = true → q = p.checkpointRoot ∨ CshakeCollision) := by
  rcases forkTwo_success h with ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩
  have accepts (c : ForkChildSpec) (ids : List UInt64) : verifyForkGenesis p.checkpointRoot (makeChild p c ids) = true := by
    unfold verifyForkGenesis
    apply decide_eq_true
    rfl
  refine ⟨accepts s.left [s.right.id], accepts s.right [s.left.id], ?_, ?_⟩
  all_goals
    intro q hq
    have he := of_decide_eq_true hq
    apply genesis_binds (id := _) (m := _) (l := _) he

/-- Every turn extends the child chain rather than overwriting the fork genesis. -/
def receiptFold (start : ByteArray) : List ByteArray → ByteArray
  | [] => start
  | event :: rest => receiptFold
      (hash "OBEND.CUSTODY.RECEIPT/v1" [start.data.toList, event.data.toList]) rest

theorem receiptFold_binds_start (events : List ByteArray) (a b : ByteArray)
    (h : receiptFold a events = receiptFold b events) : a = b ∨ CshakeCollision := by
  induction events generalizing a b with
  | nil => exact .inl h
  | cons e es ih =>
    rcases ih _ _ h with he | hc
    · rcases hash_binds "OBEND.CUSTODY.RECEIPT/v1" he with hp | hc
      · have hh : a.data.toList = b.data.toList := by simpa using hp
        exact .inl (byteArray_eq_of_toList_eq hh)
      · exact .inr hc
    · exact .inr hc

theorem fork_receipt_chain_binds_anchor_or_collision (events : List ByteArray)
    (claimed actual : ByteArray) (id : UInt64) (mind initialLeaseRoot authority : ByteArray)
    (h : receiptFold (forkGenesis claimed id mind initialLeaseRoot authority) events =
      receiptFold (forkGenesis actual id mind initialLeaseRoot authority) events) :
    claimed = actual ∨ CshakeCollision := by
  rcases receiptFold_binds_start events _ _ h with he | hc
  · exact genesis_binds he
  · exact .inr hc

/-- The allocator checks every live handle, including allocations made by sibling branches.
The per-session history additionally remembers retired identities along each lineage. -/
def forkFrontier (pre post : List ConfinedSession) (p : ConfinedSession) (s : ForkTwoSpec) :
    Except ForkRefusal (ConfinedSession × ConfinedSession × ConfinedSession) :=
  if s.left.id ∈ (pre ++ post).map (·.sessionId) ∨
      s.right.id ∈ (pre ++ post).map (·.sessionId) then .error .duplicateIdentity
  else forkTwo p s

theorem forkFrontier_success {pre post : List ConfinedSession} {p p' a b : ConfinedSession}
    {s : ForkTwoSpec} (h : forkFrontier pre post p s = .ok (p', a, b)) :
    forkTwo p s = .ok (p', a, b) ∧
    s.left.id ∉ (pre ++ post).map (·.sessionId) ∧
    s.right.id ∉ (pre ++ post).map (·.sessionId) := by
  unfold forkFrontier at h
  split at h <;> simp_all

/-- Each initial live identity is distinct; subsequent allocations are checked operationally. -/
inductive ValidSessionTree : List ConfinedSession → List ConfinedSession → Prop
  | initial (ss) : (ss.map (·.sessionId)).Nodup → ValidSessionTree ss ss
  | fork {root pre post p p' a b s} : ValidSessionTree root (pre ++ p :: post) →
      forkFrontier pre post p s = .ok (p', a, b) →
      ValidSessionTree root (pre ++ p' :: a :: b :: post)

def frontierBudget (ss : List ConfinedSession) : Nat := (ss.map (·.lease.remaining)).sum

theorem multi_fork_tree_conservation {root ss : List ConfinedSession}
    (h : ValidSessionTree root ss) : frontierBudget ss = frontierBudget root := by
  induction h with
  | initial => rfl
  | @fork pre post p p' a b s _ hf ih =>
    have hf := (forkFrontier_success hf).1
    have hc := forkTwo_conserves_budget hf
    have he := forkTwo_success hf
    have ha : a.lease.remaining = a.lease.initialBudget := by rw [he.2.2.2.2.2.2.2.2.1]; rfl
    have hb : b.lease.remaining = b.lease.initialBudget := by rw [he.2.2.2.2.2.2.2.2.2]; rfl
    simp only [frontierBudget, List.map_append, List.map_cons, List.sum_append, List.sum_cons] at *
    omega

theorem multi_fork_tree_distinct {root ss : List ConfinedSession}
    (h : ValidSessionTree root ss)
    (ids : ∀ p ∈ root, p.sessionId = p.lease.leaseId) : (ss.map (·.sessionId)).Nodup := by
  have invariant : (ss.map (·.sessionId)).Nodup ∧
      ∀ p ∈ ss, p.sessionId = p.lease.leaseId := by
    induction h with
    | initial hn => exact ⟨hn, ids⟩
    | @fork pre post p p' a b s ht hf ih =>
      obtain ⟨hf, hl, hr⟩ := forkFrontier_success hf
      obtain ⟨hne, hpl, hpr, _, _, _, _, rfl, rfl, rfl⟩ := forkTwo_success hf
      have hp := ih.2 p (by simp)
      constructor
      · simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at *
        simp only [retainedParent, makeChild]
        grind
      · intro q hq
        simp only [List.mem_append, List.mem_cons] at hq
        rcases hq with hq | rfl | rfl | rfl | hq
        · exact ih.2 q (by simp [hq])
        · exact hp
        · rfl
        · rfl
        · exact ih.2 q (by simp [hq])
  exact invariant.1

end Obend.Polis.Custody
