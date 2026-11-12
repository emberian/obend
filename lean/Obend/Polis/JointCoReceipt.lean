module
/-
# Obend.Polis.JointCoReceipt — joint turns across vats, and receipts that compose along promises

A turn that touches several vats leaves one local receipt in each. This module says when those
receipts are one turn, and how receipts with open promise ports compose into one.

1. `LocalTurn`, `JointTurn`: a local receipt checks its own arithmetic and commits to a turn digest.
   A joint turn is the pullback of the receipts over that digest (`SharedTurnId`: every leg names
   one 32-byte cSHAKE256 digest, and it is the digest of this forest of legs) together with
   bilateral conservation, the half-edges summing to zero. The shape is that of an account-update
   forest whose every party proves against one forest hash. `tensor_not_final`: valid local receipts
   do not make a joint turn, for either reason. `jointTurn_conserves_total_balance`,
   `jointTrace_conserves_total_balance` (any number of turns over a ledger with a spent-digest set;
   `jointTrace_no_replay`), `sharedTurnId_binds_forest`.
2. `jointTurn_committed_conservation_sound`: the same conservation read from 256-bit commitments,
   through `Obend.Polis.PrivatePredicate`.
3. `CoReceipt`: a receipt with typed open ports. An `AwaitPort` is a promise hole (a CapTP pending
   id, a 32-byte commitment to the awaited payload, a `DistPred` guard, and the root grant and rights
   its resolver must show); a `FulfillPort` resolves one, carrying a delegation chain.
   `composeCoReceipts` sorts both port tables (strictly ascending ids, so no hole is allocated or
   filled twice), finds each fulfilment's hole by CapTP's binary search, and checks the payload, the
   guard, the causal rank and the chain (`foldChain`: attenuation, caveats, and no revoked lineage or
   channel on any prefix). `promise_hole_no_double_fill`, `cyclic_wiring_refused`,
   `revoked_lineage_refused`, and `composeCoReceipts_closed_sound`: a composite with no open port is
   a joint turn in which every hole is filled exactly once by an authorized, unrevoked, causally
   earlier resolver.
-/
public import Obend.Polis.PrivatePredicate
public import Obend.Polis.CapTP
public import Obend.Polis.ZkBiscuit
import all Obend.Polis.CapTP

public section
namespace Obend.Polis.JointCoReceipt

open Obend.Polis
open Obend.Polis.PrivatePredicate
open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 1. Local receipts and the joint turn -/

/-- A vat. -/
abbrev VatId := Nat

/-- One vat's receipt of a turn: the turn digest it commits to, a 32-byte commitment to its local
effects, and its balance before, its half-edge, and its balance after. -/
structure LocalTurn where
  vat : VatId
  turnId : ByteArray
  body : ByteArray
  pre : Int
  half : Int
  post : Int

/-- The receipt's own arithmetic. -/
def LocalTurn.valid (t : LocalTurn) : Bool := decide (t.post = t.pre + t.half)

/-- What a leg contributes to the turn digest: the vat, its effects commitment, its half-edge. -/
def LocalTurn.legBytes (t : LocalTurn) : List UInt8 :=
  encodeFields [leb128 t.vat, t.body.data.toList, encodeInt t.half]

theorem LocalTurn.legBytes_inj {a b : LocalTurn} (h : a.legBytes = b.legBytes) :
    a.vat = b.vat ∧ a.body = b.body ∧ a.half = b.half := by
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  exact ⟨(leb128_prefix_inj (r₁ := []) (r₂ := [])
      (by rw [List.append_nil, List.append_nil, hf.1])).1,
    byteArray_eq_of_toList_eq hf.2.1,
    (encodeInt_prefix_inj (r₁ := []) (r₂ := [])
      (by rw [List.append_nil, List.append_nil, hf.2.2])).1⟩

/-- Customization string of the turn digest. -/
def turnCustomization : List UInt8 := "OBEND.POLIS.JOINTTURN/v1".toUTF8.data.toList

/-- The digest of a forest of legs, each length-prefixed. -/
def forestDigest (legs : List (List UInt8)) : ByteArray :=
  cshake32ByteArray turnCustomization (encodeFields legs)

/-- One digest names one forest, or the two forests collide. -/
theorem forestDigest_binds {a b : List (List UInt8)} (h : forestDigest a = forestDigest b) :
    a = b ∨ CollisionAmong (cshake256Bytes turnCustomization)
      (fun x => x = encodeFields a ∨ x = encodeFields b) := by
  rcases cshake32_binds turnCustomization h with hp | hc
  · exact .inl (encodeFields_injective _ _ hp)
  · exact .inr hc

/-- The turn digest of a list of local receipts. -/
def turnDigest (legs : List LocalTurn) : ByteArray := forestDigest (legs.map LocalTurn.legBytes)

/-- **The pullback over the turn digest.** Every leg commits to `tid`, and `tid` is the digest of
exactly these legs: a receipt is a receipt of this turn and of no other. -/
structure SharedTurnId (legs : List LocalTurn) where
  tid : ByteArray
  agree : ∀ t, t ∈ legs → t.turnId = tid
  pinned : tid = turnDigest legs

/-- A joint turn: receipts that are each valid, agree on the turn, and conserve between them. -/
structure JointTurn where
  legs : List LocalTurn
  shared : SharedTurnId legs
  valid : ∀ t, t ∈ legs → t.post = t.pre + t.half
  balanced : (legs.map (·.half)).sum = 0

/-- The checker for a joint turn. -/
def checkJoint (shared : ByteArray) (legs : List LocalTurn) : Bool :=
  legs.all (·.valid) && legs.all (fun t => decide (t.turnId = shared)) &&
    decide (shared = turnDigest legs) && decide ((legs.map (·.half)).sum = 0)

/-- **The checker accepts exactly the joint turns.** -/
theorem checkJoint_iff (shared : ByteArray) (legs : List LocalTurn) :
    checkJoint shared legs = true ↔ ∃ j : JointTurn, j.legs = legs ∧ j.shared.tid = shared := by
  constructor
  · intro h
    simp only [checkJoint, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      LocalTurn.valid] at h
    obtain ⟨⟨⟨hv, ha⟩, hp⟩, hb⟩ := h
    exact ⟨⟨legs, ⟨shared, ha, hp⟩, hv, hb⟩, rfl, rfl⟩
  · rintro ⟨j, rfl, rfl⟩
    simp only [checkJoint, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, LocalTurn.valid]
    exact ⟨⟨⟨j.valid, j.shared.agree⟩, j.shared.pinned⟩, j.balanced⟩

theorem sum_post_eq : ∀ legs : List LocalTurn, (∀ t, t ∈ legs → t.post = t.pre + t.half) →
    (legs.map (·.post)).sum = (legs.map (·.pre)).sum + (legs.map (·.half)).sum
  | [], _ => by simp
  | t :: ts, h => by
    have ht := h t (by simp)
    have ih := sum_post_eq ts (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, ih, ht]
    omega

/-- **A joint turn conserves the total balance** of the vats it touches. -/
theorem jointTurn_conserves_total_balance (j : JointTurn) :
    (j.legs.map (·.post)).sum = (j.legs.map (·.pre)).sum := by
  rw [sum_post_eq j.legs j.valid, j.balanced]
  omega

/-- What the checker establishes: conservation, and every leg naming the digest of this forest. -/
theorem jointTurn_sound (shared : ByteArray) (legs : List LocalTurn)
    (h : checkJoint shared legs = true) :
    (legs.map (·.post)).sum = (legs.map (·.pre)).sum ∧
      ∀ t, t ∈ legs → t.turnId = turnDigest legs := by
  obtain ⟨j, rfl, rfl⟩ := (checkJoint_iff shared legs).1 h
  exact ⟨jointTurn_conserves_total_balance j, fun t ht => (j.shared.agree t ht).trans j.shared.pinned⟩

/-- **The turn digest binds the forest.** Two joint turns with one digest have the same legs (vat,
effects commitment and half-edge of each, in order), or their forests collide. A leg cannot be
moved into another turn. -/
theorem sharedTurnId_binds_forest (j₁ j₂ : JointTurn) (h : j₁.shared.tid = j₂.shared.tid) :
    j₁.legs.map LocalTurn.legBytes = j₂.legs.map LocalTurn.legBytes ∨
      CollisionAmong (cshake256Bytes turnCustomization)
        (fun x => x = encodeFields (j₁.legs.map LocalTurn.legBytes) ∨
          x = encodeFields (j₂.legs.map LocalTurn.legBytes)) := by
  rw [j₁.shared.pinned, j₂.shared.pinned] at h
  exact forestDigest_binds h

/-- **Local receipts are not enough.** Two receipts, each valid on its own and naming one turn, that
mint a unit between them; and two receipts whose half-edges cancel but which belong to different
turns. Neither pair is a joint turn under any digest: the product of the vats' own judgements is
strictly larger than the joint one, and the binding has to be checked. -/
theorem tensor_not_final :
    (∃ a b : LocalTurn, a.valid = true ∧ b.valid = true ∧ a.turnId = b.turnId ∧
        ∀ shared, checkJoint shared [a, b] = false) ∧
      (∃ a b : LocalTurn, a.valid = true ∧ b.valid = true ∧ a.half + b.half = 0 ∧
        ∀ shared, checkJoint shared [a, b] = false) := by
  refine ⟨⟨⟨0, .empty, .empty, 0, 1, 1⟩, ⟨1, .empty, .empty, 0, 1, 1⟩, by decide, by decide, rfl,
      fun shared => ?_⟩,
    ⟨⟨0, ⟨#[0]⟩, .empty, 0, 1, 1⟩, ⟨1, ⟨#[1]⟩, .empty, 0, -1, -1⟩, by decide, by decide,
      by decide, fun shared => ?_⟩⟩
  · refine Bool.eq_false_iff.2 (fun h => ?_)
    obtain ⟨j, hl, _⟩ := (checkJoint_iff _ _).1 h
    have hb := j.balanced
    rw [hl] at hb
    simp at hb
  · refine Bool.eq_false_iff.2 (fun h => ?_)
    obtain ⟨j, hl, _⟩ := (checkJoint_iff _ _).1 h
    have h12 : (⟨#[0]⟩ : ByteArray) = ⟨#[1]⟩ :=
      (j.shared.agree ⟨0, ⟨#[0]⟩, .empty, 0, 1, 1⟩ (by rw [hl]; simp)).trans
        (j.shared.agree ⟨1, ⟨#[1]⟩, .empty, 0, -1, -1⟩ (by rw [hl]; simp)).symm
    exact absurd h12 (by decide)

/-! ## 2. Many turns: a ledger and its spent digests -/

/-- Balances by vat. -/
abbrev Ledger := VatId → Int

/-- Apply one half-edge. -/
def applyLeg (L : Ledger) (t : LocalTurn) : Ledger :=
  fun v => if v = t.vat then L v + t.half else L v

/-- Apply the half-edges of a turn. -/
def applyLegs (L : Ledger) (legs : List LocalTurn) : Ledger := legs.foldl applyLeg L

/-- The total over a set of vats. -/
def total (vats : List VatId) (L : Ledger) : Int := (vats.map L).sum

theorem total_applyLeg_of_not_mem (L : Ledger) (t : LocalTurn) : ∀ vats : List VatId,
    t.vat ∉ vats → total vats (applyLeg L t) = total vats L
  | [], _ => by rfl
  | v :: vs, h => by
    have hv : v ≠ t.vat := fun e => h (by simp [e])
    have ih := total_applyLeg_of_not_mem L t vs (fun hm => h (by simp [hm]))
    have hval : applyLeg L t v = L v := by simp [applyLeg, hv]
    simp only [total, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, hval]

theorem total_applyLeg (L : Ledger) (t : LocalTurn) : ∀ vats : List VatId, vats.Nodup →
    t.vat ∈ vats → total vats (applyLeg L t) = total vats L + t.half
  | [], _, h => by cases h
  | v :: vs, hnd, hm => by
    obtain ⟨hv, hvs⟩ := List.nodup_cons.1 hnd
    by_cases he : v = t.vat
    · have ih := total_applyLeg_of_not_mem L t vs (he ▸ hv)
      have hval : applyLeg L t v = L v + t.half := by simp [applyLeg, he]
      simp only [total, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, hval]
      omega
    · have hm' : t.vat ∈ vs := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm he
        · exact h
      have ih := total_applyLeg L t vs hvs hm'
      have hval : applyLeg L t v = L v := by simp [applyLeg, he]
      simp only [total, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, hval]
      omega

theorem total_applyLegs (vats : List VatId) (hnd : vats.Nodup) :
    ∀ (legs : List LocalTurn) (L : Ledger), (∀ t, t ∈ legs → t.vat ∈ vats) →
      total vats (applyLegs L legs) = total vats L + (legs.map (·.half)).sum
  | [], L, _ => by simp [applyLegs]
  | t :: ts, L, h => by
    have ih := total_applyLegs vats hnd ts (applyLeg L t) (fun x hx => h x (by simp [hx]))
    simp only [applyLegs, List.foldl_cons] at ih ⊢
    rw [ih, total_applyLeg L t vats hnd (h t (by simp))]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A ledger over the vats `0 … n-1` with the turn digests already applied, as a sorted set of
their 256-bit readings. -/
structure LedgerState where
  balances : Ledger
  seen : RevokedSet

/-- The 256-bit reading of a turn digest. -/
def turnKey (shared : ByteArray) : Nat := ofBE shared.data.toList

/-- Apply one joint turn: it must check, be new, and touch only vats of the ledger. -/
def stepJoint (n : Nat) (s : LedgerState) (shared : ByteArray) (legs : List LocalTurn) :
    Option LedgerState :=
  if checkJoint shared legs && !s.seen.contains (turnKey shared) &&
      legs.all (fun t => decide (t.vat < n)) then
    some ⟨applyLegs s.balances legs, s.seen.insert (turnKey shared)⟩
  else none

/-- Apply a sequence of joint turns. -/
def runTrace (n : Nat) : LedgerState → List (ByteArray × List LocalTurn) → Option LedgerState
  | s, [] => some s
  | s, (shared, legs) :: rest =>
    match stepJoint n s shared legs with
    | some s' => runTrace n s' rest
    | none => none

theorem stepJoint_eq_some {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (h : stepJoint n s shared legs = some s') :
    checkJoint shared legs = true ∧ s.seen.contains (turnKey shared) = false ∧
      (∀ t, t ∈ legs → t.vat < n) ∧
      s' = ⟨applyLegs s.balances legs, s.seen.insert (turnKey shared)⟩ := by
  unfold stepJoint at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, (Option.some.inj h).symm⟩
  · cases h

theorem stepJoint_conserves {n : Nat} {s s' : LedgerState} {shared : ByteArray}
    {legs : List LocalTurn} (h : stepJoint n s shared legs = some s') :
    total (List.range n) s'.balances = total (List.range n) s.balances := by
  obtain ⟨hc, _, hv, rfl⟩ := stepJoint_eq_some h
  obtain ⟨j, rfl, _⟩ := (checkJoint_iff shared legs).1 hc
  rw [total_applyLegs (List.range n) List.nodup_range j.legs s.balances
    (fun t ht => List.mem_range.2 (hv t ht)), j.balanced]
  omega

/-- **A replayed turn is refused.** -/
theorem replayed_turn_refused (n : Nat) (s : LedgerState) (shared : ByteArray)
    (legs : List LocalTurn) (h : s.seen.contains (turnKey shared) = true) :
    stepJoint n s shared legs = none := by
  simp [stepJoint, h]

/-- **Conservation over any number of turns.** A trace of joint turns leaves the ledger's total
where it was, and never forgets a digest it has applied. -/
theorem jointTrace_conserves_total_balance (n : Nat) :
    ∀ (trace : List (ByteArray × List LocalTurn)) (s s' : LedgerState),
      runTrace n s trace = some s' →
        total (List.range n) s'.balances = total (List.range n) s.balances ∧
          ∀ k, s.seen.contains k = true → s'.seen.contains k = true
  | [], s, s', h => by
    cases Option.some.inj h
    exact ⟨rfl, fun _ hk => hk⟩
  | (shared, legs) :: rest, s, s', h => by
    simp only [runTrace] at h
    split at h
    · rename_i s₁ hs
      obtain ⟨ht, hk⟩ := jointTrace_conserves_total_balance n rest s₁ s' h
      refine ⟨ht.trans (stepJoint_conserves hs), fun k hks => hk k ?_⟩
      obtain ⟨_, _, _, rfl⟩ := stepJoint_eq_some hs
      exact (RevokedSet.contains_insert _ _ _).2 (.inr hks)
    · cases h

/-- Every turn of a trace that runs was new when the trace began. -/
theorem runTrace_fresh (n : Nat) : ∀ (trace : List (ByteArray × List LocalTurn))
    (s s' : LedgerState), runTrace n s trace = some s' →
      ∀ e, e ∈ trace → s.seen.contains (turnKey e.1) = false
  | [], _, _, _, _, he => by cases he
  | (shared, legs) :: rest, s, s', h, e, he => by
    simp only [runTrace] at h
    split at h
    · rename_i s₁ hs
      obtain ⟨_, hnew, _, rfl⟩ := stepJoint_eq_some hs
      rcases List.mem_cons.1 he with rfl | he'
      · exact hnew
      · have h1 := runTrace_fresh n rest _ s' h e he'
        cases hc : s.seen.contains (turnKey e.1) with
        | false => rfl
        | true =>
          rw [(RevokedSet.contains_insert _ _ _).2 (.inr hc)] at h1
          cases h1
    · cases h

/-- **No turn digest is applied twice in a trace.** -/
theorem jointTrace_no_replay (n : Nat) (s s' : LedgerState) (shared : ByteArray)
    (legs legs' : List LocalTurn) (rest : List (ByteArray × List LocalTurn))
    (h : runTrace n s ((shared, legs) :: rest) = some s') : (shared, legs') ∉ rest := by
  intro hm
  simp only [runTrace] at h
  split at h
  · rename_i s₁ hs
    obtain ⟨_, _, _, rfl⟩ := stepJoint_eq_some hs
    have h1 := runTrace_fresh n rest _ s' h _ hm
    rw [RevokedSet.contains_insert_self] at h1
    cases h1
  · cases h

/-! ## 3. The joint turn over commitments -/

/-- A leg whose half-edge is hidden: its direction and a 256-bit commitment to its magnitude. -/
structure CommittedLeg where
  vat : VatId
  turnId : ByteArray
  credit : Bool
  commitment : BitVec 256

/-- What a committed leg contributes to the turn digest. -/
def CommittedLeg.legBytes (t : CommittedLeg) : List UInt8 :=
  encodeFields [leb128 t.vat, [if t.credit then 1 else 0], be 32 t.commitment.toNat]

theorem CommittedLeg.legBytes_inj {a b : CommittedLeg} (h : a.legBytes = b.legBytes) :
    a.vat = b.vat ∧ a.credit = b.credit ∧ a.commitment = b.commitment := by
  have hf := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at hf
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  refine ⟨(leb128_prefix_inj (r₁ := []) (r₂ := [])
      (by rw [List.append_nil, List.append_nil, hf.1])).1, ?_,
    BitVec.eq_of_toNat_eq (be_injective (h256 ▸ a.commitment.isLt) (h256 ▸ b.commitment.isLt)
      hf.2.2)⟩
  have hc := hf.2.1
  cases ha : a.credit <;> cases hb : b.credit <;> simp [ha, hb] at hc ⊢

/-- The commitments of the debit legs. -/
def debits (legs : List CommittedLeg) : List (BitVec 256) :=
  (legs.filter (fun t => !t.credit)).map (·.commitment)

/-- The commitments of the credit legs. -/
def credits (legs : List CommittedLeg) : List (BitVec 256) :=
  (legs.filter (·.credit)).map (·.commitment)

/-- The checker for a joint turn over commitments: the pullback over the digest of the committed
forest, and the debit commitments balancing the credit commitments. -/
def checkJointCommitted (shared : ByteArray) (legs : List CommittedLeg) : Bool :=
  legs.all (fun t => decide (t.turnId = shared)) &&
    decide (shared = forestDigest (legs.map CommittedLeg.legBytes)) &&
    homCheck (debits legs) (credits legs)

theorem checkJointCommitted_iff (shared : ByteArray) (legs : List CommittedLeg) :
    checkJointCommitted shared legs = true ↔
      (∀ t, t ∈ legs → t.turnId = shared) ∧
        shared = forestDigest (legs.map CommittedLeg.legBytes) ∧
        bvSum (debits legs) = bvSum (credits legs) := by
  simp only [checkJointCommitted, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    homCheck_iff, and_assoc]

/-- **Conservation of hidden half-edges.** If the committed checker passes, the debit and credit
commitments open to `dOpen` and `cOpen` with equal blinding totals, and neither value total wraps,
then the hidden debits and credits are equal as natural numbers and every leg names the digest of
this committed forest. The checker read commitments only. -/
theorem jointTurn_committed_conservation_sound (key : CommitKey) (shared : ByteArray)
    (legs : List CommittedLeg) (dOpen cOpen : List Opening)
    (hcheck : checkJointCommitted shared legs = true)
    (hd : debits legs = dOpen.map (Opening.commit key))
    (hc : credits legs = cOpen.map (Opening.commit key))
    (hblind : blindSum dOpen = blindSum cOpen)
    (hdw : natSum (dOpen.map (·.value)) < 2 ^ 256) (hcw : natSum (cOpen.map (·.value)) < 2 ^ 256) :
    natSum (dOpen.map (·.value)) = natSum (cOpen.map (·.value)) ∧
      ∀ t, t ∈ legs → t.turnId = forestDigest (legs.map CommittedLeg.legBytes) := by
  obtain ⟨ha, hp, hs⟩ := (checkJointCommitted_iff shared legs).1 hcheck
  refine ⟨(private_conservation_nat_sum key dOpen cOpen hblind hdw hcw).1 ?_,
    fun t ht => (ha t ht).trans hp⟩
  rw [homCheck_iff, ← hd, ← hc]
  exact hs

/-- The premises of `jointTurn_committed_conservation_sound` are met together: a debit and a credit
of `5` under blinding `7`. -/
theorem jointTurn_committed_inhabited :
    ∃ (key : CommitKey) (shared : ByteArray) (legs : List CommittedLeg) (dOpen cOpen : List Opening),
      checkJointCommitted shared legs = true ∧ debits legs = dOpen.map (Opening.commit key) ∧
        credits legs = cOpen.map (Opening.commit key) ∧ blindSum dOpen = blindSum cOpen ∧
        legs.length = 2 := by
  refine ⟨demoKey,
    forestDigest [CommittedLeg.legBytes ⟨0, .empty, false, Opening.commit demoKey ⟨5#256, 7#256⟩⟩,
      CommittedLeg.legBytes ⟨1, .empty, true, Opening.commit demoKey ⟨5#256, 7#256⟩⟩],
    [⟨0, forestDigest [CommittedLeg.legBytes ⟨0, .empty, false, Opening.commit demoKey ⟨5#256, 7#256⟩⟩,
        CommittedLeg.legBytes ⟨1, .empty, true, Opening.commit demoKey ⟨5#256, 7#256⟩⟩], false,
        Opening.commit demoKey ⟨5#256, 7#256⟩⟩,
      ⟨1, forestDigest [CommittedLeg.legBytes ⟨0, .empty, false, Opening.commit demoKey ⟨5#256, 7#256⟩⟩,
        CommittedLeg.legBytes ⟨1, .empty, true, Opening.commit demoKey ⟨5#256, 7#256⟩⟩], true,
        Opening.commit demoKey ⟨5#256, 7#256⟩⟩],
    [⟨5#256, 7#256⟩], [⟨5#256, 7#256⟩], ?_, ?_, ?_, rfl, rfl⟩
  · rw [checkJointCommitted_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> rfl
    · simp only [List.map_cons, List.map_nil, CommittedLeg.legBytes]
    · simp [debits, credits]
  · simp [debits]
  · simp [credits]

/-! ## 4. Sorted tables -/

/-- Strictly ascending, checked on neighbours. -/
def ascending : List Nat → Bool
  | a :: b :: rest => decide (a < b) && ascending (b :: rest)
  | _ => true

theorem ascending_cons {a : Nat} : ∀ {l : List Nat}, ascending (a :: l) = true →
    (∀ x, x ∈ l → a < x) ∧ ascending l = true
  | [], _ => ⟨fun _ hx => (by cases hx), by rfl⟩
  | b :: l, h => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlt, _⟩ := ascending_cons h.2
    refine ⟨fun x hx => ?_, h.2⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (hlt x hx)

theorem ascending_pairwise : ∀ l : List Nat, ascending l = true → l.Pairwise (· < ·)
  | [], _ => .nil
  | _ :: l, h => .cons (ascending_cons h).1 (ascending_pairwise l (ascending_cons h).2)

section Table

variable {α : Type} (key : α → Nat)

/-- A table in key order: one merge sort. -/
def sortByKey (l : List α) : Array α :=
  (l.mergeSort (fun a b => decide (key a ≤ key b))).toArray

/-- The table's keys strictly ascend: no key occurs twice. One pass. -/
def tableOk (A : Array α) : Bool := ascending (A.toList.map key)

/-- Find the entry with key `k` by CapTP's binary search. -/
def lookup (A : Array α) (k : Nat) : Option α := CapTP.search key A k (A.size + 1) 0 A.size

theorem sortByKey_perm (l : List α) : (sortByKey key l).toList.Perm l := by
  simpa only [sortByKey, List.toList_toArray] using
    List.mergeSort_perm l (fun a b => decide (key a ≤ key b))

theorem tableOk_pairwise {A : Array α} (h : tableOk key A = true) :
    A.toList.Pairwise (fun a b => key a < key b) :=
  List.pairwise_map.1 (ascending_pairwise _ h)

theorem tableOk_nodup {A : Array α} (h : tableOk key A = true) : (A.toList.map key).Nodup :=
  (ascending_pairwise _ h).imp (fun hlt => Nat.ne_of_lt hlt)

theorem pairwise_key_unique : ∀ {l : List α}, l.Pairwise (fun a b => key a < key b) →
    ∀ {x y : α}, x ∈ l → y ∈ l → key x = key y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, hp, x, y, hx, hy, hk => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · have := ha y hy'
      omega
    · have := ha x hx'
      omega
    · exact pairwise_key_unique hl hx' hy' hk

/-- On a table that passed `tableOk`, the binary search is the list search. -/
theorem lookup_eq_find {A : Array α} (h : tableOk key A = true) (k : Nat) :
    lookup key A k = A.toList.find? (fun x => key x == k) := by
  have hs : CapTP.SortedBy key A := by
    intro i j hi hj hij
    have := List.pairwise_iff_getElem.1 (tableOk_pairwise key h) i j (by simpa using hi)
      (by simpa using hj) hij
    simpa using this
  rw [lookup, CapTP.search_eq_spec key A hs k, CapTP.findSpec]

theorem lookup_some {A : Array α} (h : tableOk key A = true) {k : Nat} {x : α}
    (hx : lookup key A k = some x) : x ∈ A.toList ∧ key x = k := by
  rw [lookup_eq_find key h] at hx
  exact ⟨List.mem_of_find?_eq_some hx, by simpa using List.find?_some hx⟩

theorem lookup_of_mem {A : Array α} (h : tableOk key A = true) {x : α} (hx : x ∈ A.toList) :
    lookup key A (key x) = some x := by
  rw [lookup_eq_find key h]
  cases hf : A.toList.find? (fun y => key y == key x) with
  | none =>
    have := List.find?_eq_none.1 hf x hx
    simp at this
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hk : key y = key x := by simpa using List.find?_some hf
    rw [pairwise_key_unique key (tableOk_pairwise key h) hy hx hk]

end Table

theorem nodup_of_map_nodup {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) :
    l.Nodup :=
  (List.pairwise_map.1 h).imp (fun hne heq => hne (congrArg f heq))

/-! ## 5. Receipts with open ports -/

/-- A promise hole: the pending id, a 32-byte commitment to the awaited payload, the guard the
resolution must satisfy, and the authority its resolver must show (the lineage digest of a root
grant, and the rights needed). -/
structure AwaitPort where
  port : CapTP.PendingId
  payload : ByteArray
  guard : DistPred
  resolverRoot : ByteArray
  need : UInt64

/-- A resolution of a promise: the pending id, the payload commitment, and the delegation chain
the resolver holds. -/
structure FulfillPort where
  port : CapTP.PendingId
  payload : ByteArray
  root : Block
  chain : Array Block

/-- A receipt with open ports: the local turn, its causal rank, the holes it awaits and the
promises it resolves. -/
structure CoReceipt where
  turn : LocalTurn
  rank : Nat
  awaits : List AwaitPort
  fulfills : List FulfillPort

/-- A hole with the rank of the receipt that awaits it. -/
structure AwaitEntry where
  rank : Nat
  hole : AwaitPort

/-- A resolution with the rank of the receipt that makes it. -/
structure FulfillEntry where
  rank : Nat
  fill : FulfillPort

def AwaitEntry.key (e : AwaitEntry) : Nat := e.hole.port.toNat
def FulfillEntry.key (e : FulfillEntry) : Nat := e.fill.port.toNat

/-- Every hole of a diagram. -/
def awaitTable (rs : List CoReceipt) : List AwaitEntry :=
  rs.flatMap fun r => r.awaits.map (AwaitEntry.mk r.rank)

/-- Every resolution of a diagram. -/
def fulfillTable (rs : List CoReceipt) : List FulfillEntry :=
  rs.flatMap fun r => r.fulfills.map (FulfillEntry.mk r.rank)

theorem mem_awaitTable {rs : List CoReceipt} {e : AwaitEntry} :
    e ∈ awaitTable rs ↔ ∃ b, b ∈ rs ∧ ∃ w, w ∈ b.awaits ∧ AwaitEntry.mk b.rank w = e := by
  simp only [awaitTable, List.mem_flatMap, List.mem_map]

theorem mem_fulfillTable {rs : List CoReceipt} {e : FulfillEntry} :
    e ∈ fulfillTable rs ↔ ∃ a, a ∈ rs ∧ ∃ f, f ∈ a.fulfills ∧ FulfillEntry.mk a.rank f = e := by
  simp only [fulfillTable, List.mem_flatMap, List.mem_map]

/-- What a wire is checked against: the revoked set, the facts caveats are evaluated on, the
discharges presented for guards, and the step the guards read. -/
structure WireEnv where
  revoked : RevokedSet
  facts : Nat → KleenePred3
  discharges : List VkId
  step : Step

/-- The resolver's chain descends from the root the hole names, folds with no revoked lineage or
channel, and carries the rights the hole needs. -/
def capOk (env : WireEnv) (w : AwaitPort) (f : FulfillPort) : Bool :=
  decide (rootLineage f.root = w.resolverRoot) &&
    match foldChain env.revoked env.facts f.root f.chain with
    | some acc => authorize acc w.need
    | none => false

/-- One wire: the payload commitments agree, the guard admits, the resolver is causally earlier,
and it is authorized. -/
def wireOk (env : WireEnv) (w : AwaitEntry) (f : FulfillEntry) : Bool :=
  decide (f.fill.payload = w.hole.payload) &&
    admits (dischargeOracle env.discharges) env.step w.hole.guard &&
    decide (f.rank < w.rank) && capOk env w.hole f.fill

/-- A resolution wired to its hole, as a proposition. -/
def Wired (env : WireEnv) (a : CoReceipt) (f : FulfillPort) (b : CoReceipt) (w : AwaitPort) :
    Prop :=
  f.payload = w.payload ∧ admits (dischargeOracle env.discharges) env.step w.guard = true ∧
    a.rank < b.rank ∧ rootLineage f.root = w.resolverRoot ∧
    ∃ acc, foldChain env.revoked env.facts f.root f.chain = some acc ∧ authorize acc w.need = true

theorem wireOk_iff (env : WireEnv) (a b : CoReceipt) (f : FulfillPort) (w : AwaitPort) :
    wireOk env ⟨b.rank, w⟩ ⟨a.rank, f⟩ = true ↔ Wired env a f b w := by
  simp only [wireOk, capOk, Wired, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  cases foldChain env.revoked env.facts f.root f.chain with
  | none => simp
  | some acc => simp

/-- **A wired resolver is revocation-clean on every prefix** of its chain: no ancestor's lineage
nullifier is in the revoked set. -/
theorem wired_revocation_clean {env : WireEnv} {a b : CoReceipt} {f : FulfillPort} {w : AwaitPort}
    (h : Wired env a f b w) (pre ext : Array Block) (hsplit : f.chain = pre ++ ext) :
    env.revoked.contains (credNul (lineageOf f.root pre.toList)) = false := by
  obtain ⟨_, _, _, _, acc, hfold, _⟩ := h
  rw [hsplit] at hfold
  have hl := (foldChain_prefix_live env.revoked env.facts f.root pre ext acc hfold).1
  simpa [lineageLive] using hl

/-- The hole table in port order. -/
def sortedAwaits (rs : List CoReceipt) : Array AwaitEntry := sortByKey AwaitEntry.key (awaitTable rs)

/-- The resolution table in port order. -/
def sortedFulfills (rs : List CoReceipt) : Array FulfillEntry :=
  sortByKey FulfillEntry.key (fulfillTable rs)

/-- **Port linearity**: both tables strictly ascend, so no pending id is awaited twice and none is
resolved twice. -/
def portsLinear (rs : List CoReceipt) : Bool :=
  tableOk AwaitEntry.key (sortedAwaits rs) && tableOk FulfillEntry.key (sortedFulfills rs)

/-- Check a resolution against the hole it fills, if the diagram has that hole. -/
def wireChecks (env : WireEnv) (awaits : Array AwaitEntry) (f : FulfillEntry) : Bool :=
  match lookup AwaitEntry.key awaits f.key with
  | some w => wireOk env w f
  | none => true

/-- Every resolution that meets a hole passes its wire check. -/
def wiresOk (env : WireEnv) (rs : List CoReceipt) : Bool :=
  (sortedFulfills rs).toList.all (wireChecks env (sortedAwaits rs))

/-- The holes no resolution of the diagram fills. -/
def openAwaitsOf (rs : List CoReceipt) : List AwaitEntry :=
  (sortedAwaits rs).toList.filter fun w =>
    (lookup FulfillEntry.key (sortedFulfills rs) w.key).isNone

/-- The resolutions whose hole is not in the diagram. -/
def danglingOf (rs : List CoReceipt) : List FulfillEntry :=
  (sortedFulfills rs).toList.filter fun f =>
    (lookup AwaitEntry.key (sortedAwaits rs) f.key).isNone

/-- A diagram with no open port must be a joint turn. -/
def closureOk (shared : ByteArray) (rs : List CoReceipt) : Bool :=
  !((openAwaitsOf rs).isEmpty && (danglingOf rs).isEmpty) || checkJoint shared (rs.map (·.turn))

/-- A composed diagram: the shared turn digest, the legs, and the ports still open. -/
structure Composite where
  shared : ByteArray
  legs : List LocalTurn
  openAwaits : List AwaitEntry
  dangling : List FulfillEntry

/-- **Compose receipts along their promises.** Every receipt names the shared turn; the ports are
linear; every wire checks; and a diagram left with no open port is a joint turn. -/
def composeCoReceipts (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt) :
    Option Composite :=
  if (rs.all fun r => decide (r.turn.turnId = shared)) && portsLinear rs && wiresOk env rs &&
      closureOk shared rs then
    some ⟨shared, rs.map (·.turn), openAwaitsOf rs, danglingOf rs⟩
  else none

theorem composeCoReceipts_eq_some_iff (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (c : Composite) :
    composeCoReceipts env shared rs = some c ↔
      (∀ r, r ∈ rs → r.turn.turnId = shared) ∧ portsLinear rs = true ∧ wiresOk env rs = true ∧
        closureOk shared rs = true ∧
        c = ⟨shared, rs.map (·.turn), openAwaitsOf rs, danglingOf rs⟩ := by
  unfold composeCoReceipts
  split
  · rename_i hc
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    simp only [Option.some.injEq]
    constructor
    · intro he
      exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, he.symm⟩
    · intro he
      exact he.2.2.2.2.symm
  · rename_i hc
    constructor
    · intro he
      cases he
    · intro he
      refine absurd ?_ hc
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨he.1, he.2.1⟩, he.2.2.1⟩, he.2.2.2.1⟩

/-- **Every wire of an accepted diagram was checked.** Whenever a resolution and a hole of the
diagram share a pending id, that resolution is wired to that hole. -/
theorem wire_checked (env : WireEnv) (rs : List CoReceipt) (hlin : portsLinear rs = true)
    (hw : wiresOk env rs = true) {a b : CoReceipt} (ha : a ∈ rs) (hb : b ∈ rs)
    {f : FulfillPort} {w : AwaitPort} (hf : f ∈ a.fulfills) (hwm : w ∈ b.awaits)
    (hport : f.port = w.port) : Wired env a f b w := by
  have hfe : (⟨a.rank, f⟩ : FulfillEntry) ∈ (sortedFulfills rs).toList :=
    (sortByKey_perm _ _).mem_iff.2 (mem_fulfillTable.2 ⟨a, ha, f, hf, rfl⟩)
  have hwe : (⟨b.rank, w⟩ : AwaitEntry) ∈ (sortedAwaits rs).toList :=
    (sortByKey_perm _ _).mem_iff.2 (mem_awaitTable.2 ⟨b, hb, w, hwm, rfl⟩)
  simp only [portsLinear, Bool.and_eq_true] at hlin
  have hchk := List.all_eq_true.1 hw _ hfe
  have hk : FulfillEntry.key ⟨a.rank, f⟩ = AwaitEntry.key ⟨b.rank, w⟩ := by
    simp only [FulfillEntry.key, AwaitEntry.key, hport]
  unfold wireChecks at hchk
  rw [hk, lookup_of_mem AwaitEntry.key hlin.1 hwe] at hchk
  exact (wireOk_iff env a b f w).1 hchk

/-- An accepted diagram has linear ports: every pending id is awaited at most once and resolved at
most once across all its receipts. -/
theorem composeCoReceipts_ports_linear (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (c : Composite) (h : composeCoReceipts env shared rs = some c) :
    ((awaitTable rs).map (·.hole.port)).Nodup ∧ ((fulfillTable rs).map (·.fill.port)).Nodup := by
  obtain ⟨_, hlin, _, _, _⟩ := (composeCoReceipts_eq_some_iff env shared rs c).1 h
  simp only [portsLinear, Bool.and_eq_true] at hlin
  constructor
  · have h1 := ((sortByKey_perm AwaitEntry.key (awaitTable rs)).map AwaitEntry.key).nodup_iff.1
      (tableOk_nodup AwaitEntry.key hlin.1)
    refine nodup_of_map_nodup UInt64.toNat ?_
    rw [List.map_map]
    exact h1
  · have h1 := ((sortByKey_perm FulfillEntry.key (fulfillTable rs)).map FulfillEntry.key).nodup_iff.1
      (tableOk_nodup FulfillEntry.key hlin.2)
    refine nodup_of_map_nodup UInt64.toNat ?_
    rw [List.map_map]
    exact h1

/-- **No promise hole is allocated twice or filled twice.** A diagram in which two holes, or two
resolutions, carry one pending id does not compose. -/
theorem promise_hole_no_double_fill (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (hdup : ¬ ((awaitTable rs).map (·.hole.port)).Nodup ∨
      ¬ ((fulfillTable rs).map (·.fill.port)).Nodup) :
    composeCoReceipts env shared rs = none := by
  cases hc : composeCoReceipts env shared rs with
  | none => rfl
  | some c =>
    have hl := composeCoReceipts_ports_linear env shared rs c hc
    rcases hdup with hd | hd
    · exact absurd hl.1 hd
    · exact absurd hl.2 hd

/-- `b` awaits a promise that `a` resolves. -/
def Feeds (a b : CoReceipt) : Prop :=
  ∃ f, f ∈ a.fulfills ∧ ∃ w, w ∈ b.awaits ∧ f.port = w.port

/-- Causal dependency within a diagram: the transitive closure of `Feeds`. -/
inductive Causes (rs : List CoReceipt) : CoReceipt → CoReceipt → Prop where
  | step {a b : CoReceipt} : a ∈ rs → b ∈ rs → Feeds a b → Causes rs a b
  | trans {a b c : CoReceipt} : Causes rs a b → Causes rs b c → Causes rs a c

/-- In an accepted diagram, rank strictly increases along causal dependency. -/
theorem composeCoReceipts_rank_increases (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (c : Composite) (h : composeCoReceipts env shared rs = some c) {a b : CoReceipt}
    (hab : Causes rs a b) : a.rank < b.rank := by
  obtain ⟨_, hlin, hw, _, _⟩ := (composeCoReceipts_eq_some_iff env shared rs c).1 h
  induction hab with
  | step ha hb hfeeds =>
    obtain ⟨f, hf, w, hwm, hport⟩ := hfeeds
    exact (wire_checked env rs hlin hw ha hb hf hwm hport).2.2.1
  | trans _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

/-- **A causal cycle is refused.** If some receipt of the diagram transitively awaits a promise it
resolves itself, the diagram does not compose, whatever ranks it claims. -/
theorem cyclic_wiring_refused (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (hcycle : ∃ a, Causes rs a a) : composeCoReceipts env shared rs = none := by
  cases hc : composeCoReceipts env shared rs with
  | none => rfl
  | some c =>
    obtain ⟨a, ha⟩ := hcycle
    exact absurd (composeCoReceipts_rank_increases env shared rs c hc ha) (Nat.lt_irrefl _)

/-- **A revoked lineage is refused.** If a resolution meets a hole of the diagram and any prefix of
its delegation chain has a revoked lineage nullifier, the diagram does not compose. -/
theorem revoked_lineage_refused (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    {a b : CoReceipt} (ha : a ∈ rs) (hb : b ∈ rs) {f : FulfillPort} {w : AwaitPort}
    (hf : f ∈ a.fulfills) (hwm : w ∈ b.awaits) (hport : f.port = w.port) (pre ext : Array Block)
    (hsplit : f.chain = pre ++ ext)
    (hrev : env.revoked.contains (credNul (lineageOf f.root pre.toList)) = true) :
    composeCoReceipts env shared rs = none := by
  cases hc : composeCoReceipts env shared rs with
  | none => rfl
  | some c =>
    obtain ⟨_, hlin, hw, _, _⟩ := (composeCoReceipts_eq_some_iff env shared rs c).1 hc
    have hclean := wired_revocation_clean (wire_checked env rs hlin hw ha hb hf hwm hport) pre ext
      hsplit
    rw [hrev] at hclean
    cases hclean

/-- **A closed diagram is one joint turn.** If the receipts compose and no port is left open, then:
the legs are a joint turn under the shared digest (so the total balance is conserved); every
resolution is wired to a hole and every hole to a resolution, each wire with agreeing payload
commitments, an admitted guard, a causally earlier and authorized resolver; ports are linear; and
there is no causal cycle. -/
theorem composeCoReceipts_closed_sound (env : WireEnv) (shared : ByteArray) (rs : List CoReceipt)
    (c : Composite) (h : composeCoReceipts env shared rs = some c)
    (hopen : c.openAwaits = []) (hdangling : c.dangling = []) :
    (∃ j : JointTurn, j.legs = rs.map (·.turn) ∧ j.shared.tid = shared) ∧
      (∀ a f, a ∈ rs → f ∈ a.fulfills →
        ∃ b w, b ∈ rs ∧ w ∈ b.awaits ∧ f.port = w.port ∧ Wired env a f b w) ∧
      (∀ b w, b ∈ rs → w ∈ b.awaits →
        ∃ a f, a ∈ rs ∧ f ∈ a.fulfills ∧ f.port = w.port ∧ Wired env a f b w) ∧
      ((awaitTable rs).map (·.hole.port)).Nodup ∧ ((fulfillTable rs).map (·.fill.port)).Nodup ∧
      ∀ a, ¬ Causes rs a a := by
  have hlinear := composeCoReceipts_ports_linear env shared rs c h
  have hrank := fun (a : CoReceipt) (ha : Causes rs a a) =>
    Nat.lt_irrefl _ (composeCoReceipts_rank_increases env shared rs c h ha)
  obtain ⟨_, hlin, hw, hclosure, rfl⟩ := (composeCoReceipts_eq_some_iff env shared rs c).1 h
  have hlin' := hlin
  simp only [portsLinear, Bool.and_eq_true] at hlin'
  simp only at hopen hdangling
  refine ⟨?_, ?_, ?_, hlinear.1, hlinear.2, hrank⟩
  · apply (checkJoint_iff shared _).1
    simpa [closureOk, hopen, hdangling] using hclosure
  · intro a f ha hf
    have hfe : (⟨a.rank, f⟩ : FulfillEntry) ∈ (sortedFulfills rs).toList :=
      (sortByKey_perm _ _).mem_iff.2 (mem_fulfillTable.2 ⟨a, ha, f, hf, rfl⟩)
    have hsome := List.filter_eq_nil_iff.1 hdangling _ hfe
    cases hl : lookup AwaitEntry.key (sortedAwaits rs) (FulfillEntry.key ⟨a.rank, f⟩) with
    | none => simp [hl] at hsome
    | some e =>
      obtain ⟨he, hk⟩ := lookup_some AwaitEntry.key hlin'.1 hl
      obtain ⟨b, hb, w, hwm, rfl⟩ := mem_awaitTable.1 ((sortByKey_perm _ _).mem_iff.1 he)
      have hport : f.port = w.port := (UInt64.toNat_inj.1 hk).symm
      exact ⟨b, w, hb, hwm, hport, wire_checked env rs hlin hw ha hb hf hwm hport⟩
  · intro b w hb hwm
    have hwe : (⟨b.rank, w⟩ : AwaitEntry) ∈ (sortedAwaits rs).toList :=
      (sortByKey_perm _ _).mem_iff.2 (mem_awaitTable.2 ⟨b, hb, w, hwm, rfl⟩)
    have hsome := List.filter_eq_nil_iff.1 hopen _ hwe
    cases hl : lookup FulfillEntry.key (sortedFulfills rs) (AwaitEntry.key ⟨b.rank, w⟩) with
    | none => simp [hl] at hsome
    | some e =>
      obtain ⟨he, hk⟩ := lookup_some FulfillEntry.key hlin'.2 hl
      obtain ⟨a, ha, f, hf, rfl⟩ := mem_fulfillTable.1 ((sortByKey_perm _ _).mem_iff.1 he)
      have hport : f.port = w.port := UInt64.toNat_inj.1 hk
      exact ⟨a, f, ha, hf, hport, wire_checked env rs hlin hw ha hb hf hwm hport⟩

/-! ## 6. A closed diagram -/

/-- A leg of the witness diagram. -/
def demoLeg (vat : VatId) (half : Int) (tid : ByteArray) : LocalTurn :=
  ⟨vat, tid, .empty, 0, half, half⟩

/-- The root grant the witness resolver holds: right `1`, no caveat. -/
def demoGrant : Block := ⟨1, .const true, .empty, .empty⟩

/-- The turn digest of the witness diagram. -/
def demoShared : ByteArray := turnDigest [demoLeg 0 (-1) .empty, demoLeg 1 1 .empty]

/-- Two vats and one promise: vat `0` pays one unit and resolves pending id `5` under its grant;
vat `1` receives the unit and awaits id `5` from a holder of that grant. -/
def demoDiagram : List CoReceipt :=
  [⟨demoLeg 0 (-1) demoShared, 0, [], [⟨5, .empty, demoGrant, #[]⟩]⟩,
    ⟨demoLeg 1 1 demoShared, 1, [⟨5, .empty, .tt, rootLineage demoGrant, 1⟩], []⟩]

/-- Nothing revoked, no fact bound, no discharge, an empty step. -/
def demoEnv : WireEnv := ⟨RevokedSet.empty, fun _ => .unbound3, [], fun _ => ⟨none, none⟩⟩

/-- The premises of `composeCoReceipts_closed_sound` are met together: the two-vat diagram composes
and is closed. -/
theorem composeCoReceipts_closed_inhabited :
    ∃ c, composeCoReceipts demoEnv demoShared demoDiagram = some c ∧ c.openAwaits = [] ∧
      c.dangling = [] ∧ demoDiagram.length = 2 := by
  have hA : sortedAwaits demoDiagram = #[⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩] := by
    simp [sortedAwaits, sortByKey, awaitTable, demoDiagram]
  have hF : sortedFulfills demoDiagram = #[⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩] := by
    simp [sortedFulfills, sortByKey, fulfillTable, demoDiagram]
  have hTA : tableOk AwaitEntry.key
      #[⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩] = true := by
    simp [tableOk, ascending]
  have hTF : tableOk FulfillEntry.key #[⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩] = true := by
    simp [tableOk, ascending]
  have hLA : lookup AwaitEntry.key #[⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩]
      (FulfillEntry.key ⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩) =
        some ⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩ :=
    lookup_of_mem AwaitEntry.key hTA (x := ⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩)
      (by simp)
  have hLF : lookup FulfillEntry.key #[⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩]
      (AwaitEntry.key ⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩) =
        some ⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩ :=
    lookup_of_mem FulfillEntry.key hTF (x := ⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩) (by simp)
  have hfold : foldChain demoEnv.revoked demoEnv.facts demoGrant #[] =
      some ⟨1, .true3, rootLineage demoGrant⟩ := by
    simp [foldChain, foldRoot, lineageLive, channelLive, RevokedSet.contains, RevokedSet.empty,
      searchAux, demoEnv, demoGrant, Caveat.eval]
  have hwire : wireOk demoEnv ⟨1, ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩⟩
      ⟨0, ⟨5, .empty, demoGrant, #[]⟩⟩ = true :=
    (wireOk_iff demoEnv ⟨demoLeg 0 (-1) demoShared, 0, [], [⟨5, .empty, demoGrant, #[]⟩]⟩
      ⟨demoLeg 1 1 demoShared, 1, [⟨5, .empty, .tt, rootLineage demoGrant, 1⟩], []⟩
      ⟨5, .empty, demoGrant, #[]⟩ ⟨5, .empty, .tt, rootLineage demoGrant, 1⟩).2
      ⟨rfl, admits_tt _ _, by decide, rfl, _, hfold, by decide⟩
  have hjoint : checkJoint demoShared (demoDiagram.map (·.turn)) = true := by
    simp only [checkJoint, demoDiagram, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨by decide, by decide⟩, rfl, rfl⟩, ?_⟩, by decide⟩
    simp only [demoShared, turnDigest, List.map_cons, List.map_nil, LocalTurn.legBytes, demoLeg]
  refine ⟨⟨demoShared, demoDiagram.map (·.turn), openAwaitsOf demoDiagram, danglingOf demoDiagram⟩,
    (composeCoReceipts_eq_some_iff _ _ _ _).2 ⟨?_, ?_, ?_, ?_, rfl⟩, ?_, ?_, rfl⟩
  · intro r hr
    simp only [demoDiagram, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · simp only [portsLinear, hA, hF, hTA, hTF, Bool.and_self]
  · simp only [wiresOk, hA, hF, List.all_cons, List.all_nil, Bool.and_true, wireChecks, hLA, hwire]
  · simp only [closureOk, hjoint, Bool.or_true]
  · simp only [openAwaitsOf, hA, hF, List.filter_cons, List.filter_nil, hLF, Option.isNone_some,
      Bool.false_eq_true, ↓reduceIte]
  · simp only [danglingOf, hA, hF, List.filter_cons, List.filter_nil, hLA, Option.isNone_some,
      Bool.false_eq_true, ↓reduceIte]

end Obend.Polis.JointCoReceipt
end
