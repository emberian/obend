module
/-
# Obend.Polis.ZoeSeatSettlement — ZoE seat settlement on the ledger spine

Offers, seats and exits are `Obend.Ledger.Seat`'s (`Proposal`, `Seat`, `admitOffer` with its
donation guard and one-time invitations, `exitSeat`, `checkBatchReallocSafe`), run on the seat
`Book`, and every leg they move is also posted to the typed `FloorBook` through
`FloorBook.admitBatch`, which decides. `AssetBundle` is the executable form of a proposal's asset
lists. A seat's holder is a 256-bit commitment opened by its preimage. `ValidZoeTrace` and
`trace_invariant` carry the floors and every asset's total along any trace.
-/
public import Obend.Logic.SeparationFrame
public import Obend.Polis.CapTP
public import Obend.Ledger.Seat
public import Obend.Digest.HashBytes
public import Obend.Digest.Cshake256.Spec
import all Obend.Polis.CapTP

public section
namespace Obend.Polis.ZoeSeatSettlement

/-! ## 1. `AssetBundle`: sorted, positive, 64-bit amounts with a checked linear merge -/

abbrev AssetBrand := Nat
abbrev SeatId := Nat
abbrev Entry := AssetBrand × UInt64

def Canonical (xs : List Entry) : Prop :=
  xs.Pairwise (fun a b => a.1 < b.1) ∧ ∀ p ∈ xs, 0 < p.2.toNat

structure AssetBundle where
  entries : Array Entry
  canonical : Canonical entries.toList

def amountList : List Entry → AssetBrand → Nat
  | [], _ => 0
  | (k, v) :: xs, b => (if k = b then v.toNat else 0) + amountList xs b

def AssetBundle.amountSpec (a : AssetBundle) : AssetBrand → Nat := amountList a.entries.toList

def AssetBundle.empty : AssetBundle := ⟨#[], by simp [Canonical]⟩

def AssetBundle.singleton (b : AssetBrand) (v : UInt64) (hv : 0 < v.toNat) : AssetBundle :=
  ⟨#[(b, v)], by simpa [Canonical] using hv⟩

theorem amountList_zero {xs : List Entry} {b : Nat}
    (h : ∀ p ∈ xs, p.1 ≠ b) : amountList xs b = 0 := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    simp only [amountList, h p (by simp), ↓reduceIte, Nat.zero_add]
    exact ih (fun p hp => h p (by simp [hp]))

theorem amountList_lookup {xs : List Entry} (hs : xs.Pairwise (fun a b => a.1 < b.1)) (b : Nat) :
    amountList xs b = ((xs.find? (fun p => p.1 == b)).map (fun p => p.2.toNat)).getD 0 := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨hp, ht⟩ := List.pairwise_cons.mp hs
    by_cases hb : p.1 = b
    · have hz : amountList xs b = 0 := amountList_zero (fun q hq => by have := hp q hq; simp only [AssetBrand] at *; omega)
      simp [amountList, hb, hz]
    · simp [amountList, hb, ih ht]

def AssetBundle.amountOf (a : AssetBundle) (b : AssetBrand) : Nat :=
  ((CapTP.search Prod.fst a.entries b (a.entries.size + 1) 0 a.entries.size).map
    (fun p => p.2.toNat)).getD 0

theorem AssetBundle.amountOf_eq_spec (a : AssetBundle) (b : AssetBrand) :
    a.amountOf b = a.amountSpec b := by
  have hs : CapTP.SortedBy Prod.fst a.entries := by
    intro i j hi hj hij
    exact (List.pairwise_iff_getElem.mp a.canonical.1) i j (by simpa using hi)
      (by simpa using hj) hij
  rw [amountOf, CapTP.search_eq_spec _ _ hs, amountSpec, amountList_lookup a.canonical.1]
  rfl

def AssetBundle.bundleLeq (a b : AssetBundle) : Bool :=
  a.entries.all (fun p => decide (p.2.toNat ≤ b.amountOf p.1))

theorem amountList_member {xs : List Entry} (hs : xs.Pairwise (fun a b => a.1 < b.1))
    {p : Entry} (hp : p ∈ xs) : amountList xs p.1 = p.2.toNat := by
  induction xs with
  | nil => cases hp
  | cons q xs ih =>
    obtain ⟨hq, ht⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hp with rfl | hp
    · have hz : amountList xs p.1 = 0 := amountList_zero (fun p hp => by have := hq p hp; simp only [AssetBrand] at *; omega)
      simp [amountList, hz]
    · have hne : q.1 ≠ p.1 := by have := hq p hp; simp only [AssetBrand] at *; omega
      simp [amountList, hne, ih ht hp]

theorem AssetBundle.bundleLeq_iff_forall_brand (a b : AssetBundle) :
    a.bundleLeq b = true ↔ ∀ k, a.amountSpec k ≤ b.amountSpec k := by
  simp only [bundleLeq, ← Array.all_toList, List.all_eq_true, decide_eq_true_eq, amountOf_eq_spec]
  constructor
  · intro h k
    by_cases hk : ∃ p ∈ a.entries.toList, p.1 = k
    · obtain ⟨p, hp, rfl⟩ := hk
      rw [amountSpec, amountList_member a.canonical.1 hp]
      exact h p (by simpa using hp)
    · have hz := amountList_zero (xs := a.entries.toList) (b := k) (by grind)
      simp [amountSpec, hz]
  · intro h p hp
    have hm : p ∈ a.entries.toList := by simpa using hp
    simpa [amountSpec, amountList_member a.canonical.1 hm] using h p.1

/-- Linear merge; the sum is checked in the unbounded domain before conversion. -/
def mergeAmounts : List Entry → List Entry → Option (List Entry)
  | [], ys => some ys
  | x :: xs, [] => some (x :: xs)
  | x :: xs, y :: ys =>
    if x.1 < y.1 then (mergeAmounts xs (y :: ys)).map (x :: ·)
    else if y.1 < x.1 then (mergeAmounts (x :: xs) ys).map (y :: ·)
    else if x.2.toNat + y.2.toNat < 2^64 then
      (mergeAmounts xs ys).map ((x.1, UInt64.ofNat (x.2.toNat + y.2.toNat)) :: ·)
    else none
termination_by xs ys => xs.length + ys.length

theorem mergeAmounts_sum : ∀ {xs ys zs : List Entry}, mergeAmounts xs ys = some zs →
    ∀ b, amountList zs b = amountList xs b + amountList ys b
  | [], _, _, h, b => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; simp [amountList]
  | _ :: _, [], _, h, b => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; simp [amountList]
  | x :: xs, y :: ys, _, h, b => by
    simp only [mergeAmounts] at h
    split at h
    · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [amountList, mergeAmounts_sum hz b]; simp only [AssetBrand] at *; omega
    · split at h
      · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [amountList, mergeAmounts_sum hz b]; simp only [AssetBrand] at *; omega
      · split at h
        · rename_i hx hy hbound
          obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
          have hk : x.1 = y.1 := by simp only [AssetBrand] at *; omega
          simp only [amountList, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hbound,
            mergeAmounts_sum hz b, hk]
          split <;> (simp only [AssetBrand] at *; omega)
        · cases h
termination_by xs ys _ _ _ => xs.length + ys.length

theorem mergeAmounts_keys : ∀ {xs ys zs : List Entry}, mergeAmounts xs ys = some zs →
    ∀ p ∈ zs, (∃ q ∈ xs, q.1 = p.1) ∨ (∃ q ∈ ys, q.1 = p.1)
  | [], _, _, h, p, hp => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; exact .inr ⟨p, hp, rfl⟩
  | _ :: _, [], _, h, p, hp => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; exact .inl ⟨p, hp, rfl⟩
  | x :: xs, y :: ys, _, h, p, hp => by
    simp only [mergeAmounts] at h
    split at h
    · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact .inl ⟨p, by simp, rfl⟩
      · rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | hy
        · exact .inl ⟨q, by simp [hq], hk⟩
        · exact .inr hy
    · split at h
      · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
        rcases List.mem_cons.mp hp with rfl | hp
        · exact .inr ⟨p, by simp, rfl⟩
        · rcases mergeAmounts_keys hz p hp with hx | ⟨q,hq,hk⟩
          · exact .inl hx
          · exact .inr ⟨q, by simp [hq], hk⟩
      · split at h
        · obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
          rcases List.mem_cons.mp hp with rfl | hp
          · exact .inl ⟨x, by simp, rfl⟩
          · rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | ⟨q,hq,hk⟩
            · exact .inl ⟨q, by simp [hq], hk⟩
            · exact .inr ⟨q, by simp [hq], hk⟩
        · cases h
termination_by xs ys _ _ _ _ => xs.length + ys.length

theorem mergeAmounts_canonical : ∀ {xs ys zs : List Entry}, Canonical xs → Canonical ys →
    mergeAmounts xs ys = some zs → Canonical zs
  | [], _, _, _, hy, h => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; exact hy
  | _ :: _, [], _, hx, _, h => by simp only [mergeAmounts, Option.some.injEq] at h; subst h; exact hx
  | x :: xs, y :: ys, _, ⟨.cons hx sx, px⟩, ⟨.cons hy sy, py⟩, h => by
    have cx : Canonical xs := ⟨sx, fun p hp => px p (by simp [hp])⟩
    have cy : Canonical ys := ⟨sy, fun p hp => py p (by simp [hp])⟩
    simp only [mergeAmounts] at h
    split at h
    · rename_i hxy
      obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨sz, pz⟩ := mergeAmounts_canonical cx ⟨.cons hy sy, py⟩ hz
      refine ⟨.cons ?_ sz, ?_⟩
      · intro p hp
        rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | ⟨q,hq,hk⟩
        · have := hx q hq; simp only [AssetBrand] at *; omega
        · rcases List.mem_cons.mp hq with rfl | hq
          · simp only [AssetBrand] at *; omega
          · have := hy q hq; simp only [AssetBrand] at *; omega
      · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
        · exact px p (by simp)
        · exact pz p hp
    · split at h
      · rename_i hxy hyx
        obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨sz, pz⟩ := mergeAmounts_canonical ⟨.cons hx sx, px⟩ cy hz
        refine ⟨.cons ?_ sz, ?_⟩
        · intro p hp
          rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | ⟨q,hq,hk⟩
          · rcases List.mem_cons.mp hq with rfl | hq
            · simp only [AssetBrand] at *; omega
            · have := hx q hq; simp only [AssetBrand] at *; omega
          · have := hy q hq; simp only [AssetBrand] at *; omega
        · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
          · exact py p (by simp)
          · exact pz p hp
      · split at h
        · rename_i hxy hyx hb
          obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨sz, pz⟩ := mergeAmounts_canonical cx cy hz
          refine ⟨.cons ?_ sz, ?_⟩
          · intro p hp
            rcases mergeAmounts_keys hz p hp with ⟨q,hq,hk⟩ | ⟨q,hq,hk⟩
            · have := hx q hq; dsimp; simp only [AssetBrand] at *; omega
            · have := hy q hq; dsimp; simp only [AssetBrand] at *; omega
          · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
            · simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hb]
              have := px x (by simp); simp only [AssetBrand] at *; omega
            · exact pz p hp
        · cases h
termination_by xs ys _ _ _ _ => xs.length + ys.length

def AssetBundle.addChecked (a b : AssetBundle) : Option AssetBundle :=
  match h : mergeAmounts a.entries.toList b.entries.toList with
  | none => none
  | some zs => some ⟨zs.toArray, by simpa using mergeAmounts_canonical a.canonical b.canonical h⟩

theorem AssetBundle.addChecked_sum {a b c : AssetBundle} (h : a.addChecked b = some c) :
    ∀ k, c.amountSpec k = a.amountSpec k + b.amountSpec k := by
  unfold addChecked at h
  split at h
  · cases h
  · cases h
    exact mergeAmounts_sum ‹_›


theorem amountList_tail_le (x : Entry) (xs : List Entry) (b : Nat) :
    amountList xs b ≤ amountList (x :: xs) b := by simp [amountList]

theorem mergeAmounts_complete : ∀ (xs ys : List Entry),
    (∀ k, amountList xs k + amountList ys k < 2^64) →
    ∃ zs, mergeAmounts xs ys = some zs
  | [], ys, _ => ⟨ys, by simp [mergeAmounts]⟩
  | x :: xs, [], _ => ⟨x :: xs, by simp [mergeAmounts]⟩
  | x :: xs, y :: ys, hb => by
    simp only [mergeAmounts]
    split
    · obtain ⟨zs,hz⟩ := mergeAmounts_complete xs (y :: ys) (fun k =>
        Nat.lt_of_le_of_lt (Nat.add_le_add_right (amountList_tail_le x xs k) _) (hb k))
      exact ⟨x :: zs, by simp [hz]⟩
    · split
      · obtain ⟨zs,hz⟩ := mergeAmounts_complete (x :: xs) ys (fun k =>
          Nat.lt_of_le_of_lt (Nat.add_le_add_left (amountList_tail_le y ys k) _) (hb k))
        exact ⟨y :: zs, by simp [hz]⟩
      · rename_i hx hy
        have hk : x.1 = y.1 := by simp only [AssetBrand] at *; omega
        have hv : x.2.toNat + y.2.toNat < 2^64 := by
          have := hb x.1
          simp only [amountList, ← hk, ↓reduceIte] at this
          omega
        rw [ite_eq_left hv]
        obtain ⟨zs,hz⟩ := mergeAmounts_complete xs ys (fun k =>
          Nat.lt_of_le_of_lt (Nat.add_le_add (amountList_tail_le x xs k)
            (amountList_tail_le y ys k)) (hb k))
        exact ⟨(x.1, UInt64.ofNat (x.2.toNat + y.2.toNat)) :: zs, by simp [hz]⟩
termination_by xs ys _ => xs.length + ys.length

theorem amountList_bound {xs : List Entry} (hc : Canonical xs) (k : Nat) :
    amountList xs k < 2^64 := by
  by_cases hk : ∃ p ∈ xs, p.1 = k
  · obtain ⟨p,hp,rfl⟩ := hk
    rw [amountList_member hc.1 hp]
    exact p.2.toNat_lt
  · rw [amountList_zero (by grind : ∀ p ∈ xs, p.1 ≠ k)]
    decide

theorem amountList_ext : ∀ {xs ys : List Entry}, Canonical xs → Canonical ys →
    (∀ k, amountList xs k = amountList ys k) → xs = ys
  | [], [], _, _, _ => rfl
  | x :: xs, [], hx, _, h => by
    have := h x.1
    have := hx.2 x (by simp)
    simp [amountList] at *; omega
  | [], y :: ys, _, hy, h => by
    have := h y.1
    have := hy.2 y (by simp)
    simp [amountList] at *; omega
  | x :: xs, y :: ys, ⟨.cons hx sx, px⟩, ⟨.cons hy sy, py⟩, h => by
    have hk : x.1 = y.1 := by
      by_cases hn : x.1 = y.1
      · exact hn
      exfalso
      have hxn := px x (by simp)
      have hyn := py y (by simp)
      rcases Nat.lt_or_gt_of_ne hn with hl | hl
      · have hz : amountList (y :: ys) x.1 = 0 := amountList_zero (by
          intro p hp; rcases List.mem_cons.mp hp with rfl | hp
          · simp only [AssetBrand] at *; omega
          · have := hy p hp; simp only [AssetBrand] at *; omega)
        have := h x.1; rw [hz] at this; simp only [amountList, ↓reduceIte] at this; omega
      · have hz : amountList (x :: xs) y.1 = 0 := amountList_zero (by
          intro p hp; rcases List.mem_cons.mp hp with rfl | hp
          · simp only [AssetBrand] at *; omega
          · have := hx p hp; simp only [AssetBrand] at *; omega)
        have := h y.1; rw [hz] at this; simp only [amountList, ↓reduceIte] at this; omega
    have hv : x.2 = y.2 := by
      apply UInt64.toNat_inj.mp
      have he := h x.1
      rw [amountList_member (.cons hx sx) (by simp), hk,
        amountList_member (.cons hy sy) (by simp)] at he
      exact he
    have ht : xs = ys := amountList_ext ⟨sx, fun p hp => px p (by simp [hp])⟩
      ⟨sy, fun p hp => py p (by simp [hp])⟩ (fun k => by
        have := h k
        simp only [amountList, hk, hv] at this
        omega)
    rw [Prod.ext hk hv, ht]

theorem AssetBundle.ext {a b : AssetBundle} (h : ∀ k, a.amountSpec k = b.amountSpec k) : a = b := by
  have he := Array.ext' (amountList_ext a.canonical b.canonical h)
  cases a; cases b; cases he; rfl

theorem AssetBundle.addChecked_eq_some_iff_no_overflow_and_sum (a b c : AssetBundle) :
    a.addChecked b = some c ↔
      (∀ k, a.amountSpec k + b.amountSpec k < 2^64) ∧
      (∀ k, c.amountSpec k = a.amountSpec k + b.amountSpec k) := by
  constructor
  · intro h
    have hs := addChecked_sum h
    exact ⟨fun k => hs k ▸ amountList_bound c.canonical k, hs⟩
  · rintro ⟨hb,hs⟩
    obtain ⟨zs,hz⟩ := mergeAmounts_complete a.entries.toList b.entries.toList hb
    unfold addChecked
    split
    · rename_i hn; rw [hz] at hn; contradiction
    · rename_i ws hw
      congr 1
      apply ext
      intro k
      exact (mergeAmounts_sum hw k).trans (hs k).symm


/-! ## 2. `AssetBundle` is the executable refinement of `Obend.Ledger.Proposal`'s asset lists -/

open Obend.Ledger
open Obend.Digest.HashBytes (be ofBE Hash Collision be_injective ofBE_lt)

/-- The ledger reading of a bundle: a `give` or `want` list of `Obend.Ledger.Proposal`. -/
def AssetBundle.toPairs (a : AssetBundle) : List (AssetId × Nat) :=
  a.entries.toList.map (fun p => (p.1, p.2.toNat))

theorem assetAmountSum_cons (a : AssetId) (n : Nat) (xs : List (AssetId × Nat)) (k : AssetId) :
    assetAmountSum ((a, n) :: xs) k = (if a = k then n else 0) + assetAmountSum xs k := by
  unfold assetAmountSum
  by_cases h : a = k
  · subst h; simp
  · simp [h]

theorem assetAmountSum_pairs (xs : List Entry) (k : AssetId) :
    assetAmountSum (xs.map (fun p => (p.1, p.2.toNat))) k = amountList xs k := by
  induction xs with
  | nil => simp [assetAmountSum, amountList]
  | cons p xs ih =>
    obtain ⟨b, v⟩ := p
    simp only [List.map_cons, assetAmountSum_cons, ih, amountList]

/-- **Refinement.** The bundle's binary search returns what the ledger's `assetAmountSum` adds up
over the proposal list the bundle stands for. -/
theorem AssetBundle.toPairs_amount (a : AssetBundle) (k : AssetId) :
    assetAmountSum a.toPairs k = a.amountOf k := by
  rw [amountOf_eq_spec]
  exact assetAmountSum_pairs a.entries.toList k

/-- A canonical bundle names each asset once, which is what `Proposal.assetsNodupB` asks. -/
theorem AssetBundle.toPairs_nodup (a : AssetBundle) : (a.toPairs.map Prod.fst).Nodup := by
  unfold AssetBundle.toPairs List.Nodup
  rw [List.map_map, List.pairwise_map]
  exact a.canonical.1.imp (fun h => Nat.ne_of_lt h)

/-- The executable bundle order is the ledger's per-asset order on the lists. -/
theorem AssetBundle.bundleLeq_iff_ledger (a b : AssetBundle) :
    a.bundleLeq b = true ↔ ∀ k, assetAmountSum a.toPairs k ≤ assetAmountSum b.toPairs k := by
  simp only [bundleLeq_iff_forall_brand, toPairs_amount, amountOf_eq_spec]

/-- The checked linear merge adds the ledger amounts asset by asset. -/
theorem AssetBundle.addChecked_ledger {a b c : AssetBundle} (h : a.addChecked b = some c)
    (k : AssetId) :
    assetAmountSum c.toPairs k = assetAmountSum a.toPairs k + assetAmountSum b.toPairs k := by
  simp only [toPairs_amount, amountOf_eq_spec]
  exact addChecked_sum h k

/-- The ledger proposal whose `give` and `want` are the two bundles. -/
def bundleProposal (give want : AssetBundle) (exit : ExitRule) (donate : Bool := false) :
    Proposal :=
  { give := give.toPairs, want := want.toPairs, exit := exit, donate := donate }

theorem bundleProposal_assetsNodup (g w : AssetBundle) (e : ExitRule) (d : Bool) :
    (bundleProposal g w e d).assetsNodupB = true := by
  unfold Proposal.assetsNodupB bundleProposal
  exact decide_eq_true ⟨g.toPairs_nodup, w.toPairs_nodup⟩

/-- A canonical bundle holds no zero entry, so the ledger's zero-want test (the one its donation
guard reads) is emptiness of the `want` bundle. -/
theorem bundleProposal_wantsNothing_iff (g w : AssetBundle) (e : ExitRule) (d : Bool) :
    (bundleProposal g w e d).wantsNothing = true ↔ w.entries.toList = [] := by
  unfold Proposal.wantsNothing bundleProposal AssetBundle.toPairs
  constructor
  · intro h
    cases hl : w.entries.toList with
    | nil => rfl
    | cons p ps =>
      have hp := w.canonical.2 p (by rw [hl]; exact List.mem_cons_self)
      rw [hl] at h
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      exact absurd h.1 (Nat.ne_of_gt hp)
  · intro h
    simp [h]

/-! ## 3. Two books, one set of legs: `FloorBook.admitBatch` gates, the seat `Book` mirrors -/

/-- The typed `FloorBook` address of a `Book` coordinate: ordinary accounts are users, the
protected band is seats, and the band above it is the issuer wells (`issuerWellAccount`). -/
def addrOf (a : AccountId) : AccountAddr :=
  if a < protectedBase then .user a
  else if a < 2 * protectedBase then .seat (a - protectedBase)
  else .issuerWell (a - 2 * protectedBase)

theorem addrOf_injective {a b : Nat} (h : addrOf a = addrOf b) : a = b := by
  unfold addrOf at h
  by_cases ha1 : a < protectedBase <;> by_cases ha2 : a < 2 * protectedBase <;>
    by_cases hb1 : b < protectedBase <;> by_cases hb2 : b < 2 * protectedBase <;>
    simp [ha1, ha2, hb1, hb2, AccountAddr.user, AccountAddr.seat, AccountAddr.issuerWell] at h <;>
    omega

theorem addrOf_inj {a b : AccountId} : addrOf a = addrOf b ↔ a = b :=
  ⟨addrOf_injective, fun h => by rw [h]⟩

theorem addrOf_seat_kind {a : AccountId} (hlo : protectedBase ≤ a) (hhi : a < 2 * protectedBase) :
    (addrOf a).kind ≠ .issuerWell := by
  unfold addrOf
  rw [ite_eq_right (Nat.not_lt.mpr hlo), ite_eq_left hhi]
  intro h; cases h

theorem addrOf_user_kind {a : AccountId} (h : a < protectedBase) :
    (addrOf a).kind ≠ .issuerWell := by
  unfold addrOf
  rw [ite_eq_left h]
  intro h; cases h

/-- The same leg on the typed book. -/
def typedPosting (p : ResourcePosting) : TypedPosting :=
  ⟨addrOf p.source, addrOf p.destination, p.asset, p.amount⟩

/-- The seat `Book` and the `FloorBook` hold the same balance at every coordinate. -/
def BooksAgree (fb : FloorBook) (b : Book) : Prop :=
  ∀ (a : AccountId) (ast : AssetId), b.balance a ast = fb.balance (addrOf a) ast

/-- Post one list of legs to both books. The `FloorBook` decides: a leg that would take its
source below its floor refuses the whole batch, and then neither book moves. -/
def postBoth (fb : FloorBook) (b : Book) (ps : List ResourcePosting) : Option (FloorBook × Book) :=
  (fb.admitBatch (ps.map typedPosting)).map (fun fb' => (fb', applyPostings b ps))

theorem admitPosting_eq {fb fb' : FloorBook} {p : TypedPosting}
    (h : fb.admitPosting p = some fb') : fb' = fb.applyRaw p := by
  unfold FloorBook.admitPosting at h
  split at h
  · injection h with h; exact h.symm
  · cases h

theorem agree_applyPosting {fb : FloorBook} {b : Book} (hag : BooksAgree fb b)
    (p : ResourcePosting) : BooksAgree (fb.applyRaw (typedPosting p)) (b.applyPosting p) := by
  intro a ast
  rw [Book.balance_applyPosting, FloorBook.balance_applyRaw, hag a ast]
  simp only [typedPosting, addrOf_inj]
  by_cases hast : ast = p.asset <;> by_cases hs : a = p.source <;>
    by_cases hd : a = p.destination <;> simp [hast, hs, hd]

theorem admitBatch_agree : ∀ (ps : List ResourcePosting) {fb fb' : FloorBook} {b : Book},
    BooksAgree fb b → fb.admitBatch (ps.map typedPosting) = some fb' →
    BooksAgree fb' (applyPostings b ps)
  | [], fb, fb', b, hag, h => by
    simp only [List.map_nil, FloorBook.admitBatch, Option.some.injEq] at h
    subst h; exact hag
  | p :: ps, fb, fb', b, hag, h => by
    rw [List.map_cons] at h
    unfold FloorBook.admitBatch at h
    split at h
    · rename_i fb1 hstep
      rw [applyPostings_cons]
      refine admitBatch_agree ps ?_ h
      rw [admitPosting_eq hstep]
      exact agree_applyPosting hag p
    · cases h

theorem applyPostings_globalAssetSum (ps : List ResourcePosting) (b : Book) (ast : AssetId) :
    (applyPostings b ps).globalAssetSum ast = b.globalAssetSum ast := by
  induction ps generalizing b with
  | nil => rfl
  | cons p rest ih => rw [applyPostings_cons, ih, Book.applyPosting_conserves_global]

/-- **Posting to both books is sound.** The floors still hold, the books still agree, and every
asset's total is what it was, in the `FloorBook` (`assetSum`) and in the seat `Book`. -/
theorem postBoth_sound {fb fb' : FloorBook} {b b' : Book} {ps : List ResourcePosting}
    (hfl : FloorsHold fb) (hag : BooksAgree fb b) (h : postBoth fb b ps = some (fb', b')) :
    FloorsHold fb' ∧ BooksAgree fb' b' ∧ (∀ ast, fb'.assetSum ast = fb.assetSum ast) ∧
      (∀ ast, b'.globalAssetSum ast = b.globalAssetSum ast) ∧ b' = applyPostings b ps := by
  unfold postBoth at h
  obtain ⟨fb1, hadm, heq⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  obtain ⟨hfl', hsum⟩ := FloorBook.admitBatch_preserves_floors _ hfl hadm
  exact ⟨hfl', admitBatch_agree ps hag hadm, hsum, applyPostings_globalAssetSum ps b, rfl⟩

theorem giveEscrow_endpoints {offerer seatAcc : AccountId} {p : Proposal} {q : ResourcePosting}
    (hq : q ∈ giveEscrowPostings offerer seatAcc p) :
    q.source = offerer ∧ q.destination = seatAcc := by
  unfold giveEscrowPostings at hq
  obtain ⟨⟨x, amt⟩, _, rfl⟩ := List.mem_map.mp hq
  exact ⟨rfl, rfl⟩

theorem payout_endpoints {b : Book} {account payee : AccountId} {assets : List AssetId}
    {q : ResourcePosting} (hq : q ∈ payoutPostings b account payee assets) :
    q.source = account ∧ q.destination = payee := by
  unfold payoutPostings at hq
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hq
  exact ⟨rfl, rfl⟩

/-- What escrowing a proposal's `give` does to the seat `Book`: the offeror loses, and the seat
gains, the ledger's per-asset sum of the list. -/
theorem escrow_balance (src dst : AccountId) (hne : src ≠ dst) (p : Proposal) (b : Book)
    (a : AccountId) (ast : AssetId) :
    (applyPostings b (giveEscrowPostings src dst p)).balance a ast =
      b.balance a ast - (if a = src then (assetAmountSum p.give ast : Int) else 0)
        + (if a = dst then (assetAmountSum p.give ast : Int) else 0) := by
  unfold giveEscrowPostings
  generalize p.give = give
  induction give generalizing b with
  | nil => simp [assetAmountSum]
  | cons q rest ih =>
    obtain ⟨x, amt⟩ := q
    simp only [List.map_cons, applyPostings_cons]
    rw [ih, Book.balance_applyPosting, assetAmountSum_cons]
    by_cases h3 : x = ast
    · subst h3
      by_cases h1 : a = src
      · simp [h1, hne] <;> omega
      · by_cases h2 : a = dst
        · simp [h2, Ne.symm hne] <;> omega
        · simp [h1, h2]
    · have h3' : ¬ ast = x := fun h => h3 h.symm
      simp [h3, h3']

/-! ## 4. Holder capabilities: a 256-bit commitment in the host, opened by its preimage -/

/-- The domain tag of holder commitments: `obend.polis.zoe.holder.v1`. -/
def zoeHolderDomain : List UInt8 :=
  [0x6f, 0x62, 0x65, 0x6e, 0x64, 0x2e, 0x70, 0x6f, 0x6c, 0x69, 0x73, 0x2e, 0x7a, 0x6f, 0x65, 0x2e,
    0x68, 0x6f, 0x6c, 0x64, 0x65, 0x72, 0x2e, 0x76, 0x31]

/-- The deployed hash: cSHAKE256 customized by the holder domain. -/
def zoeHash : Hash := Obend.Digest.Cshake256.cshake256Bytes zoeHolderDomain

theorem zoeHash_length (x : List UInt8) : (zoeHash x).length = 32 :=
  Obend.Digest.Cshake256.cshake256Bytes_length _ _

/-- The bytes a holder commits to: the domain tag, the seat id in an eight-byte frame, the
capability's length in an eight-byte frame, the capability. -/
def holderPreimage (seatId : Nat) (cap : List UInt8) : List UInt8 :=
  zoeHolderDomain ++ (be 8 seatId ++ (be 8 cap.length ++ cap))

theorem holderPreimage_injective {s₁ s₂ : Nat} {c₁ c₂ : List UInt8}
    (h₁ : s₁ < 256 ^ 8) (h₂ : s₂ < 256 ^ 8)
    (h : holderPreimage s₁ c₁ = holderPreimage s₂ c₂) : s₁ = s₂ ∧ c₁ = c₂ := by
  unfold holderPreimage at h
  obtain ⟨hs, hrest⟩ := List.append_inj (List.append_cancel_left h) (by simp)
  obtain ⟨_, hc⟩ := List.append_inj hrest (by simp)
  exact ⟨be_injective h₁ h₂ hs, hc⟩

/-- The commitment the host stores for a seat: 256 bits of `H` over the framed preimage. -/
def holderCommit (H : Hash) (seatId : Nat) (cap : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (H (holderPreimage seatId cap)))

/-- **A commitment binds its seat and capability.** Two openings of one commitment are the same
seat and the same capability, or their framed bytes are a collision of `H`. -/
theorem holderCommit_binding {H : Hash} (hlen : ∀ x, (H x).length = 32) {s₁ s₂ : Nat}
    {c₁ c₂ : List UInt8} (h₁ : s₁ < 256 ^ 8) (h₂ : s₂ < 256 ^ 8)
    (h : holderCommit H s₁ c₁ = holderCommit H s₂ c₂) : (s₁ = s₂ ∧ c₁ = c₂) ∨ Collision H :=
  if hp : holderPreimage s₁ c₁ = holderPreimage s₂ c₂ then
    .inl (holderPreimage_injective h₁ h₂ hp)
  else .inr ⟨_, _, hp, by
    have hb : ∀ x, ofBE (H x) < 2 ^ 256 := fun x => by
      have hlt := ofBE_lt (H x)
      rwa [hlen x, (by decide : (256 : Nat) ^ 32 = 2 ^ 256)] at hlt
    have hn := congrArg BitVec.toNat h
    simp only [holderCommit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb _)] at hn
    exact hn⟩

/-! ## 5. The host over the ledger spine, and its turns -/

/-- The settlement host. `floorBook`, `seatBook`, `invReg` and `seats` are the ledger components
of `Obend.Vault.UnifiedDeosSpine`, by name and type; `seats` holds the live seats. `holders` maps
a live seat's account to the commitment of its holder capability. -/
structure ZoeHost where
  floorBook : FloorBook := {}
  seatBook  : Book := {}
  invReg    : InvitationRegistry := {}
  seats     : List Seat := []
  holders   : List (AccountId × BitVec 256) := []
  epoch     : Nat := 0
  deriving DecidableEq

def initHost : ZoeHost := {}

/-- Why a turn is refused. -/
inductive ZoeRefusal where
  /-- `Ledger.admitOffer` refused: the donation guard, the invitation, or the offeror's balance -/
  | offer (e : OfferError)
  /-- the offeror or the payee is not an ordinary account -/
  | notOrdinary
  /-- the seat coordinate is out of range or held by a live seat -/
  | seatOccupied
  /-- `FloorBook.admitBatch` refused the escrow: the `give` is not in the offeror's account -/
  | unescrowed
  /-- the funded seat fails `Ledger.safeAt` -/
  | offerUnsafe
  | noSuchSeat
  /-- the presented capability does not open the seat's commitment -/
  | wrongHolder
  | exitNotAllowed
  | payoutRefused
  | guestDeclined
  /-- `Ledger.checkBatchReallocSafe` refused, or a leg leaves the invoked seats -/
  | reallocUnsafe
  | reallocFloorRefused
  deriving DecidableEq, Repr

/-- A guest contract sees identity-blind `SeatView`s and proposes legs between seats. -/
abbrev GuestContract := List SeatView → Option BatchRealloc

inductive ZoeTurn where
  | mintInvitation (instanceId : Nat) (description : String)
  | enterOffer (invId : Nat) (offerer payee : AccountId) (seatId : SeatId) (proposal : Proposal)
      (holderCommit : BitVec 256)
  | invokeGuestContract (seatAccounts : List AccountId)
  | exitSeat (seatId : SeatId) (capPreimage : List UInt8)
  | advanceEpoch

/-- **Entering an offer.** `Ledger.admitOffer` runs on the seat `Book` (donation guard, one-time
invitation, balance), and the same escrow legs must pass `FloorBook.admitBatch` out of the
offeror's typed account. Nothing reaches a seat that was not debited from an account. -/
def enterOffer (h : ZoeHost) (invId : Nat) (offerer payee : AccountId) (seatId : SeatId)
    (p : Proposal) (commit : BitVec 256) : Except ZoeRefusal ZoeHost :=
  if hord : offerer < protectedBase ∧ payee < protectedBase then
    if seatId < 256 ^ 8 ∧ h.seats.all (fun s => s.account != protectedBase + seatId) = true then
      match admitOffer h.invReg h.seatBook invId offerer payee (protectedBase + seatId)
          (Nat.le_add_right _ _)
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le hord.2 (Nat.le_add_right _ _))) p with
      | .error e => .error (.offer e)
      | .ok (reg', b', s) =>
        match h.floorBook.admitBatch
            ((giveEscrowPostings offerer (protectedBase + seatId) p).map typedPosting) with
        | none => .error .unescrowed
        | some fb' =>
          if safeAt b' s.account s.proposal = true then
            .ok { h with
              floorBook := fb', seatBook := b', invReg := reg', seats := s :: h.seats,
              holders := (s.account, commit) :: h.holders }
          else .error .offerUnsafe
    else .error .seatOccupied
  else .error .notOrdinary

def guestInput (h : ZoeHost) (accts : List AccountId) : List SeatView :=
  (h.seats.filter (fun s => accts.contains s.account)).map Seat.view

/-- **Reallocation.** The guest's legs stay among the invoked seats, pass
`Ledger.checkBatchReallocSafe` over every live seat, and pass `FloorBook.admitBatch`. -/
def reallocStep (guest : GuestContract) (h : ZoeHost) (accts : List AccountId) :
    Except ZoeRefusal ZoeHost :=
  match guest (guestInput h accts) with
  | none => .error .guestDeclined
  | some r =>
    if (r.postings.all (fun p => accts.contains p.source && accts.contains p.destination) &&
        checkBatchReallocSafe h.seatBook h.seats r) = true then
      match postBoth h.floorBook h.seatBook r.postings with
      | none => .error .reallocFloorRefused
      | some (fb', b') => .ok { h with floorBook := fb', seatBook := b' }
    else .error .reallocUnsafe

def exitAllowed : ExitRule → Nat → Bool
  | .onDemand, _ => true
  | .afterDeadline due, epoch => decide (due ≤ epoch)

/-- **Exit.** The presented capability must open the seat's stored commitment and the exit rule
must allow it; then `Ledger.exitSeat`'s sweep pays the whole seat to the payee in both books. -/
def exitSeatStep (H : Hash) (h : ZoeHost) (seatId : SeatId) (cap : List UInt8) :
    Except ZoeRefusal ZoeHost :=
  match h.seats.find? (fun s => s.account == protectedBase + seatId) with
  | none => .error .noSuchSeat
  | some s =>
    if h.holders.lookup s.account = some (holderCommit H seatId cap) then
      if exitAllowed s.proposal.exit h.epoch = true then
        match postBoth h.floorBook h.seatBook
            (payoutPostings h.seatBook s.account s.payee (h.seatBook.heldAssets s.account)) with
        | none => .error .payoutRefused
        | some (fb', b') =>
          .ok { h with
            floorBook := fb', seatBook := b',
            seats := h.seats.filter (fun t => t.account != s.account),
            holders := h.holders.filter (fun e => e.1 != s.account) }
      else .error .exitNotAllowed
    else .error .wrongHolder

def stepZoeHost (H : Hash) (guest : GuestContract) (h : ZoeHost) :
    ZoeTurn → Except ZoeRefusal ZoeHost
  | .mintInvitation inst desc => .ok { h with invReg := (h.invReg.mint inst desc).1 }
  | .enterOffer invId offerer payee seatId p commit =>
    enterOffer h invId offerer payee seatId p commit
  | .invokeGuestContract accts => reallocStep guest h accts
  | .exitSeat seatId cap => exitSeatStep H h seatId cap
  | .advanceEpoch => .ok { h with epoch := h.epoch + 1 }

/-- The atomic application boundary retains the entire old state on failure. -/
def applyZoeTurn (H : Hash) (guest : GuestContract) (h : ZoeHost) (t : ZoeTurn) : ZoeHost :=
  match stepZoeHost H guest h t with
  | .ok f => f
  | .error _ => h

def runZoe (H : Hash) (guest : GuestContract) : ZoeHost → List ZoeTurn → ZoeHost
  | h, [] => h
  | h, t :: ts => runZoe H guest (applyZoeTurn H guest h t) ts

/-- A trace: any list of turns, each applied atomically. -/
def ValidZoeTrace (H : Hash) (guest : GuestContract) : ZoeHost → List ZoeTurn → ZoeHost → Prop
  | h, [], f => f = h
  | h, t :: ts, f => ValidZoeTrace H guest (applyZoeTurn H guest h t) ts f

theorem validZoeTrace_iff_run (H : Hash) (guest : GuestContract) (ts : List ZoeTurn) :
    ∀ (h f : ZoeHost), ValidZoeTrace H guest h ts f ↔ f = runZoe H guest h ts := by
  induction ts with
  | nil => intro h f; exact Iff.rfl
  | cons t ts ih => intro h f; exact ih _ f

/-! ## 6. What an accepted turn did -/

theorem admitOffer_ok {reg reg' : InvitationRegistry} {b b' : Book} {invId : Nat}
    {offerer payee seatAcc : AccountId} {h_prot : protectedBase ≤ seatAcc}
    {h_diff : payee ≠ seatAcc} {p : Proposal} {s : Seat}
    (hadm : admitOffer reg b invId offerer payee seatAcc h_prot h_diff p = .ok (reg', b', s)) :
    checkDonationGuard p = .ok () ∧ offerer ≠ seatAcc ∧
      b' = applyPostings b (giveEscrowPostings offerer seatAcc p) ∧
      s.account = seatAcc ∧ s.payee = payee ∧ s.proposal = p := by
  unfold admitOffer at hadm
  cases hguard : checkDonationGuard p with
  | error e => rw [hguard] at hadm; cases hadm
  | ok u =>
    rw [hguard] at hadm
    dsimp only [Bind.bind, Except.bind] at hadm
    cases hsp : reg.spend invId with
    | none => rw [hsp] at hadm; cases hadm
    | some pair =>
      rcases pair with ⟨r1, inv⟩
      rw [hsp] at hadm
      by_cases hoff : offerer == seatAcc
      · simp [hoff] at hadm
      · simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hadm
        split at hadm
        · cases hadm
        · injection hadm with hp
          have h1 := (Prod.mk.inj hp).2
          have hb := (Prod.mk.inj h1).1
          have hs := (Prod.mk.inj h1).2
          subst hb; subst hs
          exact ⟨rfl, fun he => hoff (by rw [he]; exact beq_self_eq_true _), rfl, rfl, rfl, rfl⟩

/-- Why `Ledger.admitOffer` refuses an ordinary offeror: the donation guard, a spent or unknown
invitation, or a `give` asset the offeror's balance does not cover. -/
theorem admitOffer_error {reg : InvitationRegistry} {b : Book} {invId : Nat}
    {offerer payee seatAcc : AccountId} {h_prot : protectedBase ≤ seatAcc}
    {h_diff : payee ≠ seatAcc} {p : Proposal} {e : OfferError}
    (hadm : admitOffer reg b invId offerer payee seatAcc h_prot h_diff p = .error e)
    (hne : offerer ≠ seatAcc) :
    checkDonationGuard p ≠ .ok () ∨ reg.spend invId = none ∨
      ∃ ast, b.balance offerer ast < (assetAmountSum p.give ast : Int) := by
  unfold admitOffer at hadm
  cases hguard : checkDonationGuard p with
  | error e0 => exact .inl (fun h => by cases h)
  | ok u =>
    rw [hguard] at hadm
    dsimp only [Bind.bind, Except.bind] at hadm
    cases hsp : reg.spend invId with
    | none => exact .inr (.inl rfl)
    | some pair =>
      rcases pair with ⟨r1, inv⟩
      rw [hsp] at hadm
      have hoff : (offerer == seatAcc) = false := beq_eq_false_iff_ne.mpr hne
      simp only [hoff, Bool.false_eq_true, ↓reduceIte] at hadm
      split at hadm
      · rename_i badAst hfind
        exact .inr (.inr ⟨badAst, by simpa using List.find?_some hfind⟩)
      · cases hadm

/-- **An accepted offer, taken apart.** -/
theorem enterOffer_ok {h f : ZoeHost} {invId : Nat} {offerer payee : AccountId} {seatId : SeatId}
    {p : Proposal} {commit : BitVec 256}
    (he : enterOffer h invId offerer payee seatId p commit = .ok f) :
    ∃ s : Seat, s.account = protectedBase + seatId ∧ s.payee = payee ∧ s.proposal = p ∧
      offerer < protectedBase ∧ payee < protectedBase ∧ seatId < 256 ^ 8 ∧
      (∀ t ∈ h.seats, t.account ≠ protectedBase + seatId) ∧
      checkDonationGuard p = .ok () ∧
      f.seats = s :: h.seats ∧ f.holders = (s.account, commit) :: h.holders ∧
      f.epoch = h.epoch ∧ f.invReg.spend invId = none ∧
      postBoth h.floorBook h.seatBook (giveEscrowPostings offerer (protectedBase + seatId) p) =
        some (f.floorBook, f.seatBook) ∧
      safeAt f.seatBook s.account s.proposal = true := by
  unfold enterOffer at he
  split at he
  · rename_i hord
    split at he
    · rename_i hfresh
      split at he
      · cases he
      · rename_i reg' b' s hadm
        split at he
        · cases he
        · rename_i fb' hfb
          split at he
          · rename_i hsafe
            injection he with he
            subst he
            obtain ⟨hg, _, hb, hacc, hpay, hprop⟩ := admitOffer_ok hadm
            refine ⟨s, hacc, hpay, hprop, hord.1, hord.2, hfresh.1, ?_, hg, rfl, rfl, rfl,
              admitOffer_spends_invitation_once hadm, ?_, hsafe⟩
            · intro t ht
              have := List.all_eq_true.mp hfresh.2 t ht
              simpa using this
            · rw [postBoth, hfb, hb]; rfl
          · cases he
    · cases he
  · cases he

theorem reallocStep_ok {guest : GuestContract} {h f : ZoeHost} {accts : List AccountId}
    (he : reallocStep guest h accts = .ok f) :
    ∃ r : BatchRealloc, guest (guestInput h accts) = some r ∧
      checkBatchReallocSafe h.seatBook h.seats r = true ∧
      (∀ q ∈ r.postings, q.source ∈ accts ∧ q.destination ∈ accts) ∧
      postBoth h.floorBook h.seatBook r.postings = some (f.floorBook, f.seatBook) ∧
      f.seats = h.seats ∧ f.holders = h.holders ∧ f.invReg = h.invReg ∧ f.epoch = h.epoch := by
  unfold reallocStep at he
  split at he
  · cases he
  · rename_i r hg
    split at he
    · rename_i hchk
      split at he
      · cases he
      · rename_i fb' b' hpost
        injection he with he
        subst he
        rw [Bool.and_eq_true] at hchk
        refine ⟨r, hg, hchk.2, ?_, hpost, rfl, rfl, rfl, rfl⟩
        intro q hq
        have := List.all_eq_true.mp hchk.1 q hq
        simpa using this
    · cases he

theorem exitSeatStep_ok {H : Hash} {h f : ZoeHost} {seatId : SeatId} {cap : List UInt8}
    (he : exitSeatStep H h seatId cap = .ok f) :
    ∃ s : Seat, h.seats.find? (fun s => s.account == protectedBase + seatId) = some s ∧
      h.holders.lookup s.account = some (holderCommit H seatId cap) ∧
      exitAllowed s.proposal.exit h.epoch = true ∧
      postBoth h.floorBook h.seatBook
        (payoutPostings h.seatBook s.account s.payee (h.seatBook.heldAssets s.account)) =
        some (f.floorBook, f.seatBook) ∧
      f.seats = h.seats.filter (fun t => t.account != s.account) ∧
      f.holders = h.holders.filter (fun e => e.1 != s.account) ∧
      f.invReg = h.invReg ∧ f.epoch = h.epoch := by
  unfold exitSeatStep at he
  split at he
  · cases he
  · rename_i s hfind
    split at he
    · rename_i hcap
      split at he
      · rename_i hallow
        split at he
        · cases he
        · rename_i fb' b' hpost
          injection he with he
          subst he
          exact ⟨s, hfind, hcap, hallow, hpost, rfl, rfl, rfl, rfl⟩
      · cases he
    · cases he

/-! ## 7. The invariant, and its preservation along every trace -/

/-- What every reachable host satisfies: the `FloorBook` floors, agreement of the two books,
distinct live seats in the protected band with ordinary payees, and `Ledger.safeAt` on each. -/
def ZoeInv (h : ZoeHost) : Prop :=
  FloorsHold h.floorBook ∧ BooksAgree h.floorBook h.seatBook ∧
  (h.seats.map Seat.account).Nodup ∧
  (∀ s ∈ h.seats, s.account < 2 * protectedBase ∧ s.payee < protectedBase) ∧
  (∀ s ∈ h.seats, safeAt h.seatBook s.account s.proposal = true)

theorem frameBound_lt_protectedBase : 256 ^ 8 < protectedBase := by decide

theorem initHost_invariant : ZoeInv initHost := by
  refine ⟨floorsHold_empty, fun _ _ => by rfl, List.nodup_nil, ?_, ?_⟩ <;>
    (intro s hs; cases hs)

/-- **Every accepted turn keeps the invariant and every asset's total**, in the `FloorBook`
(`assetSum`) and in the seat `Book` (`globalAssetSum`). -/
theorem step_preserves (H : Hash) (guest : GuestContract) {h f : ZoeHost} {t : ZoeTurn}
    (hi : ZoeInv h) (he : stepZoeHost H guest h t = .ok f) :
    ZoeInv f ∧ (∀ ast, f.floorBook.assetSum ast = h.floorBook.assetSum ast) ∧
      (∀ ast, f.seatBook.globalAssetSum ast = h.seatBook.globalAssetSum ast) := by
  obtain ⟨hfl, hag, hnd, hbd, hsafe⟩ := hi
  cases t with
  | mintInvitation inst desc =>
    cases he
    exact ⟨⟨hfl, hag, hnd, hbd, hsafe⟩, fun _ => rfl, fun _ => rfl⟩
  | advanceEpoch =>
    cases he
    exact ⟨⟨hfl, hag, hnd, hbd, hsafe⟩, fun _ => rfl, fun _ => rfl⟩
  | enterOffer invId offerer payee seatId p commit =>
    obtain ⟨s, hacc, hpay, hprop, ho, hp, hsid, hfresh, _, hseats, _, _, _, hpost, hsf⟩ :=
      enterOffer_ok (show enterOffer h invId offerer payee seatId p commit = .ok f from he)
    obtain ⟨hfl', hag', hc1, hc2, hb'⟩ := postBoth_sound hfl hag hpost
    refine ⟨⟨hfl', hag', ?_, ?_, ?_⟩, hc1, hc2⟩
    · rw [hseats, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hnd⟩
      obtain ⟨t, ht, hta⟩ := List.mem_map.mp hm
      exact hfresh t ht (hta.trans hacc)
    · intro t ht
      rw [hseats] at ht
      rcases List.mem_cons.mp ht with heq | ht
      · rw [heq, hacc, hpay, Nat.two_mul]
        exact ⟨Nat.add_lt_add_left (Nat.lt_trans hsid frameBound_lt_protectedBase) _, hp⟩
      · exact hbd t ht
    · intro t ht
      rw [hseats] at ht
      rcases List.mem_cons.mp ht with heq | ht
      · rw [heq]; exact hsf
      · refine safeAt_mono (fun ast => Int.le_of_eq ?_) (hsafe t ht)
        rw [hb']
        refine (applyPostings_balance_other_account _ _ _ _ fun q hq => ?_).symm
        obtain ⟨hqs, hqd⟩ := giveEscrow_endpoints hq
        rw [hqs, hqd]
        exact ⟨fun e => ordinary_ne_seat_account t ho e.symm, hfresh t ht⟩
  | invokeGuestContract accts =>
    obtain ⟨r, _, hchk, _, hpost, hseats, _, _, _⟩ :=
      reallocStep_ok (show reallocStep guest h accts = .ok f from he)
    obtain ⟨hfl', hag', hc1, hc2, hb'⟩ := postBoth_sound hfl hag hpost
    refine ⟨⟨hfl', hag', hseats ▸ hnd, hseats ▸ hbd, ?_⟩, hc1, hc2⟩
    intro t ht
    rw [hseats] at ht
    rw [hb']
    exact batchRealloc_preserves_all_seats_offer_safe h.seatBook h.seats r hchk t ht
  | exitSeat seatId cap =>
    obtain ⟨s, hfind, _, _, hpost, hseats, _, _, _⟩ :=
      exitSeatStep_ok (show exitSeatStep H h seatId cap = .ok f from he)
    have hs : s ∈ h.seats := List.mem_of_find?_eq_some hfind
    obtain ⟨hfl', hag', hc1, hc2, hb'⟩ := postBoth_sound hfl hag hpost
    refine ⟨⟨hfl', hag', ?_, ?_, ?_⟩, hc1, hc2⟩
    · rw [hseats]
      exact List.Nodup.sublist (List.filter_sublist.map _) hnd
    · intro t ht
      rw [hseats] at ht
      exact hbd t (List.mem_filter.mp ht).1
    · intro t ht
      rw [hseats] at ht
      obtain ⟨htm, hne⟩ := List.mem_filter.mp ht
      refine safeAt_mono (fun ast => Int.le_of_eq ?_) (hsafe t htm)
      rw [hb']
      refine (applyPostings_balance_other_account _ _ _ _ fun q hq => ?_).symm
      obtain ⟨hqs, hqd⟩ := payout_endpoints hq
      rw [hqs, hqd]
      exact ⟨by simpa using hne, (ordinary_ne_seat_account t (hbd s hs).2).symm⟩

theorem applyZoeTurn_preserves (H : Hash) (guest : GuestContract) (h : ZoeHost) (t : ZoeTurn)
    (hi : ZoeInv h) :
    ZoeInv (applyZoeTurn H guest h t) ∧
      (∀ ast, (applyZoeTurn H guest h t).floorBook.assetSum ast = h.floorBook.assetSum ast) ∧
      (∀ ast, (applyZoeTurn H guest h t).seatBook.globalAssetSum ast =
        h.seatBook.globalAssetSum ast) := by
  unfold applyZoeTurn
  cases he : stepZoeHost H guest h t with
  | error e => exact ⟨hi, fun _ => rfl, fun _ => rfl⟩
  | ok f => exact step_preserves H guest hi he

/-- **The trace invariant.** Along any trace, of any length, under any guest and any hash: the
invariant holds at the end, and every asset's total is what it was at the start, in the
`FloorBook` and in the seat `Book`. No turn mints and no turn burns. -/
theorem trace_invariant (H : Hash) (guest : GuestContract) (ts : List ZoeTurn) :
    ∀ (h f : ZoeHost), ZoeInv h → ValidZoeTrace H guest h ts f →
      ZoeInv f ∧ (∀ ast, f.floorBook.assetSum ast = h.floorBook.assetSum ast) ∧
        (∀ ast, f.seatBook.globalAssetSum ast = h.seatBook.globalAssetSum ast) := by
  induction ts with
  | nil =>
    intro h f hi ht
    have ht : f = h := ht
    subst ht
    exact ⟨hi, fun _ => rfl, fun _ => rfl⟩
  | cons t ts ih =>
    intro h f hi ht
    obtain ⟨hi1, hc1, hg1⟩ := applyZoeTurn_preserves H guest h t hi
    obtain ⟨hif, hc, hg⟩ := ih _ f hi1 ht
    exact ⟨hif, fun ast => (hc ast).trans (hc1 ast), fun ast => (hg ast).trans (hg1 ast)⟩

/-- The legs that fund ordinary accounts out of the issuer wells. -/
def grantPostings (grants : List (AccountId × AssetId × Nat)) : List ResourcePosting :=
  grants.map (fun g => ⟨issuerWellAccount g.2.1, g.1, g.2.1, g.2.2⟩)

/-- A genesis: both books funded by the same grants, no seat yet. -/
def fundedHost (grants : List (AccountId × AssetId × Nat)) : ZoeHost :=
  match postBoth FloorBook.empty Book.empty (grantPostings grants) with
  | some (fb, b) => { floorBook := fb, seatBook := b }
  | none => {}

theorem fundedHost_invariant (grants : List (AccountId × AssetId × Nat)) :
    ZoeInv (fundedHost grants) := by
  unfold fundedHost
  split
  · rename_i fb b hpost
    obtain ⟨hfl, hag, _, _, _⟩ :=
      postBoth_sound floorsHold_empty (fun _ _ => by rfl) hpost
    refine ⟨hfl, hag, List.nodup_nil, ?_, ?_⟩ <;> (intro s hs; cases hs)
  · exact initHost_invariant

/-- **Offer safety over the ledger, from any funded genesis.** No hypothesis constrains the
guest, the hash or the number of turns: the floors hold, every asset's `FloorBook` total is the
genesis total, every live seat passes `Ledger.safeAt`, and every live seat's escrow is a
non-negative `FloorBook` balance on every asset. -/
theorem zoe_offer_safety_unconditional (H : Hash) (guest : GuestContract)
    (grants : List (AccountId × AssetId × Nat)) (turns : List ZoeTurn) (f : ZoeHost)
    (ht : ValidZoeTrace H guest (fundedHost grants) turns f) :
    FloorsHold f.floorBook ∧
    (∀ ast, f.floorBook.assetSum ast = (fundedHost grants).floorBook.assetSum ast) ∧
    (∀ s ∈ f.seats, safeAt f.seatBook s.account s.proposal = true) ∧
    (∀ s ∈ f.seats, ∀ ast, 0 ≤ f.floorBook.balance (addrOf s.account) ast) := by
  obtain ⟨⟨hfl, _, _, hbd, hsafe⟩, hc, _⟩ :=
    trace_invariant H guest turns _ f (fundedHost_invariant grants) ht
  exact ⟨hfl, hc, hsafe, fun s hs ast =>
    nonIssuer_balance_nonneg_of_floorsHold hfl _ ast (addrOf_seat_kind s.h_protected (hbd s hs).1)⟩

/-! ## 8. What entering, reallocating and exiting do to the `FloorBook` -/

/-- **An accepted offer is escrowed out of the offeror's `FloorBook` account.** For every asset
the offeror's typed account is debited the proposal's `give`, the seat's is credited the same,
and the offeror held at least that much: no offer is funded from thin air. The donation guard
passed and the invitation is spent. -/
theorem enterOffer_escrows {h f : ZoeHost} {invId : Nat} {offerer payee : AccountId}
    {seatId : SeatId} {p : Proposal} {commit : BitVec 256} (hi : ZoeInv h)
    (he : enterOffer h invId offerer payee seatId p commit = .ok f) (ast : AssetId) :
    f.floorBook.balance (addrOf offerer) ast =
      h.floorBook.balance (addrOf offerer) ast - (assetAmountSum p.give ast : Int) ∧
    f.floorBook.balance (addrOf (protectedBase + seatId)) ast =
      h.floorBook.balance (addrOf (protectedBase + seatId)) ast + (assetAmountSum p.give ast : Int) ∧
    (assetAmountSum p.give ast : Int) ≤ h.floorBook.balance (addrOf offerer) ast ∧
    checkDonationGuard p = .ok () ∧ f.invReg.spend invId = none := by
  obtain ⟨hfl, hag, _, _, _⟩ := hi
  obtain ⟨s, _, _, _, ho, _, _, _, hg, _, _, _, hspent, hpost, _⟩ := enterOffer_ok he
  obtain ⟨hfl', hag', _, _, hb'⟩ := postBoth_sound hfl hag hpost
  have hne : offerer ≠ protectedBase + seatId :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le ho (Nat.le_add_right _ _))
  have h1 : f.floorBook.balance (addrOf offerer) ast =
      h.floorBook.balance (addrOf offerer) ast - (assetAmountSum p.give ast : Int) := by
    rw [← hag' offerer ast, hb', escrow_balance _ _ hne, hag offerer ast]
    simp [hne]
  have h2 : f.floorBook.balance (addrOf (protectedBase + seatId)) ast =
      h.floorBook.balance (addrOf (protectedBase + seatId)) ast +
        (assetAmountSum p.give ast : Int) := by
    rw [← hag' (protectedBase + seatId) ast, hb', escrow_balance _ _ hne,
      hag (protectedBase + seatId) ast]
    simp [Ne.symm hne]
  have h0 := nonIssuer_balance_nonneg_of_floorsHold hfl' (addrOf offerer) ast (addrOf_user_kind ho)
  exact ⟨h1, h2, by omega, hg, hspent⟩

/-- An unmarked donation (zero `want`, `donate = false`) is refused by name, whatever the books
hold: `Ledger.admitOffer_donationUnmarked_refused`, through the host. -/
theorem enterOffer_donationUnmarked_refused (h : ZoeHost) (invId : Nat)
    (offerer payee : AccountId) (seatId : SeatId) (p : Proposal) (commit : BitVec 256)
    (hord : offerer < protectedBase ∧ payee < protectedBase)
    (hfresh : seatId < 256 ^ 8 ∧
      h.seats.all (fun s => s.account != protectedBase + seatId) = true)
    (hwant0 : p.wantsNothing = true) (hdon : p.donate = false) :
    enterOffer h invId offerer payee seatId p commit = .error (.offer .donationUnmarked) := by
  unfold enterOffer
  rw [dite_eq_left hord, ite_eq_left hfresh,
    admitOffer_donationUnmarked_refused _ _ _ _ _ _ _ _ p hwant0 hdon]

/-- **Exit pays the whole seat to its payee in the `FloorBook`.** The seat's typed account is
left at zero on every asset, the payee's gains exactly what the seat held, and the seat is gone
from the live seats. -/
theorem exit_pays_payee {H : Hash} {h f : ZoeHost} {seatId : SeatId} {cap : List UInt8}
    (hi : ZoeInv h) (he : exitSeatStep H h seatId cap = .ok f) :
    ∃ s ∈ h.seats, s.account = protectedBase + seatId ∧
      (∀ ast, f.floorBook.balance (addrOf s.account) ast = 0) ∧
      (∀ ast, f.floorBook.balance (addrOf s.payee) ast =
        h.floorBook.balance (addrOf s.payee) ast + h.floorBook.balance (addrOf s.account) ast) ∧
      (∀ t ∈ f.seats, t.account ≠ s.account) := by
  obtain ⟨hfl, hag, _, hbd, _⟩ := hi
  obtain ⟨s, hfind, _, _, hpost, hseats, _, _, _⟩ := exitSeatStep_ok he
  have hs : s ∈ h.seats := List.mem_of_find?_eq_some hfind
  have hacc : s.account = protectedBase + seatId := by
    simpa using List.find?_some hfind
  obtain ⟨_, hag', _, _, hb'⟩ := postBoth_sound hfl hag hpost
  have hnn : ∀ ast, 0 ≤ h.seatBook.balance s.account ast := fun ast => by
    rw [hag s.account ast]
    exact nonIssuer_balance_nonneg_of_floorsHold hfl _ ast
      (addrOf_seat_kind s.h_protected (hbd s hs).1)
  obtain ⟨hzero, hpaid, _⟩ := exit_sweeps_all_assets h.seatBook s hnn
  have hb'' : f.seatBook = exitSeat h.seatBook s := hb'
  refine ⟨s, hs, hacc, fun ast => ?_, fun ast => ?_, fun t ht => ?_⟩
  · rw [← hag' s.account ast, hb'']; exact hzero ast
  · rw [← hag' s.payee ast, hb'', hpaid ast, hag s.payee ast, hag s.account ast]
  · rw [hseats] at ht
    simpa using (List.mem_filter.mp ht).2

/-- **Only the holder exits.** If a seat's stored commitment was made from `cap₀`, a capability
that exits the seat is `cap₀`, or the two framed openings are a collision of `H`. -/
theorem exit_requires_holder_preimage {H : Hash} (hlen : ∀ x, (H x).length = 32)
    {h f : ZoeHost} {seatId : SeatId} {cap cap₀ : List UInt8} (hsid : seatId < 256 ^ 8)
    (hstored : h.holders.lookup (protectedBase + seatId) = some (holderCommit H seatId cap₀))
    (he : exitSeatStep H h seatId cap = .ok f) : cap = cap₀ ∨ Collision H := by
  obtain ⟨s, hfind, hcap, _, _, _, _, _, _⟩ := exitSeatStep_ok he
  have hacc : s.account = protectedBase + seatId := by
    simpa using List.find?_some hfind
  rw [hacc, hstored] at hcap
  exact (holderCommit_binding hlen hsid hsid (Option.some.inj hcap).symm).imp_left (·.2)

/-- **A guest moves nothing outside the invoked seats.** Every ordinary account's balance is
unchanged in both books, and the legs' endpoints are among the invoked accounts. -/
theorem realloc_leaves_ordinary_untouched {guest : GuestContract} {h f : ZoeHost}
    {accts : List AccountId} (hi : ZoeInv h) (he : reallocStep guest h accts = .ok f)
    (u : AccountId) (hu : u < protectedBase) (ast : AssetId) :
    f.floorBook.balance (addrOf u) ast = h.floorBook.balance (addrOf u) ast ∧
      f.seatBook.balance u ast = h.seatBook.balance u ast := by
  obtain ⟨hfl, hag, _, _, _⟩ := hi
  obtain ⟨r, _, hchk, _, hpost, _, _, _, _⟩ := reallocStep_ok he
  obtain ⟨_, hag', _, _, hb'⟩ := postBoth_sound hfl hag hpost
  have hbal : f.seatBook.balance u ast = h.seatBook.balance u ast := by
    rw [hb']
    exact batchRealloc_disjoint_from_ordinary_accounts h.seatBook h.seats r hchk u hu ast
  exact ⟨by rw [← hag' u ast, hbal, hag u ast], hbal⟩

/-! ## 9. Refusal is complete -/

def ExitViolation (H : Hash) (h : ZoeHost) (seatId : SeatId) (cap : List UInt8) : Prop :=
  match h.seats.find? (fun s => s.account == protectedBase + seatId) with
  | none => True
  | some s =>
    h.holders.lookup s.account ≠ some (holderCommit H seatId cap) ∨
    exitAllowed s.proposal.exit h.epoch = false ∨
    h.floorBook.admitBatch ((payoutPostings h.seatBook s.account s.payee
      (h.seatBook.heldAssets s.account)).map typedPosting) = none

/-- An exit is refused exactly when there is no such live seat, the capability does not open its
commitment, its exit rule does not allow it yet, or the `FloorBook` refuses the payout. -/
theorem exitSeatStep_refused_iff (H : Hash) (h : ZoeHost) (seatId : SeatId) (cap : List UInt8) :
    (∃ e, exitSeatStep H h seatId cap = .error e) ↔ ExitViolation H h seatId cap := by
  unfold exitSeatStep ExitViolation
  cases hf : h.seats.find? (fun s => s.account == protectedBase + seatId) with
  | none => simp
  | some s =>
    by_cases hc : h.holders.lookup s.account = some (holderCommit H seatId cap)
    · cases ha : exitAllowed s.proposal.exit h.epoch with
      | false => simp [hc, ha]
      | true =>
        cases hb : h.floorBook.admitBatch ((payoutPostings h.seatBook s.account s.payee
            (h.seatBook.heldAssets s.account)).map typedPosting) with
        | none => simp [hc, ha, postBoth, hb]
        | some fb' => simp [hc, ha, postBoth, hb]
    · simp [hc]

/-- A seat whose exit rule names a deadline is not exited before it, whatever is presented. -/
theorem premature_exit_refused (H : Hash) (h : ZoeHost) (seatId : SeatId) (cap : List UInt8)
    (s : Seat) (due : Nat)
    (hf : h.seats.find? (fun s => s.account == protectedBase + seatId) = some s)
    (hw : s.proposal.exit = .afterDeadline due) (he : h.epoch < due) :
    ∃ e, exitSeatStep H h seatId cap = .error e := by
  refine (exitSeatStep_refused_iff H h seatId cap).mpr ?_
  simp only [ExitViolation, hf]
  exact .inr (.inl (by rw [hw]; exact decide_eq_false (Nat.not_le.mpr he)))

/-- The contract a refused turn broke. Minting an invitation and advancing the epoch break none. -/
def ZoeStepViolation (H : Hash) (guest : GuestContract) (h : ZoeHost) : ZoeTurn → Prop
  | .mintInvitation _ _ => False
  | .advanceEpoch => False
  | .exitSeat seatId cap => ExitViolation H h seatId cap
  | .invokeGuestContract accts =>
    match guest (guestInput h accts) with
    | none => True
    | some r =>
      (r.postings.all (fun p => accts.contains p.source && accts.contains p.destination) &&
        checkBatchReallocSafe h.seatBook h.seats r) = false ∨
      h.floorBook.admitBatch (r.postings.map typedPosting) = none
  | .enterOffer invId offerer payee seatId p _ =>
    ¬ (offerer < protectedBase ∧ payee < protectedBase) ∨
    ¬ (seatId < 256 ^ 8 ∧ h.seats.all (fun s => s.account != protectedBase + seatId) = true) ∨
    checkDonationGuard p ≠ .ok () ∨ h.invReg.spend invId = none ∨
    (∃ ast, h.seatBook.balance offerer ast < (assetAmountSum p.give ast : Int)) ∨
    h.floorBook.admitBatch
      ((giveEscrowPostings offerer (protectedBase + seatId) p).map typedPosting) = none ∨
    safeAt (applyPostings h.seatBook (giveEscrowPostings offerer (protectedBase + seatId) p))
      (protectedBase + seatId) p = false

/-- **A skipped turn broke its contract.** Every refusal is one of the named violations: the
step function declines nothing it could have run. -/
theorem zoeStep_skip_implies_violation (H : Hash) (guest : GuestContract) (h : ZoeHost)
    (t : ZoeTurn) :
    (∃ e, stepZoeHost H guest h t = .error e) → ZoeStepViolation H guest h t := by
  rintro ⟨e, he⟩
  cases t with
  | mintInvitation inst desc => cases he
  | advanceEpoch => cases he
  | exitSeat seatId cap => exact (exitSeatStep_refused_iff H h seatId cap).mp ⟨e, he⟩
  | invokeGuestContract accts =>
    have he : reallocStep guest h accts = .error e := he
    unfold reallocStep at he
    simp only [ZoeStepViolation]
    cases hg : guest (guestInput h accts) with
    | none => trivial
    | some r =>
      rw [hg] at he
      dsimp only at he ⊢
      cases hchk : (r.postings.all (fun p => accts.contains p.source &&
          accts.contains p.destination) && checkBatchReallocSafe h.seatBook h.seats r) with
      | false => exact .inl rfl
      | true =>
        cases hb : h.floorBook.admitBatch (r.postings.map typedPosting) with
        | none => exact .inr rfl
        | some fb' =>
          rw [ite_eq_left hchk] at he
          simp [postBoth, hb] at he
  | enterOffer invId offerer payee seatId p commit =>
    have he : enterOffer h invId offerer payee seatId p commit = .error e := he
    simp only [ZoeStepViolation]
    by_cases hord : offerer < protectedBase ∧ payee < protectedBase
    · by_cases hfresh : seatId < 256 ^ 8 ∧
          h.seats.all (fun s => s.account != protectedBase + seatId) = true
      · refine .inr (.inr ?_)
        have hne : offerer ≠ protectedBase + seatId :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le hord.1 (Nat.le_add_right _ _))
        unfold enterOffer at he
        rw [dite_eq_left hord, ite_eq_left hfresh] at he
        split at he
        · rename_i e' hadm
          rcases admitOffer_error hadm hne with h1 | h1 | h1
          · exact .inl h1
          · exact .inr (.inl h1)
          · exact .inr (.inr (.inl h1))
        · rename_i reg' b' s hadm
          obtain ⟨_, _, hb, hacc, _, hprop⟩ := admitOffer_ok hadm
          refine .inr (.inr (.inr ?_))
          split at he
          · rename_i hfb
            exact .inl hfb
          · split at he
            · cases he
            · rename_i hsf
              rw [hb, hacc, hprop] at hsf
              exact .inr (by simpa using hsf)
      · exact .inr (.inl hfresh)
    · exact .inl hord

/-- Two distinct live seats are reachable from a funded genesis: the harness is not a singleton. -/
theorem two_live_seats_inhabited :
    ∃ h, ValidZoeTrace zoeHash (fun _ => none) (fundedHost [(1, 0, 5), (2, 1, 5)])
        [.mintInvitation 0 "otc", .mintInvitation 0 "otc",
          .enterOffer 0 1 1 0 ⟨[(0, 5)], [(1, 5)], .onDemand, false, {}⟩ 11#256,
          .enterOffer 1 2 2 1 ⟨[(1, 5)], [(0, 5)], .onDemand, false, {}⟩ 12#256] h ∧
      h.seats.length = 2 ∧ ZoeInv h :=
  ⟨_, (validZoeTrace_iff_run _ _ _ _ _).mpr rfl, by decide +kernel,
    (trace_invariant _ _ _ _ _ (fundedHost_invariant _)
      ((validZoeTrace_iff_run _ _ _ _ _).mpr rfl)).1⟩

example : ∀ x, (zoeHash x).length = 32 := zoeHash_length
example : BooksAgree FloorBook.empty Book.empty := fun _ _ => by rfl


/-! ## 10. A reallocation as a conserved value of `Obend.Logic.SeparationFrame` -/

namespace DeltaNormalization
open Obend.Logic

/-- Explicit decidable integer equality keeps witness construction constructive. -/
def insert (k : Nat) (d : Int) : List (Nat × Int) → List (Nat × Int)
  | [] => if d = 0 then [] else [(k, d)]
  | (k', d') :: xs =>
    if k < k' then if d = 0 then (k', d') :: xs else (k, d) :: (k', d') :: xs
    else if k' < k then (k', d') :: insert k d xs
    else if d + d' = 0 then xs else (k', d + d') :: xs

theorem insert_keys {k : Nat} {d : Int} :
    ∀ {xs : List (Nat × Int)} {p : Nat × Int},
      p ∈ insert k d xs → p.1 = k ∨ ∃ d₀, (p.1, d₀) ∈ xs
  | [], p, hp => by
    simp only [insert] at hp; split at hp; · cases hp
    simp only [List.mem_singleton] at hp; subst hp; exact Or.inl rfl
  | (k', d') :: xs, p, hp => by
    simp only [insert] at hp
    split at hp
    · split at hp
      · exact Or.inr ⟨p.2, hp⟩
      · rcases List.mem_cons.1 hp with rfl | hm; exact Or.inl rfl; exact Or.inr ⟨p.2, hm⟩
    · split at hp
      · rcases List.mem_cons.1 hp with rfl | hm
        · exact Or.inr ⟨d', List.mem_cons_self⟩
        · exact (insert_keys hm).imp id fun ⟨d₀, h₀⟩ => ⟨d₀, List.mem_cons_of_mem _ h₀⟩
      · split at hp
        · exact Or.inr ⟨p.2, List.mem_cons_of_mem _ hp⟩
        · rcases List.mem_cons.1 hp with rfl | hm
          · exact Or.inr ⟨d', List.mem_cons_self⟩
          · exact Or.inr ⟨p.2, List.mem_cons_of_mem _ hm⟩

theorem insert_nonZeroSorted (k : Nat) (d : Int) :
    ∀ {xs : List (Nat × Int)}, NonZeroSorted xs → NonZeroSorted (insert k d xs)
  | [], _ => by
    simp only [insert]
    by_cases hd : d = 0
    · simp [hd, NonZeroSorted]
    · simp only [hd, ↓reduceIte, NonZeroSorted]
      refine ⟨.cons (fun _ h => by cases h) .nil, fun p hp => ?_⟩
      simp only [List.mem_singleton] at hp; subst hp
      exact fun hz => absurd (hz) hd
  | (k', d') :: xs, ⟨.cons hgt hs, hnz⟩ => by
    have htail : NonZeroSorted xs := ⟨hs, fun p hp => hnz p (List.mem_cons_of_mem _ hp)⟩
    simp only [insert]
    by_cases hlt : k < k'
    · simp only [hlt, ↓reduceIte]
      by_cases hd : d = 0
      · simp [hd]; exact ⟨.cons hgt hs, hnz⟩
      · simp only [hd, ↓reduceIte]
        refine ⟨.cons (fun p hp => ?_) (.cons hgt hs), fun p hp => ?_⟩
        · rcases List.mem_cons.1 hp with rfl | hm; exact hlt; exact Nat.lt_trans hlt (hgt p hm)
        · rcases List.mem_cons.1 hp with rfl | hm
          · exact fun hz => absurd (hz) hd
          · exact hnz p hm
    · by_cases hgt' : k' < k
      · simp only [hlt, hgt', ↓reduceIte]
        obtain ⟨hs_rec, hnz_rec⟩ := insert_nonZeroSorted k d htail
        refine ⟨.cons (fun p hp => ?_) hs_rec, fun p hp => ?_⟩
        · rcases insert_keys hp with hpk | ⟨d₀, h₀⟩
          · rw [hpk]; exact hgt'
          · exact hgt (p.1, d₀) h₀
        · rcases List.mem_cons.1 hp with rfl | hm
          · exact hnz (k', d') List.mem_cons_self
          · exact hnz_rec p hm
      · simp only [hlt, hgt', ↓reduceIte]
        by_cases hsum : d + d' = 0
        · simp [hsum]; exact htail
        · simp only [hsum, ↓reduceIte]
          refine ⟨.cons hgt hs, fun p hp => ?_⟩
          rcases List.mem_cons.1 hp with rfl | hm
          · exact fun hz => absurd (hz) hsum
          · exact htail.2 p hm

theorem deltaAt_insert (k : Nat) (d : Int) :
    ∀ {xs : List (Nat × Int)}, NonZeroSorted xs →
      ∀ q : Nat, deltaAt (insert k d xs) q = (if q == k then d else 0) + deltaAt xs q
  | [], _, q => by
    simp only [insert]
    by_cases hd : d = 0
    · rw [hd]; simp [deltaAt]
    · simp only [hd, ↓reduceIte, deltaAt]; by_cases hqk : q == k <;> simp [hqk]
  | (k', d') :: xs, ⟨.cons hgt hs, hnz⟩, q => by
    have htail : NonZeroSorted xs := ⟨hs, fun p hp => hnz p (List.mem_cons_of_mem _ hp)⟩
    simp only [insert]
    by_cases hlt : k < k'
    · simp only [hlt, ↓reduceIte]
      by_cases hd : d = 0
      · simp [hd]
      · simp only [hd, ↓reduceIte, deltaAt]
        by_cases hqk : q == k
        · have hqeq : q = k := eq_of_beq hqk
          have hqk' : (q == k') = false := beq_false_of_ne (by omega)
          have hz : deltaAt xs q = 0 := deltaAt_zero_of_forall_gt fun p hp => by
            have := hgt p hp; omega
          simp [hqk, hqk', hz]
        · simp [hqk]
    · by_cases hgt' : k' < k
      · simp only [hlt, hgt', ↓reduceIte, deltaAt]
        by_cases hqk' : q == k'
        · have hqk_f : (q == k) = false := beq_false_of_ne (by have := eq_of_beq hqk'; omega)
          simp [hqk', hqk_f]
        · simp [hqk', deltaAt_insert k d htail q]
      · have hkeq : k = k' := by omega
        subst hkeq; simp only [hlt, ↓reduceIte]
        by_cases hsum : d + d' = 0
        · simp only [hsum, ↓reduceIte]
          have hz : d + d' = 0 := hsum
          by_cases hqk : q == k
          · have hqeq : q = k := eq_of_beq hqk; subst hqeq
            simp [deltaAt, deltaAt_zero_of_forall_gt hgt]; omega
          · simp [deltaAt, hqk]
        · simp only [hsum, ↓reduceIte, deltaAt]
          by_cases hqk : q == k <;> simp [hqk]

theorem sumDeltas_insert (k : Nat) (d : Int) :
    ∀ (xs : List (Nat × Int)), sumDeltas (insert k d xs) = d + sumDeltas xs
  | [] => by
    simp only [insert]
    by_cases hd : d = 0
    · simp [hd, sumDeltas]
    · simp [hd, sumDeltas]
  | (k', d') :: xs => by
    simp only [insert]
    by_cases hlt : k < k'
    · by_cases hd : d = 0 <;> simp [hlt, hd, sumDeltas]
    · by_cases hgt' : k' < k
      · simp only [hlt, hgt', ↓reduceIte, sumDeltas, sumDeltas_insert k d xs]; omega
      · simp only [hlt, hgt', ↓reduceIte]
        by_cases hsum : d + d' = 0
        · have := hsum; simp only [hsum, ↓reduceIte, sumDeltas]; omega
        · simp only [hsum, ↓reduceIte, sumDeltas]; omega

end DeltaNormalization

open Obend.Logic in
/-- Normalize actual signed per-seat allocation changes, removing zero entries. -/
def normalizedDeltas (ds : List (Nat × Int)) : List (Nat × Int) :=
  ds.foldr (fun p acc => DeltaNormalization.insert p.1 p.2 acc) []

open Obend.Logic in
theorem normalizedDeltas_wf (ds : List (Nat × Int)) : NonZeroSorted (normalizedDeltas ds) := by
  induction ds with
  | nil => exact ⟨.nil, by simp [normalizedDeltas]⟩
  | cons p ds ih => exact DeltaNormalization.insert_nonZeroSorted p.1 p.2 ih

open Obend.Logic in
theorem normalizedDeltas_sum (ds : List (Nat × Int)) :
    sumDeltas (normalizedDeltas ds) = (ds.map Prod.snd).sum := by
  induction ds with
  | nil => rfl
  | cons p ds ih =>
    change sumDeltas (DeltaNormalization.insert p.1 p.2 (normalizedDeltas ds)) = _
    rw [DeltaNormalization.sumDeltas_insert, ih]
    rfl

open Obend.Logic in
theorem normalizedDeltas_at (ds : List (Nat × Int)) (q : Nat) :
    deltaAt (normalizedDeltas ds) q =
      (ds.map (fun p => if q == p.1 then p.2 else 0)).sum := by
  induction ds with
  | nil => rfl
  | cons p ds ih =>
    change deltaAt (DeltaNormalization.insert p.1 p.2 (normalizedDeltas ds)) q = _
    rw [DeltaNormalization.deltaAt_insert _ _ (normalizedDeltas_wf ds), ih]
    rfl

/-- The signed account deltas of the legs in asset `ast`: each leg debits its source and credits
its destination. -/
def postingDeltas (ps : List ResourcePosting) (ast : AssetId) : List (Nat × Int) :=
  (ps.filter (fun p => p.asset == ast)).flatMap
    (fun p => [(p.source, -(p.amount : Int)), (p.destination, (p.amount : Int))])

theorem postingDeltas_sum (ps : List ResourcePosting) (ast : AssetId) :
    ((postingDeltas ps ast).map Prod.snd).sum = 0 := by
  unfold postingDeltas
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p.asset = ast
    · simp only [List.filter_cons, h, beq_self_eq_true, ↓reduceIte, List.flatMap_cons,
        List.map_append, List.sum_append, ih, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
    · have hb : (p.asset == ast) = false := beq_eq_false_iff_ne.mpr h
      simp only [List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte, ih]

/-- A reallocation's legs in one asset, normalized: a `ConservedValue` (sorted accounts, no zero
entry, deltas summing to zero). -/
def reallocConservedValue (r : BatchRealloc) (ast : AssetId) : Obend.Logic.ConservedValue where
  entries := normalizedDeltas (postingDeltas r.postings ast)
  wf := normalizedDeltas_wf _
  conserved := by rw [normalizedDeltas_sum, postingDeltas_sum]

/-- Every account delta of the conserved value is the exact sum of the legs that touch it. -/
theorem conservation_bridges_separationFrame (r : BatchRealloc) (ast : AssetId) :
    ∀ q, Obend.Logic.deltaAt (reallocConservedValue r ast).entries q =
      ((postingDeltas r.postings ast).map (fun p => if q == p.1 then p.2 else 0)).sum :=
  normalizedDeltas_at _

end Obend.Polis.ZoeSeatSettlement
