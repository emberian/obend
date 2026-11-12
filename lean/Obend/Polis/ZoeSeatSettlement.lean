module
public import Obend.Logic.SeparationFrame
public import Obend.Polis.CapTP
import all Obend.Polis.CapTP

public section
namespace Obend.Polis.ZoeSeatSettlement

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

inductive ExitRule where
  | onDemand | waived | afterEpoch (deadline : Nat)
  deriving DecidableEq, Repr

structure Proposal where
  give : AssetBundle
  want : AssetBundle
  exitRule : ExitRule

inductive SeatStatus where
  | active | exited | settled
  deriving DecidableEq, Repr

structure ZoeSeat where
  seatId : SeatId
  holderCap : BitVec 256
  proposal : Proposal
  escrowed : AssetBundle
  status : SeatStatus := .active
  payout : AssetBundle := .empty

def ZoeSeat.currentAllocation (s : ZoeSeat) : AssetBundle :=
  if s.status = .active then s.escrowed else s.payout

def satisfiesWant (p : Proposal) (a : AssetBundle) : Prop :=
  ∀ b, p.want.amountSpec b ≤ a.amountSpec b

def satisfiesRefund (p : Proposal) (a : AssetBundle) : Prop :=
  ∀ b, p.give.amountSpec b ≤ a.amountSpec b

def OfferSafe (s : ZoeSeat) : Prop :=
  satisfiesWant s.proposal s.currentAllocation ∨ satisfiesRefund s.proposal s.currentAllocation

def offerSafeB (s : ZoeSeat) : Bool :=
  s.proposal.want.bundleLeq s.currentAllocation || s.proposal.give.bundleLeq s.currentAllocation

theorem offerSafeB_iff (s : ZoeSeat) : offerSafeB s = true ↔ OfferSafe s := by
  simp [offerSafeB, OfferSafe, satisfiesWant, satisfiesRefund, AssetBundle.bundleLeq_iff_forall_brand]

/-- A failed checked assembly is represented by `none`, never a wrapped bundle. -/
abbrev ProposedStaging := Option (List (SeatId × AssetBundle))
abbrev GuestContract := List (SeatId × AssetBundle) → ProposedStaging

structure ZoeHost where
  seats : List ZoeSeat := []
  deposits : List AssetBundle := []
  epoch : Nat := 0

def initHost : ZoeHost := {}

def bundleTotal (bs : List AssetBundle) (b : AssetBrand) : Nat :=
  (bs.map (fun a => a.amountSpec b)).sum

def allocations (ss : List ZoeSeat) : List AssetBundle := ss.map ZoeSeat.currentAllocation

def totalAssets (h : ZoeHost) (b : AssetBrand) : Nat := bundleTotal (allocations h.seats) b

def support (bs : List AssetBundle) : List AssetBrand :=
  bs.flatMap (fun a => a.entries.toList.map Prod.fst)

abbrev DeltaEntry := Nat × Int

def signedAt : List DeltaEntry → Nat → Int
  | [], _ => 0
  | p :: ps, b => (if p.1 = b then p.2 else 0) + signedAt ps b

theorem signedAt_append (xs ys : List DeltaEntry) (b : Nat) :
    signedAt (xs ++ ys) b = signedAt xs b + signedAt ys b := by
  induction xs with
  | nil => simp [signedAt]
  | cons p ps ih => simp only [List.cons_append, signedAt, ih]; omega

theorem signedAt_perm {xs ys : List DeltaEntry} (hp : xs.Perm ys) (b : Nat) :
    signedAt xs b = signedAt ys b := by
  induction hp with
  | nil => rfl
  | cons p _ ih => simp [signedAt, ih]
  | swap p q ps => simp only [signedAt]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem signedAt_zero {xs : List DeltaEntry} {b : Nat} (h : ∀ p ∈ xs, p.1 ≠ b) :
    signedAt xs b = 0 := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    simp only [signedAt, h p (by simp), ↓reduceIte, Int.zero_add]
    exact ih (fun p hp => h p (by simp [hp]))

/-- One linear scan of sorted signed entries; equal brands accumulate in exact `Int`. -/
def zeroGroups : List DeltaEntry → Bool
  | [] => true
  | [p] => decide (p.2 = 0)
  | p :: q :: ps =>
    if p.1 = q.1 then zeroGroups ((p.1,p.2 + q.2) :: ps)
    else decide (p.2 = 0) && zeroGroups (q :: ps)
termination_by ps => ps.length

theorem zeroGroups_iff : ∀ (ps : List DeltaEntry),
    ps.Pairwise (fun p q => p.1 ≤ q.1) →
    (zeroGroups ps = true ↔ ∀ b, signedAt ps b = 0)
  | [], _ => by simp [zeroGroups, signedAt]
  | [p], _ => by
    simp only [zeroGroups, decide_eq_true_eq]
    constructor
    · intro h b; simp [signedAt, h]
    · intro h; simpa [signedAt] using h p.1
  | p :: q :: ps, .cons hp (.cons hq hs) => by
    simp only [zeroGroups]
    by_cases hk : p.1 = q.1
    · rw [ite_eq_left hk]
      have hsort : ((p.1,p.2 + q.2) :: ps).Pairwise (fun p q => p.1 ≤ q.1) :=
        .cons (fun r hr => by simpa [hk] using hq r hr) hs
      rw [zeroGroups_iff _ hsort]
      have he : ∀ b, signedAt ((p.1,p.2 + q.2) :: ps) b = signedAt (p :: q :: ps) b := by
        intro b; simp only [signedAt, hk]; split <;> omega
      simp only [he]
    · rw [ite_eq_right hk, Bool.and_eq_true, decide_eq_true_eq, zeroGroups_iff _ (.cons hq hs)]
      have hlt : p.1 < q.1 := by have := hp q (by simp); omega
      have hz : signedAt (q :: ps) p.1 = 0 := signedAt_zero (by
        intro r hr; rcases List.mem_cons.mp hr with rfl | hr
        · omega
        · have := hq r hr; omega)
      constructor
      · rintro ⟨hd,ht⟩ b
        change (if p.1 = b then p.2 else 0) + signedAt (q :: ps) b = 0
        rw [hd, ht]; split <;> rfl
      · intro hall
        have hd : p.2 = 0 := by
          have he := hall p.1
          rw [signedAt, hz] at he
          simpa using he
        refine ⟨hd, fun b => ?_⟩
        have := hall b
        simpa only [signedAt, hd, ite_self, Int.zero_add] using this
termination_by ps _ => ps.length

def bundleEntries (bs : List AssetBundle) : List DeltaEntry :=
  bs.flatMap (fun a => a.entries.toList.map (fun p => (p.1,(p.2.toNat : Int))))

theorem signedAt_amountList (xs : List Entry) (b : AssetBrand) :
    signedAt (xs.map (fun p => (p.1,(p.2.toNat : Int)))) b = (amountList xs b : Int) := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, signedAt, amountList, Int.natCast_add, ih]
    split <;> rfl

theorem signedAt_bundleEntries (bs : List AssetBundle) (b : AssetBrand) :
    signedAt (bundleEntries bs) b = (bundleTotal bs b : Int) := by
  induction bs with
  | nil => rfl
  | cons a bs ih =>
    simp only [bundleEntries, List.flatMap_cons, signedAt_append] at *
    rw [signedAt_amountList, ih]
    simp [bundleTotal, AssetBundle.amountSpec]

def negateEntries (ps : List DeltaEntry) : List DeltaEntry := ps.map (fun p => (p.1,-p.2))

theorem signedAt_negate (ps : List DeltaEntry) (b : Nat) :
    signedAt (negateEntries ps) b = - signedAt ps b := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [negateEntries, List.map_cons, signedAt] at *
    rw [ih]; split <;> omega

def sortedDifference (xs ys : List AssetBundle) : List DeltaEntry :=
  (bundleEntries xs ++ negateEntries (bundleEntries ys)).mergeSort (fun p q => decide (p.1 ≤ q.1))

theorem sortedDifference_sorted (xs ys : List AssetBundle) :
    (sortedDifference xs ys).Pairwise (fun p q => p.1 ≤ q.1) := by
  have ht : ∀ p q r : DeltaEntry, decide (p.1 ≤ q.1) → decide (q.1 ≤ r.1) → decide (p.1 ≤ r.1) := by
    simp only [decide_eq_true_eq]; intros; omega
  have hall : ∀ p q : DeltaEntry, decide (p.1 ≤ q.1) || decide (q.1 ≤ p.1) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; intros; omega
  simpa only [sortedDifference, decide_eq_true_eq] using List.pairwise_mergeSort ht hall
    (bundleEntries xs ++ negateEntries (bundleEntries ys))

theorem sortedDifference_spec (xs ys : List AssetBundle) (b : Nat) :
    signedAt (sortedDifference xs ys) b = (bundleTotal xs b : Int) - (bundleTotal ys b : Int) := by
  rw [sortedDifference, signedAt_perm (List.mergeSort_perm _ _), signedAt_append,
    signedAt_negate, signedAt_bundleEntries, signedAt_bundleEntries]
  omega

def checkTotals (xs ys : List AssetBundle) : Bool := zeroGroups (sortedDifference xs ys)

theorem checkTotals_iff (xs ys : List AssetBundle) :
    checkTotals xs ys = true ↔ ∀ b, bundleTotal xs b = bundleTotal ys b := by
  rw [checkTotals, zeroGroups_iff _ (sortedDifference_sorted xs ys)]
  simp only [sortedDifference_spec, Int.sub_eq_zero, Int.natCast_inj]

def updateStaging (ps : List (SeatId × AssetBundle)) (s : ZoeSeat) : ZoeSeat :=
  match ps.lookup s.seatId with
  | none => s
  | some p => { s with escrowed := p }

def stagedSeats (h : ZoeHost) (ps : List (SeatId × AssetBundle)) : List ZoeSeat :=
  h.seats.map (updateStaging ps)

def checkAssetConservation (h : ZoeHost) (ps : List (SeatId × AssetBundle)) : Bool :=
  checkTotals (allocations (stagedSeats h ps)) (allocations h.seats)

def checkOfferSafety (h : ZoeHost) (ps : List (SeatId × AssetBundle)) : Bool :=
  (stagedSeats h ps).all offerSafeB

def activeId (h : ZoeHost) (id : SeatId) : Bool :=
  h.seats.any (fun s => s.seatId == id && s.status == .active)

def validStaging (h : ZoeHost) (ids : List SeatId) (ps : List (SeatId × AssetBundle)) : Bool :=
  decide ids.Nodup && decide (ps.map Prod.fst).Nodup &&
    ids.all (activeId h) && ids.all (fun id => (ps.map Prod.fst).contains id) &&
    ps.all (fun p => ids.contains p.1)

/-- Caller-facing seat contract, independent of the admission implementation. -/
def StagingSeatContract (h : ZoeHost) (ids : List SeatId) (ps : List (SeatId × AssetBundle)) : Prop :=
  ids.Nodup ∧ (ps.map Prod.fst).Nodup ∧
  (∀ id ∈ ids, ∃ s ∈ h.seats, s.seatId = id ∧ s.status = .active) ∧
  (∀ id ∈ ids, id ∈ ps.map Prod.fst) ∧ (∀ p ∈ ps, p.1 ∈ ids)

theorem validStaging_iff (h : ZoeHost) (ids : List SeatId) (ps : List (SeatId × AssetBundle)) :
    validStaging h ids ps = true ↔ StagingSeatContract h ids ps := by
  simp [validStaging, StagingSeatContract, activeId, List.all_eq_true, List.any_eq_true, and_assoc]

def admitReallocation (h : ZoeHost) (ids : List SeatId) (ps : List (SeatId × AssetBundle)) : Bool :=
  validStaging h ids ps && checkAssetConservation h ps && checkOfferSafety h ps

theorem admitReallocation_sound (h : ZoeHost) (ids : List SeatId) (ps : List (SeatId × AssetBundle))
    (ha : admitReallocation h ids ps = true) :
    (∀ b, bundleTotal (allocations (stagedSeats h ps)) b = totalAssets h b) ∧
    (∀ s ∈ stagedSeats h ps, OfferSafe s) ∧ (ps.map Prod.fst).Nodup := by
  simp only [admitReallocation, Bool.and_eq_true] at ha
  refine ⟨checkTotals_iff _ _ |>.mp ha.1.2, ?_, ?_⟩
  · intro s hs
    exact (offerSafeB_iff s).mp ((List.all_eq_true.mp ha.2) s hs)
  · have hv := ha.1.1
    simp only [validStaging, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1.1.1.2

def exitAllowed (rule : ExitRule) (epoch : Nat) : Bool :=
  match rule with
  | .onDemand => true
  | .waived => false
  | .afterEpoch deadline => decide (deadline ≤ epoch)

def closeSeat (settle : Bool) (s : ZoeSeat) : ZoeSeat :=
  { s with
    escrowed := .empty
    payout := s.escrowed
    status := if settle then .settled else .exited }

def exitSeats (ss : List ZoeSeat) (id : SeatId) (cap : BitVec 256) (epoch : Nat)
    (settle : Bool) : Option (List ZoeSeat) :=
  match ss with
  | [] => none
  | s :: ss =>
    if s.seatId = id then
      if s.holderCap = cap ∧ s.status = .active ∧
          (settle = true ∨ exitAllowed s.proposal.exitRule epoch = true) then
        some (closeSeat settle s :: ss)
      else none
    else (exitSeats ss id cap epoch settle).map (s :: ·)

inductive ZoeTurn where
  | enterOffer (proposal : Proposal) (holderCap : BitVec 256)
  | invokeGuestContract (seatIds : List SeatId)
  | exitSeat (seatId : SeatId) (capProof : BitVec 256)
  | settleSeat (seatId : SeatId) (capProof : BitVec 256)
  | advanceEpoch

def enteredSeat (h : ZoeHost) (p : Proposal) (cap : BitVec 256) : ZoeSeat :=
  ⟨h.seats.length, cap, p, p.give, .active, .empty⟩

def guestInput (h : ZoeHost) (ids : List SeatId) : List (SeatId × AssetBundle) :=
  (h.seats.filter (fun s => ids.contains s.seatId)).map (fun s => (s.seatId, s.escrowed))

def stepZoeHost (guest : GuestContract) (h : ZoeHost) : ZoeTurn → Option ZoeHost
  | .enterOffer p cap => some { h with seats := h.seats ++ [enteredSeat h p cap], deposits := h.deposits ++ [p.give] }
  | .invokeGuestContract ids => do
    let ps ← guest (guestInput h ids)
    if admitReallocation h ids ps then some { h with seats := stagedSeats h ps } else none
  | .exitSeat id cap => (exitSeats h.seats id cap h.epoch false).map (fun ss => { h with seats := ss })
  | .settleSeat id cap => (exitSeats h.seats id cap h.epoch true).map (fun ss => { h with seats := ss })
  | .advanceEpoch => some { h with epoch := h.epoch + 1 }

/-- The atomic application boundary retains the entire old state on failure. -/
def applyZoeTurn (guest : GuestContract) (h : ZoeHost) (t : ZoeTurn) : ZoeHost :=
  (stepZoeHost guest h t).getD h

inductive ValidZoeTrace (guest : GuestContract) : ZoeHost → List ZoeTurn → ZoeHost → Prop where
  | nil (h) : ValidZoeTrace guest h [] h
  | cons {h m f t ts} : applyZoeTurn guest h t = m → ValidZoeTrace guest m ts f →
      ValidZoeTrace guest h (t :: ts) f


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

def stagingDeltas (ss : List ZoeSeat) (ps : List (SeatId × AssetBundle)) (b : AssetBrand) : List (Nat × Int) :=
  ss.map (fun s => (s.seatId, (Int.ofNat ((updateStaging ps s).currentAllocation.amountSpec b)) -
    Int.ofNat (s.currentAllocation.amountSpec b)))

theorem stagingDeltas_sum (ss : List ZoeSeat) (ps : List (SeatId × AssetBundle)) (b : AssetBrand) :
    ((stagingDeltas ss ps b).map Prod.snd).sum =
      Int.ofNat (bundleTotal (allocations (ss.map (updateStaging ps))) b) -
      Int.ofNat (bundleTotal (allocations ss) b) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [stagingDeltas, List.map_cons, List.sum_cons] at *
    simp only [allocations, List.map_cons, bundleTotal, List.sum_cons, Int.ofNat_eq_natCast, Int.natCast_add] at *
    omega

def stagingToConservedValue (h : ZoeHost) (ids : List SeatId) (ps : List (SeatId × AssetBundle))
    (ha : admitReallocation h ids ps = true) (b : AssetBrand) : Obend.Logic.ConservedValue where
  entries := normalizedDeltas (stagingDeltas h.seats ps b)
  wf := normalizedDeltas_wf _
  conserved := by
    rw [normalizedDeltas_sum, stagingDeltas_sum]
    have hc : checkAssetConservation h ps = true := by
      simp only [admitReallocation, Bool.and_eq_true] at ha
      exact ha.1.2
    have hc := (checkTotals_iff _ _).mp hc b
    change bundleTotal (allocations (h.seats.map (updateStaging ps))) b =
      bundleTotal (allocations h.seats) b at hc
    rw [hc, Int.sub_self]

/-- Every account delta is the exact sum of its actual allocation changes. -/
theorem conservation_bridges_separationFrame (h : ZoeHost) (ids : List SeatId)
    (ps : List (SeatId × AssetBundle)) (ha : admitReallocation h ids ps = true) (b : AssetBrand) :
    ∃ v : Obend.Logic.ConservedValue, ∀ q,
      Obend.Logic.deltaAt v.entries q =
        ((stagingDeltas h.seats ps b).map (fun p => if q == p.1 then p.2 else 0)).sum :=
  ⟨stagingToConservedValue h ids ps ha b, normalizedDeltas_at _⟩

def HostInvariant (h : ZoeHost) : Prop :=
  (∀ b, totalAssets h b = bundleTotal h.deposits b) ∧
  (∀ s ∈ h.seats, OfferSafe s) ∧
  h.seats.map ZoeSeat.seatId = List.range h.seats.length

theorem closeSeat_allocation (s : ZoeSeat) (settle : Bool) (ha : s.status = .active) :
    (closeSeat settle s).currentAllocation = s.currentAllocation := by
  cases settle <;> simp [closeSeat, ZoeSeat.currentAllocation, ha]

theorem exitSeats_preserves (ss out : List ZoeSeat) (id : SeatId) (cap : BitVec 256)
    (epoch : Nat) (settle : Bool) (he : exitSeats ss id cap epoch settle = some out) :
    allocations out = allocations ss ∧ out.map ZoeSeat.seatId = ss.map ZoeSeat.seatId ∧
    ((∀ s ∈ ss, OfferSafe s) → ∀ s ∈ out, OfferSafe s) := by
  induction ss generalizing out with
  | nil => simp [exitSeats] at he
  | cons s ss ih =>
    simp only [exitSeats] at he
    split at he
    · split at he
      · rename_i hid hv
        cases he
        have hc := closeSeat_allocation s settle hv.2.1
        refine ⟨by simp [allocations, hc], by simp [closeSeat], ?_⟩
        intro hs q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · change satisfiesWant s.proposal (closeSeat settle s).currentAllocation ∨
            satisfiesRefund s.proposal (closeSeat settle s).currentAllocation
          rw [hc]
          exact hs s (by simp)
        · exact hs q (by simp [hq])
      · cases he
    · obtain ⟨rest,hr,rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨ha,hids,hSafe⟩ := ih rest hr
      refine ⟨by simpa only [allocations, List.map_cons] using congrArg (s.currentAllocation :: ·) ha, by simp [hids], ?_⟩
      intro hs q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hs q (by simp)
      · exact hSafe (fun s hm => hs s (by simp [hm])) q hq

theorem updateStaging_id (ps : List (SeatId × AssetBundle)) (s : ZoeSeat) :
    (updateStaging ps s).seatId = s.seatId := by
  unfold updateStaging; split <;> rfl

theorem step_preserves (guest : GuestContract) (h f : ZoeHost) (t : ZoeTurn)
    (hi : HostInvariant h) (he : stepZoeHost guest h t = some f) : HostInvariant f := by
  obtain ⟨hc,hs,hids⟩ := hi
  cases t with
  | enterOffer p cap =>
    cases he
    refine ⟨?_, ?_, ?_⟩
    · intro b
      simpa [totalAssets, allocations, bundleTotal, enteredSeat, ZoeSeat.currentAllocation,
        List.map_append, List.sum_append] using congrArg (· + p.give.amountSpec b) (hc b)
    · intro s hm
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hs s hm
      · right; intro b; exact Nat.le_refl _
    · simp [List.map_append, enteredSeat, hids, List.range_succ]
  | invokeGuestContract ids =>
    simp only [stepZoeHost] at he
    cases hg : guest (guestInput h ids) with
    | none => simp [hg] at he
    | some ps =>
      simp only [hg, bind, Option.bind] at he
      split at he
      · rename_i ha
        cases he
        obtain ⟨hcons,hsafe,_⟩ := admitReallocation_sound h ids ps ha
        refine ⟨fun b => (hcons b).trans (hc b), hsafe, ?_⟩
        simpa [stagedSeats, List.map_map, Function.comp_def, updateStaging_id] using hids
      · cases he
  | exitSeat id cap | settleSeat id cap =>
    obtain ⟨out,hout,rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨ha,hi,hsafe⟩ := exitSeats_preserves _ _ _ _ _ _ hout
    have hl : out.length = h.seats.length := by
      have := congrArg List.length hi; simpa using this
    refine ⟨?_, hsafe hs, ?_⟩
    · intro b; change bundleTotal (allocations out) b = _; rw [ha]; exact hc b
    · simpa [hl, hi] using hids
  | advanceEpoch => cases he; exact ⟨hc,hs,hids⟩

theorem initHost_invariant : HostInvariant initHost := by
  refine ⟨fun _ => rfl, ?_, rfl⟩
  intro s hs; cases hs

theorem applyZoeTurn_preserves (guest : GuestContract) (h : ZoeHost) (t : ZoeTurn)
    (hi : HostInvariant h) : HostInvariant (applyZoeTurn guest h t) := by
  unfold applyZoeTurn
  cases he : stepZoeHost guest h t with
  | none => exact hi
  | some f => exact step_preserves guest h f t hi he

theorem trace_invariant (guest : GuestContract) (h f : ZoeHost) (turns : List ZoeTurn)
    (hi : HostInvariant h) (ht : ValidZoeTrace guest h turns f) : HostInvariant f := by
  induction ht with
  | nil => exact hi
  | cons he _ ih =>
    apply ih
    rw [← he]
    exact applyZoeTurn_preserves guest _ _ hi

theorem rejected_staging_atomic (guest : GuestContract) (h : ZoeHost) (ids : List SeatId)
    (hf : stepZoeHost guest h (.invokeGuestContract ids) = none) :
    applyZoeTurn guest h (.invokeGuestContract ids) = h := by
  simp [applyZoeTurn, hf]

/-- No hypothesis constrains the guest's implementation or the number of turns. -/
theorem zoe_offer_safety_unconditional (guest : GuestContract) (turns : List ZoeTurn) (finalHost : ZoeHost)
    (ht : ValidZoeTrace guest initHost turns finalHost) :
    (∀ b, totalAssets finalHost b = bundleTotal finalHost.deposits b) ∧
    (∀ s ∈ finalHost.seats, OfferSafe s) ∧
    (∀ h ids ps, admitReallocation h ids ps = true → ∀ b,
      ∃ v : Obend.Logic.ConservedValue, ∀ q, Obend.Logic.deltaAt v.entries q =
        ((stagingDeltas h.seats ps b).map (fun p => if q == p.1 then p.2 else 0)).sum) ∧
    (∀ h ids, stepZoeHost guest h (.invokeGuestContract ids) = none →
      applyZoeTurn guest h (.invokeGuestContract ids) = h) := by
  have hi := trace_invariant guest initHost finalHost turns initHost_invariant ht
  exact ⟨hi.1, hi.2.1, conservation_bridges_separationFrame, rejected_staging_atomic guest⟩


def ExitViolation (ss : List ZoeSeat) (id : SeatId) (cap : BitVec 256) (epoch : Nat)
    (settle : Bool) : Prop :=
  match ss.find? (fun s => s.seatId == id) with
  | none => True
  | some s => s.holderCap ≠ cap ∨ s.status ≠ .active ∨
      (settle = false ∧ exitAllowed s.proposal.exitRule epoch = false)

theorem exitSeats_none_iff (ss : List ZoeSeat) (id : SeatId) (cap : BitVec 256)
    (epoch : Nat) (settle : Bool) :
    exitSeats ss id cap epoch settle = none ↔ ExitViolation ss id cap epoch settle := by
  induction ss with
  | nil => simp [exitSeats, ExitViolation]
  | cons s ss ih =>
    by_cases hid : s.seatId = id
    · simp only [exitSeats, hid, ↓reduceIte, ExitViolation, List.find?_cons]
      by_cases hc : s.holderCap = cap <;> by_cases ha : s.status = .active <;>
        cases settle <;> simp [hc, ha]
    · simpa [exitSeats, ExitViolation, hid] using ih

def ZoeStepViolation (guest : GuestContract) (h : ZoeHost) : ZoeTurn → Prop
  | .enterOffer _ _ => False
  | .advanceEpoch => False
  | .exitSeat id cap => ExitViolation h.seats id cap h.epoch false
  | .settleSeat id cap => ExitViolation h.seats id cap h.epoch true
  | .invokeGuestContract ids =>
    match guest (guestInput h ids) with
    | none => True
    | some ps => (¬ StagingSeatContract h ids ps) ∨
        (¬ ∀ b, bundleTotal (allocations (stagedSeats h ps)) b = totalAssets h b) ∨
        (¬ ∀ s ∈ stagedSeats h ps, OfferSafe s)

theorem zoeStep_skip_implies_violation (guest : GuestContract) (h : ZoeHost) (t : ZoeTurn) :
    stepZoeHost guest h t = none ↔ ZoeStepViolation guest h t := by
  cases t with
  | enterOffer p cap => simp [stepZoeHost, ZoeStepViolation]
  | advanceEpoch => simp [stepZoeHost, ZoeStepViolation]
  | exitSeat id cap | settleSeat id cap =>
    simpa [stepZoeHost, ZoeStepViolation] using exitSeats_none_iff h.seats id cap h.epoch _
  | invokeGuestContract ids =>
    cases hg : guest (guestInput h ids) with
    | none => simp [stepZoeHost, ZoeStepViolation, hg]
    | some ps =>
      have hs : checkOfferSafety h ps = true ↔ ∀ s ∈ stagedSeats h ps, OfferSafe s := by
        simp [checkOfferSafety, List.all_eq_true, offerSafeB_iff]
      have hc : checkAssetConservation h ps = true ↔
          ∀ b, bundleTotal (allocations (stagedSeats h ps)) b = totalAssets h b := checkTotals_iff _ _
      simp only [stepZoeHost, ZoeStepViolation, hg, bind, Option.bind]
      rw [← validStaging_iff, ← hc, ← hs]
      cases hv : validStaging h ids ps <;> cases hcv : checkAssetConservation h ps <;>
        cases hsv : checkOfferSafety h ps <;> simp [admitReallocation, hv, hcv, hsv]

theorem nonviolating_turn_succeeds (guest : GuestContract) (h : ZoeHost) (t : ZoeTurn)
    (hv : ¬ ZoeStepViolation guest h t) : ∃ f, stepZoeHost guest h t = some f := by
  cases he : stepZoeHost guest h t with
  | none => exact False.elim (hv ((zoeStep_skip_implies_violation guest h t).mp he))
  | some f => exact ⟨f,rfl⟩

theorem waived_exit_refused (guest : GuestContract) (h : ZoeHost) (id : SeatId) (cap : BitVec 256)
    (s : ZoeSeat) (hf : h.seats.find? (fun s => s.seatId == id) = some s)
    (hw : s.proposal.exitRule = .waived) : stepZoeHost guest h (.exitSeat id cap) = none := by
  apply (zoeStep_skip_implies_violation guest h _).mpr
  simp [ZoeStepViolation, ExitViolation, hf, hw, exitAllowed]

theorem wrong_cap_exit_refused (guest : GuestContract) (h : ZoeHost) (id : SeatId) (cap : BitVec 256)
    (s : ZoeSeat) (hf : h.seats.find? (fun s => s.seatId == id) = some s)
    (hc : s.holderCap ≠ cap) : stepZoeHost guest h (.exitSeat id cap) = none := by
  apply (zoeStep_skip_implies_violation guest h _).mpr
  simp [ZoeStepViolation, ExitViolation, hf, hc]

theorem guest_preserves_seat_authority (ps : List (SeatId × AssetBundle)) (s : ZoeSeat) :
    (updateStaging ps s).holderCap = s.holderCap ∧
    (updateStaging ps s).proposal = s.proposal ∧ (updateStaging ps s).status = s.status := by
  unfold updateStaging; split <;> exact ⟨rfl,rfl,rfl⟩

theorem premature_exit_refused (guest : GuestContract) (h : ZoeHost) (id : SeatId) (cap : BitVec 256)
    (s : ZoeSeat) (deadline : Nat) (hf : h.seats.find? (fun s => s.seatId == id) = some s)
    (hw : s.proposal.exitRule = .afterEpoch deadline) (he : h.epoch < deadline) :
    stepZoeHost guest h (.exitSeat id cap) = none := by
  apply (zoeStep_skip_implies_violation guest h _).mpr
  simp [ZoeStepViolation, ExitViolation, hf, hw, exitAllowed, show ¬ deadline ≤ h.epoch by omega]

theorem exitSeats_succeeds (ss : List ZoeSeat) (s : ZoeSeat) (cap : BitVec 256) (epoch : Nat)
    (hn : (ss.map ZoeSeat.seatId).Nodup) (hm : s ∈ ss) (hc : s.holderCap = cap)
    (ha : s.status = .active) (hp : exitAllowed s.proposal.exitRule epoch = true) :
    ∃ out, exitSeats ss s.seatId cap epoch false = some out ∧ closeSeat false s ∈ out := by
  induction ss with
  | nil => cases hm
  | cons x xs ih =>
    have hn' : x.seatId ∉ xs.map ZoeSeat.seatId ∧ (xs.map ZoeSeat.seatId).Nodup := by simpa using hn
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨closeSeat false s :: xs, by simp [exitSeats, hc, ha, hp], by simp⟩
    · have hne : x.seatId ≠ s.seatId := by
        intro he
        exact hn'.1 (he ▸ List.mem_map_of_mem hm)
      obtain ⟨out,ho,hm'⟩ := ih hn'.2 hm
      exact ⟨x :: out, by simp [exitSeats, hne, ho], by simp [hm']⟩

theorem onDemand_exit_guaranteed_before_commit (guest : GuestContract) (turns : List ZoeTurn)
    (h : ZoeHost) (ht : ValidZoeTrace guest initHost turns h) (s : ZoeSeat)
    (hm : s ∈ h.seats) (ha : s.status = .active) (hr : s.proposal.exitRule = .onDemand) :
    ∃ f, stepZoeHost guest h (.exitSeat s.seatId s.holderCap) = some f ∧
      closeSeat false s ∈ f.seats ∧
      (closeSeat false s).payout = s.escrowed ∧
      (satisfiesWant s.proposal (closeSeat false s).payout ∨
        satisfiesRefund s.proposal (closeSeat false s).payout) ∧
      (s.escrowed = s.proposal.give → (closeSeat false s).payout = s.proposal.give) := by
  have hi := trace_invariant guest initHost h turns initHost_invariant ht
  have hn : (h.seats.map ZoeSeat.seatId).Nodup := by rw [hi.2.2]; exact List.nodup_range
  obtain ⟨out,ho,hm'⟩ := exitSeats_succeeds h.seats s s.holderCap h.epoch hn hm rfl ha
    (by simp [hr, exitAllowed])
  refine ⟨{ h with seats := out }, by simp [stepZoeHost, ho], hm', rfl, ?_, fun he => he⟩
  simpa [OfferSafe, ZoeSeat.currentAllocation, ha, closeSeat] using hi.2.1 s hm

/-- Fresh entry preserves two distinct live handles; completeness is not a singleton harness. -/
theorem two_live_seats_inhabited (guest : GuestContract) (p q : Proposal) (c d : BitVec 256) :
    ∃ h, ValidZoeTrace guest initHost [.enterOffer p c, .enterOffer q d] h ∧
      h.seats.length = 2 ∧ h.seats.map ZoeSeat.seatId = [0,1] ∧ HostInvariant h := by
  let h₁ : ZoeHost := { seats := [enteredSeat initHost p c], deposits := [p.give] }
  let h₂ : ZoeHost := { seats := h₁.seats ++ [enteredSeat h₁ q d], deposits := [p.give,q.give] }
  have ht : ValidZoeTrace guest initHost [.enterOffer p c, .enterOffer q d] h₂ :=
    .cons rfl (.cons rfl (.nil h₂))
  exact ⟨h₂, ht, rfl, rfl, trace_invariant guest initHost h₂ _ initHost_invariant ht⟩


/-- Two distinct seats can jointly retain their escrow under the admission gate. -/
theorem admitReallocation_inhabited :
    ∃ h ids ps, h.seats.length = 2 ∧ ids = [0,1] ∧ admitReallocation h ids ps = true := by
  let b := AssetBundle.singleton 7 1 (by decide)
  let p : Proposal := ⟨b,b,.onDemand⟩
  let h : ZoeHost := { seats := [⟨0,11,p,b,.active,.empty⟩,⟨1,12,p,b,.active,.empty⟩], deposits := [b,b] }
  exact ⟨h,[0,1],[(0,b),(1,b)],rfl,rfl,by
    simp [admitReallocation, validStaging, checkAssetConservation, checkOfferSafety,
      checkTotals_iff, bundleTotal, allocations, stagedSeats, updateStaging, List.lookup,
      offerSafeB, AssetBundle.bundleLeq, AssetBundle.amountOf, CapTP.search, ZoeSeat.currentAllocation,
      activeId, h, p, b, AssetBundle.singleton, AssetBundle.amountSpec, amountList]⟩

end Obend.Polis.ZoeSeatSettlement
