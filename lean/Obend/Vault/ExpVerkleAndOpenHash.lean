module
public import Obend.Polis.VerkleUmem
public import Obend.Vault.ChunkedWorld
public import Obend.Vault.VerkleSnapshotBridge
public import Obend.Judge.Class
public import Std.Data.TreeSet.Lemmas
public import Obend.Crypto.FastRing
import all Obend.Crypto.BinaryTower256
import all Init.Data.Array.Basic

public section
namespace Obend.Vault.ExpVerkleAndOpenHash
open Obend.Digest.HashBytes
open Obend.Polis (encodeFields encodeFields_injective)
set_option autoImplicit false

/-- Digests always carry all 256 bits, independently of the chosen hash implementation. -/
abbrev Digest := { b : ByteArray // b.size = 32 }
abbrev Hash256 := List UInt8 → Digest

def cshakeHash : Hash256 := fun bs =>
  ⟨Obend.Crypto.cshake32ByteArray "OBEND.VAULT.EXPVERKLE/v2".toUTF8.data.toList bs,
    Obend.Crypto.cshake32ByteArray_size _ _⟩

/-- Every domain tag and payload is independently length-framed with unbounded LEB128 lengths. -/
def frameBytes (fields : List (List UInt8)) : List UInt8 := encodeFields fields

theorem frameBytes_injective {a b : List (List UInt8)}
    (h : frameBytes a = frameBytes b) : a = b := encodeFields_injective a b h

/-- Concrete collision data, not a global pigeonhole proposition. -/
structure CollisionPair (H : Hash256) where
  left : List UInt8
  right : List UInt8
  distinct : left ≠ right
  equalHash : H left = H right

/-- Constructive local reduction: both returned messages are certified equal to the compared preimages. -/
def comparePreimages (H : Hash256) (a b : List UInt8) (h : H a = H b) :
    PSum (a = b) { c : CollisionPair H // c.left = a ∧ c.right = b } :=
  if e : a = b then .inl e else .inr ⟨⟨a, b, e, h⟩, rfl, rfl⟩

abbrev Key := BitVec 256
abbrev Val := BitVec 256
abbrev PhysSlot := Nat × Nat
abbrev Slot := Option (Key × Val)

/-- Geometric capacities are fixed at creation; insertion only fills an empty physical slot. -/
structure ElasticOpenTable where
  levels : Array (Array Slot)
  seed : BitVec 256 := 0
  deriving DecidableEq

def emptyTable (base levels : Nat) (seed : BitVec 256 := 0) : ElasticOpenTable :=
  ⟨(Array.range levels).map (fun l => Array.replicate (base / 2 ^ l) none), seed⟩

def getSlot (t : ElasticOpenTable) (p : PhysSlot) : Slot :=
  (t.levels[p.1]?.bind fun row => row[p.2]?).join

/-- Independently framed full-width seed, key, and unbounded level number. -/
def probePreimage (seed : BitVec 256) (k : Key) (level : Nat) : List UInt8 :=
  frameBytes [[20], be 32 seed.toNat, be 32 k.toNat, ChunkedWorld.encNat level]

def probeDigest (H : Hash256) (seed : BitVec 256) (k : Key) (level : Nat) : Digest :=
  H (probePreimage seed k level)

/-- Salt affects all 256 hash bits before capacity reduction. A public salt does not
promise resistance to adaptive grinding; distinct hashes may share a reduced window. -/
def probeSlots (k : Key) (level cap : Nat) (seed : BitVec 256 := 0) : List Nat :=
  let base := ofBE (probeDigest cshakeHash seed k level).val.data.toList
  (List.range (min 4 cap)).map fun j => (base + j) % cap

theorem probe_seed_binding (H : Hash256) (a b : BitVec 256) (k : Key) (l : Nat)
    (hne : a ≠ b) (he : probeDigest H a k l = probeDigest H b k l) :
    H (probePreimage a k l) = H (probePreimage b k l) ∧
      probePreimage a k l ≠ probePreimage b k l := by
  refine ⟨he, ?_⟩
  intro h
  have hf := frameBytes_injective h
  have hs : be 32 a.toNat = be 32 b.toNat := by simpa only [List.cons.injEq, true_and, and_true] using hf
  apply hne
  apply BitVec.eq_of_toNat_eq
  exact be_injective (by simpa using a.isLt) (by simpa using b.isLt) hs

def probeCoords (t : ElasticOpenTable) (k : Key) : List PhysSlot :=
  (List.range t.levels.size).flatMap fun l =>
    (probeSlots k l (t.levels[l]!.size) t.seed).map fun s => (l, s)

def probeBudget (t : ElasticOpenTable) : Nat :=
  ((List.range t.levels.size).map fun l => min 4 (t.levels[l]!.size)).sum

theorem probeSlots_length (k : Key) (l cap : Nat) (seed : BitVec 256) :
    (probeSlots k l cap seed).length = min 4 cap := by simp [probeSlots]

theorem probeCoords_length (t : ElasticOpenTable) (k : Key) :
    (probeCoords t k).length = probeBudget t := by
  simp [probeCoords, probeBudget, List.length_flatMap, probeSlots_length]

theorem probeSlots_bounded {k : Key} {l cap s : Nat} {seed : BitVec 256}
    (h : s ∈ probeSlots k l cap seed) :
    s < cap := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  have hj' := List.mem_range.mp hj
  exact Nat.mod_lt _ (by omega)

def search (t : ElasticOpenTable) (k : Key) : List PhysSlot → Option (PhysSlot × Val)
  | [] => none
  | p :: ps => match getSlot t p with
    | some (key, v) => if key = k then some (p, v) else search t k ps
    | none => search t k ps

def lookup (t : ElasticOpenTable) (k : Key) : Option Val :=
  (search t k (probeCoords t k)).map Prod.snd

theorem search_none_iff (t : ElasticOpenTable) (k : Key) (ps : List PhysSlot) :
    search t k ps = none ↔ ∀ p ∈ ps, ∀ v, getSlot t p ≠ some (k, v) := by
  induction ps with
  | nil => simp [search]
  | cons p ps ih =>
    cases hg : getSlot t p with
    | none => simp [search, hg, ih]
    | some e =>
      obtain ⟨key, v⟩ := e
      by_cases hk : key = k
      · subst key; simp [search, hg]
      · simp [search, hg, hk, ih]

theorem search_complete (t : ElasticOpenTable) (k : Key) (ps : List PhysSlot)
    (p : PhysSlot) (v : Val) (hp : p ∈ ps) (hv : getSlot t p = some (k, v)) :
    ∃ q w, search t k ps = some (q, w) := by
  cases hs : search t k ps with
  | none => exact False.elim (((search_none_iff t k ps).mp hs) p hp v hv)
  | some e => exact ⟨e.1, e.2, rfl⟩

theorem lookup_none_iff (t : ElasticOpenTable) (k : Key) :
    lookup t k = none ↔ ∀ p ∈ probeCoords t k, ∀ v, getSlot t p ≠ some (k, v) := by
  simp [lookup, search_none_iff]

/-- Out-of-range writes are no-ops; occupied slots are also no-ops. -/
def fillSlot (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val) : ElasticOpenTable :=
  if getSlot t p = none then
    ⟨t.levels.modify p.1 (fun row => row.setIfInBounds p.2 (some e)), t.seed⟩
  else t

theorem fillSlot_preserves (t : ElasticOpenTable) (p q : PhysSlot) (e old : Key × Val)
    (h : getSlot t q = some old) : getSlot (fillSlot t p e) q = some old := by
  unfold fillSlot
  split
  next hp =>
    have hne : p ≠ q := by intro he; subst q; rw [hp] at h; contradiction
    simp only [getSlot] at *
    obtain ⟨pl, ps⟩ := p
    obtain ⟨ql, qs⟩ := q
    by_cases hl : pl = ql
    · subst ql
      have hs : ps ≠ qs := by intro hs; exact hne (by simp [hs])
      simp only [Array.getElem?_modify, ↓reduceIte]
      cases ht : t.levels[pl]? with
      | none => simp [ht] at h
      | some row => simpa [ht, Array.getElem?_setIfInBounds, hs] using h
    · simp [Array.getElem?_modify, hl, h]
  next => exact h

inductive InsertResult where
  | inserted (slot : PhysSlot)
  | alreadyPresent (slot : PhysSlot)
  | conflict (existing : Val)
  | tableFull
  deriving DecidableEq, Repr

/-- Write-once duplicate policy: even a different value leaves the first binding intact. -/
def insert (t : ElasticOpenTable) (k : Key) (v : Val) : ElasticOpenTable × InsertResult :=
  match search t k (probeCoords t k) with
  | some (p, old) => (t, if old = v then .alreadyPresent p else .conflict old)
  | none => match (probeCoords t k).find? (fun p => (getSlot t p).isNone) with
    | none => (t, .tableFull)
    | some p => (fillSlot t p (k, v), .inserted p)

theorem insert_preserves_all_prior_slots (t : ElasticOpenTable) (k : Key) (v : Val)
    (p : PhysSlot) (old : Key × Val) (h : getSlot t p = some old) :
    getSlot (insert t k v).1 p = some old := by
  unfold insert
  split
  · exact h
  · split
    · exact h
    · exact fillSlot_preserves _ _ _ _ _ h

def insertSeq (t : ElasticOpenTable) : List (Key × Val) → ElasticOpenTable
  | [] => t
  | (k, v) :: xs => insertSeq (insert t k v).1 xs

theorem insertSeq_preserves_all_prior_slots (t : ElasticOpenTable) (xs : List (Key × Val))
    (p : PhysSlot) (old : Key × Val) (h : getSlot t p = some old) :
    getSlot (insertSeq t xs) p = some old := by
  induction xs generalizing t with
  | nil => exact h
  | cons e xs ih => exact ih _ (insert_preserves_all_prior_slots t e.1 e.2 p old h)



def InBounds (t : ElasticOpenTable) (p : PhysSlot) : Prop :=
  ∃ row, t.levels[p.1]? = some row ∧ p.2 < row.size

theorem probeCoords_inBounds (t : ElasticOpenTable) (k : Key) (p : PhysSlot)
    (hp : p ∈ probeCoords t k) : InBounds t p := by
  obtain ⟨l, hl, hs⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
  have hl' := List.mem_range.mp hl
  refine ⟨t.levels[l], by simp [hl'], ?_⟩
  simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl'] using
    (probeSlots_bounded hj)

theorem fillSlot_same (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val)
    (hb : InBounds t p) (hn : getSlot t p = none) :
    getSlot (fillSlot t p e) p = some e := by
  obtain ⟨row, hr, hs⟩ := hb
  simp only [fillSlot, hn, ↓reduceIte]
  simp [getSlot, Array.getElem?_modify, hr, hs]

theorem fillSlot_other (t : ElasticOpenTable) (p q : PhysSlot) (e : Key × Val)
    (hne : p ≠ q) : getSlot (fillSlot t p e) q = getSlot t q := by
  unfold fillSlot
  split
  · unfold getSlot
    by_cases hl : p.1 = q.1
    · have hs : p.2 ≠ q.2 := fun he => hne (Prod.ext hl he)
      simp only [Array.getElem?_modify, hl, ↓reduceIte]
      cases t.levels[q.1]? <;> simp [hs]
    · simp [Array.getElem?_modify, hl]
  · rfl

theorem fillSlot_probeCoords (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val) (k : Key) :
    probeCoords (fillSlot t p e) k = probeCoords t k := by
  unfold fillSlot
  split
  · simp only [probeCoords, Array.size_modify]
    congr 1
    funext l
    by_cases hl : l < t.levels.size
    · simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_modify,
        Array.getElem?_eq_getElem hl]
      split <;> simp
    · simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_modify,
        Array.getElem?_eq_none (Nat.le_of_not_gt hl)]
  · rfl

/-- The physical partition shape is invariant, including geometrically shrinking row capacities. -/
def levelSizes (t : ElasticOpenTable) : Array Nat := t.levels.map Array.size

theorem emptyTable_levelSizes (base levels : Nat) :
    levelSizes (emptyTable base levels) = (Array.range levels).map (fun l => base / 2 ^ l) := by
  simp [levelSizes, emptyTable, Array.map_map]

theorem fillSlot_levelSizes (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val) :
    levelSizes (fillSlot t p e) = levelSizes t := by
  unfold fillSlot
  split
  · apply Array.ext
    · simp [levelSizes]
    · intro i hi hj
      simp only [levelSizes, Array.getElem_map] at *
      rw [Array.getElem_modify]
      split <;> simp
  · rfl

theorem insert_levelSizes (t : ElasticOpenTable) (k : Key) (v : Val) :
    levelSizes (insert t k v).1 = levelSizes t := by
  unfold insert
  split
  · rfl
  · split
    · rfl
    · exact fillSlot_levelSizes _ _ _

theorem insertSeq_levelSizes (t : ElasticOpenTable) (xs : List (Key × Val)) :
    levelSizes (insertSeq t xs) = levelSizes t := by
  induction xs generalizing t with
  | nil => rfl
  | cons e xs ih => exact (ih _).trans (insert_levelSizes t e.1 e.2)

theorem search_sound (t : ElasticOpenTable) (k : Key) (ps : List PhysSlot)
    (p : PhysSlot) (v : Val) (h : search t k ps = some (p, v)) :
    p ∈ ps ∧ getSlot t p = some (k, v) := by
  induction ps with
  | nil => simp [search] at h
  | cons q qs ih =>
    cases hg : getSlot t q with
    | none => exact ⟨List.mem_cons_of_mem _ (ih (by simpa [search, hg] using h)).1,
        (ih (by simpa [search, hg] using h)).2⟩
    | some e =>
      obtain ⟨key, value⟩ := e
      by_cases hk : key = k
      · subst key
        simp only [search, hg, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self, hg⟩
      · have ht : search t k qs = some (p, v) := by simpa [search, hg, hk] using h
        exact ⟨List.mem_cons_of_mem _ (ih ht).1, (ih ht).2⟩

theorem insert_then_lookup_eq (t : ElasticOpenTable) (k : Key) (v : Val) (p : PhysSlot)
    (hs : (insert t k v).2 = .inserted p) : lookup (insert t k v).1 k = some v := by
  unfold insert at hs ⊢
  cases hsearch : search t k (probeCoords t k) with
  | some e => simp only [hsearch] at hs; split at hs <;> cases hs
  | none =>
    simp only [hsearch] at hs ⊢
    cases hf : (probeCoords t k).find? (fun q => (getSlot t q).isNone) with
    | none => simp [hf] at hs
    | some q =>
      simp only [hf, InsertResult.inserted.injEq] at hs
      subst q
      have hp : p ∈ probeCoords t k := List.mem_of_find?_eq_some hf
      have hn : getSlot t p = none := Option.isNone_iff_eq_none.mp (show (getSlot t p).isNone = true from List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hf)
      have hb := probeCoords_inBounds t k p hp
      have hfill := fillSlot_same t p (k, v) hb hn
      simp only [lookup, fillSlot_probeCoords]
      cases ho : search (fillSlot t p (k, v)) k (probeCoords t k) with
      | none =>
        exact False.elim (((search_none_iff _ _ _).mp ho) p hp v hfill)
      | some e =>
        obtain ⟨q, w⟩ := e
        have hfound := search_sound _ _ _ q w ho
        by_cases he : p = q
        · subst q
          rw [hfill] at hfound
          have hv : v = w := (Prod.mk.inj (Option.some.inj hfound.2)).2
          simp [hv]
        · rw [fillSlot_other t p q (k, v) he] at hfound
          exact False.elim (((search_none_iff _ _ _).mp hsearch) q hfound.1 w hfound.2)

theorem search_fill_other_key (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val) (k : Key)
    (hb : InBounds t p) (hn : getSlot t p = none) (hne : e.1 ≠ k) (ps : List PhysSlot) :
    search (fillSlot t p e) k ps = search t k ps := by
  induction ps with
  | nil => rfl
  | cons q qs ih =>
    by_cases he : p = q
    · subst q
      simp only [search, fillSlot_same t p e hb hn, hn, hne, ite_false, ih]
    · simp only [search, fillSlot_other t p q e he]
      cases getSlot t q with
      | none => exact ih
      | some e => split <;> simp_all

/-- Logical lookup stability, including malformed starting tables with duplicate keys:
new inserts cannot shadow an earlier hit, because duplicate queries are never written. -/
theorem lookup_stable_insert (t : ElasticOpenTable) (k q : Key) (v w : Val)
    (hl : lookup t q = some w) : lookup (insert t k v).1 q = some w := by
  unfold insert
  split
  · exact hl
  · rename_i hs
    have hk : k ≠ q := by
      intro he; subst k
      simp [lookup, hs] at hl
    split
    · exact hl
    · rename_i p hp
      have hm := List.mem_of_find?_eq_some hp
      have hn := Option.isNone_iff_eq_none.mp
        (List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hp)
      simpa only [lookup, fillSlot_probeCoords,
        search_fill_other_key t p (k, v) q (probeCoords_inBounds t k p hm) hn hk] using hl

theorem lookup_stable (t : ElasticOpenTable) (xs : List (Key × Val)) (k : Key) (v : Val)
    (hl : lookup t k = some v) : lookup (insertSeq t xs) k = some v := by
  induction xs generalizing t with
  | nil => exact hl
  | cons e xs ih => exact ih _ (lookup_stable_insert t e.1 k e.2 v hl)

/-- Instrumented search counts the slot inspections actually performed, stopping on a hit. -/
def searchCount (t : ElasticOpenTable) (k : Key) : List PhysSlot → Option (PhysSlot × Val) × Nat
  | [] => (none, 0)
  | p :: ps => match getSlot t p with
    | some (key, v) => if key = k then (some (p, v), 1)
        else let r := searchCount t k ps; (r.1, r.2 + 1)
    | none => let r := searchCount t k ps; (r.1, r.2 + 1)

theorem searchCount_refines (t : ElasticOpenTable) (k : Key) (ps : List PhysSlot) :
    (searchCount t k ps).1 = search t k ps ∧ (searchCount t k ps).2 ≤ ps.length := by
  induction ps with
  | nil => simp [searchCount, search]
  | cons p ps ih =>
    cases hg : getSlot t p with
    | none => simpa [searchCount, search, hg] using ih
    | some e =>
      by_cases hk : e.1 = k
      · simp [searchCount, search, hg, hk]
      · simpa [searchCount, search, hg, hk] using ih

theorem lookup_worst_case (t : ElasticOpenTable) (k : Key) :
    (searchCount t k (probeCoords t k)).1.map Prod.snd = lookup t k ∧
    (searchCount t k (probeCoords t k)).2 ≤ probeBudget t := by
  have h := searchCount_refines t k (probeCoords t k)
  exact ⟨congrArg (Option.map Prod.snd) h.1, by simpa [probeCoords_length] using h.2⟩

theorem insert_succeeds_of_vacancy (t : ElasticOpenTable) (k : Key) (v : Val)
    (hn : lookup t k = none) (p : PhysSlot) (hp : p ∈ probeCoords t k) (he : getSlot t p = none) :
    ∃ q, (insert t k v).2 = .inserted q ∧ lookup (insert t k v).1 k = some v := by
  have hs : search t k (probeCoords t k) = none := by simpa [lookup] using hn
  have hf : (probeCoords t k).find? (fun q => (getSlot t q).isNone) ≠ none := by
    intro h
    have hh := List.find?_eq_none.mp h p hp
    simp [he] at hh
  cases hg : (probeCoords t k).find? (fun q => (getSlot t q).isNone) with
  | none => exact False.elim (hf hg)
  | some q =>
    have hr : (insert t k v).2 = .inserted q := by simp [insert, hs, hg]
    exact ⟨q, hr, insert_then_lookup_eq t k v q hr⟩

/-- Physical coordinates are reachable under the occupant's own bounded probe schedule. -/
def TableWF (t : ElasticOpenTable) : Prop :=
  ∀ p k v, getSlot t p = some (k, v) → p ∈ probeCoords t k

def slotBytes (s : Slot) : List UInt8 :=
  encodeFields (match s with | none => [[12]] | some (k, v) => [[13], be 32 k.toNat, be 32 v.toNat])

theorem emptyTable_wf (base levels : Nat) (seed : BitVec 256 := 0) : TableWF (emptyTable base levels seed) := by
  intro p k v h
  simp only [getSlot, emptyTable, Array.getElem?_map, Array.getElem?_range] at h
  split at h <;> simp_all [Array.getElem?_replicate]
  split at h <;> simp_all

theorem insert_wf (t : ElasticOpenTable) (k : Key) (v : Val) (hw : TableWF t) :
    TableWF (insert t k v).1 := by
  unfold insert
  split
  · exact hw
  · rename_i hn
    split
    · exact hw
    · rename_i p hp
      intro q key value hq
      have hm := List.mem_of_find?_eq_some hp
      have he : getSlot t p = none := Option.isNone_iff_eq_none.mp
        (List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hp)
      rw [fillSlot_probeCoords]
      by_cases hqp : p = q
      · subst q
        rw [fillSlot_same t p (k, v) (probeCoords_inBounds t k p hm) he] at hq
        have hk := (Prod.mk.inj (Option.some.inj hq)).1
        simpa [hk] using hm
      · exact hw q key value (by simpa [fillSlot_other t p q (k, v) hqp] using hq)

theorem insertSeq_wf (t : ElasticOpenTable) (xs : List (Key × Val)) (hw : TableWF t) :
    TableWF (insertSeq t xs) := by
  induction xs generalizing t with
  | nil => exact hw
  | cons e xs ih => exact ih _ (insert_wf t e.1 e.2 hw)

/-- Each key occupies at most one physical slot in a constructed table. -/
def KeyUnique (t : ElasticOpenTable) : Prop :=
  ∀ p q k v w, getSlot t p = some (k,v) → getSlot t q = some (k,w) → p = q

theorem emptyTable_unique (base levels : Nat) (seed : BitVec 256 := 0) :
    KeyUnique (emptyTable base levels seed) := by
  intro p q k v w h _
  simp only [getSlot, emptyTable, Array.getElem?_map, Array.getElem?_range] at h
  split at h <;> simp_all [Array.getElem?_replicate]
  split at h <;> simp_all

theorem insert_unique (t : ElasticOpenTable) (k : Key) (v : Val) (hw : TableWF t)
    (hu : KeyUnique t) : KeyUnique (insert t k v).1 := by
  unfold insert
  split
  · exact hu
  · rename_i hs
    split
    · exact hu
    · rename_i p hp
      have hm := List.mem_of_find?_eq_some hp
      have hn := Option.isNone_iff_eq_none.mp
        (List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hp)
      have hf := fillSlot_same t p (k,v) (probeCoords_inBounds t k p hm) hn
      have absent : ∀ q w, getSlot t q ≠ some (k,w) := by
        intro q w hq
        exact (search_none_iff t k _).mp hs q (hw q k w hq) w hq
      intro q r key x y hq hr
      by_cases heq : p = q
      · subst q
        have hk : k = key := (Prod.mk.inj (Option.some.inj (hf.symm.trans hq))).1
        by_cases her : p = r
        · exact her
        · rw [fillSlot_other t p r (k,v) her] at hr
          exact False.elim (absent r y (by simpa [hk] using hr))
      · rw [fillSlot_other t p q (k,v) heq] at hq
        by_cases her : p = r
        · subst r
          have hk : k = key := (Prod.mk.inj (Option.some.inj (hf.symm.trans hr))).1
          exact False.elim (absent q x (by simpa [hk] using hq))
        · rw [fillSlot_other t p r (k,v) her] at hr
          exact hu q r key x y hq hr

theorem insertSeq_unique (t : ElasticOpenTable) (xs : List (Key × Val))
    (hw : TableWF t) (hu : KeyUnique t) : KeyUnique (insertSeq t xs) := by
  induction xs generalizing t with
  | nil => exact hu
  | cons e xs ih => exact ih _ (insert_wf t e.1 e.2 hw) (insert_unique t e.1 e.2 hw hu)

theorem lookup_probe_bound (t : ElasticOpenTable) (k : Key) :
    (probeCoords t k).length ≤ 4 * t.levels.size := by
  rw [probeCoords_length]
  have hb : ∀ ls : List Nat,
      (ls.map fun l => min 4 (t.levels[l]!.size)).sum ≤ 4 * ls.length := by
    intro ls
    induction ls with
    | nil => simp
    | cons l ls ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
  simpa [probeBudget] using hb (List.range t.levels.size)

theorem lookup_complete_of_wf (t : ElasticOpenTable) (k : Key) (v : Val) (p : PhysSlot)
    (hw : TableWF t) (hv : getSlot t p = some (k,v)) : ∃ w, lookup t k = some w := by
  obtain ⟨q,w,hs⟩ := search_complete t k _ p v (hw p k v hv) hv
  exact ⟨w, by simp [lookup, hs]⟩

/-- Four inspections per level; whenever the row has more than four slots this is
strictly below a row scan. This bound is independent of key distribution and load. -/
theorem probe_level_sublinear (k : Key) (l cap : Nat) (seed : BitVec 256) (hc : 4 < cap) :
    (probeSlots k l cap seed).length < cap := by rw [probeSlots_length]; omega

/-- Capacity at height zero is one leaf; subsequent capacities are 2, 4, 16, 256, ... . -/
def capacity : Nat → Nat
  | 0 => 1
  | k + 1 => 2 ^ (2 ^ k)

def arity : Nat → Nat
  | 0 => 2
  | k + 1 => capacity (k + 1)

theorem capacity_pos (k : Nat) : 0 < capacity k := by
  cases k <;> simp [capacity, Nat.pow_pos]

theorem capacity_step (k : Nat) : capacity (k + 1) = arity k * capacity k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [capacity, arity, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_comm 2 (2 ^ k), Nat.pow_mul]
    simp [Nat.pow_two]


/-- Least exponential height, computed with integer logarithms rather than linear fuel.
The two tiny cases avoid the conventional `log2 0 = 0` corner. -/
def expVerkleDepth (n : Nat) : Nat :=
  if n ≤ 1 then 0 else if n ≤ 2 then 1 else (n - 1).log2.log2 + 2

theorem expVerkleDepth_covers (n : Nat) : n ≤ capacity (expVerkleDepth n) := by
  unfold expVerkleDepth
  split
  next h => simpa [capacity] using h
  next h =>
    split
    next h2 => simpa [capacity] using h2
    next h2 =>
      have ha := Nat.lt_log2_self (n := n - 1)
      have hb := Nat.lt_log2_self (n := (n - 1).log2)
      have hc := Nat.pow_le_pow_right (n := 2) (by decide)
        (show (n - 1).log2 + 1 ≤ 2 ^ ((n - 1).log2.log2 + 1) by omega)
      simp only [capacity]
      omega

/-- Exact node-depth bound for the canonical height actually used by automatic openings. -/
theorem expVerkle_depth_le_logLog (n k : Nat) (h : n ≤ 2 ^ (2 ^ k)) :
    expVerkleDepth n ≤ k + 1 := by
  unfold expVerkleDepth
  split
  next => omega
  next h1 =>
    split
    next => omega
    next h2 =>
      have hn : n - 1 ≠ 0 := by omega
      have ha : (n - 1).log2 < 2 ^ k := (Nat.log2_lt hn).mpr (by omega)
      have hb : 1 ≤ (n - 1).log2 := (Nat.le_log2 hn).mpr (by omega)
      have hc : (n - 1).log2.log2 < k := (Nat.log2_lt (by omega)).mpr ha
      omega

structure ExpVerkleSpec where
  entries : List Val
  deriving DecidableEq

def specEntries (s : ExpVerkleSpec) : List Val := s.entries

def specGet? (s : ExpVerkleSpec) (idx : Nat) : Option Val := s.entries[idx]?

/-- Append is an array push. Authentication is materialized on demand at snapshot/open time.
This deliberately does not claim logarithmic hash work: flat node vectors cost their arity. -/
structure ExpVerkleForestExec where
  entries : Array Val
  deriving DecidableEq

abbrev ExpVerkleForest := ExpVerkleForestExec

def appendExpVerkle (f : ExpVerkleForestExec) (v : Val) : ExpVerkleForestExec :=
  ⟨f.entries.push v⟩

def Simulates (s : ExpVerkleSpec) (f : ExpVerkleForestExec) : Prop :=
  f.entries.toList = specEntries s

theorem appendExpVerkle_refines (s : ExpVerkleSpec) (f : ExpVerkleForestExec) (v : Val)
    (h : Simulates s f) : Simulates ⟨s.entries ++ [v]⟩ (appendExpVerkle f v) := by
  simpa [Simulates, specEntries, appendExpVerkle] using congrArg (· ++ [v]) h

theorem appendExpVerkle_preserves (f : ExpVerkleForestExec) (v : Val) (idx : Nat)
    (h : idx < f.entries.size) : (appendExpVerkle f v).entries[idx]? = f.entries[idx]? := by
  simp [appendExpVerkle, Array.getElem?_push, h, Nat.ne_of_lt h]

/-- Natural metadata uses the vault's proven unbounded canonical codec, then a field frame. -/
def natBytes (n : Nat) : List UInt8 := ChunkedWorld.encNat n

theorem natBytes_injective {a b : Nat} (h : natBytes a = natBytes b) : a = b := by
  have ha := ChunkedWorld.decNat_encNat a []
  have hb := ChunkedWorld.decNat_encNat b []
  simp only [List.append_nil] at ha hb
  rw [show ChunkedWorld.encNat a = ChunkedWorld.encNat b from h, hb] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

def leafBytes (idx : Nat) (v : Option Val) : List UInt8 :=
  frameBytes [[0], natBytes idx, match v with | none => [] | some x => be 32 x.toNat]

def nodeBytes (level : Nat) (children : Array Digest) : List UInt8 :=
  frameBytes ([1] :: natBytes level :: children.toList.map (fun d => d.val.data.toList))

def forestBytes (count height : Nat) (root : Digest) : List UInt8 :=
  frameBytes [[2], natBytes count, natBytes height, root.val.data.toList]

theorem digest_bytes_injective {a b : Digest} (h : a.val.data.toList = b.val.data.toList) :
    a = b := Subtype.ext (Obend.Crypto.byteArray_eq_of_toList_eq h)

theorem leafBytes_injective {i j : Nat} {v w : Val}
    (h : leafBytes i (some v) = leafBytes j (some w)) : i = j ∧ v = w := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, and_true, true_and] at hf
  refine ⟨natBytes_injective hf.1, BitVec.eq_of_toNat_eq ?_⟩
  exact be_injective (by simpa using v.isLt) (by simpa using w.isLt) hf.2

theorem nodeBytes_injective {i j : Nat} {a b : Array Digest}
    (h : nodeBytes i a = nodeBytes j b) : i = j ∧ a = b := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, true_and] at hf
  refine ⟨natBytes_injective hf.1, Array.toList_inj.mp ?_⟩
  exact (List.map_inj_right (fun _ _ he => digest_bytes_injective he)).mp hf.2

theorem forestBytes_injective {n m i j : Nat} {a b : Digest}
    (h : forestBytes n i a = forestBytes m j b) : n = m ∧ i = j ∧ a = b := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, true_and, and_true] at hf
  exact ⟨natBytes_injective hf.1, natBytes_injective hf.2.1, digest_bytes_injective hf.2.2⟩


theorem leafBytes_all_fields_injective {i j : Nat} {v w : Option Val}
    (h : leafBytes i v = leafBytes j w) : i = j ∧ v = w := by
  cases v with
  | none =>
    cases w with
    | none =>
      have hf := frameBytes_injective h
      simp only [List.cons.injEq, true_and, and_true] at hf
      exact ⟨natBytes_injective hf, rfl⟩
    | some w =>
      have hf := frameBytes_injective h
      have hs := congrArg (fun fs => (fs[2]?.getD []).length) hf
      simp [length_be] at hs
  | some v =>
    cases w with
    | none =>
      have hf := frameBytes_injective h
      have hs := congrArg (fun fs => (fs[2]?.getD []).length) hf
      simp [length_be] at hs
    | some w =>
      obtain ⟨hi, hv⟩ := leafBytes_injective h
      exact ⟨hi, congrArg some hv⟩

def emptyBytes (height start : Nat) : List UInt8 :=
  frameBytes [[3], natBytes height, natBytes start]

theorem emptyBytes_injective {h k a b : Nat} (he : emptyBytes h a = emptyBytes k b) :
    h = k ∧ a = b := by
  have hf := frameBytes_injective he
  simp only [List.cons.injEq, true_and, and_true] at hf
  exact ⟨natBytes_injective hf.1, natBytes_injective hf.2⟩

/-- A sparse prefix, with absent leaves explicitly distinguished from every word value.
The recurrence is the actual exponential-arity tree, not a binary depth relabeling. -/
def rootAt (H : Hash256) (entries : Array Val) : Nat → Nat → Digest
  | 0, start => H (leafBytes start entries[start]?)
  | k + 1, start =>
    if start < entries.size then H (nodeBytes (k + 1)
      ((Array.range (arity k)).map fun j => rootAt H entries k (start + j * capacity k)))
    else H (emptyBytes (k + 1) start)


/-- List specification of the same exponential tree, including explicitly vacant subtrees. -/
def specTreeRoot (H : Hash256) (entries : List Val) : Nat → Nat → Digest
  | 0, start => H (leafBytes start entries[start]?)
  | k + 1, start =>
    if start < entries.length then H (nodeBytes (k + 1)
      (((List.range (arity k)).map fun j => specTreeRoot H entries k
        (start + j * capacity k)).toArray))
    else H (emptyBytes (k + 1) start)

theorem rootAt_refines (H : Hash256) (a : Array Val) (height start : Nat) :
    rootAt H a height start = specTreeRoot H a.toList height start := by
  induction height generalizing start with
  | zero => simp [rootAt, specTreeRoot]
  | succ k ih =>
    simp only [rootAt, specTreeRoot, Array.length_toList]
    split
    · congr 2
      apply Array.toList_inj.mp
      simp [Array.toList_range, ih]
    · rfl

def childrenAt (H : Hash256) (entries : Array Val) (k start : Nat) : Array Digest :=
  (Array.range (arity k)).map fun j => rootAt H entries k (start + j * capacity k)

/-- Top-down child vectors. Every sibling is transmitted; opening bytes are not O(log log N). -/
structure ExpVerkleProof where
  count : Nat
  height : Nat
  treeRoot : Digest
  vectors : List (Array Digest)

def openAt (H : Hash256) (entries : Array Val) : Nat → Nat → Nat → List (Array Digest)
  | 0, _, _ => []
  | k + 1, start, idx =>
    childrenAt H entries k start ::
      openAt H entries k (start + (idx / capacity k) * capacity k) (idx % capacity k)

theorem openAt_length (H : Hash256) (entries : Array Val) (height start idx : Nat) :
    (openAt H entries height start idx).length = height := by
  induction height generalizing start idx with
  | zero => rfl
  | succ k ih => simp [openAt, ih]

/-- Honest accounting: the opening sends every child digest. Small depth does not
imply small bandwidth; already the top vector costs the full exponential arity. -/
theorem opening_size_lower (H : Hash256) (entries : Array Val) (k start idx : Nat) :
    arity k ≤ ((openAt H entries (k+1) start idx).map Array.size).sum := by
  simp [openAt, childrenAt]

def verifyNode (H : Hash256) : Nat → Nat → Nat → Val → Digest → List (Array Digest) → Bool
  | 0, start, idx, v, root, path =>
    decide (idx = 0 ∧ path = [] ∧ H (leafBytes start (some v)) = root)
  | k + 1, start, idx, v, root, path => match path with
    | [] => false
    | children :: rest =>
      decide (children.size = arity k ∧ H (nodeBytes (k + 1) children) = root) &&
      match children[idx / capacity k]? with
      | none => false
      | some child => verifyNode H k (start + (idx / capacity k) * capacity k)
          (idx % capacity k) v child rest

def expVerkleRoot (H : Hash256) (f : ExpVerkleForestExec) (height : Nat) : Digest :=
  H (forestBytes f.entries.size height (rootAt H f.entries height 0))

def proveExpVerkle (H : Hash256) (f : ExpVerkleForestExec) (height idx : Nat) : ExpVerkleProof :=
  ⟨f.entries.size, height, rootAt H f.entries height 0, openAt H f.entries height 0 idx⟩

def verifyExpVerkleOpening (H : Hash256) (root : Digest) (idx : Nat) (v : Val)
    (p : ExpVerkleProof) : Bool :=
  decide (idx < p.count ∧ p.count ≤ capacity p.height ∧ p.height = expVerkleDepth p.count ∧
    H (forestBytes p.count p.height p.treeRoot) = root) &&
  verifyNode H p.height 0 idx v p.treeRoot p.vectors

private theorem range_get {n i : Nat} (h : i < (Array.range n).size) :
    (Array.range n)[i] = i :=
  Obend.Crypto.Fast.arrayOfFn_get (fun j : Fin n => j.val) ⟨i, by simpa only [Array.size_range] using h⟩
private theorem range_getOpt {n i : Nat} : (Array.range n)[i]? = if i < n then some i else none := by
  simp only [getElem?_def, Array.size_range, range_get, dite_eq_ite]
attribute [local simp] range_get range_getOpt

theorem verifyNode_complete (H : Hash256) (a : Array Val) (height start idx : Nat) (v : Val)
    (hi : idx < capacity height) (hv : a[start + idx]? = some v) :
    verifyNode H height start idx v (rootAt H a height start) (openAt H a height start idx) = true := by
  have hstart : start < a.size := by
    have := (Array.getElem?_eq_some_iff.mp hv).1
    omega
  induction height generalizing start idx with
  | zero =>
    have hz : idx = 0 := by simpa [capacity] using hi
    subst idx
    simp [verifyNode, rootAt, openAt, ← hv]
  | succ k ih =>
    have hdiv : idx / capacity k < arity k := by
      apply (Nat.div_lt_iff_lt_mul (capacity_pos k)).mpr
      simpa [capacity_step] using hi
    have hmod := Nat.mod_lt idx (capacity_pos k)
    have he : start + idx / capacity k * capacity k + idx % capacity k = start + idx := by
      have := Nat.mod_add_div idx (capacity k)
      rw [Nat.mul_comm (capacity k)] at this
      omega
    have ih' := ih (start + idx / capacity k * capacity k) (idx % capacity k) hmod (by simpa [he] using hv) (by
      have := (Array.getElem?_eq_some_iff.mp hv).1
      omega)
    simp only [verifyNode, openAt, rootAt, childrenAt, hstart, ite_true,
      Array.size_map, Array.size_range, true_and, decide_true, Bool.true_and,
      Array.getElem?_map, range_getOpt, hdiv, Option.map_some]
    exact ih'

theorem verifyExpVerkleOpening_complete (H : Hash256) (f : ExpVerkleForestExec)
    (height idx : Nat) (v : Val) (hc : f.entries.size ≤ capacity height)
    (hv : f.entries[idx]? = some v) (hh : height = expVerkleDepth f.entries.size) :
    verifyExpVerkleOpening H (expVerkleRoot H f height) idx v (proveExpVerkle H f height idx) = true := by
  have hi : idx < f.entries.size := (Array.getElem?_eq_some_iff.mp hv).1
  have hn := verifyNode_complete H f.entries height 0 idx v (Nat.lt_of_lt_of_le hi hc) (by simpa using hv)
  simpa [verifyExpVerkleOpening, expVerkleRoot, proveExpVerkle, hi, hc, hh, expVerkleDepth_covers] using hn



/-- Automatic API chooses the canonical bounded height; every present entry has an opening. -/
def commitExpVerkle (H : Hash256) (f : ExpVerkleForestExec) : Digest :=
  expVerkleRoot H f (expVerkleDepth f.entries.size)

def openExpVerkle (H : Hash256) (f : ExpVerkleForestExec) (idx : Nat) : ExpVerkleProof :=
  proveExpVerkle H f (expVerkleDepth f.entries.size) idx

theorem every_index_opens (H : Hash256) (f : ExpVerkleForestExec) (idx : Nat)
    (hi : idx < f.entries.size) :
    verifyExpVerkleOpening H (commitExpVerkle H f) idx f.entries[idx] (openExpVerkle H f idx) = true :=
  verifyExpVerkleOpening_complete H f _ idx _ (expVerkleDepth_covers _)
    (Array.getElem?_eq_getElem hi) rfl

theorem opening_depth_bound (H : Hash256) (f : ExpVerkleForestExec) (idx k : Nat)
    (h : f.entries.size ≤ 2 ^ (2 ^ k)) : (openExpVerkle H f idx).vectors.length ≤ k + 1 := by
  simpa [openExpVerkle, proveExpVerkle, openAt_length] using expVerkle_depth_le_logLog _ k h

theorem forest_commit_refines (H : Hash256) (f : ExpVerkleForestExec) (s : ExpVerkleSpec)
    (h : Simulates s f) : commitExpVerkle H f =
      H (forestBytes (specEntries s).length (expVerkleDepth (specEntries s).length)
        (specTreeRoot H (specEntries s) (expVerkleDepth (specEntries s).length) 0)) := by
  unfold commitExpVerkle expVerkleRoot
  rw [rootAt_refines, h]
  have hs : f.entries.size = (specEntries s).length := by rw [← h]; simp
  rw [hs]

def appendSeq (f : ExpVerkleForestExec) : List Val → ExpVerkleForestExec
  | [] => f
  | v :: vs => appendSeq (appendExpVerkle f v) vs

theorem appendSeq_entries (f : ExpVerkleForestExec) (vs : List Val) :
    (appendSeq f vs).entries.toList = f.entries.toList ++ vs := by
  induction vs generalizing f with
  | nil => simp [appendSeq]
  | cons v vs ih => simp [appendSeq, ih, appendExpVerkle, List.append_assoc]

theorem appendSeq_preserves (f : ExpVerkleForestExec) (vs : List Val) (idx : Nat)
    (hi : idx < f.entries.size) : (appendSeq f vs).entries[idx]? = f.entries[idx]? := by
  rw [← Array.getElem?_toList, appendSeq_entries, List.getElem?_append_left (by simpa using hi)]
  simp

/-- All preimages on the submitted path, retaining absolute leaf position. -/
def nodePreimages : Nat → Nat → Nat → Val → List (Array Digest) → List (List UInt8)
  | 0, start, _, v, _ => [leafBytes start (some v)]
  | _+1, _, _, _, [] => []
  | k+1, start, idx, v, a :: ps => nodeBytes (k+1) a ::
    nodePreimages k (start + idx / capacity k * capacity k) (idx % capacity k) v ps

def openingPreimages (p : ExpVerkleProof) (idx : Nat) (v : Val) : List (List UInt8) :=
  forestBytes p.count p.height p.treeRoot :: nodePreimages p.height 0 idx v p.vectors

abbrev ScopedCollision (H : Hash256) (messages : List (List UInt8)) :=
  { c : CollisionPair H // c.left ∈ messages ∧ c.right ∈ messages }

private def widenCollision {H : Hash256} {small large : List (List UInt8)}
    (c : ScopedCollision H small) (h : ∀ m ∈ small, m ∈ large) : ScopedCollision H large :=
  ⟨c.val, h _ c.property.1, h _ c.property.2⟩

/-- Traverse two accepted paths, returning the first differing preimage with equal digest.
The recursion follows actual submitted vectors, so the collision is local to the openings. -/
def extractNodeCollision (H : Hash256) (v w : Val) (hne : v ≠ w) :
    (height start idx : Nat) → (root : Digest) → (p q : List (Array Digest)) →
    verifyNode H height start idx v root p = true →
    verifyNode H height start idx w root q = true →
      ScopedCollision H (nodePreimages height start idx v p ++ nodePreimages height start idx w q)
  | 0, start, idx, root, p, q, hp, hq => by
    simp only [verifyNode, decide_eq_true_eq] at hp hq
    exact ⟨⟨leafBytes start (some v), leafBytes start (some w),
      fun he => hne (leafBytes_injective he).2, hp.2.2.trans hq.2.2.symm⟩,
      by simp [nodePreimages], by simp [nodePreimages]⟩
  | k + 1, start, idx, root, p, q, hp, hq => by
    cases p with
    | nil => simp [verifyNode] at hp
    | cons a ps =>
      cases q with
      | nil => simp [verifyNode] at hq
      | cons b qs =>
        simp only [verifyNode, Bool.and_eq_true, decide_eq_true_eq] at hp hq
        have he : H (nodeBytes (k + 1) a) = H (nodeBytes (k + 1) b) :=
          hp.1.2.trans hq.1.2.symm
        if hab : nodeBytes (k + 1) a = nodeBytes (k + 1) b then
          have hab' := (nodeBytes_injective hab).2
          subst b
          cases hg : a[idx / capacity k]? with
          | none => simp [hg] at hp
          | some child =>
            apply widenCollision (extractNodeCollision H v w hne k
              (start + idx / capacity k * capacity k) (idx % capacity k) child ps qs
              (by simpa [hg] using hp.2) (by simpa [hg] using hq.2))
            intro m hm
            simp only [nodePreimages, List.mem_append, List.mem_cons] at *
            rcases hm with hm | hm
            · exact .inl (.inr hm)
            · exact .inr (.inr hm)
        else exact ⟨⟨_, _, hab, he⟩, by simp [nodePreimages], by simp [nodePreimages]⟩

/-- Full position-binding extractor, with no choice and no unscoped collision assumption. -/
def extractOpeningCollision (H : Hash256) (root : Digest) (idx : Nat) (v w : Val)
    (p q : ExpVerkleProof) (hne : v ≠ w)
    (hp : verifyExpVerkleOpening H root idx v p = true)
    (hq : verifyExpVerkleOpening H root idx w q = true) :
    ScopedCollision H (openingPreimages p idx v ++ openingPreimages q idx w) := by
  simp only [verifyExpVerkleOpening, Bool.and_eq_true, decide_eq_true_eq] at hp hq
  have he := hp.1.2.2.2.trans hq.1.2.2.2.symm
  if hf : forestBytes p.count p.height p.treeRoot = forestBytes q.count q.height q.treeRoot then
    have hb := forestBytes_injective hf
    apply widenCollision (extractNodeCollision H v w hne p.height 0 idx p.treeRoot p.vectors q.vectors hp.2
      (by simpa [hb.2.1, hb.2.2] using hq.2))
    intro m hm
    simp only [openingPreimages, List.mem_append, List.mem_cons] at *
    rcases hm with hm | hm
    · exact .inl (.inr hm)
    · exact .inr (.inr (by simpa [hb.2.1] using hm))
  else exact ⟨⟨_, _, hf, he⟩, by simp [openingPreimages], by simp [openingPreimages]⟩

theorem verifyExpVerkleOpening_binds_or_collision (H : Hash256) (root : Digest)
    (idx : Nat) (v w : Val) (p q : ExpVerkleProof)
    (hp : verifyExpVerkleOpening H root idx v p = true)
    (hq : verifyExpVerkleOpening H root idx w q = true) :
    v = w ∨ Nonempty (ScopedCollision H (openingPreimages p idx v ++ openingPreimages q idx w)) := by
  by_cases he : v = w
  · exact .inl he
  · let c := extractOpeningCollision H root idx v w p q he hp hq
    exact .inr ⟨c⟩


theorem opening_binds_count (H : Hash256) (root : Digest) (idx : Nat) (v w : Val)
    (p q : ExpVerkleProof) (hp : verifyExpVerkleOpening H root idx v p = true)
    (hq : verifyExpVerkleOpening H root idx w q = true) :
    (p.count = q.count ∧ p.height = q.height) ∨
      Nonempty (ScopedCollision H (openingPreimages p idx v ++ openingPreimages q idx w)) := by
  simp only [verifyExpVerkleOpening, Bool.and_eq_true, decide_eq_true_eq] at hp hq
  by_cases he : forestBytes p.count p.height p.treeRoot = forestBytes q.count q.height q.treeRoot
  · have hi := forestBytes_injective he
    exact .inl ⟨hi.1,hi.2.1⟩
  · exact .inr ⟨⟨⟨_,_,he,hp.1.2.2.2.trans hq.1.2.2.2.symm⟩,
      by simp [openingPreimages], by simp [openingPreimages]⟩⟩

theorem slotBytes_injective {a b : Slot} (h : slotBytes a = slotBytes b) : a = b := by
  have hf := encodeFields_injective _ _ h
  cases a with
  | none => cases b <;> simp_all [slotBytes]
  | some a =>
    cases b with
    | none => simp_all [slotBytes]
    | some b =>
      have he : be 32 a.1.toNat = be 32 b.1.toNat ∧ be 32 a.2.toNat = be 32 b.2.toNat := by
        simpa [slotBytes] using hf
      have hk := be_injective (by simpa using a.1.isLt) (by simpa using b.1.isLt) he.1
      have hv := be_injective (by simpa using a.2.isLt) (by simpa using b.2.isLt) he.2
      exact congrArg some (Prod.ext (BitVec.eq_of_toNat_eq hk) (BitVec.eq_of_toNat_eq hv))

/-- Row forests hold all 256 bits of each framed slot digest. -/
def digestWord (d : Digest) : Val := BitVec.ofNat 256 (ofBE d.val.data.toList)

theorem digestWord_injective {a b : Digest} (h : digestWord a = digestWord b) : a = b := by
  open Obend.Crypto.BinaryTower256 in
  have inv (d : Digest) : toBytes32 (digestWord d) = d.val :=
    toBytes32_ofBytes32 d.val _ (by simp [ofBytes32, d.property, digestWord])
  exact Subtype.ext ((inv a).symm.trans ((congrArg _ h).trans (inv b)))

def slotWord (H : Hash256) (s : Slot) : Val := digestWord (H (slotBytes s))
def rowForest (H : Hash256) (row : Array Slot) : ExpVerkleForestExec := ⟨row.map (slotWord H)⟩

structure TableHeader where
  seed : BitVec 256
  rows : Array (Nat × Digest)
  deriving DecidableEq

def tableHeader (H : Hash256) (t : ElasticOpenTable) : TableHeader :=
  ⟨t.seed, t.levels.map fun row => (row.size, commitExpVerkle H (rowForest H row))⟩

def headerBytes (h : TableHeader) : List UInt8 :=
  frameBytes ([10] :: be 32 h.seed.toNat :: h.rows.toList.map fun (n, r) =>
    frameBytes [natBytes n, r.val.data.toList])

theorem headerBytes_injective {a b : TableHeader} (h : headerBytes a = headerBytes b) : a = b := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, true_and] at hf
  have hs : a.seed = b.seed := BitVec.eq_of_toNat_eq
    (be_injective (by simpa using a.seed.isLt) (by simpa using b.seed.isLt) hf.1)
  have hr : a.rows = b.rows := Array.toList_inj.mp ((List.map_inj_right (fun x y he => by
    have hh := frameBytes_injective he
    simp only [List.cons.injEq, and_true] at hh
    exact Prod.ext (natBytes_injective hh.1) (digest_bytes_injective hh.2))).mp hf.2)
  cases a; cases b; cases hs; cases hr; rfl

def tableDigest (H : Hash256) (t : ElasticOpenTable) : Digest := H (headerBytes (tableHeader H t))

def headerCoords (h : TableHeader) (k : Key) : List PhysSlot :=
  (List.range h.rows.size).flatMap fun l =>
    (probeSlots k l ((h.rows[l]?.map Prod.fst).getD 0) h.seed).map fun s => (l, s)

theorem headerCoords_eq (H : Hash256) (t : ElasticOpenTable) (k : Key) :
    headerCoords (tableHeader H t) k = probeCoords t k := by
  simp only [headerCoords, tableHeader, probeCoords, Array.size_map]
  congr 1
  funext l
  by_cases hl : l < t.levels.size
  · simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl]
  · simp only [Array.getElem?_map, Array.getElem?_eq_none (by omega : t.levels.size ≤ l),
      Option.map_none, Option.getD_none, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
    rfl

structure SlotOpening where
  coordinate : PhysSlot
  state : Slot
  proof : ExpVerkleProof

structure AbsenceCertificate where
  header : TableHeader
  windows : List SlotOpening

def verifySlotOpening (H : Hash256) (header : TableHeader) (o : SlotOpening) : Bool :=
  match header.rows[o.coordinate.1]? with
  | none => false
  | some (n, root) => decide (o.proof.count = n) &&
    verifyExpVerkleOpening H root o.coordinate.2 (slotWord H o.state) o.proof

/-- Root-only authentication: exactly the complete bounded probe window, including
empty slots, is opened. Neither a trusted table nor a trusted slot state is an input. -/
def verifyExpVerkleAbsence (H : Hash256) (root : Digest) (k : Key) (c : AbsenceCertificate) : Bool :=
  decide (H (headerBytes c.header) = root ∧ c.windows.map SlotOpening.coordinate = headerCoords c.header k) &&
  c.windows.all (fun o => verifySlotOpening H c.header o &&
    match o.state with | none => true | some (key, _) => decide (key ≠ k))

def openSlot (H : Hash256) (t : ElasticOpenTable) (p : PhysSlot) : SlotOpening :=
  ⟨p, getSlot t p, openExpVerkle H (rowForest H t.levels[p.1]!) p.2⟩

def proveAbsence (H : Hash256) (t : ElasticOpenTable) (k : Key) : AbsenceCertificate :=
  ⟨tableHeader H t, (probeCoords t k).map (openSlot H t)⟩

theorem openSlot_complete (H : Hash256) (t : ElasticOpenTable) (p : PhysSlot) (hb : InBounds t p) :
    verifySlotOpening H (tableHeader H t) (openSlot H t p) = true := by
  obtain ⟨row, hr, hs⟩ := hb
  have hv : (rowForest H row).entries[p.2]? = some (slotWord H (getSlot t p)) := by
    simp [rowForest, getSlot, hr, Array.getElem?_eq_getElem hs]
  have he := verifyExpVerkleOpening_complete H (rowForest H row) _ p.2 _ (expVerkleDepth_covers _) hv rfl
  simpa [verifySlotOpening, openSlot, tableHeader, Array.getElem?_map, hr,
    Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, openExpVerkle, proveExpVerkle,
    rowForest, commitExpVerkle] using he

theorem verifyAbsence_complete (H : Hash256) (t : ElasticOpenTable) (k : Key) (hn : lookup t k = none) :
    verifyExpVerkleAbsence H (tableDigest H t) k (proveAbsence H t k) = true := by
  have hn := (lookup_none_iff t k).mp hn
  simp only [verifyExpVerkleAbsence, proveAbsence, Bool.and_eq_true]
  constructor
  · apply decide_eq_true
    constructor
    · rfl
    · simp [openSlot, List.map_map, headerCoords_eq, Function.comp_def]
  · apply List.all_eq_true.mpr
    intro o ho
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
    rw [Bool.and_eq_true]
    refine ⟨openSlot_complete H t p (probeCoords_inBounds t k p hp), ?_⟩
    change (match getSlot t p with | none => true | some (key, _) => decide (key ≠ k)) = true
    cases hg : getSlot t p with
    | none => rfl
    | some e =>
      apply decide_eq_true
      intro he
      exact hn p hp e.2 (hg.trans (congrArg some (Prod.ext he rfl)))

def slotOpeningPreimages (H : Hash256) (t : ElasticOpenTable) (o : SlotOpening) : List (List UInt8) :=
  slotBytes o.state :: slotBytes (getSlot t o.coordinate) ::
    (openingPreimages o.proof o.coordinate.2 (slotWord H o.state) ++
      openingPreimages (openSlot H t o.coordinate).proof o.coordinate.2
        (slotWord H (getSlot t o.coordinate)))

def absencePreimages (H : Hash256) (t : ElasticOpenTable) (c : AbsenceCertificate) : List (List UInt8) :=
  headerBytes c.header :: headerBytes (tableHeader H t) :: c.windows.flatMap (slotOpeningPreimages H t)

/-- A forged slot either agrees with the committed row or yields an explicit
collision from the two openings or the two slot encodings. -/
def extractSlotCollision (H : Hash256) (t : ElasticOpenTable) (o : SlotOpening)
    (hb : InBounds t o.coordinate) (hv : verifySlotOpening H (tableHeader H t) o = true)
    (hne : o.state ≠ getSlot t o.coordinate) : ScopedCollision H (slotOpeningPreimages H t o) := by
  let row := t.levels[o.coordinate.1]!
  have hr : t.levels[o.coordinate.1]? = some row := by
    obtain ⟨r, hr, _⟩ := hb
    simp [row, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hr]
  have hs : o.coordinate.2 < row.size := by
    obtain ⟨r, hr', hs⟩ := hb
    rw [hr] at hr'
    cases Option.some.inj hr'
    exact hs
  have hg : (rowForest H row).entries[o.coordinate.2]? = some (slotWord H (getSlot t o.coordinate)) := by
    simp [rowForest, getSlot, hr, Array.getElem?_eq_getElem hs]
  have honest := verifyExpVerkleOpening_complete H (rowForest H row) _ o.coordinate.2 _
    (expVerkleDepth_covers _) hg rfl
  simp only [verifySlotOpening, tableHeader, Array.getElem?_map, hr, Option.map_some,
    Bool.and_eq_true, decide_eq_true_eq] at hv
  if he : slotWord H o.state = slotWord H (getSlot t o.coordinate) then
    exact ⟨⟨_, _, fun hh => hne (slotBytes_injective hh), digestWord_injective he⟩,
      by simp [slotOpeningPreimages], by simp [slotOpeningPreimages]⟩
  else
    apply widenCollision (extractOpeningCollision H _ _ _ _ o.proof _ he hv.2 honest)
    intro m hm
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)

/-- The reduction returns concrete collision data, scoped to the submitted certificate
and the authentic table by the extractor; successful absence covers every scheduled slot. -/
theorem verifyAbsence_sound_or_collision (H : Hash256) (t : ElasticOpenTable) (k : Key)
    (c : AbsenceCertificate) (hc : verifyExpVerkleAbsence H (tableDigest H t) k c = true) :
    lookup t k = none ∨ Nonempty (ScopedCollision H (absencePreimages H t c)) := by
  simp only [verifyExpVerkleAbsence, Bool.and_eq_true, decide_eq_true_eq] at hc
  by_cases hh : c.header = tableHeader H t
  · have coords : c.windows.map SlotOpening.coordinate = probeCoords t k := by
      simpa [hh, headerCoords_eq] using hc.1.2
    by_cases hn : lookup t k = none
    · exact .inl hn
    · right
      cases hs : search t k (probeCoords t k) with
      | none => exact False.elim (hn (by simp [lookup, hs]))
      | some e =>
        have hit := search_sound t k _ e.1 e.2 hs
        have hm : e.1 ∈ c.windows.map SlotOpening.coordinate := coords.symm ▸ hit.1
        obtain ⟨o, ho, he⟩ := List.mem_map.mp hm
        have hv := List.all_eq_true.mp hc.2 o ho
        simp only [Bool.and_eq_true] at hv
        have hne : o.state ≠ getSlot t o.coordinate := by
          intro eq
          have hx : getSlot t o.coordinate = some (k, e.2) := he ▸ hit.2
          rw [eq, hx] at hv
          simp at hv
        refine ⟨widenCollision (extractSlotCollision H t o (he ▸ probeCoords_inBounds t k e.1 hit.1)
          (by simpa [hh] using hv.1) hne) ?_⟩
        intro m hm
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨o, ho, hm⟩))
  · exact .inr ⟨⟨⟨_, _, fun he => hh (headerBytes_injective he), hc.1.1⟩,
      by simp [absencePreimages], by simp [absencePreimages]⟩⟩

/-- The deployed vault wire uses the existing total codec and preserves physical array shape. -/
def wordCodec : ChunkedWorld.FastCodec (BitVec 256) :=
  ChunkedWorld.cMap BitVec.toNat (fun n => if n < 2 ^ 256 then some (BitVec.ofNat 256 n) else none)
    (by intro w; simp [w.isLt]) ChunkedWorld.cNat

def tableCodec : ChunkedWorld.FastCodec ElasticOpenTable :=
  ChunkedWorld.cMap (fun t => (t.levels, t.seed)) (fun a => some ⟨a.1, a.2⟩) (by intro t; rfl)
    (ChunkedWorld.cPair (ChunkedWorld.cArray (ChunkedWorld.cArray
      (ChunkedWorld.cOption (ChunkedWorld.cPair wordCodec wordCodec)))) wordCodec)

def forestCodec : ChunkedWorld.FastCodec ExpVerkleForestExec :=
  ChunkedWorld.cMap ExpVerkleForestExec.entries (fun a => some ⟨a⟩) (by intro f; rfl)
    (ChunkedWorld.cArray wordCodec)

def snapshotPayloadCodec := ChunkedWorld.cPair tableCodec forestCodec

def snapshotWireTag : String := "exp-verkle-openhash@2"

/-- Replace the prior typed snapshot record; preserve unrelated transport records and world data. -/
def exportToChunkedWorld (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) : ChunkedWorld.World :=
  { w with received := (snapshotWireTag, Json.hex (snapshotPayloadCodec.enc (t, f))) :: w.received.filter (fun r => r.1 != snapshotWireTag) }

theorem exportToChunkedWorld_idempotent (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) :
    exportToChunkedWorld (exportToChunkedWorld w t f) t f = exportToChunkedWorld w t f := by
  simp [exportToChunkedWorld, List.filter_filter]

def importFromChunkedWorld (w : ChunkedWorld.World) : Option (ElasticOpenTable × ExpVerkleForestExec) := do
  let (tag, text) ← w.received.head?
  if tag ≠ snapshotWireTag then none else
    let bs ← Json.unhex text.toList
    snapshotPayloadCodec.decodeExact bs

theorem exportToChunkedWorld_roundtrip (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) : importFromChunkedWorld (exportToChunkedWorld w t f) = some (t, f) := by
  simp [importFromChunkedWorld, exportToChunkedWorld, ChunkedWorld.unhex_hex,
    ChunkedWorld.FastCodec.decodeExact_enc]

theorem exported_checkpoint_roundtrip (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) :
    ChunkedWorld.decodeShardedWorld (ChunkedWorld.encodeShardedWorld (exportToChunkedWorld w t f)) =
      .ok (exportToChunkedWorld w t f) := ChunkedWorld.decodeShardedWorld_encodeShardedWorld _

/-- Reuse the existing dirty-bucket cache rather than create a second snapshot format. -/
def exportIncremental (w : ChunkedWorld.World) (t : ElasticOpenTable) (f : ExpVerkleForestExec)
    (previous : Option (Array ChunkedWorld.CachedBucket)) : ByteArray × Array ChunkedWorld.CachedBucket :=
  ChunkedWorld.encodeWorldIncremental (exportToChunkedWorld w t f) previous

theorem exportIncremental_manifest (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) (previous : Option (Array ChunkedWorld.CachedBucket)) :
    (exportIncremental w t f previous).1.data.toList =
      ChunkedWorld.manifestBytes (exportToChunkedWorld w t f) :=
  ChunkedWorld.encodeWorldIncremental_manifest_eq _ _

/-- This is the actual full-address-space UMem root supplied by the existing snapshot bridge. -/
def bindVerkleUmemRoot (w : ChunkedWorld.World) : Digest :=
  ⟨VerkleSnapshotBridge.fullVerkleCommitChunks (VerkleSnapshotBridge.materializeWorldChunks w),
    VerkleSnapshotBridge.fullVerkleCommitChunks_size _⟩

def snapshotRam (w : ChunkedWorld.World) : Obend.Polis.ExtRam :=
  VerkleSnapshotBridge.chunksToExtRam (VerkleSnapshotBridge.materializeWorldChunks w)

theorem bindVerkleUmemRoot_preserves (w : ChunkedWorld.World) :
    (bindVerkleUmemRoot w).val = VerkleSnapshotBridge.specExtRamTreeTag (snapshotRam w) 16 0 :=
  VerkleSnapshotBridge.fullVerkleCommitChunks_eq_specExtRamRoot _

/-- Stable pointers contain physical coordinates, not insertion-order indices. -/
structure SlotPointer where
  coordinate : PhysSlot
  key : Key
  value : Val
  deriving DecidableEq

def verifySlotPointer (t : ElasticOpenTable) (p : SlotPointer) : Bool :=
  decide (p.coordinate ∈ probeCoords t p.key ∧ getSlot t p.coordinate = some (p.key, p.value))

theorem verifySlotPointer_sound (t : ElasticOpenTable) (p : SlotPointer)
    (h : verifySlotPointer t p = true) : getSlot t p.coordinate = some (p.key, p.value) := by
  simp only [verifySlotPointer, decide_eq_true_eq] at h
  exact h.2

theorem verifySlotPointer_complete (t : ElasticOpenTable) (p : SlotPointer)
    (hw : TableWF t) (h : getSlot t p.coordinate = some (p.key, p.value)) :
    verifySlotPointer t p = true := by
  simp [verifySlotPointer, hw _ _ _ h, h]

theorem slotPointer_multiTurn (t : ElasticOpenTable) (p : SlotPointer) (xs : List (Key × Val))
    (h : verifySlotPointer t p = true) :
    getSlot (insertSeq t xs) p.coordinate = some (p.key, p.value) :=
  insertSeq_preserves_all_prior_slots _ _ _ _ (verifySlotPointer_sound _ _ h)


/-- A physical slot and its append-log position are distinct coordinates, both retained. -/
structure VaultSlotLink where
  pointer : SlotPointer
  entryIndex : Nat

abbrev VaultState := ElasticOpenTable × ExpVerkleForestExec

def VaultLinkValid (s : VaultState) (link : VaultSlotLink) : Prop :=
  getSlot s.1 link.pointer.coordinate = some (link.pointer.key, link.pointer.value) ∧
  s.2.entries[link.entryIndex]? = some link.pointer.value

/-- Exactly one log append on a new physical insertion; duplicate and full-window refusals
leave both carriers unchanged. The returned physical slot links to the old array size. -/
def appendVault (s : VaultState) (k : Key) (v : Val) : VaultState × InsertResult :=
  let result := insert s.1 k v
  match result.2 with
  | .inserted p => ((result.1, appendExpVerkle s.2 v), .inserted p)
  | other => ((result.1, s.2), other)

theorem insert_placed (t : ElasticOpenTable) (k : Key) (v : Val) (p : PhysSlot)
    (h : (insert t k v).2 = .inserted p) : getSlot (insert t k v).1 p = some (k, v) := by
  unfold insert at h ⊢
  cases hs : search t k (probeCoords t k) with
  | some e => simp only [hs] at h; split at h <;> cases h
  | none =>
    simp only [hs] at h ⊢
    cases hq : (probeCoords t k).find? (fun q => (getSlot t q).isNone) with
    | none => simp [hq] at h
    | some q =>
      simp only [hq, InsertResult.inserted.injEq] at h
      subst q
      have hm := List.mem_of_find?_eq_some hq
      have hn := List.find?_some (p := fun q : PhysSlot => (getSlot t q).isNone) hq
      simpa [hq] using fillSlot_same t p (k, v) (probeCoords_inBounds t k p hm)
        (Option.isNone_iff_eq_none.mp hn)

theorem appendVault_inserted (s : VaultState) (k : Key) (v : Val) (p : PhysSlot)
    (h : (insert s.1 k v).2 = .inserted p) :
    VaultLinkValid (appendVault s k v).1 ⟨⟨p, k, v⟩, s.2.entries.size⟩ := by
  simp only [appendVault, h, VaultLinkValid]
  exact ⟨insert_placed _ _ _ _ h, by simp [appendExpVerkle]⟩

theorem appendVault_preserves_links (s : VaultState) (k : Key) (v : Val) (link : VaultSlotLink)
    (h : VaultLinkValid s link) : VaultLinkValid (appendVault s k v).1 link := by
  have hslot := insert_preserves_all_prior_slots s.1 k v link.pointer.coordinate
    (link.pointer.key, link.pointer.value) h.1
  have hi := (Array.getElem?_eq_some_iff.mp h.2).1
  cases hr : (insert s.1 k v).2 with
  | inserted p =>
    simpa [appendVault, hr, VaultLinkValid] using
      And.intro hslot ((appendExpVerkle_preserves _ v _ hi).trans h.2)
  | alreadyPresent p => simpa [appendVault, hr, VaultLinkValid] using And.intro hslot h.2
  | conflict old => simpa [appendVault, hr, VaultLinkValid] using And.intro hslot h.2
  | tableFull => simpa [appendVault, hr, VaultLinkValid] using And.intro hslot h.2

def appendVaultSeq (s : VaultState) : List (Key × Val) → VaultState
  | [] => s
  | (k, v) :: xs => appendVaultSeq (appendVault s k v).1 xs

theorem appendVaultSeq_preserves_links (s : VaultState) (xs : List (Key × Val))
    (link : VaultSlotLink) (h : VaultLinkValid s link) :
    VaultLinkValid (appendVaultSeq s xs) link := by
  induction xs generalizing s with
  | nil => exact h
  | cons e xs ih => exact ih _ (appendVault_preserves_links s e.1 e.2 link h)

theorem vaultLink_opens (H : Hash256) (s : VaultState) (link : VaultSlotLink)
    (h : VaultLinkValid s link) :
    verifyExpVerkleOpening H (commitExpVerkle H s.2) link.entryIndex link.pointer.value
      (openExpVerkle H s.2 link.entryIndex) = true :=
  verifyExpVerkleOpening_complete H s.2 _ _ _ (expVerkleDepth_covers _) h.2 rfl

/-- The weld commits all three roots, not a truncated limb or an equality between unrelated trees. -/
def weldBytes (forest table umem : Digest) : List UInt8 :=
  frameBytes [[11], forest.val.data.toList, table.val.data.toList, umem.val.data.toList]

theorem weldBytes_injective {a b c x y z : Digest}
    (h : weldBytes a b c = weldBytes x y z) : a = x ∧ b = y ∧ c = z := by
  have hf := frameBytes_injective h
  simp only [List.cons.injEq, true_and, and_true] at hf
  exact ⟨digest_bytes_injective hf.1, digest_bytes_injective hf.2.1,
    digest_bytes_injective hf.2.2⟩

structure ExpVerkleVaultSnapshot where
  world : ChunkedWorld.World
  table : ElasticOpenTable
  forest : ExpVerkleForestExec
  height : Nat
  forestRoot : Digest
  tableRoot : Digest
  umemRoot : Digest
  root : Digest

def allSlotCoords (t : ElasticOpenTable) : List PhysSlot :=
  (List.range t.levels.size).flatMap fun l => (List.range t.levels[l]!.size).map fun j => (l,j)

theorem getSlot_mem_coords (t : ElasticOpenTable) (p : PhysSlot) (e : Key × Val)
    (h : getSlot t p = some e) : p ∈ allSlotCoords t := by
  cases hr : t.levels[p.1]? with
  | none => simp [getSlot, hr] at h
  | some row =>
    have hl := (Array.getElem?_eq_some_iff.mp hr).1
    cases hs : row[p.2]? with
    | none => simp [getSlot, hr, hs] at h
    | some state =>
      have hj := (Array.getElem?_eq_some_iff.mp hs).1
      apply List.mem_flatMap.mpr
      refine ⟨p.1, List.mem_range.mpr hl, List.mem_map.mpr ⟨p.2, ?_, Prod.eta _⟩⟩
      simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hr] using List.mem_range.mpr hj

/-- Every live key is reachable, and its value is present in the authenticated append log.
This is a materialized consistency audit, not a proof of a unique historical operation trace. -/
def TableLinked (t : ElasticOpenTable) (f : ExpVerkleForestExec) : Prop :=
  ∀ p k v, getSlot t p = some (k,v) → p ∈ probeCoords t k ∧ v ∈ f.entries.toList

def forestValueIndex (f : ExpVerkleForestExec) : Std.TreeSet Nat :=
  Std.TreeSet.ofList (f.entries.toList.map BitVec.toNat) compare

theorem forestValueIndex_contains (f : ExpVerkleForestExec) (v : Val) :
    (forestValueIndex f).contains v.toNat = true ↔ v ∈ f.entries.toList := by
  simp only [forestValueIndex, Std.TreeSet.contains_ofList, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x,hx,he⟩
    exact (BitVec.eq_of_toNat_eq he) ▸ hx
  · intro h; exact ⟨v,h,rfl⟩

/-- Build the balanced value index once, then scan slots with logarithmic value queries. -/
def checkSnapshotTable (t : ElasticOpenTable) (f : ExpVerkleForestExec) : Bool :=
  let values := forestValueIndex f
  (allSlotCoords t).all fun p => match getSlot t p with
    | none => true
    | some (k,v) => decide (p ∈ probeCoords t k) && values.contains v.toNat

theorem checkSnapshotTable_iff (t : ElasticOpenTable) (f : ExpVerkleForestExec) :
    checkSnapshotTable t f = true ↔ TableLinked t f := by
  simp only [checkSnapshotTable, List.all_eq_true]
  constructor
  · intro h p k v hv
    have hh := h p (getSlot_mem_coords t p (k,v) hv)
    simpa only [hv, Bool.and_eq_true, decide_eq_true_eq, forestValueIndex_contains] using hh
  · intro h p _
    cases hg : getSlot t p with
    | none => rfl
    | some e => simpa only [Bool.and_eq_true, decide_eq_true_eq, forestValueIndex_contains] using h p e.1 e.2 hg

theorem TableLinked.wf {t : ElasticOpenTable} {f : ExpVerkleForestExec} (h : TableLinked t f) : TableWF t :=
  fun p k v hv => (h p k v hv).1

/-- Semantic consistency is stated as concrete commitment and capacity equations. -/
def SnapshotMeaning (H : Hash256) (s : ExpVerkleVaultSnapshot) : Prop :=
  TableLinked s.table s.forest ∧ s.forest.entries.size ≤ capacity s.height ∧
  s.forestRoot = expVerkleRoot H s.forest s.height ∧
  s.tableRoot = tableDigest H s.table ∧
  s.umemRoot = bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest) ∧
  s.root = H (weldBytes s.forestRoot s.tableRoot s.umemRoot)

def verifySnapshot (H : Hash256) (s : ExpVerkleVaultSnapshot) : Bool :=
  checkSnapshotTable s.table s.forest && decide (s.forest.entries.size ≤ capacity s.height) &&
  decide (s.forestRoot = expVerkleRoot H s.forest s.height) &&
  decide (s.tableRoot = tableDigest H s.table) &&
  decide (s.umemRoot = bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest)) &&
  decide (s.root = H (weldBytes s.forestRoot s.tableRoot s.umemRoot))

theorem verifySnapshot_iff (H : Hash256) (s : ExpVerkleVaultSnapshot) :
    verifySnapshot H s = true ↔ SnapshotMeaning H s := by
  simp [verifySnapshot, SnapshotMeaning, checkSnapshotTable_iff, and_assoc]

def buildSnapshot (H : Hash256) (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) (height : Nat) : ExpVerkleVaultSnapshot :=
  let fr := expVerkleRoot H f height
  let tr := tableDigest H t
  let ur := bindVerkleUmemRoot (exportToChunkedWorld w t f)
  ⟨w, t, f, height, fr, tr, ur, H (weldBytes fr tr ur)⟩

theorem buildSnapshot_complete (H : Hash256) (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) (height : Nat) (hc : f.entries.size ≤ capacity height) (hl : TableLinked t f) :
    verifySnapshot H (buildSnapshot H w t f height) = true := by
  simp [verifySnapshot, buildSnapshot, hc, (checkSnapshotTable_iff t f).mpr hl]

inductive SnapshotRefusal where
  | inconsistentCommitment
  deriving DecidableEq, Repr

/-- Total exact audit of a materialized snapshot. Refusal refutes its semantic consistency. -/
@[expose, instance_reducible] def expVerkleVaultJudge (H : Hash256) : Obend.Judge ExpVerkleVaultSnapshot Unit where
  Clause := SnapshotRefusal
  Meaning s _ := SnapshotMeaning H s
  check _ s _ := if verifySnapshot H s then .ok else .refused .inconsistentCommitment []
  sound := by
    intro _ s _ h
    split at h
    next ht => exact (verifySnapshot_iff H s).mp ht
    next => cases h
  refutes := fun _ => true
  refuted := by
    intro _ s _ _ _ h _ _ hm
    have ht := (verifySnapshot_iff H s).mpr hm
    simp [ht] at h
  Fragment := fun _ => True
  complete := by
    intro s _ h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, 0, by simp [(verifySnapshot_iff H s).mpr hc]⟩
  mono := by intros; rfl

theorem snapshot_refusal (H : Hash256) (s : ExpVerkleVaultSnapshot)
    (h : s.umemRoot ≠ bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest))
    (grade : Nat) : (expVerkleVaultJudge H).check grade s () = .refused SnapshotRefusal.inconsistentCommitment [] := by
  change (if verifySnapshot H s = true then Obend.Judge.Verdict.ok else
    Obend.Judge.Verdict.refused SnapshotRefusal.inconsistentCommitment []) = _
  have hf : verifySnapshot H s = false := by simp [verifySnapshot, h]
  rw [hf]
  rfl

end Obend.Vault.ExpVerkleAndOpenHash
