module
public import Obend.Polis.VerkleUmem
public import Obend.Vault.ChunkedWorld
public import Obend.Vault.VerkleSnapshotBridge
public import Obend.Judge.Class

public section
namespace Obend.Vault.ExpVerkleAndOpenHash
open Obend.Digest.HashBytes
open Obend.Polis (encodeFields encodeFields_injective)
set_option autoImplicit false

/-- Digests always carry all 256 bits, independently of the chosen hash implementation. -/
abbrev Digest := { b : ByteArray // b.size = 32 }
abbrev Hash256 := List UInt8 → Digest

def cshakeHash : Hash256 := fun bs =>
  ⟨Obend.Polis.tagOf bs, Obend.Crypto.cshake32ByteArray_size _ _⟩

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

def hashBytes (H : Hash256) : Hash := fun bs => (H bs).val.data.toList

theorem CollisionPair.hashBytes_collision {H : Hash256} (c : CollisionPair H) :
    Collision (hashBytes H) :=
  ⟨c.left, c.right, c.distinct, congrArg (fun d : Digest => ofBE d.val.data.toList) c.equalHash⟩

/-- Constructive local reduction: both returned messages are exactly the compared preimages. -/
def comparePreimages (H : Hash256) (a b : List UInt8) (h : H a = H b) :
    PSum (a = b) (CollisionPair H) :=
  if e : a = b then .inl e else .inr ⟨a, b, e, h⟩

abbrev Key := UInt64
abbrev Val := UInt64
abbrev PhysSlot := Nat × Nat
abbrev Slot := Option (Key × Val)

/-- Geometric capacities are fixed at creation; insertion only fills an empty physical slot. -/
structure ElasticOpenTable where
  levels : Array (Array Slot)
  deriving DecidableEq

def emptyTable (base levels : Nat) : ElasticOpenTable :=
  ⟨(Array.range levels).map fun l => Array.replicate (base / 2 ^ l) none⟩

def getSlot (t : ElasticOpenTable) (p : PhysSlot) : Slot :=
  (t.levels[p.1]?.bind fun row => row[p.2]?).join

/-- Four probes per level, truncated at the capacity. No whole-level fallback scan. -/
def probeSlots (k : Key) (level cap : Nat) : List Nat :=
  (List.range (min 4 cap)).map fun j => (k.toNat + level + j) % cap

def probeCoords (t : ElasticOpenTable) (k : Key) : List PhysSlot :=
  (List.range t.levels.size).flatMap fun l =>
    (probeSlots k l (t.levels[l]!.size)).map fun s => (l, s)

def probeBudget (t : ElasticOpenTable) : Nat :=
  ((List.range t.levels.size).map fun l => min 4 (t.levels[l]!.size)).sum

theorem probeSlots_length (k : Key) (l cap : Nat) :
    (probeSlots k l cap).length = min 4 cap := by simp [probeSlots]

theorem probeCoords_length (t : ElasticOpenTable) (k : Key) :
    (probeCoords t k).length = probeBudget t := by
  simp [probeCoords, probeBudget, List.length_flatMap, probeSlots_length]

theorem probeSlots_bounded {k : Key} {l cap s : Nat} (h : s ∈ probeSlots k l cap) :
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
    ⟨t.levels.modify p.1 (fun row => row.setIfInBounds p.2 (some e))⟩
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
  | tableFull
  deriving DecidableEq, Repr

/-- Write-once duplicate policy: even a different value leaves the first binding intact. -/
def insert (t : ElasticOpenTable) (k : Key) (v : Val) : ElasticOpenTable × InsertResult :=
  match search t k (probeCoords t k) with
  | some (p, _) => (t, .alreadyPresent p)
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
  | some e => simp [hsearch] at hs
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

/-- Physical coordinates are reachable under the occupant's own bounded probe schedule. -/
def TableWF (t : ElasticOpenTable) : Prop :=
  ∀ p k v, getSlot t p = some (k, v) → p ∈ probeCoords t k

def slotBytes (s : Slot) : List UInt8 :=
  encodeFields (match s with | none => [[0]] | some (k, v) => [[1], be 8 k.toNat, be 8 v.toNat])

/-- Rows and slots are separately framed, including empty slots and row lengths. -/
def tableBytes (t : ElasticOpenTable) : List UInt8 :=
  encodeFields ([10] :: t.levels.toList.map fun row => encodeFields (row.toList.map slotBytes))

def tableDigest (H : Hash256) (t : ElasticOpenTable) : Digest := H (tableBytes t)

/-- A trusted local table plus its authenticated root. Construction hashes once; verification
reads only the bounded windows. A root-only remote verifier would need a collision disjunct. -/
structure AuthenticatedTable (H : Hash256) where
  table : ElasticOpenTable
  root : Digest
  authentic : root = tableDigest H table

def authenticateTable (H : Hash256) (t : ElasticOpenTable) : AuthenticatedTable H :=
  ⟨t, tableDigest H t, rfl⟩

structure AbsenceCertificate where
  root : Digest
  coordinates : List PhysSlot
  states : List Slot

def proveAbsence (H : Hash256) (t : AuthenticatedTable H) (k : Key) : AbsenceCertificate :=
  ⟨t.root, probeCoords t.table k, (probeCoords t.table k).map (getSlot t.table)⟩

variable {H : Hash256} in
def verifyAbsenceCert (t : AuthenticatedTable H) (k : Key)
    (c : AbsenceCertificate) : Bool :=
  decide (c.root = t.root ∧ c.coordinates = probeCoords t.table k ∧
    c.states = c.coordinates.map (getSlot t.table)) &&
  c.states.all (fun s => match s with | none => true | some (key, _) => decide (key ≠ k))

theorem verifyAbsenceCert_sound (H : Hash256) (t : AuthenticatedTable H) (k : Key)
    (c : AbsenceCertificate) (h : verifyAbsenceCert t k c = true) :
    c.root = tableDigest H t.table ∧ lookup t.table k = none ∧
      ∀ p ∈ probeCoords t.table k, ∀ v, getSlot t.table p ≠ some (k, v) := by
  simp only [verifyAbsenceCert, Bool.and_eq_true, decide_eq_true_eq] at h
  have ha := h.2
  rw [h.1.2.2, h.1.2.1] at ha
  have hn : ∀ p ∈ probeCoords t.table k, ∀ v, getSlot t.table p ≠ some (k, v) := by
    intro p hp v hv
    have ht := List.all_eq_true.mp ha (some (k, v)) (List.mem_map.mpr ⟨p, hp, hv⟩)
    simp at ht
  exact ⟨h.1.1.trans t.authentic, (lookup_none_iff _ _).mpr hn, hn⟩

theorem verifyAbsenceCert_complete (H : Hash256) (t : AuthenticatedTable H) (k : Key)
    (h : lookup t.table k = none) : verifyAbsenceCert t k (proveAbsence H t k) = true := by
  have hn := (lookup_none_iff _ _).mp h
  simp only [verifyAbsenceCert, proveAbsence, true_and, decide_true, Bool.true_and]
  apply List.all_eq_true.mpr
  intro s hs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  cases hg : getSlot t.table p with
  | none => rfl
  | some e =>
    obtain ⟨key, v⟩ := e
    simp only [decide_eq_true_eq]
    intro he
    subst key
    exact hn p hp v hg

theorem absence_excludes_all_slots (H : Hash256) (t : AuthenticatedTable H) (k : Key)
    (c : AbsenceCertificate) (hw : TableWF t.table) (hc : verifyAbsenceCert t k c = true)
    (p : PhysSlot) (v : Val) : getSlot t.table p ≠ some (k, v) := by
  intro hp
  exact (verifyAbsenceCert_sound H t k c hc).2.2 p (hw p k v hp) v hp


theorem emptyTable_wf (base levels : Nat) : TableWF (emptyTable base levels) := by
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
  frameBytes [[0], natBytes idx, match v with | none => [] | some x => be 8 x.toNat]

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
  refine ⟨natBytes_injective hf.1, UInt64.toNat_inj.mp ?_⟩
  exact be_injective (by simpa using v.toNat_lt) (by simpa using w.toNat_lt) hf.2

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
  decide (idx < p.count ∧ p.count ≤ capacity p.height ∧
    H (forestBytes p.count p.height p.treeRoot) = root) &&
  verifyNode H p.height 0 idx v p.treeRoot p.vectors

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
    simpa [verifyNode, openAt, rootAt, childrenAt, hdiv, hstart, Array.getElem?_map,
      Array.getElem?_range] using ih'

theorem verifyExpVerkleOpening_complete (H : Hash256) (f : ExpVerkleForestExec)
    (height idx : Nat) (v : Val) (hc : f.entries.size ≤ capacity height)
    (hv : f.entries[idx]? = some v) :
    verifyExpVerkleOpening H (expVerkleRoot H f height) idx v (proveExpVerkle H f height idx) = true := by
  have hi : idx < f.entries.size := (Array.getElem?_eq_some_iff.mp hv).1
  have hn := verifyNode_complete H f.entries height 0 idx v (Nat.lt_of_lt_of_le hi hc) (by simpa using hv)
  simpa [verifyExpVerkleOpening, expVerkleRoot, proveExpVerkle, hi, hc] using hn



/-- Automatic API chooses the canonical bounded height; every present entry has an opening. -/
def commitExpVerkle (H : Hash256) (f : ExpVerkleForestExec) : Digest :=
  expVerkleRoot H f (expVerkleDepth f.entries.size)

def openExpVerkle (H : Hash256) (f : ExpVerkleForestExec) (idx : Nat) : ExpVerkleProof :=
  proveExpVerkle H f (expVerkleDepth f.entries.size) idx

theorem every_index_opens (H : Hash256) (f : ExpVerkleForestExec) (idx : Nat)
    (hi : idx < f.entries.size) :
    verifyExpVerkleOpening H (commitExpVerkle H f) idx f.entries[idx] (openExpVerkle H f idx) = true :=
  verifyExpVerkleOpening_complete H f _ idx _ (expVerkleDepth_covers _)
    (Array.getElem?_eq_getElem hi)

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

/-- Traverse two accepted paths, returning the first differing preimage with equal digest.
The recursion follows actual submitted vectors, so the collision is local to the openings. -/
def extractNodeCollision (H : Hash256) (v w : Val) (hne : v ≠ w) :
    (height start idx : Nat) → (root : Digest) → (p q : List (Array Digest)) →
    verifyNode H height start idx v root p = true →
    verifyNode H height start idx w root q = true → CollisionPair H
  | 0, start, idx, root, p, q, hp, hq => by
    simp only [verifyNode, decide_eq_true_eq] at hp hq
    exact ⟨leafBytes start (some v), leafBytes start (some w),
      fun he => hne (leafBytes_injective he).2, hp.2.2.trans hq.2.2.symm⟩
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
            exact extractNodeCollision H v w hne k
              (start + idx / capacity k * capacity k) (idx % capacity k) child ps qs
              (by simpa [hg] using hp.2) (by simpa [hg] using hq.2)
        else exact ⟨_, _, hab, he⟩

/-- Full position-binding extractor, with no choice and no unscoped collision assumption. -/
def extractOpeningCollision (H : Hash256) (root : Digest) (idx : Nat) (v w : Val)
    (p q : ExpVerkleProof) (hne : v ≠ w)
    (hp : verifyExpVerkleOpening H root idx v p = true)
    (hq : verifyExpVerkleOpening H root idx w q = true) : CollisionPair H := by
  simp only [verifyExpVerkleOpening, Bool.and_eq_true, decide_eq_true_eq] at hp hq
  have he := hp.1.2.2.trans hq.1.2.2.symm
  if hf : forestBytes p.count p.height p.treeRoot = forestBytes q.count q.height q.treeRoot then
    have hb := forestBytes_injective hf
    exact extractNodeCollision H v w hne p.height 0 idx p.treeRoot p.vectors q.vectors hp.2
      (by simpa [hb.2.1, hb.2.2] using hq.2)
  else exact ⟨_, _, hf, he⟩

theorem verifyExpVerkleOpening_binds_or_collision (H : Hash256) (root : Digest)
    (idx : Nat) (v w : Val) (p q : ExpVerkleProof)
    (hp : verifyExpVerkleOpening H root idx v p = true)
    (hq : verifyExpVerkleOpening H root idx w q = true) :
    v = w ∨ ∃ a b, a ≠ b ∧ H a = H b := by
  by_cases he : v = w
  · exact .inl he
  · let c := extractOpeningCollision H root idx v w p q he hp hq
    exact .inr ⟨c.left, c.right, c.distinct, c.equalHash⟩


/-- The deployed vault wire uses the existing total codec and preserves physical array shape. -/
def wordCodec : ChunkedWorld.FastCodec UInt64 :=
  ChunkedWorld.cMap UInt64.toNat (fun n => if n < 2 ^ 64 then some (UInt64.ofNat n) else none)
    (by intro w; simp [w.toNat_lt]) ChunkedWorld.cNat

def tableCodec : ChunkedWorld.FastCodec ElasticOpenTable :=
  ChunkedWorld.cMap ElasticOpenTable.levels (fun a => some ⟨a⟩) (by intro t; rfl)
    (ChunkedWorld.cArray (ChunkedWorld.cArray
      (ChunkedWorld.cOption (ChunkedWorld.cPair wordCodec wordCodec))))

def forestCodec : ChunkedWorld.FastCodec ExpVerkleForestExec :=
  ChunkedWorld.cMap ExpVerkleForestExec.entries (fun a => some ⟨a⟩) (by intro f; rfl)
    (ChunkedWorld.cArray wordCodec)

def snapshotPayloadCodec := ChunkedWorld.cPair tableCodec forestCodec

def snapshotWireTag : String := "exp-verkle-openhash@1"

/-- Prefix a typed snapshot payload to the world's transport records. The original world,
including its existing records, pages, and journal, is retained. -/
def exportToChunkedWorld (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) : ChunkedWorld.World :=
  { w with received := (snapshotWireTag, Json.hex (snapshotPayloadCodec.enc (t, f))) :: w.received }

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
  | some e => simp [hs] at h
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
  verifyExpVerkleOpening_complete H s.2 _ _ _ (expVerkleDepth_covers _) h.2

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

/-- Semantic consistency is stated as concrete commitment and capacity equations. -/
def SnapshotMeaning (H : Hash256) (s : ExpVerkleVaultSnapshot) : Prop :=
  s.forest.entries.size ≤ capacity s.height ∧
  s.forestRoot = expVerkleRoot H s.forest s.height ∧
  s.tableRoot = tableDigest H s.table ∧
  s.umemRoot = bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest) ∧
  s.root = H (weldBytes s.forestRoot s.tableRoot s.umemRoot)

def verifySnapshot (H : Hash256) (s : ExpVerkleVaultSnapshot) : Bool :=
  decide (s.forest.entries.size ≤ capacity s.height) &&
  decide (s.forestRoot = expVerkleRoot H s.forest s.height) &&
  decide (s.tableRoot = tableDigest H s.table) &&
  decide (s.umemRoot = bindVerkleUmemRoot (exportToChunkedWorld s.world s.table s.forest)) &&
  decide (s.root = H (weldBytes s.forestRoot s.tableRoot s.umemRoot))

theorem verifySnapshot_iff (H : Hash256) (s : ExpVerkleVaultSnapshot) :
    verifySnapshot H s = true ↔ SnapshotMeaning H s := by
  simp [verifySnapshot, SnapshotMeaning, and_assoc]

def buildSnapshot (H : Hash256) (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) (height : Nat) : ExpVerkleVaultSnapshot :=
  let fr := expVerkleRoot H f height
  let tr := tableDigest H t
  let ur := bindVerkleUmemRoot (exportToChunkedWorld w t f)
  ⟨w, t, f, height, fr, tr, ur, H (weldBytes fr tr ur)⟩

theorem buildSnapshot_complete (H : Hash256) (w : ChunkedWorld.World) (t : ElasticOpenTable)
    (f : ExpVerkleForestExec) (height : Nat) (hc : f.entries.size ≤ capacity height) :
    verifySnapshot H (buildSnapshot H w t f height) = true := by
  simp [verifySnapshot, buildSnapshot, hc]

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
