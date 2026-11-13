module
public import Obend.Crypto.Transcript

public section

/-
# Obend.Polis.VerkleUmem — extensional RAM, an array-backed offline memory checker, a wide hash tree

Supersedes §2 of `Obend.Trailblaze.Polis`: its `verifyBlumMemory` counted multiplicities with
`List.filter` once per element, its soundness theorem returned the checker's own conjuncts, and its
`verkleTag256` field was never opened against anything.

1. `ExtRam`, `execRamSpec`: memory as a function, a trace replayed in order from zero.
   `execRamFrom_eq_some_iff` says replay succeeds exactly when every read returns the value of the
   latest earlier write to its address (zero if none).
2. `verifyFastBlumArray online offline perm`, after Blum, Evans, Gemmell, Kannan and Naor, *Checking
   the Correctness of Memories* (FOCS 1991), in the sorted-transcript form: one `foldlM` over
   `online` (clocks increase), one over `offline` (strict `(addr, clk)` order and per-address
   read-after-write), one over `offline` that looks each row up in `online` through `perm`. No pass
   is quadratic. `verifyFastBlumArray_sound` gives `∃ ram, OnlineMatchesExtRam online ram`;
   `verifyFastBlumArray_complete` gives acceptance of every replayable trace with increasing clocks,
   on the witness `blumWitness` computes by merge sort.
3. A 16-ary hash tree over cSHAKE256 with 64-bit keys (sixteen levels of nibbles). It is a wide
   Merkle tree: each level of an opening carries the fifteen sibling tags, and there is no vector
   commitment. `verifyOpening_binds` and `verifyUpdate_binds` reduce a double opening to a
   `CollisionAmong` the preimages the two openings hashed.
-/

namespace Obend.Polis

open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes

set_option autoImplicit false

/-! ## 0. Option folds and two list lemmas -/

theorem foldlM_cons_some {σ α : Type} (f : σ → α → Option σ) (s : σ) (x : α) (l : List α)
    (s' : σ) :
    List.foldlM f s (x :: l) = some s' ↔ ∃ s1, f s x = some s1 ∧ List.foldlM f s1 l = some s' := by
  rw [List.foldlM_cons]
  cases h : f s x <;> simp

theorem foldlM_append_some {σ α : Type} (f : σ → α → Option σ) : ∀ (l l' : List α) (s s' : σ),
    List.foldlM f s (l ++ l') = some s' ↔
      ∃ s1, List.foldlM f s l = some s1 ∧ List.foldlM f s1 l' = some s'
  | [], _, s, _ => by
    constructor
    · intro h
      exact ⟨s, rfl, h⟩
    · rintro ⟨s1, h1, h2⟩
      have e : some s = some s1 := h1
      cases e
      exact h2
  | x :: l, l', s, s' => by
    rw [List.cons_append, foldlM_cons_some]
    constructor
    · rintro ⟨s1, h1, h2⟩
      obtain ⟨s2, h3, h4⟩ := (foldlM_append_some f l l' s1 s').1 h2
      exact ⟨s2, (foldlM_cons_some _ _ _ _ _).2 ⟨s1, h1, h3⟩, h4⟩
    · rintro ⟨s2, h3, h4⟩
      obtain ⟨s1, h1, h5⟩ := (foldlM_cons_some _ _ _ _ _).1 h3
      exact ⟨s1, h1, (foldlM_append_some f l l' s1 s').2 ⟨s2, h5, h4⟩⟩

/-- Two lists strictly sorted by an asymmetric relation, with the same members, are equal. -/
theorem eq_of_pairwise_of_mem_iff {α : Type} {R : α → α → Prop} (irrefl : ∀ a, ¬ R a a)
    (asymm : ∀ a b, R a b → R b a → False) :
    ∀ (l₁ l₂ : List α), l₁.Pairwise R → l₂.Pairwise R → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => by
    have hy := (h y).2 (List.mem_cons.2 (.inl rfl))
    cases hy
  | x :: _, [], _, _, h => by
    have hx := (h x).1 (List.mem_cons.2 (.inl rfl))
    cases hx
  | x :: t, y :: u, p₁, p₂, h => by
    obtain ⟨hx, pt⟩ := List.pairwise_cons.1 p₁
    obtain ⟨hy, pu⟩ := List.pairwise_cons.1 p₂
    have hxy : x = y := by
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons.2 (.inl rfl))) with e | hxu
      · exact e
      · rcases List.mem_cons.1 ((h y).2 (List.mem_cons.2 (.inl rfl))) with e | hyt
        · exact e.symm
        · exact (asymm x y (hx y hyt) (hy x hxu)).elim
    subst hxy
    have htail : ∀ z, z ∈ t ↔ z ∈ u := by
      intro z
      constructor
      · intro hz
        rcases List.mem_cons.1 ((h z).1 (List.mem_cons.2 (.inr hz))) with e | hzu
        · exact (irrefl x (e ▸ hx z hz)).elim
        · exact hzu
      · intro hz
        rcases List.mem_cons.1 ((h z).2 (List.mem_cons.2 (.inr hz))) with e | hzt
        · exact (irrefl x (e ▸ hy z hz)).elim
        · exact hzt
    rw [eq_of_pairwise_of_mem_iff irrefl asymm t u pt pu htail]

/-- Pigeonhole: a duplicate-free list inside a list no longer than itself exhausts it. -/
theorem subset_of_nodup_of_length_le {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) → l₂.length ≤ l₁.length →
      ∀ y, y ∈ l₂ → y ∈ l₁
  | [], l₂, _, _, hlen, y, hy => by
    have hnil : l₂ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    rw [hnil] at hy
    exact hy
  | x :: t, l₂, hnd, hsub, hlen, y, hy => by
    obtain ⟨hxt, hndt⟩ := List.nodup_cons.1 hnd
    have hx : x ∈ l₂ := hsub x (List.mem_cons.2 (.inl rfl))
    have hlen' : (l₂.erase x).length ≤ t.length := by
      rw [List.length_erase_of_mem hx]
      simp only [List.length_cons] at hlen
      omega
    have hsub' : ∀ z, z ∈ t → z ∈ l₂.erase x := by
      intro z hz
      have hzx : z ≠ x := fun e => hxt (e ▸ hz)
      exact (List.mem_erase_of_ne hzx).2 (hsub z (List.mem_cons.2 (.inr hz)))
    by_cases hyx : y = x
    · exact List.mem_cons.2 (.inl hyx)
    · exact List.mem_cons.2 (.inr
        (subset_of_nodup_of_length_le t (l₂.erase x) hndt hsub' hlen' y
          ((List.mem_erase_of_ne hyx).2 hy)))

/-! ## 1. Extensional RAM -/

/-- One memory operation: a read or a write of `val` at `addr`, stamped with a clock. -/
structure MemOp where
  addr : UInt64
  clk : UInt64
  isWrite : Bool
  val : UInt64
  deriving DecidableEq, Repr

/-- Memory as a function from addresses to words. -/
abbrev ExtRam := UInt64 → UInt64

/-- The all-zero memory every trace starts from. -/
def zeroRam : ExtRam := fun _ => 0

/-- `ram` with `a` set to `v`. -/
def writeRam (ram : ExtRam) (a v : UInt64) : ExtRam := fun x => if x = a then v else ram x

theorem writeRam_same (ram : ExtRam) (a v : UInt64) : writeRam ram a v a = v := by
  simp [writeRam]

theorem writeRam_other (ram : ExtRam) {a x : UInt64} (v : UInt64) (h : x ≠ a) :
    writeRam ram a v x = ram x := by
  simp [writeRam, h]

/-- Replay a trace in order: a write updates the memory, a read must return what the memory holds. -/
def execRamFrom (ram : ExtRam) : List MemOp → Option ExtRam
  | [] => some ram
  | op :: rest =>
    if op.isWrite then execRamFrom (writeRam ram op.addr op.val) rest
    else if op.val = ram op.addr then execRamFrom ram rest else none

/-- Replay from the zero memory. -/
def execRamSpec (ops : List MemOp) : Option ExtRam := execRamFrom zeroRam ops

/-- The online trace is a correct run of a RAM that ends in `ram`. -/
def OnlineMatchesExtRam (online : Array MemOp) (ram : ExtRam) : Prop :=
  execRamSpec online.toList = some ram

/-- The memory after the writes of a trace, reads ignored. -/
def ramAfter (ram : ExtRam) : List MemOp → ExtRam
  | [] => ram
  | op :: rest => ramAfter (if op.isWrite then writeRam ram op.addr op.val else ram) rest

/-- **Replay is "every read returns the latest earlier write".** -/
theorem execRamFrom_eq_some_iff : ∀ (ops : List MemOp) (ram ram' : ExtRam),
    execRamFrom ram ops = some ram' ↔
      ram' = ramAfter ram ops ∧
        ∀ pre r post, ops = pre ++ r :: post → r.isWrite = false →
          r.val = ramAfter ram pre r.addr
  | [], ram, ram' => by
    constructor
    · intro h
      have e : some ram = some ram' := h
      cases e
      exact ⟨rfl, fun pre r post hs _ => by simp at hs⟩
    · rintro ⟨rfl, _⟩
      rfl
  | op :: rest, ram, ram' => by
    cases hw : op.isWrite
    · by_cases hv : op.val = ram op.addr
      · have hstep : execRamFrom ram (op :: rest) = execRamFrom ram rest := by
          simp [execRamFrom, hw, hv]
        have hafter : ∀ l, ramAfter ram (op :: l) = ramAfter ram l := fun l => by
          simp [ramAfter, hw]
        rw [hstep, execRamFrom_eq_some_iff rest ram ram', hafter]
        constructor
        · rintro ⟨e, H⟩
          refine ⟨e, fun pre r post hs hr => ?_⟩
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hs
            rw [← hs.1]
            exact hv
          | cons p pre' =>
            simp only [List.cons_append, List.cons.injEq] at hs
            rw [← hs.1, hafter]
            exact H pre' r post hs.2 hr
        · rintro ⟨e, H⟩
          refine ⟨e, fun pre r post hs hr => ?_⟩
          have := H (op :: pre) r post (by rw [hs]; rfl) hr
          rwa [hafter] at this
      · have hstep : execRamFrom ram (op :: rest) = none := by
          simp [execRamFrom, hw, hv]
        rw [hstep]
        constructor
        · intro h
          simp at h
        · rintro ⟨_, H⟩
          exact absurd (H [] op rest rfl hw) hv
    · have hstep : execRamFrom ram (op :: rest) =
          execRamFrom (writeRam ram op.addr op.val) rest := by
        simp [execRamFrom, hw]
      have hafter : ∀ l, ramAfter ram (op :: l) = ramAfter (writeRam ram op.addr op.val) l :=
        fun l => by simp [ramAfter, hw]
      rw [hstep, execRamFrom_eq_some_iff rest _ ram', hafter]
      constructor
      · rintro ⟨e, H⟩
        refine ⟨e, fun pre r post hs hr => ?_⟩
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hs
          rw [← hs.1, hw] at hr
          cases hr
        | cons p pre' =>
          simp only [List.cons_append, List.cons.injEq] at hs
          rw [← hs.1, hafter]
          exact H pre' r post hs.2 hr
      · rintro ⟨e, H⟩
        refine ⟨e, fun pre r post hs hr => ?_⟩
        have := H (op :: pre) r post (by rw [hs]; rfl) hr
        rwa [hafter] at this

/-! ## 2. One cell at a time -/

/-- The operations of a trace at one address, in trace order. -/
def atAddr (a : UInt64) (ops : List MemOp) : List MemOp := ops.filter (fun o => o.addr == a)

theorem atAddr_cons_same (op : MemOp) (rest : List MemOp) :
    atAddr op.addr (op :: rest) = op :: atAddr op.addr rest := by
  simp [atAddr]

theorem atAddr_cons_ne {op : MemOp} {a : UInt64} (h : op.addr ≠ a) (rest : List MemOp) :
    atAddr a (op :: rest) = atAddr a rest := by
  simp [atAddr, h]

/-- Replay of a single cell holding `v`; addresses are not looked at. -/
def cellRun (v : UInt64) : List MemOp → Bool
  | [] => true
  | op :: rest => if op.isWrite then cellRun op.val rest else (op.val == v && cellRun v rest)

theorem cellRun_cons_write (v : UInt64) {op : MemOp} (rest : List MemOp) (hw : op.isWrite = true) :
    cellRun v (op :: rest) = cellRun op.val rest := by
  simp [cellRun, hw]

theorem cellRun_cons_read (v : UInt64) {op : MemOp} (rest : List MemOp) (hw : op.isWrite = false) :
    cellRun v (op :: rest) = (op.val == v && cellRun v rest) := by
  simp [cellRun, hw]

/-- **A trace replays exactly when each address's own subtrace does.** -/
theorem execRamFrom_isSome_iff : ∀ (ops : List MemOp) (ram : ExtRam),
    (execRamFrom ram ops).isSome = true ↔ ∀ a, cellRun (ram a) (atAddr a ops) = true
  | [], ram => by simp [execRamFrom, atAddr, cellRun]
  | op :: rest, ram => by
    cases hw : op.isWrite
    · by_cases hv : op.val = ram op.addr
      · have hstep : execRamFrom ram (op :: rest) = execRamFrom ram rest := by
          simp [execRamFrom, hw, hv]
        rw [hstep, execRamFrom_isSome_iff rest ram]
        have key : ∀ a, cellRun (ram a) (atAddr a (op :: rest)) =
            cellRun (ram a) (atAddr a rest) := by
          intro a
          by_cases ha : op.addr = a
          · subst ha
            rw [atAddr_cons_same, cellRun_cons_read _ _ hw, hv]
            simp
          · rw [atAddr_cons_ne ha]
        simp only [key]
      · have hstep : execRamFrom ram (op :: rest) = none := by
          simp [execRamFrom, hw, hv]
        rw [hstep]
        constructor
        · intro h
          simp at h
        · intro h
          have hcell := h op.addr
          rw [atAddr_cons_same, cellRun_cons_read _ _ hw] at hcell
          have hne : (op.val == ram op.addr) = false := by simpa using hv
          rw [hne] at hcell
          simp at hcell
    · have hstep : execRamFrom ram (op :: rest) =
          execRamFrom (writeRam ram op.addr op.val) rest := by
        simp [execRamFrom, hw]
      rw [hstep, execRamFrom_isSome_iff rest _]
      have key : ∀ a, cellRun (writeRam ram op.addr op.val a) (atAddr a rest) =
          cellRun (ram a) (atAddr a (op :: rest)) := by
        intro a
        by_cases ha : op.addr = a
        · subst ha
          rw [atAddr_cons_same, cellRun_cons_write _ _ hw, writeRam_same]
        · rw [atAddr_cons_ne ha, writeRam_other ram _ (Ne.symm ha)]
      simp only [key]

/-! ## 3. The three passes -/

/-- Clock order of two operations. -/
def clkLt (x y : MemOp) : Prop := x.clk.toNat < y.clk.toNat

/-- The key `(a, c)` is strictly below the `(addr, clk)` of `o`. -/
def keyLt (a c : UInt64) (o : MemOp) : Prop :=
  a.toNat < o.addr.toNat ∨ (a = o.addr ∧ c.toNat < o.clk.toNat)

/-- Strict lexicographic `(addr, clk)` order. -/
def lexLt (x y : MemOp) : Prop := keyLt x.addr x.clk y

theorem keyLt_trans {a c : UInt64} {op o : MemOp} (h₁ : keyLt a c op) (h₂ : lexLt op o) :
    keyLt a c o := by
  rcases h₁ with h₁ | ⟨h₁, h₁'⟩
  · rcases h₂ with h₂ | ⟨h₂, _⟩
    · exact .inl (Nat.lt_trans h₁ h₂)
    · exact .inl (h₂ ▸ h₁)
  · rcases h₂ with h₂ | ⟨h₂, h₂'⟩
    · exact .inl (h₁ ▸ h₂)
    · exact .inr ⟨h₁.trans h₂, Nat.lt_trans h₁' h₂'⟩

theorem lexLt_irrefl (x : MemOp) : ¬ lexLt x x := by
  rintro (h | ⟨_, h⟩) <;> exact Nat.lt_irrefl _ h

/-- Online pass: the clock strictly increases. The state is the previous clock. -/
def clkStep (prev : Option UInt64) (op : MemOp) : Option (Option UInt64) :=
  match prev with
  | none => some (some op.clk)
  | some c => if c < op.clk then some (some op.clk) else none

/-- Where the offline pass stands: the address it is in, the last clock seen there, and the value
that cell holds. -/
structure Cursor where
  addr : UInt64
  clk : UInt64
  val : UInt64

/-- The value the offline pass expects at `a`: the cursor's, if it stands at `a`; otherwise zero. -/
def Cursor.cur (st : Option Cursor) (a : UInt64) : UInt64 :=
  match st with
  | some c => if c.addr = a then c.val else 0
  | none => 0

theorem Cursor.cur_some_same (a c v : UInt64) : Cursor.cur (some ⟨a, c, v⟩) a = v := by
  simp [Cursor.cur]

theorem Cursor.cur_some_ne {a' a : UInt64} (c v : UInt64) (h : a' ≠ a) :
    Cursor.cur (some ⟨a', c, v⟩) a = 0 := by
  simp [Cursor.cur, h]

/-- Offline order check: the row is strictly above the cursor in `(addr, clk)`. -/
def offOrder (st : Option Cursor) (op : MemOp) : Bool :=
  match st with
  | none => true
  | some c => decide (c.addr < op.addr) || (c.addr == op.addr && decide (c.clk < op.clk))

/-- Offline read check: a read returns the value its cell holds. -/
def offReadOk (cur : UInt64) (op : MemOp) : Bool := op.isWrite || op.val == cur

theorem offReadOk_read {cur : UInt64} {op : MemOp} (hw : op.isWrite = false)
    (h : offReadOk cur op = true) : (op.val == cur) = true := by
  simpa [offReadOk, hw] using h

/-- Offline pass, one row. -/
def offStep (st : Option Cursor) (op : MemOp) : Option (Option Cursor) :=
  if offOrder st op && offReadOk (Cursor.cur st op.addr) op then
    some (some ⟨op.addr, op.clk, if op.isWrite then op.val else Cursor.cur st op.addr⟩)
  else none

/-- Permutation pass, one row: offline row `i` is the online row `perm[i]`. -/
def permStep (online : Array MemOp) (perm : Array Nat) (i : Nat) (op : MemOp) :
    Option Nat :=
  match perm[i]? with
  | some j => if online[j]? = some op then some (i + 1) else none
  | none => none

/-- **The offline memory checker.** `online` is the trace in execution order, `offline` the same
rows sorted by `(addr, clk)`, and `perm[i]` the position in `online` of `offline[i]`. Three linear
passes; nothing is sorted or counted here. -/
def verifyFastBlumArray (online offline : Array MemOp) (perm : Array Nat) : Bool :=
  online.size == offline.size &&
    (online.foldlM clkStep none).isSome &&
    (offline.foldlM offStep none).isSome &&
    (offline.foldlM (permStep online perm) 0).isSome

theorem clkStep_eq_some {prev st' : Option UInt64} {op : MemOp} (h : clkStep prev op = some st') :
    st' = some op.clk ∧ ∀ c, prev = some c → c.toNat < op.clk.toNat := by
  cases prev with
  | none =>
    simp only [clkStep, Option.some.injEq] at h
    exact ⟨h.symm, fun c hc => by cases hc⟩
  | some c0 =>
    simp only [clkStep] at h
    by_cases hlt : c0 < op.clk
    · simp only [hlt, ↓reduceIte, Option.some.injEq] at h
      refine ⟨h.symm, fun c hc => ?_⟩
      cases hc
      exact UInt64.lt_iff_toNat_lt.1 hlt
    · simp [hlt] at h

theorem clkScan_sorted : ∀ (l : List MemOp) (prev st' : Option UInt64),
    List.foldlM clkStep prev l = some st' →
      (∀ c, prev = some c → ∀ op, op ∈ l → c.toNat < op.clk.toNat) ∧ l.Pairwise clkLt
  | [], _, _, _ => ⟨fun _ _ _ hop => (by cases hop), List.Pairwise.nil⟩
  | op :: rest, prev, st', h => by
    obtain ⟨st1, h1, h2⟩ := (foldlM_cons_some _ _ _ _ _).1 h
    obtain ⟨rfl, hprev⟩ := clkStep_eq_some h1
    obtain ⟨ih1, ih2⟩ := clkScan_sorted rest _ _ h2
    refine ⟨fun c hc o ho => ?_, List.pairwise_cons.2 ⟨fun o ho => ih1 op.clk rfl o ho, ih2⟩⟩
    rcases List.mem_cons.1 ho with e | ho'
    · rw [e]; exact hprev c hc
    · exact Nat.lt_trans (hprev c hc) (ih1 op.clk rfl o ho')

theorem offOrder_some {c : Cursor} {op : MemOp} (h : offOrder (some c) op = true) :
    keyLt c.addr c.clk op := by
  simp only [offOrder, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

theorem offStep_eq_some {st st' : Option Cursor} {op : MemOp} (h : offStep st op = some st') :
    offOrder st op = true ∧ offReadOk (Cursor.cur st op.addr) op = true ∧
      st' = some ⟨op.addr, op.clk, if op.isWrite then op.val else Cursor.cur st op.addr⟩ := by
  unfold offStep at h
  by_cases hc : (offOrder st op && offReadOk (Cursor.cur st op.addr) op) = true
  · simp only [hc, ↓reduceIte, Option.some.injEq] at h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hc.1, hc.2, h.symm⟩
  · simp [hc] at h

theorem offScan_sorted : ∀ (l : List MemOp) (st st' : Option Cursor),
    List.foldlM offStep st l = some st' →
      (∀ c, st = some c → ∀ op, op ∈ l → keyLt c.addr c.clk op) ∧ l.Pairwise lexLt
  | [], _, _, _ => ⟨fun _ _ _ hop => (by cases hop), List.Pairwise.nil⟩
  | op :: rest, st, st', h => by
    obtain ⟨st1, h1, h2⟩ := (foldlM_cons_some _ _ _ _ _).1 h
    obtain ⟨hord, _, rfl⟩ := offStep_eq_some h1
    obtain ⟨ih1, ih2⟩ := offScan_sorted rest _ _ h2
    have hop : ∀ o, o ∈ rest → lexLt op o := fun o ho => ih1 _ rfl o ho
    refine ⟨fun c hc o ho => ?_, List.pairwise_cons.2 ⟨hop, ih2⟩⟩
    subst hc
    rcases List.mem_cons.1 ho with e | ho'
    · rw [e]; exact offOrder_some hord
    · exact keyLt_trans (offOrder_some hord) (hop o ho')

/-- Past a row at another address, the sorted remainder holds nothing at `a` when `(a, c)` was
already below that row. -/
theorem atAddr_eq_nil_of_keyLt {a c : UInt64} {op : MemOp} {rest : List MemOp} (ha : op.addr ≠ a)
    (k : keyLt a c op) (hge : ∀ o, o ∈ rest → lexLt op o) : atAddr a rest = [] := by
  unfold atAddr
  apply List.filter_eq_nil_iff.2
  intro o ho hoa
  have hoa' : o.addr = a := by simpa using hoa
  rcases k with k1 | ⟨k1, _⟩
  · rcases hge o ho with k2 | ⟨k2, _⟩
    · rw [hoa'] at k2
      omega
    · exact ha (k2.trans hoa')
  · exact ha k1.symm

/-- The offline pass replays every address's subtrace from zero. -/
theorem offScan_cellRun : ∀ (l : List MemOp) (st st' : Option Cursor),
    List.foldlM offStep st l = some st' → ∀ a, cellRun (Cursor.cur st a) (atAddr a l) = true
  | [], _, _, _ => fun _ => rfl
  | op :: rest, st, st', h => by
    obtain ⟨st1, h1, h2⟩ := (foldlM_cons_some _ _ _ _ _).1 h
    obtain ⟨hord, hread, rfl⟩ := offStep_eq_some h1
    have ih := offScan_cellRun rest _ _ h2
    have hge : ∀ o, o ∈ rest → lexLt op o := fun o ho => (offScan_sorted rest _ _ h2).1 _ rfl o ho
    intro a
    by_cases ha : op.addr = a
    · subst ha
      have ihA := ih op.addr
      rw [Cursor.cur_some_same] at ihA
      rw [atAddr_cons_same]
      cases hw : op.isWrite
      · simp only [hw, Bool.false_eq_true, ↓reduceIte] at ihA
        rw [cellRun_cons_read _ _ hw, offReadOk_read hw hread, ihA]
        rfl
      · simp only [hw, ↓reduceIte] at ihA
        rw [cellRun_cons_write _ _ hw]
        exact ihA
    · rw [atAddr_cons_ne ha]
      have ihA := ih a
      rw [Cursor.cur_some_ne _ _ ha] at ihA
      cases st with
      | none => exact ihA
      | some c =>
        by_cases hc : c.addr = a
        · have k := offOrder_some hord
          rw [hc] at k
          rw [atAddr_eq_nil_of_keyLt ha k hge]
          rfl
        · have hz : Cursor.cur (some c) a = 0 := by simp [Cursor.cur, hc]
          rw [hz]
          exact ihA

theorem permStep_mem {online : Array MemOp} {perm : Array Nat} {i i' : Nat} {op : MemOp}
    (h : permStep online perm i op = some i') : op ∈ online.toList := by
  unfold permStep at h
  cases hj : perm[i]? with
  | none => simp [hj] at h
  | some j =>
    simp only [hj] at h
    by_cases ho : online[j]? = some op
    · exact Array.mem_def.1 (Array.mem_of_getElem? ho)
    · simp [ho] at h

theorem permScan_mem (online : Array MemOp) (perm : Array Nat) : ∀ (l : List MemOp) (i i' : Nat),
    List.foldlM (permStep online perm) i l = some i' → ∀ op, op ∈ l → op ∈ online.toList
  | [], _, _, _ => fun _ hop => by cases hop
  | x :: rest, i, i', h => by
    obtain ⟨i1, h1, h2⟩ := (foldlM_cons_some _ _ _ _ _).1 h
    intro op hop
    rcases List.mem_cons.1 hop with e | hop'
    · rw [e]; exact permStep_mem h1
    · exact permScan_mem online perm rest _ _ h2 op hop'

/-- What the three passes establish together: both arrays strictly sorted in their orders, the
offline subtraces replaying from zero, and the two arrays having the same rows. -/
theorem verifyFastBlumArray_facts (online offline : Array MemOp) (perm : Array Nat)
    (h : verifyFastBlumArray online offline perm = true) :
    online.toList.Pairwise clkLt ∧ offline.toList.Pairwise lexLt ∧
      (∀ a, cellRun 0 (atAddr a offline.toList) = true) ∧
      (∀ x, x ∈ online.toList ↔ x ∈ offline.toList) := by
  unfold verifyFastBlumArray at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨hsize, ⟨c1, hclk⟩⟩, ⟨c2, hoff⟩⟩, ⟨c3, hperm⟩⟩ := h
  rw [← Array.foldlM_toList] at hclk hoff hperm
  have hOff := (offScan_sorted _ _ _ hoff).2
  have hSub : ∀ x, x ∈ offline.toList → x ∈ online.toList := permScan_mem online perm _ _ _ hperm
  have hNodup : offline.toList.Nodup :=
    hOff.imp (fun {a b} hlt e => by subst e; exact lexLt_irrefl a hlt)
  have hSup : ∀ y, y ∈ online.toList → y ∈ offline.toList :=
    subset_of_nodup_of_length_le _ _ hNodup hSub (by simp [hsize])
  exact ⟨(clkScan_sorted _ _ _ hclk).2, hOff, fun a => offScan_cellRun _ _ _ hoff a,
    fun x => ⟨hSup x, hSub x⟩⟩

/-- Two traces with the same rows, one sorted by clock and one by `(addr, clk)`, have the same
subtrace at every address. -/
theorem atAddr_eq_of_sorted {on off : List MemOp} (hOn : on.Pairwise clkLt)
    (hOff : off.Pairwise lexLt) (hmem : ∀ x, x ∈ on ↔ x ∈ off) (a : UInt64) :
    atAddr a on = atAddr a off := by
  have hOffA : (atAddr a off).Pairwise clkLt := by
    refine List.Pairwise.imp_of_mem ?_ (hOff.filter _)
    intro x y hx hy hlt
    have hxa : x.addr = a := by simpa using (List.mem_filter.1 hx).2
    have hya : y.addr = a := by simpa using (List.mem_filter.1 hy).2
    rcases hlt with k | ⟨_, k⟩
    · rw [hxa, hya] at k
      omega
    · exact k
  refine eq_of_pairwise_of_mem_iff (R := clkLt) (fun x => Nat.lt_irrefl _)
    (fun x y h₁ h₂ => Nat.lt_asymm h₁ h₂) _ _ (hOn.filter _) hOffA ?_
  intro x
  simp only [atAddr, List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hmem x).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(hmem x).2 h1, h2⟩

/-- **Soundness of the offline memory checker.** An accepted online trace is a correct run of an
extensional RAM started at zero. -/
theorem verifyFastBlumArray_sound (online offline : Array MemOp) (perm : Array Nat)
    (h : verifyFastBlumArray online offline perm = true) :
    ∃ ram : ExtRam, OnlineMatchesExtRam online ram := by
  obtain ⟨hOn, hOff, hCells, hmem⟩ := verifyFastBlumArray_facts online offline perm h
  have hSome : (execRamFrom zeroRam online.toList).isSome = true :=
    (execRamFrom_isSome_iff _ _).2 fun a => by
      rw [atAddr_eq_of_sorted hOn hOff hmem a]
      exact hCells a
  obtain ⟨ram, hram⟩ := Option.isSome_iff_exists.1 hSome
  exact ⟨ram, hram⟩

/-- Soundness, read by read: in an accepted trace every read returns the value of the latest
earlier write to its address, or zero if there is none. -/
theorem verifyFastBlumArray_reads_last_write (online offline : Array MemOp) (perm : Array Nat)
    (h : verifyFastBlumArray online offline perm = true) (pre post : List MemOp) (r : MemOp)
    (hsplit : online.toList = pre ++ r :: post) (hr : r.isWrite = false) :
    r.val = ramAfter zeroRam pre r.addr := by
  obtain ⟨ram, hram⟩ := verifyFastBlumArray_sound online offline perm h
  exact ((execRamFrom_eq_some_iff _ _ _).1 hram).2 pre r post hsplit hr

/-! ## 4. Completeness: the witness an honest prover computes -/

theorem clkScan_complete : ∀ (l : List MemOp) (prev : Option UInt64), l.Pairwise clkLt →
    (∀ c, prev = some c → ∀ op, op ∈ l → c.toNat < op.clk.toNat) →
    ∃ st', List.foldlM clkStep prev l = some st'
  | [], prev, _, _ => ⟨prev, rfl⟩
  | op :: rest, prev, hp, hprev => by
    obtain ⟨hop, hrest⟩ := List.pairwise_cons.1 hp
    have hstep : clkStep prev op = some (some op.clk) := by
      cases prev with
      | none => rfl
      | some c =>
        have hlt : c < op.clk :=
          UInt64.lt_iff_toNat_lt.2 (hprev c rfl op (List.mem_cons.2 (.inl rfl)))
        simp [clkStep, hlt]
    obtain ⟨st', h'⟩ := clkScan_complete rest (some op.clk) hrest
      (fun c hc o ho => by cases hc; exact hop o ho)
    exact ⟨st', (foldlM_cons_some _ _ _ _ _).2 ⟨_, hstep, h'⟩⟩

theorem offOrder_of_keyLt {c : Cursor} {op : MemOp} (h : keyLt c.addr c.clk op) :
    offOrder (some c) op = true := by
  simp only [offOrder, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact h

/-- The offline pass accepts every strictly sorted transcript whose per-address subtraces replay. -/
theorem offScan_complete : ∀ (l : List MemOp) (st : Option Cursor), l.Pairwise lexLt →
    (∀ c, st = some c → ∀ op, op ∈ l → keyLt c.addr c.clk op) →
    (∀ a, cellRun (Cursor.cur st a) (atAddr a l) = true) →
    ∃ st', List.foldlM offStep st l = some st'
  | [], st, _, _, _ => ⟨st, rfl⟩
  | op :: rest, st, hp, hst, hcell => by
    obtain ⟨hop, hrest⟩ := List.pairwise_cons.1 hp
    have hc := hcell op.addr
    rw [atAddr_cons_same] at hc
    have hord : offOrder st op = true := by
      cases st with
      | none => rfl
      | some c => exact offOrder_of_keyLt (hst c rfl op (List.mem_cons.2 (.inl rfl)))
    have hread : offReadOk (Cursor.cur st op.addr) op = true := by
      cases hw : op.isWrite
      · rw [cellRun_cons_read _ _ hw] at hc
        simp only [Bool.and_eq_true] at hc
        simp only [offReadOk, hw, Bool.false_or]
        exact hc.1
      · simp [offReadOk, hw]
    have hstep : offStep st op = some (some
        ⟨op.addr, op.clk, if op.isWrite then op.val else Cursor.cur st op.addr⟩) := by
      simp [offStep, hord, hread]
    have hcell' : ∀ a, cellRun (Cursor.cur (some
        ⟨op.addr, op.clk, if op.isWrite then op.val else Cursor.cur st op.addr⟩) a)
        (atAddr a rest) = true := by
      intro a
      by_cases ha : op.addr = a
      · subst ha
        rw [Cursor.cur_some_same]
        cases hw : op.isWrite
        · rw [cellRun_cons_read _ _ hw] at hc
          simp only [Bool.and_eq_true] at hc
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hc.2
        · rw [cellRun_cons_write _ _ hw] at hc
          simp only [↓reduceIte]
          exact hc
      · rw [Cursor.cur_some_ne _ _ ha]
        have h := hcell a
        rw [atAddr_cons_ne ha] at h
        cases st with
        | none => exact h
        | some c =>
          by_cases hca : c.addr = a
          · have k := hst c rfl op (List.mem_cons.2 (.inl rfl))
            rw [hca] at k
            rw [atAddr_eq_nil_of_keyLt ha k hop]
            rfl
          · have hz : Cursor.cur (some c) a = 0 := by simp [Cursor.cur, hca]
            rw [hz] at h
            exact h
    obtain ⟨st', h'⟩ := offScan_complete rest _ hrest
      (fun c hc o ho => by cases hc; exact hop o ho) hcell'
    exact ⟨st', (foldlM_cons_some _ _ _ _ _).2 ⟨_, hstep, h'⟩⟩

theorem permScan_complete (online : Array MemOp) (rows : List (MemOp × Nat))
    (hrows : ∀ x, x ∈ rows → online[x.2]? = some x.1) :
    ∀ (pre suf : List (MemOp × Nat)), rows = pre ++ suf →
      ∃ i', List.foldlM (permStep online (rows.map Prod.snd).toArray) pre.length
        (suf.map Prod.fst) = some i'
  | pre, [], _ => ⟨pre.length, rfl⟩
  | pre, x :: suf, hs => by
    have hp : (rows.map Prod.snd).toArray[pre.length]? = some x.2 := by
      rw [hs]
      simp
    have ho : online[x.2]? = some x.1 := hrows x (by rw [hs]; simp)
    have hstep : permStep online (rows.map Prod.snd).toArray pre.length x.1 =
        some (pre.length + 1) := by
      simp [permStep, hp, ho]
    obtain ⟨i', h'⟩ := permScan_complete online rows hrows (pre ++ [x]) suf (by rw [hs]; simp)
    rw [List.length_append, List.length_singleton] at h'
    exact ⟨i', (foldlM_cons_some _ _ _ _ _).2 ⟨_, hstep, h'⟩⟩

/-- Non-strict `(addr, clk)` order, as the comparison the prover sorts by. -/
def opLe (x y : MemOp) : Bool :=
  decide (x.addr < y.addr) || (x.addr == y.addr && decide (x.clk ≤ y.clk))

theorem opLe_iff (x y : MemOp) :
    opLe x y = true ↔
      x.addr.toNat < y.addr.toNat ∨ (x.addr = y.addr ∧ x.clk.toNat ≤ y.clk.toNat) := by
  simp only [opLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨id, id⟩

theorem opLe_trans {x y z : MemOp} (h₁ : opLe x y = true) (h₂ : opLe y z = true) :
    opLe x z = true := by
  rw [opLe_iff] at *
  rcases h₁ with h₁ | ⟨e₁, h₁⟩
  · rcases h₂ with h₂ | ⟨e₂, _⟩
    · exact .inl (Nat.lt_trans h₁ h₂)
    · exact .inl (e₂ ▸ h₁)
  · rcases h₂ with h₂ | ⟨e₂, h₂⟩
    · exact .inl (e₁ ▸ h₂)
    · exact .inr ⟨e₁.trans e₂, Nat.le_trans h₁ h₂⟩

theorem opLe_total (x y : MemOp) : (opLe x y || opLe y x) = true := by
  rw [Bool.or_eq_true, opLe_iff, opLe_iff]
  by_cases e : x.addr = y.addr
  · rcases Nat.le_total x.clk.toNat y.clk.toNat with h | h
    · exact .inl (.inr ⟨e, h⟩)
    · exact .inr (.inr ⟨e.symm, h⟩)
  · have hne : x.addr.toNat ≠ y.addr.toNat := fun h => e (UInt64.toNat_inj.1 h)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact .inl (.inl h)
    · exact .inr (.inl h)

/-- The comparison on indexed rows: by the row, the index ignored. -/
def rowLe (x y : MemOp × Nat) : Bool := opLe x.1 y.1

theorem pairwise_mem_trichotomy {α : Type} {R : α → α → Prop} : ∀ (l : List α), l.Pairwise R →
    ∀ x y, x ∈ l → y ∈ l → x = y ∨ R x y ∨ R y x
  | [], _, _, _, hx, _ => by cases hx
  | a :: t, hp, x, y, hx, hy => by
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 hx with ex | hxt
    · rcases List.mem_cons.1 hy with ey | hyt
      · exact .inl (ex.trans ey.symm)
      · exact .inr (.inl (by rw [ex]; exact ha y hyt))
    · rcases List.mem_cons.1 hy with ey | hyt
      · exact .inr (.inr (by rw [ey]; exact ha x hxt))
      · exact pairwise_mem_trichotomy t ht x y hxt hyt

/-- The online rows with their positions, merge-sorted by `(addr, clk)`. -/
def blumRows (online : Array MemOp) : List (MemOp × Nat) :=
  online.toList.zipIdx.mergeSort rowLe

/-- The prover's side of the checker: the sorted transcript and its permutation, in
`O(n log n)` comparisons. -/
def blumWitness (online : Array MemOp) : Array MemOp × Array Nat :=
  (((blumRows online).map Prod.fst).toArray, ((blumRows online).map Prod.snd).toArray)

/-- **Completeness of the offline memory checker.** Every correct run with strictly increasing
clocks is accepted on the witness `blumWitness` computes. -/
theorem verifyFastBlumArray_complete (online : Array MemOp) (ram : ExtRam)
    (hclk : online.toList.Pairwise clkLt) (hrun : OnlineMatchesExtRam online ram) :
    verifyFastBlumArray online (blumWitness online).1 (blumWitness online).2 = true := by
  have hperm : (blumRows online).Perm online.toList.zipIdx := List.mergeSort_perm _ _
  have hoffPerm : ((blumRows online).map Prod.fst).Perm online.toList := by
    have h := hperm.map Prod.fst
    rwa [List.zipIdx_map_fst] at h
  have hmem : ∀ x, x ∈ online.toList ↔ x ∈ (blumRows online).map Prod.fst :=
    fun x => hoffPerm.mem_iff.symm
  have hle : (blumRows online).Pairwise (fun x y => rowLe x y = true) :=
    List.pairwise_mergeSort (le := rowLe)
      (fun a b c h₁ h₂ => opLe_trans (x := a.1) (y := b.1) (z := c.1) h₁ h₂)
      (fun a b => opLe_total a.1 b.1) _
  have hoffLe : ((blumRows online).map Prod.fst).Pairwise (fun x y => opLe x y = true) :=
    List.pairwise_map.2 hle
  have hOnNodup : online.toList.Nodup :=
    hclk.imp (fun {a b} hlt e => by subst e; exact Nat.lt_irrefl _ hlt)
  have hOffNodup : ((blumRows online).map Prod.fst).Nodup := hoffPerm.symm.nodup hOnNodup
  have hOffLt : ((blumRows online).map Prod.fst).Pairwise lexLt := by
    refine List.Pairwise.imp_of_mem ?_ (hoffLe.and hOffNodup)
    intro x y hx hy hxy
    obtain ⟨hle', hne⟩ := hxy
    have hclkne : x.clk.toNat ≠ y.clk.toNat := by
      rcases pairwise_mem_trichotomy _ hclk x y ((hmem x).2 hx) ((hmem y).2 hy) with e | h | h
      · exact absurd e hne
      · exact Nat.ne_of_lt h
      · exact Nat.ne_of_gt h
    rcases (opLe_iff x y).1 hle' with h | ⟨e, h⟩
    · exact .inl h
    · exact .inr ⟨e, by omega⟩
  have hCells : ∀ a, cellRun (Cursor.cur none a)
      (atAddr a ((blumRows online).map Prod.fst)) = true := by
    intro a
    have hsome : (execRamFrom zeroRam online.toList).isSome = true := by
      have h : execRamFrom zeroRam online.toList = some ram := hrun
      rw [h]
      rfl
    rw [← atAddr_eq_of_sorted hclk hOffLt hmem a]
    exact (execRamFrom_isSome_iff _ _).1 hsome a
  have hOffScan := offScan_complete _ none hOffLt (fun c hc => by cases hc) hCells
  have hrows : ∀ x, x ∈ blumRows online → online[x.2]? = some x.1 := by
    intro x hx
    have h := List.mem_zipIdx_iff_getElem?.1 (hperm.mem_iff.1 hx)
    rwa [Array.getElem?_toList] at h
  have hPermScan := permScan_complete online (blumRows online) hrows [] (blumRows online) rfl
  have hClkScan := clkScan_complete online.toList none hclk (fun c hc => by cases hc)
  have hsize : online.size = (blumWitness online).1.size := by
    simp [blumWitness, hperm.length_eq]
  unfold verifyFastBlumArray
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists]
  refine ⟨⟨⟨hsize, ?_⟩, ?_⟩, ?_⟩
  · rw [← Array.foldlM_toList]
    exact hClkScan
  · rw [← Array.foldlM_toList]
    exact hOffScan
  · rw [← Array.foldlM_toList]
    exact hPermScan

/-! ## 5. A 16-ary hash tree over cSHAKE256 -/

/-- Customization string of the tree's hash. -/
def treeCustomization : List UInt8 := "OBEND.POLIS.UMEM.TREE/v1".toUTF8.data.toList

/-- The tree's hash: cSHAKE256 under `treeCustomization`. -/
def treeHash : Hash := cshake256Bytes treeCustomization

/-- The 32-byte tag of a preimage. -/
def tagOf (pre : List UInt8) : ByteArray := cshake32ByteArray treeCustomization pre

/-- Equal 32-byte cSHAKE256 outputs come from equal inputs, or these two inputs are a collision
of that customization's hash. The collision is named: `Collision H` alone holds of every
fixed-width hash by counting, so a reduction has to say which inputs collide. -/
theorem cshake32_binds (customization : List UInt8) {p₁ p₂ : List UInt8}
    (h : cshake32ByteArray customization p₁ = cshake32ByteArray customization p₂) :
    p₁ = p₂ ∨ CollisionAmong (cshake256Bytes customization) (fun x => x = p₁ ∨ x = p₂) := by
  by_cases hp : p₁ = p₂
  · exact .inl hp
  · right
    have hl : (cshake32ByteArray customization p₁).data.toList =
        (cshake32ByteArray customization p₂).data.toList := congrArg (fun b => b.data.toList) h
    simp only [cshake32ByteArray, Native.bytesOfList_toList] at hl
    exact ⟨p₁, p₂, .inl rfl, .inr rfl, hp, congrArg ofBE hl⟩

/-- Equal tags come from equal preimages, or the pair is a collision. -/
theorem tagOf_binds {p₁ p₂ : List UInt8} (h : tagOf p₁ = tagOf p₂) :
    p₁ = p₂ ∨ CollisionAmong treeHash (fun x => x = p₁ ∨ x = p₂) :=
  cshake32_binds treeCustomization h

theorem leb128_length_pos (n : Nat) : 0 < (leb128 n).length := by
  unfold leb128
  cases n with
  | zero => simp [leb128Aux]
  | succ k =>
    simp only [leb128Aux]
    split <;> simp

/-- A list of byte strings, each length-prefixed. -/
def encodeFields (fs : List (List UInt8)) : List UInt8 := fs.flatMap encodeListField

theorem encodeFields_injective : ∀ (fs₁ fs₂ : List (List UInt8)),
    encodeFields fs₁ = encodeFields fs₂ → fs₁ = fs₂
  | [], [], _ => rfl
  | [], b :: bs, h => by
    have hlen : (encodeFields (b :: bs)).length = 0 := by rw [← h]; rfl
    have hpos := leb128_length_pos b.length
    simp only [encodeFields, List.flatMap_cons, encodeListField, List.length_append] at hlen
    omega
  | a :: as, [], h => by
    have hlen : (encodeFields (a :: as)).length = 0 := by rw [h]; rfl
    have hpos := leb128_length_pos a.length
    simp only [encodeFields, List.flatMap_cons, encodeListField, List.length_append] at hlen
    omega
  | a :: as, b :: bs, h => by
    simp only [encodeFields, List.flatMap_cons] at h
    obtain ⟨hab, hrest⟩ := encodeListField_prefix_inj h
    rw [hab, encodeFields_injective as bs hrest]

theorem map_toList_injective : ∀ (l₁ l₂ : List ByteArray),
    l₁.map (fun b => b.data.toList) = l₂.map (fun b => b.data.toList) → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [byteArray_eq_of_toList_eq h.1, map_toList_injective as bs h.2]

/-- Preimage of a leaf holding `val`. The address is bound by the leaf's position, not its bytes. -/
def leafPreimage (val : UInt64) : List UInt8 := 0 :: be 8 val.toNat

/-- Preimage of an inner node over its children's tags. -/
def nodePreimage (children : List ByteArray) : List UInt8 :=
  1 :: encodeFields (children.map fun b => b.data.toList)

/-- The tag of a leaf. -/
def leafTag (val : UInt64) : ByteArray := tagOf (leafPreimage val)

/-- The tag of an inner node. -/
def nodeTag (children : List ByteArray) : ByteArray := tagOf (nodePreimage children)

theorem leafTag_binds {v₁ v₂ : UInt64} (h : leafTag v₁ = leafTag v₂) :
    v₁ = v₂ ∨ CollisionAmong treeHash (fun x => x = leafPreimage v₁ ∨ x = leafPreimage v₂) := by
  rcases tagOf_binds h with hp | hc
  · left
    simp only [leafPreimage, List.cons.injEq, true_and] at hp
    have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
    exact UInt64.toNat_inj.1
      (be_injective (h8 ▸ v₁.toNat_lt) (h8 ▸ v₂.toNat_lt) hp)
  · exact .inr hc

theorem nodeTag_binds {c₁ c₂ : List ByteArray} (h : nodeTag c₁ = nodeTag c₂) :
    c₁ = c₂ ∨ CollisionAmong treeHash (fun x => x = nodePreimage c₁ ∨ x = nodePreimage c₂) := by
  rcases tagOf_binds h with hp | hc
  · left
    simp only [nodePreimage, List.cons.injEq, true_and] at hp
    exact map_toList_injective _ _ (encodeFields_injective _ _ hp)
  · exact .inr hc

/-- An inner node: exactly sixteen child tags. -/
structure Arity16Node where
  children : Array ByteArray
  arity : children.size = 16

/-- The 256-bit tag of a node, through cSHAKE256. -/
def Arity16Node.verkleTag256 (n : Arity16Node) : ByteArray := nodeTag n.children.toList

/-- The nibble of `addr` that selects the child at level `lvl` (level 0 is next to the leaves). -/
def nibbleAt (addr : UInt64) (lvl : Nat) : Nat := addr.toNat / 16 ^ lvl % 16

/-- The children of a node: the fifteen siblings with the running tag at position `n`. -/
def insertAt (n : Nat) (cur : ByteArray) (sibs : List ByteArray) : List ByteArray :=
  sibs.take n ++ cur :: sibs.drop n

theorem insertAt_inj {n : Nat} {c₁ c₂ : ByteArray} {s₁ s₂ : List ByteArray}
    (hlen : s₁.length = s₂.length) (h : insertAt n c₁ s₁ = insertAt n c₂ s₂) :
    c₁ = c₂ ∧ s₁ = s₂ := by
  unfold insertAt at h
  obtain ⟨ht, hd⟩ := List.append_inj h (by simp [hlen])
  simp only [List.cons.injEq] at hd
  refine ⟨hd.1, ?_⟩
  rw [← List.take_append_drop n s₁, ← List.take_append_drop n s₂, ht, hd.2]

/-- One level of an opening. The state is the level and the running tag. -/
def climbStep (addr : UInt64) (st : Nat × ByteArray) (sibs : Array ByteArray) :
    Option (Nat × ByteArray) :=
  if sibs.size = 15 then
    some (st.1 + 1, nodeTag (insertAt (nibbleAt addr st.1) st.2 sibs.toList))
  else none

/-- Fold a path from a leaf tag towards the root. -/
def climb (addr : UInt64) (leaf : ByteArray) (path : Array (Array ByteArray)) :
    Option (Nat × ByteArray) :=
  path.foldlM (climbStep addr) (0, leaf)

/-- Verify that `addr` holds `val` under `root`: sixteen levels of fifteen siblings each. -/
def verifyOpening (root : ByteArray) (addr val : UInt64)
    (path : Array (Array ByteArray)) : Bool :=
  path.size == 16 &&
    match climb addr (leafTag val) path with
    | some st => decide (st.2 = root)
    | none => false

/-- Verify a write: the same siblings open the old value under the old root and the new value
under the new root. -/
def verifyUpdate (oldRoot newRoot : ByteArray) (addr oldVal newVal : UInt64)
    (path : Array (Array ByteArray)) : Bool :=
  verifyOpening oldRoot addr oldVal path && verifyOpening newRoot addr newVal path

theorem verifyOpening_iff (root : ByteArray) (addr val : UInt64) (path : Array (Array ByteArray)) :
    verifyOpening root addr val path = true ↔
      path.size = 16 ∧ ∃ n, climb addr (leafTag val) path = some (n, root) := by
  unfold verifyOpening
  cases hc : climb addr (leafTag val) path with
  | none => simp
  | some st =>
    obtain ⟨n, r⟩ := st
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, n, rfl, h2⟩
    · rintro ⟨h1, n', _, h2⟩
      exact ⟨h1, h2⟩

theorem climbStep_eq_some {addr : UInt64} {st st' : Nat × ByteArray} {sibs : Array ByteArray}
    (h : climbStep addr st sibs = some st') :
    sibs.size = 15 ∧ st' = (st.1 + 1, nodeTag (insertAt (nibbleAt addr st.1) st.2 sibs.toList)) := by
  unfold climbStep at h
  by_cases hsz : sibs.size = 15
  · simp only [hsz, ↓reduceIte, Option.some.injEq] at h
    exact ⟨hsz, h.symm⟩
  · simp [hsz] at h

/-- The node preimages a climb hashes, level by level. -/
def climbHashed (addr : UInt64) :
    Nat → ByteArray → List (Array ByteArray) → List UInt8 → Prop
  | _, _, [], _ => False
  | lvl, c, s :: t, x =>
    x = nodePreimage (insertAt (nibbleAt addr lvl) c s.toList) ∨
      climbHashed addr (lvl + 1) (nodeTag (insertAt (nibbleAt addr lvl) c s.toList)) t x

/-- Everything an opening hashes: its leaf preimage and the node preimages of its climb. -/
def OpeningHashed (addr val : UInt64) (path : Array (Array ByteArray))
    (x : List UInt8) : Prop :=
  x = leafPreimage val ∨ climbHashed addr 0 (leafTag val) path.toList x

/-- Two climbs of the same length that meet at the same tag started from the same tag along the
same siblings, or two of the node preimages they hashed collide. -/
theorem climb_binds (addr : UInt64) : ∀ (p₁ p₂ : List (Array ByteArray)) (lvl : Nat)
    (c₁ c₂ : ByteArray) (out₁ out₂ : Nat × ByteArray), p₁.length = p₂.length →
    List.foldlM (climbStep addr) (lvl, c₁) p₁ = some out₁ →
    List.foldlM (climbStep addr) (lvl, c₂) p₂ = some out₂ → out₁.2 = out₂.2 →
    (c₁ = c₂ ∧ p₁ = p₂) ∨
      CollisionAmong treeHash
        (fun x => climbHashed addr lvl c₁ p₁ x ∨ climbHashed addr lvl c₂ p₂ x)
  | [], [], lvl, c₁, c₂, out₁, out₂, _, h₁, h₂, hout => by
    have e₁ : some (lvl, c₁) = some out₁ := h₁
    have e₂ : some (lvl, c₂) = some out₂ := h₂
    cases e₁
    cases e₂
    exact .inl ⟨hout, rfl⟩
  | [], _ :: _, _, _, _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, hlen, _, _, _ => by simp at hlen
  | s₁ :: t₁, s₂ :: t₂, lvl, c₁, c₂, out₁, out₂, hlen, h₁, h₂, hout => by
    obtain ⟨st₁, hs₁, hr₁⟩ := (foldlM_cons_some _ _ _ _ _).1 h₁
    obtain ⟨st₂, hs₂, hr₂⟩ := (foldlM_cons_some _ _ _ _ _).1 h₂
    obtain ⟨hz₁, rfl⟩ := climbStep_eq_some hs₁
    obtain ⟨hz₂, rfl⟩ := climbStep_eq_some hs₂
    have hlen' : t₁.length = t₂.length := by simpa using hlen
    rcases climb_binds addr t₁ t₂ (lvl + 1) _ _ out₁ out₂ hlen' hr₁ hr₂ hout with ⟨htag, ht⟩ | hc
    · rcases nodeTag_binds htag with hch | hc
      · obtain ⟨hcur, hsib⟩ := insertAt_inj (by simp [hz₁, hz₂]) hch
        exact .inl ⟨hcur, by rw [Array.toList_inj.1 hsib, ht]⟩
      · exact .inr (hc.mono fun x hx =>
          hx.elim (fun e => Or.inl (Or.inl e)) (fun e => Or.inr (Or.inl e)))
    · exact .inr (hc.mono fun x hx =>
        hx.elim (fun e => Or.inl (Or.inr e)) (fun e => Or.inr (Or.inr e)))

/-- **Opening binding.** Two accepted openings of one address under one root agree on the value
and on every sibling, or two of the preimages those openings hashed are a collision of the
tree's hash. -/
theorem verifyOpening_binds {root : ByteArray} {addr v₁ v₂ : UInt64}
    {p₁ p₂ : Array (Array ByteArray)} (h₁ : verifyOpening root addr v₁ p₁ = true)
    (h₂ : verifyOpening root addr v₂ p₂ = true) :
    (v₁ = v₂ ∧ p₁ = p₂) ∨
      CollisionAmong treeHash
        (fun x => OpeningHashed addr v₁ p₁ x ∨ OpeningHashed addr v₂ p₂ x) := by
  obtain ⟨hz₁, n₁, hc₁⟩ := (verifyOpening_iff root addr v₁ p₁).1 h₁
  obtain ⟨hz₂, n₂, hc₂⟩ := (verifyOpening_iff root addr v₂ p₂).1 h₂
  unfold climb at hc₁ hc₂
  rw [← Array.foldlM_toList] at hc₁ hc₂
  rcases climb_binds addr p₁.toList p₂.toList 0 _ _ _ _ (by simp [hz₁, hz₂]) hc₁ hc₂ rfl with
    ⟨hleaf, hp⟩ | hc
  · rcases leafTag_binds hleaf with hv | hc
    · exact .inl ⟨hv, Array.toList_inj.1 hp⟩
    · exact .inr (hc.mono fun x hx =>
        hx.elim (fun e => Or.inl (Or.inl e)) (fun e => Or.inr (Or.inl e)))
  · exact .inr (hc.mono fun x hx =>
      hx.elim (fun e => Or.inl (Or.inr e)) (fun e => Or.inr (Or.inr e)))

/-- **Update binding.** Two accepted updates of one address from one old root to the same new
value agree on the old value and on the new root, or two of the preimages their old-root
openings hashed collide. -/
theorem verifyUpdate_binds {oldRoot new₁ new₂ : ByteArray} {addr old₁ old₂ newVal : UInt64}
    {p₁ p₂ : Array (Array ByteArray)}
    (h₁ : verifyUpdate oldRoot new₁ addr old₁ newVal p₁ = true)
    (h₂ : verifyUpdate oldRoot new₂ addr old₂ newVal p₂ = true) :
    (old₁ = old₂ ∧ new₁ = new₂) ∨
      CollisionAmong treeHash
        (fun x => OpeningHashed addr old₁ p₁ x ∨ OpeningHashed addr old₂ p₂ x) := by
  simp only [verifyUpdate, Bool.and_eq_true] at h₁ h₂
  rcases verifyOpening_binds (root := oldRoot) h₁.1 h₂.1 with ⟨hv, hp⟩ | hc
  · left
    refine ⟨hv, ?_⟩
    obtain ⟨_, n₁, hc₁⟩ := (verifyOpening_iff new₁ addr newVal p₁).1 h₁.2
    obtain ⟨_, n₂, hc₂⟩ := (verifyOpening_iff new₂ addr newVal p₂).1 h₂.2
    rw [hp, hc₂] at hc₁
    simp only [Option.some.injEq, Prod.mk.injEq] at hc₁
    exact hc₁.2.symm
  · exact .inr hc

/-! ## 6. The prover's side of the tree: a sparse memory and its openings

These compute a root and openings for a memory given as rows. They are not part of what a verifier
trusts, and this module proves nothing about them: that `sparseOpen` is accepted under `sparseRoot`
is exercised on concrete memories in `tests/metasystem/PolisZkOcapVerkleTest.lean`, not proved. -/

/-- The tags of the all-zero subtrees of heights `0` to `16`, computed once. -/
def emptyTags : Array ByteArray :=
  (List.range 16).foldl
    (fun acc _ => acc.push (nodeTag (List.replicate 16 (acc.getD (acc.size - 1) ByteArray.empty))))
    #[leafTag 0]

/-- The value a sparse memory holds at an address: the first row for it, zero if there is none. -/
def sparseGet (mem : Array (UInt64 × UInt64)) (addr : Nat) : UInt64 :=
  match mem.find? (fun e => e.1.toNat == addr) with
  | some e => e.2
  | none => 0

/-- The tag of the subtree of height `lvl` over the addresses `a` with `a / 16 ^ lvl = pfx`.
A subtree no row falls under is read from `emptyTags`, so the work is proportional to the rows,
not to the address space. -/
def sparseSubtreeTag (mem : Array (UInt64 × UInt64)) : Nat → Nat → ByteArray
  | 0, pfx => leafTag (sparseGet mem pfx)
  | l + 1, pfx =>
    if mem.any (fun e => e.1.toNat / 16 ^ (l + 1) == pfx) then
      nodeTag ((List.range 16).map fun d => sparseSubtreeTag mem l (pfx * 16 + d))
    else emptyTags.getD (l + 1) ByteArray.empty

/-- The root of a sparse memory. -/
def sparseRoot (mem : Array (UInt64 × UInt64)) : ByteArray := sparseSubtreeTag mem 16 0

/-- The opening of `addr`: at each level, the fifteen siblings of the subtree `addr` lies in. -/
def sparseOpen (mem : Array (UInt64 × UInt64)) (addr : UInt64) :
    Array (Array ByteArray) :=
  ((List.range 16).map fun lvl =>
    (((List.range 16).map fun d =>
      sparseSubtreeTag mem lvl (addr.toNat / 16 ^ (lvl + 1) * 16 + d)).eraseIdx
        (nibbleAt addr lvl)).toArray).toArray

/-- Every well-shaped path computes a root, without assuming collision resistance. -/
theorem climb_total (addr : UInt64) (path : List (Array ByteArray))
    (shape : ∀ sibs ∈ path, sibs.size = 15) (st : Nat × ByteArray) :
    ∃ out, List.foldlM (climbStep addr) st path = some out := by
  induction path generalizing st with
  | nil => exact ⟨st, rfl⟩
  | cons sibs rest ih =>
    have hs := shape sibs (by simp)
    obtain ⟨out, ho⟩ := ih (fun sib hmem => shape sib (by simp [hmem]))
      (st.1 + 1, nodeTag (insertAt (nibbleAt addr st.1) st.2 sibs.toList))
    exact ⟨out, (foldlM_cons_some _ _ _ _ _).2
      ⟨_, by simp [climbStep, hs], ho⟩⟩

/-- The 16-level child-digest verifier has accepted openings for every address and value. -/
theorem verifyOpening_inhabited (addr val : UInt64) :
    ∃ root path, path.size = 16 ∧ verifyOpening root addr val path = true := by
  let siblings : Array ByteArray := Array.replicate 15 .empty
  let path : Array (Array ByteArray) := Array.replicate 16 siblings
  have shape : ∀ sibs ∈ path.toList, sibs.size = 15 := by
    simp [path, siblings]
  obtain ⟨out, ho⟩ := climb_total addr path.toList shape (0, leafTag val)
  have hc : climb addr (leafTag val) path = some out := by
    simpa only [climb, Array.foldlM_toList] using ho
  refine ⟨out.2, path, by simp [path], (verifyOpening_iff _ _ _ _).2 ?_⟩
  exact ⟨by simp [path], out.1, hc⟩

end Obend.Polis

/-
# Obend.Trailblaze.PolisBlum — Verified Blum-Checked `UMem` (`O(N)` `Array` Fast Path & `O(N log N)` Merge-Sort)

Implements Organ O3's offline-permuted `UMem` memory verification subsystem (`FOCS 1991`), separated
into its own `< 1,500`-line `LAW-M1` module and re-exported by `Obend.Trailblaze.Polis`:
1. **Single-Pass `O(N)` `Array MemOp` Execution Checkers (`Spec ↔ Exec`)**:
   - `checkChronologicalLogExec`, `checkAddrTimeSortedExec`, and `checkLocalReadWriteConsistencyExec`
     proved identical to their inductive `List MemOp` specifications via `Array.foldl_toList`.
2. **`O(N log N)` `(addr, timestamp)` Merge-Sort (`sortMemOpsByAddrTime`) & `verifyBlumMemoryFast`**:
   - Replaces $O(N^2)$ `countMemOp` bag scanning with `sortMemOpsByAddrTime online.toList == offline.toList`,
     proving `List.Perm`, exact per-operation multiplicity preservation (`sortMemOpsByAddrTime_eq_implies_perm_and_counts`),
     and bidirectional equivalence `verifyBlumMemoryFast_eq_verifyBlumMemory`.
3. **Unconditional Read/Write RAM Completeness & Cross-Turn Chronological Composition**:
   - Proves `blumPermutationComplete` for **all** valid chronological read/write RAM traces
     (`checkValidOnlineRamLog online = true`, supporting uninitialized `0#64` reads, writes,
     overwrites, and multi-address interleavings), `checkChronologicalLog_append` for persistent
     multi-turn `UMem` traces, and `#tooth`-guarded `blum_write_then_read_sound`.
-/

namespace Obend.Trailblaze.Polis
set_option autoImplicit false

/-! ## 1. Declarative `List MemOp` Blum `UMem` Specification (`Spec`) -/

/-- A single `UMem` memory operation carrying a full 256-bit content-addressed Verkle tag. -/
structure MemOp where
  addr         : Nat
  timestamp    : Nat
  isWrite      : Bool
  val          : BitVec 64
  verkleTag256 : BitVec 256
  deriving DecidableEq, Repr

/-- Strictly increasing chronological timestamps along the online execution log (`Spec`). -/
def checkChronologicalLog : List MemOp → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.timestamp < b.timestamp) && checkChronologicalLog (b :: rest)

/-- Strict lexicographic `(addr, timestamp)` order for the offline Blum transcript. -/
def addrTimeStrictLt (a b : MemOp) : Bool :=
  decide (a.addr < b.addr) || ((a.addr == b.addr) && decide (a.timestamp < b.timestamp))

/-- Reflexive lexicographic `(addr, timestamp)` order for merge-sorting. -/
def addrTimeLe (a b : MemOp) : Bool :=
  decide (a.addr < b.addr) || ((a.addr == b.addr) && decide (a.timestamp ≤ b.timestamp))

/-- Check that the offline transcript is strictly sorted by `(addr, timestamp)` (`Spec`). -/
def checkAddrTimeSorted : List MemOp → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => addrTimeStrictLt a b && checkAddrTimeSorted (b :: rest)

/-- Multiplicities of `target` inside `ops` for Blum multiset permutation verification. -/
def countMemOp (target : MemOp) (ops : List MemOp) : Nat :=
  (ops.filter (fun op => op == target)).length

/-- Declarative $O(N^2)$ bag-count permutation check (`Spec`). -/
def checkBagPermutation (online offline : List MemOp) : Bool :=
  (online.length == offline.length) &&
  online.all (fun op => countMemOp op online == countMemOp op offline) &&
  offline.all (fun op => countMemOp op online == countMemOp op offline)

/-- Single-pass local read-after-write replay over an `(addr, timestamp)`-sorted transcript:
    uninitialized reads must observe `0#64`, and subsequent reads at the same address must observe
    the most recently written 64-bit word. -/
def checkLocalRwStep (curAddr : Option Nat) (lastVal : BitVec 64) : List MemOp → Bool
  | [] => true
  | op :: rest =>
    if op.isWrite then
      checkLocalRwStep (some op.addr) op.val rest
    else
      let expected := if curAddr == some op.addr then lastVal else 0#64
      (op.val == expected) && checkLocalRwStep (some op.addr) expected rest

/-- Check local read/write memory semantics from a zeroed initial RAM state (`Spec`). -/
def checkLocalReadWriteConsistency (offline : List MemOp) : Bool :=
  checkLocalRwStep none 0#64 offline

/-- Blum's offline-permuted memory checker (`FOCS 1991` declarative `List` specification). -/
def verifyBlumMemory (onlineLog addrSortedTranscript : List MemOp) : Bool :=
  checkChronologicalLog onlineLog &&
  checkAddrTimeSorted addrSortedTranscript &&
  checkBagPermutation onlineLog addrSortedTranscript &&
  checkLocalReadWriteConsistency addrSortedTranscript

/-! ## 2. Single-Pass `O(N)` `Array MemOp` Checkers & `Spec ↔ Exec` Proofs -/

/-- Single-step accumulator for `O(N)` `Array` chronological timestamp validation. -/
def stepChrono (acc : Bool × Option Nat) (op : MemOp) : Bool × Option Nat :=
  match acc.2 with
  | none => (acc.1, some op.timestamp)
  | some prevTs => (acc.1 && decide (prevTs < op.timestamp), some op.timestamp)

/-- Single-pass `O(N)` `Array MemOp` chronological timestamp checker (`Exec`). -/
def checkChronologicalLogExec (ops : Array MemOp) : Bool :=
  (ops.foldl stepChrono (true, none)).1

private theorem foldl_stepChrono_false (xs : List MemOp) (prev : Option Nat) :
    (xs.foldl stepChrono (false, prev)).1 = false := by
  induction xs generalizing prev with
  | nil => rfl
  | cons op rest ih =>
    cases prev <;> exact ih (some op.timestamp)

private theorem foldl_stepChrono_true (xs : List MemOp) (prev : MemOp) :
    (xs.foldl stepChrono (true, some prev.timestamp)).1 = checkChronologicalLog (prev :: xs) := by
  induction xs generalizing prev with
  | nil => rfl
  | cons b rest ih =>
    dsimp only [List.foldl, stepChrono, checkChronologicalLog]
    cases hLt : decide (prev.timestamp < b.timestamp)
    · simp only [Bool.true_and, Bool.false_and]
      exact foldl_stepChrono_false rest (some b.timestamp)
    · simp only [Bool.true_and]
      exact ih b

/-- Exact `Exec = Spec` equivalence for `checkChronologicalLogExec`. -/
theorem checkChronologicalLogExec_eq_spec (ops : Array MemOp) :
    checkChronologicalLogExec ops = checkChronologicalLog ops.toList := by
  unfold checkChronologicalLogExec
  rw [← Array.foldl_toList]
  cases hList : ops.toList with
  | nil => rfl
  | cons a rest =>
    dsimp only [List.foldl, stepChrono]
    exact foldl_stepChrono_true rest a

/-- Single-step accumulator for `O(N)` `Array` `(addr, timestamp)` sortedness validation. -/
def stepAddrTimeSorted (acc : Bool × Option MemOp) (op : MemOp) : Bool × Option MemOp :=
  match acc.2 with
  | none => (acc.1, some op)
  | some prev => (acc.1 && addrTimeStrictLt prev op, some op)

/-- Single-pass `O(N)` `Array MemOp` `(addr, timestamp)` sortedness checker (`Exec`). -/
def checkAddrTimeSortedExec (ops : Array MemOp) : Bool :=
  (ops.foldl stepAddrTimeSorted (true, none)).1

private theorem foldl_stepAddrTimeSorted_false (xs : List MemOp) (prev : Option MemOp) :
    (xs.foldl stepAddrTimeSorted (false, prev)).1 = false := by
  induction xs generalizing prev with
  | nil => rfl
  | cons op rest ih =>
    cases prev <;> exact ih (some op)

private theorem foldl_stepAddrTimeSorted_true (xs : List MemOp) (prev : MemOp) :
    (xs.foldl stepAddrTimeSorted (true, some prev)).1 = checkAddrTimeSorted (prev :: xs) := by
  induction xs generalizing prev with
  | nil => rfl
  | cons b rest ih =>
    dsimp only [List.foldl, stepAddrTimeSorted, checkAddrTimeSorted]
    cases hLt : addrTimeStrictLt prev b
    · simp only [Bool.true_and, Bool.false_and]
      exact foldl_stepAddrTimeSorted_false rest (some b)
    · simp only [Bool.true_and]
      exact ih b

/-- Exact `Exec = Spec` equivalence for `checkAddrTimeSortedExec`. -/
theorem checkAddrTimeSortedExec_eq_spec (ops : Array MemOp) :
    checkAddrTimeSortedExec ops = checkAddrTimeSorted ops.toList := by
  unfold checkAddrTimeSortedExec
  rw [← Array.foldl_toList]
  cases hList : ops.toList with
  | nil => rfl
  | cons a rest =>
    dsimp only [List.foldl, stepAddrTimeSorted]
    exact foldl_stepAddrTimeSorted_true rest a

/-- Single-step accumulator for `O(N)` `Array` local read-after-write validation. -/
def stepLocalRw (acc : Bool × Option Nat × BitVec 64) (op : MemOp) :
    Bool × Option Nat × BitVec 64 :=
  if !acc.1 then
    (false, acc.2)
  else if op.isWrite then
    (true, some op.addr, op.val)
  else
    let expected := if acc.2.1 == some op.addr then acc.2.2 else 0#64
    (op.val == expected, some op.addr, expected)

/-- Single-pass `O(N)` `Array MemOp` local read-after-write consistency checker (`Exec`). -/
def checkLocalReadWriteConsistencyExec (offline : Array MemOp) : Bool :=
  (offline.foldl stepLocalRw (true, none, 0#64)).1

private theorem foldl_stepLocalRw_false (xs : List MemOp) (st : Option Nat × BitVec 64) :
    (xs.foldl stepLocalRw (false, st)).1 = false := by
  induction xs generalizing st with
  | nil => rfl
  | cons op rest ih =>
    dsimp only [List.foldl, stepLocalRw]
    exact ih st

private theorem foldl_stepLocalRw_true (xs : List MemOp) (curAddr : Option Nat) (lastVal : BitVec 64) :
    (xs.foldl stepLocalRw (true, curAddr, lastVal)).1 = checkLocalRwStep curAddr lastVal xs := by
  induction xs generalizing curAddr lastVal with
  | nil => rfl
  | cons op rest ih =>
    dsimp only [List.foldl, stepLocalRw, checkLocalRwStep]
    cases hWr : op.isWrite
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hEq : (op.val == if curAddr == some op.addr then lastVal else 0#64)
      · simp only [Bool.false_and]
        exact foldl_stepLocalRw_false rest _
      · simp only [Bool.true_and]
        exact ih (some op.addr) (if curAddr == some op.addr then lastVal else 0#64)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ih (some op.addr) op.val

/-- Exact `Exec = Spec` equivalence for `checkLocalReadWriteConsistencyExec`. -/
theorem checkLocalReadWriteConsistencyExec_eq_spec (offline : Array MemOp) :
    checkLocalReadWriteConsistencyExec offline = checkLocalReadWriteConsistency offline.toList := by
  unfold checkLocalReadWriteConsistencyExec checkLocalReadWriteConsistency
  rw [← Array.foldl_toList]
  exact foldl_stepLocalRw_true offline.toList none 0#64

/-! ## 3. `O(N log N)` Merge-Sort (`sortMemOpsByAddrTime`) & `verifyBlumMemoryFast` -/

/-- Split a `List MemOp` into alternating halves in $O(N)$. -/
def splitMemOps : List MemOp → List MemOp × List MemOp
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
    let p := splitMemOps rest
    (x :: p.1, y :: p.2)

/-- Fuel-bounded linear-time merge of two `(addr, timestamp)`-sorted `MemOp` lists. -/
def mergeMemOpsFuel : Nat → List MemOp → List MemOp → List MemOp
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    if addrTimeLe x y then
      x :: mergeMemOpsFuel fuel xs (y :: ys)
    else
      y :: mergeMemOpsFuel fuel (x :: xs) ys

/-- Merge two `(addr, timestamp)`-sorted `MemOp` lists in $O(|xs| + |ys|)$. -/
def mergeMemOps (xs ys : List MemOp) : List MemOp :=
  mergeMemOpsFuel (xs.length + ys.length) xs ys

/-- Fuel-bounded $O(N \log N)$ merge-sort over `(addr, timestamp)`. -/
def sortMemOpsFuel : Nat → List MemOp → List MemOp
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | fuel + 1, x :: y :: rest =>
    let halves := splitMemOps (x :: y :: rest)
    mergeMemOps (sortMemOpsFuel fuel halves.1) (sortMemOpsFuel fuel halves.2)

/-- Deterministic $O(N \log N)$ `(addr, timestamp)` merge-sort for Blum `UMem` transcripts. -/
def sortMemOpsByAddrTime (online : List MemOp) : List MemOp :=
  sortMemOpsFuel online.length online

/-- Linear comparison of canonical sorted arrays; every operation field participates. -/
def checkSortedBagEqExec (a b : Array MemOp) : Bool := a == b

theorem checkSortedBagEqExec_toList (a b : Array MemOp) :
    checkSortedBagEqExec a b = (a.toList == b.toList) := by
  by_cases h : a = b
  · subst b; simp [checkSortedBagEqExec]
  · have ht : a.toList ≠ b.toList := fun he => h (Array.toList_inj.mp he)
    exact (beq_false_of_ne h).trans (beq_false_of_ne ht).symm

theorem checkSortedBagEqExec_counts (a b : Array MemOp)
    (h : checkSortedBagEqExec a b = true) :
    ∀ op, countMemOp op a.toList = countMemOp op b.toList := by
  have he : a = b := beq_iff_eq.mp h
  subst b
  intro op
  rfl

/-- Fast $O(N \log N)$ `Array MemOp` Blum memory verifier (`Exec`): replaces $O(N^2)$ `countMemOp`
    bag scanning with single-pass `Array` checks and `sortMemOpsByAddrTime online.toList == offline.toList`. -/
def verifyBlumMemoryFast (online offline : Array MemOp) : Bool :=
  checkChronologicalLogExec online &&
  checkSortedBagEqExec (sortMemOpsByAddrTime online.toList).toArray offline &&
  checkLocalReadWriteConsistencyExec offline

/-- Alias for `verifyBlumMemoryFast` (`Exec` fast path). -/
abbrev verifyBlumMemoryExec := verifyBlumMemoryFast

private theorem perm_cons_append {α : Type} (y : α) (l₁ l₂ : List α) :
    List.Perm (y :: (l₁ ++ l₂)) (l₁ ++ y :: l₂) := by
  induction l₁ with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    exact (List.Perm.swap x y (xs ++ l₂)).trans (List.Perm.cons x ih)

private theorem perm_append_right {α : Type} {l₁ r₁ : List α} (l₂ : List α)
    (h₁ : List.Perm l₁ r₁) :
    List.Perm (l₁ ++ l₂) (r₁ ++ l₂) := by
  induction h₁ with
  | nil => exact List.Perm.refl _
  | cons x _ ih => exact List.Perm.cons x ih
  | swap x y l => exact List.Perm.swap x y (l ++ l₂)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem perm_append_left {α : Type} (r₁ : List α) {l₂ r₂ : List α}
    (h₂ : List.Perm l₂ r₂) :
    List.Perm (r₁ ++ l₂) (r₁ ++ r₂) := by
  induction r₁ with
  | nil => exact h₂
  | cons x _ ih => exact List.Perm.cons x ih

private theorem perm_append_left_right {α : Type} {l₁ r₁ l₂ r₂ : List α}
    (h₁ : List.Perm l₁ r₁) (h₂ : List.Perm l₂ r₂) :
    List.Perm (l₁ ++ l₂) (r₁ ++ r₂) :=
  (perm_append_right l₂ h₁).trans (perm_append_left r₁ h₂)

private theorem perm_length_eq {α : Type} {xs ys : List α} (h : List.Perm xs ys) :
    xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem perm_mem_iff {α : Type} {xs ys : List α} (h : List.Perm xs ys) (z : α) :
    z ∈ xs ↔ z ∈ ys := by
  induction h with
  | nil => exact Iff.rfl
  | cons x _ ih => simp [ih]
  | swap x y l =>
    simp only [List.mem_cons]
    constructor
    · rintro (rfl | rfl | hz)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hz)
    · rintro (rfl | rfl | hz)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hz)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- `List.Perm` preserves `countMemOp` multiplicities for every `op : MemOp`. -/
theorem perm_countMemOp_eq {xs ys : List MemOp} (h : List.Perm xs ys) (op : MemOp) :
    countMemOp op xs = countMemOp op ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    unfold countMemOp at ih ⊢
    simp only [List.filter_cons]
    cases (x == op) <;> simp [ih]
  | swap x y l =>
    unfold countMemOp
    simp only [List.filter_cons]
    cases (x == op) <;> cases (y == op) <;> rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem splitMemOps_length (xs : List MemOp) :
    (splitMemOps xs).1.length ≤ xs.length ∧ (splitMemOps xs).2.length ≤ xs.length := by
  match xs with
  | [] => simp [splitMemOps]
  | [_] => simp [splitMemOps]
  | x :: y :: rest =>
    have ih := splitMemOps_length rest
    dsimp only [splitMemOps, List.length_cons]
    omega

private theorem splitMemOps_perm (xs : List MemOp) :
    List.Perm xs ((splitMemOps xs).1 ++ (splitMemOps xs).2) := by
  match xs with
  | [] => exact List.Perm.refl _
  | [x] => exact List.Perm.refl _
  | x :: y :: rest =>
    dsimp only [splitMemOps, List.cons_append]
    have ih := splitMemOps_perm rest
    exact List.Perm.cons x ((List.Perm.cons y ih).trans (perm_cons_append y _ _))

private theorem mergeMemOpsFuel_perm (fuel : Nat) (xs ys : List MemOp) :
    List.Perm (xs ++ ys) (mergeMemOpsFuel fuel xs ys) := by
  induction fuel generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ f ih =>
    cases xs with
    | nil => exact List.Perm.refl _
    | cons x xs' =>
      cases ys with
      | nil =>
        simp only [mergeMemOpsFuel, List.append_nil]
        exact List.Perm.refl _
      | cons y ys' =>
        dsimp only [mergeMemOpsFuel]
        cases hLe : addrTimeLe x y
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hStep := List.Perm.cons y (ih (x :: xs') ys')
          exact (perm_cons_append y (x :: xs') ys').symm.trans hStep
        · simp only [↓reduceIte]
          exact List.Perm.cons x (ih xs' (y :: ys'))

private theorem sortMemOpsFuel_perm (fuel : Nat) (xs : List MemOp) :
    List.Perm xs (sortMemOpsFuel fuel xs) := by
  induction fuel generalizing xs with
  | zero => exact List.Perm.refl _
  | succ f ih =>
    match xs with
    | [] => exact List.Perm.refl _
    | [x] => exact List.Perm.refl _
    | x :: y :: rest =>
      dsimp only [sortMemOpsFuel, mergeMemOps]
      let lhs := sortMemOpsFuel f (splitMemOps (x :: y :: rest)).1
      let rhs := sortMemOpsFuel f (splitMemOps (x :: y :: rest)).2
      have hSplit := splitMemOps_perm (x :: y :: rest)
      have hLeft := ih (splitMemOps (x :: y :: rest)).1
      have hRight := ih (splitMemOps (x :: y :: rest)).2
      have hBoth := perm_append_left_right hLeft hRight
      have hMerge := mergeMemOpsFuel_perm (lhs.length + rhs.length) lhs rhs
      exact hSplit.trans (hBoth.trans hMerge)

/-- `sortMemOpsByAddrTime online` is unconditionally a multiset permutation of `online`. -/
theorem sortMemOpsByAddrTime_perm (online : List MemOp) :
    List.Perm online (sortMemOpsByAddrTime online) :=
  sortMemOpsFuel_perm online.length online

/-- Any `List.Perm` implies `checkBagPermutation online offline = true`. -/
theorem perm_implies_checkBagPermutation {online offline : List MemOp}
    (hPerm : List.Perm online offline) :
    checkBagPermutation online offline = true := by
  unfold checkBagPermutation
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨perm_length_eq hPerm, ?_⟩, ?_⟩
  · intro op _hMem
    exact perm_countMemOp_eq hPerm op
  · intro op _hMem
    exact perm_countMemOp_eq hPerm op

/-- **Merge-Sort Permutation & Multiplicity Soundness**:
    Whenever `sortMemOpsByAddrTime online = offline`, `List.Perm online offline` holds,
    `countMemOp op online = countMemOp op offline` holds for every `op`, and `checkBagPermutation` holds. -/
theorem sortMemOpsByAddrTime_eq_implies_perm_and_counts
    (online offline : List MemOp) (op : MemOp)
    (hSort : sortMemOpsByAddrTime online = offline) :
    List.Perm online offline ∧
    countMemOp op online = countMemOp op offline ∧
    checkBagPermutation online offline = true := by
  subst hSort
  have hPerm := sortMemOpsByAddrTime_perm online
  exact ⟨hPerm, perm_countMemOp_eq hPerm op, perm_implies_checkBagPermutation hPerm⟩

/-! ## 4. Strict `(addr, timestamp)` Ordering, `Spec = Exec` Equivalence & Full Completeness -/

private theorem addrTimeStrictLt_irrefl (a : MemOp) : addrTimeStrictLt a a = false := by
  unfold addrTimeStrictLt
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_false_iff_not, beq_iff_eq]
  omega

private theorem addrTimeStrictLt_trans {a b c : MemOp}
    (hAB : addrTimeStrictLt a b = true)
    (hBC : addrTimeStrictLt b c = true) :
    addrTimeStrictLt a c = true := by
  unfold addrTimeStrictLt at hAB hBC ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hAB hBC ⊢
  omega

private theorem addrTimeStrictLt_of_le_and_ts_ne {a b : MemOp}
    (hNe : a.timestamp ≠ b.timestamp)
    (hLe : addrTimeLe a b = true) :
    addrTimeStrictLt a b = true := by
  unfold addrTimeLe at hLe
  unfold addrTimeStrictLt
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hLe ⊢
  omega

private theorem addrTimeStrictLt_of_not_le {a b : MemOp}
    (hNotLe : addrTimeLe a b = false) :
    addrTimeStrictLt b a = true := by
  unfold addrTimeLe at hNotLe
  unfold addrTimeStrictLt
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_false_iff_not, beq_iff_eq] at hNotLe
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  by_cases hEq : a.addr = b.addr
  · have hTs := hNotLe.2 hEq
    exact Or.inr ⟨hEq.symm, by omega⟩
  · have hGe := hNotLe.1
    exact Or.inl (by omega)

/-- Equivalence between `checkChronologicalLog` and pairwise strict timestamp ordering. -/
theorem checkChronologicalLog_iff_pairwise (xs : List MemOp) :
    checkChronologicalLog xs = true ↔ List.Pairwise (fun a b => a.timestamp < b.timestamp) xs := by
  induction xs with
  | nil => simp [checkChronologicalLog]
  | cons a rest ih =>
    cases rest with
    | nil => simp [checkChronologicalLog]
    | cons b tl =>
      unfold checkChronologicalLog
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [ih]
      constructor
      · rintro ⟨hAB, hTail⟩
        refine List.Pairwise.cons ?_ hTail
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzTl
        · exact hAB
        · cases hTail with
          | cons hB _ =>
            have hBz := hB z hzTl
            omega
      · intro hPw
        cases hPw with
        | cons hA hTail =>
          exact ⟨hA b (List.mem_cons_self ..), hTail⟩

private theorem pairwise_lt_append {xs ys : List MemOp}
    (hX : List.Pairwise (fun a b => a.timestamp < b.timestamp) xs)
    (hY : List.Pairwise (fun a b => a.timestamp < b.timestamp) ys)
    (hCross : ∀ x ∈ xs, ∀ y ∈ ys, x.timestamp < y.timestamp) :
    List.Pairwise (fun a b => a.timestamp < b.timestamp) (xs ++ ys) := by
  induction hX with
  | nil => exact hY
  | @cons x rest hRel _hTail ih =>
    refine List.Pairwise.cons ?_ (ih fun u hu v hv => hCross u (List.mem_cons_of_mem x hu) v hv)
    intro z hz
    rcases List.mem_append.mp hz with hzRest | hzYs
    · exact hRel z hzRest
    · exact hCross x (List.mem_cons_self ..) z hzYs

/-- Cross-turn chronological composition: concatenating two chronological `UMem` logs whose
    timestamps are separated (`∀ x ∈ xs, ∀ y ∈ ys, x.timestamp < y.timestamp`) yields a
    globally chronological log. -/
theorem checkChronologicalLog_append {xs ys : List MemOp}
    (hX : checkChronologicalLog xs = true)
    (hY : checkChronologicalLog ys = true)
    (hCross : ∀ x ∈ xs, ∀ y ∈ ys, x.timestamp < y.timestamp) :
    checkChronologicalLog (xs ++ ys) = true := by
  rw [checkChronologicalLog_iff_pairwise] at hX hY ⊢
  exact pairwise_lt_append hX hY hCross

private theorem checkAddrTimeSorted_iff_pairwise (xs : List MemOp) :
    checkAddrTimeSorted xs = true ↔ List.Pairwise (fun a b => addrTimeStrictLt a b = true) xs := by
  induction xs with
  | nil => simp [checkAddrTimeSorted]
  | cons a rest ih =>
    cases rest with
    | nil => simp [checkAddrTimeSorted]
    | cons b tl =>
      unfold checkAddrTimeSorted
      simp only [Bool.and_eq_true]
      rw [ih]
      constructor
      · rintro ⟨hAB, hTail⟩
        refine List.Pairwise.cons ?_ hTail
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzTl
        · exact hAB
        · cases hTail with
          | cons hB _ => exact addrTimeStrictLt_trans hAB (hB z hzTl)
      · intro hPw
        cases hPw with
        | cons hA hTail =>
          exact ⟨hA b (List.mem_cons_self ..), hTail⟩

private theorem nodup_timestamps_of_pairwise_lt {xs : List MemOp}
    (hPw : List.Pairwise (fun a b => a.timestamp < b.timestamp) xs) :
    List.Nodup (xs.map MemOp.timestamp) := by
  induction hPw with
  | nil => exact List.Pairwise.nil
  | @cons a rest hRel _hTail ih =>
    refine List.Pairwise.cons ?_ ih
    intro ts hTsMem hEq
    rcases List.mem_map.mp hTsMem with ⟨z, hzMem, rfl⟩
    have hLt := hRel z hzMem
    omega

private theorem perm_nodup_nat {xs ys : List Nat} (hPerm : List.Perm xs ys)
    (hNodup : List.Nodup xs) :
    List.Nodup ys := by
  induction hPerm with
  | nil => exact hNodup
  | cons x hSub ih =>
    cases hNodup with
    | cons hNotMem hTail =>
      refine List.Pairwise.cons ?_ (ih hTail)
      intro z hz hEq
      apply hNotMem z ((perm_mem_iff hSub z).mpr hz) hEq
  | swap x y l =>
    cases hNodup with
    | cons hY hRest =>
      cases hRest with
      | cons hX hL =>
        refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ hL)
        · intro z hz hEq
          rcases List.mem_cons.mp hz with rfl | hzL
          · exact hY x (List.mem_cons_self ..) hEq.symm
          · exact hX z hzL hEq
        · intro z hzL hEq
          exact hY z (List.mem_cons_of_mem x hzL) hEq
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hNodup)

private theorem perm_map_timestamp {xs ys : List MemOp} (h : List.Perm xs ys) :
    List.Perm (xs.map MemOp.timestamp) (ys.map MemOp.timestamp) := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih => exact List.Perm.cons x.timestamp ih
  | swap x y l => exact List.Perm.swap x.timestamp y.timestamp (l.map MemOp.timestamp)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem nodup_append_split {as bs : List Nat}
    (hNodup : List.Nodup (as ++ bs)) :
    List.Nodup as ∧ List.Nodup bs ∧ (∀ u ∈ as, ∀ v ∈ bs, u ≠ v) := by
  induction as with
  | nil =>
    exact ⟨List.Pairwise.nil, hNodup, fun _ hMem => nomatch hMem⟩
  | cons a as' ih =>
    cases hNodup with
    | cons hRel hTail =>
      rcases ih hTail with ⟨hNodA, hNodB, hDisj⟩
      refine ⟨List.Pairwise.cons ?_ hNodA, hNodB, ?_⟩
      · intro z hz
        exact hRel z (List.mem_append_left bs hz)
      · intro u hu v hv
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hRel v (List.mem_append_right as' hv)
        · exact hDisj u hu' v hv

private theorem mergeMemOpsFuel_sorted (fuel : Nat) (xs ys : List MemOp)
    (hFuel : xs.length + ys.length ≤ fuel)
    (hSortX : List.Pairwise (fun a b => addrTimeStrictLt a b = true) xs)
    (hSortY : List.Pairwise (fun a b => addrTimeStrictLt a b = true) ys)
    (hDisjTs : ∀ u ∈ xs, ∀ v ∈ ys, u.timestamp ≠ v.timestamp) :
    List.Pairwise (fun a b => addrTimeStrictLt a b = true) (mergeMemOpsFuel fuel xs ys) := by
  induction fuel generalizing xs ys with
  | zero =>
    cases xs with
    | nil =>
      cases ys with
      | nil => exact List.Pairwise.nil
      | cons y ys' => simp at hFuel
    | cons x xs' => simp at hFuel
  | succ f ih =>
    cases xs with
    | nil => exact hSortY
    | cons x xs' =>
      cases ys with
      | nil => exact hSortX
      | cons y ys' =>
        dsimp only [mergeMemOpsFuel]
        cases hSortX with
        | cons hRelX hTailX =>
          cases hSortY with
          | cons hRelY hTailY =>
            have hNeXY : x.timestamp ≠ y.timestamp :=
              hDisjTs x (List.mem_cons_self ..) y (List.mem_cons_self ..)
            cases hLe : addrTimeLe x y
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hYX : addrTimeStrictLt y x = true := addrTimeStrictLt_of_not_le hLe
              have hRec := ih (x :: xs') ys'
                (by dsimp only [List.length_cons] at hFuel ⊢; omega)
                (List.Pairwise.cons hRelX hTailX)
                hTailY
                (fun u hu v hv => hDisjTs u hu v (List.mem_cons_of_mem y hv))
              refine List.Pairwise.cons ?_ hRec
              intro z hz
              have hzOrig := (perm_mem_iff (mergeMemOpsFuel_perm f (x :: xs') ys') z).mpr hz
              rcases List.mem_append.mp hzOrig with hzX | hzY'
              · rcases List.mem_cons.mp hzX with rfl | hzXs'
                · exact hYX
                · exact addrTimeStrictLt_trans hYX (hRelX z hzXs')
              · exact hRelY z hzY'
            · simp only [↓reduceIte]
              have hXY : addrTimeStrictLt x y = true := addrTimeStrictLt_of_le_and_ts_ne hNeXY hLe
              have hRec := ih xs' (y :: ys')
                (by dsimp only [List.length_cons] at hFuel ⊢; omega)
                hTailX
                (List.Pairwise.cons hRelY hTailY)
                (fun u hu v hv => hDisjTs u (List.mem_cons_of_mem x hu) v hv)
              refine List.Pairwise.cons ?_ hRec
              intro z hz
              have hzOrig := (perm_mem_iff (mergeMemOpsFuel_perm f xs' (y :: ys')) z).mpr hz
              rcases List.mem_append.mp hzOrig with hzXs' | hzY
              · exact hRelX z hzXs'
              · rcases List.mem_cons.mp hzY with rfl | hzYs'
                · exact hXY
                · exact addrTimeStrictLt_trans hXY (hRelY z hzYs')

private theorem sortMemOpsFuel_sorted (fuel : Nat) (xs : List MemOp)
    (hFuel : xs.length ≤ fuel)
    (hNodupTs : List.Nodup (xs.map MemOp.timestamp)) :
    List.Pairwise (fun a b => addrTimeStrictLt a b = true) (sortMemOpsFuel fuel xs) := by
  induction fuel generalizing xs with
  | zero =>
    cases xs with
    | nil => exact List.Pairwise.nil
    | cons _ _ => simp at hFuel
  | succ f ih =>
    match xs with
    | [] => exact List.Pairwise.nil
    | [x] => exact List.Pairwise.cons (fun _ hMem => nomatch hMem) List.Pairwise.nil
    | x :: y :: rest =>
      dsimp only [sortMemOpsFuel, mergeMemOps]
      let halves := splitMemOps (x :: y :: rest)
      have hSplitLen := splitMemOps_length rest
      have hLen1 : halves.1.length ≤ f := by
        dsimp only [halves, splitMemOps, List.length_cons] at hFuel ⊢
        omega
      have hLen2 : halves.2.length ≤ f := by
        dsimp only [halves, splitMemOps, List.length_cons] at hFuel ⊢
        omega
      have hPermSplit := splitMemOps_perm (x :: y :: rest)
      have hPermTs := perm_map_timestamp hPermSplit
      rw [List.map_append] at hPermTs
      have hNodBoth := perm_nodup_nat hPermTs hNodupTs
      rcases nodup_append_split hNodBoth with ⟨hNod1, hNod2, hDisj⟩
      have hSort1 := ih halves.1 hLen1 hNod1
      have hSort2 := ih halves.2 hLen2 hNod2
      apply mergeMemOpsFuel_sorted _ _ _ (Nat.le_refl _) hSort1 hSort2
      intro u hu v hv hEqTs
      have huOrig := (perm_mem_iff (sortMemOpsFuel_perm f halves.1) u).mpr hu
      have hvOrig := (perm_mem_iff (sortMemOpsFuel_perm f halves.2) v).mpr hv
      exact hDisj u.timestamp (List.mem_map_of_mem huOrig) v.timestamp (List.mem_map_of_mem hvOrig) hEqTs

/-- Any chronological online log is sorted into strict `(addr, timestamp)` order by `sortMemOpsByAddrTime`. -/
theorem sortMemOpsByAddrTime_sorted (online : List MemOp)
    (hChrono : checkChronologicalLog online = true) :
    checkAddrTimeSorted (sortMemOpsByAddrTime online) = true := by
  rw [checkAddrTimeSorted_iff_pairwise]
  exact sortMemOpsFuel_sorted online.length online (Nat.le_refl _)
    (nodup_timestamps_of_pairwise_lt ((checkChronologicalLog_iff_pairwise online).mp hChrono))

/-- Extensionality of strictly `(addr, timestamp)`-sorted transcripts: two strictly sorted `MemOp`
    lists with the exact same elements are identical (`xs = ys`). -/
theorem sorted_eq_of_mem_iff {xs ys : List MemOp}
    (hSortX : List.Pairwise (fun a b => addrTimeStrictLt a b = true) xs)
    (hSortY : List.Pairwise (fun a b => addrTimeStrictLt a b = true) ys)
    (hMem : ∀ op : MemOp, op ∈ xs ↔ op ∈ ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys' =>
      have hInNil := (hMem y).mpr (List.mem_cons_self ..)
      cases hInNil
  | cons x xs' ih =>
    cases ys with
    | nil =>
      have hInNil := (hMem x).mp (List.mem_cons_self ..)
      cases hInNil
    | cons y ys' =>
      cases hSortX with
      | cons hRelX hTailX =>
        cases hSortY with
        | cons hRelY hTailY =>
          have hHeadEq : x = y := by
            rcases List.mem_cons.mp ((hMem x).mp (List.mem_cons_self ..)) with hxy | hxInYs
            · exact hxy
            · rcases List.mem_cons.mp ((hMem y).mpr (List.mem_cons_self ..)) with hyx | hyInXs
              · exact hyx.symm
              · have hYX := hRelY x hxInYs
                have hXY := hRelX y hyInXs
                have hXX := addrTimeStrictLt_trans hXY hYX
                rw [addrTimeStrictLt_irrefl x] at hXX
                cases hXX
          subst hHeadEq
          congr 1
          apply ih hTailX hTailY
          intro op
          constructor
          · intro hInXs'
            have hLt := hRelX op hInXs'
            have hNe : op ≠ x := by
              intro hEq
              subst hEq
              rw [addrTimeStrictLt_irrefl op] at hLt
              cases hLt
            rcases List.mem_cons.mp ((hMem op).mp (List.mem_cons_of_mem x hInXs')) with hEq | hInYs'
            · exact absurd hEq hNe
            · exact hInYs'
          · intro hInYs'
            have hLt := hRelY op hInYs'
            have hNe : op ≠ x := by
              intro hEq
              subst hEq
              rw [addrTimeStrictLt_irrefl op] at hLt
              cases hLt
            rcases List.mem_cons.mp ((hMem op).mpr (List.mem_cons_of_mem x hInYs')) with hEq | hInXs'
            · exact absurd hEq hNe
            · exact hInXs'

/-- Helper: if `target` is absent from `ops`, `countMemOp target ops = 0`. -/
theorem countMemOp_eq_zero_of_not_mem (target : MemOp) (ops : List MemOp)
    (hNotMem : target ∉ ops) :
    countMemOp target ops = 0 := by
  unfold countMemOp
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro op hIn hBeq
  rw [beq_iff_eq] at hBeq
  subst hBeq
  exact hNotMem hIn

private theorem countMemOp_pos_of_mem (target : MemOp) (ops : List MemOp)
    (hMem : target ∈ ops) :
    0 < countMemOp target ops := by
  induction ops with
  | nil => cases hMem
  | cons hd tl ih =>
    unfold countMemOp
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hMem with rfl | hTl
    · simp [List.length_cons]
    · have hPos := ih hTl
      unfold countMemOp at hPos
      cases (hd == target) <;> simp [List.length_cons] <;> omega

/-- Multiset bag-check soundness: `checkBagPermutation online offline = true` implies exact
    multiplicity equality `countMemOp op online = countMemOp op offline` for EVERY `op : MemOp`. -/
theorem checkBagPermutation_counts_eq (online offline : List MemOp) (op : MemOp)
    (hBag : checkBagPermutation online offline = true) :
    countMemOp op online = countMemOp op offline := by
  unfold checkBagPermutation at hBag
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hBag
  by_cases hInOn : op ∈ online
  · exact hBag.1.2 op hInOn
  · by_cases hInOff : op ∈ offline
    · exact hBag.2 op hInOff
    · rw [countMemOp_eq_zero_of_not_mem op online hInOn,
          countMemOp_eq_zero_of_not_mem op offline hInOff]

/-- **Bidirectional `Exec = Spec` Equivalence (`verifyBlumMemoryFast_eq_verifyBlumMemory`)**:
    The $O(N \log N)$ `Array MemOp` verifier computes the exact same `Bool` result as the
    declarative `List MemOp` specification `verifyBlumMemory` on all inputs. -/
theorem verifyBlumMemoryFast_eq_verifyBlumMemory (online offline : Array MemOp) :
    verifyBlumMemoryFast online offline = verifyBlumMemory online.toList offline.toList := by
  unfold verifyBlumMemoryFast verifyBlumMemory
  rw [checkSortedBagEqExec_toList, List.toList_toArray]
  rw [checkChronologicalLogExec_eq_spec, checkLocalReadWriteConsistencyExec_eq_spec]
  cases hChrono : checkChronologicalLog online.toList
  · rfl
  · cases hRw : checkLocalReadWriteConsistency offline.toList
    · simp only [Bool.and_false]
    · simp only [Bool.true_and, Bool.and_true]
      by_cases hEqSort : sortMemOpsByAddrTime online.toList = offline.toList
      · have hBeq : (sortMemOpsByAddrTime online.toList == offline.toList) = true :=
          beq_iff_eq.mpr hEqSort
        rw [hBeq]
        have hSorted : checkAddrTimeSorted offline.toList = true := by
          rw [← hEqSort]
          exact sortMemOpsByAddrTime_sorted online.toList hChrono
        have hBag : checkBagPermutation online.toList offline.toList = true :=
          (sortMemOpsByAddrTime_eq_implies_perm_and_counts online.toList offline.toList
            ⟨0, 0, false, 0#64, 0#256⟩ hEqSort).2.2
        rw [hSorted, hBag]
        rfl
      · have hBeq : (sortMemOpsByAddrTime online.toList == offline.toList) = false :=
          beq_false_of_ne hEqSort
        rw [hBeq]
        symm
        rw [Bool.and_eq_false_iff]
        by_cases hSortOff : checkAddrTimeSorted offline.toList = true
        · right
          cases hBag : checkBagPermutation online.toList offline.toList
          · rfl
          · exfalso
            apply hEqSort
            have hSortCanonical :=
              (checkAddrTimeSorted_iff_pairwise _).mp (sortMemOpsByAddrTime_sorted online.toList hChrono)
            have hSortOffPw := (checkAddrTimeSorted_iff_pairwise _).mp hSortOff
            apply sorted_eq_of_mem_iff hSortCanonical hSortOffPw
            intro op
            have hPerm := sortMemOpsByAddrTime_perm online.toList
            rw [← perm_mem_iff hPerm op]
            have hCntEq := checkBagPermutation_counts_eq online.toList offline.toList op hBag
            constructor
            · intro hInOn
              by_cases hInOff : op ∈ offline.toList
              · exact hInOff
              · exfalso
                have hPos := countMemOp_pos_of_mem op online.toList hInOn
                rw [hCntEq, countMemOp_eq_zero_of_not_mem op offline.toList hInOff] at hPos
                omega
            · intro hInOff
              by_cases hInOn : op ∈ online.toList
              · exact hInOn
              · exfalso
                have hPos := countMemOp_pos_of_mem op offline.toList hInOff
                rw [← hCntEq, countMemOp_eq_zero_of_not_mem op online.toList hInOn] at hPos
                omega
        · left
          exact Bool.eq_false_iff.mpr hSortOff

/-- Read 64-bit word at `addr` from sequential RAM state (defaulting to `0#64` on uninitialized addresses). -/
def readRamWord (ram : List (Nat × BitVec 64)) (addr : Nat) : BitVec 64 :=
  match ram with
  | [] => 0#64
  | (a, v) :: rest => if a == addr then v else readRamWord rest addr

/-- Sequential online RAM execution checker from state `ram`: writes update `(op.addr, op.val)`
    and reads must observe `readRamWord ram op.addr`. -/
def checkOnlineRamStep (ram : List (Nat × BitVec 64)) : List MemOp → Bool
  | [] => true
  | op :: rest =>
    if op.isWrite then
      checkOnlineRamStep ((op.addr, op.val) :: ram) rest
    else
      (op.val == readRamWord ram op.addr) && checkOnlineRamStep ram rest

/-- Valid chronological read/write online RAM execution trace starting from zeroed RAM (`[]`). -/
def checkValidOnlineRamLog (online : List MemOp) : Bool :=
  checkChronologicalLog online && checkOnlineRamStep [] online

/-- Per-address projection of a memory trace. -/
def filterAddr (a : Nat) (ops : List MemOp) : List MemOp :=
  ops.filter (fun op => op.addr == a)

/-- Single-address sequential read/write replay from `lastVal`. -/
def checkSingleAddrRw (lastVal : BitVec 64) : List MemOp → Bool
  | [] => true
  | op :: rest =>
    if op.isWrite then
      checkSingleAddrRw op.val rest
    else
      (op.val == lastVal) && checkSingleAddrRw lastVal rest

private theorem checkOnlineRamStep_filterAddr
    (a : Nat) (ram : List (Nat × BitVec 64)) (online : List MemOp)
    (hStep : checkOnlineRamStep ram online = true) :
    checkSingleAddrRw (readRamWord ram a) (filterAddr a online) = true := by
  induction online generalizing ram with
  | nil => rfl
  | cons op rest ih =>
    unfold checkOnlineRamStep at hStep
    unfold filterAddr
    simp only [List.filter_cons]
    cases hEqA : (op.addr == a)
    · have hNe : op.addr ≠ a := fun h => by rw [beq_iff_eq.mpr h] at hEqA; cases hEqA
      cases hWr : op.isWrite
      · rw [hWr] at hStep
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hStep
        exact ih ram hStep.2
      · rw [hWr] at hStep
        simp only [↓reduceIte] at hStep
        have hSub := ih ((op.addr, op.val) :: ram) hStep
        dsimp only [readRamWord] at hSub
        rw [beq_false_of_ne hNe] at hSub
        exact hSub
    · have hEq : op.addr = a := beq_iff_eq.mp hEqA
      subst hEq
      cases hWr : op.isWrite
      · rw [hWr] at hStep
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hStep
        simp only [↓reduceIte, checkSingleAddrRw, hWr, Bool.false_eq_true, Bool.and_eq_true]
        exact ⟨hStep.1, ih ram hStep.2⟩
      · rw [hWr] at hStep
        simp only [↓reduceIte] at hStep
        simp only [↓reduceIte, checkSingleAddrRw, hWr]
        have hSub := ih ((op.addr, op.val) :: ram) hStep
        dsimp only [readRamWord] at hSub
        rw [beq_self_eq_true] at hSub
        exact hSub

private theorem pairwise_filter {α : Type} {R : α → α → Prop} (p : α → Bool) {xs : List α}
    (hPw : List.Pairwise R xs) :
    List.Pairwise R (xs.filter p) := by
  induction hPw with
  | nil => exact List.Pairwise.nil
  | @cons x rest hRel _hTail ih =>
    simp only [List.filter_cons]
    cases p x
    · exact ih
    · refine List.Pairwise.cons ?_ ih
      intro z hz
      exact hRel z (List.mem_filter.mp hz).1

private theorem pairwise_ts_lt_and_same_addr {xs : List MemOp} (a : Nat)
    (hTs : List.Pairwise (fun x y => x.timestamp < y.timestamp) xs)
    (hAddr : ∀ op ∈ xs, op.addr = a) :
    List.Pairwise (fun x y => addrTimeStrictLt x y = true) xs := by
  induction hTs with
  | nil => exact List.Pairwise.nil
  | @cons x rest hRel _hTail ih =>
    refine List.Pairwise.cons ?_ (ih fun op h => hAddr op (List.mem_cons_of_mem x h))
    intro z hz
    have hxA := hAddr x (List.mem_cons_self ..)
    have hzA := hAddr z (List.mem_cons_of_mem x hz)
    have hLt := hRel z hz
    unfold addrTimeStrictLt
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact Or.inr ⟨by omega, hLt⟩

private theorem filterAddr_online_sorted (a : Nat) (online : List MemOp)
    (hChrono : checkChronologicalLog online = true) :
    List.Pairwise (fun x y => addrTimeStrictLt x y = true) (filterAddr a online) := by
  apply pairwise_ts_lt_and_same_addr a
  · exact pairwise_filter (fun op => op.addr == a) ((checkChronologicalLog_iff_pairwise online).mp hChrono)
  · intro op hMem
    unfold filterAddr at hMem
    exact beq_iff_eq.mp (List.mem_filter.mp hMem).2

private theorem filterAddr_sortMemOpsByAddrTime_eq (a : Nat) (online : List MemOp)
    (hChrono : checkChronologicalLog online = true) :
    filterAddr a (sortMemOpsByAddrTime online) = filterAddr a online := by
  have hSortOff :=
    pairwise_filter (fun op => op.addr == a)
      ((checkAddrTimeSorted_iff_pairwise _).mp (sortMemOpsByAddrTime_sorted online hChrono))
  have hSortOn := filterAddr_online_sorted a online hChrono
  apply sorted_eq_of_mem_iff hSortOff hSortOn
  intro op
  unfold filterAddr
  simp only [List.mem_filter]
  rw [perm_mem_iff (sortMemOpsByAddrTime_perm online) op]

private theorem pairwise_addr_le_of_sorted {xs : List MemOp}
    (hSort : List.Pairwise (fun x y => addrTimeStrictLt x y = true) xs) :
    List.Pairwise (fun x y => x.addr ≤ y.addr) xs := by
  induction hSort with
  | nil => exact List.Pairwise.nil
  | cons hRel _ ih =>
    refine List.Pairwise.cons ?_ ih
    intro z hz
    have hLt := hRel z hz
    unfold addrTimeStrictLt at hLt
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hLt
    omega

private theorem checkLocalRwStep_of_per_addr
    (xs : List MemOp) (curAddr : Option Nat) (lastVal : BitVec 64)
    (hAddrSorted : List.Pairwise (fun x y => x.addr ≤ y.addr) xs)
    (hInv :
      match curAddr with
      | none => ∀ a : Nat, checkSingleAddrRw 0#64 (filterAddr a xs) = true
      | some c =>
        (∀ op ∈ xs, c ≤ op.addr) ∧
        checkSingleAddrRw lastVal (filterAddr c xs) = true ∧
        (∀ a : Nat, c < a → checkSingleAddrRw 0#64 (filterAddr a xs) = true)) :
    checkLocalRwStep curAddr lastVal xs = true := by
  induction xs generalizing curAddr lastVal with
  | nil => rfl
  | cons op rest ih =>
    cases hAddrSorted with
    | cons hLeRest hTailSorted =>
      unfold checkLocalRwStep
      have hFilterSelf : filterAddr op.addr (op :: rest) = op :: filterAddr op.addr rest := by
        unfold filterAddr
        simp
      have hFilterGt : ∀ a : Nat, op.addr < a → filterAddr a (op :: rest) = filterAddr a rest := by
        intro a hGt
        unfold filterAddr
        simp only [List.filter_cons]
        have hNe : (op.addr == a) = false := beq_false_of_ne (by omega)
        rw [hNe]
        rfl
      cases curAddr with
      | none =>
        have hAtOp := hInv op.addr
        rw [hFilterSelf] at hAtOp
        unfold checkSingleAddrRw at hAtOp
        cases hWr : op.isWrite
        · rw [hWr] at hAtOp
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hAtOp ⊢
          have hNoneNe : (none == some op.addr) = false := rfl
          rw [hNoneNe]
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨hAtOp.1, ih (some op.addr) 0#64 hTailSorted ⟨hLeRest, hAtOp.2, ?_⟩⟩
          intro a hGt
          have hA := hInv a
          rw [hFilterGt a hGt] at hA
          exact hA
        · rw [hWr] at hAtOp
          simp only [↓reduceIte] at hAtOp ⊢
          refine ih (some op.addr) op.val hTailSorted ⟨hLeRest, hAtOp, ?_⟩
          intro a hGt
          have hA := hInv a
          rw [hFilterGt a hGt] at hA
          exact hA
      | some c =>
        rcases hInv with ⟨hAllGe, hCurRw, hAbove⟩
        have hCLeOp : c ≤ op.addr := hAllGe op (List.mem_cons_self ..)
        by_cases hEqC : c = op.addr
        · subst hEqC
          rw [hFilterSelf] at hCurRw
          unfold checkSingleAddrRw at hCurRw
          cases hWr : op.isWrite
          · rw [hWr] at hCurRw
            simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Bool.and_eq_true] at hCurRw ⊢
            refine ⟨hCurRw.1, ih (some op.addr) lastVal hTailSorted ⟨hLeRest, hCurRw.2, ?_⟩⟩
            intro a hGt
            have hA := hAbove a hGt
            rw [hFilterGt a hGt] at hA
            exact hA
          · rw [hWr] at hCurRw
            simp only [↓reduceIte] at hCurRw ⊢
            refine ih (some op.addr) op.val hTailSorted ⟨hLeRest, hCurRw, ?_⟩
            intro a hGt
            have hA := hAbove a hGt
            rw [hFilterGt a hGt] at hA
            exact hA
        · have hCLtOp : c < op.addr := by omega
          have hAtOp := hAbove op.addr hCLtOp
          rw [hFilterSelf] at hAtOp
          unfold checkSingleAddrRw at hAtOp
          have hSomeNe : (some c == some op.addr) = false := by
            simp [hEqC]
          cases hWr : op.isWrite
          · rw [hWr] at hAtOp
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hAtOp ⊢
            rw [hSomeNe]
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨hAtOp.1, ih (some op.addr) 0#64 hTailSorted ⟨hLeRest, hAtOp.2, ?_⟩⟩
            intro a hGt
            have hA := hAbove a (by omega)
            rw [hFilterGt a hGt] at hA
            exact hA
          · rw [hWr] at hAtOp
            simp only [↓reduceIte] at hAtOp ⊢
            refine ih (some op.addr) op.val hTailSorted ⟨hLeRest, hAtOp, ?_⟩
            intro a hGt
            have hA := hAbove a (by omega)
            rw [hFilterGt a hGt] at hA
            exact hA

/-- **Unconditional Blum `UMem` Completeness for Arbitrary Read/Write RAM Logs (`blumPermutationComplete`)**:
    Every valid chronological read/write RAM trace (`checkValidOnlineRamLog online = true`,
    supporting arbitrary interleaved reads, overwrites, and zero-initialized addresses) is accepted
    by both `verifyBlumMemory` and the $O(N \log N)$ `verifyBlumMemoryFast` at `sortMemOpsByAddrTime online`. -/
theorem blumPermutationComplete (online : List MemOp)
    (hValid : checkValidOnlineRamLog online = true) :
    verifyBlumMemory online (sortMemOpsByAddrTime online) = true ∧
    verifyBlumMemoryFast online.toArray (sortMemOpsByAddrTime online).toArray = true ∧
    ∃ offline : List MemOp, verifyBlumMemory online offline = true := by
  unfold checkValidOnlineRamLog at hValid
  simp only [Bool.and_eq_true] at hValid
  rcases hValid with ⟨hChrono, hOnlineRam⟩
  let offline := sortMemOpsByAddrTime online
  have hSorted : checkAddrTimeSorted offline = true := sortMemOpsByAddrTime_sorted online hChrono
  have hBag : checkBagPermutation online offline = true :=
    perm_implies_checkBagPermutation (sortMemOpsByAddrTime_perm online)
  have hLocalRw : checkLocalReadWriteConsistency offline = true := by
    unfold checkLocalReadWriteConsistency
    apply checkLocalRwStep_of_per_addr offline none 0#64
      (pairwise_addr_le_of_sorted ((checkAddrTimeSorted_iff_pairwise _).mp hSorted))
    intro a
    rw [filterAddr_sortMemOpsByAddrTime_eq a online hChrono]
    exact checkOnlineRamStep_filterAddr a [] online hOnlineRam
  have hSpec : verifyBlumMemory online offline = true := by
    unfold verifyBlumMemory
    simp [hChrono, hSorted, hBag, hLocalRw]
  have hFast : verifyBlumMemoryFast online.toArray offline.toArray = true := by
    rw [verifyBlumMemoryFast_eq_verifyBlumMemory]
    exact hSpec
  exact ⟨hSpec, hFast, offline, hSpec⟩

/-- Universal adjacent read-after-write soundness: anywhere in a Blum-checked transcript where a
    write `opW` is immediately followed by a read `opR` at the same address, `opR.val = opW.val`. -/
theorem blum_write_then_read_sound
    (pref suff : List MemOp) (opW opR : MemOp)
    (curAddr : Option Nat) (lastVal : BitVec 64)
    (hWrite : opW.isWrite = true)
    (hRead : opR.isWrite = false)
    (hSameAddr : opR.addr = opW.addr)
    (hRw : checkLocalRwStep curAddr lastVal (pref ++ opW :: opR :: suff) = true) :
    opR.val = opW.val := by
  induction pref generalizing curAddr lastVal with
  | nil =>
    simp only [List.nil_append, checkLocalRwStep, hWrite, ↓reduceIte, hRead, Bool.false_eq_true] at hRw
    rw [hSameAddr] at hRw
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hRw
    exact hRw.1
  | cons hd tl ih =>
    simp only [List.cons_append, checkLocalRwStep] at hRw
    cases hHd : hd.isWrite
    · rw [hHd] at hRw
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hRw
      exact ih (some hd.addr) (if curAddr == some hd.addr then lastVal else 0#64) hRw.2
    · rw [hHd] at hRw
      simp only [↓reduceIte] at hRw
      exact ih (some hd.addr) hd.val hRw

/-- Soundness of `verifyBlumMemory`: preserves transcript length, all per-operation multiplicities,
    chronological online ordering, `(addr, timestamp)` offline sorting, and local RAW consistency. -/
theorem verifyBlumMemory_sound
    (online offline : List MemOp) (probeOp : MemOp)
    (hOk : verifyBlumMemory online offline = true) :
    online.length = offline.length ∧
    countMemOp probeOp online = countMemOp probeOp offline ∧
    checkChronologicalLog online = true ∧
    checkAddrTimeSorted offline = true ∧
    checkLocalReadWriteConsistency offline = true := by
  unfold verifyBlumMemory at hOk
  simp only [Bool.and_eq_true] at hOk
  have hBag := hOk.1.2
  have hCnt := checkBagPermutation_counts_eq online offline probeOp hBag
  unfold checkBagPermutation at hBag
  simp only [Bool.and_eq_true, beq_iff_eq] at hBag
  exact ⟨hBag.1.1, hCnt, hOk.1.1.1, hOk.1.1.2, hOk.2⟩

/-- Canonical chronological `UMem` trace (uninitialized read `0#64` at addr `300`, writes to `200`
    and `100`, overwrite at `200`, and reads of both) and its `(addr, timestamp)`-sorted permutation. -/
def sampleOnlineMem : List MemOp :=
  [ ⟨300, 1, false, 0#64,  0x00#256⟩
  , ⟨200, 2, true,  77#64, 0xAA#256⟩
  , ⟨100, 3, true,  42#64, 0xBB#256⟩
  , ⟨200, 4, false, 77#64, 0xAA#256⟩
  , ⟨200, 5, true,  91#64, 0xCC#256⟩
  , ⟨200, 6, false, 91#64, 0xCC#256⟩
  , ⟨100, 7, false, 42#64, 0xBB#256⟩ ]

def sampleOfflineSortedMem : List MemOp :=
  sortMemOpsByAddrTime sampleOnlineMem

/-- Second chronological `UMem` turn trace at strictly later timestamps `10..12`. -/
def sampleSecondOnlineMem : List MemOp :=
  [ ⟨400, 10, true,  19#64, 0xDD#256⟩
  , ⟨500, 11, false, 0#64,  0x00#256⟩
  , ⟨400, 12, false, 19#64, 0xDD#256⟩ ]

def sampleSecondOfflineSortedMem : List MemOp :=
  sortMemOpsByAddrTime sampleSecondOnlineMem

example : checkLocalRwStep none 0#64 sampleOfflineSortedMem = true := by decide
example : checkValidOnlineRamLog sampleOnlineMem = true := by decide
example : verifyBlumMemory sampleOnlineMem sampleOfflineSortedMem = true := by decide
example : verifyBlumMemoryFast sampleOnlineMem.toArray sampleOfflineSortedMem.toArray = true := by decide
example : verifyBlumMemoryFast sampleSecondOnlineMem.toArray sampleSecondOfflineSortedMem.toArray = true := by decide

end Obend.Trailblaze.Polis

end
