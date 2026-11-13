module
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
public import Obend.Tactic.Tooth

public section
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

/-- Fast $O(N \log N)$ `Array MemOp` Blum memory verifier (`Exec`): replaces $O(N^2)$ `countMemOp`
    bag scanning with single-pass `Array` checks and `sortMemOpsByAddrTime online.toList == offline.toList`. -/
def verifyBlumMemoryFast (online offline : Array MemOp) : Bool :=
  checkChronologicalLogExec online &&
  (sortMemOpsByAddrTime online.toList == offline.toList) &&
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
