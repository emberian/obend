module
/-
# Obend.Equiv.ClairvoyantBook — the demand oracle as a memo table

Hackett and Hutton's clairvoyant call-by-value (`Obend.Equiv.Clairvoyant`) guesses, at each binding,
whether the bound term will be demanded. This module puts that guess in a certificate.

§1 is about `Run` itself. `Ω` has no derivation (`omega_diverges`), yet `(λ_. n) Ω` evaluates at
cost 2 by the Skip rule (`clairvoyant_let_unused_omega`). The guess cannot be wrong in the other
direction: a binding that is demanded was not skipped (`demanded_binding_not_skipped`), so
`(λx. x) Ω` has no derivation either (`omega_demanded_diverges`).

§2–§4 are a first-order language of supercombinators with a lazy `let` (`ScExpr`, `ScBook`). Its
reference semantics `evalCallSpec` is the lazy one: a `let` binds whatever its right-hand side
evaluates to, possibly nothing, and a variable bound to nothing cannot be read. The certificate is
a memo table (`MemoTable`): one row per call `(fnId, argVal) ↦ resVal`, with a rank and the demand
bits of the `let`s met on the way. The checker `verifyMemoTableExec` replays each row's body once:

* a `let` with bit `false` binds nothing and does not look at its right-hand side;
* a call is a binary search of the table (`lookupMemoFast`, the `Lookup` relation) and the row found
  must have a strictly smaller rank (`checkBeforeRank`, the `Before` relation).

`clairvoyantMemo_sound`: every row of an accepted table is a fact of the reference semantics. The
rank is what makes this an induction; without it a row could justify itself.

§5 lowers the call-free expressions to Core4 (a lazy `let` is a β-redex) and shows that a replay
the checker accepts is a `Run .eval` derivation (`scExpr_toCore4_clairvoyant_sound`): bit `false`
is Skip, bit `true` is Let′.
-/
public import Obend.Equiv.Clairvoyant
public import Obend.SymbolicZk.LinMem
public section
namespace Obend.Equiv
open Obend.Core.Term
open Obend.Core.TermTraverse (substitute_comp)
open Obend.SymbolicZk
set_option autoImplicit false

/-! ## 1. Laziness and demand in `Run` -/

/-- `Ω = (λx. x x) (λx. x x)`. -/
@[expose] def omegaCore4 : Term :=
  .app (.lam (.app (.bound 0) (.bound 0))) (.lam (.app (.bound 0) (.bound 0)))

theorem instantiate_self_app (x : Term) :
    instantiate (.app (.bound 0) (.bound 0)) x = .app x x := by
  rw [instantiate_eq]; simp only [Term.substitute, single]

/-- `Ω` has no clairvoyant derivation, at any cost. -/
theorem omega_diverges : ∀ (k : Nat) (v : Term), ¬ Run .eval omegaCore4 v k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro v h
    have h' : Run .eval (.app (.lam (.app (.bound 0) (.bound 0)))
        (.lam (.app (.bound 0) (.bound 0)))) v k := h
    cases h' with
    | value hv => exact app_not_ready hv
    | apply hf hb hbody =>
      obtain ⟨hbe, _⟩ := cv_lam hf
      cases hbe
      rw [instantiate_self_app] at hbody
      rcases bind_of_settled (.value (.lam _)) hb with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact ih _ (by omega) _ hbody
      · cases hbody with
        | value hv => exact app_not_ready hv
        | apply hf' _ _ => exact cv_skipped_false hf'
        | applySpec hf' _ => exact cv_skipped_false hf'
    | applySpec hf _ =>
      obtain ⟨he, _⟩ := cv_lam hf
      cases he

/-- **An unused diverging binding costs 2**: one Skip, one β. `Ω` is never entered. -/
theorem clairvoyant_let_unused_omega (n : Nat) :
    Run .eval (.app (.lam (.nat n)) omegaCore4) (.nat n) 2 := by
  have hbody : Run (.tail .eval) (instantiate (.nat n) skipped) (.nat n) 0 := by
    rw [instantiate_eq]; simp only [Term.substitute]; exact Run.value (.nat n)
  exact Run.apply (Run.value (.lam (.nat n))) (Run.skip omegaCore4) hbody

/-- What Skip leaves cannot be evaluated. -/
theorem skipped_blocks_demand (v : Term) (k : Nat) : ¬ Run .eval skipped v k := cv_skipped_false

/-- **A demanded binding was not skipped**: every derivation of `(λx. x) a` binds `a` to something
other than `skipped` and then evaluates it. -/
theorem demanded_binding_not_skipped {a v : Term} {k : Nat}
    (h : Run .eval (.app (.lam (.bound 0)) a) v k) :
    ∃ x kb ke, Run .bind a x kb ∧ x ≠ skipped ∧ Run .eval x v ke ∧ k = kb + ke + 1 := by
  cases h with
  | value hv => exact absurd hv app_not_ready
  | apply hf hb hbody =>
    obtain ⟨hbe, hk⟩ := cv_lam hf
    cases hbe
    have e : ∀ x : Term, instantiate (.bound 0) x = x := by
      intro x; rw [instantiate_eq]; simp only [Term.substitute, single]
    rw [e] at hbody
    refine ⟨_, _, _, hb, ?_, hbody, by omega⟩
    rintro rfl
    exact cv_skipped_false hbody
  | applySpec hf _ =>
    obtain ⟨he, _⟩ := cv_lam hf
    cases he

/-- A demanded `Ω` diverges whatever the oracle guesses. -/
theorem omega_demanded_diverges (v : Term) (k : Nat) :
    ¬ Run .eval (.app (.lam (.bound 0)) omegaCore4) v k := by
  intro h
  obtain ⟨x, kb, ke, hb, hne, _, _⟩ := demanded_binding_not_skipped h
  rcases bind_of_unsettled (fun hs => app_not_ready hs) hb with ⟨rfl, _⟩ | ⟨j, hj, _⟩
  · exact hne rfl
  · exact omega_diverges _ _ hj

/-! ## 2. Supercombinators with a lazy `let`: the reference semantics -/

/-- First-order expressions over 64-bit words. Variables are de Bruijn indices; a definition's
parameter is index 0 of its body. -/
inductive ScExpr where
  | lit (n : UInt64)
  | var (idx : Nat)
  | add (a b : ScExpr)
  | ifz (cond thenBr elseBr : ScExpr)
  | letLazy (rhs body : ScExpr)
  | call (fnId : UInt64) (arg : ScExpr)
  deriving DecidableEq, Repr, Inhabited

structure ScDef where
  fnId : UInt64
  body : ScExpr
  deriving DecidableEq, Repr, Inhabited

/-- A book of definitions, kept sorted by `fnId`. -/
structure ScBook where
  defs : Array ScDef
  deriving Repr, Inhabited

/-- What reading a slot bound to nothing gives. -/
@[expose] def skippedRead : Option UInt64 := none

/-- A variable read: the slot's word; a skipped slot and an unbound index give nothing. -/
@[expose] def readEnv (env : List (Option UInt64)) (i : Nat) : Option UInt64 :=
  match env[i]? with
  | some (some v) => some v
  | _ => skippedRead

/-- The lazy semantics of an expression, calls answered by `call`. A `let` binds what its
right-hand side evaluates to, which may be nothing. -/
@[expose] def evalScWith (call : UInt64 → UInt64 → Option UInt64) :
    List (Option UInt64) → ScExpr → Option UInt64
  | _, .lit n => some n
  | env, .var i => readEnv env i
  | env, .add a b =>
    match evalScWith call env a, evalScWith call env b with
    | some x, some y => some (x + y)
    | _, _ => none
  | env, .ifz c t e =>
    match evalScWith call env c with
    | some x => if x = 0 then evalScWith call env t else evalScWith call env e
    | none => none
  | env, .letLazy rhs body => evalScWith call (evalScWith call env rhs :: env) body
  | env, .call f a =>
    match evalScWith call env a with
    | some v => call f v
    | none => none

/-- The definition of `f`, by linear search. -/
@[expose] def ScBook.lookupSpec (book : ScBook) (f : UInt64) : Option ScDef :=
  book.defs.toList.find? fun d => d.fnId.toNat == f.toNat

/-- **The reference semantics of a call**, at call depth `fuel`. -/
@[expose] def evalCallSpec (book : ScBook) : Nat → UInt64 → UInt64 → Option UInt64
  | 0, _, _ => none
  | fuel + 1, f, v =>
    match book.lookupSpec f with
    | some d => evalScWith (evalCallSpec book fuel) [some v] d.body
    | none => none

/-- **The reference semantics of an expression**, at call depth `fuel`. -/
@[expose] def evalScSpec (book : ScBook) (fuel : Nat) (env : List (Option UInt64)) (e : ScExpr) :
    Option UInt64 :=
  evalScWith (evalCallSpec book fuel) env e

/-- The book is sorted by `fnId`, strictly. -/
@[expose] def ScBook.WF (book : ScBook) : Prop :=
  book.defs.toList.Pairwise fun a b => a.fnId.toNat < b.fnId.toNat

instance (book : ScBook) : Decidable book.WF := by unfold ScBook.WF; infer_instance

/-! ### The semantics is monotone: more answers and more bindings never change a result -/

theorem readEnv_some {env : List (Option UInt64)} {i : Nat} {v : UInt64}
    (h : readEnv env i = some v) : env[i]? = some (some v) := by
  unfold readEnv at h
  split at h
  · rename_i w hw; cases h; exact hw
  · cases h

theorem readEnv_of_getElem? {env : List (Option UInt64)} {i : Nat} {v : UInt64}
    (h : env[i]? = some (some v)) : readEnv env i = some v := by
  unfold readEnv; rw [h]

/-- `env'` binds everything `env` binds, to the same words. -/
def EnvLe (env env' : List (Option UInt64)) : Prop :=
  ∀ i v, readEnv env i = some v → readEnv env' i = some v

theorem EnvLe.refl (env : List (Option UInt64)) : EnvLe env env := fun _ _ h => h

theorem EnvLe.cons {env env' : List (Option UInt64)} {o o' : Option UInt64}
    (ho : ∀ v, o = some v → o' = some v) (h : EnvLe env env') : EnvLe (o :: env) (o' :: env') := by
  intro i v hv
  cases i with
  | zero =>
    have := readEnv_some hv
    simp only [List.getElem?_cons_zero, Option.some.injEq] at this
    exact readEnv_of_getElem? (by simp only [List.getElem?_cons_zero, ho v this])
  | succ n =>
    have := readEnv_some hv
    simp only [List.getElem?_cons_succ] at this
    have h2 := readEnv_some (h n v (readEnv_of_getElem? this))
    exact readEnv_of_getElem? (by simp only [List.getElem?_cons_succ, h2])

theorem evalScWith_mono {c c' : UInt64 → UInt64 → Option UInt64}
    (hc : ∀ f v r, c f v = some r → c' f v = some r) :
    ∀ (e : ScExpr) (env env' : List (Option UInt64)) (r : UInt64), EnvLe env env' →
      evalScWith c env e = some r → evalScWith c' env' e = some r := by
  intro e
  induction e with
  | lit n => intro env env' r _ h; exact h
  | var i => intro env env' r he h; exact he i r h
  | add a b iha ihb =>
    intro env env' r he h
    simp only [evalScWith] at h ⊢
    cases ha : evalScWith c env a with
    | none => simp only [ha] at h; cases h
    | some x =>
      cases hb : evalScWith c env b with
      | none => simp only [ha, hb] at h; cases h
      | some y =>
        simp only [ha, hb] at h
        rw [iha env env' x he ha, ihb env env' y he hb]
        exact h
  | ifz cnd t e ihc iht ihe =>
    intro env env' r he h
    simp only [evalScWith] at h ⊢
    cases hcnd : evalScWith c env cnd with
    | none => simp only [hcnd] at h; cases h
    | some x =>
      simp only [hcnd] at h
      rw [ihc env env' x he hcnd]
      by_cases hx : x = 0
      · simp only [hx, ite_true] at h ⊢
        exact iht env env' r he h
      · simp only [hx, ite_false] at h ⊢
        exact ihe env env' r he h
  | letLazy rhs body ihr ihb =>
    intro env env' r he h
    simp only [evalScWith] at h ⊢
    exact ihb _ _ r (EnvLe.cons (fun v hv => ihr env env' v he hv) he) h
  | call f a iha =>
    intro env env' r he h
    simp only [evalScWith] at h ⊢
    cases ha : evalScWith c env a with
    | none => simp only [ha] at h; cases h
    | some v =>
      simp only [ha] at h
      rw [iha env env' v he ha]
      exact hc f v r h

theorem evalCallSpec_succ (book : ScBook) :
    ∀ (fuel : Nat) (f v r : UInt64), evalCallSpec book fuel f v = some r →
      evalCallSpec book (fuel + 1) f v = some r := by
  intro fuel
  induction fuel with
  | zero => intro f v r h; simp only [evalCallSpec] at h; cases h
  | succ n ih =>
    intro f v r h
    simp only [evalCallSpec] at h ⊢
    cases hd : book.lookupSpec f with
    | none => simp only [hd] at h; cases h
    | some d =>
      simp only [hd] at h ⊢
      exact evalScWith_mono (ih) d.body _ _ r (EnvLe.refl _) h

theorem evalCallSpec_mono (book : ScBook) {fuel fuel' : Nat} (hle : fuel ≤ fuel') (f v r : UInt64)
    (h : evalCallSpec book fuel f v = some r) : evalCallSpec book fuel' f v = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalCallSpec_succ book _ f v r ih

/-! ## 3. The certificate: a memo table with ranks and demand bits -/

/-- One memoized call: `fnId(argVal) = resVal`, at rank `rank`, with the demand bits of the `let`s
its replay meets, in order. -/
structure MemoRow where
  fnId : UInt64
  argVal : UInt64
  resVal : UInt64
  rank : UInt64
  needs : List Bool
  deriving DecidableEq, Repr, Inhabited

structure MemoTable where
  rows : Array MemoRow
  deriving Repr, Inhabited

/-- A three-way comparison of words. -/
def cmpU64 (a b : UInt64) : Ordering := if a < b then .lt else if a = b then .eq else .gt

theorem cmpU64_eq (a b : UInt64) : cmpU64 a b = compare a.toNat b.toNat := by
  unfold cmpU64
  by_cases h1 : a < b
  · simp only [h1, ite_true]
    exact (Nat.compare_eq_lt.mpr (UInt64.lt_iff_toNat_lt.mp h1)).symm
  · by_cases h2 : a = b
    · subst h2
      simp only [h1, ite_false, ite_true]
      exact (Nat.compare_eq_eq.mpr rfl).symm
    · simp only [h1, h2, ite_false]
      have hlt : ¬ a.toNat < b.toNat := fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h)
      have hne : a.toNat ≠ b.toNat := fun h => h2 (UInt64.toNat_inj.mp h)
      exact (Nat.compare_eq_gt.mpr (by omega)).symm

/-- The key order of the table: by `fnId`, then `argVal`. -/
def memoKeyLt (a b : MemoRow) : Bool :=
  a.fnId < b.fnId || (a.fnId == b.fnId && a.argVal < b.argVal)

/-- The key as one number (reasoning only). -/
@[expose] def memoKeyOf (f a : UInt64) : Nat := f.toNat * 18446744073709551616 + a.toNat

theorem memoKeyLt_iff (a b : MemoRow) :
    memoKeyLt a b = true ↔ memoKeyOf a.fnId a.argVal < memoKeyOf b.fnId b.argVal := by
  have h1 := a.argVal.toNat_lt
  have h2 := b.argVal.toNat_lt
  simp only [memoKeyLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, memoKeyOf]
  omega

/-- One adjacent pass: keys strictly increase, so no call has two rows. -/
def checkMemoSortedUnique (table : MemoTable) : Bool := adjacentAll memoKeyLt table.rows 0

theorem checkMemoSortedUnique_iff (table : MemoTable) :
    checkMemoSortedUnique table = true ↔
      table.rows.toList.Pairwise fun a b => memoKeyOf a.fnId a.argVal < memoKeyOf b.fnId b.argVal := by
  rw [checkMemoSortedUnique, adjacentAll_iff_pairwise]
  · constructor <;> intro h <;> exact h.imp fun hab => by first
      | exact (memoKeyLt_iff _ _).1 hab
      | exact (memoKeyLt_iff _ _).2 hab
  · intro a b c hab hbc
    rw [memoKeyLt_iff] at *
    omega

/-- The comparison of a row's key against the probe `(f, a)`. -/
def memoCmp (f a : UInt64) (r : MemoRow) : Ordering :=
  match cmpU64 r.fnId f with
  | .eq => cmpU64 r.argVal a
  | o => o

theorem memoCmp_eq (f a : UInt64) (r : MemoRow) :
    memoCmp f a r = compare (memoKeyOf r.fnId r.argVal) (memoKeyOf f a) := by
  have h1 := a.toNat_lt
  have h2 := r.argVal.toNat_lt
  unfold memoCmp
  rw [cmpU64_eq, cmpU64_eq]
  rcases Nat.lt_trichotomy r.fnId.toNat f.toNat with hlt | heq | hgt
  · rw [Nat.compare_eq_lt.mpr hlt]
    exact (Nat.compare_eq_lt.mpr (by simp only [memoKeyOf]; omega)).symm
  · rw [Nat.compare_eq_eq.mpr heq]
    simp only [memoKeyOf, heq]
    rcases Nat.lt_trichotomy r.argVal.toNat a.toNat with h | h | h
    · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr (by omega)]
    · rw [Nat.compare_eq_eq.mpr h, Nat.compare_eq_eq.mpr (by omega)]
    · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr (by omega)]
  · rw [Nat.compare_eq_gt.mpr hgt]
    exact (Nat.compare_eq_gt.mpr (by simp only [memoKeyOf]; omega)).symm

/-- **`Lookup`**: the row of the call `f(a)`, by binary search: its result and its rank. -/
def lookupMemoFast (table : MemoTable) (f a : UInt64) : Option (UInt64 × UInt64) :=
  (binSearch table.rows (memoCmp f a) 0 table.rows.size).map fun r => (r.resVal, r.rank)

/-- **`Spec ↔ Exec` for `Lookup`**: on a table that passed `checkMemoSortedUnique`, the binary
search is the linear search. -/
theorem lookupMemoFast_eq_find? (table : MemoTable) (hs : checkMemoSortedUnique table = true)
    (f a : UInt64) :
    lookupMemoFast table f a =
      (table.rows.toList.find? fun r => r.fnId == f && r.argVal == a).map
        fun r => (r.resVal, r.rank) := by
  unfold lookupMemoFast
  rw [binSearch_eq_find? table.rows (memoCmp f a) (fun r => memoKeyOf r.fnId r.argVal)
    (memoKeyOf f a) (memoCmp_eq f a) ((checkMemoSortedUnique_iff table).1 hs)]
  have e : (fun r : MemoRow => memoKeyOf r.fnId r.argVal == memoKeyOf f a) =
      (fun r : MemoRow => r.fnId == f && r.argVal == a) := by
    funext r
    have h1 := a.toNat_lt
    have h2 := r.argVal.toNat_lt
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, Bool.and_eq_true, memoKeyOf, ← UInt64.toNat_inj]
    omega
  rw [e]

/-- A row found by `Lookup` is a row of the table with that key. -/
theorem lookupMemoFast_mem (table : MemoTable) (hs : checkMemoSortedUnique table = true)
    (f a res rk : UInt64) (h : lookupMemoFast table f a = some (res, rk)) :
    ∃ row ∈ table.rows.toList, row.fnId = f ∧ row.argVal = a ∧ row.resVal = res ∧ row.rank = rk := by
  rw [lookupMemoFast_eq_find? table hs] at h
  cases hf : table.rows.toList.find? (fun r => r.fnId == f && r.argVal == a) with
  | none => rw [hf] at h; cases h
  | some row =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨row, List.mem_of_find?_eq_some hf, hp.1, hp.2, h.1, h.2⟩

/-- The definition of `f`, by binary search. -/
def lookupDefFast (book : ScBook) (f : UInt64) : Option ScDef :=
  binSearch book.defs (fun d => cmpU64 d.fnId f) 0 book.defs.size

/-- **`Spec ↔ Exec` for the book**: on a sorted book the binary search is the linear search. -/
theorem lookupDefFast_eq_spec (book : ScBook) (h : book.WF) (f : UInt64) :
    lookupDefFast book f = book.lookupSpec f :=
  binSearch_eq_find? book.defs _ (fun d => d.fnId.toNat) f.toNat (fun d => cmpU64_eq d.fnId f) h

/-- **`Before`**: a callee's row ranks strictly below its caller's. -/
def checkBeforeRank (calleeRank callerRank : UInt64) : Bool := calleeRank < callerRank

/-- The replay of an expression against the table, for a row of rank `callerRank`: the word it
computes and the demand bits left. A `let` reads one bit: `false` binds nothing and skips the
right-hand side; `true` replays it and binds its word. A call is one `Lookup` and one `Before`. -/
def checkExpr (table : MemoTable) (callerRank : UInt64) :
    ScExpr → List Bool → List (Option UInt64) → Option (UInt64 × List Bool)
  | .lit n, ns, _ => some (n, ns)
  | .var i, ns, env =>
    match readEnv env i with
    | some v => some (v, ns)
    | none => none
  | .add a b, ns, env =>
    match checkExpr table callerRank a ns env with
    | some (x, ns1) =>
      match checkExpr table callerRank b ns1 env with
      | some (y, ns2) => some (x + y, ns2)
      | none => none
    | none => none
  | .ifz c t e, ns, env =>
    match checkExpr table callerRank c ns env with
    | some (x, ns1) =>
      if x = 0 then checkExpr table callerRank t ns1 env else checkExpr table callerRank e ns1 env
    | none => none
  | .letLazy rhs body, ns, env =>
    match ns with
    | [] => none
    | false :: ns1 => checkExpr table callerRank body ns1 (none :: env)
    | true :: ns1 =>
      match checkExpr table callerRank rhs ns1 env with
      | some (v, ns2) => checkExpr table callerRank body ns2 (some v :: env)
      | none => none
  | .call f a, ns, env =>
    match checkExpr table callerRank a ns env with
    | some (v, ns1) =>
      match lookupMemoFast table f v with
      | some (res, rk) => if checkBeforeRank rk callerRank = true then some (res, ns1) else none
      | none => none
    | none => none

/-- One row: its definition's body, replayed on its argument with its bits, gives its result and
uses every bit. -/
def verifyRow (book : ScBook) (table : MemoTable) (row : MemoRow) : Bool :=
  match lookupDefFast book row.fnId with
  | some d =>
    match checkExpr table row.rank d.body row.needs [some row.argVal] with
    | some (v, rest) => v == row.resVal && rest.isEmpty
    | none => false
  | none => false

/-- **The checker**: one adjacent pass for the keys, one replay per row. -/
def verifyMemoTableExec (book : ScBook) (table : MemoTable) : Bool :=
  checkMemoSortedUnique table && arrayAll (verifyRow book table) table.rows

/-- **A `let` that is not demanded is one bit of work**, whatever its right-hand side: the replay
does not look at it. -/
theorem checkExpr_skips_rhs (table : MemoTable) (rk : UInt64) (rhs : ScExpr) (n : UInt64)
    (ns : List Bool) (env : List (Option UInt64)) :
    checkExpr table rk (.letLazy rhs (.lit n)) (false :: ns) env = some (n, ns) := by
  simp only [checkExpr]

/-! ## 4. Soundness of the memo table -/

/-- A replay accepted at rank `rk`, when every row below `rk` is a fact of the reference
semantics, is an evaluation of the reference semantics at every large enough call depth. -/
theorem checkExpr_sound (book : ScBook) (table : MemoTable)
    (hs : checkMemoSortedUnique table = true) (rk : UInt64)
    (hrows : ∀ row ∈ table.rows.toList, row.rank < rk →
      ∃ fuel, evalCallSpec book fuel row.fnId row.argVal = some row.resVal) :
    ∀ (e : ScExpr) (ns : List Bool) (env : List (Option UInt64)) (v : UInt64) (rest : List Bool),
      checkExpr table rk e ns env = some (v, rest) →
      ∃ fuel, ∀ fuel', fuel ≤ fuel' → evalScSpec book fuel' env e = some v := by
  intro e
  induction e with
  | lit n =>
    intro ns env v rest h
    simp only [checkExpr, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨0, fun _ _ => by simp only [evalScSpec, evalScWith, h.1]⟩
  | var i =>
    intro ns env v rest h
    simp only [checkExpr] at h
    cases hr : readEnv env i with
    | none => simp only [hr] at h; cases h
    | some w =>
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨0, fun _ _ => by simp only [evalScSpec, evalScWith, hr, h.1]⟩
  | add a b iha ihb =>
    intro ns env v rest h
    simp only [checkExpr] at h
    cases ha : checkExpr table rk a ns env with
    | none => simp only [ha] at h; cases h
    | some p =>
      obtain ⟨x, ns1⟩ := p
      cases hb : checkExpr table rk b ns1 env with
      | none => simp only [ha, hb] at h; cases h
      | some q =>
        obtain ⟨y, ns2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨F1, h1⟩ := iha ns env x ns1 ha
        obtain ⟨F2, h2⟩ := ihb ns1 env y ns2 hb
        refine ⟨max F1 F2, fun fuel' hle => ?_⟩
        have e1 := h1 fuel' (by omega)
        have e2 := h2 fuel' (by omega)
        simp only [evalScSpec] at e1 e2 ⊢
        simp only [evalScWith, e1, e2, h.1]
  | ifz cnd t e ihc iht ihe =>
    intro ns env v rest h
    simp only [checkExpr] at h
    cases hc : checkExpr table rk cnd ns env with
    | none => simp only [hc] at h; cases h
    | some p =>
      obtain ⟨x, ns1⟩ := p
      simp only [hc] at h
      obtain ⟨F1, h1⟩ := ihc ns env x ns1 hc
      by_cases hx : x = 0
      · simp only [hx, ite_true] at h
        obtain ⟨F2, h2⟩ := iht ns1 env v rest h
        refine ⟨max F1 F2, fun fuel' hle => ?_⟩
        have e1 := h1 fuel' (by omega)
        have e2 := h2 fuel' (by omega)
        simp only [evalScSpec] at e1 e2 ⊢
        simp only [evalScWith, e1, hx, ite_true, e2]
      · simp only [hx, ite_false] at h
        obtain ⟨F2, h2⟩ := ihe ns1 env v rest h
        refine ⟨max F1 F2, fun fuel' hle => ?_⟩
        have e1 := h1 fuel' (by omega)
        have e2 := h2 fuel' (by omega)
        simp only [evalScSpec] at e1 e2 ⊢
        simp only [evalScWith, e1, hx, ite_false, e2]
  | letLazy rhs body ihr ihb =>
    intro ns env v rest h
    simp only [checkExpr] at h
    match ns, h with
    | false :: ns1, h =>
      simp only at h
      obtain ⟨F, hF⟩ := ihb ns1 (none :: env) v rest h
      refine ⟨F, fun fuel' hle => ?_⟩
      have e := hF fuel' hle
      simp only [evalScSpec] at e ⊢
      simp only [evalScWith]
      exact evalScWith_mono (fun _ _ _ h => h) body _ _ v
        (EnvLe.cons (fun _ hn => by cases hn) (EnvLe.refl env)) e
    | true :: ns1, h =>
      simp only at h
      cases hr : checkExpr table rk rhs ns1 env with
      | none => simp only [hr] at h; cases h
      | some p =>
        obtain ⟨w, ns2⟩ := p
        simp only [hr] at h
        obtain ⟨F1, h1⟩ := ihr ns1 env w ns2 hr
        obtain ⟨F2, h2⟩ := ihb ns2 (some w :: env) v rest h
        refine ⟨max F1 F2, fun fuel' hle => ?_⟩
        have e1 := h1 fuel' (by omega)
        have e2 := h2 fuel' (by omega)
        simp only [evalScSpec] at e1 e2 ⊢
        simp only [evalScWith, e1]
        exact e2
  | call f a iha =>
    intro ns env v rest h
    simp only [checkExpr] at h
    cases ha : checkExpr table rk a ns env with
    | none => simp only [ha] at h; cases h
    | some p =>
      obtain ⟨w, ns1⟩ := p
      simp only [ha] at h
      cases hl : lookupMemoFast table f w with
      | none => simp only [hl] at h; cases h
      | some q =>
        obtain ⟨res, rk'⟩ := q
        simp only [hl] at h
        by_cases hb : checkBeforeRank rk' rk = true
        · simp only [hb, ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨row, hrow, rfl, rfl, rfl, rfl⟩ := lookupMemoFast_mem table hs f w res rk' hl
          obtain ⟨F1, h1⟩ := iha ns env row.argVal ns1 ha
          obtain ⟨F2, h2⟩ := hrows row hrow (by simpa only [checkBeforeRank, decide_eq_true_eq] using hb)
          refine ⟨max F1 F2, fun fuel' hle => ?_⟩
          have e1 := h1 fuel' (by omega)
          simp only [evalScSpec] at e1 ⊢
          simp only [evalScWith, e1]
          rw [← h.1]
          exact evalCallSpec_mono book (by omega) _ _ _ h2
        · simp only [hb] at h; cases h

/-- **`clairvoyantMemo_sound`**: every row of an accepted table is a fact of the lazy reference
semantics. By induction on the rank: a row's calls were answered by rows of smaller rank. -/
theorem clairvoyantMemo_sound (book : ScBook) (table : MemoTable)
    (h_wf : book.WF) (h_ok : verifyMemoTableExec book table = true) :
    ∀ row ∈ table.rows.toList,
      ∃ fuel : Nat, evalCallSpec book fuel row.fnId row.argVal = some row.resVal := by
  rw [verifyMemoTableExec, Bool.and_eq_true] at h_ok
  obtain ⟨hs, hall⟩ := h_ok
  rw [arrayAll_iff] at hall
  have key : ∀ (n : Nat) (row : MemoRow), row ∈ table.rows.toList → row.rank.toNat = n →
      ∃ fuel : Nat, evalCallSpec book fuel row.fnId row.argVal = some row.resVal := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro row hrow hn
      have hv := hall row hrow
      unfold verifyRow at hv
      rw [lookupDefFast_eq_spec book h_wf] at hv
      cases hd : book.lookupSpec row.fnId with
      | none => simp only [hd] at hv; cases hv
      | some d =>
        simp only [hd] at hv
        cases hc : checkExpr table row.rank d.body row.needs [some row.argVal] with
        | none => simp only [hc] at hv; cases hv
        | some p =>
          obtain ⟨v, rest⟩ := p
          simp only [hc, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨F, hF⟩ := checkExpr_sound book table hs row.rank
            (fun r hr hlt => ih r.rank.toNat (by rw [← hn]; exact UInt64.lt_iff_toNat_lt.mp hlt)
              r hr rfl) d.body _ _ _ _ hc
          refine ⟨F + 1, ?_⟩
          have := hF F (Nat.le_refl _)
          simp only [evalScSpec] at this
          simp only [evalCallSpec, hd]
          rw [this, hv.1]
  exact fun row hrow => key _ row hrow rfl

/-! ### A worked book: `let y = Ω(0) in 42` -/

/-- `Ω(x) = Ω(x)`, and `main(x) = let y = Ω(0) in 42`. -/
def omegaBook : ScBook :=
  { defs := #[⟨1, .call 1 (.var 0)⟩, ⟨2, .letLazy (.call 1 (.lit 0)) (.lit 42)⟩] }

/-- One row: `main(0) = 42`, the `let` not demanded. No row for `Ω`. -/
def lazyTable : MemoTable := { rows := #[⟨2, 0, 42, 1, [false]⟩] }

/-- A forged row `Ω(0) = 42`, which only itself can justify. -/
def forgedTable : MemoTable := { rows := #[⟨1, 0, 42, 5, []⟩] }

theorem omegaBook_wf : omegaBook.WF := by decide

/-- `Ω` has no value in the reference semantics, at any depth. -/
theorem omegaBook_omega_diverges :
    ∀ (fuel : Nat) (v : UInt64), evalCallSpec omegaBook fuel 1 v = none
  | 0, _ => rfl
  | fuel + 1, v => by
    have h : omegaBook.lookupSpec 1 = some ⟨1, .call 1 (.var 0)⟩ := by decide
    simp only [evalCallSpec, h, evalScWith, readEnv, List.getElem?_cons_zero]
    exact omegaBook_omega_diverges fuel v

/-- `main` has the value 42 on every argument, at depth 1: its `let` binds nothing. -/
theorem omegaBook_main (v : UInt64) : evalCallSpec omegaBook 1 2 v = some 42 := by
  have h : omegaBook.lookupSpec 2 = some ⟨2, .letLazy (.call 1 (.lit 0)) (.lit 42)⟩ := by decide
  simp only [evalCallSpec, h, evalScWith]

/-- The one-row table is accepted: the checker never asks for `Ω(0)`. -/
theorem lazyTable_accepted : verifyMemoTableExec omegaBook lazyTable = true := by
  rw [verifyMemoTableExec, Bool.and_eq_true, checkMemoSortedUnique_iff, arrayAll_iff]
  refine ⟨List.pairwise_singleton _ _, ?_⟩
  intro row hrow
  have e : row = ⟨2, 0, 42, 1, [false]⟩ := by simpa [lazyTable] using hrow
  subst e
  have h : omegaBook.lookupSpec 2 = some ⟨2, .letLazy (.call 1 (.lit 0)) (.lit 42)⟩ := by decide
  rw [verifyRow, lookupDefFast_eq_spec omegaBook omegaBook_wf]
  simp only [h, checkExpr]
  decide

/-- The forged row is refused, and not by running anything: were it accepted, `Ω(0) = 42` would be
a fact of the reference semantics. -/
theorem forgedTable_refused : verifyMemoTableExec omegaBook forgedTable = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨fuel, hf⟩ := clairvoyantMemo_sound omegaBook forgedTable omegaBook_wf h ⟨1, 0, 42, 5, []⟩
    (by simp [forgedTable])
  rw [omegaBook_omega_diverges fuel 0] at hf
  cases hf

/-! ## 5. The replay is a clairvoyant derivation -/

/-- The lowering of a call-free expression to Core4. Addition is modulo `2^64`; a lazy `let` is a
β-redex, the binding site of `Run`. A call has no image (`skipped`, which has no derivation). -/
@[expose] def scToCore4 : ScExpr → Term
  | .lit n => .nat n.toNat
  | .var i => .bound i
  | .add a b => .binary .modulo (.binary .add (scToCore4 a) (scToCore4 b)) (.nat 18446744073709551616)
  | .ifz c t e => .ifBool (.binary .equal (scToCore4 c) (.nat 0)) (scToCore4 t) (scToCore4 e)
  | .letLazy rhs body => .app (.lam (scToCore4 body)) (scToCore4 rhs)
  | .call _ _ => skipped

/-- What a slot holds, as a Core4 term. -/
@[expose] def slotTerm : Option UInt64 → Term
  | some v => .nat v.toNat
  | none => skipped

/-- An environment as a substitution: a bound slot is its numeral, anything else is `skipped`. -/
@[expose] def envSubst (env : List (Option UInt64)) (i : Nat) : Term :=
  match env[i]? with
  | some o => slotTerm o
  | none => skipped

theorem slotTerm_rename (o : Option UInt64) (f : Nat → Nat) : (slotTerm o).rename f = slotTerm o := by
  cases o with
  | none => exact rename_skipped f
  | some v => simp only [slotTerm, Term.rename]

theorem envSubst_rename (env : List (Option UInt64)) (i : Nat) (f : Nat → Nat) :
    (envSubst env i).rename f = envSubst env i := by
  unfold envSubst
  cases env[i]? with
  | none => exact rename_skipped f
  | some o => exact slotTerm_rename o f

theorem slotTerm_substitute (o : Option UInt64) (σ : Nat → Term) :
    (slotTerm o).substitute σ = slotTerm o := by
  cases o with
  | none => exact substitute_skipped σ
  | some v => simp only [slotTerm, Term.substitute]

theorem envSubst_substitute (env : List (Option UInt64)) (i : Nat) (σ : Nat → Term) :
    (envSubst env i).substitute σ = envSubst env i := by
  unfold envSubst
  cases env[i]? with
  | none => exact substitute_skipped σ
  | some o => exact slotTerm_substitute o σ

/-- Entering a binder with the slot `o`. -/
theorem instantiate_envSubst (t : Term) (o : Option UInt64) (env : List (Option UInt64)) :
    instantiate (t.substitute (liftSubstitution (envSubst env))) (slotTerm o) =
      t.substitute (envSubst (o :: env)) := by
  rw [instantiate_eq, substitute_comp]
  congr 1
  funext i
  cases i with
  | zero => simp only [liftSubstitution, Term.substitute, single, envSubst, List.getElem?_cons_zero]
  | succ n =>
    simp only [liftSubstitution, envSubst_rename, envSubst_substitute]
    simp only [envSubst, List.getElem?_cons_succ]

theorem envSubst_of_read {env : List (Option UInt64)} {i : Nat} {v : UInt64}
    (h : readEnv env i = some v) : envSubst env i = .nat v.toNat := by
  simp only [envSubst, readEnv_some h, slotTerm]

theorem lookupMemoFast_empty (f a : UInt64) : lookupMemoFast ⟨#[]⟩ f a = none := by
  have h : binSearch (#[] : Array MemoRow) (memoCmp f a) 0 0 = none :=
    binSearch_of_ge _ _ (Nat.le_refl _)
  show Option.map _ (binSearch (#[] : Array MemoRow) (memoCmp f a) 0 0) = none
  rw [h]
  rfl

theorem binary_not_settled {op : Primitive} {l r : Term} : ¬ Settled (.binary op l r) := by
  intro h; cases h with | value h => cases h

theorem ifBool_not_settled {c x y : Term} : ¬ Settled (.ifBool c x y) := by
  intro h; cases h with | value h => cases h

/-- A lowered expression that evaluates to a numeral can be bound to it: kept when it already is
the numeral, evaluated first (Let′) otherwise. -/
theorem bind_of_eval_lowered (e : ScExpr) (env : List (Option UInt64)) (w k : Nat)
    (h : Run .eval ((scToCore4 e).substitute (envSubst env)) (.nat w) k) :
    ∃ k', Run .bind ((scToCore4 e).substitute (envSubst env)) (.nat w) k' := by
  cases e with
  | lit n =>
    simp only [scToCore4, Term.substitute] at h ⊢
    obtain ⟨hv, _⟩ := cv_of_value (.nat _) h
    rw [hv]
    exact ⟨0, .keep (.value (.nat _))⟩
  | var i =>
    simp only [scToCore4, Term.substitute] at h ⊢
    cases hg : env[i]? with
    | none => simp only [envSubst, hg] at h; exact absurd h cv_skipped_false
    | some o =>
      cases o with
      | none => simp only [envSubst, hg, slotTerm] at h; exact absurd h cv_skipped_false
      | some u =>
        simp only [envSubst, hg, slotTerm] at h ⊢
        obtain ⟨hv, _⟩ := cv_of_value (.nat _) h
        rw [hv]
        exact ⟨0, .keep (.value (.nat _))⟩
  | add a b =>
    simp only [scToCore4, Term.substitute] at h ⊢
    exact ⟨_, .eval binary_not_settled h⟩
  | ifz c t e =>
    simp only [scToCore4, Term.substitute] at h ⊢
    exact ⟨_, .eval ifBool_not_settled h⟩
  | letLazy rhs body =>
    simp only [scToCore4, Term.substitute] at h ⊢
    exact ⟨_, .eval (fun hs => app_not_ready hs) h⟩
  | call f a =>
    simp only [scToCore4, substitute_skipped] at h
    exact absurd h cv_skipped_false

/-- **`scExpr_toCore4_clairvoyant_sound`**: a replay the checker accepts with no table (so with no
call) is a clairvoyant derivation of the lowered term to the same numeral. The demand bits are the
oracle: `false` is the Skip rule, `true` is Let′. -/
theorem scExpr_toCore4_clairvoyant_sound (rk : UInt64) :
    ∀ (e : ScExpr) (ns : List Bool) (env : List (Option UInt64)) (v : UInt64) (rest : List Bool),
      checkExpr ⟨#[]⟩ rk e ns env = some (v, rest) →
      ∃ k, Run .eval ((scToCore4 e).substitute (envSubst env)) (.nat v.toNat) k := by
  intro e
  induction e with
  | lit n =>
    intro ns env v rest h
    simp only [checkExpr, Option.some.injEq, Prod.mk.injEq] at h
    simp only [scToCore4, Term.substitute, h.1]
    exact ⟨0, .value (.nat _)⟩
  | var i =>
    intro ns env v rest h
    simp only [checkExpr] at h
    cases hr : readEnv env i with
    | none => simp only [hr] at h; cases h
    | some w =>
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      simp only [scToCore4, Term.substitute, envSubst_of_read hr, h.1]
      exact ⟨0, .value (.nat _)⟩
  | add a b iha ihb =>
    intro ns env v rest h
    simp only [checkExpr] at h
    cases ha : checkExpr ⟨#[]⟩ rk a ns env with
    | none => simp only [ha] at h; cases h
    | some p =>
      obtain ⟨x, ns1⟩ := p
      cases hb : checkExpr ⟨#[]⟩ rk b ns1 env with
      | none => simp only [ha, hb] at h; cases h
      | some q =>
        obtain ⟨y, ns2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨k1, r1⟩ := iha ns env x ns1 ha
        obtain ⟨k2, r2⟩ := ihb ns1 env y ns2 hb
        have hsum : Run .eval (.binary .add ((scToCore4 a).substitute (envSubst env))
            ((scToCore4 b).substitute (envSubst env))) (.nat (x.toNat + y.toNat)) (k1 + k2 + 1) :=
          .binary r1 r2 rfl
        have hmod := Run.binary (op := .modulo) (res := .nat ((x.toNat + y.toNat) % 18446744073709551616))
          hsum (Run.value (.nat 18446744073709551616)) rfl
        simp only [scToCore4, Term.substitute]
        rw [← h.1, UInt64.toNat_add]
        exact ⟨_, hmod⟩
  | ifz cnd t e ihc iht ihe =>
    intro ns env v rest h
    simp only [checkExpr] at h
    cases hc : checkExpr ⟨#[]⟩ rk cnd ns env with
    | none => simp only [hc] at h; cases h
    | some p =>
      obtain ⟨x, ns1⟩ := p
      simp only [hc] at h
      obtain ⟨k1, r1⟩ := ihc ns env x ns1 hc
      simp only [scToCore4, Term.substitute]
      by_cases hx : x = 0
      · simp only [hx, ite_true] at h
        obtain ⟨k2, r2⟩ := iht ns1 env v rest h
        have hcond : Run .eval (.binary .equal ((scToCore4 cnd).substitute (envSubst env)) (.nat 0))
            (.boolean true) (k1 + 0 + 1) := by
          refine .binary r1 (.value (.nat 0)) ?_
          simp [primitiveResult, hx]
        exact ⟨_, .ifTrue hcond r2⟩
      · simp only [hx, ite_false] at h
        obtain ⟨k2, r2⟩ := ihe ns1 env v rest h
        have hne : x.toNat ≠ 0 := fun hz => hx (UInt64.toNat_inj.mp (by simpa using hz))
        have hcond : Run .eval (.binary .equal ((scToCore4 cnd).substitute (envSubst env)) (.nat 0))
            (.boolean false) (k1 + 0 + 1) := by
          refine .binary r1 (.value (.nat 0)) ?_
          simp [primitiveResult, hne]
        exact ⟨_, .ifFalse hcond r2⟩
  | letLazy rhs body ihr ihb =>
    intro ns env v rest h
    simp only [checkExpr] at h
    simp only [scToCore4, Term.substitute]
    match ns, h with
    | false :: ns1, h =>
      simp only at h
      obtain ⟨k2, r2⟩ := ihb ns1 (none :: env) v rest h
      rw [← instantiate_envSubst] at r2
      exact ⟨_, .apply (.value (.lam _)) (.skip _) r2⟩
    | true :: ns1, h =>
      simp only at h
      cases hr : checkExpr ⟨#[]⟩ rk rhs ns1 env with
      | none => simp only [hr] at h; cases h
      | some p =>
        obtain ⟨w, ns2⟩ := p
        simp only [hr] at h
        obtain ⟨k1, r1⟩ := ihr ns1 env w ns2 hr
        obtain ⟨kb, rb⟩ := bind_of_eval_lowered rhs env _ _ r1
        obtain ⟨k2, r2⟩ := ihb ns2 (some w :: env) v rest h
        rw [← instantiate_envSubst] at r2
        exact ⟨_, .apply (.value (.lam _)) rb r2⟩
  | call f a iha =>
    intro ns env v rest h
    simp only [checkExpr] at h
    cases ha : checkExpr ⟨#[]⟩ rk a ns env with
    | none => simp only [ha] at h; cases h
    | some p =>
      obtain ⟨w, ns1⟩ := p
      simp only [ha, lookupMemoFast_empty] at h
      cases h

end Obend.Equiv
