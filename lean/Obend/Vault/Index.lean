module
/-
# Ordered query indices

A persistent balanced tree of buckets. Each bucket retains source order and duplicates,
so its first element implements `List.find?`, including on non-unique inputs. Building
an index is linearithmic; the index belongs to a query context and is shared by its
queries, never rebuilt at each lookup.
-/
public import Std.Data.TreeMap
@[expose] public section

namespace Obend.Vault.Index

open Std

variable {α κ : Type} [Ord κ] [TransOrd κ] [LawfulEqOrd κ]
  [BEq κ] [LawfulBEq κ]

abbrev Buckets (κ α : Type) [Ord κ] := TreeMap κ (List α)

def bucket (index : Buckets κ α) (key : κ) : List α := index[key]?.getD []

def prepend (index : Buckets κ α) (key : κ) (value : α) : Buckets κ α :=
  index.insert key (value :: bucket index key)

def ofList (key : α → κ) (xs : List α) : Buckets κ α :=
  xs.foldr (fun x index => prepend index (key x) x) ∅

omit [LawfulEqOrd κ] [BEq κ] [LawfulBEq κ] in
@[simp] theorem bucket_empty (k : κ) : bucket (∅ : Buckets κ α) k = [] := by
  simp [bucket]

@[simp] theorem bucket_prepend (index : Buckets κ α) (k q : κ) (x : α) :
    bucket (prepend index k x) q = if k == q then x :: bucket index q else bucket index q := by
  simp only [bucket, prepend, TreeMap.getElem?_insert, compare_eq_iff_eq]
  by_cases h : k = q
  · subst q; simp
  · simp [h]

/-- An index query is exactly the ordered scan, even when names repeat. -/
theorem bucket_ofList (key : α → κ) (xs : List α) (k : κ) :
    bucket (ofList key xs) k = xs.filter (fun x => key x == k) := by
  induction xs with
  | nil => simp [ofList]
  | cons x xs ih =>
    simp only [ofList, List.foldr_cons, bucket_prepend, List.filter_cons]
    change (if key x == k then x :: bucket (ofList key xs) k else bucket (ofList key xs) k) = _
    rw [ih]

def first (index : Buckets κ α) (key : κ) : Option α := (bucket index key).head?

/-- A first-match query is exactly the original first-match scan. -/
theorem first_ofList (key : α → κ) (xs : List α) (k : κ) :
    first (ofList key xs) k = xs.find? (fun x => key x == k) := by
  rw [first, bucket_ofList, List.head?_filter]

/-- The first bucket of a pair index has the association list's lookup semantics. -/
theorem first_pairs_lookup {β : Type} (xs : List (κ × β)) (k : κ) :
    (first (ofList Prod.fst xs) k).map Prod.snd = xs.lookup k := by
  rw [first_ofList]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨n, v⟩
    by_cases h : n = k
    · subst n; simp [List.lookup]
    · have hn : (k == n) = false := by simpa using Ne.symm h
      simp [List.lookup, h, hn, ih]

/-- Skipping non-candidates preserves the order and early-exit behavior of a monadic scan. -/
theorem forIn_filter_skip {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type}
    (xs : List α) (p : α → Bool) (f : α → β → m (ForInStep β))
    (h : ∀ x ∈ xs, p x = false → ∀ b, f x b = pure (.yield b)) (b : β) :
    forIn (xs.filter p) b f = forIn xs b f := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    have hr : ∀ y ∈ xs, p y = false → ∀ b, f y b = pure (.yield b) :=
      fun y hy => h y (by simp [hy])
    cases hp : p x
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.forIn_cons,
        h x (by simp) hp, pure_bind]
      exact ih hr b
    · simp only [List.filter_cons, hp, ↓reduceIte, List.forIn_cons]
      congr 1
      funext step
      cases step with
      | done b => rfl
      | yield b => exact ih hr b

/-- A monadic traversal whose iterations keep their state leaves exactly that state. -/
theorem forIn_unchanged {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (xs : List α) (b : β) (f : α → β → m (ForInStep β))
    (h : ∀ x ∈ xs, f x b = pure (.yield b)) : forIn xs b f = pure b := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, h x (by simp), pure_bind]
    exact ih (fun y hy => h y (by simp [hy]))

theorem eraseDups_nodup {β : Type} [BEq β] [LawfulBEq β] (xs : List β) :
    xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | x :: xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    exact ⟨by simp, eraseDups_nodup (xs.filter (fun y => !(y == x)))⟩
termination_by xs.length
decreasing_by
  have := List.length_filter_le (fun y => !(y == x)) xs
  simp only [List.length_cons]
  omega

def prependKeys (index : Buckets κ α) (keys : List κ) (value : α) : Buckets κ α :=
  keys.foldl (fun index key => prepend index key value) index

theorem bucket_prependKeys (index : Buckets κ α) (keys : List κ) (x : α) (q : κ)
    (h : keys.Nodup) :
    bucket (prependKeys index keys x) q =
      if keys.contains q then x :: bucket index q else bucket index q := by
  induction keys generalizing index with
  | nil => simp [prependKeys]
  | cons k keys ih =>
    rw [List.nodup_cons] at h
    simp only [prependKeys, List.foldl_cons]
    change bucket (prependKeys (prepend index k x) keys x) q = _
    rw [ih _ h.2, bucket_prepend]
    by_cases hk : k = q
    · subst q
      simp [h.1]
    · simp [hk, Ne.symm hk]

def ofKeys (keys : α → List κ) (xs : List α) : Buckets κ α :=
  xs.foldr (fun x index => prependKeys index (keys x) x) ∅

/-- A reverse index selects precisely the source items containing a key, in source order. -/
theorem bucket_ofKeys (keys : α → List κ) (xs : List α) (q : κ)
    (h : ∀ x ∈ xs, (keys x).Nodup) :
    bucket (ofKeys keys xs) q = xs.filter (fun x => (keys x).contains q) := by
  induction xs with
  | nil => simp [ofKeys]
  | cons x xs ih =>
    simp only [ofKeys, List.foldr_cons]
    rw [bucket_prependKeys _ _ _ _ (h x (by simp))]
    change (if (keys x).contains q then x :: bucket (ofKeys keys xs) q
      else bucket (ofKeys keys xs) q) = _
    rw [ih (fun y hy => h y (by simp [hy]))]
    rw [List.filter_cons]

/-! ## Certified indices maintained by keyed replacements -/

def replaceKey (key : α → κ) (value : α) (xs : List α) : List α :=
  xs.map fun x => if key x == key value then value else x

theorem find_replaceKey (key : α → κ) (value : α) (xs : List α) (q : κ) :
    (replaceKey key value xs).find? (fun x => key x == q) =
      if key value == q then (xs.find? (fun x => key x == q)).map (fun _ => value)
      else xs.find? (fun x => key x == q) := by
  let f := fun x => if key x == key value then value else x
  have hf : ∀ x, key (f x) = key x := by
    intro x
    simp only [f]
    split
    · rename_i h; exact (beq_iff_eq.mp h).symm
    · rfl
  change (xs.map f).find? (fun x => key x == q) = _
  rw [List.find?_map]
  have hp : ((fun x => key x == q) ∘ f) = (fun x => key x == q) := by
    funext x; simp only [Function.comp_apply, hf]
  rw [hp]
  cases hx : xs.find? (fun x => key x == q) with
  | none => simp
  | some x =>
    have hq : key x = q := by simpa using (List.find?_some hx)
    by_cases hv : key value = q
    · simp [f, hq, hv]
    · have hv' : (key value == q) = false := by simpa using hv
      have hv'' : (q == key value) = false := by simpa using Ne.symm hv
      simp [f, hq, hv', hv'']

def replaceFirst (index : Buckets κ α) (key : κ) (value : α) : Buckets κ α :=
  index.insert key ((first index key).toList.map fun _ => value)

theorem first_replaceFirst (index : Buckets κ α) (key : κ) (value : α) (q : κ) :
    first (replaceFirst index key value) q =
      if key == q then (first index q).map (fun _ => value) else first index q := by
  by_cases h : key = q
  · subst q
    simp only [replaceFirst, first, bucket, TreeMap.getElem?_insert_self, Option.getD_some]
    cases index[key]? <;> simp
  · have hn : compare key q ≠ .eq := by simpa using h
    have hb : (key == q) = false := by simpa using h
    simp only [replaceFirst, first, bucket, TreeMap.getElem?_insert, hn, ↓reduceIte, hb, Bool.false_eq_true]

/-- A query index certified against its source sequence. The sequence occurs only in the type;
updates retain the tree and an erased correctness proof, not a second runtime copy of the source. -/
structure First (key : α → κ) (xs : List α) where
  data : Buckets κ α
  correct : ∀ q, first data q = xs.find? (fun x => key x == q)

def First.build (key : α → κ) (xs : List α) : First key xs :=
  ⟨ofList key xs, first_ofList key xs⟩

def First.find {key : α → κ} {xs : List α} (ctx : First key xs) (q : κ) : Option α :=
  first ctx.data q

omit [TransOrd κ] [LawfulEqOrd κ] [LawfulBEq κ] in
theorem First.find_eq {key : α → κ} {xs : List α} (ctx : First key xs) (q : κ) :
    ctx.find q = xs.find? (fun x => key x == q) := ctx.correct q

/-- Update one tree key for the source operation that replaces every value of that key.
Only first-match observations are represented, including duplicate and absent source keys. -/
def First.replace {key : α → κ} {xs : List α} (ctx : First key xs) (value : α) :
    First key (replaceKey key value xs) :=
  ⟨replaceFirst ctx.data (key value) value, by
    intro q
    rw [first_replaceFirst, ctx.correct, find_replaceKey]⟩

/-- A maintained index answers exactly as rebuilding from the updated source, at every key. -/
theorem First.replace_eq_rebuild {key : α → κ} {xs : List α} (ctx : First key xs) (value : α) (q : κ) :
    (ctx.replace value).find q = (First.build key (replaceKey key value xs)).find q := by
  rw [First.find_eq, First.find_eq]

end Obend.Vault.Index
