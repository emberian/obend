module
/-
# Obend.Logic.GuardedLob — tick-indexed Löb induction, C4 linearization, epoch change certificates, `Asm(Core4)`

Card `K4` ("Löb, not Kan"). Four parts, each over the real `Obend.Core.Term` reduction semantics
or the real `Obend.Logic` composition and certificate types.

**§1 Guarded recursion.** `GuardedPred := Nat → Prop`, the modality `Later P k := ∀ j < k, P j`,
and `fix_lob : (∀ k, Later P k → P k) → ∀ k, P k`. A `Contractive` operator has a guarded fixed
point `guardedFix F` (the diagonal of its finite approximants) with `guardedFix_unfold` and
`guardedFix_unique`. `StepContract Q k t` says every value `t` reaches within `k` reduction steps
satisfies `Q`. `openRec_stepContract_lob` is Löb induction for an open-recursive object
`fix s i`: the unfolding `Step.fix` is the tick that guards the self reference, so the contract
of the unfolded body at budget `k` may assume the contract of the object itself at every budget
`≤ k`. `stepContract_all_iff` transfers the indexed family back to `Evaluates`.
`selfLoop_diverges` is the smallest use: the object whose method returns `self` reaches no value.

**§2 C4 linearization.** `c4Merge` is the C3/C4 merge: take the first head that occurs in no
tail, strip it from every head, repeat; `none` on inconsistent precedence. `c4Merge_nodup` and
`c4Merge_sublist_precedence` are its two laws. `c4Linearize` linearizes a DAG of named layers
(`none` on a cycle); `c4LinearizeFuel_nodup` and `c4LinearizeFuel_precedence` lift the laws, and
`c4LinearizeFuel_single_parent` shows single inheritance linearizes to a prepend.
`c4ChainRefines` folds a linearized layer stack into an `Obend.Logic.Composition`, and
`c4Prepend_preserves_superClaimCert` transports every accepted `superClaimCheck` certificate of an
inherited layer unchanged under new top layers through `T3_super_claim_frame`: the `super`
supports hold by construction (the stack beneath the layer is the same list), so only the `self`
supports are asked of the wrapper.

**§3 Epoch change certificates.** An `EpochBook` is an array of `(key, body)` sorted strictly by
key; `lookupEpochFast` is a binary search equal to the linear specification
(`lookupEpochFast_eq_spec`). `verifyChangeCertExec B₁ B₂ U` checks both books well formed, the
same keys, and equal bodies on the unchanged set `U`. `changeCert_preservedOn_sound`: a call
whose free frame indices name only keys of `U` links to the same term against both books, so it
evaluates identically at every fuel. `ChangeCertificate` packages this with an `IndexedBridge`
(equality on `U`, a caller-chosen relation off it); `changeCert_linkable_iff` says a change with
the same keys leaves no dangling reference.

**§4 `Asm(Core4)`.** Assemblies over `Term` realizers under weak-head call-by-name, closed under
head expansion. A morphism stores its `tracker : Term` as data. `quotAssembly` and
`AsmCore4Hom.quotLift` lift along `Quot.mk` without `Quot.sound` or choice, and
`(f.quotLift R h).tracker = f.tracker` holds by `rfl`.

What is not here: `IndexedBridge` carries the off-`U` relation but no congruence theorem for it
(observational equivalence of `Term`s is not yet a congruence under substitution in this tree);
the sorted-array search is repeated in `Obend.Codec.DetCbor` over byte keys and wants one shared
home.
-/

public import Obend.Logic.Obligation
import all Obend.Logic.Obligation
public import Obend.Law.Proofs.Run

public section

namespace Obend.Logic.GuardedLob

open Obend.Core.Term
open Obend.Core.TermTraverse (encode)
open Obend.Equiv
open Obend.Logic

set_option autoImplicit false

universe u v w

/-! ## 1. Tick-indexed guarded recursion and Löb induction -/

/-- A predicate indexed by a step budget. -/
abbrev GuardedPred := Nat → Prop

/-- Downward closed in the budget: what holds with more steps holds with fewer. -/
def AntitonePred (P : GuardedPred) : Prop := ∀ {i j : Nat}, i ≤ j → P j → P i

/-- The later modality `▷ P`: `P` at every strictly smaller budget. -/
@[expose] def Later (P : GuardedPred) : GuardedPred := fun k => ∀ j, j < k → P j

/-- **Löb induction.** A property that holds now whenever it holds later holds always. -/
theorem fix_lob {P : GuardedPred} (h : ∀ k, Later P k → P k) : ∀ k, P k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih => exact h k ih

theorem later_zero (P : GuardedPred) : Later P 0 := fun _ hj => absurd hj (Nat.not_lt_zero _)

theorem later_of_antitone {P : GuardedPred} (hP : AntitonePred P) {k : Nat} (h : P k) : Later P k :=
  fun _ hj => hP (Nat.le_of_lt hj) h

theorem later_mono {P Q : GuardedPred} (h : ∀ k, P k → Q k) (k : Nat) : Later P k → Later Q k :=
  fun hl j hj => h j (hl j hj)

/-- `F P` at budget `k` reads `P` only at budgets below `k`. -/
def Contractive (F : GuardedPred → GuardedPred) : Prop :=
  ∀ (P Q : GuardedPred) (k : Nat), (∀ j, j < k → (P j ↔ Q j)) → (F P k ↔ F Q k)

/-- The finite approximants `F^n ⊤`. -/
def guardedApprox (F : GuardedPred → GuardedPred) : Nat → GuardedPred
  | 0 => fun _ => True
  | n + 1 => F (guardedApprox F n)

/-- The guarded fixed point: the diagonal of the approximants. -/
def guardedFix (F : GuardedPred → GuardedPred) : GuardedPred :=
  fun k => guardedApprox F (k + 1) k

/-- Approximants deeper than the budget agree at that budget. -/
theorem guardedApprox_stable {F : GuardedPred → GuardedPred} (hF : Contractive F) :
    ∀ (k n m : Nat), k < n → k < m → (guardedApprox F n k ↔ guardedApprox F m k) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro n m hn hm
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact hF (guardedApprox F n') (guardedApprox F m') k
      (fun j hj => ih j hj n' m' (by omega) (by omega))

theorem guardedFix_unfold {F : GuardedPred → GuardedPred} (hF : Contractive F) :
    ∀ k, guardedFix F k ↔ F (guardedFix F) k := by
  intro k
  exact hF (guardedApprox F k) (guardedFix F) k
    (fun j hj => guardedApprox_stable hF j k (j + 1) hj (Nat.lt_succ_self j))

/-- Any solution of the guarded equation is the guarded fixed point; proved by `fix_lob`. -/
theorem guardedFix_unique {F : GuardedPred → GuardedPred} (hF : Contractive F) {P : GuardedPred}
    (hP : ∀ k, P k ↔ F P k) : ∀ k, (P k ↔ guardedFix F k) := by
  apply fix_lob
  intro k hlater
  exact (hP k).trans ((hF P (guardedFix F) k hlater).trans (guardedFix_unfold hF k).symm)

/-- Exactly `n` reduction steps. -/
inductive StepsN : Nat → Term → Term → Prop where
  | refl (t : Term) : StepsN 0 t t
  | next {n : Nat} {a b c : Term} : Step a b → StepsN n b c → StepsN (n + 1) a c

theorem StepsN.steps {n : Nat} {a b : Term} (h : StepsN n a b) : Steps a b := by
  induction h with
  | refl t => exact .refl t
  | next s _ ih => exact .next s ih

theorem stepsN_of_steps {a b : Term} (h : Steps a b) : ∃ n, StepsN n a b := by
  induction h with
  | refl t => exact ⟨0, .refl t⟩
  | next s _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .next s hn⟩

/-- The step-indexed contract: every value `t` reaches within `k` steps satisfies `Q`. -/
def StepContract (Q : Term → Prop) (k : Nat) (t : Term) : Prop :=
  ∀ (n : Nat) (v : Term), n ≤ k → StepsN n t v → Value v → Q v

theorem stepContract_antitone (Q : Term → Prop) (t : Term) :
    AntitonePred (fun k => StepContract Q k t) :=
  fun hij h n v hn hs hv => h n v (Nat.le_trans hn hij) hs hv

/-- The indexed family is the contract on evaluation: nothing is lost by the budgets. -/
theorem stepContract_all_iff (Q : Term → Prop) (t : Term) :
    (∀ k, StepContract Q k t) ↔ ∀ v, Evaluates t v → Q v := by
  constructor
  · rintro h v ⟨hs, hv⟩
    obtain ⟨n, hn⟩ := stepsN_of_steps hs
    exact h n n v (Nat.le_refl n) hn hv
  · intro h k n v _ hs hv
    exact h v ⟨hs.steps, hv⟩

/-- One reduction step spends one tick: the contract moves back across it. -/
theorem stepContract_step {Q : Term → Prop} {k : Nat} {t t' : Term} (s : Step t t')
    (h : StepContract Q k t') : StepContract Q (k + 1) t := by
  intro n v hn hs hv
  cases hs with
  | refl => exact absurd s (fun s => Obend.Law.value_no_step hv s)
  | next s' hrest =>
    rw [Obend.Law.step_deterministic s' s] at hrest
    exact h _ v (by omega) hrest hv

/-- A term that is not a value owes nothing at budget zero. -/
theorem stepContract_zero {Q : Term → Prop} {t : Term} (hnv : ¬ Value t) : StepContract Q 0 t := by
  intro n v hn hs hv
  have h0 : n = 0 := by omega
  subst h0
  cases hs
  exact absurd hv hnv

/-- **Löb induction for an open-recursive object.** To prove the step contract of `fix s i` at
every budget, prove the contract of its unfolding `s (fix s i) i` at budget `k` assuming the
contract of `fix s i` itself at every budget `≤ k`. The unfolding step is the guard. -/
theorem openRec_stepContract_lob (Q : Term → Prop) (s i : Term)
    (hbody : ∀ k, Later (fun j => StepContract Q j (.fix s i)) (k + 1) →
      StepContract Q k (.app (.app s (.fix s i)) i)) :
    ∀ k, StepContract Q k (.fix s i) := by
  apply fix_lob
  intro k hlater
  cases k with
  | zero => exact stepContract_zero (fun hv => by cases hv)
  | succ k => exact stepContract_step (Step.fix s i) (hbody k hlater)

/-- The same, read at the evaluation relation. -/
theorem openRec_evaluates_lob (Q : Term → Prop) (s i : Term)
    (hbody : ∀ k, Later (fun j => StepContract Q j (.fix s i)) (k + 1) →
      StepContract Q k (.app (.app s (.fix s i)) i)) :
    ∀ v, Evaluates (.fix s i) v → Q v :=
  (stepContract_all_iff Q (.fix s i)).1 (openRec_stepContract_lob Q s i hbody)

/-- The specification whose object is its own self: `λself. λinherited. self`. -/
@[expose] def selfLoopSpec : Term := .lam (.lam (.bound 1))

/-- The self-returning object reaches no value, at any inherited seed: its contract `False`
holds at every budget by Löb induction, the self reference being two steps behind the guard. -/
theorem selfLoop_diverges (i : Term) : ∀ v, ¬ Evaluates (.fix selfLoopSpec i) v := by
  intro v hev
  refine openRec_evaluates_lob (fun _ => False) selfLoopSpec i ?_ v hev
  intro k hlater
  have s1 : Step (.app (.app selfLoopSpec (.fix selfLoopSpec i)) i)
      (.app (.lam ((Term.fix selfLoopSpec i).rename Nat.succ)) i) := by
    have hb := Step.application i (Step.beta (.lam (.bound 1)) (.fix selfLoopSpec i))
    have he : instantiate (.lam (.bound 1)) (.fix selfLoopSpec i) =
        .lam ((Term.fix selfLoopSpec i).rename Nat.succ) := by
      simp [instantiate, Term.substitute, liftSubstitution]
    rw [he] at hb
    exact hb
  have s2 : Step (.app (.lam ((Term.fix selfLoopSpec i).rename Nat.succ)) i)
      (.fix selfLoopSpec i) := by
    have hb := Step.beta ((Term.fix selfLoopSpec i).rename Nat.succ) i
    rw [instantiate_eq, shift_one_cancel] at hb
    exact hb
  match k with
  | 0 => exact stepContract_zero (fun hv => by cases hv)
  | 1 =>
    exact stepContract_step s1 (stepContract_zero (fun hv => by cases hv))
  | k + 2 =>
    exact stepContract_step s1 (stepContract_step s2 (hlater k (by omega)))

/-! ## 2. C4 method resolution order -/

/-- Total length of the sequences still to merge: the merge's fuel. -/
def c4Total (seqs : List (List String)) : Nat := seqs.foldr (fun s acc => s.length + acc) 0

/-- A head is good when it occurs in the tail of no sequence. -/
def c4Good (seqs : List (List String)) (h : String) : Bool :=
  !seqs.any (fun s => s.tail.contains h)

/-- The first good head, in sequence order. -/
def c4Pick (seqs : List (List String)) : Option String :=
  (seqs.filterMap List.head?).find? (c4Good seqs)

/-- Strip `h` from the head of a sequence. -/
def c4StripOne (h : String) : List String → List String
  | [] => []
  | x :: xs => if x == h then xs else x :: xs

def c4Strip (h : String) (seqs : List (List String)) : List (List String) :=
  seqs.map (c4StripOne h)

/-- The C3/C4 merge at a fuel: `none` when no head is good (inconsistent precedence). -/
def c4MergeFuel : Nat → List (List String) → Option (List String)
  | 0, _ => none
  | fuel + 1, seqs =>
    if seqs.all List.isEmpty then some []
    else
      match c4Pick seqs with
      | none => none
      | some h => (c4MergeFuel fuel (c4Strip h seqs)).map (h :: ·)

/-- **The C4 merge.** Each round removes at least one element, so the total length suffices. -/
def c4Merge (seqs : List (List String)) : Option (List String) :=
  c4MergeFuel (c4Total seqs + 1) seqs

theorem c4Good_spec {seqs : List (List String)} {h : String} (hg : c4Good seqs h = true) :
    ∀ s ∈ seqs, h ∉ s.tail := by
  simpa [c4Good] using hg

theorem c4Pick_spec {seqs : List (List String)} {h : String} (hp : c4Pick seqs = some h) :
    (∃ s ∈ seqs, s.head? = some h) ∧ c4Good seqs h = true := by
  have hg := List.find?_some hp
  have hm := List.mem_of_find?_eq_some hp
  rw [List.mem_filterMap] at hm
  exact ⟨hm, hg⟩

theorem c4StripOne_subset {h x : String} {s : List String} (hx : x ∈ c4StripOne h s) : x ∈ s := by
  cases s with
  | nil => exact hx
  | cons y ys =>
    by_cases hy : (y == h) = true
    · simp only [c4StripOne, hy, ↓reduceIte] at hx
      exact List.mem_cons_of_mem _ hx
    · simp only [c4StripOne, hy] at hx
      exact hx

theorem c4StripOne_nodup {h : String} {s : List String} (hs : s.Nodup) : (c4StripOne h s).Nodup := by
  cases s with
  | nil => exact hs
  | cons y ys =>
    by_cases hy : (y == h) = true
    · simp only [c4StripOne, hy, ↓reduceIte]
      exact (List.nodup_cons.1 hs).2
    · simp only [c4StripOne, hy]
      exact hs

theorem not_mem_c4StripOne {h : String} {s : List String} (ht : h ∉ s.tail) :
    h ∉ c4StripOne h s := by
  cases s with
  | nil => intro hm; cases hm
  | cons y ys =>
    by_cases hy : (y == h) = true
    · simp only [c4StripOne, hy, ↓reduceIte]
      exact ht
    · simp only [c4StripOne, hy]
      intro hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact hy (beq_self_eq_true _)
      · exact ht hm

/-- Every element of the merge comes from some sequence. -/
theorem c4MergeFuel_mem : ∀ (fuel : Nat) (seqs : List (List String)) (mro : List String),
    c4MergeFuel fuel seqs = some mro → ∀ x ∈ mro, ∃ s ∈ seqs, x ∈ s
  | 0, _, _, h => by simp [c4MergeFuel] at h
  | fuel + 1, seqs, mro, h => by
    unfold c4MergeFuel at h
    by_cases he : seqs.all List.isEmpty = true
    · rw [ite_eq_left he] at h
      cases h
      intro x hx
      cases hx
    · rw [ite_eq_right he] at h
      cases hp : c4Pick seqs with
      | none => simp [hp] at h
      | some hd =>
        simp only [hp] at h
        obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · obtain ⟨⟨s, hs, hh⟩, _⟩ := c4Pick_spec hp
          exact ⟨s, hs, List.mem_of_mem_head? hh⟩
        · obtain ⟨s', hs', hx'⟩ := c4MergeFuel_mem fuel _ _ hr x hx
          obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs'
          exact ⟨s, hs, c4StripOne_subset hx'⟩

theorem c4MergeFuel_nodup : ∀ (fuel : Nat) (seqs : List (List String)) (mro : List String),
    (∀ s ∈ seqs, s.Nodup) → c4MergeFuel fuel seqs = some mro → mro.Nodup
  | 0, _, _, _, h => by simp [c4MergeFuel] at h
  | fuel + 1, seqs, mro, hn, h => by
    unfold c4MergeFuel at h
    by_cases he : seqs.all List.isEmpty = true
    · rw [ite_eq_left he] at h
      cases h
      exact List.nodup_nil
    · rw [ite_eq_right he] at h
      cases hp : c4Pick seqs with
      | none => simp [hp] at h
      | some hd =>
        simp only [hp] at h
        obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
        have hnt := c4Good_spec (c4Pick_spec hp).2
        have hn' : ∀ s ∈ c4Strip hd seqs, s.Nodup := by
          intro s' hs'
          obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs'
          exact c4StripOne_nodup (hn s hs)
        refine List.nodup_cons.2 ⟨?_, c4MergeFuel_nodup fuel _ _ hn' hr⟩
        intro hmem
        obtain ⟨s', hs', hx'⟩ := c4MergeFuel_mem fuel _ _ hr hd hmem
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs'
        exact not_mem_c4StripOne (hnt s hs) hx'

theorem c4MergeFuel_sublist : ∀ (fuel : Nat) (seqs : List (List String)) (mro : List String),
    c4MergeFuel fuel seqs = some mro → ∀ s ∈ seqs, s.Sublist mro
  | 0, _, _, h => by simp [c4MergeFuel] at h
  | fuel + 1, seqs, mro, h => by
    unfold c4MergeFuel at h
    by_cases he : seqs.all List.isEmpty = true
    · rw [ite_eq_left he] at h
      cases h
      intro s hs
      have hs0 : s = [] := List.isEmpty_iff.1 (List.all_eq_true.1 he s hs)
      rw [hs0]
      exact List.Sublist.refl _
    · rw [ite_eq_right he] at h
      cases hp : c4Pick seqs with
      | none => simp [hp] at h
      | some hd =>
        simp only [hp] at h
        obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
        intro s hs
        cases s with
        | nil => exact List.nil_sublist _
        | cons x xs =>
          have hmem : c4StripOne hd (x :: xs) ∈ c4Strip hd seqs := List.mem_map.2 ⟨_, hs, rfl⟩
          have ih := c4MergeFuel_sublist fuel _ _ hr _ hmem
          by_cases hx : (x == hd) = true
          · have hst : c4StripOne hd (x :: xs) = xs := by simp [c4StripOne, hx]
            rw [hst] at ih
            have hxe : x = hd := beq_iff_eq.1 hx
            subst hxe
            exact ih.cons_cons _
          · have hst : c4StripOne hd (x :: xs) = x :: xs := by simp [c4StripOne, hx]
            rw [hst] at ih
            exact ih.cons _

/-- **The merge has no duplicate** when no input sequence has one. -/
theorem c4Merge_nodup {seqs : List (List String)} {mro : List String}
    (hn : ∀ s ∈ seqs, s.Nodup) (h : c4Merge seqs = some mro) : mro.Nodup :=
  c4MergeFuel_nodup _ seqs mro hn h

/-- **The merge preserves every input order**: each sequence is a sublist of the result. -/
theorem c4Merge_sublist_precedence {seqs : List (List String)} {mro : List String}
    (h : c4Merge seqs = some mro) : ∀ s ∈ seqs, s.Sublist mro :=
  c4MergeFuel_sublist _ seqs mro h

/-- A named layer of an inheritance DAG. -/
structure LayerNode where
  name : String
  layer : Layer
  parents : List String

def findNode (nodes : List LayerNode) (name : String) : Option LayerNode :=
  nodes.find? (·.name == name)

/-- Map a partial function over a list; `none` if it fails anywhere. -/
def collectSome {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: as =>
    match f a, collectSome f as with
    | some b, some bs => some (b :: bs)
    | _, _ => none

theorem collectSome_spec {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), collectSome f l = some r →
      (∀ b ∈ r, ∃ a ∈ l, f a = some b) ∧ (∀ a ∈ l, ∃ b ∈ r, f a = some b)
  | [], r, h => by
    cases h
    exact ⟨fun _ hb => (by cases hb), fun _ ha => (by cases ha)⟩
  | a :: as, r, h => by
    unfold collectSome at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hrec : collectSome f as with
      | none => simp [hfa, hrec] at h
      | some bs =>
        simp only [hfa, hrec, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := collectSome_spec f as bs hrec
        constructor
        · intro b' hb'
          rcases List.mem_cons.1 hb' with rfl | hb'
          · exact ⟨a, List.mem_cons_self, hfa⟩
          · obtain ⟨a', ha', hf'⟩ := h1 b' hb'
            exact ⟨a', List.mem_cons_of_mem _ ha', hf'⟩
        · intro a' ha'
          rcases List.mem_cons.1 ha' with rfl | ha'
          · exact ⟨b, List.mem_cons_self, hfa⟩
          · obtain ⟨b', hb', hf'⟩ := h2 a' ha'
            exact ⟨b', List.mem_cons_of_mem _ hb', hf'⟩

/-- C4 linearization at a depth fuel: `L[C] = C :: merge (L[P₁], …, L[Pₙ], [P₁, …, Pₙ])`.
`none` on a missing node, a repeated parent, an inconsistent merge, or a cycle. -/
def c4LinearizeFuel (nodes : List LayerNode) : Nat → String → Option (List String)
  | 0, _ => none
  | fuel + 1, name =>
    (findNode nodes name).bind fun node =>
    (collectSome (c4LinearizeFuel nodes fuel) node.parents).bind fun pls =>
    (c4Merge (pls ++ [node.parents])).bind fun merged =>
    if node.parents.Nodup ∧ name ∉ merged then some (name :: merged) else none

/-- **C4 linearization** of `name` in `nodes`; an acyclic DAG is no deeper than its node count. -/
def c4Linearize (nodes : List LayerNode) (name : String) : Option (List String) :=
  c4LinearizeFuel nodes (nodes.length + 1) name

theorem c4LinearizeFuel_nodup (nodes : List LayerNode) :
    ∀ (fuel : Nat) (name : String) (mro : List String),
      c4LinearizeFuel nodes fuel name = some mro → mro.Nodup
  | 0, _, _, h => by simp [c4LinearizeFuel] at h
  | fuel + 1, name, mro, h => by
    unfold c4LinearizeFuel at h
    obtain ⟨node, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨pls, hpls, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨merged, hmerge, h⟩ := Option.bind_eq_some_iff.1 h
    by_cases hc : node.parents.Nodup ∧ name ∉ merged
    · rw [ite_eq_left hc] at h
      cases h
      have hn : ∀ s ∈ pls ++ [node.parents], s.Nodup := by
        intro s hs
        rcases List.mem_append.1 hs with hs | hs
        · obtain ⟨p, _, hp⟩ := (collectSome_spec _ _ _ hpls).1 s hs
          exact c4LinearizeFuel_nodup nodes fuel p s hp
        · rw [List.mem_singleton.1 hs]
          exact hc.1
      exact List.nodup_cons.2 ⟨hc.2, c4Merge_nodup hn hmerge⟩
    · rw [ite_eq_right hc] at h
      cases h

/-- **Monotonicity and local precedence.** The linearization of a node starts with the node; the
rest keeps the declared parent order and the whole linearization of every parent, as sublists. -/
theorem c4LinearizeFuel_precedence (nodes : List LayerNode) {fuel : Nat} {name : String}
    {mro : List String} (h : c4LinearizeFuel nodes (fuel + 1) name = some mro) :
    ∃ (node : LayerNode) (merged : List String),
      findNode nodes name = some node ∧ mro = name :: merged ∧ node.parents.Sublist merged ∧
        ∀ p ∈ node.parents, ∃ pm, c4LinearizeFuel nodes fuel p = some pm ∧ pm.Sublist merged := by
  unfold c4LinearizeFuel at h
  obtain ⟨node, hnode, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨pls, hpls, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨merged, hmerge, h⟩ := Option.bind_eq_some_iff.1 h
  by_cases hc : node.parents.Nodup ∧ name ∉ merged
  · rw [ite_eq_left hc] at h
    cases h
    have hsub := c4Merge_sublist_precedence hmerge
    refine ⟨node, merged, hnode, rfl, hsub _ (List.mem_append_right _ List.mem_cons_self), ?_⟩
    intro p hp
    obtain ⟨pm, hpm, hf⟩ := (collectSome_spec _ _ _ hpls).2 p hp
    exact ⟨pm, hf, hsub _ (List.mem_append_left _ hpm)⟩
  · rw [ite_eq_right hc] at h
    cases h

/-- Merging one duplicate-free sequence returns it. -/
theorem c4MergeFuel_single : ∀ (l : List String) (fuel : Nat), l.Nodup → l.length < fuel →
    c4MergeFuel fuel [l, []] = some l
  | [], fuel, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [c4MergeFuel]
  | x :: xs, fuel, hn, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hx : x ∉ xs := (List.nodup_cons.1 hn).1
    have hpick : c4Pick [x :: xs, []] = some x := by
      simp [c4Pick, c4Good, hx]
    have hstrip : c4Strip x [x :: xs, []] = [xs, []] := by
      simp [c4Strip, c4StripOne]
    unfold c4MergeFuel
    have he : ¬ ([x :: xs, []].all List.isEmpty = true) := by simp
    rw [ite_eq_right he]
    simp only [hpick, hstrip]
    rw [c4MergeFuel_single xs f (List.nodup_cons.1 hn).2 (by simp at hf; omega)]
    rfl

/-- Merging a parent's linearization with the one-parent list returns the linearization. -/
theorem c4Merge_single_parent (p : String) (rest : List String) (hn : (p :: rest).Nodup) :
    c4Merge [p :: rest, [p]] = some (p :: rest) := by
  have hp : p ∉ rest := (List.nodup_cons.1 hn).1
  have hfuel : c4Total [p :: rest, [p]] + 1 = (rest.length + 2) + 1 := by
    simp [c4Total]
  have hpick : c4Pick [p :: rest, [p]] = some p := by
    simp [c4Pick, c4Good, hp]
  have hstrip : c4Strip p [p :: rest, [p]] = [rest, []] := by
    simp [c4Strip, c4StripOne]
  unfold c4Merge
  rw [hfuel]
  unfold c4MergeFuel
  have he : ¬ ([p :: rest, [p]].all List.isEmpty = true) := by simp
  rw [ite_eq_right he]
  simp only [hpick, hstrip]
  rw [c4MergeFuel_single rest (rest.length + 2) (List.nodup_cons.1 hn).2 (by omega)]
  rfl

/-- **Single inheritance is a prepend.** A node with the one parent `p` linearizes to itself in
front of `p`'s linearization. -/
theorem c4LinearizeFuel_single_parent (nodes : List LayerNode) {fuel : Nat} {c p : String}
    {node : LayerNode} {rest : List String} (hnode : findNode nodes c = some node)
    (hpar : node.parents = [p]) (hp : c4LinearizeFuel nodes fuel p = some (p :: rest))
    (hc : c ∉ p :: rest) :
    c4LinearizeFuel nodes (fuel + 1) c = some (c :: p :: rest) := by
  have hn : (p :: rest).Nodup := c4LinearizeFuel_nodup nodes fuel p _ hp
  unfold c4LinearizeFuel
  simp only [hnode, hpar, Option.bind_some, collectSome, hp, List.cons_append, List.nil_append,
    c4Merge_single_parent p rest hn]
  rw [ite_eq_left ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, hc⟩]

/-- Fold a linearized layer stack over a seed into a composition (outermost layer first). -/
def c4ChainRefines (mro : List Layer) (seed : List (String × Term)) : Option Composition :=
  match mro with
  | [] => none
  | top :: below => some ⟨top, below, seed⟩

/-- The composition of `name`'s C4 linearization in `nodes` over `seed`. -/
def c4Composition (nodes : List LayerNode) (name : String) (seed : List (String × Term)) :
    Option Composition :=
  (c4Linearize nodes name).bind fun mro =>
  (collectSome (fun n => (findNode nodes n).map (·.layer)) mro).bind fun layers =>
  c4ChainRefines layers seed

/-- Wrap a composition with new overriding layers on top. -/
@[expose] def prependLayers (C : Composition) (newTop : Layer) (mid : List Layer) : Composition :=
  ⟨newTop, mid ++ C.layers, C.seed⟩

theorem drop_length_append {α : Type} (mid l : List α) (n : Nat) :
    (mid ++ l).drop (mid.length + n) = l.drop n := by
  induction mid with
  | nil => simp
  | cons a t ih =>
    have hlen : (a :: t).length + n = (t.length + n) + 1 := by simp; omega
    rw [hlen]
    exact ih

/-- The stack beneath an inherited layer is unchanged by a prepend, so `super.m` unfolds there
exactly as before. -/
theorem superSymUnfold_prepend (C : Composition) (newTop : Layer) (mid : List Layer)
    (selfIdx j : Nat) (m : String) :
    superSymUnfold (prependLayers C newTop mid) selfIdx (mid.length + 1 + j) m =
      superSymUnfold C selfIdx j m := by
  have hdrop : (prependLayers C newTop mid).layers.drop (mid.length + 1 + j + 1) =
      C.layers.drop (j + 1) := by
    have hidx : mid.length + 1 + j + 1 = (mid.length + (j + 1)) + 1 := by omega
    rw [hidx]
    exact drop_length_append mid C.layers (j + 1)
  unfold superSymUnfold
  rw [hdrop]
  rfl

/-- **C4 prepend preserves every inherited certificate.** An accepted `superClaimCheck`
certificate of layer `o.layer` of `o.comp` stays accepted, with the same traced supports, at the
same layer of the composition wrapped by new top layers, provided the wrapper's `symUnfold`
agrees on the certificate's `selfSupports`. Nothing is asked of its `superSupports`, and no
parent layer is re-proved. -/
theorem c4Prepend_preserves_superClaimCert {k : Nat} {o : ClaimObj} {steps : List RStep}
    (h : superClaimCheck k o steps = .ok) (newTop : Layer) (mid : List Layer)
    (hself : ∀ s ∈ (mkSuperClaimCert k o steps).selfSupports,
      optEq (symUnfold (prependLayers o.comp newTop mid) (o.arity + 1) s.member) s.unfolded = true)
    (hwf : ({ o with comp := prependLayers o.comp newTop mid,
                     layer := mid.length + 1 + o.layer } : ClaimObj).wellFormed = true) :
    superClaimCheck k { o with comp := prependLayers o.comp newTop mid,
                               layer := mid.length + 1 + o.layer } steps = .ok ∧
      superSupports { o with comp := prependLayers o.comp newTop mid,
                             layer := mid.length + 1 + o.layer } steps = superSupports o steps := by
  refine T3_super_claim_frame h ?_ hwf
  intro sp hsp
  have hold := superSupports_holds_self o steps sp hsp
  have hall := mem_allSupports_of_mem_superSupports (k := k) hsp
  obtain ⟨rcv, m, unf⟩ := sp
  cases rcv with
  | selfReceiver =>
    have hmem : (⟨m, unf⟩ : Support) ∈ (mkSuperClaimCert k o steps).selfSupports := by
      rcases List.mem_append.1 hall with hl | hr
      · obtain ⟨s, hs, he⟩ := List.mem_map.1 hl
        cases s
        cases he
        exact hs
      · obtain ⟨s, _, he⟩ := List.mem_map.1 hr
        cases he
    exact hself _ hmem
  | superReceiver =>
    simp only [SuperSupport.holds] at hold ⊢
    rw [superSymUnfold_prepend]
    exact hold

/-! ## 3. Epoch-pinned books and change certificates -/

/-- An immutable epoch snapshot: `(key, body)` entries, strictly sorted by key. -/
structure EpochBook where
  entries : Array (String × Term)

namespace EpochBook

def keys (B : EpochBook) : List String := B.entries.toList.map (·.1)

/-- The specification of lookup: the first entry with the key. -/
def lookupSpec (B : EpochBook) (k : String) : Option Term :=
  (B.entries.toList.find? (fun e => e.1 == k)).map (·.2)

/-- Well formed: keys strictly ascending (so unique), every body closed. -/
def WF (B : EpochBook) : Prop :=
  B.entries.toList.Pairwise (fun x y => x.1 < y.1) ∧ ∀ e ∈ B.entries.toList, Closed e.2

end EpochBook

/-- Adjacent entries strictly ascending by key. -/
def sortedByB {α : Type} (key : α → String) : List α → Bool
  | a :: b :: rest => decide (key a < key b) && sortedByB key (b :: rest)
  | _ => true

theorem sortedByB_sound {α : Type} (key : α → String) :
    ∀ (l : List α), sortedByB key l = true → l.Pairwise (fun x y => key x < key y)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: rest, h => by
    simp only [sortedByB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := sortedByB_sound key (b :: rest) h.2
    refine List.pairwise_cons.2 ⟨?_, ih⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · exact String.lt_trans h.1 ((List.pairwise_cons.1 ih).1 y hy)

/-- The decided form of `EpochBook.WF`, one pass. -/
def EpochBook.wfB (B : EpochBook) : Bool :=
  sortedByB (·.1) B.entries.toList && B.entries.toList.all (fun e => Obend.Law.closedB e.2)

theorem EpochBook.wf_of_wfB {B : EpochBook} (h : B.wfB = true) : B.WF := by
  simp only [EpochBook.wfB, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨sortedByB_sound _ _ h.1, fun e he => closed_of_closedB (h.2 e he)⟩

/-- Binary search for the entry with key `k` in the window `[lo, hi)`. -/
def bsearchFuel {α : Type} (key : α → String) (a : Array α) (k : String) :
    Nat → Nat → Nat → Option α
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if lo < hi then
      match a[(lo + hi) / 2]? with
      | none => none
      | some e =>
        if key e == k then some e
        else if key e < k then bsearchFuel key a k fuel ((lo + hi) / 2 + 1) hi
        else bsearchFuel key a k fuel lo ((lo + hi) / 2)
    else none

/-- `O(log n)` search of an array sorted by `key`. -/
def sortedSearch {α : Type} (key : α → String) (a : Array α) (k : String) : Option α :=
  bsearchFuel key a k (a.size + 1) 0 a.size

theorem pairwise_getElem?_rel {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {i j : Nat} {x y : α},
      l[i]? = some x → l[j]? = some y → i < j → R x y
  | [], _, i, j, x, y, hi, _, _ => by simp at hi
  | a :: l, hp, i, j, x, y, hi, hj, hij => by
    cases j with
    | zero => omega
    | succ j =>
      rw [List.getElem?_cons_succ] at hj
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at hi
        cases hi
        exact (List.pairwise_cons.1 hp).1 y (List.mem_of_getElem? hj)
      | succ i =>
        rw [List.getElem?_cons_succ] at hi
        exact pairwise_getElem?_rel (List.pairwise_cons.1 hp).2 hi hj (by omega)

theorem find?_of_sorted {α : Type} {key : α → String} :
    ∀ {l : List α}, l.Pairwise (fun x y => key x < key y) → ∀ {i : Nat} {e : α},
      l[i]? = some e → l.find? (fun x => key x == key e) = some e
  | [], _, i, e, h => by simp at h
  | a :: l, hp, i, e, h => by
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      cases h
      simp
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      have hlt := (List.pairwise_cons.1 hp).1 e (List.mem_of_getElem? h)
      have hne : (key a == key e) = false := by
        apply Bool.eq_false_iff.2
        intro hb
        rw [beq_iff_eq.1 hb] at hlt
        exact String.lt_irrefl _ hlt
      simp only [List.find?_cons, hne]
      exact find?_of_sorted (List.pairwise_cons.1 hp).2 h

/-- The search of a window equals the linear search, when no key outside the window is `k`. -/
theorem bsearchFuel_eq_find {α : Type} (key : α → String) (a : Array α) (k : String)
    (hs : a.toList.Pairwise (fun x y => key x < key y)) :
    ∀ (fuel lo hi : Nat), hi ≤ a.size → hi - lo < fuel →
      (∀ (i : Nat) (e : α), a.toList[i]? = some e → (i < lo ∨ hi ≤ i) → key e ≠ k) →
      bsearchFuel key a k fuel lo hi = a.toList.find? (fun e => key e == k)
  | 0, _, _, _, hf, _ => by omega
  | fuel + 1, lo, hi, hhi, hf, hout => by
    unfold bsearchFuel
    by_cases hlt : lo < hi
    · rw [ite_eq_left hlt]
      have hmid : (lo + hi) / 2 < a.size := by omega
      obtain ⟨e, he⟩ : ∃ e, a[(lo + hi) / 2]? = some e := ⟨a[(lo + hi) / 2], getElem?_pos a _ hmid⟩
      have hel : a.toList[(lo + hi) / 2]? = some e := by rw [Array.getElem?_toList]; exact he
      simp only [he]
      by_cases heq : (key e == k) = true
      · rw [ite_eq_left heq]
        have hk : key e = k := beq_iff_eq.1 heq
        subst hk
        exact (find?_of_sorted hs hel).symm
      · rw [ite_eq_right heq]
        have hne : key e ≠ k := fun hk => heq (beq_iff_eq.2 hk)
        by_cases hk : key e < k
        · rw [ite_eq_left hk]
          refine bsearchFuel_eq_find key a k hs fuel _ hi hhi (by omega) ?_
          intro i x hx hcase
          rcases hcase with hi' | hi'
          · by_cases hlo : i < lo
            · exact hout i x hx (Or.inl hlo)
            · by_cases him : i = (lo + hi) / 2
              · subst him
                rw [hel] at hx
                cases hx
                exact hne
              · have hxe : key x < key e := pairwise_getElem?_rel hs hx hel (by omega)
                intro hxk
                rw [hxk] at hxe
                exact String.lt_irrefl _ (String.lt_trans hxe hk)
          · exact hout i x hx (Or.inr hi')
        · rw [ite_eq_right hk]
          refine bsearchFuel_eq_find key a k hs fuel lo _ (by omega) (by omega) ?_
          intro i x hx hcase
          rcases hcase with hi' | hi'
          · exact hout i x hx (Or.inl hi')
          · by_cases hhi' : hi ≤ i
            · exact hout i x hx (Or.inr hhi')
            · by_cases him : i = (lo + hi) / 2
              · subst him
                rw [hel] at hx
                cases hx
                exact hne
              · have hxe : key e < key x := pairwise_getElem?_rel hs hel hx (by omega)
                intro hxk
                rw [hxk] at hxe
                exact hk hxe
    · rw [ite_eq_right hlt]
      symm
      rw [List.find?_eq_none]
      intro x hx
      obtain ⟨i, hi', hget⟩ := List.mem_iff_getElem.1 hx
      have hx' : a.toList[i]? = some x := by rw [List.getElem?_eq_getElem hi', hget]
      have hne := hout i x hx' (by omega)
      intro hb
      exact hne (beq_iff_eq.1 hb)

/-- **The binary search is the linear search** on an array sorted by key. -/
theorem sortedSearch_eq_find {α : Type} (key : α → String) (a : Array α) (k : String)
    (hs : a.toList.Pairwise (fun x y => key x < key y)) :
    sortedSearch key a k = a.toList.find? (fun e => key e == k) := by
  refine bsearchFuel_eq_find key a k hs (a.size + 1) 0 a.size (Nat.le_refl _) (by omega) ?_
  intro i e he hcase
  rcases hcase with h0 | hsz
  · omega
  · have hlt : i < a.toList.length := (List.getElem?_eq_some_iff.1 he).1
    simp at hlt
    omega

/-- `O(log n)` lookup in an epoch book. -/
def lookupEpochFast (B : EpochBook) (k : String) : Option Term :=
  (sortedSearch (·.1) B.entries k).map (·.2)

theorem lookupEpochFast_eq_spec {B : EpochBook} (hwf : B.WF) (k : String) :
    lookupEpochFast B k = B.lookupSpec k := by
  unfold lookupEpochFast EpochBook.lookupSpec
  rw [sortedSearch_eq_find _ _ _ hwf.1]

theorem EpochBook.lookup_closed {B : EpochBook} (hwf : B.WF) {k : String} {t : Term}
    (h : B.lookupSpec k = some t) : Closed t := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  exact hwf.2 e (List.mem_of_find?_eq_some he)

theorem EpochBook.lookupSpec_isSome_iff (B : EpochBook) (k : String) :
    (B.lookupSpec k).isSome = true ↔ k ∈ B.keys := by
  unfold EpochBook.lookupSpec EpochBook.keys
  rw [Option.isSome_map, List.find?_isSome, List.mem_map]
  constructor
  · rintro ⟨e, he, hk⟩
    exact ⟨e, he, beq_iff_eq.1 hk⟩
  · rintro ⟨e, he, hk⟩
    exact ⟨e, he, beq_iff_eq.2 hk⟩

/-- `p` at every index below `n`. -/
def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

theorem allBelow_iff (p : Nat → Bool) : ∀ (n : Nat), allBelow p n = true ↔ ∀ i, i < n → p i = true
  | 0 => by simp [allBelow]
  | n + 1 => by
    simp only [allBelow, Bool.and_eq_true, allBelow_iff p n]
    constructor
    · rintro ⟨hn, hlt⟩ i hi
      by_cases h : i = n
      · rw [h]; exact hn
      · exact hlt i (by omega)
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

/-- Same key at every index: one pass over both arrays. -/
def checkSameKeysExec (B₁ B₂ : EpochBook) : Bool :=
  B₁.entries.size == B₂.entries.size &&
    allBelow (fun i => (B₁.entries[i]?.map (·.1)) == (B₂.entries[i]?.map (·.1))) B₁.entries.size

theorem checkSameKeysExec_sound {B₁ B₂ : EpochBook} (h : checkSameKeysExec B₁ B₂ = true) :
    B₁.keys = B₂.keys := by
  simp only [checkSameKeysExec, Bool.and_eq_true, beq_iff_eq, allBelow_iff] at h
  obtain ⟨hsz, hall⟩ := h
  apply List.ext_getElem?
  intro i
  simp only [EpochBook.keys, List.getElem?_map, Array.getElem?_toList]
  by_cases hi : i < B₁.entries.size
  · exact hall i hi
  · rw [getElem?_neg B₁.entries i hi, getElem?_neg B₂.entries i (by omega)]

def optTermEq : Option Term → Option Term → Bool
  | none, none => true
  | some a, some b => Obend.Law.termEq a b
  | _, _ => false

theorem optTermEq_sound {x y : Option Term} (h : optTermEq x y = true) : x = y := by
  match x, y, h with
  | none, none, _ => rfl
  | some a, some b, h => rw [termEq_sound' h]

/-- Every key of `U` has the same body in both books: `|U|` binary searches in each. -/
def checkPreservedOnExec (B₁ B₂ : EpochBook) (U : Array String) : Bool :=
  U.toList.all (fun k => optTermEq (lookupEpochFast B₁ k) (lookupEpochFast B₂ k))

theorem checkPreservedOnExec_sound {B₁ B₂ : EpochBook} {U : Array String}
    (h₁ : B₁.WF) (h₂ : B₂.WF) (h : checkPreservedOnExec B₁ B₂ U = true) :
    ∀ k ∈ U, B₁.lookupSpec k = B₂.lookupSpec k := by
  intro k hk
  have hk' := List.all_eq_true.1 h k (Array.mem_def.1 hk)
  rw [← lookupEpochFast_eq_spec h₁, ← lookupEpochFast_eq_spec h₂]
  exact optTermEq_sound hk'

/-- **The change-certificate verifier**: both epochs well formed, the same keys, the unchanged
set sorted, and its bodies equal. `O(n + |U| log n)` comparisons of keys. -/
def verifyChangeCertExec (B₁ B₂ : EpochBook) (U : Array String) : Bool :=
  B₁.wfB && B₂.wfB && checkSameKeysExec B₁ B₂ && sortedByB id U.toList &&
    checkPreservedOnExec B₁ B₂ U

/-- A call into a book: the body's free index `i` names the book key `imports[i]`. -/
structure EpochCall where
  imports : Array String
  body : Term

/-- Link a frame against a book: index `i` becomes the body of `imports[i]`. -/
def linkSubst (B : EpochBook) (imports : Array String) : Nat → Term := fun i =>
  match imports[i]? with
  | some k => (lookupEpochFast B k).getD (.bound i)
  | none => .bound i

/-- Evaluate a call against an epoch at a fuel. -/
def evalAgainst (B : EpochBook) (fuel : Nat) (c : EpochCall) : Option Term :=
  Obend.Law.run fuel (c.body.substitute (linkSubst B c.imports))

/-- The keys a call references lie in `U`: every free index of the body that the frame names
names a key of `U`. Bound indices and unnamed indices reference nothing. -/
def UsesOnly (U : Array String) (c : EpochCall) : Prop :=
  Obend.Core.Traverse.Tree.All (fun i => ∀ k, c.imports[i]? = some k → k ∈ U) (encode c.body)

mutual
/-- `p` at every free index of a tree, shifting under binders: a structural walk, so it reduces
in the kernel (`Tree.all` does not). -/
def freeAllB : (Nat → Bool) → Obend.Core.TermTraverse.Shape → Bool
  | p, .var i => p i
  | p, .bind b => freeAllB (fun i => match i with | 0 => true | j + 1 => p j) b
  | p, .node _ cs => freeAllsB p cs
def freeAllsB : (Nat → Bool) → List Obend.Core.TermTraverse.Shape → Bool
  | _, [] => true
  | p, c :: cs => freeAllB p c && freeAllsB p cs
end

mutual
theorem freeAllB_sound : ∀ {p : Nat → Bool} {t : Obend.Core.TermTraverse.Shape},
    freeAllB p t = true → Obend.Core.Traverse.Tree.All (fun i => p i = true) t
  | p, .var i, h => by simpa [freeAllB, Obend.Core.Traverse.Tree.All] using h
  | p, .bind b, h => by
    have ih := freeAllB_sound (p := fun i => match i with | 0 => true | j + 1 => p j) (t := b)
      (by simpa [freeAllB] using h)
    simp only [Obend.Core.Traverse.Tree.All]
    exact (Obend.Core.Traverse.Tree.all_congr _ _ _ (fun i => by cases i <;> simp)).1 ih
  | p, .node _ cs, h => by
    simp only [Obend.Core.Traverse.Tree.All]
    exact freeAllsB_sound (by simpa [freeAllB] using h)
theorem freeAllsB_sound : ∀ {p : Nat → Bool} {cs : List Obend.Core.TermTraverse.Shape},
    freeAllsB p cs = true → ∀ c ∈ cs, Obend.Core.Traverse.Tree.All (fun i => p i = true) c
  | _, [], _, _, hc => by cases hc
  | p, c :: cs, h, d, hd => by
    simp only [freeAllsB, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hd with same | hd
    · rw [same]
      exact freeAllB_sound h.1
    · exact freeAllsB_sound h.2 d hd
end

/-- The decided form of `UsesOnly` over a sorted `U`: a binary search per free occurrence. -/
def usesOnlyExec (U : Array String) (c : EpochCall) : Bool :=
  freeAllB (fun i =>
    match c.imports[i]? with
    | some k => (sortedSearch id U k).isSome
    | none => true) (encode c.body)

theorem usesOnlyExec_sound {U : Array String} {c : EpochCall}
    (hU : U.toList.Pairwise (fun x y => x < y)) (h : usesOnlyExec U c = true) : UsesOnly U c := by
  have h' := freeAllB_sound h
  refine (Obend.Core.Traverse.Tree.all_congr _ _ _ ?_).1 h'
  intro i
  constructor
  · intro hi k hk
    simp only [hk] at hi
    rw [sortedSearch_eq_find id U k hU, List.find?_isSome] at hi
    obtain ⟨x, hx, hxk⟩ := hi
    have : x = k := beq_iff_eq.1 hxk
    subst this
    exact Array.mem_def.2 hx
  · intro hi
    cases hk : c.imports[i]? with
    | none => rfl
    | some k =>
      simp only []
      rw [sortedSearch_eq_find id U k hU, List.find?_isSome]
      exact ⟨k, Array.mem_def.1 (hi k hk), beq_self_eq_true _⟩

theorem substitute_congr_all (t : Term) (p : Nat → Prop)
    (h : Obend.Core.Traverse.Tree.All p (encode t)) (σ τ : Nat → Term)
    (same : ∀ i, p i → σ i = τ i) : t.substitute σ = t.substitute τ := by
  apply Obend.Core.TermTraverse.encode_injective
  simp only [Obend.Core.TermTraverse.encode_substitute]
  apply Obend.Core.Traverse.Tree.substitute_congr_on (encode t) p h
  intro i hi
  rw [same i hi]

theorem verifyChangeCertExec_parts {B₁ B₂ : EpochBook} {U : Array String}
    (hv : verifyChangeCertExec B₁ B₂ U = true) :
    B₁.WF ∧ B₂.WF ∧ B₁.keys = B₂.keys ∧ U.toList.Pairwise (fun x y => x < y) ∧
      ∀ k ∈ U, B₁.lookupSpec k = B₂.lookupSpec k := by
  simp only [verifyChangeCertExec, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨⟨h1, h2⟩, hk⟩, hs⟩, hp⟩ := hv
  have w1 := EpochBook.wf_of_wfB h1
  have w2 := EpochBook.wf_of_wfB h2
  exact ⟨w1, w2, checkSameKeysExec_sound hk, sortedByB_sound id _ hs,
    checkPreservedOnExec_sound w1 w2 hp⟩

/-- **Change certificates preserve every call on the unchanged set.** If the verifier accepts
`(B₁, B₂, U)`, a call that references only keys of `U` links to the same term against both
epochs, so it evaluates identically at every fuel. -/
theorem changeCert_preservedOn_sound {B₁ B₂ : EpochBook} {U : Array String}
    (hv : verifyChangeCertExec B₁ B₂ U = true) (c : EpochCall) (hU : UsesOnly U c)
    (fuel : Nat) : evalAgainst B₁ fuel c = evalAgainst B₂ fuel c := by
  obtain ⟨w1, w2, _, _, hp⟩ := verifyChangeCertExec_parts hv
  unfold evalAgainst
  rw [substitute_congr_all c.body _ hU (linkSubst B₁ c.imports) (linkSubst B₂ c.imports)]
  intro i hi
  unfold linkSubst
  cases hk : c.imports[i]? with
  | none => rfl
  | some k =>
    simp only []
    rw [lookupEpochFast_eq_spec w1, lookupEpochFast_eq_spec w2, hp k (hi k hk)]

/-- The decided form end to end: verifier and usage check both executable. -/
theorem changeCert_preservedOn_exec {B₁ B₂ : EpochBook} {U : Array String}
    (hv : verifyChangeCertExec B₁ B₂ U = true) (c : EpochCall) (hc : usesOnlyExec U c = true)
    (fuel : Nat) : evalAgainst B₁ fuel c = evalAgainst B₂ fuel c :=
  changeCert_preservedOn_sound hv c
    (usesOnlyExec_sound (verifyChangeCertExec_parts hv).2.2.2.1 hc) fuel

/-- A relational bridge between two epochs: bodies equal on `U`, related by `Rel` off it. -/
def IndexedBridge (Rel : String → Term → Term → Prop) (B₁ B₂ : EpochBook) (U : Array String) :
    Prop :=
  ∀ (k : String) (t₁ t₂ : Term), B₁.lookupSpec k = some t₁ → B₂.lookupSpec k = some t₂ →
    (k ∈ U → t₁ = t₂) ∧ (k ∉ U → Rel k t₁ t₂)

/-- **A change certificate** from epoch `B₁` to epoch `B₂`. -/
structure ChangeCertificate (Rel : String → Term → Term → Prop) (B₁ B₂ : EpochBook) where
  unchangedSet : Array String
  wf₁ : B₁.WF
  wf₂ : B₂.WF
  sameKeys : B₁.keys = B₂.keys
  preserved : ∀ k ∈ unchangedSet, B₁.lookupSpec k = B₂.lookupSpec k
  bridge : IndexedBridge Rel B₁ B₂ unchangedSet

/-- Build a certificate from an accepted verifier run and the bridge evidence off `U`. -/
def ChangeCertificate.ofExec {Rel : String → Term → Term → Prop} {B₁ B₂ : EpochBook}
    (U : Array String) (hv : verifyChangeCertExec B₁ B₂ U = true)
    (hrel : ∀ (k : String) (t₁ t₂ : Term), k ∉ U → B₁.lookupSpec k = some t₁ →
      B₂.lookupSpec k = some t₂ → Rel k t₁ t₂) : ChangeCertificate Rel B₁ B₂ where
  unchangedSet := U
  wf₁ := (verifyChangeCertExec_parts hv).1
  wf₂ := (verifyChangeCertExec_parts hv).2.1
  sameKeys := (verifyChangeCertExec_parts hv).2.2.1
  preserved := (verifyChangeCertExec_parts hv).2.2.2.2
  bridge := by
    intro k t₁ t₂ h₁ h₂
    refine ⟨fun hk => ?_, fun hk => hrel k t₁ t₂ hk h₁ h₂⟩
    have := (verifyChangeCertExec_parts hv).2.2.2.2 k hk
    rw [h₁, h₂] at this
    exact Option.some.inj this

/-- A call is linkable when every key its frame names is in the book. -/
def Linkable (B : EpochBook) (c : EpochCall) : Prop :=
  ∀ k ∈ c.imports, (B.lookupSpec k).isSome = true

/-- **No dangling reference across the epoch**: the same calls are linkable before and after. -/
theorem changeCert_linkable_iff {Rel : String → Term → Term → Prop} {B₁ B₂ : EpochBook}
    (cert : ChangeCertificate Rel B₁ B₂) (c : EpochCall) : Linkable B₁ c ↔ Linkable B₂ c := by
  unfold Linkable
  simp only [EpochBook.lookupSpec_isSome_iff, cert.sameKeys]

/-- The certificate's own statement of preservation, for a call within its unchanged set. -/
theorem ChangeCertificate.eval_eq {Rel : String → Term → Term → Prop} {B₁ B₂ : EpochBook}
    (cert : ChangeCertificate Rel B₁ B₂) (c : EpochCall) (hU : UsesOnly cert.unchangedSet c)
    (fuel : Nat) : evalAgainst B₁ fuel c = evalAgainst B₂ fuel c := by
  unfold evalAgainst
  rw [substitute_congr_all c.body _ hU (linkSubst B₁ c.imports) (linkSubst B₂ c.imports)]
  intro i hi
  unfold linkSubst
  cases hk : c.imports[i]? with
  | none => rfl
  | some k =>
    simp only []
    rw [lookupEpochFast_eq_spec cert.wf₁, lookupEpochFast_eq_spec cert.wf₂,
      cert.preserved k (hi k hk)]

/-- The checks are satisfiable on a real change: `b` is rewritten, `a` is certified unchanged,
and a call whose only free index names `a` (under a binder, with `b` in its frame but unused)
is within the unchanged set. -/
example :
    verifyChangeCertExec ⟨#[("a", .nat 1), ("b", .nat 2)]⟩ ⟨#[("a", .nat 1), ("b", .nat 3)]⟩
        #["a"] = true ∧
      checkSameKeysExec ⟨#[("a", .nat 1), ("b", .nat 2)]⟩ ⟨#[("a", .nat 1), ("b", .nat 3)]⟩ = true ∧
      checkPreservedOnExec ⟨#[("a", .nat 1), ("b", .nat 2)]⟩ ⟨#[("a", .nat 1), ("b", .nat 3)]⟩
        #["a"] = true ∧
      sortedByB id ["a", "b", "c"] = true ∧
      optTermEq (some (.lam (.bound 0))) (some (.lam (.bound 0))) = true ∧
      usesOnlyExec #["a"] ⟨#["a", "b"], .lam (.bound 1)⟩ = true ∧
      freeAllB (fun i => i == 0) (encode (.lam (.bound 1))) = true ∧
      freeAllsB (fun i => i == 0) [encode (.bound 0), encode (.lam (.bound 1))] = true := by
  decide +kernel

example : UsesOnly #["a"] ⟨#["a", "b"], .lam (.bound 1)⟩ :=
  usesOnlyExec_sound (by decide +kernel) (by decide +kernel)

/-! ## 4. Choice-free assemblies over `Core4` terms -/

/-- The identity tracker. -/
@[expose] def idTerm : Term := .lam (.bound 0)

/-- The composition tracker `λx. g (f x)`. -/
@[expose] def compTerm (g f : Term) : Term :=
  .lam (.app (g.rename Nat.succ) (.app (f.rename Nat.succ) (.bound 0)))

/-- An assembly over `Term` realizers under weak-head call-by-name: a realizability relation
closed under head expansion, every element realized. -/
structure AsmCore4 (X : Type u) where
  Realizes : Term → X → Prop
  expand : ∀ {r r' : Term} {x : X}, Step r r' → Realizes r' x → Realizes r x
  realized : ∀ x : X, ∃ r : Term, Realizes r x

/-- A tracked morphism: the specification map and, as data, the term that tracks it. Arguments
are passed unevaluated, so tracking is stated at the application itself. -/
structure AsmCore4Hom {X : Type u} {Y : Type v} (A : AsmCore4 X) (B : AsmCore4 Y) where
  specFun : X → Y
  tracker : Term
  tracks : ∀ (x : X) (r : Term), A.Realizes r x → B.Realizes (.app tracker r) (specFun x)

theorem instantiate_bound_zero (r : Term) : instantiate (.bound 0) r = r := by
  simp [instantiate]

theorem instantiate_compBody (g f r : Term) :
    instantiate (.app (g.rename Nat.succ) (.app (f.rename Nat.succ) (.bound 0))) r =
      .app g (.app f r) := by
  rw [instantiate_eq]
  simp only [Term.substitute, shift_one_cancel]
  rfl

namespace AsmCore4Hom

/-- The identity morphism, tracked by `idTerm`. -/
@[expose] def id {X : Type u} (A : AsmCore4 X) : AsmCore4Hom A A where
  specFun x := x
  tracker := idTerm
  tracks x r hr := by
    refine A.expand (Step.beta (.bound 0) r) ?_
    rw [instantiate_bound_zero]
    exact hr

/-- Composition, tracked by `compTerm g.tracker f.tracker`. -/
@[expose] def comp {X : Type u} {Y : Type v} {Z : Type w} {A : AsmCore4 X} {B : AsmCore4 Y}
    {C : AsmCore4 Z} (g : AsmCore4Hom B C) (f : AsmCore4Hom A B) : AsmCore4Hom A C where
  specFun x := g.specFun (f.specFun x)
  tracker := compTerm g.tracker f.tracker
  tracks x r hr := by
    refine C.expand (Step.beta _ r) ?_
    rw [instantiate_compBody]
    exact g.tracks _ _ (f.tracks x r hr)

end AsmCore4Hom

/-- The quotient assembly: a term realizes a class when it realizes a representative. -/
@[expose] def quotAssembly {X : Type u} (A : AsmCore4 X) (R : X → X → Prop) : AsmCore4 (Quot R) where
  Realizes r q := ∃ a : X, Quot.mk R a = q ∧ A.Realizes r a
  expand s := fun ⟨a, ha, hr⟩ => ⟨a, ha, A.expand s hr⟩
  realized :=
    Quot.ind fun a =>
      let ⟨r, hr⟩ := A.realized a
      ⟨r, a, rfl, hr⟩

/-- The projection `Quot.mk R`, tracked by the identity. -/
@[expose] def quotMk {X : Type u} (A : AsmCore4 X) (R : X → X → Prop) :
    AsmCore4Hom A (quotAssembly A R) where
  specFun := Quot.mk R
  tracker := idTerm
  tracks x r hr := by
    refine (quotAssembly A R).expand (Step.beta (.bound 0) r) ?_
    rw [instantiate_bound_zero]
    exact ⟨x, rfl, hr⟩

/-- **The quotient lift.** A morphism that respects `R` lifts along `Quot.mk R` with the same
tracker: no `Quot.sound`, no choice, and the tracker equation is `rfl`. -/
@[expose] def AsmCore4Hom.quotLift {X : Type u} {Z : Type w} {A : AsmCore4 X} {C : AsmCore4 Z}
    (R : X → X → Prop) (f : AsmCore4Hom A C)
    (h : ∀ x₁ x₂, R x₁ x₂ → f.specFun x₁ = f.specFun x₂) : AsmCore4Hom (quotAssembly A R) C where
  specFun := Quot.lift f.specFun h
  tracker := f.tracker
  tracks := by
    rintro q r ⟨a, rfl, hr⟩
    exact f.tracks a r hr

theorem AsmCore4Hom.quotLift_tracker_rfl {X Z : Type} {A : AsmCore4 X} {C : AsmCore4 Z}
    (R : X → X → Prop) (f : AsmCore4Hom A C)
    (h : ∀ x₁ x₂, R x₁ x₂ → f.specFun x₁ = f.specFun x₂) :
    (f.quotLift R h).tracker = f.tracker := rfl

theorem AsmCore4Hom.quotLift_spec_mk {X Z : Type} {A : AsmCore4 X} {C : AsmCore4 Z}
    (R : X → X → Prop) (f : AsmCore4Hom A C)
    (h : ∀ x₁ x₂, R x₁ x₂ → f.specFun x₁ = f.specFun x₂) (a : X) :
    (f.quotLift R h).specFun (Quot.mk R a) = f.specFun a := rfl

/-- The lift is the unique factorization through the projection, on trackers up to one
identity redex and on specifications exactly. -/
theorem AsmCore4Hom.quotLift_comp_mk {X Z : Type} {A : AsmCore4 X} {C : AsmCore4 Z}
    (R : X → X → Prop) (f : AsmCore4Hom A C)
    (h : ∀ x₁ x₂, R x₁ x₂ → f.specFun x₁ = f.specFun x₂) :
    ((f.quotLift R h).comp (quotMk A R)).specFun = f.specFun ∧
      ((f.quotLift R h).comp (quotMk A R)).tracker = compTerm f.tracker idTerm :=
  ⟨rfl, rfl⟩

end Obend.Logic.GuardedLob

end
