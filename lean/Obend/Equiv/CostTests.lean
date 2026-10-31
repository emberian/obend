module
/- Faré's tests, costed by the clairvoyant semantics, and where that semantics parts from need.

- `keep(7, y)` costs 3 for every `y`, divergent or not: the argument is skipped (`keep_cost`).
- `{good = 7, bad = self.bad}.good` costs 8 (`good_cost`), and `.bad` has no derivation at all
  (`bad_field_no_cv`), as need blackholes it.
- `{a = 7, b = self.a}.b` has no derivation either (`self_field_no_cv`), though the reference
  semantics evaluates it to 7 (`self_field_evaluates`) and so does the machine
  (`self_field_machine`). This is Hackett and Hutton's `Let′` for a recursive binding: the body of
  `fix` is evaluated before `self` is bound, so a lazy field that reads `self`, which need forces
  only after the update, must be evaluated before it (and is stuck) or skipped (and is missing).
  Their Theorem 4.1(i) does not hold for recursive `let` with such a field.
- A knot is entered at cost 3 (`knot_unfold`). -/
public import Obend.Equiv.Cost
public import Obend.Equiv.FareTests
public import Obend.Core.Machine
@[expose] public section
namespace Obend.Equiv.CostTests
open Obend.Core.Term
open Obend.Equiv
open Obend.Equiv.FareTests (keep object goodBad loop)
open Obend.Core.TermTraverse (rename_substitute substitute_comp substitute_rename rename_comp)
set_option autoImplicit false

/-! ## Knots -/

theorem knot_body (V : Term) :
    ((((V.rename shiftSelf).rename (liftRename (liftRename Nat.succ))).substitute
      (liftSubstitution (single (.bound 0)))).substitute (single (.record []))) = V := by
  rw [rename_comp, rename_substitute, substitute_comp]
  conv => rhs; rw [← substitute_bound V]
  congr 1; funext i
  cases i with
  | zero => simp [shiftSelf, liftRename, liftSubstitution, single, Term.rename, Term.substitute]
  | succ n => simp [shiftSelf, liftRename, liftSubstitution, single, Term.rename, Term.substitute]

theorem record_nil_settled : Settled (.record []) := .value (.record (fs := []) (by simp))

theorem cv_beta_value {W x : Term} (hx : Settled x) (hv : CValue (instantiate W x)) :
    CV (.app (.lam W) x) (instantiate W x) 1 := by
  have := Run.apply (Run.value (.lam W)) (Run.keep hx) (Run.value hv)
  simpa using this

/-- Entering a knot costs 3 and gives back its value tied to the same knot. -/
theorem knot_unfold {V : Term} (hV : CValue V) :
    CV (knot V) (V.substitute (single (knot V))) 3 := by
  let W1 : Term := (V.rename shiftSelf).rename (liftRename (liftRename Nat.succ))
  have inner : CV (.app (.lam (.lam W1)) (.bound 0)) (instantiate (.lam W1) (.bound 0)) 1 :=
    cv_beta_value (.bound 0) (by rw [instantiate_eq]; simp only [Term.substitute]; exact .lam _)
  have e1 : instantiate (.lam W1) (.bound 0) = .lam (W1.substitute (liftSubstitution (single (.bound 0)))) := by
    rw [instantiate_eq]; simp only [Term.substitute]
  rw [e1] at inner
  have e2 : instantiate (W1.substitute (liftSubstitution (single (.bound 0)))) (.record []) = V := by
    rw [instantiate_eq]; exact knot_body V
  have outer := Run.apply inner (Run.keep record_nil_settled) (by rw [e2]; exact Run.value hV)
  have body : CV (selfBody (.lam (.lam (V.rename shiftSelf))) (.record [])) V 2 := by
    have e3 : selfBody (.lam (.lam (V.rename shiftSelf))) (.record []) =
        .app (.app (.lam (.lam W1)) (.bound 0)) (.record []) := by
      simp [selfBody, Term.rename, W1]
    rw [e3]; simpa using outer
  exact Run.fixLet body

/-! ## Faré's first test -/

/-- `keep(7, y)` costs 3 for every `y`: the argument is skipped. -/
theorem keep_cost (y : Term) : CV (.app (.app keep (.nat 7)) y) (.nat 7) 3 := by
  have e : instantiate (.lam (.bound 1)) (.nat 7) = .lam (.nat 7) := by
    simp [instantiate, Term.substitute, liftSubstitution, Term.rename]
  have inner : CV (.app keep (.nat 7)) (.lam (.nat 7)) 1 := by
    have := cv_beta_value (W := .lam (.bound 1)) (.value (.nat 7)) (by rw [e]; exact .lam _)
    rw [e] at this; exact this
  have e2 : instantiate (.nat 7) skipped = .nat 7 := by simp [instantiate, Term.substitute]
  have := Run.apply inner (Run.skip y) (by rw [e2]; exact Run.value (.nat 7))
  simpa using this

theorem keep_loop_cost : CV (.app (.app keep (.nat 7)) loop) (.nat 7) 3 := keep_cost loop

/-! ## Objects whose second field reads `self` -/

/-- `fix (λself. λsuper. {n1 = 7, n2 = self.m}) {}`. -/
def selfObject (n1 n2 m : String) : Term :=
  .fix (.lam (.lam (.record [(n1, .nat 7), (n2, .get (.bound 1) m)]))) (.record [])

theorem object_eq : object = selfObject "good" "bad" "bad" := rfl

theorem selfObject_selfBody (n1 n2 m : String) :
    selfBody (.lam (.lam (.record [(n1, .nat 7), (n2, .get (.bound 1) m)]))) (.record []) =
      .app (.app (.lam (.lam (.record [(n1, .nat 7), (n2, .get (.bound 1) m)]))) (.bound 0)) (.record []) := by
  simp [selfBody, Term.rename, liftRename]

theorem selfObject_inner (n1 n2 m : String) (x : Term) :
    instantiate (.lam (.record [(n1, .nat 7), (n2, .get (.bound 1) m)])) x =
      .lam (.record [(n1, .nat 7), (n2, .get (x.rename .succ) m)]) := by
  simp [instantiate, Term.substitute, liftSubstitution]

theorem selfObject_outer (n1 n2 m : String) (x y : Term) :
    instantiate (.record [(n1, .nat 7), (n2, .get (x.rename .succ) m)]) y =
      .record [(n1, .nat 7), (n2, .get x m)] := by
  rw [instantiate_eq]
  simp only [Term.substitute, List.map_cons, List.map_nil, shift_one_cancel]

/-- The record such an object's body builds: the field reading `self` is stuck when evaluated (its
`self` is unbound), so it is skipped. -/
theorem selfObject_record {n1 n2 m : String} {X V : Term} {k : Nat} (stuck : ∀ w j, ¬ CV X w j)
    (h : CV (.record [(n1, .nat 7), (n2, .get X m)]) V k) : ∃ g, V = .record [(n1, g), (n2, skipped)] := by
  cases h with
  | value h0 =>
    have := record_value_fields h0 (n2, .get X m) (by simp)
    cases this with | value h1 => cases h1
  | record _ hf =>
    cases hf with
    | cons _ hr =>
      cases hr with
      | cons hb hn =>
        cases hn
        rcases bind_of_unsettled (fun h => by cases h with | value h1 => cases h1) hb with ⟨rfl, _⟩ | ⟨j, e, _⟩
        · exact ⟨_, rfl⟩
        · cases e with
          | value h0 => cases h0
          | get e1 _ _ => exact absurd e1 (stuck _ _)

theorem selfObject_body {n1 n2 m : String} {V : Term} {k : Nat}
    (h : CV (selfBody (.lam (.lam (.record [(n1, .nat 7), (n2, .get (.bound 1) m)]))) (.record [])) V k) :
    ∃ g, V = .record [(n1, g), (n2, skipped)] := by
  rw [selfObject_selfBody] at h
  cases h with
  | value h0 => exact absurd h0 app_not_ready
  | applySpec h1 _ =>
    cases h1 with
    | apply ha _ hc =>
      obtain ⟨e, _⟩ := cv_lam ha
      cases e
      rw [selfObject_inner] at hc; obtain ⟨e, _⟩ := cv_lam hc; cases e
    | applySpec ha _ => obtain ⟨e, _⟩ := cv_lam ha; cases e
  | apply h1 h2 h3 =>
    cases h1 with
    | applySpec ha _ => obtain ⟨e, _⟩ := cv_lam ha; cases e
    | apply ha hb hc =>
      obtain ⟨e, _⟩ := cv_lam ha
      cases e
      rw [selfObject_inner] at hc
      obtain ⟨e, _⟩ := cv_lam hc
      cases e
      rw [selfObject_outer] at h3
      rcases bind_of_settled (.bound 0) hb with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact selfObject_record (fun _ _ => cv_bound_false) h3
      · exact selfObject_record (fun _ _ => cv_skipped_false) h3

theorem selfObject_value {n1 n2 m : String} {w : Term} {k : Nat} (h : CV (selfObject n1 n2 m) w k) :
    ∃ g, w = .record [(n1, g), (n2, skipped)] := by
  unfold selfObject at h
  cases h with
  | value h0 => cases h0
  | fixLet hb =>
    obtain ⟨g, rfl⟩ := selfObject_body hb
    exact ⟨g.substitute (single (knot (.record [(n1, g), (n2, skipped)]))),
      by simp [Term.substitute, substitute_skipped]⟩
  | fixSkip hb =>
    obtain ⟨g, rfl⟩ := selfObject_body hb
    exact ⟨g.substitute (single skipped), by simp [Term.substitute, substitute_skipped]⟩

/-- Selecting the field that reads `self` has no clairvoyant derivation. -/
theorem selfObject_field_no_cv {n1 n2 m : String} (ne : n1 ≠ n2) {v : Term} {k : Nat} :
    ¬ CV (.get (selfObject n1 n2 m) n2) v k := by
  intro h
  cases h with
  | value h0 => cases h0
  | get h1 hit h2 =>
    obtain ⟨g, e⟩ := selfObject_value h1
    cases e
    have miss : (n1 == n2) = false := by simpa using ne
    simp [List.find?, miss] at hit
    obtain ⟨_, rfl⟩ := hit
    exact cv_skipped_false h2

/-! ## Faré's second test -/

theorem good_body : CV (selfBody goodBad (.record []))
    (.record [("good", .nat 7), ("bad", skipped)]) 6 := by
  have inner := cv_beta_value (W := .lam (.record [("good", .nat 7), ("bad", .get (.bound 1) "bad")]))
    (.bound 0) (by rw [selfObject_inner]; exact .lam _)
  rw [selfObject_inner] at inner
  have fields : Run .fields (.record [("good", .nat 7), ("bad", .get (.bound 0) "bad")])
      (.record [("good", .nat 7), ("bad", skipped)]) 3 :=
    Run.cons (Run.keep (.value (.nat 7))) (Run.cons (Run.skip _) Run.nil)
  have built : CV (.record [("good", .nat 7), ("bad", .get (.bound 0) "bad")])
      (.record [("good", .nat 7), ("bad", skipped)]) 4 := by
    refine Run.record ?_ fields
    intro h0
    have := record_value_fields h0 ("bad", .get (.bound 0) "bad") (by simp)
    cases this with | value h1 => cases h1
  have := Run.apply inner (Run.keep record_nil_settled) (by rw [selfObject_outer]; exact built)
  simpa [goodBad, selfObject_selfBody] using this

/-- **Faré's second test, costed**: `{good = 7, bad = self.bad}.good` costs 8. -/
theorem good_cost : CV (.get object "good") (.nat 7) 8 := by
  have fixed := Run.fixLet good_body
  have e : (Term.record [("good", .nat 7), ("bad", skipped)]).substitute
      (single (knot (.record [("good", .nat 7), ("bad", skipped)]))) =
      .record [("good", .nat 7), ("bad", skipped)] := by
    simp [Term.substitute, substitute_skipped]
  rw [e] at fixed
  exact Run.get fixed (by simp) (Run.value (.nat 7))

/-- and `.bad` has no derivation: need blackholes it, and the clairvoyant semantics agrees. -/
theorem bad_field_no_cv {v : Term} {k : Nat} : ¬ CV (.get object "bad") v k :=
  selfObject_field_no_cv (by decide)

/-! ## Where the clairvoyant semantics parts from need -/

/-- `{a = 7, b = self.a}`. -/
abbrev selfField : Term := selfObject "a" "b" "a"

/-- `{a = 7, b = self.a}.b` has no clairvoyant derivation. -/
theorem self_field_no_cv {v : Term} {k : Nat} : ¬ CV (.get selfField "b") v k :=
  selfObject_field_no_cv (by decide)

theorem selfField_steps (name : String) :
    Steps (.get selfField name) (.get (.record [("a", .nat 7), ("b", .get selfField "a")]) name) := by
  have s0 : Step (.get selfField name)
      (.get (.app (.app (.lam (.lam (.record [("a", .nat 7), ("b", .get (.bound 1) "a")]))) selfField)
        (.record [])) name) := .target _ (.fix _ _)
  have s1 := Step.target name (Step.application (.record []) (Step.beta
    (.lam (.record [("a", .nat 7), ("b", .get (.bound 1) "a")])) selfField))
  rw [selfObject_inner] at s1
  have s2 := Step.target name (Step.beta
    (.record [("a", .nat 7), ("b", .get (selfField.rename .succ) "a")]) (.record []))
  rw [selfObject_outer] at s2
  exact .next s0 (.next s1 (.next s2 (.refl _)))

/-- The reference semantics evaluates `{a = 7, b = self.a}.b` to 7. -/
theorem self_field_evaluates : Evaluates (.get selfField "b") (.nat 7) := by
  refine ⟨steps_trans (selfField_steps "b") (.next (.field _ _ (.get selfField "a") (by simp)) ?_), .natural 7⟩
  exact steps_trans (selfField_steps "a") (.next (.field _ _ (.nat 7) (by simp)) (.refl _))

/-! ## `mix_assoc_cost` is not vacuous -/

/-- An extension that ignores `self` and `super`. -/
def constant7 : Term := .lam (.lam (.nat 7))

theorem constant7_app (s : Term) (hs : Settled s) : CV (.app constant7 s) (.lam (.nat 7)) 1 := by
  have e : instantiate (.lam (.nat 7)) s = .lam (.nat 7) := by
    simp [instantiate, Term.substitute]
  have := cv_beta_value (W := .lam (.nat 7)) hs (by rw [e]; exact .lam _)
  rw [e] at this; exact this

/-- `mix (mix a b) constant7` applied to `{}` and `{}` evaluates to 7 (the inner `mix` is
skipped), so the context `(·) {} {}` inhabits `mix_assoc_cost`'s hypothesis. -/
theorem assoc_left_runs (a b : Term) :
    CV (.app (.app (.mix (.mix a b) constant7) (.record [])) (.record [])) (.nat 7) 6 := by
  have body : CV (.app (.app constant7 (.record [])) (.app (.app (.mix a b) (.record [])) (.record [])))
      (.nat 7) 3 := by
    have e : instantiate (.nat 7) skipped = .nat 7 := by simp [instantiate, Term.substitute]
    have := Run.apply (constant7_app _ record_nil_settled)
      (Run.skip (Term.app (.app (.mix a b) (.record [])) (.record []))) (by rw [e]; exact Run.value (.nat 7))
    simpa using this
  have := mk_mix_app_app (Run.keep record_nil_settled) (Run.keep record_nil_settled) body
  simpa using this

/-- and so the other association evaluates to 7 within a factor of 8 (at most 48). -/
theorem assoc_right_runs (a b : Term) :
    ∃ k, CV (.app (.app (.mix a (.mix b constant7)) (.record [])) (.record [])) (.nat 7) k ∧ k ≤ 48 := by
  have h := (mix_assoc_cost a b constant7).1 Term.bound (.app (.app (.bound 0) (.record [])) (.record []))
    (.nat 7) 6 (by simpa [instantiate, Term.substitute, substitute_bound] using assoc_left_runs a b)
  obtain ⟨v', k', r, le, lit⟩ := h
  rw [lit (.nat 7)] at r
  exact ⟨k', by simpa [instantiate, Term.substitute, substitute_bound] using r, by omega⟩

end Obend.Equiv.CostTests
end
