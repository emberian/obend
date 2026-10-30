module
/-
# Obend.Spec.Proofs.Contract — the composition law

`C_{A;B}(S,I) = C_A(S,I) ∧ C_B(S, F_A(S,I))` and `F_{A;B} = F_B ∘ F_A` (`run_append`), its
associativity (`run_assoc`), what an admitted layer met (`checkLayer_ok`) and what a discharged
composition guarantees (`discharge_ok`). Statements as in minidregg
`Compiler/ObjectiveBendContract.lean` (commit 092027a2); pinned standard.
-/
public import Obend.Spec.Contract
public import Obend.AxiomPin
namespace Obend.Spec.Contract
set_option autoImplicit false

variable {τ : Type} [BEq τ]

/-! ## The composition law -/

/-- **`C_{A;B}(S,I) = C_A(S,I) ∧ C_B(S, F_A(S,I))` and `F_{A;B} = F_B ∘ F_A`**: checking the
composition of two chains is checking the first from the seed, then the second from the row the
first leaves. Associativity of composition is therefore the associativity of `++` on chains:
`run_assoc`. -/
public theorem run_append (self : Row τ) (seed : Row τ) (first second : List (Layer τ)) :
    run self seed (first ++ second) = (run self seed first).bind fun mid => run self mid second := by
  induction first generalizing seed with
  | nil => rfl
  | cons layer rest ih =>
    simp only [List.cons_append, run]
    cases checkLayer self seed layer with
    | error _ => rfl
    | ok next => exact ih next

public theorem run_assoc (self seed : Row τ) (a b c : List (Layer τ)) :
    run self seed ((a ++ b) ++ c) = run self seed (a ++ (b ++ c)) := by
  rw [List.append_assoc]

/-- An admitted layer met every clause of its contract, and left `F_L(S, I)`. -/
public theorem checkLayer_ok {self beneath next : Row τ} {layer : Layer τ}
    (admitted : checkLayer self beneath layer = .ok next) :
    missing self layer.assumes = [] ∧ missing beneath layer.consumes = [] ∧
      replaced beneath layer.provides = [] ∧ next = layer.leaves beneath := by
  unfold checkLayer checkBounds checkProvides at admitted
  by_cases a : (missing self layer.assumes).isEmpty
  · by_cases b : (missing beneath layer.consumes).isEmpty
    · by_cases r : (replaced beneath layer.provides).isEmpty
      · simp only [a, b, r, Bool.not_true, Bool.false_eq_true, if_false, Except.bind] at admitted
        cases admitted
        exact ⟨List.isEmpty_iff.mp a, List.isEmpty_iff.mp b, List.isEmpty_iff.mp r, rfl⟩
      · simp [a, b, r, Except.bind] at admitted
    · simp [a, b, Except.bind] at admitted
  · simp [a, Except.bind] at admitted

public theorem missing_nil_get {actual required : Row τ} (h : missing actual required = []) :
    ∀ n t, (n, t) ∈ required → get? actual n == some t := by
  intro n t mem
  unfold missing at h
  have := List.filterMap_eq_nil_iff.mp h (n, t) mem
  by_cases e : (get? actual n == some t) = true
  · exact e
  · simp [e] at this

/-- A discharged composition: every layer's assumptions hold in the final self, and the row the
chain leaves gives every member of the final self its declared type and declares nothing else. -/
public theorem discharge_ok {self seed : Row τ} {chain : List (Layer τ)}
    (admitted : discharge self seed chain = .ok ()) :
    ∃ final, run self seed chain = .ok final ∧
      (∀ n t, (n, t) ∈ self → get? final n == some t) ∧
      (∀ n, n ∈ names final → (get? self n).isSome) := by
  unfold discharge at admitted
  cases h : run self seed chain with
  | error e => rw [h] at admitted; cases admitted
  | ok final =>
    rw [h] at admitted
    refine ⟨final, rfl, ?_⟩
    simp only [Except.bind] at admitted
    unfold close at admitted
    by_cases m : (missing final self).isEmpty
    · simp only [m, if_true] at admitted
      by_cases x : (names final).all (fun n => (get? self n).isSome)
      · refine ⟨missing_nil_get (List.isEmpty_iff.mp m), fun n mem => ?_⟩
        exact (List.all_eq_true.mp x) n mem
      · simp [x] at admitted
    · revert admitted
      simp only [m, Bool.false_eq_true, if_false]
      split <;> (try split) <;> simp

#assert_axioms run_append run_assoc checkLayer_ok missing_nil_get discharge_ok

end Obend.Spec.Contract
