module
/- `≈b`, the behavioural equivalence of Core4's reference semantics: two terms are equivalent when
every closing substitution and every context gives them the same completed runs (the same ground
observation, and convergence to a value or not). It is the first of the three candidate
definitions in `review/EQUIV-PLAN-20261031.md`: it counts no cost and sees no heap. `mix` is
associative for it (`mix_assoc`), and both sides are `Ahead` of one term,
`λself. λsuper. c self (b self (a self super))` (`mix_assoc_ahead`). -/
public import Obend.Equiv.Simulation
public section
namespace Obend.Equiv
open Obend.Core.Term
open Obend.Core.TermTraverse (rename_substitute substitute_comp)
set_option autoImplicit false

/-! ## Completed runs -/

/-- The run of `t` completes with ground observation `o`. -/
@[expose] def Halts (t : Term) (o : Observation) : Prop := ∃ v, Evaluates t v ∧ Observes v o

/-- The run of `t` completes with some value, ground or not. -/
@[expose] def Converges (t : Term) : Prop := ∃ v, Evaluates t v

/-- Two terms have the same completed runs. -/
structure SameRuns (t t' : Term) : Prop where
  halts : ∀ o, Halts t o ↔ Halts t' o
  converges : Converges t ↔ Converges t'

theorem observes_literal {v : Term} {o : Observation} (h : Observes v o) : Literal v := by
  cases h <;> constructor

theorem sameRuns_of_ahead {t t' : Term} (h : Ahead t t') : SameRuns t t' where
  halts o := by
    constructor
    · rintro ⟨v, e, obs⟩
      obtain ⟨v', e', a⟩ := evaluates_behind h e
      rw [inv_literal_behind (observes_literal obs) a] at e'
      exact ⟨v, e', obs⟩
    · rintro ⟨v', e', obs⟩
      obtain ⟨v, e, a⟩ := evaluates_ahead h e'
      have := value_steps_eq e.2 (inv_literal_ahead (observes_literal obs) a)
      exact ⟨v, e, this ▸ obs⟩
  converges := by
    constructor
    · rintro ⟨v, e⟩; obtain ⟨v', e', _⟩ := evaluates_behind h e; exact ⟨v', e'⟩
    · rintro ⟨v', e'⟩; obtain ⟨v, e, _⟩ := evaluates_ahead h e'; exact ⟨v, e⟩

/-! ## Reflective contextual equivalence (`REquiv`, `≈r`) and compatible alias (`BEquiv`, `≈b`)

Because `REquiv` quantifies over *every* `Core4` substitution `ρ` and context `C`—including
contexts that inspect specification provenance via `.metadata`—it is the level-`r` (reflective)
contextual equivalence (`Observed .r` in `Obend.Equiv.Quote`). We name it `REquiv` (`≈r`) here and
retain `BEquiv` (`≈b`) as a backwards-compatible alias so downstream modules compile unchanged,
while `Obend.Equiv.Quote` defines `PureBEquiv` (`Observed .b`) for metadata-blind contexts and
proves `requiv_implies_pureBEquiv : a ≈r b → PureBEquiv a b`. -/

/-- `t ≈r t'`: reflective contextual equivalence over all closing substitutions `ρ` and all `Core4`
contexts `C` (including `.metadata` observers). -/
@[expose] def REquiv (t t' : Term) : Prop :=
  ∀ (ρ : Nat → Term) (C : Term),
    SameRuns (instantiate C (t.substitute ρ)) (instantiate C (t'.substitute ρ))

@[inherit_doc] infix:50 " ≈r " => REquiv

/-- Backwards-compatible alias for `REquiv` (`≈r`). For metadata-blind level-`b` contextual
equivalence, see `Obend.Equiv.PureBEquiv` (`Observed .b`) in `Obend.Equiv.Quote`. -/
@[expose] abbrev BEquiv (t t' : Term) : Prop := REquiv t t'

@[inherit_doc] infix:50 " ≈b " => BEquiv

theorem REquiv.refl (t : Term) : t ≈r t := fun _ _ => ⟨fun _ => Iff.rfl, Iff.rfl⟩

theorem REquiv.symm {t t' : Term} (h : t ≈r t') : t' ≈r t := fun ρ C =>
  ⟨fun o => ((h ρ C).halts o).symm, (h ρ C).converges.symm⟩

theorem REquiv.trans {t t' t'' : Term} (h : t ≈r t') (h' : t' ≈r t'') : t ≈r t'' := fun ρ C =>
  ⟨fun o => ((h ρ C).halts o).trans ((h' ρ C).halts o),
    (h ρ C).converges.trans (h' ρ C).converges⟩

/-- The trivial context and substitution: equivalent terms have the same completed runs. -/
theorem REquiv.sameRuns {t t' : Term} (h : t ≈r t') : SameRuns t t' := by
  have := h Term.bound (.bound 0)
  simpa [instantiate, Term.substitute, substitute_bound] using this

theorem requiv_of_ahead {t t' : Term} (h : Ahead t t') : t ≈r t' := fun ρ C =>
  sameRuns_of_ahead (ahead_instantiate (Ahead.refl C)
    (ahead_substitute h (fun n => Ahead.refl (ρ n))))

/-- Reduction is an equivalence: a term is equivalent to anything it reduces to. -/
theorem requiv_of_steps {t t' : Term} (h : Steps t t') : t ≈r t' :=
  requiv_of_ahead (Ahead.ofStepsRefl h)

theorem BEquiv.refl (t : Term) : t ≈b t := REquiv.refl t

theorem BEquiv.symm {t t' : Term} (h : t ≈b t') : t' ≈b t := REquiv.symm h

theorem BEquiv.trans {t t' t'' : Term} (h : t ≈b t') (h' : t' ≈b t'') : t ≈b t'' :=
  REquiv.trans h h'

/-- The trivial context and substitution: equivalent terms have the same completed runs. -/
theorem BEquiv.sameRuns {t t' : Term} (h : t ≈b t') : SameRuns t t' := REquiv.sameRuns h

theorem bequiv_of_ahead {t t' : Term} (h : Ahead t t') : t ≈b t' := requiv_of_ahead h

/-- Reduction is an equivalence: a term is equivalent to anything it reduces to. -/
theorem bequiv_of_steps {t t' : Term} (h : Steps t t') : t ≈b t' := requiv_of_steps h

/-! ## `mix` is associative -/

theorem shift_two_cancel (B s u : Term) :
    ((B.rename (fun n => n + 2)).substitute (liftSubstitution (single s))).substitute (single u) = B := by
  rw [rename_substitute, substitute_comp]
  conv => rhs; rw [← substitute_bound B]
  congr 1; funext i
  simp [liftSubstitution, single, Term.rename, Term.substitute]

theorem shift_one_cancel (s u : Term) : (s.rename Nat.succ).substitute (single u) = s := by
  rw [rename_substitute]
  conv => rhs; rw [← substitute_bound s]
  rfl

/-- An applied `mix` unfolds in three weak-head steps. -/
theorem mix_apply (A B s u : Term) :
    Steps (.app (.app (.mix A B) s) u) (.app (.app B s) (.app (.app A s) u)) := by
  refine .next (.application _ (.application _ (.mix _ _))) ?_
  refine .next (.application _ (.beta _ _)) ?_
  rw [instantiate_eq]
  simp only [Term.substitute]
  refine .next (.beta _ _) ?_
  rw [instantiate_eq]
  simp only [Term.substitute]
  rw [shift_two_cancel, shift_two_cancel]
  simp only [liftSubstitution, single, shift_one_cancel, Term.substitute]
  exact .refl _

/-- The common term both associations are ahead of: `λself. λsuper. c self (b self (a self super))`. -/
@[expose] def mixAssocBody (a b c : Term) : Term :=
  .lam (.lam (.app (.app (c.rename (fun n => n + 2)) (.bound 1))
    (.app (.app (b.rename (fun n => n + 2)) (.bound 1))
      (.app (.app (a.rename (fun n => n + 2)) (.bound 1)) (.bound 0)))))

theorem mix_assoc_left_ahead (a b c : Term) : Ahead (.mix (.mix a b) c) (mixAssocBody a b c) := by
  refine .run (steps_one (.mix _ _)) ?_
  simp only [mixBody, mixAssocBody, Term.rename]
  refine .lam (.lam (.app (.refl _) ?_))
  exact Ahead.ofStepsRefl (mix_apply _ _ _ _)

theorem mix_assoc_right_ahead (a b c : Term) : Ahead (.mix a (.mix b c)) (mixAssocBody a b c) := by
  refine .run (steps_one (.mix _ _)) ?_
  simp only [mixBody, mixAssocBody, Term.rename]
  exact .lam (.lam (Ahead.ofStepsRefl (mix_apply _ _ _ _)))

/-- Both associations are ahead of `λself. λsuper. c self (b self (a self super))`. -/
theorem mix_assoc_ahead (a b c : Term) :
    Ahead (.mix (.mix a b) c) (mixAssocBody a b c) ∧ Ahead (.mix a (.mix b c)) (mixAssocBody a b c) :=
  ⟨mix_assoc_left_ahead a b c, mix_assoc_right_ahead a b c⟩

/-- **`mix` is associative up to `≈r` (and `≈b`)**, for arbitrary (open) extensions. -/
theorem mix_assoc (a b c : Term) : .mix (.mix a b) c ≈b .mix a (.mix b c) :=
  (bequiv_of_ahead (mix_assoc_left_ahead a b c)).trans
    (bequiv_of_ahead (mix_assoc_right_ahead a b c)).symm

/-- No weak-head reduct is shared: each association is a value after one step, and the two
values differ (the inner `mix` is under two binders on one side and applied on the other). -/
theorem mix_assoc_not_weak_head (a b c : Term) :
    Evaluates (.mix (.mix a b) c) (mixBody (.mix a b) c) ∧
    Evaluates (.mix a (.mix b c)) (mixBody a (.mix b c)) :=
  ⟨⟨steps_one (.mix _ _), .function _⟩, ⟨steps_one (.mix _ _), .function _⟩⟩

end Obend.Equiv
end
