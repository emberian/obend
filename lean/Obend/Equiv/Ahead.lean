module
/- `Ahead t t'`: `t'` is `t` with some of its subterms, at any depth and under binders, run ahead
by Core4's reference reduction. It is the reduction-in-context that weak-head `Steps` lacks:
`mix (mix a b) c` and `mix a (mix b c)` have no common weak-head reduct (the inner unfolding sits
under two binders, or in argument position once applied), but both are `Ahead` of one term.

The relation is closed under substitution and is a simulation in both directions for weak-head
reduction, so related terms have the same completed runs (`Obend.Equiv.Behaviour`). -/
public import Obend.Equiv.Reduction
public import Obend.Equiv.Fields
@[expose] public section
namespace Obend.Equiv
open Obend.Core.Term
set_option autoImplicit false

inductive Ahead : Term → Term → Prop where
  | run {t m t' : Term} : Steps t m → Ahead m t' → Ahead t t'
  | hole (n : Nat) {σ σ' : List Term} : σ.length = σ'.length →
      (∀ p ∈ σ.zip σ', Ahead p.1 p.2) → Ahead (.hole n σ) (.hole n σ')
  | bound (i : Nat) : Ahead (.bound i) (.bound i)
  | lam {b b' : Term} : Ahead b b' → Ahead (.lam b) (.lam b')
  | app {f f' a a' : Term} : Ahead f f' → Ahead a a' → Ahead (.app f a) (.app f' a')
  | mix {l l' u u' : Term} : Ahead l l' → Ahead u u' → Ahead (.mix l u) (.mix l' u')
  | fix {s s' i i' : Term} : Ahead s s' → Ahead i i' → Ahead (.fix s i) (.fix s' i')
  | specification {m m' e e' : Term} : Ahead m m' → Ahead e e' →
      Ahead (.specification m e) (.specification m' e')
  | prototype {s s' g g' : Term} : Ahead s s' → Ahead g g' →
      Ahead (.prototype s g) (.prototype s' g')
  | reflect {p p' : Term} : Ahead p p' → Ahead (.reflect p) (.reflect p')
  | metadata {p p' : Term} : Ahead p p' → Ahead (.metadata p) (.metadata p')
  | project {p p' : Term} : Ahead p p' → Ahead (.project p) (.project p')
  | nat (n : Nat) : Ahead (.nat n) (.nat n)
  | boolean (b : Bool) : Ahead (.boolean b) (.boolean b)
  | label (l : String) : Ahead (.label l) (.label l)
  | binary (op : Primitive) {l l' r r' : Term} : Ahead l l' → Ahead r r' →
      Ahead (.binary op l r) (.binary op l' r')
  | extend {i i' : Term} {fs fs' : List (String × Term)} : Ahead i i' →
      fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', Ahead p.1.2 p.2.2) →
      Ahead (.extend i fs) (.extend i' fs')
  | record {fs fs' : List (String × Term)} :
      fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', Ahead p.1.2 p.2.2) →
      Ahead (.record fs) (.record fs')
  | get (name : String) {g g' : Term} : Ahead g g' → Ahead (.get g name) (.get g' name)
  | ifZero {v v' z z' s s' : Term} : Ahead v v' → Ahead z z' → Ahead s s' →
      Ahead (.ifZero v z s) (.ifZero v' z' s')
  | inject (l : String) {p p' : Term} : Ahead p p' → Ahead (.inject l p) (.inject l p')
  | case {sc sc' : Term} {arms arms' : List (String × Term)} : Ahead sc sc' →
      arms.map Prod.fst = arms'.map Prod.fst → (∀ p ∈ arms.zip arms', Ahead p.1.2 p.2.2) →
      Ahead (.case sc arms) (.case sc' arms')
  | ifBool {c c' x x' y y' : Term} : Ahead c c' → Ahead x x' → Ahead y y' →
      Ahead (.ifBool c x y) (.ifBool c' x' y')
  | perform {p p' : Term} : Ahead p p' → Ahead (.perform p) (.perform p')
  | done {v v' : Term} : Ahead v v' → Ahead (.done v) (.done v')

namespace Ahead

theorem ofSteps {t t' : Term} (h : Steps t t') (rest : Ahead t' t') : Ahead t t' := .run h rest

set_option linter.unusedVariables false in
/-- Every term is ahead of itself. -/
theorem refl : (t : Term) → Ahead t t
  | .hole n σ => .hole n rfl (zip_refl (fun a b => Ahead a b) σ (fun x _ => refl x))
  | .bound i => .bound i
  | .lam b => .lam (refl b)
  | .app f a => .app (refl f) (refl a)
  | .mix l u => .mix (refl l) (refl u)
  | .fix s i => .fix (refl s) (refl i)
  | .specification m e => .specification (refl m) (refl e)
  | .prototype s g => .prototype (refl s) (refl g)
  | .reflect p => .reflect (refl p)
  | .metadata p => .metadata (refl p)
  | .project p => .project (refl p)
  | .nat n => .nat n
  | .boolean b => .boolean b
  | .label l => .label l
  | .binary op l r => .binary op (refl l) (refl r)
  | .extend i fs => .extend (refl i) rfl
      (zip_refl (fun a b => Ahead a.2 b.2) fs (fun x _ => refl x.2))
  | .record fs => .record rfl (zip_refl (fun a b => Ahead a.2 b.2) fs (fun x _ => refl x.2))
  | .get g name => .get name (refl g)
  | .ifZero v z s => .ifZero (refl v) (refl z) (refl s)
  | .inject l p => .inject l (refl p)
  | .case sc arms => .case (refl sc) rfl
      (zip_refl (fun a b => Ahead a.2 b.2) arms (fun x _ => refl x.2))
  | .ifBool c x y => .ifBool (refl c) (refl x) (refl y)
  | .perform p => .perform (refl p)
  | .done v => .done (refl v)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i x hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf x.snd < sizeOf x := by cases x; simp +arith
       omega)

theorem ofStepsRefl {t t' : Term} (h : Steps t t') : Ahead t t' := .run h (refl t')

end Ahead

/-! ## Closure under renaming and substitution -/

theorem fields_map_rel {fs fs' : List (String × Term)} {R S : Term → Term → Prop}
    (g g' : Term → Term) (rel : ∀ p ∈ fs.zip fs', R p.1.2 p.2.2) (hg : ∀ x y, R x y → S (g x) (g' y)) :
    ∀ p ∈ (fs.map fun f => (f.1, g f.2)).zip (fs'.map fun f => (f.1, g' f.2)), S p.1.2 p.2.2 :=
  zip_map_rel (R := fun (a b : String × Term) => R a.2 b.2)
    (S := fun (a b : String × Term) => S a.2 b.2) _ _ rel (fun x y h => hg x.2 y.2 h)

theorem fields_map_names {fs fs' : List (String × Term)} (g g' : Term → Term)
    (names : fs.map Prod.fst = fs'.map Prod.fst) :
    (fs.map fun f => (f.1, g f.2)).map Prod.fst = (fs'.map fun f => (f.1, g' f.2)).map Prod.fst := by
  rw [names_map, names_map, names]

theorem steps_rename {t u : Term} (f : Nat → Nat) (h : Steps t u) : Steps (t.rename f) (u.rename f) := by
  rw [rename_eq_substitute, rename_eq_substitute]; exact steps_substitute _ h

theorem ahead_rename {t t' : Term} (h : Ahead t t') : ∀ f : Nat → Nat, Ahead (t.rename f) (t'.rename f) := by
  induction h with
  | run s _ ih => intro f; exact .run (steps_rename f s) (ih f)
  | hole n len _ ih =>
    intro f; simp only [Term.rename]
    exact .hole n (by simp [len]) (zip_map_rel (R := fun x y => ∀ f : Nat → Nat, Ahead (Term.rename f x) (Term.rename f y)) _ _ ih (fun x y h => h f))
  | bound i => intro f; exact .refl _
  | lam _ ih => intro f; simp only [Term.rename]; exact .lam (ih _)
  | app _ _ i1 i2 => intro f; simp only [Term.rename]; exact .app (i1 f) (i2 f)
  | mix _ _ i1 i2 => intro f; simp only [Term.rename]; exact .mix (i1 f) (i2 f)
  | fix _ _ i1 i2 => intro f; simp only [Term.rename]; exact .fix (i1 f) (i2 f)
  | specification _ _ i1 i2 => intro f; simp only [Term.rename]; exact .specification (i1 f) (i2 f)
  | prototype _ _ i1 i2 => intro f; simp only [Term.rename]; exact .prototype (i1 f) (i2 f)
  | reflect _ ih => intro f; simp only [Term.rename]; exact .reflect (ih f)
  | metadata _ ih => intro f; simp only [Term.rename]; exact .metadata (ih f)
  | project _ ih => intro f; simp only [Term.rename]; exact .project (ih f)
  | nat n => intro f; exact .refl _
  | boolean b => intro f; exact .refl _
  | label l => intro f; exact .refl _
  | binary op _ _ i1 i2 => intro f; simp only [Term.rename]; exact .binary op (i1 f) (i2 f)
  | extend _ names _ i1 i2 =>
    intro f; simp only [Term.rename]
    exact .extend (i1 f) (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ f : Nat → Nat, Ahead (Term.rename f x) (Term.rename f y)) _ _ i2 (fun x y h => h f))
  | record names _ ih =>
    intro f; simp only [Term.rename]
    exact .record (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ f : Nat → Nat, Ahead (Term.rename f x) (Term.rename f y)) _ _ ih (fun x y h => h f))
  | get name _ ih => intro f; simp only [Term.rename]; exact .get name (ih f)
  | ifZero _ _ _ i1 i2 i3 =>
    intro f; simp only [Term.rename]; exact .ifZero (i1 f) (i2 f) (i3 _)
  | inject l _ ih => intro f; simp only [Term.rename]; exact .inject l (ih f)
  | case _ names _ i1 i2 =>
    intro f; simp only [Term.rename]
    exact .case (i1 f) (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ f : Nat → Nat, Ahead (Term.rename f x) (Term.rename f y)) _ _ i2 (fun x y h => h _))
  | ifBool _ _ _ i1 i2 i3 => intro f; simp only [Term.rename]; exact .ifBool (i1 f) (i2 f) (i3 f)
  | perform _ ih => intro f; simp only [Term.rename]; exact .perform (ih f)
  | done _ ih => intro f; simp only [Term.rename]; exact .done (ih f)

theorem lift_rel {σ σ' : Nat → Term} (h : ∀ n, Ahead (σ n) (σ' n)) :
    ∀ n, Ahead (liftSubstitution σ n) (liftSubstitution σ' n)
  | 0 => .bound 0
  | n + 1 => ahead_rename (h n) _

/-- Substituting related terms into related terms gives related terms. -/
theorem ahead_substitute {t t' : Term} (h : Ahead t t') :
    ∀ {σ σ' : Nat → Term}, (∀ n, Ahead (σ n) (σ' n)) → Ahead (t.substitute σ) (t'.substitute σ') := by
  induction h with
  | run s _ ih => intro σ σ' hσ; exact .run (steps_substitute σ s) (ih hσ)
  | hole n len _ ih =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .hole n (by simp [len]) (zip_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Ahead (σ n) (σ' n)) → Ahead (x.substitute σ) (y.substitute σ')) _ _ ih (fun x y h => h hσ))
  | bound i => intro σ σ' hσ; simp only [Term.substitute]; exact hσ i
  | lam _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .lam (ih (lift_rel hσ))
  | app _ _ i1 i2 => intro σ σ' hσ; simp only [Term.substitute]; exact .app (i1 hσ) (i2 hσ)
  | mix _ _ i1 i2 => intro σ σ' hσ; simp only [Term.substitute]; exact .mix (i1 hσ) (i2 hσ)
  | fix _ _ i1 i2 => intro σ σ' hσ; simp only [Term.substitute]; exact .fix (i1 hσ) (i2 hσ)
  | specification _ _ i1 i2 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .specification (i1 hσ) (i2 hσ)
  | prototype _ _ i1 i2 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .prototype (i1 hσ) (i2 hσ)
  | reflect _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .reflect (ih hσ)
  | metadata _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .metadata (ih hσ)
  | project _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .project (ih hσ)
  | nat n => intro σ σ' hσ; simp only [Term.substitute]; exact .refl _
  | boolean b => intro σ σ' hσ; simp only [Term.substitute]; exact .refl _
  | label l => intro σ σ' hσ; simp only [Term.substitute]; exact .refl _
  | binary op _ _ i1 i2 => intro σ σ' hσ; simp only [Term.substitute]; exact .binary op (i1 hσ) (i2 hσ)
  | extend _ names _ i1 i2 =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .extend (i1 hσ) (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Ahead (σ n) (σ' n)) → Ahead (x.substitute σ) (y.substitute σ')) _ _ i2 (fun x y h => h hσ))
  | record names _ ih =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .record (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Ahead (σ n) (σ' n)) → Ahead (x.substitute σ) (y.substitute σ')) _ _ ih (fun x y h => h hσ))
  | get name _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .get name (ih hσ)
  | ifZero _ _ _ i1 i2 i3 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .ifZero (i1 hσ) (i2 hσ) (i3 (lift_rel hσ))
  | inject l _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .inject l (ih hσ)
  | case _ names _ i1 i2 =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .case (i1 hσ) (fields_map_names _ _ names)
      (fields_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Ahead (σ n) (σ' n)) → Ahead (x.substitute σ) (y.substitute σ')) _ _ i2 (fun x y h => h (lift_rel hσ)))
  | ifBool _ _ _ i1 i2 i3 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .ifBool (i1 hσ) (i2 hσ) (i3 hσ)
  | perform _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .perform (ih hσ)
  | done _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .done (ih hσ)

theorem single_rel {a a' : Term} (h : Ahead a a') : ∀ n, Ahead (single a n) (single a' n)
  | 0 => h
  | n + 1 => .bound n

theorem ahead_instantiate {b b' a a' : Term} (hb : Ahead b b') (ha : Ahead a a') :
    Ahead (instantiate b a) (instantiate b' a') := by
  rw [instantiate_eq, instantiate_eq]; exact ahead_substitute hb (single_rel ha)

theorem ahead_mixBody {l l' u u' : Term} (hl : Ahead l l') (hu : Ahead u u') :
    Ahead (mixBody l u) (mixBody l' u') :=
  .lam (.lam (.app (.app (ahead_rename hu _) (.bound 1))
    (.app (.app (ahead_rename hl _) (.bound 1)) (.bound 0))))

end Obend.Equiv
end
