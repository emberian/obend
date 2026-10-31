module
/-
# Obend.Leaf.UpTo — reduction in context, up to a base of unfolding pairs

`Ahead` (`Obend.Equiv.Ahead`) relates a term to the same term with subterms run ahead. It cannot
relate two *different* recursive objects: `O = fix S seed` and its flattening `F = fix S' {}` each
unfold to a row whose methods mention the object itself, `O` on one side and `F` on the other, so a
finite derivation relating them would have to contain itself. `Joins B` is `Ahead` with two more
rules: the right side may also have been run (`back`), and a pair of `B` is related outright
(`base`). It is sound for `≈b` when `B` is a **base** (`Base`): every pair is closed, and both sides
take at least one step to terms that `Joins B` relates (`Base.unfold`), with the pair itself free to
appear again inside. This is the up-to technique of bisimulation (Sangiorgi), made inductive by
closing over a set of pairs whose one-step unfolding is checked once.

`Ahead` is the instance `B = ⊥` (`Joins.of_ahead`). The simulations are `step_ahead` and
`step_behind`, as for `Ahead`, with the base pairs and the right-hand runs as two new cases each;
`bequiv_of_joins` is the conclusion.
-/
public import Obend.Logic.Claim
@[expose] public section
namespace Obend.Leaf
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic (Closed closed_subst closed_rename)
set_option autoImplicit false

/-- `t` and `t'` are one term up to reduction in context on either side and the pairs of `B`. -/
inductive Joins (B : Term → Term → Prop) : Term → Term → Prop where
  | base {o f : Term} : B o f → Joins B o f
  | run {t m t' : Term} : Steps t m → Joins B m t' → Joins B t t'
  | back {t t' m' : Term} : Steps t' m' → Joins B t m' → Joins B t t'
  | hole (n : Nat) {σ σ' : List Term} : σ.length = σ'.length →
      (∀ p ∈ σ.zip σ', Joins B p.1 p.2) → Joins B (.hole n σ) (.hole n σ')
  | bound (i : Nat) : Joins B (.bound i) (.bound i)
  | lam {b b' : Term} : Joins B b b' → Joins B (.lam b) (.lam b')
  | app {f f' a a' : Term} : Joins B f f' → Joins B a a' → Joins B (.app f a) (.app f' a')
  | mix {l l' u u' : Term} : Joins B l l' → Joins B u u' → Joins B (.mix l u) (.mix l' u')
  | fix {s s' i i' : Term} : Joins B s s' → Joins B i i' → Joins B (.fix s i) (.fix s' i')
  | specification {m m' e e' : Term} : Joins B m m' → Joins B e e' →
      Joins B (.specification m e) (.specification m' e')
  | prototype {s s' g g' : Term} : Joins B s s' → Joins B g g' →
      Joins B (.prototype s g) (.prototype s' g')
  | reflect {p p' : Term} : Joins B p p' → Joins B (.reflect p) (.reflect p')
  | metadata {p p' : Term} : Joins B p p' → Joins B (.metadata p) (.metadata p')
  | project {p p' : Term} : Joins B p p' → Joins B (.project p) (.project p')
  | nat (n : Nat) : Joins B (.nat n) (.nat n)
  | boolean (b : Bool) : Joins B (.boolean b) (.boolean b)
  | label (l : String) : Joins B (.label l) (.label l)
  | binary (op : Primitive) {l l' r r' : Term} : Joins B l l' → Joins B r r' →
      Joins B (.binary op l r) (.binary op l' r')
  | extend {i i' : Term} {fs fs' : List (String × Term)} : Joins B i i' →
      fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', Joins B p.1.2 p.2.2) →
      Joins B (.extend i fs) (.extend i' fs')
  | record {fs fs' : List (String × Term)} :
      fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', Joins B p.1.2 p.2.2) →
      Joins B (.record fs) (.record fs')
  | get (name : String) {g g' : Term} : Joins B g g' → Joins B (.get g name) (.get g' name)
  | ifZero {v v' z z' s s' : Term} : Joins B v v' → Joins B z z' → Joins B s s' →
      Joins B (.ifZero v z s) (.ifZero v' z' s')
  | inject (l : String) {p p' : Term} : Joins B p p' → Joins B (.inject l p) (.inject l p')
  | case {sc sc' : Term} {arms arms' : List (String × Term)} : Joins B sc sc' →
      arms.map Prod.fst = arms'.map Prod.fst → (∀ p ∈ arms.zip arms', Joins B p.1.2 p.2.2) →
      Joins B (.case sc arms) (.case sc' arms')
  | ifBool {c c' x x' y y' : Term} : Joins B c c' → Joins B x x' → Joins B y y' →
      Joins B (.ifBool c x y) (.ifBool c' x' y')
  | perform {p p' : Term} : Joins B p p' → Joins B (.perform p) (.perform p')
  | done {v v' : Term} : Joins B v v' → Joins B (.done v) (.done v')

/-- Every pair of `B` is closed, so substitution leaves it alone. -/
def ClosedPairs (B : Term → Term → Prop) : Prop := ∀ {o f : Term}, B o f → Closed o ∧ Closed f

/-- A base: closed pairs, each side taking at least one step to terms the relation joins. -/
structure Base (B : Term → Term → Prop) : Prop where
  closed : ClosedPairs B
  unfold : ∀ {o f : Term}, B o f →
    ∃ o₁ o' f₁ f', Step o o₁ ∧ Steps o₁ o' ∧ Step f f₁ ∧ Steps f₁ f' ∧ Joins B o' f'

section
variable {B : Term → Term → Prop}

/-- `Ahead` is the instance with no base pairs. -/
theorem Joins.of_ahead {t t' : Term} (h : Ahead t t') : Joins B t t' := by
  induction h with
  | run s _ ih => exact .run s ih
  | hole n len _ ih => exact .hole n len ih
  | bound i => exact .bound i
  | lam _ ih => exact .lam ih
  | app _ _ i1 i2 => exact .app i1 i2
  | mix _ _ i1 i2 => exact .mix i1 i2
  | fix _ _ i1 i2 => exact .fix i1 i2
  | specification _ _ i1 i2 => exact .specification i1 i2
  | prototype _ _ i1 i2 => exact .prototype i1 i2
  | reflect _ ih => exact .reflect ih
  | metadata _ ih => exact .metadata ih
  | project _ ih => exact .project ih
  | nat n => exact .nat n
  | boolean b => exact .boolean b
  | label l => exact .label l
  | binary op _ _ i1 i2 => exact .binary op i1 i2
  | extend _ names _ i1 i2 => exact .extend i1 names i2
  | record names _ ih => exact .record names ih
  | get name _ ih => exact .get name ih
  | ifZero _ _ _ i1 i2 i3 => exact .ifZero i1 i2 i3
  | inject l _ ih => exact .inject l ih
  | case _ names _ i1 i2 => exact .case i1 names i2
  | ifBool _ _ _ i1 i2 i3 => exact .ifBool i1 i2 i3
  | perform _ ih => exact .perform ih
  | done _ ih => exact .done ih

theorem Joins.refl (t : Term) : Joins B t t := .of_ahead (Ahead.refl t)

theorem Joins.ofSteps {t t' : Term} (h : Steps t t') : Joins B t t' := .of_ahead (Ahead.ofStepsRefl h)

/-! ## Closure under renaming and substitution -/

theorem joins_rename (hB : ClosedPairs B) {t t' : Term} (h : Joins B t t') :
    ∀ f : Nat → Nat, Joins B (t.rename f) (t'.rename f) := by
  induction h with
  | base hb =>
    intro f; rw [closed_rename (hB hb).1, closed_rename (hB hb).2]; exact .base hb
  | run s _ ih => intro f; exact .run (steps_rename f s) (ih f)
  | back s _ ih => intro f; exact .back (steps_rename f s) (ih f)
  | hole n len _ ih =>
    intro f; simp only [Term.rename]
    exact .hole n (by simp [len]) (zip_map_rel (R := fun x y => ∀ f : Nat → Nat, Joins B (Term.rename f x) (Term.rename f y)) _ _ ih (fun x y h => h f))
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
    exact .extend (i1 f) (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ f : Nat → Nat, Joins B (Term.rename f x) (Term.rename f y)) _ _ i2 (fun x y h => h f))
  | record names _ ih =>
    intro f; simp only [Term.rename]
    exact .record (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ f : Nat → Nat, Joins B (Term.rename f x) (Term.rename f y)) _ _ ih (fun x y h => h f))
  | get name _ ih => intro f; simp only [Term.rename]; exact .get name (ih f)
  | ifZero _ _ _ i1 i2 i3 =>
    intro f; simp only [Term.rename]; exact .ifZero (i1 f) (i2 f) (i3 _)
  | inject l _ ih => intro f; simp only [Term.rename]; exact .inject l (ih f)
  | case _ names _ i1 i2 =>
    intro f; simp only [Term.rename]
    exact .case (i1 f) (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ f : Nat → Nat, Joins B (Term.rename f x) (Term.rename f y)) _ _ i2 (fun x y h => h _))
  | ifBool _ _ _ i1 i2 i3 => intro f; simp only [Term.rename]; exact .ifBool (i1 f) (i2 f) (i3 f)
  | perform _ ih => intro f; simp only [Term.rename]; exact .perform (ih f)
  | done _ ih => intro f; simp only [Term.rename]; exact .done (ih f)

theorem joins_lift (hB : ClosedPairs B) {σ σ' : Nat → Term} (h : ∀ n, Joins B (σ n) (σ' n)) :
    ∀ n, Joins B (liftSubstitution σ n) (liftSubstitution σ' n)
  | 0 => .bound 0
  | n + 1 => joins_rename hB (h n) _

/-- Substituting joined terms into joined terms gives joined terms. -/
theorem joins_substitute (hB : ClosedPairs B) {t t' : Term} (h : Joins B t t') :
    ∀ {σ σ' : Nat → Term}, (∀ n, Joins B (σ n) (σ' n)) → Joins B (t.substitute σ) (t'.substitute σ') := by
  induction h with
  | base hb =>
    intro σ σ' _; rw [closed_subst (hB hb).1, closed_subst (hB hb).2]; exact .base hb
  | run s _ ih => intro σ σ' hσ; exact .run (steps_substitute σ s) (ih hσ)
  | back s _ ih => intro σ σ' hσ; exact .back (steps_substitute σ' s) (ih hσ)
  | hole n len _ ih =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .hole n (by simp [len]) (zip_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Joins B (σ n) (σ' n)) → Joins B (x.substitute σ) (y.substitute σ')) _ _ ih (fun x y h => h hσ))
  | bound i => intro σ σ' hσ; simp only [Term.substitute]; exact hσ i
  | lam _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .lam (ih (joins_lift hB hσ))
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
    exact .extend (i1 hσ) (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Joins B (σ n) (σ' n)) → Joins B (x.substitute σ) (y.substitute σ')) _ _ i2 (fun x y h => h hσ))
  | record names _ ih =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .record (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Joins B (σ n) (σ' n)) → Joins B (x.substitute σ) (y.substitute σ')) _ _ ih (fun x y h => h hσ))
  | get name _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .get name (ih hσ)
  | ifZero _ _ _ i1 i2 i3 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .ifZero (i1 hσ) (i2 hσ) (i3 (joins_lift hB hσ))
  | inject l _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .inject l (ih hσ)
  | case _ names _ i1 i2 =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .case (i1 hσ) (fields_map_names _ _ names)
      (fields_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Joins B (σ n) (σ' n)) → Joins B (x.substitute σ) (y.substitute σ')) _ _ i2 (fun x y h => h (joins_lift hB hσ)))
  | ifBool _ _ _ i1 i2 i3 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .ifBool (i1 hσ) (i2 hσ) (i3 hσ)
  | perform _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .perform (ih hσ)
  | done _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .done (ih hσ)

theorem joins_single {a a' : Term} (h : Joins B a a') : ∀ n, Joins B (single a n) (single a' n)
  | 0 => h
  | n + 1 => .bound n

theorem joins_instantiate (hB : ClosedPairs B) {b b' a a' : Term} (hb : Joins B b b') (ha : Joins B a a') :
    Joins B (instantiate b a) (instantiate b' a') := by
  rw [instantiate_eq, instantiate_eq]; exact joins_substitute hB hb (joins_single ha)

theorem joins_mixBody (hB : ClosedPairs B) {l l' u u' : Term} (hl : Joins B l l') (hu : Joins B u u') :
    Joins B (mixBody l u) (mixBody l' u') :=
  .lam (.lam (.app (.app (joins_rename hB hu _) (.bound 1))
    (.app (.app (joins_rename hB hl _) (.bound 1)) (.bound 0))))

/-! ## Inversions -/

theorem Base.no_value_right (hB : Base B) {o f : Term} (hb : B o f) (v : Value f) : False := by
  obtain ⟨_, _, _, _, _, _, st, _⟩ := hB.unfold hb
  exact value_no_step' v st

theorem Base.no_value_left (hB : Base B) {o f : Term} (hb : B o f) (v : Value o) : False := by
  obtain ⟨_, _, _, _, st, _⟩ := hB.unfold hb
  exact value_no_step' v st

variable {t t' : Term}

theorem inv_lam_ahead (hB : Base B) {p' : Term} (h : Joins B t (.lam p')) :
    ∃ p, Steps t (.lam p) ∧ Joins B p p' := by
  generalize e : Term.lam p' = u at h
  induction h
  case base hb => subst e; exact (hB.no_value_right hb (.function _)).elim
  case run s _ ih => obtain ⟨p, s2, a⟩ := ih e; exact ⟨p, steps_trans s s2, a⟩
  case back s _ ih => subst e; exact ih (value_steps_eq (.function _) s).symm
  case lam a _ => cases e; exact ⟨_, .refl _, a⟩
  all_goals cases e

theorem inv_spec_ahead (hB : Base B) {m' e' : Term} (h : Joins B t (.specification m' e')) :
    ∃ m e, Steps t (.specification m e) ∧ Joins B m m' ∧ Joins B e e' := by
  generalize eq : Term.specification m' e' = u at h
  induction h
  case base hb => subst eq; exact (hB.no_value_right hb (.specification _ _)).elim
  case run s _ ih => obtain ⟨m, e, s2, a, b⟩ := ih eq; exact ⟨m, e, steps_trans s s2, a, b⟩
  case back s _ ih => subst eq; exact ih (value_steps_eq (.specification _ _) s).symm
  case specification a b _ _ => cases eq; exact ⟨_, _, .refl _, a, b⟩
  all_goals cases eq

theorem inv_proto_ahead (hB : Base B) {s' g' : Term} (h : Joins B t (.prototype s' g')) :
    ∃ s g, Steps t (.prototype s g) ∧ Joins B s s' ∧ Joins B g g' := by
  generalize eq : Term.prototype s' g' = u at h
  induction h
  case base hb => subst eq; exact (hB.no_value_right hb (.prototype _ _)).elim
  case run st _ ih => obtain ⟨m, e, s2, a, b⟩ := ih eq; exact ⟨m, e, steps_trans st s2, a, b⟩
  case back s _ ih => subst eq; exact ih (value_steps_eq (.prototype _ _) s).symm
  case prototype a b _ _ => cases eq; exact ⟨_, _, .refl _, a, b⟩
  all_goals cases eq

theorem inv_inject_ahead (hB : Base B) {l : String} {p' : Term} (h : Joins B t (.inject l p')) :
    ∃ p, Steps t (.inject l p) ∧ Joins B p p' := by
  generalize eq : Term.inject l p' = u at h
  induction h
  case base hb => subst eq; exact (hB.no_value_right hb (.inject _ _)).elim
  case run st _ ih => obtain ⟨p, s2, a⟩ := ih eq; exact ⟨p, steps_trans st s2, a⟩
  case back s _ ih => subst eq; exact ih (value_steps_eq (.inject _ _) s).symm
  case inject a _ => cases eq; exact ⟨_, .refl _, a⟩
  all_goals cases eq

theorem inv_record_ahead (hB : Base B) {fs' : List (String × Term)} (h : Joins B t (.record fs')) :
    ∃ fs, Steps t (.record fs) ∧ fs.map Prod.fst = fs'.map Prod.fst ∧
      ∀ p ∈ fs.zip fs', Joins B p.1.2 p.2.2 := by
  generalize eq : Term.record fs' = u at h
  induction h
  case base hb => subst eq; exact (hB.no_value_right hb (.record _)).elim
  case run st _ ih => obtain ⟨fs, s2, a, b⟩ := ih eq; exact ⟨fs, steps_trans st s2, a, b⟩
  case back s _ ih => subst eq; exact ih (value_steps_eq (.record _) s).symm
  case record names rel _ => cases eq; exact ⟨_, .refl _, names, rel⟩
  all_goals cases eq

theorem inv_literal_ahead (hB : Base B) {v : Term} (lit : Literal v) (h : Joins B t v) : Steps t v := by
  induction h
  case base hb => exact (hB.no_value_right hb lit.value).elim
  case run st _ ih => exact steps_trans st (ih lit)
  case back s _ ih => cases value_steps_eq lit.value s; exact ih lit
  case nat => exact .refl _
  case boolean => exact .refl _
  case label => exact .refl _
  all_goals cases lit

/-- A term joined to a value reaches a value joined to it. -/
theorem inv_value_ahead (hB : Base B) {v' : Term} (value : Value v') (h : Joins B t v') :
    ∃ v, Steps t v ∧ Value v ∧ Joins B v v' := by
  cases value with
  | function p' => obtain ⟨p, s, a⟩ := inv_lam_ahead hB h; exact ⟨_, s, .function _, .lam a⟩
  | natural n => exact ⟨_, inv_literal_ahead hB (.nat n) h, .natural n, .refl _⟩
  | boolean b => exact ⟨_, inv_literal_ahead hB (.boolean b) h, .boolean b, .refl _⟩
  | label l => exact ⟨_, inv_literal_ahead hB (.label l) h, .label l, .refl _⟩
  | record fs' =>
    obtain ⟨fs, s, names, rel⟩ := inv_record_ahead hB h; exact ⟨_, s, .record _, .record names rel⟩
  | specification m e =>
    obtain ⟨_, _, s, a, b⟩ := inv_spec_ahead hB h; exact ⟨_, s, .specification _ _, .specification a b⟩
  | prototype s g =>
    obtain ⟨_, _, st, a, b⟩ := inv_proto_ahead hB h; exact ⟨_, st, .prototype _ _, .prototype a b⟩
  | inject l p =>
    obtain ⟨_, s, a⟩ := inv_inject_ahead hB h; exact ⟨_, s, .inject _ _, .inject l a⟩

theorem inv_lam_behind (hB : Base B) {p : Term} (h : Joins B (.lam p) t') :
    ∃ p', Steps t' (.lam p') ∧ Joins B p p' := by
  generalize e : Term.lam p = u at h
  induction h
  case base hb => subst e; exact (hB.no_value_left hb (.function _)).elim
  case run s _ ih => subst e; exact ih (value_steps_eq (.function _) s).symm
  case back s _ ih => obtain ⟨p', s2, a⟩ := ih e; exact ⟨p', steps_trans s s2, a⟩
  case lam a _ => cases e; exact ⟨_, .refl _, a⟩
  all_goals cases e

theorem inv_spec_behind (hB : Base B) {m e : Term} (h : Joins B (.specification m e) t') :
    ∃ m' e', Steps t' (.specification m' e') ∧ Joins B m m' ∧ Joins B e e' := by
  generalize eq : Term.specification m e = u at h
  induction h
  case base hb => subst eq; exact (hB.no_value_left hb (.specification _ _)).elim
  case run s _ ih => subst eq; exact ih (value_steps_eq (.specification _ _) s).symm
  case back s _ ih => obtain ⟨m', e', s2, a, b⟩ := ih eq; exact ⟨m', e', steps_trans s s2, a, b⟩
  case specification a b _ _ => cases eq; exact ⟨_, _, .refl _, a, b⟩
  all_goals cases eq

theorem inv_proto_behind (hB : Base B) {s g : Term} (h : Joins B (.prototype s g) t') :
    ∃ s' g', Steps t' (.prototype s' g') ∧ Joins B s s' ∧ Joins B g g' := by
  generalize eq : Term.prototype s g = u at h
  induction h
  case base hb => subst eq; exact (hB.no_value_left hb (.prototype _ _)).elim
  case run st _ ih => subst eq; exact ih (value_steps_eq (.prototype _ _) st).symm
  case back st _ ih => obtain ⟨s', g', s2, a, b⟩ := ih eq; exact ⟨s', g', steps_trans st s2, a, b⟩
  case prototype a b _ _ => cases eq; exact ⟨_, _, .refl _, a, b⟩
  all_goals cases eq

theorem inv_inject_behind (hB : Base B) {l : String} {p : Term} (h : Joins B (.inject l p) t') :
    ∃ p', Steps t' (.inject l p') ∧ Joins B p p' := by
  generalize eq : Term.inject l p = u at h
  induction h
  case base hb => subst eq; exact (hB.no_value_left hb (.inject _ _)).elim
  case run st _ ih => subst eq; exact ih (value_steps_eq (.inject _ _) st).symm
  case back st _ ih => obtain ⟨p', s2, a⟩ := ih eq; exact ⟨p', steps_trans st s2, a⟩
  case inject a _ => cases eq; exact ⟨_, .refl _, a⟩
  all_goals cases eq

theorem inv_record_behind (hB : Base B) {fs : List (String × Term)} (h : Joins B (.record fs) t') :
    ∃ fs', Steps t' (.record fs') ∧ fs.map Prod.fst = fs'.map Prod.fst ∧
      ∀ p ∈ fs.zip fs', Joins B p.1.2 p.2.2 := by
  generalize eq : Term.record fs = u at h
  induction h
  case base hb => subst eq; exact (hB.no_value_left hb (.record _)).elim
  case run st _ ih => subst eq; exact ih (value_steps_eq (.record _) st).symm
  case back st _ ih => obtain ⟨fs', s2, a, b⟩ := ih eq; exact ⟨fs', steps_trans st s2, a, b⟩
  case record names rel _ => cases eq; exact ⟨_, .refl _, names, rel⟩
  all_goals cases eq

theorem inv_literal_behind (hB : Base B) {v : Term} (lit : Literal v) (h : Joins B v t') : Steps t' v := by
  induction h
  case base hb => exact (hB.no_value_left hb lit.value).elim
  case run st _ ih => cases value_steps_eq lit.value st; exact ih lit
  case back st _ ih => exact steps_trans st (ih lit)
  case nat => exact .refl _
  case boolean => exact .refl _
  case label => exact .refl _
  all_goals cases lit

/-- A value joined to a term: the term reaches a value joined to it. -/
theorem inv_value_behind (hB : Base B) {v : Term} (value : Value v) (h : Joins B v t') :
    ∃ v', Steps t' v' ∧ Value v' ∧ Joins B v v' := by
  cases value with
  | function p => obtain ⟨_, s, a⟩ := inv_lam_behind hB h; exact ⟨_, s, .function _, .lam a⟩
  | natural n => exact ⟨_, inv_literal_behind hB (.nat n) h, .natural n, .refl _⟩
  | boolean b => exact ⟨_, inv_literal_behind hB (.boolean b) h, .boolean b, .refl _⟩
  | label l => exact ⟨_, inv_literal_behind hB (.label l) h, .label l, .refl _⟩
  | record fs =>
    obtain ⟨_, s, n, r⟩ := inv_record_behind hB h; exact ⟨_, s, .record _, .record n r⟩
  | specification m e =>
    obtain ⟨_, _, s, a, b⟩ := inv_spec_behind hB h; exact ⟨_, s, .specification _ _, .specification a b⟩
  | prototype s g =>
    obtain ⟨_, _, st, a, b⟩ := inv_proto_behind hB h; exact ⟨_, st, .prototype _ _, .prototype a b⟩
  | inject l p =>
    obtain ⟨_, s, a⟩ := inv_inject_behind hB h; exact ⟨_, s, .inject _ _, .inject l a⟩

end

/-! ## The two simulations -/

section
variable {B : Term → Term → Prop}

/-- A step of the right side is matched by reduction of the left side. -/
theorem step_ahead (hB : Base B) {t t' : Term} (h : Joins B t t') :
    ∀ {u' : Term}, Step t' u' → ∃ u, Steps t u ∧ Joins B u u' := by
  induction h with
  | base hb =>
    intro u' st
    obtain ⟨o₁, o', f₁, f', so, so', sf, sf', j⟩ := hB.unfold hb
    cases step_deterministic st sf
    exact ⟨o', .next so so', .back sf' j⟩
  | run s _ ih => intro u' st; obtain ⟨u, s2, a⟩ := ih st; exact ⟨u, steps_trans s s2, a⟩
  | back s rest ih =>
    intro u' st
    cases s with
    | refl => exact ih st
    | next st1 s1 => cases step_deterministic st st1; exact ⟨_, .refl _, .back s1 rest⟩
  | hole => intro u' st; cases st
  | bound => intro u' st; cases st
  | lam => intro u' st; cases st
  | app hf ha ihf _ =>
    intro u' st
    cases st with
    | beta body arg =>
      obtain ⟨p, s, a⟩ := inv_lam_ahead hB hf
      exact ⟨_, steps_snoc (steps_app _ s) (.beta _ _), joins_instantiate hB.closed a ha⟩
    | application _ st' =>
      obtain ⟨g, s, a⟩ := ihf st'
      exact ⟨_, steps_app _ s, .app a ha⟩
    | applySpecification m e _ =>
      obtain ⟨_, _, s, _, ae⟩ := inv_spec_ahead hB hf
      exact ⟨_, steps_snoc (steps_app _ s) (.applySpecification _ _ _), .app ae ha⟩
  | mix hl hu _ _ =>
    intro u' st; cases st; exact ⟨_, steps_one (.mix _ _), joins_mixBody hB.closed hl hu⟩
  | fix hs hi _ _ =>
    intro u' st; cases st; exact ⟨_, steps_one (.fix _ _), .app (.app hs (.fix hs hi)) hi⟩
  | specification => intro u' st; cases st
  | prototype => intro u' st; cases st
  | reflect hp ih =>
    intro u' st
    cases st with
    | reflectPrototype =>
      obtain ⟨_, _, s, a, _⟩ := inv_proto_ahead hB hp
      exact ⟨_, steps_snoc (steps_reflect s) (.reflectPrototype _ _), a⟩
    | reflectStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_reflect s, .reflect a⟩
  | metadata hp ih =>
    intro u' st
    cases st with
    | metadataSpecification =>
      obtain ⟨_, _, s, a, _⟩ := inv_spec_ahead hB hp
      exact ⟨_, steps_snoc (steps_metadata s) (.metadataSpecification _ _), a⟩
    | metadataStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_metadata s, .metadata a⟩
  | project hp ih =>
    intro u' st
    cases st with
    | projectPrototype =>
      obtain ⟨_, _, s, _, b⟩ := inv_proto_ahead hB hp
      exact ⟨_, steps_snoc (steps_project s) (.projectPrototype _ _), b⟩
    | projectStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_project s, .project a⟩
  | nat => intro u' st; cases st
  | boolean => intro u' st; cases st
  | label => intro u' st; cases st
  | binary op hl hr ihl ihr =>
    intro u' st
    cases st with
    | binaryLeft _ _ st' =>
      obtain ⟨_, s, a⟩ := ihl st'; exact ⟨_, steps_binaryLeft _ _ s, .binary _ a hr⟩
    | binaryRight _ _ v st' =>
      obtain ⟨_, sl, vl, al⟩ := inv_value_ahead hB v hl
      obtain ⟨_, sr, ar⟩ := ihr st'
      exact ⟨_, steps_trans (steps_binaryLeft _ _ sl) (steps_binaryRight _ vl sr), .binary _ al ar⟩
    | primitive _ _ _ _ vl vr hit =>
      obtain ⟨ll, lr, _⟩ := primitiveResult_literal hit
      exact ⟨_, steps_snoc (steps_trans (steps_binaryLeft _ _ (inv_literal_ahead hB ll hl))
        (steps_binaryRight _ vl (inv_literal_ahead hB lr hr))) (.primitive _ _ _ _ vl vr hit), .refl _⟩
  | extend hi names rel ihi _ =>
    intro u' st
    cases st with
    | extendTarget _ st' =>
      obtain ⟨_, s, a⟩ := ihi st'; exact ⟨_, steps_extend _ s, .extend a names rel⟩
    | extendRecord =>
      obtain ⟨_, s, n1, r1⟩ := inv_record_ahead hB hi
      obtain ⟨n2, r2⟩ := extendFields_rel n1 r1 names rel
      exact ⟨_, steps_snoc (steps_extend _ s) (.extendRecord _ _), .record n2 r2⟩
  | record => intro u' st; cases st
  | get name hg ih =>
    intro u' st
    cases st with
    | target _ st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_get _ s, .get _ a⟩
    | field _ _ _ hit =>
      obtain ⟨_, s, n1, r1⟩ := inv_record_ahead hB hg
      obtain ⟨_, hit0, a⟩ := find_right n1 r1 hit
      exact ⟨_, steps_snoc (steps_get _ s) (.field _ _ _ hit0), a⟩
  | ifZero hv hz hs ihv _ _ =>
    intro u' st
    cases st with
    | condition _ _ st' =>
      obtain ⟨_, s, a⟩ := ihv st'; exact ⟨_, steps_ifZero _ _ s, .ifZero a hz hs⟩
    | zero =>
      exact ⟨_, steps_snoc (steps_ifZero _ _ (inv_literal_ahead hB (.nat 0) hv)) (.zero _ _), hz⟩
    | successor n =>
      exact ⟨_, steps_snoc (steps_ifZero _ _ (inv_literal_ahead hB (.nat (n + 1)) hv))
        (.successor _ _ _), joins_instantiate hB.closed hs (.nat n)⟩
  | inject => intro u' st; cases st
  | case hsc names rel ihsc _ =>
    intro u' st
    cases st with
    | caseTarget _ st' =>
      obtain ⟨_, s, a⟩ := ihsc st'; exact ⟨_, steps_case _ s, .case a names rel⟩
    | caseInject _ _ _ _ hit =>
      obtain ⟨_, s, a⟩ := inv_inject_ahead hB hsc
      obtain ⟨_, hit0, ab⟩ := find_right names rel hit
      exact ⟨_, steps_snoc (steps_case _ s) (.caseInject _ _ _ _ hit0), joins_instantiate hB.closed ab a⟩
  | ifBool hc hx hy ihc _ _ =>
    intro u' st
    cases st with
    | ifCondition _ _ st' =>
      obtain ⟨_, s, a⟩ := ihc st'; exact ⟨_, steps_ifBool _ _ s, .ifBool a hx hy⟩
    | ifTrue =>
      exact ⟨_, steps_snoc (steps_ifBool _ _ (inv_literal_ahead hB (.boolean true) hc)) (.ifTrue _ _), hx⟩
    | ifFalse =>
      exact ⟨_, steps_snoc (steps_ifBool _ _ (inv_literal_ahead hB (.boolean false) hc)) (.ifFalse _ _), hy⟩
  | perform => intro u' st; cases st
  | done hv _ => intro u' st; cases st; exact ⟨_, steps_one (.done _), hv⟩

/-- A step of the left side is matched by reduction of the right side. -/
theorem step_behind (hB : Base B) {t t' : Term} (h : Joins B t t') :
    ∀ {u : Term}, Step t u → ∃ u', Steps t' u' ∧ Joins B u u' := by
  induction h with
  | base hb =>
    intro u st
    obtain ⟨o₁, o', f₁, f', so, so', sf, sf', j⟩ := hB.unfold hb
    cases step_deterministic st so
    exact ⟨f', .next sf sf', .run so' j⟩
  | run s rest ih =>
    intro u st
    cases s with
    | refl => exact ih st
    | next st1 s1 => cases step_deterministic st st1; exact ⟨_, .refl _, .run s1 rest⟩
  | back s _ ih => intro u st; obtain ⟨u', s2, a⟩ := ih st; exact ⟨u', steps_trans s s2, a⟩
  | hole => intro u st; cases st
  | bound => intro u st; cases st
  | lam => intro u st; cases st
  | app hf ha ihf _ =>
    intro u st
    cases st with
    | beta =>
      obtain ⟨_, s, a⟩ := inv_lam_behind hB hf
      exact ⟨_, steps_snoc (steps_app _ s) (.beta _ _), joins_instantiate hB.closed a ha⟩
    | application _ st' => obtain ⟨_, s, a⟩ := ihf st'; exact ⟨_, steps_app _ s, .app a ha⟩
    | applySpecification =>
      obtain ⟨_, _, s, _, ae⟩ := inv_spec_behind hB hf
      exact ⟨_, steps_snoc (steps_app _ s) (.applySpecification _ _ _), .app ae ha⟩
  | mix hl hu _ _ =>
    intro u st; cases st; exact ⟨_, steps_one (.mix _ _), joins_mixBody hB.closed hl hu⟩
  | fix hs hi _ _ =>
    intro u st; cases st; exact ⟨_, steps_one (.fix _ _), .app (.app hs (.fix hs hi)) hi⟩
  | specification => intro u st; cases st
  | prototype => intro u st; cases st
  | reflect hp ih =>
    intro u st
    cases st with
    | reflectPrototype =>
      obtain ⟨_, _, s, a, _⟩ := inv_proto_behind hB hp
      exact ⟨_, steps_snoc (steps_reflect s) (.reflectPrototype _ _), a⟩
    | reflectStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_reflect s, .reflect a⟩
  | metadata hp ih =>
    intro u st
    cases st with
    | metadataSpecification =>
      obtain ⟨_, _, s, a, _⟩ := inv_spec_behind hB hp
      exact ⟨_, steps_snoc (steps_metadata s) (.metadataSpecification _ _), a⟩
    | metadataStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_metadata s, .metadata a⟩
  | project hp ih =>
    intro u st
    cases st with
    | projectPrototype =>
      obtain ⟨_, _, s, _, b⟩ := inv_proto_behind hB hp
      exact ⟨_, steps_snoc (steps_project s) (.projectPrototype _ _), b⟩
    | projectStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_project s, .project a⟩
  | nat => intro u st; cases st
  | boolean => intro u st; cases st
  | label => intro u st; cases st
  | binary op hl hr ihl ihr =>
    intro u st
    cases st with
    | binaryLeft _ _ st' =>
      obtain ⟨_, s, a⟩ := ihl st'; exact ⟨_, steps_binaryLeft _ _ s, .binary _ a hr⟩
    | binaryRight _ _ v st' =>
      obtain ⟨_, sl, vl, al⟩ := inv_value_behind hB v hl
      obtain ⟨_, s, a⟩ := ihr st'
      exact ⟨_, steps_trans (steps_binaryLeft _ _ sl) (steps_binaryRight _ vl s), .binary _ al a⟩
    | primitive _ _ _ _ vl vr hit =>
      obtain ⟨ll, lr, _⟩ := primitiveResult_literal hit
      exact ⟨_, steps_snoc (steps_trans (steps_binaryLeft _ _ (inv_literal_behind hB ll hl))
        (steps_binaryRight _ vl (inv_literal_behind hB lr hr))) (.primitive _ _ _ _ vl vr hit), .refl _⟩
  | extend hi names rel ihi _ =>
    intro u st
    cases st with
    | extendTarget _ st' =>
      obtain ⟨_, s, a⟩ := ihi st'; exact ⟨_, steps_extend _ s, .extend a names rel⟩
    | extendRecord =>
      obtain ⟨_, s, n1, r1⟩ := inv_record_behind hB hi
      obtain ⟨n2, r2⟩ := extendFields_rel n1 r1 names rel
      exact ⟨_, steps_snoc (steps_extend _ s) (.extendRecord _ _), .record n2 r2⟩
  | record => intro u st; cases st
  | get name hg ih =>
    intro u st
    cases st with
    | target _ st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_get _ s, .get _ a⟩
    | field _ _ _ hit =>
      obtain ⟨_, s, n1, r1⟩ := inv_record_behind hB hg
      obtain ⟨_, hit', a⟩ := find_left n1 r1 hit
      exact ⟨_, steps_snoc (steps_get _ s) (.field _ _ _ hit'), a⟩
  | ifZero hv hz hs ihv _ _ =>
    intro u st
    cases st with
    | condition _ _ st' =>
      obtain ⟨_, s, a⟩ := ihv st'; exact ⟨_, steps_ifZero _ _ s, .ifZero a hz hs⟩
    | zero =>
      exact ⟨_, steps_snoc (steps_ifZero _ _ (inv_literal_behind hB (.nat 0) hv)) (.zero _ _), hz⟩
    | successor n =>
      exact ⟨_, steps_snoc (steps_ifZero _ _ (inv_literal_behind hB (.nat (n + 1)) hv))
        (.successor _ _ _), joins_instantiate hB.closed hs (.nat n)⟩
  | inject => intro u st; cases st
  | case hsc names rel ihsc _ =>
    intro u st
    cases st with
    | caseTarget _ st' =>
      obtain ⟨_, s, a⟩ := ihsc st'; exact ⟨_, steps_case _ s, .case a names rel⟩
    | caseInject _ _ _ _ hit =>
      obtain ⟨_, s, a⟩ := inv_inject_behind hB hsc
      obtain ⟨_, hit', ab⟩ := find_left names rel hit
      exact ⟨_, steps_snoc (steps_case _ s) (.caseInject _ _ _ _ hit'), joins_instantiate hB.closed ab a⟩
  | ifBool hc hx hy ihc _ _ =>
    intro u st
    cases st with
    | ifCondition _ _ st' =>
      obtain ⟨_, s, a⟩ := ihc st'; exact ⟨_, steps_ifBool _ _ s, .ifBool a hx hy⟩
    | ifTrue =>
      exact ⟨_, steps_snoc (steps_ifBool _ _ (inv_literal_behind hB (.boolean true) hc)) (.ifTrue _ _), hx⟩
    | ifFalse =>
      exact ⟨_, steps_snoc (steps_ifBool _ _ (inv_literal_behind hB (.boolean false) hc)) (.ifFalse _ _), hy⟩
  | perform => intro u st; cases st
  | done hv _ => intro u st; cases st; exact ⟨_, steps_one (.done _), hv⟩

/-! ## Completed runs, and `≈b` -/

theorem evaluates_behind (hB : Base B) {t t' v : Term} (h : Joins B t t') (e : Evaluates t v) :
    ∃ v', Evaluates t' v' ∧ Joins B v v' := by
  obtain ⟨s, val⟩ := e
  induction s generalizing t' with
  | refl =>
    obtain ⟨v', s', vv', a⟩ := inv_value_behind hB val h
    exact ⟨v', ⟨s', vv'⟩, a⟩
  | next st _ ih =>
    obtain ⟨_, s1, a⟩ := step_behind hB h st
    obtain ⟨v', ⟨s2, val'⟩, a2⟩ := ih a val
    exact ⟨v', ⟨steps_trans s1 s2, val'⟩, a2⟩

theorem evaluates_ahead (hB : Base B) {t t' v' : Term} (h : Joins B t t') (e : Evaluates t' v') :
    ∃ v, Evaluates t v ∧ Joins B v v' := by
  obtain ⟨s, val⟩ := e
  induction s generalizing t with
  | refl =>
    obtain ⟨v, s, vv, a⟩ := inv_value_ahead hB val h
    exact ⟨v, ⟨s, vv⟩, a⟩
  | next st _ ih =>
    obtain ⟨_, s1, a⟩ := step_ahead hB h st
    obtain ⟨v, ⟨s2, vv⟩, a2⟩ := ih a val
    exact ⟨v, ⟨steps_trans s1 s2, vv⟩, a2⟩

theorem sameRuns_of_joins (hB : Base B) {t t' : Term} (h : Joins B t t') : SameRuns t t' where
  halts o := by
    constructor
    · rintro ⟨v, e, obs⟩
      obtain ⟨v', e', a⟩ := evaluates_behind hB h e
      have := value_steps_eq e'.2 (inv_literal_behind hB (observes_literal obs) a)
      exact ⟨v, this ▸ e', obs⟩
    · rintro ⟨v', e', obs⟩
      obtain ⟨v, e, a⟩ := evaluates_ahead hB h e'
      have := value_steps_eq e.2 (inv_literal_ahead hB (observes_literal obs) a)
      exact ⟨v, e, this ▸ obs⟩
  converges := by
    constructor
    · rintro ⟨v, e⟩; obtain ⟨v', e', _⟩ := evaluates_behind hB h e; exact ⟨v', e'⟩
    · rintro ⟨v', e'⟩; obtain ⟨v, e, _⟩ := evaluates_ahead hB h e'; exact ⟨v, e⟩

/-- **Joined terms are behaviourally equivalent**, for every base. -/
theorem bequiv_of_joins (hB : Base B) {t t' : Term} (h : Joins B t t') : t ≈b t' := fun ρ C =>
  sameRuns_of_joins hB (joins_instantiate hB.closed (.refl C) (joins_substitute hB.closed h fun n => .refl (ρ n)))

end

end Obend.Leaf
end
