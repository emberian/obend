module
/- `Ahead` is a simulation in both directions for Core4's weak-head reduction. A step of the term
that is behind is matched by zero or more steps of the term that is ahead (`step_behind`); a step
of the term that is ahead is matched by one or more steps of the term that is behind
(`step_ahead`). Determinism of `Step` is what lets the term behind catch up without branching. -/
public import Obend.Equiv.Ahead
@[expose] public section
namespace Obend.Equiv
open Obend.Core.Term
set_option autoImplicit false

/-! ## Steps under evaluation frames -/

theorem steps_app {f g : Term} (a : Term) (h : Steps f g) : Steps (.app f a) (.app g a) :=
  steps_congr (fun x => .app x a) (fun s => .application a s) h
theorem steps_get {g g' : Term} (name : String) (h : Steps g g') : Steps (.get g name) (.get g' name) :=
  steps_congr (fun x => .get x name) (fun s => .target name s) h
theorem steps_extend {i i' : Term} (fs : List (String × Term)) (h : Steps i i') :
    Steps (.extend i fs) (.extend i' fs) :=
  steps_congr (fun x => .extend x fs) (fun s => .extendTarget fs s) h
theorem steps_binaryLeft {l l' : Term} (op : Primitive) (r : Term) (h : Steps l l') :
    Steps (.binary op l r) (.binary op l' r) :=
  steps_congr (fun x => .binary op x r) (fun s => .binaryLeft op r s) h
theorem steps_binaryRight {r r' : Term} (op : Primitive) {l : Term} (v : Value l) (h : Steps r r') :
    Steps (.binary op l r) (.binary op l r') :=
  steps_congr (fun x => .binary op l x) (fun s => .binaryRight op l v s) h
theorem steps_ifZero {v v' : Term} (z s : Term) (h : Steps v v') :
    Steps (.ifZero v z s) (.ifZero v' z s) :=
  steps_congr (fun x => .ifZero x z s) (fun st => .condition z s st) h
theorem steps_case {sc sc' : Term} (arms : List (String × Term)) (h : Steps sc sc') :
    Steps (.case sc arms) (.case sc' arms) :=
  steps_congr (fun x => .case x arms) (fun st => .caseTarget arms st) h
theorem steps_ifBool {c c' : Term} (x y : Term) (h : Steps c c') :
    Steps (.ifBool c x y) (.ifBool c' x y) :=
  steps_congr (fun z => .ifBool z x y) (fun st => .ifCondition x y st) h
theorem steps_reflect {p p' : Term} (h : Steps p p') : Steps (.reflect p) (.reflect p') :=
  steps_congr _ (fun s => .reflectStep s) h
theorem steps_metadata {p p' : Term} (h : Steps p p') : Steps (.metadata p) (.metadata p') :=
  steps_congr _ (fun s => .metadataStep s) h
theorem steps_project {p p' : Term} (h : Steps p p') : Steps (.project p) (.project p') :=
  steps_congr _ (fun s => .projectStep s) h

theorem steps_snoc {a b c : Term} (h : Steps a b) (s : Step b c) : Steps a c :=
  steps_trans h (steps_one s)

/-! ## Inversions: a term ahead of a value head, and a value head behind a term -/

section
variable {t t' : Term}

theorem inv_lam_ahead {p' : Term} (h : Ahead t (.lam p')) : ∃ p, Steps t (.lam p) ∧ Ahead p p' := by
  generalize e : Term.lam p' = u at h
  induction h
  case run s _ ih => obtain ⟨p, s2, a⟩ := ih e; exact ⟨p, steps_trans s s2, a⟩
  case lam a _ => cases e; exact ⟨_, .refl _, a⟩
  all_goals cases e

theorem inv_spec_ahead {m' e' : Term} (h : Ahead t (.specification m' e')) :
    ∃ m e, Steps t (.specification m e) ∧ Ahead m m' ∧ Ahead e e' := by
  generalize eq : Term.specification m' e' = u at h
  induction h
  case run s _ ih => obtain ⟨m, e, s2, a, b⟩ := ih eq; exact ⟨m, e, steps_trans s s2, a, b⟩
  case specification a b _ _ => cases eq; exact ⟨_, _, .refl _, a, b⟩
  all_goals cases eq

theorem inv_proto_ahead {s' g' : Term} (h : Ahead t (.prototype s' g')) :
    ∃ s g, Steps t (.prototype s g) ∧ Ahead s s' ∧ Ahead g g' := by
  generalize eq : Term.prototype s' g' = u at h
  induction h
  case run st _ ih => obtain ⟨m, e, s2, a, b⟩ := ih eq; exact ⟨m, e, steps_trans st s2, a, b⟩
  case prototype a b _ _ => cases eq; exact ⟨_, _, .refl _, a, b⟩
  all_goals cases eq

theorem inv_inject_ahead {l : String} {p' : Term} (h : Ahead t (.inject l p')) :
    ∃ p, Steps t (.inject l p) ∧ Ahead p p' := by
  generalize eq : Term.inject l p' = u at h
  induction h
  case run st _ ih => obtain ⟨p, s2, a⟩ := ih eq; exact ⟨p, steps_trans st s2, a⟩
  case inject a _ => cases eq; exact ⟨_, .refl _, a⟩
  all_goals cases eq

theorem inv_record_ahead {fs' : List (String × Term)} (h : Ahead t (.record fs')) :
    ∃ fs, Steps t (.record fs) ∧ fs.map Prod.fst = fs'.map Prod.fst ∧
      ∀ p ∈ fs.zip fs', Ahead p.1.2 p.2.2 := by
  generalize eq : Term.record fs' = u at h
  induction h
  case run st _ ih => obtain ⟨fs, s2, a, b⟩ := ih eq; exact ⟨fs, steps_trans st s2, a, b⟩
  case record names rel _ => cases eq; exact ⟨_, .refl _, names, rel⟩
  all_goals cases eq

/-- Literals: the scalar values every primitive consumes and every ground observation reads. -/
inductive Literal : Term → Prop where
  | nat (n : Nat) : Literal (.nat n)
  | boolean (b : Bool) : Literal (.boolean b)
  | label (l : String) : Literal (.label l)

theorem Literal.value {t : Term} : Literal t → Value t
  | .nat n => .natural n
  | .boolean b => .boolean b
  | .label l => .label l

theorem inv_literal_ahead {v : Term} (lit : Literal v) (h : Ahead t v) : Steps t v := by
  induction h
  case run st _ ih => exact steps_trans st (ih lit)
  case nat => exact .refl _
  case boolean => exact .refl _
  case label => exact .refl _
  all_goals cases lit

theorem primitiveResult_literal {op : Primitive} {l r res : Term}
    (h : primitiveResult op l r = some res) : Literal l ∧ Literal r ∧ Literal res := by
  cases op <;> cases l <;> cases r <;> simp_all [primitiveResult] <;> subst h <;>
    exact ⟨by constructor, by constructor, by constructor⟩

/-- A term ahead of a value reaches a value it is ahead of. -/
theorem inv_value_ahead {v' : Term} (value : Value v') (h : Ahead t v') :
    ∃ v, Steps t v ∧ Value v ∧ Ahead v v' := by
  cases value with
  | function p' => obtain ⟨p, s, a⟩ := inv_lam_ahead h; exact ⟨_, s, .function _, .lam a⟩
  | natural n => exact ⟨_, inv_literal_ahead (.nat n) h, .natural n, .refl _⟩
  | boolean b => exact ⟨_, inv_literal_ahead (.boolean b) h, .boolean b, .refl _⟩
  | label l => exact ⟨_, inv_literal_ahead (.label l) h, .label l, .refl _⟩
  | record fs' =>
    obtain ⟨fs, s, names, rel⟩ := inv_record_ahead h; exact ⟨_, s, .record _, .record names rel⟩
  | specification m e =>
    obtain ⟨_, _, s, a, b⟩ := inv_spec_ahead h; exact ⟨_, s, .specification _ _, .specification a b⟩
  | prototype s g =>
    obtain ⟨_, _, st, a, b⟩ := inv_proto_ahead h; exact ⟨_, st, .prototype _ _, .prototype a b⟩
  | inject l p =>
    obtain ⟨_, s, a⟩ := inv_inject_ahead h; exact ⟨_, s, .inject _ _, .inject l a⟩

theorem inv_lam_behind {p : Term} (h : Ahead (.lam p) t') : ∃ p', t' = .lam p' ∧ Ahead p p' := by
  generalize e : Term.lam p = u at h
  induction h
  case run s _ ih => subst e; exact ih (value_steps_eq (.function _) s).symm
  case lam a _ => cases e; exact ⟨_, rfl, a⟩
  all_goals cases e

theorem inv_spec_behind {m e : Term} (h : Ahead (.specification m e) t') :
    ∃ m' e', t' = .specification m' e' ∧ Ahead m m' ∧ Ahead e e' := by
  generalize eq : Term.specification m e = u at h
  induction h
  case run s _ ih => subst eq; exact ih (value_steps_eq (.specification _ _) s).symm
  case specification a b _ _ => cases eq; exact ⟨_, _, rfl, a, b⟩
  all_goals cases eq

theorem inv_proto_behind {s g : Term} (h : Ahead (.prototype s g) t') :
    ∃ s' g', t' = .prototype s' g' ∧ Ahead s s' ∧ Ahead g g' := by
  generalize eq : Term.prototype s g = u at h
  induction h
  case run st _ ih => subst eq; exact ih (value_steps_eq (.prototype _ _) st).symm
  case prototype a b _ _ => cases eq; exact ⟨_, _, rfl, a, b⟩
  all_goals cases eq

theorem inv_inject_behind {l : String} {p : Term} (h : Ahead (.inject l p) t') :
    ∃ p', t' = .inject l p' ∧ Ahead p p' := by
  generalize eq : Term.inject l p = u at h
  induction h
  case run st _ ih => subst eq; exact ih (value_steps_eq (.inject _ _) st).symm
  case inject a _ => cases eq; exact ⟨_, rfl, a⟩
  all_goals cases eq

theorem inv_record_behind {fs : List (String × Term)} (h : Ahead (.record fs) t') :
    ∃ fs', t' = .record fs' ∧ fs.map Prod.fst = fs'.map Prod.fst ∧
      ∀ p ∈ fs.zip fs', Ahead p.1.2 p.2.2 := by
  generalize eq : Term.record fs = u at h
  induction h
  case run st _ ih => subst eq; exact ih (value_steps_eq (.record _) st).symm
  case record names rel _ => cases eq; exact ⟨_, rfl, names, rel⟩
  all_goals cases eq

theorem inv_literal_behind {v : Term} (lit : Literal v) (h : Ahead v t') : t' = v := by
  induction h
  case run st _ ih => cases value_steps_eq lit.value st; exact ih lit
  case nat => rfl
  case boolean => rfl
  case label => rfl
  all_goals cases lit

/-- A value behind a term is matched by a value, with no reduction. -/
theorem inv_value_behind {v : Term} (value : Value v) (h : Ahead v t') : Value t' := by
  cases value with
  | function p => obtain ⟨_, rfl, _⟩ := inv_lam_behind h; exact .function _
  | natural n => rw [inv_literal_behind (.nat n) h]; exact .natural n
  | boolean b => rw [inv_literal_behind (.boolean b) h]; exact .boolean b
  | label l => rw [inv_literal_behind (.label l) h]; exact .label l
  | record fs => obtain ⟨_, rfl, _⟩ := inv_record_behind h; exact .record _
  | specification m e => obtain ⟨_, _, rfl, _⟩ := inv_spec_behind h; exact .specification _ _
  | prototype s g => obtain ⟨_, _, rfl, _⟩ := inv_proto_behind h; exact .prototype _ _
  | inject l p => obtain ⟨_, rfl, _⟩ := inv_inject_behind h; exact .inject _ _
end

/-! ## The two simulations -/

/-- A step of the term ahead is matched by reduction of the term behind. -/
theorem step_ahead {t t' : Term} (h : Ahead t t') :
    ∀ {u' : Term}, Step t' u' → ∃ u, Steps t u ∧ Ahead u u' := by
  induction h with
  | run s _ ih => intro u' st; obtain ⟨u, s2, a⟩ := ih st; exact ⟨u, steps_trans s s2, a⟩
  | hole => intro u' st; cases st
  | bound => intro u' st; cases st
  | lam => intro u' st; cases st
  | app hf ha ihf _ =>
    intro u' st
    cases st with
    | beta body arg =>
      obtain ⟨p, s, a⟩ := inv_lam_ahead hf
      exact ⟨_, steps_snoc (steps_app _ s) (.beta _ _), ahead_instantiate a ha⟩
    | application _ st' =>
      obtain ⟨g, s, a⟩ := ihf st'
      exact ⟨_, steps_app _ s, .app a ha⟩
    | applySpecification m e _ =>
      obtain ⟨_, _, s, _, ae⟩ := inv_spec_ahead hf
      exact ⟨_, steps_snoc (steps_app _ s) (.applySpecification _ _ _), .app ae ha⟩
  | mix hl hu _ _ =>
    intro u' st; cases st; exact ⟨_, steps_one (.mix _ _), ahead_mixBody hl hu⟩
  | fix hs hi _ _ =>
    intro u' st; cases st; exact ⟨_, steps_one (.fix _ _), .app (.app hs (.fix hs hi)) hi⟩
  | specification => intro u' st; cases st
  | prototype => intro u' st; cases st
  | reflect hp ih =>
    intro u' st
    cases st with
    | reflectPrototype =>
      obtain ⟨_, _, s, a, _⟩ := inv_proto_ahead hp
      exact ⟨_, steps_snoc (steps_reflect s) (.reflectPrototype _ _), a⟩
    | reflectStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_reflect s, .reflect a⟩
  | metadata hp ih =>
    intro u' st
    cases st with
    | metadataSpecification =>
      obtain ⟨_, _, s, a, _⟩ := inv_spec_ahead hp
      exact ⟨_, steps_snoc (steps_metadata s) (.metadataSpecification _ _), a⟩
    | metadataStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_metadata s, .metadata a⟩
  | project hp ih =>
    intro u' st
    cases st with
    | projectPrototype =>
      obtain ⟨_, _, s, _, b⟩ := inv_proto_ahead hp
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
      obtain ⟨_, sl, vl, al⟩ := inv_value_ahead v hl
      obtain ⟨_, sr, ar⟩ := ihr st'
      exact ⟨_, steps_trans (steps_binaryLeft _ _ sl) (steps_binaryRight _ vl sr), .binary _ al ar⟩
    | primitive _ _ _ _ vl vr hit =>
      obtain ⟨ll, lr, _⟩ := primitiveResult_literal hit
      exact ⟨_, steps_snoc (steps_trans (steps_binaryLeft _ _ (inv_literal_ahead ll hl))
        (steps_binaryRight _ vl (inv_literal_ahead lr hr))) (.primitive _ _ _ _ vl vr hit), .refl _⟩
  | extend hi names rel ihi _ =>
    intro u' st
    cases st with
    | extendTarget _ st' =>
      obtain ⟨_, s, a⟩ := ihi st'; exact ⟨_, steps_extend _ s, .extend a names rel⟩
    | extendRecord =>
      obtain ⟨_, s, n1, r1⟩ := inv_record_ahead hi
      obtain ⟨n2, r2⟩ := extendFields_rel n1 r1 names rel
      exact ⟨_, steps_snoc (steps_extend _ s) (.extendRecord _ _), .record n2 r2⟩
  | record => intro u' st; cases st
  | get name hg ih =>
    intro u' st
    cases st with
    | target _ st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_get _ s, .get _ a⟩
    | field _ _ _ hit =>
      obtain ⟨_, s, n1, r1⟩ := inv_record_ahead hg
      obtain ⟨_, hit0, a⟩ := find_right n1 r1 hit
      exact ⟨_, steps_snoc (steps_get _ s) (.field _ _ _ hit0), a⟩
  | ifZero hv hz hs ihv _ _ =>
    intro u' st
    cases st with
    | condition _ _ st' =>
      obtain ⟨_, s, a⟩ := ihv st'; exact ⟨_, steps_ifZero _ _ s, .ifZero a hz hs⟩
    | zero =>
      exact ⟨_, steps_snoc (steps_ifZero _ _ (inv_literal_ahead (.nat 0) hv)) (.zero _ _), hz⟩
    | successor n =>
      exact ⟨_, steps_snoc (steps_ifZero _ _ (inv_literal_ahead (.nat (n + 1)) hv))
        (.successor _ _ _), ahead_instantiate hs (.nat n)⟩
  | inject => intro u' st; cases st
  | case hsc names rel ihsc _ =>
    intro u' st
    cases st with
    | caseTarget _ st' =>
      obtain ⟨_, s, a⟩ := ihsc st'; exact ⟨_, steps_case _ s, .case a names rel⟩
    | caseInject _ _ _ _ hit =>
      obtain ⟨_, s, a⟩ := inv_inject_ahead hsc
      obtain ⟨_, hit0, ab⟩ := find_right names rel hit
      exact ⟨_, steps_snoc (steps_case _ s) (.caseInject _ _ _ _ hit0), ahead_instantiate ab a⟩
  | ifBool hc hx hy ihc _ _ =>
    intro u' st
    cases st with
    | ifCondition _ _ st' =>
      obtain ⟨_, s, a⟩ := ihc st'; exact ⟨_, steps_ifBool _ _ s, .ifBool a hx hy⟩
    | ifTrue =>
      exact ⟨_, steps_snoc (steps_ifBool _ _ (inv_literal_ahead (.boolean true) hc)) (.ifTrue _ _), hx⟩
    | ifFalse =>
      exact ⟨_, steps_snoc (steps_ifBool _ _ (inv_literal_ahead (.boolean false) hc)) (.ifFalse _ _), hy⟩
  | perform => intro u' st; cases st
  | done hv _ => intro u' st; cases st; exact ⟨_, steps_one (.done _), hv⟩

/-- A step of the term behind is matched by reduction of the term ahead. -/
theorem step_behind {t t' : Term} (h : Ahead t t') :
    ∀ {u : Term}, Step t u → ∃ u', Steps t' u' ∧ Ahead u u' := by
  induction h with
  | run s rest ih =>
    intro u st
    cases s with
    | refl => exact ih st
    | next st1 s1 => cases step_deterministic st st1; exact ⟨_, .refl _, .run s1 rest⟩
  | hole => intro u st; cases st
  | bound => intro u st; cases st
  | lam => intro u st; cases st
  | app hf ha ihf _ =>
    intro u st
    cases st with
    | beta =>
      obtain ⟨_, rfl, a⟩ := inv_lam_behind hf
      exact ⟨_, steps_one (.beta _ _), ahead_instantiate a ha⟩
    | application _ st' => obtain ⟨_, s, a⟩ := ihf st'; exact ⟨_, steps_app _ s, .app a ha⟩
    | applySpecification =>
      obtain ⟨_, _, rfl, _, ae⟩ := inv_spec_behind hf
      exact ⟨_, steps_one (.applySpecification _ _ _), .app ae ha⟩
  | mix hl hu _ _ =>
    intro u st; cases st; exact ⟨_, steps_one (.mix _ _), ahead_mixBody hl hu⟩
  | fix hs hi _ _ =>
    intro u st; cases st; exact ⟨_, steps_one (.fix _ _), .app (.app hs (.fix hs hi)) hi⟩
  | specification => intro u st; cases st
  | prototype => intro u st; cases st
  | reflect hp ih =>
    intro u st
    cases st with
    | reflectPrototype =>
      obtain ⟨_, _, rfl, a, _⟩ := inv_proto_behind hp
      exact ⟨_, steps_one (.reflectPrototype _ _), a⟩
    | reflectStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_reflect s, .reflect a⟩
  | metadata hp ih =>
    intro u st
    cases st with
    | metadataSpecification =>
      obtain ⟨_, _, rfl, a, _⟩ := inv_spec_behind hp
      exact ⟨_, steps_one (.metadataSpecification _ _), a⟩
    | metadataStep st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_metadata s, .metadata a⟩
  | project hp ih =>
    intro u st
    cases st with
    | projectPrototype =>
      obtain ⟨_, _, rfl, _, b⟩ := inv_proto_behind hp
      exact ⟨_, steps_one (.projectPrototype _ _), b⟩
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
      obtain ⟨_, s, a⟩ := ihr st'
      exact ⟨_, steps_binaryRight _ (inv_value_behind v hl) s, .binary _ hl a⟩
    | primitive _ _ _ _ vl vr hit =>
      obtain ⟨ll, lr, _⟩ := primitiveResult_literal hit
      obtain rfl := inv_literal_behind ll hl
      obtain rfl := inv_literal_behind lr hr
      exact ⟨_, steps_one (.primitive _ _ _ _ vl vr hit), .refl _⟩
  | extend hi names rel ihi _ =>
    intro u st
    cases st with
    | extendTarget _ st' =>
      obtain ⟨_, s, a⟩ := ihi st'; exact ⟨_, steps_extend _ s, .extend a names rel⟩
    | extendRecord =>
      obtain ⟨_, rfl, n1, r1⟩ := inv_record_behind hi
      obtain ⟨n2, r2⟩ := extendFields_rel n1 r1 names rel
      exact ⟨_, steps_one (.extendRecord _ _), .record n2 r2⟩
  | record => intro u st; cases st
  | get name hg ih =>
    intro u st
    cases st with
    | target _ st' => obtain ⟨_, s, a⟩ := ih st'; exact ⟨_, steps_get _ s, .get _ a⟩
    | field _ _ _ hit =>
      obtain ⟨_, rfl, n1, r1⟩ := inv_record_behind hg
      obtain ⟨_, hit', a⟩ := find_left n1 r1 hit
      exact ⟨_, steps_one (.field _ _ _ hit'), a⟩
  | ifZero hv hz hs ihv _ _ =>
    intro u st
    cases st with
    | condition _ _ st' =>
      obtain ⟨_, s, a⟩ := ihv st'; exact ⟨_, steps_ifZero _ _ s, .ifZero a hz hs⟩
    | zero =>
      obtain rfl := inv_literal_behind (.nat 0) hv
      exact ⟨_, steps_one (.zero _ _), hz⟩
    | successor n =>
      obtain rfl := inv_literal_behind (.nat (n + 1)) hv
      exact ⟨_, steps_one (.successor _ _ _), ahead_instantiate hs (.nat n)⟩
  | inject => intro u st; cases st
  | case hsc names rel ihsc _ =>
    intro u st
    cases st with
    | caseTarget _ st' =>
      obtain ⟨_, s, a⟩ := ihsc st'; exact ⟨_, steps_case _ s, .case a names rel⟩
    | caseInject _ _ _ _ hit =>
      obtain ⟨_, rfl, a⟩ := inv_inject_behind hsc
      obtain ⟨_, hit', ab⟩ := find_left names rel hit
      exact ⟨_, steps_one (.caseInject _ _ _ _ hit'), ahead_instantiate ab a⟩
  | ifBool hc hx hy ihc _ _ =>
    intro u st
    cases st with
    | ifCondition _ _ st' =>
      obtain ⟨_, s, a⟩ := ihc st'; exact ⟨_, steps_ifBool _ _ s, .ifBool a hx hy⟩
    | ifTrue =>
      obtain rfl := inv_literal_behind (.boolean true) hc
      exact ⟨_, steps_one (.ifTrue _ _), hx⟩
    | ifFalse =>
      obtain rfl := inv_literal_behind (.boolean false) hc
      exact ⟨_, steps_one (.ifFalse _ _), hy⟩
  | perform => intro u st; cases st
  | done hv _ => intro u st; cases st; exact ⟨_, steps_one (.done _), hv⟩

/-! ## Completed runs transfer both ways -/

theorem evaluates_behind {t t' v : Term} (h : Ahead t t') (e : Evaluates t v) :
    ∃ v', Evaluates t' v' ∧ Ahead v v' := by
  obtain ⟨s, val⟩ := e
  induction s generalizing t' with
  | refl => exact ⟨t', ⟨.refl _, inv_value_behind val h⟩, h⟩
  | next st _ ih =>
    obtain ⟨_, s1, a⟩ := step_behind h st
    obtain ⟨v', ⟨s2, val'⟩, a2⟩ := ih a val
    exact ⟨v', ⟨steps_trans s1 s2, val'⟩, a2⟩

theorem evaluates_ahead {t t' v' : Term} (h : Ahead t t') (e : Evaluates t' v') :
    ∃ v, Evaluates t v ∧ Ahead v v' := by
  obtain ⟨s, val⟩ := e
  induction s generalizing t with
  | refl =>
    obtain ⟨v, s, vv, a⟩ := inv_value_ahead val h
    exact ⟨v, ⟨s, vv⟩, a⟩
  | next st _ ih =>
    obtain ⟨_, s1, a⟩ := step_ahead h st
    obtain ⟨v, ⟨s2, vv⟩, a2⟩ := ih a val
    exact ⟨v, ⟨steps_trans s1 s2, vv⟩, a2⟩

end Obend.Equiv
end
