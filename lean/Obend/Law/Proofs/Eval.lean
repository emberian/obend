module
/-
# Obend.Law.Proofs.Eval — what a law's application evaluates through

The reference semantics is substitution-based call-by-name. A law `λ old. λ new. λ req. B` applied
to data steps, in three forced beta steps, to `B` under the substitution `lawEnv` that sends
`bound 0, 1, 2` to the request, the new state and the old state (`applyLaw_steps`); a `case` arm
entered with payload `p` runs under `scons p σ` (`instantiate_lift`). Neither needs the data to be
closed. The inversion lemmas (`ifBool_inv`, `case_inv`, `get_inv`, `binary_inv`) read an
evaluation of a compound term back to evaluations of its parts, and the `Data` lemmas read an
evaluation of a field selection back to the field.
-/
public import Obend.Law.Syntax
public import Obend.Law.Proofs.Run
public import Obend.Core.TermTraverse
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Data (Data fieldsTerm)
set_option autoImplicit false

/-! ## Substitutions -/

/-- `x` at index 0, `σ` above it. -/
@[expose] public def scons (x : Term) (σ : Nat → Term) : Nat → Term
  | 0 => x
  | k + 1 => σ k

/-- The substitution a law body runs under: request, new state, old state. -/
@[expose] public def lawEnv (o n rq : Term) : Nat → Term := scons rq (scons n (scons o .bound))

@[simp] public theorem scons_zero (x : Term) (σ : Nat → Term) : scons x σ 0 = x := rfl
@[simp] public theorem scons_succ (x : Term) (σ : Nat → Term) (k : Nat) : scons x σ (k + 1) = σ k := rfl

theorem substitute_bound_id (t : Term) : t.substitute .bound = t := by
  apply Obend.Core.TermTraverse.encode_injective
  rw [Obend.Core.TermTraverse.encode_substitute]
  have : (fun i => Obend.Core.TermTraverse.encode (Term.bound i)) = Obend.Core.Traverse.Tree.var := by
    funext i; simp [Obend.Core.TermTraverse.encode]
  rw [this]
  exact Obend.Core.Traverse.Tree.substitute_id _

theorem instantiate_eq (t x : Term) : instantiate t x = t.substitute (scons x .bound) := by
  unfold instantiate
  congr 1

/-- Entering a binder with payload `x`: the lifted substitution, then the payload, is `scons x σ`. -/
public theorem instantiate_lift (t x : Term) (σ : Nat → Term) :
    instantiate (t.substitute (liftSubstitution σ)) x = t.substitute (scons x σ) := by
  rw [instantiate_eq, Obend.Core.TermTraverse.substitute_comp]
  congr 1
  funext i
  cases i with
  | zero => simp [liftSubstitution, Term.substitute]
  | succ k =>
      simp only [liftSubstitution, scons_succ]
      rw [Obend.Core.TermTraverse.rename_substitute]
      exact substitute_bound_id _

/-- **A law's application steps to its body under `lawEnv`.** -/
public theorem applyLaw_steps (B : Term) (o n rq : Data) :
    Steps (applyLaw (law3 B) o n rq) (B.substitute (lawEnv o.term n.term rq.term)) := by
  unfold applyLaw law3
  refine .next (.application _ (.application _ (.beta _ _))) ?_
  rw [instantiate_eq]
  simp only [Term.substitute]
  refine .next (.application _ (.beta _ _)) ?_
  rw [instantiate_eq]
  simp only [Term.substitute]
  refine .next (.beta _ _) ?_
  rw [instantiate_lift, Obend.Core.TermTraverse.substitute_comp]
  have : (fun i => (liftSubstitution (liftSubstitution (scons o.term Term.bound)) i).substitute
      (scons rq.term (scons n.term Term.bound))) = lawEnv o.term n.term rq.term := by
    funext i
    rcases i with _ | _ | _ | k
    · simp [liftSubstitution, Term.substitute, lawEnv]
    · simp [liftSubstitution, Term.substitute, Term.rename, lawEnv]
    · simp only [liftSubstitution, scons_zero, lawEnv, scons_succ]
      rw [Obend.Core.TermTraverse.rename_substitute, Obend.Core.TermTraverse.rename_substitute]
      exact substitute_bound_id _
    · simp [liftSubstitution, Term.substitute, Term.rename, liftRename, lawEnv]
  rw [this]
  exact .refl _

/-- **What `Admits` is**: the body evaluates to `ok` under `lawEnv`. -/
public theorem admits_iff (B : Term) (o n rq : Data) :
    Admits (law3 B) o n rq ↔
      ∃ w, Evaluates (B.substitute (lawEnv o.term n.term rq.term)) (.inject "ok" w) := by
  constructor
  · rintro ⟨w, h⟩; exact ⟨w, evaluates_of_steps (applyLaw_steps B o n rq) h⟩
  · rintro ⟨w, h⟩; exact ⟨w, evaluates_steps (applyLaw_steps B o n rq) h⟩

public theorem refuses_iff (B : Term) (o n rq : Data) (why : String) :
    Refuses (law3 B) o n rq why ↔
      Evaluates (B.substitute (lawEnv o.term n.term rq.term)) (refusedT why) :=
  ⟨evaluates_of_steps (applyLaw_steps B o n rq), evaluates_steps (applyLaw_steps B o n rq)⟩

/-- A law that refuses does not admit. -/
public theorem refuses_not_admits {law : Term} {o n rq : Data} {why : String}
    (h : Refuses law o n rq why) : ¬ Admits law o n rq := by
  rintro ⟨w, hw⟩
  have := evaluates_unique h hw
  simp [refusedT] at this

/-! ## Inversion -/

public theorem ifBool_inv {c x y v : Term} (h : Evaluates (.ifBool c x y) v) :
    ∃ b, Evaluates c (.boolean b) ∧ Evaluates (if b then x else y) v := by
  obtain ⟨hs, hv⟩ := h
  generalize ht : Term.ifBool c x y = t at hs
  induction hs generalizing c with
  | refl => subst ht; cases hv
  | next s rest ih =>
      subst ht
      cases s with
      | ifCondition _ _ sc =>
          obtain ⟨b, hc, hr⟩ := ih hv rfl
          exact ⟨b, evaluates_step sc hc, hr⟩
      | ifTrue => exact ⟨true, evaluates_self (.boolean true), ⟨rest, hv⟩⟩
      | ifFalse => exact ⟨false, evaluates_self (.boolean false), ⟨rest, hv⟩⟩

public theorem case_inv {s v : Term} {arms : List (String × Term)} (h : Evaluates (.case s arms) v) :
    ∃ l p body, Evaluates s (.inject l p) ∧ arms.find? (fun arm => arm.1 == l) = some (l, body) ∧
      Evaluates (instantiate body p) v := by
  obtain ⟨hs, hv⟩ := h
  generalize ht : Term.case s arms = t at hs
  induction hs generalizing s with
  | refl => subst ht; cases hv
  | next st rest ih =>
      subst ht
      cases st with
      | caseTarget _ sc =>
          obtain ⟨l, p, body, h1, h2, h3⟩ := ih hv rfl
          exact ⟨l, p, body, evaluates_step sc h1, h2, h3⟩
      | caseInject l p _ body hf => exact ⟨l, p, body, evaluates_self (.inject _ _), hf, ⟨rest, hv⟩⟩

public theorem get_inv {t v : Term} {n : String} (h : Evaluates (.get t n) v) :
    ∃ fs body, Evaluates t (.record fs) ∧ fs.find? (fun field => field.1 == n) = some (n, body) ∧
      Evaluates body v := by
  obtain ⟨hs, hv⟩ := h
  generalize ht : Term.get t n = u at hs
  induction hs generalizing t with
  | refl => subst ht; cases hv
  | next st rest ih =>
      subst ht
      cases st with
      | target _ sc =>
          obtain ⟨fs, body, h1, h2, h3⟩ := ih hv rfl
          exact ⟨fs, body, evaluates_step sc h1, h2, h3⟩
      | field _ _ _ hf0 => exact ⟨_, _, evaluates_self (.record _), hf0, ⟨rest, hv⟩⟩

public theorem primitiveResult_value {p : Primitive} {a b r : Term} (h : primitiveResult p a b = some r) :
    Value r := by
  unfold primitiveResult at h
  split at h <;> (try cases h) <;> constructor

public theorem binary_inv {p : Primitive} {l r v : Term} (h : Evaluates (.binary p l r) v) :
    ∃ lv rv, Evaluates l lv ∧ Evaluates r rv ∧ primitiveResult p lv rv = some v := by
  obtain ⟨hs, hv⟩ := h
  generalize ht : Term.binary p l r = u at hs
  induction hs generalizing l r with
  | refl => subst ht; cases hv
  | next st rest ih =>
      subst ht
      cases st with
      | binaryLeft _ _ sl =>
          obtain ⟨lv, rv, h1, h2, h3⟩ := ih hv rfl
          exact ⟨lv, rv, evaluates_step sl h1, h2, h3⟩
      | binaryRight _ _ hl sr =>
          obtain ⟨lv, rv, h1, h2, h3⟩ := ih hv rfl
          exact ⟨lv, rv, h1, evaluates_step sr h2, h3⟩
      | primitive _ _ _ res hl hr hres =>
          have := evaluates_value (primitiveResult_value hres) ⟨rest, hv⟩
          subst this
          exact ⟨l, r, evaluates_self hl, evaluates_self hr, hres⟩

/-! ## Congruence: building evaluations -/

theorem steps_ifBool {c c' x y : Term} (h : Steps c c') : Steps (.ifBool c x y) (.ifBool c' x y) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.ifCondition _ _ s) ih

theorem steps_case {s s' : Term} {arms : List (String × Term)} (h : Steps s s') :
    Steps (.case s arms) (.case s' arms) := by
  induction h with
  | refl => exact .refl _
  | next st _ ih => exact .next (.caseTarget _ st) ih

public theorem evaluates_ifBool {c x y v : Term} {b : Bool} (hc : Evaluates c (.boolean b))
    (h : Evaluates (if b then x else y) v) : Evaluates (.ifBool c x y) v := by
  refine evaluates_steps (steps_ifBool hc.1) ?_
  cases b
  · exact evaluates_step (.ifFalse _ _) h
  · exact evaluates_step (.ifTrue _ _) h

public theorem evaluates_case {s v p body : Term} {l : String} {arms : List (String × Term)}
    (hs : Evaluates s (.inject l p)) (hf : arms.find? (fun arm => arm.1 == l) = some (l, body))
    (h : Evaluates (instantiate body p) v) : Evaluates (.case s arms) v :=
  evaluates_steps (steps_case hs.1) (evaluates_step (.caseInject _ _ _ _ hf) h)

/-! ## Data -/

public theorem data_value : (d : Data) → Value d.term
  | .natural _ => .natural _
  | .boolean _ => .boolean _
  | .label _ => .label _
  | .record _ => .record _
  | .variant _ _ => .inject _ _

public theorem evaluates_data {d : Data} {v : Term} (h : Evaluates d.term v) : v = d.term :=
  evaluates_value (data_value d) h

public theorem fieldsTerm_find (f : String) : (fs : List (String × Data)) →
    (fieldsTerm fs).find? (fun field => field.1 == f) = (fieldsLookup f fs).map (fun d => (f, d.term))
  | [] => by simp [fieldsTerm, fieldsLookup]
  | (g, d) :: rest => by
      simp only [fieldsTerm, fieldsLookup, List.find?_cons]
      by_cases h : g = f
      · subst h; simp
      · have : (g == f) = false := by simp [h]
        simp only [this]
        exact fieldsTerm_find f rest

/-- **A field selection on data means the field.** -/
public theorem get_data {d : Data} {f : String} {v : Term} (h : Evaluates (.get d.term f) v) :
    ∃ e, d.field f = some e ∧ v = e.term := by
  obtain ⟨fs, body, hr, hf, hb⟩ := get_inv h
  have hr' := evaluates_data hr
  cases d with
  | record dfs =>
      simp only [Data.term] at hr'
      cases hr'
      rw [fieldsTerm_find] at hf
      obtain ⟨e, he, heq⟩ := Option.map_eq_some_iff.1 hf
      cases heq
      exact ⟨e, he, evaluates_data hb⟩
  | _ => simp [Data.term] at hr'

public theorem data_term_nat {d : Data} {m : Nat} (h : d.term = .nat m) : d = .natural m := by
  cases d <;> simp_all [Data.term]

public theorem data_term_boolean {d : Data} {b : Bool} (h : d.term = .boolean b) : d = .boolean b := by
  cases d <;> simp_all [Data.term]

public theorem data_term_label {d : Data} {s : String} (h : d.term = .label s) : d = .label s := by
  cases d <;> simp_all [Data.term]

public theorem data_term_inject {d : Data} {l : String} {p : Term} (h : d.term = .inject l p) :
    ∃ x, d = .variant l x ∧ p = x.term := by
  cases d <;> simp_all [Data.term]

/-- A data field read and evaluated: it is that field. -/
theorem field_of_get {d : Data} {f : String} {v : Term} (h : Evaluates (.get d.term f) v) :
    ∃ e, d.field f = some e ∧ e.term = v := by
  obtain ⟨e, he, rfl⟩ := get_data h
  exact ⟨e, he, rfl⟩

/-! ## Runs as evidence -/

theorem okB_some {r : Option Term} (h : okB r = true) : ∃ w, r = some (.inject "ok" w) := by
  unfold okB at h; split at h <;> simp_all

theorem refusalOf_some {r : Option Term} {why : String} (h : refusalOf r = some why) :
    r = some (refusedT why) := by
  unfold refusalOf at h; split at h <;> simp_all [refusedT]

/-- A run that reaches `ok` is an admission. -/
public theorem admits_of_run {law : Term} {o n rq : Data} (fuel : Nat)
    (h : okB (run fuel (applyLaw law o n rq)) = true) : Admits law o n rq := by
  obtain ⟨w, hw⟩ := okB_some h
  exact ⟨w, run_sound fuel hw⟩

/-- A run that reaches a refusal is that refusal. -/
public theorem refuses_of_run {law : Term} {o n rq : Data} {why : String} (fuel : Nat)
    (h : refusalOf (run fuel (applyLaw law o n rq)) = some why) : Refuses law o n rq why :=
  run_sound fuel (refusalOf_some h)

end Obend.Law
