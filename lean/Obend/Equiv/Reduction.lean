module
/- Facts about Core4's reference reduction that the behavioural equivalence needs: renaming is a
substitution, the identity substitution is the identity, one β step commutes with substitution,
`Step` is closed under substitution, and `Step` is deterministic. -/
public import Obend.Core.Term
public import Obend.Core.TermTraverse
@[expose] public section
namespace Obend.Equiv
open Obend.Core.Term
open Obend.Core.Traverse
open Obend.Core.TermTraverse
set_option autoImplicit false

/-! ## Substitution algebra -/

theorem tree_rename_eq_substitute {Tag : Type} (t : Tree Tag) : ∀ f : Nat → Nat,
    Tree.rename f t = Tree.substitute (fun i => Tree.var (f i)) t := by
  induction t using Tree.inductionOn with
  | var i => intro f; simp only [Tree.rename, Tree.substitute, Tree.traverse]
  | bind body ih =>
    intro f
    have lifted : Tree.liftSubst (fun i => (Tree.var (f i) : Tree Tag)) =
        fun i => Tree.var (liftRename f i) := by
      funext i; cases i <;> simp [Tree.liftSubst, Tree.rename, Tree.traverse, liftRename]
    simp only [Tree.rename, Tree.substitute, Tree.traverse] at ih ⊢
    rw [lifted]; exact congrArg Tree.bind (ih (liftRename f))
  | node tag children ih =>
    intro f
    simp only [Tree.rename, Tree.substitute, Tree.traverse] at ih ⊢
    exact congrArg (Tree.node tag) (List.map_congr_left (fun c hc => ih c hc f))

theorem rename_eq_substitute (t : Term) (f : Nat → Nat) :
    t.rename f = t.substitute (fun i => .bound (f i)) := by
  apply encode_injective
  simp only [encode_rename, encode_substitute]
  rw [tree_rename_eq_substitute]
  congr 1; funext i; simp only [encode]

theorem substitute_bound (t : Term) : t.substitute Term.bound = t := by
  apply encode_injective
  simp only [encode_substitute]
  have : (fun i => encode (Term.bound i)) = Tree.var := by funext i; simp only [encode]
  rw [this]; exact Tree.substitute_id _

/-- The substitution `instantiate` performs. -/
def single (argument : Term) : Nat → Term
  | 0 => argument
  | n + 1 => .bound n

theorem instantiate_eq (body argument : Term) :
    instantiate body argument = body.substitute (single argument) := by
  unfold instantiate; congr 1

/-- One β step commutes with substitution. -/
theorem instantiate_substitute (body argument : Term) (σ : Nat → Term) :
    (instantiate body argument).substitute σ =
      instantiate (body.substitute (liftSubstitution σ)) (argument.substitute σ) := by
  simp only [instantiate_eq, substitute_comp]
  congr 1; funext i
  cases i with
  | zero => simp [single, liftSubstitution, Term.substitute]
  | succ n =>
    simp only [single, liftSubstitution, Term.substitute, rename_substitute]
    exact (substitute_bound _).symm

theorem rename_two_substitute (t : Term) (σ : Nat → Term) :
    (t.rename (fun n => n + 2)).substitute (liftSubstitution (liftSubstitution σ)) =
      (t.substitute σ).rename (fun n => n + 2) := by
  rw [rename_substitute, substitute_rename]
  congr 1; funext i
  simp only [liftSubstitution, rename_comp]

theorem mixBody_substitute (lower upper : Term) (σ : Nat → Term) :
    (mixBody lower upper).substitute σ = mixBody (lower.substitute σ) (upper.substitute σ) := by
  simp only [mixBody, Term.substitute, rename_two_substitute]
  simp [liftSubstitution, Term.rename]

/-! ## Values, primitives and records under substitution -/

theorem value_substitute {t : Term} (σ : Nat → Term) (h : Value t) : Value (t.substitute σ) := by
  cases h <;> simp only [Term.substitute] <;> constructor

theorem primitiveResult_substitute {p : Primitive} {l r res : Term} (σ : Nat → Term)
    (h : primitiveResult p l r = some res) :
    primitiveResult p (l.substitute σ) (r.substitute σ) = some (res.substitute σ) := by
  cases p <;> cases l <;> cases r <;> simp_all [primitiveResult, Term.substitute] <;>
    (subst h; simp [Term.substitute])

def mapFields (g : Term → Term) (fields : List (String × Term)) : List (String × Term) :=
  fields.map fun field => (field.1, g field.2)

theorem find_mapFields {fields : List (String × Term)} {name : String} {body : Term}
    (g : Term → Term) (h : fields.find? (fun field => field.1 == name) = some (name, body)) :
    (mapFields g fields).find? (fun field => field.1 == name) = some (name, g body) := by
  induction fields with
  | nil => simp at h
  | cons head rest ih =>
    obtain ⟨n, b⟩ := head
    by_cases hc : n = name
    · subst hc
      simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq] at h
      cases h; simp [mapFields]
    · have miss : (n == name) = false := by simpa using hc
      simp only [List.find?_cons, miss] at h
      simp only [mapFields, List.map_cons, List.find?_cons, miss]; exact ih h

theorem extendFields_map (g : Term → Term) (inherited fields : List (String × Term)) :
    extendFields (mapFields g inherited) (mapFields g fields) =
      mapFields g (extendFields inherited fields) := by
  simp only [extendFields, mapFields, List.map_append, List.filter_map, List.any_map]
  rfl

/-! ## `Step` is closed under substitution -/

theorem step_substitute {t u : Term} (σ : Nat → Term) (h : Step t u) :
    Step (t.substitute σ) (u.substitute σ) := by
  induction h generalizing σ with
  | beta body argument =>
    rw [instantiate_substitute]; simp only [Term.substitute]; exact .beta _ _
  | application argument _ ih => simp only [Term.substitute]; exact .application _ (ih σ)
  | mix lower upper => rw [mixBody_substitute]; simp only [Term.substitute]; exact .mix _ _
  | fix spec inherited => simp only [Term.substitute]; exact .fix _ _
  | applySpecification => simp only [Term.substitute]; exact .applySpecification _ _ _
  | reflectPrototype => simp only [Term.substitute]; exact .reflectPrototype _ _
  | metadataSpecification => simp only [Term.substitute]; exact .metadataSpecification _ _
  | projectPrototype => simp only [Term.substitute]; exact .projectPrototype _ _
  | reflectStep _ ih => simp only [Term.substitute]; exact .reflectStep (ih σ)
  | metadataStep _ ih => simp only [Term.substitute]; exact .metadataStep (ih σ)
  | projectStep _ ih => simp only [Term.substitute]; exact .projectStep (ih σ)
  | target name _ ih => simp only [Term.substitute]; exact .target _ (ih σ)
  | field fields name body hit =>
    simp only [Term.substitute]
    exact .field _ _ _ (find_mapFields (fun t => t.substitute σ) hit)
  | extendTarget fields _ ih => simp only [Term.substitute]; exact .extendTarget _ (ih σ)
  | extendRecord inherited fields =>
    simp only [Term.substitute]
    have := extendFields_map (fun t => t.substitute σ) inherited fields
    simp only [mapFields] at this
    rw [← this]; exact .extendRecord _ _
  | binaryLeft primitive right _ ih => simp only [Term.substitute]; exact .binaryLeft _ _ (ih σ)
  | binaryRight primitive left value _ ih =>
    simp only [Term.substitute]; exact .binaryRight _ _ (value_substitute σ value) (ih σ)
  | primitive primitive left right result lv rv hit =>
    simp only [Term.substitute]
    exact .primitive _ _ _ _ (value_substitute σ lv) (value_substitute σ rv)
      (primitiveResult_substitute σ hit)
  | condition zero successorBody _ ih => simp only [Term.substitute]; exact .condition _ _ (ih σ)
  | zero => simp only [Term.substitute]; exact .zero _ _
  | successor n zero successorBody =>
    simp only [Term.substitute]
    have := instantiate_substitute successorBody (.nat n) σ
    simp only [Term.substitute] at this
    rw [this]; exact .successor _ _ _
  | caseTarget arms _ ih => simp only [Term.substitute]; exact .caseTarget _ (ih σ)
  | caseInject label payload arms body hit =>
    simp only [Term.substitute]
    rw [instantiate_substitute]
    exact .caseInject _ _ _ _ (find_mapFields (fun t => t.substitute (liftSubstitution σ)) hit)
  | ifCondition whenTrue whenFalse _ ih => simp only [Term.substitute]; exact .ifCondition _ _ (ih σ)
  | ifTrue => simp only [Term.substitute]; exact .ifTrue _ _
  | ifFalse => simp only [Term.substitute]; exact .ifFalse _ _
  | done value => simp only [Term.substitute]; exact .done _

theorem steps_substitute {t u : Term} (σ : Nat → Term) (h : Steps t u) :
    Steps (t.substitute σ) (u.substitute σ) := by
  induction h with
  | refl => exact .refl _
  | next step _ ih => exact .next (step_substitute σ step) ih

/-! ## `Steps` composes and lifts through evaluation positions -/

theorem steps_trans {a b c : Term} (first : Steps a b) (second : Steps b c) : Steps a c := by
  induction first with
  | refl => exact second
  | next step _ ih => exact .next step (ih second)

theorem steps_one {a b : Term} (step : Step a b) : Steps a b := .next step (.refl _)

/-- Lift a reduction through an evaluation frame. -/
theorem steps_congr {a b : Term} (frame : Term → Term)
    (lift : ∀ {x y : Term}, Step x y → Step (frame x) (frame y)) (h : Steps a b) :
    Steps (frame a) (frame b) := by
  induction h with
  | refl => exact .refl _
  | next step _ ih => exact .next (lift step) ih

/-! ## Determinism -/

theorem value_no_step' {t u : Term} (value : Value t) (step : Step t u) : False := by
  cases value <;> cases step

set_option maxHeartbeats 600000 in
theorem step_deterministic {t u u' : Term} (left : Step t u) (right : Step t u') : u = u' := by
  induction left generalizing u' <;> cases right
  all_goals first
    | exact False.elim (value_no_step' (Value.function _) (by assumption))
    | exact False.elim (value_no_step' (Value.natural _) (by assumption))
    | exact False.elim (value_no_step' (Value.record _) (by assumption))
    | exact False.elim (value_no_step' (Value.specification _ _) (by assumption))
    | exact False.elim (value_no_step' (Value.prototype _ _) (by assumption))
    | exact False.elim (value_no_step' (Value.inject _ _) (by assumption))
    | exact False.elim (value_no_step' (Value.boolean _) (by assumption))
    | grind [value_no_step']

theorem value_steps_eq {v u : Term} (value : Value v) (h : Steps v u) : u = v := by
  cases h with
  | refl => rfl
  | next step _ => exact False.elim (value_no_step' value step)

end Obend.Equiv
end
