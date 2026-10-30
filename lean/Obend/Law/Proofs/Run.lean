module
/-
# Obend.Law.Proofs.Run — `step?` is the reference semantics' step, and `run` is sound

`step_iff`: `Step t t' ↔ step? t = some t'`, so `Step` is deterministic (`step_deterministic`) and
an evaluation is the run of `step?` (`run_sound`). `evaluates_of_steps`: an evaluation of `t`
passes through every term `t` steps to, which is how a meaning proof skips the forced steps of a
law's application.
-/
public import Obend.Law.Run
public import Obend.AxiomPin
namespace Obend.Law
open Obend.Core.Term
set_option autoImplicit false

public theorem isValueB_value {t : Term} (h : isValueB t = true) : Value t := by
  cases t <;> simp [isValueB] at h <;> constructor

public theorem value_isValueB {t : Term} (h : Value t) : isValueB t = true := by
  cases h <;> rfl

public theorem value_no_step {t t' : Term} (h : Value t) (s : Step t t') : False := by
  cases h <;> cases s

public theorem value_step?_none {t : Term} (h : Value t) : step? t = none := by
  cases h <;> simp [step?]

theorem find?_pair {α : Type} {l : List (String × α)} {n : String} {p : String × α}
    (h : l.find? (fun field => field.1 == n) = some p) : p = (n, p.2) := by
  have := List.find?_some h
  simp at this
  cases p; simp_all

public theorem step?_sound : (t : Term) → ∀ {t' : Term}, step? t = some t' → Step t t'
  | .app f a, t', h => by
      have ih := @step?_sound f
      simp only [step?] at h
      split at h
      · cases h; exact .beta _ _
      · cases h; exact .applySpecification _ _ _
      · obtain ⟨f', hf, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .application _ (ih hf)
  | .mix l u, t', h => by simp only [step?] at h; cases h; exact .mix _ _
  | .fix s i, t', h => by simp only [step?] at h; cases h; exact .fix _ _
  | .reflect t, t', h => by
      have ih := @step?_sound t
      simp only [step?] at h
      split at h
      · cases h; exact .reflectPrototype _ _
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .reflectStep (ih hx)
  | .metadata t, t', h => by
      have ih := @step?_sound t
      simp only [step?] at h
      split at h
      · cases h; exact .metadataSpecification _ _
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .metadataStep (ih hx)
  | .project t, t', h => by
      have ih := @step?_sound t
      simp only [step?] at h
      split at h
      · cases h; exact .projectPrototype _ _
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .projectStep (ih hx)
  | .get t n, t', h => by
      have ih := @step?_sound t
      simp only [step?] at h
      split at h
      · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
        have hp' := find?_pair hp
        rw [hp'] at hp
        exact .field _ _ _ hp
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .target _ (ih hx)
  | .extend t fs, t', h => by
      have ih := @step?_sound t
      simp only [step?] at h
      split at h
      · cases h; exact .extendRecord _ _
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .extendTarget _ (ih hx)
  | .binary p l r, t', h => by
      have ihl := @step?_sound l
      have ihr := @step?_sound r
      simp only [step?] at h
      split at h
      · cases h; exact .binaryLeft _ _ (ihl (by assumption))
      · split at h
        · split at h
          · cases h; exact .binaryRight _ _ (isValueB_value (by assumption)) (ihr (by assumption))
          · split at h
            · exact .primitive _ _ _ _ (isValueB_value (by assumption)) (isValueB_value (by assumption)) h
            · cases h
        · cases h
  | .ifZero v z s, t', h => by
      have ih := @step?_sound v
      simp only [step?] at h
      split at h
      · cases h; exact .zero _ _
      · cases h; exact .successor _ _ _
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .condition _ _ (ih hx)
  | .case t arms, t', h => by
      have ih := @step?_sound t
      simp only [step?] at h
      split at h
      · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
        have hp' := find?_pair hp
        rw [hp'] at hp
        exact .caseInject _ _ _ _ hp
      · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .caseTarget _ (ih hx)
  | .ifBool c x y, t', h => by
      have ih := @step?_sound c
      simp only [step?] at h
      split at h
      · cases h; exact .ifTrue _ _
      · cases h; exact .ifFalse _ _
      · obtain ⟨c', hc, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .ifCondition _ _ (ih hc)
  | .done v, t', h => by simp only [step?] at h; cases h; exact .done _
  | .bound _, _, h | .lam _, _, h | .nat _, _, h | .boolean _, _, h | .label _, _, h
  | .record _, _, h | .specification _ _, _, h | .prototype _ _, _, h | .inject _ _, _, h
  | .perform _, _, h => by simp [step?] at h

theorem step?_app_cong {f f' a : Term} (h : step? f = some f') : step? (.app f a) = some (.app f' a) := by
  simp only [step?]; split <;> simp_all [step?]

theorem step?_reflect_cong {t t' : Term} (h : step? t = some t') : step? (.reflect t) = some (.reflect t') := by
  simp only [step?]; split <;> simp_all [step?]

theorem step?_metadata_cong {t t' : Term} (h : step? t = some t') : step? (.metadata t) = some (.metadata t') := by
  simp only [step?]; split <;> simp_all [step?]

theorem step?_project_cong {t t' : Term} (h : step? t = some t') : step? (.project t) = some (.project t') := by
  simp only [step?]; split <;> simp_all [step?]

theorem step?_get_cong {t t' : Term} {n : String} (h : step? t = some t') : step? (.get t n) = some (.get t' n) := by
  simp only [step?]; split <;> simp_all [step?]

theorem step?_extend_cong {t t' : Term} {fs : List (String × Term)} (h : step? t = some t') :
    step? (.extend t fs) = some (.extend t' fs) := by
  simp only [step?]; split <;> simp_all [step?]

theorem step?_ifZero_cong {t t' z s : Term} (h : step? t = some t') :
    step? (.ifZero t z s) = some (.ifZero t' z s) := by
  simp only [step?]; split <;> simp_all [step?]

theorem step?_case_cong {t t' : Term} {arms : List (String × Term)} (h : step? t = some t') :
    step? (.case t arms) = some (.case t' arms) := by
  simp only [step?]; split <;> simp_all [step?]

theorem step?_ifBool_cong {t t' x y : Term} (h : step? t = some t') :
    step? (.ifBool t x y) = some (.ifBool t' x y) := by
  simp only [step?]; split <;> simp_all [step?]

public theorem step?_complete {t t' : Term} (s : Step t t') : step? t = some t' := by
  induction s with
  | beta => simp [step?]
  | application a hs ih => exact step?_app_cong ih
  | mix => simp [step?]
  | fix => simp [step?]
  | applySpecification => simp [step?]
  | reflectPrototype => simp [step?]
  | metadataSpecification => simp [step?]
  | projectPrototype => simp [step?]
  | reflectStep hs ih => exact step?_reflect_cong ih
  | metadataStep hs ih => exact step?_metadata_cong ih
  | projectStep hs ih => exact step?_project_cong ih
  | target n hs ih => exact step?_get_cong ih
  | field fs n body hf => simp [step?, hf]
  | extendTarget fs hs ih => exact step?_extend_cong ih
  | extendRecord => simp [step?]
  | binaryLeft p r hs ih => simp only [step?, ih]
  | binaryRight p l hv hs ih =>
      simp only [step?, ih, value_step?_none hv, value_isValueB hv, if_true]
  | primitive p l r res hl hr hres =>
      simp only [step?, value_step?_none hl, value_isValueB hl, value_step?_none hr, value_isValueB hr, hres,
        if_true]
  | condition z s hs ih => exact step?_ifZero_cong ih
  | zero => simp [step?]
  | successor => simp [step?]
  | caseTarget arms hs ih => exact step?_case_cong ih
  | caseInject l p arms body hf => simp [step?, hf]
  | ifCondition x y hs ih => exact step?_ifBool_cong ih
  | ifTrue => simp [step?]
  | ifFalse => simp [step?]
  | done => simp [step?]

/-- **`step?` is the step.** -/
public theorem step_iff {t t' : Term} : Step t t' ↔ step? t = some t' :=
  ⟨step?_complete, step?_sound t⟩

public theorem step_deterministic {t a b : Term} (sa : Step t a) (sb : Step t b) : a = b := by
  have := (step?_complete sa).symm.trans (step?_complete sb)
  exact Option.some.inj this

public theorem steps_trans {a b c : Term} (first : Steps a b) (second : Steps b c) : Steps a c := by
  induction first with
  | refl => exact second
  | next s _ ih => exact .next s (ih second)

/-- A value evaluates to itself, and only to itself. -/
public theorem evaluates_value {t v : Term} (hv : Value t) (h : Evaluates t v) : v = t := by
  cases h.1 with
  | refl => rfl
  | next s _ => exact (value_no_step hv s).elim

public theorem evaluates_self {t : Term} (hv : Value t) : Evaluates t t := ⟨.refl _, hv⟩

/-- An evaluation of `t` passes through every term `t` steps to. -/
public theorem evaluates_of_steps {t t' v : Term} (s : Steps t t') (h : Evaluates t v) :
    Evaluates t' v := by
  induction s with
  | refl => exact h
  | next first _ ih =>
      obtain ⟨hs, hv⟩ := h
      cases hs with
      | refl => exact (value_no_step hv first).elim
      | next second rest =>
          apply ih
          rw [step_deterministic first second]
          exact ⟨rest, hv⟩

public theorem evaluates_unique {t a b : Term} (ha : Evaluates t a) (hb : Evaluates t b) : a = b := by
  have := evaluates_of_steps ha.1 hb
  exact (evaluates_value ha.2 this).symm

/-- Steps first, then evaluate. -/
public theorem evaluates_step {t t' v : Term} (s : Step t t') (h : Evaluates t' v) : Evaluates t v :=
  ⟨.next s h.1, h.2⟩

public theorem evaluates_steps {t t' v : Term} (s : Steps t t') (h : Evaluates t' v) : Evaluates t v :=
  ⟨steps_trans s h.1, h.2⟩

/-- **The run is sound**: what `run` reaches, the term evaluates to. -/
public theorem run_sound : (fuel : Nat) → {t v : Term} → run fuel t = some v → Evaluates t v
  | 0, t, v, h => by
      simp only [run] at h
      split at h
      · cases h; exact evaluates_self (isValueB_value (by assumption))
      · cases h
  | fuel + 1, t, v, h => by
      simp only [run] at h
      split at h
      · cases h; exact evaluates_self (isValueB_value (by assumption))
      · split at h
        · exact evaluates_step (step?_sound _ (by assumption)) (run_sound fuel h)
        · cases h

#assert_axioms isValueB_value value_isValueB value_no_step value_step?_none step?_sound
  step?_complete step_iff step_deterministic steps_trans evaluates_value evaluates_self
  evaluates_of_steps evaluates_unique evaluates_step evaluates_steps run_sound

end Obend.Law
