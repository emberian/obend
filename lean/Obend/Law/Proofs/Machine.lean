module
/-
# Obend.Law.Proofs.Machine — the machine judges what the relation says

A kernel judges a law by executing its probe (`Obend.Law.Machine`). These theorems connect that
run to `Admits`/`Refuses`, which are stated over the reference semantics `Evaluates`:

* `judge_sound`: under ANY policy, limits and budget, a verdict the machine returns is the
  relation's verdict (`Judged`): `ok` means `Admits`, `refused why` means the law refused with a
  reason that evaluates to `why`.
* `judge_complete`: the relation's verdict is returned by the unrestricted `judge` at every limits,
  ticks, nodes and bytes past a threshold ("enough ticks").
* `judged_unique`: the relation gives at most one verdict, so the two together say the machine
  returns exactly the verdict `Evaluates` gives (`machine_judges`).
* `judgeEffective_sound` / `judgeEffective_names` / `judgeEffective_complete`: the same for an
  effective law, whose refusal names the ancestor: when the machine reports `refusedBy name why`,
  `name` is the first law on the precedence list that refused, with reason `why`, and every law
  before it admitted.

The bridge is `Obend.Core.Proofs.GroundExecution` (ground execution is sound and complete); the
probe turns the verdict, a sum, into a ground observation.
-/
public import Obend.Law.Machine
public import Obend.Law.Proofs.Inherit
public import Obend.Core.Proofs.GroundExecution
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data Budget Execution ExecutionWith execute executeWith fieldsTerm)
open Obend.Core.Machine (State Limits)
open Obend.Core.Invariant (Scoped)
open Obend.Core.Proofs.GroundExecution
open Obend.Core.Proofs.Adequacy (observationTerm)
set_option autoImplicit false

/-! ## Closedness -/

public theorem closedB_scoped {t : Term} (h : closedB t = true) : Scoped 0 t :=
  (Obend.Core.Invariant.scoped_encode_iff 0 t).mpr (scopedB_sound h)

mutual
public theorem data_scoped : (d : Data) → Scoped 0 d.term
  | .natural _ => .natural _
  | .boolean _ => .boolean _
  | .label _ => .label _
  | .record fs => by simp only [Data.term]; exact .record (fields_scoped fs)
  | .variant _ p => by simp only [Data.term]; exact .inject (data_scoped p)
public theorem fields_scoped : (fs : List (String × Data)) → ∀ f ∈ fieldsTerm fs, Scoped 0 f.2
  | [], f, h => by simp [fieldsTerm] at h
  | (n, v) :: rest, f, h => by
      simp only [fieldsTerm, List.mem_cons] at h
      rcases h with rfl | h
      · exact data_scoped v
      · exact fields_scoped rest f h
end

public theorem applyLaw_scoped {law : Term} (h : Scoped 0 law) (o n rq : Data) :
    Scoped 0 (applyLaw law o n rq) :=
  .app (.app (.app h (data_scoped o)) (data_scoped n)) (data_scoped rq)

theorem scoped_of_closed {t : Term} (h : Scoped 0 t) (m : Nat) : Scoped m t := by
  have := Obend.Core.Invariant.scoped_rename h id m (fun i hi => absurd hi (Nat.not_lt_zero _))
  rwa [Obend.Core.Invariant.scoped_rename_identity h id (fun _ _ => rfl)] at this

theorem chainAt_scoped : ∀ (lin : List (String × Term)) (d : Nat), (∀ p ∈ lin, closedB p.2 = true) →
    Scoped (d + 3) (chainAt ⟨d⟩ lin)
  | [], d, _ => .inject (.record (by simp))
  | (name, L) :: rest, d, hc => by
      have hL := scoped_of_closed (closedB_scoped (hc _ (List.mem_cons_self ..))) (d + 3)
      simp only [chainAt, At.old, At.new, At.req, At.under]
      refine .case (.app (.app (.app hL (.bound (by omega))) (.bound (by omega))) (.bound (by omega))) ?_
      intro arm harm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at harm
      rcases harm with rfl | rfl
      · exact chainAt_scoped rest (d + 1) (fun p hp => hc p (List.mem_cons_of_mem _ hp))
      · refine .inject (.record ?_)
        intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · exact .label _
        · exact .bound (by omega)

/-- The effective law of closed laws is closed. -/
public theorem effective_scoped {lin : List (String × Term)} (hc : ∀ p ∈ lin, closedB p.2 = true) :
    Scoped 0 (effective lin) :=
  .lam (.lam (.lam (chainAt_scoped lin 0 hc)))

theorem asLabel_scoped {k : Nat} {t : Term} (h : Scoped k t) : Scoped k (asLabel t) :=
  .ifBool (.binary h h) h h

theorem readVerdict_scoped {read v : Term} (hr : Scoped 1 read) (hv : Scoped 0 v) :
    Scoped 0 (readVerdict read v) := by
  refine .case hv ?_
  intro arm harm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at harm
  rcases harm with rfl | rfl
  · exact .boolean _
  · exact asLabel_scoped hr

public theorem verdictProbe_scoped {law : Term} (h : Scoped 0 law) (o n rq : Data) :
    Scoped 0 (verdictProbe law o n rq) :=
  readVerdict_scoped (.bound (by decide)) (applyLaw_scoped h o n rq)

public theorem blameProbe_scoped {law : Term} (h : Scoped 0 law) (field : String) (o n rq : Data) :
    Scoped 0 (blameProbe field law o n rq) :=
  readVerdict_scoped (.get (.bound (by decide))) (applyLaw_scoped h o n rq)

/-! ## The probe under the reference semantics -/

theorem steps_binaryLeft {p : Primitive} {l l' r : Term} (h : Steps l l') :
    Steps (.binary p l r) (.binary p l' r) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryLeft _ _ s) ih

theorem steps_binaryRight {p : Primitive} {l r r' : Term} (hl : Value l) (h : Steps r r') :
    Steps (.binary p l r) (.binary p l r') := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (.binaryRight _ _ hl s) ih

theorem labelEqual_inv {l r v : Term} (h : primitiveResult .labelEqual l r = some v) :
    ∃ a b, l = .label a ∧ r = .label b := by
  unfold primitiveResult at h
  split at h <;> simp_all

/-- **`asLabel x` observes exactly the label `x` evaluates to.** -/
public theorem asLabel_eval {x r : Term} : Evaluates (asLabel x) r ↔ ∃ s, r = .label s ∧ Evaluates x (.label s) := by
  constructor
  · intro h
    obtain ⟨b, hc, hb⟩ := ifBool_inv h
    obtain ⟨lv, rv, hl, _, hp⟩ := binary_inv hc
    have hx : Evaluates x r := by cases b <;> simpa using hb
    have := evaluates_unique hl hx
    subst this
    obtain ⟨a, _, rfl, _⟩ := labelEqual_inv hp
    exact ⟨a, rfl, hl⟩
  · rintro ⟨s, rfl, hx⟩
    have hb : Evaluates (.binary .labelEqual x x) (.boolean true) := by
      refine ⟨steps_trans (steps_binaryLeft hx.1) (steps_trans (steps_binaryRight (.label s) hx.1)
        (.next (.primitive _ _ _ _ (.label s) (.label s) (by simp [primitiveResult])) (.refl _))), .boolean _⟩
    exact evaluates_ifBool hb (by simpa using hx)

@[simp] theorem inst_asLabel (t p : Term) : instantiate (asLabel t) p = asLabel (instantiate t p) := by
  simp [asLabel, instantiate]

@[simp] theorem inst_bound0 (p : Term) : instantiate (.bound 0) p = p := by
  simp [instantiate]

@[simp] theorem inst_get0 (f : String) (p : Term) : instantiate (.get (.bound 0) f) p = .get p f := by
  simp [instantiate]

theorem readArms_find {l : String} {body : Term} {read : Term}
    (h : ([("ok", Term.boolean true), ("refused", asLabel read)] : List (String × Term)).find?
      (fun arm => arm.1 == l) = some (l, body)) :
    (l = "ok" ∧ body = .boolean true) ∨ (l = "refused" ∧ body = asLabel read) := by
  have hm := List.mem_of_find?_eq_some h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- The reader observes `true` exactly when the verdict is `ok`. -/
public theorem readVerdict_true {read v : Term} :
    Evaluates (readVerdict read v) (.boolean true) ↔ ∃ w, Evaluates v (.inject "ok" w) := by
  constructor
  · intro h
    obtain ⟨l, p, body, hv, hf, hb⟩ := case_inv h
    rcases readArms_find hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨p, hv⟩
    · rw [inst_asLabel] at hb
      obtain ⟨s, hs, _⟩ := asLabel_eval.1 hb
      cases hs
  · rintro ⟨w, hw⟩
    exact evaluates_case (body := .boolean true) hw (by simp) (by simpa [instantiate, Term.substitute] using evaluates_self (.boolean true))

/-- The reader observes the label `s` exactly when the verdict is a refusal whose payload, read,
evaluates to `s`. -/
public theorem readVerdict_label {read v : Term} {s : String} :
    Evaluates (readVerdict read v) (.label s) ↔
      ∃ p, Evaluates v (.inject "refused" p) ∧ Evaluates (instantiate read p) (.label s) := by
  constructor
  · intro h
    obtain ⟨l, p, body, hv, hf, hb⟩ := case_inv h
    rcases readArms_find hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := evaluates_value (.boolean true) (by simpa [instantiate, Term.substitute] using hb)
      cases this
    · rw [inst_asLabel] at hb
      obtain ⟨s', hs, hx⟩ := asLabel_eval.1 hb
      cases hs
      exact ⟨p, hv, hx⟩
  · rintro ⟨p, hv, hp⟩
    refine evaluates_case (body := asLabel read) hv (by simp) ?_
    rw [inst_asLabel]
    exact asLabel_eval.2 ⟨s, rfl, hp⟩

/-- A verdict's ground observation. -/
@[expose] public def Verdict.obs : Verdict → Observation
  | .ok => .boolean true
  | .refused why => .label why

public theorem Verdict.obs_data (v : Verdict) : observationData v.obs = v.data := by
  cases v <;> rfl

public theorem Verdict.ofData_obs (v : Verdict) : Verdict.ofData (observationData v.obs) = some v := by
  cases v <;> rfl

public theorem Verdict.ofData_some {d : Data} {v : Verdict} (h : Verdict.ofData d = some v) :
    d = observationData v.obs := by
  unfold Verdict.ofData at h
  split at h <;> cases h <;> rfl

/-- **The probe evaluates to a verdict's observation exactly when the relation gives that verdict.** -/
public theorem verdictProbe_iff (law : Term) (o n rq : Data) (v : Verdict) :
    Evaluates (verdictProbe law o n rq) (observationTerm v.obs) ↔ Judged law o n rq v := by
  cases v with
  | ok => exact readVerdict_true
  | refused why =>
      refine readVerdict_label.trans ?_
      simp only [inst_bound0]
      exact Iff.rfl

/-- `Refuses` (a literal reason) is a case of `RefusesAs`. -/
public theorem refuses_refusesAs {law : Term} {o n rq : Data} {why : String}
    (h : Refuses law o n rq why) : RefusesAs law o n rq why :=
  ⟨.label why, h, evaluates_self (.label why)⟩

/-- A refusal (lazy reason or not) is not an admission. -/
public theorem refusesAs_not_admits {law : Term} {o n rq : Data} {why : String}
    (h : RefusesAs law o n rq why) : ¬ Admits law o n rq := by
  rintro ⟨w, hw⟩
  obtain ⟨p, hp, _⟩ := h
  have := evaluates_unique hp hw
  simp at this

/-- **The relation gives at most one verdict.** -/
public theorem judged_unique {law : Term} {o n rq : Data} {v v' : Verdict}
    (h : Judged law o n rq v) (h' : Judged law o n rq v') : v = v' := by
  have e := evaluates_unique ((verdictProbe_iff law o n rq v).2 h) ((verdictProbe_iff law o n rq v').2 h')
  cases v <;> cases v' <;> simp [Verdict.obs, observationTerm] at e <;> simp [e]

/-! ## The machine -/

theorem runProbe_some {policy : State → Bool} {limits : Limits} {budget : Budget} {t : Term} {d : Data}
    (h : runProbe policy limits budget t = some d) :
    ∃ e : ExecutionWith policy limits budget t, e.extraction.result.value = d := by
  unfold runProbe at h
  split at h
  · rename_i e _; cases h; exact ⟨e, rfl⟩
  · cases h

/-- What a probe's run returns, when it returns, is a ground observation it evaluates to. -/
theorem runProbe_sound {policy : State → Bool} {limits : Limits} {budget : Budget} {t : Term}
    (closed : Scoped 0 t) {v : Verdict} (h : (runProbe policy limits budget t).bind Verdict.ofData = some v) :
    Evaluates t (observationTerm v.obs) := by
  cases hr : runProbe policy limits budget t with
  | none => rw [hr] at h; cases h
  | some d =>
      rw [hr] at h
      obtain ⟨e, he⟩ := runProbe_some hr
      have hd := Verdict.ofData_some h
      exact (execution_ground_iff closed e v.obs).1 (he.trans hd)

/-- With enough resources the unrestricted run of a probe returns the verdict it evaluates to. -/
theorem runProbe_complete {t : Term} (closed : Scoped 0 t) {v : Verdict}
    (h : Evaluates t (observationTerm v.obs)) :
    ∃ (limits₀ : Limits) (ticks₀ : Nat), ∀ (limits : Limits) (budget : Budget),
      Covers limits limits₀ → ticks₀ ≤ budget.ticks → 1 ≤ budget.nodes → groundBytes v.obs ≤ budget.bytes →
      (runProbe (fun _ => true) limits budget t).bind Verdict.ofData = some v := by
  obtain ⟨L₀, t₀, hc⟩ := execute_ground_complete closed h
  refine ⟨L₀, t₀, fun limits budget cover ticks nodes bytes => ?_⟩
  obtain ⟨e, he, hv⟩ := hc limits budget cover ticks nodes bytes
  have : runProbe (fun _ => true) limits budget t = some (observationData v.obs) := by
    unfold runProbe
    have he' : executeWith (fun _ => true) limits budget t = .ok e := he
    rw [he']
    simp only [hv]
  rw [this]
  exact Verdict.ofData_obs v

/-- **Soundness: the machine's verdict is the relation's**, under every policy, limits and budget. -/
public theorem judge_sound {law : Term} (closed : closedB law = true) {policy : State → Bool}
    {limits : Limits} {budget : Budget} {o n rq : Data} {v : Verdict}
    (h : judge policy limits budget law o n rq = some v) : Judged law o n rq v :=
  (verdictProbe_iff law o n rq v).1 (runProbe_sound (verdictProbe_scoped (closedB_scoped closed) o n rq) h)

/-- **Completeness: with enough ticks the machine returns the relation's verdict.** -/
public theorem judge_complete {law : Term} (closed : closedB law = true) {o n rq : Data} {v : Verdict}
    (h : Judged law o n rq v) :
    ∃ (limits₀ : Limits) (ticks₀ : Nat), ∀ (limits : Limits) (budget : Budget),
      Covers limits limits₀ → ticks₀ ≤ budget.ticks → 1 ≤ budget.nodes → groundBytes v.obs ≤ budget.bytes →
      judge (fun _ => true) limits budget law o n rq = some v :=
  runProbe_complete (verdictProbe_scoped (closedB_scoped closed) o n rq) ((verdictProbe_iff law o n rq v).2 h)

/-- **The machine judges what the relation says.** For a closed law: every verdict the machine
returns (any policy, any resources) is the relation's, the relation gives at most one, and with
enough resources the unrestricted machine returns it. -/
public theorem machine_judges {law : Term} (closed : closedB law = true) (o n rq : Data) :
    (∀ (policy : State → Bool) (limits : Limits) (budget : Budget) (v : Verdict),
      judge policy limits budget law o n rq = some v → Judged law o n rq v) ∧
    (∀ v v', Judged law o n rq v → Judged law o n rq v' → v = v') ∧
    (∀ v, Judged law o n rq v → ∃ (limits₀ : Limits) (ticks₀ : Nat), ∀ (limits : Limits) (budget : Budget),
      Covers limits limits₀ → ticks₀ ≤ budget.ticks → 1 ≤ budget.nodes → groundBytes v.obs ≤ budget.bytes →
      judge (fun _ => true) limits budget law o n rq = some v) :=
  ⟨fun _ _ _ _ h => judge_sound closed h, fun _ _ h h' => judged_unique h h', fun _ h => judge_complete closed h⟩

/-- A machine `ok` is an admission; a machine refusal is not. -/
public theorem admits_of_judge {law : Term} (closed : closedB law = true) {policy : State → Bool}
    {limits : Limits} {budget : Budget} {o n rq : Data}
    (h : judge policy limits budget law o n rq = some .ok) : Admits law o n rq :=
  judge_sound closed h

public theorem not_admits_of_judge {law : Term} (closed : closedB law = true) {policy : State → Bool}
    {limits : Limits} {budget : Budget} {o n rq : Data} {why : String}
    (h : judge policy limits budget law o n rq = some (.refused why)) : ¬ Admits law o n rq :=
  refusesAs_not_admits (judge_sound closed h)

/-! ## Effective laws: the machine names the ancestor -/

theorem get_record_eval {fs : List (String × Term)} {f : String} {body v : Term}
    (hf : fs.find? (fun field => field.1 == f) = some (f, body)) (h : Evaluates body v) :
    Evaluates (.get (.record fs) f) v :=
  evaluates_step (.field fs f body hf) h

theorem get_record_inv {fs : List (String × Term)} {f : String} {body v : Term}
    (hf : fs.find? (fun field => field.1 == f) = some (f, body)) (h : Evaluates (.get (.record fs) f) v) :
    Evaluates body v := by
  obtain ⟨gs, body', hr, hg, hb⟩ := get_inv h
  have := evaluates_value (.record _) hr
  cases this
  rw [hf] at hg; cases hg
  exact hb

public theorem blameProbe_true (field : String) (law : Term) (o n rq : Data) :
    Evaluates (blameProbe field law o n rq) (observationTerm (Verdict.ok).obs) ↔ Admits law o n rq :=
  readVerdict_true

public theorem blameProbe_label (field : String) (law : Term) (o n rq : Data) (s : String) :
    Evaluates (blameProbe field law o n rq) (observationTerm (Verdict.refused s).obs) ↔
      ∃ p, Evaluates (applyLaw law o n rq) (.inject "refused" p) ∧ Evaluates (.get p field) (.label s) := by
  refine readVerdict_label.trans ?_
  simp only [inst_get0]

/-- **Soundness for an effective law**: the machine's `ok` is an admission, its `refusedBy name why`
a refusal whose record says `by = name`, `reason = why`. -/
public theorem judgeEffective_sound {law : Term} (closed : Scoped 0 law) {policy : State → Bool}
    {limits : Limits} {budget : Budget} {o n rq : Data} {b : Blame}
    (h : judgeEffective policy limits budget law o n rq = some b) : BlameJudged law o n rq b := by
  unfold judgeEffective at h
  split at h
  · rename_i hby
    cases h
    exact (blameProbe_true "by" law o n rq).1 (runProbe_sound (blameProbe_scoped closed "by" o n rq) hby)
  · rename_i name hby
    split at h
    · rename_i why hwhy
      cases h
      obtain ⟨p, hp, hpb⟩ := (blameProbe_label "by" law o n rq name).1
        (runProbe_sound (blameProbe_scoped closed "by" o n rq) hby)
      obtain ⟨p', hp', hpr⟩ := (blameProbe_label "reason" law o n rq why).1
        (runProbe_sound (blameProbe_scoped closed "reason" o n rq) hwhy)
      have := evaluates_unique hp hp'
      simp only [Term.inject.injEq, true_and] at this
      subst this
      exact ⟨p, hp, hpb, hpr⟩
    · cases h
  · cases h

/-- **The machine names the ancestor clause.** Run on the effective law of a precedence list of
closed laws, a machine `refusedBy name why` means: `name` is on the list, every law before it
admitted, and its own law refused with a reason that evaluates to `why`. A machine `ok` means every
law on the list admitted. -/
public theorem judgeEffective_names {lin : List (String × Term)} (hc : ∀ p ∈ lin, closedB p.2 = true)
    {policy : State → Bool} {limits : Limits} {budget : Budget} {o n rq : Data} :
    (judgeEffective policy limits budget (effective lin) o n rq = some .ok → ∀ p ∈ lin, Admits p.2 o n rq) ∧
    (∀ name why, judgeEffective policy limits budget (effective lin) o n rq = some (.refusedBy name why) →
      ∃ pre L post, lin = pre ++ (name, L) :: post ∧ (∀ q ∈ pre, Admits q.2 o n rq) ∧ RefusesAs L o n rq why) := by
  have closed := effective_scoped hc
  refine ⟨fun h => (effective_law_eval hc o n rq).1 (judgeEffective_sound closed h), fun name why h => ?_⟩
  obtain ⟨p, hp, hby, hreason⟩ := judgeEffective_sound closed h
  obtain ⟨pre, name', L, post, why', hlin, hpre, hL, hblame⟩ := effective_refusal_names hc hp
  have := evaluates_unique hp hblame
  simp only [blamed, Term.inject.injEq, true_and] at this
  subst this
  have hn := get_record_inv (body := .label name') (by simp) hby
  have := evaluates_value (.label _) hn
  simp only [Term.label.injEq] at this
  subst this
  exact ⟨pre, L, post, hlin, hpre, why', hL, get_record_inv (body := why') (by simp) hreason⟩

/-- **Completeness for an effective law**: when every law on the list admits, or when the laws
before `name` admit and `name`'s law refuses with reason `why`, the unrestricted machine returns
that verdict at every resource past a threshold. -/
public theorem judgeEffective_complete {lin : List (String × Term)} (hc : ∀ p ∈ lin, closedB p.2 = true)
    {o n rq : Data} :
    ((∀ p ∈ lin, Admits p.2 o n rq) → ∃ (limits₀ : Limits) (ticks₀ bytes₀ : Nat), ∀ (limits : Limits) (budget : Budget),
      Covers limits limits₀ → ticks₀ ≤ budget.ticks → 1 ≤ budget.nodes → bytes₀ ≤ budget.bytes →
      judgeEffective (fun _ => true) limits budget (effective lin) o n rq = some .ok) ∧
    (∀ pre name L post why, lin = pre ++ (name, L) :: post → (∀ q ∈ pre, Admits q.2 o n rq) →
      RefusesAs L o n rq why → ∃ (limits₀ : Limits) (ticks₀ bytes₀ : Nat), ∀ (limits : Limits) (budget : Budget),
      Covers limits limits₀ → ticks₀ ≤ budget.ticks → 1 ≤ budget.nodes → bytes₀ ≤ budget.bytes →
      judgeEffective (fun _ => true) limits budget (effective lin) o n rq = some (.refusedBy name why)) := by
  have closed := effective_scoped hc
  constructor
  · intro hall
    have ha := (effective_law_eval hc o n rq).2 hall
    obtain ⟨L₀, t₀, hrun⟩ := runProbe_complete (blameProbe_scoped closed "by" o n rq)
      ((blameProbe_true "by" _ o n rq).2 ha)
    refine ⟨L₀, t₀, groundBytes (Verdict.ok).obs, fun limits budget cover ticks nodes bytes => ?_⟩
    unfold judgeEffective
    rw [hrun limits budget cover ticks nodes bytes]
  · intro pre name L post why hlin hpre hL
    obtain ⟨why', hLr, hwhy⟩ := hL
    subst hlin
    have hrb := effective_refuses_first hc hpre hLr
    have hby : Evaluates (blameProbe "by" (effective (pre ++ (name, L) :: post)) o n rq)
        (observationTerm (Verdict.refused name).obs) :=
      (blameProbe_label "by" _ o n rq name).2 ⟨_, hrb, get_record_eval (body := .label name) (by simp) (evaluates_self (.label _))⟩
    have hre : Evaluates (blameProbe "reason" (effective (pre ++ (name, L) :: post)) o n rq)
        (observationTerm (Verdict.refused why).obs) :=
      (blameProbe_label "reason" _ o n rq why).2 ⟨_, hrb, get_record_eval (body := why') (by simp) hwhy⟩
    obtain ⟨L₁, t₁, r₁⟩ := runProbe_complete (blameProbe_scoped closed "by" o n rq) hby
    obtain ⟨L₂, t₂, r₂⟩ := runProbe_complete (blameProbe_scoped closed "reason" o n rq) hre
    refine ⟨⟨max L₁.heap L₂.heap, max L₁.stack L₂.stack⟩, max t₁ t₂,
      max (groundBytes (Verdict.refused name).obs) (groundBytes (Verdict.refused why).obs),
      fun limits budget cover ticks nodes bytes => ?_⟩
    have c₁ : Covers limits L₁ := ⟨by have := cover.1; simp only at this; omega, by have := cover.2; simp only at this; omega⟩
    have c₂ : Covers limits L₂ := ⟨by have := cover.1; simp only at this; omega, by have := cover.2; simp only at this; omega⟩
    unfold judgeEffective
    rw [r₁ limits budget c₁ (by omega) nodes (by omega), r₂ limits budget c₂ (by omega) nodes (by omega)]

end Obend.Law
