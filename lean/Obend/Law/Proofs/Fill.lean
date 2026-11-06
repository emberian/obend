module
/-
# Obend.Law.Proofs.Fill — a law with holes, run and judged before and after the fill

`Obend.Core.Fill` proves the object-level substitution principle over the reference semantics
(`fill_continues`). Here it is carried to what a kernel actually runs: `run`, the fuel-bounded
iteration of `step?`, and the verdict of a law (`Judged`, which the machine's `judge` returns).

* `run_fill`: a run that reaches a value with holes in the term reaches, at the same fuel, that
  value filled.
* `run_fill_continues`: if `k` steps take the term with holes to `r` (`iterStep k t = some r`,
  typically a residual stuck at a hole), then with `k + m` fuel the filled term runs exactly as
  the filled residual runs with `m`: the first `k` steps are never redone.
* `judged_fill`: a verdict the law with holes already reaches (it never demanded a hole) is the
  verdict of every filling of it; `judged_fill_residual`: if the law's application runs to a
  residual `r`, the filled law's verdict is the verdict of `r` filled. `blameJudged_fill` is the
  same for an effective law, whose refusal names the ancestor.
* `judge_fill`: for a filled law that is closed, every verdict the machine returns is the one the
  law with holes reached, and with enough resources the machine returns it.
-/
public import Obend.Core.Fill
public import Obend.Law.Proofs.Machine
namespace Obend.Law
open Obend.Core.Term
open Obend.Core.Data (Data Budget fieldsTerm)
open Obend.Core.Machine (State Limits)
open Obend.Core.Proofs.GroundExecution (Covers groundBytes)
set_option autoImplicit false

/-! ## `run` under filling -/

theorem value_of_isValueB {t : Term} (h : isValueB t = true) : Value t := by
  cases t <;> simp [isValueB] at h <;> constructor

theorem isValueB_of_value {t : Term} (h : Value t) : isValueB t = true := by
  cases h <;> rfl

/-- `k` applications of `step?`. -/
@[expose] public def iterStep : Nat → Term → Option Term
  | 0, t => some t
  | k + 1, t => (step? t).bind (iterStep k)

public theorem iterStep_steps : ∀ (k : Nat) {t r : Term}, iterStep k t = some r → Steps t r
  | 0, t, r, h => by simp only [iterStep, Option.some.injEq] at h; subst h; exact .refl _
  | k + 1, t, r, h => by
    simp only [iterStep] at h
    cases hs : step? t with
    | none => simp [hs] at h
    | some t' =>
      simp only [hs, Option.bind_some] at h
      exact .next (step_iff.2 hs) (iterStep_steps k h)

/-- A term with holes that steps fills to a term that steps the same way, so it is not a value. -/
theorem fill_step? {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ) {t t' : Term}
    (h : HoleArity Δ t) (hs : step? t = some t') :
    step? (t.fill θ) = some (t'.fill θ) ∧ isValueB (t.fill θ) = false := by
  have s := fill_step hθ (step_iff.2 hs) h
  refine ⟨step_iff.1 s, ?_⟩
  cases hv : isValueB (t.fill θ) with
  | false => rfl
  | true => exact absurd s (value_no_step (value_of_isValueB hv))

/-- **A run of the term with holes is, at the same fuel, a run of every filling of it.** -/
public theorem run_fill {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ) :
    ∀ (fuel : Nat) {t v : Term}, HoleArity Δ t → run fuel t = some v → run fuel (t.fill θ) = some (v.fill θ)
  | 0, t, v, _, h => by
    simp only [run] at h
    split at h
    · rename_i hv
      cases h
      simp [run, isValueB_of_value (value_fill θ (value_of_isValueB hv))]
    · cases h
  | fuel + 1, t, v, ha, h => by
    simp only [run] at h
    split at h
    · rename_i hv
      cases h
      simp [run, isValueB_of_value (value_fill θ (value_of_isValueB hv))]
    · split at h
      · rename_i t' hs
        obtain ⟨hs', hv'⟩ := fill_step? hθ ha hs
        simp only [run, hv', hs', Bool.false_eq_true, ite_false]
        exact run_fill hθ fuel (holeArity_step Δ (step_iff.2 hs) ha) h
      · cases h

/-- **`fill_continues` in fuel form.** If `k` steps take the term with holes to `r`, the filled
term with `k + m` fuel runs as the filled `r` with `m`. -/
public theorem run_fill_continues {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ) :
    ∀ (k : Nat) {t r : Term}, HoleArity Δ t → iterStep k t = some r →
      ∀ m, run (k + m) (t.fill θ) = run m (r.fill θ)
  | 0, t, r, _, h, m => by
    simp only [iterStep, Option.some.injEq] at h; subst h; rw [Nat.zero_add]
  | k + 1, t, r, ha, h, m => by
    simp only [iterStep] at h
    cases hs : step? t with
    | none => simp [hs] at h
    | some t' =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨hs', hv'⟩ := fill_step? hθ ha hs
      rw [show k + 1 + m = (k + m) + 1 by omega]
      simp only [run, hv', hs', Bool.false_eq_true, ite_false]
      exact run_fill_continues hθ k (holeArity_step Δ (step_iff.2 hs) ha) h m

/-! ## Data has no holes -/

mutual
theorem data_fill (θ : Nat → Option Term) (Δ : Nat → Nat) :
    (d : Data) → d.term.fill θ = d.term ∧ HoleArity Δ d.term
  | .natural _ => ⟨by simp [Data.term, Term.fill], holeArity_literal Δ (by simp [Data.term, IsLiteral])⟩
  | .boolean _ => ⟨by simp [Data.term, Term.fill], holeArity_literal Δ (by simp [Data.term, IsLiteral])⟩
  | .label _ => ⟨by simp [Data.term, Term.fill], holeArity_literal Δ (by simp [Data.term, IsLiteral])⟩
  | .record fs => by
    obtain ⟨h1, h2⟩ := fields_fill θ Δ fs
    simp only [Data.term, Term.fill, holeArity_record]
    exact ⟨by rw [h1], h2⟩
  | .variant _ p => by
    obtain ⟨h1, h2⟩ := data_fill θ Δ p
    simp only [Data.term, Term.fill, holeArity_inject]
    exact ⟨by rw [h1], h2⟩
theorem fields_fill (θ : Nat → Option Term) (Δ : Nat → Nat) :
    (fs : List (String × Data)) →
      (fieldsTerm fs).map (fun f => (f.1, f.2.fill θ)) = fieldsTerm fs ∧ ∀ f ∈ fieldsTerm fs, HoleArity Δ f.2
  | [] => ⟨rfl, by simp [fieldsTerm]⟩
  | (_, v) :: rest => by
    obtain ⟨h1, h2⟩ := data_fill θ Δ v
    obtain ⟨r1, r2⟩ := fields_fill θ Δ rest
    simp only [fieldsTerm, List.map_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨by rw [h1, r1], h2, r2⟩
end

public theorem applyLaw_fill (θ : Nat → Option Term) (law : Term) (o n rq : Data) :
    (applyLaw law o n rq).fill θ = applyLaw (law.fill θ) o n rq := by
  simp only [applyLaw, Term.fill, (data_fill θ (fun _ => 0) o).1, (data_fill θ (fun _ => 0) n).1,
    (data_fill θ (fun _ => 0) rq).1]

public theorem holeArity_applyLaw (Δ : Nat → Nat) {law : Term} (h : HoleArity Δ law) (o n rq : Data) :
    HoleArity Δ (applyLaw law o n rq) := by
  simp only [applyLaw, holeArity_app]
  exact ⟨⟨⟨h, (data_fill (fun _ => none) Δ o).2⟩, (data_fill (fun _ => none) Δ n).2⟩,
    (data_fill (fun _ => none) Δ rq).2⟩

/-! ## A law with holes, judged -/

/-- The verdict a term reaches: `ok`, or `refused` with a reason that evaluates to the label. -/
@[expose] public def TermJudged (t : Term) : Verdict → Prop
  | .ok => ∃ w, Evaluates t (.inject "ok" w)
  | .refused why => ∃ p, Evaluates t (.inject "refused" p) ∧ Evaluates p (.label why)

public theorem judged_iff_termJudged (law : Term) (o n rq : Data) (v : Verdict) :
    Judged law o n rq v ↔ TermJudged (applyLaw law o n rq) v := by
  cases v <;> rfl

/-- What a term with holes already judges, every filling of it judges. -/
public theorem termJudged_fill {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ)
    {t : Term} (ht : HoleArity Δ t) {v : Verdict} (h : TermJudged t v) : TermJudged (t.fill θ) v := by
  cases v with
  | ok =>
    obtain ⟨w, hw⟩ := h
    exact ⟨w.fill θ, by simpa only [Term.fill] using fill_evaluates hθ hw ht⟩
  | refused why =>
    obtain ⟨p, hp, hwhy⟩ := h
    have hpa : HoleArity Δ p := by
      have := holeArity_steps Δ hp.1 ht
      simpa only [holeArity_inject] using this
    refine ⟨p.fill θ, by simpa only [Term.fill] using fill_evaluates hθ hp ht, ?_⟩
    simpa only [Term.fill] using fill_evaluates hθ hwhy hpa

/-- **A verdict the law with holes reaches is the verdict of every filling of it.** -/
public theorem judged_fill {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ)
    {law : Term} (hl : HoleArity Δ law) {o n rq : Data} {v : Verdict} (h : Judged law o n rq v) :
    Judged (law.fill θ) o n rq v := by
  rw [judged_iff_termJudged] at h ⊢
  rw [← applyLaw_fill]
  exact termJudged_fill hθ (holeArity_applyLaw Δ hl o n rq) h

/-- **The filled law's verdict is the verdict of the filled residual.** If the law with holes,
applied, runs to `r` (stuck at a hole, or anywhere), the filled law judges as `r` filled. -/
public theorem judged_fill_residual {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ)
    {law : Term} (hl : HoleArity Δ law) {o n rq : Data} {r : Term} (s : Steps (applyLaw law o n rq) r)
    (v : Verdict) : Judged (law.fill θ) o n rq v ↔ TermJudged (r.fill θ) v := by
  rw [judged_iff_termJudged, ← applyLaw_fill]
  have ha := holeArity_applyLaw Δ hl o n rq
  cases v with
  | ok =>
    exact exists_congr fun w => fill_continues hθ s ha _
  | refused why =>
    exact exists_congr fun p => and_congr_left' (fill_continues hθ s ha _)

/-- The same for an effective law: a refusal that names its ancestor stays named. -/
public theorem blameJudged_fill {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ)
    {law : Term} (hl : HoleArity Δ law) {o n rq : Data} {b : Blame} (h : BlameJudged law o n rq b) :
    BlameJudged (law.fill θ) o n rq b := by
  have ha := holeArity_applyLaw Δ hl o n rq
  cases b with
  | ok => exact judged_fill (v := .ok) hθ hl h
  | refusedBy name why =>
    obtain ⟨p, hp, hby, hwhy⟩ := h
    have hpa : HoleArity Δ p := by
      have := holeArity_steps Δ hp.1 ha
      simpa only [holeArity_inject] using this
    have hg : ∀ f, HoleArity Δ (.get p f) := fun f => by simpa only [holeArity_get] using hpa
    refine ⟨p.fill θ, ?_, ?_, ?_⟩
    · rw [← applyLaw_fill]; simpa only [Term.fill] using fill_evaluates hθ hp ha
    · simpa only [Term.fill] using fill_evaluates hθ hby (hg "by")
    · simpa only [Term.fill] using fill_evaluates hθ hwhy (hg "reason")

/-- **The machine on the filled law.** When the filled law is closed, every verdict the machine
returns on it (any policy and resources) is the verdict the law with holes reached, and with enough
resources the unrestricted machine returns it. -/
public theorem judge_fill {Δ : Nat → Nat} {θ : Nat → Option Term} (hθ : FillersScoped Δ θ)
    {law : Term} (hl : HoleArity Δ law) (closed : closedB (law.fill θ) = true) {o n rq : Data}
    {v : Verdict} (h : Judged law o n rq v) :
    (∀ (policy : State → Bool) (limits : Limits) (budget : Budget) (v' : Verdict),
      judge policy limits budget (law.fill θ) o n rq = some v' → v' = v) ∧
    ∃ (limits₀ : Limits) (ticks₀ : Nat), ∀ (limits : Limits) (budget : Budget),
      Covers limits limits₀ → ticks₀ ≤ budget.ticks → 1 ≤ budget.nodes → groundBytes v.obs ≤ budget.bytes →
      judge (fun _ => true) limits budget (law.fill θ) o n rq = some v := by
  have hf := judged_fill hθ hl h
  obtain ⟨snd, uniq, comp⟩ := machine_judges closed o n rq
  exact ⟨fun policy limits budget v' hj => uniq v' v (snd policy limits budget v' hj) hf, comp v hf⟩

end Obend.Law
