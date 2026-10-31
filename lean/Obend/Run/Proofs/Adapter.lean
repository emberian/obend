module
/-
# Obend.Run.Proofs.Adapter — what holds of every run through the completed adapter

`areachable_legal`: at every configuration the adapter reaches from a start, whatever the events
(world moves, replies, re-bases, choices, accepted or refused):

- the runner configuration is one the runner reaches from the activity's start UNDER THE CURRENT
  PARAMETERS (depth, ticks, choices), so its log is `Legal` for that activity (`reachable_legal`)
  and every theorem of the runner applies to it, the re-bases included;
- `ResponsesTyped`: every reply in the log conforms to the declared response type;
- `ChoicesHeld`: every dispatched Plan chosen at a choice point found what its choice cites holding
  at the world of its dispatch.

A re-base keeps the log exactly (`rebase_ok`); a choice changes only the choice at the run's own
position, which no dispatch of the log occupies (`dispatched_before`).
-/
public import Obend.Run.Adapter
public import Obend.Run.Proofs.Invariant
public import Obend.Run.Proofs.Core4
public import Obend.Tactic.Tooth
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Run.Core4
import all Obend.Run.Adapter
import all Obend.Run.Proofs.Invariant

namespace Obend.Run.Core4

open Obend.Slot Obend.Slot.Protocol Obend.Core.Machine Obend.Core.Data

variable {Tok Fact Ob V : Type}

/-- Every reply of the log conforms to `τ`. -/
public def ResponsesTyped (τ : Obend.Core.Ty.Ty) (log : List (Event planSig NoHole (fun _ => Stop) Fact V)) : Prop :=
  ∀ e ∈ log, ∀ x : Entry planSig, e = .respond x → x.2.2.conforms τ = true

/-- Every dispatched Plan chosen at a choice point (by `cs`, at its position) found what its choice
cites holding at the world of its dispatch. -/
public def ChoicesHeld (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (cs : List (Nat × Data)) :
    List (Event planSig NoHole (fun _ => Stop) Fact V) → Prop :=
  AtEach fun pre e => ∀ o, e = .dispatch o → choiceAt cs (histOf pre).answered.length = some o.2 →
    ∀ f ∈ D.supports o.2, (host.view (worldOf D.v₀ pre)).holds f = true

/-! ## Lists of choices -/

theorem find_filter_ne (cs : List (Nat × Data)) {pos p : Nat} (h : p ≠ pos) :
    (cs.filter fun e => e.1 != pos).find? (fun e => e.1 == p) = cs.find? (fun e => e.1 == p) := by
  induction cs with
  | nil => rfl
  | cons e t ih =>
    by_cases he : e.1 = pos
    · have hp : (e.1 == p) = false := by rw [he]; simpa using Ne.symm h
      have hne : (pos == p) = false := by simpa using Ne.symm h
      simp [he, hne, ih]
    · have hk : (e.1 != pos) = true := by simpa using he
      simp only [List.filter_cons, hk, ↓reduceIte, List.find?_cons]
      rw [ih]

theorem choiceAt_setChoice_ne (cs : List (Nat × Data)) {pos p : Nat} (q : Data) (h : p ≠ pos) :
    choiceAt (setChoice cs pos q) p = choiceAt cs p := by
  unfold choiceAt setChoice
  have hne : (pos == p) = false := by simpa using Ne.symm h
  rw [List.find?_cons, hne]
  simp only
  rw [find_filter_ne cs h]

/-! ## Logs -/

section
variable [DecidableEq Tok]

/-- An accepted runner event is appended to the log. -/
theorem run_log {host : Host V Tok Fact} {sp : Spec planSig Tok Fact Ob}
    {c c' : ACfg' Tok Fact Ob V} {e : Event planSig NoHole (fun _ => Stop) Fact V}
    (hr : run host sp c e = .ok c') : c'.log = c.log ++ [e] := by
  cases e with
  | replan h => exact nomatch (h : Empty)
  | world v =>
    simp only [run] at hr
    split at hr
    · cases hr; rfl
    · cases hr
  | dispatch o =>
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | (cases hr; subst_vars; rfl) | skip
    all_goals (cases hr; rfl)
  | respond r =>
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | (cases hr; rfl)
  | abandon o =>
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | (cases hr; rfl)

/-- A session whose every event was accepted appends them all. -/
theorem session_all_log {host : Host V Tok Fact} {sp : Spec planSig Tok Fact Ob} :
    ∀ (c : ACfg' Tok Fact Ob V) (evs : List (Event planSig NoHole (fun _ => Stop) Fact V)),
      firstRefused (session host sp c evs).2 = none → (session host sp c evs).1.log = c.log ++ evs
  | c, [], _ => by simp [session]
  | c, ev :: evs, h => by
    simp only [session] at h ⊢
    cases hr : run host sp c ev with
    | error w => rw [hr] at h; simp [firstRefused] at h
    | ok c' =>
      rw [hr] at h
      simp only [firstRefused, Option.map_eq_none_iff] at h
      rw [session_all_log c' evs h, run_log hr]
      simp

/-- **A re-base keeps the log**, and its configuration is one the runner reaches from the activity's
start under the new parameters. -/
public theorem rebase_ok {D : Deploy Tok Fact Ob V} {host : Host V Tok Fact} {sp : Spec planSig Tok Fact Ob}
    {a a' : ACfg Tok Fact Ob V} {par' : Par} (h : rebase D host sp a par' = .ok a') :
    a'.par = par' ∧ a'.cfg.log = a.cfg.log ∧ Reachable host sp (Cfg.init (D.obj par') D.v₀) a'.cfg := by
  unfold rebase at h
  simp only at h
  split at h
  · cases h
  · rename_i hn
    cases h
    exact ⟨rfl, by rw [session_all_log _ _ hn]; rfl, session_reachable .init _⟩

end

/-! ## Histories -/

section
variable {Ix : Type} {S : Sig Ix} {Hole A : Ix → Type} {Fact V : Type}

theorem histOf_snoc (log : List (Event S Hole A Fact V)) (e : Event S Hole A Fact V) :
    histOf (log ++ [e]) = match e with
      | .dispatch o => ⟨(histOf log).answered, some o⟩
      | .respond r => ⟨(histOf log).answered ++ [r], none⟩
      | _ => histOf log := by
  unfold histOf
  rw [List.foldl_append]
  cases e <;> rfl

/-- Induction from the right. -/
theorem snocInd {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ l x, motive l → motive (l ++ [x])) (l : List α) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons x t ih => rw [List.reverse_cons]; exact snoc _ _ ih

theorem answered_snoc_le (log : List (Event S Hole A Fact V)) (e : Event S Hole A Fact V) :
    (histOf log).answered.length ≤ (histOf (log ++ [e])).answered.length := by
  rw [histOf_snoc]; cases e <;> simp

theorem answered_take_le (log : List (Event S Hole A Fact V)) (n : Nat) :
    (histOf (log.take n)).answered.length ≤ (histOf log).answered.length := by
  induction log using snocInd generalizing n with
  | nil => simp
  | snoc l e ih =>
    by_cases hn : n ≤ l.length
    · rw [List.take_append_of_le_length hn]
      exact Nat.le_trans (ih n) (answered_snoc_le l e)
    · rw [List.take_of_length_le (by simp; omega)]
      exact Nat.le_refl _

/-- **A dispatch of the log sits before the log's own position**, unless a call is still in flight:
every dispatched call was answered since, so its position is less than the answered count. -/
theorem dispatched_before (log : List (Event S Hole A Fact V)) :
    ∀ n o, log[n]? = some (.dispatch o) →
      (histOf (log.take n)).answered.length < (histOf log).answered.length ∨
        (histOf log).inflight ≠ none := by
  induction log using snocInd with
  | nil => intro n o h; simp at h
  | snoc l e ih =>
    intro n o h
    by_cases hn : n < l.length
    · rw [List.getElem?_append_left hn] at h
      rw [List.take_append_of_le_length (Nat.le_of_lt hn)]
      rcases ih n o h with lt | infl
      · exact .inl (Nat.lt_of_lt_of_le lt (answered_snoc_le l e))
      · rw [histOf_snoc]
        cases e with
        | dispatch o' => exact .inr (by simp)
        | respond r =>
          refine .inl ?_
          simp only [List.length_append, List.length_singleton]
          exact Nat.lt_succ_of_le (answered_take_le l n)
        | _ => exact .inr infl
    · have hn' : n = l.length := by
        have := (List.getElem?_eq_some_iff.1 h).1
        simp at this; omega
      subst hn'
      rw [List.getElem?_append_right (Nat.le_refl _)] at h
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact .inr (by rw [histOf_snoc]; simp)

end

/-! ## Every adapter run -/

section
variable [DecidableEq Tok]
variable {D : Deploy Tok Fact Ob V} {host : Host V Tok Fact} {sp : Spec planSig Tok Fact Ob}

/-- What holds of an adapter configuration. -/
public structure AInv (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact) (sp : Spec planSig Tok Fact Ob)
    (a : ACfg Tok Fact Ob V) : Prop where
  reach : Reachable host sp (Cfg.init (D.obj a.par) D.v₀) a.cfg
  typed : ResponsesTyped D.resp a.cfg.log
  chosen : ChoicesHeld D host a.par.choices a.cfg.log

omit [DecidableEq Tok] in
theorem lift_ok {a a' : ACfg Tok Fact Ob V} {r : Except (Refusal planSig NoHole Tok Fact) (ACfg' Tok Fact Ob V)}
    (h : lift a r = .ok a') : a'.par = a.par ∧ r = .ok a'.cfg := by
  unfold lift at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem inv_run {a a' : ACfg Tok Fact Ob V} {e : Event planSig NoHole (fun _ => Stop) Fact V}
    (hI : AInv D host sp a) (hr : lift a (run host sp a.cfg e) = .ok a')
    (htyped : ∀ x, e = .respond x → x.2.2.conforms D.resp = true)
    (hchoice : ∀ o, e = .dispatch o → choiceAt a.par.choices a.cfg.obj.hist.answered.length = some o.2 →
      ∀ f ∈ D.supports o.2, (host.view a.cfg.world).holds f = true) :
    AInv D host sp a' := by
  obtain ⟨hpar, hrun⟩ := lift_ok hr
  have hlog := run_log hrun
  have hInv := refines hI.reach
  refine ⟨?_, ?_, ?_⟩
  · rw [hpar]; exact .step e hI.reach hrun
  · rw [hlog]
    intro x hx y hy
    rcases List.mem_append.1 hx with hx | hx
    · exact hI.typed x hx y hy
    · simp only [List.mem_singleton] at hx; subst hx; exact htyped y hy
  · rw [hlog, hpar]
    refine AtEach.snoc.2 ⟨hI.chosen, fun o ho hc f hf => ?_⟩
    have hhist : histOf a.cfg.log = a.cfg.obj.hist := by rw [hInv.obj]
    rw [hhist] at hc
    have := hchoice o ho hc f hf
    rw [← hInv.world]
    exact this

/-- **Every adapter run**: the runner configuration is reachable from the activity's start under the
current parameters (so its log is `Legal` for that activity), every reply conforms to the declared
response type, and every Plan chosen at a choice point found its choice's citations holding at its
dispatch. -/
public theorem areachable_inv {par₀ : Par} {a : ACfg Tok Fact Ob V}
    (h : AReachable D host sp (D.start par₀) a) : AInv D host sp a := by
  induction h with
  | init => exact ⟨.init, (fun _ hx => by cases hx), AtEach.nil _⟩
  | @step a a' ev _ hs ih =>
    cases ev with
    | world v =>
      exact inv_run ih hs (fun _ h => by cases h) (fun _ h => by cases h)
    | abandon p =>
      exact inv_run ih hs (fun _ h => by cases h) (fun _ h => by cases h)
    | respond p r =>
      simp only [arun] at hs
      by_cases ht : typedReply D r = true
      · simp only [ht, ↓reduceIte] at hs
        exact inv_run ih hs (fun x hx => by cases hx; exact ht) (fun _ h => by cases h)
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hs; cases hs
    | dispatch p =>
      simp only [arun] at hs
      cases hg : choiceGuard D host a p with
      | cons f d => rw [hg] at hs; cases hs
      | nil =>
        rw [hg] at hs
        refine inv_run ih hs (fun _ h => by cases h) fun o ho hc f hf => ?_
        cases ho
        unfold choiceGuard at hg
        rw [hc] at hg
        simp only [↓reduceIte] at hg
        have := List.filter_eq_nil_iff.1 hg f hf
        simpa using this
    | deepen m =>
      obtain ⟨hpar, hlog, hreach⟩ := rebase_ok hs
      refine ⟨hpar ▸ hreach, hlog ▸ ih.typed, ?_⟩
      rw [hlog, hpar]; exact ih.chosen
    | moreTicks m =>
      obtain ⟨hpar, hlog, hreach⟩ := rebase_ok hs
      refine ⟨hpar ▸ hreach, hlog ▸ ih.typed, ?_⟩
      rw [hlog, hpar]; exact ih.chosen
    | choose q =>
      simp only [arun] at hs
      by_cases hb : a.cfg.obj.hist.inflight.isSome = true
      · simp only [hb, ↓reduceIte] at hs; cases hs
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hs
        have hnone : a.cfg.obj.hist.inflight = none := by simpa using hb
        cases hd : choiceDead D host a.cfg q with
        | cons f d => rw [hd] at hs; cases hs
        | nil =>
          rw [hd] at hs
          simp only at hs
          split at hs
          · cases hs
          · rename_i a₁ hreb
            have ha : a' = a₁ := by
              split at hs
              · split at hs
                · cases hs; rfl
                · cases hs
              · cases hs
            subst ha
            obtain ⟨hpar, hlog, hreach⟩ := rebase_ok hreb
            refine ⟨hpar ▸ hreach, hlog ▸ ih.typed, ?_⟩
            rw [hlog, hpar]
            have hInv := refines ih.reach
            have hhist : histOf a.cfg.log = a.cfg.obj.hist := by rw [hInv.obj]
            intro n z hz o ho hc f hf
            have hpos : (histOf (a.cfg.log.take n)).answered.length ≠ a.cfg.obj.hist.answered.length := by
              subst ho
              rcases dispatched_before a.cfg.log n o hz with lt | infl
              · rw [← hhist]; exact Nat.ne_of_lt lt
              · rw [hhist, hnone] at infl; exact absurd rfl infl
            rw [choiceAt_setChoice_ne _ _ hpos] at hc
            exact ih.chosen n z hz o ho hc f hf

/-- The log of every adapter run is `Legal` for the activity under the current parameters. -/
public theorem areachable_legal {par₀ : Par} {a : ACfg Tok Fact Ob V}
    (h : AReachable D host sp (D.start par₀) a) :
    Legal host sp (D.obj a.par) D.v₀ (fun _ _ => []) a.cfg.log :=
  reachable_legal (areachable_inv h).reach

omit [DecidableEq Tok] in
/-- Without choice points the adapter's unfolding is the activity's. -/
public theorem aunfold_plain {L : Limits} {budget : Budget} {alts : Data → Option (List Data)}
    (hplain : ∀ p, alts p = none) (par : Par) :
    ∀ (n pos : Nat) (s : State), aunfold L budget alts par pos n s = unfold L par.ticks budget n s
  | 0, _, _ => rfl
  | n + 1, pos, s => by
    simp only [aunfold, unfold]
    cases turn L par.ticks budget s with
    | stop x => rfl
    | vis p y =>
      simp only [hplain p]
      congr 1
      funext r
      cases resume r.term y with
      | none => rfl
      | some s' => exact aunfold_plain hplain par n (pos + 1) s'

omit [DecidableEq Tok] in
theorem obj_plain (hplain : ∀ p, D.alts p = none) (par : Par) :
    D.obj par = activity D.L par.ticks D.budget par.depth D.s₀ D.Γ D.Δ D.Φ := by
  unfold Deploy.obj
  rw [aunfold_plain hplain par]
  rfl

/-- **Without choice points, every adapter run is a run of the machine** under the current depth
and ticks, deepened and given more ticks mid-run as it was: its log is `Legal`, its answered history
is a transcript of the machine's turns at the current tick bound, its residual is the activity
resumed, and the call in flight is the Plan the machine yields there (`trace_is_run`). -/
public theorem plain_trace (hplain : ∀ p, D.alts p = none) {par₀ : Par} {a : ACfg Tok Fact Ob V}
    (h : AReachable D host sp (D.start par₀) a) :
    Legal host sp (D.obj a.par) D.v₀ (fun _ _ => []) a.cfg.log ∧
      ∃ s' m, Transcript D.L a.par.ticks D.budget D.s₀ a.cfg.obj.hist.answered s' ∧
        a.par.depth = a.cfg.obj.hist.answered.length + m ∧
        a.cfg.res = ⟨(), unfold D.L a.par.ticks D.budget m s'⟩ ∧
        ∀ o, a.cfg.obj.hist.inflight = some o → ∃ y, turn D.L a.par.ticks D.budget s' = .vis o.2 y := by
  have hr := (areachable_inv h).reach
  rw [obj_plain hplain] at hr ⊢
  exact trace_is_run hr

/-- An adapter session ends at an adapter-reachable configuration. -/
public theorem asession_reachable {a₀ a : ACfg Tok Fact Ob V} (ha : AReachable D host sp a₀ a)
    (evs : List (AEvent V)) : AReachable D host sp a₀ (asession D host sp a evs).1 := by
  induction evs generalizing a with
  | nil => exact ha
  | cons ev evs ih =>
    simp only [asession]
    cases h : arun D host sp a ev with
    | ok a' => exact ih (.step ev ha h)
    | error w => exact ih ha

end

end Obend.Run.Core4
