module
/-
# Obend.Run.Proofs.Adapter — invariant, `Simulates` equivalence (`stepCheckpoint_eq_replay`), and `typed_checkpoint` refinement

1. `areachable_legal`: at every configuration the adapter reaches from a start, whatever the events
   (world moves, replies, re-bases, choices, accepted or refused):
   - the runner configuration is reachable under the current parameters (`reachable_legal`);
   - `ResponsesTyped`: every reply in the log conforms to the declared response type;
   - `ChoicesHeld`: every dispatched Plan chosen at a choice point found what its choice cites
     holding at the world of its dispatch.
2. `Simulates`, `stepCheckpoint_eq_replay`, `checkpointSession_eq_replay`: the $O(T)$ live
   `Checkpoint` transition (`stepCheckpoint` / `checkpointSession`) agrees identically with cold
   full-history `Log` replay (`arun` / `asession`) on every event and refusal across multi-turn
   traces while avoiding $O(M^2 T)$ replay.
3. `checkpointReachable_settled_typed`: across every reachable `Checkpoint` trace from a well-typed
   initial machine state `D.s₀`, both `ck.frontier` and the settled/compacted yield snapshot
   `ck.settled` (`Obend.Core.Collect.checkpoint`) preserve `StateTyping` via
   `Obend.Core.Collect.typed_checkpoint` and `typed_resume_preserved`.
-/
public import Obend.Run.Adapter
public import Obend.Run.Proofs.Invariant
public import Obend.Run.Proofs.Core4
public import Obend.Core.Term
public import Obend.Core.Ty
public import Obend.Core.Assumptions
public import Obend.Core.Check
public import Obend.Core.Machine
public import Obend.Core.MachineTyping
public import Obend.Core.Proofs.Force
import all Obend.Core.Data
import all Obend.Slot.Proofs.Protocol
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Run.Core4
import all Obend.Run.Adapter
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Core4
import all Obend.Core.Proofs.Force

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

theorem choiceAt_setChoice_self (cs : List (Nat × Data)) (pos : Nat) (q : Data) :
    choiceAt (setChoice cs pos q) pos = some q := by
  simp [choiceAt, setChoice]

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
        simpa [choiceDead, choiceDeadAt] using this
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

/-! ## Live $O(T)$ `Checkpoint` Simulation (`Simulates`, `stepCheckpoint_eq_replay`) & `typed_checkpoint` -/

section
variable [DecidableEq Tok]
variable {D : Deploy Tok Fact Ob V} {host : Host V Tok Fact} {sp : Spec planSig Tok Fact Ob}

omit [DecidableEq Tok] in
private theorem entered_nohole {A : Unit → Type} :
    ∀ {i : Unit} (P : Prot planSig NoHole A i) (t : Trace planSig) (b : Bool),
      entered P t b = none
  | _, .ret _, _, _ => rfl
  | _, .hole h, _, _ => nomatch (h : Empty)
  | _, .call _ _, [], _ => rfl
  | _, .call _ _, _ :: _, _ => by
    simp only [entered]
    split
    · exact entered_nohole _ _ _
    · rfl

omit [DecidableEq Tok] in
private theorem decisionDead_nohole (O : Open planSig NoHole (fun _ => Stop) Tok Fact Ob ())
    (cites : (j : Unit) → NoHole j → List Fact) (v : View Tok Fact) :
    decisionDead O cites v = [] := by
  unfold decisionDead owner
  rw [entered_nohole]

omit [DecidableEq Tok] in
private theorem pushConsumedTok_toList (spent : Array Tok) (op : Data) :
    (pushConsumedTok spent (sp.consumes (i := ()) op)).toList = spendOn (i := ()) sp spent.toList op := by
  unfold pushConsumedTok spendOn
  cases sp.consumes (i := ()) op <;> simp

omit [DecidableEq Tok] in
theorem runBounded_yielded_add (L : Limits) :
    ∀ (ticks m : Nat) (s y : State) (plan : Address),
      runBounded L ticks s = .yielded plan y →
      runBounded L (ticks + m) s = .yielded plan y
  | 0, m, s, y, plan, h => by
    obtain ⟨hc, rfl⟩ := Obend.Core.Collect.runBounded_zero_yielded h
    cases m <;> simp [runBounded, step, hc]
  | ticks + 1, m, s, y, plan, h => by
    have hadd : ticks + 1 + m = (ticks + m) + 1 := by omega
    rw [hadd]
    simp only [runBounded] at h ⊢
    cases hs : step L s with
    | suspended r next =>
      cases r with
      | ticks =>
        rw [hs] at h
        exact runBounded_yielded_add L ticks m next y plan h
      | capacity => rw [hs] at h; cases h
    | finished _ _ => rw [hs] at h; cases h
    | divergent _ _ => rw [hs] at h; cases h
    | refused _ _ => rw [hs] at h; cases h
    | yielded _ _ => rw [hs] at h; exact h

omit [DecidableEq Tok] in
theorem turn_vis_mono {L : Limits} {ticks : Nat} {budget : Budget} {s y : State} {p : Data}
    (h : turn L ticks budget s = .vis p y) (m : Nat) :
    turn L (ticks + m) budget s = .vis p y := by
  unfold turn at h ⊢
  cases hr : runBounded L ticks s with
  | yielded plan y₀ =>
    rw [hr] at h
    rw [runBounded_yielded_add L ticks m s y₀ plan hr]
    exact h
  | finished _ _ => rw [hr] at h; cases h
  | suspended _ _ => rw [hr] at h; cases h
  | divergent _ _ => rw [hr] at h; cases h
  | refused _ _ => rw [hr] at h; cases h

omit [DecidableEq Tok] in
theorem turn_vis_le {L : Limits} {ticks ticks' : Nat} {budget : Budget} {s y : State} {p : Data}
    (hle : ticks ≤ ticks') (h : turn L ticks budget s = .vis p y) :
    turn L ticks' budget s = .vis p y := by
  have heq : ticks' = ticks + (ticks' - ticks) := by omega
  rw [heq]
  exact turn_vis_mono h (ticks' - ticks)

omit [DecidableEq Tok] in
private theorem aunfold_vis_some {L : Limits} {budget : Budget} {alts : Data → Option (List Data)}
    {par : Par} {pos n : Nat} {s y : State} {rawPlan op : Data}
    (ht : turn L par.ticks budget s = .vis rawPlan y)
    (hn : nextPlanOf alts par pos rawPlan = some op) :
    aunfold L budget alts par pos (n + 1) s =
      .call (S := planSig) op fun r =>
        match resume r.term y with
        | some s' => aunfold L budget alts par (pos + 1) n s'
        | none => .ret .unresumable := by
  simp only [aunfold, ht]
  unfold nextPlanOf at hn
  cases ha : alts rawPlan with
  | none =>
    rw [ha] at hn; cases hn; rfl
  | some as =>
    rw [ha] at hn
    cases hc : choiceAt par.choices pos with
    | none => rw [hc] at hn; cases hn
    | some q =>
      rw [hc] at hn
      by_cases hmem : q ∈ as
      · simp only [hmem, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        simp only [hmem, ↓reduceIte]
        rfl
      · simp [hmem] at hn

omit [DecidableEq Tok] in
private theorem aunfold_vis_none {L : Limits} {budget : Budget} {alts : Data → Option (List Data)}
    {par : Par} {pos n : Nat} {s y : State} {rawPlan : Data}
    (ht : turn L par.ticks budget s = .vis rawPlan y)
    (hn : nextPlanOf alts par pos rawPlan = none) :
    ∃ as, aunfold L budget alts par pos (n + 1) s = .ret (.choice as) := by
  simp only [aunfold, ht]
  unfold nextPlanOf at hn
  cases ha : alts rawPlan with
  | none => rw [ha] at hn; cases hn
  | some as =>
    rw [ha] at hn
    cases hc : choiceAt par.choices pos with
    | none => exact ⟨as, rfl⟩
    | some q =>
      rw [hc] at hn
      by_cases hmem : q ∈ as
      · simp [hmem] at hn
      · exact ⟨as, by simp [hmem]⟩

private theorem session_snoc_ok (host : Host V Tok Fact) (sp : Spec planSig Tok Fact Ob) :
    ∀ (c₀ c c' : ACfg' Tok Fact Ob V)
      (log : List (Event planSig NoHole (fun _ => Stop) Fact V))
      (rs : List (Option (Refusal planSig NoHole Tok Fact)))
      (ev : Event planSig NoHole (fun _ => Stop) Fact V),
      session host sp c₀ log = (c, rs) →
      run host sp c ev = .ok c' →
      session host sp c₀ (log ++ [ev]) = (c', rs ++ [none])
  | c₀, c, c', [], rs, ev, hs, hr => by
    simp only [session, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    simp [session, hr]
  | c₀, c, c', x :: xs, rs, ev, hs, hr => by
    rw [List.cons_append]
    simp only [session] at hs ⊢
    cases hx : run host sp c₀ x with
    | ok c₁ =>
      cases htail : session host sp c₁ xs with
      | mk cf rf =>
        simp only [hx, htail, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl⟩
        have ih := session_snoc_ok host sp c₁ cf c' xs rf ev htail hr
        simp [ih]
    | error w =>
      cases htail : session host sp c₀ xs with
      | mk cf rf =>
        simp only [hx, htail, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl⟩
        have ih := session_snoc_ok host sp c₀ cf c' xs rf ev htail hr
        simp [ih]

omit [DecidableEq Tok] in
private theorem firstRefused_replicate_none :
    ∀ k : Nat, firstRefused (List.replicate k (none : Option (Refusal planSig NoHole Tok Fact))) = none
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, firstRefused, firstRefused_replicate_none k]

omit [DecidableEq Tok] in
private theorem replicate_snoc_none (k : Nat) :
    List.replicate k (none : Option (Refusal planSig NoHole Tok Fact)) ++ [none] =
      List.replicate (k + 1) none := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

omit [DecidableEq Tok] in
private theorem sigma_unit_op_ne {p q : Data} (h : p ≠ q) :
    (⟨(), p⟩ : Σ i, planSig.Op i) ≠ ⟨(), q⟩ :=
  fun heq => h (eq_of_heq (Sigma.mk.inj heq).2)

omit [DecidableEq Tok] in
private theorem follow_aunfold_vis_some {L : Limits} {budget : Budget}
    {alts : Data → Option (List Data)} {par : Par} {pos n : Nat}
    {s y s' : State} {rawPlan p r : Data}
    (ht : turn L par.ticks budget s = .vis rawPlan y)
    (hn : nextPlanOf alts par pos rawPlan = some p)
    (hres : resume r.term y = some s') :
    follow ⟨(), aunfold L budget alts par pos (n + 1) s⟩ ⟨(), p, r⟩ =
      some ⟨(), aunfold L budget alts par (pos + 1) n s'⟩ := by
  rw [aunfold_vis_some ht hn]
  simp only [follow, ↓reduceDIte, Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
  change (match resume r.term y with
    | some s' => aunfold L budget alts par (pos + 1) n s'
    | none => Prot.ret Stop.unresumable) = aunfold L budget alts par (pos + 1) n s'
  rw [hres]

/-- Monotone parameter extension preserving all already-executed and in-flight turns of `ck`. -/
public structure ParExt (ck : Checkpoint Tok Fact Ob V) (par' : Par) (rem' : Nat) : Prop where
  depth_eq : par'.depth = ck.answered.size + rem'
  inflight_depth : ck.inflight.isSome = true → 1 ≤ rem'
  ticks_le : ck.par.ticks ≤ par'.ticks
  choices_past : ∀ pos, pos < ck.answered.size →
    choiceAt par'.choices pos = choiceAt ck.par.choices pos
  choices_inflight : ck.inflight.isSome = true →
    choiceAt par'.choices ck.answered.size = choiceAt ck.par.choices ck.answered.size

/-- Simulation relation between the live $O(T)$ `Checkpoint` state `ck` and the cold-replay
specification configuration `a : ACfg`. -/
public structure Simulates (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact)
    (sp : Spec planSig Tok Fact Ob) (ck : Checkpoint Tok Fact Ob V)
    (a : ACfg Tok Fact Ob V) : Prop where
  toACfg_eq : Checkpoint.toACfg D ck = a
  depth_eq : ck.par.depth = ck.answered.size + ck.remDepth
  inflight_inv : ∀ dispPlan y, ck.inflight = some (dispPlan, y) →
    ∃ n rawPlan, ck.remDepth = n + 1 ∧
      turn D.L ck.par.ticks D.budget ck.frontier = .vis rawPlan y ∧
      nextPlanOf D.alts ck.par ck.answered.size rawPlan = some dispPlan
  ended_inflight : ∀ p, ck.ended = some p → ∃ y, ck.inflight = some (p, y)
  replays : ∀ (par' : Par) (rem' : Nat), ParExt ck par' rem' →
    session host sp (Cfg.init (D.obj par') D.v₀) ck.log.toList =
      ((Checkpoint.toACfg D { ck with par := par', remDepth := rem' }).cfg,
       List.replicate ck.log.size none)

omit [DecidableEq Tok] in
private theorem parExt_refl {ck : Checkpoint Tok Fact Ob V}
    (hdepth : ck.par.depth = ck.answered.size + ck.remDepth)
    (hinf : ∀ dispPlan y, ck.inflight = some (dispPlan, y) →
      ∃ n rawPlan, ck.remDepth = n + 1 ∧
        turn D.L ck.par.ticks D.budget ck.frontier = .vis rawPlan y ∧
        nextPlanOf D.alts ck.par ck.answered.size rawPlan = some dispPlan) :
    ParExt ck ck.par ck.remDepth where
  depth_eq := hdepth
  inflight_depth := by
    cases hi : ck.inflight with
    | none => simp
    | some xy =>
      intro _
      obtain ⟨n, _, hn, _, _⟩ := hinf xy.1 xy.2 hi
      omega
  ticks_le := Nat.le_refl _
  choices_past := fun _ _ => rfl
  choices_inflight := fun _ => rfl

/-- Every `Simulates` pair has a `Reachable` specification configuration under `a.par`. -/
public theorem Simulates.reachable {ck : Checkpoint Tok Fact Ob V} {a : ACfg Tok Fact Ob V}
    (hS : Simulates D host sp ck a) :
    Reachable host sp (Cfg.init (D.obj a.par) D.v₀) a.cfg := by
  have hrep := hS.replays ck.par ck.remDepth (parExt_refl hS.depth_eq hS.inflight_inv)
  have reach0 := session_reachable (host := host) (sp := sp)
    (c₀ := Cfg.init (D.obj ck.par) D.v₀) .init ck.log.toList
  rw [hrep] at reach0
  have ha : Checkpoint.toACfg D { ck with par := ck.par, remDepth := ck.remDepth } = a :=
    hS.toACfg_eq
  rw [← ha]
  exact reach0

omit [DecidableEq Tok] in
private theorem toACfg_init_cfg (D : Deploy Tok Fact Ob V) (par : Par) :
    (Checkpoint.toACfg D { Checkpoint.init D par with par := par, remDepth := par.depth }).cfg =
      Cfg.init (D.obj par) D.v₀ := by
  unfold Checkpoint.toACfg Checkpoint.init Cfg.init
  dsimp only
  congr 2
  exact (subst_nohole _ _).symm

/-- `Checkpoint.init D par₀` simulates `D.start par₀`. -/
public theorem init_simulates (D : Deploy Tok Fact Ob V) (host : Host V Tok Fact)
    (sp : Spec planSig Tok Fact Ob) (par₀ : Par) :
    Simulates D host sp (Checkpoint.init D par₀) (D.start par₀) where
  toACfg_eq := by
    unfold Deploy.start
    have h := toACfg_init_cfg D par₀
    cases hc : Checkpoint.toACfg D (Checkpoint.init D par₀) with
    | mk p cfg =>
      have hp : p = par₀ := by
        have := congrArg ACfg.par hc; simpa [Checkpoint.toACfg, Checkpoint.init] using this.symm
      subst hp
      have hcfg : cfg = Cfg.init (D.obj p) D.v₀ := by
        have := congrArg ACfg.cfg hc
        simpa [Checkpoint.init] using this.symm.trans h
      subst hcfg
      rfl
  depth_eq := by simp [Checkpoint.init]
  inflight_inv := fun _ _ h => by simp [Checkpoint.init] at h
  ended_inflight := fun _ h => by simp [Checkpoint.init] at h
  replays := fun par' rem' hExt => by
    have hd : par'.depth = rem' := by
      have := hExt.depth_eq; simpa [Checkpoint.init] using this
    subst hd
    simp only [Checkpoint.init, Array.toList_empty, Array.size_empty, List.replicate, session]
    exact Prod.ext (toACfg_init_cfg D par').symm rfl

private theorem rebase_of_parExt {ck : Checkpoint Tok Fact Ob V} {a : ACfg Tok Fact Ob V}
    (hS : Simulates D host sp ck a) {par' : Par} {rem' : Nat} (hExt : ParExt ck par' rem') :
    rebase D host sp a par' = .ok (Checkpoint.toACfg D { ck with par := par', remDepth := rem' }) := by
  have haEq := hS.toACfg_eq
  subst haEq
  unfold rebase
  have hlog : (Checkpoint.toACfg D ck).cfg.log = ck.log.toList := rfl
  rw [hlog, hS.replays par' rem' hExt]
  simp [firstRefused_replicate_none, Checkpoint.toACfg]

/-- **Exact Single-Step Simulation (`stepCheckpoint_eq_replay`)**:
At every `Simulates` configuration, `stepCheckpoint` produces the exact same `ACfg` (under
`Checkpoint.toACfg D`) or the exact same `ARefusal` as cold full-history `Log` replay (`arun`). -/
public theorem stepCheckpoint_eq_replay {ck : Checkpoint Tok Fact Ob V} {a : ACfg Tok Fact Ob V}
    (hS : Simulates D host sp ck a) (ev : AEvent V) :
    (stepCheckpoint D host sp ck ev).map (Checkpoint.toACfg D) = arun D host sp a ev := by
  have haEq := hS.toACfg_eq
  subst haEq
  cases ev with
  | world v' =>
    simp only [stepCheckpoint, arun, run, lift]
    by_cases hw : host.allowed ck.world v' = true
    · simp [hw, Except.map, Checkpoint.toACfg, Array.toList_push]
    · simp [hw, Except.map, Checkpoint.toACfg]
  | abandon p =>
    simp only [stepCheckpoint, arun]
    cases hend : ck.ended with
    | some e =>
      have hcl : closedBy (Checkpoint.toACfg D ck).cfg = some ⟨(), e⟩ := by
        simp [closedBy, Checkpoint.toACfg, Option.map, hend]
      simp [run, hcl, lift, Except.map]
    | none =>
      have hcl : closedBy (Checkpoint.toACfg D ck).cfg = none := by
        simp [closedBy, Checkpoint.toACfg, Option.map, hend]
      cases hinf : ck.inflight with
      | none =>
        have haw : awaiting (Checkpoint.toACfg D ck).cfg.obj.hist = none := by
          simp [awaiting, Checkpoint.toACfg, Option.map, hinf]
        simp [run, hcl, haw, lift, Except.map]
      | some xy =>
        rcases xy with ⟨o', y⟩
        have haw : awaiting (Checkpoint.toACfg D ck).cfg.obj.hist = some ⟨(), o'⟩ := by
          simp [awaiting, Checkpoint.toACfg, Option.map, hinf]
        by_cases hp : p = o'
        · subst hp
          unfold run lift
          rw [hcl, haw]
          simp [Except.map, Checkpoint.toACfg, Option.map, Array.toList_push, hend, hinf]
        · have hne := sigma_unit_op_ne hp
          unfold run lift
          rw [hcl, haw]
          simp [hp, hne, Except.map]
  | respond p r =>
    simp only [stepCheckpoint, arun]
    by_cases ht : typedReply D r = true
    · simp only [ht, ↓reduceIte]
      cases hend : ck.ended with
      | some e =>
        have hcl : closedBy (Checkpoint.toACfg D ck).cfg = some ⟨(), e⟩ := by
          simp [closedBy, Checkpoint.toACfg, Option.map, hend]
        simp [run, hcl, lift, Except.map]
      | none =>
        have hcl : closedBy (Checkpoint.toACfg D ck).cfg = none := by
          simp [closedBy, Checkpoint.toACfg, Option.map, hend]
        cases hinf : ck.inflight with
        | none =>
          have hinf' : (Checkpoint.toACfg D ck).cfg.obj.hist.inflight = none := by
            simp [Checkpoint.toACfg, Option.map, hinf]
          simp [run, hcl, hinf', lift, Except.map]
        | some xy =>
          rcases xy with ⟨o', y⟩
          have hinf' : (Checkpoint.toACfg D ck).cfg.obj.hist.inflight = some ⟨(), o'⟩ := by
            simp [Checkpoint.toACfg, Option.map, hinf]
          by_cases hp : p = o'
          · subst hp
            obtain ⟨n, rawPlan, hrem, hturn, hnext⟩ := hS.inflight_inv p y hinf
            obtain ⟨s', hres⟩ := turn_vis_resumes hturn r.term
            have hFollow : follow (Checkpoint.toACfg D ck).cfg.res ⟨(), p, r⟩ =
                some ⟨(), aunfold D.L D.budget D.alts ck.par (ck.answered.size + 1) n s'⟩ := by
              simp only [Checkpoint.toACfg, hrem]
              exact follow_aunfold_vis_some hturn hnext hres
            simp only [↓reduceIte, hres, Except.map]
            unfold run lift
            rw [hcl, hinf']
            simp only [↓reduceIte, hFollow]
            congr 1
            simp [Checkpoint.toACfg, Option.map, Array.toList_push, Array.size_push, hend, hrem]
          · have hne := sigma_unit_op_ne hp
            simp only [hp, ↓reduceIte, Except.map]
            unfold run lift
            rw [hcl, hinf']
            simp [hne]
    · simp [ht, Except.map]
  | dispatch p =>
    have hcg : choiceGuard D host (Checkpoint.toACfg D ck) p = choiceGuardCheckpoint D host ck p := by
      simp [choiceGuard, choiceGuardCheckpoint, Checkpoint.toACfg, choiceDead]
    simp only [stepCheckpoint, arun, hcg]
    cases hg : choiceGuardCheckpoint D host ck p with
    | cons f d => simp [Except.map]
    | nil =>
      simp only
      cases hend : ck.ended with
      | some e =>
        have hcl : closedBy (Checkpoint.toACfg D ck).cfg = some ⟨(), e⟩ := by
          simp [closedBy, Checkpoint.toACfg, Option.map, hend]
        simp [run, hcl, lift, Except.map]
      | none =>
        have hcl : closedBy (Checkpoint.toACfg D ck).cfg = none := by
          simp [closedBy, Checkpoint.toACfg, Option.map, hend]
        cases hinf : ck.inflight with
        | some xy =>
          have haw : awaiting (Checkpoint.toACfg D ck).cfg.obj.hist = some ⟨(), xy.1⟩ := by
            simp [awaiting, Checkpoint.toACfg, Option.map, hinf]
          simp [run, hcl, haw, lift, Except.map]
        | none =>
          have haw : awaiting (Checkpoint.toACfg D ck).cfg.obj.hist = none := by
            simp [awaiting, Checkpoint.toACfg, Option.map, hinf]
          cases hrem : ck.remDepth with
          | zero =>
            have hResCfg : (Checkpoint.toACfg D ck).cfg.res = ⟨(), .ret .depth⟩ := by
              simp [Checkpoint.toACfg, hrem, aunfold]
            simp [run, hcl, haw, hResCfg, lift, Except.map]
          | succ n =>
            rw [turnFast_eq_turn]
            cases hturn : turn D.L ck.par.ticks D.budget ck.frontier with
            | stop x =>
              have hResCfg : (Checkpoint.toACfg D ck).cfg.res = ⟨(), .ret x⟩ := by
                simp [Checkpoint.toACfg, hrem, aunfold, hturn]
              simp [run, hcl, haw, hResCfg, lift, Except.map]
            | vis rawPlan y =>
              cases hnext : nextPlanOf D.alts ck.par ck.answered.size rawPlan with
              | none =>
                obtain ⟨as, has⟩ := aunfold_vis_none (n := n) hturn hnext
                have hResCfg : (Checkpoint.toACfg D ck).cfg.res = ⟨(), .ret (.choice as)⟩ := by
                  simp [Checkpoint.toACfg, hrem, has]
                simp [hnext, run, hcl, haw, hResCfg, lift, Except.map]
              | some op =>
                have hUnf := aunfold_vis_some (n := n) hturn hnext
                have hResCfg : (Checkpoint.toACfg D ck).cfg.res =
                    ⟨(), .call (S := planSig) op fun r =>
                      match resume r.term y with
                      | some s' => aunfold D.L D.budget D.alts ck.par (ck.answered.size + 1) n s'
                      | none => .ret .unresumable⟩ := by
                  simp [Checkpoint.toACfg, hrem, hUnf]
                simp only [hnext]
                by_cases hp : p = op
                · subst hp
                  have hv : View.maskArray (host.view ck.world) ck.spent =
                      (Checkpoint.toACfg D ck).cfg.admitView host := by
                    simp [Checkpoint.toACfg, Cfg.admitView, maskArray_eq_mask]
                  have hdd : decisionDead (Checkpoint.toACfg D ck).cfg.obj
                      (Checkpoint.toACfg D ck).cfg.cites
                      ((Checkpoint.toACfg D ck).cfg.admitView host) = [] :=
                    decisionDead_nohole _ _ _
                  simp only [↓reduceIte, hv]
                  by_cases hdg : dispatchGuard (i := ()) sp ((Checkpoint.toACfg D ck).cfg.admitView host) p = true
                  · simp only [hdg, ↓reduceIte, Except.map]
                    unfold run lift
                    rw [hcl, haw, hResCfg]
                    simp only [↓reduceIte, hdg, hdd]
                    congr 1
                    simp [Checkpoint.toACfg, Option.map, Array.toList_push, hrem, hUnf, hend, hinf,
                      pushConsumedTok_toList]
                  · simp only [hdg, Bool.false_eq_true, ↓reduceIte, Except.map]
                    unfold run lift
                    rw [hcl, haw, hResCfg]
                    simp [hdg]
                · have hne := sigma_unit_op_ne hp
                  simp only [hp, ↓reduceIte, Except.map]
                  unfold run lift
                  rw [hcl, haw, hResCfg]
                  simp [hne]
  | deepen m =>
    have hExt : ParExt ck { ck.par with depth := ck.par.depth + m } (ck.remDepth + m) := by
      refine ⟨by have := hS.depth_eq; simp; omega, ?_, Nat.le_refl _, fun _ _ => rfl, fun _ => rfl⟩
      cases hi : ck.inflight with
      | none => simp
      | some xy => obtain ⟨n, _, hn, _, _⟩ := hS.inflight_inv xy.1 xy.2 hi; intro _; omega
    have hpar : (Checkpoint.toACfg D ck).par = ck.par := rfl
    simp only [stepCheckpoint, arun, Except.map, hpar]
    rw [rebase_of_parExt hS hExt]
  | moreTicks m =>
    have hExt : ParExt ck { ck.par with ticks := ck.par.ticks + m } ck.remDepth := by
      refine ⟨hS.depth_eq, ?_, by simp, fun _ _ => rfl, fun _ => rfl⟩
      cases hi : ck.inflight with
      | none => simp
      | some xy => obtain ⟨n, _, hn, _, _⟩ := hS.inflight_inv xy.1 xy.2 hi; intro _; omega
    have hpar : (Checkpoint.toACfg D ck).par = ck.par := rfl
    simp only [stepCheckpoint, arun, Except.map, hpar]
    rw [rebase_of_parExt hS hExt]
  | choose q =>
    have hinfEq : (Checkpoint.toACfg D ck).cfg.obj.hist.inflight.isSome = ck.inflight.isSome := by
      simp only [Checkpoint.toACfg, Option.map]
      cases ck.inflight <;> rfl
    have hcdEq : choiceDead D host (Checkpoint.toACfg D ck).cfg q = choiceDeadAt D host ck.world q := rfl
    have hlenEq : (Checkpoint.toACfg D ck).cfg.obj.hist.answered.length = ck.answered.size := by
      simp [Checkpoint.toACfg]
    have hpar : (Checkpoint.toACfg D ck).par = ck.par := rfl
    simp only [stepCheckpoint, arun, hinfEq, hcdEq, hlenEq, hpar]
    cases hinf : ck.inflight with
    | some _ => simp [Except.map]
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      cases hcd : choiceDeadAt D host ck.world q with
      | cons f d => simp [Except.map]
      | nil =>
        simp only
        let par₁ : Par := { ck.par with choices := setChoice ck.par.choices ck.answered.size q }
        have hExt : ParExt ck par₁ ck.remDepth := by
          refine ⟨hS.depth_eq, by simp [hinf], Nat.le_refl _, fun pos hlt => ?_, by simp [hinf]⟩
          exact choiceAt_setChoice_ne ck.par.choices q (Nat.ne_of_lt hlt)
        rw [rebase_of_parExt hS hExt]
        simp only
        cases hrem : ck.remDepth with
        | zero =>
          simp [Checkpoint.toACfg, aunfold, Except.map]
        | succ n =>
          rw [turnFast_eq_turn]
          cases hturn : turn D.L ck.par.ticks D.budget ck.frontier with
          | stop x =>
            have hturn₁ : turn D.L par₁.ticks D.budget ck.frontier = .stop x := hturn
            simp [Checkpoint.toACfg, aunfold, hturn₁, Except.map]
          | vis rawPlan y =>
            have hturn₁ : turn D.L par₁.ticks D.budget ck.frontier = .vis rawPlan y := hturn
            cases ha : D.alts rawPlan with
            | none =>
              simp only [Checkpoint.toACfg, aunfold, hturn₁, ha]
              by_cases hpq : rawPlan = q
              · subst hpq
                cases hd : decData rawPlan rawPlan with
                | isTrue _ =>
                  simp [Except.map, Checkpoint.toACfg, Option.map, par₁, aunfold, hturn, ha, hinf]
                | isFalse hf => exact absurd rfl hf
              · cases hd : decData rawPlan q with
                | isTrue ht => exact absurd ht hpq
                | isFalse _ => simp [hpq, Except.map]
            | some as =>
              have hcs : choiceAt par₁.choices ck.answered.size = some q :=
                choiceAt_setChoice_self ck.par.choices ck.answered.size q
              simp only [Checkpoint.toACfg, aunfold, hturn₁, ha, hcs]
              by_cases hmem : q ∈ as
              · cases hd : decData q q with
                | isTrue _ =>
                  simp only [hmem, decide_true, ↓reduceIte, hd, Except.map]
                  congr 1
                  simp [Checkpoint.toACfg, Option.map, par₁, aunfold, hturn, ha, hcs, hmem, hinf]
                | isFalse hf => exact absurd rfl hf
              · simp [hmem, Except.map]

/-- Accepted `stepCheckpoint` transitions preserve `Simulates` against `arun`. -/
public theorem stepCheckpoint_simulates {ck ck' : Checkpoint Tok Fact Ob V} {a : ACfg Tok Fact Ob V}
    {ev : AEvent V} (hS : Simulates D host sp ck a)
    (hStep : stepCheckpoint D host sp ck ev = .ok ck') :
    ∃ a', arun D host sp a ev = .ok a' ∧ Simulates D host sp ck' a' := by
  have hEq := stepCheckpoint_eq_replay hS ev
  rw [hStep] at hEq
  simp only [Except.map] at hEq
  refine ⟨Checkpoint.toACfg D ck', hEq.symm, ?_⟩
  cases ev with
  | world v' =>
    simp only [stepCheckpoint] at hStep
    by_cases hw : host.allowed ck.world v' = true
    · simp only [hw, ↓reduceIte, Except.ok.injEq] at hStep
      subst hStep
      refine ⟨rfl, hS.depth_eq, hS.inflight_inv, hS.ended_inflight, fun par' rem' hExt => ?_⟩
      have hExt0 : ParExt ck par' rem' :=
        ⟨hExt.depth_eq, hExt.inflight_depth, hExt.ticks_le, hExt.choices_past, hExt.choices_inflight⟩
      have hrep := hS.replays par' rem' hExt0
      have hrun : run host sp (Checkpoint.toACfg D { ck with par := par', remDepth := rem' }).cfg (.world v') =
          .ok (Checkpoint.toACfg D { ck with world := v', log := ck.log.push (.world v'), par := par', remDepth := rem' }).cfg := by
        simp [run, Checkpoint.toACfg, hw]
      simpa [Array.toList_push, Array.size_push, replicate_snoc_none] using
        session_snoc_ok host sp _ _ _ ck.log.toList _ (.world v') hrep hrun
    · simp [hw] at hStep
  | abandon p =>
    cases hend : ck.ended with
    | some _ => simp [stepCheckpoint, hend] at hStep
    | none =>
      cases hinf : ck.inflight with
      | none => simp [stepCheckpoint, hend, hinf] at hStep
      | some xy =>
        rcases xy with ⟨o', y⟩
        by_cases hp : p = o'
        · subst hp
          have hck' : ck' = { ck with ended := some p, log := ck.log.push (.abandon ⟨(), p⟩) } := by
            simp only [stepCheckpoint, hend, hinf, ↓reduceIte, Except.ok.injEq] at hStep
            simpa [hend, hinf] using hStep.symm
          subst hck'
          refine ⟨rfl, hS.depth_eq, hS.inflight_inv,
            fun q hq => by simp only [Option.some.injEq] at hq; subst hq; exact ⟨y, hinf⟩,
            fun par' rem' hExt => ?_⟩
          have hExt0 : ParExt ck par' rem' :=
            ⟨hExt.depth_eq, hExt.inflight_depth, hExt.ticks_le, hExt.choices_past, hExt.choices_inflight⟩
          have hrep := hS.replays par' rem' hExt0
          have hrun : run host sp (Checkpoint.toACfg D { ck with par := par', remDepth := rem' }).cfg (.abandon ⟨(), p⟩) =
              .ok (Checkpoint.toACfg D { ck with ended := some p, log := ck.log.push (.abandon ⟨(), p⟩), par := par', remDepth := rem' }).cfg := by
            unfold run
            have hcl : closedBy (Checkpoint.toACfg D { ck with par := par', remDepth := rem' }).cfg = none := by
              simp [closedBy, Checkpoint.toACfg, Option.map, hend]
            have haw : awaiting (Checkpoint.toACfg D { ck with par := par', remDepth := rem' }).cfg.obj.hist = some ⟨(), p⟩ := by
              simp [awaiting, Checkpoint.toACfg, Option.map, hinf]
            rw [hcl, haw]
            simp [Checkpoint.toACfg, Option.map, Array.toList_push, hinf]
          simpa [Array.toList_push, Array.size_push, replicate_snoc_none] using
            session_snoc_ok host sp _ _ _ ck.log.toList _ (.abandon ⟨(), p⟩) hrep hrun
        · simp [stepCheckpoint, hend, hinf, hp] at hStep
  | respond p r =>
    by_cases ht : typedReply D r = true
    · cases hend : ck.ended with
      | some _ => simp [stepCheckpoint, ht, hend] at hStep
      | none =>
        cases hinf : ck.inflight with
        | none => simp [stepCheckpoint, ht, hend, hinf] at hStep
        | some xy =>
          rcases xy with ⟨o', y⟩
          by_cases hp : p = o'
          · subst hp
            cases hres : resume r.term y with
            | none => simp [stepCheckpoint, ht, hend, hinf, hres] at hStep
            | some s' =>
              obtain ⟨n, rawPlan, hrem, hturn, hnext⟩ := hS.inflight_inv p y hinf
              have hck' : ck' = { ck with
                  frontier := s'
                  inflight := none
                  remDepth := n
                  answered := ck.answered.push ⟨(), p, r⟩
                  log := ck.log.push (.respond ⟨(), p, r⟩) } := by
                simp only [stepCheckpoint, ht, hend, hinf, hres, hrem, ↓reduceIte, Except.ok.injEq] at hStep
                simpa [hend] using hStep.symm
              subst hck'
              refine ⟨rfl, ?_, fun _ _ h => by simp at h,
                fun q hq => by simp [hend] at hq,
                fun par' rem' hExt => ?_⟩
              · have := hS.depth_eq
                simp [Array.size_push, hrem] at this ⊢
                omega
              · have hExt0 : ParExt ck par' (rem' + 1) := by
                  refine ⟨?_, fun _ => by omega, hExt.ticks_le,
                    fun pos hlt => hExt.choices_past pos (by simp [Array.size_push]; omega),
                    fun _ => hExt.choices_past ck.answered.size (by simp [Array.size_push])⟩
                  have hd := hExt.depth_eq
                  simp [Array.size_push] at hd
                  omega
                have hrep := hS.replays par' (rem' + 1) hExt0
                have hturn' : turn D.L par'.ticks D.budget ck.frontier = .vis rawPlan y :=
                  turn_vis_le hExt0.ticks_le hturn
                have hnext' : nextPlanOf D.alts par' ck.answered.size rawPlan = some p := by
                  unfold nextPlanOf at hnext ⊢
                  rw [hExt0.choices_inflight (by simp [hinf])]
                  exact hnext
                have hrun : run host sp (Checkpoint.toACfg D { ck with par := par', remDepth := rem' + 1 }).cfg (.respond ⟨(), p, r⟩) =
                    .ok (Checkpoint.toACfg D { ck with
                      frontier := s', inflight := none, answered := ck.answered.push ⟨(), p, r⟩,
                      log := ck.log.push (.respond ⟨(), p, r⟩), par := par', remDepth := rem' }).cfg := by
                  have hcl : closedBy (Checkpoint.toACfg D { ck with par := par', remDepth := rem' + 1 }).cfg = none := by
                    simp [closedBy, Checkpoint.toACfg, Option.map, hend]
                  have hinf' : (Checkpoint.toACfg D { ck with par := par', remDepth := rem' + 1 }).cfg.obj.hist.inflight = some ⟨(), p⟩ := by
                    simp [Checkpoint.toACfg, Option.map, hinf]
                  have hFollow : follow (Checkpoint.toACfg D { ck with par := par', remDepth := rem' + 1 }).cfg.res ⟨(), p, r⟩ =
                      some ⟨(), aunfold D.L D.budget D.alts par' (ck.answered.size + 1) rem' s'⟩ := by
                    simp only [Checkpoint.toACfg]
                    exact follow_aunfold_vis_some hturn' hnext' hres
                  unfold run
                  rw [hcl, hinf']
                  simp only [↓reduceIte, hFollow]
                  congr 1
                  simp [Checkpoint.toACfg, Option.map, Array.toList_push, Array.size_push]
                simpa [Array.toList_push, Array.size_push, replicate_snoc_none] using
                  session_snoc_ok host sp _ _ _ ck.log.toList _ (.respond ⟨(), p, r⟩) hrep hrun
          · simp [stepCheckpoint, ht, hend, hinf, hp] at hStep
    · simp [stepCheckpoint, ht] at hStep
  | dispatch p =>
    cases hg : choiceGuardCheckpoint D host ck p with
    | cons _ _ => simp [stepCheckpoint, hg] at hStep
    | nil =>
      cases hend : ck.ended with
      | some _ => simp [stepCheckpoint, hg, hend] at hStep
      | none =>
        cases hinf : ck.inflight with
        | some _ => simp [stepCheckpoint, hg, hend, hinf] at hStep
        | none =>
          cases hrem : ck.remDepth with
          | zero => simp [stepCheckpoint, hg, hend, hinf, hrem] at hStep
          | succ n =>
            cases hturn : turn D.L ck.par.ticks D.budget ck.frontier with
            | stop _ => simp [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn] at hStep
            | vis rawPlan y =>
              cases hnext : nextPlanOf D.alts ck.par ck.answered.size rawPlan with
              | none => simp [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn, hnext] at hStep
              | some op =>
                by_cases hp : p = op
                · subst hp
                  by_cases hdg : dispatchGuard (i := ()) sp (View.maskArray (host.view ck.world) ck.spent) p = true
                  · have hck' : ck' = { ck with
                        inflight := some (p, y)
                        settled := Obend.Core.Collect.checkpoint y
                        spent := pushConsumedTok ck.spent (sp.consumes (i := ()) p)
                        log := ck.log.push (.dispatch ⟨(), p⟩) } := by
                      simp only [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn, hnext,
                        hdg, ↓reduceIte, Except.ok.injEq] at hStep
                      simpa [hend, hrem] using hStep.symm
                    subst hck'
                    refine ⟨rfl, hS.depth_eq,
                      fun disp y' hEq' => by
                        simp only [Option.some.injEq, Prod.mk.injEq] at hEq'
                        rcases hEq' with ⟨rfl, rfl⟩
                        exact ⟨n, rawPlan, hrem, hturn, hnext⟩,
                      fun q hq => by simp [hend] at hq,
                      fun par' rem' hExt => ?_⟩
                    have h1le : 1 ≤ rem' := hExt.inflight_depth rfl
                    obtain ⟨m', rfl⟩ : ∃ m', rem' = m' + 1 := ⟨rem' - 1, by omega⟩
                    have hExt0 : ParExt ck par' (m' + 1) :=
                      ⟨hExt.depth_eq, by simp [hinf], hExt.ticks_le, hExt.choices_past, by simp [hinf]⟩
                    have hrep := hS.replays par' (m' + 1) hExt0
                    have hturn' : turn D.L par'.ticks D.budget ck.frontier = .vis rawPlan y :=
                      turn_vis_le hExt.ticks_le hturn
                    have hnext' : nextPlanOf D.alts par' ck.answered.size rawPlan = some p := by
                      unfold nextPlanOf at hnext ⊢
                      rw [hExt.choices_inflight rfl]
                      exact hnext
                    have hUnf := aunfold_vis_some (n := m') hturn' hnext'
                    have hrun : run host sp (Checkpoint.toACfg D { ck with par := par', remDepth := m' + 1 }).cfg (.dispatch ⟨(), p⟩) =
                        .ok (Checkpoint.toACfg D { ck with
                          inflight := some (p, y), settled := Obend.Core.Collect.checkpoint y,
                          spent := pushConsumedTok ck.spent (sp.consumes (i := ()) p),
                          log := ck.log.push (.dispatch ⟨(), p⟩), par := par', remDepth := m' + 1 }).cfg := by
                      have hcl : closedBy (Checkpoint.toACfg D { ck with par := par', remDepth := m' + 1 }).cfg = none := by
                        simp [closedBy, Checkpoint.toACfg, Option.map, hend]
                      have haw : awaiting (Checkpoint.toACfg D { ck with par := par', remDepth := m' + 1 }).cfg.obj.hist = none := by
                        simp [awaiting, Checkpoint.toACfg, Option.map, hinf]
                      have hResCfg : (Checkpoint.toACfg D { ck with par := par', remDepth := m' + 1 }).cfg.res =
                          ⟨(), .call (S := planSig) p fun r =>
                            match resume r.term y with
                            | some s' => aunfold D.L D.budget D.alts par' (ck.answered.size + 1) m' s'
                            | none => .ret .unresumable⟩ := by
                        simp [Checkpoint.toACfg, hUnf]
                      have hv : (Checkpoint.toACfg D { ck with par := par', remDepth := m' + 1 }).cfg.admitView host =
                          View.maskArray (host.view ck.world) ck.spent := by
                        simp [Checkpoint.toACfg, Cfg.admitView, maskArray_eq_mask]
                      unfold run
                      rw [hcl, haw, hResCfg]
                      simp only [↓reduceIte, hv, hdg, decisionDead_nohole]
                      congr 1
                      simp [Checkpoint.toACfg, Option.map, Array.toList_push, hUnf, pushConsumedTok_toList]
                    simpa [Array.toList_push, Array.size_push, replicate_snoc_none] using
                      session_snoc_ok host sp _ _ _ ck.log.toList _ (.dispatch ⟨(), p⟩) hrep hrun
                  · simp [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn, hnext, hdg] at hStep
                · simp [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn, hnext, hp] at hStep
  | deepen m =>
    simp only [stepCheckpoint, Except.ok.injEq] at hStep
    subst hStep
    refine ⟨rfl, by have := hS.depth_eq; simp; omega,
      fun disp y h => by
        obtain ⟨n, raw, hn, ht, hnx⟩ := hS.inflight_inv disp y h
        exact ⟨n + m, raw, by simp [hn]; omega, ht, hnx⟩,
      hS.ended_inflight,
      fun par' rem' hExt => hS.replays par' rem'
        ⟨hExt.depth_eq, hExt.inflight_depth, hExt.ticks_le, hExt.choices_past, hExt.choices_inflight⟩⟩
  | moreTicks m =>
    simp only [stepCheckpoint, Except.ok.injEq] at hStep
    subst hStep
    refine ⟨rfl, hS.depth_eq,
      fun disp y h => by
        obtain ⟨n, raw, hn, ht, hnx⟩ := hS.inflight_inv disp y h
        exact ⟨n, raw, hn, turn_vis_mono ht m, hnx⟩,
      hS.ended_inflight,
      fun par' rem' hExt => hS.replays par' rem'
        ⟨hExt.depth_eq, hExt.inflight_depth,
         Nat.le_trans (Nat.le_add_right _ _) hExt.ticks_le,
         hExt.choices_past, hExt.choices_inflight⟩⟩
  | choose q =>
    cases hinf : ck.inflight with
    | some _ => simp [stepCheckpoint, hinf] at hStep
    | none =>
      cases hcd : choiceDeadAt D host ck.world q with
      | cons _ _ => simp [stepCheckpoint, hinf, hcd] at hStep
      | nil =>
        cases hrem : ck.remDepth with
        | zero => simp [stepCheckpoint, hinf, hcd, hrem] at hStep
        | succ n =>
          cases htf : turnFast D.L ck.par.ticks D.budget ck.frontier with
          | stop _ => simp [stepCheckpoint, hinf, hcd, hrem, htf] at hStep
          | vis rawPlan y =>
            have hck' : ck' = { ck with
                par := { ck.par with choices := setChoice ck.par.choices ck.answered.size q } } := by
              cases ha : D.alts rawPlan with
              | none =>
                by_cases hpq : rawPlan = q
                · subst hpq
                  simp only [stepCheckpoint, hinf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                    hcd, hrem, htf, ha, decide_true, Except.ok.injEq] at hStep
                  simpa [hinf, hrem] using hStep.symm
                · simp [stepCheckpoint, hinf, hcd, hrem, htf, ha, hpq] at hStep
              | some as =>
                by_cases hmem : q ∈ as
                · simp only [stepCheckpoint, hinf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                    hcd, hrem, htf, ha, hmem, decide_true, Except.ok.injEq] at hStep
                  simpa [hinf, hrem] using hStep.symm
                · simp [stepCheckpoint, hinf, hcd, hrem, htf, ha, hmem] at hStep
            subst hck'
            refine ⟨rfl, hS.depth_eq, fun _ _ h => by simp [hinf] at h,
              fun p hp => by obtain ⟨_, hy⟩ := hS.ended_inflight p hp; simp [hinf] at hy,
              fun par' rem' hExt => hS.replays par' rem'
                ⟨hExt.depth_eq, by simp [hinf], hExt.ticks_le,
                 fun pos hlt => by
                   rw [hExt.choices_past pos hlt]
                   exact choiceAt_setChoice_ne ck.par.choices q (Nat.ne_of_lt hlt),
                   by simp [hinf]⟩⟩

/-- Every `CheckpointReachable` state from `Checkpoint.init D par₀` simulates an `AReachable`
specification state from `D.start par₀`. -/
public theorem checkpointReachable_simulates {par₀ : Par} {ck : Checkpoint Tok Fact Ob V}
    (h : CheckpointReachable D host sp (Checkpoint.init D par₀) ck) :
    AReachable D host sp (D.start par₀) (Checkpoint.toACfg D ck) ∧
      Simulates D host sp ck (Checkpoint.toACfg D ck) := by
  induction h with
  | init =>
    have h0 := init_simulates D host sp par₀
    exact ⟨h0.toACfg_eq.symm ▸ .init, h0.toACfg_eq.symm ▸ h0⟩
  | @step ck₁ ck₂ ev _ hStep ih =>
    obtain ⟨hAR, hSim⟩ := ih
    obtain ⟨a', hArun, hSim'⟩ := stepCheckpoint_simulates hSim hStep
    rw [← hSim'.toACfg_eq] at hArun hSim'
    exact ⟨.step ev hAR hArun, hSim'⟩

/-- Every `CheckpointReachable` trace satisfies `Legal`, `ResponsesTyped`, and `ChoicesHeld`. -/
public theorem checkpointReachable_legal {par₀ : Par} {ck : Checkpoint Tok Fact Ob V}
    (h : CheckpointReachable D host sp (Checkpoint.init D par₀) ck) :
    Legal host sp (D.obj ck.par) D.v₀ (fun _ _ => []) ck.log.toList ∧
      ResponsesTyped D.resp ck.log.toList ∧
      ChoicesHeld D host ck.par.choices ck.log.toList := by
  obtain ⟨hAR, _⟩ := checkpointReachable_simulates h
  have hInv := areachable_inv hAR
  exact ⟨reachable_legal hInv.reach, hInv.typed, hInv.chosen⟩

private theorem checkpointSession_eq_asession_aux {ck : Checkpoint Tok Fact Ob V} {a : ACfg Tok Fact Ob V}
    (hS : Simulates D host sp ck a) (evs : List (AEvent V)) :
    Checkpoint.toACfg D (checkpointSession D host sp ck evs).1 = (asession D host sp a evs).1 ∧
      (checkpointSession D host sp ck evs).2 = (asession D host sp a evs).2 := by
  induction evs generalizing ck a with
  | nil => exact ⟨hS.toACfg_eq, rfl⟩
  | cons ev evs ih =>
    simp only [checkpointSession, asession]
    cases hStep : stepCheckpoint D host sp ck ev with
    | ok ck' =>
      obtain ⟨a', hArun, hSim'⟩ := stepCheckpoint_simulates hS hStep
      rw [hArun]
      obtain ⟨h1, h2⟩ := ih hSim'
      exact ⟨h1, congrArg (none :: ·) h2⟩
    | error w =>
      have hEq := stepCheckpoint_eq_replay hS ev
      rw [hStep] at hEq
      simp only [Except.map] at hEq
      rw [← hEq]
      obtain ⟨h1, h2⟩ := ih hS
      exact ⟨h1, congrArg (some w :: ·) h2⟩

/-- **Multi-Turn Live Session Equivalence (`checkpointSession_eq_replay`)**:
Running any multi-turn event sequence `evs` through the $O(T)$ live `checkpointSession` yields the
exact same final `ACfg` and per-event refusal receipt as cold-replay `asession`. -/
public theorem checkpointSession_eq_replay (par₀ : Par) (evs : List (AEvent V)) :
    Checkpoint.toACfg D (checkpointSession D host sp (Checkpoint.init D par₀) evs).1 =
      (asession D host sp (D.start par₀) evs).1 ∧
    (checkpointSession D host sp (Checkpoint.init D par₀) evs).2 =
      (asession D host sp (D.start par₀) evs).2 :=
  checkpointSession_eq_asession_aux (init_simulates D host sp par₀) evs

/-- An adapter `checkpointSession` ends at a `CheckpointReachable` state. -/
public theorem checkpointSession_reachable {ck₀ ck : Checkpoint Tok Fact Ob V}
    (hck : CheckpointReachable D host sp ck₀ ck) (evs : List (AEvent V)) :
    CheckpointReachable D host sp ck₀ (checkpointSession D host sp ck evs).1 := by
  induction evs generalizing ck with
  | nil => exact hck
  | cons ev evs ih =>
    simp only [checkpointSession]
    cases hs : stepCheckpoint D host sp ck ev with
    | ok ck' => exact ih (.step ev hck hs)
    | error _ => exact ih hck

/-! ## Multi-Turn `StateTyping` Preservation via `Obend.Core.Collect.typed_checkpoint` -/

omit [DecidableEq Tok] in
/-- Conforming empty-row (`Unit`) responses unconditionally elaborate to closed `PartialTyping`
derivations at `.emptyRow`. -/
public theorem conforms_emptyRow_typed (assumptions : Obend.Core.Check.Assumptions)
    {r : Data} (hconf : r.conforms .emptyRow = true) :
    ∃ u, Obend.Core.Check.PartialTyping assumptions [] r.term .emptyRow u := by
  cases r with
  | record fields =>
    cases fields with
    | nil => exact ⟨_, .record (.nil []) rfl⟩
    | cons _ _ => simp [Data.conforms, rowNames] at hconf
  | natural _ => cases hconf
  | boolean _ => cases hconf
  | label _ => cases hconf
  | variant _ _ => cases hconf

/-- **Multi-Turn Live `Checkpoint` & Settled Snapshot Typing (`checkpointReachable_settled_typed`)**:
Refines `Checkpoint.frontier` and `Checkpoint.settled` directly against
`Obend.Core.Collect.typed_checkpoint` and `Obend.Core.Proofs.Preservation.typed_resume_preserved`
across arbitrary multi-turn `CheckpointReachable` traces (`world`, `dispatch`, `respond`,
`abandon`, `deepen`, `moreTicks`, `choose`). -/
public theorem checkpointReachable_settled_typed
    {assumptions : Obend.Core.Check.Assumptions} {types₀ : Obend.Core.MachineTyping.AddressTypes}
    {entryPlan entryResult : Obend.Core.Ty.Ty} {par₀ : Par} {ck : Checkpoint Tok Fact Ob V}
    (hInitTyped : Obend.Core.MachineTyping.StateTyping assumptions types₀ D.s₀
      (.computation entryPlan D.resp entryResult))
    (hInitActive : ∀ p, D.s₀.control ≠ .yielded p)
    (hRespTyped : ∀ r : Data, r.conforms D.resp = true →
      ∃ u, Obend.Core.Check.PartialTyping assumptions [] r.term D.resp u)
    (hReach : CheckpointReachable D host sp (Checkpoint.init D par₀) ck) :
    (∃ types, Nonempty (Obend.Core.MachineTyping.StateTyping assumptions types ck.frontier
      (.computation entryPlan D.resp entryResult))) ∧
    (∀ p, ck.frontier.control ≠ .yielded p) ∧
    (∃ types, Nonempty (Obend.Core.MachineTyping.StateTyping assumptions types ck.settled
      (.computation entryPlan D.resp entryResult))) ∧
    (∀ disp y, ck.inflight = some (disp, y) →
      (∃ plan, y.control = .yielded plan) ∧
      ∃ types, Nonempty (Obend.Core.MachineTyping.StateTyping assumptions types y
        (.computation entryPlan D.resp entryResult))) := by
  induction hReach with
  | init =>
    refine ⟨⟨types₀, ⟨hInitTyped⟩⟩, hInitActive,
      ⟨_, ⟨Obend.Core.Collect.typed_collect (Obend.Core.Collect.typed_settle hInitTyped)⟩⟩,
      fun _ _ h => by simp [Checkpoint.init] at h⟩
  | @step ck₁ ck₂ ev _ hStep ih =>
    obtain ⟨hFrontT, hFrontAct, hSetT, hInfT⟩ := ih
    cases ev with
    | world v' =>
      by_cases hw : host.allowed ck₁.world v' = true
      · have hck₂ : ck₂ = { ck₁ with world := v', log := ck₁.log.push (.world v') } := by
          simp only [stepCheckpoint, hw, ↓reduceIte, Except.ok.injEq] at hStep
          exact hStep.symm
        subst hck₂; exact ⟨hFrontT, hFrontAct, hSetT, hInfT⟩
      · simp [stepCheckpoint, hw] at hStep
    | abandon p =>
      cases hend : ck₁.ended with
      | some _ => simp [stepCheckpoint, hend] at hStep
      | none =>
        cases hinf : ck₁.inflight with
        | none => simp [stepCheckpoint, hend, hinf] at hStep
        | some xy =>
          rcases xy with ⟨o', y⟩
          by_cases hp : p = o'
          · subst hp
            have hck₂ : ck₂ = { ck₁ with ended := some p, log := ck₁.log.push (.abandon ⟨(), p⟩) } := by
              simp only [stepCheckpoint, hend, hinf, ↓reduceIte, Except.ok.injEq] at hStep
              simpa [hend, hinf] using hStep.symm
            subst hck₂; exact ⟨hFrontT, hFrontAct, hSetT, hInfT⟩
          · simp [stepCheckpoint, hend, hinf, hp] at hStep
    | deepen m =>
      simp only [stepCheckpoint, Except.ok.injEq] at hStep
      subst hStep; exact ⟨hFrontT, hFrontAct, hSetT, hInfT⟩
    | moreTicks m =>
      simp only [stepCheckpoint, Except.ok.injEq] at hStep
      subst hStep; exact ⟨hFrontT, hFrontAct, hSetT, hInfT⟩
    | choose q =>
      cases hinf : ck₁.inflight with
      | some _ => simp [stepCheckpoint, hinf] at hStep
      | none =>
        cases hcd : choiceDeadAt D host ck₁.world q with
        | cons _ _ => simp [stepCheckpoint, hinf, hcd] at hStep
        | nil =>
          cases hrem : ck₁.remDepth with
          | zero => simp [stepCheckpoint, hinf, hcd, hrem] at hStep
          | succ _ =>
            cases htf : turnFast D.L ck₁.par.ticks D.budget ck₁.frontier with
            | stop _ => simp [stepCheckpoint, hinf, hcd, hrem, htf] at hStep
            | vis rawPlan _ =>
              have hck₂ : ck₂ = { ck₁ with
                  par := { ck₁.par with choices := setChoice ck₁.par.choices ck₁.answered.size q } } := by
                cases ha : D.alts rawPlan with
                | none =>
                  by_cases hpq : rawPlan = q
                  · subst hpq
                    simp only [stepCheckpoint, hinf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                      hcd, hrem, htf, ha, decide_true, Except.ok.injEq] at hStep
                    simpa [hinf, hrem] using hStep.symm
                  · simp [stepCheckpoint, hinf, hcd, hrem, htf, ha, hpq] at hStep
                | some as =>
                  by_cases hmem : q ∈ as
                  · simp only [stepCheckpoint, hinf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                      hcd, hrem, htf, ha, hmem, decide_true, Except.ok.injEq] at hStep
                    simpa [hinf, hrem] using hStep.symm
                  · simp [stepCheckpoint, hinf, hcd, hrem, htf, ha, hmem] at hStep
              subst hck₂; exact ⟨hFrontT, hFrontAct, hSetT, hInfT⟩
    | dispatch p =>
      cases hg : choiceGuardCheckpoint D host ck₁ p with
      | cons _ _ => simp [stepCheckpoint, hg] at hStep
      | nil =>
        cases hend : ck₁.ended with
        | some _ => simp [stepCheckpoint, hg, hend] at hStep
        | none =>
          cases hinf : ck₁.inflight with
          | some _ => simp [stepCheckpoint, hg, hend, hinf] at hStep
          | none =>
            cases hrem : ck₁.remDepth with
            | zero => simp [stepCheckpoint, hg, hend, hinf, hrem] at hStep
            | succ n =>
              cases hturn : turn D.L ck₁.par.ticks D.budget ck₁.frontier with
              | stop _ => simp [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn] at hStep
              | vis rawPlan y =>
                cases hnext : nextPlanOf D.alts ck₁.par ck₁.answered.size rawPlan with
                | none => simp [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn, hnext] at hStep
                | some op =>
                  by_cases hp : p = op
                  · subst hp
                    by_cases hdg : dispatchGuard (i := ()) sp (View.maskArray (host.view ck₁.world) ck₁.spent) p = true
                    · have hck₂ : ck₂ = { ck₁ with
                          inflight := some (p, y)
                          settled := Obend.Core.Collect.checkpoint y
                          spent := pushConsumedTok ck₁.spent (sp.consumes (i := ()) p)
                          log := ck₁.log.push (.dispatch ⟨(), p⟩) } := by
                        simp only [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn, hnext,
                          hdg, ↓reduceIte, Except.ok.injEq] at hStep
                        simpa [hend, hrem] using hStep.symm
                      subst hck₂
                      unfold turn at hturn
                      cases hrunB : runBounded D.L ck₁.par.ticks ck₁.frontier with
                      | yielded planAddr y₀ =>
                        simp only [hrunB] at hturn
                        cases hyp : yieldedPlan D.L D.budget y₀ with
                        | error e => obtain ⟨_, _⟩ := e; simp [hyp] at hturn
                        | ok res =>
                          simp only [hyp, Turn.vis.injEq] at hturn
                          rcases hturn with ⟨_, rfl⟩
                          obtain ⟨typesF, ⟨hTF⟩⟩ := hFrontT
                          obtain ⟨typesY₀, _, ⟨hTY₀⟩⟩ :=
                            Obend.Core.Collect.typed_runBounded_any D.L ck₁.par.ticks typesF ck₁.frontier hTF
                          rw [hrunB] at hTY₀
                          dsimp only [Obend.Core.Collect.outcomeState] at hTY₀
                          have hOut : forcingShared y₀.stack = false :=
                            Obend.Core.Collect.runBounded_yields_outside D.L ck₁.par.ticks ck₁.frontier hFrontAct hrunB
                          have hChk := Obend.Core.Collect.typed_checkpoint hTY₀ hOut hyp
                          obtain ⟨typesRes, _, ⟨hTRes⟩⟩ :=
                            Obend.Core.Collect.typed_yieldedPlanWith hTY₀ hOut hyp
                          obtain ⟨aAddr, haCtrl⟩ := yieldedPlan_yielded hyp
                          have hCtrlEq := (Obend.Core.Collect.yieldedPlanWith_control hyp).1
                          refine ⟨⟨typesF, ⟨hTF⟩⟩, hFrontAct, hChk, fun disp y' hEq' => ?_⟩
                          simp only [Option.some.injEq, Prod.mk.injEq] at hEq'
                          rcases hEq' with ⟨rfl, rfl⟩
                          exact ⟨⟨aAddr, hCtrlEq.trans haCtrl⟩, ⟨typesRes, ⟨hTRes⟩⟩⟩
                      | finished _ _ => simp [hrunB] at hturn
                      | suspended _ _ => simp [hrunB] at hturn
                      | divergent _ _ => simp [hrunB] at hturn
                      | refused _ _ => simp [hrunB] at hturn
                    · simp [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn, hnext, hdg] at hStep
                  · simp [stepCheckpoint, hg, hend, hinf, hrem, turnFast_eq_turn, hturn, hnext, hp] at hStep
    | respond p r =>
      by_cases ht : typedReply D r = true
      · cases hend : ck₁.ended with
        | some _ => simp [stepCheckpoint, ht, hend] at hStep
        | none =>
          cases hinf : ck₁.inflight with
          | none => simp [stepCheckpoint, ht, hend, hinf] at hStep
          | some xy =>
            rcases xy with ⟨o', y⟩
            by_cases hp : p = o'
            · subst hp
              cases hres : resume r.term y with
              | none => simp [stepCheckpoint, ht, hend, hinf, hres] at hStep
              | some s' =>
                have hck₂ : ck₂ = { ck₁ with
                    frontier := s'
                    inflight := none
                    remDepth := ck₁.remDepth - 1
                    answered := ck₁.answered.push ⟨(), p, r⟩
                    log := ck₁.log.push (.respond ⟨(), p, r⟩) } := by
                  simp only [stepCheckpoint, ht, hend, hinf, hres, ↓reduceIte, Except.ok.injEq] at hStep
                  simpa [hend] using hStep.symm
                subst hck₂
                obtain ⟨⟨planAddr, hyCtrl⟩, ⟨typesY, ⟨hTY⟩⟩⟩ := hInfT p y hinf
                obtain ⟨u, hRT⟩ := hRespTyped r ht
                have hNextT :=
                  Obend.Core.Proofs.Preservation.typed_resume_preserved hTY hyCtrl hRT hres
                have hNextAct : ∀ q, s'.control ≠ .yielded q := by
                  obtain ⟨_, _, hc⟩ := resume_keeps_heap_and_stack r.term y s' hres
                  intro q hq; rw [hc] at hq; cases hq
                exact ⟨⟨typesY, hNextT⟩, hNextAct, hSetT, fun _ _ h => by simp at h⟩
            · simp [stepCheckpoint, ht, hend, hinf, hp] at hStep
      · simp [stepCheckpoint, ht] at hStep

end

end Obend.Run.Core4
