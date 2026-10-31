module
/-
# Obend.Run.Proofs.Core4 — a Core4 activity's turns are runner traces under `Legal`

- `transcript_of_reach` / `reach_of_transcript`: a path of the activity's protocol `unfold n s` IS a
  transcript of the machine's turns, and conversely; the residual is the activity resumed.
- `run_is_trace` (machine to runner): a transcript whose Plans are admitted at the world, each token
  spent once, is accepted event by event by the runner started at the activity; the history is the
  transcript, the residual the activity resumed, and the log `Legal`.
- `trace_is_run` (runner to machine): at every configuration the runner reaches from the activity,
  whatever the world and the proposals did, the log is `Legal`, the answered history is a
  transcript of the machine, the residual is the activity resumed after it, and the call in flight
  (if any) is the Plan the machine yields there.
-/
public import Obend.Run.Core4
public import Obend.Run.Proofs.Interpret
public import Obend.Core.Proofs.Force
public import Obend.AxiomPin
public import Obend.Tactic.Tooth
import all Obend.Core.Term
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Run.Core4
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Interpret
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping

namespace Obend.Run.Core4

open Obend.Slot.Protocol Obend.Core.Machine Obend.Core.Data

section
variable {L : Limits} {ticks : Nat} {budget : Budget}

theorem subst_nohole {A : Unit → Type} (σ : Subst planSig NoHole A) :
    ∀ {i : Unit} (P : Prot planSig NoHole A i), subst σ P = P
  | _, .ret _ => rfl
  | _, .call op k => by
    simp only [subst]
    congr 1
    funext r
    exact subst_nohole σ (k r)
  | _, .hole h => nomatch (h : Empty)

theorem yieldedPlan_yielded {y : State} {r : Result} (found : yieldedPlan L budget y = .ok r) :
    ∃ a, y.control = .yielded a := by
  unfold yieldedPlan yieldedPlanWith at found
  split at found
  · exact ⟨_, ‹_›⟩
  · simp at found

/-- The yielded state a turn hands back always takes a response. -/
public theorem turn_vis_resumes {s y : State} {p : Data} (h : turn L ticks budget s = .vis p y)
    (t : Obend.Core.Term.Term) : ∃ s', resume t y = some s' := by
  unfold turn at h
  split at h
  · rename_i y₀ _
    cases hf : yieldedPlan L budget y₀ with
    | error e => rw [hf] at h; obtain ⟨_, _⟩ := e; cases h
    | ok r =>
      rw [hf] at h
      cases h
      obtain ⟨a, ha⟩ := yieldedPlan_yielded hf
      have hc := (Obend.Core.Collect.yieldedPlanWith_control hf).1
      refine ⟨{ r.state with control := .evaluate t [] }, ?_⟩
      unfold resume
      rw [hc, ha]
  · cases h

theorem unfold_vis {s y : State} {p : Data} (h : turn L ticks budget s = .vis p y) (n : Nat) :
    unfold L ticks budget (n + 1) s = .call (S := planSig) p fun r =>
      match resume r.term y with
      | some s' => unfold L ticks budget n s'
      | none => .ret .unresumable := by
  simp only [unfold, h]
  rfl

/-- A transcript of the machine is a path of the activity's protocol. -/
public theorem reach_of_transcript {s s' : State} {t : Trace planSig}
    (ht : Transcript L ticks budget s t s') (m : Nat) :
    Reach (unfold L ticks budget (t.length + m) s) t ⟨(), unfold L ticks budget m s'⟩ := by
  induction ht with
  | nil s => simpa using Reach.here (unfold L ticks budget m s)
  | @turn s y s₁ s'' p r t hturn hres _ ih =>
    have e : (List.length (⟨(), p, r⟩ :: t) : Nat) + m = (t.length + m) + 1 := by simp; omega
    rw [e, unfold_vis hturn]
    refine Reach.call (S := planSig) r ?_
    simp only [hres]
    exact ih

/-- **A path of the activity's protocol is a transcript of the machine**, and the residual is the
activity resumed after it. -/
public theorem transcript_of_reach {t : Trace planSig} :
    ∀ {n : Nat} {s : State} {R : Σ j, Prot planSig NoHole (fun _ => Stop) j},
      Reach (unfold L ticks budget n s) t R →
      ∃ s' m, Transcript L ticks budget s t s' ∧ n = t.length + m ∧ R = ⟨(), unfold L ticks budget m s'⟩ := by
  induction t with
  | nil =>
    intro n s R hr
    have : ∀ {P : Prot planSig NoHole (fun _ => Stop) ()} {R}, Reach P [] R → R = ⟨(), P⟩ := by
      intro P R h; cases h; rfl
    rw [this hr]
    exact ⟨s, n, .nil s, by simp, rfl⟩
  | cons e t ih =>
    intro n s R hr
    cases n with
    | zero => simp only [unfold] at hr; cases hr
    | succ n =>
      cases ht : turn L ticks budget s with
      | stop x => simp only [unfold, ht] at hr; cases hr
      | vis p y =>
        rw [unfold_vis ht] at hr
        cases hr with
        | call r hr =>
          obtain ⟨s₁, hs₁⟩ := turn_vis_resumes ht r.term
          simp only [hs₁] at hr
          obtain ⟨s', m, htr, hn, hR⟩ := ih hr
          exact ⟨s', m, .turn ht hs₁ htr, by simp [hn]; omega, hR⟩

end

/-! ## Machine and runner -/

section
variable {Tok Fact Ob V : Type} [DecidableEq Tok]
variable {L : Limits} {ticks : Nat} {budget : Budget}

omit [DecidableEq Tok] in
theorem current_activity {Γ : List Fact} {Δ : List Tok} {Φ : List Ob} {n : Nat} {s : State}
    (σ : Subst planSig NoHole (fun _ => Stop)) :
    fill (activity (Ob := Ob) L ticks budget n s Γ Δ Φ).Ω σ (unfold L ticks budget n s) =
      unfold L ticks budget n s :=
  subst_nohole _ _

theorem session_of_transcript {host : Host V Tok Fact} {sp : Spec planSig Tok Fact Ob}
    {s s' : State} {t : Trace planSig} (ht : Transcript L ticks budget s t s') (m : Nat) :
    ∀ (c : Cfg planSig NoHole (fun _ => Stop) Tok Fact Ob V ()),
      c.res = ⟨(), unfold L ticks budget (t.length + m) s⟩ → c.obj.hist.inflight = none →
      c.ended = none → (∀ e ∈ t, admitOp sp (host.view c.world) e.2.1 = true) →
      (∀ tok ∈ consumed sp t, tok ∉ c.spent) → (consumed sp t).Nodup →
      (session host sp c (eventsOf t)).2 = List.replicate (2 * t.length) none ∧
        (session host sp c (eventsOf t)).1.obj.hist.answered = c.obj.hist.answered ++ t ∧
        (session host sp c (eventsOf t)).1.res = ⟨(), unfold L ticks budget m s'⟩ := by
  induction ht with
  | nil s => intro c hres _ _ _ _ _; exact ⟨rfl, by simp [session, eventsOf], by simpa [session, eventsOf] using hres⟩
  | @turn s y s₁ s'' p r t hturn hresume _ ih =>
    intro c hres hinf hlive hadm hfresh hnd
    have e : (List.length (⟨(), p, r⟩ :: t) : Nat) + m = (t.length + m) + 1 := by simp; omega
    rw [e, unfold_vis hturn] at hres
    have hcons : consumed sp (⟨(), p, r⟩ :: t) = (sp.consumes (i := ()) p).toList ++ consumed sp t := by
      simp only [consumed, List.filterMap_cons]
      cases sp.consumes p <;> rfl
    rw [hcons] at hfresh hnd
    have hadm0 := hadm ⟨(), p, r⟩ List.mem_cons_self
    have hmask : admitOp (i := ()) sp (c.admitView host) p = true := by
      simp only [admitOp, Cfg.admitView, View.mask] at hadm0 ⊢
      cases hc : sp.consumes p with
      | none => simpa [hc] using hadm0
      | some tok =>
        simp only [hc, Bool.and_eq_true] at hadm0 ⊢
        refine ⟨hadm0.1, hadm0.2, ?_⟩
        simpa using hfresh tok (by simp [hc])
    obtain ⟨c₁, c₂, h1, h2, hres₂, hhist, hlive₂, hworld, hspent, _, _, _⟩ :=
      dispatch_respond (r := r) hres hlive hinf hmask
        (decisionDead_nil _ _ _ fun _ h => nomatch (h : Empty))
    have hres₂' : c₂.res = ⟨(), unfold L ticks budget (t.length + m) s₁⟩ := by
      rw [hres₂]; simp only [hresume]
    obtain ⟨hs, ha, hr⟩ := ih c₂ hres₂' (by rw [hhist]) hlive₂
      (fun e he => by rw [hworld]; exact hadm e (List.mem_cons_of_mem _ he))
      (fun tok htok hmem => by
        rw [hspent] at hmem
        rcases List.mem_append.mp hmem with hm | hm
        · exact hfresh tok (List.mem_append_right _ htok) hm
        · exact (List.nodup_append.mp hnd).2.2 tok hm tok htok rfl)
      (List.nodup_append.mp hnd).2.1
    simp only [eventsOf, session, h1, h2]
    refine ⟨?_, ?_, hr⟩
    · simp only [hs]
      show none :: none :: List.replicate (2 * t.length) none = List.replicate (2 * (t.length + 1)) none
      rw [show 2 * (t.length + 1) = 2 * t.length + 1 + 1 by omega]
      rfl
    · rw [ha, hhist]; simp

/-- **Machine to runner**: a transcript of the activity whose Plans are admitted at the world and
which spends each token once is a runner trace: every event is accepted, the history is the
transcript, the residual is the activity resumed after it, and the log is `Legal`. -/
public theorem run_is_trace {host : Host V Tok Fact} {sp : Spec planSig Tok Fact Ob}
    {Γ : List Fact} {Δ : List Tok} {Φ : List Ob} {s₀ s' : State} {t : Trace planSig} (m : Nat)
    (v₀ : V) (ht : Transcript L ticks budget s₀ t s')
    (hadm : ∀ e ∈ t, admitOp sp (host.view v₀) e.2.1 = true) (hnd : (consumed sp t).Nodup) :
    let O := activity L ticks budget (t.length + m) s₀ Γ Δ Φ
    let c := session host sp (Cfg.init O v₀) (eventsOf t)
    c.2 = List.replicate (2 * t.length) none ∧ c.1.obj.hist.answered = t ∧
      c.1.res = ⟨(), unfold L ticks budget m s'⟩ ∧ Legal host sp O v₀ c.1.log := by
  intro O c
  obtain ⟨h1, h2, h3⟩ := session_of_transcript (host := host) ht m (Cfg.init O v₀)
    (congrArg (Sigma.mk ()) (subst_nohole _ _)) rfl rfl hadm
    (fun _ _ h => by cases h) hnd
  exact ⟨h1, h2.trans (List.nil_append t), h3, reachable_legal (session_reachable .init _)⟩

/-- **Runner to machine**: at every configuration the runner reaches from the activity (any world
moves, any proposals, accepted or refused), the log is `Legal`; the answered history is a transcript
of the machine; the residual is the activity resumed after it; the call in flight is the Plan the
machine yields there. The runner exposes no Plan the program did not yield. -/
public theorem trace_is_run {host : Host V Tok Fact} {sp : Spec planSig Tok Fact Ob}
    {Γ : List Fact} {Δ : List Tok} {Φ : List Ob} {n : Nat} {s₀ : State} {v₀ : V}
    {c : Cfg planSig NoHole (fun _ => Stop) Tok Fact Ob V ()}
    (hc : Reachable host sp (Cfg.init (activity L ticks budget n s₀ Γ Δ Φ) v₀) c) :
    Legal host sp (activity L ticks budget n s₀ Γ Δ Φ) v₀ c.log ∧
      ∃ s' m, Transcript L ticks budget s₀ c.obj.hist.answered s' ∧
        n = c.obj.hist.answered.length + m ∧ c.res = ⟨(), unfold L ticks budget m s'⟩ ∧
        ∀ o, c.obj.hist.inflight = some o → ∃ y, turn L ticks budget s' = .vis o.2 y := by
  have hI := refines hc
  refine ⟨hI.legal, ?_⟩
  have hr := hI.residual
  have hcur : c.obj.current = unfold L ticks budget n s₀ := by
    show fill c.obj.Ω c.obj.σ c.obj.template = _
    rw [hI.obj]
    exact subst_nohole _ _
  rw [hcur] at hr
  obtain ⟨s', m, htr, hn, hR⟩ := transcript_of_reach hr
  refine ⟨s', m, htr, hn, hR, fun o ho => ?_⟩
  have hcall := hI.next o ho
  rw [hR] at hcall
  cases m with
  | zero => simp [unfold, IsCall] at hcall
  | succ m =>
    cases ht : turn L ticks budget s' with
    | stop x => simp [unfold, ht, IsCall] at hcall
    | vis p y =>
      rw [unfold_vis ht] at hcall
      obtain ⟨_, o⟩ := o
      simp only [IsCall] at hcall
      cases hcall
      exact ⟨y, rfl⟩

#tooth session_of_transcript by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => false

#assert_axioms turn_vis_resumes reach_of_transcript transcript_of_reach run_is_trace trace_is_run

end

end Obend.Run.Core4
