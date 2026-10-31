module
/-
# Obend.Run.Proofs.Shared — the composition layer's theorems

At every joint configuration reachable from the start (`JInv`, `jreachable_inv`):

- `jreachable_fold`: the joint run is a run of the family `members` (the ledger and every runner,
  `Obend.Fold.Family.step`): the rows each joint transition adds fold from the start to the joint
  configuration, and each runner's log is exactly what `Obend.Fold.projectMoves` hands it of them.
- `joint_reachable_projects_legal`: each runner's own log is `Legal` for its own object at its
  local host: `Obend.Fold.project_moves_run` applied to the joint fold, read through
  `legal_iff_admission` (the one clause not per row, `Kept`, is the runner's own). The rely–guarantee
  condition is discharged once by the ledger's laws (`members_guarantee`). Its `Authorized` clause is
  the headline "every exposure was admitted at the shared view": the local host IS the shared view.
- `joint_ledger_fold`: the same theorem at the ledger member: its own rows fold from the start, so
  every commit it made was of a token not yet consumed.
- `joint_reachable_ticket_exclusive`: no token is granted twice, and the ledger's consumption is
  exactly its grants.
- `joint_once`: `OnceSpent` globally: a token spent by two runners' logs was spent by one runner.
- `joint_coupled`: every runner's world is the ledger (the projection relation).
- `loser_refused_names_winner_and_epoch`: a runner whose next call needs a token another runner
  holds is refused, naming the winner and the epoch of its grant.

None of these assumes global once-spending: it is derived from each runner's own admission at the
shared mask (`sharedLive`) and the ledger's commit laws. Durability (an abandonment releases
nothing) is a field of `Ledger`, so no theorem takes it as a hypothesis.
-/
public import Obend.Run.Shared
public import Obend.Run.Proofs.Control
public import Obend.Tactic.Tooth
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Run.Control
import all Obend.Run.Shared
import all Obend.Run.Fold
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Control

namespace Obend.Run.Shared

open Obend.Slot Obend.Slot.Protocol Obend.Run.Control

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type} {Tok Fact Ob V : Type}
variable [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok] [DecidableEq (Σ i, S.Op i)]

/-- An accepted runner event is appended to the log; only a world event moves the world. -/
theorem run_basic {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {e : Event S Hole A Fact V}
    (hr : run host sp c e = .ok c') :
    c'.log = c.log ++ [e] ∧ c'.world = (match e with | .world v => v | _ => c.world) := by
  cases e with
  | replan h f fs =>
    obtain ⟨_, _, _, _, hw, _, hl, _⟩ := run_replan_inv hr
    exact ⟨hl, hw⟩
  | world v =>
    simp only [run] at hr
    split at hr
    · cases hr; exact ⟨rfl, rfl⟩
    · cases hr
  | dispatch o =>
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | (cases hr; subst_vars; exact ⟨rfl, rfl⟩)
  | respond r =>
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | (cases hr; exact ⟨rfl, rfl⟩)
  | abandon o =>
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | (cases hr; exact ⟨rfl, rfl⟩)

/-- An accepted dispatch was admitted at the configuration's view. -/
theorem run_dispatch_admitted {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {o : Σ i, S.Op i}
    (hr : run host sp c (.dispatch o) = .ok c') : admitOp sp (c.admitView host) o.2 = true := by
  simp only [run] at hr
  repeat' split at hr
  all_goals first
    | (cases hr; done)
    | (rename_i hg _; cases hr; subst_vars; exact hg)
    | skip
  all_goals (subst_vars; assumption)

omit [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq (Σ i, S.Op i)] in
theorem spentBy_snoc_ev (sp : Spec S Tok Fact Ob) (l : List (Event S Hole A Fact V)) (e : Event S Hole A Fact V) :
    spentBy sp (l ++ [e]) = spentBy sp l ++ match e with
      | .dispatch o => (sp.consumes o.2).toList
      | _ => [] := by
  unfold spentBy; rw [List.filterMap_append]; congr 1; cases e <;> simp [List.filterMap_cons]
  cases sp.consumes _ <;> rfl

end

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable {ι P Cred Cand Tok Fact Ob W : Type}
variable [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
variable {L : Ledger ι W Tok} {base : W → View Tok Fact} {sp : ι → Spec S Tok Fact Ob}
variable {au : ι → Authority P Cred} {k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j}

/-- A controlled world event. -/
theorem crun_world {host : Host V Tok Fact} {sp' : Spec S Tok Fact Ob} {au' : Authority P Cred}
    {k' : (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j} {i₀ : Ix}
    {c c' : CCfg S Hole A P Cand Tok Fact Ob V i₀} {v : V}
    (hr : crun host sp' au' k' c (.base (.world v)) = .ok c') :
    c'.cfg.log = c.cfg.log ++ [.world v] ∧ c'.cfg.world = v ∧ c'.decisions = c.decisions := by
  obtain ⟨hrun, _, _, hd, _⟩ := crun_base_ok hr
  exact ⟨(run_basic hrun).1, (run_basic hrun).2, hd⟩

/-- A controlled world event the host allows is accepted. -/
theorem crun_world_ok {host : Host V Tok Fact} {sp' : Spec S Tok Fact Ob} {au' : Authority P Cred}
    {k' : (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j} {i₀ : Ix}
    (c : CCfg S Hole A P Cand Tok Fact Ob V i₀) {v : V} (ha : host.allowed c.cfg.world v = true) :
    ∃ c', crun host sp' au' k' c (.base (.world v)) = .ok c' := by
  simp only [crun, run, ha, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- What holds at every joint configuration. -/
public structure JInv (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}
    (d₀ : L.Rec) (O : ι → Open S Hole A Tok Fact Ob i₀) (stored₀ : ι → (j : Ix) → Hole j → Option Cand)
    (J : JCfg L S Hole A P Cand Fact Ob i₀) : Prop where
  reach : ∀ i, CReachable (localHost L base) (sp i) (au i) (k i)
    (CCfg.init (Cfg.init (O i) d₀) (stored₀ i)) (J.cfgs i)
  coupled : ∀ i, (J.cfgs i).cfg.world = J.led
  spent_grants : L.spent J.led = (L.grants J.led).map Grant.tok
  nodup : ((L.grants J.led).map Grant.tok).Nodup
  local_spent : ∀ i, spentBy (sp i) (J.cfgs i).cfg.log =
    ((L.grants J.led).filter fun g => decide (g.winner = i)).map Grant.tok

omit [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)] in
theorem ledgerStep_raw {d d' : L.Rec} {w : W} (h : ledgerStep L d (.raw w) = .ok d') :
    L.stepRaw (L.raw d) w = true ∧ d' = L.setRaw d w := by
  simp only [ledgerStep] at h; split at h
  · cases h; exact ⟨(by assumption), rfl⟩
  · cases h

omit [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)] in
theorem ledgerStep_abandon {d d' : L.Rec} {i : ι} (h : ledgerStep L d (.abandon i) = .ok d') :
    d' = L.onAbandon d i := by
  simp only [ledgerStep] at h; cases h; rfl

omit [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)] in
theorem ledgerStep_rowOf {sp' : Spec S Tok Fact Ob} {d d' : L.Rec} {i : ι} {o : Σ i, S.Op i}
    (h : ledgerStep L d (ledgerRowOf L sp' d i o) = .ok d') :
    (∀ t, sp'.consumes o.2 = some t → d' = L.commit d i t) ∧ (sp'.consumes o.2 = none → d' = d) := by
  unfold ledgerRowOf at h
  split at h
  · rename_i t ht
    simp only [ledgerStep] at h; split at h
    · split at h <;> cases h
    · cases h; exact ⟨fun t' ht' => (by rw [ht] at ht'; cases ht'; rfl), fun hn => (by rw [ht] at hn; cases hn)⟩
  · rename_i hn
    simp only [ledgerStep] at h; split at h
    · cases h; exact ⟨fun t ht => (by rw [hn] at ht; cases ht), fun _ => rfl⟩
    · cases h

/-- Propagating an allowed move of the ledger to coupled runners: each takes the world event. -/
theorem propagate_ok {i₀ : Ix} {d₀ : L.Rec} {O : ι → Open S Hole A Tok Fact Ob i₀}
    {stored₀ : ι → (j : Ix) → Hole j → Option Cand}
    (cs : ι → CCfg S Hole A P Cand Tok Fact Ob L.Rec i₀) (d d' : L.Rec)
    (hreach : ∀ i, CReachable (localHost L base) (sp i) (au i) (k i)
      (CCfg.init (Cfg.init (O i) d₀) (stored₀ i)) (cs i))
    (hc : ∀ i, (cs i).cfg.world = d) (ha : L.allowed d d' = true) :
    ∀ i, CReachable (localHost L base) (sp i) (au i) (k i)
        (CCfg.init (Cfg.init (O i) d₀) (stored₀ i)) (propagate L base sp au k d' cs i) ∧
      (propagate L base sp au k d' cs i).cfg.world = d' ∧
      (propagate L base sp au k d' cs i).cfg.log = (cs i).cfg.log ++ [.world d'] := by
  intro i
  have hal : (localHost L base).allowed (cs i).cfg.world d' = true := by
    show L.allowed _ _ = true; rw [hc i]; exact ha
  obtain ⟨c', hc'⟩ := crun_world_ok (sp' := sp i) (au' := au i) (k' := k i) (cs i) hal
  have hp : propagate L base sp au k d' cs i = c' := by
    simp only [propagate, hc']
  rw [hp]
  obtain ⟨hl, hw, _⟩ := crun_world hc'
  exact ⟨.step _ (hreach i) hc', hw, hl⟩

theorem setCfg_same {W' : Type} {i₀ : Ix} (cs : ι → CCfg S Hole A P Cand Tok Fact Ob W' i₀) (i : ι) (c) :
    setCfg cs i c i = c := by simp [setCfg]

theorem setCfg_ne {W' : Type} {i₀ : Ix} (cs : ι → CCfg S Hole A P Cand Tok Fact Ob W' i₀) {i j : ι} (c) (h : j ≠ i) :
    setCfg cs i c j = cs j := by simp [setCfg, h]

theorem filter_snoc_grant (gs : List (Grant ι Tok)) (g : Grant ι Tok) (i : ι) :
    ((gs ++ [g]).filter fun g => decide (g.winner = i)).map Grant.tok =
      ((gs.filter fun g => decide (g.winner = i)).map Grant.tok) ++ (if g.winner = i then [g.tok] else []) := by
  rw [List.filter_append, List.map_append]
  by_cases h : g.winner = i <;> simp [h]

/-- A joint session ends at a joint-reachable configuration. -/
public theorem jsession_reachable {i₀ : Ix} {J₀ J : JCfg L S Hole A P Cand Fact Ob i₀}
    (hJ : JReachable L base sp au k J₀ J) (evs : List (JEvent ι W S Hole A P Cred Cand Fact L.Rec)) :
    JReachable L base sp au k J₀ (jsession L base sp au k J evs).1 := by
  induction evs generalizing J with
  | nil => exact hJ
  | cons ev evs ih =>
    simp only [jsession]
    cases h : jrun L base sp au k J ev with
    | ok J' => exact ih (.step ev hJ h)
    | error w => exact ih hJ

/-- **The joint invariant holds at every reachable joint configuration.** -/
public theorem jreachable_inv {i₀ : Ix} {d₀ : L.Rec} {O : ι → Open S Hole A Tok Fact Ob i₀}
    {stored₀ : ι → (j : Ix) → Hole j → Option Cand} (hs₀ : L.spent d₀ = []) (hg₀ : L.grants d₀ = [])
    {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) :
    JInv L base sp au k d₀ O stored₀ J := by
  induction h with
  | init =>
    refine ⟨fun _ => .init, fun _ => rfl, ?_, ?_, fun _ => ?_⟩
    · show L.spent d₀ = (L.grants d₀).map Grant.tok; rw [hs₀, hg₀]; rfl
    · show ((L.grants d₀).map Grant.tok).Nodup; rw [hg₀]; exact List.nodup_nil
    · show spentBy _ [] = ((L.grants d₀).filter _).map Grant.tok; rw [hg₀]; rfl
  | @step J J' ev _ hs ih =>
    cases ev with
    | world w =>
      simp only [jrun] at hs
      split at hs
      · rename_i d hd
        cases hs
        obtain ⟨hstep, rfl⟩ := ledgerStep_raw hd
        have hp := propagate_ok (O := O) (stored₀ := stored₀) J.cfgs J.led (L.setRaw J.led w) ih.reach ih.coupled
          (L.allowed_setRaw _ _ hstep)
        refine ⟨fun i => (hp i).1, fun i => (hp i).2.1, ?_, ?_, fun i => ?_⟩
        · rw [L.setRaw_spent, L.setRaw_grants]; exact ih.spent_grants
        · rw [L.setRaw_grants]; exact ih.nodup
        · rw [(hp i).2.2, spentBy_snoc_ev, L.setRaw_grants, ih.local_spent i]; simp
      · cases hs
    | abandon i o =>
      simp only [jrun] at hs
      split at hs
      · rename_i c₁ hc₁
        split at hs
        rotate_left
        · cases hs
        rename_i d hd
        cases hs
        have hdd := ledgerStep_abandon hd; subst hdd
        obtain ⟨hrun, _, _, _, _⟩ := crun_base_ok hc₁
        obtain ⟨hl₁, hw₁⟩ := run_basic hrun
        have hreach' : ∀ j, CReachable (localHost L base) (sp j) (au j) (k j)
            (CCfg.init (Cfg.init (O j) d₀) (stored₀ j)) (setCfg J.cfgs i c₁ j) := by
          intro j; by_cases e : j = i
          · subst e; rw [setCfg_same]; exact .step _ (ih.reach j) hc₁
          · rw [setCfg_ne _ _ e]; exact ih.reach j
        have hcoup : ∀ j, (setCfg J.cfgs i c₁ j).cfg.world = J.led := by
          intro j; by_cases e : j = i
          · subst e; rw [setCfg_same, hw₁]; exact ih.coupled j
          · rw [setCfg_ne _ _ e]; exact ih.coupled j
        have hp := propagate_ok (O := O) (stored₀ := stored₀) (setCfg J.cfgs i c₁) J.led (L.onAbandon J.led i)
          hreach' hcoup (L.allowed_onAbandon _ _)
        refine ⟨fun j => (hp j).1, fun j => (hp j).2.1, ?_, ?_, fun j => ?_⟩
        · rw [L.abandon_spent, L.abandon_grants]; exact ih.spent_grants
        · rw [L.abandon_grants]; exact ih.nodup
        · rw [(hp j).2.2, spentBy_snoc_ev, L.abandon_grants]
          by_cases e : j = i
          · subst e; rw [setCfg_same, hl₁, spentBy_snoc_ev, ih.local_spent j]; simp
          · rw [setCfg_ne _ _ e, ih.local_spent j]; simp
      · cases hs
    | own i ev =>
      simp only [jrun] at hs
      split at hs
      · cases hs
      · cases hs
      · cases hs
      · rename_i hnw hnd hna
        split at hs
        · rename_i c₁ hc₁
          cases hs
          -- the runner's events here are replies and decisions: no dispatch, no world move
          have hstep : (c₁.cfg = (J.cfgs i).cfg) ∨ ∃ e, (∀ v, e ≠ .world v) ∧ (∀ o, e ≠ .dispatch o) ∧
              run (localHost L base) (sp i) (J.cfgs i).cfg e = .ok c₁.cfg := by
            cases ev with
            | base e =>
              refine .inr ⟨e, fun v he => hnw v (by rw [he]), fun o he => hnd o (by rw [he]), (crun_base_ok hc₁).1⟩
            | advance h =>
              rcases crun_advance_ok hc₁ with he | ⟨cand, _, hi⟩
              · exact .inl (by rw [he])
              · exact .inr ⟨_, (fun _ e => by cases e), (fun _ e => by cases e), (install_ok hi).1⟩
            | choose p cred h cand e =>
              obtain ⟨_, _, _, _, _, hi⟩ := crun_choose_ok hc₁
              exact .inr ⟨_, (fun _ e => by cases e), (fun _ e => by cases e), (install_ok hi).1⟩
          have hsame : c₁.cfg.world = (J.cfgs i).cfg.world ∧
              spentBy (sp i) c₁.cfg.log = spentBy (sp i) (J.cfgs i).cfg.log := by
            rcases hstep with he | ⟨e, hw, hd, hrun⟩
            · rw [he]; exact ⟨rfl, rfl⟩
            · obtain ⟨hl, hwld⟩ := run_basic hrun
              refine ⟨?_, ?_⟩
              · rw [hwld]; cases e <;> first | rfl | exact absurd rfl (hw _)
              · rw [hl, spentBy_snoc_ev]
                cases e with
                | dispatch o => exact absurd rfl (hd o)
                | _ => simp
          refine ⟨fun j => ?_, fun j => ?_, ih.spent_grants, ih.nodup, fun j => ?_⟩
          · by_cases e : j = i
            · subst e; show CReachable _ _ _ _ _ (setCfg J.cfgs j c₁ j); rw [setCfg_same]; exact .step _ (ih.reach j) hc₁
            · show CReachable _ _ _ _ _ (setCfg J.cfgs i c₁ j); rw [setCfg_ne _ _ e]; exact ih.reach j
          · by_cases e : j = i
            · subst e; show (setCfg J.cfgs j c₁ j).cfg.world = J.led; rw [setCfg_same, hsame.1]; exact ih.coupled j
            · show (setCfg J.cfgs i c₁ j).cfg.world = J.led; rw [setCfg_ne _ _ e]; exact ih.coupled j
          · by_cases e : j = i
            · subst e; show spentBy _ (setCfg J.cfgs j c₁ j).cfg.log = _; rw [setCfg_same, hsame.2]; exact ih.local_spent j
            · show spentBy _ (setCfg J.cfgs i c₁ j).cfg.log = _; rw [setCfg_ne _ _ e]; exact ih.local_spent j
        · cases hs
    | dispatch i o =>
      simp only [jrun] at hs
      split at hs
      · rename_i c₂ hc₂
        split at hs
        rotate_left
        · cases hs
        rename_i d hd
        cases hs
        obtain ⟨hrun, _, _, _, _⟩ := crun_base_ok hc₂
        obtain ⟨hl₂, hw₂⟩ := run_basic hrun
        have hadm := run_dispatch_admitted hrun
        have hreach' : ∀ j, CReachable (localHost L base) (sp j) (au j) (k j)
            (CCfg.init (Cfg.init (O j) d₀) (stored₀ j)) (setCfg J.cfgs i c₂ j) := by
          intro j; by_cases e : j = i
          · subst e; rw [setCfg_same]; exact .step _ (ih.reach j) hc₂
          · rw [setCfg_ne _ _ e]; exact ih.reach j
        have hcoup : ∀ j, (setCfg J.cfgs i c₂ j).cfg.world = J.led := by
          intro j; by_cases e : j = i
          · subst e; rw [setCfg_same, hw₂]; exact ih.coupled j
          · rw [setCfg_ne _ _ e]; exact ih.coupled j
        -- the token, if any, was live at the shared mask: not yet consumed
        have hfresh : ∀ t, (sp i).consumes o.2 = some t → t ∉ L.spent J.led := by
          intro t ht hm
          simp only [admitOp, Cfg.admitView, View.mask, localHost, ht, Bool.and_eq_true] at hadm
          have := hadm.2.1
          simp only [sharedLive, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
          rw [ih.coupled i] at this
          exact this.2 hm
        have hall := ledgerStep_allowed L hd
        obtain ⟨hdc, hdn⟩ := ledgerStep_rowOf hd
        have hp := propagate_ok (O := O) (stored₀ := stored₀) (setCfg J.cfgs i c₂) J.led d hreach' hcoup hall
        refine ⟨fun j => (hp j).1, fun j => (hp j).2.1, ?_, ?_, fun j => ?_⟩
        · cases ht : (sp i).consumes o.2 with
          | some t => rw [hdc t ht, L.commit_spent, L.commit_grants, ih.spent_grants]; simp
          | none => rw [hdn ht]; exact ih.spent_grants
        · cases ht : (sp i).consumes o.2 with
          | some t =>
            rw [hdc t ht, L.commit_grants, List.map_append, List.nodup_append]
            refine ⟨ih.nodup, by simp, ?_⟩
            intro a ha b hb e
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            subst hb; subst e
            exact hfresh a ht (by rw [ih.spent_grants]; exact ha)
          | none => rw [hdn ht]; exact ih.nodup
        · rw [(hp j).2.2, spentBy_snoc_ev]
          simp only [List.append_nil]
          by_cases e : j = i
          · subst e
            rw [setCfg_same, hl₂, spentBy_snoc_ev, ih.local_spent j]
            cases ht : (sp j).consumes o.2 with
            | some t => rw [hdc t ht, L.commit_grants, filter_snoc_grant]; simp [ht]
            | none => rw [hdn ht]; simp [ht]
          · rw [setCfg_ne _ _ e, ih.local_spent j]
            cases ht : (sp i).consumes o.2 with
            | some t => rw [hdc t ht, L.commit_grants, filter_snoc_grant]; simp [Ne.symm e]
            | none => rw [hdn ht]
      · split at hs <;> cases hs
      · cases hs

theorem nodup_map_inj {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b
  | [], _, a, ha, _, _, _ => by cases ha
  | x :: t, h, a, ha, b, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (e ▸ List.mem_map.2 ⟨b, hb', rfl⟩) h.1
    · exact absurd (e.symm ▸ List.mem_map.2 ⟨a, ha', rfl⟩) h.1
    · exact nodup_map_inj h.2 a ha' b hb' e

/-! ## The members' family -/

omit [DecidableEq ι] [DecidableEq Cand] in
theorem rest_world_snoc {V' : Type} (sp' : Spec S Tok Fact Ob) (σ : Subst S Hole A) (v₀ : V')
    (cs₀ : (j : Ix) → Hole j → List Fact) (l : List (Event S Hole A Fact V')) (v : V') :
    (accOf sp' σ v₀ cs₀ (l ++ [.world v])).rest = (accOf sp' σ v₀ cs₀ l).rest := by
  simp only [accOf, Acc.rest, spentBy_snoc, histOf_snoc', endedOf_snoc, planOf_snoc, citesOf_snoc,
    List.append_nil]

omit [DecidableEq ι] [DecidableEq Cand] in
/-- A `Legal` log's last row is accepted by the fold's step at the accumulator of its prefix. -/
theorem legal_snoc_step {V' : Type} {host : Host V' Tok Fact} {sp' : Spec S Tok Fact Ob} {i : Ix}
    {O' : Open S Hole A Tok Fact Ob i} {v₀ : V'} {cs₀ : (j : Ix) → Hole j → List Fact}
    {log : List (Event S Hole A Fact V')} {e : Event S Hole A Fact V'}
    (h : Legal host sp' O' v₀ cs₀ (log ++ [e])) :
    Obend.Run.step host sp' O'.template (accOf sp' O'.σ v₀ cs₀ log) e = .ok (accOf sp' O'.σ v₀ cs₀ (log ++ [e])) := by
  obtain ⟨hrows, _⟩ := (legal_iff_rows host sp' O' v₀ cs₀ _).1 h
  obtain ⟨_, hr⟩ := AtEach.snoc.1 hrows
  exact (step_accOf host sp' O' v₀ cs₀ log e _).2 ⟨hr, rfl⟩

omit [DecidableEq ι] [DecidableEq Cand] in
/-- A runner's row that does not move the world, accepted by its runner, is accepted by its member
at the shared record. -/
theorem member_run_step {i₀ : Ix} {O : ι → Open S Hole A Tok Fact Ob i₀} {d₀ : L.Rec} {i : ι}
    {log : List (Event S Hole A Fact L.Rec)} {e : Event S Hole A Fact L.Rec} (he : e.isWorld = false)
    (hleg : Legal (localHost L base) (sp i) (O i) d₀ (fun _ _ => []) (log ++ [e])) :
    (members L base sp O (.run i)).step (worldOf d₀ log, (accOf (sp i) (O i).σ d₀ (fun _ _ => []) log).rest) e =
      .ok (worldOf d₀ log, (accOf (sp i) (O i).σ d₀ (fun _ _ => []) (log ++ [e])).rest) := by
  have h := legal_snoc_step hleg
  show (Obend.Run.step _ _ _ (Acc.ofPair _ _) e).map Acc.toPair = _
  have hpair : Acc.ofPair (worldOf d₀ log) (accOf (sp i) (O i).σ d₀ (fun _ _ => []) log).rest =
      accOf (sp i) (O i).σ d₀ (fun _ _ => []) log := rfl
  rw [hpair, h]
  simp only [Except.map, Acc.toPair]
  have hw : (accOf (sp i) (O i).σ d₀ (fun _ _ => []) (log ++ [e])).world = worldOf d₀ log := by
    show worldOf d₀ (log ++ [e]) = _
    rw [worldOf_snoc]; cases e <;> simp_all [Event.isWorld]
  rw [hw]

omit [DecidableEq Cand] in
/-- **The rely–guarantee condition holds of the members**: every member allows what the ledger
allows, and every move a member makes (a ledger row, a runner's world row) is one the ledger allows. -/
public theorem members_guarantee {i₀ : Ix} (O : ι → Open S Hole A Tok Fact Ob i₀) :
    Obend.Fold.GuaranteeMoves (members L base sp O) := by
  intro m m' _ a r b hm hs
  have hal : ∀ (m : Mem ι) (x y : L.Rec), (members L base sp O m).allowed x y = L.allowed x y := by
    intro m; cases m <;> intro x y <;> rfl
  rw [hal]
  cases m' with
  | ledger =>
    change (ledgerStep L a.1 r).map (fun d => (d, ())) = _ at hs
    cases hl : ledgerStep L a.1 r with
    | error c => rw [hl] at hs; cases hs
    | ok d => rw [hl] at hs; cases hs; exact ledgerStep_allowed L hl
  | run i =>
    change (Obend.Run.step _ _ _ (Acc.ofPair a.1 a.2) r).map Acc.toPair = _ at hs
    cases r with
    | world v =>
      rw [step_world] at hs
      split at hs
      · rename_i hv; cases hs; exact hv
      · cases hs
    | _ => cases hm

omit [DecidableEq ι] [DecidableEq Cand] in
theorem ledger_member_step {i₀ : Ix} (O : ι → Open S Hole A Tok Fact Ob i₀) (x : L.Rec) (u : Unit)
    (r : LRow ι W Tok L.Rec) :
    (members L base sp O Mem.ledger).step (x, u) r = (ledgerStep L x r).map (fun d => (d, ())) := rfl

omit [DecidableEq Cand] in
theorem mrestOf_congr {i₀ : Ix} {O : ι → Open S Hole A Tok Fact Ob i₀} {d₀ : L.Rec}
    {J₁ J₂ : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : ∀ i, (accOf (sp i) (O i).σ d₀ (fun _ _ => []) (J₂.cfgs i).cfg.log).rest =
      (accOf (sp i) (O i).σ d₀ (fun _ _ => []) (J₁.cfgs i).cfg.log).rest)
    (m : Mem ι) : mrestOf sp O d₀ J₂ m = mrestOf sp O d₀ J₁ m := by
  cases m with
  | ledger => rfl
  | run i => exact h i

omit [DecidableEq Cand] in
/-- What runner `k` sees of a runner row followed by a ledger row: its own row if it is the runner's,
then the ledger's new record. -/
theorem project_pair {i₀ : Ix} {O : ι → Open S Hole A Tok Fact Ob i₀} {s₀ s₁ s₂ : L.Rec × ((m : Mem ι) → MRest ι S Hole A Tok Fact m)}
    {i : ι} {e : Event S Hole A Fact L.Rec} {r : LRow ι W Tok L.Rec} (he : e.isWorld = false)
    (h₁ : Obend.Fold.Family.step (members L base sp O) s₀ ⟨.run i, e⟩ = .ok s₁)
    (h₂ : Obend.Fold.Family.step (members L base sp O) s₁ ⟨.ledger, r⟩ = .ok s₂) (k : ι) :
    Obend.Fold.projectMoves (members L base sp O) (.run k) s₀ [⟨.run i, e⟩, ⟨.ledger, r⟩] =
      (if k = i then [e] else []) ++ [.world s₂.1] := by
  have hm₁ : (members L base sp O (.run i)).moves e = false := he
  have hm₂ : (members L base sp O .ledger).moves r = true := rfl
  simp only [Obend.Fold.projectMoves, h₁, h₂, hm₁, hm₂]
  by_cases hk : k = i
  · subst hk; simp; rfl
  · have : ¬ (Mem.run i = Mem.run k) := fun h => hk (by cases h; rfl)
    simp only [this, ↓reduceDIte, hk, ↓reduceIte, reduceCtorEq]
    rfl

/-! ## Receipts of a member's row, dated by the ledger's committed view -/

omit [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)] in
theorem viewReading_coherent (keys : List (Fact ⊕ Tok)) :
    (viewReading L base keys).Coherent (Obend.Run.hostLook (localHost L base)) := by
  intro d k
  show ((if Obend.Run.hostLook (localHost L base) d k then 1 else 0) == 1) = _
  cases Obend.Run.hostLook (localHost L base) d k <;> rfl

omit [DecidableEq Cand] in
/-- **A receipt of a runner's row at the ledger's record passes the stranger's checks**: issued under
the naming of the ledger's committed view, every opening opens against the dated root and is the bit
its proof commits, when the schema covers what the row reads. -/
public theorem member_receipt_checks [DecidableEq Fact] {i₀ : Ix} (O : ι → Open S Hole A Tok Fact Ob i₀) (i : ι)
    (keys : List (Fact ⊕ Tok)) (hs : keys.length < 2 ^ 256)
    {Cell Pin : Type} (root : Obend.Run.Rest S Hole A Tok Fact → Obend.Receipt.Digest)
    (rowDigest : Event S Hole A Fact L.Rec → Obend.Receipt.Digest) (law : Obend.Receipt.Digest)
    (pinsOf : L.Rec → List (Fact ⊕ Tok) → List (Cell × Option Pin))
    (a : L.Rec × Obend.Run.Rest S Hole A Tok Fact) (r : Event S Hole A Fact L.Rec)
    (hk : ∀ f ∈ (members L base sp O (.run i)).reads a r, f ∈ keys)
    (q : Obend.Receipt.Shape) (t : List (String × Obend.Receipt.Trust)) (p : Obend.Receipt.Digest) :
    let N := Obend.Receipt.Naming.ofReading Obend.Core.Digest.deployed (viewReading L base keys) root rowDigest law pinsOf
    Obend.Receipt.datedOpens Obend.Core.Digest.deployed (Obend.Receipt.issue (members L base sp O (.run i)) N a r q t p) = true ∧
      (viewReading L base keys).matched (Obend.Receipt.issue (members L base sp O (.run i)) N a r q t p) = true :=
  Obend.Receipt.issue_checks Obend.Receipt.Merkle.deployed_bounded (members L base sp O (.run i)) (viewReading L base keys)
    (viewReading_coherent keys) hs root rowDigest law pinsOf a r hk q t p

omit [DecidableEq Cand] in
/-- **The verdict of a member's receipt is the ledger view's**: at any record whose committed view has
the receipt's dated root, the runner's row has the receipt's verdict and post root, or cSHAKE256
collides. The view the row read is a checked support. -/
public theorem member_receipt_dated_verdict [DecidableEq Fact] {i₀ : Ix} (O : ι → Open S Hole A Tok Fact Ob i₀) (i : ι)
    (keys : List (Fact ⊕ Tok)) (hs : keys.length < 2 ^ 256)
    {Cell Pin : Type} (root : Obend.Run.Rest S Hole A Tok Fact → Obend.Receipt.Digest)
    (rowDigest : Event S Hole A Fact L.Rec → Obend.Receipt.Digest) (law : Obend.Receipt.Digest)
    (pinsOf : L.Rec → List (Fact ⊕ Tok) → List (Cell × Option Pin))
    (a : L.Rec × Obend.Run.Rest S Hole A Tok Fact) (r : Event S Hole A Fact L.Rec) (hm : r.isWorld = false)
    (hk : ∀ f ∈ (members L base sp O (.run i)).reads a r, f ∈ keys)
    (q : Obend.Receipt.Shape) (t : List (String × Obend.Receipt.Trust)) (p : Obend.Receipt.Digest) (d : L.Rec)
    (hd : dated Obend.Core.Digest.deployed L base keys a.1 = dated Obend.Core.Digest.deployed L base keys d) :
    let N := Obend.Receipt.Naming.ofReading Obend.Core.Digest.deployed (viewReading L base keys) root rowDigest law pinsOf
    (Obend.Receipt.Outcome.ofExcept ((members L base sp O (.run i)).step (d, a.2) r) =
        (Obend.Receipt.issue (members L base sp O (.run i)) N a r q t p).verdict ∧
      Obend.Receipt.postOf (members L base sp O (.run i)) N (d, a.2) r =
        (Obend.Receipt.issue (members L base sp O (.run i)) N a r q t p).post) ∨
      Obend.Digest.HashBytes.Collision Obend.Core.Digest.deployed := by
  intro N
  obtain ⟨hc, hmt⟩ := member_receipt_checks (sp := sp) O i keys hs root rowDigest law pinsOf a r hk q t p
  exact Obend.Receipt.dated_verdict Obend.Receipt.Merkle.deployed_bounded _ N (viewReading L base keys)
    (viewReading_coherent keys) a r hm d (by exact hd) hc hmt

/-! ## The headline -/

variable {i₀ : Ix} {d₀ : L.Rec} {O : ι → Open S Hole A Tok Fact Ob i₀}
  {stored₀ : ι → (j : Ix) → Hole j → Option Cand} (hs₀ : L.spent d₀ = []) (hg₀ : L.grants d₀ = [])
include hs₀ hg₀

/-- **The joint run is a run of the members' family.** At every reachable joint configuration there
are rows of the family `members` (the ledger's and the runners') that fold, under
`Obend.Fold.Family.step`, from the start to the configuration's record and every runner's
accumulator, and each runner's log is exactly what `Obend.Fold.projectMoves` hands it of them. -/
public theorem jreachable_fold {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) :
    ∃ rows : List (Σ m, MRow ι W Tok L.Rec S Hole A Fact m),
      rows.foldlM (Obend.Fold.Family.step (members L base sp O)) (d₀, mrestOf sp O d₀ (JCfg.init (P := P) L d₀ O stored₀)) =
        .ok (J.led, mrestOf sp O d₀ J) ∧
      ∀ i, Obend.Fold.projectMoves (members L base sp O) (.run i) (d₀, mrestOf sp O d₀ (JCfg.init (P := P) L d₀ O stored₀)) rows =
        (J.cfgs i).cfg.log := by
  induction h with
  | init => exact ⟨[], rfl, fun _ => rfl⟩
  | @step J J' ev hJ hs ih =>
    obtain ⟨rows, hf, hp⟩ := ih
    have hI := jreachable_inv hs₀ hg₀ hJ
    have hwl : ∀ i, worldOf d₀ (J.cfgs i).cfg.log = J.led := fun i => by
      rw [← (refines (creachable_reachable (hI.reach i))).world]; exact hI.coupled i
    suffices ∃ nr : List (Σ m, MRow ι W Tok L.Rec S Hole A Fact m),
        nr.foldlM (Obend.Fold.Family.step (members L base sp O)) (J.led, mrestOf sp O d₀ J) =
          .ok (J'.led, mrestOf sp O d₀ J') ∧
        ∀ i, (J'.cfgs i).cfg.log = (J.cfgs i).cfg.log ++
          Obend.Fold.projectMoves (members L base sp O) (.run i) (J.led, mrestOf sp O d₀ J) nr by
      obtain ⟨nr, hnf, hnp⟩ := this
      refine ⟨rows ++ nr, ?_, fun i => ?_⟩
      · simp only [List.foldlM_append, hf, bind, Except.bind]; exact hnf
      · rw [Obend.Fold.projectMoves_append _ _ rows nr _ _ hf, hp i, hnp i]
    cases ev with
    | world w =>
      simp only [jrun] at hs
      split at hs
      · rename_i d hd
        cases hs
        have hall := ledgerStep_allowed L hd
        have hp' := propagate_ok (O := O) (stored₀ := stored₀) J.cfgs J.led d hI.reach hI.coupled hall
        have hs₁ : Obend.Fold.Family.step (members L base sp O) (J.led, mrestOf sp O d₀ J) ⟨Mem.ledger, .raw w⟩ =
            .ok (d, Obend.Fold.dupd (mrestOf sp O d₀ J) Mem.ledger ()) :=
          Obend.Fold.Family.step_ok (members L base sp O) (J.led, mrestOf sp O d₀ J) (i := Mem.ledger)
            (r := LRow.raw w) (b := (d, ())) (by rw [ledger_member_step, hd]; rfl)
        refine ⟨[⟨Mem.ledger, .raw w⟩], ?_, fun i => ?_⟩
        · simp only [List.foldlM_cons, List.foldlM_nil, hs₁, bind, Except.bind, pure, Except.pure]
          apply congrArg Except.ok
          refine Prod.ext rfl (funext fun m => ?_)
          dsimp only
          cases m with
          | ledger => rfl
          | run i =>
            rw [Obend.Fold.dupd_ne _ _ (by simp)]
            show _ = (accOf _ _ _ _ (propagate L base sp au k d J.cfgs i).cfg.log).rest
            rw [(hp' i).2.2, rest_world_snoc]; rfl
        · show (propagate L base sp au k d J.cfgs i).cfg.log = _
          rw [(hp' i).2.2]
          have hm : (members L base sp O Mem.ledger).moves (.raw w) = true := rfl
          simp only [Obend.Fold.projectMoves, hs₁, hm, reduceCtorEq, ↓reduceDIte, ↓reduceIte, List.append_nil]
          rfl
      · cases hs
    | dispatch i o =>
      simp only [jrun] at hs
      split at hs
      · rename_i c₂ hc₂
        split at hs
        rotate_left
        · cases hs
        rename_i d hd
        cases hs
        obtain ⟨hrun, _, _, _, _⟩ := crun_base_ok hc₂
        obtain ⟨hl₂, _⟩ := run_basic hrun
        have hreach₂ := CReachable.step _ (hI.reach i) hc₂
        have hleg := creachable_legal hreach₂
        rw [hl₂] at hleg
        have h₁ := member_run_step (sp := sp) (base := base) (O := O) (i := i) rfl hleg
        rw [hwl i] at h₁
        have hall := ledgerStep_allowed L hd
        -- the reached configuration, and every runner's log in it
        have hreach' : ∀ j, CReachable (localHost L base) (sp j) (au j) (k j)
            (CCfg.init (Cfg.init (O j) d₀) (stored₀ j)) (setCfg J.cfgs i c₂ j) := by
          intro j; by_cases e : j = i
          · subst e; rw [setCfg_same]; exact hreach₂
          · rw [setCfg_ne _ _ e]; exact hI.reach j
        have hcoup : ∀ j, (setCfg J.cfgs i c₂ j).cfg.world = J.led := by
          intro j; by_cases e : j = i
          · subst e; rw [setCfg_same]
            obtain ⟨_, hw₂⟩ := run_basic hrun
            rw [hw₂]; exact hI.coupled j
          · rw [setCfg_ne _ _ e]; exact hI.coupled j
        have hp' := propagate_ok (O := O) (stored₀ := stored₀) (setCfg J.cfgs i c₂) J.led d hreach' hcoup hall
        let s₁ : L.Rec × ((m : Mem ι) → MRest ι S Hole A Tok Fact m) :=
          (J.led, Obend.Fold.dupd (mrestOf sp O d₀ J) (.run i)
            (accOf (sp i) (O i).σ d₀ (fun _ _ => []) ((J.cfgs i).cfg.log ++ [.dispatch o])).rest)
        have hs₁ : Obend.Fold.Family.step (members L base sp O) (J.led, mrestOf sp O d₀ J) ⟨.run i, .dispatch o⟩ =
            .ok s₁ :=
          Obend.Fold.Family.step_ok (members L base sp O) (J.led, mrestOf sp O d₀ J) (i := Mem.run i)
            (r := Event.dispatch o) h₁
        let s₂ : L.Rec × ((m : Mem ι) → MRest ι S Hole A Tok Fact m) := (d, Obend.Fold.dupd s₁.2 .ledger ())
        have hs₂ : Obend.Fold.Family.step (members L base sp O) s₁ ⟨.ledger, ledgerRowOf L (sp i) J.led i o⟩ =
            .ok s₂ :=
          Obend.Fold.Family.step_ok (members L base sp O) s₁ (i := Mem.ledger) (r := ledgerRowOf L (sp i) J.led i o)
            (b := (d, ())) (by rw [ledger_member_step, show s₁.1 = J.led from rfl, hd]; rfl)
        refine ⟨[⟨.run i, .dispatch o⟩, ⟨.ledger, ledgerRowOf L (sp i) J.led i o⟩], ?_, fun j => ?_⟩
        · simp only [List.foldlM_cons, List.foldlM_nil, hs₁, hs₂, bind, Except.bind, pure, Except.pure]
          apply congrArg Except.ok
          refine Prod.ext rfl (funext fun m => ?_)
          dsimp only
          cases m with
          | ledger => rfl
          | run j =>
            show Obend.Fold.dupd s₁.2 Mem.ledger () (Mem.run j) = (accOf _ _ _ _ (propagate L base sp au k d (setCfg J.cfgs i c₂) j).cfg.log).rest
            rw [Obend.Fold.dupd_ne _ _ (by simp), (hp' j).2.2, rest_world_snoc]
            by_cases e : j = i
            · subst e
              rw [setCfg_same, hl₂]
              show Obend.Fold.dupd _ (Mem.run j) _ (Mem.run j) = _
              rw [Obend.Fold.dupd_same]
            · rw [setCfg_ne _ _ e]
              show Obend.Fold.dupd _ (Mem.run i) _ (Mem.run j) = _
              rw [Obend.Fold.dupd_ne _ _ (by simpa using e)]; rfl
        · rw [project_pair rfl hs₁ hs₂ j, (hp' j).2.2]
          by_cases e : j = i
          · subst e; rw [setCfg_same, hl₂]; simp; rfl
          · rw [setCfg_ne _ _ e]; simp [e]; rfl
      · split at hs <;> cases hs
      · cases hs
    | abandon i o =>
      simp only [jrun] at hs
      split at hs
      · rename_i c₁ hc₁
        split at hs
        rotate_left
        · cases hs
        rename_i d hd
        cases hs
        obtain ⟨hrun, _, _, _, _⟩ := crun_base_ok hc₁
        obtain ⟨hl₁, hw₁⟩ := run_basic hrun
        have hreach₁ := CReachable.step _ (hI.reach i) hc₁
        have hleg := creachable_legal hreach₁
        rw [hl₁] at hleg
        have h₁ := member_run_step (sp := sp) (base := base) (O := O) (i := i) rfl hleg
        rw [hwl i] at h₁
        have hall := ledgerStep_allowed L hd
        have hreach' : ∀ j, CReachable (localHost L base) (sp j) (au j) (k j)
            (CCfg.init (Cfg.init (O j) d₀) (stored₀ j)) (setCfg J.cfgs i c₁ j) := by
          intro j; by_cases e : j = i
          · subst e; rw [setCfg_same]; exact hreach₁
          · rw [setCfg_ne _ _ e]; exact hI.reach j
        have hcoup : ∀ j, (setCfg J.cfgs i c₁ j).cfg.world = J.led := by
          intro j; by_cases e : j = i
          · subst e; rw [setCfg_same, hw₁]; exact hI.coupled j
          · rw [setCfg_ne _ _ e]; exact hI.coupled j
        have hp' := propagate_ok (O := O) (stored₀ := stored₀) (setCfg J.cfgs i c₁) J.led d hreach' hcoup hall
        let s₁ : L.Rec × ((m : Mem ι) → MRest ι S Hole A Tok Fact m) :=
          (J.led, Obend.Fold.dupd (mrestOf sp O d₀ J) (.run i)
            (accOf (sp i) (O i).σ d₀ (fun _ _ => []) ((J.cfgs i).cfg.log ++ [.abandon o])).rest)
        have hs₁ : Obend.Fold.Family.step (members L base sp O) (J.led, mrestOf sp O d₀ J) ⟨.run i, .abandon o⟩ =
            .ok s₁ :=
          Obend.Fold.Family.step_ok (members L base sp O) (J.led, mrestOf sp O d₀ J) (i := Mem.run i)
            (r := Event.abandon o) h₁
        let s₂ : L.Rec × ((m : Mem ι) → MRest ι S Hole A Tok Fact m) := (d, Obend.Fold.dupd s₁.2 .ledger ())
        have hs₂ : Obend.Fold.Family.step (members L base sp O) s₁ ⟨.ledger, .abandon i⟩ = .ok s₂ :=
          Obend.Fold.Family.step_ok (members L base sp O) s₁ (i := Mem.ledger) (r := .abandon i)
            (b := (d, ())) (by rw [ledger_member_step, show s₁.1 = J.led from rfl, hd]; rfl)
        refine ⟨[⟨.run i, .abandon o⟩, ⟨.ledger, .abandon i⟩], ?_, fun j => ?_⟩
        · simp only [List.foldlM_cons, List.foldlM_nil, hs₁, hs₂, bind, Except.bind, pure, Except.pure]
          apply congrArg Except.ok
          refine Prod.ext rfl (funext fun m => ?_)
          dsimp only
          cases m with
          | ledger => rfl
          | run j =>
            show Obend.Fold.dupd s₁.2 Mem.ledger () (Mem.run j) = (accOf _ _ _ _ (propagate L base sp au k d (setCfg J.cfgs i c₁) j).cfg.log).rest
            rw [Obend.Fold.dupd_ne _ _ (by simp), (hp' j).2.2, rest_world_snoc]
            by_cases e : j = i
            · subst e
              rw [setCfg_same, hl₁]
              show Obend.Fold.dupd _ (Mem.run j) _ (Mem.run j) = _
              rw [Obend.Fold.dupd_same]
            · rw [setCfg_ne _ _ e]
              show Obend.Fold.dupd _ (Mem.run i) _ (Mem.run j) = _
              rw [Obend.Fold.dupd_ne _ _ (by simpa using e)]; rfl
        · rw [project_pair rfl hs₁ hs₂ j, (hp' j).2.2]
          by_cases e : j = i
          · subst e; rw [setCfg_same, hl₁]; simp; rfl
          · rw [setCfg_ne _ _ e]; simp [e]; rfl
      · cases hs
    | own i ev =>
      simp only [jrun] at hs
      split at hs
      · cases hs
      · cases hs
      · cases hs
      · rename_i hnw hnd hna
        split at hs
        · rename_i c₁ hc₁
          cases hs
          have hstep : (c₁.cfg = (J.cfgs i).cfg) ∨ ∃ e, (∀ v, e ≠ .world v) ∧
              run (localHost L base) (sp i) (J.cfgs i).cfg e = .ok c₁.cfg := by
            cases ev with
            | base e =>
              exact .inr ⟨e, fun v he => hnw v (by rw [he]), (crun_base_ok hc₁).1⟩
            | advance h =>
              rcases crun_advance_ok hc₁ with he | ⟨cand, _, hi⟩
              · exact .inl (by rw [he])
              · exact .inr ⟨_, (fun _ e => by cases e), (install_ok hi).1⟩
            | choose p cred h cand e =>
              obtain ⟨_, _, _, _, _, hi⟩ := crun_choose_ok hc₁
              exact .inr ⟨_, (fun _ e => by cases e), (install_ok hi).1⟩
          rcases hstep with he | ⟨e, hw, hrun⟩
          · refine ⟨[], ?_, fun j => ?_⟩
            · show Except.ok (J.led, mrestOf sp O d₀ J) = .ok (J.led, mrestOf sp O d₀ ⟨J.led, setCfg J.cfgs i c₁⟩)
              congr 2; funext m
              refine (mrestOf_congr (fun j => ?_) m).symm
              by_cases e : j = i
              · subst e; show (accOf _ _ _ _ (setCfg J.cfgs j c₁ j).cfg.log).rest = _; rw [setCfg_same, he]
              · show (accOf _ _ _ _ (setCfg J.cfgs i c₁ j).cfg.log).rest = _; rw [setCfg_ne _ _ e]
            · show (setCfg J.cfgs i c₁ j).cfg.log = _
              by_cases e : j = i
              · subst e; rw [setCfg_same, he]; simp [Obend.Fold.projectMoves]
              · rw [setCfg_ne _ _ e]; simp [Obend.Fold.projectMoves]
          · obtain ⟨hl, _⟩ := run_basic hrun
            have hreach₁ := CReachable.step _ (hI.reach i) hc₁
            have hleg := creachable_legal hreach₁
            rw [hl] at hleg
            have hew : e.isWorld = false := by cases e <;> first | rfl | exact absurd rfl (hw _)
            have h₁ := member_run_step (sp := sp) (base := base) (O := O) (i := i) hew hleg
            rw [hwl i] at h₁
            have hs₁ : Obend.Fold.Family.step (members L base sp O) (J.led, mrestOf sp O d₀ J) ⟨.run i, e⟩ =
                .ok (J.led, Obend.Fold.dupd (mrestOf sp O d₀ J) (.run i)
                  (accOf (sp i) (O i).σ d₀ (fun _ _ => []) ((J.cfgs i).cfg.log ++ [e])).rest) :=
              Obend.Fold.Family.step_ok (members L base sp O) (J.led, mrestOf sp O d₀ J) (i := Mem.run i)
                (r := e) h₁
            refine ⟨[⟨.run i, e⟩], ?_, fun j => ?_⟩
            · simp only [List.foldlM_cons, List.foldlM_nil, hs₁, bind, Except.bind, pure, Except.pure]
              apply congrArg Except.ok
              refine Prod.ext rfl (funext fun m => ?_)
              dsimp only
              cases m with
              | ledger => rfl
              | run j =>
                show _ = (accOf _ _ _ _ (setCfg J.cfgs i c₁ j).cfg.log).rest
                by_cases e' : j = i
                · subst e'; rw [setCfg_same, hl, Obend.Fold.dupd_same]
                · rw [setCfg_ne _ _ e', Obend.Fold.dupd_ne _ _ (by simpa using e')]; rfl
            · show (setCfg J.cfgs i c₁ j).cfg.log = _
              simp only [Obend.Fold.projectMoves, hs₁]
              by_cases e' : j = i
              · subst e'; rw [setCfg_same, hl]; simp
              · have : ¬ (Mem.run i = Mem.run j) := fun h => e' (by cases h; rfl)
                rw [setCfg_ne _ _ e']
                simp only [this, ↓reduceDIte]
                change _ = _ ++ ((if e.isWorld then _ else []) ++ [])
                simp [hew]
        · cases hs

/-- **Projection**: every runner's own log is `Legal` for its own object at its local host. It is
`Obend.Fold.project_moves_run` applied to the joint fold (`jreachable_fold`) at the runner's member,
read through `legal_iff_admission`; the clause that is not per row (`Kept`) is the runner's own. Its
`Authorized` clause says every exposure was admitted at the shared view. -/
public theorem joint_reachable_projects_legal {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) (i : ι) :
    Legal (localHost L base) (sp i) (O i) d₀ (fun _ _ => []) (J.cfgs i).cfg.log := by
  obtain ⟨rows, hf, hp⟩ := jreachable_fold hs₀ hg₀ h
  have hm := Obend.Fold.project_moves_run (members L base sp O) (members_guarantee O) (.run i) rows _ _ hf
  rw [hp i] at hm
  refine (legal_iff_admission (localHost L base) (sp i) (O i) d₀ (fun _ _ => []) _).2
    ⟨_, hm, ?_⟩
  exact (creachable_legal ((jreachable_inv hs₀ hg₀ h).reach i)).kept

/-- **The ledger's own fold**: the same theorem at the ledger's member. The rows the ledger sees of
the joint run (its own: commits, raw moves, abandonments, observations) fold from the start to the
joint record, so every commit the ledger made was of a token not yet consumed (`ledgerStep`). -/
public theorem joint_ledger_fold {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) :
    ∃ rows : List (Σ m, MRow ι W Tok L.Rec S Hole A Fact m),
      (Obend.Fold.projectMoves (members L base sp O) .ledger (d₀, mrestOf sp O d₀ (JCfg.init (P := P) L d₀ O stored₀)) rows).foldlM
        (ledgerAdmission L base).step (d₀, ()) = .ok (J.led, ()) := by
  obtain ⟨rows, hf, _⟩ := jreachable_fold hs₀ hg₀ h
  exact ⟨rows, Obend.Fold.project_moves_run (members L base sp O) (members_guarantee O) .ledger rows _ _ hf⟩

/-- **Exclusion**: no token is granted twice, and the ledger's consumption is its grants. -/
public theorem joint_reachable_ticket_exclusive {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) :
    ((L.grants J.led).map Grant.tok).Nodup ∧ L.spent J.led = (L.grants J.led).map Grant.tok :=
  ⟨(jreachable_inv hs₀ hg₀ h).nodup, (jreachable_inv hs₀ hg₀ h).spent_grants⟩

/-- **`OnceSpent` globally**: each runner spends a token at most once, and a token two runners' logs
spent was spent by one runner. -/
public theorem joint_once {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) :
    (∀ i, (spentBy (sp i) (J.cfgs i).cfg.log).Nodup) ∧
      ∀ i j t, t ∈ spentBy (sp i) (J.cfgs i).cfg.log → t ∈ spentBy (sp j) (J.cfgs j).cfg.log → i = j := by
  have hI := jreachable_inv hs₀ hg₀ h
  refine ⟨fun i => (joint_reachable_projects_legal hs₀ hg₀ h i).once, fun i j t hi hj => ?_⟩
  rw [hI.local_spent] at hi hj
  obtain ⟨gi, hgi, rfl⟩ := List.mem_map.1 hi
  obtain ⟨gj, hgj, hgt⟩ := List.mem_map.1 hj
  rw [List.mem_filter] at hgi hgj
  have hnd := hI.nodup
  have : gi = gj := nodup_map_inj hnd gi hgi.1 gj hgj.1 hgt.symm
  have hwi := of_decide_eq_true hgi.2
  have hwj := of_decide_eq_true hgj.2
  rw [← hwi, ← hwj, this]

/-- **Coupling**: every runner's world is the ledger. -/
public theorem joint_coupled {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) (i : ι) :
    (J.cfgs i).cfg.world = J.led :=
  (jreachable_inv hs₀ hg₀ h).coupled i

/-- **The loser's refusal names the winner and the epoch**: at a joint configuration, a runner whose
next call needs a token the ledger granted is refused, naming the grant's winner and epoch, before
the call is exposed. -/
public theorem loser_refused_names_winner_and_epoch {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) (i : ι)
    {j : Ix} {op : S.Op j} {kk : (r : S.Resp op) → Prot S Hole A (S.next op r)}
    (hres : (J.cfgs i).cfg.res = ⟨j, .call op kk⟩) (hinf : (J.cfgs i).cfg.obj.hist.inflight = none)
    (hend : (J.cfgs i).cfg.ended = none) {t : Tok} (ht : (sp i).consumes op = some t)
    {g : Grant ι Tok} (hg : g ∈ L.grants J.led) (hgt : g.tok = t) :
    jrun L base sp au k J (.dispatch i ⟨j, op⟩) = .error (.taken t g.winner g.epoch) := by
  have hI := jreachable_inv hs₀ hg₀ h
  have hcw : (J.cfgs i).cfg.world = J.led := hI.coupled i
  have hspent : t ∈ L.spent J.led := by rw [hI.spent_grants]; exact List.mem_map.2 ⟨g, hg, hgt⟩
  have hgrant : grantOf L J.led t = some g := by
    unfold grantOf
    cases hf : (L.grants J.led).find? (fun g => decide (g.tok = t)) with
    | none =>
      have := List.find?_eq_none.1 hf g hg
      simp [hgt] at this
    | some g' =>
      have h1 := List.mem_of_find?_eq_some hf
      have h2 := List.find?_some hf
      simp only [decide_eq_true_eq] at h2
      rw [nodup_map_inj hI.nodup g' h1 g hg (h2.trans hgt.symm)]
  have hlive : sharedLive L base J.led t = false := by simp [sharedLive, hspent]
  simp only [jrun, crun, run]
  simp only [closedBy, hend, awaiting, hinf, hres, ↓reduceIte, dispatchGuard, admitOp, Cfg.admitView,
    View.mask, localHost, ht, hcw, hlive, Bool.false_and, Bool.and_false, Bool.false_eq_true, missingOf]
  simp [hgrant]

end

end Obend.Run.Shared

