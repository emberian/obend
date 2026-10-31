module
/-
# Obend.Run.Proofs.Shared — the composition layer's theorems

At every joint configuration reachable from the start (`JInv`, `jreachable_inv`):

- `joint_reachable_projects_legal`: each runner's own log is `Legal` for its own object at its
  local host (each joint step is a sequence of that runner's own accepted steps; the other runners'
  commits reach it as world events its host allows, by the ledger's laws). Its `Authorized` clause is
  the headline "every exposure was admitted at the shared view": the local host IS the shared view.
- `joint_reachable_ticket_exclusive`: no token is granted twice, and the ledger's consumption is
  exactly its grants.
- `joint_once`: `OnceSpent` globally: a token spent by two runners' logs was spent by one runner.
- `joint_coupled`: every runner's world is the ledger (the projection relation).
- `loser_refused_names_winner_and_epoch`: a runner whose next call needs a token another runner
  holds is refused, naming the winner and the epoch of its grant.

None of these assumes global once-spending: it is derived from each runner's own admission at the
shared mask (`sharedLive`) and the ledger's commit laws. Durability (`Ledger.Durable`: an
abandonment releases nothing) is the one law the exclusion theorems take beyond the structure.
-/
public import Obend.Run.Shared
public import Obend.Run.Proofs.Control
public import Obend.Tactic.Tooth
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Run.Control
import all Obend.Run.Shared
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
public theorem jreachable_inv (hdur : L.Durable) {i₀ : Ix} {d₀ : L.Rec} {O : ι → Open S Hole A Tok Fact Ob i₀}
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
      · rename_i hstep
        cases hs
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
        cases hs
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
        · rw [hdur.spent, hdur.grants]; exact ih.spent_grants
        · rw [hdur.grants]; exact ih.nodup
        · rw [(hp j).2.2, spentBy_snoc_ev, hdur.grants]
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
      · cases hs
      · rename_i c₁ hc₁
        obtain ⟨hl₁, hw₁, _⟩ := crun_world hc₁
        have hreach₁ := CReachable.step _ (ih.reach i) hc₁
        split at hs
        · rename_i c₂ hc₂
          cases hs
          obtain ⟨hrun, _, _, _, _⟩ := crun_base_ok hc₂
          obtain ⟨hl₂, hw₂⟩ := run_basic hrun
          have hadm := run_dispatch_admitted hrun
          have hreach' : ∀ j, CReachable (localHost L base) (sp j) (au j) (k j)
              (CCfg.init (Cfg.init (O j) d₀) (stored₀ j)) (setCfg J.cfgs i c₂ j) := by
            intro j; by_cases e : j = i
            · subst e; rw [setCfg_same]; exact .step _ hreach₁ hc₂
            · rw [setCfg_ne _ _ e]; exact ih.reach j
          have hcoup : ∀ j, (setCfg J.cfgs i c₂ j).cfg.world = J.led := by
            intro j; by_cases e : j = i
            · subst e; rw [setCfg_same, hw₂, hw₁]
            · rw [setCfg_ne _ _ e]; exact ih.coupled j
          -- the token, if any, was live at the shared mask: not yet consumed
          have hfresh : ∀ t, (sp i).consumes o.2 = some t → t ∉ L.spent J.led := by
            intro t ht hm
            simp only [admitOp, Cfg.admitView, View.mask, localHost, ht, Bool.and_eq_true] at hadm
            have := hadm.2.1
            simp only [sharedLive, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
            rw [hw₁] at this
            exact this.2 hm
          have hall : L.allowed J.led (commitOf L (sp i) J.led i o) = true := by
            unfold commitOf; split
            · exact L.allowed_commit _ _ _
            · exact L.allowed_refl _
          have hp := propagate_ok (O := O) (stored₀ := stored₀) (setCfg J.cfgs i c₂) J.led _ hreach' hcoup hall
          refine ⟨fun j => (hp j).1, fun j => (hp j).2.1, ?_, ?_, fun j => ?_⟩
          · unfold commitOf; split
            · rw [L.commit_spent, L.commit_grants, ih.spent_grants]; simp
            · exact ih.spent_grants
          · unfold commitOf; split
            · rename_i t ht
              rw [L.commit_grants, List.map_append, List.nodup_append]
              refine ⟨ih.nodup, by simp, ?_⟩
              intro a ha b hb e
              simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
              subst hb; subst e
              exact hfresh a ht (by rw [ih.spent_grants]; exact ha)
            · exact ih.nodup
          · rw [(hp j).2.2, spentBy_snoc_ev]
            simp only [List.append_nil]
            by_cases e : j = i
            · subst e
              rw [setCfg_same, hl₂, spentBy_snoc_ev, hl₁, spentBy_snoc_ev, ih.local_spent j]
              simp only [List.append_nil]
              unfold commitOf; split
              · rename_i t ht; rw [L.commit_grants, filter_snoc_grant, ht]; simp
              · rename_i ht; rw [ht]; simp
            · rw [setCfg_ne _ _ e, ih.local_spent j]
              unfold commitOf; split
              · rw [L.commit_grants, filter_snoc_grant]; simp [Ne.symm e]
              · rfl
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

/-! ## The headline -/

variable (hdur : L.Durable) {i₀ : Ix} {d₀ : L.Rec} {O : ι → Open S Hole A Tok Fact Ob i₀}
  {stored₀ : ι → (j : Ix) → Hole j → Option Cand} (hs₀ : L.spent d₀ = []) (hg₀ : L.grants d₀ = [])
include hdur hs₀ hg₀

/-- **Projection**: every runner's own log is `Legal` for its own object at its local host. Its
`Authorized` clause says every exposure was admitted at the shared view. -/
public theorem joint_reachable_projects_legal {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) (i : ι) :
    Legal (localHost L base) (sp i) (O i) d₀ (fun _ _ => []) (J.cfgs i).cfg.log :=
  creachable_legal ((jreachable_inv hdur hs₀ hg₀ h).reach i)

/-- **Exclusion**: no token is granted twice, and the ledger's consumption is its grants. -/
public theorem joint_reachable_ticket_exclusive {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) :
    ((L.grants J.led).map Grant.tok).Nodup ∧ L.spent J.led = (L.grants J.led).map Grant.tok :=
  ⟨(jreachable_inv hdur hs₀ hg₀ h).nodup, (jreachable_inv hdur hs₀ hg₀ h).spent_grants⟩

/-- **`OnceSpent` globally**: each runner spends a token at most once, and a token two runners' logs
spent was spent by one runner. -/
public theorem joint_once {J : JCfg L S Hole A P Cand Fact Ob i₀}
    (h : JReachable L base sp au k (JCfg.init L d₀ O stored₀) J) :
    (∀ i, (spentBy (sp i) (J.cfgs i).cfg.log).Nodup) ∧
      ∀ i j t, t ∈ spentBy (sp i) (J.cfgs i).cfg.log → t ∈ spentBy (sp j) (J.cfgs j).cfg.log → i = j := by
  have hI := jreachable_inv hdur hs₀ hg₀ h
  refine ⟨fun i => (joint_reachable_projects_legal hdur hs₀ hg₀ h i).once, fun i j t hi hj => ?_⟩
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
  (jreachable_inv hdur hs₀ hg₀ h).coupled i

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
  have hI := jreachable_inv hdur hs₀ hg₀ h
  have hal : (localHost L base).allowed (J.cfgs i).cfg.world J.led = true := by
    show L.allowed _ _ = true; rw [hI.coupled i]; exact L.allowed_refl _
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
  simp only [jrun, crun, run, hal, ↓reduceIte]
  simp only [closedBy, hend, awaiting, hinf, hres, ↓reduceIte, dispatchGuard, admitOp, Cfg.admitView,
    View.mask, localHost, ht, hlive, Bool.false_and, Bool.and_false, Bool.false_eq_true, missingOf]
  simp [hgrant]

end

end Obend.Run.Shared

