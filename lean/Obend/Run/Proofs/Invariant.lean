module
/-
# Obend.Run.Proofs.Invariant — the runner refines its specification

The headline is `refines`: every configuration the runner reaches from `Cfg.init O v₀` satisfies
`Inv`, by induction on reachability (`step_inv` is the induction step, for ANY accepted event, with no
premise on the event beyond the runner's acceptance). `Inv` says the log is `Legal` (every
dispatched call was admitted at its dispatch view, no token spent twice, replies paired with the
call in flight, no entered hole replanned, the history a history of the plan in force:
`reachable_legal`) and that the configuration is the log's: its world, spent tokens, history and plan
are those the log recomputes, and its residual is where the plan in force is after the answered
history, the in-flight call (if any) its next call.

The continuation clause: before dispatch, a replan of a hole the history has not entered is
accepted (`replan_accepted`), and a replacement whose next call is admitted now takes that step
(`replace_then_dispatch`); after dispatch, with the reply missing, every event other than a reply
leaves the history, the spent tokens and the dispatches as they were (`lost_reply_frozen`), a
dispatch is refused `busy` (`inflight_busy`) and a replan of the entered hole is refused
`replacesInflight` (`inflight_replan_refused`). An accepted replan satisfies the open object's own
guard `Open.Replan` (`run_replan_guard`).
-/
public import Obend.Run.Spec
public import Obend.Slot.Proofs.Protocol
public import Obend.Tactic.Tooth
public import Obend.AxiomPin
import all Obend.Run.Runner
import all Obend.Run.Spec
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping

namespace Obend.Run

open Obend.Slot Obend.Slot.Protocol

/-! ## Positions of a log -/

section
variable {α : Type}

theorem AtEach.nil (Q : List α → α → Prop) : AtEach Q [] := by
  intro n z h; simp at h

theorem AtEach.snoc {Q : List α → α → Prop} {l : List α} {x : α} :
    AtEach Q (l ++ [x]) ↔ AtEach Q l ∧ Q l x := by
  constructor
  · intro h
    refine ⟨fun n z hz => ?_, ?_⟩
    · have hn : n < l.length := (List.getElem?_eq_some_iff.mp hz).1
      have := h n z (by rw [List.getElem?_append_left hn]; exact hz)
      rwa [List.take_append_of_le_length (Nat.le_of_lt hn)] at this
    · have := h l.length x (by simp)
      simpa using this
  · rintro ⟨h, hx⟩ n z hz
    rcases Nat.lt_or_ge n l.length with hn | hn
    · rw [List.getElem?_append_left hn] at hz
      rw [List.take_append_of_le_length (Nat.le_of_lt hn)]
      exact h n z hz
    · rw [List.getElem?_append_right hn] at hz
      cases hm : n - l.length with
      | zero =>
        rw [hm] at hz
        have : n = l.length := by omega
        subst this
        simp at hz
        subst hz
        simpa using hx
      | succ m => rw [hm] at hz; simp at hz

end

/-! ## Following a trace -/

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable [DecidableEq (Σ i, S.Op i)]

public theorem follow_call {j : Ix} (op : S.Op j) (k : (r : S.Resp op) → Prot S Hole A (S.next op r))
    (r : S.Resp op) : follow ⟨j, .call op k⟩ ⟨j, op, r⟩ = some ⟨_, k r⟩ := by
  simp [follow]

theorem follow_reach {R R' : Σ j, Prot S Hole A j} {e : Entry S} (h : follow R e = some R') :
    Reach R.2 [e] R' := by
  obtain ⟨j, P⟩ := R
  obtain ⟨i', op', r'⟩ := e
  cases P with
  | ret a => simp [follow] at h
  | hole h' => simp [follow] at h
  | call op k =>
    by_cases he : (⟨i', op'⟩ : Σ i, S.Op i) = ⟨j, op⟩
    · cases he
      rw [follow_call] at h
      cases h
      exact .call r' (.here _)
    · simp [follow, he] at h

theorem advance_reach {R R' : Σ j, Prot S Hole A j} {t : Trace S} (h : advance R t = some R') :
    Reach R.2 t R' := by
  induction t generalizing R with
  | nil => cases h; exact .here _
  | cons e t ih =>
    unfold advance at h
    split at h
    · rename_i R₁ hf
      exact reach_append (t₁ := [e]) (follow_reach hf) (ih h)
    · cases h

theorem reach_advance {i : Ix} {P : Prot S Hole A i} {t : Trace S} {R : Σ j, Prot S Hole A j}
    (h : Reach P t R) : advance ⟨i, P⟩ t = some R := by
  induction h with
  | here => rfl
  | @call i op k tr R r _ ih =>
    simp only [advance, follow_call]
    exact ih

theorem entered_call {i : Ix} (op : S.Op i) (k : (r : S.Resp op) → Prot S Hole A (S.next op r))
    (r : S.Resp op) (t : Trace S) (b : Bool) :
    entered (.call op k) (⟨i, op, r⟩ :: t) b = entered (k r) t b := by
  simp [entered]

theorem entered_of_reach {i : Ix} {P : Prot S Hole A i} {t₁ t₂ : Trace S}
    {R : Σ j, Prot S Hole A j} (hr : Reach P t₁ R) {j : Ix} {h : Hole j} {b : Bool}
    (hR : R = ⟨j, .hole h⟩) (hne : t₂ ≠ [] ∨ b = true) :
    entered P (t₁ ++ t₂) b = some ⟨j, h⟩ := by
  induction hr with
  | here P =>
    cases hR
    simp only [List.nil_append, entered]
    rcases hne with hne | hne
    · cases t₂ with
      | nil => exact absurd rfl hne
      | cons => rfl
    · subst hne; simp
  | call r _ ih =>
    simp only [List.cons_append, entered_call]
    exact ih hR

theorem reach_of_entered {i : Ix} {P : Prot S Hole A i} {t : Trace S} {b : Bool} {j : Ix}
    {h : Hole j} (he : entered P t b = some ⟨j, h⟩) :
    ∃ t₁ t₂, t = t₁ ++ t₂ ∧ Reach P t₁ ⟨j, .hole h⟩ ∧ (t₂ ≠ [] ∨ b = true) := by
  induction P generalizing t with
  | ret a => simp [entered] at he
  | @hole i h' =>
    unfold entered at he
    split at he
    · cases he
    · rename_i hc
      cases he
      refine ⟨[], t, rfl, .here _, ?_⟩
      cases t with
      | nil => cases b <;> simp_all
      | cons => exact .inl (by simp)
  | @call i op k ih =>
    cases t with
    | nil => simp [entered] at he
    | cons e t =>
      obtain ⟨i', op', r'⟩ := e
      by_cases hq : (⟨i', op'⟩ : Σ i, S.Op i) = ⟨i, op⟩
      · cases hq
        rw [entered_call] at he
        obtain ⟨t₁, t₂, ht, hr, hne⟩ := ih r' he
        exact ⟨_ :: t₁, t₂, by simp [ht], .call r' hr, hne⟩
      · simp [entered, hq] at he

/-- `entered` is exactly `Dispatched`. -/
theorem entered_iff {i : Ix} {P : Prot S Hole A i} {H : Hist S} {j : Ix} {h : Hole j} :
    Dispatched P H j h ↔ entered P H.answered H.inflight.isSome = some ⟨j, h⟩ := by
  constructor
  · rintro ⟨t₁, t₂, ht, hr, hne⟩
    rw [ht]
    exact entered_of_reach hr rfl hne
  · intro he
    obtain ⟨t₁, t₂, ht, hr, hne⟩ := reach_of_entered he
    exact ⟨t₁, t₂, ht, hr, hne⟩

theorem nextIs_isCall {R : Σ j, Prot S Hole A j} {o : Σ i, S.Op i}
    (h : nextIs R (some o) = true) : IsCall R o := by
  obtain ⟨j, P⟩ := R
  cases P with
  | ret => simp [nextIs] at h
  | hole => simp [nextIs] at h
  | call op k => simpa [nextIs, IsCall] using h

theorem isCall_nextIs {R : Σ j, Prot S Hole A j} {o : Σ i, S.Op i} (h : IsCall R o) :
    nextIs R (some o) = true := by
  obtain ⟨j, P⟩ := R
  cases P with
  | ret => exact h.elim
  | hole => exact h.elim
  | call op k => simpa [nextIs, IsCall] using h

end

/-! ## Installing a filling -/

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable [DecidableEq Ix] [∀ i, DecidableEq (Hole i)]

theorem setHole_ne (σ : Subst S Hole A) {j : Ix} (h : Hole j) (f : Prot S Hole A j) {i : Ix}
    {h' : Hole i} (hne : (⟨i, h'⟩ : Σ j, Hole j) ≠ ⟨j, h⟩) : setHole σ h f i h' = σ i h' := by
  simp [setHole, hne]

theorem mine_setHole_ne {Tok Fact Ob : Type} (Ω : Ctx S Hole A Tok Fact Ob) (σ : Subst S Hole A)
    {j : Ix} (h : Hole j) (f : Prot S Hole A j) {i : Ix} {h' : Hole i}
    (hne : (⟨i, h'⟩ : Σ j, Hole j) ≠ ⟨j, h⟩) :
    (setHole σ h f).mine Ω i h' = σ.mine Ω i h' := by
  simp only [Subst.mine]
  split <;> simp [setHole_ne σ h f hne]

end

/-! ## The invariant -/

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type} {Tok Fact Ob V : Type}
variable [DecidableEq (Σ i, S.Op i)] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable {cs₀ : (j : Ix) → Hole j → List Fact}

/-- The invariant of every reachable configuration of a run of `O` from world `v₀`: the log's clauses
(`Legal`, less `Kept`, which follows: `Inv.legal`), and the configuration is the log's. -/
public structure Inv (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (O : Open S Hole A Tok Fact Ob i) (v₀ : V) (cs₀ : (j : Ix) → Hole j → List Fact)
    (c : Cfg S Hole A Tok Fact Ob V i) : Prop where
  steps : WorldSteps host v₀ c.log
  authorized : Authorized host sp v₀ c.log
  once : OnceSpent sp c.log
  paired : Paired c.log
  final : AfterAbandon c.log
  frozen : ReplansUnentered O.template c.log
  /-- the object is `O` with the plan and the history the log recomputes -/
  obj : c.obj = { O with σ := planOf O.σ c.log, hist := histOf c.log }
  world : c.world = worldOf v₀ c.log
  spent : c.spent = spentBy sp c.log
  /-- the residual is where the plan in force is after the answered history -/
  residual : Reach c.obj.current c.obj.hist.answered c.res
  /-- the call in flight is the residual's next call -/
  next : ∀ o, c.obj.hist.inflight = some o → IsCall c.res o
  /-- the run is ended by the call the log abandoned, if any -/
  ended : c.ended = endedOf c.log
  decided : DecisionsHeld host O.template v₀ cs₀ c.log
  /-- each hole's decision cites what the log's last replan of it cited -/
  cites : c.cites = citesOf cs₀ c.log

omit [DecidableEq (Σ i, S.Op i)] in
public theorem Inv.started {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c : Cfg S Hole A Tok Fact Ob V i}
    (hI : Inv host sp O v₀ cs₀ c) : Started c.obj.current c.obj.hist := by
  cases ho : c.obj.hist.inflight with
  | none =>
    have : c.obj.hist = ⟨c.obj.hist.answered, none⟩ := by rw [← ho]
    rw [this]
    exact .settled hI.residual
  | some o =>
    have : c.obj.hist = ⟨c.obj.hist.answered, some o⟩ := by rw [← ho]
    rw [this]
    exact started_some_iff.mpr ⟨_, hI.residual, hI.next o ho⟩

omit [DecidableEq (Σ i, S.Op i)] in
public theorem Inv.legal {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c : Cfg S Hole A Tok Fact Ob V i}
    (hI : Inv host sp O v₀ cs₀ c) : Legal host sp O v₀ cs₀ c.log := by
  refine ⟨hI.steps, hI.authorized, hI.decided, hI.once, hI.paired, hI.final, hI.frozen, ?_⟩
  have h := hI.started
  rw [hI.obj] at h
  exact h

omit [DecidableEq (Σ i, S.Op i)] in
theorem inv_init (host : Host V Tok Fact) (sp : Spec S Tok Fact Ob) {i : Ix}
    (O : Open S Hole A Tok Fact Ob i) (v₀ : V) : Inv host sp O v₀ cs₀ (Cfg.init O v₀ cs₀) where
  steps := AtEach.nil _
  authorized := AtEach.nil _
  once := List.nodup_nil
  paired := AtEach.nil _
  final := AtEach.nil _
  frozen := AtEach.nil _
  obj := rfl
  world := rfl
  spent := rfl
  residual := .here _
  next := fun _ h => by cases h
  ended := rfl
  decided := AtEach.nil _
  cites := rfl

omit [DecidableEq (Σ i, S.Op i)] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok] in
theorem endedOf_snoc_live {log : List (Event S Hole A Fact V)} {e : Event S Hole A Fact V}
    (he : ∀ o, e ≠ .abandon o) : endedOf (log ++ [e]) = endedOf log := by
  cases e with
  | abandon o => exact absurd rfl (he o)
  | _ => simp [endedOf, List.foldl_append]

theorem run_live {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {ev : Event S Hole A Fact V}
    (hev : ∀ v, ev ≠ .world v) (h : run host sp c ev = .ok c') : closedBy c = none := by
  cases hcl : closedBy c with
  | none => rfl
  | some x =>
    cases ev with
    | world v => exact absurd rfl (hev v)
    | _ => simp [run, hcl] at h

theorem inv_world {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c c' : Cfg S Hole A Tok Fact Ob V i} {v : V}
    (hI : Inv host sp O v₀ cs₀ c) (h : run host sp c (.world v) = .ok c') : Inv host sp O v₀ cs₀ c' := by
  simp only [run] at h
  by_cases ha : host.allowed c.world v = true
  · simp only [ha, ↓reduceIte] at h
    cases h
    refine ⟨AtEach.snoc.mpr ⟨hI.steps, ?_⟩, AtEach.snoc.mpr ⟨hI.authorized, ?_⟩, ?_,
      AtEach.snoc.mpr ⟨hI.paired, ?_, ?_, fun _ e => by cases e⟩,
      AtEach.snoc.mpr ⟨hI.final, fun _ => ⟨_, rfl⟩⟩, AtEach.snoc.mpr ⟨hI.frozen, ?_⟩, ?_, ?_, ?_,
      hI.residual, hI.next,
      by rw [endedOf_snoc_live (fun _ h => by cases h)]; exact hI.ended, AtEach.snoc.mpr ⟨hI.decided, fun _ e => by cases e⟩,
      by simpa [citesOf, List.foldl_append] using hI.cites⟩
    · intro v' e
      cases e
      rw [← hI.world]
      exact ha
    · intro o e; cases e
    · simpa [OnceSpent, spentBy, List.filterMap_append] using hI.once
    · intro o e; cases e
    · intro r e; cases e
    · intro j h f cs e; cases e
    · simpa [planOf, histOf, List.foldl_append] using hI.obj
    · simp [worldOf, List.foldl_append]
    · simpa [spentBy, List.filterMap_append] using hI.spent
  · simp only [ha] at h; cases h

theorem inv_dispatch {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c c' : Cfg S Hole A Tok Fact Ob V i}
    {o : Σ i, S.Op i}
    (hI : Inv host sp O v₀ cs₀ c) (h : run host sp c (.dispatch o) = .ok c') : Inv host sp O v₀ cs₀ c' := by
  have hcl := run_live (fun _ e => by cases e) h
  simp only [run, hcl] at h
  have haw : awaiting c.obj.hist = c.obj.hist.inflight := rfl
  rw [haw] at h
  cases hinf : c.obj.hist.inflight with
  | some o' => rw [hinf] at h; cases h
  | none =>
    rw [hinf] at h
    rcases hres : c.res with ⟨j, _ | ⟨op, k⟩ | _⟩
    · simp only [hres] at h; cases h
    · simp only [hres] at h
      by_cases ho : o = ⟨j, op⟩
      · simp only [ho, ↓reduceIte] at h
        by_cases hg : dispatchGuard sp (c.admitView host) op = true
        · simp only [hg, ↓reduceIte] at h
          have hdd : decisionDead c.obj c.cites (c.admitView host) = [] := by
            cases hdd : decisionDead c.obj c.cites (c.admitView host) with
            | nil => rfl
            | cons d ds => simp [hdd] at h
          simp only [hdd] at h
          cases h
          have hg' : admitOp sp (viewAt host sp v₀ c.log) op = true := by
            rw [viewAt, ← hI.world, ← hI.spent]; exact hg
          refine ⟨AtEach.snoc.mpr ⟨hI.steps, ?_⟩, AtEach.snoc.mpr ⟨hI.authorized, ?_⟩, ?_,
            AtEach.snoc.mpr ⟨hI.paired, ?_, ?_, fun _ e => by cases e⟩,
            AtEach.snoc.mpr ⟨hI.final, fun hne => absurd (hI.ended.symm.trans hcl) hne⟩, AtEach.snoc.mpr ⟨hI.frozen, ?_⟩, ?_, ?_, ?_,
            hres ▸ hI.residual, ?_, by rw [endedOf_snoc_live (fun _ h => by cases h)]; exact hI.ended, AtEach.snoc.mpr ⟨hI.decided, ?_⟩,
            by simpa [citesOf, List.foldl_append] using hI.cites⟩
          · intro v' e; cases e
          · intro o' e; cases e; exact hg'
          · have hsp : spentBy sp (c.log ++ [Event.dispatch ⟨j, op⟩]) =
                spentBy sp c.log ++ (sp.consumes op).toList := by
              simp only [spentBy, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
              cases sp.consumes op <;> rfl
            unfold OnceSpent
            rw [hsp]
            cases hc : sp.consumes op with
            | none => simpa [OnceSpent] using hI.once
            | some t =>
              have hfresh : t ∉ spentBy sp c.log := by
                simp only [admitOp, viewAt, View.mask, hc, Bool.and_eq_true, Bool.not_eq_true',
                  decide_eq_false_iff_not] at hg'
                exact hg'.2.2
              simp only [Option.toList_some]
              exact List.nodup_append.mpr ⟨hI.once, (by simp),
                fun a ha b hb hab => by simp at hb; subst hb; subst hab; exact hfresh ha⟩
          · intro o' _
            have := congrArg (fun O => O.hist.inflight) hI.obj
            rw [hinf] at this
            exact this.symm
          · intro r e; cases e
          · intro j h f cs e; cases e
          · show { c.obj with hist := ⟨c.obj.hist.answered, some ⟨j, op⟩⟩ } = _
            rw [hI.obj]
            simp [planOf, histOf, List.foldl_append]
          · simpa [worldOf, List.foldl_append] using hI.world
          · show c.spent ++ (sp.consumes op).toList = _
            rw [hI.spent]
            simp only [spentBy, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
            cases sp.consumes op <;> rfl
          · intro o' e
            cases e
            rfl
          · intro o' e j' h' hd f hf
            cases e
            have hent := entered_iff.mp hd
            have hown : owner c.obj = some ⟨j', h'⟩ := by
              show entered c.obj.template c.obj.hist.answered true = _
              rw [hI.obj]
              exact hent
            have hz : (match owner c.obj with
                | some ⟨j, h⟩ => (c.cites j h).filter fun f => !(c.admitView host).holds f
                | none => []) = [] := hdd
            rw [hown] at hz
            have hf' : f ∈ c.cites j' h' := by rw [hI.cites]; exact hf
            have := List.filter_eq_nil_iff.mp hz f hf'
            rw [← hI.world]
            simpa [Cfg.admitView, View.mask] using this
        · simp only [hg] at h; cases h
      · simp only [ho, ↓reduceIte] at h; cases h
    · simp only [hres] at h; cases h

theorem inv_respond {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c c' : Cfg S Hole A Tok Fact Ob V i}
    {e : Entry S}
    (hI : Inv host sp O v₀ cs₀ c) (h : run host sp c (.respond e) = .ok c') : Inv host sp O v₀ cs₀ c' := by
  have hcl := run_live (fun _ e => by cases e) h
  simp only [run, hcl] at h
  cases hinf : c.obj.hist.inflight with
  | none => rw [hinf] at h; cases h
  | some o =>
    simp only [hinf] at h
    by_cases ho : (⟨e.1, e.2.1⟩ : Σ i, S.Op i) = o
    · simp only [ho, ↓reduceIte] at h
      cases hf : follow c.res e with
      | none => rw [hf] at h; cases h
      | some R =>
        rw [hf] at h
        cases h
        refine ⟨AtEach.snoc.mpr ⟨hI.steps, ?_⟩, AtEach.snoc.mpr ⟨hI.authorized, ?_⟩, ?_,
          AtEach.snoc.mpr ⟨hI.paired, ?_, ?_, fun _ e => by cases e⟩,
          AtEach.snoc.mpr ⟨hI.final, fun hne => absurd (hI.ended.symm.trans hcl) hne⟩, AtEach.snoc.mpr ⟨hI.frozen, ?_⟩, ?_, ?_, ?_, ?_, ?_,
          by rw [endedOf_snoc_live (fun _ h => by cases h)]; exact hI.ended, AtEach.snoc.mpr ⟨hI.decided, fun _ e => by cases e⟩,
            by simpa [citesOf, List.foldl_append] using hI.cites⟩
        · intro v' e; cases e
        · intro o' e; cases e
        · simpa [OnceSpent, spentBy, List.filterMap_append] using hI.once
        · intro o' e; cases e
        · intro r er
          cases er
          have := congrArg (fun O => O.hist.inflight) hI.obj
          rw [hinf] at this
          rw [← this, ho]
        · intro j h f cs e; cases e
        · show { c.obj with hist := ⟨c.obj.hist.answered ++ [e], none⟩ } = _
          rw [hI.obj]
          simp [planOf, histOf, List.foldl_append]
        · simpa [worldOf, List.foldl_append] using hI.world
        · simpa [spentBy, List.filterMap_append] using hI.spent
        · exact reach_append hI.residual (follow_reach hf)
        · intro o' e; cases e
    · simp only [ho, ↓reduceIte] at h; cases h

theorem inv_replan {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c c' : Cfg S Hole A Tok Fact Ob V i}
    {j : Ix} {h : Hole j} {f : Prot S Hole A j} {fs : List Fact}
    (hI : Inv host sp O v₀ cs₀ c) (hr : run host sp c (.replan h f fs) = .ok c') :
    Inv host sp O v₀ cs₀ c' := by
  have hcl := run_live (fun _ e => by cases e) hr
  simp only [run, hcl] at hr
  cases hmine : isMine c.obj.Ω h with
  | false => simp [hmine] at hr
  | true =>
    simp only [hmine, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases hz : frozenHole c.obj = some ⟨j, h⟩
    · simp only [hz, ↓reduceIte] at hr
      cases hi : c.obj.hist.inflight <;> simp [hi] at hr
    · simp only [hz, ↓reduceIte] at hr
      cases hadv : advance ⟨i, (c.obj.replan (setHole c.obj.σ h f)).current⟩ c.obj.hist.answered with
      | none => simp [hadv] at hr
      | some R =>
        simp only [hadv] at hr
        by_cases hn : nextIs R c.obj.hist.inflight = true
        · simp only [hn, ↓reduceIte] at hr
          cases hr
          refine ⟨AtEach.snoc.mpr ⟨hI.steps, ?_⟩, AtEach.snoc.mpr ⟨hI.authorized, ?_⟩, ?_,
            AtEach.snoc.mpr ⟨hI.paired, ?_, ?_, fun _ e => by cases e⟩,
            AtEach.snoc.mpr ⟨hI.final, fun hne => absurd (hI.ended.symm.trans hcl) hne⟩, AtEach.snoc.mpr ⟨hI.frozen, ?_⟩, ?_, ?_, ?_,
            advance_reach hadv, ?_, by rw [endedOf_snoc_live (fun _ h => by cases h)]; exact hI.ended, AtEach.snoc.mpr ⟨hI.decided, fun _ e => by cases e⟩,
            by show setCites c.cites h fs = _; rw [hI.cites]; simp [citesOf, List.foldl_append]⟩
          · intro v' e; cases e
          · intro o' e; cases e
          · simpa [OnceSpent, spentBy, List.filterMap_append] using hI.once
          · intro o' e; cases e
          · intro r e; cases e
          · intro j' h' f' cs' e
            cases e
            intro hd
            apply hz
            have := entered_iff.mp hd
            show entered c.obj.template c.obj.hist.answered c.obj.hist.inflight.isSome = _
            rw [hI.obj]
            exact this
          · show c.obj.replan (setHole c.obj.σ h f) = _
            rw [hI.obj]
            simp [Open.replan, planOf, histOf, List.foldl_append]
          · simpa [worldOf, List.foldl_append] using hI.world
          · simpa [spentBy, List.filterMap_append] using hI.spent
          · intro o ho
            exact nextIs_isCall (by rw [← ho]; exact hn)
        · simp only [hn] at hr; cases hr

theorem run_abandon_inv {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {o : Σ i, S.Op i}
    (h : run host sp c (.abandon o) = .ok c') :
    closedBy c = none ∧ c.obj.hist.inflight = some o ∧
      c' = { c with ended := some o, log := c.log ++ [.abandon o] } := by
  have hcl := run_live (fun _ e => by cases e) h
  have haw : awaiting c.obj.hist = c.obj.hist.inflight := rfl
  simp only [run, hcl, haw] at h
  cases hinf : c.obj.hist.inflight with
  | none => simp [hinf] at h
  | some o' =>
    simp only [hinf] at h
    by_cases ho : o = o'
    · subst ho
      simp only [↓reduceIte] at h
      cases h
      exact ⟨hcl, rfl, rfl⟩
    · simp [ho] at h

theorem inv_abandon {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c c' : Cfg S Hole A Tok Fact Ob V i}
    {o : Σ i, S.Op i}
    (hI : Inv host sp O v₀ cs₀ c) (h : run host sp c (.abandon o) = .ok c') : Inv host sp O v₀ cs₀ c' := by
  obtain ⟨hcl, hinf, rfl⟩ := run_abandon_inv h
  refine ⟨AtEach.snoc.mpr ⟨hI.steps, fun _ e => by cases e⟩,
    AtEach.snoc.mpr ⟨hI.authorized, fun _ e => by cases e⟩, ?_,
    AtEach.snoc.mpr ⟨hI.paired, (fun _ e => by cases e), (fun _ e => by cases e), ?_⟩,
    AtEach.snoc.mpr ⟨hI.final, fun hne => absurd (hI.ended.symm.trans hcl) hne⟩, AtEach.snoc.mpr ⟨hI.frozen, fun _ _ _ _ e => by cases e⟩, ?_, ?_, ?_,
    hI.residual, hI.next, ?_, AtEach.snoc.mpr ⟨hI.decided, fun _ e => by cases e⟩,
    by simpa [citesOf, List.foldl_append] using hI.cites⟩
  · simpa [OnceSpent, spentBy, List.filterMap_append] using hI.once
  · intro o' e
    cases e
    have := congrArg (fun O => O.hist.inflight) hI.obj
    rw [hinf] at this
    exact this.symm
  · simpa [planOf, histOf, List.foldl_append] using hI.obj
  · simpa [worldOf, List.foldl_append] using hI.world
  · simpa [spentBy, List.filterMap_append] using hI.spent
  · simp [endedOf, List.foldl_append]

/-- **The induction step**: every event the runner accepts preserves the invariant. -/
public theorem step_inv {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c c' : Cfg S Hole A Tok Fact Ob V i}
    {ev : Event S Hole A Fact V}
    (hI : Inv host sp O v₀ cs₀ c) (h : run host sp c ev = .ok c') : Inv host sp O v₀ cs₀ c' := by
  cases ev with
  | world v => exact inv_world hI h
  | replan h f fs => exact inv_replan hI h
  | dispatch o => exact inv_dispatch hI h
  | respond e => exact inv_respond hI h
  | abandon o => exact inv_abandon hI h

-- Each guard is load-bearing in the induction step: the stored proof fails without it.
#tooth step_inv by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => true
#tooth step_inv by mutation spendOn := fun {_ _ _ _ _} _ spent {_} _ => spent
#tooth step_inv by mutation frozenHole := fun {_ _ _ _} [_] {_ _ _ _} _ => none
#tooth step_inv by mutation closedBy := fun {_ _ _ _ _ _ _ _ _} _ => none
#tooth step_inv by mutation decisionDead := fun {_ _ _ _ _ _ _ _ _} _ _ _ => []

/-- **The runner refines its specification**: every configuration reachable from `Cfg.init O v₀`
satisfies the invariant. -/
public theorem refines {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c : Cfg S Hole A Tok Fact Ob V i}
    (h : Reachable host sp (Cfg.init O v₀ cs₀) c) : Inv host sp O v₀ cs₀ c := by
  induction h with
  | init => exact inv_init host sp O v₀
  | step ev _ hs ih => exact step_inv ih hs

/-- Every reachable configuration's log is `Legal`. -/
public theorem reachable_legal {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c : Cfg S Hole A Tok Fact Ob V i}
    (h : Reachable host sp (Cfg.init O v₀ cs₀) c) : Legal host sp O v₀ cs₀ c.log :=
  (refines h).legal

/-- **A dispatch that uses a selected choice finds the choice usable at its own view** (Astra's
`AdmitOperation ∧ UsesChoice → Usable`, `astra/ASTRA-SELECTION-20261031.md` §7.3): if the hole a
dispatched call enters was decided for candidate `cand` of slot `Sl` (its decision cites `cand`'s
supports, as `resolveEvent`/`resolveEventBy` record them) and `cand` passes the judge, then `cand` is
usable at the world of that dispatch, however the world moved since the selection. -/
public theorem dispatch_usable_choice {Cand : Type} {host : Host V Tok Fact}
    {sp : Spec S Tok Fact Ob} {i : Ix} {O : Open S Hole A Tok Fact Ob i} {v₀ : V}
    {c : Cfg S Hole A Tok Fact Ob V i} (hc : Reachable host sp (Cfg.init O v₀ cs₀) c) {n : Nat}
    {o : Σ i, S.Op i} (hn : c.log[n]? = some (.dispatch o)) {j : Ix} {h : Hole j}
    (hd : Dispatched O.template ⟨(histOf (c.log.take n)).answered, some o⟩ j h)
    (Sl : Slot Fact Cand) (cand : Cand) (hcite : citesOf cs₀ (c.log.take n) j h = Sl.supports cand)
    (hjudge : Sl.judge cand = true) :
    Sl.usable (host.view (worldOf v₀ (c.log.take n))).holds cand = true := by
  have hheld := (reachable_legal hc).decided n _ hn o rfl j h hd
  rw [hcite] at hheld
  exact (Slot.usable_iff Sl _ cand).2 ⟨hjudge, hheld⟩

/-! ## What a replan may change, and the continuation clause -/

theorem run_replan_inv {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {j : Ix} {h : Hole j} {f : Prot S Hole A j} {fs : List Fact}
    (hr : run host sp c (.replan h f fs) = .ok c') :
    isMine c.obj.Ω h = true ∧ frozenHole c.obj ≠ some ⟨j, h⟩ ∧
      advance ⟨i, (c.obj.replan (setHole c.obj.σ h f)).current⟩ c.obj.hist.answered = some c'.res ∧
      c'.obj = c.obj.replan (setHole c.obj.σ h f) ∧ c'.world = c.world ∧ c'.spent = c.spent ∧
      c'.log = c.log ++ [Event.replan h f fs] ∧ c'.ended = c.ended ∧
      c'.cites = setCites c.cites h fs := by
  have hcl := run_live (fun _ e => by cases e) hr
  simp only [run, hcl] at hr
  cases hmine : isMine c.obj.Ω h with
  | false => simp [hmine] at hr
  | true =>
    simp only [hmine, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases hz : frozenHole c.obj = some ⟨j, h⟩
    · simp only [hz, ↓reduceIte] at hr
      cases hi : c.obj.hist.inflight <;> simp [hi] at hr
    · simp only [hz, ↓reduceIte] at hr
      cases hadv : advance ⟨i, (c.obj.replan (setHole c.obj.σ h f)).current⟩ c.obj.hist.answered with
      | none => simp [hadv] at hr
      | some R =>
        simp only [hadv] at hr
        by_cases hn : nextIs R c.obj.hist.inflight = true
        · simp only [hn, ↓reduceIte] at hr
          cases hr
          exact ⟨rfl, hz, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simp only [hn] at hr; cases hr

/-- **An accepted replan is guarded**: it satisfies the open object's own guard `Open.Replan` (it
agrees with the old plan on every hole the history has entered) and keeps the accepted history. -/
public theorem run_replan_guard {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {j : Ix} {h : Hole j} {f : Prot S Hole A j} {fs : List Fact}
    (hr : run host sp c (.replan h f fs) = .ok c') :
    c.obj.Replan c'.obj.σ ∧ c'.obj.hist = c.obj.hist := by
  obtain ⟨_, hz, _, hobj, _⟩ := run_replan_inv hr
  rw [hobj]
  refine ⟨fun j' h' hd => ?_, rfl⟩
  have he := entered_iff.mp hd
  have hne : (⟨j', h'⟩ : Σ j, Hole j) ≠ ⟨j, h⟩ := fun e => hz (by
    show entered c.obj.template c.obj.hist.answered c.obj.hist.inflight.isSome = _
    rw [he, e])
  exact mine_setHole_ne c.obj.Ω c.obj.σ h f hne

/-- **Before dispatch, a replan of a hole the history has not entered is accepted**, whatever the
filling, at every reachable configuration (with a call in flight or not). -/
public theorem replan_accepted {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c : Cfg S Hole A Tok Fact Ob V i}
    (hI : Inv host sp O v₀ cs₀ c) (hlive : c.ended = none) {j : Ix} {h : Hole j}
    (f : Prot S Hole A j) (fs : List Fact) (hmine : isMine c.obj.Ω h = true)
    (hnd : ¬ Dispatched c.obj.template c.obj.hist j h) :
    ∃ c', run host sp c (.replan h f fs) = .ok c' ∧
      Reach (fill c.obj.Ω (setHole c.obj.σ h f) c.obj.template) c.obj.hist.answered c'.res := by
  have hz : frozenHole c.obj ≠ some ⟨j, h⟩ := fun e => hnd (entered_iff.mpr e)
  have hg : ∀ j' (h' : Hole j'), Dispatched c.obj.template c.obj.hist j' h' →
      (setHole c.obj.σ h f).mine c.obj.Ω j' h' = c.obj.σ.mine c.obj.Ω j' h' := by
    intro j' h' hd
    apply mine_setHole_ne
    intro e
    cases e
    exact hnd hd
  have hs : Started (fill c.obj.Ω (setHole c.obj.σ h f) c.obj.template) c.obj.hist :=
    resubst_preserves_started hI.started hg
  obtain ⟨R, hR, hn⟩ : ∃ R, Reach (fill c.obj.Ω (setHole c.obj.σ h f) c.obj.template)
      c.obj.hist.answered R ∧ nextIs R c.obj.hist.inflight = true := by
    cases ho : c.obj.hist.inflight with
    | none =>
      rw [show c.obj.hist = ⟨c.obj.hist.answered, none⟩ by rw [← ho]] at hs
      cases hs with
      | settled hr => exact ⟨_, hr, rfl⟩
    | some o =>
      rw [show c.obj.hist = ⟨c.obj.hist.answered, some o⟩ by rw [← ho]] at hs
      obtain ⟨R, hr, hc⟩ := started_some_iff.mp hs
      exact ⟨R, hr, isCall_nextIs hc⟩
  have hadv : advance ⟨i, (c.obj.replan (setHole c.obj.σ h f)).current⟩ c.obj.hist.answered =
      some R := reach_advance hR
  refine ⟨{ c with
      obj := c.obj.replan (setHole c.obj.σ h f)
      res := R
      cites := setCites c.cites h fs
      log := c.log ++ [Event.replan h f fs] }, ?_, hR⟩
  have hcl : closedBy c = none := hlive
  simp only [run, hcl, hmine, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hz, hadv, hn]

/-- **A compatible currently admitted replacement takes the next step**: before dispatch, if the
replanned protocol's next call after the answered history is admitted at the current view, the
replan is accepted and so is that call's dispatch. -/
public theorem replace_then_dispatch {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c : Cfg S Hole A Tok Fact Ob V i}
    (hI : Inv host sp O v₀ cs₀ c) (hlive : c.ended = none) (hnone : c.obj.hist.inflight = none)
    {j : Ix} {h : Hole j}
    (f : Prot S Hole A j) (fs : List Fact) (hmine : isMine c.obj.Ω h = true)
    (hnd : ¬ Dispatched c.obj.template c.obj.hist j h) {j' : Ix} {op : S.Op j'}
    {k : (r : S.Resp op) → Prot S Hole A (S.next op r)}
    (hR : Reach (fill c.obj.Ω (setHole c.obj.σ h f) c.obj.template) c.obj.hist.answered
      ⟨j', .call op k⟩)
    (hadm : admitOp sp (c.admitView host) op = true)
    (hdec : decisionDead (c.obj.replan (setHole c.obj.σ h f)) (setCites c.cites h fs)
      (c.admitView host) = []) :
    ∃ c', run host sp c (.replan h f fs) = .ok c' ∧ c'.res = ⟨j', .call op k⟩ ∧
      ∃ c'', run host sp c' (.dispatch ⟨j', op⟩) = .ok c'' := by
  obtain ⟨c', hc', _⟩ := replan_accepted hI hlive f fs hmine hnd
  obtain ⟨_, _, hadv, hobj, hw, hsp, _⟩ := run_replan_inv hc'
  have hres : c'.res = ⟨j', .call op k⟩ := by
    have := reach_advance hR
    rw [show (fill c.obj.Ω (setHole c.obj.σ h f) c.obj.template) =
      (c.obj.replan (setHole c.obj.σ h f)).current from rfl] at this
    rw [this] at hadv
    exact (Option.some.inj hadv).symm
  have hinf : c'.obj.hist.inflight = none := by rw [hobj]; exact hnone
  have hg : dispatchGuard sp (c'.admitView host) op = true := by
    simp only [Cfg.admitView, hw, hsp]; exact hadm
  refine ⟨c', hc', hres, ?_⟩
  have haw : awaiting c'.obj.hist = c'.obj.hist.inflight := rfl
  have hcl : closedBy c' = none := (run_replan_inv hc').2.2.2.2.2.2.2.1.trans hlive
  have hdd : decisionDead c'.obj c'.cites (c'.admitView host) = [] := by
    rw [hobj, (run_replan_inv hc').2.2.2.2.2.2.2.2]
    simp only [Cfg.admitView, hw, hsp]
    exact hdec
  simp only [run, hcl, haw, hinf, hres, ↓reduceIte, hg, hdd]
  exact ⟨_, rfl⟩

/-- **After dispatch, no new commitment**: with a call in flight every dispatch is refused, naming
the call in flight. -/
public theorem inflight_busy {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c : Cfg S Hole A Tok Fact Ob V i} (hlive : c.ended = none) {o : Σ i, S.Op i}
    (ho : c.obj.hist.inflight = some o)
    (o' : Σ i, S.Op i) : run host sp c (.dispatch o') = .error (.busy o) := by
  have haw : awaiting c.obj.hist = c.obj.hist.inflight := rfl
  have hcl : closedBy c = none := hlive
  simp only [run, hcl, haw, ho]

/-- **The in-flight call's hole is not replanned, by name**: with a call in flight, a replan of the
hole the history has entered is refused `replacesInflight`. -/
public theorem inflight_replan_refused {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c : Cfg S Hole A Tok Fact Ob V i} (hlive : c.ended = none) {o : Σ i, S.Op i}
    (ho : c.obj.hist.inflight = some o)
    {j : Ix} {h : Hole j} (f : Prot S Hole A j) (fs : List Fact) (hmine : isMine c.obj.Ω h = true)
    (hd : Dispatched c.obj.template c.obj.hist j h) :
    run host sp c (.replan h f fs) = .error (.replacesInflight o ⟨j, h⟩) := by
  have hz : frozenHole c.obj = some ⟨j, h⟩ := entered_iff.mp hd
  have hcl : closedBy c = none := hlive
  simp [run, hcl, hmine, hz, ho]

/-- An answered hole is not replanned either, by name. -/
public theorem answered_replan_refused {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c : Cfg S Hole A Tok Fact Ob V i} (hlive : c.ended = none) (ho : c.obj.hist.inflight = none)
    {j : Ix} {h : Hole j} (f : Prot S Hole A j) (fs : List Fact) (hmine : isMine c.obj.Ω h = true)
    (hd : Dispatched c.obj.template c.obj.hist j h) :
    run host sp c (.replan h f fs) = .error (.replacesAnswered ⟨j, h⟩) := by
  have hz : frozenHole c.obj = some ⟨j, h⟩ := entered_iff.mp hd
  have hcl : closedBy c = none := hlive
  simp [run, hcl, hmine, hz, ho]

-- The no-new-commitment guard is what refuses a dispatch while a reply is missing.
#tooth inflight_busy by mutation awaiting := fun {_ _} _ => none
-- Acceptance of a safe replacement rests on the replan's consistency check passing.
#tooth replan_accepted by mutation nextIs := fun {_ _ _ _} [_] _ _ => false
#tooth replace_then_dispatch by mutation dispatchGuard := fun {_ _ _ _ _} _ _ {_} _ => false

/-! ## Abandonment: the ending a lost reply may have -/

/-- **A call in flight can be abandoned** (and only the call in flight). -/
public theorem abandon_accepted {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c : Cfg S Hole A Tok Fact Ob V i} (hlive : c.ended = none) {o : Σ i, S.Op i}
    (ho : c.obj.hist.inflight = some o) :
    run host sp c (.abandon o) = .ok { c with ended := some o, log := c.log ++ [.abandon o] } := by
  have haw : awaiting c.obj.hist = c.obj.hist.inflight := rfl
  have hcl : closedBy c = none := hlive
  simp only [run, hcl, haw, ho, ↓reduceIte]

/-- **Abandonment keeps the obligation**: the abandoned call stays in the history, dispatched and
never answered, so every obligation its dispatch established still stands, and the run is ended by
it. -/
public theorem abandon_keeps_obligation {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {o : Σ i, S.Op i}
    (h : run host sp c (.abandon o) = .ok c') :
    c'.obj.hist = c.obj.hist ∧ c'.obj.hist.inflight = some o ∧ c'.ended = some o ∧
      c'.spent = c.spent ∧ ∀ ob ∈ sp.establishes o.2, ob ∈ c'.obj.hist.established sp := by
  obtain ⟨_, hinf, rfl⟩ := run_abandon_inv h
  refine ⟨rfl, hinf, rfl, rfl, fun ob hob => ?_⟩
  obtain ⟨j, op⟩ := o
  simp only [Hist.established, hinf, List.mem_append]
  exact .inr hob

/-- **After abandonment, no new commitment**: every event but a world move is refused, naming the
abandoned call: no dispatch, no reply (a late one included), no replan, no second abandonment. -/
public theorem ended_frozen {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c : Cfg S Hole A Tok Fact Ob V i} {o : Σ i, S.Op i} (he : c.ended = some o)
    (ev : Event S Hole A Fact V) (hev : ∀ v, ev ≠ .world v) :
    run host sp c ev = .error (.abandoned o) := by
  have hcl : closedBy c = some o := he
  cases ev with
  | world v => exact absurd rfl (hev v)
  | _ => simp only [run, hcl]

#tooth ended_frozen by mutation closedBy := fun {_ _ _ _ _ _ _ _ _} _ => none

/-! ## A missing reply licenses no new commitment -/

theorem step_inflight {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c c' : Cfg S Hole A Tok Fact Ob V i} {o : Σ i, S.Op i} (ho : c.obj.hist.inflight = some o)
    {ev : Event S Hole A Fact V} (hev : ev.isRespond = false) (h : run host sp c ev = .ok c') :
    c'.obj.hist = c.obj.hist ∧ c'.spent = c.spent ∧ c'.log = c.log ++ [ev] ∧
      dispatchesOf (c.log ++ [ev]) = dispatchesOf c.log := by
  cases ev with
  | respond e => cases hev
  | dispatch o' =>
    have haw : awaiting c.obj.hist = c.obj.hist.inflight := rfl
    cases hcl : closedBy c with
    | some x => simp [run, hcl] at h
    | none => simp [run, hcl, haw, ho] at h
  | abandon o' =>
    obtain ⟨_, _, rfl⟩ := run_abandon_inv h
    exact ⟨rfl, rfl, rfl, by simp [dispatchesOf, List.filterMap_append]⟩
  | world v =>
    simp only [run] at h
    by_cases ha : host.allowed c.world v = true
    · simp only [ha, ↓reduceIte] at h
      cases h
      exact ⟨rfl, rfl, rfl, by simp [dispatchesOf, List.filterMap_append]⟩
    · simp only [ha] at h; cases h
  | replan h' f fs =>
    obtain ⟨_, _, _, hobj, _, hsp, hlog, _⟩ := run_replan_inv h
    exact ⟨by rw [hobj]; rfl, hsp, hlog, by simp [dispatchesOf, List.filterMap_append]⟩

public theorem session_reachable {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {c₀ c : Cfg S Hole A Tok Fact Ob V i} (hc : Reachable host sp c₀ c)
    (evs : List (Event S Hole A Fact V)) : Reachable host sp c₀ (session host sp c evs).1 := by
  induction evs generalizing c with
  | nil => exact hc
  | cons ev evs ih =>
    simp only [session]
    cases h : run host sp c ev with
    | ok c' => exact ih (.step ev hc h)
    | error w => exact ih hc

/-- **A missing reply licenses no new commitment**: from a reachable configuration with a call in
flight, any events but a reply (world moves, replans, proposed dispatches, in any number and order)
leave the history, the spent tokens and the log's dispatches as they were, and the call in flight
stays the residual's next call. -/
public theorem lost_reply_frozen {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} {v₀ : V} {c : Cfg S Hole A Tok Fact Ob V i}
    (hc : Reachable host sp (Cfg.init O v₀ cs₀) c) {o : Σ i, S.Op i}
    (ho : c.obj.hist.inflight = some o) (evs : List (Event S Hole A Fact V))
    (hno : ∀ e ∈ evs, e.isRespond = false) :
    (session host sp c evs).1.obj.hist = c.obj.hist ∧ (session host sp c evs).1.spent = c.spent ∧
      dispatchesOf (session host sp c evs).1.log = dispatchesOf c.log ∧
      IsCall (session host sp c evs).1.res o := by
  have key : ∀ (evs : List (Event S Hole A Fact V)) (c : Cfg S Hole A Tok Fact Ob V i),
      c.obj.hist.inflight = some o → (∀ e ∈ evs, e.isRespond = false) →
      (session host sp c evs).1.obj.hist = c.obj.hist ∧ (session host sp c evs).1.spent = c.spent ∧
        dispatchesOf (session host sp c evs).1.log = dispatchesOf c.log := by
    intro evs
    induction evs with
    | nil => intro c _ _; exact ⟨rfl, rfl, rfl⟩
    | cons ev evs ih =>
      intro c ho hno
      simp only [session]
      cases h : run host sp c ev with
      | error w => exact ih c ho (fun e he => hno e (List.mem_cons_of_mem _ he))
      | ok c' =>
        obtain ⟨hh, hs, hl, hd⟩ := step_inflight ho (hno ev List.mem_cons_self) h
        obtain ⟨hh', hs', hd'⟩ := ih c' (by rw [hh]; exact ho)
          (fun e he => hno e (List.mem_cons_of_mem _ he))
        exact ⟨hh'.trans hh, hs'.trans hs, by rw [hd', hl, hd]⟩
  obtain ⟨hh, hs, hd⟩ := key evs c ho hno
  refine ⟨hh, hs, hd, ?_⟩
  exact (refines (session_reachable hc evs)).next o (by rw [hh]; exact ho)

#assert_axioms abandon_accepted abandon_keeps_obligation ended_frozen
#assert_axioms refines reachable_legal step_inv dispatch_usable_choice run_replan_guard replan_accepted
  replace_then_dispatch inflight_busy inflight_replan_refused answered_replan_refused lost_reply_frozen
  entered_iff advance_reach reach_advance

end

end Obend.Run
