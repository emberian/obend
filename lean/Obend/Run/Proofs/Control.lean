module
/-
# Obend.Run.Proofs.Control — the controlled runner: what each preset chooses, who may decide

- The presets' choice laws, of `propose` alone: `firstUsable_law` (kept or chosen exactly the first
  usable candidate of the domain; `select_prefix` certifies it by the rejected prefix),
  `incumbentFirst_law` (kept exactly while keepable, otherwise the first usable),
  `chooserRequired_law` (never chooses; kept exactly while keepable; otherwise awaits exactly when
  some candidate of the domain is usable). Across presets: `propose_chosen` (a chosen candidate is
  permitted, usable, and the preset is automatic) and `nothingAdmissible_iff` (the outcome is
  `nothingAdmissible d` exactly when no candidate of the domain is usable, and then `d` is the exact
  diagnostics), with `diagnose_usable`, `diagnose_rejected`, `diagnose_dead` saying what each
  diagnosis means.
- The controlled runner is the runner: `creachable_reachable`, `creachable_legal`.
- Its log of decisions: `creachable_authorized` (every decision is of a permitted candidate usable
  at the world it was made at; a principal's decision was made while the principal held the office;
  a policy's decision is never a `chooserRequired` slot's), `creachable_revisions` (a slot's revision
  is the number of its decisions), and `creachable_cites` (each controlled hole's decision cites
  what its last decision's tenure says). From the last and the runner's dispatch guard:
  `office_rechecked` (a call in a hole decided `whileInOffice` by `p` is dispatched only while `p`
  holds the office).
-/
public import Obend.Run.Control
public import Obend.Run.Proofs.Invariant
public import Obend.Tactic.Tooth
import all Obend.Run.Runner
import all Obend.Run.Control
import all Obend.Run.Proofs.Invariant

namespace Obend.Run.Control

open Obend.Slot Obend.Slot.Protocol

/-! ## Diagnoses -/

section
variable {P Fact Cand : Type} [DecidableEq Cand]

omit [DecidableEq Cand] in
public theorem diagnose_usable (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) :
    diagnose S holds c = .usable ↔ S.usable holds c = true := by
  unfold diagnose
  rw [usable_iff, ← dead_eq_nil_iff]
  cases hj : S.judge c
  · simp
  · cases S.dead holds c <;> simp

omit [DecidableEq Cand] in
public theorem diagnose_rejected (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) :
    diagnose S holds c = .rejected ↔ S.judge c = false := by
  unfold diagnose
  cases hj : S.judge c
  · simp
  · cases S.dead holds c <;> simp

omit [DecidableEq Cand] in
public theorem diagnose_dead (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) (d : List Fact) :
    diagnose S holds c = .dead d ↔ S.judge c = true ∧ d ≠ [] ∧ d = S.dead holds c := by
  unfold diagnose
  cases hj : S.judge c
  · simp
  · simp only [ite_true]
    cases hd : S.dead holds c with
    | nil => simp
    | cons f t =>
      constructor
      · intro h; cases h; simp
      · rintro ⟨_, _, rfl⟩; rfl

/-! ## The presets' choice laws -/

theorem keepable_some {S : Slot Fact Cand} {D : Descriptor P Fact Cand} {holds : Fact → Bool}
    {latched : Bool} {stored : Option Cand} (h : keepable S D holds latched stored = true) :
    ∃ s, stored = some s ∧ s ∈ D.domain ∧ S.usable holds s = true ∧ latched = false := by
  cases stored with
  | none => simp [keepable] at h
  | some s =>
    simp only [keepable, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    exact ⟨s, rfl, h.1.1, h.1.2, h.2⟩

omit [DecidableEq Cand] in
theorem select_none {S : Slot Fact Cand} {holds : Fact → Bool} {order : List Cand}
    {w : Slot.Refusal Fact Cand} (h : S.select holds order = .error w) :
    ∀ c ∈ order, S.usable holds c = false := (select_error h).1

/-- What a chosen candidate is, whatever the preset: in the domain, usable, the first usable of the
domain, and chosen by an automatic preset. -/
public theorem propose_chosen {S : Slot Fact Cand} {D : Descriptor P Fact Cand} {holds : Fact → Bool}
    {stored : Option Cand} {latched : Bool} {c : Cand}
    (h : propose S D holds stored latched = .chosen c) :
    c ∈ D.domain ∧ S.usable holds c = true ∧ S.select holds D.domain = .ok c ∧
      D.preset ≠ .chooserRequired := by
  unfold propose at h
  cases hp : D.preset <;> rw [hp] at h <;> simp only at h
  · cases hs : S.select holds D.domain with
    | error w => rw [hs] at h; cases h
    | ok c' =>
      rw [hs] at h
      by_cases e : stored = some c'
      · simp only [e, ↓reduceIte] at h; cases h
      · simp only [e, ↓reduceIte] at h
        obtain rfl : c' = c := by injection h
        exact ⟨(select_ok hs).1, (select_ok hs).2.1, rfl, by simp⟩
  · have fallback : ∀ (x : Outcome Fact Cand),
        (match S.select holds D.domain with
          | .ok c => Outcome.chosen c
          | .error _ => .nothingAdmissible (diagnostics S D holds)) = .chosen c →
        c ∈ D.domain ∧ S.usable holds c = true ∧ S.select holds D.domain = .ok c := by
      intro _ h
      cases hs : S.select holds D.domain with
      | error w => rw [hs] at h; cases h
      | ok c' =>
        rw [hs] at h
        obtain rfl : c' = c := by injection h
        exact ⟨(select_ok hs).1, (select_ok hs).2.1, rfl⟩
    split at h
    · cases h
    · exact ⟨(fallback (.kept c) h).1, (fallback (.kept c) h).2.1, (fallback (.kept c) h).2.2, by simp⟩
  · split at h
    · cases h
    · cases hs : S.select holds D.domain <;> rw [hs] at h <;> cases h

/-- What a kept candidate is: the stored one, in the domain and usable; under the automatic
retaining presets also not latched. -/
public theorem propose_kept {S : Slot Fact Cand} {D : Descriptor P Fact Cand} {holds : Fact → Bool}
    {stored : Option Cand} {latched : Bool} {c : Cand}
    (h : propose S D holds stored latched = .kept c) :
    stored = some c ∧ c ∈ D.domain ∧ S.usable holds c = true := by
  unfold propose at h
  cases hp : D.preset <;> rw [hp] at h <;> simp only at h
  · cases hs : S.select holds D.domain with
    | error w => rw [hs] at h; cases h
    | ok c' =>
      rw [hs] at h
      by_cases e : stored = some c'
      · simp only [e, ↓reduceIte] at h
        obtain rfl : c' = c := by injection h
        exact ⟨e, (select_ok hs).1, (select_ok hs).2.1⟩
      · simp only [e, ↓reduceIte] at h; cases h
  all_goals
    split at h
    · rename_i s hk
      cases h
      obtain ⟨_, e, hd, hu, _⟩ := keepable_some hk
      cases e
      exact ⟨rfl, hd, hu⟩
    · first
        | (cases hs : S.select holds D.domain <;> rw [hs] at h <;> cases h)

/-- **First-usable**: the outcome is the first usable candidate of the domain, kept when it is the
stored one, chosen otherwise; nothing admissible when none is usable. -/
public theorem firstUsable_law {S : Slot Fact Cand} {D : Descriptor P Fact Cand} (hp : D.preset = .firstUsable)
    (holds : Fact → Bool) (stored : Option Cand) (latched : Bool) (c : Cand) :
    (propose S D holds stored latched = .kept c ∨ propose S D holds stored latched = .chosen c) ↔
      S.select holds D.domain = .ok c := by
  unfold propose
  rw [hp]
  simp only
  cases hs : S.select holds D.domain with
  | error w => simp
  | ok c' =>
    by_cases e : stored = some c' <;> simp [e]

/-- **Incumbent-first**: the stored choice is kept exactly while it is keepable (in the domain,
usable, not latched); otherwise the first usable candidate of the domain is chosen. -/
public theorem incumbentFirst_law {S : Slot Fact Cand} {D : Descriptor P Fact Cand}
    (hp : D.preset = .incumbentFirst) (holds : Fact → Bool) (stored : Option Cand) (latched : Bool)
    (c : Cand) :
    (propose S D holds stored latched = .kept c ↔
        stored = some c ∧ keepable S D holds latched stored = true) ∧
      (propose S D holds stored latched = .chosen c ↔
        keepable S D holds latched stored = false ∧ S.select holds D.domain = .ok c) := by
  unfold propose
  rw [hp]
  simp only
  cases stored with
  | none =>
    simp only [keepable]
    cases hs : S.select holds D.domain <;> simp
  | some s =>
    cases hk : keepable S D holds latched (some s)
    · cases hs : S.select holds D.domain <;> simp
    · simp

/-- **Chooser-required**: the policy never chooses; it keeps the stored choice exactly while it is
keepable; otherwise it awaits the chooser exactly when some candidate of the domain is usable, with
the exact diagnostics. -/
public theorem chooserRequired_law {S : Slot Fact Cand} {D : Descriptor P Fact Cand}
    (hp : D.preset = .chooserRequired) (holds : Fact → Bool) (stored : Option Cand) (latched : Bool) :
    (∀ c, propose S D holds stored latched ≠ .chosen c) ∧
      (∀ c, propose S D holds stored latched = .kept c ↔
        stored = some c ∧ keepable S D holds latched stored = true) ∧
      (∀ d, propose S D holds stored latched = .awaiting d ↔
        keepable S D holds latched stored = false ∧ (∃ c ∈ D.domain, S.usable holds c = true) ∧
          d = diagnostics S D holds) := by
  have usable_iff_select : (∃ c ∈ D.domain, S.usable holds c = true) ↔
      ∃ c, S.select holds D.domain = .ok c := by
    constructor
    · rintro ⟨c, hc, hu⟩; exact select_some hc hu
    · rintro ⟨c, hs⟩; exact ⟨c, (select_ok hs).1, (select_ok hs).2.1⟩
  unfold propose
  rw [hp]
  simp only
  rw [usable_iff_select]
  cases stored with
  | none =>
    simp only [keepable]
    cases hs : S.select holds D.domain <;> simp [eq_comm]
  | some s =>
    cases hk : keepable S D holds latched (some s)
    · cases hs : S.select holds D.domain <;> simp [eq_comm]
    · simp

/-- **Nothing admissible, honestly**, whatever the preset: the outcome is `nothingAdmissible d`
exactly when no candidate of the domain is usable, and `d` is then every candidate of the domain
with its exact diagnosis. -/
public theorem nothingAdmissible_iff (S : Slot Fact Cand) (D : Descriptor P Fact Cand) (holds : Fact → Bool)
    (stored : Option Cand) (latched : Bool) (d : List (Cand × Diag Fact)) :
    propose S D holds stored latched = .nothingAdmissible d ↔
      (∀ c ∈ D.domain, S.usable holds c = false) ∧ d = diagnostics S D holds := by
  have none_keepable : (∀ c ∈ D.domain, S.usable holds c = false) →
      keepable S D holds latched stored = false := by
    intro hn
    cases hk : keepable S D holds latched stored
    · rfl
    · obtain ⟨s, _, hd, hu, _⟩ := keepable_some hk
      rw [hn s hd] at hu; cases hu
  constructor
  · intro h
    unfold propose at h
    have sel : ∀ (x : Outcome Fact Cand), x = .nothingAdmissible d →
        ∀ w, S.select holds D.domain = .error w →
          (∀ c ∈ D.domain, S.usable holds c = false) := fun _ _ w hs => select_none hs
    cases hp : D.preset <;> rw [hp] at h <;> simp only at h
    · cases hs : S.select holds D.domain with
      | ok c => rw [hs] at h; by_cases e : stored = some c <;> simp [e] at h
      | error w => rw [hs] at h; cases h; exact ⟨select_none hs, rfl⟩
    all_goals
      split at h
      · cases h
      · cases hs : S.select holds D.domain with
        | ok c => rw [hs] at h; cases h
        | error w => rw [hs] at h; cases h; exact ⟨select_none hs, rfl⟩
  · rintro ⟨hn, rfl⟩
    have hs : S.select holds D.domain = .error (D.domain.map fun c => (c, S.dead holds c)) := by
      unfold Slot.select
      rw [show S.alternatives holds D.domain = [] from
        List.filter_eq_nil_iff.2 fun c hc => by simp [hn c hc]]
    have hk := none_keepable hn
    unfold propose
    cases hp : D.preset <;> simp only
    · rw [hs]
    all_goals
      split
      · rename_i s hk'; rw [hk] at hk'; cases hk'
      · rw [hs]

end

/-! ## The controlled runner is the runner -/

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable [DecidableEq Ix] [∀ i, DecidableEq (Hole i)]
variable {P Cred Cand Tok Fact Ob V : Type} [DecidableEq Tok] [DecidableEq Cand]
variable [DecidableEq (Σ i, S.Op i)]
variable {host : Host V Tok Fact} {sp : Spec S Tok Fact Ob} {au : Authority P Cred}
variable {k : (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j}

omit [DecidableEq Cand] in
/-- What `install` does. -/
theorem install_ok {i : Ix} {c c' : CCfg S Hole A P Cand Tok Fact Ob V i} {j : Ix} {h : Hole j}
    {K : SlotCtl S Hole A P Fact Cand j} {by_ : Option P} {cand : Cand}
    (hi : install host sp c h K by_ cand = .ok c') :
    run host sp c.cfg (.replan h (K.body cand) (citesFor K.slot K.desc by_ cand)) = .ok c'.cfg ∧
      c'.stored = upd c.stored h (some cand) ∧ c'.rev = upd c.rev h (c.rev j h + 1) ∧
      c'.decisions = c.decisions ++ [⟨⟨j, h⟩, cand, by_, c.rev j h, c.cfg.world, c.cfg.log.length⟩] := by
  unfold install at hi
  cases hr : run host sp c.cfg (.replan h (K.body cand) (citesFor K.slot K.desc by_ cand)) with
  | error r => rw [hr] at hi; cases hi
  | ok cfg' => rw [hr] at hi; cases hi; exact ⟨rfl, rfl, rfl, rfl⟩

/-- What an accepted principal's choice establishes. -/
theorem crun_choose_ok {i : Ix} {c c' : CCfg S Hole A P Cand Tok Fact Ob V i} {p : P} {cred : Cred}
    {j : Ix} {h : Hole j} {cand : Cand} {e : Nat}
    (hr : crun host sp au k c (.choose p cred h cand e) = .ok c') :
    au.verify p cred = true ∧
      (∀ f ∈ (k j h).desc.office p, (host.view c.cfg.world).holds f = true) ∧ e = c.rev j h ∧
      cand ∈ (k j h).desc.domain ∧ (k j h).slot.usable (host.view c.cfg.world).holds cand = true ∧
      install host sp c h (k j h) (some p) cand = .ok c' := by
  simp only [crun] at hr
  by_cases hv : au.verify p cred = true
  · by_cases ho : ((k j h).desc.office p).all (host.view c.cfg.world).holds = true
    · by_cases he : e = c.rev j h
      · by_cases hd : cand ∈ (k j h).desc.domain
        · by_cases hu : (k j h).slot.usable (host.view c.cfg.world).holds cand = true
          · simp only [hv, ho, he, hd, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              ne_eq, not_true_eq_false] at hr
            refine ⟨hv, fun f hf => List.all_eq_true.1 ho f hf, he, hd, hu, ?_⟩
            cases hs : c.stored j h with
            | none => rw [hs] at hr; exact hr
            | some s =>
              rw [hs] at hr
              simp only at hr
              split at hr
              · cases hr
              · exact hr
          · simp [hv, ho, he, hd, hu] at hr
        · simp [hv, ho, he, hd] at hr
      · simp [hv, ho, he] at hr
    · simp [hv, ho] at hr
  · simp [hv] at hr

/-- What an accepted advance establishes. -/
theorem crun_advance_ok {i : Ix} {c c' : CCfg S Hole A P Cand Tok Fact Ob V i} {j : Ix} {h : Hole j}
    (hr : crun host sp au k c (.advance h) = .ok c') :
    c' = c ∨ ∃ cand,
      propose (k j h).slot (k j h).desc (host.view c.cfg.world).holds (c.stored j h) (latchedOf host k c h) = .chosen cand ∧
      install host sp c h (k j h) none cand = .ok c' := by
  simp only [crun] at hr
  split at hr
  · cases hr; exact .inl rfl
  · rename_i cand hp; exact .inr ⟨cand, hp, hr⟩
  · cases hr
  · cases hr

/-- What an accepted runner event establishes: never a replan. -/
theorem crun_base_ok {i : Ix} {c c' : CCfg S Hole A P Cand Tok Fact Ob V i} {e : Event S Hole A Fact V}
    (hr : crun host sp au k c (.base e) = .ok c') :
    run host sp c.cfg e = .ok c'.cfg ∧ c'.stored = c.stored ∧ c'.rev = c.rev ∧
      c'.decisions = c.decisions ∧
      ∀ (j : Ix) (h : Hole j) f fs, e ≠ .replan h f fs := by
  simp only [crun] at hr
  cases e with
  | replan h f fs => cases hr
  | world v => ?_
  | dispatch o => ?_
  | respond r => ?_
  | abandon o => ?_
  all_goals
    simp only at hr
    split at hr
    · rename_i cfg' hrun
      cases hr
      exact ⟨hrun, rfl, rfl, rfl, fun _ _ _ _ he => by cases he⟩
    · cases hr

/-- Every accepted controlled event is a runner step or leaves the runner's configuration. -/
public theorem crun_cfg {i : Ix} {c c' : CCfg S Hole A P Cand Tok Fact Ob V i}
    {ev : CEvent S Hole A P Cred Cand Fact V} (hr : crun host sp au k c ev = .ok c') :
    c'.cfg = c.cfg ∨ ∃ e, run host sp c.cfg e = .ok c'.cfg := by
  cases ev with
  | base e => exact .inr ⟨e, (crun_base_ok hr).1⟩
  | advance h =>
    rcases crun_advance_ok hr with rfl | ⟨cand, _, hi⟩
    · exact .inl rfl
    · exact .inr ⟨_, (install_ok hi).1⟩
  | choose p cred h cand e =>
    obtain ⟨_, _, _, _, _, hi⟩ := crun_choose_ok hr
    exact .inr ⟨_, (install_ok hi).1⟩

/-- **The controlled runner's configurations are the runner's.** -/
public theorem creachable_reachable {i : Ix} {c₀ c : CCfg S Hole A P Cand Tok Fact Ob V i}
    (h : CReachable host sp au k c₀ c) : Reachable host sp c₀.cfg c.cfg := by
  induction h with
  | init => exact .init
  | step ev _ hs ih =>
    rcases crun_cfg hs with e | ⟨e, he⟩
    · rw [e]; exact ih
    · exact .step e ih he

/-- A controlled session ends at a controlled-reachable configuration. -/
public theorem csession_reachable {i : Ix} {c₀ c : CCfg S Hole A P Cand Tok Fact Ob V i}
    (hc : CReachable host sp au k c₀ c) (evs : List (CEvent S Hole A P Cred Cand Fact V)) :
    CReachable host sp au k c₀ (csession host sp au k c evs).1 := by
  induction evs generalizing c with
  | nil => exact hc
  | cons ev evs ih =>
    simp only [csession]
    cases h : crun host sp au k c ev with
    | ok c' => exact ih (.step ev hc h)
    | error w => exact ih hc

/-- **What a policy's decision installs** (the former `resolveEvent_ok`, now through the
descriptor): an accepted advance keeps the configuration, or installs the body of the first usable
candidate of the domain, citing its supports. -/
public theorem advance_installs {i : Ix} {c c' : CCfg S Hole A P Cand Tok Fact Ob V i} {j : Ix} {h : Hole j}
    (hr : crun host sp au k c (.advance h) = .ok c') :
    c' = c ∨ ∃ cand, (k j h).slot.select (host.view c.cfg.world).holds (k j h).desc.domain = .ok cand ∧
      cand ∈ (k j h).desc.domain ∧ (k j h).slot.usable (host.view c.cfg.world).holds cand = true ∧
      c'.cfg.log = c.cfg.log ++ [.replan h ((k j h).body cand) (citesFor (k j h).slot (k j h).desc none cand)] ∧
      c'.stored j h = some cand := by
  rcases crun_advance_ok hr with rfl | ⟨cand, hp, hi⟩
  · exact .inl rfl
  · obtain ⟨hdom, hu, hsel, _⟩ := propose_chosen hp
    obtain ⟨hrun, hst, _, _⟩ := install_ok hi
    refine .inr ⟨cand, hsel, hdom, hu, (run_replan_inv hrun).2.2.2.2.2.2.1, ?_⟩
    rw [hst]; simp [upd]

/-- **An authorized choice is accepted before dispatch** (the former `override_accepted`, now
through the descriptor): at a controlled configuration whose run has not ended, a choice by an
authenticated principal in office, at the current revision, of a permitted candidate usable now,
for a hole of ours the history has not entered, is accepted, if superseding a keepable stored
choice is allowed; it installs the candidate citing what its tenure says. -/
public theorem choose_accepted {i : Ix} {O : Open S Hole A Tok Fact Ob i} {v₀ : V}
    {cs₀ : (j : Ix) → Hole j → List Fact} {stored₀ : (j : Ix) → Hole j → Option Cand}
    {c : CCfg S Hole A P Cand Tok Fact Ob V i}
    (hc : CReachable host sp au k (CCfg.init (Cfg.init O v₀ cs₀) stored₀) c) (hlive : c.cfg.ended = none)
    {p : P} {cred : Cred} {j : Ix} {h : Hole j} {cand : Cand}
    (hv : au.verify p cred = true)
    (ho : ∀ f ∈ (k j h).desc.office p, (host.view c.cfg.world).holds f = true)
    (hd : cand ∈ (k j h).desc.domain) (hu : (k j h).slot.usable (host.view c.cfg.world).holds cand = true)
    (hov : ∀ s, c.stored j h = some s → s ≠ cand →
      keepable (k j h).slot (k j h).desc (host.view c.cfg.world).holds (latchedOf host k c h) (some s) = true →
      (k j h).desc.override = true)
    (hmine : isMine c.cfg.obj.Ω h = true) (hnd : ¬ Dispatched c.cfg.obj.template c.cfg.obj.hist j h) :
    ∃ c', crun host sp au k c (.choose p cred h cand (c.rev j h)) = .ok c' ∧
      c'.cfg.cites j h = citesFor (k j h).slot (k j h).desc (some p) cand ∧ c'.stored j h = some cand := by
  have hI := refines (creachable_reachable hc)
  obtain ⟨cfg', hrun, _⟩ := replan_accepted hI hlive ((k j h).body cand)
    (citesFor (k j h).slot (k j h).desc (some p) cand) hmine hnd
  let c' : CCfg S Hole A P Cand Tok Fact Ob V i :=
    { cfg := cfg'
      stored := upd c.stored h (some cand)
      rev := upd c.rev h (c.rev j h + 1)
      decisions := c.decisions ++ [⟨⟨j, h⟩, cand, some p, c.rev j h, c.cfg.world, c.cfg.log.length⟩] }
  have hinst : install host sp c h (k j h) (some p) cand = .ok c' := by
    unfold install; rw [hrun]
  have hcites : cfg'.cites j h = citesFor (k j h).slot (k j h).desc (some p) cand := by
    rw [(run_replan_inv hrun).2.2.2.2.2.2.2.2]; simp [setCites]
  have hall : ((k j h).desc.office p).all (host.view c.cfg.world).holds = true := List.all_eq_true.2 ho
  refine ⟨c', ?_, hcites, by simp [c', upd]⟩
  simp only [crun, hv, hall, hd, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq,
    not_true_eq_false, decide_true, Bool.not_true]
  cases hs : c.stored j h with
  | none => exact hinst
  | some s =>
    simp only
    by_cases hne : s = cand
    · subst hne; simp [hinst]
    · cases hk : keepable (k j h).slot (k j h).desc (host.view c.cfg.world).holds (latchedOf host k c h) (some s)
      · simp [hne, hk, hinst]
      · simp [hne, hk, hov s hs hne hk, hinst]

/-- An accepted controlled event that is not a reply is a runner step of an event that is not a
reply, or leaves the runner's configuration. -/
theorem crun_cfg_noreply {i : Ix} {c c' : CCfg S Hole A P Cand Tok Fact Ob V i}
    {ev : CEvent S Hole A P Cred Cand Fact V} (hno : ∀ r, ev ≠ .base (.respond r))
    (hr : crun host sp au k c ev = .ok c') :
    c'.cfg = c.cfg ∨ ∃ e, e.isRespond = false ∧ run host sp c.cfg e = .ok c'.cfg := by
  cases ev with
  | base e =>
    refine .inr ⟨e, ?_, (crun_base_ok hr).1⟩
    cases e with
    | respond r => exact absurd rfl (hno r)
    | _ => rfl
  | advance h =>
    rcases crun_advance_ok hr with rfl | ⟨cand, _, hi⟩
    · exact .inl rfl
    · exact .inr ⟨_, rfl, (install_ok hi).1⟩
  | choose p cred h cand e =>
    obtain ⟨_, _, _, _, _, hi⟩ := crun_choose_ok hr
    exact .inr ⟨_, rfl, (install_ok hi).1⟩

/-- **A missing reply licenses no new commitment, under control**: from a controlled configuration
with a call in flight, any controlled events but a reply (world moves, advances, choices, proposed
dispatches) leave the history, the spent tokens and the log's dispatches, and the call in flight
stays the residual's next call. -/
public theorem clost_reply_frozen {i : Ix} {O : Open S Hole A Tok Fact Ob i} {v₀ : V}
    {cs₀ : (j : Ix) → Hole j → List Fact} {stored₀ : (j : Ix) → Hole j → Option Cand}
    {c : CCfg S Hole A P Cand Tok Fact Ob V i}
    (hc : CReachable host sp au k (CCfg.init (Cfg.init O v₀ cs₀) stored₀) c) {o : Σ i, S.Op i}
    (ho : c.cfg.obj.hist.inflight = some o) (evs : List (CEvent S Hole A P Cred Cand Fact V))
    (hno : ∀ ev ∈ evs, ∀ r, ev ≠ .base (.respond r)) :
    (csession host sp au k c evs).1.cfg.obj.hist = c.cfg.obj.hist ∧
      (csession host sp au k c evs).1.cfg.spent = c.cfg.spent ∧
      dispatchesOf (csession host sp au k c evs).1.cfg.log = dispatchesOf c.cfg.log ∧
      IsCall (csession host sp au k c evs).1.cfg.res o := by
  have key : ∀ (evs : List (CEvent S Hole A P Cred Cand Fact V)) (c : CCfg S Hole A P Cand Tok Fact Ob V i),
      c.cfg.obj.hist.inflight = some o → (∀ ev ∈ evs, ∀ r, ev ≠ .base (.respond r)) →
      (csession host sp au k c evs).1.cfg.obj.hist = c.cfg.obj.hist ∧
        (csession host sp au k c evs).1.cfg.spent = c.cfg.spent ∧
        dispatchesOf (csession host sp au k c evs).1.cfg.log = dispatchesOf c.cfg.log := by
    intro evs
    induction evs with
    | nil => intro c _ _; exact ⟨rfl, rfl, rfl⟩
    | cons ev evs ih =>
      intro c ho hno
      simp only [csession]
      cases h : crun host sp au k c ev with
      | error w => exact ih c ho (fun e he => hno e (List.mem_cons_of_mem _ he))
      | ok c' =>
        have hrest := fun e he => hno e (List.mem_cons_of_mem _ he)
        rcases crun_cfg_noreply (hno ev List.mem_cons_self) h with he | ⟨e, hr, hrun⟩
        · obtain ⟨h1, h2, h3⟩ := ih c' (by rw [he]; exact ho) hrest
          rw [he] at h1 h2 h3; exact ⟨h1, h2, h3⟩
        · obtain ⟨hh, hs, hl, hd⟩ := step_inflight ho hr hrun
          obtain ⟨hh', hs', hd'⟩ := ih c' (by rw [hh]; exact ho) hrest
          exact ⟨hh'.trans hh, hs'.trans hs, by rw [hd', hl, hd]⟩
  obtain ⟨hh, hs, hd⟩ := key evs c ho hno
  refine ⟨hh, hs, hd, ?_⟩
  exact (refines (creachable_reachable (csession_reachable hc evs))).next o (by rw [hh]; exact ho)

/-- Every controlled run's runner log is `Legal`. -/
public theorem creachable_legal {i : Ix} {O : Open S Hole A Tok Fact Ob i} {v₀ : V}
    {cs₀ : (j : Ix) → Hole j → List Fact} {stored₀ : (j : Ix) → Hole j → Option Cand}
    {c : CCfg S Hole A P Cand Tok Fact Ob V i}
    (h : CReachable host sp au k (CCfg.init (Cfg.init O v₀ cs₀) stored₀) c) :
    Legal host sp O v₀ cs₀ c.cfg.log :=
  reachable_legal (creachable_reachable h)

/-! ## The decisions -/

/-- **Every decision is authorized**: a permitted candidate, usable at the world the decision was
made at; a principal's decision made while the principal held the slot's office; a policy's
decision never a `chooserRequired` slot's. Stated of the decision log alone. -/
public def DecisionsAuthorized (host : Host V Tok Fact)
    (k : (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (ds : List (Decision Hole P Cand V)) : Prop :=
  ∀ d ∈ ds, d.cand ∈ (k d.hole.1 d.hole.2).desc.domain ∧
    (k d.hole.1 d.hole.2).slot.usable (host.view d.world).holds d.cand = true ∧
    (∀ p, d.by_ = some p → ∀ f ∈ (k d.hole.1 d.hole.2).desc.office p, (host.view d.world).holds f = true) ∧
    (d.by_ = none → (k d.hole.1 d.hole.2).desc.preset ≠ .chooserRequired)

public theorem creachable_authorized {i : Ix} {c₀ c : CCfg S Hole A P Cand Tok Fact Ob V i}
    (h₀ : c₀.decisions = []) (h : CReachable host sp au k c₀ c) :
    DecisionsAuthorized host k c.decisions := by
  induction h with
  | init => rw [h₀]; intro d hd; cases hd
  | @step c c' ev _ hs ih =>
    cases ev with
    | base e => rw [(crun_base_ok hs).2.2.2.1]; exact ih
    | advance h =>
      rcases crun_advance_ok hs with rfl | ⟨cand, hp, hi⟩
      · exact ih
      · rw [(install_ok hi).2.2.2]
        intro d hd
        rcases List.mem_append.1 hd with hd | hd
        · exact ih d hd
        · simp only [List.mem_singleton] at hd
          subst hd
          obtain ⟨hdom, hu, _, hpre⟩ := propose_chosen hp
          refine ⟨hdom, hu, ?_, fun _ => hpre⟩
          intro p hp'
          exact absurd hp' (by simp)
    | choose p cred h cand e =>
      obtain ⟨_, ho, _, hdom, hu, hi⟩ := crun_choose_ok hs
      rw [(install_ok hi).2.2.2]
      intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact ih d hd
      · simp only [List.mem_singleton] at hd
        subst hd
        refine ⟨hdom, hu, ?_, ?_⟩
        · intro p' hp'
          obtain rfl : p = p' := by simpa using hp'
          exact ho
        · intro hn; exact absurd hn (by simp)

/-- **A slot's revision is the number of its decisions**: so a choice made against revision `n` is
accepted only if exactly `n` decisions of that slot were accepted before it. -/
public theorem creachable_revisions {i : Ix} {c₀ c : CCfg S Hole A P Cand Tok Fact Ob V i}
    (h₀ : c₀.decisions = []) (hr₀ : ∀ j (h : Hole j), c₀.rev j h = 0) (h : CReachable host sp au k c₀ c) :
    ∀ j (h : Hole j), c.rev j h = (c.decisions.filter fun d => decide (d.hole = ⟨j, h⟩)).length := by
  induction h with
  | init => intro j h; rw [hr₀, h₀]; rfl
  | @step c c' ev _ hs ih =>
    have inst : ∀ {j₀} {h₀ : Hole j₀} {K} {by_} {cand},
        install host sp c h₀ K by_ cand = .ok c' →
        ∀ j (h : Hole j), c'.rev j h = (c'.decisions.filter fun d => decide (d.hole = ⟨j, h⟩)).length := by
      intro j₀ h₀ K by_ cand hi j h
      obtain ⟨_, _, hrev, hdec⟩ := install_ok hi
      rw [hrev, hdec, List.filter_append]
      simp only [upd, List.length_append]
      by_cases e : (⟨j, h⟩ : Σ j, Hole j) = ⟨j₀, h₀⟩
      · simp only [e, ↓reduceIte, List.filter_cons, decide_true, List.filter_nil,
          List.length_cons, List.length_nil]
        cases e; rw [ih]
      · simp only [e, ↓reduceIte, List.filter_cons, List.filter_nil]
        rw [ih]
        have : decide ((⟨j₀, h₀⟩ : Σ j, Hole j) = ⟨j, h⟩) = false := by simpa using Ne.symm e
        simp [this]
    cases ev with
    | base e =>
      obtain ⟨_, _, hrev, hdec, _⟩ := crun_base_ok hs
      intro j h; rw [hrev, hdec]; exact ih j h
    | advance h =>
      rcases crun_advance_ok hs with rfl | ⟨cand, _, hi⟩
      · exact ih
      · exact inst hi
    | choose p cred h cand e =>
      obtain ⟨_, _, _, _, _, hi⟩ := crun_choose_ok hs
      exact inst hi

/-! ## What a decision cites, and the office rechecked at dispatch -/

/-- The last decision of hole `h` in a decision log. -/
public def lastOf (ds : List (Decision Hole P Cand V)) {j : Ix} (h : Hole j) :
    Option (Decision Hole P Cand V) :=
  ds.reverse.find? fun d => decide (d.hole = ⟨j, h⟩)

omit [DecidableEq Cand] in
theorem lastOf_snoc (ds : List (Decision Hole P Cand V)) (d : Decision Hole P Cand V) {j : Ix} (h : Hole j) :
    lastOf (ds ++ [d]) h = if d.hole = ⟨j, h⟩ then some d else lastOf ds h := by
  unfold lastOf
  rw [List.reverse_append]
  by_cases e : d.hole = ⟨j, h⟩ <;> simp [e]

omit [DecidableEq Cand] in
/-- A runner event other than a replan leaves every decision's citations. -/
theorem run_cites {i : Ix} {c c' : Cfg S Hole A Tok Fact Ob V i} {e : Event S Hole A Fact V}
    (hr : run host sp c e = .ok c') (hne : ∀ (j : Ix) (h : Hole j) f fs, e ≠ .replan h f fs) :
    c'.cites = c.cites := by
  cases e with
  | replan h f fs => exact absurd rfl (hne _ h f fs)
  | world v =>
    simp only [run] at hr
    split at hr
    · cases hr; rfl
    · cases hr
  | dispatch o =>
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | (cases hr; rfl)
  | respond r =>
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | (cases hr; rfl)
  | abandon o =>
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | (cases hr; rfl)

omit [DecidableEq Cand] in
/-- An accepted dispatch found every fact the decision of its hole cites holding at the view. -/
public theorem run_dispatch_decided {i : Ix} {c c' : Cfg S Hole A Tok Fact Ob V i} {o : Σ i, S.Op i}
    (hr : run host sp c (.dispatch o) = .ok c') {j : Ix} {h : Hole j} (ho : owner c.obj = some ⟨j, h⟩) :
    ∀ f ∈ c.cites j h, (c.admitView host).holds f = true := by
  have hd : decisionDead c.obj c.cites (c.admitView host) = [] := by
    simp only [run] at hr
    repeat' split at hr
    all_goals first | (cases hr; done) | assumption
  intro f hf
  simp only [decisionDead, ho] at hd
  have := List.filter_eq_nil_iff.1 hd f hf
  simpa using this

/-- **Each controlled hole's decision cites what its last decision's tenure says**: its candidate's
supports, and its chooser's office when it was made `whileInOffice` by a principal. -/
public theorem creachable_cites {i : Ix} {c₀ c : CCfg S Hole A P Cand Tok Fact Ob V i}
    (h₀ : c₀.decisions = []) (h : CReachable host sp au k c₀ c) :
    ∀ (j : Ix) (h : Hole j) d, lastOf c.decisions h = some d →
      c.cfg.cites j h = citesFor (k j h).slot (k j h).desc d.by_ d.cand := by
  induction h with
  | init => intro j h d hl; rw [h₀] at hl; cases hl
  | @step c c' ev _ hs ih =>
    have inst : ∀ {j₀} {h₀ : Hole j₀} {by_} {cand},
        install host sp c h₀ (k j₀ h₀) by_ cand = .ok c' →
        ∀ (j : Ix) (h : Hole j) d, lastOf c'.decisions h = some d →
          c'.cfg.cites j h = citesFor (k j h).slot (k j h).desc d.by_ d.cand := by
      intro j₀ h₀ by_ cand hi j h d hl
      obtain ⟨hrun, _, _, hdec⟩ := install_ok hi
      have hc := (run_replan_inv hrun).2.2.2.2.2.2.2.2
      rw [hdec, lastOf_snoc] at hl
      rw [hc]
      simp only [setCites]
      by_cases e : (⟨j, h⟩ : Σ j, Hole j) = ⟨j₀, h₀⟩
      · cases e
        simp only [↓reduceIte, Option.some.injEq] at hl ⊢
        rw [← hl]
      · have e' : ¬ (⟨j₀, h₀⟩ : Σ j, Hole j) = ⟨j, h⟩ := fun x => e x.symm
        simp only [e', ↓reduceIte] at hl
        simp only [e, ↓reduceIte]
        exact ih j h d hl
    cases ev with
    | base e =>
      obtain ⟨hrun, _, _, hdec, hraw⟩ := crun_base_ok hs
      intro j h d hl
      rw [hdec] at hl
      rw [run_cites hrun hraw]
      exact ih j h d hl
    | advance h =>
      rcases crun_advance_ok hs with rfl | ⟨cand, _, hi⟩
      · exact ih
      · exact inst hi
    | choose p cred h cand e =>
      obtain ⟨_, _, _, _, _, hi⟩ := crun_choose_ok hs
      exact inst hi

/-- **A `whileInOffice` decision is rechecked at every dispatch**: at a controlled configuration,
a call in a hole whose last decision was made `whileInOffice` by `p` is dispatched only while `p`
holds the slot's office. A `lasting` decision cites no office, so its chooser's leaving office voids
nothing (the fixture `Obend.Run.ControlExample` shows both). -/
public theorem office_rechecked {i : Ix} {c₀ c : CCfg S Hole A P Cand Tok Fact Ob V i}
    (h₀ : c₀.decisions = []) (hc : CReachable host sp au k c₀ c) {j : Ix} {h : Hole j}
    (ht : (k j h).desc.tenure = .whileInOffice)
    {d : Decision Hole P Cand V} {p : P} (hl : lastOf c.decisions h = some d) (hp : d.by_ = some p)
    {o : Σ i, S.Op i} {cfg' : Cfg S Hole A Tok Fact Ob V i}
    (hr : run host sp c.cfg (.dispatch o) = .ok cfg') (ho : owner c.cfg.obj = some ⟨j, h⟩) :
    ∀ f ∈ (k j h).desc.office p, (host.view c.cfg.world).holds f = true := by
  intro f hf
  have hcite := creachable_cites h₀ hc j h d hl
  have := run_dispatch_decided hr ho f (by
    rw [hcite]; simp only [citesFor, ht, hp]; simp [hf])
  simpa [Cfg.admitView, View.mask] using this

end

end Obend.Run.Control
