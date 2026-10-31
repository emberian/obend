module
/-
# Obend.Run.Proofs.Durable — the journal-first host refines the abstract commit

The theorems stated in `Obend.Run.Durable`: `hreach_inv`, `durable_refines`, `recover_restores`,
`journal_once`, `exposed_once`, `exposure_journaled`, `expose_once`, `crash_keeps`.
-/
public import Obend.Run.Durable
import all Obend.Run.Durable

namespace Obend.Run.Durable

open Obend.Slot Obend.Slot.Protocol Obend.Run.Control Obend.Run.Shared

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable {ι P Cred Cand Tok Fact Ob W : Type}
variable [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
variable {L : Ledger ι W Tok} {base : W → View Tok Fact} {sp : ι → Spec S Tok Fact Ob}
variable {au : ι → Authority P Cred} {k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j} {i₀ : Ix}

theorem replay_snoc (J : JCfg L S Hole A P Cand Fact Ob i₀) :
    ∀ (evs : List (JEv L S Hole A P Cred Cand Fact)) (ev : JEv L S Hole A P Cred Cand Fact),
      replay L base sp au k J (evs ++ [ev]) =
        (replay L base sp au k J evs).bind fun J' => (jrun L base sp au k J' ev).toOption
  | [], ev => by
    simp only [List.nil_append, replay, Option.bind_some]
    cases jrun L base sp au k J ev <;> rfl
  | e :: evs, ev => by
    simp only [List.cons_append, replay]
    cases jrun L base sp au k J e with
    | ok J' => exact replay_snoc J' evs ev
    | error _ => rfl

/-- A replayed journal ends at a configuration the abstract joint transition reaches. -/
theorem replay_reachable {J₀ : JCfg L S Hole A P Cand Fact Ob i₀} :
    ∀ (evs : List (JEv L S Hole A P Cred Cand Fact)) {J J' : JCfg L S Hole A P Cand Fact Ob i₀},
      JReachable L base sp au k J₀ J → replay L base sp au k J evs = some J' → JReachable L base sp au k J₀ J'
  | [], _, _, hJ, h => by cases h; exact hJ
  | ev :: evs, J, J', hJ, h => by
    simp only [replay] at h
    split at h
    · rename_i J₁ h₁; exact replay_reachable evs (.step ev hJ h₁) h
    · cases h

/-- **What a joint transition does to the grants**: it adds the token a dispatch consumes, and
nothing else. -/
theorem jrun_toks {J J' : JCfg L S Hole A P Cand Fact Ob i₀} {ev : JEv L S Hole A P Cred Cand Fact}
    (h : jrun L base sp au k J ev = .ok J') :
    (L.grants J'.led).map Grant.tok = (L.grants J.led).map Grant.tok ++ consumedBy L sp ev := by
  cases ev with
  | world w =>
    simp only [jrun] at h; split at h
    · rename_i d hd; rw [propagate_allowed _ (ledgerStep_allowed L hd)] at h; simp only [Except.map] at h; cases h
      obtain ⟨_, rfl⟩ := ledgerStep_raw hd
      simp [L.setRaw_grants, consumedBy]
    · cases h
  | dispatch i o =>
    simp only [jrun] at h; split at h
    · split at h
      · rename_i d hd; rw [propagate_allowed _ (ledgerStep_allowed L hd)] at h; simp only [Except.map] at h; cases h
        obtain ⟨hdc, hdn⟩ := ledgerStep_rowOf hd
        cases ht : (sp i).consumes o.2 with
        | some t => rw [hdc t ht, L.commit_grants]; simp [consumedBy, ht]
        | none => rw [hdn ht]; simp [consumedBy, ht]
      · cases h
    · split at h <;> cases h
    · cases h
  | abandon i o =>
    simp only [jrun] at h; split at h
    · split at h
      · rename_i d hd; rw [propagate_allowed _ (ledgerStep_allowed L hd)] at h; simp only [Except.map] at h; cases h
        rw [ledgerStep_abandon hd, L.abandon_grants]; simp [consumedBy]
      · cases h
    · cases h
  | own i ev =>
    simp only [jrun] at h; split at h
    · cases h
    · cases h
    · cases h
    · split at h
      · cases h; simp [consumedBy]
      · cases h

theorem replay_toks {J : JCfg L S Hole A P Cand Fact Ob i₀} :
    ∀ (evs : List (JEv L S Hole A P Cred Cand Fact)) {J' : JCfg L S Hole A P Cand Fact Ob i₀},
      replay L base sp au k J evs = some J' →
      (L.grants J'.led).map Grant.tok = (L.grants J.led).map Grant.tok ++ evs.flatMap (consumedBy L sp)
  | [], _, h => by cases h; simp
  | ev :: evs, J', h => by
    simp only [replay] at h
    split at h
    · rename_i J₁ h₁
      rw [replay_toks (J := J₁) evs h, jrun_toks h₁]
      simp
    · cases h

/-- A host session ends at a reachable host. -/
public theorem hsession_reachable {J₀ : JCfg L S Hole A P Cand Fact Ob i₀} {s : DState L S Hole A P Cred Cand Fact Ob i₀}
    (hs : HReachable L base sp au k J₀ s) (es : List (HEvent L S Hole A P Cred Cand Fact)) :
    HReachable L base sp au k J₀ (hsession L base sp au k J₀ s es).1 := by
  induction es generalizing s with
  | nil => exact hs
  | cons e es ih =>
    simp only [hsession]
    cases h : hstep L base sp au k J₀ s e with
    | ok s' => exact ih (.step e hs h)
    | error _ => exact ih hs

/-- What holds of every reachable host. -/
public structure HInv (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) (s : DState L S Hole A P Cred Cand Fact Ob i₀) : Prop where
  replays : ∃ J, replay L base sp au k J₀ s.journal = some J ∧ JReachable L base sp au k J₀ J ∧
    (s.mem = none ∨ s.mem = some J)
  outbox_nodup : s.outbox.Nodup
  outbox_dispatch : ∀ n ∈ s.outbox, ∃ i o, s.journal[n]? = some (.dispatch i o)

/-- **The invariant holds at every reachable host.** -/
public theorem hreach_inv {J₀ : JCfg L S Hole A P Cand Fact Ob i₀} {s : DState L S Hole A P Cred Cand Fact Ob i₀}
    (h : HReachable L base sp au k J₀ s) : HInv L base sp au k J₀ s := by
  induction h with
  | init => exact ⟨⟨J₀, rfl, .init, .inr rfl⟩, List.nodup_nil, fun _ h => by cases h⟩
  | @step s s' e _ hs ih =>
    obtain ⟨⟨J, hJ, hr, hm⟩, hnd, hdisp⟩ := ih
    cases e with
    | submit ev =>
      simp only [hstep] at hs
      split at hs
      · cases hs
      · rename_i J₁ hmem
        split at hs
        · rename_i J' hj
          cases hs
          have hJ₁ : J₁ = J := by
            rcases hm with hm | hm <;> rw [hm] at hmem <;> cases hmem; rfl
          subst hJ₁
          refine ⟨⟨J', ?_, .step ev hr hj, .inr rfl⟩, hnd, fun n hn => ?_⟩
          · rw [replay_snoc, hJ]; simp [hj, Except.toOption]
          · obtain ⟨i, o, hio⟩ := hdisp n hn
            have hlt : n < s.journal.length :=
              Nat.lt_of_not_le fun hc => by rw [List.getElem?_eq_none hc] at hio; cases hio
            exact ⟨i, o, by rw [List.getElem?_append_left hlt]; exact hio⟩
        · cases hs
    | expose n =>
      simp only [hstep] at hs
      split at hs
      · rename_i i o hio
        split at hs
        · cases hs
        · rename_i hnot
          cases hs
          refine ⟨⟨J, hJ, hr, hm⟩, List.nodup_append.2 ⟨hnd, by simp, fun a ha b hb e => ?_⟩, fun m hm' => ?_⟩
          · simp at hb; subst hb; subst e; exact hnot ha
          · rcases List.mem_append.1 hm' with hm' | hm'
            · exact hdisp m hm'
            · simp at hm'; subst hm'; exact ⟨i, o, hio⟩
      · cases hs
    | crash =>
      simp only [hstep] at hs; cases hs
      exact ⟨⟨J, hJ, hr, .inl rfl⟩, hnd, hdisp⟩
    | recover =>
      simp only [hstep] at hs
      split at hs
      · cases hs
      · split at hs
        · rename_i J' hJ'
          cases hs
          rw [hJ] at hJ'; cases hJ'
          exact ⟨⟨J, hJ, hr, .inr rfl⟩, hnd, hdisp⟩
        · cases hs

/-- **The host refines the abstract commit**: the journal replays to a configuration the joint
transition reaches, and the memory is that configuration or lost. -/
public theorem durable_refines {J₀ : JCfg L S Hole A P Cand Fact Ob i₀} {s : DState L S Hole A P Cred Cand Fact Ob i₀}
    (h : HReachable L base sp au k J₀ s) :
    ∃ J, replay L base sp au k J₀ s.journal = some J ∧ JReachable L base sp au k J₀ J ∧
      (s.mem = none ∨ s.mem = some J) :=
  (hreach_inv h).replays

/-- **Recovery restores the memory**: after a crash, recovery gives back exactly the configuration
the memory held. -/
public theorem recover_restores {J₀ : JCfg L S Hole A P Cand Fact Ob i₀} {s : DState L S Hole A P Cred Cand Fact Ob i₀}
    (h : HReachable L base sp au k J₀ s) {J : JCfg L S Hole A P Cand Fact Ob i₀} (hm : s.mem = some J) :
    ∃ s₁ s₂, hstep L base sp au k J₀ s .crash = .ok s₁ ∧ hstep L base sp au k J₀ s₁ .recover = .ok s₂ ∧
      s₂.mem = some J ∧ s₂.journal = s.journal ∧ s₂.outbox = s.outbox := by
  obtain ⟨J', hJ', _, hm'⟩ := (hreach_inv h).replays
  have : J' = J := by rcases hm' with hm' | hm' <;> rw [hm'] at hm <;> cases hm; rfl
  subst this
  refine ⟨⟨s.journal, s.outbox, none⟩, ⟨s.journal, s.outbox, some J'⟩, rfl, ?_, rfl, rfl, rfl⟩
  simp only [hstep, hJ']

/-- **A crash keeps the journal and the outbox.** -/
public theorem crash_keeps (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) (s : DState L S Hole A P Cred Cand Fact Ob i₀) :
    ∃ s', hstep L base sp au k J₀ s .crash = .ok s' ∧ s'.journal = s.journal ∧ s'.outbox = s.outbox ∧
      pending L s' = pending L s := ⟨_, rfl, rfl, rfl, rfl⟩

/-- **Durable before exposure**: every exposed identity is the position of a journaled dispatch. -/
public theorem exposure_journaled {J₀ : JCfg L S Hole A P Cand Fact Ob i₀} {s : DState L S Hole A P Cred Cand Fact Ob i₀}
    (h : HReachable L base sp au k J₀ s) : ∀ n ∈ s.outbox, ∃ i o, s.journal[n]? = some (.dispatch i o) :=
  (hreach_inv h).outbox_dispatch

/-- **An identity is exposed once**: a second exposure of it is refused, naming it. -/
public theorem expose_once (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) (s : DState L S Hole A P Cred Cand Fact Ob i₀)
    {n : Nat} (hn : n ∈ s.outbox) {i : ι} {o : Σ i, S.Op i} (hio : s.journal[n]? = some (.dispatch i o)) :
    hstep L base sp au k J₀ s (.expose n) = .error (.exposed n) := by
  simp [hstep, hio, hn]

theorem nodup_flatMap_pos {α β : Type} (f : α → List β) :
    ∀ (l : List α) {n m : Nat} {a b : α} {t : β}, (l.flatMap f).Nodup → l[n]? = some a → l[m]? = some b →
      t ∈ f a → t ∈ f b → n = m
  | [], _, _, _, _, _, _, ha, _, _, _ => by cases ha
  | x :: xs, n, m, a, b, t, hnd, ha, hb, hta, htb => by
    rw [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨_, hrest, hdis⟩ := hnd
    cases n with
    | zero =>
      cases m with
      | zero => rfl
      | succ m =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at ha hb
        subst ha
        exact absurd rfl (hdis t hta t (List.mem_flatMap.2 ⟨b, List.mem_of_getElem? hb, htb⟩))
    | succ n =>
      cases m with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at ha hb
        subst hb
        exact absurd rfl (hdis t htb t (List.mem_flatMap.2 ⟨a, List.mem_of_getElem? ha, hta⟩))
      | succ m =>
        simp only [List.getElem?_cons_succ] at ha hb
        rw [nodup_flatMap_pos f xs hrest ha hb hta htb]

variable {d₀ : L.Rec} {O : ι → Open S Hole A Tok Fact Ob i₀} {stored₀ : ι → (j : Ix) → Hole j → Option Cand}

/-- **Once, across restarts**: the tokens the journal's dispatches consume are pairwise distinct, at
every reachable host. -/
public theorem journal_once (hs₀ : L.spent d₀ = []) (hg₀ : L.grants d₀ = [])
    {s : DState L S Hole A P Cred Cand Fact Ob i₀} (h : HReachable L base sp au k (JCfg.init L d₀ O stored₀) s) :
    (s.journal.flatMap (consumedBy L sp)).Nodup := by
  obtain ⟨J, hJ, hr, _⟩ := (hreach_inv h).replays
  have ht := replay_toks s.journal hJ
  have hnd := (joint_reachable_ticket_exclusive hs₀ hg₀ hr).1
  rw [ht] at hnd
  have : (L.grants (JCfg.init (P := P) L d₀ O stored₀).led).map Grant.tok = [] := by
    show (L.grants d₀).map Grant.tok = []; rw [hg₀]; rfl
  rw [this, List.nil_append] at hnd
  exact hnd

/-- **Two competing clients cannot spend one token twice across a restart**: at every host reachable
through any interleaving of submissions, exposures, crashes and recoveries, two exposed effects that
consume one token are one effect, with one receipt identity. -/
public theorem exposed_once (hs₀ : L.spent d₀ = []) (hg₀ : L.grants d₀ = [])
    {s : DState L S Hole A P Cred Cand Fact Ob i₀} (h : HReachable L base sp au k (JCfg.init L d₀ O stored₀) s)
    {n m : Nat} (_hn : n ∈ s.outbox) (_hm : m ∈ s.outbox) {i j : ι} {o o' : Σ i, S.Op i} {t : Tok}
    (hio : s.journal[n]? = some (.dispatch i o)) (hjo : s.journal[m]? = some (.dispatch j o'))
    (ht : (sp i).consumes o.2 = some t) (ht' : (sp j).consumes o'.2 = some t) : n = m ∧ i = j :=
  have hnm := nodup_flatMap_pos (consumedBy L sp) s.journal (t := t) (journal_once hs₀ hg₀ h) hio hjo
    (by simp [consumedBy, ht]) (by simp [consumedBy, ht'])
  ⟨hnm, by subst hnm; rw [hio] at hjo; cases hjo; rfl⟩

end

end Obend.Run.Durable
