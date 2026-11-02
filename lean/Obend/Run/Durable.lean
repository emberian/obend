module
/-
# Obend.Run.Durable — a journal-first host for the shared ledger: durable commit, crash, recovery

`astra/ASTRA-VISION-20261031.md` §5.2 and §8.E. The joint transition (`Obend.Run.Shared.jrun`) is an
abstract atomic commit. A host refines it with a store that survives a crash and a memory that does
not (`DState`):

- the JOURNAL (durable, append-only): the accepted joint events, in order;
- the OUTBOX (durable): the journal positions whose call has been exposed, each its RECEIPT IDENTITY;
- the MEMORY (volatile): the joint configuration, or nothing after a crash.

The host's steps (`hstep`): `submit` judges an event at the memory and, if accepted, appends it to
the journal; `expose n` releases the call at journal position `n` under identity `n`; `crash` loses
the memory; `recover` replays the journal from the start (`replay`).

**The linearization point** is the journal append in `submit`. The authorized state, the spent token
and its grant, the call in flight and the receipt identity (the position) are all functions of the
journal (`replay`), so the one append makes them durable together, and an effect is exposed only by
naming a journal position that holds its dispatch (`expose`). Disk atomicity of one append is the
assumption the model makes: an append happened or it did not.

Theorems, at every configuration a host reaches through any interleaving of submissions,
exposures, crashes and recoveries (`HReachable`, `hreach_inv`):

- `durable_refines`: the journal replays to a configuration the abstract joint transition reaches;
  the memory is that configuration or nothing. So everything `Obend.Run.Proofs.Shared` proves of
  `JReachable` holds of the recovered state.
- `recover_restores`: a crash and a recovery give back the memory as it was.
- `journal_once`: the tokens the journal's dispatches consume are pairwise distinct.
- `exposed_once` (**two competing clients cannot spend one token twice across a restart**): two
  exposed effects consuming one token are one effect (one receipt identity), whoever submitted them
  and however many crashes came between.
- `exposure_journaled`: every exposed identity names a journal dispatch (durable before exposure);
  `expose_once`: an identity is exposed once, a second exposure of it is refused; the outbox and the
  journal survive a crash (`crash_keeps`), so after recovery the pending effects (`pending`) are
  exposed under their original identities, never re-issued under new ones.
-/
public import Obend.Run.Proofs.Shared
public section

namespace Obend.Run.Durable

open Obend.Slot Obend.Slot.Protocol Obend.Run.Control Obend.Run.Shared

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable {ι P Cred Cand Tok Fact Ob W : Type}
variable [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
variable (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
variable (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}

/-- A joint event, as the journal records it. -/
abbrev JEv (L : Ledger ι W Tok) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (P Cred Cand Fact : Type) :=
  JEvent ι W S Hole A P Cred Cand Fact L.Rec

/-- The host: its durable journal and outbox, its volatile memory. -/
structure DState (L : Ledger ι W Tok) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (P Cred Cand Fact Ob : Type)
    (i₀ : Ix) where
  journal : List (JEv L S Hole A P Cred Cand Fact)
  outbox : List Nat
  mem : Option (JCfg L S Hole A P Cand Fact Ob i₀)

/-- A host event. -/
inductive HEvent (L : Ledger ι W Tok) (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (P Cred Cand Fact : Type) where
  | submit (ev : JEv L S Hole A P Cred Cand Fact)
  | expose (n : Nat)
  | crash
  | recover

/-- Why the host refused. -/
inductive HRefusal (ι Tok : Type) (S : Sig Ix) (Hole : Ix → Type) (P Cand Fact : Type) where
  /-- the memory is lost: recover first -/
  | down
  /-- the joint transition refused the event -/
  | joint (r : JRefusal ι Tok S Hole P Cand Fact)
  /-- the journal holds no dispatch at this position -/
  | notDispatch (n : Nat)
  /-- this identity was exposed already -/
  | exposed (n : Nat)
  /-- the memory is up: nothing to recover -/
  | up
  /-- the journal does not replay (never, at a reachable host) -/
  | corrupt

/-- **Replay** a journal from a configuration: every event must be accepted. -/
def replay {i₀ : Ix} (J : JCfg L S Hole A P Cand Fact Ob i₀) :
    List (JEv L S Hole A P Cred Cand Fact) → Option (JCfg L S Hole A P Cand Fact Ob i₀)
  | [] => some J
  | ev :: evs =>
    match jrun L base sp au k J ev with
    | .ok J' => replay J' evs
    | .error _ => none

/-- **One host step.** The append in `submit` is the linearization point. -/
def hstep (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) (s : DState L S Hole A P Cred Cand Fact Ob i₀) :
    HEvent L S Hole A P Cred Cand Fact → Except (HRefusal ι Tok S Hole P Cand Fact) (DState L S Hole A P Cred Cand Fact Ob i₀)
  | .submit ev =>
    match s.mem with
    | none => .error .down
    | some J =>
      match jrun L base sp au k J ev with
      | .ok J' => .ok ⟨s.journal ++ [ev], s.outbox, some J'⟩
      | .error r => .error (.joint r)
  | .expose n =>
    match s.journal[n]? with
    | some (.dispatch _ _) => if n ∈ s.outbox then .error (.exposed n) else .ok ⟨s.journal, s.outbox ++ [n], s.mem⟩
    | _ => .error (.notDispatch n)
  | .crash => .ok ⟨s.journal, s.outbox, none⟩
  | .recover =>
    match s.mem with
    | some _ => .error .up
    | none =>
      match replay L base sp au k J₀ s.journal with
      | some J => .ok ⟨s.journal, s.outbox, some J⟩
      | none => .error .corrupt

/-- The host's start: nothing journaled, nothing exposed, the memory at the start. -/
def DState.init (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) : DState L S Hole A P Cred Cand Fact Ob i₀ := ⟨[], [], some J₀⟩

/-- The host configurations reachable from the start. -/
inductive HReachable (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) : DState L S Hole A P Cred Cand Fact Ob i₀ → Prop
  | init : HReachable J₀ (DState.init L J₀)
  | step {s s' : DState L S Hole A P Cred Cand Fact Ob i₀} (e : HEvent L S Hole A P Cred Cand Fact) :
      HReachable J₀ s → hstep L base sp au k J₀ s e = .ok s' → HReachable J₀ s'

/-- A host session. -/
def hsession (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    DState L S Hole A P Cred Cand Fact Ob i₀ → List (HEvent L S Hole A P Cred Cand Fact) →
      DState L S Hole A P Cred Cand Fact Ob i₀ × List (Option (HRefusal ι Tok S Hole P Cand Fact))
  | s, [] => (s, [])
  | s, e :: es =>
    match hstep L base sp au k J₀ s e with
    | .ok s' => let r := hsession J₀ s' es; (r.1, none :: r.2)
    | .error w => let r := hsession J₀ s es; (r.1, some w :: r.2)

/-- The effects journaled but not yet exposed: what recovery exposes, under their original
identities. -/
def pending (s : DState L S Hole A P Cred Cand Fact Ob i₀) : List Nat :=
  (List.range s.journal.length).filter fun n =>
    (match s.journal[n]? with
      | some (.dispatch _ _) => true
      | _ => false) && !decide (n ∈ s.outbox)

/-- The tokens an event consumes, if it is accepted. -/
def consumedBy : JEv L S Hole A P Cred Cand Fact → List Tok
  | .dispatch i o => ((sp i).consumes o.2).toList
  | _ => []

/-- Multi-step durable trace execution: steps the host through a trace of `HEvent`s,
    advancing on accepted steps and keeping the state on refused steps. -/
def runDurableTrace (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    DState L S Hole A P Cred Cand Fact Ob i₀ → List (HEvent L S Hole A P Cred Cand Fact) →
      DState L S Hole A P Cred Cand Fact Ob i₀
  | s, [] => s
  | s, e :: es =>
    match hstep L base sp au k J₀ s e with
    | .ok s' => runDurableTrace J₀ s' es
    | .error _ => runDurableTrace J₀ s es

theorem runDurableTrace_eq_hsession_fst (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    ∀ (s : DState L S Hole A P Cred Cand Fact Ob i₀) (es : List (HEvent L S Hole A P Cred Cand Fact)),
      runDurableTrace L base sp au k J₀ s es = (hsession L base sp au k J₀ s es).1
  | _, [] => rfl
  | s, e :: es => by
    simp only [runDurableTrace, hsession]
    cases hstep L base sp au k J₀ s e with
    | ok s' => exact runDurableTrace_eq_hsession_fst J₀ s' es
    | error _ => exact runDurableTrace_eq_hsession_fst J₀ s es

theorem runDurableTrace_append (J₀ : JCfg L S Hole A P Cand Fact Ob i₀) :
    ∀ (es₁ es₂ : List (HEvent L S Hole A P Cred Cand Fact)) (s : DState L S Hole A P Cred Cand Fact Ob i₀),
      runDurableTrace L base sp au k J₀ s (es₁ ++ es₂) =
        runDurableTrace L base sp au k J₀ (runDurableTrace L base sp au k J₀ s es₁) es₂
  | [], _, _ => rfl
  | e :: es₁, es₂, s => by
    simp only [List.cons_append, runDurableTrace]
    cases hstep L base sp au k J₀ s e with
    | ok s' => exact runDurableTrace_append J₀ es₁ es₂ s'
    | error _ => exact runDurableTrace_append J₀ es₁ es₂ s

theorem runDurableTrace_crash_down (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (j : List (JEv L S Hole A P Cred Cand Fact)) (o : List Nat) :
    ∀ (n : Nat),
      runDurableTrace L base sp au k J₀ ⟨j, o, none⟩ (List.replicate n .crash) = ⟨j, o, none⟩
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, runDurableTrace, hstep]
    exact runDurableTrace_crash_down J₀ j o n

/-- **Idempotent Multi-Crash Recovery**: any sequence of `crashes ≥ 1` consecutive `.crash`
    events followed by `.recover` produces the exact same `DState` as a single `.crash`
    followed by `.recover`, preserving both `journal` and `outbox` identically. -/
theorem crash_recover_idempotent (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (s : DState L S Hole A P Cred Cand Fact Ob i₀) (crashes : Nat) (hc : 1 ≤ crashes) :
    let trace : List (HEvent L S Hole A P Cred Cand Fact) := List.replicate crashes .crash ++ [.recover]
    let single : List (HEvent L S Hole A P Cred Cand Fact) := [.crash, .recover]
    runDurableTrace L base sp au k J₀ s trace = runDurableTrace L base sp au k J₀ s single ∧
    (runDurableTrace L base sp au k J₀ s trace).journal = s.journal ∧
    (runDurableTrace L base sp au k J₀ s trace).outbox = s.outbox := by
  cases crashes with
  | zero => omega
  | succ n =>
    dsimp only
    rw [List.replicate_succ, List.cons_append]
    simp only [runDurableTrace, hstep]
    rw [runDurableTrace_append, runDurableTrace_crash_down]
    simp only [runDurableTrace, hstep]
    cases hrep : replay L base sp au k J₀ s.journal <;> simp

end

theorem filter_length_lt_of_mem_false {α : Type} (p : α → Bool) {x : α} (hx_false : p x = false) :
    ∀ (l : List α), x ∈ l → (l.filter p).length < l.length
  | [], hmem => by cases hmem
  | y :: ys, hmem => by
    rcases List.mem_cons.mp hmem with rfl | hmem_tl
    · simp only [List.filter_cons, hx_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.lt_of_le_of_lt (List.length_filter_le p ys) (Nat.lt_succ_self ys.length)
    · have ih := filter_length_lt_of_mem_false p hx_false ys hmem_tl
      simp only [List.filter_cons, List.length_cons]
      split
      · simp only [List.length_cons]
        omega
      · omega

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable {ι P Cred Cand Tok Fact Ob W : Type}
variable [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
variable [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
variable (L : Ledger ι W Tok) (base : W → View Tok Fact) (sp : ι → Spec S Tok Fact Ob)
variable (au : ι → Authority P Cred) (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j) {i₀ : Ix}

/-- Every successful `.expose n` step strictly removes `n` from `pending` and appends `n`
    to `outbox` without altering `journal` or `mem`. -/
theorem pending_decreases_on_expose (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (s s' : DState L S Hole A P Cred Cand Fact Ob i₀) (n : Nat)
    (h : hstep L base sp au k J₀ s (.expose n) = .ok s') :
    s'.journal = s.journal ∧
    s'.mem = s.mem ∧
    s'.outbox = s.outbox ++ [n] ∧
    n ∈ pending L s ∧
    n ∉ pending L s' ∧
    pending L s' = (pending L s).filter (fun m => m != n) ∧
    (pending L s').length < (pending L s).length := by
  simp only [hstep] at h
  split at h
  · rename_i i o hio
    split at h
    · cases h
    · rename_i hnot_outbox
      cases h
      have hlt : n < s.journal.length :=
        Nat.lt_of_not_le fun hge => by rw [List.getElem?_eq_none hge] at hio; cases hio
      have hn_mem_pending : n ∈ pending L s := by
        unfold pending
        rw [List.mem_filter]
        refine ⟨List.mem_range.mpr hlt, ?_⟩
        simp [hio, hnot_outbox]
      have hfilter_eq : pending L ⟨s.journal, s.outbox ++ [n], s.mem⟩ =
          (pending L s).filter (fun m => m != n) := by
        unfold pending
        dsimp only
        rw [List.filter_filter]
        apply List.filter_congr
        intro m _
        by_cases hd : (match s.journal[m]? with | some (.dispatch _ _) => true | _ => false) = true
        · simp only [hd, Bool.true_and]
          by_cases hm_eq : m = n
          · subst hm_eq
            simp
          · have hne_beq : (m != n) = true := bne_iff_ne.mpr hm_eq
            simp [List.mem_append, hm_eq, hne_beq]
        · have hdf : (match s.journal[m]? with | some (.dispatch _ _) => true | _ => false) = false :=
            Bool.eq_false_iff.mpr hd
          simp [hdf]
      have hn_not_pending' : n ∉ pending L ⟨s.journal, s.outbox ++ [n], s.mem⟩ := by
        rw [hfilter_eq, List.mem_filter]
        intro ⟨_, hne⟩
        simp at hne
      have hlen_lt : (pending L ⟨s.journal, s.outbox ++ [n], s.mem⟩).length < (pending L s).length := by
        rw [hfilter_eq]
        exact filter_length_lt_of_mem_false (fun m => m != n) (by simp) (pending L s) hn_mem_pending
      exact ⟨rfl, rfl, rfl, hn_mem_pending, hn_not_pending', hfilter_eq, hlen_lt⟩
  · cases h

end

end Obend.Run.Durable

end
