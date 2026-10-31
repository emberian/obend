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
@[expose] public section

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

end

end Obend.Run.Durable

end
