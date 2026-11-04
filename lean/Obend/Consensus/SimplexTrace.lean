module
/-
# Obend.Consensus.SimplexTrace — a node's run, checked against the protocol relation

`Obend.Consensus.SimplexProtocol` is a relation. This module makes "the node is a simulator of
it" a checked sentence: a node emits its run as a TRACE, the list of messages it and its peers
sent in order, and `checkTrace P tr` decides, message by message, that each one is a `Step` of
the relation from the messages before it. `checkTrace_sound`: an accepted trace is reachable
(`Reach P tr.reverse`). A refusal is a `TraceClause` that names the message: the sender neither
in the committee nor declared faulty, a proposal not by the view's leader, a second vote in a
view (`votedTwice`), two different votes in a view (`equivocation`, carrying the
`SlashingReceipt` of those two votes, which `checks` against the trace:
`checkStep_equivocation_checks`), a block vote whose chain is not on notarized ground
(`voteRule`), or a finalize vote for a block the node did not vote for or that is not notarized
(`finalizeRule`).

The judge is `simplexTraceJudge` (object: the `Protocol`, i.e. the committee and who is declared
faulty; certificate: the trace) and the registered format is `simplex-trace@1`, decoded from JSON
(the witness wire every other format uses). `explain` renders the clause so the session's
refusal says which message, which node and, for an equivocation, which receipt.

Views and node ids are `Nat`. No signatures: the trace's sender field is taken as the signer,
as in the relation.
-/

public import Obend.Consensus.SimplexProtocol
public import Obend.Judge.Class
public import Lean

@[expose] public section

namespace Obend.Consensus.SimplexTrace

open Obend.Consensus.SimplexProtocol
open Lean (Json)

set_option autoImplicit false

/-! ## 1. The rules, decided -/

instance (P : Protocol) (sent : Sent) (v : Nat) : Decidable (NotarizedDummy P sent v) :=
  inferInstanceAs (Decidable (P.quorum ≤ votesFor P sent v (.dummy v)))

instance (P : Protocol) (sent : Sent) (v : Nat) (c : Chain) : Decidable (NotarizedBlock P sent v c) :=
  inferInstanceAs (Decidable (P.quorum ≤ votesFor P sent v (.block c)))

def entryNotarizedB (P : Protocol) (sent : Sent) (k : Nat) (upto : Chain) : Entry → Bool
  | .dummy v => v == k + 1 && decide (NotarizedDummy P sent (k + 1))
  | .block v _ => v == k + 1 && decide (NotarizedBlock P sent (k + 1) upto)

theorem entryNotarizedB_sound {P : Protocol} {sent : Sent} {k : Nat} {upto : Chain} {e : Entry}
    (h : entryNotarizedB P sent k upto e = true) : EntryNotarized P sent k upto e := by
  cases e with
  | dummy v =>
    simp only [entryNotarizedB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact h
  | block v x =>
    simp only [entryNotarizedB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact h

def chainNotarizedB (P : Protocol) (sent : Sent) (c : Chain) : Bool :=
  (List.range c.length).all fun k =>
    match c[k]? with
    | some e => entryNotarizedB P sent k (c.take (k + 1)) e
    | none => false

theorem chainNotarizedB_sound {P : Protocol} {sent : Sent} {c : Chain}
    (h : chainNotarizedB P sent c = true) : ChainNotarized P sent c := by
  intro k hk
  simp only [chainNotarizedB, List.all_eq_true, List.mem_range] at h
  have hkk := h k hk
  rw [List.getElem?_eq_getElem hk] at hkk
  exact entryNotarizedB_sound hkk

def voteRuleB (P : Protocol) (sent : Sent) (v : Nat) : Target → Bool
  | .block c =>
    decide (1 ≤ v) &&
      (match c.getLast? with
       | some (.block w _) =>
         w == v && c.dropLast.length == v - 1 && chainNotarizedB P sent c.dropLast &&
           sent.contains ⟨P.leader v, v, .propose, .block c⟩
       | _ => false)
  | .dummy w => decide (1 ≤ v) && w == v

theorem voteRuleB_sound {P : Protocol} {sent : Sent} {v : Nat} {t : Target}
    (h : voteRuleB P sent v t = true) : VoteRule P sent v t := by
  cases t with
  | dummy w =>
    simp only [voteRuleB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact h
  | block c =>
    simp only [voteRuleB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, hm⟩ := h
    cases hl : c.getLast? with
    | none => rw [hl] at hm; cases hm
    | some e =>
      rw [hl] at hm
      cases e with
      | dummy w => cases hm
      | block w x =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        obtain ⟨⟨⟨hw, hlen⟩, hchain⟩, hprop⟩ := hm
        obtain ⟨p, hp⟩ := List.getLast?_eq_some_iff.1 hl
        have hdrop : c.dropLast = p := by rw [hp]; exact List.dropLast_concat
        rw [hdrop] at hlen hchain
        subst hw
        refine ⟨h1, p, x, hp, hlen, chainNotarizedB_sound hchain, ?_⟩
        exact List.contains_iff_mem.1 hprop

/-! ## 2. One step, checked -/

inductive TraceClause where
  | senderUnknown (n : Nat)
  | notLeader (n v : Nat)
  | proposeNotBlock (n v : Nat)
  | votedTwice (n v : Nat)
  | equivocation (r : SlashingReceipt)
  | voteRule (n v : Nat)
  | finalizeRule (n v : Nat)
  | finalizeNotBlock (n v : Nat)
  deriving DecidableEq, Repr

def isVoteOf (n v : Nat) (m : Msg) : Bool :=
  m.sender == n && m.view == v && m.kind == .vote

/-- The step a message is, from the messages before it: an injection if its sender is declared
faulty; otherwise the honest rule of its kind. -/
def checkStep (P : Protocol) (sent : Sent) (m : Msg) : Except TraceClause Unit :=
  if P.faulty m.sender then .ok ()
  else if !P.committee.contains m.sender then .error (.senderUnknown m.sender)
  else
    match m.kind with
    | .propose =>
      match m.target with
      | .block _ =>
        if m.sender == P.leader m.view then .ok () else .error (.notLeader m.sender m.view)
      | .dummy _ => .error (.proposeNotBlock m.sender m.view)
    | .vote =>
      match sent.find? (isVoteOf m.sender m.view) with
      | some m' =>
        match m'.target == m.target with
        | true => .error (.votedTwice m.sender m.view)
        | false => .error (.equivocation ⟨m.view, m'.target, m.target, [m.sender]⟩)
      | none =>
        match voteRuleB P sent m.view m.target with
        | true => .ok ()
        | false => .error (.voteRule m.sender m.view)
    | .finalize =>
      match m.target with
      | .block c =>
        match voted sent m.sender m.view (.block c) && decide (NotarizedBlock P sent m.view c) with
        | true => .ok ()
        | false => .error (.finalizeRule m.sender m.view)
      | .dummy _ => .error (.finalizeNotBlock m.sender m.view)

theorem votedAny_eq_false_of_find?_none {sent : Sent} {n v : Nat}
    (h : sent.find? (isVoteOf n v) = none) : votedAny sent n v = false := by
  rw [List.find?_eq_none] at h
  unfold votedAny
  rw [List.any_eq_false]
  intro m hm
  exact h m hm

/-- **An accepted step is a `Step`.** -/
theorem checkStep_sound {P : Protocol} {sent : Sent} {m : Msg}
    (h : checkStep P sent m = .ok ()) : Step P sent (m :: sent) := by
  obtain ⟨n, v, k, t⟩ := m
  unfold checkStep at h
  simp only at h
  by_cases hf : P.faulty n = true
  · exact Step.inject sent ⟨n, v, k, t⟩ hf
  · rw [if_neg hf] at h
    have hf' : P.faulty n = false := by cases hpf : P.faulty n <;> simp_all
    by_cases hc : P.committee.contains n = true
    · rw [hc] at h
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      have hn : P.honest n := ⟨List.contains_iff_mem.1 hc, hf'⟩
      cases k with
      | propose =>
        cases t with
        | block c =>
          simp only at h
          split at h
          · rename_i hl
            exact Step.propose sent n v c hn (beq_iff_eq.1 hl)
          · cases h
        | dummy w => cases h
      | vote =>
        simp only at h
        cases hfind : sent.find? (isVoteOf n v) with
        | some m' =>
          rw [hfind] at h
          simp only at h
          cases hq : (m'.target == t) <;> rw [hq] at h <;> cases h
        | none =>
          rw [hfind] at h
          simp only at h
          cases hrule : voteRuleB P sent v t
          · rw [hrule] at h; cases h
          · exact Step.vote sent n v t hn (votedAny_eq_false_of_find?_none hfind) (voteRuleB_sound hrule)
      | finalize =>
        cases t with
        | block c =>
          simp only at h
          cases hok : (voted sent n v (.block c) && decide (NotarizedBlock P sent v c))
          · rw [hok] at h; cases h
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
            exact Step.finalize sent n v c hn hok.1 hok.2
        | dummy w => cases h
    · have hc' : P.committee.contains n = false := by cases hpc : P.committee.contains n <;> simp_all
      rw [hc'] at h
      simp at h

/-- **An equivocation refusal names a receipt that checks against the trace up to that
message**: the two votes are both in it. -/
theorem checkStep_equivocation_checks {P : Protocol} {sent : Sent} {m : Msg} {r : SlashingReceipt}
    (h : checkStep P sent m = .error (.equivocation r)) : r.checks (m :: sent) = true := by
  obtain ⟨n, v, k, t⟩ := m
  unfold checkStep at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases k with
      | propose =>
        cases t with
        | block c => simp only at h; split at h <;> cases h
        | dummy w => cases h
      | finalize =>
        cases t with
        | block c =>
          simp only at h
          cases hok : (voted sent n v (.block c) && decide (NotarizedBlock P sent v c)) <;> rw [hok] at h <;> cases h
        | dummy w => cases h
      | vote =>
        simp only at h
        cases hfind : sent.find? (isVoteOf n v) with
        | none =>
          rw [hfind] at h
          simp only at h
          cases hrule : voteRuleB P sent v t <;> rw [hrule] at h <;> cases h
        | some m' =>
          rw [hfind] at h
          simp only at h
          cases hq : (m'.target == t)
          · rw [hq] at h
            have hne : ¬ (m'.target == t) = true := by rw [hq]; decide
            cases h
            have hmem := List.mem_of_find?_eq_some hfind
            have hp := List.find?_some hfind
            simp only [isVoteOf, Bool.and_eq_true, beq_iff_eq] at hp
            obtain ⟨⟨hs, hv⟩, hk⟩ := hp
            have hm' : m' = ⟨n, v, .vote, m'.target⟩ := by
              cases m'; simp only at hs hv hk; subst hs hv hk; rfl
            simp only [SlashingReceipt.checks, Bool.and_eq_true, decide_eq_true_eq, List.all_cons,
              List.all_nil, Bool.and_true]
            refine ⟨fun heq => hne (beq_iff_eq.2 heq), ?_, ?_⟩
            · rw [voted_iff]; rw [hm'] at hmem; exact List.mem_cons_of_mem _ hmem
            · rw [voted_iff]; exact List.mem_cons_self
          · rw [hq] at h; cases h

/-! ## 3. The trace -/

def checkTraceAux (P : Protocol) : Sent → List Msg → Except TraceClause Unit
  | _, [] => .ok ()
  | sent, m :: rest =>
    match checkStep P sent m with
    | .ok () => checkTraceAux P (m :: sent) rest
    | .error k => .error k

/-- Check a trace, oldest message first. -/
def checkTrace (P : Protocol) (tr : List Msg) : Except TraceClause Unit :=
  checkTraceAux P [] tr

theorem checkTraceAux_sound (P : Protocol) :
    ∀ (tr : List Msg) (sent : Sent), Reach P sent → checkTraceAux P sent tr = .ok () →
      Reach P (tr.reverse ++ sent)
  | [], sent, hr, _ => by simpa using hr
  | m :: rest, sent, hr, h => by
    cases hc : checkStep P sent m with
    | ok u =>
      cases u
      simp only [checkTraceAux, hc] at h
      have hs := checkStep_sound hc
      have ih := checkTraceAux_sound P rest (m :: sent) (Reach.step hr hs) h
      simpa [List.reverse_cons, List.append_assoc] using ih
    | error k => simp only [checkTraceAux, hc] at h; cases h

/-- **An accepted trace is reachable.** -/
theorem checkTrace_sound {P : Protocol} {tr : List Msg} (h : checkTrace P tr = .ok ()) :
    Reach P tr.reverse := by
  have := checkTraceAux_sound P tr [] Reach.nil h
  simpa using this

/-! ## 4. The judge and the format -/

def TraceMeaning (P : Protocol) (tr : List Msg) : Prop := Reach P tr.reverse

def traceVerdict (P : Protocol) (tr : List Msg) : Obend.Judge.Verdict TraceClause :=
  match checkTrace P tr with
  | .ok () => .ok
  | .error k => .refused k []

theorem traceVerdict_ok {P : Protocol} {tr : List Msg} (h : traceVerdict P tr = .ok) :
    checkTrace P tr = .ok () := by
  unfold traceVerdict at h
  cases hc : checkTrace P tr with
  | ok u => cases u; rfl
  | error k => rw [hc] at h; cases h

@[instance_reducible] def simplexTraceJudge : Obend.Judge Protocol (List Msg) where
  Clause := TraceClause
  Meaning := TraceMeaning
  check _ P tr := traceVerdict P tr
  sound := by intro _ P tr h; exact checkTrace_sound (traceVerdict_ok h)
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ href; cases href
  Fragment _ := True
  complete := by intro P _ _; exact ⟨[], 0, rfl⟩
  mono := by intro _ _ _ _ _ _; rfl

/-- A committee of `3f+1` distinct nodes with the declared faulty ones bounded by `f`. -/
def mkProtocol? (committee : List Nat) (f : Nat) (faultyL : List Nat) : Option Protocol :=
  let faulty := fun n => faultyL.contains n
  if h : committee.Nodup ∧ committee.length = 3 * f + 1 ∧ (committee.filter faulty).length ≤ f then
    some ⟨committee, f, faulty, h.1, h.2.1, h.2.2⟩
  else none

def decodeProtocol (s : String) : Except String Protocol := do
  let j ← Json.parse s
  let committee ← (← (← j.getObjVal? "committee").getArr?).toList.mapM (·.getNat?)
  let f ← j.getObjValAs? Nat "f"
  let faultyL ← (← (← j.getObjVal? "faulty").getArr?).toList.mapM (·.getNat?)
  match mkProtocol? committee f faultyL with
  | some P => pure P
  | none => throw "the committee must be 3f+1 distinct nodes with at most f declared faulty"

def decodeEntry (j : Json) : Except String Entry := do
  match j.getObjVal? "dummy" with
  | .ok d => return .dummy (← d.getNat?)
  | .error _ =>
    let b ← j.getObjVal? "block"
    return .block (← b.getObjValAs? Nat "view") (← b.getObjValAs? Nat "payload")

def decodeTarget (j : Json) : Except String Target := do
  match j.getObjVal? "dummy" with
  | .ok d => return .dummy (← d.getNat?)
  | .error _ =>
    let arr ← (← j.getObjVal? "block").getArr?
    return .block (← arr.toList.mapM decodeEntry)

def decodeMsg (j : Json) : Except String Msg := do
  let sender ← j.getObjValAs? Nat "sender"
  let view ← j.getObjValAs? Nat "view"
  let kindS ← j.getObjValAs? String "kind"
  let kind ← match kindS with
    | "propose" => pure Kind.propose
    | "vote" => pure Kind.vote
    | "finalize" => pure Kind.finalize
    | other => throw s!"unknown message kind {other}"
  let target ← decodeTarget (← j.getObjVal? "target")
  pure { sender, view, kind, target }

def decodeTrace (s : String) : Except String (List Msg) := do
  let j ← Json.parse s
  (← j.getArr?).toList.mapM decodeMsg

def TraceClause.describe : TraceClause → String
  | .senderUnknown n => s!"node {n} sent a message but is neither in the committee nor declared faulty"
  | .notLeader n v => s!"node {n} proposed in view {v} but is not its leader"
  | .proposeNotBlock n v => s!"node {n} proposed a dummy in view {v}"
  | .votedTwice n v => s!"node {n} voted twice in view {v} (the same target: a repeat, not an equivocation)"
  | .equivocation r =>
    s!"equivocation: node {r.signers} voted in view {r.view} for {toString (repr r.a)} and for {toString (repr r.b)}; slashing receipt {toString (repr r)} checks against the trace"
  | .voteRule n v => s!"node {n}'s block vote in view {v} is not on notarized ground: the chain must end in a block of view {v}, extend a chain of {v - 1} notarized entries, and have been proposed by the leader"
  | .finalizeRule n v => s!"node {n} finalize-voted in view {v} for a block it did not vote for, or that is not notarized in the trace so far"
  | .finalizeNotBlock n v => s!"node {n} finalize-voted a dummy in view {v}"

/-- Why a witness was refused, for the session's error. -/
def explainTrace (_grade : Nat) (objWire certWire : String) : String :=
  match decodeProtocol objWire, decodeTrace certWire with
  | .error e, _ => s!"protocol: {e}"
  | _, .error e => s!"trace: {e}"
  | .ok P, .ok tr =>
    match checkTrace P tr with
    | .ok () => "accepted"
    | .error k => k.describe

/-- The planted bad pair: a committee of four with none declared faulty, and a vote by a node
outside it. -/
def badProtocol : Protocol :=
  ⟨[0, 1, 2, 3], 1, fun _ => false, by decide, by decide, by decide⟩

def badTrace : List Msg := [⟨7, 1, .vote, .dummy 1⟩]

theorem badTrace_refused :
    simplexTraceJudge.check 0 badProtocol badTrace = .refused (.senderUnknown 7) [] := rfl

/-- **The registered format `simplex-trace@1`**: object, the committee and the declared faulty
set; certificate, a node's run as the messages sent in order. -/
def simplexTraceFormat : Obend.Judge.Format where
  name := "simplex-trace"
  version := "1"
  Obj := Protocol
  Cert := List Msg
  judge := simplexTraceJudge
  decodeObj := decodeProtocol
  decodeCert := decodeTrace
  trust := .kernel
  regime := .decidable
  bad := (badProtocol, badTrace)
  badGrade := 0
  bad_refused := ⟨.senderUnknown 7, [], badTrace_refused⟩
  explain := explainTrace

end Obend.Consensus.SimplexTrace
end
