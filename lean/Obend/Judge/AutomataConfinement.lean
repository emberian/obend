module
/-
# Obend.Judge.AutomataConfinement — Inner-System Parser-Automata, Prompt-Confinement & Hoard-Clearing Judges

Integrates the inner-system verification mechanisms from `Dregg2` (`CfgCompact`, `DfaAcceptanceAir`,
`ZkHandlebars`) and `dclutch` (`EconomicKernel`, `JointClearingV1`) into `Obend`'s `Obend.Judge`,
`Obend.Slot.Protocol`, `Obend.Core.Term`, and `Obend.Leaf.Book` spine:

1. **Pillar A — Brzozowski / Table-DFA Trace & Complement Confinement (`TableDfa`, `dfaAccepts`, `dfaFormat`)**:
   Deterministic byte/token table automaton with rolling AIR digest commitment (`runningDigest`),
   Brzozowski derivative regex engine (`BrzozowskiRegex`), complement confinement guard (`InjectionFree`)
   forbidding handlebars/role-header control sequences (`"{{"`, `"}}"`, `"<|system|>"`, `"<|assistant|>"`),
   and registered `Obend.Judge.Format` (`"dfa-confinement"` v`"1"`).
2. **Pillar B — $O(\text{tokens})$ Compact Pushdown CFG Replay Certificate (`CfgRule`, `PushdownReplay`, `cfgCompactFormat`)**:
   Leftmost-derivation pushdown replay (`replayCfgCompact`) with inductive specification `PushdownReplay`,
   CFG derivation soundness (`replayCfgCompact_sound`), and registered `Obend.Judge.Format` (`"cfg-compact"` v`"1"`).
3. **Pillar C — Structured Prompt & Transcript Slot Confinement (`PromptTemplate`, `Seg.lit`, `Seg.slot`, `slot_confinement`)**:
   Semi-unstructured templates with trusted literal segments (`Seg.lit`) and untrusted `Core4` /
   `Slot.Protocol` / `Leaf.Book` holes (`Seg.slot`), proving `slot_confinement`
   (`controlTokens (renderPrompt b T) = controlTokens (litOnly T)`) under `AllSlotsClean`, plus the
   refutation tooth `injected_slot_breaks_confinement`.
4. **Pillar D — `dclutch` Liquidation-Cascade-Free Hoard Complete-Set & Joint KKT Clearing Judge
   (`HoardMarketState`, `JointClearingCert`, `dclutchHoardFormat`)**:
   Full collateral backing invariant (`∀ i < outcomes, s.supplyAt i ≤ s.hoard`) preserved under
   `splitCompleteSet` and `mergeCompleteSet`, $N$-outcome simplex KKT clearing certificate
   (`prices.sum == scale`, `collectedQuote == scale * sets`, `filled_at_or_better`, KKT optimality),
   and registered `Obend.Judge.Format` (`"dclutch-hoard-clearing"` v`"1"`).
-/

public import Lean.Data.Json
public import Obend.Judge.Class
public import Obend.Judge.Clearing
public import Obend.Slot.Protocol
public import Obend.Core.Term
public import Obend.Leaf.Emit

@[expose] public section
namespace Obend.Judge

open Lean (Json toJson)
open Obend.Core.Term
open Obend.Slot.Protocol
open Obend.Leaf

set_option autoImplicit false

/-! ## Pillar A: Brzozowski / Table-DFA Trace & Complement Confinement -/

/-- Reserved control tokens (handlebars delimiters and role-header markers) forbidden in untrusted slots. -/
def forbiddenControlTokens : List String :=
  ["{{", "}}", "<|system|>", "<|assistant|>"]

/-- Predicate testing whether `tok` is a reserved control / delimiter token. -/
def isControlToken (tok : String) : Bool :=
  tok == "{{" || tok == "}}" || tok == "<|system|>" || tok == "<|assistant|>"

/-- Extract the subsequence of control tokens from a token stream, in order. -/
def controlTokens (tokens : List String) : List String :=
  tokens.filter isControlToken

@[simp] theorem controlTokens_nil : controlTokens [] = [] := rfl

theorem controlTokens_cons (t : String) (ts : List String) :
    controlTokens (t :: ts) = if isControlToken t then t :: controlTokens ts else controlTokens ts := by
  simp [controlTokens, List.filter_cons]

theorem controlTokens_append (xs ys : List String) :
    controlTokens (xs ++ ys) = controlTokens xs ++ controlTokens ys := by
  simp [controlTokens, List.filter_append]

/-- Brzozowski derivative regular expression with Boolean complement for token-stream guards. -/
inductive BrzozowskiRegex where
  | empty
  | eps
  | tok (expected : String)
  | anyTok
  | controlTok
  | alt (r1 r2 : BrzozowskiRegex)
  | seq (r1 r2 : BrzozowskiRegex)
  | star (r : BrzozowskiRegex)
  | complement (r : BrzozowskiRegex)
  deriving DecidableEq, Repr

/-- Brzozowski nullability: whether `r` accepts the empty token stream `[]`. -/
def BrzozowskiRegex.nullable : BrzozowskiRegex → Bool
  | .empty => false
  | .eps => true
  | .tok _ => false
  | .anyTok => false
  | .controlTok => false
  | .alt r1 r2 => r1.nullable || r2.nullable
  | .seq r1 r2 => r1.nullable && r2.nullable
  | .star _ => true
  | .complement r => !r.nullable

/-- Brzozowski derivative with respect to a single token `t`. -/
def BrzozowskiRegex.deriv (t : String) : BrzozowskiRegex → BrzozowskiRegex
  | .empty => .empty
  | .eps => .empty
  | .tok expected => if t == expected then .eps else .empty
  | .anyTok => .eps
  | .controlTok => if isControlToken t then .eps else .empty
  | .alt r1 r2 => .alt (r1.deriv t) (r2.deriv t)
  | .seq r1 r2 =>
    if r1.nullable then
      .alt (.seq (r1.deriv t) r2) (r2.deriv t)
    else
      .seq (r1.deriv t) r2
  | .star r => .seq (r.deriv t) (.star r)
  | .complement r => .complement (r.deriv t)

/-- Match a token stream against a `BrzozowskiRegex` by folding derivatives. -/
def brzozowskiMatches (r : BrzozowskiRegex) : List String → Bool
  | [] => r.nullable
  | t :: ts => brzozowskiMatches (r.deriv t) ts

theorem brzozowskiMatches_complement (r : BrzozowskiRegex) (tokens : List String) :
    brzozowskiMatches (.complement r) tokens = !brzozowskiMatches r tokens := by
  induction tokens generalizing r with
  | nil => rfl
  | cons t ts ih =>
    simp only [brzozowskiMatches, BrzozowskiRegex.deriv]
    exact ih (r.deriv t)

/-- Deterministic table automaton (`TableDfa`) over `Nat` states and `String` tokens.
    `transitions` gives explicit `(state, token) ↦ nextState` entries, `stateDefaults`
    gives per-state wildcard transitions `(state ↦ defaultNext)`, and `defaultSink`
    is the global fallback state. -/
structure TableDfa where
  start : Nat
  accepting : List Nat
  transitions : List ((Nat × String) × Nat)
  stateDefaults : List (Nat × Nat) := []
  defaultSink : Nat := 0
  deriving DecidableEq, Repr

/-- Deterministic single-step table transition function `δ(q, tok)`. -/
def TableDfa.step (d : TableDfa) (q : Nat) (tok : String) : Nat :=
  match d.transitions.lookup (q, tok) with
  | some next => next
  | none =>
    match d.stateDefaults.lookup q with
    | some defNext => defNext
    | none => d.defaultSink

/-- Single decimal digit string for `d % 10` (0 axioms, kernel-reducible). -/
def digitString (d : Nat) : String :=
  match d % 10 with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"

/-- Fuel-bounded decimal digit extraction using `String.append` (purely structural, 0 `Classical.choice`). -/
def natToDecStringAux : Nat → Nat → String → String
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc' := digitString n ++ acc
    if n < 10 then acc' else natToDecStringAux fuel (n / 10) acc'

/-- Constructive `Nat → String` decimal formatter (0 axioms, reduces by `rfl`). -/
def natToDecString (n : Nat) : String :=
  natToDecStringAux (n + 1) n ""

/-- State reached by running `d` from state `q` over `tokens`. -/
def dfaClassifyFrom (d : TableDfa) (q : Nat) : List String → Nat
  | [] => q
  | tok :: rest => dfaClassifyFrom d (d.step q tok) rest

/-- State reached by running `d` from `d.start` over `tokens`. -/
def dfaClassify (d : TableDfa) (tokens : List String) : Nat :=
  dfaClassifyFrom d d.start tokens

/-- Method alias `d.classify tokens` for `dfaClassify d tokens`. -/
def TableDfa.classify (d : TableDfa) (tokens : List String) : Nat :=
  dfaClassify d tokens

/-- Boolean acceptance decision of `d` on `tokens`. -/
def dfaAccepts (d : TableDfa) (tokens : List String) : Bool :=
  d.accepting.contains (dfaClassify d tokens)

@[simp] theorem dfaClassifyFrom_nil (d : TableDfa) (q : Nat) :
    dfaClassifyFrom d q [] = q := rfl

@[simp] theorem dfaClassifyFrom_cons (d : TableDfa) (q : Nat) (tok : String) (rest : List String) :
    dfaClassifyFrom d q (tok :: rest) = dfaClassifyFrom d (d.step q tok) rest := rfl

theorem dfaClassifyFrom_append (d : TableDfa) (q : Nat) (xs ys : List String) :
    dfaClassifyFrom d q (xs ++ ys) = dfaClassifyFrom d (dfaClassifyFrom d q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.cons_append, dfaClassifyFrom_cons]
    exact ih (d.step q x)

/-- Brzozowski state-set derivative step over a `TableDfa`. -/
def brzozowskiStep (d : TableDfa) (states : List Nat) (tok : String) : List Nat :=
  states.map (fun q => d.step q tok)

/-- Multi-token Brzozowski state-set derivative run. -/
def brzozowskiRun (d : TableDfa) (states : List Nat) : List String → List Nat
  | [] => states
  | tok :: rest => brzozowskiRun d (brzozowskiStep d states tok) rest

/-- Acceptance of a Brzozowski state-set derivative run. -/
def brzozowskiAccepts (d : TableDfa) (states : List Nat) (tokens : List String) : Bool :=
  (brzozowskiRun d states tokens).any (fun q => d.accepting.contains q)

theorem brzozowskiRun_singleton (d : TableDfa) (q : Nat) (tokens : List String) :
    brzozowskiRun d [q] tokens = [dfaClassifyFrom d q tokens] := by
  induction tokens generalizing q with
  | nil => rfl
  | cons tok rest ih =>
    simp only [brzozowskiRun, brzozowskiStep, List.map_cons, List.map_nil, dfaClassifyFrom_cons]
    exact ih (d.step q tok)

/-- Singleton Brzozowski state-set acceptance coincides with `dfaAccepts`. -/
theorem brzozowskiAccepts_singleton_eq (d : TableDfa) (tokens : List String) :
    brzozowskiAccepts d [d.start] tokens = dfaAccepts d tokens := by
  unfold brzozowskiAccepts dfaAccepts dfaClassify
  rw [brzozowskiRun_singleton]
  simp [List.any_cons, List.any_nil]

/-- Complement a `TableDfa` over state space `0 .. numStates - 1` by inverting `accepting`. -/
def TableDfa.complement (d : TableDfa) (numStates : Nat := 2) : TableDfa :=
  { d with accepting := (List.range numStates).filter (fun q => !d.accepting.contains q) }

theorem dfaClassifyFrom_complement (d : TableDfa) (numStates q : Nat) (tokens : List String) :
    dfaClassifyFrom (d.complement numStates) q tokens = dfaClassifyFrom d q tokens := by
  induction tokens generalizing q with
  | nil => rfl
  | cons tok rest ih =>
    simp only [dfaClassifyFrom_cons]
    have hStep : (d.complement numStates).step q tok = d.step q tok := rfl
    rw [hStep]
    exact ih (d.step q tok)

theorem dfaClassify_complement (d : TableDfa) (numStates : Nat) (tokens : List String) :
    dfaClassify (d.complement numStates) tokens = dfaClassify d tokens :=
  dfaClassifyFrom_complement d numStates d.start tokens

/-- Complement DFA acceptance is the Boolean negation of `dfaAccepts` whenever the reached
    state lies within the declared state space `dfaClassify d tokens < numStates`. -/
theorem dfaAccepts_complement_eq (d : TableDfa) (numStates : Nat) (tokens : List String)
    (hBound : dfaClassify d tokens < numStates) :
    dfaAccepts (d.complement numStates) tokens = !dfaAccepts d tokens := by
  unfold dfaAccepts
  rw [dfaClassify_complement]
  unfold TableDfa.complement
  dsimp only
  generalize dfaClassify d tokens = q at hBound ⊢
  have hMemRange : q ∈ List.range numStates := List.mem_range.mpr hBound
  cases hAcc : d.accepting.contains q
  · simp only [Bool.not_false]
    rw [List.contains_iff_mem, List.mem_filter]
    exact ⟨hMemRange, by rw [hAcc]; rfl⟩
  · simp only [Bool.not_true]
    cases hComp : ((List.range numStates).filter (fun x => !d.accepting.contains x)).contains q
    · rfl
    · rw [List.contains_iff_mem, List.mem_filter] at hComp
      rw [hAcc] at hComp
      cases hComp.2

theorem dfaAccepts_complement_iff (d : TableDfa) (numStates : Nat) (tokens : List String)
    (hBound : dfaClassify d tokens < numStates) :
    dfaAccepts (d.complement numStates) tokens = true ↔ dfaAccepts d tokens = false := by
  rw [dfaAccepts_complement_eq d numStates tokens hBound, Bool.not_eq_true']

/-- Deterministic token encoding for rolling AIR trace commitments (0 axioms, collision-free on vocabulary). -/
def tokenCode (s : String) : Nat :=
  if s == "{{" then 101
  else if s == "}}" then 102
  else if s == "<|system|>" then 103
  else if s == "<|assistant|>" then 104
  else if s == "hello" then 201
  else if s == "world" then 202
  else if s == "injected_prompt" then 203
  else if s == "alpha" then 204
  else if s == "bravo" then 205
  else if s == "charlie" then 206
  else if s == "delta" then 207
  else if s == "foo" then 208
  else if s == "bar" then 209
  else if s == "baz" then 210
  else if s == "summarize" then 211
  else if s == "the" then 212
  else if s == "quarterly" then 213
  else if s == "report" then 214
  else if s == "ignore" then 215
  else if s == "override" then 216
  else if s == "clean" then 217
  else if s == "argument" then 218
  else if s == "first" then 219
  else if s == "question" then 220
  else if s == "safe" then 221
  else if s == "arg3" then 222
  else if s == "arg4" then 223
  else s.utf8ByteSize + 300

/-- 2-to-1 compression function for rolling trace digests. -/
def compressDigest (acc x : Nat) : Nat :=
  (acc * 1000003 + x + 97) % 1000000007

/-- 4-to-1 entry digest for a single DFA transition `(state, tok, next, 0)`. -/
def dfaEntryDigest (state : Nat) (tok : String) (next : Nat) : Nat :=
  compressDigest (compressDigest (compressDigest state (tokenCode tok)) next) 0

/-- Rolling digest commitment (`runningDigestFrom`) from starting state `q` and `seed`. -/
def runningDigestFrom (d : TableDfa) (seed : Nat) (q : Nat) : List String → Nat
  | [] => seed
  | tok :: rest =>
    let next := d.step q tok
    let entry := dfaEntryDigest q tok next
    runningDigestFrom d (compressDigest seed entry) next rest

/-- Rolling digest commitment (`runningDigest`) binding the full transition trace of `d`
    on `tokens` from `seed` (`tableCommitment`). -/
def runningDigest (d : TableDfa) (seed : Nat) (tokens : List String) : Nat :=
  runningDigestFrom d seed d.start tokens

@[simp] theorem runningDigestFrom_nil (d : TableDfa) (seed q : Nat) :
    runningDigestFrom d seed q [] = seed := rfl

@[simp] theorem runningDigestFrom_cons (d : TableDfa) (seed q : Nat) (tok : String) (rest : List String) :
    runningDigestFrom d seed q (tok :: rest) =
      runningDigestFrom d (compressDigest seed (dfaEntryDigest q tok (d.step q tok))) (d.step q tok) rest := rfl

theorem runningDigestFrom_append (d : TableDfa) (seed q : Nat) (xs ys : List String) :
    runningDigestFrom d seed q (xs ++ ys) =
      runningDigestFrom d (runningDigestFrom d seed q xs) (dfaClassifyFrom d q xs) ys := by
  induction xs generalizing seed q with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.cons_append, runningDigestFrom_cons, dfaClassifyFrom_cons]
    exact ih (compressDigest seed (dfaEntryDigest q x (d.step q x))) (d.step q x)

/-- One row of a DFA execution trace (`Dregg2.Crypto.DfaAcceptanceAir.Row`). -/
structure DfaTraceRow where
  state : Nat
  sym : String
  next : Nat
  entryHash : Nat
  running : Nat
  deriving DecidableEq, Repr

/-- Build the canonical AIR trace rows from state `q` and rolling digest `seed`. -/
def buildDfaTraceFrom (d : TableDfa) (seed : Nat) (q : Nat) : List String → List DfaTraceRow
  | [] => []
  | tok :: rest =>
    let next := d.step q tok
    let entry := dfaEntryDigest q tok next
    let run' := compressDigest seed entry
    { state := q, sym := tok, next := next, entryHash := entry, running := run' } ::
      buildDfaTraceFrom d run' next rest

/-- Build the canonical AIR trace for `d` on `tokens` starting from `seed`. -/
def buildDfaTrace (d : TableDfa) (seed : Nat) (tokens : List String) : List DfaTraceRow :=
  buildDfaTraceFrom d seed d.start tokens

/-- Verify step-by-step AIR transition and rolling-digest constraints on a trace row list. -/
def verifyDfaTraceRows (d : TableDfa) (seed : Nat) (q : Nat) : List String → List DfaTraceRow → Bool
  | [], [] => true
  | tok :: restToks, row :: restRows =>
    let next := d.step q tok
    let entry := dfaEntryDigest q tok next
    let run' := compressDigest seed entry
    (row.state == q) &&
    (tokenCode row.sym == tokenCode tok) &&
    (row.next == next) &&
    (row.entryHash == entry) &&
    (row.running == run') &&
    verifyDfaTraceRows d run' next restToks restRows
  | _, _ => false

theorem buildDfaTraceFrom_length (d : TableDfa) (seed q : Nat) (tokens : List String) :
    (buildDfaTraceFrom d seed q tokens).length = tokens.length := by
  induction tokens generalizing seed q with
  | nil => rfl
  | cons tok rest ih =>
    simp only [buildDfaTraceFrom, List.length_cons]
    rw [ih]

theorem buildDfaTrace_length (d : TableDfa) (seed : Nat) (tokens : List String) :
    (buildDfaTrace d seed tokens).length = tokens.length :=
  buildDfaTraceFrom_length d seed d.start tokens

theorem buildDfaTraceFrom_valid (d : TableDfa) (seed q : Nat) (tokens : List String) :
    verifyDfaTraceRows d seed q tokens (buildDfaTraceFrom d seed q tokens) = true := by
  induction tokens generalizing seed q with
  | nil => rfl
  | cons tok rest ih =>
    simp only [buildDfaTraceFrom, verifyDfaTraceRows, beq_self_eq_true, Bool.true_and]
    exact ih _ _

/-- The canonical AIR trace built by `buildDfaTrace` satisfies all row transition & hash constraints. -/
theorem buildDfaTrace_valid (d : TableDfa) (seed : Nat) (tokens : List String) :
    verifyDfaTraceRows d seed d.start tokens (buildDfaTrace d seed tokens) = true :=
  buildDfaTraceFrom_valid d seed d.start tokens

/-- Complement confinement DFA (`confinementDfa`):
    - State `0` is the clean, accepting state.
    - State `1` is the absorbing injection-trap state.
    Any occurrence of `"{{"`, `"}}"`, `"<|system|>"`, or `"<|assistant|>"` transitions `0 → 1`
    and remains trapped in `1`. -/
def confinementDfa : TableDfa where
  start := 0
  accepting := [0]
  transitions := [
    ((0, "{{"), 1),
    ((0, "}}"), 1),
    ((0, "<|system|>"), 1),
    ((0, "<|assistant|>"), 1)
  ]
  stateDefaults := [(0, 0), (1, 1)]
  defaultSink := 1

theorem confinementDfa_step_trap (tok : String) :
    confinementDfa.step 1 tok = 1 := by
  unfold TableDfa.step confinementDfa
  rfl

theorem confinementDfa_classifyFrom_trap (tokens : List String) :
    dfaClassifyFrom confinementDfa 1 tokens = 1 := by
  induction tokens with
  | nil => rfl
  | cons tok rest ih =>
    simp only [dfaClassifyFrom_cons, confinementDfa_step_trap]
    exact ih

private theorem prod_zero_beq (a b : String) :
    (((0 : Nat), a) == (0, b)) = (a == b) := rfl

theorem confinementDfa_step_zero (tok : String) :
    confinementDfa.step 0 tok = if isControlToken tok then 1 else 0 := by
  unfold TableDfa.step confinementDfa isControlToken
  dsimp only [List.lookup]
  rw [prod_zero_beq, prod_zero_beq, prod_zero_beq, prod_zero_beq]
  generalize (tok == "{{") = b1
  generalize (tok == "}}") = b2
  generalize (tok == "<|system|>") = b3
  generalize (tok == "<|assistant|>") = b4
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

theorem confinementDfa_classifyFrom_zero (tokens : List String) :
    dfaClassifyFrom confinementDfa 0 tokens =
      if tokens.any isControlToken then 1 else 0 := by
  induction tokens with
  | nil => rfl
  | cons tok rest ih =>
    cases hctrl : isControlToken tok
    · simp [dfaClassifyFrom_cons, confinementDfa_step_zero, hctrl, ih]
    · simp [dfaClassifyFrom_cons, confinementDfa_step_zero, hctrl, confinementDfa_classifyFrom_trap]

theorem dfaAccepts_confinementDfa_eq (tokens : List String) :
    dfaAccepts confinementDfa tokens = !(tokens.any isControlToken) := by
  unfold dfaAccepts dfaClassify
  change [0].contains (dfaClassifyFrom confinementDfa 0 tokens) = !(tokens.any isControlToken)
  rw [confinementDfa_classifyFrom_zero]
  cases tokens.any isControlToken <;> rfl

theorem list_any_eq_false_iff {α : Type} (p : α → Bool) (l : List α) :
    l.any p = false ↔ ∀ x ∈ l, p x = false := by
  induction l with
  | nil =>
    simp only [List.any_nil, true_iff]
    intro _ h; cases h
  | cons a as ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, ih]
    constructor
    · intro ⟨ha, has⟩ x hx
      cases hx with
      | head => exact ha
      | tail _ hmem => exact has x hmem
    · intro h
      exact ⟨h a List.mem_cons_self, fun x hx => h x (List.mem_cons_of_mem a hx)⟩

/-- Declarative complement guard `InjectionFree`: no token in `tokens` is a reserved
    control or delimiter token (`isControlToken tok = false`). -/
def InjectionFree (tokens : List String) : Prop :=
  ∀ tok ∈ tokens, isControlToken tok = false

theorem injectionFree_iff_dfaAccepts (tokens : List String) :
    InjectionFree tokens ↔ dfaAccepts confinementDfa tokens = true := by
  unfold InjectionFree
  rw [dfaAccepts_confinementDfa_eq, Bool.not_eq_true', list_any_eq_false_iff]

theorem filter_isControlToken_eq_nil_iff (tokens : List String) :
    controlTokens tokens = [] ↔ ∀ tok ∈ tokens, isControlToken tok = false := by
  unfold controlTokens
  induction tokens with
  | nil =>
    dsimp only [List.filter]
    constructor
    · intro _ _ h; cases h
    · intro _; rfl
  | cons a as ih =>
    dsimp only [List.filter]
    cases ha : isControlToken a
    · rw [ih]
      constructor
      · intro has x hx
        cases hx with
        | head => exact ha
        | tail _ hmem => exact has x hmem
      · intro h x hx
        exact h x (List.mem_cons_of_mem a hx)
    · constructor
      · intro h; cases h
      · intro h
        have := h a List.mem_cons_self
        rw [ha] at this
        cases this

theorem injectionFree_iff_controlTokens_nil (tokens : List String) :
    InjectionFree tokens ↔ controlTokens tokens = [] :=
  (filter_isControlToken_eq_nil_iff tokens).symm

/-- Object for the DFA confinement & trace-commitment judge. -/
structure DfaConfinementQuery where
  dfa : TableDfa
  tableSeed : Nat
  expectedFinalState : Nat
  requireInjectionFree : Bool := true
  deriving DecidableEq, Repr

/-- Certificate for the DFA confinement judge: the token stream and its claimed rolling digest. -/
structure DfaConfinementCert where
  tokens : List String
  claimedDigest : Nat
  deriving DecidableEq, Repr

/-- Refusal clauses for the DFA confinement judge. -/
inductive DfaRefusal where
  | injectionDetected (offendingToken : String)
  | notAccepted (reachedState : Nat)
  | finalStateMismatch (reached expected : Nat)
  | digestMismatch (computed claimed : Nat)
  deriving DecidableEq, Repr

/-- Executable checker for `DfaConfinementQuery` and `DfaConfinementCert`. -/
def verifyDfaConfinement (q : DfaConfinementQuery) (c : DfaConfinementCert) :
    Except DfaRefusal Unit :=
  match q.requireInjectionFree && !dfaAccepts confinementDfa c.tokens with
  | true => .error (.injectionDetected ((c.tokens.find? isControlToken).getD "{{"))
  | false =>
    match dfaAccepts q.dfa c.tokens with
    | false => .error (.notAccepted (dfaClassify q.dfa c.tokens))
    | true =>
      match dfaClassify q.dfa c.tokens == q.expectedFinalState with
      | false => .error (.finalStateMismatch (dfaClassify q.dfa c.tokens) q.expectedFinalState)
      | true =>
        match runningDigest q.dfa q.tableSeed c.tokens == c.claimedDigest with
        | false => .error (.digestMismatch (runningDigest q.dfa q.tableSeed c.tokens) c.claimedDigest)
        | true => .ok ()

/-- Declarative semantic specification for `dfaConfinementJudge`. -/
def DfaConfinementMeaning (q : DfaConfinementQuery) (c : DfaConfinementCert) : Prop :=
  dfaAccepts q.dfa c.tokens = true ∧
  dfaClassify q.dfa c.tokens = q.expectedFinalState ∧
  runningDigest q.dfa q.tableSeed c.tokens = c.claimedDigest ∧
  (q.requireInjectionFree = true → InjectionFree c.tokens)

theorem verifyDfaConfinement_sound {q : DfaConfinementQuery} {c : DfaConfinementCert}
    (h : verifyDfaConfinement q c = .ok ()) :
    DfaConfinementMeaning q c := by
  unfold verifyDfaConfinement at h
  cases h1 : (q.requireInjectionFree && !dfaAccepts confinementDfa c.tokens) <;> rw [h1] at h
  · cases h2 : dfaAccepts q.dfa c.tokens <;> rw [h2] at h
    · cases h
    · cases h3 : (dfaClassify q.dfa c.tokens == q.expectedFinalState) <;> rw [h3] at h
      · cases h
      · cases h4 : (runningDigest q.dfa q.tableSeed c.tokens == c.claimedDigest) <;> rw [h4] at h
        · cases h
        · refine ⟨h2, beq_iff_eq.mp h3, beq_iff_eq.mp h4, ?_⟩
          intro hReq
          apply (injectionFree_iff_dfaAccepts c.tokens).mpr
          cases hConf : dfaAccepts confinementDfa c.tokens
          · rw [hReq, hConf] at h1
            cases h1
          · rfl
  · cases h

/-- Standalone verdict checker for `DfaConfinementQuery` and `DfaConfinementCert`. -/
def dfaConfinementCheck (_ : Nat) (q : DfaConfinementQuery) (c : DfaConfinementCert) :
    Verdict DfaRefusal :=
  match verifyDfaConfinement q c with
  | .ok () => .ok
  | .error r => .refused r []

/-- `Judge` instance for `DfaConfinementQuery` and `DfaConfinementCert`. -/
instance dfaConfinementJudge : Judge DfaConfinementQuery DfaConfinementCert where
  Clause := DfaRefusal
  Meaning := DfaConfinementMeaning
  check := dfaConfinementCheck
  sound := by
    intro _ q c h
    unfold dfaConfinementCheck at h
    cases hVer : verifyDfaConfinement q c with
    | ok u =>
      cases u
      exact verifyDfaConfinement_sound hVer
    | error r => rw [hVer] at h; cases h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment q := ∃ c, verifyDfaConfinement q c = .ok ()
  complete := by
    intro _ ⟨c, hc⟩ _
    refine ⟨c, 0, ?_⟩
    unfold dfaConfinementCheck
    rw [hc]
  mono := by intro _ _ _ _ _ _; rfl

/-- Default query for `dfaFormat`: checks `confinementDfa` with `tableSeed = 7`, `expectedFinalState = 0`. -/
def defaultDfaQuery : DfaConfinementQuery where
  dfa := confinementDfa
  tableSeed := 7
  expectedFinalState := 0
  requireInjectionFree := true

/-- Valid clean certificate for `defaultDfaQuery`. -/
def goodDfaCert : DfaConfinementCert where
  tokens := ["hello", "world"]
  claimedDigest := runningDigest confinementDfa 7 ["hello", "world"]

/-- Planted bad certificate (`badCert`) containing an injected handlebars control token `"{{"`. -/
def badCert : DfaConfinementCert where
  tokens := ["hello", "{{", "injected_prompt"]
  claimedDigest := runningDigest confinementDfa 7 ["hello", "{{", "injected_prompt"]

theorem goodDfaCert_accepted :
    dfaConfinementCheck 1 defaultDfaQuery goodDfaCert = .ok :=
  rfl

theorem badCert_refused :
    dfaConfinementCheck 1 defaultDfaQuery badCert =
      .refused (.injectionDetected "{{") [] :=
  rfl

/-- Encode `TableDfa` to `Lean.Json`. -/
def tableDfaToJson (d : TableDfa) : Json :=
  Json.mkObj
    [ ("start", toJson d.start)
    , ("accepting", Json.arr (d.accepting.map toJson).toArray)
    , ("transitions", Json.arr (d.transitions.map fun ((q, tok), nxt) =>
        Json.mkObj [("state", toJson q), ("token", Json.str tok), ("next", toJson nxt)]).toArray)
    , ("stateDefaults", Json.arr (d.stateDefaults.map fun (q, nxt) =>
        Json.mkObj [("state", toJson q), ("next", toJson nxt)]).toArray)
    , ("defaultSink", toJson d.defaultSink) ]

/-- Parse `TableDfa` from `Lean.Json`. -/
def tableDfaOfJson (j : Json) : Except String TableDfa := do
  let start ← j.getObjValAs? Nat "start"
  let accepting ← (← (← j.getObjVal? "accepting").getArr?).toList.mapM (·.getNat?)
  let trArr ← (← j.getObjVal? "transitions").getArr?
  let transitions ← trArr.toList.mapM fun item => do
    let q ← item.getObjValAs? Nat "state"
    let tok ← item.getObjValAs? String "token"
    let nxt ← item.getObjValAs? Nat "next"
    pure ((q, tok), nxt)
  let defArr ← (← j.getObjVal? "stateDefaults").getArr?
  let stateDefaults ← defArr.toList.mapM fun item => do
    let q ← item.getObjValAs? Nat "state"
    let nxt ← item.getObjValAs? Nat "next"
    pure (q, nxt)
  let defaultSink ← j.getObjValAs? Nat "defaultSink"
  pure { start, accepting, transitions, stateDefaults, defaultSink }

/-- Encode `DfaConfinementQuery` as canonical JSON wire string. -/
def encodeDfaQuery (q : DfaConfinementQuery) : String :=
  Json.compress <| Json.mkObj
    [ ("dfa", tableDfaToJson q.dfa)
    , ("tableSeed", toJson q.tableSeed)
    , ("expectedFinalState", toJson q.expectedFinalState)
    , ("requireInjectionFree", toJson q.requireInjectionFree) ]

/-- Encode `DfaConfinementCert` as canonical JSON wire string. -/
def encodeDfaCert (c : DfaConfinementCert) : String :=
  Json.compress <| Json.mkObj
    [ ("tokens", Json.arr (c.tokens.map Json.str).toArray)
    , ("claimedDigest", toJson c.claimedDigest) ]

/-- Parse `DfaConfinementQuery` from JSON wire string. -/
def decodeDfaQuery (s : String) : Except String DfaConfinementQuery := do
  let j ← Json.parse s
  let dfa ← tableDfaOfJson (← j.getObjVal? "dfa")
  let tableSeed ← j.getObjValAs? Nat "tableSeed"
  let expectedFinalState ← j.getObjValAs? Nat "expectedFinalState"
  let requireInjectionFree ← j.getObjValAs? Bool "requireInjectionFree"
  pure { dfa, tableSeed, expectedFinalState, requireInjectionFree }

/-- Parse `DfaConfinementCert` from JSON wire string. -/
def decodeDfaCert (s : String) : Except String DfaConfinementCert := do
  let j ← Json.parse s
  let tokens ← (← (← j.getObjVal? "tokens").getArr?).toList.mapM (·.getStr?)
  let claimedDigest ← j.getObjValAs? Nat "claimedDigest"
  pure { tokens, claimedDigest }

/-- Registered `Obend.Judge.Format` for `dfa-confinement` v`1`. -/
def dfaFormat : Judge.Format where
  name := "dfa-confinement"
  version := "1"
  Obj := DfaConfinementQuery
  Cert := DfaConfinementCert
  decodeObj := decodeDfaQuery
  decodeCert := decodeDfaCert
  trust := .kernel
  regime := .decidable
  bad := (defaultDfaQuery, badCert)
  badGrade := 1
  bad_refused := ⟨_, _, badCert_refused⟩


/-! ## Pillar B: $O(\text{tokens})$ Compact Pushdown CFG Replay Certificate -/

/-- A symbol in a context-free grammar: a terminal token or a nonterminal variable. -/
inductive CfgSym where
  | terminal (tok : String)
  | nonterminal (nt : String)
  deriving DecidableEq, Repr

/-- A production rule `lhs → rhs` in a context-free grammar. -/
structure CfgRule where
  lhs : String
  rhs : List CfgSym
  deriving DecidableEq, Repr

/-- A context-free grammar with start nonterminal `start` and production list `rules`. -/
structure CfgGrammar where
  start : String
  rules : List CfgRule
  deriving DecidableEq, Repr

/-- One-step context-free production `u ⇒ v` under grammar `g`. -/
inductive CfgProduces (g : CfgGrammar) : List CfgSym → List CfgSym → Prop where
  | head (r : CfgRule) (stk : List CfgSym) (hr : r ∈ g.rules) :
      CfgProduces g (.nonterminal r.lhs :: stk) (r.rhs ++ stk)
  | under (s : CfgSym) {u v : List CfgSym} :
      CfgProduces g u v → CfgProduces g (s :: u) (s :: v)

/-- Multi-step context-free derivation `u ⇒* v` (reflexive-transitive closure of `CfgProduces`). -/
inductive CfgDerives (g : CfgGrammar) : List CfgSym → List CfgSym → Prop where
  | refl (u : List CfgSym) : CfgDerives g u u
  | step {u v w : List CfgSym} : CfgProduces g u v → CfgDerives g v w → CfgDerives g u w

theorem CfgDerives.cons_sym {g : CfgGrammar} (s : CfgSym) {u v : List CfgSym}
    (h : CfgDerives g u v) : CfgDerives g (s :: u) (s :: v) := by
  induction h with
  | refl u => exact .refl (s :: u)
  | step hp _ ih => exact .step (.under s hp) ih

/-- Inductive specification of $O(\text{tokens})$ leftmost pushdown replay (`Dregg2.Crypto.CfgCompact.Replay`):
    `PushdownReplay g rs input stk` holds when the rule sequence `rs` drives a leftmost pushdown
    derivation from stack `stk` consuming `input`. -/
inductive PushdownReplay (g : CfgGrammar) :
    List CfgRule → List String → List CfgSym → Prop where
  | done : PushdownReplay g [] [] []
  | term (t : String) {rs : List CfgRule} {input : List String} {stk : List CfgSym} :
      PushdownReplay g rs input stk →
      PushdownReplay g rs (t :: input) (.terminal t :: stk)
  | rule {r : CfgRule} {rs : List CfgRule} {input : List String} {stk : List CfgSym}
      (hr : r ∈ g.rules) :
      PushdownReplay g rs input (r.rhs ++ stk) →
      PushdownReplay g (r :: rs) input (.nonterminal r.lhs :: stk)

/-- Every accepting `PushdownReplay` from stack `stk` witnesses a genuine CFG derivation
    `CfgDerives g stk (input.map .terminal)`. -/
theorem pushdownReplay_derives {g : CfgGrammar} {rs : List CfgRule} {input : List String}
    {stk : List CfgSym} (h : PushdownReplay g rs input stk) :
    CfgDerives g stk (input.map .terminal) := by
  induction h with
  | done => exact .refl []
  | term t _ ih =>
    simp only [List.map_cons]
    exact CfgDerives.cons_sym (.terminal t) ih
  | @rule r _ _ stk hr _ ih =>
    exact .step (.head r stk hr) ih

/-- Refusal clauses for the $O(\text{tokens})$ pushdown CFG replay verifier. -/
inductive CfgRefusal where
  | unconsumedInput (remaining : List String)
  | unconsumedRules (remainingCount : Nat)
  | unexpectedEndOfInput (expected : String)
  | terminalMismatch (expected actual : String)
  | missingRuleFor (nt : String)
  | lhsMismatch (expected actual : String)
  | unknownRule (rule : CfgRule)
  | stepBudgetExhausted
  deriving DecidableEq, Repr

/-- Executable $O(|rs| + |input|)$ pushdown replay loop, structurally recursive on the exact
    step bound `steps = rs.length + input.length + 1`. -/
def replayCfgCompactAux (g : CfgGrammar) :
    Nat → List CfgRule → List String → List CfgSym → Except CfgRefusal Unit
  | 0, _, _, _ => .error .stepBudgetExhausted
  | steps + 1, rs, input, stk =>
    match stk with
    | [] =>
      match rs, input with
      | [], [] => .ok ()
      | [], x :: xs => .error (.unconsumedInput (x :: xs))
      | r :: restRules, _ => .error (.unconsumedRules (r :: restRules).length)
    | .terminal t :: restStk =>
      match input with
      | [] => .error (.unexpectedEndOfInput t)
      | x :: xs =>
        match decide (x = t) with
        | true => replayCfgCompactAux g steps rs xs restStk
        | false => .error (.terminalMismatch t x)
    | .nonterminal nt :: restStk =>
      match rs with
      | [] => .error (.missingRuleFor nt)
      | r :: restRules =>
        match decide (r.lhs = nt) with
        | false => .error (.lhsMismatch nt r.lhs)
        | true =>
          match decide (r ∈ g.rules) with
          | true => replayCfgCompactAux g steps restRules input (r.rhs ++ restStk)
          | false => .error (.unknownRule r)

/-- Replay a compact leftmost-derivation rule sequence `rs` against `input` from `[.nonterminal g.start]`
    using the exact $O(\text{tokens})$ step bound `rs.length + input.length + 1`. -/
def replayCfgCompact (g : CfgGrammar) (rs : List CfgRule) (input : List String) :
    Except CfgRefusal Unit :=
  replayCfgCompactAux g (rs.length + input.length + 1) rs input [.nonterminal g.start]

theorem replayCfgCompactAux_sound (g : CfgGrammar) :
    ∀ (steps : Nat) (rs : List CfgRule) (input : List String) (stk : List CfgSym),
      replayCfgCompactAux g steps rs input stk = .ok () →
      PushdownReplay g rs input stk
  | 0, _, _, _, h => by cases h
  | _ + 1, [], [], [], _ => .done
  | _ + 1, [], _ :: _, [], h => by cases h
  | _ + 1, _ :: _, _, [], h => by cases h
  | _ + 1, _, [], .terminal _ :: _, h => by cases h
  | steps + 1, rs, x :: xs, .terminal t :: stk, h => by
    dsimp only [replayCfgCompactAux] at h
    cases hEq : decide (x = t) <;> rw [hEq] at h
    · cases h
    · have hx : x = t := of_decide_eq_true hEq
      subst hx
      exact .term x (replayCfgCompactAux_sound g steps rs xs stk h)
  | _ + 1, [], _, .nonterminal _ :: _, h => by cases h
  | steps + 1, r :: restRules, input, .nonterminal nt :: stk, h => by
    dsimp only [replayCfgCompactAux] at h
    cases hLhs : decide (r.lhs = nt) <;> rw [hLhs] at h
    · cases h
    · cases hMem : decide (r ∈ g.rules) <;> rw [hMem] at h
      · cases h
      · have hLhs' : r.lhs = nt := of_decide_eq_true hLhs
        have hMem' : r ∈ g.rules := of_decide_eq_true hMem
        rw [← hLhs']
        exact .rule hMem' (replayCfgCompactAux_sound g steps restRules input (r.rhs ++ stk) h)

theorem replayCfgCompactAux_complete (g : CfgGrammar) {rs : List CfgRule} {input : List String}
    {stk : List CfgSym} (h : PushdownReplay g rs input stk) :
    ∀ (steps : Nat), rs.length + input.length < steps →
      replayCfgCompactAux g steps rs input stk = .ok () := by
  induction h with
  | done =>
    intro steps hlt
    cases steps with
    | zero => exact False.elim (Nat.not_lt_zero _ hlt)
    | succ k => rfl
  | @term t rs input stk _ ih =>
    intro steps hlt
    cases steps with
    | zero => exact False.elim (Nat.not_lt_zero _ hlt)
    | succ k =>
      dsimp only [replayCfgCompactAux]
      rw [decide_eq_true (rfl : t = t)]
      dsimp only [List.length] at hlt
      exact ih k (Nat.lt_of_succ_lt_succ hlt)
  | @rule r rs input stk hr _ ih =>
    intro steps hlt
    cases steps with
    | zero => exact False.elim (Nat.not_lt_zero _ hlt)
    | succ k =>
      dsimp only [replayCfgCompactAux]
      rw [decide_eq_true (rfl : r.lhs = r.lhs), decide_eq_true hr]
      dsimp only [List.length] at hlt
      rw [Nat.succ_add] at hlt
      exact ih k (Nat.lt_of_succ_lt_succ hlt)

/-- **Soundness of `replayCfgCompact`**: an accepted compact rule sequence `rs` witnesses both
    a valid `PushdownReplay` run and a multi-step CFG derivation `CfgDerives g [.nonterminal g.start] (input.map .terminal)`. -/
theorem replayCfgCompact_sound (g : CfgGrammar) (rs : List CfgRule) (input : List String)
    (h : replayCfgCompact g rs input = .ok ()) :
    PushdownReplay g rs input [.nonterminal g.start] ∧
    CfgDerives g [.nonterminal g.start] (input.map .terminal) := by
  have hReplay := replayCfgCompactAux_sound g (rs.length + input.length + 1) rs input [.nonterminal g.start] h
  exact ⟨hReplay, pushdownReplay_derives hReplay⟩

theorem replayCfgCompact_complete (g : CfgGrammar) {rs : List CfgRule} {input : List String}
    (h : PushdownReplay g rs input [.nonterminal g.start]) :
    replayCfgCompact g rs input = .ok () :=
  replayCfgCompactAux_complete g h (rs.length + input.length + 1) (Nat.lt_succ_self _)

theorem replayCfgCompact_iff_pushdownReplay (g : CfgGrammar) (rs : List CfgRule) (input : List String) :
    replayCfgCompact g rs input = .ok () ↔
    PushdownReplay g rs input [.nonterminal g.start] := by
  constructor
  · intro h
    exact (replayCfgCompact_sound g rs input h).1
  · exact replayCfgCompact_complete g

/-- Object for the `cfg-compact` judge: a grammar and the target token transcript. -/
structure CfgCompactQuery where
  grammar : CfgGrammar
  input : List String
  deriving DecidableEq, Repr

/-- Certificate for the `cfg-compact` judge: the leftmost-derivation rule sequence. -/
structure CfgCompactCert where
  rules : List CfgRule
  deriving DecidableEq, Repr

/-- Standalone verdict checker for `CfgCompactQuery` and `CfgCompactCert`. -/
def cfgCompactCheck (_ : Nat) (q : CfgCompactQuery) (c : CfgCompactCert) :
    Verdict CfgRefusal :=
  match replayCfgCompact q.grammar c.rules q.input with
  | .ok () => .ok
  | .error r => .refused r []

/-- Declarative semantic specification for `cfgCompactJudge`:
    both pushdown replay from `[.nonterminal q.grammar.start]` and multi-step CFG derivation
    `CfgDerives q.grammar [.nonterminal q.grammar.start] (q.input.map .terminal)` hold. -/
def CfgCompactMeaning (q : CfgCompactQuery) (c : CfgCompactCert) : Prop :=
  PushdownReplay q.grammar c.rules q.input [.nonterminal q.grammar.start] ∧
  CfgDerives q.grammar [.nonterminal q.grammar.start] (q.input.map .terminal)

/-- `Judge` instance for $O(\text{tokens})$ compact CFG replay. -/
instance cfgCompactJudge : Judge CfgCompactQuery CfgCompactCert where
  Clause := CfgRefusal
  Meaning := CfgCompactMeaning
  check := cfgCompactCheck
  sound := by
    intro _ q c h
    unfold cfgCompactCheck at h
    cases hVer : replayCfgCompact q.grammar c.rules q.input with
    | ok u =>
      cases u
      exact replayCfgCompact_sound q.grammar c.rules q.input hVer
    | error r => rw [hVer] at h; cases h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment (q : CfgCompactQuery) :=
    ∃ (c : CfgCompactCert), PushdownReplay q.grammar c.rules q.input [.nonterminal q.grammar.start]
  complete := by
    intro q ⟨c, hc⟩ _
    refine ⟨c, 0, ?_⟩
    unfold cfgCompactCheck
    rw [replayCfgCompact_complete q.grammar hc]
  mono := by intro _ _ _ _ _ _; rfl

/-- Reference structured API / JSON transcript grammar:
    - `rEnvelope`: `S → "{" "msg" ":" Val "}"`
    - `rArray`:    `Val → "[" Val "]"`
    - `rString`:   `Val → "\"ok\""` -/
def rEnvelope : CfgRule :=
  { lhs := "S"
  , rhs := [.terminal "{", .terminal "msg", .terminal ":", .nonterminal "Val", .terminal "}"] }

def rArray : CfgRule :=
  { lhs := "Val"
  , rhs := [.terminal "[", .nonterminal "Val", .terminal "]"] }

def rString : CfgRule :=
  { lhs := "Val"
  , rhs := [.terminal "\"ok\""] }

def transcriptCfg : CfgGrammar where
  start := "S"
  rules := [rEnvelope, rArray, rString]

def sampleCfgQuery : CfgCompactQuery where
  grammar := transcriptCfg
  input := ["{", "msg", ":", "[", "\"ok\"", "]", "}"]

def goodCfgCert : CfgCompactCert where
  rules := [rEnvelope, rArray, rString]

/-- Planted bad certificate for `cfgCompactFormat`: empty rule list on a non-empty transcript. -/
def badCfgCert : CfgCompactCert where
  rules := []

theorem goodCfgCert_accepted :
    cfgCompactCheck 1 sampleCfgQuery goodCfgCert = .ok :=
  rfl

theorem badCfgCert_refused :
    cfgCompactCheck 1 sampleCfgQuery badCfgCert =
      .refused (.missingRuleFor "S") [] :=
  rfl

/-- Encode `CfgSym` to `Lean.Json`. -/
def cfgSymToJson : CfgSym → Json
  | .terminal tok => Json.mkObj [("terminal", Json.str tok)]
  | .nonterminal nt => Json.mkObj [("nonterminal", Json.str nt)]

/-- Parse `CfgSym` from `Lean.Json`. -/
def cfgSymOfJson (j : Json) : Except String CfgSym := do
  match j.getObjValAs? String "terminal" with
  | .ok tok => pure (.terminal tok)
  | .error _ =>
    let nt ← j.getObjValAs? String "nonterminal"
    pure (.nonterminal nt)

/-- Encode `CfgRule` to `Lean.Json`. -/
def cfgRuleToJson (r : CfgRule) : Json :=
  Json.mkObj
    [ ("lhs", Json.str r.lhs)
    , ("rhs", Json.arr (r.rhs.map cfgSymToJson).toArray) ]

/-- Parse `CfgRule` from `Lean.Json`. -/
def cfgRuleOfJson (j : Json) : Except String CfgRule := do
  let lhs ← j.getObjValAs? String "lhs"
  let rhs ← (← (← j.getObjVal? "rhs").getArr?).toList.mapM cfgSymOfJson
  pure { lhs, rhs }

/-- Encode `CfgGrammar` to `Lean.Json`. -/
def cfgGrammarToJson (g : CfgGrammar) : Json :=
  Json.mkObj
    [ ("start", Json.str g.start)
    , ("rules", Json.arr (g.rules.map cfgRuleToJson).toArray) ]

/-- Parse `CfgGrammar` from `Lean.Json`. -/
def cfgGrammarOfJson (j : Json) : Except String CfgGrammar := do
  let start ← j.getObjValAs? String "start"
  let rules ← (← (← j.getObjVal? "rules").getArr?).toList.mapM cfgRuleOfJson
  pure { start, rules }

/-- Encode `CfgCompactQuery` as canonical JSON wire string. -/
def encodeCfgQuery (q : CfgCompactQuery) : String :=
  Json.compress <| Json.mkObj
    [ ("grammar", cfgGrammarToJson q.grammar)
    , ("input", Json.arr (q.input.map Json.str).toArray) ]

/-- Encode `CfgCompactCert` as canonical JSON wire string. -/
def encodeCfgCert (c : CfgCompactCert) : String :=
  Json.compress <| Json.mkObj
    [ ("rules", Json.arr (c.rules.map cfgRuleToJson).toArray) ]

/-- Parse `CfgCompactQuery` from JSON wire string. -/
def decodeCfgQuery (s : String) : Except String CfgCompactQuery := do
  let j ← Json.parse s
  let grammar ← cfgGrammarOfJson (← j.getObjVal? "grammar")
  let input ← (← (← j.getObjVal? "input").getArr?).toList.mapM (·.getStr?)
  pure { grammar, input }

/-- Parse `CfgCompactCert` from JSON wire string. -/
def decodeCfgCert (s : String) : Except String CfgCompactCert := do
  let j ← Json.parse s
  let rules ← (← (← j.getObjVal? "rules").getArr?).toList.mapM cfgRuleOfJson
  pure { rules }

/-- Registered `Obend.Judge.Format` for `cfg-compact` v`1`. -/
def cfgCompactFormat : Judge.Format where
  name := "cfg-compact"
  version := "1"
  Obj := CfgCompactQuery
  Cert := CfgCompactCert
  decodeObj := decodeCfgQuery
  decodeCert := decodeCfgCert
  trust := .kernel
  regime := .decidable
  bad := (sampleCfgQuery, badCfgCert)
  badGrade := 1
  bad_refused := ⟨_, _, badCfgCert_refused⟩


/-! ## Pillar C: Structured Prompt & Transcript Slot Confinement -/

/-- A segment of a semi-unstructured prompt/API template:
    - `Seg.lit tokens`: trusted literal tokens (which may legitimately carry system delimiters `"{{"`),
    - `Seg.slot name`: an untrusted `Core4` / `Slot.Protocol` / `Leaf.Book` hole filled at runtime. -/
inductive Seg where
  | lit (tokens : List String)
  | slot (name : String)
  deriving DecidableEq, Repr

/-- A semi-unstructured prompt template is a list of literal and slot segments. -/
abbrev PromptTemplate := List Seg

/-- Render a prompt template `T` by substituting each `Seg.slot name` with `b name`. -/
def renderPrompt (b : String → List String) : PromptTemplate → List String
  | [] => []
  | .lit ts :: rest => ts ++ renderPrompt b rest
  | .slot name :: rest => b name ++ renderPrompt b rest

/-- Extract only the trusted literal tokens of `T` (dropping all slots). -/
def litOnly : PromptTemplate → List String
  | [] => []
  | .lit ts :: rest => ts ++ litOnly rest
  | .slot _ :: rest => litOnly rest

/-- Every slot occurring in template `T` is bound to an `InjectionFree` token sequence. -/
def AllSlotsClean (b : String → List String) (T : PromptTemplate) : Prop :=
  ∀ name, Seg.slot name ∈ T → InjectionFree (b name)

/-- Executable Boolean decider for `AllSlotsClean`. -/
def allSlotsCleanB (b : String → List String) (T : PromptTemplate) : Bool :=
  T.all fun
    | .lit _ => true
    | .slot name => dfaAccepts confinementDfa (b name)

theorem allSlotsCleanB_iff (b : String → List String) (T : PromptTemplate) :
    allSlotsCleanB b T = true ↔ AllSlotsClean b T := by
  unfold allSlotsCleanB AllSlotsClean
  rw [List.all_eq_true]
  constructor
  · intro h name hmem
    exact (injectionFree_iff_dfaAccepts (b name)).mpr (h (.slot name) hmem)
  · intro h seg hmem
    cases seg with
    | lit _ => rfl
    | slot name => exact (injectionFree_iff_dfaAccepts (b name)).mp (h name hmem)

/-- **Slot Confinement Theorem (`slot_confinement`)**:
    When every untrusted slot filling in `T` passes the `InjectionFree` complement DFA guard
    (`AllSlotsClean b T`), the control-token stream of the rendered prompt equals the
    control-token stream of the trusted template literals alone:
    `controlTokens (renderPrompt b T) = controlTokens (litOnly T)`.
    Untrusted slot fillings contribute zero control tokens and cannot inject or alter delimiters. -/
theorem slot_confinement (b : String → List String) (T : PromptTemplate)
    (hClean : AllSlotsClean b T) :
    controlTokens (renderPrompt b T) = controlTokens (litOnly T) := by
  induction T with
  | nil => rfl
  | cons seg rest ih =>
    have hRestClean : AllSlotsClean b rest :=
      fun name hmem => hClean name (List.mem_cons_of_mem seg hmem)
    have hRec := ih hRestClean
    cases seg with
    | lit ts =>
      simp only [renderPrompt, litOnly, controlTokens_append]
      rw [hRec]
    | slot name =>
      have hSlotFree : InjectionFree (b name) := hClean name List.mem_cons_self
      have hSlotNil : controlTokens (b name) = [] :=
        (injectionFree_iff_controlTokens_nil (b name)).mp hSlotFree
      simp only [renderPrompt, litOnly, controlTokens_append]
      rw [hSlotNil, List.nil_append, hRec]

/-- Counting corollary of `slot_confinement`: clean slots cannot alter the control-token count. -/
theorem slot_confinement_count (b : String → List String) (T : PromptTemplate)
    (hClean : AllSlotsClean b T) :
    (controlTokens (renderPrompt b T)).length = (controlTokens (litOnly T)).length := by
  rw [slot_confinement b T hClean]

/-- Reference system prompt template containing trusted `"{{"` / `"}}"` system delimiters and a `"user"` slot. -/
def systemPromptTemplate : PromptTemplate :=
  [ .lit ["{{", "system: obey safety policy", "}}"]
  , .slot "user"
  , .lit ["{{", "end_turn", "}}"] ]

/-- Benign user slot binding containing no control tokens. -/
def benignUserBinding : String → List String :=
  fun _ => ["summarize", "the", "quarterly", "report"]

/-- Malicious user slot binding smuggling `"{{ "` and `"<|system|>"` control tokens. -/
def injectedUserBinding : String → List String :=
  fun _ => ["ignore", "{{", "<|system|>", "}}"]

theorem benign_slot_is_clean :
    AllSlotsClean benignUserBinding systemPromptTemplate := by
  rw [← allSlotsCleanB_iff]
  rfl

theorem benign_slot_preserves_control_tokens :
    controlTokens (renderPrompt benignUserBinding systemPromptTemplate) =
      controlTokens (litOnly systemPromptTemplate) :=
  slot_confinement benignUserBinding systemPromptTemplate benign_slot_is_clean

theorem benign_slot_control_tokens_eq :
    controlTokens (renderPrompt benignUserBinding systemPromptTemplate) =
      ["{{", "}}", "{{", "}}"] :=
  rfl

/-- **Refutation Tooth (`injected_slot_breaks_confinement`)**:
    An unguarded slot filling containing `"{{ "` is rejected by `AllSlotsClean` and strictly
    alters the rendered control-token stream (`controlTokens (renderPrompt ...) ≠ controlTokens (litOnly ...)`),
    proving the `InjectionFree` DFA guard is load-bearing. -/
theorem injected_slot_breaks_confinement :
    ¬ AllSlotsClean injectedUserBinding systemPromptTemplate ∧
    controlTokens (renderPrompt injectedUserBinding systemPromptTemplate) ≠
      controlTokens (litOnly systemPromptTemplate) := by
  refine ⟨?_, ?_⟩
  · intro hClean
    have hB : allSlotsCleanB injectedUserBinding systemPromptTemplate = true :=
      (allSlotsCleanB_iff injectedUserBinding systemPromptTemplate).mpr hClean
    revert hB
    decide
  · decide

/-! ### Bridges to `Obend.Slot.Protocol`, `Obend.Leaf.Book`, and `Obend.Core.Term` -/

/-- Operations of an `Obend.Slot.Protocol` prompt transcript protocol:
    - `emitLit tokens`: emit a trusted literal token segment,
    - `emitSlot name`: emit an untrusted named slot segment. -/
inductive PromptOp : Unit → Type where
  | emitLit (tokens : List String) : PromptOp ()
  | emitSlot (name : String) : PromptOp ()

/-- Indexed signature (`Obend.Slot.Protocol.Sig`) for open prompt protocols. -/
def promptSig : Sig Unit where
  Op := PromptOp
  Resp := fun _ => Unit
  next := fun _ () => ()

abbrev PromptHole : Unit → Type := fun _ => String
abbrev PromptRes : Unit → Type := fun _ => List String
abbrev PromptProt := Prot promptSig PromptHole PromptRes

/-- Convert an association-list slot binding into a slot token lookup (`bindingToSlotTokens`). -/
def bindingToSlotTokens (entries : List (String × List String)) (name : String) : List String :=
  (entries.lookup name).getD []

/-- `Obend.Slot.Protocol.Algebra` interpreting a `PromptProt` into a `PromptTemplate`. -/
def promptTemplateAlg : Algebra promptSig PromptHole PromptRes (fun _ => PromptTemplate) where
  ret := fun ts => if ts.isEmpty then [] else [.lit ts]
  call := fun op k =>
    match op with
    | .emitLit ts => .lit ts :: k ()
    | .emitSlot name => .slot name :: k ()
  hole := fun name => [.slot name]

/-- Lower an open `Obend.Slot.Protocol.Prot` (`PromptProt i`) into a `PromptTemplate` via `Slot.Protocol.fold`. -/
def protToPromptTemplate {i : Unit} (P : PromptProt i) : PromptTemplate :=
  fold promptTemplateAlg P

/-- Lift a `PromptTemplate` into an open `Obend.Slot.Protocol.Prot` (`PromptProt ()`). -/
def promptTemplateToProt : PromptTemplate → PromptProt ()
  | [] => .ret []
  | .lit ts :: rest => .call (.emitLit ts) (fun () => promptTemplateToProt rest)
  | .slot name :: rest => .call (.emitSlot name) (fun () => promptTemplateToProt rest)

theorem protToPromptTemplate_roundtrip (T : PromptTemplate) :
    protToPromptTemplate (promptTemplateToProt T) = T := by
  induction T with
  | nil => rfl
  | cons seg rest ih =>
    cases seg with
    | lit ts =>
      change Seg.lit ts :: protToPromptTemplate (promptTemplateToProt rest) = Seg.lit ts :: rest
      rw [ih]
    | slot name =>
      change Seg.slot name :: protToPromptTemplate (promptTemplateToProt rest) = Seg.slot name :: rest
      rw [ih]

/-- Lift a slot token binding `b` to an `Obend.Slot.Protocol.Subst` filling open `.hole name` nodes. -/
def slotBindingToSubst (b : String → List String) : Subst promptSig PromptHole PromptRes :=
  fun () name => some (.ret (b name))

/-- **Slot Protocol Confinement (`slot_protocol_confinement`)**:
    Any open `Obend.Slot.Protocol` prompt protocol `P` whose holes pass `AllSlotsClean`
    preserves the exact control-token stream of its trusted literal operations. -/
theorem slot_protocol_confinement (P : PromptProt ()) (b : String → List String)
    (hClean : AllSlotsClean b (protToPromptTemplate P)) :
    controlTokens (renderPrompt b (protToPromptTemplate P)) =
      controlTokens (litOnly (protToPromptTemplate P)) :=
  slot_confinement b (protToPromptTemplate P) hClean

/-- Project an `Obend.Leaf.Book` (`Obend.Leaf.Emit`) into a `PromptTemplate`:
    - static brand entries (`BookItem.static`) become trusted literal header segments,
    - dynamic slot definitions (`BookItem.slot`) become named slot holes. -/
def bookItemToSeg : BookItem → Seg
  | .static member _ => .lit ["{{", member, "}}"]
  | .slot d => .slot d.member

def bookToPromptTemplate (B : Book) : PromptTemplate :=
  B.items.map bookItemToSeg

/-- **Leaf Book Slot Confinement**: any `Obend.Leaf.Book` whose dynamic slot fillings pass
    `AllSlotsClean` preserves the exact control-token framing of its static brand entries. -/
theorem leaf_book_slot_confinement (B : Book) (b : String → List String)
    (hClean : AllSlotsClean b (bookToPromptTemplate B)) :
    controlTokens (renderPrompt b (bookToPromptTemplate B)) =
      controlTokens (litOnly (bookToPromptTemplate B)) :=
  slot_confinement b (bookToPromptTemplate B) hClean

/-- Constructive, collision-free slot name `"hole_<n>"` for `Obend.Core.Term.hole n σ`. -/
def holeSlotName (n : Nat) : String :=
  "hole_" ++ natToDecString n

/-- Extract a slot binding from an association list of hole indices `(n, tokens)`. -/
def termSlotBinding (holes : List (Nat × List String)) (name : String) : List String :=
  match holes.find? (fun p => holeSlotName p.1 == name) with
  | some (_, ts) => ts
  | none => []

/-- Project an `Obend.Core.Term` into a `PromptTemplate` where `Term.label s` is a literal segment
    and `Term.hole n _` is an untrusted slot `holeSlotName n`. -/
def termToPromptTemplate : Term → PromptTemplate
  | .label s => [.lit [s]]
  | .hole n _ => [.slot (holeSlotName n)]
  | .app f a => termToPromptTemplate f ++ termToPromptTemplate a
  | .lam body => termToPromptTemplate body
  | .inject tag payload => .lit [tag] :: termToPromptTemplate payload
  | .perform plan => termToPromptTemplate plan
  | .done value => termToPromptTemplate value
  | _ => []

theorem term_slot_confinement (t : Term) (b : String → List String)
    (hClean : AllSlotsClean b (termToPromptTemplate t)) :
    controlTokens (renderPrompt b (termToPromptTemplate t)) =
      controlTokens (litOnly (termToPromptTemplate t)) :=
  slot_confinement b (termToPromptTemplate t) hClean


/-! ## Pillar D: `dclutch` Liquidation-Cascade-Free Hoard Complete-Set & Joint KKT Clearing Judge -/

/-- `dclutch` fully-collateralized Hoard market state (`DClutch.Economic.State`):
    `outcomes` is the number of mutually exclusive categorical outcomes, `hoard` is the locked
    collateral backing in the Hoard, and `supply` is the outstanding claim supply per outcome. -/
structure HoardMarketState where
  outcomes : Nat
  hoard : Nat
  supply : List Nat
  deriving DecidableEq, Repr

/-- Outstanding supply of outcome `i` (0 if out of bounds). -/
def HoardMarketState.supplyAt (s : HoardMarketState) (i : Nat) : Nat :=
  s.supply[i]?.getD 0

/-- **The `dclutch` Hoard Complete-Set Full-Backing Invariant**:
    Every outcome `i < s.outcomes` is 100% collateralized by `s.hoard` (`s.supplyAt i ≤ s.hoard`),
    so no price path can ever cause under-collateralization or trigger a liquidation cascade. -/
def HoardCollateralInvariant (s : HoardMarketState) : Prop :=
  s.supply.length = s.outcomes ∧ ∀ i < s.outcomes, s.supplyAt i ≤ s.hoard

/-- Alias `HoardCompleteSetInvariant` for `HoardCollateralInvariant`. -/
abbrev HoardCompleteSetInvariant (s : HoardMarketState) : Prop :=
  HoardCollateralInvariant s

/-- Executable Boolean checker for `HoardCollateralInvariant`. -/
def hoardCollateralValid (s : HoardMarketState) : Bool :=
  (s.supply.length == s.outcomes) &&
  (List.range s.outcomes).all (fun i => decide (s.supplyAt i ≤ s.hoard))

theorem hoardCollateralValid_iff (s : HoardMarketState) :
    hoardCollateralValid s = true ↔ HoardCollateralInvariant s := by
  unfold hoardCollateralValid HoardCollateralInvariant
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-- Split `qty` complete sets: locks `qty` collateral into `hoard` and mints `qty` claims on every outcome. -/
def splitCompleteSet (s : HoardMarketState) (qty : Nat) : HoardMarketState where
  outcomes := s.outcomes
  hoard := s.hoard + qty
  supply := s.supply.map (fun v => v + qty)

/-- Merge `qty` complete sets: burns `qty` claims on every outcome and releases `qty` collateral from `hoard`. -/
def mergeCompleteSet (s : HoardMarketState) (qty : Nat) : HoardMarketState where
  outcomes := s.outcomes
  hoard := s.hoard - qty
  supply := s.supply.map (fun v => v - qty)

/-- Check whether `qty` complete sets are available to merge without truncation. -/
def canMergeCompleteSet (s : HoardMarketState) (qty : Nat) : Bool :=
  decide (qty ≤ s.hoard) && s.supply.all (fun v => decide (qty ≤ v))

private theorem list_map_add_sub_cancel (xs : List Nat) (qty : Nat) :
    (xs.map (fun v => v + qty)).map (fun v => v - qty) = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, Nat.add_sub_cancel, ih]

private theorem list_map_sub_add_cancel (xs : List Nat) (qty : Nat)
    (hAll : xs.all (fun v => decide (qty ≤ v)) = true) :
    (xs.map (fun v => v - qty)).map (fun v => v + qty) = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hAll
    simp only [List.map_cons, Nat.sub_add_cancel hAll.1, ih hAll.2]

/-- **Exact Split-then-Merge Conservation**: splitting `qty` complete sets and then merging `qty`
    complete sets recovers the exact original `HoardMarketState`. -/
theorem mergeCompleteSet_splitCompleteSet_cancel (s : HoardMarketState) (qty : Nat) :
    mergeCompleteSet (splitCompleteSet s qty) qty = s := by
  cases s with
  | mk outcomes hoard supply =>
    simp only [splitCompleteSet, mergeCompleteSet, Nat.add_sub_cancel, list_map_add_sub_cancel]

/-- **Exact Merge-then-Split Conservation**: when `canMergeCompleteSet s qty = true`, merging `qty`
    complete sets and then splitting `qty` complete sets recovers the exact original `HoardMarketState`. -/
theorem splitCompleteSet_mergeCompleteSet_cancel (s : HoardMarketState) (qty : Nat)
    (hCan : canMergeCompleteSet s qty = true) :
    splitCompleteSet (mergeCompleteSet s qty) qty = s := by
  unfold canMergeCompleteSet at hCan
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hCan
  cases s with
  | mk outcomes hoard supply =>
    simp only [mergeCompleteSet, splitCompleteSet, Nat.sub_add_cancel hCan.1,
      list_map_sub_add_cancel supply qty hCan.2]

theorem supplyAt_map (xs : List Nat) (f : Nat → Nat) (i : Nat) (hi : i < xs.length) :
    (xs.map f)[i]?.getD 0 = f (xs[i]?.getD 0) := by
  simp [hi]

/-- **`splitCompleteSet` preserves the Hoard full-backing invariant (`∀ i < outcomes, supply i ≤ hoard`).** -/
theorem splitCompleteSet_preserves_invariant (s : HoardMarketState) (qty : Nat)
    (hInv : HoardCollateralInvariant s) :
    HoardCollateralInvariant (splitCompleteSet s qty) := by
  obtain ⟨hLen, hBound⟩ := hInv
  refine ⟨by simp [splitCompleteSet, hLen], ?_⟩
  intro i hi
  change i < s.outcomes at hi
  have hiLen : i < s.supply.length := by omega
  have hMap := supplyAt_map s.supply (fun v => v + qty) i hiLen
  unfold HoardMarketState.supplyAt splitCompleteSet at *
  dsimp only
  rw [hMap]
  have hPrev := hBound i hi
  omega

/-- **`mergeCompleteSet` preserves the Hoard full-backing invariant (`∀ i < outcomes, supply i ≤ hoard`).** -/
theorem mergeCompleteSet_preserves_invariant (s : HoardMarketState) (qty : Nat)
    (hInv : HoardCollateralInvariant s) :
    HoardCollateralInvariant (mergeCompleteSet s qty) := by
  obtain ⟨hLen, hBound⟩ := hInv
  refine ⟨by simp [mergeCompleteSet, hLen], ?_⟩
  intro i hi
  change i < s.outcomes at hi
  have hiLen : i < s.supply.length := by omega
  have hMap := supplyAt_map s.supply (fun v => v - qty) i hiLen
  unfold HoardMarketState.supplyAt mergeCompleteSet at *
  dsimp only
  rw [hMap]
  have hPrev := hBound i hi
  omega

/-- Apply a signed complete-set delta `sets : Int` (`sets ≥ 0` splits, `sets < 0` merges). -/
def applyCompleteSetDelta (s : HoardMarketState) (sets : Int) : HoardMarketState :=
  match decide (0 ≤ sets) with
  | true => splitCompleteSet s sets.toNat
  | false => mergeCompleteSet s (-sets).toNat

/-- **Liquidation-Cascade-Free Theorem**: any signed complete-set delta preserves the Hoard
    full-backing invariant, so every outcome remains 100% backed by `hoard` under all price movements. -/
theorem applyCompleteSetDelta_preserves_invariant (s : HoardMarketState) (sets : Int)
    (hInv : HoardCollateralInvariant s) :
    HoardCollateralInvariant (applyCompleteSetDelta s sets) := by
  unfold applyCompleteSetDelta
  cases decide (0 ≤ sets)
  · exact mergeCompleteSet_preserves_invariant s (-sets).toNat hInv
  · exact splitCompleteSet_preserves_invariant s sets.toNat hInv

/-! ### $N$-Outcome Simplex KKT Joint Clearing (`DClutch.JointClearing`) -/

/-- Head-first finite sum `f 0 + f 1 + … + f (n - 1)` over outcome indices `0 .. n-1`. -/
def sumOutcomes : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => f 0 + sumOutcomes n (fun i => f (i + 1))

theorem sumOutcomes_congr {n : Nat} {f g : Nat → Int}
    (h : ∀ i, i < n → f i = g i) : sumOutcomes n f = sumOutcomes n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [sumOutcomes]
    rw [h 0 (by omega), ih (fun i hi => h (i + 1) (by omega))]

theorem sumOutcomes_add (n : Nat) (f g : Nat → Int) :
    sumOutcomes n (fun i => f i + g i) = sumOutcomes n f + sumOutcomes n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [sumOutcomes]
    rw [ih]
    omega

theorem sumOutcomes_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumOutcomes n (fun i => c * f i) = c * sumOutcomes n f := by
  induction n generalizing f with
  | zero => simp [sumOutcomes]
  | succ n ih =>
    simp only [sumOutcomes]
    rw [ih, Int.mul_add]

theorem sumOutcomes_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumOutcomes n (fun i => f i * c) = sumOutcomes n f * c := by
  rw [Int.mul_comm, ← sumOutcomes_mul_left]
  exact sumOutcomes_congr (fun i _ => Int.mul_comm _ _)

theorem sumOutcomes_zero (n : Nat) : sumOutcomes n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumOutcomes, ih]

theorem sumOutcomes_le {n : Nat} {f g : Nat → Int}
    (h : ∀ i, i < n → f i ≤ g i) : sumOutcomes n f ≤ sumOutcomes n g := by
  induction n generalizing f g with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    simp only [sumOutcomes]
    have h0 := h 0 (by omega)
    have hrest := ih (fun i hi => h (i + 1) (by omega))
    omega

def natAtZ (values : List Nat) (i : Nat) : Int :=
  (values[i]?.getD 0 : Int)

theorem sumOutcomes_natAtZ (values : List Nat) :
    sumOutcomes values.length (natAtZ values) = (values.sum : Int) := by
  induction values with
  | nil => rfl
  | cons h t ih =>
    simp only [sumOutcomes, List.sum_cons, List.length_cons]
    have h0 : natAtZ (h :: t) 0 = (h : Int) := by simp [natAtZ]
    rw [h0]
    rw [sumOutcomes_congr (f := fun i => natAtZ (h :: t) (i + 1)) (g := natAtZ t)
      (fun i _ => by simp [natAtZ])]
    rw [ih]
    omega

/-- An order in the $N$-outcome joint clearing batch (`DClutch.JointClearing.Order`). -/
structure JointOrder where
  orderId : Nat
  receivePerLot : List Nat
  deliverPerLot : List Nat
  quantity : Nat
  limit : Int
  deriving DecidableEq, Repr

/-- A fill row pairing an order with its filled lot quantity (`DClutch.JointClearing.Fill`). -/
structure JointFill where
  order : JointOrder
  lots : Nat
  deriving DecidableEq, Repr

/-- The $N$-outcome simplex KKT joint clearing certificate (`JointClearingCert`). -/
structure JointClearingCert where
  outcomeCount : Nat
  scale : Nat
  prices : List Nat
  fills : List JointFill
  sets : Int
  deriving DecidableEq, Repr

/-- Price of outcome `i` under certificate `c`. -/
def JointClearingCert.price (c : JointClearingCert) (i : Nat) : Int :=
  natAtZ c.prices i

/-- Signed per-lot claim flow of `o` on outcome `i`. -/
def JointOrder.flow (o : JointOrder) (i : Nat) : Int :=
  natAtZ o.receivePerLot i - natAtZ o.deliverPerLot i

/-- Net quote debit per lot of order `o` at the clearing prices of `c`. -/
def JointOrder.perLotDebit (c : JointClearingCert) (o : JointOrder) : Int :=
  sumOutcomes c.outcomeCount (fun i => c.price i * o.flow i)

/-- Claim flow contribution of fill `f` on outcome `i`. -/
def JointFill.contribution (f : JointFill) (i : Nat) : Int :=
  f.order.flow i * (f.lots : Int)

/-- Net claims demanded by `fills` on outcome `i`. -/
def netFlowAt (fills : List JointFill) (i : Nat) : Int :=
  (fills.map fun f => f.contribution i).sum

/-- Net claims demanded by `c.fills` on outcome `i`. -/
def JointClearingCert.net (c : JointClearingCert) (i : Nat) : Int :=
  netFlowAt c.fills i

/-- Residual claims left with the batch on outcome `i` after minting/merging `c.sets`. -/
def JointClearingCert.residual (c : JointClearingCert) (i : Nat) : Int :=
  c.sets - c.net i

/-- Net quote collected by the batch across `fills` in scale units. -/
def collectedQuote (c : JointClearingCert) (fills : List JointFill) : Int :=
  (fills.map fun f => f.order.perLotDebit c * (f.lots : Int)).sum

/-- Structural well-formedness of an order for `outcomeCount` outcomes. -/
def JointOrder.validFor (o : JointOrder) (outcomeCount : Nat) : Bool :=
  o.orderId != 0 &&
  o.receivePerLot.length == outcomeCount &&
  o.deliverPerLot.length == outcomeCount &&
  decide (0 < o.quantity)

/-- Per-row KKT admissibility of a fill `f` under clearing `c`:
    1. `f.order` is valid for `c.outcomeCount`,
    2. `f.lots ≤ f.order.quantity`,
    3. `f.lots == 0 || f.order.perLotDebit c ≤ f.order.limit` (`filled_at_or_better`),
    4. `f.lots == f.order.quantity || f.order.limit ≤ f.order.perLotDebit c` (`partial_fill_is_marginal`). -/
def jointFillAdmissible (c : JointClearingCert) (f : JointFill) : Bool :=
  f.order.validFor c.outcomeCount &&
  decide (f.lots ≤ f.order.quantity) &&
  (f.lots == 0 || decide (f.order.perLotDebit c ≤ f.order.limit)) &&
  (f.lots == f.order.quantity || decide (f.order.limit ≤ f.order.perLotDebit c))

/-- Full KKT simplex clearing predicate (`DClutch.JointClearing.Clearing.valid`). -/
def jointClearingValid (c : JointClearingCert) : Bool :=
  decide (0 < c.outcomeCount) &&
  decide (0 < c.scale) &&
  (c.prices.length == c.outcomeCount) &&
  (c.prices.sum == c.scale) &&
  c.fills.all (jointFillAdmissible c) &&
  decide (c.fills.map fun f => f.order.orderId).Nodup &&
  (List.range c.outcomeCount).all fun i =>
    decide (c.net i ≤ c.sets) && (decide (c.price i = 0) || decide (c.net i = c.sets))

/-- Unpacked proposition of a valid `JointClearingCert`. -/
structure JointCertified (c : JointClearingCert) : Prop where
  outcomes : 0 < c.outcomeCount
  scale : 0 < c.scale
  width : c.prices.length = c.outcomeCount
  simplex : c.prices.sum = c.scale
  rows : ∀ f ∈ c.fills, jointFillAdmissible c f = true
  distinct : (c.fills.map fun f => f.order.orderId).Nodup
  covered : ∀ i, i < c.outcomeCount → c.net i ≤ c.sets
  slack : ∀ i, i < c.outcomeCount → c.price i = 0 ∨ c.net i = c.sets

theorem jointCertified_of_valid (c : JointClearingCert) (h : jointClearingValid c = true) :
    JointCertified c := by
  simp only [jointClearingValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hn, hs⟩, hw⟩, hsum⟩, hrows⟩, hids⟩, hrange⟩ := h
  refine ⟨hn, hs, hw, hsum, List.all_eq_true.mp hrows, hids, ?_, ?_⟩
  · intro i hi
    have := List.all_eq_true.mp hrange i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · intro i hi
    have := List.all_eq_true.mp hrange i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.2

/-- **(1) Simplex Price Normalization**: `c.prices.sum = c.scale`. -/
theorem prices_sum_to_scale (c : JointClearingCert) (h : jointClearingValid c = true) :
    c.prices.sum = c.scale :=
  (jointCertified_of_valid c h).simplex

theorem prices_total (c : JointClearingCert) (h : jointClearingValid c = true) :
    sumOutcomes c.outcomeCount c.price = (c.scale : Int) := by
  have cert := jointCertified_of_valid c h
  unfold JointClearingCert.price
  rw [← cert.width, sumOutcomes_natAtZ, cert.simplex]

/-- **(2) Individual Rationality (`filled_at_or_better`)**: every positive fill executes at or better
    than its signed limit price. -/
theorem filled_at_or_better (c : JointClearingCert) (h : jointClearingValid c = true)
    (f : JointFill) (mem : f ∈ c.fills) (positive : 0 < f.lots) :
    f.order.perLotDebit c ≤ f.order.limit := by
  have hf := (jointCertified_of_valid c h).rows f mem
  simp only [jointFillAdmissible, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  rcases hf.1.2 with hz | hle
  · omega
  · exact hle

/-- **(3) No Interior Rationing (`partial_fill_is_marginal`)**: any order not filled in full must be
    marginal or out-of-the-money (`f.order.limit ≤ f.order.perLotDebit c`). -/
theorem partial_fill_is_marginal (c : JointClearingCert) (h : jointClearingValid c = true)
    (f : JointFill) (mem : f ∈ c.fills) (partialFill : f.lots < f.order.quantity) :
    f.order.limit ≤ f.order.perLotDebit c := by
  have hf := (jointCertified_of_valid c h).rows f mem
  simp only [jointFillAdmissible, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  rcases hf.2 with hq | hle
  · omega
  · exact hle

/-- **(4) KKT Complementary Slackness Surplus Optimality (`fill_kkt_surplus_optimal`)**:
    Every fill `f ∈ c.fills` maximizes trader limit-surplus `(f.order.limit - f.order.perLotDebit c) * lots`
    over all feasible fill quantities `0 ≤ lots' ≤ f.order.quantity`. -/
theorem fill_kkt_surplus_optimal (c : JointClearingCert) (h : jointClearingValid c = true)
    (f : JointFill) (mem : f ∈ c.fills) (lots' : Nat) (hCap : lots' ≤ f.order.quantity) :
    (f.order.limit - f.order.perLotDebit c) * (lots' : Int) ≤
      (f.order.limit - f.order.perLotDebit c) * (f.lots : Int) := by
  have hf := (jointCertified_of_valid c h).rows f mem
  simp only [jointFillAdmissible, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨_, hlotCap⟩, hrat⟩, hmarg⟩ := hf
  rcases hrat with hz | hbetter
  · rcases hmarg with hfull | hout
    · have hlots0 : lots' = 0 := by omega
      rw [hz, hlots0]
      exact Int.le_refl _
    · rw [hz]
      have hnonpos : f.order.limit - f.order.perLotDebit c ≤ 0 := by omega
      have hnonneg : (0 : Int) ≤ (lots' : Int) := by omega
      have hmul : (f.order.limit - f.order.perLotDebit c) * (lots' : Int) ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg hnonpos hnonneg
      exact Int.le_trans hmul (by simp only [Int.ofNat_zero, Int.mul_zero, Int.le_refl])
  · rcases hmarg with hfull | hout
    · rw [hfull]
      have hnonneg : 0 ≤ f.order.limit - f.order.perLotDebit c := by omega
      have hdiff : 0 ≤ (f.order.quantity : Int) - (lots' : Int) := by omega
      have hmul : 0 ≤ (f.order.limit - f.order.perLotDebit c) * ((f.order.quantity : Int) - (lots' : Int)) :=
        Int.mul_nonneg hnonneg hdiff
      rw [Int.mul_sub] at hmul
      omega
    · have heq : f.order.limit - f.order.perLotDebit c = 0 := by omega
      rw [heq]
      simp only [Int.zero_mul, Int.le_refl]

theorem fill_quote_expands (c : JointClearingCert) (f : JointFill) :
    f.order.perLotDebit c * (f.lots : Int) =
      sumOutcomes c.outcomeCount (fun i => c.price i * f.contribution i) := by
  unfold JointOrder.perLotDebit JointFill.contribution
  rw [← sumOutcomes_mul_right]
  exact sumOutcomes_congr (fun i _ => Int.mul_assoc _ _ _)

theorem collectedQuote_exchange (c : JointClearingCert) (fills : List JointFill) :
    collectedQuote c fills =
      sumOutcomes c.outcomeCount (fun i => c.price i * netFlowAt fills i) := by
  induction fills with
  | nil =>
    simp only [collectedQuote, List.map_nil, List.sum_nil, netFlowAt, Int.mul_zero]
    exact (sumOutcomes_zero c.outcomeCount).symm
  | cons f rest ih =>
    simp only [collectedQuote, List.map_cons, List.sum_cons, netFlowAt] at ih ⊢
    rw [ih]
    rw [sumOutcomes_congr (f := fun i => c.price i * (f.contribution i + (rest.map fun g => g.contribution i).sum))
      (g := fun i => c.price i * f.contribution i + c.price i * (rest.map fun g => g.contribution i).sum)
      (fun i _ => Int.mul_add _ _ _)]
    rw [sumOutcomes_add, fill_quote_expands]

/-- **(5) Exact Quote Backing (`collectedQuote_funds_sets`)**:
    Under a valid KKT simplex clearing certificate, `collectedQuote c c.fills = (c.scale : Int) * c.sets`
    (the collected quote from buyers/sellers exactly funds the complete sets minted/merged in the Hoard). -/
theorem collectedQuote_funds_sets (c : JointClearingCert) (h : jointClearingValid c = true) :
    collectedQuote c c.fills = (c.scale : Int) * c.sets := by
  rw [collectedQuote_exchange]
  have cert := jointCertified_of_valid c h
  have pointwise : ∀ i, i < c.outcomeCount → c.price i * c.net i = c.sets * c.price i := by
    intro i hi
    rcases cert.slack i hi with hp | hn
    · rw [hp]; simp
    · rw [hn, Int.mul_comm]
  unfold JointClearingCert.net at pointwise
  rw [sumOutcomes_congr pointwise, sumOutcomes_mul_left, prices_total c h, Int.mul_comm]

/-! ### Bridge to `Obend.Judge.Clearing` (`Order`, `Side`, `Order.crosses`) -/

/-- Lift a single-asset `Obend.Judge.Clearing.Order` (`side = .bid` or `.ask`) into a 2-outcome
    `JointOrder` on outcome `0` (with unit-lot bundle size `o.qty`). -/
def clearingOrderToJointOrder (id : Nat) (o : Order) : JointOrder :=
  match o.side with
  | .bid =>
    { orderId := id
      receivePerLot := [o.qty, 0]
      deliverPerLot := [0, 0]
      quantity := 1
      limit := (o.total : Int) }
  | .ask =>
    { orderId := id
      receivePerLot := [0, 0]
      deliverPerLot := [o.qty, 0]
      quantity := 1
      limit := -(o.total : Int) }

/-- Bridge theorem connecting `Obend.Judge.Clearing.Order.crosses` to `JointOrder.perLotDebit ≤ limit`:
    in a 2-outcome market with outcome-0 price `p0`, `o.crosses p0 = true` iff the lifted
    `JointOrder`'s per-lot debit at `[p0, p1]` is at or below `limit`. -/
theorem clearingOrder_crosses_iff_debit_le_limit (id p0 p1 : Nat) (o : Order) :
    o.crosses p0 = true ↔
      (clearingOrderToJointOrder id o).perLotDebit
        { outcomeCount := 2, scale := p0 + p1, prices := [p0, p1], fills := [], sets := 0 } ≤
      (clearingOrderToJointOrder id o).limit := by
  cases hSide : o.side <;>
    simp only [Order.crosses, clearingOrderToJointOrder, hSide, JointOrder.perLotDebit,
      sumOutcomes, JointClearingCert.price, JointOrder.flow, natAtZ,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Int.ofNat_zero, Int.sub_zero, Int.zero_sub, Int.mul_neg, Int.mul_zero,
      Int.add_zero, decide_eq_true_eq] <;>
    constructor <;> intro h <;> omega

/-- Refusal clauses for the combined `dclutch` Hoard & Joint KKT Clearing judge. -/
inductive DclutchHoardRefusal where
  | hoardInvariantViolated
  | outcomeCountMismatch (marketOutcomes certOutcomes : Nat)
  | insufficientHoardForMerge (requested available : Nat)
  | invalidKktClearing
  | quoteBackingMismatch (collected expected : Int)
  deriving DecidableEq, Repr

/-- Executable checker verifying both the `dclutch` Hoard complete-set invariant and the
    $N$-outcome simplex KKT clearing certificate. -/
def verifyDclutchHoardClearing (s : HoardMarketState) (c : JointClearingCert) :
    Except DclutchHoardRefusal Unit :=
  match hoardCollateralValid s with
  | false => .error .hoardInvariantViolated
  | true =>
    match s.outcomes == c.outcomeCount with
    | false => .error (.outcomeCountMismatch s.outcomes c.outcomeCount)
    | true =>
      match !decide (0 ≤ c.sets) && !canMergeCompleteSet s (-c.sets).toNat with
      | true => .error (.insufficientHoardForMerge (-c.sets).toNat s.hoard)
      | false =>
        match jointClearingValid c with
        | false => .error .invalidKktClearing
        | true =>
          match decide (collectedQuote c c.fills = (c.scale : Int) * c.sets) with
          | false => .error (.quoteBackingMismatch (collectedQuote c c.fills) ((c.scale : Int) * c.sets))
          | true => .ok ()

/-- Declarative semantic specification for `dclutchHoardJudge`:
    1. `HoardCollateralInvariant s` holds pre-clearing and post-clearing,
    2. `c.prices.sum = c.scale` (simplex price normalization),
    3. `collectedQuote c c.fills = (c.scale : Int) * c.sets` (exact Hoard set funding),
    4. Every filled order executes at or better than its limit (`perLotDebit ≤ limit`). -/
def DclutchHoardMeaning (s : HoardMarketState) (c : JointClearingCert) : Prop :=
  HoardCollateralInvariant s ∧
  HoardCollateralInvariant (applyCompleteSetDelta s c.sets) ∧
  c.prices.sum = c.scale ∧
  collectedQuote c c.fills = (c.scale : Int) * c.sets ∧
  (∀ f ∈ c.fills, 0 < f.lots → f.order.perLotDebit c ≤ f.order.limit)

/-- Bridge theorem: any `(s, c)` accepted by `verifyDclutchHoardClearing` satisfies `DclutchHoardMeaning s c`. -/
theorem verifyDclutchHoardClearing_sound {s : HoardMarketState} {c : JointClearingCert}
    (h : verifyDclutchHoardClearing s c = .ok ()) :
    DclutchHoardMeaning s c := by
  unfold verifyDclutchHoardClearing at h
  cases h1 : hoardCollateralValid s <;> rw [h1] at h
  · cases h
  · cases h2 : (s.outcomes == c.outcomeCount) <;> rw [h2] at h
    · cases h
    · cases h3 : (!decide (0 ≤ c.sets) && !canMergeCompleteSet s (-c.sets).toNat) <;> rw [h3] at h
      · cases h4 : jointClearingValid c <;> rw [h4] at h
        · cases h
        · have hInv : HoardCollateralInvariant s := (hoardCollateralValid_iff s).mp h1
          exact ⟨hInv,
            applyCompleteSetDelta_preserves_invariant s c.sets hInv,
            prices_sum_to_scale c h4,
            collectedQuote_funds_sets c h4,
            fun f hf hpos => filled_at_or_better c h4 f hf hpos⟩
      · cases h

/-- Standalone verdict checker for `HoardMarketState` and `JointClearingCert`. -/
def dclutchHoardCheck (_ : Nat) (s : HoardMarketState) (c : JointClearingCert) :
    Verdict DclutchHoardRefusal :=
  match verifyDclutchHoardClearing s c with
  | .ok () => .ok
  | .error r => .refused r []

/-- `Judge` instance for `dclutch` Hoard complete-set & joint KKT clearing.
    Note: `.hoardInvariantViolated` is a genuine universal refutation (`refutes = true`)
    because an under-collateralized `HoardMarketState` cannot satisfy `HoardCollateralInvariant s`. -/
instance dclutchHoardJudge : Judge HoardMarketState JointClearingCert where
  Clause := DclutchHoardRefusal
  Meaning := DclutchHoardMeaning
  check := dclutchHoardCheck
  sound := by
    intro _ s c h
    unfold dclutchHoardCheck at h
    cases hVer : verifyDclutchHoardClearing s c with
    | ok u =>
      cases u
      exact verifyDclutchHoardClearing_sound hVer
    | error r => rw [hVer] at h; cases h
  refutes
    | .hoardInvariantViolated => true
    | _ => false
  refuted := by
    intro _ s c k _ h hk _ hMean
    cases k <;> try cases hk
    have hInvC' : hoardCollateralValid s = true :=
      (hoardCollateralValid_iff s).mpr hMean.1
    unfold dclutchHoardCheck verifyDclutchHoardClearing at h
    rw [hInvC'] at h
    cases h2 : (s.outcomes == c.outcomeCount) <;> rw [h2] at h
    · cases h
    · cases h3 : (!decide (0 ≤ c.sets) && !canMergeCompleteSet s (-c.sets).toNat) <;> rw [h3] at h
      · cases h4 : jointClearingValid c <;> rw [h4] at h
        · cases h
        · cases h5 : decide (collectedQuote c c.fills = (c.scale : Int) * c.sets) <;> rw [h5] at h <;> cases h
      · cases h
  Fragment s := ∃ c, verifyDclutchHoardClearing s c = .ok ()
  complete := by
    intro _ ⟨c, hc⟩ _
    refine ⟨c, 0, ?_⟩
    unfold dclutchHoardCheck
    rw [hc]
  mono := by intro _ _ _ _ _ _; rfl

/-- Sample 2-outcome fully-collateralized Hoard market state (`hoard = 10`, `supply = [10, 10]`). -/
def sampleHoardState : HoardMarketState where
  outcomes := 2
  hoard := 10
  supply := [10, 10]

/-- Helper to construct a single-outcome buy order in a `width`-outcome market. -/
def mkOutcomeBuy (id outcome qty : Nat) (limit : Int) (width : Nat) : JointOrder where
  orderId := id
  receivePerLot := (List.range width).map fun i => if i == outcome then 1 else 0
  deliverPerLot := List.replicate width 0
  quantity := qty
  limit := limit

/-- Valid 2-outcome joint mint clearing certificate: two opposite buyers at prices `[50, 50]`
    (`scale = 100`) jointly fund `sets = 1` new complete set (`collectedQuote = 100`). -/
def goodHoardClearingCert : JointClearingCert where
  outcomeCount := 2
  scale := 100
  prices := [50, 50]
  fills := [
    { order := mkOutcomeBuy 1 0 1 60 2, lots := 1 },
    { order := mkOutcomeBuy 2 1 1 60 2, lots := 1 }
  ]
  sets := 1

/-- Planted bad certificate for `dclutchHoardFormat`: off-simplex prices `[50, 40]` (`sum = 90 ≠ 100`). -/
def badHoardClearingCert : JointClearingCert where
  outcomeCount := 2
  scale := 100
  prices := [50, 40]
  fills := [
    { order := mkOutcomeBuy 1 0 1 60 2, lots := 1 },
    { order := mkOutcomeBuy 2 1 1 60 2, lots := 1 }
  ]
  sets := 1

theorem goodHoardClearingCert_accepted :
    dclutchHoardCheck 1 sampleHoardState goodHoardClearingCert = .ok :=
  rfl

theorem badHoardClearingCert_refused :
    dclutchHoardCheck 1 sampleHoardState badHoardClearingCert =
      .refused .invalidKktClearing [] :=
  rfl

/-- Encode `HoardMarketState` as canonical JSON wire string. -/
def encodeHoardState (s : HoardMarketState) : String :=
  Json.compress <| Json.mkObj
    [ ("outcomes", toJson s.outcomes)
    , ("hoard", toJson s.hoard)
    , ("supply", Json.arr (s.supply.map toJson).toArray) ]

/-- Parse `HoardMarketState` from JSON wire string. -/
def decodeHoardState (s : String) : Except String HoardMarketState := do
  let j ← Json.parse s
  let outcomes ← j.getObjValAs? Nat "outcomes"
  let hoard ← j.getObjValAs? Nat "hoard"
  let supply ← (← (← j.getObjVal? "supply").getArr?).toList.mapM (·.getNat?)
  pure { outcomes, hoard, supply }

/-- Encode `JointOrder` to `Lean.Json`. -/
def jointOrderToJson (o : JointOrder) : Json :=
  Json.mkObj
    [ ("orderId", toJson o.orderId)
    , ("receivePerLot", Json.arr (o.receivePerLot.map toJson).toArray)
    , ("deliverPerLot", Json.arr (o.deliverPerLot.map toJson).toArray)
    , ("quantity", toJson o.quantity)
    , ("limit", toJson o.limit) ]

/-- Parse `JointOrder` from `Lean.Json`. -/
def jointOrderOfJson (j : Json) : Except String JointOrder := do
  let orderId ← j.getObjValAs? Nat "orderId"
  let receivePerLot ← (← (← j.getObjVal? "receivePerLot").getArr?).toList.mapM (·.getNat?)
  let deliverPerLot ← (← (← j.getObjVal? "deliverPerLot").getArr?).toList.mapM (·.getNat?)
  let quantity ← j.getObjValAs? Nat "quantity"
  let limit ← j.getObjValAs? Int "limit"
  pure { orderId, receivePerLot, deliverPerLot, quantity, limit }

/-- Encode `JointFill` to `Lean.Json`. -/
def jointFillToJson (f : JointFill) : Json :=
  Json.mkObj
    [ ("order", jointOrderToJson f.order)
    , ("lots", toJson f.lots) ]

/-- Parse `JointFill` from `Lean.Json`. -/
def jointFillOfJson (j : Json) : Except String JointFill := do
  let order ← jointOrderOfJson (← j.getObjVal? "order")
  let lots ← j.getObjValAs? Nat "lots"
  pure { order, lots }

/-- Encode `JointClearingCert` as canonical JSON wire string. -/
def encodeJointClearingCert (c : JointClearingCert) : String :=
  Json.compress <| Json.mkObj
    [ ("outcomeCount", toJson c.outcomeCount)
    , ("scale", toJson c.scale)
    , ("prices", Json.arr (c.prices.map toJson).toArray)
    , ("fills", Json.arr (c.fills.map jointFillToJson).toArray)
    , ("sets", toJson c.sets) ]

/-- Parse `JointClearingCert` from JSON wire string. -/
def decodeJointClearingCert (s : String) : Except String JointClearingCert := do
  let j ← Json.parse s
  let outcomeCount ← j.getObjValAs? Nat "outcomeCount"
  let scale ← j.getObjValAs? Nat "scale"
  let prices ← (← (← j.getObjVal? "prices").getArr?).toList.mapM (·.getNat?)
  let fills ← (← (← j.getObjVal? "fills").getArr?).toList.mapM jointFillOfJson
  let sets ← j.getObjValAs? Int "sets"
  pure { outcomeCount, scale, prices, fills, sets }

/-- Registered `Obend.Judge.Format` for `dclutch-hoard-clearing` v`1`. -/
def dclutchHoardFormat : Judge.Format where
  name := "dclutch-hoard-clearing"
  version := "1"
  Obj := HoardMarketState
  Cert := JointClearingCert
  decodeObj := decodeHoardState
  decodeCert := decodeJointClearingCert
  trust := .kernel
  regime := .decidable
  bad := (sampleHoardState, badHoardClearingCert)
  badGrade := 1
  bad_refused := ⟨_, _, badHoardClearingCert_refused⟩

end Obend.Judge
end
