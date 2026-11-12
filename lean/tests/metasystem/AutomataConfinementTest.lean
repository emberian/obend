module

public import Obend.Tactic.Tooth
public meta import Obend.Digest.HashBytes
public meta import Obend.Digest.Cshake256
public meta import Obend.Codec.DetCbor
public import Obend.Judge.AutomataConfinement
import all Obend.Judge.Class
import all Obend.Judge.AutomataConfinement

/-!
# Metasystem Test Suite — `Obend.Judge.AutomataConfinement`

Comprehensive positive tests, edge-case & negative refutation checks, `#tooth`
mutation-killing barriers, and `#print axioms` verification for all four pillars of
`Obend.Judge.AutomataConfinement`:

1. **Pillar A**: Brzozowski / Table-DFA Trace & Complement Confinement (`TableDfa`, `dfaAccepts`, `runningDigest`, `InjectionFree`, `badCert`, `dfaFormat`).
2. **Pillar B**: $O(\text{tokens})$ Compact Pushdown CFG Replay Certificate (`CfgRule`, `PushdownReplay`, `replayCfgCompact`, `replayCfgCompact_sound`, `cfgCompactFormat`).
3. **Pillar C**: Structured Prompt & Transcript Slot Confinement (`PromptTemplate`, `Seg.lit`, `Seg.slot`, `AllSlotsClean`, `slot_confinement`, `injected_slot_breaks_confinement`, `leaf_book_slot_confinement`, `term_slot_confinement`).
4. **Pillar D**: `dclutch` Liquidation-Cascade-Free Hoard Complete-Set & Joint KKT Clearing Judge (`HoardMarketState`, `splitCompleteSet`, `mergeCompleteSet`, `JointClearingCert`, `prices_sum_to_scale`, `filled_at_or_better`, `partial_fill_is_marginal`, `collectedQuote_funds_sets`, `dclutchHoardFormat`).
-/

public section
namespace Obend.Tests.Metasystem.AutomataConfinementTest

open Obend
open Obend.Core
open Obend.Core.Term
open Obend.Slot
open Obend.Leaf
open Obend.Judge

/-! ## 1. Pillar A Tests: Brzozowski / Table-DFA Trace & Complement Confinement -/

-- Format metadata checks
example : dfaFormat.name = "dfa-confinement" := by exact id rfl
example : dfaFormat.version = "1" := by exact id rfl
example : dfaFormat.regime = .decidable := by exact id rfl
example : dfaFormat.trust = .compiled := by exact id rfl

-- Positive certificate acceptance & byte-boundary acceptance
example : dfaConfinementCheck 1 defaultDfaQuery goodDfaCert = .ok :=
  goodDfaCert_accepted

#guard match dfaFormat.checkBytes 1 (encodeDfaQuery defaultDfaQuery) (encodeDfaCert goodDfaCert) with
  | .ok => true | _ => false

example (h : dfaFormat.checkBytes 1 (encodeDfaQuery defaultDfaQuery) (encodeDfaCert goodDfaCert) = .ok) :
    ∃ o c, dfaFormat.decodeObj (encodeDfaQuery defaultDfaQuery) = .ok o ∧
      dfaFormat.decodeCert (encodeDfaCert goodDfaCert) = .ok c ∧
      dfaFormat.judge.Meaning o c :=
  dfaFormat.checkBytes_sound h

-- Empty token trace boundary case
def emptyDfaCert : DfaConfinementCert where
  tokens := []
  claimedDigest := 7

example :
    dfaConfinementCheck 1 defaultDfaQuery emptyDfaCert = .ok := by exact id rfl

theorem empty_injectionFree : InjectionFree [] :=
  (injectionFree_iff_dfaAccepts []).mpr rfl

-- Planted bad certificate refusal (`badCert` containing `"{{"`)
example : dfaConfinementCheck 1 defaultDfaQuery badCert =
    .refused (.injectionDetected "{{") [] :=
  badCert_refused

#guard match dfaFormat.checkBytes 1 (encodeDfaQuery defaultDfaQuery) (encodeDfaCert badCert) with
  | .refused (.judge (.injectionDetected "{{")) [] => true | _ => false

-- Negative edge cases: tampered digest, non-accepted state, final state mismatch
def tamperedDigestDfaCert : DfaConfinementCert :=
  { goodDfaCert with claimedDigest := 999 }

#guard match dfaConfinementCheck 1 defaultDfaQuery tamperedDigestDfaCert with
  | .refused (.digestMismatch _ 999) [] => true | _ => false

def nonInjectionFreeQuery : DfaConfinementQuery :=
  { defaultDfaQuery with requireInjectionFree := false }

example :
    dfaConfinementCheck 1 nonInjectionFreeQuery badCert =
      .refused (.notAccepted 1) [] := by exact id rfl

def mismatchedExpectedStateQuery : DfaConfinementQuery :=
  { defaultDfaQuery with expectedFinalState := 1 }

theorem finalStateMismatch_refused :
    dfaConfinementCheck 1 mismatchedExpectedStateQuery goodDfaCert =
      .refused (.expectedStateNotAccepting 1) [] := by exact id rfl

-- Monotonicity & non-triviality witnesses from `dfaFormat`
example {g : Nat} (h : 1 ≤ g) :
    ∃ c w, dfaFormat.judge.check g dfaFormat.bad.1 dfaFormat.bad.2 = .refused c w :=
  dfaFormat.refused_above h

example {g : Nat} (h : 1 ≤ g) :
    dfaFormat.judge.check g dfaFormat.bad.1 dfaFormat.bad.2 ≠ .ok :=
  dfaFormat.not_trivial h

-- Pillar A `#tooth` mutation tests:
-- Mutation 1: Weakening `confinementDfa` so trap state `1` is also accepting breaks `badCert_refused`.
def brokenConfinementDfa : TableDfa where
  start := 0
  accepting := [0, 1]
  transitions := []
  stateDefaults := [(0, 0), (1, 1)]
  defaultSink := 0

#tooth Obend.Judge.badCert_refused
  by mutation Obend.Judge.confinementDfa := brokenConfinementDfa

-- A verifier that drops the committed transcript cannot establish the declared meaning.
#tooth verifyDfaConfinement_sound by
  mutation verifyDfaConfinement := fun _ _ => .ok ()



/-! ## 2. Pillar B Tests: $O(\text{tokens})$ Compact Pushdown CFG Replay Certificate -/

-- Format metadata checks
example : cfgCompactFormat.name = "cfg-compact" := by exact id rfl
example : cfgCompactFormat.version = "1" := by exact id rfl
example : cfgCompactFormat.regime = .decidable := by exact id rfl
example : cfgCompactFormat.trust = .kernel := by exact id rfl

-- Positive certificate acceptance & soundness bridge
example : cfgCompactCheck 1 sampleCfgQuery goodCfgCert = .ok :=
  goodCfgCert_accepted

#guard match cfgCompactFormat.checkBytes 1 (encodeCfgQuery sampleCfgQuery) (encodeCfgCert goodCfgCert) with
  | .ok => true | _ => false

theorem goodCfgCert_sound_derivation :
    PushdownReplay transcriptCfg goodCfgCert.rules sampleCfgQuery.input [.nonterminal transcriptCfg.start] ∧
    CfgDerives transcriptCfg [.nonterminal transcriptCfg.start] (sampleCfgQuery.input.map .terminal) :=
  replayCfgCompact_sound transcriptCfg goodCfgCert.rules sampleCfgQuery.input rfl

-- Recursive nested array derivation `{"msg": [[ "ok" ]]}`
def nestedCfgQuery : CfgCompactQuery where
  grammar := transcriptCfg
  input := ["{", "msg", ":", "[", "[", "\"ok\"", "]", "]", "}"]

def nestedCfgCert : CfgCompactCert where
  rules := [rEnvelope, rArray, rArray, rString]

theorem nestedCfgCert_accepted :
    cfgCompactCheck 1 nestedCfgQuery nestedCfgCert = .ok := by exact id rfl

-- Negative edge cases: missing rule, terminal mismatch, LHS mismatch, unknown rule, unconsumed input, unconsumed rules
example : cfgCompactCheck 1 sampleCfgQuery badCfgCert =
    .refused (.missingRuleFor "S") [] :=
  badCfgCert_refused

def terminalMismatchCfgQuery : CfgCompactQuery where
  grammar := transcriptCfg
  input := ["{", "msg", ":", "[", "{{", "]", "}"]

example :
    cfgCompactCheck 1 terminalMismatchCfgQuery goodCfgCert =
      .refused (.terminalMismatch "\"ok\"" "{{") [] := by exact id rfl

def lhsMismatchCfgCert : CfgCompactCert where
  rules := [rArray]

example :
    cfgCompactCheck 1 sampleCfgQuery lhsMismatchCfgCert =
      .refused (.lhsMismatch "S" "Val") [] := by exact id rfl

def forgedRule : CfgRule :=
  { lhs := "S", rhs := [.terminal "{{"] }

def unknownRuleCfgCert : CfgCompactCert where
  rules := [forgedRule]

example :
    cfgCompactCheck 1 sampleCfgQuery unknownRuleCfgCert =
      .refused (.unknownRule forgedRule) [] := by exact id rfl

def unconsumedInputCfgQuery : CfgCompactQuery where
  grammar := transcriptCfg
  input := ["{", "msg", ":", "[", "\"ok\"", "]", "}", "extra"]

example :
    cfgCompactCheck 1 unconsumedInputCfgQuery goodCfgCert =
      .refused (.unconsumedInput ["extra"]) [] := by exact id rfl

def unconsumedRulesCfgCert : CfgCompactCert where
  rules := [rEnvelope, rArray, rString, rString]

theorem unconsumedRulesCfg_refused :
    cfgCompactCheck 1 sampleCfgQuery unconsumedRulesCfgCert =
      .refused (.unconsumedRules 1) [] := by exact id rfl

-- Pillar B `#tooth` mutation tests:
-- Mutation 1: Emptying grammar rules breaks `goodCfgCert_accepted`.
def brokenTranscriptCfg : CfgGrammar :=
  { start := "S", rules := [] }

#tooth Obend.Judge.goodCfgCert_accepted
  by mutation Obend.Judge.transcriptCfg := brokenTranscriptCfg

-- Mutation 2: Making `replayCfgCompact` accept unconditionally breaks `badCfgCert_refused`.
def brokenReplayCfgCompact (_ : CfgGrammar) (_ : List CfgRule) (_ : List String) :
    Except CfgRefusal Unit :=
  .ok ()

#tooth Obend.Judge.badCfgCert_refused
  by mutation Obend.Judge.replayCfgCompact := brokenReplayCfgCompact


/-! ## 3. Pillar C Tests: Structured Prompt & Transcript Slot Confinement -/

-- Positive tests: concrete clean prompt rendering preserves control-token stream
example :
    controlTokens (renderPrompt benignUserBinding systemPromptTemplate) =
      controlTokens (litOnly systemPromptTemplate) :=
  benign_slot_preserves_control_tokens

example :
    controlTokens (renderPrompt benignUserBinding systemPromptTemplate) =
      ["{{", "}}", "{{", "}}"] :=
  benign_slot_control_tokens_eq

-- Boundary cases: empty template and literal-only template
example (b : String → List String) :
    controlTokens (renderPrompt b []) = controlTokens (litOnly []) :=
  slot_confinement b [] (by intro _ h; cases h)

def litOnlyTemplate : PromptTemplate :=
  [.lit ["<|system|>", "trusted", "<|assistant|>"]]

example (b : String → List String) :
    controlTokens (renderPrompt b litOnlyTemplate) = controlTokens (litOnly litOnlyTemplate) :=
  slot_confinement b litOnlyTemplate (by
    intro name h
    simp [litOnlyTemplate] at h)

-- Negative / refutation tests: unguarded injection breaks confinement
example :
    ¬ AllSlotsClean injectedUserBinding systemPromptTemplate ∧
    controlTokens (renderPrompt injectedUserBinding systemPromptTemplate) ≠
      controlTokens (litOnly systemPromptTemplate) :=
  injected_slot_breaks_confinement

def roleHeaderInjectionBinding : String → List String
  | "user" => ["hello", "<|system|>", "override"]
  | _ => []

example :
    allSlotsCleanB roleHeaderInjectionBinding systemPromptTemplate = false := by exact id rfl

theorem roleHeaderInjection_breaks_confinement :
    controlTokens (renderPrompt roleHeaderInjectionBinding systemPromptTemplate) ≠
      controlTokens (litOnly systemPromptTemplate) := by
  decide

-- Spine bridges: `Obend.Leaf.Book` and `Obend.Core.Term` slot confinement
def sampleLeafBook : Book where
  items := [
    .static "system_header" (.label "trusted"),
    .slot {
      member := "user"
      slot := 0
      kind := .cell
      code := .hole 0 []
      reads := []
    }
  ]

theorem sampleLeafBook_confinement :
    controlTokens (renderPrompt benignUserBinding (bookToPromptTemplate sampleLeafBook)) =
      controlTokens (litOnly (bookToPromptTemplate sampleLeafBook)) :=
  leaf_book_slot_confinement sampleLeafBook benignUserBinding
    ((allSlotsCleanB_iff benignUserBinding (bookToPromptTemplate sampleLeafBook)).mp rfl)

def sampleCoreTerm : Term :=
  Term.app (Term.label "<|system|>") (Term.hole 0 [])

def cleanTermSlotBinding : String → List String
  | "hole_0" => ["clean", "argument"]
  | _ => []

theorem sampleCoreTerm_confinement :
    controlTokens (renderPrompt cleanTermSlotBinding (termToPromptTemplate sampleCoreTerm)) =
      controlTokens (litOnly (termToPromptTemplate sampleCoreTerm)) :=
  term_slot_confinement sampleCoreTerm cleanTermSlotBinding
    ((allSlotsCleanB_iff cleanTermSlotBinding (termToPromptTemplate sampleCoreTerm)).mp rfl)

-- Pillar C `#tooth` mutation tests:
-- Mutation 1: Replacing `injectedUserBinding` with `benignUserBinding` breaks `injected_slot_breaks_confinement`.
#tooth Obend.Judge.injected_slot_breaks_confinement
  by mutation Obend.Judge.injectedUserBinding := benignUserBinding

-- Mutation 2: Replacing `controlTokens` with `id` (failing to filter only control tokens)
-- breaks `benign_slot_control_tokens_eq`.
def brokenControlTokens (tokens : List String) : List String := tokens

#tooth Obend.Judge.benign_slot_control_tokens_eq
  by mutation Obend.Judge.controlTokens := brokenControlTokens


/-! ## 4. Pillar D Tests: `dclutch` Hoard Complete-Set & Joint KKT Clearing Judge -/

-- Format metadata checks
example : dclutchHoardFormat.name = "dclutch-hoard-clearing" := by exact id rfl
example : dclutchHoardFormat.version = "1" := by exact id rfl
example : dclutchHoardFormat.regime = .decidable := by exact id rfl
example : dclutchHoardFormat.trust = .kernel := by exact id rfl

-- Positive certificate acceptance & soundness bridge
example : dclutchHoardCheck 1 sampleHoardState goodHoardClearingCert = .ok :=
  goodHoardClearingCert_accepted

#guard match dclutchHoardFormat.checkBytes 1 (encodeHoardState sampleHoardState) (encodeJointClearingCert goodHoardClearingCert) with
  | .ok => true | _ => false

theorem sampleHoardState_invariant : HoardCollateralInvariant sampleHoardState :=
  (hoardCollateralValid_iff sampleHoardState).mp rfl

-- Complete-set split & merge preserve Hoard full backing (`supply i ≤ hoard`)
theorem split_sampleHoardState_invariant (qty : Nat) :
    HoardCollateralInvariant (splitCompleteSet sampleHoardState qty) :=
  splitCompleteSet_preserves_invariant sampleHoardState qty sampleHoardState_invariant

theorem merge_sampleHoardState_invariant (qty : Nat) :
    HoardCollateralInvariant (mergeCompleteSet sampleHoardState qty) :=
  mergeCompleteSet_preserves_invariant sampleHoardState qty sampleHoardState_invariant

-- 3-outcome joint mint clearing certificate (`outcomeCount = 3`, `prices = [30, 30, 40]`, `sets = 2`)
def threeOutcomeHoardState : HoardMarketState where
  outcomes := 3
  hoard := 5
  supply := [5, 5, 5]

def threeOutcomeMintCert : JointClearingCert where
  outcomeCount := 3
  scale := 100
  prices := [30, 30, 40]
  fills := [
    { order := mkOutcomeBuy 10 0 2 35 3, lots := 2 },
    { order := mkOutcomeBuy 11 1 2 35 3, lots := 2 },
    { order := mkOutcomeBuy 12 2 2 45 3, lots := 2 }
  ]
  sets := 2

example :
    dclutchHoardCheck 1 threeOutcomeHoardState threeOutcomeMintCert = .ok := by exact id rfl

theorem threeOutcomeMintCert_quote_funds_sets :
    collectedQuote threeOutcomeMintCert threeOutcomeMintCert.fills = 200 := by exact id rfl

-- Joint merge clearing certificate (`sets = -1`, burning 1 complete set from `sampleHoardState`)
def mkOutcomeSell (id outcome qty : Nat) (minCredit : Int) (width : Nat) : JointOrder where
  orderId := id
  receivePerLot := List.replicate width 0
  deliverPerLot := (List.range width).map fun i => if i == outcome then 1 else 0
  quantity := qty
  limit := -minCredit

def goodHoardMergeCert : JointClearingCert where
  outcomeCount := 2
  scale := 100
  prices := [60, 40]
  fills := [
    { order := mkOutcomeSell 21 0 1 55 2, lots := 1 },
    { order := mkOutcomeSell 22 1 1 35 2, lots := 1 }
  ]
  sets := -1

theorem goodHoardMergeCert_accepted :
    dclutchHoardCheck 1 sampleHoardState goodHoardMergeCert = .ok := by exact id rfl

-- Negative / refusal edge cases:
-- 1. Off-simplex prices (`[50, 40]`, sum = 90 ≠ 100)
example : dclutchHoardCheck 1 sampleHoardState badHoardClearingCert =
    .refused .invalidKktClearing [] :=
  badHoardClearingCert_refused

-- 2. Under-collateralized Hoard (`hoard = 5 < supply = 10`)
def undercollateralizedHoardState : HoardMarketState where
  outcomes := 2
  hoard := 5
  supply := [10, 10]

theorem undercollateralizedHoardState_refused :
    dclutchHoardCheck 1 undercollateralizedHoardState goodHoardClearingCert =
      .refused .hoardInvariantViolated [] := by exact id rfl

-- 3. Excessive merge (`sets = -20` when `hoard = 10`)
def excessiveMergeCert : JointClearingCert :=
  { goodHoardMergeCert with sets := -20 }

theorem excessiveMergeCert_refused :
    dclutchHoardCheck 1 sampleHoardState excessiveMergeCert =
      .refused (.insufficientHoardForMerge 20 10) [] := by exact id rfl

-- 4. Limit price violated (`perLotDebit = 50 > limit = 40`)
def limitViolatedCert : JointClearingCert where
  outcomeCount := 2
  scale := 100
  prices := [50, 50]
  fills := [
    { order := mkOutcomeBuy 1 0 1 40 2, lots := 1 },
    { order := mkOutcomeBuy 2 1 1 60 2, lots := 1 }
  ]
  sets := 1

theorem limitViolatedCert_refused :
    dclutchHoardCheck 1 sampleHoardState limitViolatedCert =
      .refused .invalidKktClearing [] := by exact id rfl

-- 5. Duplicate order IDs in fills
def duplicateOrderIdCert : JointClearingCert where
  outcomeCount := 2
  scale := 100
  prices := [50, 50]
  fills := [
    { order := mkOutcomeBuy 1 0 1 60 2, lots := 1 },
    { order := mkOutcomeBuy 1 1 1 60 2, lots := 1 }
  ]
  sets := 1

theorem duplicateOrderIdCert_refused :
    dclutchHoardCheck 1 sampleHoardState duplicateOrderIdCert =
      .refused .invalidKktClearing [] := by exact id rfl

-- Pillar D `#tooth` mutation tests:
-- Mutation 1: Falsifying `hoardCollateralValid` breaks `goodHoardClearingCert_accepted`.
def brokenHoardCollateralValid (_ : HoardMarketState) : Bool := false

#tooth Obend.Judge.goodHoardClearingCert_accepted
  by mutation Obend.Judge.hoardCollateralValid := brokenHoardCollateralValid

-- Mutation 2: Removing the KKT simplex validation in `verifyDclutchHoardClearing`
-- breaks `badHoardClearingCert_refused`.
def brokenVerifyDclutchHoardClearing (_ : HoardMarketState) (_ : JointClearingCert) :
    Except DclutchHoardRefusal Unit :=
  .ok ()

#tooth Obend.Judge.badHoardClearingCert_refused
  by mutation Obend.Judge.verifyDclutchHoardClearing := brokenVerifyDclutchHoardClearing


/-! ## 5. Extended Edge-Case, Codec, Spine-Bridge & Regression Tests -/

-- Equal-length unknown tokens, including the former length-code collision.
#guard tokenCode "unlisted-a" != tokenCode "unlisted-b"
#guard runningDigest confinementDfa 7 ["unlisted-a"] != runningDigest confinementDfa 7 ["unlisted-b"]

-- 5.2 `TableDfa.classify`, `TableDfa.complement`, `brzozowskiAccepts_singleton_eq`, and `buildDfaTrace_valid`
example : confinementDfa.classify ["hello", "world"] = 0 := by exact id rfl
example : brzozowskiAccepts confinementDfa [0] ["hello", "world"] =
    dfaAccepts confinementDfa ["hello", "world"] :=
  brzozowskiAccepts_singleton_eq confinementDfa ["hello", "world"]

example : dfaAccepts (confinementDfa.complement 2) ["hello", "{{"] = true := by exact id rfl
example : dfaAccepts (confinementDfa.complement 2) ["hello", "world"] = false := by exact id rfl

example : verifyDfaTraceRows confinementDfa 7 0 ["hello", "world"]
    (buildDfaTrace confinementDfa 7 ["hello", "world"]) = true :=
  buildDfaTrace_valid confinementDfa 7 ["hello", "world"]

-- 5.3 Constructive wire encoders/decoders (`encodeDfaCert`, `encodeCfgCert`, `encodeHoardState`)
#guard match decodeDfaCert (encodeDfaCert goodDfaCert) with | .ok c => c == goodDfaCert | .error _ => false
#guard match decodeDfaCert (encodeDfaCert tamperedDigestDfaCert) with | .ok c => c == tamperedDigestDfaCert | .error _ => false
#guard match dfaFormat.checkBytes 1 (encodeDfaQuery defaultDfaQuery) (encodeDfaCert goodDfaCert) with | .ok => true | _ => false

#guard match decodeCfgCert (encodeCfgCert goodCfgCert) with | .ok c => c == goodCfgCert | .error _ => false
#guard match cfgCompactFormat.checkBytes 1 (encodeCfgQuery nestedCfgQuery) (encodeCfgCert nestedCfgCert) with | .ok => true | _ => false

#guard match decodeHoardState (encodeHoardState sampleHoardState) with | .ok s => s == sampleHoardState | .error _ => false
#guard match decodeHoardState (encodeHoardState threeOutcomeHoardState) with | .ok s => s == threeOutcomeHoardState | .error _ => false
#guard match dclutchHoardFormat.checkBytes 1 (encodeHoardState threeOutcomeHoardState) (encodeJointClearingCert threeOutcomeMintCert) with | .ok => true | _ => false

-- 5.4 `Obend.Slot.Protocol` spine bridge (`PromptProt`, `protToPromptTemplate_roundtrip`, `slot_protocol_confinement`)
def samplePromptProt : PromptProt () :=
  promptTemplateToProt systemPromptTemplate

example : protToPromptTemplate samplePromptProt = systemPromptTemplate :=
  protToPromptTemplate_roundtrip systemPromptTemplate

theorem samplePromptProt_confinement :
    controlTokens (renderPrompt benignUserBinding (protToPromptTemplate samplePromptProt)) =
      controlTokens (litOnly (protToPromptTemplate samplePromptProt)) :=
  slot_protocol_confinement samplePromptProt benignUserBinding
    ((allSlotsCleanB_iff benignUserBinding (protToPromptTemplate samplePromptProt)).mp rfl)

-- 5.5 Injective `holeSlotName` for `n ≥ 3` and `termSlotBinding`
example :
    holeSlotName 3 = "hole_3" ∧ holeSlotName 4 = "hole_4" ∧ holeSlotName 3 ≠ holeSlotName 4 := by
  decide

def multiHoleCoreTerm : Term :=
  Term.app (Term.inject "<|system|>" (Term.hole 3 [])) (Term.hole 4 [])

def cleanMultiHoleBinding : String → List String :=
  termSlotBinding [(3, ["safe", "arg3"]), (4, ["safe", "arg4"])]

theorem multiHoleCoreTerm_confinement :
    controlTokens (renderPrompt cleanMultiHoleBinding (termToPromptTemplate multiHoleCoreTerm)) =
      controlTokens (litOnly (termToPromptTemplate multiHoleCoreTerm)) :=
  term_slot_confinement multiHoleCoreTerm cleanMultiHoleBinding
    ((allSlotsCleanB_iff cleanMultiHoleBinding (termToPromptTemplate multiHoleCoreTerm)).mp rfl)

-- 5.6 Multi-slot prompt template with repeated slot names and empty slot fillings
def repeatedMultiSlotTemplate : PromptTemplate :=
  [ .lit ["{{", "header", "}}"]
  , .slot "user"
  , .slot "empty_ctx"
  , .lit ["<|assistant|>"]
  , .slot "user"
  , .lit ["{{", "footer", "}}"] ]

def repeatedMultiSlotBinding : String → List String :=
  bindingToSlotTokens [("user", ["first", "question"]), ("empty_ctx", [])]

theorem repeatedMultiSlot_confinement :
    controlTokens (renderPrompt repeatedMultiSlotBinding repeatedMultiSlotTemplate) =
      controlTokens (litOnly repeatedMultiSlotTemplate) :=
  slot_confinement repeatedMultiSlotBinding repeatedMultiSlotTemplate
    ((allSlotsCleanB_iff repeatedMultiSlotBinding repeatedMultiSlotTemplate).mp rfl)

-- 5.7 Complete-set split/merge exact roundtrip conservation & `HoardCompleteSetInvariant`
example : HoardCompleteSetInvariant sampleHoardState := sampleHoardState_invariant
example (qty : Nat) : mergeCompleteSet (splitCompleteSet sampleHoardState qty) qty = sampleHoardState :=
  mergeCompleteSet_splitCompleteSet_cancel sampleHoardState qty
example : splitCompleteSet (mergeCompleteSet sampleHoardState 4) 4 = sampleHoardState :=
  splitCompleteSet_mergeCompleteSet_cancel sampleHoardState 4 rfl

-- 5.8 4-outcome (`outcomes = 4 > 3`) KKT clearing certificate with partial fills on multiple marginal price levels
def fourOutcomeHoardState : HoardMarketState where
  outcomes := 4
  hoard := 20
  supply := [20, 20, 20, 20]

/-- 4-outcome clearing at prices `[25, 25, 25, 25]` (`scale = 100`, `sets = 2`):
    - outcome 0: strict in-the-money buy (`limit = 30 > 25`), filled in full (`lots = 2 = quantity`),
    - outcome 1: marginal buy (`limit = 25 = perLotDebit`), partially filled (`lots = 2 < quantity = 5`),
    - outcome 2: two marginal buys (`limit = 25 = perLotDebit`), both partially filled (`lots = 1 < quantity = 3`),
    - outcome 3: marginal buy (`limit = 25`) partially filled (`lots = 2 < quantity = 4`) + out-of-the-money buy (`limit = 20 < 25`, `lots = 0`). -/
def fourOutcomeMarginalCert : JointClearingCert where
  outcomeCount := 4
  scale := 100
  prices := [25, 25, 25, 25]
  fills := [
    { order := mkOutcomeBuy 101 0 2 30 4, lots := 2 },
    { order := mkOutcomeBuy 102 1 5 25 4, lots := 2 },
    { order := mkOutcomeBuy 103 2 3 25 4, lots := 1 },
    { order := mkOutcomeBuy 104 2 3 25 4, lots := 1 },
    { order := mkOutcomeBuy 105 3 4 25 4, lots := 2 },
    { order := mkOutcomeBuy 106 3 2 20 4, lots := 0 }
  ]
  sets := 2

theorem fourOutcomeMarginalCert_accepted :
    dclutchHoardCheck 1 fourOutcomeHoardState fourOutcomeMarginalCert = .ok := by exact id rfl

-- KKT surplus optimality on `fourOutcomeMarginalCert`
example (f : JointFill) (hf : f ∈ fourOutcomeMarginalCert.fills) (lots' : Nat)
    (hCap : lots' ≤ f.order.quantity) :
    (f.order.limit - f.order.perLotDebit fourOutcomeMarginalCert) * (lots' : Int) ≤
      (f.order.limit - f.order.perLotDebit fourOutcomeMarginalCert) * (f.lots : Int) :=
  fill_kkt_surplus_optimal fourOutcomeMarginalCert rfl f hf lots' hCap

-- Universal refutation (`dclutchHoardJudge.refuted`) on `undercollateralizedHoardState`
theorem undercollateralized_universally_refuted (c' : JointClearingCert) :
    ¬ dclutchHoardJudge.Meaning undercollateralizedHoardState c' :=
  dclutchHoardJudge.refuted undercollateralizedHoardState_refused rfl c'

-- Bridge to `Obend.Judge.Clearing.Order` (`clearingOrder_crosses_iff_debit_le_limit`)
example (o : Order) :
    o.crosses 50 = true ↔
      (clearingOrderToJointOrder 1 o).perLotDebit
        { outcomeCount := 2, scale := 100, prices := [50, 50], fills := [], sets := 0 } ≤
      (clearingOrderToJointOrder 1 o).limit :=
  clearingOrder_crosses_iff_debit_le_limit 1 50 50 o


/-! Object-level refusals exclude every certificate; ordinary certificate failures do not. -/
theorem impossibleDfa_refutes (c : DfaConfinementCert) :
    ¬ DfaConfinementMeaning mismatchedExpectedStateQuery c :=
  dfaConfinementJudge.refuted (by exact id rfl :
    dfaConfinementCheck 1 mismatchedExpectedStateQuery goodDfaCert =
      .refused (.expectedStateNotAccepting 1) []) rfl c

-- A reachable accepting target may still mismatch this particular certificate.
example : dfaConfinementCheck 1
    { mismatchedExpectedStateQuery with dfa := { confinementDfa with accepting := [0, 1] } }
    goodDfaCert = .refused (.finalStateMismatch 0 1) [] := by exact id rfl
example : dfaConfinementJudge.refutes (.finalStateMismatch 0 1) = false := by exact id rfl
example : dfaConfinementJudge.refutes (.notAccepted 1) = false := by exact id rfl
example : dfaConfinementJudge.refutes (.digestMismatch 0 1) = false := by exact id rfl
example : dfaConfinementJudge.refutes (.injectionDetected "{{") = false := by exact id rfl
example (q : DfaConfinementQuery) : dfaConfinementJudge.Fragment q := trivial

def missingStartQuery : CfgCompactQuery :=
  { grammar := { start := "S", rules := [rArray, rString] }, input := [] }

theorem missingStart_refused : cfgCompactCheck 0 missingStartQuery goodCfgCert =
    .refused (.noStartProduction "S") [] := by exact id rfl

theorem missingStart_refutes (c : CfgCompactCert) : ¬ CfgCompactMeaning missingStartQuery c :=
  cfgCompactJudge.refuted missingStart_refused rfl c

example : cfgCompactJudge.refutes (.missingRuleFor "S") = false := by exact id rfl
example (q : CfgCompactQuery) : cfgCompactJudge.Fragment q := trivial

def brokenVerifyDfaConfinement (_ : DfaConfinementQuery) (_ : DfaConfinementCert) :
    Except DfaRefusal Unit := .ok ()
#tooth Obend.Judge.verifyDfaConfinement_iff
  by mutation Obend.Judge.verifyDfaConfinement := brokenVerifyDfaConfinement
#tooth missingStart_refused
  by mutation Obend.Judge.cfgCompactCheck := fun _ _ _ => .ok

/-! ## 6. Axiom Audit (`0 sorryAx`, `0 Classical.choice`) -/

#print axioms Obend.Judge.dfaFormat
#print axioms Obend.Judge.badCert_refused
#print axioms Obend.Judge.verifyDfaConfinement_sound
#print axioms Obend.Judge.brzozowskiAccepts_singleton_eq
#print axioms Obend.Judge.dfaAccepts_complement_iff
#print axioms Obend.Judge.buildDfaTrace_valid
#print axioms Obend.Judge.cfgCompactFormat
#print axioms Obend.Judge.replayCfgCompact_sound
#print axioms Obend.Judge.replayCfgCompact_iff_pushdownReplay
#print axioms Obend.Judge.slot_confinement
#print axioms Obend.Judge.injected_slot_breaks_confinement
#print axioms Obend.Judge.slot_protocol_confinement
#print axioms Obend.Judge.protToPromptTemplate_roundtrip
#print axioms Obend.Judge.leaf_book_slot_confinement
#print axioms Obend.Judge.term_slot_confinement
#print axioms Obend.Judge.splitCompleteSet_preserves_invariant
#print axioms Obend.Judge.mergeCompleteSet_preserves_invariant
#print axioms Obend.Judge.mergeCompleteSet_splitCompleteSet_cancel
#print axioms Obend.Judge.splitCompleteSet_mergeCompleteSet_cancel
#print axioms Obend.Judge.applyCompleteSetDelta_preserves_invariant
#print axioms Obend.Judge.prices_sum_to_scale
#print axioms Obend.Judge.filled_at_or_better
#print axioms Obend.Judge.partial_fill_is_marginal
#print axioms Obend.Judge.fill_kkt_surplus_optimal
#print axioms Obend.Judge.collectedQuote_funds_sets
#print axioms Obend.Judge.clearingOrder_crosses_iff_debit_le_limit
#print axioms Obend.Judge.verifyDclutchHoardClearing_sound
#print axioms Obend.Judge.dclutchHoardFormat


-- The old tokenCode fallback gave both of these tokens code 310.
theorem aliased_trace_token_refused :
    verifyDfaTraceRows confinementDfa 7 0 ["unlisted-a"]
      [⟨0, "unlisted-b", 0, dfaEntryDigest 0 "unlisted-a" 0,
        compressDigest 7 (dfaEntryDigest 0 "unlisted-a" 0)⟩] = false := by
  simp only [verifyDfaTraceRows,
    show ("unlisted-b" == "unlisted-a") = false by decide, Bool.and_false, Bool.false_and]
#tooth aliased_trace_token_refused by mutation verifyDfaTraceRows := fun _ _ _ _ _ => true
#tooth idleHoardCert_valid by mutation idleHoardCert := fun n => ⟨n, 0, [], [], 0⟩
example : ∃ k, dclutchHoardJudge.refutes k = true := ⟨.hoardInvariantViolated, rfl⟩
theorem bad_hoard_refutes_every_certificate :
    ∀ c, ¬ DclutchHoardMeaning ⟨2, 0, [1, 0]⟩ c := by
  intro c hm
  have h := hm.1.2 0 (by decide)
  change 1 ≤ 0 at h
  omega
example : dclutchHoardCheck 0 ⟨2, 0, [1, 0]⟩ (idleHoardCert 2) =
    .refused .hoardInvariantViolated [] := by decide +kernel
example : dclutchHoardJudge.Fragment ⟨3, 0, [0, 0, 0]⟩ := by
  change 0 < 3
  decide +kernel
example : verifyDclutchHoardClearing ⟨3, 0, [0, 0, 0]⟩ (idleHoardCert 3) = .ok () := by rfl
#guard (decodeDfaCert ("{\"tokens\":[],\"claimedDigest\":" ++ toString (2^256 : Nat) ++ "}")).isOk == false
#print axioms idleHoardCert_valid

end Obend.Tests.Metasystem.AutomataConfinementTest
end
