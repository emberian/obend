module
/-
# Obend.Judge.TranscriptPolicy — selective disclosure of a transcript, confined by the JSON machine

A transcript template is a list of literal segments and slots (`Seg`); each slot is a span the
prover keeps hidden, attested by a `RedactedSpan`: where it sits, a 32-byte commitment to the
hidden bytes, and the class of bytes the notary attests they are drawn from.

**Confinement is stateful.** `slotsConfined` runs `Obend.Judge.VpaJson.stepJson` over the
template's literals and asks that every slot sits in a value string outside any escape
(`mode = .str false .normal`). A byte class is admitted only if it excludes every byte that is not
string-safe (`VpaJson.isSafeMaskByte`: printable ASCII without `"` and `\`). There is no stateless
delimiter list: a hidden backslash before a literal closing quote, or a slot placed after a
literal backslash, is refused by the machine state and the class, not by a table of bytes.

`selective_disclosure_redaction_confinement`: under `slotsConfined`, every string-safe filling of
the slots drives the machine exactly as the literals alone do, so the filled transcript has the
skeleton's grammar verdict and object key sets (`tlsn_filled_document`). `spanConfined` is the
core of `VpaJson.checkJsonRedaction` at a machine state (`checkJsonRedaction_eq_spanConfined`);
`Obend.Judge.DecoAndCallTree` folds it over the spans of a committed transcript.

`tlsnTranscriptJudge` / `tlsnTranscriptFormat` (`tlsn-transcript-policy@1`): the spans are
non-empty, of admitted classes, with 32-byte commitments, aligned with the template's slots; the
slots are confined; the skeleton is a JSON document; the policy automaton accepts the skeleton's
tokens; and the certificate's root is the span tree over the commitments. Empty spans and an
inadmissible class refute the claim under every certificate.

Not here: transcripts that are not JSON documents (an HTTP head is handled in
`DecoAndCallTree`); the notary's signature over the spans.
-/
public import Lean.Data.Json
public import Obend.Judge.Class
public import Obend.Judge.AutomataConfinement
public import Obend.Judge.VpaComplementAndJson
public import Obend.Core.Data
import all Obend.Codec.DetCbor
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Judge.VpaComplementAndJson

public section

namespace Obend.Judge

open Lean (Json toJson)
open Obend.Judge.Commit (cshakeHasher hexOf unhex)

set_option autoImplicit false

/-! ## 1. Attested spans and byte classes -/

/-- An attested redacted span: its offset and length in the transcript, the 32-byte commitment to
the hidden bytes (their span-leaf digest), and the attested byte class. -/
structure RedactedSpan where
  offset : Nat
  length : Nat
  commitment : ByteArray
  byteClassMask : Nat
  deriving DecidableEq

/-- Bit 1 of a class admits the string-safe bytes; bit 0 admits every other byte (the quote, the
backslash, control bytes, bytes above `0x7e`). -/
def byteMatchesMask (mask : Nat) (b : UInt8) : Bool :=
  if VpaJson.isSafeMaskByte b then (mask / 2) % 2 == 1 else mask % 2 == 1

/-- The class admits string-safe bytes and nothing else. -/
def maskExcludesDelimiters (mask : Nat) : Bool := mask % 2 == 0 && (mask / 2) % 2 == 1

/-- A byte of an admitted class is string-safe. -/
theorem safe_of_matches_safe_mask {mask : Nat} {b : UInt8}
    (hm : maskExcludesDelimiters mask = true) (hb : byteMatchesMask mask b = true) :
    VpaJson.isSafeMaskByte b = true := by
  unfold byteMatchesMask at hb
  cases hs : VpaJson.isSafeMaskByte b
  · rw [hs] at hb
    simp only [maskExcludesDelimiters, Bool.and_eq_true, beq_iff_eq] at hm
    simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hb
    rw [hm.1] at hb
    cases hb
  · rfl

/-! ## 2. The confinement core, and templates on the machine -/

/-- **The confinement core** at a machine state: the state is in a value string outside any
escape, the hidden span walks inside that string back to the state, and the mask is string-safe. -/
def spanConfined (st : VpaJson.JState) (span mask : List UInt8) : Bool :=
  decide (st.mode = .str false .normal) && decide (VpaJson.walkInterior st span = some st) &&
    mask.all VpaJson.isSafeMaskByte

/-- `checkJsonRedaction` is the core at the state the document reaches at the span's start. -/
theorem checkJsonRedaction_eq_spanConfined (doc : ByteArray) (l r : Nat) (mask : ByteArray) :
    VpaJson.checkJsonRedaction doc l r mask = (decide (l ≤ r) && decide (r ≤ doc.size) &&
      spanConfined (VpaJson.jsonStateAt doc l) ((doc.data.toList.drop l).take (r - l))
        mask.data.toList) := by
  simp only [VpaJson.checkJsonRedaction, spanConfined, Bool.and_assoc]

/-- A confined span and its mask both leave the machine where it was. -/
theorem spanConfined_run {st : VpaJson.JState} {span mask : List UInt8}
    (h : spanConfined st span mask = true) :
    VpaJson.specRunJson span st = st ∧ VpaJson.specRunJson mask st = st := by
  simp only [spanConfined, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨VpaJson.walkInterior_run _ _ _ h.1.2, VpaJson.specRunJson_safe h.1.1 _ h.2⟩

/-- The bytes of a literal segment. -/
def litBytes (ts : List String) : List UInt8 := ts.flatMap fun t => t.toByteArray.data.toList

/-- The public placeholder of a hidden span: `*` repeated. -/
def placeholder (len : Nat) : List UInt8 := List.replicate len 0x2a

/-- The transcript a template renders to when its slots are filled in order. -/
def renderWith : List Seg → List (List UInt8) → List UInt8
  | [], _ => []
  | .lit ts :: rest, fills => litBytes ts ++ renderWith rest fills
  | .slot _ :: rest, [] => renderWith rest []
  | .slot _ :: rest, f :: fills => f ++ renderWith rest fills

/-- The public skeleton: every slot holds its span's placeholder. -/
def renderRedactedSkeleton (segs : List Seg) (spans : List RedactedSpan) : List UInt8 :=
  renderWith segs (spans.map fun sp => placeholder sp.length)

/-- The machine over the literals alone; a slot leaves it where it is. -/
def skeletonRun : VpaJson.JState → List Seg → VpaJson.JState
  | st, [] => st
  | st, .lit ts :: rest => skeletonRun (VpaJson.specRunJson (litBytes ts) st) rest
  | st, .slot _ :: rest => skeletonRun st rest

/-- **Every slot sits in a value string outside any escape.** -/
def slotsConfined : VpaJson.JState → List Seg → Bool
  | _, [] => true
  | st, .lit ts :: rest => slotsConfined (VpaJson.specRunJson (litBytes ts) st) rest
  | st, .slot _ :: rest => decide (st.mode = .str false .normal) && slotsConfined st rest

/-- Semantic template confinement: every slot appears at a machine state inside a plain value string. -/
inductive SlotsInValueString : VpaJson.JState → List Seg → Prop
  | nil (st) : SlotsInValueString st []
  | lit {st ts rest} : SlotsInValueString (VpaJson.specRunJson (litBytes ts) st) rest →
      SlotsInValueString st (.lit ts :: rest)
  | slot {st name rest} : st.mode = .str false .normal → SlotsInValueString st rest →
      SlotsInValueString st (.slot name :: rest)

theorem SlotsInValueString.checked {st : VpaJson.JState} {segs : List Seg}
    (h : SlotsInValueString st segs) : slotsConfined st segs = true := by
  induction h with
  | nil => rfl
  | lit _ ih => exact ih
  | slot hm _ ih => simp [slotsConfined, hm, ih]

/-- **Selective-disclosure confinement.** When every slot is confined, every string-safe filling
of the slots drives the machine exactly as the literals alone do: what is hidden reaches nothing
the grammar reads. -/
theorem selective_disclosure_redaction_confinement (segs : List Seg) :
    ∀ (fills : List (List UInt8)) (st : VpaJson.JState), slotsConfined st segs = true →
      (∀ f ∈ fills, f.all VpaJson.isSafeMaskByte = true) →
      VpaJson.specRunJson (renderWith segs fills) st = skeletonRun st segs := by
  induction segs with
  | nil => intro fills st _ _; rfl
  | cons seg rest ih =>
    intro fills st hc hf
    cases seg with
    | lit ts =>
      simp only [renderWith, skeletonRun, VpaJson.specRunJson_append]
      exact ih fills _ hc hf
    | slot n =>
      simp only [slotsConfined, Bool.and_eq_true, decide_eq_true_eq] at hc
      cases fills with
      | nil =>
        simp only [renderWith, skeletonRun]
        exact ih [] st hc.2 hf
      | cons f fills =>
        simp only [renderWith, skeletonRun, VpaJson.specRunJson_append]
        rw [VpaJson.specRunJson_safe hc.1 f (hf f List.mem_cons_self)]
        exact ih fills st hc.2 fun g hg => hf g (List.mem_cons_of_mem _ hg)

/-- The filled transcript, as a document, ends in the skeleton's machine state: it has the
skeleton's grammar verdict and object key sets. -/
theorem tlsn_filled_document (segs : List Seg) (fills : List (List UInt8))
    (hc : slotsConfined VpaJson.JState.init segs = true)
    (hf : ∀ f ∈ fills, f.all VpaJson.isSafeMaskByte = true) :
    VpaJson.jsonRun ⟨(renderWith segs fills).toArray⟩ = skeletonRun VpaJson.JState.init segs := by
  rw [VpaJson.jsonRun_eq]
  exact selective_disclosure_redaction_confinement segs fills _ hc hf

/-- The public token stream of a template: its literal tokens, and `*` for a slot. -/
def skeletonTokens : List Seg → List String
  | [] => []
  | .lit ts :: rest => ts ++ skeletonTokens rest
  | .slot _ :: rest => "*" :: skeletonTokens rest

/-- The spans are the template's slots, in order, at their byte offsets in the skeleton. -/
def spansAligned : Nat → List Seg → List RedactedSpan → Bool
  | _, [], spans => spans.isEmpty
  | off, .lit ts :: rest, spans => spansAligned (off + (litBytes ts).length) rest spans
  | _, .slot _ :: _, [] => false
  | off, .slot _ :: rest, sp :: spans =>
    decide (sp.offset = off) && spansAligned (off + sp.length) rest spans

/-! ## 3. The judge and the format `tlsn-transcript-policy@1` -/

structure TlsnTranscriptQuery where
  segs : List Seg
  spans : List RedactedSpan
  policyDfa : TableDfa
  deriving DecidableEq

/-- The certificate: the slot count and the span tree over the spans' commitments. -/
structure TlsnTranscriptCert where
  slotCount : Nat
  spanRoot : VpaJson.SpanRoot
  deriving DecidableEq

inductive TlsnTranscriptRefusal where
  | emptySpans
  | spanMaskAllowsDelimiter
  | narrowCommitment
  | slotCountMismatch
  | spanMisaligned
  | slotOutsideValueString
  | skeletonNotJson
  | policyDfaRejectedSkeleton
  | spanRootMismatch
  deriving DecidableEq, Repr

def spanCommitments (q : TlsnTranscriptQuery) : List ByteArray := q.spans.map (·.commitment)

/-- The span tree over a query's commitments, at cSHAKE256. -/
def tlsnSpanRoot (q : TlsnTranscriptQuery) : VpaJson.SpanRoot :=
  VpaJson.spanMerkleRoot cshakeHasher VpaJson.spanTag (spanCommitments q)

def verifyTlsnTranscriptPolicy (q : TlsnTranscriptQuery) (c : TlsnTranscriptCert) :
    Judge.Verdict TlsnTranscriptRefusal :=
  if q.spans.isEmpty then .refused .emptySpans []
  else if q.spans.all (fun sp => maskExcludesDelimiters sp.byteClassMask) = false then
    .refused .spanMaskAllowsDelimiter []
  else if q.spans.all (fun sp => sp.commitment.size == 32) = false then
    .refused .narrowCommitment []
  else if c.slotCount ≠ q.spans.length then .refused .slotCountMismatch []
  else if spansAligned 0 q.segs q.spans = false then .refused .spanMisaligned []
  else if slotsConfined VpaJson.JState.init q.segs = false then .refused .slotOutsideValueString []
  else if VpaJson.jsonAccepting (skeletonRun VpaJson.JState.init q.segs) = false then
    .refused .skeletonNotJson []
  else if dfaAccepts q.policyDfa (skeletonTokens q.segs) = false then
    .refused .policyDfaRejectedSkeleton []
  else if c.spanRoot ≠ tlsnSpanRoot q then .refused .spanRootMismatch []
  else .ok

/-- What an accepted certificate establishes. `confined` is the semantic clause: every
string-safe filling of the hidden spans is a JSON document with the skeleton's object keys. -/
structure TlsnTranscriptMeaning (q : TlsnTranscriptQuery) (c : TlsnTranscriptCert) : Prop where
  nonempty : q.spans ≠ []
  classes : ∀ sp ∈ q.spans, maskExcludesDelimiters sp.byteClassMask = true
  wide : ∀ sp ∈ q.spans, sp.commitment.size = 32
  count : c.slotCount = q.spans.length
  aligned : spansAligned 0 q.segs q.spans = true
  confined : ∀ fills : List (List UInt8), (∀ f ∈ fills, f.all VpaJson.isSafeMaskByte = true) →
    VpaJson.runFullJsonGrammar ⟨(renderWith q.segs fills).toArray⟩ = true ∧
      VpaJson.jsonObjectKeys ⟨(renderWith q.segs fills).toArray⟩ =
        (skeletonRun VpaJson.JState.init q.segs).closed
  policy : dfaAccepts q.policyDfa (skeletonTokens q.segs) = true
  committed : c.spanRoot = tlsnSpanRoot q

/-- The checks an acceptance passed. -/
theorem verifyTlsnTranscriptPolicy_iff (q : TlsnTranscriptQuery) (c : TlsnTranscriptCert) :
    verifyTlsnTranscriptPolicy q c = .ok ↔
      q.spans.isEmpty = false ∧
        q.spans.all (fun sp => maskExcludesDelimiters sp.byteClassMask) = true ∧
        q.spans.all (fun sp => sp.commitment.size == 32) = true ∧ c.slotCount = q.spans.length ∧
        spansAligned 0 q.segs q.spans = true ∧ slotsConfined VpaJson.JState.init q.segs = true ∧
        VpaJson.jsonAccepting (skeletonRun VpaJson.JState.init q.segs) = true ∧
        dfaAccepts q.policyDfa (skeletonTokens q.segs) = true ∧ c.spanRoot = tlsnSpanRoot q := by
  unfold verifyTlsnTranscriptPolicy
  repeat' split
  all_goals first
    | (simp_all; done)
    | (simp_all
       intro hall
       rename_i hex
       obtain ⟨x, hx, hf⟩ := hex
       have h' := hall x hx
       simp_all)

theorem tlsnTranscriptPolicy_sound {q : TlsnTranscriptQuery} {c : TlsnTranscriptCert} :
    verifyTlsnTranscriptPolicy q c = .ok → TlsnTranscriptMeaning q c := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := (verifyTlsnTranscriptPolicy_iff q c).1 h
  refine ⟨fun he => ?_, List.all_eq_true.1 h2, fun sp hsp => ?_, h4, h5, fun fills hf => ?_, h8, h9⟩
  · rw [he] at h1; cases h1
  · simpa using List.all_eq_true.1 h3 sp hsp
  · have hr := tlsn_filled_document q.segs fills h6 hf
    exact ⟨by unfold VpaJson.runFullJsonGrammar; rw [hr]; exact h7,
      by unfold VpaJson.jsonObjectKeys; rw [hr]⟩

/-- Every admitted byte class excludes quotes, backslashes, controls and non-ASCII bytes. -/
theorem verifyTlsnTranscriptPolicy_masks_safe {q : TlsnTranscriptQuery} {c : TlsnTranscriptCert}
    (h : verifyTlsnTranscriptPolicy q c = .ok) :
    c.slotCount = q.spans.length ∧
    ∀ sp ∈ q.spans, ∀ b, byteMatchesMask sp.byteClassMask b = true →
      VpaJson.isSafeMaskByte b = true := by
  refine ⟨(tlsnTranscriptPolicy_sound h).count, ?_⟩
  intro sp hs b hb
  exact safe_of_matches_safe_mask (tlsnTranscriptPolicy_sound h |>.classes sp hs) hb

/-- A span tree commitment to the eight hidden bytes of the sample query. -/
def validTlsnCommitment : ByteArray :=
  VpaJson.leafHash cshakeHasher VpaJson.spanTag "hunter2!".toByteArray

/-- Canonical valid query: `{"role":"user","secret":"` · slot · `"}`. -/
def validTlsnQuery : TlsnTranscriptQuery where
  segs := [.lit ["{\"role\":\"user\",\"secret\":\""], .slot "secret", .lit ["\"}"]]
  spans := [{ offset := 25, length := 8, commitment := validTlsnCommitment, byteClassMask := 2 }]
  policyDfa := {
    start := 0
    accepting := [0]
    transitions := []
    stateDefaults := [(0, 0)]
    defaultSink := 0
  }

def validTlsnCert : TlsnTranscriptCert := ⟨1, tlsnSpanRoot validTlsnQuery⟩

/-- **The sample is accepted**: the checker's premise is inhabited. -/
theorem validTlsn_accepted : verifyTlsnTranscriptPolicy validTlsnQuery validTlsnCert = .ok := by
  have hrun : skeletonRun VpaJson.JState.init validTlsnQuery.segs =
      VpaJson.specRunJson (litBytes ["\"}"])
        (VpaJson.specRunJson (litBytes ["{\"role\":\"user\",\"secret\":\""]) VpaJson.JState.init) :=
    rfl
  refine (verifyTlsnTranscriptPolicy_iff _ _).2 ⟨rfl, by decide +kernel, ?_, rfl, by decide +kernel,
    by decide +kernel, by rw [hrun]; decide +kernel, by decide +kernel, rfl⟩
  have hs : validTlsnCommitment.size = 32 := cshakeHasher.size_eq _ _
  show (validTlsnCommitment.size == 32 && true) = true
  rw [hs]
  rfl

/-- The planted bad query: a class that admits the quote and the backslash. -/
def badTlsnQuery : TlsnTranscriptQuery :=
  { validTlsnQuery with
    spans := [{ offset := 25, length := 8, commitment := validTlsnCommitment, byteClassMask := 3 }] }

def badTlsnCert : TlsnTranscriptCert := validTlsnCert

theorem badTlsn_refused :
    verifyTlsnTranscriptPolicy badTlsnQuery badTlsnCert = .refused .spanMaskAllowsDelimiter [] := by
  have h1 : badTlsnQuery.spans.isEmpty = false := rfl
  have h2 : badTlsnQuery.spans.all (fun sp => maskExcludesDelimiters sp.byteClassMask) = false := by
    decide +kernel
  unfold verifyTlsnTranscriptPolicy
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

/-- **The transcript policy judge.** Empty spans and an inadmissible byte class refute the claim
under every certificate; completeness is claimed on the templates whose slots are confined. -/
instance tlsnTranscriptJudge : Judge TlsnTranscriptQuery TlsnTranscriptCert where
  Clause := TlsnTranscriptRefusal
  Meaning := TlsnTranscriptMeaning
  check _ q c := verifyTlsnTranscriptPolicy q c
  sound := by intro _ _ _ h; exact tlsnTranscriptPolicy_sound h
  refutes
    | .emptySpans => true
    | .spanMaskAllowsDelimiter => true
    | _ => false
  refuted := by
    intro _ q c k p h hk c' hm
    unfold verifyTlsnTranscriptPolicy at h
    split at h
    · rename_i he
      exact hm.nonempty (List.isEmpty_iff.1 he)
    · split at h
      · rename_i hmask
        rw [List.all_eq_true.2 hm.classes] at hmask
        cases hmask
      · repeat' split at h
        all_goals cases h <;> cases hk
  Fragment q := SlotsInValueString VpaJson.JState.init q.segs
  complete := by
    rintro q hfrag ⟨c, hm⟩
    have hc := hfrag.checked
    refine ⟨c, 0, (verifyTlsnTranscriptPolicy_iff q c).2 ⟨?_, List.all_eq_true.2 hm.classes,
      List.all_eq_true.2 fun sp hsp => by simpa using hm.wide sp hsp, hm.count, hm.aligned, hc,
      ?_, hm.policy, hm.committed⟩⟩
    · cases hs : q.spans with
      | nil => exact absurd hs hm.nonempty
      | cons _ _ => rfl
    · have hr := tlsn_filled_document q.segs [] hc (fun _ h => by cases h)
      have hv := (hm.confined [] (fun _ h => by cases h)).1
      unfold VpaJson.runFullJsonGrammar at hv
      rw [hr] at hv
      exact hv
  mono := by intro _ _ _ _ _ _; rfl

def segToJson : Seg → Json
  | .lit ts => Json.mkObj [("lit", Json.arr (ts.map Json.str).toArray)]
  | .slot name => Json.mkObj [("slot", Json.str name)]

def segOfJson (j : Json) : Except String Seg := do
  match j.getObjVal? "lit" with
  | .ok arrJ =>
    let ts ← (← arrJ.getArr?).toList.mapM (·.getStr?)
    pure (.lit ts)
  | .error _ =>
    let name ← j.getObjValAs? String "slot"
    pure (.slot name)

/-- A span on the wire; the commitment is lowercase hex. -/
def redactedSpanToJson (sp : RedactedSpan) : Json :=
  Json.mkObj
    [ ("offset", toJson sp.offset)
    , ("length", toJson sp.length)
    , ("commitment", Json.str (hexOf sp.commitment))
    , ("byteClassMask", toJson sp.byteClassMask) ]

def redactedSpanOfJson (j : Json) : Except String RedactedSpan := do
  let offset ← j.getObjValAs? Nat "offset"
  let length ← j.getObjValAs? Nat "length"
  let commitment ← unhex (← j.getObjValAs? String "commitment")
  let byteClassMask ← j.getObjValAs? Nat "byteClassMask"
  pure { offset, length, commitment, byteClassMask }

def encodeTlsnObj (q : TlsnTranscriptQuery) : String :=
  Json.compress <| Json.mkObj
    [ ("segs", Json.arr (q.segs.map segToJson).toArray)
    , ("spans", Json.arr (q.spans.map redactedSpanToJson).toArray)
    , ("policyDfa", tableDfaToJson q.policyDfa) ]

def decodeTlsnObj (s : String) : Except String TlsnTranscriptQuery := do
  let j ← Json.parse s
  let segs ← (← (← j.getObjVal? "segs").getArr?).toList.mapM segOfJson
  let spans ← (← (← j.getObjVal? "spans").getArr?).toList.mapM redactedSpanOfJson
  let policyDfa ← tableDfaOfJson (← j.getObjVal? "policyDfa")
  pure { segs, spans, policyDfa }

def encodeTlsnCert (c : TlsnTranscriptCert) : String :=
  Json.compress <| Json.mkObj
    [ ("slotCount", toJson c.slotCount)
    , ("spanCount", toJson c.spanRoot.count)
    , ("spanTop", Json.str (hexOf c.spanRoot.top)) ]

def decodeTlsnCert (s : String) : Except String TlsnTranscriptCert := do
  let j ← Json.parse s
  let slotCount ← j.getObjValAs? Nat "slotCount"
  let count ← j.getObjValAs? Nat "spanCount"
  let top ← unhex (← j.getObjValAs? String "spanTop")
  pure ⟨slotCount, ⟨count, top⟩⟩

/-- **The registered format** `tlsn-transcript-policy@1`. The span root is cSHAKE256, which runs
compiled. -/
@[expose] def tlsnTranscriptFormat : Judge.Format where
  name := "tlsn-transcript-policy"
  version := "1"
  Obj := TlsnTranscriptQuery
  Cert := TlsnTranscriptCert
  judge := tlsnTranscriptJudge
  decodeObj := decodeTlsnObj
  decodeCert := decodeTlsnCert
  trust := .compiled
  regime := .decidable
  bad := (badTlsnQuery, badTlsnCert)
  badGrade := 0
  bad_refused := ⟨.spanMaskAllowsDelimiter, [], badTlsn_refused⟩

end Obend.Judge
end
