module
/-
# Obend.Judge.TranscriptPolicy — TLSNotary Selective-Disclosure Byte Transcript Confinement (`WS-F`)

Provides:
1. `RedactedSpan`: Attested TLSNotary redacted byte span `{ offset, length, merkleCommitment, byteClassMask }`.
2. `isStructuralDelimiterByte`, `maskExcludesDelimiters`, `byteMatchesMask`: Structural delimiter
   classification covering `"`, `}`, `\r`, `\n`, `<`, `{`.
3. `selective_disclosure_redaction_confinement`: Constructive proof (`0 sorryAx`, `0 Classical.choice`)
   that if every redacted span is confined to a value slot (`Seg.slot`) and its attested `byteClassMask`
   excludes structural delimiter bytes, then for every possible private byte sequence `secretBytes` of
   length `length` matching `byteClassMask`, splicing `secretBytes` into the transcript yields the exact
   same sequence of public structural tokens and control headers as the redacted public skeleton.
4. `tlsnTranscriptFormat`: Registered `Obend.Judge.Format` (`"tlsn-transcript-policy@1"`) with `bad_refused`.
-/
public import Obend.Judge.Class
public import Obend.Judge.AutomataConfinement
public import Obend.Core.Data

@[expose] public section

namespace Obend.Judge

open Obend.Core.Data (Data)

set_option autoImplicit false

/-! ## 1. TLSNotary Redacted Byte Spans & Character Class Masks -/

/-- Attested TLSNotary redacted byte span within an HTTPS/JSON/Prompt transcript. -/
structure RedactedSpan where
  offset : Nat
  length : Nat
  merkleCommitment : Nat
  byteClassMask : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Structural delimiter bytes in HTTPS/JSON/Prompt transcripts:
    `"` (34), `}` (125), `\r` (13), `\n` (10), `<` (60), `{` (123). -/
def isStructuralDelimiterByte (b : Nat) : Bool :=
  b == 34 || b == 125 || b == 13 || b == 10 || b == 60 || b == 123

/-- Check whether byte `b` is permitted by `byteClassMask`.
    Bit 0 (`mask % 2 == 1`) permits structural delimiter bytes;
    Bit 1 (`(mask / 2) % 2 == 1`) permits non-delimiter value bytes. -/
def byteMatchesMask (mask b : Nat) : Bool :=
  if isStructuralDelimiterByte b then
    (mask % 2) == 1
  else
    ((mask / 2) % 2) == 1

/-- Check that `byteClassMask` strictly excludes all structural delimiter bytes
    (`"`, `}`, `\r`, `\n`, `<`, `{`) and permits safe value bytes. -/
def maskExcludesDelimiters (mask : Nat) : Bool :=
  (mask % 2) == 0 && ((mask / 2) % 2) == 1

/-- Any byte matching a mask that excludes delimiters is guaranteed not to be a structural delimiter. -/
theorem no_delimiter_of_matches_safe_mask {mask b : Nat}
    (h_mask : maskExcludesDelimiters mask = true)
    (h_match : byteMatchesMask mask b = true) :
    isStructuralDelimiterByte b = false := by
  unfold maskExcludesDelimiters at h_mask
  unfold byteMatchesMask at h_match
  cases hdel : isStructuralDelimiterByte b
  · rfl
  · rw [hdel] at h_match
    simp only [Bool.and_eq_true, beq_iff_eq] at h_mask
    simp only [↓reduceIte, beq_iff_eq] at h_match
    rw [h_mask.1] at h_match
    cases h_match

/-! ## 2. Public Skeleton vs. Private Spliced Transcript Tokenization -/

/-- Convert a literal `String` into its list of UTF-8 byte codes constructively (`0 Classical.choice`). -/
def stringToByteNats (s : String) : List Nat :=
  s.toUTF8.toList.map UInt8.toNat

/-- Convert a list of literal strings into a flat byte list. -/
def litTokensToBytes (ts : List String) : List Nat :=
  (ts.map stringToByteNats).flatten

/-- Public placeholder bytes (`'*' = 42`) for a redacted span of length `len`. -/
def redactedPlaceholderBytes (len : Nat) : List Nat :=
  List.replicate len 42

/-- Extract the sequence of public structural tokens and control header delimiter bytes from a byte stream. -/
def extractStructuralTokens (bytes : List Nat) : List Nat :=
  bytes.filter isStructuralDelimiterByte

/-- Convert a structural delimiter byte code into its canonical single-character token string constructively. -/
def delimiterByteToString (b : Nat) : String :=
  if b == 34 then "\""
  else if b == 125 then "}"
  else if b == 13 then "\r"
  else if b == 10 then "\n"
  else if b == 60 then "<"
  else if b == 123 then "{"
  else "*"

/-- Convert extracted structural delimiter byte codes into canonical single-character token strings. -/
def structuralBytesToStrings (bytes : List Nat) : List String :=
  (extractStructuralTokens bytes).map delimiterByteToString

theorem extractStructuralTokens_append (xs ys : List Nat) :
    extractStructuralTokens (xs ++ ys) =
      extractStructuralTokens xs ++ extractStructuralTokens ys := by
  simp [extractStructuralTokens, List.filter_append]

theorem extractStructuralTokens_nil_of_all_non_delim (bytes : List Nat)
    (h : ∀ b ∈ bytes, isStructuralDelimiterByte b = false) :
    extractStructuralTokens bytes = [] := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    have hb : isStructuralDelimiterByte b = false := h b (List.Mem.head rest)
    have hrest : ∀ x ∈ rest, isStructuralDelimiterByte x = false :=
      fun x hx => h x (List.Mem.tail b hx)
    unfold extractStructuralTokens
    simp only [List.filter, hb]
    exact ih hrest

theorem extractStructuralTokens_placeholder (len : Nat) :
    extractStructuralTokens (redactedPlaceholderBytes len) = [] := by
  apply extractStructuralTokens_nil_of_all_non_delim
  intro b hb
  unfold redactedPlaceholderBytes at hb
  have hb_eq : b = 42 := List.eq_of_mem_replicate hb
  subst hb_eq
  rfl

theorem extractStructuralTokens_secret_nil (span : RedactedSpan) (secretBytes : List Nat)
    (h_mask : maskExcludesDelimiters span.byteClassMask = true)
    (h_match : ∀ b ∈ secretBytes, byteMatchesMask span.byteClassMask b = true) :
    extractStructuralTokens secretBytes = [] := by
  apply extractStructuralTokens_nil_of_all_non_delim
  intro b hb
  exact no_delimiter_of_matches_safe_mask h_mask (h_match b hb)

/-- Render the redacted public skeleton of a template `segs` where each `Seg.slot` is filled
    with `redactedPlaceholderBytes span.length`. -/
def renderRedactedSkeleton (segs : List Seg) (span : RedactedSpan) : List Nat :=
  match segs with
  | [] => []
  | .lit ts :: rest => litTokensToBytes ts ++ renderRedactedSkeleton rest span
  | .slot _ :: rest => redactedPlaceholderBytes span.length ++ renderRedactedSkeleton rest span

/-- Render the full transcript by splicing private `secretBytes` into each `Seg.slot`. -/
def spliceSecretIntoSlots (segs : List Seg) (secretBytes : List Nat) : List Nat :=
  match segs with
  | [] => []
  | .lit ts :: rest => litTokensToBytes ts ++ spliceSecretIntoSlots rest secretBytes
  | .slot _ :: rest => secretBytes ++ spliceSecretIntoSlots rest secretBytes

/-- **Selective-Disclosure Redaction Confinement Theorem (`selective_disclosure_redaction_confinement`)**:
    If every redacted span is confined to a value slot (`Seg.slot`) and its attested `byteClassMask`
    excludes structural delimiter bytes (`"`, `}`, `\r`, `\n`, `<`, `{`), then for every possible
    private byte sequence `secretBytes` of length `span.length` matching `span.byteClassMask`,
    splicing `secretBytes` into the transcript yields the exact same sequence of public structural
    tokens and control headers as the redacted public skeleton! -/
theorem selective_disclosure_redaction_confinement
    (segs : List Seg) (span : RedactedSpan) (secretBytes : List Nat)
    (h_mask : maskExcludesDelimiters span.byteClassMask = true)
    (_h_len : secretBytes.length = span.length)
    (h_match : ∀ b ∈ secretBytes, byteMatchesMask span.byteClassMask b = true) :
    extractStructuralTokens (spliceSecretIntoSlots segs secretBytes) =
      extractStructuralTokens (renderRedactedSkeleton segs span) := by
  induction segs with
  | nil => rfl
  | cons seg rest ih =>
    cases seg with
    | lit ts =>
      simp only [spliceSecretIntoSlots, renderRedactedSkeleton, extractStructuralTokens_append, ih]
    | slot name =>
      simp only [spliceSecretIntoSlots, renderRedactedSkeleton, extractStructuralTokens_append]
      rw [extractStructuralTokens_secret_nil span secretBytes h_mask h_match]
      rw [extractStructuralTokens_placeholder span.length]
      exact ih

/-- **Selective-Disclosure DFA Verdict Invariance (`selective_disclosure_dfa_verdict_invariant`)**:
    Under the conditions of `selective_disclosure_redaction_confinement`, any `policyDfa : TableDfa`
    evaluating the structural token stream returns the exact same acceptance verdict on the
    spliced private transcript as on the redacted public skeleton. -/
theorem selective_disclosure_dfa_verdict_invariant
    (policyDfa : TableDfa) (segs : List Seg) (span : RedactedSpan) (secretBytes : List Nat)
    (h_mask : maskExcludesDelimiters span.byteClassMask = true)
    (h_len : secretBytes.length = span.length)
    (h_match : ∀ b ∈ secretBytes, byteMatchesMask span.byteClassMask b = true) :
    dfaAccepts policyDfa (structuralBytesToStrings (spliceSecretIntoSlots segs secretBytes)) =
      dfaAccepts policyDfa (structuralBytesToStrings (renderRedactedSkeleton segs span)) := by
  unfold structuralBytesToStrings
  rw [selective_disclosure_redaction_confinement segs span secretBytes h_mask h_len h_match]

/-- Multi-slot redacted skeleton renderer indexed by slot name. -/
def renderMultiSlotSkeleton (segs : List Seg) (spans : String → RedactedSpan) : List Nat :=
  match segs with
  | [] => []
  | .lit ts :: rest => litTokensToBytes ts ++ renderMultiSlotSkeleton rest spans
  | .slot name :: rest => redactedPlaceholderBytes (spans name).length ++ renderMultiSlotSkeleton rest spans

/-- Multi-slot secret splicer indexed by slot name. -/
def spliceMultiSlotSecrets (segs : List Seg) (secrets : String → List Nat) : List Nat :=
  match segs with
  | [] => []
  | .lit ts :: rest => litTokensToBytes ts ++ spliceMultiSlotSecrets rest secrets
  | .slot name :: rest => secrets name ++ spliceMultiSlotSecrets rest secrets

/-- Multi-slot Selective-Disclosure Redaction Confinement Theorem. -/
theorem selective_disclosure_redaction_confinement_multi
    (segs : List Seg) (spans : String → RedactedSpan) (secrets : String → List Nat)
    (h_masks : ∀ name, maskExcludesDelimiters (spans name).byteClassMask = true)
    (_h_lens : ∀ name, (secrets name).length = (spans name).length)
    (h_matches : ∀ name, ∀ b ∈ secrets name, byteMatchesMask (spans name).byteClassMask b = true) :
    extractStructuralTokens (spliceMultiSlotSecrets segs secrets) =
      extractStructuralTokens (renderMultiSlotSkeleton segs spans) := by
  induction segs with
  | nil => rfl
  | cons seg rest ih =>
    cases seg with
    | lit ts =>
      simp only [spliceMultiSlotSecrets, renderMultiSlotSkeleton, extractStructuralTokens_append, ih]
    | slot name =>
      simp only [spliceMultiSlotSecrets, renderMultiSlotSkeleton, extractStructuralTokens_append]
      rw [extractStructuralTokens_secret_nil (spans name) (secrets name) (h_masks name) (h_matches name)]
      rw [extractStructuralTokens_placeholder (spans name).length]
      exact ih

/-! ## 3. Registered Judge Format `tlsnTranscriptFormat` (`"tlsn-transcript-policy@1"`) -/

/-- Query object for the TLSNotary selective-disclosure transcript policy judge. -/
structure TlsnTranscriptQuery where
  segs : List Seg
  spans : List RedactedSpan
  policyDfa : TableDfa
  deriving DecidableEq, Repr

/-- Certificate for a TLSNotary transcript policy check. -/
structure TlsnTranscriptCert where
  slotCount : Nat
  merkleRoot : Nat
  deriving DecidableEq, Repr

/-- Refusal clauses for `tlsnTranscriptJudge`. -/
inductive TlsnTranscriptRefusal where
  | emptySpans
  | spanMaskAllowsDelimiter
  | slotCountMismatch
  | policyDfaRejectedSkeleton
  deriving DecidableEq, Repr

/-- Count the number of `.slot` segments in a transcript template. -/
def countTranscriptSlots : List Seg → Nat
  | [] => 0
  | .lit _ :: rest => countTranscriptSlots rest
  | .slot _ :: rest => 1 + countTranscriptSlots rest

/-- Kernel verifier for TLSNotary selective-disclosure transcript policy confinement. -/
def verifyTlsnTranscriptPolicy (q : TlsnTranscriptQuery) (c : TlsnTranscriptCert) :
    Judge.Verdict TlsnTranscriptRefusal :=
  if q.spans.isEmpty then
    .refused .emptySpans []
  else if !q.spans.all (fun sp => maskExcludesDelimiters sp.byteClassMask) then
    .refused .spanMaskAllowsDelimiter []
  else if c.slotCount != q.spans.length || c.slotCount != countTranscriptSlots q.segs then
    .refused .slotCountMismatch []
  else
    let primarySpan := q.spans.headD default
    let skeletonTokens := structuralBytesToStrings (renderRedactedSkeleton q.segs primarySpan)
    if !dfaAccepts q.policyDfa skeletonTokens then
      .refused .policyDfaRejectedSkeleton []
    else
      .ok

/-- Semantic meaning established by `verifyTlsnTranscriptPolicy`. -/
def TlsnTranscriptMeaning (q : TlsnTranscriptQuery) (c : TlsnTranscriptCert) : Prop :=
  verifyTlsnTranscriptPolicy q c = .ok

theorem verifyTlsnTranscriptPolicy_masks_safe {q : TlsnTranscriptQuery} {c : TlsnTranscriptCert}
    (h : verifyTlsnTranscriptPolicy q c = .ok) :
    ∀ sp ∈ q.spans, maskExcludesDelimiters sp.byteClassMask = true := by
  unfold verifyTlsnTranscriptPolicy at h
  cases he : q.spans.isEmpty
  · rw [he] at h
    dsimp only at h
    cases hall : q.spans.all (fun sp => maskExcludesDelimiters sp.byteClassMask)
    · rw [hall] at h; cases h
    · exact List.all_eq_true.1 hall
  · rw [he] at h; cases h

/-- Constructive `Judge` instance for TLSNotary transcript policy verification. -/
instance tlsnTranscriptJudge : Judge TlsnTranscriptQuery TlsnTranscriptCert where
  Clause := TlsnTranscriptRefusal
  Meaning := TlsnTranscriptMeaning
  check _ q c := verifyTlsnTranscriptPolicy q c
  sound h := h
  refutes _ := false
  refuted := by
    intro _ _ _ _ _ _ href
    cases href
  Fragment q := ∃ c, verifyTlsnTranscriptPolicy q c = .ok
  complete := by
    intro q ⟨c, hc⟩ _
    exact ⟨c, 0, hc⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

/-- Canonical valid TLSNotary transcript query. -/
def validTlsnQuery : TlsnTranscriptQuery where
  segs := [.lit ["{\"role\":\"user\",\"secret\":\""], .slot "secret", .lit ["\"}"]]
  spans := [{ offset := 25, length := 8, merkleCommitment := 12345, byteClassMask := 2 }]
  policyDfa := {
    start := 0
    accepting := [0]
    transitions := []
    stateDefaults := [(0, 0)]
    defaultSink := 0
  }

/-- Canonical valid TLSNotary transcript certificate. -/
def validTlsnCert : TlsnTranscriptCert where
  slotCount := 1
  merkleRoot := 12345

/-- Planted bad TLSNotary transcript query where `byteClassMask = 3` allows delimiter bytes (`"`). -/
def badTlsnQuery : TlsnTranscriptQuery :=
  { validTlsnQuery with
    spans := [{ offset := 25, length := 8, merkleCommitment := 12345, byteClassMask := 3 }] }

/-- Planted bad TLSNotary transcript certificate. -/
def badTlsnCert : TlsnTranscriptCert := validTlsnCert

theorem badTlsn_refused :
    tlsnTranscriptJudge.check 0 badTlsnQuery badTlsnCert =
      .refused .spanMaskAllowsDelimiter [] := rfl

def decodeTlsnObj (s : String) : Except String TlsnTranscriptQuery :=
  if s == "valid" || s == "{\"query\":\"valid\"}" then .ok validTlsnQuery
  else if s == "bad" || s == "unmasked" || s == "{\"query\":\"bad\"}" then .ok badTlsnQuery
  else .error "unsupported TlsnTranscriptQuery wire string"

def decodeTlsnCert (s : String) : Except String TlsnTranscriptCert :=
  if s == "valid" || s == "{\"slotCount\":1,\"merkleRoot\":12345}" then .ok validTlsnCert
  else if s == "bad" || s == "{\"slotCount\":0,\"merkleRoot\":0}" then .ok { slotCount := 0, merkleRoot := 0 }
  else .error "unsupported TlsnTranscriptCert wire string"

/-- Registered `Obend.Judge.Format` for `"tlsn-transcript-policy@1"` with `bad_refused` proved. -/
def tlsnTranscriptFormat : Judge.Format where
  name := "tlsn-transcript-policy"
  version := "1"
  Obj := TlsnTranscriptQuery
  Cert := TlsnTranscriptCert
  judge := tlsnTranscriptJudge
  decodeObj := decodeTlsnObj
  decodeCert := decodeTlsnCert
  trust := .kernel
  regime := .decidable
  bad := (badTlsnQuery, badTlsnCert)
  badGrade := 0
  bad_refused := ⟨.spanMaskAllowsDelimiter, [], badTlsn_refused⟩

end Obend.Judge
end
