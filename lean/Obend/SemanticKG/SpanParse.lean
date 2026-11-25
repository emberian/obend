module
/-
# Obend.SemanticKG.SpanParse — `VpaComplementAndJson` + `SymbolicRegexBisim` Span-Bound Fact Extraction

Stage 2 of the 4-stage Verifiable Semantic Knowledge Graph (`Obend.SemanticKG`):
1. **`SpanBoundAtom` & Zero Cross-Span Ambiguity (`bindAdv = 0` up to `CollisionAmong H` / `Collision H`)**:
   - Commits `(docId, byteStart, byteLen, sliceBytes)` via length-framed 64-bit big-endian fields under
     domain-separated cSHAKE256 (`spanSliceDomainTag`), proving `spanSlicePreimage_injective`,
     `spanSliceDigestWith_binding`, `spanSliceDigest_binding`, and `0 Classical` `PSum` extractor
     `spanSliceDigest_extract`.
2. **Stateful VPA + Derivative-Regex Grammar Extraction (`GrammarSpec`, `extractSpanBoundAtoms`)**:
   - Pairs a stateful `(inString : Bool, escaped : Bool)` structural JSON VPA lexer (`lexJsonVpaWordExec`
     refining `lexJsonVpaWordSpec`) with `VpaJson.runFullJsonGrammar`, `VpaJson.DetVpa` policy acceptance,
     $O(\log |D|)$ sorted CBOR-key entity dictionary lookup (`EntityDict`, `DetCbor.sortedSearch`),
     and `SymbolicRegex.PredRE` matching + delimiter-ban (`absenceOf`).
   - Proves **`span_parse_sound_and_unforgeable`** and **`redacted_span_parse_sound`** (when spans lie
     within disclosed intervals of a `checkRedactionDelimiterConfined` policy, extracted `SpanBoundAtom`s
     match the unredacted source verbatim).
-/
public import Obend.SemanticKG.Databank
public import Obend.Judge.VpaComplementAndJson
public import Obend.Judge.SymbolicRegexBisim
public import Obend.Core.Digest
public import Obend.Codec.DetCbor
import all Obend.SemanticKG.Databank
import all Obend.Codec.DetCbor
import all Obend.Core.Digest
import all Obend.Judge.VpaComplementAndJson
import all Obend.Judge.SymbolicRegexBisim

public section
namespace Obend.SemanticKG

open Obend.Codec.DetCbor
open Obend.Digest.HashBytes
open Obend.Core.Digest
open Obend.Judge
open Obend.Judge.SymbolicRegex

set_option autoImplicit false

/-! ## §1. `SpanBoundAtom` Carrier & Domain-Separated `sliceDigest` Binding -/

/-- Exact byte-span-bound relational fact extracted from a `DocChunkEntry`. -/
structure SpanBoundAtom where
  predSym     : UInt32
  args        : Array UInt32          -- Interned entity/literal IDs
  docId       : Nat
  byteStart   : Nat
  byteLen     : Nat
  sliceDigest : Digest256             -- Domain-separated cSHAKE256 of (docId, byteStart, byteLen, sliceBytes)
  deriving DecidableEq, Repr

/-- Domain tag `"Obend.SemanticKG.SpanSlice/v1\x00"` (30 ASCII bytes). -/
def spanSliceDomainTag : List UInt8 :=
  [0x4f, 0x62, 0x65, 0x6e, 0x64, 0x2e, 0x53, 0x65, 0x6d, 0x61, 0x6e, 0x74, 0x69, 0x63,
   0x4b, 0x47, 0x2e, 0x53, 0x70, 0x61, 0x6e, 0x53, 0x6c, 0x69, 0x63, 0x65, 0x2f, 0x76, 0x31, 0x00]

/-- Canonical 64-bit length-framed preimage binding `(docId, byteStart, byteLen, slice)`. -/
def spanSlicePreimage (docId byteStart byteLen : Nat) (slice : ByteArray) : List UInt8 :=
  spanSliceDomainTag ++
    be 8 docId ++ be 8 byteStart ++ be 8 byteLen ++ be 8 slice.size ++ slice.data.toList

/-- 64-bit width bounds ensuring zero modular wraparound in `spanSlicePreimage`. -/
def WfSpanSliceBounds (docId byteStart byteLen : Nat) (slice : ByteArray) : Bool :=
  decide (docId < 256 ^ 8) &&
  decide (byteStart < 256 ^ 8) &&
  decide (byteLen < 256 ^ 8) &&
  decide (slice.size < 256 ^ 8)

/-- Generic hash-parameterized 256-bit span-slice commitment. -/
def computeSpanSliceDigestWith (H : Hash) (docId byteStart byteLen : Nat) (slice : ByteArray) : Digest256 :=
  hashOfHashBytes256 H (spanSlicePreimage docId byteStart byteLen slice)

/-- Deployed cSHAKE256 256-bit span-slice commitment. -/
def computeSpanSliceDigest (docId byteStart byteLen : Nat) (slice : ByteArray) : Digest256 :=
  computeSpanSliceDigestWith deployed docId byteStart byteLen slice

theorem spanSlicePreimage_injective
    {d₁ s₁ l₁ d₂ s₂ l₂ : Nat} {b₁ b₂ : ByteArray}
    (h₁ : WfSpanSliceBounds d₁ s₁ l₁ b₁ = true)
    (h₂ : WfSpanSliceBounds d₂ s₂ l₂ b₂ = true)
    (hEq : spanSlicePreimage d₁ s₁ l₁ b₁ = spanSlicePreimage d₂ s₂ l₂ b₂) :
    d₁ = d₂ ∧ s₁ = s₂ ∧ l₁ = l₂ ∧ b₁ = b₂ := by
  simp only [WfSpanSliceBounds, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
  have h1 : be 8 d₁ ++ (be 8 s₁ ++ (be 8 l₁ ++ (be 8 b₁.size ++ b₁.data.toList))) =
      be 8 d₂ ++ (be 8 s₂ ++ (be 8 l₂ ++ (be 8 b₂.size ++ b₂.data.toList))) := by
    simpa only [spanSlicePreimage, List.append_assoc, List.append_cancel_left_eq] using hEq
  obtain ⟨hd, h2⟩ := List.append_inj h1 (by simp)
  obtain ⟨hs, h3⟩ := List.append_inj h2 (by simp)
  obtain ⟨hl, h4⟩ := List.append_inj h3 (by simp)
  obtain ⟨_, hb⟩ := List.append_inj h4 (by simp)
  exact ⟨be_injective h₁.1.1.1 h₂.1.1.1 hd,
         be_injective h₁.1.1.2 h₂.1.1.2 hs,
         be_injective h₁.1.2 h₂.1.2 hl,
         byteArray_eq_of_toList hb⟩

private theorem hash256_eq_ofBE_32 {H : Hash} {m₁ m₂ : List UInt8}
    (hlen₁ : (H m₁).length = 32) (hlen₂ : (H m₂).length = 32)
    (h : hashOfHashBytes256 H m₁ = hashOfHashBytes256 H m₂) : ofBE (H m₁) = ofBE (H m₂) := by
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  have ha : ofBE (H m₁) < 2 ^ 256 := by have := ofBE_lt (H m₁); rwa [hlen₁, hpow] at this
  have hb : ofBE (H m₂) < 2 ^ 256 := by have := ofBE_lt (H m₂); rwa [hlen₂, hpow] at this
  have hh := congrArg BitVec.toNat h
  simpa only [hashOfHashBytes256, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hh

/-- **Generic Hash Span-Slice Binding (`bindAdv = 0` up to `CollisionAmong H`)**:
    Equal `sliceDigest` values imply identical `(docId, byteStart, byteLen, slice)` or `CollisionAmong H`. -/
theorem spanSliceDigestWith_binding (H : Hash)
    {d₁ s₁ l₁ d₂ s₂ l₂ : Nat} {b₁ b₂ : ByteArray}
    (h₁ : WfSpanSliceBounds d₁ s₁ l₁ b₁ = true)
    (h₂ : WfSpanSliceBounds d₂ s₂ l₂ b₂ = true)
    (hlen : (H (spanSlicePreimage d₁ s₁ l₁ b₁)).length = 32 ∧
            (H (spanSlicePreimage d₂ s₂ l₂ b₂)).length = 32)
    (hEq : computeSpanSliceDigestWith H d₁ s₁ l₁ b₁ = computeSpanSliceDigestWith H d₂ s₂ l₂ b₂) :
    (d₁ = d₂ ∧ s₁ = s₂ ∧ l₁ = l₂ ∧ b₁ = b₂) ∨
      CollisionAmong H (fun m => m = spanSlicePreimage d₁ s₁ l₁ b₁ ∨ m = spanSlicePreimage d₂ s₂ l₂ b₂) := by
  if hp : spanSlicePreimage d₁ s₁ l₁ b₁ = spanSlicePreimage d₂ s₂ l₂ b₂ then
    exact .inl (spanSlicePreimage_injective h₁ h₂ hp)
  else
    exact .inr ⟨_, _, .inl rfl, .inr rfl, hp, hash256_eq_ofBE_32 hlen.1 hlen.2 hEq⟩

/-- **Deployed cSHAKE256 Span-Slice Binding**: equal `computeSpanSliceDigest` values bind `(docId, start, len, slice)`
    with zero cross-span/cross-document ambiguity up to a 2-preimage `CollisionAmong deployed`. -/
theorem spanSliceDigest_binding
    {d₁ s₁ l₁ d₂ s₂ l₂ : Nat} {b₁ b₂ : ByteArray}
    (h₁ : WfSpanSliceBounds d₁ s₁ l₁ b₁ = true)
    (h₂ : WfSpanSliceBounds d₂ s₂ l₂ b₂ = true)
    (hEq : computeSpanSliceDigest d₁ s₁ l₁ b₁ = computeSpanSliceDigest d₂ s₂ l₂ b₂) :
    (d₁ = d₂ ∧ s₁ = s₂ ∧ l₁ = l₂ ∧ b₁ = b₂) ∨
      CollisionAmong deployed
        (fun m => m = spanSlicePreimage d₁ s₁ l₁ b₁ ∨ m = spanSlicePreimage d₂ s₂ l₂ b₂) :=
  spanSliceDigestWith_binding deployed h₁ h₂ (by simp [deployed]) hEq

/-- **Constructive `0 Classical` Collision Extractor for `computeSpanSliceDigest`**. -/
def spanSliceDigest_extract
    {d₁ s₁ l₁ d₂ s₂ l₂ : Nat} {b₁ b₂ : ByteArray}
    (h₁ : WfSpanSliceBounds d₁ s₁ l₁ b₁ = true)
    (h₂ : WfSpanSliceBounds d₂ s₂ l₂ b₂ = true)
    (hEq : computeSpanSliceDigest d₁ s₁ l₁ b₁ = computeSpanSliceDigest d₂ s₂ l₂ b₂) :
    PSum (d₁ = d₂ ∧ s₁ = s₂ ∧ l₁ = l₂ ∧ b₁ = b₂)
      (ExactCollisionPair deployed (spanSlicePreimage d₁ s₁ l₁ b₁) (spanSlicePreimage d₂ s₂ l₂ b₂)) := by
  if hp : spanSlicePreimage d₁ s₁ l₁ b₁ = spanSlicePreimage d₂ s₂ l₂ b₂ then
    exact .inl (spanSlicePreimage_injective h₁ h₂ hp)
  else
    exact .inr ⟨hp, hash256_eq_ofBE_32 (by simp [deployed]) (by simp [deployed]) (by
      simpa only [computeSpanSliceDigest, computeSpanSliceDigestWith] using hEq)⟩

/-! ## §2. Stateful `(inString, escaped)` Structural JSON VPA Lexer (`Spec ↔ Exec`) -/

/-- Structural bracket sorts for visibly pushdown document framing. -/
inductive JsonBracketSort where
  | objBrace
  | arrBracket
  deriving DecidableEq, Repr

instance : VpaJson.FinEnum JsonBracketSort where
  elems := [.objBrace, .arrBracket]
  complete s := by cases s <;> simp

/-- Structural internal tokens outside string literals. -/
inductive JsonStructTok where
  | colon
  | comma
  | strDelim
  deriving DecidableEq, Repr

instance : VpaJson.FinEnum JsonStructTok where
  elems := [.colon, .comma, .strDelim]
  complete a := by cases a <;> simp

/-- Explicit string/escape lexer state preventing `\"` boundary smuggling (`obend-anti-cosplay` #8). -/
structure StrEscapeState where
  inString : Bool := false
  escaped  : Bool := false
  deriving DecidableEq, Repr

/-- Advance `(inString, escaped)` by one byte and optionally emit a structural VPA symbol. -/
def stepJsonVpaLex (st : StrEscapeState) (b : UInt8) :
    StrEscapeState × Option (VpaJson.Sym JsonBracketSort JsonStructTok) :=
  if st.inString then
    if st.escaped then
      ({ inString := true, escaped := false }, none)
    else if b == 0x5c then
      ({ inString := true, escaped := true }, none)
    else if b == 0x22 then
      ({ inString := false, escaped := false }, none)
    else
      ({ inString := true, escaped := false }, none)
  else
    if b == 0x22 then
      ({ inString := true, escaped := false }, some (.int .strDelim))
    else if b == 0x7b then
      (st, some (.call .objBrace))
    else if b == 0x7d then
      (st, some (.ret .objBrace))
    else if b == 0x5b then
      (st, some (.call .arrBracket))
    else if b == 0x5d then
      (st, some (.ret .arrBracket))
    else if b == 0x3a then
      (st, some (.int .colon))
    else if b == 0x2c then
      (st, some (.int .comma))
    else
      (st, none)

/-- `Spec` structural VPA word lexer over `List UInt8`. -/
def lexJsonVpaWordSpec (st : StrEscapeState) :
    List UInt8 → List (VpaJson.Sym JsonBracketSort JsonStructTok)
  | [] => []
  | b :: bs =>
    let (st', sym?) := stepJsonVpaLex st b
    match sym? with
    | some sym => sym :: lexJsonVpaWordSpec st' bs
    | none => lexJsonVpaWordSpec st' bs

/-- `Exec` tail-recursive structural VPA word lexer over `ByteArray`. -/
def lexJsonVpaWordGo (bs : ByteArray) (idx : Nat) (st : StrEscapeState)
    (acc : Array (VpaJson.Sym JsonBracketSort JsonStructTok)) :
    Array (VpaJson.Sym JsonBracketSort JsonStructTok) :=
  if h : idx < bs.size then
    let (st', sym?) := stepJsonVpaLex st (bs[idx]'h)
    let acc' := match sym? with | some s => acc.push s | none => acc
    lexJsonVpaWordGo bs (idx + 1) st' acc'
  else acc
termination_by bs.size - idx

def lexJsonVpaWordExec (bs : ByteArray) : Array (VpaJson.Sym JsonBracketSort JsonStructTok) :=
  lexJsonVpaWordGo bs 0 {} #[]

private theorem lexJsonVpaWordGo_eq_spec (bs : ByteArray) :
    ∀ (idx : Nat) (st : StrEscapeState) (acc : Array (VpaJson.Sym JsonBracketSort JsonStructTok)),
      (lexJsonVpaWordGo bs idx st acc).toList =
        acc.toList ++ lexJsonVpaWordSpec st (bs.data.toList.drop idx) := by
  intro idx st acc
  induction fuel : bs.size - idx using Nat.strongRecOn generalizing idx st acc with
  | ind fuel ih =>
    unfold lexJsonVpaWordGo
    by_cases h : idx < bs.size
    · rw [dite_eq_left h]
      have hl : idx < bs.data.toList.length := by rw [toList_length]; exact h
      rw [List.drop_eq_getElem_cons hl]
      have hg : bs.data.toList[idx]'hl = bs[idx]'h := rfl
      rw [hg, lexJsonVpaWordSpec]
      have ihStep := ih (bs.size - (idx + 1)) (by omega) (idx + 1) (stepJsonVpaLex st (bs[idx]'h)).1
      cases hSym : (stepJsonVpaLex st (bs[idx]'h)).2 with
      | none =>
        simpa [hSym] using ihStep acc rfl
      | some s =>
        simpa [hSym, Array.toList_push, List.append_assoc] using ihStep (acc.push s) rfl
    · rw [dite_eq_right h]
      have hNil : bs.data.toList.drop idx = [] :=
        List.drop_eq_nil_of_le (by rw [toList_length]; omega)
      simp [hNil, lexJsonVpaWordSpec]

/-- **`Spec ↔ Exec` Bridge**: `lexJsonVpaWordExec` computes `lexJsonVpaWordSpec` exactly. -/
theorem lexJsonVpaWordExec_eq_spec (bs : ByteArray) :
    (lexJsonVpaWordExec bs).toList = lexJsonVpaWordSpec {} bs.data.toList := by
  simpa [lexJsonVpaWordExec] using lexJsonVpaWordGo_eq_spec bs 0 {} #[]

/-- Stateful `(inString, escaped)` state reached at byte offset `pos` in `bs`. -/
def strEscapeStateAtGo (bs : ByteArray) (idx limit : Nat) (st : StrEscapeState) : StrEscapeState :=
  if h : idx < limit ∧ idx < bs.size then
    strEscapeStateAtGo bs (idx + 1) limit (stepJsonVpaLex st (bs[idx]'h.2)).1
  else st
termination_by limit - idx

def strEscapeStateAt (bs : ByteArray) (pos : Nat) : StrEscapeState :=
  strEscapeStateAtGo bs 0 pos {}

/-- Default permissive structural VPA accepting any well-matched bracket/token document. -/
def wellMatchedJsonVpa : VpaJson.DetVpa JsonBracketSort JsonStructTok Unit Unit where
  init := ()
  acc _ := true
  stepInt _ _ := ()
  stepCall _ _ := ((), ())
  stepRet _ _ _ := ()

/-! ## §3. Sorted Entity Dictionary, `GrammarSpec` & `extractSpanBoundAtoms` -/

/-- Sorted dictionary mapping raw UTF-8/byte entity literals to canonical `UInt32` IDs in $O(\log |D|)$. -/
structure EntityDict where
  entries : Array (ByteArray × UInt32)
  deriving DecidableEq

/-- Strict lexicographic key-order invariant (`DetCbor.lexLtBytes`) on `EntityDict`. -/
def WfEntityDict (d : EntityDict) : Bool :=
  sortedByKeyB Prod.fst d.entries.toList

/-- $O(\log |D|)$ binary-search lookup into `EntityDict`. -/
def lookupEntityId (d : EntityDict) (raw : ByteArray) : Option UInt32 :=
  (sortedSearch Prod.fst d.entries raw).map Prod.snd

theorem lookupEntityId_eq_find {d : EntityDict} (hWf : WfEntityDict d = true) (raw : ByteArray) :
    lookupEntityId d raw = (d.entries.toList.find? (fun e => decide (e.1 = raw))).map Prod.snd := by
  unfold lookupEntityId
  rw [sortedSearch_eq_find Prod.fst d.entries raw (sortedByKeyB_sound Prod.fst d.entries.toList hWf)]
  congr 1; congr 1; funext e
  by_cases h : e.1 = raw <;> simp [h]

/-- Per-predicate extraction rule pairing `predSym` and `arity` with `PredRE` pattern and delimiter ban. -/
structure SpanRuleSpec where
  predTag       : ByteArray
  predSym       : UInt32
  arity         : Nat
  slicePattern  : PredRE
  banDelimiter  : PredRE
  deriving DecidableEq

/-- Complete Stage-2 grammar & entity specification driving `extractSpanBoundAtoms`. -/
structure GrammarSpec where
  structuralVpa : VpaJson.DetVpa JsonBracketSort JsonStructTok Unit Unit := wellMatchedJsonVpa
  entityDict    : EntityDict
  rules         : Array SpanRuleSpec

/-- Explicit refusal diagnostics for `extractSpanBoundAtoms`. -/
inductive ParseRefusal where
  | invalidChunkIntegrity
  | unsortedEntityDict
  | malformedJsonGrammar
  | vpaPolicyRejected
  | spanInsideStringLiteral (byteStart : Nat)
  | spanOutOfBounds (byteStart byteLen : Nat)
  | unknownPredicateTag (byteStart : Nat)
  | arityMismatch (byteStart expected actual : Nat)
  | uninternedEntity (byteStart : Nat)
  | regexPatternMismatch (byteStart : Nat) (predSym : UInt32)
  | forbiddenDelimiterMatched (byteStart : Nat) (predSym : UInt32)
  deriving DecidableEq, Repr

/-- Stateful scanner extracting top-level / array-element `{ ... }` object spans `[start, len)`
    outside string literals, tracking `(inString, escaped, braceDepth)`. -/
def scanBalancedObjectSpansGo (bs : ByteArray) (idx : Nat) (st : StrEscapeState)
    (braceDepth : Nat) (objStart : Option Nat) (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
  if h : idx < bs.size then
    let b := bs[idx]'h
    let (st', _) := stepJsonVpaLex st b
    if st.inString then
      scanBalancedObjectSpansGo bs (idx + 1) st' braceDepth objStart acc
    else if b == 0x7b then
      if braceDepth = 0 then
        scanBalancedObjectSpansGo bs (idx + 1) st' 1 (some idx) acc
      else
        scanBalancedObjectSpansGo bs (idx + 1) st' (braceDepth + 1) objStart acc
    else if b == 0x7d then
      match braceDepth with
      | 0 => scanBalancedObjectSpansGo bs (idx + 1) st' 0 none acc
      | 1 =>
        let acc' := match objStart with
          | some s => acc.push (s, idx + 1 - s)
          | none => acc
        scanBalancedObjectSpansGo bs (idx + 1) st' 0 none acc'
      | d + 2 =>
        scanBalancedObjectSpansGo bs (idx + 1) st' (d + 1) objStart acc
    else
      scanBalancedObjectSpansGo bs (idx + 1) st' braceDepth objStart acc
  else acc
termination_by bs.size - idx

/-- Extract quoted string interiors (unescaped ASCII payloads) inside a JSON object slice `[0, slice.size)`. -/
def extractQuotedStringsGo (slice : ByteArray) (idx : Nat) (escaped : Bool)
    (strStart : Option Nat) (acc : Array ByteArray) : Array ByteArray :=
  if h : idx < slice.size then
    let b := slice[idx]'h
    match strStart with
    | none =>
      if b == 0x22 then extractQuotedStringsGo slice (idx + 1) false (some (idx + 1)) acc
      else extractQuotedStringsGo slice (idx + 1) false none acc
    | some s =>
      if escaped then
        extractQuotedStringsGo slice (idx + 1) false (some s) acc
      else if b == 0x5c then
        extractQuotedStringsGo slice (idx + 1) true (some s) acc
      else if b == 0x22 then
        extractQuotedStringsGo slice (idx + 1) false none (acc.push (slice.extract s idx))
      else
        extractQuotedStringsGo slice (idx + 1) false (some s) acc
  else acc
termination_by slice.size - idx

/-- Parse a sequence of quoted strings `[k0, v0, k1, v1, ...]` by taking value strings at odd indices `1, 3, ...`,
    where `v0` is the predicate tag and `v1, v2, ...` are the entity arguments. -/
def collectOddValuesGo (strs : Array ByteArray) (idx : Nat) (acc : Array ByteArray) : Array ByteArray :=
  if h : idx < strs.size then
    collectOddValuesGo strs (idx + 2) (acc.push (strs[idx]'h))
  else acc
termination_by strs.size - idx

/-- Resolve an array of raw entity slices via `lookupEntityId` in $O(k \log |D|)$. -/
def resolveEntityArgs (dict : EntityDict) (byteStart : Nat) (rawArgs : List ByteArray) :
    Except ParseRefusal (List UInt32) :=
  match rawArgs with
  | [] => .ok []
  | r :: rs =>
    match lookupEntityId dict r with
    | none => .error (.uninternedEntity byteStart)
    | some eid => do
      let rest ← resolveEntityArgs dict byteStart rs
      .ok (eid :: rest)

/-- Validate and materialize a single candidate `(byteStart, byteLen)` span against `GrammarSpec`. -/
def parseSingleObjectSpan (g : GrammarSpec) (doc : DocChunkEntry) (byteStart byteLen : Nat) :
    Except ParseRefusal SpanBoundAtom :=
  if !(decide (0 < byteLen) && decide (byteStart + byteLen ≤ doc.rawBytes.size)) then
    .error (.spanOutOfBounds byteStart byteLen)
  else if (strEscapeStateAt doc.rawBytes byteStart).inString then
    .error (.spanInsideStringLiteral byteStart)
  else
    let slice := doc.rawBytes.extract byteStart (byteStart + byteLen)
    let quoted := extractQuotedStringsGo slice 0 false none #[]
    let vals := collectOddValuesGo quoted 1 #[]
    if h0 : 0 < vals.size then
      let predName := vals[0]'h0
      match g.rules.toList.find? (fun r => decide (r.predTag.data.toList = predName.data.toList)) with
      | none => .error (.unknownPredicateTag byteStart)
      | some rule =>
        let rawArgs := (vals.extract 1 vals.size).toList
        if rawArgs.length != rule.arity then
          .error (.arityMismatch byteStart rule.arity rawArgs.length)
        else if !matchB slice.data.toList rule.slicePattern then
          .error (.regexPatternMismatch byteStart rule.predSym)
        else if !matchB slice.data.toList (absenceOf rule.banDelimiter) then
          .error (.forbiddenDelimiterMatched byteStart rule.predSym)
        else
          match resolveEntityArgs g.entityDict byteStart rawArgs with
          | .error err => .error err
          | .ok argList =>
            .ok {
              predSym := rule.predSym
              args := argList.toArray
              docId := doc.docId
              byteStart := byteStart
              byteLen := byteLen
              sliceDigest := computeSpanSliceDigest doc.docId byteStart byteLen slice
            }
    else
      .error (.unknownPredicateTag byteStart)

def parseObjectSpanList (g : GrammarSpec) (doc : DocChunkEntry) :
    List (Nat × Nat) → Except ParseRefusal (List SpanBoundAtom)
  | [] => .ok []
  | (s, l) :: rest => do
    let atom ← parseSingleObjectSpan g doc s l
    let tail ← parseObjectSpanList g doc rest
    .ok (atom :: tail)

/-- **Stage-2 Verified Span-Bound Fact Extractor**:
    Checks chunk integrity (`WfDocChunk`), sorted entity dictionary (`WfEntityDict`), full RFC 8259
    JSON grammar (`VpaJson.runFullJsonGrammar`), structural `DetVpa` policy acceptance, and per-span
    string-escape confinement + `PredRE` pattern/delimiter-ban + 256-bit `sliceDigest` commitment. -/
def extractSpanBoundAtoms (g : GrammarSpec) (doc : DocChunkEntry) :
    Except ParseRefusal (Array SpanBoundAtom) :=
  if !WfDocChunk doc then .error .invalidChunkIntegrity
  else if !WfEntityDict g.entityDict then .error .unsortedEntityDict
  else if !VpaJson.runFullJsonGrammar doc.rawBytes then .error .malformedJsonGrammar
  else if !VpaJson.accepts g.structuralVpa (lexJsonVpaWordExec doc.rawBytes).toList then
    .error .vpaPolicyRejected
  else
    let spans := scanBalancedObjectSpansGo doc.rawBytes 0 {} 0 none #[]
    match parseObjectSpanList g doc spans.toList with
    | .ok atoms => .ok atoms.toArray
    | .error err => .error err

/-! ## §4. Soundness, Unforgeability (`span_parse_sound_and_unforgeable`) & Redaction Weld -/

/-- Semantic soundness predicate established for every `SpanBoundAtom` emitted from `(g, doc)`. -/
structure ValidExtractedSpanAtom (g : GrammarSpec) (doc : DocChunkEntry) (a : SpanBoundAtom) : Prop where
  docId_eq         : a.docId = doc.docId
  len_pos          : 0 < a.byteLen
  in_bounds        : a.byteStart + a.byteLen ≤ doc.rawBytes.size
  outside_string   : (strEscapeStateAt doc.rawBytes a.byteStart).inString = false
  digest_eq        : a.sliceDigest =
    computeSpanSliceDigest doc.docId a.byteStart a.byteLen
      (doc.rawBytes.extract a.byteStart (a.byteStart + a.byteLen))
  slice_wf_bounds  : WfSpanSliceBounds a.docId a.byteStart a.byteLen
    (doc.rawBytes.extract a.byteStart (a.byteStart + a.byteLen)) = true
  matched_rule     : ∃ rule ∈ g.rules.toList,
    rule.predSym = a.predSym ∧
    a.args.size = rule.arity ∧
    Matches (doc.rawBytes.extract a.byteStart (a.byteStart + a.byteLen)).data.toList rule.slicePattern ∧
    (∀ u x v,
      (doc.rawBytes.extract a.byteStart (a.byteStart + a.byteLen)).data.toList = u ++ x ++ v →
      ¬ Matches x rule.banDelimiter)

private theorem wfSpanSliceBounds_of_chunk {doc : DocChunkEntry} {s l : Nat}
    (hChunk : WfDocChunk doc = true) (hIn : s + l ≤ doc.rawBytes.size) :
    WfSpanSliceBounds doc.docId s l (doc.rawBytes.extract s (s + l)) = true := by
  simp only [WfDocChunk, WfDocChunkBounds, Bool.and_eq_true, decide_eq_true_eq] at hChunk
  have hPow : (256 : Nat) ^ 8 = 18446744073709551616 := by decide
  have hExSz : (doc.rawBytes.extract s (s + l)).size ≤ doc.rawBytes.size := by
    rw [← toList_length, Commit.extract_toList]
    simp; omega
  simp only [WfSpanSliceBounds, Bool.and_eq_true, decide_eq_true_eq, hPow]
  exact ⟨⟨⟨hChunk.1.1.1, by omega⟩, by omega⟩, by omega⟩

private theorem resolveEntityArgs_length {dict : EntityDict} {s : Nat} :
    ∀ {raws : List ByteArray} {ids : List UInt32},
      resolveEntityArgs dict s raws = .ok ids → ids.length = raws.length
  | [], ids, h => by simp only [resolveEntityArgs, Except.ok.injEq] at h; subst h; rfl
  | r :: rs, ids, h => by
    unfold resolveEntityArgs at h
    cases hLook : lookupEntityId dict r with
    | none => rw [hLook] at h; cases h
    | some eid =>
      rw [hLook] at h
      simp only [bind, Except.bind] at h
      cases hRest : resolveEntityArgs dict s rs with
      | error _ => rw [hRest] at h; cases h
      | ok rest =>
        rw [hRest] at h; injection h with hIds; subst hIds
        simp [resolveEntityArgs_length hRest]

private theorem parseSingleObjectSpan_sound {g : GrammarSpec} {doc : DocChunkEntry}
    {s l : Nat} {a : SpanBoundAtom}
    (hChunk : WfDocChunk doc = true)
    (hOk : parseSingleObjectSpan g doc s l = .ok a) :
    ValidExtractedSpanAtom g doc a := by
  unfold parseSingleObjectSpan at hOk
  by_cases hBnd : (decide (0 < l) && decide (s + l ≤ doc.rawBytes.size)) = true
  · simp only [hBnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    by_cases hStr : (strEscapeStateAt doc.rawBytes s).inString = true
    · simp [hStr] at hOk
    · have hStrF : (strEscapeStateAt doc.rawBytes s).inString = false := Bool.eq_false_iff.mpr hStr
      simp only [hStrF, Bool.false_eq_true, ↓reduceIte] at hOk
      split at hOk
      · rename_i hValsPos
        cases hFind : g.rules.toList.find?
            (fun r => decide (r.predTag.data.toList = (collectOddValuesGo (extractQuotedStringsGo (doc.rawBytes.extract s (s + l)) 0 false none #[]) 1 #[])[0].data.toList)) with
        | none => rw [hFind] at hOk; cases hOk
        | some rule =>
          simp only [hFind] at hOk
          cases hArity : ((collectOddValuesGo (extractQuotedStringsGo (doc.rawBytes.extract s (s + l)) 0 false none #[]) 1 #[]).extract 1
              (collectOddValuesGo (extractQuotedStringsGo (doc.rawBytes.extract s (s + l)) 0 false none #[]) 1 #[]).size).toList.length != rule.arity
          · simp only [hArity, Bool.false_eq_true, ↓reduceIte] at hOk
            cases hPat : matchB (doc.rawBytes.extract s (s + l)).data.toList rule.slicePattern
            · simp only [hPat, Bool.not_false, ↓reduceIte] at hOk; cases hOk
            · simp only [hPat, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
              cases hBan : matchB (doc.rawBytes.extract s (s + l)).data.toList (absenceOf rule.banDelimiter)
              · simp only [hBan, Bool.not_false, ↓reduceIte] at hOk; cases hOk
              · simp only [hBan, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
                cases hRes : resolveEntityArgs g.entityDict s _ with
                | error _ => rw [hRes] at hOk; cases hOk
                | ok argList =>
                  rw [hRes] at hOk; injection hOk with haEq; subst haEq
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hBnd
                  have hArEq : ((collectOddValuesGo (extractQuotedStringsGo (doc.rawBytes.extract s (s + l)) 0 false none #[]) 1 #[]).extract 1
                      (collectOddValuesGo (extractQuotedStringsGo (doc.rawBytes.extract s (s + l)) 0 false none #[]) 1 #[]).size).toList.length = rule.arity :=
                    bne_eq_false_iff_eq.mp hArity
                  refine ⟨rfl, hBnd.1, hBnd.2, hStrF, rfl, wfSpanSliceBounds_of_chunk hChunk hBnd.2,
                    ⟨rule, List.mem_of_find?_eq_some hFind, rfl, ?_, (matchB_iff _ _).mp hPat,
                      (matches_absenceOf _ _).mp ((matchB_iff _ _).mp hBan)⟩⟩
                  rw [List.size_toArray, resolveEntityArgs_length hRes, hArEq]
          · simp only [hArity, ↓reduceIte] at hOk; cases hOk
      · cases hOk
  · have hBndF : (decide (0 < l) && decide (s + l ≤ doc.rawBytes.size)) = false := Bool.eq_false_iff.mpr hBnd
    simp [hBndF] at hOk

private theorem parseObjectSpanList_sound {g : GrammarSpec} {doc : DocChunkEntry}
    (hChunk : WfDocChunk doc = true) :
    ∀ {spans : List (Nat × Nat)} {atoms : List SpanBoundAtom},
      parseObjectSpanList g doc spans = .ok atoms →
      ∀ a ∈ atoms, ValidExtractedSpanAtom g doc a
  | [], atoms, hOk, a, ha => by
    simp only [parseObjectSpanList, Except.ok.injEq] at hOk; subst hOk; cases ha
  | (s, l) :: rest, atoms, hOk, a, ha => by
    unfold parseObjectSpanList at hOk
    simp only [bind, Except.bind] at hOk
    cases h1 : parseSingleObjectSpan g doc s l with
    | error _ => rw [h1] at hOk; cases hOk
    | ok headAtom =>
      rw [h1] at hOk; dsimp only at hOk
      cases h2 : parseObjectSpanList g doc rest with
      | error _ => rw [h2] at hOk; cases hOk
      | ok tailAtoms =>
        rw [h2] at hOk; injection hOk with hEq; subst hEq
        rcases List.mem_cons.mp ha with rfl | hTail
        · exact parseSingleObjectSpan_sound hChunk h1
        · exact parseObjectSpanList_sound hChunk h2 a hTail

/-- **Stage-2 Master Soundness & Unforgeability Theorem (`span_parse_sound_and_unforgeable`)**:
    1. **Grammar & Lexer Soundness**: If `extractSpanBoundAtoms g doc = .ok atoms`, then `doc` passes
       `WfDocChunk`, `VpaJson.runFullJsonGrammar`, and `g.structuralVpa` over `lexJsonVpaWordSpec`, and
       every emitted `a ∈ atoms` points to an exact in-bounds slice starting outside string literals
       matching `rule.slicePattern` and excluding `rule.banDelimiter`.
    2. **Zero Cross-Span Ambiguity (`bindAdv = 0` up to `CollisionAmong deployed`)**: Any two extracted
       atoms `a₁` (from `doc₁`) and `a₂` (from `doc₂`) sharing `a₁.sliceDigest = a₂.sliceDigest` have
       identical `(docId, byteStart, byteLen)` AND byte-identical extracted slices, or `deployed` collides
       on their exact two length-framed preimages. -/
theorem span_parse_sound_and_unforgeable
    {g₁ g₂ : GrammarSpec} {doc₁ doc₂ : DocChunkEntry} {atoms₁ atoms₂ : Array SpanBoundAtom}
    (hOk₁ : extractSpanBoundAtoms g₁ doc₁ = .ok atoms₁)
    (hOk₂ : extractSpanBoundAtoms g₂ doc₂ = .ok atoms₂) :
    WfDocChunk doc₁ = true ∧
    VpaJson.runFullJsonGrammar doc₁.rawBytes = true ∧
    VpaJson.accepts g₁.structuralVpa (lexJsonVpaWordSpec {} doc₁.rawBytes.data.toList) = true ∧
    (∀ a ∈ atoms₁, ValidExtractedSpanAtom g₁ doc₁ a) ∧
    (∀ a₁ ∈ atoms₁, ∀ a₂ ∈ atoms₂, a₁.sliceDigest = a₂.sliceDigest →
      (a₁.docId = a₂.docId ∧ a₁.byteStart = a₂.byteStart ∧ a₁.byteLen = a₂.byteLen ∧
        doc₁.rawBytes.extract a₁.byteStart (a₁.byteStart + a₁.byteLen) =
          doc₂.rawBytes.extract a₂.byteStart (a₂.byteStart + a₂.byteLen)) ∨
      CollisionAmong deployed
        (fun m =>
          m = spanSlicePreimage a₁.docId a₁.byteStart a₁.byteLen
                (doc₁.rawBytes.extract a₁.byteStart (a₁.byteStart + a₁.byteLen)) ∨
          m = spanSlicePreimage a₂.docId a₂.byteStart a₂.byteLen
                (doc₂.rawBytes.extract a₂.byteStart (a₂.byteStart + a₂.byteLen)))) := by
  have unpack {g : GrammarSpec} {doc : DocChunkEntry} {atoms : Array SpanBoundAtom}
      (hOk : extractSpanBoundAtoms g doc = .ok atoms) :
      WfDocChunk doc = true ∧
      VpaJson.runFullJsonGrammar doc.rawBytes = true ∧
      VpaJson.accepts g.structuralVpa (lexJsonVpaWordSpec {} doc.rawBytes.data.toList) = true ∧
      (∀ a ∈ atoms, ValidExtractedSpanAtom g doc a) := by
    unfold extractSpanBoundAtoms at hOk
    cases hWf : WfDocChunk doc with
    | false => simp [hWf] at hOk
    | true =>
      simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hDict : WfEntityDict g.entityDict with
      | false => simp [hDict] at hOk
      | true =>
        simp only [hDict, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        cases hJson : VpaJson.runFullJsonGrammar doc.rawBytes with
        | false => simp [hJson] at hOk
        | true =>
          simp only [hJson, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
          cases hVpa : VpaJson.accepts g.structuralVpa (lexJsonVpaWordExec doc.rawBytes).toList with
          | false => simp [hVpa] at hOk
          | true =>
            simp only [hVpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
            cases hList : parseObjectSpanList g doc _ with
            | error _ => rw [hList] at hOk; cases hOk
            | ok as =>
              rw [hList] at hOk; injection hOk with hArr; subst hArr
              rw [lexJsonVpaWordExec_eq_spec] at hVpa
              exact ⟨rfl, rfl, hVpa, fun a ha =>
                parseObjectSpanList_sound hWf hList a (Array.mem_toList_iff.mpr ha)⟩
  obtain ⟨hWf₁, hJson₁, hVpa₁, hVal₁⟩ := unpack hOk₁
  obtain ⟨_, _, _, hVal₂⟩ := unpack hOk₂
  refine ⟨hWf₁, hJson₁, hVpa₁, hVal₁, ?_⟩
  intro a₁ ha₁ a₂ ha₂ hDigEq
  have hv₁ := hVal₁ a₁ ha₁
  have hv₂ := hVal₂ a₂ ha₂
  rw [hv₁.digest_eq, hv₂.digest_eq, ← hv₁.docId_eq, ← hv₂.docId_eq] at hDigEq
  exact spanSliceDigest_binding hv₁.slice_wf_bounds hv₂.slice_wf_bounds hDigEq

/-- Constructive inhabitedness witness for `parseSingleObjectSpan`, `parseObjectSpanList`, and
    `extractSpanBoundAtoms` (proving non-vacuity of all Stage-2 soundness premises without evaluating
    Keccak-f[1600] in the kernel). -/
theorem extractSpanBoundAtoms_singleton (predSym : UInt32) :
    let raw := "{\"p\":\"rel\",\"a\":\"x\"}".toByteArray
    let doc := mkDocChunk 1 0 raw
    let g : GrammarSpec := {
      entityDict := ⟨#[("x".toByteArray, 7)]⟩
      rules := #[{
        predTag := "rel".toByteArray
        predSym := predSym
        arity := 1
        slicePattern := tt
        banDelimiter := .ff
      }]
    }
    let a : SpanBoundAtom := ⟨predSym, #[7], 1, 0, 19, computeSpanSliceDigest 1 0 19 (raw.extract 0 19)⟩
    parseSingleObjectSpan g doc 0 raw.size = .ok a ∧
    parseObjectSpanList g doc [(0, raw.size)] = .ok [a] ∧ extractSpanBoundAtoms g doc = .ok #[a] := by
  intro raw doc g a
  have hWfDoc : WfDocChunk doc = true :=
    wfDocChunk_mkDocChunk (by decide) (by decide) (by decide)
  have hDict : WfEntityDict ⟨#[("x".toByteArray, 7)]⟩ = true := by decide +kernel
  have hJson : VpaJson.runFullJsonGrammar doc.rawBytes = true := by decide +kernel
  have hVpa : VpaJson.accepts wellMatchedJsonVpa (lexJsonVpaWordExec doc.rawBytes).toList = true := by
    decide +kernel
  have hScan : scanBalancedObjectSpansGo doc.rawBytes 0 {} 0 none #[] = #[(0, 19)] := by
    decide +kernel
  have hSz : raw.size = 19 := by decide
  have hBnd : (decide (0 < 19) && decide (0 + 19 ≤ doc.rawBytes.size)) = true := by decide +kernel
  have hStr : (strEscapeStateAt doc.rawBytes 0).inString = false := by decide +kernel
  have hValsData :
      ((collectOddValuesGo (extractQuotedStringsGo (raw.extract 0 19) 0 false none #[]) 1 #[]).toList.map
        (fun b => b.data.toList)) =
      ["rel".toByteArray.data.toList, "x".toByteArray.data.toList] := by
    decide +kernel
  have hVals : collectOddValuesGo (extractQuotedStringsGo (doc.rawBytes.extract 0 19) 0 false none #[]) 1 #[] =
      #["rel".toByteArray, "x".toByteArray] := by
    change collectOddValuesGo (extractQuotedStringsGo (raw.extract 0 19) 0 false none #[]) 1 #[] = _
    apply Array.toList_inj.mp
    have aux : ∀ xs : List ByteArray,
        xs.map (fun b => b.data.toList) = ["rel".toByteArray.data.toList, "x".toByteArray.data.toList] →
        xs = ["rel".toByteArray, "x".toByteArray]
      | [b0, b1], h => by
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
        rw [byteArray_eq_of_toList h.1, byteArray_eq_of_toList h.2.1]
      | [], h => by simp at h
      | [_], h => by simp at h
      | _ :: _ :: _ :: _, h => by simp at h
    exact aux _ hValsData
  have hPat : matchB (doc.rawBytes.extract 0 19).data.toList tt = true :=
    (matchB_iff _ _).mpr (matches_tt _)
  have hBan : matchB (doc.rawBytes.extract 0 19).data.toList (absenceOf .ff) = true :=
    (matchB_iff _ _).mpr ((matches_absenceOf .ff _).mpr (fun _ _ _ _ h => h))
  have hLookX : lookupEntityId ⟨#[("x".toByteArray, 7)]⟩ "x".toByteArray = some 7 := by
    decide +kernel
  have hRes : resolveEntityArgs ⟨#[("x".toByteArray, 7)]⟩ 0 ["x".toByteArray] = .ok [7] := by
    simp [resolveEntityArgs, hLookX, bind, Except.bind]
  have ha : parseSingleObjectSpan g doc 0 19 = .ok a := by
    unfold parseSingleObjectSpan
    rw [hBnd, Bool.not_true, ite_eq_right (by decide), hStr, ite_eq_right (by decide)]
    dsimp only
    rw [hVals]
    have hPos2 : 0 < (#["rel".toByteArray, "x".toByteArray] : Array ByteArray).size := by decide
    rw [dite_eq_left hPos2]
    have hRuleToList : g.rules.toList =
        [{ predTag := "rel".toByteArray, predSym := predSym, arity := 1,
           slicePattern := tt, banDelimiter := .ff }] := rfl
    have hFindRule :
        [({ predTag := "rel".toByteArray, predSym := predSym, arity := 1,
            slicePattern := tt, banDelimiter := .ff } : SpanRuleSpec)].find?
          (fun r => decide (r.predTag.data.toList = "rel".toByteArray.data.toList)) =
        some { predTag := "rel".toByteArray, predSym := predSym, arity := 1,
               slicePattern := tt, banDelimiter := .ff } := by
      simp
    rw [show (#["rel".toByteArray, "x".toByteArray] : Array ByteArray)[0]'hPos2 = "rel".toByteArray from rfl,
        hRuleToList, hFindRule]
    dsimp only
    have hExArgs : (#["rel".toByteArray, "x".toByteArray].extract 1 2).toList = ["x".toByteArray] := rfl
    rw [show (#["rel".toByteArray, "x".toByteArray] : Array ByteArray).size = 2 from rfl, hExArgs]
    have hGeDict : g.entityDict = ⟨#[("x".toByteArray, 7)]⟩ := rfl
    rw [ite_eq_right (by decide : ¬ ((["x".toByteArray].length != 1) = true)),
        hPat, Bool.not_true, ite_eq_right (by decide),
        hBan, Bool.not_true, ite_eq_right (by decide), hGeDict, hRes]
    rfl
  refine ⟨hSz ▸ ha, ?_, ?_⟩
  · rw [hSz]; simp [parseObjectSpanList, ha, bind, Except.bind]
  · unfold extractSpanBoundAtoms
    have hGeDict : g.entityDict = ⟨#[("x".toByteArray, 7)]⟩ := rfl
    have hGeVpa : g.structuralVpa = wellMatchedJsonVpa := rfl
    rw [hGeDict, hGeVpa]
    simp [hWfDoc, hDict, hJson, hVpa, hScan, parseObjectSpanList, ha, bind, Except.bind]

theorem extractSpanBoundAtoms_inhabited (predSym : UInt32) :
    let raw := "{\"p\":\"rel\",\"a\":\"x\"}".toByteArray
    let doc := mkDocChunk 1 0 raw
    let g : GrammarSpec := {
      entityDict := ⟨#[("x".toByteArray, 7)]⟩
      rules := #[{
        predTag := "rel".toByteArray
        predSym := predSym
        arity := 1
        slicePattern := tt
        banDelimiter := .ff
      }]
    }
    (∃ a, parseSingleObjectSpan g doc 0 raw.size = .ok a) ∧
    (∃ as, parseObjectSpanList g doc [(0, raw.size)] = .ok as) ∧
    (∃ atoms, atoms.size = 1 ∧ extractSpanBoundAtoms g doc = .ok atoms) := by
  obtain ⟨hp, hl, he⟩ := extractSpanBoundAtoms_singleton predSym
  exact ⟨⟨_, hp⟩, ⟨_, hl⟩, ⟨_, rfl, he⟩⟩

private theorem checkSortedDisjointSpansFrom_hi (docLen : Nat) :
    ∀ (xs : List (Nat × Nat)) (m : Nat),
      checkSortedDisjointSpansFrom m docLen xs = true → ∀ x ∈ xs, x.2 ≤ docLen
  | [], _, _, _, hx => nomatch hx
  | (s, e) :: tl, m, hw, x, hx => by
    simp only [checkSortedDisjointSpansFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
    rcases List.mem_cons.mp hx with rfl | htl
    · exact hw.1.2
    · exact checkSortedDisjointSpansFrom_hi docLen tl (e + 1) hw.2 x htl

/-- **Stage 1 → Stage 2 Redaction Slice Preservation (`redacted_span_parse_sound`)**:
    When `doc.rawBytes` passes `checkRedactionDelimiterConfined` under `pol`, any span `[byteStart, byteStart + byteLen)`
    contained inside a disclosed interval `sp ∈ pol.disclosedSpans` has identical bytes in the redacted view
    `applyRedactionPolicy doc.rawBytes pol` and in the unredacted `doc.rawBytes`. -/
theorem redacted_span_parse_sound
    {doc : ByteArray} {pol : RedactionSlicePolicy} {sp : Nat × Nat} {byteStart byteLen : Nat}
    (hConf : checkRedactionDelimiterConfined doc pol = true)
    (hMem : sp ∈ pol.disclosedSpans.toList)
    (hStart : sp.1 ≤ byteStart) (hStop : byteStart + byteLen ≤ sp.2) :
    (applyRedactionPolicy doc pol).extract byteStart (byteStart + byteLen) =
      doc.extract byteStart (byteStart + byteLen) := by
  obtain ⟨hRedSz, hRedByte, _⟩ := applyRedactionPolicy_characterization hConf
  have hConfUnpack := hConf
  simp only [checkRedactionDelimiterConfined, Bool.and_eq_true, decide_eq_true_eq] at hConfUnpack
  obtain ⟨⟨hDocSz, hDisj⟩, _⟩ := hConfUnpack
  have hSpBound : sp.2 ≤ pol.docByteLen :=
    checkSortedDisjointSpansFrom_hi pol.docByteLen pol.disclosedSpans.toList 0 hDisj sp hMem
  apply byteArray_eq_of_toList
  rw [Commit.extract_toList, Commit.extract_toList]
  apply List.ext_getElem
  · simp [hRedSz]
  · intro k hk₁ hk₂
    have hkLt : k < byteLen := by simp [hRedSz] at hk₁; omega
    have hPosLtDoc : byteStart + k < doc.size := by omega
    have hPosInSp : inByteSpan (byteStart + k) sp = true := by
      simp only [inByteSpan, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hPosDis : isDisclosedAt pol (byteStart + k) = true :=
      List.any_eq_true.mpr ⟨sp, hMem, hPosInSp⟩
    have hByte := hRedByte (byteStart + k) hPosLtDoc
    simp only [hPosDis, ↓reduceIte] at hByte
    have hka : byteStart + k < (applyRedactionPolicy doc pol).data.toList.length := by
      rw [toList_length, hRedSz]; exact hPosLtDoc
    have hkb : byteStart + k < doc.data.toList.length := by rw [toList_length]; exact hPosLtDoc
    simp only [byteAt, hPosLtDoc, show byteStart + k < (applyRedactionPolicy doc pol).size by omega,
      ↓reduceDIte] at hByte
    have hga : (applyRedactionPolicy doc pol).data.toList[byteStart + k]'hka =
        (applyRedactionPolicy doc pol)[byteStart + k]'(by omega) := rfl
    have hgb : doc.data.toList[byteStart + k]'hkb = doc[byteStart + k]'hPosLtDoc := rfl
    simpa [List.getElem_take, List.getElem_drop, hga, hgb] using hByte

end Obend.SemanticKG
end
