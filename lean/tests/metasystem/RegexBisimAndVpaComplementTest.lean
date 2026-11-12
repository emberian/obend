module
/-
# RegexBisimAndVpaComplementTest — policies, certificates, attack fixtures and mutation teeth

Exercises `Obend.Judge.SymbolicRegexBisim` and `Obend.Judge.VpaComplementAndJson` together.

1. **Regular policies.** Delimiter bans as `absenceOf`: `noDoubleBrace` (`{{`), `noRoleDelimiter`
   (a line starting `System:`, and `<|im_start|>`). Their certificates come from `emitBisimPairs`
   and are checked in the kernel by `bisimCheck`; the inclusions are terms through
   `bisimCheck_sound` and `absenceOf_sound`. The judge refuses the false upgrade with the word `{`.
2. **Separations.** A verifier without the root openings accepts an unrelated certificate for a
   false committed statement that `verifyCommittedBisimWith` refuses; a checker without the
   nullability obligation accepts `anyByte ⊆ eps`, which `bisimCheck` refuses.
3. **Visibly pushdown policies** over three bracket sorts: complement, intersection and union
   on a nested template and on a mismatched one, a certified containment, a refusal with its
   separating word, and an inhabitant of the judge's fragment.
4. **JSON**: an accepted document, the malformed inputs refused (missing colon, trailing comma,
   raw control byte, `{]`, duplicate key, bad escape, leading zero, truncated literal, two
   values), a redaction through an escaped quote, the redactions refused, confinement, and the
   canonical commitment's refusal of unsorted and duplicate keys.
5. **Merkle span inclusion** over five spans (an odd level at each height): every honest proof
   verifies, a tampered span and a wrong index do not, and a proof carries at most three
   siblings.
6. **Teeth**: each `#tooth` replaces one real check and reports that a stored proof no longer
   checks.

Kernel runs that hash use `toyHasher`, a 32-byte fold: the theorems hold for every `Hasher`, and
the kernel does not evaluate cSHAKE256. The cSHAKE256 instances run compiled, under `#guard`.
-/

public import Obend.Tactic.Tooth
public import Obend.AssertAxioms
public import Obend.Judge.SymbolicRegexBisim
public import Obend.Judge.VpaComplementAndJson
import all Obend.Core.Term
import all Obend.Judge.Class
import all Obend.Codec.DetCbor
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256
import all Obend.Vault.Lsafe
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Judge.VpaComplementAndJson
import all Obend.AssertAxioms
import all Obend.Tactic.Tooth
meta import Obend.Digest.Cshake256
meta import Obend.Vault.Lsafe
meta import Obend.Judge.SymbolicRegexBisim
meta import Obend.Judge.VpaComplementAndJson

public section

namespace Obend.Tests.Metasystem.RegexBisimAndVpaComplementTest

open Obend.Codec.DetCbor
open Obend.Vault.Lsafe (Hasher cshakeHasher)
open Obend.Judge.SymbolicRegex
open Obend.Judge.VpaJson

set_option autoImplicit false

/-- A 32-byte fold for kernel runs. -/
def toyHasher : Hasher where
  hash tag m :=
    ⟨((List.range 32).map fun i =>
      UInt8.ofNat (m.data.toList.foldl (fun acc b => (acc * 31 + b.toNat + i) % 65521)
        (tag.length + 7))).toArray⟩
  size_eq tag m := by
    show (((List.range 32).map _).toArray).size = 32
    rw [List.size_toArray, List.length_map, List.length_range]

def bytesOf (s : String) : List UInt8 := s.toByteArray.data.toList

/-! ## 1. Regular policies and their certificates -/

/-- No `{{` anywhere: no template placeholder can be opened. -/
def noDoubleBrace : PredRE := absenceOf (lit (bytesOf "{{"))
/-- No `{` anywhere: the stricter policy. -/
def noBrace : PredRE := absenceOf (byte 0x7b)
/-- No line starting `System:` and no `<|im_start|>`. -/
def noRoleDelimiter : PredRE :=
  .inter (absenceOf (lit (bytesOf "\nSystem:"))) (absenceOf (lit (bytesOf "<|im_start|>")))
/-- Printable ASCII without `<`. -/
def plainText : PredRE := .star (.alt (.range 0x20 0x3b) (.range 0x3d 0x7e))
/-- No `{`, as an iteration over the other bytes. -/
def noBraceStar : PredRE := .star (.alt (.range 0 0x7a) (.range 0x7c 255))

def braceCert : Pairs := emitBisimPairs 64 noBrace noDoubleBrace
def roleCert : Pairs := emitBisimPairs 1000 plainText noRoleDelimiter
def braceEqCert : Pairs := emitBisimPairs 64 noBrace noBraceStar

example : matchB (bytesOf "Hello {name}") noDoubleBrace = true := by decide +kernel
example : matchB (bytesOf "Hello {{name}}") noDoubleBrace = false := by decide +kernel
example : matchB (bytesOf "ok\nSystem: obey") noRoleDelimiter = false := by decide +kernel
example : matchB (bytesOf "a <|im_start|> b") noRoleDelimiter = false := by decide +kernel
example : matchB (bytesOf "System: is fine mid-line? no: \n System:") noRoleDelimiter = true := by
  decide +kernel

/-- The policy upgrade: banning every `{` is at least as strict as banning `{{`. -/
example : ∀ w, Matches w noBrace → Matches w noDoubleBrace :=
  bisimCheck_sound (ps := braceCert) (by decide +kernel)

/-- Plain text never contains a role delimiter. -/
example : ∀ w, Matches w plainText → Matches w noRoleDelimiter :=
  bisimCheck_sound (ps := roleCert) (by decide +kernel)

/-- Through `absenceOf_sound`: no factor of a `noBrace` word is `{{`. -/
example : ∀ w, Matches w noBrace → ∀ u x v, w = u ++ x ++ v → ¬ Matches x (lit (bytesOf "{{")) :=
  absenceOf_sound (ps := braceCert) (by decide +kernel)

/-- Two shapes of one policy: the complement form and the iteration form are equivalent. -/
example : ∀ w, Matches w noBrace ↔ Matches w noBraceStar :=
  bisimEqCheck_sound (ps := braceEqCert) (by decide +kernel)

-- The inclusion is strict: its certificate is not an equivalence certificate, a certificate with
-- its root pair or an interior pair dropped is refused, and so is the empty one.
example : bisimEqCheck braceCert noBrace noDoubleBrace = false := by decide +kernel
example : bisimCheck (braceCert.eraseIdx 0) noBrace noDoubleBrace = false := by decide +kernel
example : bisimCheck (braceCert.eraseIdx 1) noBrace noDoubleBrace = false := by decide +kernel
example : bisimCheck [] noBrace noDoubleBrace = false := by decide +kernel

/-- The judge accepts the upgrade and refuses the downgrade with the word `{`. -/
example : inclusionCheck 0 ⟨noBrace, noDoubleBrace⟩ braceCert = .ok := by decide +kernel
example : inclusionCheck 3 ⟨noDoubleBrace, noBrace⟩
    (emitBisimPairs 64 noDoubleBrace noBrace) = .refused .counterexample [0x7b] := by
  decide +kernel
example : inclusionCheck 3 ⟨.eps, anyByte⟩ [] = .refused .nullableMismatch [] := by decide +kernel
/-- A wrong certificate for a true inclusion is undecided, never refuted. -/
example : inclusionCheck 2 ⟨noBrace, noDoubleBrace⟩ [] = .uncovered := by decide +kernel

/-- The downgrade is false, by the judge's refutation law. -/
example : ¬ ∀ w, Matches w noDoubleBrace → Matches w noBrace :=
  searchCex_sound (q := ⟨noDoubleBrace, noBrace⟩) (depth := 1) (w := [0x7b]) (by decide +kernel)

/-- The fragment is inhabited at the upgrade query: its exploration closes. -/
example : symbolicRegexInclusionJudge.Fragment ⟨noBrace, noDoubleBrace⟩ := ⟨64, by decide +kernel⟩

/-! ## 2. Separations -/

def rootOf (r : PredRE) : ByteArray := commitREWith toyHasher r

example : decRE (encRE noRoleDelimiter) = some noRoleDelimiter := by decide +kernel
example : (rootOf noBrace).size = 32 ∧ rootOf noBrace ≠ rootOf noDoubleBrace := by decide +kernel

/-- The committed upgrade verifies; with the roots swapped it does not. -/
example : verifyCommittedBisimWith toyHasher (rootOf noBrace) (rootOf noDoubleBrace)
    ⟨noBrace, noDoubleBrace, braceCert⟩ = true := by decide +kernel
example : verifyCommittedBisimWith toyHasher (rootOf noDoubleBrace) (rootOf noBrace)
    ⟨noBrace, noDoubleBrace, braceCert⟩ = false := by decide +kernel

/-- The weaker verifier: the certificate is checked, the openings are not. -/
def noBindVerifier (cert : CommittedBisimCert) : Bool := bisimCheck cert.pairs cert.lhs cert.rhs

/-- A true certificate about unrelated policies. -/
def splicedCert : CommittedBisimCert := ⟨byte 0x61, anyByte, emitBisimPairs 8 (byte 0x61) anyByte⟩

/-- **Binding separation.** For the false committed statement "`noDoubleBrace ⊆ noBrace`" the
unbound verifier accepts the spliced certificate, the bound verifier refuses it, and the
statement is false. -/
example : noBindVerifier splicedCert = true ∧
    verifyCommittedBisimWith toyHasher (rootOf noDoubleBrace) (rootOf noBrace) splicedCert = false ∧
    ¬ (∀ w, Matches w noDoubleBrace → Matches w noBrace) :=
  ⟨by decide +kernel, by decide +kernel,
    searchCex_sound (q := ⟨noDoubleBrace, noBrace⟩) (depth := 1) (w := [0x7b]) (by decide +kernel)⟩

/-- The extractor at the toy hasher returns the inclusion itself for the committed upgrade. -/
example : (match committedBisimExtract toyHasher (rootP := rootOf noBrace)
    (rootQ := rootOf noDoubleBrace) (cert := ⟨noBrace, noDoubleBrace, braceCert⟩)
    (by decide +kernel) noBrace noDoubleBrace rfl rfl with
    | .inl _ => true
    | .inr _ => false) = true := by decide +kernel

/-- The weaker checker: closure without the nullability obligation. -/
def bisimNoNullable (ps : Pairs) (r s : PredRE) : Bool :=
  bisimOk (fun _ _ => true) (classesOf ps) ps r s

/-- **Nullability separation.** `anyByte ⊆ eps` is false at the one-byte word; the checker
without nullability accepts it and `bisimCheck` refuses it. -/
example : bisimNoNullable (emitBisimPairs 8 anyByte .eps) anyByte .eps = true ∧
    bisimCheck (emitBisimPairs 8 anyByte .eps) anyByte .eps = false ∧
    ¬ (∀ w, Matches w anyByte → Matches w .eps) :=
  ⟨by decide +kernel, by decide +kernel,
    searchCex_sound (q := ⟨anyByte, .eps⟩) (depth := 1) (w := [0]) (by decide +kernel)⟩

-- The cSHAKE256 instances, compiled.
#guard verifyCommittedBisim (commitRE (absenceOf (byte 0x7b)))
  (commitRE (absenceOf (lit [0x7b, 0x7b])))
  ⟨absenceOf (byte 0x7b), absenceOf (lit [0x7b, 0x7b]),
    emitBisimPairs 64 (absenceOf (byte 0x7b)) (absenceOf (lit [0x7b, 0x7b]))⟩
#guard !verifyCommittedBisim (commitRE (absenceOf (lit [0x7b, 0x7b])))
  (commitRE (absenceOf (byte 0x7b)))
  ⟨byte 0x61, anyByte, emitBisimPairs 8 (byte 0x61) anyByte⟩
#guard (commitRE (absenceOf (byte 0x7b))).size == 32

/-! ## 3. Visibly pushdown policies -/

/-- Three bracket sorts: `{ }`, `[ ]`, `<tag> </tag>`. -/
inductive Br where
  | curly | square | tag
  deriving DecidableEq

/-- Internal tokens: text, and a separator. -/
inductive Tok where
  | text | sep
  deriving DecidableEq

instance : FinEnum Br := ⟨[.curly, .square, .tag], fun b => by cases b <;> simp⟩
instance : FinEnum Tok := ⟨[.text, .sep], fun t => by cases t <;> simp⟩

/-- Every well-matched word. -/
def anyNested : DetVpa Br Tok Unit Unit :=
  ⟨(), fun _ => true, fun q _ => q, fun q _ => (q, ()), fun q _ _ => q⟩

/-- Nesting depth at most `k`: the state is the depth, `none` once exceeded; a call pushes the
depth to return to. -/
def depthAtMost (k : Nat) : DetVpa Br Tok (Option Nat) Nat where
  init := some 0
  acc q := q.isSome
  stepInt q _ := q
  stepCall q _ :=
    match q with
    | some d => (if d < k then some (d + 1) else none, d)
    | none => (none, 0)
  stepRet q γ _ := q.map fun _ => γ

/-- No separator directly inside a `<tag>` element: the state is (no violation, inside a tag);
a call pushes the enclosing flag. -/
def noSepInTag : DetVpa Br Tok (Bool × Bool) Bool where
  init := (true, false)
  acc q := q.1
  stepInt q a := (q.1 && !(q.2 && decide (a = .sep)), q.2)
  stepCall q s := ((q.1, decide (s = .tag)), q.2)
  stepRet q γ _ := (q.1, γ)

/-- `{ text [ <tag> text </tag> ] }`. -/
def template : List (Sym Br Tok) :=
  [.call .curly, .int .text, .call .square, .call .tag, .int .text, .ret .tag, .ret .square,
    .ret .curly]
/-- `{ <tag> sep </tag> }`. -/
def sepInTag : List (Sym Br Tok) := [.call .curly, .call .tag, .int .sep, .ret .tag, .ret .curly]
/-- `{ ]`: a return of the wrong sort. -/
def mismatched : List (Sym Br Tok) := [.call .curly, .ret .square]

example : wellMatched template = true ∧ wellMatched mismatched = false := by decide +kernel
example : accepts anyNested template = true ∧ accepts (depthAtMost 3) template = true ∧
    accepts (depthAtMost 2) template = false := by decide +kernel
example : accepts noSepInTag template = true ∧ accepts noSepInTag sepInTag = false := by
  decide +kernel

-- Complement is exact on the well-matched template and both verdicts are `false` on `{ ]`: the
-- mismatched return is the sink of every automaton.
example : accepts (complementVpa (depthAtMost 2)) template = true ∧
    accepts (complementVpa (depthAtMost 3)) template = false := by decide +kernel
example : accepts anyNested mismatched = false ∧
    accepts (complementVpa anyNested) mismatched = false := by decide +kernel
example : accepts (complementVpa (depthAtMost 2)) template = !accepts (depthAtMost 2) template :=
  accepts_complement _ (by decide +kernel)

example : accepts (intersectVpa (depthAtMost 3) noSepInTag) template = true ∧
    accepts (intersectVpa (depthAtMost 2) noSepInTag) template = false ∧
    accepts (unionVpa (depthAtMost 2) noSepInTag) template = true ∧
    accepts (unionVpa (depthAtMost 1) noSepInTag) sepInTag = false := by decide +kernel

/-- Certified containment: depth at most two is depth at most three, for every word. -/
example : ∀ w, accepts (depthAtMost 2) w = true → accepts (depthAtMost 3) w = true :=
  verifyVpaContainment_sound
    (sum := emitVpaSummary (intersectVpa (depthAtMost 2) (complementVpa (depthAtMost 3))) 12)
    (by decide +kernel)

/-- Both bounded-depth policies are policies of well-nested documents. -/
example : ∀ w, accepts (intersectVpa (depthAtMost 2) noSepInTag) w = true →
    accepts anyNested w = true :=
  verifyVpaContainment_sound
    (sum := emitVpaSummary
      (intersectVpa (intersectVpa (depthAtMost 2) noSepInTag) (complementVpa anyNested)) 12)
    (by decide +kernel)

/-- The reverse containment is refused by the judge with the separating word `{ }`. -/
example : (match vpaCheck 2 ⟨depthAtMost 1, depthAtMost 0⟩ [] with
    | .refused (.counterexample w) p =>
      decide (w = [.call .curly, .ret .curly]) && decide (p = [2])
    | _ => false) = true := by decide +kernel

example : ¬ VpaIncluded (⟨depthAtMost 1, depthAtMost 0⟩ : VpaQuery Br Tok _ _ _ _) :=
  separates_refutes (w := [.call .curly, .ret .curly]) (by decide +kernel)

/-- The summary of `oneSortVpa ∩ ¬balancedVpa`: both states, each from each entry. -/
def oneSortSummary : List ((Bool × Unit) × (Bool × Unit)) :=
  emitVpaSummary (intersectVpa oneSortVpa (complementVpa balancedVpa)) 8

/-- **The containment judge's fragment is inhabited**: the summary is closed and its initial row
is exact (`(true, ())` by the empty word, `(false, ())` by a bracket pair of the other sort). -/
example : (vpaContainmentJudge (S := Bool) (L := Unit)).Fragment ⟨oneSortVpa, balancedVpa⟩ := by
  refine ⟨oneSortSummary, by decide +kernel, ?_⟩
  rintro ⟨b, ⟨⟩⟩ _
  cases b
  · exact ⟨[.call false, .ret false], by decide +kernel⟩
  · exact ⟨[], by decide +kernel⟩

/-! ## 4. The JSON grammar, redaction, the canonical commitment -/

def js (s : String) : ByteArray := s.toByteArray

example : runFullJsonGrammar
    (js "{\"a\": [1, -2.5e+3, true, false, null, \"x\\u00e9\\n\"], \"b\": {\"c\": {}}, \"d\": []}") =
      true := by decide +kernel
example : runFullJsonGrammar (js "0") = true ∧ runFullJsonGrammar (js " \"s\" ") = true ∧
    runFullJsonGrammar (js "[[],{}]") = true := by decide +kernel
example : jsonObjectKeys (js "{\"b\":{\"x\":1},\"a\":2}") =
    [[js "a", js "b"], [js "x"]] := by decide +kernel

-- Refused: missing colon, trailing commas, a raw control byte in a string, `{]`, a duplicate key.
example : runFullJsonGrammar (js "{\"a\" 1}") = false := by decide +kernel
example : runFullJsonGrammar (js "[1,]") = false ∧ runFullJsonGrammar (js "{\"a\":1,}") = false := by
  decide +kernel
example : runFullJsonGrammar (js "\"a\nb\"") = false := by decide +kernel
example : runFullJsonGrammar (js "{]") = false ∧ runFullJsonGrammar (js "[}") = false := by
  decide +kernel
example : runFullJsonGrammar (js "{\"a\":1,\"a\":2}") = false := by decide +kernel
example : runFullJsonGrammar (js "[{\"k\":1},{\"k\":2}]") = true := by decide +kernel
-- Refused: a bad escape, a short `\u`, an escape in a key, a leading zero, a bare dot, a
-- truncated literal, two values, a bare comma, a missing value, the empty document.
example : runFullJsonGrammar (js "\"\\x\"") = false ∧ runFullJsonGrammar (js "\"\\u12g4\"") = false ∧
    runFullJsonGrammar (js "{\"\\u0061\":1}") = false := by decide +kernel
example : runFullJsonGrammar (js "01") = false ∧ runFullJsonGrammar (js "1.") = false ∧
    runFullJsonGrammar (js "-") = false ∧ runFullJsonGrammar (js "1e") = false := by decide +kernel
example : runFullJsonGrammar (js "tru") = false ∧ runFullJsonGrammar (js "1 2") = false ∧
    runFullJsonGrammar (js "[,1]") = false ∧ runFullJsonGrammar (js "{\"a\":}") = false ∧
    runFullJsonGrammar (js "") = false ∧ runFullJsonGrammar (js "[1") = false := by decide +kernel

/-- A document whose secret contains an escaped quote. -/
def secretDoc : ByteArray := js "{\"user\":\"alice\",\"token\":\"s3\\\"cr3t\"}"
def otherDoc : ByteArray := js "{\"user\":\"alice\",\"token\":\"a much longer \\\\ secret\"}"
def mask : ByteArray := js "****"

example : runFullJsonGrammar secretDoc = true := by decide +kernel
example : checkJsonRedaction secretDoc 25 33 mask = true := by decide +kernel
example : redactJsonSpan secretDoc 25 33 mask = js "{\"user\":\"alice\",\"token\":\"****\"}" := by
  decide +kernel

/-- The redacted document is valid and has the same keys, by the theorem. -/
example : runFullJsonGrammar (redactJsonSpan secretDoc 25 33 mask) = true ∧
    jsonObjectKeys (redactJsonSpan secretDoc 25 33 mask) = [[js "token", js "user"]] := by
  obtain ⟨h1, h2, _⟩ := jsonRedaction_preserves_valid_parse_and_keys
    (doc := secretDoc) (l := 25) (r := 33) (mask := mask) (by decide +kernel)
  rw [h1, h2]
  decide +kernel

-- Refused redactions: a mask with a quote or a backslash, a span that ends between the
-- backslash and the quote it escapes, a span that leaves the string, a span inside a key, a
-- span past the end.
example : checkJsonRedaction secretDoc 25 33 (js "x\"y") = false ∧
    checkJsonRedaction secretDoc 25 33 (js "x\\") = false := by decide +kernel
example : checkJsonRedaction secretDoc 25 28 mask = false := by decide +kernel
example : checkJsonRedaction secretDoc 25 34 mask = false := by decide +kernel
example : checkJsonRedaction secretDoc 3 5 mask = false := by decide +kernel
example : checkJsonRedaction secretDoc 25 99 mask = false := by decide +kernel
/-- What the escape refusal protects: cutting between the backslash and its quote breaks the
document. -/
example : runFullJsonGrammar (redactJsonSpan secretDoc 25 28 mask) = false := by decide +kernel

/-- **Confinement, executed**: two documents that differ only in the secret redact to the same
bytes, by the theorem. -/
example : redactJsonSpan secretDoc 25 33 mask = redactJsonSpan otherDoc 25 48 mask :=
  jsonRedaction_confinement mask (by decide +kernel) (by decide +kernel)
example : checkJsonRedaction otherDoc 25 48 mask = true := by decide +kernel

/-- An object with ascending keys commits; unsorted or repeated keys do not. -/
def sortedObj : JVal := .obj [(js "a", .num (js "1")), (js "b", .arr [.null, .bool true, .str (js "x")])]
example : (jsonCborCommit toyHasher sortedObj).isSome = true := by decide +kernel
example : (jsonCborCommit toyHasher (.obj [(js "b", .null), (js "a", .null)])).isSome = false := by
  decide +kernel
example : (jsonCborCommit toyHasher (.obj [(js "a", .null), (js "a", .null)])).isSome = false := by
  decide +kernel
example : cborToJson (jsonToCbor sortedObj) = some sortedObj := cborToJson_jsonToCbor sortedObj

/-! ## 5. Merkle inclusion of one span -/

/-- Five spans: the leaf level and the level above it are odd. -/
def spans : List ByteArray := [js "alice", js "****", js "", js "edge:7->9", js "tail"]
def root : SpanRoot := spanMerkleRoot toyHasher spans

example : root.count = 5 ∧ root.top.size = 32 := by decide +kernel
example : verifySpanMerkleInclusion toyHasher root (js "edge:7->9")
    (spanMerkleProof toyHasher spans 3) = true := by decide +kernel
example : verifySpanMerkleInclusion toyHasher root (js "tail")
    (spanMerkleProof toyHasher spans 4) = true := by decide +kernel
/-- Every index, by the completeness theorem. -/
example (i : Nat) (hi : i < spans.length) :
    verifySpanMerkleInclusion toyHasher root (spans[i]'hi) (spanMerkleProof toyHasher spans i) =
      true :=
  verifySpanMerkleInclusion_complete toyHasher spans i hi

-- `⌈log₂ 5⌉ = 3` siblings at most; the promoted last leaf needs one.
example : (spanMerkleProof toyHasher spans 0).siblings.length = 3 ∧
    (spanMerkleProof toyHasher spans 4).siblings.length = 1 := by decide +kernel

-- Refused: a tampered span on an honest path, the honest span at another index, an index past
-- the count, a path with a sibling dropped, and (for the promoted last leaf, whose path depends
-- on the count) a root with another count.
example : verifySpanMerkleInclusion toyHasher root (js "edge:7->8")
    (spanMerkleProof toyHasher spans 3) = false := by decide +kernel
example : verifySpanMerkleInclusion toyHasher root (js "edge:7->9")
    ⟨2, (spanMerkleProof toyHasher spans 3).siblings⟩ = false := by decide +kernel
example : verifySpanMerkleInclusion toyHasher root (js "tail")
    ⟨5, (spanMerkleProof toyHasher spans 4).siblings⟩ = false := by decide +kernel
example : verifySpanMerkleInclusion toyHasher root (js "edge:7->9")
    ⟨3, (spanMerkleProof toyHasher spans 3).siblings.drop 1⟩ = false := by decide +kernel
example : verifySpanMerkleInclusion toyHasher ⟨6, root.top⟩ (js "tail")
    (spanMerkleProof toyHasher spans 4) = false := by decide +kernel
/-- A span's length is in its leaf: a span and its extension by a zero byte have different
leaf messages, as do a leaf and any node. -/
example : leafMsg (js "a") ≠ leafMsg (js "a\x00") := by decide +kernel

-- The cSHAKE256 tree, compiled.
#guard verifySpanMerkleInclusion cshakeHasher
  (spanMerkleRoot cshakeHasher ["alice".toByteArray, "****".toByteArray, "tail".toByteArray])
  "tail".toByteArray
  (spanMerkleProof cshakeHasher ["alice".toByteArray, "****".toByteArray, "tail".toByteArray] 2)
#guard !verifySpanMerkleInclusion cshakeHasher
  (spanMerkleRoot cshakeHasher ["alice".toByteArray, "****".toByteArray, "tail".toByteArray])
  "tale".toByteArray
  (spanMerkleProof cshakeHasher ["alice".toByteArray, "****".toByteArray, "tail".toByteArray] 2)

/-! ## 6. Mutation teeth -/

-- A checker that does not ask `null p → null q`.
#tooth bisimCheck_sound by
  mutation nullImp := fun _ _ => true

-- A checker that does not close the pairs under derivatives.
#tooth bisimCheck_sound by
  mutation closedAt := fun _ _ _ => true

-- An equivalence checker with the inclusion's nullability obligation.
#tooth bisimEqCheck_sound by
  mutation nullEq := fun p q => !null p || null q

-- A class cover without the successors of the upper ends.
#tooth classesOf_covers by
  mutation breakpoints := fun as => as.map (·.1)

-- A committed verifier that does not open the roots.
#tooth verifyCommittedBisim_sound_or_collision by
  mutation rootBinds := fun _ _ _ => true

-- A pushdown automaton whose returns pop a symbol of any sort.
#tooth verifyVpaContainment_sound by
  mutation sortMatch := fun _ _ => true

-- An emptiness check that does not look at the accepting states.
#tooth verifyVpaEmpty_sound by
  mutation summaryRejects := fun _ _ => true

-- An object that closes without the duplicate-key check.
#tooth json_object_keys_nodup by
  mutation closeObject := fun st =>
    match st.stack with
    | f :: rest =>
      if f.isObj then { st with mode := .after, stack := rest, closed := f.keys :: st.closed }
      else failJ st
    | [] => failJ st

-- A mask that may carry a quote, a backslash or a control byte.
#tooth jsonRedaction_preserves_valid_parse_and_keys by
  mutation isSafeMaskByte := fun _ => true

-- A leaf message with the node prefix.
#tooth leaf_as_node_collision by
  mutation leafPrefix := 0x01

-- A span verifier that does not compare the climbed digest with the root.
#tooth verifySpanMerkleInclusion_binding by
  mutation topMatches := fun _ _ => true

/-! ## 7. The axiom census -/

#assert_axioms_tree

end Obend.Tests.Metasystem.RegexBisimAndVpaComplementTest

end
