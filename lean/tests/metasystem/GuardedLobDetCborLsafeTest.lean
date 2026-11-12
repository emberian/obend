module
/-
# GuardedLobDetCborLsafeTest — vectors, attack fixtures and mutation teeth for cards K4, K9, K10

Exercises `Obend.Logic.GuardedLob`, `Obend.Codec.DetCbor` and `Obend.Vault.Lsafe` together:

1. **GuardedLob**: the quotient-lift tracker equation by `rfl`, the C4 diamond and the classic
   inconsistent hierarchy, a single-inheritance prepend, a `superClaimCheck` certificate
   transported under an overriding wrapper by `c4Prepend_preserves_superClaimCert`, an epoch
   change that preserves one call and not another, and divergence by Löb induction.
2. **DetCbor**: RFC 8949 Appendix A vectors in both directions, and the refusals: non-minimal
   widths, indefinite lengths, duplicate and out-of-order map keys, invalid UTF-8, trailing bytes.
3. **Lsafe**: an accepted scalar redaction, and the four attacks refused: trailing backslash
   (byte 92), CRLF, tag breakout, duplicate key; the open-world query with and without a token;
   forget-then-merge executed on a 16-bucket vault, and a forged base proof refused.
4. **Teeth**: each `#tooth` replaces one real check and reports that a stored proof no longer
   checks.

Concrete runs that hash use `toyHasher`, a 32-byte fold: the theorems hold for every `Hasher`,
and Keccak in the kernel would only measure the kernel.
-/

public import Obend.Tactic.Tooth
public import Obend.Logic.GuardedLob
public import Obend.Codec.DetCbor
public import Obend.Vault.Lsafe
import all Obend.Logic.SuperRefines
import all Obend.Logic.GuardedLob
import all Obend.Codec.DetCbor
import all Obend.Vault.Lsafe

public section

namespace Obend.Tests.Metasystem.GuardedLobDetCborLsafeTest

open Obend.Core.Term
open Obend.Logic
open Obend.Logic.GuardedLob
open Obend.Codec.DetCbor
open Obend.Vault.Lsafe

set_option autoImplicit false

/-! ## 1. GuardedLob -/

example {X Z : Type} {A : AsmCore4 X} {C : AsmCore4 Z} (R : X → X → Prop) (f : AsmCore4Hom A C)
    (h : ∀ x₁ x₂, R x₁ x₂ → f.specFun x₁ = f.specFun x₂) :
    (f.quotLift R h).tracker = f.tracker := rfl

example {X Z : Type} {A : AsmCore4 X} {C : AsmCore4 Z} (R : X → X → Prop) (f : AsmCore4Hom A C)
    (h : ∀ x₁ x₂, R x₁ x₂ → f.specFun x₁ = f.specFun x₂) (a : X) :
    (f.quotLift R h).specFun (Quot.mk R a) = f.specFun a := rfl

/-- The self-returning object has no value: Löb induction, not a fuel bound. -/
example : ¬ ∃ v, Evaluates (.fix selfLoopSpec (.record [])) v :=
  fun ⟨v, hv⟩ => selfLoop_diverges (.record []) v hv

def stubLayer (n : String) : Layer := { name := n, metadata := .record [], fields := [] }

/-- `O`, `A : O`, `B : O`, `C : A, B`. -/
def diamond : List LayerNode :=
  [⟨"O", stubLayer "O", []⟩, ⟨"A", stubLayer "A", ["O"]⟩, ⟨"B", stubLayer "B", ["O"]⟩,
    ⟨"C", stubLayer "C", ["A", "B"]⟩]

example : c4Linearize diamond "C" = some ["C", "A", "B", "O"] := by decide +kernel
example : c4Linearize diamond "A" = some ["A", "O"] := by decide +kernel
example : (c4Composition diamond "C" []).map (fun C => C.layers.map (·.name)) =
    some ["C", "A", "B", "O"] := by decide +kernel

/-- `X : A, B` and `Y : B, A` disagree on the order of `A` and `B`: `Z : X, Y` has no
linearization. -/
def inconsistent : List LayerNode :=
  [⟨"O", stubLayer "O", []⟩, ⟨"A", stubLayer "A", ["O"]⟩, ⟨"B", stubLayer "B", ["O"]⟩,
    ⟨"X", stubLayer "X", ["A", "B"]⟩, ⟨"Y", stubLayer "Y", ["B", "A"]⟩,
    ⟨"Z", stubLayer "Z", ["X", "Y"]⟩]

example : c4Linearize inconsistent "X" = some ["X", "A", "B", "O"] := by decide +kernel
example : c4Linearize inconsistent "Z" = none := by decide +kernel

/-- A cycle has no linearization. -/
example : c4Linearize [⟨"P", stubLayer "P", ["Q"]⟩, ⟨"Q", stubLayer "Q", ["P"]⟩] "P" = none := by
  decide +kernel

/-- The accepted certificate of `SuperRefines`' open-recursion witness stays accepted under the
`"apply"`-overriding wrapper: only its `self` support `"scale"` is asked of the wrapper. -/
example :
    superClaimCheck 15
      { verticalOpenRecClaimObj with
        comp := prependLayers verticalOpenRecClaimObj.comp auditWrapperLayer []
        layer := ([] : List Layer).length + 1 + verticalOpenRecClaimObj.layer }
      verticalOpenRecSteps = .ok :=
  (c4Prepend_preserves_superClaimCert (by decide +kernel) auditWrapperLayer []
    (List.all_eq_true.1 (by decide +kernel)) (by decide +kernel)).1

def epochOne : EpochBook := ⟨#[("fee", .nat 3), ("limit", .nat 10), ("rate", .nat 2)]⟩
def epochTwo : EpochBook := ⟨#[("fee", .nat 4), ("limit", .nat 10), ("rate", .nat 2)]⟩

/-- `limit * rate`: references only keys the change left alone. -/
def stableCall : EpochCall := ⟨#["limit", "rate"], .binary .multiply (.bound 0) (.bound 1)⟩
/-- `limit + fee`: references the changed key. -/
def feeCall : EpochCall := ⟨#["limit", "fee"], .binary .add (.bound 0) (.bound 1)⟩

example : verifyChangeCertExec epochOne epochTwo #["limit", "rate"] = true := by decide +kernel
example : verifyChangeCertExec epochOne epochTwo #["fee", "limit"] = false := by decide +kernel
example : usesOnlyExec #["limit", "rate"] stableCall = true := by decide +kernel
example : usesOnlyExec #["limit", "rate"] feeCall = false := by decide +kernel
example : optTermEq (lookupEpochFast epochTwo "rate") (some (.nat 2)) = true := by decide +kernel
example : (lookupEpochFast epochTwo "absent").isSome = false := by decide +kernel

/-- The stable call evaluates identically in both epochs at every fuel, by the certificate. -/
example (fuel : Nat) : evalAgainst epochOne fuel stableCall = evalAgainst epochTwo fuel stableCall :=
  changeCert_preservedOn_exec (U := #["limit", "rate"]) (by decide +kernel) stableCall
    (by decide +kernel) fuel

example : Obend.Law.termEq ((evalAgainst epochOne 5 stableCall).getD (.nat 0)) (.nat 20) = true := by
  decide +kernel
/-- The call on the changed key is not preserved. -/
example : Obend.Law.termEq ((evalAgainst epochOne 5 feeCall).getD (.nat 0)) (.nat 13) = true ∧
    Obend.Law.termEq ((evalAgainst epochTwo 5 feeCall).getD (.nat 0)) (.nat 14) = true := by
  decide +kernel

/-! ## 2. DetCbor: RFC 8949 Appendix A vectors -/

def hex (l : List UInt8) : ByteArray := ⟨l.toArray⟩

example : encodeDetCbor (.uint 0) = hex [0x00] := by decide +kernel
example : encodeDetCbor (.uint 23) = hex [0x17] := by decide +kernel
example : encodeDetCbor (.uint 24) = hex [0x18, 0x18] := by decide +kernel
example : encodeDetCbor (.uint 1000) = hex [0x19, 0x03, 0xe8] := by decide +kernel
example : encodeDetCbor (.uint 1000000) = hex [0x1a, 0x00, 0x0f, 0x42, 0x40] := by decide +kernel
example : encodeDetCbor (.uint 18446744073709551615) =
    hex [0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] := by decide +kernel
/-- `-1`, `-100`, `-18446744073709551616`. -/
example : encodeDetCbor (.nint 0) = hex [0x20] := by decide +kernel
example : encodeDetCbor (.nint 99) = hex [0x38, 0x63] := by decide +kernel
example : encodeDetCbor (.nint 18446744073709551615) =
    hex [0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] := by decide +kernel
example : encodeDetCbor (.simpleBool false) = hex [0xf4] ∧
    encodeDetCbor (.simpleBool true) = hex [0xf5] := by decide +kernel
example : encodeDetCbor (.bytes (hex [1, 2, 3, 4])) = hex [0x44, 0x01, 0x02, 0x03, 0x04] := by
  decide +kernel
example : encodeDetCbor (CborVal.ofString "IETF") = hex [0x64, 0x49, 0x45, 0x54, 0x46] := by
  decide +kernel
example : encodeDetCbor (CborVal.ofString "\u00fc") = hex [0x62, 0xc3, 0xbc] := by decide +kernel

/-- `[1, [2, 3], [4, 5]]`. -/
def nestedArray : CborVal :=
  .array [.uint 1, .array [.uint 2, .uint 3], .array [.uint 4, .uint 5]]

example : encodeDetCbor nestedArray = hex [0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05] := by
  decide +kernel
example : decodeDetCbor (hex [0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05]) =
    some nestedArray := by decide +kernel

/-- `{"a": 1, "b": [2, 3]}`. -/
def abMap : CborVal :=
  .map [(CborVal.ofString "a", .uint 1), (CborVal.ofString "b", .array [.uint 2, .uint 3])]

example : encodeDetCbor abMap = hex [0xa2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03] := by
  decide +kernel
example : decodeDetCbor (hex [0xa2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03]) =
    some abMap := by decide +kernel
example : CanonicalCbor abMap = true := by decide +kernel

/-- Keys sort by encoded bytes: `10` (`0x0a`) before `100` (`0x18 0x64`) before `-1` (`0x20`)
before `"z"` (`0x61 0x7a`) before `"aa"` (`0x62 0x61 0x61`) before `[100]` before `false`:
the RFC 8949 §4.2.1 example order. A map keyed by a nested map decodes too. -/
def mixedKeyMap : CborVal :=
  .map [(.uint 10, .uint 0), (.uint 100, .uint 0), (.nint 0, .uint 0),
    (CborVal.ofString "z", .uint 0), (CborVal.ofString "aa", .uint 0),
    (.array [.uint 100], .uint 0), (.map [(.uint 1, .uint 2)], .uint 0),
    (.simpleBool false, .uint 0)]

example : CanonicalCbor mixedKeyMap = true := by decide +kernel
example : decodeDetCbor (encodeDetCbor mixedKeyMap) = some mixedKeyMap := by decide +kernel
/-- The same theorem, universally. -/
example (v : CborVal) (h : CanonicalCbor v = true) : decodeDetCbor (encodeDetCbor v) = some v :=
  decodeDetCbor_encodeDetCbor v h

/-! ### Refusals -/

/-- `0x18 0x05`: the argument 5 in a one-byte extension. -/
example : decodeDetCbor (hex [0x18, 0x05]) = none := by decide +kernel
/-- 23 in one byte, 255 in two, 65535 in four, `2^32 - 1` in eight. -/
example : decodeDetCbor (hex [0x18, 0x17]) = none ∧ decodeDetCbor (hex [0x19, 0x00, 0xff]) = none ∧
    decodeDetCbor (hex [0x1a, 0x00, 0x00, 0xff, 0xff]) = none ∧
    decodeDetCbor (hex [0x1b, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff]) = none := by
  decide +kernel
/-- The boundary values themselves are accepted. -/
example : decodeDetCbor (hex [0x18, 0x18]) = some (.uint 24) ∧
    decodeDetCbor (hex [0x19, 0x01, 0x00]) = some (.uint 256) := by decide +kernel
/-- A non-minimal length on a nested byte string. -/
example : decodeDetCbor (hex [0x81, 0x58, 0x01, 0x00]) = none := by decide +kernel
/-- Indefinite-length array, map, byte string and text; reserved additional information. -/
example : decodeDetCbor (hex [0x9f, 0x01, 0xff]) = none ∧ decodeDetCbor (hex [0xbf, 0xff]) = none ∧
    decodeDetCbor (hex [0x5f, 0x41, 0x00, 0xff]) = none ∧
    decodeDetCbor (hex [0x7f, 0xff]) = none ∧ decodeDetCbor (hex [0x1c]) = none := by
  decide +kernel
/-- Duplicate key `{1: 0, 1: 0}`. -/
example : decodeDetCbor (hex [0xa2, 0x01, 0x00, 0x01, 0x00]) = none := by decide +kernel
/-- Out-of-order keys `{2: 0, 1: 0}`; the sorted form is accepted. -/
example : decodeDetCbor (hex [0xa2, 0x02, 0x00, 0x01, 0x00]) = none ∧
    decodeDetCbor (hex [0xa2, 0x01, 0x00, 0x02, 0x00]) =
      some (.map [(.uint 1, .uint 0), (.uint 2, .uint 0)]) := by decide +kernel
/-- Length-first order (RFC 7049) is not bytewise order: `"aa"` before `"z"` is refused. -/
example : decodeDetCbor (hex [0xa2, 0x62, 0x61, 0x61, 0x00, 0x61, 0x7a, 0x00]) = none := by
  decide +kernel
/-- Invalid UTF-8 in a text string: a lone continuation byte, an overlong, a surrogate. -/
example : decodeDetCbor (hex [0x61, 0x80]) = none ∧ decodeDetCbor (hex [0x62, 0xc0, 0xaf]) = none ∧
    decodeDetCbor (hex [0x63, 0xed, 0xa0, 0x80]) = none := by decide +kernel
/-- Trailing bytes, a truncated item, the empty input, a float, a tag. -/
example : decodeDetCbor (hex [0x01, 0x02]) = none ∧ decodeDetCbor (hex [0x82, 0x01]) = none ∧
    decodeDetCbor (hex []) = none ∧ decodeDetCbor (hex [0xf9, 0x3c, 0x00]) = none ∧
    decodeDetCbor (hex [0xc0, 0x00]) = none := by decide +kernel
/-- A duplicate key is not canonical, and a non-canonical value does not decode back. -/
example : CanonicalCbor (.map [(.uint 1, .uint 0), (.uint 1, .uint 0)]) = false ∧
    decodeDetCbor (encodeDetCbor (.map [(.uint 2, .uint 0), (.uint 1, .uint 0)])) = none := by
  decide +kernel

example : lexLtBytes (hex [0x0a]) (hex [0x18, 0x64]) = true ∧
    lexLtBytes (hex [0x61]) (hex [0x61, 0x00]) = true ∧
    lexLtBytes (hex [0x61, 0x00]) (hex [0x61]) = false := by decide +kernel
example : (CborVal.array [.uint 1] : CborVal) ≠ .array [.uint 2] := by decide +kernel

/-! ## 3. Lsafe -/

/-- `{"a":"secret","b":1}`; `secret` is bytes 6 to 12. -/
def secretDoc : ByteArray := "{\"a\":\"secret\",\"b\":1}".toByteArray

example : runLsafeVpa secretDoc = true := by decide +kernel
example : objectKeysOf secretDoc = [["b".toByteArray, "a".toByteArray]] := by decide +kernel
example : checkLsafeRedaction secretDoc 6 12 "XXXX".toByteArray = true := by decide +kernel
example : spliceByteArray secretDoc 6 12 "XXXX".toByteArray = "{\"a\":\"XXXX\",\"b\":1}".toByteArray := by
  decide +kernel
/-- The universal theorem at this redaction: accepted, and the key sets are the same. -/
example : runLsafeVpa (spliceByteArray secretDoc 6 12 "XXXX".toByteArray) = true ∧
    objectKeysOf (spliceByteArray secretDoc 6 12 "XXXX".toByteArray) = objectKeysOf secretDoc :=
  have h := lsafe_redaction_confinement (doc := secretDoc) (l := 6) (r := 12)
    (replacement := "XXXX".toByteArray) (by decide +kernel)
  ⟨h.1, h.2.2.2.2.1⟩
/-- An empty replacement and an empty span are safe. -/
example : checkLsafeRedaction secretDoc 6 12 ByteArray.empty = true ∧
    checkLsafeRedaction secretDoc 8 8 "[redacted]".toByteArray = true := by decide +kernel

/-- **Attack 1**: a trailing backslash (byte 92) would eat the closing quote. -/
example : checkLsafeRedaction secretDoc 6 12 "XX\\".toByteArray = false := by decide +kernel
/-- What the splice would have been: the document no longer passes. -/
example : runLsafeVpa (spliceByteArray secretDoc 6 12 "XX\\".toByteArray) = false := by decide +kernel
/-- **Attack 2**: CRLF. -/
example : checkLsafeRedaction secretDoc 6 12 "a\r\nb".toByteArray = false := by decide +kernel
/-- **Attack 3**: tag breakout. -/
example : checkLsafeRedaction secretDoc 6 12 "</s>".toByteArray = false ∧
    checkLsafeRedaction secretDoc 6 12 ">".toByteArray = false := by decide +kernel
/-- A quote, which would close the string and open a new member. -/
example : checkLsafeRedaction secretDoc 6 12 "x\",\"a\":\"y".toByteArray = false := by decide +kernel
/-- **Attack 4**: a duplicate key. The document with one is refused outright, and a redaction
inside a key (here the `b` at byte 15) is refused, so no redaction can create one. -/
example : runLsafeVpa "{\"a\":1,\"a\":2}".toByteArray = false := by decide +kernel
example : checkLsafeRedaction secretDoc 15 16 "a".toByteArray = false := by decide +kernel
/-- Duplicates are found at any depth, and equal keys in different objects are fine. -/
example : runLsafeVpa "{\"o\":{\"k\":1,\"j\":2,\"k\":3}}".toByteArray = false ∧
    runLsafeVpa "[{\"k\":1},{\"k\":2}]".toByteArray = true := by decide +kernel
/-- A backslash in a key is refused (`"\u0061"` would be a second `"a"`). -/
example : runLsafeVpa "{\"a\":1,\"\\u0061\":2}".toByteArray = false := by decide +kernel
/-- A span that crosses the closing quote, one outside any string, one past the end. -/
example : checkLsafeRedaction secretDoc 6 13 "X".toByteArray = false ∧
    checkLsafeRedaction secretDoc 13 14 "X".toByteArray = false ∧
    checkLsafeRedaction secretDoc 6 99 "X".toByteArray = false := by decide +kernel
/-- An escaped quote inside a value does not close it; the span right after a backslash is not
strictly inside the string and is refused. -/
example : runLsafeVpa "{\"a\":\"x\\\"y\"}".toByteArray = true ∧
    checkLsafeRedaction "{\"a\":\"x\\\"y\"}".toByteArray 8 9 "z".toByteArray = false := by decide +kernel
/-- Unbalanced and mismatched brackets, an unclosed string. -/
example : runLsafeVpa "{\"a\":[1,2}".toByteArray = false ∧ runLsafeVpa "[1,2".toByteArray = false ∧
    runLsafeVpa "{\"a\":\"x}".toByteArray = false := by decide +kernel

example : keysDistinctB ["b".toByteArray, "a".toByteArray, "c".toByteArray] = true ∧
    keysDistinctB ["b".toByteArray, "a".toByteArray, "b".toByteArray] = false := by decide +kernel

/-- A 32-byte fold for concrete runs. -/
def toyHasher : Hasher where
  hash tag m :=
    ⟨((List.range 32).map fun i =>
      UInt8.ofNat (m.data.toList.foldl (fun acc b => (acc * 31 + b.toNat + i) % 65521)
        (tag.length + 7))).toArray⟩
  size_eq tag m := by
    show (((List.range 32).map _).toArray).size = 32
    rw [List.size_toArray, List.length_map, List.length_range]

def edgeA : KgEdge := ⟨7, hex [1], hex [10]⟩
def edgeB : KgEdge := ⟨7, hex [1], hex [20]⟩
/-- The slice for predicate 7 and subject `01`, sorted by key. -/
def slice : Array KgEdge := #[edgeA, edgeB]
def graphDigest : ByteArray := edgesDigest toyHasher slice
def authKey : ByteArray := hex [42]

-- One edge opens to the graph digest by its own path; no other edge is presented.
example : verifyKgEdgeOpening toyHasher graphDigest edgeB (openKgEdge toyHasher slice 1) = true ∧
    evalOpenedKgQuery toyHasher graphDigest 7 (hex [1]) (hex [20])
      (some (openKgEdge toyHasher slice 1)) = .entailed := by decide +kernel
-- Refused: another edge on that path, the edge at another index, a claimed count of three, and
-- no opening at all (undetermined, never refuted).
example : verifyKgEdgeOpening toyHasher graphDigest ⟨7, hex [1], hex [21]⟩
      (openKgEdge toyHasher slice 1) = false ∧
    verifyKgEdgeOpening toyHasher graphDigest edgeB (openKgEdge toyHasher slice 0) = false ∧
    verifyKgEdgeOpening toyHasher graphDigest edgeB
      ⟨3, (openKgEdge toyHasher slice 1).proof⟩ = false ∧
    evalOpenedKgQuery toyHasher graphDigest 7 (hex [1]) (hex [21])
      (some (openKgEdge toyHasher slice 1)) = .undetermined ∧
    evalOpenedKgQuery toyHasher graphDigest 7 (hex [1]) (hex [20]) none = .undetermined := by
  decide +kernel
-- The digest binds the count: the slice and its one-edge prefix have different digests.
example : edgesDigest toyHasher slice ≠ edgesDigest toyHasher #[edgeA] := by decide +kernel

def sliceToken : CompletenessToken :=
  let t : CompletenessToken := ⟨graphDigest, 7, hex [1], edgesDigest toyHasher slice, ByteArray.empty⟩
  { t with issuerTag32 := tokenMac toyHasher authKey t }

/-- An edge in the committed graph is entailed. -/
example : evalOpenWorldKgQuery toyHasher graphDigest authKey 7 (hex [1]) (hex [20]) slice none =
    .entailed := by decide +kernel
/-- **The forgery**: presenting no edges and no token proves nothing. -/
example : evalOpenWorldKgQuery toyHasher graphDigest authKey 7 (hex [1]) (hex [20]) #[] none =
    .undetermined := by decide +kernel
/-- An absent edge is undetermined without a token and refuted with the issuer's token. -/
example : evalOpenWorldKgQuery toyHasher graphDigest authKey 7 (hex [1]) (hex [30]) slice none =
    .undetermined ∧
    evalOpenWorldKgQuery toyHasher graphDigest authKey 7 (hex [1]) (hex [30]) slice
      (some sliceToken) = .refuted := by decide +kernel
/-- The token does not cover a truncated witness, another subject, or another verifier key. -/
example : evalOpenWorldKgQuery toyHasher graphDigest authKey 7 (hex [1]) (hex [20]) #[edgeA]
      (some sliceToken) = .undetermined ∧
    evalOpenWorldKgQuery toyHasher graphDigest authKey 7 (hex [2]) (hex [30]) slice
      (some sliceToken) = .undetermined ∧
    evalOpenWorldKgQuery toyHasher graphDigest (hex [43]) 7 (hex [1]) (hex [30]) slice
      (some sliceToken) = .undetermined := by decide +kernel

/-- Sixteen one-entry buckets: bucket `i` maps key `i` to `1`. -/
def demoBase : Array BucketEntries :=
  ((List.range 16).map fun i => [(hex [UInt8.ofNat i], hex [1])]).toArray

def demoLive : Array BucketEntries :=
  demoBase.setIfInBounds 5 [(hex [5], hex [1]), (hex [77], hex [7])]

def demoFork : OpenFork :=
  ⟨merkleRoot16 toyHasher demoBase, ⟨5, by decide⟩, [(hex [5], hex [99])]⟩

/-- A fork is open; the base is forgotten anyway. -/
def demoVault : ShardedVault := ⟨demoLive, demoBase, [demoFork.baseRoot32]⟩

/-- **Forget, then merge, executed**: the fork's write to key 5 lands, the live write to key 77
survives, and the fork is no longer open. -/
example :
    (mergeAfterForgetWithBaseProof toyHasher (forgetHistoricalBase toyHasher demoVault) demoFork
      (extractBaseProof toyHasher demoBase demoFork.touchedBucketIdx)).map
        (fun c => (c.liveBuckets.getD 5 [], c.openForks)) =
      some ([(hex [5], hex [99]), (hex [77], hex [7])], []) := by decide +kernel

/-- The square commutes at this vault, by the theorem. -/
example :
    mergeAfterForgetWithBaseProof toyHasher (forgetHistoricalBase toyHasher demoVault) demoFork
      (extractBaseProof toyHasher demoBase demoFork.touchedBucketIdx) =
      some (forgetHistoricalBase toyHasher (mergeWithFullBase demoVault demoBase demoFork)) :=
  (forget_commutes_with_fork_merge toyHasher demoVault demoFork (by decide +kernel)
    (by decide +kernel) rfl).2

/-- A forged base bucket on the honest path does not verify, and neither does the honest
bucket at the wrong index. -/
example :
    verifyBaseProof toyHasher demoFork.baseRoot32 demoFork.touchedBucketIdx
      ⟨[(hex [5], hex [66])], (extractBaseProof toyHasher demoBase demoFork.touchedBucketIdx).siblings⟩ =
        false ∧
    verifyBaseProof toyHasher demoFork.baseRoot32 ⟨6, by decide⟩
      (extractBaseProof toyHasher demoBase demoFork.touchedBucketIdx) = false := by
  decide +kernel

/-- A hasher with one digest: every pair of messages collides. -/
def constHasher : Hasher where
  hash _ _ := hex (List.replicate 32 0)
  size_eq _ _ := rfl

def zeroPath : List ByteArray := List.replicate 4 (hex (List.replicate 32 0))

/-- **Collision extraction runs.** Under the constant hasher two different buckets open at one
index to one root; `baseProofCollision` returns the two bucket messages themselves. -/
example :
    (match baseProofCollision constHasher (root := hex (List.replicate 32 0)) (idx := ⟨3, by decide⟩)
        (p₁ := ⟨[(hex [1], hex [2])], zeroPath⟩) (p₂ := ⟨[(hex [1], hex [9])], zeroPath⟩)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) with
      | .leaf c => decide (c.m₁ = bucketMsg [(hex [1], hex [2])] ∧
          c.m₂ = bucketMsg [(hex [1], hex [9])])
      | .node _ => false) = true := by decide +kernel

/-! ## 4. Mutation teeth -/

-- K4: a certificate verifier that does not compare the bodies on `U`.
#tooth changeCert_preservedOn_sound by
  mutation checkPreservedOnExec := fun _ _ _ => true

-- K4: a C4 merge that accepts a head occurring in another sequence's tail.
#tooth c4Merge_nodup by
  mutation c4Good := fun _ _ => true

-- DetCbor: a head reader that accepts `0x18` with an argument below 24.
#tooth decodeDetCbor_encode_of_some by
  mutation argWidth := fun ai =>
    if ai = 24 then some (1, 0)
    else if ai = 25 then some (2, 256)
    else if ai = 26 then some (4, 65536)
    else if ai = 27 then some (8, 4294967296)
    else none

-- DetCbor: a map check that accepts keys in any order, duplicates included.
#tooth canonicalMap_keys_nodup by
  mutation keyOrderOk := fun _ _ _ => true

-- DetCbor: a head byte that drops the major type, so `uint` and `nint` collide.
#tooth encodeDetCbor_injective by
  mutation headByte := fun _ ai => UInt8.ofNat ai

-- Lsafe: a safe-byte predicate that lets byte 92, CR, LF, `<` and `>` through.
#tooth lsafe_redaction_confinement by
  mutation isSafeRedactionByte := fun b =>
    decide (0x20 ≤ b.toNat) && decide (b.toNat ≤ 0x7e) && b != 0x22

-- Lsafe: a mask byte predicate that lets the quote and the backslash through.
#tooth lsafe_redaction_confinement by
  mutation Obend.Judge.VpaJson.isSafeMaskByte := fun b =>
    decide (0x20 ≤ b.toNat) && decide (b.toNat ≤ 0x7e)

-- Lsafe: a string machine that ignores the backslash.
#tooth lsafe_redaction_confinement by
  mutation Obend.Judge.VpaJson.stepStr := fun _ b =>
    if b == 0x22 then .close else .cont .normal

-- Lsafe: closing an object without the duplicate-key check.
#tooth lsafe_object_keys_nodup by
  mutation Obend.Judge.VpaJson.closeObject := fun st =>
    match st.stack with
    | f :: rest =>
      if f.isObj then { st with mode := .after, stack := rest, closed := f.keys :: st.closed }
      else Obend.Judge.VpaJson.failJ st
    | [] => Obend.Judge.VpaJson.failJ st

-- Lsafe: an edge opening that does not compare the climbed digest with the graph digest.
#tooth verifyKgEdgeOpening_binding by
  mutation Obend.Judge.VpaJson.topMatches := fun _ _ _ _ => true

-- Lsafe: a graph digest that leaves the edge count out.
#tooth verifyKgEdgeOpening_binding by
  mutation Obend.Judge.VpaJson.rootHash := fun H tag _ t =>
    H.hash tag (Obend.Judge.VpaJson.rootMsg
      (Obend.Judge.VpaJson.leafHash H tag (Obend.Judge.Commit.countSpan 0)) t)

-- Lsafe: an evaluator that refutes wherever it does not entail, token or not.
#tooth openWorld_without_token_never_refutes by
  mutation evalOpenWorldKgQuery := fun H g a p s o edges tok? =>
    if (tokenOk H g a p s edges tok? || graphOk H g edges) && containsEdge edges ⟨p, s, o⟩ then
      .entailed
    else .refuted

-- K10: a path extractor that pairs each node with itself.
#tooth forget_commutes_with_fork_merge by
  mutation sibIdx := fun i => i

-- K10: a base-proof verifier that does not check sibling width.
#tooth baseProof_binding_collision by
  mutation verifyBaseProof := fun H root idx p =>
    p.siblings.length == 4 && bucketFits p.baseBucketBefore &&
      decide (climb H idx.val (bucketHash H p.baseBucketBefore) p.siblings = root)

/-! ## 5. Axiom audit -/

#print axioms fix_lob
#print axioms guardedFix_unique
#print axioms openRec_stepContract_lob
#print axioms c4Merge_nodup
#print axioms c4Merge_sublist_precedence
#print axioms c4Prepend_preserves_superClaimCert
#print axioms lookupEpochFast_eq_spec
#print axioms changeCert_preservedOn_sound
#print axioms AsmCore4Hom.quotLift_tracker_rfl
#print axioms decodeDetCbor_encodeDetCbor
#print axioms encodeDetCbor_injective
#print axioms decodeDetCbor_canonical
#print axioms decodeDetCbor_encode_of_some
#print axioms canonicalMap_keys_nodup
#print axioms lsafe_redaction_confinement
#print axioms lsafe_object_keys_nodup
#print axioms openWorld_without_token_never_refutes
#print axioms completenessToken_refute_sound
#print axioms forget_commutes_with_fork_merge
#print axioms baseProofCollision
#print axioms baseProof_binding_collision
#print axioms cshake_baseProof_binding

end Obend.Tests.Metasystem.GuardedLobDetCborLsafeTest

end
