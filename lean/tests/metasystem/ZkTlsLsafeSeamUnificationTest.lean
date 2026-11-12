module
/-
# ZkTlsLsafeSeamUnificationTest — one JSON machine, one span tree, one call tree, end to end

The seam this file holds shut: `Obend.Vault.Lsafe`, `Obend.Judge.TranscriptPolicy`,
`Obend.Judge.DecoAndCallTree` and `Obend.Trailblaze.ZkStripe` used to carry their own lexers,
masks and digests. They now share `Obend.Judge.VpaJson`'s RFC 8259 machine and span tree and
`Obend.Judge.SymbolicRegex`'s expressions.

1. **Escaped quote.** Redacting the backslash of `\"` inside a JSON string is refused by
   `checkJsonRedaction`, by `Lsafe.checkLsafeRedaction` and by `DecoAndCallTree.checkMask`; the
   same span moved one byte, or widened to the whole escape, is accepted.
2. **Reflected `subtree_root`.** A nested or quoted occurrence is not a depth-1 member.
3. **Forged GHASH.** A flipped tag bit, a changed ciphertext block, a changed header field (the
   authenticated commitment) are each refused by `checkDecoAttestation`.
4. **End to end.** A three-hop zkTLS call tree is verified and judged with its openings; one
   knowledge-graph edge about it opens to the `Lsafe` graph digest by its own Merkle path; the
   `ZkStripe` audit admits the tree's carrier under a 256-bit digest; the three byte formats
   round-trip.

Kernel runs (`decide +kernel`) touch no hash. Everything that hashes with cSHAKE256 runs compiled,
under `#guard`.
-/
public import Obend.Tactic.Tooth
public import Obend.Vault.Lsafe
public import Obend.Judge.DecoAndCallTree
public import Obend.Trailblaze.ZkStripe
import all Obend.Codec.DetCbor
import all Obend.Crypto.BinaryTower256
import all Obend.Judge.Class
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Judge.VpaComplementAndJson
import all Obend.Judge.TranscriptPolicy
import all Obend.Judge.DecoAndCallTree
import all Obend.Vault.Lsafe
import all Obend.Trailblaze.ZkStripe
import all Obend.Tactic.Tooth
public meta import Obend.Digest.Cshake256
public meta import Obend.Crypto.BinaryTower256
public meta import Obend.Judge.Class
public meta import Obend.Judge.SymbolicRegexBisim
public meta import Obend.Judge.VpaComplementAndJson
public meta import Obend.Judge.DecoAndCallTree
public meta import Obend.Vault.Lsafe
public meta import Obend.Trailblaze.ZkStripe

public section

namespace Obend.Tests.Metasystem.ZkTlsLsafeSeamUnificationTest

open Obend.Crypto.BinaryTower256
open Obend.Judge.DecoAndCallTree
open Obend.Judge.VpaJson (JState spanMerkleRoot spanMerkleProof spanTag checkJsonRedaction
  runFullJsonGrammar)
open Obend.Judge.Commit (cshakeHasher spliceByteArray)

set_option autoImplicit false

meta def js (s : String) : ByteArray := s.toByteArray

/-! ## 1. The escaped quote, at all three layers (kernel) -/

/-- `{"note":"x\"y"}`: byte 10 is the backslash, byte 11 the quote it escapes. -/
def noteDoc : ByteArray := "{\"note\":\"x\\\"y\"}".toByteArray
def star : ByteArray := "*".toByteArray

-- Refused: the backslash alone, at the JSON judge, at the vault, and as a hidden span.
example : checkJsonRedaction noteDoc 10 11 star = false := by decide +kernel
example : Obend.Vault.Lsafe.checkLsafeRedaction noteDoc 10 11 star = false := by decide +kernel
example : checkMask JState.init
    [.opened "{\"note\":\"x".toByteArray [], .masked star, .opened "\"y\"}".toByteArray []]
    ["{\"note\":\"x".toByteArray, "\\".toByteArray, "\"y\"}".toByteArray] = false := by
  decide +kernel
-- What the refusal protects: with the backslash gone the quote closes the string early.
example : runFullJsonGrammar (spliceByteArray noteDoc 10 11 star) = false := by decide +kernel
-- Accepted: the byte before it, and the whole escape pair.
example : checkJsonRedaction noteDoc 9 10 star = true ∧ checkJsonRedaction noteDoc 10 12 star = true ∧
    Obend.Vault.Lsafe.checkLsafeRedaction noteDoc 9 10 star = true := by decide +kernel
example : checkMask JState.init
    [.opened "{\"note\":\"x".toByteArray [], .masked star, .opened "y\"}".toByteArray []]
    ["{\"note\":\"x".toByteArray, "\\\"".toByteArray, "y\"}".toByteArray] = true := by
  decide +kernel

/-! ## 2. Reflected `subtree_root` (kernel) -/

def zeroRoot : Hash256 := ⟨⟨(List.replicate 32 (0 : UInt8)).toArray⟩, by decide⟩
def zeros : String := "0000000000000000000000000000000000000000000000000000000000000000"
def respView (body : String) : TranscriptView :=
  ⟨⟨2, ByteArray.empty⟩, [.opened "HTTP/1.1 200 OK\r\n\r\n".toByteArray [], .opened body.toByteArray []]⟩

example : checkSubtreeRoot (respView ("{\"subtree_root\":\"" ++ zeros ++ "\"}")) zeroRoot = true := by
  decide +kernel
-- Refused: nested in an object, and inside an escaped string value.
example : checkSubtreeRoot (respView ("{\"data\":{\"subtree_root\":\"" ++ zeros ++ "\"}}")) zeroRoot =
    false := by decide +kernel
example : checkSubtreeRoot
    (respView ("{\"user_bio\":\"...\\\"subtree_root\\\":\\\"" ++ zeros ++ "\\\"...\"}")) zeroRoot =
    false := by decide +kernel

/-! ## 3. A three-hop call tree with real commitments (compiled) -/

meta def viewOf (spans : List ByteArray) (masks : List (Nat × ByteArray)) : TranscriptView :=
  ⟨spanMerkleRoot cshakeHasher spanTag spans,
    (List.range spans.length).map fun i =>
      match masks.lookup i with
      | some m => .masked m
      | none => .opened (spans.getD i ByteArray.empty)
          (spanMerkleProof cshakeHasher spanTag spans i).siblings⟩

meta def mkAttestation (k : Tower128) (hdr : SessionHeader) (req resp : TranscriptView)
    (ct : List Tower128) (len : Tower128) : DecoAttestation :=
  let a0 : DecoAttestation := ⟨hdr, req, resp, ct, len, towerZero 7⟩
  { a0 with ghashTag := ghashAuth k (commitBlocks (recordCommit a0)) ct len }

meta def notary : ByteArray := js "notary-1"
meta def stripeHost : ByteArray := js "api.stripe.com"
meta def recorderHost : ByteArray := js "recorder.obend.org"
meta def key1 : Tower128 := unpackTower 7 0x0123456789abcdef0fedcba987654321
meta def key2 : Tower128 := unpackTower 7 0x1111222233334444aaaabbbbccccdddd

/-- The settlement request: the API key is span 4, hidden. -/
meta def settleReq : List ByteArray :=
  [js "POST /v1/pay HTTP/1.1\r\nHost: api.stripe.com\r\n\r\n", js "{\"amount\":\"", js "4200",
   js "\",\"key\":\"", js "sk_live_99", js "\"}"]
meta def settleResp : List ByteArray :=
  [js "HTTP/1.1 200 OK\r\n\r\n", js "{\"id\":\"", js "pi_3Q9x77", js "\",\"status\":\"succeeded\"}"]

meta def settlement : DecoAttestation :=
  mkAttestation key1 ⟨stripeHost, notary, 100, js "n1", js "pi_1"⟩
    (viewOf settleReq [(4, js "****")]) (viewOf settleResp [])
    [unpackTower 7 0xdeadbeef, unpackTower 7 0xfeedface] (unpackTower 7 0x80)

meta def settlementTree : HttpsCallTree := .node ⟨.leafHttpsHop, settlement⟩ []

/-- The recorder's response names the root of its children at depth 1. -/
meta def recorderResp : List ByteArray :=
  [js "HTTP/1.1 200 OK\r\n\r\n", js "{\"subtree_root\":\"",
   ⟨(hex64 (mrootC (treeRoots [settlementTree]))).toArray⟩, js "\",\"amount\":\"", js "4200", js "\"}"]

meta def recorder : DecoAttestation :=
  mkAttestation key2 ⟨recorderHost, notary, 101, js "n2", js "pi_2"⟩
    (viewOf [js "GET /settle HTTP/1.1\r\n\r\n"] []) (viewOf recorderResp [])
    [unpackTower 7 0xc0ffee] (unpackTower 7 0x40)

meta def orchestrator : DecoAttestation :=
  mkAttestation key1 ⟨js "local", notary, 0, ByteArray.empty, ByteArray.empty⟩
    (viewOf [js "settle 4200"] []) (viewOf [js "settle 4200"] []) [] (towerZero 7)

meta def tree : HttpsCallTree :=
  .node ⟨.localComputation, orchestrator⟩ [.node ⟨.recursiveHttpsCallee, recorder⟩ [settlementTree]]

meta def decoPolicy : DecoPolicy :=
  ⟨[(js "n1", key1), (js "n2", key2)], [notary], [stripeHost, recorderHost], 0, 1000, []⟩
meta def paymentPolicy : DecoPolicy := { decoPolicy with secretRequestSlots := [4] }
meta def treePolicy : CallTreePolicy := ⟨decoPolicy, ⟨[], []⟩, [recorderHost], .identity⟩

/-- `4200` flows from the recorder's response (hop 1, slot 4) into the settlement request. -/
meta def amountEdge : DataflowEdge := ⟨1, 2, 4, 2, js "4200"⟩
meta def claim : CallTreeClaim := ⟨treePolicy, tree, treeRoot tree, [amountEdge]⟩
meta def witness : CallTreeWitness := [⟨[js "GET /settle HTTP/1.1\r\n\r\n"], recorderResp⟩,
  ⟨settleReq, settleResp⟩]

meta def isOk {α : Type} : Obend.Judge.Verdict α → Bool
  | .ok => true
  | _ => false

-- The session verifies with no plaintext; its openings are the committed transcripts.
#guard checkDecoAttestation paymentPolicy ⟨[], []⟩ settlement
#guard checkOpening settlement.request settleReq && checkOpening settlement.response settleResp
-- The hidden API key must be masked: opening it violates the policy.
#guard !checkDecoAttestation paymentPolicy ⟨[], []⟩
  (mkAttestation key1 settlement.header (viewOf settleReq []) settlement.response
    settlement.ctBlocks settlement.lenBlock)

-- **Forged GHASH**: one tag bit, one ciphertext block, one authenticated header field.
#guard !checkDecoAttestation paymentPolicy ⟨[], []⟩
  { settlement with ghashTag := towerAdd 7 settlement.ghashTag (towerOne 7) }
#guard !checkDecoAttestation paymentPolicy ⟨[], []⟩
  { settlement with ctBlocks := [unpackTower 7 0xdeadbeef, unpackTower 7 0xfeedfacf] }
#guard !checkDecoAttestation paymentPolicy ⟨[], []⟩
  { settlement with header := { settlement.header with time := 102 } }
-- A tag made under another key, and a nonce the verifier holds no key for.
#guard !checkDecoAttestation paymentPolicy ⟨[], []⟩
  (mkAttestation key2 settlement.header settlement.request settlement.response
    settlement.ctBlocks settlement.lenBlock)
#guard !checkDecoAttestation { paymentPolicy with sessionKeys := [] } ⟨[], []⟩ settlement
-- Replay: the same session twice in one trace.
#guard checkDecoTrace paymentPolicy ⟨[], []⟩ [settlement]
#guard !checkDecoTrace paymentPolicy ⟨[], []⟩ [settlement, settlement]

-- A mask over the backslash of an escape: the public view and the opening are both refused.
#guard !checkView (viewOf [js "HTTP/1.1 200 OK\r\n\r\n", js "{\"note\":\"x", js "\\", js "\"y\"}"]
  [(2, js "*")])
#guard !checkOpening (viewOf [js "HTTP/1.1 200 OK\r\n\r\n", js "{\"k\":\"", js "ab\\", js "\"}"]
    [(2, js "*")])
  [js "HTTP/1.1 200 OK\r\n\r\n", js "{\"k\":\"", js "ab\\", js "\"}"]

-- **The call tree**: verified in public, judged with its openings.
#guard callTreeVerify treePolicy tree (treeRoot tree) [amountEdge]
#guard isOk (callTreeJudge.check 0 claim witness)
#guard checkSubtreeRoot recorder.response (mrootC (treeRoots [settlementTree]))
#guard !checkSubtreeRoot recorder.response (treeRoot settlementTree)
-- Refused: another expected root, a flow that is not opened on both sides, an opening that is
-- not the committed transcript.
#guard !callTreeVerify treePolicy tree (treeRoot settlementTree) [amountEdge]
#guard !callTreeVerify treePolicy tree (treeRoot tree) [{ amountEdge with dstSlot := 4 }]
#guard (callTreeCheck claim
  [⟨[js "GET /settle HTTP/1.1\r\n\r\n"], recorderResp⟩,
   ⟨[js "POST /v1/pay HTTP/1.1\r\nHost: api.stripe.com\r\n\r\n", js "{\"amount\":\"", js "4200",
     js "\",\"key\":\"", js "sk_live_98", js "\"}"], settleResp⟩]) == .refused .unfaithfulOpening []

/-! ## 4. Lsafe: one edge about the tree opens by its own path -/

/-- "This host attested this subtree root": one edge per attested hop. -/
meta def edges : Array Obend.Vault.Lsafe.KgEdge :=
  #[⟨1, recorderHost, (treeRoot (.node ⟨.recursiveHttpsCallee, recorder⟩ [settlementTree])).val⟩,
    ⟨1, stripeHost, (treeRoot settlementTree).val⟩]
meta def graphDigest : ByteArray := Obend.Vault.Lsafe.edgesDigest cshakeHasher edges

#guard graphDigest.size == 32
#guard Obend.Vault.Lsafe.evalOpenedKgQuery cshakeHasher graphDigest 1 stripeHost
  (treeRoot settlementTree).val (some (Obend.Vault.Lsafe.openKgEdge cshakeHasher edges 1)) == .entailed
-- Another root for that host, the other edge's path, a claimed count of three: undetermined.
#guard Obend.Vault.Lsafe.evalOpenedKgQuery cshakeHasher graphDigest 1 stripeHost
  (treeRoot tree).val (some (Obend.Vault.Lsafe.openKgEdge cshakeHasher edges 1)) == .undetermined
#guard Obend.Vault.Lsafe.evalOpenedKgQuery cshakeHasher graphDigest 1 stripeHost
  (treeRoot settlementTree).val (some (Obend.Vault.Lsafe.openKgEdge cshakeHasher edges 0)) ==
    .undetermined
#guard Obend.Vault.Lsafe.evalOpenedKgQuery cshakeHasher graphDigest 1 stripeHost
  (treeRoot settlementTree).val
  (some ⟨3, (Obend.Vault.Lsafe.openKgEdge cshakeHasher edges 1).proof⟩) == .undetermined
-- The whole-witness query agrees.
#guard Obend.Vault.Lsafe.evalOpenWorldKgQuery cshakeHasher graphDigest ByteArray.empty 1 stripeHost
  (treeRoot settlementTree).val
  #[⟨1, recorderHost, (treeRoot (.node ⟨.recursiveHttpsCallee, recorder⟩ [settlementTree])).val⟩,
    ⟨1, stripeHost, (treeRoot settlementTree).val⟩] none != .refuted

/-! ## 5. ZkStripe: the organ audits the tree's carrier under a 256-bit digest -/

open Obend.Trailblaze.ZkStripe in
meta def zkPolicy : ZkStripePolicy where
  trustedNotaryKeys := [notaryKeyOf notary]
  allowedRequestRe := forbidSubseq stripeLiveKeyPrefix
  allowedResponseRe := forbidSubseq stripeLiveKeyPrefix
  policyRules := [
    { name := "admit_three_hop_calltree"
      concl := "calltree_admitted"
      pos := ["hop_verified:local", "hop_verified:recorder.obend.org", "hop_verified:api.stripe.com"]
      neg := ["emergency_freeze"] }]
  targetConclusion := "calltree_admitted"

open Obend.Trailblaze.ZkStripe in
#guard verifyZkStripeCallTree zkPolicy (sessionOfCallTree tree)
open Obend.Trailblaze.ZkStripe in
#guard checkCanonicalSessionTree fastMerkleHash (sessionOfCallTree tree) &&
  (callTreeDigest fastMerkleHash (sessionOfCallTree tree)).bytes.size == 32
-- With the API key opened instead of masked, the request expression refuses the settlement hop.
open Obend.Trailblaze.ZkStripe in
#guard (match auditZkStripeCallTree zkPolicy
    (sessionOfCallTree (.node ⟨.leafHttpsHop,
      mkAttestation key1 settlement.header (viewOf settleReq []) settlement.response
        settlement.ctBlocks settlement.lenBlock⟩ [])) with
  | .error e => e == .requestRegexViolation "api.stripe.com"
  | .ok () => false)
-- The digest reads the masks: another mask, another digest.
open Obend.Trailblaze.ZkStripe in
#guard callTreeDigest fastMerkleHash (sessionOfCallTree settlementTree) !=
  callTreeDigest fastMerkleHash (sessionOfCallTree (.node ⟨.leafHttpsHop,
    mkAttestation key1 settlement.header (viewOf settleReq [(4, js "XXXX")]) settlement.response
      settlement.ctBlocks settlement.lenBlock⟩ []))

/-- **The seam as one statement.** An accepted call-tree claim whose carrier the organ admits:
its root binds the tree, every real transcript parses as its view, and every hop's redacted
request matches the request expression. -/
example (q : CallTreeClaim) (w : CallTreeWitness) (pol : Obend.Trailblaze.ZkStripe.ZkStripePolicy)
    (hj : callTreeJudge.check 0 q w = .ok)
    (ha : Obend.Trailblaze.ZkStripe.auditZkStripeCallTree pol
      (Obend.Trailblaze.ZkStripe.sessionOfCallTree q.tree) = .ok ()) :
    (∀ t', treeRoot t' = q.expectedRoot → t' = q.tree ∨ CallTreeCollision) ∧
      OpeningsParse (treeAttestations q.tree) w ∧
      ∀ h ∈ treeHops q.tree, Obend.Trailblaze.ZkStripe.matchesBytes pol.allowedRequestRe
        (viewBytes h.attestation.request.slots) = true :=
  have m : CallTreeSpec q w := callTreeJudge.sound hj
  ⟨m.bound, m.faithful,
    fun h hh => (Obend.Trailblaze.ZkStripe.audit_covers_callTree_hops ha h hh).1⟩

/-! ## 6. The three byte formats round-trip -/

-- `deco-calltree@1`: the decoded claim re-encodes to the same bytes and is judged alike.
#guard (match decodeCallTreeClaim (encodeCallTreeClaim claim),
    decodeCallTreeWitness (encodeCallTreeWitness witness) with
  | .ok c, .ok w => encodeCallTreeClaim c == encodeCallTreeClaim claim &&
      encodeCallTreeWitness w == encodeCallTreeWitness witness && isOk (callTreeJudge.check 0 c w)
  | _, _ => false)
#guard isOk (decoCallTreeFormat.checkBytes 0 (encodeCallTreeClaim claim) (encodeCallTreeWitness witness))
#guard !isOk (decoCallTreeFormat.checkBytes 0 (encodeCallTreeClaim claim) (encodeCallTreeWitness []))
#guard !isOk (decoCallTreeFormat.checkBytes 0 "zz" "")

-- `vpa-json-span@1`: the disclosure of `x` in `{"note":"x\"y"}`, and of the backslash (refused).
open Obend.Judge.VpaJson in
#guard isOk (jsonSpanFormat.checkBytes 0
  (encodeJsonSpanClaim ⟨js "{\"note\":\"x\\\"y\"}", 9, 10, js "*", js "{\"note\":\"*\\\"y\"}"⟩)
  (encodeJsonSpanCert (jsonSpanCertOf ⟨js "{\"note\":\"x\\\"y\"}", 9, 10, js "*",
    js "{\"note\":\"*\\\"y\"}"⟩)))
open Obend.Judge.VpaJson in
#guard !isOk (jsonSpanFormat.checkBytes 0
  (encodeJsonSpanClaim ⟨js "{\"note\":\"x\\\"y\"}", 10, 11, js "*", js "{\"note\":\"x*\"y\"}"⟩)
  (encodeJsonSpanCert (jsonSpanCertOf ⟨js "{\"note\":\"x\\\"y\"}", 10, 11, js "*",
    js "{\"note\":\"x*\"y\"}"⟩)))
open Obend.Judge.VpaJson in
#guard (match decodeJsonSpanClaim (encodeJsonSpanClaim ⟨js "ab", 0, 1, js "*", js "*b"⟩) with
  | .ok c => c.doc == js "ab" && c.l == 0 && c.r == 1 && c.mask == js "*" && c.redacted == js "*b"
  | .error _ => false)

-- `sym-regex-bisim@1`: `a ⊆ any byte` with the emitted certificate; the converse is refused.
open Obend.Judge.SymbolicRegex in
#guard isOk (symRegexBisimFormat.checkBytes 4 (encodeInclusionQuery ⟨byte 97, anyByte⟩)
  (encodePairs (emitBisimPairs 8 (byte 97) anyByte)))
open Obend.Judge.SymbolicRegex in
#guard !isOk (symRegexBisimFormat.checkBytes 4 (encodeInclusionQuery ⟨anyByte, byte 97⟩)
  (encodePairs (emitBisimPairs 8 anyByte (byte 97))))
open Obend.Judge.SymbolicRegex in
#guard (match decodeInclusionQuery (encodeInclusionQuery ⟨absenceOf (lit [115, 107, 95]), anyByte⟩),
    decodePairs (encodePairs [(byte 97, anyByte), (.eps, .ff)]) with
  | .ok q, .ok ps => q.lhs == absenceOf (lit [115, 107, 95]) && q.rhs == anyByte &&
      ps == [(byte 97, anyByte), (.eps, .ff)]
  | _, _ => false)

/-! ## 7. Teeth -/

-- A vault redaction check that accepts every span: the escape cut goes through.
#tooth Obend.Vault.Lsafe.lsafe_redaction_confinement by
  mutation Obend.Vault.Lsafe.checkLsafeRedaction := fun _ _ _ _ => true

-- A mask check that does not ask the hidden span to return to the machine state.
#tooth checkMask_run by mutation Obend.Judge.spanConfined := fun _ _ _ => true

-- A redaction check that accepts every span.
#tooth Obend.Judge.VpaJson.jsonRedaction_confinement by
  mutation Obend.Judge.VpaJson.checkJsonRedaction := fun _ _ _ _ => true

-- A callee link that does not read the body.
#tooth checkSubtreeRoot_iff by mutation checkSubtreeRoot := fun _ _ => true

-- A tag check that accepts every tag.
#tooth deco_ghash_forgery_keys_bound by mutation tagVerifies := fun _ _ => true

-- A policy check that skips the tag and the notary.
#tooth checkPolicy_iff by mutation checkPolicy := fun _ _ => true

-- A children root that does not read the children.
#tooth treeRoot_binds by mutation mrootC := fun _ => hash256 "none" []

-- An edge opening that does not compare the climbed digest with the graph digest.
#tooth Obend.Vault.Lsafe.verifyKgEdgeOpening_binding by
  mutation Obend.Judge.VpaJson.topMatches := fun _ _ _ _ => true

-- A call-tree digest that does not read the tree.
#tooth Obend.Trailblaze.ZkStripe.callTreeDigest_binding by
  mutation Obend.Trailblaze.ZkStripe.callTreeDigest := fun _ _ => ⟨ByteArray.empty⟩

-- An organ audit that admits every hop.
#tooth Obend.Trailblaze.ZkStripe.apex_zkstripe_calltree_audit by
  mutation Obend.Trailblaze.ZkStripe.auditNodes := fun _ _ => .ok ()

#print axioms treeRoot_binds
#print axioms checkOpening_parses
#print axioms Obend.Vault.Lsafe.verifyKgEdgeOpening_binding
#print axioms Obend.Trailblaze.ZkStripe.audit_covers_callTree_hops

end Obend.Tests.Metasystem.ZkTlsLsafeSeamUnificationTest

end
