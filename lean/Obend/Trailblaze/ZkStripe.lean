module
/-
# Obend.Trailblaze.ZkStripe — Organ O5: the regex and grammar audit of a notarized HTTPS call tree

The organ owns no regular-expression engine, no pushdown machine, no lexer and no integer digest.
It is a policy layer over three judges:

1. **Request and response confinement** is `Obend.Judge.SymbolicRegex.PredRE` (Boolean-closed, with
   complement and intersection) matched by `matchB`; `matchesBytes` is that matcher with the
   expression first, and `matchesBytes_compl` / `matchesBytes_inter` are read off its denotational
   semantics `Matches`.
2. **Response framing** is not re-checked here. The two-bit string/escape lexer and the bracket
   automaton that stood here are gone; the transcript layer checks framing once, with the RFC 8259
   machine `Obend.Judge.VpaJson.runFullJsonGrammar` (`DecoAndCallTree.checkView`;
   `checkView_body_framed`).
3. **Sessions** are the hops of an `Obend.Judge.DecoAndCallTree.HttpsCallTree`: `sessionOfCallTree`
   projects each hop to its notary key, host and redacted views, and
   `allSessionNodes_sessionOfCallTree` says the audit ranges over exactly those hops
   (`audit_covers_callTree_hops`).

`callTreeDigest` is a 256-bit digest (`CallTreeDigest`, the 32 bytes of the hash output; a
canonical tree has every node digest exactly 32 bytes wide), and the notary key is a `BitVec 256`.
`callTreeDigestBytes_binding` and `callTreeDigest_binding`: one digest, one tree (every hop's
notary key, domain, request, response and children), or a collision of the hash.
`auditNodes_all_hops_sound` and `apex_zkstripe_calltree_audit`: an admitted tree satisfies the
policy at every hop, matches no forbidden pattern in any request, supports the target conclusion
in the well-founded model, and is bound by its digest.

`CallTreeDigest` coerces to its big-endian reading only to meet `ClusterGov`'s lineage field.
-/
public import Obend.Reasons
public import Obend.Digest.HashBytes
public import Obend.Judge.Class
public import Obend.Judge.SymbolicRegexBisim
public import Obend.Judge.VpaComplementAndJson
public import Obend.Judge.DecoAndCallTree
import all Obend.Codec.DetCbor
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Judge.VpaComplementAndJson
import all Obend.Judge.DecoAndCallTree

public section
namespace Obend.Trailblaze.ZkStripe

open Obend.Digest.HashBytes (Hash ofBE be length_be be_injective Collision)
open Obend.Judge.SymbolicRegex (Matches matchB matchB_iff lit anyByte absenceOf)
open Obend.Judge.VpaJson (runFullJsonGrammar)

export Obend.Judge.SymbolicRegex (PredRE)

set_option autoImplicit false

/-! ## §1. Policies are `SymbolicRegex.PredRE` -/

/-- **The policy matcher**: `SymbolicRegex.matchB`, expression first. -/
def matchesBytes (r : PredRE) (bs : List UInt8) : Bool := matchB bs r

/-- The matcher decides the denotational semantics. -/
theorem matchesBytes_iff (r : PredRE) (bs : List UInt8) :
    matchesBytes r bs = true ↔ Matches bs r := matchB_iff bs r

/-- **Complement is exact**, on every byte string. -/
theorem matchesBytes_compl (r : PredRE) (bs : List UInt8) :
    matchesBytes (.compl r) bs = !matchesBytes r bs := by
  rw [Bool.eq_iff_iff, matchesBytes_iff, Bool.not_eq_true', ← Bool.not_eq_true, matchesBytes_iff]
  show Matches bs (.neg r) ↔ ¬ Matches bs r
  simp only [Matches]

/-- **Intersection is conjunction**, on every byte string. -/
theorem matchesBytes_inter (r₁ r₂ : PredRE) (bs : List UInt8) :
    matchesBytes (.inter r₁ r₂) bs = (matchesBytes r₁ bs && matchesBytes r₂ bs) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, matchesBytes_iff, matchesBytes_iff, matchesBytes_iff]
  simp only [Matches]

/-- **Union is disjunction**, on every byte string. -/
theorem matchesBytes_alt (r₁ r₂ : PredRE) (bs : List UInt8) :
    matchesBytes (.alt r₁ r₂) bs = (matchesBytes r₁ bs || matchesBytes r₂ bs) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, matchesBytes_iff, matchesBytes_iff, matchesBytes_iff]
  simp only [Matches]

/-- The bytes begin with `pre`. -/
def startsWith (pre : List UInt8) : PredRE := .cat (lit pre) (.star anyByte)

/-- No factor of the bytes is `pat`. -/
def forbidSubseq (pat : List UInt8) : PredRE := absenceOf (lit pat)

/-! ## §2. Session nodes, 256-bit digests, binding -/

/-- Kernel-reducible, `0`-axiom UTF-8 byte projection of `s : String` (`s.toByteArray.data.toList`). -/
def utf8Bytes (s : String) : List UInt8 :=
  s.toByteArray.data.toList

/-- `utf8Bytes` is unconditionally injective (`0` axioms: pure `String.ofByteArray` structure
    eta + proof irrelevance on `ByteArray.IsValidUTF8`). -/
theorem utf8Bytes_injective {s₁ s₂ : String} (h : utf8Bytes s₁ = utf8Bytes s₂) : s₁ = s₂ := by
  cases s₁ with
  | ofByteArray b₁ v₁ =>
    cases s₂ with
    | ofByteArray b₂ v₂ =>
      cases b₁ with
      | mk a₁ =>
        cases b₂ with
        | mk a₂ =>
          cases a₁ with
          | mk l₁ =>
            cases a₂ with
            | mk l₂ =>
              change l₁ = l₂ at h
              subst h
              rfl

/-- A hop of a notarized HTTPS call tree as the audit sees it: the notary's 32-byte key, the
server domain, the redacted request and response bytes, and the downstream sessions. -/
inductive HttpsSessionNode where
  | mk
    (notaryKey        : BitVec 256)
    (serverDomain     : String)
    (redactedRequest  : List UInt8)
    (redactedResponse : List UInt8)
    (children         : List HttpsSessionNode)

mutual
def decEqHttpsSessionNode (a b : HttpsSessionNode) : Decidable (a = b) :=
  match a, b with
  | .mk h₁ d₁ req₁ resp₁ cs₁, .mk h₂ d₂ req₂ resp₂ cs₂ =>
    if hh : h₁ = h₂ then
      if hd : d₁ = d₂ then
        if hreq : req₁ = req₂ then
          if hresp : resp₁ = resp₂ then
            match decEqHttpsSessionChildren cs₁ cs₂ with
            | isTrue hcs => isTrue (by subst hh hd hreq hresp hcs; rfl)
            | isFalse hncs => isFalse (by intro hEq; cases hEq; exact hncs rfl)
          else isFalse (by intro hEq; cases hEq; exact hresp rfl)
        else isFalse (by intro hEq; cases hEq; exact hreq rfl)
      else isFalse (by intro hEq; cases hEq; exact hd rfl)
    else isFalse (by intro hEq; cases hEq; exact hh rfl)
termination_by structural a

def decEqHttpsSessionChildren (xs ys : List HttpsSessionNode) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | x :: xs', y :: ys' =>
    match decEqHttpsSessionNode x y with
    | isTrue hx =>
      match decEqHttpsSessionChildren xs' ys' with
      | isTrue hxs => isTrue (by subst hx hxs; rfl)
      | isFalse hnxs => isFalse (by intro h; cases h; exact hnxs rfl)
    | isFalse hnx => isFalse (by intro h; cases h; exact hnx rfl)
termination_by structural xs
end

instance : DecidableEq HttpsSessionNode := decEqHttpsSessionNode

namespace HttpsSessionNode

@[expose] def notaryKey : HttpsSessionNode → BitVec 256
  | .mk k _ _ _ _ => k

@[expose] def serverDomain : HttpsSessionNode → String
  | .mk _ d _ _ _ => d

@[expose] def redactedRequest : HttpsSessionNode → List UInt8
  | .mk _ _ req _ _ => req

@[expose] def redactedResponse : HttpsSessionNode → List UInt8
  | .mk _ _ _ resp _ => resp

def children : HttpsSessionNode → List HttpsSessionNode
  | .mk _ _ _ _ cs => cs

end HttpsSessionNode

/-- Length-prefixed canonical framing (`len:4 ‖ payload`) for byte slices inside Merkle nodes. -/
def frameBytes (xs : List UInt8) : List UInt8 :=
  be 4 xs.length ++ xs

/-- **Prefix-Free Framing Injectivity**: Two 32-bit length-prefixed slices (`len < 2^32 = 256^4`)
    followed by arbitrary suffixes are equal iff both the slices and suffixes match identically. -/
theorem frameBytes_append_inj {xs ys rest₁ rest₂ : List UInt8}
    (hxs : xs.length < 2 ^ 32) (hys : ys.length < 2 ^ 32)
    (hEq : frameBytes xs ++ rest₁ = frameBytes ys ++ rest₂) :
    xs = ys ∧ rest₁ = rest₂ := by
  have hPow : (2 : Nat) ^ 32 = 256 ^ 4 := by decide
  unfold frameBytes at hEq
  rw [List.append_assoc, List.append_assoc] at hEq
  have hLenBe : (be 4 xs.length).length = (be 4 ys.length).length := by
    rw [length_be, length_be]
  obtain ⟨hBeEq, hTailEq⟩ := List.append_inj hEq hLenBe
  have hLenEq : xs.length = ys.length :=
    be_injective (hPow ▸ hxs) (hPow ▸ hys) hBeEq
  exact List.append_inj hTailEq hLenEq

/-- The preimage of one hop: a domain byte, then the notary key's 32 bytes, then the domain's
UTF-8 bytes, the request and the response (each length-framed), then the children's framed
digests. -/
def sessionNodePreimage (notaryKey : BitVec 256) (domain : String)
    (req resp childrenBytes : List UInt8) : List UInt8 :=
  (0x01 : UInt8) ::
  (be 32 notaryKey.toNat ++
   (frameBytes (utf8Bytes domain) ++
    (frameBytes req ++
     (frameBytes resp ++
      childrenBytes))))

/-- **The preimage determines every field.** -/
theorem sessionNodePreimage_inj
    {k₁ k₂ : BitVec 256} {d₁ d₂ : String}
    {req₁ req₂ resp₁ resp₂ kidsBytes₁ kidsBytes₂ : List UInt8}
    (hd₁ : (utf8Bytes d₁).length < 2 ^ 32) (hd₂ : (utf8Bytes d₂).length < 2 ^ 32)
    (hreq₁ : req₁.length < 2 ^ 32) (hreq₂ : req₂.length < 2 ^ 32)
    (hresp₁ : resp₁.length < 2 ^ 32) (hresp₂ : resp₂.length < 2 ^ 32)
    (hPre : sessionNodePreimage k₁ d₁ req₁ resp₁ kidsBytes₁ =
            sessionNodePreimage k₂ d₂ req₂ resp₂ kidsBytes₂) :
    k₁ = k₂ ∧ d₁ = d₂ ∧ req₁ = req₂ ∧ resp₁ = resp₂ ∧ kidsBytes₁ = kidsBytes₂ := by
  unfold sessionNodePreimage at hPre
  have hBody := (List.cons.inj hPre).2
  have hPow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have hBeLen : (be 32 k₁.toNat).length = (be 32 k₂.toNat).length := by rw [length_be, length_be]
  obtain ⟨hBeK, hRest1⟩ := List.append_inj hBody hBeLen
  have hKey : k₁ = k₂ :=
    BitVec.eq_of_toNat_eq (be_injective (hPow ▸ k₁.isLt) (hPow ▸ k₂.isLt) hBeK)
  obtain ⟨hDomBytes, hRest2⟩ := frameBytes_append_inj hd₁ hd₂ hRest1
  obtain ⟨hReqEq, hRest3⟩ := frameBytes_append_inj hreq₁ hreq₂ hRest2
  obtain ⟨hRespEq, hKidsBytes⟩ := frameBytes_append_inj hresp₁ hresp₂ hRest3
  exact ⟨hKey, utf8Bytes_injective hDomBytes, hReqEq, hRespEq, hKidsBytes⟩

mutual
/-- Domain-bound recursive Merkle commitment bytes of an `HttpsSessionNode` over byte hash `H`:
    commits the notary key, `serverDomain` UTF-8 bytes, `redactedRequest` bytes,
    `redactedResponse` bytes, and framed child session subtree digests. -/
def callTreeDigestBytes (H : Hash) (n : HttpsSessionNode) : List UInt8 :=
  match n with
  | .mk key domain req resp kids =>
    H (sessionNodePreimage key domain req resp (callTreeChildrenDigestBytes H kids))
termination_by structural n

def callTreeChildrenDigestBytes (H : Hash) (ns : List HttpsSessionNode) : List UInt8 :=
  match ns with
  | [] => [(0x00 : UInt8)]
  | c :: cs =>
    (0x02 : UInt8) :: (frameBytes (callTreeDigestBytes H c) ++ callTreeChildrenDigestBytes H cs)
termination_by structural ns
end

/-- **A 256-bit call-tree digest**: the bytes of the hash output (32 of them on a canonical tree). -/
structure CallTreeDigest where
  bytes : ByteArray
  deriving DecidableEq

/-- The big-endian reading of `2^k` bytes, by halves: five levels for a digest, so it stays
shallow under reduction. -/
def readHalves : Nat → List UInt8 → Nat
  | 0, l => (l.headD 0).toNat
  | k + 1, l => readHalves k (l.take (2 ^ k)) * 256 ^ (2 ^ k) + readHalves k (l.drop (2 ^ k))

/-- The big-endian reading of the 32 bytes, for welding to a lineage field that is a natural. -/
def CallTreeDigest.toNat (d : CallTreeDigest) : Nat := readHalves 5 d.bytes.data.toList

instance : Coe CallTreeDigest Nat := ⟨CallTreeDigest.toNat⟩

/-- **The digest of a call tree.** -/
def callTreeDigest (H : Hash) (node : HttpsSessionNode) : CallTreeDigest :=
  ⟨⟨(callTreeDigestBytes H node).toArray⟩⟩

mutual
/-- **Canonical**: at every hop slice lengths below `2^32` and a node digest exactly 32 bytes
wide. -/
def checkCanonicalSessionTree (H : Hash) (n : HttpsSessionNode) : Bool :=
  match n with
  | .mk key domain req resp kids =>
    decide ((utf8Bytes domain).length < 2 ^ 32) &&
    decide (req.length < 2 ^ 32) &&
    decide (resp.length < 2 ^ 32) &&
    decide ((H (sessionNodePreimage key domain req resp
      (callTreeChildrenDigestBytes H kids))).length = 32) &&
    checkCanonicalSessionChildren H kids
termination_by structural n

def checkCanonicalSessionChildren (H : Hash) (ns : List HttpsSessionNode) : Bool :=
  match ns with
  | [] => true
  | c :: cs => checkCanonicalSessionTree H c && checkCanonicalSessionChildren H cs
termination_by structural ns
end

def CanonicalSessionTree (H : Hash) (t : HttpsSessionNode) : Prop :=
  checkCanonicalSessionTree H t = true

/-- **A canonical tree's digest is 256 bits.** -/
theorem canonical_digest_width {H : Hash} {t : HttpsSessionNode}
    (h : checkCanonicalSessionTree H t = true) : (callTreeDigestBytes H t).length = 32 := by
  cases t with
  | mk k d req resp kids =>
    simp only [checkCanonicalSessionTree, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa only [callTreeDigestBytes] using h.1.2

theorem callTreeDigest_size {H : Hash} {t : HttpsSessionNode}
    (h : checkCanonicalSessionTree H t = true) : (callTreeDigest H t).bytes.size = 32 := by
  have hw := canonical_digest_width h
  simpa [callTreeDigest, ByteArray.size] using hw

mutual
theorem callTreeDigest_binding_aux (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionTree H t₁ = true)
    (hCan₂ : checkCanonicalSessionTree H t₂ = true)
    (hEq : ofBE (callTreeDigestBytes H t₁) = ofBE (callTreeDigestBytes H t₂)) :
    t₁ = t₂ ∨ Collision H := by
  cases t₁ with
  | mk h₁ d₁ req₁ resp₁ kids₁ =>
    cases t₂ with
    | mk h₂ d₂ req₂ resp₂ kids₂ =>
      simp only [checkCanonicalSessionTree, Bool.and_eq_true, decide_eq_true_eq] at hCan₁ hCan₂
      rcases hCan₁ with ⟨⟨⟨⟨hd₁, hreq₁⟩, hresp₁⟩, _⟩, hkids₁⟩
      rcases hCan₂ with ⟨⟨⟨⟨hd₂, hreq₂⟩, hresp₂⟩, _⟩, hkids₂⟩
      let pre₁ : List UInt8 :=
        sessionNodePreimage h₁ d₁ req₁ resp₁ (callTreeChildrenDigestBytes H kids₁)
      let pre₂ : List UInt8 :=
        sessionNodePreimage h₂ d₂ req₂ resp₂ (callTreeChildrenDigestBytes H kids₂)
      change ofBE (H pre₁) = ofBE (H pre₂) at hEq
      if hPre : pre₁ = pre₂ then
        obtain ⟨hNotaryEq, hDomEq, hReqEq, hRespEq, hKidsBytes⟩ :=
          sessionNodePreimage_inj hd₁ hd₂ hreq₁ hreq₂ hresp₁ hresp₂ hPre
        rcases callTreeChildrenDigestBytes_binding_aux H kids₁ kids₂ hkids₁ hkids₂ hKidsBytes with
          hKidsEq | hCol
        · subst hNotaryEq hDomEq hReqEq hRespEq hKidsEq
          exact Or.inl rfl
        · exact Or.inr hCol
      else
        exact Or.inr ⟨pre₁, pre₂, hPre, hEq⟩
termination_by structural t₁

theorem callTreeChildrenDigestBytes_binding_aux (H : Hash)
    (ns₁ ns₂ : List HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionChildren H ns₁ = true)
    (hCan₂ : checkCanonicalSessionChildren H ns₂ = true)
    (hEq : callTreeChildrenDigestBytes H ns₁ = callTreeChildrenDigestBytes H ns₂) :
    ns₁ = ns₂ ∨ Collision H := by
  cases ns₁ with
  | nil =>
    cases ns₂ with
    | nil => exact Or.inl rfl
    | cons c₂ cs₂ =>
      simp only [callTreeChildrenDigestBytes, List.cons.injEq] at hEq
      exact absurd hEq.1 (by decide)
  | cons c₁ cs₁ =>
    cases ns₂ with
    | nil =>
      simp only [callTreeChildrenDigestBytes, List.cons.injEq] at hEq
      exact absurd hEq.1 (by decide)
    | cons c₂ cs₂ =>
      simp only [checkCanonicalSessionChildren, Bool.and_eq_true] at hCan₁ hCan₂
      rcases hCan₁ with ⟨hc₁, hcs₁⟩
      rcases hCan₂ with ⟨hc₂, hcs₂⟩
      have hcd₁ : (callTreeDigestBytes H c₁).length < 2 ^ 32 := by
        rw [canonical_digest_width hc₁]; decide
      have hcd₂ : (callTreeDigestBytes H c₂).length < 2 ^ 32 := by
        rw [canonical_digest_width hc₂]; decide
      simp only [callTreeChildrenDigestBytes, List.cons.injEq] at hEq
      obtain ⟨hChildDigestEq, hRestEq⟩ := frameBytes_append_inj hcd₁ hcd₂ hEq.2
      rcases callTreeDigest_binding_aux H c₁ c₂ hc₁ hc₂ (congrArg ofBE hChildDigestEq) with
        hCEq | hCol
      · rcases callTreeChildrenDigestBytes_binding_aux H cs₁ cs₂ hcs₁ hcs₂ hRestEq with
          hCsEq | hCol
        · subst hCEq hCsEq
          exact Or.inl rfl
        · exact Or.inr hCol
      · exact Or.inr hCol
termination_by structural ns₁
end

/-- **Digest bytes bind.** Two canonical trees with one digest are one tree (every hop's notary
key, domain, request, response and children), or the hash collides. -/
theorem callTreeDigestBytes_binding (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionTree H t₁ = true)
    (hCan₂ : checkCanonicalSessionTree H t₂ = true)
    (hEq : callTreeDigestBytes H t₁ = callTreeDigestBytes H t₂) :
    t₁ = t₂ ∨ Collision H :=
  callTreeDigest_binding_aux H t₁ t₂ hCan₁ hCan₂ (congrArg ofBE hEq)

/-- **The 256-bit digest binds.** -/
theorem callTreeDigest_binding (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionTree H t₁ = true)
    (hCan₂ : checkCanonicalSessionTree H t₂ = true)
    (hEq : callTreeDigest H t₁ = callTreeDigest H t₂) :
    t₁ = t₂ ∨ Collision H := by
  have hb : callTreeDigestBytes H t₁ = callTreeDigestBytes H t₂ := by
    have hl := congrArg (fun d : CallTreeDigest => d.bytes.data.toList) hEq
    simpa [callTreeDigest] using hl
  exact callTreeDigestBytes_binding H t₁ t₂ hCan₁ hCan₂ hb

mutual
/-- Pre-order traversal collecting every `HttpsSessionNode` hop in a `CallTree`. -/
def allSessionNodes (n : HttpsSessionNode) : List HttpsSessionNode :=
  match n with
  | .mk h d req resp kids => .mk h d req resp kids :: allChildrenSessionNodes kids
termination_by structural n

def allChildrenSessionNodes (ns : List HttpsSessionNode) : List HttpsSessionNode :=
  match ns with
  | [] => []
  | c :: cs => allSessionNodes c ++ allChildrenSessionNodes cs
termination_by structural ns
end

theorem root_mem_allSessionNodes (tree : HttpsSessionNode) :
    tree ∈ allSessionNodes tree := by
  cases tree
  simp [allSessionNodes]

mutual
/-- Count total notarized HTTPS hops in a `CallTree`. -/
def callTreeHopCount : HttpsSessionNode → Nat
  | .mk _ _ _ _ kids => 1 + callTreeChildrenHopCount kids

def callTreeChildrenHopCount : List HttpsSessionNode → Nat
  | [] => 0
  | c :: cs => callTreeHopCount c + callTreeChildrenHopCount cs
end

/-! ## §3. The audit -/

/-- The audit policy: the notary keys trusted, the request and response expressions, and the
rules and target of the `Obend.Reasons` program over the verified hops. -/
structure ZkStripePolicy where
  trustedNotaryKeys   : List (BitVec 256)
  allowedRequestRe    : PredRE
  allowedResponseRe   : PredRE
  policyRules         : List Obend.Reasons.Rule
  targetConclusion    : String

inductive ZkStripeRefusal where
  | untrustedNotary (domain : String)
  | nonCanonicalBounds (domain : String)
  | requestRegexViolation (domain : String)
  | responseRegexViolation (domain : String)
  | policyUnsupported (conclusion : String) (status : Obend.Reasons.Status)
  deriving DecidableEq, Repr

def checkHopCanonicalBounds (domain : String) (req resp : List UInt8) : Bool :=
  decide ((utf8Bytes domain).length < 2 ^ 32) &&
  decide (req.length < 2 ^ 32) &&
  decide (resp.length < 2 ^ 32)

/-- A hop passes: trusted notary, canonical widths, both expressions. -/
def hopPasses (pol : ZkStripePolicy) (key : BitVec 256) (domain : String) (req resp : List UInt8) :
    Bool :=
  decide (key ∈ pol.trustedNotaryKeys) && checkHopCanonicalBounds domain req resp &&
    matchesBytes pol.allowedRequestRe req && matchesBytes pol.allowedResponseRe resp

mutual
/-- One fact `"hop_verified:<domain>"` per hop that passes. -/
def extractCallTreeFacts (pol : ZkStripePolicy) : HttpsSessionNode → List String
  | .mk key domain req resp kids =>
    (if hopPasses pol key domain req resp then ["hop_verified:" ++ domain] else []) ++
      extractChildrenFacts pol kids

def extractChildrenFacts (pol : ZkStripePolicy) : List HttpsSessionNode → List String
  | [] => []
  | c :: cs => extractCallTreeFacts pol c ++ extractChildrenFacts pol cs
end

def buildCallTreeProgram (pol : ZkStripePolicy) (root : HttpsSessionNode) :
    Obend.Reasons.Program where
  facts := extractCallTreeFacts pol root
  rules := pol.policyRules

mutual
/-- Check every hop, naming the first clause that fails. -/
def auditNodes (pol : ZkStripePolicy) : HttpsSessionNode → Except ZkStripeRefusal Unit
  | .mk key domain req resp kids =>
    if !decide (key ∈ pol.trustedNotaryKeys) then
      .error (.untrustedNotary domain)
    else if !checkHopCanonicalBounds domain req resp then
      .error (.nonCanonicalBounds domain)
    else if !matchesBytes pol.allowedRequestRe req then
      .error (.requestRegexViolation domain)
    else if !matchesBytes pol.allowedResponseRe resp then
      .error (.responseRegexViolation domain)
    else
      auditChildren pol kids

def auditChildren (pol : ZkStripePolicy) :
    List HttpsSessionNode → Except ZkStripeRefusal Unit
  | [] => .ok ()
  | c :: cs =>
    match auditNodes pol c with
    | .error e => .error e
    | .ok () => auditChildren pol cs
end

/-- **The audit**: every hop, then the policy program's support for the target conclusion. -/
def auditZkStripeCallTree (pol : ZkStripePolicy) (root : HttpsSessionNode) :
    Except ZkStripeRefusal Unit :=
  match auditNodes pol root with
  | .error e => .error e
  | .ok () =>
    let prog := buildCallTreeProgram pol root
    let st := Obend.Reasons.statusIn (Obend.Reasons.wf prog) pol.targetConclusion
    if st == .supported then
      .ok ()
    else
      .error (.policyUnsupported pol.targetConclusion st)

def verifyZkStripeCallTree (pol : ZkStripePolicy) (root : HttpsSessionNode) : Bool :=
  (auditZkStripeCallTree pol root).isOk

theorem auditZkStripeCallTree_ok_imp_verify {pol : ZkStripePolicy} {root : HttpsSessionNode}
    (h : auditZkStripeCallTree pol root = .ok ()) :
    verifyZkStripeCallTree pol root = true := by
  simp [verifyZkStripeCallTree, h, Except.isOk, Except.toBool]

/-- What the audit certifies of one hop. -/
structure HopAudited (pol : ZkStripePolicy) (node : HttpsSessionNode) : Prop where
  trustedNotary    : node.notaryKey ∈ pol.trustedNotaryKeys
  canonicalDomain  : (utf8Bytes node.serverDomain).length < 2 ^ 32
  canonicalReqLen  : node.redactedRequest.length < 2 ^ 32
  canonicalRespLen : node.redactedResponse.length < 2 ^ 32
  requestMatches   : matchesBytes pol.allowedRequestRe node.redactedRequest = true
  responseMatches  : matchesBytes pol.allowedResponseRe node.redactedResponse = true

mutual
/-- **Every hop is audited**, not only the root. -/
theorem auditNodes_all_hops_sound {pol : ZkStripePolicy} {tree : HttpsSessionNode}
    (hOk : auditNodes pol tree = .ok ()) :
    ∀ node ∈ allSessionNodes tree, HopAudited pol node := by
  cases tree with
  | mk key domain req resp kids =>
    unfold auditNodes at hOk
    cases hNotary : decide (key ∈ pol.trustedNotaryKeys)
    · rw [hNotary] at hOk; cases hOk
    · rw [hNotary] at hOk
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hCanBool : checkHopCanonicalBounds domain req resp
      · rw [hCanBool] at hOk; cases hOk
      · rw [hCanBool] at hOk
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        have hCanProps := hCanBool
        simp only [checkHopCanonicalBounds, Bool.and_eq_true, decide_eq_true_eq] at hCanProps
        rcases hCanProps with ⟨⟨hDom, hReqLen⟩, hRespLen⟩
        cases hReq : matchesBytes pol.allowedRequestRe req
        · rw [hReq] at hOk; cases hOk
        · rw [hReq] at hOk
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
          cases hResp : matchesBytes pol.allowedResponseRe resp
          · rw [hResp] at hOk; cases hOk
          · rw [hResp] at hOk
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
            intro node hMem
            simp only [allSessionNodes, List.mem_cons] at hMem
            rcases hMem with rfl | hInKids
            · exact {
                trustedNotary    := of_decide_eq_true hNotary
                canonicalDomain  := hDom
                canonicalReqLen  := hReqLen
                canonicalRespLen := hRespLen
                requestMatches   := hReq
                responseMatches  := hResp
              }
            · exact auditChildren_all_hops_sound hOk node hInKids
termination_by structural tree

theorem auditChildren_all_hops_sound {pol : ZkStripePolicy} {kids : List HttpsSessionNode}
    (hOk : auditChildren pol kids = .ok ()) :
    ∀ node ∈ allChildrenSessionNodes kids, HopAudited pol node := by
  cases kids with
  | nil =>
    intro node hMem
    cases hMem
  | cons c cs =>
    unfold auditChildren at hOk
    cases hC : auditNodes pol c with
    | error e => rw [hC] at hOk; cases hOk
    | ok u =>
      rw [hC] at hOk
      intro node hMem
      simp only [allChildrenSessionNodes, List.mem_append] at hMem
      rcases hMem with hInC | hInCs
      · exact auditNodes_all_hops_sound hC node hInC
      · exact auditChildren_all_hops_sound hOk node hInCs
termination_by structural kids
end

theorem auditZkStripeCallTree_all_hops_sound {pol : ZkStripePolicy} {tree : HttpsSessionNode}
    (hAudit : auditZkStripeCallTree pol tree = .ok ()) :
    (∀ node ∈ allSessionNodes tree, HopAudited pol node) ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf (buildCallTreeProgram pol tree))
        pol.targetConclusion = .supported := by
  unfold auditZkStripeCallTree at hAudit
  cases hNodes : auditNodes pol tree with
  | error e => rw [hNodes] at hAudit; cases hAudit
  | ok u =>
    rw [hNodes] at hAudit
    simp only at hAudit
    cases hSt : (Obend.Reasons.statusIn (Obend.Reasons.wf (buildCallTreeProgram pol tree))
        pol.targetConclusion == .supported)
    · rw [hSt] at hAudit; cases hAudit
    · exact ⟨auditNodes_all_hops_sound hNodes, beq_iff_eq.mp hSt⟩

theorem auditNodes_root_props {pol : ZkStripePolicy} {tree : HttpsSessionNode}
    (hOk : auditNodes pol tree = .ok ()) :
    HopAudited pol tree :=
  auditNodes_all_hops_sound hOk tree (root_mem_allSessionNodes tree)

/-- A succinct receipt envelope for a redacted call tree: 256-bit digests. -/
structure DualPcsCallTreeReceipt where
  committedTreeRoot : CallTreeDigest
  notaryKey         : BitVec 256
  proofBytes        : List UInt8
  deriving DecidableEq

/-- A notary's attestation envelope over a session digest. -/
structure MpcTlsNotaryAttestation where
  notaryKey      : BitVec 256
  sessionDigest  : CallTreeDigest
  signatureBytes : List UInt8
  deriving DecidableEq

def checkMpcTlsNotaryEnvelope (trustedNotaryKeys : List (BitVec 256))
    (att : MpcTlsNotaryAttestation) : Bool :=
  decide (att.notaryKey ∈ trustedNotaryKeys) &&
  decide (att.sessionDigest.bytes.size = 32) &&
  decide (att.signatureBytes.length == 64)

def checkDualPcsReceiptEnvelope (pol : ZkStripePolicy)
    (rcpt : DualPcsCallTreeReceipt) : Bool :=
  decide (rcpt.notaryKey ∈ pol.trustedNotaryKeys) &&
  decide (rcpt.committedTreeRoot.bytes.size = 32) &&
  decide (32 ≤ rcpt.proofBytes.length)

/-- The external cryptographic obligations of the organ, as existential extractions:
1. `mpcTlsNotarySignatureOrigin`: an accepted attestation under a trusted key comes from a
   canonical session with that notary key and that digest;
2. `dualPcsWitnessExtraction`: an accepted receipt has a canonical tree with its root and notary
   that passes the audit. -/
class ZkStripeObligations : Prop where
  mpcTlsNotarySignatureOrigin :
    ∀ (H : Hash) (trustedKeys : List (BitVec 256)) (att : MpcTlsNotaryAttestation),
      checkMpcTlsNotaryEnvelope trustedKeys att = true →
      ∃ session : HttpsSessionNode,
        checkCanonicalSessionTree H session = true ∧
        session.notaryKey ∈ trustedKeys ∧
        session.notaryKey = att.notaryKey ∧
        callTreeDigest H session = att.sessionDigest ∧
        att.signatureBytes.length = 64
  dualPcsWitnessExtraction :
    ∀ (H : Hash) (pol : ZkStripePolicy) (rcpt : DualPcsCallTreeReceipt),
      checkDualPcsReceiptEnvelope pol rcpt = true →
      ∃ tree : HttpsSessionNode,
        checkCanonicalSessionTree H tree = true ∧
        callTreeDigest H tree = rcpt.committedTreeRoot ∧
        tree.notaryKey = rcpt.notaryKey ∧
        32 ≤ rcpt.proofBytes.length ∧
        auditZkStripeCallTree pol tree = .ok ()

/-- **The organ's audit theorem.** When the audit admits a canonical tree under a policy whose
request expression is `.inter reqSchema (.compl forbiddenSecretRe)`, then at every hop the policy
holds and the request matches no forbidden pattern; the target conclusion is supported in the
well-founded model; and the 256-bit digest binds the tree. -/
theorem apex_zkstripe_calltree_audit
    (H : Hash) (reqSchema forbiddenSecretRe : PredRE)
    (pol : ZkStripePolicy) (tree otherTree : HttpsSessionNode)
    (hReqPolicy : pol.allowedRequestRe = .inter reqSchema (.compl forbiddenSecretRe))
    (hAudit : auditZkStripeCallTree pol tree = .ok ())
    (hCan₁ : checkCanonicalSessionTree H tree = true)
    (hCan₂ : checkCanonicalSessionTree H otherTree = true)
    (hSameDigest : callTreeDigest H tree = callTreeDigest H otherTree) :
    (∀ node ∈ allSessionNodes tree,
        HopAudited pol node ∧
        matchesBytes forbiddenSecretRe node.redactedRequest = false) ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf (buildCallTreeProgram pol tree))
        pol.targetConclusion = .supported ∧
      (tree = otherTree ∨ Collision H) := by
  obtain ⟨hAllHops, hSupported⟩ := auditZkStripeCallTree_all_hops_sound hAudit
  refine ⟨?_, hSupported, callTreeDigest_binding H tree otherTree hCan₁ hCan₂ hSameDigest⟩
  intro node hMem
  have hHop := hAllHops node hMem
  have hReq := hHop.requestMatches
  rw [hReqPolicy, matchesBytes_inter, matchesBytes_compl, Bool.and_eq_true,
      Bool.not_eq_true'] at hReq
  exact ⟨hHop, hReq.2⟩

/-! ## §4. The audit carrier of a `DecoAndCallTree` call tree

The organ runs no grammar of its own: response framing is checked once, where the transcript is
committed. `DecoAndCallTree.checkView` asks that the redacted body of every attested hop passes
`VpaJson`'s RFC 8259 machine, with every mask confined in a value string. -/

open Obend.Judge.DecoAndCallTree (HttpsCallTree HttpsHop viewBytes treeHops forestHops)

/-- A host as a domain string, byte by byte (an ASCII host reads as itself). -/
def domainOf (host : ByteArray) : String :=
  host.data.toList.foldl (fun s b => s.push (Char.ofNat b.toNat)) ""

/-- A notary identifier as a 256-bit key: the big-endian reading of its bytes. -/
def notaryKeyOf (notary : ByteArray) : BitVec 256 := BitVec.ofNat 256 (ofBE notary.data.toList)

/-- One hop as the audit sees it: the notary, the host, the whole redacted request, and the
redacted response body (the slots after the HTTP head). -/
def sessionOfHop (h : HttpsHop) (children : List HttpsSessionNode) : HttpsSessionNode :=
  .mk (notaryKeyOf h.attestation.header.notary) (domainOf h.attestation.header.host)
    (viewBytes h.attestation.request.slots) (viewBytes h.attestation.response.slots.tail) children

mutual
/-- **The audit carrier of a call tree**: the same tree, each hop projected. -/
def sessionOfCallTree : HttpsCallTree → HttpsSessionNode
  | .node h cs => sessionOfHop h (sessionsOfForest cs)
termination_by structural t => t
def sessionsOfForest : List HttpsCallTree → List HttpsSessionNode
  | [] => []
  | t :: ts => sessionOfCallTree t :: sessionsOfForest ts
termination_by structural ts => ts
end

/-- What the audit reads of a session node. -/
def auditedView (n : HttpsSessionNode) : List UInt8 × List UInt8 :=
  (n.redactedRequest, n.redactedResponse)

/-- What the audit reads of a hop. -/
def hopView (h : HttpsHop) : List UInt8 × List UInt8 :=
  (viewBytes h.attestation.request.slots, viewBytes h.attestation.response.slots.tail)

mutual
/-- The audited nodes are the projections of the tree's hops, in preorder. -/
theorem allSessionNodes_sessionOfCallTree (t : HttpsCallTree) :
    (allSessionNodes (sessionOfCallTree t)).map auditedView = (treeHops t).map hopView := by
  cases t with
  | node h cs =>
    have ih := allChildren_sessionsOfForest cs
    show auditedView (sessionOfHop h (sessionsOfForest cs)) ::
        (allChildrenSessionNodes (sessionsOfForest cs)).map auditedView =
      hopView h :: (forestHops cs).map hopView
    rw [ih]
    rfl
termination_by structural t

theorem allChildren_sessionsOfForest (ts : List HttpsCallTree) :
    (allChildrenSessionNodes (sessionsOfForest ts)).map auditedView =
      (forestHops ts).map hopView := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have ih₁ := allSessionNodes_sessionOfCallTree t
    have ih₂ := allChildren_sessionsOfForest ts
    show (allSessionNodes (sessionOfCallTree t) ++
        allChildrenSessionNodes (sessionsOfForest ts)).map auditedView =
      (treeHops t ++ forestHops ts).map hopView
    rw [List.map_append, List.map_append, ih₁, ih₂]
termination_by structural ts
end

/-- **An admitted call tree is audited hop by hop.** If the audit admits the carrier of a
`DecoAndCallTree` tree, every hop of that tree has a redacted request matching the request
expression and a redacted response body matching the response expression. -/
theorem audit_covers_callTree_hops {pol : ZkStripePolicy} {t : HttpsCallTree}
    (hAudit : auditZkStripeCallTree pol (sessionOfCallTree t) = .ok ()) :
    ∀ h ∈ treeHops t,
      matchesBytes pol.allowedRequestRe (viewBytes h.attestation.request.slots) = true ∧
      matchesBytes pol.allowedResponseRe (viewBytes h.attestation.response.slots.tail) = true := by
  intro h hh
  have hmem : hopView h ∈ (allSessionNodes (sessionOfCallTree t)).map auditedView := by
    rw [allSessionNodes_sessionOfCallTree]
    exact List.mem_map.2 ⟨h, hh, rfl⟩
  obtain ⟨n, hn, he⟩ := List.mem_map.1 hmem
  have ha := (auditZkStripeCallTree_all_hops_sound hAudit).1 n hn
  simp only [auditedView, hopView, Prod.mk.injEq] at he
  exact ⟨he.1 ▸ ha.requestMatches, he.2 ▸ ha.responseMatches⟩

/-- **The framing the organ relies on.** A view admitted by `DecoAndCallTree.checkView` has a
redacted body that is empty or one RFC 8259 document: the audited response bytes of an attested
hop are JSON because the transcript layer checked them, with the string and escape state the
masks are confined by. -/
theorem checkView_body_framed {v : Obend.Judge.DecoAndCallTree.TranscriptView}
    (h : Obend.Judge.DecoAndCallTree.checkView v = true) :
    v.slots.tail = [] ∨ runFullJsonGrammar ⟨(viewBytes v.slots.tail).toArray⟩ = true := by
  obtain ⟨root, slots⟩ := v
  simp only [Obend.Judge.DecoAndCallTree.checkView, Bool.and_eq_true] at h
  obtain ⟨_, hm⟩ := h
  cases slots with
  | nil => simp at hm
  | cons slot body =>
    cases slot with
    | masked m => simp at hm
    | opened head sibs =>
      simp only [Bool.and_eq_true] at hm
      obtain ⟨_, hb⟩ := hm
      cases hrun : Obend.Judge.DecoAndCallTree.bodyRun Obend.Judge.VpaJson.JState.init body with
      | none => rw [hrun] at hb; cases hb
      | some st =>
        rw [hrun] at hb
        simp only [Bool.or_eq_true, List.isEmpty_iff] at hb
        rcases hb with he | hacc
        · exact Or.inl he
        · right
          have hst := Obend.Judge.DecoAndCallTree.bodyRun_viewBytes body _ _ hrun
          show Obend.Judge.VpaJson.jsonAccepting (Obend.Judge.VpaJson.jsonRun _) = true
          rw [Obend.Judge.VpaJson.jsonRun_eq]
          show Obend.Judge.VpaJson.jsonAccepting
            (Obend.Judge.VpaJson.specRunJson (viewBytes body) _) = true
          rw [hst]
          exact hacc

/-! ## §5. A four-hop call tree and its planted faults -/

/-- 4-byte-strided structural mixer (`termination_by structural`) so 130+-byte Merkle & FPGA
    receipt preimages reduce in `O(N/4)` WHNF stack depth well inside default `maxRecDepth`. -/
def hashMixBytes4 : List UInt8 → Nat
  | [] => 0x5A3C9E11
  | [b0] => Nat.xor 0x5A3C9E11 (b0.toBitVec.toNat + 1)
  | [b0, b1] =>
    Nat.xor 0x5A3C9E11 (b0.toBitVec.toNat * 256 + b1.toBitVec.toNat + 2)
  | [b0, b1, b2] =>
    Nat.xor 0x5A3C9E11
      (b0.toBitVec.toNat * 65536 + b1.toBitVec.toNat * 256 + b2.toBitVec.toNat + 3)
  | b0 :: b1 :: b2 :: b3 :: bs =>
    let word :=
      b0.toBitVec.toNat * 16777216 + b1.toBitVec.toNat * 65536 +
        b2.toBitVec.toNat * 256 + b3.toBitVec.toNat
    Nat.xor (hashMixBytes4 bs + 0x9E37) word
termination_by structural bs => bs

/-- The same mixer in 16-byte strides, falling back to 4-byte strides on the tail: a preimage of
a few hundred bytes reduces in a few dozen steps, so nested digests stay inside the default
recursion depth under `decide`. -/
def hashMixBytes16 : List UInt8 → Nat
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 ::
      b15 :: bs =>
    Nat.xor (hashMixBytes16 bs + 0x9E37)
      ((((((((((((((((b0.toNat * 256 + b1.toNat) * 256 + b2.toNat) * 256 + b3.toNat) * 256 +
        b4.toNat) * 256 + b5.toNat) * 256 + b6.toNat) * 256 + b7.toNat) * 256 + b8.toNat) * 256 +
        b9.toNat) * 256 + b10.toNat) * 256 + b11.toNat) * 256 + b12.toNat) * 256 + b13.toNat) *
        256 + b14.toNat) * 256 + b15.toNat) % 4294967291)
  | bs => hashMixBytes4 bs
termination_by structural bs => bs

/-- One 4-byte word of the fixture hash: the mix, offset by the word's index. -/
def mixWord (i : Nat) (h : Nat) : List UInt8 :=
  [UInt8.ofNat ((h + i * 2654435761) / 16777216), UInt8.ofNat ((h + i * 2654435761) / 65536),
   UInt8.ofNat ((h + i * 2654435761) / 256), UInt8.ofNat (h + i * 2654435761)]

/-- A 32-byte structural hash for kernel fixtures: one pass over the input, eight words. It is
not a cryptographic hash; the theorems hold for every `Hash`, and deployments instantiate
cSHAKE256. -/
def fastMerkleHash : Hash := fun bs =>
  mixWord 0 (hashMixBytes16 bs) ++ mixWord 1 (hashMixBytes16 bs) ++ mixWord 2 (hashMixBytes16 bs) ++
    mixWord 3 (hashMixBytes16 bs) ++ mixWord 4 (hashMixBytes16 bs) ++ mixWord 5 (hashMixBytes16 bs) ++
    mixWord 6 (hashMixBytes16 bs) ++ mixWord 7 (hashMixBytes16 bs)

/-- The fixture notary key. -/
def fixtureNotaryKey : BitVec 256 :=
  0xA11CE000000000000000000000000000000000000000000000000000000A11CE#256

/-- The forbidden live secret prefix `sk_`. -/
def stripeLiveKeyPrefix : List UInt8 := [115, 107, 95]

/-- The required request prefix `GET`. -/
def httpGetPrefix : List UInt8 := [71, 69, 84]

/-- The fixture policy: the fixture notary; requests begin with `GET` and nowhere contain `sk_`;
responses nowhere contain `sk_`; the four hops support `calltree_admitted`. -/
def defaultZkStripePolicy : ZkStripePolicy where
  trustedNotaryKeys   := [fixtureNotaryKey]
  allowedRequestRe    := .inter (startsWith httpGetPrefix) (forbidSubseq stripeLiveKeyPrefix)
  allowedResponseRe   := forbidSubseq stripeLiveKeyPrefix
  policyRules := [
    { name  := "admit_four_hop_calltree"
      concl := "calltree_admitted"
      pos   := ["hop_verified:api.stripe.com", "hop_verified:auth.obend.org",
                "hop_verified:registry.hf.co", "hop_verified:cdn.dataset.org"]
      neg   := ["emergency_freeze"] }
  ]
  targetConclusion := "calltree_admitted"

/-- Four hops; hop 2's response has an unmatched `}` inside a string. -/
def validFourHopCallTree : HttpsSessionNode :=
  .mk fixtureNotaryKey "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] (utf8Bytes "{\"v\":1}") [
    .mk fixtureNotaryKey "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107]
      (utf8Bytes "{\"tok\":\"ok}v1\"}") [
      .mk fixtureNotaryKey "registry.hf.co" [71, 69, 84, 32, 47, 109, 97, 110] [123, 125] [
        .mk fixtureNotaryKey "cdn.dataset.org" [71, 69, 84, 32, 47, 115, 104, 100] [91, 52, 50, 93] []
      ]
    ]
  ]

/-- Planted fault 1: `sk_` in hop 3's request. -/
def leakedSecretCallTree : HttpsSessionNode :=
  .mk fixtureNotaryKey "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] (utf8Bytes "{\"v\":1}") [
    .mk fixtureNotaryKey "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107] [123, 125] [
      .mk fixtureNotaryKey "registry.hf.co" [71, 69, 84, 32, 115, 107, 95, 57] [123, 125] []
    ]
  ]

/-- Planted fault 2: `sk_` in hop 4's response. -/
def leakedResponseCallTree : HttpsSessionNode :=
  .mk fixtureNotaryKey "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] (utf8Bytes "{\"v\":1}") [
    .mk fixtureNotaryKey "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107] [123, 125] [
      .mk fixtureNotaryKey "registry.hf.co" [71, 69, 84, 32, 47, 109, 97, 110] [123, 125] [
        .mk fixtureNotaryKey "cdn.dataset.org" [71, 69, 84, 32, 47, 115, 104, 100]
          (utf8Bytes "{\"k\":\"sk_9\"}") []
      ]
    ]
  ]

/-- Planted fault 3: only hop 1's domain differs. -/
def spoofedDomainCallTree : HttpsSessionNode :=
  match validFourHopCallTree with
  | .mk h _ req resp kids => .mk h "evil.stripe.io" req resp kids

private def decEqExceptUnit (a b : Except ZkStripeRefusal Unit) : Decidable (a = b) :=
  match a, b with
  | .ok (), .ok () => isTrue rfl
  | .ok (), .error _ => isFalse (by intro h; cases h)
  | .error _, .ok () => isFalse (by intro h; cases h)
  | .error e₁, .error e₂ =>
    if he : e₁ = e₂ then isTrue (by subst he; rfl)
    else isFalse (by intro h; cases h; exact he rfl)

example : auditNodes defaultZkStripePolicy validFourHopCallTree = .ok () := by
  letI : DecidableEq (Except ZkStripeRefusal Unit) := decEqExceptUnit
  decide

example : auditChildren defaultZkStripePolicy validFourHopCallTree.children = .ok () := by
  letI : DecidableEq (Except ZkStripeRefusal Unit) := decEqExceptUnit
  decide

example : auditZkStripeCallTree defaultZkStripePolicy validFourHopCallTree = .ok () := by
  letI : DecidableEq (Except ZkStripeRefusal Unit) := decEqExceptUnit
  decide

example : verifyZkStripeCallTree defaultZkStripePolicy validFourHopCallTree = true := by
  decide +kernel

example : checkCanonicalSessionTree fastMerkleHash validFourHopCallTree = true := by
  decide +kernel

example : callTreeDigest fastMerkleHash validFourHopCallTree ≠
    callTreeDigest fastMerkleHash spoofedDomainCallTree := by
  decide +kernel

/-- The organ's end-to-end smoke check. -/
def silverZkStripeSmoke : Bool :=
  let hopCountOk := callTreeHopCount validFourHopCallTree == 4
  let validAdmitted := verifyZkStripeCallTree defaultZkStripePolicy validFourHopCallTree
  let canonicalOk := checkCanonicalSessionTree fastMerkleHash validFourHopCallTree
  let wide := (callTreeDigest fastMerkleHash validFourHopCallTree).bytes.size == 32
  let domainBoundOk :=
    callTreeDigest fastMerkleHash validFourHopCallTree !=
      callTreeDigest fastMerkleHash spoofedDomainCallTree
  let leakRefused :=
    match auditZkStripeCallTree defaultZkStripePolicy leakedSecretCallTree with
    | .error e => e == .requestRegexViolation "registry.hf.co"
    | .ok () => false
  let responseLeakRefused :=
    match auditZkStripeCallTree defaultZkStripePolicy leakedResponseCallTree with
    | .error e => e == .responseRegexViolation "cdn.dataset.org"
    | .ok () => false
  hopCountOk && validAdmitted && canonicalOk && wide && domainBoundOk &&
    leakRefused && responseLeakRefused

example : silverZkStripeSmoke = true := by
  decide +kernel

end Obend.Trailblaze.ZkStripe
end
