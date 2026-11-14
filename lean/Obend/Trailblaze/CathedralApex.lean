module
/- Authenticated call-tree and cluster-governance composition. -/
public import Obend.Judge.Class
public import Obend.Reasons
public import Obend.Digest.HashBytes
public import Obend.Judge.SymbolicRegexBisim
public import Obend.Judge.VpaComplementAndJson
public import Obend.Judge.DecoAndCallTree
import all Obend.Codec.DetCbor
import all Obend.Judge.SymbolicRegexBisim
import all Obend.Judge.VpaComplementAndJson
import all Obend.Judge.DecoAndCallTree
public import Obend.Hardware.Gpu.Rdna2.Semantics
import all Obend.Hardware.Gpu.Rdna2.Semantics
import Init.Data.List.Sublist
import Init.Data.String.Lemmas
import all Init.Data.String.Legacy
public import Obend.Run.HyperLaw

public section


namespace Obend.Trailblaze
set_option autoImplicit false

/-! ## 2. Executable Silver Workflows & `SilverSound` -/

/-- Executable Trailblazer workflow class pairing a live runner `runValid`, constructive named
    refusal `refuseInvalid`, declarative domain invariant `Spec`, and completeness domain `CompleteOn`. -/
class SilverWorkflow (W : Type) where
  /-- Independent declarative domain specification established by accepted runs. -/
  Spec : W → Prop
  /-- Admissible workflow domain on which `runValid` decides `Spec` completely. -/
  CompleteOn : W → Prop
  /-- Live executable Silver check (`true` iff the workflow succeeds end-to-end). -/
  runValid : W → Bool
  /-- Constructive named refusal (`none` when admitted, `some clauseName` when refused). -/
  refuseInvalid : W → Option String
  /-- Exact alignment between boolean acceptance and absence of named refusal. -/
  refuse_iff : ∀ w : W, runValid w = true ↔ refuseInvalid w = none
  /-- `SilverSound` law: every accepted Silver run satisfies `Spec`. -/
  silverSound : ∀ w : W, runValid w = true → Spec w
  /-- Every accepted Silver run belongs to the completeness domain `CompleteOn`. -/
  silverCompleteDomain : ∀ w : W, runValid w = true → CompleteOn w
  /-- Completeness law: every `CompleteOn` workflow input satisfying `Spec` is accepted by `runValid`. -/
  silverComplete : ∀ w : W, CompleteOn w → Spec w → runValid w = true

/-- Standalone propositional statement of the `SilverSound` law for workflow carrier `W`. -/
def SilverSound (W : Type) [wf : SilverWorkflow W] : Prop :=
  ∀ w : W, wf.runValid w = true → wf.Spec w

/-- Every `SilverWorkflow` instance constructively inhabits `SilverSound`. -/
theorem silverWorkflow_satisfies_silverSound
    (W : Type) [wf : SilverWorkflow W] (w : W)
    (hRun : wf.runValid w = true) :
    wf.Spec w :=
  wf.silverSound w hRun

/-- Every admitted `SilverWorkflow` input produces `none` from `refuseInvalid`. -/
theorem SilverWorkflow.admitted_no_refusal
    {W : Type} [wf : SilverWorkflow W] (w : W)
    (hRun : wf.runValid w = true) :
    wf.refuseInvalid w = none :=
  (wf.refuse_iff w).mp hRun

/-- Every rejected `SilverWorkflow` input (`runValid w = false`) produces an explicit named refusal string. -/
theorem SilverWorkflow.rejected_names_clause
    {W : Type} [wf : SilverWorkflow W] (w : W)
    (hRej : wf.runValid w = false) :
    ∃ reason : String, wf.refuseInvalid w = some reason := by
  cases hOpt : wf.refuseInvalid w with
  | none =>
    have hValid : wf.runValid w = true := (wf.refuse_iff w).mpr hOpt
    rw [hValid] at hRej
    cases hRej
  | some reason =>
    exact ⟨reason, rfl⟩

/-- Product composition of two `SilverWorkflow`s: runs both checks, preserves completeness domains,
    and reports the first named refusal. -/
@[instance_reducible] def SilverWorkflow.prod (W₁ W₂ : Type)
    [wf₁ : SilverWorkflow W₁] [wf₂ : SilverWorkflow W₂] :
    SilverWorkflow (W₁ × W₂) where
  Spec := fun p => wf₁.Spec p.1 ∧ wf₂.Spec p.2
  CompleteOn := fun p => wf₁.CompleteOn p.1 ∧ wf₂.CompleteOn p.2
  runValid := fun p => wf₁.runValid p.1 && wf₂.runValid p.2
  refuseInvalid := fun p =>
    match wf₁.refuseInvalid p.1 with
    | some r => some r
    | none => wf₂.refuseInvalid p.2
  refuse_iff := by
    intro ⟨w₁, w₂⟩
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨h₁, h₂⟩
      rw [(wf₁.refuse_iff w₁).mp h₁]
      exact (wf₂.refuse_iff w₂).mp h₂
    · intro hNone
      cases hOpt₁ : wf₁.refuseInvalid w₁ with
      | some r =>
        rw [hOpt₁] at hNone
        cases hNone
      | none =>
        rw [hOpt₁] at hNone
        exact ⟨(wf₁.refuse_iff w₁).mpr hOpt₁, (wf₂.refuse_iff w₂).mpr hNone⟩
  silverSound := by
    intro ⟨w₁, w₂⟩ hBoth
    simp only [Bool.and_eq_true] at hBoth
    exact ⟨wf₁.silverSound w₁ hBoth.1, wf₂.silverSound w₂ hBoth.2⟩
  silverCompleteDomain := by
    intro ⟨w₁, w₂⟩ hBoth
    simp only [Bool.and_eq_true] at hBoth
    exact ⟨wf₁.silverCompleteDomain w₁ hBoth.1, wf₂.silverCompleteDomain w₂ hBoth.2⟩
  silverComplete := by
    intro ⟨w₁, w₂⟩ ⟨hDom₁, hDom₂⟩ ⟨hSpec₁, hSpec₂⟩
    simp only [Bool.and_eq_true]
    exact ⟨wf₁.silverComplete w₁ hDom₁ hSpec₁, wf₂.silverComplete w₂ hDom₂ hSpec₂⟩

/-- Lift any `SilverWorkflow W` into a grade-monotone, genuinely refuting `Obend.Judge W Unit`
    whose `Fragment` is inhabited by every admitted workflow turn. -/
@[instance_reducible] def SilverWorkflow.toJudge (W : Type) [wf : SilverWorkflow W] : Obend.Judge W Unit where
  Clause := String
  Meaning := fun w _cert => wf.CompleteOn w ∧ wf.Spec w
  check := fun _grade w _cert =>
    match wf.refuseInvalid w with
    | none => .ok
    | some clause => .refused clause []
  sound := by
    intro _r w _c hOk
    cases hOpt : wf.refuseInvalid w with
    | none =>
      have hRun : wf.runValid w = true := (wf.refuse_iff w).mpr hOpt
      exact ⟨wf.silverCompleteDomain w hRun, wf.silverSound w hRun⟩
    | some clause =>
      rw [hOpt] at hOk
      cases hOk
  refutes := fun _clause => true
  refuted := by
    intro _r w _c clause _p hCheck _hRef _c' ⟨hDom, hSpec⟩
    have hRun : wf.runValid w = true := wf.silverComplete w hDom hSpec
    have hNone : wf.refuseInvalid w = none := (wf.refuse_iff w).mp hRun
    rw [hNone] at hCheck
    cases hCheck
  Fragment := fun w => wf.CompleteOn w ∧ wf.Spec w
  complete := by
    intro w ⟨hDom, hSpec⟩ _hEx
    have hRun : wf.runValid w = true := wf.silverComplete w hDom hSpec
    have hNone : wf.refuseInvalid w = none := (wf.refuse_iff w).mp hRun
    refine ⟨(), 0, ?_⟩
    rw [hNone]
  mono := by
    intro _r _r' _o _c _hle _hDec
    rfl

/-- Every admitted `SilverWorkflow` input inhabits `(SilverWorkflow.toJudge W).Fragment`. -/
theorem SilverWorkflow.admitted_in_judge_fragment
    {W : Type} [wf : SilverWorkflow W] (w : W)
    (hRun : wf.runValid w = true) :
    (SilverWorkflow.toJudge W).Fragment w :=
  ⟨wf.silverCompleteDomain w hRun, wf.silverSound w hRun⟩

/-- Every rejected `SilverWorkflow` input inside `CompleteOn` refutes `Spec`. -/
theorem SilverWorkflow.rejected_refutes_spec
    {W : Type} [wf : SilverWorkflow W] (w : W)
    (hRej : wf.runValid w = false)
    (hDom : wf.CompleteOn w) :
    ¬ wf.Spec w := by
  intro hSpec
  have hRun : wf.runValid w = true := wf.silverComplete w hDom hSpec
  rw [hRun] at hRej
  cases hRej

end Obend.Trailblaze


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

def notaryKey : HttpsSessionNode → BitVec 256
  | .mk k _ _ _ _ => k

def serverDomain : HttpsSessionNode → String
  | .mk _ d _ _ _ => d

def redactedRequest : HttpsSessionNode → List UInt8
  | .mk _ _ req _ _ => req

def redactedResponse : HttpsSessionNode → List UInt8
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
/-- The finite list of messages actually hashed by this tree. -/
def treePreimages (H : Hash) : HttpsSessionNode → List (List UInt8)
  | .mk k d req resp cs =>
    sessionNodePreimage k d req resp (callTreeChildrenDigestBytes H cs) :: childrenPreimages H cs
termination_by structural t => t
def childrenPreimages (H : Hash) : List HttpsSessionNode → List (List UInt8)
  | [] => []
  | t :: ts => treePreimages H t ++ childrenPreimages H ts
termination_by structural ts => ts
end

/-- Executable evidence: exact equal output bytes, between messages from the compared trees. -/
structure TreeHashCollision (H : Hash) (inputs : List (List UInt8)) where
  left : List UInt8
  right : List UInt8
  left_mem : left ∈ inputs
  right_mem : right ∈ inputs
  ne : left ≠ right
  eq : H left = H right

def TreeHashCollision.weaken {H : Hash} {xs ys : List (List UInt8)}
    (c : TreeHashCollision H xs) (h : ∀ x ∈ xs, x ∈ ys) : TreeHashCollision H ys :=
  ⟨c.left, c.right, h _ c.left_mem, h _ c.right_mem, c.ne, c.eq⟩

mutual
def callTreeDigest_binding_aux (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionTree H t₁ = true)
    (hCan₂ : checkCanonicalSessionTree H t₂ = true)
    (hEq : callTreeDigestBytes H t₁ = callTreeDigestBytes H t₂) :
    PSum (t₁ = t₂) (TreeHashCollision H (treePreimages H t₁ ++ treePreimages H t₂)) := by
  cases t₁ with
  | mk k₁ d₁ req₁ resp₁ cs₁ =>
    cases t₂ with
    | mk k₂ d₂ req₂ resp₂ cs₂ =>
      simp only [checkCanonicalSessionTree, Bool.and_eq_true, decide_eq_true_eq] at hCan₁ hCan₂
      obtain ⟨⟨⟨⟨hd₁, hr₁⟩, hs₁⟩, _⟩, hc₁⟩ := hCan₁
      obtain ⟨⟨⟨⟨hd₂, hr₂⟩, hs₂⟩, _⟩, hc₂⟩ := hCan₂
      let p₁ := sessionNodePreimage k₁ d₁ req₁ resp₁ (callTreeChildrenDigestBytes H cs₁)
      let p₂ := sessionNodePreimage k₂ d₂ req₂ resp₂ (callTreeChildrenDigestBytes H cs₂)
      if hp : p₁ = p₂ then
        obtain ⟨hk, hd, hr, hs, hc⟩ := sessionNodePreimage_inj hd₁ hd₂ hr₁ hr₂ hs₁ hs₂ hp
        match callTreeChildrenDigestBytes_binding_aux H cs₁ cs₂ hc₁ hc₂ hc with
        | .inl he => exact .inl (by rw [hk, hd, hr, hs, he])
        | .inr c => exact .inr (c.weaken (by
            intro x hx
            simp only [treePreimages, List.mem_append, List.mem_cons] at *
            rcases hx with hx | hx
            · exact Or.inl (Or.inr hx)
            · exact Or.inr (Or.inr hx)))
      else
        exact .inr ⟨p₁, p₂, by simp [treePreimages, p₁], by simp [treePreimages, p₂], hp, hEq⟩
termination_by structural t₁

def callTreeChildrenDigestBytes_binding_aux (H : Hash) (xs ys : List HttpsSessionNode)
    (hx : checkCanonicalSessionChildren H xs = true)
    (hy : checkCanonicalSessionChildren H ys = true)
    (he : callTreeChildrenDigestBytes H xs = callTreeChildrenDigestBytes H ys) :
    PSum (xs = ys) (TreeHashCollision H (childrenPreimages H xs ++ childrenPreimages H ys)) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => exact .inl rfl
    | cons b bs => simp [callTreeChildrenDigestBytes] at he
  | cons a as =>
    cases ys with
    | nil => simp [callTreeChildrenDigestBytes] at he
    | cons b bs =>
      simp only [checkCanonicalSessionChildren, Bool.and_eq_true] at hx hy
      have ha : (callTreeDigestBytes H a).length < 2 ^ 32 := by rw [canonical_digest_width hx.1]; decide
      have hb : (callTreeDigestBytes H b).length < 2 ^ 32 := by rw [canonical_digest_width hy.1]; decide
      have he' := (List.cons.inj he).2
      obtain ⟨hhead, htail⟩ := frameBytes_append_inj ha hb he'
      match callTreeDigest_binding_aux H a b hx.1 hy.1 hhead with
      | .inr c => exact .inr (c.weaken (by
          intro x hx
          simp only [childrenPreimages, List.mem_append] at *
          rcases hx with hx | hx
          · exact Or.inl (Or.inl hx)
          · exact Or.inr (Or.inl hx)))
      | .inl hab =>
        match callTreeChildrenDigestBytes_binding_aux H as bs hx.2 hy.2 htail with
        | .inl ht => exact .inl (by rw [hab, ht])
        | .inr c => exact .inr (c.weaken (by
            intro x hx
            simp only [childrenPreimages, List.mem_append] at *
            rcases hx with hx | hx
            · exact Or.inl (Or.inr hx)
            · exact Or.inr (Or.inr hx)))
termination_by structural xs
end

/-- Compare preimages constructively; the collision branch retains both exact messages. -/
def extractCallTreeCollision (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (h₁ : checkCanonicalSessionTree H t₁ = true) (h₂ : checkCanonicalSessionTree H t₂ = true)
    (he : callTreeDigestBytes H t₁ = callTreeDigestBytes H t₂) :
    PSum (t₁ = t₂) (TreeHashCollision H (treePreimages H t₁ ++ treePreimages H t₂)) :=
  callTreeDigest_binding_aux H t₁ t₂ h₁ h₂ he

/-- Binding is scoped to the finite union of messages hashed by the two trees. -/
theorem callTreeDigestBytes_binding (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionTree H t₁ = true)
    (hCan₂ : checkCanonicalSessionTree H t₂ = true)
    (hEq : callTreeDigestBytes H t₁ = callTreeDigestBytes H t₂) :
    t₁ = t₂ ∨ Obend.Digest.HashBytes.CollisionAmong H
      (fun x => x ∈ treePreimages H t₁ ++ treePreimages H t₂) :=
  match extractCallTreeCollision H t₁ t₂ hCan₁ hCan₂ hEq with
  | .inl h => Or.inl h
  | .inr c => Or.inr ⟨c.left, c.right, c.left_mem, c.right_mem, c.ne, congrArg ofBE c.eq⟩

/-- **The 256-bit digest binds** within the finite preimage union of the two trees. -/
theorem callTreeDigest_binding (H : Hash) (t₁ t₂ : HttpsSessionNode)
    (hCan₁ : checkCanonicalSessionTree H t₁ = true)
    (hCan₂ : checkCanonicalSessionTree H t₂ = true)
    (hEq : callTreeDigest H t₁ = callTreeDigest H t₂) :
    t₁ = t₂ ∨ Obend.Digest.HashBytes.CollisionAmong H
      (fun x => x ∈ treePreimages H t₁ ++ treePreimages H t₂) := by
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
termination_by structural t => t

def callTreeChildrenHopCount : List HttpsSessionNode → Nat
  | [] => 0
  | c :: cs => callTreeHopCount c + callTreeChildrenHopCount cs
termination_by structural ts => ts
end

/-! ## §3. The audit -/

/-- Verifier-owned TLS session evidence. Session keys come from the trusted TLS adapter;
the caller supplies attestations, never a replacement verification function. -/
structure ZkStripeVerifiers where
  policy : Obend.Judge.DecoAndCallTree.DecoPolicy
  ledger : Obend.Judge.DecoAndCallTree.SessionLedger
  attestations : List Obend.Judge.DecoAndCallTree.DecoAttestation

/-- Bind the audit's exact bytes to an authenticated DECO view. Checking the views is
essential: the GHASH record commitment alone does not authenticate arbitrary view bytes. -/
def checkSessionAuthentication (v : ZkStripeVerifiers) (key : BitVec 256)
    (domain : String) (req resp : List UInt8) : Bool :=
  v.attestations.any fun a =>
    decide (a.header.notary.data.toList = be 32 key.toNat) &&
    decide (a.header.host = domain.toUTF8) &&
    decide (Obend.Judge.DecoAndCallTree.viewBytes a.request.slots = req) &&
    decide (Obend.Judge.DecoAndCallTree.viewBytes a.response.slots.tail = resp) &&
    Obend.Judge.DecoAndCallTree.checkDecoAttestation v.policy v.ledger a

/-- Semantic authentication evidence, including the exact disclosed bytes and the
DECO freshness, policy, GHASH, and authenticated-span relation. -/
def SessionAuthenticated (v : ZkStripeVerifiers) (key : BitVec 256)
    (domain : String) (req resp : List UInt8) : Prop :=
  ∃ a ∈ v.attestations,
    a.header.notary.data.toList = be 32 key.toNat ∧ a.header.host = domain.toUTF8 ∧
    Obend.Judge.DecoAndCallTree.viewBytes a.request.slots = req ∧
    Obend.Judge.DecoAndCallTree.viewBytes a.response.slots.tail = resp ∧
    Obend.Judge.DecoAndCallTree.DecoRelation v.policy v.ledger a

theorem checkSessionAuthentication_sound {v : ZkStripeVerifiers} {key : BitVec 256}
    {domain : String} {req resp : List UInt8}
    (h : checkSessionAuthentication v key domain req resp = true) :
    SessionAuthenticated v key domain req resp := by
  simp only [checkSessionAuthentication, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨a, ha, ⟨⟨⟨⟨hk, hd⟩, hq⟩, hr⟩, hv⟩⟩ := h
  exact ⟨a, ha, hk, hd, hq, hr,
    (Obend.Judge.DecoAndCallTree.checkDecoAttestation_iff_relation _ _ _).mp hv⟩

theorem checkSessionAuthentication_complete {v : ZkStripeVerifiers} {key : BitVec 256}
    {domain : String} {req resp : List UInt8}
    (h : SessionAuthenticated v key domain req resp) :
    checkSessionAuthentication v key domain req resp = true := by
  obtain ⟨a, ha, hk, hd, hq, hr, hv⟩ := h
  simp only [checkSessionAuthentication, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨a, ha, ⟨⟨⟨⟨hk, hd⟩, hq⟩, hr⟩,
    (Obend.Judge.DecoAndCallTree.checkDecoAttestation_iff_relation _ _ _).mpr hv⟩⟩

/-- The audit policy: the notary keys trusted, the request and response expressions, and the
rules and target of the `Obend.Reasons` program over the verified hops. -/
structure ZkStripePolicy where
  verifiers : ZkStripeVerifiers
  trustedNotaryKeys   : List (BitVec 256)
  allowedRequestRe    : PredRE
  allowedResponseRe   : PredRE
  policyRules         : List Obend.Reasons.Rule
  targetConclusion    : String

inductive ZkStripeRefusal where
  | unauthenticatedSession (domain : String)
  | untrustedNotary (domain : String)
  | nonCanonicalBounds (domain : String)
  | requestRegexViolation (domain : String)
  | malformedJson (domain : String)
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
termination_by structural t => t

def extractChildrenFacts (pol : ZkStripePolicy) : List HttpsSessionNode → List String
  | [] => []
  | c :: cs => extractCallTreeFacts pol c ++ extractChildrenFacts pol cs
termination_by structural ts => ts
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
    else if !runFullJsonGrammar ⟨resp.toArray⟩ then
      .error (.malformedJson domain)
    else if !checkSessionAuthentication pol.verifiers key domain req resp then
      .error (.unauthenticatedSession domain)
    else
      auditChildren pol kids
termination_by structural t => t

def auditChildren (pol : ZkStripePolicy) :
    List HttpsSessionNode → Except ZkStripeRefusal Unit
  | [] => .ok ()
  | c :: cs =>
    match auditNodes pol c with
    | .error e => .error e
    | .ok () => auditChildren pol cs
termination_by structural ts => ts
end

open Obend.Judge.DecoAndCallTree in
/-- Match the exact hop bytes and authenticate against the current, consumed ledger. -/
def sessionMatch (v : ZkStripeVerifiers) (ledger : SessionLedger)
    (n : HttpsSessionNode) (a : DecoAttestation) : Bool :=
  decide (a.header.notary.data.toList = be 32 n.notaryKey.toNat) &&
  decide (a.header.host = n.serverDomain.toUTF8) &&
  decide (viewBytes a.request.slots = n.redactedRequest) &&
  decide (viewBytes a.response.slots.tail = n.redactedResponse) &&
  checkDecoAttestation v.policy ledger a

open Obend.Judge.DecoAndCallTree in
/-- Consume in pre-order: a child or sibling sees every earlier hop's nonce and intent. -/
def consumeSessionNodes (v : ZkStripeVerifiers) : SessionLedger → List HttpsSessionNode →
    Option SessionLedger
  | ledger, [] => some ledger
  | ledger, n :: ns => do
    let a ← v.attestations.find? (sessionMatch v ledger n)
    consumeSessionNodes v (consume ledger a) ns

open Obend.Judge.DecoAndCallTree in
theorem consumeSessionNodes_sound (v : ZkStripeVerifiers) (nodes : List HttpsSessionNode)
    (initial final : SessionLedger) (h : consumeSessionNodes v initial nodes = some final) :
    ∃ attestations, attestations.length = nodes.length ∧
      ValidDecoTrace v.policy initial attestations final := by
  induction nodes generalizing initial with
  | nil => cases h; exact ⟨[], rfl, .nil _⟩
  | cons n ns ih =>
    unfold consumeSessionNodes at h
    cases hf : v.attestations.find? (sessionMatch v initial n) with
    | none => simp [hf] at h
    | some a =>
      rw [hf] at h
      obtain ⟨rest, hlen, ht⟩ := ih (consume initial a) h
      have hm := List.find?_some hf
      simp only [sessionMatch, Bool.and_eq_true] at hm
      exact ⟨a :: rest, by simp [hlen],
        .cons ((checkDecoAttestation_iff_relation _ _ _).mp hm.2) ht⟩

open Obend.Judge.DecoAndCallTree in
/-- Every accepted pre-order suffix preserves consumed nonces and payment intents. -/
theorem consumeSessionNodes_no_replay (v : ZkStripeVerifiers) (nodes : List HttpsSessionNode)
    (initial final : SessionLedger) (h : consumeSessionNodes v initial nodes = some final)
    (a : DecoAttestation) :
    (a.header.verifierNonce ∈ initial.consumedNonces → checkDecoAttestation v.policy final a = false) ∧
    (a.header.paymentIntentId ∈ initial.consumedIntents → checkDecoAttestation v.policy final a = false) := by
  obtain ⟨as, _, ht⟩ := consumeSessionNodes_sound v nodes initial final h
  exact ⟨replay_nonce_rejected _ _ _ as ht a, replay_intent_rejected _ _ _ as ht a⟩

open Obend.Judge.DecoAndCallTree in
/-- Acceptance preserves unique nonce and payment-intent histories at every hop. -/
theorem consumeSessionNodes_unique (v : ZkStripeVerifiers) (nodes : List HttpsSessionNode)
    (initial final : SessionLedger) (h : consumeSessionNodes v initial nodes = some final)
    (hn : initial.consumedNonces.Nodup) (hi : initial.consumedIntents.Nodup) :
    final.consumedNonces.Nodup ∧ final.consumedIntents.Nodup := by
  obtain ⟨as, hlen, ht⟩ := consumeSessionNodes_sound v nodes initial final h
  clear h hlen
  induction ht with
  | nil => exact ⟨hn, hi⟩
  | cons hr _ ih =>
    exact ih (List.nodup_cons.mpr ⟨hr.1.1, hn⟩)
      (List.nodup_cons.mpr ⟨hr.1.2.1, hi⟩)

/-- **The audit**: every hop, then the policy program's support for the target conclusion. -/
def auditZkStripeCallTree (pol : ZkStripePolicy) (root : HttpsSessionNode) :
    Except ZkStripeRefusal Unit :=
  match auditNodes pol root with
  | .error e => .error e
  | .ok () =>
    let prog := buildCallTreeProgram pol root
    let st := Obend.Reasons.statusIn (Obend.Reasons.wf prog) pol.targetConclusion
    if st == .supported then
      match consumeSessionNodes pol.verifiers pol.verifiers.ledger (allSessionNodes root) with
      | some _ => .ok ()
      | none => .error (.unauthenticatedSession root.serverDomain)
    else
      .error (.policyUnsupported pol.targetConclusion st)

theorem auditZkStripeCallTree_consumes (pol : ZkStripePolicy) (root : HttpsSessionNode)
    (h : auditZkStripeCallTree pol root = .ok ()) :
    ∃ final, consumeSessionNodes pol.verifiers pol.verifiers.ledger (allSessionNodes root) = some final := by
  unfold auditZkStripeCallTree at h
  cases hn : auditNodes pol root with
  | error e => simp [hn] at h
  | ok u =>
    cases u
    rw [hn] at h
    dsimp only at h
    split at h
    · cases hc : consumeSessionNodes pol.verifiers pol.verifiers.ledger (allSessionNodes root) with
      | none => rw [hc] at h; cases h
      | some final => exact ⟨final, rfl⟩
    · cases h

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
  responseJson : runFullJsonGrammar ⟨node.redactedResponse.toArray⟩ = true
  authenticated : SessionAuthenticated pol.verifiers node.notaryKey node.serverDomain
    node.redactedRequest node.redactedResponse

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
            cases hJson : runFullJsonGrammar ⟨resp.toArray⟩
            · rw [hJson] at hOk; cases hOk
            · rw [hJson] at hOk
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
              cases hAuth : checkSessionAuthentication pol.verifiers key domain req resp
              · rw [hAuth] at hOk; cases hOk
              · rw [hAuth] at hOk
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
                    responseJson := hJson
                    authenticated := checkSessionAuthentication_sound hAuth
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
      (tree = otherTree ∨ Obend.Digest.HashBytes.CollisionAmong H
        (fun x => x ∈ treePreimages H tree ++ treePreimages H otherTree)) := by
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

/-- Four hops; hop 2's response has an unmatched `}` inside a string. -/
def validFourHopCallTree : HttpsSessionNode :=
  .mk fixtureNotaryKey "api.stripe.com" ([71, 69, 84, 32, 47, 118, 49] ++ [13, 10, 13, 10, 123, 125]) (utf8Bytes "{\"v\":1}") [
    .mk fixtureNotaryKey "auth.obend.org" ([71, 69, 84, 32, 47, 116, 111, 107] ++ [13, 10, 13, 10, 123, 125])
      (utf8Bytes "{\"tok\":\"ok}v1\"}") [
      .mk fixtureNotaryKey "registry.hf.co" ([71, 69, 84, 32, 47, 109, 97, 110] ++ [13, 10, 13, 10, 123, 125]) [123, 125] [
        .mk fixtureNotaryKey "cdn.dataset.org" ([71, 69, 84, 32, 47, 115, 104, 100] ++ [13, 10, 13, 10, 123, 125]) [91, 52, 50, 93] []
      ]
    ]
  ]

/-- Fully opened two-span HTTP view, with real cSHAKE256 inclusion paths. -/
def fixtureSessionView (head body : ByteArray) : Obend.Judge.DecoAndCallTree.TranscriptView :=
  let spans := [head, body]
  ⟨Obend.Judge.VpaJson.spanMerkleRoot Obend.Judge.Commit.cshakeHasher
      Obend.Judge.VpaJson.spanTag spans,
    (List.range 2).map fun i => .opened (spans.getD i ByteArray.empty)
      (Obend.Judge.VpaJson.spanMerkleProof Obend.Judge.Commit.cshakeHasher
        Obend.Judge.VpaJson.spanTag spans i).siblings⟩

/-- Public fixture key only; deployments receive fresh secret session keys from TLS. -/
def fixtureSessionKey : Obend.Crypto.BinaryTower256.Tower128 :=
  Obend.Crypto.BinaryTower256.unpackTower 7 0x0123456789abcdef0fedcba987654321

def fixtureSessionAttestation (n : HttpsSessionNode) (epoch : Nat := 0) : Obend.Judge.DecoAndCallTree.DecoAttestation :=
  let a : Obend.Judge.DecoAndCallTree.DecoAttestation :=
    { header := ⟨n.serverDomain.toUTF8, ⟨(be 32 n.notaryKey.toNat).toArray⟩,
        1, (n.serverDomain ++ toString epoch).toUTF8, (n.serverDomain ++ toString epoch).toUTF8⟩
      request := fixtureSessionView ⟨(n.redactedRequest.take (n.redactedRequest.length - 2)).toArray⟩ "{}".toUTF8
      response := fixtureSessionView "HTTP/1.1 200 OK\r\n\r\n".toUTF8 ⟨n.redactedResponse.toArray⟩
      ctBlocks := []
      lenBlock := Obend.Judge.DecoAndCallTree.recordLengthBlock []
      ghashTag := Obend.Crypto.BinaryTower256.towerZero 7 }
  { a with
    ghashTag :=
      Obend.Crypto.BinaryTower256.ghashAuth fixtureSessionKey
        (Obend.Judge.DecoAndCallTree.commitBlocks (Obend.Judge.DecoAndCallTree.recordCommit a))
        a.ctBlocks a.lenBlock }

def fixtureSessionVerifiers (epoch : Nat := 0) : ZkStripeVerifiers where
  policy := ⟨(allSessionNodes validFourHopCallTree).map (fun n => ((n.serverDomain ++ toString epoch).toUTF8, fixtureSessionKey)),
    [⟨(be 32 fixtureNotaryKey.toNat).toArray⟩],
    (allSessionNodes validFourHopCallTree).map (fun n => n.serverDomain.toUTF8), 0, 10, []⟩
  ledger := ⟨[], []⟩
  attestations := (allSessionNodes validFourHopCallTree).map (fun n => fixtureSessionAttestation n epoch)

/-- The fixture policy: the fixture notary; requests begin with `GET` and nowhere contain `sk_`;
responses nowhere contain `sk_`; the four hops support `calltree_admitted`. -/
def defaultZkStripePolicy : ZkStripePolicy where
  verifiers := fixtureSessionVerifiers 0
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

/-- Planted fault 1: `sk_` in hop 3's request. -/
def leakedSecretCallTree : HttpsSessionNode :=
  .mk fixtureNotaryKey "api.stripe.com" ([71, 69, 84, 32, 47, 118, 49] ++ [13, 10, 13, 10, 123, 125]) (utf8Bytes "{\"v\":1}") [
    .mk fixtureNotaryKey "auth.obend.org" ([71, 69, 84, 32, 47, 116, 111, 107] ++ [13, 10, 13, 10, 123, 125]) (utf8Bytes "{\"tok\":\"ok}v1\"}") [
      .mk fixtureNotaryKey "registry.hf.co" ([71, 69, 84, 32, 115, 107, 95, 57] ++ [13, 10, 13, 10, 123, 125]) [123, 125] []
    ]
  ]

/-- Planted fault 2: `sk_` in hop 4's response. -/
def leakedResponseCallTree : HttpsSessionNode :=
  .mk fixtureNotaryKey "api.stripe.com" ([71, 69, 84, 32, 47, 118, 49] ++ [13, 10, 13, 10, 123, 125]) (utf8Bytes "{\"v\":1}") [
    .mk fixtureNotaryKey "auth.obend.org" ([71, 69, 84, 32, 47, 116, 111, 107] ++ [13, 10, 13, 10, 123, 125]) (utf8Bytes "{\"tok\":\"ok}v1\"}") [
      .mk fixtureNotaryKey "registry.hf.co" ([71, 69, 84, 32, 47, 109, 97, 110] ++ [13, 10, 13, 10, 123, 125]) [123, 125] [
        .mk fixtureNotaryKey "cdn.dataset.org" ([71, 69, 84, 32, 47, 115, 104, 100] ++ [13, 10, 13, 10, 123, 125])
          (utf8Bytes "{\"k\":\"sk_9\"}") []
      ]
    ]
  ]

/-- Planted fault 3: only hop 1's domain differs. -/
def spoofedDomainCallTree : HttpsSessionNode :=
  match validFourHopCallTree with
  | .mk h _ req resp kids => .mk h "evil.stripe.io" req resp kids

example : checkCanonicalSessionTree fastMerkleHash validFourHopCallTree = true := by
  decide +kernel

example : callTreeDigest fastMerkleHash validFourHopCallTree ≠
    callTreeDigest fastMerkleHash spoofedDomainCallTree := by
  decide +kernel

/-- The binding premise is inhabited at the deployment hash, without reducing SHAKE in the kernel. -/
theorem cshake_callTree_binding_inhabited :
    ∃ t : HttpsSessionNode,
      checkCanonicalSessionTree (Obend.Digest.Cshake256.cshake256Bytes []) t = true ∧
      callTreeDigestBytes (Obend.Digest.Cshake256.cshake256Bytes []) t =
        callTreeDigestBytes (Obend.Digest.Cshake256.cshake256Bytes []) t := by
  refine ⟨.mk fixtureNotaryKey "api.stripe.com" [71, 69, 84] [123, 125] [], ?_, rfl⟩
  simp [checkCanonicalSessionTree, checkCanonicalSessionChildren, utf8Bytes]
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


end Obend.Trailblaze.ZkStripe


namespace Obend.Trailblaze.ClusterGov

open Obend.Run.HyperLaw (LowView HyperLaw2NonInterference checkHyperLaw2NonInterference
  checkHyperLaw2NonInterference_sound checkHyperLaw2Step checkLowEquiv)

set_option autoImplicit false

/-! ## §1. Overflow-Free Integer Dot-Product, `Array Int` `Exec` Fast Path & Centered $\mathbb{F}_p$ Reconstruction -/

/-- KoalaBear 31-bit prime `p = 2^31 - 2^24 + 1` (`2130706433`) for wrap-free integer inference. -/
def koalaBearPrime : Nat := 2130706433

/-- Certified integer dot-product / linear layer envelope over prime field modulus `modulusP`. -/
structure IntTensorBound where
  dim          : Nat
  maxAbsWeight : Nat
  maxAbsAct    : Nat
  modulusP     : Nat
  deriving DecidableEq, Repr

/-- Wrap-freedom guard: `2 * dim * maxAbsWeight * maxAbsAct < modulusP` guarantees
    every signed accumulator `z` lies strictly inside `(-modulusP / 2, modulusP / 2)`. -/
def checkSableNoWrap (b : IntTensorBound) : Bool :=
  decide (2 * b.dim * b.maxAbsWeight * b.maxAbsAct < b.modulusP)

/-- Exact integer inner product `∑ᵢ wᵢ xᵢ` (`List Int` specification). -/
def intDot : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | w :: ws, x :: xs => w * x + intDot ws xs

/-- Structural index loop for the `Array Int` inner-product `Exec` fast path. -/
def intDotExecLoop (ws xs : Array Int) (idx : Nat) : Nat → Int → Int
  | 0, acc => acc
  | rem + 1, acc =>
    if hw : idx < ws.size then
      if hx : idx < xs.size then
        intDotExecLoop ws xs (idx + 1) rem (acc + ws[idx] * xs[idx])
      else
        acc
    else
      acc
termination_by structural rem => rem

/-- Tight `Array Int` inner-product `Exec` fast path (`O(min |ws| |xs|)` with zero list allocation). -/
def intDotExec (ws xs : Array Int) : Int :=
  intDotExecLoop ws xs 0 (min ws.size xs.size) 0

theorem intDotExecLoop_eq_intDot (ws xs : Array Int) (idx rem : Nat)
    (hRem : idx + rem = min ws.size xs.size) (acc : Int) :
    intDotExecLoop ws xs idx rem acc =
      acc + intDot (ws.toList.drop idx) (xs.toList.drop idx) := by
  induction rem generalizing idx acc with
  | zero =>
    have hMin : min ws.size xs.size = idx := by omega
    unfold intDotExecLoop
    if hW : idx < ws.size then
      have hX : xs.toList.length ≤ idx := by
        rw [Array.length_toList]
        omega
      have hDropX : xs.toList.drop idx = [] := List.drop_eq_nil_of_le hX
      rw [hDropX]
      cases ws.toList.drop idx <;> simp [intDot]
    else
      have hWLe : ws.toList.length ≤ idx := by
        rw [Array.length_toList]
        omega
      have hDropW : ws.toList.drop idx = [] := List.drop_eq_nil_of_le hWLe
      rw [hDropW]
      simp [intDot]
  | succ r ih =>
    have hW : idx < ws.size := by omega
    have hX : idx < xs.size := by omega
    have hWL : idx < ws.toList.length := by rw [Array.length_toList]; exact hW
    have hXL : idx < xs.toList.length := by rw [Array.length_toList]; exact hX
    have hDropW : ws.toList.drop idx = ws[idx] :: ws.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons hWL]; rfl
    have hDropX : xs.toList.drop idx = xs[idx] :: xs.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons hXL]; rfl
    unfold intDotExecLoop
    simp only [hW, hX, ↓reduceDIte]
    have hNext : (idx + 1) + r = min ws.size xs.size := by omega
    rw [ih (idx + 1) hNext (acc + ws[idx] * xs[idx]), hDropW, hDropX]
    dsimp only [intDot]
    omega

/-- **`Spec ↔ Exec` Dot-Product Equivalence**: `intDotExec ws xs` computes the exact same integer
    inner product as `intDot ws.toList xs.toList`. -/
theorem intDotExec_eq_intDot (ws xs : Array Int) :
    intDotExec ws xs = intDot ws.toList xs.toList := by
  unfold intDotExec
  have h := intDotExecLoop_eq_intDot ws xs 0 (min ws.size xs.size) (Nat.zero_add _) 0
  simpa using h

/-- Canonical residue embedding into `[0, p)` modulo `p`. -/
def embedModP (p : Nat) (z : Int) : Int :=
  z % (p : Int)

/-- Centered signed representative reconstruction from a field residue modulo `p`. -/
def decodeSignedModP (p : Nat) (r : Int) : Int :=
  if decide (2 * (r % (p : Int)) < (p : Int)) then
    r % (p : Int)
  else
    r % (p : Int) - (p : Int)

/-- Declarative L∞ bound on an integer vector. -/
def VecAbsBounded (bound : Nat) (xs : List Int) : Prop :=
  ∀ x ∈ xs, x.natAbs ≤ bound

/-- Executable boolean L∞ bound checker on an integer vector. -/
def checkVecAbsBounded (bound : Nat) (xs : List Int) : Bool :=
  xs.all (fun x => decide (x.natAbs ≤ bound))

theorem checkVecAbsBounded_sound {bound : Nat} {xs : List Int}
    (h : checkVecAbsBounded bound xs = true) :
    VecAbsBounded bound xs := by
  intro x hx
  have hAll := List.all_eq_true.mp h x hx
  exact of_decide_eq_true hAll

/-- Cauchy–Schwarz / L1–L∞ accumulator bound: `|∑ᵢ wᵢ xᵢ| ≤ dim * maxW * maxX`. -/
theorem intDot_natAbs_le (ws xs : List Int) (dim maxW maxX : Nat)
    (hLen : ws.length ≤ dim)
    (hW : VecAbsBounded maxW ws)
    (hX : VecAbsBounded maxX xs) :
    (intDot ws xs).natAbs ≤ dim * maxW * maxX := by
  induction ws generalizing xs dim with
  | nil =>
    simp [intDot]
  | cons w wsRest ih =>
    cases xs with
    | nil => simp [intDot]
    | cons x xsRest =>
      cases dim with
      | zero =>
        simp at hLen
      | succ d =>
        have hw : w.natAbs ≤ maxW := hW w (List.mem_cons_self ..)
        have hx : x.natAbs ≤ maxX := hX x (List.mem_cons_self ..)
        have hProd : (w * x).natAbs ≤ maxW * maxX := by
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul hw hx
        have hTailLen : wsRest.length ≤ d := by
          simp at hLen
          omega
        have hTail : (intDot wsRest xsRest).natAbs ≤ d * maxW * maxX :=
          ih xsRest d hTailLen
            (fun u hu => hW u (List.mem_cons_of_mem _ hu))
            (fun v hv => hX v (List.mem_cons_of_mem _ hv))
        have hTri : (w * x + intDot wsRest xsRest).natAbs ≤
            (w * x).natAbs + (intDot wsRest xsRest).natAbs :=
          Int.natAbs_add_le (w * x) (intDot wsRest xsRest)
        have hStep : (d + 1) * maxW * maxX = maxW * maxX + d * maxW * maxX := by
          rw [Nat.succ_mul, Nat.add_mul, Nat.add_comm]
        dsimp only [intDot]
        omega

/-- **Centered Modular Exactness**: Any integer `z` with `2 * |z| < p` embeds into `ℤ/pℤ` and
    reconstructs via `decodeSignedModP` to `z` with zero wraparound error. -/
theorem decodeSignedModP_embedModP_exact (p : Nat) (z : Int)
    (hNoWrap : 2 * z.natAbs < p) :
    decodeSignedModP p (embedModP p z) = z := by
  unfold decodeSignedModP embedModP
  if hz : 0 ≤ z then
    have hLtP : z < (p : Int) := by omega
    have hMod1 : z % (p : Int) = z := Int.emod_eq_of_lt hz hLtP
    rw [hMod1, hMod1]
    have hTwoLt : 2 * z < (p : Int) := by omega
    have hDec : decide (2 * z < (p : Int)) = true := decide_eq_true hTwoLt
    rw [hDec]
    rfl
  else
    have hPosShift : 0 ≤ z + (p : Int) := by omega
    have hLtShift : z + (p : Int) < (p : Int) := by omega
    have hModNeg : z % (p : Int) = z + (p : Int) := by
      have hAddMod : (z + (p : Int) * 1) % (p : Int) = z % (p : Int) :=
        Int.add_mul_emod_self_left z (p : Int) 1
      rw [Int.mul_one] at hAddMod
      rw [← hAddMod]
      exact Int.emod_eq_of_lt hPosShift hLtShift
    rw [hModNeg, Int.emod_eq_of_lt hPosShift hLtShift]
    have hNotLt : ¬ (2 * (z + (p : Int)) < (p : Int)) := by omega
    have hDecFalse : decide (2 * (z + (p : Int)) < (p : Int)) = false :=
      decide_eq_false hNotLt
    rw [hDecFalse]
    change (z + (p : Int)) - (p : Int) = z
    omega

/-- **Modular Injectivity on the No-Wrap Envelope**: Distinct integers inside `(-p/2, p/2)`
    never collide modulo `p`. -/
theorem embedModP_injective_of_no_wrap {p : Nat} {z₁ z₂ : Int}
    (h₁ : 2 * z₁.natAbs < p) (h₂ : 2 * z₂.natAbs < p)
    (hEq : embedModP p z₁ = embedModP p z₂) :
    z₁ = z₂ := by
  have e₁ := decodeSignedModP_embedModP_exact p z₁ h₁
  have e₂ := decodeSignedModP_embedModP_exact p z₂ h₂
  rw [← e₁, ← e₂, hEq]

/-- **Overflow-Free Dot-Product Exactness Theorem (`sable_dot_exact_no_wrap`)**:
    Whenever `checkSableNoWrap b = true`, every weight vector `ws` and activation vector `xs`
    within `b` satisfies `2 * |⟨ws, xs⟩| < b.modulusP` and exact modular round-trip reconstruction. -/
theorem sable_dot_exact_no_wrap (b : IntTensorBound) (ws xs : List Int)
    (hGuard : checkSableNoWrap b = true)
    (hLen : ws.length ≤ b.dim)
    (hW : VecAbsBounded b.maxAbsWeight ws)
    (hX : VecAbsBounded b.maxAbsAct xs) :
    2 * (intDot ws xs).natAbs < b.modulusP ∧
      decodeSignedModP b.modulusP (embedModP b.modulusP (intDot ws xs)) = intDot ws xs := by
  have hBoundLt : 2 * b.dim * b.maxAbsWeight * b.maxAbsAct < b.modulusP :=
    of_decide_eq_true hGuard
  have hAbsLe : (intDot ws xs).natAbs ≤ b.dim * b.maxAbsWeight * b.maxAbsAct :=
    intDot_natAbs_le ws xs b.dim b.maxAbsWeight b.maxAbsAct hLen hW hX
  have hTwoMul :
      2 * (b.dim * b.maxAbsWeight * b.maxAbsAct) =
        2 * b.dim * b.maxAbsWeight * b.maxAbsAct := by
    simp [Nat.mul_assoc]
  have hStrict : 2 * (intDot ws xs).natAbs < b.modulusP := by
    have hMulLe := Nat.mul_le_mul_left 2 hAbsLe
    omega
  exact ⟨hStrict, decodeSignedModP_embedModP_exact b.modulusP (intDot ws xs) hStrict⟩

/-- `Array Int` `Exec` corollary of `sable_dot_exact_no_wrap`. -/
theorem sable_dotExec_exact_no_wrap (b : IntTensorBound) (ws xs : Array Int)
    (hGuard : checkSableNoWrap b = true)
    (hLen : ws.size ≤ b.dim)
    (hW : VecAbsBounded b.maxAbsWeight ws.toList)
    (hX : VecAbsBounded b.maxAbsAct xs.toList) :
    2 * (intDotExec ws xs).natAbs < b.modulusP ∧
      decodeSignedModP b.modulusP (embedModP b.modulusP (intDotExec ws xs)) =
        intDot ws.toList xs.toList := by
  rw [intDotExec_eq_intDot]
  have hLenList : ws.toList.length ≤ b.dim := by rw [Array.length_toList]; exact hLen
  exact sable_dot_exact_no_wrap b ws.toList xs.toList hGuard hLenList hW hX


/-! ## §2. Bit-Exact Integer-Sliced Collectives (`Ozaki`), `Array` `Exec` Fast Path & `HyperLaw2` -/

/-- Componentwise exact integer addition on fixed-radix mantissa slices (zero-extended). -/
def sliceVecAdd : List Int → List Int → List Int
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: sliceVecAdd xs ys

@[simp] theorem sliceVecAdd_nil_left (ys : List Int) :
    sliceVecAdd [] ys = ys := by
  cases ys <;> rfl

@[simp] theorem sliceVecAdd_nil_right (xs : List Int) :
    sliceVecAdd xs [] = xs := by
  cases xs <;> rfl

/-- Commutativity of integer-slice vector addition. -/
theorem sliceVecAdd_comm (xs ys : List Int) :
    sliceVecAdd xs ys = sliceVecAdd ys xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs' ih =>
    cases ys with
    | nil => rfl
    | cons y ys' =>
      dsimp only [sliceVecAdd]
      rw [Int.add_comm, ih ys']

/-- Associativity of integer-slice vector addition (fails for IEEE-754 floats!). -/
theorem sliceVecAdd_assoc (xs ys zs : List Int) :
    sliceVecAdd (sliceVecAdd xs ys) zs = sliceVecAdd xs (sliceVecAdd ys zs) := by
  induction xs generalizing ys zs with
  | nil => rfl
  | cons x xs' ih =>
    cases ys with
    | nil => rfl
    | cons y ys' =>
      cases zs with
      | nil => rfl
      | cons z zs' =>
        dsimp only [sliceVecAdd]
        rw [Int.add_assoc, ih ys' zs']

/-- Multi-worker integer-slice reduction across GPU workers (`List` specification). -/
def ozakiSliceSum (workers : List (List Int)) : List Int :=
  workers.foldr sliceVecAdd []

/-- Structural index loop for componentwise `Array Int` slice addition (zero-extended). -/
def sliceVecAddExecLoop (xs ys : Array Int) (idx : Nat) : Nat → Array Int → Array Int
  | 0, acc => acc
  | rem + 1, acc =>
    if hx : idx < xs.size then
      if hy : idx < ys.size then
        sliceVecAddExecLoop xs ys (idx + 1) rem (acc.push (xs[idx] + ys[idx]))
      else
        sliceVecAddExecLoop xs ys (idx + 1) rem (acc.push xs[idx])
    else if hy : idx < ys.size then
      sliceVecAddExecLoop xs ys (idx + 1) rem (acc.push ys[idx])
    else
      acc
termination_by structural rem => rem

/-- Tight `Array Int` `Exec` fast path for componentwise integer-slice addition. -/
def sliceVecAddExec (xs ys : Array Int) : Array Int :=
  let n := max xs.size ys.size
  sliceVecAddExecLoop xs ys 0 n (Array.emptyWithCapacity n)

theorem sliceVecAddExecLoop_eq_spec (xs ys : Array Int) (idx rem : Nat)
    (hRem : idx + rem = max xs.size ys.size) (acc : Array Int) :
    (sliceVecAddExecLoop xs ys idx rem acc).toList =
      acc.toList ++ sliceVecAdd (xs.toList.drop idx) (ys.toList.drop idx) := by
  induction rem generalizing idx acc with
  | zero =>
    have hXLe : xs.toList.length ≤ idx := by rw [Array.length_toList]; omega
    have hYLe : ys.toList.length ≤ idx := by rw [Array.length_toList]; omega
    rw [List.drop_eq_nil_of_le hXLe, List.drop_eq_nil_of_le hYLe]
    simp [sliceVecAddExecLoop, sliceVecAdd]
  | succ r ih =>
    have hNext : (idx + 1) + r = max xs.size ys.size := by omega
    unfold sliceVecAddExecLoop
    if hx : idx < xs.size then
      have hxL : idx < xs.toList.length := by rw [Array.length_toList]; exact hx
      have hDropX : xs.toList.drop idx = xs[idx] :: xs.toList.drop (idx + 1) := by
        rw [List.drop_eq_getElem_cons hxL]; rfl
      if hy : idx < ys.size then
        have hyL : idx < ys.toList.length := by rw [Array.length_toList]; exact hy
        have hDropY : ys.toList.drop idx = ys[idx] :: ys.toList.drop (idx + 1) := by
          rw [List.drop_eq_getElem_cons hyL]; rfl
        simp only [hx, hy, ↓reduceDIte]
        rw [ih (idx + 1) hNext (acc.push (xs[idx] + ys[idx])), hDropX, hDropY]
        simp [Array.toList_push, sliceVecAdd, List.append_assoc]
      else
        have hyLe : ys.toList.length ≤ idx := by rw [Array.length_toList]; omega
        have hyLeNext : ys.toList.length ≤ idx + 1 := by omega
        have hDropY : ys.toList.drop idx = [] := List.drop_eq_nil_of_le hyLe
        have hDropYNext : ys.toList.drop (idx + 1) = [] := List.drop_eq_nil_of_le hyLeNext
        simp only [hx, hy, ↓reduceDIte]
        rw [ih (idx + 1) hNext (acc.push xs[idx]), hDropX, hDropY, hDropYNext]
        simp [Array.toList_push, sliceVecAdd, List.append_assoc]
    else
      have hy : idx < ys.size := by omega
      have hyL : idx < ys.toList.length := by rw [Array.length_toList]; exact hy
      have hDropY : ys.toList.drop idx = ys[idx] :: ys.toList.drop (idx + 1) := by
        rw [List.drop_eq_getElem_cons hyL]; rfl
      have hxLe : xs.toList.length ≤ idx := by rw [Array.length_toList]; omega
      have hxLeNext : xs.toList.length ≤ idx + 1 := by omega
      have hDropX : xs.toList.drop idx = [] := List.drop_eq_nil_of_le hxLe
      have hDropXNext : xs.toList.drop (idx + 1) = [] := List.drop_eq_nil_of_le hxLeNext
      simp only [hx, hy, ↓reduceDIte]
      rw [ih (idx + 1) hNext (acc.push ys[idx]), hDropX, hDropXNext, hDropY]
      simp [Array.toList_push, sliceVecAdd, List.append_assoc]

/-- **`Spec ↔ Exec` Slice Addition Equivalence**: `sliceVecAddExec` refines `sliceVecAdd`. -/
theorem sliceVecAddExec_eq_sliceVecAdd (xs ys : Array Int) :
    (sliceVecAddExec xs ys).toList = sliceVecAdd xs.toList ys.toList := by
  unfold sliceVecAddExec
  have h := sliceVecAddExecLoop_eq_spec xs ys 0 (max xs.size ys.size) (Nat.zero_add _)
    (Array.emptyWithCapacity (max xs.size ys.size))
  simpa using h

/-- Structural worker loop for `ozakiSliceSumExec`. -/
def ozakiSliceSumExecLoop (workers : Array (Array Int)) (idx : Nat) :
    Nat → Array Int → Array Int
  | 0, acc => acc
  | rem + 1, acc =>
    if hw : idx < workers.size then
      ozakiSliceSumExecLoop workers (idx + 1) rem (sliceVecAddExec acc workers[idx])
    else
      acc
termination_by structural rem => rem

/-- Tight `Array (Array Int)` `Exec` fast path for multi-worker Ozaki slice reduction. -/
def ozakiSliceSumExec (workers : Array (Array Int)) : Array Int :=
  ozakiSliceSumExecLoop workers 0 workers.size #[]

theorem ozakiSliceSumExecLoop_eq_spec (workers : Array (Array Int)) (idx rem : Nat)
    (hRem : idx + rem = workers.size) (acc : Array Int) :
    (ozakiSliceSumExecLoop workers idx rem acc).toList =
      sliceVecAdd acc.toList (ozakiSliceSum ((workers.toList.drop idx).map Array.toList)) := by
  induction rem generalizing idx acc with
  | zero =>
    have hLe : workers.toList.length ≤ idx := by rw [Array.length_toList]; omega
    rw [List.drop_eq_nil_of_le hLe]
    simp [ozakiSliceSumExecLoop, ozakiSliceSum]
  | succ r ih =>
    have hw : idx < workers.size := by omega
    have hwL : idx < workers.toList.length := by rw [Array.length_toList]; exact hw
    have hDrop : workers.toList.drop idx = workers[idx] :: workers.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons hwL]; rfl
    have hNext : (idx + 1) + r = workers.size := by omega
    unfold ozakiSliceSumExecLoop
    simp only [hw, ↓reduceDIte]
    rw [ih (idx + 1) hNext (sliceVecAddExec acc workers[idx]),
        sliceVecAddExec_eq_sliceVecAdd, hDrop]
    dsimp only [List.map, ozakiSliceSum, List.foldr]
    rw [sliceVecAdd_assoc]

/-- **`Spec ↔ Exec` Multi-Worker Ozaki Equivalence**: `ozakiSliceSumExec` over `Array (Array Int)`
    produces the exact same integer slice vector as `ozakiSliceSum`. -/
theorem ozakiSliceSumExec_eq_ozakiSliceSum (workers : Array (Array Int)) :
    (ozakiSliceSumExec workers).toList = ozakiSliceSum (workers.toList.map Array.toList) := by
  unfold ozakiSliceSumExec
  have h := ozakiSliceSumExecLoop_eq_spec workers 0 workers.size (Nat.zero_add _) #[]
  simpa using h

theorem ozakiSliceSum_append (w₁ w₂ : List (List Int)) :
    ozakiSliceSum (w₁ ++ w₂) = sliceVecAdd (ozakiSliceSum w₁) (ozakiSliceSum w₂) := by
  induction w₁ with
  | nil => rfl
  | cons s rest ih =>
    dsimp only [List.cons_append, ozakiSliceSum, List.foldr] at ih ⊢
    rw [ih, sliceVecAdd_assoc]

/-- **Worker-Order / Permutation Invariance (`ozakiSliceSum_perm`)**:
    Permuting GPU worker arrival order leaves `ozakiSliceSum` bit-for-bit identical. -/
theorem ozakiSliceSum_perm {w₁ w₂ : List (List Int)}
    (hPerm : List.Perm w₁ w₂) :
    ozakiSliceSum w₁ = ozakiSliceSum w₂ := by
  induction hPerm with
  | nil => rfl
  | cons s _ ih =>
    dsimp only [ozakiSliceSum, List.foldr] at ih ⊢
    rw [ih]
  | swap s₁ s₂ rest =>
    dsimp only [ozakiSliceSum, List.foldr]
    rw [← sliceVecAdd_assoc, sliceVecAdd_comm s₂ s₁, sliceVecAdd_assoc]
  | trans _ _ ih₁ ih₂ =>
    exact ih₁.trans ih₂

/-- Arbitrary binary AllReduce reduction tree schedule (ring, butterfly, straggler tree). -/
inductive AllReduceTree where
  | empty : AllReduceTree
  | leaf (slices : List Int) : AllReduceTree
  | node (left right : AllReduceTree) : AllReduceTree
  deriving DecidableEq, Repr

/-- Reduce an `AllReduceTree` according to its exact parenthesization / tree topology. -/
def evalAllReduceTree : AllReduceTree → List Int
  | .empty => []
  | .leaf s => s
  | .node l r => sliceVecAdd (evalAllReduceTree l) (evalAllReduceTree r)

/-- Left-to-right leaf frontier of an `AllReduceTree`. -/
def flattenAllReduceTree : AllReduceTree → List (List Int)
  | .empty => []
  | .leaf s => [s]
  | .node l r => flattenAllReduceTree l ++ flattenAllReduceTree r

/-- **Tree-Topology / Re-Association Invariance (`ozaki_tree_schedule_invariant`)**:
    Every binary reduction tree over a sequence of GPU worker slices computes the exact same
    slice vector as canonical `ozakiSliceSum`. -/
theorem ozaki_tree_schedule_invariant (t : AllReduceTree) :
    evalAllReduceTree t = ozakiSliceSum (flattenAllReduceTree t) := by
  induction t with
  | empty => rfl
  | leaf s =>
    dsimp only [evalAllReduceTree, flattenAllReduceTree, ozakiSliceSum, List.foldr]
    rw [sliceVecAdd_nil_right]
  | node l r ihl ihr =>
    dsimp only [evalAllReduceTree, flattenAllReduceTree]
    rw [ihl, ihr, ozakiSliceSum_append]

/-- Reconstruct an exact scaled integer from radix-`B` Ozaki slices (`s₀ + B·s₁ + B²·s₂ + …`). -/
def evalRadixSlices (radix : Int) : List Int → Int
  | [] => 0
  | s :: ss => s + radix * evalRadixSlices radix ss

/-- `sliceVecAdd` is an exact homomorphism for radix evaluation at any radix `B`. -/
theorem evalRadixSlices_sliceVecAdd (radix : Int) (xs ys : List Int) :
    evalRadixSlices radix (sliceVecAdd xs ys) =
      evalRadixSlices radix xs + evalRadixSlices radix ys := by
  induction xs generalizing ys with
  | nil => simp [evalRadixSlices]
  | cons x xs' ih =>
    cases ys with
    | nil => simp [evalRadixSlices]
    | cons y ys' =>
      dsimp only [sliceVecAdd, evalRadixSlices]
      rw [ih ys', Int.mul_add]
      omega

/-- Multi-tenant cluster AllReduce world: `publicReducedSlices` is visible to low-security
    tenant outputs while `secretScheduleTag` records high-security co-tenant scheduling decisions. -/
structure ClusterReduceWorld where
  publicReducedSlices : List Int
  secretScheduleTag   : Nat
  deriving DecidableEq, Repr

/-- Low-security observer sees only the reduced slice vector, never the secret schedule tag. -/
def clusterPublicView : LowView ClusterReduceWorld (List Int) where
  observe w := w.publicReducedSlices

/-- Execute one cluster collective step from a tree schedule `t` and secret co-tenant tag `sec`. -/
def runScheduledAllReduce (t : AllReduceTree) (sec : Nat) : ClusterReduceWorld where
  publicReducedSlices := evalAllReduceTree t
  secretScheduleTag   := sec

/-- **Covert-Channel Closure Theorem (`ozaki_closes_schedule_covert_channel`)**:
    For any two AllReduce tree schedules `t₁, t₂` whose worker leaves are permutations of each
    other (`List.Perm (flattenAllReduceTree t₁) (flattenAllReduceTree t₂)`), varying the secret
    co-tenant schedule tag (`sec₁` vs `sec₂`) and tree parenthesization preserves `HyperLaw2`
    observational non-interference (`HyperLaw2NonInterference clusterPublicView`). -/
theorem ozaki_closes_schedule_covert_channel
    (init₁ init₂ : ClusterReduceWorld)
    (t₁ t₂ : AllReduceTree) (sec₁ sec₂ : Nat)
    (hPerm : List.Perm (flattenAllReduceTree t₁) (flattenAllReduceTree t₂)) :
    HyperLaw2NonInterference clusterPublicView
      [(init₁, init₂), (runScheduledAllReduce t₁ sec₁, runScheduledAllReduce t₂ sec₂)] := by
  apply checkHyperLaw2NonInterference_sound
  dsimp only [checkHyperLaw2NonInterference]
  cases checkLowEquiv clusterPublicView init₁ init₂
  · rfl
  · simp only [List.all_cons, List.all_nil, Bool.and_true, checkHyperLaw2Step, checkLowEquiv,
      clusterPublicView, runScheduledAllReduce]
    rw [ozaki_tree_schedule_invariant t₁, ozaki_tree_schedule_invariant t₂,
        ozakiSliceSum_perm hPerm]
    exact decide_eq_true rfl


/-! ## §3. `AriadneStep` Lineage, Authority-Pinned RTT & Lower-Curve Energy Conservation -/

/-- Lineage & compute-cap commitment for one verifiable AI training/inference step (`AriadneStep`). -/
structure AriadneStep where
  prevWeightsRoot   : Nat
  batchCallTreeRoot : Nat
  nextWeightsRoot   : Nat
  flopsUsed         : Nat
  flopsCap          : Nat
  deriving DecidableEq, Repr

/-- Authority-pinned physical round-trip latency and lower-curve metered energy envelope:
    - `authorityBudgetMicros` is pinned by the verifier hardware class (never prover-chosen;
      `proverClaimedBudgetMicros` is untrusted metadata ignored by acceptance).
    - `lowerCurveProvenMilliJ` (`E_lo`) and `idleEnergyMilliJ` (`E_idle`) credit only the minimum
      physically necessary energy of proven compute, preventing upper-curve subtraction masking.
    - `minHiddenOpMilliJ` (`e_min > 0`) bounds unproved shadow FLOPs via metered residual energy. -/
structure PhysicalEnergyEnvelope where
  measuredRttMicros         : Nat
  authorityBudgetMicros     : Nat
  proverClaimedBudgetMicros : Nat := 0
  meterEnergyMilliJ         : Nat
  lowerCurveProvenMilliJ    : Nat
  idleEnergyMilliJ          : Nat
  toleranceMilliJ           : Nat
  minHiddenOpMilliJ         : Nat
  hiddenOpsCap              : Nat
  deriving DecidableEq, Repr

/-- Metered residual energy above the proven lower curve and idle baseline:
    `meter + η - E_lo - E_idle`. -/
def physicalResidualMilliJ (env : PhysicalEnergyEnvelope) : Nat :=
  (env.meterEnergyMilliJ + env.toleranceMilliJ) - env.lowerCurveProvenMilliJ - env.idleEnergyMilliJ

/-- Executable verifier check for `PhysicalEnergyEnvelope`: enforces positive `minHiddenOpMilliJ`,
    authority-pinned RTT `measuredRttMicros ≤ authorityBudgetMicros`, and residual energy ceiling
    `physicalResidualMilliJ env ≤ minHiddenOpMilliJ * hiddenOpsCap`. -/
def checkPhysicalEnergyEnvelope (env : PhysicalEnergyEnvelope) : Bool :=
  decide (0 < env.minHiddenOpMilliJ ∧
    env.measuredRttMicros ≤ env.authorityBudgetMicros ∧
    env.lowerCurveProvenMilliJ + env.idleEnergyMilliJ ≤ env.meterEnergyMilliJ ∧
    physicalResidualMilliJ env ≤ env.minHiddenOpMilliJ * env.hiddenOpsCap)

/-- Accepted metering covers the baseline before tolerance is added or naturals
are subtracted. Tolerance cannot conceal an under-metered baseline. -/
theorem checkPhysicalEnergyEnvelope_no_underflow (env : PhysicalEnergyEnvelope)
    (h : checkPhysicalEnergyEnvelope env = true) :
    env.lowerCurveProvenMilliJ + env.idleEnergyMilliJ ≤ env.meterEnergyMilliJ := by
  exact (of_decide_eq_true h).2.2.1

/-- **Unconditional Lower-Curve Energy Conservation & Authority-Pinned RTT Theorem**:
    Whenever `checkPhysicalEnergyEnvelope env = true`:
    1. `env.measuredRttMicros ≤ env.authorityBudgetMicros`, and mutating the prover's claimed
       RTT budget never alters verifier acceptance;
    2. For any unproved shadow operation count `hiddenOps` satisfying metered energy conservation
       `e_min * hiddenOps ≤ meter + η - E_lo - E_idle`, `hiddenOps ≤ env.hiddenOpsCap`;
    3. Equivalently, any shadow FLOP count `hiddenOps > env.hiddenOpsCap` strictly violates
       metered physical energy conservation. -/
theorem energy_conservation_bounds_hidden_ops
    (env : PhysicalEnergyEnvelope) (hiddenOps : Nat)
    (hEnv : checkPhysicalEnergyEnvelope env = true) :
    env.measuredRttMicros ≤ env.authorityBudgetMicros ∧
      (∀ claimed : Nat,
        checkPhysicalEnergyEnvelope { env with proverClaimedBudgetMicros := claimed } = true) ∧
      (env.minHiddenOpMilliJ * hiddenOps ≤
        (env.meterEnergyMilliJ + env.toleranceMilliJ) -
          env.lowerCurveProvenMilliJ - env.idleEnergyMilliJ →
        hiddenOps ≤ env.hiddenOpsCap) ∧
      (env.hiddenOpsCap < hiddenOps →
        ¬ (env.minHiddenOpMilliJ * hiddenOps ≤
          (env.meterEnergyMilliJ + env.toleranceMilliJ) -
            env.lowerCurveProvenMilliJ - env.idleEnergyMilliJ)) := by
  have hDec := of_decide_eq_true hEnv
  rcases hDec with ⟨hPos, hRtt, _hBaseline, hRes⟩
  unfold physicalResidualMilliJ at hRes
  have hBound :
      env.minHiddenOpMilliJ * hiddenOps ≤
        (env.meterEnergyMilliJ + env.toleranceMilliJ) -
          env.lowerCurveProvenMilliJ - env.idleEnergyMilliJ →
      hiddenOps ≤ env.hiddenOpsCap := by
    intro hPhys
    have hChain : env.minHiddenOpMilliJ * hiddenOps ≤ env.minHiddenOpMilliJ * env.hiddenOpsCap :=
      Nat.le_trans hPhys hRes
    exact Nat.le_of_mul_le_mul_left hChain hPos
  refine ⟨hRtt, fun _ => hEnv, hBound, ?_⟩
  intro hGt hPhys
  have hLe := hBound hPhys
  omega

/-- **Universal Upper-Curve vs Lower-Curve Subtraction Theorem**:
    For any proven lower-curve energy `eLo`, positive per-op energy `0 < eMin`, and positive covert
    shadow operation count `0 < covertOps`: subtracting an inflated upper calibration curve
    `eHi = eLo + eMin * covertOps` from `meter = eHi` masks the entire `eMin * covertOps` covert
    budget (`eHi - eHi = 0`), whereas `PhysicalEnergyEnvelope` subtracting `lowerCurveProvenMilliJ = eLo`
    exposes `physicalResidualMilliJ env = eMin * covertOps` and refuses `hiddenOpsCap = 0`. -/
theorem upper_curve_subtraction_masks_covert_ops
    (eLo covertOps eMin rtt authBudget : Nat)
    (hMin : 0 < eMin) (hCovert : 0 < covertOps) :
    let eHi := eLo + eMin * covertOps
    let env : PhysicalEnergyEnvelope := {
      measuredRttMicros      := rtt
      authorityBudgetMicros  := authBudget
      meterEnergyMilliJ      := eHi
      lowerCurveProvenMilliJ := eLo
      idleEnergyMilliJ       := 0
      toleranceMilliJ        := 0
      minHiddenOpMilliJ      := eMin
      hiddenOpsCap           := 0
    }
    eHi - eHi = 0 ∧
    physicalResidualMilliJ env = eMin * covertOps ∧
    checkPhysicalEnergyEnvelope env = false := by
  dsimp only
  have hRes : (eLo + eMin * covertOps + 0) - eLo - 0 = eMin * covertOps := by omega
  have hPosProd : 0 < eMin * covertOps := Nat.mul_pos hMin hCovert
  refine ⟨Nat.sub_self _, hRes, ?_⟩
  unfold checkPhysicalEnergyEnvelope physicalResidualMilliJ
  dsimp only
  rw [hRes]
  apply decide_eq_false
  intro h
  have hBad := h.2.2.2
  omega

/-- Full cluster step audit context bundling `Sable`, `Ozaki`, `AriadneStep`, and `Reasons` policy. -/
structure ClusterStepContext where
  tensorBound   : IntTensorBound
  sampleWeights : List Int
  sampleActs    : List Int
  workerSlices  : List (List Int)
  step          : AriadneStep
  govProgram    : Obend.Reasons.Program
  targetConcl   : String

/-- Named refusal diagnostic for `ClusterGov` step auditing. -/
inductive ClusterGovRefusal where
  | sableModulusWrap (twoMaxAcc modulusP : Nat)
  | dimExceeded (actualLen maxDim : Nat)
  | weightBoundExceeded
  | activationBoundExceeded
  | flopsCapExceeded (flopsUsed flopsCap : Nat)
  | missingBatchCallTreeRoot
  | policyUnsupported (conclusion : String) (status : Obend.Reasons.Status)
  deriving DecidableEq, Repr

/-- Deterministic `ClusterGov` step auditor: checks `Sable` no-wrap envelope, vector norms,
    `flopsCap` ceiling, non-zero `batchCallTreeRoot` lineage, and `Obend.Reasons.wf` admission,
    returning the canonical `ozakiSliceSum` collective output on `.ok`. -/
def auditClusterStep (ctx : ClusterStepContext) :
    Except ClusterGovRefusal (List Int) :=
  let twoMax := 2 * ctx.tensorBound.dim * ctx.tensorBound.maxAbsWeight * ctx.tensorBound.maxAbsAct
  if !checkSableNoWrap ctx.tensorBound then
    .error (.sableModulusWrap twoMax ctx.tensorBound.modulusP)
  else if !decide (ctx.sampleWeights.length ≤ ctx.tensorBound.dim) then
    .error (.dimExceeded ctx.sampleWeights.length ctx.tensorBound.dim)
  else if !checkVecAbsBounded ctx.tensorBound.maxAbsWeight ctx.sampleWeights then
    .error .weightBoundExceeded
  else if !checkVecAbsBounded ctx.tensorBound.maxAbsAct ctx.sampleActs then
    .error .activationBoundExceeded
  else if !decide (ctx.step.flopsUsed ≤ ctx.step.flopsCap) then
    .error (.flopsCapExceeded ctx.step.flopsUsed ctx.step.flopsCap)
  else if ctx.step.batchCallTreeRoot == 0 then
    .error .missingBatchCallTreeRoot
  else
    let st := Obend.Reasons.statusIn (Obend.Reasons.wf ctx.govProgram) ctx.targetConcl
    if st == .supported then
      .ok (ozakiSliceSum ctx.workerSlices)
    else
      .error (.policyUnsupported ctx.targetConcl st)

/-- Boolean decision wrapper for `auditClusterStep`. -/
def verifyClusterStep (ctx : ClusterStepContext) : Bool :=
  (auditClusterStep ctx).isOk

/-- Extended physical + algebraic cluster step context pairing `ClusterStepContext` with
    `PhysicalEnergyEnvelope`. -/
structure PhysicalClusterStepContext where
  base     : ClusterStepContext
  physical : PhysicalEnergyEnvelope

/-- Named refusal diagnostic for `auditPhysicalClusterStep`. -/
inductive PhysicalClusterRefusal where
  | baseRefusal (err : ClusterGovRefusal)
  | zeroMinHiddenOpEnergy
  | energyBaselineUnderflow (meterMilliJ baselineMilliJ : Nat)
  | rttBudgetExceeded (measuredMicros authorityBudgetMicros : Nat)
  | energyResidualExceeded (residualMilliJ maxAllowedMilliJ : Nat)
  deriving DecidableEq, Repr

/-- Audit both algebraic `ClusterStepContext` invariants and physical RTT/energy conservation,
    returning the unboxed `Array Int` `ozakiSliceSumExec` collective result. -/
def auditPhysicalClusterStep (pctx : PhysicalClusterStepContext) :
    Except PhysicalClusterRefusal (Array Int) :=
  match auditClusterStep pctx.base with
  | .error e => .error (.baseRefusal e)
  | .ok _ =>
    let env := pctx.physical
    if !decide (0 < env.minHiddenOpMilliJ) then
      .error .zeroMinHiddenOpEnergy
    else if !decide (env.measuredRttMicros ≤ env.authorityBudgetMicros) then
      .error (.rttBudgetExceeded env.measuredRttMicros env.authorityBudgetMicros)
    else if !decide (env.lowerCurveProvenMilliJ + env.idleEnergyMilliJ ≤ env.meterEnergyMilliJ) then
      .error (.energyBaselineUnderflow env.meterEnergyMilliJ
        (env.lowerCurveProvenMilliJ + env.idleEnergyMilliJ))
    else
      let res := physicalResidualMilliJ env
      let cap := env.minHiddenOpMilliJ * env.hiddenOpsCap
      if !decide (res ≤ cap) then
        .error (.energyResidualExceeded res cap)
      else
        .ok (ozakiSliceSumExec (pctx.base.workerSlices.map List.toArray).toArray)


/-! ## §4. Executed hardware and challenged sealed-VRAM openings -/

/-- RDNA2 GFX1030 compute shader wavefront dispatch trace for collective/tensor reduction. -/
structure Rdna2WavefrontDispatch where
  shaderIsaWords  : Array UInt32
  waveSize        : Nat
  workgroupSlices : Array (Array Int)
  hwReducedOut    : Array Int
  statusTrap      : Bool
  deriving DecidableEq, Repr

/-- Load each worker's slice vector into its own VGPR, one slice per lane.
The accepted fragment is unsigned, exact 32-bit sums, at most 256 workers. -/
@[expose] def rdna2DispatchInput (d : Rdna2WavefrontDispatch) : Obend.Hardware.Gpu.Rdna2.WaveState :=
  { Obend.Hardware.Gpu.Rdna2.GWave.init {} 0 0 with
    vgpr := (((d.workgroupSlices.toList.take 256).flatMap fun (row : Array Int) =>
      (List.range 64).map fun lane =>
        if lane < d.waveSize then UInt32.ofNat (row[lane]?.getD 0).toNat
        else (0 : UInt32)) ++ List.replicate ((256 - d.workgroupSlices.size) * 64) (0 : UInt32)).toArray }


@[expose] def insertRdnaEncoding (entry : Obend.Hardware.Gpu.Rdna2.Encoding) :
    List Obend.Hardware.Gpu.Rdna2.Encoding → List Obend.Hardware.Gpu.Rdna2.Encoding
  | [] => [entry]
  | first :: rest => if entry.order ≤ first.order then entry :: first :: rest
    else first :: insertRdnaEncoding entry rest

@[expose] def orderedRdnaEncodings : List Obend.Hardware.Gpu.Rdna2.Encoding →
    List Obend.Hardware.Gpu.Rdna2.Encoding
  | [] => []
  | first :: rest => insertRdnaEncoding first (orderedRdnaEncodings rest)

open Obend.Hardware.Gpu.Rdna2 in
/-- Total decoder over AMD's generated encoding tables. A list search keeps its
logical body reducible in the kernel; entries use the same reverse insertion order as `instIndex`. -/
@[expose] def decodeRdnaSliceInst (words : List UInt32) : Option (Obend.Hardware.Gpu.Rdna2.Inst × Nat) :=
  match words with
  | [] => none
  | first :: _ =>
    let candidates := orderedRdnaEncodings encodings
    candidates.findSome? fun enc =>
      let count := enc.bitCount / 32
      if !encodingMatches first enc || count == 0 || words.length < count then none else
      let taken := words.take count
      let fields := fieldsOf enc taken
      match lookupField fields "OP" with
      | none => none
      | some opcode =>
        let entries := (instructions.flatMap fun inst =>
          inst.encodings.map fun ie => (inst, ie)).reverse
        match entries.find? (fun (_, ie) => ie.encoding == enc.name && ie.opcode == opcode &&
            match enc.conditions.find? (·.name == ie.condition) with
            | some condition => condition.expr.eval fields
            | none => false) with
        | some (inst, ie) => some (⟨inst, enc, ie, fields, taken⟩, count)
        | none => none

@[expose] def decodeRdnaSliceProgram : Nat → List UInt32 → Option (List (Option Obend.Hardware.Gpu.Rdna2.Inst))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, words@(_ :: _) => do
    let (inst, count) ← decodeRdnaSliceInst words
    let rest ← decodeRdnaSliceProgram fuel (words.drop count)
    pure (some inst :: (List.replicate (count - 1) none ++ rest))

/-- Decode the supplied ISA and execute it with a bounded instruction budget.
The result comes only from output VGPR 0; a failed decode, trap, or timeout refuses. -/
@[expose] def executeRdna2SliceReduction (d : Rdna2WavefrontDispatch) : Option (Array Int) :=
  match decodeRdnaSliceProgram d.shaderIsaWords.size d.shaderIsaWords.toList with
  | none => none
  | some program =>
    let final := Obend.Hardware.Gpu.Rdna2.run program.toArray (d.shaderIsaWords.size * 4 + 1)
      (rdna2DispatchInput d)
    if final.halted && !final.err.isSome then
      some (((List.range (ozakiSliceSumExec d.workgroupSlices).size).map
        (fun lane => Int.ofNat (Obend.Hardware.Gpu.Rdna2.readVgpr final 0 lane).toNat)).toArray)
    else none

/-- Admission compares actual decoded execution, the reported result, and exact Ozaki sums. -/
def checkRdna2DispatchEnvelope (d : Rdna2WavefrontDispatch) : Bool :=
  (d.waveSize == 32 || d.waveSize == 64) &&
  decide (0 < d.shaderIsaWords.size ∧ 0 < d.workgroupSlices.size ∧
    d.workgroupSlices.size ≤ 256) && !d.statusTrap &&
  d.workgroupSlices.all (fun row => decide (row.size ≤ d.waveSize) &&
    row.all (fun x => decide (0 ≤ x ∧ x < 4294967296))) &&
  (ozakiSliceSumExec d.workgroupSlices).all (fun x => decide (0 ≤ x ∧ x < 4294967296)) &&
  decide (executeRdna2SliceReduction d = some d.hwReducedOut ∧
    d.hwReducedOut = ozakiSliceSumExec d.workgroupSlices)

theorem rdna2Wavefront_simulates_ozaki_sound (d : Rdna2WavefrontDispatch)
    (h : checkRdna2DispatchEnvelope d = true) :
    executeRdna2SliceReduction d = some d.hwReducedOut ∧
    d.hwReducedOut.toList = ozakiSliceSum (d.workgroupSlices.toList.map Array.toList) := by
  simp only [checkRdna2DispatchEnvelope, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.2.1, ?_⟩
  rw [h.2.2, ozakiSliceSumExec_eq_ozakiSliceSum]

/-- Binary Merkle inclusion path, ordered from leaf to root. -/
structure VramPagePath where
  siblings : List (BitVec 256)
  deriving DecidableEq, Repr

def vramHash (H : Obend.Digest.HashBytes.Hash) (bytes : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (Obend.Digest.HashBytes.ofBE (H bytes))

def vramRootFromPath (H : Obend.Digest.HashBytes.Hash) (offset : Nat)
    (page : BitVec 256) (siblings : List (BitVec 256)) : BitVec 256 :=
  (siblings.foldl (fun (state : Nat × BitVec 256) sibling =>
    let pair := if state.1 % 2 = 0 then (state.2, sibling) else (sibling, state.2)
    (state.1 / 2, vramHash H (0x01 ::
      (Obend.Digest.HashBytes.be 32 pair.1.toNat ++ Obend.Digest.HashBytes.be 32 pair.2.toNat))))
    (offset, page)).2

/-- The verifier supplies the pinned root and nonce separately from this prover claim. -/
structure SealedVramOpeningClaim where
  sealedRoot256 : BitVec 256
  challengeSeed256 : BitVec 256
  totalPages : Nat
  sampledOffsets : Array Nat
  openedPageDigests : Array (BitVec 256)
  paths : Array VramPagePath
  treeDepth : Nat
  deriving DecidableEq, Repr

def deriveVramSeed (H : Obend.Digest.HashBytes.Hash) (root nonce : BitVec 256)
    (pages depth : Nat) : BitVec 256 :=
  vramHash H (0x02 :: (Obend.Digest.HashBytes.be 32 root.toNat ++
    Obend.Digest.HashBytes.be 32 nonce.toNat ++
    ZkStripe.frameBytes (toString pages).toUTF8.data.toList ++
    ZkStripe.frameBytes (toString depth).toUTF8.data.toList))

def deriveVramOffsets (H : Obend.Digest.HashBytes.Hash) (seed : BitVec 256)
    (pages count : Nat) : Array Nat :=
  (List.range count).toArray.map (fun i =>
    (vramHash H (0x03 :: (Obend.Digest.HashBytes.be 32 seed.toNat ++
      ZkStripe.frameBytes (toString i).toUTF8.data.toList))).toNat % pages)

def checkSealedVramClaimEnvelope (c : SealedVramOpeningClaim) : Bool :=
  decide (c.sealedRoot256 ≠ 0 ∧ 0 < c.totalPages ∧ c.totalPages ≤ 2^c.treeDepth ∧
    8 ≤ c.sampledOffsets.size ∧ c.sampledOffsets.size = c.openedPageDigests.size ∧
    c.paths.size = c.sampledOffsets.size) &&
  c.sampledOffsets.all (fun idx => decide (idx < c.totalPages))

def checkVramChallengeOpening (H : Obend.Digest.HashBytes.Hash)
    (pinnedRoot nonce : BitVec 256) (c : SealedVramOpeningClaim) : Bool :=
  checkSealedVramClaimEnvelope c &&
  decide (c.sealedRoot256 = pinnedRoot ∧
    c.challengeSeed256 = deriveVramSeed H pinnedRoot nonce c.totalPages c.treeDepth ∧
    c.sampledOffsets = deriveVramOffsets H c.challengeSeed256 c.totalPages c.sampledOffsets.size) &&
  (List.range c.sampledOffsets.size).all (fun i =>
    let offset := c.sampledOffsets[i]!
    let page := c.openedPageDigests[i]!
    let path := c.paths[i]?.getD ⟨[]⟩
    decide (path.siblings.length = c.treeDepth ∧
      vramRootFromPath H offset page path.siblings = pinnedRoot))

theorem sealedVramRandomOpening_sound (H : Obend.Digest.HashBytes.Hash)
    (root nonce : BitVec 256) (c : SealedVramOpeningClaim)
    (h : checkVramChallengeOpening H root nonce c = true) :
    root ≠ 0 ∧
    c.challengeSeed256 = deriveVramSeed H root nonce c.totalPages c.treeDepth ∧
    c.sampledOffsets = deriveVramOffsets H c.challengeSeed256 c.totalPages c.sampledOffsets.size ∧
    ∀ i ∈ List.range c.sampledOffsets.size,
      (c.paths[i]?.getD ⟨[]⟩).siblings.length = c.treeDepth ∧
      vramRootFromPath H c.sampledOffsets[i]! c.openedPageDigests[i]!
        (c.paths[i]?.getD ⟨[]⟩).siblings = root := by
  simp only [checkVramChallengeOpening, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  have he := h.1.1
  simp only [checkSealedVramClaimEnvelope, Bool.and_eq_true, decide_eq_true_eq] at he
  exact ⟨h.1.2.1 ▸ he.1.1, h.1.2.2.1, h.1.2.2.2, h.2⟩

/-- Two independent worker slices, added by V_ADD_NC_U32 v0, v0, v1. Its inhabitedness witness
(`rdna2Dispatch_inhabited`: real RDNA2 decode + reduction, needing kernel-heavy `rfl` decodes beyond the
tier-1 heartbeat baseline) is the tier-2 fixture in `Obend/Teeth/Hardware/Rdna2Runs.lean`. -/
def rdna2AddDispatch : Rdna2WavefrontDispatch :=
  ⟨#[0x4a000300, 0xbf810000], 32, #[#[3, 5], #[4, 6]], #[7, 11], false⟩

/-- An injective byte-string test hash with a mixed 32-byte suffix. The VRAM
projection reads that suffix, so changing either page or sibling changes this witness. -/
def vramFixtureHash (xs : List UInt8) : List UInt8 := xs ++ ZkStripe.fastMerkleHash xs

private theorem vramFixtureHash_injective (a b : List UInt8)
    (h : vramFixtureHash a = vramFixtureHash b) : a = b := by
  have hl := congrArg List.length h
  have size (xs : List UInt8) : (ZkStripe.fastMerkleHash xs).length = 32 := by
    simp [ZkStripe.fastMerkleHash, ZkStripe.mixWord]
  simp only [vramFixtureHash, List.length_append, size] at hl
  exact (List.append_inj h (by omega)).1

def vramFixtureRoot : BitVec 256 := vramRootFromPath vramFixtureHash 0 1 [2]

def vramOpeningFixture : SealedVramOpeningClaim :=
  ⟨vramFixtureRoot, deriveVramSeed vramFixtureHash vramFixtureRoot 42 1 1, 1,
    Array.replicate 8 0, Array.replicate 8 1, Array.replicate 8 ⟨[2]⟩, 1⟩

theorem vramChallengeOpening_inhabited : ∃ H root nonce c,
    (∀ a b, H a = H b → a = b) ∧ 1 ≤ c.treeDepth ∧
    checkVramChallengeOpening H root nonce c = true := by
  refine ⟨vramFixtureHash, vramFixtureRoot, 42, vramOpeningFixture,
    vramFixtureHash_injective, by decide, ?_⟩
  simp only [checkVramChallengeOpening, checkSealedVramClaimEnvelope,
    Bool.and_eq_true, decide_eq_true_eq, ← Array.all_toList]
  refine ⟨⟨⟨?_, ?_⟩, ⟨rfl, rfl, ?_⟩⟩, ?_⟩
  · decide +kernel
  · decide +kernel
  · apply Array.toList_inj.mp
    change (Array.replicate 8 0).toList =
      (deriveVramOffsets vramFixtureHash _ 1 8).toList
    simp only [deriveVramOffsets, Array.toList_map, Nat.mod_one]
    decide +kernel
  · decide +kernel

/-- **Organ O6 Unconditional Apex Step Theorem (`apex_verifiable_ai_cluster_step`)**:
    With **zero open obligations** and **zero `Classical.choice`**, whenever
    `auditClusterStep ctx = .ok reducedSlices`, Lean's kernel establishes:
    1. Exact `Sable` $F_O$ modular dot-product round-trip (`decodeSignedModP ... = intDot ...`)
       matching `intDotExec`,
    2. Permutation-invariant bit-exact `Ozaki` collective output (`ozakiSliceSum workers' = reducedSlices`),
    3. Enforced `flopsUsed ≤ flopsCap` compute cap and non-zero `batchCallTreeRoot` lineage, and
    4. Supported `Obend.Reasons.wf` governance judgment. -/
theorem apex_verifiable_ai_cluster_step
    (ctx : ClusterStepContext) (reducedSlices : List Int)
    (workers' : List (List Int))
    (hAudit : auditClusterStep ctx = .ok reducedSlices)
    (hPerm : List.Perm ctx.workerSlices workers') :
    2 * (intDot ctx.sampleWeights ctx.sampleActs).natAbs < ctx.tensorBound.modulusP ∧
      decodeSignedModP ctx.tensorBound.modulusP
        (embedModP ctx.tensorBound.modulusP (intDot ctx.sampleWeights ctx.sampleActs)) =
        intDot ctx.sampleWeights ctx.sampleActs ∧
      ozakiSliceSum workers' = reducedSlices ∧
      ctx.step.flopsUsed ≤ ctx.step.flopsCap ∧
      ctx.step.batchCallTreeRoot ≠ 0 ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf ctx.govProgram) ctx.targetConcl = .supported := by
  unfold auditClusterStep at hAudit
  cases hSable : checkSableNoWrap ctx.tensorBound
  · rw [hSable] at hAudit; cases hAudit
  · rw [hSable] at hAudit
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
    cases hDimDec : decide (ctx.sampleWeights.length ≤ ctx.tensorBound.dim)
    · rw [hDimDec] at hAudit; cases hAudit
    · rw [hDimDec] at hAudit
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
      have hDim : ctx.sampleWeights.length ≤ ctx.tensorBound.dim := of_decide_eq_true hDimDec
      cases hW : checkVecAbsBounded ctx.tensorBound.maxAbsWeight ctx.sampleWeights
      · rw [hW] at hAudit; cases hAudit
      · rw [hW] at hAudit
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
        cases hX : checkVecAbsBounded ctx.tensorBound.maxAbsAct ctx.sampleActs
        · rw [hX] at hAudit; cases hAudit
        · rw [hX] at hAudit
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
          cases hFlopsDec : decide (ctx.step.flopsUsed ≤ ctx.step.flopsCap)
          · rw [hFlopsDec] at hAudit; cases hAudit
          · rw [hFlopsDec] at hAudit
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAudit
            have hFlops : ctx.step.flopsUsed ≤ ctx.step.flopsCap := of_decide_eq_true hFlopsDec
            cases hBatchZero : (ctx.step.batchCallTreeRoot == 0)
            · rw [hBatchZero] at hAudit
              simp only [Bool.false_eq_true, ↓reduceIte] at hAudit
              have hBatchNe : ctx.step.batchCallTreeRoot ≠ 0 := by
                intro hEq0
                have hTrue : (ctx.step.batchCallTreeRoot == 0) = true := beq_iff_eq.mpr hEq0
                exact Bool.false_ne_true (hBatchZero.symm.trans hTrue)
              cases hSt : (Obend.Reasons.statusIn (Obend.Reasons.wf ctx.govProgram)
                  ctx.targetConcl == .supported)
              · rw [hSt] at hAudit; cases hAudit
              · rw [hSt] at hAudit
                simp only [↓reduceIte] at hAudit
                injection hAudit with hOut
                have hExact := sable_dot_exact_no_wrap ctx.tensorBound
                  ctx.sampleWeights ctx.sampleActs hSable hDim
                  (checkVecAbsBounded_sound hW)
                  (checkVecAbsBounded_sound hX)
                have hPermEq : ozakiSliceSum workers' = reducedSlices := by
                  rw [← ozakiSliceSum_perm hPerm, hOut]
                exact ⟨hExact.1, hExact.2, hPermEq, hFlops, hBatchNe, beq_iff_eq.mp hSt⟩
            · rw [hBatchZero] at hAudit; cases hAudit


/-! ## §5. Concrete Cluster Governance Fixtures & Silver Smoke Runner -/

/-- Valid KoalaBear (`p = 2130706433`) 4-dim tensor bound (`2 * 4 * 1024 * 1024 = 8,388,608 < p`). -/
def defaultKoalaBound : IntTensorBound where
  dim          := 4
  maxAbsWeight := 1024
  maxAbsAct    := 1024
  modulusP     := koalaBearPrime

/-- Valid `ClusterStepContext` within `Sable` no-wrap bounds and `flopsCap = 10_000_000`. -/
def validClusterStepCtx : ClusterStepContext where
  tensorBound   := {
    dim          := 4
    maxAbsWeight := 1024
    maxAbsAct    := 1024
    modulusP     := 2130706433
  }
  sampleWeights := [512, -256, 128, -64]
  sampleActs    := [300, 400, -500, 100]
  workerSlices  := [[100, -20, 3], [50, 40, -1], [-30, 10, 5]]
  step := {
    prevWeightsRoot   := 0x11112222
    batchCallTreeRoot := 0x9999AAAA
    nextWeightsRoot   := 0x33334444
    flopsUsed         := 7500000
    flopsCap          := 10000000
  }
  govProgram := {
    facts := ["cluster_quorum_signed", "corrigibility_watchdog_armed"]
    rules := [{
      name  := "admit_training_step"
      concl := "step_admitted"
      pos   := ["cluster_quorum_signed", "corrigibility_watchdog_armed"]
      neg   := ["kill_switch_tripped"]
    }]
  }
  targetConcl := "step_admitted"

/-- Default authority-pinned `PhysicalEnergyEnvelope` for rack-local cluster verification:
    `measuredRttMicros = 1200 ≤ 3000 = authorityBudgetMicros`, residual energy
    `(450 + 10) - 400 - 40 = 20 ≤ 5 * 4 = 20` mJ (`hiddenOpsCap = 4`). -/
def defaultPhysicalEnvelope : PhysicalEnergyEnvelope where
  measuredRttMicros         := 1200
  authorityBudgetMicros     := 3000
  proverClaimedBudgetMicros := 999999
  meterEnergyMilliJ         := 450
  lowerCurveProvenMilliJ    := 400
  idleEnergyMilliJ          := 40
  toleranceMilliJ           := 10
  minHiddenOpMilliJ         := 5
  hiddenOpsCap              := 4

/-- Planted bad context #1: `Sable` modulus wraparound (`2 * 4 * 50000 * 10000 = 4,000,000,000 ≥ p`). -/
def wrapOverflowClusterCtx : ClusterStepContext :=
  { validClusterStepCtx with
    tensorBound := {
      dim          := 4
      maxAbsWeight := 50000
      maxAbsAct    := 10000
      modulusP     := koalaBearPrime
    } }

/-- Planted bad context #2: `flopsUsed` (`12,500,000`) breaches `flopsCap` (`10,000,000`). -/
def flopsBreachClusterCtx : ClusterStepContext :=
  { validClusterStepCtx with
    step := { validClusterStepCtx.step with flopsUsed := 12500000 } }

/-- Executable Silver end-to-end smoke runner for Organ O6 (`ClusterGov`). -/
def silverClusterGovSmoke : Bool :=
  let validOk :=
    match auditClusterStep validClusterStepCtx with
    | .ok slices => slices == [120, 30, 7]
    | .error _ => false
  let execDotOk :=
    intDotExec #[512, -256, 128, -64] #[300, 400, -500, 100] == -19200
  let execOzakiOk :=
    ozakiSliceSumExec #[#[100, -20, 3], #[50, 40, -1], #[-30, 10, 5]] == #[120, 30, 7]
  let physOk := checkPhysicalEnergyEnvelope defaultPhysicalEnvelope
  let physRelayRefused :=
    !checkPhysicalEnergyEnvelope { defaultPhysicalEnvelope with measuredRttMicros := 52000 }
  let physEnergyRefused :=
    !checkPhysicalEnergyEnvelope { defaultPhysicalEnvelope with meterEnergyMilliJ := 500 }
  let treeLeft : AllReduceTree :=
    .node (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1])) (.leaf [-30, 10, 5])
  let treeRight : AllReduceTree :=
    .node (.leaf [-30, 10, 5]) (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1]))
  let hyperLawOk :=
    checkHyperLaw2NonInterference clusterPublicView
      [(⟨[0, 0, 0], 1⟩, ⟨[0, 0, 0], 2⟩),
       (runScheduledAllReduce treeLeft 1, runScheduledAllReduce treeRight 2)]
  let wrapRefused :=
    match auditClusterStep wrapOverflowClusterCtx with
    | .error e => e == .sableModulusWrap 4000000000 koalaBearPrime
    | .ok _ => false
  let flopsRefused :=
    match auditClusterStep flopsBreachClusterCtx with
    | .error e => e == .flopsCapExceeded 12500000 10000000
    | .ok _ => false
  validOk && execDotOk && execOzakiOk && physOk && physRelayRefused && physEnergyRefused &&
    hyperLawOk && wrapRefused && flopsRefused

example : checkVecAbsBounded 1024 [512, -256, 128, -64] = true := rfl

example : silverClusterGovSmoke = true := by
  decide

end Obend.Trailblaze.ClusterGov


namespace Obend.Trailblaze.CathedralApex

open Obend.Trailblaze.ZkStripe (consumeSessionNodes consumeSessionNodes_sound defaultZkStripePolicy fixtureSessionVerifiers)

open Obend.Digest.HashBytes (Hash ofBE be CollisionAmong)
open Obend.Run.HyperLaw (HyperLaw2NonInterference checkHyperLaw2NonInterference
  checkHyperLaw2NonInterference_sound)
open Obend.Trailblaze.ZkStripe (HttpsSessionNode ZkStripePolicy ZkStripeRefusal
  HopAudited allSessionNodes treePreimages checkCanonicalSessionTree callTreeDigestBytes callTreeDigest
  callTreeDigestBytes_binding auditZkStripeCallTree verifyZkStripeCallTree
  auditZkStripeCallTree_ok_imp_verify auditZkStripeCallTree_all_hops_sound)
open Obend.Trailblaze.ClusterGov (AriadneStep PhysicalEnergyEnvelope
  checkPhysicalEnergyEnvelope energy_conservation_bounds_hidden_ops
  ClusterStepContext ClusterGovRefusal ClusterReduceWorld AllReduceTree
  clusterPublicView runScheduledAllReduce auditClusterStep apex_verifiable_ai_cluster_step
  intDot intDotExec intDotExec_eq_intDot ozakiSliceSumExec ozakiSliceSumExec_eq_ozakiSliceSum
  embedModP decodeSignedModP)

set_option autoImplicit false

/-! ## §1. 32-Byte (`BitVec 256`) In-Rack FPGA Boolean Verifier Receipt -/

/-- Hard ceiling (32 bytes = 256 bits) on verifier receipt egress across the rack boundary,
    closing the 18.8 MB raw-SNARK proof-egress weight-exfiltration channel. -/
def maxRackReceiptBytes : Nat := 32

/-- Deterministic 256-bit (`BitVec 256`) big-endian reading of the first 32 bytes of `bs`. -/
def digestBytesToBitVec256 (bs : List UInt8) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (bs.take 32))

/-- Tail-recursive `O(w)` big-endian byte encoder (`termination_by structural`) avoiding nested
    `List.append` / `WellFounded.fix` stack frames during 256-bit kernel WHNF reduction. -/
def beAcc : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | w + 1, n, acc => beAcc w (n / 256) (UInt8.ofNat (n % 256) :: acc)
termination_by structural w => w

/-- **`Spec ↔ Exec` Big-Endian Framing Equivalence**: `beAcc w n acc` equals `be w n ++ acc`. -/
theorem beAcc_eq_be_append (w n : Nat) (acc : List UInt8) :
    beAcc w n acc = be w n ++ acc := by
  induction w generalizing n acc with
  | zero => rfl
  | succ w ih =>
    dsimp only [beAcc, be]
    rw [ih (n / 256) (UInt8.ofNat (n % 256) :: acc), List.append_assoc]
    rfl

/-- Exact 32-byte big-endian wire encoding of a verifier receipt. -/
def encodeReceipt256 (r : BitVec 256) : ByteArray :=
  ⟨(beAcc 32 r.toNat []).toArray⟩

@[simp] theorem encodeReceipt256_size (r : BitVec 256) :
    (encodeReceipt256 r).data.size = 32 := by
  simp [encodeReceipt256, beAcc_eq_be_append, Obend.Digest.HashBytes.length_be]

/-- The wire encoding preserves every bit of the receipt. -/
theorem encodeReceipt256_inj {a b : BitVec 256}
    (h : encodeReceipt256 a = encodeReceipt256 b) : a = b := by
  have hBytes := congrArg (fun bs : ByteArray => bs.data.toList) h
  simp only [encodeReceipt256, List.toList_toArray, beAcc_eq_be_append,
    List.append_nil] at hBytes
  have hPow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  exact BitVec.eq_of_toNat_eq
    (Obend.Digest.HashBytes.be_injective (hPow ▸ a.isLt) (hPow ▸ b.isLt) hBytes)

/-- Canonical 256-bit (`BitVec 256`) in-rack FPGA boolean verifier commitment over public rack/step
    anchors and single verdict bit (`0x01` = pass, `0x00` = fail); private witnesses and multi-MB
    SNARK proof transcripts never enter the preimage. -/
def computeFpgaVerifierReceipt256 (H : Hash) (rackId epoch treeRoot : Nat)
    (step : AriadneStep) (verdict : Bool) : BitVec 256 :=
  let vByte : List UInt8 := [if verdict then (0x01 : UInt8) else (0x00 : UInt8)]
  let preimage : List UInt8 :=
    (0xF6 : UInt8) ::
    beAcc 8 rackId
      (beAcc 8 epoch
        (beAcc 32 treeRoot
          (beAcc 32 step.prevWeightsRoot
            (beAcc 32 step.nextWeightsRoot
              (beAcc 8 step.flopsUsed
                (beAcc 8 step.flopsCap vByte))))))
  digestBytesToBitVec256 (H preimage)

/-- **Two-State Proof-Egress Closure (`fpgaVerifierReceipt256_at_most_two_states`)**:
    For fixed public `(H, rackId, epoch, treeRoot, step)`, the in-rack FPGA receipt `BitVec 256`
    assumes at most two values (`verdict = false` or `verdict = true`), carrying zero witness
    or prover randomness entropy across the rack boundary. -/
theorem fpgaVerifierReceipt256_at_most_two_states
    (H : Hash) (rackId epoch treeRoot : Nat) (step : AriadneStep) (verdict : Bool) :
    computeFpgaVerifierReceipt256 H rackId epoch treeRoot step verdict =
      computeFpgaVerifierReceipt256 H rackId epoch treeRoot step false ∨
    computeFpgaVerifierReceipt256 H rackId epoch treeRoot step verdict =
      computeFpgaVerifierReceipt256 H rackId epoch treeRoot step true := by
  cases verdict
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- In-rack FPGA boolean verifier receipt envelope (`BitVec 256` digest + `≤ 32`-byte wire frame). -/
structure InRackFpgaReceipt where
  rackId              : Nat
  epoch               : Nat
  verdict             : Bool
  verifierReceipt256  : BitVec 256
  receiptPayloadBytes : ByteArray
  deriving DecidableEq

/-- Verify that an `InRackFpgaReceipt` carries `verdict = true`, satisfies the 32-byte egress
    ceiling, matches `computeFpgaVerifierReceipt256`, and carries exactly its canonical bytes. -/
def checkInRackFpgaReceipt (H : Hash) (treeRoot : Nat) (step : AriadneStep)
    (rcpt : InRackFpgaReceipt) : Bool :=
  rcpt.verdict &&
  decide (rcpt.receiptPayloadBytes.data.size ≤ maxRackReceiptBytes) &&
  decide (rcpt.verifierReceipt256 =
    computeFpgaVerifierReceipt256 H rcpt.rackId rcpt.epoch treeRoot step true) &&
  decide (rcpt.receiptPayloadBytes = encodeReceipt256 rcpt.verifierReceipt256)


/-- Every computed receipt has an accepted canonical wire representation. -/
theorem checkInRackFpgaReceipt_canonical_inhabited
    (H : Hash) (rackId epoch treeRoot : Nat) (step : AriadneStep) :
    let digest := computeFpgaVerifierReceipt256 H rackId epoch treeRoot step true
    checkInRackFpgaReceipt H treeRoot step
      ⟨rackId, epoch, true, digest, encodeReceipt256 digest⟩ = true := by
  simp [checkInRackFpgaReceipt, maxRackReceiptBytes, encodeReceipt256,
    beAcc_eq_be_append, Obend.Digest.HashBytes.length_be]

/-- With public rack and epoch fixed, admission determines the entire receipt,
including every payload byte. No prover-selected wire payload remains. -/
theorem checkInRackFpgaReceipt_zero_covert_channel
    (H : Hash) (treeRoot : Nat) (step : AriadneStep)
    (r₁ r₂ : InRackFpgaReceipt)
    (hRack : r₁.rackId = r₂.rackId) (hEpoch : r₁.epoch = r₂.epoch)
    (h₁ : checkInRackFpgaReceipt H treeRoot step r₁ = true)
    (h₂ : checkInRackFpgaReceipt H treeRoot step r₂ = true) : r₁ = r₂ := by
  simp only [checkInRackFpgaReceipt, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
  rcases h₁ with ⟨⟨⟨hv₁, _⟩, hd₁⟩, hp₁⟩
  rcases h₂ with ⟨⟨⟨hv₂, _⟩, hd₂⟩, hp₂⟩
  have hDigest : r₁.verifierReceipt256 = r₂.verifierReceipt256 := by
    rw [hd₁, hd₂, hRack, hEpoch]
  have hPayload : r₁.receiptPayloadBytes = r₂.receiptPayloadBytes := by
    rw [hp₁, hp₂, hDigest]
  have hVerdict : r₁.verdict = r₂.verdict := hv₁.trans hv₂.symm
  cases r₁
  cases r₂
  simp only at hRack hEpoch hVerdict hDigest hPayload
  cases hRack
  cases hEpoch
  cases hVerdict
  cases hDigest
  cases hPayload
  rfl


/-! ## §2. Whole-System `CathedralGovernanceTurn` Carrier & Joint `Reasons` Program -/

/-- Unified governance turn wiring a domain-bound `ZkStripe` multi-hop `CallTree` into a verifiable
    `ClusterGov` AI step, `PhysicalEnergyEnvelope` RTT/energy conservation gate, 32-byte in-rack
    FPGA boolean verifier receipt, paired 2-trace `HyperLaw` audit, and `Obend.Reasons` policy. -/
structure CathedralGovernanceTurn where
  hashFn                   : Hash
  zkPolicy                 : ZkStripePolicy
  batchCallTree            : HttpsSessionNode
  committedTreeDigestBytes : List UInt8
  clusterCtx               : ClusterStepContext
  physicalEnvelope         : PhysicalEnergyEnvelope
  fpgaReceipt              : InRackFpgaReceipt
  scheduleTracePair        : List (ClusterReduceWorld × ClusterReduceWorld)
  cathedralRules           : List Obend.Reasons.Rule
  cathedralTarget          : String

/-- Named refusal diagnostic for whole-cathedral `ZkStripe → ClusterGov` turn admission. -/
inductive CathedralTurnRefusal where
  | zkStripeRefused (err : ZkStripeRefusal)
  | nonCanonicalCallTree
  | treeDigestBytesMismatch (actual expected : List UInt8)
  | batchRootWeldMismatch (treeDigest stepBatchRoot : Nat)
  | clusterStepRefused (err : ClusterGovRefusal)
  | physicalEnvelopeFailed
  | fpgaReceiptInvalid (payloadBytes : Nat)
  | covertChannelDetected
  | cathedralPolicyUnsupported (target : String) (status : Obend.Reasons.Status)
  deriving DecidableEq, Repr

/-- Modularly compose certified organ conclusions and cross-organ weld/physical/FPGA attestations
    into the top-level cathedral `Obend.Reasons.Program`. -/
def buildCathedralProgram (turn : CathedralGovernanceTurn) : Obend.Reasons.Program where
  facts := [
    turn.zkPolicy.targetConclusion,
    turn.clusterCtx.targetConcl,
    "zkstripe_root_bound",
    "ozaki_hyperlaw_verified",
    "physical_energy_envelope_verified",
    "fpga_32byte_receipt_verified"
  ]
  rules := turn.cathedralRules

/-- Audit an end-to-end `CathedralGovernanceTurn`, returning
    `(verifierReceipt256, reducedSlicesExec)` when every organ, physical envelope, 32-byte FPGA
    receipt, and cross-organ digest weld succeeds, or a named `CathedralTurnRefusal`. -/
def auditCathedralTurn (turn : CathedralGovernanceTurn) :
    Except CathedralTurnRefusal (BitVec 256 × Array Int) :=
  match auditZkStripeCallTree turn.zkPolicy turn.batchCallTree with
  | .error zErr => .error (.zkStripeRefused zErr)
  | .ok () =>
    if !checkCanonicalSessionTree turn.hashFn turn.batchCallTree then
      .error .nonCanonicalCallTree
    else
      let digestBytes := callTreeDigestBytes turn.hashFn turn.batchCallTree
      if !decide (digestBytes = turn.committedTreeDigestBytes) then
        .error (.treeDigestBytesMismatch digestBytes turn.committedTreeDigestBytes)
      else
        let treeDigest := callTreeDigest turn.hashFn turn.batchCallTree
        if !decide (treeDigest = turn.clusterCtx.step.batchCallTreeRoot) then
          .error (.batchRootWeldMismatch treeDigest turn.clusterCtx.step.batchCallTreeRoot)
        else
          match auditClusterStep turn.clusterCtx with
          | .error cErr => .error (.clusterStepRefused cErr)
          | .ok _ =>
            if !checkPhysicalEnergyEnvelope turn.physicalEnvelope then
              .error .physicalEnvelopeFailed
            else if !checkInRackFpgaReceipt turn.hashFn treeDigest
                turn.clusterCtx.step turn.fpgaReceipt then
              .error (.fpgaReceiptInvalid turn.fpgaReceipt.receiptPayloadBytes.data.size)
            else if !checkHyperLaw2NonInterference clusterPublicView turn.scheduleTracePair then
              .error .covertChannelDetected
            else
              let st := Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
                          turn.cathedralTarget
              if st == .supported then
                let execWorkers := (turn.clusterCtx.workerSlices.map List.toArray).toArray
                .ok (turn.fpgaReceipt.verifierReceipt256, ozakiSliceSumExec execWorkers)
              else
                .error (.cathedralPolicyUnsupported turn.cathedralTarget st)

/-- Total boolean decision gate for `CathedralGovernanceTurn`. -/
def checkCathedralTurn (turn : CathedralGovernanceTurn) : Bool :=
  (auditCathedralTurn turn).isOk


/-! ## §3. Unconditional Whole-System Composition Theorem (`apex_cathedral_zkstripe_to_clustergov_sound`) -/

/-- **Unconditional Cathedral End-to-End Composition Soundness (`apex_cathedral_zkstripe_to_clustergov_sound`)**:
    With **zero Stage-A hypotheses** and no choice-based computational extraction, whenever
    `checkCathedralTurn turn = true`, Lean's kernel simultaneously certifies:
    1. **Full Multi-Hop `ZkStripe` Audit**: `verifyZkStripeCallTree` passes and **every hop**
       `hop ∈ allSessionNodes turn.batchCallTree` satisfies `HopAudited` (trusted notary, canonical
       bounds, `PredRE` confinement, and string-aware `ByteArray` / `List` balanced VPA framing),
    2. **Unconditional Domain-Bound Tree Commitment Binding**: `callTreeDigestBytes` matches
       `turn.committedTreeDigestBytes`, `callTreeDigest` welds to `AriadneStep.batchCallTreeRoot`,
       and any canonical `otherTree` with the same `committedTreeDigestBytes` satisfies
       `turn.batchCallTree = otherTree ∨ Collision turn.hashFn`,
    3. **Overflow-Free `Sable` $F_O$ `Exec`/`Spec` Dot Product**: `2 * |⟨w, x⟩| < p` and exact
       centered modular round-trip on `intDotExec`,
    4. **`Ozaki` `HyperLaw2` Non-Interference**: observational schedule covert-channel closure,
    5. **Authority-Pinned RTT & Lower-Curve Shadow-FLOP Bound**: `flopsUsed ≤ flopsCap`,
       `measuredRttMicros ≤ authorityBudgetMicros`, and metered energy conservation bounds any
       unproved shadow FLOPs `hiddenOps ≤ hiddenOpsCap`,
    6. **32-Byte (`BitVec 256`) In-Rack FPGA Verifier Receipt**: `receiptPayloadBytes ≤ 32` and
       exact deterministic `computeFpgaVerifierReceipt256` binding, and
    7. **Unified `Obend.Reasons.wf` Governance Support** for `turn.cathedralTarget`. -/
theorem apex_cathedral_zkstripe_to_clustergov_sound
    (turn : CathedralGovernanceTurn)
    (otherTree : HttpsSessionNode)
    (hTurn : checkCathedralTurn turn = true)
    (hOtherCan : checkCanonicalSessionTree turn.hashFn otherTree = true)
    (hOtherBytes : callTreeDigestBytes turn.hashFn otherTree = turn.committedTreeDigestBytes) :
    verifyZkStripeCallTree turn.zkPolicy turn.batchCallTree = true ∧
      (∀ hop ∈ allSessionNodes turn.batchCallTree, HopAudited turn.zkPolicy hop) ∧
      callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes ∧
      callTreeDigest turn.hashFn turn.batchCallTree = turn.clusterCtx.step.batchCallTreeRoot ∧
      (turn.batchCallTree = otherTree ∨ CollisionAmong turn.hashFn
        (fun x => x ∈ treePreimages turn.hashFn turn.batchCallTree ++
          treePreimages turn.hashFn otherTree)) ∧
      2 * (intDot turn.clusterCtx.sampleWeights turn.clusterCtx.sampleActs).natAbs <
        turn.clusterCtx.tensorBound.modulusP ∧
      decodeSignedModP turn.clusterCtx.tensorBound.modulusP
        (embedModP turn.clusterCtx.tensorBound.modulusP
          (intDotExec turn.clusterCtx.sampleWeights.toArray turn.clusterCtx.sampleActs.toArray)) =
        intDot turn.clusterCtx.sampleWeights turn.clusterCtx.sampleActs ∧
      HyperLaw2NonInterference clusterPublicView turn.scheduleTracePair ∧
      turn.clusterCtx.step.flopsUsed ≤ turn.clusterCtx.step.flopsCap ∧
      turn.physicalEnvelope.measuredRttMicros ≤ turn.physicalEnvelope.authorityBudgetMicros ∧
      (∀ hiddenOps : Nat,
        turn.physicalEnvelope.minHiddenOpMilliJ * hiddenOps ≤
          (turn.physicalEnvelope.meterEnergyMilliJ + turn.physicalEnvelope.toleranceMilliJ) -
            turn.physicalEnvelope.lowerCurveProvenMilliJ -
            turn.physicalEnvelope.idleEnergyMilliJ →
        hiddenOps ≤ turn.physicalEnvelope.hiddenOpsCap) ∧
      turn.fpgaReceipt.receiptPayloadBytes.data.size ≤ maxRackReceiptBytes ∧
      turn.fpgaReceipt.verifierReceipt256 =
        computeFpgaVerifierReceipt256 turn.hashFn turn.fpgaReceipt.rackId turn.fpgaReceipt.epoch
          (callTreeDigest turn.hashFn turn.batchCallTree) turn.clusterCtx.step true ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
        turn.cathedralTarget = .supported := by
  unfold checkCathedralTurn auditCathedralTurn at hTurn
  cases hZk : auditZkStripeCallTree turn.zkPolicy turn.batchCallTree with
  | error e => rw [hZk] at hTurn; cases hTurn
  | ok u =>
    rw [hZk] at hTurn
    dsimp only at hTurn
    have hVerifyZk := auditZkStripeCallTree_ok_imp_verify hZk
    have hAllHops := (auditZkStripeCallTree_all_hops_sound hZk).1
    cases hCan : checkCanonicalSessionTree turn.hashFn turn.batchCallTree
    · rw [hCan] at hTurn; cases hTurn
    · rw [hCan] at hTurn
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
      cases hBytesDec : decide
          (callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes)
      · rw [hBytesDec] at hTurn; cases hTurn
      · rw [hBytesDec] at hTurn
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
        have hBytesEq :
            callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes :=
          of_decide_eq_true hBytesDec
        have hBind :
            turn.batchCallTree = otherTree ∨ CollisionAmong turn.hashFn
              (fun x => x ∈ treePreimages turn.hashFn turn.batchCallTree ++
                treePreimages turn.hashFn otherTree) :=
          callTreeDigestBytes_binding turn.hashFn turn.batchCallTree otherTree
            hCan hOtherCan (hBytesEq.trans hOtherBytes.symm)
        cases hWeldDec : decide
            (callTreeDigest turn.hashFn turn.batchCallTree =
              turn.clusterCtx.step.batchCallTreeRoot)
        · rw [hWeldDec] at hTurn; cases hTurn
        · rw [hWeldDec] at hTurn
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
          have hWeldEq :
              callTreeDigest turn.hashFn turn.batchCallTree =
                turn.clusterCtx.step.batchCallTreeRoot :=
            of_decide_eq_true hWeldDec
          cases hCluster : auditClusterStep turn.clusterCtx with
          | error cErr => rw [hCluster] at hTurn; cases hTurn
          | ok reducedSlices =>
            rw [hCluster] at hTurn
            dsimp only at hTurn
            have hStepProps :=
              apex_verifiable_ai_cluster_step turn.clusterCtx reducedSlices
                turn.clusterCtx.workerSlices hCluster (List.Perm.refl _)
            have hDotExecEq :
                intDotExec turn.clusterCtx.sampleWeights.toArray
                  turn.clusterCtx.sampleActs.toArray =
                  intDot turn.clusterCtx.sampleWeights turn.clusterCtx.sampleActs := by
              simpa using intDotExec_eq_intDot
                turn.clusterCtx.sampleWeights.toArray
                turn.clusterCtx.sampleActs.toArray
            cases hPhys : checkPhysicalEnergyEnvelope turn.physicalEnvelope
            · rw [hPhys] at hTurn; cases hTurn
            · rw [hPhys] at hTurn
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
              have hRtt :
                  turn.physicalEnvelope.measuredRttMicros ≤
                    turn.physicalEnvelope.authorityBudgetMicros :=
                (energy_conservation_bounds_hidden_ops turn.physicalEnvelope 0 hPhys).1
              have hEnergy :
                  ∀ hiddenOps : Nat,
                    turn.physicalEnvelope.minHiddenOpMilliJ * hiddenOps ≤
                      (turn.physicalEnvelope.meterEnergyMilliJ +
                        turn.physicalEnvelope.toleranceMilliJ) -
                        turn.physicalEnvelope.lowerCurveProvenMilliJ -
                        turn.physicalEnvelope.idleEnergyMilliJ →
                    hiddenOps ≤ turn.physicalEnvelope.hiddenOpsCap :=
                fun hiddenOps =>
                  (energy_conservation_bounds_hidden_ops turn.physicalEnvelope hiddenOps hPhys).2.2.1
              cases hFpga : checkInRackFpgaReceipt turn.hashFn
                  (callTreeDigest turn.hashFn turn.batchCallTree)
                  turn.clusterCtx.step turn.fpgaReceipt
              · rw [hFpga] at hTurn; cases hTurn
              · rw [hFpga] at hTurn
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
                have hFpgaProps := hFpga
                simp only [checkInRackFpgaReceipt, Bool.and_eq_true, decide_eq_true_eq]
                  at hFpgaProps
                rcases hFpgaProps with ⟨⟨⟨_, hPayloadLe⟩, hRcptEq⟩, _hCanonicalPayload⟩
                cases hHL : checkHyperLaw2NonInterference clusterPublicView turn.scheduleTracePair
                · rw [hHL] at hTurn; cases hTurn
                · rw [hHL] at hTurn
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTurn
                  cases hCatSt : (Obend.Reasons.statusIn
                      (Obend.Reasons.wf (buildCathedralProgram turn))
                      turn.cathedralTarget == .supported)
                  · rw [hCatSt] at hTurn; cases hTurn
                  · exact ⟨hVerifyZk, hAllHops, hBytesEq, hWeldEq, hBind,
                      hStepProps.1, hDotExecEq.symm ▸ hStepProps.2.1,
                      checkHyperLaw2NonInterference_sound hHL,
                      hStepProps.2.2.2.1, hRtt, hEnergy, hPayloadLe, hRcptEq,
                      beq_iff_eq.mp hCatSt⟩


/-! ## §4. Multi-Turn Cathedral Governance Trace (`List CathedralGovernanceTurn`) & Cumulative Invariants -/

deriving instance DecidableEq for Obend.Judge.DecoAndCallTree.SessionLedger

instance : Repr Obend.Judge.DecoAndCallTree.SessionLedger where
  reprPrec l _ := repr (l.consumedNonces.map (·.data), l.consumedIntents.map (·.data))

/-- Multi-turn governance state across sequential AI training/inference turns:
    tracks current model weight-lineage root, latest FPGA receipt epoch, cumulative proven FLOPs,
    remaining multi-turn FLOP budget, and remaining shadow-operation allowance. -/
structure CathedralTraceState where
  weightsRoot        : Nat
  lastEpoch          : Nat
  usedFlops          : Nat
  remFlopsBudget     : Nat
  remHiddenOpsBudget : Nat
  decoLedger : Obend.Judge.DecoAndCallTree.SessionLedger := ⟨[], []⟩
  deriving DecidableEq, Repr

/-- Total proven FLOPs across a multi-turn sequence `turns`. -/
def turnsTotalFlops : List CathedralGovernanceTurn → Nat
  | [] => 0
  | t :: ts => t.clusterCtx.step.flopsUsed + turnsTotalFlops ts

/-- Total shadow-operation cap consumed across a multi-turn sequence `turns`. -/
def turnsTotalHiddenOpsCap : List CathedralGovernanceTurn → Nat
  | [] => 0
  | t :: ts => t.physicalEnvelope.hiddenOpsCap + turnsTotalHiddenOpsCap ts

/-- Declarative weight-lineage continuity & strict epoch progression from `startRoot` and `startEpoch`
    to `(endRoot, endEpoch)` across `turns`. -/
def WeightAndEpochChain : Nat → Nat → List CathedralGovernanceTurn → Nat → Nat → Prop
  | wRoot, ep, [], endRoot, endEp => wRoot = endRoot ∧ ep = endEp
  | wRoot, ep, t :: ts, endRoot, endEp =>
    t.clusterCtx.step.prevWeightsRoot = wRoot ∧
    ep < t.fpgaReceipt.epoch ∧
    WeightAndEpochChain t.clusterCtx.step.nextWeightsRoot t.fpgaReceipt.epoch ts endRoot endEp

/-- Advance `CathedralTraceState` by one verified `CathedralGovernanceTurn`, enforcing single-turn
    cathedral soundness (`checkCathedralTurn`), weight-root continuity, strictly increasing FPGA
    epoch, and cumulative FLOP / shadow-energy budget deductions. -/
def stepCathedralTrace (st : CathedralTraceState) (turn : CathedralGovernanceTurn) :
    Option CathedralTraceState :=
  if checkCathedralTurn turn &&
     decide (turn.clusterCtx.step.prevWeightsRoot = st.weightsRoot) &&
     decide (st.lastEpoch < turn.fpgaReceipt.epoch) &&
     decide (turn.clusterCtx.step.flopsUsed ≤ st.remFlopsBudget) &&
     decide (turn.physicalEnvelope.hiddenOpsCap ≤ st.remHiddenOpsBudget) then
    (consumeSessionNodes turn.zkPolicy.verifiers st.decoLedger
      (allSessionNodes turn.batchCallTree)).map fun ledger => {
      weightsRoot        := turn.clusterCtx.step.nextWeightsRoot
      lastEpoch          := turn.fpgaReceipt.epoch
      usedFlops          := st.usedFlops + turn.clusterCtx.step.flopsUsed
      remFlopsBudget     := st.remFlopsBudget - turn.clusterCtx.step.flopsUsed
      remHiddenOpsBudget := st.remHiddenOpsBudget - turn.physicalEnvelope.hiddenOpsCap
      decoLedger := ledger
    }
  else
    none

/-- Execute an arbitrary-length sequence `List CathedralGovernanceTurn` from `init`. -/
def runCathedralTrace (init : CathedralTraceState) :
    List CathedralGovernanceTurn → Option CathedralTraceState
  | [] => some init
  | t :: ts =>
    match stepCathedralTrace init t with
    | none => none
    | some st' => runCathedralTrace st' ts

/-- Boolean decision gate for multi-turn cathedral governance traces. -/
def checkCathedralTrace (init : CathedralTraceState)
    (turns : List CathedralGovernanceTurn) : Bool :=
  (runCathedralTrace init turns).isSome

/-- **Multi-Turn Cathedral Governance Trace Soundness (`cathedralTrace_sound`)**:
    Whenever `runCathedralTrace init turns = some final` (equivalently `checkCathedralTrace init turns = true`),
    across **every turn** `t ∈ turns` and across the entire sequence:
    1. Every turn passes `checkCathedralTurn t = true` (hence `verifyZkStripeCallTree`, multi-hop
       `HopAudited`, domain-bound `callTreeDigest`, `Sable`, `Ozaki` `HyperLaw2`, RTT/energy bounds,
       and `≤ 32`-byte FPGA receipt hold at every turn),
    2. `WeightAndEpochChain` links `init.weightsRoot` to `final.weightsRoot` with strictly
       increasing FPGA receipt epochs (`init.lastEpoch ≤ final.lastEpoch`),
    3. Exact FLOP conservation `final.usedFlops + final.remFlopsBudget = init.usedFlops + init.remFlopsBudget`
       and `final.usedFlops = init.usedFlops + turnsTotalFlops turns`, and
    4. Cumulative multi-turn FLOP and shadow-operation caps never exceed the initial envelopes:
       `turnsTotalFlops turns ≤ init.remFlopsBudget` and
       `turnsTotalHiddenOpsCap turns ≤ init.remHiddenOpsBudget`. -/
theorem cathedralTrace_sound (init final : CathedralTraceState)
    (turns : List CathedralGovernanceTurn)
    (hRun : runCathedralTrace init turns = some final) :
    (∀ t ∈ turns, checkCathedralTurn t = true) ∧
      WeightAndEpochChain init.weightsRoot init.lastEpoch turns final.weightsRoot final.lastEpoch ∧
      init.lastEpoch ≤ final.lastEpoch ∧
      final.usedFlops = init.usedFlops + turnsTotalFlops turns ∧
      final.usedFlops + final.remFlopsBudget = init.usedFlops + init.remFlopsBudget ∧
      turnsTotalFlops turns ≤ init.remFlopsBudget ∧
      turnsTotalHiddenOpsCap turns ≤ init.remHiddenOpsBudget := by
  induction turns generalizing init with
  | nil =>
    injection hRun with hEq
    subst hEq
    exact ⟨(by intro _ h; cases h), ⟨rfl, rfl⟩, Nat.le_refl _,
      (by simp [turnsTotalFlops]), rfl, Nat.zero_le _, Nat.zero_le _⟩
  | cons t ts ih =>
    dsimp only [runCathedralTrace] at hRun
    cases hStep : stepCathedralTrace init t with
    | none => rw [hStep] at hRun; cases hRun
    | some st' =>
      rw [hStep] at hRun
      unfold stepCathedralTrace at hStep
      cases hCond : (checkCathedralTurn t &&
          decide (t.clusterCtx.step.prevWeightsRoot = init.weightsRoot) &&
          decide (init.lastEpoch < t.fpgaReceipt.epoch) &&
          decide (t.clusterCtx.step.flopsUsed ≤ init.remFlopsBudget) &&
          decide (t.physicalEnvelope.hiddenOpsCap ≤ init.remHiddenOpsBudget))
      · rw [hCond] at hStep; cases hStep
      · rw [hCond] at hStep
        simp only [↓reduceIte] at hStep
        cases hLedger : consumeSessionNodes t.zkPolicy.verifiers init.decoLedger
            (allSessionNodes t.batchCallTree) with
        | none => rw [hLedger] at hStep; cases hStep
        | some ledger =>
          rw [hLedger] at hStep
          simp only [Option.map_some, Option.some.injEq] at hStep
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
          rcases hCond with ⟨⟨⟨⟨hTurnOk, hPrevRoot⟩, hEpochLt⟩, hFlopsLe⟩, hHidLe⟩
          subst hStep
          obtain ⟨hAllRest, hChainRest, hEpRestLe, hUsedEq, hConsEq, hRestFlopsLe, hRestHidLe⟩ :=
            ih _ hRun
          dsimp only at hEpRestLe hUsedEq hConsEq hRestFlopsLe hRestHidLe
          refine ⟨?_, ⟨hPrevRoot, hEpochLt, hChainRest⟩, by omega, ?_, ?_, ?_, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hxRest
            · exact hTurnOk
            · exact hAllRest x hxRest
          · dsimp only [turnsTotalFlops]
            omega
          · omega
          · dsimp only [turnsTotalFlops]
            omega
          · dsimp only [turnsTotalHiddenOpsCap]
            omega


/-- No accepted Cathedral turn can reset the persistent DECO history. -/
theorem stepCathedralTrace_deco (st next : CathedralTraceState) (turn : CathedralGovernanceTurn)
    (h : stepCathedralTrace st turn = some next) :
    consumeSessionNodes turn.zkPolicy.verifiers st.decoLedger
      (allSessionNodes turn.batchCallTree) = some next.decoLedger := by
  unfold stepCathedralTrace at h
  split at h
  · cases hc : consumeSessionNodes turn.zkPolicy.verifiers st.decoLedger
        (allSessionNodes turn.batchCallTree) with
    | none => simp [hc] at h
    | some ledger => simp only [hc, Option.map_some, Option.some.injEq] at h; cases h; rfl
  · cases h

/-- Nonces and intents persist across arbitrarily many Cathedral turns. -/
theorem cathedralTrace_deco_history (initial final : CathedralTraceState)
    (turns : List CathedralGovernanceTurn) (h : runCathedralTrace initial turns = some final) :
    (∀ n ∈ initial.decoLedger.consumedNonces, n ∈ final.decoLedger.consumedNonces) ∧
    (∀ n ∈ initial.decoLedger.consumedIntents, n ∈ final.decoLedger.consumedIntents) := by
  induction turns generalizing initial with
  | nil => cases h; exact ⟨fun _ h => h, fun _ h => h⟩
  | cons turn rest ih =>
    unfold runCathedralTrace at h
    cases hs : stepCathedralTrace initial turn with
    | none => simp [hs] at h
    | some next =>
      rw [hs] at h
      obtain ⟨as, _, ht⟩ := consumeSessionNodes_sound _ _ _ _ (stepCathedralTrace_deco _ _ _ hs)
      obtain ⟨hn, hi⟩ := ih next h
      exact ⟨fun n hm => hn n (ht.nonces_mono n hm), fun n hm => hi n (ht.intents_mono n hm)⟩

/-- Changing a later turn's verifier policy cannot resurrect a consumed nonce or intent. -/
theorem cathedralTrace_replay_rejected (initial final : CathedralTraceState)
    (turns : List CathedralGovernanceTurn) (h : runCathedralTrace initial turns = some final)
    (policy : Obend.Judge.DecoAndCallTree.DecoPolicy)
    (a : Obend.Judge.DecoAndCallTree.DecoAttestation)
    (used : a.header.verifierNonce ∈ initial.decoLedger.consumedNonces ∨
      a.header.paymentIntentId ∈ initial.decoLedger.consumedIntents) :
    Obend.Judge.DecoAndCallTree.checkDecoAttestation policy final.decoLedger a = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have fresh := ((Obend.Judge.DecoAndCallTree.checkDecoAttestation_iff_relation _ _ _).mp accepted).1
  obtain ⟨hn, hi⟩ := cathedralTrace_deco_history initial final turns h
  rcases used with used | used
  · exact fresh.1 (hn _ used)
  · exact fresh.2.1 (hi _ used)

/-- Boolean-gate corollary of `cathedralTrace_sound` for `checkCathedralTrace init turns = true`. -/
theorem checkCathedralTrace_sound (init : CathedralTraceState)
    (turns : List CathedralGovernanceTurn)
    (hOk : checkCathedralTrace init turns = true) :
    ∃ final : CathedralTraceState,
      runCathedralTrace init turns = some final ∧
      (∀ t ∈ turns, checkCathedralTurn t = true) ∧
      WeightAndEpochChain init.weightsRoot init.lastEpoch turns final.weightsRoot final.lastEpoch ∧
      turnsTotalFlops turns ≤ init.remFlopsBudget ∧
      turnsTotalHiddenOpsCap turns ≤ init.remHiddenOpsBudget := by
  unfold checkCathedralTrace at hOk
  cases hRun : runCathedralTrace init turns with
  | none => rw [hRun] at hOk; cases hOk
  | some final =>
    have hProps := cathedralTrace_sound init final turns hRun
    exact ⟨final, rfl, hProps.1, hProps.2.1, hProps.2.2.2.2.2.1, hProps.2.2.2.2.2.2⟩


/-! ## §5. Concrete End-to-End Cathedral Turn & Multi-Turn Trace Witnesses -/

/-- Canonical end-to-end `CathedralGovernanceTurn` welding `ZkStripe.validFourHopCallTree`'s
    domain-bound Merkle commitment into `ClusterGov.validClusterStepCtx.step.batchCallTreeRoot`,
    `defaultPhysicalEnvelope`, and a 32-byte (`BitVec 256`) in-rack FPGA boolean verifier receipt. -/
def sampleCathedralTurn : CathedralGovernanceTurn :=
  let digestBytes := callTreeDigestBytes ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let batchRoot := callTreeDigest ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let stepWithRoot : AriadneStep :=
    { ClusterGov.validClusterStepCtx.step with batchCallTreeRoot := batchRoot }
  let rcpt256 :=
    computeFpgaVerifierReceipt256 ZkStripe.fastMerkleHash 7 1 batchRoot stepWithRoot true
  let treeLeft : AllReduceTree :=
    .node (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1])) (.leaf [-30, 10, 5])
  let treeRight : AllReduceTree :=
    .node (.leaf [-30, 10, 5]) (.node (.leaf [100, -20, 3]) (.leaf [50, 40, -1]))
  { hashFn                   := ZkStripe.fastMerkleHash
    zkPolicy                 := ZkStripe.defaultZkStripePolicy
    batchCallTree            := ZkStripe.validFourHopCallTree
    committedTreeDigestBytes := digestBytes
    clusterCtx               := { ClusterGov.validClusterStepCtx with step := stepWithRoot }
    physicalEnvelope         := ClusterGov.defaultPhysicalEnvelope
    fpgaReceipt := {
      rackId              := 7
      epoch               := 1
      verdict             := true
      verifierReceipt256  := rcpt256
      receiptPayloadBytes := encodeReceipt256 rcpt256
    }
    scheduleTracePair := [
      (⟨[0, 0, 0], 10⟩, ⟨[0, 0, 0], 20⟩),
      (runScheduledAllReduce treeLeft 10, runScheduledAllReduce treeRight 20)
    ]
    cathedralRules := [{
      name  := "cathedral_joint_admission"
      concl := "cathedral_turn_admitted"
      pos   := ["calltree_admitted", "step_admitted",
                "zkstripe_root_bound", "ozaki_hyperlaw_verified",
                "physical_energy_envelope_verified", "fpga_32byte_receipt_verified"]
      neg   := ["global_halt"]
    }]
    cathedralTarget := "cathedral_turn_admitted"
  }

/-- Second consecutive governance turn welding `prevWeightsRoot := 0x33334444` (the output weight
    root of `sampleCathedralTurn`) to `nextWeightsRoot := 0x55556666` at FPGA receipt `epoch := 2`. -/
def sampleSecondCathedralTurn : CathedralGovernanceTurn :=
  let batchRoot := callTreeDigest ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let step2 : AriadneStep := {
    prevWeightsRoot   := 0x33334444
    batchCallTreeRoot := batchRoot
    nextWeightsRoot   := 0x55556666
    flopsUsed         := 6000000
    flopsCap          := 10000000
  }
  let rcpt256 :=
    computeFpgaVerifierReceipt256 ZkStripe.fastMerkleHash 7 2 batchRoot step2 true
  { sampleCathedralTurn with
    zkPolicy := { defaultZkStripePolicy with verifiers := fixtureSessionVerifiers 1 }
    clusterCtx  := { sampleCathedralTurn.clusterCtx with step := step2 }
    fpgaReceipt := {
      rackId              := 7
      epoch               := 2
      verdict             := true
      verifierReceipt256  := rcpt256
      receiptPayloadBytes := encodeReceipt256 rcpt256
    }
  }

/-- Initial multi-turn governance envelope with 20M FLOPs and 10 shadow-ops budget. -/
def sampleInitTraceState : CathedralTraceState where
  weightsRoot        := 0x11112222
  lastEpoch          := 0
  usedFlops          := 0
  remFlopsBudget     := 20000000
  remHiddenOpsBudget := 10

/-- **Single-Turn Completeness (`checkCathedralTurn_complete`)**:
    Whenever every organ gate, canonical digest weld, physical envelope, 32-byte FPGA receipt,
    `HyperLaw2` check, and joint `Reasons.wf` target succeeds, `checkCathedralTurn turn = true`. -/
theorem checkCathedralTurn_complete (turn : CathedralGovernanceTurn)
    (reduced : List Int)
    (hZk : auditZkStripeCallTree turn.zkPolicy turn.batchCallTree = .ok ())
    (hCan : checkCanonicalSessionTree turn.hashFn turn.batchCallTree = true)
    (hBytes : callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes)
    (hWeld : callTreeDigest turn.hashFn turn.batchCallTree = turn.clusterCtx.step.batchCallTreeRoot)
    (hCluster : auditClusterStep turn.clusterCtx = .ok reduced)
    (hPhys : checkPhysicalEnergyEnvelope turn.physicalEnvelope = true)
    (hFpga : checkInRackFpgaReceipt turn.hashFn (callTreeDigest turn.hashFn turn.batchCallTree)
      turn.clusterCtx.step turn.fpgaReceipt = true)
    (hHL : checkHyperLaw2NonInterference clusterPublicView turn.scheduleTracePair = true)
    (hCat : Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
      turn.cathedralTarget = .supported) :
    checkCathedralTurn turn = true := by
  unfold checkCathedralTurn auditCathedralTurn
  have hBytesDec :
      decide (callTreeDigestBytes turn.hashFn turn.batchCallTree = turn.committedTreeDigestBytes) =
        true := decide_eq_true hBytes
  have hWeldDec :
      decide (callTreeDigest turn.hashFn turn.batchCallTree =
        turn.clusterCtx.step.batchCallTreeRoot) = true := decide_eq_true hWeld
  have hCatBeq :
      (Obend.Reasons.statusIn (Obend.Reasons.wf (buildCathedralProgram turn))
        turn.cathedralTarget == .supported) = true := beq_iff_eq.mpr hCat
  rw [hZk]
  dsimp only
  rw [hCan]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hBytesDec]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hWeldDec]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hCluster]
  dsimp only
  rw [hPhys, hFpga, hHL, hCatBeq]
  rfl

/-- **Multi-Turn Trace Completeness (`checkCathedralTrace_complete`)**:
    Extending any accepted multi-turn trace from `stepCathedralTrace init t = some st'` preserves
    `checkCathedralTrace init (t :: ts) = true` (and `runCathedralTrace init [] = some init`). -/
theorem checkCathedralTrace_complete (init st' : CathedralTraceState)
    (t : CathedralGovernanceTurn) (ts : List CathedralGovernanceTurn)
    (hTurn : checkCathedralTurn t = true)
    (hPrev : t.clusterCtx.step.prevWeightsRoot = init.weightsRoot)
    (hEp : init.lastEpoch < t.fpgaReceipt.epoch)
    (hFlops : t.clusterCtx.step.flopsUsed ≤ init.remFlopsBudget)
    (hHid : t.physicalEnvelope.hiddenOpsCap ≤ init.remHiddenOpsBudget)
    (ledger : Obend.Judge.DecoAndCallTree.SessionLedger)
    (hLedger : consumeSessionNodes t.zkPolicy.verifiers init.decoLedger
      (allSessionNodes t.batchCallTree) = some ledger)
    (hSt' : st' = {
      weightsRoot        := t.clusterCtx.step.nextWeightsRoot
      lastEpoch          := t.fpgaReceipt.epoch
      usedFlops          := init.usedFlops + t.clusterCtx.step.flopsUsed
      remFlopsBudget     := init.remFlopsBudget - t.clusterCtx.step.flopsUsed
      remHiddenOpsBudget := init.remHiddenOpsBudget - t.physicalEnvelope.hiddenOpsCap
      decoLedger := ledger
    })
    (hRest : checkCathedralTrace st' ts = true) :
    runCathedralTrace init [] = some init ∧
      checkCathedralTrace init (t :: ts) = true := by
  refine ⟨rfl, ?_⟩
  unfold checkCathedralTrace runCathedralTrace stepCathedralTrace
  have hPrevDec : decide (t.clusterCtx.step.prevWeightsRoot = init.weightsRoot) = true :=
    decide_eq_true hPrev
  have hEpDec : decide (init.lastEpoch < t.fpgaReceipt.epoch) = true := decide_eq_true hEp
  have hFlopsDec : decide (t.clusterCtx.step.flopsUsed ≤ init.remFlopsBudget) = true :=
    decide_eq_true hFlops
  have hHidDec : decide (t.physicalEnvelope.hiddenOpsCap ≤ init.remHiddenOpsBudget) = true :=
    decide_eq_true hHid
  rw [hTurn, hPrevDec, hEpDec, hFlopsDec, hHidDec]
  simp only [Bool.and_self, ↓reduceIte, hLedger, Option.map_some]
  rw [← hSt']
  exact hRest

example : checkCathedralTrace sampleInitTraceState [] = true := rfl

/-- Planted bad cathedral turn #1: swaps `batchCallTreeRoot` to an unauthenticated digest `0xDEAD`,
    breaking the `ZkStripe → ClusterGov` lineage weld. -/
def brokenWeldCathedralTurn : CathedralGovernanceTurn :=
  { sampleCathedralTurn with
    clusterCtx := {
      sampleCathedralTurn.clusterCtx with
      step := { sampleCathedralTurn.clusterCtx.step with batchCallTreeRoot := 0xDEAD }
    } }

/-- Planted bad cathedral turn #2: attempts to egress an oversized (> 32-byte) proof payload across
    the rack boundary, caught by `checkInRackFpgaReceipt`. -/
def oversizedReceiptCathedralTurn : CathedralGovernanceTurn :=
  { sampleCathedralTurn with
    fpgaReceipt := {
      sampleCathedralTurn.fpgaReceipt with
      receiptPayloadBytes := ⟨(List.replicate 64 (0xAA : UInt8)).toArray⟩
    } }

/-- Executable Silver end-to-end smoke check for `CathedralApex` (single-turn + multi-turn trace). -/
def silverCathedralApexSmoke : Bool :=
  let expectedRoot := callTreeDigest ZkStripe.fastMerkleHash ZkStripe.validFourHopCallTree
  let validOk :=
    match auditCathedralTurn sampleCathedralTurn with
    | .ok (_, slices) => slices == #[120, 30, 7]
    | .error _ => false
  let multiTurnOk :=
    match runCathedralTrace sampleInitTraceState
        [sampleCathedralTurn, sampleSecondCathedralTurn] with
    | some finalSt =>
      finalSt.weightsRoot == 0x55556666 &&
      finalSt.lastEpoch == 2 &&
      finalSt.usedFlops == 13500000 &&
      finalSt.remFlopsBudget == 6500000 &&
      finalSt.remHiddenOpsBudget == 2
    | none => false
  let replayEpochRefused :=
    !checkCathedralTrace sampleInitTraceState [sampleCathedralTurn, sampleCathedralTurn]
  let weldRefused :=
    match auditCathedralTurn brokenWeldCathedralTurn with
    | .error e => e == .batchRootWeldMismatch expectedRoot 0xDEAD
    | .ok _ => false
  let egressRefused :=
    match auditCathedralTurn oversizedReceiptCathedralTurn with
    | .error e => e == .fpgaReceiptInvalid 64
    | .ok _ => false
  validOk && multiTurnOk && replayEpochRefused && weldRefused && egressRefused

end Obend.Trailblaze.CathedralApex

end
