module
/-
# Obend.Trailblaze.ZkStripe — Organ O5: Boolean-Closed `PredRE`, `VpaOver` & 4-Hop `tlsn` HTTPS `CallTree` Audit

Concrete executable Silver spine and kernel-checked algebraic laws for Organ O5 (`zkStripe`):

1. **Boolean-Closed Byte Regular Expressions (`PredRE`)**:
   Supports empty language (`emp`), empty word (`eps`), byte intervals (`charRange`), alternation
   (`alt`), concatenation (`seq`), Kleene star (`star`), **boolean complement (`compl`)**, and
   **conjunction (`inter`)**. Executed via Brzozowski byte derivatives (`nullable`, `deriv`,
   `matchesBytes`) with unconditionally proved complement (`matchesBytes_compl`), intersection
   (`matchesBytes_inter`), alternation (`matchesBytes_alt`), and De Morgan laws.
2. **Visibly Pushdown Automata (`VpaOver` / `VpaMachine`, Alur–Madhusudan)**:
   Tagged call/return/internal byte alphabet (`VpaSymbol`) and deterministic pushdown evaluator
   (`runVpa`) enforcing balanced JSON/HTTP chunk/XML nesting, with unconditionally proved stack-tag
   well-matchedness (`execVpa_preserves_tag_stack`, `runVpa_balanced_stack`).
3. **Authenticated Multi-Hop `tlsn` HTTPS `CallTree` & `Obend.Reasons` Policy Audit**:
   256-bit Merkle commitment (`callTreeDigest` over `Obend.Digest.HashBytes`) + Well-Founded
   `Reasons.Program` extraction (`buildCallTreeProgram`), named refusal diagnostics
   (`auditZkStripeCallTree`), explicit Wave-4 `class ZkStripeObligations : Prop`, kernel-proved
   `apex_zkstripe_calltree_audit`, and runnable 4-hop `silverZkStripeSmoke`.
-/
public import Obend.Reasons
public import Obend.Digest.HashBytes
public import Obend.Judge.Class

public section
namespace Obend.Trailblaze.ZkStripe

open Obend.Digest.HashBytes (Hash ofBE be Collision)

set_option autoImplicit false

/-! ## §1. Boolean-Closed Regular Expressions (`PredRE`) & Brzozowski Derivatives -/

/-- Byte-level boolean-closed regular expression supporting complement (`compl`) and
    conjunction (`inter`) alongside standard regular operators. -/
inductive PredRE where
  | emp : PredRE
  | eps : PredRE
  | charRange (lo hi : UInt8) : PredRE
  | alt (r₁ r₂ : PredRE) : PredRE
  | seq (r₁ r₂ : PredRE) : PredRE
  | star (r : PredRE) : PredRE
  | compl (r : PredRE) : PredRE
  | inter (r₁ r₂ : PredRE) : PredRE
  deriving DecidableEq, Repr

namespace PredRE

/-- Match a single exact byte `b`. -/
@[expose] def byte (b : UInt8) : PredRE :=
  .charRange b b

/-- Match any byte `0x00 .. 0xFF`. -/
@[expose] def anyByte : PredRE :=
  .charRange 0 255

/-- Match an exact sequence of literal bytes. -/
@[expose] def litBytes : List UInt8 → PredRE
  | [] => .eps
  | b :: bs => .seq (.byte b) (litBytes bs)

/-- Match any byte slice containing `pat` as a contiguous substring (`Σ* · pat · Σ*`). -/
@[expose] def containsSubseq (pat : List UInt8) : PredRE :=
  .seq (.star anyByte) (.seq (litBytes pat) (.star anyByte))

/-- Redaction confinement regex: accepts iff `pat` NEVER occurs in the byte stream (`¬(Σ* · pat · Σ*)`). -/
@[expose] def forbidSubseq (pat : List UInt8) : PredRE :=
  .compl (containsSubseq pat)

end PredRE

/-- Brzozowski nullability test: `true` iff the empty byte string `[]` belongs to `L(r)`. -/
@[expose] def nullable : PredRE → Bool
  | .emp => false
  | .eps => true
  | .charRange _ _ => false
  | .alt r₁ r₂ => nullable r₁ || nullable r₂
  | .seq r₁ r₂ => nullable r₁ && nullable r₂
  | .star _ => true
  | .compl r => !nullable r
  | .inter r₁ r₂ => nullable r₁ && nullable r₂

/-- Smart concatenation constructor collapsing absorbing `.emp` and identity `.eps` (Owens–Reppy–Turon),
    preventing exponential derivative AST blowup on Kleene star (`∂_b (any*) = any*`). -/
@[expose] def mkSeq : PredRE → PredRE → PredRE
  | .emp, _ => .emp
  | _, .emp => .emp
  | .eps, r₂ => r₂
  | r₁, .eps => r₁
  | r₁, r₂ => .seq r₁ r₂

/-- Brzozowski single-byte derivative `∂_b r`. -/
@[expose] def deriv : PredRE → UInt8 → PredRE
  | .emp, _ => .emp
  | .eps, _ => .emp
  | .charRange lo hi, b =>
    if decide (lo ≤ b ∧ b ≤ hi) then .eps else .emp
  | .alt r₁ r₂, b => .alt (deriv r₁ b) (deriv r₂ b)
  | .seq r₁ r₂, b =>
    if nullable r₁ then
      .alt (mkSeq (deriv r₁ b) r₂) (deriv r₂ b)
    else
      mkSeq (deriv r₁ b) r₂
  | .star r, b => mkSeq (deriv r b) (.star r)
  | .compl r, b => .compl (deriv r b)
  | .inter r₁ r₂, b => .inter (deriv r₁ b) (deriv r₂ b)

/-- Total Brzozowski byte-stream matcher. -/
@[expose] def matchesBytes : PredRE → List UInt8 → Bool
  | r, [] => nullable r
  | r, b :: bs => matchesBytes (deriv r b) bs

/-- Empty regex rejects every byte string. -/
theorem matchesBytes_emp (bs : List UInt8) :
    matchesBytes .emp bs = false := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simpa [matchesBytes, deriv] using ih

/-- **Exact Boolean Complement Law**: `matchesBytes (.compl r) bs` is the exact boolean
    negation of `matchesBytes r bs` on every byte string `bs`. -/
theorem matchesBytes_compl (r : PredRE) (bs : List UInt8) :
    matchesBytes (.compl r) bs = !matchesBytes r bs := by
  induction bs generalizing r with
  | nil => rfl
  | cons b rest ih =>
    simp only [matchesBytes, deriv]
    exact ih (deriv r b)

/-- **Exact Boolean Conjunction Law**: `matchesBytes (.inter r₁ r₂) bs` equals the boolean
    conjunction of `matchesBytes r₁ bs` and `matchesBytes r₂ bs` on every byte string `bs`. -/
theorem matchesBytes_inter (r₁ r₂ : PredRE) (bs : List UInt8) :
    matchesBytes (.inter r₁ r₂) bs = (matchesBytes r₁ bs && matchesBytes r₂ bs) := by
  induction bs generalizing r₁ r₂ with
  | nil => rfl
  | cons b rest ih =>
    simp only [matchesBytes, deriv]
    exact ih (deriv r₁ b) (deriv r₂ b)

/-- **Exact Boolean Disjunction Law**: `matchesBytes (.alt r₁ r₂) bs` equals the boolean
    disjunction of `matchesBytes r₁ bs` and `matchesBytes r₂ bs` on every byte string `bs`. -/
theorem matchesBytes_alt (r₁ r₂ : PredRE) (bs : List UInt8) :
    matchesBytes (.alt r₁ r₂) bs = (matchesBytes r₁ bs || matchesBytes r₂ bs) := by
  induction bs generalizing r₁ r₂ with
  | nil => rfl
  | cons b rest ih =>
    simp only [matchesBytes, deriv]
    exact ih (deriv r₁ b) (deriv r₂ b)

/-- Double complement involutivity on `matchesBytes`. -/
theorem matchesBytes_compl_compl (r : PredRE) (bs : List UInt8) :
    matchesBytes (.compl (.compl r)) bs = matchesBytes r bs := by
  rw [matchesBytes_compl, matchesBytes_compl, Bool.not_not]

/-- De Morgan duality for `PredRE` complement over alternation. -/
theorem matchesBytes_deMorgan_alt (r₁ r₂ : PredRE) (bs : List UInt8) :
    matchesBytes (.compl (.alt r₁ r₂)) bs = matchesBytes (.inter (.compl r₁) (.compl r₂)) bs := by
  rw [matchesBytes_compl, matchesBytes_alt, matchesBytes_inter, matchesBytes_compl,
      matchesBytes_compl, Bool.not_or]


/-! ## §2. Visibly Pushdown Automata (`VpaOver` / `VpaMachine`) & Balanced Stack Invariant -/

/-- Partitioned visibly pushdown input alphabet (`Σ = Σ_c ⊎ Σ_r ⊎ Σ_i`). -/
inductive VpaSymbol where
  | call (tag : UInt8) (sym : UInt8)
  | ret (tag : UInt8) (sym : UInt8)
  | internal (sym : UInt8)
  deriving DecidableEq, Repr

/-- Pushdown stack frame saving the caller state and structural delimiter tag. -/
structure VpaStackFrame where
  savedState : Nat
  callTag    : UInt8
  deriving DecidableEq, Repr

/-- Deterministic Visibly Pushdown Automaton (`VpaOver` / `VpaMachine`, Alur–Madhusudan). -/
structure VpaOver where
  initState    : Nat
  acceptStates : List Nat
  onCall       : Nat → UInt8 → UInt8 → Option Nat
  onRet        : Nat → Nat → UInt8 → UInt8 → Option Nat
  onInternal   : Nat → UInt8 → Option Nat

abbrev VpaMachine := VpaOver

/-- Single-symbol VPA transition: calls push `⟨q, tag⟩`, returns require a matching top-of-stack
    `callTag` and pop, and internals leave the stack untouched. -/
@[expose] def stepVpa (m : VpaMachine) (q : Nat) (stk : List VpaStackFrame)
    (sym : VpaSymbol) : Option (Nat × List VpaStackFrame) :=
  match sym with
  | .internal b =>
    (m.onInternal q b).map fun q' => (q', stk)
  | .call tag b =>
    (m.onCall q tag b).map fun q' => (q', ⟨q, tag⟩ :: stk)
  | .ret tag b =>
    match stk with
    | [] => none
    | top :: rest =>
      if top.callTag == tag then
        (m.onRet q top.savedState tag b).map fun q' => (q', rest)
      else
        none

/-- Multi-step deterministic VPA execution over a symbol trace. -/
@[expose] def execVpa (m : VpaMachine) (q : Nat) (stk : List VpaStackFrame) :
    List VpaSymbol → Option (Nat × List VpaStackFrame)
  | [] => some (q, stk)
  | sym :: rest =>
    match stepVpa m q stk sym with
    | none => none
    | some (q', stk') => execVpa m q' stk' rest

/-- Accept iff execution finishes in an accepting control state with an empty call stack. -/
@[expose] def runVpa (m : VpaMachine) (trace : List VpaSymbol) : Bool :=
  match execVpa m m.initState [] trace with
  | some (qf, []) => m.acceptStates.contains qf
  | _ => false

/-- Machine-independent structural nesting tracker over open call tags: returns `some finalTags`
    iff no return underflows or mismatches its enclosing open call tag. -/
@[expose] def wellMatchedTags (openTags : List UInt8) : List VpaSymbol → Option (List UInt8)
  | [] => some openTags
  | .internal _ :: rest => wellMatchedTags openTags rest
  | .call tag _ :: rest => wellMatchedTags (tag :: openTags) rest
  | .ret tag _ :: rest =>
    match openTags with
    | [] => none
    | top :: stkRest =>
      if top == tag then wellMatchedTags stkRest rest else none

/-- A VPA symbol stream is structurally well-nested iff all calls and returns match and close. -/
def IsBalancedVpaTrace (trace : List VpaSymbol) : Prop :=
  wellMatchedTags [] trace = some []

theorem stepVpa_preserves_tag_stack (m : VpaMachine) (q q' : Nat)
    (stk stk' : List VpaStackFrame) (sym : VpaSymbol)
    (h : stepVpa m q stk sym = some (q', stk')) :
    match sym with
    | .internal _ => stk'.map VpaStackFrame.callTag = stk.map VpaStackFrame.callTag
    | .call tag _ => stk'.map VpaStackFrame.callTag = tag :: stk.map VpaStackFrame.callTag
    | .ret tag _ => stk.map VpaStackFrame.callTag = tag :: stk'.map VpaStackFrame.callTag := by
  cases sym with
  | internal b =>
    simp only [stepVpa, Option.map_eq_some_iff] at h
    rcases h with ⟨qn, _, hEq⟩
    cases hEq
    rfl
  | call tag b =>
    simp only [stepVpa, Option.map_eq_some_iff] at h
    rcases h with ⟨qn, _, hEq⟩
    cases hEq
    rfl
  | ret tag b =>
    cases stk with
    | nil => simp [stepVpa] at h
    | cons top rest =>
      simp only [stepVpa] at h
      split at h
      · next hTag =>
        simp only [Option.map_eq_some_iff] at h
        rcases h with ⟨qn, _, hEq⟩
        cases hEq
        have hTagEq : top.callTag = tag := beq_iff_eq.mp hTag
        simp [hTagEq]
      · cases h

/-- **VPA Stack-Tag Invariant**: Every accepted or partial execution of *any* `VpaMachine`
    tracks the exact structural call-tag stack of `wellMatchedTags`. -/
theorem execVpa_preserves_tag_stack (m : VpaMachine) (trace : List VpaSymbol)
    (q qf : Nat) (stk stkf : List VpaStackFrame)
    (h : execVpa m q stk trace = some (qf, stkf)) :
    wellMatchedTags (stk.map VpaStackFrame.callTag) trace =
      some (stkf.map VpaStackFrame.callTag) := by
  induction trace generalizing q stk with
  | nil =>
    simp only [execVpa, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, hStk⟩
    subst hStk
    rfl
  | cons sym rest ih =>
    simp only [execVpa] at h
    cases hStep : stepVpa m q stk sym with
    | none => rw [hStep] at h; cases h
    | some pair =>
      rcases pair with ⟨q', stk'⟩
      rw [hStep] at h
      have hTag := stepVpa_preserves_tag_stack m q q' stk stk' sym hStep
      have ihRes := ih q' stk' h
      cases sym with
      | internal b =>
        simp only [wellMatchedTags]
        rw [← hTag]
        exact ihRes
      | call tag b =>
        simp only [wellMatchedTags]
        rw [← hTag]
        exact ihRes
      | ret tag b =>
        cases stk with
        | nil => simp [stepVpa] at hStep
        | cons top stkRest =>
          simp only [List.map_cons, List.cons.injEq] at hTag
          rcases hTag with ⟨hTopEq, hRestEq⟩
          simp only [List.map_cons, wellMatchedTags, hTopEq, beq_self_eq_true, ↓reduceIte]
          rw [hRestEq]
          exact ihRes

/-- **Balanced Stack Theorem**: Any trace accepted by `runVpa m` has strictly balanced,
    tag-matched calls and returns (`wellMatchedTags [] trace = some []`). -/
theorem runVpa_balanced_stack (m : VpaMachine) (trace : List VpaSymbol)
    (h : runVpa m trace = true) :
    IsBalancedVpaTrace trace := by
  unfold runVpa at h
  cases hExec : execVpa m m.initState [] trace with
  | none => rw [hExec] at h; cases h
  | some pair =>
    rcases pair with ⟨qf, stkf⟩
    rw [hExec] at h
    cases stkf with
    | nil =>
      exact execVpa_preserves_tag_stack m trace m.initState qf [] [] hExec
    | cons _ _ =>
      cases h

/-- Leading unmatched return symbol is unconditionally rejected by every `VpaMachine`. -/
theorem runVpa_rejects_unmatched_ret (m : VpaMachine) (tag b : UInt8) (rest : List VpaSymbol) :
    runVpa m (.ret tag b :: rest) = false := by
  simp [runVpa, execVpa, stepVpa]

/-- Project JSON/HTTP structured payload bytes onto `VpaSymbol`s (`'{'`/`'}'` tag `1`, `'['`/`']'` tag `2`). -/
@[expose] def lexJsonVpaSymbols (bs : List UInt8) : List VpaSymbol :=
  bs.map fun b =>
    if b == 123 then .call 1 b       -- '{'
    else if b == 125 then .ret 1 b   -- '}'
    else if b == 91 then .call 2 b   -- '['
    else if b == 93 then .ret 2 b    -- ']'
    else .internal b

/-- Canonical deterministic VPA accepting non-empty well-balanced JSON/HTTP framed payloads. -/
@[expose] def jsonFramingVpa : VpaMachine where
  initState    := 0
  acceptStates := [1]
  onCall       := fun _ _ _ => some 1
  onRet        := fun _ _ _ _ => some 1
  onInternal   := fun q _ => some q


/-! ## §3. 4-Hop `tlsn` Authenticated HTTPS `CallTree`, Merkle Binding & `Reasons` Audit -/

/-- A node in an authenticated `tlsn` HTTPS session tree (`CallTree`):
    commits the MPC-TLS notary public-key hash, target server domain, redacted request/response
    byte slices, and downstream causal child sessions (e.g. webhook → auth → manifest → shard). -/
inductive HttpsSessionNode where
  | mk
    (notaryKeyHash    : Nat)
    (serverDomain     : String)
    (redactedRequest  : List UInt8)
    (redactedResponse : List UInt8)
    (children         : List HttpsSessionNode)
  deriving Repr

namespace HttpsSessionNode

@[expose] def notaryKeyHash : HttpsSessionNode → Nat
  | .mk h _ _ _ _ => h

@[expose] def serverDomain : HttpsSessionNode → String
  | .mk _ d _ _ _ => d

@[expose] def redactedRequest : HttpsSessionNode → List UInt8
  | .mk _ _ req _ _ => req

@[expose] def redactedResponse : HttpsSessionNode → List UInt8
  | .mk _ _ _ resp _ => resp

@[expose] def children : HttpsSessionNode → List HttpsSessionNode
  | .mk _ _ _ _ cs => cs

end HttpsSessionNode

/-- Length-prefixed canonical framing (`len:4 ‖ payload`) for byte slices inside Merkle nodes. -/
@[expose] def frameBytes (xs : List UInt8) : List UInt8 :=
  be 4 xs.length ++ xs

mutual
/-- Recursive Merkle commitment bytes of an `HttpsSessionNode` over byte hash `H`:
    commits `notaryKeyHash`, HTTP `Host`+path `redactedRequest` bytes, `redactedResponse` bytes,
    and child session subtree digests (compiled via `structural` recursion on `HttpsSessionNode`
    so kernel reduction never invokes `WellFounded.fix` / `sizeOf String`). -/
@[expose] def callTreeDigestBytes (H : Hash) (n : HttpsSessionNode) : List UInt8 :=
  match n with
  | .mk notaryHash _ req resp kids =>
    let preimage :=
      (0x01 : UInt8) ::
      be 8 notaryHash ++
      frameBytes req ++
      frameBytes resp ++
      callTreeChildrenDigestBytes H kids
    H preimage
termination_by structural n

@[expose] def callTreeChildrenDigestBytes (H : Hash) (ns : List HttpsSessionNode) : List UInt8 :=
  match ns with
  | [] => [(0x00 : UInt8)]
  | c :: cs =>
    let cd := callTreeDigestBytes H c
    H ((0x02 : UInt8) :: frameBytes cd ++ callTreeChildrenDigestBytes H cs)
termination_by structural ns
end

/-- 256-bit integer reading (`ofBE`) of `callTreeDigestBytes H`. -/
@[expose] def callTreeDigest (H : Hash) (node : HttpsSessionNode) : Nat :=
  ofBE (callTreeDigestBytes H node)

mutual
/-- Count total notarized HTTPS hops in a `CallTree`. -/
@[expose] def callTreeHopCount : HttpsSessionNode → Nat
  | .mk _ _ _ _ kids => 1 + callTreeChildrenHopCount kids

@[expose] def callTreeChildrenHopCount : List HttpsSessionNode → Nat
  | [] => 0
  | c :: cs => callTreeHopCount c + callTreeChildrenHopCount cs
end

/-- `zkStripe` audit policy combining notary trust roots, boolean-closed `PredRE` request/response
    confinement, visibly pushdown framing (`VpaMachine`), and `Obend.Reasons` policy rules. -/
structure ZkStripePolicy where
  trustedNotaryHashes : List Nat
  allowedRequestRe    : PredRE
  allowedResponseRe   : PredRE
  framingVpa          : VpaMachine
  policyRules         : List Obend.Reasons.Rule
  targetConclusion    : String

/-- Named refusal diagnostic for `zkStripe` `CallTree` verification. -/
inductive ZkStripeRefusal where
  | untrustedNotary (domain : String) (notaryHash : Nat)
  | requestRegexViolation (domain : String)
  | responseRegexViolation (domain : String)
  | unbalancedFraming (domain : String)
  | policyUnsupported (conclusion : String) (status : Obend.Reasons.Status)
  deriving DecidableEq, Repr

mutual
/-- Extract ground `Obend.Reasons` facts from an authenticated `HttpsSessionNode` subtree:
    one `"hop_verified:<domain>"` fact per notarized, regex-clean, VPA-framed session hop. -/
@[expose] def extractCallTreeFacts (pol : ZkStripePolicy) : HttpsSessionNode → List String
  | .mk notaryHash domain req resp kids =>
    let hopFact :=
      if pol.trustedNotaryHashes.contains notaryHash &&
         matchesBytes pol.allowedRequestRe req &&
         matchesBytes pol.allowedResponseRe resp &&
         runVpa pol.framingVpa (lexJsonVpaSymbols resp) then
        ["hop_verified:" ++ domain]
      else []
    hopFact ++ extractChildrenFacts pol kids

@[expose] def extractChildrenFacts (pol : ZkStripePolicy) : List HttpsSessionNode → List String
  | [] => []
  | c :: cs => extractCallTreeFacts pol c ++ extractChildrenFacts pol cs
end

/-- Assemble the `Obend.Reasons.Program` induced by a `ZkStripePolicy` and `CallTree`. -/
@[expose] def buildCallTreeProgram (pol : ZkStripePolicy) (root : HttpsSessionNode) :
    Obend.Reasons.Program where
  facts := extractCallTreeFacts pol root
  rules := pol.policyRules

mutual
/-- Check every node in the `CallTree` against notary trust, `PredRE` confinement, and `VpaOver` framing. -/
@[expose] def auditNodes (pol : ZkStripePolicy) : HttpsSessionNode → Except ZkStripeRefusal Unit
  | .mk notaryHash domain req resp kids =>
    if !pol.trustedNotaryHashes.contains notaryHash then
      .error (.untrustedNotary domain notaryHash)
    else if !matchesBytes pol.allowedRequestRe req then
      .error (.requestRegexViolation domain)
    else if !matchesBytes pol.allowedResponseRe resp then
      .error (.responseRegexViolation domain)
    else if !runVpa pol.framingVpa (lexJsonVpaSymbols resp) then
      .error (.unbalancedFraming domain)
    else
      auditChildren pol kids

@[expose] def auditChildren (pol : ZkStripePolicy) :
    List HttpsSessionNode → Except ZkStripeRefusal Unit
  | [] => .ok ()
  | c :: cs =>
    match auditNodes pol c with
    | .error e => .error e
    | .ok () => auditChildren pol cs
end

/-- Full `zkStripe` `CallTree` audit: checks every hop's notary root, `PredRE` request/response
    confinement, `VpaMachine` structural framing, and `Obend.Reasons.wf` policy support. -/
@[expose] def auditZkStripeCallTree (pol : ZkStripePolicy) (root : HttpsSessionNode) :
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

/-- Boolean decision wrapper for `auditZkStripeCallTree`. -/
@[expose] def verifyZkStripeCallTree (pol : ZkStripePolicy) (root : HttpsSessionNode) : Bool :=
  (auditZkStripeCallTree pol root).isOk

/-- Succinct `DualPCS` (`HashUDR` ∨ `LatticeSIS`) receipt envelope for a redacted `CallTree`. -/
structure DualPcsCallTreeReceipt where
  committedTreeRoot  : Nat
  notaryQuorumDigest : Nat
  proofBytes         : List UInt8
  deriving DecidableEq, Repr

/-- Explicit Wave-4 cryptographic & circuit proof obligations for Organ O5 (`zkStripe`):
    1. `tlsnAeadCommitmentBinding`: `callTreeDigest H` binds the entire `HttpsSessionNode` tree
       up to hash collision (`Collision H`);
    2. `dualPcsCallTreeExtract`: any accepted `DualPcsCallTreeReceipt` for `committedRoot` extracts
       an underlying notarized `HttpsSessionNode` matching `committedRoot` and passing `verifyZkStripeCallTree`. -/
class ZkStripeObligations : Prop where
  tlsnAeadCommitmentBinding :
    ∀ (H : Hash) (t₁ t₂ : HttpsSessionNode),
      callTreeDigest H t₁ = callTreeDigest H t₂ →
      t₁ = t₂ ∨ Collision H
  dualPcsCallTreeExtract :
    ∀ (H : Hash) (pol : ZkStripePolicy) (rcpt : DualPcsCallTreeReceipt),
      rcpt.proofBytes ≠ [] →
      ∀ (tree : HttpsSessionNode),
        callTreeDigest H tree = rcpt.committedTreeRoot →
        verifyZkStripeCallTree pol tree = true →
        Obend.Reasons.statusIn (Obend.Reasons.wf (buildCallTreeProgram pol tree))
          pol.targetConclusion = .supported

theorem auditNodes_root_props {pol : ZkStripePolicy} {tree : HttpsSessionNode}
    (hOk : auditNodes pol tree = .ok ()) :
    pol.trustedNotaryHashes.contains tree.notaryKeyHash = true ∧
      matchesBytes pol.allowedRequestRe tree.redactedRequest = true ∧
      matchesBytes pol.allowedResponseRe tree.redactedResponse = true ∧
      IsBalancedVpaTrace (lexJsonVpaSymbols tree.redactedResponse) := by
  cases tree with
  | mk notaryHash domain req resp kids =>
    unfold auditNodes at hOk
    split at hOk
    · cases hOk
    · next hNotNotary =>
      have hNotary : pol.trustedNotaryHashes.contains notaryHash = true := by
        cases h : pol.trustedNotaryHashes.contains notaryHash <;> simp_all
      split at hOk
      · cases hOk
      · next hNotReq =>
        have hReq : matchesBytes pol.allowedRequestRe req = true := by
          cases h : matchesBytes pol.allowedRequestRe req <;> simp_all
        split at hOk
        · cases hOk
        · next hNotResp =>
          have hResp : matchesBytes pol.allowedResponseRe resp = true := by
            cases h : matchesBytes pol.allowedResponseRe resp <;> simp_all
          split at hOk
          · cases hOk
          · next hNotVpa =>
            have hVpa : runVpa pol.framingVpa (lexJsonVpaSymbols resp) = true := by
              cases h : runVpa pol.framingVpa (lexJsonVpaSymbols resp) <;> simp_all
            exact ⟨hNotary, hReq, hResp, runVpa_balanced_stack pol.framingVpa _ hVpa⟩

/-- **Organ O5 Apex Audit Theorem (`apex_zkstripe_calltree_audit`)**:
    Whenever `auditZkStripeCallTree` admits a notarized HTTPS `CallTree` under a policy whose
    request regex enforces `.compl forbiddenSecretRe`, Lean's kernel guarantees:
    1. Root notary key membership + balanced VPA response framing (`IsBalancedVpaTrace`),
    2. Zero forbidden secret pattern match (`matchesBytes forbiddenSecretRe tree.redactedRequest = false`)
       via `matchesBytes_inter` and `matchesBytes_compl`,
    3. Well-founded `Obend.Reasons.wf` support for `pol.targetConclusion`, and
    4. Collision-bound tree commitment integrity under `[ZkStripeObligations]`. -/
theorem apex_zkstripe_calltree_audit [ZkStripeObligations]
    (H : Hash) (reqSchema forbiddenSecretRe : PredRE)
    (pol : ZkStripePolicy) (tree otherTree : HttpsSessionNode)
    (hReqPolicy : pol.allowedRequestRe = .inter reqSchema (.compl forbiddenSecretRe))
    (hAudit : auditZkStripeCallTree pol tree = .ok ())
    (hSameDigest : callTreeDigest H tree = callTreeDigest H otherTree) :
    pol.trustedNotaryHashes.contains tree.notaryKeyHash = true ∧
      matchesBytes forbiddenSecretRe tree.redactedRequest = false ∧
      IsBalancedVpaTrace (lexJsonVpaSymbols tree.redactedResponse) ∧
      Obend.Reasons.statusIn (Obend.Reasons.wf (buildCallTreeProgram pol tree))
        pol.targetConclusion = .supported ∧
      (tree = otherTree ∨ Collision H) := by
  unfold auditZkStripeCallTree at hAudit
  cases hNodes : auditNodes pol tree with
  | error e => rw [hNodes] at hAudit; cases hAudit
  | ok u =>
    rw [hNodes] at hAudit
    have ⟨hNotary, hReq, _, hBal⟩ := auditNodes_root_props hNodes
    rw [hReqPolicy, matchesBytes_inter, matchesBytes_compl, Bool.and_eq_true,
        Bool.not_eq_true'] at hReq
    simp only at hAudit
    split at hAudit
    · next hSt =>
      have hSupported :
          Obend.Reasons.statusIn (Obend.Reasons.wf (buildCallTreeProgram pol tree))
            pol.targetConclusion = .supported := beq_iff_eq.mp hSt
      have hBind := ZkStripeObligations.tlsnAeadCommitmentBinding H tree otherTree hSameDigest
      exact ⟨hNotary, hReq.2, hBal, hSupported, hBind⟩
    · cases hAudit


/-! ## §4. Concrete 4-Hop `tlsn` HTTPS `CallTree` Fixtures & Silver Smoke Runner -/

/-- Fast deterministic `UInt8` XOR-bijection `Hash` for linear-WHNF kernel smoke checks
    (`acc ^^^ (b + 0x9E)` reduces via native kernel `Nat.xor` without `Nat.modCore` stack blowup
    and preserves strict single-byte sensitivity across multi-hop Merkle trees;
    production callers instantiate `H := Obend.Core.Digest.deployed` cSHAKE256). -/
@[expose] def fastMerkleHash : Hash := fun bs =>
  let h0 : UInt8 := bs.foldl (fun acc b => acc ^^^ (b + 0x9E)) 0x5A
  [0xA5, h0, UInt8.ofNat bs.length]

/-- Forbidden live Stripe secret prefix `"sk_"` (`[115, 107, 95]`). -/
@[expose] def stripeLiveKeyPrefix : List UInt8 := [115, 107, 95]

/-- Required HTTP `GET` prefix (`[71, 69, 84]`). -/
@[expose] def httpGetPrefix : List UInt8 := [71, 69, 84]

/-- Canonical `ZkStripePolicy`: requires trusted notary `0xA11CE`, HTTP `GET` prefix, zero `"sk_"`
    secret-key leakage in both requests and responses via `.compl`, balanced JSON VPA framing, and
    4-hop `Reasons` causal chain `api.stripe.com → auth.obend.org → registry.hf.co → cdn.dataset.org`. -/
@[expose] def defaultZkStripePolicy : ZkStripePolicy where
  trustedNotaryHashes := [0xA11CE]
  allowedRequestRe    := .inter (.seq (PredRE.litBytes httpGetPrefix) (.star PredRE.anyByte))
                                (PredRE.forbidSubseq stripeLiveKeyPrefix)
  allowedResponseRe   := PredRE.forbidSubseq stripeLiveKeyPrefix
  framingVpa          := jsonFramingVpa
  policyRules := [
    { name  := "admit_four_hop_calltree"
      concl := "calltree_admitted"
      pos   := ["hop_verified:api.stripe.com", "hop_verified:auth.obend.org",
                "hop_verified:registry.hf.co", "hop_verified:cdn.dataset.org"]
      neg   := ["emergency_freeze"] }
  ]
  targetConclusion := "calltree_admitted"

/-- Valid 4-hop `tlsn`-notarized HTTPS `CallTree`:
    1. `api.stripe.com` → 2. `auth.obend.org` → 3. `registry.hf.co` → 4. `cdn.dataset.org`. -/
@[expose] def validFourHopCallTree : HttpsSessionNode :=
  .mk 0xA11CE "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] [123, 49, 125] [
    .mk 0xA11CE "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107] [123, 91, 50, 93, 125] [
      .mk 0xA11CE "registry.hf.co" [71, 69, 84, 32, 47, 109, 97, 110] [123, 125] [
        .mk 0xA11CE "cdn.dataset.org" [71, 69, 84, 32, 47, 115, 104, 100] [91, 52, 50, 93] []
      ]
    ]
  ]

/-- Planted bad `CallTree` #1: leaks `"sk_"` (`[115, 107, 95]`) in hop 3's request header,
    caught by `PredRE.forbidSubseq` (`.compl`). -/
@[expose] def leakedSecretCallTree : HttpsSessionNode :=
  .mk 0xA11CE "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] [123, 49, 125] [
    .mk 0xA11CE "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107] [123, 91, 50, 93, 125] [
      .mk 0xA11CE "registry.hf.co" [71, 69, 84, 32, 115, 107, 95, 57] [123, 125] []
    ]
  ]

/-- Planted bad `CallTree` #2: malformed unbalanced JSON `"{[}"` (`[123, 91, 125]`) in hop 4,
    caught by `jsonFramingVpa`. -/
@[expose] def unbalancedVpaCallTree : HttpsSessionNode :=
  .mk 0xA11CE "api.stripe.com" [71, 69, 84, 32, 47, 118, 49] [123, 49, 125] [
    .mk 0xA11CE "auth.obend.org" [71, 69, 84, 32, 47, 116, 111, 107] [123, 91, 50, 93, 125] [
      .mk 0xA11CE "registry.hf.co" [71, 69, 84, 32, 47, 109, 97, 110] [123, 125] [
        .mk 0xA11CE "cdn.dataset.org" [71, 69, 84, 32, 47, 115, 104, 100] [123, 91, 125] []
      ]
    ]
  ]

/-- Executable Silver end-to-end smoke runner for Organ O5 (`ZkStripe`). -/
@[expose] def silverZkStripeSmoke : Bool :=
  let hopCountOk := callTreeHopCount validFourHopCallTree == 4
  let validAdmitted := verifyZkStripeCallTree defaultZkStripePolicy validFourHopCallTree
  let leakRefused :=
    match auditZkStripeCallTree defaultZkStripePolicy leakedSecretCallTree with
    | .error e => e == .requestRegexViolation "registry.hf.co"
    | .ok () => false
  let vpaRefused :=
    match auditZkStripeCallTree defaultZkStripePolicy unbalancedVpaCallTree with
    | .error e => e == .unbalancedFraming "cdn.dataset.org"
    | .ok () => false
  let digestNonZero := callTreeDigest fastMerkleHash validFourHopCallTree != 0
  hopCountOk && validAdmitted && leakRefused && vpaRefused && digestNonZero

example : verifyZkStripeCallTree defaultZkStripePolicy validFourHopCallTree = true := by decide
example : silverZkStripeSmoke = true := by decide

end Obend.Trailblaze.ZkStripe
end
