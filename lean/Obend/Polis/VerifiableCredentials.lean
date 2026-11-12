module
/-
# Credential evaluation and transparent Dual-PCS receipts
Full-width fact identities, canonical witness encoding, semantic verification under a
verifier-owned policy, and statement/witness-bound compliance tables. Receipts disclose
witness data; this module does not claim zero knowledge.
-/
public import Obend.Polis.ZkBiscuit
public import Obend.Vault.Lsafe
public import Obend.SymbolicZk.LinMem
public import Obend.SymbolicZk.RankedFixpointArith
public import Obend.Crypto.DualSpine
public import Obend.SymbolicZk.CompileToPiop
import all Obend.SymbolicZk.CompileToPiop
import all Obend.SymbolicZk.CompileToPiopCore
import all Obend.SymbolicZk.RankedFixpointArith
import all Obend.Vault.Lsafe
import all Obend.Crypto.Multilinear
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.DualSpine

public section
namespace Obend.Polis.VerifiableCredentials

open Obend.Crypto
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Codec.DetCbor
open Obend.Vault.Lsafe
open Obend.SymbolicZk
open Obend.SymbolicZk.Ranked
open Obend.Judge.Computational (HashCollisionWitness SISShortVecWitness)

set_option autoImplicit false

/-! ## 1. The credential commitment -/

/-- What an issuer states about a subject. `attributes` is the machine-readable claim,
`evidence` the JSON document a disclosure redacts, `lineage` the provenance digest of the
capability chain the credential was issued under. -/
structure IssuerCredential where
  issuer : ByteArray
  subject : ByteArray
  schema : ByteArray
  attributes : CborVal
  evidence : ByteArray
  lineage : ByteArray
  epoch : Nat
  width : WithinWidth attributes = true

/-- A natural number as a field: its LEB128 bytes. -/
def natField (n : Nat) : ByteArray := Native.bytesOfList (leb128 n)

theorem natField_injective (a b : Nat) (h : natField a = natField b) : a = b := by
  have hh := congrArg (fun x : ByteArray => x.data.toList) h
  simp only [natField, Native.bytesOfList_toList] at hh
  exact (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using hh)).1

/-- The bytes committed to: three nested frames over all seven fields. -/
def credentialPayload (c : IssuerCredential) : ByteArray :=
  encodeFrame (encodeFrame c.issuer c.subject c.schema)
    (encodeFrame (encodeDetCbor c.attributes) c.evidence c.lineage)
    (natField c.epoch)

/-- **The payload determines the credential.** No field is outside a frame, and the attribute
value is recovered by `encodeDetCbor_injective`. -/
theorem credentialPayload_injective (c₁ c₂ : IssuerCredential)
    (h₁ : WithinWidth c₁.attributes = true) (h₂ : WithinWidth c₂.attributes = true)
    (h : credentialPayload c₁ = credentialPayload c₂) : c₁ = c₂ := by
  obtain ⟨i₁, s₁, k₁, a₁, e₁, l₁, n₁, ca₁⟩ := c₁
  obtain ⟨i₂, s₂, k₂, a₂, e₂, l₂, n₂, ca₂⟩ := c₂
  simp only [credentialPayload] at h
  obtain ⟨ha, hb, hc⟩ := encodeFrame_injective h
  obtain ⟨h1, h2, h3⟩ := encodeFrame_injective ha
  obtain ⟨h4, h5, h6⟩ := encodeFrame_injective hb
  have h7 := natField_injective _ _ hc
  have h8 := encodeDetCbor_injective a₁ a₂ h₁ h₂ h4
  subst h1 h2 h3 h5 h6 h7 h8
  rfl

/-- Customization string of the credential commitment. -/
def credentialCustomization : List UInt8 := "OBEND.POLIS.CREDENTIAL/v1".toUTF8.data.toList

/-- The hash a credential commitment is a collision of when it fails to bind. -/
def credentialHash : Hash := cshake256Bytes credentialCustomization

/-- **The issuer's commitment**: 32 bytes of cSHAKE256 over the framed payload. -/
def credentialCommitment (c : IssuerCredential) : ByteArray :=
  cshake32ByteArray credentialCustomization (credentialPayload c).data.toList

theorem credentialCommitment_size (c : IssuerCredential) : (credentialCommitment c).size = 32 :=
  cshake32ByteArray_size _ _

/-- **The binding extractor.** Two credentials with one commitment are equal, or their two
payloads are a collision of `credentialHash`, returned as data. -/
def credentialCommitmentExtract (c₁ c₂ : IssuerCredential)
    (h₁ : WithinWidth c₁.attributes = true) (h₂ : WithinWidth c₂.attributes = true)
    (h : credentialCommitment c₁ = credentialCommitment c₂) :
    PSum (c₁ = c₂)
      (HashCollisionWitness credentialHash
        (Nat.max (credentialPayload c₁).data.toList.length
          (credentialPayload c₂).data.toList.length)) :=
  if hp : (credentialPayload c₁).data.toList = (credentialPayload c₂).data.toList then
    .inl (credentialPayload_injective c₁ c₂ h₁ h₂ (byteArray_eq_of_toList_eq hp))
  else
    .inr
      { msgA := (credentialPayload c₁).data.toList
        msgB := (credentialPayload c₂).data.toList
        lenA := Nat.le_max_left _ _
        lenB := Nat.le_max_right _ _
        distinct := hp
        sameDigest := by
          have hl := congrArg (fun b : ByteArray => b.data.toList) h
          simp only [credentialCommitment, cshake32ByteArray, Native.bytesOfList_toList] at hl
          exact congrArg ofBE hl }

/-- **Commitment binding.** Equal commitments come from equal credentials, or the two payloads
are a named collision. -/
theorem credentialCommitment_binding (c₁ c₂ : IssuerCredential)
    (h₁ : WithinWidth c₁.attributes = true) (h₂ : WithinWidth c₂.attributes = true)
    (h : credentialCommitment c₁ = credentialCommitment c₂) :
    c₁ = c₂ ∨ CollisionAmong credentialHash (fun x =>
      x = (credentialPayload c₁).data.toList ∨ x = (credentialPayload c₂).data.toList) :=
  by
    rcases cshake32_binds credentialCustomization h with hp | hc
    · exact .inl (credentialPayload_injective c₁ c₂ h₁ h₂ (byteArray_eq_of_toList_eq hp))
    · exact .inr hc

/-! ## 2. The evaluation relation -/

/-- A status policy: rules with negation over numbered atoms, the atom that must hold, the rights
the capability chain must carry, the predicate under which the issuer publishes status facts
about a subject, and the authenticator its completeness tokens are tagged with. -/
structure StatusPolicy where
  program : ArithProgram
  goal : Nat
  need : UInt64
  statusPred : UInt64
  issuerAuth : ByteArray
  factAtoms : Array ByteArray := #[]

/-- What crosses the boundary: the commitments and the redacted document. -/
structure DisclosureView where
  credentialDigest : ByteArray
  revokedRoot : RevokedRoot
  graphDigest : ByteArray
  disclosed : ByteArray

/-- What stays with the holder. -/
structure CredentialWitness where
  credential : IssuerCredential
  grant : Block
  hops : Array Block
  revoked : RevokedSet
  edges : Array KgEdge
  token : CompletenessToken
  memory : LinMemTrace
  modelTrue : Array Bool
  modelUpper : Array Bool
  cert : ArrayCert
  spanStart : Nat
  spanEnd : Nat
  replacement : ByteArray

/-- A full-width fact identity. All three fields are length-framed before hashing. -/
def factAtomPreimage (e : KgEdge) : List UInt8 :=
  encodeListField (be 8 e.predId.toNat) ++ encodeListField e.subj.data.toList ++
    encodeListField e.obj.data.toList

def factAtom (e : KgEdge) : ByteArray :=
  cshake32ByteArray "OBEND.POLIS.FACT_ATOM/v1".toUTF8.data.toList (factAtomPreimage e)

theorem factAtom_size (e : KgEdge) : (factAtom e).size = 32 := cshake32ByteArray_size _ _

theorem factAtom_binds (a b : KgEdge) (h : factAtom a = factAtom b) :
    a = b ∨ CollisionAmong (cshake256Bytes "OBEND.POLIS.FACT_ATOM/v1".toUTF8.data.toList)
      (fun x => x = factAtomPreimage a ∨ x = factAtomPreimage b) := by
  rcases cshake32_binds "OBEND.POLIS.FACT_ATOM/v1".toUTF8.data.toList h with hp | hc
  · simp only [factAtomPreimage, List.append_assoc] at hp
    obtain ⟨hp, hs⟩ := encodeListField_prefix_inj hp
    obtain ⟨hs, ho⟩ := encodeListField_prefix_inj hs
    have ho := (encodeListField_prefix_inj (r₁ := []) (r₂ := []) (by simpa using ho)).1
    have he : a.predId = b.predId := UInt64.toNat_inj.mp
      (be_injective (by have := a.predId.toNat_lt; exact this)
        (by have := b.predId.toNat_lt; exact this) hp)
    apply Or.inl
    have hs' := byteArray_eq_of_toList_eq hs
    have ho' := byteArray_eq_of_toList_eq ho
    cases a; cases b
    simp_all
  · exact .inr hc

/-- Dense model indices name a verifier-provided dictionary of full-width fact identities.
They are indices, never truncated digests. Unknown facts are rejected by `checkFactNames`. -/
def factIndex (pol : StatusPolicy) (e : KgEdge) : UInt64 :=
  UInt64.ofNat (pol.factAtoms.toList.idxOf (factAtom e))

def checkFactNames (pol : StatusPolicy) (w : CredentialWitness) : Bool :=
  decide (pol.factAtoms.size < 2 ^ 64) &&
    w.edges.all (fun e => pol.factAtoms.contains (factAtom e))

/-- The facts a trace read, in the order it read them. -/
def loadedFacts (tr : LinMemTrace) : List UInt64 :=
  (tr.consumed.toList.map ConsumedEvent.cell).map LinCell.payload

/-- A fact is a rule with an empty body. -/
def factRule (a : UInt64) : ArithRule := ⟨a.toNat, #[], #[]⟩

/-- The program evaluated: the policy's rules, then one fact rule per fact read. -/
def evalProgram (pol : StatusPolicy) (tr : LinMemTrace) : ArithProgram :=
  ⟨pol.program.numAtoms, pol.program.rules ++ ((loadedFacts tr).map factRule).toArray⟩

/-- The three-valued reading of a well-founded model: true, undefined, false. A caveat over an
undefined atom is not accepted. -/
def kleeneEnv (t u : Array Bool) (a : Nat) : KleenePred3 :=
  if bit t a then .true3 else if bit u a then .unbound3 else .false3

/-- The credential opens the public digest. -/
def checkBinding (pub : DisclosureView) (w : CredentialWitness) : Bool :=
  decide (credentialCommitment w.credential = pub.credentialDigest) &&
    WithinWidth w.credential.attributes

/-- The capability chain folds under the committed revoked set, carries the needed rights with
its caveats true in the model, and is the chain the credential names. -/
def checkChain (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) : Bool :=
  decide (w.revoked.root = pub.revokedRoot) &&
    match foldChain w.revoked (kleeneEnv w.modelTrue w.modelUpper) w.grant w.hops with
    | none => false
    | some acc => authorize acc pol.need && decide (acc.lineage = w.credential.lineage)

/-- The facts are the issuer's complete slice for this subject, and the memory trace read each
of them once: they are its initial cells, it produced none, and none is left. -/
def checkFacts (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) : Bool :=
  verifyCompletenessToken cshakeHasher pub.graphDigest pol.issuerAuth pol.statusPred
      w.credential.subject w.edges w.token &&
    verifyLinMemExec w.memory && decide (w.memory.produced.size = 0) &&
    decide (w.memory.finalCells.size = 0) &&
    decide (w.memory.init.toList.map LinCell.payload = w.edges.toList.map (factIndex pol)) &&
    checkFactNames pol w

/-- The model is the well-founded model of the policy over the facts read, and the goal holds. -/
def checkModel (pol : StatusPolicy) (w : CredentialWitness) : Bool :=
  checkRankedWFS (evalProgram pol w.memory) w.modelTrue w.modelUpper w.cert &&
    bit w.modelTrue pol.goal

/-- The disclosed document is the evidence with one safely redacted span. -/
def checkDisclosure (pub : DisclosureView) (w : CredentialWitness) : Bool :=
  checkLsafeRedaction w.credential.evidence w.spanStart w.spanEnd w.replacement &&
    decide (pub.disclosed =
      spliceByteArray w.credential.evidence w.spanStart w.spanEnd w.replacement)

/-- **The evaluation relation.** -/
def checkCredentialEval (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) :
    Bool :=
  checkBinding pub w && checkChain pol pub w && checkFacts pol pub w && checkModel pol w &&
    checkDisclosure pub w

/-- The specification tier of an accepted evaluation. -/
structure CompliantEvaluation (pol : StatusPolicy) (pub : DisclosureView)
    (w : CredentialWitness) : Prop where
  bound : credentialCommitment w.credential = pub.credentialDigest
  width : WithinWidth w.credential.attributes = true
  revokedBound : w.revoked.root = pub.revokedRoot
  chain : ∃ acc, foldChain w.revoked (kleeneEnv w.modelTrue w.modelUpper) w.grant w.hops =
      some acc ∧ authorize acc pol.need = true ∧ acc.lineage = w.credential.lineage
  token : verifyCompletenessToken cshakeHasher pub.graphDigest pol.issuerAuth pol.statusPred
      w.credential.subject w.edges w.token = true
  memory : LinMemSpec w.memory
  noProduced : w.memory.produced.size = 0
  noResidue : w.memory.finalCells.size = 0
  initFacts : w.memory.init.toList.map LinCell.payload = w.edges.toList.map (factIndex pol)
  factNames : checkFactNames pol w = true
  modelTrue : Obend.Reasons.Same (decodeBits w.modelTrue)
      (Obend.Reasons.wf (toReasonsProgram (evalProgram pol w.memory))).1
  modelUpper : Obend.Reasons.Same (decodeBits w.modelUpper)
      (Obend.Reasons.wf (toReasonsProgram (evalProgram pol w.memory))).2
  goal : bit w.modelTrue pol.goal = true
  redaction : checkLsafeRedaction w.credential.evidence w.spanStart w.spanEnd w.replacement = true
  disclosed : pub.disclosed =
      spliceByteArray w.credential.evidence w.spanStart w.spanEnd w.replacement

theorem checkChain_iff (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) :
    checkChain pol pub w = true ↔
      w.revoked.root = pub.revokedRoot ∧
      ∃ acc, foldChain w.revoked (kleeneEnv w.modelTrue w.modelUpper) w.grant w.hops = some acc ∧
        authorize acc pol.need = true ∧ acc.lineage = w.credential.lineage := by
  unfold checkChain
  cases foldChain w.revoked (kleeneEnv w.modelTrue w.modelUpper) w.grant w.hops with
  | none => simp
  | some acc => simp

/-- **An accepted evaluation is compliant.** The accepted model is the well-founded model of the
policy over exactly the facts the trace read; the trace is a valid linear memory over the
issuer's complete slice; the chain folds, authorizes and is the credential's; the credential
opens the digest; the redaction is confined. -/
theorem stratified_credential_eval_sound (pol : StatusPolicy) (pub : DisclosureView)
    (w : CredentialWitness) (h : checkCredentialEval pol pub w = true) :
    CompliantEvaluation pol pub w := by
  simp only [checkCredentialEval, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hb, hc⟩, hf⟩, hm⟩, hd⟩ := h
  simp only [checkBinding, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hrev, hchain⟩ := (checkChain_iff pol pub w).mp hc
  simp only [checkFacts, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨htok, hlin⟩, hprod⟩, hfin⟩, hinit⟩, hnames⟩ := hf
  simp only [checkModel, Bool.and_eq_true] at hm
  obtain ⟨hmodelT, hmodelU⟩ := checkRankedWFS_sound hm.1
  simp only [checkDisclosure, Bool.and_eq_true, decide_eq_true_eq] at hd
  exact ⟨hb.1, hb.2, hrev, hchain, htok, (verifyLinMemExec_iff_spec _).mp hlin, hprod, hfin,
    hinit, hnames, hmodelT, hmodelU, hm.2, hd.1, hd.2⟩

/-- **Every compliant evaluation is accepted**, with some rank certificate for its model. -/
theorem checkCredentialEval_complete (pol : StatusPolicy) (pub : DisclosureView)
    (w : CredentialWitness) (hc : CompliantEvaluation pol pub w)
    (hw : WFProgram (evalProgram pol w.memory) = true)
    (ht : w.modelTrue.size = pol.program.numAtoms)
    (hu : w.modelUpper.size = pol.program.numAtoms) :
    ∃ cert, checkCredentialEval pol pub { w with cert := cert } = true := by
  obtain ⟨cert, hcert⟩ := checkRankedWFS_complete (evalProgram pol w.memory) w.modelTrue
    w.modelUpper hw ht hu ⟨hc.modelTrue, hc.modelUpper⟩
  refine ⟨cert, ?_⟩
  have hchain : checkChain pol pub { w with cert := cert } = true :=
    (checkChain_iff pol pub _).mpr ⟨hc.revokedBound, hc.chain⟩
  simp only [checkCredentialEval, hchain, Bool.and_eq_true, checkBinding, checkFacts, checkModel,
    checkDisclosure, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hc.bound, hc.width⟩, trivial⟩,
    ⟨⟨⟨⟨⟨hc.token, (verifyLinMemExec_iff_spec _).mpr hc.memory⟩, hc.noProduced⟩, hc.noResidue⟩,
      hc.initFacts⟩, hc.factNames⟩⟩, ⟨hcert, hc.goal⟩⟩, ⟨hc.redaction, hc.disclosed⟩⟩

/-! ### Non-omission -/

/-- The facts read are the committed facts, each as often as it was committed: no fact dropped,
none invented. -/
theorem loadedFacts_perm {pol : StatusPolicy} {pub : DisclosureView} {w : CredentialWitness}
    (h : CompliantEvaluation pol pub w) :
    (w.edges.toList.map (factIndex pol)).Perm (loadedFacts w.memory) := by
  have hp : (w.memory.init.toList ++ w.memory.produced.toList).Perm
      (w.memory.consumed.toList.map ConsumedEvent.cell ++ w.memory.finalCells.toList) :=
    h.memory.2.2
  have hprod : w.memory.produced.toList = [] :=
    List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact h.noProduced)
  have hfin : w.memory.finalCells.toList = [] :=
    List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact h.noResidue)
  rw [hprod, hfin, List.append_nil, List.append_nil] at hp
  have := hp.map LinCell.payload
  rw [h.initFacts] at this
  exact this

theorem factRule_mem_evalProgram (pol : StatusPolicy) (tr : LinMemTrace) (a : UInt64)
    (ha : a ∈ loadedFacts tr) : factRule a ∈ (evalProgram pol tr).rules := by
  simp only [evalProgram, Array.mem_append, List.mem_toArray, List.mem_map]
  exact .inr ⟨a, ha, rfl⟩

/-- What the rank checker's closure and support passes give at one atom. -/
theorem checkRankedWFS_atom {p : ArithProgram} {t u : Array Bool} {c : ArrayCert}
    (h : checkRankedWFS p t u c = true) :
    (∀ r ∈ p.rules, r.pos.size = 0 → r.neg.size = 0 → bit t r.head = true) ∧
    (∀ a, bit t a = true → bit u a = true ∧
      ∃ r ∈ p.rules, r.head = a ∧ (∀ b ∈ r.pos, bit t b = true) ∧
        ∀ d ∈ r.neg, bit u d = false) := by
  simp only [checkRankedWFS, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, ht, _, _, _, _, _, _, _, ha, _, hc⟩ := h
  refine ⟨fun r hr hpos hneg => ?_, fun a hta => ?_⟩
  · have hcl := Array.all_eq_true_iff_forall_mem.mp hc r hr
    have hp : r.pos = #[] := Array.eq_empty_of_size_eq_zero hpos
    have hn : r.neg = #[] := Array.eq_empty_of_size_eq_zero hneg
    simpa [firesFast, hp, hn] using hcl
  · have hlt : a < p.numAtoms := by
      rw [← ht]
      by_cases hn : a < t.size
      · exact hn
      · simp [bit, Array.getElem?_eq_none (xs := t) (i := a) (by omega)] at hta
    have hrow := Array.all_eq_true_iff_forall_mem.mp ha a (by simpa using hlt)
    simp only [hta, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hrow
    obtain ⟨⟨hua, hsup⟩, _⟩ := hrow
    refine ⟨hua, ?_⟩
    unfold checkTrueSupport at hsup
    split at hsup
    · cases hsup
    · rename_i r he
      simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hsup
      exact ⟨r, Array.mem_of_getElem? he, hsup.1.1, fun b hb => (hsup.1.2 b hb).1,
        fun d hd => (hsup.2 d hd).1⟩

/-- **No negative is forged by omission.** In an accepted evaluation every committed fact is true
in the model, and every true atom has a rule with that head whose positive body is true and none
of whose negated atoms is true, undefined, or a committed fact. A prover who leaves out a
revocation fact to derive what it blocks has no accepted evaluation. -/
theorem no_forged_negative_by_omission (pol : StatusPolicy) (pub : DisclosureView)
    (w : CredentialWitness) (h : checkCredentialEval pol pub w = true) :
    (∀ e ∈ w.edges.toList, bit w.modelTrue (factIndex pol e).toNat = true) ∧
    ∀ head, bit w.modelTrue head = true →
      ∃ r ∈ (evalProgram pol w.memory).rules, r.head = head ∧
        (∀ b ∈ r.pos, bit w.modelTrue b = true) ∧
        ∀ d ∈ r.neg, bit w.modelUpper d = false ∧
          ∀ e ∈ w.edges.toList, (factIndex pol e).toNat ≠ d := by
  have hc := stratified_credential_eval_sound pol pub w h
  simp only [checkCredentialEval, Bool.and_eq_true, checkModel] at h
  obtain ⟨hfacts, hatoms⟩ := checkRankedWFS_atom h.1.2.1
  have hedge : ∀ e ∈ w.edges.toList, bit w.modelTrue (factIndex pol e).toNat = true := by
    intro e he
    have hmem : factIndex pol e ∈ loadedFacts w.memory :=
      (loadedFacts_perm hc).mem_iff.mp (List.mem_map.mpr ⟨e, he, rfl⟩)
    exact hfacts (factRule (factIndex pol e)) (factRule_mem_evalProgram pol w.memory _ hmem) rfl rfl
  refine ⟨hedge, fun head hhead => ?_⟩
  obtain ⟨_, r, hr, hrh, hpos, hneg⟩ := hatoms head hhead
  refine ⟨r, hr, hrh, hpos, fun d hd => ⟨hneg d hd, fun e he hed => ?_⟩⟩
  have hu := (hatoms _ (hedge e he)).1
  rw [hed, hneg d hd] at hu
  cases hu

/-- **A committed revocation refuses the goal.** If every rule for the goal negates atom `d` and
`d` is among the committed facts, no evaluation is accepted. -/
theorem revoked_fact_refuses_goal (pol : StatusPolicy) (pub : DisclosureView)
    (w : CredentialWitness) (d : Nat)
    (hguard : ∀ r ∈ (evalProgram pol w.memory).rules, r.head = pol.goal → d ∈ r.neg)
    (e : KgEdge) (he : e ∈ w.edges.toList) (hed : (factIndex pol e).toNat = d) :
    checkCredentialEval pol pub w = false := by
  cases h : checkCredentialEval pol pub w with
  | false => rfl
  | true =>
    obtain ⟨_, hsup⟩ := no_forged_negative_by_omission pol pub w h
    have hgoal : bit w.modelTrue pol.goal = true := by
      simp only [checkCredentialEval, Bool.and_eq_true, checkModel] at h
      exact h.1.2.2
    obtain ⟨r, hr, hrh, _, hneg⟩ := hsup pol.goal hgoal
    exact absurd hed ((hneg d (hguard r hr hrh)).2 e he)

/-- The slice an accepted evaluation presents has the digest its token names. -/
theorem accepted_slice_digest (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness)
    (h : checkCredentialEval pol pub w = true) :
    edgesDigest cshakeHasher w.edges = w.token.scopedEdgesDigest32 :=
  (verifyCompletenessToken_parts (stratified_credential_eval_sound pol pub w h).token).2.2.2.2.2.2

/-- **The presented slice is the issuer's.** Against a slice with the same commitment (by
`accepted_slice_digest`, any slice the issuer committed to in the token), the witness's facts are
that slice, or the two are a collision of the slice commitment, returned as data. -/
def issuerSliceExtract (edges authentic : Array KgEdge)
    (hdig : edgesDigest cshakeHasher edges = edgesDigest cshakeHasher authentic)
    (h₁ : WithinWidth (edgesCbor edges) = true) (h₂ : WithinWidth (edgesCbor authentic) = true) :
    PSum (edges = authentic) (HashCollision cshakeHasher graphTag) :=
  if he : edges = authentic then .inl he
  else .inr (edgesCollision cshakeHasher he h₁ h₂ hdig)

/-! ### Redaction confinement -/

/-- **Non-interference across the redaction boundary.** Two accepted evaluations with one
replacement, whose evidence documents agree before the span and after it, disclose
byte-identical documents. Both evidence documents then have the final machine state of the
disclosed one, hence the same object key sets: the secrets differ only inside one value string.
The disclosed document passes the skeleton check. -/
theorem disclosure_noninterference (pol : StatusPolicy) (pub₁ pub₂ : DisclosureView)
    (w₁ w₂ : CredentialWitness)
    (h₁ : checkCredentialEval pol pub₁ w₁ = true) (h₂ : checkCredentialEval pol pub₂ w₂ = true)
    (hrep : w₁.replacement = w₂.replacement)
    (hpre : w₁.credential.evidence.data.toList.take w₁.spanStart =
      w₂.credential.evidence.data.toList.take w₂.spanStart)
    (hpost : w₁.credential.evidence.data.toList.drop w₁.spanEnd =
      w₂.credential.evidence.data.toList.drop w₂.spanEnd) :
    pub₁.disclosed = pub₂.disclosed ∧
      lsafeRun w₁.credential.evidence = lsafeRun w₂.credential.evidence ∧
      objectKeysOf pub₁.disclosed = objectKeysOf w₁.credential.evidence ∧
      objectKeysOf pub₂.disclosed = objectKeysOf w₂.credential.evidence ∧
      runLsafeVpa pub₁.disclosed = true := by
  have c₁ := stratified_credential_eval_sound pol pub₁ w₁ h₁
  have c₂ := stratified_credential_eval_sound pol pub₂ w₂ h₂
  obtain ⟨hv₁, _, _, _, hk₁, hr₁⟩ := lsafe_redaction_confinement c₁.redaction
  obtain ⟨_, _, _, _, hk₂, hr₂⟩ := lsafe_redaction_confinement c₂.redaction
  have heq : pub₁.disclosed = pub₂.disclosed := by
    rw [c₁.disclosed, c₂.disclosed]
    apply byteArray_eq_of_toList_eq
    rw [spliceByteArray_toList, spliceByteArray_toList, hpre, hpost, hrep]
  refine ⟨heq, ?_, ?_, ?_, ?_⟩
  · rw [← hr₁, ← hr₂, ← c₁.disclosed, ← c₂.disclosed, heq]
  · rw [c₁.disclosed]; exact hk₁
  · rw [c₂.disclosed]; exact hk₂
  · rw [c₁.disclosed]; exact hv₁

/-- Read one LEB128 number from the front of a byte list. -/
def unleb128 : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else
      match unleb128 rest with
      | none => none
      | some (hi, rest') => some (b.toNat - 128 + 128 * hi, rest')

theorem unleb128_leb128Aux : ∀ (fuel v : Nat) (rest : List UInt8), v ≤ fuel →
    unleb128 (leb128Aux fuel v ++ rest) = some (v, rest)
  | 0, v, rest, hv => by
    have h0 : v = 0 := by omega
    subst h0
    simp [leb128Aux, unleb128]
  | fuel + 1, v, rest, hv => by
    by_cases hlt : v < 128
    · simp [leb128Aux, unleb128, hlt, uint8_toNat_lt_256_of_lt (show v < 256 by omega)]
    · have hb : (UInt8.ofNat (128 + v % 128)).toNat = 128 + v % 128 :=
        uint8_toNat_lt_256_of_lt (by omega)
      have ih := unleb128_leb128Aux fuel (v / 128) rest (by omega)
      simp only [leb128Aux, hlt, ↓reduceIte, List.cons_append, unleb128, hb, ih]
      have hnot : ¬ 128 + v % 128 < 128 := by omega
      simp only [hnot, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, and_true]
      omega

/-- A byte codec: `dec` reads one value from the front of a byte list and returns what follows.
The round trip holds for every value and every continuation, with no width side condition. -/
structure Codec (α : Type) where
  enc : α → List UInt8
  dec : List UInt8 → Option (α × List UInt8)
  dec_enc : ∀ (a : α) (rest : List UInt8), dec (enc a ++ rest) = some (a, rest)

namespace Codec

def nat : Codec Nat :=
  ⟨leb128, unleb128, fun n rest => unleb128_leb128Aux n n rest (Nat.le_refl n)⟩

def pair {α β : Type} (ca : Codec α) (cb : Codec β) : Codec (α × β) where
  enc p := ca.enc p.1 ++ cb.enc p.2
  dec bs :=
    match ca.dec bs with
    | none => none
    | some (a, r) =>
      match cb.dec r with
      | none => none
      | some (b, r') => some ((a, b), r')
  dec_enc p rest := by simp [List.append_assoc, ca.dec_enc, cb.dec_enc]

/-- Read exactly `n` values. -/
def decodeMany {α : Type} (dec : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match dec bs with
    | none => none
    | some (a, r) =>
      match decodeMany dec n r with
      | none => none
      | some (as, r') => some (a :: as, r')

theorem decodeMany_enc {α : Type} (c : Codec α) : ∀ (l : List α) (rest : List UInt8),
    decodeMany c.dec l.length (l.flatMap c.enc ++ rest) = some (l, rest)
  | [], rest => rfl
  | a :: l, rest => by
    simp [decodeMany, List.append_assoc, c.dec_enc, decodeMany_enc c l rest]

/-- A list: its length, then its elements. -/
def list {α : Type} (c : Codec α) : Codec (List α) where
  enc l := leb128 l.length ++ l.flatMap c.enc
  dec bs :=
    match unleb128 bs with
    | none => none
    | some (n, r) => decodeMany c.dec n r
  dec_enc l rest := by
    simp [List.append_assoc, unleb128_leb128Aux l.length l.length _ (Nat.le_refl _), leb128,
      decodeMany_enc c l rest]

/-- Carry a codec along a partial map with a section. -/
def refine {α β : Type} (c : Codec α) (down : α → Option β) (up : β → α)
    (h : ∀ b, down (up b) = some b) : Codec β where
  enc b := c.enc (up b)
  dec bs :=
    match c.dec bs with
    | none => none
    | some (a, r) =>
      match down a with
      | none => none
      | some b => some (b, r)
  dec_enc b rest := by simp [c.dec_enc, h]

def byte : Codec UInt8 :=
  nat.refine (fun n => if n < 256 then some (UInt8.ofNat n) else none) UInt8.toNat
    (fun b => by simp [UInt8.toNat_lt_size b, UInt8.ofNat_toNat])

def bytes : Codec ByteArray :=
  (list byte).refine (fun l => some ⟨l.toArray⟩) (fun b => b.data.toList) (fun b => by simp)

def digest32 : Codec Digest32 :=
  bytes.refine (fun b => if h : b.size = 32 then some ⟨b, h⟩ else none) Digest32.bytes
    (fun d => by simp [d.size_eq])

/-- A field element: its canonical representative; a number at or above the prime is refused. -/
def goldilocks : Codec Goldilocks :=
  nat.refine canonicalLift? Goldilocks.val (fun x => by simp [canonicalLift?, x.isLt])

/-- An integer: a sign and a magnitude; negative zero is refused. -/
def int : Codec Int :=
  (pair nat nat).refine
    (fun p => if p.1 = 0 then some (p.2 : Int)
      else if p.1 = 1 ∧ p.2 ≠ 0 then some (-(p.2 : Int)) else none)
    (fun z => (if z < 0 then 1 else 0, z.natAbs))
    (fun z => by
      by_cases hz : z < 0
      · have hne : z.natAbs ≠ 0 := by omega
        simp only [hz, ↓reduceIte, Nat.one_ne_zero, hne, ne_eq, not_false_eq_true, and_self,
          Option.some.injEq]
        omega
      · simp only [hz, ↓reduceIte, Option.some.injEq]
        omega)

end Codec


namespace Codec

def bool : Codec Bool := nat.refine
  (fun n => if n = 0 then some false else if n = 1 then some true else none)
  (fun b => if b then 1 else 0) (fun b => by cases b <;> rfl)
def u64 : Codec UInt64 := nat.refine
  (fun n => if n < 2 ^ 64 then some (UInt64.ofNat n) else none)
  UInt64.toNat (fun n => by simp [n.toNat_lt])
def array {α : Type} (c : Codec α) : Codec (Array α) :=
  (list c).refine (fun l => some l.toArray) Array.toList (fun a => by simp)
/-- The structural codec preserves all width-bounded CBOR values, including raw text
bytes. UTF-8 validation is not part of a computational extractor's carrier. -/
def cbor : Codec {v : CborVal // WithinWidth v = true} := (list byte).refine
  (fun bs => match decSpecAt (fun _ => true) false bs.length bs with
    | some (v, []) => if h : WithinWidth v = true then some ⟨v, h⟩ else none
    | _ => none)
  (fun v => encSpec v.val)
  (fun v => by
    have hv := decSpecAt_enc (fun _ => true) false (encSpec v.val).length v.val []
      (Nat.le_refl _) v.property
    simp only [List.append_nil] at hv
    simp only [hv, v.property, dite_true])

end Codec

def caveatTokens : Caveat → List (Nat × Nat)
  | .atom v => [(0, v)]
  | .const b => [(1, if b then 1 else 0)]
  | .and a b => caveatTokens a ++ caveatTokens b ++ [(2, 0)]
  | .or a b => caveatTokens a ++ caveatTokens b ++ [(3, 0)]
  | .not a => caveatTokens a ++ [(4, 0)]

def caveatTokenStep (stack : Option (List Caveat)) (token : Nat × Nat) : Option (List Caveat) := do
  let stack ← stack
  match token, stack with
  | (0, v), ss => some (.atom v :: ss)
  | (1, 0), ss => some (.const false :: ss)
  | (1, 1), ss => some (.const true :: ss)
  | (2, 0), b :: a :: ss => some (.and a b :: ss)
  | (3, 0), b :: a :: ss => some (.or a b :: ss)
  | (4, 0), a :: ss => some (.not a :: ss)
  | _, _ => none

theorem caveatTokens_roundtrip (c : Caveat) (stack : List Caveat) :
    (caveatTokens c).foldl caveatTokenStep (some stack) = some (c :: stack) := by
  induction c generalizing stack with
  | atom _ => rfl
  | const b => cases b <;> rfl
  | and a b ha hb => simp [caveatTokens, List.foldl_append, ha, hb, caveatTokenStep]
  | or a b ha hb => simp [caveatTokens, List.foldl_append, ha, hb, caveatTokenStep]
  | not a ha => simp [caveatTokens, List.foldl_append, ha, caveatTokenStep]

def caveatCodec : Codec Caveat := (Codec.list (Codec.pair Codec.nat Codec.nat)).refine
  (fun tokens => match tokens.foldl caveatTokenStep (some []) with
    | some [c] => some c | _ => none)
  caveatTokens (fun c => by rw [caveatTokens_roundtrip])

def revokedCodec : Codec RevokedSet := (Codec.array Codec.nat).refine
  (fun keys => if h : keys.toList.Pairwise (· < ·) then some ⟨keys, h⟩ else none)
  RevokedSet.keys (fun r => by simp [r.sorted])

def credentialCodec : Codec IssuerCredential :=
  (Codec.pair Codec.bytes (Codec.pair Codec.bytes (Codec.pair Codec.bytes (Codec.pair Codec.cbor (Codec.pair Codec.bytes (Codec.pair Codec.bytes Codec.nat)))))).refine
    (fun p => some ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1.val, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2, p.2.2.2.1.property⟩)
    (fun v => (v.issuer, v.subject, v.schema, ⟨v.attributes, v.width⟩, v.evidence, v.lineage, v.epoch)) (fun v => by cases v; rfl)

def blockCodec : Codec Block :=
  (Codec.pair Codec.u64 (Codec.pair caveatCodec (Codec.pair Codec.bytes Codec.bytes))).refine
    (fun p => some ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩)
    (fun v => (v.rights, v.caveat, v.holder, v.channel)) (fun v => by cases v; rfl)

def edgeCodec : Codec KgEdge :=
  (Codec.pair Codec.u64 (Codec.pair Codec.bytes Codec.bytes)).refine
    (fun p => some ⟨p.1, p.2.1, p.2.2⟩)
    (fun v => (v.predId, v.subj, v.obj)) (fun v => by cases v; rfl)

def tokenCodec : Codec CompletenessToken :=
  (Codec.pair Codec.bytes (Codec.pair Codec.u64 (Codec.pair Codec.bytes (Codec.pair Codec.bytes Codec.bytes)))).refine
    (fun p => some ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩)
    (fun v => (v.graphDigest32, v.predId, v.subjScope, v.scopedEdgesDigest32, v.issuerTag32)) (fun v => by cases v; rfl)

def linCellCodec : Codec LinCell :=
  (Codec.pair Codec.u64 (Codec.pair Codec.u64 Codec.u64)).refine
    (fun p => some ⟨p.1, p.2.1, p.2.2⟩)
    (fun v => (v.allocId, v.birthStep, v.payload)) (fun v => by cases v; rfl)

def consumedCodec : Codec ConsumedEvent :=
  (Codec.pair linCellCodec Codec.u64).refine
    (fun p => some ⟨p.1, p.2⟩)
    (fun v => (v.cell, v.consumeStep)) (fun v => by cases v; rfl)

def memoryCodec : Codec LinMemTrace :=
  (Codec.pair (Codec.array linCellCodec) (Codec.pair (Codec.array linCellCodec) (Codec.pair (Codec.array consumedCodec) (Codec.array linCellCodec)))).refine
    (fun p => some ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩)
    (fun v => (v.init, v.produced, v.consumed, v.finalCells)) (fun v => by cases v; rfl)

def certCodec : Codec ArrayCert :=
  (Codec.pair (Codec.array Codec.nat) (Codec.pair (Codec.array Codec.nat) (Codec.pair (Codec.array Codec.nat) (Codec.pair (Codec.array Codec.nat) (Codec.pair (Codec.array Codec.nat) (Codec.array (Codec.pair Codec.bool Codec.nat))))))).refine
    (fun p => some ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩)
    (fun v => (v.stage, v.rankT, v.rankU, v.supportT, v.supportU, v.blockers)) (fun v => by cases v; rfl)

def witnessCodec : Codec CredentialWitness :=
  (Codec.pair credentialCodec (Codec.pair blockCodec (Codec.pair (Codec.array blockCodec) (Codec.pair revokedCodec (Codec.pair (Codec.array edgeCodec) (Codec.pair tokenCodec (Codec.pair memoryCodec (Codec.pair (Codec.array Codec.bool) (Codec.pair (Codec.array Codec.bool) (Codec.pair certCodec (Codec.pair Codec.nat (Codec.pair Codec.nat Codec.bytes)))))))))))).refine
    (fun p => some ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    (fun v => (v.credential, v.grant, v.hops, v.revoked, v.edges, v.token, v.memory, v.modelTrue, v.modelUpper, v.cert, v.spanStart, v.spanEnd, v.replacement)) (fun v => by cases v; rfl)

/-! ## 3. Transparent statement- and witness-bound PIOP receipts

The executable verifier receives the witness and checks its relation and canonical table.
This is a transparent PCS realization, not a hiding proof system. The policy, including its
issuer authenticator and full fact dictionary, is supplied by the verifier, never the receipt.
-/
structure ReceiptParams where
  hash : Hash32
  lattice : AjtaiParams
  cols_eq : lattice.cols = 4 * 2 ^ 5

def violationBit (ok : Bool) : Goldilocks := if ok then Goldilocks.zero else Goldilocks.one

/-- Relation checks lower into the shared Before-constraint compiler. -/
def credentialConstraintStmt (bs : List Bool) : CompileToPiop.SymbolicZkStmt :=
  { beforeConstraints := (bs.map fun b => (⟨if b then 0 else 1, 1, 1⟩ : CompileToPiop.BeforeConstraint)).toArray,
    linmemInit := #[], linmemProd := #[], linmemCons := #[], linmemFinal := #[],
    lookupTable := #[], lookupQueries := #[], numVars := 4 }

def credentialConstraintWitness (bs : List Bool) : CompileToPiop.SymbolicZkWitness :=
  ⟨(bs.map fun _ => #[Goldilocks.zero]).toArray, #[]⟩

def tableOfChecks (b₁ b₂ b₃ b₄ b₅ : Bool) : List Goldilocks :=
  CompileToPiop.symbolicResidualVector (credentialConstraintStmt [b₁, b₂, b₃, b₄, b₅])
    (credentialConstraintWitness [b₁, b₂, b₃, b₄, b₅]) Goldilocks.zero Goldilocks.zero

private theorem tableOfChecks_length (b₁ b₂ b₃ b₄ b₅ : Bool) :
    (tableOfChecks b₁ b₂ b₃ b₄ b₅).length = 12 := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> cases b₅ <;> rfl

theorem credentialConstraintStmt_semantics (b₁ b₂ b₃ b₄ b₅ : Bool) :
    CompileToPiop.SymbolicSemanticsValid (credentialConstraintStmt [b₁, b₂, b₃, b₄, b₅])
      (credentialConstraintWitness [b₁, b₂, b₃, b₄, b₅]) ↔ (b₁ && b₂ && b₃ && b₄ && b₅) = true := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> cases b₅ <;>
    simp [CompileToPiop.SymbolicSemanticsValid, credentialConstraintStmt, credentialConstraintWitness]

def policyBytes (pol : StatusPolicy) : ByteArray := Native.bytesOfList
  (encodeListField (leb128 pol.program.numAtoms) ++
   encodeListField (pol.program.rules.toList.flatMap fun r =>
     encodeListField (leb128 r.head) ++ encodeListField ((Codec.array Codec.nat).enc r.pos) ++
     encodeListField ((Codec.array Codec.nat).enc r.neg)) ++
   encodeListField (leb128 pol.goal) ++ encodeListField (be 8 pol.need.toNat) ++
   encodeListField (be 8 pol.statusPred.toNat) ++ encodeListField pol.issuerAuth.data.toList ++
   encodeListField ((Codec.array Codec.bytes).enc pol.factAtoms))

def evaluationBinding (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) : ByteArray :=
  cshake32ByteArray "OBEND.POLIS.VC-EVALUATION/v1".toUTF8.data.toList
    (encodeFrame (policyBytes pol)
      (encodeFrame pub.credentialDigest pub.revokedRoot.bytes (encodeFrame pub.graphDigest pub.disclosed ByteArray.empty))
      (Native.bytesOfList (witnessCodec.enc w))).data.toList

theorem evaluationBinding_size (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) :
    (evaluationBinding pol pub w).size = 32 := cshake32ByteArray_size _ _
attribute [local irreducible] evaluationBinding

def bindingPairs : List Goldilocks → List Goldilocks
  | [] => []
  | x :: xs => x :: CommRingOps.neg x :: bindingPairs xs

/-- Eight 32-bit limbs retain every digest bit without reducing a 64-bit word modulo the field. -/
def bindingWords (digest : ByteArray) : List Goldilocks :=
  (List.range 8).map fun i => Goldilocks.ofNat (ofBE ((digest.data.toList.drop (4 * i)).take 4))

/-- Every witness byte and public field is committed through the full 256-bit binding.
A fixed nonzero row rules out even the all-zero digest corner case. Paired rows sum to zero. -/
def complianceTable (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) : List Goldilocks :=
  tableOfChecks (checkBinding pub w) (checkChain pol pub w) (checkFacts pol pub w)
    (checkModel pol w) (checkDisclosure pub w) ++
  bindingPairs (Goldilocks.one :: bindingWords (evaluationBinding pol pub w)) ++
  List.replicate 2 Goldilocks.zero

private def ringSum : List Goldilocks → Goldilocks
  | [] => CommRingOps.zero
  | x :: xs => CommRingOps.add x (ringSum xs)
private theorem ringSum_append (xs ys : List Goldilocks) :
    ringSum (xs ++ ys) = CommRingOps.add (ringSum xs) (ringSum ys) := by
  induction xs with
  | nil => simp [ringSum, LawfulCommRing.zero_add]
  | cons x xs ih => simp [ringSum, ih, LawfulCommRing.add_assoc]
private theorem ringSum_pairs (xs : List Goldilocks) : ringSum (bindingPairs xs) = CommRingOps.zero := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [bindingPairs, ringSum, ih, LawfulCommRing.add_zero, LawfulCommRing.add_right_neg]
private theorem ringSum_zeros (n : Nat) : ringSum (List.replicate n Goldilocks.zero) = Goldilocks.zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, ringSum, ih]
    exact LawfulCommRing.zero_add _
private theorem innerProd_ones (xs : List Goldilocks) (n : Nat) (h : xs.length ≤ n) :
    innerProd xs (List.replicate n CommRingOps.one) = ringSum xs := by
  induction xs generalizing n with
  | nil => simp [innerProd, ringSum]
  | cons x xs ih =>
    cases n with
    | zero => simp at h
    | succ n => simp [List.replicate_succ, innerProd, ringSum, LawfulCommRing.mul_one, ih n (by simp at h; omega)]
private theorem cubeSum_ringSum (n : Nat) (xs : List Goldilocks) (h : xs.length ≤ 2 ^ n) :
    hypercubeSum n xs = ringSum xs := by
  unfold hypercubeSum
  rw [List.map_const', hypercube_length]
  exact innerProd_ones xs (2 ^ n) h
private theorem bindingPairs_length (xs : List Goldilocks) : (bindingPairs xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [bindingPairs, ih]; omega

theorem complianceTable_length (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) :
    (complianceTable pol pub w).length = 2 ^ 5 := by
  simp only [complianceTable, tableOfChecks_length, List.length_append, bindingPairs_length,
    List.length_cons, bindingWords, List.length_map, List.length_range, List.length_replicate]


set_option maxRecDepth 4096 in
theorem complianceTable_sum_iff (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness) :
    hypercubeSum 5 (complianceTable pol pub w) = Goldilocks.zero ↔ checkCredentialEval pol pub w = true := by
  rw [cubeSum_ringSum 5 _ (Nat.le_of_eq (complianceTable_length pol pub w))]
  simp only [complianceTable, ringSum_append, ringSum_pairs, ringSum_zeros, LawfulCommRing.add_zero]
  unfold checkCredentialEval
  generalize checkBinding pub w = b₁, checkChain pol pub w = b₂, checkFacts pol pub w = b₃,
    checkModel pol w = b₄, checkDisclosure pub w = b₅
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> cases b₅ <;>
    simp only [tableOfChecks, credentialConstraintStmt, credentialConstraintWitness,
      CompileToPiop.symbolicResidualVector, CompileToPiop.beforeResidualList,
      List.toList_toArray, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
      List.append_nil, List.cons_append, List.nil_append, ringSum,
      CompileToPiop.boolBitResidual, CompileToPiop.beforeSlackResidualArray_eq_spec,
      CompileToPiop.beforeSlackResidual, CompileToPiop.packedBitsGoldilocks,
      CompileToPiop.charPolyEvalArray, CompileToPiop.logUpTableEvalArray,
      CompileToPiop.logUpQueryEvalArray, Array.foldr_empty,
      show (#[] : Array Goldilocks).zip (#[] : Array Nat) = #[] from
        Array.zip_eq_empty_iff.mpr (.inl rfl),
      Array.empty_append, LawfulCommRing.sub_self] <;>
    rw [show ∀ x : Goldilocks, (x = Goldilocks.zero ↔ x.val = 0) from
      fun x => ⟨fun h => congrArg Goldilocks.val h, fun h => Goldilocks.ext h⟩] <;>
    simp only [CommRingOps.add, CommRingOps.sub, CommRingOps.mul, CommRingOps.zero, CommRingOps.one, Goldilocks.add_val, Goldilocks.sub_val,
      Goldilocks.mul_val, Goldilocks.ofNat, Goldilocks.zero, Goldilocks.one] <;> decide


attribute [local irreducible] complianceTable checkCredentialEval

def commitTable (P : ReceiptParams) (tbl : List Goldilocks) : CanopyCommitment × AjtaiCommitment :=
  (DualPCS (R := Goldilocks) (canopyMerklePCS P.hash) (ajtaiLatticePCS P.lattice)).commit ((), ()) 5 tbl

structure CredentialStatement where
  policyDigest : ByteArray
  credentialDigest : ByteArray
  revokedRoot : ByteArray
  graphDigest : ByteArray
  disclosed : ByteArray
  tableCommitment : CanopyCommitment × AjtaiCommitment

/-- The statement of a public view under a policy digest and a table commitment. -/
def statementOf (policyDigest : ByteArray) (pub : DisclosureView)
    (comm : CanopyCommitment × AjtaiCommitment) : CredentialStatement :=
  ⟨policyDigest, pub.credentialDigest, pub.revokedRoot.bytes, pub.graphDigest, pub.disclosed, comm⟩

/-- The framed statement: what the transcript absorbs before any challenge. -/
def statementBytes (s : CredentialStatement) : ByteArray :=
  encodeFrame (encodeFrame s.policyDigest s.credentialDigest s.revokedRoot)
    (encodeFrame s.graphDigest s.disclosed ByteArray.empty)
    (TranscriptEncode.encodeTranscriptBytes s.tableCommitment)

theorem statementBytes_injective (s₁ s₂ : CredentialStatement)
    (h : statementBytes s₁ = statementBytes s₂) : s₁ = s₂ := by
  obtain ⟨p₁, c₁, r₁, g₁, d₁, t₁⟩ := s₁
  obtain ⟨p₂, c₂, r₂, g₂, d₂, t₂⟩ := s₂
  simp only [statementBytes] at h
  obtain ⟨ha, hb, hc⟩ := encodeFrame_injective h
  obtain ⟨h1, h2, h3⟩ := encodeFrame_injective ha
  obtain ⟨h4, h5, _⟩ := encodeFrame_injective hb
  have h6 : t₁ = t₂ := LawfulTranscriptEncode.encodeTranscriptBytes_injective hc
  subst h1 h2 h3 h4 h5 h6
  rfl

/-- Customization string of the statement digest. -/
def statementCustomization : List UInt8 := "OBEND.POLIS.VC-STATEMENT/v1".toUTF8.data.toList

/-- The digest a turn's effect names its inner statement by. -/
def statementDigest (s : CredentialStatement) : ByteArray :=
  cshake32ByteArray statementCustomization (statementBytes s).data.toList

/-- Equal statement digests name equal statements, or the two framed statements collide. -/
theorem statementDigest_binding (s₁ s₂ : CredentialStatement)
    (h : statementDigest s₁ = statementDigest s₂) :
    s₁ = s₂ ∨ CollisionAmong (cshake256Bytes statementCustomization) (fun x =>
      x = (statementBytes s₁).data.toList ∨ x = (statementBytes s₂).data.toList) := by
  rcases cshake32_binds statementCustomization h with hp | hc
  · exact .inl (statementBytes_injective s₁ s₂ (byteArray_eq_of_toList_eq hp))
  · exact .inr hc


structure ExPostReceipt where
  rounds : List (RoundPoly Goldilocks)
  opening : CanopyOpeningProof × AjtaiOpeningProof
  witness : CredentialWitness

def receiptProtocolId : String := "obend.polis.vc-receipt/v2"
def receiptTranscript (vk : ByteArray) (s : CredentialStatement) : Transcript .relationBound :=
  bindRelation receiptProtocolId vk (statementBytes s) (Transcript.newUnseeded ByteArray.empty)

def receiptView (s : CredentialStatement) (w : CredentialWitness) : DisclosureView :=
  ⟨s.credentialDigest, w.revoked.root, s.graphDigest, s.disclosed⟩

def verifyExPostCredentialReceipt (P : ReceiptParams) (pol : StatusPolicy) (vk : ByteArray)
    (s : CredentialStatement) (rc : ExPostReceipt) : Bool :=
  decide (s.revokedRoot = rc.witness.revoked.root.bytes) &&
  checkCredentialEval pol (receiptView s rc.witness) rc.witness &&
  decide (s.tableCommitment = commitTable P (complianceTable pol (receiptView s rc.witness) rc.witness)) &&
  verifyDualSumcheckPIOP (canopyMerklePCS P.hash) (ajtaiLatticePCS P.lattice) ((), ()) 1 5
    s.tableCommitment Goldilocks.zero rc.rounds rc.opening (receiptTranscript vk s)

theorem verifyExPostCredentialReceipt_sound (P : ReceiptParams) (pol : StatusPolicy)
    (vk : ByteArray) (s : CredentialStatement) (rc : ExPostReceipt)
    (h : verifyExPostCredentialReceipt P pol vk s rc = true) :
    CompliantEvaluation pol (receiptView s rc.witness) rc.witness ∧
    s.revokedRoot = rc.witness.revoked.root.bytes ∧
    s.tableCommitment = commitTable P (complianceTable pol (receiptView s rc.witness) rc.witness) ∧
    verifyDualSumcheckPIOP (canopyMerklePCS P.hash) (ajtaiLatticePCS P.lattice) ((), ()) 1 5
      s.tableCommitment Goldilocks.zero rc.rounds rc.opening (receiptTranscript vk s) = true := by
  simp only [verifyExPostCredentialReceipt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨stratified_credential_eval_sound _ _ _ h.1.1.2, h.1.1.1, h.1.2, h.2⟩

private def proveExPostOpening (P : ReceiptParams) (pol : StatusPolicy) (vk : ByteArray)
    (s : CredentialStatement) (w : CredentialWitness) : List (RoundPoly Goldilocks) × (CanopyOpeningProof × AjtaiOpeningProof) :=
  let tbl := complianceTable pol (receiptView s w) w
  let comm := commitTable P tbl
  let sc := honestBoundSumcheckProver (R := Goldilocks) comm 5 tbl (receiptTranscript vk s)
  let opening := (DualPCS (R := Goldilocks) (canopyMerklePCS P.hash)
    (ajtaiLatticePCS P.lattice)).openEval ((), ()) 5 tbl sc.2.1 sc.2.2
  (sc.1, opening.1)

def proveExPostCredentialReceipt (P : ReceiptParams) (pol : StatusPolicy) (vk : ByteArray)
    (s : CredentialStatement) (w : CredentialWitness) : ExPostReceipt :=
  ⟨(proveExPostOpening P pol vk s w).1, (proveExPostOpening P pol vk s w).2, w⟩

attribute [local irreducible] honestBoundSumcheckProver verifyDualSumcheckPIOP

theorem verifyExPostCredentialReceipt_complete (P : ReceiptParams) (pol : StatusPolicy)
    (vk : ByteArray) (s : CredentialStatement) (w : CredentialWitness)
    (hr : s.revokedRoot = w.revoked.root.bytes)
    (hc : checkCredentialEval pol (receiptView s w) w = true)
    (hcomm : s.tableCommitment = commitTable P (complianceTable pol (receiptView s w) w)) :
    verifyExPostCredentialReceipt P pol vk s (proveExPostCredentialReceipt P pol vk s w) = true := by
  have h := verifyDualSumcheckPIOP_completeness (canopyMerklePCS P.hash)
    (ajtaiLatticePCS P.lattice) ((), ()) (Nat.le_refl 1) 5
    (complianceTable pol (receiptView s w) w) (receiptTranscript vk s)
    ⟨trivial, P.cols_eq⟩ (complianceTable_length _ _ _)
  dsimp only at h
  rw [(complianceTable_sum_iff _ _ _).mpr hc] at h
  unfold verifyExPostCredentialReceipt
  change (decide (s.revokedRoot = w.revoked.root.bytes) && checkCredentialEval pol (receiptView s w) w &&
    decide (s.tableCommitment = commitTable P (complianceTable pol (receiptView s w) w)) && _) = true
  apply (Bool.and_eq_true _ _).mpr
  constructor
  · exact (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨decide_eq_true hr, hc⟩, decide_eq_true hcomm⟩
  rw [hcomm]
  change verifyDualSumcheckPIOP (canopyMerklePCS P.hash) (ajtaiLatticePCS P.lattice) ((), ()) 1 5
    (commitTable P (complianceTable pol (receiptView s w) w)) Goldilocks.zero
    (proveExPostOpening P pol vk s w).1 (proveExPostOpening P pol vk s w).2 (receiptTranscript vk s) = true
  unfold proveExPostOpening
  dsimp only [commitTable] at *
  exact h

theorem honestReceipt_accepted (P : ReceiptParams) (vk policyDigest : ByteArray)
    (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness)
    (h : checkCredentialEval pol pub w = true) :
    let s := statementOf policyDigest pub (commitTable P (complianceTable pol pub w))
    verifyExPostCredentialReceipt P pol vk s (proveExPostCredentialReceipt P pol vk s w) = true := by
  have hr := (stratified_credential_eval_sound pol pub w h).revokedBound
  have hv : receiptView (statementOf policyDigest pub (commitTable P (complianceTable pol pub w))) w = pub := by
    cases pub; simp_all [receiptView, statementOf]
  apply verifyExPostCredentialReceipt_complete
  · exact congrArg RevokedRoot.bytes hr.symm
  · rwa [hv]
  · rw [hv]; rfl

def deployedReceiptParams : ReceiptParams :=
  ⟨deployedCanopyHash32, inhabitedAjtaiParams 5, (inhabitedAjtaiParams_sisHard 5).1⟩

def canopyCommitmentCodec : Codec CanopyCommitment :=
  (Codec.pair Codec.nat Codec.digest32).refine (fun p => some ⟨p.1, p.2⟩)
    (fun c => (c.numVars, c.root)) (fun _ => rfl)

def ajtaiCommitmentCodec : Codec AjtaiCommitment :=
  (Codec.pair Codec.nat (Codec.list Codec.int)).refine (fun p => some ⟨p.1, p.2⟩)
    (fun c => (c.numVars, c.syndrome)) (fun _ => rfl)

def statementCodec : Codec CredentialStatement :=
  (Codec.pair (Codec.pair Codec.bytes (Codec.pair Codec.bytes Codec.bytes))
      (Codec.pair (Codec.pair Codec.bytes Codec.bytes)
        (Codec.pair canopyCommitmentCodec ajtaiCommitmentCodec))).refine
    (fun p => some ⟨p.1.1, p.1.2.1, p.1.2.2, p.2.1.1, p.2.1.2, p.2.2⟩)
    (fun s => ((s.policyDigest, s.credentialDigest, s.revokedRoot),
      (s.graphDigest, s.disclosed), s.tableCommitment))
    (fun _ => rfl)

def receiptCodec : Codec ExPostReceipt :=
  (Codec.pair
      (Codec.list ((Codec.list Codec.goldilocks).refine (fun l => some ⟨l⟩) RoundPoly.coeffs
        (fun _ => rfl)))
      (Codec.pair (Codec.pair
        ((Codec.list (Codec.pair Codec.goldilocks (Codec.list Codec.digest32))).refine
          (fun l => some ⟨l⟩) CanopyOpeningProof.entries (fun _ => rfl))
        ((Codec.list Codec.int).refine (fun l => some ⟨l⟩) AjtaiOpeningProof.shortLimbs
          (fun _ => rfl))) witnessCodec)).refine
    (fun p => some ⟨p.1, p.2.1, p.2.2⟩)
    (fun rc => (rc.rounds, rc.opening, rc.witness)) (fun _ => rfl)

/-- A proof on the wire: the statement, then the receipt. -/
def encodeReceiptBytes (s : CredentialStatement) (rc : ExPostReceipt) : ByteArray :=
  Native.bytesOfList ((Codec.pair statementCodec receiptCodec).enc (s, rc))

/-- Decode a proof: one statement, one receipt, and nothing after them. -/
def decodeReceiptBytes (proof : ByteArray) : Option (CredentialStatement × ExPostReceipt) :=
  match (Codec.pair statementCodec receiptCodec).dec proof.data.toList with
  | some (x, []) => some x
  | _ => none

theorem decodeReceiptBytes_encode (s : CredentialStatement) (rc : ExPostReceipt) :
    decodeReceiptBytes (encodeReceiptBytes s rc) = some (s, rc) := by
  have h := (Codec.pair statementCodec receiptCodec).dec_enc (s, rc) []
  rw [List.append_nil] at h
  simp [decodeReceiptBytes, encodeReceiptBytes, Native.bytesOfList_toList, h]


/-- The verifier's policy is trusted input. Receipts cannot supply their own authorization key. -/
def verifiableCredentialInnerVerifier (P : ReceiptParams) (pol : StatusPolicy) (policyDigest : ByteArray)
    (vk statement proof : ByteArray) : Bool :=
  match decodeReceiptBytes proof with
  | none => false
  | some x => decide (statementDigest x.1 = statement) && decide (x.1.policyDigest = policyDigest) &&
      verifyExPostCredentialReceipt P pol vk x.1 x.2

theorem verifiableCredentialInnerVerifier_sound (P : ReceiptParams) (pol : StatusPolicy)
    (policyDigest vk statement proof : ByteArray)
    (h : verifiableCredentialInnerVerifier P pol policyDigest vk statement proof = true) :
    ∃ s rc, decodeReceiptBytes proof = some (s, rc) ∧ statementDigest s = statement ∧
      s.policyDigest = policyDigest ∧ verifyExPostCredentialReceipt P pol vk s rc = true ∧
      CompliantEvaluation pol (receiptView s rc.witness) rc.witness := by
  unfold verifiableCredentialInnerVerifier at h
  cases hd : decodeReceiptBytes proof with
  | none => rw [hd] at h; cases h
  | some x =>
    rw [hd] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨x.1, x.2, rfl, h.1.1, h.1.2, h.2, (verifyExPostCredentialReceipt_sound _ _ _ _ _ h.2).1⟩

theorem verifiableCredentialInnerVerifier_complete (P : ReceiptParams) (policyDigest vk : ByteArray)
    (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness)
    (h : checkCredentialEval pol pub w = true) :
    let s := statementOf policyDigest pub (commitTable P (complianceTable pol pub w))
    verifiableCredentialInnerVerifier P pol policyDigest vk (statementDigest s)
      (encodeReceiptBytes s (proveExPostCredentialReceipt P pol vk s w)) = true := by
  dsimp only
  unfold verifiableCredentialInnerVerifier
  rw [decodeReceiptBytes_encode]
  simp only [decide_true, Bool.true_and, statementOf, Bool.and_true]
  exact honestReceipt_accepted P vk policyDigest pol pub w h

theorem verifiableCredentialInnerVerifier_inhabited (P : ReceiptParams) (policyDigest vk : ByteArray)
    (pol : StatusPolicy) (pub : DisclosureView) (w : CredentialWitness)
    (h : checkCredentialEval pol pub w = true) :
    ∃ statement proof, verifiableCredentialInnerVerifier P pol policyDigest vk statement proof = true :=
  ⟨_, _, verifiableCredentialInnerVerifier_complete P policyDigest vk pol pub w h⟩

end Obend.Polis.VerifiableCredentials
