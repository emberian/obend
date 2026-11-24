module
/-
# Obend.Vault.CertifiedPartialView — Dynamic 256-Bit Sparse Authenticated Partial Views & CertifiedPeval Membranes

Implements Split-Stream authenticated partial views (Miller et al., POPL '14 `λ•` authenticated data
structures) over a dynamic, key-sorted 256-bit `cSHAKE256`-committed object dictionary together with a
certified partial evaluation membrane (`CertifiedPeval`) and a Goldilocks Module-SIS Ajtai homomorphic
linear opening bridge to `Obend.Vault.Form`:

1. **Dynamic 256-Bit Sparse Authenticated Partial-View Tree (`FullStore` vs `PartialView`)**:
   - Keys are 256-bit `Key256 := Digest256`, covering contiguous closed spans `[lo, hi]` with
     gap-free internal branch adjacency (`l.hi.toNat + 1 = r.lo.toNat`).
   - Every node body and outer span envelope is length-framed (`frameFields`) into 256-bit
     `cSHAKE256` commitments under customization `"OBEND.VAULT.CPV/v1"`.
   - Capability-frustum projection (`projectPartialView`) collapses unauthorized leaves and entire
     unauthorized subtrees into salted 256-bit `.blindedStub` digests while preserving the exact
     256-bit `worldRoot` (`partialViewRoot (projectPartialView cf fs) = fullStoreRoot fs`).
   - Constructive range non-omission (`rangeScanPartial_sound_psum`, `rangeScanPartial_sound_or_collision`):
     whenever `rangeScanPartial pv expectedRoot qLo qHi = .complete entries`, zero matching keys in
     `[qLo, qHi]` were omitted by an untrusted host, or a finite-scope `CollisionAmong` / constructive
     `CshakeCollisionWitness` is extracted in `Type` via `PSum` without `Classical.choice`.

2. **Certified Partial Evaluation Membrane (`peval` & Multi-Turn `ValidMembraneTrace`)**:
   - Partially evaluates linear/first-order `PExpr` programs (`.lit`, `.proj`, `.scale`, `.add`,
     `.sub`, `.ifLe`, `.recProj`) against a `PartialView`, folding `.present` and `.emptyGap` reads,
     pruning dead conditional branches and unselected record slots, annihilating `0`-scaled terms,
     and wrapping remaining blinded reads into capability-guarded `.guardedStubRead` nodes paired
     with a length-framed 256-bit Split-Stream transcript CID (`pevalTranscriptCid`).
   - `peval_sound_and_confidential` proves across arbitrary multi-turn read/write membrane traces
     (`ValidMembraneTrace`, with initial consistency as an external hypothesis) that residual
     evaluation under secret-only `env_sec` equals full store execution `execFullTurns` step-for-step,
     preserves `PartialViewConsistent` and `worldRoot` across writes, and leaks zero references to
     redacted keys outside `residualReadCone`.

3. **Goldilocks Module-SIS Ajtai Homomorphic Linear Opening for `Form.NExpr.peval`**:
   - Exploits additive homomorphism of Module-SIS Ajtai commitments (`Obend.Crypto.DualSpine`) over
     4-limb Goldilocks ($2^{16}$-radix) + blinding witnesses so an untrusted host certifies affine
     hidden-cell combinations in `Form.NExpr` via a single combined masked short vector
     `s_comb = ∑_i c_i • s_i + s_mask` — zero generic SNARK circuit, zero leakage of individual
     hidden fields, constructive `PSum` extraction of `SISShortVecWitness`, and direct transport into
     `Form.RMove.EvalEquivOn`, `Form.pairsOf_congr_eval`, and `Form.pairs_balanced`.
-/
public import Obend.Core.Digest
public import Obend.Vault.Form
public import Obend.Vault.Projection
public import Obend.Crypto.Transcript
public import Obend.Crypto.DualSpine
import all Obend.Vault.Form
import all Obend.Crypto.DualSpine

public section

namespace Obend.Vault.CertifiedPartialView

open Obend.Digest.HashBytes (Hash ofBE ofBE_lt CollisionAmong)
open Obend.Digest.Cshake256 (cshake256Bytes)
open Obend.Core.Digest (Digest256 bytes32OfDigest256 bytes32OfDigest256_injective)
open Obend.Crypto (leb128 leb128Aux leb128_prefix_inj encodeListField encodeListField_prefix_inj
  AjtaiParams ShortNormBound checkShortNorm checkShortNorm_iff
  vecAdd vecAdd_length ajtaiCommit vecAddMod ajtaiCommit_add extractShortDiffSISWitness)
open Obend.Judge.Computational (SISShortVecWitness)
open Obend.Vault (sumAssetDelta)
open Obend.Vault.Affordance (Auth fireGate)
open Obend.Vault.Form (NExpr PRef Known Assignment Move RMove addN subN pairsOf pairDeltas ListForall2)

set_option autoImplicit false

/-! ## 1. 256-Bit `cSHAKE256` Domain Separation, Self-Delimiting Length Framing & `PSum` Collisions -/

/-- 256-bit object key in the sparse authenticated dictionary. -/
abbrev Key256 := Digest256

/-- Constructive `Type`-valued collision witness for a byte hash `H` (`0 Classical.choice`). -/
structure CshakeCollisionWitness (H : Hash) where
  msg₁      : List UInt8
  msg₂      : List UInt8
  distinct  : msg₁ ≠ msg₂
  equalHash : ofBE (H msg₁) = ofBE (H msg₂)

theorem CshakeCollisionWitness.toScoped {H : Hash} {S : List UInt8 → Prop}
    (w : CshakeCollisionWitness H) (h₁ : S w.msg₁) (h₂ : S w.msg₂) :
    CollisionAmong H S :=
  ⟨w.msg₁, w.msg₂, h₁, h₂, w.distinct, w.equalHash⟩

/-- Explicit UTF-8 bytes of `"OBEND.VAULT.CPV/v1"` for kernel-reducible customization framing. -/
def cpvCustomization : List UInt8 :=
  [0x4f, 0x42, 0x45, 0x4e, 0x44, 0x2e, 0x56, 0x41, 0x55, 0x4c, 0x54, 0x2e, 0x43, 0x50, 0x56, 0x2f, 0x76, 0x31]

/-- Deployed `cSHAKE256` byte hash for `CertifiedPartialView`. -/
def cpvHashBytes : Hash := cshake256Bytes cpvCustomization

/-- 256-bit `Digest256` commitment over a length-framed preimage. -/
def cpvHash256 (pre : List UInt8) : Digest256 :=
  BitVec.ofNat 256 (ofBE (cpvHashBytes pre))

theorem cpvHash256_eq_to_ofBE_eq {p₁ p₂ : List UInt8}
    (h : cpvHash256 p₁ = cpvHash256 p₂) :
    ofBE (cpvHashBytes p₁) = ofBE (cpvHashBytes p₂) := by
  have hpow : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  have hl₁ : (cpvHashBytes p₁).length = 32 := by simp [cpvHashBytes]
  have hl₂ : (cpvHashBytes p₂).length = 32 := by simp [cpvHashBytes]
  have hb₁ : ofBE (cpvHashBytes p₁) < 2 ^ 256 := by
    have := ofBE_lt (cpvHashBytes p₁); rwa [hl₁, hpow] at this
  have hb₂ : ofBE (cpvHashBytes p₂) < 2 ^ 256 := by
    have := ofBE_lt (cpvHashBytes p₂); rwa [hl₂, hpow] at this
  have hn := congrArg BitVec.toNat h
  simpa only [cpvHash256, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb₁, Nat.mod_eq_of_lt hb₂] using hn

/-- Constructive `PSum` preimage binder (`0 Classical.choice`): equal 256-bit `cSHAKE256` outputs
    either have identical preimages or return the exact colliding message pair in `Type`. -/
def cpvHash256_binds_psum {p₁ p₂ : List UInt8}
    (h : cpvHash256 p₁ = cpvHash256 p₂) :
    PSum (p₁ = p₂) (CshakeCollisionWitness cpvHashBytes) :=
  if hp : p₁ = p₂ then
    .inl hp
  else
    .inr ⟨p₁, p₂, hp, cpvHash256_eq_to_ofBE_eq h⟩

/-- Finite-pair scoped collision binder (avoids pigeonhole vacuity). -/
theorem cpvHash256_binds_scoped {p₁ p₂ : List UInt8}
    (h : cpvHash256 p₁ = cpvHash256 p₂) :
    p₁ = p₂ ∨ CollisionAmong cpvHashBytes (fun x => x = p₁ ∨ x = p₂) :=
  if hp : p₁ = p₂ then
    .inl hp
  else
    .inr ⟨p₁, p₂, .inl rfl, .inr rfl, hp, cpvHash256_eq_to_ofBE_eq h⟩

theorem leb128_injective {n₁ n₂ : Nat} (h : leb128 n₁ = leb128 n₂) : n₁ = n₂ :=
  (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)).1

theorem leb128_ne_nil (n : Nat) : leb128 n ≠ [] := by
  unfold leb128
  cases n with
  | zero => simp [leb128Aux]
  | succ k =>
    simp only [leb128Aux]
    split <;> simp

theorem encodeListField_ne_nil (f rest : List UInt8) :
    encodeListField f ++ rest ≠ [] := by
  intro h
  simp only [encodeListField, List.append_assoc, List.append_eq_nil_iff] at h
  exact leb128_ne_nil f.length h.1

/-- Canonical length-prefixed multi-field byte frame `len(f₁) ‖ f₁ ‖ … ‖ len(fₙ) ‖ fₙ`. -/
def frameFields : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => encodeListField f ++ frameFields fs

theorem frameFields_injective : ∀ {fs₁ fs₂ : List (List UInt8)},
    frameFields fs₁ = frameFields fs₂ → fs₁ = fs₂
  | [], [], _ => rfl
  | [], f :: fs, h => False.elim (encodeListField_ne_nil f (frameFields fs) h.symm)
  | f :: fs, [], h => False.elim (encodeListField_ne_nil f (frameFields fs) h)
  | f₁ :: fs₁, f₂ :: fs₂, h => by
    simp only [frameFields] at h
    obtain ⟨hf, hrest⟩ := encodeListField_prefix_inj h
    rw [hf, frameFields_injective hrest]

/-- Length-framed encoding of `(fieldId, scalarVal)` pairs. -/
def encodeNatPairs (ps : List (Nat × Nat)) : List UInt8 :=
  frameFields (ps.map fun p => frameFields [leb128 p.1, leb128 p.2])

theorem encodeNatPairs_injective : ∀ {ps₁ ps₂ : List (Nat × Nat)},
    encodeNatPairs ps₁ = encodeNatPairs ps₂ → ps₁ = ps₂
  | [], [], _ => rfl
  | [], _ :: _, h => by cases frameFields_injective h
  | _ :: _, [], h => by cases frameFields_injective h
  | (a₁, b₁) :: r₁, (a₂, b₂) :: r₂, h => by
    have hm := frameFields_injective h
    simp only [List.map_cons, List.cons.injEq] at hm
    have hp := frameFields_injective hm.1
    simp only [List.cons.injEq] at hp
    have ha := leb128_injective hp.1
    have hb := leb128_injective hp.2.1
    have hr := encodeNatPairs_injective (congrArg frameFields hm.2)
    subst ha; subst hb; subst hr; rfl

def authByte : Auth → UInt8
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3
  | .reply => 4 | .reset => 5 | .control => 6 | .notify => 7

theorem authByte_injective {a b : Auth} (h : authByte a = authByte b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

def encodeAuthList (as : List Auth) : List UInt8 :=
  as.map authByte

theorem encodeAuthList_injective : ∀ {l₁ l₂ : List Auth},
    encodeAuthList l₁ = encodeAuthList l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: r₁, b :: r₂, h => by
    simp only [encodeAuthList, List.map_cons, List.cons.injEq] at h
    rw [authByte_injective h.1, encodeAuthList_injective h.2]

/-! ## 2. Dynamic Sparse Authenticated Partial-View Tree (`FullStore` vs `PartialView`) -/

/-- Multi-field object record stored at a 256-bit key, carrying named scalar slots,
    required capability gate, and a fresh 256-bit blinding salt. -/
structure ObjRecord where
  fields   : List (Nat × Nat)
  required : List Auth
  salt     : Digest256
deriving DecidableEq, Repr

def ObjRecord.getField (rec : ObjRecord) (fieldId : Nat) : Nat :=
  (rec.fields.lookup fieldId).getD 0

def ObjRecord.setField (rec : ObjRecord) (fieldId val : Nat) (newSalt : Digest256) : ObjRecord :=
  { rec with
    fields := (fieldId, val) :: rec.fields.filter (fun p => p.1 != fieldId)
    salt := newSalt }

@[simp] theorem ObjRecord.getField_setField_same (rec : ObjRecord) (f v : Nat) (s : Digest256) :
    (rec.setField f v s).getField f = v := by
  simp [ObjRecord.getField, ObjRecord.setField]

/-- Domain-separation tags for tree node bodies, outer stub commitments, and Split-Stream transcripts. -/
@[expose] def presentNodeTag : List UInt8 := [0x43, 0x50, 0x56, 0x2e, 0x50, 0x52, 0x45, 0x53, 0x01]
@[expose] def emptyGapTag    : List UInt8 := [0x43, 0x50, 0x56, 0x2e, 0x45, 0x47, 0x41, 0x50, 0x02]
@[expose] def branchNodeTag  : List UInt8 := [0x43, 0x50, 0x56, 0x2e, 0x42, 0x52, 0x43, 0x48, 0x03]
@[expose] def blindedStubTag : List UInt8 := [0x43, 0x50, 0x56, 0x2e, 0x53, 0x54, 0x55, 0x42, 0x04]
def transcriptTag            : List UInt8 := [0x43, 0x50, 0x56, 0x2e, 0x58, 0x53, 0x43, 0x52, 0x05]

def presentBodyPreimage (k : Key256) (rec : ObjRecord) : List UInt8 :=
  frameFields [
    presentNodeTag,
    bytes32OfDigest256 k,
    encodeNatPairs rec.fields,
    encodeAuthList rec.required,
    bytes32OfDigest256 rec.salt
  ]

def emptyBodyPreimage (lo hi : Key256) : List UInt8 :=
  frameFields [emptyGapTag, bytes32OfDigest256 lo, bytes32OfDigest256 hi, bytes32OfDigest256 0#256]

def branchBodyPreimage (leftRoot rightRoot : Digest256) : List UInt8 :=
  frameFields [branchNodeTag, bytes32OfDigest256 leftRoot, bytes32OfDigest256 rightRoot, bytes32OfDigest256 0#256]

def stubCommitPreimage (lo hi : Key256) (bodyDigest : Digest256) : List UInt8 :=
  frameFields [blindedStubTag, bytes32OfDigest256 lo, bytes32OfDigest256 hi, bytes32OfDigest256 bodyDigest]

def presentBodyDigest (k : Key256) (rec : ObjRecord) : Digest256 :=
  cpvHash256 (presentBodyPreimage k rec)

def emptyBodyDigest (lo hi : Key256) : Digest256 :=
  cpvHash256 (emptyBodyPreimage lo hi)

def branchBodyDigest (leftRoot rightRoot : Digest256) : Digest256 :=
  cpvHash256 (branchBodyPreimage leftRoot rightRoot)

/-- Outer span-enveloped commitment shared by `.blindedStub` and unredacted tree nodes. -/
def stubCommit (lo hi : Key256) (bodyDigest : Digest256) : Digest256 :=
  cpvHash256 (stubCommitPreimage lo hi bodyDigest)

theorem presentBodyPreimage_injective {k₁ k₂ : Key256} {r₁ r₂ : ObjRecord}
    (h : presentBodyPreimage k₁ r₁ = presentBodyPreimage k₂ r₂) :
    k₁ = k₂ ∧ r₁ = r₂ := by
  have hf := frameFields_injective h
  simp only [List.cons.injEq] at hf
  have hk := bytes32OfDigest256_injective hf.2.1
  have hfs := encodeNatPairs_injective hf.2.2.1
  have hreq := encodeAuthList_injective hf.2.2.2.1
  have hsalt := bytes32OfDigest256_injective hf.2.2.2.2.1
  cases r₁; cases r₂
  simp_all

theorem branchBodyPreimage_injective {l₁ r₁ l₂ r₂ : Digest256}
    (h : branchBodyPreimage l₁ r₁ = branchBodyPreimage l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have hf := frameFields_injective h
  simp only [List.cons.injEq] at hf
  exact ⟨bytes32OfDigest256_injective hf.2.1, bytes32OfDigest256_injective hf.2.2.1⟩

theorem stubCommitPreimage_injective {lo₁ hi₁ lo₂ hi₂ : Key256} {b₁ b₂ : Digest256}
    (h : stubCommitPreimage lo₁ hi₁ b₁ = stubCommitPreimage lo₂ hi₂ b₂) :
    lo₁ = lo₂ ∧ hi₁ = hi₂ ∧ b₁ = b₂ := by
  have hf := frameFields_injective h
  simp only [List.cons.injEq] at hf
  exact ⟨bytes32OfDigest256_injective hf.2.1,
         bytes32OfDigest256_injective hf.2.2.1,
         bytes32OfDigest256_injective hf.2.2.2.1⟩

/-- Explicit 4-element preimage scope for `.blindedStub` domain-separation checks. -/
def domainSepPreimages (sLo sHi k eLo eHi : Key256)
    (bodyDigest lRoot rRoot : Digest256) (rec : ObjRecord) : List (List UInt8) :=
  [stubCommitPreimage sLo sHi bodyDigest,
   presentBodyPreimage k rec,
   emptyBodyPreimage eLo eHi,
   branchBodyPreimage lRoot rRoot]

/-- **`.blindedStub` Tag Domain Separation (`blindedStub_domain_sep_or_collision`)**:
    No outer `.blindedStub` commitment `stubCommit` can collide with a `.present`, `.emptyGap`,
    or `.branch` body digest (preventing second-preimage depth-truncation / grafting) without
    a finite-scope `CollisionAmong` on those exact four preimages. -/
theorem blindedStub_domain_sep_or_collision
    (sLo sHi k eLo eHi : Key256) (bodyDigest lRoot rRoot : Digest256) (rec : ObjRecord) :
    (stubCommit sLo sHi bodyDigest = presentBodyDigest k rec →
      CollisionAmong cpvHashBytes
        (fun x => x ∈ domainSepPreimages sLo sHi k eLo eHi bodyDigest lRoot rRoot rec)) ∧
    (stubCommit sLo sHi bodyDigest = emptyBodyDigest eLo eHi →
      CollisionAmong cpvHashBytes
        (fun x => x ∈ domainSepPreimages sLo sHi k eLo eHi bodyDigest lRoot rRoot rec)) ∧
    (stubCommit sLo sHi bodyDigest = branchBodyDigest lRoot rRoot →
      CollisionAmong cpvHashBytes
        (fun x => x ∈ domainSepPreimages sLo sHi k eLo eHi bodyDigest lRoot rRoot rec)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases cpvHash256_binds_scoped h with hp | hc
    · have hf := frameFields_injective hp
      have hne : blindedStubTag ≠ presentNodeTag := by decide
      exact False.elim (hne (List.cons.inj hf).1)
    · exact hc.mono fun _ hm => by rcases hm with rfl | rfl <;> simp [domainSepPreimages]
  · rcases cpvHash256_binds_scoped h with hp | hc
    · have hf := frameFields_injective hp
      have hne : blindedStubTag ≠ emptyGapTag := by decide
      exact False.elim (hne (List.cons.inj hf).1)
    · exact hc.mono fun _ hm => by rcases hm with rfl | rfl <;> simp [domainSepPreimages]
  · rcases cpvHash256_binds_scoped h with hp | hc
    · have hf := frameFields_injective hp
      have hne : blindedStubTag ≠ branchNodeTag := by decide
      exact False.elim (hne (List.cons.inj hf).1)
    · exact hc.mono fun _ hm => by rcases hm with rfl | rfl <;> simp [domainSepPreimages]

/-- Constructive `PSum` domain-separation extractor for `.blindedStub` vs `.emptyGap` (`0 Classical.choice`). -/
def blindedStub_ne_emptyGap_psum (sLo sHi eLo eHi : Key256) (bodyDigest : Digest256)
    (h : stubCommit sLo sHi bodyDigest = emptyBodyDigest eLo eHi) :
    CshakeCollisionWitness cpvHashBytes :=
  match cpvHash256_binds_psum h with
  | .inr w => w
  | .inl hp =>
    have hf := frameFields_injective hp
    have htag : blindedStubTag = emptyGapTag := (List.cons.inj hf).1
    False.elim ((by decide : blindedStubTag ≠ emptyGapTag) htag)

/-- Unredacted key-sorted sparse authenticated dictionary tree. -/
inductive FullTree where
  | present  (key : Key256) (rec : ObjRecord)
  | emptyGap (keyLo keyHi : Key256)
  | branch   (left right : FullTree)
deriving DecidableEq, Repr

/-- Capability-redacted sparse authenticated partial-view tree (`λ•` shallow projection). -/
inductive PartialViewTree where
  | present     (key : Key256) (rec : ObjRecord)
  | blindedStub (bodyDigest : Digest256) (keyLo keyHi : Key256)
  | emptyGap    (keyLo keyHi : Key256)
  | branch      (left right : PartialViewTree)
deriving DecidableEq, Repr

def FullTree.lo : FullTree → Key256
  | .present k _ => k
  | .emptyGap lo _ => lo
  | .branch l _ => l.lo

def FullTree.hi : FullTree → Key256
  | .present k _ => k
  | .emptyGap _ hi => hi
  | .branch _ r => r.hi

def PartialViewTree.lo : PartialViewTree → Key256
  | .present k _ => k
  | .blindedStub _ lo _ => lo
  | .emptyGap lo _ => lo
  | .branch l _ => l.lo

def PartialViewTree.hi : PartialViewTree → Key256
  | .present k _ => k
  | .blindedStub _ _ hi => hi
  | .emptyGap _ hi => hi
  | .branch _ r => r.hi

/-- Contiguous closed-interval partition invariant: every branch splits `[l.lo, r.hi]` with
    zero unauthenticated crack (`l.hi.toNat + 1 = r.lo.toNat`). -/
def FullTree.wf : FullTree → Bool
  | .present _ _ => true
  | .emptyGap lo hi => decide (lo.toNat ≤ hi.toNat)
  | .branch l r => l.wf && r.wf && decide (l.hi.toNat + 1 = r.lo.toNat)

def PartialViewTree.wf : PartialViewTree → Bool
  | .present _ _ => true
  | .blindedStub _ lo hi => decide (lo.toNat ≤ hi.toNat)
  | .emptyGap lo hi => decide (lo.toNat ≤ hi.toNat)
  | .branch l r => l.wf && r.wf && decide (l.hi.toNat + 1 = r.lo.toNat)

theorem FullTree.wf_lo_le_hi : ∀ {t : FullTree}, t.wf = true → t.lo.toNat ≤ t.hi.toNat
  | .present _ _, _ => Nat.le_refl _
  | .emptyGap _ _, h => of_decide_eq_true h
  | .branch l r, h => by
    simp only [FullTree.wf, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := l.wf_lo_le_hi h.1.1
    have hr := r.wf_lo_le_hi h.1.2
    simp only [FullTree.lo, FullTree.hi]; omega

theorem PartialViewTree.wf_lo_le_hi : ∀ {t : PartialViewTree}, t.wf = true → t.lo.toNat ≤ t.hi.toNat
  | .present _ _, _ => Nat.le_refl _
  | .blindedStub _ _ _, h => of_decide_eq_true h
  | .emptyGap _ _, h => of_decide_eq_true h
  | .branch l r, h => by
    simp only [PartialViewTree.wf, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := l.wf_lo_le_hi h.1.1
    have hr := r.wf_lo_le_hi h.1.2
    simp only [PartialViewTree.lo, PartialViewTree.hi]; omega

/-- Direct structural 256-bit Merkle-span commitment of a `FullTree` (zero `WellFounded.fix`). -/
def fullNodeRoot : FullTree → Digest256
  | .present k rec => stubCommit k k (presentBodyDigest k rec)
  | .emptyGap lo hi => stubCommit lo hi (emptyBodyDigest lo hi)
  | .branch l r => stubCommit l.lo r.hi (branchBodyDigest (fullNodeRoot l) (fullNodeRoot r))

def fullBodyDigest : FullTree → Digest256
  | .present k rec => presentBodyDigest k rec
  | .emptyGap lo hi => emptyBodyDigest lo hi
  | .branch l r => branchBodyDigest (fullNodeRoot l) (fullNodeRoot r)

theorem fullNodeRoot_eq_stubCommit (ft : FullTree) :
    fullNodeRoot ft = stubCommit ft.lo ft.hi (fullBodyDigest ft) := by
  cases ft <;> rfl

/-- Direct structural 256-bit Merkle-span commitment of a `PartialViewTree` (zero `WellFounded.fix`). -/
def partialNodeRoot : PartialViewTree → Digest256
  | .present k rec => stubCommit k k (presentBodyDigest k rec)
  | .blindedStub d lo hi => stubCommit lo hi d
  | .emptyGap lo hi => stubCommit lo hi (emptyBodyDigest lo hi)
  | .branch l r => stubCommit l.lo r.hi (branchBodyDigest (partialNodeRoot l) (partialNodeRoot r))

def partialBodyDigest : PartialViewTree → Digest256
  | .present k rec => presentBodyDigest k rec
  | .blindedStub d _ _ => d
  | .emptyGap lo hi => emptyBodyDigest lo hi
  | .branch l r => branchBodyDigest (partialNodeRoot l) (partialNodeRoot r)

theorem partialNodeRoot_eq_stubCommit (pt : PartialViewTree) :
    partialNodeRoot pt = stubCommit pt.lo pt.hi (partialBodyDigest pt) := by
  cases pt <;> rfl

/-- Explicit finite preimage list hashed by a `FullTree`. -/
def fullTreePreimages : FullTree → List (List UInt8)
  | .present k rec =>
    [stubCommitPreimage k k (presentBodyDigest k rec), presentBodyPreimage k rec]
  | .emptyGap lo hi =>
    [stubCommitPreimage lo hi (emptyBodyDigest lo hi), emptyBodyPreimage lo hi]
  | .branch l r =>
    stubCommitPreimage l.lo r.hi (branchBodyDigest (fullNodeRoot l) (fullNodeRoot r)) ::
      branchBodyPreimage (fullNodeRoot l) (fullNodeRoot r) ::
      (fullTreePreimages l ++ fullTreePreimages r)

/-- Explicit finite preimage list hashed by a `PartialViewTree`. -/
def partialTreePreimages : PartialViewTree → List (List UInt8)
  | .present k rec =>
    [stubCommitPreimage k k (presentBodyDigest k rec), presentBodyPreimage k rec]
  | .blindedStub d lo hi =>
    [stubCommitPreimage lo hi d]
  | .emptyGap lo hi =>
    [stubCommitPreimage lo hi (emptyBodyDigest lo hi), emptyBodyPreimage lo hi]
  | .branch l r =>
    stubCommitPreimage l.lo r.hi (branchBodyDigest (partialNodeRoot l) (partialNodeRoot r)) ::
      branchBodyPreimage (partialNodeRoot l) (partialNodeRoot r) ::
      (partialTreePreimages l ++ partialTreePreimages r)

theorem stubPreimage_mem_fullTreePreimages (ft : FullTree) :
    stubCommitPreimage ft.lo ft.hi (fullBodyDigest ft) ∈ fullTreePreimages ft := by
  cases ft <;> simp [fullTreePreimages, fullBodyDigest, FullTree.lo, FullTree.hi]

theorem stubPreimage_mem_partialTreePreimages (pt : PartialViewTree) :
    stubCommitPreimage pt.lo pt.hi (partialBodyDigest pt) ∈ partialTreePreimages pt := by
  cases pt <;> simp [partialTreePreimages, partialBodyDigest, PartialViewTree.lo, PartialViewTree.hi]

/-- Unredacted authenticated key-value store. -/
structure FullStore where
  tree : FullTree
deriving DecidableEq, Repr

/-- Capability frustum governing which key intervals and authorities a partial view or residual
    evaluator is authorized to observe. -/
structure CapFrustum where
  heldAuths     : List Auth
  allowedRanges : List (Key256 × Key256)
deriving DecidableEq, Repr

/-- Capability-redacted partial view carrying the pinned 256-bit `worldRoot` and `PartialViewTree`. -/
structure PartialView where
  worldRoot   : Digest256
  viewFrustum : CapFrustum
  tree        : PartialViewTree
deriving DecidableEq, Repr

def fullStoreRoot (fs : FullStore) : Digest256 :=
  fullNodeRoot fs.tree

def partialViewRoot (pv : PartialView) : Digest256 :=
  partialNodeRoot pv.tree

/-- True iff `k` lies in the closed 256-bit key interval `[lo, hi]`. -/
def inKeyRange (lo hi k : Key256) : Bool :=
  decide (lo.toNat ≤ k.toNat) && decide (k.toNat ≤ hi.toNat)

/-- True iff closed key intervals `[aLo, aHi]` and `[bLo, bHi]` overlap (`aLo ≤ bHi ∧ bLo ≤ aHi`). -/
@[expose] def rangesOverlap (aLo aHi bLo bHi : Key256) : Bool :=
  decide (aLo.toNat ≤ bHi.toNat) && decide (bLo.toNat ≤ aHi.toNat)

def frustumCoversKey (cf : CapFrustum) (k : Key256) : Bool :=
  cf.allowedRanges.any (fun r => inKeyRange r.1 r.2 k)

def frustumTouchesSpan (cf : CapFrustum) (lo hi : Key256) : Bool :=
  cf.allowedRanges.any (fun r => rangesOverlap lo hi r.1 r.2)

def frustumAllowsEntry (cf : CapFrustum) (k : Key256) (rec : ObjRecord) : Bool :=
  frustumCoversKey cf k && fireGate rec.required cf.heldAuths

theorem any_inKeyRange_false_of_any_rangesOverlap_false
    {lo hi k : Key256} (hkLo : lo.toNat ≤ k.toNat) (hkHi : k.toNat ≤ hi.toNat) :
    ∀ (rs : List (Key256 × Key256)),
      (rs.any fun r => rangesOverlap lo hi r.1 r.2) = false →
      (rs.any fun r => inKeyRange r.1 r.2 k) = false
  | [], _ => rfl
  | r :: rest, hTouch => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hTouch ⊢
    refine ⟨?_, any_inKeyRange_false_of_any_rangesOverlap_false hkLo hkHi rest hTouch.2⟩
    have hOver := hTouch.1
    unfold rangesOverlap at hOver
    unfold inKeyRange
    by_cases h1 : r.1.toNat ≤ k.toNat
    · by_cases h2 : k.toNat ≤ r.2.toNat
      · have ha : lo.toNat ≤ r.2.toNat := Nat.le_trans hkLo h2
        have hb : r.1.toNat ≤ hi.toNat := Nat.le_trans h1 hkHi
        simp [ha, hb] at hOver
      · simp [h2]
    · simp [h1]

theorem frustumCoversKey_false_of_touchesSpan_false
    {cf : CapFrustum} {lo hi k : Key256}
    (hTouch : frustumTouchesSpan cf lo hi = false)
    (hkLo : lo.toNat ≤ k.toNat) (hkHi : k.toNat ≤ hi.toNat) :
    frustumCoversKey cf k = false :=
  any_inKeyRange_false_of_any_rangesOverlap_false hkLo hkHi cf.allowedRanges hTouch

/-- Project a `FullTree` to a capability-redacted `PartialViewTree`:
    subtrees disjoint from `cf.allowedRanges` collapse into a single 32-byte `.blindedStub`,
    and unauthorized `.present` leaves redact to salted `.blindedStub`s. -/
def projectSubtree (cf : CapFrustum) (ft : FullTree) : PartialViewTree :=
  if !frustumTouchesSpan cf ft.lo ft.hi then
    .blindedStub (fullBodyDigest ft) ft.lo ft.hi
  else
    match ft with
    | .present k rec =>
      if frustumAllowsEntry cf k rec then
        .present k rec
      else
        .blindedStub (presentBodyDigest k rec) k k
    | .emptyGap lo hi => .emptyGap lo hi
    | .branch l r => .branch (projectSubtree cf l) (projectSubtree cf r)

/-- Project an unredacted `FullStore` through `cf : CapFrustum`. -/
def projectPartialView (cf : CapFrustum) (fs : FullStore) : PartialView :=
  { worldRoot := fullStoreRoot fs
    viewFrustum := cf
    tree := projectSubtree cf fs.tree }

theorem projectSubtree_bounds (cf : CapFrustum) :
    ∀ (ft : FullTree), (projectSubtree cf ft).lo = ft.lo ∧ (projectSubtree cf ft).hi = ft.hi
  | .present k rec => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf k k = true <;>
    by_cases hA : frustumAllowsEntry cf k rec = true <;>
      simp [hT, hA, PartialViewTree.lo, PartialViewTree.hi]
  | .emptyGap lo hi => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf lo hi = true <;>
      simp [hT, PartialViewTree.lo, PartialViewTree.hi]
  | .branch l r => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf l.lo r.hi = true
    · simp [hT, PartialViewTree.lo, PartialViewTree.hi,
        (projectSubtree_bounds cf l).1, (projectSubtree_bounds cf r).2]
    · simp [hT, PartialViewTree.lo, PartialViewTree.hi]

/-- **Exact 256-Bit Root Invariance (`projectSubtree_root_eq`)**:
    Every capability-projected subtree hashes to the exact same `Digest256` as the unredacted subtree. -/
theorem projectSubtree_root_eq (cf : CapFrustum) :
    ∀ (ft : FullTree), partialNodeRoot (projectSubtree cf ft) = fullNodeRoot ft
  | .present k rec => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf k k = true <;>
    by_cases hA : frustumAllowsEntry cf k rec = true <;>
      simp [hT, hA, partialNodeRoot, fullNodeRoot, fullBodyDigest]
  | .emptyGap lo hi => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf lo hi = true <;>
      simp [hT, partialNodeRoot, fullNodeRoot, fullBodyDigest]
  | .branch l r => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf l.lo r.hi = true
    · simp [hT, partialNodeRoot, fullNodeRoot,
        projectSubtree_root_eq cf l, projectSubtree_root_eq cf r,
        (projectSubtree_bounds cf l).1, (projectSubtree_bounds cf r).2]
    · simp [hT, partialNodeRoot, fullNodeRoot, fullBodyDigest]

/-- **World-Root Invariance (`projectPartialView_root_eq`)**:
    Every projected `PartialView` hashes to the exact same 256-bit `worldRoot` as `FullStore`. -/
theorem projectPartialView_root_eq (cf : CapFrustum) (fs : FullStore) :
    partialViewRoot (projectPartialView cf fs) = fullStoreRoot fs ∧
    (projectPartialView cf fs).worldRoot = fullStoreRoot fs :=
  ⟨projectSubtree_root_eq cf fs.tree, rfl⟩

theorem projectSubtree_wf (cf : CapFrustum) :
    ∀ {ft : FullTree}, ft.wf = true → (projectSubtree cf ft).wf = true
  | .present k rec, _ => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf k k = true <;>
    by_cases hA : frustumAllowsEntry cf k rec = true <;>
      simp [hT, hA, PartialViewTree.wf]
  | .emptyGap lo hi, h => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf lo hi = true <;>
      simpa [hT, PartialViewTree.wf, FullTree.wf] using h
  | .branch l r, h => by
    have hlo_hi : l.lo.toNat ≤ r.hi.toNat := FullTree.wf_lo_le_hi (t := .branch l r) h
    simp only [FullTree.wf, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf l.lo r.hi = true
    · simp only [hT, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        PartialViewTree.wf, Bool.and_eq_true, decide_eq_true_eq,
        (projectSubtree_bounds cf l).2, (projectSubtree_bounds cf r).1]
      exact ⟨⟨projectSubtree_wf cf h.1.1, projectSubtree_wf cf h.1.2⟩, h.2⟩
    · simp [hT, PartialViewTree.wf, hlo_hi]

/-- Visible `.present` entries exposed in cleartext by a `PartialViewTree`. -/
def PartialViewTree.visibleEntries : PartialViewTree → List (Key256 × ObjRecord)
  | .present k rec => [(k, rec)]
  | .blindedStub _ _ _ => []
  | .emptyGap _ _ => []
  | .branch l r => l.visibleEntries ++ r.visibleEntries

def FullTree.entries : FullTree → List (Key256 × ObjRecord)
  | .present k rec => [(k, rec)]
  | .emptyGap _ _ => []
  | .branch l r => l.entries ++ r.entries

theorem FullTree.entries_mem_bounds :
    ∀ {ft : FullTree} {k : Key256} {rec : ObjRecord},
      ft.wf = true → (k, rec) ∈ ft.entries → ft.lo.toNat ≤ k.toNat ∧ k.toNat ≤ ft.hi.toNat
  | .present key r, k, rec, _, hmem => by
    simp only [FullTree.entries, List.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, _⟩
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | .emptyGap _ _, _, _, _, hmem => by cases hmem
  | .branch l r, k, rec, hwf, hmem => by
    simp only [FullTree.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have hl_span := l.wf_lo_le_hi hwf.1.1
    have hr_span := r.wf_lo_le_hi hwf.1.2
    simp only [FullTree.entries, List.mem_append] at hmem
    simp only [FullTree.lo, FullTree.hi]
    rcases hmem with hmemL | hmemR
    · obtain ⟨h1, h2⟩ := l.entries_mem_bounds hwf.1.1 hmemL
      omega
    · obtain ⟨h1, h2⟩ := r.entries_mem_bounds hwf.1.2 hmemR
      omega

theorem projectSubtree_visibleEntries_eq (cf : CapFrustum) :
    ∀ {ft : FullTree}, ft.wf = true →
      (projectSubtree cf ft).visibleEntries =
        ft.entries.filter (fun kv => frustumAllowsEntry cf kv.1 kv.2)
  | .present k rec, _ => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hTouch : frustumTouchesSpan cf k k = true
    · simp only [hTouch, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hAllow : frustumAllowsEntry cf k rec = true <;>
        simp [hAllow, PartialViewTree.visibleEntries, FullTree.entries]
    · have hTouchF : frustumTouchesSpan cf k k = false := Bool.eq_false_iff.mpr hTouch
      have hCovF := frustumCoversKey_false_of_touchesSpan_false hTouchF (Nat.le_refl _) (Nat.le_refl _)
      have hAllowF : frustumAllowsEntry cf k rec = false := by simp [frustumAllowsEntry, hCovF]
      simp [hTouchF, hAllowF, PartialViewTree.visibleEntries, FullTree.entries]
  | .emptyGap lo hi, _ => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf lo hi = true <;>
      simp [hT, PartialViewTree.visibleEntries, FullTree.entries]
  | .branch l r, hwf => by
    by_cases hTouch : frustumTouchesSpan cf l.lo r.hi = true
    · simp only [FullTree.wf, Bool.and_eq_true] at hwf
      simp only [projectSubtree, FullTree.lo, FullTree.hi, hTouch, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, PartialViewTree.visibleEntries, FullTree.entries,
        List.filter_append, projectSubtree_visibleEntries_eq cf hwf.1.1,
        projectSubtree_visibleEntries_eq cf hwf.1.2]
    · have hTouchF : frustumTouchesSpan cf l.lo r.hi = false := Bool.eq_false_iff.mpr hTouch
      simp only [projectSubtree, FullTree.lo, FullTree.hi, hTouchF, Bool.not_false, ↓reduceIte,
        PartialViewTree.visibleEntries]
      symm
      rw [List.filter_eq_nil_iff]
      intro kv hmem
      obtain ⟨hkLo, hkHi⟩ := FullTree.entries_mem_bounds (ft := .branch l r) hwf hmem
      have hCovF := frustumCoversKey_false_of_touchesSpan_false hTouchF hkLo hkHi
      simp [frustumAllowsEntry, hCovF]

/-- **Confidentiality / Redaction Projection (`projectPartialView_confidential`)**:
    1. Visible cleartext entries in `projectPartialView cf fs` equal the exact capability-filtered
       entries of `fs`;
    2. Every unauthorized secret record (`frustumAllowsEntry cf k rec = false`) is structurally
       absent from all `.present` nodes of the projected tree (replaced solely by salted 256-bit
       `.blindedStub` digests). -/
theorem projectPartialView_confidential (cf : CapFrustum) (fs : FullStore)
    (hwf : fs.tree.wf = true) :
    (projectPartialView cf fs).tree.visibleEntries =
      fs.tree.entries.filter (fun kv => frustumAllowsEntry cf kv.1 kv.2) ∧
    (∀ k rec, frustumAllowsEntry cf k rec = false →
      (k, rec) ∉ (projectPartialView cf fs).tree.visibleEntries) := by
  have heq := projectSubtree_visibleEntries_eq cf hwf
  refine ⟨heq, fun k rec hforb hmem => ?_⟩
  dsimp only [projectPartialView] at hmem
  rw [heq, List.mem_filter] at hmem
  rw [hforb] at hmem
  cases hmem.2

/-! ## 3. Authenticated Point Lookup & Range Non-Omission (`rangeScanPartial`) -/

def FullTree.lookup : FullTree → Key256 → Option ObjRecord
  | .present key rec, k => if k == key then some rec else none
  | .emptyGap _ _, _ => none
  | .branch l r, k => if k.toNat ≤ l.hi.toNat then l.lookup k else r.lookup k

theorem FullTree.lookup_some_iff_mem_entries :
    ∀ {ft : FullTree}, ft.wf = true → ∀ (k : Key256) (rec : ObjRecord),
      ft.lookup k = some rec ↔ (k, rec) ∈ ft.entries
  | .present key r, _, k, rec => by
    simp only [FullTree.lookup, FullTree.entries, List.mem_singleton, Prod.mk.injEq]
    by_cases hk : k = key
    · subst hk; simp [eq_comm]
    · have hne : (k == key) = false := beq_false_of_ne hk
      simp [hne, hk]
  | .emptyGap _ _, _, _, _ => by
    simp [FullTree.lookup, FullTree.entries]
  | .branch l r, hwf, k, rec => by
    simp only [FullTree.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [FullTree.lookup, FullTree.entries, List.mem_append]
    by_cases hle : k.toNat ≤ l.hi.toNat
    · simp only [hle, ↓reduceIte, l.lookup_some_iff_mem_entries hwf.1.1 k rec]
      constructor
      · exact Or.inl
      · rintro (hl | hr)
        · exact hl
        · obtain ⟨hrLo, _⟩ := r.entries_mem_bounds hwf.1.2 hr
          omega
    · simp only [hle, ↓reduceIte, r.lookup_some_iff_mem_entries hwf.1.2 k rec]
      constructor
      · exact Or.inr
      · rintro (hl | hr)
        · obtain ⟨_, hlHi⟩ := l.entries_mem_bounds hwf.1.1 hl
          omega
        · exact hr

def fullRangeEntries (ft : FullTree) (qLo qHi : Key256) : List (Key256 × ObjRecord) :=
  ft.entries.filter (fun kv => inKeyRange qLo qHi kv.1)

/-- Outcome of scanning `[qLo, qHi]` against an untrusted `PartialViewTree`. -/
inductive RangeScanResult where
  | complete        (entries : List (Key256 × ObjRecord))
  | redactedOverlap (stubLo stubHi : Key256)
  | malformedView
deriving DecidableEq, Repr

def verifyPartialView (pt : PartialViewTree) (expectedRoot : Digest256) : Bool :=
  pt.wf && (partialNodeRoot pt == expectedRoot)

def rangeScanSubtree (pt : PartialViewTree) (qLo qHi : Key256) : RangeScanResult :=
  if !rangesOverlap pt.lo pt.hi qLo qHi then
    .complete []
  else
    match pt with
    | .present k rec =>
      if inKeyRange qLo qHi k then .complete [(k, rec)] else .complete []
    | .emptyGap _ _ =>
      .complete []
    | .blindedStub _ sLo sHi =>
      .redactedOverlap sLo sHi
    | .branch l r =>
      match rangeScanSubtree l qLo qHi with
      | .complete lEnts =>
        match rangeScanSubtree r qLo qHi with
        | .complete rEnts => .complete (lEnts ++ rEnts)
        | err => err
      | err => err

/-- Stranger-verifiable range scan over `[qLo, qHi]`: verifies `pt.wf`, checks `partialNodeRoot pt == expectedRoot`,
    checks `[qLo, qHi] ⊆ [pt.lo, pt.hi]`, and rejects if any `.blindedStub` overlaps `[qLo, qHi]`. -/
def rangeScanPartial (pv : PartialView) (expectedRoot : Digest256) (qLo qHi : Key256) : RangeScanResult :=
  if !verifyPartialView pv.tree expectedRoot then
    .malformedView
  else if !(decide (qLo.toNat ≤ qHi.toNat) && decide (pv.tree.lo.toNat ≤ qLo.toNat) &&
            decide (qHi.toNat ≤ pv.tree.hi.toNat)) then
    .malformedView
  else
    rangeScanSubtree pv.tree qLo qHi

theorem not_inKeyRange_of_rangesOverlap_false
    {tLo tHi qLo qHi k : Key256}
    (hOver : rangesOverlap tLo tHi qLo qHi = false)
    (hkLo : tLo.toNat ≤ k.toNat) (hkHi : k.toNat ≤ tHi.toNat) :
    inKeyRange qLo qHi k = false := by
  unfold rangesOverlap at hOver
  unfold inKeyRange
  by_cases hq1 : qLo.toNat ≤ k.toNat
  · by_cases hq2 : k.toNat ≤ qHi.toNat
    · have ha : tLo.toNat ≤ qHi.toNat := Nat.le_trans hkLo hq2
      have hb : qLo.toNat ≤ tHi.toNat := Nat.le_trans hq1 hkHi
      simp [ha, hb] at hOver
    · simp [hq2]
  · simp [hq1]

theorem fullRangeEntries_nil_of_rangesOverlap_false
    {ft : FullTree} {qLo qHi : Key256}
    (hwf : ft.wf = true) (hOver : rangesOverlap ft.lo ft.hi qLo qHi = false) :
    fullRangeEntries ft qLo qHi = [] := by
  unfold fullRangeEntries
  rw [List.filter_eq_nil_iff]
  intro kv hmem
  obtain ⟨hkLo, hkHi⟩ := ft.entries_mem_bounds hwf hmem
  simp [not_inKeyRange_of_rangesOverlap_false hOver hkLo hkHi]

theorem rangeScanSubtree_sound_or_collision
    (ft : FullTree) (pt : PartialViewTree) (qLo qHi : Key256) (entries : List (Key256 × ObjRecord))
    (hwf : ft.wf = true)
    (hroot : partialNodeRoot pt = fullNodeRoot ft)
    (hscan : rangeScanSubtree pt qLo qHi = .complete entries) :
    entries = fullRangeEntries ft qLo qHi ∨
      CollisionAmong cpvHashBytes (fun m => m ∈ fullTreePreimages ft ++ partialTreePreimages pt) := by
  induction ft generalizing pt entries with
  | present k' rec' =>
    rw [partialNodeRoot_eq_stubCommit, fullNodeRoot_eq_stubCommit] at hroot
    unfold stubCommit at hroot
    rcases cpvHash256_binds_scoped hroot with hstubPre | hc
    · obtain ⟨hlo, hhi, hbody⟩ := stubCommitPreimage_injective hstubPre
      unfold rangeScanSubtree at hscan
      by_cases hOver : rangesOverlap pt.lo pt.hi qLo qHi = true
      · simp only [hOver, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hscan
        cases pt with
        | blindedStub _ _ _ => cases hscan
        | present k rec =>
          dsimp only at hscan
          dsimp only [partialBodyDigest, fullBodyDigest, presentBodyDigest] at hbody
          rcases cpvHash256_binds_scoped hbody with hpres | hc
          · obtain ⟨hk, hrec⟩ := presentBodyPreimage_injective hpres
            subst hk; subst hrec
            by_cases hin : inKeyRange qLo qHi k = true
            · simp only [hin, ↓reduceIte, RangeScanResult.complete.injEq] at hscan
              subst hscan
              exact .inl (by simp [fullRangeEntries, FullTree.entries, hin])
            · have hinF := Bool.eq_false_iff.mpr hin
              simp only [hinF, Bool.false_eq_true, ↓reduceIte, RangeScanResult.complete.injEq] at hscan
              subst hscan
              exact .inl (by simp [fullRangeEntries, FullTree.entries, hinF])
          · exact .inr (hc.mono fun _ hm => by
              rcases hm with rfl | rfl <;> simp [fullTreePreimages, partialTreePreimages])
        | emptyGap lo hi =>
          dsimp only [partialBodyDigest, fullBodyDigest, emptyBodyDigest, presentBodyDigest] at hbody
          rcases cpvHash256_binds_scoped hbody with hp | hc
          · have hf := frameFields_injective hp
            have hne : emptyGapTag ≠ presentNodeTag := by decide
            exact False.elim (hne (List.cons.inj hf).1)
          · exact .inr (hc.mono fun _ hm => by
              rcases hm with rfl | rfl <;> simp [fullTreePreimages, partialTreePreimages])
        | branch l r =>
          dsimp only [partialBodyDigest, fullBodyDigest, branchBodyDigest, presentBodyDigest] at hbody
          rcases cpvHash256_binds_scoped hbody with hp | hc
          · have hf := frameFields_injective hp
            have hne : branchNodeTag ≠ presentNodeTag := by decide
            exact False.elim (hne (List.cons.inj hf).1)
          · exact .inr (hc.mono fun _ hm => by
              rcases hm with rfl | rfl <;> simp [fullTreePreimages, partialTreePreimages])
      · have hOverF : rangesOverlap pt.lo pt.hi qLo qHi = false := Bool.eq_false_iff.mpr hOver
        simp only [hOverF, Bool.not_false, ↓reduceIte, RangeScanResult.complete.injEq] at hscan
        subst hscan
        rw [hlo, hhi] at hOverF
        exact .inl (fullRangeEntries_nil_of_rangesOverlap_false hwf hOverF).symm
    · exact .inr (hc.mono fun _ hm => by
        rcases hm with rfl | rfl
        · exact List.mem_append_right _ (stubPreimage_mem_partialTreePreimages pt)
        · exact List.mem_append_left _ (stubPreimage_mem_fullTreePreimages (.present k' rec')))
  | emptyGap lo' hi' =>
    rw [partialNodeRoot_eq_stubCommit, fullNodeRoot_eq_stubCommit] at hroot
    unfold stubCommit at hroot
    rcases cpvHash256_binds_scoped hroot with hstubPre | hc
    · obtain ⟨hlo, hhi, hbody⟩ := stubCommitPreimage_injective hstubPre
      unfold rangeScanSubtree at hscan
      by_cases hOver : rangesOverlap pt.lo pt.hi qLo qHi = true
      · simp only [hOver, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hscan
        cases pt with
        | blindedStub _ _ _ => cases hscan
        | emptyGap lo hi =>
          simp only [RangeScanResult.complete.injEq] at hscan
          subst hscan
          exact .inl rfl
        | present k rec =>
          dsimp only [partialBodyDigest, fullBodyDigest, presentBodyDigest, emptyBodyDigest] at hbody
          rcases cpvHash256_binds_scoped hbody with hp | hc
          · have hf := frameFields_injective hp
            have hne : presentNodeTag ≠ emptyGapTag := by decide
            exact False.elim (hne (List.cons.inj hf).1)
          · exact .inr (hc.mono fun _ hm => by
              rcases hm with rfl | rfl <;> simp [fullTreePreimages, partialTreePreimages])
        | branch l r =>
          dsimp only [partialBodyDigest, fullBodyDigest, branchBodyDigest, emptyBodyDigest] at hbody
          rcases cpvHash256_binds_scoped hbody with hp | hc
          · have hf := frameFields_injective hp
            have hne : branchNodeTag ≠ emptyGapTag := by decide
            exact False.elim (hne (List.cons.inj hf).1)
          · exact .inr (hc.mono fun _ hm => by
              rcases hm with rfl | rfl <;> simp [fullTreePreimages, partialTreePreimages])
      · have hOverF : rangesOverlap pt.lo pt.hi qLo qHi = false := Bool.eq_false_iff.mpr hOver
        simp only [hOverF, Bool.not_false, ↓reduceIte, RangeScanResult.complete.injEq] at hscan
        subst hscan
        rw [hlo, hhi] at hOverF
        exact .inl (fullRangeEntries_nil_of_rangesOverlap_false hwf hOverF).symm
    · exact .inr (hc.mono fun _ hm => by
        rcases hm with rfl | rfl
        · exact List.mem_append_right _ (stubPreimage_mem_partialTreePreimages pt)
        · exact List.mem_append_left _ (stubPreimage_mem_fullTreePreimages (.emptyGap lo' hi')))
  | branch l' r' ihl ihr =>
    rw [partialNodeRoot_eq_stubCommit, fullNodeRoot_eq_stubCommit] at hroot
    unfold stubCommit at hroot
    rcases cpvHash256_binds_scoped hroot with hstubPre | hc
    · obtain ⟨hlo, hhi, hbody⟩ := stubCommitPreimage_injective hstubPre
      unfold rangeScanSubtree at hscan
      by_cases hOver : rangesOverlap pt.lo pt.hi qLo qHi = true
      · simp only [hOver, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hscan
        cases pt with
        | blindedStub _ _ _ => cases hscan
        | present k rec =>
          dsimp only [partialBodyDigest, fullBodyDigest, presentBodyDigest, branchBodyDigest] at hbody
          rcases cpvHash256_binds_scoped hbody with hp | hc
          · have hf := frameFields_injective hp
            have hne : presentNodeTag ≠ branchNodeTag := by decide
            exact False.elim (hne (List.cons.inj hf).1)
          · exact .inr (hc.mono fun _ hm => by
              rcases hm with rfl | rfl <;> simp [fullTreePreimages, partialTreePreimages])
        | emptyGap lo hi =>
          dsimp only [partialBodyDigest, fullBodyDigest, emptyBodyDigest, branchBodyDigest] at hbody
          rcases cpvHash256_binds_scoped hbody with hp | hc
          · have hf := frameFields_injective hp
            have hne : emptyGapTag ≠ branchNodeTag := by decide
            exact False.elim (hne (List.cons.inj hf).1)
          · exact .inr (hc.mono fun _ hm => by
              rcases hm with rfl | rfl <;> simp [fullTreePreimages, partialTreePreimages])
        | branch l r =>
          dsimp only at hscan
          simp only [FullTree.wf, Bool.and_eq_true] at hwf
          dsimp only [partialBodyDigest, fullBodyDigest, branchBodyDigest] at hbody
          rcases cpvHash256_binds_scoped hbody with hp | hc
          · obtain ⟨hlRoot, hrRoot⟩ := branchBodyPreimage_injective hp
            cases hL : rangeScanSubtree l qLo qHi with
            | redactedOverlap _ _ => rw [hL] at hscan; cases hscan
            | malformedView => rw [hL] at hscan; cases hscan
            | complete lEnts =>
              rw [hL] at hscan
              cases hR : rangeScanSubtree r qLo qHi with
              | redactedOverlap _ _ => rw [hR] at hscan; cases hscan
              | malformedView => rw [hR] at hscan; cases hscan
              | complete rEnts =>
                rw [hR] at hscan
                simp only [RangeScanResult.complete.injEq] at hscan
                rcases ihl l lEnts hwf.1.1 hlRoot hL with hlEq | hc
                · rcases ihr r rEnts hwf.1.2 hrRoot hR with hrEq | hc
                  · subst hscan; subst hlEq; subst hrEq
                    simp [fullRangeEntries, FullTree.entries, List.filter_append]
                  · exact .inr (hc.mono fun m hm => by
                      simp only [List.mem_append, fullTreePreimages, partialTreePreimages, List.mem_cons] at hm ⊢
                      rcases hm with hm | hm
                      · exact .inl (.inr (.inr (.inr hm)))
                      · exact .inr (.inr (.inr (.inr hm))))
                · exact .inr (hc.mono fun m hm => by
                    simp only [List.mem_append, fullTreePreimages, partialTreePreimages, List.mem_cons] at hm ⊢
                    rcases hm with hm | hm
                    · exact .inl (.inr (.inr (.inl hm)))
                    · exact .inr (.inr (.inr (.inl hm))))
          · exact .inr (hc.mono fun _ hm => by
              rcases hm with rfl | rfl <;> simp [fullTreePreimages, partialTreePreimages])
      · have hOverF : rangesOverlap pt.lo pt.hi qLo qHi = false := Bool.eq_false_iff.mpr hOver
        simp only [hOverF, Bool.not_false, ↓reduceIte, RangeScanResult.complete.injEq] at hscan
        subst hscan
        rw [hlo, hhi] at hOverF
        exact .inl (fullRangeEntries_nil_of_rangesOverlap_false hwf hOverF).symm
    · exact .inr (hc.mono fun _ hm => by
        rcases hm with rfl | rfl
        · exact List.mem_append_right _ (stubPreimage_mem_partialTreePreimages pt)
        · exact List.mem_append_left _ (stubPreimage_mem_fullTreePreimages (.branch l' r')))

/-- **Range Non-Omission Theorem (`rangeScanPartial_sound_or_collision`)**:
    Whenever `rangeScanPartial pv (fullStoreRoot fs) qLo qHi = .complete entries` succeeds,
    `entries` equals `fullRangeEntries fs.tree qLo qHi` — ZERO matching keys in `[qLo, qHi]`
    were omitted and ZERO bogus keys were injected — or `cpvHashBytes` collides among the
    explicit finite preimages of `fs.tree` and `pv.tree`. -/
theorem rangeScanPartial_sound_or_collision
    (fs : FullStore) (pv : PartialView) (qLo qHi : Key256) (entries : List (Key256 × ObjRecord))
    (hfs : fs.tree.wf = true)
    (hscan : rangeScanPartial pv (fullStoreRoot fs) qLo qHi = .complete entries) :
    (entries = fullRangeEntries fs.tree qLo qHi ∧
     ∀ k rec, (k, rec) ∈ fs.tree.entries → inKeyRange qLo qHi k = true → (k, rec) ∈ entries) ∨
    CollisionAmong cpvHashBytes (fun m => m ∈ fullTreePreimages fs.tree ++ partialTreePreimages pv.tree) := by
  unfold rangeScanPartial verifyPartialView at hscan
  by_cases hv : (pv.tree.wf && (partialNodeRoot pv.tree == fullStoreRoot fs)) = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hscan
    split at hscan
    · cases hscan
    · simp only [Bool.and_eq_true, beq_iff_eq] at hv
      rcases rangeScanSubtree_sound_or_collision fs.tree pv.tree qLo qHi entries hfs hv.2 hscan with heq | hc
      · refine .inl ⟨heq, fun k rec hmem hin => ?_⟩
        rw [heq]
        exact List.mem_filter.mpr ⟨hmem, hin⟩
      · exact .inr hc
  · have hvF : (pv.tree.wf && (partialNodeRoot pv.tree == fullStoreRoot fs)) = false :=
      Bool.eq_false_iff.mpr hv
    simp [hvF] at hscan

/-- Completeness of `rangeScanPartial` on an unblinded singleton store. -/
theorem rangeScanPartial_singleton_complete (k : Key256) (rec : ObjRecord) :
    let fs : FullStore := ⟨.present k rec⟩
    let cf : CapFrustum := { heldAuths := rec.required, allowedRanges := [(k, k)] }
    rangeScanPartial (projectPartialView cf fs) (fullStoreRoot fs) k k = .complete [(k, rec)] := by
  have hgate : fireGate rec.required rec.required = true := by
    rw [Obend.Vault.Affordance.fireGate_iff_subset]
    intro a ha; exact ha
  simp [rangeScanPartial, verifyPartialView, projectPartialView, projectSubtree,
    frustumTouchesSpan, frustumAllowsEntry, frustumCoversKey,
    rangesOverlap, inKeyRange, PartialViewTree.wf, PartialViewTree.lo, PartialViewTree.hi,
    FullTree.lo, FullTree.hi, fullStoreRoot, partialNodeRoot, fullNodeRoot,
    rangeScanSubtree, hgate]

/-- Structural consistency relation between unredacted `FullTree` and redacted `PartialViewTree`. -/
inductive PartialViewSubtreeConsistent : FullTree → PartialViewTree → Prop where
  | present (k : Key256) (rec : ObjRecord) :
      PartialViewSubtreeConsistent (.present k rec) (.present k rec)
  | emptyGap (lo hi : Key256) (hle : lo.toNat ≤ hi.toNat) :
      PartialViewSubtreeConsistent (.emptyGap lo hi) (.emptyGap lo hi)
  | blinded (ft : FullTree) (hwf : ft.wf = true) :
      PartialViewSubtreeConsistent ft (.blindedStub (fullBodyDigest ft) ft.lo ft.hi)
  | branch {fl fr : FullTree} {pl pr : PartialViewTree}
      (hadj : fl.hi.toNat + 1 = fr.lo.toNat)
      (hl : PartialViewSubtreeConsistent fl pl)
      (hr : PartialViewSubtreeConsistent fr pr) :
      PartialViewSubtreeConsistent (.branch fl fr) (.branch pl pr)

/-- Full consistency between `fs : FullStore` and `pv : PartialView`. -/
def PartialViewConsistent (fs : FullStore) (pv : PartialView) : Prop :=
  fs.tree.wf = true ∧
  pv.tree.wf = true ∧
  pv.worldRoot = fullStoreRoot fs ∧
  PartialViewSubtreeConsistent fs.tree pv.tree

/-- Constructive `PSum` subtree consistency / collision extractor (`0 Classical.choice`). -/
def extractSubtreeConsistency :
    (ft : FullTree) → (pt : PartialViewTree) →
    ft.wf = true → pt.wf = true →
    partialNodeRoot pt = fullNodeRoot ft →
    PSum (PartialViewSubtreeConsistent ft pt) (CshakeCollisionWitness cpvHashBytes)
  | ft, pt, hfwf, hpwf, hroot =>
    have hstubEq : cpvHash256 (stubCommitPreimage pt.lo pt.hi (partialBodyDigest pt)) =
        cpvHash256 (stubCommitPreimage ft.lo ft.hi (fullBodyDigest ft)) := by
      simpa only [partialNodeRoot_eq_stubCommit, fullNodeRoot_eq_stubCommit, stubCommit] using hroot
    match cpvHash256_binds_psum hstubEq with
    | .inr w => .inr w
    | .inl hstubPre =>
      let ⟨hlo, hhi, hbody⟩ := stubCommitPreimage_injective hstubPre
      match pt with
      | .blindedStub d sLo sHi =>
        .inl (by
          simp only [PartialViewTree.lo, PartialViewTree.hi, partialBodyDigest] at hlo hhi hbody
          subst hlo; subst hhi; subst hbody
          exact .blinded ft hfwf)
      | .present k rec =>
        match ft with
        | .present k' rec' =>
          have hb : cpvHash256 (presentBodyPreimage k rec) = cpvHash256 (presentBodyPreimage k' rec') := hbody
          match cpvHash256_binds_psum hb with
          | .inr w => .inr w
          | .inl hp =>
            let ⟨hk, hrec⟩ := presentBodyPreimage_injective hp
            .inl (by subst hk; subst hrec; exact .present k rec)
        | .emptyGap lo' hi' =>
          have hb : cpvHash256 (presentBodyPreimage k rec) = cpvHash256 (emptyBodyPreimage lo' hi') := hbody
          match cpvHash256_binds_psum hb with
          | .inr w => .inr w
          | .inl hp =>
            False.elim ((by decide : presentNodeTag ≠ emptyGapTag) (List.cons.inj (frameFields_injective hp)).1)
        | .branch l' r' =>
          have hb : cpvHash256 (presentBodyPreimage k rec) =
              cpvHash256 (branchBodyPreimage (fullNodeRoot l') (fullNodeRoot r')) := hbody
          match cpvHash256_binds_psum hb with
          | .inr w => .inr w
          | .inl hp =>
            False.elim ((by decide : presentNodeTag ≠ branchNodeTag) (List.cons.inj (frameFields_injective hp)).1)
      | .emptyGap lo hi =>
        match ft with
        | .emptyGap lo' hi' =>
          .inl (by
            simp only [PartialViewTree.lo, PartialViewTree.hi, FullTree.lo, FullTree.hi] at hlo hhi
            subst hlo; subst hhi
            exact .emptyGap lo hi (of_decide_eq_true hpwf))
        | .present k' rec' =>
          have hb : cpvHash256 (emptyBodyPreimage lo hi) = cpvHash256 (presentBodyPreimage k' rec') := hbody
          match cpvHash256_binds_psum hb with
          | .inr w => .inr w
          | .inl hp =>
            False.elim ((by decide : emptyGapTag ≠ presentNodeTag) (List.cons.inj (frameFields_injective hp)).1)
        | .branch l' r' =>
          have hb : cpvHash256 (emptyBodyPreimage lo hi) =
              cpvHash256 (branchBodyPreimage (fullNodeRoot l') (fullNodeRoot r')) := hbody
          match cpvHash256_binds_psum hb with
          | .inr w => .inr w
          | .inl hp =>
            False.elim ((by decide : emptyGapTag ≠ branchNodeTag) (List.cons.inj (frameFields_injective hp)).1)
      | .branch pl pr =>
        match ft with
        | .present k' rec' =>
          have hb : cpvHash256 (branchBodyPreimage (partialNodeRoot pl) (partialNodeRoot pr)) =
              cpvHash256 (presentBodyPreimage k' rec') := hbody
          match cpvHash256_binds_psum hb with
          | .inr w => .inr w
          | .inl hp =>
            False.elim ((by decide : branchNodeTag ≠ presentNodeTag) (List.cons.inj (frameFields_injective hp)).1)
        | .emptyGap lo' hi' =>
          have hb : cpvHash256 (branchBodyPreimage (partialNodeRoot pl) (partialNodeRoot pr)) =
              cpvHash256 (emptyBodyPreimage lo' hi') := hbody
          match cpvHash256_binds_psum hb with
          | .inr w => .inr w
          | .inl hp =>
            False.elim ((by decide : branchNodeTag ≠ emptyGapTag) (List.cons.inj (frameFields_injective hp)).1)
        | .branch fl fr =>
          have hb : cpvHash256 (branchBodyPreimage (partialNodeRoot pl) (partialNodeRoot pr)) =
              cpvHash256 (branchBodyPreimage (fullNodeRoot fl) (fullNodeRoot fr)) := hbody
          match cpvHash256_binds_psum hb with
          | .inr w => .inr w
          | .inl hp =>
            let ⟨hlRoot, hrRoot⟩ := branchBodyPreimage_injective hp
            have hfSplit : (fl.wf = true ∧ fr.wf = true) ∧ fl.hi.toNat + 1 = fr.lo.toNat := by
              simpa [FullTree.wf, Bool.and_eq_true, decide_eq_true_eq] using hfwf
            have hpSplit : (pl.wf = true ∧ pr.wf = true) ∧ pl.hi.toNat + 1 = pr.lo.toNat := by
              simpa [PartialViewTree.wf, Bool.and_eq_true, decide_eq_true_eq] using hpwf
            match extractSubtreeConsistency fl pl hfSplit.1.1 hpSplit.1.1 hlRoot with
            | .inr w => .inr w
            | .inl hcl =>
              match extractSubtreeConsistency fr pr hfSplit.1.2 hpSplit.1.2 hrRoot with
              | .inr w => .inr w
              | .inl hcr => .inl (.branch hfSplit.2 hcl hcr)

theorem consistent_bounds {ft : FullTree} {pt : PartialViewTree}
    (hc : PartialViewSubtreeConsistent ft pt) :
    pt.lo = ft.lo ∧ pt.hi = ft.hi ∧ partialNodeRoot pt = fullNodeRoot ft := by
  induction hc with
  | present k rec => exact ⟨rfl, rfl, rfl⟩
  | emptyGap lo hi _ => exact ⟨rfl, rfl, rfl⟩
  | blinded ft _ => exact ⟨rfl, rfl, (fullNodeRoot_eq_stubCommit ft).symm⟩
  | branch _ _ _ ihl ihr =>
    refine ⟨ihl.1, ihr.2.1, ?_⟩
    simp [partialNodeRoot, fullNodeRoot, ihl.1, ihr.2.1, ihl.2.2, ihr.2.2]

theorem PartialViewConsistent.root_eq {fs : FullStore} {pv : PartialView}
    (hc : PartialViewConsistent fs pv) :
    partialViewRoot pv = fullStoreRoot fs :=
  (consistent_bounds hc.2.2.2).2.2

theorem projectSubtree_consistent (cf : CapFrustum) :
    ∀ {ft : FullTree}, ft.wf = true → PartialViewSubtreeConsistent ft (projectSubtree cf ft)
  | .present k rec, hf => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf k k = true
    · simp only [hT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hA : frustumAllowsEntry cf k rec = true
      · simp only [hA, ↓reduceIte]
        exact .present k rec
      · have hAF := Bool.eq_false_iff.mpr hA
        simp only [hAF, Bool.false_eq_true, ↓reduceIte]
        exact .blinded (.present k rec) hf
    · have hTF := Bool.eq_false_iff.mpr hT
      simp only [hTF, Bool.not_false, ↓reduceIte]
      exact .blinded (.present k rec) hf
  | .emptyGap lo hi, hf => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf lo hi = true
    · simp only [hT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact .emptyGap lo hi (of_decide_eq_true hf)
    · have hTF := Bool.eq_false_iff.mpr hT
      simp only [hTF, Bool.not_false, ↓reduceIte]
      exact .blinded (.emptyGap lo hi) hf
  | .branch l r, hf => by
    simp only [projectSubtree, FullTree.lo, FullTree.hi]
    by_cases hT : frustumTouchesSpan cf l.lo r.hi = true
    · simp only [hT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hf' : (l.wf = true ∧ r.wf = true) ∧ l.hi.toNat + 1 = r.lo.toNat := by
        simpa [FullTree.wf, Bool.and_eq_true, decide_eq_true_eq] using hf
      exact .branch hf'.2 (projectSubtree_consistent cf hf'.1.1) (projectSubtree_consistent cf hf'.1.2)
    · have hTF := Bool.eq_false_iff.mpr hT
      simp only [hTF, Bool.not_false, ↓reduceIte]
      exact .blinded (.branch l r) hf

theorem projectPartialView_consistent (cf : CapFrustum) (fs : FullStore)
    (hwf : fs.tree.wf = true) :
    PartialViewConsistent fs (projectPartialView cf fs) :=
  ⟨hwf, projectSubtree_wf cf hwf, rfl, projectSubtree_consistent cf hwf⟩

theorem rangeScanSubtree_eq_of_consistent {qLo qHi : Key256}
    {ft : FullTree} {pt : PartialViewTree} {ents : List (Key256 × ObjRecord)}
    (hfw : ft.wf = true)
    (hc : PartialViewSubtreeConsistent ft pt)
    (hsc : rangeScanSubtree pt qLo qHi = .complete ents) :
    ents = fullRangeEntries ft qLo qHi := by
  induction hc generalizing ents with
  | present k rec =>
    unfold rangeScanSubtree at hsc
    by_cases hOver : rangesOverlap k k qLo qHi = true
    · simp only [PartialViewTree.lo, PartialViewTree.hi, hOver, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte] at hsc
      by_cases hin : inKeyRange qLo qHi k = true
      · simp only [hin, ↓reduceIte, RangeScanResult.complete.injEq] at hsc
        subst hsc
        simp [fullRangeEntries, FullTree.entries, hin]
      · have hinF := Bool.eq_false_iff.mpr hin
        simp only [hinF, Bool.false_eq_true, ↓reduceIte, RangeScanResult.complete.injEq] at hsc
        subst hsc
        simp [fullRangeEntries, FullTree.entries, hinF]
    · have hOverF := Bool.eq_false_iff.mpr hOver
      simp only [PartialViewTree.lo, PartialViewTree.hi, hOverF, Bool.not_false,
        ↓reduceIte, RangeScanResult.complete.injEq] at hsc
      subst hsc
      exact (fullRangeEntries_nil_of_rangesOverlap_false hfw hOverF).symm
  | emptyGap lo hi _ =>
    unfold rangeScanSubtree at hsc
    by_cases hOver : rangesOverlap lo hi qLo qHi = true
    · simp only [PartialViewTree.lo, PartialViewTree.hi, hOver, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, RangeScanResult.complete.injEq] at hsc
      subst hsc; rfl
    · have hOverF := Bool.eq_false_iff.mpr hOver
      simp only [PartialViewTree.lo, PartialViewTree.hi, hOverF, Bool.not_false,
        ↓reduceIte, RangeScanResult.complete.injEq] at hsc
      subst hsc; rfl
  | blinded bft _ =>
    unfold rangeScanSubtree at hsc
    by_cases hOver : rangesOverlap bft.lo bft.hi qLo qHi = true
    · simp [PartialViewTree.lo, PartialViewTree.hi, hOver] at hsc
    · have hOverF := Bool.eq_false_iff.mpr hOver
      simp only [PartialViewTree.lo, PartialViewTree.hi, hOverF, Bool.not_false,
        ↓reduceIte, RangeScanResult.complete.injEq] at hsc
      subst hsc
      exact (fullRangeEntries_nil_of_rangesOverlap_false hfw hOverF).symm
  | @branch fl fr pl pr hadj hcl hcr ihl ihr =>
    have hfw' : (fl.wf = true ∧ fr.wf = true) ∧ fl.hi.toNat + 1 = fr.lo.toNat := by
      simpa [FullTree.wf, Bool.and_eq_true, decide_eq_true_eq] using hfw
    unfold rangeScanSubtree at hsc
    by_cases hOver : rangesOverlap pl.lo pr.hi qLo qHi = true
    · simp only [PartialViewTree.lo, PartialViewTree.hi, hOver, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte] at hsc
      cases hL : rangeScanSubtree pl qLo qHi with
      | redactedOverlap _ _ => rw [hL] at hsc; cases hsc
      | malformedView => rw [hL] at hsc; cases hsc
      | complete lEnts =>
        rw [hL] at hsc
        cases hR : rangeScanSubtree pr qLo qHi with
        | redactedOverlap _ _ => rw [hR] at hsc; cases hsc
        | malformedView => rw [hR] at hsc; cases hsc
        | complete rEnts =>
          rw [hR] at hsc
          simp only [RangeScanResult.complete.injEq] at hsc
          subst hsc
          rw [ihl hfw'.1.1 hL, ihr hfw'.1.2 hR]
          simp [fullRangeEntries, FullTree.entries, List.filter_append]
    · have hOverF := Bool.eq_false_iff.mpr hOver
      simp only [PartialViewTree.lo, PartialViewTree.hi, hOverF, Bool.not_false,
        ↓reduceIte, RangeScanResult.complete.injEq] at hsc
      subst hsc
      rw [(consistent_bounds hcl).1, (consistent_bounds hcr).2.1] at hOverF
      exact (fullRangeEntries_nil_of_rangesOverlap_false hfw hOverF).symm

/-- Constructive `PSum` range-scan soundness extractor (`0 Classical.choice`):
    given `rangeScanPartial pv (fullStoreRoot fs) qLo qHi = .complete entries`, constructively
    returns either the exact non-omission proof or a `CshakeCollisionWitness` in `Type`. -/
def rangeScanPartial_sound_psum
    (fs : FullStore) (pv : PartialView) (qLo qHi : Key256) (entries : List (Key256 × ObjRecord))
    (hfs : fs.tree.wf = true)
    (hscan : rangeScanPartial pv (fullStoreRoot fs) qLo qHi = .complete entries) :
    PSum
      (entries = fullRangeEntries fs.tree qLo qHi ∧
       ∀ k rec, (k, rec) ∈ fs.tree.entries → inKeyRange qLo qHi k = true → (k, rec) ∈ entries)
      (CshakeCollisionWitness cpvHashBytes) :=
  have hv : pv.tree.wf = true ∧ partialNodeRoot pv.tree = fullStoreRoot fs := by
    unfold rangeScanPartial verifyPartialView at hscan
    by_cases h : (pv.tree.wf && (partialNodeRoot pv.tree == fullStoreRoot fs)) = true
    · simpa [Bool.and_eq_true, beq_iff_eq] using h
    · have hf := Bool.eq_false_iff.mpr h
      simp [hf] at hscan
  match extractSubtreeConsistency fs.tree pv.tree hfs hv.1 hv.2 with
  | .inr w => .inr w
  | .inl hcons =>
    .inl (by
      have hscanSub : rangeScanSubtree pv.tree qLo qHi = .complete entries := by
        unfold rangeScanPartial at hscan
        split at hscan
        · cases hscan
        · split at hscan
          · cases hscan
          · exact hscan
      have heq := rangeScanSubtree_eq_of_consistent hfs hcons hscanSub
      exact ⟨heq, fun k rec hm hin => by rw [heq]; exact List.mem_filter.mpr ⟨hm, hin⟩⟩)

/-! ## 4. Certified Partial Evaluation Membrane (`CertifiedPeval` & Multi-Turn `ValidMembraneTrace`) -/

/-- First-order / linear expression AST evaluated across the partial-view membrane. -/
inductive PExpr where
  | lit     (n : Nat)
  | proj    (key : Key256) (fieldId : Nat)
  | scale   (coeff : Nat) (body : PExpr)
  | add     (lhs rhs : PExpr)
  | sub     (lhs rhs : PExpr)
  | ifLe    (lhs rhs thenBr elseBr : PExpr)
  | recProj (pickSecond : Bool) (slot0 slot1 : PExpr)
deriving DecidableEq, Repr

/-- Capability-guarded residual AST emitted across the membrane:
    `.present`, `.emptyGap`, and `.recProj` constructs are eliminated at the membrane;
    only blinded stub reads remain, explicitly pinned to `(stubDigest, stubLo, stubHi)`. -/
inductive ResExpr where
  | lit             (n : Nat)
  | guardedStubRead (stubDigest : Digest256) (stubLo stubHi key : Key256) (fieldId : Nat)
  | scale           (coeff : Nat) (body : ResExpr)
  | add             (lhs rhs : ResExpr)
  | sub             (lhs rhs : ResExpr)
  | ifLe            (lhs rhs thenBr elseBr : ResExpr)
deriving DecidableEq, Repr

/-- Visible Split-Stream `λ•` shallow-projection event resolved at the membrane. -/
inductive VisStreamEvent where
  | visPresent (key : Key256) (fieldId val : Nat) (bodyDigest : Digest256)
  | visAbsent  (key boundLo boundHi : Key256)
deriving DecidableEq, Repr

/-- Hidden Split-Stream stub event deferred across the membrane. -/
inductive HidStubEvent where
  | hidBlindedStub (key : Key256) (fieldId : Nat) (stubLo stubHi : Key256) (stubDigest : Digest256)
deriving DecidableEq, Repr

/-- Length-framed byte encoding of every `PExpr` AST node. -/
def encodePExpr : PExpr → List UInt8
  | .lit n => frameFields [[0x10], leb128 n]
  | .proj k f => frameFields [[0x11], bytes32OfDigest256 k, leb128 f]
  | .scale c b => frameFields [[0x12], leb128 c, encodePExpr b]
  | .add l r => frameFields [[0x13], encodePExpr l, encodePExpr r]
  | .sub l r => frameFields [[0x14], encodePExpr l, encodePExpr r]
  | .ifLe a b t f => frameFields [[0x15], encodePExpr a, encodePExpr b, encodePExpr t, encodePExpr f]
  | .recProj sel s0 s1 => frameFields [[0x16], [if sel then 1 else 0], encodePExpr s0, encodePExpr s1]

/-- Length-framed byte encoding of every `ResExpr` AST node. -/
def encodeResExpr : ResExpr → List UInt8
  | .lit n => frameFields [[0x20], leb128 n]
  | .guardedStubRead d lo hi k f =>
    frameFields [[0x21], bytes32OfDigest256 d, bytes32OfDigest256 lo,
                 bytes32OfDigest256 hi, bytes32OfDigest256 k, leb128 f]
  | .scale c b => frameFields [[0x22], leb128 c, encodeResExpr b]
  | .add l r => frameFields [[0x23], encodeResExpr l, encodeResExpr r]
  | .sub l r => frameFields [[0x24], encodeResExpr l, encodeResExpr r]
  | .ifLe a b t f => frameFields [[0x25], encodeResExpr a, encodeResExpr b, encodeResExpr t, encodeResExpr f]

def encodeVisEvent : VisStreamEvent → List UInt8
  | .visPresent k f v d => frameFields [[0x30], bytes32OfDigest256 k, leb128 f, leb128 v, bytes32OfDigest256 d]
  | .visAbsent k lo hi => frameFields [[0x31], bytes32OfDigest256 k, bytes32OfDigest256 lo, bytes32OfDigest256 hi]

def encodeHidEvent : HidStubEvent → List UInt8
  | .hidBlindedStub k f lo hi d =>
    frameFields [blindedStubTag, bytes32OfDigest256 k, leb128 f,
                 bytes32OfDigest256 lo, bytes32OfDigest256 hi, bytes32OfDigest256 d]

/-- 256-bit Split-Stream transcript digest binding `(worldRoot, partialViewRoot, e, π_vis, π_hid, e_res)`. -/
def computeSplitStreamCid (pv : PartialView) (e : PExpr)
    (vis : List VisStreamEvent) (hid : List HidStubEvent) (res : ResExpr) : Digest256 :=
  cpvHash256 (frameFields [
    transcriptTag,
    bytes32OfDigest256 pv.worldRoot,
    bytes32OfDigest256 (partialViewRoot pv),
    encodePExpr e,
    frameFields (vis.map encodeVisEvent),
    frameFields (hid.map encodeHidEvent),
    encodeResExpr res
  ])

/-- Point lookup outcome on a `PartialViewTree`. -/
inductive PartialLookup where
  | knownPresent (rec : ObjRecord)
  | knownAbsent  (gapLo gapHi : Key256)
  | outsideSpan  (rootLo rootHi : Key256)
  | blinded      (stubDigest : Digest256) (stubLo stubHi : Key256)
deriving DecidableEq, Repr

def lookupSubtree : PartialViewTree → Key256 → PartialLookup
  | .present key rec, k =>
    if k == key then .knownPresent rec else .outsideSpan key key
  | .emptyGap lo hi, _ =>
    .knownAbsent lo hi
  | .blindedStub d sLo sHi, _ =>
    .blinded d sLo sHi
  | .branch l r, k =>
    if k.toNat ≤ l.hi.toNat then lookupSubtree l k else lookupSubtree r k

def lookupPartial (pv : PartialView) (k : Key256) : PartialLookup :=
  if !inKeyRange pv.tree.lo pv.tree.hi k then
    .outsideSpan pv.tree.lo pv.tree.hi
  else
    lookupSubtree pv.tree k

/-- Full unredacted evaluation of `PExpr` against `FullStore`. -/
def evalFull (fs : FullStore) : PExpr → Nat
  | .lit n => n
  | .proj k f =>
    match fs.tree.lookup k with
    | some rec => rec.getField f
    | none => 0
  | .scale c b => c * evalFull fs b
  | .add l r => evalFull fs l + evalFull fs r
  | .sub l r => evalFull fs l - evalFull fs r
  | .ifLe a b t f =>
    if evalFull fs a ≤ evalFull fs b then evalFull fs t else evalFull fs f
  | .recProj sel s0 s1 =>
    if sel then evalFull fs s1 else evalFull fs s0

/-- Secret-only store environment (`S \ V`) used to evaluate residual `.guardedStubRead` terms. -/
abbrev SecretEnv := Key256 → Option ObjRecord

/-- Residual evaluation against `env_sec : SecretEnv` (holds zero public `.present` entries when constructed via `secretOnlyEnv`). -/
def evalResidual (env_sec : SecretEnv) : ResExpr → Nat
  | .lit n => n
  | .guardedStubRead _ _ _ k f =>
    match env_sec k with
    | some rec => rec.getField f
    | none => 0
  | .scale c b => c * evalResidual env_sec b
  | .add l r => evalResidual env_sec l + evalResidual env_sec r
  | .sub l r => evalResidual env_sec l - evalResidual env_sec r
  | .ifLe a b t f =>
    if evalResidual env_sec a ≤ evalResidual env_sec b then
      evalResidual env_sec t
    else
      evalResidual env_sec f

/-- Canonical secret-only slice `S \ V`: maps blinded keys to `fs.tree.lookup k` and maps every
    revealed `.present` or `.emptyGap` key to `none`! -/
def secretOnlyEnv (fs : FullStore) (pv : PartialView) : SecretEnv := fun k =>
  match lookupPartial pv k with
  | .blinded _ _ _ => fs.tree.lookup k
  | _ => none

/-- `env_sec` agrees with `fs` on keys that remain `.blinded` in `pv` (public keys need NOT be present in `env_sec`). -/
def SecretEnvCoversBlinded (fs : FullStore) (pv : PartialView) (env_sec : SecretEnv) : Prop :=
  ∀ k d sLo sHi, lookupPartial pv k = .blinded d sLo sHi → env_sec k = fs.tree.lookup k

theorem secretOnlyEnv_coversBlinded (fs : FullStore) (pv : PartialView) :
    SecretEnvCoversBlinded fs pv (secretOnlyEnv fs pv) := by
  intro k d sLo sHi hlk
  simp [secretOnlyEnv, hlk]

/-- Static branch condition comparator for `.ifLe` partial evaluation (`#tooth` polarity target). -/
@[expose] def branchCondLe (u v : Nat) : Bool :=
  decide (u ≤ v)

def pevalScale (c : Nat) (r : ResExpr) : ResExpr :=
  if c == 0 then .lit 0
  else if c == 1 then r
  else match r with
    | .lit v => .lit (c * v)
    | .scale d inner => .scale (c * d) inner
    | _ => .scale c r

def pevalAdd : ResExpr → ResExpr → ResExpr
  | .lit 0, y => y
  | x, .lit 0 => x
  | .lit u, .lit v => .lit (u + v)
  | x, y => .add x y

def pevalSub : ResExpr → ResExpr → ResExpr
  | x, .lit 0 => x
  | .lit 0, _ => .lit 0
  | .lit u, .lit v => .lit (u - v)
  | x, y => .sub x y

structure PevalAcc where
  residual      : ResExpr
  visStream     : List VisStreamEvent
  hidStubStream : List HidStubEvent
deriving DecidableEq, Repr

/-- Output of `peval (knownEnv : PartialView) (e : PExpr)`. -/
structure PevalOut where
  residual           : ResExpr
  visStream          : List VisStreamEvent
  hidStubStream      : List HidStubEvent
  pevalTranscriptCid : Digest256
deriving DecidableEq, Repr

def pevalAux (pv : PartialView) : PExpr → PevalAcc
  | .lit n => ⟨.lit n, [], []⟩
  | .proj k f =>
    match lookupPartial pv k with
    | .knownPresent rec =>
      let v := rec.getField f
      ⟨.lit v, [.visPresent k f v (presentBodyDigest k rec)], []⟩
    | .knownAbsent gLo gHi =>
      ⟨.lit 0, [.visAbsent k gLo gHi], []⟩
    | .outsideSpan rLo rHi =>
      ⟨.lit 0, [.visAbsent k rLo rHi], []⟩
    | .blinded stubDigest sLo sHi =>
      ⟨.guardedStubRead stubDigest sLo sHi k f, [], [.hidBlindedStub k f sLo sHi stubDigest]⟩
  | .scale c body =>
    if c == 0 then
      ⟨.lit 0, [], []⟩
    else
      let sub := pevalAux pv body
      ⟨pevalScale c sub.residual, sub.visStream, sub.hidStubStream⟩
  | .add l r =>
    let la := pevalAux pv l
    let ra := pevalAux pv r
    ⟨pevalAdd la.residual ra.residual, la.visStream ++ ra.visStream, la.hidStubStream ++ ra.hidStubStream⟩
  | .sub l r =>
    let la := pevalAux pv l
    let ra := pevalAux pv r
    ⟨pevalSub la.residual ra.residual, la.visStream ++ ra.visStream, la.hidStubStream ++ ra.hidStubStream⟩
  | .ifLe a b t f =>
    let aa := pevalAux pv a
    let ba := pevalAux pv b
    match aa.residual, ba.residual with
    | .lit u, .lit v =>
      if branchCondLe u v then
        let ta := pevalAux pv t
        ⟨ta.residual, aa.visStream ++ ba.visStream ++ ta.visStream,
         aa.hidStubStream ++ ba.hidStubStream ++ ta.hidStubStream⟩
      else
        let fa := pevalAux pv f
        ⟨fa.residual, aa.visStream ++ ba.visStream ++ fa.visStream,
         aa.hidStubStream ++ ba.hidStubStream ++ fa.hidStubStream⟩
    | ar, br =>
      let ta := pevalAux pv t
      let fa := pevalAux pv f
      ⟨.ifLe ar br ta.residual fa.residual,
       aa.visStream ++ ba.visStream ++ ta.visStream ++ fa.visStream,
       aa.hidStubStream ++ ba.hidStubStream ++ ta.hidStubStream ++ fa.hidStubStream⟩
  | .recProj sel s0 s1 =>
    if sel then pevalAux pv s1 else pevalAux pv s0

/-- Certified partial evaluation at the capability membrane. -/
def peval (knownEnv : PartialView) (e : PExpr) : PevalOut :=
  let acc := pevalAux knownEnv e
  { residual := acc.residual
    visStream := acc.visStream
    hidStubStream := acc.hidStubStream
    pevalTranscriptCid := computeSplitStreamCid knownEnv e acc.visStream acc.hidStubStream acc.residual }

/-- Keys referenced anywhere in a `ResExpr`. -/
def ResExpr.referencedKeys : ResExpr → List Key256
  | .lit _ => []
  | .guardedStubRead _ _ _ k _ => [k]
  | .scale _ b => b.referencedKeys
  | .add l r | .sub l r => l.referencedKeys ++ r.referencedKeys
  | .ifLe a b t f => a.referencedKeys ++ b.referencedKeys ++ t.referencedKeys ++ f.referencedKeys

/-- Membrane check enforcing that every residualized key read lies inside `residualReadCone` (`#tooth` target). -/
@[expose] def checkResidualReadCone (residualReadCone : CapFrustum) (r : ResExpr) : Bool :=
  r.referencedKeys.all (fun k => frustumCoversKey residualReadCone k)

/-- Full membrane gate checking view root validity, Split-Stream transcript CID integrity, and `residualReadCone` confinement. -/
def verifyPevalMembrane (pv : PartialView) (residualReadCone : CapFrustum)
    (e : PExpr) (out : PevalOut) : Bool :=
  verifyPartialView pv.tree pv.worldRoot &&
  (out.pevalTranscriptCid == computeSplitStreamCid pv e out.visStream out.hidStubStream out.residual) &&
  checkResidualReadCone residualReadCone out.residual

theorem evalResidual_pevalScale (env_sec : SecretEnv) (c : Nat) (r : ResExpr) :
    evalResidual env_sec (pevalScale c r) = c * evalResidual env_sec r := by
  unfold pevalScale
  by_cases hc0 : c == 0
  · have h0 : c = 0 := eq_of_beq hc0
    subst h0; simp [evalResidual]
  · simp only [hc0, Bool.false_eq_true, ↓reduceIte]
    by_cases hc1 : c == 1
    · have h1 : c = 1 := eq_of_beq hc1
      subst h1; simp
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      cases r <;> simp [evalResidual, Nat.mul_assoc]

theorem evalResidual_pevalAdd (env_sec : SecretEnv) (l r : ResExpr) :
    evalResidual env_sec (pevalAdd l r) = evalResidual env_sec l + evalResidual env_sec r := by
  cases l with
  | lit u =>
    cases u with
    | zero => simp [pevalAdd, evalResidual]
    | succ u' =>
      cases r with
      | lit v =>
        cases v <;> simp [pevalAdd, evalResidual]
      | _ => simp [pevalAdd, evalResidual]
  | _ =>
    cases r with
    | lit v =>
      cases v <;> simp [pevalAdd, evalResidual]
    | _ => simp [pevalAdd, evalResidual]

theorem evalResidual_pevalSub (env_sec : SecretEnv) (l r : ResExpr) :
    evalResidual env_sec (pevalSub l r) = evalResidual env_sec l - evalResidual env_sec r := by
  cases l with
  | lit u =>
    cases u with
    | zero =>
      cases r with
      | lit v => cases v <;> simp [pevalSub, evalResidual]
      | _ => simp [pevalSub, evalResidual]
    | succ u' =>
      cases r with
      | lit v => cases v <;> simp [pevalSub, evalResidual]
      | _ => simp [pevalSub, evalResidual]
  | _ =>
    cases r with
    | lit v => cases v <;> simp [pevalSub, evalResidual]
    | _ => simp [pevalSub, evalResidual]

theorem lookupSubtree_consistent_spec :
    ∀ {ft : FullTree} {pt : PartialViewTree} (k : Key256),
      ft.wf = true →
      PartialViewSubtreeConsistent ft pt →
      inKeyRange pt.lo pt.hi k = true →
      match lookupSubtree pt k with
      | .knownPresent rec => ft.lookup k = some rec
      | .knownAbsent _ _ => ft.lookup k = none
      | .outsideSpan _ _ => ft.lookup k = none
      | .blinded _ _ _ => True
  | _, _, k, _, .present key rec, hin => by
    unfold inKeyRange at hin
    simp only [PartialViewTree.lo, PartialViewTree.hi, Bool.and_eq_true] at hin
    have hlo : key.toNat ≤ k.toNat := of_decide_eq_true hin.1
    have hhi : k.toNat ≤ key.toNat := of_decide_eq_true hin.2
    have hkeq : k = key := BitVec.eq_of_toNat_eq (by omega)
    subst hkeq
    simp [lookupSubtree, FullTree.lookup]
  | _, _, k, _, .emptyGap lo hi _, _ => by
    simp [lookupSubtree, FullTree.lookup]
  | _, _, _, _, .blinded _ _, _ => by
    simp [lookupSubtree]
  | .branch fl fr, .branch pl pr, k, hfwf, .branch hadj hcl hcr, hin => by
    simp only [FullTree.wf, Bool.and_eq_true] at hfwf
    have hadjNat : fl.hi.toNat + 1 = fr.lo.toNat := hadj
    have hblHi := (consistent_bounds hcl).2.1
    have hbrLo := (consistent_bounds hcr).1
    unfold inKeyRange at hin
    simp only [PartialViewTree.lo, PartialViewTree.hi, Bool.and_eq_true] at hin
    have hkLo : pl.lo.toNat ≤ k.toNat := of_decide_eq_true hin.1
    have hkHi : k.toNat ≤ pr.hi.toNat := of_decide_eq_true hin.2
    simp only [lookupSubtree, FullTree.lookup, hblHi]
    by_cases hle : k.toNat ≤ fl.hi.toNat
    · simp only [hle, ↓reduceIte]
      have hinL : inKeyRange pl.lo pl.hi k = true := by
        unfold inKeyRange
        rw [hblHi]
        simp [decide_eq_true hkLo, decide_eq_true hle]
      exact lookupSubtree_consistent_spec k hfwf.1.1 hcl hinL
    · simp only [hle, ↓reduceIte]
      have hinR : inKeyRange pr.lo pr.hi k = true := by
        unfold inKeyRange
        rw [hbrLo]
        have hge : fr.lo.toNat ≤ k.toNat := by omega
        simp [decide_eq_true hge, decide_eq_true hkHi]
      exact lookupSubtree_consistent_spec k hfwf.1.2 hcr hinR

theorem FullTree.lookup_none_of_not_inKeyRange
    {ft : FullTree} {k : Key256} (hwf : ft.wf = true)
    (hout : inKeyRange ft.lo ft.hi k = false) :
    ft.lookup k = none := by
  cases hlk : ft.lookup k with
  | none => rfl
  | some rec =>
    have hmem := (ft.lookup_some_iff_mem_entries hwf k rec).mp hlk
    obtain ⟨hkLo, hkHi⟩ := ft.entries_mem_bounds hwf hmem
    simp [inKeyRange, hkLo, hkHi] at hout

/-- Single-expression partial evaluation semantic preservation under secret-only `env_sec`. -/
theorem pevalAux_eval_eq_full
    {fs : FullStore} {pv : PartialView} {env_sec : SecretEnv}
    (hcons : PartialViewConsistent fs pv)
    (hsec : SecretEnvCoversBlinded fs pv env_sec)
    (e : PExpr) :
    evalResidual env_sec (pevalAux pv e).residual = evalFull fs e := by
  induction e with
  | lit n => rfl
  | proj k f =>
    simp only [pevalAux, evalFull]
    cases hlk : lookupPartial pv k with
    | knownPresent rec =>
      unfold lookupPartial at hlk
      by_cases hin : inKeyRange pv.tree.lo pv.tree.hi k = true
      · simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlk
        have hspec := lookupSubtree_consistent_spec k hcons.1 hcons.2.2.2 hin
        rw [hlk] at hspec
        simp [evalResidual, hspec]
      · have hinF := Bool.eq_false_iff.mpr hin
        simp [hinF] at hlk
    | knownAbsent gLo gHi =>
      unfold lookupPartial at hlk
      by_cases hin : inKeyRange pv.tree.lo pv.tree.hi k = true
      · simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlk
        have hspec := lookupSubtree_consistent_spec k hcons.1 hcons.2.2.2 hin
        rw [hlk] at hspec
        simp [evalResidual, hspec]
      · have hinF := Bool.eq_false_iff.mpr hin
        simp [hinF] at hlk
    | outsideSpan rLo rHi =>
      unfold lookupPartial at hlk
      by_cases hin : inKeyRange pv.tree.lo pv.tree.hi k = true
      · simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlk
        have hspec := lookupSubtree_consistent_spec k hcons.1 hcons.2.2.2 hin
        rw [hlk] at hspec
        simp [evalResidual, hspec]
      · have hinF := Bool.eq_false_iff.mpr hin
        have hbl := (consistent_bounds hcons.2.2.2).1
        have hbh := (consistent_bounds hcons.2.2.2).2.1
        rw [hbl, hbh] at hinF
        simp [evalResidual, fs.tree.lookup_none_of_not_inKeyRange hcons.1 hinF]
    | blinded d sLo sHi =>
      simp [evalResidual, hsec k d sLo sHi hlk]
  | scale c body ih =>
    simp only [pevalAux, evalFull]
    by_cases hc0 : c == 0
    · have h0 : c = 0 := eq_of_beq hc0
      subst h0; simp [evalResidual]
    · simp only [hc0, Bool.false_eq_true, ↓reduceIte, evalResidual_pevalScale, ih]
  | add l r ihl ihr =>
    simp only [pevalAux, evalFull, evalResidual_pevalAdd, ihl, ihr]
  | sub l r ihl ihr =>
    simp only [pevalAux, evalFull, evalResidual_pevalSub, ihl, ihr]
  | ifLe a b t f iha ihb iht ihf =>
    simp only [pevalAux, evalFull]
    split
    · rename_i u v ha hb
      rw [ha] at iha; rw [hb] at ihb
      simp only [evalResidual] at iha ihb
      rw [← iha, ← ihb]
      cases hcond : branchCondLe u v
      · have hnotle : ¬ (u ≤ v) := of_decide_eq_false hcond
        simp [hnotle, ihf]
      · have hle : u ≤ v := of_decide_eq_true hcond
        simp [hle, iht]
    · simp only [evalResidual, iha, ihb, iht, ihf]
  | recProj sel s0 s1 ih0 ih1 =>
    cases sel <;> simp [pevalAux, evalFull, ih0, ih1]

/-! ### Multi-Turn Membrane Evolution (`MembraneTurn`, `ValidMembraneTrace`, `peval_sound_and_confidential`) -/

/-- Authorized write target `(wKey, wField, newSalt)` on a visible `.present` cell, or read-only `none`. -/
structure WriteTarget where
  key     : Key256
  fieldId : Nat
  newSalt : Digest256
deriving DecidableEq, Repr

/-- One turn across the partial-evaluation membrane. -/
structure MembraneTurn where
  expr             : PExpr
  residualReadCone : CapFrustum
  writeTarget      : Option WriteTarget := none
deriving DecidableEq, Repr

def updatePresentTreeFull : FullTree → Key256 → Nat → Nat → Digest256 → FullTree
  | .present k rec, wKey, wField, val, newSalt =>
    if wKey == k then .present k (rec.setField wField val newSalt) else .present k rec
  | .emptyGap lo hi, _, _, _, _ => .emptyGap lo hi
  | .branch l r, wKey, wField, val, newSalt =>
    if wKey.toNat ≤ l.hi.toNat then
      .branch (updatePresentTreeFull l wKey wField val newSalt) r
    else
      .branch l (updatePresentTreeFull r wKey wField val newSalt)

def updatePresentTreePartial : PartialViewTree → Key256 → Nat → Nat → Digest256 → PartialViewTree
  | .present k rec, wKey, wField, val, newSalt =>
    if wKey == k then .present k (rec.setField wField val newSalt) else .present k rec
  | .blindedStub d lo hi, _, _, _, _ => .blindedStub d lo hi
  | .emptyGap lo hi, _, _, _, _ => .emptyGap lo hi
  | .branch l r, wKey, wField, val, newSalt =>
    if wKey.toNat ≤ l.hi.toNat then
      .branch (updatePresentTreePartial l wKey wField val newSalt) r
    else
      .branch l (updatePresentTreePartial r wKey wField val newSalt)

theorem updatePresentTreeFull_bounds (wKey : Key256) (wField val : Nat) (newSalt : Digest256) :
    ∀ (ft : FullTree),
      (updatePresentTreeFull ft wKey wField val newSalt).lo = ft.lo ∧
      (updatePresentTreeFull ft wKey wField val newSalt).hi = ft.hi ∧
      (ft.wf = true → (updatePresentTreeFull ft wKey wField val newSalt).wf = true)
  | .present k rec => by
    simp only [updatePresentTreeFull]
    split <;> exact ⟨rfl, rfl, fun _ => rfl⟩
  | .emptyGap lo hi => ⟨rfl, rfl, id⟩
  | .branch l r => by
    have ihl := updatePresentTreeFull_bounds wKey wField val newSalt l
    have ihr := updatePresentTreeFull_bounds wKey wField val newSalt r
    simp only [updatePresentTreeFull]
    split
    · refine ⟨ihl.1, rfl, fun hwf => ?_⟩
      simp only [FullTree.wf, Bool.and_eq_true] at hwf ⊢
      rw [ihl.2.1]
      exact ⟨⟨ihl.2.2 hwf.1.1, hwf.1.2⟩, hwf.2⟩
    · refine ⟨rfl, ihr.2.1, fun hwf => ?_⟩
      simp only [FullTree.wf, Bool.and_eq_true] at hwf ⊢
      rw [ihr.1]
      exact ⟨⟨hwf.1.1, ihr.2.2 hwf.1.2⟩, hwf.2⟩

theorem updatePresentTreePartial_bounds (wKey : Key256) (wField val : Nat) (newSalt : Digest256) :
    ∀ (pt : PartialViewTree),
      (updatePresentTreePartial pt wKey wField val newSalt).lo = pt.lo ∧
      (updatePresentTreePartial pt wKey wField val newSalt).hi = pt.hi ∧
      (pt.wf = true → (updatePresentTreePartial pt wKey wField val newSalt).wf = true)
  | .present k rec => by
    simp only [updatePresentTreePartial]
    split <;> exact ⟨rfl, rfl, fun _ => rfl⟩
  | .blindedStub _ _ _ => ⟨rfl, rfl, id⟩
  | .emptyGap _ _ => ⟨rfl, rfl, id⟩
  | .branch l r => by
    have ihl := updatePresentTreePartial_bounds wKey wField val newSalt l
    have ihr := updatePresentTreePartial_bounds wKey wField val newSalt r
    simp only [updatePresentTreePartial]
    split
    · refine ⟨ihl.1, rfl, fun hwf => ?_⟩
      simp only [PartialViewTree.wf, Bool.and_eq_true] at hwf ⊢
      rw [ihl.2.1]
      exact ⟨⟨ihl.2.2 hwf.1.1, hwf.1.2⟩, hwf.2⟩
    · refine ⟨rfl, ihr.2.1, fun hwf => ?_⟩
      simp only [PartialViewTree.wf, Bool.and_eq_true] at hwf ⊢
      rw [ihr.1]
      exact ⟨⟨hwf.1.1, ihr.2.2 hwf.1.2⟩, hwf.2⟩

theorem updatePresentSubtree_preserves_consistent
    (wKey : Key256) (wField val : Nat) (newSalt : Digest256) :
    ∀ {ft : FullTree} {pt : PartialViewTree} {targetRec : ObjRecord},
      PartialViewSubtreeConsistent ft pt →
      lookupSubtree pt wKey = .knownPresent targetRec →
      PartialViewSubtreeConsistent
        (updatePresentTreeFull ft wKey wField val newSalt)
        (updatePresentTreePartial pt wKey wField val newSalt)
  | _, _, _, .present k rec, _ => by
    simp only [updatePresentTreeFull, updatePresentTreePartial]
    split <;> exact .present _ _
  | _, _, _, .emptyGap _ _ _, hlk => by
    simp [lookupSubtree] at hlk
  | _, _, _, .blinded _ _, hlk => by
    simp [lookupSubtree] at hlk
  | .branch fl fr, .branch pl pr, targetRec, .branch hadj hcl hcr, hlk => by
    have hblHi := (consistent_bounds hcl).2.1
    simp only [lookupSubtree, updatePresentTreeFull, updatePresentTreePartial, hblHi] at hlk ⊢
    by_cases hle : wKey.toNat ≤ fl.hi.toNat
    · simp only [hle, ↓reduceIte] at hlk ⊢
      have hadj' : (updatePresentTreeFull fl wKey wField val newSalt).hi.toNat + 1 = fr.lo.toNat := by
        rw [(updatePresentTreeFull_bounds wKey wField val newSalt fl).2.1]
        exact hadj
      exact .branch hadj' (updatePresentSubtree_preserves_consistent wKey wField val newSalt hcl hlk) hcr
    · simp only [hle, ↓reduceIte] at hlk ⊢
      have hadj' : fl.hi.toNat + 1 = (updatePresentTreeFull fr wKey wField val newSalt).lo.toNat := by
        rw [(updatePresentTreeFull_bounds wKey wField val newSalt fr).1]
        exact hadj
      exact .branch hadj' hcl (updatePresentSubtree_preserves_consistent wKey wField val newSalt hcr hlk)

theorem updatePresentSubtree_preserves_blinded_lookup
    (wKey : Key256) (wField val : Nat) (newSalt : Digest256) :
    ∀ {ft : FullTree} {pt : PartialViewTree} {targetRec : ObjRecord}
      {q : Key256} {d : Digest256} {sLo sHi : Key256},
      PartialViewSubtreeConsistent ft pt →
      lookupSubtree pt wKey = .knownPresent targetRec →
      lookupSubtree (updatePresentTreePartial pt wKey wField val newSalt) q = .blinded d sLo sHi →
      lookupSubtree pt q = .blinded d sLo sHi ∧
      (updatePresentTreeFull ft wKey wField val newSalt).lookup q = ft.lookup q
  | _, _, _, _, _, _, _, .present k rec, _, hq => by
    simp only [updatePresentTreePartial] at hq
    split at hq <;> simp only [lookupSubtree] at hq <;> split at hq <;> cases hq
  | _, _, _, _, _, _, _, .emptyGap _ _ _, hlk, _ => by
    simp [lookupSubtree] at hlk
  | _, _, _, _, _, _, _, .blinded _ _, hlk, _ => by
    simp [lookupSubtree] at hlk
  | .branch fl fr, .branch pl pr, targetRec, q, d, sLo, sHi, .branch hadj hcl hcr, hlk, hq => by
    have hblHi := (consistent_bounds hcl).2.1
    have hupdPlHi := (updatePresentTreePartial_bounds wKey wField val newSalt pl).2.1
    have hupdFlHi := (updatePresentTreeFull_bounds wKey wField val newSalt fl).2.1
    simp only [lookupSubtree, updatePresentTreePartial, hblHi] at hlk hq
    dsimp only [lookupSubtree, FullTree.lookup, updatePresentTreeFull]
    rw [hblHi]
    by_cases hw : wKey.toNat ≤ fl.hi.toNat
    · simp only [hw, ↓reduceIte, lookupSubtree, hupdPlHi, hblHi] at hlk hq
      simp only [hw, ↓reduceIte, FullTree.lookup, hupdFlHi]
      by_cases hqle : q.toNat ≤ fl.hi.toNat
      · simp only [hqle, ↓reduceIte] at hq
        refine ⟨by simp only [hqle, ↓reduceIte]; exact (updatePresentSubtree_preserves_blinded_lookup wKey wField val newSalt hcl hlk hq).1,
                by simp only [hqle, ↓reduceIte]; exact (updatePresentSubtree_preserves_blinded_lookup wKey wField val newSalt hcl hlk hq).2⟩
      · simp only [hqle, ↓reduceIte] at hq
        exact ⟨by simp only [hqle, ↓reduceIte]; exact hq, by simp only [hqle, ↓reduceIte]⟩
    · simp only [hw, ↓reduceIte, lookupSubtree, hblHi] at hlk hq
      simp only [hw, ↓reduceIte, FullTree.lookup]
      by_cases hqle : q.toNat ≤ fl.hi.toNat
      · simp only [hqle, ↓reduceIte] at hq
        exact ⟨by simp only [hqle, ↓reduceIte]; exact hq, by simp only [hqle, ↓reduceIte]⟩
      · simp only [hqle, ↓reduceIte] at hq
        refine ⟨by simp only [hqle, ↓reduceIte]; exact (updatePresentSubtree_preserves_blinded_lookup wKey wField val newSalt hcr hlk hq).1,
                by simp only [hqle, ↓reduceIte]; exact (updatePresentSubtree_preserves_blinded_lookup wKey wField val newSalt hcr hlk hq).2⟩

/-- Reference full-store single-turn step (evaluates `turn.expr` directly on `fs` without any membrane). -/
def stepFullTurn (fs : FullStore) (turn : MembraneTurn) : Option (Nat × FullStore) :=
  let v := evalFull fs turn.expr
  match turn.writeTarget with
  | none => some (v, fs)
  | some wt =>
    match fs.tree.lookup wt.key with
    | none => none
    | some _ =>
      some (v, ⟨updatePresentTreeFull fs.tree wt.key wt.fieldId v wt.newSalt⟩)

/-- Reference multi-turn full-store execution returning the list of per-turn values and final `FullStore`. -/
def execFullTurns : FullStore → List MembraneTurn → Option (List Nat × FullStore)
  | fs, [] => some ([], fs)
  | fs, t :: ts => do
    let (v, fs') ← stepFullTurn fs t
    let (vs, fsFinal) ← execFullTurns fs' ts
    pure (v :: vs, fsFinal)

/-- Membrane turn transition: evaluates `out.residual` under `env_sec`, checks that any `writeTarget`
    hits an authorized `.knownPresent` cell in `pv`, and updates `(fs, pv)` + `pv.worldRoot`. -/
def applyMembraneTurn (env_sec : SecretEnv) (fs : FullStore) (pv : PartialView)
    (turn : MembraneTurn) (out : PevalOut) : Option (FullStore × PartialView) :=
  let v := evalResidual env_sec out.residual
  match turn.writeTarget with
  | none => some (fs, pv)
  | some wt =>
    match lookupPartial pv wt.key with
    | .knownPresent _ =>
      let ft' := updatePresentTreeFull fs.tree wt.key wt.fieldId v wt.newSalt
      let pt' := updatePresentTreePartial pv.tree wt.key wt.fieldId v wt.newSalt
      some (⟨ft'⟩, { pv with tree := pt', worldRoot := partialNodeRoot pt' })
    | _ => none

/-- Multi-turn membrane trace predicate (recursive `def` over `List MembraneTurn`:
    initial `PartialViewConsistent` invariant is an external hypothesis, NOT baked into `[]`). -/
def ValidMembraneTrace (env_sec : SecretEnv) :
    FullStore → PartialView → List MembraneTurn → FullStore → PartialView → List PevalOut → Prop
  | fs, pv, [], fsFinal, pvFinal, outs =>
    fsFinal = fs ∧ pvFinal = pv ∧ outs = []
  | fs, pv, turn :: rest, fsFinal, pvFinal, out :: outsRest =>
    out = peval pv turn.expr ∧
    verifyPevalMembrane pv turn.residualReadCone turn.expr out = true ∧
    ∃ fsNext pvNext,
      applyMembraneTurn env_sec fs pv turn out = some (fsNext, pvNext) ∧
      ValidMembraneTrace env_sec fsNext pvNext rest fsFinal pvFinal outsRest
  | _, _, _ :: _, _, _, [] => False

/-- Single-turn completeness witness for `ValidMembraneTrace` on a literal query. -/
theorem validMembraneTrace_lit_complete (env_sec : SecretEnv) (fs : FullStore) (pv : PartialView)
    (cone : CapFrustum) (n : Nat)
    (hver : verifyPartialView pv.tree pv.worldRoot = true) :
    let t : MembraneTurn := { expr := .lit n, residualReadCone := cone, writeTarget := none }
    ValidMembraneTrace env_sec fs pv [t] fs pv [peval pv t.expr] := by
  refine ⟨rfl, ?_, fs, pv, rfl, rfl, rfl, rfl⟩
  simp [verifyPevalMembrane, hver, peval, pevalAux, checkResidualReadCone, ResExpr.referencedKeys]

theorem applyMembraneTurn_preserves_invariants
    {env_sec : SecretEnv} {fs fsNext : FullStore} {pv pvNext : PartialView}
    {turn : MembraneTurn} {out : PevalOut}
    (hcons : PartialViewConsistent fs pv)
    (hsec : SecretEnvCoversBlinded fs pv env_sec)
    (hout : out = peval pv turn.expr)
    (happ : applyMembraneTurn env_sec fs pv turn out = some (fsNext, pvNext)) :
    PartialViewConsistent fsNext pvNext ∧
    SecretEnvCoversBlinded fsNext pvNext env_sec ∧
    stepFullTurn fs turn = some (evalResidual env_sec out.residual, fsNext) := by
  have heval : evalResidual env_sec out.residual = evalFull fs turn.expr := by
    rw [hout]
    exact pevalAux_eval_eq_full hcons hsec turn.expr
  unfold applyMembraneTurn at happ
  unfold stepFullTurn
  cases hwt : turn.writeTarget with
  | none =>
    rw [hwt] at happ
    simp only [Option.some.injEq, Prod.mk.injEq] at happ
    rcases happ with ⟨rfl, rfl⟩
    exact ⟨hcons, hsec, by simp [heval]⟩
  | some wt =>
    rw [hwt] at happ
    dsimp only at happ
    cases hlk : lookupPartial pv wt.key with
    | knownAbsent _ _ => rw [hlk] at happ; cases happ
    | outsideSpan _ _ => rw [hlk] at happ; cases happ
    | blinded _ _ _ => rw [hlk] at happ; cases happ
    | knownPresent targetRec =>
      rw [hlk] at happ
      simp only [Option.some.injEq, Prod.mk.injEq] at happ
      rcases happ with ⟨hfsNext, hpvNext⟩
      subst hfsNext; subst hpvNext
      unfold lookupPartial at hlk
      by_cases hin : inKeyRange pv.tree.lo pv.tree.hi wt.key = true
      · simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlk
        have hfullLk := lookupSubtree_consistent_spec wt.key hcons.1 hcons.2.2.2 hin
        rw [hlk] at hfullLk
        let v := evalResidual env_sec out.residual
        have hsubCons := updatePresentSubtree_preserves_consistent wt.key wt.fieldId v wt.newSalt hcons.2.2.2 hlk
        have hftWf := (updatePresentTreeFull_bounds wt.key wt.fieldId v wt.newSalt fs.tree).2.2 hcons.1
        have hptWf := (updatePresentTreePartial_bounds wt.key wt.fieldId v wt.newSalt pv.tree).2.2 hcons.2.1
        have hrootEq := (consistent_bounds hsubCons).2.2
        have hNextCons : PartialViewConsistent
            ⟨updatePresentTreeFull fs.tree wt.key wt.fieldId v wt.newSalt⟩
            { pv with
              tree := updatePresentTreePartial pv.tree wt.key wt.fieldId v wt.newSalt
              worldRoot := partialNodeRoot (updatePresentTreePartial pv.tree wt.key wt.fieldId v wt.newSalt) } :=
          ⟨hftWf, hptWf, hrootEq, hsubCons⟩
        have hNextSec : SecretEnvCoversBlinded
            ⟨updatePresentTreeFull fs.tree wt.key wt.fieldId v wt.newSalt⟩
            { pv with
              tree := updatePresentTreePartial pv.tree wt.key wt.fieldId v wt.newSalt
              worldRoot := partialNodeRoot (updatePresentTreePartial pv.tree wt.key wt.fieldId v wt.newSalt) }
            env_sec := by
          intro q d sLo sHi hqlk
          unfold lookupPartial at hqlk
          have hloEq := (updatePresentTreePartial_bounds wt.key wt.fieldId v wt.newSalt pv.tree).1
          have hhiEq := (updatePresentTreePartial_bounds wt.key wt.fieldId v wt.newSalt pv.tree).2.1
          rw [hloEq, hhiEq] at hqlk
          by_cases hqin : inKeyRange pv.tree.lo pv.tree.hi q = true
          · simp only [hqin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hqlk
            obtain ⟨horigPt, horigFt⟩ :=
              updatePresentSubtree_preserves_blinded_lookup wt.key wt.fieldId v wt.newSalt hcons.2.2.2 hlk hqlk
            have horigPartial : lookupPartial pv q = .blinded d sLo sHi := by
              simp [lookupPartial, hqin, horigPt]
            rw [hsec q d sLo sHi horigPartial, horigFt]
          · have hqinF := Bool.eq_false_iff.mpr hqin
            simp [hqinF] at hqlk
        refine ⟨hNextCons, hNextSec, ?_⟩
        simp [hfullLk, ← heval]
      · have hinF := Bool.eq_false_iff.mpr hin
        simp [hinF] at hlk

/-- **Non-Cosplay Multi-Turn Soundness & Confidentiality (`peval_sound_and_confidential`)**:
    Given initial consistency `PartialViewConsistent fs₀ pv₀` and secret-only store coverage
    `SecretEnvCoversBlinded fs₀ pv₀ env_sec`, across ANY multi-turn membrane trace
    `ValidMembraneTrace env_sec fs₀ pv₀ turns fsFinal pvFinal outs`:
    1. `PartialViewConsistent fsFinal pvFinal` and `partialViewRoot pvFinal = fullStoreRoot fsFinal`
       hold at the end of the trace;
    2. Evaluating every emitted residual expression under `env_sec` matches full unredacted
       store execution `execFullTurns fs₀ turns` step-for-step; and
    3. Every verified residual expression across the trace contains ZERO references to redacted
       keys outside its turn's `residualReadCone`. -/
theorem peval_sound_and_confidential
    {env_sec : SecretEnv} {fs₀ fsFinal : FullStore} {pv₀ pvFinal : PartialView}
    {turns : List MembraneTurn} {outs : List PevalOut}
    (hInitCons : PartialViewConsistent fs₀ pv₀)
    (hInitSec : SecretEnvCoversBlinded fs₀ pv₀ env_sec)
    (hTrace : ValidMembraneTrace env_sec fs₀ pv₀ turns fsFinal pvFinal outs) :
    PartialViewConsistent fsFinal pvFinal ∧
    partialViewRoot pvFinal = fullStoreRoot fsFinal ∧
    execFullTurns fs₀ turns = some (outs.map (fun o => evalResidual env_sec o.residual), fsFinal) ∧
    ListForall2
      (fun turn out =>
        ∀ k, frustumCoversKey turn.residualReadCone k = false →
          k ∉ out.residual.referencedKeys)
      turns outs := by
  induction turns generalizing fs₀ pv₀ outs with
  | nil =>
    cases outs with
    | nil =>
      simp only [ValidMembraneTrace] at hTrace
      rcases hTrace with ⟨rfl, rfl, _⟩
      exact ⟨hInitCons, hInitCons.root_eq, rfl, .nil⟩
    | cons _ _ =>
      simp [ValidMembraneTrace] at hTrace
  | cons turn rest ih =>
    cases outs with
    | nil =>
      simp [ValidMembraneTrace] at hTrace
    | cons out outsRest =>
      simp only [ValidMembraneTrace] at hTrace
      rcases hTrace with ⟨hout, hver, fsNext, pvNext, happ, hrest⟩
      obtain ⟨hNextCons, hNextSec, hstepFull⟩ :=
        applyMembraneTurn_preserves_invariants hInitCons hInitSec hout happ
      obtain ⟨hFinCons, hFinRoot, hexecRest, hconeRest⟩ := ih hNextCons hNextSec hrest
      have hconeHead : ∀ k, frustumCoversKey turn.residualReadCone k = false →
          k ∉ out.residual.referencedKeys := by
        unfold verifyPevalMembrane checkResidualReadCone at hver
        simp only [Bool.and_eq_true, List.all_eq_true] at hver
        intro k hforb hmem
        have hcov := hver.2 k hmem
        rw [hforb] at hcov
        cases hcov
      refine ⟨hFinCons, hFinRoot, ?_, .cons hconeHead hconeRest⟩
      simp [execFullTurns, hstepFull, hexecRest]

/-! ## 5. Goldilocks Module-SIS Ajtai Homomorphic Linear Opening for `Form.NExpr.peval` -/

/-- Positive integer scalar multiple `(k + 1) • w` via iterated `vecAdd` (uses pure `ajtaiCommit_add`). -/
def natScaleVecPos : Nat → List Int → List Int
  | 0, w => w
  | k + 1, w => vecAdd w (natScaleVecPos k w)

/-- Modular scalar multiple `((k + 1) • syn) mod q` matching `natScaleVecPos`. -/
def natScaleModPos (q : Int) : Nat → List Int → List Int
  | 0, comm => comm
  | k + 1, comm => vecAddMod q comm (natScaleModPos q k comm)

/-- Combined masked short witness `s_comb = (∑_i (k_i + 1) • s_i) + s_mask`. -/
def combineLinearWitnesses : List (Nat × List Int) → List Int → List Int
  | [], sMask => sMask
  | (k, s) :: rest, sMask => vecAdd (natScaleVecPos k s) (combineLinearWitnesses rest sMask)

/-- Public homomorphic target commitment `(∑_i (k_i + 1) • C_i + C_mask) mod q`. -/
def combineLinearCommitments (q : Int) : List (Nat × List Int) → List Int → List Int
  | [], cMask => cMask
  | (k, comm) :: rest, cMask =>
    vecAddMod q (natScaleModPos q k comm) (combineLinearCommitments q rest cMask)

/-- Goldilocks 4-limb ($2^{16}$-radix) scalar functional $\langle [1, 2^{16}, 2^{32}, 2^{48}, 0, \dots], \mathbf{s} \rangle$:
    coordinates $0..3$ encode the 64-bit scalar; coordinates $4..\text{cols}-1$ carry pure blinding masks
    (`readGadgetScalar s_mask = 0`) so `s_comb` leaks ZERO individual hidden cell values (`#tooth` target). -/
@[expose] def readGadgetScalar : List Int → Int
  | l₀ :: l₁ :: l₂ :: l₃ :: _ =>
    l₀ + 65536 * l₁ + 4294967296 * l₂ + 281474976710656 * l₃
  | _ => 0

theorem natScaleVecPos_length (k : Nat) {w : List Int} {cols : Nat} (hw : w.length = cols) :
    (natScaleVecPos k w).length = cols := by
  induction k with
  | zero => exact hw
  | succ k ih => exact (vecAdd_length w _ (hw.trans ih.symm)).trans hw

theorem ajtaiCommit_natScaleVecPos (pp : AjtaiParams) (k : Nat) {w : List Int} (hw : w.length = pp.cols) :
    ajtaiCommit pp (natScaleVecPos k w) (natScaleVecPos_length k hw) =
      natScaleModPos (pp.modulus : Int) k (ajtaiCommit pp w hw) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [natScaleVecPos, natScaleModPos]
    rw [ajtaiCommit_add pp hw (natScaleVecPos_length k hw), ih]

theorem combineLinearWitnesses_length {cols : Nat} :
    ∀ {terms : List (Nat × List Int)} {sMask : List Int},
      (∀ cs ∈ terms, cs.2.length = cols) →
      sMask.length = cols →
      (combineLinearWitnesses terms sMask).length = cols
  | [], _, _, hMask => hMask
  | (k, s) :: rest, sMask, hTerms, hMask => by
    have hs : (natScaleVecPos k s).length = cols := natScaleVecPos_length k (hTerms (k, s) (.head _))
    have hrest := combineLinearWitnesses_length (fun cs hcs => hTerms cs (.tail _ hcs)) hMask
    exact (vecAdd_length _ _ (hs.trans hrest.symm)).trans hs

/-- **Ajtai Additive Homomorphism on `s_comb = ∑ (k_i + 1) • s_i + s_mask` (`ajtaiCommit_combineLinearWitnesses`)**:
    Committing the combined masked vector equals the modular linear combination of individual commitments! -/
theorem ajtaiCommit_combineLinearWitnesses (pp : AjtaiParams) :
    ∀ (terms : List (Nat × List Int)) (sMask : List Int)
      (hTerms : ∀ cs ∈ terms, cs.2.length = pp.cols)
      (hMask : sMask.length = pp.cols),
      ajtaiCommit pp (combineLinearWitnesses terms sMask)
        (combineLinearWitnesses_length hTerms hMask) =
      combineLinearCommitments (pp.modulus : Int)
        (terms.map fun cs => (cs.1, if h : cs.2.length = pp.cols then ajtaiCommit pp cs.2 h else []))
        (ajtaiCommit pp sMask hMask)
  | [], _, _, _ => rfl
  | (k, s) :: rest, sMask, hTerms, hMask => by
    have hs : s.length = pp.cols := hTerms (k, s) (.head _)
    have hsScale : (natScaleVecPos k s).length = pp.cols := natScaleVecPos_length k hs
    have hRestTerms : ∀ cs ∈ rest, cs.2.length = pp.cols := fun cs hcs => hTerms cs (.tail _ hcs)
    have hRestLen := combineLinearWitnesses_length hRestTerms hMask
    simp only [combineLinearWitnesses, List.map_cons, hs, ↓reduceDIte, combineLinearCommitments]
    rw [ajtaiCommit_add pp hsScale hRestLen, ajtaiCommit_natScaleVecPos pp k hs,
        ajtaiCommit_combineLinearWitnesses pp rest sMask hRestTerms hMask]

theorem readGadgetScalar_vecAdd {u v : List Int} (hu4 : 4 ≤ u.length) (hv4 : 4 ≤ v.length) :
    readGadgetScalar (vecAdd u v) = readGadgetScalar u + readGadgetScalar v := by
  rcases u with _ | ⟨u₀, _ | ⟨u₁, _ | ⟨u₂, _ | ⟨u₃, us⟩⟩⟩⟩ <;> try (simp at hu4; done)
  rcases v with _ | ⟨v₀, _ | ⟨v₁, _ | ⟨v₂, _ | ⟨v₃, vs⟩⟩⟩⟩ <;> try (simp at hv4; done)
  simp only [vecAdd, readGadgetScalar]
  omega

theorem readGadgetScalar_natScaleVecPos (k : Nat) {w : List Int} (h4 : 4 ≤ w.length) :
    readGadgetScalar (natScaleVecPos k w) = ((k + 1 : Nat) : Int) * readGadgetScalar w := by
  induction k with
  | zero => simp [natScaleVecPos]
  | succ k ih =>
    have hLenEq : (natScaleVecPos k w).length = w.length := natScaleVecPos_length k rfl
    simp only [natScaleVecPos]
    rw [readGadgetScalar_vecAdd h4 (hLenEq ▸ h4), ih]
    have hcoeff : ((k + 1 + 1 : Nat) : Int) = 1 + ((k + 1 : Nat) : Int) := by omega
    rw [hcoeff, Int.add_mul, Int.one_mul]

theorem readGadgetScalar_combineLinearWitnesses {cols : Nat} (h4 : 4 ≤ cols) :
    ∀ (terms : List (Nat × List Int)) (sMask : List Int),
      (∀ cs ∈ terms, cs.2.length = cols) →
      sMask.length = cols →
      readGadgetScalar sMask = 0 →
      readGadgetScalar (combineLinearWitnesses terms sMask) =
        (terms.map fun cs => ((cs.1 + 1 : Nat) : Int) * readGadgetScalar cs.2).sum
  | [], sMask, _, _, hMaskZero => by
    simp [combineLinearWitnesses, hMaskZero]
  | (k, s) :: rest, sMask, hTerms, hMask, hMaskZero => by
    have hs : s.length = cols := hTerms (k, s) (.head _)
    have hRestTerms : ∀ cs ∈ rest, cs.2.length = cols := fun cs hcs => hTerms cs (.tail _ hcs)
    have hScaleLen : (natScaleVecPos k s).length = cols := natScaleVecPos_length k hs
    have hRestLen := combineLinearWitnesses_length hRestTerms hMask
    simp only [combineLinearWitnesses, List.map_cons, List.sum_cons]
    rw [readGadgetScalar_vecAdd (hScaleLen ▸ h4) (hRestLen ▸ h4),
        readGadgetScalar_natScaleVecPos k (hs ▸ h4),
        readGadgetScalar_combineLinearWitnesses h4 rest sMask hRestTerms hMask hMaskZero]

/-- Verifier check for a single combined masked Ajtai opening `s_comb = ∑ (k_i + 1) • s_i + s_mask`
    certifying an affine folded scalar `claimedScalar` (`‖s_comb‖_∞ ≤ 65535`). -/
def verifyHomomorphicLinearOpening (pp : AjtaiParams)
    (publicComms : List (Nat × List Int)) (cMask : List Int)
    (claimedScalar : Int) (sComb : List Int) : Bool :=
  if hLen : sComb.length = pp.cols then
    checkShortNorm 65535 sComb &&
    (ajtaiCommit pp sComb hLen == combineLinearCommitments (pp.modulus : Int) publicComms cMask) &&
    (readGadgetScalar sComb == claimedScalar)
  else
    false

/-- **Completeness of Homomorphic Linear Opening (`verifyHomomorphicLinearOpening_complete`)**:
    Every honest combined short witness `s_comb = combineLinearWitnesses honestTerms sMask`
    passes `verifyHomomorphicLinearOpening = true`! -/
theorem verifyHomomorphicLinearOpening_complete
    (pp : AjtaiParams) (h4 : 4 ≤ pp.cols)
    (honestTerms : List (Nat × List Int)) (sMask : List Int)
    (hTerms : ∀ cs ∈ honestTerms, cs.2.length = pp.cols)
    (hMask : sMask.length = pp.cols)
    (hMaskZero : readGadgetScalar sMask = 0)
    (hShort : ShortNormBound 65535 (combineLinearWitnesses honestTerms sMask)) :
    verifyHomomorphicLinearOpening pp
      (honestTerms.map fun cs => (cs.1, if h : cs.2.length = pp.cols then ajtaiCommit pp cs.2 h else []))
      (ajtaiCommit pp sMask hMask)
      ((honestTerms.map fun cs => ((cs.1 + 1 : Nat) : Int) * readGadgetScalar cs.2).sum)
      (combineLinearWitnesses honestTerms sMask) = true := by
  have hLen : (combineLinearWitnesses honestTerms sMask).length = pp.cols :=
    combineLinearWitnesses_length hTerms hMask
  have hRead := readGadgetScalar_combineLinearWitnesses h4 honestTerms sMask hTerms hMask hMaskZero
  have hComm := ajtaiCommit_combineLinearWitnesses pp honestTerms sMask hTerms hMask
  unfold verifyHomomorphicLinearOpening
  simp only [hLen, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff]
  exact ⟨⟨hShort, hComm⟩, hRead⟩

/-- **Constructive `PSum` Knowledge Soundness of Homomorphic Linear Opening (`0 Classical.choice`)**:
    Either `claimedScalar` equals the exact hidden linear combination `∑ (k_i + 1) * readGadgetScalar s_i`,
    or `sComb - sHonest` is extracted via `Obend.Crypto.extractShortDiffSISWitness` as a non-zero
    Module-SIS short kernel vector (`‖Δs‖_∞ ≤ 131070`) in `Type`! -/
def verifyHomomorphicLinearOpening_sound_psum
    (pp : AjtaiParams) (h4 : 4 ≤ pp.cols)
    (honestTerms : List (Nat × List Int)) (sMask : List Int)
    (hTerms : ∀ cs ∈ honestTerms, cs.2.length = pp.cols)
    (hMask : sMask.length = pp.cols)
    (hMaskZero : readGadgetScalar sMask = 0)
    (hHonestShort : ShortNormBound 65535 (combineLinearWitnesses honestTerms sMask))
    (claimedScalar : Int) (sComb : List Int)
    (hVer : verifyHomomorphicLinearOpening pp
      (honestTerms.map fun cs => (cs.1, if h : cs.2.length = pp.cols then ajtaiCommit pp cs.2 h else []))
      (ajtaiCommit pp sMask hMask) claimedScalar sComb = true) :
    PSum
      (claimedScalar = (honestTerms.map fun cs => ((cs.1 + 1 : Nat) : Int) * readGadgetScalar cs.2).sum)
      (SISShortVecWitness pp.modulus 131070 pp.matrix) :=
  let sHonest := combineLinearWitnesses honestTerms sMask
  have hHonestLen : sHonest.length = pp.cols := combineLinearWitnesses_length hTerms hMask
  have hHonestRead : readGadgetScalar sHonest =
      (honestTerms.map fun cs => ((cs.1 + 1 : Nat) : Int) * readGadgetScalar cs.2).sum :=
    readGadgetScalar_combineLinearWitnesses h4 honestTerms sMask hTerms hMask hMaskZero
  if hEqVal : claimedScalar =
      (honestTerms.map fun cs => ((cs.1 + 1 : Nat) : Int) * readGadgetScalar cs.2).sum then
    .inl hEqVal
  else
    have hCombLen : sComb.length = pp.cols := by
      unfold verifyHomomorphicLinearOpening at hVer
      by_cases hL : sComb.length = pp.cols
      · exact hL
      · simp [hL] at hVer
    have hCombFacts : ShortNormBound 65535 sComb ∧
        ajtaiCommit pp sComb hCombLen = ajtaiCommit pp sHonest hHonestLen ∧
        readGadgetScalar sComb = claimedScalar := by
      unfold verifyHomomorphicLinearOpening at hVer
      simp only [hCombLen, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff] at hVer
      refine ⟨hVer.1.1, ?_, hVer.2⟩
      rw [hVer.1.2, ← ajtaiCommit_combineLinearWitnesses pp honestTerms sMask hTerms hMask]
    have hVecNe : sComb ≠ sHonest := by
      intro hSame
      apply hEqVal
      rw [← hCombFacts.2.2, hSame, hHonestRead]
    .inr (extractShortDiffSISWitness pp sComb sHonest hCombLen hHonestLen
      hCombFacts.1 hHonestShort hVecNe hCombFacts.2.1)

/-- **Knowledge Soundness of Homomorphic Linear Opening (`verifyHomomorphicLinearOpening_sound`)**:
    A verified homomorphic linear opening either proves exact equality
    `claimedScalar = ∑ (k_i + 1) * x_i` or yields a non-zero `131070`-short Module-SIS kernel vector! -/
theorem verifyHomomorphicLinearOpening_sound
    (pp : AjtaiParams) (h4 : 4 ≤ pp.cols)
    (honestTerms : List (Nat × List Int)) (sMask : List Int)
    (hTerms : ∀ cs ∈ honestTerms, cs.2.length = pp.cols)
    (hMask : sMask.length = pp.cols)
    (hMaskZero : readGadgetScalar sMask = 0)
    (hHonestShort : ShortNormBound 65535 (combineLinearWitnesses honestTerms sMask))
    (claimedScalar : Int) (sComb : List Int)
    (hVer : verifyHomomorphicLinearOpening pp
      (honestTerms.map fun cs => (cs.1, if h : cs.2.length = pp.cols then ajtaiCommit pp cs.2 h else []))
      (ajtaiCommit pp sMask hMask) claimedScalar sComb = true) :
    claimedScalar = (honestTerms.map fun cs => ((cs.1 + 1 : Nat) : Int) * readGadgetScalar cs.2).sum ∨
      Nonempty (SISShortVecWitness pp.modulus 131070 pp.matrix) := by
  have hHonestLen : (combineLinearWitnesses honestTerms sMask).length = pp.cols :=
    combineLinearWitnesses_length hTerms hMask
  have hHonestRead : readGadgetScalar (combineLinearWitnesses honestTerms sMask) =
      (honestTerms.map fun cs => ((cs.1 + 1 : Nat) : Int) * readGadgetScalar cs.2).sum :=
    readGadgetScalar_combineLinearWitnesses h4 honestTerms sMask hTerms hMask hMaskZero
  unfold verifyHomomorphicLinearOpening at hVer
  by_cases hCombLen : sComb.length = pp.cols
  · simp only [hCombLen, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq, checkShortNorm_iff] at hVer
    by_cases hVecEq : sComb = combineLinearWitnesses honestTerms sMask
    · exact .inl (by rw [← hVer.2, hVecEq, hHonestRead])
    · have hSynEq : ajtaiCommit pp sComb hCombLen =
          ajtaiCommit pp (combineLinearWitnesses honestTerms sMask) hHonestLen := by
        rw [hVer.1.2, ← ajtaiCommit_combineLinearWitnesses pp honestTerms sMask hTerms hMask]
      exact .inr ⟨extractShortDiffSISWitness pp sComb
        (combineLinearWitnesses honestTerms sMask) hCombLen hHonestLen hVer.1.1 hHonestShort hVecEq hSynEq⟩
  · simp [hCombLen] at hVer

/-! ### Direct Transport of Homomorphically Certified `Form.NExpr` into `pairsOf` & `VaultTurn` Conservation -/

/-- Extract `(publicConst, hiddenFieldTerms)` (each with weight index `k = 0`, i.e. coefficient `1`)
    from an affine `Form.NExpr` built over `.lit`, public `pubKnown` pages, hidden `isHiddenPage` pages, and `.add`. -/
def extractHiddenAffineNExpr (pubKnown : Known) (isHiddenPage : String → Bool) :
    NExpr → Option (Nat × List (Nat × String × String))
  | .lit n => some (n, [])
  | .hole _ => none
  | .field (.hole _) _ => none
  | .field (.page p) f =>
    if isHiddenPage p then
      some (0, [(0, p, f)])
    else
      match pubKnown p with
      | some d => some (Obend.Vault.natAt d f, [])
      | none => none
  | .add x y => do
    let (cx, tx) ← extractHiddenAffineNExpr pubKnown isHiddenPage x
    let (cy, ty) ← extractHiddenAffineNExpr pubKnown isHiddenPage y
    pure (cx + cy, tx ++ ty)
  | .sub _ _ => none

/-- Compositional certificate tree specializing a `Form.NExpr` across public `PartialView` cells
    and homomorphically folded hidden-cell linear combinations (`s_comb = ∑ c_i • s_i + s_mask`). -/
inductive HomomorphicNExprCert where
  | lit     (n : Nat)
  | hole    (h : String)
  | holeFld (h f : String)
  | pubFld  (p f : String)
  | keepFld (p f : String)
  | add     (lhs rhs : HomomorphicNExprCert)
  | sub     (lhs rhs : HomomorphicNExprCert)
  | homomorphicFold
      (orig : NExpr)
      (foldedVal : Nat)
      (cMask : List Int)
      (sComb : List Int)
deriving DecidableEq, Repr

/-- Original `Form.NExpr` reconstructed from a `HomomorphicNExprCert`. -/
def HomomorphicNExprCert.source : HomomorphicNExprCert → NExpr
  | .lit n => .lit n
  | .hole h => .hole h
  | .holeFld h f => .field (.hole h) f
  | .pubFld p f => .field (.page p) f
  | .keepFld p f => .field (.page p) f
  | .add l r => .add l.source r.source
  | .sub l r => .sub l.source r.source
  | .homomorphicFold orig _ _ _ => orig

/-- Residual `Form.NExpr` emitted at the membrane (all hidden page references folded into `.lit foldedVal`!). -/
def HomomorphicNExprCert.residual (pubKnown : Known) : HomomorphicNExprCert → NExpr
  | .lit n => .lit n
  | .hole h => .hole h
  | .holeFld h f => .field (.hole h) f
  | .pubFld p f =>
    match pubKnown p with
    | some d => .lit (Obend.Vault.natAt d f)
    | none => .field (.page p) f
  | .keepFld p f => .field (.page p) f
  | .add l r => addN (l.residual pubKnown) (r.residual pubKnown)
  | .sub l r => subN (l.residual pubKnown) (r.residual pubKnown)
  | .homomorphicFold _ foldedVal _ _ => .lit foldedVal

/-- True iff `e : NExpr` references zero hidden pages (`isHiddenPage p = false` on every `.field (.page p) _`). -/
def hiddenPageFree (isHiddenPage : String → Bool) : NExpr → Bool
  | .lit _ | .hole _ | .field (.hole _) _ => true
  | .field (.page p) _ => !isHiddenPage p
  | .add x y | .sub x y => hiddenPageFree isHiddenPage x && hiddenPageFree isHiddenPage y

/-- Verifier for `HomomorphicNExprCert` checking every `.homomorphicFold` via `verifyHomomorphicLinearOpening`. -/
def verifyHomomorphicNExprCert (pp : AjtaiParams)
    (pubKnown : Known) (isHiddenPage : String → Bool)
    (hiddenCommLookup : String → String → Option (List Int)) :
    HomomorphicNExprCert → Bool
  | .lit _ | .hole _ | .holeFld _ _ => true
  | .pubFld p _ => !isHiddenPage p && (pubKnown p).isSome
  | .keepFld p _ => !isHiddenPage p && (pubKnown p).isNone
  | .add l r | .sub l r =>
    verifyHomomorphicNExprCert pp pubKnown isHiddenPage hiddenCommLookup l &&
    verifyHomomorphicNExprCert pp pubKnown isHiddenPage hiddenCommLookup r
  | .homomorphicFold orig foldedVal cMask sComb =>
    match extractHiddenAffineNExpr pubKnown isHiddenPage orig with
    | none => false
    | some (pubConst, hidTerms) =>
      if pubConst ≤ foldedVal then
        match hidTerms.mapM (fun t =>
            (hiddenCommLookup t.2.1 t.2.2).map fun comm => (t.1, comm)) with
        | none => false
        | some publicComms =>
          verifyHomomorphicLinearOpening pp publicComms cMask
            ((foldedVal : Int) - (pubConst : Int)) sComb
      else
        false

theorem hiddenPageFree_addN (isHid : String → Bool) {x y : NExpr}
    (hx : hiddenPageFree isHid x = true) (hy : hiddenPageFree isHid y = true) :
    hiddenPageFree isHid (addN x y) = true := by
  cases x <;> cases y <;> simp_all [addN, hiddenPageFree]

theorem hiddenPageFree_subN (isHid : String → Bool) {x y : NExpr}
    (hx : hiddenPageFree isHid x = true) (hy : hiddenPageFree isHid y = true) :
    hiddenPageFree isHid (subN x y) = true := by
  cases x <;> cases y <;> simp_all [subN, hiddenPageFree] <;> split <;> simp [hiddenPageFree]

/-- Verified homomorphically specialized `NExpr`s expose ZERO hidden page references! -/
theorem verifyHomomorphicNExprCert_hiddenPageFree
    {pp : AjtaiParams} {pubKnown : Known} {isHiddenPage : String → Bool}
    {hiddenCommLookup : String → String → Option (List Int)} :
    ∀ {cert : HomomorphicNExprCert},
      verifyHomomorphicNExprCert pp pubKnown isHiddenPage hiddenCommLookup cert = true →
      hiddenPageFree isHiddenPage (cert.residual pubKnown) = true
  | .lit _, _ | .hole _, _ | .holeFld _ _, _ | .homomorphicFold _ _ _ _, _ => rfl
  | .pubFld p _, h => by
    simp only [verifyHomomorphicNExprCert, Bool.and_eq_true] at h
    simp only [HomomorphicNExprCert.residual]
    cases pubKnown p with
    | none => simpa [hiddenPageFree] using h.1
    | some _ => rfl
  | .keepFld p _, h => by
    simp only [verifyHomomorphicNExprCert, Bool.and_eq_true] at h
    simpa [HomomorphicNExprCert.residual, hiddenPageFree] using h.1
  | .add l r, h => by
    simp only [verifyHomomorphicNExprCert, Bool.and_eq_true] at h
    exact hiddenPageFree_addN isHiddenPage
      (verifyHomomorphicNExprCert_hiddenPageFree h.1)
      (verifyHomomorphicNExprCert_hiddenPageFree h.2)
  | .sub l r, h => by
    simp only [verifyHomomorphicNExprCert, Bool.and_eq_true] at h
    exact hiddenPageFree_subN isHiddenPage
      (verifyHomomorphicNExprCert_hiddenPageFree h.1)
      (verifyHomomorphicNExprCert_hiddenPageFree h.2)

/-- Scalar contribution `(k + 1) * natAt(fullKnown p, f)` of a single hidden affine term. -/
def evalHiddenTerm (fullKnown : Known) (t : Nat × String × String) : Nat :=
  (t.1 + 1) * match fullKnown t.2.1 with | some d => Obend.Vault.natAt d t.2.2 | none => 0

/-- Witness consistency for hidden page Ajtai commitments against `fullKnown : Form.Known`
    (zero hardness premise — dishonest openings constructively extract `SISShortVecWitness`). -/
def HiddenAjtaiConsistent (pp : AjtaiParams)
    (pubKnown fullKnown : Known) (isHiddenPage : String → Bool)
    (hiddenCommLookup : String → String → Option (List Int)) : Prop :=
  4 ≤ pp.cols ∧
  Obend.Vault.Form.Agrees pubKnown fullKnown ∧
  (∀ p, isHiddenPage p = true → (fullKnown p).isSome = true) ∧
  (∀ (hidTerms : List (Nat × String × String)) (publicComms : List (Nat × List Int))
     (cMask : List Int) (claimed : Int) (sComb : List Int),
     hidTerms.mapM (fun t => (hiddenCommLookup t.2.1 t.2.2).map fun comm => (t.1, comm)) =
       some publicComms →
     verifyHomomorphicLinearOpening pp publicComms cMask claimed sComb = true →
     ∃ (honestWit : List (Nat × List Int)) (sMask : List Int) (hMask : sMask.length = pp.cols),
       (∀ cs ∈ honestWit, cs.2.length = pp.cols) ∧
       readGadgetScalar sMask = 0 ∧
       ShortNormBound 65535 (combineLinearWitnesses honestWit sMask) ∧
       publicComms = (honestWit.map fun cs =>
         (cs.1, if h : cs.2.length = pp.cols then ajtaiCommit pp cs.2 h else [])) ∧
       cMask = ajtaiCommit pp sMask hMask ∧
       (honestWit.map fun cs => ((cs.1 + 1 : Nat) : Int) * readGadgetScalar cs.2).sum =
         ((hidTerms.map (evalHiddenTerm fullKnown)).sum : Nat))

theorem extractHiddenAffineNExpr_eval_eq
    {pubKnown fullKnown : Known} {isHiddenPage : String → Bool}
    (hAgree : Obend.Vault.Form.Agrees pubKnown fullKnown)
    (hHidLive : ∀ p, isHiddenPage p = true → (fullKnown p).isSome = true)
    (a : Assignment) :
    ∀ {e : NExpr} {pubConst : Nat} {hidTerms : List (Nat × String × String)},
      extractHiddenAffineNExpr pubKnown isHiddenPage e = some (pubConst, hidTerms) →
      (e.subst a).holes = [] ∧
      (e.subst a).eval fullKnown =
        some (pubConst + (hidTerms.map (evalHiddenTerm fullKnown)).sum)
  | .lit n, pubConst, hidTerms, h => by
    simp only [extractHiddenAffineNExpr, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [NExpr.subst, NExpr.holes, NExpr.eval]
  | .hole _, _, _, h => by cases h
  | .field (.hole _) _, _, _, h => by cases h
  | .field (.page p) f, pubConst, hidTerms, h => by
    simp only [extractHiddenAffineNExpr] at h
    by_cases hHid : isHiddenPage p = true
    · simp only [hHid, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      cases hfk : fullKnown p with
      | none =>
        have hlive := hHidLive p hHid
        rw [hfk] at hlive; cases hlive
      | some d =>
        simp [evalHiddenTerm, NExpr.subst, PRef.subst, NExpr.holes, PRef.holes, NExpr.eval, hfk]
    · have hHidF := Bool.eq_false_iff.mpr hHid
      simp only [hHidF, Bool.false_eq_true, ↓reduceIte] at h
      cases hpk : pubKnown p with
      | none => rw [hpk] at h; cases h
      | some d =>
        rw [hpk] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp [NExpr.subst, PRef.subst, NExpr.holes, PRef.holes, NExpr.eval, hAgree p d hpk]
  | .add x y, pubConst, hidTerms, h => by
    simp only [extractHiddenAffineNExpr, bind, Option.bind] at h
    cases hx : extractHiddenAffineNExpr pubKnown isHiddenPage x with
    | none => rw [hx] at h; cases h
    | some px =>
      rw [hx] at h
      cases hy : extractHiddenAffineNExpr pubKnown isHiddenPage y with
      | none => rw [hy] at h; cases h
      | some py =>
        rw [hy] at h
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨hhx, hex⟩ := extractHiddenAffineNExpr_eval_eq hAgree hHidLive a hx
        obtain ⟨hhy, hey⟩ := extractHiddenAffineNExpr_eval_eq hAgree hHidLive a hy
        refine ⟨by simp [NExpr.subst, NExpr.holes, hhx, hhy], ?_⟩
        simp only [NExpr.subst, NExpr.eval, hex, hey, bind, Option.bind, pure, List.map_append,
          List.sum_append, Option.some.injEq]
        omega
  | .sub _ _, _, _, h => by cases h

theorem verifyHomomorphicNExprCert_eval_eq_or_sis
    {pp : AjtaiParams}
    {pubKnown fullKnown : Known} {isHiddenPage : String → Bool}
    {hiddenCommLookup : String → String → Option (List Int)}
    (hCon : HiddenAjtaiConsistent pp pubKnown fullKnown isHiddenPage hiddenCommLookup)
    (a : Assignment) :
    ∀ {cert : HomomorphicNExprCert},
      verifyHomomorphicNExprCert pp pubKnown isHiddenPage hiddenCommLookup cert = true →
      (((cert.residual pubKnown).subst a).eval fullKnown = (cert.source.subst a).eval fullKnown ∧
       ((cert.residual pubKnown).subst a).holes = (cert.source.subst a).holes) ∨
      Nonempty (SISShortVecWitness pp.modulus 131070 pp.matrix)
  | .lit _, _ => .inl ⟨rfl, rfl⟩
  | .hole _, _ => .inl ⟨rfl, rfl⟩
  | .holeFld _ _, _ => .inl ⟨rfl, rfl⟩
  | .keepFld _ _, _ => .inl ⟨rfl, rfl⟩
  | .pubFld p f, _ => by
    simp only [HomomorphicNExprCert.residual, HomomorphicNExprCert.source]
    cases hpk : pubKnown p with
    | none => exact .inl ⟨rfl, rfl⟩
    | some d =>
      exact .inl (by simp [NExpr.subst, PRef.subst, NExpr.eval, NExpr.holes, PRef.holes, hCon.2.1 p d hpk])
  | .add l r, hver => by
    simp only [verifyHomomorphicNExprCert, Bool.and_eq_true] at hver
    rcases verifyHomomorphicNExprCert_eval_eq_or_sis hCon a hver.1 with ⟨ihlE, ihlH⟩ | hsis
    · rcases verifyHomomorphicNExprCert_eval_eq_or_sis hCon a hver.2 with ⟨ihrE, ihrH⟩ | hsis
      · simp only [HomomorphicNExprCert.residual, HomomorphicNExprCert.source]
        refine .inl ⟨?_, ?_⟩
        · rw [Obend.Vault.Form.eval_subst_addN]
          simp only [NExpr.subst, NExpr.eval, ihlE, ihrE]
        · rw [Obend.Vault.Form.holes_subst_addN]
          simp only [NExpr.subst, NExpr.holes, ihlH, ihrH]
      · exact .inr hsis
    · exact .inr hsis
  | .sub l r, hver => by
    simp only [verifyHomomorphicNExprCert, Bool.and_eq_true] at hver
    rcases verifyHomomorphicNExprCert_eval_eq_or_sis hCon a hver.1 with ⟨ihlE, ihlH⟩ | hsis
    · rcases verifyHomomorphicNExprCert_eval_eq_or_sis hCon a hver.2 with ⟨ihrE, ihrH⟩ | hsis
      · simp only [HomomorphicNExprCert.residual, HomomorphicNExprCert.source]
        refine .inl ⟨?_, ?_⟩
        · rw [Obend.Vault.Form.eval_subst_subN]
          simp only [NExpr.subst, NExpr.eval, ihlE, ihrE]
        · rw [Obend.Vault.Form.holes_subst_subN]
          simp only [NExpr.subst, NExpr.holes, ihlH, ihrH]
      · exact .inr hsis
    · exact .inr hsis
  | .homomorphicFold orig foldedVal cMask sComb, hver => by
    simp only [verifyHomomorphicNExprCert] at hver
    cases hex : extractHiddenAffineNExpr pubKnown isHiddenPage orig with
    | none => rw [hex] at hver; cases hver
    | some pair =>
      rcases pair with ⟨pubConst, hidTerms⟩
      rw [hex] at hver
      by_cases hle : pubConst ≤ foldedVal
      · simp only [hle, ↓reduceIte] at hver
        cases hmap : hidTerms.mapM (fun t =>
            (hiddenCommLookup t.2.1 t.2.2).map fun comm => (t.1, comm)) with
        | none => rw [hmap] at hver; cases hver
        | some publicComms =>
          rw [hmap] at hver
          obtain ⟨honestWit, sMask, hMaskLen, hTermsLen, hMaskZero, hHonestShort, hCommsEq, hMaskEq, hSumEq⟩ :=
            hCon.2.2.2 hidTerms publicComms cMask ((foldedVal : Int) - (pubConst : Int)) sComb hmap hver
          rw [hCommsEq, hMaskEq] at hver
          rcases verifyHomomorphicLinearOpening_sound pp hCon.1
              honestWit sMask hTermsLen hMaskLen hMaskZero hHonestShort
              ((foldedVal : Int) - (pubConst : Int)) sComb hver with hSound | hsis
          · rw [hSumEq] at hSound
            obtain ⟨hHoles, hOrigEval⟩ := extractHiddenAffineNExpr_eval_eq hCon.2.1 hCon.2.2.1 a hex
            have hFoldEq : foldedVal = pubConst + (hidTerms.map (evalHiddenTerm fullKnown)).sum := by
              omega
            dsimp only [HomomorphicNExprCert.residual, HomomorphicNExprCert.source,
              NExpr.subst, NExpr.eval, NExpr.holes]
            exact .inl ⟨by rw [hOrigEval, hFoldEq], hHoles.symm⟩
          · exact .inr hsis
      · simp [hle] at hver

/-- Homomorphically certified `Form.Move` carrying certificates for `amount`, `debit`, and `credit`. -/
structure CertifiedMove where
  move       : Move
  amountCert : HomomorphicNExprCert
  debitCert  : HomomorphicNExprCert
  creditCert : HomomorphicNExprCert
deriving DecidableEq, Repr

def CertifiedMove.toResidualRMove (pubKnown : Known) (cm : CertifiedMove) : RMove :=
  let u := cm.move.unfold
  { u with
    amount := cm.amountCert.residual pubKnown
    debit  := cm.debitCert.residual pubKnown
    credit := cm.creditCert.residual pubKnown }

def verifyCertifiedMove (pp : AjtaiParams)
    (pubKnown : Known) (isHiddenPage : String → Bool)
    (hiddenCommLookup : String → String → Option (List Int))
    (cm : CertifiedMove) : Bool :=
  let u := cm.move.unfold
  (cm.amountCert.source == u.amount) &&
  (cm.debitCert.source == u.debit) &&
  (cm.creditCert.source == u.credit) &&
  verifyHomomorphicNExprCert pp pubKnown isHiddenPage hiddenCommLookup cm.amountCert &&
  verifyHomomorphicNExprCert pp pubKnown isHiddenPage hiddenCommLookup cm.debitCert &&
  verifyHomomorphicNExprCert pp pubKnown isHiddenPage hiddenCommLookup cm.creditCert

/-- Completeness witness for `verifyCertifiedMove`: a literal self-balanced move verifies cleanly. -/
theorem verifyCertifiedMove_lit_complete (pp : AjtaiParams)
    (pubKnown : Known) (isHiddenPage : String → Bool)
    (hiddenCommLookup : String → String → Option (List Int))
    (asset src dst : String) (amt : Nat)
    (hSrcPub : isHiddenPage src = false) (hSrcNone : pubKnown src = none)
    (hDstPub : isHiddenPage dst = false) (hDstNone : pubKnown dst = none) :
    verifyCertifiedMove pp pubKnown isHiddenPage hiddenCommLookup
      { move := { asset := asset, src := .page src, dst := .page dst, amount := .lit amt }
        amountCert := .lit amt
        debitCert := .sub (.keepFld src asset) (.lit amt)
        creditCert := .add (.keepFld dst asset) (.lit amt) } = true := by
  simp [verifyCertifiedMove, HomomorphicNExprCert.source,
    verifyHomomorphicNExprCert, hSrcPub, hSrcNone, hDstPub, hDstNone]

/-- **Homomorphic `Form.Move` Soundness, Confidentiality & VaultTurn Conservation
    (`certifiedMoves_pairsOf_and_balanced`)**:
    When an untrusted host certifies a batch of `Form.Move`s over hidden cells using single
    masked Ajtai openings `s_comb = ∑ (k_i + 1) • s_i + s_mask`:
    1. Every residual `RMove` is `hiddenPageFree` (leaking zero hidden page references or individual hidden cell values);
    2. Either `RMove.EvalEquivOn` transports `pairsOf` directly via `Form.pairsOf_congr_eval`
       and every admitted `LegPair` list satisfies `sumAssetDelta = 0` (`Form.pairs_balanced`),
       OR an explicit `131070`-short Module-SIS kernel vector is extracted! -/
theorem certifiedMoves_pairsOf_and_balanced
    {pp : AjtaiParams}
    {pubKnown fullKnown : Known} {isHiddenPage : String → Bool}
    {hiddenCommLookup : String → String → Option (List Int)}
    (hCon : HiddenAjtaiConsistent pp pubKnown fullKnown isHiddenPage hiddenCommLookup)
    (cms : List CertifiedMove)
    (hVerAll : cms.all (verifyCertifiedMove pp pubKnown isHiddenPage hiddenCommLookup) = true)
    (a : Assignment) (tid : ByteArray) (asset : String) :
    (∀ cm ∈ cms,
      hiddenPageFree isHiddenPage (cm.toResidualRMove pubKnown).amount = true ∧
      hiddenPageFree isHiddenPage (cm.toResidualRMove pubKnown).debit = true ∧
      hiddenPageFree isHiddenPage (cm.toResidualRMove pubKnown).credit = true) ∧
    ((pairsOf fullKnown ((cms.map (CertifiedMove.toResidualRMove pubKnown)).map (·.subst a)) =
        pairsOf fullKnown (cms.map (fun cm => cm.move.unfold.subst a)) ∧
      (∀ ps, pairsOf fullKnown ((cms.map (CertifiedMove.toResidualRMove pubKnown)).map (·.subst a)) = .ok ps →
        sumAssetDelta (pairDeltas tid ps) asset = 0)) ∨
     Nonempty (SISShortVecWitness pp.modulus 131070 pp.matrix)) := by
  have hFree : ∀ cm ∈ cms,
      hiddenPageFree isHiddenPage (cm.toResidualRMove pubKnown).amount = true ∧
      hiddenPageFree isHiddenPage (cm.toResidualRMove pubKnown).debit = true ∧
      hiddenPageFree isHiddenPage (cm.toResidualRMove pubKnown).credit = true := by
    intro cm hmem
    have hv := List.all_eq_true.mp hVerAll cm hmem
    unfold verifyCertifiedMove at hv
    simp only [Bool.and_eq_true] at hv
    exact ⟨verifyHomomorphicNExprCert_hiddenPageFree hv.1.1.2,
           verifyHomomorphicNExprCert_hiddenPageFree hv.1.2,
           verifyHomomorphicNExprCert_hiddenPageFree hv.2⟩
  refine ⟨hFree, ?_⟩
  clear hFree
  have hForall2OrSis :
      ListForall2 (RMove.EvalEquivOn fullKnown a)
        (cms.map (CertifiedMove.toResidualRMove pubKnown))
        (cms.map (fun cm => cm.move.unfold)) ∨
      Nonempty (SISShortVecWitness pp.modulus 131070 pp.matrix) := by
    induction cms with
    | nil => exact .inl .nil
    | cons cm rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hVerAll
      rcases ih hVerAll.2 with hTail | hsis
      · have hv := hVerAll.1
        unfold verifyCertifiedMove at hv
        simp only [Bool.and_eq_true, beq_iff_eq] at hv
        rcases verifyHomomorphicNExprCert_eval_eq_or_sis hCon a hv.1.1.2 with hAmt | hsis
        · rcases verifyHomomorphicNExprCert_eval_eq_or_sis hCon a hv.1.2 with hDeb | hsis
          · rcases verifyHomomorphicNExprCert_eval_eq_or_sis hCon a hv.2 with hCred | hsis
            · rw [hv.1.1.1.1.1] at hAmt
              rw [hv.1.1.1.1.2] at hDeb
              rw [hv.1.1.1.2] at hCred
              exact .inl (.cons ⟨rfl, rfl, rfl, hAmt.1, hAmt.2, hDeb.1, hCred.1⟩ hTail)
            · exact .inr hsis
          · exact .inr hsis
        · exact .inr hsis
      · exact .inr hsis
  rcases hForall2OrSis with hForall2 | hsis
  · have hpairs := Obend.Vault.Form.pairsOf_congr_eval hForall2
    simp only [List.map_map] at hpairs ⊢
    exact .inl ⟨hpairs, fun ps _ => Obend.Vault.Form.pairs_balanced tid ps asset⟩
  · exact .inr hsis

end Obend.Vault.CertifiedPartialView

end
