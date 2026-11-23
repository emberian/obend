module
/-
# Obend.SymbolicZk.ProvenZkmlGate — `UD-100` Suite Floor Gate & Streaming `MXFP4` `EinSumcheck` Session

1. **Honest `UD-100` Suite Parameter Accounting (`checkZkmlSuiteProvenFloor_sound`)**:
   - Prices Reed–Solomon / BaseFold / WHIR / `zkml-ir-v2` suite parameter profiles (`ZkmlSuiteProfile`)
     under unconditional Unique-Decoding (`UDR`), Johnson-Bound (`JBR`), extension-field LogUp ceiling,
     and BCS digest ceiling (`≥ 100,000` milli-bits, `1 ≤ logArity`), pricing small-leaf
     `(lb=6, q=86, pow=16)` (`100.022`b) and wide-leaf `(lb=2, q=148, pow=0, logArity=4)` (`100.344`b)
     while refusing withdrawn `CBR-130` (`(6, 19, 16)` = `34.563`b UDR) and `logArity = 0`.
2. **Base-Field `Goldilocks` `MXFP4` Contraction Chunk PIOP & Full-Model Sequential Stream (`OBEND.SHE.ZKML_CHUNK/v1`)**:
   - Proves `proveMxfp4ChunkIop_complete`, `verifyMxfp4ChunkIop_iff_spec`, and witness-pinned
     `verifyMxfp4ChunkIop_sound` + `verifyMxfp4ChunkIop_registered_sound` (separating `OuterMleRootHit`,
     `Mxfp4SumcheckRootHit`, `AuthenticatedFoldWalkDeviation` across all 4 `D/X/Q/S` Merkle climbs and
     butterfly fold walks, `MissedInvalidWeightLeaf`, and `ZkmlCshakeCollision`).
   - **Honest Scoping**: `proveMxfp4ChunkIop` / `verifyMxfp4ChunkIop` executes over base-field `Goldilocks`
     ($p = 2^{64} - 2^{32} + 1$) and rate-1 uncoded binary Merkle fold walks (not RS codewords or
     extension-field challenges): Lean proves the exact failure-event disjunction (`0` probability axioms;
     uniform challenges give $(\mathrm{logI} + \mathrm{logJ} + 2\mathrm{logB} + 3\mathrm{logK} + 3\mathrm{logJ}) / p$,
     with 128-bit modular squeezing shifting per-point mass to $\le \lceil 2^{128}/p \rceil / 2^{128}$);
     `udrMilliBits` prices the configured `ZkmlSuiteProfile` proximity + PoW parameter floor.
   - Enforces full-model sequential layer execution (`c.chunkIdx.toNat = idx ∧ c.layerIdx.toNat = idx`
     for `idx ∈ [0, M.layers.length)`), authenticated 8-field `suite.digest`, `pinnedNumQueries`,
     pure declarative `ZkmlTurnMeaning` (`provenZkmlJudge`), and `verifyZkmlSessionTrace_sound`.
-/
public import Obend.Judge.Class
public import Obend.SymbolicZk.EinSumcheckMxfp4
public section
namespace Obend.SymbolicZk.ProvenZkmlGate
open Obend.Apps.ZkNtt Obend.Crypto Obend.Digest.Cshake256 Obend.Digest.HashBytes Obend.Judge.Computational
set_option autoImplicit false
/-! ## 1. `SuccinctMxfp4IopProof`, `ZkmlChunkReceipt` (`OBEND.SHE.ZKML_CHUNK/v1`), Prover & Soundness -/
structure Mxfp4QueryOpening where
  dVal : Goldilocks
  dPath : List Digest32
  dFoldSteps : List FoldLayerStep
  xVal : Goldilocks
  xPath : List Digest32
  xFoldSteps : List FoldLayerStep
  qMantissa : Int
  qPath : List Digest32
  qFoldSteps : List FoldLayerStep
  sShift : Nat
  sPath : List Digest32
  sFoldSteps : List FoldLayerStep
  deriving DecidableEq, Inhabited
def Mxfp4QueryOpening.encode (o : Mxfp4QueryOpening) : List UInt8 :=
  encodeZkmlFields [ glToBe8 o.dVal, encodeDigest32List o.dPath, encodeZkmlFields (o.dFoldSteps.map FoldLayerStep.encode)
    , glToBe8 o.xVal, encodeDigest32List o.xPath, encodeZkmlFields (o.xFoldSteps.map FoldLayerStep.encode)
    , encodeSignedInt o.qMantissa, encodeDigest32List o.qPath, encodeZkmlFields (o.qFoldSteps.map FoldLayerStep.encode)
    , leb128 o.sShift, encodeDigest32List o.sPath, encodeZkmlFields (o.sFoldSteps.map FoldLayerStep.encode) ]
theorem Mxfp4QueryOpening.encode_injective {o₁ o₂ : Mxfp4QueryOpening} (h : o₁.encode = o₂.encode) : o₁ = o₂ := by
  have hf := encodeZkmlFields_injective h; simp only [List.cons.injEq, and_true] at hf; obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hf
  cases o₁; cases o₂; simp only [Mxfp4QueryOpening.mk.injEq]
  have fInj := fun {xs ys : List FoldLayerStep} (he : encodeZkmlFields (xs.map FoldLayerStep.encode) = encodeZkmlFields (ys.map FoldLayerStep.encode)) =>
    (List.map_inj_right fun _ _ => FoldLayerStep.encode_injective).mp (encodeZkmlFields_injective he)
  exact ⟨glToBe8_injective h1, encodeDigest32List_injective h2, fInj h3, glToBe8_injective h4, encodeDigest32List_injective h5, fInj h6,
    encodeSignedInt_injective h7, encodeDigest32List_injective h8, fInj h9, leb128_inj h10, encodeDigest32List_injective h11, fInj h12⟩
def encodeRoundPolyList (ps : List (RoundPoly Goldilocks)) : List UInt8 := encodeZkmlFields (ps.map fun p => encodeGoldilocksVec p.coeffs)
theorem encodeRoundPolyList_injective {p₁ p₂ : List (RoundPoly Goldilocks)} (h : encodeRoundPolyList p₁ = encodeRoundPolyList p₂) : p₁ = p₂ :=
  (List.map_inj_right fun a b heq => by cases a; cases b; exact congrArg RoundPoly.mk (encodeGoldilocksVec_injective heq)).mp (encodeZkmlFields_injective h)
structure SuccinctMxfp4IopProof where
  logI : Nat
  logJ : Nat
  logK : Nat
  logB : Nat
  dClaim : Goldilocks
  sumcheckRounds : List (RoundPoly Goldilocks)
  xClaim : Goldilocks
  qClaim : Goldilocks
  sClaim : Goldilocks
  dFoldRoots : List Digest32
  xFoldRoots : List Digest32
  qFoldRoots : List Digest32
  sFoldRoots : List Digest32
  powNonce : UInt64
  queryOpenings : List Mxfp4QueryOpening
  deriving DecidableEq, Inhabited
def encodeSuccinctMxfp4IopProof (p : SuccinctMxfp4IopProof) : List UInt8 :=
  encodeZkmlFields [ leb128 p.logI, leb128 p.logJ, leb128 p.logK, leb128 p.logB, glToBe8 p.dClaim
    , encodeRoundPolyList p.sumcheckRounds, glToBe8 p.xClaim, glToBe8 p.qClaim, glToBe8 p.sClaim , encodeDigest32List p.dFoldRoots, encodeDigest32List p.xFoldRoots
    , encodeDigest32List p.qFoldRoots, encodeDigest32List p.sFoldRoots, u64ToBe8 p.powNonce , encodeZkmlFields (p.queryOpenings.map Mxfp4QueryOpening.encode) ]
theorem encodeSuccinctMxfp4IopProof_injective {p₁ p₂ : SuccinctMxfp4IopProof} (h : encodeSuccinctMxfp4IopProof p₁ = encodeSuccinctMxfp4IopProof p₂) : p₁ = p₂ := by
  have hf := encodeZkmlFields_injective h; simp only [List.cons.injEq, and_true] at hf; obtain ⟨hi, hj, hk, hb, hd, hsr, hx, hq, hs, hdf, hxf, hqf, hsf, hpn, hqo⟩ := hf
  cases p₁; cases p₂; simp only [SuccinctMxfp4IopProof.mk.injEq]
  exact ⟨leb128_inj hi, leb128_inj hj, leb128_inj hk, leb128_inj hb, glToBe8_injective hd,
    encodeRoundPolyList_injective hsr, glToBe8_injective hx, glToBe8_injective hq, glToBe8_injective hs, encodeDigest32List_injective hdf, encodeDigest32List_injective hxf,
    encodeDigest32List_injective hqf, encodeDigest32List_injective hsf, u64ToBe8_injective hpn,
    (List.map_inj_right fun _ _ => Mxfp4QueryOpening.encode_injective).mp (encodeZkmlFields_injective hqo)⟩
structure ZkmlChunkReceipt where
  modelWeightsRoot : ByteArray
  policyFloorDigest : ByteArray
  suiteDigest : ByteArray
  chunkIdx : UInt64
  layerIdx : UInt64
  stateInCommit : ByteArray
  stateOutCommit : ByteArray
  qMerkleRoot : ByteArray
  sMerkleRoot : ByteArray
  iopProof : SuccinctMxfp4IopProof
  deriving DecidableEq, Inhabited
abbrev ZkmlChunkReceipt.WellFormed32 (c : ZkmlChunkReceipt) : Prop :=
  c.modelWeightsRoot.size = 32 ∧ c.policyFloorDigest.size = 32 ∧ c.suiteDigest.size = 32 ∧
  c.stateInCommit.size = 32 ∧ c.stateOutCommit.size = 32 ∧
  c.qMerkleRoot.size = 32 ∧ c.sMerkleRoot.size = 32
def ZkmlChunkReceipt.fields (c : ZkmlChunkReceipt) : List (List UInt8) :=
  [ c.modelWeightsRoot.data.toList, c.policyFloorDigest.data.toList, c.suiteDigest.data.toList
  , u64ToBe8 c.chunkIdx, u64ToBe8 c.layerIdx, c.stateInCommit.data.toList, c.stateOutCommit.data.toList
  , c.qMerkleRoot.data.toList, c.sMerkleRoot.data.toList, encodeSuccinctMxfp4IopProof c.iopProof ]
def ZkmlChunkReceipt.preimage (c : ZkmlChunkReceipt) : List UInt8 := encodeZkmlFields c.fields
def zkmlChunkDigest (c : ZkmlChunkReceipt) : ByteArray := cshake32ByteArray "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList c.preimage
theorem zkmlChunkDigest_size (c : ZkmlChunkReceipt) : (zkmlChunkDigest c).size = 32 := cshake32ByteArray_size _ _
theorem zkmlChunkReceipt_preimage_injective {c₁ c₂ : ZkmlChunkReceipt} (h : c₁.preimage = c₂.preimage) : c₁ = c₂ := by
  have hf := encodeZkmlFields_injective h; simp only [ZkmlChunkReceipt.fields, List.cons.injEq, and_true] at hf
  obtain ⟨hw, hp, hs, hcidx, hlidx, hsin, hsout, hqr, hsr, hiop⟩ := hf; cases c₁; cases c₂; simp only [ZkmlChunkReceipt.mk.injEq]
  exact ⟨byteArray_eq_of_toList_eq hw, byteArray_eq_of_toList_eq hp, byteArray_eq_of_toList_eq hs,
    u64ToBe8_injective hcidx, u64ToBe8_injective hlidx, byteArray_eq_of_toList_eq hsin,
    byteArray_eq_of_toList_eq hsout, byteArray_eq_of_toList_eq hqr, byteArray_eq_of_toList_eq hsr, encodeSuccinctMxfp4IopProof_injective hiop⟩
def extractZkmlChunkBinding (c₁ c₂ : ZkmlChunkReceipt) (h : zkmlChunkDigest c₁ = zkmlChunkDigest c₂) : PSum (PLift (c₁ = c₂))
      (PLift (CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList) (fun x => x = c₁.preimage ∨ x = c₂.preimage))) :=
  match extractZkmlCshake32 "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList c₁.preimage c₂.preimage h with
  | .inl hp => .inl ⟨zkmlChunkReceipt_preimage_injective hp.down⟩ | .inr hc => .inr hc
theorem zkmlChunkDigest_binds {c₁ c₂ : ZkmlChunkReceipt} (h : zkmlChunkDigest c₁ = zkmlChunkDigest c₂) :
    c₁ = c₂ ∨ CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList) (fun x => x = c₁.preimage ∨ x = c₂.preimage) := by
  cases extractZkmlChunkBinding c₁ c₂ h with | inl e => exact .inl e.down | inr c => exact .inr c.down
def mxfp4SetupRaw (suite : ZkmlSuiteProfile) (logI logJ logK logB : Nat) (wRoot pol suiteD : ByteArray) (chunkIdx layerIdx : UInt64)
    (sIn sOut qRoot sRoot : ByteArray) (dClaim : Goldilocks) : List Goldilocks × List Goldilocks × Transcript .instanceBound :=
  let relBytes := Native.bytesOfList (encodeZkmlFields [ leb128 logI, leb128 logJ, leb128 logK, leb128 logB
    , leb128 suite.fieldModulusBits, leb128 suite.extDegree, leb128 suite.logBlowup, leb128 suite.numQueries
    , leb128 suite.grindBits, leb128 suite.logTraceHeight, leb128 suite.digestBits, leb128 suite.logArity ])
  let pubIoBytes := Native.bytesOfList (encodeZkmlFields [ wRoot.data.toList, pol.data.toList, suiteD.data.toList, u64ToBe8 chunkIdx, u64ToBe8 layerIdx
    , sIn.data.toList, sOut.data.toList, qRoot.data.toList, sRoot.data.toList ])
  let tr0 := (bindInstance sOut (bindRelation "OBEND.SHE.ZKML_IOP/v1" relBytes pubIoBytes (Transcript.newUnseeded ByteArray.empty))).transcript
  let (rI, tr1) := squeezeGoldilocksVec logI tr0; let (rJ, tr2) := squeezeGoldilocksVec logJ tr1
  (rI, rJ, absorbMsg zkmlDClaimLabel (Native.bytesOfList (glToBe8 dClaim)) tr2)
def encodePostFoldPayload (p : SuccinctMxfp4IopProof) : ByteArray :=
  Native.bytesOfList (encodeZkmlFields [ glToBe8 p.xClaim, glToBe8 p.qClaim, glToBe8 p.sClaim , encodeDigest32List p.dFoldRoots, encodeDigest32List p.xFoldRoots
    , encodeDigest32List p.qFoldRoots, encodeDigest32List p.sFoldRoots ])
private def hasExactLen {α : Type} : Nat → List α → Bool
  | 0, [] => true | n + 1, _ :: xs => hasExactLen n xs | _, _ => false
private theorem hasExactLen_iff {α : Type} : ∀ (n : Nat) (xs : List α), hasExactLen n xs = true ↔ xs.length = n
  | 0, [] => by simp [hasExactLen]
  | 0, _ :: _ => by simp [hasExactLen]
  | _ + 1, [] => by simp [hasExactLen]
  | n + 1, _ :: xs => by simp [hasExactLen, hasExactLen_iff n xs]
def foldRootsMatchDims (p : SuccinctMxfp4IopProof) : Bool :=
  hasExactLen (p.logI + p.logJ) p.dFoldRoots && hasExactLen (p.logI + p.logB + p.logK) p.xFoldRoots &&
  hasExactLen (p.logB + p.logK + p.logJ) p.qFoldRoots && hasExactLen (p.logK + p.logJ) p.sFoldRoots
private theorem foldRootsMatchDims_iff (p : SuccinctMxfp4IopProof) : foldRootsMatchDims p = true ↔
    p.dFoldRoots.length = p.logI + p.logJ ∧ p.xFoldRoots.length = p.logI + p.logB + p.logK ∧
    p.qFoldRoots.length = p.logB + p.logK + p.logJ ∧ p.sFoldRoots.length = p.logK + p.logJ := by
  simp [foldRootsMatchDims, Bool.and_eq_true, hasExactLen_iff, and_assoc]
abbrev ProofBoundsSpec (p : SuccinctMxfp4IopProof) : Prop :=
  (1 ≤ p.logI ∧ 1 ≤ p.logJ ∧ 1 ≤ p.logK ∧ 1 ≤ p.logB ∧
    p.logI + p.logJ < maxZkmlHypercubeVars ∧ p.logI + p.logB + p.logK < maxZkmlHypercubeVars ∧
    p.logB + p.logK + p.logJ < maxZkmlHypercubeVars) ∧
  (p.dFoldRoots.length = p.logI + p.logJ ∧ p.xFoldRoots.length = p.logI + p.logB + p.logK ∧
    p.qFoldRoots.length = p.logB + p.logK + p.logJ ∧ p.sFoldRoots.length = p.logK + p.logJ)
def proofBoundsOk (p : SuccinctMxfp4IopProof) : Bool :=
  decide (1 ≤ p.logI ∧ 1 ≤ p.logJ ∧ 1 ≤ p.logK ∧ 1 ≤ p.logB ∧
    p.logI + p.logJ < maxZkmlHypercubeVars ∧ p.logI + p.logB + p.logK < maxZkmlHypercubeVars ∧
    p.logB + p.logK + p.logJ < maxZkmlHypercubeVars) && foldRootsMatchDims p
private theorem proofBoundsOk_iff (p : SuccinctMxfp4IopProof) : proofBoundsOk p = true ↔ ProofBoundsSpec p := by
  simp only [proofBoundsOk, ProofBoundsSpec, Bool.and_eq_true, decide_eq_true_eq, foldRootsMatchDims_iff]
abbrev ReceiptBoundsSpec (c : ZkmlChunkReceipt) : Prop := c.WellFormed32 ∧ ProofBoundsSpec c.iopProof
def receiptBoundsOk (c : ZkmlChunkReceipt) : Bool := decide c.WellFormed32 && proofBoundsOk c.iopProof
private theorem receiptBoundsOk_iff (c : ZkmlChunkReceipt) : receiptBoundsOk c = true ↔ ReceiptBoundsSpec c := by
  simp only [receiptBoundsOk, ReceiptBoundsSpec, Bool.and_eq_true, decide_eq_true_eq, proofBoundsOk_iff]
def runMxfp4SumcheckPhase (suite : ZkmlSuiteProfile) (c : ZkmlChunkReceipt) :
    Option (List Goldilocks × List Goldilocks × List Goldilocks × List Goldilocks × List Goldilocks × Goldilocks × Transcript .instanceBound) :=
  let p := c.iopProof
  if !receiptBoundsOk c then none
  else
    let setup := mxfp4SetupRaw suite p.logI p.logJ p.logK p.logB c.modelWeightsRoot c.policyFloorDigest c.suiteDigest c.chunkIdx c.layerIdx
      c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot p.dClaim
    match verifyScheduledSumcheck (mxfp4DegSchedule p.logB p.logK p.logJ) p.dClaim p.sumcheckRounds setup.2.2 with
    | none => none
    | some ((allChals, finalVal), trPostSum) =>
      let rB := allChals.take p.logB; let rK := (allChals.drop p.logB).take p.logK; let rJp := allChals.drop (p.logB + p.logK)
      let expectedFinal := CommRingOps.mul (eqPolyVec setup.2.1 rJp) (CommRingOps.mul p.xClaim (CommRingOps.mul p.qClaim p.sClaim))
      if decide (finalVal = expectedFinal) then
        some (setup.1, setup.2.1, rB, rK, rJp, finalVal, absorbMsg zkmlFoldRootsLabel (encodePostFoldPayload p) trPostSum)
      else none
@[expose] def ChunkMeetsPow (suite : ZkmlSuiteProfile) (powBits : Nat) (c : ZkmlChunkReceipt) : Prop :=
  suite.grindBits ≤ powBits ∧ (powBits = 0 → c.iopProof.powNonce = 0) ∧ ReceiptBoundsSpec c ∧
  ∃ (rI rJ allChals : List Goldilocks) (fv : Goldilocks) (trPostSum : Transcript .instanceBound),
    let p := c.iopProof
    let setup := mxfp4SetupRaw suite p.logI p.logJ p.logK p.logB c.modelWeightsRoot c.policyFloorDigest c.suiteDigest c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit
      c.qMerkleRoot c.sMerkleRoot p.dClaim
    rI = setup.1 ∧ rJ = setup.2.1 ∧
    ScheduledSumcheckSpec (mxfp4DegSchedule p.logB p.logK p.logJ) p.dClaim p.sumcheckRounds setup.2.2 allChals fv trPostSum ∧
    fv = CommRingOps.mul (eqPolyVec rJ (allChals.drop (p.logB + p.logK))) (CommRingOps.mul p.xClaim (CommRingOps.mul p.qClaim p.sClaim)) ∧
    powBits ≤ 64 ∧
    digestLow64LE (powCandidateState (absorbMsg zkmlFoldRootsLabel (encodePostFoldPayload p) trPostSum) p.powNonce) % (2 ^ powBits) = 0
def checkMxfp4ChunkPow (suite : ZkmlSuiteProfile) (powBits : Nat) (c : ZkmlChunkReceipt) : Bool :=
  decide (suite.grindBits ≤ powBits) && decide (powBits = 0 → c.iopProof.powNonce = 0) &&
  match runMxfp4SumcheckPhase suite c with
  | none => false | some (_, _, _, _, _, _, trPostFold) => checkChunkPow powBits (powCandidateState trPostFold c.iopProof.powNonce)
theorem checkMxfp4ChunkPow_iff (suite : ZkmlSuiteProfile) (powBits : Nat) (c : ZkmlChunkReceipt) :
    checkMxfp4ChunkPow suite powBits c = true ↔ ChunkMeetsPow suite powBits c := by
  unfold checkMxfp4ChunkPow ChunkMeetsPow runMxfp4SumcheckPhase; dsimp only; let p := c.iopProof
  let setup := mxfp4SetupRaw suite p.logI p.logJ p.logK p.logB c.modelWeightsRoot c.policyFloorDigest c.suiteDigest c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit
    c.qMerkleRoot c.sMerkleRoot p.dClaim
  constructor
  · intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; obtain ⟨⟨hGr, hZN⟩, hPh⟩ := h
    cases hRb : receiptBoundsOk c
    · simp [hRb] at hPh
    · have hRbSpec := (receiptBoundsOk_iff c).mp hRb; simp only [hRb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPh
      refine ⟨hGr, hZN, hRbSpec, ?_⟩
      cases hVer : verifyScheduledSumcheck (mxfp4DegSchedule p.logB p.logK p.logJ) p.dClaim p.sumcheckRounds setup.2.2 with
      | none => dsimp only [p, setup] at hVer; rw [hVer] at hPh; cases hPh
      | some sub =>
        rcases sub with ⟨⟨allChals, fv⟩, trPS⟩; have hVer' := hVer; dsimp only [p, setup] at hVer'; rw [hVer'] at hPh; dsimp only at hPh
        by_cases hFv : fv = CommRingOps.mul (eqPolyVec setup.2.1 (allChals.drop (p.logB + p.logK))) (CommRingOps.mul p.xClaim (CommRingOps.mul p.qClaim p.sClaim))
        · have hFv' := hFv; dsimp only [p, setup] at hFv'; simp only [hFv', ↓reduceIte, checkChunkPow, Bool.and_eq_true, decide_eq_true_eq] at hPh
          exact ⟨_, _, allChals, fv, trPS, rfl, rfl, (verifyScheduledSumcheck_iff_spec ..).mp hVer, hFv, hPh.1, hPh.2⟩
        · have hFv' := hFv; dsimp only [p, setup] at hFv'; simp [hFv'] at hPh
  · rintro ⟨hGr, hZN, hRbSpec, rI, rJ, allChals, fv, trPS, rfl, rfl, hSpec, hFv, hP64, hMod⟩
    have hRb := (receiptBoundsOk_iff c).mpr hRbSpec
    have hVer := (verifyScheduledSumcheck_iff_spec (mxfp4DegSchedule p.logB p.logK p.logJ) p.dClaim fv p.sumcheckRounds allChals setup.2.2 trPS).mpr hSpec
    dsimp only [p, setup] at hVer; rw [hRb]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rw [hVer]
    simp [decide_eq_true hGr, decide_eq_true hZN, decide_eq_true hFv, checkChunkPow, decide_eq_true hP64, decide_eq_true hMod]
def verifyMxfp4QueryLocal (c : ZkmlChunkReceipt) (qRaw : Nat) (op : Mxfp4QueryOpening) : Bool :=
  let p := c.iopProof; let nD := 2 ^ (p.logI + p.logJ); let nX := 2 ^ (p.logI + p.logB + p.logK); let nQ := 2 ^ (p.logB + p.logK + p.logJ); let nS := 2 ^ (p.logK + p.logJ)
  isValidE2m1Mantissa op.qMantissa && isValidMxfp4Shift op.sShift &&
  climbZkml32 nD (qRaw % nD) (hashTensorLeaf (qRaw % nD) op.dVal) op.dPath c.stateOutCommit &&
  climbZkml32 nX (qRaw % nX) (hashTensorLeaf (qRaw % nX) op.xVal) op.xPath c.stateInCommit &&
  climbZkml32 nQ (qRaw % nQ) (hashMantissaLeaf (qRaw % nQ) op.qMantissa) op.qPath c.qMerkleRoot &&
  climbZkml32 nS (qRaw % nS) (hashShiftLeaf (qRaw % nS) op.sShift) op.sPath c.sMerkleRoot
def verifyMxfp4QueryOpening (c : ZkmlChunkReceipt) (rI rJ rB rK rJp : List Goldilocks) (qRaw : Nat) (op : Mxfp4QueryOpening) : Bool :=
  let p := c.iopProof; let vD := p.logI + p.logJ; let vX := p.logI + p.logB + p.logK; let vQ := p.logB + p.logK + p.logJ; let vS := p.logK + p.logJ
  verifyMxfp4QueryLocal c qRaw op &&
  verifyFoldWalk 0 vD (qRaw % (2 ^ vD)) op.dVal p.dClaim (rI ++ rJ) p.dFoldRoots op.dFoldSteps &&
  verifyFoldWalk 0 vX (qRaw % (2 ^ vX)) op.xVal p.xClaim (rI ++ rB ++ rK) p.xFoldRoots op.xFoldSteps &&
  verifyFoldWalk 0 vQ (qRaw % (2 ^ vQ)) (intToGoldilocks op.qMantissa) p.qClaim (rB ++ rK ++ rJp) p.qFoldRoots op.qFoldSteps &&
  verifyFoldWalk 0 vS (qRaw % (2 ^ vS)) (shiftToGoldilocks op.sShift) p.sClaim (rK ++ rJp) p.sFoldRoots op.sFoldSteps
def verifyMxfp4QueryList (c : ZkmlChunkReceipt) (rI rJ rB rK rJp : List Goldilocks) : List Nat → List Mxfp4QueryOpening → Bool
  | [], [] => true | [], _ :: _ => false | _ :: _, [] => false
  | q :: qs, op :: ops => verifyMxfp4QueryOpening c rI rJ rB rK rJp q op && verifyMxfp4QueryList c rI rJ rB rK rJp qs ops
inductive ZipAll {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : ZipAll R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → ZipAll R as bs → ZipAll R (a :: as) (b :: bs)
def QueryOpeningSpec (c : ZkmlChunkReceipt) (rI rJ rB rK rJp : List Goldilocks) (qRaw : Nat) (op : Mxfp4QueryOpening) : Prop :=
  let p := c.iopProof; let vD := p.logI + p.logJ; let vX := p.logI + p.logB + p.logK; let vQ := p.logB + p.logK + p.logJ; let vS := p.logK + p.logJ
  op.qMantissa ∈ e2m1Domain ∧ op.sShift ≤ maxMxfp4ScaleShift ∧
  (∃ r : Digest32, climbMerkle32 zkmlMerkleHash32 (2 ^ vD) (qRaw % 2 ^ vD) (hashTensorLeaf (qRaw % 2 ^ vD) op.dVal) op.dPath = some r ∧ r.bytes = c.stateOutCommit) ∧
  (∃ r : Digest32, climbMerkle32 zkmlMerkleHash32 (2 ^ vX) (qRaw % 2 ^ vX) (hashTensorLeaf (qRaw % 2 ^ vX) op.xVal) op.xPath = some r ∧ r.bytes = c.stateInCommit) ∧
  (∃ r : Digest32, climbMerkle32 zkmlMerkleHash32 (2 ^ vQ) (qRaw % 2 ^ vQ) (hashMantissaLeaf (qRaw % 2 ^ vQ) op.qMantissa) op.qPath = some r ∧ r.bytes = c.qMerkleRoot) ∧
  (∃ r : Digest32, climbMerkle32 zkmlMerkleHash32 (2 ^ vS) (qRaw % 2 ^ vS) (hashShiftLeaf (qRaw % 2 ^ vS) op.sShift) op.sPath = some r ∧ r.bytes = c.sMerkleRoot) ∧
  FoldWalkSpec 0 vD (qRaw % 2 ^ vD) op.dVal p.dClaim (rI ++ rJ) p.dFoldRoots op.dFoldSteps ∧
  FoldWalkSpec 0 vX (qRaw % 2 ^ vX) op.xVal p.xClaim (rI ++ rB ++ rK) p.xFoldRoots op.xFoldSteps ∧
  FoldWalkSpec 0 vQ (qRaw % 2 ^ vQ) (intToGoldilocks op.qMantissa) p.qClaim (rB ++ rK ++ rJp) p.qFoldRoots op.qFoldSteps ∧
  FoldWalkSpec 0 vS (qRaw % 2 ^ vS) (shiftToGoldilocks op.sShift) p.sClaim (rK ++ rJp) p.sFoldRoots op.sFoldSteps
private theorem verifyMxfp4QueryOpening_iff_spec (c : ZkmlChunkReceipt) (rI rJ rB rK rJp : List Goldilocks) (qRaw : Nat) (op : Mxfp4QueryOpening) :
    verifyMxfp4QueryOpening c rI rJ rB rK rJp qRaw op = true ↔ QueryOpeningSpec c rI rJ rB rK rJp qRaw op := by
  unfold verifyMxfp4QueryOpening verifyMxfp4QueryLocal QueryOpeningSpec isValidE2m1Mantissa isValidMxfp4Shift
  simp only [Bool.and_eq_true, decide_eq_true_eq, climbZkml32_iff, verifyFoldWalk_iff_spec, and_assoc]
private theorem verifyMxfp4QueryList_iff_spec (c : ZkmlChunkReceipt) (rI rJ rB rK rJp : List Goldilocks) : ∀ (qs : List Nat) (ops : List Mxfp4QueryOpening),
      verifyMxfp4QueryList c rI rJ rB rK rJp qs ops = true ↔ ZipAll (QueryOpeningSpec c rI rJ rB rK rJp) qs ops
  | [], [] => Iff.intro (fun _ => .nil) (fun _ => rfl) | [], _ :: _ => Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  | _ :: _, [] => Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  | q :: qs, op :: ops => by
    simp only [verifyMxfp4QueryList, Bool.and_eq_true, verifyMxfp4QueryOpening_iff_spec, verifyMxfp4QueryList_iff_spec c rI rJ rB rK rJp qs ops]
    exact ⟨fun ⟨h1, h2⟩ => .cons h1 h2, fun h => by cases h with | cons h1 h2 => exact ⟨h1, h2⟩⟩
private theorem mem_of_getElem?_some {α : Type} : ∀ {xs : List α} {i : Nat} {x : α}, xs[i]? = some x → x ∈ xs
  | x :: _, 0, _, h => by simp at h; exact h ▸ .head _
  | _ :: _, _ + 1, _, h => .tail _ (mem_of_getElem?_some h)
private theorem layerAndFold_implies_proofBounds {M : Mxfp4ModelManifest} {c : ZkmlChunkReceipt}
    (hL : M.layers ≠ [] ∧ M.layers.length ≤ 1024 ∧ (∀ lk ∈ M.layers, 1 ≤ lk.logI ∧ 1 ≤ lk.logJ ∧ 1 ≤ lk.logK ∧ 1 ≤ lk.logB ∧
      lk.logI + lk.logJ < maxZkmlHypercubeVars ∧ lk.logI + lk.logB + lk.logK < maxZkmlHypercubeVars ∧
      lk.logB + lk.logK + lk.logJ < maxZkmlHypercubeVars ∧ lk.qMerkleRoot.size = 32 ∧ lk.sMerkleRoot.size = 32) ∧ M.root = c.modelWeightsRoot ∧
      ∃ lk, M.layers[c.layerIdx.toNat]? = some lk ∧ lk.logI = c.iopProof.logI ∧ lk.logJ = c.iopProof.logJ ∧
        lk.logK = c.iopProof.logK ∧ lk.logB = c.iopProof.logB ∧ lk.qMerkleRoot = c.qMerkleRoot ∧ lk.sMerkleRoot = c.sMerkleRoot)
    (hFL : c.iopProof.dFoldRoots.length = c.iopProof.logI + c.iopProof.logJ ∧ c.iopProof.xFoldRoots.length = c.iopProof.logI + c.iopProof.logB + c.iopProof.logK ∧
      c.iopProof.qFoldRoots.length = c.iopProof.logB + c.iopProof.logK + c.iopProof.logJ ∧ c.iopProof.sFoldRoots.length = c.iopProof.logK + c.iopProof.logJ) :
    proofBoundsOk c.iopProof = true := by
  obtain ⟨_, _, hAll, _, lk, hGet, hli, hlj, hlk, hlb, _, _⟩ := hL; have hk := hAll lk (mem_of_getElem?_some hGet)
  rw [hli, hlj, hlk, hlb] at hk; exact (proofBoundsOk_iff c.iopProof).mpr ⟨⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1⟩, hFL⟩
def layerMatchesReceipt (M : Mxfp4ModelManifest) (c : ZkmlChunkReceipt) : Bool :=
  M.valid && decide (M.root = c.modelWeightsRoot) &&
  match M.layers[c.layerIdx.toNat]? with
  | none => false
  | some lk =>
    decide (lk.logI = c.iopProof.logI ∧ lk.logJ = c.iopProof.logJ ∧ lk.logK = c.iopProof.logK ∧ lk.logB = c.iopProof.logB ∧
      lk.qMerkleRoot = c.qMerkleRoot ∧ lk.sMerkleRoot = c.sMerkleRoot)
/-- Pure declarative `Prop` specification of chunk-IOP validity (`0` calls to executable `Bool` verifiers). -/
@[expose] def ValidMxfp4ChunkIopSpec (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (powBits : Nat) (c : ZkmlChunkReceipt) : Prop :=
  let p := c.iopProof
  c.WellFormed32 ∧ (1 ≤ suite.numQueries ∧ suite.numQueries ≤ 1024 ∧ 1 ≤ suite.logArity) ∧
  (M.layers ≠ [] ∧ M.layers.length ≤ 1024 ∧ (∀ lk ∈ M.layers, 1 ≤ lk.logI ∧ 1 ≤ lk.logJ ∧ 1 ≤ lk.logK ∧ 1 ≤ lk.logB ∧
      lk.logI + lk.logJ < maxZkmlHypercubeVars ∧ lk.logI + lk.logB + lk.logK < maxZkmlHypercubeVars ∧
      lk.logB + lk.logK + lk.logJ < maxZkmlHypercubeVars ∧ lk.qMerkleRoot.size = 32 ∧ lk.sMerkleRoot.size = 32) ∧ M.root = c.modelWeightsRoot ∧
    ∃ lk, M.layers[c.layerIdx.toNat]? = some lk ∧ lk.logI = p.logI ∧ lk.logJ = p.logJ ∧
      lk.logK = p.logK ∧ lk.logB = p.logB ∧ lk.qMerkleRoot = c.qMerkleRoot ∧ lk.sMerkleRoot = c.sMerkleRoot) ∧
  (p.dFoldRoots.length = p.logI + p.logJ ∧ p.xFoldRoots.length = p.logI + p.logB + p.logK ∧
   p.qFoldRoots.length = p.logB + p.logK + p.logJ ∧ p.sFoldRoots.length = p.logK + p.logJ) ∧
  ∃ (allChals : List Goldilocks) (fv : Goldilocks) (trPostSum : Transcript .instanceBound),
    let setup := mxfp4SetupRaw suite p.logI p.logJ p.logK p.logB c.modelWeightsRoot c.policyFloorDigest
      c.suiteDigest c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot p.dClaim
    let rB := allChals.take p.logB; let rK := (allChals.drop p.logB).take p.logK; let rJp := allChals.drop (p.logB + p.logK)
    let trPF := absorbMsg zkmlFoldRootsLabel (encodePostFoldPayload p) trPostSum
    ScheduledSumcheckSpec (mxfp4DegSchedule p.logB p.logK p.logJ) p.dClaim p.sumcheckRounds setup.2.2 allChals fv trPostSum ∧
    fv = CommRingOps.mul (eqPolyVec setup.2.1 rJp) (CommRingOps.mul p.xClaim (CommRingOps.mul p.qClaim p.sClaim)) ∧
    suite.grindBits ≤ powBits ∧ (powBits = 0 → p.powNonce = 0) ∧ powBits ≤ 64 ∧
    digestLow64LE (powCandidateState trPF p.powNonce) % (2 ^ powBits) = 0 ∧
    ZipAll (QueryOpeningSpec c setup.1 setup.2.1 rB rK rJp)
      (squeezeRawQueries suite.numQueries (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 p.powNonce)) trPF)).1 p.queryOpenings
def verifyMxfp4ChunkIop (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (powBits : Nat) (c : ZkmlChunkReceipt) : Bool :=
  let p := c.iopProof
  decide c.WellFormed32 && decide (1 ≤ suite.numQueries ∧ suite.numQueries ≤ 1024 ∧ 1 ≤ suite.logArity) &&
  layerMatchesReceipt M c && foldRootsMatchDims p &&
  match runMxfp4SumcheckPhase suite c with
  | none => false
  | some (rI, rJ, rB, rK, rJp, _, trPostFold) =>
    decide (suite.grindBits ≤ powBits) && decide (powBits = 0 → p.powNonce = 0) &&
    checkChunkPow powBits (powCandidateState trPostFold p.powNonce) &&
    verifyMxfp4QueryList c rI rJ rB rK rJp (squeezeRawQueries suite.numQueries
        (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 p.powNonce)) trPostFold)).1 p.queryOpenings
private theorem layerMatchesReceipt_iff (M : Mxfp4ModelManifest) (c : ZkmlChunkReceipt) : layerMatchesReceipt M c = true ↔ M.layers ≠ [] ∧ M.layers.length ≤ 1024 ∧
      (∀ lk ∈ M.layers, 1 ≤ lk.logI ∧ 1 ≤ lk.logJ ∧ 1 ≤ lk.logK ∧ 1 ≤ lk.logB ∧
        lk.logI + lk.logJ < maxZkmlHypercubeVars ∧ lk.logI + lk.logB + lk.logK < maxZkmlHypercubeVars ∧
        lk.logB + lk.logK + lk.logJ < maxZkmlHypercubeVars ∧ lk.qMerkleRoot.size = 32 ∧ lk.sMerkleRoot.size = 32) ∧ M.root = c.modelWeightsRoot ∧
      ∃ lk, M.layers[c.layerIdx.toNat]? = some lk ∧ lk.logI = c.iopProof.logI ∧ lk.logJ = c.iopProof.logJ ∧
        lk.logK = c.iopProof.logK ∧ lk.logB = c.iopProof.logB ∧ lk.qMerkleRoot = c.qMerkleRoot ∧ lk.sMerkleRoot = c.sMerkleRoot := by
  unfold layerMatchesReceipt Mxfp4ModelManifest.valid Mxfp4LayerKey.validDims; cases hOpt : M.layers[c.layerIdx.toNat]? with
  | none => simp | some lk => simp [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]
theorem verifyMxfp4ChunkIop_iff_spec (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (powBits : Nat) (c : ZkmlChunkReceipt) :
    verifyMxfp4ChunkIop suite M powBits c = true ↔ ValidMxfp4ChunkIopSpec suite M powBits c := by
  unfold verifyMxfp4ChunkIop ValidMxfp4ChunkIopSpec runMxfp4SumcheckPhase; dsimp only; let p := c.iopProof
  let setup := mxfp4SetupRaw suite p.logI p.logJ p.logK p.logB c.modelWeightsRoot c.policyFloorDigest
    c.suiteDigest c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot p.dClaim
  constructor
  · intro h; simp only [Bool.and_eq_true, decide_eq_true_eq, layerMatchesReceipt_iff, foldRootsMatchDims_iff] at h
    obtain ⟨⟨⟨⟨hWf, hS⟩, hL⟩, hFL⟩, hPh⟩ := h; have hPb := layerAndFold_implies_proofBounds hL hFL
    have hRb : receiptBoundsOk c = true := by simp [receiptBoundsOk, decide_eq_true hWf, hPb]
    simp only [hRb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPh; refine ⟨hWf, hS, hL, hFL, ?_⟩
    cases hVer : verifyScheduledSumcheck (mxfp4DegSchedule p.logB p.logK p.logJ) p.dClaim p.sumcheckRounds setup.2.2 with
    | none => dsimp only [p, setup] at hVer; rw [hVer] at hPh; cases hPh
    | some sub =>
      rcases sub with ⟨⟨allChals, fv⟩, trPS⟩; have hVer' := hVer; dsimp only [p, setup] at hVer'; rw [hVer'] at hPh; dsimp only at hPh
      by_cases hFv : fv = CommRingOps.mul (eqPolyVec setup.2.1 (allChals.drop (p.logB + p.logK))) (CommRingOps.mul p.xClaim (CommRingOps.mul p.qClaim p.sClaim))
      · have hFv' := hFv; dsimp only [p, setup] at hFv'
        simp only [hFv', ↓reduceIte, Bool.and_eq_true, checkChunkPow, decide_eq_true_eq, verifyMxfp4QueryList_iff_spec] at hPh
        obtain ⟨⟨⟨hGr, hZN⟩, hP64, hMod⟩, hQL⟩ := hPh
        exact ⟨allChals, fv, trPS, (verifyScheduledSumcheck_iff_spec ..).mp hVer, hFv, hGr, hZN, hP64, hMod, hQL⟩
      · have hFv' := hFv; dsimp only [p, setup] at hFv'; simp [hFv'] at hPh
  · rintro ⟨hWf, hS, hL, hFL, allChals, fv, trPS, hSpec, hFv, hGr, hZN, hP64, hMod, hQL⟩
    have hPb := layerAndFold_implies_proofBounds hL hFL
    have hRb : receiptBoundsOk c = true := by simp [receiptBoundsOk, decide_eq_true hWf, hPb]
    have hVer := (verifyScheduledSumcheck_iff_spec (mxfp4DegSchedule p.logB p.logK p.logJ) p.dClaim fv p.sumcheckRounds allChals setup.2.2 trPS).mpr hSpec
    dsimp only [p, setup] at hVer; rw [decide_eq_true hWf, decide_eq_true hS, (layerMatchesReceipt_iff M c).mpr hL, (foldRootsMatchDims_iff p).mpr hFL, hRb]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rw [hVer]
    simp [decide_eq_true hFv, decide_eq_true hGr, decide_eq_true hZN, checkChunkPow, decide_eq_true hP64, decide_eq_true hMod, (verifyMxfp4QueryList_iff_spec ..).mpr hQL]
structure Mxfp4ChunkWitness where
  model : Mxfp4ModelManifest
  layerIdx : UInt64
  logI : Nat
  logJ : Nat
  logK : Nat
  logB : Nat
  xTbl : List Goldilocks
  qInts : List Int
  sShifts : List Nat
  dTbl : List Goldilocks
  deriving DecidableEq, Inhabited
def mxfp4ActRoot32 (xs : List Goldilocks) : Digest32 := merkleRoot32 zkmlMerkleHash32 (xs.mapIdx fun i x => hashTensorLeaf i x)
def mxfp4OutRoot32 (ds : List Goldilocks) : Digest32 := merkleRoot32 zkmlMerkleHash32 (ds.mapIdx fun i d => hashTensorLeaf i d)
def mxfp4MantissaRoot32 (qs : List Int) : Digest32 := merkleRoot32 zkmlMerkleHash32 (qs.mapIdx fun i q => hashMantissaLeaf i q)
def mxfp4ShiftRoot32 (ss : List Nat) : Digest32 := merkleRoot32 zkmlMerkleHash32 (ss.mapIdx fun i sh => hashShiftLeaf i sh)
def buildHonestMxfp4Witness (M : Mxfp4ModelManifest) (layerIdx : UInt64) (logI logJ logK logB : Nat) (xTbl : List Goldilocks)
    (qInts : List Int) (sShifts : List Nat) : Mxfp4ChunkWitness :=
  { model := M, layerIdx, logI, logJ, logK, logB, xTbl, qInts, sShifts
    dTbl := mxfp4ContractTable logI logJ logK logB xTbl qInts sShifts }
@[expose] def ValidMxfp4ChunkWitness (w : Mxfp4ChunkWitness) : Prop :=
  1 ≤ w.logI ∧ 1 ≤ w.logJ ∧ 1 ≤ w.logK ∧ 1 ≤ w.logB ∧
  w.logI + w.logJ < maxZkmlHypercubeVars ∧ w.logI + w.logB + w.logK < maxZkmlHypercubeVars ∧
  w.logB + w.logK + w.logJ < maxZkmlHypercubeVars ∧
  w.model.valid = true ∧
  w.model.layers[w.layerIdx.toNat]? = some ⟨w.logI, w.logJ, w.logK, w.logB, (mxfp4MantissaRoot32 w.qInts).bytes, (mxfp4ShiftRoot32 w.sShifts).bytes⟩ ∧
  w.xTbl.length = 2 ^ (w.logI + w.logB + w.logK) ∧
  w.qInts.length = 2 ^ (w.logB + w.logK + w.logJ) ∧
  w.sShifts.length = 2 ^ (w.logK + w.logJ) ∧
  (∀ q ∈ w.qInts, isValidE2m1Mantissa q = true) ∧
  (∀ sh ∈ w.sShifts, isValidMxfp4Shift sh = true) ∧
  w.dTbl = mxfp4ContractTable w.logI w.logJ w.logK w.logB w.xTbl w.qInts w.sShifts
def proveMxfp4QueryOpening (w : Mxfp4ChunkWitness) (rI rJ rB rK rJp : List Goldilocks) (qRaw : Nat) : Mxfp4QueryOpening :=
  let vD := w.logI + w.logJ; let vX := w.logI + w.logB + w.logK; let vQ := w.logB + w.logK + w.logJ; let vS := w.logK + w.logJ
  let iD := qRaw % (2 ^ vD); let iX := qRaw % (2 ^ vX); let iQ := qRaw % (2 ^ vQ); let iS := qRaw % (2 ^ vS)
  let qTbl := w.qInts.map intToGoldilocks; let sTbl := w.sShifts.map shiftToGoldilocks
  { dVal := w.dTbl.getD iD Goldilocks.zero
    dPath := merklePath32 zkmlMerkleHash32 (w.dTbl.mapIdx fun i d => hashTensorLeaf i d) iD
    dFoldSteps := openFoldWalk 0 vD iD w.dTbl (rI ++ rJ)
    xVal := w.xTbl.getD iX Goldilocks.zero
    xPath := merklePath32 zkmlMerkleHash32 (w.xTbl.mapIdx fun i x => hashTensorLeaf i x) iX
    xFoldSteps := openFoldWalk 0 vX iX w.xTbl (rI ++ rB ++ rK)
    qMantissa := w.qInts.getD iQ 0
    qPath := merklePath32 zkmlMerkleHash32 (w.qInts.mapIdx fun i q => hashMantissaLeaf i q) iQ
    qFoldSteps := openFoldWalk 0 vQ iQ qTbl (rB ++ rK ++ rJp)
    sShift := w.sShifts.getD iS 0
    sPath := merklePath32 zkmlMerkleHash32 (w.sShifts.mapIdx fun i sh => hashShiftLeaf i sh) iS
    sFoldSteps := openFoldWalk 0 vS iS sTbl (rK ++ rJp) }
def proveMxfp4ChunkIop (suite : ZkmlSuiteProfile) (policyFloorDigest suiteDigest : ByteArray)
    (chunkIdx : UInt64) (w : Mxfp4ChunkWitness) (powNonce : UInt64) : ZkmlChunkReceipt :=
  let wRoot := w.model.root; let sIn := (mxfp4ActRoot32 w.xTbl).bytes; let sOut := (mxfp4OutRoot32 w.dTbl).bytes
  let qRoot := (mxfp4MantissaRoot32 w.qInts).bytes; let sRoot := (mxfp4ShiftRoot32 w.sShifts).bytes
  let qTbl := w.qInts.map intToGoldilocks; let sTbl := w.sShifts.map shiftToGoldilocks
  let setup0 := mxfp4SetupRaw suite w.logI w.logJ w.logK w.logB wRoot policyFloorDigest suiteDigest chunkIdx w.layerIdx sIn sOut qRoot sRoot Goldilocks.zero
  let dClaim := mleEval w.dTbl (setup0.1 ++ setup0.2.1)
  let setup := mxfp4SetupRaw suite w.logI w.logJ w.logK w.logB wRoot policyFloorDigest suiteDigest chunkIdx w.layerIdx sIn sOut qRoot sRoot dClaim
  let rI := setup.1; let rJ := setup.2.1; let (rounds, rB, rK, rJp, trPostSum) := proveMxfp4Sumcheck w.logJ w.logK w.logB w.xTbl qTbl sTbl rI rJ setup.2.2
  let preProof : SuccinctMxfp4IopProof :=
    { logI := w.logI, logJ := w.logJ, logK := w.logK, logB := w.logB, dClaim
      sumcheckRounds := rounds, xClaim := mleEval w.xTbl (rI ++ rB ++ rK)
      qClaim := mleEval qTbl (rB ++ rK ++ rJp), sClaim := mleEval sTbl (rK ++ rJp)
      dFoldRoots := buildFoldRoots 0 (w.logI + w.logJ) w.dTbl (rI ++ rJ)
      xFoldRoots := buildFoldRoots 0 (w.logI + w.logB + w.logK) w.xTbl (rI ++ rB ++ rK)
      qFoldRoots := buildFoldRoots 0 (w.logB + w.logK + w.logJ) qTbl (rB ++ rK ++ rJp)
      sFoldRoots := buildFoldRoots 0 (w.logK + w.logJ) sTbl (rK ++ rJp)
      powNonce, queryOpenings := [] }
  let trPostFold := absorbMsg zkmlFoldRootsLabel (encodePostFoldPayload preProof) trPostSum
  let (qs, _) := squeezeRawQueries suite.numQueries (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 powNonce)) trPostFold)
  { modelWeightsRoot := wRoot, policyFloorDigest, suiteDigest, chunkIdx, layerIdx := w.layerIdx
    stateInCommit := sIn, stateOutCommit := sOut, qMerkleRoot := qRoot, sMerkleRoot := sRoot
    iopProof := { preProof with queryOpenings := qs.map (proveMxfp4QueryOpening w rI rJ rB rK rJp) } }
theorem proveMxfp4ChunkIop_headers (suite : ZkmlSuiteProfile) (pol suiteD : ByteArray) (idx : UInt64) (w : Mxfp4ChunkWitness) (nonce : UInt64) :
    let c := proveMxfp4ChunkIop suite pol suiteD idx w nonce
    c.modelWeightsRoot = w.model.root ∧ c.policyFloorDigest = pol ∧ c.suiteDigest = suiteD ∧
    c.chunkIdx = idx ∧ c.layerIdx = w.layerIdx ∧
    c.stateInCommit = (mxfp4ActRoot32 w.xTbl).bytes ∧ c.stateOutCommit = (mxfp4OutRoot32 w.dTbl).bytes ∧
    c.qMerkleRoot = (mxfp4MantissaRoot32 w.qInts).bytes ∧ c.sMerkleRoot = (mxfp4ShiftRoot32 w.sShifts).bytes ∧
    c.iopProof.logI = w.logI ∧ c.iopProof.logJ = w.logJ ∧
    c.iopProof.logK = w.logK ∧ c.iopProof.logB = w.logB ∧ c.iopProof.powNonce = nonce :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
private theorem mxfp4SetupRaw_pts_indep (suite : ZkmlSuiteProfile) (li lj lk lb : Nat)
    (wR pol sD : ByteArray) (ci lidx : UInt64) (sIn sOut qR sR : ByteArray) (d₁ d₂ : Goldilocks) : (mxfp4SetupRaw suite li lj lk lb wR pol sD ci lidx sIn sOut qR sR d₁).1 =
      (mxfp4SetupRaw suite li lj lk lb wR pol sD ci lidx sIn sOut qR sR d₂).1 ∧ (mxfp4SetupRaw suite li lj lk lb wR pol sD ci lidx sIn sOut qR sR d₁).2.1 =
      (mxfp4SetupRaw suite li lj lk lb wR pol sD ci lidx sIn sOut qR sR d₂).2.1 := ⟨rfl, rfl⟩
theorem proveMxfp4ChunkIop_wellFormed32 (suite : ZkmlSuiteProfile) (pol suiteD : ByteArray) (hPol : pol.size = 32) (hSuiteD : suiteD.size = 32)
    (idx : UInt64) (w : Mxfp4ChunkWitness) (nonce : UInt64) : (proveMxfp4ChunkIop suite pol suiteD idx w nonce).WellFormed32 :=
  ⟨w.model.root_size, hPol, hSuiteD, (mxfp4ActRoot32 w.xTbl).size_eq, (mxfp4OutRoot32 w.dTbl).size_eq, (mxfp4MantissaRoot32 w.qInts).size_eq, (mxfp4ShiftRoot32 w.sShifts).size_eq⟩
theorem runMxfp4SumcheckPhase_honest (suite : ZkmlSuiteProfile) (pol suiteD : ByteArray) (hPol : pol.size = 32) (hSuiteD : suiteD.size = 32)
    (idx : UInt64) (w : Mxfp4ChunkWitness) (hw : ValidMxfp4ChunkWitness w) (powNonce : UInt64) : let c := proveMxfp4ChunkIop suite pol suiteD idx w powNonce
    let qTbl := w.qInts.map intToGoldilocks; let sTbl := w.sShifts.map shiftToGoldilocks
    ∃ (rI rJ rB rK rJp : List Goldilocks) (finalVal : Goldilocks) (trPostFold : Transcript .instanceBound),
      runMxfp4SumcheckPhase suite c = some (rI, rJ, rB, rK, rJp, finalVal, trPostFold) ∧
      rI.length = w.logI ∧ rJ.length = w.logJ ∧ rB.length = w.logB ∧ rK.length = w.logK ∧ rJp.length = w.logJ ∧
      c.iopProof.dClaim = mleEval w.dTbl (rI ++ rJ) ∧ c.iopProof.xClaim = mleEval w.xTbl (rI ++ rB ++ rK) ∧
      c.iopProof.qClaim = mleEval qTbl (rB ++ rK ++ rJp) ∧ c.iopProof.sClaim = mleEval sTbl (rK ++ rJp) ∧
      c.iopProof.dFoldRoots = buildFoldRoots 0 (w.logI + w.logJ) w.dTbl (rI ++ rJ) ∧
      c.iopProof.xFoldRoots = buildFoldRoots 0 (w.logI + w.logB + w.logK) w.xTbl (rI ++ rB ++ rK) ∧
      c.iopProof.qFoldRoots = buildFoldRoots 0 (w.logB + w.logK + w.logJ) qTbl (rB ++ rK ++ rJp) ∧
      c.iopProof.sFoldRoots = buildFoldRoots 0 (w.logK + w.logJ) sTbl (rK ++ rJp) ∧ c.iopProof.queryOpenings = (squeezeRawQueries suite.numQueries
          (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 powNonce)) trPostFold)).1.map (proveMxfp4QueryOpening w rI rJ rB rK rJp) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _, _, hXLen, hQLen, hSLen, _, _, hDEq⟩ := hw; let c := proveMxfp4ChunkIop suite pol suiteD idx w powNonce
  let setup := mxfp4SetupRaw suite w.logI w.logJ w.logK w.logB w.model.root pol suiteD idx w.layerIdx (mxfp4ActRoot32 w.xTbl).bytes (mxfp4OutRoot32 w.dTbl).bytes
    (mxfp4MantissaRoot32 w.qInts).bytes (mxfp4ShiftRoot32 w.sShifts).bytes c.iopProof.dClaim
  let rI := setup.1; let rJ := setup.2.1; have hRIL : rI.length = w.logI := squeezeGoldilocksVec_length w.logI _
  have hRJL : rJ.length = w.logJ := squeezeGoldilocksVec_length w.logJ _
  have hPts := mxfp4SetupRaw_pts_indep suite w.logI w.logJ w.logK w.logB w.model.root pol suiteD idx w.layerIdx (mxfp4ActRoot32 w.xTbl).bytes (mxfp4OutRoot32 w.dTbl).bytes
    (mxfp4MantissaRoot32 w.qInts).bytes (mxfp4ShiftRoot32 w.sShifts).bytes Goldilocks.zero c.iopProof.dClaim
  have hDClaim : c.iopProof.dClaim = mleEval w.dTbl (rI ++ rJ) := by change mleEval w.dTbl (_ ++ _) = mleEval w.dTbl (rI ++ rJ); rw [hPts.1, hPts.2]
  obtain ⟨hVer, hRBL, hRKL, hRJpL, _⟩ := proveMxfp4Sumcheck_complete w.logI w.logJ w.logK w.logB w.xTbl w.qInts w.sShifts rI rJ setup.2.2 hXLen hQLen hSLen hRIL hRJL
  rw [← hDEq, ← hDClaim] at hVer; let sc := proveMxfp4Sumcheck w.logJ w.logK w.logB w.xTbl (w.qInts.map intToGoldilocks) (w.sShifts.map shiftToGoldilocks) rI rJ setup.2.2
  let rB := sc.2.1; let rK := sc.2.2.1; let rJp := sc.2.2.2.1; let trPS := sc.2.2.2.2
  have hTakeB : (rB ++ rK ++ rJp).take w.logB = rB := by rw [List.append_assoc, List.take_left' hRBL]
  have hTakeK : ((rB ++ rK ++ rJp).drop w.logB).take w.logK = rK := by rw [List.append_assoc, List.drop_left' hRBL, List.take_left' hRKL]
  have hDropBK : (rB ++ rK ++ rJp).drop (w.logB + w.logK) = rJp := List.drop_left' (by rw [List.length_append, hRBL, hRKL])
  let finalVal := CommRingOps.mul (eqPolyVec rJ rJp) (CommRingOps.mul (mleEval w.xTbl (rI ++ rB ++ rK))
      (CommRingOps.mul (mleEval (w.qInts.map intToGoldilocks) (rB ++ rK ++ rJp)) (mleEval (w.sShifts.map shiftToGoldilocks) (rK ++ rJp))))
  let trPF := absorbMsg zkmlFoldRootsLabel (encodePostFoldPayload c.iopProof) trPS
  have hDF : c.iopProof.dFoldRoots = buildFoldRoots 0 (w.logI + w.logJ) w.dTbl (rI ++ rJ) := rfl
  have hXF : c.iopProof.xFoldRoots = buildFoldRoots 0 (w.logI + w.logB + w.logK) w.xTbl (rI ++ rB ++ rK) := rfl
  have hQF : c.iopProof.qFoldRoots = buildFoldRoots 0 (w.logB + w.logK + w.logJ) (w.qInts.map intToGoldilocks) (rB ++ rK ++ rJp) := rfl
  have hSF : c.iopProof.sFoldRoots = buildFoldRoots 0 (w.logK + w.logJ) (w.sShifts.map shiftToGoldilocks) (rK ++ rJp) := rfl
  have hPb : proofBoundsOk c.iopProof = true := by
    have hRBL' : rB.length = w.logB := hRBL; have hRKL' : rK.length = w.logK := hRKL; have hRJpL' : rJp.length = w.logJ := hRJpL
    refine (proofBoundsOk_iff c.iopProof).mpr ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, ?_⟩; rw [hDF, hXF, hQF, hSF]
    exact ⟨buildFoldRoots_length _ 0 _ _ (by simp [hRIL, hRJL]), buildFoldRoots_length _ 0 _ _ (by simp [hRIL, hRBL', hRKL', Nat.add_assoc]),
      buildFoldRoots_length _ 0 _ _ (by simp [hRBL', hRKL', hRJpL', Nat.add_assoc]), buildFoldRoots_length _ 0 _ _ (by simp [hRKL', hRJpL'])⟩
  have hRb : receiptBoundsOk c = true := (receiptBoundsOk_iff c).mpr ⟨proveMxfp4ChunkIop_wellFormed32 suite pol suiteD hPol hSuiteD idx w powNonce, (proofBoundsOk_iff c.iopProof).mp hPb⟩
  refine ⟨rI, rJ, rB, rK, rJp, finalVal, trPF, ?_, hRIL, hRJL, hRBL, hRKL, hRJpL, hDClaim, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold runMxfp4SumcheckPhase; dsimp only; rw [hRb]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hSetupEq : mxfp4SetupRaw suite c.iopProof.logI c.iopProof.logJ c.iopProof.logK c.iopProof.logB
      c.modelWeightsRoot c.policyFloorDigest c.suiteDigest c.chunkIdx c.layerIdx
      c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot c.iopProof.dClaim = setup := rfl
  have hRoundsEq : c.iopProof.sumcheckRounds = sc.1 := rfl
  have hSchedEq : mxfp4DegSchedule c.iopProof.logB c.iopProof.logK c.iopProof.logJ = mxfp4DegSchedule w.logB w.logK w.logJ := rfl
  have hClaims : c.iopProof.xClaim = mleEval w.xTbl (rI ++ rB ++ rK) ∧ c.iopProof.qClaim = mleEval (w.qInts.map intToGoldilocks) (rB ++ rK ++ rJp) ∧
      c.iopProof.sClaim = mleEval (w.sShifts.map shiftToGoldilocks) (rK ++ rJp) ∧ c.iopProof.logB = w.logB ∧ c.iopProof.logK = w.logK := ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [hSetupEq, hRoundsEq, hSchedEq, hVer]; dsimp only
  rw [hClaims.1, hClaims.2.1, hClaims.2.2.1, hClaims.2.2.2.1, hClaims.2.2.2.2, hTakeB, hTakeK, hDropBK, decide_eq_true rfl]; rfl
theorem proveMxfp4ChunkIop_complete {suite : ZkmlSuiteProfile} {policyFloorDigest suiteDigest : ByteArray} {chunkIdx : UInt64}
    {w : Mxfp4ChunkWitness} {powBits : Nat} {powNonce : UInt64} (hw : ValidMxfp4ChunkWitness w)
    (hPol : policyFloorDigest.size = 32) (hSuiteD : suiteDigest.size = 32)
    (hSuite : 1 ≤ suite.numQueries ∧ suite.numQueries ≤ 1024 ∧ 1 ≤ suite.logArity) (hGrindLe : suite.grindBits ≤ powBits)
    (hZeroNonce : powBits = 0 → powNonce = 0) (hPow :
      match runMxfp4SumcheckPhase suite (proveMxfp4ChunkIop suite policyFloorDigest suiteDigest chunkIdx w powNonce) with
      | none => False | some (_, _, _, _, _, _, trPostFold) => checkChunkPow powBits (powCandidateState trPostFold powNonce) = true) :
    verifyMxfp4ChunkIop suite w.model powBits (proveMxfp4ChunkIop suite policyFloorDigest suiteDigest chunkIdx w powNonce) = true := by
  have hwFull := hw; obtain ⟨_, _, _, _, _, _, _, hMValid, hMLayer, hXLen, hQLen, hSLen, hE2m1, hShifts, hDEq⟩ := hw
  let c := proveMxfp4ChunkIop suite policyFloorDigest suiteDigest chunkIdx w powNonce
  obtain ⟨hwR, _, _, _, hlIdx, hSin, hSout, hQr, hSr, hLI, hLJ, hLK, hLB, hPN⟩ := proveMxfp4ChunkIop_headers suite policyFloorDigest suiteDigest chunkIdx w powNonce
  obtain ⟨rI, rJ, rB, rK, rJp, _, trPF, hPhase, hRIL, hRJL, hRBL, hRKL, hRJpL, hDC, hXC, hQC, hSC, hDF, hXF, hQF, hSF, hQO⟩ :=
    runMxfp4SumcheckPhase_honest suite policyFloorDigest suiteDigest hPol hSuiteD chunkIdx w hwFull powNonce
  rw [hPhase] at hPow; dsimp only at hPow; have hDLen : w.dTbl.length = 2 ^ (w.logI + w.logJ) := hDEq ▸ mxfp4ContractTable_length _ _ _ _ _ _ _ hQLen hSLen hXLen
  have hLayerOk : layerMatchesReceipt w.model c = true := by unfold layerMatchesReceipt; rw [hwR, hlIdx, hMLayer, hMValid, hLI, hLJ, hLK, hLB, hQr, hSr]; simp
  have hFoldLens : c.iopProof.dFoldRoots.length = c.iopProof.logI + c.iopProof.logJ ∧ c.iopProof.xFoldRoots.length = c.iopProof.logI + c.iopProof.logB + c.iopProof.logK ∧
      c.iopProof.qFoldRoots.length = c.iopProof.logB + c.iopProof.logK + c.iopProof.logJ ∧ c.iopProof.sFoldRoots.length = c.iopProof.logK + c.iopProof.logJ := by
    rw [hDF, hXF, hQF, hSF, hLI, hLJ, hLK, hLB]
    exact ⟨buildFoldRoots_length _ 0 _ _ (by simp [hRIL, hRJL]), buildFoldRoots_length _ 0 _ _ (by simp [hRIL, hRBL, hRKL, Nat.add_assoc]),
           buildFoldRoots_length _ 0 _ _ (by simp [hRBL, hRKL, hRJpL, Nat.add_assoc]), buildFoldRoots_length _ 0 _ _ (by simp [hRKL, hRJpL])⟩
  have hQListOk : ∀ (qs : List Nat), verifyMxfp4QueryList c rI rJ rB rK rJp qs (qs.map (proveMxfp4QueryOpening w rI rJ rB rK rJp)) = true := by
    intro qs; induction qs with
    | nil => rfl
    | cons qRaw rest ih =>
      simp only [List.map_cons, verifyMxfp4QueryList, ih, Bool.and_true]; let vD := w.logI + w.logJ; let vX := w.logI + w.logB + w.logK
      let vQ := w.logB + w.logK + w.logJ; let vS := w.logK + w.logJ; have hiD : qRaw % 2 ^ vD < 2 ^ vD := Nat.mod_lt _ (Nat.two_pow_pos vD)
      have hiX : qRaw % 2 ^ vX < 2 ^ vX := Nat.mod_lt _ (Nat.two_pow_pos vX); have hiQ : qRaw % 2 ^ vQ < 2 ^ vQ := Nat.mod_lt _ (Nat.two_pow_pos vQ)
      have hiS : qRaw % 2 ^ vS < 2 ^ vS := Nat.mod_lt _ (Nat.two_pow_pos vS)
      have hdGet : w.dTbl.getD (qRaw % 2 ^ vD) Goldilocks.zero = w.dTbl[qRaw % 2 ^ vD]'(hDLen ▸ hiD) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hDLen ▸ hiD), Option.getD_some]
      have hxGet : w.xTbl.getD (qRaw % 2 ^ vX) Goldilocks.zero = w.xTbl[qRaw % 2 ^ vX]'(hXLen ▸ hiX) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hXLen ▸ hiX), Option.getD_some]
      have hqGet : w.qInts.getD (qRaw % 2 ^ vQ) 0 = w.qInts[qRaw % 2 ^ vQ]'(hQLen ▸ hiQ) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hQLen ▸ hiQ), Option.getD_some]
      have hsGet : w.sShifts.getD (qRaw % 2 ^ vS) 0 = w.sShifts[qRaw % 2 ^ vS]'(hSLen ▸ hiS) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hSLen ▸ hiS), Option.getD_some]
      have hClD := climbZkml32_path_len (w.dTbl.mapIdx fun i d => hashTensorLeaf i d) (by simp [hDLen, vD]) (qRaw % 2 ^ vD) hiD
      have hClX := climbZkml32_path_len (w.xTbl.mapIdx fun i x => hashTensorLeaf i x) (by simp [hXLen, vX]) (qRaw % 2 ^ vX) hiX
      have hClQ := climbZkml32_path_len (w.qInts.mapIdx fun i q => hashMantissaLeaf i q) (by simp [hQLen, vQ]) (qRaw % 2 ^ vQ) hiQ
      have hClS := climbZkml32_path_len (w.sShifts.mapIdx fun i sh => hashShiftLeaf i sh) (by simp [hSLen, vS]) (qRaw % 2 ^ vS) hiS
      simp only [List.getElem_mapIdx] at hClD hClX hClQ hClS
      have hFwD := verifyFoldWalk_complete vD 0 (qRaw % 2 ^ vD) w.dTbl (rI ++ rJ) hDLen hiD (by simp [hRIL, hRJL, vD])
      have hFwX := verifyFoldWalk_complete vX 0 (qRaw % 2 ^ vX) w.xTbl (rI ++ rB ++ rK) hXLen hiX (by simp [hRIL, hRBL, hRKL, vX, Nat.add_assoc])
      have hFwQ := verifyFoldWalk_complete vQ 0 (qRaw % 2 ^ vQ) (w.qInts.map intToGoldilocks) (rB ++ rK ++ rJp)
        (by simp [hQLen, vQ]) hiQ (by simp [hRBL, hRKL, hRJpL, vQ, Nat.add_assoc])
      have hFwS := verifyFoldWalk_complete vS 0 (qRaw % 2 ^ vS) (w.sShifts.map shiftToGoldilocks) (rK ++ rJp) (by simp [hSLen, vS]) hiS (by simp [hRKL, hRJpL, vS])
      simp only [List.getElem_map] at hFwQ hFwS; unfold verifyMxfp4QueryOpening verifyMxfp4QueryLocal; dsimp only
      rw [hLI, hLJ, hLK, hLB, hSout, hSin, hQr, hSr, hDC, hXC, hQC, hSC, hDF, hXF, hQF, hSF]; dsimp only [proveMxfp4QueryOpening]
      rw [hdGet, hxGet, hqGet, hsGet, hE2m1 _ (List.getElem_mem _), hShifts _ (List.getElem_mem _), mxfp4OutRoot32, mxfp4ActRoot32, mxfp4MantissaRoot32, mxfp4ShiftRoot32,
          hClD, hClX, hClQ, hClS, hFwD, hFwX, hFwQ, hFwS]
      rfl
  unfold verifyMxfp4ChunkIop; dsimp only; have hFoldLensDec : foldRootsMatchDims c.iopProof = true := (foldRootsMatchDims_iff c.iopProof).mpr hFoldLens
  have hWfDec : decide c.WellFormed32 = true := decide_eq_true (proveMxfp4ChunkIop_wellFormed32 suite policyFloorDigest suiteDigest hPol hSuiteD chunkIdx w powNonce)
  change (decide c.WellFormed32 && decide _ && layerMatchesReceipt w.model c && foldRootsMatchDims c.iopProof && match runMxfp4SumcheckPhase suite c with
    | none => false | some (rI, rJ, rB, rK, rJp, _, trPostFold) =>
      decide (suite.grindBits ≤ powBits) && decide (powBits = 0 → c.iopProof.powNonce = 0) &&
      checkChunkPow powBits (powCandidateState trPostFold c.iopProof.powNonce) &&
      verifyMxfp4QueryList c rI rJ rB rK rJp (squeezeRawQueries suite.numQueries
          (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 c.iopProof.powNonce)) trPostFold)).1 c.iopProof.queryOpenings) = true
  have hZN' : decide (powBits = 0 → c.iopProof.powNonce = 0) = true := decide_eq_true (fun hz => hPN.trans (hZeroNonce hz))
  rw [hWfDec, decide_eq_true hSuite, hLayerOk, hFoldLensDec, hPhase]; dsimp only
  rw [decide_eq_true hGrindLe, hZN', hPN, hPow, hQO, hQListOk]; rfl
@[expose] def WitnessMatchesMxfp4Chunk (w : Mxfp4ChunkWitness) (c : ZkmlChunkReceipt) : Prop :=
  w.logI = c.iopProof.logI ∧ w.logJ = c.iopProof.logJ ∧ w.logK = c.iopProof.logK ∧ w.logB = c.iopProof.logB ∧
  w.xTbl.length = 2 ^ (w.logI + w.logB + w.logK) ∧ w.qInts.length = 2 ^ (w.logB + w.logK + w.logJ) ∧
  w.sShifts.length = 2 ^ (w.logK + w.logJ) ∧ w.dTbl.length = 2 ^ (w.logI + w.logJ) ∧ w.model.root = c.modelWeightsRoot ∧
  (mxfp4ActRoot32 w.xTbl).bytes = c.stateInCommit ∧ (mxfp4OutRoot32 w.dTbl).bytes = c.stateOutCommit ∧
  (mxfp4MantissaRoot32 w.qInts).bytes = c.qMerkleRoot ∧ (mxfp4ShiftRoot32 w.sShifts).bytes = c.sMerkleRoot
def OuterMleRootHit (w : Mxfp4ChunkWitness) (rI rJ : List Goldilocks) : Prop :=
  let dTrue := mxfp4ContractTable w.logI w.logJ w.logK w.logB w.xTbl w.qInts w.sShifts; w.dTbl ≠ dTrue ∧ mleEval w.dTbl (rI ++ rJ) = mleEval dTrue (rI ++ rJ)
def FinalOracleMismatch (w : Mxfp4ChunkWitness) (c : ZkmlChunkReceipt) (rI rJ rB rK rJp : List Goldilocks) : Prop :=
  c.iopProof.dClaim ≠ mleEval w.dTbl (rI ++ rJ) ∨ c.iopProof.xClaim ≠ mleEval w.xTbl (rI ++ rB ++ rK) ∨
  c.iopProof.qClaim ≠ mleEval (w.qInts.map intToGoldilocks) (rB ++ rK ++ rJp) ∨ c.iopProof.sClaim ≠ mleEval (w.sShifts.map shiftToGoldilocks) (rK ++ rJp)
def QueryFoldDeviationAt (w : Mxfp4ChunkWitness) (c : ZkmlChunkReceipt) (rI rJ rB rK rJp : List Goldilocks) (qRaw : Nat) (op : Mxfp4QueryOpening) : Prop :=
  let vD := w.logI + w.logJ; let vX := w.logI + w.logB + w.logK; let vQ := w.logB + w.logK + w.logJ; let vS := w.logK + w.logJ
  (∃ hd : qRaw % 2 ^ vD < w.dTbl.length, op.dVal = w.dTbl[qRaw % 2 ^ vD]) ∧ (∃ hx : qRaw % 2 ^ vX < w.xTbl.length, op.xVal = w.xTbl[qRaw % 2 ^ vX]) ∧
  (∃ hq : qRaw % 2 ^ vQ < w.qInts.length, op.qMantissa = w.qInts[qRaw % 2 ^ vQ]) ∧ (∃ hs : qRaw % 2 ^ vS < w.sShifts.length, op.sShift = w.sShifts[qRaw % 2 ^ vS]) ∧
  ((c.iopProof.dClaim ≠ mleEval w.dTbl (rI ++ rJ) ∧ FoldPairDiscrepancy 0 vD (qRaw % 2 ^ vD) w.dTbl (rI ++ rJ) c.iopProof.dFoldRoots op.dFoldSteps) ∨
   (c.iopProof.xClaim ≠ mleEval w.xTbl (rI ++ rB ++ rK) ∧ FoldPairDiscrepancy 0 vX (qRaw % 2 ^ vX) w.xTbl (rI ++ rB ++ rK) c.iopProof.xFoldRoots op.xFoldSteps) ∨
   (c.iopProof.qClaim ≠ mleEval (w.qInts.map intToGoldilocks) (rB ++ rK ++ rJp) ∧ FoldPairDiscrepancy 0 vQ (qRaw % 2 ^ vQ) (w.qInts.map intToGoldilocks) (rB ++ rK ++ rJp) c.iopProof.qFoldRoots op.qFoldSteps) ∨
   (c.iopProof.sClaim ≠ mleEval (w.sShifts.map shiftToGoldilocks) (rK ++ rJp) ∧ FoldPairDiscrepancy 0 vS (qRaw % 2 ^ vS) (w.sShifts.map shiftToGoldilocks) (rK ++ rJp) c.iopProof.sFoldRoots op.sFoldSteps))
def AuthenticatedFoldWalkDeviation (w : Mxfp4ChunkWitness) (c : ZkmlChunkReceipt) (rI rJ rB rK rJp : List Goldilocks) (rawQueries : List Nat) : Prop :=
  rawQueries ≠ [] ∧ FinalOracleMismatch w c rI rJ rB rK rJp ∧ ZipAll (QueryFoldDeviationAt w c rI rJ rB rK rJp) rawQueries c.iopProof.queryOpenings
def invalidQIndices (w : Mxfp4ChunkWitness) : List Nat := (List.range w.qInts.length).filter fun i => if h : i < w.qInts.length then !isValidE2m1Mantissa w.qInts[i] else true
def invalidSIndices (w : Mxfp4ChunkWitness) : List Nat := (List.range w.sShifts.length).filter fun i => if h : i < w.sShifts.length then !isValidMxfp4Shift w.sShifts[i] else true
def MissedInvalidWeightLeaf (w : Mxfp4ChunkWitness) (rawQueries : List Nat) : Prop :=
  (invalidQIndices w ≠ [] ∨ invalidSIndices w ≠ []) ∧ (∀ qRaw ∈ rawQueries, qRaw % w.qInts.length ∉ invalidQIndices w ∧ qRaw % w.sShifts.length ∉ invalidSIndices w)
def mxfp4MerkleMaxBytes (w : Mxfp4ChunkWitness) (c : ZkmlChunkReceipt) : Nat :=
  let vMax := Nat.max (Nat.max (w.logI + w.logJ) (w.logI + w.logB + w.logK)) (w.logB + w.logK + w.logJ)
  65 + vMax + 2 + Nat.max 8 (maxByteLen ((c.iopProof.queryOpenings.map fun o => encodeSignedInt o.qMantissa) ++ (w.qInts.map encodeSignedInt) ++
     (c.iopProof.queryOpenings.map fun o => leb128 o.sShift) ++ (w.sShifts.map leb128)))
def ZkmlCshakeCollision (M : Mxfp4ModelManifest) (w : Mxfp4ChunkWitness) (c : ZkmlChunkReceipt) : Prop :=
  CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_WEIGHTS/v1".toUTF8.data.toList) (fun x => x = M.preimage ∨ x = w.model.preimage) ∨
  BoundedCollision (cshake256Bytes zkmlMerkleCust) (mxfp4MerkleMaxBytes w c)
private theorem runMxfp4SumcheckPhase_lens {suite : ZkmlSuiteProfile} {c : ZkmlChunkReceipt}
    {rI rJ rB rK rJp : List Goldilocks} {fv : Goldilocks} {trPF : Transcript .instanceBound} (h : runMxfp4SumcheckPhase suite c = some (rI, rJ, rB, rK, rJp, fv, trPF)) :
    rI.length = c.iopProof.logI ∧ rJ.length = c.iopProof.logJ ∧ rB.length = c.iopProof.logB ∧ rK.length = c.iopProof.logK ∧ rJp.length = c.iopProof.logJ := by
  unfold runMxfp4SumcheckPhase at h; dsimp only at h; let p := c.iopProof
  cases hRb : receiptBoundsOk c
  · simp [hRb] at h
  · simp only [hRb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    let setup := mxfp4SetupRaw suite p.logI p.logJ p.logK p.logB c.modelWeightsRoot c.policyFloorDigest
      c.suiteDigest c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot p.dClaim
    cases hVer : verifyScheduledSumcheck (mxfp4DegSchedule p.logB p.logK p.logJ) p.dClaim p.sumcheckRounds setup.2.2 with
    | none => simp [p, setup, hVer] at h
    | some sc =>
      rcases sc with ⟨⟨allChals, fv'⟩, trPS⟩; simp only [p, setup, hVer] at h; split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, _, _⟩
        obtain ⟨hAll, _⟩ := verifyScheduledSumcheck_point_len _ _ _ _ _ _ _ hVer; rw [(mxfp4DegSchedule_never_deg_four _ _ _).1] at hAll
        exact ⟨squeezeGoldilocksVec_length _ _, squeezeGoldilocksVec_length _ _,
          by dsimp [p] at hAll ⊢; rw [List.length_take, hAll]; omega,
          by dsimp [p] at hAll ⊢; rw [List.length_take, List.length_drop, hAll]; omega,
          by dsimp [p] at hAll ⊢; rw [List.length_drop, hAll]; omega⟩
      · cases h
private theorem verifyMxfp4ChunkIop_unpack {suite : ZkmlSuiteProfile} {M : Mxfp4ModelManifest} {powBits : Nat} {c : ZkmlChunkReceipt}
    (hAcc : verifyMxfp4ChunkIop suite M powBits c = true) : 1 ≤ suite.numQueries ∧ M.root = c.modelWeightsRoot ∧ ChunkMeetsPow suite powBits c ∧
    ∃ (rI rJ rB rK rJp : List Goldilocks) (finalVal : Goldilocks) (trPostFold : Transcript .instanceBound),
      runMxfp4SumcheckPhase suite c = some (rI, rJ, rB, rK, rJp, finalVal, trPostFold) ∧ ZipAll (QueryOpeningSpec c rI rJ rB rK rJp) (squeezeRawQueries suite.numQueries
          (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 c.iopProof.powNonce)) trPostFold)).1 c.iopProof.queryOpenings := by
  obtain ⟨hWf, hS, hL, hFL, allChals, fv, trPS, hSched, hFv, hGr, hZN, hP64, hMod, hQL⟩ := (verifyMxfp4ChunkIop_iff_spec suite M powBits c).mp hAcc; let p := c.iopProof
  have hPb := layerAndFold_implies_proofBounds hL hFL
  have hRb : receiptBoundsOk c = true := by simp [receiptBoundsOk, decide_eq_true hWf, hPb]
  let setup := mxfp4SetupRaw suite p.logI p.logJ p.logK p.logB c.modelWeightsRoot c.policyFloorDigest
    c.suiteDigest c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot p.dClaim
  let rB := allChals.take p.logB; let rK := (allChals.drop p.logB).take p.logK; let rJp := allChals.drop (p.logB + p.logK)
  let trPF := absorbMsg zkmlFoldRootsLabel (encodePostFoldPayload p) trPS
  have hPh : runMxfp4SumcheckPhase suite c = some (setup.1, setup.2.1, rB, rK, rJp, fv, trPF) := by
    unfold runMxfp4SumcheckPhase; dsimp only; rw [hRb]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hVer := (verifyScheduledSumcheck_iff_spec (mxfp4DegSchedule p.logB p.logK p.logJ) p.dClaim fv p.sumcheckRounds allChals setup.2.2 trPS).mpr hSched
    dsimp only [p, setup] at hVer; rw [hVer]; dsimp only; have hFv' := hFv; rw [decide_eq_true hFv']; rfl
  exact ⟨hS.1, hL.2.2.2.1, ⟨hGr, hZN, (receiptBoundsOk_iff c).mp hRb, setup.1, setup.2.1, allChals, fv, trPS, rfl, rfl, hSched, hFv, hP64, hMod⟩,
    setup.1, setup.2.1, rB, rK, rJp, fv, trPF, hPh, hQL⟩
private theorem verifyMxfp4ChunkIop_sound_of_unpack {suite : ZkmlSuiteProfile} {M : Mxfp4ModelManifest} {powBits : Nat} {w : Mxfp4ChunkWitness} {c : ZkmlChunkReceipt}
    (hUnpack : 1 ≤ suite.numQueries ∧ M.root = c.modelWeightsRoot ∧ ChunkMeetsPow suite powBits c ∧
      ∃ (rI rJ rB rK rJp : List Goldilocks) (finalVal : Goldilocks) (trPostFold : Transcript .instanceBound),
        runMxfp4SumcheckPhase suite c = some (rI, rJ, rB, rK, rJp, finalVal, trPostFold) ∧ ZipAll (QueryOpeningSpec c rI rJ rB rK rJp) (squeezeRawQueries suite.numQueries
            (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 c.iopProof.powNonce)) trPostFold)).1 c.iopProof.queryOpenings)
    (hMatch : WitnessMatchesMxfp4Chunk w c) : ChunkMeetsPow suite powBits c ∧
    ∃ (rI rJ rB rK rJp : List Goldilocks) (finalVal : Goldilocks) (trPostFold : Transcript .instanceBound),
      runMxfp4SumcheckPhase suite c = some (rI, rJ, rB, rK, rJp, finalVal, trPostFold) ∧
      (let setup := mxfp4SetupRaw suite c.iopProof.logI c.iopProof.logJ c.iopProof.logK c.iopProof.logB c.modelWeightsRoot c.policyFloorDigest c.suiteDigest
         c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot c.iopProof.dClaim
       let rawQs := (squeezeRawQueries suite.numQueries (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 c.iopProof.powNonce)) trPostFold)).1
       (M = w.model ∧ (∀ q ∈ w.qInts, isValidE2m1Mantissa q = true) ∧ (∀ sh ∈ w.sShifts, isValidMxfp4Shift sh = true) ∧
         w.dTbl = mxfp4ContractTable w.logI w.logJ w.logK w.logB w.xTbl w.qInts w.sShifts) ∨ OuterMleRootHit w rI rJ ∨
       Mxfp4SumcheckRootHit w.logJ w.logK w.logB w.xTbl (w.qInts.map intToGoldilocks) (w.sShifts.map shiftToGoldilocks) rI rJ rB rK c.iopProof.sumcheckRounds setup.2.2 ∨
       AuthenticatedFoldWalkDeviation w c rI rJ rB rK rJp rawQs ∨ MissedInvalidWeightLeaf w rawQs ∨ ZkmlCshakeCollision M w c) := by
  obtain ⟨hLI, hLJ, hLK, hLB, hXLen, hQLen, hSLen, hDLen, hWRoot, hSinRoot, hSoutRoot, hQRoot, hSRoot⟩ := hMatch
  obtain ⟨hQGe1, hMRoot, hPowSpec, rI, rJ, rB, rK, rJp, finalVal, trPostFold, hPhase, hQListOk⟩ := hUnpack
  refine ⟨hPowSpec, rI, rJ, rB, rK, rJp, finalVal, trPostFold, hPhase, ?_⟩
  cases extractMxfp4ModelBinding M w.model (hMRoot.trans hWRoot.symm) with
  | inr hColM => exact .inr (.inr (.inr (.inr (.inr (.inl hColM.down)))))
  | inl hMEqL =>
      have hMEq : M = w.model := hMEqL.down
      let cap := Nat.max 8 (maxByteLen ((c.iopProof.queryOpenings.map fun o => encodeSignedInt o.qMantissa) ++ (w.qInts.map encodeSignedInt) ++
         (c.iopProof.queryOpenings.map fun o => leb128 o.sShift) ++ (w.sShifts.map leb128)))
      have hCap8 : 8 ≤ cap := Nat.le_max_left _ _; have hCapM : maxByteLen _ ≤ cap := Nat.le_max_right _ _
      if hDomValid : (invalidQIndices w).isEmpty && (invalidSIndices w).isEmpty then
        simp only [Bool.and_eq_true, List.isEmpty_iff, invalidQIndices, invalidSIndices, List.filter_eq_nil_iff, List.mem_range] at hDomValid
        have hQAll : ∀ q ∈ w.qInts, isValidE2m1Mantissa q = true := by
          intro q hq; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq; have hc := hDomValid.1 i hi; simp only [hi, ↓reduceDIte, Bool.not_eq_true'] at hc
          cases hb : isValidE2m1Mantissa w.qInts[i] with | false => simp [hb] at hc | true => rfl
        have hSAll : ∀ sh ∈ w.sShifts, isValidMxfp4Shift sh = true := by
          intro sh hsh; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hsh; have hc := hDomValid.2 i hi; simp only [hi, ↓reduceDIte, Bool.not_eq_true'] at hc
          cases hb : isValidMxfp4Shift w.sShifts[i] with | false => simp [hb] at hc | true => rfl
        let dTrue := mxfp4ContractTable w.logI w.logJ w.logK w.logB w.xTbl w.qInts w.sShifts
        if hDEq : w.dTbl = dTrue then exact .inl ⟨hMEq, hQAll, hSAll, hDEq⟩
        else if hOuterHit : mleEval w.dTbl (rI ++ rJ) = mleEval dTrue (rI ++ rJ) then exact .inr (.inl ⟨hDEq, hOuterHit⟩)
        else if hOracleMis : c.iopProof.dClaim ≠ mleEval w.dTbl (rI ++ rJ) ∨ c.iopProof.xClaim ≠ mleEval w.xTbl (rI ++ rB ++ rK) ∨
            c.iopProof.qClaim ≠ mleEval (w.qInts.map intToGoldilocks) (rB ++ rK ++ rJp) ∨ c.iopProof.sClaim ≠ mleEval (w.sShifts.map shiftToGoldilocks) (rK ++ rJp) then
          obtain ⟨hRILc, hRJLc, hRBLc, hRKLc, hRJpLc⟩ := runMxfp4SumcheckPhase_lens hPhase; have hRIL : rI.length = w.logI := hRILc.trans hLI.symm
          have hRJL : rJ.length = w.logJ := hRJLc.trans hLJ.symm; have hRBL : rB.length = w.logB := hRBLc.trans hLB.symm
          have hRKL : rK.length = w.logK := hRKLc.trans hLK.symm; have hRJpL : rJp.length = w.logJ := hRJpLc.trans hLJ.symm
          let rawQs := (squeezeRawQueries suite.numQueries (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 c.iopProof.powNonce)) trPostFold)).1
          have hRawNe : rawQs ≠ [] := List.ne_nil_of_length_pos (by rw [squeezeRawQueries_length]; omega)
          have hAllDev : ∀ (qs : List Nat) (ops : List Mxfp4QueryOpening), (∀ op ∈ ops, op ∈ c.iopProof.queryOpenings) →
              ZipAll (QueryOpeningSpec c rI rJ rB rK rJp) qs ops → ZipAll (QueryFoldDeviationAt w c rI rJ rB rK rJp) qs ops ∨ ZkmlCshakeCollision M w c := by
            intro qs ops hSub hZip; induction hZip with
            | nil => exact .inl .nil
            | @cons qRaw op rest ops hOp _ ih =>
                obtain ⟨_, _, hClDSpec, hClXSpec, hClQSpec, hClSSpec, hFwDSpec, hFwXSpec, hFwQSpec, hFwSSpec⟩ := hOp; have hClD := (climbZkml32_iff ..).mpr hClDSpec
                have hClX := (climbZkml32_iff ..).mpr hClXSpec; have hClQ := (climbZkml32_iff ..).mpr hClQSpec; have hClS := (climbZkml32_iff ..).mpr hClSSpec
                have hFwD := (verifyFoldWalk_iff_spec ..).mpr hFwDSpec; have hFwX := (verifyFoldWalk_iff_spec ..).mpr hFwXSpec
                have hFwQ := (verifyFoldWalk_iff_spec ..).mpr hFwQSpec; have hFwS := (verifyFoldWalk_iff_spec ..).mpr hFwSSpec; have hOpMem := hSub op (.head _)
                let vD := w.logI + w.logJ; let vX := w.logI + w.logB + w.logK; let vQ := w.logB + w.logK + w.logJ; let vS := w.logK + w.logJ
                have hiD : qRaw % 2 ^ vD < 2 ^ vD := Nat.mod_lt _ (Nat.two_pow_pos vD); have hiX : qRaw % 2 ^ vX < 2 ^ vX := Nat.mod_lt _ (Nat.two_pow_pos vX)
                have hiQ : qRaw % 2 ^ vQ < 2 ^ vQ := Nat.mod_lt _ (Nat.two_pow_pos vQ); have hiS : qRaw % 2 ^ vS < 2 ^ vS := Nat.mod_lt _ (Nat.two_pow_pos vS)
                have hVD : c.iopProof.logI + c.iopProof.logJ = vD := by simp [vD, hLI, hLJ]
                have hVX : c.iopProof.logI + c.iopProof.logB + c.iopProof.logK = vX := by simp [vX, hLI, hLB, hLK]
                have hVQ : c.iopProof.logB + c.iopProof.logK + c.iopProof.logJ = vQ := by simp [vQ, hLB, hLK, hLJ]
                have hVS : c.iopProof.logK + c.iopProof.logJ = vS := by simp [vS, hLK, hLJ]
                rw [hVD] at hClD hFwD; rw [hVX] at hClX hFwX; rw [hVQ] at hClQ hFwQ; rw [hVS] at hClS hFwS
                rw [hashTensorLeaf_eq] at hClD hClX; rw [hashMantissaLeaf_eq] at hClQ; rw [hashShiftLeaf_eq] at hClS
                have hSoutR : (merkleRoot32 zkmlMerkleHash32 (w.dTbl.mapIdx fun i d => zkmlLeaf32 0x03 i (glToBe8 d))).bytes = c.stateOutCommit := by simpa only [mxfp4OutRoot32, hashTensorLeaf_eq] using hSoutRoot
                have hSinR : (merkleRoot32 zkmlMerkleHash32 (w.xTbl.mapIdx fun i x => zkmlLeaf32 0x03 i (glToBe8 x))).bytes = c.stateInCommit := by simpa only [mxfp4ActRoot32, hashTensorLeaf_eq] using hSinRoot
                have hQR : (merkleRoot32 zkmlMerkleHash32 (w.qInts.mapIdx fun i q => zkmlLeaf32 0x06 i (encodeSignedInt q))).bytes = c.qMerkleRoot := by simpa only [mxfp4MantissaRoot32, hashMantissaLeaf_eq] using hQRoot
                have hSR : (merkleRoot32 zkmlMerkleHash32 (w.sShifts.mapIdx fun i s => zkmlLeaf32 0x07 i (leb128 s))).bytes = c.sMerkleRoot := by simpa only [mxfp4ShiftRoot32, hashShiftLeaf_eq] using hSRoot
                have hGlCap : ∀ (x : Goldilocks), (glToBe8 x).length ≤ cap := fun x => by rw [glToBe8_length]; exact hCap8
                have hOpQCap : (encodeSignedInt op.qMantissa).length ≤ cap := Nat.le_trans (len_le_maxByteLen (by simp only [List.mem_append]; exact .inl (.inl (.inl (List.mem_map_of_mem hOpMem))))) hCapM
                have hWQCap : (encodeSignedInt (w.qInts[qRaw % 2 ^ vQ]'(hQLen.symm ▸ hiQ))).length ≤ cap := Nat.le_trans (len_le_maxByteLen (by simp only [List.mem_append]; exact .inl (.inl (.inr (List.mem_map_of_mem (List.getElem_mem _)))))) hCapM
                have hOpSCap : (leb128 op.sShift).length ≤ cap := Nat.le_trans (len_le_maxByteLen (by simp only [List.mem_append]; exact .inl (.inr (List.mem_map_of_mem hOpMem)))) hCapM
                have hWSCap : (leb128 (w.sShifts[qRaw % 2 ^ vS]'(hSLen.symm ▸ hiS))).length ≤ cap := Nat.le_trans (len_le_maxByteLen (by simp only [List.mem_append]; exact .inr (List.mem_map_of_mem (List.getElem_mem _)))) hCapM
                have liftCol : ∀ {v : Nat}, v ≤ Nat.max (Nat.max vD vX) vQ →
                    HashCollisionWitness (cshake256Bytes zkmlMerkleCust) (65 + v + 2 + cap) → ZkmlCshakeCollision M w c := fun hv wc => .inr ⟨wc.msgA, wc.msgB,
                    Nat.le_trans wc.lenA (by dsimp only [mxfp4MerkleMaxBytes, vD, vX, vQ, cap] at hv ⊢; omega),
                    Nat.le_trans wc.lenB (by dsimp only [mxfp4MerkleMaxBytes, vD, vX, vQ, cap] at hv ⊢; omega), wc.distinct, wc.sameDigest⟩
                cases extractZkmlMerkleAt 0x03 glToBe8 glToBe8_injective vD (qRaw % 2 ^ vD) cap w.dTbl hDLen hiD
                    op.dVal op.dPath c.stateOutCommit (hGlCap _) (hGlCap _) hSoutR hClD (zkmlMerkleHonest_climb 0x03 glToBe8 vD _ w.dTbl hDLen hiD) with
                | inr wc => exact .inr (liftCol (Nat.le_trans (Nat.le_max_left vD vX) (Nat.le_max_left _ vQ)) wc) | inl hDEl =>
                cases extractZkmlMerkleAt 0x03 glToBe8 glToBe8_injective vX (qRaw % 2 ^ vX) cap w.xTbl hXLen hiX
                    op.xVal op.xPath c.stateInCommit (hGlCap _) (hGlCap _) hSinR hClX (zkmlMerkleHonest_climb 0x03 glToBe8 vX _ w.xTbl hXLen hiX) with
                | inr wc => exact .inr (liftCol (Nat.le_trans (Nat.le_max_right vD vX) (Nat.le_max_left _ vQ)) wc) | inl hXEl =>
                cases extractZkmlMerkleAt 0x06 encodeSignedInt encodeSignedInt_injective vQ (qRaw % 2 ^ vQ) cap w.qInts hQLen hiQ
                    op.qMantissa op.qPath c.qMerkleRoot hOpQCap hWQCap hQR hClQ (zkmlMerkleHonest_climb 0x06 encodeSignedInt vQ _ w.qInts hQLen hiQ) with
                | inr wc => exact .inr (liftCol (Nat.le_max_right _ vQ) wc) | inl hQEl =>
                cases extractZkmlMerkleAt 0x07 leb128 leb128_inj vS (qRaw % 2 ^ vS) cap w.sShifts hSLen hiS op.sShift op.sPath c.sMerkleRoot hOpSCap hWSCap hSR hClS
                    (zkmlMerkleHonest_climb 0x07 leb128 vS _ w.sShifts hSLen hiS) with
                | inr wc => exact .inr (liftCol (Nat.le_trans (by dsimp only [vS, vQ]; omega) (Nat.le_max_right _ vQ)) wc)
                | inl hSEl =>
                rcases ih (fun o ho => hSub o (.tail _ ho)) with hTail | hCol
                · refine .inl (.cons ⟨⟨hDLen.symm ▸ hiD, hDEl.down⟩, ⟨hXLen.symm ▸ hiX, hXEl.down⟩, ⟨hQLen.symm ▸ hiQ, hQEl.down⟩, ⟨hSLen.symm ▸ hiS, hSEl.down⟩, ?_⟩ hTail)
                  rcases hOracleMis with hDM | hXM | hQM | hSM
                  · exact .inl ⟨hDM, verifyFoldWalk_deviates_pair vD 0 _ _ _ w.dTbl (rI ++ rJ) _ _ hDLen hiD (by simp [hRIL, hRJL, vD]) hDEl.down hDM hFwD⟩
                  · exact .inr (.inl ⟨hXM, verifyFoldWalk_deviates_pair vX 0 _ _ _ w.xTbl (rI ++ rB ++ rK) _ _ hXLen hiX (by simp [hRIL, hRBL, hRKL, vX, Nat.add_assoc]) hXEl.down hXM hFwX⟩)
                  · exact .inr (.inr (.inl ⟨hQM, verifyFoldWalk_deviates_pair vQ 0 _ _ _ (w.qInts.map intToGoldilocks) (rB ++ rK ++ rJp) _ _ (by simp [hQLen, vQ]) hiQ (by simp [hRBL, hRKL, hRJpL, vQ, Nat.add_assoc]) (by rw [List.getElem_map, hQEl.down]) hQM hFwQ⟩))
                  · exact .inr (.inr (.inr ⟨hSM, verifyFoldWalk_deviates_pair vS 0 _ _ _ (w.sShifts.map shiftToGoldilocks) (rK ++ rJp) _ _ (by simp [hSLen, vS]) hiS (by simp [hRKL, hRJpL, vS]) (by rw [List.getElem_map, hSEl.down]) hSM hFwS⟩))
                · exact .inr hCol
          exact (hAllDev rawQs c.iopProof.queryOpenings (fun _ h => h) hQListOk).elim (fun hDev => .inr (.inr (.inr (.inl ⟨hRawNe, hOracleMis, hDev⟩)))) (fun hCol => .inr (.inr (.inr (.inr (.inr hCol)))))
        else
          simp only [not_or, Decidable.not_not] at hOracleMis; obtain ⟨hDOk, hXOk, hQOk, hSOk⟩ := hOracleMis
          have hSumFalse : c.iopProof.dClaim ≠ mleEval dTrue (rI ++ rJ) := hDOk ▸ hOuterHit; unfold runMxfp4SumcheckPhase at hPhase; dsimp only at hPhase
          cases hRb : receiptBoundsOk c; · simp [hRb] at hPhase
          simp only [hRb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPhase
          let setup := mxfp4SetupRaw suite c.iopProof.logI c.iopProof.logJ c.iopProof.logK c.iopProof.logB
            c.modelWeightsRoot c.policyFloorDigest c.suiteDigest c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot c.iopProof.dClaim
          cases hVerAll : verifyScheduledSumcheck (mxfp4DegSchedule c.iopProof.logB c.iopProof.logK c.iopProof.logJ)
              c.iopProof.dClaim c.iopProof.sumcheckRounds setup.2.2 with
          | none => dsimp only [setup] at hVerAll; rw [hVerAll] at hPhase; cases hPhase
          | some scOut =>
            rcases scOut with ⟨⟨allChals, fv⟩, trPostSum⟩; have hVerAll' := hVerAll; dsimp only [setup] at hVerAll'; rw [hVerAll'] at hPhase; dsimp only at hPhase
            cases hFinChk : decide (fv = CommRingOps.mul (eqPolyVec setup.2.1 (allChals.drop (c.iopProof.logB + c.iopProof.logK)))
                (CommRingOps.mul c.iopProof.xClaim (CommRingOps.mul c.iopProof.qClaim c.iopProof.sClaim)))
            · dsimp only [setup] at hFinChk; rw [hFinChk] at hPhase; cases hPhase
            · have hFinChk' := hFinChk; dsimp only [setup] at hFinChk'; rw [hFinChk'] at hPhase; simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hPhase
              rcases hPhase with ⟨hrI, hrJ, hrB, hrK, hrJp, hfv, _⟩; subst hfv
              have hFinValEq : fv = CommRingOps.mul (eqPolyVec rJ (allChals.drop (w.logB + w.logK)))
                  (CommRingOps.mul (mleEval w.xTbl (rI ++ allChals.take w.logB ++ (allChals.drop w.logB).take w.logK))
                    (CommRingOps.mul (mleEval (w.qInts.map intToGoldilocks) (allChals.take w.logB ++ (allChals.drop w.logB).take w.logK ++ allChals.drop (w.logB + w.logK)))
                      (mleEval (w.sShifts.map shiftToGoldilocks) ((allChals.drop w.logB).take w.logK ++ allChals.drop (w.logB + w.logK))))) := by
                have hf0 := of_decide_eq_true hFinChk; have hrJ0 : setup.2.1 = rJ := hrJ; rw [hrJ0, hXOk, hQOk, hSOk, ← hrB, ← hrK, ← hrJp] at hf0
                simpa only [← hLB, ← hLK] using hf0
              have hSchedEq : mxfp4DegSchedule c.iopProof.logB c.iopProof.logK c.iopProof.logJ = mxfp4DegSchedule w.logB w.logK w.logJ := by rw [← hLB, ← hLK, ← hLJ]
              rw [hSchedEq] at hVerAll; have hRIL : rI.length = w.logI := by rw [← hrI]; exact (squeezeGoldilocksVec_length _ _).trans hLI.symm
              have hRJL : rJ.length = w.logJ := by rw [← hrJ]; exact (squeezeGoldilocksVec_length _ _).trans hLJ.symm
              have hHit := verifyMxfp4Sumcheck_sound w.logI w.logJ w.logK w.logB w.xTbl w.qInts w.sShifts
                c.iopProof.dClaim fv c.iopProof.sumcheckRounds rI rJ allChals setup.2.2 trPostSum hXLen hQLen hSLen hRIL hRJL hVerAll hFinValEq hSumFalse
              have hrBW : allChals.take w.logB = rB := by rw [hLB, hrB]
              have hrKW : (allChals.drop w.logB).take w.logK = rK := by rw [hLB, hLK, hrK]
              rw [hrBW, hrKW] at hHit; exact .inr (.inr (.inl hHit))
      else
        have hBadDom : invalidQIndices w ≠ [] ∨ invalidSIndices w ≠ [] := by
          cases h1 : (invalidQIndices w).isEmpty <;> cases h2 : (invalidSIndices w).isEmpty
          · exact .inl (by intro he; simp [he] at h1)
          · exact .inl (by intro he; simp [he] at h1)
          · exact .inr (by intro he; simp [he] at h2)
          · simp [h1, h2] at hDomValid
        let rawQs := (squeezeRawQueries suite.numQueries (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 c.iopProof.powNonce)) trPostFold)).1
        have hQR : (merkleRoot32 zkmlMerkleHash32 (w.qInts.mapIdx fun i q => zkmlLeaf32 0x06 i (encodeSignedInt q))).bytes = c.qMerkleRoot := by simpa only [mxfp4MantissaRoot32, hashMantissaLeaf_eq] using hQRoot
        have hSR : (merkleRoot32 zkmlMerkleHash32 (w.sShifts.mapIdx fun i s => zkmlLeaf32 0x07 i (leb128 s))).bytes = c.sMerkleRoot := by simpa only [mxfp4ShiftRoot32, hashShiftLeaf_eq] using hSRoot
        have hWalk : ∀ (qs : List Nat) (ops : List Mxfp4QueryOpening), (∀ op ∈ ops, op ∈ c.iopProof.queryOpenings) → ZipAll (QueryOpeningSpec c rI rJ rB rK rJp) qs ops →
            (∀ qRaw ∈ qs, qRaw % w.qInts.length ∉ invalidQIndices w ∧ qRaw % w.sShifts.length ∉ invalidSIndices w) ∨ ZkmlCshakeCollision M w c := by
          intro qs ops hSub hZip; induction hZip with
          | nil => exact .inl (fun _ hm => nomatch hm)
          | @cons qRaw op rest ops hOp _ ih =>
              obtain ⟨hQDom, hSDom, _, _, hClQSpec, hClSSpec, _⟩ := hOp; have hValidQ : isValidE2m1Mantissa op.qMantissa = true := decide_eq_true hQDom
              have hValidS : isValidMxfp4Shift op.sShift = true := decide_eq_true hSDom; have hClimbQ := (climbZkml32_iff ..).mpr hClQSpec
              have hClimbS := (climbZkml32_iff ..).mpr hClSSpec; have hOpMem := hSub op (.head _); let vQ := w.logB + w.logK + w.logJ; let vS := w.logK + w.logJ
              have hiQ : qRaw % 2 ^ vQ < 2 ^ vQ := Nat.mod_lt qRaw (Nat.two_pow_pos vQ); have hiS : qRaw % 2 ^ vS < 2 ^ vS := Nat.mod_lt qRaw (Nat.two_pow_pos vS)
              have hvQMax : vQ ≤ Nat.max (Nat.max (w.logI + w.logJ) (w.logI + w.logB + w.logK)) (w.logB + w.logK + w.logJ) := Nat.le_max_right _ _
              have hvSMax : vS ≤ Nat.max (Nat.max (w.logI + w.logJ) (w.logI + w.logB + w.logK)) (w.logB + w.logK + w.logJ) := Nat.le_trans (by dsimp only [vS, vQ]; omega) hvQMax
              if hQBad : qRaw % w.qInts.length ∈ invalidQIndices w then
                have hOpQCap : (encodeSignedInt op.qMantissa).length ≤ cap := Nat.le_trans (len_le_maxByteLen (by simp only [List.mem_append]; exact .inl (.inl (.inl (List.mem_map_of_mem hOpMem))))) hCapM
                have hWQCap : (encodeSignedInt (w.qInts[qRaw % 2 ^ vQ]'(hQLen.symm ▸ hiQ))).length ≤ cap := Nat.le_trans (len_le_maxByteLen (by simp only [List.mem_append]; exact .inl (.inl (.inr (List.mem_map_of_mem (List.getElem_mem _)))))) hCapM
                have hVQEq : c.iopProof.logB + c.iopProof.logK + c.iopProof.logJ = vQ := by simp [vQ, hLB, hLK, hLJ]
                rw [hVQEq, hashMantissaLeaf_eq] at hClimbQ
                cases extractZkmlMerkleAt 0x06 encodeSignedInt encodeSignedInt_injective vQ (qRaw % 2 ^ vQ) cap w.qInts hQLen hiQ op.qMantissa op.qPath c.qMerkleRoot hOpQCap hWQCap hQR hClimbQ (zkmlMerkleHonest_climb 0x06 encodeSignedInt vQ _ w.qInts hQLen hiQ) with
                | inr wCol => exact .inr (.inr ⟨wCol.msgA, wCol.msgB, Nat.le_trans wCol.lenA (by dsimp only [mxfp4MerkleMaxBytes, vQ, cap] at hvQMax ⊢; omega), Nat.le_trans wCol.lenB (by dsimp only [mxfp4MerkleMaxBytes, vQ, cap] at hvQMax ⊢; omega), wCol.distinct, wCol.sameDigest⟩)
                | inl hEqQ =>
                  exfalso; rw [hQLen] at hQBad; simp only [invalidQIndices, List.mem_filter, List.mem_range] at hQBad
                  obtain ⟨hLtQ, hInvQ⟩ := hQBad; simp only [hLtQ, ↓reduceDIte] at hInvQ; rw [← hEqQ.down, hValidQ] at hInvQ; simp at hInvQ
              else if hSBad : qRaw % w.sShifts.length ∈ invalidSIndices w then
                have hOpSCap : (leb128 op.sShift).length ≤ cap := Nat.le_trans (len_le_maxByteLen (by simp only [List.mem_append]; exact .inl (.inr (List.mem_map_of_mem hOpMem)))) hCapM
                have hWSCap : (leb128 (w.sShifts[qRaw % 2 ^ vS]'(hSLen.symm ▸ hiS))).length ≤ cap := Nat.le_trans (len_le_maxByteLen (by simp only [List.mem_append]; exact .inr (List.mem_map_of_mem (List.getElem_mem _)))) hCapM
                have hVSEq : c.iopProof.logK + c.iopProof.logJ = vS := by simp [vS, hLK, hLJ]
                rw [hVSEq, hashShiftLeaf_eq] at hClimbS
                cases extractZkmlMerkleAt 0x07 leb128 leb128_inj vS (qRaw % 2 ^ vS) cap w.sShifts hSLen hiS op.sShift op.sPath c.sMerkleRoot hOpSCap hWSCap hSR hClimbS (zkmlMerkleHonest_climb 0x07 leb128 vS _ w.sShifts hSLen hiS) with
                | inr wCol => exact .inr (.inr ⟨wCol.msgA, wCol.msgB, Nat.le_trans wCol.lenA (by dsimp only [mxfp4MerkleMaxBytes, vS, cap] at hvSMax ⊢; omega), Nat.le_trans wCol.lenB (by dsimp only [mxfp4MerkleMaxBytes, vS, cap] at hvSMax ⊢; omega), wCol.distinct, wCol.sameDigest⟩)
                | inl hEqS =>
                  exfalso; rw [hSLen] at hSBad; simp only [invalidSIndices, List.mem_filter, List.mem_range] at hSBad
                  obtain ⟨hLtS, hInvS⟩ := hSBad; simp only [hLtS, ↓reduceDIte] at hInvS; rw [← hEqS.down, hValidS] at hInvS; simp at hInvS
              else
                rcases ih (fun o ho => hSub o (.tail _ ho)) with hRest | hCol
                · left; intro z hz; rcases List.mem_cons.mp hz with rfl | htl
                  · exact ⟨hQBad, hSBad⟩
                  · exact hRest z htl
                · exact .inr hCol
        exact (hWalk rawQs c.iopProof.queryOpenings (fun _ h => h) hQListOk).elim (fun hMissed => .inr (.inr (.inr (.inr (.inl ⟨hBadDom, hMissed⟩))))) (fun hCol => .inr (.inr (.inr (.inr (.inr hCol)))))
theorem verifyMxfp4ChunkIop_sound {suite : ZkmlSuiteProfile} {M : Mxfp4ModelManifest} {powBits : Nat} {w : Mxfp4ChunkWitness} {c : ZkmlChunkReceipt}
    (hAcc : verifyMxfp4ChunkIop suite M powBits c = true) (hMatch : WitnessMatchesMxfp4Chunk w c) : ChunkMeetsPow suite powBits c ∧
    ∃ (rI rJ rB rK rJp : List Goldilocks) (finalVal : Goldilocks) (trPostFold : Transcript .instanceBound),
      runMxfp4SumcheckPhase suite c = some (rI, rJ, rB, rK, rJp, finalVal, trPostFold) ∧
      (let setup := mxfp4SetupRaw suite c.iopProof.logI c.iopProof.logJ c.iopProof.logK c.iopProof.logB c.modelWeightsRoot c.policyFloorDigest c.suiteDigest
         c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot c.iopProof.dClaim
       let rawQs := (squeezeRawQueries suite.numQueries (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 c.iopProof.powNonce)) trPostFold)).1
       (M = w.model ∧ (∀ q ∈ w.qInts, isValidE2m1Mantissa q = true) ∧ (∀ sh ∈ w.sShifts, isValidMxfp4Shift sh = true) ∧
         w.dTbl = mxfp4ContractTable w.logI w.logJ w.logK w.logB w.xTbl w.qInts w.sShifts) ∨ OuterMleRootHit w rI rJ ∨
       Mxfp4SumcheckRootHit w.logJ w.logK w.logB w.xTbl (w.qInts.map intToGoldilocks) (w.sShifts.map shiftToGoldilocks) rI rJ rB rK c.iopProof.sumcheckRounds setup.2.2 ∨
       AuthenticatedFoldWalkDeviation w c rI rJ rB rK rJp rawQs ∨ MissedInvalidWeightLeaf w rawQs ∨ ZkmlCshakeCollision M w c) :=
  verifyMxfp4ChunkIop_sound_of_unpack (verifyMxfp4ChunkIop_unpack hAcc) hMatch
theorem verifyMxfp4ChunkIop_registered_sound {suite : ZkmlSuiteProfile} {M : Mxfp4ModelManifest} {powBits : Nat} {w : Mxfp4ChunkWitness} {c : ZkmlChunkReceipt}
    (hAcc : verifyMxfp4ChunkIop suite M powBits c = true) (hMatch : WitnessMatchesMxfp4Chunk w c) (hRegQ : ∀ q ∈ w.qInts, isValidE2m1Mantissa q = true)
    (hRegS : ∀ sh ∈ w.sShifts, isValidMxfp4Shift sh = true) : ∃ (rI rJ rB rK rJp : List Goldilocks) (finalVal : Goldilocks) (trPostFold : Transcript .instanceBound),
      runMxfp4SumcheckPhase suite c = some (rI, rJ, rB, rK, rJp, finalVal, trPostFold) ∧
      (let setup := mxfp4SetupRaw suite c.iopProof.logI c.iopProof.logJ c.iopProof.logK c.iopProof.logB c.modelWeightsRoot c.policyFloorDigest c.suiteDigest
         c.chunkIdx c.layerIdx c.stateInCommit c.stateOutCommit c.qMerkleRoot c.sMerkleRoot c.iopProof.dClaim
       let rawQs := (squeezeRawQueries suite.numQueries (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 c.iopProof.powNonce)) trPostFold)).1
       (M = w.model ∧ w.dTbl = mxfp4ContractTable w.logI w.logJ w.logK w.logB w.xTbl w.qInts w.sShifts) ∨ OuterMleRootHit w rI rJ ∨
       Mxfp4SumcheckRootHit w.logJ w.logK w.logB w.xTbl (w.qInts.map intToGoldilocks) (w.sShifts.map shiftToGoldilocks) rI rJ rB rK c.iopProof.sumcheckRounds setup.2.2 ∨
       AuthenticatedFoldWalkDeviation w c rI rJ rB rK rJp rawQs ∨ ZkmlCshakeCollision M w c) := by
  obtain ⟨_, rI, rJ, rB, rK, rJp, fv, trPF, hPh, hDisj⟩ := verifyMxfp4ChunkIop_sound hAcc hMatch; refine ⟨rI, rJ, rB, rK, rJp, fv, trPF, hPh, ?_⟩
  rcases hDisj with ⟨hM, _, _, hD⟩ | hO | hS | hF | ⟨hBad, _⟩ | hC
  · exact .inl ⟨hM, hD⟩
  · exact .inr (.inl hO)
  · exact .inr (.inr (.inl hS))
  · exact .inr (.inr (.inr (.inl hF)))
  · exfalso; rcases hBad with hQNe | hSNe
    · apply hQNe; rw [invalidQIndices, List.filter_eq_nil_iff]; intro i hi; rw [List.mem_range] at hi; simp [hi, hRegQ _ (List.getElem_mem hi)]
    · apply hSNe; rw [invalidSIndices, List.filter_eq_nil_iff]; intro i hi; rw [List.mem_range] at hi; simp [hi, hRegS _ (List.getElem_mem hi)]
  · exact .inr (.inr (.inr (.inr hC)))
/-! ## 2. Honest `UD-100` (`UDR` & `JBR` vs. Withdrawn `CBR-130`) Suite Parameter Accounting -/
inductive ZkmlSecurityRegime where
  | provenUdr | provenJbr | withdrawnCbr
  deriving DecidableEq, Repr, Inhabited
inductive ZkmlRegimeStatus where
  | unconditionalProven | johnsonIdealised | withdrawnRefuted
  deriving DecidableEq, Repr, Inhabited
def ZkmlSecurityRegime.status : ZkmlSecurityRegime → ZkmlRegimeStatus
  | .provenUdr => .unconditionalProven | .provenJbr => .johnsonIdealised | .withdrawnCbr => .withdrawnRefuted
abbrev ZkmlSecurityRegime.Reportable (r : ZkmlSecurityRegime) : Prop := r.status ≠ .withdrawnRefuted
theorem provenUdr_reportable : ZkmlSecurityRegime.provenUdr.Reportable := by unfold ZkmlSecurityRegime.Reportable ZkmlSecurityRegime.status; decide
theorem provenJbr_reportable : ZkmlSecurityRegime.provenJbr.Reportable := by unfold ZkmlSecurityRegime.Reportable ZkmlSecurityRegime.status; decide
theorem withdrawnCbr_not_reportable : ¬ ZkmlSecurityRegime.withdrawnCbr.Reportable := by unfold ZkmlSecurityRegime.Reportable ZkmlSecurityRegime.status; decide
def provenFloorMilliBits : Nat := 100000
def udrQueryMilliBits : Nat → Nat
  | 0 => 0 | 1 => 415 | 2 => 678 | 3 => 830 | 4 => 912 | 5 => 955 | 6 => 977 | 7 => 988 | 8 => 994 | 9 => 997 | 10 => 998 | _ => 999
theorem udrQueryMilliBits_lt_1000 (lb : Nat) : udrQueryMilliBits lb < 1000 := by
  match lb with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => decide | _ + 11 => simp [udrQueryMilliBits]
theorem udrQueryMilliBits_lt_jbr {lb : Nat} (hlb : 1 ≤ lb) : udrQueryMilliBits lb < lb * 500 := by
  match lb with | 0 => omega | 1 => decide | k + 2 => have := udrQueryMilliBits_lt_1000 (k + 2); omega
def udrMilliBits (p : ZkmlSuiteProfile) : Nat := p.numQueries * udrQueryMilliBits p.logBlowup + p.grindBits * 1000
def jbrMilliBits (p : ZkmlSuiteProfile) : Nat := p.numQueries * (p.logBlowup * 500) + p.grindBits * 1000
def legacyWithdrawnCbrMilliBits (p : ZkmlSuiteProfile) : Nat := p.logBlowup * p.numQueries * 1000 + p.grindBits * 1000
def regimeMilliBits (r : ZkmlSecurityRegime) (p : ZkmlSuiteProfile) : Nat :=
  match r with | .provenUdr => udrMilliBits p | .provenJbr => jbrMilliBits p | .withdrawnCbr => legacyWithdrawnCbrMilliBits p
def logupCeilingMilliBits (p : ZkmlSuiteProfile) : Nat := ((p.fieldModulusBits - 1) * p.extDegree - p.logTraceHeight) * 1000
def bcsDigestCeilingMilliBits (p : ZkmlSuiteProfile) : Nat := (p.digestBits / 2) * 1000
def deployedIr2BabyBearExt4 : ZkmlSuiteProfile := ⟨31, 4, 6, 19, 16, 20, 256, 1⟩
def provenUdr86BabyBearExt4 : ZkmlSuiteProfile := { deployedIr2BabyBearExt4 with numQueries := 86 }
def tallTraceBabyBearExt4 : ZkmlSuiteProfile := { provenUdr86BabyBearExt4 with logTraceHeight := 25 }
def provenUdr86BabyBearExt5 : ZkmlSuiteProfile := { tallTraceBabyBearExt4 with extDegree := 5 }
def provenUdrGoldilocksExt2 : ZkmlSuiteProfile := ⟨64, 2, 6, 86, 16, 20, 256, 1⟩
def wideLeafUdr148GoldilocksExt2 : ZkmlSuiteProfile := ⟨64, 2, 2, 148, 0, 20, 256, 4⟩
def zeroLogArityGoldilocksExt2 : ZkmlSuiteProfile := { provenUdrGoldilocksExt2 with logArity := 0 }
theorem udr_strictly_below_withdrawn_cbr {p : ZkmlSuiteProfile} (hlb : 1 ≤ p.logBlowup) (hq : 1 ≤ p.numQueries) :
    udrMilliBits p < jbrMilliBits p ∧ jbrMilliBits p < legacyWithdrawnCbrMilliBits p ∧ udrMilliBits p < legacyWithdrawnCbrMilliBits p := by
  have hPos : 0 < p.numQueries := Nat.lt_of_lt_of_le (by decide) hq
  have hLbPos : 0 < p.logBlowup := Nat.lt_of_lt_of_le (by decide) hlb
  have hMul1 := Nat.mul_lt_mul_of_pos_left (udrQueryMilliBits_lt_jbr hlb) hPos
  have hMul2 := Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left (by decide : 500 < 1000) hLbPos) hPos
  have hComm : p.numQueries * (p.logBlowup * 1000) = p.logBlowup * p.numQueries * 1000 := by rw [← Nat.mul_assoc, Nat.mul_comm p.numQueries p.logBlowup]
  rw [hComm] at hMul2; unfold udrMilliBits jbrMilliBits legacyWithdrawnCbrMilliBits; have h1 := Nat.add_lt_add_right hMul1 (p.grindBits * 1000)
  have h2 := Nat.add_lt_add_right hMul2 (p.grindBits * 1000); exact ⟨h1, h2, Nat.lt_trans h1 h2⟩
theorem ud100_small_and_wide_leaf_minimality : udrMilliBits deployedIr2BabyBearExt4 = 34563 ∧ jbrMilliBits deployedIr2BabyBearExt4 = 73000 ∧
    legacyWithdrawnCbrMilliBits deployedIr2BabyBearExt4 = 130000 ∧ udrMilliBits { deployedIr2BabyBearExt4 with numQueries := 85 } = 99045 ∧
    udrMilliBits provenUdr86BabyBearExt4 = 100022 ∧ udrMilliBits { wideLeafUdr148GoldilocksExt2 with numQueries := 147 } = 99666 ∧ udrMilliBits wideLeafUdr148GoldilocksExt2 = 100344 := by decide
theorem grind_bits_additive_and_regime_free (p : ZkmlSuiteProfile) (g : Nat) : udrMilliBits { p with grindBits := p.grindBits + g } = udrMilliBits p + 1000 * g ∧
    jbrMilliBits { p with grindBits := p.grindBits + g } = jbrMilliBits p + 1000 * g ∧
    (1 ≤ p.logBlowup → udrMilliBits { p with numQueries := p.numQueries + 1 } - udrMilliBits p ≠
      jbrMilliBits { p with numQueries := p.numQueries + 1 } - jbrMilliBits p) := by
  refine ⟨by unfold udrMilliBits; simp only [Nat.add_mul]; omega,
          by unfold jbrMilliBits; simp only [Nat.add_mul]; omega, fun hlb => ?_⟩
  have := udrQueryMilliBits_lt_jbr hlb; unfold udrMilliBits jbrMilliBits; simp only [Nat.add_mul, Nat.one_mul]; omega
theorem extDegree_moves_logup_only (p : ZkmlSuiteProfile) (d' : Nat) : udrMilliBits { p with extDegree := d' } = udrMilliBits p ∧
    jbrMilliBits { p with extDegree := d' } = jbrMilliBits p := ⟨rfl, rfl⟩
@[expose] def ZkmlSuiteMeetsProvenFloor (r : ZkmlSecurityRegime) (p : ZkmlSuiteProfile) : Prop :=
  r.Reportable ∧ 1 ≤ p.logArity ∧ 1 ≤ p.numQueries ∧
  provenFloorMilliBits ≤ regimeMilliBits r p ∧
  provenFloorMilliBits ≤ logupCeilingMilliBits p ∧ provenFloorMilliBits ≤ bcsDigestCeilingMilliBits p
def checkZkmlSuiteProvenFloor (r : ZkmlSecurityRegime) (p : ZkmlSuiteProfile) : Bool :=
  decide (1 ≤ p.logArity ∧ 1 ≤ p.numQueries) &&
  match r with
  | .withdrawnCbr => false
  | .provenUdr =>
    decide (provenFloorMilliBits ≤ udrMilliBits p) &&
    decide (provenFloorMilliBits ≤ logupCeilingMilliBits p) && decide (provenFloorMilliBits ≤ bcsDigestCeilingMilliBits p)
  | .provenJbr =>
    decide (provenFloorMilliBits ≤ jbrMilliBits p) &&
    decide (provenFloorMilliBits ≤ logupCeilingMilliBits p) && decide (provenFloorMilliBits ≤ bcsDigestCeilingMilliBits p)
theorem checkZkmlSuiteProvenFloor_iff (r : ZkmlSecurityRegime) (p : ZkmlSuiteProfile) : checkZkmlSuiteProvenFloor r p = true ↔ ZkmlSuiteMeetsProvenFloor r p := by
  cases r with
  | withdrawnCbr => simp [checkZkmlSuiteProvenFloor, ZkmlSuiteMeetsProvenFloor, ZkmlSecurityRegime.Reportable, ZkmlSecurityRegime.status]
  | provenUdr => simp [checkZkmlSuiteProvenFloor, ZkmlSuiteMeetsProvenFloor, regimeMilliBits, provenUdr_reportable, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  | provenJbr => simp [checkZkmlSuiteProvenFloor, ZkmlSuiteMeetsProvenFloor, regimeMilliBits, provenJbr_reportable, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
theorem checkZkmlSuiteProvenFloor_sound {r : ZkmlSecurityRegime} {p : ZkmlSuiteProfile} (h : checkZkmlSuiteProvenFloor r p = true) :
    ZkmlSuiteMeetsProvenFloor r p ∧ r ≠ .withdrawnCbr ∧ 1 ≤ p.logArity ∧ 1 ≤ p.numQueries ∧
    p.logTraceHeight + 100 ≤ (p.fieldModulusBits - 1) * p.extDegree ∧ 200 ≤ p.digestBits := by
  have hm := (checkZkmlSuiteProvenFloor_iff r p).mp h; have hLog := hm.2.2.2.2.1; have hBcs := hm.2.2.2.2.2; unfold provenFloorMilliBits logupCeilingMilliBits at hLog
  unfold provenFloorMilliBits bcsDigestCeilingMilliBits at hBcs; exact ⟨hm, fun hEq => withdrawnCbr_not_reportable (hEq ▸ hm.1), hm.2.1, hm.2.2.1, by omega, by omega⟩
theorem suite_floor_admission_refusal_matrix : checkZkmlSuiteProvenFloor .provenUdr deployedIr2BabyBearExt4 = false ∧
    checkZkmlSuiteProvenFloor .provenJbr deployedIr2BabyBearExt4 = false ∧ checkZkmlSuiteProvenFloor .withdrawnCbr deployedIr2BabyBearExt4 = false ∧
    checkZkmlSuiteProvenFloor .provenUdr { provenUdr86BabyBearExt4 with logTraceHeight := 24 } = false ∧
    checkZkmlSuiteProvenFloor .provenUdr tallTraceBabyBearExt4 = false ∧ checkZkmlSuiteProvenFloor .provenUdr zeroLogArityGoldilocksExt2 = false ∧
    checkZkmlSuiteProvenFloor .provenUdr provenUdr86BabyBearExt4 = true ∧ checkZkmlSuiteProvenFloor .provenUdr provenUdr86BabyBearExt5 = true ∧
    checkZkmlSuiteProvenFloor .provenUdr provenUdrGoldilocksExt2 = true ∧ checkZkmlSuiteProvenFloor .provenUdr wideLeafUdr148GoldilocksExt2 = true := by decide
theorem checkZkmlSuiteProvenFloor_inhabited : ∃ r p, checkZkmlSuiteProvenFloor r p = true ∧ ZkmlSuiteMeetsProvenFloor r p :=
  ⟨.provenUdr, wideLeafUdr148GoldilocksExt2, by decide, (checkZkmlSuiteProvenFloor_iff .provenUdr wideLeafUdr148GoldilocksExt2).mp (by decide)⟩
/-! ## 3. Full-Model Sequential `MXFP4` Stream, Declarative `provenZkmlJudge` & Multi-Turn Session -/
structure ZkmlStreamStatement where
  modelWeightsRoot : ByteArray
  policyFloorDigest : ByteArray
  suiteDigest : ByteArray
  initialStateCommit : ByteArray
  finalStateCommit : ByteArray
  numChunks : Nat
  requiredPowBits : Nat
  pinnedNumQueries : Option Nat
  deriving DecidableEq, Inhabited
abbrev ZkmlStreamStatement.WellFormed32 (s : ZkmlStreamStatement) : Prop :=
  s.modelWeightsRoot.size = 32 ∧ s.policyFloorDigest.size = 32 ∧ s.suiteDigest.size = 32 ∧
  s.initialStateCommit.size = 32 ∧ s.finalStateCommit.size = 32 ∧ 1 ≤ s.numChunks ∧ s.numChunks < 2 ^ 64 ∧ s.requiredPowBits ≤ 64
inductive LayerCarrySteps (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (weightsRoot policyDigest suiteDigest : ByteArray) (powBits : Nat) :
    Nat → ByteArray → List ZkmlChunkReceipt → ByteArray → Prop where
  | nil (idx : Nat) (st : ByteArray) : LayerCarrySteps suite M weightsRoot policyDigest suiteDigest powBits idx st [] st
  | cons {idx : Nat} {finalSt : ByteArray} (c : ZkmlChunkReceipt) (rest : List ZkmlChunkReceipt) :
      c.WellFormed32 → c.modelWeightsRoot = weightsRoot → c.policyFloorDigest = policyDigest → c.suiteDigest = suiteDigest →
      c.chunkIdx.toNat = idx → c.layerIdx.toNat = idx → ChunkMeetsPow suite powBits c → ValidMxfp4ChunkIopSpec suite M powBits c →
      LayerCarrySteps suite M weightsRoot policyDigest suiteDigest powBits (idx + 1) c.stateOutCommit rest finalSt →
      LayerCarrySteps suite M weightsRoot policyDigest suiteDigest powBits idx c.stateInCommit (c :: rest) finalSt
@[expose] def ValidZkmlChunkChainSpec (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (stmt : ZkmlStreamStatement) (chain : List ZkmlChunkReceipt) : Prop :=
  stmt.WellFormed32 ∧ stmt.pinnedNumQueries = some suite.numQueries ∧ stmt.suiteDigest = suite.digest ∧ M.root = stmt.modelWeightsRoot ∧
  stmt.numChunks = M.layers.length ∧ chain.length = stmt.numChunks ∧
  LayerCarrySteps suite M stmt.modelWeightsRoot stmt.policyFloorDigest stmt.suiteDigest stmt.requiredPowBits 0 stmt.initialStateCommit chain stmt.finalStateCommit
theorem layerCarrySteps_element_invariants {suite : ZkmlSuiteProfile} {M : Mxfp4ModelManifest} {w p s : ByteArray} {pow idx : Nat}
    {stIn stOut : ByteArray} {chain : List ZkmlChunkReceipt} (h : LayerCarrySteps suite M w p s pow idx stIn chain stOut) : (∀ i (hi : i < chain.length),
      chain[i].WellFormed32 ∧ chain[i].modelWeightsRoot = w ∧ chain[i].policyFloorDigest = p ∧ chain[i].suiteDigest = s ∧
      chain[i].chunkIdx.toNat = idx + i ∧ chain[i].layerIdx.toNat = idx + i ∧ ChunkMeetsPow suite pow chain[i] ∧ ValidMxfp4ChunkIopSpec suite M pow chain[i]) ∧
    (∀ i (hi1 : i + 1 < chain.length), chain[i].stateOutCommit = chain[i + 1].stateInCommit) ∧
    (∀ hne : chain ≠ [], (chain.head hne).stateInCommit = stIn ∧ (chain.getLast hne).stateOutCommit = stOut) := by
  induction h with
  | nil => exact ⟨(fun _ hi => nomatch hi), (fun _ hi1 => nomatch hi1), (fun hne => absurd rfl hne)⟩
  | @cons idx' _ c rest hwf hw hp hs hidx hlidx hpow hiop hrest ih =>
    obtain ⟨hElem, hAdj, hEnds⟩ := ih; refine ⟨fun i hi => ?_, fun i hi1 => ?_, fun _ => ⟨rfl, ?_⟩⟩
    · cases i with
      | zero => simp only [List.getElem_cons_zero, Nat.add_zero]; exact ⟨hwf, hw, hp, hs, hidx, hlidx, hpow, hiop⟩
      | succ j => have hShift : idx' + (j + 1) = idx' + 1 + j := by omega
                  rw [hShift]; simpa only [List.getElem_cons_succ] using hElem j (Nat.lt_of_succ_lt_succ hi)
    · cases i with
      | zero => cases rest with | nil => simp at hi1 | cons c₂ rs => simpa [List.head_cons] using (hEnds (List.cons_ne_nil c₂ rs)).1.symm
      | succ j => simpa only [List.getElem_cons_succ] using hAdj j (Nat.lt_of_succ_lt_succ hi1)
    · cases rest with
      | nil => generalize hcOut : c.stateOutCommit = stMid at hrest; cases hrest; exact hcOut
      | cons c₂ rs => simpa [List.getLast_cons] using (hEnds (List.cons_ne_nil c₂ rs)).2
theorem validZkmlChunkChain_invariants {suite : ZkmlSuiteProfile} {M : Mxfp4ModelManifest} {stmt : ZkmlStreamStatement} {chain : List ZkmlChunkReceipt}
    (h : ValidZkmlChunkChainSpec suite M stmt chain) : 1 ≤ chain.length ∧ chain.length = M.layers.length ∧
    stmt.pinnedNumQueries = some suite.numQueries ∧ stmt.suiteDigest = suite.digest ∧ M.root = stmt.modelWeightsRoot ∧ (∀ i (hi : i < chain.length),
      chain[i].modelWeightsRoot = stmt.modelWeightsRoot ∧ chain[i].policyFloorDigest = stmt.policyFloorDigest ∧ chain[i].suiteDigest = stmt.suiteDigest ∧
      chain[i].chunkIdx.toNat = i ∧ chain[i].layerIdx.toNat = i ∧ ChunkMeetsPow suite stmt.requiredPowBits chain[i] ∧
      ValidMxfp4ChunkIopSpec suite M stmt.requiredPowBits chain[i]) ∧ (∀ i (hi1 : i + 1 < chain.length), chain[i].stateOutCommit = chain[i + 1].stateInCommit) ∧
    (∀ hne : chain ≠ [], (chain.head hne).stateInCommit = stmt.initialStateCommit ∧ (chain.getLast hne).stateOutCommit = stmt.finalStateCommit) := by
  obtain ⟨hStmt, hPin, hSDig, hMRoot, hNumL, hLen, hSteps⟩ := h; have hGe1 := hStmt.2.2.2.2.2.1; have hAll := layerCarrySteps_element_invariants hSteps
  refine ⟨by omega, hLen.trans hNumL, hPin, hSDig, hMRoot, fun i hi => ?_, hAll.2.1, hAll.2.2⟩
  obtain ⟨_, hw, hp, hs, hidx, hlidx, hpow, hiop⟩ := hAll.1 i hi; exact ⟨hw, hp, hs, by simpa using hidx, by simpa using hlidx, hpow, hiop⟩
theorem zkmlChunkChain_binds_endToEnd : ∀ {chain₁ chain₂ : List ZkmlChunkReceipt}, chain₁.map zkmlChunkDigest = chain₂.map zkmlChunkDigest → chain₁ = chain₂ ∨
        CollisionAmong (cshake256Bytes "OBEND.SHE.ZKML_CHUNK/v1".toUTF8.data.toList) (fun x => x ∈ (chain₁ ++ chain₂).map ZkmlChunkReceipt.preimage)
  | [], [], _ => .inl rfl | [], _ :: _, h => nomatch h | _ :: _, [], h => nomatch h
  | c₁ :: rs₁, c₂ :: rs₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h; cases extractZkmlChunkBinding c₁ c₂ h.1 with
    | inr hHeadCol =>
      exact .inr (hHeadCol.down.mono fun _ hx => by
        simp only [List.cons_append, List.map_cons, List.mem_cons, List.map_append, List.mem_append]; rcases hx with rfl | rfl
        · exact .inl rfl
        · exact .inr (.inr (.inl rfl)))
    | inl hHeadEq =>
      cases zkmlChunkChain_binds_endToEnd h.2 with
      | inl hTailEq => left; rw [hHeadEq.down, hTailEq]
      | inr hTailCol =>
        exact .inr (hTailCol.mono fun _ hx => by
          simp only [List.map_append, List.mem_append] at hx; simp only [List.cons_append, List.map_cons, List.mem_cons, List.map_append, List.mem_append]
          rcases hx with hx₁ | hx₂
          · exact .inr (.inl hx₁)
          · exact .inr (.inr (.inr hx₂)))
inductive ZkmlRefusalClause where
  | withdrawnCbrRejected | belowProven100BitFloor | unpinnedOrZeroAritySuite
  | weightRootDrift | brokenRecurrentCarry | insufficientPowGrind
  | invalidChunkIopProof | certDigestMismatch
  deriving DecidableEq, Repr, Inhabited
def provenZkmlRefutes : ZkmlRefusalClause → Bool
  | .certDigestMismatch => false | _ => true
private def chunkRootMismatch (stmt : ZkmlStreamStatement) (c : ZkmlChunkReceipt) : Bool :=
  decide (c.modelWeightsRoot.size ≠ 32) || decide (c.policyFloorDigest.size ≠ 32) ||
  decide (c.suiteDigest.size ≠ 32) || decide (c.modelWeightsRoot ≠ stmt.modelWeightsRoot) ||
  decide (c.policyFloorDigest ≠ stmt.policyFloorDigest) || decide (c.suiteDigest ≠ stmt.suiteDigest)
private def chunkCarryMismatch (idx : Nat) (curState : ByteArray) (c : ZkmlChunkReceipt) : Bool :=
  decide (c.stateInCommit.size ≠ 32) || decide (c.stateOutCommit.size ≠ 32) ||
  decide (c.qMerkleRoot.size ≠ 32) || decide (c.sMerkleRoot.size ≠ 32) ||
  decide (c.chunkIdx.toNat ≠ idx) || decide (c.layerIdx.toNat ≠ idx) || decide (c.stateInCommit ≠ curState)
private theorem validMxfp4ChunkIopSpec_implies_pow {suite : ZkmlSuiteProfile} {M : Mxfp4ModelManifest} {powBits : Nat} {c : ZkmlChunkReceipt}
    (h : ValidMxfp4ChunkIopSpec suite M powBits c) : ChunkMeetsPow suite powBits c := by
  obtain ⟨hWf, _, hL, hFL, allChals, fv, trPS, hSc, hFv, hGr, hZN, hP64, hMod, _⟩ := h
  exact ⟨hGr, hZN, ⟨hWf, (proofBoundsOk_iff c.iopProof).mp (layerAndFold_implies_proofBounds hL hFL)⟩, _, _, allChals, fv, trPS, rfl, rfl, hSc, hFv, hP64, hMod⟩
def verifyChunkStep (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (powBits idx : Nat) (c : ZkmlChunkReceipt) :
    Except (ZkmlRefusalClause × List Nat) Unit :=
  let p := c.iopProof
  if !decide c.WellFormed32 || !decide (1 ≤ suite.numQueries ∧ suite.numQueries ≤ 1024 ∧ 1 ≤ suite.logArity) ||
      !layerMatchesReceipt M c || !foldRootsMatchDims p then .error (.invalidChunkIopProof, [idx])
  else if !decide (suite.grindBits ≤ powBits) || !decide (powBits = 0 → p.powNonce = 0) then .error (.insufficientPowGrind, [idx])
  else match runMxfp4SumcheckPhase suite c with
    | none => .error (.invalidChunkIopProof, [idx])
    | some (rI, rJ, rB, rK, rJp, _, trPostFold) =>
      if !checkChunkPow powBits (powCandidateState trPostFold p.powNonce) then .error (.insufficientPowGrind, [idx])
      else if !verifyMxfp4QueryList c rI rJ rB rK rJp (squeezeRawQueries suite.numQueries
          (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 p.powNonce)) trPostFold)).1 p.queryOpenings then
        .error (.invalidChunkIopProof, [idx])
      else .ok ()
private theorem verifyChunkStep_ok_iff (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (powBits idx : Nat) (c : ZkmlChunkReceipt) :
    verifyChunkStep suite M powBits idx c = .ok () ↔ verifyMxfp4ChunkIop suite M powBits c = true := by
  unfold verifyChunkStep verifyMxfp4ChunkIop; dsimp only
  cases decide c.WellFormed32
  · simp
  · cases decide (1 ≤ suite.numQueries ∧ suite.numQueries ≤ 1024 ∧ 1 ≤ suite.logArity)
    · simp
    · cases layerMatchesReceipt M c
      · simp
      · cases foldRootsMatchDims c.iopProof
        · simp
        · cases runMxfp4SumcheckPhase suite c with
          | none => cases decide (suite.grindBits ≤ powBits) <;> cases decide (powBits = 0 → c.iopProof.powNonce = 0) <;> simp
          | some res =>
            rcases res with ⟨rI, rJ, rB, rK, rJp, _, trPF⟩
            cases decide (suite.grindBits ≤ powBits)
            · simp
            · cases decide (powBits = 0 → c.iopProof.powNonce = 0)
              · simp
              · dsimp only
                cases checkChunkPow powBits (powCandidateState trPF c.iopProof.powNonce) <;>
                cases verifyMxfp4QueryList c rI rJ rB rK rJp (squeezeRawQueries suite.numQueries
                    (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 c.iopProof.powNonce)) trPF)).1 c.iopProof.queryOpenings <;> simp
def verifyChunksLoop (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt) :
    Nat → Nat → ByteArray → Array ByteArray → Except (ZkmlRefusalClause × List Nat) (Array ByteArray)
  | 0, idx, curState, acc =>
    if decide (curState = stmt.finalStateCommit) then .ok acc else .error (.brokenRecurrentCarry, [idx])
  | rem + 1, idx, curState, acc =>
    if hIdx : idx < chunks.size then
      let c := chunks[idx]; if chunkRootMismatch stmt c then .error (.weightRootDrift, [idx])
      else if chunkCarryMismatch idx curState c then .error (.brokenRecurrentCarry, [idx])
      else match verifyChunkStep suite M stmt.requiredPowBits idx c with
        | .error e => .error e
        | .ok () => verifyChunksLoop suite M stmt chunks rem (idx + 1) c.stateOutCommit (acc.push (zkmlChunkDigest c))
    else .error (.brokenRecurrentCarry, [idx])
def verifyZkmlChunkChainExec (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (stmt : ZkmlStreamStatement)
    (chunks : Array ZkmlChunkReceipt) : Except (ZkmlRefusalClause × List Nat) (Array ByteArray) :=
  if !decide (stmt.pinnedNumQueries = some suite.numQueries) then .error (.unpinnedOrZeroAritySuite, [])
  else if !decide (stmt.requiredPowBits ≤ 64) then .error (.insufficientPowGrind, [])
  else if decide (stmt.modelWeightsRoot.size ≠ 32) || decide (stmt.policyFloorDigest.size ≠ 32) ||
      decide (stmt.suiteDigest.size ≠ 32) || decide (stmt.suiteDigest ≠ suite.digest) || decide (M.root ≠ stmt.modelWeightsRoot) then
    .error (.weightRootDrift, [])
  else if decide (stmt.initialStateCommit.size ≠ 32) || decide (stmt.finalStateCommit.size ≠ 32) || !decide (1 ≤ stmt.numChunks) || !decide (stmt.numChunks < 2 ^ 64) ||
      decide (stmt.numChunks ≠ M.layers.length) || decide (chunks.size ≠ stmt.numChunks) then
    .error (.brokenRecurrentCarry, [chunks.size])
  else verifyChunksLoop suite M stmt chunks chunks.size 0 stmt.initialStateCommit #[]
private theorem verifyChunksLoop_sound (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt) :
    ∀ (rem idx : Nat) (curState : ByteArray) (acc out : Array ByteArray), chunks.size - idx = rem → verifyChunksLoop suite M stmt chunks rem idx curState acc = .ok out →
      LayerCarrySteps suite M stmt.modelWeightsRoot stmt.policyFloorDigest stmt.suiteDigest
        stmt.requiredPowBits idx curState (chunks.toList.drop idx) stmt.finalStateCommit ∧ out.toList = acc.toList ++ (chunks.toList.drop idx).map zkmlChunkDigest
  | 0, idx, curState, acc, out, hRem, hOk => by
    rw [List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)]
    unfold verifyChunksLoop at hOk; cases hEq : decide (curState = stmt.finalStateCommit)
    · simp [hEq] at hOk
    · simp only [hEq, ↓reduceIte, Except.ok.injEq] at hOk; rw [of_decide_eq_true hEq, ← hOk]; exact ⟨.nil idx stmt.finalStateCommit, by simp⟩
  | rem + 1, idx, curState, acc, out, hRem, hOk => by
    have hIdx : idx < chunks.size := by omega
    have hDrop : chunks.toList.drop idx = chunks[idx] :: chunks.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact hIdx)]; simp only [Array.getElem_toList]
    rw [hDrop]; unfold verifyChunksLoop at hOk; simp only [hIdx, ↓reduceDIte] at hOk; cases hRoot : chunkRootMismatch stmt chunks[idx]
    · simp only [hRoot, Bool.false_eq_true, ↓reduceIte] at hOk; cases hCarry : chunkCarryMismatch idx curState chunks[idx]
      · simp only [hCarry, Bool.false_eq_true, ↓reduceIte] at hOk; cases hStep : verifyChunkStep suite M stmt.requiredPowBits idx chunks[idx] with
        | error _ => rw [hStep] at hOk; cases hOk
        | ok u =>
          cases u; rw [hStep] at hOk; dsimp only at hOk
          obtain ⟨hSteps, hOut⟩ := verifyChunksLoop_sound suite M stmt chunks rem (idx + 1)
            chunks[idx].stateOutCommit (acc.push (zkmlChunkDigest chunks[idx])) out (by omega) hOk
          have hSpec := (verifyMxfp4ChunkIop_iff_spec ..).mp ((verifyChunkStep_ok_iff ..).mp hStep)
          unfold chunkRootMismatch at hRoot; unfold chunkCarryMismatch at hCarry
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not] at hRoot hCarry; obtain ⟨⟨⟨⟨⟨hwSz, hpSz⟩, hsSz⟩, hwEq⟩, hpEq⟩, hsEq⟩ := hRoot
          obtain ⟨⟨⟨⟨⟨⟨hsinSz, hsoutSz⟩, hqrSz⟩, hsrSz⟩, hIdxEq⟩, hLIdxEq⟩, hSinEq⟩ := hCarry; rw [← hSinEq]
          refine ⟨.cons chunks[idx] _ ⟨hwSz, hpSz, hsSz, hsinSz, hsoutSz, hqrSz, hsrSz⟩ hwEq hpEq hsEq hIdxEq hLIdxEq
            (validMxfp4ChunkIopSpec_implies_pow hSpec) hSpec hSteps, ?_⟩
          rw [hOut]; simp [Array.toList_push, List.append_assoc]
      · simp [hCarry] at hOk
    · simp [hRoot] at hOk
private theorem verifyChunksLoop_complete (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt) :
    ∀ (rem idx : Nat) (curState : ByteArray) (acc : Array ByteArray), chunks.size - idx = rem →
      LayerCarrySteps suite M stmt.modelWeightsRoot stmt.policyFloorDigest stmt.suiteDigest
        stmt.requiredPowBits idx curState (chunks.toList.drop idx) stmt.finalStateCommit → verifyChunksLoop suite M stmt chunks rem idx curState acc =
        .ok ⟨acc.toList ++ (chunks.toList.drop idx).map zkmlChunkDigest⟩
  | 0, idx, _, acc, hRem, hSteps => by
    rw [List.drop_eq_nil_iff.mpr (by simp only [Array.length_toList]; omega)] at hSteps ⊢
    cases hSteps with | nil => unfold verifyChunksLoop; simp
  | rem + 1, idx, _, acc, hRem, hSteps => by
    have hIdx : idx < chunks.size := by omega
    have hDrop : chunks.toList.drop idx = chunks[idx] :: chunks.toList.drop (idx + 1) := by
      rw [List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact hIdx)]; simp only [Array.getElem_toList]
    rw [hDrop] at hSteps ⊢; cases hSteps with
    | cons _ _ hWf hwEq hpEq hsEq hIdxEq hLIdxEq _ hIopSpec hTail =>
      obtain ⟨hwSz, hpSz, hsSz, hsinSz, hsoutSz, hqrSz, hsrSz⟩ := hWf
      have hRootF : chunkRootMismatch stmt chunks[idx] = false := by unfold chunkRootMismatch; rw [hwSz, hpSz, hsSz, hwEq, hpEq, hsEq]; simp
      have hCarryF : chunkCarryMismatch idx chunks[idx].stateInCommit chunks[idx] = false := by
        unfold chunkCarryMismatch; rw [hsinSz, hsoutSz, hqrSz, hsrSz, hIdxEq, hLIdxEq]; simp
      have hStep := (verifyChunkStep_ok_iff suite M stmt.requiredPowBits idx chunks[idx]).mpr
        ((verifyMxfp4ChunkIop_iff_spec suite M stmt.requiredPowBits chunks[idx]).mpr hIopSpec)
      unfold verifyChunksLoop; simp only [hIdx, ↓reduceDIte, hRootF, hCarryF, Bool.false_eq_true, ↓reduceIte, hStep]
      rw [verifyChunksLoop_complete suite M stmt chunks rem (idx + 1) chunks[idx].stateOutCommit (acc.push (zkmlChunkDigest chunks[idx])) (by omega) hTail]
      simp [Array.toList_push, List.append_assoc]
theorem verifyZkmlChunkChainExec_iff_spec (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest)
    (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt) (out : Array ByteArray) : verifyZkmlChunkChainExec suite M stmt chunks = .ok out ↔
      ValidZkmlChunkChainSpec suite M stmt chunks.toList ∧ out.toList = chunks.toList.map zkmlChunkDigest := by
  constructor
  · intro hOk; unfold verifyZkmlChunkChainExec at hOk; cases hPin : decide (stmt.pinnedNumQueries = some suite.numQueries)
    · rw [hPin] at hOk; cases hOk
    simp only [hPin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk; cases hPow64 : decide (stmt.requiredPowBits ≤ 64)
    · rw [hPow64] at hOk; cases hOk
    simp only [hPow64, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hR : (decide (stmt.modelWeightsRoot.size ≠ 32) || decide (stmt.policyFloorDigest.size ≠ 32) ||
        decide (stmt.suiteDigest.size ≠ 32) || decide (stmt.suiteDigest ≠ suite.digest) || decide (M.root ≠ stmt.modelWeightsRoot))
    · simp only [hR, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hS : (decide (stmt.initialStateCommit.size ≠ 32) || decide (stmt.finalStateCommit.size ≠ 32) ||
          !decide (1 ≤ stmt.numChunks) || !decide (stmt.numChunks < 2 ^ 64) || decide (stmt.numChunks ≠ M.layers.length) || decide (chunks.size ≠ stmt.numChunks))
      · simp only [hS, Bool.false_eq_true, ↓reduceIte] at hOk
        obtain ⟨hSteps, hOut⟩ := verifyChunksLoop_sound suite M stmt chunks chunks.size 0 stmt.initialStateCommit #[] out (Nat.sub_zero _) hOk
        simp only [List.drop_zero] at hSteps hOut
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, decide_eq_true_eq, Decidable.not_not] at hR hS
        obtain ⟨⟨⟨⟨hwSz, hpSz⟩, hsSz⟩, hSDig⟩, hMRoot⟩ := hR; obtain ⟨⟨⟨⟨⟨hInSz, hFinSz⟩, hGe1⟩, hLt64⟩, hNumL⟩, hSzEq⟩ := hS
        exact ⟨⟨⟨hwSz, hpSz, hsSz, hInSz, hFinSz, hGe1, hLt64, of_decide_eq_true hPow64⟩,
          of_decide_eq_true hPin, hSDig, hMRoot, hNumL, by simpa only [Array.length_toList] using hSzEq, hSteps⟩, hOut⟩
      · rw [hS] at hOk; cases hOk
    · rw [hR] at hOk; cases hOk
  · rintro ⟨⟨⟨hwSz, hpSz, hsSz, hInSz, hFinSz, hGe1, hLt64, hPow64⟩, hPin, hSDig, hMRoot, hNumL, hLen, hSteps⟩, hOutEq⟩
    have hSzEq : chunks.size = stmt.numChunks := by simpa only [Array.length_toList] using hLen
    have hLoop := verifyChunksLoop_complete suite M stmt chunks chunks.size 0 stmt.initialStateCommit #[] (Nat.sub_zero _) (by simpa [List.drop_zero] using hSteps)
    simp only [List.drop_zero] at hLoop
    have hRFalse : (decide (stmt.modelWeightsRoot.size ≠ 32) || decide (stmt.policyFloorDigest.size ≠ 32) ||
        decide (stmt.suiteDigest.size ≠ 32) || decide (stmt.suiteDigest ≠ suite.digest) || decide (M.root ≠ stmt.modelWeightsRoot)) = false := by
      rw [hwSz, hpSz, hsSz, hSDig, hMRoot]; simp
    have hSFalse : (decide (stmt.initialStateCommit.size ≠ 32) || decide (stmt.finalStateCommit.size ≠ 32) ||
        !decide (1 ≤ stmt.numChunks) || !decide (stmt.numChunks < 2 ^ 64) ||
        decide (stmt.numChunks ≠ M.layers.length) || decide (chunks.size ≠ stmt.numChunks)) = false := by
      rw [hInSz, hFinSz, decide_eq_true hGe1, decide_eq_true hLt64, hSzEq, hNumL]; simp
    unfold verifyZkmlChunkChainExec; rw [decide_eq_true hPin, decide_eq_true hPow64, hRFalse, hSFalse, hLoop]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases out; simp only [Except.ok.injEq, Array.mk.injEq]; exact hOutEq.symm
theorem tampered_weights_or_hidden_carry_refused (suite : ZkmlSuiteProfile) (M : Mxfp4ModelManifest) (stmt : ZkmlStreamStatement) (chunks : Array ZkmlChunkReceipt)
    (hTamper : stmt.pinnedNumQueries ≠ some suite.numQueries ∨ stmt.suiteDigest ≠ suite.digest ∨ M.root ≠ stmt.modelWeightsRoot ∨ chunks.size ≠ M.layers.length ∨
      (∃ i : Fin chunks.size, chunks[i].modelWeightsRoot ≠ stmt.modelWeightsRoot ∨ chunks[i].policyFloorDigest ≠ stmt.policyFloorDigest ∨
        chunks[i].suiteDigest ≠ stmt.suiteDigest ∨ chunks[i].layerIdx.toNat ≠ i.val ∨ verifyMxfp4ChunkIop suite M stmt.requiredPowBits chunks[i] = false) ∨
      (∃ i : Nat, ∃ hi1 : i + 1 < chunks.size, (chunks[i]'(Nat.lt_of_succ_lt hi1)).stateOutCommit ≠ (chunks[i + 1]'hi1).stateInCommit) ∨
      (∃ h0 : 0 < chunks.size, (chunks[0]'h0).stateInCommit ≠ stmt.initialStateCommit) ∨ (∃ hpos : 0 < chunks.size,
        (chunks[chunks.size - 1]'(Nat.sub_lt hpos (by decide))).stateOutCommit ≠ stmt.finalStateCommit)) : ¬ ValidZkmlChunkChainSpec suite M stmt chunks.toList ∧
    ∀ out, verifyZkmlChunkChainExec suite M stmt chunks ≠ .ok out := by
  have hNoSpec : ¬ ValidZkmlChunkChainSpec suite M stmt chunks.toList := by
    intro hSpec; obtain ⟨_, hLenM, hPin, hSDig, hMRoot, hElem, hAdj, hEnds⟩ := validZkmlChunkChain_invariants hSpec
    rcases hTamper with hBadPin | hBadS | hMBad | hBadLen | ⟨i, hDrift⟩ | ⟨i, hi1, hBreak⟩ | ⟨h0, hInit⟩ | ⟨hpos, hFin⟩
    · exact hBadPin hPin
    · exact hBadS hSDig
    · exact hMBad hMRoot
    · exact hBadLen (by simpa only [Array.length_toList] using hLenM)
    · have hiL : i.val < chunks.toList.length := by simpa only [Array.length_toList] using i.isLt
      obtain ⟨hw, hp, hs, _, hlidx, _, hiopSpec⟩ := hElem i.val hiL; have hiop := (verifyMxfp4ChunkIop_iff_spec ..).mpr hiopSpec
      simp only [Array.getElem_toList, Fin.getElem_fin] at hw hp hs hlidx hiop hDrift
      rcases hDrift with h1 | h2 | h3 | h4 | h5
      · exact h1 hw
      · exact h2 hp
      · exact h3 hs
      · exact h4 hlidx
      · rw [hiop] at h5; cases h5
    · have hi1L : i + 1 < chunks.toList.length := by simpa only [Array.length_toList] using hi1
      exact hBreak (by simpa only [Array.getElem_toList] using hAdj i hi1L)
    · cases chunks with | mk cs => cases cs with | nil => simp at h0 | cons c₀ rest => exact hInit (hEnds (List.cons_ne_nil c₀ rest)).1
    · have hne : chunks.toList ≠ [] := List.ne_nil_of_length_pos (by simpa only [Array.length_toList] using hpos)
      have hLastEq : chunks.toList.getLast hne = chunks[chunks.size - 1]'(Nat.sub_lt hpos (by decide)) := by rw [List.getLast_eq_getElem]; simp
      exact hFin (hLastEq ▸ (hEnds hne).2)
  exact ⟨hNoSpec, fun out hOk => hNoSpec ((verifyZkmlChunkChainExec_iff_spec suite M stmt chunks out).mp hOk).1⟩
structure ZkmlTurnQuery where
  claimedRegime : ZkmlSecurityRegime
  suite : ZkmlSuiteProfile
  model : Mxfp4ModelManifest
  statement : ZkmlStreamStatement
  chunks : List ZkmlChunkReceipt
  deriving DecidableEq, Inhabited
structure ZkmlTurnCert where
  chunkDigests : List ByteArray
  deriving DecidableEq, Inhabited
@[expose] def ZkmlTurnMeaning (q : ZkmlTurnQuery) (c : ZkmlTurnCert) : Prop :=
  q.claimedRegime = .provenUdr ∧ ZkmlSuiteMeetsProvenFloor .provenUdr q.suite ∧ q.suite.grindBits ≤ q.statement.requiredPowBits ∧
  ValidZkmlChunkChainSpec q.suite q.model q.statement q.chunks ∧ c.chunkDigests = q.chunks.map zkmlChunkDigest
abbrev ZkmlDecidableFragment (q : ZkmlTurnQuery) : Prop := q.statement.WellFormed32 ∧ q.chunks ≠ []
def checkZkmlTurn (grade : Nat) (q : ZkmlTurnQuery) (c : ZkmlTurnCert) : Obend.Judge.Verdict ZkmlRefusalClause :=
  if decide (grade < q.chunks.length) then .uncovered
  else if decide (q.claimedRegime = .withdrawnCbr) then .refused .withdrawnCbrRejected []
  else if !decide (q.claimedRegime = .provenUdr) then .refused .belowProven100BitFloor []
  else if !decide (1 ≤ q.suite.logArity ∧ 1 ≤ q.suite.numQueries) then .refused .unpinnedOrZeroAritySuite []
  else if !checkZkmlSuiteProvenFloor .provenUdr q.suite then .refused .belowProven100BitFloor []
  else if !decide (q.suite.grindBits ≤ q.statement.requiredPowBits) then .refused .insufficientPowGrind []
  else match verifyZkmlChunkChainExec q.suite q.model q.statement ⟨q.chunks⟩ with
    | .error (k, path) => .refused k path
    | .ok digests => if decide (c.chunkDigests = digests.toList) then .ok else .refused .certDigestMismatch []
theorem provenZkmlJudge_sound {grade : Nat} {q : ZkmlTurnQuery} {c : ZkmlTurnCert} (h : checkZkmlTurn grade q c = .ok) : ZkmlTurnMeaning q c := by
  unfold checkZkmlTurn at h; cases hG : decide (grade < q.chunks.length)
  · simp only [hG, Bool.false_eq_true, ↓reduceIte] at h; cases hCbr : decide (q.claimedRegime = .withdrawnCbr)
    · simp only [hCbr, Bool.false_eq_true, ↓reduceIte] at h; cases hUdr : decide (q.claimedRegime = .provenUdr)
      · simp [hUdr] at h
      · simp only [hUdr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases hAr : decide (1 ≤ q.suite.logArity ∧ 1 ≤ q.suite.numQueries)
        · simp [hAr] at h
        · simp only [hAr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases hFl : checkZkmlSuiteProvenFloor .provenUdr q.suite
          · simp [hFl] at h
          · simp only [hFl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases hGr : decide (q.suite.grindBits ≤ q.statement.requiredPowBits)
            · simp [hGr] at h
            · simp only [hGr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases hChain : verifyZkmlChunkChainExec q.suite q.model q.statement ⟨q.chunks⟩ with
              | error _ => simp [hChain] at h
              | ok digests =>
                simp only [hChain] at h; cases hDig : decide (c.chunkDigests = digests.toList)
                · simp [hDig] at h
                · obtain ⟨hValid, hDigList⟩ := (verifyZkmlChunkChainExec_iff_spec q.suite q.model q.statement ⟨q.chunks⟩ digests).mp hChain
                  exact ⟨of_decide_eq_true hUdr, (checkZkmlSuiteProvenFloor_iff .provenUdr q.suite).mp hFl,
                    of_decide_eq_true hGr, hValid, (of_decide_eq_true hDig).trans hDigList⟩
    · simp [hCbr] at h
  · simp [hG] at h
theorem zkmlTurnMeaning_contraction_sound {grade : Nat} {q : ZkmlTurnQuery} {c : ZkmlTurnCert} (hOk : checkZkmlTurn grade q c = .ok)
    (i : Nat) (hi : i < q.chunks.length) (w : Mxfp4ChunkWitness) (hMatch : WitnessMatchesMxfp4Chunk w q.chunks[i]) :
    q.claimedRegime = .provenUdr ∧ ZkmlSuiteMeetsProvenFloor .provenUdr q.suite ∧ q.statement.pinnedNumQueries = some q.suite.numQueries ∧
    q.statement.suiteDigest = q.suite.digest ∧ q.chunks.length = q.model.layers.length ∧
    q.chunks[i].layerIdx.toNat = i ∧ ChunkMeetsPow q.suite q.statement.requiredPowBits q.chunks[i] ∧
    (∃ (rI rJ rB rK rJp : List Goldilocks) (finalVal : Goldilocks) (trPostFold : Transcript .instanceBound),
      runMxfp4SumcheckPhase q.suite q.chunks[i] = some (rI, rJ, rB, rK, rJp, finalVal, trPostFold) ∧
      (let setup := mxfp4SetupRaw q.suite q.chunks[i].iopProof.logI q.chunks[i].iopProof.logJ
         q.chunks[i].iopProof.logK q.chunks[i].iopProof.logB q.chunks[i].modelWeightsRoot
         q.chunks[i].policyFloorDigest q.chunks[i].suiteDigest q.chunks[i].chunkIdx q.chunks[i].layerIdx
         q.chunks[i].stateInCommit q.chunks[i].stateOutCommit q.chunks[i].qMerkleRoot
         q.chunks[i].sMerkleRoot q.chunks[i].iopProof.dClaim
       let rawQs := (squeezeRawQueries q.suite.numQueries (absorbMsg zkmlPowNonceLabel (Native.bytesOfList (u64ToBe8 q.chunks[i].iopProof.powNonce)) trPostFold)).1
       (q.model = w.model ∧ (∀ qm ∈ w.qInts, isValidE2m1Mantissa qm = true) ∧ (∀ sh ∈ w.sShifts, isValidMxfp4Shift sh = true) ∧
         w.dTbl = mxfp4ContractTable w.logI w.logJ w.logK w.logB w.xTbl w.qInts w.sShifts) ∨
       OuterMleRootHit w rI rJ ∨
       Mxfp4SumcheckRootHit w.logJ w.logK w.logB w.xTbl (w.qInts.map intToGoldilocks)
         (w.sShifts.map shiftToGoldilocks) rI rJ rB rK q.chunks[i].iopProof.sumcheckRounds setup.2.2 ∨
       AuthenticatedFoldWalkDeviation w q.chunks[i] rI rJ rB rK rJp rawQs ∨
       MissedInvalidWeightLeaf w rawQs ∨
       ZkmlCshakeCollision q.model w q.chunks[i])) := by
  obtain ⟨hUdr, hFl, _, hChain, _⟩ := provenZkmlJudge_sound hOk; obtain ⟨_, hLenM, hPin, hSDig, _, hElem, _, _⟩ := validZkmlChunkChain_invariants hChain
  obtain ⟨_, _, _, _, hlIdx, _, hSpecI⟩ := hElem i hi; obtain ⟨hPow, hSound⟩ := verifyMxfp4ChunkIop_sound ((verifyMxfp4ChunkIop_iff_spec ..).mpr hSpecI) hMatch
  exact ⟨hUdr, hFl, hPin, hSDig, hLenM, hlIdx, hPow, hSound⟩
theorem provenZkmlJudge_refuted {grade : Nat} {q : ZkmlTurnQuery} {c : ZkmlTurnCert} {k : ZkmlRefusalClause} {path : List Nat}
    (hRef : checkZkmlTurn grade q c = .refused k path) (hMarks : provenZkmlRefutes k = true) : ∀ c' : ZkmlTurnCert, ¬ ZkmlTurnMeaning q c' := by
  intro _ ⟨hRegUdr, hSuite, hGrind, hChain, _⟩; unfold checkZkmlTurn at hRef; cases hG : decide (grade < q.chunks.length)
  · simp only [hG, Bool.false_eq_true, ↓reduceIte] at hRef; have hNotCbr : decide (q.claimedRegime = .withdrawnCbr) = false := by rw [hRegUdr]; rfl
    have hFlTrue := (checkZkmlSuiteProvenFloor_iff .provenUdr q.suite).mpr hSuite
    have hArTrue : decide (1 ≤ q.suite.logArity ∧ 1 ≤ q.suite.numQueries) = true := decide_eq_true ⟨hSuite.2.1, hSuite.2.2.1⟩
    simp only [hNotCbr, decide_eq_true hRegUdr, hArTrue, hFlTrue, decide_eq_true hGrind, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
    have hExecOk : verifyZkmlChunkChainExec q.suite q.model q.statement ⟨q.chunks⟩ = .ok ⟨q.chunks.map zkmlChunkDigest⟩ :=
      (verifyZkmlChunkChainExec_iff_spec q.suite q.model q.statement ⟨q.chunks⟩ ⟨q.chunks.map zkmlChunkDigest⟩).mpr ⟨hChain, rfl⟩
    rw [hExecOk] at hRef; simp only at hRef; cases hDig : decide (c.chunkDigests = q.chunks.map zkmlChunkDigest)
    · simp only [hDig, Bool.false_eq_true, ↓reduceIte, Obend.Judge.Verdict.refused.injEq] at hRef; rcases hRef with ⟨rfl, _⟩; simp [provenZkmlRefutes] at hMarks
    · simp [hDig] at hRef
  · simp [hG] at hRef
theorem provenZkmlJudge_complete {q : ZkmlTurnQuery} (hFrag : ZkmlDecidableFragment q) (hEx : ∃ c, ZkmlTurnMeaning q c) : ∃ c r, checkZkmlTurn r q c = .ok := by
  obtain ⟨_, hRegUdr, hSuite, hGrind, hChain, _⟩ := hEx; have _hPos : 0 < q.chunks.length := List.length_pos_iff.mpr hFrag.2
  refine ⟨⟨q.chunks.map zkmlChunkDigest⟩, q.chunks.length, ?_⟩
  unfold checkZkmlTurn; have hFlTrue := (checkZkmlSuiteProvenFloor_iff .provenUdr q.suite).mpr hSuite
  have hArTrue : decide (1 ≤ q.suite.logArity ∧ 1 ≤ q.suite.numQueries) = true := decide_eq_true ⟨hSuite.2.1, hSuite.2.2.1⟩
  have hExecOk : verifyZkmlChunkChainExec q.suite q.model q.statement ⟨q.chunks⟩ = .ok ⟨q.chunks.map zkmlChunkDigest⟩ :=
    (verifyZkmlChunkChainExec_iff_spec q.suite q.model q.statement ⟨q.chunks⟩ ⟨q.chunks.map zkmlChunkDigest⟩).mpr ⟨hChain, rfl⟩
  rw [hRegUdr]; simp [Nat.lt_irrefl, hArTrue, hFlTrue, decide_eq_true hGrind, hExecOk]
theorem provenZkmlJudge_mono {r r' : Nat} {q : ZkmlTurnQuery} {c : ZkmlTurnCert} (hle : r ≤ r') (hDec : checkZkmlTurn r q c ≠ .uncovered) :
    checkZkmlTurn r' q c = checkZkmlTurn r q c := by
  unfold checkZkmlTurn at hDec ⊢; if hLt : r < q.chunks.length then simp [hLt] at hDec
  else have hNotLt' : ¬ (r' < q.chunks.length) := by omega
       simp only [decide_eq_false hLt, decide_eq_false hNotLt']
instance provenZkmlJudge : Obend.Judge ZkmlTurnQuery ZkmlTurnCert where
  Clause := ZkmlRefusalClause
  Meaning := ZkmlTurnMeaning
  check := checkZkmlTurn
  sound := provenZkmlJudge_sound
  refutes := provenZkmlRefutes
  refuted := provenZkmlJudge_refuted
  Fragment := ZkmlDecidableFragment
  complete := provenZkmlJudge_complete
  mono := provenZkmlJudge_mono
structure ZkmlSessionState where
  sessionWeightsRoot : ByteArray
  sessionPolicyFloorDigest : ByteArray
  sessionSuiteDigest : ByteArray
  sessionStateCommit : ByteArray
  totalVerifiedChunks : Nat
  deriving DecidableEq, Inhabited
inductive ValidZkmlSessionTrace : ZkmlSessionState → List (ZkmlTurnQuery × ZkmlTurnCert) → ZkmlSessionState → Prop where
  | nil (st : ZkmlSessionState) : ValidZkmlSessionTrace st [] st
  | cons {st finalSt : ZkmlSessionState} (q : ZkmlTurnQuery) (c : ZkmlTurnCert) (rest : List (ZkmlTurnQuery × ZkmlTurnCert)) :
      q.statement.modelWeightsRoot = st.sessionWeightsRoot → q.statement.policyFloorDigest = st.sessionPolicyFloorDigest →
      q.statement.suiteDigest = st.sessionSuiteDigest → q.statement.initialStateCommit = st.sessionStateCommit → ZkmlTurnMeaning q c →
      ValidZkmlSessionTrace { st with sessionStateCommit := q.statement.finalStateCommit, totalVerifiedChunks := st.totalVerifiedChunks + q.chunks.length } rest finalSt →
      ValidZkmlSessionTrace st ((q, c) :: rest) finalSt
def verifyZkmlSessionStep (grade : Nat) (st : ZkmlSessionState) (qc : ZkmlTurnQuery × ZkmlTurnCert) : Except (ZkmlRefusalClause × List Nat) ZkmlSessionState :=
  let (q, c) := qc
  if decide (q.statement.modelWeightsRoot ≠ st.sessionWeightsRoot) || decide (q.statement.policyFloorDigest ≠ st.sessionPolicyFloorDigest) ||
      decide (q.statement.suiteDigest ≠ st.sessionSuiteDigest) then .error (.weightRootDrift, [])
  else if decide (q.statement.initialStateCommit ≠ st.sessionStateCommit) then .error (.brokenRecurrentCarry, [])
  else match checkZkmlTurn grade q c with
    | .ok => .ok { st with sessionStateCommit := q.statement.finalStateCommit, totalVerifiedChunks := st.totalVerifiedChunks + q.chunks.length }
    | .refused k path => .error (k, path) | .uncovered => .error (.certDigestMismatch, [])
def verifyZkmlSessionTrace (grade : Nat) (st : ZkmlSessionState) : List (ZkmlTurnQuery × ZkmlTurnCert) → Except (ZkmlRefusalClause × List Nat) ZkmlSessionState
  | [] => .ok st
  | qc :: rest => match verifyZkmlSessionStep grade st qc with | .error err => .error err | .ok st' => verifyZkmlSessionTrace grade st' rest
theorem verifyZkmlSessionTrace_sound {grade : Nat} {init finalSt : ZkmlSessionState} {trace : List (ZkmlTurnQuery × ZkmlTurnCert)}
    (h : verifyZkmlSessionTrace grade init trace = .ok finalSt) : ValidZkmlSessionTrace init trace finalSt ∧ finalSt.sessionWeightsRoot = init.sessionWeightsRoot ∧
    finalSt.sessionPolicyFloorDigest = init.sessionPolicyFloorDigest ∧ finalSt.sessionSuiteDigest = init.sessionSuiteDigest ∧
    init.totalVerifiedChunks ≤ finalSt.totalVerifiedChunks := by
  induction trace generalizing init with
  | nil => simp only [verifyZkmlSessionTrace, Except.ok.injEq] at h; subst h; exact ⟨.nil init, rfl, rfl, rfl, Nat.le_refl _⟩
  | cons qc rest ih =>
    obtain ⟨q, c⟩ := qc; simp only [verifyZkmlSessionTrace, verifyZkmlSessionStep] at h
    cases hDr : (decide (q.statement.modelWeightsRoot ≠ init.sessionWeightsRoot) || decide (q.statement.policyFloorDigest ≠ init.sessionPolicyFloorDigest) ||
        decide (q.statement.suiteDigest ≠ init.sessionSuiteDigest))
    · simp only [hDr, Bool.false_eq_true, ↓reduceIte] at h; cases hIn : decide (q.statement.initialStateCommit ≠ init.sessionStateCommit)
      · simp only [hIn, Bool.false_eq_true, ↓reduceIte] at h; cases hChk : checkZkmlTurn grade q c with
        | refused _ _ => rw [hChk] at h; cases h
        | uncovered => rw [hChk] at h; cases h
        | ok =>
          simp only [hChk] at h; obtain ⟨hRest, hwEq, hpEq, hsEq, hMono⟩ := ih h; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not] at hDr hIn
          obtain ⟨⟨hw, hp⟩, hs⟩ := hDr; exact ⟨.cons q c rest hw hp hs hIn (provenZkmlJudge_sound hChk) hRest, hwEq, hpEq, hsEq, Nat.le_trans (Nat.le_add_right _ _) hMono⟩
      · rw [hIn] at h; simp at h
    · rw [hDr] at h; simp at h
/-! ## 4. Constructive Real-`MXFP4` Inhabitedness Witnesses (`0` Vacuous Premises) -/
def sampleIopBytes32 (b : UInt8) : ByteArray := ⟨(List.replicate 32 b).toArray⟩
theorem sampleIopBytes32_size (b : UInt8) : (sampleIopBytes32 b).size = 32 := by simp [sampleIopBytes32, ByteArray.size]
def sampleMxfp4Q0 : List Int := [1, -2, 3, 4, -6, 8, -12, 2]
def sampleMxfp4S0 : List Nat := [0, 1, 2, 1]
def sampleMxfp4Q1 : List Int := [2, -1, 4, -3, 6, -4, 1, 12]
def sampleMxfp4S1 : List Nat := [1, 0, 1, 2]
def sampleMxfp4Layer0 : Mxfp4LayerKey := ⟨1, 1, 1, 1, (mxfp4MantissaRoot32 sampleMxfp4Q0).bytes, (mxfp4ShiftRoot32 sampleMxfp4S0).bytes⟩
def sampleMxfp4Layer1 : Mxfp4LayerKey := ⟨1, 1, 1, 1, (mxfp4MantissaRoot32 sampleMxfp4Q1).bytes, (mxfp4ShiftRoot32 sampleMxfp4S1).bytes⟩
def sampleMxfp4Model : Mxfp4ModelManifest := ⟨[sampleMxfp4Layer0, sampleMxfp4Layer1]⟩
def sampleMxfp4X0 : List Goldilocks :=
  [Goldilocks.ofNat 3, Goldilocks.ofNat 5, Goldilocks.ofNat 2, Goldilocks.ofNat 7, Goldilocks.ofNat 4, Goldilocks.ofNat 1, Goldilocks.ofNat 6, Goldilocks.ofNat 2]
def sampleMxfp4Witness0 : Mxfp4ChunkWitness := buildHonestMxfp4Witness sampleMxfp4Model 0 1 1 1 1 sampleMxfp4X0 sampleMxfp4Q0 sampleMxfp4S0
theorem sampleMxfp4Witness0_valid : ValidMxfp4ChunkWitness sampleMxfp4Witness0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, rfl, rfl, rfl, rfl, by decide, by decide, rfl⟩
  show sampleMxfp4Model.valid = true; simp [sampleMxfp4Model, Mxfp4ModelManifest.valid, sampleMxfp4Layer0, sampleMxfp4Layer1, Mxfp4LayerKey.validDims, maxZkmlHypercubeVars, Digest32.size_eq]
theorem proveMxfp4ChunkIop_pow_zero (suite : ZkmlSuiteProfile) (pol suiteD : ByteArray) (hPol : pol.size = 32) (hSuiteD : suiteD.size = 32)
    (idx : UInt64) (w : Mxfp4ChunkWitness) (hw : ValidMxfp4ChunkWitness w) (hGrind0 : suite.grindBits = 0) :
    ChunkMeetsPow suite 0 (proveMxfp4ChunkIop suite pol suiteD idx w 0) ∧
    (match runMxfp4SumcheckPhase suite (proveMxfp4ChunkIop suite pol suiteD idx w 0) with
     | none => False | some (_, _, _, _, _, _, trPF) => checkChunkPow 0 (powCandidateState trPF 0) = true) := by
  obtain ⟨_, _, _, _, _, _, _, hPhase, _⟩ := runMxfp4SumcheckPhase_honest suite pol suiteD hPol hSuiteD idx w hw 0
  have hPowTrue : checkMxfp4ChunkPow suite 0 (proveMxfp4ChunkIop suite pol suiteD idx w 0) = true := by
    unfold checkMxfp4ChunkPow; have hPN : (proveMxfp4ChunkIop suite pol suiteD idx w 0).iopProof.powNonce = 0 := rfl
    have hZN0 : decide ((0 : Nat) = 0 → (proveMxfp4ChunkIop suite pol suiteD idx w 0).iopProof.powNonce = 0) = true := rfl
    rw [hGrind0, hZN0, hPhase]; dsimp only; rw [hPN, checkChunkPow_zero]; rfl
  exact ⟨(checkMxfp4ChunkPow_iff ..).mp hPowTrue, by rw [hPhase]; exact checkChunkPow_zero _⟩
theorem verifyMxfp4ChunkIop_inhabited : ∃ suite M powBits w c, ValidMxfp4ChunkWitness w ∧ WitnessMatchesMxfp4Chunk w c ∧ verifyMxfp4ChunkIop suite M powBits c = true := by
  let suite := wideLeafUdr148GoldilocksExt2; let c0 := proveMxfp4ChunkIop suite (sampleIopBytes32 0x22) suite.digest 0 sampleMxfp4Witness0 0
  obtain ⟨hwR, _, _, _, _, hSin, hSout, hQr, hSr, hLI, hLJ, hLK, hLB, _⟩ := proveMxfp4ChunkIop_headers suite (sampleIopBytes32 0x22) suite.digest 0 sampleMxfp4Witness0 0
  have hPow0 := (proveMxfp4ChunkIop_pow_zero suite (sampleIopBytes32 0x22) suite.digest (sampleIopBytes32_size _) suite.digest_size 0 sampleMxfp4Witness0 sampleMxfp4Witness0_valid rfl).2
  have hVer0 := proveMxfp4ChunkIop_complete sampleMxfp4Witness0_valid (sampleIopBytes32_size _) suite.digest_size ⟨by decide, by decide, by decide⟩ (by decide) (fun _ => rfl) hPow0
  have hDLen : sampleMxfp4Witness0.dTbl.length = 4 := mxfp4ContractTable_length 1 1 1 1 sampleMxfp4X0 sampleMxfp4Q0 sampleMxfp4S0 rfl rfl rfl
  exact ⟨suite, sampleMxfp4Model, 0, sampleMxfp4Witness0, c0, sampleMxfp4Witness0_valid,
    ⟨hLI.symm, hLJ.symm, hLK.symm, hLB.symm, rfl, rfl, rfl, hDLen, hwR.symm, hSin.symm, hSout.symm, hQr.symm, hSr.symm⟩, hVer0⟩
def sampleChainQ0 : List Int := [1, -2, 3, 4, -6, 8, -12, 2, 2, 1, -3, 6, 4, -1, 8, -4]
def sampleChainS0 : List Nat := [0, 1, 2, 1, 1, 0, 2, 3]
def sampleChainLayer0 : Mxfp4LayerKey := ⟨1, 2, 1, 1, (mxfp4MantissaRoot32 sampleChainQ0).bytes, (mxfp4ShiftRoot32 sampleChainS0).bytes⟩
def sampleChainLayer1 : Mxfp4LayerKey := ⟨1, 1, 1, 1, (mxfp4MantissaRoot32 sampleMxfp4Q1).bytes, (mxfp4ShiftRoot32 sampleMxfp4S1).bytes⟩
def sampleChainModel : Mxfp4ModelManifest := ⟨[sampleChainLayer0, sampleChainLayer1]⟩
def sampleChainWitness0 : Mxfp4ChunkWitness := buildHonestMxfp4Witness sampleChainModel 0 1 2 1 1 sampleMxfp4X0 sampleChainQ0 sampleChainS0
def sampleChainWitness1 : Mxfp4ChunkWitness := buildHonestMxfp4Witness sampleChainModel 1 1 1 1 1 sampleChainWitness0.dTbl sampleMxfp4Q1 sampleMxfp4S1
theorem sampleChainWitness0_valid : ValidMxfp4ChunkWitness sampleChainWitness0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, rfl, rfl, rfl, rfl, by decide, by decide, rfl⟩
  show sampleChainModel.valid = true; simp [sampleChainModel, Mxfp4ModelManifest.valid, sampleChainLayer0, sampleChainLayer1, Mxfp4LayerKey.validDims, maxZkmlHypercubeVars, Digest32.size_eq]
theorem sampleChainWitness1_valid : ValidMxfp4ChunkWitness sampleChainWitness1 := by
  have hD0Len : sampleChainWitness0.dTbl.length = 8 := mxfp4ContractTable_length 1 2 1 1 sampleMxfp4X0 sampleChainQ0 sampleChainS0 rfl rfl rfl
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, rfl, hD0Len, rfl, rfl, by decide, by decide, rfl⟩
  show sampleChainModel.valid = true; simp [sampleChainModel, Mxfp4ModelManifest.valid, sampleChainLayer0, sampleChainLayer1, Mxfp4LayerKey.validDims, maxZkmlHypercubeVars, Digest32.size_eq]
private def sampleChainSuite : ZkmlSuiteProfile := wideLeafUdr148GoldilocksExt2
private def sampleReceipt0 : ZkmlChunkReceipt := proveMxfp4ChunkIop sampleChainSuite (sampleIopBytes32 0x22) sampleChainSuite.digest 0 sampleChainWitness0 0
private def sampleReceipt1 : ZkmlChunkReceipt := proveMxfp4ChunkIop sampleChainSuite (sampleIopBytes32 0x22) sampleChainSuite.digest 1 sampleChainWitness1 0
private def sampleStreamStmt : ZkmlStreamStatement :=
  ⟨sampleChainModel.root, sampleIopBytes32 0x22, sampleChainSuite.digest, sampleReceipt0.stateInCommit, sampleReceipt1.stateOutCommit, 2, 0, some 148⟩
private theorem sampleStreamStmt_valid : ValidZkmlChunkChainSpec sampleChainSuite sampleChainModel sampleStreamStmt [sampleReceipt0, sampleReceipt1] := by
  obtain ⟨hPowSpec0, hPow0⟩ := proveMxfp4ChunkIop_pow_zero sampleChainSuite (sampleIopBytes32 0x22) sampleChainSuite.digest (sampleIopBytes32_size _) sampleChainSuite.digest_size 0 sampleChainWitness0 sampleChainWitness0_valid rfl
  obtain ⟨hPowSpec1, hPow1⟩ := proveMxfp4ChunkIop_pow_zero sampleChainSuite (sampleIopBytes32 0x22) sampleChainSuite.digest (sampleIopBytes32_size _) sampleChainSuite.digest_size 1 sampleChainWitness1 sampleChainWitness1_valid rfl
  have hSpec0 : ValidMxfp4ChunkIopSpec sampleChainSuite sampleChainModel 0 sampleReceipt0 :=
    (verifyMxfp4ChunkIop_iff_spec ..).mp (proveMxfp4ChunkIop_complete sampleChainWitness0_valid (sampleIopBytes32_size _) sampleChainSuite.digest_size ⟨by decide, by decide, by decide⟩ (by decide) (fun _ => rfl) hPow0)
  have hSpec1 : ValidMxfp4ChunkIopSpec sampleChainSuite sampleChainModel 0 sampleReceipt1 :=
    (verifyMxfp4ChunkIop_iff_spec ..).mp (proveMxfp4ChunkIop_complete sampleChainWitness1_valid (sampleIopBytes32_size _) sampleChainSuite.digest_size ⟨by decide, by decide, by decide⟩ (by decide) (fun _ => rfl) hPow1)
  have hWf0 := proveMxfp4ChunkIop_wellFormed32 sampleChainSuite (sampleIopBytes32 0x22) sampleChainSuite.digest (sampleIopBytes32_size _) sampleChainSuite.digest_size 0 sampleChainWitness0 0
  have hWf1 := proveMxfp4ChunkIop_wellFormed32 sampleChainSuite (sampleIopBytes32 0x22) sampleChainSuite.digest (sampleIopBytes32_size _) sampleChainSuite.digest_size 1 sampleChainWitness1 0
  obtain ⟨hw0, hp0, hs0, hi0, hli0, _, hout0, _⟩ := proveMxfp4ChunkIop_headers sampleChainSuite (sampleIopBytes32 0x22) sampleChainSuite.digest 0 sampleChainWitness0 0
  obtain ⟨hw1, hp1, hs1, hi1, hli1, hin1, _⟩ := proveMxfp4ChunkIop_headers sampleChainSuite (sampleIopBytes32 0x22) sampleChainSuite.digest 1 sampleChainWitness1 0
  have hCarry01 : sampleReceipt0.stateOutCommit = sampleReceipt1.stateInCommit := by
    change (proveMxfp4ChunkIop _ _ _ _ _ _).stateOutCommit = (proveMxfp4ChunkIop _ _ _ _ _ _).stateInCommit; rw [hout0, hin1]; rfl
  have hStep1 : LayerCarrySteps sampleChainSuite sampleChainModel sampleChainModel.root (sampleIopBytes32 0x22) sampleChainSuite.digest 0 1
      sampleReceipt1.stateInCommit [sampleReceipt1] sampleReceipt1.stateOutCommit := .cons sampleReceipt1 [] hWf1 hw1 hp1 hs1
      (by change (proveMxfp4ChunkIop _ _ _ _ _ _).chunkIdx.toNat = 1; rw [hi1]; rfl) (by change (proveMxfp4ChunkIop _ _ _ _ _ _).layerIdx.toNat = 1; rw [hli1]; rfl)
      hPowSpec1 hSpec1 (.nil 2 sampleReceipt1.stateOutCommit)
  rw [← hCarry01] at hStep1; have hTwoLt64 : 2 < 2 ^ 64 := Nat.lt_trans (by decide : 2 < 2 ^ 2) (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 2 < 64))
  exact ⟨⟨sampleChainModel.root_size, sampleIopBytes32_size _, sampleChainSuite.digest_size, hWf0.2.2.2.1, hWf1.2.2.2.2.1, by decide, hTwoLt64, by decide⟩,
    rfl, rfl, rfl, rfl, rfl, .cons sampleReceipt0 [sampleReceipt1] hWf0 hw0 hp0 hs0 (by change (proveMxfp4ChunkIop _ _ _ _ _ _).chunkIdx.toNat = 0; rw [hi0]; rfl)
      (by change (proveMxfp4ChunkIop _ _ _ _ _ _).layerIdx.toNat = 0; rw [hli0]; rfl) hPowSpec0 hSpec0 hStep1⟩
theorem provenZkmlJudge_inhabited : ∃ q c, ZkmlDecidableFragment q ∧ ZkmlTurnMeaning q c ∧ provenZkmlJudge.check 2 q c = .ok := by
  let q : ZkmlTurnQuery := ⟨.provenUdr, sampleChainSuite, sampleChainModel, sampleStreamStmt, [sampleReceipt0, sampleReceipt1]⟩
  let c : ZkmlTurnCert := ⟨[zkmlChunkDigest sampleReceipt0, zkmlChunkDigest sampleReceipt1]⟩
  have hFl : checkZkmlSuiteProvenFloor .provenUdr sampleChainSuite = true := by decide
  have hExec : verifyZkmlChunkChainExec q.suite q.model q.statement ⟨q.chunks⟩ = .ok ⟨c.chunkDigests⟩ :=
    (verifyZkmlChunkChainExec_iff_spec q.suite q.model q.statement ⟨q.chunks⟩ ⟨c.chunkDigests⟩).mpr ⟨sampleStreamStmt_valid, rfl⟩
  have hOk2 : checkZkmlTurn 2 q c = .ok := by
    unfold checkZkmlTurn; rw [hExec]; have hLen : q.chunks.length = 2 := rfl; have hSuiteEq : q.suite = sampleChainSuite := rfl
    have hRegEq : q.claimedRegime = .provenUdr := rfl; have hReqPow : q.statement.requiredPowBits = 0 := rfl; rw [hLen, hSuiteEq, hRegEq, hReqPow, hFl]
    simp [sampleChainSuite, wideLeafUdr148GoldilocksExt2]
  exact ⟨q, c, ⟨sampleStreamStmt_valid.1, List.cons_ne_nil _ _⟩, ⟨rfl, (checkZkmlSuiteProvenFloor_iff .provenUdr sampleChainSuite).mp hFl, by decide, sampleStreamStmt_valid, rfl⟩, hOk2⟩
theorem verifyZkmlSessionTrace_inhabited : ∃ init trace finalSt, 0 < trace.length ∧ verifyZkmlSessionTrace 2 init trace = .ok finalSt ∧
      ValidZkmlSessionTrace init trace finalSt := by
  obtain ⟨q, c, _, _, hOk⟩ := provenZkmlJudge_inhabited
  let init : ZkmlSessionState := ⟨q.statement.modelWeightsRoot, q.statement.policyFloorDigest, q.statement.suiteDigest, q.statement.initialStateCommit, 0⟩
  have hChk : checkZkmlTurn 2 q c = .ok := hOk
  have hStep : verifyZkmlSessionTrace 2 init [(q, c)] = .ok { init with sessionStateCommit := q.statement.finalStateCommit, totalVerifiedChunks := q.chunks.length } := by
    simp [verifyZkmlSessionTrace, verifyZkmlSessionStep, init, hChk]
  exact ⟨init, [(q, c)], _, Nat.zero_lt_succ 0, hStep, (verifyZkmlSessionTrace_sound hStep).1⟩
end Obend.SymbolicZk.ProvenZkmlGate
end
