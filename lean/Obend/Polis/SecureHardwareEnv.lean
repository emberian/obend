module
/- # Obend.Polis.SecureHardwareEnv — Multi-Turn Sovereign SHE ("Anti-Vaz") Ceremony
1. Grounded `ZkmlSuiteArtifact` + `CandidateComputation` `UD-100` receipt gate (`1 ≤ logArity`,
   pinned `observedNumQueries = pinnedNumQueries`, post-commit PoW grinding, refusing withdrawn `CBR`,
   supporting both `(lb=6, q=86, pow=16)` and wide-leaf `(lb=2, q=148, pow=0)`);
2. Sampled bit-exact `s8 × E2M1` (`MXFP4`) integer recompute audit (`ExactRecomputeAudit` with
   commit-before-coin Fiat–Shamir, `exactIntDot_reverse`, `lying_caught_at_opened_round`,
   `tolerance_checker_admits_steered_argmax_while_exact_refuses`, `verifyCandidateComputation_sound`);
3. Full-width 256-bit Post-Quantum `PqHashSignatures` (`cshake256Suite`, `TSW`/`WOTS+C` with
   `w=4, ell1≥128` or `w=16, ell1≥64` + stateful `XMSS` + stateless `leanSPHINCS` `≥100`-bit `FORS`)
   quorums (`she_ceremony_pq_quorum_unforgeable` via `0 Classical` `extractPqHashForgery`);
4. Anti-Vaz non-regressive floors, multi-turn trace safety, `seL4` private-frame copy-before-verify
   (treating external sensors/displays strictly as untrusted I/O), wire binding, & `sheCeremonyJudge`. -/
public import Obend.Judge.Class
public import Obend.Judge.Genealogy
public import Obend.OS.Sel4MicrokitKernel
public import Obend.Polis.SandboxDomainTags
public import Obend.Crypto.PqHashSignatures
import all Obend.Crypto.PqHashSignatures
public section
namespace Obend.Polis.SecureHardwareEnv
open Obend.Apps.ZkNtt Obend.Crypto Obend.Crypto.PqHashSignatures
open Obend.Digest.Cshake256 Obend.Digest.HashBytes Obend.Judge.Computational
open Obend.OS.Sel4MicrokitKernel Obend.Polis.SandboxDomainTags
set_option autoImplicit false
/-! ## 1. Sovereign Floors, Grounded `ZkmlSuiteArtifact` (`UD-100`) & Bit-Exact `fpaudit` Integer Recompute -/
inductive SheFloor where
  | sensorRoiRedaction (minRedactedRois : Nat) | consentBandNonOcclusion (minBandHeightPx : Nat)
  | zkmlProvenSoundnessMilliBits (minMilliBits : Nat) | physicalProximityMaxTicks (maxTicks : Nat)
  | e2eeTeeChannelBound (minAttestedGpus : Nat) | operatorLocalRevert (maxRevertSteps : Nat)
  deriving DecidableEq, Repr
def SheFloor.isBedrock : SheFloor → Bool | .operatorLocalRevert _ => true | _ => false
def SheFloor.wellFormed : SheFloor → Bool
  | .sensorRoiRedaction _ | .e2eeTeeChannelBound _ => true
  | .consentBandNonOcclusion px => decide (0 < px) | .zkmlProvenSoundnessMilliBits mb => decide (100000 ≤ mb)
  | .physicalProximityMaxTicks t => decide (0 < t) | .operatorLocalRevert r => decide (0 < r)
inductive ZkmlSoundnessRegime where
  | uniqueDecodingUdr | johnsonBoundJbr | withdrawnCapacityBoundCbr
  deriving DecidableEq, Repr
def ZkmlSoundnessRegime.tagByte : ZkmlSoundnessRegime → UInt8
  | .uniqueDecodingUdr => 0x01 | .johnsonBoundJbr => 0x02 | .withdrawnCapacityBoundCbr => 0x03
theorem ZkmlSoundnessRegime.tagByte_injective {r₁ r₂ : ZkmlSoundnessRegime} (h : r₁.tagByte = r₂.tagByte) : r₁ = r₂ := by
  cases r₁ <;> cases r₂ <;> simp only [ZkmlSoundnessRegime.tagByte] at h <;> first | rfl | exact absurd h (by decide)
def udrPerQueryMilliBits : Nat → Nat | 0 => 0 | 1 => 415 | 2 => 678 | 3 => 830 | 4 => 912 | 5 => 955 | 6 => 977 | 7 => 988 | _ + 8 => 994
def jbrPerQueryMilliBits (logBlowup : Nat) : Nat := logBlowup * 500
abbrev encodeSheFields : List (List UInt8) → List UInt8 := encodeSandboxFields
theorem encodeSheFields_injective {fs₁ fs₂ : List (List UInt8)} (h : encodeSheFields fs₁ = encodeSheFields fs₂) : fs₁ = fs₂ := encodeSandboxFields_injective h
def encodeNatList (xs : List Nat) : List UInt8 := encodeSheFields (xs.map leb128)
theorem encodeNatList_injective {xs₁ xs₂ : List Nat} (h : encodeNatList xs₁ = encodeNatList xs₂) : xs₁ = xs₂ := (List.map_inj_right fun _ _ => leb128_injective).mp (encodeSheFields_injective h)
def zigzagEncode : Int → Nat | Int.ofNat n => 2 * n | Int.negSucc n => 2 * n + 1
theorem zigzagEncode_injective {z₁ z₂ : Int} (h : zigzagEncode z₁ = zigzagEncode z₂) : z₁ = z₂ := by
  cases z₁ with
  | ofNat a => cases z₂ with
    | ofNat b => simp only [zigzagEncode] at h; congr; omega
    | negSucc b => simp only [zigzagEncode] at h; omega
  | negSucc a => cases z₂ with
    | ofNat b => simp only [zigzagEncode] at h; omega
    | negSucc b => simp only [zigzagEncode] at h; congr; omega
def encodeInt (z : Int) : List UInt8 := leb128 (zigzagEncode z)
theorem encodeInt_injective {z₁ z₂ : Int} (h : encodeInt z₁ = encodeInt z₂) : z₁ = z₂ := zigzagEncode_injective (leb128_injective h)
def encodeIntList (xs : List Int) : List UInt8 := encodeSheFields (xs.map encodeInt)
theorem encodeIntList_injective {xs₁ xs₂ : List Int} (h : encodeIntList xs₁ = encodeIntList xs₂) : xs₁ = xs₂ := (List.map_inj_right fun _ _ => encodeInt_injective).mp (encodeSheFields_injective h)
def encodeIntMatrix (rows : List (List Int)) : List UInt8 := encodeSheFields (rows.map encodeIntList)
theorem encodeIntMatrix_injective {m₁ m₂ : List (List Int)} (h : encodeIntMatrix m₁ = encodeIntMatrix m₂) : m₁ = m₂ := (List.map_inj_right fun _ _ => encodeIntList_injective).mp (encodeSheFields_injective h)
def encodeByteListList (xs : List (List UInt8)) : List UInt8 := encodeSheFields xs
theorem encodeByteListList_injective {xs₁ xs₂ : List (List UInt8)} (h : encodeByteListList xs₁ = encodeByteListList xs₂) : xs₁ = xs₂ := encodeSheFields_injective h
private theorem uint64_eq_of_toNat_eq {a b : UInt64} (h : a.toNat = b.toNat) : a = b := by
  cases a with | ofBitVec av => cases b with | ofBitVec bv => exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq h)
private theorem byteArray_eq_of_toList_eq {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b; exact congrArg ByteArray.mk (Array.ext' h)
def le64At (b : ByteArray) (off : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc i => acc ||| ((b.get! (off + i)).toUInt64 <<< UInt64.ofNat (8 * i))) 0
def hasLowZeroBits (b : ByteArray) (bits : Nat) : Bool :=
  if bits == 0 then true else if b.size < 8 then false else (le64At b 0 &&& ((1 <<< UInt64.ofNat bits) - 1)) == 0
private theorem hasLowZeroBits_zero (b : ByteArray) : hasLowZeroBits b 0 = true := rfl
/-- Grounded `ZkmlSuiteArtifact` (`CROSS_REPO_CONTRACTS.md` §2 & `VERDICTS.md` `UD-100`). -/
structure ZkmlSuiteArtifact where
  suiteId : List UInt8
  regime : ZkmlSoundnessRegime
  logBlowup : Nat
  logArity : Nat
  pinnedNumQueries : Nat
  powBits : Nat
  extFieldBits : Nat
  deriving DecidableEq
def encodeZkmlSuiteArtifact (s : ZkmlSuiteArtifact) : List UInt8 :=
  encodeSheFields [s.suiteId, [s.regime.tagByte], leb128 s.logBlowup, leb128 s.logArity, leb128 s.pinnedNumQueries, leb128 s.powBits, leb128 s.extFieldBits]
theorem encodeZkmlSuiteArtifact_injective {s₁ s₂ : ZkmlSuiteArtifact} (h : encodeZkmlSuiteArtifact s₁ = encodeZkmlSuiteArtifact s₂) : s₁ = s₂ := by
  have hf := encodeSheFields_injective h; simp only [List.cons.injEq, and_true] at hf; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
  cases s₁; cases s₂; simp only [ZkmlSuiteArtifact.mk.injEq]
  exact ⟨h1, ZkmlSoundnessRegime.tagByte_injective h2, leb128_injective h3, leb128_injective h4, leb128_injective h5, leb128_injective h6, leb128_injective h7⟩
def suiteArtifactDigest (s : ZkmlSuiteArtifact) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.ZKML_SUITE/v1") (encodeZkmlSuiteArtifact s)
theorem suiteArtifactDigest_size (s : ZkmlSuiteArtifact) : (suiteArtifactDigest s).size = 32 := cshake32ByteArray_size _ _
theorem suiteArtifactDigest_binds {s₁ s₂ : ZkmlSuiteArtifact} (h : suiteArtifactDigest s₁ = suiteArtifactDigest s₂) :
    s₁ = s₂ ∨ CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.ZKML_SUITE/v1")) (fun x => x = encodeZkmlSuiteArtifact s₁ ∨ x = encodeZkmlSuiteArtifact s₂) := by
  cases extractCshake32 (asciiTagBytes "OBEND.SHE.ZKML_SUITE/v1") (encodeZkmlSuiteArtifact s₁) (encodeZkmlSuiteArtifact s₂) h with
  | inl hp => exact .inl (encodeZkmlSuiteArtifact_injective hp.down) | inr hc => exact .inr hc.down
def suiteProvenMilliBits (s : ZkmlSuiteArtifact) : Nat :=
  if s.logBlowup == 0 || s.logArity == 0 || s.pinnedNumQueries == 0 then 0 else
    let cap := Nat.min (s.extFieldBits * 1000) 256000; let grindMbit := Nat.min s.powBits 24 * 1000
    match s.regime with
    | .withdrawnCapacityBoundCbr => 0
    | .uniqueDecodingUdr => Nat.min (s.pinnedNumQueries * udrPerQueryMilliBits s.logBlowup + grindMbit) cap
    | .johnsonBoundJbr => Nat.min (s.pinnedNumQueries * jbrPerQueryMilliBits s.logBlowup + grindMbit) cap
def legacyWithdrawnCbrMilliBits (s : ZkmlSuiteArtifact) : Nat := s.logBlowup * s.pinnedNumQueries * 1000 + s.powBits * 1000
theorem udr_strictly_below_legacy_cbr (s : ZkmlSuiteArtifact) (hlb : 0 < s.logBlowup) (hq : 0 < s.pinnedNumQueries) :
    suiteProvenMilliBits { s with regime := .uniqueDecodingUdr } < legacyWithdrawnCbrMilliBits s := by
  have hPerQ : udrPerQueryMilliBits s.logBlowup < s.logBlowup * 1000 := by
    match s.logBlowup, hlb with | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [udrPerQueryMilliBits] | k + 8, _ => simp [udrPerQueryMilliBits]; omega
  have hMul := Nat.mul_lt_mul_of_pos_left hPerQ hq; rw [← Nat.mul_assoc, Nat.mul_comm s.pinnedNumQueries s.logBlowup] at hMul
  have hSum := Nat.add_lt_add_of_lt_of_le hMul (Nat.mul_le_mul_right 1000 (Nat.min_le_left s.powBits 24))
  have hPos : 0 < s.logBlowup * s.pinnedNumQueries * 1000 + s.powBits * 1000 := Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos hlb hq) (by decide)) (Nat.le_add_right _ _)
  unfold suiteProvenMilliBits legacyWithdrawnCbrMilliBits; dsimp only; split
  · exact hPos
  · exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hSum
def checkSuiteArtifact (s : ZkmlSuiteArtifact) : Bool :=
  !s.suiteId.isEmpty && s.regime != .withdrawnCapacityBoundCbr && decide (0 < s.logBlowup ∧ s.logBlowup ≤ 8 ∧ 1 ≤ s.logArity ∧ 0 < s.pinnedNumQueries ∧ s.powBits ≤ 24 ∧ 100000 ≤ suiteProvenMilliBits s)
private def asciiBytes (s : String) : List UInt8 := s.toList.map fun c => UInt8.ofNat c.toNat
/-- Canonical `UD-100` small/recursed profile `(lb=6, q=86, pow=16)` (`100.022` proven UDR bits). -/
def canonicalUd100SmallSuite : ZkmlSuiteArtifact :=
  { suiteId := asciiBytes "obend.einsu.goldilocks-ext2.mxfp4.cshake256.ud100.lb6.v1", regime := .uniqueDecodingUdr, logBlowup := 6, logArity := 1, pinnedNumQueries := 86, powBits := 16, extFieldBits := 128 }
/-- Canonical `UD-100` wide-leaf profile `(lb=2, q=148, pow=0)` (`100.344` proven UDR bits). -/
def canonicalUd100WideLeafSuite : ZkmlSuiteArtifact :=
  { suiteId := asciiBytes "obend.einsu.goldilocks-ext2.mxfp4.cshake256.ud100.lb2.v1", regime := .uniqueDecodingUdr, logBlowup := 2, logArity := 1, pinnedNumQueries := 148, powBits := 0, extFieldBits := 128 }
/-- Exact `s8` activation bounds and signed `E2M1` (`MXFP4`) weight mantissa domain (`VERDICTS.md` §9). -/
def isS8 (x : Int) : Bool := decide (-128 ≤ x ∧ x ≤ 127)
def e2m1Mantissas : List Int := [-12, -8, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 6, 8, 12]
def isE2m1Mantissa (q : Int) : Bool := e2m1Mantissas.contains q
def exactIntDot : List Int → List Int → Int
  | x :: xs, w :: ws => x * w + exactIntDot xs ws
  | _, _ => 0
private theorem exactIntDot_append : ∀ {xs₁ xs₂ ws₁ ws₂ : List Int}, xs₁.length = ws₁.length →
    exactIntDot (xs₁ ++ xs₂) (ws₁ ++ ws₂) = exactIntDot xs₁ ws₁ + exactIntDot xs₂ ws₂
  | [], _, [], _, _ => by simp [exactIntDot]
  | x :: xs₁, xs₂, w :: ws₁, ws₂, h => by
    simp only [List.cons_append, exactIntDot, exactIntDot_append (Nat.succ.inj h), Int.add_assoc]
/-- **Exact Integer Dot-Product Summation-Order Invariance (`exactIntDot_reverse`)**:
    Unlike float32 kernels, exact integer matmul sums are identical across CPU/GPU/TPU reduction orders. -/
theorem exactIntDot_reverse : ∀ (xs ws : List Int), xs.length = ws.length → exactIntDot xs.reverse ws.reverse = exactIntDot xs ws
  | [], [], _ => rfl
  | x :: xs, w :: ws, h => by
    have hLen : xs.length = ws.length := Nat.succ.inj h
    have hRevLen : xs.reverse.length = ws.reverse.length := by simp [hLen]
    simp only [List.reverse_cons, exactIntDot_append hRevLen, exactIntDot_reverse xs ws hLen, exactIntDot, Int.add_zero]
    exact Int.add_comm _ _
def exactMxfp4RowLogit (xs ws : List Int) (shift : Nat) : Int := exactIntDot xs ws * Int.ofNat (2 ^ shift)
def exactMxfp4Logits (xs : List Int) : List (List Int) → List Nat → List Int
  | wRow :: wRows, sh :: shs => exactMxfp4RowLogit xs wRow sh :: exactMxfp4Logits xs wRows shs
  | _, _ => []
def argmaxIdxAux (bestIdx : Nat) (bestVal : Int) (curIdx : Nat) : List Int → Nat
  | [] => bestIdx
  | v :: vs => if bestVal < v then argmaxIdxAux curIdx v (curIdx + 1) vs else argmaxIdxAux bestIdx bestVal (curIdx + 1) vs
def argmaxIdx : List Int → Nat | [] => 0 | v :: vs => argmaxIdxAux 0 v 1 vs
def toleranceLogitCheck (τ : Nat) : List Int → List Int → Bool
  | [], [] => true
  | a :: as, b :: bs => decide ((a - b).natAbs ≤ τ) && toleranceLogitCheck τ as bs
  | _, _ => false
/-- **Exact Recompute vs Tolerance-Checker Separation (`tolerance_checker_admits_steered_argmax_while_exact_refuses`)**:
    For ANY positive logit tolerance `τ > 0`, a tolerance checker accepts steered logits whose `argmaxIdx`
    flips (`0 ≠ 1`), whereas bit-exact integer recompute (`actual == claimed`) unconditionally refuses! -/
theorem tolerance_checker_admits_steered_argmax_while_exact_refuses (τ : Nat) (hPos : 0 < τ) :
    ∃ actual claimed : List Int, toleranceLogitCheck τ actual claimed = true ∧ argmaxIdx actual ≠ argmaxIdx claimed ∧ (actual == claimed) = false := by
  refine ⟨[Int.ofNat τ, Int.ofNat τ - 1], [Int.ofNat τ - 1, Int.ofNat τ], ?_, ?_, ?_⟩
  · have h1 : (Int.ofNat τ - (Int.ofNat τ - 1)).natAbs ≤ τ := by omega
    have h2 : (Int.ofNat τ - 1 - Int.ofNat τ).natAbs ≤ τ := by omega
    simp only [toleranceLogitCheck, h1, h2, decide_true, Bool.and_true]
  · have hNot : ¬ (Int.ofNat τ < Int.ofNat τ - 1) := by omega
    have hLt : Int.ofNat τ - 1 < Int.ofNat τ := by omega
    simp only [argmaxIdx, argmaxIdxAux, hNot, hLt, ↓reduceIte]; decide
  · have hNe : Int.ofNat τ ≠ Int.ofNat τ - 1 := by omega
    cases hc : ([Int.ofNat τ, Int.ofNat τ - 1] == [Int.ofNat τ - 1, Int.ofNat τ]) with
    | false => rfl
    | true => exfalso; have hEq := beq_iff_eq.mp hc; exact hNe (List.cons.inj hEq).1
structure CommittedRecomputeRound where
  roundIdx : Nat
  inputRoot : ByteArray
  claimedLogits : List Int
  claimedArgmax : Nat
  deriving DecidableEq
structure ExactRecomputeAudit where
  committedRounds : List CommittedRecomputeRound
  commitRoot : ByteArray
  openedRoundIdx : Nat
  openedInputs : List Int
  openedWeightRows : List (List Int)
  openedBlockShifts : List Nat
  deriving DecidableEq
/-- Grounded `CandidateComputation` (`CROSS_REPO_CONTRACTS.md` §2): native code NEVER returns an acceptance bit! -/
structure CandidateComputation where
  suite : ZkmlSuiteArtifact
  statementDigest : ByteArray
  modelWeightsRoot : ByteArray
  inputRoot : ByteArray
  outputRoot : ByteArray
  boundFloorsDigest : ByteArray
  actionPayloadDigest : ByteArray
  observedNumQueries : Nat
  proofTranscriptDigest : ByteArray
  powNonce : UInt64
  recomputeAudit : ExactRecomputeAudit
  deriving DecidableEq
def candidateStatementDigest (suite : ZkmlSuiteArtifact) (modelWeightsRoot inputRoot commitRoot outputRoot : ByteArray) (numRounds : Nat) (boundFloorsDigest actionPayloadDigest : ByteArray) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.ZKML_STMT/v1") (encodeSheFields [(suiteArtifactDigest suite).data.toList, modelWeightsRoot.data.toList, inputRoot.data.toList, commitRoot.data.toList, outputRoot.data.toList, leb128 numRounds, boundFloorsDigest.data.toList, actionPayloadDigest.data.toList])
private theorem candidateStatementDigest_size (s : ZkmlSuiteArtifact) (w i c o : ByteArray) (n : Nat) (f a : ByteArray) : (candidateStatementDigest s w i c o n f a).size = 32 := cshake32ByteArray_size _ _
def candidatePowHash (statementDigest proofTranscriptDigest : ByteArray) (powNonce : UInt64) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.ZKML_POW/v1") (encodeSheFields [statementDigest.data.toList, proofTranscriptDigest.data.toList, leb128 powNonce.toNat])
def fpauditWeightsRoot (weightRows : List (List Int)) (blockShifts : List Nat) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.FPAUDIT_WEIGHTS/v1") (encodeSheFields [encodeIntMatrix weightRows, encodeNatList blockShifts])
private theorem fpauditWeightsRoot_size (ws : List (List Int)) (sh : List Nat) : (fpauditWeightsRoot ws sh).size = 32 := cshake32ByteArray_size _ _
def fpauditInputRoot (sensorSealDigest : ByteArray) (xs : List Int) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.FPAUDIT_INPUT/v1") (encodeSheFields [sensorSealDigest.data.toList, encodeIntList xs])
private theorem fpauditInputRoot_size (s : ByteArray) (xs : List Int) : (fpauditInputRoot s xs).size = 32 := cshake32ByteArray_size _ _
def fpauditRoundHash (r : CommittedRecomputeRound) : List UInt8 :=
  (cshake32ByteArray (asciiTagBytes "OBEND.SHE.FPAUDIT_ROUND/v1") (encodeSheFields [leb128 r.roundIdx, r.inputRoot.data.toList, encodeIntList r.claimedLogits, leb128 r.claimedArgmax])).data.toList
def fpauditCommitRoot (rounds : List CommittedRecomputeRound) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.FPAUDIT_COMMIT/v1") (encodeSheFields (rounds.map fpauditRoundHash))
private theorem fpauditCommitRoot_size (rs : List CommittedRecomputeRound) : (fpauditCommitRoot rs).size = 32 := cshake32ByteArray_size _ _
def fpauditOutputRoot (rounds : List CommittedRecomputeRound) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.FPAUDIT_OUT/v1") (encodeNatList (rounds.map CommittedRecomputeRound.claimedArgmax))
private theorem fpauditOutputRoot_size (rs : List CommittedRecomputeRound) : (fpauditOutputRoot rs).size = 32 := cshake32ByteArray_size _ _
def fpauditOpenedRoundIdx (statementDigest commitRoot outputRoot proofTranscriptDigest : ByteArray) (powNonce : UInt64) (numRounds : Nat) : Nat :=
  if numRounds == 0 then 0 else (le64At (cshake32ByteArray (asciiTagBytes "OBEND.SHE.FPAUDIT_COIN/v1") (encodeSheFields [statementDigest.data.toList, commitRoot.data.toList, outputRoot.data.toList, proofTranscriptDigest.data.toList, leb128 powNonce.toNat])) 0).toNat % numRounds
def verifyExactRecomputeAudit (c : CandidateComputation) : Bool :=
  let a := c.recomputeAudit
  if a.committedRounds.isEmpty || a.commitRoot.size != 32 then false
  else if !a.committedRounds.all (fun r => r.inputRoot.size == 32 && !r.claimedLogits.isEmpty && r.claimedArgmax == argmaxIdx r.claimedLogits) then false
  else if !(List.range a.committedRounds.length).all (fun i => match a.committedRounds[i]? with | some r => r.roundIdx == i | none => false) then false
  else if a.commitRoot != fpauditCommitRoot a.committedRounds || c.outputRoot != fpauditOutputRoot a.committedRounds then false
  else if a.openedRoundIdx != fpauditOpenedRoundIdx c.statementDigest a.commitRoot c.outputRoot c.proofTranscriptDigest c.powNonce a.committedRounds.length then false
  else match a.committedRounds[a.openedRoundIdx]? with
    | none => false
    | some opened =>
      if a.openedInputs.isEmpty || !a.openedInputs.all isS8 || a.openedWeightRows.isEmpty || a.openedWeightRows.length != a.openedBlockShifts.length then false
      else if !a.openedWeightRows.all (fun row => row.length == a.openedInputs.length && row.all isE2m1Mantissa) || !a.openedBlockShifts.all (fun sh => decide (sh ≤ 8)) then false
      else if c.modelWeightsRoot != fpauditWeightsRoot a.openedWeightRows a.openedBlockShifts || opened.inputRoot != fpauditInputRoot c.inputRoot a.openedInputs then false
      else let recomputed := exactMxfp4Logits a.openedInputs a.openedWeightRows a.openedBlockShifts
        recomputed == opened.claimedLogits && argmaxIdx recomputed == opened.claimedArgmax
@[expose] def verifyCandidateComputation (c : CandidateComputation) : Bool :=
  checkSuiteArtifact c.suite &&
  decide (c.statementDigest.size = 32 ∧ c.modelWeightsRoot.size = 32 ∧ c.inputRoot.size = 32 ∧ c.outputRoot.size = 32 ∧ c.boundFloorsDigest.size = 32 ∧ c.actionPayloadDigest.size = 32 ∧ c.proofTranscriptDigest.size = 32) &&
  c.observedNumQueries == c.suite.pinnedNumQueries &&
  c.statementDigest == candidateStatementDigest c.suite c.modelWeightsRoot c.inputRoot c.recomputeAudit.commitRoot c.outputRoot c.recomputeAudit.committedRounds.length c.boundFloorsDigest c.actionPayloadDigest &&
  decide (c.suite.powBits = 0 → c.powNonce = 0) &&
  hasLowZeroBits (candidatePowHash c.statementDigest c.proofTranscriptDigest c.powNonce) (Nat.min c.suite.powBits 24) &&
  verifyExactRecomputeAudit c
@[expose] def provenZkmlMilliBits (c : CandidateComputation) : Nat :=
  if verifyCandidateComputation c then suiteProvenMilliBits c.suite else 0
structure ValidExactRecomputeWitness (c : CandidateComputation) : Prop where
  nonEmptyRounds : 0 < c.recomputeAudit.committedRounds.length
  allRoundsArgmaxConsistent : ∀ r ∈ c.recomputeAudit.committedRounds, r.inputRoot.size = 32 ∧ r.claimedLogits ≠ [] ∧ r.claimedArgmax = argmaxIdx r.claimedLogits
  commitRootBound : c.recomputeAudit.commitRoot = fpauditCommitRoot c.recomputeAudit.committedRounds
  outputRootBound : c.outputRoot = fpauditOutputRoot c.recomputeAudit.committedRounds
  commitBeforeCoin : c.recomputeAudit.openedRoundIdx = fpauditOpenedRoundIdx c.statementDigest c.recomputeAudit.commitRoot c.outputRoot c.proofTranscriptDigest c.powNonce c.recomputeAudit.committedRounds.length
  inputsS8 : 0 < c.recomputeAudit.openedInputs.length ∧ ∀ x ∈ c.recomputeAudit.openedInputs, isS8 x = true
  weightsE2m1 : 0 < c.recomputeAudit.openedWeightRows.length ∧ c.recomputeAudit.openedWeightRows.length = c.recomputeAudit.openedBlockShifts.length ∧
    (∀ row ∈ c.recomputeAudit.openedWeightRows, row.length = c.recomputeAudit.openedInputs.length ∧ ∀ q ∈ row, isE2m1Mantissa q = true) ∧
    (∀ sh ∈ c.recomputeAudit.openedBlockShifts, sh ≤ 8)
  weightsCommitted : c.modelWeightsRoot = fpauditWeightsRoot c.recomputeAudit.openedWeightRows c.recomputeAudit.openedBlockShifts
  openedExactMatch : ∃ opened, c.recomputeAudit.committedRounds[c.recomputeAudit.openedRoundIdx]? = some opened ∧
    opened.inputRoot = fpauditInputRoot c.inputRoot c.recomputeAudit.openedInputs ∧
    exactMxfp4Logits c.recomputeAudit.openedInputs c.recomputeAudit.openedWeightRows c.recomputeAudit.openedBlockShifts = opened.claimedLogits ∧
    argmaxIdx (exactMxfp4Logits c.recomputeAudit.openedInputs c.recomputeAudit.openedWeightRows c.recomputeAudit.openedBlockShifts) = opened.claimedArgmax
structure ValidCandidateReceiptWitness (c : CandidateComputation) : Prop where
  suiteNonEmpty : c.suite.suiteId ≠ []
  regimeNotCbr : c.suite.regime ≠ .withdrawnCapacityBoundCbr
  logBlowupBound : 0 < c.suite.logBlowup ∧ c.suite.logBlowup ≤ 8
  logArityGe1 : 1 ≤ c.suite.logArity
  queriesPinned : 0 < c.suite.pinnedNumQueries ∧ c.observedNumQueries = c.suite.pinnedNumQueries
  powBound : c.suite.powBits ≤ 24
  powZeroCanonical : c.suite.powBits = 0 → c.powNonce = 0
  ud100Floor : 100000 ≤ suiteProvenMilliBits c.suite
  stmtBound : c.statementDigest = candidateStatementDigest c.suite c.modelWeightsRoot c.inputRoot c.recomputeAudit.commitRoot c.outputRoot c.recomputeAudit.committedRounds.length c.boundFloorsDigest c.actionPayloadDigest
  powVerified : hasLowZeroBits (candidatePowHash c.statementDigest c.proofTranscriptDigest c.powNonce) (Nat.min c.suite.powBits 24) = true
  recomputeVerified : ValidExactRecomputeWitness c
private theorem verifyExactRecomputeAudit_sound {c : CandidateComputation} (h : verifyExactRecomputeAudit c = true) : ValidExactRecomputeWitness c := by
  unfold verifyExactRecomputeAudit at h; dsimp only at h
  split at h; · cases h
  rename_i hNonEmp; split at h; · cases h
  rename_i hAllRds; split at h; · cases h
  split at h; · cases h
  rename_i hComOut; split at h; · cases h
  rename_i hCoin
  cases hGet : c.recomputeAudit.committedRounds[c.recomputeAudit.openedRoundIdx]? with
  | none => rw [hGet] at h; cases h
  | some opened =>
    rw [hGet] at h; dsimp only at h
    split at h; · cases h
    rename_i hInW; split at h; · cases h
    rename_i hE2m1; split at h; · cases h
    rename_i hComs
    simp only [Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, List.isEmpty_iff, not_or] at hNonEmp hAllRds hComOut hCoin hInW hE2m1 hComs
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hRdsPos : 0 < c.recomputeAudit.committedRounds.length := List.length_pos_iff.mpr hNonEmp.1
    have hRdsOk : ∀ r ∈ c.recomputeAudit.committedRounds, r.inputRoot.size = 32 ∧ r.claimedLogits ≠ [] ∧ r.claimedArgmax = argmaxIdx r.claimedLogits := by
      have ha := List.all_eq_true.mp (by cases hb : c.recomputeAudit.committedRounds.all (fun r => r.inputRoot.size == 32 && !r.claimedLogits.isEmpty && r.claimedArgmax == argmaxIdx r.claimedLogits) with | true => rfl | false => exact absurd hb hAllRds)
      intro r hr; have hrr := ha r hr; simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hrr
      exact ⟨hrr.1.1, (fun he => by rw [he] at hrr; cases hrr.1.2), hrr.2⟩
    have hInPos : 0 < c.recomputeAudit.openedInputs.length := List.length_pos_iff.mpr hInW.1.1.1
    have hWPos : 0 < c.recomputeAudit.openedWeightRows.length := List.length_pos_iff.mpr hInW.1.2
    have hInS8 : ∀ x ∈ c.recomputeAudit.openedInputs, isS8 x = true :=
      List.all_eq_true.mp (by cases hb : c.recomputeAudit.openedInputs.all isS8 with | true => rfl | false => exact absurd hb hInW.1.1.2)
    have hRowsOk : ∀ row ∈ c.recomputeAudit.openedWeightRows, row.length = c.recomputeAudit.openedInputs.length ∧ ∀ q ∈ row, isE2m1Mantissa q = true := by
      have ha := List.all_eq_true.mp (by cases hb : c.recomputeAudit.openedWeightRows.all (fun row => row.length == c.recomputeAudit.openedInputs.length && row.all isE2m1Mantissa) with | true => rfl | false => exact absurd hb hE2m1.1)
      intro row hr; have hrr := ha row hr; simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hrr; exact hrr
    have hShOk : ∀ sh ∈ c.recomputeAudit.openedBlockShifts, sh ≤ 8 := by
      have ha := List.all_eq_true.mp (by cases hb : c.recomputeAudit.openedBlockShifts.all (fun sh => decide (sh ≤ 8)) with | true => rfl | false => exact absurd hb hE2m1.2)
      intro sh hs; exact of_decide_eq_true (ha sh hs)
    exact ⟨hRdsPos, hRdsOk, Decidable.of_not_not hComOut.1, Decidable.of_not_not hComOut.2, Decidable.of_not_not hCoin,
      ⟨hInPos, hInS8⟩, ⟨hWPos, Decidable.of_not_not hInW.2, hRowsOk, hShOk⟩, Decidable.of_not_not hComs.1,
      ⟨opened, hGet, Decidable.of_not_not hComs.2, h.1, h.2⟩⟩
/-- **Flagship Soundness of Grounded `ZkmlSuiteArtifact` + `fpaudit` Bit-Exact Recompute Gate (`verifyCandidateComputation_sound`, `0 Classical`)**. -/
theorem verifyCandidateComputation_sound {c : CandidateComputation} (h : verifyCandidateComputation c = true) : ValidCandidateReceiptWitness c := by
  unfold verifyCandidateComputation at h; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hSuite, _⟩, hQPin⟩, hStmt⟩, hPowZero⟩, hPow⟩, hAudit⟩ := h
  unfold checkSuiteArtifact at hSuite; simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq] at hSuite
  obtain ⟨⟨hIdNe, hNotCbr⟩, hLbPos, hLbLe, hAr, hQPos, hPowBnd, h100⟩ := hSuite
  exact ⟨(fun he => by rw [he] at hIdNe; cases hIdNe), hNotCbr, ⟨hLbPos, hLbLe⟩, hAr, ⟨hQPos, hQPin⟩, hPowBnd, hPowZero, h100, hStmt, hPow, verifyExactRecomputeAudit_sound hAudit⟩
/-- **Flagship `fpaudit` Steering Detection (`lying_caught_at_opened_round`, `0 Classical`)**:
    Any server whose committed round at the commit-before-coin opened index disagrees with the bit-exact
    `s8 × E2M1` integer recompute (either logits or argmax) is unconditionally refused! -/
theorem lying_caught_at_opened_round {c : CandidateComputation} {opened : CommittedRecomputeRound}
    (hOpened : c.recomputeAudit.committedRounds[fpauditOpenedRoundIdx c.statementDigest c.recomputeAudit.commitRoot c.outputRoot c.proofTranscriptDigest c.powNonce c.recomputeAudit.committedRounds.length]? = some opened)
    (hLie : exactMxfp4Logits c.recomputeAudit.openedInputs c.recomputeAudit.openedWeightRows c.recomputeAudit.openedBlockShifts ≠ opened.claimedLogits ∨
            argmaxIdx (exactMxfp4Logits c.recomputeAudit.openedInputs c.recomputeAudit.openedWeightRows c.recomputeAudit.openedBlockShifts) ≠ opened.claimedArgmax) :
    verifyExactRecomputeAudit c = false ∧ verifyCandidateComputation c = false := by
  have hFalse : verifyExactRecomputeAudit c = false := by
    cases hVer : verifyExactRecomputeAudit c with
    | false => rfl
    | true =>
      exfalso; have hW := verifyExactRecomputeAudit_sound hVer
      obtain ⟨opened', hGet', _, hLogEq, hArgEq⟩ := hW.openedExactMatch
      rw [hW.commitBeforeCoin, hOpened] at hGet'; cases hGet'
      rcases hLie with hNeL | hNeA
      · exact hNeL hLogEq
      · exact hNeA hArgEq
  exact ⟨hFalse, by unfold verifyCandidateComputation; rw [hFalse]; simp⟩
def buildHonestCandidate (suite : ZkmlSuiteArtifact) (sensorSealDigest boundFloorsDigest actionPayloadDigest proofTranscriptDigest : ByteArray)
    (powNonce : UInt64) (roundInputs : List (List Int)) (weightRows : List (List Int)) (blockShifts : List Nat) : CandidateComputation :=
  let wRoot := fpauditWeightsRoot weightRows blockShifts
  let rounds := (List.range roundInputs.length).map fun i =>
    let xs := roundInputs.getD i []
    let logits := exactMxfp4Logits xs weightRows blockShifts
    ⟨i, fpauditInputRoot sensorSealDigest xs, logits, argmaxIdx logits⟩
  let cRoot := fpauditCommitRoot rounds; let oRoot := fpauditOutputRoot rounds
  let stmt := candidateStatementDigest suite wRoot sensorSealDigest cRoot oRoot rounds.length boundFloorsDigest actionPayloadDigest
  let openIdx := fpauditOpenedRoundIdx stmt cRoot oRoot proofTranscriptDigest powNonce rounds.length
  let openedXs := roundInputs.getD openIdx []
  { suite := suite, statementDigest := stmt, modelWeightsRoot := wRoot, inputRoot := sensorSealDigest, outputRoot := oRoot, boundFloorsDigest := boundFloorsDigest, actionPayloadDigest := actionPayloadDigest, observedNumQueries := suite.pinnedNumQueries, proofTranscriptDigest := proofTranscriptDigest, powNonce := powNonce, recomputeAudit := ⟨rounds, cRoot, openIdx, openedXs, weightRows, blockShifts⟩ }
/-! ## 2. Full-Width 256-Bit Single-Layer Stateful `PqHashSignatures` Quorums & `OBEND.SHE.TURN/v1` Wire Framing -/
def shePqParamsValid (p : PqHashParams) : Bool :=
  p.wellFormed && p.w == 4 && decide (128 ≤ p.ell1) && p.numLayers == 1 && p.statefulLeanSig &&
  decide (2 ≤ p.subtreeHeight ∧ p.subtreeHeight ≤ 20 ∧ p.maxSigsLog2 = p.subtreeHeight)
def sheStatefulPqParams : PqHashParams := { w := 4, ell1 := 128, subtreeHeight := 2, numLayers := 1, forsTrees := 0, forsHeight := 0, maxSigsLog2 := 2, statefulLeanSig := true }
def sheStatelessPqParams : PqHashParams := { w := 4, ell1 := 128, subtreeHeight := 2, numLayers := 2, forsTrees := 20, forsHeight := 5, maxSigsLog2 := 4, statefulLeanSig := false }
def checkPqSigCanonical (p : PqHashParams) (pk : PqPublicKey) (sig : PqHashSig) : Bool :=
  decide (pk.pkSeed.length = 32 ∧ pk.pkRoot.length = 32) && decide (sig.rRand.length = 32) && decide (sig.msgTswCtr < 2 ^ 32) &&
  decide (sig.leafGlobalIdx < 2 ^ p.maxSigsLog2) && decide (sig.layerSigs.length = p.numLayers) &&
  sig.layerSigs.all (fun ls => decide (ls.tswCtr < 2 ^ 32) && checkLayerSigFraming p ls) &&
  (if p.statefulLeanSig then sig.forsOpenings.isEmpty && decide (sig.msgTswCtr = 0) else decide (sig.forsOpenings.length = p.forsTrees) && sig.forsOpenings.all (checkForsOpeningFraming p))
@[expose] def verifyShePqSig (p : PqHashParams) (pk : PqPublicKey) (msg : ByteArray) (sig : PqHashSig) : Bool :=
  shePqParamsValid p && checkPqSigCanonical p pk sig && verifyPqHashSig cshake256Suite p pk msg.data.toList sig
theorem verifyShePqSig_sound {p : PqHashParams} {pk : PqPublicKey} {msg : ByteArray} {sig : PqHashSig} (h : verifyShePqSig p pk msg sig = true) :
    shePqParamsValid p = true ∧ checkPqSigCanonical p pk sig = true ∧ verifyPqHashSig cshake256Suite p pk msg.data.toList sig = true := by
  unfold verifyShePqSig at h; simp only [Bool.and_eq_true] at h; exact ⟨h.1.1, h.1.2, h.2⟩
inductive UpgradeAuthorityClaim where
  | localCustodianCeremony | vendorRootDirective (vendorSig : ByteArray) | agencyEmergencyOrder (agencyId : ByteArray) (agencySig : ByteArray)
  deriving DecidableEq
structure ActuationTurnProposal where
  sensorSeq : Nat
  sensorSealDigest : ByteArray
  candidate : CandidateComputation
  nullifier : ByteArray
  mandateCost : Nat
  redactedRoiCount : Nat
  consentBandHeightPx : Nat
  attestedGpuCount : Nat
  sharedRingAtCopy : ByteArray
  privateFrameCopy : ByteArray
  dispatchedPayload : ByteArray
  simplexCommitteeN : Nat
  simplexFaultyF : Nat
  simplexQcSignatures : List (Nat × PqHashSig)
  custodianEpoch : Nat
  custodianSignatures : List (Nat × PqHashSig)
  tofRoundTripTicks : Nat
  deriving DecidableEq
structure UpgradeJudgeProposal where
  newJudgeDigest : ByteArray
  newModelWeightsRoot : ByteArray
  newZkmlSuiteDigest : ByteArray
  newFloors : List SheFloor
  newRevertWindowSteps : Nat
  newCustodianEpoch : Nat
  custodianSignatures : List (Nat × PqHashSig)
  tofRoundTripTicks : Nat
  authorityClaim : UpgradeAuthorityClaim
  deriving DecidableEq
structure MandateAttenuation where
  newBudgetCap : Nat
  newMaxProximityTicks : Nat
  newlyRevokedCustodians : List Nat
  reasonDigest : ByteArray
  deriving DecidableEq
inductive SheTurn where
  | proposeAndSettleActuation (proposal : ActuationTurnProposal) | upgradeHabitatJudge (upgrade : UpgradeJudgeProposal) | revokeOrAttenuateMandate (attenuation : MandateAttenuation)
  deriving DecidableEq
structure SettledActuationRecord where
  sensorSeq : Nat
  sensorSealDigest : ByteArray
  nullifier : ByteArray
  mandateCost : Nat
  redactedRoiCount : Nat
  consentBandHeightPx : Nat
  attestedGpuCount : Nat
  provenZkmlMilliBits : Nat
  zkmlRegime : ZkmlSoundnessRegime
  zkmlLogArity : Nat
  zkmlObservedQueries : Nat
  zkmlPinnedQueries : Nat
  zkmlSuiteDigest : ByteArray
  fpauditCommitRoot : ByteArray
  fpauditOpenedRoundIdx : Nat
  modelWeightsRoot : ByteArray
  activeFloorsAtSettlement : List SheFloor
  boundFloorsDigest : ByteArray
  revertWindowAtSettlement : Nat
  sharedRingAtCopy : ByteArray
  privateFrameCopy : ByteArray
  dispatchedPayload : ByteArray
  simplexCommitteeN : Nat
  simplexFaultyF : Nat
  simplexQuorumCount : Nat
  simplexQcSignatures : List (Nat × PqHashSig)
  simplexQcSigningMsg : ByteArray
  custodianEpoch : Nat
  custodianSigners : List Nat
  custodianSignatures : List (Nat × PqHashSig)
  custodianSigningMsg : ByteArray
  tofRoundTripTicks : Nat
  maxProximityTicksAtSettle : Nat
  turnEnvelopeDigest : ByteArray
  deriving DecidableEq
structure SheState where
  habitatJudgeDigest : ByteArray
  pinnedModelWeightsRoot : ByteArray
  pinnedZkmlSuiteDigest : ByteArray
  monoSensorSeq : Nat
  consumedNullifiers : List ByteArray
  remainingMandateBudget : Nat
  activeSafetyAndPrivacyFloors : List SheFloor
  settledOutboxActions : List SettledActuationRecord
  pqParams : PqHashParams
  custodianPks : List PqPublicKey
  simplexValidatorPks : List PqPublicKey
  consumedCustodianLeaves : List (Nat × Nat)
  consumedSimplexLeaves : List (Nat × Nat)
  custodianThresholdT : Nat
  custodianTotalN : Nat
  custodianQuorumEpoch : Nat
  revokedCustodians : List Nat
  maxProximityTicks : Nat
  revertWindowSteps : Nat
  deriving DecidableEq
@[expose] def settledTotalCost : List SettledActuationRecord → Nat | [] => 0 | r :: rs => r.mandateCost + settledTotalCost rs
@[simp] theorem settledTotalCost_append (xs ys : List SettledActuationRecord) : settledTotalCost (xs ++ ys) = settledTotalCost xs + settledTotalCost ys := by
  induction xs with | nil => simp [settledTotalCost] | cons _ _ ih => simp [settledTotalCost, ih, Nat.add_assoc]
def SheFloor.encode : SheFloor → List UInt8
  | .sensorRoiRedaction k => 0x01 :: leb128 k | .consentBandNonOcclusion px => 0x02 :: leb128 px | .zkmlProvenSoundnessMilliBits mb => 0x03 :: leb128 mb
  | .physicalProximityMaxTicks t => 0x04 :: leb128 t | .e2eeTeeChannelBound g => 0x05 :: leb128 g | .operatorLocalRevert r => 0x06 :: leb128 r
theorem SheFloor.encode_injective {φ₁ φ₂ : SheFloor} (h : φ₁.encode = φ₂.encode) : φ₁ = φ₂ := by
  cases φ₁ <;> cases φ₂ <;> simp only [SheFloor.encode, List.cons.injEq] at h <;> first | exact absurd h.1 (by decide) | exact congrArg _ (leb128_injective h.2)
def encodeFloors (floors : List SheFloor) : List UInt8 := encodeSheFields (floors.map SheFloor.encode)
theorem encodeFloors_injective {fs₁ fs₂ : List SheFloor} (h : encodeFloors fs₁ = encodeFloors fs₂) : fs₁ = fs₂ := (List.map_inj_right (fun _ _ => SheFloor.encode_injective)).mp (encodeSheFields_injective h)
def floorsDigest (floors : List SheFloor) : ByteArray := cshake32ByteArray (asciiTagBytes "OBEND.SHE.FLOORS/v1") (encodeFloors floors)
theorem floorsDigest_size (floors : List SheFloor) : (floorsDigest floors).size = 32 := cshake32ByteArray_size _ _
theorem floorsDigest_binds {fs₁ fs₂ : List SheFloor} (h : floorsDigest fs₁ = floorsDigest fs₂) :
    fs₁ = fs₂ ∨ CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.FLOORS/v1")) (fun x => x = encodeFloors fs₁ ∨ x = encodeFloors fs₂) := by
  cases extractCshake32 (asciiTagBytes "OBEND.SHE.FLOORS/v1") (encodeFloors fs₁) (encodeFloors fs₂) h with | inl hp => exact .inl (encodeFloors_injective hp.down) | inr hc => exact .inr hc.down
def shePayloadDigest (payload : ByteArray) : ByteArray := cshake32ByteArray (asciiTagBytes "OBEND.SHE.PAYLOAD/v1") (encodeSheFields [payload.data.toList])
theorem shePayloadDigest_size (payload : ByteArray) : (shePayloadDigest payload).size = 32 := cshake32ByteArray_size _ _
theorem shePayloadDigest_binds {p₁ p₂ : ByteArray} (h : shePayloadDigest p₁ = shePayloadDigest p₂) :
    p₁ = p₂ ∨ CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.PAYLOAD/v1")) (fun x => x = encodeSheFields [p₁.data.toList] ∨ x = encodeSheFields [p₂.data.toList]) := by
  cases extractCshake32 (asciiTagBytes "OBEND.SHE.PAYLOAD/v1") (encodeSheFields [p₁.data.toList]) (encodeSheFields [p₂.data.toList]) h with
  | inr hc => exact .inr hc.down | inl hp => have hf := encodeSheFields_injective hp.down; simp only [List.cons.injEq, and_true] at hf; exact .inl (byteArray_eq_of_toList_eq hf)
def encodeCommittedRound (r : CommittedRecomputeRound) : List UInt8 := encodeSheFields [leb128 r.roundIdx, r.inputRoot.data.toList, encodeIntList r.claimedLogits, leb128 r.claimedArgmax]
theorem encodeCommittedRound_injective {a b : CommittedRecomputeRound} (h : encodeCommittedRound a = encodeCommittedRound b) : a = b := by
  have hf := encodeSheFields_injective h; simp only [List.cons.injEq, and_true] at hf; cases a; cases b; simp only [CommittedRecomputeRound.mk.injEq]
  exact ⟨leb128_injective hf.1, byteArray_eq_of_toList_eq hf.2.1, encodeIntList_injective hf.2.2.1, leb128_injective hf.2.2.2⟩
def encodeExactRecomputeAudit (a : ExactRecomputeAudit) : List UInt8 :=
  encodeSheFields [encodeSheFields (a.committedRounds.map encodeCommittedRound), a.commitRoot.data.toList, leb128 a.openedRoundIdx, encodeIntList a.openedInputs, encodeIntMatrix a.openedWeightRows, encodeNatList a.openedBlockShifts]
theorem encodeExactRecomputeAudit_injective {a b : ExactRecomputeAudit} (h : encodeExactRecomputeAudit a = encodeExactRecomputeAudit b) : a = b := by
  have hf := encodeSheFields_injective h; simp only [List.cons.injEq, and_true] at hf; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf; cases a; cases b; simp only [ExactRecomputeAudit.mk.injEq]
  exact ⟨(List.map_inj_right fun _ _ => encodeCommittedRound_injective).mp (encodeSheFields_injective h1), byteArray_eq_of_toList_eq h2, leb128_injective h3, encodeIntList_injective h4, encodeIntMatrix_injective h5, encodeNatList_injective h6⟩
def encodeCandidateComputation (c : CandidateComputation) : List UInt8 :=
  encodeSheFields [encodeZkmlSuiteArtifact c.suite, c.statementDigest.data.toList, c.modelWeightsRoot.data.toList, c.inputRoot.data.toList, c.outputRoot.data.toList, c.boundFloorsDigest.data.toList, c.actionPayloadDigest.data.toList, leb128 c.observedNumQueries, c.proofTranscriptDigest.data.toList, leb128 c.powNonce.toNat, encodeExactRecomputeAudit c.recomputeAudit]
theorem encodeCandidateComputation_injective {c₁ c₂ : CandidateComputation} (h : encodeCandidateComputation c₁ = encodeCandidateComputation c₂) : c₁ = c₂ := by
  have hf := encodeSheFields_injective h; simp only [List.cons.injEq, and_true] at hf; obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hf; cases c₁; cases c₂; simp only [CandidateComputation.mk.injEq]
  exact ⟨encodeZkmlSuiteArtifact_injective h1, byteArray_eq_of_toList_eq h2, byteArray_eq_of_toList_eq h3, byteArray_eq_of_toList_eq h4, byteArray_eq_of_toList_eq h5, byteArray_eq_of_toList_eq h6, byteArray_eq_of_toList_eq h7, leb128_injective h8, byteArray_eq_of_toList_eq h9, uint64_eq_of_toNat_eq (leb128_injective h10), encodeExactRecomputeAudit_injective h11⟩
def encodeForsOpening (o : ForsTreeOpening) : List UInt8 := encodeSheFields [o.secretVal, encodeByteListList o.authPath]
theorem encodeForsOpening_injective {a b : ForsTreeOpening} (h : encodeForsOpening a = encodeForsOpening b) : a = b := by
  have hf := encodeSheFields_injective h; simp only [List.cons.injEq, and_true] at hf; cases a; cases b; simp only [ForsTreeOpening.mk.injEq]; exact ⟨hf.1, encodeByteListList_injective hf.2⟩
def encodeLayerXmssSig (ls : LayerXmssSig) : List UInt8 := encodeSheFields [leb128 ls.tswCtr, encodeByteListList ls.wotsChains, encodeByteListList ls.authPath]
theorem encodeLayerXmssSig_injective {a b : LayerXmssSig} (h : encodeLayerXmssSig a = encodeLayerXmssSig b) : a = b := by
  have hf := encodeSheFields_injective h; simp only [List.cons.injEq, and_true] at hf; cases a; cases b; simp only [LayerXmssSig.mk.injEq]; exact ⟨leb128_injective hf.1, encodeByteListList_injective hf.2.1, encodeByteListList_injective hf.2.2⟩
def encodePqHashSig (s : PqHashSig) : List UInt8 := encodeSheFields [s.rRand, leb128 s.msgTswCtr, leb128 s.leafGlobalIdx, encodeSheFields (s.forsOpenings.map encodeForsOpening), encodeSheFields (s.layerSigs.map encodeLayerXmssSig)]
theorem encodePqHashSig_injective {a b : PqHashSig} (h : encodePqHashSig a = encodePqHashSig b) : a = b := by
  have hf := encodeSheFields_injective h; simp only [List.cons.injEq, and_true] at hf; obtain ⟨hR, hC, hL, hF, hLs⟩ := hf; cases a; cases b; simp only [PqHashSig.mk.injEq]
  exact ⟨hR, leb128_injective hC, leb128_injective hL, (List.map_inj_right fun _ _ => encodeForsOpening_injective).mp (encodeSheFields_injective hF), (List.map_inj_right fun _ _ => encodeLayerXmssSig_injective).mp (encodeSheFields_injective hLs)⟩
def encodeIndexedPqSig (entry : Nat × PqHashSig) : List UInt8 := encodeSheFields [leb128 entry.1, encodePqHashSig entry.2]
theorem encodeIndexedPqSig_injective {a b : Nat × PqHashSig} (h : encodeIndexedPqSig a = encodeIndexedPqSig b) : a = b := by
  have hf := encodeSheFields_injective h; simp only [List.cons.injEq, and_true] at hf; exact Prod.ext (leb128_injective hf.1) (encodePqHashSig_injective hf.2)
def encodeIndexedPqSigList (xs : List (Nat × PqHashSig)) : List UInt8 := encodeSheFields (xs.map encodeIndexedPqSig)
theorem encodeIndexedPqSigList_injective {xs₁ xs₂ : List (Nat × PqHashSig)} (h : encodeIndexedPqSigList xs₁ = encodeIndexedPqSigList xs₂) : xs₁ = xs₂ := (List.map_inj_right fun _ _ => encodeIndexedPqSig_injective).mp (encodeSheFields_injective h)
def encodePqParams (p : PqHashParams) : List UInt8 := encodeSheFields [leb128 p.w, leb128 p.ell1, leb128 p.subtreeHeight, leb128 p.numLayers, leb128 p.forsTrees, leb128 p.forsHeight, leb128 p.maxSigsLog2, [if p.statefulLeanSig then 1 else 0]]
def encodePqPk (pk : PqPublicKey) : List UInt8 := encodeSheFields [pk.pkSeed, pk.pkRoot]
def encodePqPkList (pks : List PqPublicKey) : List UInt8 := encodeSheFields (pks.map encodePqPk)
def encodeAuthorityClaim : UpgradeAuthorityClaim → List UInt8
  | .localCustodianCeremony => encodeSheFields [[0x01]] | .vendorRootDirective sig => encodeSheFields [[0x02], sig.data.toList] | .agencyEmergencyOrder id sig => encodeSheFields [[0x03], id.data.toList, sig.data.toList]
theorem encodeAuthorityClaim_injective {a₁ a₂ : UpgradeAuthorityClaim} (h : encodeAuthorityClaim a₁ = encodeAuthorityClaim a₂) : a₁ = a₂ := by
  cases a₁ <;> cases a₂ <;> dsimp only [encodeAuthorityClaim] at h
  all_goals have hf := encodeSheFields_injective h; try (cases (List.cons.inj (List.cons.inj hf).1).1)
  · rfl
  · simp only [List.cons.injEq, and_true] at hf; exact congrArg UpgradeAuthorityClaim.vendorRootDirective (byteArray_eq_of_toList_eq hf.2)
  · simp only [List.cons.injEq, and_true] at hf; rw [byteArray_eq_of_toList_eq hf.2.1, byteArray_eq_of_toList_eq hf.2.2]
def encodeBytes32List (xs : List ByteArray) : List UInt8 := encodeSheFields (xs.map fun b => b.data.toList)
def encodeLeafList (xs : List (Nat × Nat)) : List UInt8 := encodeSheFields (xs.map fun p => encodeSheFields [leb128 p.1, leb128 p.2])
def sheStateDigest (st : SheState) : ByteArray :=
  cshake32ByteArray (asciiTagBytes "OBEND.SHE.STATE/v1") (encodeSheFields [st.habitatJudgeDigest.data.toList, st.pinnedModelWeightsRoot.data.toList, st.pinnedZkmlSuiteDigest.data.toList, leb128 st.monoSensorSeq, encodeBytes32List st.consumedNullifiers, leb128 st.remainingMandateBudget, (floorsDigest st.activeSafetyAndPrivacyFloors).data.toList, encodeBytes32List (st.settledOutboxActions.map SettledActuationRecord.turnEnvelopeDigest), encodePqParams st.pqParams, encodePqPkList st.custodianPks, encodePqPkList st.simplexValidatorPks, encodeLeafList st.consumedCustodianLeaves, encodeLeafList st.consumedSimplexLeaves, leb128 st.custodianThresholdT, leb128 st.custodianTotalN, leb128 st.custodianQuorumEpoch, encodeNatList st.revokedCustodians, leb128 st.maxProximityTicks, leb128 st.revertWindowSteps])
def encodeUnsignedActuation (act : ActuationTurnProposal) : List UInt8 :=
  encodeSheFields [leb128 act.sensorSeq, act.sensorSealDigest.data.toList, encodeCandidateComputation act.candidate, act.nullifier.data.toList, leb128 act.mandateCost, leb128 act.redactedRoiCount, leb128 act.consentBandHeightPx, leb128 act.attestedGpuCount, act.sharedRingAtCopy.data.toList, act.privateFrameCopy.data.toList, act.dispatchedPayload.data.toList, leb128 act.simplexCommitteeN, leb128 act.simplexFaultyF, leb128 act.custodianEpoch, leb128 act.tofRoundTripTicks]
def encodeUnsignedUpgrade (up : UpgradeJudgeProposal) : List UInt8 :=
  encodeSheFields [up.newJudgeDigest.data.toList, up.newModelWeightsRoot.data.toList, up.newZkmlSuiteDigest.data.toList, encodeFloors up.newFloors, leb128 up.newRevertWindowSteps, leb128 up.newCustodianEpoch, leb128 up.tofRoundTripTicks, encodeAuthorityClaim up.authorityClaim]
def sheCustodianActuationMsg (st : SheState) (act : ActuationTurnProposal) : ByteArray := cshake32ByteArray (asciiTagBytes "OBEND.SHE.CUSTODIAN_SIG/v1") (encodeSheFields [(sheStateDigest st).data.toList, [0x01], leb128 act.custodianEpoch, encodeUnsignedActuation act])
def sheCustodianUpgradeMsg (st : SheState) (up : UpgradeJudgeProposal) : ByteArray := cshake32ByteArray (asciiTagBytes "OBEND.SHE.CUSTODIAN_SIG/v1") (encodeSheFields [(sheStateDigest st).data.toList, [0x02], leb128 up.newCustodianEpoch, encodeUnsignedUpgrade up])
def sheSimplexQcMsg (st : SheState) (act : ActuationTurnProposal) : ByteArray := cshake32ByteArray (asciiTagBytes "OBEND.SHE.SIMPLEX_QC/v1") (encodeSheFields [(sheStateDigest st).data.toList, [0x02], leb128 act.simplexCommitteeN, leb128 act.simplexFaultyF, encodeUnsignedActuation act])
def sheTurnWireFields : SheTurn → List (List UInt8)
  | .proposeAndSettleActuation act => [[0x01], leb128 act.sensorSeq, act.sensorSealDigest.data.toList, encodeCandidateComputation act.candidate, act.nullifier.data.toList, leb128 act.mandateCost, leb128 act.redactedRoiCount, leb128 act.consentBandHeightPx, leb128 act.attestedGpuCount, act.sharedRingAtCopy.data.toList, act.privateFrameCopy.data.toList, act.dispatchedPayload.data.toList, leb128 act.simplexCommitteeN, leb128 act.simplexFaultyF, encodeIndexedPqSigList act.simplexQcSignatures, leb128 act.custodianEpoch, encodeIndexedPqSigList act.custodianSignatures, leb128 act.tofRoundTripTicks]
  | .upgradeHabitatJudge up => [[0x02], up.newJudgeDigest.data.toList, up.newModelWeightsRoot.data.toList, up.newZkmlSuiteDigest.data.toList, encodeFloors up.newFloors, leb128 up.newRevertWindowSteps, leb128 up.newCustodianEpoch, encodeIndexedPqSigList up.custodianSignatures, leb128 up.tofRoundTripTicks, encodeAuthorityClaim up.authorityClaim]
  | .revokeOrAttenuateMandate rev => [[0x03], leb128 rev.newBudgetCap, leb128 rev.newMaxProximityTicks, encodeNatList rev.newlyRevokedCustodians, rev.reasonDigest.data.toList]
def sheTurnPreimage (turn : SheTurn) : List UInt8 := encodeSheFields (sheTurnWireFields turn)
theorem sheTurnPreimage_injective {t₁ t₂ : SheTurn} (h : sheTurnPreimage t₁ = sheTurnPreimage t₂) : t₁ = t₂ := by
  have hf := encodeSheFields_injective h
  cases t₁ with
  | proposeAndSettleActuation a₁ => cases t₂ with
    | proposeAndSettleActuation a₂ =>
      simp only [sheTurnWireFields, List.cons.injEq, true_and, and_true] at hf; obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hf; cases a₁; cases a₂; simp only [SheTurn.proposeAndSettleActuation.injEq, ActuationTurnProposal.mk.injEq]
      exact ⟨leb128_injective h1, byteArray_eq_of_toList_eq h2, encodeCandidateComputation_injective h3, byteArray_eq_of_toList_eq h4, leb128_injective h5, leb128_injective h6, leb128_injective h7, leb128_injective h8, byteArray_eq_of_toList_eq h9, byteArray_eq_of_toList_eq h10, byteArray_eq_of_toList_eq h11, leb128_injective h12, leb128_injective h13, encodeIndexedPqSigList_injective h14, leb128_injective h15, encodeIndexedPqSigList_injective h16, leb128_injective h17⟩
    | upgradeHabitatJudge _ | revokeOrAttenuateMandate _ => dsimp only [sheTurnWireFields] at hf; cases (List.cons.inj (List.cons.inj hf).1).1
  | upgradeHabitatJudge u₁ => cases t₂ with
    | proposeAndSettleActuation _ | revokeOrAttenuateMandate _ => dsimp only [sheTurnWireFields] at hf; cases (List.cons.inj (List.cons.inj hf).1).1
    | upgradeHabitatJudge u₂ =>
      simp only [sheTurnWireFields, List.cons.injEq, true_and, and_true] at hf; obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hf; cases u₁; cases u₂; simp only [SheTurn.upgradeHabitatJudge.injEq, UpgradeJudgeProposal.mk.injEq]
      exact ⟨byteArray_eq_of_toList_eq h1, byteArray_eq_of_toList_eq h2, byteArray_eq_of_toList_eq h3, encodeFloors_injective h4, leb128_injective h5, leb128_injective h6, encodeIndexedPqSigList_injective h7, leb128_injective h8, encodeAuthorityClaim_injective h9⟩
  | revokeOrAttenuateMandate r₁ => cases t₂ with
    | proposeAndSettleActuation _ | upgradeHabitatJudge _ => dsimp only [sheTurnWireFields] at hf; cases (List.cons.inj (List.cons.inj hf).1).1
    | revokeOrAttenuateMandate r₂ =>
      simp only [sheTurnWireFields, List.cons.injEq, true_and, and_true] at hf; obtain ⟨h1, h2, h3, h4⟩ := hf; cases r₁; cases r₂; simp only [SheTurn.revokeOrAttenuateMandate.injEq, MandateAttenuation.mk.injEq]
      exact ⟨leb128_injective h1, leb128_injective h2, encodeNatList_injective h3, byteArray_eq_of_toList_eq h4⟩
def sheTurnEnvelopeDigest (turn : SheTurn) : ByteArray := cshake32ByteArray (asciiTagBytes "OBEND.SHE.TURN/v1") (sheTurnPreimage turn)
theorem sheTurnEnvelopeDigest_size (turn : SheTurn) : (sheTurnEnvelopeDigest turn).size = 32 := cshake32ByteArray_size _ _
def extractSheTurnEnvelope (t₁ t₂ : SheTurn) (h : sheTurnEnvelopeDigest t₁ = sheTurnEnvelopeDigest t₂) :
    PSum (PLift (t₁ = t₂)) (PLift (CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.TURN/v1")) (fun x => x = sheTurnPreimage t₁ ∨ x = sheTurnPreimage t₂))) :=
  match extractCshake32 (asciiTagBytes "OBEND.SHE.TURN/v1") (sheTurnPreimage t₁) (sheTurnPreimage t₂) h with | .inl hp => .inl ⟨sheTurnPreimage_injective hp.down⟩ | .inr hc => .inr hc
theorem sheTurnEnvelope_binds {t₁ t₂ : SheTurn} (h : sheTurnEnvelopeDigest t₁ = sheTurnEnvelopeDigest t₂) :
    t₁ = t₂ ∨ CollisionAmong (cshake256Bytes (asciiTagBytes "OBEND.SHE.TURN/v1")) (fun x => x = sheTurnPreimage t₁ ∨ x = sheTurnPreimage t₂) := by
  cases extractSheTurnEnvelope t₁ t₂ h with | inl heq => exact .inl heq.down | inr hcol => exact .inr hcol.down
/-! ## 3. Deterministic Multi-Turn Sovereign SHE Transition Gate & Declarative Step Equivalence -/
inductive SheRefusal where
  | malformedInitialState | invalidDigestWidth | nonMonotoneSensorSeq (currentSeq proposedSeq : Nat) | sensorSealMismatch | zkmlProofUnverified | zkmlSuiteNotPinned | withdrawnCbrRegimeRefused | belowProven100BitFloor (actualMilliBits : Nat)
  | modelWeightsRootMismatch | floorsDigestMismatch | payloadDigestMismatch | floorConstraintViolated (floor : SheFloor) | nullifierReplayed | mandateBudgetExceeded (requested available : Nat) | privateFrameCopyMismatch
  | invalidSimplexCommittee (committeeN faultyF : Nat) | invalidSimplexFinalityQc (signedCount requiredQuorum : Nat) | invalidSimplexPqSignature (validator : Nat) | custodianEpochMismatch (expected actual : Nat)
  | duplicateOrOutOfRangeSigner | revokedCustodianSigner (signer : Nat) | insufficientCustodianQuorum (signedCount requiredT : Nat) | invalidCustodianPqSignature (signer : Nat) | reusedStatefulPqLeaf (signer leafIdx : Nat)
  | tofProximityExceeded (actualTicks maxTicks : Nat) | coerciveFloorDowngrade (droppedFloor : SheFloor) | externalAuthorityRefused | malformedFloorSet | nonMonotoneCustodianEpoch (currentEpoch proposedEpoch : Nat)
  | mandateAmplificationRefused | proximityWideningRefused (proposedTicks currentMaxTicks : Nat) | missingTargetFloor (floor : SheFloor) | terminalStateMismatch
  deriving DecidableEq, Repr
def checkListNodup {α : Type} [DecidableEq α] : List α → Bool | [] => true | x :: xs => !xs.contains x && checkListNodup xs
theorem checkListNodup_iff {α : Type} [DecidableEq α] : ∀ (xs : List α), checkListNodup xs = true ↔ xs.Nodup
  | [] => by simp [checkListNodup]
  | x :: xs => by
    cases hc : xs.contains x with
    | true => simp [checkListNodup, List.nodup_cons, List.contains_iff_mem.mp hc]
    | false => have hNot : x ∉ xs := fun hm => Bool.false_ne_true (hc.symm.trans (List.contains_iff_mem.mpr hm)); simp [checkListNodup, checkListNodup_iff xs, List.nodup_cons, hNot]
def checkStrictlyIncreasing : List Nat → Bool | [] => true | [_] => true | a :: b :: rest => decide (a < b) && checkStrictlyIncreasing (b :: rest)
private theorem checkStrictlyIncreasing_iff : ∀ (xs : List Nat), checkStrictlyIncreasing xs = true ↔ List.Pairwise (· < ·) xs
  | [] => by simp [checkStrictlyIncreasing]
  | [_] => by simp [checkStrictlyIncreasing]
  | a :: b :: rest => by
    simp only [checkStrictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq, checkStrictlyIncreasing_iff (b :: rest), List.pairwise_cons]
    refine ⟨fun ⟨hab, hbAll, hRest⟩ => ⟨fun z hz => ?_, hbAll, hRest⟩, fun ⟨haAll, hbAll, hRest⟩ => ⟨haAll b List.mem_cons_self, hbAll, hRest⟩⟩
    rcases List.mem_cons.mp hz with rfl | hzr
    · exact hab
    · exact Nat.lt_trans hab (hbAll z hzr)
private theorem pairwise_lt_implies_nodup {xs : List Nat} (hp : List.Pairwise (· < ·) xs) : xs.Nodup :=
  hp.imp fun h => Nat.ne_of_lt h
abbrev checkNatNodup : List Nat → Bool := checkListNodup
abbrev checkFloorNodup : List SheFloor → Bool := checkListNodup
def checkFloorOnActuation (revertSteps : Nat) (act : ActuationTurnProposal) : SheFloor → Bool
  | .sensorRoiRedaction m => decide (m ≤ act.redactedRoiCount) | .consentBandNonOcclusion px => decide (0 < px ∧ px ≤ act.consentBandHeightPx) | .zkmlProvenSoundnessMilliBits mb => decide (mb ≤ provenZkmlMilliBits act.candidate)
  | .physicalProximityMaxTicks t => decide (act.tofRoundTripTicks ≤ t) | .e2eeTeeChannelBound g => decide (g ≤ act.attestedGpuCount) | .operatorLocalRevert r => decide (revertSteps ≤ r)
def holdsOnSettledRecord : SheFloor → SettledActuationRecord → Bool
  | .sensorRoiRedaction m, r => decide (m ≤ r.redactedRoiCount) | .consentBandNonOcclusion px, r => decide (0 < px ∧ px ≤ r.consentBandHeightPx) | .zkmlProvenSoundnessMilliBits mb, r => decide (mb ≤ r.provenZkmlMilliBits)
  | .physicalProximityMaxTicks t, r => decide (r.tofRoundTripTicks ≤ t) | .e2eeTeeChannelBound g, r => decide (g ≤ r.attestedGpuCount) | .operatorLocalRevert rv, r => decide (r.revertWindowAtSettlement ≤ rv)
def mergeRevokedCustodians (cur newly : List Nat) : List Nat := newly.foldl (fun acc c => if acc.contains c then acc else acc ++ [c]) cur
private theorem mem_mergeRevokedCustodians_left (cur newly : List Nat) {x : Nat} (hx : x ∈ cur) : x ∈ mergeRevokedCustodians cur newly := by
  unfold mergeRevokedCustodians; induction newly generalizing cur with
  | nil => exact hx
  | cons c cs ih =>
    dsimp only [List.foldl]; apply ih; split
    · exact hx
    · exact List.mem_append_left _ hx
def guardE (cond : Bool) (err : SheRefusal) : Except SheRefusal Unit := if cond then .ok () else .error err
@[simp] private theorem guardE_ok {cond : Bool} {err : SheRefusal} : guardE cond err = .ok () ↔ cond = true := by cases cond <;> simp [guardE]
@[simp] private theorem bind_guardE_ok {α : Type} {cond : Bool} {err : SheRefusal} {k : Unit → Except SheRefusal α} {y : α} : (guardE cond err >>= k) = .ok y ↔ cond = true ∧ k () = .ok y := by cases cond <;> simp [guardE, Bind.bind, Except.bind]
@[simp] private theorem bind_ok_unit {α : Type} {k : Unit → Except SheRefusal α} : ((.ok () : Except SheRefusal Unit) >>= k) = k () := rfl
@[simp] private theorem pure_except_ok {α : Type} {x y : α} : (pure x : Except SheRefusal α) = .ok y ↔ x = y := by simp [Pure.pure, Except.pure]
def extractLeaves (sigs : List (Nat × PqHashSig)) : List (Nat × Nat) := sigs.map fun e => (e.1, e.2.leafGlobalIdx)
def checkStatefulLeafFresh (stateful : Bool) (consumed : List (Nat × Nat)) (sigs : List (Nat × PqHashSig)) : Except SheRefusal Unit :=
  if stateful then match sigs.find? (fun e => consumed.contains (e.1, e.2.leafGlobalIdx)) with | some e => .error (.reusedStatefulPqLeaf e.1 e.2.leafGlobalIdx) | none => .ok () else .ok ()
@[simp] private theorem bind_checkLeafFresh_ok {stateful : Bool} {consumed : List (Nat × Nat)} {sigs : List (Nat × PqHashSig)} {k : Unit → Except SheRefusal Unit} :
    (checkStatefulLeafFresh stateful consumed sigs >>= k) = .ok () ↔ (stateful = true → ∀ e ∈ sigs, (e.1, e.2.leafGlobalIdx) ∉ consumed) ∧ k () = .ok () := by
  unfold checkStatefulLeafFresh; cases stateful with
  | false => simp [Bind.bind, Except.bind]
  | true =>
    simp only [↓reduceIte]
    cases hLf : sigs.find? (fun e => consumed.contains (e.1, e.2.leafGlobalIdx)) with
    | some e => have hMem := List.mem_of_find?_eq_some hLf; have hSome := List.find?_some hLf; have hIn := List.contains_iff_mem.mp hSome; simp only [Bind.bind, Except.bind]; exact ⟨fun h => (nomatch h), fun ⟨hNo, _⟩ => absurd hIn (hNo trivial e hMem)⟩
    | none => have hNoLf : ∀ e ∈ sigs, (e.1, e.2.leafGlobalIdx) ∉ consumed := fun e he hIn => List.find?_eq_none.mp hLf e he (List.contains_iff_mem.mpr hIn); simp only [bind_ok_unit]; exact ⟨fun hk => ⟨fun _ => hNoLf, hk⟩, fun ⟨_, hk⟩ => hk⟩
def checkAllPqSigsValid (p : PqHashParams) (pks : List PqPublicKey) (msg : ByteArray) (sigs : List (Nat × PqHashSig)) (mkErr : Nat → SheRefusal) : Except SheRefusal Unit :=
  match sigs.find? (fun e => match pks[e.1]? with | some pk => !verifyShePqSig p pk msg e.2 | none => true) with | some bad => .error (mkErr bad.1) | none => .ok ()
@[simp] private theorem checkAllPqSigsValid_ok_iff (p : PqHashParams) (pks : List PqPublicKey) (msg : ByteArray) (sigs : List (Nat × PqHashSig)) (mkErr : Nat → SheRefusal) :
    checkAllPqSigsValid p pks msg sigs mkErr = .ok () ↔ ∀ e ∈ sigs, ∃ pk, pks[e.1]? = some pk ∧ verifyShePqSig p pk msg e.2 = true := by
  unfold checkAllPqSigsValid
  cases hBad : sigs.find? (fun e => match pks[e.1]? with | some pk => !verifyShePqSig p pk msg e.2 | none => true) with
  | some bad => have hMem := List.mem_of_find?_eq_some hBad; have hPred := List.find?_some hBad; refine ⟨fun h => (nomatch h), fun hAll => ?_⟩; obtain ⟨pk, hPk, hVer⟩ := hAll bad hMem; rw [hPk] at hPred; dsimp only at hPred; rw [hVer] at hPred; cases hPred
  | none =>
    refine ⟨fun _ e he => ?_, fun _ => rfl⟩; have hNot := List.find?_eq_none.mp hBad e he
    cases hPk : pks[e.1]? with
    | none => rw [hPk] at hNot; exact absurd rfl hNot
    | some pk => rw [hPk] at hNot; dsimp only at hNot; cases hv : verifyShePqSig p pk msg e.2 with | true => exact ⟨pk, rfl, hv⟩ | false => rw [hv] at hNot; exact absurd rfl hNot
@[simp] private theorem bind_checkAllPqSigsValid_ok {p : PqHashParams} {pks : List PqPublicKey} {msg : ByteArray} {sigs : List (Nat × PqHashSig)} {mkErr : Nat → SheRefusal} {k : Unit → Except SheRefusal Unit} :
    (checkAllPqSigsValid p pks msg sigs mkErr >>= k) = .ok () ↔ (∀ e ∈ sigs, ∃ pk, pks[e.1]? = some pk ∧ verifyShePqSig p pk msg e.2 = true) ∧ k () = .ok () := by
  cases h : checkAllPqSigsValid p pks msg sigs mkErr with
  | error e => simp only [Bind.bind, Except.bind]; exact ⟨fun hErr => (nomatch hErr), fun ⟨hAll, _⟩ => by rw [(checkAllPqSigsValid_ok_iff p pks msg sigs mkErr).mpr hAll] at h; cases h⟩
  | ok u => cases u; rw [bind_ok_unit]; exact ⟨fun hk => ⟨(checkAllPqSigsValid_ok_iff p pks msg sigs mkErr).mp h, hk⟩, fun ⟨_, hk⟩ => hk⟩
@[expose] def checkCustodianPqQuorum (st : SheState) (msg : ByteArray) (sigs : List (Nat × PqHashSig)) : Except SheRefusal Unit := do
  let signers := sigs.map Prod.fst
  guardE (decide (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN ∧ st.custodianPks.length = st.custodianTotalN) && checkListNodup st.custodianPks) (.insufficientCustodianQuorum sigs.length st.custodianThresholdT)
  guardE (checkStrictlyIncreasing signers && signers.all (fun s => decide (s < st.custodianTotalN))) .duplicateOrOutOfRangeSigner
  match signers.find? (fun s => st.revokedCustodians.contains s) with
  | some rev => .error (.revokedCustodianSigner rev)
  | none => do
    checkStatefulLeafFresh st.pqParams.statefulLeanSig st.consumedCustodianLeaves sigs
    checkAllPqSigsValid st.pqParams st.custodianPks msg sigs .invalidCustodianPqSignature
    guardE (decide (st.custodianThresholdT ≤ sigs.length)) (.insufficientCustodianQuorum sigs.length st.custodianThresholdT)
def ValidPqQuorumProp (st : SheState) (msg : ByteArray) (sigs : List (Nat × PqHashSig)) : Prop :=
  (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN ∧ st.custodianPks.length = st.custodianTotalN ∧ st.custodianPks.Nodup) ∧
  List.Pairwise (· < ·) (sigs.map Prod.fst) ∧ (∀ s ∈ sigs.map Prod.fst, s < st.custodianTotalN) ∧ (∀ s ∈ sigs.map Prod.fst, s ∉ st.revokedCustodians) ∧
  (st.pqParams.statefulLeanSig = true → ∀ e ∈ sigs, (e.1, e.2.leafGlobalIdx) ∉ st.consumedCustodianLeaves) ∧
  (∀ e ∈ sigs, ∃ pk, st.custodianPks[e.1]? = some pk ∧ verifyShePqSig st.pqParams pk msg e.2 = true) ∧ st.custodianThresholdT ≤ sigs.length
theorem checkCustodianPqQuorum_ok_iff (st : SheState) (msg : ByteArray) (sigs : List (Nat × PqHashSig)) : checkCustodianPqQuorum st msg sigs = .ok () ↔ ValidPqQuorumProp st msg sigs := by
  unfold checkCustodianPqQuorum ValidPqQuorumProp; dsimp only
  cases hRev : (sigs.map Prod.fst).find? (fun s => st.revokedCustodians.contains s) with
  | some rev => have hMem := List.mem_of_find?_eq_some hRev; have hIn := List.contains_iff_mem.mp (List.find?_some hRev); simp only [bind_guardE_ok]; exact ⟨fun ⟨_, _, hErr⟩ => (nomatch hErr), fun ⟨_, _, _, hNo, _⟩ => absurd hIn (hNo rev hMem)⟩
  | none =>
    have hNoRev : ∀ s ∈ sigs.map Prod.fst, s ∉ st.revokedCustodians := fun s hs hIn => List.find?_eq_none.mp hRev s hs (List.contains_iff_mem.mpr hIn)
    simp only [bind_guardE_ok, bind_checkLeafFresh_ok, bind_checkAllPqSigsValid_ok, guardE_ok, Bool.and_eq_true, decide_eq_true_eq, checkListNodup_iff, checkStrictlyIncreasing_iff, List.all_eq_true]
    exact ⟨fun ⟨⟨⟨h1, h2, h3⟩, h4⟩, ⟨h5, h6⟩, hLf, hAll, hLen⟩ => ⟨⟨h1, h2, h3, h4⟩, h5, h6, hNoRev, hLf, hAll, hLen⟩, fun ⟨⟨h1, h2, h3, h4⟩, h5, h6, _, hLf, hAll, hLen⟩ => ⟨⟨⟨h1, h2, h3⟩, h4⟩, ⟨h5, h6⟩, hLf, hAll, hLen⟩⟩
def checkSimplexPqQuorum (st : SheState) (msg : ByteArray) (committeeN faultyF : Nat) (sigs : List (Nat × PqHashSig)) : Except SheRefusal Unit := do
  let signers := sigs.map Prod.fst
  guardE (decide (3 * faultyF + 1 ≤ committeeN ∧ committeeN = st.simplexValidatorPks.length) && checkListNodup st.simplexValidatorPks) (.invalidSimplexCommittee committeeN faultyF)
  guardE (checkStrictlyIncreasing signers && signers.all (fun v => decide (v < committeeN)) && decide (committeeN - faultyF ≤ sigs.length)) (.invalidSimplexFinalityQc sigs.length (committeeN - faultyF))
  checkStatefulLeafFresh st.pqParams.statefulLeanSig st.consumedSimplexLeaves sigs
  checkAllPqSigsValid st.pqParams st.simplexValidatorPks msg sigs .invalidSimplexPqSignature
def ValidSimplexPqProp (st : SheState) (msg : ByteArray) (committeeN faultyF : Nat) (sigs : List (Nat × PqHashSig)) : Prop :=
  (3 * faultyF + 1 ≤ committeeN ∧ committeeN = st.simplexValidatorPks.length ∧ st.simplexValidatorPks.Nodup) ∧
  List.Pairwise (· < ·) (sigs.map Prod.fst) ∧ (∀ v ∈ sigs.map Prod.fst, v < committeeN) ∧ committeeN - faultyF ≤ sigs.length ∧
  (st.pqParams.statefulLeanSig = true → ∀ e ∈ sigs, (e.1, e.2.leafGlobalIdx) ∉ st.consumedSimplexLeaves) ∧
  (∀ e ∈ sigs, ∃ pk, st.simplexValidatorPks[e.1]? = some pk ∧ verifyShePqSig st.pqParams pk msg e.2 = true)
theorem checkSimplexPqQuorum_ok_iff (st : SheState) (msg : ByteArray) (committeeN faultyF : Nat) (sigs : List (Nat × PqHashSig)) :
    checkSimplexPqQuorum st msg committeeN faultyF sigs = .ok () ↔ ValidSimplexPqProp st msg committeeN faultyF sigs := by
  unfold checkSimplexPqQuorum ValidSimplexPqProp; simp only [bind_guardE_ok, bind_checkLeafFresh_ok, checkAllPqSigsValid_ok_iff, Bool.and_eq_true, decide_eq_true_eq, checkListNodup_iff, checkStrictlyIncreasing_iff, List.all_eq_true]
  exact ⟨fun ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h4, h5⟩, h6⟩, hLf, hAll⟩ => ⟨⟨h1, h2, h3⟩, h4, h5, h6, hLf, hAll⟩, fun ⟨⟨h1, h2, h3⟩, h4, h5, h6, hLf, hAll⟩ => ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h4, h5⟩, h6⟩, hLf, hAll⟩⟩
def buildSettledRecord (st : SheState) (act : ActuationTurnProposal) : SettledActuationRecord :=
  { sensorSeq := act.sensorSeq, sensorSealDigest := act.sensorSealDigest, nullifier := act.nullifier, mandateCost := act.mandateCost, redactedRoiCount := act.redactedRoiCount, consentBandHeightPx := act.consentBandHeightPx, attestedGpuCount := act.attestedGpuCount, provenZkmlMilliBits := provenZkmlMilliBits act.candidate, zkmlRegime := act.candidate.suite.regime, zkmlLogArity := act.candidate.suite.logArity, zkmlObservedQueries := act.candidate.observedNumQueries, zkmlPinnedQueries := act.candidate.suite.pinnedNumQueries, zkmlSuiteDigest := suiteArtifactDigest act.candidate.suite, fpauditCommitRoot := act.candidate.recomputeAudit.commitRoot, fpauditOpenedRoundIdx := act.candidate.recomputeAudit.openedRoundIdx, modelWeightsRoot := act.candidate.modelWeightsRoot, activeFloorsAtSettlement := st.activeSafetyAndPrivacyFloors, boundFloorsDigest := act.candidate.boundFloorsDigest, revertWindowAtSettlement := st.revertWindowSteps, sharedRingAtCopy := act.sharedRingAtCopy, privateFrameCopy := act.privateFrameCopy, dispatchedPayload := act.dispatchedPayload, simplexCommitteeN := act.simplexCommitteeN, simplexFaultyF := act.simplexFaultyF, simplexQuorumCount := act.simplexQcSignatures.length, simplexQcSignatures := act.simplexQcSignatures, simplexQcSigningMsg := sheSimplexQcMsg st act, custodianEpoch := act.custodianEpoch, custodianSigners := act.custodianSignatures.map Prod.fst, custodianSignatures := act.custodianSignatures, custodianSigningMsg := sheCustodianActuationMsg st act, tofRoundTripTicks := act.tofRoundTripTicks, maxProximityTicksAtSettle := st.maxProximityTicks, turnEnvelopeDigest := sheTurnEnvelopeDigest (.proposeAndSettleActuation act) }
@[expose] def applySheTurn (st : SheState) (turn : SheTurn) : Except SheRefusal SheState := match turn with
  | .proposeAndSettleActuation act => do
    guardE (decide (act.sensorSealDigest.size = 32 ∧ act.candidate.statementDigest.size = 32 ∧ act.candidate.modelWeightsRoot.size = 32 ∧ act.candidate.inputRoot.size = 32 ∧ act.candidate.outputRoot.size = 32 ∧ act.candidate.boundFloorsDigest.size = 32 ∧ act.candidate.actionPayloadDigest.size = 32 ∧ act.nullifier.size = 32)) .invalidDigestWidth
    guardE (decide (st.monoSensorSeq < act.sensorSeq)) (.nonMonotoneSensorSeq st.monoSensorSeq act.sensorSeq)
    guardE (act.candidate.inputRoot == act.sensorSealDigest) .sensorSealMismatch
    guardE (act.candidate.suite.regime != .withdrawnCapacityBoundCbr) .withdrawnCbrRegimeRefused
    guardE (verifyCandidateComputation act.candidate) .zkmlProofUnverified
    guardE (suiteArtifactDigest act.candidate.suite == st.pinnedZkmlSuiteDigest) .zkmlSuiteNotPinned
    guardE (decide (100000 ≤ provenZkmlMilliBits act.candidate)) (.belowProven100BitFloor (provenZkmlMilliBits act.candidate))
    guardE (act.candidate.modelWeightsRoot == st.pinnedModelWeightsRoot) .modelWeightsRootMismatch
    guardE (act.candidate.boundFloorsDigest == floorsDigest st.activeSafetyAndPrivacyFloors) .floorsDigestMismatch
    guardE (act.candidate.actionPayloadDigest == shePayloadDigest act.privateFrameCopy) .payloadDigestMismatch
    guardE (decide (act.tofRoundTripTicks ≤ st.maxProximityTicks)) (.tofProximityExceeded act.tofRoundTripTicks st.maxProximityTicks)
    match st.activeSafetyAndPrivacyFloors.find? (fun φ => !checkFloorOnActuation st.revertWindowSteps act φ) with
    | some violated => .error (.floorConstraintViolated violated)
    | none => do
      guardE (!st.consumedNullifiers.contains act.nullifier) .nullifierReplayed
      guardE (decide (act.mandateCost ≤ st.remainingMandateBudget)) (.mandateBudgetExceeded act.mandateCost st.remainingMandateBudget)
      guardE (act.privateFrameCopy == act.sharedRingAtCopy && act.dispatchedPayload == act.privateFrameCopy) .privateFrameCopyMismatch
      checkSimplexPqQuorum st (sheSimplexQcMsg st act) act.simplexCommitteeN act.simplexFaultyF act.simplexQcSignatures
      guardE (decide (act.custodianEpoch = st.custodianQuorumEpoch)) (.custodianEpochMismatch st.custodianQuorumEpoch act.custodianEpoch)
      checkCustodianPqQuorum st (sheCustodianActuationMsg st act) act.custodianSignatures
      pure { st with monoSensorSeq := act.sensorSeq, consumedNullifiers := st.consumedNullifiers ++ [act.nullifier], remainingMandateBudget := st.remainingMandateBudget - act.mandateCost, consumedCustodianLeaves := st.consumedCustodianLeaves ++ extractLeaves act.custodianSignatures, consumedSimplexLeaves := st.consumedSimplexLeaves ++ extractLeaves act.simplexQcSignatures, settledOutboxActions := st.settledOutboxActions ++ [buildSettledRecord st act] }
  | .upgradeHabitatJudge up =>
    match st.activeSafetyAndPrivacyFloors.find? (fun φ => !up.newFloors.contains φ) with
    | some dropped => .error (.coerciveFloorDowngrade dropped)
    | none => do
      guardE (up.authorityClaim == .localCustodianCeremony) .externalAuthorityRefused
      guardE (decide (up.newJudgeDigest.size = 32 ∧ up.newModelWeightsRoot.size = 32 ∧ up.newZkmlSuiteDigest.size = 32)) .invalidDigestWidth
      guardE (checkFloorNodup up.newFloors && up.newFloors.any SheFloor.isBedrock && up.newFloors.all SheFloor.wellFormed && up.newFloors.all (fun φ => match φ with | .operatorLocalRevert maxRev => decide (up.newRevertWindowSteps ≤ maxRev) | _ => true)) .malformedFloorSet
      guardE (decide (st.custodianQuorumEpoch < up.newCustodianEpoch)) (.nonMonotoneCustodianEpoch st.custodianQuorumEpoch up.newCustodianEpoch)
      checkCustodianPqQuorum st (sheCustodianUpgradeMsg st up) up.custodianSignatures
      guardE (decide (up.tofRoundTripTicks ≤ st.maxProximityTicks)) (.tofProximityExceeded up.tofRoundTripTicks st.maxProximityTicks)
      pure { st with habitatJudgeDigest := up.newJudgeDigest, pinnedModelWeightsRoot := up.newModelWeightsRoot, pinnedZkmlSuiteDigest := up.newZkmlSuiteDigest, activeSafetyAndPrivacyFloors := up.newFloors, revertWindowSteps := up.newRevertWindowSteps, custodianQuorumEpoch := up.newCustodianEpoch, consumedCustodianLeaves := st.consumedCustodianLeaves ++ extractLeaves up.custodianSignatures }
  | .revokeOrAttenuateMandate rev => do
    guardE (decide (rev.reasonDigest.size = 32)) .invalidDigestWidth
    guardE (decide (rev.newBudgetCap ≤ st.remainingMandateBudget)) .mandateAmplificationRefused
    guardE (decide (0 < rev.newMaxProximityTicks ∧ rev.newMaxProximityTicks ≤ st.maxProximityTicks)) (.proximityWideningRefused rev.newMaxProximityTicks st.maxProximityTicks)
    guardE (rev.newlyRevokedCustodians.all (fun c => decide (c < st.custodianTotalN))) .duplicateOrOutOfRangeSigner
    pure { st with remainingMandateBudget := rev.newBudgetCap, maxProximityTicks := rev.newMaxProximityTicks, revokedCustodians := mergeRevokedCustodians st.revokedCustodians rev.newlyRevokedCustodians }
@[expose] def runSheTurns (st : SheState) (turns : List SheTurn) : Except (Nat × SheRefusal) SheState := go 0 st turns
where go (idx : Nat) (cur : SheState) : List SheTurn → Except (Nat × SheRefusal) SheState | [] => .ok cur | t :: ts => match applySheTurn cur t with | .error r => .error (idx, r) | .ok next => go (idx + 1) next ts
@[expose] def ValidSheTrace : SheState → List SheTurn → SheState → Prop | st, [], stFinal => stFinal = st | st, t :: ts, stFinal => ∃ stNext, applySheTurn st t = .ok stNext ∧ ValidSheTrace stNext ts stFinal
theorem runSheTurns_go_ok_iff : ∀ (turns : List SheTurn) (idx : Nat) (st endSt : SheState), runSheTurns.go idx st turns = .ok endSt ↔ ValidSheTrace st turns endSt
  | [], _, _, _ => by simp [runSheTurns.go, ValidSheTrace, eq_comm]
  | t :: ts, idx, st, endSt => by simp only [runSheTurns.go, ValidSheTrace]; cases applySheTurn st t with | error _ => simp | ok next => simp [runSheTurns_go_ok_iff ts (idx + 1) next endSt]
theorem runSheTurns_ok_iff (st : SheState) (turns : List SheTurn) (endSt : SheState) : runSheTurns st turns = .ok endSt ↔ ValidSheTrace st turns endSt := runSheTurns_go_ok_iff turns 0 st endSt
inductive InductiveSheStep : SheState → SheTurn → SheState → Prop where
  | settleActuation (st : SheState) (act : ActuationTurnProposal) (hWidths : act.sensorSealDigest.size = 32 ∧ act.candidate.statementDigest.size = 32 ∧ act.candidate.modelWeightsRoot.size = 32 ∧ act.candidate.inputRoot.size = 32 ∧ act.candidate.outputRoot.size = 32 ∧ act.candidate.boundFloorsDigest.size = 32 ∧ act.candidate.actionPayloadDigest.size = 32 ∧ act.nullifier.size = 32)
      (hSeq : st.monoSensorSeq < act.sensorSeq) (hSeal : act.candidate.inputRoot = act.sensorSealDigest) (hRegime : act.candidate.suite.regime ≠ .withdrawnCapacityBoundCbr) (hVer : verifyCandidateComputation act.candidate = true) (hSuitePin : suiteArtifactDigest act.candidate.suite = st.pinnedZkmlSuiteDigest) (hBits : 100000 ≤ provenZkmlMilliBits act.candidate)
      (hWeights : act.candidate.modelWeightsRoot = st.pinnedModelWeightsRoot) (hFlDig : act.candidate.boundFloorsDigest = floorsDigest st.activeSafetyAndPrivacyFloors) (hPayDig : act.candidate.actionPayloadDigest = shePayloadDigest act.privateFrameCopy) (hTof : act.tofRoundTripTicks ≤ st.maxProximityTicks)
      (hFloors : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, checkFloorOnActuation st.revertWindowSteps act φ = true) (hFresh : act.nullifier ∉ st.consumedNullifiers) (hBudget : act.mandateCost ≤ st.remainingMandateBudget) (hCopy : act.privateFrameCopy = act.sharedRingAtCopy ∧ act.dispatchedPayload = act.privateFrameCopy)
      (hSimpQc : ValidSimplexPqProp st (sheSimplexQcMsg st act) act.simplexCommitteeN act.simplexFaultyF act.simplexQcSignatures) (hEp : act.custodianEpoch = st.custodianQuorumEpoch) (hCust : ValidPqQuorumProp st (sheCustodianActuationMsg st act) act.custodianSignatures) :
      InductiveSheStep st (.proposeAndSettleActuation act) { st with monoSensorSeq := act.sensorSeq, consumedNullifiers := st.consumedNullifiers ++ [act.nullifier], remainingMandateBudget := st.remainingMandateBudget - act.mandateCost, consumedCustodianLeaves := st.consumedCustodianLeaves ++ extractLeaves act.custodianSignatures, consumedSimplexLeaves := st.consumedSimplexLeaves ++ extractLeaves act.simplexQcSignatures, settledOutboxActions := st.settledOutboxActions ++ [buildSettledRecord st act] }
  | upgradeJudge (st : SheState) (up : UpgradeJudgeProposal) (hNonReg : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, φ ∈ up.newFloors) (hLocalAuth : up.authorityClaim = .localCustodianCeremony) (hWidths : up.newJudgeDigest.size = 32 ∧ up.newModelWeightsRoot.size = 32 ∧ up.newZkmlSuiteDigest.size = 32)
      (hFlWf : up.newFloors.Nodup ∧ (∃ φ ∈ up.newFloors, φ.isBedrock = true) ∧ (∀ φ ∈ up.newFloors, φ.wellFormed = true) ∧ (∀ φ ∈ up.newFloors, (match φ with | .operatorLocalRevert maxRev => decide (up.newRevertWindowSteps ≤ maxRev) | _ => true) = true))
      (hEp : st.custodianQuorumEpoch < up.newCustodianEpoch) (hCust : ValidPqQuorumProp st (sheCustodianUpgradeMsg st up) up.custodianSignatures) (hTof : up.tofRoundTripTicks ≤ st.maxProximityTicks) :
      InductiveSheStep st (.upgradeHabitatJudge up) { st with habitatJudgeDigest := up.newJudgeDigest, pinnedModelWeightsRoot := up.newModelWeightsRoot, pinnedZkmlSuiteDigest := up.newZkmlSuiteDigest, activeSafetyAndPrivacyFloors := up.newFloors, revertWindowSteps := up.newRevertWindowSteps, custodianQuorumEpoch := up.newCustodianEpoch, consumedCustodianLeaves := st.consumedCustodianLeaves ++ extractLeaves up.custodianSignatures }
  | attenuateMandate (st : SheState) (rev : MandateAttenuation) (hWidth : rev.reasonDigest.size = 32) (hBud : rev.newBudgetCap ≤ st.remainingMandateBudget) (hProx : 0 < rev.newMaxProximityTicks ∧ rev.newMaxProximityTicks ≤ st.maxProximityTicks) (hRevRange : ∀ c ∈ rev.newlyRevokedCustodians, c < st.custodianTotalN) :
      InductiveSheStep st (.revokeOrAttenuateMandate rev) { st with remainingMandateBudget := rev.newBudgetCap, maxProximityTicks := rev.newMaxProximityTicks, revokedCustodians := mergeRevokedCustodians st.revokedCustodians rev.newlyRevokedCustodians }
theorem applySheTurn_ok_iff_inductiveStep (st : SheState) (turn : SheTurn) (st' : SheState) : applySheTurn st turn = .ok st' ↔ InductiveSheStep st turn st' := by
  constructor
  · intro hOk; cases turn with
    | proposeAndSettleActuation act =>
      unfold applySheTurn at hOk; simp only [bind_guardE_ok] at hOk; obtain ⟨hWidths, hSeq, hSeal, hReg, hVer, hSuitePin, hBits, hW, hFlD, hPayD, hTof, hRest⟩ := hOk
      cases hFlFind : st.activeSafetyAndPrivacyFloors.find? (fun φ => !checkFloorOnActuation st.revertWindowSteps act φ) with
      | some _ => rw [hFlFind] at hRest; cases hRest
      | none =>
        rw [hFlFind] at hRest; simp only [bind_guardE_ok] at hRest; obtain ⟨hNotNul, hBud, hCopy, hRest2⟩ := hRest
        generalize hSimp : checkSimplexPqQuorum st (sheSimplexQcMsg st act) act.simplexCommitteeN act.simplexFaultyF act.simplexQcSignatures = sRes at hRest2
        cases sRes with
        | error _ => simp [Bind.bind, Except.bind] at hRest2
        | ok u1 =>
          cases u1; simp only [bind_ok_unit, bind_guardE_ok] at hRest2; obtain ⟨hEp, hRest3⟩ := hRest2
          generalize hCust : checkCustodianPqQuorum st (sheCustodianActuationMsg st act) act.custodianSignatures = cRes at hRest3
          cases cRes with
          | error _ => simp [Bind.bind, Except.bind] at hRest3
          | ok u2 =>
            cases u2; simp only [bind_ok_unit, pure_except_ok] at hRest3; subst hRest3; simp only [decide_eq_true_eq, beq_iff_eq, bne_iff_ne, Bool.and_eq_true] at hWidths hSeq hSeal hReg hSuitePin hBits hW hFlD hPayD hTof hBud hCopy hEp
            have hFresh : act.nullifier ∉ st.consumedNullifiers := fun hIn => by rw [List.contains_iff_mem.mpr hIn] at hNotNul; cases hNotNul
            have hFloors : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, checkFloorOnActuation st.revertWindowSteps act φ = true := fun φ hφ => by have hf := List.find?_eq_none.mp hFlFind φ hφ; cases hc : checkFloorOnActuation st.revertWindowSteps act φ with | true => rfl | false => rw [hc] at hf; exact absurd rfl hf
            exact .settleActuation st act hWidths hSeq hSeal hReg hVer hSuitePin hBits hW hFlD hPayD hTof hFloors hFresh hBud hCopy ((checkSimplexPqQuorum_ok_iff _ _ _ _ _).mp hSimp) hEp ((checkCustodianPqQuorum_ok_iff _ _ _).mp hCust)
    | upgradeHabitatJudge up =>
      unfold applySheTurn at hOk; dsimp only at hOk
      cases hDrop : st.activeSafetyAndPrivacyFloors.find? (fun ψ => !up.newFloors.contains ψ) with
      | some _ => rw [hDrop] at hOk; cases hOk
      | none =>
        rw [hDrop] at hOk; simp only [bind_guardE_ok] at hOk; obtain ⟨hAuth, hW, hFlAll, hEp, hRest⟩ := hOk
        generalize hCust : checkCustodianPqQuorum st (sheCustodianUpgradeMsg st up) up.custodianSignatures = cRes at hRest
        cases cRes with
        | error _ => simp [Bind.bind, Except.bind] at hRest
        | ok u =>
          cases u; simp only [bind_ok_unit, bind_guardE_ok, pure_except_ok] at hRest; simp only [decide_eq_true_eq, beq_iff_eq, Bool.and_eq_true, checkListNodup_iff, List.any_eq_true, List.all_eq_true] at hAuth hW hFlAll hEp hRest
          obtain ⟨⟨⟨hNd, hBed⟩, hWf⟩, hRevBnd⟩ := hFlAll; obtain ⟨hTof, rfl⟩ := hRest
          have hNonReg : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, φ ∈ up.newFloors := fun φ hφ => by have hf := List.find?_eq_none.mp hDrop φ hφ; cases hc : up.newFloors.contains φ with | true => exact List.contains_iff_mem.mp hc | false => rw [hc] at hf; exact absurd rfl hf
          exact .upgradeJudge st up hNonReg hAuth hW ⟨hNd, hBed, hWf, hRevBnd⟩ hEp ((checkCustodianPqQuorum_ok_iff _ _ _).mp hCust) hTof
    | revokeOrAttenuateMandate rev => unfold applySheTurn at hOk; dsimp only at hOk; simp only [bind_guardE_ok, pure_except_ok, decide_eq_true_eq, List.all_eq_true] at hOk; obtain ⟨hW, hBud, hProx, hRange, rfl⟩ := hOk; exact .attenuateMandate st rev hW hBud hProx hRange
  · intro hInd; cases hInd with
    | settleActuation act hWidths hSeq hSeal hReg hVer hSuitePin hBits hW hFlD hPayD hTof hFloors hFresh hBud hCopy hSimpQc hEp hCust =>
      unfold applySheTurn; dsimp only; have hFlNone : st.activeSafetyAndPrivacyFloors.find? (fun φ => !checkFloorOnActuation st.revertWindowSteps act φ) = none := List.find?_eq_none.mpr fun φ hφ => by simp [hFloors φ hφ]
      have hNotCont : (!st.consumedNullifiers.contains act.nullifier) = true := by cases hc : st.consumedNullifiers.contains act.nullifier with | false => rfl | true => exact absurd (List.contains_iff_mem.mp hc) hFresh
      have hSimpOk := (checkSimplexPqQuorum_ok_iff st (sheSimplexQcMsg st act) act.simplexCommitteeN act.simplexFaultyF act.simplexQcSignatures).mpr hSimpQc
      have hCustOk := (checkCustodianPqQuorum_ok_iff st (sheCustodianActuationMsg st act) act.custodianSignatures).mpr hCust
      simp only [bind_guardE_ok]; rw [hFlNone]; simp only [bind_guardE_ok]; rw [hSimpOk]; simp only [bind_ok_unit, bind_guardE_ok]; rw [hCustOk]; simp only [bind_ok_unit, pure_except_ok, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, Bool.and_eq_true]
      exact ⟨hWidths, hSeq, hSeal, hReg, hVer, hSuitePin, hBits, hW, hFlD, hPayD, hTof, hNotCont, hBud, hCopy, hEp, trivial⟩
    | upgradeJudge up hNonReg hAuth hWidths hFlWf hEp hCust hTof =>
      unfold applySheTurn; dsimp only; have hDropNone : st.activeSafetyAndPrivacyFloors.find? (fun ψ => !up.newFloors.contains ψ) = none := List.find?_eq_none.mpr fun φ hφ => by rw [List.contains_iff_mem.mpr (hNonReg φ hφ)]; decide
      have hCustOk := (checkCustodianPqQuorum_ok_iff st (sheCustodianUpgradeMsg st up) up.custodianSignatures).mpr hCust
      rw [hDropNone]; simp only [bind_guardE_ok]; rw [hCustOk]; simp only [bind_ok_unit, bind_guardE_ok, pure_except_ok, decide_eq_true_eq, beq_iff_eq, Bool.and_eq_true, checkListNodup_iff, List.any_eq_true, List.all_eq_true]
      exact ⟨hAuth, hWidths, ⟨⟨⟨hFlWf.1, hFlWf.2.1⟩, hFlWf.2.2.1⟩, hFlWf.2.2.2⟩, hEp, hTof, trivial⟩
    | attenuateMandate rev hWidth hBud hProx hRevRange => unfold applySheTurn; dsimp only; simp only [bind_guardE_ok, pure_except_ok, decide_eq_true_eq, List.all_eq_true]; exact ⟨hWidth, hBud, hProx, hRevRange, trivial⟩
theorem applySheTurn_skip_implies_contract_violation (st : SheState) (turn : SheTurn) (r : SheRefusal) (hErr : applySheTurn st turn = .error r) :
    ∀ st', ¬ InductiveSheStep st turn st' := fun st' hStep => by have hOk := (applySheTurn_ok_iff_inductiveStep st turn st').mpr hStep; rw [hErr] at hOk; cases hOk
/-! ## 4. Flagship Theorems: Anti-Vaz, Multi-Turn Trace Safety & `she_ceremony_pq_quorum_unforgeable` -/
private theorem step_preserves_floors {st st' : SheState} {turn : SheTurn} (h : applySheTurn st turn = .ok st') : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, φ ∈ st'.activeSafetyAndPrivacyFloors := by
  cases (applySheTurn_ok_iff_inductiveStep st turn st').mp h with | settleActuation | attenuateMandate => exact fun _ hφ => hφ | upgradeJudge _ hNonReg => exact hNonReg
theorem vaz_coercive_floor_downgrade_refused (initState endState : SheState) (turns : List SheTurn) :
    (∀ (st : SheState) (up : UpgradeJudgeProposal) (φ : SheFloor), φ ∈ st.activeSafetyAndPrivacyFloors → φ ∉ up.newFloors →
      (∃ dropped ∈ st.activeSafetyAndPrivacyFloors, dropped ∉ up.newFloors ∧ applySheTurn st (.upgradeHabitatJudge up) = .error (.coerciveFloorDowngrade dropped)) ∧ ∀ st', applySheTurn st (.upgradeHabitatJudge up) ≠ .ok st') ∧
    (ValidSheTrace initState turns endState → initState.activeSafetyAndPrivacyFloors ⊆ endState.activeSafetyAndPrivacyFloors) := by
  refine ⟨fun st up φ hMem hNotMem => ?_, fun hTrace => ?_⟩
  · have hPred : (!up.newFloors.contains φ) = true := by cases hc : up.newFloors.contains φ with | false => rfl | true => exact absurd (List.contains_iff_mem.mp hc) hNotMem
    cases hFind : st.activeSafetyAndPrivacyFloors.find? (fun ψ => !up.newFloors.contains ψ) with
    | none => exact absurd hPred (List.find?_eq_none.mp hFind φ hMem)
    | some dropped =>
      have hDropPred := List.find?_some hFind; have hDropNotIn : dropped ∉ up.newFloors := fun hin => by rw [List.contains_iff_mem.mpr hin] at hDropPred; cases hDropPred
      have hStepErr : applySheTurn st (.upgradeHabitatJudge up) = .error (.coerciveFloorDowngrade dropped) := by unfold applySheTurn; dsimp only; rw [hFind]
      exact ⟨⟨dropped, List.mem_of_find?_eq_some hFind, hDropNotIn, hStepErr⟩, fun _ hOk => by rw [hStepErr] at hOk; cases hOk⟩
  · induction turns generalizing initState with
    | nil => simp only [ValidSheTrace] at hTrace; subst hTrace; exact fun _ h => h
    | cons _ _ ih => obtain ⟨stNext, hStep, hRest⟩ := hTrace; exact fun φ hφ => ih stNext hRest (step_preserves_floors hStep φ hφ)
private def removeFirstNat (a : Nat) : List Nat → List Nat | [] => [] | y :: ys => if y = a then ys else y :: removeFirstNat a ys
private theorem removeFirstNat_length_of_mem {a : Nat} : ∀ {ys : List Nat}, a ∈ ys → (removeFirstNat a ys).length + 1 = ys.length
  | [], h => nomatch h
  | y :: ys, h => by
    simp only [removeFirstNat]; cases Nat.decEq y a with
    | isTrue hy => simp [hy]
    | isFalse hy =>
      simp only [hy, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.mp h with rfl | hm
      · exact absurd rfl hy
      · have := removeFirstNat_length_of_mem hm; omega
private theorem mem_removeFirstNat_of_ne {x a : Nat} : ∀ {ys : List Nat}, x ∈ ys → x ≠ a → x ∈ removeFirstNat a ys
  | [], h, _ => nomatch h
  | y :: ys, h, hne => by
    simp only [removeFirstNat]; cases Nat.decEq y a with
    | isTrue hy => subst hy; simp only [↓reduceIte]; exact match List.mem_cons.mp h with | .inl e => absurd e hne | .inr m => m
    | isFalse hy => simp only [hy, ↓reduceIte, List.mem_cons]; exact match List.mem_cons.mp h with | .inl e => .inl e | .inr m => .inr (mem_removeFirstNat_of_ne m hne)
private theorem nodup_subset_length_le : ∀ {xs ys : List Nat}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | a :: as, ys, hnd, hsub => by obtain ⟨haNotAs, hasNd⟩ := List.nodup_cons.mp hnd; have := nodup_subset_length_le hasNd fun x hx => mem_removeFirstNat_of_ne (hsub x (List.mem_cons_of_mem _ hx)) (fun heq => by subst heq; exact haNotAs hx); have := removeFirstNat_length_of_mem (hsub a List.mem_cons_self); simp only [List.length_cons]; omega
theorem coerced_subthreshold_coalition_omits_honest_signer {signers coerced : List Nat} {t : Nat} (hNodup : signers.Nodup) (hQuorum : t ≤ signers.length) (hCoerced : coerced.length < t) : ∃ h ∈ signers, h ∉ coerced := by
  cases hf : signers.find? (fun s => !coerced.contains s) with
  | some h => have hPred := List.find?_some hf; exact ⟨h, List.mem_of_find?_eq_some hf, fun hIn => by rw [List.contains_iff_mem.mpr hIn] at hPred; cases hPred⟩
  | none =>
    have hAll : ∀ s ∈ signers, s ∈ coerced := fun s hs => by
      have hp := List.find?_eq_none.mp hf s hs; cases hc : coerced.contains s with | true => exact List.contains_iff_mem.mp hc | false => rw [hc] at hp; exact absurd rfl hp
    have := nodup_subset_length_le hNodup hAll; omega
private theorem pairwise_lt_snoc {xs : List Nat} {x : Nat} (hp : List.Pairwise (· < ·) xs) (hall : ∀ y ∈ xs, y < x) : List.Pairwise (· < ·) (xs ++ [x]) := by
  induction xs with
  | nil => exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | cons a as ih => cases hp with | cons ha hpas =>
      refine List.Pairwise.cons (fun z hz => ?_) (ih hpas (fun y hy => hall y (List.mem_cons_of_mem _ hy)))
      rcases List.mem_append.mp hz with hzas | hzx
      · exact ha z hzas
      · simp only [List.mem_singleton] at hzx; exact hzx ▸ hall a List.mem_cons_self
private theorem nodup_snoc {α : Type} {xs : List α} {x : α} (hd : xs.Nodup) (hnot : x ∉ xs) : (xs ++ [x]).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | cons a as ih => cases hd with | cons ha hdas =>
      refine List.Pairwise.cons (fun z hz => ?_) (ih hdas (fun hm => hnot (List.mem_cons_of_mem _ hm)))
      rcases List.mem_append.mp hz with hzas | hzx
      · exact ha z hzas
      · simp only [List.mem_singleton] at hzx; exact fun heq => hnot ((heq.trans hzx).symm ▸ List.mem_cons_self)
private structure SheTraceInv (init cur : SheState) : Prop where
  floorsSub : init.activeSafetyAndPrivacyFloors ⊆ cur.activeSafetyAndPrivacyFloors
  seqMonoInit : init.monoSensorSeq ≤ cur.monoSensorSeq
  proxLeInit : cur.maxProximityTicks ≤ init.maxProximityTicks
  pqParamsEq : cur.pqParams = init.pqParams
  custPksEq : cur.custodianPks = init.custodianPks
  simpPksEq : cur.simplexValidatorPks = init.simplexValidatorPks
  threshEq : cur.custodianThresholdT = init.custodianThresholdT
  totalEq : cur.custodianTotalN = init.custodianTotalN
  epochMonoInit : init.custodianQuorumEpoch ≤ cur.custodianQuorumEpoch
  revokedMono : ∀ r ∈ init.revokedCustodians, r ∈ cur.revokedCustodians
  budgetConserve : settledTotalCost cur.settledOutboxActions + cur.remainingMandateBudget ≤ settledTotalCost init.settledOutboxActions + init.remainingMandateBudget
  consumedNodup : cur.consumedNullifiers.Nodup
  settledNodup : (cur.settledOutboxActions.map SettledActuationRecord.nullifier).Nodup
  settledInCons : ∀ rec ∈ cur.settledOutboxActions, rec.nullifier ∈ cur.consumedNullifiers
  seqPairwise : List.Pairwise (· < ·) (cur.settledOutboxActions.map SettledActuationRecord.sensorSeq)
  settledSeqBound : ∀ rec ∈ cur.settledOutboxActions, rec.sensorSeq ≤ cur.monoSensorSeq
  settledSafe : ∀ rec ∈ cur.settledOutboxActions, rec ∈ init.settledOutboxActions ∨
    (init.monoSensorSeq < rec.sensorSeq ∧ rec.sensorSealDigest.size = 32 ∧ rec.zkmlRegime ≠ .withdrawnCapacityBoundCbr ∧ 1 ≤ rec.zkmlLogArity ∧ rec.zkmlObservedQueries = rec.zkmlPinnedQueries ∧ 100000 ≤ rec.provenZkmlMilliBits ∧ rec.boundFloorsDigest = floorsDigest rec.activeFloorsAtSettlement ∧ init.activeSafetyAndPrivacyFloors ⊆ rec.activeFloorsAtSettlement ∧ (∀ φ ∈ rec.activeFloorsAtSettlement, holdsOnSettledRecord φ rec = true) ∧ rec.dispatchedPayload = rec.privateFrameCopy ∧ rec.privateFrameCopy = rec.sharedRingAtCopy ∧ 3 * rec.simplexFaultyF + 1 ≤ rec.simplexCommitteeN ∧ rec.simplexCommitteeN - rec.simplexFaultyF ≤ rec.simplexQuorumCount ∧ (∀ e ∈ rec.simplexQcSignatures, ∃ pk, init.simplexValidatorPks[e.1]? = some pk ∧ verifyPqHashSig cshake256Suite init.pqParams pk rec.simplexQcSigningMsg.data.toList e.2 = true) ∧ rec.custodianSigners.Nodup ∧ init.custodianThresholdT ≤ rec.custodianSigners.length ∧ (∀ s ∈ rec.custodianSigners, s < init.custodianTotalN) ∧ (∀ s ∈ rec.custodianSigners, s ∉ init.revokedCustodians) ∧ (∀ e ∈ rec.custodianSignatures, ∃ pk, init.custodianPks[e.1]? = some pk ∧ verifyPqHashSig cshake256Suite init.pqParams pk rec.custodianSigningMsg.data.toList e.2 = true) ∧ rec.tofRoundTripTicks ≤ rec.maxProximityTicksAtSettle ∧ rec.maxProximityTicksAtSettle ≤ init.maxProximityTicks)
private theorem checkFloor_eq_holdsOnSettledRecord (st : SheState) (act : ActuationTurnProposal) (φ : SheFloor) : holdsOnSettledRecord φ (buildSettledRecord st act) = checkFloorOnActuation st.revertWindowSteps act φ := by cases φ <;> rfl
private theorem verifyPq_of_verifyShePq {p : PqHashParams} {pk : PqPublicKey} {msg : ByteArray} {sig : PqHashSig} (h : verifyShePqSig p pk msg sig = true) : verifyPqHashSig cshake256Suite p pk msg.data.toList sig = true := by simp only [verifyShePqSig, Bool.and_eq_true] at h; exact h.2
private theorem sheTraceInv_step {init cur next : SheState} {turn : SheTurn} (hInv : SheTraceInv init cur) (hStep : applySheTurn cur turn = .ok next) : SheTraceInv init next := by
  cases (applySheTurn_ok_iff_inductiveStep cur turn next).mp hStep with
  | settleActuation act hWidths hSeqLt _ hNoCbr hVer _ h100 _ hFlDig _ hTof hFloors hNulFresh hBud hCopy hSimpQc _ hCust =>
    have hReceipt := verifyCandidateComputation_sound hVer
    have hNulNotSettled : act.nullifier ∉ cur.settledOutboxActions.map SettledActuationRecord.nullifier := by rintro hMap; obtain ⟨r, hr, hEq⟩ := List.mem_map.mp hMap; exact hNulFresh (hEq ▸ hInv.settledInCons r hr)
    refine { floorsSub := hInv.floorsSub, seqMonoInit := by dsimp only; have := hInv.seqMonoInit; omega, proxLeInit := hInv.proxLeInit, pqParamsEq := hInv.pqParamsEq, custPksEq := hInv.custPksEq, simpPksEq := hInv.simpPksEq, threshEq := hInv.threshEq, totalEq := hInv.totalEq, epochMonoInit := hInv.epochMonoInit, revokedMono := hInv.revokedMono
             budgetConserve := by dsimp only; rw [settledTotalCost_append]; simp only [settledTotalCost, buildSettledRecord]; have := hInv.budgetConserve; omega
             consumedNodup := nodup_snoc hInv.consumedNodup hNulFresh
             settledNodup := by dsimp only; rw [List.map_append]; exact nodup_snoc hInv.settledNodup hNulNotSettled
             settledInCons := fun rec hrec => by
               dsimp only at hrec ⊢; rcases List.mem_append.mp hrec with hold | hnew
               · exact List.mem_append_left _ (hInv.settledInCons rec hold)
               · simp only [List.mem_singleton] at hnew; subst hnew; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
             seqPairwise := by dsimp only; rw [List.map_append]; refine pairwise_lt_snoc hInv.seqPairwise fun y hy => ?_; obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy; have := hInv.settledSeqBound r hr; dsimp only [buildSettledRecord]; omega
             settledSeqBound := fun rec hrec => by
               dsimp only at hrec ⊢; rcases List.mem_append.mp hrec with hold | hnew
               · have := hInv.settledSeqBound rec hold; omega
               · simp only [List.mem_singleton] at hnew; subst hnew; exact Nat.le_refl _
             settledSafe := fun rec hrec => by
               dsimp only at hrec ⊢; rcases List.mem_append.mp hrec with hold | hnew
               · exact hInv.settledSafe rec hold
               · simp only [List.mem_singleton] at hnew; subst hnew; right; dsimp only [buildSettledRecord]
                 refine ⟨by have := hInv.seqMonoInit; omega, hWidths.1, hNoCbr, hReceipt.logArityGe1, hReceipt.queriesPinned.2, h100, hFlDig, hInv.floorsSub, fun φ hφ => (checkFloor_eq_holdsOnSettledRecord cur act φ).trans (hFloors φ hφ), hCopy.2, hCopy.1, hSimpQc.1.1, hSimpQc.2.2.2.1, fun e he => ?_, pairwise_lt_implies_nodup hCust.2.1, ?_, fun s hs => ?_, fun s hs hIn => hCust.2.2.2.1 s hs (hInv.revokedMono s hIn), fun e he => ?_, hTof, hInv.proxLeInit⟩
                 · obtain ⟨pk, hPk, hV⟩ := hSimpQc.2.2.2.2.2 e he; exact ⟨pk, hInv.simpPksEq ▸ hPk, hInv.pqParamsEq ▸ verifyPq_of_verifyShePq hV⟩
                 · rw [List.length_map, ← hInv.threshEq]; exact hCust.2.2.2.2.2.2
                 · rw [← hInv.totalEq]; exact hCust.2.2.1 s hs
                 · obtain ⟨pk, hPk, hV⟩ := hCust.2.2.2.2.2.1 e he; exact ⟨pk, hInv.custPksEq ▸ hPk, hInv.pqParamsEq ▸ verifyPq_of_verifyShePq hV⟩ }
  | upgradeJudge up hNonReg _ _ _ hEpGt _ _ => exact { hInv with floorsSub := fun φ hφ => hNonReg φ (hInv.floorsSub hφ), epochMonoInit := by dsimp only; have := hInv.epochMonoInit; omega }
  | attenuateMandate rev _ hBudLe hProx _ => exact { hInv with proxLeInit := by dsimp only; have := hInv.proxLeInit; omega, revokedMono := fun r hr => mem_mergeRevokedCustodians_left _ _ (hInv.revokedMono r hr), budgetConserve := by dsimp only; have := hInv.budgetConserve; omega }
private theorem sheTraceInv_run {init cur endSt : SheState} {turns : List SheTurn} (hInv : SheTraceInv init cur) (hTrace : ValidSheTrace cur turns endSt) : SheTraceInv init endSt := by
  induction turns generalizing cur with | nil => simp only [ValidSheTrace] at hTrace; subst hTrace; exact hInv | cons _ _ ih => obtain ⟨stMid, hStep, hRest⟩ := hTrace; exact ih (sheTraceInv_step hInv hStep) hRest
theorem she_trace_end_to_end_safe_and_anti_vaz {initState endState : SheState} {turns : List SheTurn} (hGenesisActions : initState.settledOutboxActions = []) (hGenesisNullifiers : initState.consumedNullifiers = []) (hTrace : ValidSheTrace initState turns endState) :
    initState.activeSafetyAndPrivacyFloors ⊆ endState.activeSafetyAndPrivacyFloors ∧ List.Pairwise (· < ·) (endState.settledOutboxActions.map SettledActuationRecord.sensorSeq) ∧
    settledTotalCost endState.settledOutboxActions + endState.remainingMandateBudget ≤ initState.remainingMandateBudget ∧ (endState.settledOutboxActions.map SettledActuationRecord.nullifier).Nodup ∧ endState.consumedNullifiers.Nodup ∧
    ∀ rec ∈ endState.settledOutboxActions,
      initState.monoSensorSeq < rec.sensorSeq ∧ rec.sensorSeq ≤ endState.monoSensorSeq ∧ rec.sensorSealDigest.size = 32 ∧ rec.zkmlRegime ≠ .withdrawnCapacityBoundCbr ∧ 1 ≤ rec.zkmlLogArity ∧ rec.zkmlObservedQueries = rec.zkmlPinnedQueries ∧ 100000 ≤ rec.provenZkmlMilliBits ∧
      rec.boundFloorsDigest = floorsDigest rec.activeFloorsAtSettlement ∧ initState.activeSafetyAndPrivacyFloors ⊆ rec.activeFloorsAtSettlement ∧ (∀ φ ∈ initState.activeSafetyAndPrivacyFloors, holdsOnSettledRecord φ rec = true) ∧
      rec.dispatchedPayload = rec.privateFrameCopy ∧ rec.privateFrameCopy = rec.sharedRingAtCopy ∧ 3 * rec.simplexFaultyF + 1 ≤ rec.simplexCommitteeN ∧ rec.simplexCommitteeN - rec.simplexFaultyF ≤ rec.simplexQuorumCount ∧
      (∀ e ∈ rec.simplexQcSignatures, ∃ pk, initState.simplexValidatorPks[e.1]? = some pk ∧ verifyPqHashSig cshake256Suite initState.pqParams pk rec.simplexQcSigningMsg.data.toList e.2 = true) ∧
      rec.custodianSigners.Nodup ∧ initState.custodianThresholdT ≤ rec.custodianSigners.length ∧ (∀ s ∈ rec.custodianSigners, s < initState.custodianTotalN) ∧ (∀ s ∈ rec.custodianSigners, s ∉ initState.revokedCustodians) ∧
      (∀ e ∈ rec.custodianSignatures, ∃ pk, initState.custodianPks[e.1]? = some pk ∧ verifyPqHashSig cshake256Suite initState.pqParams pk rec.custodianSigningMsg.data.toList e.2 = true) ∧
      (∀ coerced : List Nat, coerced.length < initState.custodianThresholdT → ∃ h ∈ rec.custodianSigners, h ∉ coerced) ∧ rec.tofRoundTripTicks ≤ rec.maxProximityTicksAtSettle ∧ rec.maxProximityTicksAtSettle ≤ initState.maxProximityTicks := by
  have hInitInv : SheTraceInv initState initState := { floorsSub := fun _ h => h, seqMonoInit := Nat.le_refl _, proxLeInit := Nat.le_refl _, pqParamsEq := rfl, custPksEq := rfl, simpPksEq := rfl, threshEq := rfl, totalEq := rfl, epochMonoInit := Nat.le_refl _, revokedMono := fun _ h => h, budgetConserve := Nat.le_refl _, consumedNodup := (by rw [hGenesisNullifiers]; exact List.Pairwise.nil), settledNodup := (by rw [hGenesisActions]; exact List.Pairwise.nil), settledInCons := (by rw [hGenesisActions]; intro _ h; cases h), seqPairwise := (by rw [hGenesisActions]; exact List.Pairwise.nil), settledSeqBound := (by rw [hGenesisActions]; intro _ h; cases h), settledSafe := fun _ hr => .inl hr }
  have hEnd := sheTraceInv_run hInitInv hTrace
  have hBud : settledTotalCost endState.settledOutboxActions + endState.remainingMandateBudget ≤ initState.remainingMandateBudget := by have hb := hEnd.budgetConserve; rw [hGenesisActions] at hb; simpa [settledTotalCost] using hb
  refine ⟨hEnd.floorsSub, hEnd.seqPairwise, hBud, hEnd.settledNodup, hEnd.consumedNodup, fun rec hrec => ?_⟩
  rcases hEnd.settledSafe rec hrec with hInInit | hNew
  · rw [hGenesisActions] at hInInit; cases hInInit
  · obtain ⟨hSeq, hSealSz, hNoCbr, hArity, hQPin, h100, hFlDig, hFlSub, hHoldsAll, hDisp, hPriv, hSimp1, hSimp2, hSimpPq, hCustNd, hCustLen, hCustRange, hCustUnrev, hCustPq, hTof1, hTof2⟩ := hNew
    exact ⟨hSeq, hEnd.settledSeqBound rec hrec, hSealSz, hNoCbr, hArity, hQPin, h100, hFlDig, hFlSub, fun φ hφ => hHoldsAll φ (hFlSub hφ), hDisp, hPriv, hSimp1, hSimp2, hSimpPq, hCustNd, hCustLen, hCustRange, hCustUnrev, hCustPq, fun coerced hLt => coerced_subthreshold_coalition_omits_honest_signer hCustNd hCustLen hLt, hTof1, hTof2⟩
theorem she_trace_coupled_sel4_private_frame_safe {k₀ k₁ : KState} {cfg : IngressCfg} {da₀ : Nat} {ring d : ByteArray} {mid : List KEvent} (hU : VUnique k₀.maps) (hP₀ : translate k₀.maps (.cpu cfg.vpd) cfg.privV true = some da₀) (hInv : PrivInv k₀ cfg.vpd (da₀ / pageSize) k₁) (hRing : readVia k₁ cfg.vpd cfg.sharedV cfg.len = some ring) (hCopy : (translate k₁.maps (.cpu cfg.vpd) cfg.privV true).isSome = true) (hAdv : ∀ ev ∈ mid, ev.actor ≠ some cfg.vpd) (hD : readVia (runK (ingressCopy cfg k₁) mid) cfg.vpd (dispatchVaddr cfg) cfg.len = some d) {initState endState : SheState} {turns : List SheTurn} (hGenesisActions : initState.settledOutboxActions = []) (hGenesisNullifiers : initState.consumedNullifiers = []) (hTrace : ValidSheTrace initState turns endState) :
    d = ring ∧ PrivInv k₀ cfg.vpd (da₀ / pageSize) (runK (ingressCopy cfg k₁) mid) ∧ initState.activeSafetyAndPrivacyFloors ⊆ endState.activeSafetyAndPrivacyFloors ∧ ∀ rec ∈ endState.settledOutboxActions, rec.privateFrameCopy = d → rec.dispatchedPayload = ring := by
  obtain ⟨hdRing, hPrivAfter⟩ := copy_into_private_pd_frame_before_verify hU hP₀ hInv hRing hCopy mid hAdv hD
  obtain ⟨hFloors, _, _, _, _, hRecs⟩ := she_trace_end_to_end_safe_and_anti_vaz hGenesisActions hGenesisNullifiers hTrace
  exact ⟨hdRing, hPrivAfter, hFloors, fun rec hrec hEqD => (hRecs rec hrec).2.2.2.2.2.2.2.2.2.2.1.trans (hEqD.trans hdRing)⟩
private theorem walkMerkle_out_len (suite : TweakableHashSuite) (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) {hi ni li : Nat} {lf out : List UInt8} {p : List (List UInt8)} (hlf : lf.length ≤ 32) (hw : walkMerkleAuthPath suite pkSeed layer tree nodeKind hi ni li lf p = some out) : out.length ≤ 32 := by
  cases hi with
  | zero => cases p with | nil => simp [walkMerkleAuthPath] at hw; exact hw ▸ hlf | cons _ _ => cases hw
  | succ hi' => cases p with
    | nil => cases hw
    | cons s rs =>
      simp only [walkMerkleAuthPath] at hw; split at hw
      · cases hrec : walkMerkleAuthPath suite pkSeed layer tree nodeKind hi' (2 * ni) li lf rs with | none => rw [hrec] at hw; cases hw | some sub => rw [hrec] at hw; simp only [Option.some.injEq] at hw; subst hw; exact Nat.le_of_eq (thCall_length _ _ _ _ _)
      · cases hrec : walkMerkleAuthPath suite pkSeed layer tree nodeKind hi' (2 * ni + 1) (li - 2 ^ hi') lf rs with | none => rw [hrec] at hw; cases hw | some sub => rw [hrec] at hw; simp only [Option.some.injEq] at hw; subst hw; exact Nat.le_of_eq (thCall_length _ _ _ _ _)
def extractMerklePathCollision (suite : TweakableHashSuite) (maxBytes : Nat) (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) :
    ∀ (h nodeIdx localIdx : Nat) (leaf₁ leaf₂ : List UInt8) (path₁ path₂ : List (List UInt8)) (root : List UInt8), leaf₁ ≠ leaf₂ →
      (∀ (d ni : Nat) (l r : List UInt8), l.length ≤ 32 → r.length ≤ 32 → (thPreimage tagThH pkSeed ⟨layer, tree, nodeKind, 0, UInt32.ofNat d, UInt32.ofNat ni⟩ [l, r]).length ≤ maxBytes) →
      leaf₁.length ≤ 32 → leaf₂.length ≤ 32 → (∀ s ∈ path₁, s.length ≤ 32) → (∀ s ∈ path₂, s.length ≤ 32) →
      walkMerkleAuthPath suite pkSeed layer tree nodeKind h nodeIdx localIdx leaf₁ path₁ = some root → walkMerkleAuthPath suite pkSeed layer tree nodeKind h nodeIdx localIdx leaf₂ path₂ = some root → HashCollisionWitness suite.rawHash maxBytes
  | 0, _, _, _, _, [], [], _, hNe, _, _, _, _, _, hW1, hW2 => by simp only [walkMerkleAuthPath, Option.some.injEq] at hW1 hW2; exact False.elim (hNe (hW1.trans hW2.symm))
  | 0, _, _, _, _, _ :: _, _, _, _, _, _, _, _, _, hW1, _ => by cases hW1
  | 0, _, _, _, _, _, _ :: _, _, _, _, _, _, _, _, _, hW2 => by cases hW2
  | _ + 1, _, _, _, _, [], _, _, _, _, _, _, _, _, hW1, _ => by cases hW1
  | _ + 1, _, _, _, _, _, [], _, _, _, _, _, _, _, _, hW2 => by cases hW2
  | h + 1, nodeIdx, localIdx, leaf₁, leaf₂, sib₁ :: rest₁, sib₂ :: rest₂, root, hNe, hBound, hl1, hl2, hp1, hp2, hW1, hW2 => by
    have hSib1 := hp1 sib₁ List.mem_cons_self; have hSib2 := hp2 sib₂ List.mem_cons_self; have hRest1 : ∀ s ∈ rest₁, s.length ≤ 32 := fun s hs => hp1 s (List.mem_cons_of_mem _ hs); have hRest2 : ∀ s ∈ rest₂, s.length ≤ 32 := fun s hs => hp2 s (List.mem_cons_of_mem _ hs)
    simp only [walkMerkleAuthPath] at hW1 hW2
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceIte] at hW1 hW2
      cases hRec1 : walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx) localIdx leaf₁ rest₁ with
      | none => rw [hRec1] at hW1; cases hW1
      | some sub₁ => cases hRec2 : walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx) localIdx leaf₂ rest₂ with
        | none => rw [hRec2] at hW2; cases hW2
        | some sub₂ =>
          rw [hRec1] at hW1; rw [hRec2] at hW2; simp only [Option.some.injEq] at hW1 hW2
          if hSubEq : sub₁ = sub₂ then exact extractMerklePathCollision suite maxBytes pkSeed layer tree nodeKind h (2 * nodeIdx) localIdx leaf₁ leaf₂ rest₁ rest₂ sub₁ hNe hBound hl1 hl2 hRest1 hRest2 hRec1 (hSubEq ▸ hRec2)
          else match thCall_binds_or_collision suite maxBytes (hBound (h + 1) nodeIdx sub₁ sib₁ (walkMerkle_out_len _ _ _ _ _ hl1 hRec1) hSib1) (hBound (h + 1) nodeIdx sub₂ sib₂ (walkMerkle_out_len _ _ _ _ _ hl2 hRec2) hSib2) (hW1.trans hW2.symm) with | .inl ⟨_, _, _, hArgs⟩ => exact False.elim (hSubEq (by injection hArgs)) | .inr col => exact col
    · simp only [hHalf, ↓reduceIte] at hW1 hW2
      cases hRec1 : walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf₁ rest₁ with
      | none => rw [hRec1] at hW1; cases hW1
      | some sub₁ => cases hRec2 : walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf₂ rest₂ with
        | none => rw [hRec2] at hW2; cases hW2
        | some sub₂ =>
          rw [hRec1] at hW1; rw [hRec2] at hW2; simp only [Option.some.injEq] at hW1 hW2
          if hSubEq : sub₁ = sub₂ then exact extractMerklePathCollision suite maxBytes pkSeed layer tree nodeKind h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf₁ leaf₂ rest₁ rest₂ sub₁ hNe hBound hl1 hl2 hRest1 hRest2 hRec1 (hSubEq ▸ hRec2)
          else match thCall_binds_or_collision suite maxBytes (hBound (h + 1) nodeIdx sib₁ sub₁ hSib1 (walkMerkle_out_len _ _ _ _ _ hl1 hRec1)) (hBound (h + 1) nodeIdx sib₂ sub₂ hSib2 (walkMerkle_out_len _ _ _ _ _ hl2 hRec2)) (hW1.trans hW2.symm) with | .inl ⟨_, _, _, hArgs⟩ => exact False.elim (hSubEq (by injection hArgs with _ h2; injection h2)) | .inr col => exact col
inductive ShePqForgeryBreak (params : PqHashParams) (pkSeed : List UInt8) (maxBytes : Nat) where
  | wotsBackwardInversion (w : WotsBackwardInversionWitness cshake256Suite pkSeed) | tweakableHashCollision (c : HashCollisionWitness cshake256Suite.rawHash maxBytes)
  | tswDigitCollision (hmsg₁ hmsg₂ : List UInt8) (hNe : hmsg₁ ≠ hmsg₂) (hSameDigits : extractBaseWDigits params.w params.ell1 hmsg₁ = extractBaseWDigits params.w params.ell1 hmsg₂)
def extractSheCeremonyPqForgery (params : PqHashParams) (maxBytes : Nat) (pk : PqPublicKey) (msg₁ msg₂ : ByteArray) (honestSig forgedSig : PqHashSig) (hStateful : params.statefulLeanSig = true) (hSingleLayer : params.numLayers = 1) (hMsgNe : msg₁ ≠ msg₂) (hSameLeaf : forgedSig.leafGlobalIdx = honestSig.leafGlobalIdx) (hVer₁ : verifyShePqSig params pk msg₁ honestSig = true) (hVer₂ : verifyShePqSig params pk msg₂ forgedSig = true)
    (hBound : ∀ (tag : List UInt8) (a : HashAdrs) (args : List (List UInt8)), tag ∈ [tagThF, tagThH, tagThTl, tagHMsg, tagHPre] → args.length ≤ Nat.max params.ell1 4 → (∀ x ∈ args, x.length ≤ Nat.max 32 (Nat.max msg₁.size msg₂.size)) → (thPreimage tag pk.pkSeed a args).length ≤ maxBytes) : ShePqForgeryBreak params pk.pkSeed maxBytes := by
  have hCan1 : checkPqSigCanonical params pk honestSig = true := (verifyShePqSig_sound hVer₁).2.1
  have hCan2 : checkPqSigCanonical params pk forgedSig = true := (verifyShePqSig_sound hVer₂).2.1
  have hPq1 := verifyPq_of_verifyShePq hVer₁; have hPq2 := verifyPq_of_verifyShePq hVer₂
  have hLen1 : honestSig.layerSigs.length = 1 := by simp only [checkPqSigCanonical, Bool.and_eq_true, decide_eq_true_eq] at hCan1; omega
  have hLen2 : forgedSig.layerSigs.length = 1 := by simp only [checkPqSigCanonical, Bool.and_eq_true, decide_eq_true_eq] at hCan2; omega
  match hL1 : honestSig.layerSigs, hL2 : forgedSig.layerSigs with
  | [ls₁], [ls₂] =>
    have hLeafLt1 : honestSig.leafGlobalIdx < 2 ^ params.subtreeHeight := by
      unfold verifyPqHashSig at hPq1
      split at hPq1; · cases hPq1
      split at hPq1; · cases hPq1
      split at hPq1; · cases hPq1
      rename_i hLt; simp only [hSingleLayer, Nat.one_mul, Bool.not_eq_true', decide_eq_false_iff_not] at hLt; exact Decidable.of_not_not hLt
    have hDiv0 : honestSig.leafGlobalIdx / 2 ^ params.subtreeHeight = 0 := Nat.div_eq_of_lt hLeafLt1; let kp := honestSig.leafGlobalIdx % 2 ^ params.subtreeHeight
    let mu₁ := thPreHash cshake256Suite pk.pkSeed pk.pkRoot msg₁.data.toList; let mu₂ := thPreHash cshake256Suite pk.pkSeed pk.pkRoot msg₂.data.toList
    let hmsg₁ := thHashMsg cshake256Suite honestSig.rRand pk.pkSeed pk.pkRoot mu₁ 0 0 ls₁.tswCtr; let hmsg₂ := thHashMsg cshake256Suite forgedSig.rRand pk.pkSeed pk.pkRoot mu₂ 0 0 ls₂.tswCtr
    let d₁ := extractBaseWDigits params.w params.ell1 hmsg₁; let d₂ := extractBaseWDigits params.w params.ell1 hmsg₂
    let wots₁ := recoverWotsPkFromSig cshake256Suite params pk.pkSeed 0 0 kp d₁ ls₁.wotsChains; let wots₂ := recoverWotsPkFromSig cshake256Suite params pk.pkSeed 0 0 kp d₂ ls₂.wotsChains
    have hExtract (msg : ByteArray) (sig : PqHashSig) (ls : LayerXmssSig) (hLs : sig.layerSigs = [ls]) (hLeaf : sig.leafGlobalIdx = honestSig.leafGlobalIdx) (hV : verifyPqHashSig cshake256Suite params pk msg.data.toList sig = true) :
        let mu := thPreHash cshake256Suite pk.pkSeed pk.pkRoot msg.data.toList; let hm := thHashMsg cshake256Suite sig.rRand pk.pkSeed pk.pkRoot mu 0 0 ls.tswCtr; let dg := extractBaseWDigits params.w params.ell1 hm
        checkTargetSum params.w params.ell1 params.targetSum dg = true ∧ walkMerkleAuthPath cshake256Suite pk.pkSeed 0 0 .tree params.subtreeHeight 0 kp (recoverWotsPkFromSig cshake256Suite params pk.pkSeed 0 0 kp dg ls.wotsChains) ls.authPath = some pk.pkRoot := by
      unfold verifyPqHashSig at hV; split at hV; · cases hV
      split at hV; · cases hV
      split at hV; · cases hV
      dsimp only at hV; split at hV; · cases hV
      rw [hLs, hLeaf] at hV
      cases hHt : verifyHypertreeLayers cshake256Suite params pk.pkSeed pk.pkRoot sig.rRand 0 honestSig.leafGlobalIdx (thPreHash cshake256Suite pk.pkSeed pk.pkRoot msg.data.toList) [ls] with
      | none => rw [hHt] at hV; cases hV
      | some topRoot =>
        rw [hHt] at hV; simp only [decide_eq_true_eq] at hV; subst hV; unfold verifyHypertreeLayers at hHt; dsimp only at hHt; rw [hDiv0] at hHt
        split at hHt; · cases hHt
        rename_i hNotTsw; split at hHt; · cases hHt
        split at hHt; · cases hHt
        rename_i rt hWk; simp only [verifyHypertreeLayers, Option.some.injEq] at hHt; subst hHt
        exact ⟨by cases hc : checkTargetSum params.w params.ell1 params.targetSum _ with | true => rfl | false => simp [hc] at hNotTsw, hWk⟩
    have hE1 := hExtract msg₁ honestSig ls₁ hL1 rfl hPq1; have hE2 := hExtract msg₂ forgedSig ls₂ hL2 hSameLeaf hPq2
    have hFrame1 : checkLayerSigFraming params ls₁ = true := by simp only [checkPqSigCanonical, hL1, List.all_cons, List.all_nil, Bool.and_eq_true] at hCan1; exact hCan1.1.2.1.2
    have hFrame2 : checkLayerSigFraming params ls₂ = true := by simp only [checkPqSigCanonical, hL2, List.all_cons, List.all_nil, Bool.and_eq_true] at hCan2; exact hCan2.1.2.1.2
    have hChLen1 : ∀ x ∈ ls₁.wotsChains, x.length ≤ 32 := by simp only [checkLayerSigFraming, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hFrame1; exact fun x hx => Nat.le_of_eq (hFrame1.1.1.2 x hx)
    have hChLen2 : ∀ x ∈ ls₂.wotsChains, x.length ≤ 32 := by simp only [checkLayerSigFraming, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hFrame2; exact fun x hx => Nat.le_of_eq (hFrame2.1.1.2 x hx)
    have hPathLen1 : ∀ s ∈ ls₁.authPath, s.length ≤ 32 := by simp only [checkLayerSigFraming, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hFrame1; exact fun s hs => Nat.le_of_eq (hFrame1.2 s hs)
    have hPathLen2 : ∀ s ∈ ls₂.authPath, s.length ≤ 32 := by simp only [checkLayerSigFraming, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hFrame2; exact fun s hs => Nat.le_of_eq (hFrame2.2 s hs)
    have hMax4 : ∀ k ≤ 4, k ≤ Nat.max params.ell1 4 := fun k hk => Nat.le_trans hk (Nat.le_max_right _ _); have hMax32 : ∀ k ≤ 32, k ≤ Nat.max 32 (Nat.max msg₁.size msg₂.size) := fun k hk => Nat.le_trans hk (Nat.le_max_left _ _)
    if hWotsNe : wots₁ ≠ wots₂ then
      exact .tweakableHashCollision (extractMerklePathCollision cshake256Suite maxBytes pk.pkSeed 0 0 .tree params.subtreeHeight 0 kp wots₁ wots₂ ls₁.authPath ls₂.authPath pk.pkRoot hWotsNe
        (fun d ni l r hl hr => hBound tagThH _ [l, r] (by simp) (hMax4 2 (by decide)) (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> exact hMax32 _ (by omega)))
        (Nat.le_of_eq (thCall_length _ _ _ _ _)) (Nat.le_of_eq (thCall_length _ _ _ _ _)) hPathLen1 hPathLen2 hE1.2 hE2.2)
    else
      have hWotsEq : wots₂ = wots₁ := (Decidable.of_not_not hWotsNe).symm
      if hDigNe : d₁ ≠ d₂ then
        have hEndLen (d : List Nat) (chs : List (List UInt8)) (hCh : ∀ x ∈ chs, x.length ≤ 32) : ∀ x ∈ recoverWotsEndpoints cshake256Suite params pk.pkSeed 0 0 kp d chs, x.length ≤ 32 := by
          intro x hx; simp only [recoverWotsEndpoints, List.mem_map] at hx; obtain ⟨r, _, rfl⟩ := hx; apply wotsChainSteps_len_32
          by_cases hr : r < chs.length
          · rw [list_getD_eq_getElem chs [] hr]; exact hCh _ (List.getElem_mem hr)
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hr)]; simp
        match extractPqHashForgery cshake256Suite params maxBytes pk.pkSeed 0 0 kp d₁ d₂ ls₁.wotsChains ls₂.wotsChains hE1.1 hE2.1 hDigNe hWotsEq hChLen1 hChLen2
            (hBound tagThTl _ _ (by simp) (by simp [recoverWotsEndpoints]; exact Nat.le_max_left _ _) (fun x hx => hMax32 _ (hEndLen d₂ ls₂.wotsChains hChLen2 x hx)))
            (hBound tagThTl _ _ (by simp) (by simp [recoverWotsEndpoints]; exact Nat.le_max_left _ _) (fun x hx => hMax32 _ (hEndLen d₁ ls₁.wotsChains hChLen1 x hx)))
            (fun chain s u' hu' => hBound tagThF _ [u'] (by simp) (hMax4 1 (by decide)) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hMax32 _ hu')) with
        | .inl inv => exact .wotsBackwardInversion inv | .inr col => exact .tweakableHashCollision col
      else
        have hDigEq : d₁ = d₂ := Decidable.of_not_not hDigNe
        if hHmNe : hmsg₁ ≠ hmsg₂ then exact .tswDigitCollision hmsg₁ hmsg₂ hHmNe hDigEq
        else
          have hHmEq : hmsg₁ = hmsg₂ := Decidable.of_not_not hHmNe
          have hRR1 : honestSig.rRand.length = 32 := by simp only [checkPqSigCanonical, Bool.and_eq_true, decide_eq_true_eq] at hCan1; exact hCan1.1.1.1.1.1.2
          have hRR2 : forgedSig.rRand.length = 32 := by simp only [checkPqSigCanonical, Bool.and_eq_true, decide_eq_true_eq] at hCan2; exact hCan2.1.1.1.1.1.2
          have hPkR : pk.pkRoot.length = 32 := by simp only [checkPqSigCanonical, Bool.and_eq_true, decide_eq_true_eq] at hCan1; exact hCan1.1.1.1.1.1.1.2
          have hHmBnd (rr mu : List UInt8) (ctr : Nat) (hrr : rr.length = 32) (hmu : mu.length = 32) : (thPreimage tagHMsg pk.pkSeed ⟨0, 0, .wotsHash, 0, 0, UInt32.ofNat ctr⟩ [rr, pk.pkRoot, mu, be 4 ctr]).length ≤ maxBytes :=
            hBound tagHMsg _ _ (by simp) (hMax4 4 (by decide)) (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl
              · exact hMax32 _ (by omega)
              · exact hMax32 _ (by omega)
              · exact hMax32 _ (by omega)
              · rw [length_be]; exact hMax32 _ (by decide))
          match thCall_binds_or_collision cshake256Suite maxBytes (hHmBnd honestSig.rRand mu₁ ls₁.tswCtr hRR1 (thCall_length _ _ _ _ _)) (hHmBnd forgedSig.rRand mu₂ ls₂.tswCtr hRR2 (thCall_length _ _ _ _ _)) hHmEq with
          | .inr col => exact .tweakableHashCollision col
          | .inl ⟨_, _, _, hArgs⟩ =>
            have hMuEq : mu₁ = mu₂ := by injection hArgs with _ h2; injection h2 with _ h3; injection h3 with h4
            have hPreBnd (m : ByteArray) (hm : m.data.toList.length ≤ Nat.max msg₁.size msg₂.size) : (thPreimage tagHPre pk.pkSeed zeroAdrs [pk.pkRoot, m.data.toList]).length ≤ maxBytes :=
              hBound tagHPre _ _ (by simp) (hMax4 2 (by decide)) (fun x hx => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl
                · exact hMax32 _ (by omega)
                · exact Nat.le_trans hm (Nat.le_max_right _ _))
            match thCall_binds_or_collision cshake256Suite maxBytes (hPreBnd msg₁ (by rw [Array.length_toList]; exact Nat.le_max_left _ _)) (hPreBnd msg₂ (by rw [Array.length_toList]; exact Nat.le_max_right _ _)) hMuEq with
            | .inr col => exact .tweakableHashCollision col
            | .inl ⟨_, _, _, hPArgs⟩ => exact False.elim (hMsgNe (byteArray_eq_of_toList_eq (by injection hPArgs with _ h2; injection h2)))
  | [], _ => exact False.elim (by rw [hL1] at hLen1; cases hLen1)
  | _ :: _ :: _, _ => exact False.elim (by rw [hL1] at hLen1; cases hLen1)
  | [_], [] => exact False.elim (by rw [hL2] at hLen2; cases hLen2)
  | [_], _ :: _ :: _ => exact False.elim (by rw [hL2] at hLen2; cases hLen2)
theorem she_ceremony_pq_quorum_unforgeable (st st' : SheState) (turn : SheTurn) (hStep : applySheTurn st turn = .ok st') :
    (match turn with
     | .proposeAndSettleActuation act => let msg := sheCustodianActuationMsg st act
       List.Pairwise (· < ·) (act.custodianSignatures.map Prod.fst) ∧ st.custodianThresholdT ≤ act.custodianSignatures.length ∧
       (∀ e ∈ act.custodianSignatures, e.1 < st.custodianTotalN ∧ e.1 ∉ st.revokedCustodians ∧ ∃ pk, st.custodianPks[e.1]? = some pk ∧ verifyPqHashSig cshake256Suite st.pqParams pk msg.data.toList e.2 = true) ∧
       (∀ coerced : List Nat, coerced.length < st.custodianThresholdT → ∃ e ∈ act.custodianSignatures, e.1 ∉ coerced ∧ e.1 ∉ st.revokedCustodians ∧ ∃ pk, st.custodianPks[e.1]? = some pk ∧ verifyShePqSig st.pqParams pk msg e.2 = true)
     | .upgradeHabitatJudge up => let msg := sheCustodianUpgradeMsg st up
       List.Pairwise (· < ·) (up.custodianSignatures.map Prod.fst) ∧ st.custodianThresholdT ≤ up.custodianSignatures.length ∧
       (∀ e ∈ up.custodianSignatures, e.1 < st.custodianTotalN ∧ e.1 ∉ st.revokedCustodians ∧ ∃ pk, st.custodianPks[e.1]? = some pk ∧ verifyPqHashSig cshake256Suite st.pqParams pk msg.data.toList e.2 = true) ∧
       (∀ coerced : List Nat, coerced.length < st.custodianThresholdT → ∃ e ∈ up.custodianSignatures, e.1 ∉ coerced ∧ e.1 ∉ st.revokedCustodians ∧ ∃ pk, st.custodianPks[e.1]? = some pk ∧ verifyShePqSig st.pqParams pk msg e.2 = true)
     | .revokeOrAttenuateMandate _ => True) ∧
    (∀ (maxBytes : Nat) (pk : PqPublicKey) (msg₁ msg₂ : ByteArray) (honestSig forgedSig : PqHashSig), msg₁ ≠ msg₂ → forgedSig.leafGlobalIdx = honestSig.leafGlobalIdx →
      verifyShePqSig st.pqParams pk msg₁ honestSig = true → verifyShePqSig st.pqParams pk msg₂ forgedSig = true →
      (∀ (tag : List UInt8) (a : HashAdrs) (args : List (List UInt8)), tag ∈ [tagThF, tagThH, tagThTl, tagHMsg, tagHPre] → args.length ≤ Nat.max st.pqParams.ell1 4 → (∀ x ∈ args, x.length ≤ Nat.max 32 (Nat.max msg₁.size msg₂.size)) → (thPreimage tag pk.pkSeed a args).length ≤ maxBytes) →
      Nonempty (ShePqForgeryBreak st.pqParams pk.pkSeed maxBytes)) := by
  refine ⟨?_, fun maxBytes pk m₁ m₂ hSig fSig hNe hLf hV1 hV2 hBnd => ?_⟩
  · have hQHelper (msg : ByteArray) (sigs : List (Nat × PqHashSig)) (hQ : ValidPqQuorumProp st msg sigs) :
        List.Pairwise (· < ·) (sigs.map Prod.fst) ∧ st.custodianThresholdT ≤ sigs.length ∧
        (∀ e ∈ sigs, e.1 < st.custodianTotalN ∧ e.1 ∉ st.revokedCustodians ∧ ∃ pk, st.custodianPks[e.1]? = some pk ∧ verifyPqHashSig cshake256Suite st.pqParams pk msg.data.toList e.2 = true) ∧
        (∀ coerced : List Nat, coerced.length < st.custodianThresholdT → ∃ e ∈ sigs, e.1 ∉ coerced ∧ e.1 ∉ st.revokedCustodians ∧ ∃ pk, st.custodianPks[e.1]? = some pk ∧ verifyShePqSig st.pqParams pk msg e.2 = true) := by
      obtain ⟨_, hInc, hRng, hUnrev, _, hVer, hLen⟩ := hQ; refine ⟨hInc, hLen, fun e he => ?_, fun coerced hLt => ?_⟩
      · obtain ⟨pk, hPk, hV⟩ := hVer e he; exact ⟨hRng e.1 (List.mem_map.mpr ⟨e, he, rfl⟩), hUnrev e.1 (List.mem_map.mpr ⟨e, he, rfl⟩), pk, hPk, verifyPq_of_verifyShePq hV⟩
      · obtain ⟨h, hMem, hNotC⟩ := coerced_subthreshold_coalition_omits_honest_signer (pairwise_lt_implies_nodup hInc) (by rw [List.length_map]; exact hLen) hLt; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hMem; exact ⟨e, he, hNotC, hUnrev e.1 (List.mem_map.mpr ⟨e, he, rfl⟩), hVer e he⟩
    cases (applySheTurn_ok_iff_inductiveStep st turn st').mp hStep with | settleActuation act _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hCust => exact hQHelper _ _ hCust | upgradeJudge up _ _ _ _ _ hCust _ => exact hQHelper _ _ hCust | attenuateMandate => trivial
  · have hPol := (verifyShePqSig_sound hV1).1; unfold shePqParamsValid at hPol; simp only [Bool.and_eq_true, beq_iff_eq] at hPol
    exact ⟨extractSheCeremonyPqForgery st.pqParams maxBytes pk m₁ m₂ hSig fSig hPol.1.2 hPol.1.1.2 hNe hLf hV1 hV2 hBnd⟩
/-! ## 5. `sheCeremonyJudge` (`Obend.Judge`) & Constructive Inhabitedness Witnesses -/
structure SheStateWellFormed (st : SheState) : Prop where
  judgeDigest32 : st.habitatJudgeDigest.size = 32
  weightsRoot32 : st.pinnedModelWeightsRoot.size = 32
  suiteDigest32 : st.pinnedZkmlSuiteDigest.size = 32
  genesisHistoryEmpty : st.settledOutboxActions = [] ∧ st.consumedNullifiers = [] ∧ st.consumedCustodianLeaves = [] ∧ st.consumedSimplexLeaves = []
  floorsNodup : st.activeSafetyAndPrivacyFloors.Nodup
  hasBedrock : ∃ φ ∈ st.activeSafetyAndPrivacyFloors, φ.isBedrock = true
  floorsWf : ∀ φ ∈ st.activeSafetyAndPrivacyFloors, φ.wellFormed = true
  pqParamsValid : shePqParamsValid st.pqParams = true
  custPksValid : st.custodianPks.length = st.custodianTotalN ∧ st.custodianPks.Nodup ∧ (∀ pk ∈ st.custodianPks, pk.pkSeed.length = 32 ∧ pk.pkRoot.length = 32)
  simpPksValid : 0 < st.simplexValidatorPks.length ∧ st.simplexValidatorPks.Nodup ∧ (∀ pk ∈ st.simplexValidatorPks, pk.pkSeed.length = 32 ∧ pk.pkRoot.length = 32) ∧ (∀ pk ∈ st.custodianPks, pk ∉ st.simplexValidatorPks)
  thresholdValid : 1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN
  proximityPos : 0 < st.maxProximityTicks
def checkSheStateWellFormed (st : SheState) : Bool :=
  decide (st.habitatJudgeDigest.size = 32 ∧ st.pinnedModelWeightsRoot.size = 32 ∧ st.pinnedZkmlSuiteDigest.size = 32) &&
  st.settledOutboxActions.isEmpty && st.consumedNullifiers.isEmpty && st.consumedCustodianLeaves.isEmpty && st.consumedSimplexLeaves.isEmpty &&
  checkFloorNodup st.activeSafetyAndPrivacyFloors && st.activeSafetyAndPrivacyFloors.any SheFloor.isBedrock && st.activeSafetyAndPrivacyFloors.all SheFloor.wellFormed && shePqParamsValid st.pqParams && decide (st.custodianPks.length = st.custodianTotalN) && checkListNodup st.custodianPks && st.custodianPks.all (fun pk => decide (pk.pkSeed.length = 32 ∧ pk.pkRoot.length = 32)) && decide (0 < st.simplexValidatorPks.length) && checkListNodup st.simplexValidatorPks && st.simplexValidatorPks.all (fun pk => decide (pk.pkSeed.length = 32 ∧ pk.pkRoot.length = 32)) && st.custodianPks.all (fun pk => !st.simplexValidatorPks.contains pk) && decide (1 ≤ st.custodianThresholdT ∧ st.custodianThresholdT ≤ st.custodianTotalN) && decide (0 < st.maxProximityTicks)
private theorem not_contains_iff_not_mem {α : Type} [DecidableEq α] (xs : List α) (x : α) : (!xs.contains x) = true ↔ x ∉ xs := by
  cases hc : xs.contains x with | true => simp [List.contains_iff_mem.mp hc] | false => exact ⟨fun _ hm => Bool.false_ne_true (hc.symm.trans (List.contains_iff_mem.mpr hm)), fun _ => rfl⟩
theorem checkSheStateWellFormed_iff (st : SheState) : checkSheStateWellFormed st = true ↔ SheStateWellFormed st := by
  unfold checkSheStateWellFormed; simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, checkListNodup_iff, List.any_eq_true, List.all_eq_true, not_contains_iff_not_mem]
  exact ⟨fun ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSz, hA⟩, hN⟩, hCL⟩, hSL⟩, hFlNd⟩, hBed⟩, hFlWf⟩, hPq⟩, hCN⟩, hCNd⟩, hCPk⟩, hSPos⟩, hSNd⟩, hSPk⟩, hDisj⟩, hTh⟩, hProx⟩ => ⟨hSz.1, hSz.2.1, hSz.2.2, ⟨hA, hN, hCL, hSL⟩, hFlNd, hBed, hFlWf, hPq, ⟨hCN, hCNd, hCPk⟩, ⟨hSPos, hSNd, hSPk, hDisj⟩, hTh, hProx⟩,
         fun h => ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.judgeDigest32, h.weightsRoot32, h.suiteDigest32⟩, h.genesisHistoryEmpty.1⟩, h.genesisHistoryEmpty.2.1⟩, h.genesisHistoryEmpty.2.2.1⟩, h.genesisHistoryEmpty.2.2.2⟩, h.floorsNodup⟩, h.hasBedrock⟩, h.floorsWf⟩, h.pqParamsValid⟩, h.custPksValid.1⟩, h.custPksValid.2.1⟩, h.custPksValid.2.2⟩, h.simpPksValid.1⟩, h.simpPksValid.2.1⟩, h.simpPksValid.2.2.1⟩, h.simpPksValid.2.2.2⟩, h.thresholdValid⟩, h.proximityPos⟩⟩
inductive InductiveSheTrace : SheState → List SheTurn → SheState → Prop where
  | nil (st : SheState) : InductiveSheTrace st [] st | cons {st stMid stEnd : SheState} {t : SheTurn} {ts : List SheTurn} : InductiveSheStep st t stMid → InductiveSheTrace stMid ts stEnd → InductiveSheTrace st (t :: ts) stEnd
theorem inductiveSheTrace_iff_validSheTrace : ∀ {turns : List SheTurn} {st endSt : SheState}, InductiveSheTrace st turns endSt ↔ ValidSheTrace st turns endSt
  | [], st, _ => by simp only [ValidSheTrace]; exact ⟨fun h => by cases h; rfl, fun h => h ▸ .nil st⟩
  | _ :: _, _, _ => by simp only [ValidSheTrace]; exact ⟨fun h => by cases h with | cons hs hr => exact ⟨_, (applySheTurn_ok_iff_inductiveStep _ _ _).mpr hs, inductiveSheTrace_iff_validSheTrace.mp hr⟩, fun ⟨_, hOk, hr⟩ => .cons ((applySheTurn_ok_iff_inductiveStep _ _ _).mp hOk) (inductiveSheTrace_iff_validSheTrace.mpr hr)⟩
structure SheCeremonyObj where
  initState : SheState
  turns : List SheTurn
  targetFloors : List SheFloor
  deriving DecidableEq
structure CeremonyMeaning (o : SheCeremonyObj) (endSt : SheState) : Prop where
  wfInit : SheStateWellFormed o.initState
  validTrace : InductiveSheTrace o.initState o.turns endSt
  achievesFloors : ∀ φ ∈ o.targetFloors, φ ∈ endSt.activeSafetyAndPrivacyFloors
@[expose] def sheRefusalRefutes : SheRefusal → Bool | .terminalStateMismatch => false | _ => true
def checkSheCeremony (grade : Nat) (o : SheCeremonyObj) (certEnd : SheState) : Judge.Verdict SheRefusal :=
  if grade < o.turns.length then .uncovered
  else if !checkSheStateWellFormed o.initState then .refused .malformedInitialState []
  else match runSheTurns o.initState o.turns with
    | .error (idx, r) => .refused (match r with | .terminalStateMismatch => .malformedInitialState | other => other) [idx]
    | .ok computedEnd =>
      match o.targetFloors.find? (fun φ => !computedEnd.activeSafetyAndPrivacyFloors.contains φ) with
      | some missing => .refused (.missingTargetFloor missing) []
      | none => if computedEnd == certEnd then .ok else .refused .terminalStateMismatch []
instance sheCeremonyJudge : Judge SheCeremonyObj SheState where
  Clause := SheRefusal
  Meaning := CeremonyMeaning
  check := checkSheCeremony
  refutes := sheRefusalRefutes
  sound {r o c} h := by
    unfold checkSheCeremony at h; split at h; · cases h
    split at h; · cases h
    rename_i hWfNot; have hWfBool : checkSheStateWellFormed o.initState = true := by cases hc : checkSheStateWellFormed o.initState with | true => rfl | false => simp [hc] at hWfNot
    cases hRun : runSheTurns o.initState o.turns with
    | error _ => rw [hRun] at h; cases h
    | ok compEnd =>
      rw [hRun] at h; dsimp only at h
      cases hMiss : o.targetFloors.find? (fun φ => !compEnd.activeSafetyAndPrivacyFloors.contains φ) with
      | some _ => rw [hMiss] at h; cases h
      | none =>
        rw [hMiss] at h; dsimp only at h; cases hEq : compEnd == c with
        | false => simp [hEq] at h
        | true =>
          have hCompEq := beq_iff_eq.mp hEq; subst hCompEq; refine ⟨(checkSheStateWellFormed_iff _).mp hWfBool, inductiveSheTrace_iff_validSheTrace.mpr ((runSheTurns_ok_iff _ _ _).mp hRun), fun φ hφ => ?_⟩
          have hf := List.find?_eq_none.mp hMiss φ hφ; cases hc : compEnd.activeSafetyAndPrivacyFloors.contains φ with | true => exact List.contains_iff_mem.mp hc | false => rw [hc] at hf; exact absurd rfl hf
  refuted {r o c k p} h hr c' hm := by
    unfold checkSheCeremony at h; split at h; · cases h
    split at h
    · rename_i hNotWf; simp [(checkSheStateWellFormed_iff _).mpr hm.wfInit] at hNotWf
    · rw [(runSheTurns_ok_iff _ _ _).mpr (inductiveSheTrace_iff_validSheTrace.mp hm.validTrace)] at h; dsimp only at h
      cases hMiss : o.targetFloors.find? (fun φ => !c'.activeSafetyAndPrivacyFloors.contains φ) with
      | some missing => have hPred := List.find?_some hMiss; rw [List.contains_iff_mem.mpr (hm.achievesFloors missing (List.mem_of_find?_eq_some hMiss))] at hPred; cases hPred
      | none => rw [hMiss] at h; dsimp only at h; split at h <;> (cases h; try simp [sheRefusalRefutes] at hr)
  Fragment o := SheStateWellFormed o.initState
  complete {o} hFrag hEx := by
    obtain ⟨endSt, hm⟩ := hEx; refine ⟨endSt, o.turns.length, ?_⟩; unfold checkSheCeremony
    have hMiss : o.targetFloors.find? (fun φ => !endSt.activeSafetyAndPrivacyFloors.contains φ) = none := List.find?_eq_none.mpr fun φ hφ => by rw [List.contains_iff_mem.mpr (hm.achievesFloors φ hφ)]; decide
    simp only [Nat.lt_irrefl, ↓reduceIte, (checkSheStateWellFormed_iff _).mpr hFrag, Bool.not_true]; rw [(runSheTurns_ok_iff _ _ _).mpr (inductiveSheTrace_iff_validSheTrace.mp hm.validTrace)]; dsimp only; rw [hMiss]; simp
  mono {r r' o c} hle hdec := by
    unfold checkSheCeremony at hdec ⊢; cases Nat.decLt r o.turns.length with
    | isTrue hlt => simp [hlt] at hdec
    | isFalse hlt =>
      have hlt' : ¬ r' < o.turns.length := by omega
      simp only [hlt, hlt', ↓reduceIte]
theorem checkSheCeremony_refutes_sound (grade : Nat) (o : SheCeremonyObj) (certEnd c' : SheState) (k : SheRefusal) (p : List Nat) (h : checkSheCeremony grade o certEnd = .refused k p) (hr : sheRefusalRefutes k = true) : ¬ CeremonyMeaning o c' := sheCeremonyJudge.refuted h hr c'
theorem sheRefusalRefutes_inhabited (φ : SheFloor) : sheRefusalRefutes (.coerciveFloorDowngrade φ) = true := rfl
private def padBytes32 (b : UInt8) : ByteArray := ⟨(List.replicate 32 b).toArray⟩
private theorem padBytes32_size (b : UInt8) : (padBytes32 b).size = 32 := by simp [padBytes32, ByteArray.size]
private def mkGenesisPk (s r : UInt8) : PqPublicKey := ⟨List.replicate 32 s, List.replicate 32 r⟩
def canonicalGenesisFloors : List SheFloor := [.sensorRoiRedaction 2, .consentBandNonOcclusion 32, .zkmlProvenSoundnessMilliBits 100000, .physicalProximityMaxTicks 50, .e2eeTeeChannelBound 1, .operatorLocalRevert 8]
def canonicalGenesisCustodianPks : List PqPublicKey := [mkGenesisPk 0xA0 0xB0, mkGenesisPk 0xA1 0xB1, mkGenesisPk 0xA2 0xB2, mkGenesisPk 0xA3 0xB3, mkGenesisPk 0xA4 0xB4]
def canonicalGenesisSimplexPks : List PqPublicKey := [mkGenesisPk 0xC0 0xD0, mkGenesisPk 0xC1 0xD1, mkGenesisPk 0xC2 0xD2, mkGenesisPk 0xC3 0xD3]
def canonicalGenesisSheState (extraBudget : Nat) : SheState :=
  { habitatJudgeDigest := padBytes32 0x10, pinnedModelWeightsRoot := padBytes32 0x22, pinnedZkmlSuiteDigest := suiteArtifactDigest canonicalUd100SmallSuite, monoSensorSeq := 0, consumedNullifiers := [], remainingMandateBudget := 100 + extraBudget, activeSafetyAndPrivacyFloors := canonicalGenesisFloors, settledOutboxActions := [], pqParams := sheStatefulPqParams, custodianPks := canonicalGenesisCustodianPks, simplexValidatorPks := canonicalGenesisSimplexPks, consumedCustodianLeaves := [], consumedSimplexLeaves := [], custodianThresholdT := 3, custodianTotalN := 5, custodianQuorumEpoch := 1, revokedCustodians := [], maxProximityTicks := 50, revertWindowSteps := 4 }
theorem sheCeremonyJudge_fragment_inhabited (extraBudget : Nat) : SheStateWellFormed (canonicalGenesisSheState extraBudget) := by
  refine ⟨padBytes32_size _, padBytes32_size _, suiteArtifactDigest_size _, ⟨rfl, rfl, rfl, rfl⟩,
    (checkListNodup_iff _).mp (by dsimp [canonicalGenesisSheState]; decide),
    ⟨.operatorLocalRevert 8, by dsimp [canonicalGenesisSheState]; decide, rfl⟩,
    fun φ hφ => by dsimp [canonicalGenesisSheState] at hφ; revert φ; decide,
    by dsimp [canonicalGenesisSheState]; decide,
    ⟨rfl, (checkListNodup_iff _).mp (by dsimp [canonicalGenesisSheState]; decide),
      fun pk hpk => by dsimp [canonicalGenesisSheState] at hpk; revert pk; decide⟩,
    ⟨by dsimp [canonicalGenesisSheState]; decide,
      (checkListNodup_iff _).mp (by dsimp [canonicalGenesisSheState]; decide),
      fun pk hpk => by dsimp [canonicalGenesisSheState] at hpk; revert pk; decide,
      fun pk hpk => by dsimp [canonicalGenesisSheState] at hpk ⊢; revert pk; decide⟩,
    ⟨by dsimp [canonicalGenesisSheState]; decide, by dsimp [canonicalGenesisSheState]; decide⟩,
    by dsimp [canonicalGenesisSheState]; decide⟩
private theorem fpauditOpenedRoundIdx_single (s c o t : ByteArray) (p : UInt64) : fpauditOpenedRoundIdx s c o t p 1 = 0 := by
  unfold fpauditOpenedRoundIdx; simp [Nat.mod_one]
/-- **Constructive Completeness for an Honest Single-Round `UD-100` + `s8 × E2M1` Candidate (`buildHonestCandidate_1round_complete`)**. -/
theorem buildHonestCandidate_1round_complete (suite : ZkmlSuiteArtifact) (sensorSealDigest boundFloorsDigest actionPayloadDigest proofTranscriptDigest : ByteArray)
    (xs : List Int) (weightRows : List (List Int)) (blockShifts : List Nat)
    (hSuite : checkSuiteArtifact suite = true) (hPow0 : suite.powBits = 0)
    (hSizes : sensorSealDigest.size = 32 ∧ boundFloorsDigest.size = 32 ∧ actionPayloadDigest.size = 32 ∧ proofTranscriptDigest.size = 32)
    (hXs : !xs.isEmpty = true ∧ xs.all isS8 = true)
    (hW : !weightRows.isEmpty = true ∧ weightRows.length = blockShifts.length ∧
      weightRows.all (fun row => row.length == xs.length && row.all isE2m1Mantissa) = true ∧ blockShifts.all (fun sh => decide (sh ≤ 8)) = true) :
    verifyCandidateComputation (buildHonestCandidate suite sensorSealDigest boundFloorsDigest actionPayloadDigest proofTranscriptDigest 0 [xs] weightRows blockShifts) = true ∧
    100000 ≤ provenZkmlMilliBits (buildHonestCandidate suite sensorSealDigest boundFloorsDigest actionPayloadDigest proofTranscriptDigest 0 [xs] weightRows blockShifts) := by
  have hLogEmpty : (exactMxfp4Logits xs weightRows blockShifts).isEmpty = false := by
    cases weightRows with
    | nil => cases hW.1
    | cons wr wrs => cases blockShifts with
      | nil => simp at hW
      | cons sh shs => rfl
  have hVer : verifyCandidateComputation (buildHonestCandidate suite sensorSealDigest boundFloorsDigest actionPayloadDigest proofTranscriptDigest 0 [xs] weightRows blockShifts) = true := by
    have hXsNotEmp : xs.isEmpty = false := by cases hc : xs.isEmpty with | false => rfl | true => rw [hc] at hXs; cases hXs.1
    have hWNotEmp : weightRows.isEmpty = false := by cases hc : weightRows.isEmpty with | false => rfl | true => rw [hc] at hW; cases hW.1
    have hWLen : (weightRows.length != blockShifts.length) = false := by rw [hW.2.1]; exact bne_self_eq_false _
    have hRange1 : List.range (0 + 1) = [0] := rfl
    unfold verifyCandidateComputation verifyExactRecomputeAudit buildHonestCandidate
    dsimp only; rw [show ([xs] : List (List Int)).length = 1 from rfl, show List.range 1 = [0] from rfl]
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.length_cons, List.length_nil]
    rw [fpauditOpenedRoundIdx_single, hRange1]
    simp only [List.getD_cons_zero, List.getElem?_cons_zero, hSuite, hPow0, Nat.min_eq_left (Nat.zero_le _),
      hasLowZeroBits_zero, candidateStatementDigest_size, fpauditWeightsRoot_size, fpauditOutputRoot_size,
      fpauditCommitRoot_size, fpauditInputRoot_size, hSizes.1, hSizes.2.1, hSizes.2.2.1, hSizes.2.2.2,
      and_self, decide_true, BEq.rfl, Bool.and_true, List.isEmpty_cons,
      Bool.false_or, bne_self_eq_false, List.all_cons, List.all_nil, hLogEmpty,
      hXsNotEmp, hXs.2, hWNotEmp, hWLen, hW.2.2.1, hW.2.2.2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  refine ⟨hVer, ?_⟩
  unfold provenZkmlMilliBits; rw [hVer]; dsimp only [buildHonestCandidate]
  unfold checkSuiteArtifact at hSuite; simp only [Bool.and_eq_true, decide_eq_true_eq] at hSuite; exact hSuite.2.2.2.2.2.2
/-- **Unconditional Constructive Inhabitedness Witness (`verifyCandidateComputation_inhabited`)**:
    Wide-leaf `UD-100` (`lb=2, q=148, pow=0`, `100.344` bits) + exact `s8 × E2M1` integer recompute! -/
theorem verifyCandidateComputation_inhabited : ∃ c : CandidateComputation, verifyCandidateComputation c = true ∧ 100000 ≤ provenZkmlMilliBits c :=
  ⟨_, buildHonestCandidate_1round_complete canonicalUd100WideLeafSuite (padBytes32 0x33) (padBytes32 0x44) (padBytes32 0x55) (padBytes32 0x66)
    [3, -2, 5, -1] [[2, -1, 4, 3], [-2, 1, 2, -4]] [0, 1]
    (by decide) rfl ⟨padBytes32_size _, padBytes32_size _, padBytes32_size _, padBytes32_size _⟩ (by decide) (by decide)⟩
theorem validSheTrace_multiTurn_inhabited (extraBudget : Nat) :
    ∃ (turns : List SheTurn) (endState : SheState), turns.length = 2 ∧ ValidSheTrace (canonicalGenesisSheState extraBudget) turns endState ∧ endState.remainingMandateBudget = 50 ∧ endState.maxProximityTicks = 30 := by
  let st₀ := canonicalGenesisSheState extraBudget
  let rev₁ : MandateAttenuation := { newBudgetCap := 75, newMaxProximityTicks := 40, newlyRevokedCustodians := [4], reasonDigest := padBytes32 0x61 }
  let rev₂ : MandateAttenuation := { newBudgetCap := 50, newMaxProximityTicks := 30, newlyRevokedCustodians := [3], reasonDigest := padBytes32 0x62 }
  let st₁ : SheState := { st₀ with remainingMandateBudget := 75, maxProximityTicks := 40, revokedCustodians := mergeRevokedCustodians st₀.revokedCustodians [4] }
  let st₂ : SheState := { st₁ with remainingMandateBudget := 50, maxProximityTicks := 30, revokedCustodians := mergeRevokedCustodians st₁.revokedCustodians [3] }
  have hs₁ : applySheTurn st₀ (.revokeOrAttenuateMandate rev₁) = .ok st₁ := (applySheTurn_ok_iff_inductiveStep _ _ _).mpr (.attenuateMandate st₀ rev₁ (padBytes32_size _) (by dsimp [st₀, rev₁, canonicalGenesisSheState]; omega) (by dsimp [st₀, rev₁, canonicalGenesisSheState]; omega) (by simp [st₀, rev₁, canonicalGenesisSheState]))
  have hs₂ : applySheTurn st₁ (.revokeOrAttenuateMandate rev₂) = .ok st₂ := (applySheTurn_ok_iff_inductiveStep _ _ _).mpr (.attenuateMandate st₁ rev₂ (padBytes32_size _) (by dsimp [st₁, rev₂]; omega) (by dsimp [st₁, rev₂]; omega) (by simp [st₁, st₀, rev₂, canonicalGenesisSheState]))
  exact ⟨[.revokeOrAttenuateMandate rev₁, .revokeOrAttenuateMandate rev₂], st₂, rfl, ⟨st₁, hs₁, ⟨st₂, hs₂, rfl⟩⟩, rfl, rfl⟩
end Obend.Polis.SecureHardwareEnv
end
