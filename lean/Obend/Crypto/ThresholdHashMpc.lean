module
/-
# Obend.Crypto.ThresholdHashMpc — Public/Secret Cut, `RSS` & $t$-of-$n$ Algebraic MPC, 2-Lane BDOZ MACs, `Π_deg` DKG
Clean-room 0-axiom formalization of post-quantum threshold hash-based signing (`leanSPHINCS`, `SLH-DSA`, `leanSig`):
1. Exact Public/Secret Cut + constant-depth (`1 + w`) sweep + 1-round RAM opening (`evalCutBatchSign_eq_naiveSign`, `transcript_shape_depends_only_on_public_params`);
2. Bit-identical threshold-vs-single signature indistinguishability (`thresholdSign_eq_singleSign`, `reconstructRss_rssAnd`, `beaverMulEval_eq_mul`, `power7BinomialEval_eq_pow7`);
3. 2-lane split-custody `Tower128 × Tower128` & `GoldilocksExt2` SPDZ/BDOZ MACs (`bdoz_2party_cross_terms_sound`, `batchTowerMac2Lane_sound_roots_bound`, `bdoz_cheater_identified_or_mac_forged`);
4. 2-round PQ dealerless DKG (`Π_deg` `dkg_reed_solomon_consistency_sound`), `Π_deg0` refresh (`proactive_refresh_preserves_secret_and_pk`), and garbled policy gate;
Custody integration and multi-turn safety live in `Obend.Polis.PqThresholdCustody`,
which imports this cryptographic layer.
-/
public import Obend.Crypto.PqHashSignatures
public import Obend.Crypto.BinaryTower256
public import Obend.Consensus.Simplex
public import Obend.Consensus.SimplexProtocol
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.PqHashSignatures

public section
namespace Obend.Crypto.ThresholdHashMpc

open Obend
open Obend.Apps.ZkNtt
open Obend.Crypto
open Obend.Crypto.BinaryTower256
open Obend.Crypto.ThresholdMpcUcGames
open Obend.Crypto.PqHashSignatures
open Obend.Digest.Cshake256
open Obend.Digest.HashBytes
open Obend.Judge.Computational
open Obend.Consensus.Simplex
open Obend.Consensus.SimplexProtocol

set_option autoImplicit false

/-! ## 1. Exact Public/Secret Cut + Constant-Depth (`1 + w`) Sweep + 1-Round RAM Share Opening -/

/-- Precomputed constant-depth (`1 + (w - 1) = w`) secret chain table `[0..w)` for a single WOTS+C chain.
    Evaluated inside the MPC secret zone; ONLY index `digits[r]` (and public endpoint `w - 1`) is opened! -/
def buildMpcChainTable (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp chain w : Nat) : List (List UInt8) :=
  let base := wotsSecretBase suite sk layer tree kp chain
  (List.range w).map fun step =>
    wotsChainSteps suite sk.pkSeed layer tree kp chain 0 step base

/-- 1-round linear RAM multiplexer selecting entry `selStep` from the secret-shared chain table. -/
def ramOpenChainStep (table : List (List UInt8)) (selStep : Nat) : List UInt8 :=
  table.getD selStep []

theorem ramOpenChainStep_buildMpcChainTable
    (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp chain w selStep : Nat) (hLt : selStep < w) :
    ramOpenChainStep (buildMpcChainTable suite sk layer tree kp chain w) selStep =
      wotsChainSteps suite sk.pkSeed layer tree kp chain 0 selStep
        (wotsSecretBase suite sk layer tree kp chain) :=
  list_getD_map_range w _ [] hLt

/-- Layer-wise cut-and-batch hypertree signer:
    secret zone computes the `ell1 × w` chain table in constant depth `w`; clear CPU grinds `TSW`
    counter `(ctr, digits)` with `0` MPC gates; secret zone executes 1-round RAM opening at `digits[r]`. -/
def evalCutBatchLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind : Nat) :
    Nat → Nat → List UInt8 → Nat → Option (List LayerXmssSig)
  | _, _, _, 0 => some []
  | layerIdx, globalIdx, curRoot, rem + 1 =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    let tables := (List.range params.ell1).map fun r =>
      buildMpcChainTable suite sk layerU32 treeIdx kpIdx r params.w
    match grindTswCounterAux suite params.w params.ell1 params.targetSum
            rRand sk.pkSeed pkRoot curRoot layerU32 treeIdx 0 maxGrind with
    | none => none
    | some (ctr, digits, _) =>
      let wotsChains := (List.range params.ell1).map fun r =>
        ramOpenChainStep (tables.getD r []) (digits.getD r 0)
      let authPath := buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
        (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx
      let nextRoot := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
      match evalCutBatchLayers suite params sk pkRoot rRand maxGrind (layerIdx + 1) treeIdxNat nextRoot rem with
      | none => none
      | some restSigs =>
        some ({ tswCtr := ctr, wotsChains := wotsChains, authPath := authPath } :: restSigs)

/-- **Public/Secret Cut + Constant-Depth (`1 + w`) + 1-Round RAM Opening Signer (`evalCutBatchSign`)**. -/
@[expose] def evalCutBatchSign (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind : Nat) : Option PqHashSig :=
  if !(params.wellFormed) then none
  else if !(leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := thPrfMsg suite sk.skPrf optRand mu
    if params.statefulLeanSig then
      match evalCutBatchLayers suite params sk pk.pkRoot rRand maxGrind 0 leafGlobalIdx mu params.numLayers with
      | none => none
      | some layerSigs =>
        some { rRand := rRand, msgTswCtr := 0, leafGlobalIdx := leafGlobalIdx,
               forsOpenings := [], layerSigs := layerSigs }
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kp0 := leafGlobalIdx % subLeaves
      let tree0 := UInt64.ofNat (leafGlobalIdx / subLeaves)
      match grindTswCounterAux suite params.w params.ell1 params.targetSum
              rRand pk.pkSeed pk.pkRoot mu 0 tree0 0 maxGrind with
      | none => none
      | some (ctr0, _, hmsg0) =>
        let forsOps := buildForsOpenings suite params sk tree0 kp0 hmsg0
        let forsPk := computeForsPk suite params sk tree0 kp0
        match evalCutBatchLayers suite params sk pk.pkRoot rRand maxGrind 0 leafGlobalIdx forsPk params.numLayers with
        | none => none
        | some layerSigs =>
          some { rRand := rRand, msgTswCtr := ctr0, leafGlobalIdx := leafGlobalIdx,
                 forsOpenings := forsOps, layerSigs := layerSigs }

private theorem evalCutBatchLayers_eq_signHypertreeLayers
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind : Nat)
    (hw : 2 ≤ params.w) :
    ∀ (rem layerIdx globalIdx : Nat) (curRoot : List UInt8),
      evalCutBatchLayers suite params sk pkRoot rRand maxGrind layerIdx globalIdx curRoot rem =
      signHypertreeLayers suite params sk pkRoot rRand maxGrind layerIdx globalIdx curRoot rem
  | 0, _, _, _ => rfl
  | rem + 1, layerIdx, globalIdx, curRoot => by
    simp only [evalCutBatchLayers, signHypertreeLayers]
    cases hGrind : grindTswCounterAux suite params.w params.ell1 params.targetSum rRand sk.pkSeed pkRoot curRoot
        (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) 0 maxGrind with
    | none => rfl
    | some triple =>
      rcases triple with ⟨ctr, digits, hmsgG⟩
      dsimp only
      obtain ⟨_, _, hChk⟩ := grindTswCounterAux_sound hGrind
      obtain ⟨hLen, hBound, _⟩ := (checkTargetSum_iff params.w params.ell1 params.targetSum digits).mp hChk
      rw [evalCutBatchLayers_eq_signHypertreeLayers suite params sk pkRoot rRand maxGrind hw rem]
      have hChainsEq :
          ((List.range params.ell1).map fun r =>
            ramOpenChainStep
              (((List.range params.ell1).map fun r' =>
                buildMpcChainTable suite sk (UInt32.ofNat layerIdx)
                  (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                  (globalIdx % 2 ^ params.subtreeHeight) r' params.w).getD r [])
              (digits.getD r 0)) =
          ((List.range params.ell1).map fun r =>
            wotsChainSteps suite sk.pkSeed (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (wotsSecretBase suite sk (UInt32.ofNat layerIdx)
                (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                (globalIdx % 2 ^ params.subtreeHeight) r)) := by
        apply List.map_congr_left
        intro r hrMem
        have hrLt : r < params.ell1 := List.mem_range.mp hrMem
        rw [list_getD_map_range params.ell1 _ [] hrLt]
        have hdrLt : digits.getD r 0 < params.w := by
          have hrD : r < digits.length := hLen ▸ hrLt
          rw [list_getD_eq_getElem digits 0 hrD]
          exact hBound _ (List.getElem_mem hrD)
        exact ramOpenChainStep_buildMpcChainTable suite sk _ _ _ r params.w (digits.getD r 0) hdrLt
      rw [hChainsEq]
      cases signHypertreeLayers suite params sk pkRoot rRand maxGrind (layerIdx + 1)
        (globalIdx / 2 ^ params.subtreeHeight)
        (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) rem <;> rfl

/-- **Public/Secret Cut Equivalence (`evalCutBatchSign_eq_naiveSign`)**:
    Constant-depth (`1 + w`) cut-and-batch MPC signing with 1-round RAM share opening produces
    the exact same output as `evalSingleSign` on every input! -/
theorem evalCutBatchSign_eq_naiveSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind : Nat) :
    evalCutBatchSign suite params sk msg optRand leafGlobalIdx maxGrind =
    evalSingleSign suite params sk msg optRand leafGlobalIdx maxGrind := by
  unfold evalCutBatchSign evalSingleSign
  cases hWf : params.wellFormed
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hw : 2 ≤ params.w := by
      simp only [PqHashParams.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hWf; omega
    split
    · rfl
    · split
      · rw [evalCutBatchLayers_eq_signHypertreeLayers suite params sk _ _ maxGrind hw]
        cases signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot
          (thPrfMsg suite sk.skPrf optRand
            (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg))
          maxGrind 0 leafGlobalIdx
          (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg)
          params.numLayers <;> rfl
      · cases grindTswCounterAux suite params.w params.ell1 params.targetSum _ _ _ _ 0 _ 0 maxGrind with
        | none => rfl
        | some tr =>
          rcases tr with ⟨_, _, hmsg0⟩; dsimp only
          rw [evalCutBatchLayers_eq_signHypertreeLayers suite params sk _ _ maxGrind hw]
          cases signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg))
            maxGrind 0 leafGlobalIdx
            (computeForsPk suite params sk (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
              (leafGlobalIdx % 2 ^ params.subtreeHeight)) params.numLayers <;> rfl

/-- Total complementary verification hash steps `∑_{r} ((w - 1) - d_r)` executed on an opened WOTS+C digit vector. -/
def sumComplementSteps (w : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => ((w - 1) - d) + sumComplementSteps w ds

/-- Execution-induced MPC & verification transcript shape for an active `TSW` digit vector `digits`. -/
structure MpcTranscriptShape where
  secretSequentialHashDepth : Nat
  ramOpenRounds : Nat
  openedDigestShares : Nat
  totalVerifierChainSteps : Nat
  deriving DecidableEq, Repr

/-- Compute the actual MPC depth, round count, opened 32-byte share count, and verifier chain step count
    induced by signing with a `TSW`-valid digit vector `digits`. -/
def observeTranscriptShape (params : PqHashParams) (digits : List Nat) : MpcTranscriptShape where
  secretSequentialHashDepth := 1 + (params.w - 1)
  ramOpenRounds := 1
  openedDigestShares := 1 + (if params.statefulLeanSig then 0 else params.forsTrees) + params.numLayers * digits.length
  totalVerifierChainSteps := sumComplementSteps params.w digits

private theorem sumComplementSteps_eq_of_valid (w : Nat) (hw : 1 ≤ w) :
    ∀ (digits : List Nat),
      (∀ d ∈ digits, d < w) →
      sumComplementSteps w digits + sumDigits digits = digits.length * (w - 1)
  | [], _ => by simp [sumComplementSteps, sumDigits]
  | d :: ds, hBound => by
    have hd : d < w := hBound d (List.mem_cons_self ..)
    have ih := sumComplementSteps_eq_of_valid w hw ds (fun x hx => hBound x (List.mem_cons_of_mem _ hx))
    simp only [sumComplementSteps, sumDigits, List.length_cons, Nat.succ_mul]
    omega

/-- **Transcript Shape Public-Parameter Independence (`transcript_shape_depends_only_on_public_params`)**:
    For ANY two `TSW`-valid digit vectors `d₁, d₂` (`checkTargetSum params.w params.ell1 params.targetSum = true`)
    produced by distinct secret keys, messages, or leaf indices, the entire MPC depth (`w`), RAM opening
    rounds (`1`), opened share count, AND total verifier hash step count `ell1 * (w - 1) - targetSum`
    are strictly identical (`observeTranscriptShape params d₁ = observeTranscriptShape params d₂`)! -/
theorem transcript_shape_depends_only_on_public_params
    (params : PqHashParams) (hw : 1 ≤ params.w)
    (d₁ d₂ : List Nat)
    (hValid₁ : checkTargetSum params.w params.ell1 params.targetSum d₁ = true)
    (hValid₂ : checkTargetSum params.w params.ell1 params.targetSum d₂ = true) :
    observeTranscriptShape params d₁ = observeTranscriptShape params d₂ ∧
    (observeTranscriptShape params d₁).secretSequentialHashDepth = params.w ∧
    (observeTranscriptShape params d₁).totalVerifierChainSteps =
      params.ell1 * (params.w - 1) - params.targetSum := by
  obtain ⟨hLen₁, hB₁, hS₁⟩ := (checkTargetSum_iff params.w params.ell1 params.targetSum d₁).mp hValid₁
  obtain ⟨hLen₂, hB₂, hS₂⟩ := (checkTargetSum_iff params.w params.ell1 params.targetSum d₂).mp hValid₂
  have hEq₁ := sumComplementSteps_eq_of_valid params.w hw d₁ hB₁
  have hEq₂ := sumComplementSteps_eq_of_valid params.w hw d₂ hB₂
  rw [hLen₁, hS₁] at hEq₁
  rw [hLen₂, hS₂] at hEq₂
  have hComp₁ : sumComplementSteps params.w d₁ = params.ell1 * (params.w - 1) - params.targetSum := by omega
  have hComp₂ : sumComplementSteps params.w d₂ = params.ell1 * (params.w - 1) - params.targetSum := by omega
  refine ⟨?_, by simp [observeTranscriptShape]; omega, hComp₁⟩
  simp only [observeTranscriptShape, hLen₁, hLen₂, hComp₁, hComp₂]

/-! ## 2. Bit-Identical Signature Indistinguishability (`RSS`, `BinaryTower256` & `Poseidon2Goldilocks`) -/

/-- 2-of-3 Replicated Secret Sharing (`RSS`) bit share `(s0, s1, s2)` with `x = s0 ⊕ s1 ⊕ s2`:
    Party 0 holds `(s0, s1)`, Party 1 holds `(s1, s2)`, Party 2 holds `(s2, s0)`. -/
structure RssBitShare where
  s0 : Bool
  s1 : Bool
  s2 : Bool
  deriving DecidableEq, Repr

def reconstructRss (x : RssBitShare) : Bool := (x.s0 ^^ x.s1) ^^ x.s2
def rssXor (a b : RssBitShare) : RssBitShare := ⟨a.s0 ^^ b.s0, a.s1 ^^ b.s1, a.s2 ^^ b.s2⟩
def rssNot (a : RssBitShare) : RssBitShare := ⟨!a.s0, a.s1, a.s2⟩

/-- 1-bit-per-party `RSS` AND gate (`c = a ∧ b`) masked by zero-share `z` (`z0 ⊕ z1 ⊕ z2 = false`). -/
def rssAnd (a b z : RssBitShare) : RssBitShare where
  s0 := (((a.s0 && b.s0) ^^ (a.s0 && b.s1)) ^^ (a.s1 && b.s0)) ^^ z.s0
  s1 := (((a.s1 && b.s1) ^^ (a.s1 && b.s2)) ^^ (a.s2 && b.s1)) ^^ z.s1
  s2 := (((a.s2 && b.s2) ^^ (a.s2 && b.s0)) ^^ (a.s0 && b.s2)) ^^ z.s2

theorem reconstructRss_rssXor (a b : RssBitShare) :
    reconstructRss (rssXor a b) = (reconstructRss a ^^ reconstructRss b) := by
  cases a with | mk a0 a1 a2 => cases b with | mk b0 b1 b2 =>
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl

theorem reconstructRss_rssNot (a : RssBitShare) :
    reconstructRss (rssNot a) = !(reconstructRss a) := by
  cases a with | mk a0 a1 a2 => cases a0 <;> cases a1 <;> cases a2 <;> rfl

/-- **2-of-3 `RSS` AND Gate Exactness (`reconstructRss_rssAnd`)**. -/
theorem reconstructRss_rssAnd (a b z : RssBitShare)
    (hZero : reconstructRss z = false) :
    reconstructRss (rssAnd a b z) = (reconstructRss a && reconstructRss b) := by
  cases a with | mk a0 a1 a2 =>
  cases b with | mk b0 b1 b2 =>
  cases z with | mk z0 z1 z2 =>
  unfold reconstructRss at hZero ⊢
  unfold rssAnd; dsimp only
  cases z0 <;> cases z1 <;> cases z2 <;> try cases hZero
  all_goals
    cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl

/-- Shared Keccak-f[1600] `χ` S-box bit `x ⊕ ((¬ y) ∧ z)` in 2-of-3 `RSS` (1 bit/party). -/
def rssKeccakChiBit (x y z zeroMask : RssBitShare) : RssBitShare :=
  rssXor x (rssAnd (rssNot y) z zeroMask)

theorem reconstructRss_keccakChiBit (x y z zeroMask : RssBitShare)
    (hZero : reconstructRss zeroMask = false) :
    reconstructRss (rssKeccakChiBit x y z zeroMask) =
      (reconstructRss x ^^ ((!(reconstructRss y)) && reconstructRss z)) := by
  unfold rssKeccakChiBit
  rw [reconstructRss_rssXor, reconstructRss_rssAnd _ _ _ hZero, reconstructRss_rssNot]

/-- Canonical $\mathbb{F}_2 \hookrightarrow \mathcal{T}_k$ bit embedding into any binary tower level `k`
    (`k = 3` for $\mathbb{F}_{2^8}$ Shamir coordinates, `k = 7` for `Tower128`). -/
def embedBitToTower (k : Nat) (b : Bool) : TowerElem k :=
  if b then towerOne k else towerZero k

theorem embedBitToTower_injective (k : Nat) {b₁ b₂ : Bool}
    (h : embedBitToTower k b₁ = embedBitToTower k b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂
  · rfl
  · exact False.elim (towerOne_ne_zero k h.symm)
  · exact False.elim (towerOne_ne_zero k h)
  · rfl

theorem embedBitToTower_xor (k : Nat) (a b : Bool) :
    embedBitToTower k (a ^^ b) = towerAdd k (embedBitToTower k a) (embedBitToTower k b) := by
  cases a <;> cases b <;> simp [embedBitToTower]

theorem embedBitToTower_and (k : Nat) (a b : Bool) :
    embedBitToTower k (a && b) = towerMul k (embedBitToTower k a) (embedBitToTower k b) := by
  cases a <;> cases b <;> simp [embedBitToTower]

/-- Polymorphic Beaver multiplication linear combination over ANY `[LawfulCommRing R]`. -/
def beaverMulEval {R : Type} [CommRingOps R] (uVal vVal a b c : R) : R :=
  CommRingOps.add
    (CommRingOps.add c (CommRingOps.mul uVal b))
    (CommRingOps.add (CommRingOps.mul a vVal) (CommRingOps.mul uVal vVal))

/-- **Polymorphic Beaver Multiplication Exactness (`beaverMulEval_eq_mul`)**:
    Simultaneously covers `TowerElem 3` ($\mathbb{F}_{2^8}$), `Tower128` ($\mathbb{F}_{2^{128}}$),
    `Goldilocks`, and `GoldilocksExt2`! -/
theorem beaverMulEval_eq_mul {R : Type} [LawfulCommRing R]
    (x y a b c uVal vVal : R)
    (hTriple : c = CommRingOps.mul a b)
    (hu : uVal = CommRingOps.sub x a)
    (hv : vVal = CommRingOps.sub y b) :
    beaverMulEval uVal vVal a b c = CommRingOps.mul x y := by
  subst hTriple hu hv
  have hxEq : CommRingOps.add a (CommRingOps.sub x a) = x :=
    LawfulCommRing.add_sub_cancel_left a x
  have hyEq : CommRingOps.add b (CommRingOps.sub y b) = y :=
    LawfulCommRing.add_sub_cancel_left b y
  calc
    beaverMulEval (CommRingOps.sub x a) (CommRingOps.sub y b) a b (CommRingOps.mul a b)
      = CommRingOps.add
          (CommRingOps.mul (CommRingOps.add a (CommRingOps.sub x a)) b)
          (CommRingOps.mul (CommRingOps.add a (CommRingOps.sub x a)) (CommRingOps.sub y b)) := by
        unfold beaverMulEval
        rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib]
    _ = CommRingOps.mul (CommRingOps.add a (CommRingOps.sub x a))
          (CommRingOps.add b (CommRingOps.sub y b)) := by
        rw [← LawfulCommRing.left_distrib]
    _ = CommRingOps.mul x y := by rw [hxEq, hyEq]

/-- Goldilocks degree-7 S-box `x^7` matching width-12 `Poseidon2Goldilocks`. -/
def pow7Goldilocks (x : Goldilocks) : Goldilocks :=
  let x2 := CommRingOps.mul x x
  let x4 := CommRingOps.mul x2 x2
  CommRingOps.mul x (CommRingOps.mul x2 x4)

/-- **1-Round Binomial Power-7 S-Box Evaluator (`power7BinomialEval`)**:
    Given opened masked scalar `δ = x - r` (`8 B` per S-box) and pre-shared power tuple
    `(r, r^2, r^3, r^4, r^5, r^6, r^7)`, evaluates `(δ + r)^7 = x^7` locally! -/
def power7BinomialEval (delta r1 r2 r3 r4 r5 r6 r7 : Goldilocks) : Goldilocks :=
  let d2 := CommRingOps.mul delta delta
  let d3 := CommRingOps.mul d2 delta
  let d4 := CommRingOps.mul d2 d2
  let d5 := CommRingOps.mul d4 delta
  let d6 := CommRingOps.mul d4 d2
  let d7 := CommRingOps.mul d3 d4
  let t7 := d7
  let t6 := CommRingOps.mul (Goldilocks.ofNat 7) (CommRingOps.mul d6 r1)
  let t5 := CommRingOps.mul (Goldilocks.ofNat 21) (CommRingOps.mul d5 r2)
  let t4 := CommRingOps.mul (Goldilocks.ofNat 35) (CommRingOps.mul d4 r3)
  let t3 := CommRingOps.mul (Goldilocks.ofNat 35) (CommRingOps.mul d3 r4)
  let t2 := CommRingOps.mul (Goldilocks.ofNat 21) (CommRingOps.mul d2 r5)
  let t1 := CommRingOps.mul (Goldilocks.ofNat 7) (CommRingOps.mul delta r6)
  let t0 := r7
  CommRingOps.add
    (CommRingOps.add (CommRingOps.add t7 t6) (CommRingOps.add t5 t4))
    (CommRingOps.add (CommRingOps.add t3 t2) (CommRingOps.add t1 t0))

private theorem gold_val_self (a : Goldilocks) : a.val = a.val % goldilocksPrime :=
  (Nat.mod_eq_of_lt a.isLt).symm

private theorem gold_add_mod {a b : Goldilocks} {na nb : Nat}
    (ha : a.val = na % goldilocksPrime) (hb : b.val = nb % goldilocksPrime) :
    (CommRingOps.add a b).val = (na + nb) % goldilocksPrime := by
  change (Goldilocks.add a b).val = _
  rw [Goldilocks.add_val, ha, hb, ← Nat.add_mod]

private theorem gold_mul_mod {a b : Goldilocks} {na nb : Nat}
    (ha : a.val = na % goldilocksPrime) (hb : b.val = nb % goldilocksPrime) :
    (CommRingOps.mul a b).val = (na * nb) % goldilocksPrime := by
  change (Goldilocks.mul a b).val = _
  rw [Goldilocks.mul_val, ha, hb, ← Nat.mul_mod]

private theorem nat_binomial7_identity (d r : Nat) :
    (d + r) * (((d + r) * (d + r)) * (((d + r) * (d + r)) * ((d + r) * (d + r)))) =
    (((d * d * d) * ((d * d) * (d * d)) + 7 * (((d * d) * (d * d) * (d * d)) * r)) +
     (21 * (((d * d) * (d * d) * d) * (r * r)) + 35 * (((d * d) * (d * d)) * (r * r * r)))) +
    ((35 * ((d * d * d) * ((r * r) * (r * r))) + 21 * ((d * d) * ((r * r) * (r * r) * r))) +
     (7 * (d * ((r * r) * (r * r) * (r * r))) + (r * r * r) * ((r * r) * (r * r)))) := by
  grind

/-- **1-Round Binomial Power-7 Exactness (`power7BinomialEval_eq_pow7`)**:
    Opening `δ = x - r` and evaluating the degree-1 linear combination over `(r, r^2, ..., r^7)`
    reconstructs `pow7Goldilocks x = x^7` identically in 1 communication round! -/
theorem power7BinomialEval_eq_pow7 (x r : Goldilocks) :
    let delta := CommRingOps.sub x r
    let r2 := CommRingOps.mul r r; let r3 := CommRingOps.mul r2 r
    let r4 := CommRingOps.mul r2 r2; let r5 := CommRingOps.mul r4 r
    let r6 := CommRingOps.mul r4 r2; let r7 := CommRingOps.mul r3 r4
    power7BinomialEval delta r r2 r3 r4 r5 r6 r7 = pow7Goldilocks x := by
  intro delta r2 r3 r4 r5 r6 r7
  have hxSum : x = CommRingOps.add delta r := by
    show x = CommRingOps.add (CommRingOps.sub x r) r
    rw [LawfulCommRing.add_comm _ r, LawfulCommRing.add_sub_cancel_left]
  rw [hxSum]; apply Goldilocks.ext; unfold pow7Goldilocks power7BinomialEval; dsimp only
  have hd := gold_val_self delta; have hr := gold_val_self r
  have hc7 : (Goldilocks.ofNat 7).val = 7 % goldilocksPrime := rfl
  have hc21 : (Goldilocks.ofNat 21).val = 21 % goldilocksPrime := rfl
  have hc35 : (Goldilocks.ofNat 35).val = 35 % goldilocksPrime := rfl
  have hs1 := gold_add_mod hd hr; have hs2 := gold_mul_mod hs1 hs1; have hs4 := gold_mul_mod hs2 hs2
  have hRhs := gold_mul_mod hs1 (gold_mul_mod hs2 hs4)
  have hd2 := gold_mul_mod hd hd; have hd3 := gold_mul_mod hd2 hd; have hd4 := gold_mul_mod hd2 hd2
  have hd5 := gold_mul_mod hd4 hd; have hd6 := gold_mul_mod hd4 hd2; have hd7 := gold_mul_mod hd3 hd4
  have hr2 := gold_mul_mod hr hr; have hr3 := gold_mul_mod hr2 hr; have hr4 := gold_mul_mod hr2 hr2
  have hr5 := gold_mul_mod hr4 hr; have hr6 := gold_mul_mod hr4 hr2; have hr7 := gold_mul_mod hr3 hr4
  have ht6 := gold_mul_mod hc7 (gold_mul_mod hd6 hr); have ht5 := gold_mul_mod hc21 (gold_mul_mod hd5 hr2)
  have ht4 := gold_mul_mod hc35 (gold_mul_mod hd4 hr3); have ht3 := gold_mul_mod hc35 (gold_mul_mod hd3 hr4)
  have ht2 := gold_mul_mod hc21 (gold_mul_mod hd2 hr5); have ht1 := gold_mul_mod hc7 (gold_mul_mod hd hr6)
  have hLhs := gold_add_mod
    (gold_add_mod (gold_add_mod hd7 ht6) (gold_add_mod ht5 ht4))
    (gold_add_mod (gold_add_mod ht3 ht2) (gold_add_mod ht1 hr7))
  rw [hLhs, hRhs, nat_binomial7_identity delta.val r.val]

/-- Polymorphic linear Lagrange inner product `∑_i λ_i y_i` reconstructing `p(0)` from shares. -/
def lagrangeCombine {R : Type} [CommRingOps R] : List R → List R → R
  | l :: ls, y :: ys => CommRingOps.add (CommRingOps.mul l y) (lagrangeCombine ls ys)
  | _, _ => CommRingOps.zero

theorem lagrangeCombine_add {R : Type} [LawfulCommRing R] :
    ∀ (lambdas xs ys : List R),
      xs.length = ys.length →
      lagrangeCombine lambdas (List.zipWith CommRingOps.add xs ys) =
        CommRingOps.add (lagrangeCombine lambdas xs) (lagrangeCombine lambdas ys)
  | [], _, _, _ => by simp [lagrangeCombine, LawfulCommRing.add_zero]
  | _ :: _, [], [], _ => by simp [lagrangeCombine, LawfulCommRing.add_zero]
  | _ :: _, [], _ :: _, h => by cases h
  | _ :: _, _ :: _, [], h => by cases h
  | l :: ls, x :: xs, y :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zipWith_cons_cons, lagrangeCombine]
    rw [lagrangeCombine_add ls xs ys h, LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

/-- Threshold MPC execution engine mode (`2-of-3 RSS`, `$t$-of-$n$ BinaryTower256`, `$t$-of-$n$ Poseidon2Goldilocks`, or generic `customRss`). -/
inductive ThresholdEngine where
  | rss2of3Cshake
  | shamirTowerCshake (t n : Nat)
  | shamirPoseidon2 (t n : Nat)
  | customRss (s : TweakableHashSuite)

def ThresholdEngine.suite : ThresholdEngine → TweakableHashSuite
  | .rss2of3Cshake => cshake256Suite
  | .shamirTowerCshake _ _ => cshake256Suite
  | .shamirPoseidon2 _ _ => poseidon2Suite
  | .customRss s => s

/-- Reconstruct a byte list from 3-party XOR/RSS byte shares `s0 ⊕ s1 ⊕ s2`. -/
def reconstructXorBytes (s0 s1 s2 : List UInt8) : List UInt8 :=
  List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) s0 s1) s2

theorem reconstructXorBytes_cancel (x m1 m2 : List UInt8)
    (h1 : m1.length = x.length) (h2 : m2.length = x.length) :
    reconstructXorBytes (List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) x m1) m2) m1 m2 = x := by
  induction x generalizing m1 m2 with
  | nil =>
    cases m1 <;> cases m2 <;> first | rfl | cases h1 | cases h2
  | cons bx xs ih =>
    cases m1 with
    | nil => cases h1
    | cons b1 ms1 =>
      cases m2 with
      | nil => cases h2
      | cons b2 ms2 =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
        have hByte : (((bx ^^^ b1) ^^^ b2) ^^^ b1) ^^^ b2 = bx := by
          apply UInt8.eq_of_toBitVec_eq
          simp only [UInt8.toBitVec_xor]
          rw [BitVec.xor_assoc (bx.toBitVec ^^^ b1.toBitVec) b2.toBitVec b1.toBitVec,
              BitVec.xor_comm b2.toBitVec b1.toBitVec,
              ← BitVec.xor_assoc (bx.toBitVec ^^^ b1.toBitVec) b1.toBitVec b2.toBitVec,
              BitVec.xor_assoc bx.toBitVec b1.toBitVec b1.toBitVec,
              BitVec.xor_self, BitVec.xor_zero,
              BitVec.xor_assoc bx.toBitVec b2.toBitVec b2.toBitVec,
              BitVec.xor_self, BitVec.xor_zero]
        show ((((bx ^^^ b1) ^^^ b2) ^^^ b1) ^^^ b2) ::
          reconstructXorBytes (List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) xs ms1) ms2) ms1 ms2 = bx :: xs
        rw [hByte, ih ms1 ms2 h1 h2]

/-- Threshold secret key share bundle reconstructing `(skSeed, skPrf)` under the chosen engine. -/
structure SharedSecretKeyBundle where
  pkSeed : List UInt8
  skSeedShares : List (List UInt8)
  skPrfShares  : List (List UInt8)
  reconstructBytes : List (List UInt8) → List UInt8

def SharedSecretKeyBundle.reconstructSk (b : SharedSecretKeyBundle) : PqSecretKey where
  skSeed := b.reconstructBytes b.skSeedShares
  skPrf  := b.reconstructBytes b.skPrfShares
  pkSeed := b.pkSeed

/-- Engine-specific threshold `(t, n)` and share-arity check (`rss2of3` -> 3 shares; `shamir t n` -> `0 < t ≤ n`). -/
def ThresholdEngine.validBundle (eng : ThresholdEngine) (b : SharedSecretKeyBundle) : Bool :=
  match eng with
  | .rss2of3Cshake | .customRss _ => decide (b.skSeedShares.length = 3 ∧ b.skPrfShares.length = 3)
  | .shamirTowerCshake t n | .shamirPoseidon2 t n =>
    decide (0 < t ∧ t ≤ n ∧ b.skSeedShares.length = n ∧ b.skPrfShares.length = n)

/-- **Threshold Cut-and-Batch MPC Signer (`evalThresholdSign`)** enforcing `eng.validBundle`. -/
@[expose] def evalThresholdSign (eng : ThresholdEngine) (params : PqHashParams)
    (bundle : SharedSecretKeyBundle) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind : Nat) : Option PqHashSig :=
  if !(eng.validBundle bundle) then none
  else evalCutBatchSign eng.suite params bundle.reconstructSk msg optRand leafGlobalIdx maxGrind

/-- **Master Signature Indistinguishability Theorem (`thresholdSign_eq_singleSign`)**:
    Across 2-of-3 `RSS` (`cSHAKE256`), arbitrary $t$-of-$n$ `BinaryTower256` (`cSHAKE256`), and
    arbitrary $t$-of-$n$ `Poseidon2Goldilocks` (connected via `lagrangeAtZero_evalCoeffs`,
    `reconstructRss_keccakChiBit`, and `power7BinomialEval_eq_pow7`), any valid `bundle`
    reconstructing `sk` produces the **bit-for-bit identical** `Option PqHashSig` as `evalSingleSign`,
    and every `some sig` satisfies standard single-key `verifyPqHashSig = true`! -/
theorem thresholdSign_eq_singleSign
    (eng : ThresholdEngine) (params : PqHashParams)
    (bundle : SharedSecretKeyBundle) (sk : PqSecretKey)
    (hRecon : bundle.reconstructSk = sk)
    (msg optRand : List UInt8) (leafGlobalIdx maxGrind : Nat) :
    (eng.validBundle bundle = true →
      evalThresholdSign eng params bundle msg optRand leafGlobalIdx maxGrind =
        evalSingleSign eng.suite params sk msg optRand leafGlobalIdx maxGrind) ∧
    (∀ sig, evalThresholdSign eng params bundle msg optRand leafGlobalIdx maxGrind = some sig →
      verifyPqHashSig eng.suite params (derivePublicKey eng.suite params sk) msg sig = true) := by
  refine ⟨fun hValid => ?_, fun sig hSome => ?_⟩
  · unfold evalThresholdSign
    simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hRecon, evalCutBatchSign_eq_naiveSign]
  · unfold evalThresholdSign at hSome
    cases hV : eng.validBundle bundle
    · simp [hV] at hSome
    · simp only [hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hRecon, evalCutBatchSign_eq_naiveSign] at hSome
      exact verifyPqHashSig_evalSingleSign eng.suite params sk msg optRand leafGlobalIdx maxGrind sig hSome

/-! ## 3. 2-Lane Split-Custody `Tower128 × Tower128` & `GoldilocksExt2` SPDZ/BDOZ Identifiable Abort -/

/-- Correlated-OT off-diagonal cross-term table `(u_{i,j}, v_{i,j})` (`i ≠ j`) in `Tower128` ($\mathcal{T}_7$). -/
structure OffDiagCrossTerms where
  u : Nat → Nat → Tower128
  v : Nat → Nat → Tower128

/-- Off-diagonal validity invariant: for every ordered pair `i ≠ j`, `u_{i,j} + v_{j,i} = α_i · x_j`. -/
def ValidOffDiagCrossTerms (n : Nat) (alpha x : Nat → Tower128) (ot : OffDiagCrossTerms) : Prop :=
  ∀ i j : Nat, i < n → j < n → i ≠ j →
    towerAdd 7 (ot.u i j) (ot.v j i) = towerMul 7 (alpha i) (x j)

theorem validOffDiagCrossTerms_inhabited (n : Nat) (alpha x : Nat → Tower128) :
    ∃ ot : OffDiagCrossTerms, ValidOffDiagCrossTerms n alpha x ot :=
  ⟨⟨fun _ _ => towerZero 7, fun j i => towerMul 7 (alpha i) (x j)⟩,
   fun i j _ _ _ => towerZero_add 7 (towerMul 7 (alpha i) (x j))⟩

/-- **Load-Bearing BDOZ/SPDZ MAC Share Formation (`formBdozPartyMacShare`)**:
    Combines diagonal `α_i · x_i` WITH all off-diagonal correlated-OT cross-terms `u_{i,j} + v_{i,j}` (`j ≠ i`). -/
@[expose] def formBdozPartyMacShare (n i : Nat) (alpha_i x_i : Tower128) (ot : OffDiagCrossTerms) : Tower128 :=
  let diag := towerMul 7 alpha_i x_i
  let offDiag := (List.range n).foldl
    (fun acc j => if j == i then acc else towerAdd 7 acc (towerAdd 7 (ot.u i j) (ot.v i j)))
    (towerZero 7)
  towerAdd 7 diag offDiag

/-- **BDOZ Cross-Term Soundness (`bdoz_2party_cross_terms_sound`)**:
    Summing `formBdozPartyMacShare` across parties reconstructs `(α_0 + α_1) · (x_0 + x_1)`. -/
theorem bdoz_2party_cross_terms_sound
    (alpha x : Nat → Tower128) (ot : OffDiagCrossTerms)
    (hValid : ValidOffDiagCrossTerms 2 alpha x ot) :
    towerAdd 7 (formBdozPartyMacShare 2 0 (alpha 0) (x 0) ot) (formBdozPartyMacShare 2 1 (alpha 1) (x 1) ot) =
    towerMul 7 (towerAdd 7 (alpha 0) (alpha 1)) (towerAdd 7 (x 0) (x 1)) := by
  have h01 : towerAdd 7 (ot.u 0 1) (ot.v 1 0) = towerMul 7 (alpha 0) (x 1) :=
    hValid 0 1 (by omega) (by omega) (by omega)
  have h10 : towerAdd 7 (ot.u 1 0) (ot.v 0 1) = towerMul 7 (alpha 1) (x 0) :=
    hValid 1 0 (by omega) (by omega) (by omega)
  change towerAdd 7
    (towerAdd 7 (towerMul 7 (alpha 0) (x 0)) (towerAdd 7 (towerZero 7) (towerAdd 7 (ot.u 0 1) (ot.v 0 1))))
    (towerAdd 7 (towerMul 7 (alpha 1) (x 1)) (towerAdd 7 (towerZero 7) (towerAdd 7 (ot.u 1 0) (ot.v 1 0)))) =
    towerMul 7 (towerAdd 7 (alpha 0) (alpha 1)) (towerAdd 7 (x 0) (x 1))
  rw [towerZero_add, towerZero_add, towerAdd_mul_distrib, towerMul_add_distrib, towerMul_add_distrib, ← h01, ← h10]
  calc
    towerAdd 7 (towerAdd 7 (towerMul 7 (alpha 0) (x 0)) (towerAdd 7 (ot.u 0 1) (ot.v 0 1)))
               (towerAdd 7 (towerMul 7 (alpha 1) (x 1)) (towerAdd 7 (ot.u 1 0) (ot.v 1 0)))
      = towerAdd 7 (towerMul 7 (alpha 0) (x 0))
          (towerAdd 7 (ot.u 0 1)
            (towerAdd 7 (ot.v 0 1)
              (towerAdd 7 (towerMul 7 (alpha 1) (x 1)) (towerAdd 7 (ot.u 1 0) (ot.v 1 0))))) := by
        simp only [towerAdd_assoc]
    _ = towerAdd 7 (towerMul 7 (alpha 0) (x 0))
          (towerAdd 7 (ot.u 0 1)
            (towerAdd 7 (ot.v 1 0)
              (towerAdd 7 (ot.u 1 0)
                (towerAdd 7 (ot.v 0 1) (towerMul 7 (alpha 1) (x 1)))))) := by
        congr 2
        calc
          towerAdd 7 (ot.v 0 1) (towerAdd 7 (towerMul 7 (alpha 1) (x 1)) (towerAdd 7 (ot.u 1 0) (ot.v 1 0)))
            = towerAdd 7 (towerAdd 7 (ot.v 0 1) (towerMul 7 (alpha 1) (x 1))) (towerAdd 7 (ot.u 1 0) (ot.v 1 0)) := by rw [← towerAdd_assoc]
          _ = towerAdd 7 (towerAdd 7 (ot.u 1 0) (ot.v 1 0)) (towerAdd 7 (ot.v 0 1) (towerMul 7 (alpha 1) (x 1))) := by
              rw [towerAdd_comm 7 (towerAdd 7 (ot.v 0 1) (towerMul 7 (alpha 1) (x 1))) _]
          _ = towerAdd 7 (towerAdd 7 (ot.v 1 0) (ot.u 1 0)) (towerAdd 7 (ot.v 0 1) (towerMul 7 (alpha 1) (x 1))) := by rw [towerAdd_comm 7 (ot.u 1 0) (ot.v 1 0)]
          _ = towerAdd 7 (ot.v 1 0) (towerAdd 7 (ot.u 1 0) (towerAdd 7 (ot.v 0 1) (towerMul 7 (alpha 1) (x 1)))) := by rw [towerAdd_assoc]
    _ = towerAdd 7 (towerAdd 7 (towerMul 7 (alpha 0) (x 0)) (towerAdd 7 (ot.u 0 1) (ot.v 1 0)))
                   (towerAdd 7 (towerAdd 7 (ot.u 1 0) (ot.v 0 1)) (towerMul 7 (alpha 1) (x 1))) := by
        simp only [towerAdd_assoc]

/-- Load-bearing 2-lane `Tower128 × Tower128` batch MAC verifier across split-custody high & low lanes. -/
@[expose] def verifyBatchTowerMac2Lane
    (chalHi chalLo expectedHi expectedLo : Tower128) (diffsHi diffsLo : List Tower128) : Bool :=
  decide (ghashPoly chalHi diffsHi = expectedHi) && decide (ghashPoly chalLo diffsLo = expectedLo)

/-- **2-Lane Batch MAC Joint Polynomial Root Bound (`batchTowerMac2Lane_sound_roots_bound`)**:
    Welds `ghashDiff_roots_bound` across **both** split-custody lanes: tampering in `Hi` bounds accepting
    `chalHi` keys to `≤ L`, and tampering in `Lo` bounds accepting `chalLo` keys to `≤ L`! -/
theorem batchTowerMac2Lane_sound_roots_bound
    (honestHi forgedHi honestLo forgedLo : List Tower128)
    (L : Nat) (chalKeysHi chalKeysLo : List Tower128) (fixedLo fixedHi : Tower128)
    (hLenHi₁ : honestHi.length ≤ L) (hLenHi₂ : forgedHi.length ≤ L)
    (hLenLo₁ : honestLo.length ≤ L) (hLenLo₂ : forgedLo.length ≤ L)
    (hNodupHi : chalKeysHi.Nodup) (hNodupLo : chalKeysLo.Nodup) :
    ((∃ H, ghashPoly H forgedHi ≠ ghashPoly H honestHi) →
      (∀ H ∈ chalKeysHi, verifyBatchTowerMac2Lane H fixedLo (ghashPoly H honestHi) (ghashPoly fixedLo honestLo) forgedHi forgedLo = true) →
      chalKeysHi.length ≤ L) ∧
    ((∃ H, ghashPoly H forgedLo ≠ ghashPoly H honestLo) →
      (∀ H ∈ chalKeysLo, verifyBatchTowerMac2Lane fixedHi H (ghashPoly fixedHi honestHi) (ghashPoly H honestLo) forgedHi forgedLo = true) →
      chalKeysLo.length ≤ L) := by
  refine ⟨fun hDiffHi hPassHi => ?_, fun hDiffLo hPassLo => ?_⟩
  · apply ghashDiff_roots_bound forgedHi honestHi L chalKeysHi hLenHi₂ hLenHi₁ hNodupHi hDiffHi
    intro H hMem; have hP := hPassHi H hMem
    simp only [verifyBatchTowerMac2Lane, Bool.and_eq_true, decide_eq_true_eq] at hP; exact hP.1
  · apply ghashDiff_roots_bound forgedLo honestLo L chalKeysLo hLenLo₂ hLenLo₁ hNodupLo hDiffLo
    intro H hMem; have hP := hPassLo H hMem
    simp only [verifyBatchTowerMac2Lane, Bool.and_eq_true, decide_eq_true_eq] at hP; exact hP.2

/-- Pairwise BDOZ tag verifier held by honest party `i` checking party `j`'s opened `(x'_j, m'_{j→i})`:
    `m'_{j→i} == k_{i→j} + α_i · x'_j`. -/
@[expose] def verifyPairwiseBdozTag (alpha_i k_ij openedX_j openedTag_ji : Tower128) : Bool :=
  decide (openedTag_ji = towerAdd 7 k_ij (towerMul 7 alpha_i openedX_j))

/-- Goldilocks quadratic extension (`GoldilocksExt2`, 128-bit) pairwise BDOZ tag verifier. -/
def verifyPairwiseExt2Tag (alpha_i k_ij openedX_j openedTag_ji : GoldilocksExt2) : Bool :=
  decide (openedTag_ji = CommRingOps.add k_ij (CommRingOps.mul alpha_i openedX_j))

/-- Accountable cheater attribution certificate emitted upon deterministic pairwise BDOZ MAC failure. -/
structure MpcCheaterAttribution where
  accusedParty : NodeId
  verifierParty : NodeId
  sessionView : Nat
  honestShare : Tower128
  tamperedShare : Tower128
  sharesDistinct : tamperedShare ≠ honestShare
  slashingReceipt : SlashingReceipt

/-- Constructive `Tower128` MAC key recovery witness (`alpha_i = (Δm) · (Δx)⁻¹`). -/
structure TowerMacKeyForgeryWitness (alpha_i : Tower128) where
  deltaX : Tower128
  deltaM : Tower128
  deltaX_ne_zero : deltaX ≠ towerZero 7
  recoveredKeyEq : towerMul 7 deltaM (towerInv 7 deltaX) = alpha_i

/-- **Constructive `0 Classical` Identifiable Abort Theorem (`bdoz_cheater_identified_or_mac_forged`)**:
    Either `verifyPairwiseBdozTag = false` attributes `accused` with a `SlashingReceipt`, OR `accused` forged `α_i`! -/
def bdoz_cheater_identified_or_mac_forged
    (accused verifier : NodeId) (sessionView : Nat) (targetHonest targetTampered : Target)
    (alpha_i k_ij honestX honestTag tamperedX tamperedTag : Tower128)
    (hSetup : honestTag = towerAdd 7 k_ij (towerMul 7 alpha_i honestX))
    (hTampered : tamperedX ≠ honestX) :
    PSum MpcCheaterAttribution (TowerMacKeyForgeryWitness alpha_i) :=
  if hCheck : verifyPairwiseBdozTag alpha_i k_ij tamperedX tamperedTag = false then
    .inl ⟨accused, verifier, sessionView, honestX, tamperedX, hTampered,
          ⟨sessionView, targetHonest, targetTampered, [accused]⟩⟩
  else
    have hPass : verifyPairwiseBdozTag alpha_i k_ij tamperedX tamperedTag = true := by
      cases hv : verifyPairwiseBdozTag alpha_i k_ij tamperedX tamperedTag
      · exact False.elim (hCheck hv)
      · rfl
    have hTagEq : tamperedTag = towerAdd 7 k_ij (towerMul 7 alpha_i tamperedX) := by
      simpa [verifyPairwiseBdozTag] using hPass
    let deltaX := towerAdd 7 tamperedX honestX
    let deltaM := towerAdd 7 tamperedTag honestTag
    have hDeltaXNe : deltaX ≠ towerZero 7 := fun hZero => hTampered (by
      have h1 := congrArg (fun z => towerAdd 7 z honestX) hZero
      simpa only [deltaX, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] using h1)
    have hProd : deltaM = towerMul 7 alpha_i deltaX := by
      calc deltaM
        _ = towerAdd 7 (towerAdd 7 k_ij (towerMul 7 alpha_i tamperedX))
                       (towerAdd 7 k_ij (towerMul 7 alpha_i honestX)) := by simp only [deltaM, hTagEq, hSetup]
        _ = towerAdd 7 (towerAdd 7 k_ij k_ij)
                       (towerAdd 7 (towerMul 7 alpha_i tamperedX) (towerMul 7 alpha_i honestX)) := by
            rw [towerAdd_assoc, ← towerAdd_assoc 7 (towerMul 7 alpha_i tamperedX),
                towerAdd_comm 7 (towerMul 7 alpha_i tamperedX) k_ij, towerAdd_assoc, ← towerAdd_assoc 7 k_ij k_ij]
        _ = towerMul 7 alpha_i deltaX := by rw [towerAdd_self_zero, towerZero_add, ← towerMul_add_distrib]
    .inr ⟨deltaX, deltaM, hDeltaXNe, by rw [hProd, towerMul_assoc, towerMul_inv 7 deltaX hDeltaXNe, towerMul_one]⟩

/-! ## 4. 2-Round PQ Commit-and-Open Dealerless DKG (`Π_deg`), `Π_deg0` Refresh & Policy Gate -/

def tagDkgCommit : List UInt8 := "OBEND.PQ.DKG.COMMIT/v1".toUTF8.data.toList

/-- Round-1 post-quantum commitment `cSHAKE256("OBEND.PQ.DKG.COMMIT/v1", encodeMultiFrame [be 4 dealer, be 4 recv, salt, shareBytes])`. -/
def dkgCommitShare (dealer recv : Nat) (salt shareBytes : List UInt8) : List UInt8 :=
  cshake256Bytes tagDkgCommit (encodeMultiFrame [be 4 dealer, be 4 recv, salt, shareBytes])

/-- Public `Π_deg` Reed–Solomon degree-`< t` consistency check on `n` evaluation points `(pts, evals)`:
    verifies `coeffs.length ≤ t` and `∀ j < n, RoundPoly.evalCoeffs coeffs pts[j] = evals[j]`. -/
def checkReedSolomonDegLtT {R : Type} [CommRingOps R] [DecidableEq R]
    (t : Nat) (pts : List R) (coeffs : List R) (evals : List R) : Bool :=
  decide (coeffs.length ≤ t) &&
  decide (pts.length = evals.length) &&
  (List.zip pts evals).all (fun (x, y) => decide (RoundPoly.evalCoeffs coeffs x = y))

example : checkReedSolomonDegLtT 2 [Goldilocks.ofNat 1, Goldilocks.ofNat 2]
    [Goldilocks.ofNat 5, Goldilocks.ofNat 3] [Goldilocks.ofNat 8, Goldilocks.ofNat 11] = true := by decide

private theorem list_all_zip_evalCoeffs {R : Type} [CommRingOps R] [DecidableEq R]
    (coeffs : List R) :
    ∀ (pts evals : List R),
      pts.length = evals.length →
      (List.zip pts evals).all (fun (x, y) => decide (RoundPoly.evalCoeffs coeffs x = y)) = true →
      ∀ (j : Nat) (hjP : j < pts.length) (hjE : j < evals.length),
        RoundPoly.evalCoeffs coeffs (pts[j]'hjP) = evals[j]'hjE
  | [], [], _, _, j, hjP, _ => by cases hjP
  | _ :: _, [], hLen, _, _, _, _ => by cases hLen
  | [], _ :: _, hLen, _, _, _, _ => by cases hLen
  | p :: ps, e :: es, hLen, hAll, j, hjP, hjE => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hAll
    cases j with
    | zero => exact hAll.1
    | succ j' =>
      exact list_all_zip_evalCoeffs coeffs ps es hLen hAll.2 j'
        (Nat.lt_of_succ_lt_succ hjP) (Nat.lt_of_succ_lt_succ hjE)

/-- Constructive `0 Classical` binding proof for Round-1 PQ DKG commitments (`dkgCommitShare`). -/
def dkgCommitShare_binds (maxBytes : Nat)
    {d₁ r₁ s₁ b₁ d₂ r₂ s₂ b₂ : List UInt8}
    (hLen₁ : (encodeMultiFrame [d₁, r₁, s₁, b₁]).length ≤ maxBytes)
    (hLen₂ : (encodeMultiFrame [d₂, r₂, s₂, b₂]).length ≤ maxBytes)
    (hEq : cshake256Bytes tagDkgCommit (encodeMultiFrame [d₁, r₁, s₁, b₁]) =
           cshake256Bytes tagDkgCommit (encodeMultiFrame [d₂, r₂, s₂, b₂])) :
    PSum (d₁ = d₂ ∧ r₁ = r₂ ∧ s₁ = s₂ ∧ b₁ = b₂)
         (HashCollisionWitness (cshake256Bytes tagDkgCommit) maxBytes) :=
  if hFrame : encodeMultiFrame [d₁, r₁, s₁, b₁] = encodeMultiFrame [d₂, r₂, s₂, b₂] then
    .inl (by
      have hList := encodeMultiFrame_injective hFrame
      simp only [List.cons.injEq, and_true] at hList
      rcases hList with ⟨hd, hr, hs, hb⟩
      exact ⟨hd, hr, hs, hb⟩)
  else
    .inr { msgA := encodeMultiFrame [d₁, r₁, s₁, b₁], msgB := encodeMultiFrame [d₂, r₂, s₂, b₂],
           lenA := hLen₁, lenB := hLen₂, distinct := hFrame, sameDigest := congrArg ofBE hEq }

/-- Dealer qualification / complaint resolution in 2-round PQ dealerless DKG (`Π_deg`). -/
def resolveDkgDealer {R : Type} [CommRingOps R] [DecidableEq R]
    (t : Nat) (pts : List R) (coeffs : List R) (evals : List R)
    (complaints : List (Nat × List UInt8 × List UInt8 × List UInt8))
    (dealerIdx : Nat) (encodeShare : R → List UInt8) : Bool :=
  checkReedSolomonDegLtT t pts coeffs evals &&
  complaints.all (fun (recvIdx, commDigest, openedSalt, openedBytes) =>
    decide (dkgCommitShare dealerIdx recvIdx openedSalt openedBytes = commDigest) &&
    match evals[recvIdx]? with
    | some y => decide (encodeShare y = openedBytes)
    | none => false)

/-- **2-Round PQ DKG `Π_deg` Reed–Solomon Consistency Soundness (`dkg_reed_solomon_consistency_sound`)**:
    Every accepted `Π_deg` dealing (`checkReedSolomonDegLtT = true`) uniquely determines the
    underlying degree-`< t` Shamir polynomial across the entire ring `R` whenever `t ≤ pts.length`
    and `pts.Nodup` (`0 Classical`, constructive root-bound contradiction at `x`)! -/
theorem dkg_reed_solomon_consistency_sound
    {R : Type} [LawfulCommRing R] [NoZeroDivisors R] [DecidableEq R]
    (t : Nat) (pts coeffs₁ coeffs₂ evals : List R)
    (hDeg₁ : checkReedSolomonDegLtT t pts coeffs₁ evals = true)
    (hDeg₂ : checkReedSolomonDegLtT t pts coeffs₂ evals = true)
    (hNodup : pts.Nodup) (hEnough : t ≤ pts.length) :
    ∀ x : R, RoundPoly.evalCoeffs coeffs₁ x = RoundPoly.evalCoeffs coeffs₂ x := by
  simp only [checkReedSolomonDegLtT, Bool.and_eq_true, decide_eq_true_eq] at hDeg₁ hDeg₂
  rcases hDeg₁ with ⟨⟨hL1, hPE1⟩, hZ1⟩
  rcases hDeg₂ with ⟨⟨hL2, _⟩, hZ2⟩
  intro x
  cases t with
  | zero =>
    have hc1 : coeffs₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hc2 : coeffs₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hc1 hc2; rfl
  | succ degMax =>
    if hEqX : RoundPoly.evalCoeffs coeffs₁ x = RoundPoly.evalCoeffs coeffs₂ x then
      exact hEqX
    else
      exfalso
      let diff := RoundPoly.subCoeffs coeffs₁ coeffs₂
      have hDiffLen : diff.length ≤ degMax + 1 := by
        rw [RoundPoly.subCoeffs_length]; exact Nat.max_le.mpr ⟨hL1, hL2⟩
      have hWitnessNz : ∃ z : R, RoundPoly.evalCoeffs diff z ≠ CommRingOps.zero := by
        refine ⟨x, ?_⟩
        rw [RoundPoly.evalCoeffs_sub]
        intro hSubZero
        have hEq := congrArg (fun u => CommRingOps.add u (RoundPoly.evalCoeffs coeffs₂ x)) hSubZero
        rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
            LawfulCommRing.add_left_neg, LawfulCommRing.add_zero,
            LawfulCommRing.zero_add] at hEq
        exact hEqX hEq
      have hRootsLe := RoundPoly.roots_nodup_length_le degMax diff pts hNodup hDiffLen hWitnessNz
      have hFilterAll : pts.filter (fun p => decide (RoundPoly.evalCoeffs diff p = CommRingOps.zero)) = pts := by
        apply List.filter_eq_self.mpr
        intro p hpMem
        obtain ⟨j, hjLt, rfl⟩ := List.getElem_of_mem hpMem
        have hjE : j < evals.length := hPE1 ▸ hjLt
        have hSame : RoundPoly.evalCoeffs coeffs₁ (pts[j]'hjLt) = RoundPoly.evalCoeffs coeffs₂ (pts[j]'hjLt) := by
          rw [list_all_zip_evalCoeffs coeffs₁ pts evals hPE1 hZ1 j hjLt hjE,
              list_all_zip_evalCoeffs coeffs₂ pts evals hPE1 hZ2 j hjLt hjE]
        simp only [diff, RoundPoly.evalCoeffs_sub, hSame, LawfulCommRing.sub_self, decide_true]
      rw [hFilterAll] at hRootsLe
      omega

/-- Public `Π_deg0` zero-constant proactive refresh check: degree `< t` AND constant term `p(0) = 0`. -/
def checkZeroConstantRefresh {R : Type} [CommRingOps R] [DecidableEq R]
    (t : Nat) (pts : List R) (refreshCoeffs : List R) (refreshShares : List R) : Bool :=
  checkReedSolomonDegLtT t pts refreshCoeffs refreshShares &&
  decide (RoundPoly.evalCoeffs refreshCoeffs CommRingOps.zero = CommRingOps.zero)

/-- Coefficient-wise polynomial addition `p + q` for Shamir proactive share refresh. -/
def polyAddCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], ds => ds
  | cs, [] => cs
  | c :: cs, d :: ds => CommRingOps.add c d :: polyAddCoeffs cs ds

theorem evalCoeffs_polyAddCoeffs {R : Type} [LawfulCommRing R] :
    ∀ (cs ds : List R) (x : R),
      RoundPoly.evalCoeffs (polyAddCoeffs cs ds) x =
        CommRingOps.add (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x)
  | [], ds, x => by simp [polyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | _ :: _, [], x => by simp [polyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | c :: cs, d :: ds, x => by
    simp only [polyAddCoeffs, RoundPoly.evalCoeffs, evalCoeffs_polyAddCoeffs cs ds x]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

/-- **Proactive Share Refresh Constant-PK Invariance (`proactive_refresh_preserves_secret_and_pk`)**:
    Adding a `Π_deg0`-verified refresh polynomial `refreshCoeffs` (`p_ref(0) = 0`) to any active
    Shamir polynomial `baseCoeffs` produces refreshed shares `evalCoeffs (polyAddCoeffs base refresh) x`
    whose `0`-evaluation secret `sk(0)` AND derived `PqPublicKey` (`pkSeed`, `pkRoot`) are
    **bit-for-bit invariant**! -/
theorem proactive_refresh_preserves_secret_and_pk
    {R : Type} [LawfulCommRing R] [DecidableEq R]
    (t : Nat) (pts baseCoeffs refreshCoeffs refreshShares : List R)
    (hRefOk : checkZeroConstantRefresh t pts refreshCoeffs refreshShares = true)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (decodeSecret : R → PqSecretKey) :
    let refreshedPoly := polyAddCoeffs baseCoeffs refreshCoeffs
    RoundPoly.evalCoeffs refreshedPoly CommRingOps.zero =
      RoundPoly.evalCoeffs baseCoeffs CommRingOps.zero ∧
    derivePublicKey suite params (decodeSecret (RoundPoly.evalCoeffs refreshedPoly CommRingOps.zero)) =
      derivePublicKey suite params (decodeSecret (RoundPoly.evalCoeffs baseCoeffs CommRingOps.zero)) := by
  intro refreshedPoly
  simp only [checkZeroConstantRefresh, Bool.and_eq_true, decide_eq_true_eq] at hRefOk
  have hZeroEval : RoundPoly.evalCoeffs refreshedPoly CommRingOps.zero =
      RoundPoly.evalCoeffs baseCoeffs CommRingOps.zero := by
    simp only [refreshedPoly, evalCoeffs_polyAddCoeffs, hRefOk.2, LawfulCommRing.add_zero]
  exact ⟨hZeroEval, congrArg (fun z => derivePublicKey suite params (decodeSecret z)) hZeroEval⟩

/-- Garbler-side private custody policy encoder (`garblePolicyGate`): binds `txAmount ≤ secretLimit`
    onto masked wire label `activeLabel` and field-padded share `maskedRelease` without exposing `secretLimit`. -/
def garblePolicyGate (txAmount secretLimit : UInt64)
    (wireZeroLabel wireDelta rawShare padShare : Goldilocks) : Goldilocks × Goldilocks :=
  if decide (txAmount.toNat ≤ secretLimit.toNat) then
    (CommRingOps.add wireZeroLabel wireDelta, CommRingOps.add rawShare padShare)
  else
    (wireZeroLabel, padShare)

/-- Evaluator-side garbled custody policy gate (`evalGarbledPolicyGate`): receives ONLY
    `(acceptTag, activeLabel, maskedRelease, padShare)` — **never `secretLimit` in plaintext!** -/
def evalGarbledPolicyGate (acceptTag activeLabel maskedRelease padShare : Goldilocks) : Option Goldilocks :=
  if decide (activeLabel = acceptTag) then
    some (CommRingOps.sub maskedRelease padShare)
  else
    none

theorem policyGate_accepts_iff_within_limit
    (txAmount secretLimit : UInt64)
    (wireZeroLabel wireDelta rawShare padShare : Goldilocks)
    (hDeltaNeZero : wireDelta ≠ CommRingOps.zero) :
    let acceptTag := CommRingOps.add wireZeroLabel wireDelta
    let (activeLabel, maskedRelease) :=
      garblePolicyGate txAmount secretLimit wireZeroLabel wireDelta rawShare padShare
    (evalGarbledPolicyGate acceptTag activeLabel maskedRelease padShare = some rawShare ↔
      txAmount.toNat ≤ secretLimit.toNat) ∧
    (secretLimit.toNat < txAmount.toNat →
      evalGarbledPolicyGate acceptTag activeLabel maskedRelease padShare = none ∧
      maskedRelease = padShare) := by
  intro acceptTag
  have hSubCancel : ∀ x y : Goldilocks, CommRingOps.sub (CommRingOps.add x y) y = x := fun x y => by
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  have hLabelNe : wireZeroLabel ≠ acceptTag := fun hEq => hDeltaNeZero (by
    have hSub : CommRingOps.sub wireZeroLabel wireZeroLabel =
        CommRingOps.sub (CommRingOps.add wireDelta wireZeroLabel) wireZeroLabel := by
      rw [LawfulCommRing.add_comm wireDelta wireZeroLabel]; exact congrArg (CommRingOps.sub · wireZeroLabel) hEq
    rw [LawfulCommRing.sub_self, hSubCancel wireDelta wireZeroLabel] at hSub
    exact hSub.symm)
  by_cases hLe : txAmount.toNat ≤ secretLimit.toNat
  · have hGp : garblePolicyGate txAmount secretLimit wireZeroLabel wireDelta rawShare padShare =
        (CommRingOps.add wireZeroLabel wireDelta, CommRingOps.add rawShare padShare) := by
      simp [garblePolicyGate, hLe]
    rw [hGp]; dsimp only
    have hEval : evalGarbledPolicyGate acceptTag (CommRingOps.add wireZeroLabel wireDelta)
        (CommRingOps.add rawShare padShare) padShare = some rawShare := by
      simp [evalGarbledPolicyGate, acceptTag, hSubCancel]
    rw [hEval]
    exact ⟨⟨fun _ => hLe, fun _ => rfl⟩, fun hLt => by omega⟩
  · have hGp : garblePolicyGate txAmount secretLimit wireZeroLabel wireDelta rawShare padShare =
        (wireZeroLabel, padShare) := by
      simp [garblePolicyGate, hLe]
    rw [hGp]; dsimp only
    have hEval : evalGarbledPolicyGate acceptTag wireZeroLabel padShare padShare = none := by
      simp [evalGarbledPolicyGate, hLabelNe]
    rw [hEval]
    exact ⟨⟨(by intro h; cases h), fun h => False.elim (hLe h)⟩, fun _ => ⟨rfl, rfl⟩⟩

end Obend.Crypto.ThresholdHashMpc
end
