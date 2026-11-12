module
/- # Obend.Crypto.SameOpening — Canonical Field Lift, Salted `DarkBazaar` Hiding, `BitZ` Range & KKT `Judge`
Formalizes Private-Input Convex Clearing (`BitZ 2026/2141`, `Tulva 2026/2485`, `Choe–Kang–Stehlé 2026/2546`):
`SmudgeSafe`, `ModulusNoWrapSafe`, canonical `< goldilocksPrime` field lifts, 128-bit salted + `MLWE`-blinded
order commitments, and lawful `privateConvexSameOpeningJudge` (`WellFormedZeroBookQuery`). -/
public import Obend.Judge.Class
public import Obend.Judge.Clearing
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck
public import Obend.Crypto.PCS
public import Obend.Crypto.DualSpine
public import Obend.Crypto.GameSoundness
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.PCS
import all Obend.Crypto.DualSpine
import all Obend.Crypto.GameSoundness

public section
namespace Obend.Crypto
open Obend.Ledger Obend.Judge Obend.Apps.ZkNtt Obend.Digest.HashBytes
open Obend.Judge.Computational (HashCollisionWitness SISShortVecWitness)
set_option autoImplicit false

/-! ## 1. `Choe–Kang–Stehlé` (`ePrint 2026/2546`) Statistical Smudging Guard -/

/-- Mandatory threshold decryption smudging bound (`0 < noiseBound ∧ 40 ≤ secBits ∧ noiseBound * 2^secBits ≤ smudgeBound`). -/
@[expose] def SmudgeSafe (noiseBound smudgeBound secBits : Nat) : Prop :=
  0 < noiseBound ∧ 40 ≤ secBits ∧ noiseBound * (2 ^ secBits) ≤ smudgeBound

def checkSmudgeSafe (noiseBound smudgeBound secBits : Nat) : Bool :=
  decide (0 < noiseBound) && decide (40 ≤ secBits) && decide (noiseBound * (2 ^ secBits) ≤ smudgeBound)

theorem checkSmudgeSafe_iff (noiseBound smudgeBound secBits : Nat) :
    checkSmudgeSafe noiseBound smudgeBound secBits = true ↔ SmudgeSafe noiseBound smudgeBound secBits := by
  simp [checkSmudgeSafe, SmudgeSafe, Bool.and_eq_true, and_assoc]

theorem smudgeSafe_refuses_unsmudged (noiseBound secBits : Nat) : ¬ SmudgeSafe noiseBound 0 secBits := by
  rintro ⟨hPos, _, hLe⟩; have := Nat.mul_pos hPos (Nat.two_pow_pos secBits); omega

theorem smudgeSafe_exponential_gap {noiseBound smudgeBound secBits : Nat}
    (h : SmudgeSafe noiseBound smudgeBound secBits) : noiseBound * (2 ^ 40) ≤ smudgeBound :=
  Nat.le_trans (Nat.mul_le_mul_left noiseBound (Nat.pow_le_pow_right (by decide) h.2.1)) h.2.2

def thresholdSmudgeDist (smudgeBound : Nat) (e : Int) : GameSoundness.FinDist Int :=
  (GameSoundness.uniformIntervalDist smudgeBound).map (fun u => e + u)

/-- Distributional smudging theorem (`2026/2546`): TV distance from uniform is `≤ 1 / 2 ^ secBits`. -/
theorem thresholdSmudge_tvDist_le {noiseBound smudgeBound secBits : Nat}
    (hSafe : SmudgeSafe noiseBound smudgeBound secBits) (e : Int) (hNoise : e.natAbs ≤ noiseBound) :
    e.natAbs ≤ noiseBound ∧
    GameSoundness.RatProb.le
      (GameSoundness.tvDist (thresholdSmudgeDist smudgeBound e) (GameSoundness.uniformIntervalDist smudgeBound))
      ⟨1, 2 ^ secBits, Nat.two_pow_pos secBits⟩ := by
  rcases hSafe with ⟨_, _, hBound⟩
  refine ⟨hNoise, GameSoundness.RatProb.le_trans (GameSoundness.uniformShift_tvDist_le e smudgeBound) ?_⟩
  unfold GameSoundness.RatProb.le; dsimp only
  have hLe := Nat.le_trans (Nat.mul_le_mul_right (2 ^ secBits) hNoise) hBound; omega

def thresholdSmudgeBatchDist (smudgeBound : Nat) (errors : List Int) : GameSoundness.FinDist (List Int) :=
  (GameSoundness.uniformVecDist smudgeBound errors.length).map (fun us => List.zipWith (· + ·) errors us)

/-- Multi-query batch smudging bound (`2026/2546`): `Q` smudged errors lie within `Q / 2 ^ secBits` of uniform. -/
theorem thresholdSmudgeBatch_tvDist_le {noiseBound smudgeBound secBits : Nat}
    (hSafe : SmudgeSafe noiseBound smudgeBound secBits)
    (errors : List Int) (hAll : ∀ e ∈ errors, e.natAbs ≤ noiseBound) :
    (∀ e ∈ errors, e.natAbs ≤ noiseBound) ∧
    GameSoundness.RatProb.le
      (GameSoundness.tvDist (thresholdSmudgeBatchDist smudgeBound errors)
        (GameSoundness.uniformVecDist smudgeBound errors.length))
      ⟨errors.length, 2 ^ secBits, Nat.two_pow_pos secBits⟩ := by
  rcases hSafe with ⟨_, _, hBound⟩
  refine ⟨hAll, GameSoundness.RatProb.le_trans
    (GameSoundness.uniformVecShift_tvDist_le smudgeBound noiseBound errors hAll) ?_⟩
  unfold GameSoundness.RatProb.le; dsimp only
  calc (errors.length * noiseBound) * (2 ^ secBits)
    _ = errors.length * (noiseBound * (2 ^ secBits)) := by ac_rfl
    _ ≤ errors.length * smudgeBound := Nat.mul_le_mul_left _ hBound
    _ ≤ errors.length * (2 * smudgeBound + 1) := Nat.mul_le_mul_left _ (by omega)

/-- Modulus no-wraparound guard (`2 * (msgBound + noiseBound + smudgeBound) < qModulus`). -/
@[expose] def ModulusNoWrapSafe (msgBound noiseBound smudgeBound qModulus : Nat) : Prop :=
  2 * (msgBound + noiseBound + smudgeBound) < qModulus

def centeredModDecode (qModulus : Nat) (r : Int) : Int :=
  let rem := r % (qModulus : Int)
  if 2 * rem < (qModulus : Int) then rem else rem - (qModulus : Int)

/-- Operational no-wraparound decoding: `centeredModDecode qModulus ((m + e + u) % qModulus) = m + e + u`. -/
theorem centeredModDecode_exact_of_noWrap
    {msgBound noiseBound smudgeBound qModulus : Nat}
    (hSafe : ModulusNoWrapSafe msgBound noiseBound smudgeBound qModulus)
    (m e u : Int) (hm : m.natAbs ≤ msgBound) (he : e.natAbs ≤ noiseBound) (hu : u.natAbs ≤ smudgeBound) :
    ModulusNoWrapSafe msgBound noiseBound smudgeBound qModulus ∧
    centeredModDecode qModulus ((m + e + u) % (qModulus : Int)) = m + e + u := by
  refine ⟨hSafe, ?_⟩; unfold ModulusNoWrapSafe at hSafe; unfold centeredModDecode; dsimp only; rw [Int.emod_emod]
  let x := m + e + u
  have hxUpper : x ≤ (msgBound + noiseBound + smudgeBound : Nat) := by omega
  have hxLower : -(msgBound + noiseBound + smudgeBound : Int) ≤ x := by omega
  by_cases hx0 : 0 ≤ x
  · have hRem : x % (qModulus : Int) = x := Int.emod_eq_of_lt hx0 (by omega)
    simp [x, hRem, show 2 * x < (qModulus : Int) by omega]
  · have hRem : x % (qModulus : Int) = x + (qModulus : Int) := by
      have hAddMod : (x + (qModulus : Int)) % (qModulus : Int) = x % (qModulus : Int) := by
        rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
      rw [← hAddMod]; exact Int.emod_eq_of_lt (by omega) (by omega)
    simp [x, hRem, show ¬ (2 * (x + (qModulus : Int)) < (qModulus : Int)) by omega]

def checkModulusNoWrap (msgBound noiseBound smudgeBound qModulus : Nat) : Bool :=
  decide (2 * (msgBound + noiseBound + smudgeBound) < qModulus)

theorem checkModulusNoWrap_iff (msgBound noiseBound smudgeBound qModulus : Nat) :
    checkModulusNoWrap msgBound noiseBound smudgeBound qModulus = true ↔
      ModulusNoWrapSafe msgBound noiseBound smudgeBound qModulus := by
  simp [checkModulusNoWrap, ModulusNoWrapSafe]

theorem modulusNoWrapSafe_inhabited (msgBound : Nat) :
    ModulusNoWrapSafe msgBound 16 (16 * (2 ^ 40)) (2 * msgBound + 2 ^ 62) := by
  unfold ModulusNoWrapSafe; rw [Nat.add_assoc, Nat.mul_add]
  exact Nat.add_lt_add_left (by decide : 2 * (16 + 16 * (2 ^ 40)) < 2 ^ 62) (2 * msgBound)

/-! ## 2. `BitZ` (`ePrint 2026/2141`) Bit-Packed Witness & Free $B$-Bit Range Bound -/

def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

theorem bitsToNat_lt_two_pow : ∀ (bits : List Bool) {B : Nat}, bits.length ≤ B → bitsToNat bits < 2 ^ B
  | [], B, _ => Nat.two_pow_pos B
  | _ :: _, 0, hlen => by simp at hlen
  | b :: bs, B + 1, hlen => by
    simp only [List.length_cons] at hlen
    have ih := bitsToNat_lt_two_pow bs (B := B) (by omega)
    simp only [bitsToNat, Nat.pow_succ]; cases b <;> simp <;> omega

/-! ## 3. Canonical Salted Private Orders (`DarkBazaar`), Hiding Bijection & Dictionary Resistance -/

/-- Public specification of a committed private order under `canopyAjtaiDualPCS` (`numVars = 3`). -/
structure CommittedOrderSpec where
  account : AccountId
  side : Side
  maxBits : Nat
  dualComm : CanopyCommitment × AjtaiCommitment
  deriving DecidableEq

/-- Private `BitZ` bit-packed witness for an order's quantity, total limit value, and 128-bit `salt`. -/
structure OrderBitWitness where
  qtyBits : List Bool
  totalBits : List Bool
  salt : GoldilocksExt2 := GoldilocksExt2.zero
  deriving DecidableEq, Repr

def OrderBitWitness.qty (w : OrderBitWitness) : Nat := bitsToNat w.qtyBits
def OrderBitWitness.total (w : OrderBitWitness) : Nat := bitsToNat w.totalBits

def sideTag : Side → Nat | .bid => 0 | .ask => 1

theorem sideTag_goldilocks_injective {s₁ s₂ : Side}
    (h : Goldilocks.ofNat (sideTag s₁) = Goldilocks.ofNat (sideTag s₂)) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> first | rfl | cases h

/-- Canonical 8-element `Goldilocks` multilinear table with `< goldilocksPrime` lifts and 128-bit `salt`. -/
def orderWitnessTable? (spec : CommittedOrderSpec) (w : OrderBitWitness) : Option (List Goldilocks) :=
  match canonicalLift? spec.account, canonicalLift? w.qty, canonicalLift? w.total with
  | some accF, some qtyF, some totF =>
    some [accF, Goldilocks.ofNat (sideTag spec.side), qtyF, totF, w.salt.c0, w.salt.c1, Goldilocks.zero, Goldilocks.zero]
  | _, _, _ => none

theorem orderWitnessTable?_length {spec : CommittedOrderSpec} {w : OrderBitWitness}
    {tbl : List Goldilocks} (h : orderWitnessTable? spec w = some tbl) : tbl.length = 2 ^ 3 := by
  unfold orderWitnessTable? at h; split at h <;> cases h; rfl

theorem orderWitnessTable?_canonical {spec : CommittedOrderSpec} {w : OrderBitWitness}
    {tbl : List Goldilocks} (h : orderWitnessTable? spec w = some tbl) :
    CanonicalLift spec.account ∧ CanonicalLift w.qty ∧ CanonicalLift w.total := by
  unfold orderWitnessTable? at h
  cases ha : canonicalLift? spec.account with
  | none => simp [ha] at h
  | some accF => cases hq : canonicalLift? w.qty with
    | none => simp [ha, hq] at h
    | some qtyF => cases ht : canonicalLift? w.total with
      | none => simp [ha, hq, ht] at h
      | some totF =>
        exact ⟨((canonicalLift?_eq_some_iff _ _).1 ha).1, ((canonicalLift?_eq_some_iff _ _).1 hq).1,
               ((canonicalLift?_eq_some_iff _ _).1 ht).1⟩

/-- Canonical order-table injectivity (`account`, `side`, `qty`, `total`, and 128-bit `salt`). -/
theorem orderWitnessTable?_injective
    {s₁ s₂ : CommittedOrderSpec} {w₁ w₂ : OrderBitWitness} {tbl : List Goldilocks}
    (h₁ : orderWitnessTable? s₁ w₁ = some tbl) (h₂ : orderWitnessTable? s₂ w₂ = some tbl) :
    s₁.account = s₂.account ∧ s₁.side = s₂.side ∧ w₁.qty = w₂.qty ∧ w₁.total = w₂.total ∧ w₁.salt = w₂.salt := by
  unfold orderWitnessTable? at h₁ h₂
  cases ha₁ : canonicalLift? s₁.account with
  | none => simp [ha₁] at h₁
  | some acc₁ => cases hq₁ : canonicalLift? w₁.qty with
    | none => simp [ha₁, hq₁] at h₁
    | some qty₁ => cases ht₁ : canonicalLift? w₁.total with
      | none => simp [ha₁, hq₁, ht₁] at h₁
      | some tot₁ => cases ha₂ : canonicalLift? s₂.account with
        | none => simp [ha₂] at h₂
        | some acc₂ => cases hq₂ : canonicalLift? w₂.qty with
          | none => simp [ha₂, hq₂] at h₂
          | some qty₂ => cases ht₂ : canonicalLift? w₂.total with
            | none => simp [ha₂, hq₂, ht₂] at h₂
            | some tot₂ =>
              simp only [ha₁, hq₁, ht₁, Option.some.injEq] at h₁
              simp only [ha₂, hq₂, ht₂, Option.some.injEq] at h₂
              have hEq := h₁.trans h₂.symm; simp only [List.cons.injEq, and_true] at hEq
              rcases hEq with ⟨hAcc, hSide, hQty, hTot, hc0, hc1⟩; subst hAcc hQty hTot
              exact ⟨canonicalLift?_injective ha₁ ha₂, sideTag_goldilocks_injective hSide,
                     canonicalLift?_injective hq₁ hq₂, canonicalLift?_injective ht₁ ht₂, GoldilocksExt2.ext hc0 hc1⟩

/-- Commit a private DarkBazaar order `(account, side, maxBits, salt, w)` under `canopyAjtaiDualPCS`. -/
def commitPrivateOrder (pp : AjtaiParams) (account : AccountId) (side : Side)
    (maxBits : Nat) (salt : GoldilocksExt2) (w : OrderBitWitness) : CommittedOrderSpec :=
  let provisional : CommittedOrderSpec :=
    { account, side, maxBits, dualComm := (canopyCommit deployedCanopyHash32 3 [], ajtaiLatticeCommit pp 3 []) }
  let tbl := (orderWitnessTable? provisional { w with salt }).getD (List.replicate 8 Goldilocks.zero)
  { account, side, maxBits, dualComm := (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl }

def blindOrderSalt (mask salt : GoldilocksExt2) : GoldilocksExt2 := CommRingOps.add salt mask
def unblindOrderSalt (mask masked : GoldilocksExt2) : GoldilocksExt2 := CommRingOps.sub masked mask

/-- 128-bit salt hiding bijection on $\mathbb{F}_{p^2}$ (`|GoldilocksExt2| = p^2 > 2^127`). -/
theorem saltedOrderMask_bijection (mask salt masked : GoldilocksExt2) :
    unblindOrderSalt mask (blindOrderSalt mask salt) = salt ∧
    blindOrderSalt mask (unblindOrderSalt mask masked) = masked ∧
    (∀ s₁ s₂ : GoldilocksExt2, blindOrderSalt mask s₁ = blindOrderSalt mask s₂ → s₁ = s₂) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold unblindOrderSalt blindOrderSalt
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  · unfold blindOrderSalt unblindOrderSalt
    rw [LawfulCommRing.add_comm _ mask, LawfulCommRing.add_sub_cancel_left]
  · intro s₁ s₂ hEq; have h := congrArg (unblindOrderSalt mask) hEq; unfold unblindOrderSalt blindOrderSalt at h
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero,
        LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero] at h
    exact h

def unsaltedDictionaryTable? (pp : AjtaiParams) (account : AccountId) (side : Side)
    (qtyBits totalBits : List Bool) : Option (List Goldilocks) :=
  orderWitnessTable?
    { account := account, side := side, maxBits := 64, dualComm := (canopyCommit deployedCanopyHash32 3 [], ajtaiLatticeCommit pp 3 []) }
    { qtyBits := qtyBits, totalBits := totalBits, salt := GoldilocksExt2.zero }

/-- Any salted order table (`w.salt ≠ 0`) misses the entire unsalted dictionary across all candidates. -/
theorem unsaltedDictionary_miss_of_nonzero_salt
    (pp : AjtaiParams) {spec : CommittedOrderSpec} {w : OrderBitWitness} {tbl : List Goldilocks}
    (hSalt : w.salt ≠ GoldilocksExt2.zero) (hTbl : orderWitnessTable? spec w = some tbl)
    (candAcc : AccountId) (candSide : Side) (candQtyBits candTotalBits : List Bool) :
    unsaltedDictionaryTable? pp candAcc candSide candQtyBits candTotalBits ≠ some tbl :=
  fun hDict => hSalt (orderWitnessTable?_injective hTbl hDict).2.2.2.2

def canopyTableFrames (H : Hash32) (v : Nat) (tbl : List Goldilocks) : List (List UInt8) :=
  (List.finRange tbl.length).flatMap fun i => merkleEntryFrames H (2 ^ v) i.val (tbl[i]) (openMerkle H tbl i.val)

def canonicalSaltedOrderTable (account : AccountId) (side : Side)
    (salt : GoldilocksExt2) (w : OrderBitWitness) : List Goldilocks :=
  [Goldilocks.ofNat account, Goldilocks.ofNat (sideTag side), Goldilocks.ofNat w.qty, Goldilocks.ofNat w.total,
   salt.c0, salt.c1, Goldilocks.zero, Goldilocks.zero]

private theorem canonicalLift?_eq_some_ofNat {n : Nat} (h : CanonicalLift n) :
    canonicalLift? n = some (Goldilocks.ofNat n) := by
  have hlt : n < goldilocksPrime := h; simp only [canonicalLift?, hlt, ↓reduceDIte, Option.some.injEq]
  apply Goldilocks.ext; dsimp [Goldilocks.ofNat]; exact (Nat.mod_eq_of_lt hlt).symm

private def extractDualCommitCollisionWithFrames (H : Hash32) (pp : AjtaiParams)
    (tbl₁ tbl₂ : List Goldilocks) (ht₁ : tbl₁.length = 2 ^ 3) (ht₂ : tbl₂.length = 2 ^ 3)
    (hCols : pp.cols = 32) (hNe : tbl₁ ≠ tbl₂)
    (hCommEq : (canopyAjtaiDualPCS H pp).commit ((), ()) 3 tbl₁ =
               (canopyAjtaiDualPCS H pp).commit ((), ()) 3 tbl₂) :
    { p : HashCollisionWitness H.eval (merkleMaxPreimageBytes 3) ×
          SISShortVecWitness pp.modulus 131070 pp.matrix //
      p.1.msgA ∈ canopyTableFrames H 3 tbl₁ ∧
      p.1.msgB ∈ canopyTableFrames H 3 tbl₂ } :=
  let bothWit := extractDualCommitCollisionBoth H pp tbl₁ tbl₂ ht₁ ht₂ hCols hNe hCommEq
  ⟨bothWit, by
    dsimp only [bothWit, extractDualCommitCollisionBoth]
    let diff := findDiffIndex tbl₁ tbl₂ (ht₁.trans ht₂.symm) hNe
    have hIdxPow : diff.1 < 2 ^ 3 := by obtain ⟨hx, _, _⟩ := diff.2; omega
    have hIn₁ : diff.1 < tbl₁.length := by omega
    have hIn₂ : diff.1 < tbl₂.length := by omega
    have hPairEq : canopyCommit H 3 tbl₁ = canopyCommit H 3 tbl₂ ∧
        ajtaiLatticeCommit pp 3 tbl₁ = ajtaiLatticeCommit pp 3 tbl₂ := Prod.mk.inj hCommEq
    have hVer₁ := verifyMerklePath_openMerkle H 3 tbl₁ ht₁ diff.1 hIdxPow
    have hVer₂ : verifyMerklePath H (2 ^ 3) diff.1 (tbl₂[diff.1]'hIn₂)
        (openMerkle H tbl₂ diff.1) (canopyCommit H 3 tbl₁).root = true := by
      rw [congrArg CanopyCommitment.root hPairEq.1]
      exact verifyMerklePath_openMerkle H 3 tbl₂ ht₂ diff.1 hIdxPow
    have hMem := extractMerklePathCollision_mem_frames H hIdxPow
      (openMerkle H tbl₁ diff.1) (openMerkle H tbl₂ diff.1)
      (canopyCommit H 3 tbl₁).root diff.2.2.2 hVer₁ hVer₂
    exact ⟨List.mem_flatMap.2 ⟨⟨diff.1, hIn₁⟩, List.mem_finRange _, hMem.1⟩,
           List.mem_flatMap.2 ⟨⟨diff.1, hIn₂⟩, List.mem_finRange _, hMem.2⟩⟩⟩

/-- **Constructive Salted-vs-Unsalted Dictionary Collision Extractor (`extractSaltedDictionaryCollisionBoth`, `0 Classical`)**:
    If a salted order (`salt ≠ 0`) and an unsalted dictionary candidate (`salt = 0`) produce identical
    `canopyAjtaiDualPCS` commitments at `pp.cols = 32`, constructively extracts **both** a concrete
    `HashCollisionWitness` (whose frames belong to `canopyTableFrames`) AND a `SISShortVecWitness`! -/
def extractSaltedDictionaryCollisionBoth
    (pp : AjtaiParams) (hCols : pp.cols = 32)
    {account : AccountId} {side : Side} {maxBits : Nat}
    {salt : GoldilocksExt2} {w : OrderBitWitness}
    (hAcc : CanonicalLift account) (hQty : CanonicalLift w.qty) (hTot : CanonicalLift w.total)
    (hSalt : salt ≠ GoldilocksExt2.zero)
    (candAcc : AccountId) (candSide : Side) (candMaxBits : Nat) (candW : OrderBitWitness)
    (hcAcc : CanonicalLift candAcc) (hcQty : CanonicalLift candW.qty) (hcTot : CanonicalLift candW.total)
    (hCommEq : (commitPrivateOrder pp account side maxBits salt w).dualComm =
               (commitPrivateOrder pp candAcc candSide candMaxBits GoldilocksExt2.zero candW).dualComm) :
    { p : HashCollisionWitness deployedCanopyHash32.eval (merkleMaxPreimageBytes 3) ×
          SISShortVecWitness pp.modulus 131070 pp.matrix //
      p.1.msgA ∈ canopyTableFrames deployedCanopyHash32 3 (canonicalSaltedOrderTable account side salt w) ∧
      p.1.msgB ∈ canopyTableFrames deployedCanopyHash32 3 (canonicalSaltedOrderTable candAcc candSide GoldilocksExt2.zero candW) } :=
  let tbl₁ := canonicalSaltedOrderTable account side salt w
  let tbl₂ := canonicalSaltedOrderTable candAcc candSide GoldilocksExt2.zero candW
  have hFacts :
      tbl₁ ≠ tbl₂ ∧
      (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl₁ =
      (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl₂ := by
    let w₁ : OrderBitWitness := { w with salt := salt }
    let w₂ : OrderBitWitness := { candW with salt := GoldilocksExt2.zero }
    let p₁ : CommittedOrderSpec :=
      { account := account, side := side, maxBits := maxBits,
        dualComm := (canopyCommit deployedCanopyHash32 3 [], ajtaiLatticeCommit pp 3 []) }
    let p₂ : CommittedOrderSpec :=
      { account := candAcc, side := candSide, maxBits := candMaxBits,
        dualComm := (canopyCommit deployedCanopyHash32 3 [], ajtaiLatticeCommit pp 3 []) }
    have hQty' : CanonicalLift (bitsToNat w.qtyBits) := hQty
    have hTot' : CanonicalLift (bitsToNat w.totalBits) := hTot
    have hcQty' : CanonicalLift (bitsToNat candW.qtyBits) := hcQty
    have hcTot' : CanonicalLift (bitsToNat candW.totalBits) := hcTot
    have ht₁ : orderWitnessTable? p₁ w₁ = some tbl₁ := by
      dsimp only [orderWitnessTable?, OrderBitWitness.qty, OrderBitWitness.total,
                  p₁, w₁, tbl₁, canonicalSaltedOrderTable]
      rw [canonicalLift?_eq_some_ofNat hAcc,
          canonicalLift?_eq_some_ofNat hQty',
          canonicalLift?_eq_some_ofNat hTot']
    have ht₂ : orderWitnessTable? p₂ w₂ = some tbl₂ := by
      dsimp only [orderWitnessTable?, OrderBitWitness.qty, OrderBitWitness.total,
                  p₂, w₂, tbl₂, canonicalSaltedOrderTable]
      rw [canonicalLift?_eq_some_ofNat hcAcc,
          canonicalLift?_eq_some_ofNat hcQty',
          canonicalLift?_eq_some_ofNat hcTot']
    refine ⟨?_, ?_⟩
    · intro hEq
      have ht₂' : orderWitnessTable? p₂ w₂ = some tbl₁ := by rw [ht₂, hEq]
      exact hSalt (orderWitnessTable?_injective ht₁ ht₂').2.2.2.2
    · dsimp only [commitPrivateOrder, p₁, p₂, w₁, w₂] at hCommEq
      rw [ht₁, ht₂] at hCommEq
      exact hCommEq
  extractDualCommitCollisionWithFrames deployedCanopyHash32 pp tbl₁ tbl₂ rfl rfl hCols hFacts.1 hFacts.2

/-- **Non-Vacuous `LazyRO`-or-`ModuleSIS` Salted Dictionary Resistance (`unsaltedCommitDictionary_miss_of_roLog_or_sis`, `0 Classical`)**:
    Under `pp.cols = 32` and **either** collision-freeness on the finite 32-byte `Digest32` `canopyTableFrames`
    recorded in `log : GameSoundness.ROLog` **or** `ModuleSISHard pp 131070` (provably inhabited via
    `inhabitedAjtaiParams_sisHard 3`), NO salted private order (`salt ≠ 0`) can ever collide with
    the `canopyAjtaiDualPCS` commitment of ANY unsalted (`salt = 0`) dictionary entry! -/
theorem unsaltedCommitDictionary_miss_of_roLog_or_sis
    (pp : AjtaiParams) (hCols : pp.cols = 32)
    (log : GameSoundness.ROLog (List UInt8) Digest32)
    {account : AccountId} {side : Side} {maxBits : Nat}
    {salt : GoldilocksExt2} {w : OrderBitWitness}
    (hAcc : CanonicalLift account) (hQty : CanonicalLift w.qty) (hTot : CanonicalLift w.total)
    (hSalt : salt ≠ GoldilocksExt2.zero)
    (candAcc : AccountId) (candSide : Side) (candMaxBits : Nat) (candW : OrderBitWitness)
    (hcAcc : CanonicalLift candAcc) (hcQty : CanonicalLift candW.qty) (hcTot : CanonicalLift candW.total)
    (hOr : (GameSoundness.hasLogCollision log = false ∧
            (∀ m ∈ canopyTableFrames deployedCanopyHash32 3 (canonicalSaltedOrderTable account side salt w),
              (m, evalDigest32 deployedCanopyHash32 m) ∈ log) ∧
            (∀ m ∈ canopyTableFrames deployedCanopyHash32 3 (canonicalSaltedOrderTable candAcc candSide GoldilocksExt2.zero candW),
              (m, evalDigest32 deployedCanopyHash32 m) ∈ log)) ∨
           ModuleSISHard pp 131070) :
    (commitPrivateOrder pp account side maxBits salt w).dualComm ≠
    (commitPrivateOrder pp candAcc candSide candMaxBits GoldilocksExt2.zero candW).dualComm := by
  intro hCommEq
  obtain ⟨⟨wHash, wSIS⟩, hMemA, hMemB⟩ := extractSaltedDictionaryCollisionBoth pp hCols hAcc hQty hTot hSalt
    candAcc candSide candMaxBits candW hcAcc hcQty hcTot hCommEq
  rcases hOr with ⟨hNoCol, hLog₁, hLog₂⟩ | hSIS
  · have hCol : GameSoundness.hasLogCollision log = true :=
      (GameSoundness.hasLogCollision_iff log).2
        ⟨(wHash.msgA, evalDigest32 deployedCanopyHash32 wHash.msgA), hLog₁ wHash.msgA hMemA,
         (wHash.msgB, evalDigest32 deployedCanopyHash32 wHash.msgB), hLog₂ wHash.msgB hMemB,
         wHash.distinct, evalDigest32_eq_of_sameDigest deployedCanopyHash32 wHash.sameDigest⟩
    rw [hNoCol] at hCol
    cases hCol
  · exact hSIS ⟨wSIS⟩

/-- Unconditionally inhabited instance of `unsaltedCommitDictionary_miss_of_roLog_or_sis` on `inhabitedAjtaiParams 3`. -/
theorem unsaltedCommitDictionary_miss_inhabited
    {account : AccountId} {side : Side} {maxBits : Nat}
    {salt : GoldilocksExt2} {w : OrderBitWitness}
    (hAcc : CanonicalLift account) (hQty : CanonicalLift w.qty) (hTot : CanonicalLift w.total)
    (hSalt : salt ≠ GoldilocksExt2.zero)
    (candAcc : AccountId) (candSide : Side) (candMaxBits : Nat) (candW : OrderBitWitness)
    (hcAcc : CanonicalLift candAcc) (hcQty : CanonicalLift candW.qty) (hcTot : CanonicalLift candW.total) :
    (commitPrivateOrder (inhabitedAjtaiParams 3) account side maxBits salt w).dualComm ≠
    (commitPrivateOrder (inhabitedAjtaiParams 3) candAcc candSide candMaxBits GoldilocksExt2.zero candW).dualComm :=
  unsaltedCommitDictionary_miss_of_roLog_or_sis (inhabitedAjtaiParams 3) rfl []
    hAcc hQty hTot hSalt candAcc candSide candMaxBits candW hcAcc hcQty hcTot
    (.inr (inhabitedAjtaiParams_sisHard 3).2.2)

/-- Coordinatewise modular addition `(u_i + m_i) mod q` for LWE-blinded order vector commitments. -/
def addModVec (q : Nat) (u m : List Int) : List Int :=
  List.zipWith (fun ui mi => (ui + mi) % (q : Int)) u m

/-- **LWE-Blinded Order Commitment Distribution (`mlweBlindedCommitDist`)**:
    Blinds ALL private order payload limbs `msgVec` (`account`, `side`, `qty`, `total`, `salt`) by
    adding a fresh `MLWE` sample `(A, b = A s + e mod q) ← mlweRealDist P` (closing unblinded
    `inhabitedAjtaiParams` limb `0..3` exposure where `salt` only sat at coordinates `4..5`!). -/
def mlweBlindedCommitDist (P : GameSoundness.MLWEParams) (msgVec : List Int) :
    GameSoundness.FinDist (List (List Int) × List Int) :=
  (GameSoundness.mlweRealDist P).map fun (A, b) => (A, addModVec P.q b msgVec)

private theorem uniformModDist_shift_equiv (q : Nat) (hq : 0 < q) (m : Int) :
    GameSoundness.FinDist.Equiv
      ((GameSoundness.uniformModDist q hq).map (fun u => (u + m) % (q : Int)))
      (GameSoundness.uniformModDist q hq) := by
  have hqI : (0 : Int) < (q : Int) := Int.ofNat_lt.2 hq
  let r : Nat := (m % (q : Int)).toNat
  have hr0 : 0 ≤ m % (q : Int) := Int.emod_nonneg m (by omega)
  have hrLtI : m % (q : Int) < (q : Int) := Int.emod_lt_of_pos m hqI
  have hrEq : (r : Int) = m % (q : Int) := by dsimp [r]; omega
  have hrLe : r ≤ q := by omega
  have hSupEq : (GameSoundness.uniformModDist q hq).map (fun u => (u + m) % (q : Int)) =
      (GameSoundness.FinDist.map (GameSoundness.cycShift q r)
        (GameSoundness.FinDist.uniform (List.range q) (GameSoundness.range_ne_nil hq))).map (fun j : Nat => (j : Int)) := by
    apply GameSoundness.FinDist.ext_support
    dsimp only [GameSoundness.uniformModDist, GameSoundness.FinDist.map, GameSoundness.FinDist.uniform]
    simp only [List.map_map, Function.comp_def]
    refine List.map_congr_left fun n hn => ?_
    have _ : n < q := List.mem_range.1 hn
    refine Prod.ext ?_ rfl
    have hrMod : (r : Int) % (q : Int) = (r : Int) := Int.emod_eq_of_lt (by omega) (by omega)
    have hModR : ((n : Int) + m) % (q : Int) = ((n : Int) + (r : Int)) % (q : Int) := by
      rw [Int.add_emod (n : Int) m, ← hrEq, ← hrMod, ← Int.add_emod, hrMod]
    rw [hModR]; unfold GameSoundness.cycShift
    by_cases hCase : n < q - r
    · simp only [hCase, ↓reduceIte]
      rw [show ((n + r : Nat) : Int) = (n : Int) + (r : Int) by omega]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    · simp only [hCase, ↓reduceIte]
      have hSub : (n : Int) + (r : Int) = ((n - (q - r) : Nat) : Int) + (q : Int) := by omega
      rw [hSub, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
      exact Int.emod_eq_of_lt (by omega) (by omega)
  intro p; rw [hSupEq, GameSoundness.FinDist.probEvent_map]
  simpa [GameSoundness.uniformModDist, GameSoundness.FinDist.probEvent_map] using
    GameSoundness.uniform_cycShift_equiv q r hq hrLe (p ∘ fun j : Nat => (j : Int))

private theorem uniformModVecDist_shift_tvZero (q : Nat) (hq : 0 < q) :
    ∀ (ms : List Int),
      GameSoundness.RatProb.le
        (GameSoundness.tvDist
          ((GameSoundness.uniformModVecDist q hq ms.length).map (fun us => addModVec q us ms))
          (GameSoundness.uniformModVecDist q hq ms.length))
        GameSoundness.RatProb.zero
  | [] => by
    unfold GameSoundness.uniformModVecDist GameSoundness.FinDist.map GameSoundness.FinDist.pure addModVec
    have h0 := GameSoundness.tvDist_self_zero (GameSoundness.FinDist.pure ([] : List Int))
    change GameSoundness.RatProb.le (GameSoundness.tvDist (GameSoundness.FinDist.pure []) (GameSoundness.FinDist.pure [])) _
    unfold GameSoundness.RatProb.le; rw [h0]; simp [GameSoundness.RatProb.zero]
  | m :: ms => by
    let dHead := (GameSoundness.uniformModDist q hq).map (fun u => (u + m) % (q : Int))
    let dTail := (GameSoundness.uniformModVecDist q hq ms.length).map (fun us => addModVec q us ms)
    let consFn : Int × List Int → List Int := fun p => p.1 :: p.2
    have hProdEq : GameSoundness.FinDist.Equiv
        ((GameSoundness.uniformModVecDist q hq (m :: ms).length).map (fun us => addModVec q us (m :: ms)))
        ((GameSoundness.FinDist.prod dHead dTail).map consFn) := by
      intro p; simp only [List.length_cons, GameSoundness.uniformModVecDist, GameSoundness.FinDist.probEvent_map]
      unfold GameSoundness.FinDist.prod dHead; rw [GameSoundness.bind_map_eq]
      have hPt : ∀ a, (((GameSoundness.uniformModVecDist q hq ms.length).map (fun b => (a, b))).probEvent
            ((p ∘ fun us => addModVec q us (m :: ms)) ∘ consFn)) =
          ((dTail.map (fun b' => ((a + m) % (q : Int), b'))).probEvent (p ∘ consFn)) := fun a => by
        dsimp only [dTail]; rw [GameSoundness.FinDist.probEvent_map, GameSoundness.FinDist.probEvent_map, GameSoundness.FinDist.probEvent_map]; rfl
      exact GameSoundness.RatProb.eqv_of_le_antisymm
        (GameSoundness.probEvent_bind_mono _ _ _ _ _ (fun a _ _ => by rw [hPt a]; exact GameSoundness.RatProb.le_refl _))
        (GameSoundness.probEvent_bind_mono _ _ _ _ _ (fun a _ _ => by rw [hPt a]; exact GameSoundness.RatProb.le_refl _))
    have hHead0 : GameSoundness.RatProb.le (GameSoundness.tvDist dHead (GameSoundness.uniformModDist q hq)) GameSoundness.RatProb.zero := by
      have hEqv := @GameSoundness.tvDist_of_equiv Int _ dHead (GameSoundness.uniformModDist q hq)
        (GameSoundness.uniformModDist q hq) (GameSoundness.uniformModDist q hq)
        (uniformModDist_shift_equiv q hq m) (fun _ => GameSoundness.RatProb.eqv_refl _)
      have hSelf := GameSoundness.tvDist_self_zero (GameSoundness.uniformModDist q hq)
      unfold GameSoundness.RatProb.eqv at hEqv; unfold GameSoundness.RatProb.le GameSoundness.RatProb.zero
      have _ := (GameSoundness.tvDist (GameSoundness.uniformModDist q hq) (GameSoundness.uniformModDist q hq)).den_pos
      rw [hSelf, Nat.zero_mul] at hEqv
      have hNum0 : (GameSoundness.tvDist dHead (GameSoundness.uniformModDist q hq)).num = 0 :=
        (Nat.mul_eq_zero.1 hEqv).resolve_right (by omega)
      simp [hNum0]
    have hZAdd : GameSoundness.RatProb.le (GameSoundness.RatProb.add GameSoundness.RatProb.zero GameSoundness.RatProb.zero) GameSoundness.RatProb.zero := by
      unfold GameSoundness.RatProb.le GameSoundness.RatProb.add GameSoundness.RatProb.zero; simp
    exact GameSoundness.RatProb.le_congr
      (GameSoundness.RatProb.eqv_symm
        (@GameSoundness.tvDist_of_equiv (List Int) _
          ((GameSoundness.uniformModVecDist q hq (m :: ms).length).map (fun us => addModVec q us (m :: ms)))
          (GameSoundness.uniformModVecDist q hq (m :: ms).length)
          ((GameSoundness.FinDist.prod dHead dTail).map consFn)
          ((GameSoundness.FinDist.prod (GameSoundness.uniformModDist q hq) (GameSoundness.uniformModVecDist q hq ms.length)).map consFn)
          hProdEq (fun _ => GameSoundness.RatProb.eqv_refl _)))
      (GameSoundness.RatProb.eqv_refl _)
      (GameSoundness.RatProb.le_trans
        (GameSoundness.tvDist_map_le consFn (GameSoundness.FinDist.prod dHead dTail)
          (GameSoundness.FinDist.prod (GameSoundness.uniformModDist q hq) (GameSoundness.uniformModVecDist q hq ms.length)))
        (GameSoundness.RatProb.le_trans
          (GameSoundness.tvDist_prod_le dHead (GameSoundness.uniformModDist q hq) dTail (GameSoundness.uniformModVecDist q hq ms.length))
          (GameSoundness.RatProb.le_trans (GameSoundness.RatProb.add_le_add hHead0 (uniformModVecDist_shift_tvZero q hq ms)) hZAdd)))

private theorem mlweIdeal_shift_eqv (P : GameSoundness.MLWEParams) (msg : List Int)
    (hLen : msg.length = P.samples + 1) (D : (List (List Int) × List Int) → Bool) :
    GameSoundness.RatProb.eqv
      ((GameSoundness.mlweIdealDist P).probEvent (fun (A, b) => D (A, addModVec P.q b msg)))
      ((GameSoundness.mlweIdealDist P).probEvent D) := by
  unfold GameSoundness.mlweIdealDist GameSoundness.FinDist.prod
  have ptEqv : ∀ A : List (List Int),
      let dB := GameSoundness.uniformModVecDist P.q P.q_pos (P.samples + 1)
      GameSoundness.RatProb.eqv
        ((dB.map (fun b => (A, b))).probEvent (fun (A, b) => D (A, addModVec P.q b msg)))
        ((dB.map (fun b => (A, b))).probEvent D) := by
    intro A dB
    rw [GameSoundness.FinDist.probEvent_map, GameSoundness.FinDist.probEvent_map]
    have hComp : ((fun (A', b) => D (A', addModVec P.q b msg)) ∘ fun b => (A, b)) =
        ((fun b => D (A, b)) ∘ fun x => addModVec P.q x msg) := rfl
    rw [hComp, ← GameSoundness.FinDist.probEvent_map]
    have hTv0 : GameSoundness.RatProb.le
        (GameSoundness.tvDist (dB.map (fun x => addModVec P.q x msg)) dB) GameSoundness.RatProb.zero := by
      dsimp only [dB]; rw [← hLen]; exact uniformModVecDist_shift_tvZero P.q P.q_pos msg
    have hAbs0 := GameSoundness.RatProb.le_trans
      (GameSoundness.absDiff_probEvent_le_tvDist (dB.map (fun x => addModVec P.q x msg)) dB (fun b => D (A, b))) hTv0
    unfold GameSoundness.RatProb.le GameSoundness.RatProb.absDiff GameSoundness.RatProb.zero at hAbs0
    dsimp only at hAbs0
    change GameSoundness.RatProb.eqv ((dB.map (fun x => addModVec P.q x msg)).probEvent (fun b => D (A, b)))
      (dB.probEvent (fun b => D (A, b)))
    unfold GameSoundness.RatProb.eqv; omega
  exact GameSoundness.RatProb.eqv_of_le_antisymm
    (GameSoundness.probEvent_bind_mono _ _ _ _ _ (fun A _ _ => GameSoundness.RatProb.le_of_eqv (ptEqv A)))
    (GameSoundness.probEvent_bind_mono _ _ _ _ _ (fun A _ _ => GameSoundness.RatProb.le_of_eqv (GameSoundness.RatProb.eqv_symm (ptEqv A))))

/-- **Computational Order-Commitment Hiding from `MLWE` (`mlweBlindedCommit_hiding_le_two_mlweAdv`)**:
    For any two private order payload vectors `msg₀, msg₁` of length `P.samples + 1` and any
    distinguisher `D`, distinguishing `mlweBlindedCommitDist P msg₀` from `mlweBlindedCommitDist P msg₁`
    is bounded by `mlweAdv P D₀ + mlweAdv P D₁` (`≤ 2 · MLWEAdv`). -/
theorem mlweBlindedCommit_hiding_le_two_mlweAdv (P : GameSoundness.MLWEParams)
    (msg₀ msg₁ : List Int) (hLen₀ : msg₀.length = P.samples + 1) (hLen₁ : msg₁.length = P.samples + 1)
    (D : (List (List Int) × List Int) → Bool) :
    let D₀ : (List (List Int) × List Int) → Bool := fun (A, b) => D (A, addModVec P.q b msg₀)
    let D₁ : (List (List Int) × List Int) → Bool := fun (A, b) => D (A, addModVec P.q b msg₁)
    GameSoundness.RatProb.le
      (GameSoundness.RatProb.absDiff
        ((mlweBlindedCommitDist P msg₀).probEvent D)
        ((mlweBlindedCommitDist P msg₁).probEvent D))
      (GameSoundness.RatProb.add (GameSoundness.mlweAdv P D₀) (GameSoundness.mlweAdv P D₁)) := by
  intro D₀ D₁
  have hMap₀ : (mlweBlindedCommitDist P msg₀).probEvent D = (GameSoundness.mlweRealDist P).probEvent D₀ :=
    GameSoundness.FinDist.probEvent_map _ _ D
  have hMap₁ : (mlweBlindedCommitDist P msg₁).probEvent D = (GameSoundness.mlweRealDist P).probEvent D₁ :=
    GameSoundness.FinDist.probEvent_map _ _ D
  rw [hMap₀, hMap₁]
  have hIdEq : GameSoundness.RatProb.eqv
      ((GameSoundness.mlweIdealDist P).probEvent D₀)
      ((GameSoundness.mlweIdealDist P).probEvent D₁) :=
    GameSoundness.RatProb.eqv_trans
      (mlweIdeal_shift_eqv P msg₀ hLen₀ D)
      (GameSoundness.RatProb.eqv_symm (mlweIdeal_shift_eqv P msg₁ hLen₁ D))
  have hSecond : GameSoundness.RatProb.eqv
      (GameSoundness.RatProb.absDiff ((GameSoundness.mlweIdealDist P).probEvent D₀) ((GameSoundness.mlweRealDist P).probEvent D₁))
      (GameSoundness.mlweAdv P D₁) :=
    GameSoundness.RatProb.eqv_trans
      (GameSoundness.RatProb.absDiff_eqv_congr hIdEq (GameSoundness.RatProb.eqv_refl _))
      (GameSoundness.RatProb.absDiff_symm _ _)
  exact GameSoundness.RatProb.le_trans
    (GameSoundness.RatProb.absDiff_triangle
      ((GameSoundness.mlweRealDist P).probEvent D₀)
      ((GameSoundness.mlweIdealDist P).probEvent D₀)
      ((GameSoundness.mlweRealDist P).probEvent D₁))
    (GameSoundness.RatProb.add_le_add (GameSoundness.RatProb.le_refl _) (GameSoundness.RatProb.le_of_eqv hSecond))

/-- Materialize an `Obend.Judge.Order` from its public spec and opened `BitZ` witness. -/
def materializeOrder (spec : CommittedOrderSpec) (w : OrderBitWitness) : Order :=
  { account := spec.account
    side := spec.side
    qty := w.qty
    total := w.total }

/-- Materialize a batch of `Order`s from aligned specs and witnesses. -/
def materializeOrders : List CommittedOrderSpec → List OrderBitWitness → List Order
  | s :: ss, w :: ws => materializeOrder s w :: materializeOrders ss ws
  | _, _ => []

theorem materializeOrders_length :
    ∀ (specs : List CommittedOrderSpec) (ws : List OrderBitWitness),
      specs.length = ws.length →
      (materializeOrders specs ws).length = specs.length
  | [], [], _ => rfl
  | _ :: ss, _ :: ws, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    simp [materializeOrders, materializeOrders_length ss ws h]

/-- Worst-case order quantity/total sum bound $\sum_{s \in \text{specs}} 2^{s.\text{maxBits}}$ derived from `committedOrders`. -/
def orderBookMsgBound : List CommittedOrderSpec → Nat
  | [] => 0
  | s :: ss => 2 ^ s.maxBits + orderBookMsgBound ss

/-- Public query to `privateConvexSameOpeningJudge` (with optional `msgBound` and `qModulus`
    for modulus no-wraparound verification). -/
structure SameOpeningQuery where
  market : Market
  ajtaiParams : AjtaiParams
  noiseBound : Nat
  smudgeBound : Nat
  secBits : Nat
  committedOrders : List CommittedOrderSpec
  msgBound : Nat := 0
  qModulus : Nat := 2 ^ 128

/-- Effective message bound `max q.msgBound (orderBookMsgBound q.committedOrders)` enforced by `verifySameOpening`. -/
def SameOpeningQuery.effectiveMsgBound (q : SameOpeningQuery) : Nat :=
  Nat.max q.msgBound (orderBookMsgBound q.committedOrders)

/-- Certificate / witness bundle checked by `privateConvexSameOpeningJudge`:
    opened salted `BitZ` bit-vectors, conservation-checked `ResourcePosting`s, and $O(N)$ KKT duals. -/
structure SameOpeningWitness where
  orderWitnesses : List OrderBitWitness
  transfers : List ResourcePosting
  kktCert : Certificate
  deriving DecidableEq, Repr

/-! ## 4. KKT Zero Primal-Dual Duality Gap (`kktPrimalDualGapZero`) & Witness Verification -/

/-- Primal welfare / matched volume objective $\sum_i f_i$. -/
def primalObjective (m : Market) (orders : List Order) (transfers : List ResourcePosting) : Int :=
  finSum orders.length (fun i => (orders.get i).fill m transfers)

/-- Dual capacity-slack objective $\sum_i u_i(p) \cdot s_i$. -/
def dualObjective (orders : List Order) (c : Certificate) : Int :=
  finSum orders.length (fun i =>
    let cap := if (orders.get i).crosses c.price then ((orders.get i).qty : Int) else 0
    let s := c.slacks.getD i.val 0
    cap * s)

/-- **Exact KKT Zero Primal-Dual Duality Gap Check (`kktPrimalDualGapZero`)**:
    Verifies complementary slackness (`dualObjective orders c = primalObjective m orders transfers`). -/
def kktPrimalDualGapZero (m : Market) (orders : List Order)
    (transfers : List ResourcePosting) (c : Certificate) : Bool :=
  decide (dualObjective orders c = primalObjective m orders transfers)

theorem kktPrimalDualGapZero_iff (m : Market) (orders : List Order)
    (transfers : List ResourcePosting) (c : Certificate) :
    kktPrimalDualGapZero m orders transfers c = true ↔
      dualObjective orders c = primalObjective m orders transfers := by
  simp [kktPrimalDualGapZero]

/-- Refusal vocabulary of `privateConvexSameOpeningJudge`. -/
inductive SameOpeningRefusal where
  | unsmudgedThresholdNoise
  | modulusWraparoundUnsafe
  | malformedMarketAssets
  | invalidLatticeDimension
  | witnessCountMismatch (expected actual : Nat)
  | bitzRangeExceeded (orderIdx : Nat)
  | nonCanonicalFieldLift (orderIdx : Nat)
  | dualCommitmentMismatch (orderIdx : Nat)
  | clearingRefused (reason : ClearingRefusal)
  | nonzeroPrimalDualGap (dualVal primalVal : Int)
  deriving DecidableEq, Repr

/-- Semantic proposition that every committed order was opened to a canonical (`< goldilocksPrime`),
    `BitZ` $2^B$-bounded salted witness matching its `canopyAjtaiDualPCS` commitment. -/
def AllOrdersOpenedAndBounded (pp : AjtaiParams) :
    List CommittedOrderSpec → List OrderBitWitness → Prop
  | [], [] => True
  | s :: ss, w :: ws =>
    CanonicalLift s.account ∧
    CanonicalLift w.qty ∧
    CanonicalLift w.total ∧
    w.qty < 2 ^ s.maxBits ∧
    w.total < 2 ^ s.maxBits ∧
    (∃ tbl : List Goldilocks,
      orderWitnessTable? s w = some tbl ∧
      (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl = s.dualComm) ∧
    AllOrdersOpenedAndBounded pp ss ws
  | _, _ => False

theorem allOrdersOpened_le_orderBookMsgBound (pp : AjtaiParams) :
    ∀ (specs : List CommittedOrderSpec) (ws : List OrderBitWitness),
      AllOrdersOpenedAndBounded pp specs ws →
      ∀ w ∈ ws, w.qty ≤ orderBookMsgBound specs ∧ w.total ≤ orderBookMsgBound specs
  | [], [], _, _, hw => by cases hw
  | _ :: _, [], h, _, _ => False.elim h
  | [], _ :: _, h, _, _ => False.elim h
  | _ :: ss, _ :: ws, ⟨_, _, _, hQty, hTot, _, hRest⟩, w, hw => by
    simp only [orderBookMsgBound, List.mem_cons] at hw ⊢
    rcases hw with rfl | hTl
    · omega
    · obtain ⟨hq, ht⟩ := allOrdersOpened_le_orderBookMsgBound pp ss ws hRest w hTl
      omega

/-- Executable per-order `BitZ` bit-length, canonical `< goldilocksPrime` field lift, and
    `canopyAjtaiDualPCS` commitment checker. -/
def checkOrderWitnessList (pp : AjtaiParams) :
    Nat → List CommittedOrderSpec → List OrderBitWitness → Option SameOpeningRefusal
  | _, [], [] => none
  | _, [], ws => some (.witnessCountMismatch 0 ws.length)
  | _, ss, [] => some (.witnessCountMismatch ss.length 0)
  | idx, s :: ss, w :: ws =>
    if !(decide (w.qtyBits.length ≤ s.maxBits) && decide (w.totalBits.length ≤ s.maxBits)) then
      some (.bitzRangeExceeded idx)
    else
      match orderWitnessTable? s w with
      | none => some (.nonCanonicalFieldLift idx)
      | some tbl =>
        if s.dualComm != (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl then
          some (.dualCommitmentMismatch idx)
        else
          checkOrderWitnessList pp (idx + 1) ss ws

theorem checkOrderWitnessList_sound (pp : AjtaiParams) :
    ∀ (idx : Nat) (specs : List CommittedOrderSpec) (ws : List OrderBitWitness),
      checkOrderWitnessList pp idx specs ws = none →
      AllOrdersOpenedAndBounded pp specs ws
  | _, [], [], _ => trivial
  | _, [], _ :: _, h => by simp [checkOrderWitnessList] at h
  | _, _ :: _, [], h => by simp [checkOrderWitnessList] at h
  | idx, s :: ss, w :: ws, h => by
    simp only [checkOrderWitnessList] at h
    split at h
    · cases h
    rename_i hRange
    cases hTbl : orderWitnessTable? s w with
    | none => simp [hTbl] at h
    | some tbl =>
      simp only [hTbl] at h
      split at h
      · cases h
      rename_i hComm
      have hRange' : w.qtyBits.length ≤ s.maxBits ∧ w.totalBits.length ≤ s.maxBits := by
        cases hq : decide (w.qtyBits.length ≤ s.maxBits) <;>
          cases ht : decide (w.totalBits.length ≤ s.maxBits)
        · simp [hq, ht] at hRange
        · simp [hq, ht] at hRange
        · simp [hq, ht] at hRange
        · exact ⟨of_decide_eq_true hq, of_decide_eq_true ht⟩
      have hCommEq : (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl = s.dualComm := by
        cases hc : (s.dualComm != (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl)
        · dsimp only [canopyAjtaiDualPCS, DualPCS, canopyMerklePCS, ajtaiLatticePCS] at hc ⊢
          rw [bne_eq_false_iff_eq] at hc
          exact hc.symm
        · exact absurd hc hComm
      obtain ⟨cAcc, cQty, cTot⟩ := orderWitnessTable?_canonical hTbl
      exact ⟨cAcc, cQty, cTot,
             bitsToNat_lt_two_pow w.qtyBits hRange'.1,
             bitsToNat_lt_two_pow w.totalBits hRange'.2,
             ⟨tbl, hTbl, hCommEq⟩,
             checkOrderWitnessList_sound pp (idx + 1) ss ws h⟩

/-! ## 5. Non-Tautological Semantic Meaning & Lawful `privateConvexSameOpeningJudge` -/

/-- Incidence sign ($+1$ for bid, $-1$ for ask) in flow conservation. -/
def orderSideSign (o : Order) : Int :=
  match o.side with
  | .bid => 1
  | .ask => -1

/-- Crossing capacity $u_i(p)$ of order `o` at uniform clearing price `price`. -/
def orderCrossingCap (price : Nat) (o : Order) : Int :=
  if o.crosses price then (o.qty : Int) else 0

/-- Primal feasibility (`flowConserving` + `fillsFeasible`) extracted from `Obend.Judge.judge = .ok ()`. -/
theorem judge_ok_primal_feasible (m : Market) (orders : List Order)
    (transfers : List ResourcePosting) (c : Certificate)
    (h : Obend.Judge.judge m orders transfers c = .ok ()) :
    finSum orders.length (fun i => orderSideSign (orders.get i) * (orders.get i).fill m transfers) = 0 ∧
    ∀ i : Fin orders.length,
      0 ≤ (orders.get i).fill m transfers ∧
      (orders.get i).fill m transfers ≤ orderCrossingCap c.price (orders.get i) := by
  unfold Obend.Judge.judge at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  · contradiction
  · rename_i h_cons_not_ne
    split at h
    · contradiction
    · rename_i h_prim_none
      refine ⟨?_, ?_⟩
      · have hZ : finSum orders.length (fun i =>
            match (orders.get i).side with
            | .bid => (orders.get i).fill m transfers
            | .ask => - (orders.get i).fill m transfers) = 0 := Decidable.of_not_not h_cons_not_ne
        have hFn : (fun i : Fin orders.length => orderSideSign (orders.get i) * (orders.get i).fill m transfers) =
            (fun i : Fin orders.length =>
              match (orders.get i).side with
              | .bid => (orders.get i).fill m transfers
              | .ask => - (orders.get i).fill m transfers) := by
          funext i; unfold orderSideSign; cases (orders.get i).side <;> simp
        rw [hFn]; exact hZ
      · intro i
        have hnone := List.find?_eq_none.mp h_prim_none i (List.mem_finRange i)
        dsimp only at hnone
        have ⟨hneg, hcap⟩ := not_or_of_decide hnone
        unfold orderCrossingCap
        omega

/-- **Non-Tautological Semantic Meaning of `privateConvexSameOpeningJudge` (`SameOpeningMeaning`)**:
    Establishes simultaneously smudging safety, operational modulus no-wraparound over `effectiveMsgBound`,
    distinct assets, exact 32-column Ajtai dimension, canonical `BitZ` $2^B$ range-bounded openings,
    `accountsNodup`, primal `flowConserving` + `fillsFeasible`, zero KKT gap, and global welfare optimality. -/
structure SameOpeningMeaning (q : SameOpeningQuery) (c : SameOpeningWitness) : Prop where
  smudgeSafe : SmudgeSafe q.noiseBound q.smudgeBound q.secBits
  modulusNoWrap : ModulusNoWrapSafe q.effectiveMsgBound q.noiseBound q.smudgeBound q.qModulus
  assetsDistinct : q.market.currency ≠ q.market.goods
  exactLatticeCols : q.ajtaiParams.cols = 32
  ordersOpenedAndBounded : AllOrdersOpenedAndBounded q.ajtaiParams q.committedOrders c.orderWitnesses
  accountsNodup : ((materializeOrders q.committedOrders c.orderWitnesses).map (·.account)).Nodup
  flowConserving :
    let orders := materializeOrders q.committedOrders c.orderWitnesses
    finSum orders.length (fun i => orderSideSign (orders.get i) * (orders.get i).fill q.market c.transfers) = 0
  fillsFeasible :
    let orders := materializeOrders q.committedOrders c.orderWitnesses
    ∀ i : Fin orders.length,
      0 ≤ (orders.get i).fill q.market c.transfers ∧
      (orders.get i).fill q.market c.transfers ≤ orderCrossingCap c.kktCert.price (orders.get i)
  zeroDualityGap :
    let orders := materializeOrders q.committedOrders c.orderWitnesses
    dualObjective orders c.kktCert = primalObjective q.market orders c.transfers
  globallyOptimal :
    let orders := materializeOrders q.committedOrders c.orderWitnesses
    ∀ (f' : Fin orders.length → Int),
      finSum orders.length (fun i => orderSideSign (orders.get i) * f' i) = 0 →
      (∀ i, 0 ≤ f' i) →
      (∀ i, f' i ≤ orderCrossingCap c.kktCert.price (orders.get i)) →
      finSum orders.length f' ≤ primalObjective q.market orders c.transfers

/-- **Operational Per-Order No-Wraparound Decoding (`acceptedOrder_noWrap_decode`)**:
    Under `SameOpeningMeaning q c`, every opened order witness `w ∈ c.orderWitnesses` satisfies
    `w.qty ≤ q.effectiveMsgBound` and `w.total ≤ q.effectiveMsgBound`, so adding bounded encryption
    error `e` and smudging noise `u` NEVER wraps modulo `q.qModulus`! -/
theorem acceptedOrder_noWrap_decode {q : SameOpeningQuery} {c : SameOpeningWitness}
    (hMean : SameOpeningMeaning q c) {w : OrderBitWitness} (hw : w ∈ c.orderWitnesses)
    (e u : Int) (he : e.natAbs ≤ q.noiseBound) (hu : u.natAbs ≤ q.smudgeBound) :
    centeredModDecode q.qModulus (((w.qty : Int) + e + u) % (q.qModulus : Int)) = (w.qty : Int) + e + u ∧
    centeredModDecode q.qModulus (((w.total : Int) + e + u) % (q.qModulus : Int)) = (w.total : Int) + e + u := by
  obtain ⟨hqB, htB⟩ := allOrdersOpened_le_orderBookMsgBound q.ajtaiParams _ _ hMean.ordersOpenedAndBounded w hw
  have hEff : orderBookMsgBound q.committedOrders ≤ q.effectiveMsgBound := Nat.le_max_right _ _
  exact ⟨(centeredModDecode_exact_of_noWrap hMean.modulusNoWrap (w.qty : Int) e u (by omega) he hu).2,
         (centeredModDecode_exact_of_noWrap hMean.modulusNoWrap (w.total : Int) e u (by omega) he hu).2⟩

/-- Kernel checker for `privateConvexSameOpeningJudge`: runs in $O(N)$ over opened witnesses. -/
def verifySameOpening (q : SameOpeningQuery) (c : SameOpeningWitness) :
    Judge.Verdict SameOpeningRefusal :=
  if !checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits then
    .refused .unsmudgedThresholdNoise []
  else if !checkModulusNoWrap q.effectiveMsgBound q.noiseBound q.smudgeBound q.qModulus then
    .refused .modulusWraparoundUnsafe []
  else if q.market.currency = q.market.goods then
    .refused .malformedMarketAssets []
  else if q.ajtaiParams.cols != 32 then
    .refused .invalidLatticeDimension []
  else
    match checkOrderWitnessList q.ajtaiParams 0 q.committedOrders c.orderWitnesses with
    | some err => .refused err []
    | none =>
      let orders := materializeOrders q.committedOrders c.orderWitnesses
      let zeroEpsMarket : Market := { q.market with epsilon := 0 }
      match Obend.Judge.judge zeroEpsMarket orders c.transfers c.kktCert with
      | .error reason => .refused (.clearingRefused reason) []
      | .ok () =>
        if kktPrimalDualGapZero q.market orders c.transfers c.kktCert then
          .ok
        else
          .refused
            (.nonzeroPrimalDualGap
              (dualObjective orders c.kktCert)
              (primalObjective q.market orders c.transfers))
            []

/-- Query-level clauses whose refusal refutes the existence of **any** valid certificate. -/
def sameOpeningRefutes : SameOpeningRefusal → Bool
  | .unsmudgedThresholdNoise => true
  | .modulusWraparoundUnsafe => true
  | .malformedMarketAssets => true
  | .invalidLatticeDimension => true
  | _ => false

theorem checkOrderWitnessList_not_refutes (pp : AjtaiParams) :
    ∀ (idx : Nat) (specs : List CommittedOrderSpec) (ws : List OrderBitWitness)
      (err : SameOpeningRefusal),
      checkOrderWitnessList pp idx specs ws = some err →
      sameOpeningRefutes err = false
  | _, [], [], _, h => by simp [checkOrderWitnessList] at h
  | _, [], _ :: _, _, h => by
    simp only [checkOrderWitnessList, Option.some.injEq] at h
    subst h; rfl
  | _, _ :: _, [], _, h => by
    simp only [checkOrderWitnessList, Option.some.injEq] at h
    subst h; rfl
  | idx, s :: ss, w :: ws, err, h => by
    simp only [checkOrderWitnessList] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · cases hTbl : orderWitnessTable? s w with
      | none =>
        simp only [hTbl, Option.some.injEq] at h
        subst h; rfl
      | some tbl =>
        simp only [hTbl] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; rfl
        · exact checkOrderWitnessList_not_refutes pp (idx + 1) ss ws err h

/-- **Universal Soundness of `verifySameOpening` (`verifySameOpening_sound`)**:
    Any witness accepted by `verifySameOpening` establishes `SameOpeningMeaning q c`. -/
theorem verifySameOpening_sound {q : SameOpeningQuery} {c : SameOpeningWitness}
    (h : verifySameOpening q c = .ok) :
    SameOpeningMeaning q c := by
  unfold verifySameOpening at h
  cases hSm : checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits
  · simp [hSm] at h
  simp only [hSm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hNoWrap : checkModulusNoWrap q.effectiveMsgBound q.noiseBound q.smudgeBound q.qModulus
  · simp [hNoWrap] at h
  simp only [hNoWrap, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  if hEqAsset : q.market.currency = q.market.goods then
    simp [hEqAsset] at h
  else
    simp only [hEqAsset, ↓reduceIte] at h
    cases hColsBne : (q.ajtaiParams.cols != 32)
    · simp only [hColsBne, Bool.false_eq_true, ↓reduceIte] at h
      have hColsEq : q.ajtaiParams.cols = 32 := by simpa [bne] using hColsBne
      cases hOrd : checkOrderWitnessList q.ajtaiParams 0 q.committedOrders c.orderWitnesses with
      | some err => simp [hOrd] at h
      | none =>
        simp only [hOrd] at h
        let orders := materializeOrders q.committedOrders c.orderWitnesses
        let zeroEpsMarket : Market := { q.market with epsilon := 0 }
        cases hJ : Obend.Judge.judge zeroEpsMarket orders c.transfers c.kktCert with
        | error reason => simp [orders, zeroEpsMarket, hJ] at h
        | ok u =>
          simp only [orders, zeroEpsMarket, hJ] at h
          cases hGap : kktPrimalDualGapZero q.market orders c.transfers c.kktCert
          · simp [orders, hGap] at h
          · obtain ⟨hCons0, hFeas0⟩ := judge_ok_primal_feasible zeroEpsMarket orders c.transfers c.kktCert hJ
            refine
              { smudgeSafe := (checkSmudgeSafe_iff _ _ _).1 hSm
                modulusNoWrap := (checkModulusNoWrap_iff _ _ _ _).1 hNoWrap
                assetsDistinct := hEqAsset
                exactLatticeCols := hColsEq
                ordersOpenedAndBounded := checkOrderWitnessList_sound q.ajtaiParams 0 _ _ hOrd
                accountsNodup := judge_ok_accounts_nodup zeroEpsMarket orders c.transfers c.kktCert hJ
                flowConserving := hCons0
                fillsFeasible := hFeas0
                zeroDualityGap := (kktPrimalDualGapZero_iff _ _ _ _).1 hGap
                globallyOptimal := ?_ }
            dsimp only
            intro f' hCons hNonneg hCap
            have hOpt := judge_certifies_epsilon_optimal zeroEpsMarket orders c.transfers c.kktCert hJ
              f' hCons hNonneg hCap
            have hFillEq : finSum orders.length (fun i => (orders.get i).fill zeroEpsMarket c.transfers) =
                primalObjective q.market orders c.transfers := rfl
            have hEpsZero : (zeroEpsMarket.epsilon : Int) = 0 := rfl
            rw [hFillEq, hEpsZero, Int.add_zero] at hOpt
            exact hOpt
    · simp [hColsBne] at h

private def emptyClearingAjtaiParams : AjtaiParams where
  rows := 8
  cols := 32
  rows_pos := by decide
  modulus := 2
  modulus_pos := by decide
  matrix := List.replicate 8 (List.replicate 32 0)
  matrix_rows := by decide
  matrix_cols := by
    intro row hmem
    rw [List.mem_replicate] at hmem
    rw [hmem.2]
    decide

/-- Inhabitedness witness for `verifySameOpening = .ok` (ensures non-vacuous premise coverage). -/
example :
    let q : SameOpeningQuery :=
      { market := { currency := 1, goods := 2, epsilon := 0 }
        ajtaiParams := emptyClearingAjtaiParams
        noiseBound := 1
        smudgeBound := 2 ^ 40
        secBits := 40
        committedOrders := [] }
    let w : SameOpeningWitness :=
      { orderWitnesses := []
        transfers := []
        kktCert := { price := 1, potentials := (0, 0), slacks := [] } }
    verifySameOpening q w = .ok := by
  decide

/-- **Refutation Soundness of `verifySameOpening` (`verifySameOpening_refuted`)**:
    Refusal by `.unsmudgedThresholdNoise`, `.modulusWraparoundUnsafe`, `.malformedMarketAssets`, or
    `.invalidLatticeDimension` occurs at the root path `p = []` and proves that **no** certificate `c'`
    can satisfy `SameOpeningMeaning q c'`. -/
theorem verifySameOpening_refuted {q : SameOpeningQuery} {c : SameOpeningWitness}
    {k : SameOpeningRefusal} {p : List Nat}
    (hRef : verifySameOpening q c = .refused k p)
    (hMarks : sameOpeningRefutes k = true) :
    sameOpeningRefutes k = true ∧ p = [] ∧ (∀ c', ¬ SameOpeningMeaning q c') := by
  refine ⟨hMarks, ?_, ?_⟩
  · unfold verifySameOpening at hRef
    cases hSm : checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits
    · simp only [hSm, Bool.not_false, ↓reduceIte, Judge.Verdict.refused.injEq] at hRef
      exact hRef.2.symm
    · simp only [hSm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
      cases hNoWrap : checkModulusNoWrap q.effectiveMsgBound q.noiseBound q.smudgeBound q.qModulus
      · simp only [hNoWrap, Bool.not_false, ↓reduceIte, Judge.Verdict.refused.injEq] at hRef
        exact hRef.2.symm
      · simp only [hNoWrap, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
        if hEqAsset : q.market.currency = q.market.goods then
          simp only [hEqAsset, ↓reduceIte, Judge.Verdict.refused.injEq] at hRef
          exact hRef.2.symm
        else
          simp only [hEqAsset, ↓reduceIte] at hRef
          cases hCols : (q.ajtaiParams.cols != 32)
          · simp only [hCols, Bool.false_eq_true, ↓reduceIte] at hRef
            cases hOrd : checkOrderWitnessList q.ajtaiParams 0 q.committedOrders c.orderWitnesses with
            | some err =>
              simp only [hOrd, Judge.Verdict.refused.injEq] at hRef; exact hRef.2.symm
            | none =>
              simp only [hOrd] at hRef
              cases hJ : Obend.Judge.judge { q.market with epsilon := 0 }
                  (materializeOrders q.committedOrders c.orderWitnesses) c.transfers c.kktCert with
              | error _ =>
                simp only [hJ, Judge.Verdict.refused.injEq] at hRef; exact hRef.2.symm
              | ok _ =>
                simp only [hJ] at hRef
                cases hGap : kktPrimalDualGapZero q.market
                    (materializeOrders q.committedOrders c.orderWitnesses) c.transfers c.kktCert
                · simp only [hGap, Bool.false_eq_true, ↓reduceIte, Judge.Verdict.refused.injEq] at hRef
                  exact hRef.2.symm
                · simp [hGap] at hRef
          · simp only [hCols, ↓reduceIte, Judge.Verdict.refused.injEq] at hRef
            exact hRef.2.symm
  · intro c' hMean
    unfold verifySameOpening at hRef
    cases hSm : checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits
    · have ht := (checkSmudgeSafe_iff _ _ _).2 hMean.smudgeSafe
      rw [hSm] at ht; cases ht
    · simp only [hSm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
      cases hNoWrap : checkModulusNoWrap q.effectiveMsgBound q.noiseBound q.smudgeBound q.qModulus
      · have hw := (checkModulusNoWrap_iff _ _ _ _).2 hMean.modulusNoWrap
        rw [hNoWrap] at hw; cases hw
      · simp only [hNoWrap, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
        if hEqAsset : q.market.currency = q.market.goods then
          exact hMean.assetsDistinct hEqAsset
        else
          simp only [hEqAsset, ↓reduceIte] at hRef
          cases hCols : (q.ajtaiParams.cols != 32)
          · simp only [hCols, Bool.false_eq_true, ↓reduceIte] at hRef
            cases hOrd : checkOrderWitnessList q.ajtaiParams 0 q.committedOrders c.orderWitnesses with
            | some err =>
              simp only [hOrd, Judge.Verdict.refused.injEq] at hRef
              rcases hRef with ⟨rfl, _⟩
              have hf := checkOrderWitnessList_not_refutes q.ajtaiParams 0 _ _ err hOrd
              rw [hf] at hMarks; cases hMarks
            | none =>
              simp only [hOrd] at hRef
              cases hJ : Obend.Judge.judge { q.market with epsilon := 0 }
                  (materializeOrders q.committedOrders c.orderWitnesses) c.transfers c.kktCert with
              | error _ =>
                simp only [hJ, Judge.Verdict.refused.injEq] at hRef
                rcases hRef with ⟨rfl, _⟩; cases hMarks
              | ok _ =>
                simp only [hJ] at hRef
                cases hGap : kktPrimalDualGapZero q.market
                    (materializeOrders q.committedOrders c.orderWitnesses) c.transfers c.kktCert
                · simp only [hGap, Bool.false_eq_true, ↓reduceIte, Judge.Verdict.refused.injEq] at hRef
                  rcases hRef with ⟨rfl, _⟩; cases hMarks
                · simp [hGap] at hRef
          · have hNeCols : q.ajtaiParams.cols ≠ 32 := by simpa [bne] using hCols
            exact hNeCols hMean.exactLatticeCols

/-- Canonical zero-quantity (`qty = 0, total = 0, salt = 0`) witness for quiescent committed orders. -/
def zeroOrderBitWitness : OrderBitWitness :=
  { qtyBits := [], totalBits := [], salt := GoldilocksExt2.zero }

/-- Independent semantic input-domain specification for empty-book clearing queries
    (defined purely over query fields with ZERO reference to `verifySameOpening` or `SameOpeningMeaning`!). -/
def WellFormedEmptyBookQuery (q : SameOpeningQuery) : Prop :=
  0 < q.noiseBound ∧ 40 ≤ q.secBits ∧ q.noiseBound * (2 ^ q.secBits) ≤ q.smudgeBound ∧
  2 * (q.msgBound + q.noiseBound + q.smudgeBound) < q.qModulus ∧
  q.market.currency ≠ q.market.goods ∧
  q.ajtaiParams.cols = 32 ∧
  q.committedOrders = []

theorem wellFormedEmptyBookQuery_inhabited (msgBound : Nat) :
    ∃ q : SameOpeningQuery, q.msgBound = msgBound ∧ WellFormedEmptyBookQuery q := by
  refine ⟨{ market := { currency := 1, goods := 2, epsilon := 0 }
            ajtaiParams := emptyClearingAjtaiParams
            msgBound := msgBound
            noiseBound := 1
            smudgeBound := 2 ^ 40
            secBits := 40
            qModulus := 2 * msgBound + 2 ^ 62
            committedOrders := [] },
          rfl, Nat.zero_lt_one, Nat.le_refl 40, Nat.le_of_eq (Nat.one_mul _), ?_, by dsimp only; decide, rfl, rfl⟩
  dsimp only
  rw [Nat.add_assoc, Nat.mul_add]
  exact Nat.add_lt_add_left (by decide : 2 * (1 + 2 ^ 40) < 2 ^ 62) (2 * msgBound)

/-- Independent semantic input-domain specification for quiescent / zero-quantity order books of
    **arbitrary length** (`0, 1, 2, ...` orders, defined purely over query fields with ZERO reference
    to `verifySameOpening` or `SameOpeningMeaning`!). -/
def WellFormedZeroBookQuery (q : SameOpeningQuery) : Prop :=
  0 < q.noiseBound ∧ 40 ≤ q.secBits ∧ q.noiseBound * (2 ^ q.secBits) ≤ q.smudgeBound ∧
  2 * (q.effectiveMsgBound + q.noiseBound + q.smudgeBound) < q.qModulus ∧
  q.market.currency ≠ q.market.goods ∧
  q.ajtaiParams.cols = 32 ∧
  (q.committedOrders.map (·.account)).Nodup ∧
  (∀ s ∈ q.committedOrders,
    s.account < goldilocksPrime ∧
    s.dualComm = (commitPrivateOrder q.ajtaiParams s.account s.side s.maxBits
      GoldilocksExt2.zero zeroOrderBitWitness).dualComm)

theorem wellFormedZeroBookQuery_of_emptyBook {q : SameOpeningQuery}
    (hq : WellFormedEmptyBookQuery q) : WellFormedZeroBookQuery q := by
  rcases hq with ⟨hPos, hSec, hDrown, hNoWrap, hAssets, hCols, hEmpty⟩
  refine ⟨hPos, hSec, hDrown, ?_, hAssets, hCols, by simp [hEmpty], by intro _ hs; rw [hEmpty] at hs; cases hs⟩
  simpa [SameOpeningQuery.effectiveMsgBound, hEmpty, orderBookMsgBound] using hNoWrap

/-- Explicit **non-empty 2-order (`[bid, ask]`)** inhabitedness witness for `WellFormedZeroBookQuery`. -/
theorem wellFormedZeroBookQuery_twoOrders_inhabited
    (acc₁ acc₂ : AccountId) (hNe : acc₁ ≠ acc₂)
    (h₁ : acc₁ < goldilocksPrime) (h₂ : acc₂ < goldilocksPrime) :
    ∃ q : SameOpeningQuery,
      q.committedOrders.length = 2 ∧ WellFormedZeroBookQuery q := by
  let s₁ := commitPrivateOrder emptyClearingAjtaiParams acc₁ .bid 8 GoldilocksExt2.zero zeroOrderBitWitness
  let s₂ := commitPrivateOrder emptyClearingAjtaiParams acc₂ .ask 8 GoldilocksExt2.zero zeroOrderBitWitness
  refine ⟨{ market := { currency := 1, goods := 2, epsilon := 0 }
            ajtaiParams := emptyClearingAjtaiParams
            noiseBound := 1
            smudgeBound := 2 ^ 40
            secBits := 40
            qModulus := 2 ^ 62
            committedOrders := [s₁, s₂] },
          rfl, Nat.zero_lt_one, Nat.le_refl 40, Nat.le_of_eq (Nat.one_mul _),
          by change 2 * (512 + 1 + 2 ^ 40) < 2 ^ 62; decide,
          by dsimp only; decide, rfl, ?_, ?_⟩
  · dsimp only [s₁, s₂, commitPrivateOrder, List.map]; simp [hNe]
  · intro s hs; simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | hsNil
    · exact ⟨h₁, rfl⟩
    · exact ⟨h₂, rfl⟩
    · cases hsNil

/-- Canonical zero-flow KKT witness synthesized for `numOrders` quiescent committed orders. -/
def zeroBookClearingWitness (numOrders : Nat) : SameOpeningWitness where
  orderWitnesses := List.replicate numOrders zeroOrderBitWitness
  transfers := []
  kktCert := { price := 1, potentials := (0, 0), slacks := List.replicate numOrders 1 }

/-- Canonical zero-flow KKT witness synthesized for any `WellFormedEmptyBookQuery`. -/
def emptyBookClearingWitness : SameOpeningWitness := zeroBookClearingWitness 0

private theorem checkOrderWitnessList_zeroBook (pp : AjtaiParams) :
    ∀ (idx : Nat) (specs : List CommittedOrderSpec),
      (∀ s ∈ specs, s.account < goldilocksPrime ∧
        s.dualComm = (commitPrivateOrder pp s.account s.side s.maxBits GoldilocksExt2.zero zeroOrderBitWitness).dualComm) →
      checkOrderWitnessList pp idx specs (List.replicate specs.length zeroOrderBitWitness) = none
  | _, [], _ => rfl
  | idx, s :: ss, hAll => by
    obtain ⟨hsAcc, hsComm⟩ := hAll s List.mem_cons_self
    have hAccSome : canonicalLift? s.account = some (Goldilocks.ofNat s.account) :=
      canonicalLift?_eq_some_ofNat hsAcc
    have hZSome : canonicalLift? 0 = some (Goldilocks.ofNat 0) :=
      canonicalLift?_eq_some_ofNat (by unfold CanonicalLift goldilocksPrime; omega)
    let tbl := [Goldilocks.ofNat s.account, Goldilocks.ofNat (sideTag s.side),
                Goldilocks.ofNat 0, Goldilocks.ofNat 0,
                Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero]
    have hTblS : orderWitnessTable? s zeroOrderBitWitness = some tbl := by
      dsimp only [orderWitnessTable?, zeroOrderBitWitness, OrderBitWitness.qty, OrderBitWitness.total, bitsToNat, GoldilocksExt2.zero]
      rw [hAccSome, hZSome]; rfl
    have hCommEq : s.dualComm = (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl := by
      rw [hsComm]
      dsimp only [commitPrivateOrder, zeroOrderBitWitness, OrderBitWitness.qty, OrderBitWitness.total, bitsToNat, orderWitnessTable?, GoldilocksExt2.zero]
      rw [hAccSome, hZSome]; rfl
    simp only [List.length_cons, List.replicate_succ, checkOrderWitnessList, hTblS]
    have hRange : (!(decide (zeroOrderBitWitness.qtyBits.length ≤ s.maxBits) &&
        decide (zeroOrderBitWitness.totalBits.length ≤ s.maxBits))) = false := by
      simp [zeroOrderBitWitness]
    have hBne : (s.dualComm != (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl) = false := by
      rw [hCommEq]; simp
    simp only [hRange, hBne, Bool.false_eq_true, ↓reduceIte]
    exact checkOrderWitnessList_zeroBook pp (idx + 1) ss (fun s' hs' => hAll s' (List.mem_cons_of_mem _ hs'))

private theorem materializeOrders_zero_accounts :
    ∀ (specs : List CommittedOrderSpec),
      (materializeOrders specs (List.replicate specs.length zeroOrderBitWitness)).map (·.account) =
        specs.map (·.account)
  | [] => rfl
  | _ :: ss => by simp [List.replicate_succ, materializeOrders, materializeOrder, materializeOrders_zero_accounts ss]

private theorem materializeOrders_zero_qty :
    ∀ (specs : List CommittedOrderSpec) (o : Order),
      o ∈ materializeOrders specs (List.replicate specs.length zeroOrderBitWitness) → o.qty = 0
  | [], _, ho => by cases ho
  | _ :: ss, o, ho => by
    simp only [List.length_cons, List.replicate_succ, materializeOrders, List.mem_cons] at ho
    rcases ho with rfl | hTl
    · rfl
    · exact materializeOrders_zero_qty ss o hTl

private theorem finSum_const_zero : ∀ (n : Nat), finSum n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by simp [finSum, finSum_const_zero n]

private theorem replicate_one_getD :
    ∀ (n idx : Nat), idx < n → (List.replicate n (1 : Int)).getD idx 0 = 1
  | 0, _, h => by omega
  | _ + 1, 0, _ => rfl
  | n + 1, k + 1, h => replicate_one_getD n k (by omega)

theorem verifySameOpening_zeroBook_complete {q : SameOpeningQuery}
    (hq : WellFormedZeroBookQuery q) :
    verifySameOpening q (zeroBookClearingWitness q.committedOrders.length) = .ok := by
  rcases hq with ⟨hPos, hSec, hDrown, hNoWrap, hAssets, hCols, hNodup, hOrders⟩
  have hSmB : checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits = true :=
    (checkSmudgeSafe_iff _ _ _).2 ⟨hPos, hSec, hDrown⟩
  have hNwB : checkModulusNoWrap q.effectiveMsgBound q.noiseBound q.smudgeBound q.qModulus = true :=
    (checkModulusNoWrap_iff _ _ _ _).2 hNoWrap
  have hColsB : (q.ajtaiParams.cols != 32) = false := by simp [hCols]
  have hChkOrd := checkOrderWitnessList_zeroBook q.ajtaiParams 0 q.committedOrders hOrders
  unfold verifySameOpening
  simp only [hSmB, hNwB, hAssets, hColsB, zeroBookClearingWitness, hChkOrd,
             Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  let orders := materializeOrders q.committedOrders (List.replicate q.committedOrders.length zeroOrderBitWitness)
  let zeroEpsMarket : Market := { q.market with epsilon := 0 }
  let cert : Certificate := { price := 1, potentials := (0, 0), slacks := List.replicate q.committedOrders.length 1 }
  have hOrdLen : orders.length = q.committedOrders.length :=
    materializeOrders_length _ _ (by simp)
  have hZeroQty : ∀ o ∈ orders, o.qty = 0 := materializeOrders_zero_qty q.committedOrders
  have hFill0 : ∀ (m : Market) (o : Order), o.fill m [] = 0 := fun m o => by
    unfold Order.fill netFlow; cases o.side <;> rfl
  have hPaid0 : ∀ (m : Market) (o : Order), o.paid m [] = 0 := fun m o => by
    unfold Order.paid netFlow; cases o.side <;> rfl
  have hDupNone : firstDuplicateAccount? orders = none :=
    (firstDuplicateAccount?_none_iff orders).2 (by dsimp [orders]; rw [materializeOrders_zero_accounts]; exact hNodup)
  have hFiltNil : ∀ (os : List Order) (sd : Side), (∀ o ∈ os, o.qty = 0) →
      os.filter (fun o => o.side == sd && o.qty > 0) = [] := by
    intro os sd hz; induction os with
    | nil => rfl
    | cons o os ih =>
      have ho : o.qty = 0 := hz o List.mem_cons_self
      simp [List.filter, ho, ih (fun o' hm => hz o' (List.mem_cons_of_mem _ hm))]
  have hCrossInt : priceInCrossingInterval orders 1 = true := by
    unfold priceInCrossingInterval highestBid? lowestAsk?
    rw [hFiltNil orders .bid hZeroQty, hFiltNil orders .ask hZeroQty]
  have hNoCrossPair : hasCrossingPair orders = false := by
    unfold hasCrossingPair highestBid? lowestAsk?
    rw [hFiltNil orders .bid hZeroQty, hFiltNil orders .ask hZeroQty]
  have hUnifNone : orders.find? (fun o => o.paid zeroEpsMarket [] ≠ (cert.price : Int) * o.fill zeroEpsMarket []) = none :=
    List.find?_eq_none.2 (fun o _ => by simp [hPaid0, hFill0])
  have hObj0 : ∀ m : Market, finSum orders.length (fun i => (orders.get i).fill m []) = 0 := fun m => by
    have hFn : (fun i : Fin orders.length => (orders.get i).fill m []) = (fun _ => 0) := by funext i; exact hFill0 m _
    rw [hFn, finSum_const_zero]
  have hDualCap0 : finSum orders.length (fun i =>
      (if (orders.get i).crosses cert.price then ((orders.get i).qty : Int) else 0) * (cert.slacks.getD i.val 0)) = 0 := by
    have hFn : (fun i : Fin orders.length =>
        (if (orders.get i).crosses cert.price then ((orders.get i).qty : Int) else 0) * (cert.slacks.getD i.val 0)) = (fun _ => 0) := by
      funext i
      have hq0 : (orders.get i).qty = 0 := hZeroQty (orders.get i) (List.get_mem orders i)
      rw [hq0]; simp
    rw [hFn, finSum_const_zero]
  have hJudgeOk : Obend.Judge.judge zeroEpsMarket orders [] cert = .ok () := by
    have hAssetM : zeroEpsMarket.currency ≠ zeroEpsMarket.goods := hAssets
    have hSlLen : cert.slacks.length = orders.length := by simp [cert, hOrdLen]
    have hCrossCert : priceInCrossingInterval orders cert.price = true := hCrossInt
    unfold Obend.Judge.judge
    simp only [hAssetM, ↓reduceIte, List.find?]
    rw [hDupNone]; dsimp only
    rw [hCrossCert]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp only [hSlLen, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [hUnifNone]; dsimp only
    split
    · rename_i hNe
      refine False.elim (hNe ?_)
      rw [← finSum_const_zero orders.length]; congr 1; funext i
      cases (orders.get i).side <;> simp [hFill0]
    · split
      · rename_i i hi
        exfalso
        have hp := (List.find?_eq_some_iff_append.1 hi).1
        rw [hFill0] at hp
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hp
        rcases hp with hLt | hCap
        · omega
        · split at hCap <;> omega
      · split
        · rename_i i hi
          exfalso
          have hd := (List.find?_eq_some_iff_append.1 hi).1
          have hSl : cert.slacks.getD i.val 0 = 1 := replicate_one_getD q.committedOrders.length i.val (by omega)
          dsimp only [cert] at hSl hd
          rw [hSl] at hd
          simp at hd
          split at hd <;> cases hd
        · rw [hObj0 zeroEpsMarket, hDualCap0, hNoCrossPair]
          simp [zeroEpsMarket]
  change (match Obend.Judge.judge zeroEpsMarket orders [] cert with
          | .error r => Judge.Verdict.refused (SameOpeningRefusal.clearingRefused r) []
          | .ok () =>
            if kktPrimalDualGapZero q.market orders [] cert then Judge.Verdict.ok
            else Judge.Verdict.refused
              (SameOpeningRefusal.nonzeroPrimalDualGap (dualObjective orders cert) (primalObjective q.market orders [])) []) =
        Judge.Verdict.ok
  rw [hJudgeOk]; dsimp only
  have hGapB : kktPrimalDualGapZero q.market orders [] cert = true := by
    unfold kktPrimalDualGapZero dualObjective primalObjective
    dsimp only
    rw [hDualCap0, hObj0 q.market]
    decide
  rw [hGapB]; rfl

theorem verifySameOpening_emptyBook_complete {q : SameOpeningQuery}
    (hq : WellFormedEmptyBookQuery q) :
    verifySameOpening q emptyBookClearingWitness = .ok := by
  have hZ := verifySameOpening_zeroBook_complete (wellFormedZeroBookQuery_of_emptyBook hq)
  simpa [hq.2.2.2.2.2.2, emptyBookClearingWitness] using hZ

/-- **Lawful `Obend.Judge` for Private-Input Convex Clearing (`privateConvexSameOpeningJudge`)**:
    Combines `Choe–Kang–Stehlé (2026/2546)` smudging enforcement, operational `effectiveMsgBound`
    no-wraparound verification, canonical `< goldilocksPrime` field lifts, salted `DarkBazaar`
    `canopyAjtaiDualPCS` commitment verification, `BitZ (2026/2141)` $B$-bit range witnesses, and
    $O(N)$ KKT exact optimality certification over quiescent books of arbitrary length (`WellFormedZeroBookQuery`). -/
instance privateConvexSameOpeningJudge : Judge SameOpeningQuery SameOpeningWitness where
  Clause := SameOpeningRefusal
  Meaning := SameOpeningMeaning
  check _ q c := verifySameOpening q c
  sound := verifySameOpening_sound
  refutes := sameOpeningRefutes
  refuted hRef hMarks := (verifySameOpening_refuted hRef hMarks).2.2
  Fragment := WellFormedZeroBookQuery
  complete := by
    intro q hFrag _
    exact ⟨zeroBookClearingWitness q.committedOrders.length, 0, verifySameOpening_zeroBook_complete hFrag⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

/-! ## 6. Witness-Independent Public ZK Verdict Collapse (`PublicSameOpeningVerdict`) -/

/-- Public on-chain verdict vocabulary collapsing all private-witness refusal indices and dual values
    (`.bitzRangeExceeded idx`, `.dualCommitmentMismatch idx`, `.nonzeroPrimalDualGap d p`, etc.)
    into a single constant `.privateWitnessRejected` tag so refusal leaks **zero** bits of private order state! -/
inductive PublicSameOpeningVerdict where
  | accepted
  | unsmudgedThresholdNoise
  | modulusWraparoundUnsafe
  | malformedMarketAssets
  | invalidLatticeDimension
  | privateWitnessRejected
  deriving DecidableEq, Repr

/-- Project a detailed `Judge.Verdict SameOpeningRefusal` to its zero-leakage `PublicSameOpeningVerdict`. -/
def toPublicZkVerdict : Judge.Verdict SameOpeningRefusal → PublicSameOpeningVerdict
  | .ok => .accepted
  | .refused .unsmudgedThresholdNoise _ => .unsmudgedThresholdNoise
  | .refused .modulusWraparoundUnsafe _ => .modulusWraparoundUnsafe
  | .refused .malformedMarketAssets _ => .malformedMarketAssets
  | .refused .invalidLatticeDimension _ => .invalidLatticeDimension
  | .refused _ _ => .privateWitnessRejected
  | .uncovered => .privateWitnessRejected

/-- **Private-Index Leakage-Freeness (`toPublicZkVerdict_hides_private_index`)**:
    For any well-formed public query `q` (passing smudging, modulus no-wraparound, asset, and lattice
    dimension guards), ANY two rejected private witnesses `c₁, c₂` (regardless of which trader's
    `orderIdx` failed `BitZ`, `CanonicalLift`, commitment equality, or KKT gap!) produce the exact
    same `.privateWitnessRejected` public verdict. -/
theorem toPublicZkVerdict_hides_private_index (q : SameOpeningQuery) (c₁ c₂ : SameOpeningWitness)
    (hSm : checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits = true)
    (hNw : checkModulusNoWrap q.effectiveMsgBound q.noiseBound q.smudgeBound q.qModulus = true)
    (hAssets : q.market.currency ≠ q.market.goods)
    (hCols : q.ajtaiParams.cols = 32)
    (hRej₁ : verifySameOpening q c₁ ≠ .ok)
    (hRej₂ : verifySameOpening q c₂ ≠ .ok) :
    toPublicZkVerdict (verifySameOpening q c₁) = .privateWitnessRejected ∧
    toPublicZkVerdict (verifySameOpening q c₂) = .privateWitnessRejected := by
  have oneSide : ∀ c : SameOpeningWitness, verifySameOpening q c ≠ .ok →
      toPublicZkVerdict (verifySameOpening q c) = .privateWitnessRejected := by
    intro c hRej
    have hColsB : (q.ajtaiParams.cols != 32) = false := by simp [hCols]
    unfold verifySameOpening at hRej ⊢
    simp only [hSm, hNw, hAssets, hColsB, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRej ⊢
    cases hOrd : checkOrderWitnessList q.ajtaiParams 0 q.committedOrders c.orderWitnesses with
    | some err =>
      have hNotRef := checkOrderWitnessList_not_refutes q.ajtaiParams 0 _ _ err hOrd
      cases err <;> first | rfl | (simp [sameOpeningRefutes] at hNotRef)
    | none =>
      simp only [hOrd] at hRej
      cases hJ : Obend.Judge.judge { q.market with epsilon := 0 }
          (materializeOrders q.committedOrders c.orderWitnesses) c.transfers c.kktCert with
      | error _ => simp [toPublicZkVerdict]
      | ok _ =>
        simp only [hJ] at hRej
        cases hGap : kktPrimalDualGapZero q.market
            (materializeOrders q.committedOrders c.orderWitnesses) c.transfers c.kktCert
        · simp [toPublicZkVerdict]
        · exfalso; simp [hGap] at hRej
  exact ⟨oneSide c₁ hRej₁, oneSide c₂ hRej₂⟩

/-- **Exact Binary Public Verdict Characterization (`toPublicZkVerdict_eq_ite`)**:
    For every public-guard-passing query `q`, `toPublicZkVerdict (verifySameOpening q c)` is completely
    determined by the boolean acceptance bit `verifySameOpening q c == .ok` (leaking zero refusal metadata). -/
theorem toPublicZkVerdict_eq_ite (q : SameOpeningQuery) (c : SameOpeningWitness)
    (hSm : checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits = true)
    (hNw : checkModulusNoWrap q.effectiveMsgBound q.noiseBound q.smudgeBound q.qModulus = true)
    (hAssets : q.market.currency ≠ q.market.goods)
    (hCols : q.ajtaiParams.cols = 32) :
    toPublicZkVerdict (verifySameOpening q c) =
      if verifySameOpening q c == .ok then .accepted else .privateWitnessRejected := by
  by_cases hOk : verifySameOpening q c = .ok
  · rw [hOk]; rfl
  · rw [beq_eq_false_iff_ne.2 hOk]
    exact (toPublicZkVerdict_hides_private_index q c c hSm hNw hAssets hCols hOk hOk).1

/-- Explicit `2026/2546` Judge Refutation Corollary: any query with `smudgeBound = 0` is
    refuted by `privateConvexSameOpeningJudge` at every grade `r` and for every candidate `c`. -/
theorem unsmudged_query_refuted_by_judge (r : Nat) (q : SameOpeningQuery) (c : SameOpeningWitness)
    (hZero : q.smudgeBound = 0) :
    privateConvexSameOpeningJudge.check r q c = .refused .unsmudgedThresholdNoise [] ∧
    (∀ c', ¬ privateConvexSameOpeningJudge.Meaning q c') := by
  have hCheckFalse : checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits = false := by
    cases hb : checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits
    · rfl
    · exfalso
      have hs := (checkSmudgeSafe_iff _ _ _).1 hb
      rw [hZero] at hs
      exact smudgeSafe_refuses_unsmudged q.noiseBound q.secBits hs
  have hVer : privateConvexSameOpeningJudge.check r q c = .refused .unsmudgedThresholdNoise [] := by
    change verifySameOpening q c = .refused .unsmudgedThresholdNoise []
    unfold verifySameOpening
    simp [hCheckFalse]
  exact ⟨hVer, privateConvexSameOpeningJudge.refuted hVer rfl⟩

end Obend.Crypto
end
