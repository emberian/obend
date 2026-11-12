module
/-
# Obend.Crypto.SameOpening — Canonical Field Lift, Salted `DarkBazaar` Hiding, `BitZ` Range & KKT `Judge`

Formalizes the 2026 **Private-Input Convex Clearing (`SameOpening` / `DarkBazaar`)** architecture
(`BitZ ePrint 2026/2141` + `Tulva ePrint 2026/2485` + `Choe–Kang–Stehlé ePrint 2026/2546` defense):
1. **Mandatory Statistical Smudging Guard (`SmudgeSafe`)**:
   Enforces `0 < noiseBound ∧ 40 ≤ secBits ∧ noiseBound * 2 ^ secBits ≤ smudgeBound`,
   provably refusing unsmudged threshold decryptions (`smudgeSafe_refuses_unsmudged`).
2. **Canonical `< goldilocksPrime` Field Lift (`orderWitnessTable?`)**:
   Enforces `CanonicalLift` (`< goldilocksPrime`) on `account`, `qty`, and `total` (`orderWitnessTable?_injective`),
   closing the `0` vs `p = 2^64 - 2^32 + 1` modular wrap-around alias at `maxBits = 64`.
3. **Explicit 128-Bit `GoldilocksExt2` Salt (`commitPrivateOrder`) & Dictionary Resistance**:
   Commits 8-element (`numVars = 3`, 32-limb exact-dimension Ajtai) salted order tables, proving
   the additive $\mathbb{F}_{p^2}$ hiding bijection (`saltedOrderMask_bijection`) and unconditional
   resistance to unsalted price/order dictionary lookup (`unsaltedDictionary_miss_of_nonzero_salt`,
   `unsaltedCommitDictionary_miss_of_nonzero_salt`).
4. **Lawful `Obend.Judge` (`privateConvexSameOpeningJudge`)**:
   Certifies smudging safety, canonical field lifts, `BitZ` $2^B$ range bounds, exact-dimension
   `canopyAjtaiDualPCS` commitment binding, zero primal-dual KKT gap, and global welfare optimality.
-/
public import Obend.Judge.Class
public import Obend.Judge.Clearing
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck
public import Obend.Crypto.PCS
public import Obend.Crypto.DualSpine
import all Obend.Judge.Class
import all Obend.Judge.Clearing
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Transcript
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.PCS
import all Obend.Crypto.DualSpine

public section
namespace Obend.Crypto

open Obend.Ledger
open Obend.Judge
open Obend.Apps.ZkNtt

set_option autoImplicit false

/-! ## 1. `Choe–Kang–Stehlé` (`ePrint 2026/2546`) Statistical Smudging Guard -/

/-- **Mandatory Threshold Decryption Smudging Bound (`SmudgeSafe`)**:
    Defends threshold/collective FHE decryptions (`Tulva 2026/2485`) against the
    `Choe–Kang–Stehlé (2026/2546)` IND-CPA-D key-recovery attack by requiring positive noise bound,
    at least 40 bits of statistical drowning security, and `noiseBound * 2 ^ secBits ≤ smudgeBound`. -/
@[expose] def SmudgeSafe (noiseBound smudgeBound secBits : Nat) : Prop :=
  0 < noiseBound ∧ 40 ≤ secBits ∧ noiseBound * (2 ^ secBits) ≤ smudgeBound

/-- Executable checker for `SmudgeSafe`. -/
def checkSmudgeSafe (noiseBound smudgeBound secBits : Nat) : Bool :=
  decide (0 < noiseBound) &&
  decide (40 ≤ secBits) &&
  decide (noiseBound * (2 ^ secBits) ≤ smudgeBound)

theorem checkSmudgeSafe_iff (noiseBound smudgeBound secBits : Nat) :
    checkSmudgeSafe noiseBound smudgeBound secBits = true ↔
      SmudgeSafe noiseBound smudgeBound secBits := by
  simp [checkSmudgeSafe, SmudgeSafe, Bool.and_eq_true, and_assoc]

/-- **`ePrint 2026/2546` Unsmudged Refusal Theorem**:
    Any zero-smudge (`smudgeBound = 0`) collective decryption configuration is unconditionally
    rejected by `SmudgeSafe`. -/
theorem smudgeSafe_refuses_unsmudged (noiseBound secBits : Nat) :
    ¬ SmudgeSafe noiseBound 0 secBits := by
  rintro ⟨hPos, _, hLe⟩
  have hPowPos : 0 < 2 ^ secBits := Nat.two_pow_pos secBits
  have hMulPos : 0 < noiseBound * (2 ^ secBits) := Nat.mul_pos hPos hPowPos
  omega

/-- Every `SmudgeSafe` configuration enforces at least a $2^{40}$ drowning ratio over `noiseBound`. -/
theorem smudgeSafe_exponential_gap {noiseBound smudgeBound secBits : Nat}
    (h : SmudgeSafe noiseBound smudgeBound secBits) :
    noiseBound * (2 ^ 40) ≤ smudgeBound := by
  rcases h with ⟨_, hSec, hBound⟩
  have hPow : 2 ^ 40 ≤ 2 ^ secBits := Nat.pow_le_pow_right (by decide) hSec
  exact Nat.le_trans (Nat.mul_le_mul_left noiseBound hPow) hBound

/-! ## 2. `BitZ` (`ePrint 2026/2141`) Bit-Packed Witness & Free $B$-Bit Range Bound -/

/-- Little-endian boolean bit-packing $\sum_{i} b_i 2^i$. -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

/-- **`BitZ` (`2026/2141`) Free $B$-Bit Range Theorem (`bitsToNat_lt_two_pow`)**:
    Any boolean bit-list of length $\le B$ decodes to a natural number strictly below $2^B$. -/
theorem bitsToNat_lt_two_pow :
    ∀ (bits : List Bool) {B : Nat}, bits.length ≤ B → bitsToNat bits < 2 ^ B
  | [], B, _ => Nat.two_pow_pos B
  | _ :: _, 0, hlen => by simp at hlen
  | b :: bs, B + 1, hlen => by
    simp only [List.length_cons] at hlen
    have ih := bitsToNat_lt_two_pow bs (B := B) (by omega)
    simp only [bitsToNat, Nat.pow_succ]
    cases b <;> simp <;> omega

/-! ## 3. Canonical Salted Private Orders (`DarkBazaar`), Hiding Bijection & Dictionary Resistance -/

/-- Public on-chain / query specification of a committed private order:
    public account and side, `BitZ` bit-width cap `maxBits`, and cross-assumption
    `canopyAjtaiDualPCS` commitment `(CanopyCommitment × AjtaiCommitment)` at arity `numVars = 3`. -/
structure CommittedOrderSpec where
  account : AccountId
  side : Side
  maxBits : Nat
  dualComm : CanopyCommitment × AjtaiCommitment
  deriving DecidableEq

/-- Private `BitZ` bit-packed witness for an order's quantity, total limit value, and
    128-bit cryptographic salt `salt : GoldilocksExt2` (defeating unsalted price dictionary lookup). -/
structure OrderBitWitness where
  qtyBits : List Bool
  totalBits : List Bool
  salt : GoldilocksExt2 := GoldilocksExt2.zero
  deriving DecidableEq, Repr

def OrderBitWitness.qty (w : OrderBitWitness) : Nat :=
  bitsToNat w.qtyBits

def OrderBitWitness.total (w : OrderBitWitness) : Nat :=
  bitsToNat w.totalBits

def sideTag : Side → Nat
  | .bid => 0
  | .ask => 1

theorem sideTag_goldilocks_injective {s₁ s₂ : Side}
    (h : Goldilocks.ofNat (sideTag s₁) = Goldilocks.ofNat (sideTag s₂)) : s₁ = s₂ := by
  cases s₁ <;> cases s₂
  · rfl
  · cases h
  · cases h
  · rfl

/-- Canonical 3-variable ($2^3 = 8$-element, 32-limb) `Goldilocks` multilinear table committed
    by both FHE input ciphertexts and KKT `SameOpening`:
    - Enforces `canonicalLift?` (`< goldilocksPrime`) on `account`, `qty`, and `total`
      (closing the `0` vs `p = 2^64 - 2^32 + 1` modular wrap-around alias!).
    - Embeds 128-bit `w.salt : GoldilocksExt2` in coordinates `(4, 5)` (closing unsalted dictionary lookup!). -/
def orderWitnessTable? (spec : CommittedOrderSpec) (w : OrderBitWitness) :
    Option (List Goldilocks) :=
  match canonicalLift? spec.account, canonicalLift? w.qty, canonicalLift? w.total with
  | some accF, some qtyF, some totF =>
    some [accF,
          Goldilocks.ofNat (sideTag spec.side),
          qtyF,
          totF,
          w.salt.c0,
          w.salt.c1,
          Goldilocks.zero,
          Goldilocks.zero]
  | _, _, _ => none

theorem orderWitnessTable?_length {spec : CommittedOrderSpec} {w : OrderBitWitness}
    {tbl : List Goldilocks} (h : orderWitnessTable? spec w = some tbl) :
    tbl.length = 2 ^ 3 := by
  unfold orderWitnessTable? at h
  split at h
  · cases h; rfl
  · cases h

theorem orderWitnessTable?_canonical {spec : CommittedOrderSpec} {w : OrderBitWitness}
    {tbl : List Goldilocks} (h : orderWitnessTable? spec w = some tbl) :
    CanonicalLift spec.account ∧ CanonicalLift w.qty ∧ CanonicalLift w.total := by
  unfold orderWitnessTable? at h
  cases ha : canonicalLift? spec.account with
  | none => simp [ha] at h
  | some accF =>
    cases hq : canonicalLift? w.qty with
    | none => simp [ha, hq] at h
    | some qtyF =>
      cases ht : canonicalLift? w.total with
      | none => simp [ha, hq, ht] at h
      | some totF =>
        obtain ⟨ca, _⟩ := (canonicalLift?_eq_some_iff spec.account accF).1 ha
        obtain ⟨cq, _⟩ := (canonicalLift?_eq_some_iff w.qty qtyF).1 hq
        obtain ⟨ct, _⟩ := (canonicalLift?_eq_some_iff w.total totF).1 ht
        exact ⟨ca, cq, ct⟩

/-- **Canonical Order-Table Injectivity (`orderWitnessTable?_injective`)**:
    Two order witnesses mapping to the same canonical `Goldilocks` table agree identically on
    `account`, `side`, `qty`, `total`, and 128-bit `salt` (impossible under `Goldilocks.ofNat`
    where `qty = 0` and `qty = goldilocksPrime` collide!). -/
theorem orderWitnessTable?_injective
    {s₁ s₂ : CommittedOrderSpec} {w₁ w₂ : OrderBitWitness} {tbl : List Goldilocks}
    (h₁ : orderWitnessTable? s₁ w₁ = some tbl)
    (h₂ : orderWitnessTable? s₂ w₂ = some tbl) :
    s₁.account = s₂.account ∧ s₁.side = s₂.side ∧
    w₁.qty = w₂.qty ∧ w₁.total = w₂.total ∧ w₁.salt = w₂.salt := by
  unfold orderWitnessTable? at h₁ h₂
  cases ha₁ : canonicalLift? s₁.account with
  | none => simp [ha₁] at h₁
  | some acc₁ =>
    cases hq₁ : canonicalLift? w₁.qty with
    | none => simp [ha₁, hq₁] at h₁
    | some qty₁ =>
      cases ht₁ : canonicalLift? w₁.total with
      | none => simp [ha₁, hq₁, ht₁] at h₁
      | some tot₁ =>
        cases ha₂ : canonicalLift? s₂.account with
        | none => simp [ha₂] at h₂
        | some acc₂ =>
          cases hq₂ : canonicalLift? w₂.qty with
          | none => simp [ha₂, hq₂] at h₂
          | some qty₂ =>
            cases ht₂ : canonicalLift? w₂.total with
            | none => simp [ha₂, hq₂, ht₂] at h₂
            | some tot₂ =>
              simp only [ha₁, hq₁, ht₁, Option.some.injEq] at h₁
              simp only [ha₂, hq₂, ht₂, Option.some.injEq] at h₂
              have hEq := h₁.trans h₂.symm
              simp only [List.cons.injEq, and_true] at hEq
              rcases hEq with ⟨hAcc, hSide, hQty, hTot, hc0, hc1⟩
              subst hAcc hQty hTot
              exact ⟨canonicalLift?_injective ha₁ ha₂,
                     sideTag_goldilocks_injective hSide,
                     canonicalLift?_injective hq₁ hq₂,
                     canonicalLift?_injective ht₁ ht₂,
                     GoldilocksExt2.ext hc0 hc1⟩

/-- Helper constructor committing a private DarkBazaar order `(account, side, maxBits, salt, w)`
    with explicit 128-bit `salt : GoldilocksExt2` under `canopyAjtaiDualPCS` (`numVars = 3`). -/
def commitPrivateOrder (pp : AjtaiParams) (account : AccountId) (side : Side)
    (maxBits : Nat) (salt : GoldilocksExt2) (w : OrderBitWitness) : CommittedOrderSpec :=
  let wSalted : OrderBitWitness := { w with salt := salt }
  let provisional : CommittedOrderSpec :=
    { account := account
      side := side
      maxBits := maxBits
      dualComm := (canopyCommit deployedCanopyHash32 3 [], ajtaiLatticeCommit pp 3 []) }
  let tbl := (orderWitnessTable? provisional wSalted).getD (List.replicate 8 Goldilocks.zero)
  let comm := (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl
  { account := account
    side := side
    maxBits := maxBits
    dualComm := comm }

/-- Additive 128-bit salt blinding in `GoldilocksExt2` ($\mathbb{F}_{p^2}$). -/
def blindOrderSalt (mask salt : GoldilocksExt2) : GoldilocksExt2 :=
  CommRingOps.add salt mask

/-- Additive 128-bit salt unblinding in `GoldilocksExt2` ($\mathbb{F}_{p^2}$). -/
def unblindOrderSalt (mask masked : GoldilocksExt2) : GoldilocksExt2 :=
  CommRingOps.sub masked mask

/-- **128-Bit Salt Hiding Bijection (`saltedOrderMask_bijection`)**:
    For every payload-derived mask `mask : GoldilocksExt2`, `blindOrderSalt mask` is a strict
    bijection on $\mathbb{F}_{p^2}$ (`|GoldilocksExt2| = p^2 > 2^127`), so a uniform 128-bit `salt`
    induces a uniform masked tag completely independent of `(account, side, qty, total)`. -/
theorem saltedOrderMask_bijection (mask salt masked : GoldilocksExt2) :
    unblindOrderSalt mask (blindOrderSalt mask salt) = salt ∧
    blindOrderSalt mask (unblindOrderSalt mask masked) = masked ∧
    (∀ s₁ s₂ : GoldilocksExt2, blindOrderSalt mask s₁ = blindOrderSalt mask s₂ → s₁ = s₂) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold unblindOrderSalt blindOrderSalt
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  · unfold blindOrderSalt unblindOrderSalt
    rw [LawfulCommRing.add_comm _ mask, LawfulCommRing.add_sub_cancel_left]
  · intro s₁ s₂ hEq
    have h := congrArg (unblindOrderSalt mask) hEq
    unfold unblindOrderSalt blindOrderSalt at h
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero,
        LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero] at h
    exact h

/-- Unsalted (`salt = 0`) dictionary table entry for candidate `(account, side, qtyBits, totalBits)`. -/
def unsaltedDictionaryTable? (pp : AjtaiParams) (account : AccountId) (side : Side)
    (qtyBits totalBits : List Bool) : Option (List Goldilocks) :=
  let dummySpec : CommittedOrderSpec :=
    { account := account
      side := side
      maxBits := 64
      dualComm := (canopyCommit deployedCanopyHash32 3 [], ajtaiLatticeCommit pp 3 []) }
  orderWitnessTable? dummySpec { qtyBits := qtyBits, totalBits := totalBits, salt := GoldilocksExt2.zero }

/-- **Unsalted Dictionary Table Miss (`unsaltedDictionary_miss_of_nonzero_salt`)**:
    Any canonical order table committed with a non-zero salt `w.salt ≠ 0` is disjoint from
    the entire unsalted price/quantity dictionary across **all** `(candAcc, candSide, candQty, candTotal)`. -/
theorem unsaltedDictionary_miss_of_nonzero_salt
    (pp : AjtaiParams) {spec : CommittedOrderSpec} {w : OrderBitWitness} {tbl : List Goldilocks}
    (hSalt : w.salt ≠ GoldilocksExt2.zero)
    (hTbl : orderWitnessTable? spec w = some tbl)
    (candAcc : AccountId) (candSide : Side) (candQtyBits candTotalBits : List Bool) :
    unsaltedDictionaryTable? pp candAcc candSide candQtyBits candTotalBits ≠ some tbl := by
  intro hDict
  unfold unsaltedDictionaryTable? at hDict
  have hInj := orderWitnessTable?_injective hTbl hDict
  exact hSalt hInj.2.2.2.2

/-- **Cryptographic Resistance to Unsalted Price Dictionary Lookup (`unsaltedCommitDictionary_miss_of_nonzero_salt`, `0 Classical`)**:
    Under `pp.cols = 32` and **either** `¬ BoundedCollision deployedCanopyHash32.eval (merkleMaxPreimageBytes 3)`
    **or** `ModuleSISHard pp 131070`, NO salted private order (`salt ≠ 0`) can ever match the
    `canopyAjtaiDualPCS` commitment of ANY unsalted (`salt = 0`) dictionary candidate! -/
theorem unsaltedCommitDictionary_miss_of_nonzero_salt
    (pp : AjtaiParams) (hCols : pp.cols = 32)
    (hOr : ¬ BoundedCollision deployedCanopyHash32.eval (merkleMaxPreimageBytes 3) ∨
           ModuleSISHard pp 131070)
    {account : AccountId} {side : Side} {maxBits : Nat}
    {salt : GoldilocksExt2} {w : OrderBitWitness}
    (hAcc : CanonicalLift account) (hQty : CanonicalLift w.qty) (hTot : CanonicalLift w.total)
    (hSalt : salt ≠ GoldilocksExt2.zero)
    (candAcc : AccountId) (candSide : Side) (candMaxBits : Nat) (candW : OrderBitWitness)
    (hcAcc : CanonicalLift candAcc) (hcQty : CanonicalLift candW.qty) (hcTot : CanonicalLift candW.total) :
    (commitPrivateOrder pp account side maxBits salt w).dualComm ≠
    (commitPrivateOrder pp candAcc candSide candMaxBits GoldilocksExt2.zero candW).dualComm := by
  intro hCommEq
  let w₁ : OrderBitWitness := { w with salt := salt }
  let w₂ : OrderBitWitness := { candW with salt := GoldilocksExt2.zero }
  let p₁ : CommittedOrderSpec :=
    { account := account, side := side, maxBits := maxBits,
      dualComm := (canopyCommit deployedCanopyHash32 3 [], ajtaiLatticeCommit pp 3 []) }
  let p₂ : CommittedOrderSpec :=
    { account := candAcc, side := candSide, maxBits := candMaxBits,
      dualComm := (canopyCommit deployedCanopyHash32 3 [], ajtaiLatticeCommit pp 3 []) }
  let tbl₁ := [liftCanonical account hAcc, Goldilocks.ofNat (sideTag side),
               liftCanonical w.qty hQty, liftCanonical w.total hTot,
               salt.c0, salt.c1, Goldilocks.zero, Goldilocks.zero]
  let tbl₂ := [liftCanonical candAcc hcAcc, Goldilocks.ofNat (sideTag candSide),
               liftCanonical candW.qty hcQty, liftCanonical candW.total hcTot,
               Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero]
  have ht₁ : orderWitnessTable? p₁ w₁ = some tbl₁ := by
    dsimp only [orderWitnessTable?, canonicalLift?, liftCanonical, p₁, w₁, tbl₁,
                OrderBitWitness.qty, OrderBitWitness.total]
    simp [show account < goldilocksPrime from hAcc,
          show bitsToNat w.qtyBits < goldilocksPrime from hQty,
          show bitsToNat w.totalBits < goldilocksPrime from hTot]
  have ht₂ : orderWitnessTable? p₂ w₂ = some tbl₂ := by
    dsimp only [orderWitnessTable?, canonicalLift?, liftCanonical, p₂, w₂, tbl₂,
                OrderBitWitness.qty, OrderBitWitness.total]
    have hz0 : GoldilocksExt2.zero.c0 = Goldilocks.zero := rfl
    have hz1 : GoldilocksExt2.zero.c1 = Goldilocks.zero := rfl
    simp [hz0, hz1,
          show candAcc < goldilocksPrime from hcAcc,
          show bitsToNat candW.qtyBits < goldilocksPrime from hcQty,
          show bitsToNat candW.totalBits < goldilocksPrime from hcTot]
  have hTblNe : tbl₁ ≠ tbl₂ := by
    intro hEq
    have ht₂' : orderWitnessTable? p₂ w₂ = some tbl₁ := by rw [ht₂, hEq]
    have hInj := orderWitnessTable?_injective ht₁ ht₂'
    exact hSalt hInj.2.2.2.2
  have hCommitTblEq :
      (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl₁ =
      (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 3 tbl₂ := by
    dsimp only [commitPrivateOrder, p₁, p₂, w₁, w₂] at hCommEq
    rw [ht₁, ht₂] at hCommEq
    exact hCommEq
  let bothWit := extractDualCommitCollisionBoth deployedCanopyHash32 pp tbl₁ tbl₂
    rfl rfl hCols hTblNe hCommitTblEq
  rcases hOr with hNoCol | hSIS
  · exact hNoCol ⟨bothWit.1⟩
  · exact hSIS ⟨bothWit.2⟩

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

/-- Public query to `privateConvexSameOpeningJudge`. -/
structure SameOpeningQuery where
  market : Market
  ajtaiParams : AjtaiParams
  noiseBound : Nat
  smudgeBound : Nat
  secBits : Nat
  committedOrders : List CommittedOrderSpec

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

/-- **Non-Tautological Semantic Meaning of `privateConvexSameOpeningJudge` (`SameOpeningMeaning`)**:
    Establishes simultaneously:
    1. `smudgeSafe`: `Choe–Kang–Stehlé (2026/2546)` threshold decryption drowning safety;
    2. `assetsDistinct`: well-formed distinct currency and goods assets;
    3. `exactLatticeCols`: exact 32-column Ajtai dimension matching 8-element salted order tables;
    4. `ordersOpenedAndBounded`: canonical `< goldilocksPrime` field lifts, `BitZ (2026/2141)` $2^B$
       range bounds, and `canopyAjtaiDualPCS` commitment equality for every private order;
    5. `accountsNodup`: one order per account;
    6. `zeroDualityGap`: exact KKT complementary slackness (`dualObjective = primalObjective`);
    7. `globallyOptimal`: universal global welfare optimality over **every** feasible circulation `f'`. -/
structure SameOpeningMeaning (q : SameOpeningQuery) (c : SameOpeningWitness) : Prop where
  smudgeSafe : SmudgeSafe q.noiseBound q.smudgeBound q.secBits
  assetsDistinct : q.market.currency ≠ q.market.goods
  exactLatticeCols : q.ajtaiParams.cols = 32
  ordersOpenedAndBounded : AllOrdersOpenedAndBounded q.ajtaiParams q.committedOrders c.orderWitnesses
  accountsNodup : ((materializeOrders q.committedOrders c.orderWitnesses).map (·.account)).Nodup
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

/-- Kernel checker for `privateConvexSameOpeningJudge`: runs in $O(N)$ over opened witnesses. -/
def verifySameOpening (q : SameOpeningQuery) (c : SameOpeningWitness) :
    Judge.Verdict SameOpeningRefusal :=
  if !checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits then
    .refused .unsmudgedThresholdNoise []
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
          · refine
              { smudgeSafe := (checkSmudgeSafe_iff _ _ _).1 hSm
                assetsDistinct := hEqAsset
                exactLatticeCols := hColsEq
                ordersOpenedAndBounded := checkOrderWitnessList_sound q.ajtaiParams 0 _ _ hOrd
                accountsNodup := judge_ok_accounts_nodup zeroEpsMarket orders c.transfers c.kktCert hJ
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
    Refusal by `.unsmudgedThresholdNoise`, `.malformedMarketAssets`, or `.invalidLatticeDimension`
    occurs at the root path `p = []` and proves that **no** certificate `c'` can satisfy `SameOpeningMeaning q c'`. -/
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
      if hEqAsset : q.market.currency = q.market.goods then
        simp only [hEqAsset, ↓reduceIte, Judge.Verdict.refused.injEq] at hRef
        exact hRef.2.symm
      else
        simp only [hEqAsset, ↓reduceIte] at hRef
        cases hCols : (q.ajtaiParams.cols != 32)
        · simp only [hCols, Bool.false_eq_true, ↓reduceIte] at hRef
          cases hOrd : checkOrderWitnessList q.ajtaiParams 0 q.committedOrders c.orderWitnesses with
          | some err =>
            simp only [hOrd, Judge.Verdict.refused.injEq] at hRef
            exact hRef.2.symm
          | none =>
            simp only [hOrd] at hRef
            cases hJ : Obend.Judge.judge { q.market with epsilon := 0 }
                (materializeOrders q.committedOrders c.orderWitnesses) c.transfers c.kktCert with
            | error _ =>
              simp only [hJ, Judge.Verdict.refused.injEq] at hRef
              exact hRef.2.symm
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
    · have hNotSm : ¬ SmudgeSafe q.noiseBound q.smudgeBound q.secBits := by
        intro hs
        have ht := (checkSmudgeSafe_iff _ _ _).2 hs
        rw [hSm] at ht; cases ht
      exact hNotSm hMean.smudgeSafe
    · simp only [hSm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
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
            rw [hf] at hMarks
            cases hMarks
          | none =>
            simp only [hOrd] at hRef
            cases hJ : Obend.Judge.judge { q.market with epsilon := 0 }
                (materializeOrders q.committedOrders c.orderWitnesses) c.transfers c.kktCert with
            | error _ =>
              simp only [hJ, Judge.Verdict.refused.injEq] at hRef
              rcases hRef with ⟨rfl, _⟩
              cases hMarks
            | ok _ =>
              simp only [hJ] at hRef
              cases hGap : kktPrimalDualGapZero q.market
                  (materializeOrders q.committedOrders c.orderWitnesses) c.transfers c.kktCert
              · simp only [hGap, Bool.false_eq_true, ↓reduceIte, Judge.Verdict.refused.injEq] at hRef
                rcases hRef with ⟨rfl, _⟩
                cases hMarks
              · simp [hGap] at hRef
        · have hNeCols : q.ajtaiParams.cols ≠ 32 := by simpa [bne] using hCols
          exact hNeCols hMean.exactLatticeCols

/-- **Lawful `Obend.Judge` for Private-Input Convex Clearing (`privateConvexSameOpeningJudge`)**:
    Combines `Choe–Kang–Stehlé (2026/2546)` smudging enforcement, canonical `< goldilocksPrime`
    field lifts, salted `DarkBazaar` `canopyAjtaiDualPCS` dual-spine commitment verification,
    `BitZ (2026/2141)` $B$-bit range witnesses, and $O(N)$ KKT exact optimality certification. -/
instance privateConvexSameOpeningJudge : Judge SameOpeningQuery SameOpeningWitness where
  Clause := SameOpeningRefusal
  Meaning := SameOpeningMeaning
  check _ q c := verifySameOpening q c
  sound := verifySameOpening_sound
  refutes := sameOpeningRefutes
  refuted hRef hMarks := (verifySameOpening_refuted hRef hMarks).2.2
  Fragment q := ∃ c, verifySameOpening q c = .ok
  complete := by
    intro _ ⟨c, hc⟩ _
    exact ⟨c, 0, hc⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

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
