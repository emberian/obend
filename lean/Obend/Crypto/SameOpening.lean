module
/-
# Obend.Crypto.SameOpening — Untrusted FHE Search, `BitZ` Range Packing, Smudged Threshold Guard & KKT `Judge`

Formalizes the 2026 **Private-Input Convex Clearing (`SameOpening`)** architecture
(`BitZ ePrint 2026/2141` + `Tulva ePrint 2026/2485` + `Choe–Kang–Stehlé ePrint 2026/2546` defense):
1. **Mandatory Statistical Smudging Guard (`SmudgeSafe`)**:
   Enforces `0 < noiseBound ∧ 40 ≤ secBits ∧ noiseBound * 2 ^ secBits ≤ smudgeBound`,
   provably refusing unsmudged threshold decryptions (`smudgeSafe_refuses_unsmudged`) that leak
   exact LWE/RLWE secret-key linear equations under `Choe–Kang–Stehlé (2026/2546)`.
2. **`BitZ` (`2026/2141`) Boolean Bit-Packing & Free $B$-Bit Range Theorem**:
   `bitsToNat` and `bitsToNat_lt_two_pow`, proving that committing to a length-$\le B$ bit vector
   yields `val < 2 ^ B` with zero auxiliary range-gadget overhead.
3. **Dual-Spine `SameOpeningWitness` & Exact Zero-Gap KKT Certificate (`kktPrimalDualGapZero`)**:
   Verifies that private orders opened into the $O(N)$ primal-dual KKT clearing check match the
   exact `canopyAjtaiDualPCS` commitments (`Canopy` 256-bit Merkle + `Ajtai` Module-SIS) and satisfy
   zero primal-dual duality gap (`dualObjective = primalObjective`).
4. **Lawful `Obend.Judge` (`privateConvexSameOpeningJudge`)**:
   Registered `Judge SameOpeningQuery SameOpeningWitness` whose non-tautological semantic
   `SameOpeningMeaning` certifies smudging safety, `BitZ` range bounds, dual-spine commitment
   binding, zero KKT gap, and universal global optimality over **all** feasible allocations —
   with zero trust in the off-chain FHE solver.
-/
public import Obend.Judge.Class
public import Obend.Judge.Clearing
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck
public import Obend.Crypto.PCS
public import Obend.Crypto.DualSpine

@[expose] public section
namespace Obend.Crypto

open Obend.Ledger
open Obend.Judge

set_option autoImplicit false

/-! ## 1. `Choe–Kang–Stehlé` (`ePrint 2026/2546`) Statistical Smudging Guard -/

/-- **Mandatory Threshold Decryption Smudging Bound (`SmudgeSafe`)**:
    Defends threshold/collective FHE decryptions (`Tulva 2026/2485`) against the
    `Choe–Kang–Stehlé (2026/2546)` IND-CPA-D key-recovery attack by requiring positive noise bound,
    at least 40 bits of statistical drowning security, and `noiseBound * 2 ^ secBits ≤ smudgeBound`. -/
def SmudgeSafe (noiseBound smudgeBound secBits : Nat) : Prop :=
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
  | b :: bs, 0, hlen => by simp at hlen
  | b :: bs, B + 1, hlen => by
    simp only [List.length_cons] at hlen
    have ih := bitsToNat_lt_two_pow bs (B := B) (by omega)
    simp only [bitsToNat, Nat.pow_succ]
    cases b <;> simp <;> omega

/-! ## 3. Dual-Spine Committed Private Orders & `SameOpening` Data Model -/

/-- Public on-chain / query specification of a committed private order:
    public account and side, `BitZ` bit-width cap `maxBits`, and cross-assumption
    `canopyAjtaiDualPCS` commitment `(CanopyCommitment × AjtaiCommitment)`. -/
structure CommittedOrderSpec where
  account : AccountId
  side : Side
  maxBits : Nat
  dualComm : CanopyCommitment × AjtaiCommitment
  deriving DecidableEq

/-- Private `BitZ` bit-packed witness for an order's quantity and total limit value. -/
structure OrderBitWitness where
  qtyBits : List Bool
  totalBits : List Bool
  deriving DecidableEq, Repr

def OrderBitWitness.qty (w : OrderBitWitness) : Nat :=
  bitsToNat w.qtyBits

def OrderBitWitness.total (w : OrderBitWitness) : Nat :=
  bitsToNat w.totalBits

def sideTag : Side → Nat
  | .bid => 0
  | .ask => 1

/-- Canonical 2-variable ($2^2 = 4$-element) `Goldilocks` multilinear table committed by both
    the FHE input ciphertexts (`BitZ` / `Tulva`) and the KKT clearing proof (`SameOpening`). -/
def orderWitnessTable (spec : CommittedOrderSpec) (w : OrderBitWitness) : List Goldilocks :=
  [Goldilocks.ofNat spec.account,
   Goldilocks.ofNat (sideTag spec.side),
   Goldilocks.ofNat w.qty,
   Goldilocks.ofNat w.total]

theorem orderWitnessTable_length (spec : CommittedOrderSpec) (w : OrderBitWitness) :
    (orderWitnessTable spec w).length = 2 ^ 2 := rfl

/-- Helper constructor committing a private `(account, side, maxBits, w)` under `canopyAjtaiDualPCS`. -/
def commitPrivateOrder (pp : AjtaiParams) (account : AccountId) (side : Side)
    (maxBits : Nat) (w : OrderBitWitness) : CommittedOrderSpec :=
  let provisional : CommittedOrderSpec :=
    { account := account
      side := side
      maxBits := maxBits
      dualComm := (canopyCommit deployedCanopyHash32 2 [], ajtaiLatticeCommit pp 2 []) }
  let comm := (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 2
    (orderWitnessTable provisional w)
  { account := account
    side := side
    maxBits := maxBits
    dualComm := comm }

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
    opened `BitZ` bit-vectors, conservation-checked `ResourcePosting`s, and $O(N)$ KKT duals. -/
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
  | witnessCountMismatch (expected actual : Nat)
  | bitzRangeExceeded (orderIdx : Nat)
  | dualCommitmentMismatch (orderIdx : Nat)
  | clearingRefused (reason : ClearingRefusal)
  | nonzeroPrimalDualGap (dualVal primalVal : Int)
  deriving DecidableEq, Repr

/-- Compute the concrete `CanopyCommitment × AjtaiCommitment` pair for `(spec, w)`. -/
def commitOrderDual (pp : AjtaiParams) (spec : CommittedOrderSpec) (w : OrderBitWitness) :
    CanopyCommitment × AjtaiCommitment :=
  (canopyAjtaiDualPCS deployedCanopyHash32 pp).commit ((), ()) 2 (orderWitnessTable spec w)

/-- Semantic proposition that every committed order was opened to a valid `BitZ` $2^B$-bounded
    witness matching its `canopyAjtaiDualPCS` commitment. -/
def AllOrdersOpenedAndBounded (pp : AjtaiParams) :
    List CommittedOrderSpec → List OrderBitWitness → Prop
  | [], [] => True
  | s :: ss, w :: ws =>
    w.qty < 2 ^ s.maxBits ∧
    w.total < 2 ^ s.maxBits ∧
    commitOrderDual pp s w = s.dualComm ∧
    AllOrdersOpenedAndBounded pp ss ws
  | _, _ => False

/-- Executable per-order `BitZ` bit-length and `canopyAjtaiDualPCS` commitment checker. -/
def checkOrderWitnessList (pp : AjtaiParams) :
    Nat → List CommittedOrderSpec → List OrderBitWitness → Option SameOpeningRefusal
  | _, [], [] => none
  | _, [], ws => some (.witnessCountMismatch 0 ws.length)
  | _, ss, [] => some (.witnessCountMismatch ss.length 0)
  | idx, s :: ss, w :: ws =>
    if !(decide (w.qtyBits.length ≤ s.maxBits) && decide (w.totalBits.length ≤ s.maxBits)) then
      some (.bitzRangeExceeded idx)
    else if commitOrderDual pp s w != s.dualComm then
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
    have hCommEq : commitOrderDual pp s w = s.dualComm := by
      cases hc : (commitOrderDual pp s w != s.dualComm)
      · simpa [bne] using hc
      · exact absurd hc hComm
    exact ⟨bitsToNat_lt_two_pow w.qtyBits hRange'.1,
           bitsToNat_lt_two_pow w.totalBits hRange'.2,
           hCommEq,
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
    1. `SmudgeSafe`: `Choe–Kang–Stehlé (2026/2546)` threshold decryption drowning safety;
    2. `assetsDistinct`: well-formed distinct currency and goods assets;
    3. `ordersOpenedAndBounded`: `BitZ (2026/2141)` $2^B$ range bounds and `canopyAjtaiDualPCS`
       commitment equality for every private order;
    4. `accountsNodup`: one order per account;
    5. `zeroDualityGap`: exact KKT complementary slackness (`dualObjective = primalObjective`);
    6. `globallyOptimal`: universal global welfare optimality over **every** feasible circulation
       `f'`, without trusting the FHE solver that found `(transfers, kktCert)`. -/
structure SameOpeningMeaning (q : SameOpeningQuery) (c : SameOpeningWitness) : Prop where
  smudgeSafe : SmudgeSafe q.noiseBound q.smudgeBound q.secBits
  assetsDistinct : q.market.currency ≠ q.market.goods
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
    · split at h
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
  by_cases hEqAsset : q.market.currency = q.market.goods
  · simp [hEqAsset] at h
  simp only [hEqAsset, ↓reduceIte] at h
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

/-- **Refutation Soundness of `verifySameOpening` (`verifySameOpening_refuted`)**:
    Refusal by `.unsmudgedThresholdNoise` (`2026/2546`) or `.malformedMarketAssets` occurs at
    the root path `p = []` and proves that **no** certificate `c'` can satisfy `SameOpeningMeaning q c'`. -/
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
      by_cases hEqAsset : q.market.currency = q.market.goods
      · simp only [hEqAsset, ↓reduceIte, Judge.Verdict.refused.injEq] at hRef
        exact hRef.2.symm
      · simp only [hEqAsset, ↓reduceIte] at hRef
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
  · intro c' hMean
    unfold verifySameOpening at hRef
    cases hSm : checkSmudgeSafe q.noiseBound q.smudgeBound q.secBits
    · have hNotSm : ¬ SmudgeSafe q.noiseBound q.smudgeBound q.secBits := by
        intro hs
        have ht := (checkSmudgeSafe_iff _ _ _).2 hs
        rw [hSm] at ht; cases ht
      exact hNotSm hMean.smudgeSafe
    · simp only [hSm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRef
      by_cases hEqAsset : q.market.currency = q.market.goods
      · exact hMean.assetsDistinct hEqAsset
      · simp only [hEqAsset, ↓reduceIte] at hRef
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

/-- **Lawful `Obend.Judge` for Private-Input Convex Clearing (`privateConvexSameOpeningJudge`)**:
    Combines `Choe–Kang–Stehlé (2026/2546)` smudging enforcement, `BitZ (2026/2141)` $B$-bit
    range witnesses, `canopyAjtaiDualPCS` dual-spine commitment verification, and $O(N)$ KKT
    exact optimality certification. -/
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
