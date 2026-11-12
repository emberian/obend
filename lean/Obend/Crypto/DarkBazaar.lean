module
/-
# Obend.Crypto.DarkBazaar — Pillar-4 Sealed Private Market Clearing Spine
End-to-end verified Pillar-4 `DarkBazaar` pipeline (`quarry/obend-apex.toml`) welding five stages
into `darkBazaar_sable_rlwe_smudge_clearing_conserves` and multi-epoch `ValidDarkBazaarTrace`:
1. **Nonlinear Utility / Risk Enclosure (`Obend.Analysis.TaylorModel`)** (`checkUtilityEnclosure_sound`).
2. **Exact Quantized `Sable` Inference (`FastRing` & `RangeSafe`)** (`sableDot_goldilocks_exact_of_noWrap`).
3. **Additive/Scalar RLWE Order Book Aggregation (`FastRing`)** (`rlweAdd_decrypts_to_sum`).
4. **Smudged Threshold Decryption & Refusals (`SmudgeSafe`)** (`thresholdDecrypt_exact_under_noise_cap`).
5. **`SameOpening` Salted KKT Clearing & `ConservedValue` Settlement** (`ValidDarkBazaarTrace`).
-/
public import Obend.Analysis.TaylorModel
public import Obend.Core.RangeSafe
public import Obend.Crypto.FastRing
public import Obend.Crypto.Poseidon2Goldilocks
public import Obend.Crypto.SameOpening
public import Obend.Logic.SeparationFrame
import all Obend.Analysis.RealAnalysis
import all Obend.Analysis.TaylorModel
import all Obend.Crypto.FastRing
import all Obend.Crypto.SameOpening
public section
namespace Obend.Crypto
open Obend.Apps.ZkNtt Obend.Crypto.Fast Obend.Ledger Obend.Judge Obend.Logic
set_option autoImplicit false

/-! ## 1. Stage 1 — Nonlinear Utility / Risk Enclosure (`Obend.Analysis.TaylorModel`) -/
structure TraderUtilityCert where
  tm : Obend.Analysis.TaylorModel
  feature : Obend.Analysis.CanonicalRat
  tickScale : Nat
  side : Side
  submittedTotal : Nat
  deriving DecidableEq, Repr
/-- Executable `TaylorModel` point/range enclosure & conservative tick-scaled reservation checker. -/
@[expose] def checkUtilityEnclosure (cert : TraderUtilityCert) : Bool :=
  let ptIv := Obend.Analysis.evalTaylorModelPoint cert.tm cert.feature
  let rngIv := Obend.Analysis.evalTaylorModelRange cert.tm
  let scaleRat : Obend.Analysis.CanonicalRat := cert.tickScale
  let subRat : Obend.Analysis.CanonicalRat := cert.submittedTotal
  let sideBoundOk :=
    match cert.side with
    | .bid => decide (subRat ≤ scaleRat * ptIv.lo)
    | .ask => decide (scaleRat * ptIv.hi ≤ subRat)
  decide (0 < cert.tickScale) &&
  cert.tm.domain.containsRat cert.feature &&
  decide (ptIv.lo ≤ ptIv.hi) &&
  decide (rngIv.lo ≤ rngIv.hi) &&
  sideBoundOk
/-- Semantic meaning of `TraderUtilityCert` with respect to the true nonlinear curve `u`. -/
def UtilityEnclosureHolds (u : Obend.Analysis.CanonicalRat → Obend.Analysis.CanonicalRat)
    (cert : TraderUtilityCert) : Prop :=
  0 < cert.tickScale ∧
  cert.feature ∈ cert.tm.domain ∧
  u cert.feature ∈ Obend.Analysis.evalTaylorModelPoint cert.tm cert.feature ∧
  u cert.feature ∈ Obend.Analysis.evalTaylorModelRange cert.tm ∧
  match cert.side with
  | .bid => (cert.submittedTotal : Obend.Analysis.CanonicalRat) ≤
      (cert.tickScale : Obend.Analysis.CanonicalRat) * u cert.feature
  | .ask => (cert.tickScale : Obend.Analysis.CanonicalRat) * u cert.feature ≤
      (cert.submittedTotal : Obend.Analysis.CanonicalRat)
theorem checkUtilityEnclosure_sound (cert : TraderUtilityCert)
    (u : Obend.Analysis.CanonicalRat → Obend.Analysis.CanonicalRat)
    (hModels : Obend.Analysis.TaylorModel.Models u cert.tm)
    (hOk : checkUtilityEnclosure cert = true) :
    UtilityEnclosureHolds u cert := by
  unfold checkUtilityEnclosure at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  rcases hOk with ⟨⟨⟨⟨hScalePos, hInDomB⟩, _⟩, _⟩, hSide⟩
  have hx : cert.feature ∈ cert.tm.domain :=
    (Obend.Analysis.Interval.containsRat_iff_mem cert.tm.domain cert.feature).1 hInDomB
  have hPt := Obend.Analysis.evalTaylorModelPoint_encloses hModels hx
  have hRng := Obend.Analysis.evalTaylorModelRange_encloses hModels hx
  have hPtBounds := (Obend.Analysis.Interval.mem_iff _ _).1 hPt
  have hScaleNonneg : (0 : Obend.Analysis.CanonicalRat) ≤ (cert.tickScale : Obend.Analysis.CanonicalRat) := by
    exact_mod_cast Nat.zero_le cert.tickScale
  refine ⟨hScalePos, hx, hPt, hRng, ?_⟩
  cases hs : cert.side
  · simp only [hs, decide_eq_true_eq] at hSide
    have hMul := Rat.mul_le_mul_of_nonneg_left hPtBounds.1 hScaleNonneg
    exact Rat.le_trans hSide hMul
  · simp only [hs, decide_eq_true_eq] at hSide
    have hMul := Rat.mul_le_mul_of_nonneg_left hPtBounds.2 hScaleNonneg
    exact Rat.le_trans hMul hSide
/-- Batch utility-enclosure alignment tying each trader's `TraderUtilityCert` to their `CommittedOrderSpec` and `OrderBitWitness`. -/
def checkUtilityBatch : List TraderUtilityCert → List CommittedOrderSpec → List OrderBitWitness → Bool
  | [], [], [] => true
  | c :: cs, s :: ss, w :: ws =>
    checkUtilityEnclosure c &&
    decide (c.side = s.side) &&
    decide (c.submittedTotal = w.total) &&
    checkUtilityBatch cs ss ws
  | _, _, _ => false
/-- Batch semantic predicate for Stage 1 across all traders in the auction. -/
def AllUtilityEnclosuresHold :
    List (Obend.Analysis.CanonicalRat → Obend.Analysis.CanonicalRat) →
    List TraderUtilityCert → List CommittedOrderSpec → List OrderBitWitness → Prop
  | [], [], [], [] => True
  | u :: us, c :: cs, s :: ss, w :: ws =>
    UtilityEnclosureHolds u c ∧
    c.side = s.side ∧
    c.submittedTotal = w.total ∧
    AllUtilityEnclosuresHold us cs ss ws
  | _, _, _, _ => False
/-- Pairwise `TaylorModel.Models` hypothesis across a trader curve list. -/
def AllTaylorModelsHold :
    List (Obend.Analysis.CanonicalRat → Obend.Analysis.CanonicalRat) →
    List TraderUtilityCert → Prop
  | [], [] => True
  | u :: us, c :: cs => Obend.Analysis.TaylorModel.Models u c.tm ∧ AllTaylorModelsHold us cs
  | _, _ => False
theorem checkUtilityBatch_sound
    (us : List (Obend.Analysis.CanonicalRat → Obend.Analysis.CanonicalRat))
    (certs : List TraderUtilityCert) (specs : List CommittedOrderSpec) (ws : List OrderBitWitness)
    (hModels : AllTaylorModelsHold us certs)
    (hBatch : checkUtilityBatch certs specs ws = true) :
    AllUtilityEnclosuresHold us certs specs ws := by
  induction us generalizing certs specs ws with
  | nil =>
    cases certs <;> cases specs <;> cases ws <;>
      simp [AllTaylorModelsHold, AllUtilityEnclosuresHold, checkUtilityBatch] at hModels hBatch ⊢
  | cons u us ih =>
    cases certs with
    | nil => simp [AllTaylorModelsHold] at hModels
    | cons c cs =>
      cases specs with
      | nil => simp [checkUtilityBatch] at hBatch
      | cons s ss =>
        cases ws with
        | nil => simp [checkUtilityBatch] at hBatch
        | cons w ws' =>
          simp only [AllTaylorModelsHold] at hModels
          simp only [checkUtilityBatch, Bool.and_eq_true, decide_eq_true_eq] at hBatch
          rcases hBatch with ⟨⟨⟨hEnc, hSide⟩, hTot⟩, hRest⟩
          exact ⟨checkUtilityEnclosure_sound c u hModels.1 hEnc,
                 hSide, hTot, ih cs ss ws' hModels.2 hRest⟩
theorem utilityBatch_inhabited (pp : AjtaiParams) (salt : GoldilocksExt2) :
    ∃ (u : Obend.Analysis.CanonicalRat → Obend.Analysis.CanonicalRat)
      (c : TraderUtilityCert) (s : CommittedOrderSpec) (w : OrderBitWitness),
      checkUtilityEnclosure c = true ∧
      AllTaylorModelsHold [u] [c] ∧
      checkUtilityBatch [c] [s] [w] = true := by
  let dom := Obend.Analysis.Interval.ofPoint 0
  let c : TraderUtilityCert := ⟨Obend.Analysis.tmConst 1 0 dom, 0, 1, .bid, 0⟩
  let w : OrderBitWitness := ⟨[], [], salt⟩
  let s : CommittedOrderSpec := commitPrivateOrder pp 1 .bid 8 salt w
  have hsSide : s.side = .bid := rfl
  have hwTot : w.total = 0 := rfl
  have hcEnc : checkUtilityEnclosure c = true := by decide +kernel
  refine ⟨fun _ => 1, c, s, w, hcEnc, ⟨Obend.Analysis.TaylorModel.const_models 1 0 dom, trivial⟩, ?_⟩
  simp [checkUtilityBatch, hcEnc, hsSide, hwTot, c]

/-! ## 2. Stage 2 — Exact Quantized `Sable` Inference (`FastRing` & `RangeSafe`) -/
/-- Exact unbounded integer quantized dot-product $b + \sum_{i=0}^{d-1} w_i x_i$ over `FastIntPoly d`. -/
@[expose] def sableDotInt {d : Nat} (w x : FastIntPoly d) (bias : Int) : Int :=
  bias + sumInt d (fun i => if hi : i < d then w.spec ⟨i, hi⟩ * x.spec ⟨i, hi⟩ else 0)
/-- Modular `Goldilocks` prefix sum $\sum_{i=0}^{n-1} f(i) \pmod p$. -/
def sumGoldilocks : Nat → (Nat → Goldilocks) → Goldilocks
  | 0, _ => Goldilocks.zero
  | n + 1, f => Goldilocks.add (sumGoldilocks n f) (f n)
/-- Modular `Goldilocks` witness evaluation of quantized `Sable` linear layer. -/
@[expose] def sableDotGoldilocks {d : Nat} (w x : FastIntPoly d) (bias : Int) : Goldilocks :=
  Goldilocks.add (goldOfInt bias)
    (sumGoldilocks d (fun i =>
      if hi : i < d then
        Goldilocks.mul (goldOfInt (w.spec ⟨i, hi⟩)) (goldOfInt (x.spec ⟨i, hi⟩))
      else Goldilocks.zero))
private theorem sumGoldilocks_goldOfInt (n : Nat) (f : Nat → Int) :
    sumGoldilocks n (fun i => goldOfInt (f i)) = goldOfInt (sumInt n f) := by
  induction n with
  | zero =>
    apply Goldilocks.ext
    rfl
  | succ n ih =>
    simp only [sumGoldilocks, sumInt, ih, goldOfInt_add]
theorem sableDotGoldilocks_eq_goldOfInt {d : Nat} (w x : FastIntPoly d) (bias : Int) :
    sableDotGoldilocks w x bias = goldOfInt (sableDotInt w x bias) := by
  unfold sableDotGoldilocks sableDotInt
  have hFn : (fun i =>
      if hi : i < d then
        Goldilocks.mul (goldOfInt (w.spec ⟨i, hi⟩)) (goldOfInt (x.spec ⟨i, hi⟩))
      else Goldilocks.zero) =
      (fun i => goldOfInt (if hi : i < d then w.spec ⟨i, hi⟩ * x.spec ⟨i, hi⟩ else 0)) := by
    funext i
    split
    · exact goldOfInt_mul _ _
    · apply Goldilocks.ext; rfl
  rw [hFn, sumGoldilocks_goldOfInt, goldOfInt_add]
theorem sableDotInt_natAbs_le {d : Nat} (w x : FastIntPoly d) (bias : Int) :
    (sableDotInt w x bias).natAbs ≤
      bias.natAbs + d * normInfFast w.coeffs * normInfFast x.coeffs := by
  unfold sableDotInt
  apply Nat.le_trans (Int.natAbs_add_le _ _)
  apply Nat.add_le_add_left
  rw [Nat.mul_assoc]
  apply sumInt_bound
  intro i hi
  simp only [hi, ↓reduceDIte, Int.natAbs_mul]
  exact Nat.mul_le_mul (coeff_le_norm w ⟨i, hi⟩) (coeff_le_norm x ⟨i, hi⟩)
/-- Decidable `Sable` no-wrap guard ensuring non-negative quantized inference strictly below `goldilocksPrime`. -/
def checkSableDotNoWrap {d : Nat} (w x : FastIntPoly d) (bias : Int) : Bool :=
  decide (0 ≤ sableDotInt w x bias) &&
  decide (bias.natAbs + d * normInfFast w.coeffs * normInfFast x.coeffs < goldilocksPrime)
/-- **`Sable` Quantized Dot-Product Exactness (`sableDot_goldilocks_exact_of_noWrap`)**:
    Under the `ℓ_∞` Cauchy–Schwarz norm bound `< goldilocksPrime`, modular `Goldilocks` witness
    evaluation equals the **exact** integer dot-product with zero modular wrap-around. -/
theorem sableDot_goldilocks_exact_of_noWrap {d : Nat} (w x : FastIntPoly d) (bias : Int)
    (hSafe : checkSableDotNoWrap w x bias = true) :
    0 ≤ sableDotInt w x bias ∧
    sableDotInt w x bias < (goldilocksPrime : Int) ∧
    ((sableDotGoldilocks w x bias).val : Int) = sableDotInt w x bias := by
  unfold checkSableDotNoWrap at hSafe
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSafe
  rcases hSafe with ⟨hNonneg, hNormLt⟩
  have hAbsLt : (sableDotInt w x bias).natAbs < goldilocksPrime :=
    Nat.lt_of_le_of_lt (sableDotInt_natAbs_le w x bias) hNormLt
  have hIntLt : sableDotInt w x bias < (goldilocksPrime : Int) := by
    omega
  refine ⟨hNonneg, hIntLt, ?_⟩
  rw [sableDotGoldilocks_eq_goldOfInt, goldOfInt_val]
  exact Int.emod_eq_of_lt hNonneg hIntLt
/-- Quantized `Sable` linear inference witness for one trader's private order limit total. -/
structure SableLinearWitness (d : Nat) where
  weights : FastIntPoly d
  features : FastIntPoly d
  bias : Int
  deriving DecidableEq
def checkSableBatch {d : Nat} : List (SableLinearWitness d) → List OrderBitWitness → Bool
  | [], [] => true
  | s :: ss, w :: ws =>
    checkSableDotNoWrap s.weights s.features s.bias &&
    decide ((sableDotGoldilocks s.weights s.features s.bias).val = w.total) &&
    checkSableBatch ss ws
  | _, _ => false
def AllSableInferencesExact {d : Nat} : List (SableLinearWitness d) → List OrderBitWitness → Prop
  | [], [] => True
  | s :: ss, w :: ws =>
    0 ≤ sableDotInt s.weights s.features s.bias ∧
    sableDotInt s.weights s.features s.bias < (goldilocksPrime : Int) ∧
    ((sableDotGoldilocks s.weights s.features s.bias).val : Int) =
      sableDotInt s.weights s.features s.bias ∧
    sableDotInt s.weights s.features s.bias = (w.total : Int) ∧
    AllSableInferencesExact ss ws
  | _, _ => False
theorem checkSableBatch_sound {d : Nat}
    (sables : List (SableLinearWitness d)) (ws : List OrderBitWitness)
    (hOk : checkSableBatch sables ws = true) :
    AllSableInferencesExact sables ws := by
  induction sables generalizing ws with
  | nil =>
    cases ws with
    | nil => trivial
    | cons _ _ => simp [checkSableBatch] at hOk
  | cons s ss ih =>
    cases ws with
    | nil => simp [checkSableBatch] at hOk
    | cons w ws' =>
      simp only [checkSableBatch, Bool.and_eq_true, decide_eq_true_eq] at hOk
      rcases hOk with ⟨⟨hNoWrap, hEqTot⟩, hRest⟩
      obtain ⟨hNonneg, hLt, hExact⟩ :=
        sableDot_goldilocks_exact_of_noWrap s.weights s.features s.bias hNoWrap
      have hTotInt : sableDotInt s.weights s.features s.bias = (w.total : Int) := by
        rw [← hExact, hEqTot]
      exact ⟨hNonneg, hLt, hExact, hTotInt, ih ws' hRest⟩
theorem sableBatch_inhabited (salt : GoldilocksExt2) :
    ∃ (s : SableLinearWitness 1) (w : OrderBitWitness),
      checkSableBatch [s] [w] = true := by
  let s : SableLinearWitness 1 := ⟨zeroVec 1, zeroVec 1, 0⟩
  let w : OrderBitWitness := ⟨[], [], salt⟩
  have hNoWrap : checkSableDotNoWrap s.weights s.features s.bias = true := by decide
  have hVal : (sableDotGoldilocks s.weights s.features s.bias).val = 0 := by decide
  have hwTot : w.total = 0 := rfl
  exact ⟨s, w, by simp [checkSableBatch, hNoWrap, hVal, hwTot]⟩
/-- Direct bridge to `Obend.Core.RangeSafe` (`evaluates_goldilocks_exact_of_rangeSafe`) for arbitrary
    Core4 quantized `Sable` terms compiled into `Goldilocks` arithmetic circuits. -/
theorem sableCoreTerm_goldilocks_exact
    (Γ : List Obend.Core.RangeSafe.Interval)
    (env : List Obend.Core.Term.Term) (modVals : List Nat) (t : Obend.Core.Term.Term)
    (hSafe : Obend.Core.RangeSafe.checkRangeSafeMod goldilocksPrime Γ t = true)
    (hAgree : Obend.Core.RangeSafe.ModEnvAgrees goldilocksPrime Γ env modVals) :
    ∃ (I : Obend.Core.RangeSafe.Interval) (v : Obend.Core.Term.Term),
      Obend.Core.RangeSafe.inferRange Γ t = some I ∧
      Obend.Core.Term.Evaluates (Obend.Core.RangeSafe.closeTerm env t) v ∧
      Obend.Core.RangeSafe.ValueInInterval I v ∧
      Obend.Core.RangeSafe.scalarToNat v < goldilocksPrime ∧
      Obend.Core.RangeSafe.evalMod goldilocksPrime modVals t =
        some (Obend.Core.RangeSafe.scalarToNat v) :=
  Obend.Core.RangeSafe.evaluates_goldilocks_exact_of_rangeSafe Γ env modVals t hSafe hAgree

/-! ## 3. Stage 3 — Additive/Scalar RLWE Order Book Aggregation (`FastRing`) -/
/-- Cyclotomic RLWE parameter bundle over $R_q = \mathbb{Z}_q[X]/(X^d + 1)$ with even plaintext modulus
    $t = 2h$ and exact scaling factor $\Delta = q / t = 2 B$ ($B = \lfloor q / (2t) \rfloor$). -/
structure RlweParams where
  d : Nat
  q : Nat
  t : Nat
  deriving DecidableEq, Repr
/-- Parameter well-formedness: positive ring degree `d`, even plaintext modulus `t ≥ 2`, and exact
    even scaling $q = 2 t B$ with positive noise cap $B = q / (2t) \ge 1$. -/
def RlweParams.wfB (pp : RlweParams) : Bool :=
  decide (0 < pp.d) &&
  decide (2 ≤ pp.t) &&
  decide (pp.t % 2 = 0) &&
  decide (2 * pp.t ≤ pp.q) &&
  decide (pp.q % (2 * pp.t) = 0)
def RlweParams.delta (pp : RlweParams) : Int := (pp.q / pp.t : Nat)
def RlweParams.noiseCap (pp : RlweParams) : Nat := pp.q / (2 * pp.t)
def RlweParams.halfT (pp : RlweParams) : Int := (pp.t / 2 : Nat)
private theorem rlweParams_identities (pp : RlweParams) (hwf : pp.wfB = true) :
    0 < pp.d ∧ 2 ≤ pp.t ∧ pp.t % 2 = 0 ∧ 0 < pp.noiseCap ∧
    (pp.q : Int) = 2 * (pp.t : Int) * (pp.noiseCap : Int) ∧
    pp.delta = 2 * (pp.noiseCap : Int) ∧
    (pp.t : Int) = 2 * pp.halfT := by
  unfold RlweParams.wfB at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  rcases hwf with ⟨⟨⟨⟨hd, ht2⟩, htEven⟩, hqGe⟩, hqMod⟩
  unfold RlweParams.noiseCap RlweParams.delta RlweParams.halfT
  have hBPos : 0 < pp.q / (2 * pp.t) := Nat.div_pos hqGe (by omega)
  have hqEqNat : pp.q = (2 * pp.t) * (pp.q / (2 * pp.t)) := by
    have h := Nat.div_add_mod pp.q (2 * pp.t)
    omega
  have hDeltaNat : pp.q / pp.t = 2 * (pp.q / (2 * pp.t)) := by
    have hq2 : pp.q = pp.t * (2 * (pp.q / (2 * pp.t))) := by
      calc pp.q = (2 * pp.t) * (pp.q / (2 * pp.t)) := hqEqNat
      _ = pp.t * (2 * (pp.q / (2 * pp.t))) := by
        rw [Nat.mul_comm 2 pp.t, Nat.mul_assoc]
    conv => lhs; rw [hq2]
    exact Nat.mul_div_right _ (by omega)
  have htNat : pp.t = 2 * (pp.t / 2) := by
    have h := Nat.div_add_mod pp.t 2
    omega
  refine ⟨hd, ht2, htEven, hBPos, ?_, ?_, ?_⟩
  · have hCast : (pp.q : Int) = (((2 * pp.t) * (pp.q / (2 * pp.t)) : Nat) : Int) :=
      congrArg Int.ofNat hqEqNat
    simpa [Int.natCast_mul, Int.mul_assoc] using hCast
  · exact_mod_cast hDeltaNat
  · exact_mod_cast htNat
/-- Reduce every coefficient of `a : FastIntPoly d` canonically into `[0, q)`. -/
def reducePolyMod {d : Nat} (q : Nat) (a : FastIntPoly d) : FastIntPoly d :=
  Sized.ofFn fun i => a.spec i % (q : Int)
@[simp] theorem reducePolyMod_spec {d : Nat} (q : Nat) (a : FastIntPoly d) (i : Fin d) :
    (reducePolyMod q a).spec i = a.spec i % (q : Int) := by
  simp [reducePolyMod]
def checkCanonicalModPoly {d : Nat} (q : Nat) (a : FastIntPoly d) : Bool :=
  (List.finRange d).all fun i => decide (0 ≤ a.spec i ∧ a.spec i < (q : Int))
theorem checkCanonicalModPoly_iff {d : Nat} (q : Nat) (a : FastIntPoly d) :
    checkCanonicalModPoly q a = true ↔
      ∀ i : Fin d, 0 ≤ a.spec i ∧ a.spec i < (q : Int) := by
  simp [checkCanonicalModPoly, List.all_eq_true, List.mem_finRange]
/-- RLWE ciphertext $(c_0, c_1) \in R_q^2$ encrypting a signed order polynomial $m \in R_t$. -/
structure RlweCiphertext (d : Nat) where
  c0 : FastIntPoly d
  c1 : FastIntPoly d
  deriving DecidableEq
/-- Symmetric RLWE encryption $c_0 = (-s \cdot a + \Delta \cdot m + e) \bmod q$, $c_1 = a \bmod q$. -/
@[expose] def rlweEncrypt (pp : RlweParams) (sk a m e : FastIntPoly pp.d) : RlweCiphertext pp.d :=
  let c1 := reducePolyMod pp.q a
  let sa := negacyclicMulFast sk c1
  let body := intAdd (intSub (intScale pp.delta m) sa) e
  { c0 := reducePolyMod pp.q body, c1 := c1 }
/-- Homomorphic RLWE ciphertext addition $(c_0^{(1)} + c_0^{(2)}, c_1^{(1)} + c_1^{(2)}) \bmod q$. -/
@[expose] def rlweAdd (pp : RlweParams) (ct1 ct2 : RlweCiphertext pp.d) : RlweCiphertext pp.d :=
  { c0 := reducePolyMod pp.q (intAdd ct1.c0 ct2.c0)
    c1 := reducePolyMod pp.q (intAdd ct1.c1 ct2.c1) }
/-- Homomorphic scalar multiplication $(k \cdot c_0, k \cdot c_1) \bmod q$. -/
def rlweScale (pp : RlweParams) (k : Int) (ct : RlweCiphertext pp.d) : RlweCiphertext pp.d :=
  { c0 := reducePolyMod pp.q (intScale k ct.c0)
    c1 := reducePolyMod pp.q (intScale k ct.c1) }
/-- Zero ciphertext $(0, 0) \in R_q^2$. -/
def rlweZero (pp : RlweParams) : RlweCiphertext pp.d :=
  { c0 := zeroVec pp.d, c1 := zeroVec pp.d }
/-- Homomorphic batch aggregation of a list of encrypted trader order vectors. -/
def rlweAggregateBatch (pp : RlweParams) : List (RlweCiphertext pp.d) → RlweCiphertext pp.d
  | [] => rlweZero pp
  | ct :: cts => rlweAdd pp ct (rlweAggregateBatch pp cts)
/-- Aggregate plaintext order vectors in $\mathbb{Z}^d$. -/
def sumPlainBatch (d : Nat) : List (FastIntPoly d) → FastIntPoly d
  | [] => zeroVec d
  | m :: ms => intAdd m (sumPlainBatch d ms)
/-- Decode one noisy phase residue $\phi \in \mathbb{Z}_q$ into a signed coefficient in $[-t/2, t/2)$. -/
def rlweDecodeSignedCoeff (pp : RlweParams) (phi : Int) : Int :=
  let B : Int := pp.noiseCap
  let u : Int := ((phi + B) % (pp.q : Int)) / pp.delta
  if u < pp.halfT then u else u - (pp.t : Int)
/-- Secret-key RLWE decryption: compute phase $\phi = (c_0 + s \cdot c_1) \bmod q$ and round+center. -/
@[expose] def rlweDecrypt (pp : RlweParams) (sk : FastIntPoly pp.d)
    (ct : RlweCiphertext pp.d) : FastIntPoly pp.d :=
  let phase := reducePolyMod pp.q (intAdd ct.c0 (negacyclicMulFast sk ct.c1))
  Sized.ofFn fun i => rlweDecodeSignedCoeff pp (phase.spec i)
/-- Phase invariant: $(c_0 + s \cdot c_1) \equiv \Delta \cdot m + e \pmod q$ coefficient-wise. -/
def RlweEncryptsWithError (pp : RlweParams) (sk : FastIntPoly pp.d)
    (ct : RlweCiphertext pp.d) (m e : FastIntPoly pp.d) : Prop :=
  ∀ i : Fin pp.d,
    (ct.c0.spec i + (negacyclicMulFast sk ct.c1).spec i) % (pp.q : Int) =
      (pp.delta * m.spec i + e.spec i) % (pp.q : Int)
private theorem neg_mod_congr_int (a b q : Int) (h : a % q = b % q) : -a % q = -b % q := by
  have hh := congrArg (fun r : Int => (0 % q - r) % q) h
  rw [← Int.sub_emod, ← Int.sub_emod] at hh
  simpa only [Int.zero_sub] using hh
private theorem sumInt_zero_const (n : Nat) : sumInt n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => simp [sumInt, ih]
private theorem negacyclicSpec_mod_right {d : Nat} (q : Int) (s a b : IntCycloSpec d)
    (h : ∀ j : Fin d, a j % q = b j % q) (k : Fin d) :
    negacyclicSpec s a k % q = negacyclicSpec s b k % q := by
  unfold negacyclicSpec
  conv => lhs; rw [← sumInt_mod]
  conv => rhs; rw [← sumInt_mod]
  congr 1
  apply sumInt_congr
  intro i hi
  simp only [hi, ↓reduceDIte, wrapSign]
  let idx : Fin d := ⟨(k.val + d - i) % d, Nat.mod_lt _ (by omega)⟩
  have hMulCong : (s ⟨i, hi⟩ * a idx) % q = (s ⟨i, hi⟩ * b idx) % q := by
    rw [Int.mul_emod, h idx, ← Int.mul_emod]
  split
  · exact hMulCong
  · exact neg_mod_congr_int _ _ _ hMulCong
private theorem negacyclicSpec_zero_right {d : Nat} (s : IntCycloSpec d) (k : Fin d) :
    negacyclicSpec s (fun _ => 0) k = 0 := by
  unfold negacyclicSpec
  conv => rhs; rw [← sumInt_zero_const d]
  apply sumInt_congr
  intro i hi
  simp [hi, wrapSign]
private theorem negacyclicSpec_scale_right {d : Nat} (kScalar : Int) (s a : IntCycloSpec d) (idx : Fin d) :
    negacyclicSpec s (fun j => kScalar * a j) idx = kScalar * negacyclicSpec s a idx := by
  unfold negacyclicSpec
  rw [← sumInt_mul]
  apply sumInt_congr
  intro i hi
  simp only [hi, ↓reduceDIte, wrapSign]
  let bIdx : Fin d := ⟨(idx.val + d - i) % d, Nat.mod_lt _ (by omega)⟩
  have hMul : s ⟨i, hi⟩ * (kScalar * a bIdx) = kScalar * (s ⟨i, hi⟩ * a bIdx) := by
    rw [← Int.mul_assoc, Int.mul_comm (s ⟨i, hi⟩) kScalar, Int.mul_assoc]
  rw [hMul]
  split
  · rfl
  · exact (Int.mul_neg kScalar _).symm
theorem rlweEncrypt_encryptsWithError (pp : RlweParams) (sk a m e : FastIntPoly pp.d) :
    RlweEncryptsWithError pp sk (rlweEncrypt pp sk a m e) m e := by
  intro i
  unfold rlweEncrypt
  dsimp only
  rw [reducePolyMod_spec]
  simp only [addFast_eq_spec, subFast_eq_spec, scaleFast_eq_spec]
  rw [Int.emod_add_emod]
  congr 1
  omega
theorem rlweAdd_encrypts_sum (pp : RlweParams) (sk : FastIntPoly pp.d)
    (ct1 ct2 : RlweCiphertext pp.d) (m1 e1 m2 e2 : FastIntPoly pp.d)
    (h1 : RlweEncryptsWithError pp sk ct1 m1 e1)
    (h2 : RlweEncryptsWithError pp sk ct2 m2 e2) :
    RlweEncryptsWithError pp sk (rlweAdd pp ct1 ct2) (intAdd m1 m2) (intAdd e1 e2) := by
  intro i
  unfold rlweAdd
  dsimp only
  rw [reducePolyMod_spec, addFast_eq_spec]
  have hMulMod : (negacyclicMulFast sk (reducePolyMod pp.q (intAdd ct1.c1 ct2.c1))).spec i % (pp.q : Int) =
      ((negacyclicMulFast sk ct1.c1).spec i + (negacyclicMulFast sk ct2.c1).spec i) % (pp.q : Int) := by
    rw [negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec]
    have hRed := negacyclicSpec_mod_right (pp.q : Int) sk.spec
      (reducePolyMod pp.q (intAdd ct1.c1 ct2.c1)).spec (intAdd ct1.c1 ct2.c1).spec
      (fun j => by rw [reducePolyMod_spec, Int.emod_emod]) i
    rw [hRed, addFast_eq_spec, negacyclicMul_left_distrib]
  rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
  rw [Int.add_emod, hMulMod, ← Int.add_emod]
  have hRearr : ct1.c0.spec i + ct2.c0.spec i +
      ((negacyclicMulFast sk ct1.c1).spec i + (negacyclicMulFast sk ct2.c1).spec i) =
      (ct1.c0.spec i + (negacyclicMulFast sk ct1.c1).spec i) +
      (ct2.c0.spec i + (negacyclicMulFast sk ct2.c1).spec i) := by omega
  rw [hRearr, Int.add_emod, h1 i, h2 i, ← Int.add_emod]
  simp only [addFast_eq_spec, Int.mul_add]
  congr 1
  omega
theorem rlweScale_encrypts_scaled (pp : RlweParams) (k : Int) (sk : FastIntPoly pp.d)
    (ct : RlweCiphertext pp.d) (m e : FastIntPoly pp.d)
    (h : RlweEncryptsWithError pp sk ct m e) :
    RlweEncryptsWithError pp sk (rlweScale pp k ct) (intScale k m) (intScale k e) := by
  intro i
  unfold rlweScale
  dsimp only
  rw [reducePolyMod_spec, scaleFast_eq_spec]
  have hMulMod : (negacyclicMulFast sk (reducePolyMod pp.q (intScale k ct.c1))).spec i % (pp.q : Int) =
      (k * (negacyclicMulFast sk ct.c1).spec i) % (pp.q : Int) := by
    rw [negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec]
    have hRed := negacyclicSpec_mod_right (pp.q : Int) sk.spec
      (reducePolyMod pp.q (intScale k ct.c1)).spec (intScale k ct.c1).spec
      (fun j => by rw [reducePolyMod_spec, Int.emod_emod]) i
    rw [hRed, scaleFast_eq_spec, negacyclicSpec_scale_right]
  rw [Int.add_emod, Int.emod_emod, ← Int.add_emod, Int.add_emod, hMulMod, ← Int.add_emod]
  rw [← Int.mul_add, Int.mul_emod, h i, ← Int.mul_emod]
  simp only [scaleFast_eq_spec, Int.mul_add]
  have hAssoc : pp.delta * (k * m.spec i) = k * (pp.delta * m.spec i) := by
    rw [← Int.mul_assoc, Int.mul_comm pp.delta k, Int.mul_assoc]
  rw [hAssoc]
theorem rlweZero_encrypts_zero (pp : RlweParams) (sk : FastIntPoly pp.d) :
    RlweEncryptsWithError pp sk (rlweZero pp) (zeroVec pp.d) (zeroVec pp.d) := by
  intro i
  unfold rlweZero
  dsimp only
  rw [negacyclicMulFast_eq_spec]
  have hz : (zeroVec pp.d).spec = fun _ => (0 : Int) := Sized.spec_ofFn _
  rw [hz, negacyclicSpec_zero_right]
  simp
/-- Exact rounding & signed centering theorem: whenever $-t/2 \le m < t/2$ and $|e| < \lfloor q / (2t) \rfloor$,
    `rlweDecodeSignedCoeff` recovers `m` **exactly** from any $\phi \equiv \Delta \cdot m + e \pmod q$. -/
theorem rlweDecodeSignedCoeff_exact (pp : RlweParams) (phi m e : Int)
    (hwf : pp.wfB = true)
    (hCong : phi % (pp.q : Int) = (pp.delta * m + e) % (pp.q : Int))
    (hmLo : -pp.halfT ≤ m) (hmHi : m < pp.halfT)
    (heLt : e.natAbs < pp.noiseCap) :
    rlweDecodeSignedCoeff pp phi = m := by
  obtain ⟨_, _, _, hBPos, hqEq, hDeltaEq, htEq⟩ := rlweParams_identities pp hwf
  unfold rlweDecodeSignedCoeff
  dsimp only
  let B : Int := pp.noiseCap
  have hBIntPos : 0 < B := Int.ofNat_lt.2 hBPos
  have htPos : 0 < (pp.t : Int) := by omega
  have hqPos : 0 < (pp.q : Int) := by
    rw [hqEq]
    exact Int.mul_pos (by omega) hBIntPos
  have heBounds : -B < e ∧ e < B := by omega
  let u : Int := m % (pp.t : Int)
  have huNonneg : 0 ≤ u := Int.emod_nonneg m (by omega)
  have huLtT : u < (pp.t : Int) := Int.emod_lt_of_pos m htPos
  have hmDecomp : m = (pp.t : Int) * (m / (pp.t : Int)) + u := by
    have h := Int.emod_def m (pp.t : Int)
    dsimp only [u]
    omega
  have hDeltaMul : pp.delta * m = (pp.q : Int) * (m / (pp.t : Int)) + pp.delta * u := by
    conv => lhs; rw [hmDecomp]
    rw [Int.mul_add, ← Int.mul_assoc, hDeltaEq]
    have hqComm : 2 * B * (pp.t : Int) = (pp.q : Int) := by
      rw [hqEq]
      have hc : 2 * B * (pp.t : Int) = 2 * (pp.t : Int) * B := by
        rw [Int.mul_assoc, Int.mul_comm B (pp.t : Int), ← Int.mul_assoc]
      exact hc
    rw [hqComm]
  have hPhiMod : (phi + B) % (pp.q : Int) = 2 * B * u + (e + B) := by
    rw [Int.add_emod, hCong, ← Int.add_emod]
    have hShift : pp.delta * m + e + B = (pp.delta * u + (e + B)) + (pp.q : Int) * (m / (pp.t : Int)) := by
      rw [hDeltaMul]; omega
    rw [hShift, Int.add_mul_emod_self_left, hDeltaEq]
    have hNonnegVal : 0 ≤ 2 * B * u + (e + B) := by
      have h2Bu : 0 ≤ 2 * B * u := Int.mul_nonneg (by omega) huNonneg
      omega
    have hUpperVal : 2 * B * u + (e + B) < (pp.q : Int) := by
      have huLe : u ≤ (pp.t : Int) - 1 := by omega
      have hMulLe : 2 * B * u ≤ 2 * B * ((pp.t : Int) - 1) :=
        Int.mul_le_mul_of_nonneg_left huLe (by omega)
      have hExpand : 2 * B * ((pp.t : Int) - 1) = (pp.q : Int) - 2 * B := by
        rw [Int.mul_sub, Int.mul_one, hqEq]
        have hc : 2 * B * (pp.t : Int) = 2 * (pp.t : Int) * B := by
          rw [Int.mul_assoc, Int.mul_comm B (pp.t : Int), ← Int.mul_assoc]
        rw [hc]
      omega
    exact Int.emod_eq_of_lt hNonnegVal hUpperVal
  have hDivU : (2 * B * u + (e + B)) / pp.delta = u := by
    rw [hDeltaEq]
    have hComm : 2 * B * u + (e + B) = (e + B) + (2 * B) * u := by omega
    rw [hComm, Int.add_mul_ediv_left _ _ (by omega)]
    have hSmallDiv : (e + B) / (2 * B) = 0 :=
      Int.ediv_eq_zero_of_lt (by omega) (by omega)
    omega
  rw [hPhiMod, hDivU]
  if hmNonneg : 0 ≤ m then
    have huEqM : u = m := Int.emod_eq_of_lt hmNonneg (by omega)
    rw [huEqM]; split <;> omega
  else
    have hmPlusNonneg : 0 ≤ m + (pp.t : Int) := by omega
    have hmPlusLt : m + (pp.t : Int) < (pp.t : Int) := by omega
    have huEqMPlus : u = m + (pp.t : Int) := by
      change m % (pp.t : Int) = m + (pp.t : Int)
      rw [← Int.add_emod_right m (pp.t : Int)]
      exact Int.emod_eq_of_lt hmPlusNonneg hmPlusLt
    rw [huEqMPlus]; split <;> omega
/-- Signed plaintext range predicate: every coefficient lies in $[-t/2, t/2)$. -/
def SignedPlainInRange (pp : RlweParams) (m : FastIntPoly pp.d) : Prop :=
  ∀ i : Fin pp.d, -pp.halfT ≤ m.spec i ∧ m.spec i < pp.halfT
/-- **Homomorphic RLWE Addition Exactness (`rlweAdd_decrypts_to_sum`)**:
    When $(c_0^{(1)}, c_1^{(1)})$ encrypts $m_1$ with noise $e_1$ and $(c_0^{(2)}, c_1^{(2)})$
    encrypts $m_2$ with noise $e_2$, and the cumulative noise satisfies
    $\|e_1 + e_2\|_\infty < \lfloor q / (2t) \rfloor$, decrypting `rlweAdd pp ct1 ct2`
    recovers `intAdd m1 m2` **identically**. -/
theorem rlweAdd_decrypts_to_sum (pp : RlweParams) (sk : FastIntPoly pp.d)
    (ct1 ct2 : RlweCiphertext pp.d) (m1 e1 m2 e2 : FastIntPoly pp.d)
    (hwf : pp.wfB = true)
    (h1 : RlweEncryptsWithError pp sk ct1 m1 e1)
    (h2 : RlweEncryptsWithError pp sk ct2 m2 e2)
    (hmSum : SignedPlainInRange pp (intAdd m1 m2))
    (hNoise : normInfFast (intAdd e1 e2).coeffs < pp.noiseCap) :
    rlweDecrypt pp sk (rlweAdd pp ct1 ct2) = intAdd m1 m2 := by
  have hEncSum := rlweAdd_encrypts_sum pp sk ct1 ct2 m1 e1 m2 e2 h1 h2
  apply Sized.ext
  funext i
  unfold rlweDecrypt
  simp only [Sized.spec_ofFn, reducePolyMod_spec, addFast_eq_spec]
  have hPhiCong :
      ((rlweAdd pp ct1 ct2).c0.spec i + (negacyclicMulFast sk (rlweAdd pp ct1 ct2).c1).spec i) %
        (pp.q : Int) % (pp.q : Int) =
      (pp.delta * (m1.spec i + m2.spec i) + (e1.spec i + e2.spec i)) % (pp.q : Int) := by
    rw [Int.emod_emod]
    simpa [addFast_eq_spec] using hEncSum i
  have heCoeffLt : (e1.spec i + e2.spec i).natAbs < pp.noiseCap := by
    have hLe := coeff_le_norm (intAdd e1 e2) i
    simpa [addFast_eq_spec] using Nat.lt_of_le_of_lt hLe hNoise
  obtain ⟨hmLo, hmHi⟩ := hmSum i
  simp only [addFast_eq_spec] at hmLo hmHi
  exact rlweDecodeSignedCoeff_exact pp _ (m1.spec i + m2.spec i) (e1.spec i + e2.spec i)
    hwf hPhiCong hmLo hmHi heCoeffLt
/-- Pairwise encryption witness across a batch of trader RLWE ciphertexts. -/
def BatchEncryptsWithErrors (pp : RlweParams) (sk : FastIntPoly pp.d) :
    List (RlweCiphertext pp.d) → List (FastIntPoly pp.d) → List (FastIntPoly pp.d) → Prop
  | [], [], [] => True
  | ct :: cts, m :: ms, e :: es =>
    RlweEncryptsWithError pp sk ct m e ∧ BatchEncryptsWithErrors pp sk cts ms es
  | _, _, _ => False
theorem rlweAggregateBatch_encrypts_sum (pp : RlweParams) (sk : FastIntPoly pp.d)
    (cts : List (RlweCiphertext pp.d)) (ms es : List (FastIntPoly pp.d))
    (hBatch : BatchEncryptsWithErrors pp sk cts ms es) :
    RlweEncryptsWithError pp sk (rlweAggregateBatch pp cts)
      (sumPlainBatch pp.d ms) (sumPlainBatch pp.d es) := by
  induction cts generalizing ms es with
  | nil =>
    cases ms <;> cases es <;> try (simp [BatchEncryptsWithErrors] at hBatch; done)
    exact rlweZero_encrypts_zero pp sk
  | cons ct cts ih =>
    cases ms with
    | nil => simp [BatchEncryptsWithErrors] at hBatch
    | cons m ms' =>
      cases es with
      | nil => simp [BatchEncryptsWithErrors] at hBatch
      | cons e es' =>
        exact rlweAdd_encrypts_sum pp sk ct (rlweAggregateBatch pp cts)
          m e (sumPlainBatch pp.d ms') (sumPlainBatch pp.d es')
          hBatch.1 (ih ms' es' hBatch.2)

/-! ## 4. Stage 4 — Threshold Decryption with Smudging NoiseBound & Refusals -/
/-- Partial decryption share $d_j = (s_j \cdot c_1 + e_{\text{smudge},j}) \bmod q$ from guardian `guardianId`. -/
structure PartialDecryptionShare (d : Nat) where
  guardianId : Nat
  sharePoly : FastIntPoly d
  deriving DecidableEq
/-- Honest guardian partial decryption share generation with explicit drowning noise `eSmudge`. -/
@[expose] def computePartialShare (pp : RlweParams) (guardianId : Nat)
    (skShare c1 eSmudge : FastIntPoly pp.d) : PartialDecryptionShare pp.d :=
  { guardianId := guardianId
    sharePoly := reducePolyMod pp.q (intAdd (negacyclicMulFast skShare c1) eSmudge) }
theorem computePartialShare_canonical (pp : RlweParams) (hwf : pp.wfB = true)
    (guardianId : Nat) (skShare c1 eSmudge : FastIntPoly pp.d) :
    checkCanonicalModPoly pp.q (computePartialShare pp guardianId skShare c1 eSmudge).sharePoly = true := by
  obtain ⟨_, _, _, hBPos, hqEq, _, _⟩ := rlweParams_identities pp hwf
  have hqPos : 0 < (pp.q : Int) := by
    rw [hqEq]
    exact Int.mul_pos (by omega) (by exact_mod_cast hBPos)
  apply (checkCanonicalModPoly_iff _ _).2
  intro i
  unfold computePartialShare
  simp only [reducePolyMod_spec]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hqPos⟩
/-- Threshold decryption configuration enforcing `SmudgeSafe`, quorum, and total noise budget. -/
structure ThresholdDecryptConfig where
  params : RlweParams
  quorum : Nat
  encNoiseBound : Nat
  smudgeBound : Nat
  secBits : Nat
  deriving DecidableEq, Repr
/-- Deterministic refusal reasons for collective threshold RLWE decryption. -/
inductive ThresholdRefusal where
  | invalidRlweParams
  | unsmudgedThresholdNoise
  | insufficientQuorum (got required : Nat)
  | duplicateGuardian (guardianId : Nat)
  | nonCanonicalShare (guardianId : Nat)
  | noiseBudgetExceeded (totalNoiseBound cap : Nat)
  deriving DecidableEq, Repr
def firstDupNat? : List Nat → Option Nat
  | [] => none
  | x :: xs => if xs.any (· == x) then some x else firstDupNat? xs
theorem firstDupNat?_none_iff (xs : List Nat) :
    firstDupNat? xs = none ↔ xs.Nodup := by
  induction xs with
  | nil => simp [firstDupNat?]
  | cons x xs ih =>
    simp only [firstDupNat?, List.nodup_cons]
    constructor
    · intro h
      split at h
      · cases h
      · rename_i hAny
        refine ⟨?_, ih.1 h⟩
        intro hMem
        apply hAny
        exact List.any_eq_true.2 ⟨x, hMem, beq_self_eq_true x⟩
    · rintro ⟨hNotMem, hNd⟩
      split
      · rename_i hAny
        obtain ⟨y, hyMem, hyEq⟩ := List.any_eq_true.1 hAny
        have hxy : y = x := eq_of_beq hyEq
        subst hxy
        exact absurd hyMem hNotMem
      · exact ih.2 hNd
def findNonCanonicalShare? {d : Nat} (q : Nat) :
    List (PartialDecryptionShare d) → Option Nat
  | [] => none
  | sh :: rest =>
    if !checkCanonicalModPoly q sh.sharePoly then some sh.guardianId
    else findNonCanonicalShare? q rest
def combineSharePolys (pp : RlweParams) : List (PartialDecryptionShare pp.d) → FastIntPoly pp.d
  | [] => zeroVec pp.d
  | sh :: rest => reducePolyMod pp.q (intAdd sh.sharePoly (combineSharePolys pp rest))
/-- **Checked Threshold RLWE Decryption (`thresholdDecryptChecked`)**:
    Verifies parameter well-formedness, `SmudgeSafe` ($2^{40}$ drowning defense), `quorum` count,
    distinct guardian IDs, canonical `[0, q)` share bounds, and strict decryption noise budget
    `encNoiseBound + shares.length * smudgeBound < pp.noiseCap`, then reconstructs `m`. -/
@[expose] def thresholdDecryptChecked (cfg : ThresholdDecryptConfig)
    (ct : RlweCiphertext cfg.params.d)
    (shares : List (PartialDecryptionShare cfg.params.d)) :
    Except ThresholdRefusal (FastIntPoly cfg.params.d) :=
  if !cfg.params.wfB then
    .error .invalidRlweParams
  else if !checkSmudgeSafe cfg.encNoiseBound cfg.smudgeBound cfg.secBits then
    .error .unsmudgedThresholdNoise
  else if shares.length < cfg.quorum || cfg.quorum == 0 then
    .error (.insufficientQuorum shares.length cfg.quorum)
  else
    match firstDupNat? (shares.map (·.guardianId)) with
    | some gid => .error (.duplicateGuardian gid)
    | none =>
      match findNonCanonicalShare? cfg.params.q shares with
      | some gid => .error (.nonCanonicalShare gid)
      | none =>
        let totalBound := cfg.encNoiseBound + shares.length * cfg.smudgeBound
        if !(decide (totalBound < cfg.params.noiseCap)) then
          .error (.noiseBudgetExceeded totalBound cfg.params.noiseCap)
        else
          let combined := combineSharePolys cfg.params shares
          let phase := reducePolyMod cfg.params.q (intAdd ct.c0 combined)
          .ok (Sized.ofFn fun i => rlweDecodeSignedCoeff cfg.params (phase.spec i))
/-- Relational witness that `shares` were honestly generated from key shares `skShares` and
    bounded smudging noises `smudgeNoises` ($\|e_{\text{smudge},j}\|_\infty \le B_{\text{smudge}}$). -/
def ValidThresholdShares (pp : RlweParams) (c1 : FastIntPoly pp.d) (smudgeBound : Nat) :
    List (PartialDecryptionShare pp.d) → List (FastIntPoly pp.d) → List (FastIntPoly pp.d) → Prop
  | [], [], [] => True
  | sh :: shs, sk :: sks, es :: ess =>
    (∀ i : Fin pp.d,
      sh.sharePoly.spec i % (pp.q : Int) =
        ((negacyclicMulFast sk c1).spec i + es.spec i) % (pp.q : Int)) ∧
    normInfFast es.coeffs ≤ smudgeBound ∧
    ValidThresholdShares pp c1 smudgeBound shs sks ess
  | _, _, _ => False
private theorem negacyclicSpec_add_left {d : Nat} (s1 s2 a : IntCycloSpec d) (k : Fin d) :
    negacyclicSpec (fun i => s1 i + s2 i) a k =
      negacyclicSpec s1 a k + negacyclicSpec s2 a k := by
  unfold negacyclicSpec
  rw [← sumInt_add]
  apply sumInt_congr
  intro i hi
  simp only [hi, ↓reduceDIte, Int.add_mul, wrapSign]
  split <;> omega
private theorem negacyclicSpec_zero_left {d : Nat} (a : IntCycloSpec d) (k : Fin d) :
    negacyclicSpec (fun _ => 0) a k = 0 := by
  unfold negacyclicSpec
  conv => rhs; rw [← sumInt_zero_const d]
  apply sumInt_congr
  intro i hi
  simp [hi, wrapSign]
private theorem combineSharePolys_phase_mod (pp : RlweParams) (c1 : FastIntPoly pp.d)
    (smudgeBound : Nat)
    (shares : List (PartialDecryptionShare pp.d))
    (skShares smudgeNoises : List (FastIntPoly pp.d))
    (hValid : ValidThresholdShares pp c1 smudgeBound shares skShares smudgeNoises) :
    (∀ i : Fin pp.d,
      (combineSharePolys pp shares).spec i % (pp.q : Int) =
        ((negacyclicMulFast (sumPlainBatch pp.d skShares) c1).spec i +
         (sumPlainBatch pp.d smudgeNoises).spec i) % (pp.q : Int)) ∧
    normInfFast (sumPlainBatch pp.d smudgeNoises).coeffs ≤ shares.length * smudgeBound := by
  induction shares generalizing skShares smudgeNoises with
  | nil =>
    cases skShares <;> cases smudgeNoises <;> try (simp [ValidThresholdShares] at hValid; done)
    refine ⟨fun i => ?_, ?_⟩
    · simp only [combineSharePolys, sumPlainBatch, negacyclicMulFast_eq_spec]
      have hz : (zeroVec pp.d).spec = fun _ => (0 : Int) := Sized.spec_ofFn _
      rw [hz, negacyclicSpec_zero_left]
      simp
    · simpa [sumPlainBatch] using norm_le (zeroVec pp.d) 0 (fun _ => by simp [zeroVec])
  | cons sh shs ih =>
    cases skShares with
    | nil => simp [ValidThresholdShares] at hValid
    | cons sk sks =>
      cases smudgeNoises with
      | nil => simp [ValidThresholdShares] at hValid
      | cons es ess =>
        rcases hValid with ⟨hShMod, hEsNorm, hRest⟩
        obtain ⟨ihMod, ihNorm⟩ := ih sks ess hRest
        refine ⟨fun i => ?_, ?_⟩
        · simp only [combineSharePolys, sumPlainBatch, reducePolyMod_spec, addFast_eq_spec]
          rw [Int.emod_emod, Int.add_emod, hShMod i, ihMod i, ← Int.add_emod]
          have hSkAdd : (negacyclicMulFast (intAdd sk (sumPlainBatch pp.d sks)) c1).spec i =
              (negacyclicMulFast sk c1).spec i +
              (negacyclicMulFast (sumPlainBatch pp.d sks) c1).spec i := by
            rw [negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec, negacyclicMulFast_eq_spec,
                addFast_eq_spec, negacyclicSpec_add_left]
          rw [hSkAdd]
          congr 1
          omega
        · simp only [sumPlainBatch, List.length_cons]
          apply Nat.le_trans (normInfFast_add_le es (sumPlainBatch pp.d ess))
          rw [Nat.succ_mul, Nat.add_comm (shs.length * smudgeBound) smudgeBound]
          exact Nat.add_le_add hEsNorm ihNorm
/-- **Threshold Decryption Exactness Under Smudging Noise Cap (`thresholdDecrypt_exact_under_noise_cap`)**:
    Whenever `thresholdDecryptChecked cfg ct shares = .ok mOut`, if `ct` encrypts `m` under aggregate
    secret key `sumPlainBatch d skShares` with bounded encryption error `‖eEnc‖_∞ ≤ cfg.encNoiseBound`
    and `ValidThresholdShares` holds, then `mOut = m` **identically** AND `SmudgeSafe` holds! -/
theorem thresholdDecrypt_exact_under_noise_cap (cfg : ThresholdDecryptConfig)
    (ct : RlweCiphertext cfg.params.d)
    (shares : List (PartialDecryptionShare cfg.params.d))
    (skShares smudgeNoises : List (FastIntPoly cfg.params.d))
    (m eEnc mOut : FastIntPoly cfg.params.d)
    (hDec : thresholdDecryptChecked cfg ct shares = .ok mOut)
    (hEnc : RlweEncryptsWithError cfg.params (sumPlainBatch cfg.params.d skShares) ct m eEnc)
    (hEncNorm : normInfFast eEnc.coeffs ≤ cfg.encNoiseBound)
    (hShares : ValidThresholdShares cfg.params ct.c1 cfg.smudgeBound shares skShares smudgeNoises)
    (hmRange : SignedPlainInRange cfg.params m) :
    mOut = m ∧
    SmudgeSafe cfg.encNoiseBound cfg.smudgeBound cfg.secBits ∧
    cfg.quorum ≤ shares.length ∧
    (shares.map (·.guardianId)).Nodup ∧
    cfg.encNoiseBound + shares.length * cfg.smudgeBound < cfg.params.noiseCap := by
  unfold thresholdDecryptChecked at hDec
  cases hWf : cfg.params.wfB
  · simp [hWf] at hDec
  simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hDec
  cases hSm : checkSmudgeSafe cfg.encNoiseBound cfg.smudgeBound cfg.secBits
  · simp [hSm] at hDec
  simp only [hSm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hDec
  cases hQuorum : (decide (shares.length < cfg.quorum) || (cfg.quorum == 0))
  · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at hQuorum
    have hQCheckFalse : (shares.length < cfg.quorum || cfg.quorum == 0) = false := by
      simp [hQuorum.1, hQuorum.2]
    simp only [hQCheckFalse, Bool.false_eq_true, ↓reduceIte] at hDec
    cases hDup : firstDupNat? (shares.map (·.guardianId)) with
    | some gid => simp [hDup] at hDec
    | none =>
      simp only [hDup] at hDec
      cases hCanon : findNonCanonicalShare? cfg.params.q shares with
      | some gid => simp [hCanon] at hDec
      | none =>
        simp only [hCanon] at hDec
        cases hCapB : decide (cfg.encNoiseBound + shares.length * cfg.smudgeBound < cfg.params.noiseCap)
        · simp [hCapB] at hDec
        · simp only [hCapB, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hDec
          have hCapLt : cfg.encNoiseBound + shares.length * cfg.smudgeBound < cfg.params.noiseCap :=
            of_decide_eq_true hCapB
          obtain ⟨hCombMod, hSmudgeNorm⟩ :=
            combineSharePolys_phase_mod cfg.params ct.c1 cfg.smudgeBound shares skShares smudgeNoises hShares
          refine ⟨?_, (checkSmudgeSafe_iff _ _ _).1 hSm, by omega,
                  (firstDupNat?_none_iff _).1 hDup, hCapLt⟩
          rw [← hDec]
          apply Sized.ext
          funext i
          simp only [Sized.spec_ofFn, reducePolyMod_spec, addFast_eq_spec]
          let eTot := eEnc.spec i + (sumPlainBatch cfg.params.d smudgeNoises).spec i
          have hPhaseCong :
              (ct.c0.spec i + (combineSharePolys cfg.params shares).spec i) %
                (cfg.params.q : Int) % (cfg.params.q : Int) =
              (cfg.params.delta * m.spec i + eTot) % (cfg.params.q : Int) := by
            rw [Int.emod_emod, Int.add_emod, hCombMod i, ← Int.add_emod]
            have hRearr : ct.c0.spec i +
                ((negacyclicMulFast (sumPlainBatch cfg.params.d skShares) ct.c1).spec i +
                 (sumPlainBatch cfg.params.d smudgeNoises).spec i) =
                (ct.c0.spec i + (negacyclicMulFast (sumPlainBatch cfg.params.d skShares) ct.c1).spec i) +
                (sumPlainBatch cfg.params.d smudgeNoises).spec i := by omega
            rw [hRearr, Int.add_emod, hEnc i, ← Int.add_emod]
            congr 1
            dsimp only [eTot]
            omega
          have heTotLt : eTot.natAbs < cfg.params.noiseCap := by
            have h1 := coeff_le_norm eEnc i
            have h2 := coeff_le_norm (sumPlainBatch cfg.params.d smudgeNoises) i
            have hTri := Int.natAbs_add_le (eEnc.spec i) ((sumPlainBatch cfg.params.d smudgeNoises).spec i)
            omega
          obtain ⟨hmLo, hmHi⟩ := hmRange i
          exact rlweDecodeSignedCoeff_exact cfg.params _ (m.spec i) eTot
            hWf hPhaseCong hmLo hmHi heTotLt
  · have hQCheckTrue : (shares.length < cfg.quorum || cfg.quorum == 0) = true := hQuorum
    simp [hQCheckTrue] at hDec
/-- Deterministic refusal when cumulative noise meets or exceeds $\lfloor q / (2t) \rfloor$. -/
theorem thresholdDecrypt_refuses_noise_overflow (cfg : ThresholdDecryptConfig)
    (ct : RlweCiphertext cfg.params.d) (shares : List (PartialDecryptionShare cfg.params.d))
    (hwf : cfg.params.wfB = true)
    (hSm : checkSmudgeSafe cfg.encNoiseBound cfg.smudgeBound cfg.secBits = true)
    (hQuorumPos : 0 < cfg.quorum) (hQuorumLe : cfg.quorum ≤ shares.length)
    (hNodup : (shares.map (·.guardianId)).Nodup)
    (hCanon : findNonCanonicalShare? cfg.params.q shares = none)
    (hOverflow : cfg.params.noiseCap ≤ cfg.encNoiseBound + shares.length * cfg.smudgeBound) :
    thresholdDecryptChecked cfg ct shares =
      .error (.noiseBudgetExceeded (cfg.encNoiseBound + shares.length * cfg.smudgeBound) cfg.params.noiseCap) := by
  unfold thresholdDecryptChecked
  have hQFalse : (shares.length < cfg.quorum || cfg.quorum == 0) = false := by
    simp [Nat.not_lt.2 hQuorumLe, Nat.ne_of_gt hQuorumPos]
  have hDupNone := (firstDupNat?_none_iff (shares.map (·.guardianId))).2 hNodup
  have hCapFalse : decide (cfg.encNoiseBound + shares.length * cfg.smudgeBound < cfg.params.noiseCap) = false :=
    decide_eq_false (by omega)
  simp [hwf, hSm, hQFalse, hDupNone, hCanon, hCapFalse]
/-- Deterministic refusal when `smudgeBound = 0` (`Choe–Kang–Stehlé` defense). -/
theorem thresholdDecrypt_refuses_unsmudged (cfg : ThresholdDecryptConfig)
    (ct : RlweCiphertext cfg.params.d) (shares : List (PartialDecryptionShare cfg.params.d))
    (hwf : cfg.params.wfB = true) (hZeroSmudge : cfg.smudgeBound = 0) :
    thresholdDecryptChecked cfg ct shares = .error .unsmudgedThresholdNoise := by
  unfold thresholdDecryptChecked
  have hSmFalse : checkSmudgeSafe cfg.encNoiseBound cfg.smudgeBound cfg.secBits = false := by
    cases hb : checkSmudgeSafe cfg.encNoiseBound cfg.smudgeBound cfg.secBits
    · rfl
    · exact False.elim (smudgeSafe_refuses_unsmudged cfg.encNoiseBound cfg.secBits
        (hZeroSmudge ▸ (checkSmudgeSafe_iff _ _ _).1 hb))
  simp [hwf, hSmFalse]
/-- Deterministic refusal when a guardian submits a non-canonical share outside `[0, q)`. -/
theorem thresholdDecrypt_refuses_malformed_share (cfg : ThresholdDecryptConfig)
    (ct : RlweCiphertext cfg.params.d) (shares : List (PartialDecryptionShare cfg.params.d)) (gid : Nat)
    (hwf : cfg.params.wfB = true)
    (hSm : checkSmudgeSafe cfg.encNoiseBound cfg.smudgeBound cfg.secBits = true)
    (hQuorumPos : 0 < cfg.quorum) (hQuorumLe : cfg.quorum ≤ shares.length)
    (hNodup : (shares.map (·.guardianId)).Nodup)
    (hBad : findNonCanonicalShare? cfg.params.q shares = some gid) :
    thresholdDecryptChecked cfg ct shares = .error (.nonCanonicalShare gid) := by
  unfold thresholdDecryptChecked
  have hQFalse : (shares.length < cfg.quorum || cfg.quorum == 0) = false := by
    simp [Nat.not_lt.2 hQuorumLe, Nat.ne_of_gt hQuorumPos]
  have hDupNone := (firstDupNat?_none_iff (shares.map (·.guardianId))).2 hNodup
  simp [hwf, hSm, hQFalse, hDupNone, hBad]

/-! ## 4b. What smudging hides: the statistical bound on one clearing seat

A guardian's share reveals a seat quantity `q` only through `q + e` with `e` uniform on `[-B, B]`,
`B = cfg.smudgeBound`. For two candidate quantities at distance `|q₁ - q₂| ≤ seatSensitivity`, the transcripts
`q₁ + e₁` and `q₂ + e₂` are both uniform on `2B + 1` points and their supports overlap in
`2B + 1 - |q₁ - q₂|` points. On the overlap the two distributions are identical point for point (so every Rényi
divergence between them, conditioned on the overlap, is `0`), and a transcript leaves the overlap with
probability `|q₁ - q₂| / (2B + 1)`, which is the statistical distance. -/

/-- Number of smudged transcripts both seat quantities can produce under noise bound `B`. -/
def smudgedOverlapMass (B : Nat) (q₁ q₂ : Int) : Nat := 2 * B + 1 - (q₁ - q₂).natAbs
/-- The smudging range is `2^secBits` times the seat sensitivity: `seatSensitivity · 2^secBits ≤ 2B + 1`. -/
def checkRenyiSmudgeSecurity (cfg : ThresholdDecryptConfig) (seatSensitivity : Nat) : Bool :=
  decide (seatSensitivity * 2 ^ cfg.secBits ≤ 2 * cfg.smudgeBound + 1)
example : checkRenyiSmudgeSecurity
    { params := ⟨4, 2 ^ 54, 256⟩, quorum := 3, encNoiseBound := 8, smudgeBound := 2 ^ 43, secBits := 40 } 16 = true := by
  decide
/-- **Statistical smudging bound.** For seat quantities within `seatSensitivity` under an accepted configuration:
1. every transcript `y` in the overlap of the two noise ranges is produced by both, each by exactly one in-range
   mask (so both give it mass `1 / (2B + 1)`);
2. the overlap has exactly `smudgedOverlapMass` points;
3. the mass outside the overlap, `(2B + 1 - overlap) / (2B + 1) = |q₁ - q₂| / (2B + 1)`, is at most `2^-secBits`. -/
theorem renyiSmudgingBound_sound (cfg : ThresholdDecryptConfig) (seatSensitivity : Nat) (q₁ q₂ : Int)
    (hChk : checkRenyiSmudgeSecurity cfg seatSensitivity = true) (hSens : (q₁ - q₂).natAbs ≤ seatSensitivity) :
    (∀ y : Int, max (q₁ - cfg.smudgeBound) (q₂ - cfg.smudgeBound) ≤ y →
      y ≤ min (q₁ + cfg.smudgeBound) (q₂ + cfg.smudgeBound) →
      ∃ e₁ e₂ : Int, e₁.natAbs ≤ cfg.smudgeBound ∧ e₂.natAbs ≤ cfg.smudgeBound ∧ q₁ + e₁ = y ∧ q₂ + e₂ = y ∧
        ∀ e : Int, (q₁ + e = y → e = e₁) ∧ (q₂ + e = y → e = e₂)) ∧
    min (q₁ + cfg.smudgeBound) (q₂ + cfg.smudgeBound) - max (q₁ - cfg.smudgeBound) (q₂ - cfg.smudgeBound) + 1 =
      (smudgedOverlapMass cfg.smudgeBound q₁ q₂ : Int) ∧
    (2 * cfg.smudgeBound + 1 - smudgedOverlapMass cfg.smudgeBound q₁ q₂) * 2 ^ cfg.secBits ≤
      2 * cfg.smudgeBound + 1 := by
  simp only [checkRenyiSmudgeSecurity, decide_eq_true_eq] at hChk
  have hMul : (q₁ - q₂).natAbs * 2 ^ cfg.secBits ≤ seatSensitivity * 2 ^ cfg.secBits :=
    Nat.mul_le_mul_right _ hSens
  have hD : (q₁ - q₂).natAbs ≤ 2 * cfg.smudgeBound + 1 :=
    Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) (Nat.le_trans hMul hChk)
  have e : 2 * cfg.smudgeBound + 1 - smudgedOverlapMass cfg.smudgeBound q₁ q₂ = (q₁ - q₂).natAbs := by
    unfold smudgedOverlapMass; omega
  refine ⟨fun y hLo hHi => ⟨y - q₁, y - q₂, by omega, by omega, by omega, by omega, fun e => ⟨by omega, by omega⟩⟩,
    by unfold smudgedOverlapMass; omega, ?_⟩
  rw [e]; exact Nat.le_trans hMul hChk
/-- A `SmudgeSafe` configuration hides seat differences up to its encryption noise bound. -/
theorem smudgeSafe_checkRenyiSmudgeSecurity (cfg : ThresholdDecryptConfig)
    (h : SmudgeSafe cfg.encNoiseBound cfg.smudgeBound cfg.secBits) :
    checkRenyiSmudgeSecurity cfg cfg.encNoiseBound = true := by
  have := h.2.2
  simp only [checkRenyiSmudgeSecurity, decide_eq_true_eq]; omega

/-! ## 5. Stage 5 — `SameOpening` Salted KKT Clearing, `ConservedValue` Settlement & Multi-Epoch Trace -/
def postingToConservedForAsset (ast : AssetId) (p : ResourcePosting) : ConservedValue :=
  if p.asset == ast then ConservedValue.transfer p.source p.destination (p.amount : Int)
  else ConservedValue.zero
/-- Compile a cleared `ResourcePosting` settlement batch for asset `ast` into `ConservedValue`. -/
@[expose] def settleAssetConserved (ast : AssetId) : List ResourcePosting → ConservedValue
  | [] => ConservedValue.zero
  | p :: ps => ConservedValue.add (postingToConservedForAsset ast p) (settleAssetConserved ast ps)
/-- **Exact `MintSafe` Settlement Conservation (`settleAssetConserved_deltaAt_eq_netFlow`)**:
    For every account `acc` and asset `ast`, `deltaAt` of `settleAssetConserved ast ts` equals
    `Obend.Judge.netFlow ts acc ast` **identically**, and total supply change `sumDeltas` is `0`! -/
theorem settleAssetConserved_deltaAt_eq_netFlow
    (ast : AssetId) (ts : List ResourcePosting) (acc : AccountId) :
    deltaAt (settleAssetConserved ast ts).entries acc = netFlow ts acc ast ∧
    sumDeltas (settleAssetConserved ast ts).entries = 0 := by
  refine ⟨?_, (settleAssetConserved ast ts).conserved⟩
  induction ts with
  | nil =>
    simp [settleAssetConserved, ConservedValue.zero, deltaAt, netFlow]
  | cons p ps ih =>
    simp only [settleAssetConserved]
    let headCV := postingToConservedForAsset ast p
    let tailCV := settleAssetConserved ast ps
    change deltaAt (addDeltaLists headCV.entries tailCV.entries) acc = netFlow (p :: ps) acc ast
    rw [deltaAt_addDeltaLists headCV.wf tailCV.wf acc, ih]
    simp only [netFlow, List.map_cons, List.sum_cons]
    have hHead : deltaAt headCV.entries acc =
        (if p.destination = acc ∧ p.asset = ast then (p.amount : Int) else 0) -
        (if p.source = acc ∧ p.asset = ast then (p.amount : Int) else 0) := by
      dsimp only [headCV, postingToConservedForAsset]
      by_cases hAst : p.asset = ast
      · have hAstT : (p.asset == ast) = true := beq_iff_eq.2 hAst
        simp only [hAstT, ↓reduceIte]
        rw [ConservedValue.transfer_deltaAt]
        by_cases hSrc : acc = p.source <;> by_cases hDst : acc = p.destination
        · subst hSrc; simp [hDst.symm, hAst]; omega
        · subst hSrc; have hNe : (p.source == p.destination) = false := beq_false_of_ne hDst
          simp [hNe, Ne.symm hDst, hAst]
        · subst hDst; have hNe : (p.destination == p.source) = false := beq_false_of_ne hSrc
          simp [hNe, Ne.symm hSrc, hAst]
        · have hNeS : (acc == p.source) = false := beq_false_of_ne hSrc
          have hNeD : (acc == p.destination) = false := beq_false_of_ne hDst
          simp [hNeS, hNeD, Ne.symm hSrc, Ne.symm hDst, hAst]
      · have hAstF : (p.asset == ast) = false := beq_false_of_ne hAst
        simp [hAstF, hAst, ConservedValue.zero, deltaAt]
    rw [hHead]
/-- Encode a trader's opened order `(side, qty, total)` into its signed demand/supply RLWE vector:
    lane 0 carries signed quantity (`+qty` for `.bid`, `-qty` for `.ask`), lane 1 carries signed limit
    value (`+total` for `.bid`, `-total` for `.ask`), and higher lanes carry `0`. -/
def orderSignedPlainVec (d : Nat) (side : Side) (qty total : Nat) : FastIntPoly d :=
  let sign : Int := match side with | .bid => 1 | .ask => -1
  Sized.ofFn fun i =>
    if i.val = 0 then sign * (qty : Int)
    else if i.val = 1 then sign * (total : Int)
    else 0
def expectedAggregateOrderBook (d : Nat) :
    List CommittedOrderSpec → List OrderBitWitness → FastIntPoly d
  | s :: ss, w :: ws =>
    intAdd (orderSignedPlainVec d s.side w.qty w.total) (expectedAggregateOrderBook d ss ws)
  | _, _ => zeroVec d
theorem expectedAggregateOrderBook_eq_sumPlainBatch (d : Nat)
    (specs : List CommittedOrderSpec) (ws : List OrderBitWitness)
    (hLen : specs.length = ws.length) :
    expectedAggregateOrderBook d specs ws =
      sumPlainBatch d ((specs.zip ws).map fun (s, w) => orderSignedPlainVec d s.side w.qty w.total) := by
  induction specs generalizing ws with
  | nil =>
    cases ws with
    | nil => rfl
    | cons _ _ => simp at hLen
  | cons s ss ih =>
    cases ws with
    | nil => simp at hLen
    | cons w ws' =>
      simp only [List.length_cons, Nat.succ.injEq] at hLen
      simp [expectedAggregateOrderBook, sumPlainBatch, ih ws' hLen]
/-- Complete single-epoch `DarkBazaar` private clearing bundle across all 5 stages. -/
structure DarkBazaarEpochBatch (sableDim : Nat) (cfg : ThresholdDecryptConfig) where
  epochNullifier : Nat
  utilityCerts : List TraderUtilityCert
  sableWitnesses : List (SableLinearWitness sableDim)
  encryptedOrders : List (RlweCiphertext cfg.params.d)
  thresholdShares : List (PartialDecryptionShare cfg.params.d)
  openingQuery : SameOpeningQuery
  openingWitness : SameOpeningWitness
/-- Verified settlement outcome produced by `verifyAndClearDarkBazaarEpoch`. -/
structure DarkBazaarClearedOutcome (d : Nat) where
  decryptedBook : FastIntPoly d
  currencySettlement : ConservedValue
  goodsSettlement : ConservedValue
/-- Unified refusal sum for `verifyAndClearDarkBazaarEpoch`. -/
inductive DarkBazaarRefusal where
  | smudgeParamMismatch | utilityBatchInvalid | sableBatchInvalid | ciphertextCountMismatch
  | thresholdFailed (reason : ThresholdRefusal) | aggregateBookMismatch
  | sameOpeningFailed (reason : SameOpeningRefusal) | sameOpeningUncovered
  deriving DecidableEq, Repr
/-- **Executable 5-Stage `DarkBazaar` Epoch Verifier & Settlement Engine (`verifyAndClearDarkBazaarEpoch`)**. -/
@[expose] def verifyAndClearDarkBazaarEpoch {sableDim : Nat} (cfg : ThresholdDecryptConfig)
    (batch : DarkBazaarEpochBatch sableDim cfg) :
    Except DarkBazaarRefusal (DarkBazaarClearedOutcome cfg.params.d) :=
  if !(decide (batch.openingQuery.noiseBound = cfg.encNoiseBound) &&
       decide (batch.openingQuery.smudgeBound = cfg.smudgeBound) &&
       decide (batch.openingQuery.secBits = cfg.secBits)) then .error .smudgeParamMismatch
  else if !checkUtilityBatch batch.utilityCerts
      batch.openingQuery.committedOrders batch.openingWitness.orderWitnesses then .error .utilityBatchInvalid
  else if !@checkSableBatch sableDim batch.sableWitnesses batch.openingWitness.orderWitnesses then .error .sableBatchInvalid
  else if batch.encryptedOrders.length != batch.openingQuery.committedOrders.length then .error .ciphertextCountMismatch
  else
    let aggCt := rlweAggregateBatch cfg.params batch.encryptedOrders
    match thresholdDecryptChecked cfg aggCt batch.thresholdShares with
    | .error r => .error (.thresholdFailed r)
    | .ok decBook =>
      let expBook := expectedAggregateOrderBook cfg.params.d
        batch.openingQuery.committedOrders batch.openingWitness.orderWitnesses
      if decBook != expBook then .error .aggregateBookMismatch
      else
        match verifySameOpening batch.openingQuery batch.openingWitness with
        | .refused r _ => .error (.sameOpeningFailed r)
        | .uncovered => .error .sameOpeningUncovered
        | .ok =>
          .ok { decryptedBook := decBook
              , currencySettlement := settleAssetConserved batch.openingQuery.market.currency batch.openingWitness.transfers
              , goodsSettlement := settleAssetConserved batch.openingQuery.market.goods batch.openingWitness.transfers }
/-- **Grand Pillar-4 Theorem (`darkBazaar_sable_rlwe_smudge_clearing_conserves`)**:
    Welds `TaylorModel` enclosure, `Sable` `Goldilocks` exactness, homomorphic RLWE aggregation,
    smudged $k$-of-$n$ threshold decryption, `SameOpening` KKT zero-gap clearing, and `ConservedValue`. -/
theorem darkBazaar_sable_rlwe_smudge_clearing_conserves
    {sableDim : Nat} (cfg : ThresholdDecryptConfig)
    (batch : DarkBazaarEpochBatch sableDim cfg)
    (us : List (Obend.Analysis.CanonicalRat → Obend.Analysis.CanonicalRat))
    (skShares smudgeNoises orderNoises : List (FastIntPoly cfg.params.d))
    (out : DarkBazaarClearedOutcome cfg.params.d)
    (hClear : verifyAndClearDarkBazaarEpoch cfg batch = .ok out)
    (hTM : AllTaylorModelsHold us batch.utilityCerts)
    (hEncBatch : BatchEncryptsWithErrors cfg.params (sumPlainBatch cfg.params.d skShares)
      batch.encryptedOrders
      ((batch.openingQuery.committedOrders.zip batch.openingWitness.orderWitnesses).map
        fun (s, w) => orderSignedPlainVec cfg.params.d s.side w.qty w.total)
      orderNoises)
    (hEncNorm : normInfFast (sumPlainBatch cfg.params.d orderNoises).coeffs ≤ cfg.encNoiseBound)
    (hShares : ValidThresholdShares cfg.params
      (rlweAggregateBatch cfg.params batch.encryptedOrders).c1
      cfg.smudgeBound batch.thresholdShares skShares smudgeNoises)
    (hPlainRange : SignedPlainInRange cfg.params
      (sumPlainBatch cfg.params.d
        ((batch.openingQuery.committedOrders.zip batch.openingWitness.orderWitnesses).map
          fun (s, w) => orderSignedPlainVec cfg.params.d s.side w.qty w.total))) :
    AllUtilityEnclosuresHold us batch.utilityCerts
      batch.openingQuery.committedOrders batch.openingWitness.orderWitnesses ∧
    AllSableInferencesExact batch.sableWitnesses batch.openingWitness.orderWitnesses ∧
    SmudgeSafe cfg.encNoiseBound cfg.smudgeBound cfg.secBits ∧
    cfg.encNoiseBound + batch.thresholdShares.length * cfg.smudgeBound < cfg.params.noiseCap ∧
    out.decryptedBook =
      sumPlainBatch cfg.params.d
        ((batch.openingQuery.committedOrders.zip batch.openingWitness.orderWitnesses).map
          fun (s, w) => orderSignedPlainVec cfg.params.d s.side w.qty w.total) ∧
    out.decryptedBook =
      expectedAggregateOrderBook cfg.params.d
        batch.openingQuery.committedOrders batch.openingWitness.orderWitnesses ∧
    SameOpeningMeaning batch.openingQuery batch.openingWitness ∧
    sumDeltas out.currencySettlement.entries = 0 ∧
    sumDeltas out.goodsSettlement.entries = 0 ∧
    (∀ acc : AccountId,
      deltaAt out.currencySettlement.entries acc =
        netFlow batch.openingWitness.transfers acc batch.openingQuery.market.currency ∧
      deltaAt out.goodsSettlement.entries acc =
        netFlow batch.openingWitness.transfers acc batch.openingQuery.market.goods) := by
  unfold verifyAndClearDarkBazaarEpoch at hClear
  cases hSmAlign : (decide (batch.openingQuery.noiseBound = cfg.encNoiseBound) &&
      decide (batch.openingQuery.smudgeBound = cfg.smudgeBound) &&
      decide (batch.openingQuery.secBits = cfg.secBits))
  · simp [hSmAlign] at hClear
  simp only [hSmAlign, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hClear
  cases hUtil : checkUtilityBatch batch.utilityCerts
      batch.openingQuery.committedOrders batch.openingWitness.orderWitnesses
  · simp [hUtil] at hClear
  simp only [hUtil, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hClear
  cases hSable : checkSableBatch batch.sableWitnesses batch.openingWitness.orderWitnesses
  · simp [hSable] at hClear
  simp only [hSable, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hClear
  cases hCtLen : (batch.encryptedOrders.length != batch.openingQuery.committedOrders.length)
  · simp only [hCtLen, Bool.false_eq_true, ↓reduceIte] at hClear
    cases hDec : thresholdDecryptChecked cfg
        (rlweAggregateBatch cfg.params batch.encryptedOrders) batch.thresholdShares with
    | error r => simp [hDec] at hClear
    | ok decBook =>
      simp only [hDec] at hClear
      let expBook := expectedAggregateOrderBook cfg.params.d
        batch.openingQuery.committedOrders batch.openingWitness.orderWitnesses
      cases hBookNe : (decBook != expBook)
      · simp only [expBook, hBookNe, Bool.false_eq_true, ↓reduceIte] at hClear
        have hBookEq : decBook = expBook := bne_eq_false_iff_eq.1 hBookNe
        cases hSO : verifySameOpening batch.openingQuery batch.openingWitness with
        | refused r p => simp [hSO] at hClear
        | uncovered => simp [hSO] at hClear
        | ok =>
          simp only [hSO, Except.ok.injEq] at hClear
          have hAggEnc := rlweAggregateBatch_encrypts_sum cfg.params
            (sumPlainBatch cfg.params.d skShares)
            batch.encryptedOrders _ orderNoises hEncBatch
          obtain ⟨hDecExact, hSmSafe, _, _, hCapLt⟩ :=
            thresholdDecrypt_exact_under_noise_cap cfg
              (rlweAggregateBatch cfg.params batch.encryptedOrders)
              batch.thresholdShares skShares smudgeNoises _
              (sumPlainBatch cfg.params.d orderNoises) decBook
              hDec hAggEnc hEncNorm hShares hPlainRange
          subst hClear
          refine ⟨checkUtilityBatch_sound us batch.utilityCerts _ _ hTM hUtil,
                  checkSableBatch_sound batch.sableWitnesses _ hSable,
                  hSmSafe, hCapLt, hDecExact, hBookEq,
                  verifySameOpening_sound hSO,
                  (settleAssetConserved _ _).conserved,
                  (settleAssetConserved _ _).conserved,
                  fun acc => ⟨(settleAssetConserved_deltaAt_eq_netFlow _ _ acc).1,
                              (settleAssetConserved_deltaAt_eq_netFlow _ _ acc).1⟩⟩
      · simp [expBook, hBookNe] at hClear
  · simp [hCtLen] at hClear

/-! ## 6. Multi-Epoch Stateful Batch Auction Machine (`ValidDarkBazaarTrace`) -/
/-- Decidable membership probe on `NullifierSet`. -/
def nullifierContainsB (s : NullifierSet) (nf : Nat) : Bool :=
  s.items.contains nf
theorem nullifierContainsB_iff (s : NullifierSet) (nf : Nat) :
    nullifierContainsB s nf = true ↔ nf ∈ s.items :=
  List.contains_iff_mem
/-- Persistent multi-epoch `DarkBazaar` protocol state tracking epoch counter, replay-preventing
    `NullifierSet`, cumulative conserved settlements, and remaining decryption budget. -/
structure DarkBazaarState where
  epoch : Nat
  spentNullifiers : NullifierSet
  cumulativeCurrency : ConservedValue
  cumulativeGoods : ConservedValue
  remainingDecryptionBudget : Nat
/-- Initial empty `DarkBazaarState` with a fixed multi-epoch decryption budget. -/
def DarkBazaarState.init (budget : Nat) : DarkBazaarState :=
  { epoch := 0, spentNullifiers := .empty, cumulativeCurrency := .zero, cumulativeGoods := .zero, remainingDecryptionBudget := budget }
inductive DarkBazaarTraceError where
  | nullifierAlreadySpent (nf : Nat) | decryptionBudgetExhausted (needed available : Nat) | epochClearingFailed (reason : DarkBazaarRefusal)
  deriving DecidableEq, Repr
/-- Execute one stateful `DarkBazaar` batch-auction epoch transition. -/
@[expose] def stepDarkBazaarEpoch {sableDim : Nat} (cfg : ThresholdDecryptConfig)
    (st : DarkBazaarState) (batch : DarkBazaarEpochBatch sableDim cfg) :
    Except DarkBazaarTraceError (DarkBazaarState × DarkBazaarClearedOutcome cfg.params.d) :=
  if nullifierContainsB st.spentNullifiers batch.epochNullifier then .error (.nullifierAlreadySpent batch.epochNullifier)
  else if st.remainingDecryptionBudget < batch.thresholdShares.length then
    .error (.decryptionBudgetExhausted batch.thresholdShares.length st.remainingDecryptionBudget)
  else
    match verifyAndClearDarkBazaarEpoch cfg batch with
    | .error r => .error (.epochClearingFailed r)
    | .ok out =>
      .ok ({ epoch := st.epoch + 1, spentNullifiers := st.spentNullifiers.insert batch.epochNullifier
           , cumulativeCurrency := ConservedValue.add st.cumulativeCurrency out.currencySettlement
           , cumulativeGoods := ConservedValue.add st.cumulativeGoods out.goodsSettlement
           , remainingDecryptionBudget := st.remainingDecryptionBudget - batch.thresholdShares.length }, out)
/-- Multi-turn reachability relation for sequential `DarkBazaar` batch-auction epochs. -/
inductive ValidDarkBazaarTrace {sableDim : Nat} (cfg : ThresholdDecryptConfig) :
    DarkBazaarState → List (DarkBazaarEpochBatch sableDim cfg) → DarkBazaarState → Prop where
  | nil (st : DarkBazaarState) : ValidDarkBazaarTrace cfg st [] st
  | step {st mid final : DarkBazaarState} {batch : DarkBazaarEpochBatch sableDim cfg}
      {rest : List (DarkBazaarEpochBatch sableDim cfg)} {out : DarkBazaarClearedOutcome cfg.params.d}
      (hStep : stepDarkBazaarEpoch cfg st batch = .ok (mid, out))
      (hTail : ValidDarkBazaarTrace cfg mid rest final) : ValidDarkBazaarTrace cfg st (batch :: rest) final
private theorem subsetB_trans_nullifiers {a b c : NullifierSet} (h1 : a.subsetB b = true) (h2 : b.subsetB c = true) :
    a.subsetB c = true :=
  NullifierSet.subsetB_iff.2 fun x hx => NullifierSet.subsetB_iff.1 h2 x (NullifierSet.subsetB_iff.1 h1 x hx)
private theorem subsetB_insert_self (s : NullifierSet) (nf : Nat) : s.subsetB (s.insert nf) = true :=
  NullifierSet.subsetB_iff.2 fun _ hx => NullifierSet.mem_insert.2 (Or.inr hx)
/-- **Multi-Epoch `DarkBazaar` Safety, Nullifier Non-Replay, Budget Monotonicity & `MintSafe` Conservation
    (`validDarkBazaarTrace_conserves_and_safe`)**. -/
theorem validDarkBazaarTrace_conserves_and_safe {sableDim : Nat} (cfg : ThresholdDecryptConfig)
    (init final : DarkBazaarState) (batches : List (DarkBazaarEpochBatch sableDim cfg))
    (hTrace : ValidDarkBazaarTrace cfg init batches final) :
    final.epoch = init.epoch + batches.length ∧ sumDeltas final.cumulativeCurrency.entries = 0 ∧
    sumDeltas final.cumulativeGoods.entries = 0 ∧ init.spentNullifiers.subsetB final.spentNullifiers = true ∧
    final.remainingDecryptionBudget ≤ init.remainingDecryptionBudget ∧
    (∀ b ∈ batches, nullifierContainsB final.spentNullifiers b.epochNullifier = true) ∧
    (batches.map (·.epochNullifier)).Nodup := by
  induction hTrace with
  | nil st =>
    refine ⟨by simp, st.cumulativeCurrency.conserved, st.cumulativeGoods.conserved,
            NullifierSet.subsetB_iff.2 (fun _ hx => hx), Nat.le_refl _, ?_, List.nodup_nil⟩
    intro _ hMem; cases hMem
  | @step st mid fin batch rest out hStep hTail ih =>
    unfold stepDarkBazaarEpoch at hStep
    cases hSpent : nullifierContainsB st.spentNullifiers batch.epochNullifier
    · simp only [hSpent, Bool.false_eq_true, ↓reduceIte] at hStep
      cases hBud : decide (st.remainingDecryptionBudget < batch.thresholdShares.length)
      · have hNotLt : ¬ (st.remainingDecryptionBudget < batch.thresholdShares.length) := of_decide_eq_false hBud
        simp only [hNotLt, ↓reduceIte] at hStep
        cases hClear : verifyAndClearDarkBazaarEpoch cfg batch with
        | error r => simp [hClear] at hStep
        | ok cleared =>
          simp only [hClear, Except.ok.injEq, Prod.mk.injEq] at hStep
          rcases hStep with ⟨hMidEq, _⟩
          rcases ih with ⟨hEp, hCur0, hGds0, hSubTail, hBudTail, hAllSpent, hNdTail⟩
          have hMidSub : st.spentNullifiers.subsetB mid.spentNullifiers = true := by
            rw [← hMidEq]; exact subsetB_insert_self st.spentNullifiers batch.epochNullifier
          have hBatchInMid : batch.epochNullifier ∈ mid.spentNullifiers.items := by
            rw [← hMidEq]; exact NullifierSet.mem_insert.2 (Or.inl rfl)
          have hBatchInFin : nullifierContainsB fin.spentNullifiers batch.epochNullifier = true :=
            (nullifierContainsB_iff _ _).2 (NullifierSet.subsetB_iff.1 hSubTail batch.epochNullifier hBatchInMid)
          have hMidEp : mid.epoch = st.epoch + 1 := by rw [← hMidEq]
          have hMidBud : mid.remainingDecryptionBudget ≤ st.remainingDecryptionBudget := by rw [← hMidEq]; dsimp only; omega
          refine ⟨by simp [List.length_cons, hEp, hMidEp]; omega, hCur0, hGds0,
                  subsetB_trans_nullifiers hMidSub hSubTail, Nat.le_trans hBudTail hMidBud, ?_, ?_⟩
          · intro b hb; rcases List.mem_cons.1 hb with rfl | hbRest; exact hBatchInFin; exact hAllSpent b hbRest
          · rw [List.map_cons, List.nodup_cons]; refine ⟨?_, hNdTail⟩
            intro hDupMem; rcases List.mem_map.1 hDupMem with ⟨b2, hb2Mem, hb2Eq⟩
            have hSubFirst : ∀ {s1 s2 : DarkBazaarState} {bs : List (DarkBazaarEpochBatch sableDim cfg)},
                ValidDarkBazaarTrace cfg s1 bs s2 → b2 ∈ bs →
                nullifierContainsB s1.spentNullifiers b2.epochNullifier = false := by
              intro s1 s2 bs hTr
              induction hTr with
              | nil _ => intro hm; cases hm
              | @step sa sb sc hd tl out' hSt' _ ihTr =>
                intro hm
                rcases List.mem_cons.1 hm with hEqHd | hmTl
                · rw [hEqHd]
                  unfold stepDarkBazaarEpoch at hSt'
                  cases hc : nullifierContainsB sa.spentNullifiers hd.epochNullifier
                  · rfl
                  · simp [hc] at hSt'
                · have hNotInSb := ihTr hmTl
                  unfold stepDarkBazaarEpoch at hSt'
                  cases hc : nullifierContainsB sa.spentNullifiers hd.epochNullifier
                  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hSt'
                    by_cases hBl : sa.remainingDecryptionBudget < hd.thresholdShares.length
                    · simp [hBl] at hSt'
                    · simp only [hBl, ↓reduceIte] at hSt'
                      cases hCl : verifyAndClearDarkBazaarEpoch cfg hd with
                      | error _ => simp [hCl] at hSt'
                      | ok _ =>
                        simp only [hCl, Except.ok.injEq, Prod.mk.injEq] at hSt'
                        have hSubSaSb : sa.spentNullifiers.subsetB sb.spentNullifiers = true := by
                          rw [← hSt'.1]
                          exact subsetB_insert_self _ _
                        cases hInSa : nullifierContainsB sa.spentNullifiers b2.epochNullifier
                        · rfl
                        · exfalso
                          have hMemSb := NullifierSet.subsetB_iff.1 hSubSaSb _
                            ((nullifierContainsB_iff _ _).1 hInSa)
                          rw [(nullifierContainsB_iff _ _).2 hMemSb] at hNotInSb
                          cases hNotInSb
                  · simp [hc] at hSt'
            have hFalse := hSubFirst hTail hb2Mem
            have hInMidB : nullifierContainsB mid.spentNullifiers batch.epochNullifier = true :=
              (nullifierContainsB_iff _ _).2 hBatchInMid
            rw [hb2Eq, hInMidB] at hFalse
            cases hFalse
      · have hLt : st.remainingDecryptionBudget < batch.thresholdShares.length :=
          of_decide_eq_true hBud
        simp [hLt] at hStep
    · simp [hSpent] at hStep
/-- Every accepted epoch step induces a genuine `AuthCamera` frame-preserving update (`spend_nullifier_fpu`). -/
theorem stepDarkBazaarEpoch_authCamera_fpu {sableDim : Nat} (cfg : ThresholdDecryptConfig)
    (st st' : DarkBazaarState) (batch : DarkBazaarEpochBatch sableDim cfg)
    (out : DarkBazaarClearedOutcome cfg.params.d)
    (hStep : stepDarkBazaarEpoch cfg st batch = .ok (st', out)) :
    FPU (AuthCamera.mkAuth st.epoch st.spentNullifiers st.cumulativeCurrency)
      (fun b => ∃ authNext : AuthCamera,
        authNext = AuthCamera.mkAuth st.epoch st'.spentNullifiers st.cumulativeCurrency ∧
        LawfulPCM.op? authNext
          (AuthCamera.mkFrag st.epoch (.singleton batch.epochNullifier) out.currencySettlement) = some b) := by
  unfold stepDarkBazaarEpoch at hStep
  cases hSpent : nullifierContainsB st.spentNullifiers batch.epochNullifier
  · simp only [hSpent, Bool.false_eq_true, ↓reduceIte] at hStep
    by_cases hBud : st.remainingDecryptionBudget < batch.thresholdShares.length
    · simp [hBud] at hStep
    · simp only [hBud, ↓reduceIte] at hStep
      cases hClear : verifyAndClearDarkBazaarEpoch cfg batch with
      | error r => simp [hClear] at hStep
      | ok cleared =>
        simp only [hClear, Except.ok.injEq, Prod.mk.injEq] at hStep
        rcases hStep with ⟨hStEq, _⟩
        have hNfs : st'.spentNullifiers = st.spentNullifiers.insert batch.epochNullifier := by
          rw [← hStEq]
        rw [hNfs]
        exact AuthCamera.spend_nullifier_fpu st.epoch st.spentNullifiers
          batch.epochNullifier st.cumulativeCurrency out.currencySettlement
  · simp [hSpent] at hStep
/-- Open-world refusal completeness: `stepDarkBazaarEpoch` returns `.error` iff inadmissible. -/
theorem stepDarkBazaarEpoch_error_iff_inadmissible {sableDim : Nat} (cfg : ThresholdDecryptConfig)
    (st : DarkBazaarState) (batch : DarkBazaarEpochBatch sableDim cfg)
    (err : DarkBazaarTraceError) :
    stepDarkBazaarEpoch cfg st batch = .error err ↔
      (nullifierContainsB st.spentNullifiers batch.epochNullifier = true ∧
        err = .nullifierAlreadySpent batch.epochNullifier) ∨
      (nullifierContainsB st.spentNullifiers batch.epochNullifier = false ∧
        st.remainingDecryptionBudget < batch.thresholdShares.length ∧
        err = .decryptionBudgetExhausted batch.thresholdShares.length st.remainingDecryptionBudget) ∨
      (nullifierContainsB st.spentNullifiers batch.epochNullifier = false ∧
        batch.thresholdShares.length ≤ st.remainingDecryptionBudget ∧
        ∃ r, verifyAndClearDarkBazaarEpoch cfg batch = .error r ∧ err = .epochClearingFailed r) := by
  unfold stepDarkBazaarEpoch
  cases hSpent : nullifierContainsB st.spentNullifiers batch.epochNullifier
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, false_or]
    by_cases hBud : st.remainingDecryptionBudget < batch.thresholdShares.length
    · simp only [hBud, ↓reduceIte, Except.error.injEq, true_and]
      constructor
      · intro h; exact Or.inl h.symm
      · rintro (rfl | ⟨hGe, _⟩)
        · rfl
        · omega
    · have hGe : batch.thresholdShares.length ≤ st.remainingDecryptionBudget := by omega
      simp only [hBud, ↓reduceIte, false_and, false_or, hGe, true_and]
      cases hCl : verifyAndClearDarkBazaarEpoch cfg batch with
      | error r =>
        simp only [Except.error.injEq]
        exact ⟨fun h => ⟨r, rfl, h.symm⟩, fun ⟨r', hr', he⟩ => by cases hr'; exact he.symm⟩
      | ok _ =>
        simp
  · simp only [↓reduceIte, Except.error.injEq, true_and, Bool.true_eq_false, false_and, or_false]
    exact ⟨Eq.symm, Eq.symm⟩

/-! ## 7. Authorized Guardian Committee & 256-Bit Order-Payload Nullifier Binding -/
/-- Verify `committee` has no duplicate IDs, is non-empty, and authorizes every share's `guardianId`. -/
def checkAuthorizedCommittee {d : Nat} (committee : List Nat) (shares : List (PartialDecryptionShare d)) : Bool :=
  (firstDupNat? committee).isNone && !committee.isEmpty && shares.all (fun s => committee.contains s.guardianId)

theorem checkAuthorizedCommittee_sound {d : Nat} (committee : List Nat) (shares : List (PartialDecryptionShare d))
    (h : checkAuthorizedCommittee committee shares = true) :
    committee ≠ [] ∧ ∀ s ∈ shares, s.guardianId ∈ committee := by
  simp only [checkAuthorizedCommittee, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  exact ⟨fun hc => by simp [hc] at h, fun s hs => List.contains_iff_mem.mp (h.2 s hs)⟩
example : checkAuthorizedCommittee ([0, 1] : List Nat) ([] : List (PartialDecryptionShare 4)) = true := by decide

private def dbFrameBytes (bs : List UInt8) : List UInt8 := Obend.Digest.HashBytes.be 8 bs.length ++ bs
def encodeDarkBazaarIntBytes (z : Int) : List UInt8 :=
  (if z < 0 then [(1 : UInt8)] else [(0 : UInt8)]) ++ Obend.Digest.HashBytes.be 8 z.natAbs

/-- Derive a 256-bit order-payload nullifier via `poseidon2Hash32` over framed market context,
`CommittedOrderSpec` commitments, and `RlweCiphertext` polynomials — independent of `epochNullifier`. -/
def deriveOrderBatchNullifier256 {d : Nat} (market : Market)
    (committedOrders : List CommittedOrderSpec) (encryptedOrders : List (RlweCiphertext d)) : BitVec 256 :=
  let mktBytes := dbFrameBytes (reprStr market).toUTF8.toList
  let ordBytes := dbFrameBytes (committedOrders.flatMap fun s =>
    dbFrameBytes (reprStr s.account).toUTF8.toList ++
    [match s.side with | .bid => (0 : UInt8) | .ask => (1 : UInt8)] ++
    Obend.Digest.HashBytes.be 8 s.maxBits ++
    dbFrameBytes (TranscriptEncode.encodeTranscriptBytes s.dualComm).toList)
  let ctBytes := dbFrameBytes (encryptedOrders.flatMap fun ct =>
    dbFrameBytes (ct.c0.coeffs.toList.flatMap encodeDarkBazaarIntBytes) ++
    dbFrameBytes (ct.c1.coeffs.toList.flatMap encodeDarkBazaarIntBytes))
  BitVec.ofNat 256 (Obend.Digest.HashBytes.ofBE (poseidon2Hash32 (mktBytes ++ ordBytes ++ ctBytes)))

structure DarkBazaarAuthState where
  base : DarkBazaarState
  committee : List Nat
  spentOrderDigests : List (BitVec 256)

inductive DarkBazaarAuthError where
  | unauthorizedGuardianCommittee
  | orderPayloadReplay (digest256 : BitVec 256)
  | traceError (err : DarkBazaarTraceError)
  deriving DecidableEq, Repr

/-- Authenticated multi-epoch step binding guardian committee authorization and 256-bit order nullifiers. -/
def stepDarkBazaarEpochAuth {sableDim : Nat} (cfg : ThresholdDecryptConfig)
    (st : DarkBazaarAuthState) (batch : DarkBazaarEpochBatch sableDim cfg) :
    Except DarkBazaarAuthError (DarkBazaarAuthState × DarkBazaarClearedOutcome cfg.params.d) :=
  if !checkAuthorizedCommittee st.committee batch.thresholdShares then
    .error .unauthorizedGuardianCommittee
  else
    let ordDig := deriveOrderBatchNullifier256 batch.openingQuery.market
      batch.openingQuery.committedOrders batch.encryptedOrders
    if st.spentOrderDigests.contains ordDig then
      .error (.orderPayloadReplay ordDig)
    else
      match stepDarkBazaarEpoch cfg st.base batch with
      | .error e => .error (.traceError e)
      | .ok (base', out) =>
        .ok ({ st with base := base', spentOrderDigests := ordDig :: st.spentOrderDigests }, out)

/-- **Order-Payload Replay Refusal (`stepDarkBazaarEpochAuth_refuses_order_replay`)**:
re-submitting the same `(market, committedOrders, encryptedOrders)` in any subsequent state is refused
even when the caller supplies a fresh `b₂.epochNullifier`! -/
theorem stepDarkBazaarEpochAuth_refuses_order_replay {sableDim : Nat} (cfg : ThresholdDecryptConfig)
    (st st₁ st₂ : DarkBazaarAuthState) (b₁ b₂ : DarkBazaarEpochBatch sableDim cfg)
    (out₁ : DarkBazaarClearedOutcome cfg.params.d)
    (hStep₁ : stepDarkBazaarEpochAuth cfg st b₁ = .ok (st₁, out₁))
    (hMono : ∀ d ∈ st₁.spentOrderDigests, d ∈ st₂.spentOrderDigests)
    (hMkt : b₂.openingQuery.market = b₁.openingQuery.market)
    (hSpecs : b₂.openingQuery.committedOrders = b₁.openingQuery.committedOrders)
    (hCts : b₂.encryptedOrders = b₁.encryptedOrders) :
    (∀ st₃ out₂, stepDarkBazaarEpochAuth cfg st₂ b₂ ≠ .ok (st₃, out₂)) ∧
    (checkAuthorizedCommittee st₂.committee b₂.thresholdShares = true →
      stepDarkBazaarEpochAuth cfg st₂ b₂ = .error (.orderPayloadReplay
        (deriveOrderBatchNullifier256 b₁.openingQuery.market b₁.openingQuery.committedOrders b₁.encryptedOrders))) := by
  unfold stepDarkBazaarEpochAuth at hStep₁
  cases hComm₁ : checkAuthorizedCommittee st.committee b₁.thresholdShares
  · simp [hComm₁] at hStep₁
  simp only [hComm₁, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep₁
  cases hSpent₁ : st.spentOrderDigests.contains
      (deriveOrderBatchNullifier256 b₁.openingQuery.market b₁.openingQuery.committedOrders b₁.encryptedOrders)
  · simp only [hSpent₁, Bool.false_eq_true, ↓reduceIte] at hStep₁
    cases hBase₁ : stepDarkBazaarEpoch cfg st.base b₁ with
    | error e => simp [hBase₁] at hStep₁
    | ok pair =>
      simp only [hBase₁, Except.ok.injEq, Prod.mk.injEq] at hStep₁
      have hMem₁ : deriveOrderBatchNullifier256 b₁.openingQuery.market b₁.openingQuery.committedOrders b₁.encryptedOrders ∈
          st₁.spentOrderDigests := by rw [← hStep₁.1]; exact List.Mem.head _
      have hMem₂ : deriveOrderBatchNullifier256 b₁.openingQuery.market b₁.openingQuery.committedOrders b₁.encryptedOrders ∈
          st₂.spentOrderDigests := hMono _ hMem₁
      refine ⟨fun st₃ out₂ => ?_, fun hComm₂ => ?_⟩
      · unfold stepDarkBazaarEpochAuth; rw [hMkt, hSpecs, hCts]
        cases checkAuthorizedCommittee st₂.committee b₂.thresholdShares <;> simp [hMem₂]
      · unfold stepDarkBazaarEpochAuth; rw [hComm₂, hMkt, hSpecs, hCts]; simp [hMem₂]
  · rw [hSpent₁] at hStep₁; cases hStep₁
end Obend.Crypto
end
