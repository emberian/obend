module
public import Obend.Crypto.BinaryTower256
import all Obend.Crypto.BinaryTower256
import Obend.Tactic.Tooth

/-!
# `Obend.Crypto.Tower256TracePack` — Frigo–shelat (`eprint 2026/2770`) Trace-Duality
`256`-Bit Bijective Packing & Constructive Additive Hilbert-90 Single-Mask ZK

Pure Lean 4.35 (`0 sorry`, `0 axiom`, `0 native_decide`, `0 Classical.choice`) formalization
over `Obend.Crypto.BinaryTower256.TowerElem k` with `Spec ↔ Exec` (`BitVec (2^k)`) refinement
and `#tooth` mutation witnesses.
-/

public section
namespace Obend.Crypto.Tower256TracePack

open Obend.Crypto
open Obend.Crypto.BinaryTower256

set_option autoImplicit false

private theorem lt_pow2_succ {k n : Nat} (h : n < 2 ^ k) : n < 2 ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_two]; omega
private theorem add_pow2_lt {k n : Nat} (h : n < 2 ^ k) : 2 ^ k + n < 2 ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_two]; omega
private theorem sub_pow2_lt {k n : Nat} (h1 : n < 2 ^ (k + 1)) (h2 : ¬ n < 2 ^ k) : n - 2 ^ k < 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_two] at h1; omega

/-! ## §1. Characteristic-2 Squaring, Frobenius, & `BitVec` Parity-Mask Trace -/

def towerSq (k : Nat) (a : TowerElem k) : TowerElem k := towerMul k a a
def sqExec (k : Nat) (a : TowerBitVec k) : TowerBitVec k := mulExec k a a

theorem sqExec_refines (k : Nat) (a : TowerElem k) :
    sqExec k (packTower k a) = packTower k (towerSq k a) := mulExec_refines k a a

/-- Characteristic-2 Freshman's Dream: `(a + b)^2 = a^2 + b^2`. -/
theorem frobenius_add (k : Nat) (a b : TowerElem k) :
    towerSq k (towerAdd k a b) = towerAdd k (towerSq k a) (towerSq k b) := by
  unfold towerSq
  rw [towerMul_add_distrib, towerAdd_mul_distrib, towerAdd_mul_distrib,
    towerMul_comm k b a, towerAdd_assoc, ← towerAdd_assoc k (towerMul k a b),
    towerAdd_self_zero, towerZero_add]

theorem towerSq_mul (k : Nat) (a b : TowerElem k) :
    towerSq k (towerMul k a b) = towerMul k (towerSq k a) (towerSq k b) := by
  unfold towerSq
  rw [towerMul_assoc, towerMul_left_comm_of_assoc k (towerMul_assoc k) b a b, ← towerMul_assoc]

theorem towerSq_injective (k : Nat) (a b : TowerElem k) (h : towerSq k a = towerSq k b) : a = b := by
  have hdiff : towerSq k (towerAdd k a b) = towerZero k := by rw [frobenius_add, h, towerAdd_self_zero]
  have hz : towerAdd k a b = towerZero k := by
    rcases (towerMul_eq_zero_iff k (towerAdd k a b) (towerAdd k a b)).mp hdiff with h0 | h0 <;> exact h0
  have he := congrArg (towerAdd k a) hz
  rw [towerAdd_cancel, towerAdd_zero] at he; exact he.symm

def bitDotAux (w : Nat) (u v : BitVec w) : Nat → Bool
  | 0 => false
  | n + 1 => bitDotAux w u v n ^^ (u.getLsbD n && v.getLsbD n)
def bitDot (w : Nat) (u v : BitVec w) : Bool := bitDotAux w u v w

private theorem bitDotAux_comm (w : Nat) (u v : BitVec w) (n : Nat) : bitDotAux w u v n = bitDotAux w v u n := by
  induction n with | zero => rfl | succ n ih => simp [bitDotAux, ih, Bool.and_comm]
theorem bitDot_comm (w : Nat) (u v : BitVec w) : bitDot w u v = bitDot w v u := bitDotAux_comm w u v w

private theorem bitDotAux_xor_right (w : Nat) (u v₁ v₂ : BitVec w) (n : Nat) :
    bitDotAux w u (v₁ ^^^ v₂) n = (bitDotAux w u v₁ n ^^ bitDotAux w u v₂ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bitDotAux, ih, BitVec.getLsbD_xor]
    cases u.getLsbD n <;> cases v₁.getLsbD n <;> cases v₂.getLsbD n <;>
      cases bitDotAux w u v₁ n <;> cases bitDotAux w u v₂ n <;> rfl
theorem bitDot_xor_right (w : Nat) (u v₁ v₂ : BitVec w) :
    bitDot w u (v₁ ^^^ v₂) = (bitDot w u v₁ ^^ bitDot w u v₂) := bitDotAux_xor_right w u v₁ v₂ w
theorem bitDot_xor_left (w : Nat) (u₁ u₂ v : BitVec w) :
    bitDot w (u₁ ^^^ u₂) v = (bitDot w u₁ v ^^ bitDot w u₂ v) := by
  rw [bitDot_comm, bitDot_xor_right, bitDot_comm w v u₁, bitDot_comm w v u₂]

private theorem bitDotAux_zero_left (w : Nat) (v : BitVec w) (n : Nat) : bitDotAux w (0#w) v n = false := by
  induction n with | zero => rfl | succ n ih => simp [bitDotAux, ih]
theorem bitDot_zero_left (w : Nat) (v : BitVec w) : bitDot w (0#w) v = false := bitDotAux_zero_left w v w

private theorem joinBits_getLsbD_low (k : Nat) (lo hi : TowerBitVec k) {n : Nat} (hn : n < 2 ^ k) :
    (joinBits k lo hi).getLsbD n = lo.getLsbD n := by
  simp only [joinBits, BitVec.getLsbD_cast, BitVec.getLsbD_append]
  split
  · rfl
  · omega

private theorem joinBits_getLsbD_high (k : Nat) (lo hi : TowerBitVec k) {n : Nat} :
    (joinBits k lo hi).getLsbD (2 ^ k + n) = hi.getLsbD n := by
  simp only [joinBits, BitVec.getLsbD_cast, BitVec.getLsbD_append]
  split
  · omega
  · simp [Nat.add_sub_cancel_left]

private theorem bitDotAux_join_low (k : Nat) (u₀ u₁ v₀ v₁ : TowerBitVec k) :
    ∀ n, n ≤ 2 ^ k → bitDotAux (2 ^ (k + 1)) (joinBits k u₀ u₁) (joinBits k v₀ v₁) n = bitDotAux (2 ^ k) u₀ v₀ n
  | 0, _ => rfl
  | n + 1, hn => by
    have hlt : n < 2 ^ k := by omega
    simp only [bitDotAux, bitDotAux_join_low k u₀ u₁ v₀ v₁ n (by omega),
      joinBits_getLsbD_low k u₀ u₁ hlt, joinBits_getLsbD_low k v₀ v₁ hlt]

private theorem bitDotAux_join_high (k : Nat) (u₀ u₁ v₀ v₁ : TowerBitVec k) :
    ∀ n, n ≤ 2 ^ k → bitDotAux (2 ^ (k + 1)) (joinBits k u₀ u₁) (joinBits k v₀ v₁) (2 ^ k + n) =
      (bitDot (2 ^ k) u₀ v₀ ^^ bitDotAux (2 ^ k) u₁ v₁ n)
  | 0, _ => by simpa [bitDot, bitDotAux] using bitDotAux_join_low k u₀ u₁ v₀ v₁ (2 ^ k) (Nat.le_refl _)
  | n + 1, hn => by
    have ih := bitDotAux_join_high k u₀ u₁ v₀ v₁ n (by omega)
    rw [show 2 ^ k + (n + 1) = (2 ^ k + n) + 1 by omega]
    simp only [bitDotAux, ih, joinBits_getLsbD_high, Bool.xor_assoc]

theorem bitDot_join (k : Nat) (u₀ u₁ v₀ v₁ : TowerBitVec k) :
    bitDot (2 ^ (k + 1)) (joinBits k u₀ u₁) (joinBits k v₀ v₁) =
      (bitDot (2 ^ k) u₀ v₀ ^^ bitDot (2 ^ k) u₁ v₁) := by
  have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
  unfold bitDot
  have haux : bitDotAux (2 ^ (k + 1)) (joinBits k u₀ u₁) (joinBits k v₀ v₁) (2 ^ k + 2 ^ k) =
      (bitDot (2 ^ k) u₀ v₀ ^^ bitDot (2 ^ k) u₁ v₁) :=
    bitDotAux_join_high k u₀ u₁ v₀ v₁ (2 ^ k) (Nat.le_refl _)
  rw [← h2] at haux; exact haux

/-- Self-adjointness of `scaleXExec` over `GF(2)`: `⟨u, X_k v⟩ = ⟨X_k u, v⟩`. -/
theorem bitDot_scaleXExec (k : Nat) (u v : TowerBitVec k) :
    bitDot (2 ^ k) u (scaleXExec k v) = bitDot (2 ^ k) (scaleXExec k u) v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    conv => lhs; rw [← joinBits_split k u, scaleXExec, bitDot_join, bitDot_xor_right, ih]
    conv => rhs; rw [← joinBits_split k v, scaleXExec, bitDot_join, bitDot_xor_left]
    cases bitDot (2 ^ k) (lowBits k u) (highBits k v) <;>
      cases bitDot (2 ^ k) (highBits k u) (lowBits k v) <;>
      cases bitDot (2 ^ k) (scaleXExec k (highBits k u)) (highBits k v) <;> rfl

def traceMask : (k : Nat) → TowerBitVec k
  | 0 => 1#1
  | k + 1 => joinBits k (0#(2 ^ k)) (scaleXExec k (traceMask k))
def traceExec (k : Nat) (x : TowerBitVec k) : Bool := bitDot (2 ^ k) (traceMask k) x

/-- Exact `Spec ↔ Exec` trace refinement: `traceExec k (packTower k a) = towerTrace k a`. -/
theorem traceExec_refines (k : Nat) (a : TowerElem k) : traceExec k (packTower k a) = towerTrace k a := by
  induction k with
  | zero => cases a <;> decide
  | succ k ih =>
    cases a with
    | mk lo hi =>
      change bitDot (2 ^ (k + 1)) (joinBits k (0#(2 ^ k)) (scaleXExec k (traceMask k)))
        (joinBits k (packTower k lo) (packTower k hi)) = towerTrace k (towerMul k (towerX k) hi)
      rw [bitDot_join, bitDot_zero_left, Bool.false_xor, ← bitDot_scaleXExec, scaleXExec_refines]
      have hrec : bitDot (2 ^ k) (traceMask k) (packTower k (towerScaleX k hi)) = towerTrace k (towerScaleX k hi) :=
        ih (towerScaleX k hi)
      rw [hrec, towerScaleX_eq_mul]

/-- Fan–Paar `T_8` tooth: bit 255 (`X_0 ... X_7`) has trace `0`, while `towerX 8` (bit 128) has trace `1`. -/
theorem tooth_top_monomial_trace_zero_T8 :
    traceMask 8 = 0x26c6636dc63a6da5c63a6da56da5a55700000000000000000000000000000000#256 ∧
    traceExec 8 (1#256 <<< 255) = false ∧ traceExec 8 (1#256 <<< 128) = true := by decide +kernel

/-! ## §2. Canonical Basis, Unique Recursive Dual Basis, & Bijective Bit Packing -/

def basisElem : (k : Nat) → Fin (2 ^ k) → TowerElem k
  | 0, _ => true
  | k + 1, i =>
    if h : i.val < 2 ^ k then (basisElem k ⟨i.val, h⟩, towerZero k)
    else (towerZero k, basisElem k ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt h⟩)

def dualBasis : (k : Nat) → Fin (2 ^ k) → TowerElem k
  | 0, _ => true
  | k + 1, i =>
    if h : i.val < 2 ^ k then
      let a := dualBasis k ⟨i.val, h⟩; (a, towerMul k (towerInvX k) a)
    else
      let a := dualBasis k ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt h⟩; (towerMul k (towerInvX k) a, towerZero k)

def invXExec : (k : Nat) → TowerBitVec k
  | 0 => 1#1
  | k + 1 => joinBits k (packTower k (towerX k)) (packTower k (towerOne k))
theorem invXExec_refines (k : Nat) : invXExec k = packTower k (towerInvX k) := by cases k <;> rfl

def dualBasisExec : (k : Nat) → Array (TowerBitVec k)
  | 0 => #[1#1]
  | k + 1 =>
    let prev := dualBasisExec k; let ix := invXExec k
    prev.map (fun a => joinBits k a (mulExec k ix a)) ++
      prev.map (fun a => joinBits k (mulExec k ix a) (0#(2 ^ k)))

theorem dualBasisExec_size (k : Nat) : (dualBasisExec k).size = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [dualBasisExec, Array.size_append, Array.size_map, ih, Nat.pow_succ, Nat.mul_two]

private theorem packTower_zero (k : Nat) : packTower k (towerZero k) = 0#(2 ^ k) := by
  induction k with | zero => rfl | succ k ih => simp [towerZero, packTower, ih, joinBits]

theorem dualBasisExec_refines (k : Nat) (i : Fin (2 ^ k)) :
    (dualBasisExec k)[i.val]'(by rw [dualBasisExec_size]; exact i.isLt) = packTower k (dualBasis k i) := by
  induction k with
  | zero => simp [dualBasisExec, dualBasis, packTower]
  | succ k ih =>
    simp only [dualBasisExec, dualBasis]
    have hsz : ((dualBasisExec k).map fun a => joinBits k a (mulExec k (invXExec k) a)).size = 2 ^ k := by
      simp [dualBasisExec_size]
    by_cases h : i.val < 2 ^ k
    · rw [Array.getElem_append_left (by omega), Array.getElem_map]
      simp only [h, ↓reduceDIte]
      rw [ih ⟨i.val, h⟩, invXExec_refines, mulExec_refines]; rfl
    · rw [Array.getElem_append_right (by omega), Array.getElem_map]
      simp only [h, ↓reduceDIte, hsz]
      rw [ih ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt h⟩, invXExec_refines, mulExec_refines, ← packTower_zero k]; rfl

/-- **Dual-Basis Biorthogonality:** `Tr_k(α_i · β_j) = (i == j)` for all `k, i, j`. -/
theorem dual_basis_biorthogonal (k : Nat) (i j : Fin (2 ^ k)) :
    towerTrace k (towerMul k (dualBasis k i) (basisElem k j)) = decide (i.val = j.val) := by
  induction k with
  | zero =>
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
    have hj : j = ⟨0, by decide⟩ := Fin.ext (by have := j.isLt; omega)
    subst hi; subst hj; rfl
  | succ k ih =>
    by_cases hi : i.val < 2 ^ k <;> by_cases hj : j.val < 2 ^ k
    · simp only [dualBasis, basisElem, hi, hj, ↓reduceDIte, towerTrace, towerMul, towerMul_zero,
        towerZero_add, towerAdd_zero]
      rw [← towerMul_assoc, ← towerMul_assoc, towerX_mul_invX, towerOne_mul, ih ⟨i.val, hi⟩ ⟨j.val, hj⟩]
    · simp only [dualBasis, basisElem, hi, hj, ↓reduceDIte, towerTrace, towerMul, towerMul_zero, towerAdd_zero]
      rw [← towerMul_assoc k (towerX k), ← towerMul_assoc k (towerX k), towerX_mul_invX, towerOne_mul,
        towerAdd_self_zero, towerMul_zero, towerTrace_zero]
      have hne : i.val ≠ j.val := fun h => hj (h ▸ hi); simp [hne]
    · simp only [dualBasis, basisElem, hi, hj, ↓reduceDIte, towerTrace, towerMul, towerMul_zero,
        towerZero_mul, towerAdd_zero, towerTrace_zero]
      have hne : i.val ≠ j.val := fun h => hi (h ▸ hj); simp [hne]
    · simp only [dualBasis, basisElem, hi, hj, ↓reduceDIte, towerTrace, towerMul, towerZero_mul,
        towerMul_zero, towerAdd_zero]
      rw [← towerMul_assoc, ← towerMul_assoc, towerX_mul_invX, towerOne_mul,
        ih ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt hi⟩ ⟨j.val - 2 ^ k, sub_pow2_lt j.isLt hj⟩]
      have hiff : (i.val - 2 ^ k = j.val - 2 ^ k) ↔ (i.val = j.val) := by
        constructor
        · intro h
          have he := congrArg (· + 2 ^ k) h
          simpa only [Nat.sub_add_cancel (Nat.le_of_not_lt hi),
            Nat.sub_add_cancel (Nat.le_of_not_lt hj)] using he
        · intro h; exact congrArg (· - 2 ^ k) h
      exact decide_eq_decide.mpr hiff

def packBits : (k : Nat) → (Fin (2 ^ k) → Bool) → TowerElem k
  | 0, bits => bits ⟨0, by decide⟩
  | k + 1, bits => (packBits k (fun j => bits ⟨j.val, lt_pow2_succ j.isLt⟩),
                    packBits k (fun j => bits ⟨2 ^ k + j.val, add_pow2_lt j.isLt⟩))

def pluckBit (k : Nat) (i : Fin (2 ^ k)) (X : TowerElem k) : Bool :=
  towerTrace k (towerMul k (dualBasis k i) X)

private theorem pluckBit_succ_low (k : Nat) (j : Fin (2 ^ k)) (lo hi : TowerElem k) :
    pluckBit (k + 1) ⟨j.val, lt_pow2_succ j.isLt⟩ (lo, hi) = pluckBit k j lo := by
  simp only [pluckBit, dualBasis, j.isLt, ↓reduceDIte, Fin.eta, towerTrace, towerMul]
  have hsimp : towerMul k (towerX k) (towerAdd k (towerAdd k (towerMul k (dualBasis k j) hi)
      (towerMul k (towerMul k (towerInvX k) (dualBasis k j)) lo))
      (towerMul k (towerX k) (towerMul k (towerMul k (towerInvX k) (dualBasis k j)) hi))) =
      towerMul k (dualBasis k j) lo := by
    rw [← towerMul_assoc k (towerX k) (towerMul k (towerInvX k) (dualBasis k j)),
      ← towerMul_assoc k (towerX k) (towerInvX k), towerX_mul_invX, towerOne_mul,
      towerAdd_comm k (towerMul k (dualBasis k j) hi), towerAdd_assoc, towerAdd_self_zero, towerAdd_zero,
      ← towerMul_assoc k (towerX k), ← towerMul_assoc k (towerX k), towerX_mul_invX, towerOne_mul]
  rw [hsimp]

private theorem pluckBit_succ_high (k : Nat) (j : Fin (2 ^ k)) (lo hi : TowerElem k) :
    pluckBit (k + 1) ⟨2 ^ k + j.val, add_pow2_lt j.isLt⟩ (lo, hi) = pluckBit k j hi := by
  have hge : ¬ (2 ^ k + j.val < 2 ^ k) := by omega
  simp only [pluckBit, dualBasis, hge, ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta, towerTrace, towerMul]
  have hsimp : towerMul k (towerX k) (towerAdd k (towerAdd k
      (towerMul k (towerMul k (towerInvX k) (dualBasis k j)) hi) (towerMul k (towerZero k) lo))
      (towerMul k (towerX k) (towerMul k (towerZero k) hi))) = towerMul k (dualBasis k j) hi := by
    simp only [towerZero_mul, towerMul_zero, towerAdd_zero]
    rw [← towerMul_assoc, ← towerMul_assoc, towerX_mul_invX, towerOne_mul]
  rw [hsimp]

/-- **Left Inverse (`pluckBit ∘ packBits = id`):** zero bit-booleanity constraints needed! -/
theorem pluckBit_packBits_id (k : Nat) (bits : Fin (2 ^ k) → Bool) (i : Fin (2 ^ k)) :
    pluckBit k i (packBits k bits) = bits i := by
  induction k with
  | zero =>
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; omega)
    subst hi; unfold pluckBit packBits dualBasis
    cases hb : bits ⟨0, by decide⟩ <;> simp [towerTrace, towerMul]
  | succ k ih =>
    unfold packBits
    by_cases hi : i.val < 2 ^ k
    · have hidx : i = ⟨i.val, lt_pow2_succ hi⟩ := rfl
      rw [hidx, pluckBit_succ_low k ⟨i.val, hi⟩]
      exact ih (fun j => bits ⟨j.val, lt_pow2_succ j.isLt⟩) ⟨i.val, hi⟩
    · have hsub := sub_pow2_lt i.isLt hi
      have hidx : i = ⟨2 ^ k + (i.val - 2 ^ k), add_pow2_lt hsub⟩ :=
        Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hi)).symm
      rw [hidx, pluckBit_succ_high k ⟨i.val - 2 ^ k, hsub⟩]
      exact ih (fun j => bits ⟨2 ^ k + j.val, add_pow2_lt j.isLt⟩) ⟨i.val - 2 ^ k, hsub⟩

/-- **Right Inverse (`packBits ∘ pluckBit = id`):** exact `GF(2)`-linear bijection! -/
theorem packBits_pluckBit_id (k : Nat) (X : TowerElem k) : packBits k (fun i => pluckBit k i X) = X := by
  induction k with
  | zero => cases X <;> rfl
  | succ k ih =>
    cases X with
    | mk lo hi =>
      change (packBits k (fun j => pluckBit (k + 1) ⟨j.val, lt_pow2_succ j.isLt⟩ (lo, hi)),
              packBits k (fun j => pluckBit (k + 1) ⟨2 ^ k + j.val, add_pow2_lt j.isLt⟩ (lo, hi))) = (lo, hi)
      apply Prod.ext
      · simp only [pluckBit_succ_low]; exact ih lo
      · simp only [pluckBit_succ_high]; exact ih hi

/-- Uniqueness of the dual basis (`2026/2770` Lemma 3.1(3)) without `Classical.choice`. -/
theorem dual_basis_unique (k : Nat) (i : Fin (2 ^ k)) (α' : TowerElem k)
    (hb : ∀ j : Fin (2 ^ k), towerTrace k (towerMul k α' (basisElem k j)) = decide (i.val = j.val)) :
    α' = dualBasis k i := by
  let d := towerAdd k α' (dualBasis k i)
  have hzero : ∀ X : TowerElem k, towerTrace k (towerMul k d X) = false := by
    have hpack : ∀ m : Nat, ∀ (v Y : TowerElem m),
        (∀ j : Fin (2 ^ m), towerTrace m (towerMul m v (basisElem m j)) = false) →
        towerTrace m (towerMul m v Y) = false := by
      intro m; induction m with
      | zero =>
        intro v Y hv; cases Y
        · cases v <;> rfl
        · exact hv ⟨0, by decide⟩
      | succ m ihm =>
        intro v Y hv; cases Y with
        | mk y0 y1 =>
          have hpair : (y0, y1) = towerAdd (m + 1) (y0, towerZero m) (towerZero m, y1) :=
            Prod.ext (towerAdd_zero m y0).symm (towerZero_add m y1).symm
          have hsplit : towerMul (m + 1) v (y0, y1) =
              towerAdd (m + 1) (towerMul (m + 1) v (y0, towerZero m)) (towerMul (m + 1) v (towerZero m, y1)) := by
            conv => lhs; rw [hpair]
            exact towerMul_add_distrib (m + 1) v (y0, towerZero m) (towerZero m, y1)
          rw [hsplit, towerTrace_add]
          have hred0 : ∀ w : TowerElem m, towerTrace (m + 1) (towerMul (m + 1) v (w, towerZero m)) =
              towerTrace m (towerMul m (towerMul m (towerX m) v.2) w) := fun w => by
            simp only [towerTrace, towerMul, towerMul_zero, towerZero_add, towerAdd_zero, towerMul_assoc]
          have hred1 : ∀ w : TowerElem m, towerTrace (m + 1) (towerMul (m + 1) v (towerZero m, w)) =
              towerTrace m (towerMul m (towerMul m (towerX m) (towerAdd m v.1 (towerMul m (towerX m) v.2))) w) := fun w => by
            simp only [towerTrace, towerMul, towerMul_zero, towerAdd_zero, towerMul_add_distrib,
              towerAdd_mul_distrib, towerMul_assoc]
          have h1 : towerTrace (m + 1) (towerMul (m + 1) v (y0, towerZero m)) = false := by
            rw [hred0 y0]; apply ihm _ y0; intro j
            have hvj := hv ⟨j.val, lt_pow2_succ j.isLt⟩
            simp only [basisElem, j.isLt, ↓reduceDIte] at hvj; rw [hred0] at hvj; exact hvj
          have h2 : towerTrace (m + 1) (towerMul (m + 1) v (towerZero m, y1)) = false := by
            rw [hred1 y1]; apply ihm _ y1; intro j
            have hvj := hv ⟨2 ^ m + j.val, add_pow2_lt j.isLt⟩
            have hge : ¬ (2 ^ m + j.val < 2 ^ m) := by omega
            simp only [basisElem, hge, ↓reduceDIte, Nat.add_sub_cancel_left] at hvj; rw [hred1] at hvj; exact hvj
          rw [h1, h2]; rfl
    intro X; apply hpack k d X; intro j
    rw [towerAdd_mul_distrib, towerTrace_add, hb j, dual_basis_biorthogonal, Bool.xor_self]
  if hd0 : d = towerZero k then
    have he := congrArg (towerAdd k (dualBasis k i)) hd0
    dsimp only [d] at he
    rw [towerAdd_comm k α', towerAdd_cancel, towerAdd_zero] at he; exact he
  else
    have hc := hzero (towerMul k (towerInv k d) (towerX k))
    rw [← towerMul_assoc, towerMul_inv k d hd0, towerOne_mul, towerTrace_X] at hc; cases hc

/-! ## §3. Constructive Additive Hilbert Theorem 90 (`0 Classical.choice`) -/

def artinSchreier (k : Nat) (t : TowerElem k) : TowerElem k := towerAdd k (towerSq k t) t

theorem artinSchreier_add (k : Nat) (u v : TowerElem k) :
    artinSchreier k (towerAdd k u v) = towerAdd k (artinSchreier k u) (artinSchreier k v) := by
  unfold artinSchreier; rw [frobenius_add, towerAdd_assoc, towerAdd_left_comm k (towerSq k v) u v, ← towerAdd_assoc]

theorem towerTrace_artinSchreier (k : Nat) (t : TowerElem k) : towerTrace k (artinSchreier k t) = false := by
  unfold artinSchreier towerSq; rw [towerTrace_add, towerTrace_square, Bool.xor_self]

private theorem solveArtinSchreier_flip_trace (k : Nat) (z0 t1₀ : TowerElem k)
    (htr : ¬ towerTrace k (towerAdd k z0 (towerSq k t1₀)) = false) :
    towerTrace k (towerAdd k z0 (towerSq k (towerAdd k t1₀ (towerInvX k)))) = false := by
  have htr0 : towerTrace k (towerAdd k z0 (towerSq k t1₀)) = true := by
    cases h : towerTrace k (towerAdd k z0 (towerSq k t1₀)) <;> simp_all
  have heq : towerAdd k z0 (towerSq k (towerAdd k t1₀ (towerInvX k))) =
      towerAdd k (towerAdd k z0 (towerSq k t1₀)) (towerSq k (towerInvX k)) := by
    rw [frobenius_add, towerAdd_assoc]
  rw [heq, towerTrace_add, htr0, towerSq, towerTrace_square, towerTrace_invX]; rfl

private def towerMk {k : Nat} (lo hi : TowerElem k) : TowerElem (k + 1) := (lo, hi)
private def towerLo {k : Nat} (z : TowerElem (k + 1)) : TowerElem k := z.1
private def towerHi {k : Nat} (z : TowerElem (k + 1)) : TowerElem k := z.2

private theorem towerTrace_succ_snd (k : Nat) (z : TowerElem (k + 1))
    (hz : towerTrace (k + 1) z = false) :
    towerTrace k (towerMul k (towerX k) (towerHi z)) = false := hz

/-- Constructive recursive Artin–Schreier solver (`0 Classical.choice`). -/
def solveArtinSchreier : (k : Nat) → (z : TowerElem k) → towerTrace k z = false → TowerElem k
  | 0, _, _ => false
  | k + 1, z, hz =>
    let u := solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz)
    let t1₀ := towerMul k (towerInvX k) u
    if htr : towerTrace k (towerAdd k (towerLo z) (towerSq k t1₀)) = false then
      towerMk (solveArtinSchreier k (towerAdd k (towerLo z) (towerSq k t1₀)) htr) t1₀
    else
      towerMk (solveArtinSchreier k (towerAdd k (towerLo z) (towerSq k (towerAdd k t1₀ (towerInvX k))))
        (solveArtinSchreier_flip_trace k (towerLo z) t1₀ htr)) (towerAdd k t1₀ (towerInvX k))

theorem solveArtinSchreier_spec :
    ∀ (k : Nat) (z : TowerElem k) (hz : towerTrace k z = false),
      artinSchreier k (solveArtinSchreier k z hz) = z
  | 0, false, _ => rfl
  | 0, true, hz => by cases hz
  | k + 1, z, hz => by
    have step : ∀ (t0 t1 : TowerElem k), artinSchreier k t0 = towerAdd k (towerLo z) (towerSq k t1) →
        artinSchreier k (towerMul k (towerX k) t1) = towerMul k (towerX k) (towerHi z) →
        artinSchreier (k + 1) (towerMk t0 t1) = z := by
      intro t0 t1 h0 h1; apply Prod.ext
      · change towerAdd k (towerAdd k (towerMul k t0 t0) (towerMul k t1 t1)) t0 = towerLo z
        rw [towerAdd_comm k (towerMul k t0 t0), towerAdd_assoc, towerAdd_comm k (towerMul k t0 t0)]
        have h0' : towerAdd k (towerMul k t0 t0) t0 = towerAdd k (towerLo z) (towerMul k t1 t1) := h0
        rw [towerAdd_comm k t0, h0', towerAdd_comm k (towerLo z), towerAdd_cancel]
      · change towerAdd k (towerAdd k (towerAdd k (towerMul k t0 t1) (towerMul k t1 t0))
          (towerMul k (towerX k) (towerMul k t1 t1))) t1 = towerHi z
        rw [towerMul_comm k t1 t0, towerAdd_self_zero, towerZero_add]
        have hmul := congrArg (towerMul k (towerInvX k)) h1
        rw [artinSchreier, towerSq, towerMul_add_distrib] at hmul
        have h1a : towerMul k (towerInvX k) (towerMul k (towerMul k (towerX k) t1) (towerMul k (towerX k) t1)) =
            towerMul k (towerX k) (towerMul k t1 t1) := by
          rw [← towerMul_assoc, ← towerMul_assoc, ← towerMul_assoc, towerMul_comm k (towerInvX k) (towerX k),
            towerX_mul_invX, towerOne_mul, towerMul_assoc, towerMul_left_comm_of_assoc k (towerMul_assoc k) t1 (towerX k) t1]
        have h1b : towerMul k (towerInvX k) (towerMul k (towerX k) t1) = t1 := by
          rw [← towerMul_assoc, towerMul_comm k (towerInvX k) (towerX k), towerX_mul_invX, towerOne_mul]
        have h1c : towerMul k (towerInvX k) (towerMul k (towerX k) (towerHi z)) = towerHi z := by
          rw [← towerMul_assoc, towerMul_comm k (towerInvX k) (towerX k), towerX_mul_invX, towerOne_mul]
        rw [h1a, h1b, h1c] at hmul; exact hmul
    simp only [solveArtinSchreier]
    let u := solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz)
    have hu : artinSchreier k u = towerMul k (towerX k) (towerHi z) :=
      solveArtinSchreier_spec k _ (towerTrace_succ_snd k z hz)
    let t1₀ := towerMul k (towerInvX k) u
    have hxt0 : towerMul k (towerX k) t1₀ = u := by
      dsimp only [t1₀]; rw [← towerMul_assoc, towerX_mul_invX, towerOne_mul]
    split
    · rename_i htr; exact step _ t1₀ (solveArtinSchreier_spec k _ htr) (by rw [hxt0]; exact hu)
    · rename_i htr
      have hxt1 : towerMul k (towerX k) (towerAdd k t1₀ (towerInvX k)) = towerAdd k u (towerOne k) := by
        rw [towerMul_add_distrib, hxt0, towerX_mul_invX]
      have hu1 : artinSchreier k (towerAdd k u (towerOne k)) = towerMul k (towerX k) (towerHi z) := by
        rw [artinSchreier_add, hu]
        have h1z : artinSchreier k (towerOne k) = towerZero k := by unfold artinSchreier towerSq; rw [towerMul_one, towerAdd_self_zero]
        rw [h1z, towerAdd_zero]
      exact step _ _ (solveArtinSchreier_spec k _ _) (by rw [hxt1]; exact hu1)

/-- **Additive Hilbert Theorem 90 (`2026/2770` Lemma 4.1):** `Tr_k(z) = 0 ↔ ∃ t, t^2 + t = z`. -/
theorem trace_eq_zero_iff_artin_schreier (k : Nat) (z : TowerElem k) :
    towerTrace k z = false ↔ ∃ t : TowerElem k, artinSchreier k t = z :=
  ⟨fun hz => ⟨solveArtinSchreier k z hz, solveArtinSchreier_spec k z hz⟩, fun ⟨t, ht⟩ => ht ▸ towerTrace_artinSchreier k t⟩

theorem trace_one_no_artin_schreier_root (k : Nat) (z : TowerElem k) (hz : towerTrace k z = true) :
    (∀ t : TowerElem k, artinSchreier k t ≠ z) ∧
    (∀ Z : TowerElem k, towerTrace k Z = false → towerTrace k (towerAdd k Z z) = true) := by
  refine ⟨fun t ht => ?_, fun Z hZ => by rw [towerTrace_add, hZ, hz]; rfl⟩
  have h0 := towerTrace_artinSchreier k t; rw [ht, hz] at h0; cases h0

theorem trace_one_witness_T8 : towerTrace 8 (towerX 8) = true := towerTrace_X 8

def solveArtinSchreierExec : (k : Nat) → TowerBitVec k → TowerBitVec k
  | 0, _ => 0#1
  | k + 1, z =>
    let z0 := lowBits k z; let z1 := highBits k z
    let u := solveArtinSchreierExec k (scaleXExec k z1); let ix := invXExec k
    let t1₀ := mulExec k ix u; let rhs₀ := z0 ^^^ sqExec k t1₀
    if traceExec k rhs₀ then let t1₁ := t1₀ ^^^ ix; joinBits k (solveArtinSchreierExec k (z0 ^^^ sqExec k t1₁)) t1₁
    else joinBits k (solveArtinSchreierExec k rhs₀) t1₀

theorem solveArtinSchreierExec_refines (k : Nat) (z : TowerElem k) (hz : towerTrace k z = false) :
    solveArtinSchreierExec k (packTower k z) = packTower k (solveArtinSchreier k z hz) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let u := solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz)
    let t1₀ := towerMul k (towerInvX k) u
    let rhs₀ := towerAdd k (towerLo z) (towerSq k t1₀)
    have hpk : packTower (k + 1) z = joinBits k (packTower k (towerLo z)) (packTower k (towerHi z)) := rfl
    have hmk : ∀ a b : TowerElem k, packTower (k + 1) (towerMk a b) = joinBits k (packTower k a) (packTower k b) :=
      fun _ _ => rfl
    have huE : solveArtinSchreierExec k (scaleXExec k (packTower k (towerHi z))) = packTower k u := by
      rw [scaleXExec_refines, towerScaleX_eq_mul]; exact ih (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz)
    have ht1E : mulExec k (invXExec k) (packTower k u) = packTower k t1₀ := by
      rw [invXExec_refines, mulExec_refines]
    have hrhsE : packTower k (towerLo z) ^^^ sqExec k (packTower k t1₀) = packTower k rhs₀ := by
      rw [sqExec_refines, ← packTower_add]
    rw [hpk]; unfold solveArtinSchreierExec
    simp only [lowBits_join, highBits_join]
    rw [huE, ht1E, hrhsE, traceExec_refines]
    cases htr : towerTrace k rhs₀
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have htr' : towerTrace k (towerAdd k (towerLo z) (towerSq k (towerMul k (towerInvX k)
          (solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz))))) = false := htr
      have hR : solveArtinSchreier (k + 1) z hz = towerMk (solveArtinSchreier k rhs₀ htr) t1₀ := by
        conv => lhs; unfold solveArtinSchreier
        dsimp only; rw [dite_eq_left_of_eq_true (eq_true htr')]
      rw [hR, hmk]; congr 1; exact ih rhs₀ htr
    · simp only [↓reduceIte]
      have htrF : ¬ (towerTrace k rhs₀ = false) := by rw [htr]; decide
      have htrF' : ¬ (towerTrace k (towerAdd k (towerLo z) (towerSq k (towerMul k (towerInvX k)
          (solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz))))) = false) := htrF
      have hR : solveArtinSchreier (k + 1) z hz =
          towerMk (solveArtinSchreier k (towerAdd k (towerLo z) (towerSq k (towerAdd k t1₀ (towerInvX k))))
            (solveArtinSchreier_flip_trace k (towerLo z) t1₀ htrF)) (towerAdd k t1₀ (towerInvX k)) := by
        conv => lhs; unfold solveArtinSchreier
        dsimp only; rw [dite_eq_right_of_eq_false (eq_false htrF')]
      rw [hR, hmk]
      have ht11 : packTower k t1₀ ^^^ invXExec k = packTower k (towerAdd k t1₀ (towerInvX k)) := by
        rw [invXExec_refines, ← packTower_add]
      have hrhs1 : packTower k (towerLo z) ^^^ sqExec k (packTower k (towerAdd k t1₀ (towerInvX k))) =
          packTower k (towerAdd k (towerLo z) (towerSq k (towerAdd k t1₀ (towerInvX k)))) := by
        rw [sqExec_refines, ← packTower_add]
      rw [ht11, hrhs1]; congr 1; exact ih _ (solveArtinSchreier_flip_trace k (towerLo z) t1₀ htrF)

/-! ## §4. Frigo–shelat §4 Frobenius Mask Folding & Single-Mask ZK Soundness -/

def listSum (k : Nat) : List (TowerElem k) → TowerElem k
  | [] => towerZero k
  | a :: rest => towerAdd k a (listSum k rest)

theorem listSum_map_add (k : Nat) {α : Type} (xs : List α) (f g : α → TowerElem k) :
    listSum k (xs.map fun x => towerAdd k (f x) (g x)) =
      towerAdd k (listSum k (xs.map f)) (listSum k (xs.map g)) := by
  induction xs with
  | nil => simp [listSum]
  | cons a rest ih => simp only [List.map_cons, listSum, ih]; rw [towerAdd_assoc, towerAdd_left_comm k (g a), ← towerAdd_assoc]

/-- **Frigo–shelat §4 Frobenius Folding:** `∑_j δ_j^2 t_j^2 = (∑_j δ_j t_j)^2`. -/
theorem frobenius_weighted_sum_sq (k : Nat) {α : Type} (xs : List α) (δ t : α → TowerElem k) :
    listSum k (xs.map fun x => towerMul k (towerSq k (δ x)) (towerSq k (t x))) =
      towerSq k (listSum k (xs.map fun x => towerMul k (δ x) (t x))) := by
  induction xs with
  | nil => simp [listSum, towerSq]
  | cons p rest ih => simp only [List.map_cons, listSum, frobenius_add, ih, towerSq_mul]

/-- **Fig. 2 Single-Mask ZK Completeness (`0` quadratic PCS constraints).** -/
theorem zk_single_mask_completeness (k : Nat)
    (claims : List (TowerElem k × TowerElem k × TowerElem k)) (r : TowerElem k) :
    let U : TowerElem k × TowerElem k × TowerElem k → TowerElem k := fun p => towerAdd k p.1 (artinSchreier k p.2.1)
    let A := towerAdd k r (listSum k (claims.map fun p => towerMul k p.2.2 p.2.1))
    let b := towerSq k r
    towerAdd k (listSum k (claims.map fun p => towerMul k (towerSq k p.2.2) (U p))) (towerSq k A) =
      towerAdd k (towerAdd k (listSum k (claims.map fun p => towerMul k (towerSq k p.2.2) p.1))
        (listSum k (claims.map fun p => towerMul k (towerSq k p.2.2) p.2.1))) b := by
  intro U A b
  have hA2 : towerSq k A = towerAdd k b (listSum k (claims.map fun p => towerMul k (towerSq k p.2.2) (towerSq k p.2.1))) := by
    simp only [A, b, frobenius_add]
    rw [← frobenius_weighted_sum_sq k claims (fun p => p.2.2) (fun p => p.2.1)]
  have hU : listSum k (claims.map fun p => towerMul k (towerSq k p.2.2) (U p)) =
      towerAdd k (listSum k (claims.map fun p => towerMul k (towerSq k p.2.2) p.1))
        (towerAdd k (listSum k (claims.map fun p => towerMul k (towerSq k p.2.2) (towerSq k p.2.1)))
          (listSum k (claims.map fun p => towerMul k (towerSq k p.2.2) p.2.1))) := by
    have h1 : (claims.map fun p => towerMul k (towerSq k p.2.2) (U p)) =
        claims.map fun p => towerAdd k (towerMul k (towerSq k p.2.2) p.1)
          (towerAdd k (towerMul k (towerSq k p.2.2) (towerSq k p.2.1)) (towerMul k (towerSq k p.2.2) p.2.1)) := by
      congr 1; funext p; simp only [U, artinSchreier, towerMul_add_distrib]
    rw [h1, listSum_map_add, listSum_map_add]
  rw [hU, hA2]
  have hcancel : ∀ (x y z w : TowerElem k),
      towerAdd k (towerAdd k x (towerAdd k y z)) (towerAdd k w y) = towerAdd k (towerAdd k x z) w := fun x y z w => by
    rw [towerAdd_comm k w y, ← towerAdd_assoc k (towerAdd k x (towerAdd k y z)) y w,
      towerAdd_assoc k x (towerAdd k y z) y, towerAdd_comm k y z, towerAdd_assoc k z y y,
      towerAdd_self_zero, towerAdd_zero]
  exact hcancel _ _ _ _

/-- Theorem 3.4, conditional on the other batch weights. For a nonzero error
coordinate exactly one field challenge hits the target, for every fixed partial sum. -/
theorem linear_batching_unique_challenge (k : Nat) (err partialSum target : TowerElem k)
    (hne : err ≠ towerZero k) :
    ∃ hit : TowerElem k, ∀ challenge,
      towerAdd k partialSum (towerMul k err challenge) = target ↔ challenge = hit := by
  let hit := towerMul k (towerInv k err) (towerAdd k partialSum target)
  have hprod : towerMul k err hit = towerAdd k partialSum target := by
    simp only [hit, ← towerMul_assoc, towerMul_inv k err hne, towerOne_mul]
  refine ⟨hit, fun challenge => ⟨fun h => ?_, fun h => ?_⟩⟩
  · apply towerMul_cancel_left k err _ _ hne
    rw [hprod, ← h, towerAdd_cancel]
  · rw [h, hprod, towerAdd_cancel]

/-- **Single-Challenge Vandermonde Power-Batching Soundness (`≤ d` roots, `≤ 255 / 2^{256}` at `k = 8`).** -/
theorem power_batching_roots_le (k d : Nat) (es deltas : List (TowerElem k))
    (hnd : deltas.Nodup) (hlen : es.length ≤ d + 1)
    (hnz : ∃ δ, RoundPoly.evalCoeffs es δ ≠ towerZero k)
    (hzero : ∀ δ ∈ deltas, RoundPoly.evalCoeffs es δ = towerZero k) : deltas.length ≤ d := by
  have hb := RoundPoly.roots_nodup_length_le d es deltas hnd hlen hnz
  have hf : deltas.filter (fun δ => decide (RoundPoly.evalCoeffs es δ = towerZero k)) = deltas :=
    List.filter_eq_self.mpr fun δ hδ => by simp [hzero δ hδ]
  change (deltas.filter (fun δ => decide (RoundPoly.evalCoeffs es δ = towerZero k))).length ≤ d at hb
  rwa [hf] at hb

theorem power_batching_witness_T8 :
    ∃ (es deltas : List (TowerElem 8)), deltas.Nodup ∧ es.length ≤ 256 ∧
      (∃ δ, RoundPoly.evalCoeffs es δ ≠ towerZero 8) ∧
      (∀ δ ∈ deltas, RoundPoly.evalCoeffs es δ = towerZero 8) :=
  ⟨[towerX 8], [], List.nodup_nil, by decide,
    ⟨towerZero 8, fun h => by
      have ht := congrArg (towerTrace 8) h
      simp [RoundPoly.evalCoeffs, CommRingOps.zero, CommRingOps.add, CommRingOps.mul,
        towerTrace_X, towerTrace_zero] at ht⟩,
    fun _ h => by cases h⟩

/-! ## §5. `#tooth` Mutation-Sensitivity Witnesses -/

private def traceExecNaiveTopBitOnly (k : Nat) (x : TowerBitVec k) : Bool := x.getLsbD (2 ^ k - 1)

private def dualBasisDropInvX : (k : Nat) → Fin (2 ^ k) → TowerElem k
  | 0, _ => true
  | k + 1, i =>
    if h : i.val < 2 ^ k then let a := dualBasisDropInvX k ⟨i.val, h⟩; (a, a)
    else (dualBasisDropInvX k ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt h⟩, towerZero k)

private def artinSchreierTraceOneBug (k : Nat) (t : TowerElem k) : TowerElem k :=
  towerAdd k (towerAdd k (towerSq k t) t) (towerX k)

#tooth traceExec_refines by mutation traceExec := traceExecNaiveTopBitOnly
#tooth dual_basis_biorthogonal by mutation dualBasis := dualBasisDropInvX
#tooth towerTrace_artinSchreier by mutation artinSchreier := artinSchreierTraceOneBug

end Obend.Crypto.Tower256TracePack
