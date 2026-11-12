module
/-
# Obend.Crypto.Poseidon2Goldilocks — Algebraic Width-12 Goldilocks `Poseidon2` Permutation & 256-Bit Sponge

Closes the algebraic sponge gap noted in `Obend.Apps.ZkNtt` (`lines 30–32`) over the canonical
64-bit `Goldilocks` prime field ($p = 2^{64} - 2^{32} + 1 = 18446744069414584321$):

1. **Degree-7 S-Box Bijection (`sbox7_bijective`)**:
   - Since $p - 1 = 2^{32}(2^{32} - 1) = 2^{32} \cdot 3 \cdot 5 \cdot 17 \cdot 257 \cdot 65537$ is coprime
     to $7$, the exact inverse exponent $d_{\text{inv}} = \frac{4(p - 1) + 1}{7} = 10540996611094048183$
     satisfies $7 \cdot d_{\text{inv}} = 4(p - 1) + 1 \equiv 1 \pmod{p - 1}$.
   - Proves `(sbox7 x) ^ d_inv = x` and `(x ^ d_inv) ^ 7 = x` constructively via Fermat's Little Theorem
     (`IsPrimeNat.pow_sub_one_mod` from `Obend.Crypto.Sumcheck`).
2. **Full Width-12 (`rate = 8, capacity = 4` = 256-Bit Capacity) `Poseidon2` Permutation (`poseidon2Perm12`)**:
   - External linear layer $M_E = \text{circ}(2 M_4, M_4, M_4)$ built from the $4 \times 4$ MDS circulant
     $M_4 = \text{circ}(2, 3, 1, 1)$, proved strictly invertible (`applyMEInv_applyME`, `applyME_applyMEInv`).
   - Internal linear layer $M_I = \mathbf{1}\mathbf{1}^T + \text{diag}(-2, 1, 2, 4, \dots, 1024)$, proved
     strictly invertible via exact Sherman–Morrison reduction (`applyMIInv_applyMI`, `applyMI_applyMIInv`).
   - Full $R_F = 8$ external rounds (4 initial + 4 terminal) and $R_P = 22$ internal rounds with proved
     two-sided inverse permutation (`poseidon2Perm12Inv_left_inv`, `poseidon2Perm12_bijective`).
3. **Canonical `< 2^56` Limb Framing, Injective `10*1` Sponge Padding & `poseidon2Hash32`**:
   - Encodes arbitrary byte strings into `< 2^56` Goldilocks limbs (`bytesToLimbs56_lt_two_pow_56`,
     `bytesToLimbs56_injective`), applies multi-rate `10*1` rate-8 sponge padding (`poseidon2Pad_injective`),
     absorbs across `poseidon2Perm12`, and squeezes 4 canonical Goldilocks elements = 32-byte (256-bit)
     digest (`poseidon2Hash32 : HashBytes.Hash`, `poseidon2Hash32_length`).
-/
public import Obend.Apps.ZkNtt.Goldilocks
public import Obend.Digest.HashBytes
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck
public import Obend.Crypto.FastRing
public import Obend.Crypto.PCS

public section
namespace Obend.Crypto

open Obend.Apps.ZkNtt
open Obend.Digest.HashBytes
open Obend.Crypto.Fast

set_option autoImplicit false

/-! ## 1. Goldilocks Power Map $x \mapsto x^7 \pmod p$ & Exact Inverse $d_{\text{inv}}$ (`sbox7_bijective`) -/

/-- Exact inverse exponent $d_{\text{inv}} = \frac{4(p - 1) + 1}{7} = 10540996611094048183$
    satisfying $7 \cdot d_{\text{inv}} \equiv 1 \pmod{p - 1}$ on Goldilocks. -/
@[expose] def poseidon2DInv : Nat := 10540996611094048183

/-- Coprimality $\gcd(7, p - 1) = 1$, exact Fermat prime factorization of $p - 1$, and Bézout identity
    $7 \cdot d_{\text{inv}} = 4(p - 1) + 1$. -/
theorem goldilocksPred_coprime_seven (x : Goldilocks) :
    7 * poseidon2DInv = 4 * (goldilocksPrime - 1) + 1 ∧
    Nat.gcd 7 (goldilocksPrime - 1) = 1 ∧
    goldilocksPrime - 1 = (2 ^ 32) * 3 * 5 * 17 * 257 * 65537 ∧
    x.val < goldilocksPrime := by
  have hBez : 7 * poseidon2DInv = 4 * (goldilocksPrime - 1) + 1 := rfl
  refine ⟨hBez, ?_, rfl, x.isLt⟩
  obtain ⟨k1, hk1⟩ := Nat.gcd_dvd_left 7 (goldilocksPrime - 1)
  obtain ⟨k2, hk2⟩ := Nat.gcd_dvd_right 7 (goldilocksPrime - 1)
  let g := Nat.gcd 7 (goldilocksPrime - 1)
  have h1 : g ∣ 1 := ⟨k1 * poseidon2DInv - 4 * k2, by
    have h7 : 7 * poseidon2DInv = g * (k1 * poseidon2DInv) := by
      calc 7 * poseidon2DInv = (g * k1) * poseidon2DInv := by rw [← hk1]
      _ = g * (k1 * poseidon2DInv) := Nat.mul_assoc _ _ _
    have h4 : 4 * (goldilocksPrime - 1) = g * (4 * k2) := by
      calc 4 * (goldilocksPrime - 1) = 4 * (g * k2) := by rw [← hk2]
      _ = g * (4 * k2) := by rw [← Nat.mul_assoc, Nat.mul_comm 4 g, Nat.mul_assoc]
    rw [Nat.mul_sub_left_distrib, ← h7, ← h4]
    omega⟩
  exact Nat.eq_one_of_dvd_one h1

/-- Degree-7 algebraic S-box $x \mapsto x^7$ over `Goldilocks` computed via 4 field multiplications. -/
@[expose] def sbox7 (x : Goldilocks) : Goldilocks :=
  let x2 := Goldilocks.mul x x
  let x3 := Goldilocks.mul x2 x
  let x4 := Goldilocks.mul x2 x2
  Goldilocks.mul x3 x4

theorem sbox7_val (x : Goldilocks) :
    (sbox7 x).val = (x.val ^ 7) % goldilocksPrime := by
  have hx2 : (Goldilocks.mul x x).val = (x.val * x.val) % goldilocksPrime := Goldilocks.mul_val x x
  have hx3 : (Goldilocks.mul (Goldilocks.mul x x) x).val = (x.val * x.val * x.val) % goldilocksPrime := by
    rw [Goldilocks.mul_val, hx2, Nat.mod_mul_mod]
  have hx4 : (Goldilocks.mul (Goldilocks.mul x x) (Goldilocks.mul x x)).val =
      ((x.val * x.val) * (x.val * x.val)) % goldilocksPrime := by
    rw [Goldilocks.mul_val, hx2, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  unfold sbox7
  dsimp only
  rw [Goldilocks.mul_val, hx3, hx4, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]
  congr 1
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]

/-- Binary square-and-multiply exponentiation over `Goldilocks` (`O(log exp)` field multiplications). -/
def goldilocksPowAux : Nat → Goldilocks → Nat → Goldilocks
  | 0, _, _ => Goldilocks.one
  | fuel + 1, base, exp =>
    if exp = 0 then Goldilocks.one
    else
      let half := goldilocksPowAux fuel base (exp / 2)
      let sq := Goldilocks.mul half half
      if exp % 2 = 1 then Goldilocks.mul sq base else sq

@[expose] def goldilocksPow (x : Goldilocks) (exp : Nat) : Goldilocks :=
  if x.val == 0 then
    if exp == 0 then Goldilocks.one else Goldilocks.zero
  else
    goldilocksPowAux 64 x exp

/-- Exact inverse S-box $x \mapsto x^{d_{\text{inv}}}$ over `Goldilocks`. -/
@[expose] def sbox7Inv (x : Goldilocks) : Goldilocks :=
  goldilocksPow x poseidon2DInv

private theorem pow_two_mul_nat (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem goldilocksPowAux_val (fuel : Nat) (base : Goldilocks) :
    ∀ (exp : Nat), exp < 2 ^ fuel →
      (goldilocksPowAux fuel base exp).val = (base.val ^ exp) % goldilocksPrime := by
  induction fuel with
  | zero =>
    intro exp hlt
    have he0 : exp = 0 := by simp at hlt; omega
    subst he0
    rfl
  | succ fuel ih =>
    intro exp hlt
    simp only [goldilocksPowAux]
    if h0 : exp = 0 then
      subst h0
      rfl
    else
      simp only [h0, ↓reduceIte]
      have hexpHalf : exp / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hlt
        omega
      have ihHalf := ih (exp / 2) hexpHalf
      let half := goldilocksPowAux fuel base (exp / 2)
      have hsq : (Goldilocks.mul half half).val = (base.val ^ (2 * (exp / 2))) % goldilocksPrime := by
        rw [Goldilocks.mul_val, ihHalf, ← Nat.mul_mod, ← pow_two_mul_nat]
      have hmod2 : exp % 2 = 0 ∨ exp % 2 = 1 := by omega
      rcases hmod2 with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide, ↓reduceIte]
        have hexp : 2 * (exp / 2) = exp := by omega
        rw [hsq, hexp]
      · simp only [hr1, ↓reduceIte]
        have hexp : exp = 2 * (exp / 2) + 1 := by omega
        change (Goldilocks.mul (Goldilocks.mul half half) base).val = _
        rw [Goldilocks.mul_val, hsq, Nat.mod_mul_mod]
        conv => rhs; rw [hexp, Nat.pow_add, Nat.pow_one]

theorem goldilocksPow_val (x : Goldilocks) (exp : Nat) (hLt : exp < 2 ^ 64) :
    (goldilocksPow x exp).val = (x.val ^ exp) % goldilocksPrime := by
  unfold goldilocksPow
  cases hx0 : (x.val == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact goldilocksPowAux_val 64 x exp hLt
  · simp only [↓reduceIte]
    have hxEq : x.val = 0 := eq_of_beq hx0
    rw [hxEq]
    cases he0 : (exp == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have heNe : exp ≠ 0 := by intro h; subst h; simp at he0
      rw [Nat.zero_pow (Nat.pos_of_ne_zero heNe), Nat.zero_mod]
      rfl
    · simp only [↓reduceIte]
      have heEq : exp = 0 := eq_of_beq he0
      rw [heEq, Nat.pow_zero]
      rfl

theorem sbox7Inv_val (x : Goldilocks) :
    (sbox7Inv x).val = (x.val ^ poseidon2DInv) % goldilocksPrime := by
  unfold sbox7Inv
  exact goldilocksPow_val x poseidon2DInv (by decide)

private theorem pow_mod_congr_nat {x y m : Nat} (h : x % m = y % m) (k : Nat) :
    (x ^ k) % m = (y ^ k) % m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, h, ← Nat.mul_mod]

private theorem pow4_mod_one {u p : Nat} (hp : 1 < p) (hu : u % p = 1) :
    (u ^ 4) % p = 1 := by
  have h2 : u ^ 2 = u * u := by
    rw [show (2 : Nat) = 1 + 1 from rfl, Nat.pow_add, Nat.pow_one]
  have h4 : u ^ 4 = (u * u) * (u * u) := by
    rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add, h2]
  have hu2 : (u * u) % p = 1 := by
    rw [Nat.mul_mod, hu, Nat.one_mul, Nat.mod_eq_of_lt hp]
  rw [h4, Nat.mul_mod, hu2, Nat.one_mul, Nat.mod_eq_of_lt hp]

private theorem pow_seven_dInv_mod (a : Goldilocks) :
    (a.val ^ (7 * poseidon2DInv)) % goldilocksPrime = a.val := by
  if ha0 : a.val = 0 then
    have hexp0 : 7 * poseidon2DInv = (4 * (goldilocksPrime - 1)) + 1 := rfl
    rw [ha0, hexp0, Nat.zero_pow (by omega), Nat.zero_mod]
  else
    have hndvd : ¬ (goldilocksPrime ∣ a.val) := fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      have hlt := a.isLt
      omega
    have hflt : (a.val ^ (goldilocksPrime - 1)) % goldilocksPrime = 1 :=
      (goldilocksPrime_isPrime ()).pow_sub_one_mod hndvd
    have hexp : 7 * poseidon2DInv = (goldilocksPrime - 1) * 4 + 1 := rfl
    have hp1 : 1 < goldilocksPrime := by decide
    have hu4 : ((a.val ^ (goldilocksPrime - 1)) ^ 4) % goldilocksPrime = 1 :=
      pow4_mod_one hp1 hflt
    rw [hexp, Nat.pow_add, Nat.pow_mul, Nat.pow_one, Nat.mul_mod, hu4,
        Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt a.isLt]

theorem sbox7Inv_sbox7 (x : Goldilocks) : sbox7Inv (sbox7 x) = x := by
  apply Goldilocks.ext
  have hCongr : (sbox7 x).val % goldilocksPrime = (x.val ^ 7) % goldilocksPrime := by
    rw [sbox7_val, Nat.mod_mod]
  rw [sbox7Inv_val, pow_mod_congr_nat hCongr poseidon2DInv, ← Nat.pow_mul, pow_seven_dInv_mod]

theorem sbox7_sbox7Inv (x : Goldilocks) : sbox7 (sbox7Inv x) = x := by
  apply Goldilocks.ext
  have hCongr : (sbox7Inv x).val % goldilocksPrime = (x.val ^ poseidon2DInv) % goldilocksPrime := by
    rw [sbox7Inv_val, Nat.mod_mod]
  rw [sbox7_val, pow_mod_congr_nat hCongr 7, ← Nat.pow_mul, Nat.mul_comm poseidon2DInv 7, pow_seven_dInv_mod]

/-- **Goldilocks Degree-7 S-Box Bijection Theorem (`sbox7_bijective`)**:
    `sbox7` ($x \mapsto x^7 \pmod p$) and `sbox7Inv` ($x \mapsto x^{d_{\text{inv}}} \pmod p$) are
    strict two-sided inverses over `Goldilocks`, establishing injectivity and surjectivity. -/
theorem sbox7_bijective (x y : Goldilocks) :
    sbox7Inv (sbox7 x) = x ∧
    sbox7 (sbox7Inv y) = y ∧
    (sbox7 x = sbox7 y ↔ x = y) ∧
    (∃ z : Goldilocks, sbox7 z = y) := by
  refine ⟨sbox7Inv_sbox7 x, sbox7_sbox7Inv y, ?_, ⟨sbox7Inv y, sbox7_sbox7Inv y⟩⟩
  constructor
  · intro h
    have hInv := congrArg sbox7Inv h
    rwa [sbox7Inv_sbox7, sbox7Inv_sbox7] at hInv
  · intro h
    subst h
    rfl

/-! ## 2. Width-12 State (`rate = 8, capacity = 4`) & Invertible Linear Layers $M_E, M_I$ -/

/-- A 4-lane Goldilocks word block. -/
structure Lane4 where
  x0 : Goldilocks
  x1 : Goldilocks
  x2 : Goldilocks
  x3 : Goldilocks
  deriving DecidableEq, Repr

theorem Lane4.ext {a b : Lane4}
    (h0 : a.x0 = b.x0) (h1 : a.x1 = b.x1) (h2 : a.x2 = b.x2) (h3 : a.x3 = b.x3) : a = b := by
  cases a; cases b; simp only at *; subst h0 h1 h2 h3; rfl

/-- Full Width-12 Goldilocks sponge state:
    - Rate lanes `0..7`: `b0` (`0..3`) and `b1` (`4..7`) (`rate = 8`),
    - Capacity lanes `8..11`: `b2` (`capacity = 4` = 256 bits). -/
structure Poseidon2State12 where
  b0 : Lane4
  b1 : Lane4
  b2 : Lane4
  deriving DecidableEq, Repr

theorem Poseidon2State12.ext {s t : Poseidon2State12}
    (h0 : s.b0 = t.b0) (h1 : s.b1 = t.b1) (h2 : s.b2 = t.b2) : s = t := by
  cases s; cases t; simp only at *; subst h0 h1 h2; rfl

def Poseidon2State12.toList (s : Poseidon2State12) : List Goldilocks :=
  [s.b0.x0, s.b0.x1, s.b0.x2, s.b0.x3,
   s.b1.x0, s.b1.x1, s.b1.x2, s.b1.x3,
   s.b2.x0, s.b2.x1, s.b2.x2, s.b2.x3]

def Poseidon2State12.ofList12? : List Goldilocks → Option Poseidon2State12
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] =>
    some ⟨⟨x0, x1, x2, x3⟩, ⟨x4, x5, x6, x7⟩, ⟨x8, x9, x10, x11⟩⟩
  | _ => none

theorem Poseidon2State12.ofList12?_toList (s : Poseidon2State12) :
    Poseidon2State12.ofList12? s.toList = some s ∧ s.toList.length = 12 := by
  cases s with | mk b0 b1 b2 =>
    cases b0; cases b1; cases b2
    exact ⟨rfl, rfl⟩

def lane4Zero : Lane4 := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

def lane4Add (a b : Lane4) : Lane4 :=
  ⟨Goldilocks.add a.x0 b.x0, Goldilocks.add a.x1 b.x1,
   Goldilocks.add a.x2 b.x2, Goldilocks.add a.x3 b.x3⟩

def lane4Sub (a b : Lane4) : Lane4 :=
  ⟨Goldilocks.sub a.x0 b.x0, Goldilocks.sub a.x1 b.x1,
   Goldilocks.sub a.x2 b.x2, Goldilocks.sub a.x3 b.x3⟩

def lane4Scale (c : Goldilocks) (a : Lane4) : Lane4 :=
  ⟨Goldilocks.mul c a.x0, Goldilocks.mul c a.x1,
   Goldilocks.mul c a.x2, Goldilocks.mul c a.x3⟩

def lane4Sum (a : Lane4) : Goldilocks :=
  Goldilocks.add (Goldilocks.add a.x0 a.x1) (Goldilocks.add a.x2 a.x3)

private def inv4G : Goldilocks := ⟨13835058052060938241, by decide⟩
private def inv7G : Goldilocks := ⟨2635249152773512046, by decide⟩
private def inv15G : Goldilocks := ⟨17216961131453612033, by decide⟩
private def inv1024G : Goldilocks := ⟨18428729670909296641, by decide⟩
private def inv2559G : Goldilocks := ⟨16817606062502628066, by decide⟩

private theorem ofNat_eq_goldOfInt (k : Nat) : Goldilocks.ofNat k = goldOfInt (k : Int) := by
  apply Goldilocks.ext
  apply Int.ofNat_inj.mp
  rw [goldOfInt_val]
  simp [Goldilocks.ofNat, goldP, Int.natCast_emod]

private theorem mul_cancel_of_prod_one {u k : Goldilocks} (h : Goldilocks.mul u k = Goldilocks.one)
    (x : Goldilocks) :
    Goldilocks.mul u (Goldilocks.mul k x) = x := by
  change CommRingOps.mul u (CommRingOps.mul k x) = x
  rw [← LawfulCommRing.mul_assoc]
  change CommRingOps.mul (Goldilocks.mul u k) x = x
  rw [h]
  exact LawfulCommRing.one_mul x

private theorem inv4G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv4G (Goldilocks.mul (Goldilocks.ofNat 4) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem mul_inv4G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 4) (Goldilocks.mul inv4G x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv7G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv7G (Goldilocks.mul (Goldilocks.ofNat 7) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem mul_inv7G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv15G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv15G (Goldilocks.mul (Goldilocks.ofNat 15) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv1024G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv1024G (Goldilocks.mul (Goldilocks.ofNat 1024) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv2559G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv2559G (Goldilocks.mul (Goldilocks.ofNat 2559) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem mul_inv2559G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 2559) (Goldilocks.mul inv2559G x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

/-- $4 \times 4$ MDS circulant matrix $M_4 = \text{circ}(2, 3, 1, 1)$ over `Goldilocks`
    ($\det(M_4) = -105 \not\equiv 0 \pmod p$, all $1\times 1, 2\times 2, 3\times 3, 4\times 4$ minors non-zero). -/
def applyM4 (b : Lane4) : Lane4 :=
  let s := lane4Sum b
  let c2 := Goldilocks.ofNat 2
  ⟨Goldilocks.add s (Goldilocks.add b.x0 (Goldilocks.mul c2 b.x1)),
   Goldilocks.add s (Goldilocks.add b.x1 (Goldilocks.mul c2 b.x2)),
   Goldilocks.add s (Goldilocks.add b.x2 (Goldilocks.mul c2 b.x3)),
   Goldilocks.add s (Goldilocks.add b.x3 (Goldilocks.mul c2 b.x0))⟩

private def makeM4InvRaw (y : Lane4) (s : Goldilocks) : Lane4 :=
  let u0 := Goldilocks.sub y.x0 s
  let u1 := Goldilocks.sub y.x1 s
  let u2 := Goldilocks.sub y.x2 s
  let u3 := Goldilocks.sub y.x3 s
  let c2 := Goldilocks.ofNat 2
  let c4 := Goldilocks.ofNat 4
  let c8 := Goldilocks.ofNat 8
  ⟨Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u3) (Goldilocks.mul c4 u2)) (Goldilocks.mul c2 u1)) u0,
   Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u0) (Goldilocks.mul c4 u3)) (Goldilocks.mul c2 u2)) u1,
   Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u1) (Goldilocks.mul c4 u0)) (Goldilocks.mul c2 u3)) u2,
   Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u2) (Goldilocks.mul c4 u1)) (Goldilocks.mul c2 u0)) u3⟩

/-- Explicit algebraic inverse $M_4^{-1}$ over `Goldilocks` via cyclic telescoping ($15 x_i = 8 u_{i-1} - 4 u_{i-2} + 2 u_{i+1} - u_i$). -/
def applyM4Inv (y : Lane4) : Lane4 :=
  lane4Scale inv15G (makeM4InvRaw y (Goldilocks.mul inv7G (lane4Sum y)))

private theorem lane4Sum_applyM4 (b : Lane4) :
    lane4Sum (applyM4 b) = Goldilocks.mul (Goldilocks.ofNat 7) (lane4Sum b) := by
  unfold applyM4 lane4Sum
  dsimp only
  rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3,
      ofNat_eq_goldOfInt, ofNat_eq_goldOfInt]
  simp only [goldOfInt_add, goldOfInt_mul]
  congr 1
  omega

private theorem makeM4InvRaw_applyM4 (b : Lane4) :
    makeM4InvRaw (applyM4 b) (lane4Sum b) = lane4Scale (Goldilocks.ofNat 15) b := by
  unfold makeM4InvRaw applyM4 lane4Sum lane4Scale
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyM4Inv_applyM4 (b : Lane4) : applyM4Inv (applyM4 b) = b := by
  unfold applyM4Inv
  rw [lane4Sum_applyM4, inv7G_mul_cancel, makeM4InvRaw_applyM4]
  unfold lane4Scale
  exact Lane4.ext
    (inv15G_mul_cancel b.x0)
    (inv15G_mul_cancel b.x1)
    (inv15G_mul_cancel b.x2)
    (inv15G_mul_cancel b.x3)

private theorem applyM4_scale (c : Goldilocks) (b : Lane4) :
    applyM4 (lane4Scale c b) = lane4Scale c (applyM4 b) := by
  have h2 : ∀ x : Int, (c.val : Int) * (((2 : Nat) : Int) * x) =
      ((2 : Nat) : Int) * ((c.val : Int) * x) := fun x => by
    rw [← Int.mul_assoc, Int.mul_comm (c.val : Int) ((2 : Nat) : Int), Int.mul_assoc]
  unfold applyM4 lane4Scale lane4Sum
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat c, ← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1,
         ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul, Int.mul_add, h2])

private theorem applyM4_makeM4InvRaw (y : Lane4) (s : Goldilocks) :
    applyM4 (makeM4InvRaw y s) =
      let rem := Goldilocks.mul (Goldilocks.ofNat 5)
        (Goldilocks.sub (lane4Sum y) (Goldilocks.mul (Goldilocks.ofNat 7) s))
      ⟨Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x0) rem,
       Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x1) rem,
       Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x2) rem,
       Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x3) rem⟩ := by
  unfold applyM4 makeM4InvRaw lane4Sum
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat y.x0, ← goldOfInt_nat y.x1, ← goldOfInt_nat y.x2,
         ← goldOfInt_nat y.x3, ← goldOfInt_nat s];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyM4_applyM4Inv (y : Lane4) : applyM4 (applyM4Inv y) = y := by
  unfold applyM4Inv
  rw [applyM4_scale, applyM4_makeM4InvRaw]
  have hs7 : Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G (lane4Sum y)) = lane4Sum y :=
    mul_inv7G_cancel (lane4Sum y)
  have hRemZero : Goldilocks.mul (Goldilocks.ofNat 5)
      (Goldilocks.sub (lane4Sum y) (Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G (lane4Sum y)))) =
      Goldilocks.zero := by
    rw [hs7]
    have hz : Goldilocks.sub (lane4Sum y) (lane4Sum y) = Goldilocks.zero := by
      change CommRingOps.sub (lane4Sum y) (lane4Sum y) = CommRingOps.zero
      exact LawfulCommRing.sub_self _
    rw [hz]
    decide
  unfold lane4Scale
  dsimp only at *
  rw [hRemZero]
  have hAddZero : ∀ a : Goldilocks, Goldilocks.add a Goldilocks.zero = a := fun a => by
    change CommRingOps.add a CommRingOps.zero = a
    exact LawfulCommRing.add_zero a
  rw [hAddZero, hAddZero, hAddZero, hAddZero]
  exact Lane4.ext
    (inv15G_mul_cancel y.x0)
    (inv15G_mul_cancel y.x1)
    (inv15G_mul_cancel y.x2)
    (inv15G_mul_cancel y.x3)

/-- Width-12 external $3 \times 4 \times 4$ block-circulant linear layer $M_E = \text{circ}(2 M_4, M_4, M_4)$. -/
@[expose] def applyME (st : Poseidon2State12) : Poseidon2State12 :=
  let y0 := applyM4 st.b0
  let y1 := applyM4 st.b1
  let y2 := applyM4 st.b2
  let s := lane4Add (lane4Add y0 y1) y2
  ⟨lane4Add y0 s, lane4Add y1 s, lane4Add y2 s⟩

/-- Exact inverse $M_E^{-1}$ of the Width-12 external linear layer. -/
def applyMEInv (st : Poseidon2State12) : Poseidon2State12 :=
  let sumAll := lane4Add (lane4Add st.b0 st.b1) st.b2
  let s := lane4Scale inv4G sumAll
  ⟨applyM4Inv (lane4Sub st.b0 s),
   applyM4Inv (lane4Sub st.b1 s),
   applyM4Inv (lane4Sub st.b2 s)⟩

private theorem scalar_sum_four_cancel (a b c : Goldilocks) :
    Goldilocks.mul inv4G (Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add a b) c))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add a b) c)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add a b) c))) =
      Goldilocks.add (Goldilocks.add a b) c := by
  have h : Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add a b) c))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add a b) c)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add a b) c)) =
      Goldilocks.mul (Goldilocks.ofNat 4) (Goldilocks.add (Goldilocks.add a b) c) := by
    rw [← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1; omega
  rw [h, inv4G_mul_cancel]

private theorem lane4_sum_four_cancel (y0 y1 y2 : Lane4) :
    lane4Scale inv4G (lane4Add (lane4Add (lane4Add y0 (lane4Add (lane4Add y0 y1) y2))
      (lane4Add y1 (lane4Add (lane4Add y0 y1) y2)))
      (lane4Add y2 (lane4Add (lane4Add y0 y1) y2))) =
    lane4Add (lane4Add y0 y1) y2 := by
  unfold lane4Scale lane4Add
  exact Lane4.ext
    (scalar_sum_four_cancel y0.x0 y1.x0 y2.x0)
    (scalar_sum_four_cancel y0.x1 y1.x1 y2.x1)
    (scalar_sum_four_cancel y0.x2 y1.x2 y2.x2)
    (scalar_sum_four_cancel y0.x3 y1.x3 y2.x3)

private theorem lane4Sub_add_right (a s : Lane4) : lane4Sub (lane4Add a s) s = a := by
  unfold lane4Sub lane4Add
  apply Lane4.ext <;>
    (change CommRingOps.sub (CommRingOps.add _ _) _ = _;
     rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
         LawfulCommRing.add_right_neg, LawfulCommRing.add_zero])

theorem applyMEInv_applyME (st : Poseidon2State12) : applyMEInv (applyME st) = st := by
  unfold applyMEInv applyME
  dsimp only
  rw [lane4_sum_four_cancel]
  rw [lane4Sub_add_right, lane4Sub_add_right, lane4Sub_add_right]
  rw [applyM4Inv_applyM4, applyM4Inv_applyM4, applyM4Inv_applyM4]

private theorem lane4SubSumId (b0 b1 b2 s : Lane4) :
    lane4Add (lane4Add (lane4Sub b0 s) (lane4Sub b1 s)) (lane4Sub b2 s) =
      lane4Add s (lane4Sub (lane4Add (lane4Add b0 b1) b2) (lane4Scale (Goldilocks.ofNat 4) s)) := by
  unfold lane4Add lane4Sub lane4Scale
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat b0.x0, ← goldOfInt_nat b0.x1, ← goldOfInt_nat b0.x2, ← goldOfInt_nat b0.x3,
         ← goldOfInt_nat b1.x0, ← goldOfInt_nat b1.x1, ← goldOfInt_nat b1.x2, ← goldOfInt_nat b1.x3,
         ← goldOfInt_nat b2.x0, ← goldOfInt_nat b2.x1, ← goldOfInt_nat b2.x2, ← goldOfInt_nat b2.x3,
         ← goldOfInt_nat s.x0, ← goldOfInt_nat s.x1, ← goldOfInt_nat s.x2, ← goldOfInt_nat s.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyME_applyMEInv (st : Poseidon2State12) : applyME (applyMEInv st) = st := by
  unfold applyME applyMEInv
  dsimp only
  rw [applyM4_applyM4Inv, applyM4_applyM4Inv, applyM4_applyM4Inv]
  let sumAll := lane4Add (lane4Add st.b0 st.b1) st.b2
  have h4 : lane4Scale (Goldilocks.ofNat 4) (lane4Scale inv4G sumAll) = sumAll := by
    unfold lane4Scale
    exact Lane4.ext
      (mul_inv4G_cancel sumAll.x0)
      (mul_inv4G_cancel sumAll.x1)
      (mul_inv4G_cancel sumAll.x2)
      (mul_inv4G_cancel sumAll.x3)
  have hSumSub : lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
      (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll)) =
      lane4Scale inv4G sumAll := by
    rw [lane4SubSumId st.b0 st.b1 st.b2 (lane4Scale inv4G sumAll), h4]
    have hZero : lane4Sub sumAll sumAll = lane4Zero := by
      unfold lane4Sub lane4Zero
      apply Lane4.ext <;> exact LawfulCommRing.sub_self _
    rw [hZero]
    unfold lane4Add lane4Zero
    apply Lane4.ext <;> exact LawfulCommRing.add_zero _
  change Poseidon2State12.mk
    (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
      (lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
        (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll))))
    (lane4Add (lane4Sub st.b1 (lane4Scale inv4G sumAll))
      (lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
        (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll))))
    (lane4Add (lane4Sub st.b2 (lane4Scale inv4G sumAll))
      (lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
        (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll)))) = st
  rw [hSumSub]
  have hAddSub : ∀ a b : Lane4, lane4Add (lane4Sub a b) b = a := fun a b => by
    unfold lane4Add lane4Sub
    apply Lane4.ext <;>
      (change CommRingOps.add (CommRingOps.sub _ _) _ = _;
       rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left])
  rw [hAddSub, hAddSub, hAddSub]

def state12Sum (st : Poseidon2State12) : Goldilocks :=
  Goldilocks.add (Goldilocks.add (lane4Sum st.b0) (lane4Sum st.b1)) (lane4Sum st.b2)

/-- Width-12 internal diagonal-plus-ones linear layer $M_I = \mathbf{1}\mathbf{1}^T + \text{diag}(v)$
    with shift-friendly non-zero diagonal $v = (-2, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024)$. -/
@[expose] def applyMI (st : Poseidon2State12) : Poseidon2State12 :=
  let s := state12Sum st
  let b0 := st.b0
  let b1 := st.b1
  let b2 := st.b2
  ⟨⟨Goldilocks.add (Goldilocks.mul (goldOfInt (-2)) b0.x0) s,
    Goldilocks.add b0.x1 s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 2) b0.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 4) b0.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 8) b1.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 16) b1.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 32) b1.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 64) b1.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 128) b2.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 256) b2.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 512) b2.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 1024) b2.x3) s⟩⟩

private def weightedSumMI (y : Poseidon2State12) : Goldilocks :=
  let t0 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt (-512)) y.b0.x0) (Goldilocks.mul (goldOfInt 1024) y.b0.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 512) y.b0.x2) (Goldilocks.mul (goldOfInt 256) y.b0.x3))
  let t1 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 128) y.b1.x0) (Goldilocks.mul (goldOfInt 64) y.b1.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 32) y.b1.x2) (Goldilocks.mul (goldOfInt 16) y.b1.x3))
  let t2 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 8) y.b2.x0) (Goldilocks.mul (goldOfInt 4) y.b2.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 2) y.b2.x2) y.b2.x3)
  Goldilocks.add (Goldilocks.add t0 t1) t2

private def makeMIInvRaw (y : Poseidon2State12) (inv1024 s : Goldilocks) : Poseidon2State12 :=
  let scale (w : Int) (yi : Goldilocks) : Goldilocks :=
    Goldilocks.mul inv1024 (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))
  ⟨⟨scale (-512) y.b0.x0, scale 1024 y.b0.x1, scale 512 y.b0.x2, scale 256 y.b0.x3⟩,
   ⟨scale 128 y.b1.x0, scale 64 y.b1.x1, scale 32 y.b1.x2, scale 16 y.b1.x3⟩,
   ⟨scale 8 y.b2.x0, scale 4 y.b2.x1, scale 2 y.b2.x2, scale 1 y.b2.x3⟩⟩

/-- Exact Sherman–Morrison inverse $M_I^{-1}$ over `Goldilocks` ($\sigma = 1024 + \sum \tilde{w}_i = 2559 \neq 0$). -/
def applyMIInv (y : Poseidon2State12) : Poseidon2State12 :=
  makeMIInvRaw y inv1024G (Goldilocks.mul inv2559G (weightedSumMI y))

private theorem weightedSumMI_applyMI (st : Poseidon2State12) :
    weightedSumMI (applyMI st) = Goldilocks.mul (Goldilocks.ofNat 2559) (state12Sum st) := by
  unfold weightedSumMI applyMI state12Sum lane4Sum
  dsimp only
  rw [← goldOfInt_nat st.b0.x0, ← goldOfInt_nat st.b0.x1, ← goldOfInt_nat st.b0.x2, ← goldOfInt_nat st.b0.x3,
      ← goldOfInt_nat st.b1.x0, ← goldOfInt_nat st.b1.x1, ← goldOfInt_nat st.b1.x2, ← goldOfInt_nat st.b1.x3,
      ← goldOfInt_nat st.b2.x0, ← goldOfInt_nat st.b2.x1, ← goldOfInt_nat st.b2.x2, ← goldOfInt_nat st.b2.x3]
  simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
  congr 1; omega

private theorem mi_lane_recover (v w : Int) (hv : v * w = 1024) (x s : Goldilocks) :
    Goldilocks.mul inv1024G (Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s)) = x := by
  have hProd : Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s) =
      Goldilocks.mul (Goldilocks.ofNat 1024) x := by
    rw [← goldOfInt_nat x, ← goldOfInt_nat s, ofNat_eq_goldOfInt]
    simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
    congr 1
    have hEq : w * (v * (x.val : Int) + (s.val : Int) - (s.val : Int)) = (v * w) * (x.val : Int) := by
      rw [Int.add_sub_cancel, ← Int.mul_assoc, Int.mul_comm w v]
    rw [hEq, hv]
    omega
  rw [hProd, inv1024G_mul_cancel x]

theorem applyMIInv_applyMI (st : Poseidon2State12) : applyMIInv (applyMI st) = st := by
  unfold applyMIInv
  rw [weightedSumMI_applyMI, inv2559G_mul_cancel (state12Sum st)]
  unfold makeMIInvRaw applyMI
  dsimp only
  have h1 : Goldilocks.add st.b0.x1 (state12Sum st) =
      Goldilocks.add (Goldilocks.mul (goldOfInt 1) st.b0.x1) (state12Sum st) := by
    have hone : goldOfInt 1 = CommRingOps.one := rfl
    change _ = Goldilocks.add (CommRingOps.mul (goldOfInt 1) st.b0.x1) _
    rw [hone, LawfulCommRing.one_mul]
  apply Poseidon2State12.ext
  · apply Lane4.ext
    · exact mi_lane_recover (-2) (-512) rfl st.b0.x0 (state12Sum st)
    · rw [h1]; exact mi_lane_recover 1 1024 rfl st.b0.x1 (state12Sum st)
    · exact mi_lane_recover 2 512 rfl st.b0.x2 (state12Sum st)
    · exact mi_lane_recover 4 256 rfl st.b0.x3 (state12Sum st)
  · apply Lane4.ext
    · exact mi_lane_recover 8 128 rfl st.b1.x0 (state12Sum st)
    · exact mi_lane_recover 16 64 rfl st.b1.x1 (state12Sum st)
    · exact mi_lane_recover 32 32 rfl st.b1.x2 (state12Sum st)
    · exact mi_lane_recover 64 16 rfl st.b1.x3 (state12Sum st)
  · apply Lane4.ext
    · exact mi_lane_recover 128 8 rfl st.b2.x0 (state12Sum st)
    · exact mi_lane_recover 256 4 rfl st.b2.x1 (state12Sum st)
    · exact mi_lane_recover 512 2 rfl st.b2.x2 (state12Sum st)
    · exact mi_lane_recover 1024 1 rfl st.b2.x3 (state12Sum st)

private theorem mi_lane_assoc_aux (v w : Int) (hv : v * w = 1024) (inv1024 yi s : Goldilocks) :
    Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv1024 (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))) =
      Goldilocks.mul inv1024 (Goldilocks.mul (Goldilocks.ofNat 1024) (Goldilocks.sub yi s)) := by
  rw [← goldOfInt_nat inv1024, ← goldOfInt_nat yi, ← goldOfInt_nat s, ofNat_eq_goldOfInt]
  simp only [goldOfInt_sub, goldOfInt_mul]
  congr 1
  have hEq : v * ((inv1024.val : Int) * (w * ((yi.val : Int) - (s.val : Int)))) =
      (inv1024.val : Int) * ((v * w) * ((yi.val : Int) - (s.val : Int))) := by
    rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm v (inv1024.val : Int),
        Int.mul_assoc (inv1024.val : Int) v w, Int.mul_assoc]
  rw [hEq, hv]
  rfl

private theorem mi_lane_forward (v w : Int) (hv : v * w = 1024) (yi s : Goldilocks) :
    Goldilocks.add (Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv1024G (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s)))) s = yi := by
  rw [mi_lane_assoc_aux v w hv inv1024G yi s, inv1024G_mul_cancel (Goldilocks.sub yi s)]
  change CommRingOps.add (CommRingOps.sub yi s) s = yi
  rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

private theorem state12Sum_makeMIInvRaw (y : Poseidon2State12) (inv1024 s : Goldilocks) :
    state12Sum (makeMIInvRaw y inv1024 s) =
      Goldilocks.mul inv1024 (Goldilocks.sub (weightedSumMI y) (Goldilocks.mul (goldOfInt 1535) s)) := by
  unfold state12Sum makeMIInvRaw lane4Sum weightedSumMI
  dsimp only
  rw [← goldOfInt_nat inv1024, ← goldOfInt_nat s,
      ← goldOfInt_nat y.b0.x0, ← goldOfInt_nat y.b0.x1, ← goldOfInt_nat y.b0.x2, ← goldOfInt_nat y.b0.x3,
      ← goldOfInt_nat y.b1.x0, ← goldOfInt_nat y.b1.x1, ← goldOfInt_nat y.b1.x2, ← goldOfInt_nat y.b1.x3,
      ← goldOfInt_nat y.b2.x0, ← goldOfInt_nat y.b2.x1, ← goldOfInt_nat y.b2.x2, ← goldOfInt_nat y.b2.x3]
  simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul, ← Int.mul_add]
  congr 1
  congr 1
  omega

private theorem mi_2559_sub_1535 (s : Goldilocks) :
    Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 2559) s) (Goldilocks.mul (goldOfInt 1535) s) =
      Goldilocks.mul (Goldilocks.ofNat 1024) s := by
  rw [← goldOfInt_nat s, ofNat_eq_goldOfInt, ofNat_eq_goldOfInt]
  simp only [goldOfInt_sub, goldOfInt_mul]
  congr 1; omega

private theorem applyMI_makeMIInvRaw_helper (y : Poseidon2State12) (s : Goldilocks)
    (hSum : state12Sum (makeMIInvRaw y inv1024G s) = s) :
    applyMI (makeMIInvRaw y inv1024G s) = y := by
  unfold applyMI
  rw [hSum]
  unfold makeMIInvRaw
  dsimp only
  have h1 : ∀ a : Goldilocks, a = Goldilocks.mul (goldOfInt 1) a := fun a => by
    rw [← goldOfInt_nat a, goldOfInt_mul, Int.one_mul]
  apply Poseidon2State12.ext
  · apply Lane4.ext
    · exact mi_lane_forward (-2) (-512) rfl y.b0.x0 s
    · rw [h1 (Goldilocks.mul inv1024G (Goldilocks.mul (goldOfInt 1024) (Goldilocks.sub y.b0.x1 s)))]
      exact mi_lane_forward 1 1024 rfl y.b0.x1 s
    · exact mi_lane_forward 2 512 rfl y.b0.x2 s
    · exact mi_lane_forward 4 256 rfl y.b0.x3 s
  · apply Lane4.ext
    · exact mi_lane_forward 8 128 rfl y.b1.x0 s
    · exact mi_lane_forward 16 64 rfl y.b1.x1 s
    · exact mi_lane_forward 32 32 rfl y.b1.x2 s
    · exact mi_lane_forward 64 16 rfl y.b1.x3 s
  · apply Lane4.ext
    · exact mi_lane_forward 128 8 rfl y.b2.x0 s
    · exact mi_lane_forward 256 4 rfl y.b2.x1 s
    · exact mi_lane_forward 512 2 rfl y.b2.x2 s
    · exact mi_lane_forward 1024 1 rfl y.b2.x3 s

theorem applyMI_applyMIInv (y : Poseidon2State12) : applyMI (applyMIInv y) = y := by
  have hs2559 : Goldilocks.mul (Goldilocks.ofNat 2559) (Goldilocks.mul inv2559G (weightedSumMI y)) =
      weightedSumMI y :=
    mul_inv2559G_cancel (weightedSumMI y)
  have hSumEq : state12Sum (makeMIInvRaw y inv1024G (Goldilocks.mul inv2559G (weightedSumMI y))) =
      Goldilocks.mul inv2559G (weightedSumMI y) := by
    rw [state12Sum_makeMIInvRaw]
    conv => lhs; arg 2; arg 1; rw [← hs2559]
    rw [mi_2559_sub_1535, inv1024G_mul_cancel]
  exact applyMI_makeMIInvRaw_helper y (Goldilocks.mul inv2559G (weightedSumMI y)) hSumEq

/-! ## 3. Full Width-12 `Poseidon2` Permutation ($R_F = 8, R_P = 22$) & `poseidon2Perm12_bijective` -/

def state12Add (a b : Poseidon2State12) : Poseidon2State12 :=
  ⟨lane4Add a.b0 b.b0, lane4Add a.b1 b.b1, lane4Add a.b2 b.b2⟩

def state12Sub (a b : Poseidon2State12) : Poseidon2State12 :=
  ⟨lane4Sub a.b0 b.b0, lane4Sub a.b1 b.b1, lane4Sub a.b2 b.b2⟩

private theorem state12Sub_add_right (a c : Poseidon2State12) : state12Sub (state12Add a c) c = a := by
  unfold state12Sub state12Add
  exact Poseidon2State12.ext (lane4Sub_add_right _ _) (lane4Sub_add_right _ _) (lane4Sub_add_right _ _)

private theorem state12Add_sub_right (a c : Poseidon2State12) : state12Add (state12Sub a c) c = a := by
  have h4 : ∀ x y : Lane4, lane4Add (lane4Sub x y) y = x := fun x y => by
    unfold lane4Add lane4Sub
    apply Lane4.ext <;>
      (change CommRingOps.add (CommRingOps.sub _ _) _ = _;
       rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left])
  unfold state12Add state12Sub
  exact Poseidon2State12.ext (h4 _ _) (h4 _ _) (h4 _ _)

def sboxLane4 (b : Lane4) : Lane4 :=
  ⟨sbox7 b.x0, sbox7 b.x1, sbox7 b.x2, sbox7 b.x3⟩

def sboxLane4Inv (b : Lane4) : Lane4 :=
  ⟨sbox7Inv b.x0, sbox7Inv b.x1, sbox7Inv b.x2, sbox7Inv b.x3⟩

def sboxState12 (st : Poseidon2State12) : Poseidon2State12 :=
  ⟨sboxLane4 st.b0, sboxLane4 st.b1, sboxLane4 st.b2⟩

def sboxState12Inv (st : Poseidon2State12) : Poseidon2State12 :=
  ⟨sboxLane4Inv st.b0, sboxLane4Inv st.b1, sboxLane4Inv st.b2⟩

private theorem sboxState12Inv_sboxState12 (st : Poseidon2State12) :
    sboxState12Inv (sboxState12 st) = st := by
  unfold sboxState12Inv sboxState12 sboxLane4Inv sboxLane4
  apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact sbox7Inv_sbox7 _

private theorem sboxState12_sboxState12Inv (st : Poseidon2State12) :
    sboxState12 (sboxState12Inv st) = st := by
  unfold sboxState12 sboxState12Inv sboxLane4 sboxLane4Inv
  apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact sbox7_sbox7Inv _

/-- One external Poseidon2 round: add 12 round constants, apply $x^7$ to all 12 lanes, apply $M_E$. -/
def externalRound (rc : Poseidon2State12) (st : Poseidon2State12) : Poseidon2State12 :=
  applyME (sboxState12 (state12Add st rc))

/-- Exact inverse of one external Poseidon2 round. -/
def externalRoundInv (rc : Poseidon2State12) (st : Poseidon2State12) : Poseidon2State12 :=
  state12Sub (sboxState12Inv (applyMEInv st)) rc

private theorem externalRoundInv_externalRound (rc st : Poseidon2State12) :
    externalRoundInv rc (externalRound rc st) = st := by
  unfold externalRoundInv externalRound
  rw [applyMEInv_applyME, sboxState12Inv_sboxState12, state12Sub_add_right]

private theorem externalRound_externalRoundInv (rc st : Poseidon2State12) :
    externalRound rc (externalRoundInv rc st) = st := by
  unfold externalRound externalRoundInv
  rw [state12Add_sub_right, sboxState12_sboxState12Inv, applyME_applyMEInv]

/-- One internal Poseidon2 round: add round constant to lane 0, apply $x^7$ only to lane 0, apply $M_I$. -/
def internalRound (rc : Goldilocks) (st : Poseidon2State12) : Poseidon2State12 :=
  let x0' := sbox7 (Goldilocks.add st.b0.x0 rc)
  applyMI ⟨⟨x0', st.b0.x1, st.b0.x2, st.b0.x3⟩, st.b1, st.b2⟩

/-- Exact inverse of one internal Poseidon2 round. -/
def internalRoundInv (rc : Goldilocks) (st : Poseidon2State12) : Poseidon2State12 :=
  let u := applyMIInv st
  let x0 := Goldilocks.sub (sbox7Inv u.b0.x0) rc
  ⟨⟨x0, u.b0.x1, u.b0.x2, u.b0.x3⟩, u.b1, u.b2⟩

private theorem internalRoundInv_internalRound (rc : Goldilocks) (st : Poseidon2State12) :
    internalRoundInv rc (internalRound rc st) = st := by
  unfold internalRoundInv internalRound
  rw [applyMIInv_applyMI]
  dsimp only
  rw [sbox7Inv_sbox7]
  have hSub : Goldilocks.sub (Goldilocks.add st.b0.x0 rc) rc = st.b0.x0 := by
    change CommRingOps.sub (CommRingOps.add st.b0.x0 rc) rc = st.b0.x0
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  rw [hSub]

private theorem internalRound_step_cancel (rc : Goldilocks) (u : Poseidon2State12) :
    internalRound rc ⟨⟨Goldilocks.sub (sbox7Inv u.b0.x0) rc, u.b0.x1, u.b0.x2, u.b0.x3⟩, u.b1, u.b2⟩ =
      applyMI u := by
  cases u with | mk b0 b1 b2 =>
    cases b0 with | mk x0 x1 x2 x3 =>
      unfold internalRound
      dsimp only
      have hAdd : Goldilocks.add (Goldilocks.sub (sbox7Inv x0) rc) rc = sbox7Inv x0 := by
        change CommRingOps.add (CommRingOps.sub (sbox7Inv x0) rc) rc = sbox7Inv x0
        rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]
      rw [hAdd, sbox7_sbox7Inv]

private theorem internalRound_internalRoundInv (rc : Goldilocks) (st : Poseidon2State12) :
    internalRound rc (internalRoundInv rc st) = st := by
  change internalRound rc
    ⟨⟨Goldilocks.sub (sbox7Inv (applyMIInv st).b0.x0) rc,
      (applyMIInv st).b0.x1, (applyMIInv st).b0.x2, (applyMIInv st).b0.x3⟩,
     (applyMIInv st).b1, (applyMIInv st).b2⟩ = st
  rw [internalRound_step_cancel rc (applyMIInv st), applyMI_applyMIInv]

/-- One SplitMix64 output step (Steele, Lea & Flood, "Fast Splittable Pseudorandom Number Generators",
    OOPSLA 2014; Vigna's reference `splitmix64.c`): add the golden gamma, then the xor-shift-multiply finalizer.
    From state `0` the reference stream is `0xE220A8397B1DCDAF, 0x6E789E6AA1B965F4, 0x06C45D188009454F`. -/
def splitMix64Mix (x : UInt64) : UInt64 :=
  let z0 := x + 0x9E3779B97F4A7C15
  let z1 := (z0 ^^^ (z0 >>> 30)) * 0xBF58476D1CE4E5B9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB
  z2 ^^^ (z2 >>> 31)

example : splitMix64Mix 0 = 0xE220A8397B1DCDAF ∧ splitMix64Mix 0x9E3779B97F4A7C15 = 0x6E789E6AA1B965F4 ∧
    splitMix64Mix 0x3C6EF372FE94F82A = 0x06C45D188009454F := by decide

/-- Domain IV of the round-constant generator: ASCII `POS2_GL1`. -/
def poseidon2ConstIV : UInt64 := 0x504F53325F474C31

/-- The 64-bit round-constant word: `(tag, round, lane)` absorbed one at a time into the IV, a SplitMix64 step
    after each. `tag` is `0` for the initial external rounds, `1` for the internal rounds, `2` for the terminal. -/
def poseidon2ConstWord (tag round lane : Nat) : UInt64 :=
  splitMix64Mix (splitMix64Mix (splitMix64Mix (poseidon2ConstIV ^^^ UInt64.ofNat tag) ^^^ UInt64.ofNat round) ^^^
    UInt64.ofNat lane)

/-- Round constant: the SplitMix64 word reduced modulo `p` (a word in `[p, 2^64)` has probability `2^-32`). -/
def poseidon2ConstAt (tag round lane : Nat) : Goldilocks :=
  Goldilocks.ofNat (poseidon2ConstWord tag round lane).toNat

/-- **The round-constant generator is not affine in the round index.** No field elements `a`, `b` make
    `a + b·r` reproduce the internal round constants: the first three are not in arithmetic progression. (The
    generator this replaces was `a + b·r` modulo `2^64`.) -/
theorem poseidon2ConstAt_not_affine (a b : Goldilocks) :
    ¬ ∀ r : Nat, poseidon2ConstAt 1 r 0 = Goldilocks.add a (Goldilocks.mul b (Goldilocks.ofNat r)) := by
  intro h
  have key : ((poseidon2ConstAt 1 0 0).val + (poseidon2ConstAt 1 2 0).val) % goldilocksPrime ≠
      (2 * (poseidon2ConstAt 1 1 0).val) % goldilocksPrime := by decide +kernel
  have h0 := congrArg Goldilocks.val (h 0)
  have h1 := congrArg Goldilocks.val (h 1)
  have h2 := congrArg Goldilocks.val (h 2)
  rw [Goldilocks.add_val, Goldilocks.mul_val] at h0 h1 h2
  have o0 : (Goldilocks.ofNat 0).val = 0 := by decide
  have o1 : (Goldilocks.ofNat 1).val = 1 := by decide
  have o2 : (Goldilocks.ofNat 2).val = 2 := by decide
  rw [o0] at h0; rw [o1] at h1; rw [o2] at h2
  apply key; rw [h0, h1, h2]
  have ha := a.isLt
  have hb := b.isLt
  simp only [goldilocksPrime] at *
  omega

def poseidon2ExtRoundConst (tag round : Nat) : Poseidon2State12 :=
  ⟨⟨poseidon2ConstAt tag round 0, poseidon2ConstAt tag round 1,
    poseidon2ConstAt tag round 2, poseidon2ConstAt tag round 3⟩,
   ⟨poseidon2ConstAt tag round 4, poseidon2ConstAt tag round 5,
    poseidon2ConstAt tag round 6, poseidon2ConstAt tag round 7⟩,
   ⟨poseidon2ConstAt tag round 8, poseidon2ConstAt tag round 9,
    poseidon2ConstAt tag round 10, poseidon2ConstAt tag round 11⟩⟩

/-- $R_F / 2 = 4$ initial external round constant vectors (`R_F = 8` total external rounds). -/
def poseidon2InitialExtConsts : List Poseidon2State12 :=
  (List.range 4).map (poseidon2ExtRoundConst 0)

/-- $R_P = 22$ internal round constants on lane 0. -/
def poseidon2InternalConsts : List Goldilocks :=
  (List.range 22).map (fun r => poseidon2ConstAt 1 r 0)

/-- $R_F / 2 = 4$ terminal external round constant vectors. -/
def poseidon2TerminalExtConsts : List Poseidon2State12 :=
  (List.range 4).map (poseidon2ExtRoundConst 2)

def runRounds {α σ : Type} (step : α → σ → σ) : List α → σ → σ
  | [], s => s
  | c :: cs, s => runRounds step cs (step c s)

def runRoundsInv {α σ : Type} (stepInv : α → σ → σ) : List α → σ → σ
  | [], s => s
  | c :: cs, s => stepInv c (runRoundsInv stepInv cs s)

private theorem runRoundsInv_runRounds {α σ : Type} (step stepInv : α → σ → σ)
    (hInv : ∀ c s, stepInv c (step c s) = s) (cs : List α) :
    ∀ (s : σ), runRoundsInv stepInv cs (runRounds step cs s) = s := by
  induction cs with
  | nil => intro s; rfl
  | cons c cs ih =>
    intro s
    simp only [runRounds, runRoundsInv, ih (step c s), hInv]

private theorem runRounds_runRoundsInv {α σ : Type} (step stepInv : α → σ → σ)
    (hInv : ∀ c s, step c (stepInv c s) = s) (cs : List α) :
    ∀ (s : σ), runRounds step cs (runRoundsInv stepInv cs s) = s := by
  induction cs with
  | nil => intro s; rfl
  | cons c cs ih =>
    intro s
    simp only [runRoundsInv, runRounds, hInv, ih s]

/-- **Full Width-12 `Poseidon2` Permutation (`poseidon2Perm12`)**:
    Pre-round $M_E$, $R_F/2 = 4$ initial external rounds, $R_P = 22$ internal rounds,
    and $R_F/2 = 4$ terminal external rounds ($R_F = 8, R_P = 22$). -/
@[expose] def poseidon2Perm12 (st : Poseidon2State12) : Poseidon2State12 :=
  let s0 := applyME st
  let s1 := runRounds externalRound poseidon2InitialExtConsts s0
  let s2 := runRounds internalRound poseidon2InternalConsts s1
  runRounds externalRound poseidon2TerminalExtConsts s2

/-- **Exact Inverse Width-12 `Poseidon2` Permutation (`poseidon2Perm12Inv`)**. -/
@[expose] def poseidon2Perm12Inv (st : Poseidon2State12) : Poseidon2State12 :=
  let s2 := runRoundsInv externalRoundInv poseidon2TerminalExtConsts st
  let s1 := runRoundsInv internalRoundInv poseidon2InternalConsts s2
  let s0 := runRoundsInv externalRoundInv poseidon2InitialExtConsts s1
  applyMEInv s0

theorem poseidon2Perm12Inv_left_inv (st : Poseidon2State12) :
    poseidon2Perm12Inv (poseidon2Perm12 st) = st := by
  unfold poseidon2Perm12Inv poseidon2Perm12
  dsimp only
  rw [runRoundsInv_runRounds externalRound externalRoundInv externalRoundInv_externalRound,
      runRoundsInv_runRounds internalRound internalRoundInv internalRoundInv_internalRound,
      runRoundsInv_runRounds externalRound externalRoundInv externalRoundInv_externalRound,
      applyMEInv_applyME]

theorem poseidon2Perm12Inv_right_inv (st : Poseidon2State12) :
    poseidon2Perm12 (poseidon2Perm12Inv st) = st := by
  unfold poseidon2Perm12 poseidon2Perm12Inv
  dsimp only
  rw [applyME_applyMEInv,
      runRounds_runRoundsInv externalRound externalRoundInv externalRound_externalRoundInv,
      runRounds_runRoundsInv internalRound internalRoundInv internalRound_internalRoundInv,
      runRounds_runRoundsInv externalRound externalRoundInv externalRound_externalRoundInv]

/-- **Width-12 Goldilocks `Poseidon2` Permutation Bijection Theorem (`poseidon2Perm12_bijective`)**:
    `poseidon2Perm12` and `poseidon2Perm12Inv` form an exact bijection on $\mathbb{F}_p^{12}$. -/
theorem poseidon2Perm12_bijective (s t : Poseidon2State12) :
    poseidon2Perm12Inv (poseidon2Perm12 s) = s ∧
    poseidon2Perm12 (poseidon2Perm12Inv t) = t ∧
    (poseidon2Perm12 s = poseidon2Perm12 t ↔ s = t) ∧
    (∃ pre : Poseidon2State12, poseidon2Perm12 pre = t) := by
  refine ⟨poseidon2Perm12Inv_left_inv s, poseidon2Perm12Inv_right_inv t, ?_,
          ⟨poseidon2Perm12Inv t, poseidon2Perm12Inv_right_inv t⟩⟩
  constructor
  · intro h
    have hInv := congrArg poseidon2Perm12Inv h
    rwa [poseidon2Perm12Inv_left_inv, poseidon2Perm12Inv_left_inv] at hInv
  · intro h
    subst h
    rfl

/-! ## 4. Canonical `< 2^56` Limb Framing, Injective `10*1` Sponge Padding & `poseidon2Hash32` -/

private theorem pad7_length (bs : List UInt8) :
    ((bs ++ List.replicate (7 - bs.length) (0 : UInt8)).take 7).length = 7 := by
  rw [List.length_take, List.length_append, List.length_replicate]
  omega

/-- Pack 7 bytes into a canonical `< 2^56` Goldilocks field element (`2^56 < p`). -/
def pack7BytesLimb (bs : List UInt8) : Goldilocks :=
  let chunk : List UInt8 := (bs ++ List.replicate (7 - bs.length) (0 : UInt8)).take 7
  have hLt256 : ofBE chunk < 256 ^ 7 := pad7_length bs ▸ ofBE_lt chunk
  have hLtP : ofBE chunk < goldilocksPrime :=
    Nat.lt_trans hLt256 (by decide)
  ⟨ofBE chunk, hLtP⟩

theorem pack7BytesLimb_lt_two_pow_56 (bs : List UInt8) :
    (pack7BytesLimb bs).val < 2 ^ 56 := by
  unfold pack7BytesLimb
  dsimp only
  let chunk : List UInt8 := (bs ++ List.replicate (7 - bs.length) (0 : UInt8)).take 7
  have hLt : ofBE chunk < 256 ^ 7 := pad7_length bs ▸ ofBE_lt chunk
  have hPow : (256 : Nat) ^ 7 = 2 ^ 56 := rfl
  exact hPow ▸ hLt

private theorem be_foldl_acc :
    ∀ (bs : List UInt8) (w acc : Nat),
      be (w + bs.length) (bs.foldl (fun a b => a * 256 + b.toNat) acc) = be w acc ++ bs
  | [], w, acc => by simp
  | b :: rest, w, acc => by
    have hLen : w + (b :: rest).length = (w + 1) + rest.length := by simp; omega
    rw [List.foldl_cons, hLen, be_foldl_acc rest (w + 1) (acc * 256 + b.toNat)]
    have hb : b.toNat < 256 := b.toNat_lt
    have hDiv : (acc * 256 + b.toNat) / 256 = acc := by omega
    have hMod : UInt8.ofNat ((acc * 256 + b.toNat) % 256) = b := by
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      rw [h8]; omega
    simp only [be, hDiv, hMod, List.append_assoc, List.singleton_append]

theorem be7_pack7BytesLimb_of_length_eq {bs : List UInt8} (hLen : bs.length = 7) :
    be 7 (pack7BytesLimb bs).val = bs := by
  unfold pack7BytesLimb
  dsimp only
  have hChunk : (bs ++ List.replicate (7 - bs.length) (0 : UInt8)).take 7 = bs := by
    rw [hLen]
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
    exact List.take_of_length_le (Nat.le_of_eq hLen)
  rw [hChunk, ← hLen]
  simpa [ofBE, be] using be_foldl_acc bs 0 0

/-- Split a list of bytes whose length is a multiple of 7 into exact 7-byte limbs. -/
def chunk7Exact : List UInt8 → List Goldilocks
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest =>
    pack7BytesLimb [b0, b1, b2, b3, b4, b5, b6] :: chunk7Exact rest
  | _ => []

def unchunk7Exact : List Goldilocks → List UInt8
  | [] => []
  | x :: xs => be 7 x.val ++ unchunk7Exact xs

private theorem unchunk7Exact_chunk7Exact :
    ∀ (bs : List UInt8), bs.length % 7 = 0 → unchunk7Exact (chunk7Exact bs) = bs
  | [], _ => rfl
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest, hMod => by
    have hRest : rest.length % 7 = 0 := by
      simp only [List.length_cons] at hMod
      omega
    simp only [chunk7Exact, unchunk7Exact,
      be7_pack7BytesLimb_of_length_eq (bs := [b0, b1, b2, b3, b4, b5, b6]) rfl,
      unchunk7Exact_chunk7Exact rest hRest]
    rfl
  | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h
  | [_, _, _, _, _], h | [_, _, _, _, _, _], h => by simp at h

private theorem chunk7Exact_lt_two_pow_56 :
    ∀ (bs : List UInt8) (x : Goldilocks), x ∈ chunk7Exact bs → x.val < 2 ^ 56
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest, x, hx => by
    simp only [chunk7Exact, List.mem_cons] at hx
    rcases hx with rfl | hmem
    · exact pack7BytesLimb_lt_two_pow_56 _
    · exact chunk7Exact_lt_two_pow_56 rest x hmem
  | [], _, hx => by cases hx
  | [_], _, hx | [_, _], _, hx | [_, _, _], _, hx | [_, _, _, _], _, hx
  | [_, _, _, _, _], _, hx | [_, _, _, _, _, _], _, hx => by simp [chunk7Exact] at hx

/-- Frame an arbitrary byte string canonically into `< 2^56` Goldilocks limbs by appending a
    `0x01` delimiter byte followed by `0..6` zero pad bytes to a 7-byte boundary. -/
def bytesToLimbs56 (msg : List UInt8) : List Goldilocks :=
  let marked := msg ++ [(0x01 : UInt8)]
  let padLen := (7 - marked.length % 7) % 7
  chunk7Exact (marked ++ List.replicate padLen (0x00 : UInt8))

theorem bytesToLimbs56_lt_two_pow_56 (msg : List UInt8) (x : Goldilocks)
    (hx : x ∈ bytesToLimbs56 msg) : x.val < 2 ^ 56 :=
  chunk7Exact_lt_two_pow_56 _ x hx

private def stripLeadingZeroBytes : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if b == (0x00 : UInt8) then stripLeadingZeroBytes bs else b :: bs

private theorem stripLeadingZeroBytes_replicate (k : Nat) (b : UInt8) (rest : List UInt8)
    (hb : b ≠ 0x00) :
    stripLeadingZeroBytes (List.replicate k (0x00 : UInt8) ++ (b :: rest)) = b :: rest := by
  induction k with
  | zero =>
    have hne : (b == (0x00 : UInt8)) = false := beq_false_of_ne hb
    simp [stripLeadingZeroBytes, hne]
  | succ k ih =>
    simp [List.replicate_succ, stripLeadingZeroBytes, ih]

/-- Left inverse of `bytesToLimbs56` recovering the exact input byte string. -/
def limbs56ToBytes (limbs : List Goldilocks) : List UInt8 :=
  match stripLeadingZeroBytes (unchunk7Exact limbs).reverse with
  | _ :: revMsg => revMsg.reverse
  | [] => []

theorem limbs56ToBytes_bytesToLimbs56 (msg : List UInt8) :
    limbs56ToBytes (bytesToLimbs56 msg) = msg := by
  unfold bytesToLimbs56 limbs56ToBytes
  let marked := msg ++ [(0x01 : UInt8)]
  let padLen := (7 - marked.length % 7) % 7
  have hMod : (marked ++ List.replicate padLen (0x00 : UInt8)).length % 7 = 0 := by
    simp only [List.length_append, List.length_replicate, padLen]
    omega
  rw [unchunk7Exact_chunk7Exact _ hMod]
  have hRev : (marked ++ List.replicate padLen (0x00 : UInt8)).reverse =
      List.replicate padLen (0x00 : UInt8) ++ ((0x01 : UInt8) :: msg.reverse) := by
    simp [marked, List.reverse_append, List.reverse_replicate]
  rw [hRev, stripLeadingZeroBytes_replicate padLen 0x01 msg.reverse (by decide)]
  exact List.reverse_reverse msg

theorem bytesToLimbs56_injective {m₁ m₂ : List UInt8}
    (h : bytesToLimbs56 m₁ = bytesToLimbs56 m₂) : m₁ = m₂ := by
  have hInv := congrArg limbs56ToBytes h
  rwa [limbs56ToBytes_bytesToLimbs56, limbs56ToBytes_bytesToLimbs56] at hInv

/-- High-bit sponge domain marker $2^{56}$ (`< p`, disjoint from `< 2^56` message limbs). -/
def padEndMarker : Goldilocks := ⟨2 ^ 56, by decide⟩

/-- Combined single-lane `10*1` marker $2^{56} + 1$ when start `1` and end `2^56` land in one lane. -/
def padBothMarker : Goldilocks := ⟨2 ^ 56 + 1, by decide⟩

/-- Multi-rate `10*1` suffix of `(z + 1)` Goldilocks elements (`0 ≤ z < 8`):
    - `z = 0`: `[2^56 + 1]` (start bit `1` + end bit `2^56` in final lane, analogous to `0x81`),
    - `z = k + 1`: `[1] ++ replicate k 0 ++ [2^56]`. -/
def pad101Suffix : Nat → List Goldilocks
  | 0 => [padBothMarker]
  | k + 1 => [Goldilocks.one] ++ List.replicate k Goldilocks.zero ++ [padEndMarker]

/-- **Multi-Rate `10*1` Sponge Padding (`poseidon2Pad`, `rate = 8`)**:
    Appends `pad101Suffix` so the padded limb sequence has positive length divisible by `8`. -/
@[expose] def poseidon2Pad (xs : List Goldilocks) : List Goldilocks :=
  let z := (8 - (xs.length + 1) % 8) % 8
  xs ++ pad101Suffix z

theorem poseidon2Pad_length_mod (xs : List Goldilocks) :
    0 < (poseidon2Pad xs).length ∧ (poseidon2Pad xs).length % 8 = 0 := by
  unfold poseidon2Pad
  let z := (8 - (xs.length + 1) % 8) % 8
  have hSuffixLen : (pad101Suffix z).length = z + 1 := by
    cases z <;> simp [pad101Suffix]
  rw [List.length_append, hSuffixLen]
  refine ⟨by omega, ?_⟩
  dsimp only [z]
  omega

private def stripLeadingZeroLimbs : List Goldilocks → List Goldilocks
  | [] => []
  | x :: xs => if x == Goldilocks.zero then stripLeadingZeroLimbs xs else x :: xs

private theorem stripLeadingZeroLimbs_replicate (k : Nat) (rest : List Goldilocks) :
    stripLeadingZeroLimbs (List.replicate k Goldilocks.zero ++ (Goldilocks.one :: rest)) =
      Goldilocks.one :: rest := by
  induction k with
  | zero =>
    have hne : (Goldilocks.one == Goldilocks.zero) = false := by decide
    simp [stripLeadingZeroLimbs, hne]
  | succ k ih =>
    simp [List.replicate_succ, stripLeadingZeroLimbs, ih]

/-- Constructive left-inverse unpadder for `poseidon2Pad`. -/
def poseidon2Unpad (ys : List Goldilocks) : List Goldilocks :=
  match ys.reverse with
  | last :: revInit =>
    if last == padBothMarker then
      revInit.reverse
    else
      match stripLeadingZeroLimbs revInit with
      | _ :: revMsg => revMsg.reverse
      | [] => []
  | [] => []

theorem poseidon2Unpad_poseidon2Pad (xs : List Goldilocks) :
    poseidon2Unpad (poseidon2Pad xs) = xs := by
  unfold poseidon2Pad poseidon2Unpad
  let z := (8 - (xs.length + 1) % 8) % 8
  change (match (xs ++ pad101Suffix z).reverse with
    | last :: revInit =>
      if last == padBothMarker then revInit.reverse
      else match stripLeadingZeroLimbs revInit with
      | _ :: revMsg => revMsg.reverse
      | [] => []
    | [] => []) = xs
  cases z with
  | zero =>
    have hRev : (xs ++ pad101Suffix 0).reverse = padBothMarker :: xs.reverse := by
      simp [pad101Suffix]
    rw [hRev]
    simp [List.reverse_reverse]
  | succ k =>
    have hRev : (xs ++ pad101Suffix (k + 1)).reverse =
        padEndMarker :: (List.replicate k Goldilocks.zero ++ (Goldilocks.one :: xs.reverse)) := by
      simp [pad101Suffix, List.reverse_append, List.reverse_replicate, List.append_assoc]
    have hNe : (padEndMarker == padBothMarker) = false :=
      beq_eq_false_iff_ne.2 fun h => by
        have hv := congrArg Goldilocks.val h
        dsimp only [padEndMarker, padBothMarker] at hv
        omega
    rw [hRev]
    simp [hNe, stripLeadingZeroLimbs_replicate, List.reverse_reverse]

/-- **`poseidon2Pad_injective`**:
    Multi-rate `10*1` sponge padding is unconditionally injective on `List Goldilocks`. -/
theorem poseidon2Pad_injective {xs ys : List Goldilocks}
    (h : poseidon2Pad xs = poseidon2Pad ys) : xs = ys := by
  have hInv := congrArg poseidon2Unpad h
  rwa [poseidon2Unpad_poseidon2Pad, poseidon2Unpad_poseidon2Pad] at hInv

/-- Complete byte-to-padded-rate-limbs pipeline (`bytesToLimbs56` composed with `poseidon2Pad`). -/
def poseidon2PadBytes (msg : List UInt8) : List Goldilocks :=
  poseidon2Pad (bytesToLimbs56 msg)

/-- **`poseidon2PadBytes_injective`**:
    Two distinct byte messages never map to the same `10*1`-padded Goldilocks sponge input. -/
theorem poseidon2PadBytes_injective {m₁ m₂ : List UInt8}
    (h : poseidon2PadBytes m₁ = poseidon2PadBytes m₂) : m₁ = m₂ :=
  bytesToLimbs56_injective (poseidon2Pad_injective h)

/-- Domain-separated initial Width-12 sponge state (`rate = 8`, `capacity = 4` = 256 bits). -/
def poseidon2InitState : Poseidon2State12 :=
  ⟨lane4Zero,
   lane4Zero,
   ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 4,
    Goldilocks.ofNat 32, Goldilocks.ofNat 0x504F53325F474C31⟩⟩

/-- Absorb one 8-limb rate block into lanes `0..7` (leaving capacity `b2` untouched), then permute. -/
def absorbRate8Block (st : Poseidon2State12) (r0 r1 : Lane4) : Poseidon2State12 :=
  poseidon2Perm12 ⟨lane4Add st.b0 r0, lane4Add st.b1 r1, st.b2⟩

/-- Absorb a padded limb stream in 8-element rate blocks. -/
def absorbLimbStream (st : Poseidon2State12) : List Goldilocks → Poseidon2State12
  | m0 :: m1 :: m2 :: m3 :: m4 :: m5 :: m6 :: m7 :: rest =>
    let st' := absorbRate8Block st ⟨m0, m1, m2, m3⟩ ⟨m4, m5, m6, m7⟩
    absorbLimbStream st' rest
  | _ => st

/-- Squeeze the first 4 Goldilocks elements (`b0`, 256 bits) as a 32-byte big-endian digest. -/
def squeeze32Bytes (st : Poseidon2State12) : List UInt8 :=
  be 8 st.b0.x0.val ++ be 8 st.b0.x1.val ++ be 8 st.b0.x2.val ++ be 8 st.b0.x3.val

/-- Squeeze encoding of `b0 : Lane4` into 32 bytes is lossless (`Goldilocks.val < p < 256^8`). -/
theorem squeeze32Bytes_b0_injective {s₁ s₂ : Poseidon2State12}
    (h : squeeze32Bytes s₁ = squeeze32Bytes s₂) : s₁.b0 = s₂.b0 := by
  unfold squeeze32Bytes at h
  simp only [List.append_assoc] at h
  obtain ⟨hx0, hrest1⟩ := List.append_inj h (by simp)
  obtain ⟨hx1, hrest2⟩ := List.append_inj hrest1 (by simp)
  obtain ⟨hx2, hx3⟩ := List.append_inj hrest2 (by simp)
  have hPow : (2 : Nat) ^ 64 = 256 ^ 8 := rfl
  exact Lane4.ext
    (Goldilocks.ext (be_injective (hPow ▸ Goldilocks.val_lt_two_pow_64 _) (hPow ▸ Goldilocks.val_lt_two_pow_64 _) hx0))
    (Goldilocks.ext (be_injective (hPow ▸ Goldilocks.val_lt_two_pow_64 _) (hPow ▸ Goldilocks.val_lt_two_pow_64 _) hx1))
    (Goldilocks.ext (be_injective (hPow ▸ Goldilocks.val_lt_two_pow_64 _) (hPow ▸ Goldilocks.val_lt_two_pow_64 _) hx2))
    (Goldilocks.ext (be_injective (hPow ▸ Goldilocks.val_lt_two_pow_64 _) (hPow ▸ Goldilocks.val_lt_two_pow_64 _) hx3))

/-- **256-Bit Algebraic Goldilocks `Poseidon2` Sponge Hash (`poseidon2Hash32 : HashBytes.Hash`)**:
    Frames `msg` into `< 2^56` Goldilocks limbs, applies injective `10*1` rate-8 padding,
    absorbs across Width-12 (`capacity = 4` = 256-bit) `poseidon2Perm12`, and squeezes 32 bytes. -/
@[expose] def poseidon2Hash32 : Hash := fun msg =>
  let finalSt := absorbLimbStream poseidon2InitState (poseidon2PadBytes msg)
  squeeze32Bytes finalSt

theorem poseidon2Hash32_length (msg : List UInt8) :
    (poseidon2Hash32 msg).length = 32 := by
  unfold poseidon2Hash32 squeeze32Bytes
  simp [length_be]

/-! Known answers, byte-identical to `poseidon2_perm12` and `poseidon2_hash32` in
`crates/obend-crypto-exec/src/goldilocks.rs`: the permutation of the zero state, and the digests of `[]`, `[0x00]`,
`[0x01, 0x02, 0x03]` and the 65 bytes `0x00 … 0x40` (two rate blocks). -/

example : (poseidon2Perm12 ⟨lane4Zero, lane4Zero, lane4Zero⟩).toList.map (·.val) =
    [444626622888223479, 10486189390627733761, 5399253379101132897, 5052010181030417489, 6267397916963039069,
     9245911245446346418, 9661705423445490201, 787089484585814203, 14953692268052641311, 11458212182116269477,
     16934754160153525625, 6948793053817514326] := by decide +kernel
example : poseidon2Hash32 [] =
    [138, 190, 114, 201, 171, 117, 245, 165, 115, 111, 42, 219, 119, 171, 10, 76, 186, 173, 182, 128, 209, 69, 108,
     220, 169, 239, 117, 130, 81, 43, 90, 65] := by decide +kernel
example : poseidon2Hash32 [0x00] =
    [233, 139, 182, 115, 89, 72, 21, 126, 245, 149, 62, 120, 26, 254, 106, 209, 111, 96, 153, 251, 141, 207, 186,
     100, 74, 174, 87, 99, 85, 43, 117, 48] := by decide +kernel
example : poseidon2Hash32 [0x01, 0x02, 0x03] =
    [196, 180, 177, 170, 216, 21, 133, 248, 62, 149, 42, 39, 133, 17, 81, 112, 144, 59, 209, 93, 95, 26, 110, 112,
     237, 219, 50, 120, 128, 103, 142, 202] := by decide +kernel
example : poseidon2Hash32 ((List.range 65).map UInt8.ofNat) =
    [39, 156, 89, 149, 6, 55, 81, 19, 223, 99, 122, 54, 228, 229, 22, 100, 172, 170, 142, 201, 25, 219, 70, 102,
     137, 73, 207, 135, 141, 48, 175, 71] := by decide +kernel

/-- Bundled `Hash32` instance plugging `poseidon2Hash32` directly into `CanopyMerklePCS` / `evalDigest32`. -/
@[expose] def poseidon2CanopyHash32 : Hash32 where
  eval := poseidon2Hash32
  len_eq := poseidon2Hash32_length

end Obend.Crypto
end
