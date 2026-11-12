module
/-
# Obend.Crypto.Multilinear — Polymorphic Commutative Rings, Goldilocks / Ext2 & Multilinear Algebra

Zero-Mathlib algebraic spine for Obend's dual-track post-quantum PIOP and PCS stack:
1. `CommRingOps R` and `LawfulCommRing R` with derived ring identities, including the
   hardware butterfly identity `lo + r * (hi - lo) = (1 - r) * lo + r * hi`.
2. Canonical 64-bit `Goldilocks` ($p = 2^{64} - 2^{32} + 1$) backed directly by the
   hardware-matched shift/mask reduction `Obend.Apps.ZkNtt.goldilocksReduce128Spec`,
   plus the 128-bit challenge quadratic extension `GoldilocksExt2` ($\mathbb{F}_p[u]/(u^2 - 7)$),
   both proved `LawfulCommRing`.
3. Multilinear Lagrange basis `eqPoly`, hypercube table evaluation `mleEval`,
   stride-2 wavefront folding `foldFirstVar`, and the universal folding soundness theorem
   `mleEval_foldFirstVar` (`mleEval (foldFirstVar tbl r₀) rs = mleEval tbl (r₀ :: rs)`).
-/
public import Obend.Apps.ZkNtt.Goldilocks

@[expose] public section
namespace Obend.Crypto

open Obend.Apps.ZkNtt

set_option autoImplicit false

/-! ## 1. Polymorphic Zero-Mathlib Commutative Ring Typeclasses -/

/-- Algebraic operations of a commutative ring with unity. -/
class CommRingOps (R : Type) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  sub : R → R → R

/-- Lawful commutative ring axioms over `CommRingOps R`. -/
class LawfulCommRing (R : Type) extends CommRingOps R where
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  zero_add : ∀ a : R, add zero a = a
  add_zero : ∀ a : R, add a zero = a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  sub_eq_add_neg : ∀ a b : R, sub a b = add a (neg b)
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : R, mul a b = mul b a
  one_mul : ∀ a : R, mul one a = a
  mul_one : ∀ a : R, mul a one = a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)

namespace LawfulCommRing
variable {R : Type} [LawfulCommRing R]
open CommRingOps

theorem add_right_neg (a : R) : add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem add_left_cancel {a b c : R} (h : add a b = add a c) : b = c := by
  have h1 : add (neg a) (add a b) = add (neg a) (add a c) := congrArg (add (neg a)) h
  rw [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1
  exact h1

theorem sub_self (a : R) : sub a a = zero := by
  rw [sub_eq_add_neg, add_right_neg]

theorem neg_zero (R : Type) [LawfulCommRing R] : neg (zero : R) = zero := by
  apply add_left_cancel (a := zero)
  rw [add_right_neg, add_zero]

theorem sub_zero (a : R) : sub a zero = a := by
  rw [sub_eq_add_neg, neg_zero R, add_zero]

theorem mul_zero (a : R) : mul a zero = zero := by
  apply add_left_cancel (a := mul a zero)
  rw [← left_distrib, add_zero, add_zero]

theorem zero_mul (a : R) : mul zero a = zero := by
  rw [mul_comm, mul_zero]

theorem neg_neg (a : R) : neg (neg a) = a := by
  apply add_left_cancel (a := neg a)
  rw [add_right_neg, add_left_neg]

theorem mul_neg (a b : R) : mul a (neg b) = neg (mul a b) := by
  apply add_left_cancel (a := mul a b)
  rw [← left_distrib, add_right_neg, mul_zero, add_right_neg]

theorem neg_mul (a b : R) : mul (neg a) b = neg (mul a b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem mul_sub (a b c : R) : mul a (sub b c) = sub (mul a b) (mul a c) := by
  rw [sub_eq_add_neg, left_distrib, mul_neg, ← sub_eq_add_neg]

theorem sub_mul (a b c : R) : mul (sub a b) c = sub (mul a c) (mul b c) := by
  rw [sub_eq_add_neg, right_distrib, neg_mul, ← sub_eq_add_neg]

theorem add_sub_cancel_left (a b : R) : add a (sub b a) = b := by
  rw [sub_eq_add_neg, add_comm b (neg a), ← add_assoc, add_right_neg, zero_add]

theorem add_add_add_comm (a b c d : R) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [add_assoc, ← add_assoc b c d, add_comm b c, add_assoc c b d, ← add_assoc]

/-- **Hardware Butterfly Identity**: `lo + r * (hi - lo) = (1 - r) * lo + r * hi`.
    Connects the 1-multiply RDNA2/FPGA sumcheck fold step to the 2-term Lagrange basis. -/
theorem foldStep_eq_barycentric (lo hi r : R) :
    add lo (mul r (sub hi lo)) = add (mul (sub one r) lo) (mul r hi) := by
  rw [sub_mul, one_mul, sub_eq_add_neg lo (mul r lo), add_assoc]
  congr 1
  rw [add_comm (neg (mul r lo)) (mul r hi), ← sub_eq_add_neg, ← mul_sub]

end LawfulCommRing

/-! ## 2. LawfulCommRing Instance for `Int` (Lattice / Ajtai / KKT Carrier) -/

instance : CommRingOps Int where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  sub := (· - ·)

instance : LawfulCommRing Int where
  add_assoc a b c := Int.add_assoc a b c
  add_comm a b := Int.add_comm a b
  zero_add a := Int.zero_add a
  add_zero a := Int.add_zero a
  add_left_neg a := Int.add_left_neg a
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  mul_assoc a b c := Int.mul_assoc a b c
  mul_comm a b := Int.mul_comm a b
  one_mul a := Int.one_mul a
  mul_one a := Int.mul_one a
  left_distrib a b c := Int.mul_add a b c
  right_distrib a b c := Int.add_mul a b c

/-! ## 3. Canonical 64-Bit Goldilocks Field ($p = 2^{64} - 2^{32} + 1$) -/

/-- Canonical element of the Goldilocks prime field $\mathbb{F}_p$ ($p = 2^{64} - 2^{32} + 1$). -/
structure Goldilocks where
  val : Nat
  isLt : val < goldilocksPrime
  deriving DecidableEq, Repr

namespace Goldilocks

theorem ext {a b : Goldilocks} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem val_lt_two_pow_64 (a : Goldilocks) : a.val < 2 ^ 64 := by
  have hp : goldilocksPrime < 2 ^ 64 := by decide
  exact Nat.lt_trans a.isLt hp

/-- Project any natural number modulo $p$ into canonical `Goldilocks`. -/
def ofNat (n : Nat) : Goldilocks :=
  ⟨n % goldilocksPrime, Nat.mod_lt n (by decide)⟩

def zero : Goldilocks := ⟨0, by decide⟩
def one : Goldilocks := ⟨1, by decide⟩

theorem canon_eq_val (a : Goldilocks) : goldilocksCanon64 a.val = a.val := by
  unfold goldilocksCanon64
  have h := a.isLt
  split <;> omega

/-- Hardware-exact Goldilocks addition via `goldilocksAddSpec`. -/
def add (a b : Goldilocks) : Goldilocks :=
  ⟨goldilocksAddSpec a.val b.val,
   (goldilocksAddSpec_spec (val_lt_two_pow_64 a) (val_lt_two_pow_64 b)).1⟩

theorem add_val (a b : Goldilocks) :
    (add a b).val = (a.val + b.val) % goldilocksPrime :=
  (goldilocksAddSpec_spec (val_lt_two_pow_64 a) (val_lt_two_pow_64 b)).2

/-- Hardware-exact Goldilocks subtraction via `goldilocksSubSpec`. -/
def sub (a b : Goldilocks) : Goldilocks :=
  ⟨goldilocksSubSpec a.val b.val,
   (goldilocksSubSpec_spec (val_lt_two_pow_64 a) (val_lt_two_pow_64 b)).1⟩

theorem sub_val (a b : Goldilocks) :
    (sub a b).val = (a.val + goldilocksPrime - b.val) % goldilocksPrime := by
  unfold sub
  dsimp only
  have h := (goldilocksSubSpec_spec (val_lt_two_pow_64 a) (val_lt_two_pow_64 b)).2
  simpa only [canon_eq_val] using h

/-- Canonical Goldilocks negation. -/
def neg (a : Goldilocks) : Goldilocks :=
  sub zero a

theorem neg_val (a : Goldilocks) :
    (neg a).val = (goldilocksPrime - a.val) % goldilocksPrime := by
  unfold neg
  simpa [zero] using sub_val zero a

/-- Hardware-exact Goldilocks multiplication via 128-to-64 `goldilocksReduce128Spec`. -/
def mul (a b : Goldilocks) : Goldilocks :=
  let prod := a.val * b.val
  let lo := prod % (2 ^ 64)
  let hi := prod / (2 ^ 64)
  have hLo : lo < 2 ^ 64 := Nat.mod_lt prod (by decide)
  have hHi : hi < 2 ^ 64 :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' (val_lt_two_pow_64 a) (val_lt_two_pow_64 b))
  ⟨goldilocksReduce128Spec lo hi, (goldilocksReduce128Spec_sound hLo hHi).1⟩

/-- Exact refinement between 128-to-64 `mul` and `(a.val * b.val) % goldilocksPrime`. -/
theorem mul_val (a b : Goldilocks) :
    (mul a b).val = (a.val * b.val) % goldilocksPrime := by
  unfold mul
  dsimp only
  have hLo : (a.val * b.val) % (2 ^ 64) < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hHi : (a.val * b.val) / (2 ^ 64) < 2 ^ 64 :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' (val_lt_two_pow_64 a) (val_lt_two_pow_64 b))
  rw [(goldilocksReduce128Spec_sound hLo hHi).2, Nat.mod_add_div]

instance : CommRingOps Goldilocks where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub

instance : LawfulCommRing Goldilocks where
  add_assoc a b c := by
    apply ext
    simp only [CommRingOps.add, add_val, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]
  add_comm a b := by
    apply ext
    simp only [CommRingOps.add, add_val, Nat.add_comm]
  zero_add a := by
    apply ext
    simp only [CommRingOps.add, CommRingOps.zero, add_val, zero, Nat.zero_add,
      Nat.mod_eq_of_lt a.isLt]
  add_zero a := by
    apply ext
    simp only [CommRingOps.add, CommRingOps.zero, add_val, zero, Nat.add_zero,
      Nat.mod_eq_of_lt a.isLt]
  add_left_neg a := by
    apply ext
    simp only [CommRingOps.add, CommRingOps.neg, CommRingOps.zero, add_val, neg_val, zero,
      Nat.mod_add_mod]
    have ha := a.isLt
    have hsum : goldilocksPrime - a.val + a.val = goldilocksPrime := by omega
    rw [hsum, Nat.mod_self]
  sub_eq_add_neg a b := by
    apply ext
    simp only [CommRingOps.sub, CommRingOps.add, CommRingOps.neg, sub_val, add_val, neg_val,
      Nat.add_mod_mod]
    have hb := b.isLt
    have h1 : a.val + (goldilocksPrime - b.val) = a.val + goldilocksPrime - b.val := by omega
    rw [h1]
  mul_assoc a b c := by
    apply ext
    simp only [CommRingOps.mul, mul_val]
    rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod]
  mul_comm a b := by
    apply ext
    simp only [CommRingOps.mul, mul_val, Nat.mul_comm]
  one_mul a := by
    apply ext
    simp only [CommRingOps.mul, CommRingOps.one, mul_val, one, Nat.one_mul,
      Nat.mod_eq_of_lt a.isLt]
  mul_one a := by
    apply ext
    simp only [CommRingOps.mul, CommRingOps.one, mul_val, one, Nat.mul_one,
      Nat.mod_eq_of_lt a.isLt]
  left_distrib a b c := by
    apply ext
    simp only [CommRingOps.mul, CommRingOps.add, mul_val, add_val]
    rw [Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_mod, ← Nat.left_distrib]
  right_distrib a b c := by
    apply ext
    simp only [CommRingOps.mul, CommRingOps.add, mul_val, add_val]
    rw [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, ← Nat.right_distrib]

end Goldilocks

/-! ## 4. Quadratic Challenge Extension `GoldilocksExt2` ($\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$) -/

/-- Quadratic extension $\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$ providing 128-bit Fiat–Shamir
    and sumcheck soundness over the 64-bit Goldilocks datapath ($7 \equiv 7 \pmod p$ is a non-residue
    since $p \equiv 6 \pmod 7$). -/
structure GoldilocksExt2 where
  c0 : Goldilocks
  c1 : Goldilocks
  deriving DecidableEq, Repr

namespace GoldilocksExt2

/-- Non-residue $w = 7$ defining $u^2 = 7$ in $\mathbb{F}_p$. -/
def nonResidue : Goldilocks := ⟨7, by decide⟩

theorem ext {x y : GoldilocksExt2} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; simp only at h0 h1; subst h0 h1; rfl

/-- Canonical embedding $\mathbb{F}_p \hookrightarrow \mathbb{F}_{p^2}$. -/
def ofBase (a : Goldilocks) : GoldilocksExt2 := ⟨a, CommRingOps.zero⟩

def zero : GoldilocksExt2 := ⟨CommRingOps.zero, CommRingOps.zero⟩
def one : GoldilocksExt2 := ⟨CommRingOps.one, CommRingOps.zero⟩
def uBasis : GoldilocksExt2 := ⟨CommRingOps.zero, CommRingOps.one⟩

def add (x y : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.add x.c0 y.c0, CommRingOps.add x.c1 y.c1⟩

def neg (x : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.neg x.c0, CommRingOps.neg x.c1⟩

def sub (x y : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.sub x.c0 y.c0, CommRingOps.sub x.c1 y.c1⟩

/-- $(a_0 + a_1 u)(b_0 + b_1 u) = (a_0 b_0 + 7 a_1 b_1) + (a_0 b_1 + a_1 b_0) u$. -/
def mul (x y : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.add (CommRingOps.mul x.c0 y.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)),
   CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)⟩

instance : CommRingOps GoldilocksExt2 where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub

instance : LawfulCommRing GoldilocksExt2 where
  add_assoc x y z :=
    ext (LawfulCommRing.add_assoc x.c0 y.c0 z.c0) (LawfulCommRing.add_assoc x.c1 y.c1 z.c1)
  add_comm x y :=
    ext (LawfulCommRing.add_comm x.c0 y.c0) (LawfulCommRing.add_comm x.c1 y.c1)
  zero_add x :=
    ext (LawfulCommRing.zero_add x.c0) (LawfulCommRing.zero_add x.c1)
  add_zero x :=
    ext (LawfulCommRing.add_zero x.c0) (LawfulCommRing.add_zero x.c1)
  add_left_neg x :=
    ext (LawfulCommRing.add_left_neg x.c0) (LawfulCommRing.add_left_neg x.c1)
  sub_eq_add_neg x y :=
    ext (LawfulCommRing.sub_eq_add_neg x.c0 y.c0) (LawfulCommRing.sub_eq_add_neg x.c1 y.c1)
  mul_comm x y := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 y.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) =
        CommRingOps.add (CommRingOps.mul y.c0 x.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 x.c1))
      rw [LawfulCommRing.mul_comm x.c0 y.c0, LawfulCommRing.mul_comm x.c1 y.c1]
    · change CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0) =
        CommRingOps.add (CommRingOps.mul y.c0 x.c1) (CommRingOps.mul y.c1 x.c0)
      rw [LawfulCommRing.mul_comm x.c0 y.c1, LawfulCommRing.mul_comm x.c1 y.c0,
          LawfulCommRing.add_comm]
  one_mul x := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul CommRingOps.one x.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul CommRingOps.zero x.c1)) = x.c0
      rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero,
          LawfulCommRing.add_zero]
    · change CommRingOps.add (CommRingOps.mul CommRingOps.one x.c1)
          (CommRingOps.mul CommRingOps.zero x.c0) = x.c1
      rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
  mul_one x := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 CommRingOps.one)
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 CommRingOps.zero)) = x.c0
      rw [LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
          LawfulCommRing.add_zero]
    · change CommRingOps.add (CommRingOps.mul x.c0 CommRingOps.zero)
          (CommRingOps.mul x.c1 CommRingOps.one) = x.c1
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.zero_add]
  left_distrib x y z := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 (CommRingOps.add y.c0 z.c0))
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.add y.c1 z.c1))) = _
      rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
    · change CommRingOps.add (CommRingOps.mul x.c0 (CommRingOps.add y.c1 z.c1))
          (CommRingOps.mul x.c1 (CommRingOps.add y.c0 z.c0)) = _
      rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
  right_distrib x y z := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c1)) = _
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c1)
          (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c0) = _
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
  mul_assoc x y z := by
    apply ext
    · change CommRingOps.add
          (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1))) z.c0)
          (CommRingOps.mul nonResidue
            (CommRingOps.mul
              (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)) z.c1)) =
        CommRingOps.add
          (CommRingOps.mul x.c0
            (CommRingOps.add (CommRingOps.mul y.c0 z.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))))
          (CommRingOps.mul nonResidue
            (CommRingOps.mul x.c1
              (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0))))
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
          LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
      have t1 : CommRingOps.mul (CommRingOps.mul x.c0 y.c0) z.c0 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c0) :=
        LawfulCommRing.mul_assoc _ _ _
      have t2 : CommRingOps.mul (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c0 =
          CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0)) := by
        rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc]
      have t3 : CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c1) =
          CommRingOps.mul x.c0 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc x.c0 y.c1 z.c1,
            ← LawfulCommRing.mul_assoc nonResidue x.c0 _,
            LawfulCommRing.mul_comm nonResidue x.c0,
            LawfulCommRing.mul_assoc]
      have t4 : CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c1) =
          CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c1)) := by
        rw [LawfulCommRing.mul_assoc x.c1 y.c0 z.c1]
      rw [t1, t2, t3, t4, LawfulCommRing.add_add_add_comm]
      congr 1
      exact LawfulCommRing.add_comm _ _
    · change CommRingOps.add
          (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1))) z.c1)
          (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)) z.c0) =
        CommRingOps.add
          (CommRingOps.mul x.c0
            (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0)))
          (CommRingOps.mul x.c1
            (CommRingOps.add (CommRingOps.mul y.c0 z.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))))
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
          LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
      have s1 : CommRingOps.mul (CommRingOps.mul x.c0 y.c0) z.c1 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c1) :=
        LawfulCommRing.mul_assoc _ _ _
      have s2 : CommRingOps.mul (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c1 =
          CommRingOps.mul x.c1 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc,
            ← LawfulCommRing.mul_assoc nonResidue x.c1 _,
            LawfulCommRing.mul_comm nonResidue x.c1,
            LawfulCommRing.mul_assoc]
      have s3 : CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c0 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c1 z.c0) :=
        LawfulCommRing.mul_assoc _ _ _
      have s4 : CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c0 =
          CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c0) :=
        LawfulCommRing.mul_assoc _ _ _
      rw [s1, s2, s3, s4, LawfulCommRing.add_add_add_comm]
      congr 1
      exact LawfulCommRing.add_comm _ _

/-- `ofBase` is an injective ring homomorphism $\mathbb{F}_p \hookrightarrow \mathbb{F}_{p^2}$. -/
theorem ofBase_injective {a b : Goldilocks} (h : ofBase a = ofBase b) : a = b :=
  congrArg GoldilocksExt2.c0 h

theorem ofBase_add (a b : Goldilocks) :
    ofBase (CommRingOps.add a b) = CommRingOps.add (ofBase a) (ofBase b) :=
  ext rfl (LawfulCommRing.add_zero (CommRingOps.zero : Goldilocks)).symm

theorem ofBase_mul (a b : Goldilocks) :
    ofBase (CommRingOps.mul a b) = CommRingOps.mul (ofBase a) (ofBase b) := by
  apply ext
  · change CommRingOps.mul a b =
      CommRingOps.add (CommRingOps.mul a b)
        (CommRingOps.mul nonResidue (CommRingOps.mul CommRingOps.zero CommRingOps.zero))
    rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  · change (CommRingOps.zero : Goldilocks) =
      CommRingOps.add (CommRingOps.mul a CommRingOps.zero) (CommRingOps.mul CommRingOps.zero b)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

end GoldilocksExt2

/-! ## 5. Multilinear Lagrange Basis, Table Evaluation & Partial-Point Folding -/

/-- Univariate multilinear Lagrange factor $(1 - r)$ for `false`, $r$ for `true`. -/
def eqBit {R : Type} [CommRingOps R] (r : R) (b : Bool) : R :=
  match b with
  | false => CommRingOps.sub CommRingOps.one r
  | true  => r

/-- Multilinear equality polynomial $\widetilde{\text{eq}}(\mathbf{r}, \mathbf{b}) =
    \prod_{i=0}^{v-1} ((1 - r_i)(1 - b_i) + r_i b_i)$. -/
def eqPoly {R : Type} [CommRingOps R] : List R → List Bool → R
  | [], [] => CommRingOps.one
  | r :: rs, b :: bs => CommRingOps.mul (eqBit r b) (eqPoly rs bs)
  | _, _ => CommRingOps.zero

/-- Boolean element embedding (`false ↦ 0`, `true ↦ 1`). -/
def bitElem {R : Type} [CommRingOps R] (b : Bool) : R :=
  if b then CommRingOps.one else CommRingOps.zero

theorem eqBit_diag {R : Type} [LawfulCommRing R] (b : Bool) :
    eqBit (bitElem (R := R) b) b = CommRingOps.one := by
  cases b
  · simp [eqBit, bitElem, LawfulCommRing.sub_zero]
  · rfl

theorem eqBit_off_diag {R : Type} [LawfulCommRing R] {b b' : Bool} (hne : b ≠ b') :
    eqBit (bitElem (R := R) b) b' = CommRingOps.zero := by
  cases b <;> cases b'
  · contradiction
  · rfl
  · simp [eqBit, bitElem, LawfulCommRing.sub_self]
  · contradiction

/-- Kronecker-delta property of `eqPoly` on the boolean hypercube $\{0,1\}^v$. -/
theorem eqPoly_kronecker {R : Type} [LawfulCommRing R] :
    ∀ (bs bs' : List Bool), bs.length = bs'.length →
      eqPoly (bs.map (bitElem (R := R))) bs' =
        if bs = bs' then CommRingOps.one else CommRingOps.zero
  | [], [], _ => by simp [eqPoly]
  | b :: bs, b' :: bs', hlen => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    simp only [List.map_cons, eqPoly]
    by_cases hb : b = b'
    · subst hb
      rw [eqBit_diag, LawfulCommRing.one_mul, eqPoly_kronecker bs bs' hlen]
      by_cases hbs : bs = bs' <;> simp [hbs]
    · rw [eqBit_off_diag hb, LawfulCommRing.zero_mul]
      have hne : b :: bs ≠ b' :: bs' := fun h => hb (List.cons.inj h).1
      simp [hne]

/-- Little-endian hypercube enumeration of $\{0,1\}^v$: adjacent pairs differ in coordinate $0$. -/
def hypercube : Nat → List (List Bool)
  | 0 => [[]]
  | v + 1 => (hypercube v).flatMap fun bs => [false :: bs, true :: bs]

theorem hypercube_length : ∀ v : Nat, (hypercube v).length = 2 ^ v
  | 0 => rfl
  | v + 1 => by
    have haux : ∀ (l : List (List Bool)),
        (l.flatMap fun bs => [false :: bs, true :: bs]).length = 2 * l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih => simp [List.flatMap_cons, ih]; omega
    rw [hypercube, haux, hypercube_length v, Nat.pow_succ, Nat.mul_comm]

/-- Inner product of two lists in `R` (padded with `0` if lengths differ). -/
def innerProd {R : Type} [CommRingOps R] : List R → List R → R
  | [], _ => CommRingOps.zero
  | _, [] => CommRingOps.zero
  | x :: xs, y :: ys => CommRingOps.add (CommRingOps.mul x y) (innerProd xs ys)

/-- Multilinear extension evaluation $\tilde{f}(\mathbf{r}) = \sum_{\mathbf{b} \in \{0,1\}^v}
    \text{tbl}[\mathbf{b}] \cdot \widetilde{\text{eq}}(\mathbf{r}, \mathbf{b})$. -/
def mleEval {R : Type} [CommRingOps R] (tbl : List R) (rs : List R) : R :=
  innerProd tbl ((hypercube rs.length).map (eqPoly rs))

/-- Partial-point folding of the first variable at `r₀`:
    replaces each adjacent `(lo, hi)` butterfly pair with `lo + r₀ * (hi - lo)`
    (exact inner loop of RDNA2 wavefront and FPGA BRAM sumcheck). -/
def foldFirstVar {R : Type} [CommRingOps R] : List R → R → List R
  | lo :: hi :: rest, r₀ =>
    CommRingOps.add lo (CommRingOps.mul r₀ (CommRingOps.sub hi lo)) :: foldFirstVar rest r₀
  | [lo], r₀ =>
    [CommRingOps.add lo (CommRingOps.mul r₀ (CommRingOps.sub CommRingOps.zero lo))]
  | [], _ => []

theorem foldFirstVar_length {R : Type} [CommRingOps R] :
    ∀ (tbl : List R) (r₀ : R), (foldFirstVar tbl r₀).length = (tbl.length + 1) / 2
  | [], _ => by simp [foldFirstVar]
  | [_], _ => by simp [foldFirstVar]
  | _ :: _ :: rest, r₀ => by
    simp only [foldFirstVar, List.length_cons, foldFirstVar_length rest r₀]
    omega

theorem flatMap_eqPoly_cons {R : Type} [CommRingOps R] (r₀ : R) (rs : List R) :
    ∀ (cubes : List (List Bool)),
      (cubes.flatMap fun bs => [false :: bs, true :: bs]).map (eqPoly (r₀ :: rs)) =
        (cubes.map (eqPoly rs)).flatMap fun w =>
          [CommRingOps.mul (CommRingOps.sub CommRingOps.one r₀) w, CommRingOps.mul r₀ w]
  | [] => rfl
  | bs :: rest => by
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil, eqPoly, eqBit,
      flatMap_eqPoly_cons r₀ rs rest]

theorem innerProd_foldFirstVar_aux {R : Type} [LawfulCommRing R] (r₀ : R) :
    ∀ (ws : List R) (tbl : List R),
      innerProd (foldFirstVar tbl r₀) ws =
        innerProd tbl (ws.flatMap fun w =>
          [CommRingOps.mul (CommRingOps.sub CommRingOps.one r₀) w, CommRingOps.mul r₀ w])
  | [], tbl => by
    cases tbl with
    | nil => rfl
    | cons _ tl =>
      cases tl <;> rfl
  | w :: ws, [] => rfl
  | w :: ws, [lo] => by
    simp only [foldFirstVar, List.flatMap_cons, List.cons_append, List.nil_append, innerProd]
    rw [LawfulCommRing.add_zero, LawfulCommRing.add_zero]
    rw [LawfulCommRing.foldStep_eq_barycentric, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rw [LawfulCommRing.mul_comm (CommRingOps.sub CommRingOps.one r₀) lo, LawfulCommRing.mul_assoc]
  | w :: ws, lo :: hi :: rest => by
    simp only [foldFirstVar, List.flatMap_cons, List.cons_append, List.nil_append, innerProd]
    rw [innerProd_foldFirstVar_aux r₀ ws rest]
    rw [LawfulCommRing.foldStep_eq_barycentric, LawfulCommRing.right_distrib]
    rw [LawfulCommRing.mul_comm (CommRingOps.sub CommRingOps.one r₀) lo, LawfulCommRing.mul_assoc]
    rw [LawfulCommRing.mul_comm r₀ hi, LawfulCommRing.mul_assoc]
    rw [LawfulCommRing.add_assoc]

/-- **Multilinear Partial-Point Folding Theorem (`mleEval_foldFirstVar`)**:
    Evaluating `foldFirstVar tbl r₀` at `rs` equals evaluating `tbl` at `r₀ :: rs`,
    for every lawful commutative ring `R`, table `tbl`, and evaluation coordinates `r₀ :: rs`. -/
theorem mleEval_foldFirstVar {R : Type} [LawfulCommRing R]
    (tbl : List R) (r₀ : R) (rs : List R) :
    mleEval (foldFirstVar tbl r₀) rs = mleEval tbl (r₀ :: rs) := by
  unfold mleEval
  simp only [List.length_cons, hypercube]
  rw [flatMap_eqPoly_cons, innerProd_foldFirstVar_aux]

/-- Sum of `tbl` over the $v$-dimensional boolean hypercube $\{0,1\}^v$. -/
def hypercubeSum {R : Type} [CommRingOps R] (v : Nat) (tbl : List R) : R :=
  innerProd tbl ((hypercube v).map fun _ => CommRingOps.one)

theorem hypercubeSum_zero {R : Type} [LawfulCommRing R] (tbl : List R) :
    hypercubeSum 0 tbl = mleEval tbl [] := by
  rfl

theorem innerProd_ones_split {R : Type} [LawfulCommRing R] :
    ∀ (ones : List R) (tbl : List R),
      innerProd tbl (ones.flatMap fun u => [u, u]) =
        CommRingOps.add (innerProd (foldFirstVar tbl CommRingOps.zero) ones)
                        (innerProd (foldFirstVar tbl CommRingOps.one) ones)
  | [], tbl => by
    cases tbl with
    | nil => simp [innerProd, foldFirstVar, LawfulCommRing.add_zero]
    | cons _ tl =>
      cases tl <;> simp [innerProd, foldFirstVar, LawfulCommRing.add_zero]
  | u :: us, [] => by
    simp [innerProd, foldFirstVar, LawfulCommRing.add_zero]
  | u :: us, [lo] => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, innerProd, foldFirstVar]
    rw [LawfulCommRing.add_zero, LawfulCommRing.add_zero, LawfulCommRing.add_zero]
    rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [LawfulCommRing.one_mul, LawfulCommRing.add_sub_cancel_left, LawfulCommRing.zero_mul,
        LawfulCommRing.add_zero]
  | u :: us, lo :: hi :: rest => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, innerProd, foldFirstVar]
    rw [innerProd_ones_split us rest]
    rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [LawfulCommRing.one_mul, LawfulCommRing.add_sub_cancel_left]
    rw [LawfulCommRing.add_add_add_comm, LawfulCommRing.add_assoc]

theorem flatMap_const_one {R : Type} [CommRingOps R] :
    ∀ (cubes : List (List Bool)),
      (cubes.flatMap fun bs => [false :: bs, true :: bs]).map (fun _ => (CommRingOps.one : R)) =
        (cubes.map fun _ => (CommRingOps.one : R)).flatMap fun u => [u, u]
  | [] => rfl
  | _ :: rest => by
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
      flatMap_const_one rest]

/-- **Hypercube Split Identity**:
    $\sum_{x \in \{0,1\}^{v+1}} \tilde{f}(x) =
     \sum_{x' \in \{0,1\}^v} \tilde{f}(0, x') + \sum_{x' \in \{0,1\}^v} \tilde{f}(1, x')$. -/
theorem hypercubeSum_succ {R : Type} [LawfulCommRing R] (v : Nat) (tbl : List R) :
    hypercubeSum (v + 1) tbl =
      CommRingOps.add (hypercubeSum v (foldFirstVar tbl CommRingOps.zero))
                      (hypercubeSum v (foldFirstVar tbl CommRingOps.one)) := by
  unfold hypercubeSum
  simp only [hypercube]
  rw [flatMap_const_one, innerProd_ones_split]

/-- Linear dependence of `hypercubeSum v (foldFirstVar tbl r)` on $r$:
    $\sum_{x' \in \{0,1\}^v} \tilde{f}(r, x') = s_0 + r \cdot (s_1 - s_0)$. -/
theorem innerProd_foldFirstVar_linear {R : Type} [LawfulCommRing R] (r : R) :
    ∀ (ones : List R) (tbl : List R),
      innerProd (foldFirstVar tbl r) ones =
        CommRingOps.add
          (innerProd (foldFirstVar tbl CommRingOps.zero) ones)
          (CommRingOps.mul r (CommRingOps.sub
            (innerProd (foldFirstVar tbl CommRingOps.one) ones)
            (innerProd (foldFirstVar tbl CommRingOps.zero) ones)))
  | [], tbl => by
    cases tbl with
    | nil =>
      simp [innerProd, foldFirstVar, LawfulCommRing.sub_self,
            LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | cons _ tl =>
      cases tl <;>
        simp [innerProd, foldFirstVar, LawfulCommRing.sub_self,
              LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | u :: us, [] => by
    simp [innerProd, foldFirstVar, LawfulCommRing.sub_self,
          LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | u :: us, [lo] => by
    simp only [innerProd, foldFirstVar]
    rw [LawfulCommRing.add_zero, LawfulCommRing.add_zero, LawfulCommRing.add_zero]
    rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [LawfulCommRing.one_mul, LawfulCommRing.add_sub_cancel_left, LawfulCommRing.zero_mul]
    rw [LawfulCommRing.right_distrib, LawfulCommRing.mul_assoc,
        LawfulCommRing.sub_mul, LawfulCommRing.zero_mul]
  | u :: us, lo :: hi :: rest => by
    simp only [innerProd, foldFirstVar]
    rw [innerProd_foldFirstVar_linear r us rest]
    rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [LawfulCommRing.one_mul, LawfulCommRing.add_sub_cancel_left]
    rw [LawfulCommRing.right_distrib, LawfulCommRing.mul_assoc, LawfulCommRing.sub_mul]
    let s0 := innerProd (foldFirstVar rest CommRingOps.zero) us
    let s1 := innerProd (foldFirstVar rest CommRingOps.one) us
    have hsub : CommRingOps.sub (CommRingOps.add (CommRingOps.mul hi u) s1)
                                (CommRingOps.add (CommRingOps.mul lo u) s0) =
                CommRingOps.add (CommRingOps.sub (CommRingOps.mul hi u) (CommRingOps.mul lo u))
                                (CommRingOps.sub s1 s0) := by
      apply LawfulCommRing.add_left_cancel
        (a := CommRingOps.add (CommRingOps.mul lo u) s0)
      rw [LawfulCommRing.add_sub_cancel_left]
      rw [LawfulCommRing.add_add_add_comm,
          LawfulCommRing.add_sub_cancel_left,
          LawfulCommRing.add_sub_cancel_left]
    rw [hsub, LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem hypercubeSum_foldFirstVar {R : Type} [LawfulCommRing R]
    (v : Nat) (tbl : List R) (r : R) :
    hypercubeSum v (foldFirstVar tbl r) =
      CommRingOps.add (hypercubeSum v (foldFirstVar tbl CommRingOps.zero))
        (CommRingOps.mul r (CommRingOps.sub
          (hypercubeSum v (foldFirstVar tbl CommRingOps.one))
          (hypercubeSum v (foldFirstVar tbl CommRingOps.zero)))) :=
  innerProd_foldFirstVar_linear r ((hypercube v).map fun _ => CommRingOps.one) tbl

end Obend.Crypto
end
