module
/-
# Obend.SymbolicZk.CompileToPiopCore — Field Primality, `Before` Range-Safe Weld & `LinMem` Characteristic Polynomials

Core algebraic & polynomial substrate for `Obend.SymbolicZk.CompileToPiop` over
`Obend.Crypto.Multilinear`, `Obend.Crypto.Transcript`, `Obend.Crypto.Sumcheck`, and
`Obend.Core.RangeSafe`:
1. Constructive Proth primality `goldilocksPrime_isPrime` and `LawfulIntegralDomain` / `LawfulField`
   instances for `Goldilocks` ($p = 2^{64} - 2^{32} + 1$).
2. `Before` arithmetization (`beforePolyConstraint_iff_lt`) with `RangeSafe` no-wrap guard
   $2 \cdot 2^w \le p$, `Spec ↔ Array` execution, and 63-bit wraparound refutation.
3. `LinMem` characteristic-product weld (`charPoly_eq_iff_perm`, `linmemPolyIdentity_implies_perm`)
   with Ruffini synthetic division and constructive univariate Schwartz–Zippel root bound.
-/
public import Obend.Core.RangeSafe
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript
public import Obend.Crypto.Sumcheck

public section
namespace Obend.SymbolicZk.CompileToPiop

open Obend.Apps.ZkNtt (goldilocksPrime)
open Obend.Core.RangeSafe
open Obend.Crypto

set_option autoImplicit false

/-! ## 1. `LawfulIntegralDomain`, Proth Primality of `Goldilocks`, and `LawfulField` -/

class LawfulIntegralDomain (R : Type) extends LawfulCommRing R where
  zero_ne_one : zero ≠ one
  mul_eq_zero : ∀ a b : R, mul a b = zero → a = zero ∨ b = zero

namespace LawfulIntegralDomain
variable {R : Type} [LawfulIntegralDomain R]
open CommRingOps

theorem mul_eq_zero_iff (a b : R) : mul a b = zero ↔ a = zero ∨ b = zero :=
  ⟨mul_eq_zero a b, fun h => by
    rcases h with rfl | rfl; exact LawfulCommRing.zero_mul b; exact LawfulCommRing.mul_zero a⟩

theorem mul_ne_zero {a b : R} (ha : a ≠ zero) (hb : b ≠ zero) : mul a b ≠ zero :=
  fun h => (mul_eq_zero a b h).elim ha hb

theorem sub_eq_zero_iff (a b : R) : sub a b = zero ↔ a = b :=
  ⟨eq_of_sub_eq_zero, fun h => h ▸ LawfulCommRing.sub_self a⟩

theorem mul_left_cancel {a b c : R} (ha : a ≠ zero) (h : mul a b = mul a c) : b = c := by
  have hsub : mul a (sub b c) = zero := by rw [LawfulCommRing.mul_sub, h, LawfulCommRing.sub_self]
  exact (mul_eq_zero a (sub b c) hsub).elim (fun h0 => absurd h0 ha) eq_of_sub_eq_zero

theorem mul_right_cancel {a b c : R} (hc : c ≠ zero) (h : mul a c = mul b c) : a = b := by
  apply mul_left_cancel hc; rw [LawfulCommRing.mul_comm c a, LawfulCommRing.mul_comm c b]; exact h
end LawfulIntegralDomain

instance : LawfulIntegralDomain Int where
  zero_ne_one := by decide
  mul_eq_zero a b h := Int.mul_eq_zero.mp h

class LawfulField (F : Type) extends LawfulIntegralDomain F where
  inv : F → F
  inv_zero : inv zero = zero
  mul_inv_cancel : ∀ a : F, a ≠ zero → mul a (inv a) = one

def powModSpec (b : Nat) : Nat → Nat → Nat
  | 0, m => 1 % m
  | e + 1, m => (powModSpec b e m * (b % m)) % m

private theorem powModSpec_lt {b : Nat} : ∀ {e m : Nat}, 0 < m → powModSpec b e m < m
  | 0, _, hm => Nat.mod_lt 1 hm
  | _ + 1, _, hm => Nat.mod_lt _ hm

private theorem powModSpec_self_mod (b : Nat) : ∀ (e m : Nat), powModSpec b e m % m = powModSpec b e m
  | 0, m => Nat.mod_mod 1 m
  | _ + 1, m => Nat.mod_mod _ m

private theorem powModSpec_add (b e₁ : Nat) :
    ∀ (e₂ m : Nat), powModSpec b (e₁ + e₂) m = (powModSpec b e₁ m * powModSpec b e₂ m) % m
  | 0, m => by
    rw [Nat.add_zero, powModSpec, Nat.mul_mod_mod, Nat.mul_one]
    exact (powModSpec_self_mod b e₁ m).symm
  | k + 1, m => by
    rw [← Nat.add_assoc, powModSpec, powModSpec, powModSpec_add b e₁ k m,
        Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod]

private theorem powModSpec_mul (b e₁ : Nat) :
    ∀ (e₂ m : Nat), powModSpec b (e₁ * e₂) m = powModSpec (powModSpec b e₁ m) e₂ m
  | 0, _ => rfl
  | k + 1, m => by
    rw [Nat.mul_succ, powModSpec_add, powModSpec_mul b e₁ k m, powModSpec,
        powModSpec_self_mod, Nat.mul_comm]

private theorem powModSpec_one_base : ∀ (e m : Nat), powModSpec 1 e m = 1 % m
  | 0, _ => rfl
  | k + 1, m => by rw [powModSpec, powModSpec_one_base k m, Nat.mod_mul_mod, Nat.one_mul, Nat.mod_mod]

private theorem powModSpec_mod_of_dvd {b e p q : Nat} (hdvd : q ∣ p) :
    powModSpec b e p % q = powModSpec (b % q) e q := by
  rcases hdvd with ⟨k, hp⟩; rw [Nat.mul_comm] at hp; subst hp
  induction e with
  | zero => simp only [powModSpec]; exact Nat.mod_mul_left_mod 1 k q
  | succ n ih =>
    simp only [powModSpec]
    rw [Nat.mod_mul_left_mod, Nat.mul_mod (powModSpec b n (k * q)), ih,
        Nat.mod_mul_left_mod b k q, Nat.mod_mod]

def sqModIter : Nat → Nat → Nat → Nat
  | x, 0, m => x % m
  | x, k + 1, m => sqModIter ((x * x) % m) k m

private theorem powModSpec_mod_base (b e m : Nat) : powModSpec (b % m) e m = powModSpec b e m := by
  induction e with | zero => rfl | succ k ih => simp [powModSpec, ih]

private theorem sqModIter_eq : ∀ (k x m : Nat), sqModIter x k m = powModSpec x (2 ^ k) m
  | 0, x, m => by simp only [sqModIter, Nat.pow_zero, powModSpec]; rw [Nat.mod_mul_mod, Nat.one_mul, Nat.mod_mod]
  | k + 1, x, m => by
    rw [sqModIter, sqModIter_eq k ((x * x) % m) m, powModSpec_mod_base,
        show 2 ^ (k + 1) = 2 * 2 ^ k by rw [Nat.pow_succ, Nat.mul_comm], powModSpec_mul]
    have h2 : powModSpec x 2 m = (x * x) % m := by
      change ((1 % m * (x % m)) % m * (x % m)) % m = (x * x) % m
      rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mod_mul_mod, Nat.one_mul, ← Nat.mul_mod]
    rw [h2, powModSpec_mod_base]

def goldilocksRoot2Pow32 : Nat := 1753635133440165772

private theorem goldilocks_proth_euler :
    powModSpec goldilocksRoot2Pow32 (2 ^ 31) goldilocksPrime = goldilocksPrime - 1 := by
  have s1 : powModSpec goldilocksRoot2Pow32 (2 ^ 8) goldilocksPrime = 9713644485405565297 := by
    rw [← sqModIter_eq]; decide
  have s2 : powModSpec 9713644485405565297 (2 ^ 8) goldilocksPrime = 6115771955107415310 := by
    rw [← sqModIter_eq]; decide
  have s3 : powModSpec 6115771955107415310 (2 ^ 8) goldilocksPrime = 13797081185216407910 := by
    rw [← sqModIter_eq]; decide
  have s4 : powModSpec 13797081185216407910 (2 ^ 7) goldilocksPrime = goldilocksPrime - 1 := by
    rw [← sqModIter_eq]; decide
  rw [show (2 : Nat) ^ 31 = 2 ^ 8 * 2 ^ 8 * 2 ^ 8 * 2 ^ 7 by decide,
      powModSpec_mul, powModSpec_mul, powModSpec_mul, s1, s2, s3, s4]

private theorem dvd_two_pow_dichotomy {d : Nat} :
    ∀ n : Nat, d ∣ 2 ^ (n + 1) → d = 2 ^ (n + 1) ∨ d ∣ 2 ^ n
  | 0, ⟨k, hk⟩ => by
    match d with
    | 0 => simp at hk
    | 1 => exact .inr ⟨1, rfl⟩
    | 2 => exact .inl rfl
    | d' + 3 =>
      cases k with
      | zero => simp at hk
      | succ k' => have : 3 ≤ (d' + 3) * (k' + 1) := by rw [Nat.mul_succ]; omega
                   simp at hk; omega
  | n + 1, hd => by
    have hpow2 : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hpow1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases heven : d % 2 = 0
    · have hdEq : d = 2 * (d / 2) := by have := Nat.div_add_mod d 2; omega
      have hd' : (d / 2) ∣ 2 ^ (n + 1) := by
        rcases hd with ⟨k, hk⟩; rw [hpow2, hdEq, Nat.mul_assoc] at hk
        exact ⟨k, Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hk⟩
      rcases dvd_two_pow_dichotomy n hd' with hEq | ⟨m, hm⟩
      · left; rw [hdEq, hEq, ← hpow2]
      · right; exact ⟨m, by rw [hpow1, hdEq, hm, Nat.mul_assoc]⟩
    · right
      have hcop : Nat.Coprime d 2 := by
        unfold Nat.Coprime
        have := Nat.le_of_dvd (by decide : 0 < 2) (Nat.gcd_dvd_right d 2)
        have := Nat.gcd_pos_of_pos_right d (by decide : 0 < 2)
        have : Nat.gcd d 2 ≠ 2 := fun h2 => by
          rcases (h2 ▸ Nat.gcd_dvd_left d 2 : 2 ∣ d) with ⟨_, rfl⟩; omega
        omega
      exact hcop.dvd_of_dvd_mul_right (show d ∣ 2 ^ (n + 1) * 2 from hd)

theorem nodup_sublist_len_le {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ z ∈ l₁, z ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: as, l₂, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha := hsub a List.mem_cons_self
    have hle := nodup_sublist_len_le as (l₂.erase a) hnd.2 fun z hz =>
      (List.mem_erase_of_ne (fun heq => by subst heq; exact hnd.1 hz)).mpr (hsub z (List.mem_cons_of_mem a hz))
    have := List.length_erase_of_mem ha; have := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

private theorem exists_min_nat {P : Nat → Prop} [DecidablePred P] :
    ∀ (n : Nat), P n → ∃ m, m ≤ n ∧ P m ∧ ∀ k, k < m → ¬ P k := by
  intro n; induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    cases hfilt : (List.range n).filter (fun k => decide (P k)) with
    | nil =>
      refine ⟨n, Nat.le_refl n, hn, fun k hk hkP => ?_⟩
      have hmem : k ∈ (List.range n).filter (fun x => decide (P x)) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr hk, decide_eq_true hkP⟩
      rw [hfilt] at hmem; cases hmem
    | cons k _ =>
      have hkMem : k ∈ (List.range n).filter (fun x => decide (P x)) := by rw [hfilt]; exact List.mem_cons_self
      rw [List.mem_filter] at hkMem
      obtain ⟨m, hmk, hmP, hmMin⟩ := ih k (List.mem_range.mp hkMem.1) (of_decide_eq_true hkMem.2)
      exact ⟨m, by have := List.mem_range.mp hkMem.1; omega, hmP, hmMin⟩

private theorem nodup_map_of_lt_inj {β : Type} (f : Nat → β) :
    ∀ (l : List Nat), l.Pairwise (· < ·) → (∀ i ∈ l, ∀ j ∈ l, i < j → f i ≠ f j) → (l.map f).Nodup
  | [], _, _ => List.Pairwise.nil
  | x :: xs, hpw, hinj => by
    rw [List.pairwise_cons] at hpw; simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨fun ⟨y, hy, hfy⟩ => hinj x List.mem_cons_self y (List.mem_cons_of_mem x hy) (hpw.1 y hy) hfy.symm,
      nodup_map_of_lt_inj f xs hpw.2 (fun i hi j hj => hinj i (List.mem_cons_of_mem x hi) j (List.mem_cons_of_mem x hj))⟩

private theorem pairwise_lt_range : ∀ n : Nat, (List.range n).Pairwise (· < ·)
  | 0 => List.Pairwise.nil
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    refine ⟨pairwise_lt_range n, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb; exact List.mem_range.mp ha

/-- **Constructive Proth Primality Theorem for `goldilocksPrime` ($p = 2^{64} - 2^{32} + 1$)**. -/
theorem goldilocksPrime_isPrime (d : Nat) (hd : d ∣ goldilocksPrime) :
    d = 1 ∨ d = goldilocksPrime := by
  have hpPos : 0 < goldilocksPrime := by decide
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hpPos
  by_cases hd1 : d = 1; · exact .inl hd1
  by_cases hdp : d = goldilocksPrime; · exact .inr hdp
  exfalso; rcases hd with ⟨e, he⟩
  have heGt1 : 1 < e := by
    by_cases he0 : e = 0; · subst he0; unfold goldilocksPrime at he; omega
    by_cases he1 : e = 1; · subst he1; simp at he; exact absurd he.symm hdp
    omega
  have hSmall : ∃ q, 1 < q ∧ q < 2 ^ 32 ∧ q ∣ goldilocksPrime := by
    by_cases hdSmall : d < 2 ^ 32
    · exact ⟨d, by omega, hdSmall, ⟨e, he⟩⟩
    · refine ⟨e, heGt1, Decidable.byContradiction fun heBig => ?_, ⟨d, by rw [Nat.mul_comm]; exact he⟩⟩
      have hge := Nat.mul_le_mul (show 2 ^ 32 ≤ d by omega) (show 2 ^ 32 ≤ e by omega)
      have hpLt : goldilocksPrime < 2 ^ 32 * 2 ^ 32 := by decide
      omega
  rcases hSmall with ⟨q, hqGt1, hqLt32, hqDvd⟩
  have hqGe3 : 3 ≤ q := by
    by_cases hq2 : q = 2
    · subst hq2; rcases hqDvd with ⟨m, hm⟩; have : goldilocksPrime % 2 = 1 := by decide
      omega
    · omega
  let a := goldilocksRoot2Pow32 % q
  have haHalf : powModSpec a (2 ^ 31) q = q - 1 := by
    rw [← powModSpec_mod_of_dvd hqDvd, goldilocks_proth_euler]
    rcases hqDvd with ⟨m, hm⟩
    have hmPos : 0 < m := by by_cases hm0 : m = 0; · subst hm0; unfold goldilocksPrime at hm; omega
                             omega
    have hRewrite : goldilocksPrime - 1 = (q - 1) + q * (m - 1) := by
      have : q * m = q * 1 + q * (m - 1) := by rw [← Nat.left_distrib]; congr 1; omega
      omega
    rw [hRewrite, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have haFull : powModSpec a (2 ^ 32) q = 1 := by
    rw [show (2 : Nat) ^ 32 = (2 ^ 31) * 2 by decide, powModSpec_mul, haHalf, powModSpec, powModSpec, powModSpec]
    have h1q : 1 % q = 1 := Nat.mod_eq_of_lt hqGt1
    have hqm : (q - 1) % q = q - 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1q, hqm, Nat.one_mul, hqm]
    have hsq : (q - 1) * (q - 1) = 1 + q * (q - 2) := by
      match q with
      | 0 | 1 | 2 => omega
      | q2 + 3 =>
        change (q2 + 2) * (q2 + 2) = 1 + (q2 + 3) * (q2 + 1)
        calc (q2 + 2) * (q2 + 2) = (q2 + 2) * (q2 + 1) + (q2 + 2) := rfl
          _ = 1 + (q2 + 3) * (q2 + 1) := by
            rw [show (q2 + 3) = (q2 + 2) + 1 from rfl, Nat.add_mul (q2 + 2) 1 (q2 + 1), Nat.one_mul]; omega
    rw [hsq, Nat.add_mul_mod_self_left, h1q]
  obtain ⟨d₀, _, ⟨hd₀Pos, hd₀Eq1⟩, hd₀Min⟩ :=
    exists_min_nat (P := fun k => 0 < k ∧ powModSpec a k q = 1) (2 ^ 32) ⟨by decide, haFull⟩
  have hd₀Dvd : d₀ ∣ 2 ^ 32 := by
    refine ⟨2 ^ 32 / d₀, ?_⟩
    by_cases hrem0 : 2 ^ 32 % d₀ = 0
    · have := Nat.div_add_mod (2 ^ 32) d₀; omega
    · exfalso; have h1 := haFull
      rw [(Nat.div_add_mod (2 ^ 32) d₀).symm, powModSpec_add, powModSpec_mul, hd₀Eq1, powModSpec_one_base,
          Nat.mod_eq_of_lt hqGt1, Nat.one_mul, Nat.mod_eq_of_lt (powModSpec_lt (by omega))] at h1
      exact hd₀Min (2 ^ 32 % d₀) (Nat.mod_lt _ hd₀Pos) ⟨Nat.pos_of_ne_zero hrem0, h1⟩
  have _hd₀Eq32 : d₀ = 2 ^ 32 := by
    rcases dvd_two_pow_dichotomy 31 hd₀Dvd with hEq | ⟨k, hk⟩
    · exact hEq
    · exfalso
      have hHalf1 : powModSpec a (2 ^ 31) q = 1 := by
        rw [hk, powModSpec_mul, hd₀Eq1, powModSpec_one_base, Nat.mod_eq_of_lt hqGt1]
      rw [haHalf] at hHalf1; omega
  let orb := (List.range (2 ^ 32)).map (fun i => powModSpec a i q)
  have horbNodup : orb.Nodup := by
    apply nodup_map_of_lt_inj _ (List.range (2 ^ 32)) (pairwise_lt_range _)
    intro i hi j hj hij hEq; rw [List.mem_range] at hi hj
    have hmul : (powModSpec a i q * powModSpec a (2 ^ 32 - j) q) % q =
        (powModSpec a j q * powModSpec a (2 ^ 32 - j) q) % q := by rw [hEq]
    rw [← powModSpec_add, ← powModSpec_add, show j + (2 ^ 32 - j) = 2 ^ 32 by omega, haFull] at hmul
    exact hd₀Min (i + (2 ^ 32 - j)) (by omega) ⟨by omega, hmul⟩
  have horbBounds : ∀ y ∈ orb, y ∈ (List.range q).erase 0 := by
    intro y hy; rcases List.mem_map.mp hy with ⟨i, hi, rfl⟩; rw [List.mem_range] at hi
    have hne0 : powModSpec a i q ≠ 0 := fun hz => by
      have h1 : powModSpec a (i + (2 ^ 32 - i)) q = 1 := by rw [show i + (2 ^ 32 - i) = 2 ^ 32 by omega, haFull]
      rw [powModSpec_add, hz, Nat.zero_mul, Nat.zero_mod] at h1; omega
    exact (List.mem_erase_of_ne hne0).mpr (List.mem_range.mpr (powModSpec_lt (by omega)))
  have hLenLe := nodup_sublist_len_le orb ((List.range q).erase 0) horbNodup horbBounds
  rw [List.length_erase_of_mem (List.mem_range.mpr (by omega)), List.length_range] at hLenLe
  simp only [orb, List.length_map, List.length_range] at hLenLe; omega

theorem goldilocksPrime_dvd_mul {a b : Nat} (h : goldilocksPrime ∣ a * b) :
    goldilocksPrime ∣ a ∨ goldilocksPrime ∣ b := by
  by_cases ha : a % goldilocksPrime = 0
  · exact .inl (Nat.dvd_of_mod_eq_zero ha)
  · right
    have hnot : ¬ (goldilocksPrime ∣ a) := fun ⟨k, hk⟩ => ha (by rw [hk, Nat.mul_mod_right])
    have hcop : Nat.Coprime goldilocksPrime a :=
      (goldilocksPrime_isPrime _ (Nat.gcd_dvd_left goldilocksPrime a)).resolve_right
        fun hp => hnot (hp ▸ Nat.gcd_dvd_right goldilocksPrime a)
    exact hcop.dvd_of_dvd_mul_left h

instance : LawfulIntegralDomain Goldilocks where
  zero_ne_one h := by
    have hv := congrArg Goldilocks.val h
    simp [CommRingOps.zero, CommRingOps.one, Goldilocks.zero, Goldilocks.one] at hv
  mul_eq_zero a b h := by
    have hv : (Goldilocks.mul a b).val = 0 := congrArg Goldilocks.val h
    rw [Goldilocks.mul_val] at hv
    rcases goldilocksPrime_dvd_mul (Nat.dvd_of_mod_eq_zero hv) with ⟨k, hk⟩ | ⟨k, hk⟩
    · left; apply Goldilocks.ext; have := a.isLt
      by_cases hk0 : k = 0; · subst hk0; simp at hk; exact hk
      have := Nat.mul_le_mul_left goldilocksPrime (show 1 ≤ k by omega); omega
    · right; apply Goldilocks.ext; have := b.isLt
      by_cases hk0 : k = 0; · subst hk0; simp at hk; exact hk
      have := Nat.mul_le_mul_left goldilocksPrime (show 1 ≤ k by omega); omega

def extGcd (m n : Nat) : Int × Int :=
  if _hm : m = 0 then (0, 1)
  else let (u, v) := extGcd (n % m) m; (v - (n / m : Nat) * u, u)
termination_by m
decreasing_by exact Nat.mod_lt n (Nat.pos_of_ne_zero _hm)

theorem extGcd_bezout (m n : Nat) :
    (m : Int) * (extGcd m n).1 + (n : Int) * (extGcd m n).2 = (Nat.gcd m n : Int) := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih =>
    rw [extGcd.eq_def]
    by_cases hm : m = 0; · subst hm; simp [Nat.gcd_zero_left]
    simp only [hm, ↓reduceDIte]
    rw [Nat.gcd_rec m n, ← ih (n % m) (Nat.mod_lt n (Nat.pos_of_ne_zero hm)) m]
    let u := (extGcd (n % m) m).1; let v := (extGcd (n % m) m).2
    change (m : Int) * (v - (n / m : Nat) * u) + (n : Int) * u = ((n % m : Nat) : Int) * u + (m : Int) * v
    have hdivInt : (m : Int) * ((n / m : Nat) : Int) + ((n % m : Nat) : Int) = (n : Int) := by
      exact_mod_cast Nat.div_add_mod n m
    rw [Int.mul_sub, ← Int.mul_assoc, ← hdivInt, Int.add_mul]
    let mqu := (m : Int) * ((n / m : Nat) : Int) * u
    change (m : Int) * v - mqu + (mqu + ((n % m : Nat) : Int) * u) = ((n % m : Nat) : Int) * u + (m : Int) * v
    omega

def Goldilocks.inv (a : Goldilocks) : Goldilocks :=
  if a.val = 0 then Goldilocks.zero
  else Goldilocks.ofNat (Int.toNat ((extGcd a.val goldilocksPrime).1 % (goldilocksPrime : Int)))

theorem Goldilocks.mul_inv_cancel (a : Goldilocks) (hne : a ≠ Goldilocks.zero) :
    Goldilocks.mul a (Goldilocks.inv a) = Goldilocks.one := by
  have ha0 : a.val ≠ 0 := fun hz => hne (Goldilocks.ext hz)
  apply Goldilocks.ext; rw [Goldilocks.mul_val]; unfold Goldilocks.inv
  simp only [ha0, ↓reduceIte, Goldilocks.ofNat, Goldilocks.one]
  let u := (extGcd a.val goldilocksPrime).1; let v := (extGcd a.val goldilocksPrime).2
  have hgcd : Nat.gcd a.val goldilocksPrime = 1 :=
    (goldilocksPrime_isPrime _ (Nat.gcd_dvd_right a.val goldilocksPrime)).resolve_right fun hp =>
      Nat.not_le_of_lt a.isLt (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) (hp ▸ Nat.gcd_dvd_left a.val goldilocksPrime))
  have hbez := extGcd_bezout a.val goldilocksPrime; rw [hgcd] at hbez
  have humodNonneg : 0 ≤ u % (goldilocksPrime : Int) := Int.emod_nonneg u (by decide)
  have humodLt : u % (goldilocksPrime : Int) < (goldilocksPrime : Int) := Int.emod_lt_of_pos u (by decide)
  let rNat := Int.toNat (u % (goldilocksPrime : Int))
  have hrInt : (rNat : Int) = u % (goldilocksPrime : Int) := Int.toNat_of_nonneg humodNonneg
  rw [Nat.mod_eq_of_lt (by omega : rNat < goldilocksPrime)]
  have hdivU := Int.mul_ediv_add_emod u (goldilocksPrime : Int)
  have hprodMod : ((a.val * rNat : Nat) : Int) % (goldilocksPrime : Int) = 1 := by
    rw [Int.natCast_mul, hrInt]
    let k := (a.val : Int) * (u / (goldilocksPrime : Int)) + v
    have hEq1 : (a.val : Int) * (u % (goldilocksPrime : Int)) + (goldilocksPrime : Int) * k = 1 := by
      have h1 : (a.val : Int) * (u % (goldilocksPrime : Int)) +
          (a.val : Int) * ((goldilocksPrime : Int) * (u / (goldilocksPrime : Int))) = (a.val : Int) * u := by
        rw [← Int.mul_add, Int.add_comm (u % _), hdivU]
      calc (a.val : Int) * (u % (goldilocksPrime : Int)) +
             (goldilocksPrime : Int) * ((a.val : Int) * (u / (goldilocksPrime : Int)) + v)
        _ = (a.val : Int) * (u % (goldilocksPrime : Int)) +
            ((a.val : Int) * ((goldilocksPrime : Int) * (u / (goldilocksPrime : Int))) + (goldilocksPrime : Int) * v) := by
          rw [Int.mul_add, ← Int.mul_assoc (goldilocksPrime : Int) (a.val : Int),
              Int.mul_comm (goldilocksPrime : Int) (a.val : Int), Int.mul_assoc]
        _ = (a.val : Int) * u + (goldilocksPrime : Int) * v := by rw [← Int.add_assoc, h1]
        _ = 1 := hbez
    rw [show (a.val : Int) * (u % (goldilocksPrime : Int)) = 1 + (goldilocksPrime : Int) * (-k) by rw [Int.mul_neg]; omega,
        Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by decide) (by decide)
  rw [← Int.natCast_emod] at hprodMod; exact Int.ofNat.inj hprodMod

instance : LawfulField Goldilocks where
  inv := Goldilocks.inv
  inv_zero := by change Goldilocks.inv Goldilocks.zero = Goldilocks.zero; unfold Goldilocks.inv; rfl
  mul_inv_cancel := Goldilocks.mul_inv_cancel

/-! ## 2. `Before` Arithmetization (`beforePolyConstraint_iff_lt`) & `RangeSafe` Guard -/

structure BeforeConstraint where
  lhs : Nat
  rhs : Nat
  bitWidth : Nat
  deriving DecidableEq, Repr

@[expose] def beforeWidthSafe (w : Nat) : Bool := decide (2 * (2 ^ w) ≤ goldilocksPrime)

theorem beforeWidthSafe_implies_pow_lt {w : Nat} (h : beforeWidthSafe w = true) :
    2 ^ w < goldilocksPrime ∧ 2 * (2 ^ w) ≤ goldilocksPrime := by
  simp only [beforeWidthSafe, decide_eq_true_eq] at h; have := Nat.two_pow_pos w; exact ⟨by omega, h⟩

@[expose] def boolBitResidual (bit : Goldilocks) : Goldilocks :=
  CommRingOps.mul bit (CommRingOps.sub bit CommRingOps.one)

theorem boolBitResidual_eq_zero_iff (bit : Goldilocks) :
    boolBitResidual bit = CommRingOps.zero ↔ bit = CommRingOps.zero ∨ bit = CommRingOps.one := by
  unfold boolBitResidual; rw [LawfulIntegralDomain.mul_eq_zero_iff, LawfulIntegralDomain.sub_eq_zero_iff]

def packedBitsGoldilocks : List Goldilocks → Goldilocks
  | [] => CommRingOps.zero
  | b :: bs => CommRingOps.add b (CommRingOps.mul (Goldilocks.ofNat 2) (packedBitsGoldilocks bs))

def packedBitsArray (bits : Array Goldilocks) : Goldilocks :=
  bits.foldr (fun b acc => CommRingOps.add b (CommRingOps.mul (Goldilocks.ofNat 2) acc)) CommRingOps.zero

theorem packedBitsArray_eq_spec (bits : Array Goldilocks) :
    packedBitsArray bits = packedBitsGoldilocks bits.toList := by
  unfold packedBitsArray; rw [← Array.foldr_toList]
  induction bits.toList with | nil => rfl | cons b bs ih => simp only [List.foldr_cons, packedBitsGoldilocks, ih]

def bitsFieldToNat : List Goldilocks → Nat
  | [] => 0
  | b :: bs => b.val + 2 * bitsFieldToNat bs

theorem bitsFieldToNat_lt_two_pow :
    ∀ (bits : List Goldilocks),
      (∀ b ∈ bits, boolBitResidual b = CommRingOps.zero) → bitsFieldToNat bits < 2 ^ bits.length
  | [], _ => by decide
  | b :: bs, hbool => by
    have hb := (boolBitResidual_eq_zero_iff b).mp (hbool b List.mem_cons_self)
    have hbs := bitsFieldToNat_lt_two_pow bs (fun x hx => hbool x (List.mem_cons_of_mem b hx))
    have hbLe : b.val ≤ 1 := by rcases hb with rfl | rfl <;> decide
    simp only [bitsFieldToNat, List.length_cons, Nat.pow_succ]; omega

theorem packedBitsGoldilocks_val_of_bool :
    ∀ (bits : List Goldilocks), 2 ^ bits.length ≤ goldilocksPrime →
      (∀ b ∈ bits, boolBitResidual b = CommRingOps.zero) →
      (packedBitsGoldilocks bits).val = bitsFieldToNat bits
  | [], _, _ => rfl
  | b :: bs, hpow, hbool => by
    simp only [List.length_cons, Nat.pow_succ] at hpow
    have hb := (boolBitResidual_eq_zero_iff b).mp (hbool b List.mem_cons_self)
    have hbsBool : ∀ x ∈ bs, boolBitResidual x = CommRingOps.zero := fun x hx => hbool x (List.mem_cons_of_mem b hx)
    have ih := packedBitsGoldilocks_val_of_bool bs (by omega) hbsBool
    have hbsLt := bitsFieldToNat_lt_two_pow bs hbsBool
    have hbLe : b.val ≤ 1 := by rcases hb with rfl | rfl <;> decide
    simp only [packedBitsGoldilocks, bitsFieldToNat]
    change (Goldilocks.add b (Goldilocks.mul (Goldilocks.ofNat 2) (packedBitsGoldilocks bs))).val = _
    rw [Goldilocks.add_val, Goldilocks.mul_val, ih, show (Goldilocks.ofNat 2).val = 2 by decide,
        Nat.mod_eq_of_lt (by omega : 2 * bitsFieldToNat bs < goldilocksPrime), Nat.mod_eq_of_lt (by omega)]

def beforeSlackResidual (a b : Nat) (bits : List Goldilocks) : Goldilocks :=
  CommRingOps.sub (CommRingOps.sub (CommRingOps.sub (Goldilocks.ofNat b) (Goldilocks.ofNat a)) CommRingOps.one)
    (packedBitsGoldilocks bits)

def beforeSlackResidualArray (a b : Nat) (bits : Array Goldilocks) : Goldilocks :=
  CommRingOps.sub (CommRingOps.sub (CommRingOps.sub (Goldilocks.ofNat b) (Goldilocks.ofNat a)) CommRingOps.one)
    (packedBitsArray bits)

theorem beforeSlackResidualArray_eq_spec (a b : Nat) (bits : Array Goldilocks) :
    beforeSlackResidualArray a b bits = beforeSlackResidual a b bits.toList := by
  simp [beforeSlackResidualArray, beforeSlackResidual, packedBitsArray_eq_spec]

def checkBeforePolySpec (c : BeforeConstraint) (bits : List Goldilocks) : Bool :=
  beforeWidthSafe c.bitWidth && decide (c.lhs < 2 ^ c.bitWidth) &&
  decide (c.rhs ≤ 2 ^ c.bitWidth) && decide (bits.length = c.bitWidth) &&
  bits.all (fun b => decide (boolBitResidual b = CommRingOps.zero)) &&
  decide (beforeSlackResidual c.lhs c.rhs bits = CommRingOps.zero)

def checkBeforePolyArray (c : BeforeConstraint) (bits : Array Goldilocks) : Bool :=
  beforeWidthSafe c.bitWidth && decide (c.lhs < 2 ^ c.bitWidth) &&
  decide (c.rhs ≤ 2 ^ c.bitWidth) && decide (bits.size = c.bitWidth) &&
  bits.all (fun b => decide (boolBitResidual b = CommRingOps.zero)) &&
  decide (beforeSlackResidualArray c.lhs c.rhs bits = CommRingOps.zero)

theorem checkBeforePolyArray_eq_spec (c : BeforeConstraint) (bits : Array Goldilocks) :
    checkBeforePolyArray c bits = checkBeforePolySpec c bits.toList := by
  simp [checkBeforePolyArray, checkBeforePolySpec, beforeSlackResidualArray_eq_spec, Array.all_toList]

def compileBeforeBits : Nat → Nat → List Goldilocks
  | 0, _ => []
  | w + 1, s => (if s % 2 = 1 then CommRingOps.one else CommRingOps.zero) :: compileBeforeBits w (s / 2)

def compileBeforeWitness (c : BeforeConstraint) : Array Goldilocks :=
  (compileBeforeBits c.bitWidth (c.rhs - c.lhs - 1)).toArray

theorem compileBeforeBits_spec :
    ∀ (w s : Nat), s < 2 ^ w →
      (compileBeforeBits w s).length = w ∧
      (∀ b ∈ compileBeforeBits w s, boolBitResidual b = CommRingOps.zero) ∧
      bitsFieldToNat (compileBeforeBits w s) = s
  | 0, s, hs => by
    have hs0 : s = 0 := by simp at hs; exact hs
    subst hs0; simp [compileBeforeBits, bitsFieldToNat]
  | w + 1, s, hs => by
    simp only [Nat.pow_succ] at hs
    obtain ⟨hlen, hbool, hval⟩ := compileBeforeBits_spec w (s / 2) (by omega)
    refine ⟨by simp [compileBeforeBits, hlen], ?_, ?_⟩
    · intro b hb; rcases List.mem_cons.mp hb with rfl | htail
      · split <;> decide
      · exact hbool b htail
    · simp only [compileBeforeBits, bitsFieldToNat, hval]
      by_cases hm : s % 2 = 1
      · simp only [hm, ↓reduceIte, show (CommRingOps.one : Goldilocks).val = 1 by decide]; omega
      · simp only [hm, ↓reduceIte, show (CommRingOps.zero : Goldilocks).val = 0 by decide]; omega

theorem compileBeforeWitness_size (c : BeforeConstraint) (hs : c.rhs - c.lhs - 1 < 2 ^ c.bitWidth) :
    (compileBeforeWitness c).size = c.bitWidth := by
  simpa [compileBeforeWitness] using (compileBeforeBits_spec c.bitWidth (c.rhs - c.lhs - 1) hs).1

theorem goldilocks_ofNat_add (x y : Nat) :
    Goldilocks.ofNat (x + y) = CommRingOps.add (Goldilocks.ofNat x) (Goldilocks.ofNat y) := by
  apply Goldilocks.ext
  change (x + y) % goldilocksPrime = (Goldilocks.add (Goldilocks.ofNat x) (Goldilocks.ofNat y)).val
  rw [Goldilocks.add_val]; simp [Goldilocks.ofNat, Nat.add_mod]

private theorem compileBeforeBits_slack_zero {a b w s : Nat}
    (hPow : 2 ^ w ≤ goldilocksPrime) (hsLt : s < 2 ^ w)
    (hbEq : Goldilocks.ofNat b = Goldilocks.ofNat (a + 1 + s)) :
    beforeSlackResidual a b (compileBeforeBits w s) = CommRingOps.zero := by
  obtain ⟨hlen, hbool, hval⟩ := compileBeforeBits_spec w s hsLt
  have hpackEq : packedBitsGoldilocks (compileBeforeBits w s) = Goldilocks.ofNat s := by
    apply Goldilocks.ext; rw [packedBitsGoldilocks_val_of_bool _ (by rw [hlen]; exact hPow) hbool, hval]
    simp only [Goldilocks.ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm
  unfold beforeSlackResidual
  have hOneEq : (CommRingOps.one : Goldilocks) = Goldilocks.ofNat 1 := by apply Goldilocks.ext; decide
  rw [hpackEq, hbEq, goldilocks_ofNat_add (a + 1) s, goldilocks_ofNat_add a 1, ← hOneEq]
  have hc1 : CommRingOps.sub
      (CommRingOps.add (CommRingOps.add (Goldilocks.ofNat a) CommRingOps.one) (Goldilocks.ofNat s))
      (Goldilocks.ofNat a) = CommRingOps.add CommRingOps.one (Goldilocks.ofNat s) := by
    apply LawfulCommRing.add_left_cancel (a := Goldilocks.ofNat a)
    rw [LawfulCommRing.add_sub_cancel_left, LawfulCommRing.add_assoc]
  have hc2 : CommRingOps.sub (CommRingOps.add CommRingOps.one (Goldilocks.ofNat s)) CommRingOps.one =
      Goldilocks.ofNat s := by
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.one); rw [LawfulCommRing.add_sub_cancel_left]
  rw [hc1, hc2, LawfulCommRing.sub_self]

/-- **Main `Before` Arithmetization Equivalence (`beforePolyConstraint_iff_lt`)**. -/
theorem beforePolyConstraint_iff_lt (a b w : Nat)
    (hWidth : beforeWidthSafe w = true) (ha : a < 2 ^ w) (hb : b ≤ 2 ^ w) :
    (∃ bits : Array Goldilocks,
      bits.size = w ∧
      (∀ bit ∈ bits.toList, boolBitResidual bit = CommRingOps.zero) ∧
      beforeSlackResidualArray a b bits = CommRingOps.zero) ↔ a < b := by
  obtain ⟨_, hTwoPowLe⟩ := beforeWidthSafe_implies_pow_lt hWidth
  constructor
  · rintro ⟨bits, hsz, hbool, hslack⟩
    rw [beforeSlackResidualArray_eq_spec] at hslack
    have hlen : bits.toList.length = w := by simpa using hsz
    have hsLt : bitsFieldToNat bits.toList < 2 ^ w := by rw [← hlen]; exact bitsFieldToNat_lt_two_pow _ hbool
    have hpackVal := packedBitsGoldilocks_val_of_bool bits.toList (by rw [hlen]; omega) hbool
    have hEq2 : CommRingOps.sub (Goldilocks.ofNat b) (Goldilocks.ofNat a) =
        CommRingOps.add CommRingOps.one (packedBitsGoldilocks bits.toList) := by
      have h := congrArg (CommRingOps.add CommRingOps.one) (eq_of_sub_eq_zero hslack)
      rwa [LawfulCommRing.add_sub_cancel_left] at h
    have hEq3 : Goldilocks.ofNat b =
        CommRingOps.add (Goldilocks.ofNat a) (CommRingOps.add CommRingOps.one (packedBitsGoldilocks bits.toList)) := by
      have h := congrArg (CommRingOps.add (Goldilocks.ofNat a)) hEq2
      rwa [LawfulCommRing.add_sub_cancel_left] at h
    have hPackedEqOfNat : packedBitsGoldilocks bits.toList = Goldilocks.ofNat (bitsFieldToNat bits.toList) := by
      apply Goldilocks.ext; rw [hpackVal]; simp only [Goldilocks.ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm
    have hOneEq : (CommRingOps.one : Goldilocks) = Goldilocks.ofNat 1 := by apply Goldilocks.ext; decide
    rw [hPackedEqOfNat, hOneEq, ← goldilocks_ofNat_add, ← goldilocks_ofNat_add] at hEq3
    have hValEq : b % goldilocksPrime = (a + (1 + bitsFieldToNat bits.toList)) % goldilocksPrime :=
      congrArg Goldilocks.val hEq3
    rw [Nat.mod_eq_of_lt (by omega : b < goldilocksPrime),
        Nat.mod_eq_of_lt (by omega : a + (1 + bitsFieldToNat bits.toList) < goldilocksPrime)] at hValEq
    omega
  · intro hlt
    let s := b - a - 1
    have hsLt : s < 2 ^ w := by omega
    obtain ⟨hlen, hbool, _⟩ := compileBeforeBits_spec w s hsLt
    refine ⟨(compileBeforeBits w s).toArray, by simpa using hlen, by simpa using hbool, ?_⟩
    rw [beforeSlackResidualArray_eq_spec]
    exact compileBeforeBits_slack_zero (by omega) hsLt (by congr 1; omega)

theorem checkBeforePolyArray_complete (c : BeforeConstraint)
    (hWidth : beforeWidthSafe c.bitWidth = true)
    (ha : c.lhs < 2 ^ c.bitWidth) (hb : c.rhs ≤ 2 ^ c.bitWidth) (hlt : c.lhs < c.rhs) :
    checkBeforePolyArray c (compileBeforeWitness c) = true := by
  obtain ⟨_, hTwoPowLe⟩ := beforeWidthSafe_implies_pow_lt hWidth
  let s := c.rhs - c.lhs - 1
  have hsLt : s < 2 ^ c.bitWidth := by omega
  obtain ⟨hlen, hbool, _⟩ := compileBeforeBits_spec c.bitWidth s hsLt
  rw [checkBeforePolyArray_eq_spec]; unfold compileBeforeWitness checkBeforePolySpec
  have htoL : (compileBeforeBits c.bitWidth s).toArray.toList = compileBeforeBits c.bitWidth s := rfl
  rw [htoL]
  have hall := List.all_eq_true.mpr fun b hm => decide_eq_true (hbool b hm)
  have hslack := compileBeforeBits_slack_zero (a := c.lhs) (b := c.rhs) (by omega) hsLt (by congr 1; omega)
  simp [hWidth, ha, hb, hlen, hall, hslack]

theorem checkBeforePolyArray_sound {c : BeforeConstraint} {bits : Array Goldilocks}
    (h : checkBeforePolyArray c bits = true) : c.lhs < c.rhs := by
  rw [checkBeforePolyArray_eq_spec] at h
  simp only [checkBeforePolySpec, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨hW, ha⟩, hb⟩, hlen⟩, hall⟩, hslack⟩
  exact (beforePolyConstraint_iff_lt c.lhs c.rhs c.bitWidth hW ha hb).mp
    ⟨bits, by simpa using hlen, hall, by rw [beforeSlackResidualArray_eq_spec]; exact hslack⟩

theorem compileBeforeWitness_residuals_zero (c : BeforeConstraint)
    (hWidth : beforeWidthSafe c.bitWidth = true)
    (ha : c.lhs < 2 ^ c.bitWidth) (hb : c.rhs ≤ 2 ^ c.bitWidth) (hlt : c.lhs < c.rhs) :
    (compileBeforeWitness c).size = c.bitWidth ∧
    (∀ b ∈ (compileBeforeWitness c).toList, boolBitResidual b = CommRingOps.zero) ∧
    beforeSlackResidualArray c.lhs c.rhs (compileBeforeWitness c) = CommRingOps.zero := by
  have h := checkBeforePolyArray_complete c hWidth ha hb hlt
  rw [checkBeforePolyArray_eq_spec] at h
  simp only [checkBeforePolySpec, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  rcases h with ⟨⟨⟨_, hlen⟩, hall⟩, hslack⟩
  exact ⟨by simpa using hlen, hall, by rw [beforeSlackResidualArray_eq_spec]; exact hslack⟩

example : checkBeforePolyArray ⟨3, 10, 32⟩ (compileBeforeWitness ⟨3, 10, 32⟩) = true :=
  checkBeforePolyArray_complete ⟨3, 10, 32⟩ (by decide) (by decide) (by decide) (by decide)

/-- **Mod-$p$ Wraparound Refutation Theorem (`beforeWraparound_at_63bits`)**. -/
theorem beforeWraparound_at_63bits (a : Nat)
    (hLo : goldilocksPrime - 2 ^ 63 ≤ a) (hHi : a < 2 ^ 63) :
    2 ^ 63 < goldilocksPrime ∧ beforeWidthSafe 63 = false ∧ ¬ (a < 0) ∧
    let forgedBits := (compileBeforeBits 63 (goldilocksPrime - a - 1)).toArray
    forgedBits.size = 63 ∧
    (∀ bit ∈ forgedBits.toList, boolBitResidual bit = CommRingOps.zero) ∧
    beforeSlackResidualArray a 0 forgedBits = CommRingOps.zero := by
  have hp63 : 2 ^ 63 < goldilocksPrime := by decide
  refine ⟨hp63, by decide, by omega, ?_⟩; dsimp only
  let s := goldilocksPrime - a - 1
  have hsLt : s < 2 ^ 63 := by omega
  obtain ⟨hlen, hbool, _⟩ := compileBeforeBits_spec 63 s hsLt
  refine ⟨by simpa using hlen, by simpa using hbool, ?_⟩
  rw [beforeSlackResidualArray_eq_spec]
  apply compileBeforeBits_slack_zero (by omega) hsLt
  apply Goldilocks.ext; have hsum : a + 1 + s = goldilocksPrime := by omega
  simp [Goldilocks.ofNat, hsum]

/-! ## 3. Univariate Polynomial Factoring, Schwartz–Zippel & `LinMem` Multiset Weld -/

theorem exists_ne_zero_of_all_false {R : Type} [CommRingOps R] [DecidableEq R] :
    ∀ (l : List R), l.all (fun c => decide (c = CommRingOps.zero)) = false → ∃ c ∈ l, c ≠ CommRingOps.zero
  | [], h => by simp at h
  | x :: xs, h => by
    simp only [List.all_cons, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    rcases h with hne | hrest
    · exact ⟨x, List.mem_cons_self, hne⟩
    · obtain ⟨c, hc, hne⟩ := exists_ne_zero_of_all_false xs hrest
      exact ⟨c, List.mem_cons_of_mem x hc, hne⟩

private theorem sub_sub_cancel_add {R : Type} [LawfulCommRing R] (x y z : R) :
    CommRingOps.sub x (CommRingOps.sub y z) = CommRingOps.add (CommRingOps.sub x y) z := by
  apply LawfulCommRing.add_left_cancel (a := CommRingOps.sub y z)
  rw [LawfulCommRing.add_sub_cancel_left]
  have hz : CommRingOps.add (CommRingOps.sub y z) z = y := by
    rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]
  rw [← LawfulCommRing.add_assoc (CommRingOps.sub y z) (CommRingOps.sub x y) z,
      LawfulCommRing.add_comm (CommRingOps.sub y z) (CommRingOps.sub x y),
      LawfulCommRing.add_assoc, hz, LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

private theorem sub_right_comm {R : Type} [LawfulCommRing R] (x y z : R) :
    CommRingOps.sub (CommRingOps.sub x y) z = CommRingOps.sub (CommRingOps.sub x z) y := by
  rw [LawfulCommRing.sub_eq_add_neg (CommRingOps.sub x y) z, LawfulCommRing.sub_eq_add_neg x y,
      LawfulCommRing.add_assoc, LawfulCommRing.add_comm (CommRingOps.neg y) (CommRingOps.neg z),
      ← LawfulCommRing.add_assoc, ← LawfulCommRing.sub_eq_add_neg, ← LawfulCommRing.sub_eq_add_neg]

def mulLinFactorAux {R : Type} [CommRingOps R] (prev a : R) : List R → List R
  | [] => [prev]
  | c :: cs => CommRingOps.sub prev (CommRingOps.mul a c) :: mulLinFactorAux c a cs

def mulLinFactor {R : Type} [CommRingOps R] (a : R) (p : RoundPoly R) : RoundPoly R :=
  ⟨mulLinFactorAux CommRingOps.zero a p.coeffs⟩

theorem mulLinFactorAux_length {R : Type} [CommRingOps R] (prev a : R) :
    ∀ cs : List R, (mulLinFactorAux prev a cs).length = cs.length + 1
  | [] => rfl
  | _ :: cs => by simp [mulLinFactorAux, mulLinFactorAux_length _ a cs]

theorem mulLinFactor_length {R : Type} [CommRingOps R] (a : R) (p : RoundPoly R) :
    (mulLinFactor a p).coeffs.length = p.coeffs.length + 1 :=
  mulLinFactorAux_length CommRingOps.zero a p.coeffs

theorem evalCoeffs_mulLinFactorAux {R : Type} [LawfulCommRing R] (a x : R) :
    ∀ (cs : List R) (prev : R),
      RoundPoly.evalCoeffs (mulLinFactorAux prev a cs) x =
        CommRingOps.add prev (CommRingOps.mul (CommRingOps.sub x a) (RoundPoly.evalCoeffs cs x))
  | [], prev => by simp [mulLinFactorAux, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | c :: cs, prev => by
    simp only [mulLinFactorAux, RoundPoly.evalCoeffs, evalCoeffs_mulLinFactorAux a x cs c]
    rw [LawfulCommRing.left_distrib, ← LawfulCommRing.add_assoc]
    have hhead : CommRingOps.add (CommRingOps.sub prev (CommRingOps.mul a c)) (CommRingOps.mul x c) =
        CommRingOps.add prev (CommRingOps.mul (CommRingOps.sub x a) c) := by
      rw [LawfulCommRing.sub_mul, LawfulCommRing.sub_eq_add_neg prev _,
          LawfulCommRing.add_assoc, LawfulCommRing.add_comm (CommRingOps.neg (CommRingOps.mul a c)),
          ← LawfulCommRing.sub_eq_add_neg]
    have htail : CommRingOps.mul x (CommRingOps.mul (CommRingOps.sub x a) (RoundPoly.evalCoeffs cs x)) =
        CommRingOps.mul (CommRingOps.sub x a) (CommRingOps.mul x (RoundPoly.evalCoeffs cs x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x (CommRingOps.sub x a), LawfulCommRing.mul_assoc]
    rw [hhead, htail, LawfulCommRing.add_assoc, ← LawfulCommRing.left_distrib]

theorem eval_mulLinFactor {R : Type} [LawfulCommRing R] (a : R) (p : RoundPoly R) (x : R) :
    (mulLinFactor a p).eval x = CommRingOps.mul (CommRingOps.sub x a) (p.eval x) := by
  unfold mulLinFactor RoundPoly.eval; rw [evalCoeffs_mulLinFactorAux, LawfulCommRing.zero_add]

theorem mulLinFactorAux_inj_of_len {R : Type} [LawfulCommRing R] (a : R) :
    ∀ {cs₁ cs₂ : List R} {prev₁ prev₂ : R},
      cs₁.length = cs₂.length →
      mulLinFactorAux prev₁ a cs₁ = mulLinFactorAux prev₂ a cs₂ → prev₁ = prev₂ ∧ cs₁ = cs₂
  | [], [], _, _, _, h => by simp only [mulLinFactorAux, List.cons.injEq] at h; exact ⟨h.1, rfl⟩
  | c₁ :: cs₁, c₂ :: cs₂, _, _, hlen, h => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    simp only [mulLinFactorAux, List.cons.injEq] at h
    obtain ⟨hc, hcs⟩ := mulLinFactorAux_inj_of_len a hlen h.2; subst hc hcs
    have h1 := congrArg (fun z => CommRingOps.add z (CommRingOps.mul a c₁)) h.1
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc, LawfulCommRing.add_left_neg,
        LawfulCommRing.add_zero, LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_left_neg, LawfulCommRing.add_zero] at h1
    exact ⟨h1, rfl⟩

theorem mulLinFactor_injective {R : Type} [LawfulCommRing R] (a : R) {p q : RoundPoly R}
    (h : mulLinFactor a p = mulLinFactor a q) : p = q := by
  have hc : mulLinFactorAux CommRingOps.zero a p.coeffs = mulLinFactorAux CommRingOps.zero a q.coeffs :=
    congrArg RoundPoly.coeffs h
  have hlenEq := congrArg List.length hc
  rw [mulLinFactorAux_length, mulLinFactorAux_length] at hlenEq
  obtain ⟨_, hcs⟩ := mulLinFactorAux_inj_of_len a (Nat.succ.inj hlenEq) hc
  cases p; cases q; simp only at hcs; subst hcs; rfl

private theorem mulLinFactorAux_comm_gen {R : Type} [LawfulCommRing R] (a b : R) :
    ∀ (cs : List R) (prev pA pB : R),
      CommRingOps.sub pA (CommRingOps.mul a prev) = CommRingOps.sub pB (CommRingOps.mul b prev) →
      mulLinFactorAux pA a (mulLinFactorAux prev b cs) = mulLinFactorAux pB b (mulLinFactorAux prev a cs)
  | [], _, _, _, hInv => by simp only [mulLinFactorAux, List.cons.injEq, and_true]; exact hInv
  | c :: cs, prev, pA, pB, hInv => by
    simp only [mulLinFactorAux, List.cons.injEq]
    refine ⟨?_, mulLinFactorAux_comm_gen a b cs c
      (CommRingOps.sub prev (CommRingOps.mul b c)) (CommRingOps.sub prev (CommRingOps.mul a c))
      (sub_right_comm prev (CommRingOps.mul b c) (CommRingOps.mul a c))⟩
    rw [LawfulCommRing.mul_sub, LawfulCommRing.mul_sub, sub_sub_cancel_add, sub_sub_cancel_add,
        hInv, ← LawfulCommRing.mul_assoc a b c, LawfulCommRing.mul_comm a b, LawfulCommRing.mul_assoc]

theorem mulLinFactor_comm {R : Type} [LawfulCommRing R] (a b : R) (p : RoundPoly R) :
    mulLinFactor a (mulLinFactor b p) = mulLinFactor b (mulLinFactor a p) := by
  unfold mulLinFactor; congr 1; apply mulLinFactorAux_comm_gen
  rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero]

def divByLinearAux {R : Type} [CommRingOps R] (r c : R) : List R → List R × R
  | [] => ([], c)
  | c' :: cs => let (q, rem) := divByLinearAux r c' cs; (rem :: q, CommRingOps.add c (CommRingOps.mul r rem))

theorem divByLinearAux_len {R : Type} [CommRingOps R] (r : R) :
    ∀ (c : R) (cs : List R), (divByLinearAux r c cs).1.length = cs.length
  | _, [] => rfl
  | _, c' :: cs => by simp [divByLinearAux, divByLinearAux_len r c' cs]

theorem divByLinearAux_rem {R : Type} [LawfulCommRing R] (r : R) :
    ∀ (c : R) (cs : List R), (divByLinearAux r c cs).2 = RoundPoly.evalCoeffs (c :: cs) r
  | _, [] => by simp [divByLinearAux, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | _, c' :: cs => by simp [divByLinearAux, RoundPoly.evalCoeffs, divByLinearAux_rem r c' cs]

theorem divByLinearAux_spec {R : Type} [LawfulCommRing R] (r : R) :
    ∀ (c : R) (cs : List R), mulLinFactorAux (divByLinearAux r c cs).2 r (divByLinearAux r c cs).1 = c :: cs
  | _, [] => rfl
  | c, c' :: cs => by
    simp only [divByLinearAux, mulLinFactorAux, divByLinearAux_spec r c' cs, List.cons.injEq, and_true]
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul r (divByLinearAux r c' cs).2)
    rw [LawfulCommRing.add_sub_cancel_left, LawfulCommRing.add_comm]

theorem evalCoeffs_eq_zero_of_all_zero {R : Type} [LawfulCommRing R] (x : R) :
    ∀ (cs : List R), (∀ c ∈ cs, c = CommRingOps.zero) → RoundPoly.evalCoeffs cs x = CommRingOps.zero
  | [], _ => rfl
  | c :: cs, hz => by
    simp only [RoundPoly.evalCoeffs, hz c List.mem_cons_self,
      evalCoeffs_eq_zero_of_all_zero x cs (fun y hy => hz y (List.mem_cons_of_mem c hy)),
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem mulLinFactorAux_all_zero {R : Type} [LawfulCommRing R] (a : R) :
    ∀ (cs : List R) (prev : R),
      prev = CommRingOps.zero → (∀ c ∈ cs, c = CommRingOps.zero) →
      ∀ z ∈ mulLinFactorAux prev a cs, z = CommRingOps.zero
  | [], _, hp, _, z, hz => by simp [mulLinFactorAux, hp] at hz; exact hz
  | c :: cs, _, hp, hcs, z, hz => by
    have hc0 : c = CommRingOps.zero := hcs c List.mem_cons_self
    rcases List.mem_cons.mp hz with rfl | htail
    · rw [hp, hc0, LawfulCommRing.mul_zero, LawfulCommRing.sub_self]
    · exact mulLinFactorAux_all_zero a cs c hc0 (fun y hy => hcs y (List.mem_cons_of_mem c hy)) z htail

theorem nodup_filter {α : Type} (p : α → Bool) : ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.Pairwise.nil
  | _ :: xs, hnd => by
    rw [List.nodup_cons] at hnd; simp only [List.filter_cons]; split
    · rw [List.nodup_cons]; exact ⟨fun hm => hnd.1 (List.mem_filter.mp hm).1, nodup_filter p hnd.2⟩
    · exact nodup_filter p hnd.2

/-- **Constructive Univariate Schwartz–Zippel Root Bound (`schwartzZippel_roots_le_deg`)**. -/
theorem schwartzZippel_roots_le_deg {R : Type} [LawfulIntegralDomain R] [DecidableEq R] :
    ∀ (d : Nat) (p : RoundPoly R) (S : List R),
      S.Nodup → p.coeffs.length ≤ d + 1 → (∃ c ∈ p.coeffs, c ≠ CommRingOps.zero) →
      (S.filter fun r => decide (p.eval r = CommRingOps.zero)).length ≤ d
  | 0, ⟨cs⟩, S, _, hlen, ⟨c, hcMem, hcNe⟩ => by
    cases cs with
    | nil => cases hcMem
    | cons _ tl =>
      cases tl with
      | cons _ _ => simp at hlen
      | nil =>
        simp only [List.mem_singleton] at hcMem; subst hcMem
        have hnone : S.filter (fun r => decide ((⟨[c]⟩ : RoundPoly R).eval r = CommRingOps.zero)) = [] := by
          rw [List.filter_eq_nil_iff]; intro r _
          simp [RoundPoly.eval, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero, hcNe]
        rw [hnone]; exact Nat.zero_le _
  | d + 1, ⟨cs⟩, S, hnd, hlen, hnz => by
    let pred : R → Bool := fun r => decide ((⟨cs⟩ : RoundPoly R).eval r = CommRingOps.zero)
    cases hroots : S.filter pred with
    | nil => exact Nat.zero_le _
    | cons r₀ restRoots =>
      have hr₀Mem : r₀ ∈ S.filter pred := by rw [hroots]; exact List.mem_cons_self
      have hr₀Eval : (⟨cs⟩ : RoundPoly R).eval r₀ = CommRingOps.zero := of_decide_eq_true (List.mem_filter.mp hr₀Mem).2
      cases cs with
      | nil => rcases hnz with ⟨_, hm, _⟩; cases hm
      | cons c₀ csTail =>
        simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
        let q : RoundPoly R := ⟨(divByLinearAux r₀ c₀ csTail).1⟩
        have hfCoeffs : mulLinFactorAux CommRingOps.zero r₀ q.coeffs = c₀ :: csTail := by
          change mulLinFactorAux CommRingOps.zero r₀ (divByLinearAux r₀ c₀ csTail).1 = c₀ :: csTail
          rw [← (show (divByLinearAux r₀ c₀ csTail).2 = CommRingOps.zero by rw [divByLinearAux_rem]; exact hr₀Eval)]
          exact divByLinearAux_spec r₀ c₀ csTail
        have hFactor : mulLinFactor r₀ q = ⟨c₀ :: csTail⟩ := congrArg RoundPoly.mk hfCoeffs
        have hqLen : q.coeffs.length ≤ d + 1 := by unfold q; rw [divByLinearAux_len]; exact hlen
        have hqNz : ∃ c' ∈ q.coeffs, c' ≠ CommRingOps.zero := by
          cases hqb : q.coeffs.all (fun y => decide (y = CommRingOps.zero)) with
          | false => exact exists_ne_zero_of_all_false q.coeffs hqb
          | true =>
            exfalso; rcases hnz with ⟨c, hcMem, hcNe⟩
            have hcAll := mulLinFactorAux_all_zero r₀ q.coeffs CommRingOps.zero rfl
              (fun y hy => of_decide_eq_true (List.all_eq_true.mp hqb y hy))
            rw [hfCoeffs] at hcAll; exact hcNe (hcAll c hcMem)
        have hRootsNd : (r₀ :: restRoots).Nodup := hroots ▸ nodup_filter pred hnd
        rw [List.nodup_cons] at hRootsNd
        have hSub : ∀ r ∈ restRoots, r ∈ (S.erase r₀).filter (fun x => decide (q.eval x = CommRingOps.zero)) := by
          intro r hr
          have hrInFilter : r ∈ S.filter pred := by rw [hroots]; exact List.mem_cons_of_mem r₀ hr
          rw [List.mem_filter] at hrInFilter ⊢
          have hrNe : r ≠ r₀ := fun heq => hRootsNd.1 (heq ▸ hr)
          refine ⟨(List.mem_erase_of_ne hrNe).mpr hrInFilter.1, decide_eq_true ?_⟩
          have h0 : (mulLinFactor r₀ q).eval r = CommRingOps.zero := by rw [hFactor]; exact of_decide_eq_true hrInFilter.2
          rw [eval_mulLinFactor] at h0
          exact (LawfulIntegralDomain.mul_eq_zero _ _ h0).resolve_left
            fun hsub0 => hrNe ((LawfulIntegralDomain.sub_eq_zero_iff r r₀).mp hsub0)
        have hRestLe := nodup_sublist_len_le restRoots _ hRootsNd.2 hSub
        have ih := schwartzZippel_roots_le_deg d q (S.erase r₀) (hnd.erase r₀) hqLen hqNz
        simp only [List.length_cons]; omega

def allGoldilocksElems : List Goldilocks := (List.range goldilocksPrime).map Goldilocks.ofNat
private theorem allGoldilocksElems_length : allGoldilocksElems.length = goldilocksPrime := by simp [allGoldilocksElems]
theorem mem_allGoldilocksElems (x : Goldilocks) : x ∈ allGoldilocksElems :=
  List.mem_map.mpr ⟨x.val, List.mem_range.mpr x.isLt, Goldilocks.ext (Nat.mod_eq_of_lt x.isLt)⟩

private theorem allGoldilocksElems_nodup : allGoldilocksElems.Nodup := by
  apply nodup_map_of_lt_inj Goldilocks.ofNat (List.range goldilocksPrime) (pairwise_lt_range _)
  intro i hi j hj hij hEq; have hv := congrArg Goldilocks.val hEq
  simp only [Goldilocks.ofNat, Nat.mod_eq_of_lt (List.mem_range.mp hi),
    Nat.mod_eq_of_lt (List.mem_range.mp hj)] at hv; omega

private theorem filter_neg_add_filter_len {α : Type} (q : α → Bool) :
    ∀ l : List α, (l.filter (fun x => !q x)).length + (l.filter q).length = l.length
  | [] => rfl
  | a :: as => by
    have ih := filter_neg_add_filter_len q as; simp only [List.filter_cons]
    cases q a <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

theorem goldilocks_all_coeffs_zero_of_eval_zero_except {p : RoundPoly Goldilocks}
    (S_excl : List Goldilocks) (hBound : p.coeffs.length + S_excl.length ≤ goldilocksPrime)
    (hZero : ∀ x : Goldilocks, x ∉ S_excl → p.eval x = CommRingOps.zero) :
    ∀ c ∈ p.coeffs, c = CommRingOps.zero := by
  intro c hc; exact Decidable.byContradiction fun hcNe => by
    let pool := allGoldilocksElems.filter (fun x => !decide (x ∈ S_excl))
    have hAllRoots : pool.filter (fun r => decide (p.eval r = CommRingOps.zero)) = pool := by
      rw [List.filter_eq_self]; intro r hr; exact decide_eq_true (hZero r (by simpa using (List.mem_filter.mp hr).2))
    have hpPos : 0 < p.coeffs.length := List.length_pos_of_mem hc
    have hSz := schwartzZippel_roots_le_deg (p.coeffs.length - 1) p pool
      (nodup_filter _ allGoldilocksElems_nodup) (by omega) ⟨c, hc, hcNe⟩
    rw [hAllRoots] at hSz
    let inExcl := allGoldilocksElems.filter (fun x => decide (x ∈ S_excl))
    have hInExclLe := nodup_sublist_len_le inExcl S_excl (nodup_filter _ allGoldilocksElems_nodup)
      (fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2)
    have hPartLen := filter_neg_add_filter_len (fun x => decide (x ∈ S_excl)) allGoldilocksElems
    rw [allGoldilocksElems_length] at hPartLen
    change pool.length + inExcl.length = goldilocksPrime at hPartLen; omega

def charPoly {R : Type} [CommRingOps R] : List R → RoundPoly R
  | [] => ⟨[CommRingOps.one]⟩
  | a :: as => mulLinFactor a (charPoly as)

@[simp] theorem charPoly_nil (R : Type) [CommRingOps R] : charPoly ([] : List R) = ⟨[CommRingOps.one]⟩ := by rfl
@[simp] theorem charPoly_cons {R : Type} [CommRingOps R] (a : R) (as : List R) :
    charPoly (a :: as) = mulLinFactor a (charPoly as) := by rfl

def charPolyArray {R : Type} [CommRingOps R] (arr : Array R) : RoundPoly R :=
  arr.foldr mulLinFactor ⟨[CommRingOps.one]⟩

theorem charPolyArray_eq_spec {R : Type} [CommRingOps R] (arr : Array R) :
    charPolyArray arr = charPoly arr.toList := by
  unfold charPolyArray; rw [← Array.foldr_toList]
  induction arr.toList with | nil => rfl | cons a as ih => simp only [List.foldr_cons, charPoly, ih]

def charPolyEvalArray {R : Type} [CommRingOps R] (arr : Array R) (γ : R) : R :=
  arr.foldr (fun a acc => CommRingOps.mul (CommRingOps.sub γ a) acc) CommRingOps.one

theorem charPolyEvalArray_eq_spec {R : Type} [LawfulCommRing R] (arr : Array R) (γ : R) :
    charPolyEvalArray arr γ = (charPoly arr.toList).eval γ := by
  unfold charPolyEvalArray; rw [← Array.foldr_toList]
  induction arr.toList with
  | nil => simp [charPoly, RoundPoly.eval, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | cons a as ih => simp only [List.foldr_cons, charPoly, eval_mulLinFactor, ih]

theorem charPoly_length {R : Type} [CommRingOps R] :
    ∀ as : List R, (charPoly as).coeffs.length = as.length + 1
  | [] => rfl
  | _ :: as => by simp [charPoly, mulLinFactor, mulLinFactorAux_length, charPoly_length as]

theorem charPoly_eval_eq_zero_iff {R : Type} [LawfulIntegralDomain R] (x : R) :
    ∀ as : List R, (charPoly as).eval x = CommRingOps.zero ↔ x ∈ as
  | [] => by simp [charPoly, RoundPoly.eval, RoundPoly.evalCoeffs,
                   LawfulCommRing.mul_zero, LawfulCommRing.add_zero, Ne.symm LawfulIntegralDomain.zero_ne_one]
  | a :: as => by rw [charPoly, eval_mulLinFactor, LawfulIntegralDomain.mul_eq_zero_iff,
                      LawfulIntegralDomain.sub_eq_zero_iff, charPoly_eval_eq_zero_iff x as, List.mem_cons]

theorem charPoly_perm {R : Type} [LawfulCommRing R] {as bs : List R} (h : as.Perm bs) :
    charPoly as = charPoly bs := by
  induction h with
  | nil => rfl
  | cons x _ ih => exact congrArg (mulLinFactor x) ih
  | swap x y l => exact mulLinFactor_comm y x (charPoly l)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Exact Algebraic Multiset Equivalence (`charPoly_eq_iff_perm`)**. -/
theorem charPoly_eq_iff_perm {R : Type} [LawfulIntegralDomain R] [DecidableEq R] :
    ∀ (as bs : List R), charPoly as = charPoly bs ↔ as.Perm bs
  | [], bs =>
    ⟨fun h => by
      have hlen := congrArg (fun p => p.coeffs.length) h
      rw [charPoly_length, charPoly_length] at hlen
      cases bs with | nil => exact .nil | cons _ _ => simp at hlen, charPoly_perm⟩
  | a :: as, bs =>
    ⟨fun h => by
      have haEval : (charPoly bs).eval a = CommRingOps.zero := by
        rw [← h, charPoly, eval_mulLinFactor, LawfulCommRing.sub_self, LawfulCommRing.zero_mul]
      have hPermErase : bs.Perm (a :: bs.erase a) := List.perm_cons_erase ((charPoly_eval_eq_zero_iff a bs).mp haEval)
      rw [charPoly, charPoly_perm hPermErase] at h
      exact ((charPoly_eq_iff_perm as (bs.erase a)).mp (mulLinFactor_injective a h)).cons a |>.trans hPermErase.symm,
     charPoly_perm⟩

theorem subCoeffs_length_le {R : Type} [CommRingOps R] :
    ∀ (cs ds : List R), (RoundPoly.subCoeffs cs ds).length ≤ max cs.length ds.length
  | [], [] => by simp [RoundPoly.subCoeffs]
  | _ :: cs, [] => by have ih := subCoeffs_length_le cs []; simp only [RoundPoly.subCoeffs, List.length_cons, List.length_nil] at ih ⊢; omega
  | [], _ :: ds => by have ih := subCoeffs_length_le [] ds; simp only [RoundPoly.subCoeffs, List.length_cons, List.length_nil] at ih ⊢; omega
  | _ :: cs, _ :: ds => by have ih := subCoeffs_length_le cs ds; simp only [RoundPoly.subCoeffs, List.length_cons]; omega

private theorem subCoeffs_nil_left {R : Type} [CommRingOps R] :
    ∀ ds : List R, RoundPoly.subCoeffs [] ds = ds.map CommRingOps.neg
  | [] => by simp [RoundPoly.subCoeffs]
  | _ :: ds => by simp only [RoundPoly.subCoeffs, List.map_cons, subCoeffs_nil_left ds]

private theorem subCoeffs_nil_right {R : Type} [CommRingOps R] :
    ∀ cs : List R, RoundPoly.subCoeffs cs [] = cs
  | [] => by simp [RoundPoly.subCoeffs]
  | _ :: cs => by simp only [RoundPoly.subCoeffs, subCoeffs_nil_right cs]

private theorem subCoeffs_cons_cons {R : Type} [CommRingOps R] (c d : R) (cs ds : List R) :
    RoundPoly.subCoeffs (c :: cs) (d :: ds) = CommRingOps.sub c d :: RoundPoly.subCoeffs cs ds := by
  simp [RoundPoly.subCoeffs]

private theorem subCoeffs_all_zero_monic_eq {F : Type} [LawfulIntegralDomain F] :
    ∀ (cs ds : List F), cs.getLast? = some CommRingOps.one → ds.getLast? = some CommRingOps.one →
      (∀ z ∈ RoundPoly.subCoeffs cs ds, z = CommRingOps.zero) → cs = ds
  | [], _, h1, _, _ => by cases h1
  | _, [], _, h2, _ => by cases h2
  | [c], [d], h1, h2, _ => by simp at h1 h2; subst h1 h2; rfl
  | [_], _ :: d2 :: ds2, _, h2, hz => by
    exfalso
    have hneg0 : CommRingOps.neg (CommRingOps.one : F) = CommRingOps.zero :=
      hz _ (by simp only [RoundPoly.subCoeffs, subCoeffs_nil_left]
               exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_getLast? h2)))
    have h01 := congrArg (CommRingOps.add CommRingOps.one) hneg0
    rw [LawfulCommRing.add_right_neg, LawfulCommRing.add_zero] at h01
    exact LawfulIntegralDomain.zero_ne_one h01
  | _ :: c2 :: cs2, [_], h1, _, hz => by
    exfalso
    have h10 : (CommRingOps.one : F) = CommRingOps.zero :=
      hz _ (by simp only [RoundPoly.subCoeffs, subCoeffs_nil_right]
               exact List.mem_cons_of_mem _ (List.mem_of_getLast? h1))
    exact LawfulIntegralDomain.zero_ne_one h10.symm
  | c :: c2 :: cs2, d :: d2 :: ds2, h1, h2, hz => by
    rw [subCoeffs_cons_cons] at hz
    have hcd : c = d := eq_of_sub_eq_zero (hz _ List.mem_cons_self)
    have htail : c2 :: cs2 = d2 :: ds2 := subCoeffs_all_zero_monic_eq (c2 :: cs2) (d2 :: ds2) h1 h2
      (fun z hm => hz z (List.mem_cons_of_mem _ hm))
    rw [hcd, htail]

private theorem mulLinFactorAux_getLast {F : Type} [CommRingOps F] (a : F) :
    ∀ (cs : List F) (prev : F), cs ≠ [] → (mulLinFactorAux prev a cs).getLast? = cs.getLast?
  | [], _, h => absurd rfl h
  | [_], _, _ => rfl
  | _ :: v :: vs, _, _ => mulLinFactorAux_getLast a (v :: vs) _ (by simp)

private theorem charPoly_monic {F : Type} [CommRingOps F] :
    ∀ l : List F, (charPoly l).coeffs.getLast? = some CommRingOps.one
  | [] => rfl
  | a :: as => by
    simp only [charPoly, mulLinFactor]
    rw [mulLinFactorAux_getLast a (charPoly as).coeffs CommRingOps.zero
      (fun he => by have hl := charPoly_length as; rw [he] at hl; simp at hl)]
    exact charPoly_monic as

/-- **`LinMem` Characteristic-Polynomial Multiset Weld (`linmemPolyIdentity_implies_perm`)**. -/
theorem linmemPolyIdentity_implies_perm {F : Type} [LawfulIntegralDomain F] [DecidableEq F]
    (init prod cons final S : List F) (hS : S.Nodup) :
    let lhs := init ++ prod
    let rhs := cons ++ final
    let N := max lhs.length rhs.length
    ((lhs.Perm rhs → ∀ γ : F, (charPoly lhs).eval γ = (charPoly rhs).eval γ) ∧
     (lhs.Perm rhs ∨
      (S.filter fun γ => decide ((charPoly lhs).eval γ = (charPoly rhs).eval γ)).length ≤ N)) := by
  dsimp only
  let lhs := init ++ prod; let rhs := cons ++ final; let N := max lhs.length rhs.length
  refine ⟨fun hp γ => by rw [charPoly_perm hp], ?_⟩
  by_cases hPolyEq : charPoly lhs = charPoly rhs
  · exact .inl ((charPoly_eq_iff_perm lhs rhs).mp hPolyEq)
  · right
    let diff := (charPoly lhs).sub (charPoly rhs)
    have hDiffLen : diff.coeffs.length ≤ N + 1 := by
      have hl := subCoeffs_length_le (charPoly lhs).coeffs (charPoly rhs).coeffs
      rw [charPoly_length, charPoly_length] at hl; unfold diff RoundPoly.sub; dsimp only; omega
    have hNz : ∃ c ∈ diff.coeffs, c ≠ CommRingOps.zero := by
      cases hdb : diff.coeffs.all (fun z => decide (z = CommRingOps.zero)) with
      | false => exact exists_ne_zero_of_all_false diff.coeffs hdb
      | true =>
        exfalso
        have hcsEq := subCoeffs_all_zero_monic_eq _ _ (charPoly_monic lhs) (charPoly_monic rhs)
          (fun z hz => of_decide_eq_true (List.all_eq_true.mp hdb z hz))
        apply hPolyEq
        cases hp1 : charPoly lhs with | mk cs1 =>
        cases hp2 : charPoly rhs with | mk cs2 =>
        rw [hp1, hp2] at hcsEq; exact congrArg RoundPoly.mk hcsEq
    have hFilterEq : S.filter (fun γ => decide ((charPoly lhs).eval γ = (charPoly rhs).eval γ)) =
        S.filter (fun γ => decide (diff.eval γ = CommRingOps.zero)) := by
      apply List.filter_congr; intro γ _
      simp only [diff, RoundPoly.eval_sub, LawfulIntegralDomain.sub_eq_zero_iff]
    rw [hFilterEq]; exact schwartzZippel_roots_le_deg N diff S hS hDiffLen hNz

end Obend.SymbolicZk.CompileToPiop
end
