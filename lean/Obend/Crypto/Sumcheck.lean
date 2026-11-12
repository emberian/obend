module
/-
# Obend.Crypto.Sumcheck — Instance-Bound Multilinear Sumcheck PIOP & 128-Bit $\mathbb{F}_{p^2}$ Field Soundness
Polymorphic Fiat–Shamir Sumcheck PIOP over `[LawfulCommRing R]` paired with `Transcript` & `BoundTranscript`,
constructive Proth primality of `goldilocksPrime`, `GoldilocksExt2.inv` ($\mathbb{F}_{p^2}$), `NoZeroDivisors`,
and exact degree-$d$ polynomial root bound (`RoundPoly.roots_nodup_length_le`, $\le d / p^2 < d / 2^{127}$).
-/
public import Obend.Crypto.Multilinear
public import Obend.Crypto.Transcript

public section
namespace Obend.Crypto

open Obend.Digest.Cshake256
open Obend.Apps.ZkNtt
open Obend.Judge.Computational

set_option autoImplicit false

/-! ## 1. Transcript Challenge Interface (`Goldilocks` & `GoldilocksExt2`) -/

/-- Bridges a ring/field `R` to a seeded 256-bit Fiat–Shamir `Transcript phase`. -/
class TranscriptChallenge (R : Type) where
  encodeElem : R → ByteArray
  squeezeChallenge : ∀ {phase : TranscriptPhase} [CanSqueezeTranscript phase],
    Transcript phase → R × Transcript phase

instance : TranscriptChallenge Goldilocks where
  encodeElem := encodeGoldilocksBytes
  squeezeChallenge := squeezeGoldilocks

instance : TranscriptChallenge GoldilocksExt2 where
  encodeElem := encodeGoldilocksExt2Bytes
  squeezeChallenge := squeezeGoldilocksExt2

/-! ## 2. Zero-Axiom Proth Primality of `goldilocksPrime` & $\mathbb{F}_{p^2}$ Field Inversion -/

/-- Strict `Nat` WHNF thunk breaker so kernel `decide` reduces intermediate results once per step. -/
private def strictNat (n : Nat) (k : Nat → Nat) : Nat :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

private theorem strictNat_eq (n : Nat) (k : Nat → Nat) : strictNat n k = k n := by
  cases n <;> rfl

/-- Fuel-bounded binary modular exponentiation `base ^ exp % m` (kernel-reducible via `decide`). -/
def modPowFuel : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, base, exp, m =>
    if exp = 0 then 1 % m
    else
      strictNat (modPowFuel fuel base (exp / 2) m) fun half =>
        strictNat ((half * half) % m) fun sq =>
          if exp % 2 = 1 then (sq * (base % m)) % m else sq

private theorem pow_two_mul (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem modPowFuel_eq_pow_mod :
    ∀ (fuel base exp m : Nat), exp < 2 ^ fuel → modPowFuel fuel base exp m = (base ^ exp) % m
  | 0, _, exp, m, hlt => by
    have he0 : exp = 0 := by simp at hlt; omega
    subst he0; simp [modPowFuel]
  | fuel + 1, base, exp, m, hlt => by
    simp only [modPowFuel]
    if h0 : exp = 0 then
      subst h0; simp
    else
      simp only [h0, ↓reduceIte, strictNat_eq]
      have hexpHalf : exp / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hlt; omega
      have ih := modPowFuel_eq_pow_mod fuel base (exp / 2) m hexpHalf
      have hsq : ((modPowFuel fuel base (exp / 2) m) * (modPowFuel fuel base (exp / 2) m)) % m =
          (base ^ (2 * (exp / 2))) % m := by
        rw [ih, ← Nat.mul_mod, ← pow_two_mul]
      have hmod2 : exp % 2 = 0 ∨ exp % 2 = 1 := by omega
      rcases hmod2 with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide, ↓reduceIte]
        have hexp : 2 * (exp / 2) = exp := by omega
        rw [hsq, hexp]
      · simp only [hr1, ↓reduceIte]
        have hexp : exp = 2 * (exp / 2) + 1 := by omega
        conv => rhs; rw [hexp, Nat.pow_add, Nat.pow_one, Nat.mul_mod]
        rw [hsq]

/-- Elementary primality predicate on `Nat`. -/
def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

private def minDivisorAux (n d : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n % d = 0 then d else minDivisorAux n (d + 1) fuel

private def minDivisor (n : Nat) : Nat :=
  if n < 2 then n else minDivisorAux n 2 n

private theorem minDivisorAux_spec :
    ∀ (fuel n d : Nat),
      2 ≤ n → 2 ≤ d → n ≤ d + fuel →
      (∀ k : Nat, 2 ≤ k → k < d → ¬ (k ∣ n)) →
      let q := minDivisorAux n d fuel
      2 ≤ q ∧ q ∣ n ∧ (∀ k : Nat, 2 ≤ k → k < q → ¬ (k ∣ n))
  | 0, n, d, hn2, _, _, hno => by
    dsimp only [minDivisorAux]
    refine ⟨hn2, Nat.dvd_refl n, ?_⟩
    intro k hk2 hklt
    exact hno k hk2 (by omega)
  | fuel + 1, n, d, hn2, hd, hle, hno => by
    dsimp only [minDivisorAux]
    if hmod : n % d = 0 then
      simp only [hmod, ↓reduceIte]
      exact ⟨hd, Nat.dvd_of_mod_eq_zero hmod, hno⟩
    else
      simp only [hmod, ↓reduceIte]
      apply minDivisorAux_spec fuel n (d + 1) hn2 (by omega) (by omega)
      intro k hk2 hklt
      if hkd : k = d then
        subst hkd
        intro hdvd
        exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
      else
        exact hno k hk2 (by omega)

private theorem minDivisor_isPrime {n : Nat} (hn : 2 ≤ n) :
    IsPrimeNat (minDivisor n) ∧ minDivisor n ∣ n ∧ minDivisor n ≤ n := by
  unfold minDivisor
  have hnot : ¬ n < 2 := by omega
  simp only [hnot, ↓reduceIte]
  obtain ⟨hq2, hqdvd, hqmin⟩ := minDivisorAux_spec n n 2 hn (by decide) (by omega) (by intros; omega)
  have hqle : minDivisorAux n 2 n ≤ n := Nat.le_of_dvd (by omega) hqdvd
  refine ⟨⟨hq2, ?_⟩, hqdvd, hqle⟩
  intro d hd
  if hd1 : d = 1 then exact .inl hd1
  else if hdq : d = minDivisorAux n 2 n then exact .inr hdq
  else
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hdle : d ≤ minDivisorAux n 2 n := Nat.le_of_dvd (by omega) hd
    exact False.elim (hqmin d (by omega) (by omega) (Nat.dvd_trans hd hqdvd))

/-- Extended Euclidean algorithm returning `(g, x, y)` with `g ∣ a`, `g ∣ b`, and `a*x + b*y = g`. -/
def extGcd (a b : Nat) : Nat × Int × Int :=
  if _hb : b = 0 then (a, 1, 0)
  else
    let r := extGcd b (a % b)
    (r.1, r.2.2, r.2.1 - ((a / b : Nat) : Int) * r.2.2)
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero _hb)

theorem extGcd_dvd (a b : Nat) : (extGcd a b).1 ∣ a ∧ (extGcd a b).1 ∣ b := by
  if hb : b = 0 then
    subst hb
    rw [extGcd]
    simp only [↓reduceDIte]
    exact ⟨Nat.dvd_refl a, Nat.dvd_zero a⟩
  else
    obtain ⟨hdb, hdmod⟩ := extGcd_dvd b (a % b)
    have heq : (extGcd a b).1 = (extGcd b (a % b)).1 := by
      conv => lhs; rw [extGcd]
      simp [hb]
    rw [heq]
    refine ⟨?_, hdb⟩
    have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have hmul : (extGcd b (a % b)).1 ∣ b * (a / b) := Nat.dvd_trans hdb (Nat.dvd_mul_right b (a / b))
    have hsum := Nat.dvd_add hmul hdmod
    rwa [hdiv] at hsum
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

theorem extGcd_bezout (a b : Nat) :
    (a : Int) * (extGcd a b).2.1 + (b : Int) * (extGcd a b).2.2 = ((extGcd a b).1 : Int) := by
  if hb : b = 0 then
    subst hb
    rw [extGcd]
    simp
  else
    have ih := extGcd_bezout b (a % b)
    have hstep : extGcd a b =
        ((extGcd b (a % b)).1,
         (extGcd b (a % b)).2.2,
         (extGcd b (a % b)).2.1 - ((a / b : Nat) : Int) * (extGcd b (a % b)).2.2) := by
      conv => lhs; rw [extGcd]
      simp [hb]
    rw [hstep]
    dsimp only
    have hdivInt : (b : Int) * ((a / b : Nat) : Int) + ((a % b : Nat) : Int) = (a : Int) := by
      exact_mod_cast Nat.div_add_mod a b
    have h1 : (b : Int) * ((extGcd b (a % b)).2.1 - ((a / b : Nat) : Int) * (extGcd b (a % b)).2.2) =
        (b : Int) * (extGcd b (a % b)).2.1 - ((b : Int) * ((a / b : Nat) : Int)) * (extGcd b (a % b)).2.2 := by
      rw [Int.mul_sub, Int.mul_assoc]
    have h2 : ((a : Int) - (b : Int) * ((a / b : Nat) : Int)) * (extGcd b (a % b)).2.2 =
        (a : Int) * (extGcd b (a % b)).2.2 - ((b : Int) * ((a / b : Nat) : Int)) * (extGcd b (a % b)).2.2 :=
      Int.sub_mul _ _ _
    have h3 : ((a % b : Nat) : Int) = (a : Int) - (b : Int) * ((a / b : Nat) : Int) := by omega
    rw [h3, h2] at ih
    rw [h1]
    omega
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

theorem IsPrimeNat.dvd_mul {q a b : Nat} (hq : IsPrimeNat q)
    (hdvd : q ∣ a * b) (hna : ¬ (q ∣ a)) : q ∣ b := by
  obtain ⟨hda, hdq⟩ := extGcd_dvd a q
  have hg1 : (extGcd a q).1 = 1 := by
    rcases hq.2 _ hdq with h1 | hqq
    · exact h1
    · rw [hqq] at hda
      exact False.elim (hna hda)
  have hbez := extGcd_bezout a q
  rw [hg1] at hbez
  obtain ⟨k, hk⟩ := hdvd
  have hmul : ((a : Int) * (extGcd a q).2.1 + (q : Int) * (extGcd a q).2.2) * (b : Int) =
      1 * (b : Int) := congrArg (· * (b : Int)) hbez
  rw [Int.add_mul, Int.one_mul] at hmul
  have hab : (a : Int) * (extGcd a q).2.1 * (b : Int) =
      (q : Int) * ((k : Int) * (extGcd a q).2.1) := by
    have hkInt : (a : Int) * (b : Int) = (q : Int) * (k : Int) := by exact_mod_cast hk
    rw [Int.mul_right_comm (a : Int), hkInt, Int.mul_assoc]
  rw [hab, Int.mul_assoc (q : Int), ← Int.mul_add] at hmul
  exact Int.ofNat_dvd.1 ⟨(k : Int) * (extGcd a q).2.1 + (extGcd a q).2.2 * (b : Int), hmul.symm⟩

private def posRange : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: posRange n

private theorem posRange_length (n : Nat) : (posRange n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [posRange, ih]

private theorem mem_posRange_iff {x : Nat} : ∀ {n : Nat}, x ∈ posRange n ↔ 1 ≤ x ∧ x ≤ n
  | 0 => by simp [posRange]; omega
  | n + 1 => by
    simp only [posRange, List.mem_cons, mem_posRange_iff]
    omega

private theorem posRange_nodup : ∀ (n : Nat), (posRange n).Nodup
  | 0 => .nil
  | n + 1 =>
    .cons
      (fun b hb heq => by
        have hle := (mem_posRange_iff.1 hb).2
        omega)
      (posRange_nodup n)

private def listProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * listProd xs

private def eraseFirst (v : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if y = v then ys else y :: eraseFirst v ys

private theorem mem_of_mem_eraseFirst {v z : Nat} :
    ∀ {ys : List Nat}, z ∈ eraseFirst v ys → z ∈ ys
  | [], h => by cases h
  | y :: ys, h => by
    simp only [eraseFirst] at h
    split at h
    · exact .tail _ h
    · cases h with
      | head => exact .head _
      | tail _ ht => exact .tail _ (mem_of_mem_eraseFirst ht)

private theorem eraseFirst_spec {v : Nat} :
    ∀ {ys : List Nat},
      ys.Nodup → v ∈ ys →
      listProd ys = v * listProd (eraseFirst v ys) ∧
      (eraseFirst v ys).length + 1 = ys.length ∧
      (eraseFirst v ys).Nodup ∧
      (∀ z : Nat, z ≠ v → z ∈ ys → z ∈ eraseFirst v ys)
  | [], _, hmem => by cases hmem
  | y :: ys, .cons hrel hnd, hmem => by
    dsimp only [eraseFirst]
    if hy : y = v then
      subst hy
      simp only [↓reduceIte, listProd, List.length_cons]
      refine ⟨trivial, trivial, hnd, ?_⟩
      intro z hzne hzmem
      cases hzmem with
      | head => exact False.elim (hzne rfl)
      | tail _ htail => exact htail
    else
      simp only [hy, ↓reduceIte, listProd, List.length_cons]
      have hvTail : v ∈ ys := by
        cases hmem with
        | head => exact False.elim (hy rfl)
        | tail _ ht => exact ht
      obtain ⟨hprod, hlen, hnd', hsub⟩ := eraseFirst_spec hnd hvTail
      refine ⟨?_, by omega, .cons (fun b hb heq => hrel b (mem_of_mem_eraseFirst hb) heq) hnd', ?_⟩
      · rw [hprod, ← Nat.mul_assoc, Nat.mul_comm y v, Nat.mul_assoc]
      · intro z hzne hzmem
        cases hzmem with
        | head => exact .head _
        | tail _ ht => exact .tail _ (hsub z hzne ht)

private theorem listProd_eq_of_nodup_subset :
    ∀ {xs ys : List Nat},
      xs.Nodup → ys.Nodup → xs.length = ys.length →
      (∀ x ∈ xs, x ∈ ys) → listProd xs = listProd ys
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | x :: xs, ys, .cons hrel hndX, hndY, hlen, hsub => by
    obtain ⟨hprodY, hlenE, hndE, hmemE⟩ := eraseFirst_spec hndY (hsub x (.head _))
    simp only [List.length_cons] at hlen
    have ih := listProd_eq_of_nodup_subset hndX hndE (by omega) (fun z hz =>
      hmemE z (fun heq => hrel z hz heq.symm) (hsub z (.tail _ hz)))
    simp only [listProd, ih, hprodY]

private theorem listProd_map_mul_mod (a q : Nat) :
    ∀ (n : Nat),
      listProd ((posRange n).map (fun i => (a * i) % q)) % q =
      (a ^ n * listProd (posRange n)) % q
  | 0 => by simp [posRange, listProd]
  | n + 1 => by
    simp only [posRange, List.map_cons, listProd]
    rw [Nat.mul_mod ((a * (n + 1)) % q), Nat.mod_mod, listProd_map_mul_mod a q n, ← Nat.mul_mod]
    have hcomm : a * (n + 1) * (a ^ n * listProd (posRange n)) =
        a ^ (n + 1) * ((n + 1) * listProd (posRange n)) := by
      rw [Nat.pow_succ, Nat.mul_comm (a ^ n) a]
      rw [Nat.mul_assoc a (n + 1) (a ^ n * listProd (posRange n)),
          ← Nat.mul_assoc (n + 1) (a ^ n) (listProd (posRange n)),
          Nat.mul_comm (n + 1) (a ^ n),
          Nat.mul_assoc (a ^ n) (n + 1) (listProd (posRange n)),
          ← Nat.mul_assoc a (a ^ n) _]
    rw [hcomm]

private theorem not_dvd_listProd_posRange {q : Nat} (hq : IsPrimeNat q) :
    ∀ {n : Nat}, n < q → ¬ (q ∣ listProd (posRange n))
  | 0, _, hdvd => by
    dsimp only [posRange, listProd] at hdvd
    have hle := Nat.le_of_dvd (by decide) hdvd
    have hq2 := hq.1
    omega
  | n + 1, hlt, hdvd => by
    simp only [posRange, listProd] at hdvd
    have hnot1 : ¬ (q ∣ (n + 1)) := by
      intro h1
      have hle := Nat.le_of_dvd (by omega) h1
      omega
    exact not_dvd_listProd_posRange hq (by omega) (hq.dvd_mul hdvd hnot1)

private theorem sub_dvd_of_mod_eq {x y q : Nat} (hle : y ≤ x) (hmod : x % q = y % q) :
    q ∣ (x - y) := by
  have hx : q * (x / q) + x % q = x := Nat.div_add_mod x q
  have hy : q * (y / q) + y % q = y := Nat.div_add_mod y q
  have hdivLe : y / q ≤ x / q := Nat.div_le_div_right hle
  refine ⟨x / q - y / q, ?_⟩
  rw [Nat.mul_sub]
  omega

private theorem one_le_pow_of_pos {a : Nat} (ha : 1 ≤ a) : ∀ k : Nat, 1 ≤ a ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => by
    rw [Nat.pow_succ]
    exact Nat.le_trans (one_le_pow_of_pos ha k) (Nat.le_mul_of_pos_right _ ha)

/-- **Fermat's Little Theorem (`IsPrimeNat.pow_sub_one_mod`)**:
    For every prime `q` and integer `a` with `¬ (q ∣ a)`, `a ^ (q - 1) % q = 1`. -/
theorem IsPrimeNat.pow_sub_one_mod {q a : Nat} (hq : IsPrimeNat q) (hna : ¬ (q ∣ a)) :
    (a ^ (q - 1)) % q = 1 := by
  let L := posRange (q - 1)
  let f := fun i : Nat => (a * i) % q
  have hMem : ∀ x ∈ L.map f, x ∈ L := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hi1, hi2⟩ := mem_posRange_iff.1 hi
    have hni : ¬ (q ∣ i) := fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      have hq2 := hq.1
      omega
    have hnai : ¬ (q ∣ a * i) := fun hd => hni (hq.dvd_mul (Nat.mul_comm a i ▸ hd) hna)
    have hmodPos : 0 < (a * i) % q := by
      if hz : (a * i) % q = 0 then
        exact False.elim (hnai (Nat.dvd_of_mod_eq_zero hz))
      else omega
    have hmodLt : (a * i) % q < q := Nat.mod_lt _ (by have := hq.1; omega)
    dsimp only [f]
    exact mem_posRange_iff.2 ⟨hmodPos, by omega⟩
  have hInjOn : ∀ i j : Nat, i ∈ L → j ∈ L → f i = f j → i = j := by
    intro i j hi hj hij
    obtain ⟨hi1, hi2⟩ := mem_posRange_iff.1 hi
    obtain ⟨hj1, hj2⟩ := mem_posRange_iff.1 hj
    have hq2 := hq.1
    if hijLe : i ≤ j then
      have hdvd : q ∣ a * (j - i) := by
        have hmul : a * j - a * i = a * (j - i) := (Nat.mul_sub a j i).symm
        rw [← hmul]
        exact sub_dvd_of_mod_eq (Nat.mul_le_mul_left a hijLe) hij.symm
      have hdvdDiff : q ∣ (j - i) := hq.dvd_mul hdvd hna
      if hdiff0 : j - i = 0 then omega
      else
        have hle := Nat.le_of_dvd (by omega) hdvdDiff
        omega
    else
      have hjiLe : j ≤ i := by omega
      have hdvd : q ∣ a * (i - j) := by
        have hmul : a * i - a * j = a * (i - j) := (Nat.mul_sub a i j).symm
        rw [← hmul]
        exact sub_dvd_of_mod_eq (Nat.mul_le_mul_left a hjiLe) hij
      have hdvdDiff : q ∣ (i - j) := hq.dvd_mul hdvd hna
      if hdiff0 : i - j = 0 then omega
      else
        have hle := Nat.le_of_dvd (by omega) hdvdDiff
        omega
  have hNodupMap : (L.map f).Nodup := by
    have hsubNd : ∀ {xs : List Nat}, xs.Nodup → (∀ z ∈ xs, z ∈ L) → (xs.map f).Nodup := by
      intro xs hnd hxs
      induction hnd with
      | nil => exact .nil
      | @cons x rest hrel hndRest ih =>
        refine .cons (fun b hb heq => ?_) (ih (fun z hz => hxs z (.tail _ hz)))
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
        have hxy := hInjOn x y (hxs x (.head _)) (hxs y (.tail _ hy)) heq
        exact hrel y hy hxy
    exact hsubNd (posRange_nodup (q - 1)) (fun z hz => hz)
  have hProdEq : listProd (L.map f) = listProd L :=
    listProd_eq_of_nodup_subset hNodupMap (posRange_nodup (q - 1)) (by simp) hMem
  have hModEq : (a ^ (q - 1) * listProd L) % q = (listProd L) % q := by
    rw [← listProd_map_mul_mod a q (q - 1), hProdEq]
  have haPos : 1 ≤ a := by
    if ha0 : a = 0 then subst ha0; exact False.elim (hna (Nat.dvd_zero q))
    else omega
  have hpowPos : 1 ≤ a ^ (q - 1) := one_le_pow_of_pos haPos (q - 1)
  have hdvdMul : q ∣ (a ^ (q - 1) - 1) * listProd L := by
    have hsub : a ^ (q - 1) * listProd L - listProd L = (a ^ (q - 1) - 1) * listProd L := by
      rw [Nat.sub_mul, Nat.one_mul]
    rw [← hsub]
    exact sub_dvd_of_mod_eq (Nat.le_mul_of_pos_left _ hpowPos) hModEq
  have hnotF : ¬ (q ∣ listProd L) :=
    not_dvd_listProd_posRange hq (by have := hq.1; omega)
  have hdvdPow : q ∣ (a ^ (q - 1) - 1) :=
    hq.dvd_mul (Nat.mul_comm (a ^ (q - 1) - 1) (listProd L) ▸ hdvdMul) hnotF
  obtain ⟨k, hk⟩ := hdvdPow
  have hEq : a ^ (q - 1) = q * k + 1 := by omega
  rw [hEq, Nat.mul_add_mod, Nat.mod_eq_of_lt hq.1]

private theorem pow_mod_eq_one_of_eq_one {a q : Nat} (hq : 2 ≤ q) (ha : a % q = 1) :
    ∀ k : Nat, (a ^ k) % q = 1
  | 0 => Nat.mod_eq_of_lt hq
  | k + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod, pow_mod_eq_one_of_eq_one hq ha k, ha]
    exact Nat.mod_eq_of_lt hq

private theorem pow_gcd_mod_eq_one {a q : Nat} (hq : 2 ≤ q) :
    ∀ (m n : Nat), (a ^ m) % q = 1 → (a ^ n) % q = 1 → (a ^ (Nat.gcd m n)) % q = 1
  | 0, n, _, hn => by simpa [Nat.gcd_zero_left] using hn
  | m + 1, n, hm, hn => by
    have hdiv : (m + 1) * (n / (m + 1)) + n % (m + 1) = n := Nat.div_add_mod n (m + 1)
    have hrem : (a ^ (n % (m + 1))) % q = 1 := by
      have hn' : (a ^ ((m + 1) * (n / (m + 1)) + n % (m + 1))) % q = 1 := hdiv.symm ▸ hn
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod,
          pow_mod_eq_one_of_eq_one hq hm (n / (m + 1)), Nat.one_mul, Nat.mod_mod] at hn'
      exact hn'
    rw [Nat.gcd_rec (m + 1) n]
    exact pow_gcd_mod_eq_one hq (n % (m + 1)) (m + 1) hrem hm
termination_by m _ => m
decreasing_by exact Nat.mod_lt n (Nat.succ_pos m)

private theorem dvd_of_two_pow_dvd_mul_odd :
    ∀ (k g c : Nat), c % 2 = 1 → 2 ^ k ∣ g * c → 2 ^ k ∣ g
  | 0, g, _, _, _ => Nat.one_dvd g
  | k + 1, g, c, hodd, hdvd => by
    have h2prime : IsPrimeNat 2 := ⟨by decide, fun d hd => by
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
      have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd
      omega⟩
    have hnc : ¬ (2 ∣ c) := fun hc => by obtain ⟨t, rfl⟩ := hc; omega
    have h2dvd : 2 ∣ g * c := by
      rw [Nat.pow_succ] at hdvd
      exact Nat.dvd_trans (Nat.dvd_mul_left 2 (2 ^ k)) hdvd
    obtain ⟨g', rfl⟩ := h2prime.dvd_mul (Nat.mul_comm g c ▸ h2dvd) hnc
    have hdvd' : 2 ^ k ∣ g' * c := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc 2 g' c] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by decide) hdvd
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    exact Nat.mul_dvd_mul_left 2 (dvd_of_two_pow_dvd_mul_odd k g' c hodd hdvd')

private theorem goldilocksEuler_modPow :
    ∀ u : Unit, u = () →
      (7 ^ ((goldilocksPrime - 1) / 2)) % goldilocksPrime = goldilocksPrime - 1 := by
  intro _ _
  rw [← modPowFuel_eq_pow_mod 64 7 ((goldilocksPrime - 1) / 2) goldilocksPrime (by decide)]
  decide

/-- **Zero-Axiom Proth Primality Theorem for `goldilocksPrime` ($p = 2^{64} - 2^{32} + 1$)**:
    Every natural divisor of `goldilocksPrime` is `1` or `goldilocksPrime`. -/
theorem goldilocksPrime_dvd_cases (d : Nat) (hd : d ∣ goldilocksPrime) :
    d = 1 ∨ d = goldilocksPrime := by
  if hd1 : d = 1 then exact .inl hd1
  else if hdp : d = goldilocksPrime then exact .inr hdp
  else
    exfalso
    obtain ⟨e, he⟩ := hd
    have hdPos : 2 ≤ d := by
      if hd0 : d = 0 then subst hd0; simp [goldilocksPrime] at he
      else omega
    have hePos : 2 ≤ e := by
      if he0 : e = 0 then subst he0; simp [goldilocksPrime] at he
      else if he1 : e = 1 then subst he1; simp at he; exact False.elim (hdp he.symm)
      else omega
    let m := if d ≤ e then d else e
    have hm2 : 2 ≤ m := by dsimp [m]; split <;> omega
    have hmDvd : m ∣ goldilocksPrime := by
      dsimp [m]; split
      · exact ⟨e, he⟩
      · exact ⟨d, Nat.mul_comm d e ▸ he⟩
    have hmSq : m * m ≤ goldilocksPrime := by
      dsimp [m]; split
      · rename_i hle; rw [he]; exact Nat.mul_le_mul_left d hle
      · rename_i hgt; rw [he, Nat.mul_comm d e]; exact Nat.mul_le_mul_left e (by omega)
    obtain ⟨q, hqDef⟩ : ∃ q, minDivisor m = q := ⟨minDivisor m, rfl⟩
    obtain ⟨hqPrime, hqDvdM, hqLeM⟩ := minDivisor_isPrime hm2
    rw [hqDef] at hqPrime hqDvdM hqLeM
    have hqDvdP : q ∣ goldilocksPrime := Nat.dvd_trans hqDvdM hmDvd
    have hqSq : q * q < (2 ^ 32) * (2 ^ 32) := by
      have hpLt : goldilocksPrime < (2 ^ 32) * (2 ^ 32) := by decide
      exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul hqLeM hqLeM) hmSq) hpLt
    have hqLt32 : q < 2 ^ 32 := by
      if hge : 2 ^ 32 ≤ q then
        have hsqGe := Nat.mul_le_mul hge hge
        omega
      else omega
    have hqGe3 : 3 ≤ q := by
      have hq2 := hqPrime.1
      if hqEq2 : q = 2 then
        obtain ⟨k, hk⟩ := hqDvdP
        have hodd : goldilocksPrime % 2 = 1 := by decide
        rw [hqEq2] at hk
        omega
      else omega
    have hqNotDvd7 : ¬ (q ∣ 7) := by
      intro hd7
      have hle7 : q ≤ 7 := Nat.le_of_dvd (by decide) hd7
      have hrem : goldilocksPrime % 3 ≠ 0 ∧ goldilocksPrime % 5 ≠ 0 ∧ goldilocksPrime % 7 ≠ 0 := by
        decide
      obtain ⟨k, hk⟩ := hqDvdP
      have hcases : q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · exact hrem.1 (by omega)
      · rcases hqPrime.2 2 ⟨2, rfl⟩ with h | h <;> omega
      · exact hrem.2.1 (by omega)
      · rcases hqPrime.2 2 ⟨3, rfl⟩ with h | h <;> omega
      · exact hrem.2.2 (by omega)
    let half := (goldilocksPrime - 1) / 2
    have hEuler := goldilocksEuler_modPow () rfl
    have hHalfPlusOneDvdP : goldilocksPrime ∣ (7 ^ half + 1) := by
      have hdiv := Nat.div_add_mod (7 ^ half) goldilocksPrime
      rw [hEuler] at hdiv
      refine ⟨(7 ^ half) / goldilocksPrime + 1, ?_⟩
      have hpPos : 1 ≤ goldilocksPrime := by decide
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hHalfPlusOneDvdQ : q ∣ (7 ^ half + 1) := Nat.dvd_trans hqDvdP hHalfPlusOneDvdP
    have hHalfModQ : (7 ^ half) % q = q - 1 := by
      obtain ⟨t, ht⟩ := hHalfPlusOneDvdQ
      have htPos : 1 ≤ t := by
        if ht0 : t = 0 then
          rw [ht0, Nat.mul_zero] at ht
          exact False.elim (Nat.succ_ne_zero (7 ^ half) ht)
        else omega
      have hEq : 7 ^ half = q * (t - 1) + (q - 1) := by
        rw [Nat.mul_sub, Nat.mul_one]
        have hq1 : q ≤ q * t := by
          have h := Nat.mul_le_mul_left q htPos
          rwa [Nat.mul_one] at h
        omega
      rw [hEq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hPm1ModQ : (7 ^ (goldilocksPrime - 1)) % q = 1 := by
      have h2half : goldilocksPrime - 1 = 2 * half := by decide
      rw [h2half, pow_two_mul, Nat.mul_mod, hHalfModQ]
      obtain ⟨q2, hq2Eq⟩ : ∃ q2, q = q2 + 3 := ⟨q - 3, by omega⟩
      have hsq : (q - 1) * (q - 1) = q * (q - 2) + 1 := by
        rw [hq2Eq]
        have ha : q2 + 3 - 1 = q2 + 2 := by omega
        have hb : q2 + 3 - 2 = q2 + 1 := by omega
        rw [ha, hb]
        simp only [Nat.mul_add, Nat.add_mul]
        omega
      rw [hsq, Nat.mul_add_mod, Nat.mod_eq_of_lt hqPrime.1]
    have hQm1ModQ : (7 ^ (q - 1)) % q = 1 := hqPrime.pow_sub_one_mod hqNotDvd7
    obtain ⟨g, hgDef⟩ : ∃ g, Nat.gcd (goldilocksPrime - 1) (q - 1) = g := ⟨_, rfl⟩
    have hgPow : (7 ^ g) % q = 1 := by
      rw [← hgDef]
      exact pow_gcd_mod_eq_one hqPrime.1 (goldilocksPrime - 1) (q - 1) hPm1ModQ hQm1ModQ
    have hgNotDvdHalf : ¬ (g ∣ half) := by
      rintro ⟨u, hu⟩
      have h1 : (7 ^ half) % q = 1 := by
        rw [hu, Nat.pow_mul]
        exact pow_mod_eq_one_of_eq_one hqPrime.1 hgPow u
      rw [hHalfModQ] at h1
      omega
    obtain ⟨c, hc⟩ := hgDef ▸ Nat.gcd_dvd_left (goldilocksPrime - 1) (q - 1)
    have hcOdd : c % 2 = 1 := by
      if hce : c % 2 = 0 then
        obtain ⟨c', hc'⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
        have h2half : goldilocksPrime - 1 = 2 * half := by decide
        have hmul : 2 * half = 2 * (g * c') := by
          rw [← h2half, hc, hc', ← Nat.mul_assoc, Nat.mul_comm g 2, Nat.mul_assoc]
        have hhalfEq : half = g * c' := by omega
        exact False.elim (hgNotDvdHalf ⟨c', hhalfEq⟩)
      else omega
    have h2pow32DvdPm1 : 2 ^ 32 ∣ (goldilocksPrime - 1) := ⟨2 ^ 32 - 1, by decide⟩
    rw [hc] at h2pow32DvdPm1
    have h2pow32DvdG : 2 ^ 32 ∣ g := dvd_of_two_pow_dvd_mul_odd 32 g c hcOdd h2pow32DvdPm1
    have h2pow32DvdQm1 : 2 ^ 32 ∣ (q - 1) :=
      Nat.dvd_trans h2pow32DvdG (hgDef ▸ Nat.gcd_dvd_right (goldilocksPrime - 1) (q - 1))
    have hge : 2 ^ 32 ≤ q - 1 := Nat.le_of_dvd (by omega) h2pow32DvdQm1
    omega

theorem goldilocksPrime_isPrime (u : Unit) : IsPrimeNat goldilocksPrime :=
  ⟨by decide, fun _ => (let _ := u; goldilocksPrime_dvd_cases _)⟩

/-- Constructive field inverse in `Goldilocks` via $a^{p-2} \bmod p$ ($O(\log p)$ steps, `inv 0 = 0`). -/
def Goldilocks.inv (a : Goldilocks) : Goldilocks :=
  if a.val = 0 then Goldilocks.zero
  else Goldilocks.ofNat (modPowFuel 64 a.val (goldilocksPrime - 2) goldilocksPrime)

theorem Goldilocks.mul_inv_cancel {a : Goldilocks} (ha : a ≠ Goldilocks.zero) :
    CommRingOps.mul a (Goldilocks.inv a) = CommRingOps.one := by
  have hvalNe : a.val ≠ 0 := fun h => ha (Goldilocks.ext h)
  have hnotDvd : ¬ (goldilocksPrime ∣ a.val) := fun hd => by
    have hle := Nat.le_of_dvd (by omega) hd
    have hlt := a.isLt
    omega
  apply Goldilocks.ext
  change (Goldilocks.mul a (Goldilocks.inv a)).val = 1
  rw [Goldilocks.mul_val]
  unfold Goldilocks.inv
  simp only [hvalNe, ↓reduceIte, Goldilocks.ofNat]
  rw [modPowFuel_eq_pow_mod 64 a.val (goldilocksPrime - 2) goldilocksPrime (by decide),
      Nat.mod_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm a.val,
      ← Nat.pow_succ, show (goldilocksPrime - 2).succ = goldilocksPrime - 1 by decide]
  exact (goldilocksPrime_isPrime ()).pow_sub_one_mod hnotDvd

/-- Typeclass asserting that a commutative ring has no non-trivial zero divisors (integral domain). -/
class NoZeroDivisors (R : Type) [CommRingOps R] : Type where
  eq_zero_or_eq_zero_of_mul_eq_zero :
    ∀ {a b : R}, CommRingOps.mul a b = CommRingOps.zero →
      a = CommRingOps.zero ∨ b = CommRingOps.zero

instance : NoZeroDivisors Goldilocks where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    if ha : a = Goldilocks.zero then
      exact .inl ha
    else
      right
      have hmul := congrArg (CommRingOps.mul (Goldilocks.inv a)) h
      rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (Goldilocks.inv a) a,
          Goldilocks.mul_inv_cancel ha, LawfulCommRing.one_mul] at hmul
      exact hmul

private theorem pow_mod_congr {x y m : Nat} (h : x % m = y % m) :
    ∀ k : Nat, (x ^ k) % m = (y ^ k) % m
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, pow_mod_congr h k, h, ← Nat.mul_mod]

/-- **Quadratic Non-Residue Theorem (`GoldilocksExt2.nonResidue_not_square`)**:
    $7$ has no square root in `Goldilocks` (verified via Euler's criterion $7^{(p-1)/2} \equiv -1 \pmod p$),
    so $u^2 - 7$ is irreducible over $\mathbb{F}_p$ and `GoldilocksExt2` is the true field $\mathbb{F}_{p^2}$. -/
theorem GoldilocksExt2.nonResidue_not_square (y : Goldilocks) :
    CommRingOps.mul y y ≠ GoldilocksExt2.nonResidue := by
  intro hsq
  have hyNe : y.val ≠ 0 := by
    intro hy0
    have h0 : y = Goldilocks.zero := Goldilocks.ext hy0
    rw [h0] at hsq
    cases hsq
  have hval : (y.val * y.val) % goldilocksPrime = 7 := by
    have hv := congrArg Goldilocks.val hsq
    rw [show CommRingOps.mul y y = Goldilocks.mul y y from rfl, Goldilocks.mul_val] at hv
    exact hv
  let half := (goldilocksPrime - 1) / 2
  have hy2 : (y.val ^ 2) % goldilocksPrime = 7 % goldilocksPrime := by
    have h2 : y.val ^ 2 = y.val * y.val := by simp [Nat.pow_succ]
    rw [h2, hval]
    decide
  have hpowEq : ((y.val ^ 2) ^ half) % goldilocksPrime = (7 ^ half) % goldilocksPrime :=
    pow_mod_congr hy2 half
  rw [← Nat.pow_mul] at hpowEq
  have h2half : 2 * half = goldilocksPrime - 1 := by decide
  rw [h2half] at hpowEq
  have hnotDvd : ¬ (goldilocksPrime ∣ y.val) := fun hd => by
    have hle := Nat.le_of_dvd (by omega) hd
    have hlt := y.isLt
    omega
  have hflt := (goldilocksPrime_isPrime ()).pow_sub_one_mod hnotDvd
  have heuler := goldilocksEuler_modPow () rfl
  rw [hflt, heuler] at hpowEq
  revert hpowEq
  decide

/-- Algebraic norm $N(c_0 + c_1 u) = c_0^2 - 7 c_1^2 \in \mathbb{F}_p$ on `GoldilocksExt2`. -/
def GoldilocksExt2.norm (z : GoldilocksExt2) : Goldilocks :=
  CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
    (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1))

theorem GoldilocksExt2.norm_ne_zero {z : GoldilocksExt2} (hz : z ≠ GoldilocksExt2.zero) :
    GoldilocksExt2.norm z ≠ Goldilocks.zero := by
  intro hnorm
  change CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) =
      CommRingOps.zero at hnorm
  have hEq : CommRingOps.mul z.c0 z.c0 =
      CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1) := by
    have h1 := congrArg (fun t => CommRingOps.add t
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1))) hnorm
    rw [LawfulCommRing.zero_add, LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.add_assoc, LawfulCommRing.add_left_neg, LawfulCommRing.add_zero] at h1
    exact h1
  if hc1 : z.c1 = Goldilocks.zero then
    have hrhs : CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1) =
        Goldilocks.zero := by
      rw [hc1]
      change CommRingOps.mul GoldilocksExt2.nonResidue
        (CommRingOps.mul CommRingOps.zero CommRingOps.zero) = CommRingOps.zero
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero]
    rw [hrhs] at hEq
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hEq with hc0 | hc0 <;>
      exact hz (GoldilocksExt2.ext hc0 hc1)
  else
    let q := CommRingOps.mul z.c0 (Goldilocks.inv z.c1)
    have hqSq : CommRingOps.mul q q = GoldilocksExt2.nonResidue := by
      dsimp only [q]
      have hassoc : CommRingOps.mul (CommRingOps.mul z.c0 (Goldilocks.inv z.c1))
          (CommRingOps.mul z.c0 (Goldilocks.inv z.c1)) =
          CommRingOps.mul (CommRingOps.mul z.c0 z.c0)
            (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) := by
        rw [LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
            ← LawfulCommRing.mul_assoc (Goldilocks.inv z.c1) z.c0 _,
            LawfulCommRing.mul_comm (Goldilocks.inv z.c1) z.c0,
            LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
            ← LawfulCommRing.mul_assoc z.c0 z.c0 _]
      rw [hassoc, hEq, LawfulCommRing.mul_assoc GoldilocksExt2.nonResidue]
      have hcancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
          (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) = CommRingOps.one := by
        rw [LawfulCommRing.mul_assoc z.c1 z.c1 _,
            ← LawfulCommRing.mul_assoc z.c1 (Goldilocks.inv z.c1) _,
            Goldilocks.mul_inv_cancel hc1, LawfulCommRing.one_mul,
            Goldilocks.mul_inv_cancel hc1]
      rw [hcancel, LawfulCommRing.mul_one]
    exact GoldilocksExt2.nonResidue_not_square q hqSq

/-- Constructive 128-bit field inverse in `GoldilocksExt2` ($\mathbb{F}_{p^2}$):
    $(c_0 + c_1 u)^{-1} = (c_0 - c_1 u) \cdot (c_0^2 - 7 c_1^2)^{-1}$. -/
def GoldilocksExt2.inv (z : GoldilocksExt2) : GoldilocksExt2 :=
  let invN := Goldilocks.inv (GoldilocksExt2.norm z)
  ⟨CommRingOps.mul z.c0 invN, CommRingOps.neg (CommRingOps.mul z.c1 invN)⟩

theorem GoldilocksExt2.mul_inv_cancel {z : GoldilocksExt2} (hz : z ≠ GoldilocksExt2.zero) :
    CommRingOps.mul z (GoldilocksExt2.inv z) = CommRingOps.one := by
  have hnormNe := GoldilocksExt2.norm_ne_zero hz
  let invN := Goldilocks.inv (GoldilocksExt2.norm z)
  apply GoldilocksExt2.ext
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.mul z.c0 invN))
        (CommRingOps.mul GoldilocksExt2.nonResidue
          (CommRingOps.mul z.c1 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))) =
      CommRingOps.one
    rw [← LawfulCommRing.mul_assoc z.c0 z.c0 invN,
        LawfulCommRing.mul_neg z.c1, LawfulCommRing.mul_neg GoldilocksExt2.nonResidue,
        ← LawfulCommRing.mul_assoc z.c1 z.c1 invN,
        ← LawfulCommRing.mul_assoc GoldilocksExt2.nonResidue _ invN,
        ← LawfulCommRing.sub_eq_add_neg,
        ← LawfulCommRing.sub_mul]
    exact Goldilocks.mul_inv_cancel hnormNe
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))
        (CommRingOps.mul z.c1 (CommRingOps.mul z.c0 invN)) =
      CommRingOps.zero
    rw [LawfulCommRing.mul_neg,
        ← LawfulCommRing.mul_assoc z.c0 z.c1 invN,
        ← LawfulCommRing.mul_assoc z.c1 z.c0 invN,
        LawfulCommRing.mul_comm z.c1 z.c0,
        LawfulCommRing.add_left_neg]

instance : NoZeroDivisors GoldilocksExt2 where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    if ha : a = GoldilocksExt2.zero then
      exact .inl ha
    else
      right
      have hmul := congrArg (CommRingOps.mul (GoldilocksExt2.inv a)) h
      rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (GoldilocksExt2.inv a) a,
          GoldilocksExt2.mul_inv_cancel ha, LawfulCommRing.one_mul] at hmul
      exact hmul

/-- Exact 128-bit challenge space lower bound: $|\mathbb{F}_{p^2}| = p^2 > 2^{126}$
    (in fact $p^2 = 2^{128} - 2^{97} + 3 \cdot 2^{64} - 2^{33} + 1 > 2^{127}$). -/
theorem goldilocksExt2_card_gt_two_pow_126 (k : Nat) (hk : k ≤ 127) :
    2 ^ k < goldilocksPrime ^ 2 := by
  have hpow : 2 ^ k ≤ 2 ^ 127 := Nat.pow_le_pow_right (by decide) hk
  have hlt : 2 ^ 127 < goldilocksPrime ^ 2 := by decide
  exact Nat.lt_of_le_of_lt hpow hlt

/-! ## 3. Univariate Round Polynomials (`RoundPoly R`) & Exact Root-Counting Bound -/

/-- Univariate polynomial in monomial basis `coeffs = [c₀, c₁, …, c_d]`. -/
structure RoundPoly (R : Type) where
  coeffs : List R
  deriving DecidableEq, Repr

namespace RoundPoly

/-- Horner evaluation $c_0 + x (c_1 + x (\cdots))$. -/
def evalCoeffs {R : Type} [CommRingOps R] : List R → R → R
  | [], _ => CommRingOps.zero
  | c :: cs, x => CommRingOps.add c (CommRingOps.mul x (evalCoeffs cs x))

def eval {R : Type} [CommRingOps R] (p : RoundPoly R) (x : R) : R :=
  evalCoeffs p.coeffs x

/-- Check formal degree bound `coeffs.length ≤ maxDeg + 1`. -/
def degLe {R : Type} (maxDeg : Nat) (p : RoundPoly R) : Bool :=
  decide (p.coeffs.length ≤ maxDeg + 1)

/-- Coefficient-wise polynomial subtraction `p - q`. -/
def subCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], [] => []
  | c :: cs, [] => c :: subCoeffs cs []
  | [], d :: ds => CommRingOps.neg d :: subCoeffs [] ds
  | c :: cs, d :: ds => CommRingOps.sub c d :: subCoeffs cs ds

def sub {R : Type} [CommRingOps R] (p q : RoundPoly R) : RoundPoly R :=
  ⟨subCoeffs p.coeffs q.coeffs⟩

theorem subCoeffs_length :
    ∀ {R : Type} [CommRingOps R] (cs ds : List R),
      (subCoeffs cs ds).length = Nat.max cs.length ds.length
  | _, _, [], [] => by simp [subCoeffs]
  | _, _, _ :: cs, [] => by simp [subCoeffs, subCoeffs_length cs []]
  | _, _, [], _ :: ds => by simp [subCoeffs, subCoeffs_length [] ds]
  | _, _, _ :: cs, _ :: ds => by
    simp [subCoeffs, subCoeffs_length cs ds, Nat.succ_max_succ]

theorem evalCoeffs_sub {R : Type} [LawfulCommRing R] :
    ∀ (cs ds : List R) (x : R),
      evalCoeffs (subCoeffs cs ds) x = CommRingOps.sub (evalCoeffs cs x) (evalCoeffs ds x)
  | [], [], _ => by
    simp [subCoeffs, evalCoeffs, LawfulCommRing.sub_self]
  | c :: cs, [], x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub cs [] x]
    rw [LawfulCommRing.sub_zero, LawfulCommRing.sub_zero]
  | [], d :: ds, x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub [] ds x]
    rw [LawfulCommRing.sub_eq_add_neg CommRingOps.zero (evalCoeffs ds x),
        LawfulCommRing.zero_add, LawfulCommRing.mul_neg,
        LawfulCommRing.sub_eq_add_neg CommRingOps.zero _,
        LawfulCommRing.zero_add]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add d (CommRingOps.mul x (evalCoeffs ds x)))
    rw [LawfulCommRing.add_right_neg,
        LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_zero]
  | c :: cs, d :: ds, x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub cs ds x]
    rw [LawfulCommRing.mul_sub]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add d (CommRingOps.mul x (evalCoeffs ds x)))
    rw [LawfulCommRing.add_sub_cancel_left]
    rw [LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_sub_cancel_left]

theorem eval_sub {R : Type} [LawfulCommRing R] (p q : RoundPoly R) (x : R) :
    (sub p q).eval x = CommRingOps.sub (p.eval x) (q.eval x) :=
  evalCoeffs_sub p.coeffs q.coeffs x

theorem eval_linear_zero {R : Type} [LawfulCommRing R] (c₀ c₁ : R) :
    eval ⟨[c₀, c₁]⟩ CommRingOps.zero = c₀ := by
  simp [eval, evalCoeffs, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

theorem eval_linear_one {R : Type} [LawfulCommRing R] (c₀ c₁ : R) :
    eval ⟨[c₀, c₁]⟩ CommRingOps.one = CommRingOps.add c₀ c₁ := by
  simp [eval, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.one_mul]

theorem eval_linear {R : Type} [LawfulCommRing R] (c₀ c₁ r : R) :
    eval ⟨[c₀, c₁]⟩ r = CommRingOps.add c₀ (CommRingOps.mul r c₁) := by
  simp [eval, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-- Monic synthetic linear division quotient `(p(X) - p(r)) / (X - r)` in ANY `CommRingOps R`. -/
def quotLinear {R : Type} [CommRingOps R] : List R → R → List R
  | [], _ => []
  | [_], _ => []
  | _ :: c₁ :: cs, r => evalCoeffs (c₁ :: cs) r :: quotLinear (c₁ :: cs) r

theorem quotLinear_length {R : Type} [CommRingOps R] :
    ∀ (cs : List R) (r : R), (quotLinear cs r).length = cs.length - 1
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: c₁ :: cs, r => by
    simp only [quotLinear, List.length_cons, quotLinear_length (c₁ :: cs) r]
    simp

/-- **Factor Theorem Identity (`evalCoeffs_eq_mul_quotLinear_add`)**:
    $p(x) = (x - r) \cdot q(x) + p(r)$ in every `LawfulCommRing R`. -/
theorem evalCoeffs_eq_mul_quotLinear_add {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r x : R),
      evalCoeffs cs x =
        CommRingOps.add
          (CommRingOps.mul (CommRingOps.sub x r) (evalCoeffs (quotLinear cs r) x))
          (evalCoeffs cs r)
  | [], r, x => by
    simp [quotLinear, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | [c₀], r, x => by
    simp [quotLinear, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
  | c₀ :: c₁ :: cs, r, x => by
    let tl := c₁ :: cs
    have ih := evalCoeffs_eq_mul_quotLinear_add tl r x
    change CommRingOps.add c₀ (CommRingOps.mul x (evalCoeffs tl x)) =
      CommRingOps.add
        (CommRingOps.mul (CommRingOps.sub x r)
          (CommRingOps.add (evalCoeffs tl r) (CommRingOps.mul x (evalCoeffs (quotLinear tl r) x))))
        (CommRingOps.add c₀ (CommRingOps.mul r (evalCoeffs tl r)))
    rw [ih]
    rw [LawfulCommRing.left_distrib x,
        LawfulCommRing.left_distrib (CommRingOps.sub x r),
        LawfulCommRing.sub_mul x r (evalCoeffs tl r)]
    have hcommX : CommRingOps.mul (CommRingOps.sub x r)
        (CommRingOps.mul x (evalCoeffs (quotLinear tl r) x)) =
        CommRingOps.mul x
          (CommRingOps.mul (CommRingOps.sub x r) (evalCoeffs (quotLinear tl r) x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (CommRingOps.sub x r) x,
          LawfulCommRing.mul_assoc]
    rw [hcommX]
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul r (evalCoeffs tl r))
    let A := CommRingOps.mul r (evalCoeffs tl r)
    let B := CommRingOps.mul x (evalCoeffs tl r)
    let C := CommRingOps.mul x (CommRingOps.mul (CommRingOps.sub x r) (evalCoeffs (quotLinear tl r) x))
    change CommRingOps.add A (CommRingOps.add c₀ (CommRingOps.add C B)) =
      CommRingOps.add A (CommRingOps.add (CommRingOps.add (CommRingOps.sub B A) C) (CommRingOps.add c₀ A))
    rw [← LawfulCommRing.add_assoc A (CommRingOps.add (CommRingOps.sub B A) C) (CommRingOps.add c₀ A),
        ← LawfulCommRing.add_assoc A (CommRingOps.sub B A) C,
        LawfulCommRing.add_sub_cancel_left A B]
    rw [LawfulCommRing.add_comm C B,
        LawfulCommRing.add_comm c₀ A,
        ← LawfulCommRing.add_assoc A c₀ (CommRingOps.add B C),
        LawfulCommRing.add_comm A c₀,
        LawfulCommRing.add_assoc c₀ A (CommRingOps.add B C),
        ← LawfulCommRing.add_assoc c₀ A (CommRingOps.add B C),
        LawfulCommRing.add_comm (CommRingOps.add c₀ A) (CommRingOps.add B C)]

private theorem filter_length_le_of_imp {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl 0
  | x :: xs, himp => by
    simp only [List.filter]
    have ih := filter_length_le_of_imp xs (fun y hy => himp y (.tail _ hy))
    cases hp : p x
    · cases hq : q x <;> simp only [List.length_cons] <;> omega
    · have hq : q x = true := himp x (.head _) hp
      simp only [hq, List.length_cons]
      omega

private theorem mem_of_mem_filter_local {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → x ∈ l
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h
    split at h
    · cases h with
      | head => exact .head _
      | tail _ hm => exact .tail _ (mem_of_mem_filter_local hm)
    · exact .tail _ (mem_of_mem_filter_local h)

private theorem pred_of_mem_filter_local {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → p x = true
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h
    split at h
    · rename_i hpx
      cases h with
      | head => exact hpx
      | tail _ hm => exact pred_of_mem_filter_local hm
    · exact pred_of_mem_filter_local h

private theorem nodup_filter_local {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | _ :: _, .cons hrel htail => by
    simp only [List.filter]
    split
    · exact .cons (fun b hb => hrel b (mem_of_mem_filter_local hb)) (nodup_filter_local p htail)
    · exact nodup_filter_local p htail

private theorem filter_eq_self_of_forall {α : Type} {p : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = true) → xs.filter p = xs
  | [], _ => rfl
  | y :: ys, h => by
    have hy := h y (.head _)
    simp only [List.filter, hy]
    exact congrArg (y :: ·) (filter_eq_self_of_forall (fun z hz => h z (.tail _ hz)))

/-- **Lagrange / Factor-Theorem Root-Counting Bound (`roots_nodup_length_le`)**:
    Over every `LawfulCommRing R` without zero divisors (including both `Goldilocks` and
    128-bit `GoldilocksExt2`), any non-identically-zero polynomial of formal degree $\le d$
    has **at most `d` roots** in any duplicate-free challenge list `S : List R`. -/
theorem roots_nodup_length_le
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R] :
    ∀ (d : Nat) (cs : List R) (S : List R),
      S.Nodup →
      cs.length ≤ d + 1 →
      (∃ x₀ : R, evalCoeffs cs x₀ ≠ CommRingOps.zero) →
      (S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero))).length ≤ d
  | 0, cs, S, _, hlen, ⟨x₀, hx₀⟩ => by
    have hempty : S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) = [] := by
      cases hfilt : S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) with
      | nil => rfl
      | cons r rs =>
        exfalso
        have hpred := pred_of_mem_filter_local (p := fun r => decide (evalCoeffs cs r = CommRingOps.zero))
          (l := S) (x := r) (by rw [hfilt]; exact .head _)
        rw [decide_eq_true_eq] at hpred
        cases cs with
        | nil => exact hx₀ rfl
        | cons c₀ tl =>
          cases tl with
          | nil =>
            simp only [evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hpred hx₀
            exact hx₀ hpred
          | cons _ _ =>
            simp only [List.length_cons] at hlen
            omega
    rw [hempty]
    exact Nat.le_refl 0
  | d + 1, cs, S, hNodup, hlen, ⟨x₀, hx₀⟩ => by
    have hndRoots : (S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero))).Nodup :=
      nodup_filter_local _ hNodup
    cases hRoots : S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) with
    | nil => simp
    | cons r rest =>
      rw [hRoots] at hndRoots
      cases hndRoots with
      | cons hNotMem hndRest =>
        have hrRoot : evalCoeffs cs r = CommRingOps.zero := by
          have hp := pred_of_mem_filter_local
            (p := fun r => decide (evalCoeffs cs r = CommRingOps.zero))
            (l := S) (x := r) (by rw [hRoots]; exact .head _)
          exact of_decide_eq_true hp
        let qcs := quotLinear cs r
        have hqLen : qcs.length ≤ d + 1 := by
          dsimp [qcs]; rw [quotLinear_length]; omega
        have hqNonzero : ∃ x₁ : R, evalCoeffs qcs x₁ ≠ CommRingOps.zero := by
          refine ⟨x₀, fun hq0 => hx₀ ?_⟩
          rw [evalCoeffs_eq_mul_quotLinear_add cs r x₀, hq0, hrRoot,
              LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
        have hSubRest : ∀ y ∈ rest, decide (evalCoeffs qcs y = CommRingOps.zero) = true := by
          intro y hy
          have hyInFilt : y ∈ S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) := by
            rw [hRoots]; exact .tail _ hy
          have hyRoot : evalCoeffs cs y = CommRingOps.zero :=
            of_decide_eq_true
              (pred_of_mem_filter_local (p := fun r => decide (evalCoeffs cs r = CommRingOps.zero)) hyInFilt)
          have hyNeR : y ≠ r := fun heq => hNotMem y hy heq.symm
          have hSubNe : CommRingOps.sub y r ≠ CommRingOps.zero := by
            intro hsub0
            have h1 := congrArg (fun z => CommRingOps.add z r) hsub0
            rw [LawfulCommRing.zero_add, LawfulCommRing.sub_eq_add_neg,
                LawfulCommRing.add_assoc, LawfulCommRing.add_left_neg,
                LawfulCommRing.add_zero] at h1
            exact hyNeR h1
          have hfac := evalCoeffs_eq_mul_quotLinear_add cs r y
          rw [hyRoot, hrRoot, LawfulCommRing.add_zero] at hfac
          rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hfac.symm with hbad | hqy0
          · exact False.elim (hSubNe hbad)
          · exact decide_eq_true hqy0
        have hRestEq : rest.filter (fun y => decide (evalCoeffs qcs y = CommRingOps.zero)) = rest :=
          filter_eq_self_of_forall hSubRest
        have ih := roots_nodup_length_le d qcs rest hndRest hqLen hqNonzero
        rw [hRestEq] at ih
        simp only [List.length_cons]
        omega

end RoundPoly

/-! ## 4. Sumcheck Evaluation Claim, Seeded & Instance-Bound Verifiers -/

/-- Final evaluation claim reduced by a $v$-round Sumcheck execution:
    asserts $\tilde{g}(\text{point}) = \text{expectedVal}$ with `point.length = numVars`. -/
structure EvalClaim (R : Type) (numVars : Nat) where
  point : List R
  point_len : point.length = numVars
  expectedVal : R
  deriving DecidableEq, Repr

/-- `"SUMCHECK.ROUND"` domain label bytes. -/
def sumcheckRoundLabel : ByteArray :=
  Native.bytesOfList [0x53, 0x55, 0x4d, 0x43, 0x48, 0x45, 0x43, 0x4b,
                      0x2e, 0x52, 0x4f, 0x55, 0x4e, 0x44]

/-- Serialize a `RoundPoly R` as length-prefixed canonical element bytes. -/
def encodeRoundPoly {R : Type} [TranscriptChallenge R] (p : RoundPoly R) : ByteArray :=
  Native.bytesOfList
    (leb128 p.coeffs.length ++
      (p.coeffs.flatMap fun c => encodeListField (TranscriptChallenge.encodeElem c).data.toList))

/-- Absorb a round polynomial into a seeded transcript and squeeze challenge `r`. -/
def absorbAndSqueezeRound {R : Type} [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (p : RoundPoly R) (tr : Transcript phase) : R × Transcript phase :=
  let trAbs := absorbMsg sumcheckRoundLabel (encodeRoundPoly p) tr
  TranscriptChallenge.squeezeChallenge trAbs

/-- Verify one Sumcheck round: checks `deg(p) ≤ maxDeg` and `p(0) + p(1) = claimedSum`,
    absorbs `p` into the seeded transcript, squeezes `r`, and outputs `(r, p(r), tr')`. -/
def verifySumcheckRound {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (maxDeg : Nat) (claimedSum : R) (p : RoundPoly R) (tr : Transcript phase) :
    Option (R × R × Transcript phase) :=
  if p.degLe maxDeg &&
     decide (CommRingOps.add (p.eval CommRingOps.zero) (p.eval CommRingOps.one) = claimedSum) then
    let (r, tr') := absorbAndSqueezeRound p tr
    some (r, p.eval r, tr')
  else
    none

/-- **Complete Fiat–Shamir Sumcheck Verifier (`verifySumcheck`)**:
    Reduces $\sum_{\mathbf{x} \in \{0,1\}^{\text{numVars}}} g(\mathbf{x}) = \text{claimedSum}$
    over `Transcript phase` (`[CanSqueezeTranscript phase]`) to `EvalClaim R numVars`. -/
def verifySumcheck {R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (maxDeg : Nat) :
    (numVars : Nat) → (claimedSum : R) → (rounds : List (RoundPoly R)) →
    Transcript phase → Option (EvalClaim R numVars × Transcript phase)
  | 0, claimedSum, [], tr =>
    some (⟨[], rfl, claimedSum⟩, tr)
  | v + 1, claimedSum, p :: ps, tr =>
    match verifySumcheckRound maxDeg claimedSum p tr with
    | none => none
    | some (r, nextClaim, tr') =>
      match verifySumcheck maxDeg v nextClaim ps tr' with
      | none => none
      | some (subClaim, trFinal) =>
        some (⟨r :: subClaim.point, congrArg Nat.succ subClaim.point_len, subClaim.expectedVal⟩,
              trFinal)
  | _, _, _, _ => none

/-- **Instance-Bound Sumcheck Verifier (`verifyBoundSumcheck`)**:
    Accepts ONLY a `BoundTranscript inst` produced by `bindInstance (comm, numVars, claimedSum) tr`,
    reading `(comm, numVars, claimedSum)` directly from `btr.inst` so `(comm, claimedSum)` is guaranteed
    to have been absorbed into `.instanceBound` BEFORE any round challenge is squeezed. -/
def verifyBoundSumcheck {Commit R : Type} [CommRingOps R] [DecidableEq R] [TranscriptChallenge R]
    {inst : Commit × Nat × R} (maxDeg : Nat) (btr : BoundTranscript inst)
    (rounds : List (RoundPoly R)) :
    Option (Commit × EvalClaim R inst.2.1 × Transcript .instanceBound) :=
  match verifySumcheck maxDeg inst.2.1 inst.2.2 rounds btr.transcript with
  | none => none
  | some (claim, trOut) => some (inst.1, claim, trOut)

/-! ## 5. Honest Multilinear Sumcheck Prover & Completeness -/

/-- Honest degree-1 round polynomial $p^*(X) = s_0 + (s_1 - s_0) X$ for `v + 1` variables. -/
def honestRoundPoly {R : Type} [CommRingOps R] (v : Nat) (tbl : List R) : RoundPoly R :=
  let s₀ := hypercubeSum v (foldFirstVar tbl CommRingOps.zero)
  let s₁ := hypercubeSum v (foldFirstVar tbl CommRingOps.one)
  ⟨[s₀, CommRingOps.sub s₁ s₀]⟩

theorem honestRoundPoly_sum {R : Type} [LawfulCommRing R] (v : Nat) (tbl : List R) :
    CommRingOps.add ((honestRoundPoly v tbl).eval CommRingOps.zero)
                    ((honestRoundPoly v tbl).eval CommRingOps.one) =
      hypercubeSum (v + 1) tbl := by
  unfold honestRoundPoly
  rw [RoundPoly.eval_linear_zero, RoundPoly.eval_linear_one,
      LawfulCommRing.add_sub_cancel_left, hypercubeSum_succ]

theorem honestRoundPoly_eval {R : Type} [LawfulCommRing R] (v : Nat) (tbl : List R) (r : R) :
    (honestRoundPoly v tbl).eval r = hypercubeSum v (foldFirstVar tbl r) := by
  unfold honestRoundPoly
  rw [RoundPoly.eval_linear]
  exact (hypercubeSum_foldFirstVar v tbl r).symm

/-- Honest Fiat–Shamir Sumcheck prover folding `tbl` round-by-round via `foldFirstVar`. -/
def honestSumcheckProver {R : Type} [CommRingOps R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    (numVars : Nat) → List R → Transcript phase →
    List (RoundPoly R) × EvalClaim R numVars × Transcript phase
  | 0, tbl, tr =>
    ([], ⟨[], rfl, mleEval tbl []⟩, tr)
  | v + 1, tbl, tr =>
    let p := honestRoundPoly v tbl
    let (r, tr') := absorbAndSqueezeRound p tr
    let tbl' := foldFirstVar tbl r
    let (restPolys, subClaim, trFinal) := honestSumcheckProver v tbl' tr'
    (p :: restPolys,
     ⟨r :: subClaim.point, congrArg Nat.succ subClaim.point_len, subClaim.expectedVal⟩,
     trFinal)

/-- Honest instance-bound Sumcheck prover: binds `(comm, v, hypercubeSum v tbl)` into `.instanceBound`
    via `bindInstance` before generating round polynomials. -/
def honestBoundSumcheckProver {Commit R : Type} [CommRingOps R] [TranscriptChallenge R]
    [TranscriptEncode Commit] [TranscriptEncode R]
    (comm : Commit) (v : Nat) (tbl : List R) (tr : Transcript .relationBound) :
    List (RoundPoly R) × EvalClaim R v × Transcript .instanceBound :=
  let btr := bindInstance (comm, (v, hypercubeSum v tbl)) tr
  honestSumcheckProver v tbl btr.transcript

/-- Single-round completeness witness for `verifySumcheckRound`: honest linear round polynomials
    are accepted for every `maxDeg ≥ 1`. -/
theorem verifySumcheckRound_complete
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    {maxDeg : Nat} (v : Nat) (tbl : List R)
    (tr : Transcript phase) :
    1 ≤ maxDeg →
    verifySumcheckRound (R := R) (phase := phase) maxDeg (hypercubeSum (v + 1) tbl)
      (honestRoundPoly v tbl) tr =
      some ((absorbAndSqueezeRound (phase := phase) (honestRoundPoly v tbl) tr).1,
            hypercubeSum v (foldFirstVar tbl (absorbAndSqueezeRound (phase := phase) (honestRoundPoly v tbl) tr).1),
            (absorbAndSqueezeRound (phase := phase) (honestRoundPoly v tbl) tr).2) := by
  intro hDeg
  unfold verifySumcheckRound
  have hLen : (honestRoundPoly v tbl).degLe maxDeg = true := by
    unfold RoundPoly.degLe honestRoundPoly
    rw [decide_eq_true_eq]
    simp only [List.length_cons, List.length_nil]
    omega
  have hSum : decide (CommRingOps.add ((honestRoundPoly v tbl).eval CommRingOps.zero)
      ((honestRoundPoly v tbl).eval CommRingOps.one) =
      hypercubeSum (v + 1) tbl) = true := by
    rw [decide_eq_true_eq]
    exact honestRoundPoly_sum v tbl
  rw [hLen, hSum]
  simp only [Bool.true_and, ↓reduceIte, honestRoundPoly_eval]

/-- **Honest Sumcheck Prover Completeness (`honestSumcheckProver_completeness`)**:
    For every `maxDeg ≥ 1`, variable count `v`, table `tbl`, and seeded transcript `tr`,
    `honestSumcheckProver` produces a proof accepted by `verifySumcheck` whose final
    `EvalClaim` equals the true multilinear evaluation `mleEval tbl claim.point`. -/
theorem honestSumcheckProver_completeness
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    {maxDeg : Nat} (hDeg : 1 ≤ maxDeg) :
    ∀ (v : Nat) (tbl : List R) (tr : Transcript phase),
      let (rounds, claim, trOut) := honestSumcheckProver (phase := phase) v tbl tr
      verifySumcheck (R := R) (phase := phase) maxDeg v (hypercubeSum v tbl) rounds tr = some (claim, trOut) ∧
      claim.expectedVal = mleEval tbl claim.point
  | 0, tbl, tr => by
    simp [honestSumcheckProver, verifySumcheck, hypercubeSum_zero]
  | v + 1, tbl, tr => by
    dsimp only [honestSumcheckProver]
    have hRound := verifySumcheckRound_complete v tbl tr hDeg
    obtain ⟨ihVer, ihEval⟩ :=
      honestSumcheckProver_completeness hDeg v
        (foldFirstVar tbl (absorbAndSqueezeRound (honestRoundPoly v tbl) tr).1)
        (absorbAndSqueezeRound (honestRoundPoly v tbl) tr).2
    refine ⟨?_, ?_⟩
    · simp only [verifySumcheck, hRound, ihVer]
    · rw [ihEval, mleEval_foldFirstVar]

/-- Completeness of instance-bound `verifyBoundSumcheck`. -/
theorem verifyBoundSumcheck_completeness
    {Commit R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    [TranscriptEncode Commit] [TranscriptEncode R]
    {maxDeg : Nat} (hDeg : 1 ≤ maxDeg)
    (comm : Commit) (v : Nat) (tbl : List R) (tr : Transcript .relationBound) :
    let (rounds, claim, trOut) := honestBoundSumcheckProver (Commit := Commit) (R := R) comm v tbl tr
    verifyBoundSumcheck (Commit := Commit) (R := R) maxDeg
      (bindInstance (comm, (v, hypercubeSum v tbl)) tr) rounds =
      some (comm, claim, trOut) ∧
    claim.expectedVal = mleEval tbl claim.point := by
  dsimp only [verifyBoundSumcheck, honestBoundSumcheckProver, BoundTranscript.inst]
  obtain ⟨hVer, hVal⟩ := honestSumcheckProver_completeness hDeg v tbl
    (bindInstance (comm, (v, hypercubeSum v tbl)) tr).transcript
  exact ⟨by rw [hVer], hVal⟩

/-! ## 6. Round-by-Round, Multi-Round LFKN & 128-Bit $\mathbb{F}_{p^2}$ Quantitative Soundness -/

/-- Witness that Fiat–Shamir challenge `r` hit a root of a non-identically-zero round
    discrepancy polynomial `diff = p - p^*` (`diff(r) = 0` while `diff(0) ≠ 0 ∨ diff(1) ≠ 0`). -/
def RoundDiscrepancyRootHit {R : Type} [CommRingOps R] (p pStar : RoundPoly R) (r : R) : Prop :=
  (p.sub pStar).eval r = CommRingOps.zero ∧
  ((p.sub pStar).eval CommRingOps.zero ≠ CommRingOps.zero ∨
   (p.sub pStar).eval CommRingOps.one ≠ CommRingOps.zero)

theorem eq_of_sub_eq_zero {R : Type} [LawfulCommRing R] {a b : R}
    (h : CommRingOps.sub a b = CommRingOps.zero) : a = b := by
  have h1 := congrArg (fun z => CommRingOps.add z b) h
  rw [LawfulCommRing.zero_add, LawfulCommRing.sub_eq_add_neg,
      LawfulCommRing.add_assoc, LawfulCommRing.add_left_neg, LawfulCommRing.add_zero] at h1
  exact h1

/-- **Single-Round Sumcheck Soundness (`verifySumcheck_round_sound`)**:
    If `verifySumcheckRound` accepts `p` on a false `claimedSum ≠ hypercubeSum (v + 1) tbl`,
    then `deg(p) ≤ maxDeg`, `p(0) + p(1) = claimedSum`, and **either** the next-round claim
    `nextClaim` remains false for the folded table `foldFirstVar tbl r`, **or** challenge `r`
    hit an exact algebraic root of the non-zero discrepancy polynomial `p - honestRoundPoly v tbl`. -/
theorem verifySumcheck_round_sound
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    {maxDeg v : Nat} {claimedSum : R} {p : RoundPoly R} {tr : Transcript phase}
    {r nextClaim : R} {tr' : Transcript phase}
    (tbl : List R)
    (hAcc : verifySumcheckRound maxDeg claimedSum p tr = some (r, nextClaim, tr'))
    (hFalse : claimedSum ≠ hypercubeSum (v + 1) tbl) :
    p.coeffs.length ≤ maxDeg + 1 ∧
    CommRingOps.add (p.eval CommRingOps.zero) (p.eval CommRingOps.one) = claimedSum ∧
    tr' = (absorbAndSqueezeRound (phase := phase) p tr).2 ∧
    (nextClaim ≠ hypercubeSum v (foldFirstVar tbl r) ∨
     RoundDiscrepancyRootHit (R := R) p (honestRoundPoly v tbl) r) := by
  unfold verifySumcheckRound at hAcc
  split at hAcc
  · rename_i hCond
    simp only [Bool.and_eq_true, RoundPoly.degLe, decide_eq_true_eq] at hCond
    simp only [Option.some.injEq, Prod.mk.injEq] at hAcc
    rcases hAcc with ⟨hr, hNext, hTr⟩
    subst hr hNext
    refine ⟨hCond.1, hCond.2, hTr.symm, ?_⟩
    let pStar := honestRoundPoly v tbl
    let ch := (absorbAndSqueezeRound p tr).1
    if hAgree : p.eval ch = hypercubeSum v (foldFirstVar tbl ch) then
      right
      have hAgreePoly : p.eval ch = pStar.eval ch := by
        rw [hAgree]; exact (honestRoundPoly_eval v tbl ch).symm
      have hRoot : (p.sub pStar).eval ch = CommRingOps.zero := by
        rw [RoundPoly.eval_sub, hAgreePoly, LawfulCommRing.sub_self]
      refine ⟨hRoot, ?_⟩
      if h0 : (p.sub pStar).eval CommRingOps.zero = CommRingOps.zero then
        right
        intro h1
        have eq0 : p.eval CommRingOps.zero = pStar.eval CommRingOps.zero := by
          rw [RoundPoly.eval_sub] at h0
          exact eq_of_sub_eq_zero h0
        have eq1 : p.eval CommRingOps.one = pStar.eval CommRingOps.one := by
          rw [RoundPoly.eval_sub] at h1
          exact eq_of_sub_eq_zero h1
        have hEqSum : claimedSum = hypercubeSum (v + 1) tbl := by
          rw [← hCond.2, eq0, eq1]
          exact honestRoundPoly_sum v tbl
        exact hFalse hEqSum
      else
        exact .inl h0
    else
      exact .inl hAgree
  · cases hAcc

/-- **Quantitative Bad-Challenge Bound per Sumcheck Round (`roundDiscrepancy_bad_challenge_count_le`)**:
    Over any integral domain `R` (`NoZeroDivisors R`, instantiated for both `Goldilocks` and
    128-bit `GoldilocksExt2`), for any false round claim `claimedSum ≠ hypercubeSum (v + 1) tbl`,
    any degree-`≤ maxDeg` prover polynomial `p` (`1 ≤ maxDeg`, `p(0) + p(1) = claimedSum`), and
    any duplicate-free challenge set `S : List R` (up to all $p^2 > 2^{127}$ elements of $\mathbb{F}_{p^2}$),
    **at most `maxDeg` challenges** in `S` make `p(r) = hypercubeSum v (foldFirstVar tbl r)`! -/
theorem roundDiscrepancy_bad_challenge_count_le
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R]
    {maxDeg v : Nat} (hDeg : 1 ≤ maxDeg)
    (tbl : List R) (claimedSum : R) (p : RoundPoly R) (S : List R)
    (hNodup : S.Nodup)
    (hPolyDeg : p.degLe maxDeg = true)
    (hSumEq : CommRingOps.add (p.eval CommRingOps.zero) (p.eval CommRingOps.one) = claimedSum)
    (hFalse : claimedSum ≠ hypercubeSum (v + 1) tbl) :
    (S.filter (fun r => decide (p.eval r = hypercubeSum v (foldFirstVar tbl r)))).length ≤ maxDeg := by
  let pStar := honestRoundPoly v tbl
  let diff := p.sub pStar
  have hDiffLen : diff.coeffs.length ≤ maxDeg + 1 := by
    dsimp [diff, RoundPoly.sub, pStar, honestRoundPoly]
    rw [RoundPoly.subCoeffs_length, Nat.max_le]
    rw [RoundPoly.degLe, decide_eq_true_eq] at hPolyDeg
    simp only [List.length_cons, List.length_nil]
    omega
  have hDiffNonzero : ∃ x₀ : R, RoundPoly.evalCoeffs diff.coeffs x₀ ≠ CommRingOps.zero := by
    if h0 : diff.eval CommRingOps.zero = CommRingOps.zero then
      refine ⟨CommRingOps.one, fun h1 => hFalse ?_⟩
      have eq0 : p.eval CommRingOps.zero = pStar.eval CommRingOps.zero :=
        eq_of_sub_eq_zero ((RoundPoly.eval_sub p pStar CommRingOps.zero) ▸ h0)
      have eq1 : p.eval CommRingOps.one = pStar.eval CommRingOps.one :=
        eq_of_sub_eq_zero ((RoundPoly.eval_sub p pStar CommRingOps.one) ▸ h1)
      rw [← hSumEq, eq0, eq1]
      exact honestRoundPoly_sum v tbl
    else
      exact ⟨CommRingOps.zero, h0⟩
  have hFilterEq :
      S.filter (fun r => decide (p.eval r = hypercubeSum v (foldFirstVar tbl r))) =
      S.filter (fun r => decide (RoundPoly.evalCoeffs diff.coeffs r = CommRingOps.zero)) := by
    apply List.filter_congr
    intro r _
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    constructor
    · intro hr
      change diff.eval r = CommRingOps.zero
      rw [RoundPoly.eval_sub, hr, ← honestRoundPoly_eval v tbl r, LawfulCommRing.sub_self]
    · intro hr
      have hsub : CommRingOps.sub (p.eval r) (pStar.eval r) = CommRingOps.zero := by
        rw [← RoundPoly.eval_sub]; exact hr
      rw [eq_of_sub_eq_zero hsub, honestRoundPoly_eval]
  rw [hFilterEq]
  exact RoundPoly.roots_nodup_length_le maxDeg diff.coeffs S hNodup hDiffLen hDiffNonzero

/-- **128-Bit `GoldilocksExt2` Rational Soundness Error Bound (`goldilocksExt2_round_soundness_err`)**:
    Over `GoldilocksExt2` ($\mathbb{F}_{p^2}$), the fraction of accepting bad challenges in any
    `Nodup` challenge set `S` satisfies `ratLe (badCount, goldilocksPrime ^ 2) (maxDeg, goldilocksPrime ^ 2)`
    with denominator `goldilocksPrime ^ 2 > 2 ^ 127`. -/
theorem goldilocksExt2_round_soundness_err
    {maxDeg v : Nat} (hDeg : 1 ≤ maxDeg)
    (tbl : List GoldilocksExt2) (claimedSum : GoldilocksExt2)
    (p : RoundPoly GoldilocksExt2) (S : List GoldilocksExt2)
    (hNodup : S.Nodup)
    (hPolyDeg : p.degLe maxDeg = true)
    (hSumEq : CommRingOps.add (p.eval CommRingOps.zero) (p.eval CommRingOps.one) = claimedSum)
    (hFalse : claimedSum ≠ hypercubeSum (v + 1) tbl) :
    ratLe
      ((S.filter (fun r => decide (p.eval r = hypercubeSum v (foldFirstVar tbl r)))).length,
       goldilocksPrime ^ 2)
      (maxDeg, goldilocksPrime ^ 2) ∧
    2 ^ 127 < goldilocksPrime ^ 2 := by
  refine ⟨?_, goldilocksExt2_card_gt_two_pow_126 127 (Nat.le_refl 127)⟩
  unfold ratLe
  exact Nat.mul_le_mul_right (goldilocksPrime ^ 2)
    (roundDiscrepancy_bad_challenge_count_le hDeg tbl claimedSum p S hNodup hPolyDeg hSumEq hFalse)

/-- Inductive predicate witnessing that at least one Sumcheck round encountered a
    Fiat–Shamir challenge landing on a root of a non-zero bounded-degree discrepancy polynomial. -/
def ExistsRoundRootHit {R : Type} [CommRingOps R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase] :
    (numVars : Nat) → List R → List (RoundPoly R) → Transcript phase → Prop
  | 0, _, _, _ => False
  | _ + 1, _, [], _ => False
  | v + 1, tbl, p :: ps, tr =>
    let (r, tr') := absorbAndSqueezeRound p tr
    RoundDiscrepancyRootHit p (honestRoundPoly v tbl) r ∨
    ExistsRoundRootHit v (foldFirstVar tbl r) ps tr'

/-- **Multi-Round LFKN Sumcheck Soundness Dichotomy (`verifySumcheck_sound_dichotomy`)**:
    Whenever `verifySumcheck` accepts a proof `rounds` for a false hypercube sum
    `claimedSum ≠ hypercubeSum v tbl`, **either** the final evaluation claim is false
    (`claim.expectedVal ≠ mleEval tbl claim.point`), **or** at least one Fiat–Shamir
    round challenge hit an algebraic root of a non-zero degree-`≤ maxDeg` discrepancy polynomial. -/
theorem verifySumcheck_sound_dichotomy
    {R : Type} [LawfulCommRing R] [DecidableEq R] [TranscriptChallenge R]
    {phase : TranscriptPhase} [CanSqueezeTranscript phase]
    (maxDeg : Nat) :
    ∀ (v : Nat) (tbl : List R) (claimedSum : R) (rounds : List (RoundPoly R))
      (tr : Transcript phase) (claim : EvalClaim R v) (trFinal : Transcript phase),
      verifySumcheck maxDeg v claimedSum rounds tr = some (claim, trFinal) →
      claimedSum ≠ hypercubeSum v tbl →
      claim.expectedVal ≠ mleEval tbl claim.point ∨
      ExistsRoundRootHit v tbl rounds tr
  | 0, tbl, claimedSum, [], _, claim, _, hVer, hFalse => by
    simp only [verifySumcheck, Option.some.injEq, Prod.mk.injEq] at hVer
    rcases hVer with ⟨rfl, rfl⟩
    left
    simpa [hypercubeSum_zero] using hFalse
  | 0, _, _, _ :: _, _, _, _, hVer, _ => by
    cases hVer
  | _ + 1, _, _, [], _, _, _, hVer, _ => by
    cases hVer
  | v + 1, tbl, claimedSum, p :: ps, tr, claim, trFinal, hVer, hFalse => by
    simp only [verifySumcheck] at hVer
    cases hRound : verifySumcheckRound maxDeg claimedSum p tr with
    | none => rw [hRound] at hVer; cases hVer
    | some stepOut =>
      rcases stepOut with ⟨r, nextClaim, tr'⟩
      rw [hRound] at hVer
      dsimp only at hVer
      cases hRec : verifySumcheck maxDeg v nextClaim ps tr' with
      | none => rw [hRec] at hVer; cases hVer
      | some recOut =>
        rcases recOut with ⟨subClaim, trEnd⟩
        rw [hRec] at hVer
        simp only [Option.some.injEq, Prod.mk.injEq] at hVer
        rcases hVer with ⟨rfl, rfl⟩
        have hStepEq : (r, tr') = absorbAndSqueezeRound p tr := by
          unfold verifySumcheckRound at hRound
          split at hRound
          · simp only [Option.some.injEq, Prod.mk.injEq] at hRound
            exact Prod.ext hRound.1.symm hRound.2.2.symm
          · cases hRound
        obtain ⟨_, _, _, hDich⟩ := verifySumcheck_round_sound tbl hRound hFalse
        rcases hDich with hNextFalse | hHit0
        · rcases verifySumcheck_sound_dichotomy maxDeg v (foldFirstVar tbl r)
              nextClaim ps tr' subClaim trEnd hRec hNextFalse with hEvalFalse | hLaterHit
          · left
            simpa only [mleEval_foldFirstVar] using hEvalFalse
          · right
            dsimp only [ExistsRoundRootHit]
            rw [← hStepEq]
            exact .inr hLaterHit
        · right
          dsimp only [ExistsRoundRootHit]
          rw [← hStepEq]
          exact .inl hHit0

end Obend.Crypto
end
