module
public import Obend.Crypto.Multilinear
public import Obend.Tactic.Tooth

public section
namespace Obend.Crypto.Fast

/-- Exact dimensions are part of the carrier, including at dimension zero. -/
structure Sized (α : Type) (d : Nat) where
  coeffs : Array α
  size_eq : coeffs.size = d
  deriving DecidableEq

@[expose] def Sized.ofFn {α : Type} {d : Nat} (f : Fin d → α) : Sized α d :=
  ⟨Array.ofFn f, Array.size_ofFn⟩

@[expose] def Sized.spec {α : Type} {d : Nat} (a : Sized α d) (i : Fin d) : α :=
  a.coeffs[i.val]'(by have := a.size_eq; omega)

private theorem arrayOfFn_size_go {α : Type} {n : Nat} (f : Fin n → α)
    (acc : Array α) (i : Nat) (h : i ≤ n) : (Array.ofFn.go f acc i h).size = acc.size + i := by
  induction i generalizing acc with
  | zero => simp only [Array.ofFn.go, Nat.add_zero]
  | succ i ih => simp only [Array.ofFn.go, ih, Array.size_push]; omega

/-- The core getElem_ofFn proof uses classical contradiction on an arbitrary
coefficient equality. This local proof keeps contradiction in False. -/
private theorem arrayOfFn_get_go {α : Type} {n : Nat} (f : Fin n → α)
    (acc : Array α) (i k : Nat) (h : i ≤ n) (hw : k < acc.size+i) :
    (Array.ofFn.go f acc i h)[k]'(by rw [arrayOfFn_size_go]; exact hw) =
      if hk : k < acc.size then acc[k] else f ⟨n-i+k-acc.size, by omega⟩ := by
  induction i generalizing acc with
  | zero =>
    have hk : k < acc.size := by omega
    simp only [Array.ofFn.go, hk, ↓reduceDIte]
  | succ i ih =>
    simp only [Array.ofFn.go]
    rw [ih]
    · by_cases hk : k < acc.size
      · have hp : k < (acc.push (f ⟨n-i-1, by omega⟩)).size := by rw [Array.size_push]; omega
        simp only [hk, hp, ↓reduceDIte, Array.getElem_push_lt hk]
      · by_cases he : k = acc.size
        · subst k
          simp only [Array.size_push, Nat.lt_succ_self, ↓reduceDIte, Array.getElem_push_eq,
            Nat.lt_irrefl]
          congr 1
          apply Fin.ext
          dsimp
          omega
        · have hp : ¬ k < (acc.push (f ⟨n-i-1, by omega⟩)).size := by rw [Array.size_push]; omega
          simp only [hk, hp, ↓reduceDIte]
          congr 1
          apply Fin.ext
          simp only [Array.size_push]
          omega
    · simp only [Array.size_push]; omega

theorem arrayOfFn_get {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Array.ofFn f)[i.val]'(by rw [Array.size_ofFn]; exact i.isLt) = f i := by
  have h := arrayOfFn_get_go f (Array.emptyWithCapacity n) n i.val (Nat.le_refl _)
    (by simpa only [Array.emptyWithCapacity_eq, Array.size_empty, Nat.zero_add] using i.isLt)
  simpa only [Array.ofFn, Array.emptyWithCapacity_eq, Array.size_empty, Nat.not_lt_zero, ↓reduceDIte,
    Nat.sub_self, Nat.zero_add, Nat.sub_zero] using h

@[simp] theorem Sized.spec_ofFn {α : Type} {d : Nat} (f : Fin d → α) :
    (Sized.ofFn f).spec = f := by
  funext i
  exact arrayOfFn_get f i

theorem Sized.ext {α : Type} {d : Nat} {a b : Sized α d}
    (h : a.spec = b.spec) : a = b := by
  have hc : a.coeffs = b.coeffs := by
    apply Array.ext (a.size_eq.trans b.size_eq.symm)
    intro i ha hb
    exact congrFun h ⟨i, by have := a.size_eq; omega⟩
  cases a; cases b; cases hc; rfl

/-- Search a finite function extensionally, returning the differing index as data. -/
def findDifference {α : Type} [DecidableEq α] : (n : Nat) →
    (a b : Fin n → α) → a ≠ b → {i : Fin n // a i ≠ b i}
  | 0, a, b, h => False.elim (h (by funext i; exact Fin.elim0 i))
  | n+1, a, b, h =>
    if he : a ⟨n, by omega⟩ = b ⟨n, by omega⟩ then
      let smaller := findDifference n (fun i => a ⟨i.val, by omega⟩) (fun i => b ⟨i.val, by omega⟩)
        (fun hh => h (by
          funext i
          by_cases hi : i.val < n
          · exact congrFun hh ⟨i.val, hi⟩
          · have ei : i = ⟨n, by omega⟩ := by apply Fin.ext; dsimp; omega
            rw [ei]; exact he))
      ⟨⟨smaller.val.val, by have := smaller.val.isLt; omega⟩, smaller.property⟩
    else ⟨⟨n, by omega⟩, he⟩

/-- Parsing rejects a trailing coordinate rather than truncating it. -/
@[expose] def checked {α : Type} (d : Nat) (xs : Array α) : Option (Sized α d) :=
  if h : xs.size = d then some ⟨xs, h⟩ else none

theorem checked_dimension {α : Type} (d : Nat) (xs : Array α) (a : Sized α d)
    (h : checked d xs = some a) : xs.size = d := by
  unfold checked at h; split at h <;> simp_all

abbrev FastIntPoly := Sized Int
abbrev FastGoldilocksRing := Sized Goldilocks
abbrev IntCycloSpec (d : Nat) := Fin d → Int
/-- Canonical residues; q=0 has no coefficients, without an implicit modulus assumption. -/
abbrev CycloSpec (d q : Nat) := Fin d → {x : Int // 0 ≤ x ∧ x < (q : Int)}

@[expose] def sumInt : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumInt n f + f n

theorem sumInt_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumInt, sumInt, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumInt_add (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i + g i) = sumInt n f + sumInt n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumInt, ih]; omega

theorem sumInt_mul (n : Nat) (c : Int) (f : Nat → Int) :
    sumInt n (fun i => c * f i) = c * sumInt n f := by
  induction n with
  | zero => simp [sumInt]
  | succ n ih => simp [sumInt, ih, Int.mul_add]

@[expose] def intAdd {d : Nat} (a b : FastIntPoly d) : FastIntPoly d :=
  Sized.ofFn fun i => a.spec i + b.spec i
@[expose] def intSub {d : Nat} (a b : FastIntPoly d) : FastIntPoly d :=
  Sized.ofFn fun i => a.spec i - b.spec i
@[expose] def intNeg {d : Nat} (a : FastIntPoly d) : FastIntPoly d :=
  Sized.ofFn fun i => -a.spec i
@[expose] def intScale {d : Nat} (c : Int) (a : FastIntPoly d) : FastIntPoly d :=
  Sized.ofFn fun i => c * a.spec i
@[expose] def zeroVec (d : Nat) : FastIntPoly d := Sized.ofFn fun _ => 0

@[simp] theorem addFast_eq_spec {d : Nat} (a b : FastIntPoly d) :
    (intAdd a b).spec = fun i => a.spec i + b.spec i := Sized.spec_ofFn _
@[simp] theorem subFast_eq_spec {d : Nat} (a b : FastIntPoly d) :
    (intSub a b).spec = fun i => a.spec i - b.spec i := Sized.spec_ofFn _
@[simp] theorem negFast_eq_spec {d : Nat} (a : FastIntPoly d) :
    (intNeg a).spec = fun i => -a.spec i := Sized.spec_ofFn _
@[simp] theorem scaleFast_eq_spec {d : Nat} (c : Int) (a : FastIntPoly d) :
    (intScale c a).spec = fun i => c * a.spec i := Sized.spec_ofFn _

/-- The wrap coefficient is negative because X^d = -1. -/
@[expose] def wrapSign (i k : Nat) (x : Int) : Int := if i ≤ k then x else -x

@[expose] def negacyclicSpec {d : Nat} (a b : IntCycloSpec d) (k : Fin d) : Int :=
  sumInt d fun i => if hi : i < d then
    wrapSign i k.val (a ⟨i, hi⟩ * b ⟨(k.val + d - i) % d, Nat.mod_lt _ (by omega)⟩)
    else 0

/-- The executable kernel has two branch-free arithmetic loops. The wrap boundary is
hoisted out of the loops, and neither loop performs division by the degree. -/
@[expose] def splitConvolution {α : Type} (add sub mul : α → α → α) (zero : α)
    (d k : Nat) (a b : Nat → α) : α :=
  let lo := (Array.range (k+1)).foldl (fun acc j => add acc (mul (a j) (b (k-j)))) zero
  (Array.range (d-(k+1))).foldl
    (fun acc t => sub acc (mul (a (k+1+t)) (b (d-1-t)))) lo

theorem rangeFold_add (n : Nat) (f : Nat → Int) (z : Int) :
    (Array.range n).foldl (fun acc j => acc + f j) z = z + sumInt n f := by
  induction n with
  | zero => simp [Array.range_eq_range', sumInt]
  | succ n ih =>
    rw [Array.range_succ, Array.foldl_append]
    change (Array.range n).foldl (fun acc j => acc + f j) z + f n = _
    rw [ih, sumInt, Int.add_assoc]

theorem rangeFold_sub (n : Nat) (f : Nat → Int) (z : Int) :
    (Array.range n).foldl (fun acc j => acc - f j) z = z - sumInt n f := by
  induction n with
  | zero => simp [Array.range_eq_range', sumInt]
  | succ n ih =>
    rw [Array.range_succ, Array.foldl_append]
    change (Array.range n).foldl (fun acc j => acc - f j) z - f n = _
    rw [ih, sumInt]; omega

theorem sumInt_split (l h : Nat) (f : Nat → Int) :
    sumInt (l+h) f = sumInt l f + sumInt h (fun i => f (l+i)) := by
  induction h with
  | zero => simp [sumInt]
  | succ h ih =>
    change sumInt (l+h) f + f (l+h) = sumInt l f + (sumInt h (fun i => f (l+i)) + f (l+h))
    rw [ih]; omega

theorem splitConvolution_eq_spec {d : Nat} (a b : Nat → Int) (k : Fin d) :
    splitConvolution (· + ·) (· - ·) (· * ·) 0 d k.val a b =
      negacyclicSpec (fun i => a i.val) (fun i => b i.val) k := by
  unfold splitConvolution negacyclicSpec
  dsimp only
  rw [rangeFold_sub, rangeFold_add]
  have hd : d = (k.val+1) + (d-(k.val+1)) := by omega
  conv => rhs; arg 1; rw [hd]
  rw [sumInt_split (k.val+1) (d-(k.val+1))]
  simp only [Int.zero_add]
  have hlo : ∀ i, i < k.val+1 →
      (if hi : i < d then wrapSign i k.val
        (a i * b ((k.val+d-i)%d)) else 0) = a i * b (k.val-i) := by
    intro i hi
    have him : i < d := by omega
    have hmod : (k.val+d-i)%d = k.val-i := by
      have he : k.val+d-i = (k.val-i)+d := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [him, wrapSign, show i ≤ k.val by omega, hmod]
  have hhi : ∀ t, t < d-(k.val+1) →
      (if hi : k.val+1+t < d then wrapSign (k.val+1+t) k.val
        (a (k.val+1+t) * b ((k.val+d-(k.val+1+t))%d)) else 0) =
          -(a (k.val+1+t) * b (d-1-t)) := by
    intro t ht
    have him : k.val+1+t < d := by omega
    have he : k.val+d-(k.val+1+t) = d-1-t := by omega
    simp [him, wrapSign, show ¬ k.val+1+t ≤ k.val by omega, he,
      Nat.mod_eq_of_lt (show d-1-t < d by omega)]
  rw [sumInt_congr hlo, sumInt_congr hhi]
  have hn := sumInt_mul (d-(k.val+1)) (-1) (fun t => a (k.val+1+t)*b (d-1-t))
  simp only [Int.neg_one_mul] at hn
  rw [hn]; omega

@[expose] def negacyclicMulFast {d : Nat} (a b : FastIntPoly d) : FastIntPoly d :=
  Sized.ofFn fun k => splitConvolution (· + ·) (· - ·) (· * ·) 0 d k.val
    (fun j => a.coeffs[j]?.getD 0) (fun j => b.coeffs[j]?.getD 0)

/-- Compatibility name; execution uses the split-loop kernel. -/
@[expose] def negacyclicMulInt {d : Nat} (a b : FastIntPoly d) : FastIntPoly d :=
  negacyclicMulFast a b

theorem negacyclicMulFast_eq_spec {d : Nat} (a b : FastIntPoly d) :
    (negacyclicMulFast a b).spec = negacyclicSpec a.spec b.spec := by
  funext k
  simp only [negacyclicMulFast, Sized.spec_ofFn, splitConvolution_eq_spec]
  have ha : (fun i : Fin d => a.coeffs[i.val]?.getD 0) = a.spec := by
    funext i; simp [Sized.spec, a.size_eq, i.isLt]
  have hb : (fun i : Fin d => b.coeffs[i.val]?.getD 0) = b.spec := by
    funext i; simp [Sized.spec, b.size_eq, i.isLt]
  rw [ha, hb]

theorem negacyclicMul_left_distrib {d : Nat} (a b c : IntCycloSpec d) :
    negacyclicSpec a (fun i => b i + c i) =
      fun k => negacyclicSpec a b k + negacyclicSpec a c k := by
  funext k
  unfold negacyclicSpec
  rw [← sumInt_add]
  apply sumInt_congr
  intro i hi
  simp only [hi, ↓reduceDIte, Int.mul_add, wrapSign]
  split <;> omega

@[expose] def reduceSpec {d q : Nat} (hq : 0 < q) (a : IntCycloSpec d) : CycloSpec d q :=
  fun i => ⟨a i % (q : Int), Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
@[expose] def cycloAdd {d q : Nat} (hq : 0 < q) (a b : CycloSpec d q) : CycloSpec d q :=
  reduceSpec hq (fun i => (a i).val + (b i).val)
@[expose] def cycloNeg {d q : Nat} (hq : 0 < q) (a : CycloSpec d q) : CycloSpec d q :=
  reduceSpec hq (fun i => -(a i).val)

theorem reduceSpec_add {d q : Nat} (hq : 0 < q) (a b : IntCycloSpec d) :
    reduceSpec hq (fun i => a i + b i) = cycloAdd hq (reduceSpec hq a) (reduceSpec hq b) := by
  funext i; apply Subtype.ext; exact Int.add_emod _ _ _

theorem cyclo_add_comm {d q : Nat} (hq : 0 < q) (a b : CycloSpec d q) :
    cycloAdd hq a b = cycloAdd hq b a := by
  funext i; apply Subtype.ext; simp [cycloAdd, reduceSpec, Int.add_comm]

theorem cyclo_add_assoc {d q : Nat} (hq : 0 < q) (a b c : CycloSpec d q) :
    cycloAdd hq (cycloAdd hq a b) c = cycloAdd hq a (cycloAdd hq b c) := by
  funext i; apply Subtype.ext
  simp only [cycloAdd, reduceSpec]
  rw [Int.emod_add_emod, Int.add_emod_emod, Int.add_assoc]

theorem cyclo_add_neg {d q : Nat} (hq : 0 < q) (a : CycloSpec d q) :
    cycloAdd hq a (cycloNeg hq a) = reduceSpec hq (fun _ => 0) := by
  funext i; apply Subtype.ext
  simp [cycloAdd, cycloNeg, reduceSpec, Int.add_emod_emod, Int.add_right_neg]

/-- A single pass over the contiguous array; the execution path allocates no list. -/
@[expose] def normInfFast (a : Array Int) : Nat := a.foldl (fun m x => max m x.natAbs) 0

private theorem maxFold_bound (xs : List Int) (m B : Nat) :
    xs.foldl (fun m x => max m x.natAbs) m ≤ B ↔
      m ≤ B ∧ ∀ x ∈ xs, x.natAbs ≤ B := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.max_le, List.mem_cons, forall_eq_or_imp]
    exact and_assoc

/-- Mathematical supremum characterization, independent of traversal order. -/
theorem normInfFast_eq_spec (a : Array Int) (B : Nat) :
    normInfFast a ≤ B ↔ ∀ i : Fin a.size, a[i.val].natAbs ≤ B := by
  unfold normInfFast
  rw [← Array.foldl_toList, maxFold_bound]
  simp only [Nat.zero_le, true_and, List.mem_iff_getElem, Array.length_toList, Array.getElem_toList]
  constructor
  · intro h i; exact h _ ⟨i.val, i.isLt, rfl⟩
  · intro h x ⟨i, hi, hx⟩; subst x; exact h ⟨i, hi⟩

theorem coeff_le_norm {d : Nat} (a : FastIntPoly d) (i : Fin d) :
    (a.spec i).natAbs ≤ normInfFast a.coeffs :=
  (normInfFast_eq_spec a.coeffs _).mp (Nat.le_refl _) ⟨i.val, by have := a.size_eq; omega⟩

theorem norm_le {d : Nat} (a : FastIntPoly d) (B : Nat)
    (h : ∀ i, (a.spec i).natAbs ≤ B) : normInfFast a.coeffs ≤ B := by
  apply (normInfFast_eq_spec _ _).mpr
  intro i
  exact h ⟨i.val, by have := a.size_eq; omega⟩

theorem normInfFast_add_le {d : Nat} (a b : FastIntPoly d) :
    normInfFast (intAdd a b).coeffs ≤ normInfFast a.coeffs + normInfFast b.coeffs := by
  apply norm_le; intro i
  simp only [addFast_eq_spec]
  exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add (coeff_le_norm a i) (coeff_le_norm b i))

theorem normInfFast_sub_le {d : Nat} (a b : FastIntPoly d) :
    normInfFast (intSub a b).coeffs ≤ normInfFast a.coeffs + normInfFast b.coeffs := by
  apply norm_le; intro i
  simp only [subFast_eq_spec, Int.sub_eq_add_neg]
  apply Nat.le_trans (Int.natAbs_add_le _ _)
  simpa using Nat.add_le_add (coeff_le_norm a i) (coeff_le_norm b i)

theorem normInfFast_scale_le {d : Nat} (c : Int) (a : FastIntPoly d) :
    normInfFast (intScale c a).coeffs ≤ c.natAbs * normInfFast a.coeffs := by
  apply norm_le; intro i
  simpa [Int.natAbs_mul] using Nat.mul_le_mul_left c.natAbs (coeff_le_norm a i)

theorem sumInt_bound (n B : Nat) (f : Nat → Int) (h : ∀ i, i < n → (f i).natAbs ≤ B) :
    (sumInt n f).natAbs ≤ n * B := by
  induction n with
  | zero => simp [sumInt]
  | succ n ih =>
    exact Nat.le_trans (Int.natAbs_add_le _ _)
      (by simpa [Nat.succ_mul] using Nat.add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega)))

theorem normInfFast_negacyclicMul_le {d : Nat} (a b : FastIntPoly d) :
    normInfFast (negacyclicMulInt a b).coeffs ≤ d * normInfFast a.coeffs * normInfFast b.coeffs := by
  apply norm_le; intro k
  change ((negacyclicMulFast a b).spec k).natAbs ≤ _
  rw [negacyclicMulFast_eq_spec]
  unfold negacyclicSpec
  rw [Nat.mul_assoc]
  apply sumInt_bound
  intro i hi
  simp only [hi, ↓reduceDIte, wrapSign]
  split <;> simp only [Int.natAbs_neg, Int.natAbs_mul]
  all_goals exact Nat.mul_le_mul (coeff_le_norm a ⟨i, hi⟩) (coeff_le_norm b _)

@[expose] def checkShort (d β : Nat) (xs : Array Int) : Bool :=
  decide (xs.size = d ∧ normInfFast xs ≤ β)

theorem checkShort_iff (d β : Nat) (xs : Array Int) :
    checkShort d β xs = true ↔ xs.size = d ∧ normInfFast xs ≤ β := by
  simp [checkShort]

theorem wrapSign_high (i k : Nat) (x : Int) (h : k < i) : wrapSign i k x = -x := by
  simp [wrapSign, Nat.not_le_of_lt h]

theorem sumInt_mod (n : Nat) (q : Int) (f : Nat → Int) :
    sumInt n (fun i => f i % q) % q = sumInt n f % q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumInt]
    rw [Int.add_emod, ih, Int.emod_emod, ← Int.add_emod]

@[expose] def cycloMul {d q : Nat} (hq : 0 < q) (a b : CycloSpec d q) : CycloSpec d q :=
  reduceSpec hq (negacyclicSpec (fun i => (a i).val) (fun i => (b i).val))

private theorem neg_mod_congr (a b q : Int) (h : a % q = b % q) : -a % q = -b % q := by
  have hh := congrArg (fun r : Int => (0 % q - r) % q) h
  rw [← Int.sub_emod, ← Int.sub_emod] at hh
  simpa only [Int.zero_sub] using hh

theorem reduceSpec_mul {d q : Nat} (hq : 0 < q) (a b : IntCycloSpec d) :
    cycloMul hq (reduceSpec hq a) (reduceSpec hq b) = reduceSpec hq (negacyclicSpec a b) := by
  funext k; apply Subtype.ext
  simp only [cycloMul, reduceSpec, negacyclicSpec]
  conv => lhs; rw [← sumInt_mod]
  conv => rhs; rw [← sumInt_mod]
  congr 1
  apply sumInt_congr
  intro i hi
  simp only [hi, ↓reduceDIte, wrapSign]
  split
  · exact (Int.mul_emod _ _ _).symm
  · exact neg_mod_congr _ _ _ (Int.mul_emod _ _ _).symm

/-- A checked lift, not modular reduction: noncanonical machine words are rejected. -/
@[expose] def canonicalGoldilocksOfUInt64 (x : UInt64) : Option Goldilocks :=
  if h : x.toNat < Obend.Apps.ZkNtt.goldilocksPrime then some ⟨x.toNat, h⟩ else none

theorem canonicalGoldilocksOfUInt64_complete (x : UInt64)
    (h : x.toNat < Obend.Apps.ZkNtt.goldilocksPrime) :
    canonicalGoldilocksOfUInt64 x = some ⟨x.toNat, h⟩ := by
  simp [canonicalGoldilocksOfUInt64, h]

theorem canonicalGoldilocksOfUInt64_isSome_iff (x : UInt64) :
    (canonicalGoldilocksOfUInt64 x).isSome = true ↔ x.toNat < Obend.Apps.ZkNtt.goldilocksPrime := by
  unfold canonicalGoldilocksOfUInt64
  split <;> simp_all

theorem canonicalGoldilocksOfUInt64_injective (x y : UInt64) (z : Goldilocks)
    (hx : canonicalGoldilocksOfUInt64 x = some z)
    (hy : canonicalGoldilocksOfUInt64 y = some z) : x = y := by
  unfold canonicalGoldilocksOfUInt64 at hx hy
  split at hx
  · split at hy
    · apply UInt64.toNat_inj.mp
      exact (congrArg Goldilocks.val (Option.some.inj hx)).trans
        (congrArg Goldilocks.val (Option.some.inj hy)).symm
    · contradiction
  · contradiction

/- Goldilocks has v₂(p−1)=32. For d=2^s, X^d+1 has min(d,2^31)
irreducible factors over this field; it is not an irreducible lattice ring.
Ajtai/MSIS below uses exact Int witnesses and an independent arbitrary q_lat. -/
abbrev goldP : Int := Obend.Apps.ZkNtt.goldilocksPrime

@[expose] def goldOfInt (z : Int) : Goldilocks :=
  ⟨(z % goldP).toNat, by
    have := Int.emod_nonneg z (show goldP ≠ 0 by decide)
    have := Int.emod_lt_of_pos z (show 0 < goldP by decide)
    dsimp only [goldP] at *
    omega⟩

theorem goldOfInt_val (z : Int) : ((goldOfInt z).val : Int) = z % goldP := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))

theorem goldOfInt_nat (a : Goldilocks) : goldOfInt a.val = a := by
  apply Goldilocks.ext
  have h : (a.val : Int) % goldP = a.val := Int.emod_eq_of_lt (by omega) (by have := a.isLt; dsimp only [goldP]; omega)
  have := goldOfInt_val a.val
  omega

theorem gold_add_int (a b : Goldilocks) :
    ((Goldilocks.add a b).val : Int) = ((a.val : Int) + b.val) % goldP := by
  rw [Goldilocks.add_val, Int.natCast_emod, Int.natCast_add]

theorem gold_mul_int (a b : Goldilocks) :
    ((Goldilocks.mul a b).val : Int) = ((a.val : Int) * b.val) % goldP := by
  rw [Goldilocks.mul_val, Int.natCast_emod, Int.natCast_mul]

theorem gold_sub_int (a b : Goldilocks) :
    ((Goldilocks.sub a b).val : Int) = ((a.val : Int) - b.val) % goldP := by
  rw [Goldilocks.sub_val, Int.natCast_emod,
    Int.ofNat_sub (by have := b.isLt; omega), Int.natCast_add]
  have he : (a.val : Int) + goldP - b.val = ((a.val : Int) - b.val) + goldP := by omega
  rw [he, Int.add_emod_right]

theorem goldOfInt_add (a b : Int) :
    Goldilocks.add (goldOfInt a) (goldOfInt b) = goldOfInt (a+b) := by
  apply Goldilocks.ext; apply Int.ofNat_inj.mp
  rw [gold_add_int, goldOfInt_val, goldOfInt_val, goldOfInt_val, ← Int.add_emod]

theorem goldOfInt_sub (a b : Int) :
    Goldilocks.sub (goldOfInt a) (goldOfInt b) = goldOfInt (a-b) := by
  apply Goldilocks.ext; apply Int.ofNat_inj.mp
  rw [gold_sub_int, goldOfInt_val, goldOfInt_val, goldOfInt_val, ← Int.sub_emod]

theorem goldOfInt_mul (a b : Int) :
    Goldilocks.mul (goldOfInt a) (goldOfInt b) = goldOfInt (a*b) := by
  apply Goldilocks.ext; apply Int.ofNat_inj.mp
  rw [gold_mul_int, goldOfInt_val, goldOfInt_val, goldOfInt_val, ← Int.mul_emod]

theorem splitConvolution_gold (d k : Nat) (a b : Nat → Int) :
    splitConvolution Goldilocks.add Goldilocks.sub Goldilocks.mul Goldilocks.zero d k
      (fun i => goldOfInt (a i)) (fun i => goldOfInt (b i)) =
    goldOfInt (splitConvolution (· + ·) (· - ·) (· * ·) 0 d k a b) := by
  unfold splitConvolution
  have hz : Goldilocks.zero = goldOfInt 0 := by apply Goldilocks.ext; rfl
  simp only [goldOfInt_mul, hz]
  rw [Array.foldl_hom goldOfInt (fun x y => goldOfInt_add x (a y * b (k-y)))]
  exact Array.foldl_hom goldOfInt (fun x y => goldOfInt_sub x (a (k+1+y)*b (d-1-y)))

namespace FastGoldilocksRing
@[expose] def zeroFast (d : Nat) : FastGoldilocksRing d := Sized.ofFn fun _ => Goldilocks.zero
@[expose] def oneFast (d : Nat) : FastGoldilocksRing d :=
  Sized.ofFn fun i => if i.val = 0 then Goldilocks.one else Goldilocks.zero
@[expose] def addFast {d : Nat} (a b : FastGoldilocksRing d) : FastGoldilocksRing d :=
  Sized.ofFn fun i => Goldilocks.add (a.spec i) (b.spec i)
@[expose] def subFast {d : Nat} (a b : FastGoldilocksRing d) : FastGoldilocksRing d :=
  Sized.ofFn fun i => Goldilocks.sub (a.spec i) (b.spec i)
@[expose] def negFast {d : Nat} (a : FastGoldilocksRing d) : FastGoldilocksRing d :=
  Sized.ofFn fun i => Goldilocks.neg (a.spec i)
@[expose] def scalarMulFast {d : Nat} (c : Goldilocks) (a : FastGoldilocksRing d) : FastGoldilocksRing d :=
  Sized.ofFn fun i => Goldilocks.mul c (a.spec i)
/-- Native field arithmetic in the two loops; no unbounded Int convolution. -/
@[expose] def negacyclicMulFast {d : Nat} (a b : FastGoldilocksRing d) : FastGoldilocksRing d :=
  Sized.ofFn fun k => splitConvolution Goldilocks.add Goldilocks.sub Goldilocks.mul Goldilocks.zero
    d k.val (fun j => a.coeffs[j]?.getD Goldilocks.zero) (fun j => b.coeffs[j]?.getD Goldilocks.zero)

@[expose] def cycloSpec {d : Nat} (a : FastGoldilocksRing d) : CycloSpec d Obend.Apps.ZkNtt.goldilocksPrime :=
  fun i => ⟨(a.spec i).val, by have := (a.spec i).isLt; omega⟩

theorem addFast_eq_spec {d : Nat} (a b : FastGoldilocksRing d) :
    cycloSpec (addFast a b) = cycloAdd (by decide) (cycloSpec a) (cycloSpec b) := by
  funext i; apply Subtype.ext
  simpa only [cycloSpec, addFast, Sized.spec_ofFn, cycloAdd, reduceSpec] using gold_add_int (a.spec i) (b.spec i)

theorem subFast_eq_spec {d : Nat} (a b : FastGoldilocksRing d) :
    cycloSpec (subFast a b) = reduceSpec (by decide)
      (fun i => (cycloSpec a i).val - (cycloSpec b i).val) := by
  funext i; apply Subtype.ext
  simpa only [cycloSpec, subFast, Sized.spec_ofFn, reduceSpec] using gold_sub_int (a.spec i) (b.spec i)

theorem negacyclicMulFast_eq_spec {d : Nat} (a b : FastGoldilocksRing d) :
    cycloSpec (negacyclicMulFast a b) = cycloMul (by decide) (cycloSpec a) (cycloSpec b) := by
  funext k; apply Subtype.ext
  simp only [cycloSpec, negacyclicMulFast, Sized.spec_ofFn, cycloMul, reduceSpec]
  have ha : (fun j : Nat => a.coeffs[j]?.getD Goldilocks.zero) =
      (fun j => goldOfInt (a.coeffs[j]?.getD Goldilocks.zero).val) := by
    funext j; exact (goldOfInt_nat _).symm
  have hb : (fun j : Nat => b.coeffs[j]?.getD Goldilocks.zero) =
      (fun j => goldOfInt (b.coeffs[j]?.getD Goldilocks.zero).val) := by
    funext j; exact (goldOfInt_nat _).symm
  rw [ha, hb, splitConvolution_gold, goldOfInt_val, splitConvolution_eq_spec]
  have ea : (fun i : Fin d => ((a.coeffs[i.val]?.getD Goldilocks.zero).val : Int)) =
      (fun i => ((a.spec i).val : Int)) := by funext i; simp [Sized.spec, a.size_eq, i.isLt]
  have eb : (fun i : Fin d => ((b.coeffs[i.val]?.getD Goldilocks.zero).val : Int)) =
      (fun i => ((b.spec i).val : Int)) := by funext i; simp [Sized.spec, b.size_eq, i.isLt]
  rw [ea, eb]

end FastGoldilocksRing

end Obend.Crypto.Fast
