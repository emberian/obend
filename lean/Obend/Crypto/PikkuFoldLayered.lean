module
public import Obend.Crypto.FastRing
public import Obend.Crypto.Transcript
public import Obend.Crypto.GameSoundness
import all Obend.Crypto.GameSoundness

public section
namespace Obend.Crypto.Fast

open Obend.Crypto.GameSoundness

/-- Sparse ternary rows contain only signed unit entries; absence represents zero. -/
structure SignedIndex (n : Nat) where
  col : Fin n
  negative : Bool
  deriving DecidableEq

abbrev TernaryMatrix (rows cols : Nat) := Sized (Array (SignedIndex cols)) rows

def signedValue (negative : Bool) (x : Int) : Int := if negative then -x else x

def sparseRow {n : Nat} (row : Array (SignedIndex n)) (w : FastIntPoly n) : Int :=
  sumInt row.size fun j => if h : j < row.size then
    signedValue row[j].negative (w.spec row[j].col) else 0

/-- Only additions/subtractions of selected coefficients; no integer multiplications. -/
def sparseRowFast {n : Nat} (row : Array (SignedIndex n)) (w : FastIntPoly n) : Int :=
  row.foldl (fun acc e => acc + signedValue e.negative (w.spec e.col)) 0

theorem sparseRowFast_eq_sparseRow {n : Nat} (row : Array (SignedIndex n)) (w : FastIntPoly n) :
    sparseRowFast row w = sparseRow row w := by
  apply Array.foldl_induction (motive := fun k acc => acc = sumInt k (fun j =>
    if h : j < row.size then signedValue row[j].negative (w.spec row[j].col) else 0)) rfl
  intro i acc hacc
  simp only [sumInt, hacc, i.isLt, ↓reduceDIte]
  rfl

def applyTernary {m n : Nat} (M : TernaryMatrix m n) (w : FastIntPoly n) : FastIntPoly m :=
  Sized.ofFn fun i => sparseRowFast (M.spec i) w

def rowWeight {m n : Nat} (M : TernaryMatrix m n) : Nat :=
  M.coeffs.foldl (fun k row => max k row.size) 0

private theorem rowWeight_ge {m n : Nat} (M : TernaryMatrix m n) (i : Fin m) :
    (M.spec i).size ≤ rowWeight M := by
  have aux (xs : List (Array (SignedIndex n))) (k : Nat) (x : Array (SignedIndex n))
      (hx : x ∈ xs) : x.size ≤ xs.foldl (fun k row => max k row.size) k := by
    have lower (ys : List (Array (SignedIndex n))) (k : Nat) :
        k ≤ ys.foldl (fun k row => max k row.size) k := by
      induction ys generalizing k with
      | nil => exact Nat.le_refl _
      | cons y ys ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
    induction xs generalizing k with
    | nil => simp at hx
    | cons y ys ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst x; exact Nat.le_trans (Nat.le_max_right _ _) (lower ys _)
      · exact ih _ h
  unfold rowWeight
  rw [← Array.foldl_toList]
  apply aux M.coeffs.toList 0 (M.spec i)
  apply List.mem_iff_getElem.mpr
  exact ⟨i.val, by simp [M.size_eq], rfl⟩

theorem sparseRow_add {n : Nat} (row : Array (SignedIndex n)) (a b : FastIntPoly n) :
    sparseRow row (intAdd a b) = sparseRow row a + sparseRow row b := by
  unfold sparseRow; rw [← sumInt_add]
  apply sumInt_congr; intro j hj
  simp only [hj, ↓reduceDIte, addFast_eq_spec, signedValue]
  split <;> omega

theorem sparseRow_sub {n : Nat} (row : Array (SignedIndex n)) (a b : FastIntPoly n) :
    sparseRow row (intSub a b) = sparseRow row a - sparseRow row b := by
  have h := sumInt_mul row.size (-1) (fun j => if h : j < row.size then
    signedValue row[j].negative (b.spec row[j].col) else 0)
  unfold sparseRow
  rw [Int.sub_eq_add_neg, ← Int.neg_one_mul, ← h, ← sumInt_add]
  apply sumInt_congr; intro j hj
  simp only [hj, ↓reduceDIte, subFast_eq_spec, signedValue]
  split <;> omega

theorem applyKroneckerTernary_add {m n : Nat} (M : TernaryMatrix m n) (a b : FastIntPoly n) :
    applyTernary M (intAdd a b) = intAdd (applyTernary M a) (applyTernary M b) := by
  apply Sized.ext; funext i
  simp only [applyTernary, addFast_eq_spec, Sized.spec_ofFn, sparseRowFast_eq_sparseRow, sparseRow_add]

theorem applyKroneckerTernary_sub {m n : Nat} (M : TernaryMatrix m n) (a b : FastIntPoly n) :
    applyTernary M (intSub a b) = intSub (applyTernary M a) (applyTernary M b) := by
  apply Sized.ext; funext i
  simp only [applyTernary, subFast_eq_spec, Sized.spec_ofFn, sparseRowFast_eq_sparseRow, sparseRow_sub]

theorem normInf_ternary_le {m n : Nat} (M : TernaryMatrix m n) (w : FastIntPoly n) :
    normInfFast (applyTernary M w).coeffs ≤ rowWeight M * normInfFast w.coeffs := by
  apply norm_le; intro i
  simp only [applyTernary, Sized.spec_ofFn, sparseRowFast_eq_sparseRow]
  apply Nat.le_trans (sumInt_bound _ _ _ ?_) (Nat.mul_le_mul_right _ (rowWeight_ge M i))
  intro j hj
  simp only [hj, ↓reduceDIte, signedValue]
  split <;> simpa using coeff_le_norm w ((M.spec i)[j].col)

/-- I_r ⊗ M, with every expanded column indexed into exactly r*n inputs. -/
def kronecker {m n : Nat} (r : Nat) (M : TernaryMatrix m n) : TernaryMatrix (r * m) (r * n) :=
  Sized.ofFn fun i =>
    have hm : 0 < m := by
      by_cases hz : m = 0
      · have := i.isLt; simp [hz] at this
      · omega
    have hb : i.val / m < r := (Nat.div_lt_iff_lt_mul hm).mpr (by simpa [Nat.mul_comm] using i.isLt)
    (M.spec ⟨i.val % m, Nat.mod_lt _ hm⟩).map fun entry =>
      ⟨⟨i.val / m * n + entry.col.val, by
        have := entry.col.isLt
        have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hb)
        simp only [Nat.succ_mul] at this
        omega⟩, entry.negative⟩

/-- Read each block in place. No expanded matrix or copied witness slices are allocated. -/
def applyKroneckerTernaryFast {m n : Nat} (r : Nat) (M : TernaryMatrix m n)
    (w : FastIntPoly (r*n)) : FastIntPoly (r*m) :=
  Sized.ofFn fun i =>
    have hm : 0 < m := by
      have := i.isLt
      by_cases h : m = 0
      · simp [h] at this
      · omega
    have hb : i.val / m < r := (Nat.div_lt_iff_lt_mul hm).mpr (by simpa [Nat.mul_comm] using i.isLt)
    (M.spec ⟨i.val % m, Nat.mod_lt _ hm⟩).foldl (fun acc e =>
      acc + signedValue e.negative (w.spec ⟨i.val / m * n + e.col.val, by
        have := e.col.isLt
        have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hb)
        simp only [Nat.succ_mul] at this
        omega⟩)) 0

theorem applyKroneckerTernaryFast_eq_spec {m n : Nat} (r : Nat) (M : TernaryMatrix m n)
    (w : FastIntPoly (r*n)) :
    applyKroneckerTernaryFast r M w = applyTernary (kronecker r M) w := by
  apply Sized.ext; funext i
  simp only [applyKroneckerTernaryFast, applyTernary, Sized.spec_ofFn,
    sparseRowFast, kronecker, Array.foldl_map]

/-- The public execution entry point also uses the unmaterialized kernel. -/
def applyKroneckerTernary {m n : Nat} (r : Nat) (M : TernaryMatrix m n)
    (w : FastIntPoly (r*n)) : FastIntPoly (r*m) := applyKroneckerTernaryFast r M w

theorem rowWeight_kronecker_le {m n : Nat} (r : Nat) (M : TernaryMatrix m n) :
    rowWeight (kronecker r M) ≤ rowWeight M := by
  apply Array.foldl_induction (motive := fun _ acc => acc ≤ rowWeight M) (Nat.zero_le _)
  intro i acc hacc
  apply Nat.max_le.mpr ⟨hacc, ?_⟩
  change ((kronecker r M).spec ⟨i.val, by simpa [(kronecker r M).size_eq] using i.isLt⟩).size ≤ _
  simp only [kronecker, Sized.spec_ofFn, Array.size_map]
  exact rowWeight_ge M _

/-- Dependent composition prevents malformed adjacent layer dimensions. -/
inductive Layers : Nat → Nat → Type where
  | done (n : Nat) : Layers n n
  | step {n m k : Nat} (M : TernaryMatrix m n) (rest : Layers m k) : Layers n k

def Layers.apply {n m : Nat} : Layers n m → FastIntPoly n → FastIntPoly m
  | .done _, w => w
  | .step M rest, w => rest.apply (applyTernary M w)
def Layers.weight {n m : Nat} : Layers n m → Nat
  | .done _ => 1
  | .step M rest => rest.weight * rowWeight M
def Layers.length {n m : Nat} : Layers n m → Nat
  | .done _ => 0
  | .step _ rest => rest.length + 1

theorem normInf_layeredKronecker_le {n m : Nat} (layers : Layers n m) (w : FastIntPoly n)
    (β : Nat) (hw : normInfFast w.coeffs ≤ β) :
    normInfFast (layers.apply w).coeffs ≤ layers.weight * β := by
  induction layers generalizing β with
  | done n => simpa [Layers.apply, Layers.weight] using hw
  | step M rest ih =>
    exact Nat.le_trans (ih (applyTernary M w) (rowWeight M * β)
      (Nat.le_trans (normInf_ternary_le M w) (Nat.mul_le_mul_left _ hw)))
      (by simp [Layers.weight, Nat.mul_assoc])

def Layers.uniform {n m : Nat} (K : Nat) : Layers n m → Prop
  | .done _ => True
  | .step M rest => rowWeight M ≤ K ∧ rest.uniform K

theorem normInf_uniformLayers_le {n m : Nat} (layers : Layers n m) (K β : Nat)
    (hK : layers.uniform K) (w : FastIntPoly n) (hw : normInfFast w.coeffs ≤ β) :
    normInfFast (layers.apply w).coeffs ≤ K^layers.length * β := by
  have aux : ∀ {a b} (ls : Layers a b), ls.uniform K → ls.weight ≤ K^ls.length := by
    intro a b ls
    induction ls with
    | done n => intro h; simp [Layers.weight, Layers.length]
    | step M rest ih =>
      intro hK
      exact Nat.le_trans (Nat.mul_le_mul (ih hK.2) hK.1) (by simp [Layers.length, Nat.pow_succ])
  exact Nat.le_trans (normInf_layeredKronecker_le layers w β hw) (Nat.mul_le_mul_right β (aux layers hK))

abbrev IntMatrix (rows cols : Nat) := Sized (FastIntPoly cols) rows

@[expose] def dot {n : Nat} (a b : FastIntPoly n) : Int :=
  sumInt n fun i => if h : i < n then a.spec ⟨i,h⟩ * b.spec ⟨i,h⟩ else 0
@[expose] def matVec {m n : Nat} (A : IntMatrix m n) (w : FastIntPoly n) : FastIntPoly m :=
  Sized.ofFn fun i => dot (A.spec i) w
@[expose] def matVecModQ {m n : Nat} (A : IntMatrix m n) (q : Nat) (w : FastIntPoly n) : FastIntPoly m :=
  Sized.ofFn fun i => (matVec A w).spec i % (q : Int)

theorem dot_add {n : Nat} (a u v : FastIntPoly n) : dot a (intAdd u v) = dot a u + dot a v := by
  unfold dot; rw [← sumInt_add]
  apply sumInt_congr; intro i hi
  simp [hi, Int.mul_add]

theorem dot_scale {n : Nat} (a u : FastIntPoly n) (c : Int) :
    dot a (intScale c u) = c * dot a u := by
  unfold dot; rw [← sumInt_mul]
  apply sumInt_congr; intro i hi
  simp only [hi, ↓reduceDIte, scaleFast_eq_spec]
  rw [← Int.mul_assoc, Int.mul_comm (a.spec _), Int.mul_assoc]

theorem dot_sub {n : Nat} (a u v : FastIntPoly n) : dot a (intSub u v) = dot a u - dot a v := by
  have he : intSub u v = intAdd u (intScale (-1) v) := by
    apply Sized.ext; funext i; simp; omega
  rw [he, dot_add, dot_scale]; omega

/-- L0 output data: exact dimension, nonzero, modular kernel equation and shortness. -/
structure MSISBreakWitness {m n : Nat} (A : IntMatrix m n) (q B : Nat) where
  z : FastIntPoly n
  nonzero : z ≠ zeroVec n
  kernel : matVecModQ A q z = zeroVec m
  short : normInfFast z.coeffs ≤ B

abbrev ShortSISKernelVec := @MSISBreakWitness

/-- Computable subtraction; proofs erase and the returned vector is usable at runtime. -/
def foldTwoInstances_binding_reduction {m n : Nat} (A : IntMatrix m n) (q β : Nat)
    (u v : FastIntPoly n) (hne : u ≠ v)
    (hcm : matVecModQ A q u = matVecModQ A q v)
    (hu : normInfFast u.coeffs ≤ β) (hv : normInfFast v.coeffs ≤ β) :
    MSISBreakWitness A q (2 * β) where
  z := intSub u v
  nonzero := by
    intro hz; apply hne; apply Sized.ext; funext i
    have h := congrArg (fun w => w.spec i) hz
    simp [zeroVec] at h; omega
  kernel := by
    apply Sized.ext; funext i
    have h := congrArg (fun w => w.spec i) hcm
    simp only [matVecModQ, matVec, Sized.spec_ofFn] at h ⊢
    rw [dot_sub, Int.sub_emod, h, Int.sub_self, Int.zero_emod]
    simp [zeroVec]
  short := Nat.le_trans (normInfFast_sub_le u v) (by omega)

@[expose] def foldWitness {n : Nat} (c : Int) (u v : FastIntPoly n) : FastIntPoly n :=
  intAdd u (intScale c v)

theorem foldTwoInstances_complete {m n : Nat} (A : IntMatrix m n) (c : Int)
    (u v : FastIntPoly n) (β₁ β₂ : Nat)
    (hu : normInfFast u.coeffs ≤ β₁) (hv : normInfFast v.coeffs ≤ β₂) :
    matVec A (foldWitness c u v) = foldWitness c (matVec A u) (matVec A v) ∧
    normInfFast (foldWitness c u v).coeffs ≤ β₁ + c.natAbs * β₂ := by
  constructor
  · apply Sized.ext; funext i
    simp [matVec, foldWitness, dot_add, dot_scale]
  · exact Nat.le_trans (normInfFast_add_le _ _)
      (Nat.add_le_add hu (Nat.le_trans (normInfFast_scale_le _ _) (Nat.mul_le_mul_left _ hv)))

/-- Signed, length-delimited integer encoding, including zero's unique sign. -/
def encodeInts {n : Nat} (w : FastIntPoly n) : ByteArray :=
  Obend.Digest.Cshake256.Native.bytesOfList
    (leb128 n ++ w.coeffs.toList.flatMap fun x =>
      (if x < 0 then [1] else [0]) ++ leb128 x.natAbs)

/-- The verifier supplies the materialized matrix descriptor and both public instances. -/
def foldTranscript (descriptor cm₁ y₁ cm₂ y₂ : ByteArray) : Transcript .relationBound :=
  bindRelation "OBEND.PIKKU/v1" descriptor
    (encodeFrame (encodeFrame cm₁ y₁ ByteArray.empty) (encodeFrame cm₂ y₂ ByteArray.empty) ByteArray.empty)
    (Transcript.newUnseeded ByteArray.empty)

/-- Full-field Goldilocks fold helper for ring-level transcript callers; use `boundedFoldFromTranscript`
    and `verifyBoundedChallengeFold` for norm-controlled lattice folding (`|c| ≤ bChal`). -/
def foldFromTranscript {n : Nat} (tr : Transcript .relationBound) (u v : FastIntPoly n) :
    FastIntPoly n × Transcript .relationBound :=
  let (c, tr') := squeezeGoldilocks tr
  (foldWitness (c.val : Int) u v, tr')

def splitLo {m : Nat} (w : FastIntPoly (2*m)) : FastIntPoly m :=
  Sized.ofFn fun i => w.spec ⟨i.val, by omega⟩
def splitHi {m : Nat} (w : FastIntPoly (2*m)) : FastIntPoly m :=
  Sized.ofFn fun i => w.spec ⟨m + i.val, by omega⟩
@[expose] def akitaFold {m : Nat} (c : Int) (w : FastIntPoly (2*m)) : FastIntPoly m :=
  foldWitness c (splitLo w) (splitHi w)

def matrixLo {m n : Nat} (A : IntMatrix m (2*n)) : IntMatrix m n :=
  Sized.ofFn fun i => splitLo (A.spec i)
def matrixHi {m n : Nat} (A : IntMatrix m (2*n)) : IntMatrix m n :=
  Sized.ofFn fun i => splitHi (A.spec i)

theorem dot_split {n : Nat} (a w : FastIntPoly (2*n)) :
    dot a w = dot (splitLo a) (splitLo w) + dot (splitHi a) (splitHi w) := by
  unfold dot
  have hn : 2*n = n+n := by omega
  conv => lhs; arg 1; rw [hn]
  rw [sumInt_split n n]
  congr 1
  · apply sumInt_congr; intro i hi
    simp only [show i < 2*n by omega, hi, ↓reduceDIte, splitLo, Sized.spec_ofFn]
  · apply sumInt_congr; intro i hi
    simp only [show n+i < 2*n by omega, hi, ↓reduceDIte, splitHi, Sized.spec_ofFn]

/-- Horizontal splitting uses the corresponding key half; the shared-key folding
identity below is deliberately a separate statement. -/
theorem matVecModQ_split {m n : Nat} (A : IntMatrix m (2*n)) (q : Nat) (w : FastIntPoly (2*n)) :
    matVecModQ A q w = Sized.ofFn (fun i =>
      ((matVecModQ (matrixLo A) q (splitLo w)).spec i +
       (matVecModQ (matrixHi A) q (splitHi w)).spec i) % (q : Int)) := by
  apply Sized.ext; funext i
  simp only [matVecModQ, matVec, matrixLo, matrixHi, Sized.spec_ofFn, dot_split]
  exact Int.add_emod _ _ _

def foldModQ {m : Nat} (q : Nat) (c : Int) (lo hi : FastIntPoly m) : FastIntPoly m :=
  Sized.ofFn fun i => (lo.spec i + c * hi.spec i) % (q : Int)

theorem matVecModQ_foldWitness {m n : Nat} (G : IntMatrix m n) (q : Nat) (c : Int)
    (lo hi : FastIntPoly n) :
    matVecModQ G q (foldWitness c lo hi) = foldModQ q c (matVecModQ G q lo) (matVecModQ G q hi) := by
  apply Sized.ext; funext i
  simp only [matVecModQ, matVec, foldWitness, foldModQ, Sized.spec_ofFn, dot_add, dot_scale]
  simp only [Int.add_emod, Int.mul_emod, Int.emod_emod]

theorem matVecModQ_akitaFold {m n : Nat} (G : IntMatrix m n) (q : Nat) (c : Int)
    (w : FastIntPoly (2*n)) :
    matVecModQ G q (akitaFold c w) =
      foldModQ q c (matVecModQ G q (splitLo w)) (matVecModQ G q (splitHi w)) :=
  matVecModQ_foldWitness G q c (splitLo w) (splitHi w)

theorem akitaFold_complete {m : Nat} (c : Int) (w : FastIntPoly (2*m)) (β : Nat)
    (hw : normInfFast w.coeffs ≤ β) :
    normInfFast (akitaFold c w).coeffs ≤ β + c.natAbs * β := by
  have hlo : normInfFast (splitLo w).coeffs ≤ β := by
    apply norm_le; intro i; simp only [splitLo, Sized.spec_ofFn]; exact Nat.le_trans (coeff_le_norm w _) hw
  have hhi : normInfFast (splitHi w).coeffs ≤ β := by
    apply norm_le; intro i; simp only [splitHi, Sized.spec_ofFn]; exact Nat.le_trans (coeff_le_norm w _) hw
  exact Nat.le_trans (normInfFast_add_le _ _)
    (Nat.add_le_add hlo (Nat.le_trans (normInfFast_scale_le _ _) (Nat.mul_le_mul_left _ hhi)))

/-- k rounds consume exactly 2^k*m coefficients and return exactly m. -/
def akitaFoldRounds (m : Nat) : (cs : List Int) → FastIntPoly (2^cs.length*m) → FastIntPoly m
  | [], w => ⟨w.coeffs, by simpa using w.size_eq⟩
  | c :: cs, w =>
    akitaFoldRounds m cs (akitaFold c ⟨w.coeffs, by
      simpa [List.length_cons, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using w.size_eq⟩)

@[expose] def akitaBudget : List Int → Nat → Nat
  | [], β => β
  | c :: cs, β => akitaBudget cs (β + c.natAbs * β)

theorem akitaFoldRounds_complete (m : Nat) (cs : List Int)
    (w : FastIntPoly (2^cs.length*m)) (β : Nat) (hw : normInfFast w.coeffs ≤ β) :
    normInfFast (akitaFoldRounds m cs w).coeffs ≤ akitaBudget cs β := by
  induction cs generalizing β with
  | nil => exact hw
  | cons c cs ih => exact ih _ _ (akitaFold_complete c _ β hw)

/-- A double opening of the same half commitment gives a short kernel vector.
Different challenges alone do not imply a collision without this consistency premise. -/
def akitaSplitFold_extract_sis {m n : Nat} (A : IntMatrix m n) (q β : Nat)
    (u v : FastIntPoly n) (hne : u ≠ v)
    (hcm : matVecModQ A q u = matVecModQ A q v)
    (hu : normInfFast u.coeffs ≤ β) (hv : normInfFast v.coeffs ≤ β) : MSISBreakWitness A q (2*β) :=
  foldTwoInstances_binding_reduction A q β u v hne hcm hu hv

/-- Two distinct *integer* challenges determine both halves before modular commitment.
No division in the lattice ring, and no unit-difference assumption, is hidden here. -/
theorem akitaTwoChallenge_injective {n : Nat} (c₁ c₂ : Int) (hc : c₁ ≠ c₂)
    (u v : FastIntPoly (2*n))
    (h₁ : akitaFold c₁ u = akitaFold c₁ v) (h₂ : akitaFold c₂ u = akitaFold c₂ v) : u = v := by
  have halves (i : Fin n) : (splitLo u).spec i = (splitLo v).spec i ∧
      (splitHi u).spec i = (splitHi v).spec i := by
    have h₁ := congrArg (fun x => x.spec i) h₁
    have h₂ := congrArg (fun x => x.spec i) h₂
    simp only [akitaFold, foldWitness, addFast_eq_spec, scaleFast_eq_spec] at h₁ h₂
    have hp : (c₁-c₂) * ((splitHi u).spec i - (splitHi v).spec i) = 0 := by
      simp only [Int.sub_mul, Int.mul_sub]; omega
    have hh : (splitHi u).spec i = (splitHi v).spec i := by
      rcases Int.mul_eq_zero.mp hp with hz | hz
      · exact False.elim (hc (by omega))
      · omega
    constructor
    · rw [hh] at h₁; omega
    · exact hh
  apply Sized.ext; funext i
  by_cases hi : i.val < n
  · simpa only [splitLo, Sized.spec_ofFn] using (halves ⟨i.val, hi⟩).1
  · have h := (halves ⟨i.val-n, by omega⟩).2
    simpa only [splitHi, Sized.spec_ofFn, Nat.add_sub_of_le (by omega : n ≤ i.val)] using h

/-- An inconsistent pair of split witnesses accepted at both challenges yields an
actual short kernel vector. The branch chooses a differing folded witness. -/
def akitaTwoChallenge_extract_sis {m n : Nat} (G : IntMatrix m n) (q β : Nat)
    (c₁ c₂ : Int) (hc : c₁ ≠ c₂) (u v : FastIntPoly (2*n)) (hne : u ≠ v)
    (h₁ : matVecModQ G q (akitaFold c₁ u) = matVecModQ G q (akitaFold c₁ v))
    (h₂ : matVecModQ G q (akitaFold c₂ u) = matVecModQ G q (akitaFold c₂ v))
    (hu : normInfFast u.coeffs ≤ β) (hv : normInfFast v.coeffs ≤ β) :
    ShortSISKernelVec G q (2*(β + max c₁.natAbs c₂.natAbs * β)) := by
  have bound (c : Int) (h : c.natAbs ≤ max c₁.natAbs c₂.natAbs)
      (w : FastIntPoly (2*n)) (hw : normInfFast w.coeffs ≤ β) :
      normInfFast (akitaFold c w).coeffs ≤ β + max c₁.natAbs c₂.natAbs * β :=
    Nat.le_trans (akitaFold_complete c w β hw) (Nat.add_le_add_left (Nat.mul_le_mul_right β h) β)
  if he : akitaFold c₁ u = akitaFold c₁ v then
    exact foldTwoInstances_binding_reduction G q _ (akitaFold c₂ u) (akitaFold c₂ v)
      (fun h => hne (akitaTwoChallenge_injective c₁ c₂ hc u v he h)) h₂
      (bound c₂ (Nat.le_max_right _ _) u hu) (bound c₂ (Nat.le_max_right _ _) v hv)
  else
    exact foldTwoInstances_binding_reduction G q _ (akitaFold c₁ u) (akitaFold c₁ v) he h₁
      (bound c₁ (Nat.le_max_left _ _) u hu) (bound c₁ (Nat.le_max_left _ _) v hv)

/-! ## Fenzi-Safe Instance-Bound Small-Norm Challenge Folding & `TranscriptTree` Extraction -/

/-- Canonical folding instance absorbed *after* relation binding and *before* squeezing
    (`Fenzi ePrint 2026/1838` countermeasure + cross-term commitment binding). -/
abbrev PikkuFoldInstance := ((List Int × List Int) × (ByteArray × ByteArray)) × ByteArray

/-- Bind the materialized circuit/matrix descriptor via `bindRelation` and then absorb
    both commitments `(cm₁, cm₂)`, public evaluations `(y₁, y₂)`, and auxiliary cross-terms
    via `bindInstance` into `.instanceBound` *before* any folding challenge is squeezed. -/
def fenziSafeFoldTranscript (descriptor : ByteArray) (cm₁ cm₂ : List Int)
    (y₁ y₂ crossTerms : ByteArray) : BoundTranscript ((((cm₁, cm₂), (y₁, y₂)), crossTerms) : PikkuFoldInstance) :=
  let trRel := bindRelation "OBEND.PIKKU.BOUNDED/v2" descriptor ByteArray.empty (Transcript.newUnseeded ByteArray.empty)
  bindInstance (((cm₁, cm₂), (y₁, y₂)), crossTerms) trRel

/-- Constructive `0 Classical` statement + cross-term binding extractor for `fenziSafeFoldTranscript`:
    equal `.instanceBound` sponge states either come from the exact same `(descriptor, cm₁, cm₂, y₁, y₂, crossTerms)`
    or constructively produce a bounded `cSHAKE256` collision witness on `fsBindCustomization` or `fsInstanceCustomization`. -/
def extractFenziSafeFoldCollisionOrEq
    (d₁ d₂ : ByteArray) (cm₁A cm₂A cm₁B cm₂B : List Int) (y₁A y₂A ctA y₁B y₂B ctB : ByteArray)
    (hState : (fenziSafeFoldTranscript d₁ cm₁A cm₂A y₁A y₂A ctA).transcript.state =
              (fenziSafeFoldTranscript d₂ cm₁B cm₂B y₁B y₂B ctB).transcript.state) :
    PSum
      (d₁ = d₂ ∧ cm₁A = cm₁B ∧ cm₂A = cm₂B ∧ y₁A = y₁B ∧ y₂A = y₂B ∧ ctA = ctB)
      (PSum
        (Obend.Judge.Computational.HashCollisionWitness
          (Obend.Digest.Cshake256.cshake256Bytes fsInstanceCustomization)
          (Nat.max
            (instancePreimageList
              (bindRelation "OBEND.PIKKU.BOUNDED/v2" d₁ ByteArray.empty (Transcript.newUnseeded ByteArray.empty)).state
              (bindRelation "OBEND.PIKKU.BOUNDED/v2" d₁ ByteArray.empty (Transcript.newUnseeded ByteArray.empty)).stepCount
              (TranscriptEncode.encodeTranscriptBytes (((cm₁A, cm₂A), (y₁A, y₂A)), ctA))).length
            (instancePreimageList
              (bindRelation "OBEND.PIKKU.BOUNDED/v2" d₂ ByteArray.empty (Transcript.newUnseeded ByteArray.empty)).state
              (bindRelation "OBEND.PIKKU.BOUNDED/v2" d₂ ByteArray.empty (Transcript.newUnseeded ByteArray.empty)).stepCount
              (TranscriptEncode.encodeTranscriptBytes (((cm₁B, cm₂B), (y₁B, y₂B)), ctB))).length))
        (Obend.Judge.Computational.HashCollisionWitness
          (Obend.Digest.Cshake256.cshake256Bytes fsBindCustomization)
          (Nat.max
            (bindPreimageList (Transcript.newUnseeded ByteArray.empty).state "OBEND.PIKKU.BOUNDED/v2" d₁ ByteArray.empty).length
            (bindPreimageList (Transcript.newUnseeded ByteArray.empty).state "OBEND.PIKKU.BOUNDED/v2" d₂ ByteArray.empty).length))) :=
  match extractBindInstanceOrEq
      (((cm₁A, cm₂A), (y₁A, y₂A)), ctA) (((cm₁B, cm₂B), (y₁B, y₂B)), ctB)
      (bindRelation "OBEND.PIKKU.BOUNDED/v2" d₁ ByteArray.empty (Transcript.newUnseeded ByteArray.empty))
      (bindRelation "OBEND.PIKKU.BOUNDED/v2" d₂ ByteArray.empty (Transcript.newUnseeded ByteArray.empty)) hState with
  | .inr wInst => .inr (.inl wInst)
  | .inl ⟨hTrRel, hInstEq⟩ =>
    match extractBindRelationOrEq
        (Transcript.newUnseeded ByteArray.empty) (Transcript.newUnseeded ByteArray.empty)
        "OBEND.PIKKU.BOUNDED/v2" "OBEND.PIKKU.BOUNDED/v2"
        d₁ d₂ ByteArray.empty ByteArray.empty (congrArg Transcript.state hTrRel) with
    | .inr wBind => .inr (.inr wBind)
    | .inl ⟨_, _, hdEq, _⟩ =>
      .inl (by
        rcases Prod.mk.inj hInstEq with ⟨hPair, hCt⟩
        rcases Prod.mk.inj hPair with ⟨hCm, hY⟩
        rcases Prod.mk.inj hCm with ⟨hCm1, hCm2⟩
        rcases Prod.mk.inj hY with ⟨hY1, hY2⟩
        exact ⟨hdEq, hCm1, hCm2, hY1, hY2, hCt⟩)

/-- Squeeze a small-norm signed integer challenge `c ∈ [-bChal, bChal]` strictly from an `.instanceBound`
    transcript (preventing both unabsorbed challenge grinding and 64-bit Goldilocks norm explosion). -/
def squeezeBoundedSignedChal (bChal : Nat) (tr : Transcript .instanceBound) : Int × Transcript .instanceBound :=
  let (w, tr') := squeezeGoldilocks tr
  let span := 2 * bChal + 1
  (((w.val % span : Nat) : Int) - (bChal : Int), tr')

theorem squeezeBoundedSignedChal_abs_le (bChal : Nat) (tr : Transcript .instanceBound) :
    (squeezeBoundedSignedChal bChal tr).1.natAbs ≤ bChal := by
  unfold squeezeBoundedSignedChal
  dsimp only
  have hMod : (squeezeGoldilocks tr).1.val % (2 * bChal + 1) < 2 * bChal + 1 :=
    Nat.mod_lt _ (by omega)
  omega

/-- Fold two witnesses using the small-norm signed challenge squeezed from an `.instanceBound` transcript. -/
def boundedFoldFromTranscript {n : Nat} (bChal : Nat) (tr : Transcript .instanceBound)
    (u v : FastIntPoly n) : Int × FastIntPoly n × Transcript .instanceBound :=
  let (c, tr') := squeezeBoundedSignedChal bChal tr
  (c, foldWitness c u v, tr')

theorem boundedFoldFromTranscript_norm_le {n : Nat} (bChal : Nat) (tr : Transcript .instanceBound)
    (u v : FastIntPoly n) (β₁ β₂ : Nat)
    (hu : normInfFast u.coeffs ≤ β₁) (hv : normInfFast v.coeffs ≤ β₂) :
    normInfFast (boundedFoldFromTranscript bChal tr u v).2.1.coeffs ≤ β₁ + bChal * β₂ := by
  unfold boundedFoldFromTranscript
  have hStep := (foldTwoInstances_complete (Sized.ofFn fun (_ : Fin 0) => zeroVec n)
    (squeezeBoundedSignedChal bChal tr).1 u v β₁ β₂ hu hv).2
  have hc := squeezeBoundedSignedChal_abs_le bChal tr
  exact Nat.le_trans hStep (Nat.add_le_add_left (Nat.mul_le_mul_right β₂ hc) β₁)

/-- **`LatticeFold+` Norm-Split / Refresh Gate (`checkNormRefreshGate`)**:
    Ensures positive challenge budget `0 < bChal`, folded norm `β₁ + bChal * β₂ ≤ nextRoundCap`,
    and full 2-special-soundness fork-extraction headroom `2 * bChal * nextRoundCap < sisBetaBound`. -/
@[expose] def checkNormRefreshGate (β₁ β₂ bChal nextRoundCap sisBetaBound : Nat) : Bool :=
  decide (0 < bChal) &&
    decide (β₁ + bChal * β₂ ≤ nextRoundCap) &&
    decide (2 * bChal * nextRoundCap < sisBetaBound)

theorem checkNormRefreshGate_inhabited (β : Nat) :
    checkNormRefreshGate β β 2 (3 * β) (12 * β + 1) = true := by
  unfold checkNormRefreshGate
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem checkNormRefreshGate_sound {n : Nat} {β₁ β₂ bChal nextRoundCap sisBetaBound : Nat}
    (hGate : checkNormRefreshGate β₁ β₂ bChal nextRoundCap sisBetaBound = true)
    (tr : Transcript .instanceBound) (u v : FastIntPoly n)
    (hu : normInfFast u.coeffs ≤ β₁) (hv : normInfFast v.coeffs ≤ β₂) :
    0 < bChal ∧
    normInfFast (boundedFoldFromTranscript bChal tr u v).2.1.coeffs ≤ nextRoundCap ∧
    2 * bChal * nextRoundCap < sisBetaBound := by
  simp only [checkNormRefreshGate, Bool.and_eq_true, decide_eq_true_eq] at hGate
  rcases hGate with ⟨⟨hbPos, hCap⟩, hSis⟩
  exact ⟨hbPos, Nat.le_trans (boundedFoldFromTranscript_norm_le bChal tr u v β₁ β₂ hu hv) hCap, hSis⟩

/-- Canonical length-framed serialization of an `m × n` integer matrix `A` for Fiat–Shamir relation binding. -/
def encodeIntMatrix {m n : Nat} (A : IntMatrix m n) : ByteArray :=
  Obend.Digest.Cshake256.Native.bytesOfList
    (leb128 m ++ leb128 n ++ A.coeffs.toList.flatMap fun row => encodeListField (encodeInts row).data.toList)

/-- Relation-level Fiat–Shamir descriptor binding `(descriptor, A, q, bChal, nextRoundCap, sisBetaBound)`
    before `.instanceBound` challenge squeezing (preventing post-commitment matrix/modulus/bound grinding). -/
def pikkuBoundedDimDesc {m n : Nat} (A : IntMatrix m n)
    (q bChal nextRoundCap sisBetaBound : Nat) (descriptor : ByteArray) : ByteArray :=
  encodeFrame descriptor (encodeIntMatrix A)
    (Obend.Digest.Cshake256.Native.bytesOfList
      (leb128 q ++ leb128 bChal ++ leb128 nextRoundCap ++ leb128 sisBetaBound))

/-- **Fenzi-Safe Bounded-Challenge Fold Verifier (`verifyBoundedChallengeFold`)**:
    Enforces `checkNormRefreshGate`, absorbs `(A, q, bChal, nextRoundCap, sisBetaBound, descriptor,
    cm₁, cm₂, y₁, y₂, crossTerms)` into `.instanceBound`, squeezes `|c| ≤ bChal`, checks
    `‖wFolded‖_∞ ≤ nextRoundCap`, and checks `A · wFolded ≡ cm₁ + c · cm₂ (mod q)`. -/
@[expose] def verifyBoundedChallengeFold {m n : Nat} (A : IntMatrix m n)
    (q β₁ β₂ bChal nextRoundCap sisBetaBound : Nat)
    (descriptor y₁ y₂ crossTerms : ByteArray)
    (cm₁ cm₂ : FastIntPoly m) (wFolded : FastIntPoly n) : Bool :=
  let dimDesc := pikkuBoundedDimDesc A q bChal nextRoundCap sisBetaBound descriptor
  checkNormRefreshGate β₁ β₂ bChal nextRoundCap sisBetaBound &&
    let bTr := fenziSafeFoldTranscript dimDesc cm₁.coeffs.toList cm₂.coeffs.toList y₁ y₂ crossTerms
    let (c, _) := squeezeBoundedSignedChal bChal bTr.transcript
    decide (cm₁.coeffs.size = m && wFolded.coeffs.size = n) &&
      decide (normInfFast wFolded.coeffs ≤ nextRoundCap) &&
      decide (matVecModQ A q wFolded = foldModQ q c cm₁ cm₂)

theorem verifyBoundedChallengeFold_complete {m n : Nat} (A : IntMatrix m n)
    (q β₁ β₂ bChal nextRoundCap sisBetaBound : Nat)
    (descriptor y₁ y₂ crossTerms : ByteArray) (u v : FastIntPoly n)
    (hGate : checkNormRefreshGate β₁ β₂ bChal nextRoundCap sisBetaBound = true)
    (hu : normInfFast u.coeffs ≤ β₁) (hv : normInfFast v.coeffs ≤ β₂) :
    let dimDesc := pikkuBoundedDimDesc A q bChal nextRoundCap sisBetaBound descriptor
    let cm₁ := matVecModQ A q u
    let cm₂ := matVecModQ A q v
    let bTr := fenziSafeFoldTranscript dimDesc cm₁.coeffs.toList cm₂.coeffs.toList y₁ y₂ crossTerms
    let (_, wFolded, _) := boundedFoldFromTranscript bChal bTr.transcript u v
    wFolded.coeffs.size = n ∧ cm₁.coeffs.size = m ∧
    verifyBoundedChallengeFold A q β₁ β₂ bChal nextRoundCap sisBetaBound
      descriptor y₁ y₂ crossTerms cm₁ cm₂ wFolded = true := by
  dsimp only [verifyBoundedChallengeFold, boundedFoldFromTranscript]
  let dimDesc := pikkuBoundedDimDesc A q bChal nextRoundCap sisBetaBound descriptor
  have hSnd := checkNormRefreshGate_sound hGate
    (fenziSafeFoldTranscript dimDesc (matVecModQ A q u).coeffs.toList
      (matVecModQ A q v).coeffs.toList y₁ y₂ crossTerms).transcript u v hu hv
  have hMod := matVecModQ_foldWitness A q
    (squeezeBoundedSignedChal bChal (fenziSafeFoldTranscript dimDesc (matVecModQ A q u).coeffs.toList
      (matVecModQ A q v).coeffs.toList y₁ y₂ crossTerms).transcript).1 u v
  refine ⟨?_, (matVecModQ A q u).size_eq, ?_⟩
  · exact (foldWitness _ u v).size_eq
  · simp only [hGate, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨(matVecModQ A q u).size_eq, (foldWitness _ u v).size_eq⟩, hSnd.2.1⟩, hMod⟩

private theorem fold_fork_elim_mod (c₁ c₂ d₁ d₂ ci₁ ci₂ q : Int)
    (h₁ : d₁ % q = (ci₁ + c₁ * ci₂) % q) (h₂ : d₂ % q = (ci₁ + c₂ * ci₂) % q) :
    (c₂ * d₁ - c₁ * d₂) % q = ((c₂ - c₁) * ci₁) % q := by
  rw [Int.sub_emod, Int.mul_emod c₂ d₁, h₁, ← Int.mul_emod,
      Int.mul_emod c₁ d₂, h₂, ← Int.mul_emod, ← Int.sub_emod]
  congr 1
  simp only [Int.mul_add, Int.sub_mul]
  have hc : c₂ * (c₁ * ci₂) = c₁ * (c₂ * ci₂) := by ac_rfl
  rw [hc]; omega

/-- **2-Special-Soundness Rewinding / Forking Extraction for Bounded-Challenge Fold**:
    Any two folded witnesses `w₁, w₂` accepted at distinct small challenges `c₁ ≠ c₂` (`|cᵢ| ≤ bChal`,
    `‖wᵢ‖_∞ ≤ nextRoundCap`, `matVecModQ A q wᵢ = foldModQ q cᵢ cm₁ cm₂`) extract a relaxed opening
    `Δw = c₂ · w₁ - c₁ · w₂` of `cm₁` with slack `δ = c₂ - c₁ ≠ 0`, `|δ| ≤ 2 * bChal`, and
    `‖Δw‖_∞ ≤ 2 * bChal * nextRoundCap`. -/
theorem verifyBoundedChallengeFold_forking_extract {m n : Nat} (A : IntMatrix m n)
    (q bChal nextRoundCap : Nat) (cm₁ cm₂ : FastIntPoly m)
    (c₁ c₂ : Int) (w₁ w₂ : FastIntPoly n)
    (hcNe : c₁ ≠ c₂) (hc₁ : c₁.natAbs ≤ bChal) (hc₂ : c₂.natAbs ≤ bChal)
    (hw₁ : normInfFast w₁.coeffs ≤ nextRoundCap) (hw₂ : normInfFast w₂.coeffs ≤ nextRoundCap)
    (hRel₁ : matVecModQ A q w₁ = foldModQ q c₁ cm₁ cm₂)
    (hRel₂ : matVecModQ A q w₂ = foldModQ q c₂ cm₁ cm₂) :
    let Δw := intSub (intScale c₂ w₁) (intScale c₁ w₂)
    let δ := c₂ - c₁
    c₁ ≠ c₂ ∧ δ ≠ 0 ∧ δ.natAbs ≤ 2 * bChal ∧
    normInfFast Δw.coeffs ≤ 2 * bChal * nextRoundCap ∧
    matVecModQ A q Δw = Sized.ofFn (fun i => (δ * cm₁.spec i) % (q : Int)) := by
  refine ⟨hcNe, by omega, by omega, ?_, ?_⟩
  · have hb₁ : normInfFast (intScale c₂ w₁).coeffs ≤ bChal * nextRoundCap :=
      Nat.le_trans (normInfFast_scale_le c₂ w₁) (Nat.mul_le_mul hc₂ hw₁)
    have hb₂ : normInfFast (intScale c₁ w₂).coeffs ≤ bChal * nextRoundCap :=
      Nat.le_trans (normInfFast_scale_le c₁ w₂) (Nat.mul_le_mul hc₁ hw₂)
    calc normInfFast (intSub (intScale c₂ w₁) (intScale c₁ w₂)).coeffs
      _ ≤ bChal * nextRoundCap + bChal * nextRoundCap :=
          Nat.le_trans (normInfFast_sub_le _ _) (Nat.add_le_add hb₁ hb₂)
      _ = 2 * bChal * nextRoundCap := by rw [Nat.mul_assoc, ← Nat.two_mul]
  · apply Sized.ext; funext i
    have h₁i := congrArg (fun v => v.spec i) hRel₁
    have h₂i := congrArg (fun v => v.spec i) hRel₂
    simp only [matVecModQ, matVec, foldModQ, Sized.spec_ofFn] at h₁i h₂i ⊢
    rw [dot_sub, dot_scale, dot_scale]
    exact fold_fork_elim_mod c₁ c₂ _ _ _ _ (q : Int) h₁i h₂i

/-- Composes `checkNormRefreshGate` directly with `verifyBoundedChallengeFold_forking_extract`:
    passing the runtime norm-refresh gate guarantees `normInfFast Δw.coeffs < sisBetaBound`! -/
theorem verifyBoundedChallengeFold_forking_within_sisBeta {m n : Nat} (A : IntMatrix m n)
    (q β₁ β₂ bChal nextRoundCap sisBetaBound : Nat) (cm₁ cm₂ : FastIntPoly m)
    (c₁ c₂ : Int) (w₁ w₂ : FastIntPoly n)
    (hGate : checkNormRefreshGate β₁ β₂ bChal nextRoundCap sisBetaBound = true)
    (hcNe : c₁ ≠ c₂) (hc₁ : c₁.natAbs ≤ bChal) (hc₂ : c₂.natAbs ≤ bChal)
    (hw₁ : normInfFast w₁.coeffs ≤ nextRoundCap) (hw₂ : normInfFast w₂.coeffs ≤ nextRoundCap)
    (hRel₁ : matVecModQ A q w₁ = foldModQ q c₁ cm₁ cm₂)
    (hRel₂ : matVecModQ A q w₂ = foldModQ q c₂ cm₁ cm₂) :
    let Δw := intSub (intScale c₂ w₁) (intScale c₁ w₂)
    normInfFast Δw.coeffs < sisBetaBound ∧
    matVecModQ A q Δw = Sized.ofFn (fun i => ((c₂ - c₁) * cm₁.spec i) % (q : Int)) := by
  have hExt := verifyBoundedChallengeFold_forking_extract A q bChal nextRoundCap cm₁ cm₂ c₁ c₂ w₁ w₂
    hcNe hc₁ hc₂ hw₁ hw₂ hRel₁ hRel₂
  simp only [checkNormRefreshGate, Bool.and_eq_true, decide_eq_true_eq] at hGate
  exact ⟨Nat.lt_of_le_of_lt hExt.2.2.2.1 hGate.2, hExt.2.2.2.2⟩

/-- **Quantitative Parallel Challenge Soundness / Anti-Grinding Bound (`parallelBoundedChalHitProb_le`)**:
    Sampling $k$ small-norm challenges from `[-bChal, bChal]^k` (`uniformVecDist bChal target.length`)
    hits any specific bad challenge vector `target` (e.g. a cheating root in each parallel slot)
    with probability at most $(2 \cdot b_{\text{chal}} + 1)^{-k}$ (`(2*bChal+1)^(-k)` amplification). -/
theorem parallelBoundedChalHitProb_le (bChal : Nat) :
    ∀ (target : List Int),
      RatProb.le
        ((uniformVecDist bChal target.length).probEvent (· == target))
        ⟨1, (2 * bChal + 1) ^ target.length, Nat.pow_pos (by omega)⟩
  | [] => by
    unfold uniformVecDist FinDist.pure FinDist.probEvent RatProb.le
    simp [FinDist.totalWeight, eventMass, weightSum]
  | t :: ts => by
    have hHead0 : RatProb.le ((uniformIntervalDist bChal).probEvent (· == t)) ⟨1, 2 * bChal + 1, by omega⟩ := by
      unfold uniformIntervalDist; rw [FinDist.probEvent_map]
      unfold FinDist.uniform FinDist.probEvent FinDist.totalWeight RatProb.le
      dsimp only [Function.comp_def]; rw [uniform_weightSum, uniform_eventMass, List.length_range]
      apply Nat.mul_le_mul_right
      have hNodupOne : ∀ (ks : List Nat), ks.Nodup → (ks.filter (fun k : Nat => ((k : Int) - bChal) == t)).length ≤ 1 := by
        intro ks; induction ks with
        | nil => intros; exact Nat.zero_le 1
        | cons k ks ih =>
          intro hNd; rcases hNd with _ | ⟨hNot, hNdR⟩; dsimp only [List.filter]
          by_cases hk : ((k : Int) - bChal) = t
          · simp only [beq_iff_eq.2 hk, List.length_cons]
            have hEmpty : ks.filter (fun j : Nat => ((j : Int) - bChal) == t) = [] := by
              rw [List.filter_eq_nil_iff]; intro j hj; simp only [beq_iff_eq]; intro hjEq
              exact hNot j hj (by omega)
            simp [hEmpty]
          · simp [beq_eq_false_iff_ne.2 hk, ih hNdR]
      exact hNodupOne _ List.nodup_range
    have hHead := hHead0
    have ih := parallelBoundedChalHitProb_le bChal ts
    simp only [List.length_cons, uniformVecDist, FinDist.probEvent_map]
    unfold FinDist.prod
    unfold RatProb.le FinDist.probEvent FinDist.totalWeight at ih hHead
    unfold RatProb.le FinDist.probEvent FinDist.bind FinDist.totalWeight
    dsimp only at ih hHead ⊢
    rw [bindRaw_weightSum, Nat.pow_succ]
    have hTailLe : ∀ a, eventMass ((· == (t :: ts)) ∘ fun q : Int × List Int => q.1 :: q.2)
          ((uniformVecDist bChal ts.length).map (fun b => (a, b))).support * ((2 * bChal + 1) ^ ts.length) ≤
        (if a == t then 1 else 0) * (uniformVecDist bChal ts.length).totalWeight := by
      intro a; by_cases ha : a = t
      · subst ha
        have hEvEq : ((· == (a :: ts)) ∘ fun q : Int × List Int => q.1 :: q.2) ∘ (fun b => (a, b)) = (· == ts) := by
          funext b; simp [Function.comp_def]
        have hMp := FinDist.probEvent_map (fun b => (a, b)) (uniformVecDist bChal ts.length)
          ((· == (a :: ts)) ∘ fun q : Int × List Int => q.1 :: q.2)
        rw [hEvEq] at hMp
        have hCross : eventMass ((· == (a :: ts)) ∘ fun q => q.1 :: q.2)
            ((uniformVecDist bChal ts.length).map (fun b => (a, b))).support =
            eventMass (· == ts) (uniformVecDist bChal ts.length).support :=
          congrArg RatProb.num hMp
        rw [hCross]; simp only [beq_self_eq_true, ↓reduceIte, Nat.one_mul]
        simpa [FinDist.totalWeight] using ih
      · simp only [beq_eq_false_iff_ne.2 ha, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]
        rw [Nat.le_zero, Nat.mul_eq_zero]
        left
        let ev : Int × List Int → Bool := ((· == (t :: ts)) ∘ fun q => q.1 :: q.2)
        have hZero : ∀ (xs : List ((Int × List Int) × Nat)),
            (∀ p ∈ xs, p.1.1 = a) → eventMass ev xs = 0 := by
          intro xs; induction xs with
          | nil => intros; rfl
          | cons hd rest ihZ =>
            rcases hd with ⟨⟨a', b'⟩, w'⟩; intro hAll
            have ha' : a' = a := hAll _ List.mem_cons_self; subst ha'
            have hF : ev (a', b') = false := beq_eq_false_iff_ne.2 (fun h => ha (List.cons.inj h).1)
            dsimp only [eventMass]; rw [hF]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
            exact ihZ (fun p hp => hAll p (List.mem_cons_of_mem _ hp))
        apply hZero
        intro p hp
        unfold FinDist.map at hp
        rcases List.mem_map.1 hp with ⟨⟨_, _⟩, _, rfl⟩
        rfl
    have auxB : ∀ (zs : List (Int × Nat)),
        eventMass ((· == (t :: ts)) ∘ fun q : Int × List Int => q.1 :: q.2)
          (bindRaw zs (fun a => (uniformVecDist bChal ts.length).map (fun b => (a, b)))).1 *
          ((2 * bChal + 1) ^ ts.length) ≤
        eventMass (· == t) zs *
          (bindRaw zs (fun a => (uniformVecDist bChal ts.length).map (fun b => (a, b)))).2 := by
      intro zs; induction zs with
      | nil => simp [bindRaw, eventMass]
      | cons hd zs ihZ =>
        rcases hd with ⟨a, u⟩
        simp only [bindRaw, eventMass_append, eventMass_scaleSupport, eventMass]
        let subD := (uniformVecDist bChal ts.length).map (fun b => (a, b))
        let E1 := eventMass ((· == (t :: ts)) ∘ fun q : Int × List Int => q.1 :: q.2) subD.support
        let T1 := weightSum subD.support
        let B1 := eventMass ((· == (t :: ts)) ∘ fun q : Int × List Int => q.1 :: q.2)
                    (bindRaw zs (fun x => (uniformVecDist bChal ts.length).map (fun b => (x, b)))).1
        let D1 := (bindRaw zs (fun x => (uniformVecDist bChal ts.length).map (fun b => (x, b)))).2
        have hT1 : T1 = (uniformVecDist bChal ts.length).totalWeight := FinDist.weightSum_map _ _
        have hStep1 := hTailLe a
        rw [← hT1] at hStep1
        rw [Nat.add_mul]
        have p1 : u * D1 * E1 * ((2 * bChal + 1) ^ ts.length) ≤ (if a == t then u else 0) * (T1 * D1) := by
          calc u * D1 * E1 * ((2 * bChal + 1) ^ ts.length)
            _ = u * D1 * (E1 * ((2 * bChal + 1) ^ ts.length)) := by ac_rfl
            _ ≤ u * D1 * ((if a == t then 1 else 0) * T1) := Nat.mul_le_mul_left _ hStep1
            _ = (if a == t then u else 0) * (T1 * D1) := by cases (a == t) <;> simp <;> ac_rfl
        have p2 : T1 * B1 * ((2 * bChal + 1) ^ ts.length) ≤ eventMass (· == t) zs * (T1 * D1) := by
          calc T1 * B1 * ((2 * bChal + 1) ^ ts.length)
            _ = T1 * (B1 * ((2 * bChal + 1) ^ ts.length)) := by ac_rfl
            _ ≤ T1 * (eventMass (· == t) zs * D1) := Nat.mul_le_mul_left _ ihZ
            _ = eventMass (· == t) zs * (T1 * D1) := by ac_rfl
        calc u * D1 * E1 * ((2 * bChal + 1) ^ ts.length) + T1 * B1 * ((2 * bChal + 1) ^ ts.length)
          _ ≤ (if a == t then u else 0) * (T1 * D1) + eventMass (· == t) zs * (T1 * D1) := Nat.add_le_add p1 p2
          _ = ((if a == t then u else 0) + eventMass (· == t) zs) * (T1 * D1) := by rw [Nat.add_mul]
    let zs0 := (uniformIntervalDist bChal).support
    let D0 := (bindRaw zs0 (fun a => (uniformVecDist bChal ts.length).map (fun b => (a, b)))).2
    calc eventMass ((· == (t :: ts)) ∘ fun q : Int × List Int => q.1 :: q.2)
          (bindRaw zs0 (fun a => (uniformVecDist bChal ts.length).map (fun b => (a, b)))).1 *
          (((2 * bChal + 1) ^ ts.length) * (2 * bChal + 1))
      _ = (eventMass ((· == (t :: ts)) ∘ fun q : Int × List Int => q.1 :: q.2)
            (bindRaw zs0 (fun a => (uniformVecDist bChal ts.length).map (fun b => (a, b)))).1 *
            ((2 * bChal + 1) ^ ts.length)) * (2 * bChal + 1) := by ac_rfl
      _ ≤ (eventMass (· == t) zs0 * D0) * (2 * bChal + 1) := Nat.mul_le_mul_right _ (auxB zs0)
      _ = (eventMass (· == t) zs0 * (2 * bChal + 1)) * D0 := by ac_rfl
      _ ≤ (1 * weightSum zs0) * D0 := Nat.mul_le_mul_right D0 hHead
      _ = 1 * (weightSum zs0 * D0) := by ac_rfl

/-- Convert `IntMatrix m n` to `List (List Int)` for `GameSoundness.TranscriptTree` extraction. -/
def intMatrixToLists {m n : Nat} (A : IntMatrix m n) : List (List Int) :=
  A.coeffs.toList.map (fun row => row.coeffs.toList)

theorem intMatrixToLists_rows {m n : Nat} (A : IntMatrix m n) :
    ∀ row ∈ intMatrixToLists A, row.length = n := by
  intro row hMem
  rcases List.mem_map.1 hMem with ⟨r, _, rfl⟩
  simpa using r.size_eq

/-- Multi-round `TranscriptTree` extraction bridge for `PikkuFoldLayered`:
    any depth-$d$ binary forking tree over `intMatrixToLists A` with per-round challenge bound `bChal`
    and leaf witness bound `b₀` satisfying `normAtDepth bChal d b₀ < sisBetaBound` constructively
    extracts a relaxed witness `(w, δ)` with `δ ≠ 0`, `Nat.Coprime δ.natAbs q`, and `‖w‖_∞ < sisBetaBound`. -/
theorem pikkuForkingTree_extract_within_sisBeta {m n : Nat}
    (A : IntMatrix m n) (q bChal b₀ sisBetaBound : Nat)
    {d : Nat} (tr : TranscriptTree d)
    (hValid : ValidForkingTree q n bChal b₀ (intMatrixToLists A) tr)
    (hGate : normAtDepth bChal d b₀ < sisBetaBound) :
    let (w, δ) := extractFromForkingTree tr
    w.length = n ∧ δ ≠ 0 ∧ δ.natAbs ≤ slackAtDepth bChal d ∧
    (∀ x ∈ w, x.natAbs < sisBetaBound) ∧
    (∀ p ∈ List.zip (intMatrixToLists A) tr.rootCm, (dotInt p.1 w - δ * p.2) % (q : Int) = 0) ∧
    Nat.Coprime δ.natAbs q := by
  have hS := extractFromForkingTree_sound q n bChal b₀ (intMatrixToLists A) (intMatrixToLists_rows A) tr hValid
  have hB := extractFromForkingTree_within_sisBeta q n bChal b₀ sisBetaBound (intMatrixToLists A) (intMatrixToLists_rows A) tr hValid hGate
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hB, hS.2.2.2.2.1, hS.2.2.2.2.2⟩

end Obend.Crypto.Fast
