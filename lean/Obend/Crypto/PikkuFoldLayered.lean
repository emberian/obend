module
public import Obend.Crypto.FastRing
public import Obend.Crypto.Transcript

public section
namespace Obend.Crypto.Fast

/-- Sparse ternary rows contain only signed unit entries; absence represents zero. -/
structure SignedIndex (n : Nat) where
  col : Fin n
  negative : Bool
  deriving DecidableEq

abbrev TernaryMatrix (rows cols : Nat) := Sized (Array (SignedIndex cols)) rows

@[expose] def signedValue (negative : Bool) (x : Int) : Int := if negative then -x else x

@[expose] def sparseRow {n : Nat} (row : Array (SignedIndex n)) (w : FastIntPoly n) : Int :=
  sumInt row.size fun j => if h : j < row.size then
    signedValue row[j].negative (w.spec row[j].col) else 0

/-- Only additions/subtractions of selected coefficients; no integer multiplications. -/
@[expose] def sparseRowFast {n : Nat} (row : Array (SignedIndex n)) (w : FastIntPoly n) : Int :=
  row.foldl (fun acc e => acc + signedValue e.negative (w.spec e.col)) 0

theorem sparseRowFast_eq_sparseRow {n : Nat} (row : Array (SignedIndex n)) (w : FastIntPoly n) :
    sparseRowFast row w = sparseRow row w := by
  apply Array.foldl_induction (motive := fun k acc => acc = sumInt k (fun j =>
    if h : j < row.size then signedValue row[j].negative (w.spec row[j].col) else 0)) rfl
  intro i acc hacc
  simp only [sumInt, hacc, i.isLt, ↓reduceDIte]
  rfl

@[expose] def applyTernary {m n : Nat} (M : TernaryMatrix m n) (w : FastIntPoly n) : FastIntPoly m :=
  Sized.ofFn fun i => sparseRowFast (M.spec i) w

@[expose] def rowWeight {m n : Nat} (M : TernaryMatrix m n) : Nat :=
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
@[expose] def applyKroneckerTernaryFast {m n : Nat} (r : Nat) (M : TernaryMatrix m n)
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
@[expose] def applyKroneckerTernary {m n : Nat} (r : Nat) (M : TernaryMatrix m n)
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

@[expose] def Layers.apply {n m : Nat} : Layers n m → FastIntPoly n → FastIntPoly m
  | .done _, w => w
  | .step M rest, w => rest.apply (applyTernary M w)
@[expose] def Layers.weight {n m : Nat} : Layers n m → Nat
  | .done _ => 1
  | .step M rest => rest.weight * rowWeight M
@[expose] def Layers.length {n m : Nat} : Layers n m → Nat
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

@[expose] def Layers.uniform {n m : Nat} (K : Nat) : Layers n m → Prop
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
@[expose] def encodeInts {n : Nat} (w : FastIntPoly n) : ByteArray :=
  Obend.Digest.Cshake256.Native.bytesOfList
    (leb128 n ++ w.coeffs.toList.flatMap fun x =>
      (if x < 0 then [1] else [0]) ++ leb128 x.natAbs)

/-- The verifier supplies the materialized matrix descriptor and both public instances. -/
def foldTranscript (descriptor cm₁ y₁ cm₂ y₂ : ByteArray) : Transcript .relationBound :=
  bindRelation "OBEND.PIKKU/v1" descriptor
    (encodeFrame (encodeFrame cm₁ y₁ ByteArray.empty) (encodeFrame cm₂ y₂ ByteArray.empty) ByteArray.empty)
    (Transcript.newUnseeded ByteArray.empty)

/-- No auxiliary commitment is generated by this fold. -/
def foldFromTranscript {n : Nat} (tr : Transcript .relationBound) (u v : FastIntPoly n) :
    FastIntPoly n × Transcript .relationBound :=
  let (c, tr') := squeezeGoldilocks tr
  (foldWitness (c.val : Int) u v, tr')

@[expose] def splitLo {m : Nat} (w : FastIntPoly (2*m)) : FastIntPoly m :=
  Sized.ofFn fun i => w.spec ⟨i.val, by omega⟩
@[expose] def splitHi {m : Nat} (w : FastIntPoly (2*m)) : FastIntPoly m :=
  Sized.ofFn fun i => w.spec ⟨m + i.val, by omega⟩
@[expose] def akitaFold {m : Nat} (c : Int) (w : FastIntPoly (2*m)) : FastIntPoly m :=
  foldWitness c (splitLo w) (splitHi w)

@[expose] def matrixLo {m n : Nat} (A : IntMatrix m (2*n)) : IntMatrix m n :=
  Sized.ofFn fun i => splitLo (A.spec i)
@[expose] def matrixHi {m n : Nat} (A : IntMatrix m (2*n)) : IntMatrix m n :=
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

@[expose] def foldModQ {m : Nat} (q : Nat) (c : Int) (lo hi : FastIntPoly m) : FastIntPoly m :=
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

end Obend.Crypto.Fast
