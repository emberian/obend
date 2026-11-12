module
public import Obend.Crypto.BinaryTower256
public import Obend.Crypto.Transcript
public import Obend.Crypto.CanopyReduce
public import Obend.Hardware.PipelinedZkCrypto
public import Obend.Judge.Class
import all Obend.Crypto.Multilinear
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.BinaryTower256
import all Obend.Hardware.PipelinedZkCrypto

public section
namespace Obend.Crypto.BinarySpartanAndShout
open Obend.Crypto.BinaryTower256 Obend.Digest.HashBytes Obend.Digest.Cshake256
set_option autoImplicit false

/-! Exact sampling budgets. These certify independent uniform coordinate queries;
they do not turn a proximity test into a polynomial commitment by assumption. -/
inductive FieldKind where
  | binaryAdditive | primeExtension
  deriving DecidableEq, Repr
inductive ProximityRegime where
  | uniqueDecoding | johnsonBound | capacityMca
  deriving DecidableEq, Repr
structure PcsCodeParams where
  fieldKind : FieldKind
  logRateInv : Nat
  numQueries : Nat
  logDomainSize : Nat
  regime : ProximityRegime
  targetSecurityBits : Nat
  distanceNumerator : Nat
  distanceDenominator : Nat
  deriving DecidableEq, Repr

def computeSoundnessBitsFloor (p : PcsCodeParams) : Nat :=
  Nat.log2 (p.distanceDenominator ^ p.numQueries /
    (p.distanceDenominator - p.distanceNumerator) ^ p.numQueries)

/-- Strict UDR, or the strict Johnson inequality `(1-δ)² > R` for prime domains.
Capacity requires a separate theorem about the code; this guard never assumes it. -/
@[expose] def regimeDistance (p : PcsCodeParams) : Prop :=
  match p.regime with
  | .uniqueDecoding => 2 * p.distanceNumerator * 2^p.logRateInv <
      p.distanceDenominator * (2^p.logRateInv - 1)
  | .johnsonBound => p.fieldKind = .primeExtension ∧
      p.distanceDenominator^2 <
        (p.distanceDenominator - p.distanceNumerator)^2 * 2^p.logRateInv
  | .capacityMca => False
instance (p : PcsCodeParams) : Decidable (regimeDistance p) := by
  unfold regimeDistance; cases p.regime <;> infer_instance

@[expose] def PcsSoundnessRegime (p : PcsCodeParams) : Prop :=
  0 < p.logRateInv ∧ p.logRateInv ≤ p.logDomainSize ∧
  0 < p.distanceNumerator ∧ p.distanceNumerator < p.distanceDenominator ∧
  regimeDistance p ∧
  (p.distanceDenominator - p.distanceNumerator)^p.numQueries * 2^p.targetSecurityBits ≤
    p.distanceDenominator^p.numQueries
instance (p : PcsCodeParams) : Decidable (PcsSoundnessRegime p) := by
  unfold PcsSoundnessRegime; infer_instance

def checkPcsSoundnessRegime (p : PcsCodeParams) : Bool := decide (PcsSoundnessRegime p)

theorem checkPcsSoundnessRegime_iff (p : PcsCodeParams) :
    checkPcsSoundnessRegime p = true ↔ PcsSoundnessRegime p := by
  simp [checkPcsSoundnessRegime]

theorem binaryAdditive_refuses_beyond_udr (p : PcsCodeParams)
    (hf : p.fieldKind = .binaryAdditive) (hr : p.regime ≠ .uniqueDecoding) :
    checkPcsSoundnessRegime p = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hd := ((checkPcsSoundnessRegime_iff p).mp h).2.2.2.2.1
  cases he : p.regime <;> simp_all [regimeDistance]

theorem pcs_sampling_bound (p : PcsCodeParams) (h : checkPcsSoundnessRegime p = true) :
    (p.distanceDenominator - p.distanceNumerator)^p.numQueries * 2^p.targetSecurityBits ≤
      p.distanceDenominator^p.numQueries :=
  ((checkPcsSoundnessRegime_iff p).mp h).2.2.2.2.2

/-- Rate 1/4, distance 1/4 strictly below 3/8, 320 queries for 128 bits. -/
def binaryUdrPcsParams : PcsCodeParams :=
  ⟨.binaryAdditive, 2, 320, 20, .uniqueDecoding, 128, 1, 4⟩
/-- A conservative Goldilocks extension profile, within the prime Johnson radius. -/
def primeGoldilocksPcsParams : PcsCodeParams :=
  ⟨.primeExtension, 2, 320, 20, .johnsonBound, 128, 1, 4⟩

theorem binaryUdrPcsParams_valid (u : Unit) :
    checkPcsSoundnessRegime binaryUdrPcsParams = true := by cases u; decide +kernel
theorem primeGoldilocksPcsParams_valid (u : Unit) :
    checkPcsSoundnessRegime primeGoldilocksPcsParams = true := by cases u; decide +kernel

/-- The code domain is exactly the Canopy row domain, not an unrelated parameter. -/
def canopyPcsParams (cfg : Fast.Canopy.Config) : PcsCodeParams :=
  { primeGoldilocksPcsParams with logDomainSize := cfg.bottomDepth + cfg.capDepth }

/-- In F₄ the received word x² agrees on two points with each of the three
nonzero-slope lines a*x. The three agreement sets overlap at zero. At rate 1/2
these are distinct degree-1 codewords at distance 1/2, outside UDR (1/4).
This refutes naive uniqueness/correlated-agreement assumptions there; it does
not purport to refute every list-decoding theorem for binary codes. -/
def smallSubfield : List (TowerElem 1) :=
  [(false,false), (true,false), (false,true), (true,true)]
def subfieldAgreement (a : TowerElem 1) : List (TowerElem 1) :=
  smallSubfield.filter fun x => decide (towerMul 1 x x = towerMul 1 a x)

theorem subfield_agreement_counterexample (u : Unit) :
    (subfieldAgreement (true,false)).length = 2 ∧
    (subfieldAgreement (false,true)).length = 2 ∧
    (subfieldAgreement (true,true)).length = 2 ∧
    towerMul 1 (true,false) (true,false) ≠ towerMul 1 (false,true) (true,false) ∧
    towerMul 1 (false,true) (true,false) ≠ towerMul 1 (true,true) (true,false) := by
  cases u; decide +kernel

/-! Full framed sparse statements. All indices, dimensions, values, public IO,
and the entire witness commitment are absorbed before any challenge. -/
abbrev F := Tower128
local notation "𝟘" => towerZero 7
local notation "𝟙" => towerOne 7
local infixl:65 " ⊞ " => towerAdd 7
local infixl:70 " ⊠ " => towerMul 7

structure SparseEntry where
  row : Nat
  col : Nat
  value : F
  deriving DecidableEq
structure R1csInstance where
  logRows : Nat
  numCols : Nat
  a : List SparseEntry
  b : List SparseEntry
  c : List SparseEntry
  publicIO : List (Nat × F)
  deriving DecidableEq

def encodeField (x : F) : ByteArray := Native.bytesOfList (be 16 (packTower 7 x).toNat)
theorem encodeField_injective {x y : F} (h : encodeField x = encodeField y) : x = y := by
  have hb := congrArg (fun b => b.data.toList) h
  simp only [encodeField, Native.bytesOfList_toList] at hb
  have hp : 256^16 = 2^128 := by decide
  have hn := be_injective (by rw [hp]; exact (packTower 7 x).isLt)
    (by rw [hp]; exact (packTower 7 y).isLt) hb
  exact packTower_injective 7 x y (BitVec.eq_of_toNat_eq hn)
instance : LawfulTranscriptEncode F where
  encodeTranscriptBytes := encodeField
  encodeTranscriptBytes_injective := encodeField_injective

/-- Count plus independently length-framed elements, including empty lists. -/
def encodeItems {α : Type} [TranscriptEncode α] (xs : List α) : List UInt8 :=
  leb128 xs.length ++ xs.flatMap (fun x => encodeListField
    (TranscriptEncode.encodeTranscriptBytes x).data.toList)

theorem encodeItems_injective {α : Type} [LawfulTranscriptEncode α]
    {xs ys : List α} (h : encodeItems xs = encodeItems ys) : xs = ys := by
  obtain ⟨hl, ht⟩ := leb128_prefix_inj h
  clear h
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp only [List.length_nil, List.length_cons] at hl; omega
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons] at hl; omega
    | cons y ys =>
      obtain ⟨hx, hs⟩ := encodeListField_prefix_inj ht
      have he : x = y := LawfulTranscriptEncode.encodeTranscriptBytes_injective
        (byteArray_eq_of_toList_eq hx)
      have heq : xs = ys := ih (by simpa using hl) hs
      rw [he, heq]

instance {α : Type} [LawfulTranscriptEncode α] : LawfulTranscriptEncode (List α) where
  encodeTranscriptBytes xs := Native.bytesOfList (encodeItems xs)
  encodeTranscriptBytes_injective h := encodeItems_injective (by
    simpa only [Native.bytesOfList_toList] using congrArg (fun b => b.data.toList) h)
instance : LawfulTranscriptEncode SparseEntry where
  encodeTranscriptBytes e := TranscriptEncode.encodeTranscriptBytes (e.row, e.col, e.value)
  encodeTranscriptBytes_injective {x y} h := by
    have he : (x.row, x.col, x.value) = (y.row, y.col, y.value) :=
      LawfulTranscriptEncode.encodeTranscriptBytes_injective h
    cases x; cases y; cases he; rfl

def encodeR1csInstance (i : R1csInstance) : ByteArray :=
  encodeFrame "binary-spartan-shout@1".toUTF8
    (TranscriptEncode.encodeTranscriptBytes (i.logRows, i.numCols, i.a, i.b, i.c, i.publicIO)) ByteArray.empty
theorem encodeR1csInstance_injective {i j : R1csInstance}
    (h : encodeR1csInstance i = encodeR1csInstance j) : i = j := by
  have he : (i.logRows, i.numCols, i.a, i.b, i.c, i.publicIO) =
      (j.logRows, j.numCols, j.a, j.b, j.c, j.publicIO) :=
    LawfulTranscriptEncode.encodeTranscriptBytes_injective (encodeFrame_injective h).2.1
  cases i; cases j; cases he; rfl
instance : LawfulTranscriptEncode R1csInstance where
  encodeTranscriptBytes := encodeR1csInstance
  encodeTranscriptBytes_injective := encodeR1csInstance_injective

instance : TranscriptChallenge F where
  encodeElem := encodeField
  squeezeChallenge tr :=
    let (bytes, next) := squeezeChallenge256 tr
    (unpackTower 7 (BitVec.ofNat 128 (ofBE (bytes.val.data.toList.take 16))), next)

def witnessCommitment (z : Array F) : Digest32 :=
  evalDigest32 deployedCanopyHash32 (encodeItems z.toList)
variable (context : Transcript .relationBound)

def absorbR1csInstance (i : R1csInstance) (z : Array F) :
    BoundTranscript (i, (witnessCommitment z).bytes) :=
  bindInstance (i, (witnessCommitment z).bytes) context

/-- Every commitment bit and every sparse entry participates in the binding reduction. -/
theorem r1cs_binding_or_collision (i j : R1csInstance) (z w : Array F)
    (h : (absorbR1csInstance context i z).transcript.state =
      (absorbR1csInstance context j w).transcript.state) :
    i = j ∨ Collision (cshake256Bytes fsInstanceCustomization) := by
  rcases bindInstance_binds_or_collides h with he | hc
  · exact .inl (congrArg Prod.fst he.2)
  · exact .inr (boundedCollision_imp_collision hc)

/-- A sparse row is a list spec; the execution path traverses an Array once. -/
def sparseRowSpec (entries : List SparseEntry) (z : Array F) (row : Nat) : F :=
  entries.foldl (fun acc e => if e.row = row then acc ⊞ (e.value ⊠ z[e.col]?.getD 𝟘) else acc) 𝟘
def sparseRowExec (entries : Array SparseEntry) (z : Array F) (row : Nat) : F :=
  entries.foldl (fun acc e => if e.row = row then acc ⊞ (e.value ⊠ z[e.col]?.getD 𝟘) else acc) 𝟘
theorem sparseRow_exec_eq_spec (entries : Array SparseEntry) (z : Array F) (row : Nat) :
    sparseRowExec entries z row = sparseRowSpec entries.toList z row := by
  simp only [sparseRowExec, sparseRowSpec, Array.foldl_toList]

def discrepancy (i : R1csInstance) (z : Array F) (row : Nat) : F :=
  (sparseRowExec i.a.toArray z row ⊠ sparseRowExec i.b.toArray z row) ⊞
    sparseRowExec i.c.toArray z row

def R1csSatisfied (i : R1csInstance) (z : Array F) : Prop :=
  ∀ row, row < 2^i.logRows →
    sparseRowSpec i.a z row ⊠ sparseRowSpec i.b z row = sparseRowSpec i.c z row

theorem discrepancy_zero_iff (i : R1csInstance) (z : Array F) (row : Nat) :
    discrepancy i z row = 𝟘 ↔
      sparseRowSpec i.a z row ⊠ sparseRowSpec i.b z row = sparseRowSpec i.c z row := by
  simp only [discrepancy, sparseRow_exec_eq_spec]
  constructor
  · intro h
    have hh := congrArg (towerAdd 7 (sparseRowSpec i.c z row)) h
    simpa only [towerAdd_comm 7 (sparseRowSpec i.c z row), towerAdd_assoc,
      towerAdd_self_zero, towerAdd_zero, towerZero_add] using hh
  · intro h; rw [h, towerAdd_self_zero]

private theorem array_get_ofFn {α : Type} {n : Nat} (f : Fin n → α) (j : Nat)
    (hj : j < (Array.ofFn f).size) : (Array.ofFn f)[j] = f ⟨j, by simpa only [Array.size_ofFn] using hj⟩ :=
  Fast.arrayOfFn_get f ⟨j, by simpa only [Array.size_ofFn] using hj⟩
attribute [local simp] array_get_ofFn

/-! Tensor one-hot lookup. The address contains d bits; no field-valued unit-sum
is ever mistaken for integer Hamming weight one. -/
def tensorWeight (address index : List Bool) : F := eqPoly (address.map (bitElem (R := F))) index

theorem tensorWeight_kronecker (address index : List Bool) (h : address.length = index.length) :
    tensorWeight address index = if address = index then 𝟙 else 𝟘 :=
  eqPoly_kronecker address index h

def bitAddress : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitAddress bs

theorem bitAddress_lt (bs : List Bool) : bitAddress bs < 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp [bitAddress, List.length_cons, Nat.pow_succ] <;> omega

def checkTensor (address : List Bool) (weights : Array F) : Bool :=
  decide (weights.size = 2^address.length) &&
    (Array.ofFn fun j : Fin weights.size =>
      decide (weights[j.val] = if j.val = bitAddress address then 𝟙 else 𝟘)).all id

def checkBinaryShout (table : Array F) (address : List Bool) (weights : Array F) (value : F) : Bool :=
  decide (table.size = 2^address.length) && checkTensor address weights &&
    decide (innerProd weights.toList table.toList = value)

theorem checkTensor_iff (address : List Bool) (weights : Array F) :
    checkTensor address weights = true ↔ weights.size = 2^address.length ∧
      ∀ j (hj : j < weights.size), weights[j] = if j = bitAddress address then 𝟙 else 𝟘 := by
  simp only [checkTensor, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun j hj => ?_⟩
    have hh := Array.all_eq_true.mp h j (by simpa using hj)
    simpa only [array_get_ofFn, id_eq, decide_eq_true_eq] using hh
  · rintro ⟨hs, h⟩
    refine ⟨hs, Array.all_eq_true.mpr ?_⟩
    intro j hj
    simpa only [array_get_ofFn, id_eq, decide_eq_true_eq] using h j (by simpa using hj)

private theorem innerProd_unit (xs ys : List F) (a : Nat)
    (hlen : xs.length = ys.length) (ha : a < xs.length)
    (hx : ∀ j (hj : j < xs.length), xs[j] = if j = a then 𝟙 else 𝟘) :
    innerProd xs ys = ys[a]'(by omega) := by
  induction xs generalizing ys a with
  | nil => simp at ha
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      cases a with
      | zero =>
        have h0 := hx 0 (by simp)
        simp only [List.getElem_cons_zero, ite_true] at h0
        have hz : innerProd xs ys = 𝟘 := by
          have aux (us vs : List F) (hu : ∀ j (hj : j < us.length), us[j] = 𝟘) :
              innerProd us vs = 𝟘 := by
            induction us generalizing vs with
            | nil => rfl
            | cons u us ih =>
              cases vs with
              | nil => rfl
              | cons v vs =>
                have hu0 := hu 0 (by simp)
                simp only [List.getElem_cons_zero] at hu0
                change (u ⊠ v) ⊞ innerProd us vs = 𝟘
                rw [hu0, towerZero_mul, towerZero_add]
                exact ih vs (fun j hj => hu (j+1) (by simp; omega))
          apply aux
          intro j hj
          have hh := hx (j+1) (by simp; omega)
          change xs[j] = (if j+1 = 0 then 𝟙 else 𝟘) at hh
          simpa using hh
        change (x ⊠ y) ⊞ innerProd xs ys = y
        rw [h0, towerOne_mul, hz, towerAdd_zero]
      | succ a =>
        have h0 := hx 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.zero_ne_add_one, ite_false] at h0
        have hay : a < ys.length := by simp only [List.length_cons] at hlen ha; omega
        change (x ⊠ y) ⊞ innerProd xs ys = ys[a]'hay
        rw [h0, towerZero_mul, towerZero_add]
        apply ih ys a (by simpa using hlen) (by simp at ha; omega)
        intro j hj
        have hh := hx (j+1) (by simp; omega)
        change xs[j] = (if j+1 = a+1 then 𝟙 else 𝟘) at hh
        simpa using hh

theorem binaryShout_onehot_lookup_sound (table : Array F) (address : List Bool)
    (weights : Array F) (value : F) (h : checkBinaryShout table address weights value = true) :
    ∃ a : Fin table.size, a.val = bitAddress address ∧ value = table[a.val] ∧
      ∀ j (hj : j < weights.size), weights[j] = 𝟙 ↔ j = a.val := by
  simp only [checkBinaryShout, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, hw⟩ := (checkTensor_iff _ _).mp h.1.2
  have ha := bitAddress_lt address
  refine ⟨⟨bitAddress address, by omega⟩, rfl, ?_, ?_⟩
  · apply h.2.symm.trans
    exact innerProd_unit weights.toList table.toList (bitAddress address)
      (by simpa using hs.trans h.1.1.symm) (by simpa using (show bitAddress address < weights.size by omega))
      (by simpa using hw)
  · intro j hj
    rw [hw j hj]
    split <;> simp_all [Ne.symm (towerOne_ne_zero 7)]

theorem tripleHot_sum_is_one (x : F) :
    (𝟙 ⊞ 𝟙) ⊞ 𝟙 = 𝟙 ∧ (x ⊠ (𝟙 ⊞ x) = 𝟘 ↔ x = 𝟘 ∨ x = 𝟙) := by
  constructor
  · simp
  · rw [towerMul_eq_zero_iff]
    constructor
    · rintro (h | h)
      · exact .inl h
      · right
        have hh := congrArg (towerAdd 7 𝟙) h
        simpa only [towerAdd_cancel, towerAdd_zero] using hh
    · rintro (h | h)
      · exact .inl h
      · right; rw [h, towerAdd_self_zero]

/-! One scatter pass over sparse nonzeros, replacing repeated row scans in the
compiled discrepancy-table construction. Duplicate entries accumulate in F. -/
def sparseRows (n : Nat) (entries : Array SparseEntry) (z : Array F) : Array F :=
  entries.foldl (fun acc e => acc.modify e.row (fun v => v ⊞ (e.value ⊠ z[e.col]?.getD 𝟘)))
    (Array.replicate n 𝟘)

theorem sparseRows_get (n : Nat) (entries : Array SparseEntry) (z : Array F)
    (row : Nat) (hr : row < n) :
    (sparseRows n entries z)[row]?.getD 𝟘 = sparseRowSpec entries.toList z row := by
  have aux (es : List SparseEntry) (acc : Array F) (ha : row < acc.size) :
      ((es.foldl (fun acc e => acc.modify e.row (fun v => v ⊞ (e.value ⊠ z[e.col]?.getD 𝟘))) acc)[row]?).getD 𝟘 =
      es.foldl (fun v e => if e.row = row then v ⊞ (e.value ⊠ z[e.col]?.getD 𝟘) else v)
        (acc[row]?.getD 𝟘) := by
    induction es generalizing acc with
    | nil => rfl
    | cons e es ih =>
      simp only [List.foldl_cons]
      rw [ih _ (by simpa using ha), Array.getElem?_modify]
      split <;> simp [Array.getElem?_eq_getElem ha]
  unfold sparseRows sparseRowSpec
  rw [← Array.foldl_toList, aux _ _ (by simpa using hr)]
  simp [hr]

/-! Boolean interpolation and the outer Schwartz–Zippel witness. -/
theorem hypercube_mem (bs : List Bool) : bs ∈ hypercube bs.length := by
  induction bs with
  | nil => simp [hypercube]
  | cons b bs ih =>
    simp only [List.length_cons, hypercube, List.mem_flatMap]
    exact ⟨bs, ih, by cases b <;> simp⟩

theorem hypercube_member_length (n : Nat) (bs : List Bool) (h : bs ∈ hypercube n) : bs.length = n := by
  induction n generalizing bs with
  | zero => simpa [hypercube] using h
  | succ n ih =>
    simp only [hypercube, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
    obtain ⟨xs, hx, rfl | rfl⟩ := h <;> simp [ih xs hx]

theorem hypercube_nodup (n : Nat) : (hypercube n).Nodup := by
  induction n with
  | zero => simp [hypercube]
  | succ n ih =>
    change List.Pairwise (· ≠ ·) (hypercube (n+1))
    rw [hypercube, List.pairwise_flatMap]
    constructor
    · intro xs _; simp
    · apply ih.imp
      intro xs ys hne
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro zs (rfl | rfl) ws (rfl | rfl) <;> simp_all

private theorem innerProd_delta {α : Type} [DecidableEq α] (xs : List α)
    (f : α → F) (a : α) (hn : xs.Nodup) (ha : a ∈ xs) :
    innerProd (xs.map f) (xs.map fun b => if a = b then 𝟙 else 𝟘) = f a := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.nodup_cons] at hn
    simp only [List.map_cons, innerProd]
    change (f x ⊠ (if a = x then 𝟙 else 𝟘)) ⊞ _ = _
    by_cases he : a = x
    · subst a
      rw [ite_eq_left rfl, towerMul_one]
      have hz : innerProd (xs.map f) (xs.map fun b => if x = b then 𝟙 else 𝟘) = 𝟘 := by
        have aux (ys : List α) (hy : x ∉ ys) :
            innerProd (ys.map f) (ys.map fun b => if x = b then 𝟙 else 𝟘) = 𝟘 := by
          induction ys with
          | nil => rfl
          | cons y ys ih =>
            simp only [List.mem_cons, not_or] at hy
            simp only [List.map_cons, innerProd, hy.1, ite_false]
            change (f y ⊠ 𝟘) ⊞ _ = 𝟘
            rw [towerMul_zero, towerZero_add, ih hy.2]
        exact aux xs hn.1
      rw [hz, towerAdd_zero]
    · rw [ite_eq_right he, towerMul_zero, towerZero_add]
      exact ih hn.2 ((List.mem_cons.mp ha).resolve_left he)

def discrepancyTable (i : R1csInstance) (z : Array F) : List F :=
  (hypercube i.logRows).map (fun bs => discrepancy i z (bitAddress bs))

/-- Three O(nnz + rows) scatters, followed by an indexed array pass. -/
def discrepancyTableExec (i : R1csInstance) (z : Array F) : List F :=
  let av := sparseRows (2^i.logRows) i.a.toArray z
  let bv := sparseRows (2^i.logRows) i.b.toArray z
  let cv := sparseRows (2^i.logRows) i.c.toArray z
  (hypercube i.logRows).toArray.map (fun bs =>
    (av[bitAddress bs]?.getD 𝟘 ⊠ bv[bitAddress bs]?.getD 𝟘) ⊞ cv[bitAddress bs]?.getD 𝟘) |>.toList

theorem discrepancyTable_exec_eq_spec (i : R1csInstance) (z : Array F) :
    discrepancyTableExec i z = discrepancyTable i z := by
  unfold discrepancyTableExec discrepancyTable
  simp only [Array.toList_map]
  apply List.map_congr_left
  intro bs hb
  have hr : bitAddress bs < 2^i.logRows := by
    have h := bitAddress_lt bs
    rwa [hypercube_member_length _ _ hb] at h
  simp only [sparseRows_get _ _ _ _ hr, discrepancy, sparseRow_exec_eq_spec]

@[csimp] theorem discrepancyTable_eq_exec : discrepancyTable = discrepancyTableExec := by
  funext i z
  exact (discrepancyTable_exec_eq_spec i z).symm

theorem discrepancy_polynomial_at_vertex (i : R1csInstance) (z : Array F) (bs : List Bool)
    (hlen : bs.length = i.logRows) :
    mleEval (discrepancyTable i z) (bs.map (bitElem (R := F))) = discrepancy i z (bitAddress bs) := by
  unfold mleEval discrepancyTable
  simp only [List.length_map, hlen]
  have he : (hypercube i.logRows).map (eqPoly (bs.map (bitElem (R := F)))) =
      (hypercube i.logRows).map (fun cs => if bs = cs then 𝟙 else 𝟘) := by
    apply List.map_congr_left
    intro cs hc
    exact eqPoly_kronecker bs cs (hlen.trans (hypercube_member_length _ _ hc).symm)
  rw [he]
  exact innerProd_delta _ _ _ (hypercube_nodup _) (hlen ▸ hypercube_mem bs)

def addressBits : Nat → Nat → List Bool
  | 0, _ => []
  | n+1, j => (j % 2 = 1) :: addressBits n (j/2)

theorem addressBits_length (n j : Nat) : (addressBits n j).length = n := by
  induction n generalizing j <;> simp [addressBits, *]
theorem bitAddress_addressBits (n j : Nat) (h : j < 2^n) : bitAddress (addressBits n j) = j := by
  induction n generalizing j with
  | zero =>
    have hj : j = 0 := by simpa using h
    subst j; rfl
  | succ n ih =>
    have hj : j/2 < 2^n := by rw [Nat.pow_succ] at h; omega
    simp only [addressBits, bitAddress, ih (j/2) hj, decide_eq_true_eq]
    split <;> omega

theorem discrepancy_polynomial_nonzero (i : R1csInstance) (z : Array F)
    (row : Nat) (hr : row < 2^i.logRows) (hd : discrepancy i z row ≠ 𝟘) :
    ∃ bs ∈ hypercube i.logRows,
      mleEval (discrepancyTable i z) (bs.map (bitElem (R := F))) ≠ 𝟘 := by
  let bs := addressBits i.logRows row
  have hl : bs.length = i.logRows := addressBits_length _ _
  refine ⟨bs, hl ▸ hypercube_mem bs, ?_⟩
  rw [discrepancy_polynomial_at_vertex i z bs hl, bitAddress_addressBits _ _ hr]
  exact hd

/-- The suffix is fixed before the next random coordinate is drawn. -/
def outerSlice (tbl : List F) (suffix : List Bool) : RoundPoly F :=
  let lo := mleEval tbl (𝟘 :: suffix.map (bitElem (R := F)))
  let hi := mleEval tbl (𝟙 :: suffix.map (bitElem (R := F)))
  ⟨[lo, hi ⊞ lo]⟩

set_option maxHeartbeats 800000 in
theorem outerSlice_eval (tbl : List F) (suffix : List Bool) (r : F) :
    (outerSlice tbl suffix).eval r = mleEval tbl (r :: suffix.map (bitElem (R := F))) := by
  rw [outerSlice, RoundPoly.eval_linear]
  rw [← mleEval_foldFirstVar, ← mleEval_foldFirstVar, ← mleEval_foldFirstVar]
  exact (innerProd_foldFirstVar_linear (R := F) r _ tbl).symm

def outerAnchor (tbl : List F) (n : Nat) : Option (List Bool) :=
  (hypercube n).find? (fun bs => decide (mleEval tbl (bs.map (bitElem (R := F))) ≠ 𝟘))
def anchorPolynomial (tbl : List F) (n : Nat) : RoundPoly F :=
  outerSlice tbl ((outerAnchor tbl (n+1)).getD []).tail

/-- A concrete root with a nonzero evaluation witness, not a named error flag. -/
def PolynomialRootHit (degree : Nat) (p : RoundPoly F) (r : F) : Prop :=
  p.coeffs.length ≤ degree+1 ∧ (∃ x, p.eval x ≠ 𝟘) ∧ p.eval r = 𝟘

theorem polynomial_roots_count (d : Nat) (p : RoundPoly F) (roots : List F)
    (hn : roots.Nodup) (hd : p.coeffs.length ≤ d+1) (hp : ∃ x, p.eval x ≠ 𝟘)
    (hr : ∀ x ∈ roots, p.eval x = 𝟘) : roots.length ≤ d := by
  have hb := RoundPoly.roots_nodup_length_le d p.coeffs roots hn hd hp
  have hf : roots.filter (fun x => decide (p.eval x = 𝟘)) = roots :=
    List.filter_eq_self.mpr (fun x hx => by simp only [hr x hx, decide_true])
  change (roots.filter (fun x => decide (p.eval x = 𝟘))).length ≤ d at hb
  rwa [hf] at hb

def OuterRootHit : List F → List F → Prop
  | _, [] => False
  | tbl, r :: rs => PolynomialRootHit 1 (anchorPolynomial tbl rs.length) r ∨
      OuterRootHit (foldFirstVar tbl r) rs

private theorem anchor_exists (tbl : List F) (n : Nat)
    (h : ∃ bs ∈ hypercube n, mleEval tbl (bs.map (bitElem (R := F))) ≠ 𝟘) :
    ∃ bs, outerAnchor tbl n = some bs := by
  cases he : outerAnchor tbl n with
  | some bs => exact ⟨bs, rfl⟩
  | none =>
    obtain ⟨bs, hb, hv⟩ := h
    have hn := List.find?_eq_none.mp he bs hb
    exact False.elim (hn (by simpa using hv))

theorem outer_zero_implies_root (tbl : List F) (rs : List F)
    (hn : ∃ bs ∈ hypercube rs.length, mleEval tbl (bs.map (bitElem (R := F))) ≠ 𝟘)
    (hz : mleEval tbl rs = 𝟘) : OuterRootHit tbl rs := by
  induction rs generalizing tbl with
  | nil =>
    obtain ⟨bs, hb, hv⟩ := hn
    have hb0 : bs = [] := by simpa [hypercube] using hb
    subst bs; exact (hv hz).elim
  | cons r rs ih =>
    obtain ⟨bs, hb⟩ := anchor_exists tbl (rs.length+1) hn
    have hm := List.mem_of_find?_eq_some hb
    have hv : mleEval tbl (bs.map (bitElem (R := F))) ≠ 𝟘 := by
      have hv := List.find?_some hb
      simpa only [decide_eq_true_eq] using hv
    have hl := hypercube_member_length _ _ hm
    cases bs with
    | nil => simp only [List.length_nil] at hl; exact False.elim (by omega)
    | cons b bs =>
      have hbl : bs.length = rs.length := by simpa using hl
      cases ha : outerAnchor (foldFirstVar tbl r) rs.length with
      | some cs =>
        right
        apply ih (foldFirstVar tbl r)
        · exact ⟨cs, List.mem_of_find?_eq_some ha, by
          have hv := List.find?_some ha
          simpa only [decide_eq_true_eq] using hv⟩
        · simpa only [mleEval_foldFirstVar] using hz
      | none =>
        left
        have hs : anchorPolynomial tbl rs.length = outerSlice tbl bs := by
          simp only [anchorPolynomial, hb, Option.getD_some, List.tail_cons]
        rw [hs]
        refine ⟨by simp [outerSlice], ⟨bitElem b, ?_⟩, ?_⟩
        · simpa only [outerSlice_eval, List.map_cons] using hv
        · rw [outerSlice_eval, ← mleEval_foldFirstVar]
          have hn := List.find?_eq_none.mp ha bs (hbl ▸ hypercube_mem bs)
          simpa only [decide_eq_true_eq, Decidable.not_not] using hn

/-! A materialized discrepancy-table reduction. This is a witness-carrying
reference protocol: the verifier computes the sparse rows and final oracle.
It makes no succinctness or zero-knowledge claim. It accepts degree ≤2 round
polynomials (the honest table prover uses degree 1), leaving one degree per
coordinate for the outer test in the 3s/2^128 algebraic budget. -/
def weightedTable (tbl : List F) (rs : List F) : List F :=
  List.zipWith (towerMul 7) tbl ((hypercube rs.length).map (eqPoly rs))

private theorem innerProd_weighted (xs ys : List F) :
    innerProd (List.zipWith (towerMul 7) xs ys) (ys.map fun _ => 𝟙) = innerProd xs ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      change ((x ⊠ y) ⊠ 𝟙) ⊞ _ = (x ⊠ y) ⊞ _
      rw [towerMul_one, ih]

theorem weighted_sum_eq_outer (tbl : List F) (rs : List F) :
    hypercubeSum rs.length (weightedTable tbl rs) = mleEval tbl rs := by
  unfold hypercubeSum weightedTable mleEval
  have h := innerProd_weighted tbl ((hypercube rs.length).map (eqPoly rs))
  simpa only [List.map_map, Function.comp_def, CommRingOps.one] using h

def squeezeOuter : Nat → Transcript .instanceBound → List F × Transcript .instanceBound
  | 0, tr => ([], tr)
  | n+1, tr =>
    let (r, tr') := TranscriptChallenge.squeezeChallenge (R := F) tr
    let (rs, tr'') := squeezeOuter n tr'
    (r :: rs, tr'')
theorem squeezeOuter_length (n : Nat) (tr : Transcript .instanceBound) :
    (squeezeOuter n tr).1.length = n := by
  induction n generalizing tr <;> simp [squeezeOuter, *]

def checkR1csShape (i : R1csInstance) (z : Array F) : Bool :=
  decide (z.size = i.numCols) &&
    (i.a ++ i.b ++ i.c).all (fun e => decide (e.row < 2^i.logRows ∧ e.col < i.numCols)) &&
    i.publicIO.all (fun (j, v) => decide (z[j]? = some v))
structure BinarySpartanProof where
  boundInstance : R1csInstance
  witness : Array F
  commitment : Digest32
  rounds : List (RoundPoly F)

def spartanSetup (i : R1csInstance) (z : Array F) : List F × Transcript .instanceBound :=
  squeezeOuter i.logRows (absorbR1csInstance context i z).transcript

def proveBinarySpartan (i : R1csInstance) (z : Array F) : BinarySpartanProof :=
  let (rs, tr) := spartanSetup context i z
  let tbl := weightedTable (discrepancyTable i z) rs
  ⟨i, z, witnessCommitment z, (honestSumcheckProver i.logRows tbl tr).1⟩

def verifyBinarySpartan (i : R1csInstance) (p : BinarySpartanProof) : Bool :=
  decide (p.boundInstance = i) && checkR1csShape i p.witness &&
  decide (p.commitment = witnessCommitment p.witness) &&
  let (rs, tr) := spartanSetup context i p.witness
  let tbl := weightedTable (discrepancyTable i p.witness) rs
  match verifySumcheck 2 i.logRows 𝟘 p.rounds tr with
  | none => false
  | some (claim, _) => decide (claim.expectedVal = mleEval tbl claim.point)

/-- A bounded round root event carries the actual Fiat–Shamir challenge. -/
def BoundedRoundRootHit : Nat → List F → List (RoundPoly F) → Transcript .instanceBound → Prop
  | 0, _, _, _ => False
  | _+1, _, [], _ => False
  | n+1, tbl, p :: ps, tr =>
    let (r, tr') := absorbAndSqueezeRound p tr
    PolynomialRootHit 2 (p.sub (honestRoundPoly n tbl)) r ∨
      BoundedRoundRootHit n (foldFirstVar tbl r) ps tr'

theorem bounded_sumcheck_sound :
    ∀ (n : Nat) (tbl : List F) (sum : F) (rounds : List (RoundPoly F))
      (tr : Transcript .instanceBound) (claim : EvalClaim F n) (last : Transcript .instanceBound),
      verifySumcheck 2 n sum rounds tr = some (claim, last) →
      sum ≠ hypercubeSum n tbl →
      claim.expectedVal ≠ mleEval tbl claim.point ∨ BoundedRoundRootHit n tbl rounds tr
  | 0, tbl, sum, [], _, claim, _, h, hn => by
    simp only [verifySumcheck, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact .inl (by simpa [hypercubeSum_zero] using hn)
  | 0, _, _, _ :: _, _, _, _, h, _ => by cases h
  | _+1, _, _, [], _, _, _, h, _ => by cases h
  | n+1, tbl, sum, p :: ps, tr, claim, last, h, hn => by
    simp only [verifySumcheck] at h
    cases hr : verifySumcheckRound 2 sum p tr with
    | none => rw [hr] at h; cases h
    | some out =>
      obtain ⟨r, next, tr'⟩ := out
      rw [hr] at h
      dsimp only at h
      cases hs : verifySumcheck 2 n next ps tr' with
      | none => rw [hs] at h; cases h
      | some sub =>
        obtain ⟨sc, last'⟩ := sub
        rw [hs] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have he : (r, tr') = absorbAndSqueezeRound p tr := by
          unfold verifySumcheckRound at hr
          split at hr
          · simp only [Option.some.injEq, Prod.mk.injEq] at hr
            exact Prod.ext hr.1.symm hr.2.2.symm
          · cases hr
        obtain ⟨hd, _, _, hnext⟩ := verifySumcheck_round_sound tbl hr hn
        rcases hnext with hf | hit
        · rcases bounded_sumcheck_sound n (foldFirstVar tbl r) next ps tr' sc last' hs hf with hf | hh
          · exact .inl (by simpa only [mleEval_foldFirstVar] using hf)
          · right; dsimp only [BoundedRoundRootHit]; rw [← he]; exact .inr hh
        · right; dsimp only [BoundedRoundRootHit]; rw [← he]
          left
          refine ⟨?_, ?_, hit.1⟩
          · simp only [RoundPoly.sub, RoundPoly.subCoeffs_length, honestRoundPoly,
              List.length_cons, List.length_nil]
            exact Nat.max_le.mpr ⟨hd, by decide⟩
          · rcases hit.2 with h0 | h1
            · exact ⟨𝟘, h0⟩
            · exact ⟨𝟙, h1⟩

/-- Every accepted false R1CS has an explicit nonzero-polynomial root event.
Exact instance equality is checked in addition to hashing, so the stronger
no-collision-branch conclusion holds for this witness-carrying verifier. -/
theorem binarySpartan_verify_sound_or_schwartzZippel (i : R1csInstance) (p : BinarySpartanProof)
    (h : verifyBinarySpartan context i p = true) :
    R1csSatisfied i p.witness ∨
      OuterRootHit (discrepancyTable i p.witness) (spartanSetup context i p.witness).1 ∨
      BoundedRoundRootHit i.logRows
        (weightedTable (discrepancyTable i p.witness) (spartanSetup context i p.witness).1)
        p.rounds (spartanSetup context i p.witness).2 := by
  let setup := spartanSetup context i p.witness
  let tbl := discrepancyTable i p.witness
  have hl : setup.1.length = i.logRows := squeezeOuter_length _ _
  simp only [verifyBinarySpartan, Bool.and_eq_true] at h
  have hv := h.2
  change (match verifySumcheck 2 i.logRows 𝟘 p.rounds setup.2 with
    | none => false
    | some (claim, _) => decide (claim.expectedVal = mleEval (weightedTable tbl setup.1) claim.point)) = true at hv
  cases he : verifySumcheck 2 i.logRows 𝟘 p.rounds setup.2 with
  | none => simp [he] at hv
  | some out =>
    obtain ⟨claim, last⟩ := out
    rw [he] at hv
    have hval := of_decide_eq_true hv
    if hg : mleEval tbl setup.1 = 𝟘 then
      cases ha : outerAnchor tbl i.logRows with
      | none =>
        left
        intro row hr
        apply (discrepancy_zero_iff _ _ _).mp
        by_cases hd : discrepancy i p.witness row = 𝟘
        · exact hd
        · obtain ⟨bs, hb, hv⟩ := discrepancy_polynomial_nonzero i p.witness row hr hd
          exact False.elim (List.find?_eq_none.mp ha bs hb (by simpa using hv))
      | some bs =>
        right; left
        apply outer_zero_implies_root tbl setup.1
        · rw [hl]
          exact ⟨bs, List.mem_of_find?_eq_some ha, by
          have hv := List.find?_some ha
          simpa only [decide_eq_true_eq] using hv⟩
        · exact hg
    else
      right; right
      have hs : 𝟘 ≠ hypercubeSum i.logRows (weightedTable tbl setup.1) := by
        rw [← hl, weighted_sum_eq_outer]
        exact Ne.symm hg
      exact (bounded_sumcheck_sound _ _ _ _ _ _ _ he hs).resolve_left (not_not_intro hval)

/-- Conditional uniform-challenge union budget: s linear outer tests and s
quadratic round tests. Fiat–Shamir hash outputs are deterministic; an adversary
probability theorem additionally needs a random-oracle/query-budget model. -/
theorem binarySpartan_root_budget (s : Nat) (outer round : Fin s → Nat)
    (ho : ∀ j, outer j ≤ 1) (hr : ∀ j, round j ≤ 2) :
    ((List.finRange s).map (fun j => outer j + round j)).sum * 2^128 ≤ (3*s) * 2^128 := by
  apply Nat.mul_le_mul_right
  have h : ∀ xs : List (Fin s), (xs.map (fun j => outer j + round j)).sum ≤ 3*xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons j js ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; have := ho j; have := hr j; omega
  simpa using h (List.finRange s)

/-! Prover completeness and a total deterministic audit judge. -/
private theorem innerProd_zero_left (xs ys : List F) (h : ∀ x ∈ xs, x = 𝟘) :
    innerProd xs ys = 𝟘 := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      change (x ⊠ y) ⊞ _ = 𝟘
      rw [h x List.mem_cons_self, towerZero_mul, towerZero_add]
      exact ih ys (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem satisfied_outer_zero (i : R1csInstance) (z : Array F) (h : R1csSatisfied i z) (rs : List F) :
    mleEval (discrepancyTable i z) rs = 𝟘 := by
  apply innerProd_zero_left
  intro x hx
  obtain ⟨bs, hb, rfl⟩ := List.mem_map.mp hx
  apply (discrepancy_zero_iff _ _ _).mpr
  apply h
  have hh := bitAddress_lt bs
  rwa [hypercube_member_length _ _ hb] at hh

theorem proveBinarySpartan_complete (i : R1csInstance) (z : Array F)
    (hshape : checkR1csShape i z = true) (hsat : R1csSatisfied i z) :
    verifyBinarySpartan context i (proveBinarySpartan context i z) = true := by
  let st := spartanSetup context i z
  let tbl := weightedTable (discrepancyTable i z) st.1
  have hl : st.1.length = i.logRows := squeezeOuter_length _ _
  have hz : hypercubeSum i.logRows tbl = 𝟘 := by
    rw [← hl, weighted_sum_eq_outer]
    exact satisfied_outer_zero i z hsat st.1
  obtain ⟨hv, he⟩ := honestSumcheckProver_completeness (R := F) (maxDeg := 2) (by decide)
    i.logRows tbl st.2
  rw [hz] at hv
  unfold verifyBinarySpartan proveBinarySpartan
  simp only [decide_true, hshape, Bool.true_and]
  change (match verifySumcheck 2 i.logRows 𝟘 (honestSumcheckProver i.logRows tbl st.2).1 st.2 with
    | none => false
    | some (claim, _) => decide (claim.expectedVal = mleEval tbl claim.point)) = true
  rw [hv]
  exact decide_eq_true he

theorem verifyBinarySpartan_binds_instance (i : R1csInstance) (p : BinarySpartanProof)
    (h : verifyBinarySpartan context i p = true) : p.boundInstance = i := by
  simp only [verifyBinarySpartan, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

@[expose] def R1csShape (i : R1csInstance) (z : Array F) : Prop :=
  z.size = i.numCols ∧ (∀ e ∈ i.a ++ i.b ++ i.c, e.row < 2^i.logRows ∧ e.col < i.numCols) ∧
    ∀ j v, (j,v) ∈ i.publicIO → z[j]? = some v

theorem checkR1csShape_iff (i : R1csInstance) (z : Array F) :
    checkR1csShape i z = true ↔ R1csShape i z := by
  simp only [checkR1csShape, R1csShape, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Prod.forall]
  exact and_assoc

def checkAllRows (i : R1csInstance) (z : Array F) : Bool :=
  (List.range (2^i.logRows)).all (fun row => decide (discrepancy i z row = 𝟘))
theorem checkAllRows_iff (i : R1csInstance) (z : Array F) :
    checkAllRows i z = true ↔ R1csSatisfied i z := by
  simp only [checkAllRows, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    discrepancy_zero_iff, R1csSatisfied]

structure AuditObject where
  statement : R1csInstance
  witness : Array F
  params : PcsCodeParams
  table : Array F
  address : List Bool
  value : F

/-- Independent mathematical meaning. The certificate is unnecessary because
this total judge audits the supplied witness and public table exhaustively. -/
def AuditMeaning (o : AuditObject) : Prop :=
  R1csShape o.statement o.witness ∧ R1csSatisfied o.statement o.witness ∧
  PcsSoundnessRegime o.params ∧ o.table.size = 2^o.address.length ∧
  o.table[bitAddress o.address]? = some o.value
inductive AuditClause where
  | malformedInstance | constraint | proximity | tableShape | lookup
  deriving DecidableEq, Repr

def auditCheck (o : AuditObject) : Obend.Judge.Verdict AuditClause :=
  if checkR1csShape o.statement o.witness = false then .refused .malformedInstance []
  else if checkAllRows o.statement o.witness = false then .refused .constraint []
  else if checkPcsSoundnessRegime o.params = false then .refused .proximity []
  else if o.table.size ≠ 2^o.address.length then .refused .tableShape []
  else if o.table[bitAddress o.address]? ≠ some o.value then .refused .lookup []
  else .ok

theorem auditCheck_iff (o : AuditObject) : auditCheck o = .ok ↔ AuditMeaning o := by
  simp only [AuditMeaning, ← checkR1csShape_iff, ← checkAllRows_iff,
    ← checkPcsSoundnessRegime_iff]
  unfold auditCheck
  split <;> rename_i hshape
  · simp [hshape]
  · have hs : checkR1csShape o.statement o.witness = true := by cases h : checkR1csShape o.statement o.witness <;> simp_all
    split <;> rename_i hrows
    · simp [hrows]
    · have hr : checkAllRows o.statement o.witness = true := by cases h : checkAllRows o.statement o.witness <;> simp_all
      split <;> rename_i hpcs
      · simp [hpcs]
      · have hp : checkPcsSoundnessRegime o.params = true := by cases h : checkPcsSoundnessRegime o.params <;> simp_all
        split <;> rename_i ht
        · simp [ht]
        · split <;> simp_all

theorem auditCheck_total (o : AuditObject) : auditCheck o ≠ .uncovered := by
  unfold auditCheck
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> try simp
  split <;> simp

instance binarySpartanShoutJudge : Obend.Judge AuditObject Unit where
  Clause := AuditClause
  Meaning o _ := AuditMeaning o
  check _ o _ := auditCheck o
  sound h := (auditCheck_iff _).mp h
  refutes _ := true
  refuted h _ _ hm := by
    have hok := (auditCheck_iff _).mpr hm
    rw [hok] at h; cases h
  Fragment _ := True
  complete _ h := by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, 0, (auditCheck_iff _).mpr hc⟩
  mono _ _ := rfl

/-- Exact integer interpretation of the query budget's logarithmic report. -/
theorem pcs_floor_meets_target (p : PcsCodeParams) (h : checkPcsSoundnessRegime p = true) :
    p.targetSecurityBits ≤ computeSoundnessBitsFloor p := by
  have hp := (checkPcsSoundnessRegime_iff p).mp h
  have hdist := hp.2.2.2.1
  have hd : 0 < (p.distanceDenominator - p.distanceNumerator)^p.numQueries :=
    Nat.pow_pos (by omega)
  have hq : 2^p.targetSecurityBits ≤ p.distanceDenominator^p.numQueries /
      (p.distanceDenominator-p.distanceNumerator)^p.numQueries := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    simpa only [Nat.mul_comm] using pcs_sampling_bound p h
  have hz : p.distanceDenominator^p.numQueries /
      (p.distanceDenominator-p.distanceNumerator)^p.numQueries ≠ 0 := by
    have := Nat.pow_pos (n := p.targetSecurityBits) (show 0 < 2 by decide)
    omega
  exact (Nat.le_log2 hz).mpr hq

/-! The software packed multiplier and the pipelined RTL use identical bases.
This bridge prevents accidentally interpreting tower coordinates in a different
binary polynomial basis at a hardware boundary. -/
private theorem hardware_join (k : Nat) (lo hi : TowerBitVec k) :
    Obend.Hardware.PipelinedZkCrypto.towerJoin (k := k) lo hi = joinBits k lo hi := rfl
private theorem hardware_lo (k : Nat) (x : TowerBitVec (k+1)) :
    Obend.Hardware.PipelinedZkCrypto.towerLo x = lowBits k x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [Obend.Hardware.PipelinedZkCrypto.towerLo, lowBits, hj]
private theorem hardware_hi (k : Nat) (x : TowerBitVec (k+1)) :
    Obend.Hardware.PipelinedZkCrypto.towerHi x = highBits k x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [Obend.Hardware.PipelinedZkCrypto.towerHi, highBits,
    BitVec.getLsbD_ushiftRight, hj, Nat.add_comm]
private theorem hardware_scale (k : Nat) (x : TowerBitVec k) :
    Obend.Hardware.PipelinedZkCrypto.towerMulOmega k x = scaleXExec k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Obend.Hardware.PipelinedZkCrypto.towerMulOmega, scaleXExec,
      hardware_join, hardware_lo, hardware_hi, ih]

theorem hardware_mul_refines (k : Nat) (a b : TowerElem k) :
    Obend.Hardware.PipelinedZkCrypto.towerMul k (packTower k a) (packTower k b) =
      packTower k (towerMul k a b) := by
  have h (k : Nat) (x y : TowerBitVec k) :
      Obend.Hardware.PipelinedZkCrypto.towerMul k x y = mulExec k x y := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Obend.Hardware.PipelinedZkCrypto.towerMul, mulExec,
        hardware_join, hardware_lo, hardware_hi, hardware_scale, ih]
  rw [h, mulExec_refines]

theorem verify_rejects_bad_round (i : R1csInstance) (p : BinarySpartanProof)
    (hrows : 0 < i.logRows) (q : RoundPoly F) (qs : List (RoundPoly F))
    (hq : p.rounds = q :: qs) (hbad : q.eval 𝟘 ⊞ q.eval 𝟙 ≠ 𝟘) :
    verifyBinarySpartan context i p = false := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hrows)
  have hr (tr : Transcript .instanceBound) : verifySumcheckRound 2 𝟘 q tr = none := by
    simp only [verifySumcheckRound]
    have hb : decide (CommRingOps.add (q.eval CommRingOps.zero) (q.eval CommRingOps.one) = 𝟘) = false :=
      decide_eq_false hbad
    simp only [hb, Bool.and_false, Bool.false_eq_true, ite_false]
  have hv (tr : Transcript .instanceBound) : verifySumcheck 2 i.logRows 𝟘 (q :: qs) tr = none := by
    rw [hn]
    simp only [verifySumcheck, hr]
  simp only [verifyBinarySpartan, hq, hv, Bool.and_false]

theorem bitAddress_injective (a b : List Bool) (hl : a.length = b.length)
    (he : bitAddress a = bitAddress b) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp_all
    | cons y ys =>
      have hlen : xs.length = ys.length := by simpa using hl
      cases x <;> cases y <;> simp only [bitAddress, Bool.false_eq_true, ite_false, ite_true] at he
      · exact congrArg (List.cons false) (ih ys hlen (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih ys hlen (by omega))

/-- This equality connects the integer address checker to the actual tensor
product of characteristic-two equality factors. -/
theorem tensorWeight_at_index (address : List Bool) (j : Nat) (hj : j < 2^address.length) :
    tensorWeight address (addressBits address.length j) =
      if j = bitAddress address then 𝟙 else 𝟘 := by
  rw [tensorWeight_kronecker _ _ (addressBits_length _ _).symm]
  have he : address = addressBits address.length j ↔ j = bitAddress address := by
    constructor
    · intro h
      have hv := congrArg bitAddress h
      rw [bitAddress_addressBits _ _ hj] at hv
      exact hv.symm
    · intro h
      apply bitAddress_injective _ _ (addressBits_length _ _).symm
      rw [bitAddress_addressBits _ _ hj, h]
  simp only [he]

structure ShoutRead where
  address : List Bool
  value : F

def tensorVector (address : List Bool) : Array F :=
  Array.ofFn (fun j : Fin (2^address.length) => if j.val = bitAddress address then 𝟙 else 𝟘)
def verifyShoutRead (table : Array F) (read : ShoutRead) : Bool :=
  decide (table.size = 2^read.address.length) &&
    decide (table[bitAddress read.address]? = some read.value)
def verifyShoutBatch (table : Array F) (reads : Array ShoutRead) : Bool :=
  reads.all (verifyShoutRead table)

theorem tensorVector_valid (address : List Bool) : checkTensor address (tensorVector address) = true := by
  apply (checkTensor_iff _ _).mpr
  constructor
  · exact Array.size_ofFn
  · intro j hj
    exact array_get_ofFn _ j hj

/-- O(d) address representation and one table read, with the dense O(N) tensor
retained only as a mathematical specification. -/
theorem binaryShoutSparse_exec_eq_dense (table : Array F) (read : ShoutRead) :
    verifyShoutRead table read = checkBinaryShout table read.address (tensorVector read.address) read.value := by
  by_cases hs : table.size = 2^read.address.length
  · have ha : bitAddress read.address < table.size := by rw [hs]; exact bitAddress_lt _
    have hi : innerProd (tensorVector read.address).toList table.toList = table[bitAddress read.address] := by
      apply innerProd_unit _ _ (bitAddress read.address)
      · simp only [Array.length_toList, tensorVector, Array.size_ofFn, hs]
      · simp only [Array.length_toList, tensorVector, Array.size_ofFn]; exact bitAddress_lt _
      · intro j hj
        simp only [Array.getElem_toList, tensorVector, array_get_ofFn]
    simp only [verifyShoutRead, checkBinaryShout, hs, decide_true, tensorVector_valid,
      Bool.true_and, Array.getElem?_eq_getElem ha, Option.some.injEq, hi]
  · simp [verifyShoutRead, checkBinaryShout, hs]

theorem verifyShoutRead_sound (table : Array F) (read : ShoutRead)
    (h : verifyShoutRead table read = true) :
    ∃ a : Fin table.size, a.val = bitAddress read.address ∧ read.value = table[a.val] := by
  rw [binaryShoutSparse_exec_eq_dense] at h
  obtain ⟨a, ha, hv, _⟩ := binaryShout_onehot_lookup_sound _ _ _ _ h
  exact ⟨a, ha, hv⟩

/-! Sparse matrix/vector inner reduction. Each sparse nonzero supplies one
term; the virtual zero padding is free. The claim is the very same sparse row
used by the outer discrepancy, and the same instance-bound transcript is used. -/
def sparseInnerTable (entries : List SparseEntry) (z : Array F) (row : Nat) : List F :=
  entries.map (fun e => if e.row = row then e.value ⊠ z[e.col]?.getD 𝟘 else 𝟘)

private theorem innerProd_ones_fold (xs : List F) (ys : List (List Bool))
    (hl : xs.length ≤ ys.length) :
    innerProd xs (ys.map fun _ => 𝟙) = xs.foldl (towerAdd 7) 𝟘 := by
  have hfold (xs : List F) (a : F) :
      xs.foldl (towerAdd 7) a = a ⊞ xs.foldr (towerAdd 7) 𝟘 := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih => simp only [List.foldl_cons, List.foldr_cons, ih, towerAdd_assoc]
  rw [hfold, towerZero_add]
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      change (x ⊠ 𝟙) ⊞ _ = x ⊞ _
      rw [towerMul_one, ih ys (by simpa using hl)]

theorem sparseInner_sum_eq_row (entries : List SparseEntry) (z : Array F) (row n : Nat)
    (hlen : entries.length ≤ 2^n) :
    hypercubeSum n (sparseInnerTable entries z row) = sparseRowSpec entries z row := by
  unfold hypercubeSum
  change innerProd (sparseInnerTable entries z row) ((hypercube n).map fun _ => 𝟙) = _
  rw [innerProd_ones_fold _ _ (by simpa [sparseInnerTable, hypercube_length] using hlen)]
  simp only [sparseInnerTable, List.foldl_map, sparseRowSpec]
  congr 1
  funext acc e
  split <;> simp [*]

def sparseInnerTranscript (i : R1csInstance) (z : Array F) (entries : List SparseEntry)
    (row n : Nat) (claimed : F) : Transcript .instanceBound :=
  absorbMsg "binary-spartan.inner@1".toUTF8
    (TranscriptEncode.encodeTranscriptBytes (entries, row, n, claimed))
    (absorbR1csInstance context i z).transcript

def proveSparseInner (i : R1csInstance) (z : Array F) (entries : List SparseEntry) (row n : Nat) :
    List (RoundPoly F) :=
  (honestSumcheckProver n (sparseInnerTable entries z row) (sparseInnerTranscript context i z entries row n (sparseRowSpec entries z row))).1

def verifySparseInner (i : R1csInstance) (z : Array F) (entries : List SparseEntry) (row n : Nat)
    (claimed : F) (rounds : List (RoundPoly F)) : Bool :=
  decide (entries = i.a ∨ entries = i.b ∨ entries = i.c) && decide (entries.length ≤ 2^n) &&
  match verifySumcheck 2 n claimed rounds (sparseInnerTranscript context i z entries row n claimed) with
  | none => false
  | some (claim, _) => decide (claim.expectedVal = mleEval (sparseInnerTable entries z row) claim.point)

theorem sparseInner_verify_sound (i : R1csInstance) (z : Array F) (entries : List SparseEntry)
    (row n : Nat) (claimed : F) (rounds : List (RoundPoly F))
    (h : verifySparseInner context i z entries row n claimed rounds = true) :
    claimed = sparseRowSpec entries z row ∨
      BoundedRoundRootHit n (sparseInnerTable entries z row) rounds (sparseInnerTranscript context i z entries row n claimed) := by
  simp only [verifySparseInner, Bool.and_eq_true, decide_eq_true_eq] at h
  have heq := sparseInner_sum_eq_row entries z row n h.1.2
  by_cases he : claimed = sparseRowSpec entries z row
  · exact .inl he
  · right
    have hv := h.2
    cases hs : verifySumcheck 2 n claimed rounds (sparseInnerTranscript context i z entries row n claimed) with
    | none => simp [hs] at hv
    | some out =>
      obtain ⟨claim, tr⟩ := out
      rw [hs] at hv
      have hval := of_decide_eq_true hv
      exact (bounded_sumcheck_sound n _ _ _ _ _ _ hs (by rwa [heq])).resolve_left (not_not_intro hval)

theorem proveSparseInner_complete (i : R1csInstance) (z : Array F) (entries : List SparseEntry)
    (row n : Nat) (he : entries = i.a ∨ entries = i.b ∨ entries = i.c) (hlen : entries.length ≤ 2^n) :
    verifySparseInner context i z entries row n (sparseRowSpec entries z row)
      (proveSparseInner context i z entries row n) = true := by
  obtain ⟨hv, heval⟩ := honestSumcheckProver_completeness (R := F) (maxDeg := 2) (by decide)
    n (sparseInnerTable entries z row) (sparseInnerTranscript context i z entries row n (sparseRowSpec entries z row))
  rw [sparseInner_sum_eq_row entries z row n hlen] at hv
  simp only [verifySparseInner, proveSparseInner, he, hlen, decide_true, Bool.true_and, hv]
  exact decide_eq_true heval

/-- Computational collision extraction remains in PSum: no choice from an
existential proposition enters the executable path. -/
def extractR1csBinding (i j : R1csInstance) (z w : Array F)
    (h : (absorbR1csInstance context i z).transcript.state = (absorbR1csInstance context j w).transcript.state) :=
  extractBindInstanceOrEq (i, (witnessCommitment z).bytes) (j, (witnessCommitment w).bytes) context context h

/-! Exact challenge-space size and a root-set form of the full algebraic
budget. The root sets may be arbitrary duplicate-free subsets; nothing requires
materializing a list with 2^128 elements. -/
def binaryChallengeAt (j : Fin (2^128)) : F := unpackTower 7 (BitVec.ofNat 128 j.val)

theorem binaryChallengeAt_injective (a b : Fin (2^128))
    (h : binaryChallengeAt a = binaryChallengeAt b) : a = b := by
  have hh := congrArg (fun x => (packTower 7 x).toNat) h
  simp only [binaryChallengeAt, packTower_unpackTower, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hh
  exact Fin.ext hh

theorem binaryChallengeAt_surjective (x : F) : ∃ j, binaryChallengeAt j = x := by
  refine ⟨⟨(packTower 7 x).toNat, (packTower 7 x).isLt⟩, ?_⟩
  simp only [binaryChallengeAt, BitVec.ofNat_toNat, BitVec.setWidth_eq, unpackTower_packTower]

/-- Outer linear roots plus degree-two table-sumcheck roots, scaled as exact
rational numerators over the 2^128-element challenge space. -/
theorem binarySpartan_root_sets_bound (s : Nat)
    (outer round : Fin s → RoundPoly F) (os rs : Fin s → List F)
    (hon : ∀ j, (os j).Nodup) (hrn : ∀ j, (rs j).Nodup)
    (hod : ∀ j, (outer j).coeffs.length ≤ 2) (hrd : ∀ j, (round j).coeffs.length ≤ 3)
    (hop : ∀ j, ∃ x, (outer j).eval x ≠ 𝟘) (hrp : ∀ j, ∃ x, (round j).eval x ≠ 𝟘)
    (hor : ∀ j x, x ∈ os j → (outer j).eval x = 𝟘)
    (hrr : ∀ j x, x ∈ rs j → (round j).eval x = 𝟘) :
    ((List.finRange s).map (fun j => (os j).length + (rs j).length)).sum * 2^128 ≤
      (3*s) * 2^128 :=
  binarySpartan_root_budget s (fun j => (os j).length) (fun j => (rs j).length)
    (fun j => polynomial_roots_count 1 (outer j) (os j) (hon j) (hod j) (hop j) (hor j))
    (fun j => polynomial_roots_count 2 (round j) (rs j) (hrn j) (hrd j) (hrp j) (hrr j))

/-- Multilinear matrix-vector tables at the Boolean constraint vertices. -/
def matrixTable (n : Nat) (entries : List SparseEntry) (z : Array F) : List F :=
  (hypercube n).map (fun bs => sparseRowSpec entries z (bitAddress bs))

theorem matrixTable_at_vertex (n : Nat) (entries : List SparseEntry) (z : Array F)
    (bs : List Bool) (hl : bs.length = n) :
    mleEval (matrixTable n entries z) (bs.map (bitElem (R := F))) = sparseRowSpec entries z (bitAddress bs) := by
  unfold mleEval matrixTable
  simp only [List.length_map, hl]
  have he : (hypercube n).map (eqPoly (bs.map (bitElem (R := F)))) =
      (hypercube n).map (fun cs => if bs = cs then 𝟙 else 𝟘) := by
    apply List.map_congr_left
    intro cs hc
    exact eqPoly_kronecker bs cs (hl.trans (hypercube_member_length _ _ hc).symm)
  rw [he]
  exact innerProd_delta _ _ _ (hypercube_nodup _) (hl ▸ hypercube_mem bs)

/-- The displayed R1CS zerocheck summand, including characteristic-two addition.
The materialized reduction interpolates these values after restricting X to
Boolean vertices; it does not equate the two polynomials off the cube. -/
def r1csZerocheckTerm (i : R1csInstance) (z : Array F) (rs : List F) (bs : List Bool) : F :=
  let x := bs.map (bitElem (R := F))
  eqPoly rs bs ⊠ ((mleEval (matrixTable i.logRows i.a z) x ⊠
    mleEval (matrixTable i.logRows i.b z) x) ⊞ mleEval (matrixTable i.logRows i.c z) x)

theorem r1csZerocheckTerm_eq (i : R1csInstance) (z : Array F) (rs : List F) (bs : List Bool)
    (hl : bs.length = i.logRows) :
    r1csZerocheckTerm i z rs bs = eqPoly rs bs ⊠ discrepancy i z (bitAddress bs) := by
  simp only [r1csZerocheckTerm, matrixTable_at_vertex _ _ _ _ hl,
    discrepancy, sparseRow_exec_eq_spec]

end Obend.Crypto.BinarySpartanAndShout
