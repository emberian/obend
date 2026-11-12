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
  encodeFrame "OBEND.BINARY-SPARTAN/TOWER128/OUTER1/ROUND2/REFERENCE/v2".toUTF8
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
def witnessPreimage (z : Array F) : List UInt8 :=
  (encodeFrame "OBEND.BINARY-SPARTAN/WITNESS/TOWER128/v2".toUTF8
    (Native.bytesOfList (encodeItems z.toList)) ByteArray.empty).data.toList
theorem witnessPreimage_injective {z w : Array F} (h : witnessPreimage z = witnessPreimage w) : z = w := by
  have hf := (encodeFrame_injective (byteArray_eq_of_toList_eq h)).2.1
  have hi := congrArg (fun b : ByteArray => b.data.toList) hf
  exact Array.toList_inj.mp (encodeItems_injective (by simpa only [Native.bytesOfList_toList] using hi))
def witnessCommitment (z : Array F) : Digest32 :=
  evalDigest32 deployedCanopyHash32 (witnessPreimage z)
variable (context : Transcript .relationBound)
def absorbR1csInstance (i : R1csInstance) (z : Array F) :
    BoundTranscript (i, (witnessCommitment z).bytes) :=
  bindInstance (i, (witnessCommitment z).bytes) context
/-- Exact messages used by the instance-binding hash, including context and commitment. -/
def r1csPreimage (i : R1csInstance) (z : Array F) : List UInt8 :=
  instancePreimageList context.state context.stepCount
    (TranscriptEncode.encodeTranscriptBytes (i, (witnessCommitment z).bytes))
theorem r1cs_binding_or_collision (i j : R1csInstance) (z w : Array F)
    (h : (absorbR1csInstance context i z).transcript.state =
      (absorbR1csInstance context j w).transcript.state) :
    (i = j ∧ (witnessCommitment z).bytes = (witnessCommitment w).bytes) ∨
    CollisionAmong (cshake256Bytes fsInstanceCustomization)
      (fun m => m = r1csPreimage context i z ∨ m = r1csPreimage context j w) := by
  by_cases he : r1csPreimage context i z = r1csPreimage context j w
  · have hi := (instancePreimageList_injective he).2.2
    have hp : (i, (witnessCommitment z).bytes) = (j, (witnessCommitment w).bytes) :=
      LawfulTranscriptEncode.encodeTranscriptBytes_injective hi
    exact .inl (Prod.mk.inj hp)
  · right
    refine ⟨_, _, Or.inl rfl, Or.inr rfl, he, ?_⟩
    change (bindInstance _ context).transcript.state = (bindInstance _ context).transcript.state at h
    rw [bindInstance_state_eq, bindInstance_state_eq] at h
    have hh := congrArg (fun b : ByteArray => ofBE b.data.toList) h
    simpa only [r1csPreimage, cshake32ByteArray, Native.bytesOfList_toList] using hh
theorem witnessCommitment_binds (z w : Array F)
    (h : witnessCommitment z = witnessCommitment w) : z = w ∨
    CollisionAmong deployedCanopyHash32.eval
      (fun m => m = witnessPreimage z ∨ m = witnessPreimage w) := by
  by_cases he : witnessPreimage z = witnessPreimage w
  · exact .inl (witnessPreimage_injective he)
  · refine .inr ⟨_, _, Or.inl rfl, Or.inr rfl, he, ?_⟩
    have hh := congrArg (fun d : Digest32 => ofBE d.bytes.data.toList) h
    simpa only [witnessCommitment, evalDigest32, Native.bytesOfList_toList] using hh
/-- Both fields and the protocol domain are independently length framed. -/
def saltedWitnessPreimage (z : Array F) (salt : Digest32) : List UInt8 :=
  (encodeFrame "OBEND.BINARY-SPARTAN/BLINDED-WITNESS/v1".toUTF8
    (TranscriptEncode.encodeTranscriptBytes (z.toList, salt.bytes)) ByteArray.empty).data.toList
theorem saltedWitnessPreimage_injective {z w : Array F} {s₁ s₂ : Digest32}
    (h : saltedWitnessPreimage z s₁ = saltedWitnessPreimage w s₂) : z = w ∧ s₁ = s₂ := by
  have he : (z.toList, s₁.bytes) = (w.toList, s₂.bytes) :=
    LawfulTranscriptEncode.encodeTranscriptBytes_injective
      (encodeFrame_injective (byteArray_eq_of_toList_eq h)).2.1
  refine ⟨Array.toList_inj.mp (congrArg Prod.fst he), ?_⟩
  have hs := congrArg Prod.snd he
  cases s₁; cases s₂; cases hs; rfl
def saltedWitnessCommitment (z : Array F) (salt : Digest32) : Digest32 :=
  evalDigest32 deployedCanopyHash32 (saltedWitnessPreimage z salt)
def extractSaltedWitnessBinding (z w : Array F) (s₁ s₂ : Digest32)
    (h : saltedWitnessCommitment z s₁ = saltedWitnessCommitment w s₂) :
    PSum (z = w ∧ s₁ = s₂) (CollisionAmong deployedCanopyHash32.eval
      (fun m => m = saltedWitnessPreimage z s₁ ∨ m = saltedWitnessPreimage w s₂)) := by
  if he : saltedWitnessPreimage z s₁ = saltedWitnessPreimage w s₂ then
    exact .inl (saltedWitnessPreimage_injective he)
  else
    refine .inr ⟨_, _, Or.inl rfl, Or.inr rfl, he, ?_⟩
    have hh := congrArg (fun d : Digest32 => ofBE d.bytes.data.toList) h
    simpa only [saltedWitnessCommitment, evalDigest32, Native.bytesOfList_toList] using hh
theorem saltedWitnessCommitment_binds (z w : Array F) (s₁ s₂ : Digest32)
    (h : saltedWitnessCommitment z s₁ = saltedWitnessCommitment w s₂) :
    (z = w ∧ s₁ = s₂) ∨ CollisionAmong deployedCanopyHash32.eval
      (fun m => m = saltedWitnessPreimage z s₁ ∨ m = saltedWitnessPreimage w s₂) := by
  cases extractSaltedWitnessBinding z w s₁ s₂ h with
  | inl he => exact .inl he
  | inr hc => exact .inr hc
def blindEval (v mask : F) : F := v ⊞ mask
/-- Exact OTP coupling for a uniform independent field mask; no hash hiding assumption.
A zero-sum table alone does NOT imply its evaluation is uniform at every point. -/
theorem blindEval_bijection_hides_witness (v₀ v₁ : F) :
    let f := fun m => (m ⊞ v₀) ⊞ v₁
    let g := f
    (∀ m, g (f m) = m) ∧ (∀ m, f (g m) = m) ∧
      (∀ m, blindEval v₁ (f m) = blindEval v₀ m) := by
  dsimp
  have hi (m : F) : (((m ⊞ v₀) ⊞ v₁) ⊞ v₀) ⊞ v₁ = m := by
    simp only [towerAdd_assoc, towerAdd_left_comm, towerAdd_cancel]
    rw [towerAdd_comm 7 m v₁, towerAdd_cancel]
  exact ⟨hi, hi, fun m => by
    simp only [blindEval, towerAdd_assoc, towerAdd_left_comm]
    rw [towerAdd_comm 7 m v₁, towerAdd_cancel]⟩
def maskedTable (tbl mask : List F) : List F := List.zipWith (towerAdd 7) tbl mask
private theorem innerProd_masked (xs ms ys : List F) (hl : xs.length = ms.length) :
    innerProd (maskedTable xs ms) ys = innerProd xs ys ⊞ innerProd ms ys := by
  induction xs generalizing ms ys with
  | nil =>
    cases ms with
    | nil => exact (towerAdd_zero 7 𝟘).symm
    | cons m ms => simp only [List.length_nil, List.length_cons] at hl; omega
  | cons x xs ih =>
    cases ms with
    | nil => simp at hl
    | cons m ms =>
      cases ys with
      | nil => simp [maskedTable, innerProd, CommRingOps.zero]
      | cons y ys =>
        change ((x ⊞ m) ⊠ y) ⊞ innerProd (maskedTable xs ms) ys =
          ((x ⊠ y) ⊞ innerProd xs ys) ⊞ ((m ⊠ y) ⊞ innerProd ms ys)
        rw [ih ms ys (by simpa using hl), towerAdd_mul_distrib]
        simp only [towerAdd_assoc, towerAdd_left_comm]
theorem maskedTable_hypercubeSum_eq (n : Nat) (tbl mask : List F)
    (hl : tbl.length = mask.length) (hz : hypercubeSum n mask = 𝟘) :
    hypercubeSum n (maskedTable tbl mask) = hypercubeSum n tbl := by
  unfold hypercubeSum at *
  rw [innerProd_masked _ _ _ hl, hz, towerAdd_zero]
theorem maskedTable_eval (tbl mask : List F) (pt : List F) (hl : tbl.length = mask.length) :
    mleEval (maskedTable tbl mask) pt = blindEval (mleEval tbl pt) (mleEval mask pt) :=
  innerProd_masked _ _ _ hl
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
/-- Pairing is a nontrivial zero-sum mask in characteristic two (virtual zero padding). -/
theorem pairedMask_zeroSum (n : Nat) (m : F) : hypercubeSum (n+1) [m, m] = 𝟘 := by
  cases hc : hypercube n with
  | nil =>
    have hh := hypercube_length n
    rw [hc] at hh
    have hp : 0 < 2^n := Nat.two_pow_pos n
    simp only [List.length_nil] at hh; omega
  | cons b bs => simp [hypercubeSum, hypercube, hc, innerProd, CommRingOps.add, CommRingOps.mul, CommRingOps.one, CommRingOps.zero]
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
theorem discrepancyTable_eq_exec (i : R1csInstance) (z : Array F) :
    discrepancyTable i z = discrepancyTableExec i z := (discrepancyTable_exec_eq_spec i z).symm
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
theorem outerSlice_eval (tbl : List F) (suffix : List Bool) (r : F) :
    (outerSlice tbl suffix).eval r = mleEval tbl (r :: suffix.map (bitElem (R := F))) := by
  let pts := suffix.map (bitElem (R := F))
  let ones := (hypercube pts.length).map (eqPoly pts)
  have h0 : mleEval tbl (𝟘 :: pts) = innerProd (foldFirstVar tbl 𝟘) ones :=
    (mleEval_foldFirstVar tbl 𝟘 pts).symm
  have h1 : mleEval tbl (𝟙 :: pts) = innerProd (foldFirstVar tbl 𝟙) ones :=
    (mleEval_foldFirstVar tbl 𝟙 pts).symm
  have hr : innerProd (foldFirstVar tbl r) ones = mleEval tbl (r :: pts) :=
    mleEval_foldFirstVar tbl r pts
  refine Eq.trans ?_ hr
  refine Eq.trans (RoundPoly.eval_linear _ _ r) ?_
  rw [h0, h1]
  exact (innerProd_foldFirstVar_linear (R := F) r ones tbl).symm
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
@[expose] def R1csShape (i : R1csInstance) (z : Array F) : Prop :=
  z.size = i.numCols ∧ (∀ e ∈ i.a ++ i.b ++ i.c, e.row < 2^i.logRows ∧ e.col < i.numCols) ∧
    ∀ j v, (j,v) ∈ i.publicIO → z[j]? = some v
theorem checkR1csShape_iff (i : R1csInstance) (z : Array F) :
    checkR1csShape i z = true ↔ R1csShape i z := by
  simp only [checkR1csShape, R1csShape, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Prod.forall]
  exact and_assoc
structure BinarySpartanProof where
  boundInstance : R1csInstance
  witness : Array F
  commitment : Digest32
  rounds : List (RoundPoly F)
def spartanCommitmentSetup (i : R1csInstance) (cm : Digest32) : List F × Transcript .instanceBound :=
  squeezeOuter i.logRows (bindInstance (i, cm.bytes) context).transcript
theorem spartanCommitmentSetup_eq (i : R1csInstance) (cm : Digest32) :
    spartanCommitmentSetup context i cm = squeezeOuter i.logRows (bindInstance (i, cm.bytes) context).transcript := by unfold spartanCommitmentSetup; rfl
def spartanSetup (i : R1csInstance) (z : Array F) : List F × Transcript .instanceBound :=
  spartanCommitmentSetup context i (witnessCommitment z)
def proveBinarySpartan (i : R1csInstance) (z : Array F) : BinarySpartanProof :=
  let (rs, tr) := spartanSetup context i z
  let tbl := weightedTable (discrepancyTableExec i z) rs
  ⟨i, z, witnessCommitment z, (honestSumcheckProver i.logRows tbl tr).1⟩
def verifyBinarySpartan (i : R1csInstance) (p : BinarySpartanProof) : Bool :=
  decide (p.boundInstance = i) && checkR1csShape i p.witness &&
  decide (p.commitment = witnessCommitment p.witness) &&
  let (rs, tr) := spartanCommitmentSetup context i p.commitment
  let tbl := weightedTable (discrepancyTableExec i p.witness) rs
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
    R1csShape i p.witness ∧ (R1csSatisfied i p.witness ∨
      OuterRootHit (discrepancyTable i p.witness) (spartanSetup context i p.witness).1 ∨
      BoundedRoundRootHit i.logRows
        (weightedTable (discrepancyTable i p.witness) (spartanSetup context i p.witness).1)
        p.rounds (spartanSetup context i p.witness).2) := by
  have hshape : R1csShape i p.witness := (checkR1csShape_iff _ _).mp (by
    simp only [verifyBinarySpartan, discrepancyTable_exec_eq_spec, Bool.and_eq_true] at h
    exact h.1.1.2)
  refine ⟨hshape, ?_⟩
  let setup := spartanSetup context i p.witness
  let tbl := discrepancyTable i p.witness
  have hl : setup.1.length = i.logRows := squeezeOuter_length _ _
  simp only [verifyBinarySpartan, discrepancyTable_exec_eq_spec, Bool.and_eq_true] at h
  have hv := h.2
  rw [of_decide_eq_true h.1.2] at hv
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
/-- Wire opening: neither the witness, salt, nor mask is a field of this message. -/
structure BlindedSpartanOpening where
  commitment : Digest32
  maskCommitment : Digest32
  rounds : List (RoundPoly F)
  evaluation : F
def blindedSpartanTranscript (n : Nat) (sum : F) (cm mm : Digest32) : Transcript .instanceBound :=
  (bindInstance ("OBEND.BINARY-SPARTAN/BLINDED-OPENING/v1".toUTF8, n, sum, cm.bytes, mm.bytes) context).transcript
/-- Reference opening-oracle checker. z, salt and mask are private oracle inputs,
not public messages. The OTP theorem covers one evaluation, not full-transcript ZK. -/
def verifyBlindedSpartan (n : Nat) (z mask : Array F) (salt : Digest32) (sum : F)
    (p : BlindedSpartanOpening) : Bool :=
  decide (z.size = mask.size ∧ z.size = 2^n ∧ hypercubeSum n mask.toList = 𝟘 ∧
    p.commitment = saltedWitnessCommitment z salt ∧ p.maskCommitment = saltedWitnessCommitment mask salt) &&
  match verifySumcheck 2 n sum p.rounds (blindedSpartanTranscript context n sum p.commitment p.maskCommitment) with
  | none => false
  | some (claim, _) => decide (claim.expectedVal = p.evaluation ∧
      p.evaluation = blindEval (mleEval z.toList claim.point) (mleEval mask.toList claim.point))
def proveBlindedSpartan (n : Nat) (z mask : Array F) (salt : Digest32) (sum : F) : BlindedSpartanOpening :=
  let cm := saltedWitnessCommitment z salt
  let mm := saltedWitnessCommitment mask salt
  let out := honestSumcheckProver n (maskedTable z.toList mask.toList) (blindedSpartanTranscript context n sum cm mm)
  ⟨cm, mm, out.1, out.2.1.expectedVal⟩
theorem blindedSpartan_sound_or_schwartzZippel (n : Nat) (z mask : Array F) (salt : Digest32)
    (sum : F) (p : BlindedSpartanOpening) (h : verifyBlindedSpartan context n z mask salt sum p = true) :
    sum = hypercubeSum n z.toList ∨ BoundedRoundRootHit n (maskedTable z.toList mask.toList) p.rounds
      (blindedSpartanTranscript context n sum p.commitment p.maskCommitment) := by
  simp only [verifyBlindedSpartan, Bool.and_eq_true, decide_eq_true_eq] at h
  have hl : z.toList.length = mask.toList.length := by simpa using h.1.1
  by_cases he : sum = hypercubeSum n z.toList
  · exact .inl he
  · right
    have hv := h.2
    cases hs : verifySumcheck 2 n sum p.rounds (blindedSpartanTranscript context n sum p.commitment p.maskCommitment) with
    | none => simp [hs] at hv
    | some out =>
      rw [hs] at hv
      have hv := of_decide_eq_true hv
      have hf : out.1.expectedVal = mleEval (maskedTable z.toList mask.toList) out.1.point := by
        rw [maskedTable_eval _ _ _ hl]; exact hv.1.trans hv.2
      exact (bounded_sumcheck_sound n _ _ _ _ _ _ hs (by
        rwa [maskedTable_hypercubeSum_eq n _ _ hl h.1.2.2.1])).resolve_left (not_not_intro hf)
theorem proveBlindedSpartan_complete (n : Nat) (z mask : Array F) (salt : Digest32)
    (hl : z.size = mask.size) (hn : z.size = 2^n) (hz : hypercubeSum n mask.toList = 𝟘) :
    verifyBlindedSpartan context n z mask salt (hypercubeSum n z.toList)
      (proveBlindedSpartan context n z mask salt (hypercubeSum n z.toList)) = true := by
  have hlen : z.toList.length = mask.toList.length := by simpa using hl
  obtain ⟨hv, he⟩ := honestSumcheckProver_completeness (R := F) (maxDeg := 2) (by decide) n
    (maskedTable z.toList mask.toList) (blindedSpartanTranscript context n (hypercubeSum n z.toList)
      (saltedWitnessCommitment z salt) (saltedWitnessCommitment mask salt))
  rw [maskedTable_hypercubeSum_eq _ _ _ hlen hz] at hv
  have hm : mask.size = 2^n := hl.symm.trans hn
  simp only [verifyBlindedSpartan, proveBlindedSpartan, hl, hm, hz, and_self, decide_true, Bool.true_and, hv]
  exact decide_eq_true ⟨True.intro, he.trans (maskedTable_eval _ _ _ hlen)⟩
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
  simp only [discrepancyTable_exec_eq_spec, decide_true, hshape, Bool.true_and]
  change (match verifySumcheck 2 i.logRows 𝟘 (honestSumcheckProver i.logRows tbl st.2).1 st.2 with
    | none => false
    | some (claim, _) => decide (claim.expectedVal = mleEval tbl claim.point)) = true
  rw [hv]
  exact decide_eq_true he
theorem verifyBinarySpartan_binds_instance (i : R1csInstance) (p : BinarySpartanProof)
    (h : verifyBinarySpartan context i p = true) : p.boundInstance = i := by
  simp only [verifyBinarySpartan, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1
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
/-- Least-significant factor first: the address is Σⱼ indexⱼ B^j. -/
def radixAddress {B : Nat} : List (Fin B) → Nat
  | [] => 0
  | i :: is => i.val + B * radixAddress is
theorem radixAddress_lt {B : Nat} (is : List (Fin B)) :
    radixAddress is < B^is.length := by
  induction is with
  | nil => simp [radixAddress]
  | cons i is ih =>
    have h := Nat.mul_le_mul_left B (show radixAddress is + 1 ≤ B^is.length by omega)
    simp only [radixAddress, List.length_cons, Nat.pow_succ]
    have := i.isLt
    rw [Nat.mul_add, Nat.mul_one] at h
    rw [Nat.mul_comm (B^is.length) B]
    omega
theorem radixAddress_injective {B : Nat} (hb : 0 < B) (is js : List (Fin B))
    (hl : is.length = js.length) (he : radixAddress is = radixAddress js) : is = js := by
  induction is generalizing js with
  | nil =>
    cases js with
    | nil => rfl
    | cons j js => simp only [List.length_nil, List.length_cons] at hl; omega
  | cons i is ih =>
    cases js with
    | nil => simp only [List.length_nil, List.length_cons] at hl; omega
    | cons j js =>
      have hm := congrArg (· % B) he
      simp only [radixAddress, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt,
        Nat.mod_eq_of_lt j.isLt] at hm
      have hij : i = j := Fin.ext hm
      subst j
      have ht : radixAddress is = radixAddress js := by
        simp only [radixAddress] at he
        exact Nat.eq_of_mul_eq_mul_left hb (Nat.add_left_cancel he)
      exact congrArg (List.cons i) (ih js (Nat.succ.inj hl) ht)
def radixDigits (B : Nat) (hb : 0 < B) : Nat → Nat → List (Fin B)
  | 0, _ => []
  | d+1, a => ⟨a % B, Nat.mod_lt a hb⟩ :: radixDigits B hb d (a / B)
theorem radixDigits_length (B : Nat) (hb : 0 < B) (d a : Nat) :
    (radixDigits B hb d a).length = d := by
  induction d generalizing a <;> simp [radixDigits, *]
theorem radixAddress_digits (B : Nat) (hb : 0 < B) (d a : Nat) (ha : a < B^d) :
    radixAddress (radixDigits B hb d a) = a := by
  induction d generalizing a with
  | zero =>
    simp only [Nat.pow_zero] at ha
    have hz : a = 0 := by omega
    simp [radixDigits, radixAddress, hz]
  | succ d ih =>
    have hd : a / B < B^d := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa [Nat.pow_succ] using ha)
    simp only [radixDigits, radixAddress, ih _ hd]
    exact Nat.mod_add_div a B
def basisFactor {B : Nat} (i : Fin B) : Array F :=
  Array.ofFn fun j : Fin B => if j.val = i.val then 𝟙 else 𝟘
theorem basisFactor_boolean_unit {B : Nat} (i : Fin B) :
    (basisFactor i).size = B ∧
    innerProd (basisFactor i).toList (List.replicate B 𝟙) = 𝟙 ∧
    ∀ j (hj : j < (basisFactor i).size),
      ((basisFactor i)[j] = 𝟘 ∨ (basisFactor i)[j] = 𝟙) ∧
      ((basisFactor i)[j] = 𝟙 ↔ j = i.val) := by
  refine ⟨by simp [basisFactor], ?_, ?_⟩
  · have he := innerProd_unit (basisFactor i).toList (List.replicate B 𝟙) i.val
      (by simp only [Array.length_toList, basisFactor, Array.size_ofFn, List.length_replicate])
      (by simpa only [Array.length_toList, basisFactor, Array.size_ofFn] using i.isLt)
      (by intro j hj; simp only [Array.getElem_toList, basisFactor, array_get_ofFn])
    simpa using he
  · intro j hj
    simp only [basisFactor, array_get_ofFn]
    split <;> simp_all [Ne.symm (towerOne_ne_zero 7)]
/-- Exact Hamming weight one, not the unsound characteristic-two sum-only test. -/
def checkFactors {B : Nat} (is : List (Fin B)) (factors : Array (Array F)) : Bool :=
  decide (factors = (is.map basisFactor).toArray)
theorem checkFactors_complete {B : Nat} (is : List (Fin B)) :
    checkFactors is (is.map basisFactor).toArray = true := decide_eq_true rfl
theorem checkFactors_sound {B : Nat} (is : List (Fin B)) (fs : Array (Array F))
    (h : checkFactors is fs = true) :
    fs = (is.map basisFactor).toArray ∧
    ∀ j (hj : j < is.length), (fs[j]'(by simpa [of_decide_eq_true h] using hj)).size = B := by
  have he : fs = (is.map basisFactor).toArray := of_decide_eq_true h
  refine ⟨he, ?_⟩
  subst fs
  intro j hj
  simp [basisFactor]
/-- The actual Kronecker product, defined without materializing its B^d coefficients. -/
def tensorProduct (B : Nat) : List (Array F) → Nat → F
  | [], a => if a = 0 then 𝟙 else 𝟘
  | v :: vs, a => v[a % B]?.getD 𝟘 ⊠ tensorProduct B vs (a / B)
theorem tensorProduct_basis {B : Nat} (hb : 0 < B) (is : List (Fin B)) (a : Nat) :
    tensorProduct B (is.map basisFactor) a = if a = radixAddress is then 𝟙 else 𝟘 := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih =>
    have hm := Nat.mod_lt a hb
    have hf : (basisFactor i)[a % B]?.getD 𝟘 = if a % B = i.val then 𝟙 else 𝟘 := by
      rw [Array.getElem?_eq_getElem (by simpa [basisFactor] using hm)]
      simp only [Option.getD_some, basisFactor, array_get_ofFn]
    simp only [List.map_cons, tensorProduct, ih, hf]
    have he : a = i.val + B * radixAddress is ↔
        a % B = i.val ∧ a / B = radixAddress is := by
      constructor
      · intro h; subst a
        simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt,
          Nat.add_mul_div_left, Nat.div_eq_of_lt i.isLt, hb]
      · rintro ⟨hm, hd⟩
        simpa [hm, hd] using (Nat.mod_add_div a B).symm
    simp only [radixAddress, he]
    split <;> split <;> simp_all
/-- A reference-only dense tensor; verification below reads just the selected table cell. -/
def tensorExpansion (B : Nat) (fs : Array (Array F)) : Array F :=
  Array.ofFn fun a : Fin (B^fs.size) => tensorProduct B fs.toList a.val
structure TensorShoutRead (B : Nat) where
  indices : List (Fin B)
  factors : Array (Array F)
  value : F
def verifyTensorShoutRead (B d : Nat) (table : Array F) (r : TensorShoutRead B) : Bool :=
  decide (2 ≤ B ∧ 1 ≤ d ∧ r.indices.length = d ∧ table.size = B^d) &&
    checkFactors r.indices r.factors && decide (table[radixAddress r.indices]? = some r.value)
def verifyTensorShoutBatch (B d : Nat) (table : Array F) (rs : Array (TensorShoutRead B)) : Bool :=
  rs.all (verifyTensorShoutRead B d table)
/-- Acceptance proves a unique mixed-radix address, every tensor coefficient, and the
actual dense inner product. No length-K witness is supplied or constructed by the verifier. -/
theorem tensorShout_sound (B d : Nat) (table : Array F) (r : TensorShoutRead B)
    (h : verifyTensorShoutRead B d table r = true) :
    ∃ a : Fin table.size, a.val = radixAddress r.indices ∧ r.value = table[a] ∧
      (tensorExpansion B r.factors).size = B^d ∧
      (∀ j (hj : j < (tensorExpansion B r.factors).size),
        (tensorExpansion B r.factors)[j] = if j = a.val then 𝟙 else 𝟘) ∧
      innerProd (tensorExpansion B r.factors).toList table.toList = r.value := by
  simp only [verifyTensorShoutRead, Bool.and_eq_true, decide_eq_true_eq] at h
  have hf := (checkFactors_sound _ _ h.1.2).1
  have hs : r.factors.size = d := by rw [hf]; simpa using h.1.1.2.2.1
  have ha : radixAddress r.indices < table.size := by
    rw [h.1.1.2.2.2, ← h.1.1.2.2.1]
    exact radixAddress_lt _
  have hv : r.value = table[radixAddress r.indices] := by
    simpa [Array.getElem?_eq_getElem ha] using h.2.symm
  have ht : ∀ j (hj : j < (tensorExpansion B r.factors).size),
      (tensorExpansion B r.factors)[j] = if j = radixAddress r.indices then 𝟙 else 𝟘 := by
    intro j hj
    simp only [tensorExpansion, array_get_ofFn, hf, List.toList_toArray]
    exact tensorProduct_basis (by omega) _ j
  refine ⟨⟨_, ha⟩, rfl, hv, by simp [tensorExpansion, hs], ht, ?_⟩
  rw [hv]
  apply innerProd_unit _ _ (radixAddress r.indices)
  · simp only [Array.length_toList, tensorExpansion, Array.size_ofFn, hs, h.1.1.2.2.2]
  · simpa only [Array.length_toList, tensorExpansion, Array.size_ofFn, hs, h.1.1.2.2.2] using ha
  · simpa using ht
/-- Booleanity and unit sum of the full tensor follow from exact one-hotness,
not from a field sum test. This includes existence of the nonzero coefficient. -/
theorem tensorShout_boolean_unit (B d : Nat) (table : Array F) (r : TensorShoutRead B)
    (h : verifyTensorShoutRead B d table r = true) :
    innerProd (tensorExpansion B r.factors).toList (List.replicate (B^d) 𝟙) = 𝟙 ∧
    ∀ j (hj : j < (tensorExpansion B r.factors).size),
      (tensorExpansion B r.factors)[j] = 𝟘 ∨ (tensorExpansion B r.factors)[j] = 𝟙 := by
  obtain ⟨a, ha, _, hs, ht, _⟩ := tensorShout_sound B d table r h
  have hshape : table.size = B^d := by
    simp only [verifyTensorShoutRead, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.2.2.2
  have hb : a.val < (tensorExpansion B r.factors).size := by rw [hs, ← hshape]; exact a.isLt
  constructor
  · have he := innerProd_unit (tensorExpansion B r.factors).toList (List.replicate (B^d) 𝟙)
      a.val (by simpa using hs) (by simpa using hb) (by simpa using ht)
    simpa using he
  · intro j hj
    rw [ht j hj]
    split <;> simp
theorem tensorShout_batch_sound (B d : Nat) (table : Array F) (rs : Array (TensorShoutRead B))
    (h : verifyTensorShoutBatch B d table rs = true) (j : Nat) (hj : j < rs.size) :
    ∃ a : Fin table.size, rs[j].value = table[a] := by
  obtain ⟨a, _, hv, _⟩ := tensorShout_sound B d table rs[j] (Array.all_eq_true.mp h j hj)
  exact ⟨a, hv⟩
theorem verifyTensorShoutRead_complete (B d : Nat) (table : Array F) (is : List (Fin B))
    (hb : 2 ≤ B) (hd : 1 ≤ d) (hl : is.length = d) (ht : table.size = B^d) :
    ∃ v, verifyTensorShoutRead B d table ⟨is, (is.map basisFactor).toArray, v⟩ = true := by
  have ha : radixAddress is < table.size := ht ▸ hl ▸ radixAddress_lt is
  exact ⟨table[radixAddress is], by simp [verifyTensorShoutRead, hb, hd, hl, ht, checkFactors, Array.getElem?_eq_getElem ha]⟩
theorem verifyTensorShoutBatch_complete (B d : Nat) (table : Array F)
    (hb : 2 ≤ B) (hd : 1 ≤ d) (ht : table.size = B^d) :
    ∃ r, verifyTensorShoutBatch B d table #[r] = true := by
  obtain ⟨v, hv⟩ := verifyTensorShoutRead_complete B d table (radixDigits B (by omega) d 0) hb hd (radixDigits_length B (by omega) d 0) ht
  exact ⟨_, by simpa [verifyTensorShoutBatch] using hv⟩
/-- Indices and every factor coefficient are bound, with list lengths preserved. -/
def shoutFactorsPreimage {B : Nat} (rs : Array (TensorShoutRead B)) : List UInt8 :=
  (encodeFrame "OBEND.TENSOR-SHOUT/FACTORS/v1".toUTF8 (TranscriptEncode.encodeTranscriptBytes
    (rs.toList.map fun r => (r.indices.map Fin.val, r.factors.toList.map Array.toList))) ByteArray.empty).data.toList
def shoutFactorsDigest {B : Nat} (rs : Array (TensorShoutRead B)) : Digest32 :=
  evalDigest32 deployedCanopyHash32 (shoutFactorsPreimage rs)
theorem shoutFactorsDigest_binds {B : Nat} (rs ss : Array (TensorShoutRead B))
    (h : shoutFactorsDigest rs = shoutFactorsDigest ss) :
    (rs.toList.map fun r => (r.indices.map Fin.val, r.factors.toList.map Array.toList)) =
      (ss.toList.map fun r => (r.indices.map Fin.val, r.factors.toList.map Array.toList)) ∨
    CollisionAmong deployedCanopyHash32.eval (fun m => m = shoutFactorsPreimage rs ∨ m = shoutFactorsPreimage ss) := by
  by_cases he : shoutFactorsPreimage rs = shoutFactorsPreimage ss
  · exact .inl (LawfulTranscriptEncode.encodeTranscriptBytes_injective
      (encodeFrame_injective (byteArray_eq_of_toList_eq he)).2.1)
  · refine .inr ⟨_, _, Or.inl rfl, Or.inr rfl, he, ?_⟩
    have hh := congrArg (fun d : Digest32 => ofBE d.bytes.data.toList) h
    simpa only [shoutFactorsDigest, evalDigest32, Native.bytesOfList_toList] using hh
def absorbShoutCommitments (B d : Nat) (tableDigest factorsDigest : Digest32) (values : List F) :
    Transcript .instanceBound :=
  (bindInstance (B, d, tableDigest.bytes, factorsDigest.bytes, values) context).transcript
theorem absorbShoutCommitments_eq (B d : Nat) (td fd : Digest32) (vs : List F) :
    absorbShoutCommitments context B d td fd vs =
      (bindInstance (B, d, td.bytes, fd.bytes, vs) context).transcript := by
  unfold absorbShoutCommitments; rfl
def extractShoutBinding (B d B' d' : Nat) (td fd td' fd' : Digest32) (vs vs' : List F)
    (h : (absorbShoutCommitments context B d td fd vs).state =
      (absorbShoutCommitments context B' d' td' fd' vs').state) :=
  extractBindInstanceOrEq (B, d, td.bytes, fd.bytes, vs) (B', d', td'.bytes, fd'.bytes, vs') context context h
def shoutBatchTranscript (B d : Nat) (table : Array F) (rs : Array (TensorShoutRead B)) :
    Transcript .instanceBound :=
  absorbShoutCommitments context B d (witnessCommitment table) (shoutFactorsDigest rs) (rs.toList.map (·.value))
/-- Horner batching uses sparse selected-cell reads; soundness below connects these
reads to the actual tensor inner products, without allocating dense tensors. -/
def batchedReadInnerProd {B : Nat} (γ : F) (rs : Array (TensorShoutRead B)) (table : Array F) : F :=
  rs.foldr (fun r acc => table[radixAddress r.indices]?.getD 𝟘 ⊞ (γ ⊠ acc)) 𝟘
def batchedClaimedValue {B : Nat} (γ : F) (rs : Array (TensorShoutRead B)) : F :=
  rs.foldr (fun r acc => r.value ⊞ (γ ⊠ acc)) 𝟘
def verifyBoundTensorShoutBatch (B d : Nat) (table : Array F) (rs : Array (TensorShoutRead B)) : Bool :=
  let γ := (TranscriptChallenge.squeezeChallenge (R := F) (shoutBatchTranscript context B d table rs)).1
  verifyTensorShoutBatch B d table rs && decide (batchedReadInnerProd γ rs table = batchedClaimedValue γ rs)
/-- Exact per-read checking makes the algebraic error branch unnecessary: this is
stronger than a Schwartz–Zippel alternative. γ is never a caller-supplied input. -/
theorem boundTensorShout_sound_or_schwartzZippel (B d : Nat) (table : Array F) (rs : Array (TensorShoutRead B))
    (h : verifyBoundTensorShoutBatch context B d table rs = true) :
    (∀ j (hj : j < rs.size), innerProd (tensorExpansion B rs[j].factors).toList table.toList = rs[j].value) ∧
    let tr := (bindInstance (B, d, (witnessCommitment table).bytes, (shoutFactorsDigest rs).bytes,
      rs.toList.map (·.value)) context).transcript
    let γ := (TranscriptChallenge.squeezeChallenge (R := F) tr).1
    batchedReadInnerProd γ rs table = batchedClaimedValue γ rs := by
  simp only [verifyBoundTensorShoutBatch, shoutBatchTranscript, absorbShoutCommitments_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun j hj => ?_, h.2⟩
  obtain ⟨_, _, _, _, _, hi⟩ := tensorShout_sound B d table rs[j] (Array.all_eq_true.mp h.1 j hj); exact hi
theorem batchedReadInnerProd_refines (B d : Nat) (γ : F) (table : Array F) (rs : Array (TensorShoutRead B))
    (h : verifyTensorShoutBatch B d table rs = true) : batchedReadInnerProd γ rs table =
    rs.toList.foldr (fun r acc => innerProd (tensorExpansion B r.factors).toList table.toList ⊞ (γ ⊠ acc)) 𝟘 := by
  have he : ∀ r ∈ rs.toList, table[radixAddress r.indices]?.getD 𝟘 =
      innerProd (tensorExpansion B r.factors).toList table.toList := by
    intro r hr
    have hv := (Array.all_eq_true_iff_forall_mem.mp h) r (by simpa using hr)
    obtain ⟨_, _, _, _, _, hs⟩ := tensorShout_sound B d table r hv
    simp only [verifyTensorShoutRead, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [hv.2]; exact hs.symm
  have hm := List.map_congr_left he
  have hh := congrArg (fun xs : List F => xs.foldr (fun v acc => v ⊞ (γ ⊠ acc)) 𝟘) hm
  simpa only [List.foldr_map, batchedReadInnerProd, ← Array.foldr_toList] using hh
theorem verifyBoundTensorShoutBatch_complete (B d : Nat) (table : Array F) (rs : Array (TensorShoutRead B))
    (h : verifyTensorShoutBatch B d table rs = true) : verifyBoundTensorShoutBatch context B d table rs = true := by
  have he : ∀ r ∈ rs.toList, table[radixAddress r.indices]?.getD 𝟘 = r.value := by
    intro r hr
    have hv := (Array.all_eq_true_iff_forall_mem.mp h) r (by simpa using hr)
    simp only [verifyTensorShoutRead, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [hv.2]; rfl
  have hf (γ : F) : batchedReadInnerProd γ rs table = batchedClaimedValue γ rs := by
    simp only [batchedReadInnerProd, batchedClaimedValue, ← Array.foldr_toList]
    have hm : rs.toList.map (fun r => table[radixAddress r.indices]?.getD 𝟘) = rs.toList.map (·.value) :=
      List.map_congr_left he
    have hh := congrArg (fun xs : List F => xs.foldr (fun v acc => v ⊞ (γ ⊠ acc)) 𝟘) hm
    simpa only [List.foldr_map] using hh
  simp only [verifyBoundTensorShoutBatch, h, hf, decide_true, Bool.and_self]
theorem tensorShout_witness_size {B : Nat} (r : TensorShoutRead B)
    (h : checkFactors r.indices r.factors = true) :
    (r.factors.toList.map Array.size).sum = r.indices.length * B := by
  rw [(checkFactors_sound _ _ h).1]
  simp only [List.map_map, Function.comp_def, basisFactor, Array.size_ofFn]
  induction r.indices with
  | nil => simp
  | cons i is ih => simp [ih, Nat.add_mul, Nat.add_comm]
/-- The sole equality corner for d≥2, B≥2 is (d,B)=(2,2). -/
theorem tensorShout_witness_sublinear (B d : Nat) (hb : 2 ≤ B) (hd : 2 ≤ d)
    (hne : d ≠ 2 ∨ B ≠ 2) : d * B < B^d := by
  have base : 3 * B < B^3 := by
    have h4 : 4 ≤ B * B := Nat.mul_le_mul hb hb
    have hm := Nat.mul_lt_mul_of_pos_right (show 3 < B * B by omega) (show 0 < B by omega)
    simpa [Nat.pow_succ, Nat.mul_assoc] using hm
  have grow : ∀ n, 3 ≤ n → n * B < B^n := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn3 : n = 2
      · subst n; exact base
      have hn : 3 ≤ n := by omega
      have ih := ih hn
      have he : (n+1)*B ≤ (n*B)*B := by
        have h := Nat.mul_le_mul_left n hb
        exact Nat.mul_le_mul_right B (by omega)
      have hm := Nat.mul_lt_mul_of_pos_right ih (show 0 < B by omega)
      exact Nat.lt_of_le_of_lt he (by simpa [Nat.pow_succ] using hm)
  by_cases h : d = 2
  · subst d
    have hb3 : 3 ≤ B := by omega
    simpa [Nat.pow_two] using Nat.mul_lt_mul_of_pos_right (show 2 < B by omega) (show 0 < B by omega)
  · exact grow d (by omega)
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
