module
public import Obend.Crypto.FastRing
import all Obend.Crypto.FastRing
public import Obend.Crypto.PikkuFoldLayered
import all Obend.Crypto.PikkuFoldLayered
public import Obend.Crypto.CanopyReduce
import all Obend.Crypto.CanopyReduce
import all Obend.Crypto.PCS
public meta import Obend.Crypto.Multilinear
public meta import Obend.Crypto.Transcript
public meta import Obend.Crypto.PCS
import Obend.Tactic.Tooth

public section
namespace Obend.Crypto.Fast.Tests
open Canopy

@[expose] def basis (d k : Nat) : FastIntPoly d := Sized.ofFn fun i => if i.val = k then 1 else 0

@[expose] def vector8 : FastIntPoly 8 := ⟨#[1, 2, 3, 4, 5, 6, 7, 8], rfl⟩
@[expose] def vector16 : FastIntPoly 16 := ⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], rfl⟩

#guard (negacyclicMulInt vector8 (basis 8 1)).coeffs = #[-8, 1, 2, 3, 4, 5, 6, 7]
#guard (negacyclicMulInt vector16 (basis 16 1)).coeffs = #[-16, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
example : (negacyclicMulInt vector8 vector8).spec = negacyclicSpec vector8.spec vector8.spec :=
  negacyclicMulFast_eq_spec _ _
example : normInfFast vector8.coeffs = 8 := by decide +kernel
example : checkShort 8 8 vector8.coeffs = true := by decide +kernel
example : checkShort 7 8 vector8.coeffs = false := by decide +kernel
example : checkShort 8 7 vector8.coeffs = false := by decide +kernel
example : checked 2 (#[0, 0, 1] : Array Int) = none := by decide +kernel

@[expose] def goldBasis (d k : Nat) : FastGoldilocksRing d :=
  Sized.ofFn fun i => if i.val = k then Goldilocks.one else Goldilocks.zero


#guard ((FastGoldilocksRing.negacyclicMulFast (goldBasis 8 7) (goldBasis 8 1)).spec ⟨0, by decide +kernel⟩).val =
    18446744069414584320

#guard ((FastGoldilocksRing.negacyclicMulFast (goldBasis 16 15) (goldBasis 16 1)).spec ⟨0, by decide +kernel⟩).val =
    18446744069414584320

@[expose] def twoRows : TernaryMatrix 2 2 := ⟨#[#[⟨⟨0, by decide +kernel⟩, false⟩, ⟨⟨1, by decide +kernel⟩, true⟩],
  #[⟨⟨0, by decide +kernel⟩, false⟩, ⟨⟨1, by decide +kernel⟩, false⟩]], rfl⟩
@[expose] def threeLayers : Layers 2 2 := .step twoRows (.step twoRows (.step twoRows (.done 2)))
@[expose] def smallWitness : FastIntPoly 2 := ⟨#[3, -2], rfl⟩

example : (threeLayers.apply smallWitness).coeffs = #[-2, 10] := by decide +kernel
example : threeLayers.weight = 8 := by decide +kernel
example : normInfFast (threeLayers.apply smallWitness).coeffs ≤ 8*3 :=
  normInf_layeredKronecker_le threeLayers smallWitness 3 (by decide +kernel)
example : (applyKroneckerTernary 2 twoRows ⟨#[3, -2, 4, 1], rfl⟩).coeffs = #[5, 1, 3, 5] := by decide +kernel
example : (foldWitness 2 smallWitness smallWitness).coeffs = #[9, -6] := by decide +kernel
example : (akitaFold (m := 4) 2 vector8).coeffs = #[11, 14, 17, 20] := by decide +kernel
example : (akitaFoldRounds 1 [2, 3, 4] vector8).coeffs = #[358] := by decide +kernel
example : (akitaFoldRounds 1 [2, 3, 4] vector8).coeffs.size = 1 := (akitaFoldRounds 1 [2, 3, 4] vector8).size_eq

@[expose] def sumMatrix : IntMatrix 1 2 := ⟨#[⟨#[1, 1], rfl⟩], rfl⟩
@[expose] def openA : FastIntPoly 2 := ⟨#[1, 0], rfl⟩
@[expose] def openB : FastIntPoly 2 := ⟨#[0, 1], rfl⟩
@[expose] def extracted : MSISBreakWitness sumMatrix 17 2 :=
  foldTwoInstances_binding_reduction sumMatrix 17 1 openA openB (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : extracted.z.coeffs = #[1, -1] := by decide +kernel
example : matVecModQ sumMatrix 17 extracted.z = zeroVec 1 := extracted.kernel
example : normInfFast extracted.z.coeffs ≤ 2 := extracted.short

@[expose] def boundFold := foldTranscript ByteArray.empty (encodeInts (matVec sumMatrix openA)) ByteArray.empty
  (encodeInts (matVec sumMatrix openB)) ByteArray.empty
#guard boundFold.stepCount == 1
#guard (foldFromTranscript boundFold openA openB).2.stepCount == 2
#guard (foldFromTranscript boundFold openA openB).1.coeffs.size == 2

@[expose] def cfg : Config := ⟨2, 2, by decide +kernel, 2, .primeField, .uniqueDecodingRadius, .primeUDR⟩
@[expose] def table : Table cfg := Sized.ofFn fun i =>
  ⟨#[Goldilocks.ofNat i.val, Goldilocks.ofNat (i.val+1)], rfl⟩
@[expose] def queries : Array (Query cfg) := #[⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨4, by decide +kernel⟩, ⟨15, by decide +kernel⟩]
@[expose] def opening := openBatchCanopy cfg table queries

example : verifyBatchCanopy cfg (commit cfg table) queries opening = true :=
  verifyBatchCanopy_complete cfg table queries
example : (opening.rows.spec ⟨2, by decide +kernel⟩).coeffs = #[Goldilocks.ofNat 4, Goldilocks.ofNat 5] := rfl
example : canopyBatchHashes 4 4 2 = 11 := rfl
example : naiveMerkleBatchHashes 4 4 = 16 := rfl
example : canopyBatchHashes 4 4 2 < naiveMerkleBatchHashes 4 4 := canopy_hash_count_strictly_less 4 4 2 (by decide +kernel) (by decide +kernel)
example : 100 * canopyBatchHashes 64 16 7 ≤ 69 * naiveMerkleBatchHashes 64 16 := by decide +kernel
example : 100 * canopyBatchHashes 128 16 8 ≤ 63 * naiveMerkleBatchHashes 128 16 := by decide +kernel

-- Executable cSHAKE checks supplement the universal kernel proofs above.
#guard verifyBatchCanopy cfg (commit cfg table) queries opening

@[expose] def forgedRows : BatchOpening cfg queries := { opening with
  rows := Sized.ofFn fun j => if j.val = 0 then ⟨#[Goldilocks.ofNat 99, Goldilocks.zero], rfl⟩ else opening.rows.spec j }
#guard !(verifyBatchCanopy cfg (commit cfg table) queries forgedRows)

@[expose] def forgedCap : BatchOpening cfg queries := { opening with
  cap := Sized.ofFn fun i => if i.val = 0 then hashRow 100 #[] else opening.cap.spec i }
#guard !(verifyBatchCanopy cfg (commit cfg table) queries forgedCap)

#tooth checkShort_iff by mutation checkShort := fun _ _ _ => true
#tooth wrapSign_high by mutation wrapSign := fun _ _ x => x
#tooth normInf_ternary_le by mutation sparseRow := fun _ _ => 1000000
#tooth verifyBatchCanopy_complete by mutation verifyBatchCanopy := fun _ _ _ _ => false
#tooth checkProximityConfig_iff by mutation checkProximityConfig := fun _ _ => true

-- Split boundaries: empty ring, degree one, and a dense signed convolution.
example : (negacyclicMulFast (zeroVec 0) (zeroVec 0)).coeffs = #[] := by decide +kernel
#guard (negacyclicMulFast ⟨#[-3], rfl⟩ ⟨#[7], rfl⟩).coeffs = #[-21]
#guard (negacyclicMulFast ⟨#[1,-2,3,-4], rfl⟩ ⟨#[-5,6,-7,8], rfl⟩).coeffs = #[56,-36,-2,60]
example : (negacyclicMulFast vector8 vector8).spec = negacyclicSpec vector8.spec vector8.spec :=
  negacyclicMulFast_eq_spec _ _
example : FastGoldilocksRing.cycloSpec
    (FastGoldilocksRing.negacyclicMulFast (goldBasis 8 7) (goldBasis 8 1)) =
    cycloMul (by decide +kernel) (FastGoldilocksRing.cycloSpec (goldBasis 8 7)) (FastGoldilocksRing.cycloSpec (goldBasis 8 1)) :=
  FastGoldilocksRing.negacyclicMulFast_eq_spec _ _
example : canonicalGoldilocksOfUInt64 0 = some Goldilocks.zero := by decide +kernel
example : canonicalGoldilocksOfUInt64 18446744069414584321 = none := by decide +kernel
example : (canonicalGoldilocksOfUInt64 18446744069414584320).map Goldilocks.val = some 18446744069414584320 := by decide +kernel
example : canonicalGoldilocksOfUInt64 18446744073709551615 = none := by decide +kernel
example : (applyKroneckerTernaryFast 2 twoRows ⟨#[3,-2,4,1], rfl⟩).coeffs = #[5,1,3,5] := by decide +kernel
example : applyKroneckerTernaryFast 2 twoRows ⟨#[3,-2,4,1], rfl⟩ =
    applyTernary (kronecker 2 twoRows) ⟨#[3,-2,4,1], rfl⟩ := applyKroneckerTernaryFast_eq_spec _ _ _
example : rowWeight (kronecker 10 twoRows) ≤ rowWeight twoRows := rowWeight_kronecker_le _ _
example : normInfFast (threeLayers.apply smallWitness).coeffs ≤ 2^threeLayers.length*3 :=
  normInf_uniformLayers_le threeLayers 2 3 (by simp only [threeLayers, Layers.uniform]; decide +kernel) smallWitness (by decide +kernel)

@[expose] def akitaInput : FastIntPoly 4 := ⟨#[3,-2,4,1], rfl⟩
example : matVecModQ sumMatrix 17 (akitaFold 2 akitaInput) =
    foldModQ 17 2 (matVecModQ sumMatrix 17 (splitLo akitaInput)) (matVecModQ sumMatrix 17 (splitHi akitaInput)) :=
  matVecModQ_akitaFold _ _ _ _
example : (matVecModQ sumMatrix 17 (akitaFold 2 akitaInput)).coeffs = #[11] := by decide +kernel

@[expose] def challengeU : FastIntPoly 4 := ⟨#[1,0,0,1], rfl⟩
@[expose] def challengeV : FastIntPoly 4 := ⟨#[0,1,1,0], rfl⟩
@[expose] def challengeExtract := akitaTwoChallenge_extract_sis sumMatrix 17 1 0 2 (by decide +kernel)
  challengeU challengeV (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : challengeExtract.z.coeffs = #[1,-1] := by decide +kernel
-- The first folds coincide here; extraction must use the second challenge.
@[expose] def challengeLateU : FastIntPoly 4 := ⟨#[0,0,1,0], rfl⟩
@[expose] def challengeLateV : FastIntPoly 4 := ⟨#[0,0,0,1], rfl⟩
@[expose] def challengeLateExtract := akitaTwoChallenge_extract_sis sumMatrix 17 1 0 2 (by decide +kernel)
  challengeLateU challengeLateV (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : challengeLateExtract.z.coeffs = #[2,-2] := by decide +kernel

@[expose] def evalWeights : Sized Goldilocks 2 := ⟨#[Goldilocks.ofNat 2, Goldilocks.ofNat 3], rfl⟩
@[expose] def evalRows : Sized (Sized Goldilocks 2) 2 :=
  ⟨#[⟨#[Goldilocks.ofNat 1,Goldilocks.ofNat 2],rfl⟩,
      ⟨#[Goldilocks.ofNat 3,Goldilocks.ofNat 4],rfl⟩],rfl⟩
#guard (evalRow evalWeights (iacc (Goldilocks.ofNat 5) evalRows)).val = 58
example : evalRow evalWeights (iacc (Goldilocks.ofNat 5) evalRows) =
    evalRows.coeffs.foldl (fun acc row => Goldilocks.add (canopyMul (Goldilocks.ofNat 5) acc)
      (evalRow evalWeights row)) Goldilocks.zero := evalRow_iacc _ _ _
example : ifold (n := 1) (Goldilocks.ofNat 7) (iacc (Goldilocks.ofNat 5) evalRows) =
    iacc (Goldilocks.ofNat 5) (foldRows (w := 1) (Goldilocks.ofNat 7) evalRows) := ifold_iacc _ _ _

-- Two rows, width one: the integer witnesses share a lattice commitment.
@[expose] def dualCfg : Config := ⟨0,1,by decide +kernel,1,.primeField,.uniqueDecodingRadius,.primeUDR⟩
@[expose] def dualQueries : Array (Query dualCfg) := #[⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩]
@[expose] def dualTable := encodeWitness dualCfg 1 openA
@[expose] def dualOpening := openBatchCanopy dualCfg dualTable dualQueries

@[expose] def dualSIS := extractDualDiscrepancy dualCfg 1 sumMatrix 17 openA openB
  (commit dualCfg dualTable) (matVecModQ sumMatrix 17 openA) rfl dualQueries dualOpening ⟨0,by decide +kernel⟩
  (verifyBatchCanopy_complete _ _ _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
#guard (match dualSIS with | .inl _ => #[] | .inr z => z.z.coeffs) = #[-1,1]

-- These are branch proofs over arbitrary accepted adversarial data, not a claim to
-- have found a concrete cSHAKE collision. Acceptance is deliberately retained.
private theorem dual_hash_branch {m : Nat} (cfg : Config) (β : Nat)
    (A : IntMatrix m (2^(cfg.bottomDepth+cfg.capDepth)*cfg.width)) (q : Nat)
    (wRef u : Witness cfg) (digest : Digest32) (cmLat : FastIntPoly m)
    (hRef : commitDual cfg β A q wRef = (digest,cmLat))
    (qs : Array (Query cfg)) (p : BatchOpening cfg qs) (j : Fin qs.size)
    (hp : verifyBatchCanopy cfg digest qs p = true) (hLat : matVecModQ A q u = cmLat)
    (hu : normInfFast u.coeffs ≤ β) (hr : normInfFast wRef.coeffs ≤ β)
    (hne : p.rows.spec j ≠ encodeRowOf cfg β u qs[j.val])
    (href : p.rows.spec j ≠ encodeRowOf cfg β wRef qs[j.val]) :
    (match extractDualDiscrepancy cfg β A q wRef u digest cmLat hRef qs p j hp hLat hu hr hne with
      | .inl _ => true | .inr _ => false) = true := by
  simp only [extractDualDiscrepancy, href, ↓reduceDIte]

private theorem dual_double_opening_kernel {m : Nat} (cfg : Config) (β : Nat)
    (hβ : 2*β < Obend.Apps.ZkNtt.goldilocksPrime)
    (A : IntMatrix m (2^(cfg.bottomDepth+cfg.capDepth)*cfg.width)) (q : Nat)
    (u v : Witness cfg) (digest : Digest32) (qs : Array (Query cfg)) (j : Fin qs.size)
    (p r : BatchOpening cfg qs)
    (hpu : p.rows.spec j = encodeRowOf cfg β u qs[j.val])
    (hrv : r.rows.spec j = encodeRowOf cfg β v qs[j.val])
    (hu : normInfFast u.coeffs ≤ β) (hv : normInfFast v.coeffs ≤ β)
    (hp : verifyBatchCanopy cfg digest qs p = true) (hr : verifyBatchCanopy cfg digest qs r = true)
    (hne : witnessRow cfg u qs[j.val] ≠ witnessRow cfg v qs[j.val])
    (hcm : matVecModQ A q u = matVecModQ A q v) :
    (extractDualDoubleOpening cfg β hβ A q u v digest qs j p r hpu hrv hu hv hp hr hne hcm).2.z = intSub u v := rfl

#guard verifyCanopyCommitAndReduce cfg (w := 1) rfl (commit cfg table) queries opening
  (Goldilocks.ofNat 7) (Goldilocks.ofNat 5) (Sized.ofFn fun _ => Goldilocks.one)
  (evalRow (Sized.ofFn fun _ => Goldilocks.one)
    (ifold (Goldilocks.ofNat 7) (iacc (Goldilocks.ofNat 5) (pairedRows (w := 1) cfg rfl opening.rows))))

#tooth negacyclicMulFast_eq_spec by mutation negacyclicMulFast := fun _ _ => Sized.ofFn fun _ => 0
#tooth FastGoldilocksRing.negacyclicMulFast_eq_spec by mutation FastGoldilocksRing.negacyclicMulFast := fun _ _ => Sized.ofFn fun _ => Goldilocks.zero
#tooth canonicalGoldilocksOfUInt64_injective by mutation canonicalGoldilocksOfUInt64 := fun _ => some Goldilocks.zero
#tooth applyKroneckerTernaryFast_eq_spec by mutation applyKroneckerTernaryFast := fun _ _ _ => Sized.ofFn fun _ => 0
#tooth evalRow_iacc by mutation rowScale := fun _ _ => Sized.ofFn fun _ => Goldilocks.zero
#tooth ifold_iacc by mutation ifold := fun _ _ => Sized.ofFn fun _ => Goldilocks.one
#tooth verifyCanopyCommitAndReduce_complete by mutation verifyCanopyCommitAndReduce := fun _ _ _ _ _ _ _ _ _ => false

#print axioms foldTwoInstances_binding_reduction
#print axioms akitaSplitFold_extract_sis
#print axioms akitaTwoChallenge_extract_sis
#print axioms verifyBatchCanopy_binding_collision
#print axioms verifyCanopyCommitAndReduce_binding
#print axioms extractDualDoubleOpening
#print axioms extractDualDiscrepancy
#print axioms negacyclicMulFast_eq_spec
#print axioms FastGoldilocksRing.negacyclicMulFast_eq_spec
#print axioms evalRow_iacc

-- Fail the build if any L0 reduction acquires choice, an admitted proof,
-- compiler trust, or a custom axiom. Propositional extensionality and quotient
-- soundness are Lean's kernel-supported extensionality foundations.
run_cmd do
  for n in [``foldTwoInstances_binding_reduction, ``akitaSplitFold_extract_sis,
      ``akitaTwoChallenge_extract_sis, ``verifyBatchCanopy_binding_collision,
      ``verifyCanopyCommitAndReduce_binding, ``extractDualDoubleOpening, ``extractDualDiscrepancy] do
    let axioms ← Lean.collectAxioms n
    for ax in axioms do
      unless ax == ``propext || ax == ``Quot.sound do
        throwError "L0 extractor {n} depends on forbidden axiom {ax}"

end Obend.Crypto.Fast.Tests
