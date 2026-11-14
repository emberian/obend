module
public import Obend.Crypto.BinarySpartanAndShout
import all Init.Data.Array.Basic
import all Obend.Apps.ZkNtt.Goldilocks
import all Obend.AssertAxioms
import all Obend.Core.Data
import all Obend.Core.Digest
import all Obend.Core.Machine
import all Obend.Core.MachineFast
import all Obend.Core.Term
import all Obend.Core.Ty
import all Obend.Crypto.BinarySpartanAndShout
import all Obend.Crypto.BinaryTower256
import all Obend.Crypto.CanopyReduce
import all Obend.Crypto.FastRing
import all Obend.Crypto.Multilinear
import all Obend.Crypto.PCS
import all Obend.Crypto.PikkuFoldLayered
import all Obend.Crypto.Sumcheck
import all Obend.Crypto.Transcript
import all Obend.Digest.Cshake256
import all Obend.Digest.Cshake256.Fast
import all Obend.Digest.Cshake256.Seam
import all Obend.Digest.Cshake256.Spec
import all Obend.Digest.HashBytes
import all Obend.Fold
import all Obend.Hardware.HDL
import all Obend.Hardware.PipelinedZkCrypto
import all Obend.Hardware.Process
import all Obend.Hardware.Retiming
import all Obend.Judge.Class
import all Obend.Judge.Computational
import all Obend.Law.Syntax
import all Obend.Ledger.Register
import all Obend.Receipt
import all Obend.Receipt.Merkle
import all Obend.Run.Control
import all Obend.Run.Fold
import all Obend.Run.Fork
import all Obend.Run.Proofs.Control
import all Obend.Run.Proofs.Invariant
import all Obend.Run.Proofs.Shared
import all Obend.Run.Runner
import all Obend.Run.Shared
import all Obend.Run.Spec
import all Obend.Slot
import all Obend.Slot.Integrity
import all Obend.Slot.Proofs.Protocol
import all Obend.Slot.Proofs.ProtocolTyping
import all Obend.Slot.Protocol
import all Obend.Slot.Selection
import all Obend.Slot.World
import all Obend.Tactic.Cases
import all Obend.Tactic.Tooth
import all Obend.Category.Refines
import all Obend.Crypto.GameSoundness

public section
namespace Obend.Tests.BinarySpartanAndShout
open Obend.Crypto Obend.Crypto.BinaryTower256 Obend.Crypto.BinarySpartanAndShout
set_option autoImplicit false
set_option Elab.async false
local notation "𝟘" => towerZero 7
local notation "𝟙" => towerOne 7

variable (context : Transcript .relationBound)

example : checkPcsSoundnessRegime binaryUdrPcsParams = true := binaryUdrPcsParams_valid ()
example : checkPcsSoundnessRegime primeGoldilocksPcsParams = true := primeGoldilocksPcsParams_valid ()
example : computeSoundnessBitsFloor binaryUdrPcsParams = 132 := by decide +kernel
example : checkPcsSoundnessRegime { binaryUdrPcsParams with regime := .johnsonBound } = false := by decide +kernel
example : checkPcsSoundnessRegime { binaryUdrPcsParams with regime := .capacityMca } = false := by decide +kernel
example : checkPcsSoundnessRegime { binaryUdrPcsParams with numQueries := 10 } = false := by decide +kernel
example : checkPcsSoundnessRegime { binaryUdrPcsParams with distanceNumerator := 3, distanceDenominator := 8 } = false := by decide +kernel
example : checkPcsSoundnessRegime { primeGoldilocksPcsParams with distanceNumerator := 1, distanceDenominator := 2 } = false := by decide +kernel
example : (subfieldAgreement (false,true)).length = 2 := (subfield_agreement_counterexample ()).2.1

/-- Two nonempty constraints: z₀*z₀=z₀ on both rows, with public z₀=1. -/
def circuit : R1csInstance :=
  ⟨1, 1, [⟨0,0,𝟙⟩, ⟨1,0,𝟙⟩], [⟨0,0,𝟙⟩, ⟨1,0,𝟙⟩], [⟨0,0,𝟙⟩, ⟨1,0,𝟙⟩], [(0,𝟙)]⟩
def witness : Array F := #[𝟙]
private theorem circuit_shape : checkR1csShape circuit witness = true := by decide +kernel
private theorem circuit_sat : R1csSatisfied circuit witness := by
  intro row hr
  have hh : row = 0 ∨ row = 1 := by change row < 2 at hr; omega
  rcases hh with rfl | rfl <;> simp [circuit, sparseRowSpec, witness]
example : verifyBinarySpartan context circuit (proveBinarySpartan context circuit witness) = true :=
  proveBinarySpartan_complete context circuit witness circuit_shape circuit_sat
example : (spartanSetup context circuit witness).1.length = 1 := squeezeOuter_length _ _

example : encodeR1csInstance circuit ≠ encodeR1csInstance { circuit with numCols := 2 } := by
  intro h
  have he := encodeR1csInstance_injective h
  have hn : (1 : Nat) = 2 := congrArg R1csInstance.numCols he
  exact (by decide : (1 : Nat) ≠ 2) hn
example : verifyBinarySpartan context { circuit with numCols := 2 } (proveBinarySpartan context circuit witness) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := verifyBinarySpartan_binds_instance context _ _ h
  have hn : (1 : Nat) = 2 := congrArg R1csInstance.numCols he
  exact (by decide : (1 : Nat) ≠ 2) hn

/-- The corrupted first round has endpoint sum 1 instead of the required 0. -/
def corruptRound : RoundPoly F := ⟨[𝟘,𝟙]⟩
private theorem corruptRound_bad : towerAdd 7 (corruptRound.eval 𝟘) (corruptRound.eval 𝟙) ≠ 𝟘 := by
  have hzero : corruptRound.eval 𝟘 = 𝟘 := RoundPoly.eval_linear_zero (R := F) 𝟘 𝟙
  have hone : corruptRound.eval 𝟙 = 𝟙 := by
    exact (RoundPoly.eval_linear_one (R := F) 𝟘 𝟙).trans (towerZero_add 7 𝟙)
  rw [hzero, hone, towerZero_add]
  exact towerOne_ne_zero 7

example : verifyBinarySpartan context circuit { proveBinarySpartan context circuit witness with rounds := [corruptRound] } = false :=
  verify_rejects_bad_round context _ _ (by decide +kernel) corruptRound [] rfl corruptRound_bad

/-- A genuinely unsatisfied row, whose Boolean evaluation makes G nonzero. -/
def brokenCircuit : R1csInstance := { circuit with c := [] }
example : verifyBinarySpartan context brokenCircuit (proveBinarySpartan context circuit witness) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := verifyBinarySpartan_binds_instance context _ _ h
  have hn : (2 : Nat) = 0 := congrArg (fun i => i.c.length) he
  exact (by decide : (2 : Nat) ≠ 0) hn

private theorem broken_nonzero : discrepancy brokenCircuit witness 0 ≠ 𝟘 := by
  simp only [discrepancy, sparseRow_exec_eq_spec]
  simp [sparseRowSpec, brokenCircuit, circuit, witness, towerOne_ne_zero]
example : ∃ bs ∈ hypercube brokenCircuit.logRows,
    mleEval (discrepancyTable brokenCircuit witness) (bs.map (bitElem (R := F))) ≠ 𝟘 :=
  discrepancy_polynomial_nonzero _ _ 0 (by decide +kernel) broken_nonzero
private theorem broken_rejected : checkAllRows brokenCircuit witness = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact broken_nonzero ((discrepancy_zero_iff _ _ _).mpr ((checkAllRows_iff _ _).mp h 0 (by decide +kernel)))

/-- The lookup table has four rows and an address of two bits. -/
def table : Array F := #[𝟘,𝟙,𝟘,𝟘]
def read3 : TensorShoutRead 3 :=
  ⟨[1,2,1], #[(basisFactor (1 : Fin 3)), basisFactor (2 : Fin 3), basisFactor (1 : Fin 3)], 𝟙⟩
def table3 : Array F := basisFactor (16 : Fin 27)
def read4 : TensorShoutRead 2 :=
  ⟨[1,0,1,1], #[basisFactor (1 : Fin 2), basisFactor (0 : Fin 2),
    basisFactor (1 : Fin 2), basisFactor (1 : Fin 2)], 𝟙⟩
def table4 : Array F := basisFactor (13 : Fin 16)
example : verifyTensorShoutRead 3 3 table3 read3 = true := by decide +kernel
example : verifyTensorShoutRead 2 4 table4 read4 = true := by decide +kernel
example : verifyTensorShoutBatch 3 3 table3 #[read3,read3] = true := by decide +kernel
example : verifyTensorShoutRead 3 3 table3 { read3 with value := 𝟘 } = false := by decide +kernel
example : verifyTensorShoutRead 3 3 table3 { read3 with factors := #[#[𝟙,𝟙,𝟙],basisFactor (2 : Fin 3),basisFactor (1 : Fin 3)] } = false := by decide +kernel
example : verifyTensorShoutRead 3 3 table3 { read3 with factors := #[] } = false := by decide +kernel
example : verifyTensorShoutRead 3 4 table3 read3 = false := by decide +kernel
example : 3*3 < 3^3 := tensorShout_witness_sublinear 3 3 (by decide) (by decide) (by decide)
example : 4*2 < 2^4 := tensorShout_witness_sublinear 2 4 (by decide) (by decide) (by decide)
example : ¬ 2*2 < 2^2 := by decide
example : radixAddress read3.indices = 16 ∧ radixAddress read4.indices = 13 := by decide +kernel
example : towerAdd 7 (towerAdd 7 𝟙 𝟙) 𝟙 = 𝟙 := (tripleHot_sum_is_one 𝟘).1
example : innerProd (tensorExpansion 3 read3.factors).toList table3.toList = 𝟙 :=
  (tensorShout_sound 3 3 table3 read3 (by decide +kernel)).choose_spec.2.2.2.2
example : innerProd (tensorExpansion 2 read4.factors).toList (List.replicate 16 𝟙) = 𝟙 :=
  (tensorShout_boolean_unit 2 4 table4 read4 (by decide +kernel)).1

def audit : AuditObject := ⟨circuit, witness, binaryUdrPcsParams, table, [true,false], 𝟙⟩
private theorem audit_ok : auditCheck audit = .ok := by
  apply (auditCheck_iff _).mpr
  exact ⟨(checkR1csShape_iff _ _).mp circuit_shape, circuit_sat,
    (checkPcsSoundnessRegime_iff _).mp (binaryUdrPcsParams_valid ()), rfl, rfl⟩
example : auditCheck audit = .ok := audit_ok
example : binarySpartanShoutJudge.Fragment audit := True.intro
example : binarySpartanShoutJudge.check 0 audit () = .ok := audit_ok
example : auditCheck { audit with statement := brokenCircuit } = .refused .constraint [] := by
  have hs : checkR1csShape brokenCircuit witness = true := by decide +kernel
  simp only [auditCheck, audit, hs, Bool.true_eq_false, ite_false, broken_rejected, ite_true]
example : auditCheck { audit with value := 𝟘 } = .refused .lookup [] := by
  have hr := (checkAllRows_iff _ _).mpr circuit_sat
  simp only [auditCheck, audit, circuit_shape, hr, binaryUdrPcsParams_valid (), Bool.true_eq_false, ite_false]
  decide +kernel
example : auditCheck { audit with params := { binaryUdrPcsParams with numQueries := 10 } } = .refused .proximity [] := by
  have hr := (checkAllRows_iff _ _).mpr circuit_sat
  have hp : checkPcsSoundnessRegime { binaryUdrPcsParams with numQueries := 10 } = false := by decide +kernel
  simp only [auditCheck, audit, circuit_shape, hr, Bool.true_eq_false, ite_false, hp, ite_true]

example : verifySparseInner context circuit witness circuit.a 0 1 (sparseRowSpec circuit.a witness 0)
    (proveSparseInner context circuit witness circuit.a 0 1) = true :=
  proveSparseInner_complete context _ _ _ _ _ (Or.inl rfl) (by decide +kernel)

/-- A real seed demonstrates that the context-indexed API is inhabited. -/
example : ∃ tr : Transcript .relationBound,
    verifyBinarySpartan tr circuit (proveBinarySpartan tr circuit witness) = true :=
  ⟨bindRelation "binary-spartan-shout@1" ByteArray.empty ByteArray.empty (Transcript.newUnseeded ByteArray.empty),
    proveBinarySpartan_complete _ _ _ circuit_shape circuit_sat⟩

example (a b : Tower128) :
    Obend.Hardware.PipelinedZkCrypto.towerMul 7 (packTower 7 a) (packTower 7 b) =
      packTower 7 (towerMul 7 a b) := hardware_mul_refines 7 a b
example (i : R1csInstance) (z : Array F) : discrepancyTableExec i z = discrepancyTable i z :=
  discrepancyTable_exec_eq_spec i z
example (p : RoundPoly F) (roots : List F) (hn : roots.Nodup)
    (hd : p.coeffs.length ≤ 4) (hp : ∃ x, p.eval x ≠ 𝟘) (hr : ∀ x ∈ roots, p.eval x = 𝟘) :
    roots.length ≤ 3 := polynomial_roots_count 3 p roots hn hd hp hr

example : PolynomialRootHit 1 (⟨[𝟘,𝟙]⟩ : RoundPoly F) 𝟘 := by
  refine ⟨by decide, ⟨𝟙, ?_⟩, RoundPoly.eval_linear_zero 𝟘 𝟙⟩
  have he := RoundPoly.eval_linear_one (R := F) 𝟘 𝟙
  have hz : (⟨[𝟘,𝟙]⟩ : RoundPoly F).eval 𝟙 = 𝟙 := he.trans (towerZero_add 7 𝟙)
  rw [hz]
  exact towerOne_ne_zero 7

#tooth binaryAdditive_refuses_beyond_udr by mutation checkPcsSoundnessRegime := fun _ => true
#tooth pcs_sampling_bound by mutation checkPcsSoundnessRegime := fun p => decide (regimeDistance p)
#tooth verifyBinarySpartan_binds_instance by mutation verifyBinarySpartan := fun _ _ _ => true
#tooth verify_rejects_bad_round by mutation verifyBinarySpartan := fun _ _ _ => true
#tooth tensorShout_sound by mutation verifyTensorShoutRead := fun _ _ _ _ => true
#tooth tensorShout_sound by mutation checkFactors := fun _ _ => true
#tooth tensorProduct_basis by mutation tensorProduct := fun _ _ _ => 𝟙
#tooth tensorShout_witness_size by mutation checkFactors := fun _ _ => true
#tooth binarySpartan_verify_sound_or_schwartzZippel by mutation verifyBinarySpartan := fun _ _ _ => true
#tooth witnessCommitment_binds by mutation witnessCommitment := fun _ => ⟨⟨Array.replicate 32 0⟩, by decide⟩
#tooth r1cs_binding_or_collision by mutation encodeR1csInstance := fun _ => ByteArray.empty
#tooth encodeR1csInstance_injective by mutation encodeR1csInstance := fun _ => ByteArray.empty
#tooth discrepancyTable_exec_eq_spec by mutation discrepancyTableExec := fun _ _ => []
#tooth auditCheck_iff by mutation checkAllRows := fun _ _ => true

/-- Honest proving on the broken relation, rather than an instance-mismatch rejection. -/
def seeded : Transcript .relationBound := bindRelation "B1-regression" ByteArray.empty ByteArray.empty
  (Transcript.newUnseeded ByteArray.empty)
#guard !verifyBinarySpartan seeded brokenCircuit (proveBinarySpartan seeded brokenCircuit witness)
#guard verifyBinarySpartan seeded circuit (proveBinarySpartan seeded circuit witness)

open Obend.Digest.Cshake256 Obend.Digest.HashBytes
local infixl:65 " ⊞ " => towerAdd 7

def salt : Digest32 := ⟨⟨Array.replicate 32 0⟩, by decide⟩
def otherSalt : Digest32 := ⟨⟨Array.replicate 32 1⟩, by decide⟩
example : saltedWitnessPreimage witness salt ≠ saltedWitnessPreimage witness otherSalt := by
  intro h
  exact (by decide +kernel : salt ≠ otherSalt) (saltedWitnessPreimage_injective h).2
example : saltedWitnessPreimage witness salt ≠ saltedWitnessPreimage #[𝟘] salt := by
  intro h
  exact (by decide +kernel : witness ≠ #[𝟘]) (saltedWitnessPreimage_injective h).1
example : blindEval 𝟘 𝟙 = 𝟙 ∧ blindEval 𝟙 𝟙 = 𝟘 := by simp [blindEval]
example (v₀ v₁ m : F) : blindEval v₁ ((m ⊞ v₀) ⊞ v₁) = blindEval v₀ m :=
  (blindEval_bijection_hides_witness v₀ v₁).2.2 m
example (n : Nat) (m : F) : hypercubeSum (n+1) [m,m] = 𝟘 := pairedMask_zeroSum n m
example : hypercubeSum 1 (maskedTable [𝟘,𝟙] [𝟙,𝟙]) = hypercubeSum 1 [𝟘,𝟙] :=
  maskedTable_hypercubeSum_eq 1 _ _ rfl (pairedMask_zeroSum 0 𝟙)
example : verifyBlindedSpartan context 1 #[𝟘,𝟙] #[𝟙,𝟙] salt (hypercubeSum 1 [𝟘,𝟙])
    (proveBlindedSpartan context 1 #[𝟘,𝟙] #[𝟙,𝟙] salt (hypercubeSum 1 [𝟘,𝟙])) = true :=
  proveBlindedSpartan_complete context 1 _ _ salt rfl rfl (pairedMask_zeroSum 0 𝟙)
example : verifyBoundTensorShoutBatch context 3 3 table3 #[read3,read3] = true :=
  verifyBoundTensorShoutBatch_complete context _ _ _ _ (by decide +kernel)
example : verifyBoundTensorShoutBatch context 3 3 table3 #[{ read3 with value := 𝟘 }] = false := by
  simp only [verifyBoundTensorShoutBatch]
  have h : verifyTensorShoutBatch 3 3 table3 #[{ read3 with value := 𝟘 }] = false := by decide +kernel
  rw [h, Bool.false_and]

#tooth blindEval_bijection_hides_witness by mutation blindEval := fun v _ => v
#tooth maskedTable_hypercubeSum_eq by mutation maskedTable := fun _ mask => mask
#tooth saltedWitnessCommitment_binds by mutation saltedWitnessCommitment := fun z _ => witnessCommitment z
#tooth saltedWitnessPreimage_injective by mutation saltedWitnessPreimage := fun z _ => witnessPreimage z
#tooth blindedSpartan_sound_or_schwartzZippel by mutation verifyBlindedSpartan := fun _ _ _ _ _ _ _ => true
#tooth proveBlindedSpartan_complete by mutation blindEval := fun v _ => v
#tooth spartanCommitmentSetup_eq by mutation spartanCommitmentSetup := fun tr i _ =>
  squeezeOuter i.logRows (bindInstance (i, ByteArray.empty) tr).transcript
#tooth absorbShoutCommitments_eq by mutation absorbShoutCommitments := fun tr B d td _ vs =>
  (bindInstance (B, d, td.bytes, ByteArray.empty, vs) tr).transcript
#tooth boundTensorShout_sound_or_schwartzZippel by mutation absorbShoutCommitments := fun tr B d td _ vs =>
  (bindInstance (B, d, td.bytes, ByteArray.empty, vs) tr).transcript
#tooth boundTensorShout_sound_or_schwartzZippel by mutation verifyBoundTensorShoutBatch := fun _ _ _ _ _ => true
#tooth batchedReadInnerProd_refines by mutation batchedReadInnerProd := fun _ _ _ => 𝟘
#tooth shoutFactorsDigest_binds by mutation shoutFactorsDigest := fun _ => salt

-- Executable accepted/refused wire messages; all evaluation runs only on hbox.
def blinded : BlindedSpartanOpening := proveBlindedSpartan seeded 1 #[𝟘,𝟙] #[𝟙,𝟙] salt 𝟙
#guard verifyBlindedSpartan seeded 1 #[𝟘,𝟙] #[𝟙,𝟙] salt 𝟙 blinded
#guard !verifyBlindedSpartan seeded 1 #[𝟘,𝟙] #[𝟙,𝟙] salt 𝟙 { blinded with evaluation := blinded.evaluation ⊞ 𝟙 }
#guard !verifyBlindedSpartan seeded 1 #[𝟘,𝟙] #[𝟙,𝟘] salt 𝟙 blinded
#guard !verifyBlindedSpartan seeded 1 #[𝟘,𝟙] #[𝟙,𝟙] otherSalt 𝟙 blinded
#guard verifyBoundTensorShoutBatch seeded 3 3 table3 #[read3,read3]
#guard !verifyBoundTensorShoutBatch seeded 3 3 table3 #[{ read3 with value := 𝟘 }]
#guard (spartanCommitmentSetup seeded circuit salt).1 != (spartanCommitmentSetup seeded circuit otherSalt).1
#guard (absorbShoutCommitments seeded 3 3 salt salt [𝟙]).state !=
  (absorbShoutCommitments seeded 3 3 salt otherSalt [𝟙]).state

-- A separate constructive-extraction gate: the package census permits choice.
open Lean Elab Command in
run_cmd do
  for name in [``saltedWitnessPreimage, ``saltedWitnessPreimage_injective, ``saltedWitnessCommitment,
      ``extractSaltedWitnessBinding, ``saltedWitnessCommitment_binds, ``blindEval, ``blindEval_bijection_hides_witness,
      ``maskedTable, ``maskedTable_hypercubeSum_eq, ``maskedTable_eval, ``pairedMask_zeroSum,
      ``spartanCommitmentSetup, ``spartanCommitmentSetup_eq, ``absorbShoutCommitments, ``extractShoutBinding,
      ``batchedReadInnerProd_refines, ``shoutFactorsDigest, ``shoutFactorsDigest_binds, ``shoutBatchTranscript, ``batchedReadInnerProd, ``batchedClaimedValue,
      ``verifyBoundTensorShoutBatch, ``boundTensorShout_sound_or_schwartzZippel, ``verifyBoundTensorShoutBatch_complete,
      ``blindedSpartanTranscript, ``verifyBlindedSpartan, ``proveBlindedSpartan,
      ``blindedSpartan_sound_or_schwartzZippel, ``proveBlindedSpartan_complete, ``extractR1csBinding, ``witnessCommitment_binds, ``r1cs_binding_or_collision, ``tensorShout_sound, ``tensorShout_boolean_unit, ``basisFactor_boolean_unit,
      ``radixAddress_injective, ``radixAddress_digits, ``tensorShout_witness_sublinear, ``binarySpartan_verify_sound_or_schwartzZippel] do
    let axioms ← liftCoreM (collectAxioms name)
    if axioms.contains ``Classical.choice then
      throwError "Constructive audit failed: {name} uses choice"
  -- Check authored top-level contracts, excluding generated constructor/sizeOf lemmas.
  let env ← getEnv
  for (name, info) in env.constants.map₁.toList do
    if name.getPrefix == `Obend.Crypto.BinarySpartanAndShout then
      if let .thmInfo _ := info then
        if ← liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
          throwError "Closed library theorem: {name}"
  logInfo "B1 constructive security and open-theorem audits passed"
#assert_axioms_tree

end Obend.Tests.BinarySpartanAndShout
