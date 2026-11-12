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
private theorem canonical_tensor : tensorVector [true,false] = #[𝟘,𝟙,𝟘,𝟘] := by rfl
example : checkBinaryShout table [true,false] #[𝟘,𝟙,𝟘,𝟘] 𝟙 = true := by
  rw [← canonical_tensor, ← binaryShoutSparse_exec_eq_dense table ⟨[true,false],𝟙⟩]
  decide +kernel
private theorem zero_vector_rejected : checkTensor [true,false] #[𝟘,𝟘,𝟘,𝟘] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh := ((checkTensor_iff _ _).mp h).2 1 (by decide)
  exact towerOne_ne_zero 7 hh.symm
private theorem double_vector_rejected : checkTensor [true,false] #[𝟙,𝟙,𝟘,𝟘] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh := ((checkTensor_iff _ _).mp h).2 0 (by decide)
  exact towerOne_ne_zero 7 hh
private theorem triple_vector_rejected : checkTensor [true,false] #[𝟙,𝟙,𝟙,𝟘] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh := ((checkTensor_iff _ _).mp h).2 0 (by decide)
  exact towerOne_ne_zero 7 hh
example : checkBinaryShout table [true,false] #[𝟘,𝟘,𝟘,𝟘] 𝟙 = false := by
  simp only [checkBinaryShout, zero_vector_rejected, Bool.and_false, Bool.false_and]
example : checkBinaryShout table [true,false] #[𝟙,𝟙,𝟘,𝟘] 𝟙 = false := by
  simp only [checkBinaryShout, double_vector_rejected, Bool.and_false, Bool.false_and]
example : checkBinaryShout table [true,false] #[𝟙,𝟙,𝟙,𝟘] 𝟙 = false := by
  simp only [checkBinaryShout, triple_vector_rejected, Bool.and_false, Bool.false_and]
example : checkBinaryShout table [true,false] #[𝟘,𝟙,𝟘,𝟘] 𝟘 = false := by
  rw [← canonical_tensor, ← binaryShoutSparse_exec_eq_dense table ⟨[true,false],𝟘⟩]
  decide +kernel
example : towerAdd 7 (towerAdd 7 𝟙 𝟙) 𝟙 = 𝟙 := (tripleHot_sum_is_one 𝟘).1
example : verifyShoutRead table ⟨[true,false],𝟙⟩ = true := by decide +kernel
example : verifyShoutBatch table #[⟨[true,false],𝟙⟩,⟨[false,false],𝟘⟩] = true := by decide +kernel
example : verifyShoutRead table ⟨[true,false],𝟘⟩ = false := by decide +kernel
example (address : List Bool) (j : Nat) (hj : j < 2^address.length) :
    tensorWeight address (addressBits address.length j) = if j = bitAddress address then 𝟙 else 𝟘 :=
  tensorWeight_at_index address j hj

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

example : verifyBinarySpartan context circuit (proveBinarySpartan context circuit witness) = true ∧
    verifyShoutRead table ⟨[true,false],𝟙⟩ = true ∧
    checkPcsSoundnessRegime binaryUdrPcsParams = true ∧
    binarySpartanShoutJudge.check 0 audit () = .ok :=
  ⟨proveBinarySpartan_complete context _ _ circuit_shape circuit_sat,
    by decide +kernel, binaryUdrPcsParams_valid (), audit_ok⟩

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
#tooth checkTensor_iff by mutation checkTensor := fun a w => decide (w.size = 2^a.length)
#tooth checkTensor_iff by mutation checkTensor := fun a w =>
  decide (w.size = 2^a.length) && decide (w.toList.foldl (towerAdd 7) 𝟘 = 𝟙)
#tooth binaryShout_onehot_lookup_sound by mutation checkBinaryShout := fun _ a w _ => checkTensor a w
#tooth verifyShoutRead_sound by mutation verifyShoutRead := fun _ _ => true
#tooth encodeR1csInstance_injective by mutation encodeR1csInstance := fun _ => ByteArray.empty
#tooth discrepancyTable_exec_eq_spec by mutation discrepancyTableExec := fun _ _ => []
#tooth auditCheck_iff by mutation checkAllRows := fun _ _ => true

#print axioms binarySpartan_verify_sound_or_schwartzZippel
#print axioms outer_zero_implies_root
#print axioms polynomial_roots_count
#print axioms binaryShout_onehot_lookup_sound
#print axioms encodeR1csInstance_injective
#print axioms r1cs_binding_or_collision
#print axioms proveBinarySpartan_complete
#print axioms hardware_mul_refines
#print axioms encodeField_injective
#print axioms encodeItems_injective
#print axioms checkTensor_iff
#print axioms extractR1csBinding
run_cmd do
  for name in [``extractR1csBinding, ``binarySpartan_verify_sound_or_schwartzZippel,
      ``outer_zero_implies_root, ``polynomial_roots_count, ``encodeR1csInstance_injective,
      ``binaryShout_onehot_lookup_sound, ``proveBinarySpartan_complete, ``sparseInner_verify_sound,
      ``proveSparseInner_complete, ``binaryShoutSparse_exec_eq_dense, ``hardware_mul_refines,
      ``binaryChallengeAt_injective, ``binaryChallengeAt_surjective, ``binarySpartan_root_sets_bound,
      ``r1csZerocheckTerm_eq] do
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.contains ``Classical.choice then
      throwError "Constructive audit failed: {name} depends on Classical.choice"
  Lean.logInfo "Constructive audit: all security theorems and collision extraction are choice-free"
#assert_axioms_tree

end Obend.Tests.BinarySpartanAndShout
