import Obend.Analysis.Equitable
import Obend.Analysis.QuantumWalk
import Obend.Analysis.SosLyapunov
import Obend.Hardware.Photonics
import Obend.Hardware.QuantumMatter
import Obend.Judge

/-!
# `tests/QuantumMatterTest.lean` — End-to-End Verification Suite for WS-T

Verifies:
1. Block-equitable $2\times 2$ Pauli spinor partitions & polynomial intertwining (`block_equitable_intertwining_poly`),
2. Full 16D injectivity of `cliffordToTetronMatrix` & bidirectional `commutesWithParity ↔ checkBlockEquitablePartition`,
3. Faddeev–LeVerrier thermo-optic crosstalk compensation (`faddeevAdjugate_cancels_crosstalk_4x4`, `compensateThermalCrosstalk_exact_4x4`),
4. 2-boson permanent Hong–Ou–Mandel bunching & Bose symmetry (`hong_ou_mandel_bunching_exact`, `twoBosonPermanent_bose_symmetry`, `twoBoson_equitable_intertwining_poly`),
5. Ivanov Majorana braiding unitarity, parity conservation, mode exchange, and Artin braid group relations (`majoranaBraid_artin_relation`),
6. Open-system Lindblad parity cooling & zero even-sector leakage (`lindbladDissipator2_trace_zero`, `parityCoolingJumpOp_dark_on_even_and_corrects_odd`),
7. Polynomial SOS Lyapunov, Control Barrier Functions (CBF), and Index-1 DAE manifold certificates (`"sos-lyapunov-cbf@1"`).
-/

namespace Obend.Tests.QuantumMatterTest

open Obend.Analysis
open Obend.Hardware.Photonics
open Obend.Hardware.QuantumMatter
open Obend.Judge

/-! ## 1. Block-Equitable $2\times 2$ Spinor Partitions & 16D Clifford Injectivity -/

/-- Logical Pauli $Z_L = e_5 + e_{12}$ and $X_L = e_3 + e_6$ have non-scalar $2\times 2$ blocks
($e_{00} \neq e_{11}$) yet satisfy `checkBlockEquitablePartition = true`! -/
def logicalPauliZL : CliffordElem :=
  { cliffordZero with b6 := 1, b9 := -1 }

example :
    commutesWithParity logicalPauliZL = true ∧
    checkBlockEquitablePartition
      (cliffordToTetronMatrix logicalPauliZL) 2 2 majoranaParityPart (cliffordParityQuotient logicalPauliZL) = true ∧
    (cliffordToTetronMatrix logicalPauliZL).entry 0 0 ≠ (cliffordToTetronMatrix logicalPauliZL).entry 1 1 := by
  decide +kernel

/-- Full bi-implication and 16D injectivity of `cliffordToTetronMatrix`. -/
theorem test_clifford_tetron_biimplication_and_injectivity (H : CliffordElem) :
    (commutesWithParity H = true ↔
      checkBlockEquitablePartition (cliffordToTetronMatrix H) 2 2 majoranaParityPart (cliffordParityQuotient H) = true) ∧
    (cliffordToTetronMatrix H = IntMatrix.zero 4 ↔ H = cliffordZero) := by
  have h := clifford_commutesWithParity_iff_offblock_and_equitable H
  exact ⟨h.2.1, h.2.2⟩

/-- Polynomial intertwining on $2\times 2$ block-equitable spinor partitions. -/
theorem test_block_equitable_intertwining_poly
    (A : IntMatrix) (Q : Nat → Nat → IntMatrix) (part : Nat → Nat)
    (d : Nat) (cellIndices : List Nat) (blockCellOfJ : Nat → List Nat)
    (coeffs : List Int) (W : Nat → Nat → Int) (p alpha : Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ q, q ∈ blockCellOfJ j → blockCellOf part d q = j)
    (hEqAll : ∀ p alpha, ∀ j, j ∈ cellIndices → ∀ beta, beta ∈ List.range d →
      blockCellRowSumEntry A d (blockCellOfJ j) p alpha beta = (Q (blockCellOf part d p) j).entry alpha beta) :
    evalBlockMatrixPoly (blockPartitionedMatVec A d cellIndices blockCellOfJ) coeffs
        (liftBlockQuotientVec part d W) p alpha =
      liftBlockQuotientVec part d
        (evalBlockMatrixPoly (blockQuotientMatVec Q d cellIndices) coeffs W) p alpha :=
  block_equitable_intertwining_poly A Q part d cellIndices blockCellOfJ coeffs W p alpha hCells hEqAll

/-! ## 2. Thermo-Optic Crosstalk Cancellation & 2-Boson Hong–Ou–Mandel Photonics -/

theorem test_thermo_optic_crosstalk_and_hom_bunching (phi0 phi1 phi2 phi3 : Int) :
    (faddeevAdjugateAndDet goldenThermalCrosstalk4x4).1.mul goldenThermalCrosstalk4x4 =
      IntMatrix.scaledIdentity 4 8769 ∧
    goldenThermalCrosstalk4x4.mulVec
      (compensateThermalCrosstalk goldenThermalCrosstalk4x4 [phi0, phi1, phi2, phi3]).1 =
      [8769 * phi0, 8769 * phi1, 8769 * phi2, 8769 * phi3] ∧
    twoBosonPermanent (beamSplitter5050 ⟨0, by decide⟩ ⟨1, by decide⟩)
      ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ = GaussianInt.zero ∧
    checkEquitablePartition twoBosonHamiltonian 3 twoBosonPart twoBosonQuotient = true :=
  ⟨faddeevAdjugate_cancels_crosstalk_4x4.2.2,
   compensateThermalCrosstalk_exact_4x4 phi0 phi1 phi2 phi3,
   hong_ou_mandel_bunching_exact ⟨0, by decide⟩ ⟨1, by decide⟩,
   by decide +kernel⟩

theorem test_two_boson_bose_symmetry (U : GaussianMatrix) (a b c d : Fin 4) :
    twoBosonPermanent U b a c d = twoBosonPermanent U a b c d ∧
    twoBosonPermanent U a b d c = twoBosonPermanent U a b c d :=
  twoBosonPermanent_bose_symmetry U a b c d

/-! ## 3. Ivanov Majorana Braiding, Artin Braid Group & Lindblad Parity Cooling -/

example :
    let m0 : Fin 4 := ⟨0, by decide⟩
    let m1 : Fin 4 := ⟨1, by decide⟩
    let m2 : Fin 4 := ⟨2, by decide⟩
    cliffordMul (majoranaBraidElem m0 m1) (majoranaBraidAdjElem m0 m1) = cliffordScale 2 cliffordOne ∧
    cliffordMul (cliffordMul (majoranaBraidElem m0 m1) (cliffordGamma m0)) (majoranaBraidAdjElem m0 m1) =
      cliffordScale (-2) (cliffordGamma m1) ∧
    cliffordMul (cliffordMul (majoranaBraidElem m0 m1) (majoranaBraidElem m1 m2)) (majoranaBraidElem m0 m1) =
      cliffordMul (cliffordMul (majoranaBraidElem m1 m2) (majoranaBraidElem m0 m1)) (majoranaBraidElem m1 m2) ∧
    ((spinorBraidGate m0 m1).mul (spinorBraidGate m1 m2)).mul (spinorBraidGate m0 m1) =
      ((spinorBraidGate m1 m2).mul (spinorBraidGate m0 m1)).mul (spinorBraidGate m1 m2) := by
  decide +kernel

theorem test_lindblad_parity_cooling (a : Fin 4) (rho : GaussianMatrix) :
    (lindbladDissipator2 (parityCoolingJumpOp a) rho).trace = GaussianInt.zero ∧
    (parityCoolingJumpOp a).mul spinorEvenParityProjector = GaussianMatrix.zero 4 ∧
    ((parityCoolingJumpOp a).mul spinorOddParityProjector).mul (parityCoolingJumpOp a).conjTranspose =
      spinorEvenParityProjector :=
  ⟨lindbladDissipator2_trace_zero a rho,
   (parityCoolingJumpOp_dark_on_even_and_corrects_odd a).1,
   (parityCoolingJumpOp_dark_on_even_and_corrects_odd a).2.2.1⟩

/-! ## 4. SOS Lyapunov, CBF & Index-1 DAE Certificate Format (`"sos-lyapunov-cbf@1"`) -/

theorem test_sos_lyapunov_cbf_dae_format_and_registry :
    (Format.find? "sos-lyapunov-cbf" "1").isSome = true ∧
    checkSosLyapunov goldenLyapunovSpec2D goldenLyapunovWitness2D = true ∧
    checkSosCbf goldenCbfSpec2D goldenCbfWitness2D = true ∧
    checkDaeManifold goldenCircleDaeSpec goldenCircleDaeWitness = true ∧
    checkSosLyapunovProblem 1
      { lyapunov := goldenLyapunovSpec2D, cbf := goldenCbfSpec2D, dae := goldenCircleDaeSpec }
      { lyapunovWitness := goldenLyapunovWitness2D, cbfWitness := goldenCbfWitness2D, daeWitness := goldenCircleDaeWitness } = Verdict.ok :=
  ⟨by decide,
   sos_lyapunov_cbf_dae_showcase_sound.1,
   sos_lyapunov_cbf_dae_showcase_sound.2.1,
   sos_lyapunov_cbf_dae_showcase_sound.2.2.1,
   sos_lyapunov_cbf_dae_showcase_sound.2.2.2⟩

end Obend.Tests.QuantumMatterTest
