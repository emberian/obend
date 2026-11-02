module

public import Obend.Tactic.Tooth
public import Obend.Analysis.Equitable
public import Obend.Analysis.QuantumWalk
public import Obend.Hardware.Photonics
public import Obend.Hardware.QuantumMatter
import all Obend.Analysis.Equitable
import all Obend.Analysis.QuantumWalk
import all Obend.Hardware.Photonics
import all Obend.Hardware.QuantumMatter

/-!
# Metasystem Test Suite — Quantum Walks, Spectral Synthesis, Planar Clements Photonics & Clifford $Cl_4$ Majorana Algebra (`WS-E`)

Comprehensive universal theorem checks, boundary & negative refutation tests, `#tooth`
kernel mutation-killing probes, and `#print axioms` verification (`0 sorryAx`, `0 Classical.choice`)
across:
1. `Obend.Analysis.Equitable`:
   - `checkEquitablePartition_sound`,
   - `sumIntOver_cellMembers_partition`, `partitionedMatVec_eq_matVec`, `matMulEntry_eq_partitionedMatVec`,
   - `equitable_intertwining_step_unpartitioned`,
   - `evalMatrixPoly`, `equitable_intertwining_poly`.
2. `Obend.Analysis.QuantumWalk`:
   - `faddeevLeVerrier`, `charPoly2x2`, `charPoly3x3`, `charPoly4x4`, `synthesizeP4RatioMinPoly`,
     `faddeevLeVerrier_charPoly_and_p4_obstruction_sound`,
   - `synthesizeSylvesterProjector`, `synthesizeSylvesterProjectorPoly`,
     `checkSpectralDecomposition`, `checkSpectralDecomposition_sound`,
   - `evalTaylorPropagator`, `propagatorTaylorStep`, `continuous_time_taylor_propagator_intertwines`.
3. `Obend.Hardware.Photonics` & `Obend.Hardware.QuantumMatter` (Coupler Ratios & Planar Clements Mesh):
   - `couplerKrawtchouk375`, `couplerRealizesQuotientRatio`, `synthesizeKrawtchoukPhotonicCouplers`,
     `compileEquitableToPhotonicArray_ratio_sound`,
   - `evalPlanarClements4Mesh`, `planarClements4Mesh_conserves_optical_power`.
4. `Obend.Hardware.QuantumMatter` (Clifford $Cl_4$ Majorana Algebra & Parity Eigenspace Protection):
   - `cliffordSign`, `cliffordMul`, `clifford_majorana_algebra_laws`,
   - `commutesWithParity`, `isEvenBladeSupported`, `clifford_commutesWithParity_iff_even_blades`,
   - `cliffordToTetronMatrix`, `cliffordParityQuotient`,
     `clifford_commutesWithParity_zero_offblock_and_leakage`,
     `clifford_parity_protected_zero_sector_leakage`.
-/

@[expose] public section
namespace Obend.Tests.Metasystem.QuantumCliffordClementsTest

open Obend.Judge.SOS
open Obend.Analysis
open Obend.Hardware.Photonics
open Obend.Hardware.QuantumMatter
set_option autoImplicit false

/-! ## 1. Pillar 1 Tests: `Obend.Analysis.Equitable` — Checker Soundness, Partition Bijection & Polynomial Intertwining -/

-- 1.1 Universal soundness bridge `checkEquitablePartition_sound` on P3, GQA, and Q3
theorem p3_equitable_sound_instance :
    (∀ u, u < path3Matrix.dim → path3Part u < 2) ∧
    (∀ j, j < 2 → 1 ≤ cellSize (List.range path3Matrix.dim) path3Part j) ∧
    (∀ u j, u < path3Matrix.dim → j < 2 →
      cellRowSum path3Matrix.entry (cellMembers (List.range path3Matrix.dim) path3Part j) u =
        path3Quotient (path3Part u) j) :=
  checkEquitablePartition_sound path3Matrix 2 path3Part path3Quotient rfl

theorem q3_equitable_sound_instance :
    (∀ u, u < hypercubeQ3Matrix.dim → hypercubeQ3Part u < 4) ∧
    (∀ j, j < 4 → 1 ≤ cellSize (List.range hypercubeQ3Matrix.dim) hypercubeQ3Part j) ∧
    (∀ u j, u < hypercubeQ3Matrix.dim → j < 4 →
      cellRowSum hypercubeQ3Matrix.entry (cellMembers (List.range hypercubeQ3Matrix.dim) hypercubeQ3Part j) u =
        hypercubeQ3Quotient (hypercubeQ3Part u) j) :=
  checkEquitablePartition_sound hypercubeQ3Matrix 4 hypercubeQ3Part hypercubeQ3Quotient rfl

-- 1.2 Partition sum bijection `matMulEntry_eq_partitionedMatVec` & `partitionedMatVec_eq_matVec`
theorem p3_matVec_eq_partitioned (v : Nat → Int) (u : Nat) :
    matVec (List.range 3) path3Matrix.entry v u =
      partitionedMatVec path3Matrix.entry (List.range 2) (cellMembers (List.range 3) path3Part) v u := by
  apply matMulEntry_eq_partitionedMatVec
  intro x hx
  exact p3_equitable_sound_instance.1 x (List.mem_range.mp hx)

-- Empty vertex list boundary case for `sumIntOver_cellMembers_partition`
example (f : Nat → Int) (part : Nat → Nat) (numCells : Nat) :
    sumIntOver (fun j => sumIntOver f (cellMembers [] part j)) (List.range numCells) =
      sumIntOver f [] :=
  sumIntOver_cellMembers_partition f part numCells [] (fun _ hx => False.elim (List.not_mem_nil hx))

-- 1.3 Unpartitioned one-step intertwining `equitable_intertwining_step_unpartitioned`
theorem q3_unpartitioned_intertwining (w : Nat → Int) (u : Nat) (hu : u < 8) :
    matVec (List.range 8) hypercubeQ3Matrix.entry (liftVec hypercubeQ3Part w) u =
      liftVec hypercubeQ3Part (quotientMatVec hypercubeQ3Quotient (List.range 4) w) u :=
  equitable_intertwining_step_unpartitioned hypercubeQ3Matrix 4 hypercubeQ3Part hypercubeQ3Quotient w u rfl hu

-- 1.4 Universal Polynomial Intertwining (`equitable_intertwining_poly`) & Boundary Cases
-- Empty polynomial `coeffs = []` yields identically 0 on both full and quotient spaces
example (w : Nat → Int) (u : Nat) :
    evalMatrixPoly (partitionedMatVec path3Matrix.entry [0, 1] (cellMembers [0, 1, 2] path3Part))
      [] (liftVec path3Part w) u = 0 := rfl

-- Concrete degree-3 polynomial `p(x) = 2 - x + 4x^2 - 3x^3` intertwining on Q3 (8 vertices -> 4 cells)
theorem q3_cubic_poly_intertwining_concrete :
    let coeffs : List Int := [2, -1, 4, -3]
    let w : Nat → Int := fun j => if j == 0 then 1 else if j == 2 then -2 else 0
    let HOp := partitionedMatVec hypercubeQ3Matrix.entry (List.range 4)
      (cellMembers (List.range 8) hypercubeQ3Part)
    let QOp := quotientMatVec hypercubeQ3Quotient (List.range 4)
    (List.range 8).all (fun u =>
      decide (evalMatrixPoly HOp coeffs (liftVec hypercubeQ3Part w) u =
              liftVec hypercubeQ3Part (evalMatrixPoly QOp coeffs w) u)) = true := by
  decide +kernel

-- Universal unpartitioned & partitioned polynomial intertwining directly on `path3Matrix` and `hypercubeQ3Matrix`
-- (bridged directly from `checkEquitablePartition = true` for all `u < m.dim` with zero modulo wrappers!)
theorem p3_unpartitioned_poly_intertwining (coeffs : List Int) (w : Nat → Int) (u : Nat) (hu : u < 3) :
    evalMatrixPoly (matVec (List.range 3) path3Matrix.entry) coeffs (liftVec path3Part w) u =
      liftVec path3Part (evalMatrixPoly (quotientMatVec path3Quotient (List.range 2)) coeffs w) u ∧
    evalMatrixPoly (partitionedMatVec path3Matrix.entry (List.range 2) (cellMembers (List.range 3) path3Part))
        coeffs (liftVec path3Part w) u =
      liftVec path3Part (evalMatrixPoly (quotientMatVec path3Quotient (List.range 2)) coeffs w) u :=
  equitable_intertwining_poly_unpartitioned path3Matrix 2 path3Part path3Quotient coeffs w u rfl hu

theorem q3_unpartitioned_poly_intertwining (coeffs : List Int) (w : Nat → Int) (u : Nat) (hu : u < 8) :
    evalMatrixPoly (matVec (List.range 8) hypercubeQ3Matrix.entry) coeffs (liftVec hypercubeQ3Part w) u =
      liftVec hypercubeQ3Part (evalMatrixPoly (quotientMatVec hypercubeQ3Quotient (List.range 4)) coeffs w) u ∧
    evalMatrixPoly (partitionedMatVec hypercubeQ3Matrix.entry (List.range 4) (cellMembers (List.range 8) hypercubeQ3Part))
        coeffs (liftVec hypercubeQ3Part w) u =
      liftVec hypercubeQ3Part (evalMatrixPoly (quotientMatVec hypercubeQ3Quotient (List.range 4)) coeffs w) u :=
  equitable_intertwining_poly_unpartitioned hypercubeQ3Matrix 4 hypercubeQ3Part hypercubeQ3Quotient coeffs w u rfl hu

-- `#tooth` mutation probes for Pillar 1
def brokenCheckEquitablePartition (_ : IntMatrix) (_ : Nat) (_ : Nat → Nat) (_ : Nat → Nat → Int) : Bool :=
  true

#tooth Obend.Analysis.equitable_partition_and_residual_floor_sound
  by mutation Obend.Analysis.checkEquitablePartition := brokenCheckEquitablePartition

def brokenEvalMatrixPoly (_ : (Nat → Int) → (Nat → Int)) (_ : List Int) (_ : Nat → Int) (u : Nat) : Int :=
  (u : Int)

#tooth Obend.Analysis.equitable_intertwining_poly
  by mutation Obend.Analysis.evalMatrixPoly := brokenEvalMatrixPoly


/-! ## 2. Pillar 2 Tests: `Obend.Analysis.QuantumWalk` — Faddeev–LeVerrier, Sylvester Projectors & Taylor Propagator -/

-- 2.1 Faddeev–LeVerrier Characteristic Polynomial Synthesis & P4 Irrational Ratio Obstruction
example : faddeevLeVerrierCoeffs k2Matrix = [1, 0, -1] := rfl
example : faddeevLeVerrierCoeffs path3Matrix = [1, 0, -2, 0] := rfl
example : faddeevLeVerrierCoeffs path4Matrix = [1, 0, -3, 0, 1] := rfl
example : faddeevLeVerrierCoeffs p4EvenQuotient2x2 = [1, -1, -1] := rfl
example : faddeevLeVerrierCoeffs p4OddQuotient2x2 = [1, 1, -1] := rfl
example : faddeevLeVerrierCoeffs hypercubeQ3QuotientMatrix = [1, 0, -10, 0, 9] := rfl
example : synthesizeP4RatioMinPoly = p4RatioMinPolyR2Minus3RPlus1 := rfl
example : synthesizeP4RatioMinPolyCoeffs = [1, -3, 1] := rfl
example : checkP4IrrationalRatioObstruction = true := by decide +kernel

-- Universal 2x2 Faddeev–LeVerrier exact divisibility & Cayley–Hamilton check
example (a b c d : Int) :
    faddeevLeVerrierCoeffs (mat2x2 a b c d) = [1, -(a + d), a * d - b * c] :=
  (faddeevLeVerrier_2x2_exact_and_cayley_hamilton a b c d).2.2.1

-- 1x1 boundary case for Faddeev–LeVerrier (`det(λ I - [7]) = λ - 7`)
def matrix1x1Seven : IntMatrix where
  dim  := 1
  rows := [[7]]

example : faddeevLeVerrierCoeffs matrix1x1Seven = [1, -7] := rfl

-- 2.2 Lagrange–Sylvester Spectral Projector Synthesis & `checkSpectralDecomposition_sound`
example : checkSpectralDecomposition k2Matrix 2 [1, -1] [k2ProjPlus, k2ProjMinus] = true := rfl
example : checkSpectralDecomposition hypercubeQ3QuotientMatrix 48 [3, 1, -1, -3] q3QuotientSylvesterProjectors = true := rfl

theorem q3_sylvester_decomposition_sound :
    sumIntMatrices 4 q3QuotientSylvesterProjectors = IntMatrix.scaledIdentity 4 48 ∧
    (∀ P, P ∈ q3QuotientSylvesterProjectors → P.mul P = P.scale 48) ∧
    (∀ i j, i < q3QuotientSylvesterProjectors.length → j < q3QuotientSylvesterProjectors.length → i ≠ j →
      (q3QuotientSylvesterProjectors[i]?.getD (IntMatrix.zero 4)).mul
        (q3QuotientSylvesterProjectors[j]?.getD (IntMatrix.zero 4)) = IntMatrix.zero 4) ∧
    weightedSumIntMatrices 4 [3, 1, -1, -3] q3QuotientSylvesterProjectors =
      hypercubeQ3QuotientMatrix.scale 48 :=
  checkSpectralDecomposition_sound hypercubeQ3QuotientMatrix 48 [3, 1, -1, -3] q3QuotientSylvesterProjectors rfl

-- Negative test: corrupted projector list fails `checkSpectralDecomposition`
example : checkSpectralDecomposition k2Matrix 2 [1, -1] [k2ProjPlus, k2ProjPlus] = false := rfl

-- 2.3 Continuous-Time Taylor Propagator Intertwining (`continuous_time_taylor_propagator_intertwines` & `_unpartitioned`)
-- Boundary case N = 0: 0-th order Taylor propagator is the identity scaled by `0! = 1`
example (H Q : Nat → Nat → Int) (part : Nat → Nat) (cellIndices : List Nat)
    (cellOf : Nat → List Nat) (tVal : Int) (w : Nat → Int) (u : Nat) :
    propagatorTaylorStep H Q part cellIndices cellOf tVal 0 w u =
      (⟨liftVec part w u * 1 + 0, liftVec part w u * 0 + 0⟩,
       ⟨w (part u) * 1 + 0, w (part u) * 0 + 0⟩) := rfl

-- Universal arbitrary-order `tOrder` and arbitrary-time `t` Taylor propagator intertwining on Q3
theorem q3_universal_taylor_intertwines (t : Int) (tOrder : Nat) (w : Nat → Int) (u : Nat) (hu : u < 8) :
    evalTaylorPropagator (matVec (List.range 8) hypercubeQ3Matrix.entry) t tOrder (liftVec hypercubeQ3Part w) u =
      evalTaylorPropagator (quotientMatVec hypercubeQ3Quotient (List.range 4)) t tOrder w (hypercubeQ3Part u) ∧
    (propagatorTaylorStep hypercubeQ3Matrix.entry hypercubeQ3Quotient hypercubeQ3Part
      (List.range 4) (cellMembers (List.range 8) hypercubeQ3Part) t tOrder w u).1 =
    (propagatorTaylorStep hypercubeQ3Matrix.entry hypercubeQ3Quotient hypercubeQ3Part
      (List.range 4) (cellMembers (List.range 8) hypercubeQ3Part) t tOrder w u).2 :=
  continuous_time_taylor_propagator_intertwines_unpartitioned
    hypercubeQ3Matrix 4 hypercubeQ3Part hypercubeQ3Quotient t tOrder w u rfl hu

-- Concrete 3rd-order Taylor propagator intertwining on Q3 at `t = 2`
theorem q3_taylor_order3_intertwines_concrete :
    let cellIndices := List.range 4
    let cellOf := cellMembers (List.range 8) hypercubeQ3Part
    let w : Nat → Int := fun j => if j == 0 then 5 else if j == 3 then -2 else 1
    (List.range 8).all (fun u =>
      let (fullAmp, quotAmp) :=
        propagatorTaylorStep hypercubeQ3Matrix.entry hypercubeQ3Quotient
          hypercubeQ3Part cellIndices cellOf 2 3 w u
      decide (fullAmp = quotAmp)) = true := by
  decide +kernel

-- `#tooth` mutation probes for Pillar 2
def brokenFaddeevLeVerrierCoeffs (_ : IntMatrix) : List Int :=
  [1, 0, 0]

#tooth Obend.Analysis.faddeevLeVerrier_charPoly_and_p4_obstruction_sound
  by mutation Obend.Analysis.faddeevLeVerrierCoeffs := brokenFaddeevLeVerrierCoeffs

def brokenSynthesizeSylvesterProjector (Q : IntMatrix) (_ : List Int) (_ : Nat) (_ : Int) : IntMatrix :=
  IntMatrix.zero Q.dim

#tooth Obend.Analysis.ctqw_k2_antipodal_pst_exact
  by mutation Obend.Analysis.synthesizeSylvesterProjector := brokenSynthesizeSylvesterProjector


/-! ## 3. Pillar 3 Tests: Coupler-to-Quotient Ratio Synthesis & Planar Clements 4-Mode Mesh -/

-- 3.1 Exact Coupler-to-Quotient Ratio Verification (`couplerRealizesQuotientRatio`, `compileEquitableToPhotonicArray_ratio_sound`)
example : couplerRealizesQuotientRatio hypercubeQ3Quotient
    [couplerKrawtchouk375, coupler3dB, couplerKrawtchouk375] = true := rfl

example (Q : Nat → Nat → Int) (dim : Nat) (scale : Int) :
    couplerRealizesQuotientRatio Q (synthesizeKrawtchoukPhotonicCouplers Q dim scale) = true :=
  synthesizeKrawtchoukPhotonicCouplers_realizes_ratio Q dim scale

-- Negative refusal poles: uniform 1:1:1 couplers and 36:50:36 couplers are strictly refused!
example : couplerRealizesQuotientRatio hypercubeQ3Quotient
    [coupler3dB, coupler3dB, coupler3dB] = false := rfl

example : compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part
    hypercubeQ3Quotient illegalMismatchedUniformCouplerArray = false := rfl

example : compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part
    hypercubeQ3Quotient illegalMismatched36_50_36CouplerArray = false := rfl

example : compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part
    hypercubeQ3Quotient certifiedQ3KrawtchoukPhotonicArray = true := rfl

-- 3.2 Planar Clements 4-Mode Nearest-Neighbor Mesh (`evalPlanarClements4Mesh`, `planarClements4Mesh_conserves_optical_power`)
-- Zero-input boundary case
example (t1 k1 t2 k2 : Int) :
    evalPlanarClements4Mesh t1 k1 t2 k2 ⟨0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ =
      (⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩) := by
  simp [evalPlanarClements4Mesh, evalPhotonicArray4LayerEven, evalPhotonicArray4LayerOdd,
    evalDirectionalCoupler2x2]

-- Planar locality test: changing input `e3` on waveguide 3 has ZERO effect on output mode 0
-- in `evalPlanarClements4Mesh`, unlike non-planar `evalPhotonicArray4Mesh2Step`!
theorem planarClements_mode0_independent_of_mode3
    (t1 k1 t2 k2 : Int) (e0 e1 e2 e3 e3' : ComplexField) :
    (evalPlanarClements4Mesh t1 k1 t2 k2 e0 e1 e2 e3).1 =
      (evalPlanarClements4Mesh t1 k1 t2 k2 e0 e1 e2 e3').1 :=
  rfl

-- Contrast with non-planar `evalPhotonicArray4Mesh2Step`, where mode 0 DOES depend on mode 3
example :
    (evalPhotonicArray4Mesh2Step 1 1 ⟨1, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩).1 ≠
      (evalPhotonicArray4Mesh2Step 1 1 ⟨1, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩).1 := by
  decide

-- `#tooth` mutation probes for Pillar 3
def brokenCouplerRealizesQuotientRatio (_ : Nat → Nat → Int) (_ : List DirectionalCouplerSpec) : Bool :=
  true

#tooth Obend.Hardware.QuantumMatter.compileEquitableToPhotonicArray_ratio_sound
  by mutation Obend.Hardware.QuantumMatter.couplerRealizesQuotientRatio := brokenCouplerRealizesQuotientRatio

def brokenEvalPlanarClements4Mesh (t1 k1 _ _ : Int) (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  (e0, e1, e2, { re := e3.re + t1 + k1 + 1, im := e3.im })

#tooth Obend.Hardware.QuantumMatter.planarClements4Mesh_conserves_optical_power
  by mutation Obend.Hardware.QuantumMatter.evalPlanarClements4Mesh := brokenEvalPlanarClements4Mesh


/-! ## 4. Pillar 4 Tests: Clifford Algebra $Cl_4$ & Majorana Parity Eigenspace Protection -/

-- 4.1 Majorana generator relations: γ_a^2 = 1, {γ_a, γ_b} = 0 (a ≠ b), P = -γ_0 γ_1 γ_2 γ_3, P^2 = 1
theorem clifford_parity_eq_neg_gamma_product :
    cliffordParity =
      cliffordScale (-1)
        (cliffordMul (cliffordGamma ⟨0, by decide⟩)
          (cliffordMul (cliffordGamma ⟨1, by decide⟩)
            (cliffordMul (cliffordGamma ⟨2, by decide⟩) (cliffordGamma ⟨3, by decide⟩)))) := by
  decide +kernel

-- Exhaustive verification across all 16 basis blades `m ∈ {0..15}`:
-- `commutesWithParity (cliffordBasisBlade m) == (bladePopcount m % 2 == 0)`
theorem clifford_all_16_basis_blades_parity_selection :
    (List.range 16).all (fun m =>
      commutesWithParity (cliffordBasisBlade m) == (bladePopcount m % 2 == 0)) = true := by
  decide +kernel

-- All 4 single Majorana generators γ_0, γ_1, γ_2, γ_3 anticommute with P (`P γ_a + γ_a P = 0`)
theorem clifford_single_majoranas_anticommute_with_parity :
    (∀ a : Fin 4,
      cliffordAdd (cliffordMul cliffordParity (cliffordGamma a))
                  (cliffordMul (cliffordGamma a) cliffordParity) = cliffordZero) ∧
    (∀ a : Fin 4, commutesWithParity (cliffordGamma a) = false) := by
  decide +kernel

-- All 6 bilinear Majorana pairings γ_a γ_b (a < b) commute with P (`[γ_a γ_b, P] = 0`)
theorem clifford_bilinear_majoranas_commute_with_parity :
    ∀ a b : Fin 4,
      commutesWithParity (cliffordMul (cliffordGamma a) (cliffordGamma b)) = true := by
  decide +kernel

-- 4.2 Universal Clifford Parity Selection, Bidirectional Off-Block Vanishing & Zero Sector Leakage
example (H : CliffordElem) :
    commutesWithParity H = true ↔ isEvenBladeSupported H = true :=
  clifford_commutesWithParity_iff_even_blades H

-- Even-blade `b6 = 1` commutes with parity and passes `checkEquitablePartition = true`
example :
    let H := { cliffordZero with b6 := 1 }
    commutesWithParity H = true ∧
    checkEquitablePartition (cliffordToTetronMatrix H) 2 majoranaParityPart (cliffordParityQuotient H) = true :=
  ⟨rfl, (clifford_commutesWithParity_iff_offblock_and_equitable { cliffordZero with b6 := 1 }).2 rfl⟩

-- Odd-blade combination `b4 = 1, b11 = -1, b13 = -1` fails `commutesWithParity` and has non-zero off-sector entries
example :
    let dH := { cliffordZero with b4 := 1, b11 := -1, b13 := -1 }
    commutesWithParity dH = false ∧
    cliffordToTetronMatrix dH ≠ IntMatrix.zero 4 := by
  decide +kernel

example (cH cDH : CliffordElem) (eps : Int) (w : Nat → Int)
    (hH : commutesWithParity cH = true) (hDH : commutesWithParity cDH = true) (hw : w 1 = 0) :
    quotientMatVec (perturbedQuotient (cliffordParityQuotient cH) (cliffordParityQuotient cDH) eps) [0, 1] w 1 = 0 ∧
    matVec [0, 1, 2, 3]
      (perturbedHamiltonian (cliffordToTetronMatrix cH).entry (cliffordToTetronMatrix cDH).entry eps)
      (liftQuotientVec majoranaParityPart w) 2 = 0 ∧
    matVec [0, 1, 2, 3]
      (perturbedHamiltonian (cliffordToTetronMatrix cH).entry (cliffordToTetronMatrix cDH).entry eps)
      (liftQuotientVec majoranaParityPart w) 3 = 0 :=
  clifford_parity_protected_zero_sector_leakage cH cDH eps w hH hDH hw

-- `#tooth` mutation probes for Pillar 4
def brokenCliffordSign (_ _ : Nat) : Int :=
  1

#tooth Obend.Hardware.QuantumMatter.clifford_majorana_algebra_laws
  by mutation Obend.Hardware.QuantumMatter.cliffordSign := brokenCliffordSign

def brokenIsEvenBladeSupported (_ : CliffordElem) : Bool :=
  true

#tooth Obend.Hardware.QuantumMatter.clifford_commutesWithParity_iff_even_blades
  by mutation Obend.Hardware.QuantumMatter.isEvenBladeSupported := brokenIsEvenBladeSupported


/-! ## 5. Axiom Audit (`0 sorryAx`, `0 Classical.choice`) -/

#print axioms Obend.Analysis.checkEquitablePartition_sound
#print axioms Obend.Analysis.sumIntOver_cellMembers_partition
#print axioms Obend.Analysis.partitionedMatVec_eq_matVec
#print axioms Obend.Analysis.matMulEntry_eq_partitionedMatVec
#print axioms Obend.Analysis.equitable_intertwining_step_unpartitioned
#print axioms Obend.Analysis.equitable_intertwining_power_unpartitioned
#print axioms Obend.Analysis.equitable_intertwining_poly
#print axioms Obend.Analysis.equitable_intertwining_poly_unpartitioned
#print axioms Obend.Analysis.faddeevLeVerrier_2x2_exact_and_cayley_hamilton
#print axioms Obend.Analysis.faddeevLeVerrier_charPoly_and_p4_obstruction_sound
#print axioms Obend.Analysis.checkSpectralDecomposition_sound
#print axioms Obend.Analysis.continuous_time_taylor_propagator_intertwines
#print axioms Obend.Analysis.continuous_time_taylor_propagator_intertwines_unpartitioned
#print axioms Obend.Hardware.QuantumMatter.planarClements4Mesh_conserves_optical_power
#print axioms Obend.Hardware.QuantumMatter.synthesizeKrawtchoukPhotonicCouplers_realizes_ratio
#print axioms Obend.Hardware.QuantumMatter.compileEquitableToPhotonicArray_ratio_sound
#print axioms Obend.Hardware.QuantumMatter.clifford_majorana_algebra_laws
#print axioms Obend.Hardware.QuantumMatter.clifford_commutesWithParity_iff_even_blades
#print axioms Obend.Hardware.QuantumMatter.clifford_commutesWithParity_zero_offblock_and_leakage
#print axioms Obend.Hardware.QuantumMatter.clifford_commutesWithParity_iff_offblock_and_equitable
#print axioms Obend.Hardware.QuantumMatter.cliffordToSpinorMatrix_algebra_hom
#print axioms Obend.Hardware.QuantumMatter.clifford_parity_protected_zero_sector_leakage
#print axioms Obend.Hardware.QuantumMatter.symmetry_preserving_noise_zero_leakage

end Obend.Tests.Metasystem.QuantumCliffordClementsTest
end
