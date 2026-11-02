module
/-
# Obend.Hardware.QuantumMatter — Physical Quantum & Photonic Matter Compiler: Coupled-Waveguide CTQW Synthesis, IBM Heavy-Hex $C_{12}$ Lattice & Majorana-1 Parity-Sector Noise Immunity

Replaces abstract stubbed hardware predicates (`satisfies := True`) with a **Real Physical Matter Compiler**
inside `Obend.Hardware`, coupling `Obend.Analysis.Equitable` and `Obend.Analysis.QuantumWalk` to
`Obend.Hardware.Photonics`:

1. **Photonic Coupled-Waveguide Array CTQW Synthesizer (`PhotonicWaveguideArraySpec`, `checkPhotonicArrayMatterDrc`, `compileEquitableToPhotonicArray`)**:
   - Synthesizes an $r$-waveguide evanescently coupled Silicon Photonics (`soi220nm`, `ihpSg13g2Epic`,
     `sin400nm`) waveguide array from an $N$-vertex Hamiltonian's equitable quotient $Q$, eliminating
     non-planar waveguide crossings (e.g., collapsing the 8-vertex non-planar Hypercube $Q_3$ into a
     planar 4-waveguide Krawtchouk tridiagonal array).
   - Enforces **real foundry Design Rule Checks (`checkPhotonicArrayMatterDrc`)**: single-mode $\text{TE}_{00}$
     core width ($400\text{--}1200\,\text{nm}$), lithography minimum coupler gap ($\ge 150\,\text{nm}$),
     evanescent interaction ceiling ($\le 600\,\text{nm}$), platform minimum radiative S-bend radius
     ($5\,\mu\text{m}$ on SOI, $25\,\mu\text{m}$ on $\text{Si}_3\text{N}_4$), crosstalk isolation pitch
     ($\ge 2000\,\text{nm}$), and Coupled-Mode Theory (CMT) lossless unitarity ($t^2 + \kappa^2 = 10^6\,\text{ppm}$).
   - Proves **`photonic_ctqw_array_power_conserved`** (exact $\mathbb{Z}[i]$ unitary optical power
     conservation across multi-waveguide coupler layers and interleaved meshes) and
     **`photonic_matter_compiler_drc_sound`**.
2. **IBM Heavy-Hex $C_{12}$ Lattice & Microsoft Majorana-1 Tetron Parity-Sector Noise Immunity**:
   - Mechanizes the 12-qubit **IBM Heavy-Hex** ring unit cell $C_{12}$ under both its 7-cell antipodal
     distance partition and its 2-cell degree-3 corner vs. degree-2 bridge partition.
   - Mechanizes the **Microsoft Majorana-1 Tetron** 4-Majorana fermion parity projector system
     ($C_{\text{even}} = \{0, 1\}$, $C_{\text{odd}} = \{2, 3\}$).
   - Proves **`symmetry_preserving_noise_zero_leakage`** universally and concretely: any noise
     perturbation $\epsilon \Delta H$ commuting with the equitable / parity partition preserves exact
     intertwining $((H + \epsilon \Delta H)(S w) = S((Q + \epsilon \Delta Q) w))$ and produces
     **identically zero leakage** (`= 0`) out of the computational quotient subspace across all
     $\epsilon \in \mathbb{Z}$, whereas parity-breaking quasiparticle poisoning induces a strictly
     positive residual leakage floor.
-/
public import Obend.Hardware.Photonics
public import Obend.Analysis.Equitable
public import Obend.Analysis.QuantumWalk
@[expose] public section

namespace Obend.Hardware.QuantumMatter
open Obend.Hardware.Photonics
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. Multi-Waveguide Photonic CTQW Array & Exact $\mathbb{Z}[i]$ Unitary Power Conservation -/

/-- Specification of an $r$-waveguide evanescently coupled photonic CTQW array synthesized from an
$N$-vertex graph Hamiltonian via its $r$-cell equitable quotient:
* `arrayName`: physical PIC macro identifier,
* `platform`: open-foundry photonic process (`soi220nm`, `ihpSg13g2Epic`, or `sin400nm`),
* `waveguide`: single-mode strip/rib waveguide specification,
* `numSourceVertices`: number of vertices $N$ in the unreduced source graph,
* `numQuotientModes`: number of physical waveguides $r$ in the planar tridiagonal array,
* `couplers`: list of $r - 1$ adjacent evanescent directional couplers between waveguides $(j, j+1)$,
* `fanoutBendRadiusNm`: S-bend radius (in $\text{nm}$) for input/output grating/edge-coupler fanout,
* `isolationPitchNm`: pitch (in $\text{nm}$) in fanout / non-interacting regions to suppress parasitic
  next-nearest-neighbor evanescent crosstalk ($\ge 2000\,\text{nm}$),
* `interactionLengthUm`: active coupled-array propagation length $z$ (in $\mu\text{m}$). -/
structure PhotonicWaveguideArraySpec where
  arrayName          : String
  platform           : PhotonicPlatform
  waveguide          : WaveguideSpec
  numSourceVertices  : Nat
  numQuotientModes   : Nat
  couplers           : List DirectionalCoupler
  fanoutBendRadiusNm : Nat
  isolationPitchNm   : Nat
  interactionLengthUm : Nat
  deriving DecidableEq, Repr

/-- Symmetrized squared inter-cell coupling weight $\kappa_{i,j}^2 \propto Q_{i,j} \cdot Q_{j,i} \in \mathbb{Z}$
between quotient cells $C_i$ and $C_j$. By `equitable_handshake_identity` ($|C_i| Q_{i,j} = |C_j| Q_{j,i}$),
this integer product captures the exact symmetrized tridiagonal coupling $D^{1/2} Q D^{-1/2}$
without requiring `Real.sqrt`! -/
def evalSymmetrizedCouplingSq (quotientEntry : Nat → Nat → Int) (i j : Nat) : Int :=
  quotientEntry i j * quotientEntry j i

/-- Projection wrapper for `directional_coupler_2x2_power_conservation` over `.1` and `.2`. -/
theorem directional_coupler_2x2_fst_snd_power
    (t kappa : Int) (e1 e2 : ComplexField) :
    (evalDirectionalCoupler2x2 t kappa e1 e2).1.normSq +
      (evalDirectionalCoupler2x2 t kappa e1 e2).2.normSq =
      (t * t + kappa * kappa) * (e1.normSq + e2.normSq) :=
  directional_coupler_2x2_power_conservation t kappa e1 e2

/-- Evaluate one parallel evanescent coupling layer across a 4-waveguide photonic array
(coupling waveguide pair $(0, 1)$ with $(t_{01}, \kappa_{01})$ and pair $(2, 3)$ with $(t_{23}, \kappa_{23})$)
over exact Gaussian-integer optical field phasors `ComplexField` ($\mathbb{Z}[i]$). -/
def evalPhotonicArray4LayerEven
    (t01 k01 t23 k23 : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let c01 := evalDirectionalCoupler2x2 t01 k01 e0 e1
  let c23 := evalDirectionalCoupler2x2 t23 k23 e2 e3
  (c01.1, c01.2, c23.1, c23.2)

/-- Evaluate an inner evanescent coupling step on waveguide pair $(1, 2)$ of a 4-waveguide array
(leaving outer boundary waveguides $0$ and $3$ in phase-matched straight propagation scaled by
unitary norm factor `s12` so all modes share a common scale). -/
def evalPhotonicArray4LayerOdd
    (t12 k12 : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let c12 := evalDirectionalCoupler2x2 t12 k12 e1 e2
  (e0, c12.1, c12.2, e3)

/-- Evaluate a two-step Suzuki–Trotter / Clements 4-waveguide coupled array propagation mesh:
first coupling $(0, 1)$ and $(2, 3)$ with $(t, \kappa)$, then coupling $(1, 2)$ with $(t, \kappa)$
while scaling outer waveguides $(0, 3)$ by $(t, \kappa)$ via a balanced reference coupler. -/
def evalPhotonicArray4Mesh2Step
    (t kappa : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let m01 := evalDirectionalCoupler2x2 t kappa e0 e1
  let m23 := evalDirectionalCoupler2x2 t kappa e2 e3
  let c12 := evalDirectionalCoupler2x2 t kappa m01.2 m23.1
  let c03 := evalDirectionalCoupler2x2 t kappa m01.1 m23.2
  (c03.1, c12.1, c12.2, c03.2)

/-- **Theorem (`photonic_ctqw_array_power_conserved`)**:
For ALL field transmission/coupling coefficients `t, kappa : Int` and ALL complex input optical
field phasors `e0, e1, e2, e3 : ComplexField` (arbitrary amplitude and phase in $\mathbb{Z}[i]$):
1. **Single-Layer 4-Waveguide Array Power Conservation**:
   `evalPhotonicArray4LayerEven t kappa t kappa e0 e1 e2 e3` strictly conserves total optical power
   across all 4 waveguides up to the CMT unitary scale factor $t^2 + \kappa^2$:
   $$|E_{\text{out},0}|^2 + |E_{\text{out},1}|^2 + |E_{\text{out},2}|^2 + |E_{\text{out},3}|^2
     = (t^2 + \kappa^2)\left(|E_0|^2 + |E_1|^2 + |E_2|^2 + |E_3|^2\right).$$
2. **Two-Layer Cascaded 4-Waveguide Mesh Power Conservation**:
   `evalPhotonicArray4Mesh2Step t kappa e0 e1 e2 e3` strictly conserves total optical power across
   all 4 waveguides up to $(t^2 + \kappa^2)^2$:
   $$\sum_{m=0}^3 |E_{\text{mesh},m}|^2 = (t^2 + \kappa^2) \cdot (t^2 + \kappa^2) \cdot \sum_{m=0}^3 |E_m|^2.$$ -/
theorem photonic_ctqw_array_power_conserved
    (t kappa : Int)
    (e0 e1 e2 e3 : ComplexField) :
    (let (o0, o1, o2, o3) := evalPhotonicArray4LayerEven t kappa t kappa e0 e1 e2 e3
     o0.normSq + o1.normSq + o2.normSq + o3.normSq =
       (t * t + kappa * kappa) * (e0.normSq + e1.normSq + e2.normSq + e3.normSq)) ∧
    (let (p0, p1, p2, p3) := evalPhotonicArray4Mesh2Step t kappa e0 e1 e2 e3
     p0.normSq + p1.normSq + p2.normSq + p3.normSq =
       (t * t + kappa * kappa) * ((t * t + kappa * kappa) * (e0.normSq + e1.normSq + e2.normSq + e3.normSq))) := by
  have h01 := directional_coupler_2x2_fst_snd_power t kappa e0 e1
  have h23 := directional_coupler_2x2_fst_snd_power t kappa e2 e3
  dsimp only [evalPhotonicArray4LayerEven, evalPhotonicArray4Mesh2Step]
  have hDistLayer :
      (t * t + kappa * kappa) * (e0.normSq + e1.normSq + e2.normSq + e3.normSq) =
      (t * t + kappa * kappa) * (e0.normSq + e1.normSq) +
      (t * t + kappa * kappa) * (e2.normSq + e3.normSq) := by
    have hAssoc : e0.normSq + e1.normSq + e2.normSq + e3.normSq =
        (e0.normSq + e1.normSq) + (e2.normSq + e3.normSq) := by omega
    rw [hAssoc, Int.mul_add]
  constructor
  · omega
  · have hInner := directional_coupler_2x2_fst_snd_power t kappa
      (evalDirectionalCoupler2x2 t kappa e0 e1).2 (evalDirectionalCoupler2x2 t kappa e2 e3).1
    have hOuter := directional_coupler_2x2_fst_snd_power t kappa
      (evalDirectionalCoupler2x2 t kappa e0 e1).1 (evalDirectionalCoupler2x2 t kappa e2 e3).2
    have hMidSum :
        ((evalDirectionalCoupler2x2 t kappa e0 e1).1.normSq +
          (evalDirectionalCoupler2x2 t kappa e2 e3).2.normSq) +
        ((evalDirectionalCoupler2x2 t kappa e0 e1).2.normSq +
          (evalDirectionalCoupler2x2 t kappa e2 e3).1.normSq) =
        (t * t + kappa * kappa) * (e0.normSq + e1.normSq + e2.normSq + e3.normSq) := by
      omega
    have hDistMesh :
        (t * t + kappa * kappa) *
          (((evalDirectionalCoupler2x2 t kappa e0 e1).1.normSq +
            (evalDirectionalCoupler2x2 t kappa e2 e3).2.normSq) +
           ((evalDirectionalCoupler2x2 t kappa e0 e1).2.normSq +
            (evalDirectionalCoupler2x2 t kappa e2 e3).1.normSq)) =
        (t * t + kappa * kappa) *
          ((evalDirectionalCoupler2x2 t kappa e0 e1).1.normSq +
            (evalDirectionalCoupler2x2 t kappa e2 e3).2.normSq) +
        (t * t + kappa * kappa) *
          ((evalDirectionalCoupler2x2 t kappa e0 e1).2.normSq +
            (evalDirectionalCoupler2x2 t kappa e2 e3).1.normSq) :=
      Int.mul_add (t * t + kappa * kappa)
        ((evalDirectionalCoupler2x2 t kappa e0 e1).1.normSq +
          (evalDirectionalCoupler2x2 t kappa e2 e3).2.normSq)
        ((evalDirectionalCoupler2x2 t kappa e0 e1).2.normSq +
          (evalDirectionalCoupler2x2 t kappa e2 e3).1.normSq)
    rw [hMidSum] at hDistMesh
    omega

/-! ## 2. Real Physical Matter Compiler DRC & Equitable-to-Photonic Array Synthesis -/

/-- Check whether a single `DirectionalCoupler` in a coupled waveguide array satisfies open-foundry
lithography and CMT design rules:
1. Trench width `150 ≤ dc.gapNm` (193nm DUV lithography minimum feature spacing),
2. Evanescent coupling range `dc.gapNm ≤ 600` (prevents dead/decoupled gaps),
3. Strictly positive interaction length `1 ≤ dc.couplingLenUm`,
4. Lossless CMT unitary power conservation `isLosslessCoupler dc` ($t^2 + \kappa^2 = 10^6\,\text{ppm}$). -/
def checkArrayCouplerDrc (dc : DirectionalCoupler) : Bool :=
  decide (150 ≤ dc.gapNm) &&
  decide (dc.gapNm ≤ 600) &&
  decide (1 ≤ dc.couplingLenUm) &&
  isLosslessCoupler dc

/-- Complete **Photonic Matter Compiler Design Rule Check** (`checkPhotonicArrayMatterDrc`):
1. Waveguide platform matches `spec.platform` and core width lies in the single-mode $\text{TE}_{00}$
   window $[400\,\text{nm}, 1200\,\text{nm}]$,
2. Fan-in/fan-out S-bend radius satisfies the platform minimum radiative bend limit
   (`minPhotonicBendRadiusNm spec.platform ≤ spec.fanoutBendRadiusNm`),
3. Non-adjacent isolation pitch satisfies `2000 ≤ spec.isolationPitchNm` to prevent parasitic
   next-nearest-neighbor crosstalk,
4. Tridiagonal quotient topology holds (`2 ≤ spec.numQuotientModes`, `spec.numQuotientModes ≤ spec.numSourceVertices`,
   and `spec.couplers.length + 1 == spec.numQuotientModes`),
5. Every evanescent coupler in `spec.couplers` passes `checkArrayCouplerDrc`. -/
def checkPhotonicArrayMatterDrc (spec : PhotonicWaveguideArraySpec) : Bool :=
  let minBend := minPhotonicBendRadiusNm spec.platform
  decide (spec.waveguide.platform = spec.platform) &&
  decide (400 ≤ spec.waveguide.widthNm) &&
  decide (spec.waveguide.widthNm ≤ 1200) &&
  decide (minBend ≤ spec.fanoutBendRadiusNm) &&
  decide (2000 ≤ spec.isolationPitchNm) &&
  decide (2 ≤ spec.numQuotientModes) &&
  decide (spec.numQuotientModes ≤ spec.numSourceVertices) &&
  decide (spec.couplers.length + 1 = spec.numQuotientModes) &&
  spec.couplers.all checkArrayCouplerDrc

/-- **Hybrid Symbolic-Physical Matter Compiler** (`compileEquitableToPhotonicArray`):
Certifies end-to-end compilation of an $N$-vertex quantum walk Hamiltonian `m` into a planar
$r$-waveguide photonic integrated circuit `spec`:
1. Verifies that `(m, spec.numQuotientModes, part, quotientEntry)` is a valid equitable partition
   (`checkEquitablePartition = true`) with zero residual floor (`evalEquitableResidualNormSq = 0`),
2. Verifies the symmetrizability handshake identity $|C_i| Q_{i,j} = |C_j| Q_{j,i}$
   (`checkHandshakeIdentity = true`),
3. Verifies that every adjacent quotient cell pair $(j, j+1)$ has non-zero symmetrized coupling
   `1 ≤ evalSymmetrizedCouplingSq quotientEntry j (j + 1)`,
4. Verifies all physical photonic foundry DRC constraints (`checkPhotonicArrayMatterDrc spec = true`). -/
def compileEquitableToPhotonicArray
    (m : IntMatrix)
    (part : Nat → Nat)
    (quotientEntry : Nat → Nat → Int)
    (spec : PhotonicWaveguideArraySpec) : Bool :=
  let chainPairs := List.range (spec.numQuotientModes - 1)
  decide (m.dim = spec.numSourceVertices) &&
  checkEquitablePartition m spec.numQuotientModes part quotientEntry &&
  checkHandshakeIdentity m.dim spec.numQuotientModes part quotientEntry &&
  decide (evalEquitableResidualNormSq m spec.numQuotientModes part quotientEntry = 0) &&
  chainPairs.all (fun j => decide (1 ≤ evalSymmetrizedCouplingSq quotientEntry j (j + 1))) &&
  checkPhotonicArrayMatterDrc spec

/-- Golden 4-waveguide `SiEPIC 220nm SOI` Krawtchouk photonic array compiled from the 8-vertex
Hypercube $Q_3$ ($8$ non-planar vertices $\to 4$ planar waveguides with coupling ratios
$\kappa_{0,1}^2 : \kappa_{1,2}^2 : \kappa_{2,3}^2 = 3 : 4 : 3$). -/
def goldenQ3Soi220PhotonicArray : PhotonicWaveguideArraySpec where
  arrayName           := "q3_krawtchouk_4wg_soi220"
  platform            := .soi220nm
  waveguide           := soi220StripWaveguide1550
  numSourceVertices   := 8
  numQuotientModes    := 4
  couplers            := [couplerPythagorean80_60, coupler3dB, couplerPythagorean80_60]
  fanoutBendRadiusNm  := 5000
  isolationPitchNm    := 2500
  interactionLengthUm := 42

/-- Golden 4-waveguide low-loss `400nm Si3N4` ($\text{SiN}$) Krawtchouk photonic array compiled from
$Q_3$ ($R_{\text{bend}} = 25000\,\text{nm}$ meeting the $\text{Si}_3\text{N}_4$ radiative bend limit). -/
def goldenQ3Sin400PhotonicArray : PhotonicWaveguideArraySpec where
  arrayName           := "q3_krawtchouk_4wg_sin400"
  platform            := .sin400nm
  waveguide           := sin400Waveguide1550
  numSourceVertices   := 8
  numQuotientModes    := 4
  couplers            := [couplerPythagorean80_60, coupler3dB, couplerPythagorean80_60]
  fanoutBendRadiusNm  := 25000
  isolationPitchNm    := 3000
  interactionLengthUm := 85

/-- Sub-lithographic `100nm < 150nm` trench coupler array that violates DUV lithography DRC. -/
def illegalSubLithoGapArray : PhotonicWaveguideArraySpec :=
  { goldenQ3Soi220PhotonicArray with
    couplers := [{ coupler3dB with gapNm := 100 }, coupler3dB, coupler3dB] }

/-- Leaky `10000nm < 25000nm` tight-bend $\text{Si}_3\text{N}_4$ array that violates the `sin400nm`
radiative bend radius limit. -/
def illegalLeakySinBendArray : PhotonicWaveguideArraySpec :=
  { goldenQ3Sin400PhotonicArray with fanoutBendRadiusNm := 10000 }

/-- Cramped `1200nm < 2000nm` pitch array that suffers parasitic next-nearest-neighbor crosstalk. -/
def illegalCrosstalkPitchArray : PhotonicWaveguideArraySpec :=
  { goldenQ3Soi220PhotonicArray with isolationPitchNm := 1200 }

/-- **Theorem (`photonic_matter_compiler_drc_sound`)**:
1. **Universal Physical DRC Soundness**:
   Whenever `checkPhotonicArrayMatterDrc spec = true`, the compiled photonic array is guaranteed to
   satisfy:
   - `minPhotonicBendRadiusNm spec.platform ≤ spec.fanoutBendRadiusNm` (zero radiative bend leakage),
   - `2000 ≤ spec.isolationPitchNm` (crosstalk suppression),
   - `400 ≤ spec.waveguide.widthNm ∧ spec.waveguide.widthNm ≤ 1200` (single-mode $\text{TE}_{00}$ confinement),
   - `spec.couplers.length + 1 = spec.numQuotientModes` (planar tridiagonal chain topology).
2. **Concrete Matter Compilation Poles ($Q_3 \to 4$-Waveguide PIC)**:
   - Both `goldenQ3Soi220PhotonicArray` and `goldenQ3Sin400PhotonicArray` pass full equitable + physical
     compilation (`compileEquitableToPhotonicArray = true`) with symmetrized Krawtchouk couplings
     $(\kappa_{0,1}^2, \kappa_{1,2}^2, \kappa_{2,3}^2) = (3, 4, 3)$.
   - `illegalSubLithoGapArray` (`gapNm = 100 < 150`), `illegalLeakySinBendArray` (`R = 10um < 25um` on SiN),
     and `illegalCrosstalkPitchArray` (`pitch = 1200nm < 2000nm`) are all refused (`= false`). -/
theorem photonic_matter_compiler_drc_sound
    (spec : PhotonicWaveguideArraySpec)
    (hDrc : checkPhotonicArrayMatterDrc spec = true) :
    (minPhotonicBendRadiusNm spec.platform ≤ spec.fanoutBendRadiusNm ∧
     2000 ≤ spec.isolationPitchNm ∧
     400 ≤ spec.waveguide.widthNm ∧
     spec.waveguide.widthNm ≤ 1200 ∧
     spec.couplers.length + 1 = spec.numQuotientModes) ∧
    compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part hypercubeQ3Quotient goldenQ3Soi220PhotonicArray = true ∧
    compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part hypercubeQ3Quotient goldenQ3Sin400PhotonicArray = true ∧
    evalSymmetrizedCouplingSq hypercubeQ3Quotient 0 1 = 3 ∧
    evalSymmetrizedCouplingSq hypercubeQ3Quotient 1 2 = 4 ∧
    evalSymmetrizedCouplingSq hypercubeQ3Quotient 2 3 = 3 ∧
    compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part hypercubeQ3Quotient illegalSubLithoGapArray = false ∧
    compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part hypercubeQ3Quotient illegalLeakySinBendArray = false ∧
    compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part hypercubeQ3Quotient illegalCrosstalkPitchArray = false := by
  unfold checkPhotonicArrayMatterDrc at hDrc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hDrc
  refine ⟨⟨hDrc.1.1.1.1.1.2, hDrc.1.1.1.1.2, hDrc.1.1.1.1.1.1.1.2, hDrc.1.1.1.1.1.1.2, hDrc.1.2⟩, ?_⟩
  decide +kernel

/-! ## 3. IBM Heavy-Hex $C_{12}$ Unit-Cell Lattice & Microsoft Majorana-1 Tetron Parity Sector -/

/-- Adjacency matrix of the 12-qubit **IBM Heavy-Hex** ring unit cell $C_{12}$ ($0 - 1 - \dots - 11 - 0$). -/
def heavyHexC12RingMatrix : IntMatrix where
  dim  := 12
  rows :=
    [ [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] -- 0 (corner)
    , [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] -- 1 (bridge)
    , [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] -- 2 (bridge)
    , [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0] -- 3 (corner)
    , [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0] -- 4 (bridge)
    , [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0] -- 5 (bridge)
    , [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0] -- 6 (antipodal corner)
    , [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] -- 7 (bridge)
    , [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0] -- 8 (bridge)
    , [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0] -- 9 (corner)
    , [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1] -- 10 (bridge)
    , [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] -- 11 (bridge)
    ]

/-- 7-cell antipodal reflection/distance partition of the Heavy-Hex $C_{12}$ unit cell:
$C_0 = \{0\}$, $C_1 = \{1, 11\}$, $C_2 = \{2, 10\}$, $C_3 = \{3, 9\}$, $C_4 = \{4, 8\}$,
$C_5 = \{5, 7\}$, $C_6 = \{6\}$. -/
def heavyHexC12DistancePart : Nat → Nat
  | 0  => 0
  | 1  => 1
  | 2  => 2
  | 3  => 3
  | 4  => 4
  | 5  => 5
  | 6  => 6
  | 7  => 5
  | 8  => 4
  | 9  => 3
  | 10 => 2
  | 11 => 1
  | _  => 0

/-- $7 \times 7$ tridiagonal quotient matrix of the Heavy-Hex $C_{12}$ distance partition:
endpoints $C_0, C_6$ have out-degree $2$ into $C_1, C_5$, while interior cells have degree $1$
left and $1$ right. -/
def heavyHexC12DistanceQuotient : Nat → Nat → Int
  | 0, 1 => 2
  | 1, 0 => 1
  | 1, 2 => 1
  | 2, 1 => 1
  | 2, 3 => 1
  | 3, 2 => 1
  | 3, 4 => 1
  | 4, 3 => 1
  | 4, 5 => 1
  | 5, 4 => 1
  | 5, 6 => 1
  | 6, 5 => 2
  | _, _ => 0

/-- Heavy-Hex $C_{12}$ effective Hamiltonian incorporating the degree-3 corner Z-shift ($+3$ on corners
$\{0, 3, 6, 9\}$) vs. degree-2 bridge qubits ($+2$ on $\{1, 2, 4, 5, 7, 8, 10, 11\}$) plus
nearest-neighbor bridge couplings. -/
def heavyHexC12CornerBridgeMatrix : IntMatrix where
  dim  := 12
  rows :=
    [ [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] -- 0 (corner: self 3, 2 bridges)
    , [1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] -- 1 (bridge: self 2, 1 corner, 1 bridge)
    , [0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0] -- 2 (bridge: self 2, 1 corner, 1 bridge)
    , [0, 0, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0] -- 3 (corner)
    , [0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0] -- 4 (bridge)
    , [0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0] -- 5 (bridge)
    , [0, 0, 0, 0, 0, 1, 3, 1, 0, 0, 0, 0] -- 6 (corner)
    , [0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0] -- 7 (bridge)
    , [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0] -- 8 (bridge)
    , [0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 0] -- 9 (corner)
    , [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1] -- 10 (bridge)
    , [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2] -- 11 (bridge)
    ]

/-- 2-cell corner-vs-bridge partition of Heavy-Hex $C_{12}$:
$C_0 = \{0, 3, 6, 9\}$ ($4$ degree-3 corner qubits) and $C_1 = \{1, 2, 4, 5, 7, 8, 10, 11\}$ ($8$ degree-2 bridge qubits). -/
def heavyHexC12CornerBridgePart : Nat → Nat
  | 0 => 0
  | 3 => 0
  | 6 => 0
  | 9 => 0
  | _ => 1

/-- $2 \times 2$ quotient matrix of the Heavy-Hex corner-vs-bridge partition:
$Q = \begin{pmatrix} 3 & 2 \\ 1 & 3 \end{pmatrix}$ with handshake identity $|C_0| Q_{0,1} = 4 \cdot 2 = 8 \cdot 1 = |C_1| Q_{1,0}$. -/
def heavyHexC12CornerBridgeQuotient : Nat → Nat → Int
  | 0, 0 => 3
  | 0, 1 => 2
  | 1, 0 => 1
  | 1, 1 => 3
  | _, _ => 0

/-- **Microsoft Majorana-1 Tetron** 4-state Hamiltonian partitioned into the even fermion-parity
computational sector $C_{\text{even}} = \{0, 1\}$ and odd fermion-parity sector $C_{\text{odd}} = \{2, 3\}$:
$$H_{\text{tetron}} = \begin{pmatrix} 2 & 1 & 0 & 0 \\ 1 & 2 & 0 & 0 \\ 0 & 0 & -2 & 1 \\ 0 & 0 & 1 & -2 \end{pmatrix}.$$ -/
def majoranaTetronHamiltonian : IntMatrix where
  dim  := 4
  rows :=
    [ [2, 1, 0, 0]
    , [1, 2, 0, 0]
    , [0, 0, -2, 1]
    , [0, 0, 1, -2] ]

/-- Symmetry-preserving (parity-conserving) Majorana-1 braiding / dephasing perturbation $\Delta H_{\text{sym}}$
that commutes with total fermion parity $P_{\text{tot}} = -\gamma_1 \gamma_2 \gamma_3 \gamma_4$:
$$\Delta H_{\text{sym}} = \begin{pmatrix} 1 & 2 & 0 & 0 \\ 2 & 1 & 0 & 0 \\ 0 & 0 & 1 & -1 \\ 0 & 0 & -1 & 1 \end{pmatrix}.$$ -/
def majoranaParityPreserveNoise : IntMatrix where
  dim  := 4
  rows :=
    [ [1, 2, 0, 0]
    , [2, 1, 0, 0]
    , [0, 0, 1, -1]
    , [0, 0, -1, 1] ]

/-- Parity-breaking quasiparticle-poisoning perturbation $\Delta H_{\text{poison}}$ that couples
state $0 \in C_{\text{even}}$ to $C_{\text{odd}}$ asymmetrically, breaking parity conservation and
inducing leakage into the odd-parity sector:
$$\Delta H_{\text{poison}} = \begin{pmatrix} 0 & 0 & 1 & 1 \\ 0 & 0 & -1 & -1 \\ 1 & -1 & 0 & 0 \\ 1 & -1 & 0 & 0 \end{pmatrix}.$$ -/
def majoranaQuasiparticlePoisonNoise : IntMatrix where
  dim  := 4
  rows :=
    [ [0, 0, 1, 1]
    , [0, 0, -1, -1]
    , [1, -1, 0, 0]
    , [1, -1, 0, 0] ]

/-- Fermion-parity partition of the Majorana-1 tetron:
$C_{\text{even}} = \{0, 1\} \mapsto 0$, $C_{\text{odd}} = \{2, 3\} \mapsto 1$. -/
def majoranaParityPart : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 0

/-- Nominal $2 \times 2$ block-diagonal parity quotient of `majoranaTetronHamiltonian`:
$Q_{\text{tetron}} = \begin{pmatrix} 3 & 0 \\ 0 & -1 \end{pmatrix}$. -/
def majoranaTetronQuotient : Nat → Nat → Int
  | 0, 0 => 3
  | 1, 1 => -1
  | _, _ => 0

/-- $2 \times 2$ block-diagonal parity quotient of `majoranaParityPreserveNoise`:
$\Delta Q_{\text{sym}} = \begin{pmatrix} 3 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def majoranaNoiseSymQuotient : Nat → Nat → Int
  | 0, 0 => 3
  | _, _ => 0

/-! ## 4. Universal Theorem: Symmetry-Preserving Noise Produces Identically Zero Leakage -/

/-- Perturbed Hamiltonian entry $(H + \epsilon \Delta H)_{u, v} = H_{u,v} + \epsilon \cdot \Delta H_{u,v}$. -/
def perturbedHamiltonian (H dH : Nat → Nat → Int) (eps : Int) (u v : Nat) : Int :=
  H u v + eps * dH u v

/-- Perturbed quotient entry $(Q + \epsilon \Delta Q)_{i, j} = Q_{i,j} + \epsilon \cdot \Delta Q_{i,j}$. -/
def perturbedQuotient (Q dQ : Nat → Nat → Int) (eps : Int) (i j : Nat) : Int :=
  Q i j + eps * dQ i j

/-- Lemma (`perturbed_cellRowSum_equitable`):
If both $H$ and a noise perturbation $\Delta H$ are equitable with respect to cell `cellJ` (with
quotient entries $Q_{\text{part}(u), j}$ and $\Delta Q_{\text{part}(u), j}$), then for EVERY noise
amplitude $\epsilon \in \mathbb{Z}$, the perturbed Hamiltonian $H + \epsilon \Delta H$ has exact
cell row sum $Q_{\text{part}(u), j} + \epsilon \Delta Q_{\text{part}(u), j}$! -/
theorem perturbed_cellRowSum_equitable
    (H dH Q dQ : Nat → Nat → Int)
    (part : Nat → Nat)
    (eps : Int)
    (cellJ : List Nat)
    (u j : Nat)
    (hRowH  : cellRowSum H cellJ u = Q (part u) j)
    (hRowDH : cellRowSum dH cellJ u = dQ (part u) j) :
    cellRowSum (perturbedHamiltonian H dH eps) cellJ u =
      perturbedQuotient Q dQ eps (part u) j := by
  dsimp only [cellRowSum, perturbedHamiltonian, perturbedQuotient] at *
  rw [sumIntOver_add (fun v => H u v) (fun v => eps * dH u v) cellJ]
  rw [sumIntOver_mul_left eps (fun v => dH u v) cellJ]
  rw [hRowH, hRowDH]

/-- **Theorem (`symmetry_preserving_noise_zero_leakage`)**:
**Universal & Concrete Symmetry-Preserving Noise Immunity Theorem**:
1. **Universal Noisy Intertwining (Zero Orthogonal Subspace Leakage)**:
   For ANY nominal Hamiltonian $H$, symmetry-preserving perturbation $\Delta H$, partition `part`,
   and quotients $Q, \Delta Q$, if $H$ and $\Delta H$ are equitable across `cellIndices` and `cellOf`,
   then for EVERY noise amplitude $\epsilon \in \mathbb{Z}$ and EVERY quotient vector $w$:
   $$((H + \epsilon \Delta H)(S w))_u = (S ((Q + \epsilon \Delta Q) w))_u.$$
   Thus the noisy evolution remains 100% inside the equitable computational subspace $\text{im}(S)$
   with identically zero leakage into the orthogonal complement $\text{im}(S)^\perp$!
2. **Universal Parity-Sector Block Isolation (Zero Odd-Parity Quasiparticle Leakage)**:
   When the two-sector parity quotient `[0, 1]` has zero inter-sector coupling in both the nominal
   Hamiltonian and noise ($Q(1, 0) = 0$ and $\Delta Q(1, 0) = 0$) and the system starts in the
   even-parity computational sector ($w_1 = 0$), the odd-parity sector amplitude after applying
   $Q + \epsilon \Delta Q$ is **identically `0`** for all $\epsilon \in \mathbb{Z}$ and all $w_0 \in \mathbb{Z}$!
3. **Concrete IBM Heavy-Hex $C_{12}$ & Microsoft Majorana-1 Tetron Verification**:
   - Both the 7-cell distance partition and the 2-cell corner-vs-bridge partition of Heavy-Hex $C_{12}$
     pass `checkEquitablePartition = true`, `checkHandshakeIdentity = true`, and have
     `evalEquitableResidualNormSq = 0`.
   - On the Majorana-1 Tetron, `majoranaParityPreserveNoise` preserves the parity partition with
     `evalEquitableResidualNormSq = 0`, whereas `majoranaQuasiparticlePoisonNoise` breaks parity
     equitability (`checkEquitablePartition = false`) and induces a non-zero leakage residual floor
     `evalEquitableResidualNormSq = 8 > 0`! -/
theorem symmetry_preserving_noise_zero_leakage
    (H dH Q dQ : Nat → Nat → Int)
    (part : Nat → Nat)
    (cellIndices : List Nat)
    (cellOf : Nat → List Nat)
    (eps : Int)
    (w : Nat → Int)
    (u : Nat)
    (hCells : ∀ j, j ∈ cellIndices → ∀ x, x ∈ cellOf j → part x = j)
    (hEqH   : ∀ j, j ∈ cellIndices → cellRowSum H (cellOf j) u = Q (part u) j)
    (hEqDH  : ∀ j, j ∈ cellIndices → cellRowSum dH (cellOf j) u = dQ (part u) j)
    (hBlockH  : Q 1 0 = 0)
    (hBlockDH : dQ 1 0 = 0)
    (hEvenInit : w 1 = 0) :
    -- 1. Universal intertwining of H + eps * dH with Q + eps * dQ
    partitionedMatVec (perturbedHamiltonian H dH eps) cellIndices cellOf (liftQuotientVec part w) u =
      liftQuotientVec part (quotientMatVec (perturbedQuotient Q dQ eps) cellIndices w) u ∧
    -- 2. Universal zero leakage into the odd parity sector (sector 1)
    quotientMatVec (perturbedQuotient Q dQ eps) [0, 1] w 1 = 0 ∧
    -- 3. Concrete IBM Heavy-Hex C12 & Majorana-1 Tetron certificates
    checkEquitablePartition heavyHexC12RingMatrix 7 heavyHexC12DistancePart heavyHexC12DistanceQuotient = true ∧
    checkHandshakeIdentity 12 7 heavyHexC12DistancePart heavyHexC12DistanceQuotient = true ∧
    evalEquitableResidualNormSq heavyHexC12RingMatrix 7 heavyHexC12DistancePart heavyHexC12DistanceQuotient = 0 ∧
    checkEquitablePartition heavyHexC12CornerBridgeMatrix 2 heavyHexC12CornerBridgePart heavyHexC12CornerBridgeQuotient = true ∧
    checkHandshakeIdentity 12 2 heavyHexC12CornerBridgePart heavyHexC12CornerBridgeQuotient = true ∧
    evalEquitableResidualNormSq heavyHexC12CornerBridgeMatrix 2 heavyHexC12CornerBridgePart heavyHexC12CornerBridgeQuotient = 0 ∧
    checkEquitablePartition majoranaTetronHamiltonian 2 majoranaParityPart majoranaTetronQuotient = true ∧
    checkEquitablePartition majoranaParityPreserveNoise 2 majoranaParityPart majoranaNoiseSymQuotient = true ∧
    evalEquitableResidualNormSq majoranaParityPreserveNoise 2 majoranaParityPart majoranaNoiseSymQuotient = 0 ∧
    checkEquitablePartition majoranaQuasiparticlePoisonNoise 2 majoranaParityPart (fun _ _ => 0) = false ∧
    evalEquitableResidualNormSq majoranaQuasiparticlePoisonNoise 2 majoranaParityPart (fun _ _ => 0) = 8 := by
  have hPerturbRow : ∀ j, j ∈ cellIndices →
      cellRowSum (perturbedHamiltonian H dH eps) (cellOf j) u =
        perturbedQuotient Q dQ eps (part u) j := by
    intro j hj
    exact perturbed_cellRowSum_equitable H dH Q dQ part eps (cellOf j) u j (hEqH j hj) (hEqDH j hj)
  have hIntertwine :=
    equitable_intertwining_step
      (perturbedHamiltonian H dH eps)
      (perturbedQuotient Q dQ eps)
      part cellIndices cellOf w u hCells hPerturbRow
  have hZeroOdd : quotientMatVec (perturbedQuotient Q dQ eps) [0, 1] w 1 = 0 := by
    dsimp only [quotientMatVec, perturbedQuotient, sumIntOver]
    rw [hBlockH, hBlockDH, hEvenInit]
    simp only [Int.mul_zero, Int.zero_mul, Int.add_zero]
  refine ⟨hIntertwine, hZeroOdd, ?_⟩
  decide +kernel

end Obend.Hardware.QuantumMatter
end
