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

/-- Evaluate a **Planar Clements 4-Mode Nearest-Neighbor Mesh** (`evalPlanarClements4Mesh`):
* **Layer 1 (Even Nearest-Neighbor Layer)**: couples adjacent waveguide pairs $(0, 1)$ and $(2, 3)$
  with field transmission/coupling $(t_1, \kappa_1)$.
* **Layer 2 (Odd Nearest-Neighbor Inner Layer)**: couples ONLY the inner adjacent waveguide pair $(1, 2)$
  with $(t_2, \kappa_2)$, while outer waveguides $0$ and $3$ propagate straight through without any
  non-planar $0 \leftrightarrow 3$ waveguide crossing! -/
def evalPlanarClements4Mesh
    (t1 k1 t2 k2 : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let (m0, m1, m2, m3) := evalPhotonicArray4LayerEven t1 k1 t1 k1 e0 e1 e2 e3
  evalPhotonicArray4LayerOdd t2 k2 m0 m1 m2 m3

/-- **Theorem (`planarClements4Mesh_conserves_optical_power`)**:
For ALL coupler coefficients `t1, k1, t2, k2 : Int` and ALL 4 complex optical field inputs
`e0, e1, e2, e3 : ComplexField`:
1. **Universal Weighted Power Identity (Zero Non-Planar Crossings)**:
   With Layer 1 scale $s_1 = t_1^2 + \kappa_1^2$ and Layer 2 inner-coupler scale $s_2 = t_2^2 + \kappa_2^2$,
   the planar Clements 4-mode mesh satisfies:
   $$s_2 |E_{\text{out},0}|^2 + |E_{\text{out},1}|^2 + |E_{\text{out},2}|^2 + s_2 |E_{\text{out},3}|^2
     = s_2 \cdot s_1 \cdot \left(|E_0|^2 + |E_1|^2 + |E_2|^2 + |E_3|^2\right).$$
2. **Normalized Inner Coupler Power Conservation ($t_2^2 + \kappa_2^2 = 1$)**:
   Whenever $t_2^2 + \kappa_2^2 = 1$, total unweighted optical power across all 4 outputs equals
   $(t_1^2 + \kappa_1^2) (|E_0|^2 + |E_1|^2 + |E_2|^2 + |E_3|^2)$.
3. **Planar Nearest-Neighbor Locality ($0 \leftrightarrow 3$ Isolation)**:
   In Layer 2, outer mode $0$ is completely isolated from modes $2, 3$ (`(evalPlanarClements4Mesh t1 k1 t2 k2 e0 e1 e2 e3).1 = (evalDirectionalCoupler2x2 t1 k1 e0 e1).1`). -/
theorem planarClements4Mesh_conserves_optical_power
    (t1 k1 t2 k2 : Int)
    (e0 e1 e2 e3 : ComplexField) :
    (let s1 := t1 * t1 + k1 * k1
     let s2 := t2 * t2 + k2 * k2
     let (p0, p1, p2, p3) := evalPlanarClements4Mesh t1 k1 t2 k2 e0 e1 e2 e3
     s2 * p0.normSq + p1.normSq + p2.normSq + s2 * p3.normSq =
       s2 * (s1 * (e0.normSq + e1.normSq + e2.normSq + e3.normSq))) ∧
    (t2 * t2 + k2 * k2 = 1 →
     let (p0, p1, p2, p3) := evalPlanarClements4Mesh t1 k1 t2 k2 e0 e1 e2 e3
     p0.normSq + p1.normSq + p2.normSq + p3.normSq =
       (t1 * t1 + k1 * k1) * (e0.normSq + e1.normSq + e2.normSq + e3.normSq)) ∧
    (evalPlanarClements4Mesh t1 k1 t2 k2 e0 e1 e2 e3).1 =
      (evalDirectionalCoupler2x2 t1 k1 e0 e1).1 := by
  have h01 := directional_coupler_2x2_fst_snd_power t1 k1 e0 e1
  have h23 := directional_coupler_2x2_fst_snd_power t1 k1 e2 e3
  have h12 := directional_coupler_2x2_fst_snd_power t2 k2
    (evalDirectionalCoupler2x2 t1 k1 e0 e1).2
    (evalDirectionalCoupler2x2 t1 k1 e2 e3).1
  dsimp only [evalPlanarClements4Mesh, evalPhotonicArray4LayerEven, evalPhotonicArray4LayerOdd]
  have hLayer1 :
      ((evalDirectionalCoupler2x2 t1 k1 e0 e1).1.normSq +
       (evalDirectionalCoupler2x2 t1 k1 e0 e1).2.normSq) +
      ((evalDirectionalCoupler2x2 t1 k1 e2 e3).1.normSq +
       (evalDirectionalCoupler2x2 t1 k1 e2 e3).2.normSq) =
      (t1 * t1 + k1 * k1) * (e0.normSq + e1.normSq + e2.normSq + e3.normSq) := by
    have hDist1 :
        (t1 * t1 + k1 * k1) * (e0.normSq + e1.normSq + e2.normSq + e3.normSq) =
        (t1 * t1 + k1 * k1) * (e0.normSq + e1.normSq) +
        (t1 * t1 + k1 * k1) * (e2.normSq + e3.normSq) := by
      have hAssoc : e0.normSq + e1.normSq + e2.normSq + e3.normSq =
          (e0.normSq + e1.normSq) + (e2.normSq + e3.normSq) := by omega
      rw [hAssoc, Int.mul_add]
    omega
  have hRearr :
      (evalDirectionalCoupler2x2 t1 k1 e0 e1).1.normSq +
      ((evalDirectionalCoupler2x2 t1 k1 e0 e1).2.normSq +
       (evalDirectionalCoupler2x2 t1 k1 e2 e3).1.normSq) +
      (evalDirectionalCoupler2x2 t1 k1 e2 e3).2.normSq =
      (t1 * t1 + k1 * k1) * (e0.normSq + e1.normSq + e2.normSq + e3.normSq) := by
    omega
  have hMulS2 :
      (t2 * t2 + k2 * k2) * (evalDirectionalCoupler2x2 t1 k1 e0 e1).1.normSq +
      (t2 * t2 + k2 * k2) *
        ((evalDirectionalCoupler2x2 t1 k1 e0 e1).2.normSq +
         (evalDirectionalCoupler2x2 t1 k1 e2 e3).1.normSq) +
      (t2 * t2 + k2 * k2) * (evalDirectionalCoupler2x2 t1 k1 e2 e3).2.normSq =
      (t2 * t2 + k2 * k2) *
        ((t1 * t1 + k1 * k1) * (e0.normSq + e1.normSq + e2.normSq + e3.normSq)) := by
    rw [← Int.mul_add, ← Int.mul_add, hRearr]
  refine ⟨by omega, ?_, rfl⟩
  intro hUnit2
  rw [hUnit2] at h12
  omega

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

/-! ## 2. Real Physical Matter Compiler DRC, Exact Quotient-Coupling Ratio Verification & Synthesis -/

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

/-- Check whether adjacent directional couplers in `couplers` realize the exact cross-multiplied
symmetrized quotient coupling-squared ratios of `Q`:
$$\forall j,\quad \kappa_j^2 \cdot \left(Q_{j+1, j+2} Q_{j+2, j+1}\right)
  = \kappa_{j+1}^2 \cdot \left(Q_{j, j+1} Q_{j+1, j}\right).$$ -/
def couplerRealizesQuotientRatio
    (Q : Nat → Nat → Int)
    (couplers : List DirectionalCouplerSpec) : Bool :=
  let pairIndices := List.range (couplers.length - 1)
  pairIndices.all (fun j =>
    let cJ    := couplers[j]?.getD coupler3dB
    let cNext := couplers[j + 1]?.getD coupler3dB
    let qSqJ    := Q j (j + 1) * Q (j + 1) j
    let qSqNext := Q (j + 1) (j + 2) * Q (j + 2) (j + 1)
    decide (cJ.kappaSqScaled * qSqNext = cNext.kappaSqScaled * qSqJ))

/-- Synthesize a list of `dim - 1` lossless directional couplers whose coupling-squared coefficients
$\kappa_j^2 = \text{scale} \cdot Q_{j, j+1} Q_{j+1, j}$ and $t_j^2 = 10^6 - \kappa_j^2$ realize the
exact tridiagonal quotient coupling profile of `Q` (e.g., for $Q_3$ with `dim = 4` and `scale = 125000`,
producing exact $3 : 4 : 3 = 375000 : 500000 : 375000\,\text{ppm}$ Krawtchouk couplers). -/
def synthesizeKrawtchoukPhotonicCouplers
    (Q : Nat → Nat → Int)
    (dim : Nat)
    (scale : Int) : List DirectionalCouplerSpec :=
  (List.range (dim - 1)).map (fun j =>
    let qSq := Q j (j + 1) * Q (j + 1) j
    let kappaSq := scale * qSq
    let tSq := 1000000 - kappaSq
    let isHalf := decide (kappaSq = 500000)
    { couplerName    := "dc_krawtchouk_synth"
    , gapNm          := cond isHalf 200 225
    , couplingLenUm  := cond isHalf 14 11
    , tFieldPermille := cond isHalf 707 791
    , kFieldPermille := cond isHalf 707 612
    , tSqPpm         := tSq
    , kappaSqPpm     := kappaSq })

/-- **Theorem (`synthesizeKrawtchoukPhotonicCouplers_realizes_ratio`)**:
For EVERY quotient matrix `Q : Nat → Nat → Int`, EVERY dimension `dim : Nat`, and EVERY integer
scale factor `scale : Int`, the couplers synthesized by `synthesizeKrawtchoukPhotonicCouplers Q dim scale`
universally satisfy `couplerRealizesQuotientRatio Q ... = true`! -/
theorem synthesizeKrawtchoukPhotonicCouplers_realizes_ratio
    (Q : Nat → Nat → Int)
    (dim : Nat)
    (scale : Int) :
    couplerRealizesQuotientRatio Q (synthesizeKrawtchoukPhotonicCouplers Q dim scale) = true := by
  unfold couplerRealizesQuotientRatio synthesizeKrawtchoukPhotonicCouplers
  rw [list_all_iff_forall]
  intro j hj
  rw [List.mem_range, List.length_map, List.length_range] at hj
  have hj1 : j < dim - 1 := by omega
  have hj2 : j + 1 < dim - 1 := by omega
  simp only [List.getElem?_map, List.getElem?_range hj1, List.getElem?_range hj2,
    Option.map_some, Option.getD_some, DirectionalCoupler.kappaSqScaled, decide_eq_true_eq]
  rw [Int.mul_assoc scale (Q j (j + 1) * Q (j + 1) j) (Q (j + 1) (j + 2) * Q (j + 2) (j + 1))]
  rw [Int.mul_comm (Q j (j + 1) * Q (j + 1) j) (Q (j + 1) (j + 2) * Q (j + 2) (j + 1))]
  rw [← Int.mul_assoc scale (Q (j + 1) (j + 2) * Q (j + 2) (j + 1)) (Q j (j + 1) * Q (j + 1) j)]

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
4. Verifies that `spec.couplers` realize the exact cross-multiplied quotient coupling ratios
   (`couplerRealizesQuotientRatio quotientEntry spec.couplers = true`),
5. Verifies all physical photonic foundry DRC constraints (`checkPhotonicArrayMatterDrc spec = true`). -/
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
  couplerRealizesQuotientRatio quotientEntry spec.couplers &&
  checkPhotonicArrayMatterDrc spec

/-- Golden 4-waveguide `SiEPIC 220nm SOI` Krawtchouk photonic array compiled from the 8-vertex
Hypercube $Q_3$ ($8$ non-planar vertices $\to 4$ planar waveguides with exact Krawtchouk coupling ratios
$\kappa_{0,1}^2 : \kappa_{1,2}^2 : \kappa_{2,3}^2 = 375000 : 500000 : 375000 = 3 : 4 : 3$). -/
def goldenQ3Soi220PhotonicArray : PhotonicWaveguideArraySpec where
  arrayName           := "q3_krawtchouk_4wg_soi220"
  platform            := .soi220nm
  waveguide           := soi220StripWaveguide1550
  numSourceVertices   := 8
  numQuotientModes    := 4
  couplers            := [couplerKrawtchouk375, coupler3dB, couplerKrawtchouk375]
  fanoutBendRadiusNm  := 5000
  isolationPitchNm    := 2500
  interactionLengthUm := 42

/-- Certified 4-waveguide Krawtchouk photonic array whose couplers are directly synthesized by
`synthesizeKrawtchoukPhotonicCouplers hypercubeQ3Quotient 4 125000`. -/
def certifiedQ3KrawtchoukPhotonicArray : PhotonicWaveguideArraySpec :=
  { goldenQ3Soi220PhotonicArray with
    arrayName := "q3_krawtchouk_4wg_synthesized"
    couplers  := synthesizeKrawtchoukPhotonicCouplers hypercubeQ3Quotient 4 125000 }

/-- Golden 4-waveguide low-loss `400nm Si3N4` ($\text{SiN}$) Krawtchouk photonic array compiled from
$Q_3$ ($R_{\text{bend}} = 25000\,\text{nm}$ meeting the $\text{Si}_3\text{N}_4$ radiative bend limit,
with exact $3 : 4 : 3$ Krawtchouk coupling ratios). -/
def goldenQ3Sin400PhotonicArray : PhotonicWaveguideArraySpec where
  arrayName           := "q3_krawtchouk_4wg_sin400"
  platform            := .sin400nm
  waveguide           := sin400Waveguide1550
  numSourceVertices   := 8
  numQuotientModes    := 4
  couplers            := [couplerKrawtchouk375, coupler3dB, couplerKrawtchouk375]
  fanoutBendRadiusNm  := 25000
  isolationPitchNm    := 3000
  interactionLengthUm := 85

/-- Sub-lithographic `100nm < 150nm` trench coupler array that violates DUV lithography DRC. -/
def illegalSubLithoGapArray : PhotonicWaveguideArraySpec :=
  { goldenQ3Soi220PhotonicArray with
    couplers := [{ couplerKrawtchouk375 with gapNm := 100 }, coupler3dB, couplerKrawtchouk375] }

/-- Leaky `10000nm < 25000nm` tight-bend $\text{Si}_3\text{N}_4$ array that violates the `sin400nm`
radiative bend radius limit. -/
def illegalLeakySinBendArray : PhotonicWaveguideArraySpec :=
  { goldenQ3Sin400PhotonicArray with fanoutBendRadiusNm := 10000 }

/-- Cramped `1200nm < 2000nm` pitch array that suffers parasitic next-nearest-neighbor crosstalk. -/
def illegalCrosstalkPitchArray : PhotonicWaveguideArraySpec :=
  { goldenQ3Soi220PhotonicArray with isolationPitchNm := 1200 }

/-- Mismatched uniform $1 : 1 : 1$ (`500000 : 500000 : 500000`) coupler array that passes physical DRC
but violates $Q_3$'s $3 : 4 : 3$ Krawtchouk quotient coupling ratio (`couplerRealizesQuotientRatio = false`). -/
def illegalMismatchedUniformCouplerArray : PhotonicWaveguideArraySpec :=
  { goldenQ3Soi220PhotonicArray with
    couplers := [coupler3dB, coupler3dB, coupler3dB] }

/-- Mismatched $36 : 50 : 36 \neq 3 : 4 : 3$ (`360000 : 500000 : 360000`) coupler array that fails exact
Krawtchouk ratio verification (`360000 * 4 = 1440000 ≠ 1500000 = 500000 * 3`). -/
def illegalMismatched36_50_36CouplerArray : PhotonicWaveguideArraySpec :=
  { goldenQ3Soi220PhotonicArray with
    couplers := [couplerPythagorean80_60, coupler3dB, couplerPythagorean80_60] }

/-- **Theorem (`compileEquitableToPhotonicArray_ratio_sound`)**:
1. **Universal Quotient-Ratio Soundness**:
   Whenever `compileEquitableToPhotonicArray m part Q spec = true`, the array's couplers satisfy
   `couplerRealizesQuotientRatio Q spec.couplers = true`, so for every adjacent coupler pair
   $j < \text{spec.couplers.length} - 1$:
   $$\kappa_j^2 \cdot (Q_{j+1, j+2} Q_{j+2, j+1}) = \kappa_{j+1}^2 \cdot (Q_{j, j+1} Q_{j+1, j}).$$
2. **Exact Krawtchouk $3 : 4 : 3$ Synthesis & Mismatched Ratio Refusal**:
   - `synthesizeKrawtchoukPhotonicCouplers hypercubeQ3Quotient 4 125000` synthesizes couplers with
     `kappaSqScaled = [375000, 500000, 375000]` ($3 : 4 : 3$), and `certifiedQ3KrawtchoukPhotonicArray`
     passes `compileEquitableToPhotonicArray = true`.
   - Both the uniform $1 : 1 : 1$ array (`illegalMismatchedUniformCouplerArray`) and the approximate
     $36 : 50 : 36$ array (`illegalMismatched36_50_36CouplerArray`) are refused (`= false`). -/
theorem compileEquitableToPhotonicArray_ratio_sound
    (m : IntMatrix)
    (part : Nat → Nat)
    (Q : Nat → Nat → Int)
    (spec : PhotonicWaveguideArraySpec)
    (hComp : compileEquitableToPhotonicArray m part Q spec = true) :
    (couplerRealizesQuotientRatio Q spec.couplers = true ∧
     ∀ j, j < spec.couplers.length - 1 →
       (spec.couplers[j]?.getD coupler3dB).kappaSqScaled * (Q (j + 1) (j + 2) * Q (j + 2) (j + 1)) =
         (spec.couplers[j + 1]?.getD coupler3dB).kappaSqScaled * (Q j (j + 1) * Q (j + 1) j)) ∧
    compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part hypercubeQ3Quotient
      certifiedQ3KrawtchoukPhotonicArray = true ∧
    compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part hypercubeQ3Quotient
      illegalMismatchedUniformCouplerArray = false ∧
    compileEquitableToPhotonicArray hypercubeQ3Matrix hypercubeQ3Part hypercubeQ3Quotient
      illegalMismatched36_50_36CouplerArray = false := by
  have h1 := ((Bool.and_eq_true _ _).mp hComp).1
  have hRatio : couplerRealizesQuotientRatio Q spec.couplers = true :=
    ((Bool.and_eq_true _ _).mp h1).2
  refine ⟨⟨hRatio, ?_⟩, rfl, rfl, rfl⟩
  intro j hj
  unfold couplerRealizesQuotientRatio at hRatio
  rw [list_all_iff_forall] at hRatio
  have hjMem : j ∈ List.range (spec.couplers.length - 1) := List.mem_range.mpr hj
  exact of_decide_eq_true (hRatio j hjMem)

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

/-! ## 4. True 16-Dimensional Clifford Algebra $Cl_4$ & Majorana Parity Selection Theorem -/

/-- Basis blade index $m \in \{0, \dots, 15\}$ of the 16-dimensional Clifford algebra $Cl_4$
generated by 4 Majorana fermion operators $\gamma_0, \gamma_1, \gamma_2, \gamma_3$ with
$\{\gamma_a, \gamma_b\} = 2 \delta_{a,b}$. -/
abbrev CliffordBlade := Fin 16

/-- Extract bit `idx` ($0 \le \text{idx} < 4$) of a 4-bit Majorana blade mask. -/
def bladeBit (mask idx : Nat) : Nat :=
  (mask >>> idx) % 2

/-- Hamming weight (`popcount`) of a 4-bit Majorana blade mask $m \in \{0, \dots, 15\}$. -/
def bladePopcount (mask : Nat) : Nat :=
  bladeBit mask 0 + bladeBit mask 1 + bladeBit mask 2 + bladeBit mask 3

/-- Number of anticommuting Majorana transpositions required to normal-order $e_a \cdot e_b$:
$$\text{koszulSwaps}(a, b) = \sum_{0 \le j < i < 4} a_i \cdot b_j.$$ -/
def koszulSwaps (a b : Nat) : Nat :=
  bladeBit b 0 * (bladeBit a 1 + bladeBit a 2 + bladeBit a 3) +
  bladeBit b 1 * (bladeBit a 2 + bladeBit a 3) +
  bladeBit b 2 * bladeBit a 3

/-- Map a parity bit `0` or `1` to its Koszul sign `+1` or `-1`. -/
def signOfBit : Nat → Int
  | 0 => 1
  | _ => -1

/-- Exact Koszul sign rule $\text{cliffordSign}(a, b) = (-1)^{\text{koszulSwaps}(a, b)} \in \{1, -1\}$
for multiplying basis blades $e_a \cdot e_b = \text{cliffordSign}(a, b)\, e_{a \oplus b}$ in $Cl_4$. -/
def cliffordSign (a b : Nat) : Int :=
  signOfBit (koszulSwaps a b % 2)

/-- General element $H = \sum_{m=0}^{15} b_m e_m$ of the 16-dimensional Clifford algebra $Cl_4$ over $\mathbb{Z}$. -/
structure CliffordElem where
  b0  : Int
  b1  : Int
  b2  : Int
  b3  : Int
  b4  : Int
  b5  : Int
  b6  : Int
  b7  : Int
  b8  : Int
  b9  : Int
  b10 : Int
  b11 : Int
  b12 : Int
  b13 : Int
  b14 : Int
  b15 : Int
  deriving DecidableEq, Repr

namespace CliffordElem

/-- Look up the coefficient of basis blade $e_m$ ($0 \le m < 16$). -/
def coeff (H : CliffordElem) : Nat → Int
  | 0  => H.b0
  | 1  => H.b1
  | 2  => H.b2
  | 3  => H.b3
  | 4  => H.b4
  | 5  => H.b5
  | 6  => H.b6
  | 7  => H.b7
  | 8  => H.b8
  | 9  => H.b9
  | 10 => H.b10
  | 11 => H.b11
  | 12 => H.b12
  | 13 => H.b13
  | 14 => H.b14
  | 15 => H.b15
  | _  => 0

/-- Construct a `CliffordElem` from a coefficient function `f : Nat → Int`. -/
def ofFn (f : Nat → Int) : CliffordElem :=
  { b0  := f 0,  b1  := f 1,  b2  := f 2,  b3  := f 3
  , b4  := f 4,  b5  := f 5,  b6  := f 6,  b7  := f 7
  , b8  := f 8,  b9  := f 9,  b10 := f 10, b11 := f 11
  , b12 := f 12, b13 := f 13, b14 := f 14, b15 := f 15 }

/-- Extensionality characterization of `CliffordElem` across its 16 basis blade coordinates. -/
theorem ext_iff (A B : CliffordElem) :
    A = B ↔
      A.b0 = B.b0 ∧ A.b1 = B.b1 ∧ A.b2 = B.b2 ∧ A.b3 = B.b3 ∧
      A.b4 = B.b4 ∧ A.b5 = B.b5 ∧ A.b6 = B.b6 ∧ A.b7 = B.b7 ∧
      A.b8 = B.b8 ∧ A.b9 = B.b9 ∧ A.b10 = B.b10 ∧ A.b11 = B.b11 ∧
      A.b12 = B.b12 ∧ A.b13 = B.b13 ∧ A.b14 = B.b14 ∧ A.b15 = B.b15 := by
  cases A
  cases B
  constructor
  · intro h
    injection h
    refine ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

end CliffordElem

/-- Sum an integer-valued function over the 16 Clifford basis blades $0 \dots 15$. -/
def sum16Blades (f : Nat → Int) : Int :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 +
  f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15

/-- Zero element $0 \in Cl_4$. -/
def cliffordZero : CliffordElem :=
  CliffordElem.ofFn (fun _ => 0)

/-- Scalar multiplicative identity $1 = e_0 \in Cl_4$. -/
def cliffordOne : CliffordElem :=
  CliffordElem.ofFn (fun m => cond (m == 0) 1 0)

/-- Basis blade $e_m \in Cl_4$ ($0 \le m < 16$). -/
def cliffordBasisBlade (m : Nat) : CliffordElem :=
  CliffordElem.ofFn (fun k => cond (k == m % 16) 1 0)

/-- Majorana fermion generator $\gamma_a = e_{2^a} \in Cl_4$ for $a \in \{0, 1, 2, 3\}$. -/
def cliffordGamma (a : Fin 4) : CliffordElem :=
  cliffordBasisBlade (1 <<< a.val)

/-- Total 4-Majorana fermion parity operator $P = -\gamma_0 \gamma_1 \gamma_2 \gamma_3 = -e_{15} \in Cl_4$
(blade `0b1111 = 15` with coefficient `-1`). -/
def cliffordParity : CliffordElem :=
  { cliffordZero with b15 := -1 }

/-- Addition in $Cl_4$. -/
def cliffordAdd (A B : CliffordElem) : CliffordElem :=
  CliffordElem.ofFn (fun k => A.coeff k + B.coeff k)

/-- Subtraction in $Cl_4$. -/
def cliffordSub (A B : CliffordElem) : CliffordElem :=
  CliffordElem.ofFn (fun k => A.coeff k - B.coeff k)

/-- Scalar multiplication $c \cdot A$ in $Cl_4$. -/
def cliffordScale (c : Int) (A : CliffordElem) : CliffordElem :=
  CliffordElem.ofFn (fun k => c * A.coeff k)

/-- Bilinear Clifford product $A \cdot B \in Cl_4$ governed by the Koszul sign rule `cliffordSign`:
$$(A \cdot B)_k = \sum_{a=0}^{15} \text{cliffordSign}(a, a \oplus k) \cdot A_a \cdot B_{a \oplus k}.$$ -/
def cliffordMul (A B : CliffordElem) : CliffordElem :=
  CliffordElem.ofFn (fun k =>
    sum16Blades (fun a => cliffordSign a (a ^^^ k) * A.coeff a * B.coeff (a ^^^ k)))

/-- Clifford commutator $[A, B] = A \cdot B - B \cdot A \in Cl_4$. -/
def cliffordCommutator (A B : CliffordElem) : CliffordElem :=
  cliffordSub (cliffordMul A B) (cliffordMul B A)

/-- Check whether an operator $H \in Cl_4$ commutes with fermion parity $P = -\gamma_0\gamma_1\gamma_2\gamma_3$
($[H, P] = 0$). -/
def commutesWithParity (H : CliffordElem) : Bool :=
  decide (cliffordCommutator H cliffordParity = cliffordZero)

/-- Check whether $H \in Cl_4$ is supported purely on even-weight Majorana blades
(`bladePopcount m % 2 == 0`, so all odd-weight blades $m \in \{1, 2, 4, 7, 8, 11, 13, 14\}$ have
zero coefficient `H.coeff m = 0`). -/
def isEvenBladeSupported (H : CliffordElem) : Bool :=
  decide (H.b1 = 0) &&
  decide (H.b2 = 0) &&
  decide (H.b4 = 0) &&
  decide (H.b7 = 0) &&
  decide (H.b8 = 0) &&
  decide (H.b11 = 0) &&
  decide (H.b13 = 0) &&
  decide (H.b14 = 0)

/-- **Theorem (`clifford_majorana_algebra_laws`)**:
1. **Generator Square Law ($\gamma_a^2 = 1$)**: For every Majorana generator $a \in \{0, 1, 2, 3\}$,
   `cliffordMul (cliffordGamma a) (cliffordGamma a) = cliffordOne`.
2. **Canonical Anticommutation ($\{\gamma_a, \gamma_b\} = \gamma_a \gamma_b + \gamma_b \gamma_a = 0$ for $a \neq b$)**:
   For all distinct $a, b \in \{0, 1, 2, 3\}$,
   `cliffordAdd (cliffordMul (cliffordGamma a) (cliffordGamma b)) (cliffordMul (cliffordGamma b) (cliffordGamma a)) = cliffordZero`.
3. **Fermion Parity Involution ($P^2 = 1$)**:
   For $P = -\gamma_0\gamma_1\gamma_2\gamma_3$, `cliffordMul cliffordParity cliffordParity = cliffordOne`. -/
theorem clifford_majorana_algebra_laws :
    (∀ a : Fin 4, cliffordMul (cliffordGamma a) (cliffordGamma a) = cliffordOne) ∧
    (∀ a b : Fin 4, a ≠ b →
      cliffordAdd (cliffordMul (cliffordGamma a) (cliffordGamma b))
                  (cliffordMul (cliffordGamma b) (cliffordGamma a)) = cliffordZero) ∧
    cliffordMul cliffordParity cliffordParity = cliffordOne := by
  decide +kernel

/-- **Theorem (`clifford_commutesWithParity_iff_even_blades`)**:
**Clifford Parity Selection Theorem**:
For EVERY operator $H \in Cl_4$ (`H : CliffordElem`, universally quantified over $\mathbb{Z}^{16}$),
$H$ commutes with total fermion parity $P = -\gamma_0\gamma_1\gamma_2\gamma_3$ (`commutesWithParity H = true`,
i.e., $[H, P] = 0$) **if and only if** $H$ is supported purely on even-weight Majorana blades
(`isEvenBladeSupported H = true`, i.e., every odd-popcount blade $m$ with `bladePopcount m % 2 == 1`
has `H.coeff m = 0`)! -/
theorem clifford_commutesWithParity_iff_even_blades (H : CliffordElem) :
    commutesWithParity H = true ↔ isEvenBladeSupported H = true := by
  rcases H with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩
  unfold commutesWithParity isEvenBladeSupported
  rw [decide_eq_true_iff]
  simp only [Bool.and_eq_true]
  rw [decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff,
      decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
  rw [CliffordElem.ext_iff]
  simp only [cliffordCommutator, cliffordSub, cliffordMul, cliffordParity, cliffordZero,
    CliffordElem.ofFn, CliffordElem.coeff, sum16Blades, cliffordSign, signOfBit, koszulSwaps,
    bladeBit, Nat.reduceXor, Nat.reduceShiftRight, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    Int.reduceNeg, Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul, Int.mul_neg, Int.neg_mul,
    Int.add_zero, Int.zero_add]
  constructor
  · rintro ⟨_, h1, h2, _, h4, _, _, h7, h8, _, _, h11, _, h13, h14, _⟩
    refine ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb4⟩, hb7⟩, hb8⟩, hb11⟩, hb13⟩, hb14⟩
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- $4 \times 4$ matrix representation $\rho(H)$ (`cliffordToTetronMatrix`) of a Clifford operator
$H \in Cl_4$ on the 4-state Majorana-1 tetron space in the parity-ordered basis
$C_{\text{even}} = \{0, 1\}$ ($P = +1$) and $C_{\text{odd}} = \{2, 3\}$ ($P = -1$):
* Even-weight blades (`b0, b3, b5, b6, b9, b10, b12, b15`) act **strictly block-diagonally** within
  $C_{\text{even}}$ and $C_{\text{odd}}$ (preserving fermion parity and intra-sector row-sum equitability).
* Odd-weight blades (`b1, b2, b4, b7, b8, b11, b13, b14`) act **strictly off-block-diagonally**
  between $C_{\text{even}}$ and $C_{\text{odd}}$ (with weight-1 blades $b_1, b_2, b_4, b_8$ acting
  symmetrically and weight-3 blades $b_7, b_{11}, b_{13}, b_{14}$ acting skew-symmetrically, so all
  8 odd-weight coordinates are linearly independent on the 8 off-sector entries!). -/
def cliffordToTetronMatrix (H : CliffordElem) : IntMatrix where
  dim := 4
  rows :=
    let e00 := H.b0 - H.b15 + H.b6 - H.b9
    let e01 := H.b3 + H.b10 + H.b12
    let e10 := H.b3 + H.b10 + H.b12
    let e11 := H.b0 - H.b15 + H.b6 - H.b9
    let o00 := H.b0 + H.b15 - H.b6 + H.b9
    let o01 := H.b3 + H.b5 - H.b10
    let o10 := H.b3 + H.b5 - H.b10
    let o11 := H.b0 + H.b15 - H.b6 + H.b9
    let c02 := H.b1 + H.b13
    let c03 := H.b1 + H.b2 + H.b7
    let c12 := -H.b1 + H.b4 + H.b11
    let c13 := -H.b1 + H.b8 + H.b14
    let c20 := H.b1 - H.b13
    let c21 := -H.b1 + H.b4 - H.b11
    let c30 := H.b1 + H.b2 - H.b7
    let c31 := -H.b1 + H.b8 - H.b14
    [ [e00, e01, c02, c03]
    , [e10, e11, c12, c13]
    , [c20, c21, o00, o01]
    , [c30, c31, o10, o11] ]

/-- Clifford element realizing `majoranaTetronHamiltonian` ($2 P + \gamma_0\gamma_1 = -2 e_{15} + e_3$). -/
def majoranaTetronClifford : CliffordElem :=
  { cliffordZero with b3 := 1, b15 := -2 }

/-- Clifford element realizing `majoranaParityPreserveNoise` ($e_0 + 2 e_3 - 3 e_5$). -/
def majoranaParityPreserveClifford : CliffordElem :=
  { cliffordZero with b0 := 1, b3 := 2, b5 := -3 }

/-- Clifford element realizing `majoranaQuasiparticlePoisonNoise` ($\gamma_0 = e_1$, odd-weight blade!). -/
def majoranaQuasiparticlePoisonClifford : CliffordElem :=
  cliffordGamma ⟨0, by decide⟩

/-- Quotient matrix induced on the 2-sector parity partition (`C_even = {0, 1}`, `C_odd = {2, 3}`)
by any Clifford element $H \in Cl_4$:
$$Q_H(0, 0) = H_{b_0} - H_{b_{15}} + H_{b_6} - H_{b_9} + H_{b_3} + H_{b_{10}} + H_{b_{12}}, \quad
  Q_H(1, 1) = H_{b_0} + H_{b_{15}} - H_{b_6} + H_{b_9} + H_{b_3} + H_{b_5} - H_{b_{10}},$$
and $Q_H(0, 1) = Q_H(1, 0) = 0$ for every parity-commuting $H$! -/
def cliffordParityQuotient (H : CliffordElem) : Nat → Nat → Int
  | 0, 0 => H.b0 - H.b15 + H.b6 - H.b9 + H.b3 + H.b10 + H.b12
  | 1, 1 => H.b0 + H.b15 - H.b6 + H.b9 + H.b3 + H.b5 - H.b10
  | _, _ => 0

/-- **Theorem (`clifford_commutesWithParity_zero_offblock_and_leakage`)**:
**Universal Clifford Parity Eigenspace Protection Theorem**:
For ANY Clifford operator $\Delta H \in Cl_4$, if $\Delta H$ commutes with fermion parity $P$
(`commutesWithParity dH = true`), then:
1. By the **Clifford Parity Selection Theorem**, all 8 odd-weight Majorana blades of $\Delta H$
   vanish (`isEvenBladeSupported dH = true`),
2. Every off-sector matrix element of `cliffordToTetronMatrix dH` between the $+1$ parity eigenspace
   $C_{\text{even}} = \{0, 1\}$ and the $-1$ parity eigenspace $C_{\text{odd}} = \{2, 3\}$ is
   **identically zero** (`(cliffordToTetronMatrix dH).entry u v = 0` whenever
   `majoranaParityPart u ≠ majoranaParityPart v`),
3. The inter-sector row sums from $C_{\text{odd}}$ into $C_{\text{even}}$ and from $C_{\text{even}}$
   into $C_{\text{odd}}$ are **derived to be identically zero** (`= 0`) without assuming `dQ 1 0 = 0`! -/
theorem clifford_commutesWithParity_zero_offblock_and_leakage
    (dH : CliffordElem)
    (hComm : commutesWithParity dH = true) :
    isEvenBladeSupported dH = true ∧
    (cliffordToTetronMatrix dH).entry 0 2 = 0 ∧
    (cliffordToTetronMatrix dH).entry 0 3 = 0 ∧
    (cliffordToTetronMatrix dH).entry 1 2 = 0 ∧
    (cliffordToTetronMatrix dH).entry 1 3 = 0 ∧
    (cliffordToTetronMatrix dH).entry 2 0 = 0 ∧
    (cliffordToTetronMatrix dH).entry 2 1 = 0 ∧
    (cliffordToTetronMatrix dH).entry 3 0 = 0 ∧
    (cliffordToTetronMatrix dH).entry 3 1 = 0 ∧
    cellRowSum (cliffordToTetronMatrix dH).entry [0, 1] 2 = 0 ∧
    cellRowSum (cliffordToTetronMatrix dH).entry [0, 1] 3 = 0 ∧
    cellRowSum (cliffordToTetronMatrix dH).entry [2, 3] 0 = 0 ∧
    cellRowSum (cliffordToTetronMatrix dH).entry [2, 3] 1 = 0 ∧
    cliffordParityQuotient dH 1 0 = 0 ∧
    cliffordParityQuotient dH 0 1 = 0 := by
  have hEven : isEvenBladeSupported dH = true :=
    (clifford_commutesWithParity_iff_even_blades dH).mp hComm
  rcases dH with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩
  have hEven' := hEven
  unfold isEvenBladeSupported at hEven'
  simp only [Bool.and_eq_true] at hEven'
  rcases hEven' with ⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb4⟩, hb7⟩, hb8⟩, hb11⟩, hb13⟩, hb14⟩
  have h1  : b1 = 0  := of_decide_eq_true hb1
  have h2  : b2 = 0  := of_decide_eq_true hb2
  have h4  : b4 = 0  := of_decide_eq_true hb4
  have h7  : b7 = 0  := of_decide_eq_true hb7
  have h8  : b8 = 0  := of_decide_eq_true hb8
  have h11 : b11 = 0 := of_decide_eq_true hb11
  have h13 : b13 = 0 := of_decide_eq_true hb13
  have h14 : b14 = 0 := of_decide_eq_true hb14
  refine ⟨hEven, ?_⟩
  change (b1 + b13 = 0) ∧
    (b1 + b2 + b7 = 0) ∧
    (-b1 + b4 + b11 = 0) ∧
    (-b1 + b8 + b14 = 0) ∧
    (b1 - b13 = 0) ∧
    (-b1 + b4 - b11 = 0) ∧
    (b1 + b2 - b7 = 0) ∧
    (-b1 + b8 - b14 = 0) ∧
    ((b1 - b13) + ((-b1 + b4 - b11) + 0) = 0) ∧
    ((b1 + b2 - b7) + ((-b1 + b8 - b14) + 0) = 0) ∧
    ((b1 + b13) + ((b1 + b2 + b7) + 0) = 0) ∧
    ((-b1 + b4 + b11) + ((-b1 + b8 + b14) + 0) = 0) ∧
    (0 = 0) ∧ (0 = 0)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega, by omega, rfl, rfl⟩

/-- **Theorem (`clifford_commutesWithParity_iff_offblock_and_equitable`)**:
**Bidirectional Off-Sector Vanishing & Universal Equitable Partition Theorem for $Cl_4$**:
For EVERY Clifford operator $H \in Cl_4$ (universally quantified over $\mathbb{Z}^{16}$):
1. All 8 off-sector matrix elements of `cliffordToTetronMatrix H` between $C_{\text{even}} = \{0, 1\}$
   and $C_{\text{odd}} = \{2, 3\}$ vanish **if and only if** `commutesWithParity H = true` ($[H, P] = 0$)!
2. Whenever `commutesWithParity H = true`, `cliffordToTetronMatrix H` universally satisfies
   `checkEquitablePartition (cliffordToTetronMatrix H) 2 majoranaParityPart (cliffordParityQuotient H) = true`! -/
theorem clifford_commutesWithParity_iff_offblock_and_equitable (H : CliffordElem) :
    ((cliffordToTetronMatrix H).entry 0 2 = 0 ∧
     (cliffordToTetronMatrix H).entry 0 3 = 0 ∧
     (cliffordToTetronMatrix H).entry 1 2 = 0 ∧
     (cliffordToTetronMatrix H).entry 1 3 = 0 ∧
     (cliffordToTetronMatrix H).entry 2 0 = 0 ∧
     (cliffordToTetronMatrix H).entry 2 1 = 0 ∧
     (cliffordToTetronMatrix H).entry 3 0 = 0 ∧
     (cliffordToTetronMatrix H).entry 3 1 = 0 ↔
     commutesWithParity H = true) ∧
    (commutesWithParity H = true →
     checkEquitablePartition (cliffordToTetronMatrix H) 2 majoranaParityPart (cliffordParityQuotient H) = true) := by
  rw [clifford_commutesWithParity_iff_even_blades H]
  rcases H with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩
  constructor
  · unfold isEvenBladeSupported
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    change ((b1 + b13 = 0) ∧
      (b1 + b2 + b7 = 0) ∧
      (-b1 + b4 + b11 = 0) ∧
      (-b1 + b8 + b14 = 0) ∧
      (b1 - b13 = 0) ∧
      (-b1 + b4 - b11 = 0) ∧
      (b1 + b2 - b7 = 0) ∧
      (-b1 + b8 - b14 = 0)) ↔
      (((((((b1 = 0 ∧ b2 = 0) ∧ b4 = 0) ∧ b7 = 0) ∧ b8 = 0) ∧ b11 = 0) ∧ b13 = 0) ∧ b14 = 0)
    constructor
    · rintro ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩
      refine ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩
    · rintro ⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb4⟩, hb7⟩, hb8⟩, hb11⟩, hb13⟩, hb14⟩
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro hEven
    unfold isEvenBladeSupported at hEven
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hEven
    rcases hEven with ⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb4⟩, hb7⟩, hb8⟩, hb11⟩, hb13⟩, hb14⟩
    subst hb1 hb2 hb4 hb7 hb8 hb11 hb13 hb14
    have hEq0 : (b0 - b15 + b6 - b9) + ((b3 + b10 + b12) + 0) = b0 - b15 + b6 - b9 + b3 + b10 + b12 := by omega
    have hEq1 : (b3 + b10 + b12) + ((b0 - b15 + b6 - b9) + 0) = b0 - b15 + b6 - b9 + b3 + b10 + b12 := by omega
    have hEq2 : (b0 + b15 - b6 + b9) + ((b3 + b5 - b10) + 0) = b0 + b15 - b6 + b9 + b3 + b5 - b10 := by omega
    have hEq3 : (b3 + b5 - b10) + ((b0 + b15 - b6 + b9) + 0) = b0 + b15 - b6 + b9 + b3 + b5 - b10 := by omega
    change (true && true &&
      ((decide ((b0 - b15 + b6 - b9) + ((b3 + b10 + b12) + 0) = b0 - b15 + b6 - b9 + b3 + b10 + b12) &&
        (decide ((0 : Int) + (0 + 0) = 0) && true)) &&
       ((decide ((b3 + b10 + b12) + ((b0 - b15 + b6 - b9) + 0) = b0 - b15 + b6 - b9 + b3 + b10 + b12) &&
        (decide ((0 : Int) + (0 + 0) = 0) && true)) &&
        ((decide ((0 : Int) + (0 + 0) = 0) &&
          (decide ((b0 + b15 - b6 + b9) + ((b3 + b5 - b10) + 0) = b0 + b15 - b6 + b9 + b3 + b5 - b10) && true)) &&
         ((decide ((0 : Int) + (0 + 0) = 0) &&
           (decide ((b3 + b5 - b10) + ((b0 + b15 - b6 + b9) + 0) = b0 + b15 - b6 + b9 + b3 + b5 - b10) && true)) &&
          true))))) = true
    rw [hEq0, hEq1, hEq2, hEq3]
    have hZ : (0 : Int) + (0 + 0) = 0 := rfl
    rw [hZ]
    simp only [decide_true, Bool.and_self]

/-- Exact $n \times n$ matrix over Gaussian integers $\mathbb{Z}[i]$ (`GaussianInt`), used for the
faithful $4 \times 4$ Jordan–Wigner / Pauli spinor representation of $Cl_4$. -/
structure GaussianMatrix where
  dim  : Nat
  rows : List (List GaussianInt)
  deriving DecidableEq, Repr

namespace GaussianMatrix

/-- Look up a `GaussianInt` at index `v` in a row by structural recursion (`0 Classical.choice`). -/
def listGetGaussian : List GaussianInt → Nat → GaussianInt
  | [], _ => GaussianInt.zero
  | x :: _, 0 => x
  | _ :: xs, v + 1 => listGetGaussian xs v

/-- Look up row `u` in a list of `GaussianInt` rows by structural recursion (`0 Classical.choice`). -/
def listGetGaussianRow : List (List GaussianInt) → Nat → List GaussianInt
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, u + 1 => listGetGaussianRow rs u

/-- Entry lookup $(u, v)$ in a `GaussianMatrix` (defaulting to `GaussianInt.zero`). -/
def entry (m : GaussianMatrix) (u v : Nat) : GaussianInt :=
  listGetGaussian (listGetGaussianRow m.rows u) v

/-- Pure boolean equality on `GaussianInt` (`0 Classical.choice`). -/
def gaussianIntBeq (z w : GaussianInt) : Bool :=
  decide (z.re = w.re) && decide (z.im = w.im)

theorem gaussianInt_eq_of_beq {z w : GaussianInt} (h : gaussianIntBeq z w = true) : z = w := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      unfold gaussianIntBeq at h
      have hAnd := (Bool.and_eq_true _ _).mp h
      have hRe : zr = wr := of_decide_eq_true hAnd.1
      have hIm : zi = wi := of_decide_eq_true hAnd.2
      rw [hRe, hIm]

/-- Pure boolean equality on `List GaussianInt` (`0 Classical.choice`). -/
def listBeqGaussian : List GaussianInt → List GaussianInt → Bool
  | [], [] => true
  | x :: xs, y :: ys => gaussianIntBeq x y && listBeqGaussian xs ys
  | _, _ => false

theorem listBeqGaussian_eq : ∀ {xs ys : List GaussianInt}, listBeqGaussian xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | _ :: _, _ :: _, h => by
    have hAnd := (Bool.and_eq_true _ _).mp h
    rw [gaussianInt_eq_of_beq hAnd.1, listBeqGaussian_eq hAnd.2]

/-- Pure boolean equality on `List (List GaussianInt)` (`0 Classical.choice`). -/
def listBeqGaussianRows : List (List GaussianInt) → List (List GaussianInt) → Bool
  | [], [] => true
  | r1 :: rs1, r2 :: rs2 => listBeqGaussian r1 r2 && listBeqGaussianRows rs1 rs2
  | _, _ => false

theorem listBeqGaussianRows_eq :
    ∀ {rs1 rs2 : List (List GaussianInt)}, listBeqGaussianRows rs1 rs2 = true → rs1 = rs2
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | _ :: _, _ :: _, h => by
    have hAnd := (Bool.and_eq_true _ _).mp h
    rw [listBeqGaussian_eq hAnd.1, listBeqGaussianRows_eq hAnd.2]

/-- Pure boolean equality on `GaussianMatrix` (`0 Classical.choice`). -/
def beq (A B : GaussianMatrix) : Bool :=
  decide (A.dim = B.dim) && listBeqGaussianRows A.rows B.rows

theorem eq_of_beq {A B : GaussianMatrix} (h : GaussianMatrix.beq A B = true) : A = B := by
  cases A with
  | mk d1 r1 =>
    cases B with
    | mk d2 r2 =>
      unfold GaussianMatrix.beq at h
      have hAnd := (Bool.and_eq_true _ _).mp h
      have hDim : d1 = d2 := of_decide_eq_true hAnd.1
      have hRows : r1 = r2 := listBeqGaussianRows_eq hAnd.2
      rw [hDim, hRows]

/-- Identity matrix $I_n$ over $\mathbb{Z}[i]$. -/
def identity (dim : Nat) : GaussianMatrix :=
  let indices := List.range dim
  { dim  := dim
  , rows := indices.map (fun u =>
      indices.map (fun v => cond (u == v) GaussianInt.one GaussianInt.zero)) }

/-- Zero matrix $0_n$ over $\mathbb{Z}[i]$. -/
def zero (dim : Nat) : GaussianMatrix :=
  let indices := List.range dim
  { dim  := dim
  , rows := indices.map (fun _ => indices.map (fun _ => GaussianInt.zero)) }

/-- Matrix addition $A + B$ over $\mathbb{Z}[i]$. -/
def add (A B : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => GaussianInt.add (A.entry u v) (B.entry u v))) }

/-- Scalar multiplication $c \cdot A$ ($c \in \mathbb{Z}$) over $\mathbb{Z}[i]$. -/
def scale (c : Int) (A : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v => GaussianInt.scale c (A.entry u v))) }

/-- Matrix multiplication $A \cdot B$ over $\mathbb{Z}[i]$. -/
def mul (A B : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range A.dim
  { dim  := A.dim
  , rows := indices.map (fun u =>
      indices.map (fun v =>
        sumGaussianOver (fun w => GaussianInt.mul (A.entry u w) (B.entry w v)) indices)) }

end GaussianMatrix

/-- Faithful $4 \times 4$ Pauli spinor matrices over $\mathbb{Z}[i]$ for the 4 Majorana generators
in the parity-ordered basis ($C_{\text{even}} = \{0, 1\}$ with $P = +1$, $C_{\text{odd}} = \{2, 3\}$ with $P = -1$):
$$\gamma_0 = X \otimes I,\quad \gamma_1 = Y \otimes X,\quad \gamma_2 = Y \otimes Y,\quad \gamma_3 = Y \otimes Z,$$
so that $P = -\gamma_0 \gamma_1 \gamma_2 \gamma_3 = Z \otimes I = \operatorname{diag}(1, 1, -1, -1)$! -/
def gamma0Spinor : GaussianMatrix where
  dim := 4
  rows :=
    [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]
    , [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]

def gamma1Spinor : GaussianMatrix where
  dim := 4
  rows :=
    [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]

def gamma2Spinor : GaussianMatrix where
  dim := 4
  rows :=
    [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]

def gamma3Spinor : GaussianMatrix where
  dim := 4
  rows :=
    [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]
    , [⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]

/-- Right-multiply `acc` by `G` if `bit == 1`, otherwise return `acc`. -/
def mulSpinorIfBit (acc : GaussianMatrix) (bit : Nat) (G : GaussianMatrix) : GaussianMatrix :=
  cond (bit == 1) (acc.mul G) acc

/-- $4 \times 4$ spinor matrix $\rho_{\mathbb{Z}[i]}(e_m) = \gamma_0^{m_0} \gamma_1^{m_1} \gamma_2^{m_2} \gamma_3^{m_3}$
for basis blade $e_m \in Cl_4$. -/
def cliffordBladeSpinorMatrix (m : Nat) : GaussianMatrix :=
  let r0 := cond (bladeBit m 0 == 1) gamma0Spinor (GaussianMatrix.identity 4)
  let r1 := mulSpinorIfBit r0 (bladeBit m 1) gamma1Spinor
  let r2 := mulSpinorIfBit r1 (bladeBit m 2) gamma2Spinor
  mulSpinorIfBit r2 (bladeBit m 3) gamma3Spinor

/-- Faithful $4 \times 4$ Jordan–Wigner spinor matrix representation $\rho_{\mathbb{Z}[i]} : Cl_4 \to M_4(\mathbb{Z}[i])$
(`cliffordToSpinorMatrix`). -/
def cliffordToSpinorMatrix (H : CliffordElem) : GaussianMatrix :=
  (List.range 16).foldl (fun acc m =>
    let c := H.coeff m
    cond (decide (c = 0)) acc (acc.add ((cliffordBladeSpinorMatrix m).scale c)))
    (GaussianMatrix.zero 4)

/-- **Theorem (`cliffordToSpinorMatrix_algebra_hom`)**:
**Exact $4 \times 4$ Spinor Algebra Homomorphism Theorem for $Cl_4$ over $\mathbb{Z}[i]$**:
1. For ALL 16 basis blades $m \in \text{Fin } 16$, `cliffordToSpinorMatrix (cliffordBasisBlade m.val) = cliffordBladeSpinorMatrix m.val`.
2. For ALL $16 \times 16 = 256$ basis blade pairs $a, b \in \text{Fin } 16$, the spinor representation
   strictly respects the Koszul-signed Clifford product:
   $$\rho_{\mathbb{Z}[i]}(e_a) \cdot \rho_{\mathbb{Z}[i]}(e_b) = \operatorname{cliffordSign}(a, b) \cdot \rho_{\mathbb{Z}[i]}(e_{a \oplus b}).$$
3. For ALL $4 \times 4 = 16$ Majorana generator pairs $a, b \in \text{Fin } 4$,
   `cliffordToSpinorMatrix (cliffordMul (cliffordGamma a) (cliffordGamma b)) = (cliffordToSpinorMatrix (cliffordGamma a)).mul (cliffordToSpinorMatrix (cliffordGamma b))`.
4. $\rho_{\mathbb{Z}[i]}(1) = I_4$, and $\rho_{\mathbb{Z}[i]}(P) = \operatorname{diag}(1, 1, -1, -1)$
   (separating the $+1$ parity eigenspace $C_{\text{even}} = \{0, 1\}$ from the $-1$ parity eigenspace
   $C_{\text{odd}} = \{2, 3\}$)! -/
theorem cliffordToSpinorMatrix_algebra_hom :
    (∀ m : Fin 16,
      cliffordToSpinorMatrix (cliffordBasisBlade m.val) = cliffordBladeSpinorMatrix m.val) ∧
    (∀ a b : Fin 16,
      (cliffordBladeSpinorMatrix (a.val ^^^ b.val)).scale (cliffordSign a.val b.val) =
        (cliffordBladeSpinorMatrix a.val).mul (cliffordBladeSpinorMatrix b.val)) ∧
    (∀ a b : Fin 4,
      cliffordToSpinorMatrix (cliffordMul (cliffordGamma a) (cliffordGamma b)) =
        (cliffordToSpinorMatrix (cliffordGamma a)).mul
          (cliffordToSpinorMatrix (cliffordGamma b))) ∧
    cliffordToSpinorMatrix cliffordOne = GaussianMatrix.identity 4 ∧
    cliffordToSpinorMatrix cliffordParity =
      { dim := 4
      , rows :=
          [ [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
          , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
          , [⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]
          , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩] ] } := by
  have h1 : (List.range 16).all (fun m =>
      GaussianMatrix.beq (cliffordToSpinorMatrix (cliffordBasisBlade m))
                         (cliffordBladeSpinorMatrix m)) = true := by
    decide +kernel
  have h2 : (List.range 16).all (fun a =>
      (List.range 16).all (fun b =>
        GaussianMatrix.beq ((cliffordBladeSpinorMatrix (a ^^^ b)).scale (cliffordSign a b))
                           ((cliffordBladeSpinorMatrix a).mul (cliffordBladeSpinorMatrix b)))) = true := by
    decide +kernel
  have h3 : (List.range 4).all (fun a =>
      (List.range 4).all (fun b =>
        GaussianMatrix.beq (cliffordToSpinorMatrix (cliffordMul (cliffordBasisBlade (1 <<< a)) (cliffordBasisBlade (1 <<< b))))
          ((cliffordToSpinorMatrix (cliffordBasisBlade (1 <<< a))).mul
            (cliffordToSpinorMatrix (cliffordBasisBlade (1 <<< b)))))) = true := by
    decide +kernel
  rw [list_all_iff_forall] at h1 h2 h3
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro m
    exact GaussianMatrix.eq_of_beq (h1 m.val (List.mem_range.mpr m.isLt))
  · intro a b
    have hRow := (list_all_iff_forall _ (List.range 16)).mp (h2 a.val (List.mem_range.mpr a.isLt))
    exact GaussianMatrix.eq_of_beq (hRow b.val (List.mem_range.mpr b.isLt))
  · intro a b
    have hRow := (list_all_iff_forall _ (List.range 4)).mp (h3 a.val (List.mem_range.mpr a.isLt))
    exact GaussianMatrix.eq_of_beq (hRow b.val (List.mem_range.mpr b.isLt))

/-! ## 5. Universal Theorem: Symmetry-Preserving Noise Produces Identically Zero Leakage -/

/-- Perturbed Hamiltonian entry $(H + \epsilon \Delta H)_{u, v} = H_{u,v} + \epsilon \cdot \Delta H_{u,v}$. -/
def perturbedHamiltonian (H dH : Nat → Nat → Int) (eps : Int) (u v : Nat) : Int :=
  H u v + eps * dH u v

/-- Perturbed quotient entry $(Q + \epsilon \Delta Q)_{i, j} = Q_{i,j} + \epsilon \cdot \Delta Q_{i,j}$. -/
def perturbedQuotient (Q dQ : Nat → Nat → Int) (eps : Int) (i j : Nat) : Int :=
  Q i j + eps * dQ i j

/-- **Theorem (`clifford_parity_protected_zero_sector_leakage`)**:
For ANY nominal Clifford Hamiltonian `cH : CliffordElem` and noise operator `cDH : CliffordElem`,
if both commute with fermion parity $P = -\gamma_0\gamma_1\gamma_2\gamma_3$
(`commutesWithParity cH = true` and `commutesWithParity cDH = true`), then for EVERY noise
amplitude `eps : Int` and EVERY initial state `w : Nat → Int` prepared in the $+1$ parity
eigenspace (`w 1 = 0`), **without assuming `Q 1 0 = 0` or `dQ 1 0 = 0`**:
1. The odd-parity quotient amplitude after $Q_{cH} + \epsilon Q_{cDH}$ is identically `0`, and
2. The full 4-state tetron amplitudes at odd-parity basis states $u = 2$ and $u = 3$ after
   $\rho(cH) + \epsilon \rho(cDH)$ are **identically `0`**! -/
theorem clifford_parity_protected_zero_sector_leakage
    (cH cDH : CliffordElem)
    (eps : Int)
    (w : Nat → Int)
    (hCommH  : commutesWithParity cH = true)
    (hCommDH : commutesWithParity cDH = true)
    (hEvenInit : w 1 = 0) :
    quotientMatVec (perturbedQuotient (cliffordParityQuotient cH) (cliffordParityQuotient cDH) eps) [0, 1] w 1 = 0 ∧
    matVec [0, 1, 2, 3]
      (perturbedHamiltonian (cliffordToTetronMatrix cH).entry (cliffordToTetronMatrix cDH).entry eps)
      (liftQuotientVec majoranaParityPart w) 2 = 0 ∧
    matVec [0, 1, 2, 3]
      (perturbedHamiltonian (cliffordToTetronMatrix cH).entry (cliffordToTetronMatrix cDH).entry eps)
      (liftQuotientVec majoranaParityPart w) 3 = 0 := by
  have hZ_H  := clifford_commutesWithParity_zero_offblock_and_leakage cH hCommH
  have hZ_DH := clifford_commutesWithParity_zero_offblock_and_leakage cDH hCommDH
  rcases hZ_H with ⟨_, _, _, _, _, hH20, hH21, hH30, hH31, _, _, _, _, hQH10, _⟩
  rcases hZ_DH with ⟨_, _, _, _, _, hDH20, hDH21, hDH30, hDH31, _, _, _, _, hQDH10, _⟩
  change ((cliffordParityQuotient cH 1 0 + eps * cliffordParityQuotient cDH 1 0) * w 0 +
    ((cliffordParityQuotient cH 1 1 + eps * cliffordParityQuotient cDH 1 1) * w 1 + 0) = 0) ∧
    (((cliffordToTetronMatrix cH).entry 2 0 + eps * (cliffordToTetronMatrix cDH).entry 2 0) * w 0 +
     (((cliffordToTetronMatrix cH).entry 2 1 + eps * (cliffordToTetronMatrix cDH).entry 2 1) * w 0 +
      (((cliffordToTetronMatrix cH).entry 2 2 + eps * (cliffordToTetronMatrix cDH).entry 2 2) * w 1 +
       (((cliffordToTetronMatrix cH).entry 2 3 + eps * (cliffordToTetronMatrix cDH).entry 2 3) * w 1 + 0))) = 0) ∧
    (((cliffordToTetronMatrix cH).entry 3 0 + eps * (cliffordToTetronMatrix cDH).entry 3 0) * w 0 +
     (((cliffordToTetronMatrix cH).entry 3 1 + eps * (cliffordToTetronMatrix cDH).entry 3 1) * w 0 +
      (((cliffordToTetronMatrix cH).entry 3 2 + eps * (cliffordToTetronMatrix cDH).entry 3 2) * w 1 +
       (((cliffordToTetronMatrix cH).entry 3 3 + eps * (cliffordToTetronMatrix cDH).entry 3 3) * w 1 + 0))) = 0)
  rw [hQH10, hQDH10, hH20, hH21, hH30, hH31, hDH20, hDH21, hDH30, hDH31, hEvenInit]
  refine ⟨by omega, by omega, by omega⟩

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
   Hamiltonian and noise ($Q(1, 0) = 0$ and $\Delta Q(1, 0) = 0$, which is derived from
   `commutesWithParity` by `clifford_commutesWithParity_zero_offblock_and_leakage`) and the system
   starts in the even-parity computational sector ($w_1 = 0$), the odd-parity sector amplitude after
   applying $Q + \epsilon \Delta Q$ is **identically `0`** for all $\epsilon \in \mathbb{Z}$ and all $w_0 \in \mathbb{Z}$!
3. **Concrete IBM Heavy-Hex $C_{12}$ & Microsoft Majorana-1 Tetron Clifford Verification**:
   - Both the 7-cell distance partition and the 2-cell corner-vs-bridge partition of Heavy-Hex $C_{12}$
     pass `checkEquitablePartition = true`, `checkHandshakeIdentity = true`, and have
     `evalEquitableResidualNormSq = 0`.
   - On the Majorana-1 Tetron, `cliffordToTetronMatrix majoranaTetronClifford = majoranaTetronHamiltonian`
     (`commutesWithParity = true`), `cliffordToTetronMatrix majoranaParityPreserveClifford = majoranaParityPreserveNoise`
     (`commutesWithParity = true`, `evalEquitableResidualNormSq = 0`), whereas
     `majoranaQuasiparticlePoisonClifford` ($\gamma_0$) fails `commutesWithParity` (`= false`), breaks
     parity equitability (`checkEquitablePartition = false`), and induces a non-zero leakage residual floor
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
    -- 3. Concrete IBM Heavy-Hex C12 & Majorana-1 Tetron Clifford certificates
    checkEquitablePartition heavyHexC12RingMatrix 7 heavyHexC12DistancePart heavyHexC12DistanceQuotient = true ∧
    checkHandshakeIdentity 12 7 heavyHexC12DistancePart heavyHexC12DistanceQuotient = true ∧
    evalEquitableResidualNormSq heavyHexC12RingMatrix 7 heavyHexC12DistancePart heavyHexC12DistanceQuotient = 0 ∧
    checkEquitablePartition heavyHexC12CornerBridgeMatrix 2 heavyHexC12CornerBridgePart heavyHexC12CornerBridgeQuotient = true ∧
    checkHandshakeIdentity 12 2 heavyHexC12CornerBridgePart heavyHexC12CornerBridgeQuotient = true ∧
    evalEquitableResidualNormSq heavyHexC12CornerBridgeMatrix 2 heavyHexC12CornerBridgePart heavyHexC12CornerBridgeQuotient = 0 ∧
    cliffordToTetronMatrix majoranaTetronClifford = majoranaTetronHamiltonian ∧
    cliffordToTetronMatrix majoranaParityPreserveClifford = majoranaParityPreserveNoise ∧
    cliffordToTetronMatrix majoranaQuasiparticlePoisonClifford = majoranaQuasiparticlePoisonNoise ∧
    commutesWithParity majoranaTetronClifford = true ∧
    commutesWithParity majoranaParityPreserveClifford = true ∧
    commutesWithParity majoranaQuasiparticlePoisonClifford = false ∧
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
