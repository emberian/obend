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
public import Obend.Hardware.OpenHypergraph
public import Obend.Leaf.Specialize
public import Obend.Analysis.Equitable
public import Obend.Analysis.QuantumWalk
@[expose] public section

namespace Obend.Hardware.QuantumMatter
open Obend.Hardware.Photonics
open Obend.Hardware.OpenHypergraph
open Obend.Leaf
open Obend.Slot
open Obend.Slot.World
open Obend.Core.Term
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
$$\Delta H_{\text{sym}} = \begin{pmatrix} 1 & 2 & 0 & 0 \\ 2 & 1 & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \end{pmatrix}.$$ -/
def majoranaParityPreserveNoise : IntMatrix where
  dim  := 4
  rows :=
    [ [1, 2, 0, 0]
    , [2, 1, 0, 0]
    , [0, 0, 1, 0]
    , [0, 0, 0, 1] ]

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
$\Delta Q_{\text{sym}} = \begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def majoranaNoiseSymQuotient : Nat → Nat → Int
  | 0, 0 => 3
  | 1, 1 => 1
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

/-- Rank-16 bijective $4 \times 4$ Pauli-block matrix representation $\rho(H)$ (`cliffordToTetronMatrix`)
of a Clifford operator $H \in Cl_4$ on the 4-state Majorana-1 tetron space in the parity-ordered basis
$C_{\text{even}} = \{0, 1\}$ ($P = +1$) and $C_{\text{odd}} = \{2, 3\}$ ($P = -1$):
* Even-weight blades (`b0, b3, b5, b6, b9, b10, b12, b15`) act **strictly block-diagonally** as full
  $2 \times 2$ Pauli spinor blocks ($I_L, Z_L, X_L, i Y_L$) within $C_{\text{even}}$ and $C_{\text{odd}}$,
  preserving all 8 even blades with $e_{00} \neq e_{11}$ whenever $Z_L \neq 0$ (`b6 ≠ b9`)!
* Odd-weight blades (`b1, b2, b4, b7, b8, b11, b13, b14`) act **strictly off-block-diagonally**
  between $C_{\text{even}}$ and $C_{\text{odd}}$, so all 16 Clifford blades are linearly independent
  (`cliffordToTetronMatrix H = IntMatrix.zero 4 ↔ H = cliffordZero`). -/
def cliffordToTetronMatrix (H : CliffordElem) : IntMatrix where
  dim := 4
  rows :=
    let e00 := (H.b0 - H.b15) + (H.b6 - H.b9)
    let e01 := (H.b3 + H.b12) + (H.b5 + H.b10)
    let e10 := (H.b3 + H.b12) - (H.b5 + H.b10)
    let e11 := (H.b0 - H.b15) - (H.b6 - H.b9)
    let o00 := (H.b0 + H.b15) + (H.b6 + H.b9)
    let o01 := (H.b3 - H.b12) + (H.b5 - H.b10)
    let o10 := (H.b3 - H.b12) - (H.b5 - H.b10)
    let o11 := (H.b0 + H.b15) - (H.b6 + H.b9)
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

/-- Clifford element realizing `majoranaParityPreserveNoise` ($e_0 + e_3 + e_{12}$). -/
def majoranaParityPreserveClifford : CliffordElem :=
  { cliffordZero with b0 := 1, b3 := 1, b12 := 1 }

/-- Clifford element realizing `majoranaQuasiparticlePoisonNoise` ($\gamma_0 = e_1$, odd-weight blade!). -/
def majoranaQuasiparticlePoisonClifford : CliffordElem :=
  cliffordGamma ⟨0, by decide⟩

/-- $2 \times 2$ Pauli spinor block quotient induced on the 2-sector parity partition
(`C_even = {0, 1}`, `C_odd = {2, 3}`) by any Clifford element $H \in Cl_4$:
* `cliffordParityQuotient H 0 0` is the $2 \times 2$ logical qubit Pauli block on $C_{\text{even}}$,
* `cliffordParityQuotient H 1 1` is the $2 \times 2$ poisoned Pauli block on $C_{\text{odd}}$,
* `cliffordParityQuotient H 0 1 = cliffordParityQuotient H 1 0 = IntMatrix.zero 2`. -/
def cliffordParityQuotient (H : CliffordElem) : Nat → Nat → IntMatrix
  | 0, 0 => extractCellBlock (cliffordToTetronMatrix H) 2 0 0
  | 1, 1 => extractCellBlock (cliffordToTetronMatrix H) 2 1 1
  | _, _ => IntMatrix.zero 2

/-- **Theorem (`clifford_commutesWithParity_zero_offblock_and_leakage`)**:
**Universal Clifford Parity Eigenspace Protection Theorem**:
For ANY Clifford operator $\Delta H \in Cl_4$, if $\Delta H$ commutes with fermion parity $P$
(`commutesWithParity dH = true`), then:
1. By the **Clifford Parity Selection Theorem**, all 8 odd-weight Majorana blades of $\Delta H$
   vanish (`isEvenBladeSupported dH = true`),
2. Every off-sector matrix element of `cliffordToTetronMatrix dH` between the $+1$ parity eigenspace
   $C_{\text{even}} = \{0, 1\}$ and the $-1$ parity eigenspace $C_{\text{odd}} = \{2, 3\}$ is
   **identically zero** (`extractCellBlock (cliffordToTetronMatrix dH) 2 0 1 = IntMatrix.zero 2` and
   `extractCellBlock (cliffordToTetronMatrix dH) 2 1 0 = IntMatrix.zero 2`),
3. The inter-sector row sums from $C_{\text{odd}}$ into $C_{\text{even}}$ and from $C_{\text{even}}$
   into $C_{\text{odd}}$ are **derived to be identically zero** (`= 0`)! -/
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
    cliffordParityQuotient dH 1 0 = IntMatrix.zero 2 ∧
    cliffordParityQuotient dH 0 1 = IntMatrix.zero 2 := by
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
    (IntMatrix.zero 2 = IntMatrix.zero 2) ∧ (IntMatrix.zero 2 = IntMatrix.zero 2)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega, by omega, rfl, rfl⟩

/-- **Theorem (`clifford_commutesWithParity_iff_offblock_and_equitable`)**:
**Bidirectional $2 \times 2$ Block Off-Sector Vanishing, Block-Equitable Partition & 16D Injectivity Theorem for $Cl_4$**:
For EVERY Clifford operator $H \in Cl_4$ (universally quantified over $\mathbb{Z}^{16}$):
1. Both off-diagonal $2 \times 2$ blocks (`extractCellBlock (cliffordToTetronMatrix H) 2 0 1` and
   `extractCellBlock (cliffordToTetronMatrix H) 2 1 0`, i.e., all 8 off-sector entries between
   $C_{\text{even}} = \{0, 1\}$ and $C_{\text{odd}} = \{2, 3\}$) vanish **if and only if**
   `commutesWithParity H = true` ($[H, P] = 0$)!
2. `commutesWithParity H = true` holds **if and only if** `cliffordToTetronMatrix H` satisfies
   `checkBlockEquitablePartition (cliffordToTetronMatrix H) 2 2 majoranaParityPart (cliffordParityQuotient H) = true`
   (full bidirectional `↔` with $2 \times 2$ Pauli spinor blocks)!
3. `cliffordToTetronMatrix H = IntMatrix.zero 4` holds **if and only if** `H = cliffordZero`
   (full 16-dimensional injectivity across all 8 even and 8 odd blades!). -/
private theorem list_range_two : List.range 2 = [0, 1] := rfl
private theorem list_range_four : List.range 4 = [0, 1, 2, 3] := rfl

theorem clifford_commutesWithParity_iff_offblock_and_equitable (H : CliffordElem) :
    ((extractCellBlock (cliffordToTetronMatrix H) 2 0 1 = IntMatrix.zero 2 ∧
      extractCellBlock (cliffordToTetronMatrix H) 2 1 0 = IntMatrix.zero 2) ↔
     commutesWithParity H = true) ∧
    (commutesWithParity H = true ↔
     checkBlockEquitablePartition (cliffordToTetronMatrix H) 2 2 majoranaParityPart (cliffordParityQuotient H) = true) ∧
    (cliffordToTetronMatrix H = IntMatrix.zero 4 ↔ H = cliffordZero) := by
  rw [clifford_commutesWithParity_iff_even_blades H]
  rcases H with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold isEvenBladeSupported
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    change (({ dim := 2, rows := [[b1 + b13, b1 + b2 + b7], [-b1 + b4 + b11, -b1 + b8 + b14]] } : IntMatrix) =
              { dim := 2, rows := [[0, 0], [0, 0]] } ∧
            ({ dim := 2, rows := [[b1 - b13, -b1 + b4 - b11], [b1 + b2 - b7, -b1 + b8 - b14]] } : IntMatrix) =
              { dim := 2, rows := [[0, 0], [0, 0]] }) ↔
      (((((((b1 = 0 ∧ b2 = 0) ∧ b4 = 0) ∧ b7 = 0) ∧ b8 = 0) ∧ b11 = 0) ∧ b13 = 0) ∧ b14 = 0)
    simp only [IntMatrix.mk.injEq, List.cons.injEq, and_true, true_and]
    constructor
    · rintro ⟨⟨⟨h02, h03⟩, ⟨h12, h13⟩⟩, ⟨⟨h20, h21⟩, ⟨h30, h31⟩⟩⟩
      refine ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩
    · rintro ⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb4⟩, hb7⟩, hb8⟩, hb11⟩, hb13⟩, hb14⟩
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩
  · unfold isEvenBladeSupported checkBlockEquitablePartition
    have hDiv42 : (4 : Nat) / 2 = 2 := by decide
    simp [cliffordToTetronMatrix, hDiv42, list_range_two,
      blockCellOf, blockCellMembers, blockCellRowSumEntry,
      cliffordParityQuotient, extractCellBlock, majoranaParityPart,
      IntMatrix.zero, IntMatrix.scaledIdentity, IntMatrix.entry, listGetInt, sumIntOver]
    constructor
    · intro h
      repeat' constructor <;> omega
    · intro h
      repeat' constructor <;> omega
  · rw [CliffordElem.ext_iff]
    change ({ dim := 4
            , rows :=
                [ [(b0 - b15) + (b6 - b9), (b3 + b12) + (b5 + b10), b1 + b13, b1 + b2 + b7]
                , [(b3 + b12) - (b5 + b10), (b0 - b15) - (b6 - b9), -b1 + b4 + b11, -b1 + b8 + b14]
                , [b1 - b13, -b1 + b4 - b11, (b0 + b15) + (b6 + b9), (b3 - b12) + (b5 - b10)]
                , [b1 + b2 - b7, -b1 + b8 - b14, (b3 - b12) - (b5 - b10), (b0 + b15) - (b6 + b9)] ] } : IntMatrix) =
           { dim := 4, rows := [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]] } ↔
      (b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0 ∧ b5 = 0 ∧ b6 = 0 ∧ b7 = 0 ∧
       b8 = 0 ∧ b9 = 0 ∧ b10 = 0 ∧ b11 = 0 ∧ b12 = 0 ∧ b13 = 0 ∧ b14 = 0 ∧ b15 = 0)
    simp only [IntMatrix.mk.injEq, List.cons.injEq, and_true, true_and]
    constructor
    · rintro ⟨⟨e00, e01, c02, c03⟩, ⟨e10, e11, c12, c13⟩, ⟨c20, c21, o00, o01⟩, ⟨c30, c31, o10, o11⟩⟩
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
              by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

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

/-- Perturbed $2 \times 2$ block quotient $(Q + \epsilon \Delta Q)_{i, j} = Q_{i,j} + \epsilon \cdot \Delta Q_{i,j}$. -/
def perturbedBlockQuotient (Q dQ : Nat → Nat → IntMatrix) (eps : Int) (i j : Nat) : IntMatrix :=
  (Q i j).add ((dQ i j).scale eps)

/-- **Theorem (`clifford_parity_protected_zero_sector_leakage`)**:
For ANY nominal Clifford Hamiltonian `cH : CliffordElem` and noise operator `cDH : CliffordElem`,
if both commute with fermion parity $P = -\gamma_0\gamma_1\gamma_2\gamma_3$
(`commutesWithParity cH = true` and `commutesWithParity cDH = true`), then for EVERY noise
amplitude `eps : Int` and EVERY initial state `w : Nat → Int` prepared in the $+1$ parity
eigenspace (`w 1 = 0`), **without assuming `Q 1 0 = 0` or `dQ 1 0 = 0`**:
1. The odd-parity $2 \times 2$ inter-sector block quotient after $Q_{cH} + \epsilon Q_{cDH}$ is identically `IntMatrix.zero 2`, and
2. The full 4-state tetron amplitudes at odd-parity basis states $u = 2$ and $u = 3$ after
   $\rho(cH) + \epsilon \rho(cDH)$ are **identically `0`**! -/
theorem clifford_parity_protected_zero_sector_leakage
    (cH cDH : CliffordElem)
    (eps : Int)
    (w : Nat → Int)
    (hCommH  : commutesWithParity cH = true)
    (hCommDH : commutesWithParity cDH = true)
    (hEvenInit : w 1 = 0) :
    perturbedBlockQuotient (cliffordParityQuotient cH) (cliffordParityQuotient cDH) eps 1 0 = IntMatrix.zero 2 ∧
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
  refine ⟨?_, ?_⟩
  · dsimp only [perturbedBlockQuotient]
    rw [hQH10, hQDH10]
    change ({ dim := 2, rows := [[0 + eps * 0, 0 + eps * 0], [0 + eps * 0, 0 + eps * 0]] } : IntMatrix) =
           { dim := 2, rows := [[0, 0], [0, 0]] }
    simp only [Int.mul_zero, Int.add_zero]
  · change (((cliffordToTetronMatrix cH).entry 2 0 + eps * (cliffordToTetronMatrix cDH).entry 2 0) * w 0 +
      (((cliffordToTetronMatrix cH).entry 2 1 + eps * (cliffordToTetronMatrix cDH).entry 2 1) * w 0 +
       (((cliffordToTetronMatrix cH).entry 2 2 + eps * (cliffordToTetronMatrix cDH).entry 2 2) * w 1 +
        (((cliffordToTetronMatrix cH).entry 2 3 + eps * (cliffordToTetronMatrix cDH).entry 2 3) * w 1 + 0))) = 0) ∧
      (((cliffordToTetronMatrix cH).entry 3 0 + eps * (cliffordToTetronMatrix cDH).entry 3 0) * w 0 +
       (((cliffordToTetronMatrix cH).entry 3 1 + eps * (cliffordToTetronMatrix cDH).entry 3 1) * w 0 +
        (((cliffordToTetronMatrix cH).entry 3 2 + eps * (cliffordToTetronMatrix cDH).entry 3 2) * w 1 +
         (((cliffordToTetronMatrix cH).entry 3 3 + eps * (cliffordToTetronMatrix cDH).entry 3 3) * w 1 + 0))) = 0)
    rw [hH20, hH21, hH30, hH31, hDH20, hDH21, hDH30, hDH31, hEvenInit]
    exact ⟨by omega, by omega⟩

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

/-! ## 6. Ivanov Majorana Braiding Gates, Artin Braid Group & Open-System Lindblad Parity Cooling -/

/-- Scaled Ivanov / measurement-based Majorana exchange braid generator $T_{a, b} = 1 + \gamma_a \gamma_b \in Cl_4$
($U_{a,b} = \frac{1}{\sqrt{2}}(1 + \gamma_a \gamma_b) = \exp(\frac{\pi}{4}\gamma_a\gamma_b)$). -/
def majoranaBraidElem (a b : Fin 4) : CliffordElem :=
  cliffordAdd cliffordOne (cliffordMul (cliffordGamma a) (cliffordGamma b))

/-- Hermitian adjoint Majorana braid generator $T_{a, b}^\dagger = 1 + \gamma_b \gamma_a = 1 - \gamma_a \gamma_b \in Cl_4$
(for $a \neq b$). -/
def majoranaBraidAdjElem (a b : Fin 4) : CliffordElem :=
  cliffordAdd cliffordOne (cliffordMul (cliffordGamma b) (cliffordGamma a))

/-- Direct lookup of the $4 \times 4$ spinor matrix $\rho_{\mathbb{Z}[i]}(\gamma_a)$ for Majorana index $a \in \mathbb{N}$. -/
def spinorGammaNat : Nat → GaussianMatrix
  | 0 => gamma0Spinor
  | 1 => gamma1Spinor
  | 2 => gamma2Spinor
  | _ => gamma3Spinor

/-- Direct lookup of the $4 \times 4$ spinor matrix $\rho_{\mathbb{Z}[i]}(\gamma_a)$ for Majorana generator $a \in \text{Fin } 4$. -/
def spinorGamma (a : Fin 4) : GaussianMatrix :=
  spinorGammaNat a.val

/-- $4 \times 4$ spinor matrix $\rho_{\mathbb{Z}[i]}(T_{a,b}) = I_4 + \rho_{\mathbb{Z}[i]}(\gamma_a)\rho_{\mathbb{Z}[i]}(\gamma_b)$
of the Majorana braiding gate over $\mathbb{Z}[i]$. -/
def spinorBraidGate (a b : Fin 4) : GaussianMatrix :=
  (GaussianMatrix.identity 4).add ((spinorGamma a).mul (spinorGamma b))

/-- Exact equivalence between `spinorBraidGate a b` and `cliffordToSpinorMatrix (majoranaBraidElem a b)`
for all Majorana modes $a, b \in \text{Fin } 4$. -/
theorem spinorBraidGate_eq_cliffordToSpinorMatrix (a b : Fin 4) :
    spinorBraidGate a b = cliffordToSpinorMatrix (majoranaBraidElem a b) := by
  have hCheck : (List.range 4).all (fun i =>
      (List.range 4).all (fun j =>
        GaussianMatrix.beq
          (spinorBraidGate ⟨i % 4, Nat.mod_lt i (by decide)⟩ ⟨j % 4, Nat.mod_lt j (by decide)⟩)
          (cliffordToSpinorMatrix
            (majoranaBraidElem ⟨i % 4, Nat.mod_lt i (by decide)⟩ ⟨j % 4, Nat.mod_lt j (by decide)⟩)))) = true := by
    decide +kernel
  rw [list_all_iff_forall] at hCheck
  have hRow := (list_all_iff_forall _ (List.range 4)).mp (hCheck a.val (List.mem_range.mpr a.isLt))
  have hEq := GaussianMatrix.eq_of_beq (hRow b.val (List.mem_range.mpr b.isLt))
  have ha : (⟨a.val % 4, Nat.mod_lt a.val (by decide)⟩ : Fin 4) = a := by
    ext; exact Nat.mod_eq_of_lt a.isLt
  have hb : (⟨b.val % 4, Nat.mod_lt b.val (by decide)⟩ : Fin 4) = b := by
    ext; exact Nat.mod_eq_of_lt b.isLt
  rw [ha, hb] at hEq
  exact hEq

/-- Chiral fermion parity spinor matrix $\rho_{\mathbb{Z}[i]}(P) = \operatorname{diag}(1, 1, -1, -1)$. -/
def spinorChiralParity : GaussianMatrix where
  dim  := 4
  rows :=
    [ [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩] ]

/-- Even-parity computational subspace projector $\Pi_{\text{even}} = \frac{1}{2}(I_4 + P) = \operatorname{diag}(1, 1, 0, 0)$
over $\mathbb{Z}[i]$. -/
def spinorEvenParityProjector : GaussianMatrix where
  dim  := 4
  rows :=
    [ [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] ]

/-- Odd-parity poisoned subspace projector $\Pi_{\text{odd}} = \frac{1}{2}(I_4 - P) = \operatorname{diag}(0, 0, 1, 1)$
over $\mathbb{Z}[i]$. -/
def spinorOddParityProjector : GaussianMatrix where
  dim  := 4
  rows :=
    [ [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]
    , [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩] ]

/-- **Theorem (`majoranaBraidElem_unitary`)**:
For every pair of distinct Majorana modes $a, b \in \text{Fin } 4$ ($a \neq b$), the Ivanov braid
generator $T_{a,b} = 1 + \gamma_a\gamma_b$ is scaled unitary of norm $2$:
$$T_{a,b} T_{a,b}^\dagger = T_{a,b}^\dagger T_{a,b} = 2 \cdot 1_{Cl_4} \;\wedge\;
  \rho(T_{a,b}) \rho(T_{a,b})^\dagger = \rho(T_{a,b})^\dagger \rho(T_{a,b}) = 2 I_4.$$ -/
theorem majoranaBraidElem_unitary (a b : Fin 4) (hNe : a ≠ b) :
    cliffordMul (majoranaBraidElem a b) (majoranaBraidAdjElem a b) = cliffordScale 2 cliffordOne ∧
    cliffordMul (majoranaBraidAdjElem a b) (majoranaBraidElem a b) = cliffordScale 2 cliffordOne ∧
    (spinorBraidGate a b).mul (spinorBraidGate a b).conjTranspose = (GaussianMatrix.identity 4).scale 2 ∧
    (spinorBraidGate a b).conjTranspose.mul (spinorBraidGate a b) = (GaussianMatrix.identity 4).scale 2 := by
  revert a b hNe
  decide +kernel

/-- **Theorem (`majoranaBraid_preserves_parity`)**:
For all Majorana modes $a, b \in \text{Fin } 4$, the braid gate $T_{a,b}$ commutes with total fermion
parity $P = -\gamma_0\gamma_1\gamma_2\gamma_3$ both in $Cl_4$ and in the $4 \times 4$ spinor representation:
$$\text{commutesWithParity}(T_{a,b}) = \text{true} \;\wedge\; \rho(T_{a,b}) \rho(P) = \rho(P) \rho(T_{a,b}).$$ -/
theorem majoranaBraid_preserves_parity (a b : Fin 4) :
    commutesWithParity (majoranaBraidElem a b) = true ∧
    commutesWithParity (majoranaBraidAdjElem a b) = true ∧
    (spinorBraidGate a b).mul spinorChiralParity = spinorChiralParity.mul (spinorBraidGate a b) := by
  revert a b
  decide +kernel

/-- **Theorem (`spinorParityProjectors_orthogonal_idempotent`)**:
The even and odd fermion-parity projectors $\Pi_{\text{even}}, \Pi_{\text{odd}}$ form a complete
orthogonal idempotent resolution of the identity and spectral decomposition of chiral parity $P$:
$$\Pi_{\text{even}}^2 = \Pi_{\text{even}},\quad \Pi_{\text{odd}}^2 = \Pi_{\text{odd}},\quad
  \Pi_{\text{even}}\Pi_{\text{odd}} = \Pi_{\text{odd}}\Pi_{\text{even}} = 0_4,\quad
  \Pi_{\text{even}} + \Pi_{\text{odd}} = I_4,\quad \Pi_{\text{even}} - \Pi_{\text{odd}} = P.$$ -/
theorem spinorParityProjectors_orthogonal_idempotent :
    spinorEvenParityProjector.mul spinorEvenParityProjector = spinorEvenParityProjector ∧
    spinorOddParityProjector.mul spinorOddParityProjector = spinorOddParityProjector ∧
    spinorEvenParityProjector.mul spinorOddParityProjector = GaussianMatrix.zero 4 ∧
    spinorOddParityProjector.mul spinorEvenParityProjector = GaussianMatrix.zero 4 ∧
    spinorEvenParityProjector.add spinorOddParityProjector = GaussianMatrix.identity 4 ∧
    spinorEvenParityProjector.sub spinorOddParityProjector = spinorChiralParity := by
  decide +kernel

/-- **Theorem (`majoranaBraid_exchanges_modes`)**:
**Ivanov Non-Abelian Majorana Exchange Law**:
For all distinct Majorana modes $a, b \in \text{Fin } 4$ ($a \neq b$), conjugating $\gamma_a$ and $\gamma_b$
by $T_{a,b} = 1 + \gamma_a\gamma_b$ exchanges the two Majorana modes with a topological relative minus sign:
$$T_{a,b} \gamma_a T_{a,b}^\dagger = -2 \gamma_b \;\wedge\; T_{a,b} \gamma_b T_{a,b}^\dagger = +2 \gamma_a.$$ -/
theorem majoranaBraid_exchanges_modes (a b : Fin 4) (hNe : a ≠ b) :
    cliffordMul (cliffordMul (majoranaBraidElem a b) (cliffordGamma a)) (majoranaBraidAdjElem a b) =
      cliffordScale (-2) (cliffordGamma b) ∧
    cliffordMul (cliffordMul (majoranaBraidElem a b) (cliffordGamma b)) (majoranaBraidAdjElem a b) =
      cliffordScale 2 (cliffordGamma a) := by
  revert a b hNe
  decide +kernel

/-- **Theorem (`majoranaBraid_artin_relation`)**:
**Non-Abelian Artin Braid Group Relation ($T_{a,b} T_{b,c} T_{a,b} = T_{b,c} T_{a,b} T_{b,c}$)**:
For all pairwise distinct Majorana zero modes $a, b, c \in \text{Fin } 4$ ($a \neq b$, $b \neq c$, $a \neq c$),
the braiding generators satisfy the non-Abelian Artin braid relation in both $Cl_4$ and $M_4(\mathbb{Z}[i])$,
while failing to commute ($T_{a,b} T_{b,c} \neq T_{b,c} T_{a,b}$)! -/
theorem majoranaBraid_artin_relation (a b c : Fin 4) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cliffordMul (cliffordMul (majoranaBraidElem a b) (majoranaBraidElem b c)) (majoranaBraidElem a b) =
      cliffordMul (cliffordMul (majoranaBraidElem b c) (majoranaBraidElem a b)) (majoranaBraidElem b c) ∧
    ((spinorBraidGate a b).mul (spinorBraidGate b c)).mul (spinorBraidGate a b) =
      ((spinorBraidGate b c).mul (spinorBraidGate a b)).mul (spinorBraidGate b c) ∧
    cliffordMul (majoranaBraidElem a b) (majoranaBraidElem b c) ≠
      cliffordMul (majoranaBraidElem b c) (majoranaBraidElem a b) := by
  revert a b c hab hbc hac
  decide +kernel

/-- Scaled open-system Lindblad dissipator $2 \mathcal{D}[L](\rho) = 2 L \rho L^\dagger - (L^\dagger L \rho + \rho L^\dagger L)$
over $M_4(\mathbb{Z}[i])$. -/
def lindbladDissipator2 (L rho : GaussianMatrix) : GaussianMatrix :=
  let indices := List.range L.dim
  let rhoNorm : GaussianMatrix :=
    { dim  := L.dim
    , rows := indices.map (fun u => indices.map (fun v => rho.entry u v)) }
  let lDag := L.conjTranspose
  let lDagL := lDag.mul L
  let jumpTerm := ((L.mul rhoNorm).mul lDag).scale 2
  let antiComm := (lDagL.mul rhoNorm).add (rhoNorm.mul lDagL)
  jumpTerm.sub antiComm

/-- Engineered dissipative parity-cooling jump operator $L_{\text{cool}}(a) = \rho(\gamma_a) \Pi_{\text{odd}}$
that detects and resets odd-parity quasiparticle-poisoned states back into the even-parity logical
qubit sector without disturbing even-parity states. -/
def parityCoolingJumpOp (a : Fin 4) : GaussianMatrix :=
  (spinorGamma a).mul spinorOddParityProjector

/-- **Theorem (`lindbladDissipator2_trace_zero`)**:
For every Majorana parity-cooling jump operator $L_{\text{cool}}(a)$ ($a \in \text{Fin } 4$) and
EVERY $4 \times 4$ density matrix $\rho \in M_4(\mathbb{Z}[i])$ (universally quantified over all
matrix entries of $\rho$), the Lindblad dissipator is strictly trace-preserving:
$$\operatorname{Tr}(2 \mathcal{D}[L_{\text{cool}}(a)](\rho)) = 0 + 0i.$$ -/
private theorem spinorGamma_0 (h : 0 < 4) : spinorGamma ⟨0, h⟩ = gamma0Spinor := rfl
private theorem spinorGamma_1 (h : 1 < 4) : spinorGamma ⟨1, h⟩ = gamma1Spinor := rfl
private theorem spinorGamma_2 (h : 2 < 4) : spinorGamma ⟨2, h⟩ = gamma2Spinor := rfl
private theorem spinorGamma_3 (h : 3 < 4) : spinorGamma ⟨3, h⟩ = gamma3Spinor := rfl

theorem lindbladDissipator2_trace_zero (a : Fin 4) (rho : GaussianMatrix) :
    (lindbladDissipator2 (parityCoolingJumpOp a) rho).trace = GaussianInt.zero := by
  rcases a with ⟨aVal, hLt⟩
  rcases aVal with _ | aVal
  · unfold parityCoolingJumpOp
    rw [spinorGamma_0]
    dsimp only [lindbladDissipator2,
      gamma0Spinor, spinorOddParityProjector,
      GaussianMatrix.mul, GaussianMatrix.conjTranspose,
      GaussianMatrix.scale, GaussianMatrix.add, GaussianMatrix.sub, GaussianMatrix.identity,
      GaussianMatrix.zero, GaussianMatrix.trace]
    rw [list_range_four]
    dsimp only [GaussianMatrix.entry,
      GaussianMatrix.listGetGaussianRow, GaussianMatrix.listGetGaussian,
      sumGaussianOver, GaussianInt.mul, GaussianInt.add, GaussianInt.sub,
      GaussianInt.scale, GaussianInt.conj, GaussianInt.one, GaussianInt.zero,
      List.map]
    simp only [GaussianInt.mk.injEq]
    constructor <;> omega
  · rcases aVal with _ | aVal
    · unfold parityCoolingJumpOp
      rw [spinorGamma_1]
      dsimp only [lindbladDissipator2,
        gamma1Spinor, spinorOddParityProjector,
        GaussianMatrix.mul, GaussianMatrix.conjTranspose,
        GaussianMatrix.scale, GaussianMatrix.add, GaussianMatrix.sub, GaussianMatrix.identity,
        GaussianMatrix.zero, GaussianMatrix.trace]
      rw [list_range_four]
      dsimp only [GaussianMatrix.entry,
        GaussianMatrix.listGetGaussianRow, GaussianMatrix.listGetGaussian,
        sumGaussianOver, GaussianInt.mul, GaussianInt.add, GaussianInt.sub,
        GaussianInt.scale, GaussianInt.conj, GaussianInt.one, GaussianInt.zero,
        List.map]
      simp only [GaussianInt.mk.injEq]
      constructor <;> omega
    · rcases aVal with _ | aVal
      · unfold parityCoolingJumpOp
        rw [spinorGamma_2]
        dsimp only [lindbladDissipator2,
          gamma2Spinor, spinorOddParityProjector,
          GaussianMatrix.mul, GaussianMatrix.conjTranspose,
          GaussianMatrix.scale, GaussianMatrix.add, GaussianMatrix.sub, GaussianMatrix.identity,
          GaussianMatrix.zero, GaussianMatrix.trace]
        rw [list_range_four]
        dsimp only [GaussianMatrix.entry,
          GaussianMatrix.listGetGaussianRow, GaussianMatrix.listGetGaussian,
          sumGaussianOver, GaussianInt.mul, GaussianInt.add, GaussianInt.sub,
          GaussianInt.scale, GaussianInt.conj, GaussianInt.one, GaussianInt.zero,
          List.map]
        simp only [GaussianInt.mk.injEq]
        constructor <;> omega
      · rcases aVal with _ | aVal
        · unfold parityCoolingJumpOp
          rw [spinorGamma_3]
          dsimp only [lindbladDissipator2,
            gamma3Spinor, spinorOddParityProjector,
            GaussianMatrix.mul, GaussianMatrix.conjTranspose,
            GaussianMatrix.scale, GaussianMatrix.add, GaussianMatrix.sub, GaussianMatrix.identity,
            GaussianMatrix.zero, GaussianMatrix.trace]
          rw [list_range_four]
          dsimp only [GaussianMatrix.entry,
            GaussianMatrix.listGetGaussianRow, GaussianMatrix.listGetGaussian,
            sumGaussianOver, GaussianInt.mul, GaussianInt.add, GaussianInt.sub,
            GaussianInt.scale, GaussianInt.conj, GaussianInt.one, GaussianInt.zero,
            List.map]
          simp only [GaussianInt.mk.injEq]
          constructor <;> omega
        · omega

/-- **Theorem (`lindblad_bilocal_preserves_even_sector`)**:
For all Majorana mode pairs $a, b \in \text{Fin } 4$, any bilocal parity-conserving Lindblad jump
operator $L_{a,b} = \rho(\gamma_a \gamma_b)$ preserves the even-parity computational sector with
identically zero dissipative leakage into the odd-parity sector ($\Pi_{\text{odd}} \mathcal{D}[L_{a,b}](\Pi_{\text{even}}) = 0_4$). -/
theorem lindblad_bilocal_preserves_even_sector (a b : Fin 4) :
    let L := (spinorGamma a).mul (spinorGamma b)
    let D := lindbladDissipator2 L spinorEvenParityProjector
    spinorOddParityProjector.mul D = GaussianMatrix.zero 4 ∧
    D.mul spinorOddParityProjector = GaussianMatrix.zero 4 ∧
    D = GaussianMatrix.zero 4 := by
  revert a b
  decide +kernel

/-- **Theorem (`parityCoolingJumpOp_dark_on_even_and_corrects_odd`)**:
For every Majorana mode $a \in \text{Fin } 4$, the engineered parity-cooling jump operator
$L_{\text{cool}}(a) = \rho(\gamma_a) \Pi_{\text{odd}}$ satisfies:
1. **Even-Sector Dark State**: $L_{\text{cool}}(a) \Pi_{\text{even}} = 0_4$ and
   $\mathcal{D}[L_{\text{cool}}(a)](\Pi_{\text{even}}) = 0_4$ (the logical even-parity subspace is
   completely dark to the cooling channel),
2. **Autonomous Odd-to-Even Quasiparticle Reset**:
   $L_{\text{cool}}(a) \Pi_{\text{odd}} L_{\text{cool}}(a)^\dagger = \Pi_{\text{even}}$ and
   $\Pi_{\text{even}} L_{\text{cool}}(a) = L_{\text{cool}}(a)$ (every odd-parity poisoned state is
   autonomously transferred back into the even-parity computational sector!). -/
theorem parityCoolingJumpOp_dark_on_even_and_corrects_odd (a : Fin 4) :
    (parityCoolingJumpOp a).mul spinorEvenParityProjector = GaussianMatrix.zero 4 ∧
    lindbladDissipator2 (parityCoolingJumpOp a) spinorEvenParityProjector = GaussianMatrix.zero 4 ∧
    ((parityCoolingJumpOp a).mul spinorOddParityProjector).mul (parityCoolingJumpOp a).conjTranspose =
      spinorEvenParityProjector ∧
    spinorEvenParityProjector.mul (parityCoolingJumpOp a) = parityCoolingJumpOp a ∧
    (lindbladDissipator2 (parityCoolingJumpOp a) spinorOddParityProjector).trace = GaussianInt.zero := by
  revert a
  decide +kernel

/-! ## 7. Perturbative Equitable Breaking Score & Grönwall/Duhamel Disorder Leakage Bound (`breakingScore_zero_iff_equitable`, `perturbative_disorder_leakage_bound`) -/

/-- Auxiliary lookup finding the index $i$ of the cell in `part : List (List Nat)` that contains vertex `u`. -/
def cellIndexOfListPartAux (u : Nat) (idx : Nat) : List (List Nat) → Nat
  | [] => 0
  | cell :: rest =>
    if cell.contains u then idx
    else cellIndexOfListPartAux u (idx + 1) rest

/-- Map vertex `u` to its cell index in `part : List (List Nat)`. -/
def cellIndexOfListPart (part : List (List Nat)) (u : Nat) : Nat :=
  cellIndexOfListPartAux u 0 part

/-- Members of cell `j` in `part : List (List Nat)`. -/
def cellMembersAt (part : List (List Nat)) (j : Nat) : List Nat :=
  part[j]?.getD []

/-- **Equitable Breaking Residual Matrix (`equitableBreakingResidual`)**:
Given an $n \times n$ perturbation/disorder matrix $\Delta H$, partition `part : List (List Nat)`
of $n$ vertices into $r$ cells, and candidate $r \times r$ quotient perturbation $Q_\Delta$,
computes the $n \times r$ intertwining defect matrix
$$R(\Delta H, P, Q_\Delta) = \Delta H \cdot P - P \cdot Q_\Delta,$$
whose entry $(u, j)$ is $\sum_{v \in C_j} \Delta H_{u, v} - Q_\Delta(\text{cell}(u), j)$. -/
def equitableBreakingResidual
    (dH : IntMatrix)
    (n r : Nat)
    (part : List (List Nat))
    (Q_d : Nat → Nat → Int) : IntMatrix where
  dim  := n
  rows := (List.range n).map (fun u =>
    (List.range r).map (fun j =>
      cellRowSum dH.entry (cellMembersAt part j) u - Q_d (cellIndexOfListPart part u) j))

/-- Sum a list of natural numbers using right-associative addition (convenient for structural induction). -/
def sumNatListRight : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNatListRight xs

/-- **Perturbative Equitable Breaking Score (`equitableBreakingScore`)**:
Computes the entrywise $\ell_1$ norm $\| \Delta H \cdot P - P \cdot Q_\Delta \|_1 = \sum_{u < n} \sum_{j < r} |R_{u, j}|$
of `equitableBreakingResidual dH n r part Q_d`. -/
def equitableBreakingScore
    (dH : IntMatrix)
    (n r : Nat)
    (part : List (List Nat))
    (Q_d : Nat → Nat → Int) : Nat :=
  let res := equitableBreakingResidual dH n r part Q_d
  sumNatListRight (res.rows.map (fun row => sumNatListRight (row.map Int.natAbs)))

theorem sumNatListRight_eq_zero_iff (xs : List Nat) :
    sumNatListRight xs = 0 ↔ ∀ x, x ∈ xs → x = 0 := by
  induction xs with
  | nil =>
    simp [sumNatListRight]
  | cons x rest ih =>
    simp only [sumNatListRight, Nat.add_eq_zero_iff, List.mem_cons]
    constructor
    · rintro ⟨hx, hrest⟩ y (rfl | hy)
      · exact hx
      · exact (ih.mp hrest) y hy
    · intro hAll
      exact ⟨hAll x (Or.inl rfl), ih.mpr (fun y hy => hAll y (Or.inr hy))⟩

/-- **Theorem (`breakingScore_zero_iff_equitable`)**:
**Equitable Breaking Score Zero Equivalence Theorem**:
1. **Universal Zero-Score $\iff$ Exact Equitability**:
   For ANY $n \times n$ perturbation matrix $\Delta H$, dimensions $n, r \in \mathbb{N}$, partition
   `part : List (List Nat)`, and quotient $Q_\Delta$,
   `equitableBreakingScore dH n r part Q_d = 0` **if and only if** every cell-transition residual vanishes:
   $$\forall u < n,\; \forall j < r,\quad \sum_{v \in C_j} \Delta H_{u,v} = Q_\Delta(\text{cell}(u), j).$$
2. **Exact Intertwining Recovery (`symmetry_preserving_noise_zero_leakage` Special Case)**:
   Whenever `equitableBreakingScore dH n r part Q_d = 0` and `part` assigns every $x \in C_j$ to cell $j$,
   $\Delta H$ intertwines identically with $Q_\Delta$ across all $u < n$ and all quotient states $w$:
   $$(\Delta H (P w))_u = (P (Q_\Delta w))_u.$$
3. **Concrete Majorana-1 Parity Noise Verification**:
   - Parity-preserving bilocal noise `majoranaParityPreserveNoise` on cells `[[0, 1], [2, 3]]` has
     `equitableBreakingScore = 0`,
   - Quasiparticle poisoning noise `majoranaQuasiparticlePoisonNoise` ($\gamma_0$) breaks parity
     equitability with strictly positive breaking score `equitableBreakingScore = 4 > 0`! -/
theorem breakingScore_zero_iff_equitable
    (dH : IntMatrix)
    (n r : Nat)
    (part : List (List Nat))
    (Q_d : Nat → Nat → Int) :
    (equitableBreakingScore dH n r part Q_d = 0 ↔
      ∀ u, u < n → ∀ j, j < r →
        cellRowSum dH.entry (cellMembersAt part j) u = Q_d (cellIndexOfListPart part u) j) ∧
    (equitableBreakingScore dH n r part Q_d = 0 →
      (∀ j, j ∈ List.range r → ∀ x, x ∈ cellMembersAt part j → cellIndexOfListPart part x = j) →
      ∀ (w : Nat → Int) (u : Nat), u < n →
        partitionedMatVec dH.entry (List.range r) (cellMembersAt part)
          (liftQuotientVec (cellIndexOfListPart part) w) u =
        liftQuotientVec (cellIndexOfListPart part) (quotientMatVec Q_d (List.range r) w) u) ∧
    equitableBreakingScore majoranaParityPreserveNoise 4 2 [[0, 1], [2, 3]] majoranaNoiseSymQuotient = 0 ∧
    equitableBreakingScore majoranaQuasiparticlePoisonNoise 4 2 [[0, 1], [2, 3]] (fun _ _ => 0) = 4 := by
  have hIff :
      equitableBreakingScore dH n r part Q_d = 0 ↔
        ∀ u, u < n → ∀ j, j < r →
          cellRowSum dH.entry (cellMembersAt part j) u = Q_d (cellIndexOfListPart part u) j := by
    unfold equitableBreakingScore equitableBreakingResidual
    dsimp only
    rw [sumNatListRight_eq_zero_iff]
    simp only [List.mem_map, List.mem_range]
    constructor
    · intro hRows u hu j hj
      have hRowZero := hRows
        (sumNatListRight ((List.range r).map (fun j =>
          Int.natAbs (cellRowSum dH.entry (cellMembersAt part j) u - Q_d (cellIndexOfListPart part u) j))))
        ⟨(List.range r).map (fun j =>
          cellRowSum dH.entry (cellMembersAt part j) u - Q_d (cellIndexOfListPart part u) j),
          ⟨u, hu, rfl⟩, by rw [List.map_map]; rfl⟩
      rw [sumNatListRight_eq_zero_iff] at hRowZero
      simp only [List.mem_map, List.mem_range] at hRowZero
      have hEntryZero := hRowZero
        (Int.natAbs (cellRowSum dH.entry (cellMembersAt part j) u - Q_d (cellIndexOfListPart part u) j))
        ⟨j, hj, rfl⟩
      omega
    · rintro hAll _ ⟨row, ⟨u, hu, rfl⟩, rfl⟩
      rw [List.map_map, sumNatListRight_eq_zero_iff]
      simp only [List.mem_map, List.mem_range, Function.comp_apply]
      rintro _ ⟨j, hj, rfl⟩
      have hEq := hAll u hu j hj
      omega
  refine ⟨hIff, ?_, by decide +kernel, by decide +kernel⟩
  intro hZero hCells w u hu
  have hRows := hIff.mp hZero u hu
  exact equitable_intertwining_step dH.entry Q_d (cellIndexOfListPart part) (List.range r)
    (cellMembersAt part) w u hCells (fun j hj => hRows j (List.mem_range.mp hj))

/-- Discrete-time Duhamel / Grönwall error propagation recurrence for $K$ propagator steps under
nominal operator norm bound `opNorm` ($\|H\|$) and per-step symmetry-breaking score bound `epsBreak` ($\varepsilon_{\text{break}}$):
$$E_0 = 0, \qquad E_{k+1} = \|H\| \cdot E_k + \varepsilon_{\text{break}} \cdot \|H\|^k.$$ -/
def evalDuhamelLeakageRecurrence (opNorm epsBreak : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => opNorm * evalDuhamelLeakageRecurrence opNorm epsBreak k + epsBreak * (opNorm ^ k)

/-- Exact closed-form identity for `evalDuhamelLeakageRecurrence`:
for EVERY $K \in \mathbb{N}$, $E_K = K \cdot \varepsilon_{\text{break}} \cdot \|H\|^{K-1}$. -/
theorem evalDuhamelLeakageRecurrence_closed_form (opNorm epsBreak K : Nat) :
    evalDuhamelLeakageRecurrence opNorm epsBreak K = K * epsBreak * (opNorm ^ (K - 1)) := by
  induction K with
  | zero => simp [evalDuhamelLeakageRecurrence]
  | succ k ih =>
    cases k with
    | zero =>
      simp [evalDuhamelLeakageRecurrence]
    | succ m =>
      change opNorm * evalDuhamelLeakageRecurrence opNorm epsBreak (m + 1) + epsBreak * (opNorm ^ (m + 1)) =
        (m + 1 + 1) * epsBreak * (opNorm ^ (m + 1))
      rw [ih]
      have hSub : m + 1 - 1 = m := rfl
      rw [hSub, Nat.pow_succ]
      calc opNorm * ((m + 1) * epsBreak * opNorm ^ m) + epsBreak * (opNorm ^ m * opNorm)
        _ = (m + 1) * (epsBreak * (opNorm ^ m * opNorm)) + 1 * (epsBreak * (opNorm ^ m * opNorm)) := by
          ac_rfl
        _ = (m + 1 + 1) * (epsBreak * (opNorm ^ m * opNorm)) := by
          rw [← Nat.add_mul]
        _ = (m + 1 + 1) * epsBreak * (opNorm ^ m * opNorm) := by
          ac_rfl

/-- **Theorem (`perturbative_disorder_leakage_bound`)**:
**Quantitative Perturbative Fabrication-Disorder Leakage Bound (Discrete Duhamel / Grönwall Certificate)**:
Suppose fabrication or thermal disorder $\Delta H$ has equitable breaking score bounded by
`equitableBreakingScore dH n r part Q_d ≤ epsBreak` ($\varepsilon_{\text{break}}$) and the nominal
propagator step has operator norm bound `opNorm` ($\|H\|$). Then for ANY non-negative leaked amplitude
trajectory `leak : Nat → Nat` starting in the equitable/Majorana code space (`leak 0 = 0`) and
satisfying the per-step Duhamel inequality
$$\forall k,\quad \text{leak}(k + 1) \le \|H\| \cdot \text{leak}(k) + \text{equitableBreakingScore}(\Delta H) \cdot \|H\|^k:$$
1. **Closed-Form Duhamel Envelope**: `evalDuhamelLeakageRecurrence opNorm epsBreak K = K * epsBreak * (opNorm ^ (K - 1))` for all $K \in \mathbb{N}$.
2. **Universal Polynomial Leakage Bound**: After $K$ discrete propagator steps, the leaked amplitude
   outside the equitable code space satisfies
   $$\text{leak}(K) \le K \cdot \varepsilon_{\text{break}} \cdot \|H\|^{K - 1}.$$
3. **Zero-Leakage Corollary ($\varepsilon_{\text{break}} = 0$)**: When `epsBreak = 0` (exact symmetry-preserving
   disorder), `leak K = 0` for all $K \in \mathbb{N}$! -/
theorem perturbative_disorder_leakage_bound
    (dH : IntMatrix)
    (n r : Nat)
    (part : List (List Nat))
    (Q_d : Nat → Nat → Int)
    (opNorm epsBreak : Nat)
    (leak : Nat → Nat)
    (hScore : equitableBreakingScore dH n r part Q_d ≤ epsBreak)
    (hInit : leak 0 = 0)
    (hStep : ∀ k, leak (k + 1) ≤ opNorm * leak k + equitableBreakingScore dH n r part Q_d * (opNorm ^ k)) :
    ∀ (K : Nat),
      evalDuhamelLeakageRecurrence opNorm epsBreak K = K * epsBreak * (opNorm ^ (K - 1)) ∧
      leak K ≤ K * epsBreak * (opNorm ^ (K - 1)) ∧
      (epsBreak = 0 → leak K = 0) := by
  have hLeRec : ∀ K, leak K ≤ evalDuhamelLeakageRecurrence opNorm epsBreak K := by
    intro K
    induction K with
    | zero =>
      simp [evalDuhamelLeakageRecurrence, hInit]
    | succ k ih =>
      dsimp only [evalDuhamelLeakageRecurrence]
      have hk := hStep k
      have h1 : opNorm * leak k ≤ opNorm * evalDuhamelLeakageRecurrence opNorm epsBreak k :=
        Nat.mul_le_mul_left opNorm ih
      have h2 : equitableBreakingScore dH n r part Q_d * (opNorm ^ k) ≤ epsBreak * (opNorm ^ k) :=
        Nat.mul_le_mul_right (opNorm ^ k) hScore
      omega
  intro K
  have hClosed := evalDuhamelLeakageRecurrence_closed_form opNorm epsBreak K
  have hBound : leak K ≤ K * epsBreak * (opNorm ^ (K - 1)) := by
    rw [← hClosed]
    exact hLeRec K
  refine ⟨hClosed, hBound, ?_⟩
  intro hZero
  rw [hZero] at hBound
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.le_zero] at hBound
  exact hBound

/-- Broken `equitableBreakingScore` that always returns `0`. -/
def equitableBreakingScoreConstZeroBug
    (_dH : IntMatrix) (_n _r : Nat) (_part : List (List Nat)) (_Q_d : Nat → Nat → Int) : Nat := 0

#tooth breakingScore_zero_iff_equitable by mutation equitableBreakingScore := equitableBreakingScoreConstZeroBug

/-- Broken `evalDuhamelLeakageRecurrence` that omits the previous step accumulation term `opNorm * E_k`. -/
def evalDuhamelLeakageRecurrenceDropPrevBug (opNorm epsBreak : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => epsBreak * (opNorm ^ k)

#tooth perturbative_disorder_leakage_bound by mutation evalDuhamelLeakageRecurrence := evalDuhamelLeakageRecurrenceDropPrevBug

/-! ## 8. True Planar 4-Mode Clements Photonic MZI Mesh (`evalPlanarClements4x4`, `planarClements4x4_conserves_optical_power`) -/

/-- Evaluate a single **Planar Odd Nearest-Neighbor Layer** on a 4-mode waveguide array with
phase-matched outer reference waveguides:
- Inner adjacent waveguide pair $(1, 2)$ is coupled by `evalDirectionalCoupler2x2 t kappa e1 e2`,
- Outer waveguides $0$ and $3$ propagate through uncoupled phase-matched reference waveguides
  (`evalDirectionalCoupler2x2 t kappa e0 ⟨0, 0⟩` and `evalDirectionalCoupler2x2 t kappa ⟨0, 0⟩ e3`,
  i.e., zero non-planar $0 \leftrightarrow 3$ coupling!). -/
def evalPlanarOddLayer4x4
    (t kappa : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let ref0 := evalDirectionalCoupler2x2 t kappa e0 ⟨0, 0⟩
  let c12  := evalDirectionalCoupler2x2 t kappa e1 e2
  let ref3 := evalDirectionalCoupler2x2 t kappa ⟨0, 0⟩ e3
  (ref0.1, c12.1, c12.2, ref3.1)

/-- Evaluate a **True Planar 4-Mode Clements Photonic Mesh (`evalPlanarClements4x4`)**:
Alternates planar nearest-neighbor directional coupler layers `[(0, 1), (2, 3)]` (even layer) and
`[(1, 2)]` (odd layer, with outer waveguides $0$ and $3$ completely uncoupled from each other —
zero waveguide crossings!):
1. **Layer 1 (Even Nearest-Neighbor Layer `[(0, 1), (2, 3)]`)**: couples $(0, 1)$ and $(2, 3)$,
2. **Layer 2 (Odd Nearest-Neighbor Layer `[(1, 2)]`)**: couples $(1, 2)$ while outer modes $0$ and $3$
   never interact (`0 ↔ 3` crossing-free). -/
def evalPlanarClements4x4
    (t kappa : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let (m0, m1, m2, m3) := evalPhotonicArray4LayerEven t kappa t kappa e0 e1 e2 e3
  evalPhotonicArray4LayerOdd t kappa m0 m1 m2 m3

/-- Alias `evalClements4x4Mesh` for the planar 4-mode Clements mesh. -/
abbrev evalClements4x4Mesh := evalPlanarClements4x4

/-- **Theorem (`planarClements4x4_conserves_optical_power`)**:
**Universal Planar 4-Mode Clements Mesh Optical Power Conservation Theorem**:
For ALL coupler transmission/coupling parameters `t, kappa : Int` and ALL input optical fields
`e0, e1, e2, e3 : ComplexField` ($\mathbb{Z}[i]$), proved by composing `directional_coupler_2x2_power_conservation`:
1. **Planar 2-Layer Clements Mesh (`evalPlanarClements4x4`) Weighted Power Conservation**:
   With CMT scale $s = t^2 + \kappa^2$, the planar Clements mesh (which couples `[(0, 1), (2, 3)]`
   in Layer 1 and ONLY `[(1, 2)]` in Layer 2, with zero $0 \leftrightarrow 3$ crossing) satisfies:
   $$s |E_{\text{out},0}|^2 + |E_{\text{out},1}|^2 + |E_{\text{out},2}|^2 + s |E_{\text{out},3}|^2
     = s^2 \left(|E_0|^2 + |E_1|^2 + |E_2|^2 + |E_3|^2\right).$$
2. **Unweighted Power Conservation at Normalized Scale ($t^2 + \kappa^2 = 1$)**:
   Whenever $t^2 + \kappa^2 = 1$,
   $$|E_{\text{out},0}|^2 + |E_{\text{out},1}|^2 + |E_{\text{out},2}|^2 + |E_{\text{out},3}|^2
     = |E_0|^2 + |E_1|^2 + |E_2|^2 + |E_3|^2.$$
3. **Strict Planar $0 \leftrightarrow 3$ Isolation**:
   Outer output mode $0$ of `evalPlanarClements4x4 t kappa e0 e1 e2 e3` depends ONLY on inputs
   $(e_0, e_1)$ and is completely independent of $(e_2, e_3)$, proving zero $0 \leftrightarrow 3$ crosstalk! -/
theorem planarClements4x4_conserves_optical_power
    (t kappa : Int)
    (e0 e1 e2 e3 : ComplexField) :
    (let s := t * t + kappa * kappa
     let (p0, p1, p2, p3) := evalPlanarClements4x4 t kappa e0 e1 e2 e3
     s * p0.normSq + p1.normSq + p2.normSq + s * p3.normSq =
       s * (s * (e0.normSq + e1.normSq + e2.normSq + e3.normSq))) ∧
    (t * t + kappa * kappa = 1 →
     let (p0, p1, p2, p3) := evalPlanarClements4x4 t kappa e0 e1 e2 e3
     p0.normSq + p1.normSq + p2.normSq + p3.normSq =
       e0.normSq + e1.normSq + e2.normSq + e3.normSq) ∧
    (∀ e2' e3' : ComplexField,
      (evalPlanarClements4x4 t kappa e0 e1 e2 e3).1 =
        (evalPlanarClements4x4 t kappa e0 e1 e2' e3').1) := by
  have hBase := planarClements4Mesh_conserves_optical_power t kappa t kappa e0 e1 e2 e3
  dsimp only [evalPlanarClements4x4]
  refine ⟨hBase.1, ?_, fun _ _ => rfl⟩
  intro hUnit
  have h2 := hBase.2.1 hUnit
  rw [hUnit, Int.one_mul] at h2
  exact h2

/-- Broken `evalPlanarClements4x4` that zeroes out mode 1 in the odd layer (violating power conservation). -/
def evalPlanarClements4x4LossyBug
    (t kappa : Int)
    (e0 e1 e2 e3 : ComplexField) :
    ComplexField × ComplexField × ComplexField × ComplexField :=
  let (m0, _m1, m2, m3) := evalPhotonicArray4LayerEven t kappa t kappa e0 e1 e2 e3
  (m0, ⟨0, 0⟩, m2, m3)

#tooth planarClements4x4_conserves_optical_power by mutation evalPlanarClements4x4 := evalPlanarClements4x4LossyBug

/-! ## 9. Symmetric `StrictOpenHypergraph` Equitable Quotient Compression & `quotientHypergraphSlot` (`quotientOpenHypergraph_intertwines_eval_and_adjoint`, `quotientHypergraph_moved_pin_blocks`) -/

/-- Partition of a 4-channel parallel hardware/photonic/attention hypergraph into $r = 2$ equitable
symmetry cells $C_0 = \{0, 1\}$ and $C_1 = \{2, 3\}$. -/
def sym4LaneCellOf : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 0

/-- Construct an $N = 4$-channel `StrictOpenHypergraph` where each channel lane $u \in \{0, 1, 2, 3\}$
processes its input pair $(x_u, y_u)$ through a channel-weighted stage-1 scale `.scale w_u` followed
by a shared stage-2 operation `op2 : OpticOp`:
- Lane $u \in \{0, 1, 2, 3\}$ occupies a 6-wire slice `[6*u .. 6*u + 5]`:
  * `6*u + 0`: boundary input $x_u$,
  * `6*u + 1`: boundary input $y_u$ (fans out to both stage 1 and stage 2),
  * `6*u + 2`: stage-1 output $m_u = w_u \cdot x_u$,
  * `6*u + 3`: boundary output $z_u = \text{op}_2(m_u, y_u)$,
  * `6*u + 4`, `6*u + 5`: internal scratch wires. -/
def buildSymmetric4LaneHypergraph
    (w0 w1 w2 w3 : Int)
    (op2 : OpticOp) : StrictOpenHypergraph :=
  let lane0 := opticFwdHyperEdges (.scale w0) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5
  let lane1 := opticFwdHyperEdges (.scale w1) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11
  let lane2 := opticFwdHyperEdges (.scale w2) 12 13 14 16 ++ opticFwdHyperEdges op2 14 13 15 17
  let lane3 := opticFwdHyperEdges (.scale w3) 18 19 20 22 ++ opticFwdHyperEdges op2 20 19 21 23
  mkStrictOpenHypergraph 24
    [0, 1, 6, 7, 12, 13, 18, 19]
    [3, 9, 15, 21]
    (reindexHyperEdges (lane0 ++ lane1 ++ lane2 ++ lane3))

/-- **Equitable Quotient Open Hypergraph Compression (`quotientOpenHypergraph`)**:
Compresses the $N = 4$-channel symmetric `StrictOpenHypergraph` (with equitable cell weights
$w_0 = w_1 = W_0$ on cell $C_0 = \{0, 1\}$ and $w_2 = w_3 = W_1$ on cell $C_1 = \{2, 3\}$)
down to an $r = 2$-cell quotient `StrictOpenHypergraph` ($12$ wires instead of $24$, and half the
hyperedges in both the forward pass and `compileGraphAdjoint`!). -/
def quotientOpenHypergraph
    (W0 W1 : Int)
    (op2 : OpticOp) : StrictOpenHypergraph :=
  let cell0 := opticFwdHyperEdges (.scale W0) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5
  let cell1 := opticFwdHyperEdges (.scale W1) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11
  mkStrictOpenHypergraph 12
    [0, 1, 6, 7]
    [3, 9]
    (reindexHyperEdges (cell0 ++ cell1))

/-- Initial wire environment for the compressed $r = 2$-cell quotient hypergraph (and its adjoint
`compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2)`, whose output cotangent seed wires are
`12` and `13`). -/
def quotientHypergraphInitEnv
    (x0 y0 x1 y1 dOut0 dOut1 : Int) (w : Nat) : Int :=
  match w with
  | 0  => x0
  | 1  => y0
  | 6  => x1
  | 7  => y1
  | 12 => dOut0
  | 13 => dOut1
  | _  => 0

/-- Cell-constant lifted wire environment for the $N = 4$-lane symmetric hypergraph (and its adjoint
`compileGraphAdjoint (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2)`, whose output cotangent seed
wires are `24, 25, 26, 27`), lifting cell $C_0$'s inputs $(x_0, y_0, dOut_0)$ to lanes $0, 1$ and
cell $C_1$'s inputs $(x_1, y_1, dOut_1)$ to lanes $2, 3$. -/
def liftSymmetric4LaneInitEnv
    (x0 y0 x1 y1 dOut0 dOut1 : Int) (w : Nat) : Int :=
  match w with
  | 0  => x0
  | 1  => y0
  | 6  => x0
  | 7  => y0
  | 12 => x1
  | 13 => y1
  | 18 => x1
  | 19 => y1
  | 24 => dOut0
  | 25 => dOut0
  | 26 => dOut1
  | 27 => dOut1
  | _  => 0

/-- Lift the 2-cell forward output vector `[z0, z1]` of `quotientOpenHypergraph` to the 4-lane
output vector `[z0, z0, z1, z1]` across $C_0 = \{0, 1\}$ and $C_1 = \{2, 3\}$. -/
def liftQuotientFwdOutputs (qOut : List Int) : List Int :=
  [qOut.getD 0 0, qOut.getD 0 0, qOut.getD 1 0, qOut.getD 1 0]

/-- Lift the 6-element adjoint output vector `[z0, z1, dx0, dy0, dx1, dy1]` of
`compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2)` to the 12-element 4-lane adjoint output
vector `[z0, z0, z1, z1, dx0, dy0, dx0, dy0, dx1, dy1, dx1, dy1]`. -/
def liftQuotientAdjointOutputs (qAdjOut : List Int) : List Int :=
  let z0  := qAdjOut.getD 0 0
  let z1  := qAdjOut.getD 1 0
  let dx0 := qAdjOut.getD 2 0
  let dy0 := qAdjOut.getD 3 0
  let dx1 := qAdjOut.getD 4 0
  let dy1 := qAdjOut.getD 5 0
  [z0, z0, z1, z1, dx0, dy0, dx0, dy0, dx1, dy1, dx1, dy1]

set_option maxHeartbeats 1600000 in
/-- **Theorem (`quotientOpenHypergraph_intertwines_eval_and_adjoint`)**:
**Universal Symmetric `StrictOpenHypergraph` Forward & Reverse-Mode AD Quotient Intertwining Theorem**:
For EVERY stage-2 operation `op2 : OpticOp`, EVERY symmetry-cell weight pair `W0, W1 : Int`,
EVERY cell-constant primal input state `x0, y0, x1, y1 : Int`, and EVERY cell-constant upstream
cotangent seed `dOut0, dOut1 : Int`:
1. **Structural Well-Formedness & $2\times$ Compression**:
   Both `buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2` ($24$ wires) and its compressed quotient
   `quotientOpenHypergraph W0 W1 op2` ($12$ wires) are well-formed (`wf = true`).
2. **Combinational & Wavefront-Layered Forward Intertwining (`evalHypergraphComb` & `evalHypergraphLayered`)**:
   Evaluating the 4-lane symmetric hypergraph via `evalHypergraphComb` or `evalHypergraphLayered`
   on the lifted cell-constant environment produces the exact lifted output of the compressed 2-cell
   quotient hypergraph:
   $$\text{evalHypergraphLayered}(G_{\text{full}}, P w) = P_{\text{out}}\!\left(\text{evalHypergraphLayered}(G_{\text{quot}}, w)\right).$$
3. **Whole-DAG Reverse-Mode AD Intertwining (`compileGraphAdjoint`)**:
   Running whole-DAG reverse-mode AD `compileGraphAdjoint` on the 4-lane symmetric hypergraph
   (via `evalHypergraphComb` or `evalHypergraphLayered`) produces the **exact lifted primal outputs
   AND lifted input cotangent gradients $(\partial L / \partial x_u, \partial L / \partial y_u)$**
   of `compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2)`! -/
theorem quotientOpenHypergraph_intertwines_eval_and_adjoint
    (W0 W1 : Int)
    (op2 : OpticOp)
    (x0 y0 x1 y1 dOut0 dOut1 : Int) :
    let gFull := buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2
    let gQuot := quotientOpenHypergraph W0 W1 op2
    let envFull := liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1
    let envQuot := quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1
    let adjFull := compileGraphAdjoint gFull
    let adjQuot := compileGraphAdjoint gQuot
    -- 1. Well-formedness & compression ratio
    gFull.wf = true ∧
    gQuot.wf = true ∧
    gFull.nodeTypes.length = 24 ∧
    gQuot.nodeTypes.length = 12 ∧
    -- 2. Forward combinational & wavefront-layered intertwining
    evalHypergraphComb gFull envFull = liftQuotientFwdOutputs (evalHypergraphComb gQuot envQuot) ∧
    evalHypergraphLayered gFull envFull = liftQuotientFwdOutputs (evalHypergraphLayered gQuot envQuot) ∧
    -- 3. Whole-DAG reverse-mode AD (compileGraphAdjoint) combinational & layered intertwining
    evalHypergraphComb adjFull envFull = liftQuotientAdjointOutputs (evalHypergraphComb adjQuot envQuot) ∧
    evalHypergraphLayered adjFull envFull = liftQuotientAdjointOutputs (evalHypergraphLayered adjQuot envQuot) := by
  have hPipeFull := (evalHypergraph_pipelined_eq_comb (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2)
    (liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1)).1
  have hPipeQuot := (evalHypergraph_pipelined_eq_comb (quotientOpenHypergraph W0 W1 op2)
    (quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1)).1
  have hPipeAdjFull := (evalHypergraph_pipelined_eq_comb
    (compileGraphAdjoint (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2))
    (liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1)).1
  have hPipeAdjQuot := (evalHypergraph_pipelined_eq_comb
    (compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2))
    (quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1)).1
  have hWfFull : (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2).wf = true := by
    cases op2 <;> rfl
  have hWfQuot : (quotientOpenHypergraph W0 W1 op2).wf = true := by
    cases op2 <;> rfl
  have hFwdComb :
      evalHypergraphComb (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2)
        (liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1) =
      liftQuotientFwdOutputs
        (evalHypergraphComb (quotientOpenHypergraph W0 W1 op2)
          (quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1)) := by
    unfold buildSymmetric4LaneHypergraph quotientOpenHypergraph
    rw [evalHypergraphComb_mkStrictOpenHypergraph_reindex,
        evalHypergraphComb_mkStrictOpenHypergraph_reindex]
    cases op2 <;>
      dsimp [opticFwdHyperEdges, evalHyperEdgesComb, stepHyperEdge, evalHypergraphOp,
        liftSymmetric4LaneInitEnv, quotientHypergraphInitEnv, liftQuotientFwdOutputs,
        List.foldl, List.map, list_getD_zero_cons, list_getD_one_cons] <;>
      rfl
  have hAdjComb :
      evalHypergraphComb (compileGraphAdjoint (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2))
        (liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1) =
      liftQuotientAdjointOutputs
        (evalHypergraphComb (compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2))
          (quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1)) := by
    have hEqFull :
        compileGraphAdjoint (buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2) =
          compileGraphAdjointAux 24 [0, 1, 6, 7, 12, 13, 18, 19] [3, 9, 15, 21]
            (reindexHyperEdges
              ((opticFwdHyperEdges (.scale W0) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5) ++
               (opticFwdHyperEdges (.scale W0) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11) ++
               (opticFwdHyperEdges (.scale W1) 12 13 14 16 ++ opticFwdHyperEdges op2 14 13 15 17) ++
               (opticFwdHyperEdges (.scale W1) 18 19 20 22 ++ opticFwdHyperEdges op2 20 19 21 23))) := by
      unfold compileGraphAdjoint buildSymmetric4LaneHypergraph
      change compileGraphAdjointAux (List.replicate 24 64).length
        [0, 1, 6, 7, 12, 13, 18, 19] [3, 9, 15, 21]
        (extractHyperEdges (mkStrictOpenHypergraph 24 [0, 1, 6, 7, 12, 13, 18, 19] [3, 9, 15, 21] _)) = _
      rw [List.length_replicate, extractHyperEdges_mkStrictOpenHypergraph]
    have hEqQuot :
        compileGraphAdjoint (quotientOpenHypergraph W0 W1 op2) =
          compileGraphAdjointAux 12 [0, 1, 6, 7] [3, 9]
            (reindexHyperEdges
              ((opticFwdHyperEdges (.scale W0) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5) ++
               (opticFwdHyperEdges (.scale W1) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11))) := by
      unfold compileGraphAdjoint quotientOpenHypergraph
      change compileGraphAdjointAux (List.replicate 12 64).length [0, 1, 6, 7] [3, 9]
        (extractHyperEdges (mkStrictOpenHypergraph 12 [0, 1, 6, 7] [3, 9] _)) = _
      rw [List.length_replicate, extractHyperEdges_mkStrictOpenHypergraph]
    rw [hEqFull, hEqQuot, evalHypergraphComb_compileGraphAdjointAux, evalHypergraphComb_compileGraphAdjointAux]
    cases op2 <;>
      dsimp [evalBuildGraphAdjointComb, buildGraphAdjointState,
        opticFwdHyperEdges, reindexHyperEdges, reindexHyperEdgesAux,
        seedCotangentStateAux, accumWireCotangent, emitAndAccum, upsertCotWire,
        pullbackHyperEdge, wireAt, emitRevEdge, resolveInputCotWires, setCotWire,
        evalHyperEdgesComb, stepHyperEdge, evalHypergraphOp,
        liftSymmetric4LaneInitEnv, quotientHypergraphInitEnv, liftQuotientAdjointOutputs,
        List.reverse, List.reverseAux, List.foldl, List.map, List.lookup,
        list_getD_zero_cons, list_getD_one_cons, list_getD_two_cons, list_getD_nil] <;>
      rfl
  dsimp only
  refine ⟨hWfFull, hWfQuot, rfl, rfl, hFwdComb, ?_, hAdjComb, ?_⟩
  · rw [hPipeFull, hPipeQuot, hFwdComb]
  · rw [hPipeAdjFull, hPipeAdjQuot, hAdjComb]

/-- Specialization candidates for `quotientHypergraphSlot`:
- `.quotientCompressed gFull gQuot weightPins eqOk`: the compressed $r$-lane quotient hypergraph
  `gQuot`, supported by the `LeafPin` list `weightPins` pinning every channel weight parameter
  $w_i = W_{\text{cell}(i)}$ across symmetry cells,
- `.unreducedFull gFull`: the unreduced $N$-lane hypergraph fallback (no symmetry pins required). -/
inductive QuotientHypergraphCandidate where
  | quotientCompressed
      (gFull : StrictOpenHypergraph)
      (gQuot : StrictOpenHypergraph)
      (weightPins : List LeafPin)
      (equitableOk : Bool)
  | unreducedFull (gFull : StrictOpenHypergraph)

/-- Support pins for a `QuotientHypergraphCandidate`. -/
def QuotientHypergraphCandidate.supports : QuotientHypergraphCandidate → List LeafPin
  | .quotientCompressed _ _ pins _ => pins
  | .unreducedFull _ => []

/-- Admission judge for a `QuotientHypergraphCandidate`. -/
def QuotientHypergraphCandidate.judge : QuotientHypergraphCandidate → Bool
  | .quotientCompressed gFull gQuot _ eqOk => gFull.wf && gQuot.wf && eqOk
  | .unreducedFull gFull => gFull.wf

/-- **The Quotient Hypergraph Specialization Slot (`quotientHypergraphSlot`)**:
Pins the symmetry-preserving channel weight parameters (`w_i = w_j` within each equitable cell)
and automatically invalidates the compressed $r$-lane quotient candidate whenever an outer `.obend`
layer overrides a channel weight and breaks equitability. -/
def quotientHypergraphSlot : Slot LeafPin QuotientHypergraphCandidate :=
  ⟨QuotientHypergraphCandidate.supports, QuotientHypergraphCandidate.judge⟩

/-- Construct a `LeafPin` pinning channel weight key `key` (e.g. `"weights.w1"`) to integer literal `w`. -/
def mkChannelWeightPin (key : String) (w : Nat) : LeafPin :=
  ⟨.layer key, .nat w⟩

/-- The 4 symmetry-preserving channel weight pins for a 4-lane hypergraph with cell weights $W_0, W_1 \in \mathbb{N}$
($w_0 = W_0, w_1 = W_0$ in cell $C_0$, and $w_2 = W_1, w_3 = W_1$ in cell $C_1$). -/
def sym4LaneWeightPins (W0 W1 : Nat) : List LeafPin :=
  [ mkChannelWeightPin "weights.w0" W0
  , mkChannelWeightPin "weights.w1" W0
  , mkChannelWeightPin "weights.w2" W1
  , mkChannelWeightPin "weights.w3" W1 ]

/-- Build a `LeafView` at `clock` assigning channel weights `(w0, w1, w2, w3)` to `"weights.w0" .. "weights.w3"`. -/
def mkChannelWeightView (clock w0 w1 w2 w3 : Nat) : LeafView where
  clock := clock
  decl
    | .layer "weights.w0" => some (.nat w0)
    | .layer "weights.w1" => some (.nat w1)
    | .layer "weights.w2" => some (.nat w2)
    | .layer "weights.w3" => some (.nat w3)
    | _ => none

/-- **Theorem (`quotientHypergraph_moved_pin_blocks`)**:
1. **Universal Moved-Pin Blocking (`read_blocked_exact`)**:
   Whenever a compressed quotient candidate `cand = .quotientCompressed gFull gQuot pins true` is
   admitted (`quotientHypergraphSlot.judge cand = true`), if ANY symmetry-preserving channel weight
   pin `p ∈ pins` ceases to hold at `v : LeafView` (`holdsAt v p = false`), then reading
   `quotientHypergraphSlot` at `v` immediately returns `.blocked cand d` with `p ∈ d` and
   `∀ q, q ∈ d ↔ q ∈ pins ∧ holdsAt v q = false`, AND `slotAdvance.advance` falls back to
   `.ok (.unreducedFull gFull)` in 1 cycle!
2. **Concrete `.obend` Single-Channel Weight Override Verification**:
   - At clock $0$ (`vSym := mkChannelWeightView 0 5 5 7 7`, where $w_0 = w_1 = 5$ and $w_2 = w_3 = 7$
     preserve equitability), the compressed 2-lane quotient candidate is `.usable`.
   - At clock $1$ (`vBroken := mkChannelWeightView 1 5 99 7 7`, where an outer `.obend` layer overrides
     a single channel weight $w_1 := 99 \neq 5$ and breaks equitability), `quotientHypergraphSlot.read`
     blocks the compressed quotient candidate in 1 cycle, naming the exact broken pin cell
     `[.layer "weights.w1"]`! -/
theorem quotientHypergraph_moved_pin_blocks
    (v : LeafView)
    (gFull gQuot : StrictOpenHypergraph)
    (pins : List LeafPin)
    (hWfFull : gFull.wf = true)
    (hWfQuot : gQuot.wf = true)
    (p : LeafPin)
    (hp : p ∈ pins)
    (hd : holdsAt v p = false) :
    let cand := QuotientHypergraphCandidate.quotientCompressed gFull gQuot pins true
    let fallback := QuotientHypergraphCandidate.unreducedFull gFull
    (∃ d,
      quotientHypergraphSlot.read (holdsAt v) (some cand) = .blocked cand d ∧
      p ∈ d ∧
      (∀ q, q ∈ d ↔ q ∈ pins ∧ holdsAt v q = false)) ∧
    (slotAdvance : Advance LeafView LeafPin QuotientHypergraphCandidate).advance
      quotientHypergraphSlot v [cand, fallback] (some cand) = .ok fallback ∧
    (let gFullConcrete := buildSymmetric4LaneHypergraph 5 5 7 7 .add
     let gQuotConcrete := quotientOpenHypergraph 5 7 .add
     let pinsConcrete := sym4LaneWeightPins 5 7
     let candConcrete := QuotientHypergraphCandidate.quotientCompressed
                           gFullConcrete gQuotConcrete pinsConcrete true
     let vSym := mkChannelWeightView 0 5 5 7 7
     let vBroken := mkChannelWeightView 1 5 99 7 7
     quotientHypergraphSlot.usable (holdsAt vSym) candConcrete = true ∧
     quotientHypergraphSlot.usable (holdsAt vBroken) candConcrete = false ∧
     (quotientHypergraphSlot.dead (holdsAt vBroken) candConcrete).map LeafPin.cell =
       [.layer "weights.w1"]) := by
  dsimp only
  let cand := QuotientHypergraphCandidate.quotientCompressed gFull gQuot pins true
  let fallback := QuotientHypergraphCandidate.unreducedFull gFull
  have hJudge : quotientHypergraphSlot.judge cand = true := by
    simp [quotientHypergraphSlot, QuotientHypergraphCandidate.judge, cand, hWfFull, hWfQuot]
  have hMemDead : p ∈ quotientHypergraphSlot.dead (holdsAt v) cand :=
    (mem_dead_iff quotientHypergraphSlot (holdsAt v) cand p).2 ⟨hp, hd⟩
  have hread : ∃ d,
      quotientHypergraphSlot.read (holdsAt v) (some cand) = .blocked cand d ∧ p ∈ d := by
    unfold Slot.read
    simp only [hJudge, ite_true]
    cases hdd : quotientHypergraphSlot.dead (holdsAt v) cand with
    | nil =>
      rw [hdd] at hMemDead
      cases hMemDead
    | cons g t =>
      exact ⟨g :: t, rfl, hdd ▸ hMemDead⟩
  obtain ⟨d, hr, hpd⟩ := hread
  have hRead : ∃ d,
      quotientHypergraphSlot.read (holdsAt v) (some cand) = .blocked cand d ∧
      p ∈ d ∧
      (∀ q, q ∈ d ↔ q ∈ pins ∧ holdsAt v q = false) :=
    ⟨d, hr, hpd, (read_blocked_exact quotientHypergraphSlot _ _ _ _ hr).2⟩
  have hNotUsable : quotientHypergraphSlot.usable (holdsAt v) cand = false := by
    unfold Slot.usable
    cases hdd : quotientHypergraphSlot.dead (holdsAt v) cand with
    | nil =>
      rw [hdd] at hMemDead
      cases hMemDead
    | cons _ _ =>
      simp [List.isEmpty]
  have hFallbackUsable : quotientHypergraphSlot.usable (holdsAt v) fallback = true := by
    simp [Slot.usable, Slot.dead, quotientHypergraphSlot,
      QuotientHypergraphCandidate.supports, QuotientHypergraphCandidate.judge, fallback, hWfFull]
  have hAdv :
      (slotAdvance : Advance LeafView LeafPin QuotientHypergraphCandidate).advance
        quotientHypergraphSlot v [cand, fallback] (some cand) = .ok fallback := by
    refine (incumbent_choice quotientHypergraphSlot v [cand, fallback] (some cand) fallback).2
      (.inr ⟨fun c hc => by cases hc; exact hNotUsable, ?_⟩)
    simp [Slot.select, Slot.alternatives, hNotUsable, hFallbackUsable]
  refine ⟨hRead, hAdv, ?_⟩
  decide +kernel

/-- Broken `quotientOpenHypergraph` that swaps cell weights $W_0$ and $W_1$. -/
def quotientOpenHypergraphSwapWeightsBug (W0 W1 : Int) (op2 : OpticOp) : StrictOpenHypergraph :=
  let cell0 := opticFwdHyperEdges (.scale W1) 0 1 2 4 ++ opticFwdHyperEdges op2 2 1 3 5
  let cell1 := opticFwdHyperEdges (.scale W0) 6 7 8 10 ++ opticFwdHyperEdges op2 8 7 9 11
  mkStrictOpenHypergraph 12
    [0, 1, 6, 7]
    [3, 9]
    (reindexHyperEdges (cell0 ++ cell1))

#tooth quotientOpenHypergraph_intertwines_eval_and_adjoint by mutation quotientOpenHypergraph := quotientOpenHypergraphSwapWeightsBug

/-- Broken `QuotientHypergraphCandidate.supports` that drops all channel weight pins (`[]`). -/
def quotientSupportsDropPinsBug : QuotientHypergraphCandidate → List LeafPin
  | _ => []

#tooth quotientHypergraph_moved_pin_blocks by mutation QuotientHypergraphCandidate.supports := quotientSupportsDropPinsBug

end Obend.Hardware.QuantumMatter
end
