module
/-
# Obend.Hardware.Magnetics — 2D FEMM Electromagnetic FEA, Nonlinear Silicon-Steel B-H Saturation, $dq0$ IPM Reluctance Torque & Steinmetz Core-Loss Signoff

Formalizes **2D planar magnetostatic/time-harmonic Finite Element Analysis (FEMM-style, after
David Meeker's Finite Element Method Magnetics)** and **liquid-cooled Interior Permanent Magnet
(IPM) electric machine physics** within `Obend.Hardware`:

1. **2D Planar First-Order Triangular Finite Element (`FemmTriangle2D`) for $\nabla \cdot (\nu \nabla A_z) + J_z = 0$**:
   - Models a first-order Meeker/Courant triangular mesh element with integer vertex coordinates
     $(x_0, y_0), (x_1, y_1), (x_2, y_2)$, magnetic reluctivity $\nu = 1/\mu$, and out-of-plane
     source current density $J_z$,
   - Defines shape function gradient coefficients $b_i = y_{i+1} - y_{i+2}$ and $c_i = x_{i+2} - x_{i+1}$
     along with signed double-area $2\Delta = b_0 c_1 - b_1 c_0$,
   - Proves **`femm_gradient_sum_zero`** ($\sum_i b_i = 0 \wedge \sum_i c_i = 0$) and
     **`femm_gauge_invariance`** (shifting nodal magnetic vector potentials $A_i \mapsto A_i + c$
     leaves $\nabla A_z$ and magnetic flux density $\mathbf{B} = \nabla \times (A_z \hat{\mathbf{z}})$
     strictly invariant for all $A_0, A_1, A_2, c \in \mathbb{Z}$),
   - Proves **`femm_element_energy_nonneg`** and **`femm_mesh_energy_nonneg`** (universal
     co-energy convexity $0 \le \sum_{e \in \mathcal{T}} \nu_e \|\nabla A_z\|_e^2$ across any 2D mesh).
2. **Nonlinear Silicon-Steel B-H Saturation & Chord Reluctivity (`BhReluctivityModel`)**:
   - Models ferromagnetic stator/rotor lamination saturation $\nu(B^2) = \nu_0 + k_{\text{sat}} B^2$,
   - Proves **`bh_saturation_increases_reluctivity`**: for any non-negative saturation coefficient
     $k_{\text{sat}} \ge 0$, increasing flux density squared $B_1^2 \le B_2^2$ monotonically increases
     effective core reluctivity $\nu(B_1^2) \le \nu(B_2^2)$ (decreasing differential permeability).
3. **$dq0$ Interior Permanent Magnet (IPM) & Synchronous Reluctance Torque (`IpmMotorSpec`)**:
   - Models Park/Clarke $dq0$-frame electromagnetic torque
     $T_e \propto p \left(\psi_{\text{PM}} i_q + (L_d - L_q) i_d i_q\right)$,
   - Proves **`ipm_reluctance_torque_boost`**: for any salient IPM rotor ($L_d \le L_q$, $p \ge 0$)
     operated under field-weakening / Maximum-Torque-Per-Ampere (MTPA) negative $d$-axis current
     ($i_d \le 0, i_q \ge 0$), the reluctance torque term $(L_d - L_q) i_d i_q \ge 0$ strictly boosts
     total shaft torque above the pure permanent-magnet alignment torque $p \psi_{\text{PM}} i_q$.
4. **Steinmetz Core Loss, AC Winding Loss & Liquid-Cooled Motor Signoff (`checkMagneticsSignoff`)**:
   - Models hysteresis and eddy-current iron core loss
     $P_{\text{core}} = k_h f B_{\text{pk}}^2 + k_e f^2 B_{\text{pk}}^2$,
   - Proves **`steinmetz_core_loss_nonneg`**, **`checkMagneticsSignoff_sound`**, and
     **`golden_femm_liquid_motor_magnetics_verified`** (`decide +kernel`).
-/
public import Obend.Hardware.Thermal
@[expose] public section

namespace Obend.Hardware.Magnetics
open Obend.Hardware.Thermal
set_option autoImplicit false

/-! ## 1. 2D Planar First-Order Triangular Finite Element (`FemmTriangle2D`) -/

/-- A 2D planar first-order triangular finite element for the magnetostatic PDE
$\nabla \cdot (\nu \nabla A_z) + J_z = 0$ (as solved by David Meeker's FEMM):
* `(x0, y0)`, `(x1, y1)`, `(x2, y2)`: integer vertex coordinates (e.g. in micrometers),
* `nuScaled`: element magnetic reluctivity $\nu = 1/\mu$ (scaled integer units),
* `jzScaled`: out-of-plane source current density $J_z$ (scaled integer units). -/
structure FemmTriangle2D where
  x0       : Int
  y0       : Int
  x1       : Int
  y1       : Int
  x2       : Int
  y2       : Int
  nuScaled : Int
  jzScaled : Int
  deriving DecidableEq, Repr

/-- Shape function $x$-gradient numerator $b_0 = y_1 - y_2$. -/
def FemmTriangle2D.b0 (tri : FemmTriangle2D) : Int := tri.y1 - tri.y2

/-- Shape function $x$-gradient numerator $b_1 = y_2 - y_0$. -/
def FemmTriangle2D.b1 (tri : FemmTriangle2D) : Int := tri.y2 - tri.y0

/-- Shape function $x$-gradient numerator $b_2 = y_0 - y_1$. -/
def FemmTriangle2D.b2 (tri : FemmTriangle2D) : Int := tri.y0 - tri.y1

/-- Shape function $y$-gradient numerator $c_0 = x_2 - x_1$. -/
def FemmTriangle2D.c0 (tri : FemmTriangle2D) : Int := tri.x2 - tri.x1

/-- Shape function $y$-gradient numerator $c_1 = x_0 - x_2$. -/
def FemmTriangle2D.c1 (tri : FemmTriangle2D) : Int := tri.x0 - tri.x2

/-- Shape function $y$-gradient numerator $c_2 = x_1 - x_0$. -/
def FemmTriangle2D.c2 (tri : FemmTriangle2D) : Int := tri.x1 - tri.x0

/-- Twice the signed area $2\Delta = b_0 c_1 - b_1 c_0$ of the 2D triangle. -/
def FemmTriangle2D.twiceArea (tri : FemmTriangle2D) : Int :=
  tri.b0 * tri.c1 - tri.b1 * tri.c0

/-- Theorem (`femm_gradient_sum_zero`):
For every 2D triangular element `tri`, the shape-function gradient coefficients sum to zero
along both axes ($b_0 + b_1 + b_2 = 0$ and $c_0 + c_1 + c_2 = 0$), guaranteeing that a constant
nodal potential produces zero magnetic flux density. -/
theorem femm_gradient_sum_zero (tri : FemmTriangle2D) :
    tri.b0 + tri.b1 + tri.b2 = 0 ∧ tri.c0 + tri.c1 + tri.c2 = 0 := by
  unfold FemmTriangle2D.b0 FemmTriangle2D.b1 FemmTriangle2D.b2
  unfold FemmTriangle2D.c0 FemmTriangle2D.c1 FemmTriangle2D.c2
  constructor <;> omega

/-- Scaled $x$-component numerator of $\nabla A_z$ (equal to $-2\Delta \cdot B_y$):
$b_0 A_0 + b_1 A_1 + b_2 A_2$. -/
def gradAxScaled (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  tri.b0 * a0 + tri.b1 * a1 + tri.b2 * a2

/-- Scaled $y$-component numerator of $\nabla A_z$ (equal to $2\Delta \cdot B_x$):
$c_0 A_0 + c_1 A_1 + c_2 A_2$. -/
def gradAyScaled (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  tri.c0 * a0 + tri.c1 * a1 + tri.c2 * a2

/-- Scaled squared magnetic flux density numerator $(2\Delta)^2 \|\mathbf{B}\|^2 = (\nabla_x A_z)^2 + (\nabla_y A_z)^2$. -/
def fluxDensitySqScaled (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  (gradAxScaled tri a0 a1 a2) * (gradAxScaled tri a0 a1 a2) +
  (gradAyScaled tri a0 a1 a2) * (gradAyScaled tri a0 a1 a2)

/-- Scaled magnetic stored energy numerator $\nu \|\nabla A_z\|^2$ inside element `tri`. -/
def evalElementMagneticEnergyScaled (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  tri.nuScaled * fluxDensitySqScaled tri a0 a1 a2

/-- Universal Gauge Invariance Theorem (`femm_gauge_invariance`):
Adding any uniform scalar gauge offset $c \in \mathbb{Z}$ to all three nodal vector potentials
$(A_0 + c, A_1 + c, A_2 + c)$ leaves both components of $\nabla A_z$ (and therefore the magnetic
flux density $\mathbf{B} = \nabla \times (A_z \hat{\mathbf{z}})$) strictly unchanged. -/
theorem femm_gauge_invariance (tri : FemmTriangle2D) (a0 a1 a2 c : Int) :
    gradAxScaled tri (a0 + c) (a1 + c) (a2 + c) = gradAxScaled tri a0 a1 a2 ∧
    gradAyScaled tri (a0 + c) (a1 + c) (a2 + c) = gradAyScaled tri a0 a1 a2 := by
  have hZero := femm_gradient_sum_zero tri
  constructor
  · unfold gradAxScaled
    rw [Int.mul_add, Int.mul_add, Int.mul_add]
    have hSumB : (tri.b0 + tri.b1 + tri.b2) * c = 0 := by
      rw [hZero.1, Int.zero_mul]
    rw [Int.add_mul, Int.add_mul] at hSumB
    omega
  · unfold gradAyScaled
    rw [Int.mul_add, Int.mul_add, Int.mul_add]
    have hSumC : (tri.c0 + tri.c1 + tri.c2) * c = 0 := by
      rw [hZero.2, Int.zero_mul]
    rw [Int.add_mul, Int.add_mul] at hSumC
    omega

/-- Corollary (`femm_energy_gauge_invariance`):
Element magnetic stored energy is strictly invariant under any uniform vector-potential shift $c$. -/
theorem femm_energy_gauge_invariance (tri : FemmTriangle2D) (a0 a1 a2 c : Int) :
    evalElementMagneticEnergyScaled tri (a0 + c) (a1 + c) (a2 + c) =
      evalElementMagneticEnergyScaled tri a0 a1 a2 := by
  have hGauge := femm_gauge_invariance tri a0 a1 a2 c
  unfold evalElementMagneticEnergyScaled fluxDensitySqScaled
  rw [hGauge.1, hGauge.2]

/-- Universal Element Energy Non-Negativity (`femm_element_energy_nonneg`):
For any triangular element with non-negative magnetic reluctivity `0 ≤ tri.nuScaled` and any
nodal potentials `a0, a1, a2 : Int`, the element magnetic energy is non-negative. -/
theorem femm_element_energy_nonneg (tri : FemmTriangle2D) (a0 a1 a2 : Int)
    (hNu : 0 ≤ tri.nuScaled) :
    0 ≤ evalElementMagneticEnergyScaled tri a0 a1 a2 := by
  unfold evalElementMagneticEnergyScaled fluxDensitySqScaled
  have hAx : 0 ≤ gradAxScaled tri a0 a1 a2 * gradAxScaled tri a0 a1 a2 :=
    int_sq_nonneg (gradAxScaled tri a0 a1 a2)
  have hAy : 0 ≤ gradAyScaled tri a0 a1 a2 * gradAyScaled tri a0 a1 a2 :=
    int_sq_nonneg (gradAyScaled tri a0 a1 a2)
  exact int_mul_nonneg tri.nuScaled _ hNu (by omega)

/-- Total magnetic energy numerator summed over a 2D finite-element mesh `mesh : List FemmTriangle2D`. -/
def evalMeshMagneticEnergyScaled (mesh : List FemmTriangle2D) (a0 a1 a2 : Int) : Int :=
  match mesh with
  | [] => 0
  | tri :: rest =>
    evalElementMagneticEnergyScaled tri a0 a1 a2 + evalMeshMagneticEnergyScaled rest a0 a1 a2

/-- Universal Mesh Energy Non-Negativity (`femm_mesh_energy_nonneg`):
Across any 2D mesh `mesh : List FemmTriangle2D` whose elements all have non-negative reluctivity,
the total assembled magnetic energy is non-negative. -/
theorem femm_mesh_energy_nonneg (mesh : List FemmTriangle2D) (a0 a1 a2 : Int)
    (hNu : ∀ tri ∈ mesh, 0 ≤ tri.nuScaled) :
    0 ≤ evalMeshMagneticEnergyScaled mesh a0 a1 a2 := by
  induction mesh with
  | nil =>
    simp [evalMeshMagneticEnergyScaled]
  | cons tri rest ih =>
    simp only [evalMeshMagneticEnergyScaled]
    have hTri : 0 ≤ evalElementMagneticEnergyScaled tri a0 a1 a2 :=
      femm_element_energy_nonneg tri a0 a1 a2 (hNu tri (List.mem_cons_self ..))
    have hRest : 0 ≤ evalMeshMagneticEnergyScaled rest a0 a1 a2 :=
      ih (fun t ht => hNu t (List.mem_cons_of_mem tri ht))
    omega

/-! ## 2. Nonlinear Silicon-Steel B-H Saturation & Chord Reluctivity (`BhReluctivityModel`) -/

/-- Nonlinear ferromagnetic B-H saturation model for silicon-steel laminations (e.g. M19 / 35JN210):
* `materialName`: lamination grade identifier,
* `nuLinear`: unsaturated linear reluctivity $\nu_0$,
* `kSat`: quadratic saturation coefficient $k_{\text{sat}} \ge 0$,
* `bKneeMilliT`: knee flux density in millitesla (e.g. $1500\,\text{mT} = 1.5\,\text{T}$). -/
structure BhReluctivityModel where
  materialName : String
  nuLinear     : Int
  kSat         : Int
  bKneeMilliT  : Int
  deriving DecidableEq, Repr

/-- Evaluates nonlinear chord reluctivity $\nu(B^2) = \nu_0 + k_{\text{sat}} B^2$. -/
def evalNonlinearReluctivity (nuLinear kSat bSq : Int) : Int :=
  nuLinear + kSat * bSq

/-- Universal Reluctivity Monotonicity Under Core Saturation (`bh_saturation_increases_reluctivity`):
For any non-negative saturation coefficient `0 ≤ kSat`, increasing squared flux density
`bSq1 ≤ bSq2` monotonically increases core reluctivity $\nu(B_1^2) \le \nu(B_2^2)$. -/
theorem bh_saturation_increases_reluctivity (nuLinear kSat bSq1 bSq2 : Int)
    (hSat : 0 ≤ kSat) (hB : bSq1 ≤ bSq2) :
    evalNonlinearReluctivity nuLinear kSat bSq1 ≤ evalNonlinearReluctivity nuLinear kSat bSq2 := by
  unfold evalNonlinearReluctivity
  have hMul : kSat * bSq1 ≤ kSat * bSq2 :=
    int_mul_le_mul_of_nonneg_left bSq1 bSq2 kSat hB hSat
  omega

/-! ## 3. $dq0$ Interior Permanent Magnet (IPM) & Synchronous Reluctance Torque (`IpmMotorSpec`) -/

/-- Synchronous $dq0$-frame parameters of an Interior Permanent Magnet (IPM) machine:
* `polePairs`: number of rotor pole pairs $p$,
* `psiPmMilliWb`: permanent magnet flux linkage $\psi_{\text{PM}}$ in milliwebers ($\text{mWb}$),
* `ldMicroH`: $d$-axis inductance $L_d$ in microhenries ($\mu\text{H}$),
* `lqMicroH`: $q$-axis inductance $L_q$ in microhenries ($\mu\text{H}$), where $L_d \le L_q$ for salient IPM rotors. -/
structure IpmMotorSpec where
  polePairs    : Int
  psiPmMilliWb : Int
  ldMicroH     : Int
  lqMicroH     : Int
  deriving DecidableEq, Repr

/-- Scaled electromagnetic torque in the rotor $dq0$ reference frame:
$T_{\text{scaled}} = p \cdot (\psi_{\text{PM}} i_q + (L_d - L_q) i_d i_q)$. -/
def evalIpmTorqueScaled (m : IpmMotorSpec) (idAmp iqAmp : Int) : Int :=
  m.polePairs * (m.psiPmMilliWb * iqAmp + (m.ldMicroH - m.lqMicroH) * idAmp * iqAmp)

/-- Universal Reluctance Torque Boost Under Field Weakening (`ipm_reluctance_torque_boost`):
For any salient IPM machine (`0 ≤ m.polePairs`, `m.ldMicroH ≤ m.lqMicroH`) driven with negative
$d$-axis demagnetizing / MTPA current (`idAmp ≤ 0`) and non-negative $q$-axis torque current
(`0 ≤ iqAmp`), the reluctance torque component is non-negative and boosts total shaft torque
above the pure permanent-magnet torque `m.polePairs * (m.psiPmMilliWb * iqAmp)`. -/
theorem ipm_reluctance_torque_boost (m : IpmMotorSpec) (idAmp iqAmp : Int)
    (hPoles : 0 ≤ m.polePairs) (hSal : m.ldMicroH ≤ m.lqMicroH)
    (hId : idAmp ≤ 0) (hIq : 0 ≤ iqAmp) :
    m.polePairs * (m.psiPmMilliWb * iqAmp) ≤ evalIpmTorqueScaled m idAmp iqAmp := by
  unfold evalIpmTorqueScaled
  have hNegSalId : (m.lqMicroH - m.ldMicroH) * idAmp ≤ 0 := by
    have hLe := int_mul_le_mul_of_nonneg_left idAmp 0 (m.lqMicroH - m.ldMicroH) hId (by omega)
    rw [Int.mul_zero] at hLe
    exact hLe
  have hSumZero : (m.lqMicroH - m.ldMicroH) * idAmp + (m.ldMicroH - m.lqMicroH) * idAmp = 0 := by
    have hAdd : ((m.lqMicroH - m.ldMicroH) + (m.ldMicroH - m.lqMicroH)) * idAmp = 0 := by
      have hSub : (m.lqMicroH - m.ldMicroH) + (m.ldMicroH - m.lqMicroH) = 0 := by omega
      rw [hSub, Int.zero_mul]
    rw [Int.add_mul] at hAdd
    exact hAdd
  have hRelProd : 0 ≤ (m.ldMicroH - m.lqMicroH) * idAmp := by omega
  have hRelTorque : 0 ≤ (m.ldMicroH - m.lqMicroH) * idAmp * iqAmp :=
    int_mul_nonneg ((m.ldMicroH - m.lqMicroH) * idAmp) iqAmp hRelProd hIq
  rw [Int.mul_add]
  have hPolesRel : 0 ≤ m.polePairs * ((m.ldMicroH - m.lqMicroH) * idAmp * iqAmp) :=
    int_mul_nonneg m.polePairs ((m.ldMicroH - m.lqMicroH) * idAmp * iqAmp) hPoles hRelTorque
  omega

/-! ## 4. Steinmetz Core Loss & Liquid-Cooled Electric Machine Signoff -/

/-- Evaluates two-term Steinmetz iron core loss (hysteresis + eddy current):
$P_{\text{core}} = k_h f B_{\text{pk}}^2 + k_e f^2 B_{\text{pk}}^2$ (in scaled milliwatts). -/
def evalSteinmetzCoreLossMw (kh ke freqHz bPeakMilliT : Int) : Int :=
  kh * freqHz * bPeakMilliT * bPeakMilliT +
  ke * freqHz * freqHz * bPeakMilliT * bPeakMilliT

/-- Theorem (`steinmetz_core_loss_nonneg`):
For non-negative Steinmetz coefficients `0 ≤ kh`, `0 ≤ ke` and electrical frequency `0 ≤ freqHz`,
the iron core loss is universally non-negative for all peak flux densities `bPeakMilliT : Int`. -/
theorem steinmetz_core_loss_nonneg (kh ke freqHz bPeakMilliT : Int)
    (hKh : 0 ≤ kh) (hKe : 0 ≤ ke) (hFreq : 0 ≤ freqHz) :
    0 ≤ evalSteinmetzCoreLossMw kh ke freqHz bPeakMilliT := by
  unfold evalSteinmetzCoreLossMw
  have hBsq : 0 ≤ bPeakMilliT * bPeakMilliT := int_sq_nonneg bPeakMilliT
  have hFsq : 0 ≤ freqHz * freqHz := int_sq_nonneg freqHz
  have hKhF : 0 ≤ kh * freqHz := int_mul_nonneg kh freqHz hKh hFreq
  have hHyst : 0 ≤ kh * freqHz * (bPeakMilliT * bPeakMilliT) :=
    int_mul_nonneg (kh * freqHz) (bPeakMilliT * bPeakMilliT) hKhF hBsq
  have hKeFsq : 0 ≤ ke * (freqHz * freqHz) :=
    int_mul_nonneg ke (freqHz * freqHz) hKe hFsq
  have hEddy : 0 ≤ ke * (freqHz * freqHz) * (bPeakMilliT * bPeakMilliT) :=
    int_mul_nonneg (ke * (freqHz * freqHz)) (bPeakMilliT * bPeakMilliT) hKeFsq hBsq
  rw [Int.mul_assoc (kh * freqHz) bPeakMilliT bPeakMilliT]
  rw [Int.mul_assoc ke freqHz freqHz]
  rw [Int.mul_assoc (ke * (freqHz * freqHz)) bPeakMilliT bPeakMilliT]
  omega

/-- Combined electromagnetic & thermal-loss signoff predicate for a liquid-cooled electric machine:
verifies that shaft torque meets `minTorqueScaled`, stator tooth peak flux density remains within
`maxSatMilliT`, and total Steinmetz core loss remains within the cooling jacket budget `maxCoreLossMw`. -/
def checkMagneticsSignoff
    (torqueScaled minTorqueScaled bPeakMilliT maxSatMilliT coreLossMw maxCoreLossMw : Int) : Bool :=
  decide (minTorqueScaled ≤ torqueScaled ∧ bPeakMilliT ≤ maxSatMilliT ∧ coreLossMw ≤ maxCoreLossMw)

/-- Soundness Theorem (`checkMagneticsSignoff_sound`):
If `checkMagneticsSignoff` returns `true`, then the torque target, tooth saturation ceiling, and
core-loss thermal budget constraints all hold simultaneously. -/
theorem checkMagneticsSignoff_sound
    (torqueScaled minTorqueScaled bPeakMilliT maxSatMilliT coreLossMw maxCoreLossMw : Int)
    (h : checkMagneticsSignoff torqueScaled minTorqueScaled bPeakMilliT maxSatMilliT coreLossMw maxCoreLossMw = true) :
    minTorqueScaled ≤ torqueScaled ∧ bPeakMilliT ≤ maxSatMilliT ∧ coreLossMw ≤ maxCoreLossMw := by
  unfold checkMagneticsSignoff at h
  exact of_decide_eq_true h

/-- Golden liquid-cooled 4-pole-pair IPM traction/dynamometer motor specification. -/
def goldenLiquidIpmMotor : IpmMotorSpec :=
  { polePairs    := 4
    psiPmMilliWb := 180
    ldMicroH     := 150
    lqMicroH     := 380 }

/-- Golden 2D FEMM stator-tooth triangular mesh element (in micrometers, $\nu = 800$). -/
def goldenStatorToothTriangle : FemmTriangle2D :=
  { x0       := 0
    y0       := 0
    x1       := 2000
    y1       := 0
    x2       := 0
    y2       := 1500
    nuScaled := 800
    jzScaled := 0 }

/-- Golden Theorem (`golden_femm_liquid_motor_magnetics_verified`):
Kernel-checked verification of the 2D FEMM stator-tooth element area, gauge invariance,
nonlinear silicon-steel reluctivity, IPM reluctance torque boost under MTPA ($i_d = -100\,\text{A}$,
$i_q = 250\,\text{A}$), and Steinmetz core-loss signoff. -/
theorem golden_femm_liquid_motor_magnetics_verified :
    goldenStatorToothTriangle.twiceArea = 3000000 ∧
    evalElementMagneticEnergyScaled goldenStatorToothTriangle 120 220 320 =
      evalElementMagneticEnergyScaled goldenStatorToothTriangle 170 270 370 ∧
    evalNonlinearReluctivity 500 2 1440000 ≤ evalNonlinearReluctivity 500 2 2890000 ∧
    goldenLiquidIpmMotor.polePairs * (goldenLiquidIpmMotor.psiPmMilliWb * 250) <
      evalIpmTorqueScaled goldenLiquidIpmMotor (-100) 250 ∧
    checkMagneticsSignoff
      (evalIpmTorqueScaled goldenLiquidIpmMotor (-100) 250)
      20000000
      1650
      1850
      (evalSteinmetzCoreLossMw 2 1 400 16)
      50000000 = true := by
  decide +kernel

/-! ## 5. Newton-Raphson Nonlinear B-H Tangent Stiffness & Convexity -/

/-- Evaluates the directional quadratic form of the Newton-Raphson tangent stiffness matrix
$K_T = K(\nu) + \Delta K_{\text{NR}}$ for a 2D nonlinear ferromagnetic element with secant
reluctivity $\nu(B^2)$ and differential reluctivity slope $d\nu / d(B^2) \ge 0$:
$$\delta A^\top K_T \delta A = \nu(B^2) \cdot \delta B^2 + 2 \frac{d\nu}{d(B^2)} \cdot (B \cdot \delta B)^2.$$ -/
def evalNewtonRaphsonTangentEnergy (nuSecant dNuDBsq deltaBSq bDotDeltaB : Int) : Int :=
  nuSecant * deltaBSq + 2 * dNuDBsq * (bDotDeltaB * bDotDeltaB)

/-- Universal Positive Semi-Definiteness of Newton-Raphson Tangent Stiffness (`femm_newton_raphson_tangent_psd`):
For any monotonic ferromagnetic B-H curve (`0 ≤ nuSecant`, `0 ≤ dNuDBsq`) and non-negative
perturbation energy (`0 ≤ deltaBSq`), the Newton-Raphson tangent operator is positive semi-definite
and strictly dominates the Picard secant stiffness energy `nuSecant * deltaBSq`. -/
theorem femm_newton_raphson_tangent_psd (nuSecant dNuDBsq deltaBSq bDotDeltaB : Int)
    (hNu : 0 ≤ nuSecant) (hSlope : 0 ≤ dNuDBsq) (hDelta : 0 ≤ deltaBSq) :
    nuSecant * deltaBSq ≤ evalNewtonRaphsonTangentEnergy nuSecant dNuDBsq deltaBSq bDotDeltaB ∧
    0 ≤ evalNewtonRaphsonTangentEnergy nuSecant dNuDBsq deltaBSq bDotDeltaB := by
  unfold evalNewtonRaphsonTangentEnergy
  have hSec : 0 ≤ nuSecant * deltaBSq := int_mul_nonneg nuSecant deltaBSq hNu hDelta
  have hSq : 0 ≤ bDotDeltaB * bDotDeltaB := int_sq_nonneg bDotDeltaB
  have h2Slope : 0 ≤ 2 * dNuDBsq := by omega
  have hTan : 0 ≤ 2 * dNuDBsq * (bDotDeltaB * bDotDeltaB) :=
    int_mul_nonneg (2 * dNuDBsq) (bDotDeltaB * bDotDeltaB) h2Slope hSq
  omega

/-! ## 6. Matrix-Free Element Action (`libCEED` / GPU Tensor Contraction `arXiv:2103.12881`) -/

/-- Evaluates the 3-node matrix-free element operator action $y_e = G_e^\top (D_e (G_e A_e))$
(`libCEED` decomposition $A = P^\top G^\top D G P$, Brown et al., `arXiv:2103.12881`) directly
from element geometry `tri` and nodal potentials `(a0, a1, a2)` without assembling a global
sparse CSR matrix. -/
def evalMatrixFreeElementAction (tri : FemmTriangle2D) (a0 a1 a2 : Int) : Int × Int × Int :=
  let gB := gradAxScaled tri a0 a1 a2
  let gC := gradAyScaled tri a0 a1 a2
  let y0 := tri.nuScaled * (tri.b0 * gB + tri.c0 * gC)
  let y1 := tri.nuScaled * (tri.b1 * gB + tri.c1 * gC)
  let y2 := tri.nuScaled * (tri.b2 * gB + tri.c2 * gC)
  (y0, y1, y2)

/-- Conservation of Nodal Currents in Matrix-Free Element Action (`femm_matrix_free_nodal_sum_zero`):
Because $b_0 + b_1 + b_2 = 0$ and $c_0 + c_1 + c_2 = 0$, the sum of the three nodal residual
contributions $y_0 + y_1 + y_2$ produced by `evalMatrixFreeElementAction` is identically zero
for every triangle `tri` and nodal potential triple `(a0, a1, a2)`. -/
theorem femm_matrix_free_nodal_sum_zero (tri : FemmTriangle2D) (a0 a1 a2 : Int) :
    let (y0, y1, y2) := evalMatrixFreeElementAction tri a0 a1 a2
    y0 + y1 + y2 = 0 := by
  dsimp only [evalMatrixFreeElementAction]
  have hZero := femm_gradient_sum_zero tri
  have hb := hZero.1
  have hc := hZero.2
  have hFactor :
      tri.nuScaled * (tri.b0 * gradAxScaled tri a0 a1 a2 + tri.c0 * gradAyScaled tri a0 a1 a2) +
      tri.nuScaled * (tri.b1 * gradAxScaled tri a0 a1 a2 + tri.c1 * gradAyScaled tri a0 a1 a2) +
      tri.nuScaled * (tri.b2 * gradAxScaled tri a0 a1 a2 + tri.c2 * gradAyScaled tri a0 a1 a2) =
      tri.nuScaled *
        ((tri.b0 + tri.b1 + tri.b2) * gradAxScaled tri a0 a1 a2 +
         (tri.c0 + tri.c1 + tri.c2) * gradAyScaled tri a0 a1 a2) := by
    simp only [Int.add_mul, Int.mul_add]
    omega
  rw [hFactor, hb, hc, Int.zero_mul, Int.zero_mul, Int.add_zero, Int.mul_zero]

private theorem femm_linear_comb_factor
    (nu b0 b1 b2 c0 c1 c2 a0 a1 a2 gB gC : Int) :
    a0 * (nu * (b0 * gB + c0 * gC)) +
    a1 * (nu * (b1 * gB + c1 * gC)) +
    a2 * (nu * (b2 * gB + c2 * gC)) =
    nu * ((b0 * a0 + b1 * a1 + b2 * a2) * gB + (c0 * a0 + c1 * a1 + c2 * a2) * gC) := by
  have hTerm : ∀ (a n b g : Int), a * (n * (b * g)) = n * (b * a * g) := by
    intro a n b g
    rw [← Int.mul_assoc a n (b * g), Int.mul_comm a n, Int.mul_assoc n a (b * g),
        ← Int.mul_assoc a b g, Int.mul_comm a b]
  simp only [Int.mul_add, Int.add_mul, hTerm]
  omega

/-- Matrix-Free Energy Equivalence Theorem (`femm_matrix_free_energy_identity`):
The inner product $a_0 y_0 + a_1 y_1 + a_2 y_2$ of the nodal vector potential with the
`libCEED` matrix-free operator action equals `evalElementMagneticEnergyScaled tri a0 a1 a2`. -/
theorem femm_matrix_free_energy_identity (tri : FemmTriangle2D) (a0 a1 a2 : Int) :
    let (y0, y1, y2) := evalMatrixFreeElementAction tri a0 a1 a2
    a0 * y0 + a1 * y1 + a2 * y2 = evalElementMagneticEnergyScaled tri a0 a1 a2 := by
  dsimp only [evalMatrixFreeElementAction]
  rw [femm_linear_comb_factor]
  rfl

/-! ## 7. Global Mesh Nodal Residual Equilibrium (`evalGlobalNodalResidual`) -/

/-- Alias `evalLibCeedElementOp` for `evalMatrixFreeElementAction` (`libCEED` $G_e^\top D_e G_e$ element operator). -/
abbrev evalLibCeedElementOp := evalMatrixFreeElementAction

/-- A 2D triangular finite element together with its three global mesh vertex indices `(n0, n1, n2)`
and its three internal nodal residual contributions `(f0, f1, f2)` computed by `evalLibCeedElementOp`. -/
structure MeshElementResidual2D where
  n0 : Nat
  n1 : Nat
  n2 : Nat
  f0 : Int
  f1 : Int
  f2 : Int
  deriving DecidableEq, Repr

/-- A 2D triangular mesh element connecting global vertex indices `(n0, n1, n2)` with geometry `tri`. -/
structure FemmMeshElement2D where
  n0  : Nat
  n1  : Nat
  n2  : Nat
  tri : FemmTriangle2D
  deriving DecidableEq, Repr

/-- Evaluates the element nodal residual record `MeshElementResidual2D` for a mesh triangle `elem`
under a global nodal vector-potential field `nodalA : Nat → Int`. -/
def evalElementResidual2D (elem : FemmMeshElement2D) (nodalA : Nat → Int) : MeshElementResidual2D :=
  let (f0, f1, f2) := evalLibCeedElementOp elem.tri (nodalA elem.n0) (nodalA elem.n1) (nodalA elem.n2)
  { n0 := elem.n0, n1 := elem.n1, n2 := elem.n2, f0 := f0, f1 := f1, f2 := f2 }

/-- Scatters (`P_e^\top`) the internal nodal forces `(f0, f1, f2)` of an element residual `er`
onto global mesh vertex `nodeIdx : Nat`. -/
def evalElementNodeContribution (er : MeshElementResidual2D) (nodeIdx : Nat) : Int :=
  (if er.n0 == nodeIdx then er.f0 else 0) +
  (if er.n1 == nodeIdx then er.f1 else 0) +
  (if er.n2 == nodeIdx then er.f2 else 0)

/-- Assembles the global nodal magnetostatic residual $\sum_{e \in \mathcal{T}} (P_e^\top G_e^\top D_e G_e P_e A)_{\text{nodeIdx}}$
at global mesh vertex `nodeIdx : Nat` across an entire 2D finite-element mesh `mesh : List FemmMeshElement2D`. -/
def evalGlobalNodalResidual
    (mesh : List FemmMeshElement2D) (nodalA : Nat → Int) (nodeIdx : Nat) : Int :=
  match mesh with
  | [] => 0
  | elem :: rest =>
    evalElementNodeContribution (evalElementResidual2D elem nodalA) nodeIdx +
    evalGlobalNodalResidual rest nodalA nodeIdx

/-- Sums all internal nodal residuals $\sum_{e \in \mathcal{T}} (f_{e,0} + f_{e,1} + f_{e,2})$
across a 2D finite-element mesh `mesh`. -/
def evalMeshTotalResidualSum (mesh : List FemmMeshElement2D) (nodalA : Nat → Int) : Int :=
  match mesh with
  | [] => 0
  | elem :: rest =>
    let er := evalElementResidual2D elem nodalA
    (er.f0 + er.f1 + er.f2) + evalMeshTotalResidualSum rest nodalA

/-- **Discrete Divergence Theorem / Global Nodal Residual Conservation (`femm_global_residual_sum_zero`)**:
For every mesh element `elem`, every 2D mesh `mesh : List FemmMeshElement2D`, and every global nodal
vector potential field `nodalA : Nat → Int`, the sum of internal nodal residuals over each element
and over the entire mesh is identically zero. -/
theorem femm_global_residual_sum_zero
    (elem : FemmMeshElement2D) (mesh : List FemmMeshElement2D) (nodalA : Nat → Int) :
    let er := evalElementResidual2D elem nodalA
    (er.f0 + er.f1 + er.f2 = 0) ∧ evalMeshTotalResidualSum mesh nodalA = 0 := by
  constructor
  · dsimp only [evalElementResidual2D, evalLibCeedElementOp]
    exact femm_matrix_free_nodal_sum_zero elem.tri (nodalA elem.n0) (nodalA elem.n1) (nodalA elem.n2)
  · induction mesh with
    | nil => rfl
    | cons hd tl ih =>
      dsimp only [evalMeshTotalResidualSum, evalElementResidual2D, evalLibCeedElementOp]
      have hHd := femm_matrix_free_nodal_sum_zero hd.tri (nodalA hd.n0) (nodalA hd.n1) (nodalA hd.n2)
      dsimp only at hHd
      rw [hHd, ih, Int.add_zero]

/-- Helper lemma: `evalLibCeedElementOp` is invariant under adding a uniform scalar gauge shift `c`
to all three nodal vector potentials. -/
theorem femm_libceed_element_gauge_invariant (tri : FemmTriangle2D) (a0 a1 a2 c : Int) :
    evalLibCeedElementOp tri (a0 + c) (a1 + c) (a2 + c) =
      evalLibCeedElementOp tri a0 a1 a2 := by
  have hGauge := femm_gauge_invariance tri a0 a1 a2 c
  unfold evalLibCeedElementOp evalMatrixFreeElementAction
  rw [hGauge.1, hGauge.2]

/-- Helper lemma: `evalElementResidual2D` is invariant under adding a uniform scalar gauge shift `c`
to the global nodal vector-potential field `nodalA`. -/
theorem femm_element_residual_gauge_invariant
    (elem : FemmMeshElement2D) (nodalA : Nat → Int) (c : Int) :
    evalElementResidual2D elem (fun n => nodalA n + c) =
      evalElementResidual2D elem nodalA := by
  unfold evalElementResidual2D
  rw [femm_libceed_element_gauge_invariant elem.tri (nodalA elem.n0) (nodalA elem.n1) (nodalA elem.n2) c]

/-- **Global Nodal Residual Gauge Invariance (`femm_global_equilibrium_gauge_invariant`)**:
Adding a constant scalar gauge offset $c \in \mathbb{Z}$ to all nodal vector potentials
$A_i \mapsto A_i + c$ leaves the assembled global nodal residual at every mesh vertex `nodeIdx : Nat`
strictly unchanged across any 2D mesh `mesh : List FemmMeshElement2D`. -/
theorem femm_global_equilibrium_gauge_invariant
    (mesh : List FemmMeshElement2D) (nodalA : Nat → Int) (c : Int) (nodeIdx : Nat) :
    evalGlobalNodalResidual mesh (fun n => nodalA n + c) nodeIdx =
      evalGlobalNodalResidual mesh nodalA nodeIdx := by
  induction mesh with
  | nil => rfl
  | cons elem rest ih =>
    dsimp only [evalGlobalNodalResidual]
    rw [femm_element_residual_gauge_invariant elem nodalA c, ih]

/-! ## 8. Maxwell Stress Tensor (`MST`) Air-Gap Torque Integration (`evalMaxwellStressTorque`) -/

/-- A circumferential quadrature sample along the stator-rotor air-gap contour $\Gamma_{\text{ag}}$
for Maxwell Stress Tensor (`MST`) electromagnetic torque integration
$T_{\text{MST}} = \frac{L_{\text{stk}} r_{\text{ag}}^2}{\mu_0} \oint_{\Gamma_{\text{ag}}} B_r(\theta) B_\theta(\theta)\,d\theta$:
* `bRadialMt`: radial magnetic flux density $B_r(\theta)$ in millitesla ($\text{mT}$),
* `bTangentialMt`: tangential (circumferential) magnetic flux density $B_\theta(\theta)$ in millitesla ($\text{mT}$),
* `arcWeight`: non-negative quadrature arc-length / stack-volume scaling weight $w_k \ge 0$. -/
structure AirGapHarmonicSample where
  bRadialMt     : Int
  bTangentialMt : Int
  arcWeight     : Int
  deriving DecidableEq, Repr

/-- Evaluates the Maxwell Stress Tensor shear contribution $w_k \cdot B_{r,k} \cdot B_{\theta,k}$
of a single circumferential air-gap quadrature sample. -/
def evalSampleMaxwellShear (s : AirGapHarmonicSample) : Int :=
  s.arcWeight * s.bRadialMt * s.bTangentialMt

/-- Integrates the Maxwell Stress Tensor (`MST`) electromagnetic torque across a list of
circumferential air-gap quadrature samples:
$$T_{\text{MST}} = \sum_{k} w_k \, B_{r,k} \, B_{\theta,k}.$$ -/
def evalMaxwellStressTorque : List AirGapHarmonicSample → Int
  | [] => 0
  | s :: rest => evalSampleMaxwellShear s + evalMaxwellStressTorque rest

/-- Scales the radial rotor excitation field by `kRadial` and tangential stator armature field by
`kTan` across an air-gap sample contour. -/
def scaleAirGapContour (kRadial kTan : Int) : List AirGapHarmonicSample → List AirGapHarmonicSample
  | [] => []
  | s :: rest =>
    { bRadialMt     := kRadial * s.bRadialMt
      bTangentialMt := kTan * s.bTangentialMt
      arcWeight     := s.arcWeight } :: scaleAirGapContour kRadial kTan rest

/-- **Bilinear Scaling of Maxwell Stress Tensor Air-Gap Torque (`maxwell_stress_torque_bilinear_scale`)**:
Scaling the radial rotor flux density by $k_r$ and tangential stator current flux density by $k_q$
scales the integrated Maxwell Stress Tensor air-gap torque by $k_r \cdot k_q$. -/
theorem maxwell_stress_torque_bilinear_scale
    (kRadial kTan : Int) (samples : List AirGapHarmonicSample) :
    evalMaxwellStressTorque (scaleAirGapContour kRadial kTan samples) =
      (kRadial * kTan) * evalMaxwellStressTorque samples := by
  induction samples with
  | nil =>
    dsimp only [scaleAirGapContour, evalMaxwellStressTorque]
    omega
  | cons s rest ih =>
    dsimp only [scaleAirGapContour, evalMaxwellStressTorque, evalSampleMaxwellShear]
    rw [ih]
    grind

/-- **Maxwell Stress Tensor Torque Positivity & Monotonicity (`maxwell_stress_torque_monotone`)**:
For any air-gap contour sample with non-negative quadrature weight (`0 ≤ arcWeight`) and non-negative
radial rotor flux density (`0 ≤ bRadialMt`), increasing the quadrature-aligned tangential stator
flux density (`0 ≤ bTan1` and `bTan1 ≤ bTan2`) produces non-negative torque and monotonically
increases the integrated Maxwell Stress Tensor air-gap torque. -/
theorem maxwell_stress_torque_monotone
    (bRadialMt bTan1 bTan2 arcWeight : Int)
    ( rest : List AirGapHarmonicSample)
    (hWeight : 0 ≤ arcWeight)
    (hRad    : 0 ≤ bRadialMt)
    (hTanPos : 0 ≤ bTan1)
    (hTanLe  : bTan1 ≤ bTan2) :
    let s1 : AirGapHarmonicSample := { bRadialMt := bRadialMt, bTangentialMt := bTan1, arcWeight := arcWeight }
    let s2 : AirGapHarmonicSample := { bRadialMt := bRadialMt, bTangentialMt := bTan2, arcWeight := arcWeight }
    0 ≤ evalSampleMaxwellShear s1 ∧
    evalMaxwellStressTorque (s1 :: rest) ≤ evalMaxwellStressTorque (s2 :: rest) := by
  dsimp only [evalMaxwellStressTorque, evalSampleMaxwellShear]
  have hWR : 0 ≤ arcWeight * bRadialMt := int_mul_nonneg arcWeight bRadialMt hWeight hRad
  have hShearPos : 0 ≤ arcWeight * bRadialMt * bTan1 :=
    int_mul_nonneg (arcWeight * bRadialMt) bTan1 hWR hTanPos
  have hShearMono : arcWeight * bRadialMt * bTan1 ≤ arcWeight * bRadialMt * bTan2 :=
    int_mul_le_mul_of_nonneg_left bTan1 bTan2 (arcWeight * bRadialMt) hTanLe hWR
  omega

end Obend.Hardware.Magnetics
end

