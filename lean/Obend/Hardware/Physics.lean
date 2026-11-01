module
/-
# Obend.Hardware.Physics — First-Principles PDE Discretization, PRIMA Passive MOR & Open Nanofab Metrology

Formalizes **first-principles semiconductor & thermal PDE discretization**, **PRIMA passive
model-order reduction** (for Lanyon AI multiphysics-to-SPICE/Cauer interoperability), and
**open nanofab / neofab computational metrology** (`HackerFab`, `AtomicSemi`, `FabuBlox`, `FABμBOX`):

1. **Semiconductor Poisson-Drift-Diffusion (PDD) & Finite-Volume Continuity Conservation**:
   - Models 1D/2D finite-volume semiconductor control volumes (`PddControlVolume`) with carrier
     densities, Shockley-Read-Hall / Auger net recombination, and Scharfetter-Gummel interface fluxes,
   - Proves **`pdd_discrete_flux_telescopes`** and **`pdd_total_charge_conserved`**: internal
     interface fluxes $+J_{i,i+1}$ and $-J_{i,i+1}$ cancel identically across adjacent cells, so
     total interior charge change equals net terminal current minus integrated recombination.
2. **Fourier Heat PDE to Cauer RC Model-Order Reduction via PRIMA Congruence Projection**:
   - Models a symmetric positive-semidefinite fine-mesh thermal conductance operator
     (`FineThermalOperator`) with quadratic dissipation $E(x_1, x_2) = g_1 x_1^2 + g_2 x_2^2 + g_{12}(x_1 - x_2)^2$,
   - Proves **`fine_thermal_operator_dissipative`** ($E(x_1, x_2) \ge 0$ for all $x_1, x_2 \in \mathbb{Z}$)
     and **`prima_preserves_passivity`** (congruence projection $V^\top G V$ onto a reduced Cauer
     macromodel strictly preserves non-negative energy dissipation $\hat{g} z^2 \ge 0$),
   - Formalizes the a posteriori PDE-to-lumped state truncation error bound (`checkMorErrorBound`,
     `mor_error_bound_sound`).
3. **Open Nanofab / Neofab Process & Computational Metrology (`HackerFab` / `AtomicSemi` / `FabuBlox` / `FABμBOX`)**:
   - Models maskless UV DLP / i-line photolithography (`LithoStepperSpec`), Rayleigh minimum critical
     dimension (`rayleighCdNm`), Depth of Focus (`rayleighDofNm`), and wavelength monotonicity
     (`rayleigh_cd_monotone_wavelength`),
   - Models self-limiting Atomic Layer Deposition (`AldProcessSpec`, `evalAldFilmThicknessPm`),
     proving **`ald_saturation_invariant`** (once precursor dose reaches saturation `doseMs ≥ satDoseMs`,
     extra precursor dose does not increase film thickness beyond `cycles * gpcPm`) and refusing
     parasitic CVD growth when `purgeMs < minPurgeMs`,
   - Models 4-point-probe sheet resistance ($R_s = \frac{\pi}{\ln 2} \frac{V}{I} \approx 4.532 \frac{V}{I}$)
     and optical reflectometry film-thickness signoff (`checkNeofabMetrology`, `neofabMetrology_sound`).
-/
public import Obend.Hardware.Thermal
@[expose] public section

namespace Obend.Hardware.Physics
open Obend.Hardware.Thermal
set_option autoImplicit false

/-! ## 1. Semiconductor Poisson-Drift-Diffusion (PDD) & Finite-Volume Continuity Conservation -/

/-- A 1D/2D finite-volume control cell for the semiconductor Poisson-Drift-Diffusion (PDD) PDE system:
* `cellIdx`: mesh cell index $i$,
* `nPermille`: normalized electron concentration $n_i$,
* `pPermille`: normalized hole concentration $p_i$,
* `dopingNetPermille`: ionized net dopant concentration $N_{D,i}^+ - N_{A,i}^-$,
* `recombRate`: integrated net Shockley-Read-Hall (SRH) + Auger recombination rate $R_i$ in cell $i$,
* `fluxIn`: Scharfetter-Gummel current flux $J_{i-1/2}$ entering through the left interface,
* `fluxOut`: Scharfetter-Gummel current flux $J_{i+1/2}$ leaving through the right interface. -/
structure PddControlVolume where
  cellIdx           : Nat
  nPermille         : Int
  pPermille         : Int
  dopingNetPermille : Int
  recombRate        : Int
  fluxIn            : Int
  fluxOut           : Int
  deriving DecidableEq, Repr

/-- Local space-charge density $\rho_i = p_i - n_i + (N_{D,i}^+ - N_{A,i}^-)$ on the right-hand side
of the discretized Poisson equation $-\nabla \cdot (\varepsilon \nabla \psi)_i = q \rho_i$. -/
def evalSpaceChargePermille (cell : PddControlVolume) : Int :=
  cell.pPermille - cell.nPermille + cell.dopingNetPermille

/-- Theorem (`charge_neutral_equilibrium_zero_rhs`):
When a control volume is in local charge neutrality ($n_i - p_i = N_{D,i}^+ - N_{A,i}^-$), the
Poisson right-hand side space-charge density vanishes identically (`evalSpaceChargePermille cell = 0`). -/
theorem charge_neutral_equilibrium_zero_rhs
    (cell : PddControlVolume)
    (hNeutral : cell.nPermille - cell.pPermille = cell.dopingNetPermille) :
    evalSpaceChargePermille cell = 0 := by
  dsimp only [evalSpaceChargePermille]
  omega

/-- Discrete finite-volume carrier continuity time-derivative in a single control volume:
$$\frac{\Delta Q_i}{\Delta t} = J_{\text{in},i} - J_{\text{out},i} - R_i.$$ -/
def evalCellContinuityRate (cell : PddControlVolume) : Int :=
  cell.fluxIn - cell.fluxOut - cell.recombRate

/-- Build a 3-cell finite-volume PDD mesh chain with terminal boundary fluxes `jAnode`, `jCathode`,
shared interior Scharfetter-Gummel interface fluxes `j01`, `j12`, and cell recombination rates
`r0`, `r1`, `r2`. -/
def makeThreeCellPddChain
    (jAnode j01 j12 jCathode : Int)
    (r0 r1 r2 : Int) : PddControlVolume × PddControlVolume × PddControlVolume :=
  let c0 : PddControlVolume :=
    { cellIdx := 0, nPermille := 1000, pPermille := 10, dopingNetPermille := 990
    , recombRate := r0, fluxIn := jAnode, fluxOut := j01 }
  let c1 : PddControlVolume :=
    { cellIdx := 1, nPermille := 500, pPermille := 500, dopingNetPermille := 0
    , recombRate := r1, fluxIn := j01, fluxOut := j12 }
  let c2 : PddControlVolume :=
    { cellIdx := 2, nPermille := 10, pPermille := 1000, dopingNetPermille := -990
    , recombRate := r2, fluxIn := j12, fluxOut := jCathode }
  (c0, c1, c2)

/-- Theorem (`pdd_discrete_flux_telescopes`):
Across two adjacent finite-volume control cells `cLeft` and `cRight` sharing a conservative
Scharfetter-Gummel interface flux (`cLeft.fluxOut = cRight.fluxIn`), the internal interface flux
cancels identically when summing the two cells' continuity rates:
$$\frac{\Delta Q_{\text{left}}}{\Delta t} + \frac{\Delta Q_{\text{right}}}{\Delta t}
  = J_{\text{in,left}} - J_{\text{out,right}} - (R_{\text{left}} + R_{\text{right}}).$$ -/
theorem pdd_discrete_flux_telescopes
    (cLeft cRight : PddControlVolume)
    (hInterface : cLeft.fluxOut = cRight.fluxIn) :
    evalCellContinuityRate cLeft + evalCellContinuityRate cRight =
      cLeft.fluxIn - cRight.fluxOut - (cLeft.recombRate + cRight.recombRate) := by
  dsimp only [evalCellContinuityRate]
  omega

/-- Theorem (`pdd_total_charge_conserved`):
For any 3-cell finite-volume PDD mesh chain with shared interior Scharfetter-Gummel fluxes
`j01` and `j12`, the total carrier continuity rate across the entire domain depends ONLY on the
external terminal currents (`jAnode - jCathode`) and total bulk recombination (`r0 + r1 + r2`),
and is strictly invariant to the internal interface fluxes `j01` and `j12`! -/
theorem pdd_total_charge_conserved
    (jAnode j01 j12 jCathode r0 r1 r2 : Int) :
    let (c0, c1, c2) := makeThreeCellPddChain jAnode j01 j12 jCathode r0 r1 r2
    evalCellContinuityRate c0 + evalCellContinuityRate c1 + evalCellContinuityRate c2 =
      jAnode - jCathode - (r0 + r1 + r2) := by
  dsimp only [makeThreeCellPddChain, evalCellContinuityRate]
  omega

/-- Theorem (`pdd_steady_state_recomb_balances_terminal_current`):
In steady state ($\frac{\Delta Q_i}{\Delta t} = 0$ in every cell), the net terminal current difference
$J_{\text{anode}} - J_{\text{cathode}}$ equals the total integrated SRH/Auger recombination
$R_0 + R_1 + R_2$. -/
theorem pdd_steady_state_recomb_balances_terminal_current
    (jAnode j01 j12 jCathode r0 r1 r2 : Int)
    (hSs0 : evalCellContinuityRate (makeThreeCellPddChain jAnode j01 j12 jCathode r0 r1 r2).1 = 0)
    (hSs1 : evalCellContinuityRate (makeThreeCellPddChain jAnode j01 j12 jCathode r0 r1 r2).2.1 = 0)
    (hSs2 : evalCellContinuityRate (makeThreeCellPddChain jAnode j01 j12 jCathode r0 r1 r2).2.2 = 0) :
    jAnode - jCathode = r0 + r1 + r2 := by
  dsimp only [makeThreeCellPddChain, evalCellContinuityRate] at hSs0 hSs1 hSs2
  omega

/-! ## 2. Fourier Heat PDE to Cauer RC Model-Order Reduction via PRIMA Congruence Projection -/

/-- Symmetric positive-semidefinite discretized Fourier heat-conduction operator (`G` matrix):
$$G = \begin{pmatrix} g_1 + g_{12} & -g_{12} \\ -g_{12} & g_2 + g_{12} \end{pmatrix}$$
with ambient boundary conductances $g_1, g_2 \ge 0$ and inter-node diffusive coupling $g_{12} \ge 0$
(in micro-watts per kelvin $\mu\text{W/K}$). -/
structure FineThermalOperator where
  g1  : Int
  g2  : Int
  g12 : Int
  deriving DecidableEq, Repr

/-- Quadratic thermal power dissipation form $E(x_1, x_2) = x^\top G x$ of `FineThermalOperator`
at nodal temperature elevations $(x_1, x_2)$:
$$x^\top G x = g_1 x_1^2 + g_2 x_2^2 + g_{12} (x_1 - x_2)^2.$$ -/
def evalFineThermalEnergy (op : FineThermalOperator) (x1 x2 : Int) : Int :=
  op.g1 * (x1 * x1) + op.g2 * (x2 * x2) + op.g12 * ((x1 - x2) * (x1 - x2))

/-- Theorem (`fine_thermal_operator_dissipative`):
For any non-negative physical conductances `0 ≤ op.g1`, `0 ≤ op.g2`, `0 ≤ op.g12` and any nodal
temperature state `(x1, x2) : Int × Int`, the discretized Fourier heat operator is strictly
dissipative (positive semidefinite):
$$0 \le E(x_1, x_2) = x^\top G x.$$ -/
theorem fine_thermal_operator_dissipative
    (op : FineThermalOperator) (x1 x2 : Int)
    (hg1  : 0 ≤ op.g1)
    (hg2  : 0 ≤ op.g2)
    (hg12 : 0 ≤ op.g12) :
    0 ≤ evalFineThermalEnergy op x1 x2 := by
  dsimp only [evalFineThermalEnergy]
  have hSq1 : 0 ≤ x1 * x1 := int_sq_nonneg x1
  have hSq2 : 0 ≤ x2 * x2 := int_sq_nonneg x2
  have hSq12 : 0 ≤ (x1 - x2) * (x1 - x2) := int_sq_nonneg (x1 - x2)
  have hTerm1 : 0 ≤ op.g1 * (x1 * x1) := int_mul_nonneg op.g1 (x1 * x1) hg1 hSq1
  have hTerm2 : 0 ≤ op.g2 * (x2 * x2) := int_mul_nonneg op.g2 (x2 * x2) hg2 hSq2
  have hTerm12 : 0 ≤ op.g12 * ((x1 - x2) * (x1 - x2)) :=
    int_mul_nonneg op.g12 ((x1 - x2) * (x1 - x2)) hg12 hSq12
  omega

/-- PRIMA congruence projection $\hat{g} = V^\top G V$ of a 2D `FineThermalOperator` onto a 1D
Krylov / POD basis vector $V = (v_1, v_2)^\top$:
$$\hat{g} = g_1 v_1^2 + g_2 v_2^2 + g_{12} (v_1 - v_2)^2.$$ -/
def primaProject1D (op : FineThermalOperator) (v1 v2 : Int) : Int :=
  evalFineThermalEnergy op v1 v2

/-- Thermal dissipation $\hat{E}(z) = \hat{g} \cdot z^2$ of the PRIMA reduced-order Cauer macromodel
at reduced coordinate $z \in \mathbb{Z}$. -/
def evalReducedThermalEnergy (op : FineThermalOperator) (v1 v2 z : Int) : Int :=
  primaProject1D op v1 v2 * (z * z)

/-- Theorem (`prima_preserves_passivity`):
PRIMA congruence projection ($V^\top G V$) unconditionally preserves passivity: for ANY projection
basis $(v_1, v_2) \in \mathbb{Z}^2$ and ANY reduced coordinate $z \in \mathbb{Z}$, both the reduced
conductance $\hat{g}$ and the reduced macromodel energy dissipation $\hat{E}(z) = \hat{g} z^2$ are
non-negative (`0 ≤ primaProject1D op v1 v2` and `0 ≤ evalReducedThermalEnergy op v1 v2 z`).
Consequently, coupling the reduced Cauer thermal macromodel to a nonlinear SPICE circuit can NEVER
create artificial energy or spurious instability! -/
theorem prima_preserves_passivity
    (op : FineThermalOperator) (v1 v2 z : Int)
    (hg1  : 0 ≤ op.g1)
    (hg2  : 0 ≤ op.g2)
    (hg12 : 0 ≤ op.g12) :
    0 ≤ primaProject1D op v1 v2 ∧
    0 ≤ evalReducedThermalEnergy op v1 v2 z ∧
    0 ≤ evalFineThermalEnergy op (v1 * z) (v2 * z) := by
  dsimp only [primaProject1D, evalReducedThermalEnergy]
  have hGhat : 0 ≤ evalFineThermalEnergy op v1 v2 :=
    fine_thermal_operator_dissipative op v1 v2 hg1 hg2 hg12
  have hSqZ : 0 ≤ z * z := int_sq_nonneg z
  have hEnergy : 0 ≤ evalFineThermalEnergy op v1 v2 * (z * z) :=
    int_mul_nonneg (evalFineThermalEnergy op v1 v2) (z * z) hGhat hSqZ
  have hFull : 0 ≤ evalFineThermalEnergy op (v1 * z) (v2 * z) :=
    fine_thermal_operator_dissipative op (v1 * z) (v2 * z) hg1 hg2 hg12
  exact ⟨hGhat, hEnergy, hFull⟩

/-- A posteriori PDE-to-lumped Model-Order Reduction (MOR) error certificate:
Given the PDE residual norm $\|r(\hat{x})\| = \text{residualNorm}$, coercivity (minimum eigenvalue)
lower bound $\lambda_{\min} > 0$, and maximum allowable temperature error `maxErrorMk`, verifies the
Lax-Milgram / Babuška-Brezzi bound $\|r(\hat{x})\| \le \text{maxErrorMk} \cdot \lambda_{\min}$. -/
def checkMorErrorBound (residualNorm lambdaMin maxErrorMk : Nat) : Bool :=
  decide (lambdaMin > 0) && decide (residualNorm ≤ maxErrorMk * lambdaMin)

/-- Theorem (`mor_error_bound_sound`):
If `checkMorErrorBound residualNorm lambdaMin maxErrorMk = true`, then the coercivity constant is
strictly positive (`lambdaMin > 0`), the residual satisfies `residualNorm ≤ maxErrorMk * lambdaMin`,
and `residualNorm / lambdaMin ≤ (maxErrorMk * lambdaMin) / lambdaMin`. -/
theorem mor_error_bound_sound
    (residualNorm lambdaMin maxErrorMk : Nat)
    (hOk : checkMorErrorBound residualNorm lambdaMin maxErrorMk = true) :
    lambdaMin > 0 ∧
    residualNorm ≤ maxErrorMk * lambdaMin ∧
    residualNorm / lambdaMin ≤ (maxErrorMk * lambdaMin) / lambdaMin := by
  unfold checkMorErrorBound at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  have hDiv : residualNorm / lambdaMin ≤ (maxErrorMk * lambdaMin) / lambdaMin :=
    Nat.div_le_div_right hOk.2
  exact ⟨hOk.1, hOk.2, hDiv⟩

/-! ## 3. Open Nanofab / Neofab Process & Computational Metrology (`HackerFab` / `AtomicSemi` / `FabuBlox` / `FABμBOX`) -/

/-- Optical lithography exposure system specification (covering maskless UV DLP steppers like
`HackerFab`, `AtomicSemi`, `FABμBOX`, and i-line / DUV projection steppers):
* `toolName`: lithography platform identifier,
* `wavelengthNm`: illumination wavelength $\lambda$ in nanometers (`405` UV DLP, `365` i-line, `248` KrF, `193` ArF),
* `naPermille`: numerical aperture $\text{NA} \times 1000$ (e.g. `450` for $\text{NA} = 0.45$),
* `k1Permille`: Rayleigh process factor $k_1 \times 1000$ (theoretical coherent limit $\ge 250$; single-exposure $\approx 500$),
* `k2Permille`: Rayleigh depth-of-focus factor $k_2 \times 1000$ ($\approx 500$). -/
structure LithoStepperSpec where
  toolName     : String
  wavelengthNm : Nat
  naPermille   : Nat
  k1Permille   : Nat
  k2Permille   : Nat
  deriving DecidableEq, Repr

/-- Rayleigh minimum resolvable feature size (Critical Dimension $\text{CD}$, in nanometers):
$$\text{CD}_{\text{nm}} = \frac{k_1 \cdot \lambda_{\text{nm}}}{\text{NA}}.$$ -/
def rayleighCdNm (spec : LithoStepperSpec) : Nat :=
  (spec.k1Permille * spec.wavelengthNm) / spec.naPermille

/-- Rayleigh Depth of Focus ($\text{DOF}$, in nanometers):
$$\text{DOF}_{\text{nm}} = \frac{k_2 \cdot \lambda_{\text{nm}} \cdot 1000}{\text{NA}^2}.$$ -/
def rayleighDofNm (spec : LithoStepperSpec) : Nat :=
  (spec.k2Permille * spec.wavelengthNm * 1000) / (spec.naPermille * spec.naPermille)

/-- Theorem (`rayleigh_cd_monotone_wavelength`):
For fixed numerical aperture `naPermille` and process factor `k1Permille`, reducing the exposure
wavelength $\lambda_1 \le \lambda_2$ (e.g. moving from $405\,\text{nm}$ UV DLP to $365\,\text{nm}$
i-line or $248\,\text{nm}$ DUV) monotonically reduces (improves) the minimum resolvable feature size
`rayleighCdNm`. -/
theorem rayleigh_cd_monotone_wavelength
    (s1 s2 : LithoStepperSpec)
    (hSameNa : s1.naPermille = s2.naPermille)
    (hSameK1 : s1.k1Permille = s2.k1Permille)
    (hWave : s1.wavelengthNm ≤ s2.wavelengthNm) :
    rayleighCdNm s1 ≤ rayleighCdNm s2 := by
  dsimp only [rayleighCdNm]
  rw [← hSameNa, ← hSameK1]
  have hNum : s1.k1Permille * s1.wavelengthNm ≤ s1.k1Permille * s2.wavelengthNm :=
    Nat.mul_le_mul_left s1.k1Permille hWave
  exact Nat.div_le_div_right hNum

/-- Self-limiting Atomic Layer Deposition (ALD) process specification (e.g., thermal $\text{Al}_2\text{O}_3$
from TMA + $\text{H}_2\text{O}$ or $\text{HfO}_2$ high-$k$ gate dielectric in `FabuBlox` / `FABμBOX`):
* `filmName`: dielectric or barrier film name,
* `gpcPm`: self-saturated Growth-Per-Cycle in picometers (`110 pm/cycle` = `1.1 Å/cycle` for $\text{Al}_2\text{O}_3$),
* `satDoseMs`: minimum precursor pulse duration ($\text{ms}$) required to reach 100% surface monolayer saturation,
* `minPurgeMs`: minimum inert $\text{N}_2$/$\text{Ar}$ purge time ($\text{ms}$) required to evacuate unabsorbed precursor,
* `aldWindowMinC`, `aldWindowMaxC`: self-limiting thermal ALD temperature window ($^\circ\text{C}$). -/
structure AldProcessSpec where
  filmName      : String
  gpcPm         : Nat
  satDoseMs     : Nat
  minPurgeMs    : Nat
  aldWindowMinC : Nat
  aldWindowMaxC : Nat
  deriving DecidableEq, Repr

/-- Verify that an ALD recipe operates strictly inside the self-limiting surface-saturation regime
(adequate precursor dose, adequate purge to prevent parasitic CVD reaction, and chamber temperature
within the thermal ALD window). -/
def checkAldSelfLimiting (spec : AldProcessSpec) (doseMs purgeMs chamberTempC : Nat) : Bool :=
  decide (spec.satDoseMs ≤ doseMs) &&
  decide (spec.minPurgeMs ≤ purgeMs) &&
  decide (spec.aldWindowMinC ≤ chamberTempC) &&
  decide (chamberTempC ≤ spec.aldWindowMaxC)

/-- Evaluate the deposited ALD film thickness (in picometers $\text{pm}$) after `cycles` ALD cycles:
* In the saturated self-limiting regime (`spec.satDoseMs ≤ doseMs`), every cycle deposits
  exactly one saturated monolayer (`gpcPm`), independent of excess precursor dose!
* In the sub-saturated regime (`doseMs < spec.satDoseMs`), growth scales proportionally to `doseMs / satDoseMs`. -/
def evalAldFilmThicknessPm (spec : AldProcessSpec) (cycles doseMs : Nat) : Nat :=
  if spec.satDoseMs ≤ doseMs then
    cycles * spec.gpcPm
  else
    (cycles * spec.gpcPm * doseMs) / spec.satDoseMs

/-- Theorem (`ald_saturation_invariant`):
Once the precursor pulse duration reaches surface monolayer saturation (`spec.satDoseMs ≤ dose1`
and `spec.satDoseMs ≤ dose2`), any two precursor doses `dose1` and `dose2` produce the EXACT same
film thickness `cycles * spec.gpcPm`! This formalizes the defining physical property of ALD:
conformal, digital thickness control determined solely by cycle count `cycles`. -/
theorem ald_saturation_invariant
    (spec : AldProcessSpec) (cycles dose1 dose2 : Nat)
    (hSat1 : spec.satDoseMs ≤ dose1)
    (hSat2 : spec.satDoseMs ≤ dose2) :
    evalAldFilmThicknessPm spec cycles dose1 = evalAldFilmThicknessPm spec cycles dose2 ∧
    evalAldFilmThicknessPm spec cycles dose1 = cycles * spec.gpcPm := by
  dsimp only [evalAldFilmThicknessPm]
  rw [if_pos hSat1, if_pos hSat2]
  exact ⟨rfl, rfl⟩

/-- Theorem (`ald_insufficient_purge_refused`):
If the inert gas purge duration `purgeMs` is shorter than `spec.minPurgeMs` (which would allow gas-phase
precursors to overlap and cause non-conformal parasitic CVD deposition), `checkAldSelfLimiting`
returns `false`. -/
theorem ald_insufficient_purge_refused
    (spec : AldProcessSpec) (doseMs purgeMs chamberTempC : Nat)
    (hShortPurge : purgeMs < spec.minPurgeMs) :
    checkAldSelfLimiting spec doseMs purgeMs chamberTempC = false := by
  unfold checkAldSelfLimiting
  have hNotGe : ¬(spec.minPurgeMs ≤ purgeMs) := by omega
  simp [hNotGe]

/-- Inline computational metrology specification for an open nanofab / neofab wafer lot:
* `fourPointProbeVmUv`: 4-point collinear probe measured voltage $V$ in microvolts ($\mu\text{V}$),
* `fourPointProbeImUa`: 4-point collinear probe injected current $I$ in microamperes ($\mu\text{A}$),
* `targetSheetRhoMohmPerSq`: target sheet resistance $R_s$ in milliohms per square ($\text{m}\Omega/\square$),
* `maxSheetRhoTolMohm`: maximum acceptable sheet resistance deviation ($\text{m}\Omega/\square$),
* `reflectometryMeasuredPm`: optical reflectometry / ellipsometry measured dielectric thickness ($\text{pm}$),
* `aldTargetCycles`: number of executed ALD cycles. -/
structure NeofabMetrologyReading where
  fourPointProbeVmUv      : Nat
  fourPointProbeImUa      : Nat
  targetSheetRhoMohmPerSq : Nat
  maxSheetRhoTolMohm      : Nat
  reflectometryMeasuredPm : Nat
  maxThicknessTolPm       : Nat
  aldTargetCycles         : Nat
  deriving DecidableEq, Repr

/-- Collinear 4-point-probe sheet resistance (in milliohms per square $\text{m}\Omega/\square$)
for semi-infinite thin films ($t \ll s$):
$$R_s = \frac{\pi}{\ln 2} \cdot \frac{V}{I} \approx 4.532 \cdot \frac{V_{\mu\text{V}}}{I_{\mu\text{A}}}.$$ -/
def evalFourPointSheetRhoMohm (vUv iUa : Nat) : Nat :=
  (4532 * vUv) / iUa

/-- Absolute difference $|a - b|$ on natural numbers. -/
def natAbsDiff (a b : Nat) : Nat :=
  if b ≤ a then a - b else b - a

/-- Complete inline metrology signoff check for an open nanofab (`HackerFab` / `AtomicSemi` /
`FabuBlox` / `FABμBOX`) process module:
1. Lithography stepper NA and wavelength resolve the target minimum CD (`rayleighCdNm ≤ targetCdNm`),
2. ALD recipe satisfies self-limiting saturation and purge rules (`checkAldSelfLimiting`),
3. Optical reflectometry film thickness matches the digital ALD growth law `cycles * gpcPm` within `maxThicknessTolPm`,
4. 4-point-probe sheet resistance $R_s = 4.532 \frac{V}{I}$ matches `targetSheetRhoMohmPerSq` within `maxSheetRhoTolMohm`. -/
def checkNeofabMetrology
    (litho : LithoStepperSpec) (targetCdNm : Nat)
    (ald : AldProcessSpec) (doseMs purgeMs tempC : Nat)
    (metro : NeofabMetrologyReading) : Bool :=
  let cdNm := rayleighCdNm litho
  let expectedFilmPm := evalAldFilmThicknessPm ald metro.aldTargetCycles doseMs
  let measuredRsMohm := evalFourPointSheetRhoMohm metro.fourPointProbeVmUv metro.fourPointProbeImUa
  decide (litho.naPermille > 0) &&
  decide (cdNm ≤ targetCdNm) &&
  checkAldSelfLimiting ald doseMs purgeMs tempC &&
  decide (metro.fourPointProbeImUa > 0) &&
  decide (natAbsDiff metro.reflectometryMeasuredPm expectedFilmPm ≤ metro.maxThicknessTolPm) &&
  decide (natAbsDiff measuredRsMohm metro.targetSheetRhoMohmPerSq ≤ metro.maxSheetRhoTolMohm)

/-- Theorem (`neofabMetrology_sound`):
Whenever `checkNeofabMetrology` passes (`= true`), the lithography stepper resolves `targetCdNm`,
the ALD recipe is strictly inside the self-limiting window (`checkAldSelfLimiting = true`), and both
the reflectometry film thickness and 4-point-probe sheet resistance lie within their metrological
tolerance bands. -/
theorem neofabMetrology_sound
    (litho : LithoStepperSpec) (targetCdNm : Nat)
    (ald : AldProcessSpec) (doseMs purgeMs tempC : Nat)
    (metro : NeofabMetrologyReading)
    (hOk : checkNeofabMetrology litho targetCdNm ald doseMs purgeMs tempC metro = true) :
    rayleighCdNm litho ≤ targetCdNm ∧
    checkAldSelfLimiting ald doseMs purgeMs tempC = true ∧
    natAbsDiff metro.reflectometryMeasuredPm (evalAldFilmThicknessPm ald metro.aldTargetCycles doseMs) ≤
      metro.maxThicknessTolPm ∧
    natAbsDiff (evalFourPointSheetRhoMohm metro.fourPointProbeVmUv metro.fourPointProbeImUa)
      metro.targetSheetRhoMohmPerSq ≤ metro.maxSheetRhoTolMohm := by
  unfold checkNeofabMetrology at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  exact ⟨hOk.1.1.1.1.2, hOk.1.1.1.2, hOk.1.2, hOk.2⟩

/-- Golden open-nanofab baseline specification (`HackerFab` / `FABμBOX` i-line maskless stepper +
thermal $\text{Al}_2\text{O}_3$ ALD gate dielectric + TiN/Al metal metrology). -/
def goldenHackerFabLitho : LithoStepperSpec where
  toolName     := "FABuBOX_Maskless_iLine_365nm"
  wavelengthNm := 365
  naPermille   := 450
  k1Permille   := 500
  k2Permille   := 500

def goldenAl2O3AldSpec : AldProcessSpec where
  filmName      := "Thermal_Al2O3_TMA_H2O"
  gpcPm         := 110
  satDoseMs     := 150
  minPurgeMs    := 2000
  aldWindowMinC := 150
  aldWindowMaxC := 300

def goldenNeofabMetrology : NeofabMetrologyReading where
  fourPointProbeVmUv      := 1000
  fourPointProbeImUa      := 100
  targetSheetRhoMohmPerSq := 45320
  maxSheetRhoTolMohm      := 500
  reflectometryMeasuredPm := 22000
  maxThicknessTolPm       := 250
  aldTargetCycles         := 200

/-- Theorem (`goldenNeofabBaseline_passes`):
The golden open-nanofab baseline (`365 nm` i-line maskless lithography with $\text{CD} = 405\,\text{nm} \le 500\,\text{nm}$,
200-cycle $\text{Al}_2\text{O}_3$ ALD yielding $22.0\,\text{nm}$ high-$k$ dielectric, and 4-point-probe
sheet resistance $45.32\,\Omega/\square$) passes `checkNeofabMetrology`. -/
theorem goldenNeofabBaseline_passes :
    checkNeofabMetrology goldenHackerFabLitho 500 goldenAl2O3AldSpec 200 2500 250 goldenNeofabMetrology = true := by
  rfl

end Obend.Hardware.Physics
end
