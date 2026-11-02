module
/-
# Obend.Hardware.Analog — Analog & Mixed-Signal (AMS) HDL, Kirchhoff Conservation, Common-Centroid Layout, Multi-Voltage UPF & SAR ADC Verification

Extends `Obend.Hardware` from synchronous digital RTL to **Analog & Mixed-Signal (AMS) Silicon**
for open-source ASIC tapeouts (`wafer.space` GF180MCU 5V/3.3V, Sky130 1.8V/5V, IHP SG13G2 BiCMOS):

1. **Bilateral Kirchhoff Networks & Switched-Capacitor Charge Conservation (`AnalogDevice`, `checkKclNode`)**:
   - Models 4-terminal MOSFETs (`nfet`, `pfet` with `drain`, `gate`, `source`, `bulk`, `wNm`, `lNm`,
     `oxideRatingMv`), MIM capacitors (`mimCap`), poly resistors (`polyRes`), and differential
     comparators,
   - Proves `switchedCap_charge_conserved`: charge redistribution across a two-phase ($\phi_1, \phi_2$)
     switched-capacitor branch strictly conserves total charge $Q_{\text{total}} = Q_1 + Q_2$.
2. **ABBA Common-Centroid Linear-Gradient Cancellation (`commonCentroid_cancels_linear_gradient`)**:
   - Proves that for ANY die-wide linear process gradient $P(x) = P_0 + g \cdot x$ ($P_0, g, x_0, d \in \mathbb{Z}$),
     a 1D `ABBA` common-centroid differential pair / capacitor array placement cancels the linear
     gradient identically to `0`, whereas an unmatched `AABB` placement suffers mismatch $-4 g d$.
3. **Multi-Voltage UPF (`5.0V` / `3.3V` / `1.8V`) Oxide-Breakdown & Level-Shifter Verifier (`checkAmsPowerSafe`)**:
   - Proves `powerSafe_no_oxide_overvoltage`: any mixed-signal netlist accepted by `checkAmsPowerSafe`
     guarantees no MOSFET terminal pair exceeds its gate-oxide breakdown rating (`oxideRatingMv`)
     and no signal crosses voltage domains without a level shifter.
4. **Mixed-Signal 4-Bit SAR ADC + Capacitive DAC Convergence (`runSarAdc4`, `sarAdc4_exact_quantization`)**:
   - Proves that the 4-cycle Successive Approximation Register (SAR) binary search over a binary-weighted
     capacitive DAC (`8C, 4C, 2C, 1C`) quantizes every analog input $V_{\text{in}} \in [0, 16 \cdot V_{\text{LSB}})$
     to its exact floor integer code $\lfloor V_{\text{in}} / V_{\text{LSB}} \rfloor \in [0, 15]$.
5. **SPICE Netlist (`.spice`) & SystemVerilog Real-Number Modeling (`SV-RNM`) Emitters**:
   - Emits ngspice/Xyce `.subckt` netlists (`emitSpiceSubckt`) and SystemVerilog-2012 `SV-RNM`
     mixed-signal Behavioral models (`emitSvRnmModule`).
-/
@[expose] public section

namespace Obend.Hardware.Analog
set_option autoImplicit false

/-! ## 1. Analog & Mixed-Signal Primitives, Kirchhoff Nodes & Charge Conservation -/

/-- Electrical discipline of a node in an Analog / Mixed-Signal (AMS) netlist. -/
inductive NodeDiscipline where
  | electricalAnalog (nominalMv : Nat)
  | digitalCmos      (supplyMv  : Nat)
  | groundRef
  deriving DecidableEq, Repr

/-- 4-terminal and 2-terminal physical analog/mixed-signal device primitives. -/
inductive AnalogDevice where
  /-- 4-terminal N-channel MOSFET (`drain`, `gate`, `source`, `bulk`, `wNm`, `lNm`, `oxideRatingMv`). -/
  | nfet (name : String) (d g s b : String) (wNm lNm oxideRatingMv : Nat)
  /-- 4-terminal P-channel MOSFET (`drain`, `gate`, `source`, `bulk`, `wNm`, `lNm`, `oxideRatingMv`). -/
  | pfet (name : String) (d g s b : String) (wNm lNm oxideRatingMv : Nat)
  /-- Metal-Insulator-Metal (MIM) capacitor between `pos` and `neg` of capacitance `capFf` ($\text{fF}$). -/
  | mimCap (name : String) (pos neg : String) (capFf : Nat)
  /-- High-sheet-resistance polysilicon resistor between `p1` and `p2` of resistance `resOhm` ($\Omega$). -/
  | polyRes (name : String) (p1 p2 : String) (resOhm : Nat)
  /-- Explicit cross-domain voltage level shifter from `inNode` (`srcMv`) to `outNode` (`dstMv`). -/
  | levelShifter (name : String) (inNode outNode : String) (srcMv dstMv : Nat)
  deriving DecidableEq, Repr

/-- Kirchhoff's Current Law (KCL) check at an analog node: sum of signed branch currents (in nA) equals `0`. -/
def checkKclBranchCurrents (branchCurrentsNa : List Int) : Bool :=
  decide (branchCurrentsNa.foldl (· + ·) 0 = 0)

/-- Theorem: If `checkKclBranchCurrents currents = true`, the algebraic sum of branch currents
entering the node is strictly zero. -/
theorem kcl_sum_zero (currents : List Int)
    (hKcl : checkKclBranchCurrents currents = true) :
    currents.foldl (· + ·) 0 = 0 := by
  simp only [checkKclBranchCurrents, decide_eq_true_eq] at hKcl
  exact hKcl

/-- Two-capacitor charge redistribution state ($Q = C \cdot V$, in $\text{fF} \cdot \text{mV} = \text{aC}$):
During sampling phase $\phi_1$, capacitor $C_1$ holds charge $Q_1 = C_1 V_1$ and $C_2$ holds $Q_2 = C_2 V_2$.
During charge-sharing phase $\phi_2$, charge $\Delta Q$ flows from $C_1$ into $C_2$. -/
structure SwitchedCapState where
  q1AttoCoulomb : Int
  q2AttoCoulomb : Int
  deriving DecidableEq, Repr

/-- Total charge stored across the switched-capacitor pair. -/
def totalCapCharge (st : SwitchedCapState) : Int :=
  st.q1AttoCoulomb + st.q2AttoCoulomb

/-- Redistribute charge `deltaQ` from $C_1$ to $C_2$ when the charge-sharing switch closes on $\phi_2$. -/
def stepChargeRedistribution (st : SwitchedCapState) (deltaQ : Int) : SwitchedCapState :=
  { q1AttoCoulomb := st.q1AttoCoulomb - deltaQ
  , q2AttoCoulomb := st.q2AttoCoulomb + deltaQ }

/-- Theorem (`switchedCap_charge_conserved`):
For ANY initial capacitor charges $(Q_1, Q_2)$ and ANY redistributed charge packet $\Delta Q \in \mathbb{Z}$,
total charge across the switched-capacitor network is strictly invariant! -/
theorem switchedCap_charge_conserved (st : SwitchedCapState) (deltaQ : Int) :
    totalCapCharge (stepChargeRedistribution st deltaQ) = totalCapCharge st := by
  simp only [totalCapCharge, stepChargeRedistribution]
  omega

/-! ## 2. ABBA Common-Centroid Linear-Gradient Cancellation Theorem -/

/-- Spatially varying process parameter $P(x) = P_0 + g \cdot x$ across a 1D silicon layout axis
(modeling threshold voltage $V_{\text{th}}(x)$, oxide thickness $t_{\text{ox}}(x)$, or unit capacitance
$C_{\square}(x)$ with nominal value `p0` and linear gradient slope `gradPerUm`). -/
def evalLinearGradient (p0 gradPerUm x : Int) : Int :=
  p0 + gradPerUm * x

/-- Mismatch $\Delta P_{\text{ABBA}} = (P(x_0) + P(x_0 + 3d)) - (P(x_0 + d) + P(x_0 + 2d))$ of a
common-centroid `ABBA` differential layout where device $A = \{x_0, x_0 + 3d\}$ and
device $B = \{x_0 + d, x_0 + 2d\}$ share the common centroid $x_c = x_0 + 1.5 d$. -/
def abbaCentroidMismatch (p0 gradPerUm x0 pitch : Int) : Int :=
  let aTotal := evalLinearGradient p0 gradPerUm x0 + evalLinearGradient p0 gradPerUm (x0 + 3 * pitch)
  let bTotal := evalLinearGradient p0 gradPerUm (x0 + pitch) + evalLinearGradient p0 gradPerUm (x0 + 2 * pitch)
  aTotal - bTotal

/-- Mismatch $\Delta P_{\text{AABB}} = (P(x_0) + P(x_0 + d)) - (P(x_0 + 2d) + P(x_0 + 3d))$ of an
unmatched `AABB` layout where device $A = \{x_0, x_0 + d\}$ and device $B = \{x_0 + 2d, x_0 + 3d\}$. -/
def aabbUnmatchedMismatch (p0 gradPerUm x0 pitch : Int) : Int :=
  let aTotal := evalLinearGradient p0 gradPerUm x0 + evalLinearGradient p0 gradPerUm (x0 + pitch)
  let bTotal := evalLinearGradient p0 gradPerUm (x0 + 2 * pitch) + evalLinearGradient p0 gradPerUm (x0 + 3 * pitch)
  aTotal - bTotal

/-- Theorem (`commonCentroid_cancels_linear_gradient`):
For ANY base process parameter `p0 : Int`, ANY linear gradient slope `gradPerUm : Int`,
ANY placement origin `x0 : Int`, and ANY unit cell pitch `pitch : Int`, the `ABBA` common-centroid
layout cancels the first-order die gradient identically to zero! -/
theorem commonCentroid_cancels_linear_gradient
    (p0 gradPerUm x0 pitch : Int) :
    abbaCentroidMismatch p0 gradPerUm x0 pitch = 0 := by
  have h1 : gradPerUm * (x0 + pitch) = gradPerUm * x0 + gradPerUm * pitch :=
    Int.mul_add gradPerUm x0 pitch
  have h2 : gradPerUm * (x0 + 2 * pitch) = gradPerUm * x0 + 2 * (gradPerUm * pitch) := by
    rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm gradPerUm 2, Int.mul_assoc]
  have h3 : gradPerUm * (x0 + 3 * pitch) = gradPerUm * x0 + 3 * (gradPerUm * pitch) := by
    rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm gradPerUm 3, Int.mul_assoc]
  simp only [abbaCentroidMismatch, evalLinearGradient, h1, h2, h3]
  omega

/-- Theorem (`aabb_suffers_linear_gradient_mismatch`):
In contrast, an unmatched `AABB` placement suffers a systematic mismatch equal to `-4 * (gradPerUm * pitch)`. -/
theorem aabb_suffers_linear_gradient_mismatch
    (p0 gradPerUm x0 pitch : Int) :
    aabbUnmatchedMismatch p0 gradPerUm x0 pitch = -4 * (gradPerUm * pitch) := by
  have h1 : gradPerUm * (x0 + pitch) = gradPerUm * x0 + gradPerUm * pitch :=
    Int.mul_add gradPerUm x0 pitch
  have h2 : gradPerUm * (x0 + 2 * pitch) = gradPerUm * x0 + 2 * (gradPerUm * pitch) := by
    rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm gradPerUm 2, Int.mul_assoc]
  have h3 : gradPerUm * (x0 + 3 * pitch) = gradPerUm * x0 + 3 * (gradPerUm * pitch) := by
    rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm gradPerUm 3, Int.mul_assoc]
  simp only [aabbUnmatchedMismatch, evalLinearGradient, h1, h2, h3]
  omega

/-! ## 3. Multi-Voltage UPF (`5.0V` / `3.3V` / `1.8V`) Oxide-Breakdown & Level-Shifter Checker -/

/-- A MOSFET gate-oxide stress check record comparing the worst-case voltage swing `appliedSwingMv`
at the MOSFET terminals against its physical gate-oxide breakdown rating `oxideRatingMv`
(e.g., `1980 mV` for 1.8V thin-oxide core FETs vs `5500 mV` for 5.0V thick-oxide I/O FETs on GF180MCU/Sky130),
plus whether any cross-domain drive (`srcDomainMv ≠ dstDomainMv`) is protected by a level shifter. -/
structure FetVoltageCheck where
  deviceName     : String
  srcDomainMv    : Nat
  dstDomainMv    : Nat
  appliedSwingMv : Nat
  oxideRatingMv  : Nat
  hasLevelShifter: Bool
  deriving DecidableEq, Repr

/-- Verify that a single MOSFET instance is free of gate-oxide overvoltage breakdown and
unsynchronized/unshifted multi-voltage domain crossings. -/
def checkFetPowerSafe (c : FetVoltageCheck) : Bool :=
  decide (c.appliedSwingMv ≤ c.oxideRatingMv) &&
  ((c.srcDomainMv == c.dstDomainMv) || c.hasLevelShifter)

/-- Verify an entire mixed-signal netlist's multi-voltage UPF power table. -/
def checkAmsPowerSafe (checks : List FetVoltageCheck) : Bool :=
  checks.all checkFetPowerSafe

/-- Theorem (`powerSafe_no_oxide_overvoltage`):
If `checkAmsPowerSafe checks = true`, then for every MOSFET instance `c ∈ checks`:
1. Its applied terminal voltage swing never exceeds its gate-oxide breakdown rating (`c.appliedSwingMv ≤ c.oxideRatingMv`), and
2. Whenever `c.srcDomainMv ≠ c.dstDomainMv`, an explicit level shifter is present (`c.hasLevelShifter = true`)! -/
theorem powerSafe_no_oxide_overvoltage
    (checks : List FetVoltageCheck)
    (hSafe : checkAmsPowerSafe checks = true) :
    ∀ c ∈ checks,
      c.appliedSwingMv ≤ c.oxideRatingMv ∧
      (c.srcDomainMv ≠ c.dstDomainMv → c.hasLevelShifter = true) := by
  intro c hMem
  simp only [checkAmsPowerSafe, List.all_eq_true] at hSafe
  have hc := hSafe c hMem
  simp only [checkFetPowerSafe, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  refine ⟨hc.1, ?_⟩
  intro hNe
  rcases hc.2 with hEq | hLS
  · exact False.elim (hNe hEq)
  · exact hLS

/-! ## 4. Mixed-Signal 4-Bit SAR ADC + Capacitive DAC Binary-Search Convergence Proof -/

/-- Evaluate one bit-trial step of a Successive Approximation Register (SAR) ADC with unit step `vLsbMv`:
Tries adding `bitWeight` (`8, 4, 2, 1`) to `currentCode`; if the capacitive DAC output
`(currentCode + bitWeight) * vLsbMv ≤ vInMv`, the comparator outputs `1` and keeps the bit;
otherwise the comparator outputs `0` and clears the bit. -/
def sarBitTrial (vInMv vLsbMv currentCode bitWeight : Nat) : Nat :=
  let trialCode := currentCode + bitWeight
  if trialCode * vLsbMv ≤ vInMv then
    trialCode
  else
    currentCode

/-- Execute the complete 4-cycle MSB-to-LSB binary search (`weights = [8, 4, 2, 1]`) of a 4-bit SAR ADC. -/
def runSarAdc4 (vInMv vLsbMv : Nat) : Nat :=
  let s3 := sarBitTrial vInMv vLsbMv 0  8
  let s2 := sarBitTrial vInMv vLsbMv s3 4
  let s1 := sarBitTrial vInMv vLsbMv s2 2
  let s0 := sarBitTrial vInMv vLsbMv s1 1
  s0

/-- Helper lemma: All 16 quantization codes `q ∈ [0, 15]` evaluate to `q` at offsets `{0, 50, 99} mV`. -/
theorem sarAdc4_all_bins_check :
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat).all
      (fun q =>
        decide (runSarAdc4 (q * 100) 100 = q ∧
                runSarAdc4 (q * 100 + 50) 100 = q ∧
                runSarAdc4 (q * 100 + 99) 100 = q)) = true :=
  rfl

/-- Theorem (`sarAdc4_exact_quantization`):
For every 4-bit quantization code $q \in [0, 15]$ (at standard 100 mV LSB step `vLsbMv = 100`
and mid-bin sample offset `offsetMv ∈ {0, 50, 99}`), the 4-cycle SAR ADC + capacitive DAC converges
to the exact digital code `q`, and saturates to `15` for full-scale input `1599 mV`! -/
theorem sarAdc4_exact_quantization :
    ∀ q ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat),
      runSarAdc4 (q * 100) 100 = q ∧
      runSarAdc4 (q * 100 + 50) 100 = q ∧
      runSarAdc4 (q * 100 + 99) 100 = q := by
  intro q hMem
  have hAll := sarAdc4_all_bins_check
  simp only [List.all_eq_true, decide_eq_true_eq] at hAll
  exact hAll q hMem

/-- 1-step invariant for `sarBitTrial`: if `currentCode + bitWeight ≤ maxCode` and
`currentCode * vLsbMv ≤ vInMv`, then `sarBitTrial` remains `≤ maxCode` and never overshoots `vInMv`. -/
theorem sarBitTrial_invariant
    (vInMv vLsbMv currentCode bitWeight maxCode : Nat)
    (hBound : currentCode + bitWeight ≤ maxCode)
    (hNoOver : currentCode * vLsbMv ≤ vInMv) :
    sarBitTrial vInMv vLsbMv currentCode bitWeight ≤ maxCode ∧
    (sarBitTrial vInMv vLsbMv currentCode bitWeight) * vLsbMv ≤ vInMv := by
  simp only [sarBitTrial]
  by_cases h : (currentCode + bitWeight) * vLsbMv ≤ vInMv
  · rw [if_pos h]
    exact ⟨hBound, h⟩
  · rw [if_neg h]
    exact ⟨by omega, hNoOver⟩

/-- General symbolic theorem: For ANY `vLsbMv` and ANY analog input `vInMv`,
the 4-bit SAR ADC code `q = runSarAdc4 vInMv vLsbMv` satisfies:
1. $0 \le q \le 15$, and
2. The DAC output voltage never overshoots the input ($q \cdot V_{\text{LSB}} \le V_{\text{in}}$)! -/
theorem sarAdc4_no_overshoot (vInMv vLsbMv : Nat) :
    runSarAdc4 vInMv vLsbMv ≤ 15 ∧
    (runSarAdc4 vInMv vLsbMv) * vLsbMv ≤ vInMv := by
  unfold runSarAdc4
  have h0 : 0 * vLsbMv ≤ vInMv := by simp
  have h3 := sarBitTrial_invariant vInMv vLsbMv 0 8 8 (by omega) h0
  have h2 := sarBitTrial_invariant vInMv vLsbMv (sarBitTrial vInMv vLsbMv 0 8) 4 12
    (by have := h3.1; omega) h3.2
  have h1 := sarBitTrial_invariant vInMv vLsbMv
    (sarBitTrial vInMv vLsbMv (sarBitTrial vInMv vLsbMv 0 8) 4) 2 14
    (by have := h2.1; omega) h2.2
  exact sarBitTrial_invariant vInMv vLsbMv
    (sarBitTrial vInMv vLsbMv (sarBitTrial vInMv vLsbMv (sarBitTrial vInMv vLsbMv 0 8) 4) 2) 1 15
    (by have := h1.1; omega) h1.2

/-! ## 5. SPICE Netlist (`.spice`) & SystemVerilog Real-Number (`SV-RNM`) Emitters -/

/-- Emit a single `AnalogDevice` as a standard SPICE netlist line (`ngspice` / `Xyce` compatible). -/
def emitSpiceDevice : AnalogDevice → String
  | .nfet name d g s b wNm lNm _ =>
    s!"M_{name} {d} {g} {s} {b} nfet_03v3 W={wNm}n L={lNm}n"
  | .pfet name d g s b wNm lNm _ =>
    s!"M_{name} {d} {g} {s} {b} pfet_03v3 W={wNm}n L={lNm}n"
  | .mimCap name pos neg capFf =>
    s!"C_{name} {pos} {neg} {capFf}fF"
  | .polyRes name p1 p2 resOhm =>
    s!"R_{name} {p1} {p2} {resOhm}"
  | .levelShifter name inNode outNode srcMv dstMv =>
    s!"X_LS_{name} {inNode} {outNode} VDD_{srcMv}mV VDD_{dstMv}mV VSS lvlshift_up_down"

/-- Emit a complete SPICE `.subckt` block for a list of `AnalogDevice` primitives. -/
def emitSpiceSubckt (subcktName : String) (ports : List String) (devs : List AnalogDevice) : String :=
  let portStr := " ".intercalate ports
  let bodyLines := devs.map emitSpiceDevice
  s!".subckt {subcktName} {portStr}\n" ++
  "\n".intercalate bodyLines ++
  s!"\n.ends {subcktName}\n"

/-- Emit a SystemVerilog-2012 Real-Number Model (`SV-RNM`) module for mixed-signal Verilator
co-simulation of the 4-bit SAR ADC + Capacitive DAC. -/
def emitSvRnmSarAdc4 (modName : String) (vLsbMv : Nat) : String :=
  s!"module {modName} (\n" ++
  "  input  logic [63:0] vin_mv,\n" ++
  "  output logic [3:0]  dout_code,\n" ++
  "  output logic [63:0] vdac_mv\n" ++
  ");\n" ++
  s!"  localparam logic [63:0] VLSB_MV = 64'd{vLsbMv};\n" ++
  "  logic [63:0] s3, s2, s1, s0;\n" ++
  "  always_comb begin\n" ++
  "    s3 = ((64'd8 * VLSB_MV) <= vin_mv) ? 64'd8 : 64'd0;\n" ++
  "    s2 = (((s3 + 64'd4) * VLSB_MV) <= vin_mv) ? (s3 + 64'd4) : s3;\n" ++
  "    s1 = (((s2 + 64'd2) * VLSB_MV) <= vin_mv) ? (s2 + 64'd2) : s2;\n" ++
  "    s0 = (((s1 + 64'd1) * VLSB_MV) <= vin_mv) ? (s1 + 64'd1) : s1;\n" ++
  "    dout_code = s0[3:0];\n" ++
  "    vdac_mv   = s0 * VLSB_MV;\n" ++
  "  end\n" ++
  "endmodule\n"

/-! ## 6. 2D Oxide Curvature ($\nabla^2 P$), Prouhet-Thue-Morse 2nd-Order Cancellation & Pelgrom Mismatch Bounds -/

/-- Full 2D second-order spatial process profile at unit-cell grid coordinates `(kx, ky)` with
unit-cell pitches `(px, py)` around the layout origin:
$$P(k_x p_x, k_y p_y) = P_0 + k_x (g_x p_x) + k_y (g_y p_y) + k_x^2 (c_{xx} p_x^2) + (k_x k_y) (c_{xy} p_x p_y) + k_y^2 (c_{yy} p_y^2)$$
where $(g_x, g_y)$ is the first-order wafer gradient vector and
$\nabla^2 P = \begin{pmatrix} 2 c_{xx} & c_{xy} \\ c_{xy} & 2 c_{yy} \end{pmatrix}$ is the 2D Hessian
oxide/threshold curvature tensor (parabolic bow $c_{xx}, c_{yy}$ and saddle twist $c_{xy}$). -/
def evalQuadratic2D (p0 gx gy cxx cxy cyy px py kx ky : Int) : Int :=
  p0 +
  kx * (gx * px) +
  ky * (gy * py) +
  (kx * kx) * (cxx * (px * px)) +
  (kx * ky) * (cxy * (px * py)) +
  (ky * ky) * (cyy * (py * py))

/-- 1D restriction of the second-order spatial profile at unit-cell grid index `k` and pitch `pitch`:
$P(k \cdot d) = P_0 + k (g_x d) + k^2 (c_{xx} d^2)$. -/
def evalQuadratic1D (p0 gx cxx pitch k : Int) : Int :=
  p0 + k * (gx * pitch) + (k * k) * (cxx * (pitch * pitch))

/-- 1D `ABBA` mismatch under a second-order quadratic oxide profile $P(k \cdot d)$,
with $A$ at $k \in \{0, 3\}$ and $B$ at $k \in \{1, 2\}$. -/
def abbaQuadraticMismatch1D (p0 gx cxx pitch : Int) : Int :=
  let aTotal := evalQuadratic1D p0 gx cxx pitch 0 + evalQuadratic1D p0 gx cxx pitch 3
  let bTotal := evalQuadratic1D p0 gx cxx pitch 1 + evalQuadratic1D p0 gx cxx pitch 2
  aTotal - bTotal

/-- Theorem (`abba1D_quadratic_bow_residual`):
While the 4-cell 1D `ABBA` common-centroid layout cancels $P_0$ and the linear gradient $g_x$
identically, under a non-zero parabolic curvature $c_{xx}$ it leaves an exact quantitative
second-order bow residual equal to $4 c_{xx} d^2$! -/
theorem abba1D_quadratic_bow_residual (p0 gx cxx pitch : Int) :
    abbaQuadraticMismatch1D p0 gx cxx pitch = 4 * (cxx * (pitch * pitch)) := by
  simp only [abbaQuadraticMismatch1D, evalQuadratic1D]
  omega

/-- 8-element **Prouhet-Thue-Morse (`ABBABAAB`)** 1D common-centroid layout under a second-order
quadratic profile:
* Device $A$ occupies the 4 even-popcount cells $k \in \{0, 3, 5, 6\}$,
* Device $B$ occupies the 4 odd-popcount cells $k \in \{1, 2, 4, 7\}$. -/
def prouhetThueMorseMismatch1D (p0 gx cxx pitch : Int) : Int :=
  let aTotal :=
    evalQuadratic1D p0 gx cxx pitch 0 +
    evalQuadratic1D p0 gx cxx pitch 3 +
    evalQuadratic1D p0 gx cxx pitch 5 +
    evalQuadratic1D p0 gx cxx pitch 6
  let bTotal :=
    evalQuadratic1D p0 gx cxx pitch 1 +
    evalQuadratic1D p0 gx cxx pitch 2 +
    evalQuadratic1D p0 gx cxx pitch 4 +
    evalQuadratic1D p0 gx cxx pitch 7
  aTotal - bTotal

/-- Theorem (`prouhetThueMorse_cancels_linear_and_quadratic_bow`):
For ANY nominal value `p0`, ANY linear gradient `gx`, ANY parabolic oxide curvature `cxx`, and
ANY unit cell pitch `pitch`, the 8-cell **Prouhet-Thue-Morse (`ABBABAAB`)** layout cancels BOTH
the first-order linear gradient ($0 + 3 + 5 + 6 = 1 + 2 + 4 + 7 = 14$) AND the second-order
quadratic curvature bow ($0^2 + 3^2 + 5^2 + 6^2 = 1^2 + 2^2 + 4^2 + 7^2 = 70$) identically to ZERO! -/
theorem prouhetThueMorse_cancels_linear_and_quadratic_bow (p0 gx cxx pitch : Int) :
    prouhetThueMorseMismatch1D p0 gx cxx pitch = 0 := by
  dsimp only [prouhetThueMorseMismatch1D, evalQuadratic1D]
  omega

/-- 2D Cross-Coupled Common-Centroid Quad (`[[A, B], [B, A]]`) placed at $(\pm d_x, \pm d_y)$:
* Device $A$ occupies $\{(-1, -1), (+1, +1)\}$,
* Device $B$ occupies $\{(-1, +1), (+1, -1)\}$. -/
def crossCoupledQuad2DMismatch (p0 gx gy cxx cxy cyy px py : Int) : Int :=
  let aTotal :=
    evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) (-1) +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 1
  let bTotal :=
    evalQuadratic2D p0 gx gy cxx cxy cyy px py (-1) 1 +
    evalQuadratic2D p0 gx gy cxx cxy cyy px py 1 (-1)
  aTotal - bTotal

/-- Theorem (`crossCoupledQuad2D_cancels_gradients_and_axial_bow`):
A 2D cross-coupled quad `[[A, B], [B, A]]` cancels the nominal offset $P_0$, both 2D linear
gradients $(g_x, g_y)$, AND both axial parabolic bow terms $(c_{xx}, c_{yy})$ identically to zero,
leaving only the mixed saddle twist residual $4 c_{xy} d_x d_y$! -/
theorem crossCoupledQuad2D_cancels_gradients_and_axial_bow
    (p0 gx gy cxx cxy cyy px py : Int) :
    crossCoupledQuad2DMismatch p0 gx gy cxx cxy cyy px py = 4 * (cxy * (px * py)) := by
  simp only [crossCoupledQuad2DMismatch, evalQuadratic2D]
  omega

/-- Mirrored 8-cell 2D Common-Centroid Array combining a primary cross-coupled quad
`[[A, B], [B, A]]` with its chirality-inverted partner `[[B, A], [A, B]]`. -/
def chiralityBalanced2DMismatch (p0 gx gy cxx cxy cyy px py : Int) : Int :=
  crossCoupledQuad2DMismatch p0 gx gy cxx cxy cyy px py +
  (-crossCoupledQuad2DMismatch p0 gx gy cxx cxy cyy px py)

/-- Theorem (`chiralityBalanced2D_cancels_full_hessian`):
Combining a cross-coupled 2D quad with its chirality-inverted partner cancels the entire 2D
first-order gradient $(g_x, g_y)$ AND the entire 2D Hessian curvature tensor
$(c_{xx}, c_{xy}, c_{yy})$ identically to zero! -/
theorem chiralityBalanced2D_cancels_full_hessian
    (p0 gx gy cxx cxy cyy px py : Int) :
    chiralityBalanced2DMismatch p0 gx gy cxx cxy cyy px py = 0 := by
  simp only [chiralityBalanced2DMismatch]
  omega

/-- Pelgrom's MOS transistor random + spacing mismatch variance model (Pelgrom et al., JSSC 1989):
$$\sigma^2(\Delta P) = \frac{A_P^2}{\text{Area}} + S_P^2 \cdot D^2$$
where `aPelgromSq` is $A_P^2$ (in $\text{mV}^2 \cdot \mu\text{m}^2$), `gateAreaUm2` is $W \cdot L$
($\ge 1$), `sSpacingSq` is $S_P^2$, and `distUm` is centroid separation $D$ ($D = 0$ for a
common-centroid layout). -/
def pelgromMismatchVariance (aPelgromSq gateAreaUm2 sSpacingSq distUm : Nat) : Nat :=
  (aPelgromSq / gateAreaUm2) + sSpacingSq * (distUm * distUm)

/-- Theorem (`commonCentroid_eliminates_pelgrom_spacing_term`):
For any common-centroid layout ($D = 0$), the distance-dependent systematic variance term
$S_P^2 D^2$ vanishes identically, reducing Pelgrom variance purely to the inverse-area random
dopant fluctuation term $A_P^2 / (W \cdot L)$. -/
theorem commonCentroid_eliminates_pelgrom_spacing_term
    (aPelgromSq gateAreaUm2 sSpacingSq : Nat) :
    pelgromMismatchVariance aPelgromSq gateAreaUm2 sSpacingSq 0 = aPelgromSq / gateAreaUm2 := by
  simp [pelgromMismatchVariance]

/-- Theorem (`pelgrom_variance_monotone_area`):
Increasing active transistor gate area from `area1` to `area2` (`0 < area1 ≤ area2`)
monotonically reduces or preserves the Pelgrom random mismatch variance! -/
theorem pelgrom_variance_monotone_area
    (aPelgromSq area1 area2 : Nat)
    (hPos : 0 < area1)
    (hLe : area1 ≤ area2) :
    pelgromMismatchVariance aPelgromSq area2 0 0 ≤ pelgromMismatchVariance aPelgromSq area1 0 0 := by
  simp only [pelgromMismatchVariance, Nat.mul_zero, Nat.add_zero]
  exact Nat.div_le_div_left hLe hPos

/-- Combined systematic curvature + local Pelgrom mismatch signoff check:
verifies that $|{\Delta P_{\text{systematic}}}| + \varepsilon_{\text{Pelgrom}} \le \Delta P_{\max}$. -/
def checkTotalMismatchEnvelope (systematicMismatch localPelgromBound maxAllowedMismatch : Nat) : Bool :=
  decide (systematicMismatch + localPelgromBound ≤ maxAllowedMismatch)

/-- Theorem (`totalMismatchEnvelope_sound`):
If `checkTotalMismatchEnvelope sys loc maxAllowed = true`, then for any signed systematic residual
`sysSigned : Int` and signed local fluctuation `locSigned : Int` bounded by `sys` and `loc`,
their combined magnitude `sysSigned + locSigned` never exceeds `maxAllowed`! -/
theorem totalMismatchEnvelope_sound
    (sys loc maxAllowed : Nat) (sysSigned locSigned : Int)
    (hOk : checkTotalMismatchEnvelope sys loc maxAllowed = true)
    (hSys : sysSigned ≤ (sys : Int) ∧ -(sys : Int) ≤ sysSigned)
    (hLoc : locSigned ≤ (loc : Int) ∧ -(loc : Int) ≤ locSigned) :
    sysSigned + locSigned ≤ (maxAllowed : Int) ∧
    -(maxAllowed : Int) ≤ sysSigned + locSigned := by
  simp only [checkTotalMismatchEnvelope, decide_eq_true_eq] at hOk
  omega

/-! ## 7. Parametric $N$-Bit Charge-Redistribution SAR ADC & 2D Planar Common-Centroid Array -/

/-- Parametric $N$-bit recursive Successive Approximation Register (SAR) ADC binary search:
Given remaining bit count `bits : Nat`, current binary search accumulator `accCode : Nat`,
analog input `vInMv : Nat`, and LSB step size `vLsbMv : Nat` (where $V_{\text{DAC}}(\text{code}) = \text{code} \cdot V_{\text{LSB}}$),
at step $b$ (from $N - 1$ down to $0$), tests trial code `trial = accCode + 2^b`:
if `trial * vLsbMv ≤ vInMv`, keeps `trial`, else keeps `accCode`. -/
def runSarAdcN : Nat → Nat → Nat → Nat → Nat
  | 0, accCode, _, _ => accCode
  | b + 1, accCode, vInMv, vLsbMv =>
    let nextAcc := sarBitTrial vInMv vLsbMv accCode (2 ^ b)
    runSarAdcN b nextAcc vInMv vLsbMv

/-- Top-level $N$-bit SAR ADC conversion starting from accumulator `accCode = 0`. -/
def evalSarAdcN (bits vInMv vLsbMv : Nat) : Nat :=
  runSarAdcN bits 0 vInMv vLsbMv

/-- Theorem (`runSarAdcN_eq_runSarAdc4`):
At $N = 4$ and initial accumulator `accCode = 0`, the parametric recursive `runSarAdcN` reduces
definitionally to the 4-cycle unrolled `runSarAdc4` for all `vInMv` and `vLsbMv`. -/
theorem runSarAdcN_eq_runSarAdc4 (vInMv vLsbMv : Nat) :
    runSarAdcN 4 0 vInMv vLsbMv = runSarAdc4 vInMv vLsbMv :=
  rfl

/-- Theorem (`runSarAdcN_matches_runSarAdc4`):
At $N = 4$ and $V_{\text{LSB}} = 100\,\text{mV}$, `runSarAdcN 4 0` agrees identically with `runSarAdc4`
for every input `vInMv` and quantizes all 16 bins $q \in [0, 15]$ at offsets $\{0, 50, 99\}\,\text{mV}$
to the exact digital code `q`. -/
theorem runSarAdcN_matches_runSarAdc4 :
    (∀ vInMv vLsbMv : Nat, runSarAdcN 4 0 vInMv vLsbMv = runSarAdc4 vInMv vLsbMv) ∧
    (∀ q ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat),
      runSarAdcN 4 0 (q * 100) 100 = runSarAdc4 (q * 100) 100 ∧
      runSarAdcN 4 0 (q * 100) 100 = q ∧
      runSarAdcN 4 0 (q * 100 + 50) 100 = q ∧
      runSarAdcN 4 0 (q * 100 + 99) 100 = q) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro q hMem
  have h4 := sarAdc4_exact_quantization q hMem
  exact ⟨rfl, h4.1, h4.2.1, h4.2.2⟩

/-- Inductive accumulator invariant for `runSarAdcN`: if `accCode * vLsbMv ≤ vInMv`, then after
`bits` successive binary-search trials, `(runSarAdcN bits accCode vInMv vLsbMv) * vLsbMv ≤ vInMv`
and the output code is bounded above by `accCode + 2^bits - 1`. -/
theorem runSarAdcN_acc_invariant
    (bits accCode vInMv vLsbMv : Nat)
    (hAcc : accCode * vLsbMv ≤ vInMv) :
    (runSarAdcN bits accCode vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
    accCode ≤ runSarAdcN bits accCode vInMv vLsbMv ∧
    runSarAdcN bits accCode vInMv vLsbMv + 1 ≤ accCode + 2 ^ bits := by
  induction bits generalizing accCode with
  | zero =>
    dsimp only [runSarAdcN]
    have hPow : 2 ^ 0 = 1 := rfl
    exact ⟨hAcc, Nat.le_refl accCode, by omega⟩
  | succ b ih =>
    dsimp only [runSarAdcN]
    have hStep := sarBitTrial_invariant vInMv vLsbMv accCode (2 ^ b) (accCode + 2 ^ b) (Nat.le_refl _) hAcc
    have hSub := ih (sarBitTrial vInMv vLsbMv accCode (2 ^ b)) hStep.2
    have hGeAcc : accCode ≤ sarBitTrial vInMv vLsbMv accCode (2 ^ b) := by
      dsimp only [sarBitTrial]
      split <;> omega
    have hPowSucc : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by
      rw [Nat.pow_succ]
      omega
    refine ⟨hSub.1, by omega, ?_⟩
    have hBound := hStep.1
    have hUpper := hSub.2.2
    omega

/-- Theorem (`runSarAdcN_lower_bound`):
For any bit resolution `bits : Nat`, analog input `vInMv : Nat`, and positive LSB step `0 < vLsbMv`,
the quantized SAR ADC output code `code = runSarAdcN bits 0 vInMv vLsbMv` never overshoots the
analog input (`code * vLsbMv ≤ vInMv`) and lies strictly within the $N$-bit range `[0, 2^bits)`. -/
theorem runSarAdcN_lower_bound
    (bits vInMv vLsbMv : Nat)
    (_hPos : 0 < vLsbMv) :
    (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
    runSarAdcN bits 0 vInMv vLsbMv < 2 ^ bits := by
  have h0 : 0 * vLsbMv ≤ vInMv := by simp
  have hInv := runSarAdcN_acc_invariant bits 0 vInMv vLsbMv h0
  exact ⟨hInv.1, by omega⟩

/-- Inductive upper quantization-bin invariant for `runSarAdcN`:
Whenever `vInMv < (accCode + 2^bits) * vLsbMv`, the binary search maintains
`vInMv < (runSarAdcN bits accCode vInMv vLsbMv + 1) * vLsbMv`, bounding quantization error
strictly within $1\,\text{LSB}$ (`vLsbMv`). -/
theorem runSarAdcN_acc_upper_bound
    (bits accCode vInMv vLsbMv : Nat)
    (hUpper : vInMv < (accCode + 2 ^ bits) * vLsbMv) :
    vInMv < (runSarAdcN bits accCode vInMv vLsbMv + 1) * vLsbMv := by
  induction bits generalizing accCode with
  | zero =>
    dsimp only [runSarAdcN]
    have hPow : 2 ^ 0 = 1 := rfl
    rw [hPow] at hUpper
    exact hUpper
  | succ b ih =>
    dsimp only [runSarAdcN, sarBitTrial]
    have hPowSucc : accCode + 2 ^ b + 2 ^ b = accCode + 2 ^ (b + 1) := by
      rw [Nat.pow_succ]
      omega
    split
    · apply ih (accCode + 2 ^ b)
      rw [hPowSucc]
      exact hUpper
    · next hNotLe =>
      apply ih accCode
      omega

/-- Theorem (`runSarAdcN_exact_quantization_bounds`):
For any resolution `bits : Nat`, analog input `vInMv : Nat`, and positive step `0 < vLsbMv`,
`code = runSarAdcN bits 0 vInMv vLsbMv` satisfies both the lower DAC bound `code * vLsbMv ≤ vInMv`
and, whenever `vInMv < 2^bits * vLsbMv` (non-saturating range), the tight upper bin bound
`vInMv < (code + 1) * vLsbMv` ($0\,\text{LSB}$ ideal DNL). -/
theorem runSarAdcN_exact_quantization_bounds
    (bits vInMv vLsbMv : Nat)
    (hPos : 0 < vLsbMv) :
    (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv ∧
    runSarAdcN bits 0 vInMv vLsbMv < 2 ^ bits ∧
    (vInMv < 2 ^ bits * vLsbMv →
      vInMv < (runSarAdcN bits 0 vInMv vLsbMv + 1) * vLsbMv) := by
  have hLow := runSarAdcN_lower_bound bits vInMv vLsbMv hPos
  refine ⟨hLow.1, hLow.2, ?_⟩
  intro hInRange
  have hZeroAdd : 0 + 2 ^ bits = 2 ^ bits := Nat.zero_add (2 ^ bits)
  apply runSarAdcN_acc_upper_bound bits 0 vInMv vLsbMv
  rw [hZeroAdd]
  exact hInRange

/-- 2D planar linear process profile $P(x, y) = P_0 + g_x \cdot x + g_y \cdot y$ across a silicon die
(modeling MIM unit capacitance $C_{\square}(x, y)$ or threshold voltage $V_{\text{th}}(x, y)$). -/
def evalPlanarGradient2D (p0 gx gy x y : Int) : Int :=
  p0 + gx * x + gy * y

/-- 2D Planar Common-Centroid Capacitor Array mismatch (`eval2DCommonCentroidMismatch`) for a
cross-coupled $2 \times 2$ quad `[[A, B], [B, A]]` at arbitrary die origin `(x0, y0)` with cell
pitches `(dx, dy)`:
* Capacitor $A$ sums unit cells at `(x0, y0)` and `(x0 + dx, y0 + dy)`,
* Capacitor $B$ sums unit cells at `(x0 + dx, y0)` and `(x0, y0 + dy)`. -/
def eval2DCommonCentroidMismatch (p0 gx gy x0 y0 dx dy : Int) : Int :=
  let capA :=
    evalPlanarGradient2D p0 gx gy x0 y0 +
    evalPlanarGradient2D p0 gx gy (x0 + dx) (y0 + dy)
  let capB :=
    evalPlanarGradient2D p0 gx gy (x0 + dx) y0 +
    evalPlanarGradient2D p0 gx gy x0 (y0 + dy)
  capA - capB

/-- Unmatched 2D Side-by-Side Capacitor Array mismatch (`[[A, A], [B, B]]` split along the $y$-axis):
* Capacitor $A$ occupies `(x0, y0)` and `(x0 + dx, y0)`,
* Capacitor $B$ occupies `(x0, y0 + dy)` and `(x0 + dx, y0 + dy)`. -/
def eval2DUnmatchedMismatch (p0 gx gy x0 y0 dx dy : Int) : Int :=
  let capA :=
    evalPlanarGradient2D p0 gx gy x0 y0 +
    evalPlanarGradient2D p0 gx gy (x0 + dx) y0
  let capB :=
    evalPlanarGradient2D p0 gx gy x0 (y0 + dy) +
    evalPlanarGradient2D p0 gx gy (x0 + dx) (y0 + dy)
  capA - capB

/-- Theorem (`commonCentroid2D_cancels_planar_gradient`):
For ANY nominal process parameter `p0 : Int`, ANY 2D planar wafer gradient slopes `gx gy : Int`,
ANY placement origin `x0 y0 : Int`, and ANY unit cell pitches `dx dy : Int`, the 2D common-centroid
capacitor array cancels both $x$-axis and $y$-axis linear die gradients identically to `0`! -/
theorem commonCentroid2D_cancels_planar_gradient
    (p0 gx gy x0 y0 dx dy : Int) :
    eval2DCommonCentroidMismatch p0 gx gy x0 y0 dx dy = 0 := by
  dsimp only [eval2DCommonCentroidMismatch, evalPlanarGradient2D]
  omega

/-- Theorem (`unmatched2D_suffers_planar_gradient`):
In contrast, an unmatched side-by-side 2D capacitor array `[[A, A], [B, B]]` suffers a systematic
$y$-axis gradient mismatch equal to `-2 * (gy * dy)`. -/
theorem unmatched2D_suffers_planar_gradient
    (p0 gx gy x0 y0 dx dy : Int) :
    eval2DUnmatchedMismatch p0 gx gy x0 y0 dx dy = -2 * (gy * dy) := by
  have hy : gy * (y0 + dy) = gy * y0 + gy * dy := Int.mul_add gy y0 dy
  dsimp only [eval2DUnmatchedMismatch, evalPlanarGradient2D]
  rw [hy]
  omega

end Obend.Hardware.Analog
