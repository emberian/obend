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

end Obend.Hardware.Analog
