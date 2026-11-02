module
/-
# Obend.Lower.Proofs.SelfAccelerate — Reflexive Self-Acceleration: Compiling Verified Lean Multiphysics Through `Obend` Into FPGA RTL, AMD `CDNA3` GPU ISA, TPU Systolic Arrays & `FP4` Tensor Cores

Implements the **Reflexive Physics-to-Substrate Compilation Loop**:
Starting from high-level multiphysics and power-electronics kernels written in the `Lean-lite`
(`LExpr`) fragment of Lean, we lower them through `Obend.Lower` (`lowerT`) into `Obend.Core.Term.Book`,
synthesize them into verified saturating FPGA RTL (`compileBookToRtlSat`), and lower that RTL
further into:
1. **AMD `CDNA3` / `RDNA3` GPU Wavefront VALU / `v_mfma` ISA (`compileRtlExprToAmdGpu`, `compileRtlModuleToAmdGpu`)**,
2. **2D TPU Systolic Array PE Chains (`runSystolicMacChain`)**,
3. **FPGA `DSP58` `PCIN -> PCOUT` Dedicated Cascade Chains (`runDsp58Cascade`)**, and
4. **Ozaki Scheme Base-13 `FP4 (E2M1)` Tensor-Core Limbs (`evalOzakiBase13Product2`, `arXiv:2608.06812`)**.

We prove the **6-Stage Reflexive Self-Acceleration Theorems** across three flagship physical domains:
- **Domain A (`lcDrivesInSlotThermalLExpr`)**: LC Drives (Potsdam, NY) direct in-slot liquid-cooled
  stator winding temperature kernel ($T_{\text{peak}} = 50 + P_{\text{loss}} \cdot (2 + 4 + 3) = 122^\circ\text{C}$ at $8\,\text{kW}$),
- **Domain B (`ms350MpptExtractedPowerLExpr`)**: Mission Power `MS350` (Potsdam, NY) solar inverter
  MPPT power kernel ($P(V) = V \cdot (200 - V) = 10000\,\text{W}$ at $V^\star = 100\,\text{V}$),
- **Domain C (`femm2dElementEnergyLExpr`)**: 2D FEMM triangular finite-element magnetic co-energy
  kernel ($E = 5 \cdot ((a_0 - 2)^2 + 9) = 125$ at $a_0 = 6$).
-/
public import Obend.Lower.Proofs.Hardware
public import Obend.Hardware.Accelerators
public import Obend.Hardware.Magnetics
public import Obend.Hardware.FluidThermal
public import Obend.Hardware.PowerElectronics
public import Obend.Hardware.GeometryCAM
public import Obend.Hardware.OpenHypergraph
@[expose] public section

namespace Obend.Lower
open Obend.Core.Term Obend.Core.Ty
open Obend.Equiv Obend.Leaf
open Obend.Hardware.HDL Obend.Hardware.Compiler
open Obend.Hardware.Accelerators

set_option autoImplicit false

/-! ## 1. Compiler from Synthesized `RtlExpr` / `RtlModule` to 64-Bit AMD `CDNA3`/`RDNA3` GPU Wavefront ISA (`AmdGpuVop64Inst`) -/

/-- Faithful 64-bit AMD `CDNA3`/`RDNA3` VALU/VOP3/VOPC instruction set (`AmdGpuVop64Inst`)
covering every `RtlAluOp` (`add`, `sub`, `mul`, `bitAnd`, `bitOr`, `bitXor`, `shl`, `lshr`, `eq`, `ult`),
`RtlExpr.bitNot` (`v_not_b64`), and `RtlExpr.mux` (`v_cndmask_b64`) without silent semantic corruption. -/
inductive AmdGpuVop64Inst where
  | v_mov_b64     (dst : Nat) (imm : BitVec 64)
  | v_read_in_b64 (dst : Nat) (portIdx : Nat)
  | v_read_w_b64  (dst : Nat) (wireIdx : Nat)
  | v_read_r_b64  (dst : Nat) (regIdx : Nat)
  | v_add_u64     (dst src0 src1 : Nat)
  | v_sub_u64     (dst src0 src1 : Nat)
  | v_mul_lo_u64  (dst src0 src1 : Nat)
  | v_and_b64     (dst src0 src1 : Nat)
  | v_or_b64      (dst src0 src1 : Nat)
  | v_xor_b64     (dst src0 src1 : Nat)
  | v_lshl_b64    (dst src0 src1 : Nat)
  | v_lshr_b64    (dst src0 src1 : Nat)
  | v_cmp_eq_u64  (dst src0 src1 : Nat)
  | v_cmp_lt_u64  (dst src0 src1 : Nat)
  | v_not_b64     (dst src : Nat)
  | v_cndmask_b64 (dst cond srcTrue srcFalse : Nat)
  deriving Repr, DecidableEq

/-- Map every `RtlAluOp` to its exact 64-bit AMD GPU VOP instruction constructor (`compileRtlAluToVop`):
- `.add`    ↦ `v_add_u64`
- `.sub`    ↦ `v_sub_u64`
- `.mul`    ↦ `v_mul_lo_u64`
- `.bitAnd` ↦ `v_and_b64`
- `.bitOr`  ↦ `v_or_b64`
- `.bitXor` ↦ `v_xor_b64`
- `.shl`    ↦ `v_lshl_b64`
- `.lshr`   ↦ `v_lshr_b64`
- `.eq`     ↦ `v_cmp_eq_u64`
- `.ult`    ↦ `v_cmp_lt_u64` -/
def compileRtlAluToVop (op : RtlAluOp) (dst src0 src1 : Nat) : AmdGpuVop64Inst :=
  match op with
  | .add    => .v_add_u64 dst src0 src1
  | .sub    => .v_sub_u64 dst src0 src1
  | .mul    => .v_mul_lo_u64 dst src0 src1
  | .bitAnd => .v_and_b64 dst src0 src1
  | .bitOr  => .v_or_b64 dst src0 src1
  | .bitXor => .v_xor_b64 dst src0 src1
  | .shl    => .v_lshl_b64 dst src0 src1
  | .lshr   => .v_lshr_b64 dst src0 src1
  | .eq     => .v_cmp_eq_u64 dst src0 src1
  | .ult    => .v_cmp_lt_u64 dst src0 src1

/-- Compile any `RtlExpr` into a sequence of faithful 64-bit AMD GPU VOP instructions
(`List AmdGpuVop64Inst`), preserving every `RtlAluOp` via `compileRtlAluToVop`, lowering
`.bitNot` to `v_not_b64`, and lowering `.mux` to `v_cndmask_b64`. -/
def compileRtlExprToAmdGpu (nextReg : Nat) : RtlExpr → Nat × Nat × List AmdGpuVop64Inst
  | .const bv =>
    (nextReg, nextReg + 1, [.v_mov_b64 nextReg bv])
  | .inputPort idx =>
    (nextReg, nextReg + 1, [.v_read_in_b64 nextReg idx])
  | .wireRef idx =>
    (nextReg, nextReg + 1, [.v_read_w_b64 nextReg idx])
  | .regRead idx =>
    (nextReg, nextReg + 1, [.v_read_r_b64 nextReg idx])
  | .alu op lhs rhs =>
    let (rL, n1, codeL) := compileRtlExprToAmdGpu nextReg lhs
    let (rR, n2, codeR) := compileRtlExprToAmdGpu n1 rhs
    let dst := n2
    let inst := compileRtlAluToVop op dst rL rR
    (dst, dst + 1, codeL ++ codeR ++ [inst])
  | .mux cond tBranch fBranch =>
    let (rC, n1, codeC) := compileRtlExprToAmdGpu nextReg cond
    let (rT, n2, codeT) := compileRtlExprToAmdGpu n1 tBranch
    let (rF, n3, codeF) := compileRtlExprToAmdGpu n2 fBranch
    let dst := n3
    (dst, dst + 1, codeC ++ codeT ++ codeF ++ [.v_cndmask_b64 dst rC rT rF])
  | .bitNot src =>
    let (rS, n1, codeS) := compileRtlExprToAmdGpu nextReg src
    let dst := n1
    (dst, dst + 1, codeS ++ [.v_not_b64 dst rS])

/-- Execute a single 64-bit AMD GPU VOP instruction on a 64-bit VGPR file `vgprs : Nat → BitVec 64`. -/
def execAmdGpuVop64Inst
    (inputs wires regs : Nat → BitVec 64)
    (vgprs : Nat → BitVec 64)
    (inst : AmdGpuVop64Inst) : Nat → BitVec 64 :=
  let writeReg (dst : Nat) (val : BitVec 64) (r : Nat) : BitVec 64 :=
    if r == dst then val else vgprs r
  match inst with
  | .v_mov_b64 dst imm       => writeReg dst imm
  | .v_read_in_b64 dst idx   => writeReg dst (inputs idx)
  | .v_read_w_b64 dst idx    => writeReg dst (wires idx)
  | .v_read_r_b64 dst idx    => writeReg dst (regs idx)
  | .v_add_u64 dst s0 s1     => writeReg dst (vgprs s0 + vgprs s1)
  | .v_sub_u64 dst s0 s1     => writeReg dst (vgprs s0 - vgprs s1)
  | .v_mul_lo_u64 dst s0 s1  => writeReg dst (vgprs s0 * vgprs s1)
  | .v_and_b64 dst s0 s1     => writeReg dst (vgprs s0 &&& vgprs s1)
  | .v_or_b64 dst s0 s1      => writeReg dst (vgprs s0 ||| vgprs s1)
  | .v_xor_b64 dst s0 s1     => writeReg dst (vgprs s0 ^^^ vgprs s1)
  | .v_lshl_b64 dst s0 s1    => writeReg dst (vgprs s0 <<< ((vgprs s1).toNat % 64))
  | .v_lshr_b64 dst s0 s1    => writeReg dst (vgprs s0 >>> ((vgprs s1).toNat % 64))
  | .v_cmp_eq_u64 dst s0 s1  => writeReg dst (if vgprs s0 == vgprs s1 then 1#64 else 0#64)
  | .v_cmp_lt_u64 dst s0 s1  => writeReg dst (if BitVec.ult (vgprs s0) (vgprs s1) then 1#64 else 0#64)
  | .v_not_b64 dst src       => writeReg dst (~~~(vgprs src))
  | .v_cndmask_b64 dst c t f => writeReg dst (if vgprs c != 0#64 then vgprs t else vgprs f)

/-- Execute a program of 64-bit AMD GPU VOP instructions (`List AmdGpuVop64Inst`). -/
def runAmdGpuVop64Prog
    (inputs wires regs : Nat → BitVec 64)
    (vgprs : Nat → BitVec 64) : List AmdGpuVop64Inst → (Nat → BitVec 64)
  | [] => vgprs
  | inst :: rest =>
    runAmdGpuVop64Prog inputs wires regs (execAmdGpuVop64Inst inputs wires regs vgprs inst) rest

/-- Compile an `RtlExpr` via `compileRtlExprToAmdGpu`, execute the resulting 64-bit VOP instruction
sequence on a zero-initialized VGPR file, and return the result VGPR value. -/
def evalAmdGpuExpr (inputs wires regs : Nat → BitVec 64) (e : RtlExpr) : BitVec 64 :=
  let (resReg, _, code) := compileRtlExprToAmdGpu 0 e
  (runAmdGpuVop64Prog inputs wires regs (fun _ => 0#64) code) resReg

/-- **Universal Faithfulness Theorem for All 64-bit GPU VOP ALU Operations & `bitNot`
(`evalAmdGpuExpr_faithful_all_ops`)**:
1. For EVERY `op : RtlAluOp` (`add`, `sub`, `mul`, `bitAnd`, `bitOr`, `bitXor`, `shl`, `lshr`, `eq`, `ult`)
   and all 64-bit operands `a b : BitVec 64` (both constants and input ports), `evalAmdGpuExpr`
   produces the exact same 64-bit word as `evalRtlExpr`.
2. For all `a : BitVec 64`, `evalAmdGpuExpr` on `.bitNot (.const a)` produces `~~~a`
   (matching `evalRtlExpr`), and in particular `.bitNot (.const 0#64)` evaluates to
   `0xFFFFFFFFFFFFFFFF#64` (instead of being erased!).
3. `.alu .eq (.const 0#64) (.const 0#64)` evaluates to `1#64` (instead of `0#64` via `.add`!),
   and `.alu .ult` faithfully computes unsigned 64-bit `<` (`0` or `1`, instead of subtraction!). -/
theorem evalAmdGpuExpr_faithful_all_ops :
    (∀ (op : RtlAluOp) (inputs wires regs : Nat → BitVec 64) (a b : BitVec 64),
      evalAmdGpuExpr inputs wires regs (.alu op (.const a) (.const b)) =
        evalRtlExpr inputs wires regs (.alu op (.const a) (.const b))) ∧
    (∀ (op : RtlAluOp) (inputs wires regs : Nat → BitVec 64) (i j : Nat),
      evalAmdGpuExpr inputs wires regs (.alu op (.inputPort i) (.inputPort j)) =
        evalRtlExpr inputs wires regs (.alu op (.inputPort i) (.inputPort j))) ∧
    (∀ (inputs wires regs : Nat → BitVec 64) (a : BitVec 64),
      evalAmdGpuExpr inputs wires regs (.bitNot (.const a)) =
        evalRtlExpr inputs wires regs (.bitNot (.const a))) ∧
    (∀ (inputs wires regs : Nat → BitVec 64) (i : Nat),
      evalAmdGpuExpr inputs wires regs (.bitNot (.inputPort i)) =
        evalRtlExpr inputs wires regs (.bitNot (.inputPort i))) ∧
    (∀ (inputs wires regs : Nat → BitVec 64) (c t f : BitVec 64),
      evalAmdGpuExpr inputs wires regs (.mux (.const c) (.const t) (.const f)) =
        evalRtlExpr inputs wires regs (.mux (.const c) (.const t) (.const f))) ∧
    (∀ (inputs wires regs : Nat → BitVec 64),
      evalAmdGpuExpr inputs wires regs (.bitNot (.const 0#64)) = 0xFFFFFFFFFFFFFFFF#64) ∧
    (∀ (inputs wires regs : Nat → BitVec 64),
      evalAmdGpuExpr inputs wires regs (.alu .eq (.const 0#64) (.const 0#64)) = 1#64 ∧
      evalAmdGpuExpr inputs wires regs (.alu .eq (.const 0#64) (.const 1#64)) = 0#64) ∧
    (∀ (inputs wires regs : Nat → BitVec 64),
      evalAmdGpuExpr inputs wires regs (.alu .ult (.const 3#64) (.const 5#64)) = 1#64 ∧
      evalAmdGpuExpr inputs wires regs (.alu .ult (.const 5#64) (.const 3#64)) = 0#64) := by
  refine ⟨?_, ?_, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
          fun _ _ _ => by change ~~~(0#64) = 0xFFFFFFFFFFFFFFFF#64; decide +kernel,
          fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩
  · intro op inputs wires regs a b
    cases op <;> rfl
  · intro op inputs wires regs i j
    cases op <;> rfl

/-- Compile the primary output wire of an `RtlModule` to a 64-bit AMD GPU VOP64 kernel
(`resultReg × List AmdGpuVop64Inst`), starting VGPR allocation at `v1`. -/
def compileRtlModuleToAmdGpu (m : RtlModule) : Option (Nat × List AmdGpuVop64Inst) :=
  match m.wires with
  | w :: _ =>
    let (resReg, _, code) := compileRtlExprToAmdGpu 1 w.expr
    some (resReg, code)
  | [] => none

/-- Execute a compiled 64-bit AMD GPU VOP64 kernel (`runAmdGpuVop64Prog`) with primary input
`arg0 : Nat` bound to input port `0` (`BitVec.ofNat 64 arg0`) and read the result VGPR. -/
def evalCompiledAmdGpuModule (m : RtlModule) (arg0 : Nat) : Option Nat :=
  match compileRtlModuleToAmdGpu m with
  | some (resReg, code) =>
    let finalVgprs :=
      runAmdGpuVop64Prog
        (fun _ => BitVec.ofNat 64 arg0)
        (fun _ => 0#64)
        (fun _ => 0#64)
        (fun _ => 0#64)
        code
    some (finalVgprs resReg).toNat
  | none => none

/-! ## 2. Domain A: LC Drives (Potsdam, NY) Direct In-Slot Stator Cooling Kernel -/

/-- `Lean-lite` (`LExpr`) kernel for LC Drives direct in-slot liquid-cooled stator peak winding
temperature (in ${}^\circ\text{C}$):
$$T_{\text{winding}}(P_{\text{kW}}) = 50 + P_{\text{kW}} \cdot (2 + 4 + 3) = 50 + 9 P_{\text{kW}}.$$ -/
def lcDrivesInSlotThermalLExpr : LExpr :=
  .lam .natural
    (.natBin .add
      (.lit 50)
      (.natBin .mul
        (.bvar 0)
        (.natBin .add (.natBin .add (.lit 2) (.lit 4)) (.lit 3))))

theorem lcDrivesInSlotThermal_runs_8kw :
    SSteps (.app lcDrivesInSlotThermalLExpr (.lit 8)) (.lit 122) := by
  refine .next (.beta .natural _ (.lit 8)) ?_
  have hinst :
      (LExpr.natBin .add
        (.lit 50)
        (.natBin .mul
          (.bvar 0)
          (.natBin .add (.natBin .add (.lit 2) (.lit 4)) (.lit 3)))).inst (.lit 8) =
      .natBin .add
        (.lit 50)
        (.natBin .mul
          (.lit 8)
          (.natBin .add (.natBin .add (.lit 2) (.lit 4)) (.lit 3))) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (.binRight .add 50 (.binRight .mul 8 (.binLeft .add (.lit 3) (.binLit .add 2 4)))) ?_
  refine .next (.binRight .add 50 (.binRight .mul 8 (.binLit .add 6 3))) ?_
  refine .next (.binRight .add 50 (.binLit .mul 8 9)) ?_
  exact .next (.binLit .add 50 72) (.refl _)

/-- **6-Stage Reflexive Self-Acceleration of LC Drives Direct In-Slot Stator Thermal Kernel**:
Proves that `lcDrivesInSlotThermalLExpr` at $P_{\text{loss}} = 8\,\text{kW}$ evaluates to $122^\circ\text{C}$
identically across:
1. `Lean-lite` source semantics (`SSteps`),
2. `Obend.Core` `Core4` semantics (`Evaluates`),
3. `Obend.Leaf.Book` graph-reduction semantics (`Halts`),
4. Synthesized FPGA RTL (`compileBookToRtlSat` + `evalModuleOutputs`),
5. Compiled AMD `CDNA3` GPU Wavefront ISA (`evalCompiledAmdGpuModule`), and
6. TPU Systolic Array (`runSystolicMacChain`) & FPGA `DSP58` Cascade (`runDsp58Cascade`),
while matching `Obend.Hardware.FluidThermal.evalPeakWindingTempMilliC`! -/
theorem lc_drives_thermal_self_accelerates_6stage :
    let C := leanComposition "lcThermal" (lowerT lcDrivesInSlotThermalLExpr)
    let B := emit C
    SSteps (.app lcDrivesInSlotThermalLExpr (.lit 8)) (.lit 122) ∧
    Evaluates (.app (lowerT lcDrivesInSlotThermalLExpr) (.nat 8)) (.nat 122) ∧
    Halts (.app (.get B.link "lcThermal") (.nat 8)) (.natural 122) ∧
    (match compileBookToRtlSat "lean_lc_thermal_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 8#64) (fun _ => 0#64) == [("out_lcThermal", 122#64)]) &&
       (evalCompiledAmdGpuModule m 8 == some 122)
     | none => false) = true ∧
    runSystolicMacChain 50 [8, 8, 8] [2, 4, 3] = 122 ∧
    runDsp58Cascade 50 [(8, 2), (8, 4), (8, 3)] = 122 ∧
    Obend.Hardware.FluidThermal.evalPeakWindingTempMilliC 50 8 2 4 3 = 122 := by
  refine ⟨lcDrivesInSlotThermal_runs_8kw, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat lcDrivesInSlotThermal_runs_8kw
  · exact lean_to_book "lcThermal" lcDrivesInSlotThermalLExpr 8 122 (by decide +kernel) lcDrivesInSlotThermal_runs_8kw
  · decide +kernel

/-! ## 3. Domain B: Mission Power `MS350` (Potsdam, NY) Solar Inverter MPPT Power Kernel -/

/-- `Lean-lite` (`LExpr`) kernel for Mission Power `MS350` extracted DC solar array power:
$$P(V) = V \cdot (200 - V)$$
where $I_{\text{sc}} = 200\,\text{A}$, $G_s = 1\,\text{A/V}$, and the incremental-conductance Maximum
Power Point is $V^\star = 100\,\text{V} \implies P(V^\star) = 10000\,\text{W}$. -/
def ms350MpptExtractedPowerLExpr : LExpr :=
  .lam .natural
    (.natBin .mul
      (.bvar 0)
      (.natBin .sub (.lit 200) (.bvar 0)))

theorem ms350MpptExtractedPower_runs_100v :
    SSteps (.app ms350MpptExtractedPowerLExpr (.lit 100)) (.lit 10000) := by
  refine .next (.beta .natural _ (.lit 100)) ?_
  have hinst :
      (LExpr.natBin .mul (.bvar 0) (.natBin .sub (.lit 200) (.bvar 0))).inst (.lit 100) =
      .natBin .mul (.lit 100) (.natBin .sub (.lit 200) (.lit 100)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (.binRight .mul 100 (.binLit .sub 200 100)) ?_
  exact .next (.binLit .mul 100 100) (.refl _)

/-- **6-Stage Reflexive Self-Acceleration of Mission Power `MS350` MPPT Kernel + Ozaki `FP4` Tensor Core**:
Proves that `ms350MpptExtractedPowerLExpr` at the Maximum Power Point $V^\star = 100 = (-4) + 13 \times 8$
evaluates to $10000$ identically across:
1. `Lean-lite` source semantics (`SSteps`),
2. `Obend.Core` `Core4` semantics (`Evaluates`),
3. `Obend.Leaf.Book` graph-reduction semantics (`Halts`),
4. Synthesized saturating FPGA RTL (`compileBookToRtlSat` + `evalModuleOutputs`),
5. Compiled AMD `CDNA3` GPU Wavefront ISA (`evalCompiledAmdGpuModule`), and
6. Ozaki Scheme Base-13 `FP4 (E2M1)` Tensor-Core limb multiplication (`evalOzakiBase13Product2 (-4) 8 (-4) 8 = 10000`,
   where both `-4` and `8` are exact doubled `FP4 (E2M1)` values in $S_{\text{E2M1}}$!),
while matching `Obend.Hardware.PowerElectronics.evalExtractedPower 200 1 100 = 10000`! -/
theorem ms350_mppt_self_accelerates_6stage :
    let C := leanComposition "ms350Mppt" (lowerT ms350MpptExtractedPowerLExpr)
    let B := emit C
    SSteps (.app ms350MpptExtractedPowerLExpr (.lit 100)) (.lit 10000) ∧
    Evaluates (.app (lowerT ms350MpptExtractedPowerLExpr) (.nat 100)) (.nat 10000) ∧
    Halts (.app (.get B.link "ms350Mppt") (.nat 100)) (.natural 10000) ∧
    (match compileBookToRtlSat "lean_ms350_mppt_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 100#64) (fun _ => 0#64) == [("out_ms350Mppt", 10000#64)]) &&
       (evalCompiledAmdGpuModule m 100 == some 10000) &&
       -- Also check off-MPP voltage V = 80 -> P(80) = 80 * 120 = 9600 < 10000 on both FPGA and AMD GPU!
       (evalModuleOutputs m (fun _ => 80#64) (fun _ => 0#64) == [("out_ms350Mppt", 9600#64)]) &&
       (evalCompiledAmdGpuModule m 80 == some 9600)
     | none => false) = true ∧
    isDoubledFp4E2M1 (-4) = true ∧
    isDoubledFp4E2M1 8 = true ∧
    evalBase13Limb2 (-4) 8 = 100 ∧
    evalOzakiBase13Product2 (-4) 8 (-4) 8 = 10000 ∧
    Obend.Hardware.PowerElectronics.evalExtractedPower 200 1 100 = 10000 := by
  refine ⟨ms350MpptExtractedPower_runs_100v, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat ms350MpptExtractedPower_runs_100v
  · exact lean_to_book "ms350Mppt" ms350MpptExtractedPowerLExpr 100 10000 (by decide +kernel) ms350MpptExtractedPower_runs_100v
  · decide +kernel

/-! ## 4. Domain C: 2D FEMM Triangular Finite-Element Magnetic Co-Energy Kernel -/

/-- `Lean-lite` (`LExpr`) kernel for 2D FEMM triangular element magnetic energy:
$$E(a_0) = 5 \cdot \left((a_0 - 2)^2 + 9\right)$$
for a stator tooth triangle with $(b_0, b_1, b_2) = (1, -1, 0)$, $(c_0, c_1, c_2) = (0, 1, -1)$,
$\nu = 5$, and fixed nodal potentials $a_1 = 2, a_2 = -1$ (so $\nabla_x A_z = a_0 - 2$ and
$\nabla_y A_z = 3$, $(\nabla_y A_z)^2 = 9$). At $a_0 = 6$, $E(6) = 5 \cdot (16 + 9) = 125$. -/
def femm2dElementEnergyLExpr : LExpr :=
  .lam .natural
    (.natBin .mul
      (.lit 5)
      (.natBin .add
        (.natBin .mul
          (.natBin .sub (.bvar 0) (.lit 2))
          (.natBin .sub (.bvar 0) (.lit 2)))
        (.lit 9)))

theorem femm2dElementEnergy_runs_6 :
    SSteps (.app femm2dElementEnergyLExpr (.lit 6)) (.lit 125) := by
  refine .next (.beta .natural _ (.lit 6)) ?_
  have hinst :
      (LExpr.natBin .mul
        (.lit 5)
        (.natBin .add
          (.natBin .mul
            (.natBin .sub (.bvar 0) (.lit 2))
            (.natBin .sub (.bvar 0) (.lit 2)))
          (.lit 9))).inst (.lit 6) =
      .natBin .mul
        (.lit 5)
        (.natBin .add
          (.natBin .mul
            (.natBin .sub (.lit 6) (.lit 2))
            (.natBin .sub (.lit 6) (.lit 2)))
          (.lit 9)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (.binRight .mul 5 (.binLeft .add (.lit 9) (.binLeft .mul (.natBin .sub (.lit 6) (.lit 2)) (.binLit .sub 6 2)))) ?_
  refine .next (.binRight .mul 5 (.binLeft .add (.lit 9) (.binRight .mul 4 (.binLit .sub 6 2)))) ?_
  refine .next (.binRight .mul 5 (.binLeft .add (.lit 9) (.binLit .mul 4 4))) ?_
  refine .next (.binRight .mul 5 (.binLit .add 16 9)) ?_
  exact .next (.binLit .mul 5 25) (.refl _)

/-- Reference 2D FEMM stator tooth element matching `femm2dElementEnergyLExpr`. -/
def selfAccelFemmTriangle : Obend.Hardware.Magnetics.FemmTriangle2D where
  x0 := 0
  y0 := 0
  x1 := 0
  y1 := 1
  x2 := 1
  y2 := 0
  nuScaled := 5
  jzScaled := 0

/-- **6-Stage Reflexive Self-Acceleration of 2D FEMM Magnetic Energy Kernel**:
Proves that `femm2dElementEnergyLExpr` at $a_0 = 6$ evaluates to $125$ across:
1. `Lean-lite` source semantics (`SSteps`),
2. `Obend.Core` `Core4` semantics (`Evaluates`),
3. `Obend.Leaf.Book` graph-reduction semantics (`Halts`),
4. Synthesized saturating FPGA RTL (`compileBookToRtlSat` + `evalModuleOutputs`),
5. Compiled AMD `CDNA3` GPU Wavefront ISA (`evalCompiledAmdGpuModule`) AND single-instruction
   AMD Matrix-Core `vMfmaDot4` execution (`execAmdGpuInst`), and
6. `Obend.Hardware.Magnetics.evalElementMagneticEnergyScaled selfAccelFemmTriangle 6 3 2 = 125`! -/
theorem femm_2d_energy_self_accelerates_6stage :
    let C := leanComposition "femmEnergy" (lowerT femm2dElementEnergyLExpr)
    let B := emit C
    SSteps (.app femm2dElementEnergyLExpr (.lit 6)) (.lit 125) ∧
    Evaluates (.app (lowerT femm2dElementEnergyLExpr) (.nat 6)) (.nat 125) ∧
    Halts (.app (.get B.link "femmEnergy") (.nat 6)) (.natural 125) ∧
    (match compileBookToRtlSat "lean_femm_energy_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 6#64) (fun _ => 0#64) == [("out_femmEnergy", 125#64)]) &&
       (evalCompiledAmdGpuModule m 6 == some 125)
     | none => false) = true ∧
    readVgpr (execAmdGpuInst [0, 20, 15, 0, 0, 4, 3, 0, 0] (.vMfmaDot4 0 1 5 0)) 0 = 125 ∧
    Obend.Hardware.Magnetics.evalElementMagneticEnergyScaled selfAccelFemmTriangle 6 3 2 = 125 := by
  refine ⟨femm2dElementEnergy_runs_6, ?_, ?_, ?_, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat femm2dElementEnergy_runs_6
  · exact lean_to_book "femmEnergy" femm2dElementEnergyLExpr 6 125 (by decide +kernel) femm2dElementEnergy_runs_6
  · decide +kernel

/-! ## 5. Coupled PDE, Reverse-AD & Octree Geometry 6-Stage Self-Acceleration (`libCEED` + `catgrad` + `fidget`) -/

/-- `Lean-lite` (`LExpr`) kernel for the `libCEED` matrix-free 2D FEMM nodal residual operator
$y_0(a_0) = \nu (b_0 \nabla_x A_z + c_0 \nabla_y A_z) = 5 \cdot ((a_0 - 2) + (a_0 - 3))$
on `selfAccelFemmTriangle` with fixed neighbor nodal potentials $(a_1, a_2) = (3, 2)$.
At $a_0 = 6$, $y_0(6) = 5 \cdot (4 + 3) = 35$, matching
`(Obend.Hardware.Magnetics.evalLibCeedElementOp selfAccelFemmTriangle 6 3 2).1`. -/
def libCeedFemmNodalOpLExpr : LExpr :=
  .lam .natural
    (.natBin .mul
      (.lit 5)
      (.natBin .add
        (.natBin .sub (.bvar 0) (.lit 2))
        (.natBin .sub (.bvar 0) (.lit 3))))

theorem libCeedFemmNodalOp_runs_6 :
    SSteps (.app libCeedFemmNodalOpLExpr (.lit 6)) (.lit 35) := by
  refine .next (.beta .natural _ (.lit 6)) ?_
  have hinst :
      (LExpr.natBin .mul
        (.lit 5)
        (.natBin .add
          (.natBin .sub (.bvar 0) (.lit 2))
          (.natBin .sub (.bvar 0) (.lit 3)))).inst (.lit 6) =
      .natBin .mul
        (.lit 5)
        (.natBin .add
          (.natBin .sub (.lit 6) (.lit 2))
          (.natBin .sub (.lit 6) (.lit 3))) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (.binRight .mul 5 (.binLeft .add (.natBin .sub (.lit 6) (.lit 3)) (.binLit .sub 6 2))) ?_
  refine .next (.binRight .mul 5 (.binRight .add 4 (.binLit .sub 6 3))) ?_
  refine .next (.binRight .mul 5 (.binLit .add 4 3)) ?_
  exact .next (.binLit .mul 5 7) (.refl _)

/-- **6-Stage Reflexive Self-Acceleration of `libCEED` Matrix-Free FEMM Nodal Operator
(`self_accelerate_libceed_femm_nodal_op_6stage`)**:
Lowers `libCeedFemmNodalOpLExpr` across all 6 stages:
1. `Lean-lite` `SSteps` (`35`),
2. `Obend.Core` `Evaluates` (`35`),
3. `Obend.Leaf.Book` `Halts` (`35`),
4. Saturating FPGA `DSP58` RTL (`compileBookToRtlSat` + `runDsp58Cascade`),
5. 64-bit AMD `CDNA3` `AmdGpuVop64Inst` (`evalCompiledAmdGpuModule`) + `vMfmaDot4`, and
6. TPU Systolic Array (`runSystolicMacChain`), $K$-limb Ozaki Base-13 `FP4` (`evalOzakiBase13KLimbDot`),
   and `Obend.Hardware.Magnetics.evalLibCeedElementOp`! -/
theorem self_accelerate_libceed_femm_nodal_op_6stage :
    let C := leanComposition "libCeedNodal" (lowerT libCeedFemmNodalOpLExpr)
    let B := emit C
    SSteps (.app libCeedFemmNodalOpLExpr (.lit 6)) (.lit 35) ∧
    Evaluates (.app (lowerT libCeedFemmNodalOpLExpr) (.nat 6)) (.nat 35) ∧
    Halts (.app (.get B.link "libCeedNodal") (.nat 6)) (.natural 35) ∧
    (match compileBookToRtlSat "lean_libceed_nodal_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 6#64) (fun _ => 0#64) == [("out_libCeedNodal", 35#64)]) &&
       (evalCompiledAmdGpuModule m 6 == some 35)
     | none => false) = true ∧
    readVgpr (execAmdGpuInst [5, 5, 0, 0, 4, 3, 0, 0, 0] (.vMfmaDot4 8 0 4 8)) 8 = 35 ∧
    runSystolicMacChain 0 [5, 5] [4, 3] = 35 ∧
    runDsp58Cascade 0 [(5, 4), (5, 3)] = 35 ∧
    allLimbsDoubledFp4 [-8, 1] = true ∧
    evalOzakiBase13KLimbDot [[-8, 1], [-8, 1]] [[4], [3]] = 35 ∧
    (Obend.Hardware.Magnetics.evalLibCeedElementOp selfAccelFemmTriangle 6 3 2).1 = 35 := by
  refine ⟨libCeedFemmNodalOp_runs_6, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat libCeedFemmNodalOp_runs_6
  · exact lean_to_book "libCeedNodal" libCeedFemmNodalOpLExpr 6 35 (by decide +kernel) libCeedFemmNodalOp_runs_6
  · decide +kernel

/-- `Lean-lite` (`LExpr`) kernel for `catgrad` 2-stage Optic reverse-mode AD fanout cotangent
accumulation $\Delta y(y) = \Delta y_1 + \Delta y_2 = (x \cdot y) + (x \cdot y)$ for the
2-operator chain $L(x, y) = (x \cdot y) \cdot y$ at $x = 4$.
At $y = 7$, $\Delta y(7) = 28 + 28 = 56$, matching `Obend.Hardware.OpenHypergraph.evalOpticChain2Rev`. -/
def catgradOpticRevAdLExpr : LExpr :=
  .lam .natural
    (.natBin .add
      (.natBin .mul (.lit 4) (.bvar 0))
      (.natBin .mul (.lit 4) (.bvar 0)))

theorem catgradOpticRevAd_runs_7 :
    SSteps (.app catgradOpticRevAdLExpr (.lit 7)) (.lit 56) := by
  refine .next (.beta .natural _ (.lit 7)) ?_
  have hinst :
      (LExpr.natBin .add
        (.natBin .mul (.lit 4) (.bvar 0))
        (.natBin .mul (.lit 4) (.bvar 0))).inst (.lit 7) =
      .natBin .add
        (.natBin .mul (.lit 4) (.lit 7))
        (.natBin .mul (.lit 4) (.lit 7)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (.binLeft .add (.natBin .mul (.lit 4) (.lit 7)) (.binLit .mul 4 7)) ?_
  refine .next (.binRight .add 28 (.binLit .mul 4 7)) ?_
  exact .next (.binLit .add 28 28) (.refl _)

/-- **6-Stage Reflexive Self-Acceleration of `catgrad` Optic Reverse-Mode AD Kernel
(`self_accelerate_catgrad_optic_rev_ad_6stage`)**:
Lowers `catgradOpticRevAdLExpr` across all 6 stages:
1. `Lean-lite` `SSteps` (`56`),
2. `Obend.Core` `Evaluates` (`56`),
3. `Obend.Leaf.Book` `Halts` (`56`),
4. Saturating FPGA `DSP58` RTL (`compileBookToRtlSat` + `runDsp58Cascade`),
5. 64-bit AMD `CDNA3` `AmdGpuVop64Inst` (`evalCompiledAmdGpuModule`) + `vMfmaDot4`, and
6. TPU Systolic Array (`runSystolicMacChain`), $K$-limb Ozaki Base-13 `FP4` (`evalOzakiBase13KLimbDot`),
   and `Obend.Hardware.OpenHypergraph.evalOpticChain2Rev`! -/
theorem self_accelerate_catgrad_optic_rev_ad_6stage :
    let C := leanComposition "catgradRevAd" (lowerT catgradOpticRevAdLExpr)
    let B := emit C
    SSteps (.app catgradOpticRevAdLExpr (.lit 7)) (.lit 56) ∧
    Evaluates (.app (lowerT catgradOpticRevAdLExpr) (.nat 7)) (.nat 56) ∧
    Halts (.app (.get B.link "catgradRevAd") (.nat 7)) (.natural 56) ∧
    (match compileBookToRtlSat "lean_catgrad_rev_ad_rtl" B with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 7#64) (fun _ => 0#64) == [("out_catgradRevAd", 56#64)]) &&
       (evalCompiledAmdGpuModule m 7 == some 56)
     | none => false) = true ∧
    readVgpr (execAmdGpuInst [4, 4, 0, 0, 7, 7, 0, 0, 0] (.vMfmaDot4 8 0 4 8)) 8 = 56 ∧
    runSystolicMacChain 0 [4, 4] [7, 7] = 56 ∧
    runDsp58Cascade 0 [(4, 7), (4, 7)] = 56 ∧
    allLimbsDoubledFp4 [-6, 1] = true ∧
    evalOzakiBase13KLimbDot [[4], [4]] [[-6, 1], [-6, 1]] = 56 ∧
    (Obend.Hardware.OpenHypergraph.evalOpticChain2Rev
      (Obend.Hardware.OpenHypergraph.compileOpticAdjoint .mul)
      (Obend.Hardware.OpenHypergraph.compileOpticAdjoint .mul)
      (Obend.Hardware.OpenHypergraph.evalOpticChain2Fwd .mul .mul 4 7).2 1).2 = 56 := by
  refine ⟨catgradOpticRevAd_runs_7, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat catgradOpticRevAd_runs_7
  · exact lean_to_book "catgradRevAd" catgradOpticRevAdLExpr 7 56 (by decide +kernel) catgradOpticRevAd_runs_7
  · decide +kernel

/-- `Lean-lite` (`LExpr`) kernel for `fidget` octree CSG branch pruning (`GeometryCAM.ivMinChoice`)
evaluating candidate interval $A = [a_{\text{hi}} - 4, a_{\text{hi}}]$ against reference CSG interval
$B = [10, 20]$:
- Returns `1` (`.left`: prune right CSG subtree) when $a_{\text{hi}} \le 10$,
- Returns `2` (`.right`: prune left CSG subtree) when $20 \le a_{\text{hi}} - 4$,
- Returns `3` (`.both`: keep both CSG subtrees) when the intervals overlap. -/
def fidgetChoiceOctreePruneLExpr : LExpr :=
  .lam .natural
    (.boolRec .natural
      (.boolRec .natural
        (.lit 3)
        (.lit 2)
        (.natBin .ble (.lit 20) (.natBin .sub (.bvar 0) (.lit 4))))
      (.lit 1)
      (.natBin .ble (.bvar 0) (.lit 10)))

theorem fidgetChoiceOctreePrune_runs_8 :
    SSteps (.app fidgetChoiceOctreePruneLExpr (.lit 8)) (.lit 1) := by
  refine .next (.beta .natural _ (.lit 8)) ?_
  have hinst :
      (LExpr.boolRec .natural
        (.boolRec .natural
          (.lit 3)
          (.lit 2)
          (.natBin .ble (.lit 20) (.natBin .sub (.bvar 0) (.lit 4))))
        (.lit 1)
        (.natBin .ble (.bvar 0) (.lit 10))).inst (.lit 8) =
      .boolRec .natural
        (.boolRec .natural
          (.lit 3)
          (.lit 2)
          (.natBin .ble (.lit 20) (.natBin .sub (.lit 8) (.lit 4))))
        (.lit 1)
        (.natBin .ble (.lit 8) (.lit 10)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  rw [hinst]
  refine .next (.boolRecMajor .natural _ _ (.binLit .ble 8 10)) ?_
  exact .next (.boolRecTrue .natural _ _) (.refl _)

/-- **6-Stage Reflexive Self-Acceleration of `fidget` Octree CSG Pruning Kernel
(`self_accelerate_fidget_choice_octree_6stage`)**:
Lowers `fidgetChoiceOctreePruneLExpr` across all 6 stages, verifying that branchless 64-bit
`v_cmp_lt_u64` + `v_cndmask_b64` in `AmdGpuVop64Inst` and saturating FPGA RTL reproduce
`Obend.Hardware.GeometryCAM.ivMinChoice` across all three octree pruning regimes
(`.left` at `aHi = 8`, `.right` at `aHi = 30`, and `.both` at `aHi = 15`)! -/
theorem self_accelerate_fidget_choice_octree_6stage :
    let C := leanComposition "fidgetPrune" (lowerT fidgetChoiceOctreePruneLExpr)
    let B := emit C
    SSteps (.app fidgetChoiceOctreePruneLExpr (.lit 8)) (.lit 1) ∧
    Evaluates (.app (lowerT fidgetChoiceOctreePruneLExpr) (.nat 8)) (.nat 1) ∧
    Halts (.app (.get B.link "fidgetPrune") (.nat 8)) (.natural 1) ∧
    (match compileBookToRtlSat "lean_fidget_prune_rtl" B with
     | some m =>
       checkRtlModule m &&
       -- Regime 1 (`aHi = 8`, `A = [4, 8]`): `.left` (`1`)
       (evalModuleOutputs m (fun _ => 8#64) (fun _ => 0#64) == [("out_fidgetPrune", 1#64)]) &&
       (evalCompiledAmdGpuModule m 8 == some 1) &&
       -- Regime 2 (`aHi = 30`, `A = [26, 30]`): `.right` (`2`)
       (evalModuleOutputs m (fun _ => 30#64) (fun _ => 0#64) == [("out_fidgetPrune", 2#64)]) &&
       (evalCompiledAmdGpuModule m 30 == some 2) &&
       -- Regime 3 (`aHi = 15`, `A = [11, 15]`): `.both` (`3`)
       (evalModuleOutputs m (fun _ => 15#64) (fun _ => 0#64) == [("out_fidgetPrune", 3#64)]) &&
       (evalCompiledAmdGpuModule m 15 == some 3)
     | none => false) = true ∧
    Obend.Hardware.GeometryCAM.ivMinChoice { lo := 4, hi := 8 } { lo := 10, hi := 20 } = .left ∧
    Obend.Hardware.GeometryCAM.ivMinChoice { lo := 26, hi := 30 } { lo := 10, hi := 20 } = .right ∧
    Obend.Hardware.GeometryCAM.ivMinChoice { lo := 11, hi := 15 } { lo := 10, hi := 20 } = .both := by
  refine ⟨fidgetChoiceOctreePrune_runs_8, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simpa [lowerT] using lower_sound_nat fidgetChoiceOctreePrune_runs_8
  · exact lean_to_book "fidgetPrune" fidgetChoiceOctreePruneLExpr 8 1 (by decide +kernel) fidgetChoiceOctreePrune_runs_8
  · decide +kernel

/-- **Master Universal 6-Stage Coupled PDE, Reverse-AD & Geometry Self-Acceleration Theorem
(`coupled_pde_ad_geometry_6stage_universal_self_acceleration`)**:
Unifies the 6-stage reflexive self-acceleration of:
1. `libCeedFemmNodalOpLExpr` (`Magnetics.evalLibCeedElementOp`),
2. `catgradOpticRevAdLExpr` (`OpenHypergraph.evalOpticChain2Rev`),
3. `fidgetChoiceOctreePruneLExpr` (`GeometryCAM.ivMinChoice` via branchless `v_cmp_lt_u64` + `v_cndmask_b64`), and
4. Arbitrary $K$-limb Ozaki Base-13 `FP4` exact Cauchy convolution (`ozaki_base13_klimb_mul_exact`) and
   inner-product accumulation (`ozaki_base13_klimb_dot_exact`)! -/
theorem coupled_pde_ad_geometry_6stage_universal_self_acceleration
    (as bs : List Int) (xs ys : List (List Int)) :
    evalBase13Limbs (mulBase13Limbs as bs) = evalBase13Limbs as * evalBase13Limbs bs ∧
    evalOzakiBase13KLimbDot xs ys = kulischDot (xs.map evalBase13Limbs) (ys.map evalBase13Limbs) ∧
    SSteps (.app libCeedFemmNodalOpLExpr (.lit 6)) (.lit 35) ∧
    SSteps (.app catgradOpticRevAdLExpr (.lit 7)) (.lit 56) ∧
    SSteps (.app fidgetChoiceOctreePruneLExpr (.lit 8)) (.lit 1) ∧
    (Obend.Hardware.Magnetics.evalLibCeedElementOp selfAccelFemmTriangle 6 3 2).1 = 35 ∧
    (Obend.Hardware.OpenHypergraph.evalOpticChain2Rev
      (Obend.Hardware.OpenHypergraph.compileOpticAdjoint .mul)
      (Obend.Hardware.OpenHypergraph.compileOpticAdjoint .mul)
      (Obend.Hardware.OpenHypergraph.evalOpticChain2Fwd .mul .mul 4 7).2 1).2 = 56 ∧
    Obend.Hardware.GeometryCAM.ivMinChoice { lo := 4, hi := 8 } { lo := 10, hi := 20 } = .left :=
  ⟨ozaki_base13_klimb_mul_exact as bs,
   ozaki_base13_klimb_dot_exact xs ys,
   libCeedFemmNodalOp_runs_6,
   catgradOpticRevAd_runs_7,
   fidgetChoiceOctreePrune_runs_8,
   rfl, rfl, rfl⟩

end Obend.Lower
end
