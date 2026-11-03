# Hardware-Assisted Lean 4, "Meat-on-Bones" `.obend` Foundations, Cloud-FPGA Qualification Ladder & The 8 Flagship Userspace Applications

This document is the authoritative, unscoped engineering specification for **Wave 4** of Objective Bend. Every component closes a real external verification, hardware simulation, or sovereign execution loop—eliminating simplified "combinational-only" or "host-precomputed" shortcuts so the **fullest version** of every pipeline and demo operates end-to-end.

---

## 0. The 6 Unscoped Interoperability Mandates ("No Scoped-Down Subsets")

1. **Unified `.obend` Front-End Parity (`Obend.Spec.*` AND `Obend.Elab.Workbook` / `Obend.Hardware.UserspacePhysical`)**:
   - Every new language and compiler capability—bitwise/shift operators (`&`, `|`, `^`, `~`, `<<`, `>>`, `>>>`), signed 64-bit & fixed-point (`Q16.16` / `Q32.32`, `slt`, `sle`, `qmul32`), hex literals (`0x...`), multi-argument methods, `RtlLayoutCtx` packed struct slices (`.record`, `.get`, `.extend`), sum tag-muxes (`.inject`, `.case`), sequential `always_ff @(posedge clk)` state registers (`compileStatefulStepToRtl`), and `AutoCert` `by judge(...)` synthesis—is wired through **both** `Obend.Spec.{Parse,Elaborate,FrontEnd}` (`obend check` / `obend run`) **and** `Obend.Elab.Workbook` + `Obend.Hardware.UserspacePhysical` (`#import_obend`, `obend verilate`, `obend tapeout`).
2. **True Handle-Level Hardware Stack Machine in Zone 4 (`stepZone4StackFsm`, Zero Host Precomputation)**:
   - Zone 4 of `SiliconElabFabric` (`lean/Obend/Lower/SiliconElabFabric.lean` and `obend_zone4_kernel_fsm` in `silicon_elab_top.sv`) implements a complete, recursive handle-level bidirectional type inference and declaration checker (`hwCamInferType` / `hwCamCheckDecl` / `stepZone4StackFsm`) with an explicit hardware work-stack (`WorkFrame`) and de Bruijn binder-type context stack (`ctxHandles : List CamHandle`), plus `HwCamLevelEntry` and `HwCamSymbolEntry` tables in the `OBCAMv1` DMA frame. The Verilated RTL checks declarations in real clock cycles without calling `KExpr`-based `kernelCheckDecl` or `encodeDeclStatusTag` on the host.
3. **Complete Transitive `Lean.Environment` Cone & Recursor $\iota$-Rule Extraction (`extractLeanEnvCone`)**:
   - `lean/Obend/Lower/ExprCAM.lean` extracts not only single `.defnInfo`/`.thmInfo` nodes, but the **entire transitive declaration cone** from a live `Lean.Environment`, including `.inductInfo`, `.ctorInfo`, and **`.recInfo` (`Lean.RecursorVal` $\to$ `List KRecRule` via `extractLeanRecRules`)**, stripping `.mdata` in `fromLeanExpr` so $\iota$-reduction on pattern-matching and structural recursion works on real Lean 4 declarations.
4. **Hierarchical SystemVerilog Macro Emission (`emitHierarchicalSV`) & Canonical `hardware/sim/`**:
   - `lean/Obend/Hardware/{HDL,Silicon,ReductionMachine}.lean` emits lint-clean, synthesizable hierarchical SystemVerilog-2012 modules (`emitHierarchicalSV`) for all verified hardware macro blocks: 4-stage `DSP48E2` MAC, `URAM288` with RAW collision bypass, 2-slot `AXI4-Stream` skid buffer, 2D XY credit-flow `NocRouter` mesh, `ICAP` DPR tile wrapper with glitch-free isolation fence, and 88-bit `HwExprCAM`. Static Oct 31 `.sv`/`.smt2` files in `hardware/sim/` are replaced by the live output of `obend hardware emit-sv` and `obend verilate`.
5. **Real In-Core Decode & Sequential `always_ff` State Across All Userspace `apps/`**:
   - `apps/obend-risc/` decodes raw 32/64-bit instructions (`opcode`, `rd`, `funct3`, `rs1`, `rs2`, sign-extended `imm`) *inside* `.obend` using bitwise/shift primitives and maintains its own `pc`, CSRs (`mstatus`, `mepc`, `mcause`), and register file in `always_ff` hardware registers (never offloading decode or `pc`/regfile storage to C++).
   - `apps/foc-hil/`, `apps/sdr-ft8/`, and `apps/zk-ntt/` use real `always_ff` integral accumulators, CIC integrator/comb delay lines ($z^{-1}$), CORDIC pipeline stages, and sumcheck round accumulators, plus compile-time `AutoCert` certificates.
6. **Single Unified `crates/obend-fpga-hal` Aperture Driving `Verilator`, `obend-node`, `obend-gui`, and AWS EC2 F2 (`vu47p`)**:
   - One unified PCIe BAR0 (`AXI4-Lite`) + 512-bit `AXI4-Stream` DMA HAL (`crates/obend-fpga-hal`) serves `#silicon_check` / `by silicon_*`, `obend verilate`, `obend-node` sovereign batch acceleration, `obend-gui` live telemetry, and the AWS EC2 F2 `cl_obend` (`vu47p`) custom logic shell.

---

## 1. The 5 Foundational "Meat-on-Bones" Upgrades (`Foundation A`–`Foundation E`)

### 1.1 Foundation A — Multi-Argument, `RtlLayoutCtx` Struct/Union Slices & Stateful `always_ff` RTL/GPU Lowering
- **`lean/Obend/Hardware/Types.lean`**:
  - Defines `widthMask64`, `RtlLayoutCtx` (`structSlices : List (String × (Nat × Nat))`, `unionTagBits : Nat`, `unionArms : List (String × (Nat × Nat))`), `compileSliceExtractRtl`, `compileSliceInsertRtl`, `compileSliceUpdateRtl`, and `compileTagInjectRtl`.
  - Proves `compileSliceExtract_insert_disjoint_sound` and `compileTagInject_caseMux_sound`.
- **`lean/Obend/Hardware/Compiler.lean` & `SelfAccelerate.lean`**:
  - `compileRichTerm` lowers arbitrary $k$-argument lambdas (`peelLambdas`), `.record`, `.get` (both `self` calls and bit-slice / state-register projections), `.extend` (functional slice updates), `.inject`, and `.case` (with payload de Bruijn binder `ePay :: varEnv`) to `RtlExpr` and 64-bit AMD `AmdGpuVop64Inst`.
  - `StatefulStepSpec` & `compileStatefulStepToRtl` lower stateful `.obend` `contract` `step(state, input) -> state'` and multi-register `record` declarations into sequential `RtlModule`s with parallel 64-bit `always_ff @(posedge clk)` state registers (`RegSpec`), AXI4-Stream `in_valid`/`in_ready`/`out_valid` handshakes, and proved cycle-for-cycle simulation equivalence (`compileStatefulStepToRtl_simulates_step`, `compileStatefulStepToRtl_trace_sound`).

### 1.2 Foundation B — Signed Fixed-Point (`Q16.16` / `Q32.32`), Bitwise/Shift Ops & Hex Literals
- **`lean/Obend/Core/Term.lean`**:
  - Extends `Obend.Core.Term.Primitive` with `.bitAnd`, `.bitOr`, `.bitXor`, `.shl`, `.lshr`, `.ashr`, `.slt`, and `.qmul32` over the 64-bit two's-complement carrier (`word64 n : BitVec 64`), preserving all existing `Term` and `Ty` constructors and substitution/lifting theorems.
- **`lean/Obend/Spec/{Parse,Elaborate}.lean`, `lean/Obend/Elab/Workbook.lean` & `lean/Obend/Hardware/UserspacePhysical.lean`**:
  - Adds hex literals (`0x...`), fixed-point `q32` helpers (`q32FromInt`, `q32ToInt`, `qmul32`), infix operators (`<<`, `>>`, `>>>`, `&`, `|`, `^`, `<s`), and named intrinsics (`bitAnd`, `bitOr`, `bitXor`, `bitNot`, `shl`, `lshr`, `ashr`, `slt`, `sle`, `qmul32`) across both the full `.obend` parser and `#import_obend`.
- **`lean/Obend/Hardware/HDL.lean`**:
  - Extends `RtlAluOp`, `evalAluOp`, and `emitAluOpSV` with `.ashr` (`$signed(a) >>> b[5:0]`), `.slt` (`$signed(a) < $signed(b)`), and `.qmul32` (`64'((128'($signed(a)) * 128'($signed(b))) >>> 32)`).

### 1.3 Foundation C — Automatic Certificate Synthesis (`AutoCert`, `lean/Obend/Elab/AutoCert.lean`)
- Automatically synthesizes and wire-encodes external judge witnesses during `.obend` elaboration (`Workbook.elaborateObendSource` and `FrontEnd.elaborateContractsWithCerts`) for:
  1. **`"interval@1"`**: Extracts variable box bounds and target inequality into `IntervalObj`, runs interval evaluation + adaptive bisection (`IntervalCert.bisect`), and encodes `encodeIntervalObj` / `encodeIntervalCert`.
  2. **`"taylor-model@1"`**: Evaluates degree-$k$ Taylor models (`tmAdd`, `tmSub`, `tmScale`, `tmMul`, `tmExpCertified`, `tmSinCertified`, `tmCosCertified`, `picardStepLinear`) and encodes `encodeTaylorModelQuery` / `encodeTaylorModelCert`.
  3. **`"sos-lyapunov-cbf@1"`**: Extracts `SosLyapunovProblem` ($V(x)$, $f(x)$, $B(x)$, algebraic constraints $g_j(x) = 0$), performs polynomial reduction with quotient tracking (`polyReduceWithQuotients`), completes squares into `SOSPoly` Gram witnesses, and encodes `encodeSosLyapunovProblem` / `encodeSosLyapunovCert`.
  4. **`"groebner@1"`**: Runs `polyDivModWithQuotients` + bounded S-polynomial Buchberger completion with cofactor tracking to synthesize `GroebnerCert.membership` / `.positivstellensatz` witnesses and encodes `encodeGroebnerQuery` / `encodeGroebnerCert`.
  5. **`"rtl-synth@1"` / `"hw-rtl-synth@1"`**: Synthesizes the target `Leaf.Book` via `compileBookToRtlSat` / `compileStatefulStepToRtl`, checks `checkRtlSynth`, and encodes `encodeRtlSynthObj` / `encodeRtlSynthCert`.
- **Soundness (`synthesizeClaimExternalJudge_sound`)**: Every synthesized payload is gated by `obligationCheckWithJudges workbookFormats .total c.obligation just == .ok` and proved sound via `Obend.Logic.obligationWithJudges_sound`.

### 1.4 Foundation D — Hierarchical SystemVerilog Macro Emission (`emitHierarchicalSV`) & `hardware/sim/` Cleanup
- **`lean/Obend/Hardware/HDL.lean` & `Silicon.lean` & `ReductionMachine.lean`**:
  - Adds `emitHierarchicalSV` emitting standalone, synthesizable SystemVerilog-2012 macro modules for:
    - `obend_macro_dsp48e2` (4-stage pipelined `DSP48E2` multiply-accumulate matching `Silicon.stepDspMac`),
    - `obend_macro_uram288_bypass` (synchronous RAM with RAW collision bypass matching `Silicon.stepBypassRAM`),
    - `obend_macro_axis_skid` (2-slot `AXI4-Stream` skid buffer matching `Silicon.stepSkid`),
    - `obend_macro_noc_router_xy` (5-port 2D XY dimension-ordered credit-flow router matching `ReductionMachine.stepNocFabric`),
    - `obend_macro_icap_dpr_tile` (reconfigurable LUT6/carry tile with glitch-free isolation fence `isolated ? skidHeldOutput : activeOut` matching `UserspacePhysical.evalReconfigTile`).
- **`hardware/sim/` Canonicalization**:
  - Purges the static Oct 31 files (`obend_hw.sv`, `obend_silicon_process.sv`, `obend_efpga_fabric.sv`, `lec_check.smt2`, `lec_fabric.smt2`, `openlane_sky130_config.json`, `multiphysics_sim`) and wires `hardware/sim/` directly to `obend hardware emit-sv` and `obend verilate`.

### 1.5 Foundation E — First-Class `obend verilate` Differential Co-Simulation & `Z3` `QF_BV` LEC (`lean/Obend/Hardware/VerilateRunner.lean`)
- **`obend verilate <input.obend> [--top <name>] [--vectors N] [--cycles C] [--vcd <out.vcd>] [--lec]`**:
  - **Rung 1**: Emits SystemVerilog via `emitModuleSV` / `emitHierarchicalSV`, generates a C++17 `Verilator` harness with `Verilated::randReset(2)` (pseudo-random initialization of reset-free pipeline stages) and `VerilatedVcdC` waveform dumping, and verifies $0$ bit mismatches across $N \times C$ clock cycles against both `Obend.Core.MachineFast.evalFuelFast` and `Obend.Hardware.HDL.runModuleTrace`.
  - **Rung 2 (`--lec`)**: Lowers the module to a gate-level `TechNetlist` (`BelGate.lut2`, `BelGate.carry4`, `BelGate.dsp48`, `BelGate.fdre` via `Synth.synthesizeModuleToBels`, plus `Yosys` `write_smt2` when present), emits `<target>_lec.smt2`, invokes `z3 -smt2 <target>_lec.smt2`, and verifies `unsat` ($0$ counterexamples across all $2^{64 \times k}$ states).

---

## 2. North Star End-Target 1: Live Hardware-Assisted Lean 4 & Reflexive Self-Hosting

### 2.1 88-Bit `PackedNodeWord` (`BitVec 88`) & Complete 7-Section `OBCAMv1` Binary Wire Protocol
Each `PackedNodeWord` in `Obend.Lower.ExprCAM.HwExprCAM` is packed via `packNodeWord88` / `unpackNodeWord88` (`unpack_packNodeWord88` proved in `lean/Obend/Lower/ExprCAM.lean:1819-1877`) into a 16-byte aligned DMA beat:
- `[15:0]`: `h0` (16b) | `[31:16]`: `h1` (16b) | `[47:32]`: `h2` (16b) | `[63:48]`: `symIdx` (16b) | `[79:64]`: `maxLooseBVar` (16b)
- `[80]`: `hasFVar` (1b) | `[81]`: `hasMVar` (1b) | `[82]`: `hasLooseBVar` (1b) | `[83]`: `0` (1b) | `[87:84]`: `tag` (4b)
- `[113:88]`: `hash26` (26b) | `[127:114]`: `pad0` (14b)

A complete `SiliconElabWireFrame` (`OBCAMv1`) contains:
1. **Header (`64 B`, `SiliconElabWireHeader`)**: Magic `0x31564D4143424F00` (`"\0OBCAMV1"`), `version = 1`, `flags`, `nodeCount`, `symbolCount`, `levelCount`, `constCount`, `recRuleCount`, `lutEntryCount`, `icapFrameCount`, `targetDeclSymIdx`, `targetExprHandle`, `targetTypeHandle`, `fuelBudget`, `envPinDigest64`.
2. **Section 1**: `PackedNodeWord` table ($N_{\text{nodes}} \times 16\text{ B}$).
3. **Section 2**: `HwCamSymbolEntry` table ($N_{\text{syms}} \times 16\text{ B}$: `sortEntry`, `constEntry`, `litEntry`, `projEntry`).
4. **Section 3**: `HwCamLevelEntry` table ($N_{\text{levels}} \times 16\text{ B}$: `.zero`, `.succ`, `.max`, `.imax`, `.param` for hardware `kernelLevelEq` / `imax` impredicativity).
5. **Section 4**: `HwCamConstEntry` table ($N_{\text{consts}} \times 16\text{ B}$).
6. **Section 5**: `HwCamRecRuleEntry` table ($N_{\text{rec}} \times 16\text{ B}$).
7. **Section 6 & 7**: Zone 3 `DiscrTreeLutEntry` ($N_{\text{lut}} \times 16\text{ B}$) & `IcapBitstreamFrame` ($N_{\text{icap}} \times 16\text{ B}$) tables.

### 2.2 5-Module Hierarchical `silicon_elab_top.sv` (`emitSiliconElabFabricSV`)
1. **`obend_zone1_expr_cam`**: 88-bit associative CAM/SRAM, handle-level `hwCamLiftLooseBVars` / `hwCamInstantiateAt`, and 1-cycle closed-term $\beta$-substitution bypass (`!body_has_loose_bvar || body_max_loose_bvar <= depth`).
2. **`obend_zone2_noc_unifier`**: $2 \times 2$ 2D XY credit-flow NoC mesh parallelizing `.app f1 a1 =?= .app f2 a2` obligations with 1-cycle handle-equality short-circuit (`h1 == h2`), bit-80/81 occurs-check filter, and hardware `joinMCtxAssigns?` conflict detector.
3. **`obend_zone3_discr_lut`**: 1-cycle `@[simp]` `DiscrTree` LUT gated by `SlotGuardReg` and 3-phase glitch-free `ICAP` DPR isolation fence (`pin_fallback_to_zone1` asserted in 1 cycle on stale pins).
4. **`obend_zone4_kernel_fsm`**: True handle-level stack-machine typechecker (`stepZone4StackFsm`) with hardware work-stack (`hw_work_stack[0:255]`), de Bruijn binder context stack (`hw_ctx_stack[0:255]`), and universe level evaluator (`level_mem[0:1023]`).
5. **`silicon_elab_top`**: Top-level AXI4-Lite + 128/512-bit AXI4-Stream wrapper compiled by `Verilator` into `crates/obend-fpga-hal` (`libobend_silicon_rtl` / `obend-silicon-sim`).

### 2.3 Live Lean 4 Commands, All 5 `by silicon_*` Tactics & Reflexive Self-Hosting (`lean/Obend/Tactic/SiliconElab.lean`)
- **`#silicon_check <DeclName>`**:
  - Extracts the full transitive declaration + inductive + recursor cone from `Lean.Environment` (`extractLeanEnvCone`), serializes `OBCAMv1`, runs both `stepZone4StackFsm` and Verilated `silicon_elab_top.sv`, verifies bit-exact agreement, and logs hardware clock cycles, CAM hit rate, 1-cycle closed-term $\beta$-bypasses, NoC flits, and LUT hits.
- **Reflexive Self-Hosting Milestone (`silicon_self_hosting_milestone_sound`)**:
  - Executes `#silicon_check` on `Obend.Lower.LeanKernel.kernelCheckDecl`, `Obend.Lower.SiliconElabFabric.stepSiliconKernelCamFsm`, and `Obend.Core.type_preservation`—proving and demonstrating the Verilated RTL hardware kernel checking its own Lean 4 source declarations in real clock cycles.
- **All 5 Proof-Reconstructing Tactics (Untrusted Hardware Oracle $\to$ Kernel-Verified Lean 4 Proof Term)**:
  1. **`by silicon_simp`**: Runs Zone 3 hardware `DiscrTree` LUT matching + Zone 1 WHNF and reconstructs a Lean kernel proof from the matched `@[simp]` theorem trace.
  2. **`by silicon_eqsat`**: Saturates the goal in `Obend.Analysis.EqSatHypergraph.HyperEGraph`, extracts the Clairvoyant minimum-cost DAG, and closes the goal via `eqSat_preserves_eval_and_adjoint`.
  3. **`by silicon_sos`**: Synthesizes the SOS Gram / Lyapunov / CBF witness and closes the goal via `sos_cert_implies_nonneg`, `checkSosLyapunov_sound`, or `checkSosCbf_sound`.
  4. **`by silicon_interval`**: Evaluates Taylor Model / branch-and-bound interval enclosures and closes the goal via `taylorModel_transcendental_enclosure_sound` or `verifyRealBoundSubdiv_sound`.
  5. **`by silicon_flowpipe`**: Synthesizes an $N$-dimensional validated Picard flowpipe enclosure (`Obend.Analysis.Flowpipe`) and closes ODE trajectory reachability goals via `picard_step_encloses_trajectory` / `taylorModel_picard_sound`.

---

## 3. North Star End-Targets 2 & 3: Unified Cloud-FPGA HAL (`crates/obend-fpga-hal`), Live DPR Deoptimization, `obend-node` & `obend-gui`

### 3.1 Unified BAR0 (`AXI4-Lite`) & 512-Bit `AXI4-Stream` Aperture (`crates/obend-fpga-hal/src/regs.rs`)
| BAR0 Offset | Aperture | Registers |
| :--- | :--- | :--- |
| `0x0000..0x00FF` | **Global Shell, Clock & DMA Ring CSRs** | `OBEND_MAGIC` (`"OBENDF20"`), `OBEND_VERSION_CAPS`, `OBEND_CTRL` (`AP_START`, `AP_DONE`, `SOFT_RST`, `STEP_ONCE`, `DPR_ISOLATE_EN`), `OBEND_CYCLE_COUNT`, `DMA_TX_RING`, `DMA_RX_RING` |
| `0x0100..0x03FF` | **Generic `.obend` Core I/O & ILA State Snapshot** | `OBEND_IN_PORT[0..31]`, `OBEND_OUT_PORT[0..31]`, `OBEND_STATE_SNAP[0..31]` (`always_ff` architectural state readback), `OBEND_DPR_SLOT_GUARD_PIN` |
| `0x0400..0x04FF` | **4-Zone `SiliconElabFabric` Co-Processor CSRs** | `SILICON_CTRL_STATUS`, `TARGET_EXPR_H`, `TARGET_TYPE_H`, `TARGET_DECL_SYM`, `FUEL_BUDGET`, `RESULT_STATUS`, `PERF_CYCLES`, `PERF_CAM_HITS`, `PERF_CAM_ALLOCS`, `PERF_BYPASS_CNT`, `PERF_NOC_FLITS`, `PERF_LUT_HITS`, `ZONE3_MATCH_THM` |

- **Backends**:
  1. **Rung 3 (`sim_backend.rs` + `verilator_daemon_bridge.hpp`)**: `4 MiB` POSIX shared memory (`shm_open` + `mmap`) + Unix domain control socket driving Verilated `silicon_elab_top.sv` and compiled `.obend` cores at $\ge 1\text{ M cycles/s}$.
  2. **Rung 4 (`aws_f2_backend.rs` + `hardware/aws-f2/cl_obend_shell_bridge.sv`)**: AWS EC2 F2 (`vu47p` `cl_obend`) `/dev/fpga0` BAR0 MMIO (`sh_ocl_*`) + `/dev/xdma0_{h2c,c2h}_0` 512-bit `AXI4-Stream` (`sh_pcis_*`) driver + `synth_cl_obend.tcl`.
- **Live Specialization Deoptimization & `obend-gui` / `obend-node` Wiring**:
  - When a `.obend` layer or environment pin mutates at runtime, `dprTileSlot` / `SlotGuardReg` blocks the stale specialized LUT in 1 cycle (`moved_pin_blocks`), asserts `DPR_ISOLATE_EN` (`skidHeldOutput` clamp), loads the updated `IcapBitstreamFrame` over BAR0/DMA, and releases the fence without dropping a single control tick.
  - Wired into `crates/obend-node` (for hardware-accelerated batch/turn verification) and `crates/obend-gui` (exposing live Verilator / FPGA cycle counters and waveform telemetry).

---

## 4. North Star 4: All 8 Flagship Userspace Applications (`apps/`)

| # | Application Directory & Lean Module | Full-Stack Architecture & Qualification Criteria |
| :--- | :--- | :--- |
| **1** | **`apps/obend-risc/`**<br>(`lean/Obend/Apps/ObendRisc.lean`) | **3-Layer Open-Recursive Sequential RISC Softcore CPU**:<br>• `BaseRiscCore.obend` $\gg$ `PrivilegeCsrOverride.obend` $\gg$ `CustomSimdZkExt.obend`.<br>• **In-core instruction bit-slice decoding** (`opcode`, `rd`, `funct3`, `rs1`, `rs2`, sign-extended `imm`) using `.obend` bitwise/shift ops (`&`, `|`, `^`, `<<`, `>>`, `>>>`, `slt`).<br>• **True `always_ff` architectural registers** (`pc`, `mstatus`, `mepc`, `mcause`, `x1..x15`) + `imem`/`dmem` bus outputs.<br>• Proves `risc_base_opcode_non_interference` via `by weave` + SMT2 LEC; boots `firmware/test_prog.hex` (Fibonacci + CSR trap/mret + SIMD/ZK MAC) in `Verilator` with `.vcd` waveform. |
| **2** | **`apps/foc-hil/`**<br>(`lean/Obend/Apps/FocHil.lean`) | **Closed-Loop 20 kHz Field-Oriented Motor Drive + 6-Level SiC FCML Inverter HIL**:<br>• Multi-argument struct-packed stateful `always_ff` `.obend` controller (`ClarkePark.obend` $\to$ `PiCurrentLoop.obend` with `int_d`/`int_q` accumulators $\to$ `SosCbfThermalBarrier.obend` + FCML Lyapunov capacitor balancer).<br>• **Compile-time `AutoCert` synthesis** of `by judge("sos-lyapunov-cbf@1")`, `by judge("taylor-model@1")`, and `by judge("interval@1")`.<br>• Closed-loop 20 kHz `Verilator` co-simulation against 500,000-step ($\Delta t = 100\text{ ns}$) continuous-time RK4 `LC Drives` IPM + `MS350` SiC plant, including **live mid-run ICAP DPR layer hot-swap** and over-temperature 1-cycle trip. |
| **3** | **`apps/sdr-ft8/`**<br>(`lean/Obend/Apps/SdrFt8.lean`) | **All-Digital 40m Tayloe IQ SDR & 4-Stage CORDIC FT8 Demodulator**:<br>• Signed fixed-point (`Q16.16`/`Q32.32`) stateful `always_ff` `.obend` receiver chain (`QuadratureNcoMixer.obend` $\to$ `CicDecimator.obend` with 3-stage $z^{-1}$ integrator/comb registers $\to$ `PolyphaseFirImageReject.obend` $\to$ `CordicFt8ToneExtractor.obend` with $\Delta\phi[n] = \phi[n] - \phi[n-1]$ state).<br>• Processes 16,384-sample IQ stream in `Verilator`, suppressing a $+40\text{ dB}$ lower-sideband image interferer by $\ge 60\text{ dB}$ IRR and recovering 79/79 FT8 symbols. |
| **4** | **`apps/zk-ntt/`**<br>(`lean/Obend/Apps/ZkNtt.lean`) | **Goldilocks ($p = 2^{64} - 2^{32} + 1$) 256-Point NTT & 8-Round Sumcheck Co-Processor (RTL + AMD `VOP64`)**:<br>• 128-to-64-bit Goldilocks reduction ($2^{64} \equiv 2^{32}-1 \pmod p$) using `.obend` shifts/masks, Cooley–Tukey radix-2 butterfly, and stateful `always_ff` Sumcheck round polynomial accumulators.<br>• Optimized via `EqSatHypergraph` ($\ge 30\%$ multiplier cost reduction), compiled to **both** 4-stage `resetFree` pipelined SystemVerilog (`Verilator`) **and** 64-bit AMD `VOP64` assembly (`SelfAccelerate.compileRtlExprToAmdGpu`), verified bit-exact on 256-point $\text{INTT}(\text{NTT}(x)) = x$ and 8-round Sumcheck. |
| **5** | **`apps/silicon-kernel-verilator/`**<br>(`lean/Obend/Apps/SiliconKernelVerilator.lean`) | **Verilated 4-Zone Silicon Elaborator & Live ICAP DPR Hot-Swap Showcase**:<br>• Streams compiled `.obend` and Lean `OBCAMv1` declaration bundles over 128/512-bit AXI4-Stream into `silicon_elab_top.sv` in `Verilator`.<br>• Performs a **live mid-stream 3-phase glitch-free ICAP eFPGA bitstream hot-swap** of Zone 3 (`admitSimpTheoremDpr`), demonstrates 1-cycle `moved_pin_blocks` fallback to Zone 1 WHNF on pin mutation, and verifies hardware refusal flags on `#tooth`-mutated proofs. |
| **6** | **`apps/fidget-cam/`**<br>(`lean/Obend/Apps/FidgetCam.lean`) | **Parametric `.obend` OpenUSD/F-Rep CAD $\to$ Pruned SSA Tape $\to$ Verilated Voxelizer, `.stl` Mesh & 5-Axis G-Code**:<br>• Authors a hierarchical OpenUSD/F-Rep mechanical part in `.obend` (with `LIVERPS` overrides for cooling channels and mounting bosses).<br>• Lowers to a linear SSA F-Rep tape (`GeometryCAM.lean`), runs interval pruning + backward-liveness compaction (`prune_and_compact_ssa_tape_sound`), compiles the pruned tape to SystemVerilog (`Verilator`), evaluates the 3D affine-arithmetic octree on the Verilated hardware pipeline, and writes out a real binary `.stl` 3D mesh file + gouge-verified 5-axis G-code toolpath. |
| **7** | **`apps/sovereign-drex/`**<br>(`lean/Obend/Apps/SovereignDrex.lean`) | **Live `DReX` + `K-CARRY` Hot-Upgradable Sovereign Exchange on a 4-Validator `obend-node` Cluster**:<br>• Multi-file `.obend` package (`Seat.obend`, `OrderBook.obend`, `BatchClearing.obend`) running on a 4-validator `obend-node` cluster coupled to `crates/obend-fpga-hal`.<br>• Submits live order batches, executes a mid-flight schema/law hot-upgrade via `K-CARRY` (`"world-carry@1"` in `Carry.lean`), kills and recovers a validator from its WAL (`DurableSimplexHost`), and verifies conservation of supply and zero double-execution. |
| **8** | **`apps/quantum-photonic-matter/`**<br>(`lean/Obend/Apps/QuantumPhotonicMatter.lean`) | **Planar Clements Photonic CTQW, Majorana Tetron Lindblad Co-Processor & 1-WL `catgrad` Quotient Hypergraph Accelerator**:<br>• Multi-layer `.obend` (`stdlib/physical/QuantumPhotonicMatter.obend`: `PlanarWaveguideMeshBase` $\gg$ `KrawtchoukFaddeevCompensatedOverride` and `TetronParitySectorBase` $\gg$ `LindbladCooledTetronOverride`).<br>• Runs 1-WL color refinement (`wlStabilize`) and `quotientOpenHypergraph` to compress an $N$-lane symmetric `StrictOpenHypergraph` + its `compileGraphAdjoint` reverse-AD pass down to an $r$-lane quotient (`quotientOpenHypergraph_intertwines_eval_and_adjoint`), guarded by `quotientHypergraphSlot` (`moved_pin_blocks` 1-cycle fallback on symmetry-breaking weight overrides).<br>• Synthesizes Lagrange–Sylvester spectral projectors (`computeLagrangeProjector`), verifies discrete-time Szegedy walk lumping (`cellUniformSzegedyPST_iff_quotient`), Faddeev–LeVerrier thermal crosstalk cancellation, Ivanov Majorana braiding ($T_{a,b} = 1 + \gamma_a\gamma_b$), and Lindblad parity cooling in `Verilator` and 64-bit AMD `VOP64`. |
