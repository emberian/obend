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

### 1.4 Foundation D — SystemVerilog emission and the one `silicon_elab_top` (status 2026-11-04)
- `Obend.Hardware.HDL.emitModuleSV` is the only emitter of `RtlModule`s. It writes one `clk`/`rst` pair per
  single-domain module (or `clk_<d>`/`rst_<d>` per domain), `(* ASYNC_REG = "TRUE" *)` on synchronizers, and is
  gated by `checkRtlModuleW` (DAG, CDC, two-flop chains, `checkWidths`).
- Widths (2026-11-05, answering `review/EXPERT-fpga-silicon-20261103.md` §3.5): values are still carried as
  `BitVec 64`, so `Compiler.lean` and `lower_to_rtl_sat_sound` are unchanged, and width is a checked refinement on
  top. Inputs, wires (`WireAssign.width`), registers (`RegSpec.width`) and outputs declare 1..64 bits (default 64);
  `RtlExpr.resize` carries `slice hi lo`, `zext w`, `sext from to` and `trunc w`, and `RtlExpr.concat` is a shift and
  an or. `inferWidthE` bounds every expression; `checkWidths` refuses, naming the signal, a signal driven by a wider
  expression or a slice outside its source. The theorems: a checked expression's value is below `2^w`
  (`evalRtlExpr_lt_of_inferWidthE`), every register stays inside its width through any trace (`runModuleTrace_lt`),
  and the port truncation is the identity (`evalModuleOutputsW_eq_of_checkWidths`). The emitter declares each signal
  `logic [w-1:0]`, reads narrow signals zero-extended and stores through `w'(...)`, so all arithmetic is still 64-bit
  in the text; a module whose signals are all 64 bits emits the bytes it did before.
  `Obend.Lower.lower_to_rtl_sat_sound_width` restates the apex at a `w`-bit port: when the compiled
  expression's inferred width fits `w`, the source-level hardware value of `lowerT e` is exactly a `BitVec w`, the
  value the port carries, zero-extended.
- Clock domains (§3.6): `stepModuleDomain m d` is one edge of `clk_<d>` (`d`'s registers latch, the rest hold,
  `stepModuleDomain_other_holds`), equal to `stepModuleRegs` for a one-domain module; `stepDomain_nonSync_reads_own_domain`
  says a non-synchronizer register passing `checkRegCdc` samples only its own domain's registers at its clock's edge
  (direct reads, the wire table held fixed; the wire-transitive form is not proved). `obend verilate` still drives
  all clocks on the same tick, so it checks the emitter, not asynchronous behaviour.
- The one `silicon_elab_top.sv` is `Obend.Lower.SiliconElabFabric.emitSiliconElabFabricSV`, written by
  `obend hardware emit-silicon-sv` to `apps/silicon-kernel-verilator/verilator/`. The two other copies (a hand-written
  Verilog-2001 file there and a string literal in `VerilateRunner`) were deleted; `hardware/README.md` says why.
- `lean/tools/emitsv` (`obend-emit-sv`) regenerates every checked-in emitted `.sv` (`risc`, `zk`, `fidget`, `drex`,
  `quantum`, the `hardware/sim/` cores and `obend_width_probe`, `ice40-mac8`) and the Lean goldens (`risc_golden.txt`,
  `zk_ntt_golden.txt`, the silicon-kernel harness); every verify script compares bytes and fails on a hand edit. Files
  the tool does not know are hand-written and say so in their header (`foc_drive_top.sv`, `sdr_ft8_top.sv`).
  (2026-11-05: `obend_risc_cpu.sv`, `zk_ntt_coproc.sv` and `sovereign_drex_batch_top.sv` regenerated once the apps built
  again; the zk transcript initial state in Lean was `340688748100`, not the documented `0x4F42454E44` = "OBEND",
  which the C++ reference in `goldilocks_ref.hpp` uses, and is now the latter.)
- The "hard-IP macro" strings in `HDL.lean` (`emitMacro*SV`) are not instantiated by any emitted design and are not
  tied to `Silicon.lean`'s models by any theorem; treat them as sketches.

### 1.5 Foundation E — `obend verilate` (`lean/Obend/Hardware/VerilateRunner.lean`)
- **Differential simulation**: emit with `emitModuleSV`, drive the Verilated module with `numVectors × numCycles`
  held-input cycles (small constants and a 16-bit LCG, masked to each input's width; default 16 × 4 = 64 cycles) and
  compare every output with Lean's `runModuleTrace`/`evalModuleOutputsW` of the same `RtlModule` (and `MachineFast` for
  `.obend` compositions). A module with several domains gets every `clk_<d>` toggled together. It refuses a module that
  fails `checkRtlModuleW`, printing the width reasons. `--top obend_width_probe` (`goldenWidthProbeRtl`) exercises
  narrow signals, every width operator and a two-flop crossing.
  This checks the emitter against Lean's own semantics; it is thin and is the thing to grow (wider vectors, more cycles,
  random reset).
- **LEC (`hardware/lec/lec.sh`, `Obend.Hardware.YosysLec`).** Every `verify_*.sh` whose `.sv` comes from
  an `RtlModule` (risc, zk, fidget, quantum, drex, and in `hardware/sim/` mac2, tcad, stator, mill and the width
  probe) proves the emitted `.sv` equal to Lean's model of the same module: Yosys reads the `.sv` (frontend and
  `proc`, `write_smt2`), `obend-emit-sv <target> --lec` writes the Lean half, and z3 must answer `unsat`; a planted
  one-bit mutation of a copy must answer `sat` with a counterexample. The Lean half is the print of one Lean
  value, `lecScript m`, and `lecScript_holds_iff` proves what z3 is asked: some output Yosys reads in state `s`, or
  register it reads in `s1`, differs at its width from Lean's step on the inputs and registers it reads in `s`.
  So `unsat` is agreement on every input and register state (sequential equivalence with registers matched by
  name) and `sat` is a real disagreement. For one clock domain with distinct register indices,
  `lecScript_unsat_of_step` states it against `evalModuleOutputsW` and `stepModuleRegs`. The clocking checked is
  Yosys's single global clock with each register reset by its own domain's `rst_<d>`; for several domains that is
  all clocks rising together, not the edge-by-edge `stepModuleDomain`. Trusted: Yosys's SystemVerilog frontend and
  `write_smt2`, z3, and the two print functions (`LecScript.print`, `SmtBV.print`) writing SMT-LIB syntax, which
  `lean/tests/silicon_elab/YosysLecTest.lean` pins against committed files. Where it terminates, EQY also proves
  the `.sv` equal to its own gate-level netlist (tcad, stator, mill, width probe, drex); see `hardware/README.md`.

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

### 2.2 The one `silicon_elab_top.sv` (`Obend.Lower.SiliconElabFabric.emitSiliconElabFabricSV`)
What the emitted RTL is today, read from the text, not from the zone names:
1. `obend_zone1_expr_cam`: a 256 × 88-bit register array (`cam_mem`, asynchronous reads, written under an
   asynchronous-reset `always_ff`), a focus register and the one-cycle closed-term β bypass
   (`app` whose function is a `lam` whose body has no loose bvar → focus moves to the body). Handles are assigned by
   the host; nothing in the RTL matches on content. "CAM" names the Lean structure (`HwExprCAM`), not the hardware.
2. `obend_zone2_noc_unifier`: the handle-equality short-circuit, the bit-81 mvar filter, and one instance of
   `obend_macro_noc_router_xy` fed a single flit; there is no mesh.
3. `obend_zone3_discr_lut`: a pinned-epoch comparator (`pin_valid && pkt_epoch == pinned_epoch`) in front of
   `obend_macro_icap_dpr_tile`, which is a `gain*x+offset` tile with a shadow configuration, an isolation hold value
   and a digest compare. It is a register swap behind a mux; there is no ICAP primitive, partial bitstream or
   reconfigurable partition, and none is claimed by the Lean model either (`ReconfigTileState.isolated : Bool`).
4. `obend_zone4_kernel_fsm`: a combinational code table (`1` Nat, `2` Prop, `3` Type, `5` Bool, `17` Nat→Nat,
   `34` ∀P:Prop,P→P) registered on `check_start`, with `sorryAx` and sort-mismatch status tags.
5. `silicon_elab_top`: wires the four together on one clock, no bus.
The harness (`apps/silicon-kernel-verilator/verilator/sim_main.cpp`) reads its expected values from
`silicon_elab_golden.txt`, written from the Lean model (`runVerilatorCoSimModel`) by `obend-emit-sv
golden-silicon-kernel`, so the Verilated RTL is checked against Lean's numbers rather than against literals.

### 2.3 Live Lean 4 Commands, All 5 `by silicon_*` Tactics & Reflexive Self-Hosting (`lean/Obend/Tactic/SiliconElab.lean`)
- **`#silicon_check <DeclName>`**:
  - Extracts the full transitive declaration + inductive + recursor cone from `Lean.Environment` (`extractLeanEnvCone`), serializes `OBCAMv1`, runs both `stepZone4StackFsm` and Verilated `silicon_elab_top.sv`, verifies bit-exact agreement, and logs hardware clock cycles, CAM hit rate, 1-cycle closed-term $\beta$-bypasses, NoC flits, and LUT hits.
- **Reflexive Self-Hosting Milestone (`silicon_self_hosting_milestone_sound`)**:
  - Executes `#silicon_check` on `Obend.Lower.LeanKernel.kernelCheckDecl`, `Obend.Lower.SiliconElabFabric.stepSiliconKernelCamFsm`, and `Obend.Core.Proofs.Preservation.typed_stepRaw_preserved`—proving and demonstrating the Verilated RTL hardware kernel checking its own Lean 4 source declarations in real clock cycles.
- **All 5 Proof-Reconstructing Tactics (Untrusted Hardware Oracle $\to$ Kernel-Verified Lean 4 Proof Term)**:
  1. **`by silicon_simp`**: Runs Zone 3 hardware `DiscrTree` LUT matching + Zone 1 WHNF and reconstructs a Lean kernel proof from the matched `@[simp]` theorem trace.
  2. **`by silicon_eqsat`**: Saturates the goal in `Obend.Analysis.HyperEGraph`, extracts the Clairvoyant minimum-cost DAG, and closes the goal via `eqSat_preserves_eval_and_adjoint`.
  3. **`by silicon_sos`**: Synthesizes the SOS Gram / Lyapunov / CBF witness and closes the goal via `sos_cert_implies_nonneg`, `checkSosLyapunov_sound`, or `checkSosCbf_sound`.
  4. **`by silicon_interval`**: Evaluates Taylor Model / branch-and-bound interval enclosures and closes the goal via `taylorModel_transcendental_enclosure_sound` or `verifyRealBoundSubdiv_sound`.
  5. **`by silicon_flowpipe`**: Synthesizes an $N$-dimensional validated Picard flowpipe enclosure (`Obend.Analysis.Flowpipe`) and closes ODE trajectory reachability goals via `picard_step_encloses_trajectory` / `taylorModel_picard_sound`.

---

## 3. The host side: `crates/obend-fpga-hal`, and what is documentation until a bitstream exists

### 3.1 Register map and the `MockBackend` (`crates/obend-fpga-hal/src/regs.rs`, `sim_backend.rs`)
| BAR0 Offset | Aperture | Registers |
| :--- | :--- | :--- |
| `0x0000..0x00FF` | Global, clock & DMA ring CSRs | `OBEND_MAGIC` (`"OBENDF20"`), `OBEND_VERSION_CAPS`, `OBEND_CTRL` (`AP_START`, `AP_DONE`, `SOFT_RST`, `STEP_ONCE`, `DPR_ISOLATE_EN`), `OBEND_CYCLE_COUNT`, `DMA_TX_RING`, `DMA_RX_RING` |
| `0x0100..0x03FF` | Core I/O & state snapshot | `OBEND_IN_PORT[0..31]`, `OBEND_OUT_PORT[0..31]`, `OBEND_STATE_SNAP[0..31]`, `OBEND_DPR_SLOT_GUARD_PIN` |
| `0x0400..0x04FF` | Fabric CSRs | `SILICON_CTRL_STATUS`, `TARGET_*`, `FUEL_BUDGET`, `RESULT_STATUS`, `PERF_*`, `ZONE3_MATCH_THM` |

- The only backend is `MockBackend`: Rust that computes what the registers would read. There is no Verilated model
  behind it (nothing links one) and no hardware backend. `obend-gui` and `obend-node` talk to this model through
  `ObendFpgaHal::auto_connect()`; `OBEND_FPGA_BACKEND` set to anything but `mock` is refused.
- The AWS F2 backend and `hardware/aws-f2/` were removed on 2026-11-04 (`hardware/README.md`): the bridge used a PCIS
  AXI4-Stream the F2 shell does not have and a Tcl flow that cannot produce an AFI. An F2 custom logic is written
  against the HDK on an instance.
- First physical target: the iCE40 HX1K on an iCEstick (`hardware/ice40/`), with the width-annotated emitted
  `obend_ice40_mac8` through yosys/nextpnr-ice40/icestorm.

### 3.2 PDK, DRC, FabuBlox, TCAD, wafer.space, PnR, retiming: documentation until a bitstream exists
`Obend.Hardware.{DRC,FabuBlox,TcadBridge,WaferSpace,PlaceRoute,Retiming,TapeoutPipeline}` and the `obend hardware
*-signoff` commands check certificates that are worked examples (`golden*` records in the modules; `TapeoutConfig`
defaults in the pipeline). No layout, deck, extraction or tool run of any design in this tree feeds them; the LVS
"signature" in `TapeoutPipeline` is derived from the BEL list on both sides. Their theorems are true of the records
they quantify over. `obend tapeout` therefore writes no signoff receipt (it refuses `--out-receipt`), and nothing in
this document should be read as a claim about GF180MCU, Sky130 or SG13G2 signoff.

### 3.3 An eFPGA bitstream read back and checked against Lean (`hardware/fabulous/`, 2026-11-05)
The one bitstream in this tree that a theorem is about. `obend_ice40_mac8` is built by FABulous's own flow on the
fabric of `hardware/fabulous/fabric.csv` (25 × (`W_IO` + 3 `LUT4AB`)). `Obend.Hardware.Fabulous.Bitstream` decodes the
`.bin` with FABulous's bitstream specification and routing graph and follows the configuration back to a `Net`
(LUT4 gates, flops with enable and set/reset, output pins); `obend fabric check` refuses a bitstream that does not
read back to the committed `mac8Net`, and with `--golden` names every differing bit it reads. For that net,
`Obend.Hardware.Fabulous.mac8_fabric_realizes_module` proves agreement with `iceStickMac8` on every cycle of every
in-width trace, and `mac8_fabric_realizes_module_from_reset` from any power-up flop state after one reset cycle.
Trusted: FABulous's metadata files, the decoder as compiled code (it is not proved to invert `bit_gen`; on this
design it agrees with nextpnr's FASM bit for bit), and `bv_decide`'s compiled LRAT check. FABulous's simulation of its
generated fabric RTL, configured through the self-write port with the same bitstream, agrees with the Lean model
cycle by cycle (`verify_fabric.sh`). The carry chain, `MUX8LUT`, block RAM, DSP and register-file tiles are not modelled.
The LUT4AB tile is modelled from FABulous's generated RTL (`Obend.Hardware.Fabulous.Tile`) and LEC'd against it by
Yosys and z3 (`hardware/fabulous/lec_tile.sh`); every routing pip the decoder reads agrees with that model
(`obend fabric tile-agree`, `pip_sound`). `smModule_eval_eq_SmPrim_eval` joins the LEC'd switch-matrix module to the
data-level model, and `readback_sound` composes the tiles: the grid's semantics is a consistency relation over every
wire (switch matrices through `smModule`, LUT4 cells through `lut4cModule`), the extraction emits a certificate of
every hop it took (`Mac8Cert.lean`, kernel-checked by `mac8Cert_check`), and `mac8_fabric_tiles_realize_module` states
the MAC result for every consistent run of a fabric with those tile models, wires and configuration bits, the decoder
no longer in the statement. Taken as given: the tiles' top-level wiring (as FABulous's fixed pips), the configuration
latches' index-to-frame map, the IO pad as pass-through, and that a consistent assignment exists.

---

## 4. North Star 4: All 8 Flagship Userspace Applications (`apps/`)

| # | Application Directory & Lean Module | Full-Stack Architecture & Qualification Criteria |
| :--- | :--- | :--- |
| **1** | **`apps/obend-risc/`**<br>(`lean/Obend/Apps/ObendRisc.lean`) | **3-Layer Open-Recursive Sequential RISC Softcore CPU**:<br>• `BaseRiscCore.obend` $\gg$ `PrivilegeCsrOverride.obend` $\gg$ `CustomSimdZkExt.obend`.<br>• **In-core instruction bit-slice decoding** (`opcode`, `rd`, `funct3`, `rs1`, `rs2`, sign-extended `imm`) using `.obend` bitwise/shift ops (`&`, `|`, `^`, `<<`, `>>`, `>>>`, `slt`).<br>• **True `always_ff` architectural registers** (`pc`, `mstatus`, `mepc`, `mcause`, `x1..x15`) + `imem`/`dmem` bus outputs.<br>• Proves `risc_base_opcode_non_interference` in Lean; the emitted `.sv` is checked against `obendRiscCpuRtlModule` by the LEC (`hardware/lec/lec.sh`); boots `firmware/test_prog.hex` (Fibonacci + CSR trap/mret + SIMD/ZK MAC) in `Verilator` with `.vcd` waveform. |
| **2** | **`apps/foc-hil/`**<br>(`lean/Obend/Apps/FocHil.lean`) | **Closed-Loop 20 kHz Field-Oriented Motor Drive + 6-Level SiC FCML Inverter HIL**:<br>• Multi-argument struct-packed stateful `always_ff` `.obend` controller (`ClarkePark.obend` $\to$ `PiCurrentLoop.obend` with `int_d`/`int_q` accumulators $\to$ `SosCbfThermalBarrier.obend` + FCML Lyapunov capacitor balancer).<br>• **Compile-time `AutoCert` synthesis** of `by judge("sos-lyapunov-cbf@1")`, `by judge("taylor-model@1")`, and `by judge("interval@1")`.<br>• Closed-loop 20 kHz `Verilator` co-simulation against 500,000-step ($\Delta t = 100\text{ ns}$) continuous-time RK4 `LC Drives` IPM + `MS350` SiC plant, including **live mid-run ICAP DPR layer hot-swap** and over-temperature 1-cycle trip. |
| **3** | **`apps/sdr-ft8/`**<br>(`lean/Obend/Apps/SdrFt8.lean`) | **All-Digital 40m Tayloe IQ SDR & 4-Stage CORDIC FT8 Demodulator**:<br>• Signed fixed-point (`Q16.16`/`Q32.32`) stateful `always_ff` `.obend` receiver chain (`QuadratureNcoMixer.obend` $\to$ `CicDecimator.obend` with 3-stage $z^{-1}$ integrator/comb registers $\to$ `PolyphaseFirImageReject.obend` $\to$ `CordicFt8ToneExtractor.obend` with $\Delta\phi[n] = \phi[n] - \phi[n-1]$ state).<br>• Processes 16,384-sample IQ stream in `Verilator`, suppressing a $+40\text{ dB}$ lower-sideband image interferer by $\ge 60\text{ dB}$ IRR and recovering 79/79 FT8 symbols. |
| **4** | **`apps/zk-ntt/`**<br>(`lean/Obend/Apps/ZkNtt.lean`) | **Goldilocks ($p = 2^{64} - 2^{32} + 1$) 256-Point NTT & 8-Round Sumcheck Co-Processor (RTL + AMD `VOP64`)**:<br>• 128-to-64-bit Goldilocks reduction ($2^{64} \equiv 2^{32}-1 \pmod p$) using `.obend` shifts/masks, Cooley–Tukey radix-2 butterfly, and stateful `always_ff` Sumcheck round polynomial accumulators.<br>• Optimized via `EqSatHypergraph` ($\ge 30\%$ multiplier cost reduction), compiled to **both** 4-stage `resetFree` pipelined SystemVerilog (`Verilator`) **and** 64-bit AMD `VOP64` assembly (`SelfAccelerate.compileRtlExprToAmdGpu`), verified bit-exact on 256-point $\text{INTT}(\text{NTT}(x)) = x$ and 8-round Sumcheck. |
| **5** | **`apps/silicon-kernel-verilator/`**<br>(`lean/Obend/Apps/SiliconKernelVerilator.lean`) | **Verilated 4-Zone Silicon Elaborator & Live ICAP DPR Hot-Swap Showcase**:<br>• Streams compiled `.obend` and Lean `OBCAMv1` declaration bundles over 128/512-bit AXI4-Stream into `silicon_elab_top.sv` in `Verilator`.<br>• Performs a **live mid-stream 3-phase glitch-free ICAP eFPGA bitstream hot-swap** of Zone 3 (`admitSimpTheoremDpr`), demonstrates 1-cycle `moved_pin_blocks` fallback to Zone 1 WHNF on pin mutation, and verifies hardware refusal flags on `#tooth`-mutated proofs. |
| **6** | **`apps/fidget-cam/`**<br>(`lean/Obend/Apps/FidgetCam.lean`) | **Parametric `.obend` OpenUSD/F-Rep CAD $\to$ Pruned SSA Tape $\to$ Verilated Voxelizer, `.stl` Mesh & 5-Axis G-Code**:<br>• Authors a hierarchical OpenUSD/F-Rep mechanical part in `.obend` (with `LIVERPS` overrides for cooling channels and mounting bosses).<br>• Lowers to a linear SSA F-Rep tape (`GeometryCAM.lean`), runs interval pruning + backward-liveness compaction (`prune_and_compact_ssa_tape_sound`), compiles the pruned tape to SystemVerilog (`Verilator`), evaluates the 3D affine-arithmetic octree on the Verilated hardware pipeline, and writes out a real binary `.stl` 3D mesh file + gouge-verified 5-axis G-code toolpath. |
| **7** | **`apps/sovereign-drex/`**<br>(`lean/Obend/Apps/SovereignDrex.lean`) | **Live `DReX` + `K-CARRY` Hot-Upgradable Sovereign Exchange on a 4-Validator `obend-node` Cluster**:<br>• Multi-file `.obend` package (`Seat.obend`, `OrderBook.obend`, `BatchClearing.obend`) running on a 4-validator `obend-node` cluster coupled to `crates/obend-fpga-hal`.<br>• Submits live order batches, executes a mid-flight schema/law hot-upgrade via `K-CARRY` (`"world-carry@1"` in `Carry.lean`), kills and recovers a validator from its WAL (`DurableSimplexHost`), and verifies conservation of supply and zero double-execution. |
| **8** | **`apps/quantum-photonic-matter/`**<br>(`lean/Obend/Apps/QuantumPhotonicMatter.lean`) | **Planar Clements Photonic CTQW, Majorana Tetron Lindblad Co-Processor & 1-WL `catgrad` Quotient Hypergraph Accelerator**:<br>• Multi-layer `.obend` (`stdlib/physical/QuantumPhotonicMatter.obend`: `PlanarWaveguideMeshBase` $\gg$ `KrawtchoukFaddeevCompensatedOverride` and `TetronParitySectorBase` $\gg$ `LindbladCooledTetronOverride`).<br>• Runs 1-WL color refinement (`wlStabilize`) and `quotientOpenHypergraph` to compress an $N$-lane symmetric `StrictOpenHypergraph` + its `compileGraphAdjoint` reverse-AD pass down to an $r$-lane quotient (`quotientOpenHypergraph_intertwines_eval_and_adjoint`), guarded by `quotientHypergraphSlot` (`moved_pin_blocks` 1-cycle fallback on symmetry-breaking weight overrides).<br>• Synthesizes Lagrange–Sylvester spectral projectors (`computeLagrangeProjector`), verifies discrete-time Szegedy walk lumping (`cellUniformSzegedyPST_iff_quotient`), Faddeev–LeVerrier thermal crosstalk cancellation, Ivanov Majorana braiding ($T_{a,b} = 1 + \gamma_a\gamma_b$), and Lindblad parity cooling in `Verilator` and 64-bit AMD `VOP64`. |
