# Expert read: FPGA / silicon (`fpga-silicon`), 2026-11-03

Reader profile: shipped UltraScale+ designs and AWS F1/F2 custom logic, iCE40 with the open
toolchain, one open-PDK tapeout. Scope: `lean/Obend/Hardware/`, `lean/Obend/Lower/SiliconElabFabric.lean`,
`apps/*/verilator/`, `hardware/`, `crates/obend-fpga-hal`, `SILICON-ELABORATOR.md`,
`QUALIFICATION-AND-SILICON-LEAN.md` §2-3, README "Hardware" row. Working tree as of today, not HEAD.

Tags: **READ** = I opened the file, `path:line`. **INFERRED** = deduced from READ facts (or from
domain knowledge, marked as such). **PROPOSED** = a recommendation. Numbers carry the command.

I ran no Lean or Rust build. I ran the built CLI (`lean/.lake/build/bin/obend`, dated Nov 1 16:31)
and one `verilator --lint-only` on `hardware/aws-f2/cl_obend_shell_bridge.sv`.

---

## 1. Verdict

The hardware tier has one honest kernel and a thick shell of claims that do not attach to it.

**READ.** The honest kernel is `lean/Obend/Hardware/HDL.lean` (677 lines): a 64-bit word-level RTL AST
(`RtlExpr`, `RegSpec`, `RtlModule`), a topological DAG checker with a real locality theorem
(`evalRtlExpr_dag_locality`, HDL.lean:109-132), a cycle semantics (`stepModuleRegs`, 345-359) and a
small emitter (`emitModuleSV`, 406-449) whose output parses under `verilator -Wall`. `obend verilate`
(`VerilateRunner.lean:2039-2096`) drives that emitted SV through Verilator against Lean's own
`runModuleTrace` — the right architecture for an emitter-correctness check.

**READ / INFERRED.** Everything that an FPGA person would ask to see next is missing or counterfeit:

- Three of the eight flagship `.sv` files are hand-written and labelled "Emitted & Verified" (§3.1).
- None of the eight `*_lec.smt2` "LEC" files is derived from the RTL or from the `RtlModule`; they are
  hand-typed third models, and the in-tree generator compares a word-level AST with a renaming of
  itself (§3.2).
- There are three different `silicon_elab_top` designs with incompatible port lists; the documented
  one is not the simulated one, and the simulated one is not the one the AWS bridge instantiates (§3.3).
- The "88-bit CAM", "2x2 XY credit-flow NoC" and "3-phase ICAP DPR" are, in the RTL, a 256-entry
  register file, a counter incremented by 2 or 4, and a mux between two 64-bit registers. No
  `ICAPE3`, no DFX pblock, no partial bitstream exists anywhere (§3.4).
- `RtlExpr` is 64-bit everywhere, there is one clock in every emitted module, and the CDC checker
  proves a property about clock domains that the emitted RTL does not have (§3.5, §3.6).
- The AWS F2 shell bridge uses a port list the F2 shell does not expose and a Tcl flow that cannot
  produce an AFI (§3.7).
- The "Rung 1 Verilator SHM daemon" in `crates/obend-fpga-hal` is Rust code computing the expected
  outputs; no Verilated model is linked (§3.8).
- The tapeout/PDK "signoff" receipts are written from constants and then checked (§3.9).

This extends the council's §1-2 pattern (theorem-shaped tests, two of everything, checkers without a
bridge, documents describing a system that does not exist) into the hardware tier with one new
species: **artifacts labelled as generated that were typed by hand**, which is worse than a missing
theorem because a reader cannot tell from the file.

---

## 2. Suspicions in the first ten minutes, and what happened to each

| # | Suspicion | What would clear it | Found? | Verdict |
|---|---|---|---|---|
| 1 | `RtlExpr` has no widths | a `width` field or `BitVec w` | No: `const (val : BitVec 64)`, all ports `logic [63:0]` (HDL.lean:64-72, 408-415) | **Confirmed** §3.5 |
| 2 | Checked-in `.sv` are hand-written | file text reproducible from `emitModuleSV` | 4 of 8 apps yes by shape; 3 cannot be (signed 32-bit ports, `localparam`, functions); `silicon_elab_top` is Verilog-2001 by hand | **Confirmed for 4 files** §3.1 |
| 3 | `.smt2` "LEC" not generated from RTL | a generator reading the `.sv` or the `RtlModule`, and files that match it | Generator exists but compares AST to itself; all app files hand-written; the one auto-generated file next to an `.sv` is stale and disagrees with it | **Confirmed** §3.2 |
| 4 | Testbenches short / self-referential | cycle counts, golden source | 21+24 cycles (RISC), 16x4 cycles with inputs < 65536 (`verilate`), directed asserts (silicon kernel); foc-hil 500k cycles is real but DUT is hand RTL | **Mostly confirmed** §3.10 |
| 5 | One clock, CDC is decorative | multi-clock emission, `ASYNC_REG`, 2-FF | one `clk` emitted; checker accepts a single flop as "2-FF synchronizer"; no module in tree sets `isSynchronizer := true` | **Confirmed** §3.6 |
| 6 | ICAP DPR / NoC are data structures | a primitive, a DFX flow, a router with buffers | none; Lean side is `structure` with `isolated : Bool`; RTL side is a register mux | **Confirmed** §3.4 |
| 7 | "88-bit CAM" is a RAM | content-addressable match logic | `cam_mem[addr]` 256x88, 5 read ports; `hash_bucket` variant compares stale read data | **Confirmed** §3.4 |
| 8 | AWS F2 files cannot compile/link | `cl_ports.vh`, shell DCP link, DFX | lint passes; interface is not the F2 shell's; Tcl is out-of-context synth only | **Confirmed (interface), INFERRED (flow)** §3.7 |
| 9 | PDK signoff checks constants | a real deck, a layout, a tool run | 5-rule `FoundryDrcDeck`, hand-entered feature, receipts with literal `987654321` signatures | **Confirmed** §3.9 |
| 10 | fpga-hal "co-sim" is not Verilator | a linked Verilated model | `step_one_cycle` writes `700`, `250`, `in*5+250` from Rust | **Confirmed** §3.8 |

---

## 3. Findings, ranked by how much they would embarrass us

### 3.1 Hand-written SystemVerilog labelled as emitter output

**READ.** `emitModuleSV` (HDL.lean:406-449) can only produce: ports `input logic clk`, `input logic rst`,
every other port `logic [63:0] <name>`; wires `logic [63:0] w_<i>; // <name>`; one `always_comb`;
one reset-free `always_ff` and one sync-reset `always_ff`; constants as `64'd<n>`; no `localparam`,
no `function`, no `signed` declarations, no bit-selects, no widths other than 64.

**READ.** Files whose header claims emission but whose text the emitter cannot produce:

- `apps/foc-hil/verilator/foc_drive_top.sv:1-3` "Emitted & Verified SystemVerilog ... Corresponds to
  `Obend.Apps.FocHil.focHilSequentialRtlModule`". Lines 12-38: `input logic signed [31:0]`,
  `output logic fault_trip` (1 bit); 43-48 `localparam signed [63:0]`; 88-90 `/ 64'sd1000000`
  (three 64-bit signed dividers); 112-115 saturation. The Lean module it names
  (`lean/Obend/Apps/FocHil.lean:1406-1470`) has six 64-bit inputs `id_err_ma, iq_err_ma, cap_err_mv,
  winding_temp_c, dpr_isolate_en, dpr_high_bw_sel`, five wires, integrators `int_q + iq_err*65`,
  `fcml_cap_err := cap_err*800` — no division, no `/1000` scaling, no feed-forward, no gate counts.
  **INFERRED:** the SV and the Lean module are two different controllers; the `_sim_sound` theorem
  (FocHil.lean:1585-1604) simulates the Lean one.
- `apps/sdr-ft8/verilator/sdr_ft8_top.sv:1-3` same header; 24-44 `signed [31:0]`, `[2:0] ft8_tone_bin`;
  61-64 four `/ 64'sd500`; 151 `/ 64'sd600`. Lean `sdrFt8SequentialRtlModule` (SdrFt8.lean:1414) is a
  6-register toy. Also: the comment says "3-Stage Hogenauer CIC" (73) but there is one comb stage
  (`comb_diff = cic_int3 - cic_comb_d1`, 81) — a 3-integrator/1-comb structure is not a CIC.
- `apps/zk-ntt/verilator/zk_ntt_coproc.sv`: `localparam` (30), `function automatic` (33-98),
  1-bit `sc_clear/sc_enable` (11-12). The "4-stage pipelined Goldilocks butterfly" (116-140) computes
  `u + v*w` and `u - v*w` **mod 2^64** (`s1_vw <= v_in * w_in`, 120), not mod P; only the
  combinational path (102-106) uses `gl_mul`. The testbench's 2048-butterfly NTT is driven through
  the combinational port with the NTT loop structure in C++ (`zk_ntt_tb.cpp:114-160`).
- `apps/silicon-kernel-verilator/verilator/silicon_elab_top.sv`: Verilog-2001 `reg`/`wire`/`always @(*)`
  (66), `localparam` (53); no Lean emitter in the tree produces this dialect.

**READ.** Files that are consistent with `emitModuleSV` output (shape: all-64-bit `w_<i>` wires, two
`always_ff` blocks): `apps/obend-risc/verilator/obend_risc_cpu.sv`, `apps/fidget-cam/verilator/
fidget_impeller_voxel_cam.sv` (header line 1 says so), `apps/sovereign-drex/verilator/
sovereign_drex_batch_top.sv`, `apps/quantum-photonic-matter/verilator/quantum_photonic_coproc_top.sv`,
and `hardware/sim/{cleanroom_tcad_stack,lc_drives_userspace_stator,cnc_5axis_userspace_mill,
obend_retimed_mac2}.sv`.

**READ.** Nothing in the tree ties a checked-in `.sv` to the emitter output: no `include_str`, no
`IO.FS.readFile` of a `.sv`, no `git diff --exit-code` in any `verify_*.sh`
(`grep -rn "include_str\|readFile.*\.sv" lean crates` → nothing relevant; the scripts only run
`verilator` and `z3`). The built CLI does not have the emission subcommands at all:
`strings lean/.lake/build/bin/obend | grep -x "verilate\|emit-lec-smt2"` → nothing; `obend hardware
emit-sv` prints the generic usage. `Obend/Hardware/Cli.lean:476-497` dispatches them in the working
tree, so the binary predates them.

**INFERRED.** A reader who opens `foc_drive_top.sv` and trusts line 1 believes a verified compiler
produced a 32-bit signed FOC controller with anti-windup and feed-forward. It did not; the compiler
cannot express a 32-bit signal.

### 3.2 "LEC" is not logic equivalence checking

**READ.** All eight `apps/*/verilator/*_lec.smt2` are hand-authored: narrative headers ("Flagship App
#1", `risc_lec.smt2:1-2`), hand-chosen free variables (`rs1_val`, `rs2_val` instead of the register
file, `risc_lec.smt2:12-13`), hand-transcribed "RTL" (`rtl_imm_b`, 44-55). The obligations are
properties of that third model (decoder slice vs shift/mask, trap preemption, non-interference), not
equivalence of the `.sv` or the `RtlModule` with anything. `foc_drive_lec.smt2:23-57` encodes
`int_q + iq_err*65` and no `/1000` — it matches the Lean toy, not the SV; its "Synthesized RTL
Gate-Level Netlist Model" (58-100) is the same arithmetic with muxes rewritten as `bvand (bvneg ...)`.
`verify_risc.sh:28-34` and friends gate PASS on `z3 ... == unsat` of these files.

**READ.** The generator that exists, `emitModuleLecSmt2` (VerilateRunner.lean:668-703), compares the
`RtlModule` against `synthesizeModuleToBels` of the same `RtlModule`. Every "BEL" is a 64-bit word
operation: `emitBelCellSmt2` (606-666) renders `lut2 0x8` as `(bvand in0 in1)` on `(_ BitVec 64)`,
`carry4` as `(bvadd xor (bvshl (bvand a b) 1))`, `dspMul` as 64x64 `bvmul`. `Synth.lean:149-162`
defines `BelKind.lut2 (initMask : Nat)` with no bit width; `countFfBels` (307) counts a 64-bit
register as one FF. Z3 `unsat` here says the Lean-side renaming is consistent; it says nothing about
any netlist, and it never reads a `.sv`. QUALIFICATION §66 says "plus Yosys `write_smt2` when present";
`grep -rn yosys lean crates hardware apps` finds only prose.

**READ.** The one auto-generated miter checked in beside an `.sv` of the same module is stale and
disagrees with it: `hardware/sim/cleanroom_tcad_stack_lec.smt2` declares `reg_0..reg_4` and
`spec_next_reg_*` (6-10, 23-27) while the current generator emits `r_<i>` and `spec_reg_<name>`
(VerilateRunner.lean:672-682); its `spec_w_2 = in_0*5 + reg_1` (15) vs the `.sv`'s
`w_2 = arg*8 + 20 + 4` (`cleanroom_tcad_stack.sv:26`). Different circuit, same filename. The
`obend_retimed_mac2` pair does match (both current).

### 3.3 Three `silicon_elab_top`s; the documented one is not the tested one

**READ.** Counts of distinctive identifiers (command:
`for pat in s_axis_tvalid rst_n ap_start hw_ctx_stack level_mem dma_we; do grep -c "$pat" <file>; done`):

| text | `s_axis_tvalid` | `rst_n` | `ap_start` | `hw_ctx_stack` | `level_mem` | `dma_we` | lines |
|---|---|---|---|---|---|---|---|
| (a) `apps/silicon-kernel-verilator/verilator/silicon_elab_top.sv` | 4 | 14 | 0 | 0 | 0 | 0 | 792 |
| (b) `hardware/sim/silicon_elab_top.sv` = `VerilateRunner.emitSiliconElabFabricTopSV` (1036-1826) | 0 | 0 | 6 | 5 | 5 | 18 | 1052 |
| (c) `Obend.Lower.SiliconElabFabric.emitSiliconElabFabricSV` (2383-3166) | 0 | 15 | 0 | 7 | 8 | 12 | n/a, never written to disk |

`diff (a) (b) | wc -l` → 1833. (a) has `rst_n` + 128-bit AXI4-Stream + `cmd_*` ports (593-645);
(b) has `rst`, `ap_start`, `dma_we`, `fuel_budget` (909-947); (c) has `rst_n` + `dma_we` + a binder
context stack and level memory that neither checked-in file has.

**READ.** QUALIFICATION §2.2 (lines 18-23) describes (c): "`hw_work_stack[0:255]`, de Bruijn binder
context stack (`hw_ctx_stack[0:255]`), universe level evaluator (`level_mem[0:1023]`)". The AWS bridge
instantiates (b) (`cl_obend_shell_bridge.sv:30,164-202`). The Verilator harness with the asserts tests
(a) (`verilator/Makefile:3`, `sim_main.cpp`). `verify_silicon_kernel.sh:13-16` lints (b), then
`make run` builds (a).

**READ.** The Lean "co-simulation theorem" `silicon_kernel_verilator_cosim_sound`
(`Apps/SiliconKernelVerilator.lean:296-317`) is `decide +kernel` over `runVerilatorCoSimModel`
(225-285), a Lean function whose `cycles := 46`, `camHits := 18`, `nocFlits := 6`, `lutHits := 2` are
record literals (275-281) and whose `vcdPath := "silicon_elab_wave.vcd"` is a string. It reads no
simulator output and no `.sv`. The `#tooth` (329) mutates a second record literal
(`runVerilatorCoSimModelAcceptMutant`, 310-324). This is the council's "theorem-shaped test" with a
Verilator costume.

### 3.4 The CAM, the NoC and the ICAP DPR

**READ, (a).** "88-bit synchronous BRAM/URAM CAM": `reg [87:0] cam_mem [0:255]` addressed by an
8-bit handle, five synchronous read ports (`silicon_elab_top.sv:50, 106-110`). There is no
content-match logic; handles are assigned by the host (`sim_main.cpp:268-293`). Five read ports plus
one write port on a 256x88 array will not infer BRAM/URAM (2 ports each); Vivado will build it as
replicated LUTRAM or flops. `cam_valid_q[rd_addr]` (51, 106-110) is a 256-bit vector dynamically
indexed five times.

**READ, (b).** `hash_bucket = child0[9:0] ^ child1[9:0] ^ {2'b0, opcode}` (hw/sim:310),
`u_cam_uram` with `.raddr(hash_bucket)` and `.we(alloc_req && !cam_hit_out)` (312-321),
`cam_hit_out = (rdata_word == wdata_word) && rdata_word != 0` (338). `rdata_word` is the output of a
3-register read pipeline (hw/sim:70-105), so the hit compares the *current* input word with data read
2-3 cycles ago at the bucket of *that* cycle's inputs; a hit can only register if the same word is
presented on consecutive cycles. Collisions evict silently. The testbench only asserts
`perf_cam_allocs != 0` (`hardware/sim/sim_main.cpp:126-128`).

**READ.** "2x2 2D XY credit-flow NoC unifier" (a:199-253): one FSM, two 88-bit compares,
`perf_noc_flits <= perf_noc_flits + 2` or `+ 4` (231, 242, 246). No link, no router instance, no
credit. The HDL-side `obend_macro_noc_router_xy` (HDL.lean:624-644) is a combinational direction
decoder with no buffer; the hw/sim version (155-205) adds a 4-bit credit counter initialised to 4 with
`downstream_credit_in` defaulting to `1'b1` (164). Neither is instantiated by (a) or (b)'s zones.

**READ.** "3-phase glitch-free ICAP DPR" (a:259-358): two 64-bit registers `active_gain`,
`active_offset` swapped behind `isolated_fence ? skid_held_output : gain*x+offset` (291-297, 314-340);
the "digest" is `(gain << 12) + offset` (291). The macro `obend_macro_icap_dpr_tile`
(HDL.lean:564-620; hw/sim:207-265) XORs a 64-bit mask; its "CRC" is FNV-1a
(`* 64'h0000_0100_0000_01B3`, HDL.lean:604). `grep -rn "ICAPE3\|ICAP_E3\|csib\|rdwrb" hardware apps
lean/Obend/Hardware` → nothing. `synth_cl_obend.tcl` has no `HD.RECONFIGURABLE`, no partial pblock,
no decoupler, no `write_bitstream -cell`. **INFERRED (domain):** there is no partial reconfiguration
here in any sense a Xilinx tool would recognise; what exists is a shadow-register update with an
output hold, which is a fine thing but is called by the wrong name in roughly forty places.

**READ.** The Lean side agrees with the RTL about what this is: `ReconfigTileState`
(ReductionMachine.lean:218-226) is `{ activeTile : AutomatonTile, isolated : Bool, skidHeldOutput :
BitVec 64, ... }`; `verifyIcapFrameDigest` (321-326) recomputes `computeTilePayloadDigest frame.newTile`
from the payload it is verifying, where the digest (299-309) is `(y1 - y0) <<< 12 + y0` for the tile
evaluated at 0 and 1 — a digest of a linear function's two coefficients. `NocTileState`
(1332-1341) is `inbox : List NocFlit`, `outbox : List NocFlit`, `credits : Nat`, `rules : List
AutomatonTile`; `stepNocRouter` (1358-1394) rotates a list. These are simulation data structures;
nothing maps them to the emitted SV, and the emitted SV does not implement them.

**INFERRED (domain), resources on `xcvu47p`.** (a)'s `hw_work_stack [0:255]` (36-bit) and
`hw_val_stack [0:255]` (64-bit) are written at up to three indices in one cycle
(`top_idx`, `work_sp`, `work_sp+1`, 494-496) and read asynchronously (404, 514-517): ~25.6K flip-flops
plus 256:1 read muxes, not BRAM. The five-port `cam_mem` is ~5x replicated 256x88 LUTRAM. Zone 4's
"typechecker" is a fixed table over six type codes (`1, 2, 3, 5, 17, 34`, lines 485-487, 514-518,
540-546). None of this is near a vu47p's limits (2.6M LUT / 5.2M FF / 960 URAM); the point is that
"URAM CAM" and "NoC" are not what would be built. The only URAM-shaped module,
`obend_macro_uram288_bypass`, is 4096x64 in HDL.lean:489-499 and 1024x88 in hw/sim:47-60 (default
`ADDR_BITS = 10`); a URAM288 is 4096x72, so the second is a BRAM-sized array, and neither carries
`(* ram_style = "ultra" *)`.

### 3.5 No widths

**READ.** `RtlExpr.const (val : BitVec 64)`; `evalRtlExpr : ... → BitVec 64` (HDL.lean:64-89). No
slice, concat, zero/sign-extend, no memory, no enable. Every port and register is emitted as
`logic [63:0]` (408-415). `obend_risc_cpu.sv:9` has `output logic [63:0] dmem_we`. Register file
`x1..x15` is 15 named 64-bit regs with a 15-deep ternary chain for each read port
(`obend_risc_cpu.sv:88-89`) and a 64x64 `*` in the single-cycle ALU path (96). **INFERRED (domain):**
synthesisable, but Vivado will give ~16 DSP48E2 in cascade plus a long carry/mux path per `*`; one-bit
control registers cost 64 FDREs unless `opt_design` can prove the upper bits constant (it can for
`eq`-derived flags, not for counters). As a "verified HDL" fragment this is coherent; as "RV64I/M
softcore" and "FOC controller" it is the wrong tool, which is presumably why those files were
written by hand (§3.1).

### 3.6 Clock domains exist only inside the checker

**READ.** `ClkDomain` has `coreClk | axiIoClk | cfgJtagClk` (HDL.lean:165-169). `emitModuleSV` emits
exactly one `clk` (410) and puts every register in `always_ff @(posedge clk)` regardless of
`r.domain` (429, 439). `stepModuleRegs` (345-359) steps all registers on one edge. So
`checkModuleCdc` (264-267) is a property of a design the emitter never produces: a module with
registers in two domains emits as a single-clock module, and would be wrong if a top level ever
drove two clocks into it. `checkRegCdc` (251-260) accepts a destination register as a "2-FF
synchronizer" if it is flagged `isSynchronizer` and its `nextExpr` is a bare `.regRead` — that is one
flop, not two, and no `ASYNC_REG` attribute is emitted. In the tree, no `RegSpec` sets
`isSynchronizer := true` (`grep -rn "isSynchronizer := true" lean` → none); the only uses of a
second domain are a tooth (`Teeth/Hardware/SiliconTeeth.lean:122-126`) and a test
(`tests/m5/Milestone5Challenger1StressTest.lean:370`). Reset: sync only (`ResetKind`, 172-175),
raw `rst` sampled, no reset synchroniser; acceptable for FPGA.

### 3.7 The AWS F2 shell bridge

**READ.** `hardware/aws-f2/cl_obend_shell_bridge.sv:32-67` declares `clk_main_a0`, `rst_main_n`,
`sh_ocl_*`/`ocl_sh_*` AXI-Lite, and `sh_pcis_h2c_tvalid/tdata[511:0]/tkeep/tlast` plus
`pcis_sh_c2h_*` as an AXI4-Stream. `crates/obend-fpga-hal/src/aws_f2_backend.rs:33-35, 64-66` opens
`/dev/fpga0` with `mmap` and `/dev/xdma0_{h2c,c2h}_0` as the stream.

**INFERRED (domain).** The F1/F2 shell's CL interface is fixed by `cl_ports.vh`: OCL is AXI-Lite with
these names (correct here); PCIS is a 512-bit **AXI4 memory-mapped** slave (`sh_cl_dma_pcis_awaddr`,
`...wdata`, `...rready`), fed by the shell's XDMA engine; there is no `sh_pcis_*_tvalid` stream port.
BAR0 is reached through `fpga_pci_attach`/`fpga_pci_peek`/`poke` (fpga-libs), not an `mmap` of a
character device. `synth_cl_obend.tcl` runs `synth_design -mode out_of_context` on the CL alone and
`write_checkpoint`; an AFI needs the shell-linked flow (`aws_build_dcp_from_cl.py` →
`create_dcp_from_cl.tcl`, `cl_ports.vh` include, `CL_` top, `encrypt.tcl`, manifest). So "compile" in
the narrow sense: `verilator --lint-only -Wall -Wno-DECLFILENAME --top-module cl_obend_shell_bridge
hardware/aws-f2/cl_obend_shell_bridge.sv` → 0 warnings (I ran it). In the sense that matters, it
cannot be built into an F2 image without rewriting the interface.

**READ, protocol.** AXI-Lite read channel: `ocl_sh_arready = 1` always (268); `rvalid` set on every
`arvalid` and `rdata` overwritten while `rvalid && !rready` (439-487) — violates AXI stability. Reset
mixing: cores get `rst = !rst_main_n || ctrl_soft_rst` (75) while the CSR block resets on
`!rst_main_n` only (277). `s_axis_tready = 1'b1` always in (a) (646) and `h2c_skid_ready = 1'b1`
after the skid (220) — no backpressure anywhere, so the 512-bit skid buffer is decorative.

### 3.8 The "Rung 1 Verilator SHM daemon" is Rust computing the answers

**READ.** `crates/obend-fpga-hal/src/sim_backend.rs:242-330` (`step_one_cycle`): writes `oxide = 700`,
`vth = 250`, `idrain = in*5 + 250`, `stator ... 395`, `mill ... 10000 + in*4` into the shared-memory
"BAR0"; emulates the CAM with a Rust `HashMap` (`cam_uram`) and `last_write_bucket`. No Verilated
model is linked: `verilator_daemon_bridge.hpp` is referenced by no build
(`grep -rn verilator_daemon_bridge --include=*.rs --include=*.cpp --include=*.toml --include=Makefile .`
→ only the header itself and a doc comment); `obend-silicon-sim` (`src/bin`) uses `SimBackend`.
QUALIFICATION §3.1:49 calls this "4 MiB POSIX shared memory ... driving Verilated `silicon_elab_top.sv`
at ≥ 1 M cycles/s". The `cargo test -p obend-fpga-hal` that `verify_silicon_kernel.sh:24` falls back
to is Rust testing Rust. The AWS "mock" (`aws_f2_backend.rs:93-144`) is three files and a thread
that sets `AP_DONE`.

### 3.9 PDK / tapeout signoff checks constants it wrote

**READ.** `Obend/Hardware/Cli.lean` `cmdTapeout` (working-tree lines ~455-470) writes a
`waferspace-signoff@1` receipt with literal `dieWidthUm 2920`, `numVddPads 4`, `numSignalPads 24`,
`schematicSig 987654321`, `layoutSig 987654321`, `densityPermille 450` for any input design.
`cmdWaferSpaceSignoff` (Cli.lean:117-146) builds the certificate from `--mode golden|bad_antenna|bad_cmp`
with literal areas and counts, then verifies it. `TapeoutPipeline.compileCompositionToSiliconTapeout`
(TapeoutPipeline.lean:393-480) checks `cfg.drcDeck`, `cfg.cutlineFeature`, `cfg.metalBoxA/B`,
`cfg.viaBox`, `cfg.waferSpaceCert`, `cfg.fabSteps` — configuration defaults
(`goldenGf180SignoffCert`, lines 110, 126) with no dependence on the `RtlModule`;
`derivedWaferSpaceCert := bindWaferSpaceCertToBelNetlist cfg.waferSpaceCert belNetlist` (416) sets
both LVS signatures from the same BEL hash (WaferSpace.lean:306-312, 263-283), so LVS passes by
construction. `FoundryDrcDeck` (DRC.lean:189-196) is five scalars; `checkCutlineDRC` (215-221) is six
inequalities on one hand-entered `CutlineDrcFeature`. There is no GDS, no layout, no polygon, no deck
file. `emitLibreLaneGf180Json` (WaferSpace.lean:377) writes a config for a flow nothing invokes
(`IO.Process` appears only in `VerilateRunner.lean`, for `verilator` and `z3`). **INFERRED:** the
theorems in DRC/WaferSpace/FabuBlox are true statements about their own records; "GF180MCU signoff"
is not something this code can assert about any design.

### 3.10 What the Verilator testbenches compare, and for how long

**READ.**

| app | DUT origin | cycles | golden |
|---|---|---|---|
| obend-risc | emitted | 2+21 and 2+24 (`risc_soc_tb.cpp:78-129, 214-222`) | hand-expected register values |
| zk-ntt | hand | ~2100 single-cycle butterflies + 67-cycle stream + 8 rounds | `__uint128_t` reference; NTT loop in C++; pipeline path is mod 2^64 (§3.1) |
| foc-hil | hand | 500,000 (`foc_hil_tb.cpp:33, 81`) | RK4 PMSM plant, tolerance checks — the one real closed-loop test |
| sdr-ft8 | hand | 16,384 samples | synthesized IQ stream |
| quantum-photonic | emitted | 16 iterations (`quantum_photonic_tb.cpp:115`) | literal constants in `printf` |
| sovereign-drex | emitted | ~45 ticks | literal asserts |
| fidget-cam | emitted | octree sweep, thousands of ticks | C++ reference; STL/G-code emitted |
| silicon-kernel (a) | hand | ~100 | directed `assert`s with literal handles (`sim_main.cpp:299-497`) |
| `hardware/sim/tb_top` | emitted + (b) | ~20 (`sim_main.cpp`) | literal constants |
| `obend verilate` | emitted | `numVectors 16 x numCycles 4` (VerilateRunner.lean:98-99); inputs: `8,6,4,200` then LCG `% 65536` (329-337, the docstring says "SplitMix64") | Lean `runModuleTrace` of the same `RtlModule` (361-401) — the right golden |

`Verilated::randReset(2)` is set in every harness (good). `VerilateReport.bitMismatches := 0,
traceAgreed := true` are literals on the success path (VerilateRunner.lean:2085-2086), though
`"mismatches=0"` is substring-checked on stdout (2071). No `verify_*.sh` is invoked from lake,
cargo, or CI (`grep -rln verify_risc ... --include=*.yml --include=*.toml --include=*.lean .` → only
the scripts; no `.github/workflows`). Simulation binaries and VCDs in `apps/*/verilator` post-date
their `.sv` (Nov 2 21:13-23:37 vs 16:51-18:10), so the apps were run after the last edit; they are
untracked (`git ls-files apps | grep -c obj_dir` → 0).

### 3.11 Smaller things a reviewer would still write down

- **READ.** Two `obend_macro_dsp48e2`s: HDL.lean:453-480 is 27x18 with `c1→c2→c3` (a DSP48E2 has one C
  register); hw/sim:9-45 is 64x64 with `ce`. Same module name, different hardware.
- **READ.** `emitExprSV` for `qmul32` (HDL.lean:398) uses `>>>` on a signed 128-bit product while
  `evalAluOp` (61) uses logical `>>>` on `BitVec 128`; they agree because bits [95:32] are kept
  either way — fine, but worth a comment, since this is exactly where emitter/semantics drift hides.
- **READ.** `obend_macro_uram288_bypass` (HDL.lean:500-516) forwards the same write/read pair at two
  stages (503-504); harmless, not "pipelined RAW forwarding".
- **READ.** SV-2012 default port values (`input logic dma_we = 1'b0`, hw/sim:278, 917-934) — legal,
  Verilator-friendly, uncommon in Vivado flows.
- **READ.** `Judge.hwSynthFormat` / `hw-rtl-synth@1` (Judge.lean:87, 771): the certificate is the
  `RtlModule` and the verdict is `checkRtlModule`. A receipt that the DAG checker ran; it says nothing
  about synthesis.
- **READ.** `retiming_closes_16nm_500MHz` (Synth.lean:141-144) and `PlaceRoute.validAdderPnrCert`
  (267-285): `decide` on hand-entered `TimingPath`/`PnrCertificate` records (`logicLevels := 8` vs `3`,
  two placed cells). The Leiserson–Saxe checker (`Retiming.lean:120-152, 238-246`) is a genuine
  certificate checker; its inputs here are never extracted from a design.
- **READ.** `cleanroom_tcad_stack.sv` is called "5-stage pipelined RTL" (`tb_top.sv:5`); its outputs are
  driven from the combinational wires (29-33) and the five registers are written but never read
  (36-42) — Vivado will delete them.

---

## 4. What is sound and worth keeping

- **READ.** `HDL.lean`: `checkWireTableDAG` + `evalRtlExpr_dag_locality` (93-160) really do exclude
  combinational loops in this fragment; `stepModuleRegs` evaluates next-state against the old state
  (nonblocking semantics); `emitModuleSV` is faithful to it as far as I can see, and its output lints
  clean under `-Wall` in four apps.
- **READ.** `obend verilate` (VerilateRunner.lean:2039-2096): Lean model → emitted SV → Verilator →
  compare with Lean trace, `randReset(2)`, `--x-assign unique --x-initial unique` (2063). Thin
  (64 cycles, 16-bit inputs) but the right shape; this is the thing to grow.
- **READ.** `hardware/sim/obend_retimed_mac2.sv` and its miter are both current generator output and
  agree.
- **READ.** `Retiming.lean` theorems (`path_weight_telescopes`, `cycle_weight_invariant`,
  `solveVerifiedRetiming_sound`) are real statements about retiming lags.
- **READ.** `foc_hil_tb.cpp` is a real 50 ms closed-loop HIL harness with a plant model; the DUT it
  tests is hand RTL, but the harness is the kind of thing an FPGA team actually writes.
- **READ.** `Silicon.lean` §2 (`pipe2_x_free`, `stepSkid_queue_conserved`, `bypassRAM_exact_latest_write`)
  states the X-propagation and skid-buffer properties correctly at the model level.

---

## 5. Three changes, in order

1. **One emitter, one artifact, one gate (PROPOSED).** Every `apps/*/verilator/*.sv` and `*_lec.smt2`
   is produced by `obend hardware emit-sv` / `emit-lec-smt2` inside its `verify_*.sh`, followed by
   `git diff --exit-code` on the file; the four hand-written SV files are either regenerated from an
   `RtlModule` that can express them (which needs change 2) or moved to `reference/` and relabelled
   "hand-written reference RTL, not emitter output" with their Lean twins renamed to say they are toys.
   Make LEC mean LEC: `yosys -p "read_verilog -sv X.sv; prep -top X; write_smt2 X.yosys.smt2"` and a
   miter between that and the Lean-emitted spec (`emitExprSmt2` already exists). Cost: ~2 days plus a
   Yosys dependency; the hard part is deleting the four files' headers.
2. **Widths and clocks in `RtlExpr` (PROPOSED).** Add `width : Nat` to ports/wires/regs with
   `slice`/`concat`/`zext`/`sext` constructors and a width-check pass; emit `logic [w-1:0]`; emit one
   `clk_<domain>` per `ClkDomain` present and `(* ASYNC_REG = "TRUE" *)` on synchronizer pairs, and
   require two flops. Cost: `Compiler.lean` (3,120 lines) and `Lower/Proofs/Hardware.lean` are proved
   over `BitVec 64`; a parametric `BitVec w` is multi-week. The cheap first step is a
   `trunc (w : Nat)` node whose semantics is `setWidth` and whose emission is `logic [w-1:0]` at ports
   only; that alone removes `output logic [63:0] dmem_we`.
3. **One `silicon_elab_top`, one simulator backend (PROPOSED).** Check in the text of
   `SiliconElabFabric.emitSiliconElabFabricSV` as the only `silicon_elab_top.sv`, delete (a) and the
   VerilateRunner copy (b), and make `sim_main.cpp` read its golden from a serialized
   `runVerilatorCoSimModel` rather than asserting literals; rename `SimBackend` to `MockBackend` and
   either link a Verilated model through `verilator_daemon_bridge.hpp` or stop calling it Rung 1.
   Leave the F2 bridge alone until someone has an F2 instance; until then label it "untested sketch,
   not `cl_ports.vh`-compatible" in `QUALIFICATION-AND-SILICON-LEAN.md` §3.1. Cost: 1-2 days.

---

## 6. The one question for Ember

Is the hardware tier meant to put a bitstream on an F2 (or an iCE40) in the next few months, or is
it meant to be a verified *model* of hardware that stays in Lean? If the former, the critical path is
widths, a real shell interface, and a DFX flow, and the PDK/tapeout layer should be frozen as
documentation; if the latter, the `.sv` files, Verilator claims, F2 bridge and `obend-fpga-hal`
should come out of the claims and the HDL can stay 64-bit. Right now the repository claims both, and
the evidence supports neither.

---

## Appendix: commands used

```
# emitter call sites / sv headers
grep -rn "emitModuleSV\|emitHierarchicalSV" --include='*.lean' --include='*.rs' --include='*.sh' lean crates apps hardware
for f in apps/*/verilator/*.sv hardware/sim/*.sv hardware/aws-f2/*.sv; do head -12 "$f"; done
# built binary lacks hardware subcommands
strings lean/.lake/build/bin/obend | grep -x "verilate\|emit-lec-smt2\|hw-rtl-synth\|hardware"
lean/.lake/build/bin/obend hardware emit-sv   # prints generic usage
# three silicon_elab_top texts
diff apps/silicon-kernel-verilator/verilator/silicon_elab_top.sv hardware/sim/silicon_elab_top.sv | wc -l   # 1833
for pat in s_axis_tvalid rst_n ap_start hw_ctx_stack level_mem dma_we; do grep -c "$pat" <each file / Lean range>; done
# no ICAP primitive, no yosys
grep -rn "ICAPE3\|ICAP_E3\|csib\|rdwrb" hardware apps lean/Obend/Hardware
grep -rn -i yosys lean crates hardware apps
# clock domains / synchronizers
grep -rn "axiIoClk\|cfgJtagClk" --include='*.lean' lean | grep -v HDL.lean
grep -rn "isSynchronizer := true" --include='*.lean' lean
# fpga-hal daemon header unused
grep -rn verilator_daemon_bridge --include='*.rs' --include='*.cpp' --include='*.toml' --include=Makefile .
# the one lint allowed
cd hardware/aws-f2 && verilator --lint-only -Wall -Wno-DECLFILENAME --top-module cl_obend_shell_bridge cl_obend_shell_bridge.sv
# artifacts untracked, timestamps
git ls-files apps hardware | grep -c obj_dir ; ls -la apps/*/verilator apps/*/verilator/obj_dir
```
