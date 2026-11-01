# Report — Hardware Lane (`Obend.Hardware`): Synchronous HDL, Whole-Book Compiler, Technology Mapping, FABulous eFPGA & FabuBlox Nanofabrication

## 1. Architecture & First-Class Library Modules (`lean/Obend/Hardware/`)

The `Obend.Hardware` library connects Objective Bend's demand machine (`Obend.Equiv.Demand`),
quantity & reuse discipline (`Obend.Core.Ty`), leaf object books (`Obend.Leaf.Emit`), specialization
slots (`Obend.Slot` / `Obend.Leaf.Specialize`), capability laws (`Obend.Vault.Law`), and streaming
ledger (`Obend.Ledger`) to a verified synchronous Hardware Description Language, technology mapper,
FABulous eFPGA bitstream fabric, and FabuBlox (`fabublox.com`) cleanroom nanofabrication engine:

1. **[`Obend.Hardware.HDL`](file:///Users/ember/dev/obend/lean/Obend/Hardware/HDL.lean)** —
   * **Core Synchronous HDL (`RtlAluOp`, `RtlExpr`, `WireAssign`, `RegSpec`, `RtlModule`)**:
     64-bit combinational expressions and sequential registers with explicit clock domains
     (`ClkDomain.coreClk`, `.axiIoClk`, `.cfgJtagClk`) and reset discipline
     (`ResetKind.resetFree` vs `ResetKind.syncReset initVal`).
   * **Topological Combinational DAG Verifier (`checkExprDAG`, `checkWireTableDAG`)**:
     Statically rules out combinational loops and proves `evalRtlExpr_dag_locality` (wire `i`
     depends only on wires `< i`, guaranteeing single-pass deterministic evaluation).
   * **Static Clock-Domain Crossing (CDC) Verifier (`checkRegCdc`, `checkModuleCdc`)**:
     Proves `cdcSafe_no_unsynchronized_crossing`: no register in `dstReg.domain` may read a
     register from `srcDom ≠ dstReg.domain` unless `dstReg.isSynchronizer = true` and `nextExpr` is
     a direct `.regRead` with no intermediate combinational logic.
   * **AST-Driven SystemVerilog-2012 Emitter (`emitModuleSV`)**:
     Directly pretty-prints any verified `RtlModule` AST into synthesizable SystemVerilog-2012,
     separating reset-free datapath registers from synchronous-reset control registers.

2. **[`Obend.Hardware.Compiler`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Compiler.lean)** —
   * **Hardware Input-Port Substitution (`substInputPort0`, `substInputPort0_sound`)**:
     Specializes compiled slot bodies at call sites `self.m(arg)` with universal soundness proof.
   * **General `Term` → `RtlExpr` Compiler (`compileTerm`, `compileTerm_sound`)**:
     Compiles `.nat`, `.boolean`, `.bound`, `.get (.bound selfDepth) member`,
     `.app (.lam subBody) arg` (flattened `super`/`let` β-redexes),
     `.app (.get (.bound selfDepth) member) arg` (method calls through `self`),
     `.binary` (`add`, `multiply`, `subtract`, `equal`, `conjunction`, `less`, `lessEqual`),
     `.ifBool`, and `.ifZero` (with de Bruijn environment shifting `predExpr :: varEnv`).
     Proves universal structural soundness `compileTerm_sound` by recursion over `t : Term`.
   * **Whole-Book Compiler (`compileBookToRtl`)**:
     Compiles an `Obend.Leaf.Book` (such as `emit (comp 1)` from `ReviewMember.obend`) directly
     into a DAG- and CDC-verified `RtlModule`.

3. **[`Obend.Hardware.Synth`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Synth.lean)** —
   * **Verified `LUT2`/`LUT3` & `CARRY8` Technology Mapping**:
     Proves `lut2_or_sound` (`0xE`), `lut3_mux_sound` (`0xCA`), `evalLut3MuxBits_sound`, and
     two's-complement subtractor mapping `carrySubBel_eq_fullSubStageSpec` (`a + !b + cin`).
   * **Verified Pipeline Retiming (`stepRetime2`, `retime2Stage_sound`, `retiming_closes_16nm_500MHz`)**:
     Splits a deep combinational tree `f (g x) (h y)` across a register cutset, proving 2-cycle
     latency-shifted equivalence from any initial `X` state and closing 500 MHz (`2000 ps`) timing
     on 16nm FinFET SS (`2718 ps` un-retimed → `1084 ps` retimed).

4. **[`Obend.Hardware.FabuBlox`](file:///Users/ember/dev/obend/lean/Obend/Hardware/FabuBlox.lean)** —
   * **FabuBlox (`fabublox.com`) Cleanroom Process Intelligence & 2D Cutline Layer-Stack Emulator**:
     Models multi-material wafer cross-sections (`CutlineColumn`, `WaferState`) along a GDS layout
     cutline under sequential cleanroom fabrication steps (`lithoWindow`, `anisotropicRieOxide`,
     `stripPhotoresist`, `depositMetal`, `cmpMetal`, `feolThermalAnneal`).
   * **`Facility OS` Cleanroom Contamination, Thermal & Etch-Stop Rules (`checkFacilityStep`)**:
     - `facilityCheck_prevents_scorched_resist`: prevents steps `> 150°C` while photoresist is present;
     - `facilityCheck_prevents_feol_contamination`: prevents wafers with exposed `Cu` or `Au` from
       entering `.feolFurnace` or `.aldChamber`;
     - `rie_masked_column_invariant` & `rie_selective_via_landing_sound`: proves anisotropic RIE
       preserves masked dielectric columns while clearing unmasked contact windows and preserving
       the underlying $\text{TiN}$ barrier layer under finite selectivity;
     - `fabublox_damascene_flow_verified` & `extractCornerFromWafer_closes_500MHz`: verifies a
       6-step CMOS contact-via + copper damascene flow and extracts PDK timing parameters that
       close 500 MHz static timing signoff.

5. **[`Obend.Hardware.Silicon`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Silicon.lean)** —
   * 1-hot hardware wave refinement of `Obend.Equiv.Demand` (`waveHw_divergent_fires`),
   * Linear/affine wire fanout and `.cap bankId` SRAM access tokens (`quantityDuplicated_refused`),
   * Reset-free 2-stage Laguna crossing (`pipe2_x_free`), 4-stage `DSP48E2` MAC (`dspMac_latency_4`),
     and `URAM288` with RAW collision bypass (`bypassRAM_exact_latest_write`),
   * 2-slot AXI4-Stream skid buffer (`skid2_conservation`, `skid2_preserve_under_stall`),
   * Inter-SLR die crossing & Manhattan wirelength bounds (`checkChannelHop`).

6. **[`Obend.Hardware.Process`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Process.lean)** —
   * `LUT2`/`LUT6` + `CARRY8` full-adder BEL equivalence (`carryBel_eq_fullAdderSpec`),
   * FABulous eFPGA BLE tile bitstream synthesis (`efpga_bitstream_fullAdder_sound`),
   * Multi-corner PVT static timing signoff (`corner7nm_SS`, `corner16nm_SS`, `corner130nm_SS`,
     `timingSignoff_sound`, `obend_multi_process_timing_signoff`),
   * Cycle-accurate `Obend.Ledger` co-processor (`hwLedger_balanced_conserved`).

7. **[`Obend.Hardware.Fabric`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Fabric.lean)** —
   * $2\times 2$ FABulous eFPGA tile mesh & configuration frame loader (`frameLoader_immutable_when_locked`,
     `efpga_mesh_twiceReview_sound`),
   * Hardware Merkle-view receipt climber (`hwMerkle_climb_complete`),
   * `DeosCounter.obend` + `Obend.Vault.Law` register bank (`deosHw_writeOnce_immutable`),
   * 3-tier hardware specialization slot (`HwCandidate`: `.bitstream` → `.book` → `.machine`,
     `hwBitstream_usable_sound`, `hwMoved_pin_blocks_bitstream`).

## 2. Teeth, Refusal Poles & Mutation Verification ([`SiliconTeeth.lean`](file:///Users/ember/dev/obend/lean/Obend/Teeth/Hardware/SiliconTeeth.lean))

* **Refusal Poles**: `duplicated_affine_refused`, `sky130_overclock_500mhz_refused`,
  `unregistered_slr_crossing_refused`, `combinational_loop_refused`, `unsynchronized_cdc_refused`,
  `fabublox_under_and_over_etch_refused`.
* **End-to-End Book → RTL Compilation**: `review_book_compiled_rtl_verified` compiles the actual
  `emit (comp 1)` book of `ReviewMember.obend`, verifies `checkRtlModule = true`, and evaluates
  `out_review(3) = 5` and `out_twice(3) = 7`.
* **10 `#tooth` Kernel Mutation Checks**:
  1. `Obend.Hardware.Silicon.pipe2_x_free`
  2. `Obend.Hardware.Silicon.dspMac_latency_4`
  3. `Obend.Hardware.Silicon.bypassRAM_exact_latest_write`
  4. `Obend.Hardware.Process.carryBel_eq_fullAdderSpec`
  5. `Obend.Hardware.Fabric.deosHw_writeOnce_immutable`
  6. `Obend.Hardware.Fabric.hwBitstream_usable_sound`
  7. `Obend.Hardware.HDL.cdcSafe_no_unsynchronized_crossing`
  8. `Obend.Hardware.Compiler.compilePrim_sound`
  9. `Obend.Hardware.Synth.lut3_mux_sound`
  10. `Obend.Hardware.FabuBlox.facilityCheck_prevents_feol_contamination`
