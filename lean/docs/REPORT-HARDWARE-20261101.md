# Report — Hardware Lane (`Obend.Hardware`): Synchronous & Guarded-Action HDL, Whole-Book Compiler, Technology Mapping, FABulous eFPGA, FabuBlox Nanofabrication & `wafer.space` Mixed-Signal ASIC Signoff

## 1. Architecture & First-Class Library Modules (`lean/Obend/Hardware/` — 16 Modules)

The `Obend.Hardware` library connects Objective Bend's demand machine (`Obend.Equiv.Demand`),
quantity & reuse discipline (`Obend.Core.Ty`), leaf object books (`Obend.Leaf.Emit`), specialization
slots (`Obend.Slot` / `Obend.Leaf.Specialize`), capability laws (`Obend.Vault.Law`), streaming
ledger (`Obend.Ledger`), and receipt judge (`Obend.Judge` / `Obend.Receipt`) to a verified
hardware description language, whole-book compiler, technology mapper, FABulous eFPGA bitstream
fabric, FabuBlox (`fabublox.com`) cleanroom nanofabrication engine, Analog/Mixed-Signal (AMS)
verifier, and `wafer.space` (`wafer.space`) MPW ASIC signoff suite:

1. **[`Obend.Hardware.HDL`](file:///Users/ember/dev/obend/lean/Obend/Hardware/HDL.lean)** —
   * **Core Synchronous HDL (`RtlAluOp`, `RtlExpr`, `WireAssign`, `RegSpec`, `RtlModule`)**:
     64-bit combinational expressions and sequential registers with explicit clock domains
     (`ClkDomain.coreClk`, `.axiIoClk`, `.cfgJtagClk`) and reset discipline
     (`ResetKind.resetFree` vs `ResetKind.syncReset initVal`).
   * **Topological Combinational DAG Verifier (`checkExprDAG`, `checkWireTableDAG`)**:
     Statically rules out combinational loops and proves `evalRtlExpr_dag_locality`.
   * **Static Clock-Domain Crossing (CDC) Verifier (`checkRegCdc`, `checkModuleCdc`)**:
     Proves `cdcSafe_no_unsynchronized_crossing`.
   * **AST-Driven SystemVerilog-2012 Emitter (`emitModuleSV`)**:
     Directly pretty-prints any verified `RtlModule` AST into synthesizable SystemVerilog-2012.

2. **[`Obend.Hardware.Types`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Types.lean)** —
   * **Hardware Bit-Level Type Algebra (`HwType`)**:
     Arbitrary-width `.bits w`, packed records `.struct fields`, tagged sums `.taggedUnion tagWidth variants`,
     and fixed-length `.array len elem`.
   * **Bit-Slice Lens Algebra & Packing Isomorphism**:
     Proves `extractSlice_UpdateSlice_same` (get-put), `extractSlice_updateSlice_disjoint`
     (non-interference across disjoint record fields), `packFields_unpackFields_roundtrip`, and
     `compileConstructor_extractTag`.

3. **[`Obend.Hardware.Rules`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Rules.lean)** —
   * **Kôika / Kami / Bluespec Guarded Atomic Actions (`HwAction`, `HwRule`, `RuleScheduler`)**:
     Dynamic action logs (`ActionLog`: `regsRead`, `regsWritten`, `sramReadPorts`, `sramWritePorts`),
     write-before-read (`W < R`) and double-write (`W ⋈ W`) conflict detection (`logsConflict`),
     and static conflict-matrix checker (`checkConflictFreePair`).
   * **One-Rule-At-A-Time (ORAAT) Refinement (`compileScheduleToCycle`, `oraat_two_rule_refinement`)**:
     Proves that every concurrent multi-rule schedule execution refines to sequential atomic
     application of the non-aborted rules in priority order.

4. **[`Obend.Hardware.FSM`](file:///Users/ember/dev/obend/lean/Obend/Hardware/FSM.lean)** —
   * **Multi-Cycle Valid/Ready FSMs & Fuel-Bounded `fix` Loops (`FsmController`, `FixLoopHw`)**:
     Synthesizes bounded `fix` recurrences (`stepFixLoopHw`) with `fixLoopHw_unroll_sound` and
     `fixLoopHw_busy_rejects_req` (no request overwrite while busy).
   * **Algebraic Effect Handshakes (`PerformHandshakeHw`)**:
     Compiles `perform`/`resume` into a pause-and-resume bus protocol (`performHandshake_resume_exact`,
     `performHandshake_paused_holds_arg`).

5. **[`Obend.Hardware.Compiler`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Compiler.lean)** —
   * **Total Structural `Term` → `RtlExpr` Compiler (`compileTerm`, `compileTerm_sound`)**:
     Compiles `.nat`, `.boolean`, `.bound`, `.get`, `.app (.lam ..)` (let/super β-redexes),
     `.app (.get (.bound selfDepth) member) arg` (inlined slot calls via `substInputPort0_sound`),
     `.binary` (`add`, `multiply`, `subtract`, `equal`, `conjunction`, `less`, `lessEqual`),
     `.ifBool`, `.ifZero`, `.construct` / `.match` (packed tagged unions), `.letRec` (bounded
     hardware unrolling), and `.perform` (host bus channel read).
   * **Whole-Book Compiler (`compileBookToRtl`)**:
     Compiles an `Obend.Leaf.Book` (including `ReviewMember.obend` and `TwiceReview.obend`) directly
     into a DAG- and CDC-verified `RtlModule`.

6. **[`Obend.Hardware.Synth`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Synth.lean)** —
   * **Verified `LUT2`/`LUT3` & `CARRY8` Technology Mapping**:
     Proves `lut2_or_sound`, `lut3_mux_sound`, `evalLut3MuxBits_sound`, and `carrySubBel_eq_fullSubStageSpec`.
   * **2-Stage Cutset Pipeline Retiming (`stepRetime2`, `retime2Stage_sound`, `retiming_closes_16nm_500MHz`)**.

7. **[`Obend.Hardware.Retiming`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Retiming.lean)** —
   * **Leiserson–Saxe Synchronous Graph Retiming (`RetimeGraph`, `RetimeCert`)**:
     Verifies integer vertex lag assignments $r : V \to \mathbb{Z}$, proving non-negative edge
     register counts (`checkEdgeNonNeg_sound`), cycle register weight invariance (`retimeCycleWeight_invariant`:
     $\sum_{e \in C} w_r(e) = \sum_{e \in C} w(e)$ via telescoping cancellation), and 3-node MAC
     retiming from `2718 ps` down to `1359 ps` (`macRetime_closes_500MHz`).

8. **[`Obend.Hardware.PlaceRoute`](file:///Users/ember/dev/obend/lean/Obend/Hardware/PlaceRoute.lean)** —
   * **Untrusted Place-and-Route (PnR) & Bitstream Certificate Checker (`DeviceGrid`, `PnRCertificate`, `checkPnRCertificate`)**:
     Certifying verifier for external placement & routing (Nextpnr / VPR / Vivado): placement site
     injectivity (`placementInjective_no_overlap`), PIP routing tree vertex disjointness
     (`pipDisjoint_no_short`), Elmore RC wire-delay slack (`elmoreDelay_monotone`), and FABulous
     bitstream frame decoder round-trip (`decodeEncode_bitstream_roundtrip`).

9. **[`Obend.Hardware.FabuBlox`](file:///Users/ember/dev/obend/lean/Obend/Hardware/FabuBlox.lean)** —
   * **FabuBlox (`fabublox.com`) Cleanroom Process Intelligence & 2D Cutline `StackSimulator`**:
     Models multi-material wafer cross-sections (`CutlineColumn`, `WaferState`) across `lithoWindow`,
     `anisotropicRieOxide`, `stripPhotoresist`, `depositMetal`, `cmpMetal`, and `feolThermalAnneal`.
   * **`Facility OS` Safety Laws**:
     `facilityCheck_prevents_scorched_resist`, `facilityCheck_prevents_feol_contamination`,
     `rie_masked_column_invariant`, `rie_selective_via_landing_sound`, and `fabublox_damascene_flow_verified`.

10. **[`Obend.Hardware.DRC`](file:///Users/ember/dev/obend/lean/Obend/Hardware/DRC.lean)** —
    * **4-Zone Cleanroom Contamination Lattice (`ContamZone`: `.feolClean`, `.beolPreMetal`, `.beolCu`, `.backsideGold`)**:
      Monotone contamination state transition checker (`zoneOrder_transitive`, `stepContamZone_monotone`)
      andRCA/piranha strip decontamination rules.
    * **Trench Aspect-Ratio Step-Coverage & Keyhole Void Detector (`checkStepCoverageNoKeyhole`)**:
      Proves `ald_high_aspect_trench_void_free` vs `pvd_high_aspect_trench_keyhole_detected`.
    * **Lithography Overlay + Etch Undercut Enclosure & Cutline $RC$ Extraction (`checkViaLandingEnclosure`, `extractCutlineParasitics`)**.

11. **[`Obend.Hardware.Analog`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Analog.lean)** —
    * **Kirchhoff Bilateral Electrical Networks (`BilateralBranch`, `AnalogNetlist`)**:
      Proves `branch_kcl_conserved` ($I_{a\to b} + I_{b\to a} = 0$) and charge conservation across
      switch-capacitor networks.
    * **4-Terminal Analog Primitives & `ABBA` Common-Centroid Matching (`evalCommonCentroidDiff`)**:
      Proves `commonCentroid_ABBA_cancels_linear_gradient` (exact first-order process gradient
      cancellation $\Delta P(x) = P_0 + g_x \cdot x$) vs `unmatched_AABB_suffers_gradient_mismatch`.
    * **Multi-Voltage UPF Power Domains (`gf180_5v0`, `gf180_3v3`, `sky130_1v8`)**:
      Proves `domainCrossing_requires_levelShifter` and gate-oxide breakdown refusal (`checkOxideSafe`).
    * **Mixed-Signal 4-Bit SAR ADC + Capacitive DAC Convergence (`runSarAdc4`, `sarAdc4_exact_convergence`, `sarAdc4_no_overshoot`)**:
      Proves that 4 successive-approximation trials recover $\lfloor V_{\text{in}} / V_{\text{LSB}} \rfloor \in [0, 15]$
      for every analog input $V_{\text{in}} \in [0, 16 \cdot V_{\text{LSB}})$, plus `.spice` & `SV-RNM` emitters.

12. **[`Obend.Hardware.WaferSpace`](file:///Users/ember/dev/obend/lean/Obend/Hardware/WaferSpace.lean)** —
    * **`wafer.space` Open-Silicon MPW Shuttle Signoff (`gf180mcuD`, `sky130A`, `ihpSg13g2`)**:
      Verifies padring & double-diode ESD continuity (`padringCheck_guarantees_esd_protection`),
      plasma-etch antenna ratios & tie-down diode discharge (`antennaDiode_relaxes_ratio`,
      `excessive_antenna_without_diode_refused`), CMP metal density window $[30\%, 70\%]$,
      Layout-Versus-Schematic (LVS) isomorphism (`lvsIso_preserves_incidence`), and OpenLane /
      LibreLane configuration emission (`emitLibreLaneConfigJson`).

13. **[`Obend.Hardware.Judge`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Judge.lean)** & **[`Obend.Hardware.Cli`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Cli.lean)** —
    * **5 Kernel-Verified `Obend.Judge.Format` Certificates**:
      `hw-rtl-synth@1`, `hw-retime-sta@1`, `hw-pnr-bitstream@1`, `fabublox-run@1`, and `waferspace-signoff@1`,
      each with proven `Sound` and `Complete` theorems and wired into `obend hardware ...`,
      `obend fabublox check ...`, and `obend verify RECEIPT.json`.

14. **[`Obend.Hardware.Silicon`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Silicon.lean)**, **[`Obend.Hardware.Process`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Process.lean)**, **[`Obend.Hardware.Fabric`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Fabric.lean)** —
    * 1-hot demand wave chip, `DSP48E2` 4-stage MAC, `URAM288` with RAW bypass, 2-slot AXI4-Stream skid
      buffer, `LUT2`/`CARRY8` BELs, FABulous $2\times 2$ eFPGA mesh, Merkle-view receipt climber,
      `DeosCounter.obend` + `Vault.Law` register bank, and 3-tier hardware specialization slot.

## 2. Teeth, Refusal Poles & Mutation Verification ([`SiliconTeeth.lean`](file:///Users/ember/dev/obend/lean/Obend/Teeth/Hardware/SiliconTeeth.lean))

* **20 `#tooth` Kernel Mutation Checks**:
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
  11. `Obend.Hardware.Types.extractSlice_updateSlice_disjoint`
  12. `Obend.Hardware.Rules.oraat_two_rule_refinement`
  13. `Obend.Hardware.FSM.performHandshake_resume_exact`
  14. `Obend.Hardware.Retiming.checkEdgeNonNeg_sound`
  15. `Obend.Hardware.PlaceRoute.decodeEncode_bitstream_roundtrip`
  16. `Obend.Hardware.DRC.stepContamZone_monotone`
  17. `Obend.Hardware.Analog.commonCentroid_ABBA_cancels_linear_gradient`
  18. `Obend.Hardware.Analog.sarAdc4_no_overshoot`
  19. `Obend.Hardware.WaferSpace.padringCheck_guarantees_esd_protection`
  20. `Obend.Hardware.Judge.waferspaceSignoffFormat_sound`

## 3. End-to-End Verification Summary

* **Lean 4 Kernel Census (`Obend.Census`)**: `47,950` package constants, `0 sorryAx`, `0` declared axioms.
* **Hardware Co-Simulation & CLI Suite (`python3 lean/tests/run-hardware.py`)**: `20/20` passed (4 Z3 SMT-LIB2 bit-precise & mixed-signal equivalence suites, Verilator 5.050 15-module `-Wall` X-randomized elaboration, 10 cycle-accurate C++ hardware simulation suites, and 4 `obend` CLI receipt generation + `obend verify` + negative refusal checks).
