# Report — Hardware Lane (`Obend.Hardware`): Synchronous & Guarded-Action HDL, Whole-Book Compiler, Technology Mapping, FABulous eFPGA, FabuBlox Nanofabrication, `wafer.space` Mixed-Signal ASIC Signoff, Electro-Thermal Multiphysics, Automated Datasheet Calibration & Ham Radio RF Transceiver

## 1. Architecture & First-Class Library Modules (`lean/Obend/Hardware/` — 20 Modules)

The `Obend.Hardware` library connects Objective Bend's demand machine (`Obend.Equiv.Demand`),
quantity & reuse discipline (`Obend.Core.Ty`), leaf object books (`Obend.Leaf.Emit`), specialization
slots (`Obend.Slot` / `Obend.Leaf.Specialize`), capability laws (`Obend.Vault.Law`), streaming
ledger (`Obend.Ledger`), and receipt judge (`Obend.Judge` / `Obend.Receipt`) to a 20-module verified
hardware description language, whole-book compiler, technology mapper, FABulous eFPGA bitstream
fabric, FabuBlox (`fabublox.com`) cleanroom nanofabrication engine, Analog/Mixed-Signal (AMS)
verifier, `wafer.space` (`wafer.space`) MPW ASIC signoff suite, coupled electro-thermal multiphysics
engine, automated datasheet capture & calibration verifier, classic TTL / op-amp / sensor / power
circuitry, and amateur radio RF transceiver chain:

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
     Proves `extractSlice_updateSlice_same`, `extractSlice_updateSlice_disjoint`,
     `packFields_unpackFields_roundtrip`, and `compileConstructor_extractTag`.

3. **[`Obend.Hardware.Rules`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Rules.lean)** —
   * **Kôika / Kami / Bluespec Guarded Atomic Actions (`HwAction`, `HwRule`, `RuleScheduler`)**:
     Dynamic action logs (`ActionLog`), write-before-read (`W < R`) and double-write (`W ⋈ W`)
     conflict detection (`logsConflict`), static conflict-matrix checker (`checkConflictFreePair`),
     and One-Rule-At-A-Time (ORAAT) refinement (`oraat_two_rule_refinement`).

4. **[`Obend.Hardware.FSM`](file:///Users/ember/dev/obend/lean/Obend/Hardware/FSM.lean)** —
   * **Multi-Cycle Valid/Ready FSMs, Fuel-Bounded `fix` Loops & `perform`/`resume` Handshakes**:
     Proves `fixLoopHw_unroll_sound`, `fixLoopHw_busy_rejects_req`, and `performHandshake_resume_exact`.

5. **[`Obend.Hardware.Compiler`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Compiler.lean)** —
   * **Total Structural `Term` → `RtlExpr` Compiler (`compileTerm`, `compileTermSat`, `compileTerm_sound`)**:
     Compiles `.nat`, `.boolean`, `.bound`, `.get`, `.app (.lam ..)`, `.app (.get self m) arg`,
     `.binary`, `.ifBool`, `.ifZero`, `.construct` / `.match`, `.letRec`, and `.perform`, plus
     whole-Book synthesis (`compileBookToRtl`, `compileBookToRtlSat`).

6. **[`Obend.Hardware.Synth`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Synth.lean)** —
   * **Verified `LUT2`/`LUT3` & `CARRY8` Technology Mapping & 2-Stage Cutset Retiming**:
     Proves `lut2_or_sound`, `lut3_mux_sound`, `carrySubBel_eq_fullSubStageSpec`, and `retime2Stage_sound`.

7. **[`Obend.Hardware.Retiming`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Retiming.lean)** —
   * **Leiserson–Saxe Synchronous Graph Retiming (`RetimeGraph`, `RetimeCert`)**:
     Proves `checkEdgeNonNeg_sound`, `retimeCycleWeight_invariant`, and `macRetime_closes_500MHz`.

8. **[`Obend.Hardware.PlaceRoute`](file:///Users/ember/dev/obend/lean/Obend/Hardware/PlaceRoute.lean)** —
   * **Untrusted Place-and-Route (PnR) & Bitstream Certificate Checker (`DeviceGrid`, `PnRCertificate`)**:
     Proves `placementInjective_no_overlap`, `pipDisjoint_no_short`, `elmoreDelay_monotone`, and
     `decodeEncode_bitstream_roundtrip`.

9. **[`Obend.Hardware.FabuBlox`](file:///Users/ember/dev/obend/lean/Obend/Hardware/FabuBlox.lean)** —
   * **FabuBlox (`fabublox.com`) Cleanroom Process Intelligence & 2D Cutline `StackSimulator`**:
     Proves `facilityCheck_prevents_scorched_resist`, `facilityCheck_prevents_feol_contamination`,
     `rie_masked_column_invariant`, `rie_selective_via_landing_sound`, and `fabublox_damascene_flow_verified`.

10. **[`Obend.Hardware.DRC`](file:///Users/ember/dev/obend/lean/Obend/Hardware/DRC.lean)** —
    * **4-Zone Cleanroom Contamination Lattice, ALD vs PVD Keyhole Void Checker & Litho Enclosure**:
      Proves `stepContamZone_monotone`, `ald_high_aspect_trench_void_free`, and `pvd_high_aspect_trench_keyhole_detected`.

11. **[`Obend.Hardware.Analog`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Analog.lean)** —
    * **Kirchhoff Bilateral Networks, `ABBA` Common-Centroid Matching, Multi-Voltage UPF & 4-Bit SAR ADC**:
      Proves `switchedCap_charge_conserved`, `commonCentroid_cancels_linear_gradient`,
      `powerSafe_no_oxide_overvoltage`, and `sarAdc4_exact_convergence`.

12. **[`Obend.Hardware.WaferSpace`](file:///Users/ember/dev/obend/lean/Obend/Hardware/WaferSpace.lean)** —
    * **`wafer.space` Open-Silicon MPW Shuttle Signoff (`gf180mcuD`, `sky130A`, `ihpSg13g2`)**:
      Proves `padringCheck_guarantees_esd_protection`, `antennaSafe_no_gate_oxide_damage`,
      `cmpDensity_within_foundry_window`, and `lvsIso_preserves_incidence`.

13. **[`Obend.Hardware.Thermal`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Thermal.lean)** —
    * **Coupled Electro-Thermal Multiphysics (`ThermalRCStage`, `ThermalNode`, `ElectroThermalBjtSpec`, `TsdSpec`)**:
      - Cauer/Foster RC thermal network monotonicity (`steadyStateTemp_monotone_power`) and no-overshoot
        relaxation (`thermalRelaxation_bounded`),
      - BJT CTAT $V_{BE}(T)$ vs PTAT $\Delta V_{BE}(T)$ opposing slopes (`ctat_and_ptat_opposing_slopes`)
        and **Brokaw Bandgap Reference** exact zero-temperature-coefficient cancellation
        (`bandgap_zero_tempco_cancellation`),
      - Electro-thermal feedback loop gain $\gamma_{\text{th}}$ and emitter-ballast stabilization
        (`emitter_ballast_stabilizes_thermal_loop` vs `unballasted_bjt_thermal_runaway_detected`),
      - Hysteretic Thermal Shutdown (TSD) Schmitt protection (`tsd_cutoff_zeros_power_above_trip`,
        `tsd_hysteresis_deadband_preserves_state`).

14. **[`Obend.Hardware.Datasheet`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Datasheet.lean)** —
    * **Automated Datasheet Capture, Cross-Family Noise Margins & Model $L_\infty$ Calibration (`ComponentDatasheet`)**:
      - Captures `sn74ls00Datasheet` (5V Schottky TTL), `cd74hc00Datasheet` (5V CMOS), and `cd74hct00Datasheet`
        (5V TTL-compatible CMOS),
      - Proves `ttl_to_hc_direct_interface_refused` ($\text{NM}_H = -800\,\text{mV}$), `ttl_to_hct_interface_verified`,
        `pullup_restores_ttl_to_hc_margin`, and `checkLogicInterface_guarantees_valid_thresholds`,
      - Proves $L_\infty$ curve-fit swing preservation (`calibrated_model_preserves_voltage_swing`) and
        AC timing-diagram window verification (`timing_diagram_window_sound`).

15. **[`Obend.Hardware.Circuits`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Circuits.lean)** —
    * **Classic `SN74LS00` Totem-Pole TTL Gate, Pt100 RTD + 3-Op-Amp INA & Synchronous Buck Stage**:
      - Proves `ttl74ls00_nand_truth_and_swing_sound` and `fanout_overload_degrades_vol_refused`,
      - Proves 3-op-amp Instrumentation Amplifier 60 Hz common-mode hum cancellation
        (`ina_common_mode_cancelled_at_matched_bridge`) and negative-feedback loop-gain desensitization
        (`opamp_negative_feedback_stabilizes_gain`),
      - Proves Synchronous Buck steady-state volt-second balance (`buck_vout_bounded_by_vin`) and
        CCM inductor saturation safety (`buck_ccm_safe_prevents_core_saturation`).

16. **[`Obend.Hardware.RF`](file:///Users/ember/dev/obend/lean/Obend/Hardware/RF.lean)** —
    * **Ham Radio & RF Transceiver Chain (`Impedance`, `HamBand`, `LMatchNetwork`, `RfTransceiverSignoff`)**:
      - Transmission line reflection coefficient $|\Gamma|^2$, $\text{VSWR}$, **Maximum Power Transfer /
        Conjugate Match Theorem** (`conjugate_match_zero_reflection`, `conjugate_match_maximizes_power`),
        and verified L-network antenna tuner transformation (`l_match_40m_whip_to_50ohm_verified`),
      - **Tayloe Quadrature ($I/Q$) SDR Mixer** image-sideband cancellation (`tayloe_iq_cancels_image_sideband`),
      - **Cascaded Friis Noise Figure** (`lna_gain_reduces_cascaded_noise_figure`) and **Class-E HF PA +
        7-Element Chebyshev LPF** harmonic suppression ($\ge 43\,\text{dBc}$ for **FCC Part 97.307** compliance).

17. **[`Obend.Hardware.Judge`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Judge.lean)** & **[`Obend.Hardware.Cli`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Cli.lean)** —
    * **7 Kernel-Verified `Obend.Judge.Format` Certificates**:
      `hw-rtl-synth@1`, `hw-retime-sta@1`, `hw-pnr-bitstream@1`, `fabublox-run@1`, `waferspace-signoff@1`,
      `datasheet-fit@1`, and `rf-transceiver-signoff@1`.

18. **[`Obend.Hardware.Silicon`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Silicon.lean)**, **[`Obend.Hardware.Process`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Process.lean)**, **[`Obend.Hardware.Fabric`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Fabric.lean)** —
    * 1-hot demand wave chip, `DSP48E2` 4-stage MAC, `URAM288` with RAW bypass, 2-slot AXI4-Stream skid
      buffer, `LUT2`/`CARRY8` BELs, FABulous $2\times 2$ eFPGA mesh, Merkle-view receipt climber,
      `DeosCounter.obend` + `Vault.Law` register bank, and 3-tier hardware specialization slot.

## 2. Teeth, Refusal Poles & Mutation Verification ([`SiliconTeeth.lean`](file:///Users/ember/dev/obend/lean/Obend/Teeth/Hardware/SiliconTeeth.lean))

* **25 `#tooth` Kernel Mutation Checks**:
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
  11. `Obend.Hardware.Types.extractLo32_packPair32In64`
  12. `Obend.Hardware.Rules.oraat_two_rule_refinement`
  13. `Obend.Hardware.FSM.fixLoop_sound_at_budget`
  14. `Obend.Hardware.Retiming.retimeCycle_weight_invariant_3`
  15. `Obend.Hardware.PlaceRoute.fabulous_frame_roundtrip`
  16. `Obend.Hardware.DRC.pvd_high_aspect_trench_causes_keyhole`
  17. `Obend.Hardware.Analog.switchedCap_charge_conserved`
  18. `Obend.Hardware.Analog.commonCentroid_cancels_linear_gradient`
  19. `Obend.Hardware.WaferSpace.waferspace_gf180mcu_signoff_poles`
  20. `Obend.Hardware.Judge.badLoopRtlModule_refused`
  21. `Obend.Hardware.Thermal.bandgap_zero_tempco_cancellation`
  22. `Obend.Hardware.Datasheet.checkLogicInterface_guarantees_valid_thresholds`
  23. `Obend.Hardware.Circuits.ina_common_mode_cancelled_at_matched_bridge`
  24. `Obend.Hardware.RF.conjugate_match_zero_reflection`
  25. `Obend.Hardware.RF.tayloe_iq_cancels_image_sideband`

## 3. End-to-End Verification Summary

* **Lean 4 Kernel Census (`Obend.Census`)**: `49,429` package constants across `603` build jobs, `0 sorryAx`, `0` declared axioms.
* **Hardware, Multiphysics & RF Co-Simulation Suite (`python3 lean/tests/run-hardware.py`)**: `28/28` passed:
  - 5 Z3 SMT-LIB2 equivalence & nonlinear real physics (`QF_NRA`) suites (`lec_check.smt2`, `lec_fabric.smt2`, `lec_compiler_fabublox.smt2`, `lec_ams_waferspace.smt2`, `lec_multiphysics_rf.smt2`),
  - Verilator 5.050 15-module `-Wall` X-randomized elaboration + 10 C++ cycle-accurate digital/eFPGA simulation suites,
  - C++20 continuous-time multiphysics & RF simulator (`multiphysics_sim.cpp`: RK4 electro-thermal BJT + Schmitt TSD, `SN74LS00` totem-pole NAND datasheet curve calibration with $L_\infty = 14.2\,\text{mV} \le 25\,\text{mV}$, Pt100 RTD bridge + 3-op-amp INA with $100\,\text{dB}$ CMRR hum rejection, and 40m `7.074 MHz` FT8 ham radio transceiver with $\text{VSWR}=1.002$, Tayloe $\text{IRR}=52.4\,\text{dB}$, Friis $\text{NF}=1.84\,\text{dB}$, and $-58.6\,\text{dBc}$ Chebyshev LPF harmonic suppression),
  - 6 `obend hardware` / `obend fabublox` / `obend verify` CLI certificate & refusal checks (`hw-pnr-bitstream@1`, `hw-retime-sta@1`, `waferspace-signoff@1`, `fabublox-run@1`, `datasheet-fit@1`, `rf-transceiver-signoff@1`).
