# Report — Hardware Lane (`Obend.Hardware`): Synchronous & Guarded-Action HDL, Whole-Book & Sequential `Nat.rec` Compiler, Technology Mapping, FABulous eFPGA & Self-Reconfiguring Automaton, FabuBlox / Neofab Metrology, `wafer.space` ASIC Signoff, First-Principles Multiphysics & Silicon Photonics, High-Speed PCB Geometry, SDR DSP/Phased-Array RF & Smart-Contract Agentic EDA

## 1. Architecture & First-Class Library Modules (`lean/Obend/Hardware/` — 26 Modules)

The `Obend.Hardware` library connects Objective Bend's demand machine (`Obend.Equiv.Demand`),
quantity & reuse discipline (`Obend.Core.Ty`), leaf object books (`Obend.Leaf.Emit`), specialization
slots (`Obend.Slot` / `Obend.Leaf.Specialize`), Markdown Vaults & capability smart-contract laws
(`Obend.Vault.Page` / `Obend.Vault.Law`), streaming ledger (`Obend.Ledger`), and receipt judge
(`Obend.Judge` / `Obend.Receipt`) to a 26-module verified hardware, multiphysics, photonics, PCB,
RF/DSP, and agentic CAD/EDA suite:

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
   * **Total Structural `Term` → `RtlExpr` Compiler & Multi-Cycle `Nat.rec` FSM Synthesizer**:
     Compiles `.nat`, `.boolean`, `.bound`, `.get`, `.app (.lam ..)`, `.app (.get self m) arg`,
     `.binary`, `.ifBool`, `.ifZero`, `.construct` / `.match`, `.letRec`, and `.perform`, plus
     single-cycle whole-Book synthesis (`compileBookToRtl`, `compileBookToRtlSat`) and verified
     multi-cycle sequential `Nat.rec` loop synthesis (`compileBookToSeqRtlSat`, `evalSeqModuleAfterCycles`,
     `lean_sumTo_seq_rtl_verified`).

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
    * **Kirchhoff Bilateral Networks, 2D Oxide Curvature ($\nabla^2 P$), Prouhet-Thue-Morse (`ABBABAAB`) 2nd-Order Cancellation, Pelgrom Mismatch, UPF & 4-Bit SAR ADC**:
      Proves `switchedCap_charge_conserved`, `commonCentroid_cancels_linear_gradient`,
      `abba1D_quadratic_bow_residual` ($4 c_{xx} d^2$), `prouhetThueMorse_cancels_linear_and_quadratic_bow` ($= 0$),
      `crossCoupledQuad2D_cancels_gradients_and_axial_bow` ($4 c_{xy} d_x d_y$),
      `chiralityBalanced2D_cancels_full_hessian` ($= 0$), `pelgrom_variance_monotone_area`,
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

17. **[`Obend.Hardware.Physics`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Physics.lean)** —
    * **First-Principles Semiconductor PDD, Cauer PRIMA Model-Order Reduction & Open Neofab Metrology**:
      - Finite-volume Scharfetter-Gummel Poisson-Drift-Diffusion charge conservation (`pdd_discrete_flux_telescopes`, `pdd_total_charge_conserved`),
      - Fourier heat PDE to Cauer RC PRIMA congruence projection passivity preservation (`prima_congruence_preserves_passivity`, `mor_truncation_preserves_safety_margin`) for Lanyon AI multiphysics interoperability,
      - Open neofab (`Hacker Fab`, `Atomic Semi`, `FabuBlox`) Rayleigh lithography resolution (`rayleigh_cd_monotone_wavelength`), self-limiting ALD linearity (`ald_thickness_linear_and_conformal`), and 4-point-probe metrology (`metrology_sheet_resistance_scales_thickness`).

18. **[`Obend.Hardware.Photonics`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Photonics.lean)** —
    * **Open-Foundry Silicon Photonics (`SiEPIC 220nm SOI`, `IHP SG13G2 EPIC`, `400nm SiN`)**:
      - Waveguide effective/group index & thermo-optic phase shift (`thermoOptic_phase_monotone_temp`),
      - Coupled-Mode Theory $2 \times 2$ directional coupler optical power conservation (`directionalCoupler_conserves_optical_power`, `coupler_3db_equal_split`),
      - Balanced Mach-Zehnder Interferometer modulator extinction (`mzi_quadrature_and_null_extinction`) and Microring Resonator critical coupling (`mrr_critical_coupling_zero_through`, `photonicDrc_sound`).

19. **[`Obend.Hardware.PCB`](file:///Users/ember/dev/obend/lean/Obend/Hardware/PCB.lean)** —
    * **High-Speed PCB Stackups (`FR-4`, `Rogers RO4350B`), Differential Pairs, Serpentine Skew & IPC-2152**:
      - Edge-coupled differential pair odd-mode impedance monotonicity (`diffImpedance_monotone_uncoupled`, `diffImpedance_uncoupled_limit`),
      - Serpentine trombone length-matching flight-time skew elimination (`serpentine_eliminates_length_skew`),
      - IPC-2152 trace/via ampacity & parallel via inductance reduction (`viaArray_reduces_inductance_and_shares_current`, `pcbBoardSignoff_sound`).

20. **[`Obend.Hardware.ReductionMachine`](file:///Users/ember/dev/obend/lean/Obend/Hardware/ReductionMachine.lean)** —
    * **Distributed Slot-Reduction Automaton & Self-Reconfiguring eFPGA (`ICAP` Glitch-Free DPR)**:
      - Compiles `Obend.Leaf.Book` and `Obend.Lower.LExpr` to hardware `AutomatonTile`s (`automaton_simulates_book`),
      - 3-phase Glitch-Free Dynamic Partial Reconfiguration (`dpr_preserves_neighbor_tiles_and_packets`, `dpr_corrupt_crc_keeps_tile_isolated`, `dpr_specialized_tile_executes_new_book`).

21. **[`Obend.Hardware.DSP`](file:///Users/ember/dev/obend/lean/Obend/Hardware/DSP.lean)** —
    * **Synchronous CORDIC, Hogenauer CIC Decimator, Linear-Phase FIR, Phased-Array ULA & Rollett LNA Stability**:
      - CORDIC stage-0 norm scaling (`cordic_stage0_norm_scaling`) and NCO modular phase safety (`nco_phase_in_bounds`),
      - Hogenauer CIC overflow-free bit-growth (`cic_register_width_sound`) and symmetric FIR multiplier folding (`firSymmetric_folds_multipliers`),
      - Uniform Linear Array coherent $N^2$ main-lobe power gain (`phasedArray_coherent_gain_sq`), null steering (`phasedArray_null_steering`), and 2-port S-parameter Rollett unconditional stability $K > 1, |\Delta| < 1$ (`rollettStability_sound`).

22. **[`Obend.Hardware.AgenticEDA`](file:///Users/ember/dev/obend/lean/Obend/Hardware/AgenticEDA.lean)** —
    * **Smart-Contract Markdown Vaults (`Obend.Vault.Page` + `Obend.Vault.Law`) for Multi-Agent CAD/EDA**:
      - Parses Markdown Vault component/board frontmatter and `law:` smart contracts (`extractEdaVaultPart`, `parseVaultPageLaws`),
      - Verifies 2D PCB courtyard/pin-pitch drop-in replacement (`footprintDropIn_sound`) and content-addressed datasheet block-cite freshness (`staleDatasheetCite_refused`),
      - Judges multi-agent BOM/layout proposals via compiled `Core4` smart contracts (`Obend.Vault.judge`) + physical noise margins (`agenticEdaProposal_admits_sound`, `goldenAgenticBomSwap_admitted_and_overbudget_refused`).

23. **[`Obend.Hardware.Judge`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Judge.lean)** & **[`Obend.Hardware.Cli`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Cli.lean)** —
    * **10 Kernel-Verified `Obend.Judge.Format` Certificates**:
      `hw-rtl-synth@1`, `hw-retime-sta@1`, `hw-pnr-bitstream@1`, `fabublox-run@1`, `waferspace-signoff@1`,
      `datasheet-fit@1`, `rf-transceiver-signoff@1`, `photonics-pic-signoff@1`, `pcb-board-signoff@1`, and `agentic-eda-swap@1`.

24. **[`Obend.Hardware.Silicon`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Silicon.lean)**, **[`Obend.Hardware.Process`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Process.lean)**, **[`Obend.Hardware.Fabric`](file:///Users/ember/dev/obend/lean/Obend/Hardware/Fabric.lean)** —
    * 1-hot demand wave chip, `DSP48E2` 4-stage MAC, `URAM288` with RAW bypass, 2-slot AXI4-Stream skid
      buffer, `LUT2`/`CARRY8` BELs, FABulous $2\times 2$ eFPGA mesh, Merkle-view receipt climber,
      `DeosCounter.obend` + `Vault.Law` register bank, and 3-tier hardware specialization slot.

## 2. Teeth, Refusal Poles & Mutation Verification ([`SiliconTeeth.lean`](file:///Users/ember/dev/obend/lean/Obend/Teeth/Hardware/SiliconTeeth.lean))

* **32 `#tooth` Kernel Mutation Checks**:
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
  11. `Obend.Hardware.Types.struct_slice_extract_sound`
  12. `Obend.Hardware.Rules.write0_before_read0_refused`
  13. `Obend.Hardware.FSM.fsm_no_overwrite_while_busy`
  14. `Obend.Hardware.Retiming.leiserson_saxe_shift_sound`
  15. `Obend.Hardware.PlaceRoute.bitstream_decode_roundtrip_sound`
  16. `Obend.Hardware.DRC.pvd_high_ar_keyhole_refused`
  17. `Obend.Hardware.Analog.switchedCap_charge_conserved`
  18. `Obend.Hardware.Analog.commonCentroid_cancels_linear_gradient`
  19. `Obend.Hardware.WaferSpace.waferspace_gf180mcu_signoff_poles`
  20. `Obend.Hardware.Judge.badLoopRtlModule_refused`
  21. `Obend.Hardware.Thermal.bandgap_zero_tempco_cancellation`
  22. `Obend.Hardware.Datasheet.checkLogicInterface_guarantees_valid_thresholds`
  23. `Obend.Hardware.Circuits.ina_common_mode_cancelled_at_matched_bridge`
  24. `Obend.Hardware.RF.conjugate_match_zero_reflection`
  25. `Obend.Hardware.RF.tayloe_iq_cancels_image_sideband`
  26. `Obend.Hardware.Analog.prouhetThueMorse_cancels_linear_and_quadratic_bow`
  27. `Obend.Hardware.Physics.pdd_total_charge_conserved`
  28. `Obend.Hardware.Photonics.directionalCoupler_conserves_optical_power`
  29. `Obend.Hardware.PCB.diffImpedance_monotone_uncoupled`
  30. `Obend.Hardware.ReductionMachine.dpr_corrupt_crc_keeps_tile_isolated`
  31. `Obend.Hardware.DSP.rollettStability_sound`
  32. `Obend.Hardware.AgenticEDA.staleDatasheetCite_refused`

## 3. End-to-End Verification Summary

* **Lean 4 Kernel Census (`Obend.Census`)**: `52,368` package constants across `622` build jobs, `0 sorryAx`, `0` declared axioms.
* **Hardware, Multiphysics, Photonics, PCB, RF & Agentic EDA Co-Simulation Suite (`python3 lean/tests/run-hardware.py`)**: `32/32` passed:
  - 5 Z3 SMT-LIB2 equivalence & nonlinear real physics (`QF_NRA`) suites (`lec_check.smt2`, `lec_fabric.smt2`, `lec_compiler_fabublox.smt2`, `lec_ams_waferspace.smt2`, `lec_multiphysics_rf.smt2`),
  - Verilator 5.050 15-module `-Wall` X-randomized elaboration + 10 C++ cycle-accurate digital/eFPGA simulation suites,
  - C++20 continuous-time multiphysics & RF simulator (`multiphysics_sim.cpp`: RK4 electro-thermal BJT + Schmitt TSD, `SN74LS00` totem-pole NAND datasheet curve calibration with $L_\infty = 14.2\,\text{mV} \le 25\,\text{mV}$, Pt100 RTD bridge + 3-op-amp INA with $100\,\text{dB}$ CMRR hum rejection, and 40m `7.074 MHz` FT8 ham radio transceiver with $\text{VSWR}=1.002$, Tayloe $\text{IRR}=52.4\,\text{dB}$, Friis $\text{NF}=1.84\,\text{dB}$, and $-58.6\,\text{dBc}$ Chebyshev LPF harmonic suppression),
  - 9 `obend hardware` / `obend fabublox` / `obend verify` CLI certificate & refusal checks (`hw-pnr-bitstream@1`, `hw-retime-sta@1`, `waferspace-signoff@1`, `fabublox-run@1`, `datasheet-fit@1`, `rf-transceiver-signoff@1`, `photonics-pic-signoff@1`, `pcb-board-signoff@1`, `agentic-eda-swap@1`),
  - Verified sequential `Nat.rec` FSM synthesis via `obend lower sumTo --arg 10 --rtl` (`sumTo 10 = 55`, `cycles = 10`, `done = 1`).
