# Hardware, FPGA, and GPU Architecture

Obend's hardware stack (`lean/Obend/Hardware`, `lean/Obend/Apps`, `lean/Obend/Trailblaze/StageBInstances.lean`) compiles functional specifications, open hypergraphs, and array kernels to synthesizable RTL, interaction nets, FABulous FPGA bitstreams, WGSL compute shaders, and validated AMD RDNA2 machine code.

---

## 1. Synchronous RTL and Yosys Logic Equivalence (`lean/Obend/Hardware/YosysLec.lean`)

`lean/Obend/Hardware/Types.lean` and `lean/Obend/Hardware/HDL.lean` model synchronous register-transfer designs (`RtlModule`, `RtlExpr`, `WireAssign`, `RegSpec`, `OutputPort`, `ClkDomain`) evaluated over 64-bit bitvectors (`evalWireTable`, `stepModuleRegs`).

`Obend.Hardware.YosysLec` (`lean/Obend/Hardware/YosysLec.lean`) bridges Lean's operational RTL semantics to external synthesis verification:
- Translates `RtlModule` combinational wires and next-state register equations into typed SMT-LIB2 bitvector formulas (`SmtBV`, `SmtBool`, `OutObl`, `RegObl`, `LecScript`).
- `moduleFaithful_of_checkWidths` verifies port and register width bounds (`checkWidths`).
- `lecScript_holds_iff`, `lecScript_unsat_of_agree`, and `lecScript_unsat_of_step` prove that unsatisfiability of the emitted SMT miter script guarantees exact step-by-step equivalence with `stepModuleRegs`.
- `Obend.Hardware.Judge` (`lean/Obend/Hardware/Judge.lean`) exposes RTL synthesis equivalence in `Obend.Judge.registry` as `rtl-synth@1` (`rtlSynthFormat`).

---

## 2. Interaction-Net Lowering (`lean/Obend/Hardware/Hvm`)

For graph-reduction workloads, `lean/Obend/Hardware/Hvm.lean` lowers `Obend.Leaf.Book` definitions to interaction combinator nets (`lean/Obend/Hardware/Hvm/Inet.lean`, `lean/Obend/Hardware/Hvm/Model.lean`, `lean/Obend/Hardware/Hvm/Net.lean`, `lean/Obend/Hardware/Hvm/Lower.lean`):
- `comp_reduces` and `main_reduces` (`lean/Obend/Hardware/Hvm/Net.lean`) prove fuel-indexed reduction soundness from functional intermediate definitions (`FExp`, `FDef`) to active redex nets (`Cfg`, `HTree`).
- `lowerBookToHvm_sound` (`lean/Obend/Hardware/Hvm/Lower.lean`) proves that compiling an `Obend.Leaf.Book` into an `HvmBook` preserves evaluation over scalar arguments, complemented by `CofibLUT16` / linear delta-net FPGA synthesis in `lean/Obend/Trailblaze/StageBInstances.lean` (`apex_lean_fpga_rung2_to_rung5`).

---

## 3. FABulous FPGA Bitstream, Readback, and Glitch-Free DPR (`lean/Obend/Hardware/Fabulous`, `lean/Obend/Hardware/ReductionMachine.lean`)

Rather than trusting place-and-route and bitstream packing tools blindly, `lean/Obend/Hardware/Fabulous` verifies configured FPGA fabric behavior directly from configuration bit patterns:

- **Switch-Matrix & Tile Semantics (`lean/Obend/Hardware/Fabulous/Tile.lean`, `lean/Obend/Hardware/Fabulous/LUT4ABSwitchMatrix.lean`, `lean/Obend/Hardware/Fabulous/WIOSwitchMatrix.lean`)**: Parses tile configuration maps (`SwitchMatrix`, `TileModel`) and proves programmable interconnect multiplexer soundness (`pip_sound`).
- **Bitstream Readback Certificates (`lean/Obend/Hardware/Fabulous/Readback.lean`, `lean/Obend/Hardware/Fabulous/Bitstream.lean`)**: `Cert` (`GateCert`, `FlopCert`, `Entry`) checks routing hops and LUT4/FF configuration bits against a physical bitstream `Bits`; `Cert.required_ofF` establishes netlist realization on the tile `Grid`.
- **End-to-End iCEstick MAC8 Proof (`lean/Obend/Hardware/Fabulous/Mac8.lean`, `lean/Obend/Hardware/Fabulous/Mac8Net.lean`)**: Verifies the complete 8-bit multiply-accumulate (`iceStickMac8`) netlist (`mac8Net`) from reset through arbitrary clock cycles (`mac8_reset_realizes`, `mac8_step_realizes`, `mac8_fabric_realizes_module`, `mac8_fabric_realizes_module_from_reset`).
- **Three-Phase Glitch-Free `ICAP` Reconfiguration (`lean/Obend/Hardware/ReductionMachine.lean`)**: `ReconfigTileState` (`frameCrc64`) and `IcapBitstreamFrame` (`expectedCrc64`, `computedCrc64`) enforce fence isolation (`isolated_fence_clamps_output_during_write`) and corrupt-CRC quarantine (`dpr_corrupt_crc_keeps_tile_isolated`).

---

## 4. Square Open-Hypergraph Compiler (`lean/Obend/Hardware/Square.lean`)

`Obend.Hardware.Square` (`lean/Obend/Hardware/Square.lean`, `lean/Obend/Hardware/OpenHypergraph.lean`) compiles strict symmetric monoidal open hypergraphs (`StrictOpenHypergraph`) simultaneously to synchronous RTL and GPU kernels:
- `compileHypergraphToRtl_sound` proves RTL wire evaluation matches hypergraph denotation (`evalGraph_ofScalar`).
- `rtl_eq_gpu` proves exact output agreement between the compiled RTL module and the lowered GPU kernel program.
- `pipelined_eq_comb` proves that retimed/pipelined hypergraph stages compute the exact same function after pipeline fill latency as combinational evaluation.

---

## 5. GPU Kernels, Vulkan Memory Model, RDNA2 Validation, and ZKP/Collectives

### 5.1 WGSL Emission and Vulkan Scope Presheaves (`lean/Obend/Hardware/Gpu.lean`, `lean/Obend/Hardware/Gpu/Memory.lean`)

- **Kernel & Stage IR (`lean/Obend/Hardware/Gpu.lean`, `lean/Obend/Hardware/ArrayKernel.lean`)**: Lowers typed array and block programs (`ArrayKernel.Program`, `GpuStage`, `GpuProgram`) to multi-stage WebGPU WGSL shaders (`emitStageWgsl`) and host dispatch manifests (`emitPlanJson`), enforcing linear output ownership (`lean/Obend/Hardware/ArrayKernelOwnership.lean`, `lean/Obend/Hardware/ArrayKernelUnique.lean`).
- **Scoped Memory Presheaf (`lean/Obend/Hardware/Gpu/Memory.lean`)**: Formalizes Vulkan/WebGPU memory scopes (`Space`, `Shape`, `Obj`) as a presheaf (`Shape.restrict`, `restrict_device`, `restrictObs_comp`), proving that a candidate execution outcome is permitted by the memory model iff local scope observations glue consistently (`allowed_iff_glues`).

### 5.2 AMD RDNA2 Binary Translation Validator (`lean/Obend/Hardware/Gpu/Rdna2`)

To eliminate shader-compiler bugs between WGSL/kernel IR and GPU silicon, `lean/Obend/Hardware/Gpu/Rdna2` validates compiled AMD RDNA2 (gfx1030) machine binaries directly:
- **Instruction Decoder & Symbolic Semantics (`lean/Obend/Hardware/Gpu/Rdna2/Decode.lean`, `lean/Obend/Hardware/Gpu/Rdna2/Semantics.lean`, `lean/Obend/Hardware/Gpu/Rdna2/Waitcnt.lean`)**: Decodes scalar, vector, LDS, and `s_waitcnt` encodings (`lean/Obend/Hardware/Gpu/Rdna2/Insts/C0.lean`–`lean/Obend/Hardware/Gpu/Rdna2/Insts/C12.lean`) into wavefront machine transitions.
- **Translation Validation (`lean/Obend/Hardware/Gpu/Rdna2/Certified.lean`, `lean/Obend/Hardware/Gpu/Rdna2/CertSound.lean`, `lean/Obend/Hardware/Gpu/Rdna2/Schedule.lean`)**:
  - `certifyDump_sound`: proves a disassembled RDNA2 binary implements an `ArrayGraph`.
  - `certifyBlockDump_sound`: proves workgroup block-kernel equivalence including shared LDS memory (`parseDumpLds`).
  - `certifySchedule_sound`: proves end-to-end correctness of multi-dispatch host schedules (`Schedule`).

### 5.3 Workgroup Blelloch Collectives and Stockham Goldilocks NTT

- **Blelloch Scans & Reductions (`lean/Obend/Hardware/Gpu/CollectiveBuildCorrect.lean`, `lean/Obend/Hardware/Gpu/CollectiveCorrect.lean`)**: Proves workgroup upsweep/downsweep scan and tree-reduction value correctness and memory framing (`scanGroup_value`, `scanGroup_frame`, `reduceGroup_value`, `reduceGroup_frame`).
- **Stockham Goldilocks NTT (`lean/Obend/Hardware/Gpu/Ntt.lean`, `lean/Obend/Hardware/Gpu/NttEndToEnd.lean`, `lean/Obend/Hardware/Gpu/GoldilocksSourceCorrect.lean`)**: Verifies 64-bit Goldilocks prime ($p = 2^{64} - 2^{32} + 1$) modular multiplication (`glMul_sound`) and multi-stage Stockham DIF/DIT number-theoretic transforms (`nttBlockProgram`, `encoded_dft_of_uploads`).

---

## 6. Verified Silicon Applications (`lean/Obend/Apps`, `crates/obend-gui`)

- **`Obend.Hardware.PipelinedRisc` (`lean/Obend/Hardware/PipelinedRisc.lean`, `lean/Obend/Hardware/PipelinedRiscCore.lean`)**: Synthesizable 5-stage 64-bit RISC processor RTL (`pipelinedRiscCoreRtlModule`) with proved Burch–Dill pipeline flushing commutation and sequential register-transfer refinement (`burchDill_step_commutes`, `pipelinedRisc_multiCycle_refines_isa`, `pipelinedRiscRtl_step_refines`).
- **`Obend.Apps.FocHil` (`lean/Obend/Apps/FocHil.lean`)**: Closed-loop 20 kHz salient IPM field-oriented motor drive and 6-level SiC flying-capacitor multilevel inverter (`focHilSequentialRtlModule`, `foc_hil_flatten_and_book_sound`), emitted via `obend-emit-sv foc-hil` with 1-cycle overtemperature fault dominance and Yosys SMT-LIB2 LEC verification.
- **`Obend.Apps.ZkNtt` (`lean/Obend/Apps/ZkNtt.lean`, `lean/Obend/Apps/ZkNtt/Goldilocks.lean`)**: Hardware Goldilocks NTT butterfly and Fiat–Shamir sumcheck transcript coprocessor (`zkNttCoprocRtlModule`).
- **`Obend.Apps.SovereignDrex` (`lean/Obend/Apps/SovereignDrex.lean`)**: Hardware batch-auction clearing datapath (`sovereignDrexBatchTopRtlModule`) paired with `Obend.Vault.UnifiedDeos`.
- **`Obend.Apps.SdrFt8Rx` (`lean/Obend/Apps/SdrFt8.lean`, `lean/Obend/Apps/SdrFt8Rx.lean`)**: Numerically controlled oscillator and quadrature FT8 receiver pipeline with proved phasor error and $\ge 63\,\text{dB}$ image-rejection ratio (`nco_phasor_error`, `sdr_irr_ge_63dB`).
- **Waveform & Geometry Inspection (`crates/obend-gui`)**: Streaming `.vcd` value-change-dump parser (`VcdWaveform`), binary/ASCII `.stl` mesh parser (`StlMesh`), and `.ngc` RS-274 G-code parser (`NgcToolpath`) in `crates/obend-gui/src/apps.rs`.
