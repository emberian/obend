# Objective Bend (`obend`)

Objective Bend is a verified open-recursive language, certificate-checked sovereign state engine, mathematical analysis substrate, and hardware compiler/elaborator written in Mathlib-free **Lean 4.35** (`479` modules under [`lean/Obend/`](lean/Obend/), `0 sorryAx`, `0` custom axioms) paired with a **Rust** runtime, cloud-FPGA HAL, BFT node, and interactive PIDE workbench ([`crates/`](crates/)).

---

## Architecture Overview

```text
  .obend / .obnb / Lean 4 Declarations
         │
         ├──► Front-End & AutoCert (Obend.Spec / Obend.Elab)
         │      C4 open recursion (`self` / `super` / `fix`), nominal `#kind` lineage,
         │      surface laws + Bellman-Ford witness repair, compile-time `AutoCert`
         │      synthesis (`interval@1`, `taylor-model@1`, `sos-lyapunov-cbf@1`,
         │      `groebner@1`, `rtl-synth@1`)
         │
         ├──► Core4, Leaf Specialization & Futamura Staging (Obend.Core / Obend.Leaf)
         │      Lazy call-by-need demand machine = call-by-name semantics, linear
         │      resource conservation, `super`-free prototype flattening (`Book`),
         │      pin-guarded specialization (`Slot`: 1-cycle deoptimization on moved pins)
         │
         ├──► Silicon Lean 4 Elaborator & Proof Tactics (Obend.Lower / Obend.Tactic)
         │      88-bit `HwExprCAM` (`OBCAMv1` wire protocol), 4-Zone `SiliconElabFabric`
         │      (CAM WHNF, 2D XY NoC unifier, ICAP DPR `@[simp]` LUT, Zone-4 kernel FSM),
         │      `#silicon_check`, `by silicon_{simp,eqsat,sos,interval,flowpipe}`
         │
         ├──► Verified RTL, GPU & Foundry Spine (Obend.Hardware / Obend.Analysis)
         │      Stateful `always_ff` SystemVerilog-2012 + hard-IP macros (`DSP48E2`,
         │      `URAM288`, `ICAP` DPR), 64-bit AMD `VOP64`, Z3 `QF_BV` LEC, Verilator
         │      co-sim (`obend verilate`), 9-stage ASIC/MPW signoff (`obend tapeout`),
         │      AWS EC2 F2 (`vu47p` `cl_obend`) shell + `crates/obend-fpga-hal`
         │
         └──► Sovereign Vaults, Ledger & BFT Node (Obend.Vault / Obend.Consensus / crates/)
                Pijul pushout document/state graphs, double-entry `Ledger` & `DReX` LP
                batch clearing, `K-CARRY` (`world-carry@1`) live schema/law migration,
                Simplex BFT + WAL recovery (`obend-node`), Literate PIDE GUI (`obend-gui`)
```

---

## Quickstart

### 1. Build the Lean 4 Kernel, Compiler & Axiom/Mutation Gates

```bash
cd lean
lake build obend Obend        # Tier 1: compiler, kernel, tactics, hardware & apps
lake build Obend.Census Teeth # Tier 2: whole-tree 0-sorryAx census + #tooth mutation suite
```

### 2. Run, Elaborate, Verilate & Tape Out `.obend` Programs

```bash
# Typecheck and evaluate an open-recursive .obend module
cd lean && lake exe obend check ../stdlib/physical/Cnc5AxisMill.obend
cd lean && lake exe obend run ../stdlib/physical/Cnc5AxisMill.obend compensatedErrorSample

# Differential Verilator co-simulation + Z3 QF_BV gate-level equivalence check (LEC)
cd lean && lake exe obend verilate ../stdlib/physical/QuantumPhotonicMatter.obend --vectors 8 --cycles 4 --lec

# End-to-end 9-stage RTL -> BEL -> Retiming -> PnR -> DRC/TCAD -> SystemVerilog/LibreLane tapeout
cd lean && lake exe obend tapeout ../stdlib/physical/CleanroomTcadStack.obend --out-sv /tmp/tcad.sv
```

### 3. Hardware-Assisted Lean 4 (`#silicon_check` & `by silicon_*`)

Inside Lean 4 (`import Obend.Tactic.SiliconElab`), declarations can be extracted into an 88-bit associative `HwExprCAM` (`OBCAMv1`), checked on the 4-zone hardware state machine and Verilated RTL co-processor, or discharged by untrusted hardware/symbolic oracles that reconstruct `0 sorry` Lean kernel proofs:

```lean
import Obend.Tactic.SiliconElab

-- Reflexive self-hosting check over the 88-bit HwExprCAM + Zone-4 hardware FSM + Verilator RTL
#silicon_check Obend.Lower.LeanKernel.kernelCheckDecl
#silicon_check Obend.Core.type_preservation

-- Proof-reconstructing hardware/analytic tactics (kernel-verified proof terms, 0 sorryAx)
example (x : Int) : (x + 3) * (x + 3) = x * x + 6 * x + 9 := by silicon_eqsat
```

### 4. Rust Workspace: Cloud-FPGA HAL, Sovereign Node & PIDE Workbench

```bash
cargo test --workspace

# Run the standalone 4-zone Silicon Elaborator + ICAP DPR simulator via obend-fpga-hal
cargo run -p obend-fpga-hal --bin obend-silicon-sim -- --cycles 8 --dpr-test

# Launch the Literate PIDE, CAD/Multiphysics & Live FPGA/ILA Workbench
cargo run -p obend-gui -- serve --bind 127.0.0.1:7878
```

---

## Repository Layout

| Directory | Contents |
| :--- | :--- |
| [`lean/Obend/`](lean/Obend/) | `479`-module Mathlib-free Lean 4.35 formalization, compiler, tactics, external certificate judges, hardware synthesizer, and `obend` CLI (`Obend/Main.lean`). |
| [`crates/obend-fpga-hal/`](crates/obend-fpga-hal/) | Unified BAR0 (`AXI4-Lite`) + 512-bit `AXI4-Stream` HAL (`ObendFpgaHal`) spanning POSIX `mmap` Verilator co-sim (`SimBackend`) and AWS EC2 F2 `vu47p` `/dev/fpga0` + XDMA (`AwsF2Backend`). |
| [`crates/obend-node/`](crates/obend-node/) | Durable Simplex BFT validator host (`DurableSimplexHost`), Fog-of-War Merkle multiproofs, `drex-clearing@1` batch settlement, `world-carry@1` hot upgrades, and `ObendFpgaHal` turn acceleration. |
| [`crates/obend-gui/`](crates/obend-gui/) | Literate `.obend` / `.obnb` PIDE HTTP workbench, SVG/3D multiphysics & GDSII viewports, `LawDial` sliders, live FPGA/ILA register inspection, and flagship app explorer. |
| [`crates/obend-ffi/`](crates/obend-ffi/) & [`crates/obend-sandbox/`](crates/obend-sandbox/) | C-ABI / Lean FFI session bridge (`Obend/FFI/Bridge.lean`) and capability-isolated grain execution sandbox. |
| [`apps/`](apps/) | **8 end-to-end flagship userspace qualification applications**, each with multi-layer `.obend` sources, Lean soundness proofs (`Obend/Apps/`), cycle-accurate C++ Verilator testbenches, and Z3 `QF_BV` LEC miters. |
| [`stdlib/`](stdlib/) | Canonical `.obend` standard library packages (`core/Cell`, `ledger/Account`, `usd/ScenePrim`, `physical/{CleanroomTcadStack,Cnc5AxisMill,LcDrivesStator,Ms350FcmlPhaseLeg,QuantumPhotonicMatter}`). |
| [`hardware/`](hardware/) | Canonical SystemVerilog/Z3 simulation harnesses (`hardware/sim/`) and AWS EC2 F2 `vu47p` custom logic bridge & Vivado synthesis scripts (`hardware/aws-f2/`). |

---

## The 8 Flagship Qualification Applications ([`apps/`](apps/))

Each flagship application exercises the full stack from multi-layer open-recursive `.obend` specs through Lean kernel theorems (`lean/Obend/Apps/*.lean`), SystemVerilog RTL emission, Z3 `QF_BV` equivalence checking, and cycle-accurate `Verilator` co-simulation:

1. **[`apps/obend-risc/`](apps/obend-risc/)** ([`Obend/Apps/ObendRisc.lean`](lean/Obend/Apps/ObendRisc.lean)) — **3-Layer Open-Recursive Sequential RISC Softcore**: `BaseRiscCore` $\gg$ `PrivilegeCsrOverride` (`ECALL`/`MRET`) $\gg$ `CustomSimdZkExt` (`0x2B` MAC) with in-core bit-slice instruction decode, `always_ff` `pc`/CSR/regfile state, non-interference proofs, and firmware boot in Verilator.
2. **[`apps/foc-hil/`](apps/foc-hil/)** ([`Obend/Apps/FocHil.lean`](lean/Obend/Apps/FocHil.lean)) — **Closed-Loop 20 kHz FOC Motor Drive & 6-Level SiC FCML HIL**: Stateful `ClarkePark` $\to$ `PiCurrentLoop` $\to$ `SicFcmlInverterLeg` controller with `AutoCert` Lyapunov/CBF & Taylor-model certificates, co-simulated against a continuous-time RK4 PMSM + SiC plant with live mid-run ICAP DPR hot-swap.
3. **[`apps/sdr-ft8/`](apps/sdr-ft8/)** ([`Obend/Apps/SdrFt8.lean`](lean/Obend/Apps/SdrFt8.lean)) — **All-Digital 40m Tayloe IQ SDR & 4-Stage CORDIC FT8 Demodulator**: Signed fixed-point Quadrature NCO $\to$ 3-stage $z^{-1}$ CIC decimator & polyphase FIR $\to$ CORDIC phase differentiator suppressing a $+40\text{ dB}$ image interferer by $\ge 60\text{ dB}$ IRR and recovering 79/79 FT8 symbols in Verilator.
4. **[`apps/zk-ntt/`](apps/zk-ntt/)** ([`Obend/Apps/ZkNtt.lean`](lean/Obend/Apps/ZkNtt.lean)) — **Goldilocks ($p = 2^{64} - 2^{32} + 1$) NTT & Multilinear Sumcheck Co-Processor**: 128-to-64 Goldilocks reduction, radix-2 butterfly, and Sumcheck round folding optimized via `EqSatHypergraph` and lowered to both pipelined SystemVerilog (`Verilator`) and 64-bit AMD `VOP64`.
5. **[`apps/silicon-kernel-verilator/`](apps/silicon-kernel-verilator/)** ([`Obend/Apps/SiliconKernelVerilator.lean`](lean/Obend/Apps/SiliconKernelVerilator.lean)) — **Verilated 4-Zone Silicon Elaborator & Live ICAP DPR Showcase**: Streams `OBCAMv1` bundles over AXI4-Stream into `silicon_elab_top.sv`, executes a 3-phase glitch-free Zone-3 `@[simp]` LUT hot-swap, verifies 1-cycle `moved_pin_blocks` fallback, and refuses `#tooth`-mutated / `sorryAx` proofs in hardware.
6. **[`apps/fidget-cam/`](apps/fidget-cam/)** ([`Obend/Apps/FidgetCam.lean`](lean/Obend/Apps/FidgetCam.lean)) — **Parametric OpenUSD/F-Rep Impeller $\to$ Verilated Voxelizer, `.stl` Mesh & 5-Axis G-Code**: Multi-layer `.obend` F-Rep CAD with `LIVERPS` overrides $\to$ certified Lipschitz & wall-thickness bounds $\to$ pruned SSA tape $\to$ Verilated octree evaluator emitting binary `.stl` and gouge-verified 5-axis `.ngc` G-code.
7. **[`apps/sovereign-drex/`](apps/sovereign-drex/)** ([`Obend/Apps/SovereignDrex.lean`](lean/Obend/Apps/SovereignDrex.lean)) — **Hot-Upgradable Sovereign Exchange (`DReX` + `K-CARRY`)**: Multi-file `Seat` / `OrderBook` / `BatchClearing` `.obend` package with half-edge supply conservation, `"world-carry@1"` live schema/law migration, Verilator/Z3 batch clearing, and 4-validator `obend-node` WAL crash/recovery.
8. **[`apps/quantum-photonic-matter/`](apps/quantum-photonic-matter/)** ([`Obend/Apps/QuantumPhotonicMatter.lean`](lean/Obend/Apps/QuantumPhotonicMatter.lean)) — **Planar Clements Photonic CTQW, Majorana Tetron Co-Processor & 1-WL Quotient Accelerator**: Compresses symmetric `StrictOpenHypergraph` forward + reverse-AD graphs via 1-WL `quotientOpenHypergraph` (with 1-cycle `quotientHypergraphSlot` fallback), Faddeev–LeVerrier thermal crosstalk cancellation, $Q_3$ Krawtchouk PST, and Majorana parity cooling in Verilator + Z3.

---

## Lean 4 Library Subsystems ([`lean/Obend/`](lean/Obend/))

| Subsystem | Scope & Key Verified Components |
| :--- | :--- |
| `Obend.Core`, `Obend.Equiv` | Core4 calculus (`Term`, `Check`, `Machine`, `MachineFast`, `Packet`, `Code`), call-by-name $\equiv$ call-by-need equivalence, bitwise/shift & signed `Q32.32` (`qmul32`) primitives, nominal `#kind` branding, linear conservation, subject reduction (`Obend/Core/Proofs/SubjectReduction.lean`), and clairvoyant cost equivalence (`Obend/Equiv/Clairvoyant.lean`). |
| `Obend.Spec`, `Obend.Elab` | `.obend` parser/elaborator (`Parse`, `Elaborate`, `FrontEnd`), cross-package C4 linearization (`CrossPackage`), `#import_obend` (`Obend/Elab/Workbook.lean`), `LawDial` Bellman-Ford multi-field repair, and compile-time `AutoCert` external witness synthesis (`Obend/Elab/AutoCert.lean`). |
| `Obend.Law`, `Obend.Logic` | Inherited occasion-judged contracts (`Obend/Law/Contract.lean`), open-recursive equational logic (`late_binding`, `rewrite_sound`, `claim_frame`), external judge discharge (`Obend/Logic/Obligation.lean`), and notebook derivation turns. |
| `Obend.Slot`, `Obend.Kind`, `Obend.Intention` | Contextual deferred-decision `Slot`s with withdrawable supports and 1-cycle invalidation (`moved_pin_blocks`), C4 `Kind` cells, and unified cross-package/vault `Intention` resolution. |
| `Obend.Leaf` | Prototype flattening (`Flatten`: eliminates `super` dispatch), first-order `Book` emission, pin-guarded `Specialize`, `BendTT` lowering, and in-core Futamura projections (`Obend/Leaf/Futamura.lean`). |
| `Obend.Lower`, `Obend.Tactic` | Bidirectional Lean 4 $\leftrightarrow$ Core4 lowering (`Inductive`, `LCNF`, `LeanKernel`, `Reflect`), 88-bit `ExprCAM` (`OBCAMv1` wire codec & transitive cone extraction), 4-Zone `SiliconElabFabric`, 64-bit AMD `VOP64` & Ozaki FP4 (`Obend/Lower/Proofs/SelfAccelerate.lean`), `#silicon_check` & `by silicon_*` (`Obend/Tactic/SiliconElab.lean`), `by obend`, `by weave`, `#tooth`, and `#check_docs_census`. |
| `Obend.Analysis` | Validated `TaylorModel`s, $N$-D Picard–Lindelöf ODE `Flowpipe`s, `SosLyapunov` (`sos-lyapunov-cbf@1` Positivstellensatz/CBF/DAE), `EqSatHypergraph` + whole-DAG reverse AD, 1-WL `Equitable` block-spinor partitions, `QuantumWalk` spectral projectors, and static change-impact cones. |
| `Obend.Hardware` | `43`-module verified hardware & multiphysics stack: `HDL` (`emitHierarchicalSV`), packed `Types` (`RtlLayoutCtx`), `Compiler` (`compileRichTerm`, `compileStatefulStepToRtl`), `ReductionMachine` (NoC + ICAP DPR), `Synth`, `Retiming`, `PlaceRoute`, `DRC`, `FabuBlox`, `TcadBridge`, `WaferSpace`, `TapeoutPipeline`, `VerilateRunner`, CSR `OpenHypergraph`, `QuantumMatter`, `Photonics`, `OpenUSD`, `GeometryCAM`, `DigitalTwin`, `RF`, `DSP`, `PCB`, `Analog`, `Thermal`, `Physics`, `Judge`, and `Codec`. |
| `Obend.Fold`, `Obend.Judge`, `Obend.Receipt` | Audited `Fold`, kernel-verified `Judge` format registry (`Lrat`, `Interval`, `Groebner`, `TaylorModel`, `SosLyapunov`, `WorldCarry`, and `Hardware` formats), and cSHAKE256 Merkle-dated `Receipt`s with blind multiproofs. |
| `Obend.Doc`, `Obend.Vault`, `Obend.Ledger`, `Obend.Consensus`, `Obend.Run`, `Obend.FFI` | Pijul pushout `Vault` merges, `"world-carry@1"` live state migration (`Obend/Vault/Carry.lean`), `SovereignEngine`, double-entry `Ledger` & `DReX` clearing, Simplex BFT & `SovereignFinality` (`Obend/Consensus/SovereignFinality.lean`), durable `Run`, and C-ABI `FFI` (`Obend/FFI/Bridge.lean`). |

---

## Design & Specification Documents

- [`QUALIFICATION-AND-SILICON-LEAN.md`](QUALIFICATION-AND-SILICON-LEAN.md) — Wave 4 full-stack specification: unscoped `.obend` hardware/compiler foundations, `AutoCert`, live Hardware-Assisted Lean 4 (`#silicon_check` / `by silicon_*`), 4-rung Verilator $\to$ AWS EC2 F2 (`vu47p`) qualification ladder, and the 8 flagship `apps/`.
- [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md) — 4-Zone `SiliconElabFabric` architecture (`HwExprCAM`, 2D NoC unifier, `Slot`-guarded ICAP DPR `DiscrTree` LUT, and Zone-4 hardware kernel FSM).
- [`PHYSICAL.md`](PHYSICAL.md) — Verified silicon synthesis, TCAD/cleanroom physics, photonics, quantum matter, F-Rep/OpenUSD CAD/CAM, RF/DSP, and power electronics metatheory.
- [`NEXT-MATHEMATICA.md`](NEXT-MATHEMATICA.md) — Symbolic-analytic-physical workbook architecture (`TaylorModel`, `Flowpipe`, `SosLyapunov`, `EqSatHypergraph`, `OpenHypergraph`, `.obnb` PIDE).
- [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md) — Sovereign `Vault`s, `CellContract`s, `K-CARRY` hot-upgrades, `DReX` batch clearing, DeOS capability surfaces, and Simplex/Epistemic finality.
- [`METATHEORY.md`](METATHEORY.md) — Theorem-by-theorem catalog, `#tooth` mutation verification methodology, and `Obend/Census.lean` zero-`sorryAx` enforcement.
- [`DESIGN.md`](DESIGN.md) · [`THESIS.md`](THESIS.md) · [`AMBITION.md`](AMBITION.md) · [`PLAN.md`](PLAN.md) · [`GROUNDING.md`](GROUNDING.md) — Core language design, falsifiable thesis claims, roadmap, and lineage.

---

## License

AGPL-3.0 — Ember Arlynx ([ember.software](https://ember.software)).
