# System Architecture Plan and Verification Gates

This document describes how Obend's subsystems compose from source elaboration through runtime execution, categorical/cryptographic assurance, durable sharded vault storage, and hardware emission, along with the automated verification gates enforced at each boundary.

---

## 1. End-to-End Subsystem Pipeline

```
  .obend / .obnb Source & Certificate Envelopes
                       │
        ┌──────────────┴──────────────┐
        ▼                             ▼
  Obend.Spec / Obend.Elab       Obend.Doc.Structured
  (Parse, C4, AutoCert)         (Graph, Merge, Section)
        │                             │
        ▼                             │
  Obend.Core (Term, Ty,               │
  Check, Bidirectional, Machine)      │
        │                             │
        ├──────────────┬──────────────┘
        ▼              ▼
  Obend.Leaf     Obend.Vault (Replay.World, ChunkedWorld,
  (Flatten,      Form, FormCheck, CheckedCarry, UnifiedDeos)
   Emit, Book)   + Reasons + Ledger + Consensus + Crypto
        │              │
        ▼              ▼
  Obend.Hardware / Obend.Lower        Obend.FFI.Bridge
  (Square, YosysLec, Hvm, Fabulous,   (C ABI ↔ crates/obend-ffi,
   Gpu, Rdna2, FocHil, GeometryCAM)    obend-sandbox, obend-gui)
```

---

## 2. Subsystem Boundaries and Contracts

### 2.1 Language Front-End and Core (`Obend.Spec`, `Obend.Elab`, `Obend.Core`, `Obend.Leaf`)

- **Front-End Elaboration (`lean/Obend/Spec/Parse.lean`, `lean/Obend/Spec/Elaborate.lean`, `lean/Obend/Spec/C4.lean`)**: Parses `.obend` modules, linearizes multiple-inheritance prototype hierarchies via C4 (`PrecedenceList`), and elaborates laws and claims (`lean/Obend/Spec/LawCompile.lean`, `lean/Obend/Elab/AutoCert.lean`).
- **Core Type & Resource Checking (`lean/Obend/Core/Bidirectional.lean`, `lean/Obend/Core/Check.lean`)**: Validates graded multiplicities (`Quantity`), closure reuse (`Reuse`), canonical/equi-recursive rows (`Ty`), and effect computations (`checkAgainst_sound`, `checked_runBounded_no_refusal`).
- **Book Specialization (`lean/Obend/Leaf/Flatten.lean`, `lean/Obend/Leaf/Emit.lean`, `lean/Obend/Leaf/Specialize.lean`)**: Compiles closed prototype compositions into flat vtables and specialized `Book` definitions (`flatten_sound`, `book_sound`, `specSlot`).

### 2.2 Documents, Sharded Vaults, Ledgers, and Consensus (`Obend.Doc`, `Obend.Vault`, `Obend.Reasons`, `Obend.Ledger`, `Obend.Consensus`)

- **Structured Documents (`lean/Obend/Doc/Graph.lean`, `lean/Obend/Doc/Merge.lean`, `lean/Obend/Doc/Structured.lean`)**: Represents prose, citations, fields, and `.obnb` cells as pushout patch graphs (`IsPushout`, `mergeKeyedCells3_commutative`, `projection_preservation`).
- **Replayable & Sharded Vaults (`lean/Obend/Vault/Replay.lean`, `lean/Obend/Vault/ChunkedWorld.lean`, `lean/Obend/Vault/Form.lean`, `lean/Obend/Vault/CheckedCarry.lean`, `lean/Obend/Vault/UnifiedDeos.lean`)**: Commits hash-linked turns (`state_eq_replay_log`), persists binary-framed sharded bucket snapshots (`FastCodec`, `dig_eq_unbe_logHashArray`), evaluates partial-evaluation authorization membranes (`eval_fill_eq_subst_residual`, `rechecked_zero`), preserves capabilities across rerooting (`live_capability_survives_rerooting`), transports scoped capabilities (`lean/Obend/Vault/Transport.lean`), and composes multi-asset DEOS settlement (`unifiedDeos_ledger_and_turn_sound`).
- **Justification, Multilateral Netting & Finality (`lean/Obend/Reasons.lean`, `lean/Obend/Run/HyperLaw.lean`, `lean/Obend/Ledger/Register.lean`, `lean/Obend/Judge/Netting.lean`, `lean/Obend/Consensus/SimplexProtocol.lean`, `lean/Obend/Consensus/SimplexTrace.lean`)**: Grounds live rules in Van Gelder's 3-valued fixpoint (`gamma_least`) and Gelfond–Lifschitz modal equilibria (`glEquilibriumJudge`, `checkGLEquilibrium_sound`), enforces double-entry conservation and multilateral obligation netting (`vault_conserved`, `trial_balance_binds`, `settleNetting_agrees_with_gross`), and verifies `simplex-trace@1` Byzantine finality certificates (`checkTrace_sound`).

### 2.3 Silicon, GPU, and Physical Compilation (`Obend.Hardware`, `Obend.Lower`, `Obend.Apps`)

- **Digital, FPGA & Silicon Elaborator (`lean/Obend/Hardware/YosysLec.lean`, `lean/Obend/Hardware/Hvm/Lower.lean`, `lean/Obend/Hardware/Fabulous/Mac8.lean`, `lean/Obend/Lower/Proofs/SiliconKernel.lean`, `lean/Obend/Tactic/SiliconElab.lean`)**: Lowers `Book` and Lean kernel definitions to RTL and interaction nets (`lowerBookToHvm_sound`, `silicon_kernel_5stage_check_sound`), drives proof-producing `silicon_simp` rewriting, emits SMT-LIB2 LEC obligations (`lecScript_unsat_of_step`), and verifies FABulous FPGA bitstreams (`mac8_fabric_realizes_module`).
- **GPU & Collectives (`lean/Obend/Hardware/Square.lean`, `lean/Obend/Hardware/Gpu.lean`, `lean/Obend/Hardware/Gpu/Memory.lean`, `lean/Obend/Hardware/Gpu/Rdna2/Certified.lean`, `lean/Obend/Hardware/Gpu/CollectiveCorrect.lean`, `lean/Obend/Hardware/Gpu/NttEndToEnd.lean`)**: Lowers open hypergraphs and array kernels to WGSL and validated RDNA2 ISA binaries (`rtl_eq_gpu`, `certifyDump_sound`, `scanGroup_value`, `encoded_dft_of_uploads`).
- **Continuous, Power-Electronics & Geometric Judges (`lean/Obend/Hardware/Device/DriftDiffusion.lean`, `lean/Obend/Apps/FocHil.lean`, `lean/Obend/Hardware/GeometryCAM.lean`, `lean/Obend/Apps/FidgetCamCert.lean`, `lean/Obend/Apps/SdrFt8Rx.lean`)**: Certifies 1D semiconductor drift-diffusion (`ddFormat_sound`), 20 kHz FOC motor control + 6-level SiC FCML RTL (`focHilSequentialRtlModule`), CNC toolpath gouge freedom (`fidget_toolpath_no_gouge_continuous`), and fixed-point SDR receiver bounds (`sdr_irr_ge_63dB`).

### 2.4 Categorical Foundations, Representation Repair, Dual-Track Cryptography & Trailblazers (`Obend.Category`, `Obend.Repair`, `Obend.Crypto`, `Obend.Trailblaze`)

- **Categorical Open Systems & Graded Refinement (`lean/Obend/Category/OpenSystem.lean`, `lean/Obend/Category/Refines.lean`, `lean/Obend/Category/GradedLogic.lean`)**: Composes port-Hamiltonian dissipative systems (`OpenDissipativeSys`, `skew_gyrator_power_cancels`), metric/stutter Galois refinements (`GaloisRefinement`, `sim_preserves_galois`), and 5-axis graded Hoare triples (`GradedM`, `CompositeGrade`, `frame_triple`).
- **Algebraic/Coalgebraic Repair & Compositional Automation (`lean/Obend/Repair/AlgConfig.lean`, `lean/Obend/Repair/CoalgConfig.lean`, `lean/Obend/Repair/QuotAssembly.lean`, `lean/Obend/Tactic/Compositional.lean`)**: Transports invariants across representation changes via initial-algebra configurations (`AlgConfig`, `repair_by_instantiation`), parameterized coinduction (`paco_coind`), effective quotients (`EffectiveQuotient`, `quotAssembly`), and `Judge` / `Format.ofCodec` combinators (`gradedTriple_of_symExec`).
- **Dual-Track Post-Quantum Cryptography & Trailblazer Slices (`lean/Obend/Crypto/DualSpine.lean`, `lean/Obend/Crypto/SameOpening.lean`, `lean/Obend/Trailblaze/Polis.lean`, `lean/Obend/Trailblaze/LeanFpga.lean`)**: Binds multilinear sumcheck and polynomial commitments simultaneously to Merkle hash openings and Module-SIS Ajtai lattice commitments (`canopyAjtaiDualPCS_sound_of_hash_or_sis`, `verifySameOpening_sound`), alongside vertical `seL4`/Blum-memory (`apex_polis_deos_turn_safe`) and `CofibLUT16`/delta-net FPGA (`apex_lean_fpga_rung2_to_rung5`) slices.

### 2.5 Host FFI and Rust Libraries (`Obend.FFI.Bridge`, `crates/*`)

- **`crates/obend-ffi`**: Links against `libobend_Obend.so` (`lean/Obend/FFI/Bridge.lean`, `lean/c/obend_bridge.c`) to drive thread-pinned `!Send` `ObendSession` (`Obend.Vault.Replay.Session`), `.obend` cell evaluation, `Obend.Judge.registry` witness checks, and Merkle receipt verification.
- **`crates/obend-sandbox`**: Enforces process sandboxing (`LaunchGate`, `GrainExecutor`, `CpuMeter`, `bwrap`, macOS SBPL).
- **`crates/obend-gui`**: Provides zero-copy/streaming `.vcd`, `.stl`, and `.ngc` artifact parsers (`crates/obend-gui/src/apps.rs`) and a dedicated worker-thread session client (`ObendSession` in `crates/obend-gui/src/evaluator.rs`).

---

## 3. Verification Gates

| Gate | Implementation | Invariant Enforced |
| :--- | :--- | :--- |
| **Axiom & Compiler-Trust Census** | `lean/Obend/AssertAxioms.lean`, `lean/Obend/AssertCompiled.lean`, `lean/Obend/Census.lean` | Rejects `sorryAx` (`no_sorry_ax` floor) and undeclared axioms across the `Obend` module graph; re-executes compiled-decision obligations via `#assert_compiled`. |
| **Mutation Falsifiability (`#tooth`)** | `lean/Obend/Tactic/Tooth.lean`, `lean/Obend/Teeth/` | Verifies that soundness proofs fail when checkers, encoders, or step relations are adversarially mutated. |
| **Documentation Slot Census** | `lean/Obend/Tactic/DocsCensus.lean` (`#check_docs_census`, `#docs_census`, `#census_environment`) | Verifies that all thirteen root `.md` documents resolve every cited `lean/Obend/...` or repo path, `Obend.*` constant, bare/qualified identifier, and fenced `inductive` constructor block against `Lean.Environment`. |
| **FFI & Rust Integration Tests** | `lean/tests/metasystem/FfiTruthfulnessTest.lean`, `crates/obend-ffi/tests/`, `crates/obend-sandbox`, `crates/obend-gui/tests/` | Exercises live `Replay.World` turn admission, fail-closed witness checking, `simplex-trace@1` FFI verification, OS sandbox confinement, and `.vcd`/`.stl`/`.ngc` parsers. |
