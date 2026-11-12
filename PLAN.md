# System Architecture Plan and Verification Gates

This document describes how Obend's subsystems compose from source elaboration through runtime execution, durable vault storage, and hardware emission, along with the automated verification gates enforced at each boundary.

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
  Obend.Leaf     Obend.Vault (Replay.World, Form,
  (Flatten,      FormCheck, Transport, Retention,
   Emit, Book)   Merge) + Reasons + Ledger + Consensus
        │              │
        ▼              ▼
  Obend.Hardware / Obend.Lower        Obend.FFI.Bridge
  (Square, YosysLec, Hvm, Fabulous,   (C ABI ↔ crates/obend-ffi,
   Gpu, Rdna2, Device, GeometryCAM)    obend-sandbox, obend-gui)
```

---

## 2. Subsystem Boundaries and Contracts

### 2.1 Language Front-End and Core (`Obend.Spec`, `Obend.Elab`, `Obend.Core`, `Obend.Leaf`)

- **Front-End Elaboration (`lean/Obend/Spec/Parse.lean`, `lean/Obend/Spec/Elaborate.lean`, `lean/Obend/Spec/C4.lean`)**: Parses `.obend` modules, linearizes multiple-inheritance prototype hierarchies via C4 (`PrecedenceList`), and elaborates laws and claims (`lean/Obend/Spec/LawCompile.lean`, `lean/Obend/Elab/AutoCert.lean`).
- **Core Type & Resource Checking (`lean/Obend/Core/Bidirectional.lean`, `lean/Obend/Core/Check.lean`)**: Validates graded multiplicities (`Quantity`), closure reuse (`Reuse`), canonical/equi-recursive rows (`Ty`), and effect computations (`checkAgainst_sound`, `checked_runBounded_no_refusal`).
- **Book Specialization (`lean/Obend/Leaf/Flatten.lean`, `lean/Obend/Leaf/Emit.lean`, `lean/Obend/Leaf/Specialize.lean`)**: Compiles closed prototype compositions into flat vtables and specialized `Book` definitions (`flatten_sound`, `book_sound`, `specSlot`).

### 2.2 Documents, Vaults, Ledgers, and Consensus (`Obend.Doc`, `Obend.Vault`, `Obend.Reasons`, `Obend.Ledger`, `Obend.Consensus`)

- **Structured Documents (`lean/Obend/Doc/Graph.lean`, `lean/Obend/Doc/Merge.lean`, `lean/Obend/Doc/Structured.lean`)**: Represents prose, citations, fields, and `.obnb` cells as pushout patch graphs (`IsPushout`, `mergeKeyedCells3_commutative`, `projection_preservation`).
- **Replayable Vaults (`lean/Obend/Vault/Replay.lean`, `lean/Obend/Vault/Form.lean`, `lean/Obend/Vault/FormCheck.lean`)**: Commits hash-linked turns (`state_eq_replay_log`), evaluates partial-evaluation authorization membranes (`eval_fill_eq_subst_residual`, `rechecked_zero`), transports scoped capabilities (`lean/Obend/Vault/Transport.lean`), and compacts redacted history (`lean/Obend/Vault/Retention.lean`).
- **Justification, Accounting & Finality (`lean/Obend/Reasons.lean`, `lean/Obend/Ledger/Register.lean`, `lean/Obend/Consensus/SimplexProtocol.lean`, `lean/Obend/Consensus/SimplexTrace.lean`)**: Grounds live rules in Van Gelder's 3-valued fixpoint (`gamma_least`), enforces double-entry conservation (`vault_conserved`, `trial_balance_binds`), and verifies `simplex-trace@1` Byzantine finality certificates (`checkTrace_sound`).

### 2.3 Silicon, GPU, and Physical Compilation (`Obend.Hardware`, `Obend.Lower`, `Obend.Apps`)

- **Digital & FPGA (`lean/Obend/Hardware/YosysLec.lean`, `lean/Obend/Hardware/Hvm/Lower.lean`, `lean/Obend/Hardware/Fabulous/Mac8.lean`, `lean/Obend/Lower/Proofs/SiliconKernel.lean`)**: Lowers `Book` and Lean kernel definitions to RTL and interaction nets (`lowerBookToHvm_sound`, `real_silicon_kernel_node_check_sound`), emits SMT-LIB2 LEC obligations (`lecScript_unsat_of_step`), and verifies FABulous FPGA bitstreams (`mac8_fabric_realizes_module`).
- **GPU & Collectives (`lean/Obend/Hardware/Square.lean`, `lean/Obend/Hardware/Gpu.lean`, `lean/Obend/Hardware/Gpu/Memory.lean`, `lean/Obend/Hardware/Gpu/Rdna2/Certified.lean`, `lean/Obend/Hardware/Gpu/CollectiveCorrect.lean`, `lean/Obend/Hardware/Gpu/NttEndToEnd.lean`)**: Lowers open hypergraphs and array kernels to WGSL and validated RDNA2 ISA binaries (`rtl_eq_gpu`, `certifyDump_sound`, `scanGroup_value`, `encoded_dft_of_uploads`).
- **Continuous & Geometric Judges (`lean/Obend/Hardware/Device/DriftDiffusion.lean`, `lean/Obend/Hardware/GeometryCAM.lean`, `lean/Obend/Apps/FidgetCamCert.lean`, `lean/Obend/Apps/SdrFt8Rx.lean`)**: Certifies 1D semiconductor drift-diffusion (`ddFormat_sound`), CNC toolpath gouge freedom (`fidget_toolpath_no_gouge_continuous`), and fixed-point SDR receiver bounds (`sdr_irr_ge_63dB`).

### 2.4 Host FFI and Rust Libraries (`Obend.FFI.Bridge`, `crates/*`)

- **`crates/obend-ffi`**: Links against `libobend_Obend.so` (`lean/Obend/FFI/Bridge.lean`, `lean/c/obend_bridge.c`) to drive `Obend.Vault.Replay.Session`, `.obend` cell evaluation, `Obend.Judge.registry` witness checks, and Merkle receipt verification.
- **`crates/obend-sandbox`**: Enforces process sandboxing (`LaunchGate`, `GrainExecutor`, `CpuMeter`, `bwrap`, macOS SBPL).
- **`crates/obend-gui`**: Provides zero-copy/streaming `.vcd`, `.stl`, and `.ngc` artifact parsers (`crates/obend-gui/src/apps.rs`) and an asynchronous PIDE session client (`ObendSession` in `crates/obend-gui/src/evaluator.rs`).

---

## 3. Verification Gates

| Gate | Implementation | Invariant Enforced |
| :--- | :--- | :--- |
| **Axiom & Compiler-Trust Census** | `lean/Obend/AssertAxioms.lean`, `lean/Obend/AssertCompiled.lean`, `lean/Obend/Census.lean` | Rejects `sorryAx` (`no_sorry_ax` floor) and undeclared axioms across the `Obend` module graph; re-executes compiled-decision obligations via `#assert_compiled`. |
| **Mutation Falsifiability (`#tooth`)** | `lean/Obend/Tactic/Tooth.lean`, `lean/Obend/Teeth/` | Verifies that soundness proofs fail when checkers, encoders, or step relations are adversarially mutated. |
| **Documentation Slot Census** | `lean/Obend/Tactic/DocsCensus.lean` (`#check_docs_census`, `#docs_census`, `#census_environment`) | Verifies that all thirteen root `.md` documents resolve every cited `lean/Obend/...` or repo path, `Obend.*` constant, bare/qualified identifier, and fenced `inductive` constructor block against `Lean.Environment`. |
| **FFI & Rust Integration Tests** | `lean/tests/metasystem/FfiTruthfulnessTest.lean`, `crates/obend-ffi/tests/`, `crates/obend-sandbox`, `crates/obend-gui/tests/` | Exercises live `Replay.World` turn admission, fail-closed witness checking, `simplex-trace@1` FFI verification, OS sandbox confinement, and `.vcd`/`.stl`/`.ngc` parsers. |
