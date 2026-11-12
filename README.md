# Obend

Obend is a formally verified programming language, local-first document and vault substrate, certificate-checking judgment registry, and hardware/GPU compilation stack implemented in Lean 4 (`lean/Obend`) with a thin Rust host workspace (`crates/`).

Every semantic layer — from extrinsic linear/graded row typing and open-recursive specialization to append-only vault replay, double-entry ledger conservation, Simplex consensus trace verification, FABulous FPGA bitstream readback, and RDNA2 GPU binary translation validation — is defined once as an executable model in Lean 4 and paired with kernel-checked soundness and refusal proofs.

---

## Architecture Overview

| Layer | Lean Modules / Host Crates | Primary Guarantees |
| :--- | :--- | :--- |
| **Core Calculus & Typing** | `lean/Obend/Core/Term.lean`, `lean/Obend/Core/Ty.lean`, `lean/Obend/Core/Check.lean`, `lean/Obend/Core/Bidirectional.lean`, `lean/Obend/Core/Machine.lean` | Extrinsic graded/linear (`Quantity`, `Reuse`) bidirectional checker (`checkAgainst_sound`) over Amadio–Cardelli equi-recursive and canonical finite rows (`finite_field_commute`, `finite_field_shadow`), paired with type preservation (`step_preserves_typing`, `checked_runBounded_no_refusal`). |
| **Intentions, Slots & Leaf** | `lean/Obend/Intention.lean`, `lean/Obend/Slot.lean`, `lean/Obend/Slot/Protocol.lean`, `lean/Obend/Leaf/Flatten.lean`, `lean/Obend/Leaf/Emit.lean`, `lean/Obend/Leaf/Residual.lean`, `lean/Obend/Leaf/Specialize.lean` | Explicit dependency pinning (`current_iff_usable`, `stale_iff_blocked`), open-recursive prototype flattening (`flatten_sound`, `book_sound`), residual super-reference elimination (`vtable_clean`, `no_residual_super`), and Futamura book specialization (`specSlot`, `moved_pin_blocks`). |
| **Patch-Graph Documents** | `lean/Obend/Doc/Graph.lean`, `lean/Obend/Doc/Merge.lean`, `lean/Obend/Doc/Section.lean`, `lean/Obend/Doc/Structured.lean` | Pijul-style directed atom graphs (`IsPushout`), commutative 3-way cell merges (`mergeKeyedCells3_commutative`), citation drift refusal (`SourceMoves`), and lossless structured `.obnb` cell round-trips (`projection_preservation`, `stale_pin_invalidates`). |
| **Live Vault, Reasons & Ledger** | `lean/Obend/Vault/Replay.lean`, `lean/Obend/Vault/Form.lean`, `lean/Obend/Vault/FormCheck.lean`, `lean/Obend/Vault/Transport.lean`, `lean/Obend/Vault/Retention.lean`, `lean/Obend/Vault/Merge.lean`, `lean/Obend/Reasons.lean`, `lean/Obend/Ledger/Register.lean`, `lean/Obend/Ledger/Report.lean` | Hash-chained log replay (`state_eq_replay_log`, `checkpoint_is_cache`), residual authorization membranes (`eval_fill_eq_subst_residual`, `admit_no_amplification`), single-pass form checking (`rechecked_zero`), capability handoff (`handoff_no_absence`), right-to-forget log compaction (`state_eq_replay_compacted`), Van Gelder 3-valued justification (`gamma_least`, `no_conclusion_from_cycles`), and double-entry conservation (`vault_conserved`, `trial_balance_binds`). |
| **Judges, Genealogy & Consensus** | `lean/Obend/Judge.lean`, `lean/Obend/Judge/Class.lean`, `lean/Obend/Judge/Lrat.lean`, `lean/Obend/Judge/RealAnalysis.lean`, `lean/Obend/Judge/Genealogy.lean`, `lean/Obend/Consensus/SimplexProtocol.lean`, `lean/Obend/Consensus/SimplexTrace.lean` | Graded `Judge` interface with byte-decoded formats (`Obend.Judge.registry`), self-judged succession (`succession_sound`, `lob_cost_necessary`), and Byzantine Simplex safety and trace checking (`finalized_consistent`, `accountable`, `checkTrace_sound`). |
| **Hardware, GPU & Physical** | `lean/Obend/Hardware/YosysLec.lean`, `lean/Obend/Hardware/Hvm/Lower.lean`, `lean/Obend/Hardware/Fabulous/Mac8.lean`, `lean/Obend/Hardware/Square.lean`, `lean/Obend/Hardware/Gpu.lean`, `lean/Obend/Hardware/Gpu/Memory.lean`, `lean/Obend/Hardware/Gpu/Rdna2/Certified.lean`, `lean/Obend/Hardware/Device/DriftDiffusion.lean`, `lean/Obend/Hardware/GeometryCAM.lean` | RTL-to-SMT Yosys LEC (`lecScript_unsat_of_step`), interaction-net lowering (`lowerBookToHvm_sound`), FABulous iCEstick MAC8 bitstream readback (`mac8_fabric_realizes_module`), hypergraph-to-RTL/GPU compilation (`rtl_eq_gpu`), Vulkan scope presheaf (`allowed_iff_glues`), RDNA2 ISA binary validation (`certifyDump_sound`), Blelloch scans (`scanGroup_value`), Stockham Goldilocks NTT (`encoded_dft_of_uploads`), 1D drift-diffusion (`ddFormat_sound`), and CAM gouge checking (`fidget_toolpath_no_gouge_continuous`). |
| **FFI Bridge & Rust Host** | `lean/Obend/FFI/Bridge.lean`, `crates/obend-ffi`, `crates/obend-sandbox`, `crates/obend-gui` | Stateful C ABI backed by `Obend.Vault.Replay.Session`, `.obend` elaboration via `Obend.Spec`, `Obend.Judge.registry` witness verification, Linux `bwrap` / macOS SBPL sandboxing, and streaming `.vcd`, `.stl`, `.ngc` parsers plus PIDE session client. |

---

## Repository Layout

- `lean/Obend/` — Verified Lean 4 core, language front-end (`Spec`, `Elab`, `Law`), document graph (`Doc`), durable vault (`Vault`, `Reasons`, `Ledger`, `Consensus`), certificate registry (`Judge`), Lean-to-silicon lowering (`Lower`), and hardware/GPU/device stacks (`Hardware`, `Apps`).
- `lean/c/obend_bridge.c` — Thin C ABI shim exporting `lean/Obend/FFI/Bridge.lean` entrypoints into `libobend_Obend.so`.
- `crates/obend-ffi/` — Safe Rust bindings over the Lean C ABI (`Session`, `Receipt`), linking directly against the compiled Lean shared library.
- `crates/obend-sandbox/` — Confinement primitives (`LaunchGate`, `GrainExecutor`, `CpuMeter`, Linux `bwrap`, macOS Seatbelt SBPL) for untrusted external solvers and toolchains.
- `crates/obend-gui/` — Rust library providing streaming `.vcd` waveform, `.stl` mesh, and `.ngc` G-code parsers (`apps`) alongside an asynchronous PIDE session client (`ObendSession`) over `obend-ffi`.

---

## Building and Testing

Build the Lean 4 library and shared FFI artifact from `lean/`:

```bash
cd lean
lake build Obend
lake build Obend:shared
```

Run the Rust workspace test suite against the compiled Lean shared library:

```bash
cargo test --workspace
```

Compile-time metatheoretic and documentation integrity gates live in `lean/Obend/AssertAxioms.lean`, `lean/Obend/AssertCompiled.lean`, `lean/Obend/Tactic/Tooth.lean`, and `lean/Obend/Tactic/DocsCensus.lean` (`#check_docs_census`, `#docs_census`, `#census_environment`).

---

## Documentation Map

- `AMBITION.md` — System scope and unifying architectural principles.
- `THESIS.md` — Contextual `Intention` and `Slot` discipline across code, documents, vaults, and hardware.
- `DESIGN.md` — Complete technical design: `Core.Term`, `Core.Ty`, rows, `Slot`/`Leaf`, `Doc`, `Vault`, `Reasons`, `Ledger`, `Judge`, `Hardware`/`Gpu`, and `FFI`.
- `METATHEORY.md` — Soundness theorems, observational improvement, Van Gelder fixpoints, and `#tooth` mutation verification.
- `GROUNDING.md` — Byte-level format decoders, cryptographic digests, log replay, and physical/silicon semantic models.
- `PLAN.md` — Subsystem boundaries, dataflow pipelines, and verification gates.
- `HARDWARE.md` — RTL, Yosys LEC, HVM lowering, FABulous MAC8 bitstream readback, Square hypergraphs, WGSL, Vulkan memory scopes, RDNA2 binary validation, Blelloch collectives, and Goldilocks NTT.
- `PHYSICAL.md` — Certified interval/Taylor/SOS/hybrid analysis, `devsim-dd1d@1` Sky130 diode drift-diffusion, `cam-gouge@1` CNC toolpath verification, and SDR FT8 receiver proofs.
- `SILICON-ELABORATOR.md` — Lean kernel checking and elaboration nodes lowered to `Obend` books and RTL (`Obend.Lower.LeanKernel`, `Obend.Lower.Proofs.SiliconKernel`).
- `QUALIFICATION-AND-SILICON-LEAN.md` — Trust base qualification, `#tooth` falsifiability, `#assert_axioms_tree`, and `#docs_census`.
- `DEOS-CONTRACTS-CONSENSUS.md` — Durable `Vault` state, `Form` membranes, `Transport`, `Retention`, `Reasons`, `Ledger`, `Judge.Genealogy`, and `SimplexProtocol` / `SimplexTrace`.
- `NEXT-MATHEMATICA.md` — Structured `.obnb` documents, `Doc.Structured` lossless projections, certified symbolic algebra (`AutoCert`), and interactive FFI sessions.
