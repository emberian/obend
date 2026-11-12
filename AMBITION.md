# Ambition: One Typed, Certificate-Carrying Substrate

Obend unifies four concerns that conventional software stacks split across incompatible languages and unverified glue:

1. **Extensible, resource-safe computation** (`lean/Obend/Core`, `lean/Obend/Leaf`, `lean/Obend/Spec`, `lean/Obend/Law`): open-recursive prototypes and specifications checked by an extrinsic graded/linear bidirectional type system over canonical and equi-recursive rows.
2. **Local-first structured documents** (`lean/Obend/Doc`): Pijul-style patch graphs where prose, citations, key-value fields, and typed code/certificate quotation cells merge commutatively and track fine-grained footprint pins.
3. **Append-only state, authorization, and consensus** (`lean/Obend/Vault`, `lean/Obend/Reasons`, `lean/Obend/Ledger`, `lean/Obend/Consensus`): crash-recoverable worlds reconstructed by deterministic log replay, governed by residual capability membranes, 3-valued non-monotonic justification, conserved double-entry registers, and accountable Byzantine finality traces.
4. **Verified silicon, GPU, and physical artifacts** (`lean/Obend/Hardware`, `lean/Obend/Apps`, `lean/Obend/Lower`): RTL synthesis equivalence, FPGA bitstream readback, RDNA2 machine-code validation, workgroup collectives, finite-field NTTs, semiconductor drift-diffusion enclosures, and gouge-free CNC toolpaths checked by total Lean 4 judges.

---

## Core Engineering Commitments

### 1. External Solvers Propose; Total Kernel Judges Dispose

Untrusted external tools — SAT solvers emitting LRAT proofs, computer algebra engines proposing Gröbner cofactors or sum-of-squares Gram decompositions, device simulators solving 1D Poisson/drift-diffusion grids, or compilers emitting RDNA2 machine code and FPGA bitstreams — run outside the trusted computing base inside OS sandboxes (`crates/obend-sandbox`).

Every artifact crossing back into Obend enters through a registered `Obend.Judge.Format` (`lean/Obend/Judge.lean`, `lean/Obend/Judge/Class.lean`):
- Wire decoders parse untrusted bytes into typed query and certificate structures and fail closed on malformed or under-constrained inputs.
- Total checkers return `Verdict.ok`, `Verdict.refused clause path` (pinpointing the exact violated obligation), or `Verdict.uncovered`.
- Every format carries both a soundness theorem (`Format.checkBytes_sound`) and a concrete refusal proof on a planted invalid certificate.

### 2. Late Binding Without Stale Silent Drift

Across programs (`lean/Obend/Leaf/Specialize.lean`), citations (`lean/Obend/Doc/Section.lean`), structured cells (`lean/Obend/Doc/Structured.lean`), vault proposals (`lean/Obend/Vault/Form.lean`), and architecture documentation (`lean/Obend/Tactic/DocsCensus.lean`), Obend instantiates a single dependency abstraction: `Obend.Intention` and `Obend.Slot` (`lean/Obend/Intention.lean`, `lean/Obend/Slot.lean`).

Every cached specialization, quotation receipt, or capability membrane explicitly lists its `supports`. When upstream state mutates any supporting fact, `Slot.read` transitions deterministically from `Reading.usable` to `Reading.blocked`, naming the exact invalidated supports (`read_blocked_exact`, `moved_pin_blocks`, `stale_pin_invalidates`).

### 3. Replayable State With Provable Conservation and Right-to-Forget

`Obend.Vault.Replay.World` (`lean/Obend/Vault/Replay.lean`) eliminates mutable shadow state:
- Live state equals the fold of the hash-linked turn log (`state_eq_replay_log`), while snapshots act strictly as verified caches (`checkpoint_is_cache`).
- Redacting sensitive payloads via `Obend.Vault.Retention` preserves hash linkage and replay equivalence on surviving pages (`state_eq_replay_compacted`) while refusing erasure of facts still supporting active obligations (`forget_refused_when_needed`).
- Value transfers lower to balanced postings in `Obend.Ledger.Register` and `Obend.Ledger.Vault`, conserving net balances across every admitted turn (`vault_conserved`, `trial_balance_binds`).

### 4. End-to-End Semantics Down to Gates, Wavefronts, and Toolpaths

Hardware and physical compilation targets share the same verification standard as software evaluation:
- `Obend.Hardware.Square` lowers strict open hypergraphs to both RTL modules and GPU kernels with proved observational agreement (`rtl_eq_gpu`, `pipelined_eq_comb`).
- `Obend.Hardware.Fabulous.Mac8` and `Obend.Hardware.Fabulous.Readback` verify a physical iCEstick FABulous FPGA bitstream from tile switch-matrix configuration bits up to multi-cycle MAC8 register-transfer behavior (`mac8_fabric_realizes_module`).
- `Obend.Hardware.Gpu.Rdna2.Certified` validates disassembled AMD RDNA2 ISA binaries directly against `ArrayGraph` and workgroup block programs (`certifyDump_sound`, `certifyBlockDump_sound`).
- `Obend.Hardware.Device.DriftDiffusion` and `Obend.Hardware.GeometryCAM` enclose continuous semiconductor and geometric invariants using exact `CanonicalRat` interval arithmetic (`ddFormat_sound`, `fidget_toolpath_no_gouge_continuous`).
