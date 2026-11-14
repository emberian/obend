# Grounding: From Untrusted Bytes to Kernel-Checked Meaning

A formal theorem protects a running system only to the extent that its statement governs the actual bytes arriving over sockets, files, and hardware buses. Obend grounds abstract semantics to concrete representations across four boundaries: wire-format decoders, cryptographic digests, log-replayed sharded vaults, and physical/silicon enclosure models.

---

## 1. Byte-Level `Judge.Format` Decoders and Refusal Witnesses

In `lean/Obend/Judge/Class.lean` and `lean/Obend/Judge.lean`, a registered certificate checker (`Format`) is not merely an abstract function `Obj → Cert → Verdict Clause`; it must supply concrete wire parsers for both the problem statement and the witness:

1. **Input-Reading Wire Decoders**: `Format.checkBytes` parses untrusted `objBytes` and `certBytes` before invoking the graded `Judge` (including round-trip `Format.ofCodec` combinators in `lean/Obend/Tactic/Compositional.lean`). Every registered format in `Obend.Judge.registry` pairs a real structural decoder with a concrete negative refusal theorem on a planted invalid input.
2. **Pinpointed Refusals**: Checkers return `Verdict.refused clause path` rather than a bare `false`, identifying the exact violated clause or proof step:
   - `Obend.Judge.Lrat` (`lean/Obend/Judge/Lrat.lean`): `checkText_sound` establishes `Unsat F` from DIMACS + LRAT text, while `planted_refused` proves `check 1 contradiction planted = .refused .noConflict [0]`.
   - `Obend.Elab.AutoCert` (`lean/Obend/Elab/AutoCert.lean`, `lean/Obend/Elab/AutoCertTaylorSound.lean`): `checkGroebnerJudge_sound`, `taylorModelJudge_semantic`, and `badGroebnerCert_refused` bind polynomial ideal/Positivstellensatz and Taylor-model enclosures to `CanonicalRat` evaluation.
   - `Obend.Judge.Netting` & `Obend.Judge.TranscriptPolicy` (`lean/Obend/Judge/Netting.lean`, `lean/Obend/Judge/TranscriptPolicy.lean`): `checkNetting_sound` and `settleNetting_agrees_with_gross` verify `netting@1` multilateral obligation compression, while `tlsnTranscriptPolicy_sound` and `badTlsn_refused` enforce selective-disclosure DFA policy invariants across redacted spans.
   - `Obend.Run.HyperLaw` (`lean/Obend/Run/HyperLaw.lean`): `glEquilibriumFormat` (`gl-equilibrium@1`) parses JSON modal rule bases and verifies Gelfond–Lifschitz stable equilibria via `Obend.Reasons.gamma` (`checkGLEquilibrium_sound`, `self_defeating_modal_refused_on_p`).
   - `Obend.Consensus.SimplexTrace` (`lean/Obend/Consensus/SimplexTrace.lean`): `checkTrace_sound` and `checkStep_equivocation_checks` validate `simplex-trace@1` wire transcripts and produce verifiable `SlashingReceipt` evidence on equivocation.
   - `Obend.Hardware.Device.DriftDiffusion` (`lean/Obend/Hardware/Device/DriftDiffusion.lean`): `ddFormat_sound` and `bad_refused_doping` verify `devsim-dd1d@1` semiconductor carrier-continuity and Poisson residuals.
   - `Obend.Hardware.GeometryCAM` (`lean/Obend/Hardware/GeometryCAM.lean`): `camGougeFormat` and `camGougeBad_refused` verify `cam-gouge@1` swept-tool clearance against functional-representation (`FRepExpr`) stock geometry.

---

## 2. Content Addressing, Canonical Digests, and Dual-Track Commitments

Identity across packages, specialization pins, document cells, and vault logs rests on domain-separated `cSHAKE256` (`lean/Obend/Digest/Cshake256.lean`, `lean/Obend/Digest/HashBytes.lean`) paired with post-quantum lattice commitments (`lean/Obend/Crypto/DualSpine.lean`):

- **Spec vs. Fast Keccak Seam (`lean/Obend/Digest/Cshake256/Spec.lean`, `lean/Obend/Digest/Cshake256/Fast.lean`, `lean/Obend/Digest/Cshake256/Seam.lean`)**: A reference sponge specification is paired with a word-level implementation across an explicit seam.
- **Canonical Term & Type Encoding (`lean/Obend/Core/Code.lean`, `lean/Obend/Core/Digest.lean`)**: Terms, types, and `Core.Data.Data` values serialize canonically prior to hashing, allowing `Leaf` book compilation (`emit_of_digest` in `lean/Obend/Leaf/Emit.lean`) and `Doc.Structured` cell pins (`projection_preservation` in `lean/Obend/Doc/Structured.lean`) to bind directly to collision-resistant digests.
- **Dual-Track Hash + Module-SIS Spine (`lean/Obend/Crypto/DualSpine.lean`, `lean/Obend/Crypto/SameOpening.lean`)**: `canopyAjtaiDualPCS` binds multilinear polynomial witnesses simultaneously to Merkle hash roots and Goldilocks Ajtai commitments (`canopyAjtaiDualPCS_sound_of_hash_or_sis`, `verifySameOpening_sound`).

---

## 3. Durable State Grounded in Append-Only Replay and Sharded Buckets

Both persistent vaults (`lean/Obend/Vault/Replay.lean`, `lean/Obend/Vault/Log.lean`, `lean/Obend/Vault/WorldTree.lean`) and interactive FFI sessions (`lean/Obend/FFI/Bridge.lean`) derive their in-memory world from an append-only turn log:

- **Single Source of Truth & Sharded Persistence**: `state_eq_replay_log` proves that the live store of a `Replay.World` equals the fold of its hash-linked log (`log_wellLinked`), `checkpoint_is_cache` ensures snapshots never introduce unlogged state, and `Obend.Vault.ChunkedWorld` (`FastCodec.decodeExactArray_eq`, `dig_eq_unbe_logHashArray`, `writeShardedWorld`, `loadShardedWorld`) grounds O(1)-bucket world snapshots to exact `ByteArray` round-trips and 256-bit digest anchors.
- **Thread-Pinned FFI Session Binding**: `Obend.FFI.SessionState` (`lean/Obend/FFI/Bridge.lean`, `!Send` `ObendSession` in `crates/obend-ffi/src/session.rs`) embeds `Obend.Vault.Replay.Session`. `turnCommitCore_preserves_reachable` proves that every FFI commit advances the underlying `Replay.World` along a valid `Log.Session.admit` step, and `verifyReceiptCore_sound` checks 56-byte Merkle receipts exclusively against `committedRoots`.

---

## 4. Silicon, GPU, and Physical Grounding

Hardware claims are anchored to vendor-consumable or hardware-extracted artifacts rather than internal intermediate ASTs alone:

- **RTL Synthesis & SMT Equivalence (`lean/Obend/Hardware/YosysLec.lean`, `lean/Obend/Apps/FocHil.lean`)**: `lecScript_holds_iff` and `lecScript_unsat_of_step` tie `RtlModule` cycle semantics (`stepModuleRegs`, including `focHilSequentialRtlModule` emitted by `obend-emit-sv foc-hil`) directly to the SMT-LIB2 miter queries discharged during Yosys logic equivalence checking.
- **FPGA Configuration Readback (`lean/Obend/Hardware/Fabulous/Readback.lean`, `lean/Obend/Hardware/Fabulous/Tile.lean`, `lean/Obend/Hardware/Fabulous/Mac8.lean`)**: `pip_sound`, `Cert.required_ofF`, and `mac8_fabric_realizes_module` ground gate/flop netlists directly in physical FABulous tile configuration bits for the iCEstick MAC8 design.
- **RDNA2 ISA Binary Validation (`lean/Obend/Hardware/Gpu/Rdna2/Decode.lean`, `lean/Obend/Hardware/Gpu/Rdna2/Certified.lean`, `lean/Obend/Hardware/Gpu/Rdna2/Schedule.lean`)**: Decodes raw AMD RDNA2 machine-instruction encodings (`Insts`) and proves equivalence against `ArrayGraph`, workgroup block kernels, and multi-dispatch schedules (`certifyDump_sound`, `certifyBlockDump_sound`, `certifySchedule_sound`).
- **Host Confinement (`crates/obend-sandbox`)**: External synthesis, solver, and simulation processes execute under `GrainExecutor`, `LaunchGate`, and `CpuMeter` confinement (Linux `bwrap` namespaces and macOS Seatbelt SBPL profiles) with SHA-256 input/output pinning.
