# Obend Technical Design

This document specifies the concrete data types, typing judgments, operational semantics, storage invariants, hardware compilers, and host FFI boundaries implemented in `lean/Obend` and `crates/`.

---

## 1. Core Calculus and Extrinsic Graded Row Typing

### 1.1 Core Term Syntax (`lean/Obend/Core/Term.lean`)

`Obend.Core.Term` defines the untyped runtime and elaboration core using de Bruijn indices (`bound`), synthesis holes (`hole`), first-class open-recursive prototypes (`prototype`, `specification`, `mix`, `reflect`, `metadata`, `project`), row-polymorphic records and variants (`record`, `extend`, `get`, `split`, `inject`, `case`), and delimited effectful computations (`perform`, `done`).

Arithmetic, comparison, bitwise, and Q32 fixed-point operations are represented by `Obend.Core.Term.Primitive`:

```lean
inductive Primitive where
  | add
  | multiply
  | equal
  | conjunction
  | labelEqual
  | subtract
  | divide
  | less
  | lessEqual
  | modulo
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | lshr
  | ashr
  | slt
  | qmul32
```

The term syntax `Obend.Core.Term.Term` has twenty-five constructors:

```lean
inductive Term where
  | hole (index : Nat)
  | bound (index : Nat)
  | lam (body : Term)
  | app (function : Term) (argument : Term)
  | mix (extension : Term) (base : Term)
  | fix (body : Term)
  | specification (body : Term)
  | prototype (metadata : Term) (body : Term)
  | reflect (target : Term)
  | metadata (target : Term)
  | project (target : Term)
  | nat (value : Nat)
  | boolean (value : Bool)
  | label (value : String)
  | binary (primitive : Primitive) (left : Term) (right : Term)
  | extend (name : String) (value : Term) (rest : Term)
  | record (fields : List (String × Term))
  | get (target : Term) (name : String)
  | ifZero (scrutinee : Term) (whenZero : Term) (whenSucc : Term)
  | inject (tag : String) (payload : Term)
  | case (scrutinee : Term) (arms : List (String × Term))
  | ifBool (scrutinee : Term) (whenTrue : Term) (whenFalse : Term)
  | perform (plan : Term)
  | done (value : Term)
  | split (target : Term) (names : List String) (body : Term)
```

Operational execution is defined by the heap-and-frame abstract machine in `lean/Obend/Core/Machine.lean` (`RuntimeValue`, `Closure`, `Cell`, `Frame`, `Control`, `State`, `Limits`, `Suspension`, `run`) and its fast mirror in `lean/Obend/Core/MachineFast.lean`. Effectful `perform` expressions suspend cleanly at top-level yield boundaries (`perform_yields`) and are refused inside thunk-update frames (`perform_under_update_refused`), preserving single-shot heap invariants across resumption (`resume_requires_yield`, `resume_keeps_heap_and_stack`).

### 1.2 Graded Quantities, Reuse Modes, and Row Types (`lean/Obend/Core/Ty.lean`)

Typing is **extrinsic**: `Term` carries no type annotations, while `AnnotatedTerm` (`lean/Obend/Core/Check.lean`) supplies side-table `Annotations` and equi-recursive `Assumptions` to the bidirectional checker (`lean/Obend/Core/Bidirectional.lean`), erasing cleanly back to `Term` (`checked_erasure`).

Variable usage and closure invocation multiplicity are governed by `Obend.Core.Ty.Quantity` and `Obend.Core.Ty.Reuse`:

```lean
inductive Quantity where
  | erased
  | affine
  | linear
  | unrestricted

inductive Reuse where
  | once
  | reusable
```

- `Quantity.fits` checks exact usage counts (`0` for `erased`, `≤ 1` for `affine`, `= 1` for `linear`, arbitrary for `unrestricted`).
- `Quantity.agrees` (`branchesAgree`) requires control-flow arms (`ifZero`, `ifBool`, `case`) to consume every linear binding identically while allowing affine/unrestricted slack.
- `reusableCaptures` (`reusable_lambda_capture_rule`) forbids a `Reuse.reusable` lambda from capturing `linear` or `affine` context bindings, preventing aliasing of linear capabilities (`Ty.custody`) or suspended computations (`computation_not_shareable`).

Types and rows share a single inductive syntax `Obend.Core.Ty.Ty`:

```lean
inductive Ty where
  | natural
  | label
  | boolean
  | variable (index : Nat)
  | arrow (reuse : Reuse) (quantity : Quantity) (domain : Ty) (codomain : Ty)
  | emptyRow
  | field (name : String) (member : Ty) (rest : Ty)
  | specification (row : Ty)
  | prototype (metadata : Ty) (row : Ty)
  | custody (content : Ty)
  | variant (row : Ty)
  | computation (plan : Ty) (response : Ty) (result : Ty)
```

Rows support both canonical finite normalization (`Ty.canonical`, `Ty.canonical_canonical`, `finite_field_commute`, `finite_field_shadow` in `lean/Obend/Core/FiniteRowLaws.lean`) and Amadio–Cardelli equi-recursive row bounds (`Assumptions`, `lookupV_iff`, `isRowV_iff` in `lean/Obend/Core/Check.lean`, plus tree/bisimulation equivalence in `lean/Obend/Core/EquiRecursiveAgreement.lean` and `lean/Obend/Core/FiniteBisimulation.lean`).

`Obend.Core.Bidirectional` (`checkAgainst`, `infer`) rejects unfilled holes (`elaborate_refuses_hole`) and proves soundness into the typing judgment (`checkAgainst_sound`), which in turn guarantees bounded machine execution without internal or wrong-value refusals (`step_preserves_typing`, `steps_preserve_typing`, `typed_stepRaw_preserved`, `checked_runBounded_no_refusal`).

---

## 2. Contextual `Slot` / `Intention` and `Leaf` Specialization

### 2.1 `Slot`, `Intention`, and Indexed Protocols

- `Obend.Slot.Slot` (`lean/Obend/Slot.lean`) pairs `supports : Cand → List Fact` with `judge : Cand → Bool`, proving `usable_iff`, `read_usable_supports`, and `read_blocked_exact`.
- `Obend.Intention` (`lean/Obend/Intention.lean`) manages stateful pin resolution and renewal (`current_iff_usable`, `stale_iff_blocked`, `renew_repairs`, `stays`).
- `Obend.Slot.Protocol` (`lean/Obend/Slot/Protocol.lean`, `lean/Obend/Slot/Proofs/ProtocolTyping.lean`) models typed multi-party interaction protocols `Prot S Hole A i` with hole substitution, resource envelopes, and handler algebras (`HasProt`, `Open.WF`).

### 2.2 Open-Recursive Prototypes and `Leaf` Compilation

Surface `.obend` packages (`lean/Obend/Spec/Syntax.lean`, `lean/Obend/Spec/Elaborate.lean`, `lean/Obend/Spec/C4.lean`) elaborate C4-linearized prototype layers (`Layer`, `Composition`) into `Core.Term`.

`Obend.Leaf` compiles open-recursive compositions into flat vtables and specialized definition books:
- **Flattening (`lean/Obend/Leaf/Flatten.lean`)**: `flatten_object` and `flatten_sound` prove that a flattened vtable is observationally equivalent (`≈b`) to dynamic `mix` prototype inheritance on closed compositions.
- **Super-Elimination (`lean/Obend/Leaf/Residual.lean`)**: `vtable_clean` and `no_residual_super` guarantee that flattened methods contain zero residual super-layer lookups.
- **Book Emission (`lean/Obend/Leaf/Emit.lean`)**: `emit` extracts slotted methods into a `Book` (`LeafDef`, `BookItem`), with `emit_sound` and `book_sound` establishing behavioral equivalence and `emit_of_digest` tying compilation deterministically to `Cshake256` code digests.
- **Futamura Specialization (`lean/Obend/Leaf/Specialize.lean`, `lean/Obend/Leaf/Static.lean`, `lean/Obend/Leaf/Futamura.lean`)**: `dataPinSpecialize` and `specializeBook` inline pinned cross-package values (`link_bequiv_specializeBook`, `specializeBook_member_sound`), guarded by `specSlot` so any mutated upstream pin immediately blocks stale specialized code (`moved_pin_blocks`, `specialized_moved_pin_blocks`).

---

## 3. Patch-Graph Documents (`lean/Obend/Doc`)

`Obend.Doc` models collaborative structured notebooks (`.obnb`) and specifications without line-based merge heuristics:
- **Atom Graph (`lean/Obend/Doc/Graph.lean`)**: A `Graph` stores `AtomId × Content` vertices (`text`, `cite`, `field`, `cell`) and directed causal edges, deciding reachability on closed cones (`beforeB_iff`).
- **Pushout & Keyed Cell Merge (`lean/Obend/Doc/Merge.lean`)**: Graph merges form categorical pushouts (`IsPushout`), while keyed structured cells merge commutatively and idempotently with conflict isolation (`mergeKeyedCells3_idempotent`, `mergeKeyedCells3_commutative`, `mergeKeyedCells3_disjoint_edits_no_conflicts`).
- **Citations (`lean/Obend/Doc/Section.lean`)**: `Cite` tracks byte-range and identity spans across pages, detecting upstream source movement (`SourceMoves`).
- **Lossless Structured Projection (`lean/Obend/Doc/Structured.lean`)**: `StructuredCell` embeds `Core.Data.Data`, hexadecimal footprint pins (`pinsToData`, `pinsOfData`), and optional Merkle receipts (`receiptToData`, `receiptOfData`) into `Content.cell`. `hexToByteArray_byteArrayToHex` closes exact `ByteArray` round-tripping, yielding unconditional `projection_preservation` alongside `stale_pin_invalidates`.

---

## 4. Live Vault, Membranes, Reasons, and Double-Entry Ledger

### 4.1 Log-Replayed Worlds (`lean/Obend/Vault/Replay.lean`)

`Obend.Vault.Replay.World` is the canonical durable state container:
- Every mutation enters as a hash-linked `Turn` (`log_wellLinked`) producing a deterministic `Outcome`; `judge_refuses_duplicate` and `judge_by_identity` prevent replay or forging of turn IDs.
- Current state is defined by replaying the log (`state_eq_replay_log`, `recover_eq_replay_prefix`), and materialized checkpoints are proved equivalent caches (`checkpoint_is_cache`).
- Outstanding and landed obligations persist across crash recovery (`outstanding_kept`, `landed_kept`, `obligations_survive_crash`).

### 4.2 Residual Membranes and Single-Pass Caching (`lean/Obend/Vault/Form.lean`, `lean/Obend/Vault/FormCheck.lean`)

- `Form` partially evaluates page laws (`NExpr.peval`) into residual obligations (`eval_fill_eq_subst_residual`) that cannot read hidden state (`residual_reads_nothing_known`, `hidden_change_invisible_through_form`) or amplify authority (`admit_no_amplification`, `judgeProposal_sound`, `judgeFill_sound`).
- `CheckUnit`, `CheckKey`, and `CheckRecord` (`lean/Obend/Vault/FormCheck.lean`, `lean/Obend/Vault/FormCheckCache.lean`) cache verified law evaluations across checkpoints and fills (`checksOf_records`, `kept_typed`, `rechecked_zero`).

### 4.3 Capability Transport, Retention, and Branch Merge

- **Transport (`lean/Obend/Vault/Transport.lean`)**: Governs cross-vault capability delegation (`Contract`, `Issue`, `Grants`, `Obligation`, `Landing`), proving fresh recapture (`judge_recapture_iff`), continuous custody with no absence window (`handoff_no_absence`), and revocation priority under concurrent merges (`merge_revocation_wins`, `merge_live_comm`).
- **Retention (`lean/Obend/Vault/Retention.lean`)**: Compacts redacted turns out of logs (`Compacts`, `recoverLog`) while preserving state equivalence on retained pages (`state_eq_replay_compacted`, `recover_eq_replay_prefix_compacted`) and refusing redaction of active obligation supports (`forget_refused_when_needed`, `forget_keeps_reasons` in `Replay.lean`).
- **Vault Merge (`lean/Obend/Vault/Merge.lean`)**: Reconciles divergent vault histories (`sharedPrefix`, `mergeFront`, `keepPending`, `mergeVault`) with agreement theorems (`plan_agrees`, `mergeVault_agrees`).

### 4.4 Van Gelder 3-Valued `Reasons` and Double-Entry `Ledger`

- **Justification (`lean/Obend/Reasons.lean`)**: Computes 3-valued well-founded `Status` (`supported`, `undefined`, `unsupported`) via `gamma` and `rounds` (`gamma_least`, `rounds_least`), preventing circular self-justification (`no_conclusion_from_cycles`) and requiring grounded support for actions (`action_needs_support`).
- **Ledger (`lean/Obend/Ledger/Register.lean`, `lean/Obend/Ledger/Vault.lean`, `lean/Obend/Ledger/Report.lean`, `lean/Obend/Ledger/Commit.lean`)**: Double-entry `Posting` and `Journal` registers enforce balance conservation (`conserved`, `net_conserved`, `vault_conserved`), account closure permanence (`closed_forever`), exact reversal cancellation (`reversal_cancels`), and `trial-balance@1` audit coverage (`trial_balance_covers`, `trial_balance_binds`, `posting_receipt_checks`).

---

## 5. Judges, Consensus, and Verified Hardware / GPU Stack

- **Certificate Registry (`lean/Obend/Judge.lean`, `lean/Obend/Judge/Class.lean`)**: Uniform `Judge` and byte-level `Format` registry (`lrat@1`, `interval-bound@1`, `taylor-model@1`, `groebner-ideal@1`, `hybrid-flowpipe@1`, `sos-lyapunov-cbf@1`, `simplex-trace@1`, `cam-gouge@1`, `devsim-dd1d@1`, `judge-succession@1`, `rtl-synth@1`).
- **Judge Genealogy (`lean/Obend/Judge/Genealogy.lean`)**: Models self-governing judge upgrades (`Habitat`, `Gate`, `Method`, `LobCost`) with `succession_sound`, `run_floors`, `run_noninterference`, and Gödel–Löb trust-floor accounting (`lob_labelled`, `lob_cost_necessary`).
- **Simplex Consensus (`lean/Obend/Consensus/SimplexProtocol.lean`, `lean/Obend/Consensus/SimplexTrace.lean`)**: Proves quorum intersection (`honest_quorum_intersection`), notarized uniqueness (`notarized_block_unique`), prefix consistency (`finalized_consistent`), slashing accountability (`accountable`), and wire-format trace verification (`checkTrace_sound`, `simplexTraceFormat`).
- **Hardware & GPU (`lean/Obend/Hardware`, `lean/Obend/Apps`)**: Covers SMT Yosys LEC (`lecScript_unsat_of_step`), HVM interaction-net lowering (`lowerBookToHvm_sound`), FABulous iCEstick MAC8 bitstream readback (`mac8_fabric_realizes_module`), Square hypergraph compilation (`compileHypergraphToRtl_sound`, `rtl_eq_gpu`), WGSL kernel emission (`Obend.Hardware.Gpu`), Vulkan memory-scope presheaves (`allowed_iff_glues`), RDNA2 ISA validation (`certifyDump_sound`, `certifySchedule_sound`), Blelloch collectives (`scanGroup_value`, `reduceGroup_value`), Stockham Goldilocks NTT (`encoded_dft_of_uploads`), Sky130 drift-diffusion (`ddFormat_sound`), and gouge-free CAM (`fidget_toolpath_no_gouge_continuous`).

---

## 6. FFI Session Bridge and Rust Workspace

`lean/Obend/FFI/Bridge.lean` exposes a thread-safe handle table (`SessionState`) over the C ABI (`lean/c/obend_bridge.c`) consumed by `crates/obend-ffi`:
- **Live Vault Backing**: Each `SessionState` wraps a real `Obend.Vault.Replay.Session`. `turnProposeCore` and `turnCommitCore` decode canonical turn wire bytes and commit them through `Log.Session.admit`, preserving log reachability (`turnCommitCore_preserves_reachable`).
- **Fail-Closed Cell & Witness Evaluation**: `evalCellCore` elaborates `.obend` source through `Obend.Spec` and refuses unknown cell formats (`evalCellCore_non_obend_refused`); `projectHardwareCore` verifies `TurnWitness` envelopes against `Obend.Judge.registry` (`projectHardwareCore_sound`, `projectHardwareCore_non_witness_refused`); committed Merkle receipts verify against `committedRoots` (`verifyReceiptCore_sound`).
- **Host Libraries**:
  - `crates/obend-ffi`: Safe `Session` and `Receipt` wrappers tested end-to-end against `libobend_Obend.so`, including `simplex-trace@1` kernel trace verification (`crates/obend-ffi/tests/simplex_trace_kernel.rs`).
  - `crates/obend-sandbox`: Sandboxed process execution (`GrainExecutor`, `LaunchGate`, `CpuMeter`, Linux `bwrap`, macOS SBPL) with SHA-256 content addressing.
  - `crates/obend-gui`: Streaming `.vcd` waveform, `.stl` triangle mesh, and `.ngc` G-code parsers (`crates/obend-gui/src/apps.rs`) plus an asynchronous PIDE elaboration client (`ObendSession` in `crates/obend-gui/src/evaluator.rs`).
