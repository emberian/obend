# Qualification Methodology and Trust Base Accounting

High-assurance verification fails in practice not because the underlying proof assistant is unsound, but because specifications drift from deployed code, decoders ignore untrusted input bytes, vacuous hypotheses make theorems hold trivially, or documentation cites nonexistent proofs.

Obend enforces four machine-checked qualification gates across `lean/Obend` and `crates/` to close each failure mode.

---

## 1. Trust Base Accounting (`lean/Obend/Judge/Class.lean`, `lean/Obend/AssertAxioms.lean`)

Every verified claim in Obend explicitly identifies its trust boundary:

1. **Lean 4 Kernel Foundations (`Obend.AssertAxioms.standard`)**: Propositional extensionality (`propext`), quotient soundness (`Quot.sound`), and classical choice (`Classical.choice`) where used; constructive computational theorems avoid `Classical.choice` wherever decidable reduction suffices.
2. **Axiom Census (`lean/Obend/AssertAxioms.lean`, `lean/Obend/AssertCompiled.lean`, `lean/Obend/Census.lean`)**:
   - `theoremCensus` traverses every exported constant under `Obend`, enforcing the `no_sorry_ax` rule across the module graph.
   - Any theorem relying on Lean's native code-generation reduction (`isCompilerTrust`) is isolated by name and re-verified by `#assert_compiled` (`lean/Obend/AssertCompiled.lean`).
3. **Self-Judged Upgrade Floor (`lean/Obend/Judge/Genealogy.lean`)**: When a node upgrades a registered judge (`judge-succession@1`), `succession_sound` and `lob_cost_necessary` ensure that conservation/safety floors (`run_floors`) continue to hold and any extension of logical trust is explicitly tagged with `LobCost`.

---

## 2. Adversarial Mutation Testing With `#tooth` (`lean/Obend/Tactic/Tooth.lean`)

A theorem of the form `check x = .ok → Valid x` could pass review while `Valid x` was accidentally defined as `True`, or while `check` never inspected a critical field of `x`.

`lean/Obend/Tactic/Tooth.lean` provides the `#tooth` command:
- Given a proved theorem and an adversarial `mutation` of a definition in its dependency cone (e.g., mutating a checker to always return `Verdict.ok`, dropping a linearity check, or swapping wire indices), `#tooth` clones the declaration graph with the mutated body and re-runs the Lean kernel typechecker.
- `#tooth` succeeds **only if the kernel rejects the theorem** under the mutation.
- Dedicated mutation suites in `lean/Obend/Teeth/` and integration tests (`lean/tests/metasystem/FfiTruthfulnessTest.lean`, `lean/tests/metasystem/AutoCertTest.lean`) enforce `#tooth` kills across:
  - Core typing, linearity, row lookup, and garbage collection (`lean/Obend/Teeth/Core/`),
  - Open-recursion flattening and static specialization (`lean/Obend/Teeth/Leaf/`),
  - Law compilation and machine probes (`lean/Obend/Teeth/Law/`, `lean/Obend/Teeth/Spec/`),
  - Lowering and silicon kernel node checking (`lean/Obend/Teeth/Lower/`, `lean/Obend/Teeth/Hardware/`),
  - Vault replay, residual membranes, and FFI session commits (`lean/Obend/Teeth/Vault.lean`, `lean/tests/metasystem/FfiTruthfulnessTest.lean`).

---

## 3. Byte-Boundary and Host Sandbox Qualification

Untrusted bytes and external binaries are isolated at two boundaries:

- **Input-Reading `Judge.Format` Decoders (`lean/Obend/Judge.lean`, `lean/Obend/Judge/Class.lean`)**: Every format in `Obend.Judge.registry` (`lrat@1`, `interval-bound@1`, `taylor-model@1`, `groebner-ideal@1`, `hybrid-flowpipe@1`, `sos-lyapunov-cbf@1`, `simplex-trace@1`, `cam-gouge@1`, `devsim-dd1d@1`, `judge-succession@1`, `rtl-synth@1`) pairs `checkBytes_sound` with a planted bad-certificate refusal theorem (`planted_refused`, `badGroebnerCert_refused`, `camGougeBad_refused`, `bad_refused`).
- **Live FFI Session Truthfulness (`lean/Obend/FFI/Bridge.lean`, `crates/obend-ffi`)**:
  - `evalCellCore` refuses non-`.obend` payloads (`evalCellCore_non_obend_refused`) rather than echoing unverified bytes.
  - `projectHardwareCore` requires a valid `TurnWitness` accepted by `Obend.Judge.registry` (`projectHardwareCore_sound`).
  - `verifyReceiptCore` accepts only 56-byte receipts whose root was genuinely committed via `turnCommitCore` (`verifyReceiptCore_sound`, `verifyReceiptCore_proposed_not_committed_refused`).
- **Sandboxed External Execution (`crates/obend-sandbox`)**: External toolchains execute inside `GrainExecutor` confinement (`LaunchGate` pre-launch checks, `CpuMeter` resource accounting, Linux `bwrap` user/mount/network isolation, and macOS Seatbelt SBPL profiles) with SHA-256 content digests.

---

## 4. Compile-Time Documentation Governance (`lean/Obend/Tactic/DocsCensus.lean`)

Architecture documentation is treated as a formal `Obend.Slot` client rather than unchecked prose:

- `Obend.Tactic.DocsCensus` (`lean/Obend/Tactic/DocsCensus.lean`) instantiates `docIntention` and `docSlot` over `DocEnvWorld` across all thirteen root `.md` files (`canonicalGovernedDocs`).
- `#check_docs_census` and `#docs_census` (`lean/Obend/Census.lean`) verify at compile time that:
  1. Every cited `lean/Obend/...` module or directory path and backticked `crates/...` / `lean/tests/...` repo path exists on disk.
  2. Every backticked `Obend.*` constant, bare snake-case theorem/definition identifier, and qualified member identifier resolves in `Lean.Environment`.
  3. Every fenced `inductive <Name>` code block lists only authentic constructors belonging to a matching `InductiveVal` in `Lean.Environment`.
- `#census_environment` exports the verified constant inventory so vault pages (`lean/Obend/Vault/Page.lean`) enforce the exact same symbol-resolution discipline on user documents.
