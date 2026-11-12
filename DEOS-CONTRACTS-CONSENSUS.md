# Vault Durability, Capability Membranes, Ledger Conservation, and Simplex Consensus

This document specifies Obend's distributed and persistent state stack: log-replayed vaults (`lean/Obend/Vault`), non-monotonic justification (`lean/Obend/Reasons.lean`), double-entry accounting (`lean/Obend/Ledger`), self-judged upgrades (`lean/Obend/Judge/Genealogy.lean`), and Byzantine fault-tolerant consensus (`lean/Obend/Consensus`).

---

## 1. Durable Worlds by Log Replay (`lean/Obend/Vault/Replay.lean`)

`Obend.Vault.Replay.World` models a node's persistent store as a deterministic projection of an append-only, hash-chained turn log (`lean/Obend/Vault/Log.lean`, `lean/Obend/Vault/LogBytes.lean`, `lean/Obend/Vault/SegmentLog.lean`):

- **Replay Equivalence**: `state_eq_replay_log` proves that the in-memory store equals the fold of its committed turns; `recover_eq_replay_prefix` proves crash recovery reconstructs the exact prefix of durable turns; `checkpoint_is_cache` proves checkpoints never diverge from log replay.
- **Turn Identity & Deduplication**: `log_wellLinked` enforces cryptographic parent linkage, while `judge_refuses_duplicate` and `judge_by_identity` reject duplicate or colliding turn submissions.
- **Crash-Safe Obligations**: `outstanding_kept`, `landed_kept`, and `obligations_survive_crash` prove that pending obligations created by admitted turns cannot vanish across restarts, and `late_correction_refused` prevents retroactive mutation of settled obligations.

---

## 2. Residual Authorization Membranes (`lean/Obend/Vault/Form.lean`, `lean/Obend/Vault/FormCheck.lean`)

Multi-party transactions frequently depend on page laws that reference private fields of a vault alongside public parameters supplied by a counterparty. `Obend.Vault.Form` compiles page laws into capability **membranes**:

1. **Partial Evaluation (`NExpr.peval`)**: Evaluates known vault fields out of a page's law expression, emitting a residual `Form` with typed holes (`eval_subst_peval`, `eval_fill_eq_subst_residual`, `abstract_then_fill`).
2. **Confidentiality**: The residual `Form` contains zero references to hidden state (`residual_reads_nothing_known`, `capture_hidden_absent`), and mutating hidden fields cannot alter residual evaluation (`hidden_change_invisible_through_form`).
3. **Gate-First Atomic Admission & Non-Amplification**: `judgeProposal_gate_first` and `judgeProposal_atomic` ensure guard checks precede state transitions; `admit_no_amplification`, `admitFill_no_amplification`, `admit_hidden_untouched`, `admit_conserves_written`, and `admit_conserves_total` prove authority and value conservation across both proposal and fill admission (`judgeProposal_sound`, `judgeFill_sound`).
4. **Single-Pass Verification (`lean/Obend/Vault/FormCheck.lean`, `lean/Obend/Vault/FormCheckCache.lean`)**: Compiles residual checks into typed `Obend.Core.Term` obligations (`judge_runs_checked`, `judged_typed`, `coreTerm_evaluates`) and caches `CheckUnit` records (`checksOf_records`, `kept_typed`) so unchanged units are never re-evaluated (`rechecked_zero`).

---

## 3. Capability Transport, Right-to-Forget, and Vault Merging

- **Cross-Vault Transport (`lean/Obend/Vault/Transport.lean`)**: `Contract`, `Issue`, `Grants`, `Obligation`, and `Landing` govern transferring authority and obligations across vaults. `recapture` re-pins fresh display and effect versions (`display_fresh_iff`, `effect_fresh_display_fresh`, `judge_recapture_iff`); `transport_sound` and `transport_continues_iff` characterize valid landings; `handoff_no_absence` proves that custody is never simultaneously absent from both source and destination; `merge_revocation_wins` and `merge_live_comm` ensure concurrent revocations dominate stale grants.
- **Retention & Log Compaction (`lean/Obend/Vault/Retention.lean`)**: `Compacts` and `recoverLog` allow redacting expired or sensitive page payloads while preserving hash-chain verification and state equivalence on retained pages (`replay_compacted`, `state_eq_replay_compacted`, `recover_eq_replay_prefix_compacted`). `forget_refused_when_needed` and `forget_keeps_reasons` (`lean/Obend/Vault/Replay.lean`) refuse erasure when a page still backs an active obligation or live justification.
- **Divergent Vault Merge (`lean/Obend/Vault/Merge.lean`)**: `sharedPrefix`, `mergeFront`, `keepPending`, and `mergeVault` reconcile forked vault logs while preserving pending obligations and agreeing on common non-conflicting pages (`keepPending_histories`, `plan_agrees`, `mergeVault_agrees`).

---

## 4. Van Gelder 3-Valued Justification (`lean/Obend/Reasons.lean`)

`Obend.Reasons` governs standing policies, revocable delegations, and defeasible claims via Van Gelder's alternating fixpoint over general logic programs (`Rule`, `Program`):

```lean
inductive Status where
  | supported
  | undefined
  | unsupported
```

- `gamma_least` and `rounds_least` establish the well-founded model `wf`.
- `no_conclusion_from_cycles` prevents circular rules from manufacturing `Status.supported`.
- `survives_one_support`, `defeat_only_by_evidence`, `propose_keeps_judgment`, `wf_local`, and `action_needs_support` ensure incremental stability and require every admitted action to carry non-circular support (`justified_needs_support`).

---

## 5. Double-Entry Ledger and Judge Genealogy

### 5.1 Conserved Registers and Trial Balance (`lean/Obend/Ledger`)

- **Register Conservation (`lean/Obend/Ledger/Register.lean`, `lean/Obend/Ledger/Vault.lean`, `lean/Obend/Ledger/Commit.lean`)**: `Reg`, `Posting`, `Row`, and `Journal` enforce balanced debits and credits (`conserved`, `net_conserved`, `vault_conserved`), permanent account closure (`closed_forever`), kind-level balance laws (`kindLaw_holds`, `kindLaw_balanced`), and exact reversal cancellation (`reversal_cancels`).
- **Audit Reporting (`lean/Obend/Ledger/Report.lean`)**: `tb` and `tbFormat` (`trial-balance@1`) aggregate account registers with completeness and binding theorems (`trial_balance_covers`, `trial_balance_binds`, `posting_receipt_checks`).

### 5.2 Judge Genealogy (`lean/Obend/Judge/Genealogy.lean`)

`Habitat`, `Gate`, `Method` (`eval`, `lemma`), `Exec`, and `LobCost` formalize constitutional upgrades of `Obend.Judge` checkers (`judge-succession@1`):
- `succession_sound` and `run_floors` guarantee that no judge upgrade weakens habitat floor invariants.
- `cage_not_inhabitant` and `run_noninterference` isolate sandboxed candidate runs from committed state, while `revert_admitted` and `revert_obligation` guarantee rollback paths.
- `lob_labelled` and `lob_cost_necessary` enforce explicit accounting whenever a successor judge relies on a stronger proof-theoretic floor.

---

## 6. Simplex Byzantine Consensus and Trace Verification (`lean/Obend/Consensus`)

`lean/Obend/Consensus/SimplexProtocol.lean` and `lean/Obend/Consensus/SimplexTrace.lean` formalize the Simplex BFT consensus protocol and expose a kernel-verified wire format (`simplex-trace@1`):

- **Quorum Safety & Accountable Slashing (`lean/Obend/Consensus/SimplexProtocol.lean`)**:
  - Under $< n/3$ Byzantine faults, `honest_quorum_intersection` proves any two $2f + 1$ quorums intersect at an honest replica.
  - `notarized_block_unique`, `finalized_no_dummy`, `finalized_prefix_of_notarized`, `finalized_consistent`, and `fin_cert_unique_per_height` prove safety across heights and views.
  - When ≥ $n/3$ Byzantine replicas equivocate to finalize conflicting blocks, `accountable` extracts cryptographic equivocation witnesses (`SlashingReceipt`).
- **Wire-Format Trace Judge (`lean/Obend/Consensus/SimplexTrace.lean`, `crates/obend-ffi/tests/simplex_trace_kernel.rs`)**:
  - `checkStep_sound`, `checkStep_equivocation_checks`, and `checkTrace_sound` verify serialized `Entry` transcripts via `simplexTraceFormat` (`simplex-trace@1` in `Obend.Judge.registry`), exercised across the Rust FFI boundary in `crates/obend-ffi/tests/simplex_trace_kernel.rs`.
