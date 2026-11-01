# Obend — Engineering Plan & Workstream Status

> **Current Build**: **437 Lean modules**, **62,167+ package constants** across **437+ build jobs**, **4 Rust crates** (`obend-sandbox`, `obend-ffi`, `obend-gui`, `obend-node`), **`0 sorryAx`**, **`0` custom axioms**.

---

## Part I — Completed Foundation Workstreams (`WS 1` – `WS 17`)

All 17 foundational workstreams from the initial `Obend` roadmap are **complete, mechanized with `0 sorryAx`, and verified with `#tooth` mutation tests**:

| Workstream | Scope | Key Modules | Key Mechanized Theorems ([`METATHEORY.md`](METATHEORY.md)) |
|---|---|---|---|
| **WS 1: Judge & Dated Receipts (`G4`)** | Single gatekeeper `Judge`, multi-slot citations, cSHAKE256 Merkle-dated replay resistance | [`Obend/Judge.lean`](lean/Obend/Judge.lean), [`Obend/Receipt.lean`](lean/Obend/Receipt.lean), [`Obend/Receipt/Merkle.lean`](lean/Obend/Receipt/Merkle.lean) | `certified_sound`, `accepts_cited_sound`, `dated_sound`, `opens_binds` |
| **WS 2: Canonical Code & Quoting (`C1`)** | Version-prefixed binary encoding, hole-free portable `Code Ψ A θ`, observer ladder `≈q ⊆ ≈r ⊆ ≈b` | [`Obend/Core/Code.lean`](lean/Obend/Core/Code.lean), [`Obend/Equiv/Quote.lean`](lean/Obend/Equiv/Quote.lean) | `encodingVersion_binds`, `import_roundtrip`, `import_complete`, `code_noHole`, `observer_ladder` |
| **WS 3: Nominal `#kind` Branding (`C1`, `G2`)** | First-class `Ty.kinded`, `_kind.md` C4 Vault cells, capability-gated reflective mirrors | [`Obend/Core/Nominal.lean`](lean/Obend/Core/Nominal.lean), [`Obend/Kind.lean`](lean/Obend/Kind.lean), [`Obend/Run/Reflect.lean`](lean/Obend/Run/Reflect.lean) | `kinded_refuses`, `kinds_never_agree`, `kind_stale_iff_blocked`, `forged_descriptor_refused` |
| **WS 4: Cost, Demand & Ticks (`G1`)** | Xia least-demand analysis, clairvoyant simulation, tight machine tick bounds | [`Obend/Equiv/Demand.lean`](lean/Obend/Equiv/Demand.lean), [`Obend/Equiv/Cost.lean`](lean/Obend/Equiv/Cost.lean), [`Obend/Core/Proofs/TickCost.lean`](lean/Obend/Core/Proofs/TickCost.lean) | `demand_is_least`, `sim_cv`, `mix_assoc_cost`, `ticks_within_fragment` |
| **WS 5 & WS 15: `Leaf`, `BendTT` & 1st Futamura (`G6`)** | Layer flattening, zero residual vtables, supercombinator emission, affine interaction nets, `specSlot` deopt guards | [`Obend/Leaf/Flatten.lean`](lean/Obend/Leaf/Flatten.lean), [`Residual.lean`](lean/Obend/Leaf/Residual.lean), [`Emit.lean`](lean/Obend/Leaf/Emit.lean), [`BendTT.lean`](lean/Obend/Leaf/BendTT.lean), [`Specialize.lean`](lean/Obend/Leaf/Specialize.lean) | `flatten_sound`, `vtable_clean`, `book_sound`, `book_to_bendtt_sound`, `specialize_choice`, `moved_pin_blocks` |
| **WS 6: Concurrent Runner & Atomic Stitch** | Shared-world ticket exclusivity, crash-safe journal, offline fork/join atomic stitch | [`Obend/Run/Runner.lean`](lean/Obend/Run/Runner.lean), [`Obend/Run/Durable.lean`](lean/Obend/Run/Durable.lean), [`Obend/Run/Fork.lean`](lean/Obend/Run/Fork.lean) | `joint_reachable_ticket_exclusive`, `durable_refines`, `stitch_atomic`, `stitch_double_spend` |
| **WS 7 & WS 9: Surface `.obend`, Law Dials & Repair** | Surface parser/elaborator, 3-mode `LawDial` (`.free`/`.press`/`.locked`), Bellman-Ford multi-field repair synthesis | [`Obend/Spec/LawDial.lean`](lean/Obend/Spec/LawDial.lean), [`Obend/Vault/Law.lean`](lean/Obend/Vault/Law.lean) | `dial_free_confluent`, `demoOr_not_confluent`, `solveLawWitness_sound`, `suggestMultiField_admits` |
| **WS 8: Double-Entry Capability Ledger** | Conserved streaming ledger fold, `trial-balance@1` non-omission coverage, Vault-backed ledger | [`Obend/Ledger/Register.lean`](lean/Obend/Ledger/Register.lean), [`Report.lean`](lean/Obend/Ledger/Report.lean), [`Vault.lean`](lean/Obend/Ledger/Vault.lean) | `conserved`, `net_conserved`, `closed_forever`, `omitted_refused`, `vault_conserved` |
| **WS 10–12: Late-Bound Logic (T1, T2, T3)** | Open-recursive late binding, contextual `≈r` rewriting, disjoint-field framing | [`Obend/Logic/LateBinding.lean`](lean/Obend/Logic/LateBinding.lean), [`Rewrite.lean`](lean/Obend/Logic/Rewrite.lean), [`Frame.lean`](lean/Obend/Logic/Frame.lean) | `late_binding`, `rewrite_sound`, `claim_frame`, `repeated_survives_override` |
| **WS 13: Linear Conservation & `Term.split` (`C2`, `G3`)** | Source `SubjectReduction`, `.linear` step conservation, `Term.split` record destructor, `Join.max` branch accounting | [`Obend/Core/Proofs/SubjectReduction.lean`](lean/Obend/Core/Proofs/SubjectReduction.lean), [`Conservation.lean`](lean/Obend/Core/Proofs/Conservation.lean), [`Aggregate.lean`](lean/Obend/Core/Proofs/Aggregate.lean) | `step_preserves_typing`, `step_conserves_linear`, `machine_split_passes_all`, `splice_typed` |
| **WS 14: Static Impact Cones & Proof Journal** | Kleene 3-valued abstract interpretation, exact change-impact cones, whole-repo proof dependency journal | [`Obend/Analysis/Impact.lean`](lean/Obend/Analysis/Impact.lean), [`Coverage.lean`](lean/Obend/Analysis/Coverage.lean), [`lean/Journal/Journal.lean`](lean/Journal/Journal.lean) | `read3_sound`, `affected_exact`, `unlisted_unchanged`, `verdict_unaffected_iff` |
| **WS 16: `Lower` (Lean 4 Kernel $\to$ `Core4` $\to$ `Leaf` $\to$ RTL)** | Kernel `Expr` lowering, `f.eq_def` recursion, Tait–Girard completeness, `transport@1`, RTL bridge | [`Obend/Lower/Fragment.lean`](lean/Obend/Lower/Fragment.lean), [`Transport.lean`](lean/Obend/Lower/Transport.lean), [`Proofs/Sound.lean`](lean/Obend/Lower/Proofs/Sound.lean), [`Complete.lean`](lean/Obend/Lower/Proofs/Complete.lean), [`Hardware.lean`](lean/Obend/Lower/Proofs/Hardware.lean) | `lower_sound`, `lower_checks`, `lower_complete_ltyped_nat`, `transportTheorem`, `lower_to_rtl_sat_sound` |
| **WS 17: Verified Silicon Stack (`Obend/Hardware/`)** | 26-module RTL-to-GDSII, STA, Place & Route, DRC/LVS, Multiphysics, Photonics, PCB, RF, eFPGA `ReductionMachine` with `ICAP` DPR, 32 `#tooth` checks | [`Obend/Hardware/`](lean/Obend/Hardware/) (26 modules), [`Obend/Teeth/Hardware/SiliconTeeth.lean`](lean/Obend/Teeth/Hardware/SiliconTeeth.lean) | `compileBook_correct`, `automaton_simulates_book`, `dpr_preserves_neighbor_tiles_and_packets`, `dpr_specialized_tile_executes_new_book` |

---

## Part II — Completed Next-Generation Workstreams (`WS 18` – `WS 27`)

All 10 next-generation workstreams (`WS 18`–`WS 27`) from [`NEXT-MATHEMATICA.md`](NEXT-MATHEMATICA.md), [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md), and [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md) are **complete, mechanized with `0 sorryAx`, and verified across the Lean and Rust workspaces**:

### WS 18 (`R1`): Semantic `CellContract`s, Forever-Crowns (`Narrows`), Real Analysis & Bidirectional Lean Tactic Bridge — **COMPLETE**
- **Modules**:
  - [`Obend/Law/Contract.lean`](lean/Obend/Law/Contract.lean): Semantic `CellContract` ($I(\text{old}) \to T(\text{old}, \text{new}) \to I(\text{new})$) and `Narrows newC oldC` monotonic forever-crowns (`narrows_refl`, `narrows_trans`, `relaw_preserves_forever_crown`, `cellContract_step_inductive`), plus backwards-compatible embedding of legacy `Law.Claim`.
  - [`Obend/Analysis/RealAnalysis.lean`](lean/Obend/Analysis/RealAnalysis.lean) & [`Obend/Judge/RealAnalysis.lean`](lean/Obend/Judge/RealAnalysis.lean): Verified rational/dyadic interval arithmetic (`Interval.add_correct`, `Interval.mul_correct`, `evalInterval_correct`), Horner polynomial enclosures, and contraction-mapping fixed-point certificates (`banach_contraction_enclosure`).
  - [`Obend/Lower/Reflect.lean`](lean/Obend/Lower/Reflect.lean) & [`Obend/Tactic/Weave.lean`](lean/Obend/Tactic/Weave.lean): Outward reflection (`reflectTerm` / `reflectTerm_sound`) and Lean 4 tactic suite (`obend_unfold`, `obend_law`, `obend_split`, `obend_tooth`, `byLoweredLean_sound`).

### WS 19 (`R2`): Proof-Carrying Smart Contract Vault, Wide-Pullback Hyperedges, `Seat`s & Certified `drex-clearing@1` — **COMPLETE**
- **Modules**:
  - [`Obend/Vault/Hyperedge.lean`](lean/Obend/Vault/Hyperedge.lean): Multi-slot atomic `VaultTurn` (`reads`, `writes`, `created`, `consumed`, `witnesses`) with `vaultTurn_wide_pullback_sound` and `vaultTurn_conserves_linear_slots`.
  - [`Obend/Ledger/Book.lean`](lean/Obend/Ledger/Book.lean) & [`Obend/Ledger/Seat.lean`](lean/Obend/Ledger/Seat.lean): Multi-commodity linear `Book` conservation and ZoE-style `Seat` offer safety (`zoe_offer_safety`: want-predicate satisfaction or full refund).
  - [`Obend/Judge/Clearing.lean`](lean/Obend/Judge/Clearing.lean): Primal-dual LP certificate checker (`drex-clearing@1`) proving supply conservation, primal/dual feasibility, and zero duality gap (`drex_clearing_optimal_and_conserving`).

### WS 20 (`R3`): DeOS Capability Surfaces, Blinded Projections (`FogOfWar`), `Mandate`s & Sandstorm Grain Confinement — **COMPLETE**
- **Modules**:
  - [`Obend/Vault/Escrow.lean`](lean/Obend/Vault/Escrow.lean) & [`Obend/Vault/Affordance.lean`](lean/Obend/Vault/Affordance.lean): First-class DeOS capability patterns (`SealedEscrow`, `PrepaidLease`, `GatedAffordance`, `PublishGate`) built over `VaultTurn` and `Seat`.
  - [`Obend/Vault/Projection.lean`](lean/Obend/Vault/Projection.lean): Merkle-committed `BlindedVaultView` (`FogOfWar`) proving public `CellContract` satisfaction without revealing blinded private branches (`blinded_projection_non_forgeable`).
  - [`Obend/Vault/Mandate.lean`](lean/Obend/Vault/Mandate.lean) & [`crates/obend-sandbox`](crates/obend-sandbox): Sandstorm-style isolated `Grain` execution (`grain_confinement_sound`), `Powerbox` capability attenuation (`powerbox_attenuation_monotonic`), human-auditable `Mandate` bounds (`mandate_bounds_turn`), and native OS sandboxing (`sandbox-exec` / `bwrap`).

### WS 21 (`R4`): Symbolic `Simplex` BFT, 4-Tier Finality, `EpistemicConsensus` & `Fold.collapse` — **COMPLETE**
- **Modules**:
  - [`Obend/Consensus/Simplex.lean`](lean/Obend/Consensus/Simplex.lean): Symbolic-mode `Simplex` BFT consensus (`PropCert` $2f+1$ notarization, `SkipCert` $2f+1$ dummy-block timeout, `FinCert` $2f+1$ finalization) with `simplex_safety`, `simplex_accountable_safety` (concrete `SlashingReceipt` on any fork), and `simplex_bounded_liveness_after_gst`.
  - [`Obend/Consensus/Epistemic.lean`](lean/Obend/Consensus/Epistemic.lean): Subjective trust-graph weighted `EpistemicConsensus` and `epistemic_sybil_bounded_by_seed_cut`.
  - [`Obend/Consensus/Finality.lean`](lean/Obend/Consensus/Finality.lean) & [`Obend/Fold/Collapse.lean`](lean/Obend/Fold/Collapse.lean): Unified 4-tier finality state machine connecting `LawDial.free` CRDT $\to$ `VaultTurn` disjoint fast-path (`disjoint_turns_commute`) $\to$ `Simplex` BFT $\to$ `EpistemicConsensus` + `Fold.collapse` (`collapse_sound`).

### WS 22 (`R5`): `.obnb` Structured Notebook Cells, Read-Only Silicon Projections & Thin Rust GUI/FFI — **COMPLETE**
- **Modules**:
  - [`Obend/Doc/Structured.lean`](lean/Obend/Doc/Structured.lean) & [`Obend/Vault/HardwareProjection.lean`](lean/Obend/Vault/HardwareProjection.lean): Typed `BlockGraph` `.obnb` notebook cells and read-only projection adapters over `Obend/Hardware/*` (`circuit`, `netlist`, `timing`, `gdsii`, `waveform`, `cellQuote`, `notebookCell`, `proofTree`, `contractBadge`, `clearingLedger`).
  - [`Obend/FFI/Bridge.lean`](lean/Obend/FFI/Bridge.lean), [`lean/c/obend_bridge.c`](lean/c/obend_bridge.c), [`crates/obend-ffi`](crates/obend-ffi), & [`crates/obend-gui`](crates/obend-gui): C-ABI bridge and Rust GUI/CLI shell.

### WS 23 & WS 24: Recursive Inductives, 2nd/3rd Futamura Specialization, 64-Bit `ExprCAM` & Silicon Lean Elaborator — **COMPLETE**
- **Modules**:
  - [`Obend/Lower/Inductive.lean`](lean/Obend/Lower/Inductive.lean): Recursive inductive data model (`IndVal`, `RecRule`, `IndSig`, `LcnfDecl`), constructor-tag packing (`packCtorTag_roundtrip`), structural `matchCtor` (`matchCtor_on_ctor`), and `fromLeanExpr` reflection bridge.
  - [`Obend/Leaf/Futamura.lean`](lean/Obend/Leaf/Futamura.lean): 1st/2nd/3rd Futamura specialization hierarchy (`specializeBook`, `selfSpecializeFlatten`, `compilerGenerator`, `futamura1_sound`, `futamura2_self_specialize_sound`, `futamura3_cogen_deterministic`).
  - [`Obend/Lower/LeanKernel.lean`](lean/Obend/Lower/LeanKernel.lean) & [`Obend/Lower/Proofs/SiliconKernel.lean`](lean/Obend/Lower/Proofs/SiliconKernel.lean): Pure `KLevel`/`KExpr`/`KEnv` Lean 4 kernel (`kernelWhnf`, `kernelIsDefEq`, `kernelInferType`, `kernelCheckDecl`) with general user-defined inductive $\iota$-reduction (`KInductDecl`, `KRecRule`, `kernelWhnf_general_iota_sound`), `Quot.lift` on `Quot.mk` (`kernelWhnf_quot_lift_sound`), live `checkLeanEnvDeclInSilicon`, and end-to-end `ReductionMachine` eFPGA synthesis (`silicon_kernel_check_sound`, `silicon_elab_dpr_reconfig_sound`).
  - [`Obend/Lower/ExprCAM.lean`](lean/Obend/Lower/ExprCAM.lean): 64-bit hardware hash-consed DAG / CAM pool (`PackedNodeWord`, `ExprCAMPool`, `internExpr`, `unintern`) with 1-cycle handle equality (`exprCam_eq_iff_handle_eq`), $O(1)$ `hasLooseBVar` bit-flag soundness (`exprCam_looseBVar_flag_sound`), and lossless round-trip (`intern_unintern_roundtrip`).

### WS 25: Symbolic & Interval Automatic Differentiation, Validated ODE Flowpipes & Rich Viewport Rendering — **COMPLETE**
- **Modules**:
  - [`Obend/Analysis/Diff.lean`](lean/Obend/Analysis/Diff.lean): Forward-mode rational & interval dual numbers (`DualRat`, `DualInterval`), symbolic differentiation (`symbolicDeriv`), and reverse-mode gradient pullback (`gradReverse`), proving `evalDual_fst_eq_eval`, `symbolicDeriv_agrees_with_dual`, and `interval_mean_value_enclosure`.
  - [`Obend/Analysis/Flowpipe.lean`](lean/Obend/Analysis/Flowpipe.lean): Validated Euler–Taylor / Picard–Lindelöf interval ODE flowpipe integrator (`OdeSystem`, `stepFlowpipe`, `computeFlowpipeTrajectory`), proving `flowpipe_step_encloses_euler` and `flowpipe_safety_admits_contract`.
  - [`crates/obend-gui/src/viewport.rs`](crates/obend-gui/src/viewport.rs): Interactive SVG/HTML/terminal-canvas viewport renderer across all 10 `ProjectionKind`s, 2D/3D ODE flowpipe phase-portrait plots, GDSII layouts with DRC markers, `ReductionMachine` eFPGA heatmaps, and live `.free`/`.press`/`.locked` `LawDial` controls.

### WS 26: Live Multi-Node Rust Runner (`crates/obend-node`) — **COMPLETE**
- **Modules**:
  - [`crates/obend-node/src/lib.rs`](crates/obend-node/src/lib.rs): Concrete FIPS 180-4 SHA-256, domain-separated cSHAKE256, and deterministic Ed25519 signing/verification bound to `Simplex` BFT certificates (`PropCert`, `SkipCert`, `FinCert`, `EquivocationSlashReceipt`), `FogOfWar` `BlindedVaultMultiProof`, and an off-chain primal-dual LP `drex-clearing@1` batch clearing solver verified via `ObendSession` FFI.

---

## Part III — Completed Kernel & Subsystem Hardening Frontiers (`WS 27`: `G1` – `G6`)

All fine-grained kernel hardening targets (`G1`–`G6`, [`METATHEORY.md` §3.1](METATHEORY.md)) are **complete and mechanized with `0 sorryAx`**:
- **`G1` (`Obend/Core/Proofs/TickCost.lean` & `Obend/Run/Ticks.lean`)**: Proved `runBounded_mono`, `finishedNat_mono`, `cost_indexed_completeness`, `deepenBounded_mono`, and `deepenBounded_eq_deepen`.
- **`G2` (`Obend/Spec/C4.lean` & `Obend/Kind/Registry.lean`)**: Proved `orderedPresentationInvariant` for C4 linearization under injective renamings and `effectiveOf_agree_of_lineage_agree` for cross-registry stable kind identities.
- **`G3` (`Obend/Core/Proofs/GradedRecord.lean` & `Obend/Core/Proofs/Aggregate.lean`)**: Formalized per-field graded $\Sigma^\otimes / \Sigma^\&$ record quantities (`graded_sigma_tensor_conserves_linear`, `graded_sigma_with_get_conserves_linear`) and machine-level heap-address linear conservation (`heap_linear_conserved`).
- **`G4` (`Obend/Receipt/Merkle.lean` & `Obend/Fold/Collapse.lean`)**: Chained world/epoch roots via cSHAKE256 Merkle proofs (`dated_sound`, `opens_binds`, `collapse_sound`).
- **`G5` (`Obend/Judge/Lrat.lean`, `Obend/Judge/Clearing.lean`, `Obend/Judge/RealAnalysis.lean`)**: Unified external certificate judges (`lrat@1`, `drex-clearing@1`, `real-analysis@1`) under `Judge`.
- **`G6` (`Obend/Leaf/Residual.lean` & `Obend/Leaf/Flatten.lean`)**: Formalized `superOnlyProjected` / `superOnlyProjectedRow` and proved `openVtable_no_residual_super` and `no_residual_super` for open and closed vtable flattening.
