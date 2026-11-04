# Obend — Engineering Plan & Workstream Status

> **Current build**: the Lean library under `lean/Obend/` (tier 1, `lake build`), the teeth, apps, test suites and census (tier 2, `lake build Obend.Census Teeth Tests` on a build box), and 5 Rust crates (`obend-sandbox`, `obend-ffi`, `obend-gui`, `obend-node`, `obend-fpga-hal`). This document keeps no counts of modules, constants or theorems: the census prints a per-directory classification (universal theorems, closed theorems, examples, teeth) and refuses any constant resting on `sorryAx` or a declared axiom; headline totals were retired on 2026-11-04 (`review/DECISIONS-20261031.md`).

---

## Part I — Completed Foundation Workstreams (`WS 1` – `WS 17`)

All 17 foundational workstreams from the initial `Obend` roadmap are **complete**; the census and the teeth, not this table, are the record of what is proved:

| Workstream | Scope | Key Modules | Key Mechanized Theorems ([`METATHEORY.md`](METATHEORY.md)) |
|---|---|---|---|
| **WS 1: Judge & Dated Receipts (`G4`)** | Single gatekeeper `Judge`, multi-slot citations, cSHAKE256 Merkle-dated replay resistance | [`Obend/Judge.lean`](lean/Obend/Judge.lean), [`Obend/Receipt.lean`](lean/Obend/Receipt.lean), [`Obend/Receipt/Merkle.lean`](lean/Obend/Receipt/Merkle.lean) | `accepts_cited_sound`, `dated_sound`, `opens_binds` |
| **WS 2: Canonical Code & Quoting (`C1`)** | Version-prefixed binary encoding, hole-free portable `Code Ψ A θ`, observer ladder `≈q ⊆ ≈r ⊆ ≈b` | [`Obend/Core/Code.lean`](lean/Obend/Core/Code.lean), [`Obend/Equiv/Quote.lean`](lean/Obend/Equiv/Quote.lean) | `encodingVersion_binds`, `import_roundtrip`, `import_complete`, `code_noHole`, `observer_ladder` |
| **WS 3: Nominal `#kind` Branding (`C1`, `G2`)** | First-class `Ty.kinded`, `_kind.md` C4 Vault cells, capability-gated reflective mirrors | [`Obend/Core/Nominal.lean`](lean/Obend/Core/Nominal.lean), [`Obend/Kind.lean`](lean/Obend/Kind.lean), [`Obend/Run/Reflect.lean`](lean/Obend/Run/Reflect.lean) | `kinded_refuses`, `kinds_never_agree`, `kind_stale_iff_blocked`, `forged_descriptor_refused` |
| **WS 4: Cost, Demand & Ticks (`G1`)** | Xia least-demand analysis, clairvoyant simulation, tight machine tick bounds | [`Obend/Equiv/Demand.lean`](lean/Obend/Equiv/Demand.lean), [`Obend/Equiv/Cost.lean`](lean/Obend/Equiv/Cost.lean), [`Obend/Core/Proofs/TickCost.lean`](lean/Obend/Core/Proofs/TickCost.lean) | `demand_is_least`, `sim_cv`, `mix_assoc_cost`, `ticks_within_fragment` |
| **WS 5 & WS 15: `Leaf` (`G6`)** | Layer flattening, zero residual vtables, book emission, `specSlot` deopt guards (the `BendTT` net module was deleted 2026-11-04) | [`Obend/Leaf/Flatten.lean`](lean/Obend/Leaf/Flatten.lean), [`Residual.lean`](lean/Obend/Leaf/Residual.lean), [`Emit.lean`](lean/Obend/Leaf/Emit.lean), [`Static.lean`](lean/Obend/Leaf/Static.lean), [`Specialize.lean`](lean/Obend/Leaf/Specialize.lean) | `flatten_sound`, `vtable_clean`, `book_sound`, `bequiv_dataPinSpecialize`, `specialize_choice`, `moved_pin_blocks` |
| **WS 6: Concurrent Runner & Atomic Stitch** | Shared-world ticket exclusivity, crash-safe journal, offline fork/join atomic stitch | [`Obend/Run/Runner.lean`](lean/Obend/Run/Runner.lean), [`Obend/Run/Durable.lean`](lean/Obend/Run/Durable.lean), [`Obend/Run/Fork.lean`](lean/Obend/Run/Fork.lean) | `joint_reachable_ticket_exclusive`, `durable_refines`, `stitch_atomic`, `stitch_double_spend` |
| **WS 7 & WS 9: Surface `.obend`, Law Dials & Repair** | Surface parser/elaborator, 3-mode `LawDial` (`.free`/`.press`/`.locked`), Bellman-Ford multi-field repair synthesis | [`Obend/Spec/LawDial.lean`](lean/Obend/Spec/LawDial.lean), [`Obend/Vault/Law.lean`](lean/Obend/Vault/Law.lean) | `dial_free_confluent`, `demoOr_not_confluent`, `solveLawWitness_sound` |
| **WS 8: Double-Entry Capability Ledger** | Conserved streaming ledger fold, `trial-balance@1` non-omission coverage, Vault-backed ledger | [`Obend/Ledger/Register.lean`](lean/Obend/Ledger/Register.lean), [`Report.lean`](lean/Obend/Ledger/Report.lean), [`Vault.lean`](lean/Obend/Ledger/Vault.lean) | `conserved`, `net_conserved`, `closed_forever`, `vault_conserved` |
| **WS 10–12: Late-Bound Logic (T1, T2, T3)** | Open-recursive late binding, contextual `≈r` rewriting, disjoint-field framing | [`Obend/Logic/LateBinding.lean`](lean/Obend/Logic/LateBinding.lean), [`Rewrite.lean`](lean/Obend/Logic/Rewrite.lean), [`Frame.lean`](lean/Obend/Logic/Frame.lean) | `late_binding`, `rewrite_sound`, `claim_frame` |
| **WS 13: Linear Conservation & `Term.split` (`C2`, `G3`)** | Source `SubjectReduction`, `.linear` step conservation, `Term.split` record destructor, `Join.max` branch accounting | [`Obend/Core/Proofs/SubjectReduction.lean`](lean/Obend/Core/Proofs/SubjectReduction.lean), [`Conservation.lean`](lean/Obend/Core/Proofs/Conservation.lean), [`Aggregate.lean`](lean/Obend/Core/Proofs/Aggregate.lean) | `step_preserves_typing`, `step_conserves_linear`, `machine_split_passes_all`, `splice_typed` |
| **WS 14: Static Impact Cones & Proof Journal** | Kleene 3-valued abstract interpretation, exact change-impact cones, whole-repo proof dependency journal | [`Obend/Analysis/Impact.lean`](lean/Obend/Analysis/Impact.lean), [`Coverage.lean`](lean/Obend/Analysis/Coverage.lean), [`lean/Journal/Journal.lean`](lean/Journal/Journal.lean) | `read3_sound`, `affected_exact`, `unlisted_unchanged`, `verdict_unaffected_iff` |
| **WS 16: `Lower` (Lean 4 Kernel $\to$ `Core4` $\to$ `Leaf` $\to$ RTL)** | Kernel `Expr` lowering, `f.eq_def` recursion, Tait–Girard completeness, `transport@1`, RTL bridge | [`Obend/Lower/Fragment.lean`](lean/Obend/Lower/Fragment.lean), [`Transport.lean`](lean/Obend/Lower/Transport.lean), [`Proofs/Sound.lean`](lean/Obend/Lower/Proofs/Sound.lean), [`Complete.lean`](lean/Obend/Lower/Proofs/Complete.lean), [`Hardware.lean`](lean/Obend/Lower/Proofs/Hardware.lean) | `lower_sound`, `lower_checks`, `lower_complete_ltyped_nat`, `transportTheorem`, `lower_to_rtl_sat_sound` |
| **WS 17: Verified Silicon Stack (`Obend/Hardware/`)** | RTL-to-GDSII, STA, Place & Route, DRC/LVS, Multiphysics, Photonics, PCB, RF, eFPGA `ReductionMachine` with `ICAP` DPR, and the `#tooth` checks in `SiliconTeeth.lean` | [`Obend/Hardware/`](lean/Obend/Hardware/), [`Obend/Teeth/Hardware/SiliconTeeth.lean`](lean/Obend/Teeth/Hardware/SiliconTeeth.lean) | `automaton_simulates_book`, `dpr_preserves_neighbor_tiles_and_packets`, `dpr_specialized_tile_executes_new_book` |

---

## Part II — Completed Next-Generation Workstreams (`WS 18` – `WS 27`)

All 10 next-generation workstreams (`WS 18`–`WS 27`) from [`NEXT-MATHEMATICA.md`](NEXT-MATHEMATICA.md), [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md), and [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md) are **complete and verified across the Lean and Rust workspaces**:

### WS 18 (`R1`): Semantic `CellContract`s, Forever-Crowns (`Narrows`), Real Analysis & Bidirectional Lean Tactic Bridge — **COMPLETE**
- **Modules**:
  - [`Obend/Law/Contract.lean`](lean/Obend/Law/Contract.lean): Semantic `CellContract` ($I(\text{old}) \to T(\text{old}, \text{new}) \to I(\text{new})$) and `Narrows newC oldC` monotonic forever-crowns (`narrows_refl`, `narrows_trans`, `carry_preserves_forever_crowns`), plus backwards-compatible embedding of legacy `Law.Claim`.
  - [`Obend/Analysis/RealAnalysis.lean`](lean/Obend/Analysis/RealAnalysis.lean) & [`Obend/Judge/RealAnalysis.lean`](lean/Obend/Judge/RealAnalysis.lean): Verified rational/dyadic interval arithmetic (`Interval.add_mem`, `Interval.mul_mem`, `evalInterval_sound`), Horner polynomial enclosures, and contraction-mapping fixed-point certificates .
  - [`Obend/Lower/Reflect.lean`](lean/Obend/Lower/Reflect.lean) & [`Obend/Tactic/Weave.lean`](lean/Obend/Tactic/Weave.lean): Outward reflection (`reflectTerm`) and Lean 4 tactic suite (`obend_unfold`, `obend_law`, `obend_split`, `obend_tooth`).

### WS 19 (`R2`): Proof-Carrying Smart Contract Vault, Wide-Pullback Hyperedges, `Seat`s & Certified `drex-clearing@1` — **COMPLETE**
- **Modules**:
  - [`Obend/Vault/Hyperedge.lean`](lean/Obend/Vault/Hyperedge.lean): Multi-slot atomic `VaultTurn` (`reads`, `writes`, `created`, `consumed`, `witnesses`) with .
  - [`Obend/Ledger/Book.lean`](lean/Obend/Ledger/Book.lean) & [`Obend/Ledger/Seat.lean`](lean/Obend/Ledger/Seat.lean): Multi-commodity linear `Book` conservation and ZoE-style `Seat` offer safety (: want-predicate satisfaction or full refund).
  - [`Obend/Judge/Clearing.lean`](lean/Obend/Judge/Clearing.lean): Primal-dual LP certificate checker (`drex-clearing@1`) proving supply conservation, primal/dual feasibility, and zero duality gap .

### WS 20 (`R3`): DeOS Capability Surfaces, Blinded Projections (`FogOfWar`), `Mandate`s & Sandstorm Grain Confinement — **COMPLETE**
- **Modules**:
  - [`Obend/Vault/Escrow.lean`](lean/Obend/Vault/Escrow.lean) & [`Obend/Vault/Affordance.lean`](lean/Obend/Vault/Affordance.lean): First-class DeOS capability patterns (`SealedEscrow`, `PrepaidLease`, `GatedAffordance`, `PublishGate`) built over `VaultTurn` and `Seat`.
  - [`Obend/Vault/Projection.lean`](lean/Obend/Vault/Projection.lean): Merkle-committed `BlindedVaultView` (`FogOfWar`) proving public `CellContract` satisfaction without revealing blinded private branches .
  - [`Obend/Vault/Mandate.lean`](lean/Obend/Vault/Mandate.lean) & [`crates/obend-sandbox`](crates/obend-sandbox): Sandstorm-style isolated `Grain` execution , `Powerbox` capability attenuation , human-auditable `Mandate` bounds , and native OS sandboxing (`sandbox-exec` / `bwrap`).

### WS 21 (`R4`): Simplex-shaped consensus lemmas, 4-Tier Finality, `EpistemicConsensus` & `Fold.collapse` — **PARTIAL (reassessed 2026-11-04, `review/EXPERT-distributed-security-20261103.md`)**
- **Modules**:
  - [`Obend/Consensus/Simplex.lean`](lean/Obend/Consensus/Simplex.lean): quorum-intersection and same-view uniqueness lemmas over abstract vote predicates (`honest_quorum_intersection`, `qc_same_view_unique`), a count-based `SimplexState` cell contract, and `simplex_accountable_safety` over a receipt that names voters but carries no votes. There is NO protocol state machine (no proposal, vote, or view-change handler) and no  or ; the Rust simulator's one-round protocol is described in `DEOS-CONTRACTS-CONSENSUS.md` §5.2.
  - [`Obend/Consensus/Epistemic.lean`](lean/Obend/Consensus/Epistemic.lean): Subjective trust-graph weighted `EpistemicConsensus` and `epistemic_sybil_bounded_by_seed_cut`.
  - [`Obend/Consensus/Finality.lean`](lean/Obend/Consensus/Finality.lean) & [`Obend/Fold/Collapse.lean`](lean/Obend/Fold/Collapse.lean): Unified 4-tier finality state machine connecting `LawDial.free` CRDT $\to$ `VaultTurn` disjoint fast-path  $\to$ `Simplex` BFT $\to$ `EpistemicConsensus` + `Fold.collapse` .

### WS 22 (`R5`): `.obnb` Structured Notebook Cells, Read-Only Silicon Projections & Thin Rust GUI/FFI — **COMPLETE**
- **Modules**:
  - [`Obend/Doc/Structured.lean`](lean/Obend/Doc/Structured.lean) & [`Obend/Vault/HardwareProjection.lean`](lean/Obend/Vault/HardwareProjection.lean): Typed `BlockGraph` `.obnb` notebook cells and read-only projection adapters over `Obend/Hardware/*` (`circuit`, `netlist`, `timing`, `gdsii`, `waveform`, `cellQuote`, `notebookCell`, `proofTree`, `contractBadge`, `clearingLedger`).
  - [`Obend/FFI/Bridge.lean`](lean/Obend/FFI/Bridge.lean), [`lean/c/obend_bridge.c`](lean/c/obend_bridge.c), [`crates/obend-ffi`](crates/obend-ffi), & [`crates/obend-gui`](crates/obend-gui): C-ABI bridge and Rust GUI/CLI shell.

### WS 23 & WS 24: Recursive Inductives, 2nd/3rd Futamura Specialization, 64-Bit `ExprCAM` & Silicon Lean Elaborator — **COMPLETE**
- **Modules**:
  - [`Obend/Lower/Inductive.lean`](lean/Obend/Lower/Inductive.lean): Recursive inductive data model (`IndVal`, `RecRule`, `IndSig`, `LcnfDecl`), constructor-tag packing , structural `matchCtor` , and `fromLeanExpr` reflection bridge.
  - [`Obend/Leaf/Static.lean`](lean/Obend/Leaf/Static.lean): the constant folder and `specializeBook` (`bequiv_dataPinSpecialize`, `staticApply_slot_sound`). The 2nd/3rd Futamura projections claimed here were deleted on 2026-11-04 (`review/EXPERT-compiler-runtime-20261103.md` §2.1); nothing in the tree self-applies a specializer.
  - [`Obend/Lower/LeanKernel.lean`](lean/Obend/Lower/LeanKernel.lean) & [`Obend/Lower/Proofs/SiliconKernel.lean`](lean/Obend/Lower/Proofs/SiliconKernel.lean): Pure `KLevel`/`KExpr`/`KEnv` Lean 4 kernel (`kernelWhnf`, `kernelIsDefEq`, `kernelInferType`, `kernelCheckDecl`) with general user-defined inductive $\iota$-reduction (`KInductDecl`, `KRecRule`, `kernelWhnf_general_iota_sound`), `Quot.lift` on `Quot.mk` (`kernelWhnf_quot_lift_sound`), live `checkLeanEnvDeclInSilicon`, and end-to-end `ReductionMachine` eFPGA synthesis (`silicon_kernel_check_sound`).
  - [`Obend/Lower/ExprCAM.lean`](lean/Obend/Lower/ExprCAM.lean): 64-bit hardware hash-consed DAG / CAM pool (`PackedNodeWord`, `ExprCAMPool`, `internExpr`, `unintern`) with 1-cycle handle equality (`exprCam_eq_iff_handle_eq`), $O(1)$ `hasLooseBVar` bit-flag soundness (`exprCam_looseBVar_flag_sound`), and lossless round-trip (`intern_unintern_roundtrip`).

### WS 25: Symbolic & Interval Automatic Differentiation, Validated ODE Flowpipes & Rich Viewport Rendering — **COMPLETE**
- **Modules**:
  - [`Obend/Analysis/Diff.lean`](lean/Obend/Analysis/Diff.lean): Forward-mode rational & interval dual numbers (`DualRat`, `DualInterval`), symbolic differentiation (`symbolicDeriv`), and reverse-mode gradient pullback (`gradReverse`), proving `evalDual_fst_eq_eval`, `symbolicDeriv_agrees_with_dual`, and `interval_mean_value_enclosure`.
  - [`Obend/Analysis/Flowpipe.lean`](lean/Obend/Analysis/Flowpipe.lean): Validated Euler–Taylor / Picard–Lindelöf interval ODE flowpipe integrator (`OdeSystem`, `stepFlowpipe`, `computeFlowpipeTrajectory`), proving `flowpipe_step_encloses_euler` and `flowpipe_safety_admits_contract`.
  - [`crates/obend-gui/src/viewport.rs`](crates/obend-gui/src/viewport.rs): Interactive SVG/HTML/terminal-canvas viewport renderer across all 10 `ProjectionKind`s, 2D/3D ODE flowpipe phase-portrait plots, GDSII layouts with DRC markers, `ReductionMachine` eFPGA heatmaps, and live `.free`/`.press`/`.locked` `LawDial` controls.

### WS 26: `crates/obend-node`, an in-process SIMULATOR (reclassified 2026-11-04) — **COMPLETE AS A SIMULATOR**
- **Modules**:
  - [`crates/obend-node/src/lib.rs`](crates/obend-node/src/lib.rs): simulator primitives (hand-written SHA-256, cSHAKE256, and a Schnorr scheme on edwards25519 named `SimulatorKeypair`, NOT Ed25519 and not constant-time), `PropCert` / `SkipCert` / `FinCert` / `EquivocationSlashReceipt` over them, `FogOfWar` `BlindedVaultMultiProof` (a list of per-cell openings, not a multiproof), the `drex-clearing@1` primal-dual solver, and Lean-session receipts bound by `kernel_receipt_check` (`ObendSession::commit_payload`). Not a deployable validator; the validator is redone at the minidregg/dregg integration.

---

## Part III — Completed Kernel & Subsystem Hardening Frontiers (`WS 27`: `G1` – `G6`)

All fine-grained kernel hardening targets (`G1`–`G6`, [`METATHEORY.md` §3.1](METATHEORY.md)) are **complete and mechanized**:
- **`G1` (`Obend/Core/Proofs/TickCost.lean` & `Obend/Run/Ticks.lean`)**: Proved `runBounded_mono`, `finishedNat_mono`, `cost_indexed_completeness`, `deepenBounded_mono`, and `deepenBounded_eq_deepen`.
- **`G2` (`Obend/Spec/C4.lean` & `Obend/Kind/Registry.lean`)**: Proved `orderedPresentationInvariant` for C4 linearization under injective renamings and `effectiveOf_agree_of_lineage_agree` for cross-registry stable kind identities.
- **`G3` (`Obend/Core/Proofs/GradedRecord.lean` & `Obend/Core/Proofs/Aggregate.lean`)**: Formalized per-field graded $\Sigma^\otimes / \Sigma^\&$ record quantities (`graded_sigma_tensor_conserves_linear`, `graded_sigma_with_get_conserves_linear`) and machine-level heap-address linear conservation (`heap_linear_conserved`).
- **`G4` (`Obend/Receipt/Merkle.lean` & `Obend/Fold/Collapse.lean`)**: Chained world/epoch roots via cSHAKE256 Merkle proofs (`dated_sound`, `opens_binds`).
- **`G5` (`lean/Obend/Run/Runner.lean`, `lean/Obend/Run/Shared.lean`, `lean/Obend/Run/HyperLaw.lean`, `lean/Obend/Judge/Lrat.lean`, `lean/Obend/Judge/Clearing.lean`, `lean/Obend/Judge/RealAnalysis.lean`)**: Implemented Effect Laws Designs A–D (Design A single-runner history & dispatch guards in `Obend.Run.Runner`; Design B multi-runner atomic ledger commit & `OnceSpent` in `Obend.Run.Shared`; Design C `k=2` relational safety hyperproperties & non-interference `Obend.Run.HyperLaw.checkHyperLaw2NonInterference_sound`; Design D `Oracle7` Gelfond-Lifschitz modal `□` epistemic equilibrium judge `Obend.Run.HyperLaw.oracle7Judge` / `Obend.Run.HyperLaw.checkOracle7Equilibrium_sound`) and unified external certificate judges (`lrat@1`, `drex-clearing@1`, `real-analysis@1`) under `Obend.Judge`.
- **`G6` (`Obend/Leaf/Residual.lean` & `Obend/Leaf/Flatten.lean`)**: Formalized `superOnlyProjected` / `superOnlyProjectedRow` and proved `openVtable_no_residual_super` and `no_residual_super` for open and closed vtable flattening.

---

## Part IV — Completed 5-Horizon Full Slate (`WS 28` – `WS 32`)

### WS 28: Silicon Elaborator Stage 5 & 6 — `MetaM` Unification, `DiscrTree` LUT Compiler & Verilator Co-Sim (`SILICON-ELABORATOR.md` §6–7) — **COMPLETE**
- **Modules**:
  - [`Obend/Lower/MetaUnify.lean`](lean/Obend/Lower/MetaUnify.lean): Pure `MetavarContext` state (`MVarId`, `MVarDecl`, `PostponedConstraint`), occurs-check (`occursMVar`), contextual substitution (`instantiateMVars`), higher-order Miller pattern unification (`millerProjectBody?`, `solveMillerPattern?`), structural unification (`metaUnifyFuel`), postponed constraint solving (`resolvePostponedConstraints`), and kernel-certified elaboration (`elaborateWithMetaUnify`, `metaUnify_assign_sound`, `lowerMetaUnifyToBook`).
  - [`Obend/Lower/DiscrTreeLUT.lean`](lean/Obend/Lower/DiscrTreeLUT.lean): Discrimination-tree key & trie formalization (`DiscrKey`, `DiscrTrie`, `extractLeanDiscrKeys`), compilation of a trie into Zone-3 eFPGA LUT pipelines (`compileDiscrTrieToLutPipeline`, `compileDiscrTrieToTile`), `SlotGuardReg` epoch pin invalidation, and synthesizable SystemVerilog emission (`emitExprCamKernelLutSV`, `exprCam_siliconKernel_sv_cosim_sound`).
  - [`tests/silicon_elab/run_verilator_cosim.py`](tests/silicon_elab/run_verilator_cosim.py): Cycle-accurate Verilator 5.046 SystemVerilog testbench verifying the 64-bit `ExprCAM` + `SiliconKernel` + Zone-3 `DiscrTree` LUT FSM across 5 clock cycles.

### WS 29: The Next Mathematica II — Taylor Models, Gröbner / Positivstellensatz CAS & Hybrid Systems (`NEXT-MATHEMATICA.md`) — **COMPLETE**
- **Modules**:
  - [`Obend/Analysis/TaylorModel.lean`](lean/Obend/Analysis/TaylorModel.lean): High-order Taylor models $(p(x), I_{\text{rem}})$ (`TaylorModel1D`), degree-$k$ truncated arithmetic (`tmAdd`, `tmSub`, `tmMul`), verified transcendental enclosures (`tmExp`, `tmSin`, `tmCos`, `tmLn1p`, `tmSqrt1p`, `taylorModel_transcendental_enclosure_sound`), and contractive Picard–Lindelöf ODE integration (`stepTaylorModelPicardLinear1D`, `taylorModel_picard_sound`).
  - [`Obend/Analysis/Groebner.lean`](lean/Obend/Analysis/Groebner.lean): Multivariate polynomial division (`polyReduceStep`, `polyNormalForm`), Buchberger S-polynomials (`sPolynomial`, `checkGroebnerBasis`), certified ideal membership ($f = \sum q_i g_i$, `checkIdealMembershipCert`, `groebner_ideal_membership_sound`), and Stengle Positivstellensatz semi-algebraic certificates (`PositivstellensatzCert`, `positivstellensatzJudge`, `stengle_positivstellensatz_sound`) wired into `obend_law` ([`Obend/Tactic/Weave.lean`](lean/Obend/Tactic/Weave.lean)).
  - [`Obend/Analysis/Hybrid.lean`](lean/Obend/Analysis/Hybrid.lean): Hybrid automata (`HybridMode`, `GuardBox3D`, `AffineReset3D`, `HybridAutomaton`) coupling continuous `Flowpipe` ODE integration with discrete guarded transitions and affine reset maps (`stepHybridTrace`, `hybrid_flowpipe_safety_admits_contract`).

### WS 30: Physical-World & Mechatronic Co-Design Bridge (`PHYSICAL.md` $\leftrightarrow$ `.obnb` Notebooks) — **COMPLETE**
- **Modules**:
  - [`Obend/Vault/PhysicalProjection.lean`](lean/Obend/Vault/PhysicalProjection.lean): Strictly read-only `.obnb` cell projections (`Doc.Content.cell`) for 5-axis CNC kinematic toolpaths with Featherstone 6D twists/wrenches and 21-parameter Abbe compensation (`projectCncToolpath`, `physical_cnc_abbe_projection_sound`), OpenUSD `SdfPath` scene graphs with `LIVERPS` relocates and `AffineForm1D` SDF enclosures (`projectOpenUsdScene`), and coupled LC-drive stator multiphysics (`projectStatorMultiphysics`, `physical_projection_deterministic`, `physical_projection_doc_noninterference`).
  - [`crates/obend-gui/src/viewport.rs`](crates/obend-gui/src/viewport.rs): Interactive SVG, HTML `LawDial`, and ANSI terminal renderers (`render_cnc_5axis_toolpath_svg`, `render_openusd_scene_svg`, `render_stator_multiphysics_svg`, `render_physical_viewport`).

### WS 31: Live Interactive `.obnb` Workbench Daemon & Lean 4 LSP Bridge (`crates/obend-gui` & `crates/obend-ffi`) — **COMPLETE**
- **Modules**:
  - [`Obend/FFI/Bridge.lean`](lean/Obend/FFI/Bridge.lean), [`lean/c/obend_bridge.c`](lean/c/obend_bridge.c), & [`crates/obend-ffi`](crates/obend-ffi): Extended C-ABI with `obend_view_affordances`, `obend_cell_pop_lean`, and `obend_cell_weave_cert`.
  - [`crates/obend-gui/src/server.rs`](crates/obend-gui/src/server.rs): Sub-5ms interactive HTTP/JSON `.obnb` workbench daemon (`WorkbenchServer`, `GET /notebook`, `POST /dial`, `POST /eval`, `POST /lean-bridge`) backed by a persistent `mimalloc`-safe `ObendSession` worker thread, Bellman–Ford multi-field repair synthesis (`suggest_multi_field_admits`), and live `"Pop Out to Lean 4"` / `"Weave Certificate"` verification.

### WS 32: Multi-validator simulation over loopback & Sandboxed Grain Execution (`crates/obend-node` & `crates/obend-sandbox`) — **COMPLETE AS A SIMULATOR (reclassified 2026-11-04)**
- **Modules**:
  - [`crates/obend-node/src/net.rs`](crates/obend-node/src/net.rs) & [`crates/obend-node/src/lib.rs`](crates/obend-node/src/lib.rs): `SimplexCluster` runs $N$ simulated validators in ONE process over `127.0.0.1:0` TCP/UDP, keys derived from the public `SimplexCluster::simulator_seed`, JSON wire frames, an in-memory `DurableNodeWal`, harness-driven view changes. The protocol is one-round (finalize vote on a current-view proposal extending the committed tip; `FinCert` = 2f+1 such votes); the 2026-11-03 faults (finalize votes accepted for future views, finalized blocks deduplicated by height) are fixed; see `DEOS-CONTRACTS-CONSENSUS.md` §5.2 for what is proved versus what is argued. `obend-sandbox`: fail-closed `BubblewrapRunner` (Linux) / Seatbelt (macOS, permissive profile), `ConfinementPolicy`, `LaunchGate`, `CpuMeter`; `Powerbox` mandates are keyed by agent name (not unforgeable) and delegation now debits the parent.

### WS 33: Rehydratable Membranes, `Sturdyref`, Functorial `Rerender` Square & 3D `ReactiveAffordance` (`DEOS-CONTRACTS-CONSENSUS.md` §4.4) — **COMPLETE**
- **Modules**:
  - [`Obend/Vault/Rehydration.lean`](lean/Obend/Vault/Rehydration.lean): Mechanizes the 4-pillar Rehydratable Membranes architecture:
    1. **Derived `Rehydration` Liveness-Type (`Live | ReplayedDeterministic | ReconstructedApproximate`)**: `AttestedRoot.holds`, `InteractionLog`, `confined`, `classify`, `replayedDeterministic_iff_confined`, `reconstructedApproximate_iff_unconfined`, `invalidAttestation_not_replayed`, `confined_chain_covers_log`, `unconfined_chain_drops_interactions`, and `replayedDeterministic_replays`.
    2. **`Sturdyref`, Relational `Membrane` & Chained Multi-Hop Reshare (`Membrane.reshare`)**: `MembraneViewer`, `membraneShows`, `projectMembrane`, `membrane_two_viewers_distinct`, `Membrane.reshare` ($A \to B \to C$ cumulative active-name attenuation with `amplifying_reshare_refused`, `reshare_chain_attenuates`, `reshare_chain_blocks_delayed_permits_amplification`), and `rehydrateSturdyref`.
    3. **Functorial Rerender Square & Frustum-Snapshot Re-Expansion**: `rerender_square` (`project ∘ step = step ∘ project`), `rerender_after_step_authorized`, `snapshot_roundtrip`, and `snapshot_roundtrip_attenuated`.
    4. **3-Dimensional `ReactiveAffordance`**: `TransitionGate` (`pre old ∧ post new ∧ link old new`) + `[openHeight, closeHeight]` deadline window + the 6 cross-polarity teeth (`fireReactive_iff`, `fireReactive_wrong_old_refuses`, `fireReactive_after_deadline_refuses`, `fireReactive_window_reactive`).
  - [`lean/tests/rehydration/RehydrationTest.lean`](lean/tests/rehydration/RehydrationTest.lean): the `#tooth` kernel mutation tests and `#print axioms` checks for it (built by the `Tests` target).
