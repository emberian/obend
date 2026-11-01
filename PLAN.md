# Obend — Engineering Plan & Workstream Status

> **Current Build**: **408+ Lean modules**, **52,368 package constants** across **622 build jobs**, **`0 sorryAx`**, **`0` custom axioms**.

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

## Part II — Active Next-Generation Workstreams (`WS 18` – `WS 23`)

Detailed blueprints in [`NEXT-MATHEMATICA.md`](NEXT-MATHEMATICA.md), [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md), and [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md).

### WS 18 (`R1`): Semantic `CellContract`s, Forever-Crowns (`Narrows`), Real Analysis & Bidirectional Lean Tactic Bridge
- **Modules**:
  - `Obend/Law/Contract.lean` & `Obend/Law/Proofs/Contract.lean`: Semantic `CellContract` ($I(\text{old}) \to T(\text{old}, \text{new}) \to I(\text{new})$) and `Narrows newC oldC` monotonic forever-crowns (`narrows_refl`, `narrows_trans`, `relaw_preserves_forever_crown`), plus backwards-compatible embedding of legacy `Law.Claim`.
  - `Obend/Analysis/Interval.lean`, `Obend/Analysis/Diff.lean`, `Obend/Analysis/Fixpoint.lean`: Verified dyadic interval enclosures, forward/reverse automatic differentiation over `Core4`, and contraction-mapping fixed-point certificates integrated into `Obend/Spec/LawDial.lean` (`.press`).
  - `Obend/Lower/Reflect.lean` & `Obend/Lower/Tactics.lean`: Outward reflection (`Core4.Term` $\to$ `Lean.Expr`) and Lean 4 tactic suite (`obend_unfold`, `obend_law`, `obend_split`, `obend_tooth`, `byLoweredLean`) closing the round-trip loop from `Obend` obligations to Mathlib/Lean 4 tactics and back to `Core4` witnesses.

### WS 19 (`R2`): Proof-Carrying Smart Contract Vault, Wide-Pullback Hyperedges, `Seat`s & Certified `drex-clearing@1`
- **Modules**:
  - `Obend/Vault/Turn.lean` & `Obend/Vault/Proofs/Turn.lean`: Multi-slot atomic `VaultTurn` (`reads`, `writes`, `created`, `consumed`, `witnesses`) with `vaultTurn_wide_pullback_sound` and `vaultTurn_conserves_linear_slots`.
  - `Obend/Ledger/Book.lean` & `Obend/Ledger/Seat.lean`: Multi-commodity linear `Book` conservation and ZoE-style `Seat` offer safety (`zoe_offer_safety`: want-predicate satisfaction or full refund).
  - `Obend/Ledger/Clearing.lean`: $O(|E| + |V|)$ primal-dual LP certificate checker (`drex-clearing@1`) proving supply conservation, primal/dual feasibility, and zero duality gap (`drex_clearing_optimal_and_conserving`).

### WS 20 (`R3`): DeOS Capability Surfaces, Blinded Projections (`FogOfWar`), `Mandate`s & Sandstorm Grain Confinement
- **Modules**:
  - `Obend/Vault/Surface.lean`: First-class DeOS capability patterns (`SealedEscrow`, `PrepaidLease`, `GatedAffordance`, `PublishGate`) built over `VaultTurn` and `Seat`.
  - `Obend/Vault/Blinded.lean`: Merkle-committed `BlindedVaultView` (`FogOfWar`) proving public `CellContract` satisfaction without revealing blinded private branches (`blinded_projection_non_forgeable`).
  - `Obend/Vault/Grain.lean` & `Obend/Vault/Mandate.lean`: Sandstorm-style isolated `Grain` execution (`grain_confinement_sound`), `Powerbox` capability attenuation (`powerbox_attenuation_monotonic`), and human-auditable `Mandate` bounds (`mandate_bounds_turn`).

### WS 21 (`R4`): Symbolic `Simplex` BFT, 4-Tier Finality, `EpistemicConsensus` & `Fold.collapse`
- **Modules**:
  - `Obend/Ledger/Simplex.lean` & `Obend/Ledger/Proofs/Simplex.lean`: Symbolic-mode `Simplex` BFT consensus (`PropCert` $2f+1$ notarization, `SkipCert` $2f+1$ dummy-block timeout, `FinCert` $2f+1$ finalization) with `simplex_safety`, `simplex_accountable_safety` (concrete `SlashingReceipt` on any fork), and `simplex_bounded_liveness_after_gst`.
  - `Obend/Ledger/Epistemic.lean`: Subjective trust-graph weighted `EpistemicConsensus` and `epistemic_sybil_bounded_by_seed_cut`.
  - `Obend/Ledger/Finality.lean`: Unified 4-tier finality state machine connecting `LawDial.free` CRDT $\to$ `VaultTurn` disjoint fast-path (`disjoint_turns_commute`) $\to$ `Simplex` BFT $\to$ `EpistemicConsensus` + `Fold.collapse`.

### WS 22 (`R5`): `.obnb` Structured Notebook Cells, Read-Only Silicon Projections & Thin Rust GUI/FFI
- **Modules**:
  - `Obend/Doc/Notebook.lean` & `Obend/Doc/HardwareView.lean`: Typed `BlockGraph` `.obnb` notebook cells (`CodeCell`, `LawCell`, `ProofCell`, `Plot2DCell`, `Plot3DCell`, `CircuitSchematicCell`, `LayoutViewportCell`, `SliderWidgetCell`, `ContractEscrowCell`) and read-only projection adapters over `Obend/Hardware/*` (`projectSchematic`, `projectLayoutViewport`, `projectTimingCone`, `projectTileFabric`).
  - `Obend/FFI/Exports.lean`: Clean `@[export]` C-ABI surface (`obend_vault_open`, `obend_notebook_apply_op`, `obend_cell_set_dial`, `obend_tactic_reflect`, `obend_viewport_render_frame`) for the thin Rust `wgpu` native shell.

### WS 23: Recursive Inductives in `Lower`, 2nd/3rd Futamura Specialization & the Silicon Lean Elaborator
- **Specification**: [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md).
- **Stages**:
  1. **Stage A (`Obend/Lower/Inductive.lean`)**: Extend `Obend/Lower/Fragment.lean` from finite non-recursive inductives (`Bool`, `Prod`, `And`, `Eq`) to **recursive user inductives** (`Lean.Level`, `Lean.Expr`, `Lean.Syntax`, `Obend.Core.Term`, `List`, `Array`, `String`) mapped to `Core4` `Term.ind` / `Term.ctor` / `Term.matchE` / `Term.recConst`, plus an LCNF (`Lean.Compiler.LCNF`) bulk-ingestion bridge (`lcnf_to_core4_sound`).
  2. **Stage B (`Obend/Leaf/Futamura.lean`)**: Extend `Obend/Leaf/Flatten.lean` with **static data-pin specialization** (inlining known environment tables and unfolding recursive lookups on static constructors) and lower `Flatten.lean` *into `Core4` itself* to realize the **2nd and 3rd Futamura projections** (`futamura2_self_specialize_sound`).
  3. **Stage C (`Obend/Hardware/LeanKernelTile.lean` / Read-Only Adapter)**: Lower the pure Lean 4 kernel (`Lean4Lean`: `whnf`, `isDefEq`, `check`) and pure `Lean.Elab` (`simp`, typeclass synthesis) through `Core4` $\to$ `Leaf.Book` $\to$ `BendTT` $\to$ `ReductionMachine` eFPGA `AutomatonTile`s, using `specSlot` + `ICAP` Glitch-Free Dynamic Partial Reconfiguration to bake imported `Environment` constants directly into LUTs with 1-cycle fallback (`moved_pin_blocks`).

---

## Part III — Kernel & Subsystem Hardening Frontiers (`G1` – `G6`)

Detailed theorem targets in [`METATHEORY.md` §3.1](METATHEORY.md):
- **`G1` (Unconditional Tick Completeness & Linear `deepen`)**: Discharge `CostIndexedCompleteness c` across unbounded closures (`Obend/Core/Proofs/TickCost.lean`) and prove `runBounded_mono` for linear-time `Judge.deepen` (`Obend/Judge/Cost.lean`).
- **`G2` (Ordered C4 & Stable Kind Identity)**: Prove `OrderedPresentationInvariant` (`Obend/Spec/C4.lean`), add explicit stable kind names (`record Mile as "units/mile"`), prove cross-registry `effectiveOf` agreement, and unify `Vault/Law.kindChain` with `Obend.Kind`.
- **`G3` (Per-Field Graded Record Quantities)**: Extend `Term.split` with per-field graded $\Sigma^\otimes / \Sigma^\&$ record quantities (`Obend/Core/Proofs/Aggregate.lean`) and machine-level heap-address linear conservation.
- **`G4` (Chained World Roots & Impact Binding)**: Chain ledger/world view roots via an MMR/hash chain, bind `impact@1` receipts to the world root in `obend verify --world`, and unify `Ledger.Register` with `Run.Shared` (`jrun`).
- **`G5` (External Certificate Judges & Activity Rebase)**: Register `Std.Tactic.BVDecide.LRAT.check` alongside `Obend/Judge/Lrat.lean`, add VeriPB/SMT formats, and prove `rebase` (`deepen`/`moreTicks`) totality via activity simulation (`Obend/Run/Adapter.lean`).
- **`G6` (Open Vtable Residual Check)**: Add `SuperOnlyProjected` static check and no-residual-`super` theorem for open vtable flattening (`Obend/Leaf/Flatten.lean`).
