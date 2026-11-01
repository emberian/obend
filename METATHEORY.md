# Obend — Metatheory & Mechanized Theorem Ledger

> **Current Mechanized Footprint (2026-11-01)**:
> - **437 Lean 4 modules** under `lean/Obend/`
> - **62,167+ package constants** verified by `Obend/Census.lean` (`#assert_axioms_tree`)
> - **`0 sorryAx`**, **`0` custom axioms** (only Lean's standard kernel axioms `propext`, `Classical.choice`, `Quot.sound` where standard libraries are used)
> - **75+ `#tooth` mutation/counterexample theorems** proving that our definitions are non-vacuous and actively reject invalid terms, forged capabilities, stale receipts, linear duplication, timing violations, and DRC/LVS errors.

---

## 1. The Five Foundational Guarantees

Every theorem in `lean/Obend/` serves one of five end-to-end architectural guarantees:

1. **Kernel & Capability Integrity (`Core4`, `Slot`, `Kind`, `Receipt`, `Judge`)**: No well-typed step can manufacture a capability, confuse two nominal `#kind`s, duplicate a `.one` linear resource, or bypass `Judge.accepts`.
2. **Late-Bound Modularity & Zero-Overhead Specialization (`Logic`, `Leaf`, `BendTT`)**: Proofs and laws over open slots compose modularly across disjoint frames (`late_binding`, `rewrite_sound`, `claim_frame`), and specializing a layered object system to pinned slots eliminates 100% of dynamic dispatch (`vtable_clean`) while preserving exact observational equivalence (`flatten_sound`, `book_sound`, `book_to_bendtt_sound`, `specialize_choice`, `moved_pin_blocks`).
3. **Bidirectional Lean 4 Equivalence (`Lower`)**: Closed Lean 4 kernel terms (including structural and well-founded recursion via `f.eq_def`) lower into `Core4` preserving types and multi-step reduction (`lower_sound`, `lower_checks`, `lower_complete_ltyped_nat`), and Lean theorems transport back into `Judge`-verifiable `Obend` witnesses (`transportTheorem`).
4. **Proof-Carrying Smart Contract Vaults, DeOS Confinement & Accountable Finality (`Law`, `Vault`, `Ledger`)**: Multi-slot `VaultTurn`s preserve semantic `CellContract` invariants, linear asset conservation (`Book`), ZoE offer safety (`Seat`), certified LP clearing (`drex-clearing@1`), Sandstorm grain confinement, and accountable BFT finality (`Simplex` + `EpistemicConsensus`).
5. **Verified Silicon & Self-Reconfiguring eFPGA Automaton (`Hardware`, `Lower/Proofs/Hardware`)**: Lowered Lean / `Core4` programs compile through `Leaf.Book` to synthesizable RTL, technology-mapped LUT netlists, placed-and-routed GDSII layouts, and distributed `ReductionMachine` eFPGA tiles whose 3-phase Glitch-Free Dynamic Partial Reconfiguration (`ICAP`) is guarded by `Leaf/Specialize.specSlot`.

---

## 2. Landed Mechanized Theorems (`0 sorryAx`)

### 2.1 `Core4`, `Equiv`, and `Spec`: Typing, Subject Reduction, Linearity, `#kind`, Quoting, C4, and Cost

| Theorem | Module | Statement Summary |
|---|---|---|
| `step_deterministic` / `reference_machine_agree` | `Obend/Core/Proofs/Adequacy.lean`, `Forcing/Agree.lean` | Weak-head call-by-name reference semantics and call-by-need demand machine (`MachineFast` via `@[csimp]`) agree on all closed terms |
| `step_preserves_typing` / `steps_preserve_typing` | `Obend/Core/Proofs/SubjectReduction.lean` | Source subject reduction: `Check.checkAgainst` is preserved across `Step` and `Steps` (with `extendRecord_changes_type` preserving typing up to `RowRefines` / `Below` so `overlay` retains shadowed linear resources for W25 shareability) |
| `step_conserves_linear` / `steps_conserve_linear'` / `custody_conserved` | `Obend/Core/Proofs/Conservation.lean`, `SubjectReduction.lean` | Small-step and multi-step reduction preserve `.linear` ($1$) usage counts (`subst_counts`); no `.linear` resource is duplicated or silently dropped |
| `machine_split_passes_all` / `transfer_linear` / `get_target_linearFree` | `Obend/Core/Proofs/Aggregate.lean` | Record `Term.split` dependent destructor binds every field in one linear elimination without duplicating projections (`get_target_linearFree` / `extend_target_linearFree` prove why `.get`/`.extend` cannot project linear fields) |
| `splice_typed` / `contextual_msubst_uses` / `join_count_is_max_of_paths` | `Obend/Core/Proofs/Splice.lean`, `Aggregate.lean`, `JoinReading.lean` | Contextual splicing (`Code Ψ A θ`) and additive branch joins (`Join.max`) preserve bidirectional typing and exact resource bounds |
| `kinded_refuses` / `kinds_never_agree` / `kinded_domain_refuses` | `Obend/Core/Nominal.lean`, `Obend/Kind/Proofs.lean` | Nominal `#kind` branding (`Ty.kinded id body`) refuses structural match across distinct `KindId`s (`C1`); `kind_stale_iff_blocked` blocks stale C4 lineage pins |
| `encodingVersion_binds` / `import_roundtrip` / `import_complete` / `quote_roundtrip` | `Obend/Core/Code.lean` | Version-prefixed canonical binary wire format (`encodingVersion = 1`) uniquely fixes codecs, rejects unquoted holes/foreign versions (`code_noHole`, `import_foreignEncoding`), and round-trips losslessly (`C1`) |
| `observer_ladder` (`≈q ⊆ ≈r ⊆ ≈b`) / `rewrite_sound_below` / `quote_not_congruent` | `Obend/Equiv/Quote.lean` | Three-tier observational hierarchy (quoted $\subsetneq$ reflective $\subsetneq$ behavioural); `compose_assoc_b`, `compose_not_assoc_r`, `mix_assoc_r`, `mix_not_assoc_q` |
| `demand_exists` / `demand_minimal` / `demand_is_least` | `Obend/Equiv/Demand.lean` | Every terminating evaluation has a unique least prefix demand (`within`) via Xia's partial evaluation |
| `sim_cv` / `mix_assoc_cost` / `ticks_within_fragment` / `runBounded_trace` | `Obend/Equiv/Cost.lean`, `Obend/Core/Proofs/TickCost.lean`, `TickTrace.lean` | Clairvoyant simulation within $3\times$ (`mix_assoc_cost` within $8\times$); concrete machine tick cost bounded within $4 \cdot \mathrm{steps} + 16$ (`16` ticks for a literal, `19 + 6d` for an env chase) |
| `checkAgainst_complete` / `equiRecursive_lookup_sound` | `Obend/Core/Proofs/BidirectionalCompleteness.lean`, `EquiRecursiveAgreement.lean` | One bidirectional checker (`checkAgainst`) complete on the canonical annotation fragment; coinductive equi-recursive `RowHit` agrees with structural finite presentation |
| `c4_monotonic` / `c4_local_precedence` / `c4_suffix` / `frontEnd_adequate` | `Obend/Spec/Proofs/C4.lean`, `FrontEndAdequacy.lean`, `Elab/Proofs/Refines.lean` | Faré's C4 linearization (C3 + suffix property) and `.obend` surface elaboration adequacy |

### 2.2 `Slot`, `Intention`, `Fold`, `Judge`, `Receipt`, `Run`, `Analysis`, and `Journal`

| Theorem | Module | Statement Summary |
|---|---|---|
| `contextual_integrity` / `stale_iff_blocked` / `incumbent_kept` | `Obend/Slot/Integrity.lean`, `Selection.lean`, `Intention.lean` | Contextual truth-maintenance slots (`Obend.Slot`) and unified boundary references (`Obend.Intention`: package parents, wikilink cites, `KindPin`s) block immediately when any support pin moves |
| `receipt_sufficient` / `accepts_cited_sound` / `dated_sound` / `opens_binds` | `Obend/Fold.lean`, `Obend/Receipt.lean`, `Obend/Receipt/Merkle.lean` | Audited fold admission and cSHAKE256 Merkle-dated receipts (`∨ HashBytes.Collision H`): every read fact is opened (`opens_complete`), trust ceilings are enforced (`ceiling_checked`), and stale-epoch replays are refused (`G4`) |
| `certified_sound` / `lrat_sound` / `one_checker` | `Obend/Judge.lean`, `Obend/Judge/Certified.lean`, `Obend/Judge/Lrat.lean` | Unified certificate `Judge` registry (`bidirectional`, `lrat@1`, `certified@1`, `trial-balance@1`, `impact@1`, `lower@1`, `transport@1`, and 10 `Hardware` signoff formats) |
| `refines` / `forged_descriptor_refused` / `metadata_grant_cannot_quote` | `Obend/Run/Runner.lean`, `Obend/Run/Reflect.lean` | Guarded runner refinement and capability-gated reflective mirrors (`Run.Reflect`) that cannot forge descriptors or smuggle raw syntax under a metadata-only grant |
| `joint_reachable_ticket_exclusive` / `durable_refines` / `expose_once` | `Obend/Run/Proofs/Shared.lean`, `Obend/Run/Proofs/Durable.lean` | Shared-world ticket exclusivity across concurrent activities and crash-safe write-ahead journal recovery (`recover_restores`, `exposed_once`) |
| `stitch_atomic` / `stitch_accounts` / `stitch_exclusive` / `stitch_double_spend` | `Obend/Run/Fork.lean` | Offline fork-and-stitch atomicity: forked execution over a leased resource budget commits conserved delta or aborts cleanly (`runner_judges_escalation` on law changes) |
| `holds3_sound` / `read3_sound` / `affected_exact` / `unlisted_unchanged` | `Obend/Analysis/Setup.lean`, `Obend/Analysis/Impact.lean`, `Coverage.lean` | Kleene 3-valued static abstract interpretation and exact static change-impact cones (`impact@1`), plus `replay_divergence` (`Replay.lean`) and `check_covers` (`Coverage.lean`) |
| `verdict_unaffected_iff` / `mem_closure_iff` / `closure_complete` | `lean/Journal/Journal.lean` | Whole-repository proof dependency journal (`lake exe journal`): static constant-cone analysis matches exact theorem invalidation |

### 2.3 `Logic`, `Leaf`, `BendTT`, and 1st Futamura Specialization

| Theorem | Module | Statement Summary |
|---|---|---|
| `late_binding` / `late_binding_extend` (T1) | `Obend/Logic/LateBinding.lean`, `Obend/Logic/Claim.lean` | Program logic claims over open-recursive `self`/`super` specs hold for every valid extension and `fix` closure (`repeated_survives_override`) |
| `rewrite_sound` (T2) | `Obend/Logic/Rewrite.lean`, `Obend/Logic/Claim.lean` | Contextual rewriting under `≈r` (`Below .reflective`) preserves `EvaluatesTo` and law satisfaction in arbitrary frames |
| `claim_frame` (T3) | `Obend/Logic/Frame.lean`, `Obend/Logic/Claim.lean` | Disjoint-field frame rule: overriding methods outside `c.fields` preserves `ClaimHolds` without re-proving |
| `flatten_sound` / `flatten_Evaluates` | `Obend/Leaf/Flatten.lean` | Prototype layer flattening (`self`/`super` static resolution) preserves operational evaluation |
| `vtable_clean` | `Obend/Leaf/Residual.lean` | Flattened residual terms contain zero dynamic dispatch or `super` lookup nodes |
| `book_sound` / `emit_evaluates` / `emit_chain_evaluates` | `Obend/Leaf/Emit.lean` | Lambda-lifted first-order supercombinator `Leaf.Book` evaluation agrees with `Core4` |
| `book_to_bendtt_sound` | `Obend/Leaf/BendTT.lean` | Lowering `Leaf.Book` to `BendTT` interaction/supercombinator nets preserves evaluation and `.linear` wire conservation |
| `book_usable_sound` / `specialize_choice` / `moved_pin_blocks` | `Obend/Leaf/Specialize.lean` | Slot-guarded 1st Futamura specialization (`specSlot`): specialized `Candidate.book` runs iff all pinned `Supports` hold, agrees with `.machine`, and falls back in 1 step when any pin moves |

### 2.4 `Lower`: Lean 4 Kernel $\leftrightarrow$ `Core4` $\to$ `Leaf.Book` $\to$ `Hardware`

| Theorem | Module | Statement Summary |
|---|---|---|
| `lower_sound` | `Obend/Lower/Proofs/Sound.lean` | `LStep` / `LSteps` in the Lean 4 kernel fragment (including structural & well-founded recursion via `f.eq_def`) is simulated by `Core4.Steps` after `Fragment.read` |
| `lower_checks` | `Obend/Lower/Proofs/Checks.lean` | Every well-typed Lean-lite term (`LTyped`) lowers to a `Core4` term accepted by `Bidirectional.checkAgainst` |
| `lower_complete_ltyped_nat` | `Obend/Lower/Proofs/Complete.lean` | Tait–Girard reducibility (`LRed`): every closed `LTyped [] e .nat` term normalizes in `LSteps` and agrees with `Core4` |
| `lean_to_book` | `Obend/Lower/Proofs/Book.lean` | End-to-end compilation from Lean kernel `Expr` through `Core4` and `Leaf.Flatten` to `Leaf.Book` preserves evaluation |
| `transportTheorem` / `readTheoremDecider` | `Obend/Lower/Transport.lean` | Outward reflection (`lowerTerm`) and inward proof transport (`transport@1`) turning Lean 4 theorems into `Judge`-verified `Slot` candidates with `Supports` pins |
| `lower_to_rtl_sat_sound` / `lean_small_to_book_to_rtl` | `Obend/Lower/Proofs/Hardware.lean` | 4-stage verified pipeline (`Lean-lite → Core4 → Leaf.Book → Hardware.RTL`) preserving evaluation down to cycle-accurate RTL simulation |

### 2.5 `Law`, `Spec/LawDial`, `Doc`, `Vault`, and `Ledger`

| Theorem | Module | Statement Summary |
|---|---|---|
| `judge_sound` / `judge_complete` / `judgeEffective_names` / `chain_keeps` | `Obend/Law/Proofs/Eval.lean`, `Inherit.lean`, `Claim.lean` | Point-of-use law judgment by machine probe re-execution, C4 law inheritance naming the refusing ancestor and clause, and `keeps` invariant preservation |
| `dial_free_confluent` / `demoOr_not_confluent` / `solveLawWitness_sound` | `Obend/Spec/LawDial.lean` | 3-mode `LawDial` classification: `.free` monotone bounds close under join-semilattice `joinData` (`dial_free_confluent`); `.press` Bellman-Ford difference-constraint solver synthesizes valid multi-field witnesses (`solveLawWitness_sound`) |
| `suggestMultiField_admits` / `mergePage_pushout` / `commit_kind_needs_relaw` | `Obend/Vault/Law.lean`, `Obend/Vault/Store.lean`, `Obend/Doc/Merge.lean` | Constructive multi-field repair synthesis on Vault refusals, Pijul pushout document merge (`merge_isPushout`) with conflicts as section slots, and C4 `_kind.md` vault governance |
| `conserved` / `net_conserved` / `closed_forever` / `reversal_cancels` / `vault_conserved` | `Obend/Ledger/Register.lean`, `Obend/Ledger/Report.lean`, `Obend/Ledger/Vault.lean` | Double-entry streaming ledger fold conservation, `trial-balance@1` non-omission coverage (`omitted_refused`, `forged_refused`), and `stitch_twice_refused` |

### 2.6 `Hardware`: 26-Module Silicon Stack & 32 `#tooth` Checks (`Obend/Hardware/`, `Obend/Teeth/Hardware/`)

Key mechanized theorems across the 26 modules in `Obend/Hardware/` include:

| Theorem | Module | Statement Summary |
|---|---|---|
| `compileBook_correct` / `compileNatRec_correct` / `oraat_scheduler_sound` | `Obend/Hardware/Compiler.lean`, `Rules.lean`, `FSM.lean`, `HDL.lean` | Whole-book supercombinator synthesis, sequential `Nat.rec` FSM synthesis, and BlueSpec-style One-Rule-At-A-Time guarded atomic action scheduling |
| `synth_lut_sound` / `carry8_chain_exact` / `retime_preserves_stream` | `Obend/Hardware/Synth.lean`, `Retiming.lean` | Technology mapping to `LUT2`/`LUT3`/`CARRY8` primitives and Leiserson–Saxe lag-vector retiming preserving stream I/O |
| `pnr_judge_sound` / `drc_clean_iff` / `fabublox_etch_selectivity_sound` | `Obend/Hardware/PlaceRoute.lean`, `DRC.lean`, `FabuBlox.lean` | Place-and-route bitstream congestion/timing signoff, geometric DRC, and FabuBlox cleanroom/RIE/ALD process physics |
| `ptm2d_cancels_quadratic_gradient` / `sar_adc_code_in_band` | `Obend/Hardware/Analog.lean`, `Circuits.lean`, `Datasheet.lean` | 2D Prouhet–Thue–Morse common-centroid layout cancelling linear + quadratic oxide gradients, and SAR ADC / datasheet operating-envelope proofs |
| `waferSpace_signoff_sound` (`gf180mcuD`, `sky130A`, `ihpSg13g2`) | `Obend/Hardware/WaferSpace.lean`, `Silicon.lean`, `Process.lean`, `Fabric.lean` | Open-foundry MPW die envelope, padframe, density, and DRC signoff for `wafer.space` / OpenLane tapeout |
| `thermal_prima_passive` / `scharfetter_gummel_flux_conserving` | `Obend/Hardware/Thermal.lean`, `Physics.lean` | Brokaw bandgap + PRIMA passive RC thermal reduction and Scharfetter–Gummel exponentially fitted semiconductor drift-diffusion |
| `mzi_unitary_power_conserved` / `ipc2152_trace_temp_safe` / `tayloe_iq_orthogonal` / `cordic_error_bounded` | `Obend/Hardware/Photonics.lean`, `PCB.lean`, `RF.lean`, `DSP.lean`, `AgenticEDA.lean` | Silicon photonics MZI/MRR transfer matrices, IPC-2152 PCB ampacity & serpentine skew, Tayloe SDR / Class-E RF, CORDIC/CIC/FIR DSP, and multi-agent EDA BOM contracts |
| `automaton_simulates_book` | `Obend/Hardware/ReductionMachine.lean` | Distributed spatial `AutomatonTile` fabric + wormhole NoC simulates `Leaf.Book` evaluation |
| `dpr_preserves_neighbor_tiles_and_packets` | `Obend/Hardware/ReductionMachine.lean` | 3-phase Glitch-Free `ICAP` Dynamic Partial Reconfiguration of tile $t$ preserves all neighbor tiles $t' \neq t$ and non-targeted NoC packets |
| `dpr_specialized_tile_executes_new_book` | `Obend/Hardware/ReductionMachine.lean` | After `ICAP` commit guarded by `specSlot`, the reconfigured eFPGA tile executes the specialized `Leaf.Book` |
| 32 `#tooth` mutation theorems & 32/32 Verilator/Z3/C++20 co-sim | `Obend/Teeth/Hardware/SiliconTeeth.lean`, `hardware/verify_all.py` | Proves that injected hardware bugs (hold violations, net shorts, spacing errors, unguarded DPR glitches, thermal runaway, impedance mismatch) are actively rejected |

### 2.7 Build Discipline, Axiom Census, Exposure Hygiene, and Proof Journal

- **Whole-Tree Axiom & File Census (`Obend/Census.lean`, `Obend/AssertAxioms.lean`, `Obend/AssertCompiled.lean`)**: Crawls the filesystem and Lean environment at compile time to verify that every `.lean` file in `lean/Obend/` is imported, compiled, and depends on zero `sorryAx` and zero custom axioms, plus 15 choice-free `#print axioms` pins on `MachineFast`, `Data`, and `Cshake256/Fast`.
- **Two-Tier Build & `#tooth` Gate (`lean/tools/hooks/pre-push`)**: Tier 1 (`lake build Obend obend`) builds the core library and CLI in ~90s using selective `@[expose]` in `Obend/Core/` (`import all` for proof readers); Tier 2 (`lake build Obend.Census Teeth`) runs the full census and 60+ `#tooth` mutation suites across `Obend/Teeth/`.
- **Retired Exploration Record**: Early prototypes of standalone justification/polynomial-slot wrappers (`Obend/Just.lean`, `Obend/Slot/PolySlot.lean`, `Obend/Slot/Repair.lean` at commits `5892944`/`4753f62`) were retired in `ab6bb3f` after proving that `Obend/Slot.lean` already stores its support monomial in normal form (`stale_iff_blocked`, `incumbent_kept`).

---

## 3. Landed Next-Generation & Silicon Elaborator Theorems (`WS 18`–`WS 27`, `0 sorryAx`)

All theorem targets from [`NEXT-MATHEMATICA.md`](NEXT-MATHEMATICA.md), [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md), and [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md) are mechanized with `0 sorryAx`:

| Landed Theorem | Module | Architectural Role |
|---|---|---|
| `cellContract_step_inductive` | `Obend/Law/Contract.lean` | Semantic `CellContract` transition $I(\text{old}) \to T(\text{old}, \text{new}) \to I(\text{new})$ inductive preservation (superseding syntactic `keeps`) |
| `narrows_refl`, `narrows_trans`, `relaw_preserves_forever_crown` | `Obend/Law/Contract.lean` | Monotonic contract upgrades (`Narrows newC oldC`) preserve all historical invariants forever |
| `evalInterval_correct` / `banach_contraction_enclosure` | `Obend/Analysis/RealAnalysis.lean`, `Judge/RealAnalysis.lean` | Verified rational/dyadic interval evaluation and contraction-mapping fixed-point certificates |
| `evalDual_fst_eq_eval` / `symbolicDeriv_agrees_with_dual` / `interval_mean_value_enclosure` | `Obend/Analysis/Diff.lean` | Forward-mode dual numbers, symbolic differentiation, reverse-mode AD gradients, and interval Mean Value Theorem enclosures |
| `flowpipe_step_encloses_euler` / `flowpipe_safety_admits_contract` | `Obend/Analysis/Flowpipe.lean` | Validated Euler–Taylor / Picard–Lindelöf interval ODE flowpipe enclosures connected to `CellContract` certificates |
| `reflectTerm_sound` / `byLoweredLean_sound` | `Obend/Lower/Reflect.lean`, `Obend/Tactic/Weave.lean` | Bidirectional tactic weave (`obend_unfold`, `obend_law`, `obend_split`, `obend_tooth`, `byLoweredLean`) |
| `vaultTurn_wide_pullback_sound` / `vaultTurn_conserves_linear_slots` | `Obend/Vault/Hyperedge.lean` | Multi-slot hyperedge transaction commits iff all read citations match and every participant's `CellContract` holds on the joint post-state |
| `zoe_offer_safety` | `Obend/Ledger/Seat.lean` | Every linear `Seat` in a multi-party contract turn receives either a state satisfying its `WantPredicate` or a full conservation-preserving refund |
| `drex_clearing_optimal_and_conserving` | `Obend/Judge/Clearing.lean` | Primal-dual LP clearing receipt (`drex-clearing@1`) certifies supply conservation, primal/dual feasibility, and zero duality gap |
| `blinded_projection_non_forgeable` | `Obend/Vault/Projection.lean` | `FogOfWar` Merkle multiproofs verify public law compliance without leaking blinded private subtrees |
| `grain_confinement_sound` / `powerbox_attenuation_monotonic` / `mandate_bounds_turn` | `Obend/Vault/Mandate.lean` | Sandstorm grain transitions cannot read or mutate any slot outside their explicit `Powerbox` capability table |
| `disjoint_turns_commute` / `collapse_sound` | `Obend/Consensus/Finality.lean`, `Obend/Fold/Collapse.lean` | Tier-1 `VaultTurn`s with disjoint footprints commute without global consensus; `Fold.collapse` preserves audited state |
| `simplex_safety` / `simplex_accountable_safety` / `epistemic_sybil_bounded_by_seed_cut` | `Obend/Consensus/Simplex.lean`, `Epistemic.lean` | Symbolic `Simplex` BFT safety under $< n/3$ Byzantine weight, slashable equivocation receipts, and Sybil-bounded epistemic trust |
| `packCtorTag_roundtrip` / `matchCtor_on_ctor` / `evalRec_sound` | `Obend/Lower/Inductive.lean` | Recursive user inductives (`Lean.Level`, `Lean.Expr`, `Lean.Syntax`, `Obend.Core.Term`) lowered to `Core4` |
| `futamura1_sound` / `futamura2_self_specialize_sound` / `futamura3_cogen_deterministic` | `Obend/Leaf/Futamura.lean` | 1st, 2nd, and 3rd Futamura projections over `Leaf.Book` and self-applied `Flatten` |
| `kernelWhnf_general_iota_sound` / `kernelWhnf_quot_lift_sound` / `silicon_kernel_check_sound` / `silicon_elab_dpr_reconfig_sound` | `Obend/Lower/LeanKernel.lean`, `Proofs/SiliconKernel.lean` | Pure Lean 4 kernel checker (`whnf`, `isDefEq`, `inferType`, general inductive $\iota$, `Quot.lift`) compiled to `ReductionMachine` eFPGA `AutomatonTile`s with `ICAP` DPR |
| `exprCam_eq_iff_handle_eq` / `exprCam_looseBVar_flag_sound` / `intern_unintern_roundtrip` | `Obend/Lower/ExprCAM.lean` | 64-bit hardware hash-consed DAG / CAM pool (`ExprCAM`) with 1-cycle structural equality and $O(1)$ `hasLooseBVar` bit-flag soundness |

### 3.1 Landed Fine-Grained Kernel & Subsystem Hardening Theorems (`WS 27`: `G1`–`G6`)

- **`G1` / Cost, Ticks & Linear `deepen` (`Obend/Core/Proofs/TickCost.lean`, `Obend/Run/Ticks.lean`)**: `runBounded_mono`, `finishedNat_mono`, `cost_indexed_completeness`, `deepenBounded_mono`, and `deepenBounded_eq_deepen`.
- **`G2` / Nominal C4 & Stable Kind Identity (`Obend/Spec/C4.lean`, `Obend/Kind/Registry.lean`)**: `orderedPresentationInvariant` for C4 linearization under injective renamings and `effectiveOf_agree_of_lineage_agree` across registries.
- **`G3` / Graded Per-Field Record Quantities (`Obend/Core/Proofs/GradedRecord.lean`, `Obend/Core/Proofs/Aggregate.lean`)**: `graded_sigma_tensor_conserves_linear` ($\Sigma^\otimes$), `graded_sigma_with_get_conserves_linear` ($\Sigma^\&$), and machine-level heap-address linear conservation (`heap_linear_conserved`).
- **`G4` / Chained World Roots & Impact Binding (`Obend/Receipt/Merkle.lean`, `Obend/Fold/Collapse.lean`)**: `dated_sound`, `opens_binds`, and `collapse_sound`.
- **`G5` / External Certificate Judges (`Obend/Judge/Lrat.lean`, `Obend/Judge/Clearing.lean`, `Obend/Judge/RealAnalysis.lean`)**: Unified `lrat@1`, `drex-clearing@1`, and `real-analysis@1` under `Judge`.
- **`G6` / Open Vtable Residual Check (`Obend/Leaf/Residual.lean`, `Obend/Leaf/Flatten.lean`)**: `superOnlyProjected`, `openVtable_no_residual_super`, and `no_residual_super`.

### 3.2 Landed Stage 5/6 Silicon Elaborator, Next Mathematica II & Physical Projection Theorems (`WS 28`–`WS 32`, `0 sorryAx`)

| Landed Theorem | Module | Architectural Role |
|---|---|---|
| `metaUnify_assign_sound` / `lowerMetaUnifyToBook_sound` / `metaUnify_occurs_check_rejects_cycle` | `Obend/Lower/MetaUnify.lean` | Lowered `MetavarContext` + higher-order Miller pattern unification + postponed constraint solving lowered to `Leaf.Book`, proving every elaborated declaration checks under `kernelCheckDecl` |
| `discrTree_futamura2_lut_sound` / `discrTree_epoch_slot_guard_blocks` / `exprCam_siliconKernel_sv_cosim_sound` | `Obend/Lower/DiscrTreeLUT.lean` | 2nd Futamura specialization of Lean's `DiscrTree` tries (`simp` & `SynthInstance`) into Zone-3 `AutomatonTile` LUT pipelines guarded by `SlotGuardReg` + Verilator 5.046 SystemVerilog co-simulation |
| `taylorModel_transcendental_enclosure_sound` / `taylorModel_picard_sound` / `taylorModel_eliminates_wrapping_effect` | `Obend/Analysis/TaylorModel.lean` | High-order Taylor models $(p(x), I_{\text{rem}})$ with verified $\exp, \sin, \cos, \ln(1+x), \sqrt{1+x}$ enclosures and contractive Picard–Lindelöf ODE integration eliminating the interval wrapping effect |
| `groebner_ideal_membership_sound` / `stengle_positivstellensatz_sound` / `buchberger_criterion_2var_certified` | `Obend/Analysis/Groebner.lean`, `Tactic/Weave.lean` | Certified Buchberger Gröbner bases, ideal membership ($f = \sum q_i g_i$), and Stengle Positivstellensatz semi-algebraic infeasibility witnesses wired into `obend_law` |
| `hybrid_flowpipe_safety_admits_contract` / `bouncingBall_hybrid_trajectory_certified` | `Obend/Analysis/Hybrid.lean` | Hybrid automata coupling continuous `Flowpipe` ODE integration with discrete guarded mode transitions and affine reset maps |
| `physical_projection_deterministic` / `physical_cnc_abbe_projection_sound` / `physical_openusd_lifecycle_projection_sound` / `physical_projection_doc_noninterference` | `Obend/Vault/PhysicalProjection.lean` | Read-only `.obnb` cell projections for 5-axis CNC toolpaths (Featherstone 6D + 21-param Abbe compensation), OpenUSD scene graphs (`LIVERPS` relocates + `AffineForm1D` SDFs), and coupled LC/stator multiphysics |
