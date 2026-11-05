# Obend — Metatheory & Mechanized Theorem Ledger

> **What is checked, and where to read it (2026-11-04)**: the census (`lean/Obend/Census.lean`, tier 2:
> `lake build Obend.Census Teeth Tests`) refuses any constant that rests on `sorryAx` or a declared
> axiom (only `propext`, `Classical.choice`, `Quot.sound` pass; `native_decide`/`bv_decide` are
> compiled trust, counted per directory and each re-run by `#assert_compiled`), and prints, per
> directory, how many theorems quantify over something, how many are closed statements (fixtures
> that should be `example`s), how many `example`s and how many `#tooth` mutation commands there are.
> This document carries no totals: a count of theorems averaged real metatheory with fixtures and
> was retired as harmful (`review/DECISIONS-20261031.md`, `review/EXPERT-lean-proof-engineering-20261103.md`).
> The theorem names below are checked against the environment by `#docs_census`; a name that is not
> in the tree fails the census.

---

## 1. The Five Foundational Guarantees

Every theorem in `lean/Obend/` serves one of five end-to-end architectural guarantees:

1. **Kernel & Capability Integrity (`Core4`, `Slot`, `Kind`, `Receipt`, `Judge`)**: No well-typed step can manufacture a capability, confuse two nominal `#kind`s, duplicate a `.one` linear resource, or bypass `Judge.accepts`.
2. **Late-Bound Modularity & Flattening (`Logic`, `Leaf`)**: Proofs and laws over open slots compose modularly across disjoint frames (`late_binding`, `rewrite_sound`, `claim_frame`); flattening a closed composition removes `super` and the mix chain (`vtable_clean`) and preserves `≈b` (`flatten_sound`, `book_sound`); the emitted book is a slot candidate whose supports are the whole layer codes (`specialize_choice`, `moved_pin_blocks`).
3. **Bidirectional Lean 4 Equivalence (`Lower`)**: Closed Lean 4 kernel terms (including structural and well-founded recursion via `f.eq_def`) lower into `Core4` preserving types and multi-step reduction (`lower_sound`, `lower_checks`, `lower_complete_ltyped_nat`), and Lean theorems transport back into `Judge`-verifiable `Obend` witnesses (`transportTheorem`).
4. **Proof-Carrying Smart Contract Vaults, DeOS Confinement & Accountable Finality (`Law`, `Vault`, `Ledger`)**: Multi-slot `VaultTurn`s preserve semantic `CellContract` invariants, linear asset conservation (`Book`), ZoE offer safety (`Seat`), certified LP clearing (`drex-clearing@1`), Sandstorm grain confinement, and accountable BFT finality (`Simplex` + `EpistemicConsensus`).
5. **Verified Silicon & Self-Reconfiguring eFPGA Automaton (`Hardware`, `Lower/Proofs/Hardware`)**: Lowered Lean / `Core4` programs compile through `Leaf.Book` to synthesizable RTL, technology-mapped LUT netlists, placed-and-routed GDSII layouts, and distributed `ReductionMachine` eFPGA tiles whose 3-phase Glitch-Free Dynamic Partial Reconfiguration (`ICAP`) is guarded by `Leaf/Specialize.specSlot`.

---

## 2. Landed Mechanized Theorems

### 2.1 `Core4`, `Equiv`, and `Spec`: Typing, Subject Reduction, Linearity, `#kind`, Quoting, C4, and Cost

| Theorem | Module | Statement Summary |
|---|---|---|
| `step_deterministic` | `Obend/Core/Proofs/Adequacy.lean`, `Forcing/Agree.lean` | Weak-head call-by-name reference semantics and call-by-need demand machine (`MachineFast` via `@[csimp]`) agree on all closed terms |
| `step_preserves_typing` / `steps_preserve_typing` | `Obend/Core/Proofs/SubjectReduction.lean` | Source subject reduction: `Check.checkAgainst` is preserved across `Step` and `Steps` (with `extendRecord_changes_type` preserving typing up to `RowRefines` / `Below` so `overlay` retains shadowed linear resources for W25 shareability) |
| `step_conserves_linear` / `steps_conserve_linear'` / `custody_conserved` | `Obend/Core/Proofs/Conservation.lean`, `SubjectReduction.lean` | Small-step and multi-step reduction preserve `.linear` ($1$) usage counts (`subst_counts`); no `.linear` resource is duplicated or silently dropped |
| `machine_split_passes_all` / `transfer_linear` / `get_target_linearFree` | `Obend/Core/Proofs/Aggregate.lean` | Record `Term.split` dependent destructor binds every field in one linear elimination without duplicating projections (`get_target_linearFree` / `extend_target_linearFree` prove why `.get`/`.extend` cannot project linear fields) |
| `splice_typed` / `contextual_msubst_uses` / `join_count_is_max_of_paths` | `Obend/Core/Proofs/Splice.lean`, `Aggregate.lean`, `JoinReading.lean` | Contextual splicing (`Code Ψ A θ`) and additive branch joins (`Join.max`) preserve bidirectional typing and exact resource bounds |
| `kinded_refuses` / `kinds_never_agree` / `kinded_domain_refuses` | `Obend/Core/Nominal.lean`, `Obend/Kind/Proofs.lean` | Nominal `#kind` branding (`Ty.kinded id body`) refuses structural match across distinct `KindId`s (`C1`); `kind_stale_iff_blocked` blocks stale C4 lineage pins |
| `encodingVersion_binds` / `import_roundtrip` / `import_complete` / `quote_roundtrip` | `Obend/Core/Code.lean` | Version-prefixed canonical binary wire format (`encodingVersion = 1`) uniquely fixes codecs, rejects unquoted holes/foreign versions (`code_noHole`, `import_foreignEncoding`), and round-trips losslessly (`C1`) |
| `observer_ladder` (`≈q ⊆ ≈r ⊆ ≈b`) / `rewrite_sound_below` / `quote_not_congruent` | `Obend/Equiv/Quote.lean` | Three-tier observational hierarchy (quoted $\subsetneq$ reflective $\subsetneq$ behavioural); `compose_assoc_b`, `compose_not_assoc_r`, `mix_assoc_r`, `mix_not_assoc_q` |
| `demand_exists` / `demand_minimal` / `demand_is_least` | `Obend/Equiv/Demand.lean` | Every terminating evaluation has a unique least prefix demand (`within`) via Xia's partial evaluation |
| `sim_cv` / `mix_assoc_cost` / `ticks_within_fragment` / `runBounded_trace` | `Obend/Equiv/Cost.lean`, `Obend/Core/Proofs/TickCost.lean`, `TickTrace.lean` | Clairvoyant simulation within $3\times$ (`mix_assoc_cost` within $8\times$); concrete machine tick cost bounded within $4 \cdot \mathrm{steps} + 16$ (`16` ticks for a literal, `19 + 6d` for an env chase) |
|  | `Obend/Core/Proofs/BidirectionalCompleteness.lean`, `EquiRecursiveAgreement.lean` | One bidirectional checker (`checkAgainst`) complete on the canonical annotation fragment; coinductive equi-recursive `RowHit` agrees with structural finite presentation |
|  | `Obend/Spec/Proofs/C4.lean`, `FrontEndAdequacy.lean`, `Elab/Proofs/Refines.lean` | Faré's C4 linearization (C3 + suffix property) and `.obend` surface elaboration adequacy |

### 2.2 `Slot`, `Intention`, `Fold`, `Judge`, `Receipt`, `Run`, `Analysis`, and `Journal`

| Theorem | Module | Statement Summary |
|---|---|---|
| `stale_iff_blocked` | `Obend/Slot/Integrity.lean`, `Selection.lean`, `Intention.lean` | Contextual truth-maintenance slots (`Obend.Slot`) and unified boundary references (`Obend.Intention`: package parents, wikilink cites, `KindPin`s) block immediately when any support pin moves |
| `receipt_sufficient` / `accepts_cited_sound` / `dated_sound` / `opens_binds` | `Obend/Fold.lean`, `Obend/Receipt.lean`, `Obend/Receipt/Merkle.lean` | Audited fold admission and cSHAKE256 Merkle-dated receipts (`∨ HashBytes.Collision H`): every read fact is opened (`opens_complete`), trust ceilings are enforced (`ceiling_checked`), and stale-epoch replays are refused (`G4`) |
|  | `Obend/Judge.lean`, `Obend/Judge/Certified.lean`, `Obend/Judge/Lrat.lean` | Unified certificate `Judge` registry (`bidirectional`, `lrat@1`, `certified@1`, `trial-balance@1`, `impact@1`, `lower@1`, `transport@1`, `oracle7-gl-equilibrium@1`, and `Hardware` signoff formats) |
| `refines` / `forged_descriptor_refused` / `metadata_grant_cannot_quote` | `Obend/Run/Runner.lean`, `Obend/Run/Reflect.lean` | Guarded runner refinement and capability-gated reflective mirrors (`Run.Reflect`) that cannot forge descriptors or smuggle raw syntax under a metadata-only grant |
| `joint_reachable_ticket_exclusive` / `durable_refines` / `expose_once` / `checkHyperLaw2NonInterference_sound` / `checkOracle7Equilibrium_sound` | `Obend/Run/Proofs/Shared.lean`, `Obend/Run/Proofs/Durable.lean`, `Obend/Run/HyperLaw.lean` | Shared-world ticket exclusivity across concurrent activities, crash-safe write-ahead journal recovery (`recover_restores`, `exposed_once`), `k=2` relational hyperlaws (`HyperLaw2`), and Gelfond-Lifschitz modal `□` equilibrium (`Oracle7`) |
| `stitch_atomic` / `stitch_accounts` / `stitch_exclusive` / `stitch_double_spend` | `Obend/Run/Fork.lean` | Offline fork-and-stitch atomicity: forked execution over a leased resource budget commits conserved delta or aborts cleanly (`runner_judges_escalation` on law changes) |
| `holds3_sound` / `read3_sound` / `affected_exact` / `unlisted_unchanged` | `Obend/Analysis/Setup.lean`, `Obend/Analysis/Impact.lean`, `Coverage.lean` | Kleene 3-valued static abstract interpretation and exact static change-impact cones (`impact@1`), plus `replay_divergence` (`Replay.lean`) and `check_covers` (`Coverage.lean`) |
| `verdict_unaffected_iff` / `mem_closure_iff` / `closure_complete` | `lean/Journal/Journal.lean` | Whole-repository proof dependency journal (`lake exe journal`): static constant-cone analysis matches exact theorem invalidation |

### 2.3 `Logic` and `Leaf`

| Theorem | Module | Statement Summary |
|---|---|---|
| `late_binding` (T1) | `Obend/Logic/LateBinding.lean`, `Obend/Logic/Claim.lean` | Program logic claims over open-recursive `self`/`super` specs hold for every valid extension and `fix` closure  |
| `rewrite_sound` (T2) | `Obend/Logic/Rewrite.lean`, `Obend/Logic/Claim.lean` | Contextual rewriting under `≈r` (`Below .reflective`) preserves `EvaluatesTo` and law satisfaction in arbitrary frames |
| `claim_frame` (T3) | `Obend/Logic/Frame.lean`, `Obend/Logic/Claim.lean` | Disjoint-field frame rule: overriding methods outside `c.fields` preserves `ClaimHolds` without re-proving |
| `flatten_sound` | `Obend/Leaf/Flatten.lean` | Prototype layer flattening (`self`/`super` static resolution) preserves operational evaluation |
| `vtable_clean` | `Obend/Leaf/Residual.lean` | Flattened residual terms contain zero dynamic dispatch or `super` lookup nodes |
| `book_sound` | `Obend/Leaf/Emit.lean` | Lambda-lifted first-order supercombinator `Leaf.Book` evaluation agrees with `Core4` |
| `bequiv_dataPinSpecialize` / `staticApply_slot_sound` / `specializeDefCode_bequiv_and_halts` | `Obend/Leaf/Static.lean` | Four passes of a bottom-up constant folder are a reduction in context (`t ≈b dataPinSpecialize t`); a term folded at a static argument is a slot candidate with the slot theorems; each definition of `specializeBook B pins` is `≈b` its pinned original. The link-level equivalence of a specialized book is open; `evalBook*` are syntactic normal forms, not runs |
| `book_usable_sound` / `specialize_choice` / `moved_pin_blocks` | `Obend/Leaf/Specialize.lean` | The emitted book as a slot candidate: usable iff every pinned layer code and the composition are structurally equal at the view (`termEq`), kept exactly while usable, else the machine; a blocked read names the moved pins. Decided once before a run; no guard in the machine |

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
| `mergePage_pushout` / `commit_kind_needs_relaw` | `Obend/Vault/Law.lean`, `Obend/Vault/Store.lean`, `Obend/Doc/Merge.lean` | Constructive multi-field repair synthesis on Vault refusals, Pijul pushout document merge (`merge_isPushout`) with conflicts as section slots, and C4 `_kind.md` vault governance |
| `conserved` / `net_conserved` / `closed_forever` / `reversal_cancels` / `vault_conserved` | `Obend/Ledger/Register.lean`, `Obend/Ledger/Report.lean`, `Obend/Ledger/Vault.lean` | Double-entry streaming ledger fold conservation, `trial-balance@1` non-omission coverage , and `stitch_twice_refused` |

### 2.6 `Hardware`: the Silicon Stack & its `#tooth` Checks (`Obend/Hardware/`, `Obend/Teeth/Hardware/`)

Key mechanized theorems in `Obend/Hardware/` include:

| Theorem | Module | Statement Summary |
|---|---|---|
|  | `Obend/Hardware/Compiler.lean`, `Rules.lean`, `FSM.lean`, `HDL.lean` | Whole-book supercombinator synthesis, sequential `Nat.rec` FSM synthesis, and BlueSpec-style One-Rule-At-A-Time guarded atomic action scheduling |
|  | `Obend/Hardware/Synth.lean`, `Retiming.lean` | Technology mapping to `LUT2`/`LUT3`/`CARRY8` primitives and Leiserson–Saxe lag-vector retiming preserving stream I/O |
|  | `Obend/Hardware/PlaceRoute.lean`, `DRC.lean`, `FabuBlox.lean` | Place-and-route bitstream congestion/timing signoff, geometric DRC, and FabuBlox cleanroom/RIE/ALD process physics |
|  | `Obend/Hardware/Analog.lean`, `Circuits.lean`, `Datasheet.lean` | 2D Prouhet–Thue–Morse common-centroid layout cancelling linear + quadratic oxide gradients, and SAR ADC / datasheet operating-envelope proofs |
| `waferSpaceFormat_sound` (`gf180mcuD`, `sky130A`, `ihpSg13g2`) | `Obend/Hardware/WaferSpace.lean`, `Silicon.lean`, `Process.lean`, `Fabric.lean` | Open-foundry MPW die envelope, padframe, density, and DRC signoff for `wafer.space` / OpenLane tapeout |
|  | `Obend/Hardware/Thermal.lean`, `Physics.lean` | Brokaw bandgap + PRIMA passive RC thermal reduction and Scharfetter–Gummel exponentially fitted semiconductor drift-diffusion |
|  | `Obend/Hardware/Photonics.lean`, `PCB.lean`, `RF.lean`, `DSP.lean`, `AgenticEDA.lean` | Silicon photonics MZI/MRR transfer matrices, IPC-2152 PCB ampacity & serpentine skew, Tayloe SDR / Class-E RF, CORDIC/CIC/FIR DSP, and multi-agent EDA BOM contracts |
| `automaton_simulates_book` | `Obend/Hardware/ReductionMachine.lean` | Distributed spatial `AutomatonTile` fabric + wormhole NoC simulates `Leaf.Book` evaluation |
| `dpr_preserves_neighbor_tiles_and_packets` | `Obend/Hardware/ReductionMachine.lean` | 3-phase Glitch-Free `ICAP` Dynamic Partial Reconfiguration of tile $t$ preserves all neighbor tiles $t' \neq t$ and non-targeted NoC packets |
| `dpr_specialized_tile_executes_new_book` | `Obend/Hardware/ReductionMachine.lean` | After `ICAP` commit guarded by `specSlot`, the reconfigured eFPGA tile executes the specialized `Leaf.Book` |
| The `#tooth` mutation theorems & the Verilator/Z3/C++20 co-simulations | `Obend/Teeth/Hardware/SiliconTeeth.lean`, `hardware/verify_all.py` | Proves that injected hardware bugs (hold violations, net shorts, spacing errors, unguarded DPR glitches, thermal runaway, impedance mismatch) are actively rejected |

### 2.7 Build Discipline, Axiom Census, Exposure Hygiene, and Proof Journal

- **Whole-Tree Axiom & File Census (`Obend/Census.lean`, `Obend/AssertAxioms.lean`, `Obend/AssertCompiled.lean`, `Obend/Tactic/DocsCensus.lean`)**: Crawls the filesystem and Lean environment at compile time to verify that every `.lean` file in `lean/Obend/` is imported and compiled, that no constant depends on `sorryAx` or a custom axiom, plus the choice-free `#print axioms` pins on `MachineFast`, `Data`, and `Cshake256/Fast` and `Obend.Slot`-backed markdown documentation pins (`#docs_census`).
- **Two-Tier Build & `#tooth` Gate (`lean/tools/hooks/pre-push`)**: Tier 1 (`lake build Obend obend`) builds the core library and CLI using selective `@[expose]` in `Obend/Core/` (`import all` for proof readers); Tier 2 (`lake build Obend.Census Teeth Tests`) runs the full census and `#tooth` mutation suites across `Obend/Teeth/` and `Obend/Apps/`.
- **Retired Exploration Record**: Early prototypes of standalone justification/polynomial-slot wrappers (`Obend/Logic/Obligation.lean`, `Obend/Slot/Selection.lean`, `Obend/Intention.lean` at commits `5892944`/`4753f62`) were retired in `ab6bb3f` after proving that `Obend/Slot.lean` already stores its support monomial in normal form (`stale_iff_blocked`).

---

## 3. Landed Next-Generation & Silicon Elaborator Theorems (`WS 18`–`WS 27`)

All theorem targets from [`NEXT-MATHEMATICA.md`](NEXT-MATHEMATICA.md), [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md), and [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md) are mechanized:

| Landed Theorem | Module | Architectural Role |
|---|---|---|
|  | `Obend/Law/Contract.lean` | Semantic `CellContract` transition $I(\text{old}) \to T(\text{old}, \text{new}) \to I(\text{new})$ inductive preservation (superseding syntactic `keeps`) |
| `narrows_refl`, `narrows_trans`, `carry_preserves_forever_crowns` | `Obend/Law/Contract.lean` | Monotonic contract upgrades (`Narrows newC oldC`) preserve all historical invariants forever |
| `evalInterval_sound` | `Obend/Analysis/RealAnalysis.lean`, `Judge/RealAnalysis.lean` | Verified rational/dyadic interval evaluation and contraction-mapping fixed-point certificates |
| `evalDual_fst_eq_eval` / `symbolicDeriv_agrees_with_dual` / `interval_mean_value_enclosure` | `Obend/Analysis/Diff.lean` | Forward-mode dual numbers, symbolic differentiation, reverse-mode AD gradients, and interval Mean Value Theorem enclosures |
| `flowpipe_step_encloses_euler` / `flowpipe_safety_admits_contract` | `Obend/Analysis/Flowpipe.lean` | Validated Euler–Taylor / Picard–Lindelöf interval ODE flowpipe enclosures connected to `CellContract` certificates |
|  | `Obend/Lower/Reflect.lean`, `Obend/Tactic/Weave.lean` | Bidirectional tactic weave (`obend_unfold`, `obend_law`, `obend_split`, `obend_tooth`, `byLoweredLean`) |
|  | `Obend/Vault/Hyperedge.lean` | Multi-slot hyperedge transaction commits iff all read citations match and every participant's `CellContract` holds on the joint post-state |
|  | `Obend/Ledger/Seat.lean` | Every linear `Seat` in a multi-party contract turn receives either a state satisfying its `WantPredicate` or a full conservation-preserving refund |
|  | `Obend/Judge/Clearing.lean` | Primal-dual LP clearing receipt (`drex-clearing@1`) certifies supply conservation, primal/dual feasibility, and zero duality gap |
|  | `Obend/Vault/Projection.lean` | `FogOfWar` Merkle multiproofs verify public law compliance without leaking blinded private subtrees |
|  | `Obend/Vault/Mandate.lean` | Sandstorm grain transitions cannot read or mutate any slot outside their explicit `Powerbox` capability table |
|  | `Obend/Consensus/Finality.lean`, `Obend/Fold/Collapse.lean` | Tier-1 `VaultTurn`s with disjoint footprints commute without global consensus; `Fold.collapse` preserves audited state |
| `simplex_accountable_safety` / `epistemic_sybil_bounded_by_seed_cut` | `Obend/Consensus/Simplex.lean`, `Epistemic.lean` | Symbolic `Simplex` BFT safety under $< n/3$ Byzantine weight, slashable equivocation receipts, and Sybil-bounded epistemic trust |
|  | `Obend/Lower/Inductive.lean` | Recursive user inductives (`Lean.Level`, `Lean.Expr`, `Lean.Syntax`, `Obend.Core.Term`) lowered to `Core4` |
| `kernelWhnf_general_iota_sound` / `kernelWhnf_quot_lift_sound` / `silicon_kernel_check_sound` | `Obend/Lower/LeanKernel.lean`, `Proofs/SiliconKernel.lean` | Pure Lean 4 kernel checker (`whnf`, `isDefEq`, `inferType`, general inductive $\iota$, `Quot.lift`) compiled to `ReductionMachine` eFPGA `AutomatonTile`s with `ICAP` DPR |
| `exprCam_eq_iff_handle_eq` / `exprCam_looseBVar_flag_sound` / `intern_unintern_roundtrip` | `Obend/Lower/ExprCAM.lean` | 64-bit hardware hash-consed DAG / CAM pool (`ExprCAM`) with 1-cycle structural equality and $O(1)$ `hasLooseBVar` bit-flag soundness |

### 3.1 Landed Fine-Grained Kernel & Subsystem Hardening Theorems (`WS 27`: `G1`–`G6`)

- **`G1` / Cost, Ticks & Linear `deepen` (`Obend/Core/Proofs/TickCost.lean`, `Obend/Run/Ticks.lean`)**: `runBounded_mono`, `finishedNat_mono`, `cost_indexed_completeness`, `deepenBounded_mono`, and `deepenBounded_eq_deepen`.
- **`G2` / Nominal C4 & Stable Kind Identity (`Obend/Spec/C4.lean`, `Obend/Kind/Registry.lean`)**: `orderedPresentationInvariant` for C4 linearization under injective renamings and `effectiveOf_agree_of_lineage_agree` across registries.
- **`G3` / Graded Per-Field Record Quantities (`Obend/Core/Proofs/GradedRecord.lean`, `Obend/Core/Proofs/Aggregate.lean`)**: `graded_sigma_tensor_conserves_linear` ($\Sigma^\otimes$), `graded_sigma_with_get_conserves_linear` ($\Sigma^\&$), and machine-level heap-address linear conservation (`heap_linear_conserved`).
- **`G4` / Chained World Roots & Impact Binding (`Obend/Receipt/Merkle.lean`, `Obend/Fold/Collapse.lean`)**: `dated_sound`, `opens_binds`,.
- **`G5` / Effect Laws Designs A–D & External Certificate Judges (`Obend/Run/Runner.lean`, `Obend/Run/Shared.lean`, `Obend/Run/HyperLaw.lean`, `Obend/Judge/Lrat.lean`, `Obend/Judge/Clearing.lean`, `Obend/Judge/RealAnalysis.lean`)**: Design A single-runner history & dispatch guards (`Obend.Run.Runner`), Design B multi-runner atomic ledger commit & `OnceSpent` (`Obend.Run.Shared`), Design C `k=2` relational safety hyperproperties & non-interference (`Obend.Run.HyperLaw.checkHyperLaw2NonInterference_sound`), Design D `Oracle7` Gelfond-Lifschitz modal `□` equilibrium judge (`Obend.Run.HyperLaw.oracle7Judge`, `Obend.Run.HyperLaw.checkOracle7Equilibrium_sound`), and unified `lrat@1`, `drex-clearing@1`, and `real-analysis@1` under `Obend.Judge`.
- **`G6` / Open Vtable Residual Check (`Obend/Leaf/Residual.lean` & `Obend/Leaf/Flatten.lean`)**: `superOnlyProjected`, `openVtable_no_residual_super`, and `no_residual_super`.

### 3.2 Landed Stage 5/6 Silicon Elaborator, Next Mathematica II & Physical Projection Theorems (`WS 28`–`WS 32`)

| Landed Theorem | Module | Architectural Role |
|---|---|---|
| `metaUnify_assign_sound` | `Obend/Lower/MetaUnify.lean` | Lowered `MetavarContext` + higher-order Miller pattern unification + postponed constraint solving lowered to `Leaf.Book`, proving every elaborated declaration checks under `kernelCheckDecl` |
| `discrTree_lut_compile_sound` / `exprCam_siliconKernel_sv_cosim_sound` | `Obend/Lower/DiscrTreeLUT.lean` | A `DiscrTree` epoch compiled to a Zone-3 `AutomatonTile` LUT guarded by `SlotGuardReg` (concrete instances), and the `ExprCAM`/kernel/LUT RTL module checked in Lean |
| `taylorModel_transcendental_enclosure_sound` / `taylorModel_picard_sound` | `Obend/Analysis/TaylorModel.lean` | High-order Taylor models $(p(x), I_{\text{rem}})$ with verified $\exp, \sin, \cos, \ln(1+x), \sqrt{1+x}$ enclosures and contractive Picard–Lindelöf ODE integration eliminating the interval wrapping effect |
| `groebner_ideal_membership_sound` / `stengle_positivstellensatz_sound` | `Obend/Analysis/Groebner.lean`, `Tactic/Weave.lean` | Certified Buchberger Gröbner bases, ideal membership ($f = \sum q_i g_i$), and Stengle Positivstellensatz semi-algebraic infeasibility witnesses wired into `obend_law` |
| `hybrid_flowpipe_safety_admits_contract` | `Obend/Analysis/Hybrid.lean` | Hybrid automata coupling continuous `Flowpipe` ODE integration with discrete guarded mode transitions and affine reset maps |
| `physical_projection_deterministic` / `physical_cnc_abbe_projection_sound` / `physical_projection_doc_noninterference` | `Obend/Vault/PhysicalProjection.lean` | Read-only `.obnb` cell projections for 5-axis CNC toolpaths (Featherstone 6D + 21-param Abbe compensation), OpenUSD scene graphs (`LIVERPS` relocates + `AffineForm1D` SDFs), and coupled LC/stator multiphysics |
| `replayedDeterministic_iff_confined` / `reconstructedApproximate_iff_unconfined` / `replayedDeterministic_replays` / `unconfined_chain_drops_interactions` | `Obend/Vault/Rehydration.lean` | Derived `Rehydration` liveness-type (`Live \| ReplayedDeterministic \| ReconstructedApproximate`) proving `ReplayedDeterministic` is iff every external interaction stayed inside the capability membrane, with tamper-evident and complete replay receipt coverage |
| `membrane_two_viewers_distinct` / `reshare_chain_attenuates` / `reshare_chain_blocks_delayed_permits_amplification` / `rerender_square` / `snapshot_roundtrip_attenuated` / `fireReactive_iff` | `Obend/Vault/Rehydration.lean` | Relational `Membrane` + multi-hop `Membrane.reshare` ($A \to B \to C$), functorial rerender commuting square (`project ∘ step = step ∘ project`), per-viewer `Sturdyref` snapshot rehydration, and 3D `ReactiveAffordance` (`TransitionGate` + `[openHeight, closeHeight]` deadline window) |
