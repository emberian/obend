# `obend` Constitutional & Architectural Decisions Ledger (`DECISIONS-LEDGER`)

An append-only record of every foundational, metatheoretic, runtime, and hardware decision in `obend`, unifying the October 30–November 1 founding decisions (`DECISIONS-20261031`, `ASTRA-DECISIONS-20261101`, `ASTRA-EFFECT-LAWS-20261031`) with the November 1–3 Wave 3–5 Whole-System Synthesis across all four realms.

---

## §1. Constitutional Rule — "Nothing Lands Beside; Everything Replaces"

1. **One Shared Kernel Spine**: Every domain in `obend`—epistemic digital gardens, validated symbolic/numeric analysis, sovereign OCap worlds and BFT markets, and physical CAD/CAM/silicon synthesis—rides the single shared kernel spine:
   - **`Core4`** (`lean/Obend/Core/Term.lean`, `lean/Obend/Core/Machine.lean`, `lean/Obend/Core/Check.lean`): 23 term constructors, 12 type constructors, total typechecker, total bounded abstract machine, and machine-checked preservation/progress (`lean/Obend/Core/Proofs/Preservation.lean`, `lean/Obend/Core/Proofs/Adequacy.lean`).
   - **Nominal `#kind` & `K-CARRY`** (`lean/Obend/Core/Nominal.lean`, `lean/Obend/Kind.lean`, `lean/Obend/Vault/Carry.lean`): nominal stamps (`#kind` as a `Term.stamp` constructor, not a reservable record field) and monotonic ancestor law inheritance across turns.
   - **`Intention` & `Slot`** (`lean/Obend/Intention.lean`, `lean/Obend/Slot.lean`): open obligations whose support pins are tracked against a changing `World`, with monotonic repair and exact refutation diagnostics.
   - **`Judge` & `Judge.Format`** (`lean/Obend/Judge/Class.lean`, `lean/Obend/Judge.lean`): every domain checker is an instance of `Obend.Judge Obj Cert` with kernel-proved `sound`, `mono`, and a registered `Obend.Judge.Format` carrying a planted bad certificate (`bad_refused`) and `#tooth` mutation witness (`lean/Obend/Tactic/Tooth.lean`).
   - **Guarded `Run` & Audited `Fold`** (`lean/Obend/Run.lean`, `lean/Obend/Fold.lean`): capability-carrying execution with durable journals (`lean/Obend/Run/Durable.lean`), shared atomic ledgers (`lean/Obend/Run/Shared.lean`), offline fork-and-stitch (`lean/Obend/Run/Fork.lean`), and `G5` Effect Laws (`lean/Obend/Run/HyperLaw.lean`).
   - **Cryptographic `Receipt`** (`lean/Obend/Receipt.lean`, `lean/Obend/Receipt/Merkle.lean`): domain-separated cSHAKE256 commitments (`0x00` leaf, `0x01` internal node, `0x02` schema) and fail-closed Merkle openings (`lean/Obend/Vault/Projection.lean`).
   - **Living `Doc` & `Vault`** (`lean/Obend/Doc.lean`, `lean/Obend/Vault.lean`, `lean/Journal/Journal.lean`): content-addressed causal graphs, section pushouts, transcluding wikilinks, and self-governing documentation slots (`lean/Obend/Tactic/DocsCensus.lean`).
2. **Replacement Discipline**: No subsystem may introduce a parallel untrusted AST, an unverified ad-hoc checker without `Obend.Judge`, or an unpinned side-channel state outside `Slot`/`Fold`/`Receipt`. Every new capability replaces prior scaffolding inside the same kernel hierarchy.
3. **Zero Axiom Escape**: All production and metatheoretic proofs must elaborate with `0 sorryAx` and `0` custom axioms, enforced at build time by `#assert_axioms_tree` in `lean/Obend/Census.lean`.

---

## §2. Chronological Decision Log

### 2026-10-29 — Core4 Surface & Metatheory Baseline
- ** Core4 23-Constructor Term & 12-Constructor Type Discipline** (`lean/Obend/Core/Term.lean`, `lean/Obend/Core/Ty.lean`):
  Fixed the core calculus to 23 term constructors (`var`, `lam`, `app`, `letIn`, `fix`, `nat`, `bool`, `str`, `unit`, `unary`, `binary`, `ite`, `record`, `get`, `set`, `variant`, `matchVariant`, `ret`, `bind`, `yield`, `handle`, `quote`, `stamp`) and 12 type constructors (`nat`, `bool`, `str`, `unit`, `arrow`, `record`, `variant`, `activity`, `code`, `nominal`, `forallTy`, `var`), with `0 sorry` preservation and adequacy (`lean/Obend/Core/Proofs/Preservation.lean`, `lean/Obend/Core/Proofs/Adequacy.lean`).

### 2026-10-30 — Intention, Slot, Causal Document Graph & Proof Journal
- **`Obend.Intention` and `Obend.Slot`** (`lean/Obend/Intention.lean`, `lean/Obend/Slot.lean`):
  Separated the world-dependent specification (`Intention`) from the candidate selection and support-pin machinery (`Slot`). Proved contextual repair (`Obend.Slot.repair_of_contextual` in `lean/Obend/Slot/Integrity.lean`) and non-repeating budget bounds (`lean/Obend/Slot/Budget.lean`).
- **Causal Document Graph & Section Pushout** (`lean/Obend/Doc/Graph.lean`, `lean/Obend/Doc/Merge.lean`, `lean/Obend/Doc/Section.lean`):
  Documents are causal graphs of atoms; concurrent edits form pushouts whose fork points are `Slot` sections (`Obend.Doc.conflict_is_section`).
- **Proof Journal as `Slot` Instances** (`lean/Journal/Journal.lean`):
  Each theorem in an environment export is a `Slot` whose supports are transitive meaning-edges (`.stmt` and `.proof`), with complete cycle-safe DFS closure (`Journal.walk_complete`).

### 2026-10-31 — Contracts `C1`–`C4`, Generalizations `G1`–`G6` & Effect Laws (`ASTRA-EFFECT-LAWS`)
- **Contract `C1` — Nominal `#kind` as a Kernel Constructor (`Term.stamp` / `Ty.nominal`)**:
  Replaced the reservable string field `"#kind"` in open records with the dedicated nominal constructor `Term.stamp` and type `Ty.nominal` (`lean/Obend/Core/Nominal.lean`, `lean/Obend/Core/Brand.lean`). Distinct nominal `#kind` brands never agree and cannot be forged (`Obend.Core.Nominal.kinds_never_agree`, `Obend.Core.Nominal.kinded_refuses`).
- **Contract `C2` — Exact Value Conservation in `split` & Multi-Asset Clearing**:
  Replaced boolean `&&` conjunction in conservation laws with exact additive conservation over `Nat`/`Int` balances (`lean/Obend/Ledger/Vault.lean`, `lean/Obend/Judge/AutomataConfinement.lean`).
- **Contract `C3` — Domain-Separated cSHAKE256 & Fail-Closed Merkle Openings**:
  Enforced domain separation (`0x00` leaf, `0x01` branch, `0x02` schema) in `lean/Obend/Receipt/Merkle.lean` and fail-closed verification of blinded multiproofs in `lean/Obend/Vault/Projection.lean` (`Obend.Vault.Projection.stranger_verification_sound`).
- **Contract `C4` — Clairvoyant Call-by-Value (`Obend.Equiv.CV`) & Layered Cost Completeness**:
  Defined two-stage clairvoyant evaluation `Obend.Equiv.CV` (`lean/Obend/Equiv/Clairvoyant.lean`) and proved `Obend.Core.Proofs.TickCost.cost_indexed_completeness` (`lean/Obend/Core/Proofs/TickCost.lean`) and `Obend.Judge.LayeredCost.layered_sound` (`lean/Obend/Judge/LayeredCost.lean`), while keeping the general arbitrary-recursion `Obend.Core.Proofs.TickCost.CostIndexedCompleteness` conjecture explicitly open as a documented boundary.
- **Generalizations `G1`–`G6`**:
  - `G1`: `Obend.Fold.Admission` (`lean/Obend/Fold.lean`) — universal audited left fold with pin-sufficiency (`Obend.Fold.step_of_pins`).
  - `G2`: `Obend.Judge` & `Obend.Judge.Format` (`lean/Obend/Judge/Class.lean`) — universal graded certificate checker with `sound`, `refuted`, `complete`, `mono`, and `bad_refused`.
  - `G3`: `Obend.Kind` (`lean/Obend/Kind.lean`) — nominal DAG inheritance, cycle rejection, and monotone law accumulation (`Obend.Kind.kind_law_inherited`).
  - `G4`: `Obend.Receipt` (`lean/Obend/Receipt.lean`) — universal dated Merkle receipt and support opening verifier.
  - `G5`: Effect Laws Designs A–D (`lean/Obend/Run/Runner.lean`, `lean/Obend/Run/Shared.lean`, `lean/Obend/Run/HyperLaw.lean`) plus external certificate judges (`LRAT`, `RealAnalysis`, `Clearing`, `Hardware`).
  - `G6`: First-Order Program Logic, Late-Bound Spec Layers & Futamura Specialization (`lean/Obend/Logic/Obligation.lean`, `lean/Obend/Leaf/Flatten.lean`, `lean/Obend/Leaf/Futamura.lean`).

### 2026-11-01 to 2026-11-03 — Wave 3–5 Whole-System Synthesis Across Four Realms
- **Encoding Version Discipline (`encodingVersion : Nat := 1`)**:
  All wire receipts, workbook transports (`lean/Obend/Elab/Workbook.lean`), and hardware/analysis formats pin an explicit version tag checked by `Obend.Judge.Format.checkBytes`.
- **Realm I (Epistemic Digital Garden & Self-Governing Census)**:
  - Repaired `Obend.Doc.Graph.atomText` (`lean/Obend/Doc/Section.lean`) and `Obend.Vault.contentText` (`lean/Obend/Vault/Page.lean`) so `.field` and `.cell` atoms render canonically (`:key: value` and fenced ```` ```obend #<id> ```` blocks) instead of erasing to `""` on disk.
  - Enabled block and heading transclusions `![[Page#^blockId]]` and `![[Page#Heading]]` in `lean/Obend/Doc/Render.lean` (`Obend.Doc.renderTranscludedAt`) while preserving `Obend.Doc.renderAt_fresh`.
  - Upgraded `lean/Obend/Tactic/DocsCensus.lean` to instantiate `Obend.Intention` and `Obend.Slot` over `DocEnvWorld` (`Lean.Environment × RepoFsSnapshot`), turning every top-level architecture document into a live kernel-checked `Slot`.
- **Realm II (Validated Symbolic & Numeric Analysis — Post-Mathematica)**:
  - Registered certified interval (`interval-v1`), Taylor-model (`taylor-model-v1`), Gröbner ideal membership (`groebner-ideal-v1`), SOS Lyapunov stability (`sos-lyapunov@1`), and hybrid ODE flowpipe (`hybrid-flowpipe@1`) judges (`lean/Obend/Elab/AutoCert.lean`, `lean/Obend/Analysis/SosLyapunov.lean`, `lean/Obend/Analysis/Hybrid.lean`).
- **Realm III (Sovereign OCap Worlds, Simplex BFT Finality & DReX Clearing)**:
  - Unified `K-CARRY` world transitions (`lean/Obend/Vault/Carry.lean`), Simplex BFT consensus safety (`lean/Obend/Consensus/Simplex.lean`, `lean/Obend/Consensus/SovereignFinality.lean`), TigerBeetle conservation (`lean/Obend/Ledger/Report.lean`), and DReX batch auctions (`lean/Obend/Vault/DragonsExchange.lean`).
- **Realm IV (Physical OpenUSD/CAD/5-Axis CAM & Synthesized Silicon/FPGA Realization)**:
  - Closed the RTL/eFPGA/ASIC/CAM verification loop (`lean/Obend/Hardware/Judge.lean`, `lean/Obend/Hardware/GeometryCAM.lean`, `lean/Obend/Lower/SiliconElabFabric.lean`) with 13 registered hardware `Obend.Judge.Format` instances and `#silicon_elab` kernel replay (`lean/Obend/Tactic/SiliconElab.lean`).

---

## §3. Contract & Generalization Status Table (`C1`–`C4`, `G1`–`G6`)

| ID | Contract / Generalization | Primary Modules | Kernel Theorems (`0 sorryAx`) | Open / Documented Scope Boundary |
| :--- | :--- | :--- | :--- | :--- |
| **`C1`** | Nominal `#kind` Stamp & `K-CARRY` Inheritance | `lean/Obend/Core/Nominal.lean`, `lean/Obend/Kind.lean`, `lean/Obend/Vault/Carry.lean` | `Obend.Core.Nominal.kinds_never_agree`, `Obend.Kind.kind_law_inherited`, `Obend.Vault.carry_conserves_total_book` | Complete for finite DAG kind hierarchies. |
| **`C2`** | Additive Value Conservation (`split` & Clearing) | `lean/Obend/Ledger/Vault.lean`, `lean/Obend/Ledger/Report.lean`, `lean/Obend/Vault/DragonsExchange.lean` | `Obend.Ledger.vault_conserved`, `Obend.Ledger.tbFormat`, `Obend.Vault.settleRing_conserves_net_worth` | Complete over arbitrary finite asset vectors and batch books. |
| **`C3`** | Domain-Separated cSHAKE256 & Fail-Closed Merkle Openings | `lean/Obend/Receipt/Merkle.lean`, `lean/Obend/Vault/Projection.lean` | `Obend.Vault.Projection.stranger_verification_sound`, `Obend.Vault.Projection.fog_of_war_noninterference` | Cryptographic collision resistance of cSHAKE256 is an external physical assumption; tree/prefix structure is kernel-proved. |
| **`C4`** | Clairvoyant CBV (`CV`) & Layered Cost Completeness | `lean/Obend/Equiv/Clairvoyant.lean`, `lean/Obend/Judge/LayeredCost.lean`, `lean/Obend/Core/Proofs/TickCost.lean` | `Obend.Equiv.evalClairvoyantMinCost_sound`, `Obend.Core.Proofs.TickCost.cost_indexed_completeness` | **Open Boundary**: `Obend.Core.Proofs.TickCost.CostIndexedCompleteness` for arbitrary unconstrained `fix` terms remains an explicit open conjecture (`Prop` definition in `lean/Obend/Core/Proofs/TickCost.lean`); proved on the stratified/bounded `InFragment`. |
| **`G1`** | Universal Audited Fold (`Admission`) | `lean/Obend/Fold.lean`, `lean/Obend/Fold/Collapse.lean` | `Obend.Fold.step_of_pins`, `Obend.Fold.project_moves_run` | Complete. |
| **`G2`** | Universal Graded `Judge` & `Judge.Format` | `lean/Obend/Judge/Class.lean`, `lean/Obend/Logic/Obligation.lean` | `Obend.Judge.Format.checkBytes_sound`, `Obend.Judge.Format.not_trivial`, `Obend.Judge.trivial_unregistrable` | Complete across all 35+ registered `Judge.Format` instances. |
| **`G3`** | Nominal Kind DAGs & Versioned Relawing | `lean/Obend/Kind.lean`, `lean/Obend/Vault/Store.lean` | `Obend.Vault.commit_kind_needs_relaw`, `Obend.Vault.commit_stale_needs_relaw`, `Obend.Vault.createFrom_kind_preserves_ancestor_laws` | Complete. |
| **`G4`** | Dated Merkle Receipts & Format Negotiation | `lean/Obend/Receipt.lean`, `lean/Obend/Receipt/Negotiation.lean` | `Obend.Receipt.receipt_sufficient` | Complete. |
| **`G5`** | Effect Laws (Designs A–D) & Domain Certificate Judges | `lean/Obend/Run/Runner.lean`, `lean/Obend/Run/Shared.lean`, `lean/Obend/Run/HyperLaw.lean`, `lean/Obend/Judge/Lrat.lean` | Design A (`Obend.Run.refines`), Design B (`Obend.Run.Shared.joint_once`), Design C (`Obend.Run.HyperLaw.checkHyperLaw2NonInterference_sound`), Design D (`Obend.Run.HyperLaw.checkOracle7Equilibrium_sound`) | Design C checks finite `k=2` relational traces; infinite-trace liveness hyperproperties (`∀π₁ ∃π₂`) are outside decidable trace checking. |
| **`G6`** | Program Logic, Late Binding & Futamura Projections | `lean/Obend/Logic/Obligation.lean`, `lean/Obend/Leaf/Flatten.lean`, `lean/Obend/Leaf/Futamura.lean` | `Obend.Leaf.flatten_sound`, `Obend.Leaf.Futamura.futamura1_book_specializer_sound` | Complete on closed compositions (`closedB = true`). |

---

## §4. Registered `Obend.Judge.Format` Table & Build Encapsulation Gates

### 4.1 Registered `Obend.Judge.Format` Instances

Every registered format below provides a total `check`, a kernel proof of `sound` and `mono`, and a concrete planted bad certificate with `bad_refused`:

| Format Wire Name (`name@version`) | Lean Definition | Module | Regime | Trust Base |
| :--- | :--- | :--- | :--- | :--- |
| `rewrite@1` | `Obend.Logic.claimFormat` | `lean/Obend/Logic/Obligation.lean` | `.decidable` | `.kernel` |
| `lrat@1` | `Obend.Judge.Lrat.format` | `lean/Obend/Judge/Lrat.lean` | `.decidable` | `.kernel` |
| `clearing@1` | `Obend.Logic.clearingFormat` | `lean/Obend/Logic/Obligation.lean` | `.decidable` | `.kernel` |
| `world-carry@1` | `Obend.Vault.worldCarryFormat` | `lean/Obend/Vault/Carry.lean` | `.decidable` | `.kernel` |
| `oracle7-gl-equilibrium@1` | `Obend.Run.HyperLaw.oracle7Format` | `lean/Obend/Run/HyperLaw.lean` | `.decidable` | `.kernel` |
| `dfa-confinement@1` | `Obend.Judge.dfaFormat` | `lean/Obend/Judge/AutomataConfinement.lean` | `.decidable` | `.kernel` |
| `cfg-compact@1` | `Obend.Judge.cfgCompactFormat` | `lean/Obend/Judge/AutomataConfinement.lean` | `.decidable` | `.kernel` |
| `dclutch-hoard-clearing@1` | `Obend.Judge.dclutchHoardFormat` | `lean/Obend/Judge/AutomataConfinement.lean` | `.decidable` | `.kernel` |
| `tlsn-transcript-policy@1` | `Obend.Judge.tlsnTranscriptFormat` | `lean/Obend/Judge/TranscriptPolicy.lean` | `.decidable` | `.kernel` |
| `tigerbeetle-conservation@1` | `Obend.Ledger.tbFormat` | `lean/Obend/Ledger/Report.lean` | `.decidable` | `.kernel` |
| `interval@1` | `Obend.Analysis.format` | `lean/Obend/Analysis/Format.lean` | `.decidable` | `.kernel` |
| `interval-v1@1` | `Obend.Elab.AutoCert.intervalFormat` | `lean/Obend/Elab/AutoCert.lean` | `.decidable` | `.kernel` |
| `taylor-model-v1@1` | `Obend.Elab.AutoCert.taylorModelFormat` | `lean/Obend/Elab/AutoCert.lean` | `.decidable` | `.kernel` |
| `groebner-ideal-v1@1` | `Obend.Elab.AutoCert.groebnerFormat` | `lean/Obend/Elab/AutoCert.lean` | `.decidable` | `.kernel` |
| `sos-lyapunov@1` | `Obend.Analysis.sosLyapunovFormat` | `lean/Obend/Analysis/SosLyapunov.lean` | `.decidable` | `.kernel` |
| `hybrid-flowpipe@1` | `Obend.Analysis.hybridFlowpipeFormat` | `lean/Obend/Analysis/Hybrid.lean` | `.decidable` | `.kernel` |
| `lower-trace@1` | `Obend.Lower.format` | `lean/Obend/Lower/Judge.lean` | `.decidable` | `.kernel` |
| `transport-v1@1` | `Obend.Lower.transportFormat` | `lean/Obend/Lower/Transport.lean` | `.decidable` | `.kernel` |
| `workbook-transport@1` | `Obend.Elab.Workbook.workbookTransportFormat` | `lean/Obend/Elab/Workbook.lean` | `.decidable` | `.kernel` |
| `hw-synth@1` .. `binary-cbor@1` (13 formats) | `Obend.Hardware.Judge.hwSynthFormat` et al. | `lean/Obend/Hardware/Judge.lean` | `.decidable` | `.kernel` |
| `foc-interval@1`, `foc-taylor@1` | `Obend.Apps.FocHil.focIntervalFormat` et al. | `lean/Obend/Apps/FocHil.lean` | `.decidable` | `.kernel` |
| `sdr-interval@1`, `sdr-taylor@1` | `Obend.Apps.SdrFt8.sdrIntervalFormat` et al. | `lean/Obend/Apps/SdrFt8.lean` | `.decidable` | `.kernel` |

### 4.2 Two-Tier Module Encapsulation & Build Gates (`lean/Obend/Census.lean`)

1. **Tier 1 (`Obend` Library in `lean/lakefile.toml`)**:
   Every production module under `lean/Obend/` starts with the `module` header and exports its public definitions and theorem signatures via `public section` (never `@[expose] public section` on proof-heavy modules), keeping proof terms encapsulated for fast incremental builds.
2. **Tier 2 (`Teeth` Library & `lean/Obend/Census.lean`)**:
   `lean/Obend/Census.lean` walks `lean/Obend/`, verifies that 100% of `.lean` files are imported and assigned to either Tier 1 (`name = "Obend"` globs in `lean/lakefile.toml`) or Tier 2 (`name = "Teeth"` globs in `lean/lakefile.toml`), runs `#assert_axioms_tree` to guarantee `0 sorryAx` and `0` custom axioms across the entire dependency closure, and runs `#docs_census` (`lean/Obend/Tactic/DocsCensus.lean`) to verify that every file path and `Obend.*` constant cited in the architecture docs resolves in the live repository and `Lean.Environment`.
