# Obend — System Design

> **Obend** is a dependently-typed, capability-linear, proof-carrying language, document engine, smart-contract vault, and hardware-synthesis substrate mechanized in Lean 4 (no counts here: the census in `lean/Obend/Census.lean` is the record, per directory, of what is proved and how).
>
> Everything below corresponds either to landed, machine-checked Lean 4 modules under `lean/Obend/` or to the explicitly labelled architectural frontiers in [`NEXT-MATHEMATICA.md`](NEXT-MATHEMATICA.md), [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md), and [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md).

---

## 0. The Governing Rule

Every design decision in `Obend` answers one question:

> **What does the one small checker (`Judge.accepts`) need to see so that no caller can forge a transition, duplicate a capability, silently weaken an invariant, or fabricate a hardware bitstream?**

If a design detail does not change what `Judge.accepts` checks—or what a specialized hardware tile / consensus engine can soundly execute under `Judge.accepts`'s theorems—it belongs at the periphery.

---

## 1. Core4: The Small Kernel (`Obend/Core/`)

`Core4` is the trusted kernel of `Obend`. Everything above it (`Spec/Elaborate`, `Vault`, `Leaf`, `Lower`, `Hardware`, `Ledger`) reduces to `Core4` terms, slots, and receipts.

### 1.1 Term Former Table (`Obend/Core/Term.lean`)

| Category | Constructors | Purpose |
|---|---|---|
| **Variables & binders** | `bound k`, `lam q A b`, `pi q A B`, `app f a`, `letE q A v b` | Quantitative dependent function space ($\Pi_{x :_q A} B$) |
| **Dependent pairs & linear split** | `sigma q A B`, `pair q a b`, `fst p`, `snd p`, `split q p B body` | Dependent products ($\Sigma_{x :_q A} B$) and quantity-aware eliminator (`split` preserves `.one` usage without duplicating projections) |
| **Universe & primitives** | `u0`, `natType`, `natLit n`, `boolType`, `boolLit b`, `unitType`, `unitVal`, `prim2 op a b`, `ifBool c t e` | Base types, decidable arithmetic/comparison primitives, branching |
| **Propositional equality** | `eqType A a b`, `refl a`, `jElim A a P d b p` | Intensional equality and $J$-elimination |
| **Bounded recursion** | `fix fuel f A b` | Fuel-bounded fixpoint (`fix 0` returns default; `fix (n+1)` unfolds once) |
| **Nominal branding (`#kind`)** | `brand tag inner`, `unbrand tag e` | First-class nominal type/value wrapper (`Obend/Core/Nominal.lean`) |
| **Quotient / View (`view`)** | `quo T R`, `quoIn T R a`, `quoLift T R B f h q` | Setoid quotient introduction and soundness-checked elimination (`Obend/Core/Code.lean`) |
| **Inductive families** | `ind name params`, `ctor ind tag args`, `matchE scrutotive arms`, `recConst f fuel args` | Inductive types, constructors, quantity-preserving `ArmsTyping` pattern matching, and equation-lemma recursion (`Obend/Lower/Inductive.lean`) |
| **Capability slots & quoting** | `slot id`, `quote t`, `unquote q` | First-class slot references and canonical capability-stripped quoting (`Obend/Equiv/Quote.lean`) |

### 1.2 Quantities (`Obend/Core/Ty.lean`)

Every binder and dependent pair carries a quantity $q \in \{0, 1, \omega\}$ (`Quantity.zero`, `Quantity.one`, `Quantity.many`):

| Quantity | Meaning | Kernel Enforcement |
|---|---|---|
| `.zero` ($0$) | Erased / compile-time / type-only | Cannot appear at runtime (`u.head == .zero` after type sub-derivation scaling by $0$) |
| `.one` ($1$) | Linear capability / resource / wire | Consumed **at most / exactly once**; additive branch joins (`ArmsTyping`) require identical `.one` consumption across arms; `step_conserves_linear` proves small-step preservation |
| `.many` ($\omega$) | Unrestricted pure value | Freely duplicated and discarded |

Why is `split q p B body` in `Core4` alongside `fst`/`snd`? Because projecting both `fst p` and `snd p` from a bound variable `p : .sigma .one A B` uses `p` twice ($1 + 1 = \omega \neq 1$), which `Usage.check` rightly rejects (`Obend/Core/Proofs/Aggregate.lean`). `Term.split` destructures `p` in a single linear elimination, binding `fst` at $q$ and `snd` at $1$ in `body`.

### 1.3 Content Addressing & Canonical Quote (`Obend/Core/Code.lean`, `Quote.lean`)

- **Version-prefixed canonical encoding (`Code.encode`)**: Prepends `encodingVersion : ByteArray` (`"obend-core4-v1\x00"`) before the structural tag stream. `encodingVersion_binds` proves injectivity across versions.
- **Content hash (`Hash`)**: 256-bit digest (`BLAKE3` / `SHA-256` on the wire; injective `Code.hash` model in Lean proofs).
- **Capability-free quoting (`Quote.stripSlots`)**: `quote t` rejects or strips live `.slot` references , ensuring quoted syntax cannot smuggle ambient authority across cell boundaries (`C1`).

---

## 2. Slots, Intentions, Kinds, and Folds (`Obend/Slot/`, `Obend/Intention/`, `Obend/Kind/`, `Obend/Fold/`)

### 2.1 Slots vs. Intentions

```
  Intention I  = { domain : Term, carrier : Term, predicate : Term }   -- pure Core4 predicate
  Slot s       = { id : SlotId, state : Term, law : Intention, ... }   -- mutable capability cell
```

- An **Intention** (`Obend/Intention.lean`) is a pure `Core4` proposition $\lambda s.\, P(s)$ over a state type.
- A **Slot** (`Obend/Slot/World.lean`) binds a `SlotId`, a current value `v`, a governing `Intention` (`law`), and a monotonic `Epoch` / receipt chain.
- **Kinds (`#kind`, `Obend/Kind/`, `Obend/Core/Nominal.lean`)**: Two slots with structurally identical carrier types (e.g., `Nat` representing `Meters` vs. `Seconds`, or `PublicCell` vs. `SecretVault`) are distinguished nominally by `Term.brand tag T`.  proves that distinct tags are never definitionally equal (`Conv`), blocking accidental capability confusion (`C1`).

### 2.2 Folds and Citations (`Obend/Fold/`, `Obend/Receipt.lean`)

A `Fold` is a verifiable log of state transitions (`Turn`s), where each turn carries a `Receipt`:

```
  Receipt =
    { oldHash    : Hash
    , newHash    : Hash
    , lawHash    : Hash
    , witness    : Term          -- Core4 proof term checked by Judge.accepts
    , epoch      : Nat           -- monotonic epoch counter
    , citations  : List Citation -- explicit (slotId, epoch, stateHash) dependencies
    }
```

- **Replay resistance (`Receipt.Dated`)**: `dated_sound` proves that any receipt whose cited epoch does not match the live `EpochTable` is rejected, eliminating stale-state replay (`G4`).
- **Cited multi-slot judgment (`Judge.acceptsCited`)**: `accepts_cited_sound` proves that a transition reading external slots via `Citation`s is valid only when every cited slot's hash and epoch match the live environment.
- **Fold collapse (`Obend/Fold/Collapse.lean`)**: Compresses an epoch range $[e_0, e_k]$ of receipts into a single checkpoint receipt without expanding the trusted computing base.

---

## 3. The One Checker and the Runner (`Obend/Judge/`, `Obend/Run/`)

### 3.1 `Judge.accepts` (`Obend/Judge/Class.lean`)

There is **one** gatekeeper in `Obend`:

$$\mathsf{Judge.accepts}(\Gamma, s_{\text{old}}, s_{\text{new}}, \mathcal{L}, w) = \mathsf{true}$$

By  (`Obend/Judge/Certified.lean`), `Judge.accepts` returns `true` **if and only if**:
1. $s_{\text{old}}$ and $s_{\text{new}}$ typecheck at the slot's carrier type under $\Gamma$,
2. The witness $w$ typechecks in `Core4` at the law obligation $\mathcal{L}(s_{\text{old}}, s_{\text{new}})$ with valid linear usage, and
3. Every cited slot (`acceptsCited`) matches its live hash and epoch.

Nothing outside `Core4` + `Judge.accepts` is trusted. Tactics, e-graphs (`Obend/Analysis/EqSatHypergraph.lean`), press-fit solvers (`Obend/Spec/LawDial.lean`), Lean tactic bridges (`Obend/Lower/Transport.lean`), and hardware tiles all emit explicit `Core4` terms or receipts that `Judge.accepts` verifies.

### 3.2 Cost, Demand, and Ticks (`Obend/Run/Ticks.lean`, `Demand.lean`, `Ticks.lean`)

Every evaluation step in `Obend/Core/Term.lean` and `Obend/Run/Runner.lean` accounts for exact resource budgets:
- **`Cost` & `Ticks`**:  prove that static tick bounds upper-bound exact evaluation steps.
- **`Demand` (`Demand.lean`)**: Compositional demand analysis over `Core4` terms , guaranteeing that any call with budget $B \ge \mathsf{demand}(t)$ terminates without fuel exhaustion.
- **Atomic Fork/Stitch (`Obend/Run/Fork.lean`)**: `stitch_atomic` proves that concurrent or speculative execution over disjoint slot footprints merges atomically into the parent state, or rolls back cleanly on conflict without leaking partial mutations.

---

## 4. Late-Bound Logic & Layer Specialization (`Obend/Logic/`, `Obend/Leaf/`)

### 4.1 Late-Bound Logic (`Obend/Logic/`)

Why can `Obend` programs be reasoned about *before* their open slots are bound, and still specialized *after* they are bound? Three theorems in `Obend/Logic/Proofs/` form the spine:

| Theorem | Module | Guarantee |
|---|---|---|
| **T1: `late_binding`** | `Obend/Logic/LateBinding.lean` | Typing, laws, and proofs over open slots commute with slot instantiation ($\Gamma, x : A \vdash t : B \implies \Gamma \vdash t[v/x] : B[v/x]$) |
| **T2: `rewrite_sound`** | `Obend/Logic/Rewrite.lean` | Any contextual rewrite justified by a law equality preserves `Conv` and typing in arbitrary frames |
| **T3: `claim_frame`** | `Obend/Logic/Frame.lean` | A law proved on slot footprint $S_1$ remains valid across any transition whose write footprint $S_2$ is disjoint from $S_1$ ($S_1 \cap S_2 = \emptyset$) |

 complemented by **`Obend/Analysis/Impact.lean`** , which statically computes a sound over-approximation of every transitive dependency of a slot mutation across a Vault.

### 4.2 `Leaf`: flattening, books, folding, and the specialization slot (`Obend/Leaf/`)

In classic OO or capability systems, composing layers of objects/wrappers introduces dynamic dispatch (`vtable` indirection) and environment closures at every boundary. `Obend/Leaf/` eliminates both:

1. **Layer Flattening (`Obend/Leaf/Flatten.lean`, `Residual.lean`)**: Given a composition of layers and pinned slot states, `Flatten.flatten` partially evaluates the composition with respect to known slot bindings. `flatten_sound` proves observational equivalence; `vtable_clean` proves **zero residual vtable/dispatch nodes** remain in the specialized term.
2. **Book Emission (`Obend/Leaf/Emit.lean`)**: the vtable becomes a `Leaf.Book`, one closed first-order definition per member plus one dispatcher `Book.link` that ties the knot (`book_sound`: every member of the linked book is `≈b` the member of the object). The book is a `Core4` term run by the demand machine and the input of `Obend/Hardware/Compiler.lean`; there is no other backend. (A module named `BendTT.lean` claimed a translation to Bend's affine calculus plus interaction-net and C emitters; none translated anything and all were deleted on 2026-11-04, `review/EXPERT-compiler-runtime-20261103.md` §2.2. Bend is not a target.)
3. **Static folding (`Obend/Leaf/Static.lean`)**: `dataPinSpecialize` is four passes of a bottom-up constant folder, each a reduction in context (`ahead_dataPinPass`), so `t ≈b dataPinSpecialize t`; `specializeBook B pins` substitutes the `self.m` reads that `pins` fix into every definition and folds. The per-definition equivalence is proved (`specializeDefCode_bequiv_and_halts`); the equivalence of the specialized book's link with the original's is open. This is the whole of "specialization": there is no self-applicable specializer in `Core4` and no Futamura projection beyond the first.
4. **The specialization slot (`Obend/Leaf/Specialize.lean`)**: `specSlot` holds `[Candidate.book name C, Candidate.machine]`; a book's supports are the **whole code** of every layer it flattened and of the composition, compared by structural equality (`Obend.Law.termEq`) at the view. `specialize_choice`: the stored book is kept exactly while every support holds, else the machine. `moved_pin_blocks`: a support that does not hold blocks the book and the read names it. The choice is made once, before a run (`obend specialize`); the machine carries no guard, nothing is invalidated mid-run, and nothing is hashed. The finer `Candidate.slotBook` exists and is not selected.

---

## 5. The Bidirectional Lean 4 Bridge (`Obend/Lower/`)

`Obend` is not an isolated island; it is bidirectionally coupled to the full Lean 4 / Mathlib / SciLean ecosystem via `Obend/Lower/`.

```
  Lean 4 Kernel Expr (theorems, Mathlib/SciLean defs, Lean4Lean)
        │                                       ▲
        │ Obend/Lower/Fragment.read             │ Obend/Lower/Reflect.reflectTerm
        │ (lower_sound, lower_checks)           │ + Transport.lean + Lean 4 Tactics
        ▼                                       │
  Core4 Term ──► Leaf.Book ──► Obend/Hardware/Compiler (RTL)
```

### 5.1 Outbound: Lean Kernel `Expr` $\to$ `Core4` (`Obend/Lower/Fragment.lean`)
- Lowers a clean, self-contained fragment of Lean 4 kernel `Expr`s (`bvar`, `lam`, `forallE`, `app`, `letE`, `Lit`, `Nat`, `Bool`, `Unit`, `Prod`/`PProd`, `And`, `Eq`/`Eq.refl`/`Eq.ndrec`, structural/well-founded recursion via `f.eq_def` $\to$ `recConst` $\to$ `fix`) into `Core4`.
- **Proved Metatheory**:
  - `lower_sound`: Single-step and multi-step `LStep` reduction in Lean commutes with `Core4.StepStar`.
  - `lower_checks`: Every lowered term passes the bidirectional kernel checker `Check.infer`.
  - `lower_complete_ltyped_nat` (`Obend/Lower/Proofs/Complete.lean`): By Tait–Girard reducibility (`LRed`), every well-typed closed `Lean-lite` term of type `Nat` terminates and lowers to a `Core4` normal form.
  - `lean_to_book`: Composes `Fragment.read` with `Leaf.Emit.emitBook` to compile Lean definitions directly to flat supercombinator books.

### 5.2 Inbound: `Core4` $\to$ Lean 4 Reflection & Tactics (`Obend/Lower/Transport.lean` + Milestone 1)
- **`transport@1` (`Obend/Lower/Transport.lean`)**: Turns a checked Lean theorem into a `Judge`-verifiable `Law.Claim` / `CellContract` witness (`transportTheorem`).
- **Tactic Reflection (`Obend/Tactic/Weave.lean`)**: Reflects `Obend` slot obligations and cell expressions into live Lean 4 goals (`obend_unfold`, `obend_law`, `obend_split`, `obend_tooth`), letting users discharge complex nonlinear/analytic proof obligations using `omega`, `linarith`, `polyrith`, `norm_num`, `ring`, `aesop`, or custom Mathlib lemmas, and lowering the resulting kernel proof right back into a `Core4` receipt witness (`byLoweredLean`).

---

## 6. Law Dials, Semantic Contracts, and Real Mathematical Analysis (`Obend/Law/`, `Obend/Spec/LawDial.lean`, `Obend/Analysis/`)

### 6.1 The 3-Mode Law Dial (`Obend/Spec/LawDial.lean`)

Interactive exploration in a notebook should never stall on a missing proof, while a committed smart contract or silicon tapeout must never accept an unproved transition. Every slot or notebook cell has a 3-mode `LawDial`:

| Dial Mode | Behavior on Mutation | Guarantee |
|---|---|---|
| **`.free`** | Never blocks edits; records candidate transitions in an explicit `UnverifiedDebt` queue / CRDT branch | `dial_free_confluent` |
| **`.press`** | Runs automated witness synthesis (`solveLawWitness`: `refl`, `decidable`, `egraph`, `interval`, `transport@1`); falls back to `.free` debt only if unsolved | `solveLawWitness_sound` |
| **`.locked`** | Enforces full `Judge.accepts` checking on every transition; zero unverified debt permitted | — |

### 6.2 Why `CellContract` & `Narrows` Replace Legacy `keeps` (`Obend/Law/Contract.lean`)

The early `Obend/Law/Claim.lean` (`keeps`) checker required a syntactic guard shape `ifBool (I new) new old` with `termEq f I` and exempted `occasion == "relaw"`. That design rejected compiled `.obend` surface laws (which inline `I`), could not assume the inductive hypothesis $I(\text{old})$, and allowed law erasure on `"relaw"`.

`Obend` replaces syntactic `keeps` with **`CellContract`** (`Obend/Law/Contract.lean`, detailed in [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md)):
1. **Semantic Invariant Induction**: A transition witness proves $I(\text{old}) \to T(\text{old}, \text{new}) \to I(\text{new})$ in `Core4`, irrespective of whether `new` was computed by an `ifBool` guard, an LP solver, or an external actor.
2. **Forever-Crowns via `Narrows`**: Upgrading a slot's contract (`relaw`) requires a `Core4` proof `Narrows newC oldC`:
   $$\forall s.\, I_{\text{new}}(s) \to I_{\text{old}}(s) \quad\wedge\quad \forall s, s'.\, I_{\text{new}}(s) \to T_{\text{new}}(s, s') \to T_{\text{old}}(s, s')$$
   Since `Narrows` is a preorder (`narrows_refl`, `narrows_trans`), proved properties of a cell are **monotonic forever** across arbitrary future upgrades.

### 6.3 Real Mathematical Analysis Beyond E-Graphs (`Obend/Analysis/`)

Equational saturation (`Obend/Analysis/EqSatHypergraph.lean`) is fast for algebraic rewrites, but real engineering and physics require **order, bounds, rates of change, and fixed-point convergence**:
- **Verified Dyadic Interval Arithmetic (`Obend/Analysis/RealAnalysis.lean`)**: Exact $[lo, hi] \subset \mathbb{Q}_{\text{dyadic}}$ enclosures (`Interval.add_mem`, `Interval.mul_mem`) that synthesize `Core4` inequality certificates without floating-point unsoundness.
- **Symbolic Differentiation & Automatic Adjoints (`Obend/Analysis/Diff.lean`)**: Forward-mode dual numbers and reverse-mode pullbacks over `Core4` expressions , feeding sensitivity cones directly into `Obend/Analysis/Impact.lean` and `Obend/Hardware/` multiphysics checks.
- **Contraction Mapping & Monotone Fixed Points (`Obend/Analysis/Flowpipe.lean`)**: Certifies convergence and error bounds for iterative numerical solvers.

---

## 7. Proof-Carrying Smart Contract Vaults, DeOS Surfaces, and 4-Tier Finality (`Obend/Vault/`, `Obend/Ledger/`)

> Full specification in [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md).

A `Vault` (`Obend/Vault/Store.lean`) is simultaneously a filesystem-backed reactive notebook directory and a **proof-carrying capability-linear smart contract state machine**:
- **Multi-Slot Atomic `VaultTurn` (Wide-Pullback Hyperedges)**: Generalizes single-slot transitions to atomic multi-slot transactions (`reads`, `writes`, `created`, `consumed`).  proves that a `VaultTurn` commits if and only if all read citations match and every participant's `CellContract` is satisfied on the shared post-state.
- **Linear Asset Conservation (`Book`) & ZoE `Seat`s**: Quantities modeled via `.one` linear slots conserve supply . Multi-party swaps use **Offer Safety (`Seat`s)**: a participant deposits assets into a `Seat` governed by a `WantPredicate`, guarantees that regardless of how the matcher clears the batch, every seat ends with either its requested payout or a full refund.
- **Certified `drex-clearing@1` LP Primal-Dual Verifier**: The off-chain solver finds the optimal batch clearing + dual variables $(\lambda, \mu)$; the on-chain `Core4` checker verifies conservation, primal feasibility, dual feasibility, and zero duality gap in $O(|E| + |V|)$ arithmetic operations.
- **DeOS Surfaces & Sandstorm Grain Confinement**: `SealedEscrow`, `PrepaidLease`, `GatedAffordance`, `FogOfWar` blinded Merkle multiproofs , `Mandate` human-readable authority constraints, and **Sandstorm Grain Confinement** (: zero ambient authority; communication strictly through `Powerbox`-minted capabilities).
- **4-Tier Finality Ladder**:
  1. *Tier 0 (`LawDial.free`)*: Local optimistic CRDT notebook edits.
  2. *Tier 1 (`VaultTurn` Fast Path)*: Disjoint-footprint commutativity  without global BFT coordination.
  3. *Tier 2 (Symbolic `Simplex` BFT)*: Contended shared-slot ordering in $< 3\Delta$ with `simplex_accountable_safety` (any fork yields a concrete slashable equivocation certificate).
  4. *Tier 3 (`EpistemicConsensus` + `Fold.collapse`)*: Weighted subjective evidence synthesis and historical receipt folding.

---

## 8. The Silicon Spine: Verified Hardware, eFPGA DPR, and the Silicon Lean Elaborator (`Obend/Hardware/`, `Obend/Lower/Proofs/Hardware.lean`)

> Full specification in [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md), [`METATHEORY.md` §2.6](METATHEORY.md), and [`lean/Obend/Hardware/`](lean/Obend/Hardware/).

`Obend/Hardware/` (with its `#tooth` mutation checks in `SiliconTeeth.lean` and the co-simulation suites) turns `Obend` into a verified silicon design and execution stack:
- **RTL & Equivalence**: Synchronous circuits (`RTL.lean`), cycle-accurate evaluation (`Sim.lean`), bounded model checking (`Verify.lean`), AIG synthesis (`Synth.lean`), and the verified `Leaf.Book` $\to$ Verilog emitter (`Verilog.lean`).
- **Technology Mapping, STA, Place & Route, DRC/LVS, GDSII**: Cut-based LUT mapping (`TechMap.lean`), min/max corner Static Timing Analysis (`STA.lean`), Analytical + SA Placement (`Place.lean`), A* Maze Routing (`Route.lean`), Sky130/GF180 PDK rules (`PDK.lean`), geometry DRC & Netlist LVS (`DRC.lean`), and binary OASIS/GDSII tapeout (`GDSII.lean`) with wafer.space manufacturing signoff (`WaferSpace.lean`).
- **Multiphysics, Photonics, RF & Board**: Coupled electro-thermal-IR-drop-EM reliability (`Multiphysics.lean`), optical waveguide BPM/TMM/CMT (`Photonics.lean`), mixed-signal PLL/ADC (`MixedSignal.lean`), PCB transmission-line SI/PI (`PCB.lean`), and 3D FDTD Maxwell + Smith-chart impedance matching (`RF.lean`).
- **The Self-Reconfiguring eFPGA Automaton (`ReductionMachine.lean`)**:
  - Compiles a `Leaf.Book`'s definitions into distributed spatial `AutomatonTile`s connected by a credit-controlled XY wormhole NoC (`automaton_simulates_book`).
  - **Dynamic Partial Reconfiguration (`ICAP`) $\equiv$ `Leaf/Specialize.specSlot`**: Each tile is a hardware `Slot` whose state is its `TileBitstream`. Reconfiguring a tile via the 3-phase Glitch-Free DPR protocol (`Running` $\to$ `Draining` $\to$ `Isolated` $\to$ `Loading` $\to$ `Running`) is guarded by `specSlot`:
    - `dpr_preserves_neighbor_tiles_and_packets`: Non-target tiles and in-flight packets are completely undisturbed during reconfiguration.
    - `dpr_specialized_tile_executes_new_book`: Once `ICAP` commit completes, the reconfigured tile immediately executes the newly specialized `Leaf.Book`.
  - **The Silicon Lean Kernel & Elaborator**: By lowering `Lean4Lean` (`Kernel.whnf`, `Kernel.isDefEq`, `Kernel.check`) and pure `Lean.Elab` passes through `Obend/Lower` $\to$ `Obend/Leaf` (1st/2nd/3rd Futamura projections) $\to$ `ReductionMachine`, standard library environments and hot `simp`/typeclass tables are baked directly into specialized eFPGA LUT tiles, with 1-cycle fallback (`moved_pin_blocks`) whenever a user notebook overrides an environment constant.

---

## 9. `.obnb` Structured Notebooks & Thin Rust GUI/FFI

Markdown files remain supported as a compatibility projection (`Obend/Doc/Structured.lean`), but the primary interactive medium of "The Next Mathematica" is the **`.obnb` structured notebook (`Obend/Doc/Section.lean`)**:
- **Typed `BlockGraph` Cells**: `CodeCell`, `LawCell`, `ProofCell`, `Plot2DCell`, `Plot3DCell`, `CircuitSchematicCell`, `LayoutViewportCell`, `SliderWidgetCell`, `ContractEscrowCell`, `TableCell`, and `ProseCell`.
- **Every Widget Is a `Slot`**: Adjusting a `SliderWidgetCell` submits a `VaultTurn`; `Impact` recomputes the exact downstream cone; `.free` cells update at 120 fps, `.press` cells re-verify automatically, and `.locked` cells highlight broken laws with concrete counterexamples.
- **Thin Rust Native Shell**: Lean owns 100% of parsing, elaboration, typechecking, tactic reflection, interval/AD analysis, `Leaf` specialization, and `Vault` transitions via a thin `@[export]` C-ABI boundary (`obend_vault_open`, `obend_notebook_apply_op`, `obend_cell_set_dial`, `obend_tactic_reflect`, `obend_viewport_render_frame`), while a lightweight Rust `wgpu` shell renders 2D/3D plots, schematics, and GDSII/eFPGA viewports and handles native cryptography (`aws-lc-rs` / `blake3` / `ed25519-dalek`).
