# Ambition

Objective Bend is being built to become the symbolic, analytic, coordination, and silicon core of
what comes after Mathematica: a language, kernel, and hardware-software co-design substrate in
which mathematics, real analysis, programs, structured notebooks, proof-carrying smart contracts,
capability-secure operating surfaces (DeOS), and custom silicon (from dynamically reconfiguring
eFPGAs to open-foundry ASICs) live in one world—where every answer carries the evidence a stranger
can check (`∨ HashBytes.Collision H`), every refusal names what would pass, and the system is as
automated as the laws of computer science and physics permit.

## The claim

A term rewriter with a notebook was the twentieth century's symbolic core. What it lacks is not
more rules. It lacks:
- **Objects many hands build without forking**: open-recursive layers (`self`/`super`) across
  packages that linearize by C4 and close lazily under `fix`, so a partial specification is already
  a value you can inspect, extend, and judge;
- **Laws and contracts judged at the moment of change**: inheritable along the nominal `Kind`
  lineage, equipped with inductive 2-state `CellContract`s, `Narrows` forever-crowns on upgrades,
  and Bellman-Ford difference-constraint synthesis (`LawDial`) that turns a refusal into a
  constructive multi-field repair suggestion (`suggestMultiField_admits`);
- **Bidirectional reflection with Lean 4**: where any object, method, or contract can pop out into
  Lean 4 (`Obend/Lower/Reflect` + `Weave` tactics `obend_unfold`, `obend_law`, `obend_split`,
  `obend_tooth`) for arbitrary mathematical induction, real analysis, or tactic proof, and weave its
  kernel-checked certificate right back into the notebook's live `Slot`;
- **Deferred decisions with withdrawable supports (`Obend/Slot` & `Obend/Intention`)**: where
  package parents, wikilink citations, kind versions, proof obligations, and compiler/hardware
  specializations are all instances of one contextual truth-maintenance calculus (`stale_iff_blocked`,
  `moved_pin_blocks`); and
- **A kernel that never trusts a search it did not run**: where SAT/LRAT solvers, primal-dual LP
  market clearers, real-analytic interval/SOS/Taylor provers, place-and-route engines, and AI agents
  act purely as untrusted certificate producers checked in linear/polynomial time by registered
  kernel `Judge`s.

Objective Bend has these in a **408+ module, 52,368-constant Mathlib-free Lean 4.35 mechanized
metatheory** with zero `sorryAx`, zero custom axioms, and 60+ kernel proof-mutation suites (`#tooth`).

## The six destinations

1. **The Next Mathematica: A Structured Symbolic, Analytic & CAD Workspace (`.obnb` `BlockGraph`).**
   Expressions are objects whose terms are canonical `Core.Data` quotations (`Code Ψ A θ`);
   notebooks are pushout-mergeable Pijul graphs (`Doc.Merge`) whose cells are typed `Slot`s carrying
   prose, `.obend` specifications, symbolic CAS derivations, real mathematical analysis (`tauceti` /
   interval enclosures / SOS / symbolic-numeric certificates), popped-out Lean 4 tactic proofs, live
   DeOS capability widgets, and interactive EDA/CAD schematics, timing histograms, and 2D GDSII
   layouts (`HardwareProjection`). A simplification with no certificate is labeled `attested` and
   its receipt says so.
2. **Staged, Futamura-Specialized Metaprogramming That Reaches All the Way to Silicon.**
   Quotation sits at the bottom of a proved observer ladder (`≈q ⊆ ≈r ⊆ ≈b`); splicing is checked
   contextual substitution (`splice_typed`); reflection is a capability-guarded runner operation
   (`Run/Reflect`). The specialization slot (`Obend/Leaf/Specialize`: `specSlot`) unifies software
   JIT deoptimization and hardware reconfiguration:
   - **1st Futamura Projection (`Leaf.Flatten` + `Residual.vtable_clean` + Data-Pin Folding)**:
     Specializes open-recursive layer stacks and interpreters at pinned code and cell data fields into
     flat first-order `Book`s (`book_sound`) and strict affine `BendTT` nets (`book_to_bendtt_sound`).
   - **2nd & 3rd Futamura Projections (Self-Lowering via `Obend/Lower`)**: Because `Obend/Lower`
     lowers Lean 4 definitions into `Core4` (`lower_sound`, `lower_checks`), extending `Lower.Fragment`
     with recursive inductives allows `Leaf.Flatten` and `Lean4Lean` themselves to be lowered into
     `Core4`—making the partial evaluator self-applicable inside the Vault.
3. **The Silicon Lean Elaborator & Self-Reconfiguring eFPGA Automaton (`SILICON-ELABORATOR.md`).**
   By composing `Obend/Lower` (`Lean → Core4`) with `Obend/Leaf` (`Core4 → Book/BendTT`) and
   `Obend/Hardware/ReductionMachine` (`Book → AutomatonTile` + 3-phase Glitch-Free `ICAP` Dynamic
   Partial Reconfiguration), hot slices of a Lean `Environment`, typeclass table, `whnf` reducer, or
   tactic loop are Futamura-specialized into reconfigurable FPGA tiles (`Candidate.book`) whose
   supports (`Candidate.supports`) are the exact `Environment` pins baked into LUTs. While a proof
   stays within those pins, reduction runs at hardwired gate speed (`book_usable_sound`,
   `automaton_simulates_book`); the instant a cell overrides a pinned definition, `moved_pin_blocks`
   and `specialize_choice` multiplex cleanly back to the resident general `Core4` fabric (`.machine`)
   in one cycle while a background worker synthesizes the new tile—paving the path from eFPGA
   acceleration to a custom open-foundry ASIC (`WaferSpace`).
4. **Proof-Carrying Smart Contract Vaults, DeOS Surfaces & 4-Tier Finality (`DEOS-CONTRACTS-CONSENSUS.md`).**
   Smart contracts are ordinary Vault `Kind`s governed by inductive `CellContract`s and `Narrows`
   forever-crowns. Multi-cell transitions execute as wide-pullback `VaultTurn` hyperedges with
   TOCTOU-free `Slot` footprint pins (`PlanBinding`), conserved multi-asset `Book`s, offer-safe ZoE
   `Seat`s, certified primal-dual DrEX batch clearing (`drex-clearing@1`), and standard house
   capacities (`SealedEscrow`, `PrepaidLease`, `Mandate`, Sandstorm grain confinement). Every window
   is a capability projection (`FogOfWar` over `Receipt.blind` Merkle multiproofs) whose interactive
   controls obey `FireProgramAgreement` (`enabled ↔ Admits`). Distributed state scales smoothly
   across a **4-tier finality ladder**:
   - **Tier 0 (0 RTT)**: Local deterministic evaluation and `Judge` certificate checking.
   - **Tier 1 (0.5 RTT)**: Join-semilattice CRDTs (`Doc.Merge` pushouts and `LawDial.free` monotone laws).
   - **Tier 2 (1 RTT)**: Single-owner and disjoint-footprint `VaultTurn` fast paths.
   - **Tier 3 (2 RTT)**: Contended multi-party turns ordered by symbolic-mode `GenericSimplex` BFT,
     paired with `EpistemicConsensus` so distributed solver/prover/EDA swarms racing on open `Slot`s
     converge deterministically on the minimal-cost valid certificate.
5. **First-Principles Verified Hardware, Multiphysics, Photonics, PCB & RF (`Obend/Hardware`).**
   One mechanized library spans synchronous/guarded-action RTL (`HDL`, `Rules`, `FSM`), whole-book
   and sequential `Nat.rec` synthesis (`Compiler`), `LUT2`/`LUT3`/`CARRY8` tech mapping (`Synth`),
   Leiserson–Saxe retiming (`Retiming`), PnR bitstream verification (`PlaceRoute`), cleanroom
   metrology and RIE/ALD process physics (`FabuBlox`, `DRC`), 2D Prouhet–Thue–Morse oxide-curvature
   cancellation and SAR ADCs (`Analog`), open-silicon MPW signoff for `gf180mcuD`/`sky130A`/`ihpSg13g2`
   (`WaferSpace`), coupled electro-thermal multiphysics and Scharfetter–Gummel semiconductor PDD
   (`Thermal`, `Physics`), silicon photonics (`Photonics`), high-speed PCB stackups (`PCB`), SDR/RF
   transceivers (`RF`, `DSP`), and smart-contract multi-agent BOM/layout signoff (`AgenticEDA`).
6. **Pleasant, Low-Friction Interactive GUI (`obend-gui` over `Obend/FFI/Bridge.lean`).**
   Mathematica is *nice to use*. A thin, fast-compiling Rust GPU frontend (`wgpu` / WebGPU) talks to
   the Lean 4 kernel across an 8-function zero-copy `ByteArray` C-ABI (`Obend/FFI/Bridge.lean`),
   rendering live math boxes, constructive law-repair sliders, Lean 4 tactic infoviews, DeOS
   powerboxes, and 120fps instanced schematics/GDSII layouts in one unified workspace.

## What we hold to

The kernel admits by re-execution and checks certificates it never searched for. Every judgment
carries its quantifier, its trust ceiling (`checked | attested`), and its Merkle date (`dated_sound`).
Resources are not meanings: budgets, ticks, and tokens are declared and fail by name. A law is a
line a person can read, judged on every write, inheritable, and amendable by someone who did not
write it. Nothing lands beside; everything replaces. No per-theorem axiom lists; the crawling tree
census (`#assert_axioms_tree`) and mutation teeth (`#tooth`) are the gate.

## Lineage

François-René Rideau's *Lambda, the Ultimate Object* for the objects; nanodregg's contextual theory
for slots and justifications; minidregg's Core4, wide-pullback hyperedge turns, ZoE seats, certified
LP clearing, Simplex BFT, and epistemic consensus; breadstuffs' Dregg2 and DeOS for "every action is
a proof, not a promise", affordances as the projection of the gate, and blinded rehydration
membranes; Victor Taelin's Bend and BendTT for the affine leaf; Lean4Lean for the source reduction
table of `Obend/Lower`.
