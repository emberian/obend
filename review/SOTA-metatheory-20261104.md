# To the state of the art and past it: breadstuffs, minidregg, obend (2026-11-04)

Read from the code, not the Markdown. Two workflow passes of readers with a skeptic each, every
cited theorem reopened at its line; pass 1 (seven areas) is folded in here, pass 2 (nine areas over
what pass 1 did not open) lands as a dated addendum. Sources: the Lean inventories in the session
scratchpad (`inv/metatheory-lean.tsv`, `crates.tsv`, `docs.tsv`), pass-1 reports
(`pass1-results.json`), `~/paperbin`. Claim labels follow the research repos: READ, INFERRED, OPEN.

## 0. Coverage, so nobody mistakes this for the whole

| region | inventory | opened by pass 1 | pass 2 |
|---|---|---|---|
| metatheory Lean files | 2,656 (Dregg2/Circuit 1,142 of them, 714K lines) | 274 modules | Emit families, Mina/Kimchi/Pasta/Pickles, Bridge, Exec, Games, PathOfAngels, Verify, Paco/Realizability/Deos/Metatheory, root emitters |
| Rust crates | 208 crates, 5.3M lines (headver 2.7M is a vendored tree) | fhegg-*, multi_step, blocklace_sync, verified_settle by grep | circuit, circuit-prove, verifier, recursion-verify, lean-ffi, exec-lean, crypto-*, auth, DSL, light clients, games |
| design documents | 826 (docs/deos 249, reference 102, metatheory/docs 59) | pointers only | pointers only |

What pass 1 did open, it opened properly: the skeptics confirmed every one of the cited theorems
exists at its line with the stated hypotheses, found no `sorry` in any cited file, and corrected
about a quarter of the reader claims on specifics (reachability from the default build, which pin
covers what, line drift, overstated prose). Those corrections are applied below.

## 1. The spine that is already there

Across the three trees one shape recurs, and it is the ingredient I had been missing when I read
Selvage alone.

**A certificate is a chain of a relation, and arithmetization is the replay of that chain.**
`Dregg2/Crypto/Chain.lean` (READ): `Cert R start goal` exists iff `ReflTransGen R start goal`,
`Cert.map` is functorial, `Cert.foldSound` walks a chain accumulating output under a prepend-sound
semantics. `Crypto/Hypergraph.lean` instantiates it twice: positional hyperedge replacement on an
edge list, and `cfg_parse_via_reduction` (a Mathlib `ContextFreeGrammar.Produces` chain iff the word
is in the language). Three automata rungs then sit on the one substrate, and the file says so
(`three_rungs_share_substrate`): regular (`DfaAsCert`, step relation `b.state = a.next`),
context-free (`CfgCompact`: a leftmost rule sequence replayed by a pushdown, `compact_sound` against
the Mathlib language), visibly pushdown (`VpaAsCert`, with `VpaDecidable` giving Alur–Madhusudan
determinization, complement by accept-flip, and a computable `decidable_template_equivalence`
with kernel `#guard`s). The parse-as-derivation chain closes end to end for Dyck against a
byte-pinned descriptor: `Circuit/Emit/DyckStackReplay.parse_sat_imp_replay_emit_unconditional`
(READ, pinned), which is the proof-producing arithmetizer the July design document promised, done
for one grammar. For regular guards, `GuardToAutomatonCircuit.guardDfa_decides` is universal over
`Value` words through the minterm encoding, and the `Deriv/` tower underneath is a faithful port of
extended regular expressions with symbolic minterm alphabets, kernel-decidable emptiness and
equivalence on a widening fragment, no lookarounds.

Three other spines, in the same style:

- **Logic to descriptor, verified-compiler shaped.** `TypedLinearPredicate.sound`, `fol_sound`,
  `BoolGraph.public_statement_sound` are once-per-fragment theorems instantiated by elaborator; the
  optimizer is translation validation (`DirectLogicOptimizerCertificate`: endpoints reconstructed
  from rule payloads, never trusted; `check_sound`); passive optimization is a two-law contract
  (security refinement plus completeness) per pass; Gabbay's direct arithmetization is formalized
  exactly over ℚ, priced into the prime field as an exact iff under numerator and denominator
  bounds, and the finite-field reading is refuted by Lean-proved BabyBear counterexamples.
  `ProofObjectDescent.verifiedEvidence_descends` is a sheaf-gluing theorem for locally checked
  witnesses under a complete cover.
- **Guards, authority, intents, dials.** One abstract `Spec/Guard` seam; `Exec/Program`'s
  `StateConstraint` as the live gate; caveat and token attenuation; the generative authority graph
  with an origin base case (Granovetter, mechanized); `Await`'s temporal ⊕ dataflow factoring;
  `ConditionalTurn`'s executable Kahn batch; `DriftStable`'s four tiers (monotone, reservation,
  locked, coordinated) consumed by the gated executor; ring settlement pinned to the FFI-exported
  executor (`cycle_individuallyRational`, Shapley–Scarf); flow refinement decided for the
  iteration-free fragment (`decideRefines_iff`). The genuinely new theorems in this area are the
  separations and refutations (`gwrite_conservation_trivializes`, `height_cannot_recover_causal`,
  `directed_conjecture_refuted`, `knows_ne_box`, `no_conflictFree_pushout`, `flow_choice_right_skewed`).
- **Proof systems and crypto.** Generic m-term unique-decoding correlated agreement
  (`Circuit/CorrelatedAgreement/{Scaffolding,BerlekampWelch,Theorems,Interface}`), parallel to
  Selvage's `ProximityGapUDTight` at the line and more general in arity; Blum offline memory
  checking fully proved (`MemoryChecking`, `UniversalMemory`); a query-bounded decision-tree
  adversary with birthday and forking as theorems (`RomOracle`, `RomQueryFloor`,
  `RomForkingExtractor`); ML-KEM correctness and the ML-DSA executable verifier with its ACVP pin.
- **FHE.** The only kernel-pinned FHE mathematics in the group is in `metatheory/Bfv`: exact BFV
  correctness (add, fold, one multiply, ring lift attaining δ_R = N, public-linear depth ceiling 42
  on the deployed fhe.rs 4096 parameters), an exact smudging bound exported into the running n-of-n
  Rust party, the cross-limb vFHE hole exhibited as theorems with the obvious fix proved vacuous, a
  dual certificate binding a proof relation and a BFV program to one opening, dark-market relation
  semantics (clearing optimality, collective opening soundness, uniqueness, quorum necessity, a
  metadata leak map).
- **Consensus.** DAG-BFT safety on a vote-count algebra transferred to the Cordial Miners commit
  rule with the quorum read off the lace, lifted to two nodes and to the executable `finalLeaderAt`;
  the Lean function gates live finalization in the Rust node through two FFI exports, with the Rust
  τ a logged differential when Lean answers in time. That model-runs-in-the-node tie is unusual.

## 2. Where we stand, by area

Verdicts from the readers, corrected by the skeptics. "Ahead" means nobody else has it mechanized.

**Automata, parsing, rewriting.** Ahead: VpaDecidable; the Dyck parse-as-derivation chain; the
private graph-rewrite SAT⇒Accepts bridge. Parallel: the Deriv tower against Veanes-style symbolic
derivatives (ours mechanized, theirs more general). Behind: Reef (regex proofs at document scale by
skipping alternating finite automata over a lookup argument); CoStar and the Menhir validator
(parser completeness, not just certificate soundness). Absent here: JSON and JWT parsing in zero
knowledge (zkLogin, Crescent); proof-producing equality saturation (egg); Lafont interaction
combinators and HVM2 (two papers in paperbin, nothing implements principal-port rewriting);
arithmetization of interaction-net traces (ePrint 2022/1211). Corrections that matter: the DFA
routing refinement rungs (`DfaRoutingRefine`, `DfaRoutingRung2`) are outside the default build; DFA
routing soundness is anchor-relative (nothing binds trace length or which automaton ran inside the
circuit); `GraphRewrite` is contextual hyperedge replacement on edge lists, not double pushout, and
`PrivateGraphRewrite` carries no pin; the interaction-net modules are Boolean gate trees with a
share binder, no active pairs.

**Logic arithmetization.** Ahead: the Gabbay formalization and refutation. Parallel: Coda (ours
compiler-level, theirs per-circuit); certified equality saturation (ours a fixed 14-rule root
rewriter with certificates, no e-graph). Behind: ArkLib and FlashProve (no proved IOP soundness;
the STARK floor is a class with no instance); Jolt and Lasso (quantifiers grounded exhaustively,
function tables public, no lookup lowering). Absent: Picus-style under-constraint analysis.
Specific holes: `FOLSatisfied2` accepts a false sentence on the empty trace; canonicality is a
Lean-side premise while the descriptor emits no range lookups (the Gabbay descriptor shows the
repair, never applied to `FiniteLogicDescriptorIR2`); `GateExpr` is imported by 72 files and has no
pin; `noWrap_boolean_hybrid_triangle` is trivially true and should not be cited.

**Coordination.** Ahead: Zoe-style offer safety on the ledger model; macaroon attenuation and
third-party discharge with teeth. Parallel: Pradic's Weihrauch non-distributivity (mechanized for
our flows), stellar resolution (behaviours built natively, no stellar resolution), CALM, Anoma
(ours mechanized settlement, theirs a spec), seL4-style authority backbone. Behind: I-confluence
decision procedures; choreographic programming (no language, no endpoint projection, no deadlock
freedom). Absent: biscuit's Datalog. Structural fact: a load-bearing spine and a large verdict
layer nothing imports (the three Biorth modules, the arithmetic, quantified and private closures,
`CaveatConvergence`, the epistemic atoms, `Centers`, `SemanticConvergence`, `BranchStitch`,
`GuardedHole`); several headline iffs are definitional and the files say so.

**Proof systems.** Behind ArkLib and FlashProve on the one thing that matters most: no theorem
binds a descriptor's satisfaction to a proof. `StarkSound` is a class (`CircuitSoundness.lean:917`),
`AlgoStarkSound` has no unconditional instance, `FriLowDegreeSound` is proved vacuous
(`FriCarrierVacuity.lean:123`) and still bound by twenty modules including the gnark emit path,
`ClosureAll`'s apex carries a hypothesis refuted at deployed width and its own header says not to
read it as applicable. Johnson-radius results exist only on 128-point toy setups. Recursive
aggregation is an assumed `EngineSound` record. UC is deterministic Prop-level; the one real UC
theorem is in Isabelle via a human-checked transport. Parallel: DECO as game-based unforgeability
reductions. Absent: WHIR and STIR vocabulary (Selvage has it), Nova-style folding with a security
notion, Twist and Shout memory arguments.

**FHE and dark.** Ahead on precision for one coordinate (exact finite smudging TV, failing side
proved) and on BFV noise analysis attaining δ_R = N. Parallel to Viand et al.'s vFHE framing and the
Cong–Smart line (same instinct, dealerless cut stops at `AwaitingCrossTermProvider`). Behind:
Rinocchio-style SNARKs over ℤ_Q (we prove the rescale is not a ℤ_Q polynomial, we have no ℤ_Q
prover); Zama lattice folding for bootstrapping; Jambon and Okada threshold FHE (we are n-of-n,
synchronous); CatCrypt (no Rust-to-Lean extraction, only golden vectors). Absent: VERITAS
authenticators, HEIR-style compilation with noise semantics. The honest status: no theorem that a
ciphertext encrypts the committed book (`SameOpening` is proved required and unbuilt), no malicious
share validity circuit, no t-of-n in Lean, no ct×ct arithmetization anywhere, zkml's 51-file patch
unapplied; verification still costs more than recomputation at these sizes.

**Distributed.** Ahead on the executable twin gating the node. Behind IronFleet, Verdi, LiDO on
liveness: every liveness theorem concludes a vote-count quorum, never the DAG's `Committed`; the
cross-node apex rests on four never-discharged hypotheses (union model per pair, content-address
collision resistance, `ThresholdAgrees` which fails at n = 3f+4, observer-local versus global
equivocation). Absent: any hyperlogic (Polis self-composes two subjects on finite arenas); verified
mechanism design. Noninterference covers one slice (`setFieldA`).

**Landing sites.** obend has no arithmetization layer, so every obend format re-executes and no
succinct or zero-knowledge certificate can be registered today; `Judge.Format` has no field for an
error bound or a named assumption, so `.attestable` and `.external` are defined and unused;
`LawExpr` has no `sumEq`, no commitment atom, no foreign-cell read, no quantifier, no temporal
operator; there are 35 `Format` declaration sites for 26 names with duplicates (`world-carry@1`
twice with different objects) and no registry uniqueness theorem; the dfa-policy reader lowers to a
`dfa-air` tag with no registered format, and `slot_confinement` is a theorem with no judge. The
obend automata port sets `Judge.Meaning` to the checker verdict in all three instances, so its
format-level soundness is tautological; the semantic theorems sit beside the judge, not in it.

## 3. The frame §1 and §2 had wrong: the system is the object

Ember's correction (2026-11-04): the ambition is formally verified, zero-knowledge, distributed
Houyhnhnm computing. The eleven chapters of Rideau's manifesto are the spec; dregg and deos are
the construction (`docs/deos/HOUYHNHNM-CONVERGENCE.md`, the 2026-06-19 frontier memory); the
metatheory is constructive knowledge: a principal's authority over a resource is its ability to
produce a witness the kernel accepts, under non-forgeability, monotone attenuation, kernel
enforcement and zk-checkability (`metatheory/CONSTRUCTIVE-KNOWLEDGE.md` §0). Read that way, §2's
comparisons are the comparison for one slice: chapter 10 says global deterministic semantics
matters only to verify other parties' computations, so Selvage, FlashProve and ArkLib are measured
by whether a light client holding no secrets can check a production, not by prover throughput.
The rest of the manifesto has its own theorems, and the trees already carry some of them. The
table is the ledger to keep; "exists" means a reader or the tree's own ledger located the
declaration, "pass 2" means the running second pass reopens it.

| principle (chapter) | the theorem it needs | what exists | status |
|---|---|---|---|
| orthogonal persistence; the log fully determines state (2, 3) | replay of the witnessed input stream over the deployed kernel is deterministic and reaches the same image | `Exec/CellRuntime` `replay_deterministic_run`, `checkpoint_restore_roundtrip`; `World::open_recovering` in Rust | pass 2 reopens; the Rust boot path is bound by no theorem |
| virtualization is branching; errors stay imaginary in unmerged branches (3, 4) | a branch holds no capability to main, so its effects cannot reach main: noninterference across the membrane | `Exec/CellRuntime.time_travel_fork`; `Deos/FogOfWar.noninterference`, whose hypothesis is its conclusion (pass 1, confirmed); `Proof/Noninterference` covers the `setFieldA` slice only | the central theorem of the branch story is vacuous today |
| settlement; revocation as the one non-monotone operation (3 and the frontier memory) | accept implies a genuine transition whose authority was live at the settlement tip | `Metatheory/SettlementSoundness.lean:153` and `Dregg2/Circuit/SettlementSoundness.lean:244`, pinned per the tree's own ledger; `finalized_commit_binds_revoked` | pass 2 reopens; rests on the STARK floor of §2 |
| the Monitor: an external, simple, complete watcher that reads the live artifact (3, 6) | claimed-versus-actual divergence is a decidable judge over the live state, recursively | `sel4/dregg-firmament/src/recovery_monitor.rs`, Rust only | no Lean statement; obend's `Judge.Format` is the natural home |
| non-stop change; code change as a transaction; linear-logic upgrade (5) | migration conforms, conserves and cannot brick; dropped data is dropped explicitly | `Exec/StateMigration` `migrate_conforms`, `migrate_conserves`, `migrate_anti_brick`; `Exec/CellUpgrade` | pass 2 reopens; the "explicit drop" half is prose |
| polycentric kernels; full abstraction enforced (6, 8) | every cell is its own kernel; no amplification; CapTP handoff and GC sound across vats | `Spec/Authority` (Granovetter with origin), `Exec/CapTP*` (`handoff_non_amplifying`, GC by lease), `Firmament/SeL4*` | pass 2 reopens; crypto enters as classes throughout (pass 1) |
| platforms not applications; no difference between using and programming (7) | the inspector and the document language are turns over the same cells | `Deos/PatchCategory`, `DocMerge`, `BranchStitch` (merge as pushout); dregg-doc crate; the self-hosting loop (`docs/deos/SELF-HOSTING-LOOP.md`) | pass 2 reopens; `BranchStitch` has no importer (pass 1) |
| turtles: building down, no turtle special; meta is down (4) | each lowering preserves behaviour, so an abstraction can be re-chosen later | obend `Lower` (Lean to Core4 to Leaf to RTL to silicon) with `link_bequiv_bindBookPins` landed today; Dregg2 `Metatheory/CertifiedPresentationChange` | obend is the turtle tower of the group; the hardware floor is the FPGA lane |
| the Urbit critique: metaprogramming plus proven equivalence, not a frozen VM with jets (10) | a fast path is admitted only with an equivalence proof to the semantics | obend's bisimulation-up-to and the specialization judge are exactly jets-with-proofs; `Theory/NockCost` in minidregg prices the alternative | ahead of Urbit by construction; the claim needs the lowering chain closed to silicon |
| build system as the dev system at the meta level; hermetic, source-addressed (9) | the demand-driven memo is the build | the M2 memo (frontier memory); obebuilder's segment ledger | not a theorem anywhere; obebuilder is where it would live |
| bad tools not bad users; preemptive enforcement (8, 11) | the harness refuses, the agent does not promise | obend `#tooth`, minidregg hypothesis ledger, Dregg2 `Verify/` ratchets, obebuilder lints | the method, not a feature; pass 2 compares the three instrument sets |

System-level state of the art the earlier sections never named, which is what "beyond" has to
be measured against: seL4 and l4v (integrity and confidentiality theorems the authority spine
already templates on), CertiKOS and Hyperkernel (verified kernels with no capability network),
Spritely Goblins and OCapN (object capabilities with transactional heaps and time travel, no
proofs), Agoric SwingSet (vats, upgrade, no proofs), Croquet and TeaTime (replicated deterministic
computation, the persistence-by-replay story without a verifier), Unison (content-addressed code
and abilities), Nix and Guix (hermetic source-addressed builds, chapter 9 realized without
verification), Pijul and the local-first line (Automerge, Willow: patch theory and sheaf
restriction without authority), Sandstorm (the grain model the tree already bridges to), Urbit
(the foil), Mina (the succinct cross-party verification slice, from ember's own history), and
Robigalia (the 2015 idea this continues). No system on that list has the combination: capability
kernel, conservation, verified executor exported into the running node, light-client checkable
settlement, branching with consent, and a hardware lowering with equivalence proofs. The trees
have each piece in some state; the proof-system items in §4 are what the settlement and
light-client rows rest on, and the three vacuous or absent rows (membrane noninterference, the
Monitor as a judge, the build as a theorem) are the system-level gaps.

## 4. The proof-system ingredients, named

What "formal to the bones" needs that is not in any of the three trees, or is in one and not the
others:

1. **The chain-certificate substrate as the relation IR.** `Chain.Cert` is Mathlib-light (a local
   `ReflTransGen` suffices) and is the right common object for degg's Dark Relation IR, obend's
   laws, and every automaton and rewrite certificate. It should be the thing obend ports first.
2. **A descriptor semantics in obend.** Nothing arithmetized can land until obend has a
   `Satisfied2`-like denotation of a gate system. The honest source is minidregg
   `Compiler/PredCompile.lower_correct` with `Compiler/Air` and `AirFlatten`, as a new
   `Judge/Air.lean`.
3. **An error-bounded, assumption-carrying `Judge.Format`.** Two fields: the assumption or error
   the `Meaning` is conditioned on, and a sigma-typed object. Without them BaseFold, FlashProve
   and the rank-1 and low-rank zkML checks cannot be registered honestly.
4. **Lookup-centric automaton steps.** One DFA step as one lookup (Lasso, Jolt, Reef's SAFA) rather
   than gates; the `TableDfa` already is a table. This also closes the anchor-relative hole: commit
   the table, bind the trace length.
5. **Interaction nets as the universal execution model and its one descriptor.** obend already has
   the hardware (`Hardware/ReductionMachine` interaction nets, `OpenHypergraph` with adjoints,
   `EqSatHypergraph`); Dregg2 has the trace checkers; nobody has the universal circuit over net
   traces (ePrint 2022/1211) or Lafont's combinators. A rewrite history is a `Chain.Cert` of
   active-pair steps; one descriptor for all programs is the "beyond" here, and it is the point
   where obend's silicon and the proof work meet.
6. **Proof-producing rewriting.** obend's `EqSatHypergraph` should emit certificates in the
   `DirectLogicOptimizerCertificate` discipline (endpoints reconstructed from rule payloads); the
   private graph rewrite should become double pushout with a gluing interface and dangling
   condition before it is called graph rewriting.
7. **Verified IOP soundness.** Import ArkLib's Johnson mutual correlated agreement (zero sorry,
   same Lean), bridge to Selvage's `HaboeckMCAAt`, retire `HaboeckTheorem2` and
   `WHIRConjecture412` from the allowlist and the toy Johnson chain in Dregg2; write Selvage's
   executable BaseFold verifier with its theorem (FlashProve's shape), retire `FriLowDegreeSound`
   and every binder on it.
8. **The twelve law forms.** Witnessed and third-party atoms; event-shaped temporal (until, since,
   cooled-since, rate bound, challenge window); multi-field affine and polynomial relations
   (`sumEq`, `Σ cᵢ·fᵢ ≤ k`, `x·y = k`); bounded quantifiers and committed-set membership; private
   predicates over commitments; epistemic and finality guards; cross-cell laws; intents as law
   objects with a fulfil and refund lifecycle; a coordination dial with a `thirdParty` verdict and a
   cost ladder; decidable refinement with an unsat certificate; first-order caveats in `Mandate`
   instead of an opaque closure; late-filled slots with eager guards. Each has an honest source
   module named in the pass-1 report.
9. **One statement audit across the three trees.** minidregg's hypothesis ledger (PROVED, REFUTED,
   OPEN families; VACUOUS, STALE, TOOTHLESS consumers; planted defects; shrinking allowlist) over
   obend and over Dregg2, unified with Dregg2's `Verify/` ratchets and obend's `#tooth`. Pass 1 found
   whole areas with no row in any ledger (automata, logic arithmetization, BFV, dark market), pins
   missing on load-bearing modules, and refinement rungs outside the default build.
10. **Rust bound to Lean by something stronger than golden vectors.** Aeneas or hax extraction for
    one crate first (pass 2 names the candidate); the current binding is vectors, FFI exports and
    Lean-modelled programs.
11. **The FHE object that is proved required and unbuilt**: RLWE well-formedness in Lean,
    `SameOpening`, t-of-n decryption, ct×ct arithmetization (apply or retire the zkml patch), the
    Rényi machinery connected to `Bfv/Smudging`.
12. **Liveness that reaches the DAG, and k-safety as a logic.** A theorem of the form "under
    GST-style delivery and honest-leader recurrence some wave has `Committed`", and a Hyper
    Hoare-style logic over `execFullTurnA` so noninterference grows past one slice.

## 5. The program, in order of leverage

Each item names the source module and the destination; nothing here is a spike. Reordered after
§3: the system theorems lead, the proof-system items are what they rest on.

0. The three system-level gaps of §3: membrane noninterference as a real theorem over
   `execFullTurnA` (a Hyper Hoare-style unwinding, replacing `FogOfWar.noninterference`); the
   Monitor as a registered judge whose object is the live cell state and whose certificate is the
   divergence witness; settlement soundness reopened with its STARK floor named as a hypothesis in
   the `Judge.Format` sense rather than carried as a class.
1. obend `Judge/Air.lean` from minidregg `PredCompile` + `Air` + `AirFlatten`; `Judge.Format`
   grows an assumption field and a sigma object; one registry with a uniqueness theorem
   (`Logic/Obligation.findFormat` and `Vault/Hyperedge.findJudgeFormat` collapse to one).
2. `Chain.Cert` into obend (Mathlib-free); `AutomataConfinement`'s three formats get a semantic
   `Meaning` (the derivation relation, not the checker verdict), `TableDfa` gets its state space,
   the digest becomes an abstract compress with a named collision hypothesis, the hoard-clearing
   pillar moves out to `Judge/Clearing`.
3. Selvage: ArkLib Johnson import and bridge; `BaseFoldVerify` executable with
   `basefold_verify_sound` in the ROM at the ledger's bound, Rust twin on the conformance-vector
   discipline, registered in obend as `basefold@1`; FlashProve beside it as `flashprove@0.16`.
   Import from Dregg2 into minidregg: `CorrelatedAgreement/Interface`, `MemoryChecking` (port the
   `List.Perm` form `memCheck_iff_perm` for obend), the `RomOracle` family as the adaptive adversary
   Selvage says it is owed.
4. Laws: `sumEq`, `hashEq` (minidregg `Pred/Core`, `HashEqDigest`) into `LawExpr`, `LawCompile`,
   `LawDial` with the `thirdParty` verdict; `Pred/Frame.reads` so footprint pins derive from the
   law; `Pred/Satisfiable.certificate_unsat` replacing `solveLawWitness`; `Kernel/ObjectLaw.
   package_law_enforced` as the end-to-end vault theorem; then the temporal, quantified, private
   and cross-cell forms from `Authority/*`.
5. Instruments: the hypothesis ledger core into `Obend/Census.lean` (prefix `Obend`, no Mathlib,
   obend plants); pass-2's matrix of vacuity classes against the three instrument sets decides what
   is written new; the lints in `obebuilder/DESIGN.md` §2.6 are its consumers. The §3 ledger of
   principles against theorems becomes a row family in the same instrument.
6. Interaction nets: a `Chain.Cert` of active-pair steps over obend `ReductionMachine`'s net, one
   descriptor, a refinement theorem from its satisfaction to the net reduction; compare 2022/1211
   and HVM2 for the step shape; `EqSatHypergraph` emits rewrite certificates.
7. FHE: the `SameOpening` gadget on RLWE well-formedness, then t-of-n, then the zkml patch decision.
8. Distributed: DAG liveness; Hyper Hoare over the executor; Polis beyond two subjects.

## 6. What pass 2 is reading

The Emit families and whether each has a refinement theorem and a Rust consumer; the Lean Kimchi
and Pickles models and what accept implies; the inbound light clients and the zkOracle stack; the
executable kernel, its FFI exports and the CapTP theorems; the verified games and their AIRs; Path
of Angels as the consumer map of the whole substrate; the `Verify/` instruments against the
hypothesis ledger and `#tooth`; Paco, realizability, categorical semantics, Deos patch theory; the
Rust prover stack and every Lean binding point, with the first candidate for extraction. Its
addendum follows this file.

## Sources

Pass-1 reports and verdicts: session scratchpad `pass1-results.json`. Papers: Reef (ePrint
2023/1886), 2022/1211, Crescent (2024/2013), Zombie (NSDI 2024), zk-regex (PoPETs 2026), egg
proofs (arXiv 2209.03398), Coda (arXiv 2304.07648), Picus (ePrint 2023/547), ArkLib, FlashProve
(Nov 2026, `~/paperbin/anthropic2026-flashprove-*`), Pradic (arXiv 2408.14999), Eng and Seiller,
Bailis I-confluence, CALM, Velisarios, IronFleet, Verdi, LiDO, Bythos, Cordial Miners, HyperLTL,
Hyper Hoare Logic, VeriFx, Viand et al. 2023 (arXiv 2301.07041), Rinocchio, VERITAS, Jambon
(2026/2290), Okada (2026/957), Cong et al. (2026/2403), CatCrypt (2026/604), Zama lattice folding.

---

## Addendum, pass 2 (same day): the regions pass 1 did not open

Nine inventory-driven readers with a skeptic each; eight returned (the Exec kernel and CapTP
reader overflowed its context and is re-running as two narrower slices). Every reader opened every
file in its slice at least to header depth; skeptics reopened every cited line; a quarter of the
claims were corrected on specifics, none refuted outright. Reports and verdicts: session scratchpad
`pass2-results.json`. What follows is what the coverage table in §0 was missing.

### A. The emitted circuits (Circuit/Emit, 305 files outside Mina and Gnark)

`DescriptorIR2.Satisfied2` is the denotation everything hangs on: per-row constraints over a
(local, next, public, challenge) window, lookups as table membership, memory as a global leg
(`Nodup`, closed, disciplined, `MemCheck` by the Blum weld). The lowering is certified at the
compiler level (`EffectLowerCertified.lowerAir_forces_gates`: every lowered gate that holds forces
the source constraint), `EffectVmEmitV2.graduateV1` is sound and complete, and the transfer
effect has the full chain (`transferDescriptor_full_sound`, pinned). The 28 IR2 effect descriptors
and the rotation registries are consumed by Rust by sha256 fingerprint; 132 by-name descriptors
carry Lean byte goldens. What is hypothesis everywhere: lookup soundness and chip-table
genuineness (`ChipTableSound` on the Poseidon2 chip; `LogUpSoundness` exists and is reachable but
`Satisfied2` takes membership as primitive). Thirty-three refinement rungs (Temporal, Quantified,
Fold, NoteSpendingLeaf, CommittedThreshold, MultiStepChain, IvcStateTransition, the Rung-2
bindings) are compiled by no target and sit on an orphan allowlist. Temporal until and since and
the bounded quantifiers have no emitted circuit. The compound predicate's AND/OR/threshold is not
recomputed in circuit, with a machine-checked countermodel. `Exec/CircuitEmit`'s rail is dead:
its theorems are about a wire no Rust path interprets. State of the art: parallel to Coda and to
CompCert-style lowering; behind ArkLib and FlashProve on the step from satisfaction to verifier
acceptance; Picus-style under-constraint analysis absent.

### B. Mina, Kimchi, Pickles (219 files)

A Lean model of the Kimchi verifier, the Pickles step and wrap statements, Lean-synthesized
step-main and wrap-main circuits proved by a pure-Rust prover, and Lean-authored BabyBear AIRs for
the wrap verifier legs. The Mina specification objects (binprot, state hash, chain selection,
sliding window, VRF threshold) are kernel-proved with real-block differentials; everything
wrap-arithmetic is one-block kernel plus seven-block compiled conformance. No theorem says an
accepted wrap proof implies a valid Mina transition: `ipaOk` and `transcriptOk` are Bool carriers,
and `real_block_accepts` passes all three carriers as literal `true`. The deployed Pasta MSM
descriptors still ride the 9×30 multiplier core whose forcing lemma is over ℤ only, while
`PastaFieldSound` exists and has not been rebased under them. Heavy `native_decide` in the welds,
with the tree's own record of three such theorems being false for 62 commits because the module
did not build. The `#assert_compiled` discipline (re-run the oracle, refuse name recognition) is
the right answer to that and obend should take it. Ahead of Mina Foundation's own RFC-0011
deliverables, which have no public artifact; behind Nethermind's verified-verifier and the
Bailey–Miller Groth16 soundness on having a soundness theorem at all.

### C. Light clients and the oracle (70 Bridge and Lightclient files, 14 crates)

The central finding is a shape error repeated across every inbound client: the `CryptoLeaf` and
`EthLeaf` collision-resistance carriers entail global injectivity, so they are uninhabitable at
any compressing hash, and every no-forgery theorem that takes them (`eth_no_forgery`,
`tmNoForgery`, `sol_no_forgery`, `mid_no_forgery`, `mpt_noForgery`) is vacuous at a production
leaf. The Emit fold modules know this and carry the honest `pairSepOn` floor; the Bridge modules
never do. Solana and Midnight have no export and no Rust caller, so the deployed decisions are
Rust's, with inconsistent strictness between its two tallies; Midnight's path verifies no GRANDPA
justification. The ETH and Tendermint AIRs have every public anchor decorative
(`AnchorConnectivity` census), so the portable proof binds no chain state. BLS and Ed25519 are
witnessed bits; the gadgets stop before the pairing and the signature equation. The Tendermint
path is the healthy one: Lean gate first, Informal's verifier second, conjunction. zkOracle is a
TLSNotary deployment with a verified parse certificate and injection-free matcher downstream; the
2PC and notary trust are not modelled. Behind SP1 Helios, Telepathy, zkBridge, Plumo; parallel to
Informal's Tendermint client; Etheorem is the executable spec to refine against if Ethereum is
ever modelled again.

### D. Games (53 files plus Automatafl's 32 emitters)

Automatafl is the strongest application chain in the group: the rules are proved (conservation,
permutation invariance, n² termination) and the emitted AIR is proved to refine them from
`Satisfied2` of byte-pinned descriptors (`astep_sat_imp_automatonStepCfgN`,
`resolve_sat_imp_roundBoard11`, the capstones), with executable falsifiers for earlier wounds. No
prior work has both halves. Honest residuals: capstones carry clash and resolvability as
hypotheses instead of deriving them; the winner is never a public input; seat identity is outside
the proof; the sealed-move leg is proved not to compose with the live host; the full match fold is
`#[ignore]`d everywhere with one documented run. MultiwayTug's AIR and program are reachable from
no target. The private descriptors (preference, raid, shuffle) never state hiding; the shuffle
proves no randomness. The beacon relation used by dice and procgen is in Rust only; `Dungeon`
takes it as an opaque natural. Behind Bayer–Groth shuffles and drand; ahead of every formalized
game-rules effort on the rules-to-circuit refinement.

### E. Path of Angels (161 files, 14 crates)

The consumer map of the substrate. The content contract forbids prose and admits only numeric
authored content through a validator proved sound and complete against a Prop; the judge wire is
one exported function with empty string as the sole refusal, a strict decoder with injective
accepted bytes, and a success-iff theorem; hidden instances are derived at judge time from a
per-slot commitment and re-derived inside admission; event sourcing has kernel-checked replay and
snapshot-cache equivalence laws; constructor-privacy boundaries are pinned per runtime. Those six
shapes are the application discipline obend `apps/` should adopt. Gaps: byte-layer parser
adequacy is named (`CanonicalCodec.ParserAdequate`) and proved nowhere; the hidden-instance
commitment has no hiding or binding theorem; signature verification is external; the network
judge is sound only under a prose precondition about the node; `native_decide` remains inside
the FFI closure in ten non-fixture modules, contrary to the fixture split's own claim; the
dreggnet game-infrastructure crates have no Lean at all. Ahead of MUD and of every surveyed
interactive-fiction engine on verifiable content and event sourcing; behind Dojo on proved
execution leaving the node; no attested-inference seam by design.

### F. The instruments (Verify/, Claims, Tactics, scripts, wip)

breadstuffs has the richest refutation-armed gating of the three trees: `FloorRatchet` with a
baseline that may only shrink and five throw sites before a floor is honoured,
`FreeConclusionRatchet`, `KeystoneLint` with satisfiable and teeth companions, `ToothCheck`,
`ApexPremiseVacuity` (the four injectivity floors refuted at BabyBear through `compress` alone),
`#assert_compiled`, `#assert_depends_on`. It is behind the 2026 Lean dataset-defects checkers on
the generic contradiction attempt, empty-domain and unused-binder checks, and it has no catch for
tautological statements, Prop-valued typeclass fields entering as instance arguments, empty-carrier
quantification, fixture-only decides, checker-verdict meanings, or duplicate baseline rows (426
names registered twice with slack logged only). `CLAIMS.md` is stale on its own headline
statements (zero `native_decide` against 603 files that use it; twenty parked pins against
hundreds live) and its rows are checked by nothing in any workflow; the prose-claims script, the
orphan check and the ratchet-darkness check are hand-run. The reader produced the unified design
obebuilder §2.6 asked for: one census pass over the elaborated environment emitting typed findings
`(decl, class, evidence, verdict)` against a checked-in baseline, ten classes each with its honest
source module (obend Census for reachability, `#assert_compiled` and `#assert_depends_on` from
Dregg2 Tactics, `FloorRatchet.surface` and `InjSpelling` generalized for refuted families,
`FreeConclusionRatchet` over every theorem rather than tagged keystones, minidregg's STALE and
TOOTHLESS verdicts and inhabitation check, `atp-checkers` VacuousCheck, `ToothCheck` same-object
companions, `#docs_census` with the mechanical subset of prose claims, and new code only for
tautology detection and baseline hygiene).

### G. Foundations (158 files)

Paco is a faithful lattice-level port with the full up-to and companion tower, sorry-free, used
load-bearingly only by `CoinductiveAdversary`; its respectfulness route rests on a class
(`ExtCompatImpliesCompat`) that Coq's paco proves unconditionally; the vendored source says MIT
while its LICENSE is Apache 2.0 and the upstream repository could not be found. The Realizability
layer is a clean evidenced-frame and tripos-fragment library interpreting nothing in Dregg2;
`CONSTRUCTIVE-KNOWLEDGE.md`'s link from the authority thesis to realizability is prose. The
categorical semantics has `Initiality` partial inside its own file but discharged tree-wide by
`Argus/CompileFold`. Deos: `PatchCategory` is the best mechanized categorical patch theory the
reader could find anywhere (pushout-up-to-iso uniqueness, conflict as missing pushout), with
dregg-doc linked by comment only; `FogOfWar.noninterference` and `Vault.donation_immunity` are
tautologies inside pin lists; `InfoFlow/Confinement` refutes full noninterference on the kernel
(credit signal, refusal timing) and proves the integrity half, which is the honest statement §3
should cite instead. `ForMathlib/PolishchukSpielman` is a full mechanization of the corrected
bivariate lemma with no public counterpart found; Guruswami–Sudan's interpolation half is a named
Prop; Berry–Esseen is a tilt identity, not the bound. One real `sorry` in the whole pass:
`Bignum/LedgerBalance.biasedLimbs_valid`, imported by nothing.

### H. The Rust prover stack (37 crates)

Plonky3 at a pinned revision (BabyBear, Poseidon2 width 16, LogUp, FRI arity 8, log blowup 6, 19
queries), with a Lean-owned parametric FRI ledger (`FriLedgerSound`, `FriArityTransfer`) whose
per-fold bound holds only for words at least 496 of 512 far and is false in the Johnson band;
`DeployedRefines` (Rust verify implies Lean `verifyAlgo`) is an undischarged Prop with mutation
tests as its only evidence; `EngineSound` is assumed. The Lean to Rust binding is 227 exported
symbols through `dregg-lean-ffi` with a C shim, archive-freshness tests and a cfg ledger, plus
819 `include_str` sites of Lean-emitted artifacts; the archive seed is not in the repository, so
a fresh checkout builds dark with every Lean-backed decision silently absent. The verifier shares
the prover's descriptor interpreter and links the recursion prover. Whole-history proofs for
grains are not minted (`WHOLE_HISTORY_GAP`). The post-quantum and threshold crates are reference
implementations bound to Lean by API models and doc comments, not vectors; dregg-pq's fallback is
unaudited RustCrypto behind an abort gate where libcrux would be the verified drop-in. Nothing is
extracted; hax 0.4's Lean backend is the stated upstream path and the FRI ledger's config types
are the first candidate. obend's `hardware/rust-ffi` has no build script, no C linkage and a
Rust-versus-Rust codec test; the dregg-lean-ffi build, shim, freshness and fail-closed oracle
patterns are the model to copy.

### What pass 2 changes in §5

- **A seventh system-level row.** The light-client carriers are the same shape error as
  `FogOfWar`: a hypothesis that cannot be inhabited at the deployed instance, carried through
  `#assert_axioms`-clean theorems. The unified instrument's class 3 (refuted families) and class 6
  (inhabitation) would have caught both; it moves ahead of item 1 in §5, because every other item
  lands theorems that the instrument must be able to refuse.
- **Rebase, do not rewrite.** The Pasta MSM tower onto `PastaFieldSound`; the Bridge no-forgery
  theorems onto the `pairSepOn` floor the Emit folds already carry; the thirty-three orphan rungs
  into the default build or out of the tree.
- **The application discipline is settled** by Automatafl and Path of Angels: rules first with
  conservation and invariance proved, the emitter second with a `Satisfied2` capstone, a
  single-export judge wire with a success-iff theorem, numeric content contracts, event sourcing
  with replay laws, constructor-privacy boundaries. obend `apps/` adopts those six shapes.
- **obend's FFI is the first concrete port**: build script, C shim, freshness ledger, fail-closed
  oracle registration, one Lean root for the exported closure, Lean-emitted goldens in place of
  the Rust-versus-Rust test.
- **Two licences and one sorry to settle by hand**: the Paco provenance, and
  `LedgerBalance.biasedLimbs_valid`.

The Exec kernel and CapTP slice follows as a second addendum when its two readers report.

### I. The executable kernel and the FFI boundary (second addendum, two readers)

The kernel is `execFullA` over a 31-constructor per-asset action type, with a step invariant of
four conjuncts (per-asset ledger vector, log suffix with receipt membership, strict log growth, a
per-kind obligation) proved for every arm (`execFullA_attests_per_asset`), a handler registry whose
obligations are proof fields on the handler record so that a generic `turn_conserves` falls out by
list induction, and an admission gate of eight legs with a prologue that is never rolled back. The
deployed entry is `dregg_exec_full_forest_auth` in `Exec/FFI.lean`, and `FFI/Refine` proves, by
`rfl`, that the export equals the model on parseable input; it is the only export with such a
theorem. Production prefers the no-copy `execDirect` twin, which has no theorem and four `#guard`
fixtures; the Rust side installs Lean's verdict unconditionally on the covered set and treats
disagreement as a Rust bug. Corrections the skeptic made: conservation does not reach `Core`
through the `ConservesStep` instance (its proof is a simp over a zero measure); the Claims ledger
pins a different `recCexec_attests` from the one the executor proves; the record-cell
step-completeness predicates are disjunctions with no conservation conjunct.

What is missing at this layer is exactly the orthogonal-persistence row of §3: no replay-determinism
or log-determines-state theorem over the deployed entry; `Durability`'s headline theorems are `rfl`
(recover and live are the same definition); `Receipt.replay_deterministic` is a tautology; the
hash-linked receipt chain is a separate structure under injectivity and freshness hypotheses,
connected to admission only through those hypotheses, while the kernel's chain-link conjunct is a
list-length fact. Gas is scalar-only and unwired. Migration is modelled (`addField`, `renameField`)
but no executor arm calls it and there is no explicit-drop obligation. The Lean compiler, C codegen
and runtime are unverified TCB, and the project does not claim otherwise. Behind CompCert and
CakeML on the executable chain; parallel to seL4's layering without its refinement to code;
Verus, Aeneas and CertiCoq absent.

### J. Capabilities, cells, forests, Argus and the firmament

Non-amplification is a theorem at four layers (attenuation on the cap set and on conferred rights;
CapTP handoff over an abstract semilattice and over the concrete Bool lattice; the executed
delegate-attenuate arm in the gated forest), with handoff unforgeability under a named
`K.unforgeable`, GC by lease with the undecidability of distributed death proved rather than
assumed, pipelining shown unable to mint authority, and the N-ary conservation discipline (derived
within a cell, carried as an explicit and proved-irreducible hypothesis across cells). Against the
state of the art this is ahead of OCapN and Genode, which have no machine-checked semantics, and
parallel to the third-party model checking of SwingSet. The seL4 transcription is one
derivation rule with the architecture branch opaque and three bridge fields unproved; nothing in
the firmament states scheduling, interleaving or confidentiality. The Rust binding is a runtime
gate seam that captp can fill with a non-Lean "assume non-amplifying" implementation (two such
fillers exist), the cell crate declares itself the legacy unverified duplicate, and six effects
lack an Argus weld. `EmitRoundtrip` relates Lean's emitter to Lean's parser only.

For obend, the two readers agree on the ports: `Vault/Mandate` takes `Agent/Mandate` wholesale
(target, keep at most held, budget, caveat, sub-delegation that clamps and narrows, the
well-attenuated tree invariant and its four theorems); `Vault/Hyperedge` keeps the wide-pullback
statement with `hyperedge_sound_needs_binding` as the honest negative; the ChainLink conjunct of
the deployed entry becomes the hash-linked receipt chain with injectivity and freshness as named
hypotheses, with log-determines-state proved over the entry the FFI actually calls; host-fed
inputs become an explicit `HostFacts` record with a `Reflects` relation; the handler-registry
shape replaces an effects-by-invariants matrix; the FFI root is one manifest module whose import
closure is the export surface, with the gate mandatory rather than a seam.
