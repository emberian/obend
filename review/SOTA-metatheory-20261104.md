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

## 3. The ingredients, named

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

## 4. The program, in order of leverage

Each item names the source module and the destination; nothing here is a spike.

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
   is written new; the lints in `obebuilder/DESIGN.md` §2.6 are its consumers.
6. Interaction nets: a `Chain.Cert` of active-pair steps over obend `ReductionMachine`'s net, one
   descriptor, a refinement theorem from its satisfaction to the net reduction; compare 2022/1211
   and HVM2 for the step shape; `EqSatHypergraph` emits rewrite certificates.
7. FHE: the `SameOpening` gadget on RLWE well-formedness, then t-of-n, then the zkml patch decision.
8. Distributed: DAG liveness; Hyper Hoare over the executor; Polis beyond two subjects.

## 5. What pass 2 is reading

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
