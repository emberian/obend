# Decisions ledger, 2026-10-29 to 10-31

Every decision a lane or reviewer addressed to Ember, with who took it and on what authority.
"Standing approval" is Ember's "let's raise our ambition and I approve. go forward as you like"
(10-31). Anything marked TAKEN BY CLAUDE is reversible; the cost of reversing is stated.

## Decided by Ember

| decision | choice | where |
|---|---|---|
| Align the checker with declarative typing, with solvers where completeness is out of reach | yes | `review/CHECKER-COMPLETENESS-REPORT`, Argon's answer, `METATHEORY.md` §6 |
| Type agreement descends into types, equi-recursively (option c) | yes | `REPORT-EQUIREC-20261031.md` |
| Stored selection: incumbent-first default, chooser override, policies per slot | yes, after Astra's analysis | `astra/ASTRA-SELECTION-20261031.md`, `Obend/Slot/Selection.lean` |
| No per-theorem axiom lists; one crawling census | yes | `393eb2b`, memory `feedback-no-manual-axiom-lists` |
| Statements may be restructured for compositionality | yes | ProofEng lane |
| The 15 choice-free `#print axioms` pins stay: they pin something nonstandard (a choice-free set), which the census cannot state | yes | `lean/docs/REPORT-PROOFENG-20261031.md` |
| Modularity first: Lean modules and typeclasses from day one | yes | `REPORT-20261030.md` |
| Build our own thing; depend on Bend, never fork it | yes | `DESIGN.md` §7 |

| `quote` is a kernel function on held terms and `splice` a turn; no new `Term` constructor; program-level quote on values refused | yes (2026-11-01) | `review/QUOTE-ORIENTATION-20261101.md` §3, §8 |
| `linear` separates from `affine` in the checker: exact discharge enforced in the kernel | yes (2026-11-01) | gates T7; `review/ALGEBRAIC-SUBTYPING-20261031.md` §5.1 |
| Nominal kinds (the kind cell; every instance tagged; the kind's law an ancestor; dispatch by kind) | yes (2026-11-01) | `lean/docs/REPORT-EXTENDS-20261031.md` |
| REFLECTION's open question: the intensional fixed point is inside the knot with the description a term (Löb's rule) | taken by Claude from the literature, 2026-11-01 | `review/QUOTE-ORIENTATION-20261101.md` §2.6, §8 |

## Taken by Claude under standing approval (reversible)

| decision | what was taken | cost to reverse |
|---|---|---|
| **What a wikilink is** (Doc lane) | (c): `[[Beta]]` cites identity only; `![[Beta]]` and `[[Beta#^id]]` are byte cites; a byte cite stays current while its bytes are unchanged (rule b). The LawDoc brief says "Ember chose (c)"; that was my reading of standing approval, not a choice you made. | `Cite` and `Vault.read` in `Obend/Doc/{Section,Render}.lean`; theorem shapes unchanged; the Vault lane is building on it now |
| Lost reply with no ending (Runner) | (b): an `abandon` event, obligation kept, run ended | one constructor, one spec clause, one proof case |
| Initial plan choices rechecked at dispatch (Runner) | citations added to `Cfg.init`, default none | small |
| Package law at adoption and relaw (LawDoc) | (b) adoption judged with old = new state; (c) relaw of a package law refused, change is by upgrade | two compiler arms and two theorems |
| Front end grant (Elab) | (b) `checkWork` replaces `typeFuel`; cohorts re-pinned at 43,237 | revert one commit; cohorts back to 4096 |
| Inherited refusal carries `{by, reason}` in its own verdict type (Law) | kept the richer verdict | a kernel judging by effective laws must accept it; alternatives were unnamed reason or a Core4 label-join primitive |
| Journal supports are the transitive meaning closure (lane B) | kept | two one-line changes to the flat scheme |
| `Accepted`'s constructor public; wire theorems in a proof module (lane C, D21) | kept | none; Kimi's D5 argument covers it |
| Public constructors on execution evidence (lane A, D5) | kept, closed by Kimi's review | none |

| `BEquiv` (`Equiv/Behaviour`) quantifies over every context including `metadata`, so it is ≈r; the extensional ≈b is `Observed .b` (Quote-1's `observed_r_iff`). Rename queued after the Cost lane lands so no lane rebases across it. | taken by Claude under standing approval, 2026-11-01 | `lean/docs/REPORT-QUOTE1-20261101.md` |

| Branch uses: every branch vector joins by pointwise max (`Ty.joinUses`), with a separate agreement check that a `linear` hypothesis is used equally on every arm; the instruction said unrestricted sums, the lane corrected to max because the count must be term-only for `Checked.eq_of_type` and `prepare_checks` | taken by Claude under standing approval 2026-11-01 (instruction); corrected by the Linear lane (representation); recorded here as the accepted deviation | `lean/docs/REPORT-LINEAR-20261101.md` round 2 |

| Tier 2 (teeth and census) runs pre-push via `core.hooksPath lean/tools/hooks`; an engineering rule, not a decision; a hook on a clone is not proof it ran | taken by Claude | `lean/docs/REPORT-BUILD-20261101.md` |

| World resolution has no shared semantics with term-level `fix`: policies are history-dependent choice functions inside the monotone envelope of the invariants (Gemini Experiment 1, kernel-verified); the support-set generalization is adopted as per-cell admissible-pin domains | decided 2026-11-01 | `review/GEMINI-CHECKPOINT-20261101b.md` §3 |
| The equation judgment of the claim logic is partial (`HoldsEq`); ground and Lean certificates prove total convergence; the receipt names which | taken 2026-11-01 from Gemini's finding | §1 |

| `extendRecord` preserves typing up to `RowRefines`, not `sameType`: kept as stated in `step_preserves_typing` (Gemini, 2026-11-01). Dropping shadowed fields in `Ty.overlay` was refused: it breaks `overlay_instantiate` on open row templates, row congruence across recursive unfoldings, and the W25 shareability audit. If exact `sameType` is ever wanted, the route is a shareability premise on shadowed fields in `PartialTyping.extend`, not `overlay`. | decided 2026-11-01 | `review/GEMINI-CHECKPOINT-20261101b.md`; `REPORT-SOUND-20261101.md` §6 |

| Accept 52 modules per checker edit for now; the half-measure (unexpose `Bidirectional`, its readers `import all`, `decide` fixtures to tier 2) is queued for the Build list, not taken, since an `elaborate` edit would still rebuild all 52 | taken by Claude under standing approval, 2026-11-01 | `REPORT-ONECHECKER-20261101.md` |

| An impact receipt names the world's root (digest of `.obend/world.json` or of the workspace's records and releases), so `obend verify --world` re-exports the question and refuses a receipt whose table is not the world's; the same move as chaining the view roots (C3) | taken by Claude under standing approval, 2026-11-01; queued with the C3 chaining work | `REPORT-IMPACT-20261101.md` |

| The cost semantics' `fix` stage passes a raw record as `super` (Demand lane's option (a)), not elaborator flattening: the Leaf lane's `flatten_sound` already proves flattening is `≈b`-sound, so the cost of a layered object can be stated through its flattening without changing the elaborator or the semantics; the Demand lane generalizes `Sim`'s settled-substitution rule where needed. Layered objects get derivations through `flatten`; option (b) is refused because the elaborator's output is what Logic and Leaf prove about. | taken by Claude under standing approval, 2026-11-01 | `REPORT-DEMAND-20261101.md`, `REPORT-LEAF-20261101.md` |

| Posting identity across machines is a digest of the posting's content plus the history it was made on, numbered by the receiving register (Ledger lane's option A): the same invoice posted identically on the same history by two machines is one posting, merging twice is harmless; a different history is a conflict | taken by Claude under standing approval, 2026-11-01 | `REPORT-LEDGER-20261101.md` |

| A kind's identity is its declaring module plus name; a declaration may carry its own stable identity (`record Mile as "units/mile"`) that survives a move, with the module path only the default (C1 lane's question). Taken as yes: an identity that dies when a file is renamed is the wrong identity for a thing with instances in other people's vaults; the explicit name is an intention like a package parent. Deferred to the next C1 pass. | taken by Claude under standing approval, 2026-11-01 | `REPORT-C1-20261101.md` |

| A split binds every field at a quantity the whole record allows (coarse); the per-field `FieldsTyping.cons` guard refused (rejects `{held = h}` at `linear Nat`; sound only under semantic shareability); direction: per-field graded record types (`Σ⊗`), next C2 pass, outside read before promotion | taken by Claude under standing approval, 2026-11-01 | `REPORT-C2-20261101.md` |

| Recursive Lean definitions lower from their unfolding equation to a simply typed `fix` (recursive-δ in the source semantics), not by giving Core4 a type for the `Nat.below` tower | taken by Claude under standing approval, 2026-11-01 | `REPORT-LOWER-20261101.md` |
| Lean4Lean is not a dependency yet: its theory has 9 `sorry`s and no inductive types at HEAD, and its kernel port does not build at 4.35; the connection theorem is stated as a rule table until upstream has ι | finding, 2026-11-01 | `REPORT-LOWER-20261101.md` |

## Still open

| item | where it is written | size |
|---|---|---|
| `@[expose]`-all per definitional module is a migration expedient (Kimi §3) | `REPORT-20261030.md` §2 | a tightening pass, measured by the one-edit rebuild check |
| Rename `slot_repair` (a bundle of reading and permanence lemmas) and `Integrity.transition` | Kimi §1; runner report §9 | names only |
| Journal baseline `env-b3ddd73.jsonl` (8.9 MB) is committed; ignore or keep | lane B D6 | one `.gitignore` line |
| Runner: decision authority beyond the `.me` chooser; per-slot selection descriptor; versioned candidate domain; richer "nothing admissible" diagnostics; leases and hysteresis | `REPORT-RUNNER-20261031.md` §8–9; Astra selection §8 | a lane |
| Runner adapter: reference-tree statement, depth deepening, ticks, response typing, plan authority through Law, holes in emitted plans | `REPORT-RUNNER-20261031.md` §10 | a lane |
| Elab: open-template check still `Check.check`; `#tooth` on `prepare_checks` fails on a compiler-generated dependency; seed-with-extra-members not wired | `REPORT-ELAB-20261031.md` | small each |
| Law: machine-to-`Admits` connection; `c3_tree_is_chain`; `keeps` typing | `REPORT-LAW-20261030.md` | medium |
| The template elaborator by Simple-sub with emitted coercions | `review/ALGEBRAIC-SUBTYPING-20261031.md` §3–4; `METATHEORY.md` §5.5 | a lane, next after Extends |
| `≈b` via Iris-Lean; Leaf emitter and refinement against `bendtt.lean` | `METATHEORY.md` §2, §5.6 | two lanes |
| minidregg, nanodregg, delvetalk `require obend` and delete their twins | `SHIP.md` §3 | a lane per tree; the reason the library exists |
| Carry between package versions | `SHIP.md` §4.6 | a lane |
| Papers never fetched: Moran–Sands 1999, Brandt–Henglein 1998, Leijen 2005, Ducournau 1994, Cardelli 1986, Birgisson 2014 | `review/PRIOR-ART-20261030.md` | Anna's key |
| `respectTransparency` debt from the 4.35 bump | `REPORT-LEAN435-20261031.md` | in the ProofEng lane now |

## In flight

ProofEng (speed, restructuring, waterfall); Extends (cross-package `extends`, intentions as slots,
laws across packages, orthogonal protocols); Vault (`obend open`).

## Plan for the open items (2026-10-31, launched)

| item | lane | brief |
|---|---|---|
| World non-return law; renames; runner authority and descriptor; adapter gaps | SlotRun (opus) | `lean/docs/LANE-SLOTRUN-BRIEF-20261031.md` |
| machine-to-`Admits`; `c3_tree_is_chain`; `keeps` typing; laws reach the runner | LawFinish (opus) | `lean/docs/LANE-LAWFINISH-BRIEF-20261031.md` |
| the trees consuming `obend` | Adoption study (opus, read-only) | `review/ADOPTION-BRIEF-20261031.md` |
| `≈b`, `mix_assoc`, Iris-Lean usability | Equiv study and spike (opus) | `review/EQUIV-BRIEF-20261031.md` |
| the six unfetched papers | Papers (sonnet) | `review/PAPERS-BRIEF-20261031.md` |
| expose-all tightening | after ProofEng lands (same files) | queued |
| Elab leftovers; Simple-sub template elaborator; carry | after Extends lands (Spec files) | queued |
| Leaf emitter and refinement | after the Equiv spike and the runner adapter | queued |


## Decision record, restructured (2026-11-01, after `astra/ASTRA-DECISIONS-20261101.md` §1 and §6)

Each decision from here carries: id; decider and authority (Ember / integrator under standing
approval / lane); the semantic contract it fixes; status (proposed, taken, built, promoted to a
relied-on boundary); first consumers; evidence; residual obligations; reversal and migration cost.
A lane may complete its deliverable while the workstream's gate stays open; when evidence refutes
a gate, the integrator replaces it with a true one and names the remaining obligation. The PLAN rows
now carry "deliverable" and "gate" separately.

The four contracts that are the real pending decisions (replacing the four lane epilogues):

| id | contract | recommendation | owner; evidence before promotion |
|---|---|---|---|
| C1 | Identity across kinds, checked code and upgrades (Gemini: `encodingVersion` hashes only the syntax schema, not `Ty`, quantities, assumptions or the checker edition, and only tag representatives at that (Kimi A); `Code` via `Checked` versus `importWith` via `checkAgainst` forces `import_complete` to re-synthesize; mirrors are forgeable `Data` records; two kind systems, `Kind` and `Vault/Law.kindChain`, and kind pins do not cover ancestor versions (Kimi A)) | nominal kind identity survives every boundary (quotation, import, higher-order crossings, upgrades); stable kind identity distinct from the pinned version of its layout, law and methods; layout/law versions and the typing edition explicit in a portable checked-code artifact; compatibility and migration are judgments, never assumed; anonymous structural records kept as a separate facility | integrator with Kind, Quote and Elab; Ember for what a user means by identity across upgrades; outside read of the equality/import boundary before promotion |
| C2 | Ownership across aggregates and staging (Gemini: four eliminator holes, in the Sound lane; records are `⊗`-constructed with neither `⊗` nor `&` elimination, so a pattern-matching destructor or an all-siblings-shareable `get` is the positive counterpart; a linear conservation theorem over `Step` is the missing soundness statement) | keep exact-use at binders, branch agreement and transfer restrictions, stated as exactly that (no eventual-fulfilment theorem); add a consuming decomposition that accounts for every resourceful component as the positive counterpart to the projection refusal; a stated contract for dropping, transferring, splitting and returning aggregates and what a terminal machine state owes; syntactic ownership never used to prove the runner's durable spend tokens by vocabulary | typing and resource lane with outside review; Ember only if meaning or ergonomics change materially; required before T7 is advertised as preventing laundering |
| C3 | Receipt meaning and authoritative history (Gemini: `capOpening` fails open, `recheck` never enforces read coverage, `R.trust` unchecked, `.cited` trusts the bit, all in the Sound lane; `Collides` conflates ABA content return with hash collision unless `pinOf` commits to the version; `Kept` is not a state invariant because `Rest` drops abandoned obligations; `exposed_once` is at-least-once with idempotency keys; Kimi B: `recheck` does not tie the receipt to its row, one Merkle tree should serve all openings) | re-execution proves legality relative to the receipt's inputs; commitments prove binding; membership in an authoritative history is a separate claim relative to an independently selected head under a stated host model; the verifier produces the conclusion it established (allowed quantifier, execution basis, remaining premises) rather than trusting producer metadata; projection invariance of the dial is not proof-strength invariance; non-omission needs a coverage argument | runner and receipt integrator; independent boundary read; Ember chooses deployment and trust commitments, not the hash-tree plumbing; Astra's two probes (clock-shifted receipt verifies; quantifier label trusted) are the countermodels |
| C4 | Runtime cost and optimization claims (**decided 2026-11-01 on Gemini Experiment 2 and Xia et al. ICFP 2024**: the two-stage demand semantics, settle the template once with `self` free then iterate field waves on approximation types, extended to knots; no heap, no cell table; Gemini: the Hackett–Hutton obstruction is a `fixLet` staging artifact, repairable by iterated approximants from `skipped` with no heap, which flips the recommendation from a cell table to fixing the staging; `CostWithin` is a symmetric `8ⁿ` factor, not improvement, and a parallel `Sim` per step makes it a flat 8; `Judge.deepen` is quadratic where `runBounded_mono` would make the law judge linear) | adequate need-based cost first; the clairvoyant cell table if it buys a simpler proof, not as a commitment; directional improvement kept distinct from factor equivalence; no public optimization guarantee before an outside semantic read of the recursive-demand cases | Cost lane; outside semantic review before any charging consumer depends on it |

Engineering tasks kept visible with owners, not decisions: the Leaf toolchain arrangement (one
emitted program through the intended refinement route; no silent maintained fork); the expose and
build gates (clean build under two minutes, `Check` edit within twenty modules) still open.

## Record note (2026-11-04)

Commit `8f8c022` (2026-11-01 02:57, "checkpoint") deleted this file and 141 others (every lane report
under `lean/docs/`, every study under `review/` and `astra/`, `paper/objective-bend.md`). It was restored
from `8f8c022^` on 2026-11-04 and the decisions since are appended below. `review/` was in `.gitignore`
until 2026-11-04; it no longer is. The file `review/DECISIONS-LEDGER.md` written by a Gemini lane on
2026-11-03 describes a Core4 with constructors `stamp`, `letIn`, `handle` and a type `Ty.nominal` that
`lean/Obend/Core/Term.lean` and `Ty.lean` do not have; it is not a source of truth for anything in §1–§2.

## Decided by Ember, 2026-11-02 (to Gemini, Antigravity history)

| decision | choice | where |
|---|---|---|
| `native_decide` and compiled trust are not a concern now; string/JSON proofs are the wrong shape but not a priority; a trustworthiness pass comes much later | yes (11-02 09:25) | `~/.gemini/antigravity-cli/history.jsonl` |
| Wave 4 (`QUALIFICATION-AND-SILICON-LEAN.md`) approved; no `flash` sub-agents | yes (11-02 13:37) | same |

## Decided by Ember, 2026-11-04 (answers to the expert panel, `review/EXPERT-*-20261103.md`)

| decision | choice | where |
|---|---|---|
| The hardware tier aims at a bitstream soon (F2 or iCE40); widths, the F2 shell ports and DFX are the critical path; PDK and tapeout modules are documentation until then | yes | `EXPERT-fpga-silicon` |
| Headline counts (theorems, constants, `0 sorryAx`) are a ritual and harmful; stop printing them; stop writing concrete `decide` fixtures as `theorem`s; existing fixtures leave the theorem count (as `example` or tier 2) | yes | `EXPERT-lean-proof-engineering` |
| Bend is not "the leaf"; the phrase is retired; Bend compatibility is no longer a goal ("what is it doing for us"); the BendTT and C emitters and the interaction-net vocabulary go unless something consumes them | yes | `EXPERT-compiler-runtime` |
| `obend-node` is an in-process simulator of the Lean theorems; it may become a validator later, but the validator is redone at the minidregg/dregg integration, so no investment in hand-rolled crypto now; the Bridge self-admission paths are removed regardless | yes | `EXPERT-distributed-security` |
| Physics: the LC Drives current loop is the one device that gets the honest low-level-model-to-valid-approximation treatment first (ODE → ZOH → PI → RTL with `R`, `L`, `T_s` as variables) | yes | `EXPERT-physics-numerics` |
| The project frame is research into the consequences of its design decisions; the user frame (the Oct 29 gardener, the README's user) is a lens taken sometimes, never the overriding one; the root documents say so | yes | `EXPERT-language-user` |

Open after these: which of Gemini's eight S-lanes (handoff `review/GEMINI-HANDOFF-20261103.md`) resume
at all now that Bend is retired; whether "Core4 does not grow" holds for the eight bit-level
primitives; which file is the single `#import_obend`.
