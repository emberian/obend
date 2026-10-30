# Astra implementation report — meaning, extension, and mutation

The semantic substitution law is fuel-free; the slot spends an explicit grade to obtain evidence of it. Generic traversal laws now serve the existing metatheory. The `hole-exercise` branch extends syntax, execution, checkpoints, and the proofs, and was merged only after its whole library built with the existing pins. Custom tactics are used by the library itself.

This report concerns Astra's changes, not the interleaved Spec, Law, paper, review, or journal-fix commits. Those lanes retained their files. The exercise used an isolated worktree inside this repository, preserving the live `dev` checkout.

## Landed commits and validation

| Commit | Change |
|---|---|
| `8bf6b08` | Meaning/procedure/budget split, semantic substitution, checker-completeness obstructions, graded lifting, budgeted slots |
| `3fdab06` | Generic binder-aware traversal and adoption by scoping, substitution, and Core slot free-variable tests |
| `26231a7` | `obend_cases` and existing preservation proof adoption |
| `d8db9f8` | Green `hole-exercise`: explicit payload syntax, demanded-hole refusal, codec, proof repairs and teeth |
| `fa669fe` | Merge of the green exercise into `dev` alongside the concurrent lanes |
| `7a3a45c` | Stored-proof mutation command, persistent negative checks, real consumer teeth, and budget-refusal diagnostic |

Validation used serialized Lake builds and focused standalone Lean checks during repairs. The isolated exercise passed `LEAN_NUM_THREADS=2 lake build`; the integrated tree's final result is recorded below. Existing axiom and compiled pins remain. No theorem statement was weakened to accommodate the hole, and no placeholder or axiom was added. The stronger checker-completeness request was refuted explicitly, as the resumed brief authorized, rather than asserted.

The integrated `dev` library also passed `LEAN_NUM_THREADS=2 lake build`, including the persistent mutation-command guards and every existing pin. Subsequent report-only edits do not change that Lean result.

## Module graph and actual consumers

`Core.Graded` supplies a nonnegative ordered additive commutative monoid. `Tactic.Fuel` imports it; `Slot.Calculus` imports it and the generic slot. `Slot.Core4` now imports semantic `Proofs.TypedSubstitution` and the completeness obstruction module, and instantiates a fuel-free `Calculus` separately from `Decides Nat`. `Slot.Budget` connects that instance to the toy World and Integrity; the public root exports the grade and budget modules.

`Core.Traverse` defines a binder-aware tree and a single rebuilding traversal. Renaming, substitution, variable occurrence, and scoping are derived over that shape. `Core.TermTraverse` is the syntax boundary: tags preserve constructor payloads and labeled-list order, and encode/decode establish the bridge to `Term`. `Core.Invariant` and `Core.Proofs.Adequacy` use generic laws through that bridge; `Slot.Core4.freeIn` uses the generic occurrence test. The old executable rename/substitute equations remain compatible, but their composition and scoping consumers no longer repeat the constructor inductions.

`Tactic.Cases` is a macro module importing Lean. Its definitions respect the module visibility discipline; failed finishing tactics leave real goals, and invalid simp inputs remain errors. Preservation/Base uses it in existing proofs. The exercise uses it in the syntax bridges, checker transport, checkpoint proofs, StepCases, preservation, adequacy, completeness, collection and forcing repairs. `Proofs.Hole` supplies the new execution/checker/traversal teeth.

`Tactic.Tooth` imports Lean for command elaboration and kernel replay. `Slot`, `Slot.Integrity`, and `Core.Proofs.Substitution` import it for local mutation commands; `Tactic.ToothChecks` checks the command's error behavior. This does add the tactic import to foundational Slot consumers. The replay scratch environment is discarded after each command.

## Meaning, procedure, and budget

`Calculus.Typed` in the Core instance means existence of a `Checked` derivation with the stated type. `checked_msubst` transports the underlying mutually inductive typing derivations and usage bounds. `calculus_typed_msubst` is the instance's substitution theorem, independent of a checker budget. Existing procedural transport theorems remain available; their grade lifting uses `fuel_lift` through `Graded.lift` instead of local arithmetic proofs.

The inherited obstruction was real. Semantic typing can use evidence the current checker never reconstructs: absent annotations are not the only obstruction; conversions, empty elimination, and duplicate-label behavior supply further pinned examples. `Decides.check_complete` therefore has an explicit `Covered` premise. The Core instance calls its predicate `Recognized`, an eventual-success witness. It does not pretend that this is an independently characterized decidable fragment.

`slotOf` takes a declared `Budget`; `slotOf_usable`, `resolve_checks`, and Integrity's `slotFiller_typed` conclude semantic typing. `Calculus.admit` returns the named `uncovered` refusal. `slotFiller_uncovered` connects an actual resolver failure, for a named candidate whose ordinary supports are live, to that admission refusal. The toy World supplies the budget as a function of its view. `budget_tooth` is a decidable usable-at-combined-budget/refused-at-short-budget example, and the old `fuel_tooth` remains a procedural budget tooth.

The generic Slot still records a failed judge through its existing refusal API. `uncovered` means that this invocation did not establish coverage; it does not falsely diagnose every failure as repairable by more fuel.

## The extension exercise and the journal

The before export was taken at `26231a7` before changing syntax. The after export was taken from the completed exercise tree subsequently committed as `d8db9f8`. Both snapshots are local scratch artifacts under `astra/impl`. The final comparison uses the corrected journal from `7bf1bbe`: the concurrent review found that the old closure could omit reachable supports. Export data are unchanged by that algorithm repair; the corrected diff is the result used here.

[The exact names and classifications](HOLE-REPAIR-SET-20261030.md) are the journal's repair reading, stated there once, together with the separate list of declarations actually repaired. A dependency warning is an obligation to re-check, not a claim that a proof failed. Generated declarations and broad dependents are retained in the journal inventory; source-edited proof names are distinguished from them.

The new `Term.hole n σ` is inert unresolved syntax. Its identifier is not a bound index. Renaming, substitution, and scoping traverse its explicit payload at the current lexical depth. Demanding it produces `unresolvedHole`; lazy code may ignore it. No typing or evaluation rule grants a value to an unresolved hole. Checkpoints preserve arbitrary payloads and trailing input; old wire tags and refusal names retain their meanings. The public Spec and Packet languages were not extended.

What the shape saved: generic renaming composition, substitution interchange, identity and congruence proofs did not change. Semantic typing substitution did not change. Their syntax boundary equations and scoping bridge did need the new list-shaped arm. What it did not save: runtime dispatch, checker rejection, checkpoint encoding, machine/source correspondence, finite completion, collection, forcing, and typed-source exclusion still require domain decisions. Adequacy needed a genuine contradiction from a terminating source derivation, supplied by `sourceDerivation_hole_false`; preservation needed `source_not_hole`.

## Tactics in use

`obend_cases h with [lemmas]` and its induction form split, simplify, then try `grind`/`omega`. The following are proof-body physical line counts, excluding statements and the opening `:= by`; this is the sole proof-size comparison in this report.

| Theorem | Before | After |
|---|---:|---:|
| `heap_type_pure` | 2 | 2 |
| `lookup_not_computation` | 1 | 1 |
| `isRow_not_computation` | 1 | 1 |
| `callable_arrow_not_computation` | 1 | 1 |
| `typed_control_not_refused` | 1 | 1 |
| `safe_quantity_add_left` | 1 | 1 |
| `canonical_is_variable` | 2 | 2 |
| `canonical_tail` | 4 | 1 |
| `canonical_type_head` | 2 | 2 |
| `natural_value_form` | 7 | 5 |
| `boolean_value_form` | 7 | 5 |
| `label_value_form` | 7 | 5 |
| `specification_value_form` | 7 | 5 |
| `prototype_value_form` | 7 | 5 |
| `typed_source_focus_preserved` | 16 | 13 |
| `record_value_form` | 8 | 6 |
| `variant_value_form` | 7 | 5 |

`fuel_lift` is used in `Slot.Core4.calculus_check_msubst` and `calculus_check_msubst_within`. It accepts the monotonicity lemma and derives common-grade bounds from the grade laws, with concrete arithmetic only as a fallback.

`#tooth T by mutation definition := replacement` replays the stored proof dependency closure in a fresh environment. It first checks the original renamed closure, checks replacement and declaration types, then requires a kernel proof failure under the mutation. Invalid definition reconstruction, unsupported declaration kinds, malformed replacements, and resource failures are errors, not teeth. An unchanged mutation must error because the proof still succeeds. Persistent checks also verify transitive proof dependencies and restoration of the original environment.

Commands sit beside `fuel_tooth`, `open_filling_tooth`, `assumptions_tooth`, `toy_repair`, the Integrity floor counterexamples, and `slot_repair`. The substitution teeth mutate fixtures and reject their computation proofs; the original corner statements remain. The slot mutation rejects a helper used by the repair theorem. The Integrity mutations either erase the contract or replace a deliberately bad filler with the correct one.

The claim is stored-proof sensitivity, not that the mutated proposition is unprovable. The printed failure may be in a helper in the named theorem's closure. Affected inductive groups, recursive dependency cycles, unsafe definitions, and unavailable same-or-later-module bodies are conservatively refused. Earlier-module hidden bodies cannot depend on a later mutation by import ordering; that is why they can be reused.

## Inheritance, workers, and corrections

I inherited and retained the stopped run's Graded, traversal, fuel tactic, semantic substitution, completeness-obstruction, Cases, and preservation work. I read the worker code and built the integrations rather than accepting the old handoff. The inherited obstruction changed the design. I replaced the old fixed-fuel account of semantic substitution and the downstream handwritten structural inductions; I did not discard the useful inherited implementations wholesale.

Native Sol workers had written, disjoint file briefs carrying the supplied rules, and committed nothing. The traversal worker completed shape laws and the Term boundary, then the hole payload/scoping bridge. The typing worker completed semantic substitution and checked its obstruction, then repaired checker transport and Templates, and finally completeness. The cases worker repaired and exercised the macro, adopted it in preservation, then handled machine/StepCases/preservation and forcing. The tooth worker implemented and adversarially checked the scratch replay command, then handled checkpoint payload roundtrips and the persistent rejection tests. I designed and integrated the graded calculus/slot split, the budget examples and diagnostic, reviewed their Lean, repaired collection and adequacy, serialized builds, ran the journal, and committed the result.

Corrections mattered. Semantic substitution needed a reserved-name/list-lemma repair. Canonical-form proofs needed observer simplification in the right order. The shape bridge needed direct-list membership size arguments distinct from labeled pairs; scoping needed late product normalization. A broad `grind` rewrite of MachineFast introduced `Classical.choice` into a proof with a stricter exact axiom expectation; we restored its constructive branches and confined the tactic to the new arm. No pin was widened. The mutation guard originally depended on which member of an affected inductive group was visited first; it now checks the stable rejection class. A transient missing build artifact on the shared checkout required a retry after checking that no other build remained; no cache was removed.

Several hole repairs use a mechanically unnecessary payload/index split to invoke the requested tactic while retaining an existing proof's context and exact trust bound. This is sound but weaker adoption than `StepCases.apply` and forcing's actual syntax dispatch. It is recorded as a limitation, not presented as automation of semantic design.

## Decisions, critiques, and meta-critiques

| Decision | Critique | Meta-critique |
|---|---|---|
| Keep semantic typing stronger than checker recognition; make completeness conditional | `Recognized` packages eventual success and does not explain the recognized fragment independently | The stronger claim is false; honest separation preserves the useful semantic law and leaves a precise checker-design problem |
| Prove substitution for the Core instance instead of adding a generic field with underspecified premises | Another calculus must supply its own theorem | The brief permits the instance theorem, and its closure, assumptions and usage premises are concrete rather than silently generalized |
| Use a nonnegative grade monoid | This excludes resource orders without a least zero | Joint-budget lifting needs each component bounded by the sum; the restriction is explicit and fits current fuel |
| Retain executable Term equations behind the generic bridge | Syntax extension still repairs encoding equations | Existing computation and simplification remain stable while real downstream laws share their proofs |
| Add named admission and a resolver diagnostic without replacing generic Slot refusals | Consumers still call a separate diagnostic to obtain `uncovered` | Existing refusal meanings survive, and the actual resolver is connected to the name by a theorem |
| Supply the toy grant from its World view | Budget is not yet a first-class World fact whose retirement is audited | This implements declared invocation coverage without claiming a protocol for resource issuance |
| Treat holes as inert syntax and refuse on demand | This is not a contextual-metavariable solver or a new surface feature | It is a real constructor extension with preserved laziness and a complete metatheory repair exercise |
| Extend checkpoint encoding rather than reject holes at serialization | The wire language grows | The existing arbitrary-Term roundtrip contract requires preserving the new constructor |
| Land Cases before the hole exercise | This differs from the brief's outer numbered ordering | The exercise explicitly requires using the tactic during its repairs |
| Use std Lean macros and opportunistic finishing | `simp_all` can alter more context than a manual proof, and some repairs remain mechanical | Invalid inputs remain errors, unresolved arms stay visible, and exact axiom pins constrain adoption |
| Replay stored proof closures for mutation | Failure of a particular proof is weaker than falsity of its proposition | This is the requested proof-failure experiment; original counterexample statements supply their separate semantic claim |
| Reject unsupported mutation reconstruction | Some useful mutations cannot yet be expressed | False evidence from stale inductive groups or invalid definitions would be worse than an explicit limitation |
| Put tooth commands beside foundational theorems | Lean meta imports propagate through consumers | The requested checks are exercised by ordinary library builds, not left in an unused tooling leaf |
| Isolate the branch exercise in a repository-local worktree | It requires a separate warm build tree | Concurrent lane files are never switched, reset, or stashed |
| Use the corrected journal for both saved exports | Its result is produced after the exercise rather than by the original executable | The old closure had a demonstrated omission; preserved exports allow a valid comparison without rerunning unrelated source changes |

## Not done, and the decision for Ember

I did not claim total checker completeness, implement contextual-hole solving, add hole surface syntax, instantiate a production World, import Iris, change toolchains, or modify the concurrent lanes. Those are separate semantic or integration tasks, not missing proof repairs for this extension. The generic shape does not eliminate the Term bridge or derive machine semantics. Mutation replay does not reconstruct affected inductive groups.

The decision for Ember is whether the next checker lane should align the procedure with declarative typing or deliberately document a smaller independently characterized checking fragment. I recommend a bidirectional, explicitly characterized coverage design first, keeping fuel-free typing as the semantic contract. Merely adding fuel cannot repair the proved obstructions.
