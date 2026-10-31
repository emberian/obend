# Report: the whole-library axiom census, and the missing pins

Brief: `docs/LANE-CENSUS-BRIEF-20261031.md`. Lean v4.35.0.

## Totals

`Obend/Census.lean`, built by `lake build` (it is in the `Obend` glob), reports on `a87ec35` + this commit:

    #assert_axioms_tree: 25028 package constants; 27 rest on the compiler trust (native_decide);
    0 are computed_fields overrides (lcProof, compiled code only); none on sorryAx or a declared axiom

The 27 compiled theorems, each already pinned by `#assert_compiled` in its module:

| Module | Theorems |
| --- | --- |
| `Core/Proofs/DigestChecks` | 4: `digest_one_one`, `sealed_known_answer`, `sealed_lowBit_not_vote`, `sealed_yes_no_differ` |
| `Spec/Proofs/C4Vectors` | 5: `pommette_vectors`, `pommette_refusals`, `fuel_is_not_inconsistency`, `dag_local_orders`, `ordered_presentation_invariance_4000` |
| `Spec/Proofs/FrontEndAdequacy` | 1: `accept_inhabited` |
| `Spec/Proofs/Law` | 3: `parse_tally`, `parse_precedence`, `parse_refuses_nested` |
| `Spec/Proofs/SpecificationClosure` | 14 (`twice_accepted`, `claim_spec_accepted`, … the accepted/refused vectors) |

No constant rests on anything outside `propext`, `Classical.choice`, `Quot.sound` and those 27
theorems' own `_native` axioms. There was nothing to fix.

## The census is not a `module`

The brief asked for a `module` importing the library. Two measurements on `ec15a09` made it a plain file:

- A `module` may import only modules; 11 files under `Obend/` are legacy non-module leaves
  (`Core/Teeth/*`, `Core/Proofs/DataBudget`, `Law/Proofs/TypingTeeth`, `Run/Core4Example`,
  `Spec/Proofs/{LawCompileTeeth,TermWire}`). A module census sees 24684 constants; the plain file
  sees 25026, those leaves' 342 included.
- Under a plain `module` import a theorem whose body is not exposed arrives as an axiom. The
  census over plain imports refused 5661 constants that way (each "resting on" itself).
  `import all` fixes that, not the first point. A non-module importer gets every module's
  private part.

Two probes, both removed after: a module declaring `private axiom stray : 1 = 2` and a private
theorem using it was refused by the plain-file census (both constants named); a new empty module
under `Obend/` not listed in the census's imports was refused by its coverage check
(`census: 1 library modules are not imported here: [Obend.ZTmp]`). That check reads `Obend/` on
disk and runs when the census rebuilds, i.e. when anything it imports changes; a new leaf added
alone is caught at the next such rebuild.

The census covers the `Obend` library, not the `Journal` tool library.

## Pins added

`#assert_axioms` naming every theorem in the file, before its closing `end`, and
`public import Obend.AxiomPin`:

| File | Theorems pinned |
| --- | --- |
| `Core/Proofs/Force.lean` | 19 |
| `Core/Proofs/Settle.lean` | 39 |
| `Core/Proofs/Forcing/Run.lean` | 19 |
| `Core/Proofs/Preservation/Cases/Activities.lean` | 11 |
| `Core/Proofs/Preservation/Cases/Arithmetic.lean` | 9 |
| `Core/Proofs/Preservation/Cases/Functions.lean` | 13 |
| `Core/Proofs/Preservation/Cases/Pairs.lean` | 7 |
| `Core/Proofs/Preservation/Cases/Records.lean` | 14 |
| `Core/Proofs/Preservation/Cases/Sums.lean` | 11 |
| `Slot/Proofs/Protocol.lean` | 56 (including the `Coin` namespace) |
| `Slot/Proofs/Negotiation.lean` | 21 |

`Spec/Proofs/{Law,C4Vectors}.lean` were already fully pinned: every theorem there is a
`native_decide` fact with its `#assert_compiled` line, which `#assert_axioms` would refuse.
They are unchanged. `Obend.Core.Collect.agree_runBounded`, which the paper's axioms paragraph names
as unpinned at `e5fca29`, is now pinned in `Settle.lean`.

README's pins paragraph now names the census. The `AssertAxioms.lean` docstring named a root
module `AxiomCensus` that never existed and said the file lives in `Theory/` and imports
Mathlib; both are corrected.
