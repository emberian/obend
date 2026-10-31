# Report: the judgment class and the receipt type (lane Judge, Claude Opus, 2026-10-31)

Brief: `lean/docs/LANE-JUDGE-BRIEF-20261031.md`. Full build green at 251 jobs (start: 241, warm replay);
`#assert_axioms_tree`: 31184 package constants, none on `sorryAx` or a declared axiom, 27 on the
compiler trust as before (this lane adds no `native_decide`). Receipts end to end:
`python3 tests/run-receipts.py` from `lean/`, 17/17.

## What landed

**`Obend/Judge/Class.lean`.** `class Judge (Obj Cert R) [Graded R]` with `Clause`, `Meaning`,
deterministic `check : R → Obj → Cert → Verdict Clause`, and the laws as fields: `sound` (ok ⇒ the
meaning), `refuted` (a refusal by a clause the judge marks refuting means no certificate could mean
the claim: refuted, not unproved), `complete` on a stated `Fragment`, `mono` (a verdict that is not
`uncovered` is kept at every larger grade). `Verdict = ok | refused Clause Path | uncovered`.
`Judge.deepen` makes any procedure that is sound at every grade monotone (it runs grades 0…k and keeps
the first answer). `Regime = decidable | semidecidable | attestable`, `TrustBase = kernel | compiled |
external who`. `Format`: name, version, decoders, judge, trust base, regime, a planted bad
certificate with `bad_refused` at its grade; `checkBytes_sound` (an acceptance of bytes is an
acceptance of the statement they decode to, and its meaning holds of exactly it), `refused_above`,
`not_trivial`, and `trivial_unregistrable` (a check that accepts everything has no refused planted
certificate). `Translation` with `encode_sound`, composed by `Translation.sound`.

**`Obend/Judge/Instances.lean`.** The existing judges as instances, their theorems as the fields:

| judge | certificate | `sound` | `complete`, on |
|---|---|---|---|
| any `Decides` (`ofDecides`) | the prepared term | `check_sound` | `check_complete`, `Typed ∧ Covered` |
| bidirectional checker | annotations | `checkAgainst_sound`, `reannotates_typed` | `full_annotated`, every typed term |
| law machine probe (`lawProbe`) | none | `judge_sound`; refusal refutes by `refusesAs_not_admits` | `judge_complete` + `judged_unique`, closed laws |
| `coerce` (`coercion`) | the emitted coercion | `checkAgainst_sound` | `coerce_checks`, where the emitter succeeds |
| C4 (`c4`) | none | `precedence_ok` | `precedence_tree`, acyclic trees |
| protocol envelope (`envelope E`) | none | `checkProt_sound` | `checkProt_complete`, every derivation |

The law probe is deepened along a resource ladder, so no fuel monotonicity of the machine was needed.
The protocol envelope had no executable checker: `checkProt` is new (on finite signatures, with the
result predicate and hole posts presented as Booleans in an `Envelope`), sound and complete against
the existing `HasProt`, so its refusal is a refutation. Exercised on the negotiation's template
(`template_enveloped`; without the capability `template_refused` and `template_untyped`).

**The foreign format: LRAT** (`Obend/Judge/Lrat.lean`). DIMACS CNFs, LRAT steps (RUP additions,
deletions), a checker over an association list of held clauses (the kernel and compiled code run the
same function), `propagate_sound`, `run_sound`, `check_sound` (accepted ⇒ `Unsat`). Certificates are
refutations or models; a model satisfying the formula is refused by `satisfiable`, which refutes
(`check_refuted`); RAT hints are refused as unsupported. Completeness is claimed only on formulas with
complementary unit clauses (`complementary_accepted`); completeness for every unsatisfiable formula
would be resolution's and is not claimed. Decoders for CaDiCaL's text output; `format` registered
with trust `compiled` and a planted refutation refused by `noConflict`.

**Encoding as a theorem** (`Obend/Judge/Identity.lean`). Conditional identities over bits (`Identity`:
hypothesis, two lists of expressions, `Holds`); Tseitin `encode` with `tseitin_bounds`,
`tseitin_spec` (the encoding has a model extending any assignment, giving each literal its
expression's value), `encode_sound` (unsatisfiable encoding ⇒ the identity holds), `translation`.
The instance: `noCarry n`, `x &&& y = 0 → x + y = x ||| y` over the ripple-carry adder's bits.

**A real solver, end to end** (`Obend/Judge/Certified.lean`). `encode (noCarry 8)` (231 vars, 683
clauses) refuted by CaDiCaL 3.0.1 (`brew install cadical`; `--lrat --binary=false`); its 215-step
proof is a literal and `steps8_accepted` is the kernel's run of the checker on it (`decide +kernel`,
about 10 s); `noCarry8_holds`. The tooth `dropped_refused`: the same proof with clause 687 deleted
right after it is added is refused `missingHint 687` at step 10, where 688 cites it. The 32-bit
instance (2439 vars, 7679 clauses, 3207 steps) is checked by the compiled checker on its bytes
(`obend lrat`, 0.15 s). Both certificates are under `tests/judge/`.

**`Obend/Receipt.lean`.** `Receipt {pre post row law prev : Digest; pins : List (Cell × Option Pin);
openings; verdict : Outcome; quantifier : Shape; trust : List (support × Trust); dated : Nat}`.
`Outcome` holds the judge verdicts and Astra's `noAdmissible | awaitingChoice | preferenceKept |
candidateRejected | staleEvidence | executionFrozen`. `Trust = checked format version base | attested
principal revision`, per support; `overall` is attested once any support is, and names it.
`issue` (a row of any `Fold.Admission`); `receipt_sufficient` (`Fold.receipt_sufficient` over the
receipt: verdict and post root at every world agreeing with the openings); `recheck`,
`recheck_sound`, `recheck_issued`; `openings_of_pins` (`rfl`) and `pins_sufficient`; `chained` and
`chain_binds` (under a binding digest a verified chain is fixed by its head and length); the dial
`full | cited | bit` with `dial_invariant` (the follower replaying, the stranger reading openings and
the holder of one bit agree).

**`holdsOfPin`** (`Slot/World.lean`). `holdsOfPin : Cell → Option Pin → Fact → Bool` is now the field
and `holdsAt` is defined from it, so `holds_pin` is `rfl` and `holds_congr` is a congruence. Restated,
none lost: the former fields `holds_congr` and `retired_dead` are theorems with the same statements
and names (`World.holds_congr`, `World.retired_dead`), from the new field `dead_none`. The four
instances (`toyWorld`, `pinWorld`, the negotiation's, `Returning`) give `holdsOfPin`; three proofs in
`Repair.lean` add `holdsOfPin, pin, cell` to their simp sets.

**Both exercised** (`Obend/Receipt/Negotiation.lean`, `Export.lean`, `Cli.lean`). The negotiation's
admitted dispatch of the commitment to `p2` (row 4 of the accepted log, under `legalAdmission`):
`row4_admitted`, `receipt4`, `realize` (a view built from pins), `realize_reads`, `row4_recheck`.
Canonical JSON for rows and the accumulator's rest (protocol trees unfolded over the listed
responses, so the root binds the plan in force), cSHAKE256 digests. `script_outcomes` maps the
session's refusals: the commit on `p1` is refused by its clause, the six events after the commitment
went in flight or was abandoned are `executionFrozen`. The identity receipt carries the statement,
the CNF digest and the certificate; `verifyIdentityCore_sound` (an accepted identity receipt's
statement holds). The CLI:

    obend receipt cnf 32 nc32.cnf; cadical -q --lrat --binary=false nc32.cnf nc32.lrat
    obend receipt identity 32 nc32.lrat identity.json
    obend receipt negotiation negotiation.json [--full] --prev identity.json
    obend verify negotiation.json --prev identity.json
      world-transition (cited): true at view 4; trust attested by host@clock 1 (support view)
      prev: identity no-carry-add-is-or-32: holds (lrat@1, 3207 steps, trust compiled)
      chain: linked

The consumer holds no producer state. It re-encodes the statement and re-runs the checker. It
decodes the rest and the row and checks their digests. It computes each world opening from its pin
by `holdsOfPin`, builds the view from the pins and runs `recheck`. `tests/run-receipts.py` checks
these refusals:

- a deleted needed clause;
- an opening its pin does not read;
- flipped pins, which recompute another verdict;
- a tampered rest (the `pre` root);
- a wrong predecessor;
- a bad embedded certificate;
- a statement changed after the certificate.

## Not done, said plainly

- The registry holds one format. The six native judges are `Judge` instances, not `Format`s: they
  have no byte decoders.
- LRAT completeness is claimed only on the complementary-unit fragment.
- The 32-bit certificate runs on compiled trust. Only the 8-bit one is replayed by the kernel.
- `Binds` is an assumption about the digest, which `binds_or_collides` discharges per pair up to a
  collision. It is not proved of cSHAKE.
- `dated` is a natural number, the log index, not a ledger view.
- The world-transition receipt's view is `attested`, which is the decision below.

## The one decision for Ember

Should the shared ledger's view commit pins? The fold's verdict is checked, but every World-transition
receipt is `attested` as a whole today, because the pins it opens are the host's word. If `dated` were
a ledger root committing every cell's pin (a cSHAKE Merkle map, per view of `Run.Shared`'s commit
ledger), a stranger could check each opening against `dated`. The view support would then become
`checked`, and the `cited` setting of the dial would need no trust in the host. The cost: the shared
World layer would carry a commitment scheme and an opening proof per read. That is the middle rung of
GENERATED §2.4's ladder, and it decides what `dated : View` is.
