# Design: as built, and as planned

Revised 2026-11-01. The earlier design (10-29) and the studies that corrected it are in `review/`;
this file says what the system is now and what each next part is. `AMBITION.md` is the destination;
`METATHEORY.md` is what is proved; `PLAN.md` is the order.

## 1. The seam

Objective Bend is a lazy, non-affine language of specifications whose targets include Bend books.
Where a family is known at elaboration, `fix` emits a book in which `self` and `super` are names;
where a specification is built or inspected at run time, it runs on the call-by-need demand machine.
The specification graph is kept after a book is emitted, so reflection sees the composition that is
running. Each author keeps their claim whole: Taelin's "parallelism competes with laziness" is true
inside a leaf, and leaves are strict and affine; Faré's "lazy makes OO easy" is true of elaboration,
and elaboration is lazy; Faré's linearity (each ancestor counted once) is a theorem about `fix` over
the C4 list, Girard's affinity a theorem about the leaves it emits. Built: the calculus, the machine,
the checker, the front end. Planned: the leaf emitter and its refinement against BendTT's `Eval`, as
one of the two mature instantiations (`§8`).

## 2. Laws, three kinds, one word

A `law` line is one of three things by where it is written: a proposition about leaf definitions
proved once under BendTT; a decidable predicate on one write of one object under the current
request, judged on every write by re-executing a machine probe (`judge_sound`, `judge_complete`);
or a `keeps` claim the kernel refuses to let be false, checked by shape at install. World laws
inherit: a kind's and a parent package's laws are ancestors, the effective law is the conjunction
along the C4 list, a child only narrows (`package_never_widens`), and a refusal names the ancestor
and clause and, where one exists, the request that would pass. Every law says what it does when
added over existing state; an adoption is judged with old state equal to new; a package law changes
only by upgrade. Built. Planned (`review/GENERALIZATION-20261031.md` G5): laws over declared domains,
`law L on plan P` (the yielded tree and its continuation), `world law L for W` (the joint
invariant at the shared commit), `hyperlaw L on P` (a product invariant over admitted traces), and
attestations as supports.

## 3. Slots, worlds, the runner

A slot is a deferred decision: candidates, each justified by supports (facts about cells at
versions) and a judge; a support can be withdrawn by name and the slot repaired under a stated
compatibility condition. A `World` has pins, retirement and a version order with an explicit
collision stance. Stored selection is incumbent-first by default with an authorized chooser's
override, and selection control is mandatory on every runner hole. The runner proves `refines`:
every dispatched operation was admitted at its own view, no token is spent twice, a reply pairs
with the call in flight, nothing in flight is replanned, an abandoned call keeps its obligation. The
shared-World ledger composes any number of runners through an atomic commit and proves
`joint_reachable_ticket_exclusive`: "no two members ever both hold the ticket" is a theorem. Built.
Planned: durable commit and recovery, the ledger as a fold member so projection is the generic
theorem applied, consensus-time as a ledger fact every law reads, and the World fork-and-stitch for
offline work.

## 4. The audited fold, the judge, the receipt, the intention

Every admission is a fold over rows with an accumulator and witnessed pin reads, and a row's
verdict depends only on the pins of what it reads (`Obend/Fold.lean`; `Legal` and the law judge as
instances; `receipt_sufficient`). Built. In progress: the judgment class (`Judge Obj Cert R` with
`sound`, `complete` on a stated fragment, monotone in the grade; a `Format` registration whose
encoding is a theorem, with a planted-bad-certificate tooth; the five existing judges as instances
and one foreign certificate format end to end) and the receipt type (roots, row, law digest, cited
openings, verdict, quantifier shape, per-support trust `checked | attested`, dated by the ledger's
view, prev-hash chained; the disclosure dial as three projections). Planned: one `Intention` module
for every reference across a boundary (package parents, cites, kinds, leaf proofs, attestations),
each a slot whose candidates are pins, with `resolve`, `recite` and `renew` as one repair.

## 5. Cross-package extension

`package NAME extends commons/record@^2, bells@0xHASH`: a hash parent is an extension fixed
forever, a name parent is an intention resolved inside a workspace's ecosystem root; the closure
is one fixed point, a layer per package in C4 order with `(intention, declaration)` identity, so a
diamond applies a parent once; a turn pins every root it resolved and a moved pin is `stale` by
name (`stale_iff_blocked`); package laws inherit across the boundary; a third package attaches a
method to a kind it is not an ancestor of through an orthogonal protocol. Built. Decided: kinds
are nominal (the kind cell: every instance carries its kind's identity, the kind's law is an
ancestor of each instance's law, dispatch is by kind). Planned: the kind cell, the C4 `linearize`
rewritten structurally and proved, the suffix property across packages, carry between versions.

## 6. Documents

Five words a person writes in: page, section (a slot over runs), cite (a support with a byte
commitment), law, kind. Patches with `apply_compose` and `apply_invert`; merge as the pushout with
the universal property proved and conflicts as objects; identity cites for `[[page]]`, byte cites
for embeds and `^id` block references current while the quoted bytes are unchanged; backlinks as
the exact live-cite index. `obend open DIR` keeps a world beside a folder of markdown, writes
behind-marks the reader strips exactly, merges a second copy by the pushout, judges frontmatter and
folder laws on every write, and admits members who may post but not select. Built. Planned: the
notebook as a page whose cells are slots over quoted terms and judged results; forms as view
methods; reports as judged folds with non-omission receipts.

## 7. Quotation, staging, specialization

Decided (`review/QUOTE-ORIENTATION-20261101.md`): `quote : Term → Data` is a function of the kernel on
terms it holds (a slot's candidates, a law's code, a page's cells, a package member), never on a
running value; a program that wants code names it through a mirror of depth `code` and yields.
`Code Ψ A θ` is the checker's typed subtype with the assumptions as theory index and the encoding's
digest as version; `import` decodes, checks scope and type, and refuses an escaped index, a foreign
encoding or a hole by name; `splice` is a turn whose response the machine runs closed, guarded by the
usage-composed contextual substitution. `≈q` is equality of encodings; the ladder `≈q ⊆ ≈r ⊆ ≈b`
with cost as a refinement; `rewrite_sound_below` is "no congruence under box" as a theorem about
contexts with an observer census. No new `Term` constructor, no machine frame; a program-level
quote on values is refused (Taha–Sheard, Kiselyov, Kavvos). Reflection goes through mirrors with
depths; stages are views of the World. Then the specialization slot: an emitted leaf is a candidate whose supports are the
pins it assumed, the machine is the always-usable fallback, deoptimization is the withdrawal of a
support, and an optimization is a candidate justified under `≈c`.

## 8. Two mature instantiations

Both implement the same lazy source language and the same governed document interface; they vary
one thing, the affine execution boundary. I: Objective Bend on its own Lean demand machine (built,
with reflection and `perform` in the term language). II: Objective Bend on ordinary Bend leaves
through the emitter (planned). Both run one report through the same life: independent package
extension, a diamond, a protocol from a third package, evidence withdrawal, an offline conflict, a
law amendment, a schema migration. The comparison is a discussion of where each makes expression,
explanation, implementation and proof simpler, not a benchmark.

## 9. Upstream and the sibling trees

Build our own thing; depend on Bend as a leaf toolchain and BendTT as the leaf checker; never fork.
The sibling trees (minidregg, nanodregg, delvetalk) consuming this library and deleting their twins
is studied in `review/ADOPTION-PLAN-20261031.md` and deferred: we are surpassing what they attained,
not waiting for them to catch up.
