# Ambition

Objective Bend is a research project. It exists to find out what follows from a handful of design
decisions taken together: that a program is an open object other hands extend without forking
(Faré's `fix` over layers that see `self` and `super`); that a law is a line a person can read,
judged at the moment someone tries to change something, inherited along a nominal kind lineage,
and amendable by someone who did not write it; that a deferred decision is a slot whose supports
can be withdrawn, so that staleness is exact and repair touches only what moved; that every answer
is labelled by the regime it was established in (decided, certified and re-checkable, or merely
attested) and carries a receipt a stranger can re-judge; and that the kernel admits by re-execution
and checks certificates it never searched for. The repository is the record of those consequences:
what they let a small calculus do, where they bite one another, and what they turn out to cost.

The project is not organised around a user. Along the way it sometimes takes a user-motivated frame
on purpose: a person keeping notes in a folder of markdown, a firm keeping its books, a stranger
extending a package they have not read, an engineer who wants a pipeline's timing refused by name.
Each of those is a lens held up to the design to see what it does and does not let that person
complete. A lens is kept while it shows something; it is not the overriding frame, and no root
document should read as a product brief for one of them.

## The claim

A term rewriter with a notebook was the twentieth century's symbolic core. What it lacks is not
more rules. It lacks objects many hands build without forking; laws judged at the moment someone
tries to change something; provenance that survives a second author; answers labelled by their
regime; deferred decisions that stay open with their justifications until a chooser settles them;
and a kernel that never trusts a search it did not run. Objective Bend has these in a mechanized
metatheory. Its calculus is small on purpose: Faré's objects, laws by occasion, slots with
withdrawable supports, a guarded runner, documents with pushout merge. Everything rich sits beside
it as judged subsystems and native leaves, never inside it.

## The measure of a subsystem

A subsystem counts when a stranger can complete one workflow through it, end to end, on the shared
artifact: make a change, be refused by a judgment that names the law or the withdrawn support and
what would pass, repair only that, and hold a receipt a third party re-judges without the producer.
Restart and merge are part of the workflow, not extras. A subsystem that has theorems and no such
workflow is a study; it is kept as a study and described as one. The number of modules, constants,
theorems or `sorry`s is not a measure of anything and is not printed in these documents.

Today that measure is met by the vault and the package spine, and by nothing else:

- a folder of markdown opened with `obend open`, whose pages carry laws in their frontmatter, whose
  members post without overwriting, whose offline copies merge by pushout, whose cites know when
  their source moved, whose deleted and renamed pages are deleted and renamed, and whose register
  of postings is a double-entry ledger with a trial balance and receipts (`lean/tests/vault/WALKTHROUGH.md`,
  `lean/tests/ledger/WALKTHROUGH.md`);
- a package of `.obend` modules checked, run, judged against every package's laws, proved by
  re-execution and late binding where that suffices and refuted by a ground instance where it does
  not, emitted to a first-order book and specialized behind a pinned slot (`obend check`, `run`,
  `judge`, `prove`, `verify`, `ground`, `emit`, `specialize`; `lean/tests/run-*.py`).

Everything else in `lean/Obend/` (analysis, consensus, the notebook format; the hardware tier has its own program in `HARDWARE.md`, the
notebook format) is a study of what the same primitives can carry. Its documents say what is
proved and what is a worked example, and claim no workflow until one runs.

## What we hold to

The kernel admits by re-execution and checks certificates it never searched for. Every judgment
carries its quantifier and its date. Resources are not meanings: budgets, ticks and tokens are
declared and can fail by name. A law is a line a person can read, judged on every write,
inheritable, and amendable by someone who did not write it. Nothing lands beside; everything
replaces: a second interval arithmetic, a second law language, a second object finder is a defect
to be folded back, not a feature. A generalization is adopted only when it shortens proofs against
a control, and a refuted one is kept as the record of its refutation. A concrete `decide` on one
instance is a test and is written as one, never reported as a theorem. We refuse higher structure
that does not pay for itself, circuits in the trusted base until the fold is proved, and uniform
nouns that erase different semantics.

## What this is not

Not a product, and not a bigger calculus: Core4 does not grow a CAS, a verb catalog or a view IR;
machine primitives it carries (the bit-level ones) are primitives, not a direction. Not a stack of
trusted interpreters: the tower is a sequence of worlds with the same kernel, and a reflective
change is a judged turn. Not a solver: the system is as automated as the certificates it can
check, and a claim the rewriter cannot certify is reported unchecked, not proved. Not the next
anything: "what comes after Mathematica" names a direction the primitives point in, not a thing
this repository is. Not a catalog of demos: an application directory that no one can check, run
or prove from the command line is a fixture and is called one. Not a ledger of counts.

## Lineage

François-René Rideau's *Lambda, the Ultimate Object* for the objects; nanodregg's contextual
theory for slots and justifications; minidregg's Core4 for the calculus and its proofs;
breadstuffs' deos for "every action is a proof, not a promise", affordances as the projection of
the gate, and the lesson that a substrate nobody can extend produces organs nobody uses. The
decisions that fixed and revised this framing are in `review/DECISIONS-20261031.md`.
