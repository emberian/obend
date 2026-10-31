# Objective Bend: the thesis, what the research supports, and what could be extracted

Stated 2026-10-29; statuses revised 2026-11-01 against what is now proved in `lean/`. Status words:
PROVED (a theorem in the library), SUPPORTED (the trees and studies show it), OPEN (not yet settled).

## 1. The thesis, stated so it can be wrong

Bend's pitch is: laws + proofs + a fast compiler, and the thing that makes all three possible is
*affinity* (BendTT: live code may not copy a function; that is what lets `Type : Type` and
negative datatypes stay consistent, lets a `match` free its node, and makes fork-join parallelism
free). "LAWS.bend is AGENTS.md backed by proof."

The thesis of this repository is that **for the thing people want out of Bend — a place where AI
and humans keep building together under rules that cannot be broken — affinity is the wrong load-
bearing wall, and Faré's object model is the right one.** Specifically:

1. **Core4 gives a reusable `self` a non-affine source semantics on purpose, and Bend's live
   fragment has no such value.** `fix spec seed ⟶ spec (fix spec seed) seed` hands one `self` to
   every layer and uses it as many times as there are methods. In Bend a closure "can be called
   at most once, even when everything it captures is Data" and a function type is never `+`; the
   one freely reusable thing is a top-level definition name (BendTT §7). So Bend *can* express a
   statically known family's late binding, by generating names, a Data receiver tag and a
   dispatcher, or a represented interpreter with fuel, and a Bend user must write all of that by
   hand today (Astra, §A). What Bend cannot express is Faré's first-class lazy `fix`/`mix` over a
   reusable record of methods *as a value*. Taelin knows the affine core is a placeholder ("we
   don't have that answer yet", 2026-09-19); Faré's answer is a layer above the leaf, not EAL boxes.
2. **Laziness is necessary for partial objects, not for every law system, and it is compatible
   with parallel leaves.** Taelin: "parallelism is inherently competing with laziness." Faré: "the
   simplest, most natural and safest usable setting for OO is: lazy evaluation";
   `{good=7, bad=self.bad}.good` must be 7, `keep(7, fix(identity))` must be 7. A law over an
   object other people are still specifying is a partial specification. Lazy *selection* of
   demanded work and parallel *execution* of independent demanded leaves do not conflict (Astra,
   §A); the `WHY-OBJECTIVE-BEND` argument already allowed strict implementations with explicit
   indirection. SUPPORTED by Core4's call-by-name reference; CONTESTED by nanodregg's CBV cut
   (LANG-2's own critique: exponential blowup under CBV where CBN is linear), which the two
   mature instantiations in `DESIGN.md` §6 are built to settle by elaboration.
3. **The right "linearity" for a law system is Faré's, not Girard's.** LTUO §7.3.5.2: every
   ancestor's contribution counted *once and only once* in the linearized composition. That is
   what lets ten authors' laws combine into one judged conjunction without a fight. Girard-style
   affinity of *variables* buys GC-freedom and parallel speed; it buys nothing for "whose law
   applies, in what order, and can I add mine without rewriting yours."
4. **The laws people want are judged at the point of use, and Bend laws are one source of
   their justification.** Bend's `law` quantifies over inputs and its proof may live in another
   module, so it is modular, not "closed" (Astra, §A). But it is proved once about leaf code.
   What every tree here found people wanting is a *judge on every write*: a predicate on one
   write of one object under the current authority, naming the clause that refused and, where
   one exists, a request that would pass, re-derivable by anyone, amendable by someone who did
   not write it, and saying what it does when added over existing state. That is minidregg's cell
   law + `why`/`can --any`, delvetalk2's `law NAME "reading": EXPR` + metarule + `under`,
   nanodregg's `Verdict` by occasion + `adopt`. The two meet in nano's `keeps inv law` (LANG-92):
   a sentence the kernel refuses to let be false, checked by shape at install and holding along
   every admitted chain, which is a proposition about a program *and* a civic law at once. So the
   split is not civic versus propositional; it is *when* and *by whom* a law is discharged.
   PROVED: `judge_sound`/`judge_complete` (the machine's verdict is the relation's),
   `legal_law_admitted` (every dispatched write in a legal log was admitted by every law on the
   precedence list), `package_never_widens` and `judgeEffective_names` (inheritance across packages
   with the ancestor named), `keeps`/`chain_keeps`, and the `.obend` fragment compiled with agreement
   to its meaning (`lean/Obend/Law`, `Spec/LawCompile`).
5. **Extensible, contextual theories are the missing half, and they were found, not designed.**
   The nanodregg contextual program is what you get when you ask "what is an installed program
   whose meaning depends on a world the author never saw?" and answer with the literature: CMTT
   for the typing, ATMS/Doyle for selection, provenance semirings for the refusal, stable models
   for alternatives, from-scratch consistency for repair. Five existing nano things turned out to
   be one object (the SLOT). PROVED as `Obend.Slot` with `World`, `Integrity.contextual`, `repair_sound` under a stated
   compatibility condition, stored selection and the runner's `refines`; USABLE as `obend open DIR`
   on a folder of markdown, where a section is a slot, a cite is a support, and a law line is judged
   on every write.

What the thesis does **not** claim: that Bend is wrong for what Bend is for (fast pure numeric
code with proofs about it), or that affinity is useless (nanodregg's protocol tokens are affine
on purpose; conservation of value is linear in the kernel). It claims that the *object-and-law*
layer people reach for Bend to get is better founded on Faré + contextual theory, and that the
two research lines could be put together.

## 2. The claim, extended

The five points above were about Bend. The vision studies (`review/VISION-CLAUDE-20261031.md`,
`astra/ASTRA-VISION-20261031.md`) extend the claim to what the kernel is *for*, and `AMBITION.md`
states the destination. The extended claim, stated so it can be wrong:

6. **The symbolic core of a system that reasons over heterogeneous subsystems is a checker, not a
   rewriter.** A term rewriter and an e-graph are search structures and belong to the producer; the
   kernel at the center is a judged fold over a world whose rows cite pinned facts, and the lazy
   object is the right value at the center because partial things are values a law can be judged on.
   What Core4 lacks for this is terms as data (`quote`), not a larger term language. SUPPORTED by the
   two studies and `review/GENERALIZATION-20261031.md`; OPEN until `quote` exists under an observer
   ladder with its preservation theorems (`review/QUOTE-BRIEF-20261101.md`).
7. **Automation is as powerful as the certificates the kernel can check.** Every solver is a
   producer; every claim is labeled decidable, semi-decidable-with-certificate, or attested; power
   comes from the breadth and cheapness of the registry, never from trusting a cleverer producer.
   SUPPORTED by `Decides`, the law probe, `coerce`, `HasProt` and C4's checked linearization as the
   five judges that exist; OPEN until the judgment class holds one foreign certificate format end to
   end (the Judge lane).
8. **A compiler's assumptions are supports and its deoptimization is repair.** A specialized artifact
   is a candidate whose supports are the pins it assumed; the demand machine is the always-usable
   fallback; `Integrity.contextual` and `repair` are the policy theory. PROVED for the slot;
   OPEN as a runtime until the leaf emitter and the specialization slot exist.

## 3. What would refute it

A member who cannot extend a stranger's package without reading it (refutes 1 and 5: the Extends
lane's stranger example is the test, `tests/obend-source/stranger/`). A law a person cannot read, or
a refusal that cannot say what would pass (refutes 4: the vault walkthrough is the test). A cost
rewrite that changes what a member is charged with no theorem saying by how much (refutes 8 until
`≈c` exists). A judge whose `check` searches, or a certificate format whose encoding is not a theorem
(refutes 7). A `quote` under which `mix_assoc` fails observably where a law could see it (refutes 6:
the observer ladder is the discipline). And the oldest one: breadth before one inhabited surface,
which deos showed and the vault is built to prevent.

The trees this was extracted from, with dates and paths, are in `GROUNDING.md`; the decisions and
who took them are in `review/DECISIONS-20261031.md`.
