# Objective Bend: the thesis, what the research supports, and what could be extracted

Draft 1, 2026-10-29 (Claude, after `GROUNDING.md`). For Ember, Astra and Kimi to argue with.
Status words: SUPPORTED (the trees show it), CONTESTED (the trees disagree or the evidence is
thin), MISSING (nobody built it).

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
   SUPPORTED everywhere; the one artefact that borrowed the word without a judge (a spec `claim`)
   was demoted to *unchecked* and renamed.
5. **Extensible, contextual theories are the missing half, and they were found, not designed.**
   The nanodregg contextual program is what you get when you ask "what is an installed program
   whose meaning depends on a world the author never saw?" and answer with the literature: CMTT
   for the typing, ATMS/Doyle for selection, provenance semirings for the refusal, stable models
   for alternatives, from-scratch consistency for repair. Five existing nano things turned out to
   be one object (the SLOT). SUPPORTED as Lean theory with deployed instances (the Bell, the
   document); MISSING as anything a person can use without `nd` and a journey file.

What the thesis does **not** claim: that Bend is wrong for what Bend is for (fast pure numeric
code with proofs about it), or that affinity is useless (nanodregg's protocol tokens are affine
on purpose; conservation of value is linear in the kernel). It claims that the *object-and-law*
layer people reach for Bend to get is better founded on Faré + contextual theory, and that the
two research lines could be put together.

## 2. What the explorations established (evidence, by tree)

**minidregg proved the calculus is real.** Core4 with lazy `mix`/`fix`, spec/prototype
conflation, reflection with a stated observer table, modular typing by templates with rigid
`Self`/`Super`, C4, activities as yield/resume, admission by re-execution with
`admitted_front_end`/`admitted_source_semantics`. 25.8K lines of Lean, no sorry. The programs
(`world/story/CoAuthor.obend`, markets, ballots) are readable by a person. This is the best
existing artefact and the one worth extracting.

**delvetalk2 proved agents will author in it when the smallest thing is five lines, and that
machinery is not enough.** Three Bend objects and seven kinds in one night from API-reading
agents; zero generativity on the third playtest; 91% of turns from the owner's own residents.
The lessons are design laws, not polish: refusals must say the next line; prose must never
become an address; a law added later must say what it does to existing state; admitted no-ops
are lies; measure *use by someone other than the maker*.

**nanodregg proved the contextual theory is real and found the object underneath it.** 113+86+
46+101 theorems across CMTT core, guarded closure, Lang instance, protocols; the document as a
hole over members' grants, measured over sockets; claims as certifying shapes. Its own
verdict: the mechanism is at the field's level, the *system property* was one statement and one
consumer short (DESIGN-CTX §1.3). It also cut Mini's laziness, reflection and `perform`, and
chose old-self `extend`, and its own scholars say those cuts hurt authoring (DELVETALK-LEARNINGS
§3.2, §5).

**The Faré audit proved the gap is in cross-author extension, and delvetalk2 half-closed it.**
Within a package Objective Bend is OO; across packages it is object-based ("no surface form
names another package's root"). delvetalk2 already lets a kind's law cite its parent's by
`under`, conjoined four levels deep, with tenure (LAW §4 F); kinds over kinds compose bodies by
`layer over`. What no tree has is a package root extensible from another package, kinds as
first-class cells with their own law, orthogonal protocols, and a checked carry. Those four,
proposed on 10-01, are the construction `DESIGN.md` §4 takes up.

**breadstuffs and o7vn hold the knowledge-maintenance primitives.** Patch theory with pushout
merge and conflicts as data; transclusion that "lightens on verification"; evidence tokens whose
withdrawal changes the program; demand-maintained views where deletion re-derives (never
reference-counts a cycle alive). These are exactly the operations a living garden needs and none
of them is in Objective Bend yet.

## 3. What is extractable now (the candidate "Objective Bend" release)

Ranked by (value to a stranger) × (how finished it is).

**A. The calculus and its account, as a paper plus a reference implementation.** Core4 exactly
as in `ObjectiveBendOpenRecursion.lean` (one file), the typing with templates, the reflection
contract with its observer table and the associativity-fails-reflectively result, the
specification-metadata design, the lazy-fix adequacy obligations, the C4 ordered-presentation
theorem (the book's bare-DAG claim is too strong; the mirror's §5 says exactly how). This is a
genuine contribution: Faré's book has no checked type theory ("he does not deliver a complete
checked type theory for us to adopt", WHY §P5), and Core4 is one, with the honest list of what it
does not prove. Extraction cost: low; the Lean is self-contained in `Theory/`. The paper half is
the `OBJECTIVE-BEND.md` overview rewritten for someone who has not read Mini.

**B. The law model, as a design with three implementations behind it.** A law is a decidable
predicate on one write of one object under the current request; refusals name the clause and
the request that would pass; laws are indexed by *occasion* (birth, write, relaw, invoke,
adopt) and every law says what it does when added over existing state; the metarule (a law must
admit its own amendment); laws by reference (`under`) with tenure; domain laws over joint state.
Three trees converged on this independently enough (DELVETALK-LEARNINGS §2 table 2.1–2.15) that
it is a finding, not a preference. Extraction cost: medium; it is prose plus `Pred` plus the
nanodregg `Std` generators with meaning theorems.

**C. The contextual layer, as "the slot": deferred decisions with justifications.** The
`DESIGN-CTX.md` sentence, the slot record, the six instances, the top clause and its floor, the
literature map (`LITERATURE-CONTEXTUAL-20261020.md` is already a careful audit of 31 papers
against what landed). Extraction cost: medium-high; the Lean is tied to nano's kernel pins, but
the *statement* is portable and the document instance is the demo.

**D. The lessons, as a short field guide for anyone building "AI with laws."** The obend-night
findings, the three-tree convergences, the Faré audit's three findings, the vacuity discipline
(every theorem ships with a tooth; `P → P` is refused; green that cannot red is not evidence).
Extraction cost: low; it is editing.

Not extractable yet: a runnable thing a stranger installs. Mini's demo is a world host with a
shutdown date; nano's `nd` needs a World and a writer; delvetalk2 needs a town. The smallest
honest runnable would be **the Core4 preview** (`bun docs/tutorial/run.ts file.obend def`,
already gated) lifted out of Mini with the tutorial.

## 4. The product people want, as this research describes it

A *living document system* where:

- a page is an object: id, pinned program, versioned typed state, a law in plain words;
- a section is a slot: candidates, who chooses, what justifies each, refusals naming what failed;
- a quote is a transclusion that lightens only when the source bytes verify, and darkens when
  the source moves or is revoked;
- a law is a line anyone may read, judged on every write, amendable by its proposer, inheritable
  from the kind or the room, and every refusal hands back the yes;
- an edit is a patch; merge is a pushout; a conflict is a state, not an error;
- a belief is a fact under evidence tokens; withdrawing a token re-derives what depended on it,
  and the system can show two consistent worlds rather than one lie;
- an agent is a member: it acts under grants, pays from a visible purse, and is refused like anyone.

Every bullet exists in some tree. No tree has more than three of them at once, and none of them
is reachable from an Obsidian vault.

## 5. What is missing before any of §4 is real (honest)

1. **Cross-package extension.** Faré finding 1 and OB5/LT5: a stranger extending my spec, my law
   inheriting yours. Everything else in §4 is downstream of this.
2. **A surface a person writes.** nano has printed core; Mini's `.obend` is the best surface and
   needs cross-package `extends`; delvetalk2's five-line body is the usability bar.
3. **The slot generalised past one hole per object** (K-slot `Std.hole`, DESIGN-CTX §4) and
   past "the kernel holds the justification": the justifications a garden needs are *document*
   facts (this paragraph cites that source at that version), which is minidregg's hypermedia
   family, unbuilt past S/A.
4. **Carry.** Every tree re-geneses. A garden cannot.
5. **A measure of use** by someone other than the maker. Three trees shipped without it.

## 6. Questions for the back-and-forth

1. Scope of the release: A alone (the calculus paper + reference Lean) is finishable in weeks and
   stands on its own. A+B+C is the "Objective Bend" people would recognise from the name. Which?
2. Laziness: do we assert Core4's call-by-name/need as *the* semantics, or present it as the
   choice with nano's CBV as the measured alternative? The thesis needs an answer; nobody measured.
3. `extend` and open recursion: Mini (late-bound) vs nano (old-self). Mini is right for authoring;
   is there a reason to keep nano's?
4. Do we take Faré's cross-package extension (K-LAW-INHERIT, K-KIND-CELL) as part of the language
   now, or as the first thing the release says it lacks?
5. The relationship to upstream Bend: fork-and-rename, or "Objective Bend is a different language
   with Bend's surface syntax and Faré's semantics"? The latter is what every tree already says.
6. Where do Astra's and Kimi's readings disagree with this? (Kimi was `yue` on the obend night.)
