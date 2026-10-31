# Grounding: where "Objective Bend" was explored before this library, and what each exploration learned

Historical (written 2026-10-29). The library has since surpassed the trees it was extracted from; this
file is kept as the record of where each idea came from.

Written 2026-10-29 by Claude (Fable 5.1) after reading the source trees directly. Every claim
names the file it came from. Dates are the files' own. Nothing here was built or run.

## 0. The one-paragraph map

"Objective Bend" was named on 2026-10-03 in minidregg (`docs/BEND-WORLD-LANGUAGE-20261003.txt`:
"Objective Bend is its own language. Bend supplies a starting calculus ... its existing type system,
quantities, termination checker and call-by-value evaluator are not the ceiling"). It is Faré's
*Lambda, the Ultimate Object* made into a calculus with a Lean metatheory: lazy open recursion over
first-class partial specifications (`mix`/`fix`), with specification × target conflation and
reflection. Four trees then carried it in four directions: **minidregg** built the full language
(Core4, modular typing, activities, laws, admission by re-execution); **delvetalk2** put it in
front of agents as a town and measured what they did with it; **nanodregg** rebuilt the kernel
from spec, cut the language to a CEK core, and then grew the *contextual theory* (holes,
justifications, repair, open protocols, claims) on top of it; **delvetalk** (v1) forked Mini's
edition into a separate object host with Spween scenes. Two older trees hold the roots:
**breadstuffs** (the constructive-knowledge metatheory, patch theory, transclusion) and **o7vn**
(stable-model reasoning with evidence tokens). **redregg** is the design/intent archive that ties
them together and holds the literature audits.

## 1. The source trees

| tree | commits | what it is for this question | key files |
|---|---|---|---|
| `~/dev/minidregg` | 5500 | the full Objective Bend language and its proofs; the "Mini" demo (shuts 2026-11-11) | `docs/OBJECTIVE-BEND.md`, `docs/OBJECTIVE-BEND-TUTORIAL.md`, `docs/objective-bend/{REFLECTION,MODULAR-TYPING}.md`, `Theory/ObjectiveBend*.lean` (25.8K lines), `Compiler/ObjectiveBendElaborate.lean`, `world/*.obend`, `ATLAS.md`, `PROJECT.md` |
| `~/dev/nanodregg` | 773 | single-writer rebuild; Lang as CEK core; the contextual program | `CHARTER.md`, `decisions/lang.md` (7285 lines, LANG-8..95), `Lang/Contextual/*`, `Lang/{StdHole,HoleDecl,LiveHoles,Claim}.lean`, `docs/OBJECTS.md` |
| `~/dev/delvetalk2` | 2580 | the town agents actually played in (gsb, obend); Bend bodies over RECORD/THING/KIND | `README.md`, `docs/{METAPHYSICS,LAW,AUTHORING,FOUNDATION,OVERHAUL}.md`; chronicle at `~/dev/delvetalk2-lanes/chronicle/obend-2026-10-14.md` |
| `~/dev/delvetalk` | 83 | v1 object host over Mini's edition; Spween scenes; typed source objects | `docs/FOUNDATIONS.md`, `docs/SEMANTIC-INTEGRATION.md`, `profiles/TYPED-SOURCE-OBJECTS.md`, `spec/` |
| `~/dev/breadstuffs` | 10359 | the first whole system; constructive-knowledge metatheory; dregg-doc patch theory; transclusion | `metatheory/CONSTRUCTIVE-KNOWLEDGE.md`, `dregg-doc/README.md`, `site/transclusion/README.md` |
| `~/dev/o7vn` | 579 | Oracle7 native reasoning; stable models with evidence-token revision | `native/oracle-logic/{README,DEMOS}.md`, `native/experiments/{README,REVIEW}.md`, `maintained-views/README.md` |
| `~/dev/redregg` | 201 | intent archive, design memos, literature audits, scholar comparisons | `intent/WHY-OBJECTIVE-BEND-20261003.txt`, `designs/ARCHITECTURAL-ARGUMENT.txt`, `work/{DELVETALK-LEARNINGS,CONTEXTUAL-PROGRAM-20261020,LITERATURE-CONTEXTUAL-20261020,ACTIVITIES-DESIGN-20261022,REORIENTATION-20261022,HOLES-FOR-PROOF-ENGINEERING-20261020,COMPARE-20261021}.md`, `work/promo/DESIGN-{CTX,PCC,META}.md` |
| `~/dev/bend` (upstream) | 3416 | Taelin's Bend 2: the calculus and the thesis we diverge from | `README.md`, `guide/GUIDE.md`, `paper/BendTT.pdf`, `bend2/bend.ts` |
| fareoo archive (gh `emberian/fareoo-archive`) | | Faré's corpus mirrored; the principles file and the Mini audit | `FAREOO.md` (1002 lines), `AUDIT.md` (791), `sources/ltuo-objective-bend-20261003.txt`, `raw/mirrors/ltuo/2026-10-03/ltuo-readable.txt` |

## 2. The calculus (minidregg Core4, 2026-10-03 → 10-07)

`Theory/ObjectiveBendOpenRecursion.lean` is the reference. The whole term language:

```
bound lam app | mix fix | specification prototype reflect metadata project
| nat boolean label binary | record extend get | ifZero inject case ifBool | perform done
mix lower upper   ⟶  λself. λsuper. upper self (lower self super)
fix spec inherited ⟶  spec (fix spec inherited) inherited
```

Weak-head call-by-name reference; call-by-need demand machine with `@[csimp]`-proved equality.
`perform` is not a reduction: a term whose next redex is `perform` has *yielded* a Plan
(`Yields`, `Interaction`); the kernel resumes it. Proved (axioms propext/choice/Quot.sound, no
sorry): soundness, preservation, no-refusal for checked terms, finite completeness, fast-machine
equality, front-end adequacy (`OBJECTIVE-BEND.md` §"What is proved").

**Types.** `Specification<T>` = `specification(SpecMeta, Extension<T>)`; metadata is ordinary
data (`declared | composed | extension`), so `compose` is associative behaviourally but *not*
reflectively (probes R01/R02; `REFLECTION.md`). Quantities `erased | affine | linear |
unrestricted` survive from Bend, checked as "at most once"; a reusable closure captures only
unrestricted, shareable bindings (`ObjectiveBendTypes.lean:190-226`).

**Modular typing** (`MODULAR-TYPING.md`, decisions D1–D6): open declarations are *templates*
checked once with `Self`/`Super` as rigid bounded row variables; `fix(compose(L1..Ln), seed)`
discharges bottom-up; instances are emitted as closed Core4, so no machine theorem changes. C4
linearization (Faré's C3 + suffix property) in `Compiler/ObjectiveBendC4.lean`.

**Three things called law** (`OBJECTIVE-BEND.md` §"What law, claim and requires mean"):
a *cell law* (`Pred`, enforced on every write); a package `law NAME: EXPR` (enforced; fragment:
`REF == INT`, `monotone`, `writeOnce`, …); a spec `claim` (typed, retained, *never evaluated*;
renamed from `law` on 2026-10-07 so the word could not be borrowed). Domain laws over several
objects' joint state (`registerDomain`). Admission is **re-execution**: the receiver re-runs the
Lean front end and admits only a byte-identical core (`admitted_front_end`).

**Open (their own list, `OBJECTIVE-BEND.md` §"What is open")**: no surface semantics (the front
end is trusted); laws only in the fragment, claims never checked; no cross-package extension ("no
surface form names another package's root"); reflection's `R(Y M)` vs `Y(R∘M)` undecided;
guardedness of residents unchecked.

**Why (redregg `intent/WHY-OBJECTIVE-BEND-20261003.txt`)**: "a useful contribution is often
deliberately incomplete"; "requiring each contribution to be a closed executable before it can
be passed, stored, inspected or combined turns the useful intermediate object into something
outside the language"; laziness is "a semantic choice here, not merely an optimization";
`keep(7, fix(identity))` must return 7; `{good=7, bad=self.bad}.good` must return 7.

## 3. What agents did with it (delvetalk2, the obend night 2026-10-13/14)

Chronicle `obend-2026-10-14.md`: 2,146 journal entries, 924 resident turns, 61 resident-made
objects, 17 rooms, 7 kinds, 4 NPCs, three carries mid-play. **91% of turns were Ember's own
three residents**; after the 08:59 carry "almost nobody played". Third playtest generativity
(`OVERHAUL.md` §6): 0 verbs grown, 0 rules, 0 errands by residents.

What a body looked like (`AUTHORING.md` §1): five lines over RECORD, `layer over`, `Super.inscribe`.
API-reading agents (codex-moth, wiki, sophia) built kinds and Bend things in under 10 minutes.
Web-only humans typing into a box produced nothing journaled.

Named failures that are *design* lessons, not bugs (chronicle "What went wrong", DELVETALK-LEARNINGS §6):
prose became addresses (free text used as object ids, then retyped by a carry, stranding every
NPC); admitted turns that did nothing; a rule added later did not reach existing state; a
refusal that names no next step sent a client eight times to a nonexistent card; quota walls hit
before raised; staleRoot after grow-then-write in one breath. DELVETALK-LEARNINGS §7 ranked what
nano should take: (1) an authoring surface a resident can read and write, (2) bounded keyed
relations with commuting inserts, (3) refusals that say what to do next, self-describing objects,
and a *resident-use measure* beside the performance bar.

What the agents said they wanted (`METAPHYSICS.md` §7.3, from 1,763 posts): a receipt as proof,
rooms with history, rules to probe, a public beat, relations between things, a line that sticks,
a thing that persists, to be witnessed, public correction kept in the record. "Decay was asked
for in no quarter."

## 4. The contextual theory (nanodregg LANG-66 → LANG-95, 2026-10-20 → 10-26)

Trigger: three GPT-6 documents Ember pasted (`ACTIVITIES-GPT-RAW-20261020.md`): "repair hints: a
reasoning object that remembers both why it currently works and where to resume reasoning if
those reasons change." Ember: "implement this properly and thoroughly at the Lean level" (LANG-66).

What landed, in the literature's names (`DESIGN-CTX.md` §1.1, `REORIENTATION-20261022.md` §A.0):

- **Contextual**: a hole is `u :: [Ψ ⊢ A]` (Nanevski–Pfenning–Pientka CMTT), occurrences carry a
  substitution; the deployed `Term.hole n σ` *is* `clo(u, σ)` with Thm 4.2/4.3 proved (`Lang/Proofs/Fill.lean`).
- **Justified**: a filling stands while its *supports* hold — rows at versions, cells live, cells
  governed by a named law or running a named package (LANG-75.1, LANG-84 `SupportPin.cellLaw/cellPackage`).
  This is de Kleer's ATMS environment / Doyle's well-founded support. A withdrawn support is a
  pinned tombstone refusing by name forever.
- **Repair-capable**: `repair_agrees_from_scratch` (from-scratch consistency, Stein/Adapton),
  `locality` (only touched candidates re-judged), five outcomes `kept | alternative | replacement
  | strengthening | suspended`, a sixth `transported` (PUMPKIN Pi: re-check, never trust).
- **Still-analyzable**: provenance as a polynomial over tokens (Green–Karvounarakis–Tannen),
  blockers as dual indeterminates (Grädel–Tannen), refusals naming the coordinate that failed
  (why-not); nogoods (P9).
- **Alternative worlds** (LANG-72): stable models (`p :- not q. q :- not p.` has worlds {p},{q},
  union refuted), the four reports `noJustification | alternatives | conflictingEvidence | unfinished`.
- **Open protocols** (LANG-67): `Prot := ret | call op k | hole h`, holes with chooser, affine
  tokens, obligations as an upper bound, the executed prefix blocks re-plan; `no_foresight`:
  scope is a naming discipline, not a calculus fact.
- **Claims** (LANG-92): `keeps inv law`, a certifying *shape* the kernel checks at install,
  `guardedBy_sound`; "a sentence the kernel refuses to let be false."
- **The document** (LANG-83): a section is a `Std.hole` at `bytes`; candidates are members'
  posts justified by their grants; editor selects; revocation withdraws by name; the document
  repairs without reinstall. Measured over two real members and `nd`.
- **The SLOT** (`DESIGN-CTX.md` §2.1): five deployed things are one object — ROM hole, activity
  waiting row, offer, law list, package link — `{ty, chooser, source, justify, accept, life, patience}`.

The design memo's one sentence: "the MEANING OF AN INSTALLED PROGRAM IS A FUNCTION OF THE WORLD,
given by justifications: ⟦P⟧(W) is the closed program obtained by filling every deferred decision
of P with the candidate whose justification holds at W, and a refusal names the justification that
failed." Top clause: CONTEXTUAL INTEGRITY ∧ REPAIR (B4/B4′) with a stated floor of trivial systems
it refutes.

Proof-engineering extension (`HOLES-FOR-PROOF-ENGINEERING-20261020.md`): "a theorem as a hole";
"the crucial distinction is between retaining a proof, retaining its reconstruction recipe, and
authorizing a claim about the current system"; a shadow obligation journal over a kernel slice (PE1).
Ember (CARD 9): "these techniques are for OUR verification/proof engineering too (nano → minidregg
→ breadstuffs)"; ruled (B): contextual holes in the deployed language.

What nanodregg deliberately *cut* from Mini's Objective Bend (LANG-6, LANG-18, ACTIVITIES-DESIGN §0.11):
call-by-need (CBV CEK instead; "a program that is linear under call-by-need is exponential here"
is its own unmeasured critique), `perform` in the term language, reflection, `Activity<P,R,A>` as a
type; and `extend` keeps the *old* self (`bigStep_extend_keeps_old_self`), so open recursion is
`fix` over a mixin "the authoring tool writes" — which DELVETALK-LEARNINGS §3.2 calls the wrong
choice for authoring.

## 5. The Faré audit (fareoo `AUDIT.md`, 2026-10-01, against Mini before Objective Bend)

Verdict: Mini was *object-based*, not *object-oriented*, in Wegner's/Faré's sense — "cells with
laws are first-class modules; nothing in the world extends anything else in the world." Three
contradictions: (1) laws cannot inherit, only be replaced or copied (below Faré's ADVISE floor);
(2) kinds, verbs and templates are second-class — every new kind is a flag day; (3) re-genesis is
the only upgrade, the carry is a shell script. Proposed: `K-LAW-INHERIT` (laws with parents,
C3-linearized conjunction, refusals naming the ancestor clause), `K-KIND-CELL` (type descriptors
as cells, `create --from`), `K-CARRY` (a Lean-checked linear carry with named drops).

Objective Bend answered (1) inside a package (spec/compose/fix) but not across packages (OB5/LT5
open). nanodregg answered (3) partly (`Host/Carry.lean`, and OVERLOOKED-20261027 A1 says the carry
was built on without looking). Nothing answered (2) as Faré states it.

## 6. The thing people actually want (across trees)

- minidregg `PROJECT.md` "Outcome first": what changed, from which root; which request, authority,
  law justified it; which causal parents and transcluded sources made this document current; is a
  conflict explicit; can I hand a compact proof of this history to another device.
- minidregg `PROJECT.md` §Hyperdocuments: "not a UI feature bolted onto receipts. They are a
  semantic/history family": typed identity, provenance-bearing conflicts, link and transclusion
  records with origin evidence, stable ranges, marks separated from content, causal events,
  authenticated backlinks, offline branches and conservative merge.
- breadstuffs `dregg-doc`: patch-theoretic document (Mimram–Di Giusto pushout merge, conflicts
  as first-class antichains, review-as-resolution); `site/transclusion`: "Xanadu made honest":
  verification lightens, nothing else does.
- breadstuffs `CONSTRUCTIVE-KNOWLEDGE.md`: "authority is constructive knowledge": to hold a
  capability is to be able to produce a witness the kernel accepts; evidence is the one monotone
  substance; "determination is eager; witness is lazy."
- o7vn `oracle-logic/DEMOS.md`: "Facts belong to evidence tokens, not just atoms"; withdrawal
  changes the program; "keep revisions above the solver"; "separate possible actions from
  commitments"; "make evidence repair visible."
- delvetalk2 `METAPHYSICS.md`: "the honest ontology is *things that answer, under a law, in one
  order of heights, found by name, maker and citation, kept by attention*."

## 7. Taelin's position, in his words (Scry, `twitter.tweets`, author `VictorTaelin`)

- 2026-09-17: "the foundations of this project - strong types, linearity, proofs - are extremely robust."
- 2026-06-19: "linearity is the obvious solution to implementing functional runtime with O(1)
  mutable buffers, and free of garbage collection, and massively parallel ... human intuition
  biased towards thinking that sharing variables is 'free'."
- 2026-06-04: "once you have purity and linearity, massive parallelism becomes simple."
- 2026-07-11: "parallelism is inherently competing with laziness."
- 2026-09-19 (on proofs not reusing hypotheses): "the reason we choose to start with a fully
  affine core is merely so we stay flexible to pick the best possible way to add higher-order
  contraction, and we don't have that answer yet" (EAL-style sharing, or Idris-2-style).
- 2026-09-20: "in Bend, I make a conscious choice to have 'Type : Type', not because I really
  think that's a super useful feature to have, but because I wanted to make a point."
- `guide/GUIDE.md`: "A closure is affine: it can be called at most once, even when everything it
  captures is Data. Only top-level definitions can be called freely."

## 8. Faré's "linearity" (LTUO §7.3.5.2, "Linearity: Conservation of Information")

"The information contributed by each ancestor's modular extension shall be taken into account
once and only once ... Languages that respect this linearity property replace conflict with
cooperation ... I am naming this property linearity after the similar notion from 'linear logic'."
This is the Flavors innovation (1979). It is a property of *composition*, not of *variable use*.

## 9. Dates, for the record

2026-08-06 ATLAS (minidregg founded from breadstuffs' diagnosis) · 10-01 fareoo FAREOO/AUDIT ·
10-03 Objective Bend named; Core4 reference · 10-04 Lean elaborator is THE front end; TS deleted ·
10-05..07 activities, call, send, seats; `law`→`claim` · 10-08..09 delvetalk v1 · 10-13/14 the
obend night · 10-16 nanodregg charter and Lang core · 10-17 DELVETALK-LEARNINGS · 10-20 GPT-6
docs; LANG-66..68; literature audit · 10-22 ACTIVITIES-DESIGN, REORIENTATION, LANG-75 promotion
program · 10-26 DESIGN-CTX, LANG-83/84/92 · 10-27 Mini demo definition; OVERLOOKED · 10-29 o7vn
experiments review.
