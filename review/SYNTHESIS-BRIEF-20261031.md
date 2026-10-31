# Synthesis brief: a hybrid foundation for Objective Bend, better than any one paper

Ember asks for a hard think, not a survey: read what we have, read the papers we drew on, and look
for the generalization that unifies them for our setting, drawing on higher category theory and
whatever else earns its place, so that the result builds directly on the papers' wisdom and is
better for us than any of them alone. Write it as a research design that a lane could start on.

What we have, in reading order: `/Users/ember/dev/obend/THESIS.md`, `DESIGN.md`, `METATHEORY.md`,
`review/PRIOR-ART-20261030.md`, `review/ARGON-RESPONSE-20261030.md`, `review/ALGEBRAIC-SUBTYPING-20261031.md`
(yesterday's scholar: Dolan's lattice mapped onto Core4, the template elaborator, rows versus width,
the quantity question), `lean/docs/REPORT-EQUIREC-20261031.md` (equi-recursive agreement by finite
bisimulation), `lean/docs/REPORT-DOC-20261030.md` (patches, the pushout, conflicts as objects),
`lean/docs/REPORT-LAW-20261030.md`, `lean/docs/REPORT-20261031.md` (the slot's `World` and
`Integrity`), `review/KIMI-REVIEW-20261030.md` §1 and §2 (where the slot theory is weak), and the
Lean itself where a claim needs it (`lean/Obend/{Core,Slot,Law,Doc}`). The sources: `~/paperbin`
(each `.pdf` with a `.txt`): Dolan's thesis and MLsub, Parreaux's Simple-sub, MLstruct and SuperF,
Tang et al. on structural subtyping as parametric polymorphism, Cook–Palsberg and Bracha–Cook on
inheritance as fixed points over generators, Canning's F-bounded polymorphism, Bruce–Cardelli–Pierce
on object encodings, Mimram–Di Giusto's categorical patches and Angiuli et al.'s homotopical patch
theory, Nanevski–Pfenning–Pientka's CMTT and Cave–Pientka's first-class substitutions, Wood–Atkey on
usage vectors, Gaboardi et al. and Orchard et al. on graded modalities, Green–Tannen and Grädel–Tannen
on provenance semirings, de Kleer's ATMS and Doyle, Mokhov et al.'s build systems, Delaware's
meta-theory à la carte, Xia's interaction trees, Amadio–Cardelli, Launchbury and Moran–Sands, Faré's
*Lambda, the Ultimate Object* (`/Users/ember/dev/obend/astra/fareoo/raw/mirrors/ltuo/2026-10-03/ltuo-readable.txt`
if present, else the GitHub mirror `emberian/fareoo-archive`). Fetch what you need beyond that through
Kagi (key in `~/dev/allgame/.env`, request shape in `~/dev/allgame/claude_resident/tools/web_tools.py`,
`$ANNAS_SECRET_KEY` for paywalled papers), into `~/paperbin` with a `.txt` sibling.

The threads that look like one thing, which is the question: a specification is a generator and an
object is a fixed point (Cook); composition of layers is linearized so each contributes once (Faré's
linearity, C4); the type of a layer is a bounded variable in a lattice (Dolan) or a row-polymorphic
function (Rémy, Tang); a law is judged at every write and inherits along the same DAG; a slot is a
deferred decision with supports that can be withdrawn and repaired, and its justifications are a
semiring (Tannen); a document is a graph with patches whose merge is a pushout in a free cocompletion
(Mimram–Di Giusto); a hole is a contextual modal type with a substitution (CMTT); usage is a vector
over a semiring (Wood–Atkey); laziness is a semantic choice with an improvement order (Moran–Sands).
Each of these has a categorical reading: generators and their fixed points as algebras and
coalgebras; linearization as an ordered colimit; the lattice of types as a (co)complete poset
enriched over something; laws as predicates in a fibration over the world's history; slots and
justifications as a Grothendieck construction over the semiring of supports; patches as a 2-category
or a double category with conflicts as objects; CMTT's contexts as a fibration; graded usage as a
graded comonad; improvement as a preorder-enrichment. Where is the single structure of which these
are instances, for *our* setting (lazy, non-affine object layer over affine leaves, admission by
re-execution, refusals that name what would pass), and what does having it buy: fewer theorems,
theorems that transport, a kernel that is one construction rather than six? Be concrete about which
level of structure is actually needed (a double category, a fibration, a graded monad, a 2-category
of patches) and where plain order theory or a monoidal category suffices; higher structure that does
not pay for itself is a cost. Say where the papers' own generality should be *refused* for us.

Write `/Users/ember/dev/obend/review/SYNTHESIS-20261031.md`: the candidate unifying structure(s),
stated precisely enough that a Lean definition could be written from it; what each existing module
becomes under it (Core, Spec, Law, Slot, Doc, Leaf) and which current theorems become instances of
one general theorem; the new theorems it makes available (the ones none of the papers has because
none of them has all the pieces); what it would cost to adopt (which modules change, which
statements change shape); the three experiments that would test whether it is real before
committing (each a Lean file a lane could write in a day); and the honest list of what it does not
unify. Tag claims READ, INFERRED, PROPOSED. Plain prose, one claim per sentence, no praise, as long
as it needs to be. Commit the file alone on `dev` with `git -c commit.gpgsign=false commit -F -`
and the trailer `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`, then push; a Lean lane is
editing `lean/` concurrently, so touch nothing there. Reply with the commit hash, the structure you
propose in one sentence, and the single experiment you would run first.
