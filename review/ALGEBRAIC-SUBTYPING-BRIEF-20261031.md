# Scholar brief: algebraic subtyping for Objective Bend

Ember watched a talk on Dolan's algebraic subtyping (bunification over a distributive lattice,
automaton representation of recursive types, width subtyping on records versus rows, MLscript) and
asked whether our system benefits. My first read is in the conversation summary below; your job is
to read the papers properly and produce the design, including where my read is wrong.

Read, in this order, from `~/paperbin` (`.txt` beside each `.pdf`): `dolan2016-algebraic-subtyping-thesis`
(chapters on the lattice, biunification, polar types, the automaton simplification; it is long,
read what the design needs), `dolan-mycroft2017-mlsub`, `parreaux2020-simple-essence-algebraic-subtyping`
(the implementable core), `parreaux-chau2022-mlstruct`, `parreaux2024-superf-subtyping-constraints-liberate`
(first-class polymorphism), `tang2023-structural-subtyping-as-parametric-polymorphism` (rows versus
structural subtyping, the encoding theorems; this one decides our rows question), and the OO
precedents `canning1989-f-bounded-polymorphism`, `cook-hill-canning1990-inheritance-is-not-subtyping`,
`bruce2002-comparing-object-encodings`. Then our side: `/Users/ember/dev/obend/DESIGN.md` §2 and §4,
`METATHEORY.md`, `review/CHECKER-COMPLETENESS-REPORT-20261030.md`, `review/ARGON-RESPONSE-20261030.md`,
`lean/docs/REPORT-EQUIREC-20261031.md` (equi-recursive agreement by finite bisimulation, full
annotated completeness via `Classical.choose`, nine decisions), `minidregg`'s
`docs/objective-bend/MODULAR-TYPING.md` (templates with rigid `Self`/`Super`, D1–D6; read-only at
`/Users/ember/dev/minidregg`), and the code: `lean/Obend/Core/Ty.lean`, `Core/Check.lean`
(`PartialTyping`, `Assumptions` with `bounds` and `rigid`), `Core/EquiRecursiveAgreement.lean`,
`Core/Bidirectional.lean`, `Spec/Elaborate.lean` (`templateLayer`, `chainFix`, `instantiate`).

My first read, to be checked: (1) a template's rigid `Self ≥ ρ` is an MLsub variable with a lower
bound from the provided methods and upper bounds from each `self.m` use, so biunification infers
the principal mixin type with no written bound; (2) our finite-bisimulation equality is Dolan's
automaton representation minus the subsumption direction; (3) biunification is the constructive
elaborator our `annotateFromDerivation` lacks; (4) the kernel must keep equality and re-check
certificates, so subtyping belongs in the elaborator with explicit coercions (projections,
injections) emitted into Core4, which Bend's copy-on-subtype leaves pay for anyway; (5) quantities
are orthogonal but unexamined; (6) scoped rows with duplicate labels carry field provenance that
width subtyping forgets, and C4 and reflection care about that.

Write `/Users/ember/dev/obend/review/ALGEBRAIC-SUBTYPING-20261031.md`: the mapping of Core4's type
algebra onto Dolan's lattice (what is a lattice element, what polarity means for arrows, records,
variants and our bounded and rigid variables, what has no image); the template elaborator by
biunification as a design, with the exact coercion grammar it emits and the theorem it would carry
(the emitted annotated term checks under `Bidirectional.checkAgainst`, making annotation discovery
executable on the template fragment); the rows-versus-width decision argued from Tang et al. and
from what C4 and reflection need; the quantity interaction stated as open with the specific case
that worries you; and a construction order with the first artefact. Tag claims READ, INFERRED or
PROPOSED. Plain prose, one claim per sentence, no praise, as long as it needs to be. You may fetch
one or two more papers through Kagi if a claim needs them (key in `~/dev/allgame/.env`, request shape
in `~/dev/allgame/claude_resident/tools/web_tools.py`, PDFs into `~/paperbin` with a `.txt` sibling via
`pdftotext`). Commit the file on `dev` with `git -c commit.gpgsign=false commit -F -` and the trailer
`Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`; another lane is editing `lean/`, so
commit only your file and push. Reply with the commit hash and the three places you disagree with
my first read.
