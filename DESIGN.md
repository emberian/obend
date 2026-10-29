# Objective Bend over Leaf Bend: the design

Draft 1, 2026-10-29 (Claude). Builds on `GROUNDING.md` and `THESIS.md`; written to Ember's
direction of the same day: link the non-affine object layer to Taelin's affine leaf
computations; make cross-package extension, laws and document-type thinking natural; strongest
version, wide scope, no named gaps; two mature instantiations rather than a harness.

## 1. The seam, in one sentence

**Objective Bend is a lazy, non-affine language of specifications whose targets are Bend books;
`fix` elaborates a book; `self` and `super` are names in that book, not runtime values.**

Bend already has exactly one freely reusable thing, and BendTT §7 says which: "the name of a
definition is not a variable, so a program may call a definition any number of times." BendTT
ties recursion through names ("Recursion goes through the names of definitions", §4). Mini's
front end already lowers `self.m` to a knot field `M.m` and `super.m` to a hidden layer global
`M.S#primary` (`OBJECTIVE-BEND-FRONTEND.md`, "Surface language and its core lowering"). So the
object layer's non-affinity is the non-affinity Bend already grants to names, and nothing else.
Faré said this of C++: templates are "a full-fledged Pure Functional Lazy Dynamically-Typed
Prototype OO language at compile-time" (LTUO §2.2.3). Objective Bend is that layer, done on
purpose, with a checked metatheory, over Bend instead of C++.

```
  Objective Bend                      lazy · non-affine · partial specifications
    spec / compose / fix / reflect    Faré's linearity: each layer applied once, in C4 order
    laws judged on writes             civic laws: the clause that refused, the request that passes
    slots, justifications, repair     contextual theory: meaning as a function of the world
  ─────────────── fix ⇒ a book ────────────────────────────────────────────────────────────────
  Leaf Bend (= Bend)                  strict · affine · total
    def Obj.m(state: S, args) -> R    Faré's U-encoding: receiver first; names freely callable
    law / def Laws.m  (BendTT)        Girard's affinity: no β step copies a call ⇒ termination
    bend -o  (C, Metal, CUDA, JS)     Taelin's parallelism, GC-freedom, O(1) arrays
```

Each author keeps their claim whole. Taelin: "parallelism is inherently competing with
laziness" is true *inside a leaf*, and leaves are strict. Faré: "Lazy makes OO easy" is true
*of elaboration*, and elaboration is lazy: a method nobody demands is never built, a spec with
a divergent target is still a value you can extend and reflect on. Faré's linearity
(conservation of each ancestor's contribution, LTUO §7.3.5.2) is a theorem about `fix` over
the C4 list; Girard's affinity is a theorem about the leaves it emits. They never meet in the
same term.

## 2. What `fix` emits, and what it costs in the leaf

**Books.** `fix(compose(L1 … Ln), seed)` with target `T` emits a Bend book: one top-level
`def Obj.m(state: T.State, …)` per provided method, `Obj.m@k` for each layer's version of `m`
(so `super.m` is a name), a `type Obj.State is Data` for the declared state, and the laws as
`law`/`def Laws.*` pairs where the spec's claims are leaf claims. Open specs (templates with
rigid `Self`/`Super`) are checked once and instantiated per `fix` as Mini already does
(`MODULAR-TYPING.md` D1), which is exactly Bend's `~` template discipline ("each distinct set of
`~` arguments compiles to its own copy").

**State is Data.** Bend: a `+` value must be `Data`; closures are `Type`. Mini: declared state
is first-order data, and an activity type "is never shareable, so no effect can sit in a field,
argument, payload or Plan" (`OBJECTIVE-BEND.md` §Types). The two restrictions coincide. An
object's state is a `Data` record; its behaviour is a set of names. Nothing is lost that either
system allowed.

**Mutual recursion through `self`.** Bend's rule: a definition may call earlier definitions, or
itself on smaller arguments; two mutually recursive functions "become one def with an extra
argument selecting which to run" (GUIDE, "Recursion and Termination"); otherwise `@unsafe`,
which runs but leaves the proof fragment. The elaborator knows the whole post-`fix` call graph,
so it does what Bend asks, mechanically:

1. methods whose call graph through `self`/`super` is acyclic are emitted in topological
   order as ordinary defs (the common case: `bill` calls `price`, `price` calls nothing);
2. a strongly connected component of methods is emitted as Bend's own prescribed shape, one
   dispatcher `def Obj.dispatch(which: Obj.Method, fuel: Nat, state, args)` with a descending
   `fuel`, which BendTT accepts (the 10-03 note already saw this: "a single checked tagged
   dispatcher with explicit descending fuel");
3. a method the author marks `live` is emitted `@unsafe`: Bend runs it, BendTT names every
   dependent proof it taints, and in the world it is admitted the way Mini admits everything,
   by re-execution under a declared envelope with refusals by name. World code is not proof
   code; the two already have different gates in every tree here.

**Where laziness stops.** Inside a leaf, evaluation is Bend's. Laziness lives in three places,
all above the leaf: elaboration (which layers and methods are built), the kernel (a slot is
filled when demanded, an activity yields and is resumed), and the record of thunks a method may
return (a Bend record of names, not of closures). Faré's two tests pass by construction:
`keep(7, fix(identity))` is `7` because `fix(identity)` elaborates to an empty book nobody
demands; `{good = 7, bad = self.bad}.good` is `7` because `bad` is a def nobody calls.

**Effects.** A method's effects are data it returns (a Plan), as in Mini and nano and
delvetalk2 ("asking the world is the only effect"). Bend's `IO` never appears in a method; the
kernel is the event loop. Bend's own `IO` stays available to a Leaf program a member runs
outside the world, which is Bend today.

## 3. Laws, three kinds, one word

A `law` line means one of three things, and the page says which by where it is written:

| where | what it is | who checks | when |
|---|---|---|---|
| `LAWS.bend` of a leaf package | a proposition about leaf definitions, proved in `PROOF.bend` | BendTT (`bend --verdict`) | once, at publish |
| `law NAME "reading": EXPR` on an object or kind | a decidable predicate on one write of one object under the current request | the kernel, by re-execution | every write |
| `keeps inv law` on a package | a sentence the kernel refuses to let be false, by a certifying shape | the install check (nano LANG-92) | at install |

The three compose: a world law may *cite* a leaf law as a justification. In the slot
vocabulary (`DESIGN-CTX.md` §2.1) that is a new support constructor beside `cellLaw` and
`cellPackage`: `leafProof (package, lawName, kernelHash)`, "the hub record for this package
carries ALL PROOFS CHECK for this law under BendTT kernel `H`." When the package is upgraded and
the proof no longer checks, every slot that cited it is withdrawn *by that name*. Bend's static
laws become defeasible justifications in a living world without changing what they prove.

World laws inherit (Faré finding 1, `AUDIT.md` §1): a law may name parents; the kind's text is
an implicit parent (`under`, delvetalk2); the room's law is another; the effective law is the
C4 linearization of that DAG, combined by conjunction, so a child only narrows; a refusal
names the ancestor clause ("refused: lab/board (kind law) clause 2: monotone(state); the write
that would pass: …"). Every law states its `adopt` arm: what it does when added over existing
state (nano LANG-24), so a kind's owner amending the kind re-laws every instance at its next
write and the amendment is judged by the kind's own law. The metarule stands: a law is accepted
only if it admits an amendment by its proposer (delvetalk2), with the escrow-shaped exception
that a package may declare its laws frozen at birth (nano), which the metarule reads as "the
proposer chose to bind their own hands, and said so."

## 4. Cross-package extension: names are intentions, hashes are extensions

Faré, LTUO §9.3.7: "a name path or location properly identifies an extensible 'intention'
rather than an immutable 'extension', a meeting point rather than fixed code ... If users
wanted the latter, they would be using cryptographic hashes, not names." Bend's hub already has
both forms: `import 0x<hash>/main.bend` and `import name@version/main.bend`. The design takes
them as the two halves of one thing.

- **A package root is a specification**, as Mini already makes it (`fix(specification({package:
  …}, λ$globals λ$seed. extend $seed {…}), {})`). The missing surface form is one line:
  `package Garden extends commons/record@^2, bells@0x9f…` names other packages' roots as
  parents. A hash parent is an extension: fixed forever. A name parent is an intention: a
  **slot** whose chooser is the name's owner (the hub record, or a kernel cell under that
  owner's law), whose candidates are the versions, whose justification is "the record names
  version v at pin p." Resolving an intention is a fill; a new version is a repair offered, not
  applied; the executed prefix (objects already born) keeps its pins until their owners adopt.
- **C4 across packages.** Identity is already the qualified declaration key; it becomes
  `(intention, declaration)`, so a diamond through two routes to `commons/record` applies it
  once, and `compose(E, E)` still applies `E` twice. The precedence list is one list over the
  whole DAG; the suffix property lets a package declare itself a suffix of its base so the
  base's optimizations hold (LTUO §7.4). A cycle or incompatible suffix refuses at `fix` with
  the two packages named.
- **Orthogonal protocols** (LTUO §9.2.9): a method lives on the pair (generic, spec). A third
  package may `protocol Render for commons/record: def render(self) -> Page` without being in
  record's ancestry and without record's author anticipating it; C4 orders the protocol's
  layers with the rest. This is the expression problem's "real solution" in Faré's words and
  the platform-not-application demand of Houyhnhnm ch. 7: a new kind of thing is usable by every
  existing interface, and a new interface attaches to existing things after the fact.
- **What the kernel admits.** A member's turn against an object whose spec crosses packages
  pins every root it resolved (the intentions' fills at their versions). Admission re-derives
  the `fix` at those pins and runs the method; a moved pin is `stale` by name; a changed law on
  an ancestor is an `adopt` occasion for every instance at its next write. The ecosystem is
  "one vast open recursion until the very last moment" (Faré, `todo`), closed lazily per demand,
  which is nixpkgs' global fixed point with pins instead of a channel.
- **Kinds are cells** (`AUDIT.md` §2, K-KIND-CELL): a type descriptor is first-order data in a
  cell with its own law; `create --from K` births under it; a kind may inherit from a kind. So
  a stranger mints a kind without anyone rebuilding anything, and the kind's law is an ancestor
  of every instance's effective law.

## 5. Document-type thinking: one vocabulary

Five words, each a thing in the world, together a page a person writes in:

| word | what it is underneath | what it does |
|---|---|---|
| **page** | an object of kind `Page`: id, pinned program, versioned state (rows of runs), law lines | the unit a person names and links |
| **section** | a slot at type `Run`: candidates posted by members, a chooser, each candidate justified | the unit of contribution; selection is editing, revocation withdraws by name |
| **cite** | a support: `(page, range, version)` of another page's bytes | a quote that lightens when the bytes verify and darkens when the source moves |
| **law** | a `law NAME "reading": EXPR` line on the page or its kind | judged on every write; refusals hand back the yes |
| **kind** | a spec over `Page` (a layer): forms, verbs, rules, wants, a voice | what a stranger extends; a notebook, a ledger, a ballot, a story room are kinds |

Derived, not separate subsystems: a **transclusion** is a section whose selected candidate is a
cite (the document instance of LANG-83 with `cite` as the support); a **patch** is the row edit
a write makes, with dregg-doc's algebra (`Add | Delete | Connect | SetField`, compose, invert)
as the kernel's edit type for `Run` relations; a **merge** is the pushout of two patches, and a
**conflict** is a section with two live candidates and no selection, which the slot already
reports as `alternatives`; a **belief** is a line whose supports are evidence tokens, and a
withdrawn token is a tombstone the reader sees as `support dead: camera/bird`; a **backlink**
is the authenticated reverse index of cites, which the kernel maintains because a cite is a
support it already pins.

What an Obsidian-shaped person does on day one: `obend open ~/vault` reads every `.md` as a
page (the file is the page's rendering, kept on disk), every `[[wikilink]]` as a cite, every
`law:` line in frontmatter as a law, every folder as a kind they may later give a body. Nothing
in the vault changes shape. What changes is that a second person's edit to a page is a
candidate in a section, a quote from a moved source darkens, a law they wrote refuses an edit
and says which line would pass, and an agent they invite is a member who pays for its writes and
is refused like anyone. The vault is still markdown; the world is where it means something.

## 6. Two mature instantiations

Not a harness. Two complete elaborations of the same programs, so the ideas can be read worked
out and compared by the people who wrote them.

**I. Objective Bend over Leaf Bend.** `fix` emits Bend books; methods run on Bend's compiler;
leaf laws are BendTT theorems; the world kernel (admission, slots, laws, receipts) is Lean, as
Mini's and nano's are. Laziness lives above the leaf. "Mature" means: the CoAuthor story, the
single-seller market, the Tally resident and the two-member document (LANG-83) all run with
their laws, and a Bend user's unmodified package is an ancestor of a world kind.

**II. Objective Bend over Core4.** Mini's language as built: lazy call-by-need all the way down,
reflection and `perform` in the term language, admission by re-execution on the Lean machine.
"Mature" means the same four programs, plus cross-package `extends` added to the front end.

What the comparison teaches: where laziness must live. I says "in elaboration and the kernel";
II says "in every value." Both are consistent with Faré; only II is in tension with Taelin.
The programs are the same; the difference is in the elaborator's output and in what each proves
about a method body. Whoever reads both elaborations will know which they want, and why, which
no number would have told them.

## 7. Upstream

Build our own thing; depend on Bend as a toolchain; never fork it. Reasons from the trees:
Mini already deleted its embedded upstream Bend stack on 10-04 and made the Lean elaborator the
one front end; `bend2/bend.ts` is capped at 48k tokens and "only Taelin changes them"
(`bend/AGENTS.md`); the compiler is "99% AI-written" by its own header. What we take from Bend
is exactly what it is good at and we are not: the leaf compiler to four backends, the BendTT
kernel as the checker for leaf laws, the hub as the store of hashed extensions and named
intentions. What Bend's users gain from us, on day one: their package becomes an object a
stranger can extend without forking, their `LAWS.bend` becomes a justification a living
document can cite and lose, and their code runs as the method bodies of a world where agents
are members. That is the interop story, and it needs no change to Bend.

## 8. What this demands (the construction, not a backlog)

1. The elaborator's second target: Core4 ⇒ Bend book, with the acyclic/dispatcher/`live`
   emission rule and the theorem that the emitted book's behaviour is the Core4 term's
   (`accepted_execution_semantics` restated against Bend's reference evaluator).
2. `package … extends …` in the front end; C4 identity `(intention, declaration)`; intentions
   as slots in the kernel; `leafProof` as a support constructor.
3. Laws with parents and `adopt` arms; the kind cell; refusals naming the ancestor clause and
   the request that passes, in the browser as well as the shell.
4. The `Page` kind with sections as slots, cites as supports, patches as the edit type, the
   `obend open vault` reader and the markdown renderer.
5. The carry as a Lean function with named drops (`AUDIT.md` K-CARRY), because a garden is
   never re-genesised.
6. Both instantiations complete on the same four programs.
