# Scholar brief: `quote` for Core4, oriented in two decades of staging and reflection theory

Ember, 2026-11-01: "I do agree that quote is necessary. We need to be careful though. There have been
a lot of papers the past two decades about good ways to do these things while retaining important
formal properties. We may need to pull more things into paperbin and orient a bit more deeply into
that theory." This is that orientation. It lands nothing in `lean/`; its output is a property list,
a theorem list and a design, precise enough to brief the lane that builds `quote`.

## Where the question stands

Read `review/VISION-CLAUDE-20261031.md` §3.2, §3.4, §4 (the `quote`/`splice`/`≈q` design, the observer
ladder, `rewrite_sound_below`, mirrors, stages as views, EP boundaries) and `astra/ASTRA-VISION-20261031.md`
§2 (typed represented syntax first, checked contextual substitution, three separate promises, Tan–Wei
2026, no tower authorizes its own admission change). They disagree on whether `quote` is a Core4
constructor from the start or a library over a represented syntax promoted later; the working
position is Astra's order with the Claude study's targets. Then the calculus as it is: `lean/Obend/Core/Term.lean`
(24 constructors; `reflect`, `metadata`, `perform`, `hole n σ`), `Core/Machine.lean` (call-by-need,
cells, blackholing, checkpoints), `Core/Check.lean` (`PartialTyping`, uses vectors, quantities,
`reusableAllowed`), `Core/Equiv/*` (`Ahead`, `≈b`, `mix_assoc`), `Obend/Slot.lean` and
`Slot/Calculus.lean` (CMTT-shaped holes, `Scoped 0` fillings, `calculus_typed_msubst`),
`minidregg/docs/objective-bend/REFLECTION.md` (read-only: the observer table; associativity fails
reflectively on purpose), `review/EQUIV-PLAN-20261031.md`, `review/ALGEBRAIC-SUBTYPING-20261031.md` §5
(quantities are not orthogonal to coercions; the same will be true of splices).

## The literature to pull into `~/paperbin` and read

Fetch each (Kagi key in `~/dev/allgame/.env`, request shape in `~/dev/allgame/claude_resident/tools/web_tools.py`;
`~/.annas-key` and `$ANNAS_SECRET_KEY` for paywalled ones; name files `author-year-short-title.pdf`
with a `.txt` sibling via `pdftotext`; several may already be there, check first). Read them for the
*property* each one isolates and the *construction* that secures it:

- Modal staging and contextual types: Davies–Pfenning, *A modal analysis of staged computation* (JACM
  2001); Davies 1996 (`○`, temporal); Nanevski, *Meta-programming with names and necessity* (ICFP 2002)
  and Nanevski–Pfenning, *Staged computation with names and necessity* (JFP 2005); Nanevski–Pfenning–Pientka
  CMTT (in paperbin); Jang–Gélineau–Monnier–Pientka, *Mœbius: metaprogramming using contextual types*
  (POPL 2022; pattern matching on code with contextual types); Pientka's Beluga and Cocon (Cocon in
  paperbin); Kavvos, *Intensionality, intensional recursion, and the Gödel–Löb axiom* (2017) and his
  thesis on the semantics of intensionality (quote as an intensional operation and what it does to
  extensionality; the modal law that makes intensional recursion consistent); Gratzer–Kavvos–Nuyts–Birkedal
  MTT (multimodal dependent type theory) for the modality discipline.
- Multi-stage programming: Taha–Sheard, *MetaML and multi-stage programming with explicit annotations*
  (TCS 2000); Taha–Nielsen, *Environment classifiers* (POPL 2003); Calcagno–Moggi–Taha on classifier
  inference; Kiselyov, *The design and implementation of BER MetaOCaml* and the 2026 *MetaOCaml: ten
  years later* (Astra fetched it); Kameyama–Kiselyov–Shan, *Shifting the stage* and *Combinators for
  impure yet hygienic code generation*; Rhiger, *First-class open and closed code fragments*;
  Kovács, *Staged compilation with two-level type theory* (ICFP 2022) and Kovács–Kaposi,
  *Closure-free functional programming in a two-level type theory* (ICFP 2024); Annenkov–Capriotti–Kraus–Sattler,
  *Two-level type theory and applications*; Xie–Pickering–Löh–Wu–Yallop–Wang, *Staging with class*
  (POPL 2022); Stucki–Biboudis–Doeraene–Odersky, *Multi-stage programming with generative and
  analytical macros* (GPCE 2021; Scala 3 quotes, splices, pattern matching on code); Amin–Rompf,
  *Collapsing towers of interpreters* (POPL 2018; Astra fetched it) and Rompf–Amin, *Functional pearl: a
  SQL to C compiler in 500 lines* for stage polymorphism in practice; Tan–Wei 2026 (Astra fetched it).
- Hygiene and scope: Dybvig's syntactic closures / Adams, *Towards the essence of hygiene* (POPL 2015);
  Ullrich–de Moura, *Beyond notations: hygienic macro expansion for theorem proving languages* (Astra
  fetched); the scope-extrusion problem as MetaOCaml states it.
- Typed quotation with proofs: Devriese–Piessens, *Typed syntactic meta-programming* (ICFP 2013);
  Sozeau et al., *The MetaCoq project* (JAR 2020) and *Coq Coq correct!* (POPL 2020) (verified
  quote/unquote and a verified checker); Chapman, *Type theory should eat itself*; Altenkirch–Kaposi,
  *Type theory in type theory using quotient inductive types* (POPL 2016); Kaposi–Kovács–Altenkirch on
  shallow embeddings being morally correct; Christiansen–Brady, *Elaborator reflection* (ICFP 2016).
- Program logics for metaprogramming: Berger–Tratt, *Program logics for homogeneous generative
  run-time meta-programming* (LMCS 2015); Berger–Tratt–Urban on the same for MetaML-style `run`.
- Content addressing and quotation under laziness: Maziarz–Ellis–Lawrence–Fitzgibbon–Peyton Jones,
  *Hashing modulo alpha-equivalence* (PLDI 2021); the Lurk audit (in paperbin: `audit-inference-lurk.pdf`);
  Barendregt on quote and the loss of β-equivalence; Jay's pattern calculus / factorisation calculus
  (intensional computation) if it bears.
- Boundaries: New–Ahmed, *Graduality from embedding-projection pairs* (Astra fetched);
  Perconti–Ahmed open-compiler multi-language semantics (fetched); Patterson–Ahmed linking types.
- Mirrors: Bracha–Ungar, *Mirrors: design principles for meta-level facilities of object-oriented
  programming languages* (OOPSLA 2004).

Add anything else you find load-bearing; say what you added and why.

## What to write

`/Users/ember/dev/obend/review/QUOTE-ORIENTATION-20261101.md`, with claims tagged READ, INFERRED,
PROPOSED:

1. **The properties.** One paragraph per formal property the literature isolated, with the paper that
   isolated it and the construction that secures it: well-typedness of quoted code (typed quotation);
   hygiene under nested generators; no scope extrusion (classifiers, CMTT contexts); cross-stage
   persistence and what may cross; `run` safety; what quotation does to extensional equivalence
   (intensionality; why `quote` must sit at the bottom of an observer ladder and what the Gödel–Löb
   discipline says about intensional recursion); semantics preservation of staging annotations
   (erasure; let-insertion); pattern matching on code without breaking the above (Mœbius, Scala 3);
   verified quote/unquote round trips (MetaCoq, Devriese–Piessens); reflection as capability (mirrors);
   boundaries as EP pairs with graduality.
2. **Each property against Core4 as it is.** For each: what in our calculus already secures it
   (`Scoped 0` fillings, `calculus_typed_msubst`, the observer table, `Ahead`), what threatens it (the
   lazy heap with sharing and blackholes; `perform` and yields; uses vectors and affine binders at a
   splice; laws judged on every write; content addressing by `Digest`; `hole n σ` as CMTT), and what
   theorem would secure it here, with its statement sketched in Lean-shaped prose.
3. **The design.** `quote` as a library over typed represented syntax first (Astra's order): the
   representation (`Code (stage, theory, Γ, A, usage, observers)` or what the literature says it should
   be), the checked importer, `splice` as checked contextual substitution, the observer ladder with
   `≈q`, `rewrite_sound_below`, mirrors as the capability discipline; then the promotion criterion: the
   erasure and preservation theorems that must exist before `quote` enters `Term`, and what changes in
   `Machine`, `Check`, `Equiv` and `Law` when it does. Say where the lazy heap and yields force a
   different construction than the CBV literature gives, and what Tan–Wei's result does and does not
   transfer.
4. **The theorem list**, numbered, each with its property, its shape and its tooth, in the order a
   lane should prove them; and the first lane's scope, briefable from your text.
5. **What you refuse**, with the paper's own words where a construction is known to break under
   laziness, effects or resources.

Commit the file alone on `dev` with `git -c commit.gpgsign=false commit -F -` and trailer
`Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`, rebase before pushing; a Lean lane is live
under `lean/` in a worktree, touch nothing there. Ember's safety paragraph, verbatim: "Never kill by
pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you
started is stopped by the PID in its PID file, and only that. Every detached job writes one
(`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop
writing to it, tell Ember, wait. Reply with the commit hash, the papers you could not get, and the
one property you think we are most likely to get wrong.
