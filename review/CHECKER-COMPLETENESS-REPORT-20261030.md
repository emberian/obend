# The checker is provably incomplete for its own declarative typing: the problem, as we understand it

Written 2026-10-30 for outside analysis. Everything below is about code at
github.com/emberian/obend, branch `dev`, directory `lean/Obend`, Lean 4.30.0. File and theorem
names are real and can be checked.

**1. The system and the two judgments.** Objective Bend is a language of partial specifications in
the sense of Rideau's *Lambda, the Ultimate Object*: lazy open recursion (`mix`, `fix`) over
first-class specifications, with a reflective prototype pairing a specification with its target.
Its core calculus, Core4, is a small untyped term language (de Bruijn `bound`, `lam`, `app`, `mix`,
`fix`, records with `extend`/`get`, sums with `inject`/`case`, Nat/Bool/label scalars, strict
primitives, and `perform`/`done` for activities that yield typed plans to a host) with a call-by-name
reference semantics and a call-by-need demand machine proved equal to it. On top sit two typing
judgments. The declarative one is `PartialTyping assumptions context term type uses` (file
`Obend/Core/Check.lean`, line 183): an inductive relation with the usual rules plus three features
that matter here. Lambdas are typed against an *existential* annotation (domain, codomain, a
quantity `erased | affine | linear | unrestricted`, and a reuse flag), so the relation says "there is
some annotation under which the body types." A `conversion` rule lets any derivation retype a term
to a `sameType`-equal type, where `sameType` is type equality up to one bounded head unfolding of an
alias variable (a bounded-variable row that may be rigid, for templates typed once against a lower
bound). Record selection and extension use a fuel-indexed `lookup`/`isRow` on row types. The
judgment also carries a *uses vector*: a count per context slot, with `safeUses` enforcing at most
one use for affine and linear binders and `reusableAllowed` governing which captures a reusable
closure may hold. The procedural judgment is `check : AnnotatedTerm → Context → Nat → Option Checked`
(line 622), an annotation-directed `infer` over fuel that returns a *proof-producing certificate*
`Checked` whose field `derivation : PartialTyping …` is the declarative derivation. Soundness is by
construction. The question is completeness.

**2. What is proved.** Three results frame the problem. (a) `check_msubst`
(`Core/Proofs/Substitution.lean`): if a term checks at fuel n and each closed filling checks at
fuel m at its hypothesis's type, the substituted term checks at fuel n+m, with the uses vector
pointwise no larger. Fuel is additive, and `fuel_tooth` shows the sum is needed. (b)
`calculus_typed_msubst` (`Obend/Slot/Core4.lean`): the same substitution law stated over
`Typed := ∃ c : Checked …`, with no fuel at all. So *meaning* has a clean substitution lemma and the
*procedure* has a graded one. (c) `Core/Proofs/CheckCompletenessObstruction.lean` proves that
completeness of the procedure for the meaning is false, not merely fuel-bounded:
`checked_does_not_imply_eventual_success : ¬ ∀ source context, Nonempty (Checked source context) → ∃
fuel, (check source context fuel).isSome`. The counterexamples are of three independent kinds. First,
a closed lambda with no annotation (`λ. 0`) has a declarative derivation at `Nat → Nat` but is refused
at every fuel, because `infer` reads the lambda's type from the annotation table and never infers
one. Second, and this is the one that bites, a lambda whose annotation is *exactly right* is still
refused at every fuel (`correct_lambda_annotation_still_incomplete`): the body is `if true then x
else 0` where `x : α` for an alias variable `α := Nat`; declaratively the branch types agree by one
`conversion`, but `infer` compares the two branch types by exact canonical equality and never
inserts the conversion. Third, an empty `case` has a declarative eliminator at any result type, but
the algorithm refuses an empty arm list because it has no result type to infer; and duplicate labels
in rows behave differently under the two judgments. The library's slot layer therefore carries an
explicit coverage premise: `Decides.check_complete : Typed Ψ t A → Covered Ψ t A → ∃ r, check r Ψ t A
= true` with `check_covered` the converse, where the Core4 instance defines `Covered` as "there
exists a fuel at which `check` succeeds" (named `Recognized`). That is honest and useless: it does not
characterize the recognized fragment independently of running the checker.

**3. Why it matters here more than in a compiler.** In this system the checker is not a development
tool; it is the *admission judge*. Objects live in a shared world where every write is admitted by
re-executing the same Lean checker and machine on every member's node; a filling for a *slot* (a
deferred decision whose candidates are posted by other members and justified by supports such as
"this grant is live at this version") is admitted iff `check` accepts it at the budget the world
declared. Two consequences follow. A stranger's filling that is semantically well typed can be refused
with no repair available to them except guessing which conversion the algorithm wanted, which
contradicts the project's rule that every refusal names what would pass. And the substitution lemma
the slot theory needs is the one on `Typed`, but the law the kernel actually enforces is the one on
`check`, so the gap between them is exactly the set of programs the kernel will refuse that the
semantics accepts, and today that set has no description. The system's other rule, "resources are not
meanings" (fuel, ticks and heap are declared budgets whose exhaustion is a named refusal), has been
honoured: Astra's rework made the budget a support that can fail by name (`uncovered`). The remaining
gap is not about fuel. More fuel cannot fix any of the three counterexamples; they are refused at
every fuel.

**4. What we think the shape of the right answer is.** We want to keep `PartialTyping` as the
semantic contract (it is what the metatheory is proved against) and make the procedure complete for a
fragment we can *state*, with a proof of completeness for that fragment and a decision procedure for
membership in it. The obvious design is a genuinely bidirectional checker: inference mode for
elimination forms and variables, checking mode for introduction forms against an expected type, with
`conversion` applied at the mode switch (the standard Pierce–Turner / Dunfield–Krishnaswami
discipline). That alone repairs the second counterexample (the branches are *checked* against the
expected type, so the alias unfolds) and the third (the empty case is checked against the expected
result type), and it reduces the first to "every lambda not in checking position needs an
annotation," which is a statable fragment. Our worry is the parts of the judgment that are not
standard: the uses vectors (linear/affine accounting is a resource constraint, and bidirectional
typing does not by itself tell you how to split uses between a function and its argument when the
annotation is absent); the bounded alias unfolding and rigid row variables (a limited form of
subtyping/recursive types where "one head unfolding" is a deliberate bound and an equivalence
checker would need to decide equality of bounded recursive row types); and the fuel-indexed
`lookup`/`isRow` on rows, which exists because rows may be recursive sums and the checker is
structurally recursive on fuel rather than on a well-founded measure.

**5. Where solvers and automated reasoning might enter.** If the goal is "complete for all of
`PartialTyping`" rather than "complete for a stated fragment," the three sub-problems look like
decision problems with known tools. The quantity side is a system of linear inequalities over Nat
per binder (sum of uses across subterms ≤ 1 for affine/linear, free for unrestricted, with
`reusableAllowed` adding side conditions on captures): an ILP or an SMT query in linear integer
arithmetic, small per lambda. The conversion side, with aliases bounded to one head unfolding and
rigid variables, is a type equivalence problem over a finite algebra of records, sums, arrows and
bounded variables, plausibly decidable by a congruence closure or by E-graph-style rewriting; the
question is whether we should widen `sameType` to full equi-recursive equality (coinductive row
equality, Amadio–Cardelli) or keep the bound and decide it exactly. The inference side (missing
annotations) is higher-order unification in general, but the terms are first-order enough (no
polymorphism in Core4 beyond the template layer, which instantiates before checking) that
constraint-based type inference with unification variables for omitted annotations may be complete
for everything except reuse flags, which are a policy choice rather than a type. The architectural
constraint on any of this is the project's trust discipline: the kernel never trusts a solver. A
solver may *find* a derivation, but the thing admitted must be a certificate the small Lean checker
re-verifies, which is exactly the shape `Checked` already has (a derivation term plus decidable side
conditions). So "solver" here means certificate-producing search whose output is checked by `check`,
in the same way the system refuses to trust a proof it cannot re-run.

**6. What is already available in the tree to build with.** Lean 4.30 ships `grind` (congruence
closure plus E-matching, with linear arithmetic), `omega` (Presburger), `decide +kernel`, and a
`#tooth` command the project wrote that fails a theorem under a stated mutation. The row algebra and
the C4 linearization are already decided by `decide` on finite inputs. The journal
(`lean/Journal`) computes, for any change, the exact set of theorems whose justification is affected,
so a redesigned checker can be rolled through 1700 theorems with the repair set known in advance. The
metatheory is modular (every file a Lean 4.30 `module`; definitional modules do not see proof
bodies), so a new checker can be developed beside the old one, proven sound against the same
`PartialTyping`, and swapped in once its completeness theorem is stated. The slot layer is already
parametric over the judge through `Decides`, with the budget as a support, so a certificate-producing
search with a declared budget fits without changing the slot theorems.

**7. The questions we would like analysed.** First, is there a known complete bidirectional
discipline for a quantitative type theory with at-most-once binders and *per-closure* capture
restrictions (ours: a reusable closure may capture only unrestricted, shareable bindings) that
preserves a uses-vector accounting, or must inference of use splits go to a solver? Second, what is
the right decidable notion of type equality for records and sums with bounded alias variables where
some variables are rigid lower bounds (templates) and others are aliases, and is one head unfolding
a coherent bound or should we move to full equi-recursive equality with a coinductive decision
procedure? Third, given the kernel's requirement that admission re-execute a checker rather than
trust a solver, what is the best architecture for certificate-producing type inference (solver finds
annotations and conversion placements; the existing `check` verifies the annotated term), and what
completeness statement is achievable for it: complete for all of `PartialTyping`, or complete for a
fragment we can define syntactically? Fourth, are there precedents for exactly this situation, a
proof-producing checker with an inductive specification where completeness fails on conversion
placement and empty elimination, and how was the fragment stated there (Agda's and Lean's own
elaborators, Abel–Öhman–Vezzosi's decidability of conversion, bidirectional MLTT)? Fifth, is there a
way to state `Covered` as an independent, decidable predicate on annotated terms now, before any
redesign, so that the kernel's refusals can name the missing conversion or annotation rather than
only "typing refused"?

**8. What we would do absent better advice.** Write the bidirectional checker as a new module
beside the old one, with inference and checking modes and conversion at mode switches; keep
`PartialTyping` fixed; prove soundness by construction as now; state `Covered` syntactically as
"every lambda in inference position is annotated and every empty case is in checking position" and
prove completeness for that fragment; move the uses-vector accounting to a separate pass that
either decides the linear constraints directly (they are small) or emits them to `omega`; keep
`sameType`'s bound and decide it exactly, with a theorem that it is an equivalence; and only then
ask whether a search layer above the checker buys anything that the fragment statement did not.
Argon's view on whether that order is right, and on anything the five questions miss, is what we are
asking for.
