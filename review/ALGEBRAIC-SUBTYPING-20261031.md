# Algebraic subtyping for Objective Bend: the design

2026-10-31, Claude, on `review/ALGEBRAIC-SUBTYPING-BRIEF-20261031.md`. Tags: READ is a claim a named
source states; INFERRED is a consequence I drew from read sources or from the code; PROPOSED is a design
choice this document makes. Code claims are READ against `lean/Obend` at `9e03d9e`. Dolan's order is used
throughout: a record with more fields is the subtype, a sum with fewer labels is the subtype, `⊤` is the
largest type. Where the project's own vocabulary runs the other way ("a lower bound discloses the members
available"), the inversion is stated at the point of use.

## 0. Sources

All nine papers in the brief were read from `~/paperbin`. The three the brief could not fetch are now
there: `dolan-mycroft2017-mlsub.{pdf,txt}` (Cambridge repository bitstream),
`parreaux2020-simple-essence-algebraic-subtyping.{pdf,txt}` (EPFL Infoscience bitstream), and
`bruce2002-comparing-object-encodings.{pdf,txt}` (Pierce's PostScript, converted; it is the 1997
TACS/1999 Information and Computation version). Our side: `DESIGN.md` §2 and §4, `METATHEORY.md`,
`review/CHECKER-COMPLETENESS-REPORT-20261030.md`, `review/ARGON-RESPONSE-20261030.md`,
`lean/docs/REPORT-EQUIREC-20261031.md`, minidregg `docs/objective-bend/MODULAR-TYPING.md` and
`REFLECTION.md`, and the Lean modules `Core/Ty.lean`, `Core/Assumptions.lean`, `Core/Check.lean`,
`Core/Bidirectional.lean`, `Core/EquiRecursiveAgreement.lean`, `Core/TemplateDischarge.lean`,
`Spec/Elaborate.lean`, `Spec/Contract.lean`, `Spec/Annotated.lean`, `Slot/Core4.lean`.

One premise of the brief was not checked: that Bend copies on subtype in its leaves. Nothing below
depends on it.

## 1. Core4's type algebra on Dolan's lattice

### 1.1 What a lattice element is

READ (thesis ch. 3). Dolan's types are the initial algebra of a functor on distributive lattices,
`T = Σ_i (C_i)^⊤_⊥`, a coproduct of components, each component being a constant lattice, a finite
product, or an image under `(−)^op` and `(−)^⊤`, with one top and one bottom shared by the coproduct.
READ (thesis 3.4). Recursive types come from completing this lattice to its profinite completion,
which is simultaneously the terminal coalgebra and the metric completion, so that guarded covariant
equations have unique solutions that are least pre-fixed and greatest post-fixed points.
READ (thesis 3.2.3, Prop. 12). In the coproduct, `⊓_i τ_i ⩽ ⊔_j τ'_j` holds iff some `τ_k ⩽ τ'_k` within
one component; this is the property that makes subsumption decidable (ch. 8) and is the content of
"extensibility".
READ (thesis 5.1). Finite syntax reaches only the polar types: `⊔` in positive positions, `⊓` in negative
positions, `µ` guarded and covariant.

INFERRED. A Core4 `Ty` value denotes a *constructed* element of this lattice: an element with no `⊔`,
`⊓`, `⊤`, `⊥` at any node, that is, an element of the image of Dolan's `T_s` (the plain initial algebra of
Section 3.1) inside `T`, completed through aliases. An alias variable (an index in `Assumptions.bounds`
not in `rigid`) denotes the regular tree its unfolding describes, which is a `µ`-type; the equi-recursive
report's finite bisimulation (`Core/TypeGraph.lean`, D1) is equality of these regular trees. The image
of a canonical `Ty` is therefore exactly what Amadio–Cardelli call a ground regular type, and Dolan's
Section 10.1.2 identifies that class as the ground fragment of his own lattice.

### 1.2 Components, one per constructor

Each row gives the Core4 constructor, its component in Dolan's ingredients, and the polarity of its
arguments. "Variance" means how the component orders its arguments in the subtyping order.

- `natural`, `label`, `boolean`. Three one-point components `1^⊤_⊥`, pairwise incomparable, like
  Dolan's `bool`. READ (thesis 3.1). No order between `natural` and `label` is justified by any rule in
  `Check.lean`; `primitiveTypes` keys primitives on exact scalars. INFERRED.
- `arrow reuse quantity domain codomain`. A component `R × Q × T^op × T`, with `R` and `Q` constant
  finite lattices on `Reuse` and `Quantity`, `domain` contravariant, `codomain` covariant. Finite constant
  lattices as factors of a component are among Dolan's ingredients (thesis ch. 9 opening). READ. The
  orders on `R` and `Q` are not Dolan's business; they are fixed in §5 from what the checker admits.
  PROPOSED.
- `emptyRow`, `field name member tail`. Records: `(T^⊤)^L`, the top of `T^⊤` meaning "label absent", so a
  record lacking a label is above one having it; depth covariant. READ (thesis 3.1.2, 9.2). Core4 rows
  are ordered lists with repeated labels and a canonical form (`Ty.canonical`, `insertCanonical`) that
  sorts labels and keeps a shadowed member only when it is not shareable. READ (`Core/Ty.lean`). The
  image of a row is the partial function `label ↦ first member` only when the row has no retained
  non-shareable shadow; a row with a retained shadow has no image in `(T^⊤)^L` (see 1.4). INFERRED.
- A row whose tail is a rigid variable (`Self`, `Super`) is an open row. Dolan has no row variables;
  his Section 9.2.2 adds presence as a second kind `P` and remarks that "the algorithms previously
  presented require almost no changes to cope with a new kind". READ. Rémy's row variable is the
  construction Tang et al. study; §4 takes the open tail as a row-kinded variable in a two-kinded
  version of Dolan's construction. PROPOSED.
- `variant row`. Sums: `(T_⊥)^L`, the bottom of `T_⊥` meaning "label absent", so a sum with fewer labels
  is below one with more; payloads covariant. READ (thesis 9.2). A variant whose row tail is an alias is
  a recursive sum, an ordinary `µ`. INFERRED.
- `specification metadata extension`, `prototype specification target`. Covariant pairs `T × T`. Nothing
  in Dolan; a product is an allowed ingredient. INFERRED. The checker never coerces a specification's
  `self` component: `mix` demands `self' = self` syntactically and `fix` demands `output = target`
  (`Bidirectional.lean`, `.mix` case `hs : self' = self`, `.fix` case `ho : output = target`). READ. So
  within a `fix` chain the `self` argument of every layer is invariant by construction, and only the
  inherited and provided rows carry an order.
- `custody identity`. One one-point component per identity, mutually incomparable, like MLstruct's
  nominal tags `#C` without inheritance. READ (MLstruct 2.2.2 for the tag idea). INFERRED for us.
- `computation plan response result`. `T × T^op × T`: `plan` is what the activity yields (covariant),
  `response` is what the host sends back (contravariant), `result` covariant. INFERRED from the
  `perform` and `effectCase` rules. The `perform` rule types a yield at `computation planType response
  response`, so at that constructor the same type occurs in both polarities; Dolan's remedy for an
  invariant parameter is to split it into a contravariant and a covariant copy (thesis 9.1.1). READ.
  §3.5 does not coerce activities at all, so no split is needed in this edition. PROPOSED.
- `variable k` with `k ∈ rigid`. A lattice variable in Dolan's sense (an indeterminate, thesis 3.3),
  with one *upper* bound in Dolan's order: `Self ⩽ R_S`, read "every instance has at least the members of
  `R_S`". The project calls the same fact a lower bound (`MODULAR-TYPING.md` D2, `Assumptions.rigid`
  docstring). READ both. The inversion is only vocabulary, but it matters when reading the brief's
  claim (1), see §2.
- `variable k` with `k ∉ rigid`. Not a lattice element of its own; it is a `µ`-binder (1.1).

### 1.3 What polarity means for us

READ (thesis 5.1, MLsub 2017 §3.3). A positive type describes an output and may contain `⊔` and `⊥`; a
negative type describes an input and may contain `⊓` and `⊤`; a variable has positive and negative
occurrences, and a typing scheme's variables are nothing but labels for flow edges from negative to
positive occurrences (thesis 7.3, Theorem 75).

INFERRED, applied to a template `λself. λsuper. extend super {m_i = e_i}` (`Elaborate.layerAt`):
`self` and `super` are λ-bound, so their types are negative; every `self.m` read puts a record
constraint on the negative occurrence of `Self`; the provided row is positive; a method result `-> Self`
is a positive occurrence of `Self`; a method parameter `other: Self` is a negative occurrence of `Self`
inside the positive provided row. The knot at `fix` adds the constraint `provided ⩽ Self`, which is the
only place a positive occurrence of the provided row flows into the negative `Self`. This is
Canning–Cook's F-bound `t ⩽ F[t]` written as a flow edge. READ (Canning 1989 §4; Cook–Hill–Canning 1990
§3.2) for the F-bound; the identification with the `fix` constraint is INFERRED.

### 1.4 What has no image

- `Assumptions.shareableVariables`, `Assumptions.rigid` as a list, `Assumptions.valid`. These are
  side conditions on environments, not elements.
- `Uses` vectors, `Binding.quantity`, `safeUses`, `reusableCaptures`, `argumentAllowed`. Resource
  accounting is not in the lattice. Dolan's effect-system remark (thesis 9.4) is about tracking effects
  as a kind, not about counting uses, and SuperF and MLstruct have no linearity. INFERRED.
- A row with a retained non-shareable shadow (`{a : Bool, a : Custody}` keeps both; D2 of the
  equi-recursive report). Dolan's records are partial functions from labels, so there is no element for
  "the first `a` is a `Bool` and a `Custody` is hidden behind it". READ (thesis 3.1 defines records as
  partial functions). The representation Astra built (ordered resourceful shadow streams) is a strict
  extension of the record component; §4 says why it must stay outside the subtyping order.
- `hole n σ`. No typing rule; no element.
- An alias-only cycle (`α := α`). Dolan excludes unguarded `µ` (thesis 5.1); the equi-recursive report
  gives it its own nominal class (D1, D5). The template elaborator must refuse such a bound rather than
  embed it. PROPOSED.
- `computation` beyond equality. There is no coercion term for an activity (§3.5), so the component is
  present but no proper subtyping inside it is ever used.

## 2. The first read, checked

(1) "A template's rigid `Self ≥ ρ` is an MLsub variable with a lower bound from the provided methods and
upper bounds from each `self.m` use, so biunification infers the principal mixin type with no written
bound." Three corrections.

- Direction. In Dolan's order the `self.m` uses give `Self` an upper bound (a record with those
  members) and the provided row gives it a lower bound only at `fix`, through the knot. In the
  template itself the provided row does not bound `Self` at all: `layerAt` types `self : target` and
  returns `provided` separately, and the knot is tied by `chainFix` through `Contract.close` (final row
  equals the self) and the `fix` rule's `output = target`. READ (`Elaborate.lean` 1045–1056, 1140–1143,
  1203–1213). So the one MLsub variable is bounded above by the reads and below by nothing until the
  instance is closed.
- What inference can find. Biunification infers the requirement row from the body's reads; that is
  MLsub's `λx. x.foo` and it is complete for it (thesis 6.2.2, MLsub 2017 §4). READ. It cannot find an
  F-bound such as `heavier(other: Self) -> Self` from a body: the body of `heavier` reads `other.weight`
  and so infers `other : {weight : Nat}`, a structural type, never "the final self". MLsub's inferred
  type of such a binary method is `{weight : Nat} → (Self ⊔ {weight : Nat})`, which accepts any record
  with a `weight`. INFERRED from MLsub's rules; this is Cook–Hill–Canning's point that a binary method's
  parameter type is a design choice, not a consequence of the body (1990 §6, `ColorPoint`). READ. The
  declared bound is also the contract other layers read (`Contract.assumes`, the `requires` lines, D4
  of MODULAR-TYPING), and a contract is not inferred from one layer's body. So "no written bound" holds
  for the fragment of the bound that is a pure read requirement, and fails for F-bounds and for
  `requires`.
- `extend` on an abstract `Super` is outside MLsub's polar syntax. The provided row
  `overlay defs Super` is a record intersection in a positive position, which polar types forbid
  (thesis 5.1); MLstruct allows positive intersections but merges same-label members by `∧`
  (`{x : τ} ∧ {x : π} ⩽ {x : τ ∧ π}`, MLstruct 2.2.2), which is not first-wins overriding; and MLstruct
  itself says ad-hoc field extension needs row variables (MLstruct §6, "Polymorphic records/variants").
  READ. So the provided side of a template needs a row kind, which is Rémy, not Dolan; §3.2 keeps the
  `Contract` for it.

(2) "Our finite-bisimulation equality is Dolan's automaton representation minus the subsumption
direction." Partly. What is shared is the visited-pair memoisation, which Dolan attributes to Kozen,
Palsberg and Schwartzbach (thesis 5.3.3) and which `Core/FiniteBisimulation.lean` implements. READ. What
is absent is the lattice: Dolan's automata carry head-constructor *sets* per state, `ε`-edges for `⊔`
and `⊓`, polarity on states, and flow edges for variables, and his representation theorem is about
regular *languages* in a Kleene algebra of type pairs (thesis 7.2). Ours is a deterministic constructor
graph with no `⊔`, no `⊓`, no polarity and no variables, whose bisimulation is Amadio–Cardelli equality,
which Dolan lists as the ground fragment (thesis 10.1.2). READ. The subsumption direction is the least
of what is missing; the reduced-form (subset-construction) step and Prop. 12 are what would have to be
added, and they only make sense once `⊔`/`⊓` exist. INFERRED.

(3) "Biunification is the constructive elaborator our `annotateFromDerivation` lacks." Half. For the
template fragment, yes: §3 makes annotation discovery executable there. For closed Core4 fillings
(the slot judge's input, `Slot/Core4.lean`), no: Core4's declarative typing has no subtyping rule, its
`get` already looks fields up through wider rows, and every other position is exact (`argumentType =
domain`, `output = target` at `fix`). READ. Biunification on an equality system degenerates to
unification (thesis 5.3.3 says deleting the record, subtyping and recursive cases recovers Martelli–
Montanari); what a filling needs is regular-tree unification plus the bidirectional propagation already
in `checkAgainst`. INFERRED. And `annotateFromDerivation` is `Classical.choose (full_annotated c)`, a
noncomputable witness of an existence theorem, not an algorithm with a gap; the executable replacement
for the template fragment is stated in §3.6.

(4) "The kernel keeps equality and re-checks certificates; subtyping belongs in the elaborator with
explicit coercions emitted into Core4." Agreed, and it is the project's own two-tier rule
(`ARGON-RESPONSE` item 7). Two qualifications. A coercion changes the erased term, so it is not a
`Reannotates` preparation (`Slot/Core4.lean`: `source.term = target.term`); coercions therefore belong
in the elaborator's own output (templates, chains), which the checker checks as a whole program, and
never in the slot judge's `Prepares`. INFERRED. And coercions are terms with uses and ticks, so they
are seen by the resource discipline and by the budget; §5 is about the first and §3.7 about the second.

(5) "Quantities are orthogonal but unexamined." Not orthogonal. §5 gives the cases.

(6) "Scoped rows with duplicate labels carry field provenance that width subtyping forgets, and C4 and
reflection care about that." The retained shadows carry *resource obligations*, not provenance: a
shadowed member is kept iff it is not shareable (`insertCanonical`), and D2 of the equi-recursive
report says why ("blindly dropping every shadow would lose custody and once-closure obligations").
READ. C4 orders *declaration keys* (`Spec/C4.lean`), and the contract compares rows by name with
first-wins (`Contract.get?`), neither reading the hidden stream. READ. Reflection observes `SpecMeta`,
a first-order value of names, interfaces and law statuses, and never a row type (`REFLECTION.md`,
observer table). READ. Provenance of a member lives in the knot field names `M.m@k` and in
`SpecMeta.composed`, outside the type. So what width subtyping endangers is custody and once closures,
and that is a §5 matter, not a C4 or reflection one.

## 3. The template elaborator by biunification

### 3.1 Which algorithm

PROPOSED. Use Parreaux's Simple-sub formulation (bounds attached to variables, `constrain` with a
cache, extrusion by levels) rather than Dolan's syntactic biunification or his automata. READ
(Parreaux 2020 §3, §5; Parreaux shows agreement with MLsub on 1.3 million terms, §6). MLstruct §3.1
restates the same core and calls it the basis of its inference. READ. The reasons are concrete: the
bounds form keeps the inferred requirement row as a plain record of bounds, which is what the
`Contract` consumes; the cache is the same visited-pair discipline the kernel already proves
terminating; and Dolan's automata are needed only for simplification and for the subsumption check,
where MLstruct's skolemisation (§3.3) does the same job without a second representation.

### 3.2 Reads by inference, writes by contract

PROPOSED. The body of an open declaration is typed by Simple-sub over Core4 heads (the components of
§1.2) with `self` and `super` at fresh variables. The upper bounds collected on `self` form the
inferred requirement row `R_S^inf`, those on `super` form `R_I^inf`. These replace the two READ clauses
of `Contract.checkBounds` (`assumes`, `consumes`) as the *inferred* reads. The WRITE clause
(`checkProvides`, `F_L(S, I) = provides ++ I`) is unchanged, because record extension over an abstract
row is a row-kind operation that no polar type expresses (§2, item 1). Dolan's own extension to a second
kind (thesis 9.2.2) is the licence to run biunification on `T` while rows are handled by `Row`-kinded
reasoning; Pottier's remark that row polymorphism and subtyping complement each other, cited by both
Parreaux papers, is the same point. READ.

### 3.3 Declared bounds stay, checked by subsumption

PROPOSED. The declared bound (`Self has {...}`, `requires`, `Super has {...}`) remains the interface.
Declaration-time checking becomes: infer the scheme `Σ = [self : s⁻, super : i⁻] p⁺` and decide
`Σ ⩽∀ [self : B_S, super : B_I] P_decl`. READ (thesis ch. 8; MLsub 2017 §1.1 says subsumption is
decidable only because of the algebraic construction). The algorithm: instantiate the left scheme's
variables fresh, make the right side's variables rigid nominal tags, run `constrain` (MLstruct §3.3).
READ. A refusal names the first failing pair of heads and the path (MLstruct's constraining is
deterministic and returns `err` with the pair; the current `self-unbound-member` and
`inherited-unprovided` refusals become instances of it). INFERRED.

Consequences for the surface, all INFERRED from §2 item 1:

- `requires m(...)` lines for members the body only reads become optional; the inferred row supplies
  them and the subsumption check shows them. A `requires` the body never touches stays written, since it
  is a promise to later layers.
- An F-bound (`Self` negative in a signature) stays written. The check `Σ ⩽∀ declared` then compares
  the inferred `other : {weight : Nat}` against the declared `other : Self`; the declared is the
  subtype of the inferred (a `Self` has at least `weight`), so the declared signature is an instance and
  the check passes. This is exactly Cook's `G[t] ⩽ F[t]` (1990 §3.2) read as a subsumption.
- Cook's "inheritance is not subtyping" is reproduced, not escaped: two instances of one template at
  different selves are not subtypes of each other when `Self` occurs negatively in the provided row.
  READ (Cook 1990 §5; Bruce–Cardelli–Pierce §4.7, "`I <: J` implies `OR(I) <: OR(J)` only when `J` is
  covariant"). Our objects are `fix` over a method suite taking `self`, which is the `OR` encoding with
  an explicit self parameter; Bruce et al. say binary methods are "built in" for that encoding at the
  price of subtyping between object types, and name the alternative "matching". READ. The template
  discipline (one check, instantiate per `fix`) is matching.

### 3.4 Instances

PROPOSED. At `chainFix`, for each open layer at `σ = {Self ↦ T, Super ↦ I_{k-1}}`, decide
`Σ ⩽∀ [self : T, super : I_{k-1}] P[σ]` by the same algorithm; the scheme is computed once and each
instance is one constraining run, which is cheaper than re-elaborating the layer. Then emit
`ATerm.instantiate σ template` as today (`Elaborate.lean` 1164–1166), followed by the coercion pass of
§3.5. `Contract.checkProvides` and `Contract.close` run unchanged. The whole closed program is then
checked by `Bidirectional.checkAgainst`, as MODULAR-TYPING §6 already requires.

### 3.5 The coercion grammar

PROPOSED. Placement: one coercion at each hypothesis of an elimination form where the flowing type is
a strict subtype of the position's type, and none at the conclusion. This is the normalised derivation
Dolan uses in the preservation proof and in principality ("(Sub) is applied exactly once to the
hypotheses", thesis 4.1.4, 6.1.1). READ. With one placement there is one elaboration, which is what
Dolan asks of implicit subtyping in 2.3.3 ("between two types there should not be a choice of possible
subtyping routes") and what Canning et al. could not verify for their coercion translation (1989 §5,
"coherence is a difficult technical property"). READ.

In Core4 the positions with an exact expected type are: the argument of `app` (`argumentType =
domain`), the fields of a `record` or `extend` checked against an annotated row, the seed of `fix`
(`argumentAllowed ... inherited`), and the final `output = target` of `fix`. READ (`Check.lean`
`PartialTyping`). `get` needs no coercion because `lookup` walks a wider row. READ. Within a template
instance three of these arise: a method body whose inferred result is a strict subtype of its declared
signature (`layerAt` annotates each method with `method.resultType`), a self-method applied to an
argument whose inferred domain is narrower than the argument's type, and the `fix` seed, which is
coerced to the row of `T` whose labels no layer provides. INFERRED.

`coerce : Ty → Ty → Except CoercionRefusal ATerm`, defined on `A ⩽ B` decided by `constrain`:

- identity: `sameType A B` gives no term; the derivation is a `conversion`.
- record: for `A = {ℓ_i : A_i, ...}`, `B = {ℓ_j : B_j}` with `labels(B) ⊆ labels(A)`,
  `λx. record [(ℓ_j, coerce A_j B_j (get x ℓ_j))]`. Tang et al. §4.3 give this as the η-expansion
  translation and note it copies the receiver once per kept field. READ. The binder `x` is used
  `|labels(B)|` times, so for two or more kept fields the parameter must be `unrestricted`, which
  demands `A` shareable (`validContext`). READ (`Ty.lean`, `Check.lean`). Refusal
  `coercionNeedsSharing path` otherwise.
- variant: for `A = variant R_A`, `B = variant R_B` with `labels(A) ⊆ labels(B)`,
  `λx. case x [(ℓ, inject ℓ (coerce A_ℓ B_ℓ (bound 0)))]` with each `inject` annotated at `B`. Tang
  et al. §4.1. READ. The scrutinee is used once and arm payloads are already required shareable
  (`ArmsTyping.cons`), so this always types. READ.
- arrow: `λf. λx. coerce C C' (app f (coerce D' D x))` for `arrow r q D C ⩽ arrow r' q' D' C'`;
  admissible `(r, q) ⩽ (r', q')` is fixed in §5.
- specification: `λs. specification (metadata s) (λself. λsuper. coerce P P' (app (app s self) super))`,
  keeping the metadata value, so `≈r` (reflective equivalence) is undisturbed; the `self` component is
  never coerced (§1.2). Only needed for `compose` of closed specs whose middle rows mismatch
  (`inherited-mismatch` today); not used by `chainFix`.
- prototype: `λp. prototype (coerce (reflect p)) (coerce (project p))`, two uses of `p`, so `p` must
  be shareable; `prototype` is shareable iff both parts are. READ (`Ty.shareable`).
- recursive coercions (two aliases whose unfoldings are in the order but not equal) are refused by
  name in this edition: a recursive coercion needs a recursive function, which in Core4 is a `fix`
  over a specification or the demand machine, and neither is justified for a type-directed wrapper.
  PROPOSED.
- `computation`, `custody`, scalars: identity only.

### 3.6 The theorems

PROPOSED, with the shapes they must have.

- `inferTemplate : Term → Bounds → Except Refusal Scheme` (Simple-sub over Core4 heads),
  `subsumes : Scheme → Instance → Bool` (skolemised constraining),
  `readback : Scheme → Instance → Term → AnnotatedTerm` (annotations from the scheme's negative
  coalescence at the instance, coercions from §3.5).
- Soundness, the theorem the brief asks for:
  `readback_checks : inferTemplate b B = .ok Σ → subsumes Σ σ = true →
   ∃ c, Bidirectional.checkAgainst (readback Σ σ b) [] (σ.self ⇒ σ.super ⇒ σ.provided) = .ok c`.
  Its proof is by induction on the Simple-sub run, using Parreaux's Lemma 2 (consistent bounds give
  subtypes under coalescence) at each constraint, with each subtyping step discharged by the coercion
  of §3.5 whose own typing lemma `coerce_checks : coerce A B = .ok t → checkAgainst t [] (A ⇒ B) = .ok _`
  is proved once per constructor. READ for Parreaux's lemma; the assembly is PROPOSED.
- Completeness on the fragment: for a template body `b` in the fragment that embeds into MLsub
  (`lam`, `app`, `record`, `get`, `extend` with a row-kinded tail, `ifBool`, scalars, `binary`), if some
  annotation map makes `instantiate σ b` check, then `inferTemplate b B` succeeds and `subsumes Σ σ`
  holds. This is Dolan's principality (thesis Prop. 66; MLsub 2017 Theorems 8 and 9 for biunification;
  Parreaux 2020 Theorem 2 for Simple-sub) transported through the observation that every
  `PartialTyping` derivation on this fragment is an MLsub derivation whose `(Sub)` steps are all
  reflexive or lookups. INFERRED.
- Relation to the existing completeness: `full_annotated` and `annotateFromDerivation` are about all
  of `PartialTyping` and are noncomputable; `readback` is a computable witness on the template fragment.
  Nothing in `Core` changes; `Decides` and the slot judge are untouched.

### 3.7 Costs that become visible

INFERRED. A coercion is a term, so it has ticks on the demand machine and a depth under the judge's
grant (`termDepth`). `REFLECTION.md` says resource observations under a budget distinguish programs
that agree on completed runs; an elaborator that inserts coercions therefore changes what a member is
charged for. The refusal that names a budget must be able to name the coercion
(`uncovered` at the path of the coercion), which is a small addition to the diagnostics and not to the
metatheory.

## 4. Rows versus width

### 4.1 What Tang et al. prove

READ (Tang 2023). Simple record subtyping has a local type-only encoding in presence polymorphism
(§4.4) and none in row polymorphism (Theorem 4.9, §4.5). Strictly covariant record subtyping has a
global type-only encoding in presence polymorphism by hoisting quantifiers (§5.2). Full record
subtyping has no type-only encoding in row-plus-presence polymorphism (Theorem 5.4). Strictly
covariant *variant* subtyping has none either (Theorem 5.3), because a case split needs a monomorphic
scrutinee. With rank-1 polymorphism and inference, erasure encodes full record subtyping for terms
whose types have rank-2 records (§6, Theorem 6.2, weak type preservation), and the restriction is
necessary: `id` and `const` at `⟨ℓ : Int⟩ → ⟨ℓ : Int⟩` get different row-polymorphic types and no
parameter type unifies with both (§6 end). Their §7.2 conclusion: "Row polymorphism simply is not
expressive enough to give a local encoding of unrestricted structural subtyping".

### 4.2 Where we already are

INFERRED. The template discipline is Tang's §6 regime: rigid `Self` and `Super` are row-kinded
variables of rank 1, generalised once at the declaration and instantiated at every `fix`
(`ATerm.instantiate σ`). MODULAR-TYPING D1's stated cost, "an open template is second-class (a parameter
can be any closed `Extension<T>`, not 'any extension over `Self has {x}`')", is Tang's `℧₂` restriction:
a template may not take a record-manipulating function over `Self` as a parameter and use it at two
widths. The two limits are the same theorem. Within that limit the current rows-only design is
complete for what width subtyping would give, by Theorem 6.2.

### 4.3 What C4 needs

READ. C4 orders declaration keys and the contract compares members by name and exact canonical type
(`Contract.replaced` refuses a type change; MODULAR-TYPING §6 "a type change is `replace-undeclared`").
Width subtyping does not touch the order. Depth subtyping on an override would admit Cook's type
inheritance (`G[t] = F[t] + R[t]` with changed member types, 1990 §5), which is what makes an inherited
type fail to be a subtype; the contract's refusal is the choice that keeps every `I_k` an exact row and
the `fix` close an equality. Cook also notes that record combination with first-wins is unsound under
subsumption because hidden fields of the overriding record would win (1990 §2.3). READ. Our `overlay`
puts the layer's own literal fields first, so hidden fields can only be in the inherited row, where they
are shadowed; the hazard does not arise. INFERRED.

### 4.4 What reflection needs

READ. Nothing from row types (§2, item 6). The one reflection constraint on coercions is that a
specification coercion preserve `metadata`, which §3.5 does.

### 4.5 The decision

PROPOSED. Rows remain the mechanism of the template fragment: `Self` and `Super` as row-kinded
variables, requirement rows inferred (§3.2), declared bounds checked by subsumption (§3.3), instances by
`instantiate σ`. Width subtyping enters only as elaborator-emitted coercions at the exact positions
listed in §3.5, and in the first edition at exactly three sites: a method result against its declared
signature, method arguments inside a template body whose inferred domain is narrower than the supplied
type, and the `fix` seed, where it turns `seedExtra` from a refusal into a coercion to the row of `T`
that no layer provides, for seeds whose extra members are shareable (the `fix` rule already demands the
seed be shareable, so this is every admissible seed). READ for the `fix` premise.
Subtyping never enters `Contract.replaced`, never enters `Core`, and never applies to objects of
templates with a negative `Self`, where Bruce–Cardelli–Pierce §4.7 says it cannot hold.

What this buys that rows alone cannot: Tang's Theorem 5.4 cases, which in our setting are a self-method
called on two differently wide arguments through one binder, and the seed. What it does not attempt:
lifting `℧₂` (a template parameterised by an open extension). SuperF shows how that could be done
later without higher-rank rows: never infer a polymorphic type for a parameter, infer an intersection
of its uses and let subtyping at the call site do the rest (SuperF §2.2, §2.4; its §2.7 `fooLet` is the
limit). READ. That is a later edition.

## 5. Quantities and reuse: open, with the cases

The brief calls quantities orthogonal. They are not, because every coercion of §3.5 is a term whose
binders have quantities and whose body has a uses vector.

### 5.1 The orders the checker actually admits

INFERRED from `PartialTyping.lambda`, `application`, `argumentAllowed`, `reusableAllowed`,
`validContext`, `safeQuantity`, by typing the η-wrapper `λ(x : D', q'). app f (coerce D' D x)` with
reuse `r'` against `f : arrow r q D C`:

- `q' = erased` is never a coercion target, because the wrapper mentions `x` and `safeQuantity .erased`
  demands zero uses. Only the identity relates `erased` to anything.
- `q = unrestricted` forces `q' = unrestricted`: `argumentAllowed .unrestricted` requires
  `reusableCaptures` of the argument's uses, and the argument uses `x`, so `x` must be an unrestricted
  shareable binder.
- `q ∈ {erased, affine, linear}` allows any `q' ∈ {affine, linear, unrestricted}`.
- `affine` and `linear` are interchangeable under coercion, because `safeQuantity` treats both as
  "at most once"; `Quantity.fits` (exactly once for `linear`) is only used in `CheckTeeth`. READ. So a
  coercion wrapper can relabel a `linear` parameter as `affine` or back, and the terminal-ownership
  protocol that is "checked separately" (`safeQuantity` docstring) would see the relabelled quantity,
  not the original. This is the first case that worries me.
- `r' = reusable` forces `r = reusable` and `f` bound unrestricted: `reusableAllowed` requires every
  used capture to be unrestricted and shareable, and an `arrow` is shareable iff `reusable`. So
  `reusable ⩽ once` and not conversely. `Reuse` is a two-point chain.

So the `Q` factor of the arrow component is not the five-point lattice one would guess from "promises"
but `erased` (isolated), `affine ≡ linear`, `unrestricted` above them, with `erased` reachable only by
identity. Whether that is the order we want, or whether the exact-discharge semantics should be made
part of the checker so that `linear` separates, is open and must be decided before `Coerce.lean` picks
its table.

### 5.2 Dropping is not free

INFERRED. A record coercion drops the labels of `A` not in `B`. The checker permits dropping any binder
with zero uses, including an affine or linear one (`safeQuantity` is at most once), and a `custody` is
not shareable but is droppable. So the width coercion `{handle : Custody, tag : Nat, extra : once
closure} ⩽ {handle : Custody}` type-checks with one kept field and an `affine` parameter, and silently
discards `extra`. The `fix` seed cannot carry such a row (it must be shareable), so the site is a method
argument: a template whose method reads only `h.handle` infers `h : {handle : Custody}` and accepts an
argument with a once closure in another field, which the coercion forgets. The checker's own canonical
form refuses to forget such a member (`insertCanonical` keeps non-shareable shadows), so the elaborator
would be undoing a discipline the kernel keeps. This is the second case.

### 5.3 Keeping is not free either

INFERRED. With two or more kept fields the coercion's binder is used twice, so the source row must be
shareable. A row with a `custody` member therefore cannot be width-coerced at all when more than one
field is kept, although `constrain` will have said `A ⩽ B`. The subsumption check and the emission then
disagree, which breaks the "refusal names what would pass" rule unless the order itself is restricted.
Restricting it is not a side condition one can bolt on: "`A ⩽ B` iff `labels(B) ⊆ labels(A)` and every
dropped member is shareable" makes the record component depend on a predicate (`ResourceSemantics.
shareable`, a greatest fixed point) that is not a lattice congruence, since the join of a shareable and
a non-shareable record (the common fields) can be shareable while their meet is not. Whether to (a)
make shareability a side condition on emission and accept that `subsumes` over-approximates, or (b) split
`T` into a shareable sublattice where absence has a top and a non-shareable part where it does not,
which changes the component construction, is the open design question of this document. Until it is
decided, the elaborator refuses to coerce any row with a non-shareable member, by name.

### 5.4 Activities

READ. `argumentAllowed` refuses an activity as an argument, so no coercion term can take an activity;
`computation` stays equality-only (§1.2). An arrow whose codomain is an activity coerces on its domain
only.

## 6. Construction order and the first artefact

PROPOSED. Every module lives under `lean/Obend/Elab/`, imports `Core` and never the reverse, and is
built against the real tree, not a scratch copy.

1. `Elab/Coerce.lean`, the first artefact. The grammar of §3.5 as `coerce : Assumptions → Ty → Ty →
   Except CoercionRefusal ATerm` over canonical finite types, with `coerce_checks` proved per
   constructor against `Bidirectional.checkAgainst`, and the `Quantity`/`Reuse` table of §5.1 written
   down as a `decide`-able relation with a tooth for each row of the table. Gate: the theorem, plus
   `#guard` probes for the §5.2 and §5.3 refusals. It is first because it is independent of inference,
   because it is the only new thing the kernel-facing theorem needs, because it retires `seedExtra` for
   shareable seeds on its own, and because it forces the §5 decision into code on day one.
2. `Elab/Polar.lean`. The component table of §1.2 as `embed : Ty → Option Polar` with its domain the
   image of §1.1, `readback : Polar → Ty` on constructed elements, and the theorem that `sameType` and
   polar equivalence agree on the image, proved for finite rows first and for aliases through
   `TypeGraph`. Gate: round-trip on the eight executable `sameType` probes of the equi-recursive report.
3. `Elab/Infer.lean`. Simple-sub with levels over Core4 heads and a `Row` kind for rigid tails;
   `inferTemplate`. Gate: Dolan's `select`, `twice`, `λx. x x` and MLsub 2017's examples reproduce the
   published schemes; the minidregg LT2 cohort (`W04-RecursiveNode` through `W10-BinarySelf`) yields
   schemes that subsume the declared bounds.
4. `Elab/Subsume.lean`. Skolemised constraining per MLstruct §3.3; `subsumes`. Gate: the same cohort,
   plus a refusal that names the head pair and path for each `self-unbound-member` and
   `inherited-unprovided` case the cohort pins today.
5. Integration in `Spec/Elaborate.lean`: `templateLayer` calls `inferTemplate` and `subsumes` against
   the declared bounds; `chainFix` calls `subsumes` at each open instance in place of the READ clauses of
   `Contract.checkBounds`, keeps `checkProvides` and `close`, and runs `coerce` at the two §4.5 sites.
   Gate: `tests/run-obend-source.py` cohorts unchanged except the rows whose refusal text names a
   contract read clause, which now name a head pair; the journal's repair set for `Spec` is reported.
6. `readback_checks` (§3.6), then the fragment completeness. These are the theorems that make
   annotation discovery executable on the template fragment and are the lane's exit.

Not in this order and not in this edition: subtyping in `Core`, subtyping in `Contract.replaced`,
recursive coercions, activity coercions, lifting `℧₂`.

## 7. Where this disagrees with the brief's first read

1. Item (1). The declared bound is not inferable in full and not replaced by inference: the reads are
   inferred, the F-bound and the `requires` contract are not, the direction is inverted in Dolan's
   order, and the provided row needs a row kind that polar types do not have.
2. Item (6). Duplicate-label rows carry custody and once-closure obligations, not provenance; C4 reads
   names and reflection reads `SpecMeta`; the thing width subtyping would forget is a resource.
3. Item (5). Quantities are not orthogonal: coercions are terms, so the checker's own rules fix the
   order on `Quantity` and `Reuse` (identifying `affine` with `linear` and excluding `erased` as a
   target), width coercions need shareable sources when they keep two fields, and dropping a
   non-shareable field is permitted by the checker and forbidden by the discipline the checker's
   canonical form already keeps.

Items (2) and (3) are half right, as §2 says; item (4) is right with the two qualifications given there.
