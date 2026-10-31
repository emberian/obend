# A hybrid foundation for Objective Bend: the structure under the six modules

2026-10-31, Claude, on `review/SYNTHESIS-BRIEF-20261031.md`. Tags: READ is a claim a named source
states, or a fact of `lean/Obend` at `3ed9eba` read in the file named; INFERRED is a consequence I drew
from read sources; PROPOSED is a design choice this document makes. Where a source is cited from
memory rather than from a text read for this document, the sentence says so.

## 0. Sources

READ in full or in the sections cited: `THESIS.md`, `DESIGN.md`, `METATHEORY.md`,
`review/PRIOR-ART-20261030.md`, `review/ARGON-RESPONSE-20261030.md`,
`review/ALGEBRAIC-SUBTYPING-20261031.md`, `lean/docs/REPORT-EQUIREC-20261031.md`,
`lean/docs/REPORT-DOC-20261030.md`, `lean/docs/REPORT-LAW-20261030.md`, `lean/docs/REPORT-20261031.md`,
`review/KIMI-REVIEW-20261030.md` §1–§3; the Lean modules `Slot.lean`, `Slot/{World,Integrity,Budget,
Calculus,Protocol,Core4}.lean`, `Law/{Syntax,Inherit,Claim,Std}.lean`, `Spec/{C4,Contract}.lean`,
`Core/{Term,Graded,Interaction,Capacity}.lean`, `Doc/{Merge,Section}.lean` (declarations), and
`Journal/Journal.lean` (the closure, now with `mem_closure_iff` and `closure_complete`).

READ in `~/paperbin`: Mimram–Di Giusto (whole), Angiuli et al. §3–§4, Cook–Palsberg §1–§4.1,
Bracha–Cook §1–§2, Canning et al. (the F-bound), Bruce–Cardelli–Pierce (the encodings), Green et al.
§1–§3, Grädel–Tannen 2017 §1–§3, Dannert et al. §1–§3 (absorptive semirings), de Kleer §4.3 (labels),
Doyle 1992 §1–§3, Mokhov et al. §3 (the task abstraction, correctness), Nanevski et al. §2–§3 (the
contextual modality and its substitution principle), Cave–Pientka §1–§2, Wood–Atkey §1–§3, Gaboardi
et al. §1–§2, Orchard–Wadler–Eades §1–§2, Xia et al. §2–§4 (`interp`, `iter`, handlers), Delaware
et al. §1–§2, Hackett–Hutton §1, Myers (the extended abstract), Johnson–Rosebrugh–Wood §1, Cai et al.
(abstract), Shulman (abstract and contents), Faré's LTUO §2.3.2 (conflation), §5.5.3, §6.1.x,
§7.3.5.2, §7.4.4, §9.3.7. The equi-recursive, algebraic-subtyping and checker material is taken from
the three reviews, which read Dolan, Parreaux, Tang and Amadio–Cardelli for us.

Not in `~/paperbin`: Moran–Sands 1999 (`PRIOR-ART` lists it; the file is absent). Claims about
improvement theory below are from memory and are tagged so. Hasegawa's traced cartesian categories
and Bloom–Ésik's iteration theories are cited from memory. Lawvere 1973 is in `~/paperbin` but was not
re-read; the enrichment remark cites it from memory.

## 1. The finding, in one paragraph

INFERRED. The nine threads the brief lists are not instances of one structure; they are instances of
two, joined by one map. The first structure is a commutative semiring K of justifications and the
K-weighted relations over the World's facts: every judge in `Slot`, `Law`, `Doc`, `Journal` and
`Protocol` is the Boolean image, under a semiring homomorphism fixed by the view, of one polynomial
over fact tokens; every refusal is that polynomial evaluated in the dual semiring, which names the
tokens that failed; every repair is re-evaluation at a later view; every closure (`beforeB`, the
journal's walk) is a Kleene star in a finite idempotent semiring. The second structure is a category
of extensions with a lazy fixed-point operator: Core4's `mix` is composition, `fix` is the fixed
point, C4 chooses a path through the precedence DAG, and Faré's linearity is the statement that the
chosen composite visits each node once. The map between them is resolution: an intention (a named
parent, a cite, a kind) is a hole whose candidates are pins, so the specification DAG at a view is a
K-weighted graph and the justification of a composed object is the product of the pins it resolved.
Where the brief asks for a double category, a fibration, a graded monad or a 2-category of patches,
the answer is that each is the right *name* for a part of the picture and the wrong *thing to
formalize*: the base change a double category would provide is precomposition with a row projection;
the fibration over the World's history is a family of homomorphisms indexed by views; the graded
monad is a lax monoid homomorphism from substitutions to an ordered monoid; the 2-category of patches
is a thin category with partial joins. Each of those costs one definition in Lean. The one place where
higher structure is not decoration is the cost-sensitive equivalence of `mix` under sharing, and that
is the Iris-Lean row of `METATHEORY.md` §2, unchanged by this document.

## 2. What each module is, as built

Each sentence is READ from the module named unless tagged otherwise.

- `Slot`: `Slot Fact Cand = (supports : Cand → List Fact, judge : Cand → Bool)`; `usable holds c =
  judge c && (supports c).all holds`; `alternatives` filters the chooser's order; `read` reports
  `usable c ev | blocked c dead | rejected c | empty`; `select`/`resolve` take the first usable or
  return `order.map (c, dead c)`. `slot_repair` is four unfoldings and `Permanent`. INFERRED (Kimi
  §1): everything here is "a conjunction per candidate, a disjunction over candidates, read at a
  valuation".
- `Slot.World`: a class with `pin : V → Cell → Option Pin`, `holdsAt : V → Fact → Bool`, `Step`, and
  three laws: truth is a function of the cell's pin, a retired cell's facts are false, retirement is
  terminal along `Step`. `Integrity.contextual` and `Integrity.repair` are proved for the first-usable
  filler over every World; Kimi §1 shows `repair` follows from `contextual`, and §2 that the class
  carries only the retirement fragment of nano's version law.
- `Slot.Calculus`/`Decides`/`Budget`: a `Typed` relation, a graded procedure `check : R → …` monotone
  in `R` (`Graded R` an ordered commutative monoid), a `Prepares` relation, and `admit` returning
  `uncovered r`. The substitution law lives on `Typed` (`calculus_typed_msubst`); the graded one holds
  at `n + m` (`check_msubst`) with `UsesLE` on usage vectors.
- `Slot.Protocol`: `Prot S Hole A i` is the free monad on an indexed signature with a third
  constructor `hole`; `subst` is single-pass; `interp` runs a resolver at each hole to depth `n`;
  `Frag`/`fromScratch`/`repair`/`residual` are verifying traces with static supports.
- `Law`: a law is a closed Core4 term `S → S → Req → Verdict`; `Admits`/`Refuses` are over
  `Evaluates`; `effective lin` conjoins laws along a C4 list and names the first refuser
  (`inheritedVerdictTy`); every `Std` generator is built from `guards`/`allOf`/`anyOf`, each guard a
  decidable field comparison with a reason string (`Law/Std.lean`); `keeps` is a certifying-shape
  check lifted to admitted chains.
- `Spec/C4`: a port of pommette's C4; `OrderedPresentationInvariant` stated, checked on 4000 DAGs,
  not proved; `Contract.run` composes layer contracts as `C_{A;B}(S,I) = C_A(S,I) ∧ C_B(S, F_A(S,I))`
  and `close` requires the final row to equal the self.
- `Core`: `mix lower upper → λself.λsuper. upper self (lower self super)`; `fix spec seed → spec
  (fix spec seed) seed`; call-by-name weak head; `hole n σ` is a constructor with no typing rule;
  `Interaction` gives an activity's reference meaning as an interaction tree (`vis/ret/spin`).
- `Doc`: pages are finite graphs with stable atom identities; `Le` is a preorder (content, tombstones
  and edges carried); `merge` is union, a pushout when `Compatible`, `no_cocone` otherwise;
  `sectionAt p x : Slot Fact Run` with supports `live`, `head`, and a cite's `verifies`/`current`;
  `beforeB` is a depth-bounded walk with a closure certificate (D4: completeness not proved).

## 3. Structure I: justifications as a semiring, judges as homomorphisms

### 3.1 The definition

PROPOSED, stated so that a Lean file can be written from it without Mathlib.

```
/-- A commutative semiring of justifications. `absorb` makes it a lattice-like semiring in which
`1` is the top: a justification that needs fewer facts absorbs one that needs more. -/
structure Just (K : Type) where
  zero one : K
  add mul : K → K → K
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  zero_mul : ∀ a, mul zero a = zero
  distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  absorb : ∀ a b, add a (mul a b) = a

/-- A polynomial over tokens `X`, in the free absorptive semiring: a finite set of monomials, each a
finite set of tokens. Addition is union then minimisation; multiplication is pairwise union. -/
structure Poly (X : Type) where
  monomials : List (List X)

/-- The unique semiring homomorphism out of the free one at a valuation. -/
def Poly.eval [Just K] (ν : X → K) : Poly X → K
```

READ (Green et al. §3–§4; Grädel–Tannen 2017 §1.2; Dannert et al. Def. 10, Prop. 11). A commutative
semiring is what the relational algebra forces on annotations; the polynomial semiring N[X] is the
free one, every K-semantics factors through it along the homomorphism induced by the valuation;
`PosBool(X)` is the distributive lattice freely generated by X; a semiring is absorptive iff `1 + b =
1` iff multiplication is decreasing iff `1` is the greatest element, and absorptive semirings are
idempotent. INFERRED. `Poly X` above is `PosBool(X)` (equivalently Dannert's `S[X]` without
exponents): monomials are sets, sums are minimal antichains, `1` is the empty monomial, `0` the empty
sum. That is the semiring de Kleer's labels live in. READ (de Kleer §4.3): an ATMS label is a set of
environments (sets of assumptions) that is consistent, sound, complete and minimal; a node holds in a
context iff some label environment is a subset of the context's assumptions. INFERRED: minimality is
absorption, "holds in a context" is evaluation at the context's valuation into the Boolean semiring.

### 3.2 The dual semiring and the refusal

READ (Grädel–Tannen 2017 §3.1, Def. 15, Prop. 14). `N[X, X̄]` is the quotient of `N[X ∪ X̄]` by
`p · p̄ = 0`; a provenance-tracking interpretation maps positive facts to `X ∪ {0,1}` and negative
facts to `X̄ ∪ {0,1}`; it has the universal property for valuations with `f(p) · f(p̄) = 0`. READ
(Dannert et al. §1): "beyond Boolean semantics, negation is not a compositional logical operation";
negation is handled by negation normal form and dual tokens.

PROPOSED. The refusal semiring of Objective Bend is `Poly (X ⊕ X̄)` modulo `p · p̄ = 0` with absorption:
`Dual X`. The tracking valuation of a view `v` is

```
νᵈ v : X → Dual X
νᵈ v f := if holdsAt v f then 1 else token f̄
```

INFERRED. For a candidate `c` with polynomial `P c = ∏_{f ∈ supports c} f · j_c` (with `j_c` the
judge's token), `(P c).eval (νᵈ v)` is the monomial `∏_{f dead at v} f̄ · (j̄_c if the judge fails)`:
a single monomial naming exactly the dead supports. That monomial is `Slot.dead (holdsAt v) c` as an
element of a semiring instead of a list, and `Refusal` is `order.map (fun c => (c, (P c).eval (νᵈ v)))`.
In the Boolean image, `(P c).eval (ν v) = usable (holdsAt v) c`. So the Boolean judge and the named
refusal are two evaluations of one polynomial, related by the homomorphism `Dual X → B` that sends
every negative token to `0`. This is Green–Tannen's factoring applied to the slot.

### 3.3 The valuation of a World

PROPOSED. A World supplies, for each view, a Boolean valuation `ν v : Fact → B` and the tracking
valuation `νᵈ v` derived from it, with two laws:

```
/-- Truth factors through pins: the valuation is `ev ∘ pin`. -/
factor : ∃ ev : (Cell → Option Pin) → Fact → Bool, ∀ v f, ν v f = ev (fun c => pin v c) f
/-- Retirement is a zero that stays zero along steps. -/
retired_zero : pin v (cell f) = none → ν v f = 0
retired_step : Step v v' → pin v c = none → pin v' c = none
```

READ (`Slot/World.lean`): these are `holds_congr`, `retired_dead`, `retired_step` restated; nothing is
added. INFERRED. Everything the module proves after them (`holds_agree`, `dead_congr`,
`usable_congr`, `read_congr`, `alternatives_congr`, `dead_behind_forever`, `blocked_forever`,
`retired_later`) is one of two lemmas about polynomials: evaluation depends only on the valuation of
the tokens that occur (`eval_congr`), and a token valued `0` zeroes every monomial containing it
(`zero_mul`, with `retired_step` making the zero persist along `Later`). Eight theorems become two
instances.

READ (Kimi §2): the class admits a pin that returns, and the version law "a moved pin never returns"
is outside it. PROPOSED. Do not add a version order. Add a predicate on tokens, `Permanent f`
(already in `Slot.lean`), and a partial repair action `repair : Fact → Option (V → V)` with
`repair_step : repair f = some r → Step v (r v)` and `repair_holds : ν (r v) f = 1`; `Permanent f ↔
repair f = none` is then a theorem of each instance, and the version law is the instance's statement
that a moved pin's token has no repair. Kimi's cyclic pin world is then a World whose flipping token
is not Permanent and whose repair is "wait one step", which is the honest description of it.

### 3.4 The first-usable lemma

INFERRED. Two modules select the first element of an ordered list that is a unit: `Slot.select`
takes the first candidate with `eval = 1`; `Law.effective` takes the first ancestor with verdict
`refused` and otherwise `ok`. READ (`Law/Inherit.lean` docstring): "a refusal names the ancestor whose
clause refused"; (`Slot.lean`): "the first usable candidate in the chooser's order". PROPOSED. One
lemma over an ordered list `l : List K` and a homomorphism `h : K → B`:

```
firstUnit (h) (l) : Option (Nat × K)   -- index and value of the first element with h x = 1
firstUnit_some : firstUnit h l = some (i, x) → l[i] = x ∧ h x = 1 ∧ ∀ j < i, h l[j] = 0
firstUnit_none : firstUnit h l = none → ∀ x ∈ l, h x = 0
```

`select_ok`, `select_error`, `resolve_ok`, `resolve_error`, `resolve_eq_select`, and in `Law`
`effective_refusal_names`, `effective_refuses_first`, `effective_law_eval`,
`inherited_never_widens`, `inherited_refusal_kept` are its instances, the Law ones through the
verdict monoid of §6.3. The chooser's order itself is not semiring data; it is a choice function on
top of the semiring, and the synthesis leaves it there (§11).

### 3.5 Grades are the multiplicative half of two more semirings

READ (Wood–Atkey §2–§3): usage annotations are vectors over a (skew) semiring, renaming and
substitution act by matrices, and the metatheory is the linear algebra of those matrices; the
`0 ≤ ω ≥ 1` semiring gives DILL. READ (`Core/Graded.lean`, `Slot/Calculus.lean`): `Graded R` is an
ordered commutative additive monoid with `0` least and `+` monotone; `Decides.check` is monotone in
the grade; `check_msubst` holds at `n + m` with `UsesLE` on uses. READ (Gaboardi et al. §1–§2): effect
grades are a preordered monoid, coeffect grades a semiring, and their interaction needs a graded
distributive law. READ (Orchard–Wadler–Eades §1): a category-graded monad is a lax functor indexed by
morphisms, generalising both graded and parameterised monads.

INFERRED. Objective Bend has two grades and no interaction between them. The usage vector is a
coeffect in Wood–Atkey's sense; its substitution law is the matrix law. The budget is not a grade on
terms but on a procedure; its substitution law `grade (msubst σ t) ≤ grade t + Σ grade (σ x)` says the
grade is a lax monoid homomorphism from the category of contextual substitutions (CMTT's `[σ]`) to
`(R, +, ≤)`. Both laws are "a functor from substitutions to a semiring's multiplicative monoid, lax
up to the order". No distributive law is needed because nothing in the judge lets the budget change
the usage or conversely; no graded monad is needed because no term is wrapped. PROPOSED. State the
laxness once in `Decides`:

```
grade_msubst : check r Ψ t A = true → (∀ x f, σ x = some f → check (s x) (Ψ at x) f (Ψ[x]) = true) →
  check (r + Σ_x s x) Ψ (msubst σ t) A = true
```

and derive `calculus_check_msubst`, `calculus_check_msubst_within` and the `UsesLE` conclusion
(§6.1). This is what `METATHEORY.md` §1 asked for ("the arithmetic of `n + m` becomes the monoid law,
stated once"); it is the only place the synthesis touches `Core`.

### 3.6 Closure is a Kleene star

READ (Green et al. §5, abstract): datalog provenance is a least fixed point in an ω-continuous
semiring; for finite distributive lattices the fixed point is reached in finitely many steps. READ
(Mimram–Di Giusto Thm 15, Prop. 16): objects of the cocompletion are finite sets with a transitive
relation; the pushout is union followed by transitive closure. READ (`Doc/Graph.lean` via
REPORT-DOC D4): `beforeB` walks to depth `|edges|` with a `Closed` certificate; completeness is
"a pigeonhole argument I did not write". READ (`Journal/Journal.lean`): the walk now has
`mem_closure_iff` and `closure_complete`; Kimi's fuel counterexample is retired.

INFERRED. Both `Before` and the journal's meaning-edge reachability are the reflexive–transitive
closure of a Boolean matrix on a finite set, which is the Kleene star `Σ_{k ≤ n} E^k` and stabilises
at `n = |atoms|`. PROPOSED. One theorem, `star_stabilises`, on finite Boolean matrices (or on
`Poly`-weighted ones, which gives "why is `a` before `b`" as a monomial of edges, i.e. the blame the
Doc lane did not build), with `beforeB_complete` and the journal's `closure_complete` as instances. D4
closes without a pigeonhole argument of its own.

## 4. Structure II: the category of extensions with a lazy fixed point

### 4.1 The definition

READ (Cook–Palsberg §3.2): a wrapper `W : Self → Super → Record`; wrapper application `W ⊛ G = λself.
W(self)(G(self)) ⊕ G(self)`; a class is a generator, an object its fixed point. READ (Bracha–Cook §2):
`C = Δ(P) ⊕ P`, the delta parametric in the parent; a mixin is a delta abstracted from its parent;
linearization is "an implementation technique for mixins". READ (`Core/Term.lean`): `mixBody lower
upper = λself.λsuper. upper self (lower self super)`; `fix spec inherited → spec (fix spec inherited)
inherited`. READ (LTUO §5.5.3): "Because mix is associative"; `mix/list` folds a list with `idModExt`.

INFERRED. Fix a self type `S`. Extensions `E : S → I → P` are the morphisms `I → P` of a category
`Ext_S`, with composition `(upper ∘ lower) self = upper self ∘ lower self` and identity `λself.λi.i`.
Core4's `mix` is this composition up to β; `fix E seed`, for `E : S → I → S`, is the fixed point of
`s ↦ E s seed`. `Spec.Contract` is the same category at the type level: objects are rows, a layer is
a morphism `I → F_L(S, I)` defined when `C_L(S, I)`, and `run_append` is composition; `close` is the
knot `F(S, seed) = S`. Cook's ⊕ is Core4's `extend` (first wins), and the row contract's "a provided
member never changes the type beneath" is what keeps ⊕ a morphism of rows rather than a replacement.

PROPOSED. Name this in Lean as a structure, not a typeclass, since there is exactly one instance:

```
structure ExtCat (S : Ty) where
  Hom : Ty → Ty → Type          -- closed Core4 terms of type S → I → P
  id : Hom I I
  comp : Hom I P → Hom P Q → Hom I Q     -- mix, with the lower first
  fix : Hom I S → (seed : Term) → Term
  comp_assoc : ∀ e f g, comp (comp e f) g ≈β comp e (comp f g)
  fix_unfold : Evaluates (fix e seed) (app (app e (fix e seed)) seed)
```

Both laws are already theorems about terms (`Step.mix`, `Step.fix`, β); the associativity is
syntactic, up to β-equivalence of `mixBody` nests, before any heap enters. The cost-sensitive
associativity (`≈b` with sharing) is a different statement and stays where `METATHEORY.md` §2 put it.

### 4.2 C4 is a choice of path; linearity is a count

READ (LTUO §7.3.5.2): linearity is "the information contributed by each ancestor's modular extension
shall be taken into account once and only once"; §7.3.5.3: a uniform order across methods must be a
linearization of the DAG; §7.4.4: C4 adds the suffix property to C3's monotonicity, local order and
extended precedence. READ (`Spec/C4.lean`): `linearize` returns the precedence list and the most
specific suffix; the invariance theorem is checked, not proved.

INFERRED. In `Ext_S`, the precedence DAG is a graph on specifications; a linearization is a path in
its transitive closure visiting every node exactly once; the composite along the path is one morphism
`mix/list lin`; "once and only once" is the statement that the path is simple, which is true of every
output of C4 by construction (each candidate is removed when chosen). The object is `fix` of that
composite. `compose(E, E)` applies `E` twice because it is the path `E · E`, with `E` a repeated
node, which is why identity must be the qualified declaration key, as `DESIGN.md` §4 says. So the
"ordered colimit" of the brief is not a colimit; it is a composite chosen by an algorithm, and the
theorem the object layer needs about it is equivariance under renaming (`OrderedPresentationInvariant`),
which is naturality of `linearize` in the identities, plus "the composite depends only on the list",
which is `comp_assoc`. The brief's "generators and their fixed points as algebras and coalgebras" is
Cook's cpo reading; Core4 refuses it (§8.11) because `fix` is call-by-name syntax and only `≈b` needs
a domain.

### 4.3 Where laziness and sharing enter

READ (Hackett–Hutton §1): Launchbury's heap "greatly complicates reasoning"; clairvoyant evaluation
replaces the heap by nondeterminism and gives the first denotational cost semantics for laziness.
From memory (Moran–Sands 1999, not in paperbin): improvement is a preorder on terms refining
observational equivalence by cost in every context. From memory (Hasegawa 1997): a Conway fixed-point
operator on a cartesian category is the same as a trace, and cyclic sharing in a lazy heap is the
trace's graph. INFERRED. The lazy fixed point with sharing is the only part of Structure II that a
semiring does not describe and that order theory does not settle; it is a traced structure, and the
theorem that needs it is `mix` associative up to improvement. The synthesis places it and does not
shrink it. It also identifies the cost semiring: improvement is the tropical weighting of evaluation
in the same sense that the budget is the tropical weighting of checking, and `REFLECTION.md`'s
"resource observations under a budget distinguish programs that agree on completed runs" is
Grädel–Tannen's "a semiring semantics refines the Boolean one" said of evaluation.

## 5. The map between the structures: resolution of intentions

READ (LTUO §9.3.7): "a name path or location properly identifies an extensible intention rather than
an immutable extension"; (`DESIGN.md` §4): a name parent is a slot whose chooser is the name's owner,
whose candidates are the versions, whose justification is "the record names version v at pin p".

PROPOSED. The specification DAG at a view is a graph whose intention edges are candidates of slots:
`parentSlot (name) : Slot Fact Version` with `supports v = [pinnedAt name v]` and `judge v =` "the
version's root is a specification of the expected shape". Resolution at a view is `select` on each
intention, then C4 on the resolved graph, then `fix`. INFERRED. The justification of the composed
object is the product over the intentions it crossed of the chosen version's monomial, by §3.2 and
§4.2 together; a moved pin is a dead token named in the dual evaluation (`stale` by name,
`DESIGN.md` §4); `read_congr` applied to the DAG says the linearization at two views agrees when the
pins of every intention on it agree. This is the only place the two structures meet, and it is where
"the ecosystem is one vast open recursion closed lazily per demand" (Faré, cited in `DESIGN.md`)
becomes a theorem shape rather than a slogan.

## 6. What each module becomes, and which theorems become instances

### 6.1 Core

PROPOSED. Core4's syntax and semantics are unchanged. `Decides` gains `grade_msubst` (§3.5) and
`Graded` is read as the multiplicative monoid of a cost semiring. `check_msubst` (at `n + m`),
`calculus_check_msubst`, `calculus_check_msubst_within` become instances of `grade_msubst` at
`R = Nat`; `UsesLE` becomes the matrix inequality of Wood–Atkey at the quantity semiring, stated once
for `PartialTyping` and inherited by `Bidirectional`. `Interaction` is unchanged; §6.5 says how
`Protocol` relates to it.

### 6.2 Spec

PROPOSED. `Contract` is presented as `Ext_S` at the type level (one docstring, no code change);
`Contract.run_append` is `comp` in `Ext_S`. C4 gains the intention layer of §5. The theorem to add
is `linearize_simple : ∀ x ∈ lin, count x lin = 1` (Faré's linearity, trivial but currently unstated)
and the renaming naturality the vectors check, now as the statement that `linearize` reads identities
only through equality.

### 6.3 Law

READ (`Law/Syntax.lean`, `Law/Inherit.lean`): laws at one state type `S`; `effective` conjoins at that
type. INFERRED. A law is a decidable relation on `S × S × Req`, i.e. a `B`-valued matrix, and the
`Std` generators are products of guard tokens with named negatives: `ownerSigns = ∏ (eqLabel agent
principal)`, `allowlist = ∏ (listed)`, `bounded = ∏ (new.f ≤ max)`, `quorum`, `windowed`, `machine`
likewise through `guards`/`allOf`/`anyOf`. So a `Std` law's verdict is the evaluation of a `Dual`
polynomial over condition tokens whose negative tokens carry the reason strings, and `effective lin`
is the lexicographic product of §3.4.

PROPOSED. Three changes.
1. The verdict type is the monoid `Verdict = ok | refused r` with `ok` the unit and `refused r · x =
   refused r`; `effective` is the monoid product along the list; `effective_refusal_names` and
   `effective_refuses_first` are `firstUnit`.
2. Base change. A parent law at `S_parent` is pulled back to a child at `S_child` along the row
   projection `π : S_child → S_parent` (the record coercion of `ALGEBRAIC-SUBTYPING` §3.5):
   `pull π L := λo n r. L (π o) (π n) r`, a Core4 term. `effective` takes a list of `(name, π, law)`.
   `inherited_never_widens` becomes `π^* L ∧ L' ≤ π^* L`, and `effective_law_eval` becomes `Admits
   (effective lin) o n r ↔ ∀ (name, π, L) ∈ lin, Admits L (π o) (π n) r`. This is the framed-
   bicategory base change of Shulman's `Rel` (abstract, READ), costing one definition.
3. Laws depend only on the fields they read: `admits_congr : (∀ f ∈ fields L, o.f = o'.f ∧ n.f = n'.f)
   → (Admits L o n r ↔ Admits L o' n' r)`, an instance of `eval_congr` for the `Std` fragment. This is
   what an `adopt` occasion needs to re-judge only the instances it must.

`keeps inv law` is unchanged: it is the statement that `inv` is closed under the relation, i.e. a
square in `Rel`, and `chain_keeps` is closure under the composite of the laws in force along the
history (relaw changes the relation; the composite is still a composite in `Rel`).

### 6.4 Slot

PROPOSED. `Slot Fact Cand` keeps its two fields and gains `poly : Cand → Poly (Fact ⊕ JudgeTok)`
defined from them; `usable`, `dead`, `evidence`, `read`, `alternatives`, `select`, `resolve`,
`Refusal` are redefined as evaluations (`usable = eval (ν v)`, `dead = eval (νᵈ v)` read back as a
list, `select = firstUnit`). Theorems that become instances: `dead_eq_nil_iff`, `mem_dead_iff`,
`usable_iff`, `read_usable_iff`, `read_blocked_names`, `slot_repair` (1), (2), (4), `select_ok`,
`select_error`, `resolve_ok`, `resolve_error`, `resolve_eq_select`, `slotOf_usable`,
`resolve_checks`, and all of `World`'s congruence and retirement lemmas (§3.3). `slot_repair` (3) and
`Integrity.repair` (1) become `zero_mul` along `Later`; `Integrity.repair` (2) is `firstUnit_none`
contrapositive, which is Kimi's redundancy made explicit. `slotFiller_uncovered` is the statement
that the judge's negative token is `uncovered r`. The three floors stay as mutations of the
valuation (ignore supports = evaluate at `ν ≡ 1`; ignore the judge = drop `j_c`; blind refusal =
evaluate in `B` instead of `Dual`), which is a cleaner statement of what each floor forgets.

### 6.5 Protocol

READ (Xia et al. §2.3, §3.2, §4): `interp : (E ⇝ M) → itree E ⇝ M` folds a handler over events and
is a monad morphism; `E +' F` leaves `F` uninterpreted; `mrec` ties recursive handlers. INFERRED.
`Prot S Hole A` is the free monad on the signature `S +' Hole` with no `Tau`; `Slot.interp call
resolve n` is `interp` with the handler `Hole ⇝ Except Refusal` for the `Hole` summand and `call` for
the `S` summand, and `n` is the fuel on `mrec` for fillings with holes; `RunsR` is its trace;
`runsR_withdrawn` is "interp of a triggered event is the handler's answer"; `.other` holes are the
summand the handler passes through. PROPOSED. Restate `interp` as a handler fold with the two
summands explicit. The gain is handler composition (a chooser's holes, a budget's holes and a cite's
holes are three summands with three handlers, interpreted in any order), which the deployed resident
with two holes already needs. Coinduction, `Tau` and `eutt` are refused (§8.7).

READ (Mokhov et al. §3.3–§3.4, Def. 3.1): `Task c k v = ∀f. c f ⇒ (k → f v) → f v`; `Applicative`
tasks have static dependencies, `Monad` tasks dynamic ones; a build is correct iff inputs are
unchanged and every non-input key equals its recomputation in the result store. INFERRED.
`Frag`'s `support` is a static dependency list, so `fromScratch`/`repair`/`residual` are the
`Applicative` case, and "from-scratch consistency" is `eval_congr`: a fragment's verdict is a function
of its support's valuation. A slot's supports are `Applicative`; a nested fill (a filling with
holes) is `Monad`-shaped, and its justification is a trace, not a polynomial known in advance (§11).

### 6.6 Doc

READ (Mimram–Di Giusto Def. 5, Thm 15, Thm 20, Prop. 16; REPORT-DOC D1–D5). INFERRED. With stable
identities the category of pages is thin, `Le` is inclusion of labelled relations, `merge` is union,
and the pushout is the join; Mimram's objects (finite sets, transitive relation, labels) are exactly
`Doc.Graph` once edges are closed transitively, which is D2's deviation and the reason freeness is
not provable as built. PROPOSED. Keep the thin category; take `Before` as the Kleene star of `edge`
(§3.6) so `Le` carries the order and D2 closes; `merge_isPushout`, `pushout_unique`, `merge_comm`,
`merge_self`, `le_merge_left/right`, `merge_le` become the join's properties in a semilattice;
`no_cocone` stays as the identity discipline's theorem. `sectionAt` is already a slot; its theorems
`section_alternatives`, `conflict_is_section`, `pinned_cite_stays`, `following_cite_behind`,
`verifies_stays` are `eval_congr` (the tokens `live`, `head`, `verifies` are unchanged when the
source moves) and `zero_mul` (the `current` token dies); `recite_holds` is the repair action of the
`current` token (§3.3), the first concrete instance of `repair f = some r`. REPORT-DOC §5's
decision (what a wikilink is) is then a choice of which tokens a cite carries, and (c) with (b)'s
currency is "a byte cite carries `verifies` and a range-stable `current`; a reference carries only
`exists`".

### 6.7 Leaf

INFERRED. Nothing in Structure I or II constrains the leaf; `DESIGN.md` §3's `leafProof (package,
law, kernelHash)` is one more token with a repair action (re-prove under the new kernel) and no more.
The leaf refinement theorem (`METATHEORY.md` §2, itree simulation against BendTT) is untouched.

## 7. The new theorems

Each is PROPOSED with the shape it must have; each needs pieces no single paper has.

T1. Composite justification of a nested fill (CMTT × ATMS × Tannen). For `interp call resolve n P`
run at view `v` to outcome `done`, there is a trace of resolved holes `h_1 … h_k` with chosen
candidates `c_1 … c_k` such that the run's justification `∏_i poly c_i` evaluates to `1` at `ν v`,
and for outcome `withdrawn h_j w`, `w` is `eval (νᵈ v)` of hole `j`'s slot while `∏_{i<j} poly c_i`
evaluates to `1`. Why new: CMTT has holes and substitution but no world; the ATMS has labels but no
holes; Tannen has polynomials but no run.

T2. Repair soundness (World × slot × repair actions). If `select` refuses with `w` and some
candidate's monomial in `w` consists of repairable tokens, applying their repairs in sequence yields
`v'` with `Later v v'` and `select` at `v'` succeeding; `Permanent f ↔ repair f = none`; and
`Integrity.repair` (1) is the corollary for retired tokens. Why new: Doyle's foundations approach
records reasons but has no audited step that re-establishes one; Grädel–Tannen's reverse provenance
finds models, not steps.

T3. Cross-package law inheritance by base change (C4 × laws × rows). With `effective` over
`(name, π, law)`, `Admits (effective lin) o n r ↔ ∀ (_, π, L) ∈ lin, Admits L (π o) (π n) r` and
`inherited_never_widens` across state types; the refusal names `(package, ancestor, clause)`.
Why new: Cook and Bracha have wrappers without laws; nano has laws at one type; the Faré audit asked
for it and no one has the coercion in hand but this tree.

T4. Law repair on the `Std` fragment (laws × dual polynomials). `wouldPass : StdLaw → Data → Data →
Data → Option Data` with `wouldPass L o n r = some r' → Admits L o n r'` and `= none → ∀ r' agreeing
with r outside the controllable fields, ¬ Admits L o n r'`. The controllable fields are declared per
generator (the signer, the window, the approval set). Why new: "a refusal names the request that
would pass" has no precedent (`PRIOR-ART` §10); this makes it a theorem on the fragment people write.

T5. Intentions as slots (C4 × slots × World). The linearization of a DAG with intentions at two views
agrees when the pins of every intention on the result agree (`linearize_congr`), and a moved pin
names itself in the refusal (`stale`). Why new: Faré has intentions as prose; nix has the global
fixed point without pins as justifications.

T6. Closure as a star (Doc × Journal). `star_stabilises` on finite Boolean matrices, with
`beforeB_complete` and `closure_complete` as instances; the weighted version gives blame for order.

T7. Grade laxness, once (Core × Slot). `grade_msubst` for any `Decides` instance, with Core4's three
substitution theorems as instances and the usage matrix law as the second semiring's instance.

## 8. Which level of structure is needed, and which generality is refused

8.1 Double categories (Shulman's framed bicategories, Myers, Grandis–Paré). INFERRED. The content used
is base change of a relation along a function (`pull π L`) and squares of the form "the relation
restricts to the subobject" (`keeps`). Both are definitions in `Rel`, which is locally thin. No
coherence is at stake; a double-category library would buy nothing. Myers' double Grothendieck
construction of open systems is refused: our open objects are terms with holes, and their composition
is substitution, not a span.

8.2 Fibrations. INFERRED. The fibration over the World's history is the family `ν v`, and its
Grothendieck construction is the category whose objects are `(v, c)` with `eval (ν v) (poly c) = 1`
and whose morphisms are steps preserving that; `Integrity.repair` (1) says the fibre over a view with
a retired support is empty. One sentence; no construction to build. Johnson–Rosebrugh–Wood's
c-lenses as opfibrations (READ §1) would matter if the kernel translated view updates to world
updates universally; it does not, repair actions are declared per token (§3.3).

8.3 Graded monads and distributive laws. Refused (§3.5): no term is wrapped, no interaction exists.
Kept: the lax homomorphism from substitutions to an ordered monoid.

8.4 2-categories and HITs of patches. READ (Angiuli et al. §3): patches as paths, laws as 2-paths,
merge from pseudocommutation, which requires inverses. INFERRED. Our patches are not invertible
morphisms (`invert` is an operation on patches, `Le` is a preorder), merge is a join, and no
reordering of patches is ever computed. Refused entirely.

8.5 Mimram's free cocompletion. READ (Thm 20): morphisms are partial functions respecting labels and
relations; Example 18 shows cycles arising from sequentialization. INFERRED. With stable identities
the hom-sets are subsingletons and the cocompletion collapses to formal joins; a conflict is a slot,
not a new object kind. Refused beyond the thin category; kept: pushout as join, conflicts as objects.

8.6 Provenance generality. READ (Green et al. §4–§6; Dannert et al. abstract, Def. 10). Refused:
multiplicities (`N[X]` counts proof trees; we never count), formal power series and ω-continuity
(no infinite slots), full continuity and `S∞[X, X̄]` (no alternation of least and greatest fixed
points in a judge; the one greatest fixed point in the tree, `ResourceSemantics.shareable`, is
Boolean on a finite graph). Kept: the absorptive (lattice) semiring, dual tokens, the factoring
theorem, the finite Kleene star.

8.7 Interaction trees. Refused: coinduction, `Tau`, `eutt`; `Prot` is inductive and every run is
finite. Kept: free monad on a signature sum, handlers, `interp` as a fold, `mrec` with fuel.

8.8 CMTT and first-class substitutions. READ (Nanevski et al. §3): `[Ψ]A` internalises `A valid[Ψ]`
with the contextual substitution principle; (Cave–Pientka §1): substitution variables `Γ[Ψ]`.
Refused: substitution variables, dependent contextual types; fillings stay closed (`Scoped 0`,
REPORT-20261031 D9, Kimi §1 on `open_filling_tooth`). Kept: the meta-context `Ω` as the type of
holes, the substitution principle as `grade_msubst`.

8.9 The ATMS. Refused: the label-propagation algorithm, derived nodes, nogood databases. Our
justifications do not chain through a network; they chain through nested fills, which are traces.
Kept: labels as minimal environments, contexts as valuations, foundations over coherence (Doyle 1992
§1–§3, READ; the project's choice, `PRIOR-ART` §9).

8.10 Wood–Atkey, Granule. Refused: skew semirings, the full λR. Kept: vectors and the matrix law at a
three-point quantity semiring, as `ALGEBRAIC-SUBTYPING` §5.1 measured it.

8.11 Cook–Palsberg's domain theory, Dolan's lattice, Delaware's feature algebras. Refused as kernel
structure: `fix` is syntax, not a cpo least fixed point, until `≈b`; the type lattice belongs to the
elaborator (the scholar's decision stands); feature algebras do not remove the domain-lemma class
(`PRIOR-ART` §6). None of the three is unified by this document (§11).

## 9. What it would cost to adopt

PROPOSED, per module, with the statements whose shape changes.

- New: `Obend/Just.lean` (the semiring, `Poly`, `Dual`, `eval`, `eval_congr`, `firstUnit`,
  `star_stabilises`), about 400 lines, no imports beyond `AxiomPin`.
- `Slot.lean`: `read`, `select`, `resolve`, `Refusal` redefined through `eval`; `slot_repair`'s four
  clauses keep their statements but `Reading.blocked`'s payload becomes a monomial read back as a
  list, so `read_blocked_names` changes from list membership to monomial membership. Every pin stays
  checkable; every tooth stays red. `Protocol.lean`: `interp` restated as a handler fold; `RunsR`
  changes shape. `World.lean`: `repair`/`Permanent` added; nothing removed. `Integrity.lean`:
  `Integrity.repair` becomes a corollary (stated, kept).
- `Law/Inherit.lean`: `effective` over `(name, π, law)`; `effective_law_eval`,
  `inherited_never_widens`, `effective_refusal_names` change shape (a projection per ancestor);
  `Law/Syntax.lean`: the verdict monoid stated; `Law/Std.lean`: a `fields`/`controllable` reading per
  generator for T4.
- `Doc/Graph.lean`: `Before` as the star, `beforeB` retired, D4 closed; `Doc/Merge.lean`: proofs
  change, statements do not; `Doc/Section.lean`: `recite` registered as the `current` token's repair.
- `Core/Graded.lean`, `Slot/Calculus.lean`: `grade_msubst` in `Decides`; `Slot/Core4.lean`: the three
  substitution theorems become instances (statements kept as corollaries).
- `Spec/C4.lean`: `linearize_simple` added; `Spec/Intention.lean` new for §5.
- Untouched: `Core/Term.lean`, the checker, the machine, equi-recursion, the elaborator, the front end.

The adoption is additive in `Core`/`Spec`, a redefinition under kept statements in `Slot`/`Doc`, and a
shape change in `Law` and `Protocol`. The hole exercise's journal (`EQUIREC-JOURNAL` style) measures
the cascade; the prediction is that `Slot`'s and `World`'s theorem count halves and `Law`'s grows by
the base-change lemmas.

## 10. Three experiments, each one Lean file a lane could write in a day

E1. `lean/Obend/Just.lean` plus a scratch `Slot/PolySlot.lean` that redefines `usable`, `dead`,
`read`, `select` through `eval` at `ν` and `νᵈ` and re-proves, from `eval_congr`, `zero_mul` and
`firstUnit` alone, every theorem of `Slot.lean` and `Slot/World.lean` listed in §6.4, with the
original pins and the original `#tooth` mutations (eight in `Slot.lean`, eight in `World.lean`, eight
in `Integrity.lean`). Gate: every one re-proved; total proof text shorter than the originals'. Red: a proof that is longer, or a statement that cannot be reached
without re-unfolding `read`. This is the experiment to run first, because if the polynomial does not
shorten the slot, the rest of the document is renaming.

E2. `lean/Obend/Law/Pull.lean`: `pull π L` as a Core4 term using the record coercion of
`ALGEBRAIC-SUBTYPING` §3.5 (`λo n r. L (π o) (π n) r` with `π = λx. record [(ℓ, get x ℓ)]`),
`pull_admits` over `Evaluates`, `effective` over `(name, π, law)`, and the two inheritance theorems
across state types, with a tooth: a child law that admits a write the parent refuses is refused by
name of the parent. Gate: `pull_admits` without a new primitive in Core4. Red: the `Evaluates`
plumbing for the coercion needs a `Core.Term` change, in which case base change is not free and §8.1
is wrong about its cost.

E3. `lean/Obend/Slot/Trace.lean`: T1. Define the justification of a `RunsR` derivation as the product
of the resolved candidates' polynomials, prove `runs_done_justified` and `runs_withdrawn_named`, and
instantiate on the negotiation of `Slot/Protocol.lean` with a view in which one provider's authority
is retired. Gate: the theorem for every `n`, by induction on `RunsR`. Red: the depth-`n` nesting makes
the justification depend on the order of resolution in a way the product does not capture, in which
case nested justifications are traces only and T1 must be weakened to a per-step statement.

After these: `star_stabilises` with D4 and the journal as instances (T6), and the repair file (T2),
which depend on E1.

## 11. What it does not unify

- The object layer's fixed point, laziness, sharing, reflection and `prototype` provenance.
  Structure II describes them and Structure I does not; the bridge is intentions only.
- The chooser's order. Who chooses, and in what order candidates are tried, is a choice function
  outside the semiring; `firstUnit` takes it as input. The civics are not algebra.
- Equi-recursive agreement, the checker, bidirectional completeness, the type lattice, coercions
  and quantities (`ALGEBRAIC-SUBTYPING` §5's open decision). The synthesis uses the row projection
  and nothing else from that work.
- The demand machine, adequacy, `≈b`, improvement theory, Iris-Lean, the leaf refinement, affinity.
- Dynamic dependencies: a nested fill's justification is a trace (T1), not a polynomial computable
  before the run; Mokhov's `Monad` case has no static semiring description.
- Modular syntax (Delaware), the `obend_cases` tactic, the hole exercise's cascade.
- Authority: signatures, hash commitments and collisions (D15), capabilities as tokens. A support is
  a fact the World answers; what makes the answer trustworthy is outside the model.
- The front end, parsing, rendering, the markdown reader, the CLI.
- Measurement of use by someone other than the maker.

INFERRED, last. The brief asked whether having the structure buys "fewer theorems, theorems that
transport, a kernel that is one construction rather than six". The count is: about thirty theorems
across `Slot`, `World`, `Integrity`, `Law`, `Doc`, `Journal` become instances of four lemmas
(`eval_congr`, `zero_mul` along `Later`, `firstUnit`, `star_stabilises`); the theorems that transport
are the congruence and retirement lemmas, which hold for any future judge written as a polynomial
(laws over packages, cites, leaf proofs, budgets); and the kernel's contextual half becomes one
module (`Just`) instantiated five times, while its object half stays Core4. Two constructions, not
one, and the second is the one the thesis is about.
