# Objective Bend: lazy open recursion over partial specifications, and its mechanized metatheory

Draft 2, 2026-10-30. Draft 1 is commit `9126123`; this revision adds prior art (§11), restates the
template instantiation path of §6 from the elaborator's code, re-reads §10 against the tree, and
brings the checker story of §3.5 and §8 up to date. Written against `origin/dev` at `e5fca29`
(`lean/`, Lean `v4.30.0`, no Mathlib); only what is committed there is described. For a reader who
knows Bend or Lean and has never seen minidregg.

Evidence words, as the trees use them. *Compiled*: Lean checked it, and where the check is
`native_decide` the claim rests on the compiler trust (`#assert_compiled`). *Proved*: a theorem in
the tree resting only on `propext`, `Classical.choice` and `Quot.sound`. *Executed*: a command was
run and its output is shown. *Integrated*: a host admitted it on a scratch world; every integration
claim lives in minidregg, outside this library, and this paper makes none of its own. *Deployed*:
nothing here is. Every theorem is cited by its `Obend.*` name; the module is the file under `lean/`.

## Abstract

Objective Bend is a calculus for building one object out of many partial pieces written by
different hands, without the pieces knowing each other. Its model is François-René Rideau's
("Faré") account of object orientation as modularity plus incrementality: a *specification* is a
first-class function from the eventual whole (`self`) and what has been built so far (`super`) to a
larger piece; two operations, `mix` and `fix`, compose specifications and tie the recursive knot.
The reference semantics is weak-head call-by-name, because a partial specification may mention
parts that do not exist yet; the machine is call-by-need with update frames. The checker is
proof-producing, types an extension against the members it uses rather than against a whole target
it has seen (templates over rigid `Self` and `Super`), and checks quantities (erased, affine,
linear, unrestricted). Effects are yields, not reductions. We describe the term language Core4
(23 constructors), its typing, the reflection contract that tells which equivalences
hold for which observers, and what the Lean development proves: determinism of the reference
semantics, soundness and finite completeness of the demand machine, type preservation and
no-refusal for checked terms, instantiation of templates, the composition contract, front-end
adequacy, checkpoint transparency, and, for the checker, both a proof that the annotation-directed
procedure is incomplete and a completeness theorem for a bidirectional one on a stated fragment. We say what it does not prove, among them that `mix` is
associative up to behavioural equivalence, that the surface language has a meaning of its own, and
that call-by-need costs no more than call-by-name. One correction to the literature is recorded:
the book's claim that C4 linearization is determined by a bare DAG is too strong; the invariance
that holds, and is checked on 4000 seeded DAGs, is under renaming of the *ordered* presentation.

## 1. The problem

Anyone who has watched several people, or several agents, build one thing meets the same shape.
The thing is a record of behaviours; each contributor writes one aspect; and each aspect is written
*before* the others exist. A review policy says how to combine judgments but needs a provider of
evidence it does not have. A pricing module reads a tax it did not write. The useful intermediate
object is incomplete on purpose: it cannot run, and it still has to be passed around, stored,
inspected and combined with a stranger's contribution.

Most languages answer this outside the language, with a closed executable per contribution and
build scripts, registries and conventions that reconstruct what each piece requires. The redregg
design note states the cost: requiring each contribution to be a closed executable before it can
be passed, stored, inspected or combined turns the useful intermediate object into something
outside the language. The alternative is to make the partial piece a *value*.

There is a second pressure. The laws people want from a shared object are judged at the point of
use: a predicate on one write of one object under the current authority, naming the clause that
refused. If ten hands built the object, ten sets of laws must combine into one judgment without a
fight and without any hand rewriting another's. That is a statement about *composition*: whose
contribution is counted, how often, in what order. It is why ancestry (§9) matters here. The law
layer itself is not part of what this paper covers: `Obend/Law` has landed in five steps
(the law's types, generators, meaning theorems over the reference step, `keeps` claims, inheritance
along a C4 precedence list; `lean/docs/REPORT-LAW-20261030.md`), no row of §8 is about it, and §10
says what it does and does not connect), and the cell laws that judge writes live in minidregg's kernel. What is here is the calculus underneath them.

Bend's answer to "laws plus proofs plus a fast compiler" rests on affinity: live code may not copy
a function, which lets a `match` free its node and gives fork-join parallelism for free. The thesis
of this repository (`THESIS.md` §1) is that for the object-and-law layer affinity is the wrong
load-bearing wall and Faré's object model the right one. It is stated so it can be wrong, and this
paper supports only the part about the calculus. With `THESIS.md`'s labels:

1. Core4 gives a reusable `self` a non-affine source semantics on purpose: `fix` hands one `self`
   to every layer. Bend can express a statically known family's late binding by generating names, a
   tag and a dispatcher; it cannot express Faré's first-class lazy `fix` and `mix` over a reusable
   record of methods as a value. (Unlabelled; the statement about Bend is `THESIS.md`'s reading of
   BendTT, not something this tree proves.)
2. Laziness is necessary for partial objects, not for every law system, and is compatible with
   parallel leaves. SUPPORTED by Core4's call-by-name reference; CONTESTED by nanodregg's
   call-by-value cut, which two mature instantiations in `DESIGN.md` §6 are built to settle by
   elaboration, not by a harness number.
3. The right linearity for a law system is Faré's, not Girard's. §2 and §9.
4. Laws are judged at the point of use. SUPPORTED everywhere in the trees; not in this library.
5. Extensible contextual theories (the slot) are the missing half. SUPPORTED as Lean theory with
   deployed instances; MISSING as anything usable without a journey file. One paragraph in §11.

It does not claim that Bend is wrong for fast pure numeric code, or that affinity is useless.
Core4 keeps Bend's quantities; §3.5 says what they check.

## 2. Faré's account, and the two equations

Faré's reconstruction of object orientation (poof, EOOMI, and the chapters of *The Land of the
Ultimate Object*, "ltuo", cited below) takes *modularity* and *incrementality* as the two ideas an
object system exists to provide, and makes both ordinary computation. A **specification** is an
extension: given the final whole and the inherited target, produce a result. In the self-first
convention these trees use, with `C` the final context, `V` the inherited target and `W` the
provided result, `Extension C V W = C → V → W` (the book writes the arguments super-first). The
three vary independently. A homogeneous `C = V = W` is a useful special case, not the general
operation: an extension may read a richer record than the one it extends, or change representation.
For a fixed `C`, heterogeneous extensions form a category; a neat homogeneous theorem would have
hidden lost expressiveness.

Two operations do the work. Composition feeds every layer the *same* final self and each layer the
whole result below it, and `fix` ties the recursive context when a construction is ready to close:

> mix parent child = λself. λsuper. child self (parent self super)
>
> fix spec inherited = spec (fix spec inherited) inherited

§3.2 shows them as the reduction rules they are. The word "equations" needs a caution Faré makes
himself: **`fix` is a computation, not an equation.** Every value solves `x = identity x`, yet the
operational `fix identity` has no weak-head result. The operational rule is the meaning.

**`self` and `super` differ.** If one layer counts parts from `self.parts` and later layers add
parts, the count must see the *final* collection: that is `self`. A layer that wraps the inherited
result needs that particular inherited meaning, not another lookup through the final whole: that is
`super`.

**Laziness is a semantic choice here.** Open recursion does not logically force an evaluation
strategy; strict systems can support guarded methods with explicit indirection. The reading Core4
aims at preserves arbitrary computational targets, incomplete recursive constructions and the usable
parts of partially defined objects, which eager demand of the whole construction can destroy before
any wanted part exists. Two tests separate the choices, both real programs in §3.3:
`keep(7, fix(identity))` must be 7, and `{good=7, bad=self.bad}.good` must be 7 though `bad` is
cyclic. Suspending the record is not enough; forcing it would force every field.

**Conflation.** A prototype pairs a specification with the target built from it, so reflection can
reach the specification without forcing the target (ltuo §2.3.3, §6.1). §4 says what reflection may
see.

**Linearity as conservation.** Faré (ltuo §7.3.5.2) names a property of *composition*: the
information contributed by each ancestor's extension shall be taken into account once and only once,
so that conforming languages "replace conflict with cooperation". It is the Flavors innovation of
1979, named after linear logic, and it concerns how contributions combine, not how a variable is
used. Core4 has both notions, kept apart: quantities (§3.5) concern variables; the identity of an
ancestor in C4 (§9) concerns contributions.

## 3. Core4

### 3.1 The term language

`Obend.Core.Term.Term` is the whole language. There are 23 constructors and 10 scalar primitives.

| Constructor | Meaning |
| --- | --- |
| `bound`, `lam`, `app` | de Bruijn variable, abstraction, application (β; the machine makes the argument one shared cell) |
| `mix lower upper`, `fix spec inherited` | the two rules of §2 |
| `specification metadata extension` | a value; applying it applies `extension`; `metadata` is reachable without forcing `extension` |
| `prototype spec target` | a value pairing a specification with its target |
| `reflect p`, `metadata s`, `project p` | the specification of a prototype, the metadata of a specification, the target of a prototype; none forces the other component |
| `nat`, `boolean`, `label` | scalars; naturals are unbounded, labels are opaque strings and are not Booleans |
| `binary p l r` | strict left to right; `p` is one of `add multiply equal conjunction labelEqual subtract divide less lessEqual modulo`, each one machine step |
| `record fs`, `extend r fs`, `get t name` | records of separate suspensions (first match wins), override, selection by a static name |
| `ifZero v z s` | case on a natural; the successor branch binds the predecessor |
| `inject l p`, `case s arms`, `ifBool c t f` | sums (a lazy injection, case on its label) and the Boolean branch |
| `perform plan`, `done v` | an activity yields a Plan and is resumed with a response; `done` returns a pure value from an activity |

The scalars are exact and total where they could be partial: `Obend.Core.Term.subtract_truncated_exact`
(truncated at zero), `Obend.Core.Term.divide_floor_exact` (floor division, `a / 0 = 0`),
`Obend.Core.Term.divide_modulo_reconstruct` (`(a / b) * b + a % b = a` for every `b`, zero
included), `Obend.Core.Term.order_exact`. Labels compare only with labels
(`Obend.Core.Term.label_equality_booleans_refused`). There is no digest primitive and no
computed-name `get`: field selection is by a static name, which is part of why a `case` on a label
is the only dynamic dispatch.

### 3.2 The two rules

The reference relation is `Obend.Core.Term.Step`, a small-step weak-head call-by-name relation.
`mix` is a rule that unfolds to a definition, `mixBody`; `fix` is one rule.

```lean lean/Obend/Core/Term.lean:150-154
/-- `λself. λsuper. upper self (lower self super)`: the inherited target is a
computation; both extensions receive the identical final self expression. -/
def mixBody (lower upper : Term) : Term :=
  .lam (.lam (.app (.app (upper.rename (fun n => n + 2)) (.bound 1))
    (.app (.app (lower.rename (fun n => n + 2)) (.bound 1)) (.bound 0))))
```

```lean lean/Obend/Core/Term.lean:252-254
  | mix (lower upper : Term) : Step (.mix lower upper) (mixBody lower upper)
  | fix (spec inherited : Term) :
      Step (.fix spec inherited) (.app (.app spec (.fix spec inherited)) inherited)
```

`mixBody` is the first equation of §2 with de Bruijn indices: under two binders, index 1 is the
final self and index 0 the inherited target, and both extensions are applied to the *identical*
`bound 1`. `fix` unfolds by passing the whole `fix` expression back as the self. Nothing else in
the language knows about objects. A record is a value, `extend` overrides fields of a record, and a
class hierarchy, a method table or a prototype is a pattern of these.

The checker gives the same two rules typing rules (`Obend.Core.Check.PartialTyping`, constructors
`mix` and `fix`). In `mix`, `lower : self → inherited → middle`, `upper : self → middle → provided`,
and the result is `self → inherited → provided`: composition is heterogeneous by construction. The
`fix` rule is homogeneous, `target → inherited → target`, and is below.

```lean lean/Obend/Core/Check.lean:254-261
  | fix {context : Context} {spec inheritedTerm : Term} {specType inherited target : Ty} {su iu : Uses} :
      PartialTyping assumptions context spec specType su →
      callable specType = .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target) →
      PartialTyping assumptions context inheritedTerm inherited iu →
      target.shareableUnder assumptions.shareableVariables = true →
      argumentAllowed assumptions .unrestricted context inherited iu = true →
      reusableCaptures assumptions.shareableVariables context su = true →
      PartialTyping assumptions context (.fix spec inheritedTerm) target (addUses su iu)
```

The side conditions are the content. Both rules require the closure's captures to be reusable
(`reusableCaptures`), and the self, inherited and middle types, or the fix target, to be
*shareable* under the explicitly checked premises on rigid variables. Shareability is what keeps an
activity, a one-shot closure or a custody value from being handed to every layer: `self` is used
as many times as there are methods, so what it contains must survive being used many times.

### 3.3 Reference semantics: call-by-name, and what laziness means

A value (`Obend.Core.Term.Value`) is a lambda, a scalar, a record, a specification, a prototype or an
injection. `Evaluates t v` is `Steps t v` with `Value v`. The relation is deterministic
(`Obend.Core.Proofs.Adequacy.sourceStep_deterministic`, `Obend.Core.Proofs.Adequacy.source_evaluates_unique`),
including fixed-point unfolding and field shadowing. Because the argument of a β-step is substituted
unevaluated, a function that ignores its argument ignores a divergent one:
`Obend.Core.Check.ignores_any_partial_argument` proves `Evaluates ((λ. 7) a) 7` for every term `a`,
a divergent `fix` among them. This is `keep(7, fix(identity))`. As a program:

```obend lean/tests/obend-source/LazyUnusedArgument.obend
edition ObjectiveBend 1

def keep(first: Nat, ignored: Nat) -> Nat:
  first

def result() -> Nat:
  keep(7n, fix(extension(self: Nat, super: Nat) -> Nat: self, 0n))
```

and the field version, where the cyclic `bad` is never demanded:

```obend lean/tests/obend-source/LazyUnusedField.obend
edition ObjectiveBend 1

record Pair:
  good: Nat
  bad: Nat

extension Fields(self: Pair, super: Pair) -> Pair:
  {good: 7n, bad: self.bad}

def result() -> Nat:
  fix(Fields, {good: 0n, bad: 0n}).good
```

Both executed on the built `obend` of this tree:

```sh
$ obend run tests/obend-source/LazyUnusedArgument.obend result
status: finished
type: Nat
result: 7

$ obend run tests/obend-source/LazyUnusedField.obend result
status: finished
type: Nat
result: 7
```

Under call-by-value the first diverges at the argument and the second at the record. The reference
semantics is call-by-name because it is the simplest relation with these properties, and because it
is *independent*: it is defined with no heap, so a theorem relating it to the machine says
something external to the machine's own implementation.

### 3.4 The demand machine

Call-by-name re-evaluates an argument at each use. The machine, `Obend.Core.Machine`, is
call-by-need. A state is a heap of cells, a control and a stack (`Obend.Core.Machine.State`). A cell
is `suspended` (an expression and its environment), `evaluating`, or `cached` (with its value). An
`enter` of a suspended cell marks it `evaluating` and pushes an `update` frame; the value returned
to that frame is written back as `cached`. Entering an `evaluating` cell is a **blackhole**, a
non-result divergence observation, not a catchable exception. Every argument and every record field
is one shared cell. `fix` ties exactly one address to itself:

```lean lean/Obend/Core/Machine.lean:117-120
    | .fix spec inherited =>
      let address := state.heap.size
      let body := Term.app (Term.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ)
      {state with heap:=state.heap.push (.suspended ⟨body,address::environment⟩),control:=.enter address}
```

The new cell's environment is its own address pushed on the old one, and the body passes `bound 0`,
that cell, as the self: one shared thunk per allocated identity, not a memo table over equal calls.

The machine is bounded. `runBounded limits ticks` returns one of five outcomes
(`Obend.Core.Machine.Outcome`): `finished`, `suspended` (out of ticks, or out of heap or stack
room, retaining the exact state, so raising a bound never loses control), `divergent`
(blackhole), `refused` and `yielded`. Resource exhaustion is a suspension, never an error. The
compiled code does not run `stepRaw`; it runs a faster machine, with the equality as a theorem
(`Obend.Core.MachineFast.runBounded_eq_fast`, a `@[csimp]` replacement; the compiler's use of it is
trusted, the equality is proved).

**What relates the machine to the reference.** The machine's cyclic heaps cannot be related to
reference terms by finite textual unfolding, so the development uses a graph relation:
`GraphRepresentsBy` gives every address a permanent meaning as a closed term, and a stack is a
context around a focus. On it:

- *Soundness.* A finished bounded run of a closed term is a reference evaluation of it:
  `Obend.Core.Proofs.Adequacy.runBounded_value_sound` for any weak-head value (through the
  meaning of the heap), `Obend.Core.Proofs.Adequacy.runBounded_observation_sound` for ground
  observations. Two finished runs under different limits observe the same
  (`Obend.Core.Proofs.Adequacy.runBounded_resource_independent`).
- *Finite completeness.* A closed term the reference evaluates to an observable value is finished by
  the machine in finitely many steps: `Obend.Core.Proofs.Completeness.rawRun_finite_completion`,
  and in the contract's form `Obend.Core.Proofs.Completeness.machine_evaluation_complete`. The
  machine inhabits the reference `Obend.Core.Term.Representation` for every closed source
  (`Obend.Core.Proofs.Completeness.coreRepresentation`). The proof is a lexicographic descent on the
  residual source cost and a stutter rank, so a transition either does a genuine reference
  reduction of the whole residual program or strictly decreases a syntactic potential of the machine
  state.
- *Laziness and sharing, in the executor.* An unused argument, a divergent `fix` included, stays
  suspended at its original address (`Obend.Core.Proofs.Adequacy.unused_argument_executor`), and the
  second demand of a shared argument sees the first demand's cache at the identical address
  (`Obend.Core.Proofs.Adequacy.shared_argument_executor`).

The two executor theorems are fixtures, general in the argument or the number but about one program shape. The
cost claim that matters is not a theorem: the tree states none that call-by-need never costs more
than call-by-name. What a shared field buys is visible in an executed program:

```obend lean/tests/obend-source/LazySharedField.obend
edition ObjectiveBend 1

record Pair:
  costly: Nat
  twice: Nat

def work(n: Nat) -> Nat:
  match n:
    case 0n: 1n
    case 1n+pred: work(pred) + work(pred)

extension Fields(self: Pair, super: Pair) -> Pair:
  {costly: work(8n), twice: self.costly + self.costly}

def result() -> Nat:
  fix(Fields, {costly: 0n, twice: 0n}).twice
```

```sh
$ obend run tests/obend-source/LazySharedField.obend result
status: finished
type: Nat
result: 512
```

`work(8)` is 256 and is demanded twice through `self.costly`; call-by-name would compute it twice,
the machine once. The tree proves the values agree; it does not prove the cost difference, which is
the reason for the machine.

### 3.5 Types and quantities

`Obend.Core.Ty.Ty` has twelve constructors: the scalars; `variable` (a rigid or bounded variable);
`arrow` carrying a *reuse* (`once` or `reusable`) and a *quantity* for its parameter; the rows
`emptyRow` and `field name member tail`, where a row tail is kept and never flattened;
`specification`, `prototype`, `variant` (a sum over the labels of a row, closed when its tail is
`emptyRow`); `custody` (an identity that must not be copied); and
`computation plan response result`, the type of an activity.

The checker `Obend.Core.Check.check` is *proof-producing*: it returns `Checked`, a record containing
a `PartialTyping` derivation of the term it was given (`Obend.Core.Check.checked_erasure`, which is
a projection, and says so). Four design points.

*Rows are compared canonically.* There is no subtyping. Type agreement, `Obend.Core.Check.sameType`,
is exact up to canonical row order (first field of a name wins) and the unfolding of declared alias
variables at the head, repeated: it is the equivalence closure of the one-step agreement
(`Obend.Core.Check.sameType_equivalence`), decided by testing whether the two head-unfolding orbits
meet within as many steps as there are declared bounds (`Obend.Core.Check.Assumptions.chase_bounded`
is why that bound is exact). It does not descend into constructors, so an alias-domain arrow and the
arrow it names stay distinct, and a rigid variable is never unfolded. Canonical form forgets a
shadowed row member only if that member is shareable
(`Obend.Core.Proofs.CheckTeeth.canonical_agreement_keeps_shareability`), so a conversion cannot launder a custody
value. A bounded variable keeps its row tail, so a method can be typed against a future self it has not
seen (`Obend.Core.Proofs.CheckTeeth.future_row_instantiation_accepted`), and a `mix` may join layers
with different inherited, middle and provided types
(`Obend.Core.Proofs.CheckTeeth.heterogeneous_runtime_mix_accepted`).

*Quantities are `erased`, `affine`, `linear` and `unrestricted`, and the checker enforces at most
once for both affine and linear.* The reason is in the source: a partial computation may retain a
linear obligation forever, so exactly-once cannot be inferred for arbitrary recursion; it is
checked separately for terminal ownership protocols. What is proved is the safe bound
(`Obend.Core.Ty.safe_use_bound`) and that duplicating an affine use is refused
(`Obend.Core.Proofs.CheckTeeth.duplicate_affine_refused`). The tutorial program `twice(affine x)`
returning `x + x` is refused with "ownership refused" when run; `droppedLinear(linear y)` returning
`0` was accepted while "linear" meant at most once; since 2026-11-01 a `linear` binder must be used exactly once (`linearBinderUnused`), and this example is held as a deviation from Mini.

*A reusable closure captures only unrestricted, shareable bindings*
(`Obend.Core.Check.reusable_lambda_capture_rule`). Shareability looks through wrappers: a record
cannot hide a custody value (`Obend.Core.Proofs.CheckTeeth.record_wrapper_does_not_hide_custody`),
and a conversion the checker inserts never manufactures it
(`Obend.Core.Check.agree_never_manufactures_shareability`), because canonical equality forgets a
shadowed field and a row hiding a custody value behind one would otherwise equal a shareable row.

*An activity type is never shareable* (`Obend.Core.Check.computation_not_shareable`), so no
activity can sit in a field, an argument, a payload or a Plan. §7 returns to this.

The checker is sound for its derivation type and not complete for it. Fuel is monotone
(`Obend.Core.Proofs.Substitution.check_mono`), and `Obend.Core.Proofs.CheckCompletenessObstruction.checked_does_not_imply_eventual_success`
exhibits a term that has a `Checked` certificate but is refused at every fuel (a lambda with no
annotation: annotations are inputs to the checker, not inferred). A second, bidirectional procedure
exists beside `check` and is complete on a named fragment; §8.1 states both results and where each
stops. The front end still admits programs with `check`. The tree separates *meaning*,
which is existence of a derivation, from *procedure*, which is `check` at a granted fuel.
`Obend.Core.Graded` is the monoid of grades the procedure is indexed by. Nothing in a statement
about meaning mentions fuel.

Well-typed does not mean terminating. Typed programs can diverge, and the theorems of §8 never say
otherwise.

## 4. Specifications, prototypes and the reflection contract

At the surface, every specification has one type, `Specification<T>`, which in Core4 is
`Ty.specification metadata extension`: the pair of a metadata value and an extension
`T → T → T`. The metadata is *ordinary data*, a built-in sum:

- `declared`: a name, an interface label (a JSON text that includes the C4 precedence list, §9) and a
  list of claims, each with a name and a status;
- `composed`: the metadata of the inherited and the wrapping operand;
- `extension`: a bare extension carries none.

`compose(a, b)` is `specification(composed{inherited: P a, wrapping: P b}, mix a b)`, where `P x` is
`metadata(x)` for a specification and `extension{}` for a bare extension. Laws, ancestry and
composition change the metadata *value*, never the type, so `Specification<T>` is closed under
`compose` at every shareable target (`Obend.Spec.Proofs.SpecificationClosure.composeTy_closed`,
`Obend.Spec.Proofs.SpecificationClosure.compose_wrapper_typed`) and a function like
`def twice(e: Extension<Nat>) -> Specification<Nat>: compose(e, e)` checks
(`Obend.Spec.Proofs.SpecificationClosure.twice_accepted`, compiled).

Why ordinary data and not an opaque metadata parameter: an existential would need a new Core4 type
former and a packing rule, so every machine preservation proof would grow a case, and a client could
observe nothing of provenance. Metadata as data needs no change to Core4, keeps every safety theorem,
and lets a program inspect provenance with `match`. The cost is that metadata cannot carry closures,
which is the right cost: a closure nobody calls is a promise nobody keeps. A spec's `claim` is typed
to return Boolean and is listed with the status `unchecked`; nothing evaluates it
(`Obend.Spec.Proofs.SpecificationClosure.claim_spec_accepted`, compiled, shows it is accepted, not
that it holds).

### The observers

Every observer is a reason two programs that compute the same answers are nonetheless different,
and every rewrite law ("compose is associative") holds only for the observers that cannot see the
difference. So the observers are listed.

| Observer | Sees | Runs the extension? |
| --- | --- | --- |
| `metadata(s)` | the `SpecMeta` value | no |
| `reflect(p)` | the specification stored in a prototype | no |
| `targetOf(p)` | the target stored in a prototype | forces the target only |
| application, `fix(s, seed)`, `mix` | the extension's behaviour | yes |
| `==` on `String` fields of `SpecMeta` | names, interfaces, law names and statuses | no |

There is no observer of a closure's code, of a law's code, of the interface label's structure other
than as a string, or of heap identity. The first three rows are `Core4`'s `metadata`, `reflect` and
`project`; `Obend.Core.Term.prototype_metadata_unforced` and
`Obend.Core.Term.specification_metadata_unforced` say that `reflect` and `metadata` step without
touching the other component. Those two are one reduction each; they are what the rules are
*designed* to give, not deep results.

Two equivalences follow. Behavioural `a ≈b b`: for every well-typed seed and every context that uses
`a` and `b` only through application, `fix` and `mix`, completed runs agree. Informally `mix` is
associative up to `≈b`, because both associations run `C self (B self (A self super))`. Reflective `a ≈r b`: `≈b`
and equal metadata. Associativity fails up to `≈r`: the two associations have different `SpecMeta`
trees, and a program can tell them apart.

```obend lean/tests/obend-source/ltuo/AssociationProvenance.obend
edition ObjectiveBend 1
# LTUO probes R01/R02 (reflection contract, docs/objective-bend/REFLECTION.md). The two
# associations of compose behave alike (W03) and share one type, but their SpecMeta
# provenance differs and a program can observe it: associativity holds for behaviour,
# not for reflective specifications.

record Counter:
  n: Nat

spec A for Counter:
  def n() -> Nat:
    super.n + 1n
spec B for Counter:
  def n() -> Nat:
    super.n * 2n
spec C for Counter:
  def n() -> Nat:
    super.n + 3n

def isComposed(meta: SpecMeta) -> Bool:
  match meta:
    case declared(d): false
    case composed(c): true
    case extension(e): false

def inheritedOf(meta: SpecMeta) -> SpecMeta:
  match meta:
    case declared(d): meta
    case composed(c): c.inherited
    case extension(e): meta

def leftNested() -> Bool:
  isComposed(inheritedOf(metadata(compose(compose(A, B), C))))

def rightNested() -> Bool:
  isComposed(inheritedOf(metadata(compose(A, compose(B, C)))))
```

```sh
$ obend run tests/obend-source/ltuo/AssociationProvenance.obend leftNested
status: finished
type: Bool
result: true

$ obend run tests/obend-source/ltuo/AssociationProvenance.obend rightNested
status: finished
type: Bool
result: false
```

Executed. That is the whole of what is established. **Neither equivalence is a theorem.** The tree
does not define `≈b` and does not state associativity of `Term.mix`; a rewrite justified by `≈b` may
be applied only where no `metadata` observer can reach the rewritten specification. Equal answers on
completed runs also do not imply equal ticks, heap or outcome under one budget, so a
resource-preserving rewrite needs its own statement, which none has.

### Prototypes

`prototype(spec, target)` is a raw lazy pair: its typing checks the components independently
(`Obend.Core.Check.PartialTyping`, constructor `prototype`), so `reflect(p)` returns what was stored and
proves nothing about how `targetOf(p)` was built. A sound reflective constructor would establish
provenance by construction, `instantiate(spec, seed) = prototype(spec, fix(spec, seed))`, with a
theorem relating `targetOf` to `fix`. `Obend.Core.Term.instantiatePrototype` is a definition of that
shape, tying the knot *inside* the recursion so `self` is the whole prototype (Faré's treatment:
wrapping only the already-built result is too late). No theorem in the tree mentions it, and the
surface language does not use it. Whether reflective self-reference goes inside the knot or outside
it is an open decision, listed in §10.

## 5. The surface language and the package knot

`.obend` source is lowered by a front end (`Obend.Spec`) to a Core4 term plus a typing proposal, and
the proof-producing checker either accepts the proposal with a derivation or refuses it. A source
file starts with `edition ObjectiveBend 1`. Here `Review` is built from three specifications
written separately. `Twice` declares that it needs `review` from the final self; `Augmented` wraps
the inherited `review` through `super`:

```obend lean/tests/obend-source/examples/Review.obend
edition ObjectiveBend 1

record Review:
  review(value: Nat) -> Nat
  twice(value: Nat) -> Nat

spec Base for Review:
  def review(value: Nat) -> Nat:
    value + 1n

spec Twice for Review:
  requires review(value: Nat) -> Nat
  def twice(value: Nat) -> Nat:
    self.review(self.review(value))

spec Augmented for Review:
  def review(value: Nat) -> Nat:
    super.review(value) + 1n

def reviewOfThree() -> Nat:
  fix(compose(Base, Twice, Augmented), {}).review(3n)

def twiceOfThree() -> Nat:
  fix(compose(Base, Twice, Augmented), {}).twice(3n)
```

`super.review(3)` is `Base`'s 4, so the final `review(3)` is 5. `twice` reads `review` through
`self`, the final, augmented `review`, so `twice(3)` is `review(review(3)) = review(5) = 7`.

```sh
$ obend run tests/obend-source/examples/Review.obend reviewOfThree
status: finished
type: Nat
result: 5

$ obend run tests/obend-source/examples/Review.obend twiceOfThree
status: finished
type: Nat
result: 7
```

The seed is `{}`; each layer is typed at the row actually beneath it, so no placeholder methods are needed (§6).

### Where the surface stops being proved

The front end is **trusted, with no theorem**: the parser, the elaborator's choices (including its
typing proposal) and the C4 implementation. There is no surface semantics, so nothing states that
the core term means what the source means. What is proved is about the output of the front end
(§8, `Obend.Spec.Proofs.FrontEndAdequacy`). The statement of the boundary is the header of
`lean/Obend/Spec.lean`. This is the same boundary as its predecessor's, and a conformance harness
(`lean/tests/run-obend-source.py`) holds the port to the pinned outcomes of 30 probes, 71 tutorial
commands and a 161-item preview cohort; a differing outcome is a port defect, not a new truth.

### The package is a specification

Every global declaration is a field of one record knot, so mutual recursion works through it. The
root is itself a specification: `fix(specification({package: ...}, λ$globals λ$seed. extend $seed
{M.decl: ...}), {})`, and a global reference is `get $globals "M.name"`. The root extends its
inherited row, but **no surface form names another package's root**, so another package cannot yet
extend it. Within a package Objective Bend is object-oriented; across packages it is object-based.
This is the gap Faré's audit of minidregg found, and closing it is the first item in §10.

What does work across packages is composition of *specifications*. Three files, written separately:
`Shop` declares the record every package targets, `Pricing` prices and totals and reads `tax`
through the final self, `Taxes` computes tax from the final `price`.

```obend lean/tests/obend-source/three-package/Shop.obend
edition ObjectiveBend 1
# Row D three-package case, shared part: the record every package targets.
record Store:
  price(n: Nat) -> Nat
  tax(n: Nat) -> Nat
  total(n: Nat) -> Nat

def blank() -> Store:
  {price: fn(n: Nat) -> Nat: 0n, tax: fn(n: Nat) -> Nat: 0n, total: fn(n: Nat) -> Nat: 0n}
```

```obend lean/tests/obend-source/three-package/Pricing.obend
edition ObjectiveBend 1
# Package A: prices and the total. It reads tax and price through the FINAL self.
import ./Shop.obend as Shop

spec Pricing for Shop.Store:
  requires tax(n: Nat) -> Nat
  def price(n: Nat) -> Nat:
    n * 10n
  def total(n: Nat) -> Nat:
    self.price(n) + self.tax(n)
```

```obend lean/tests/obend-source/three-package/Taxes.obend
edition ObjectiveBend 1
# Package B: the tax, authored without A. It reads price through the FINAL self.
import ./Shop.obend as Shop

spec Taxes for Shop.Store:
  requires price(n: Nat) -> Nat
  def tax(n: Nat) -> Nat:
    self.price(n) * 2n
```

A fourth package integrates the other two without editing them and overrides `price`:

```obend lean/tests/obend-source/three-package/Integration.obend
edition ObjectiveBend 1
# Package C: integrates A and B without editing them and overrides price. A s total
# and B s tax must both see C s price: 100 + 200 = 300 (A and B alone: 10 + 20 = 30).
import ./Shop.obend as Shop
import ./Pricing.obend as A
import ./Taxes.obend as B

spec Premium for Shop.Store:
  def price(n: Nat) -> Nat:
    n * 100n

def integrated() -> Nat:
  fix(compose(A.Pricing, B.Taxes, Premium), Shop.blank()).total(1n)

def unintegrated() -> Nat:
  fix(compose(A.Pricing, B.Taxes), Shop.blank()).total(1n)
```

`Pricing.total` and `Taxes.tax` both see `Integration`'s `price`: 100 + 200 = 300, against 10 + 20 =
30 without it. The two numbers are the cohort items `D1-ThreePackageFinalSelf` and
`D1b-TwoPackageBaseline` of `lean/tests/obend-source/preview-cohort.json`, run by
`lean/tests/run-obend-source.py` through multi-module capture. They were not re-run for this paper.

## 6. Modular typing

A specification should be typed against what it *uses*, not against a whole target it has seen.
Faré's chapter 8 draws the line between typing an extension against one already-known complete
context ("trivial non-modular types") and typing it against only what it reads, so it survives
collaborators that did not exist when it was written. The first front end did the former:
`spec S for T` typed both `self` and `super` as the whole `T`, so a one-method spec needed a
whole-`T` seed, `requires` was a string nobody compared, a record could not name itself, and an
extension written for three fields could not be reused at four. Core4 already had the ingredients,
bounded variables that keep row tails, lookup-based width checking and heterogeneous `mix`. What was
missing was an authored binder, a discipline that checks an extension against its binder alone, and
a closing rule that discharges the binder at `fix`. The decisions, with their labels in the design
record, D1 to D6:

- **D1. Templates, not polymorphic core terms.** An open declaration is a *template*, checked once
  against its bounds with `Self` and `Super` rigid; every use is an *instance* with the actual
  final self and inherited types substituted. The emitted program contains only instances, so it is
  an ordinary closed Core4 program.
- **D2. Rigid variables are not aliases.** An ordinary bounded variable is equal to its bound. A
  template's `Self` is a *lower* bound: the instance supports it, it is not equal to it
  (`Obend.Core.Check.Assumptions.alias_rigid`; with `rigid = []` the checker is the old checker,
  `Obend.Core.Check.Assumptions.alias_of_rigid_nil`).
- **D3. Closed specs get an open inherited row.** `spec S for T` keeps `self : T` but types `super`
  at the members `S` reads through it.
- **D4. `requires` is the Self bound, and it is checked** (`refused (requires-signature)`).
- **D5. `fix` discharges.** `fix(compose(L1, ..., Ln), seed)` types the chain bottom-up from the
  seed; the final row must be the target.
- **D6. Recursive records are nominal**, distinct from the F-bounded binder: `Node` is one closed
  recursive type, while `Self has {combine(other: Self) -> Self}` ranges over every future type
  with such a method.

### Why templates and not a polymorphic core

A core `forall` would add a case to every machine preservation proof. With templates the machine
theorems keep their statements and proofs, and the new obligation is one checker-level theorem.
Nothing below Core4 ever sees an open term: the checker and the machine receive a closed program.
The costs are real and recorded: code grows with the number of distinct instances (memoized, one
knot field per substitution), and an open template is second-class (a parameter can be any closed
`Extension<T>`, not "any extension over `Self has {x}`").

Open declarations are written with binders. `AddY` is written knowing only `x`, and is used under a
four-field self:

```obend lean/tests/obend-source/examples/Modular.obend
edition ObjectiveBend 1

record XY:
  x: Nat
  y: Nat
record XYZW:
  x: Nat
  y: Nat
  z: Nat
  w: Nat

extension AddY[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:
  extend(super, {y: 2n * self.x})

extension AddZW(self: XYZW, super: XY) -> XYZW:
  extend(super, {z: self.y, w: self.z + 1n})

def wOfFive() -> Nat:
  fix(compose(AddY, AddZW), {x: 5n}).w
```

```sh
$ obend run tests/obend-source/examples/Modular.obend wOfFive
status: finished
type: Nat
result: 11
```

`AddY` is checked once, at its own bounds, with `Self` and `Super` rigid: the body may read `self.x`
and nothing else. `Super with {y: Nat}` keeps whatever else `Super` has. The tooth for rigidity is
a program that passes `self` where a value of exactly its bound row is expected. An alias checker
would accept that at `AddY`'s own bounds and refuse only the wider instance, anonymously; the
template check refuses it at the declaration, by name:

```sh
$ obend run tests/obend-source/ltuo/OpenSelfRigid.obend wOfFive
status: refused
stage: objective-core-elaboration
message: refused (self-rigid): open declaration OpenSelfRigid.AddY uses self as a value of its Self bound row; ...
```

(`OpenSelfRigid.obend` is `Modular.obend` with `AddY`'s body changed to
`extend(super, {y: firstX(self)})`, where `firstX` takes exactly `{x: Nat}`; the message is
shortened.) The same fact is a theorem about the checker, as the acceptance and the refusal of two
instances of one term: `Obend.Core.Proofs.Templates.self_as_bound_row_alias_accepted` and
`Obend.Core.Proofs.Templates.self_as_bound_row_rigid_refused`, both by `decide`.

F-bounds make a binary method typed against the future self:

```obend lean/tests/obend-source/examples/Heavier.obend
edition ObjectiveBend 1

record Node:
  weight: Nat
  heavier(other: Node) -> Node
record ColoredNode:
  weight: Nat
  color: Nat
  heavier(other: ColoredNode) -> ColoredNode

spec Heavier[Self has {weight: Nat, heavier(other: Self) -> Self}, Super has {weight: Nat}]:
  def heavier(other: Self) -> Self:
    if other.weight <= self.weight then self else other

def node(n: Nat) -> Node:
  fix(Heavier, {weight: n})

def colored(n: Nat, c: Nat) -> ColoredNode:
  fix(Heavier, {weight: n, color: c})

def pick() -> Nat:
  node(3n).heavier(node(5n)).weight + colored(2n, 7n).heavier(colored(1n, 9n)).color
```

```sh
$ obend run tests/obend-source/examples/Heavier.obend pick
status: finished
type: Nat
result: 12
```

`Heavier`'s `heavier(other: Self) -> Self` becomes `heavier(other: Node) -> Node` at `node` and
`heavier(other: ColoredNode) -> ColoredNode` at `colored`, by substitution inside the bound.

### The theorem, and what it is not

What is proved at the checker (`Obend.Core.Proofs.Templates`): `canonical_instantiate`, that canonical
form commutes with instantiation up to a final canonicalization (including the override case, where
an instantiated tail repeats a listed field), is the technical heart. On it,
`Obend.Core.Proofs.Templates.Discharges.infer_instantiate` and
`Obend.Core.Proofs.Templates.Discharges.check_instantiate` say that a template the checker accepts under
rigid bounds is accepted at every substitution that discharges them, at the instantiated type, with
the same uses, given a fixed amount of extra fuel (`extend`'s row check reads `isRow` at fuel + 64 for
this reason). The theorem is inhabited by a real example
(`Obend.Core.Proofs.Templates.coloured_discharges`, `Obend.Core.Proofs.Templates.coloured_instance_accepted`).

What admission *relies on* is not that theorem. This is what the elaborator does
(`Obend.Spec.Elaborate`, read at `e5fca29`; I traced it by reading, and ran nothing).

1. `templateLayer` elaborates an open declaration once, at its own bounds, with `Self` and `Super`
   its two bounded variables, and caches `(Self index, Super index, layer)` under the declaration's
   key. That layer is the declaration's own knot field, and `Obend.Spec.FrontEnd.checkTemplates`
   checks each such field once with those variables rigid (`refused (self-rigid)`,
   `(super-rigid)` or `(template-typing)`).
2. `chainFix` lowers a `fix` over a chain of declared specifications when some layer is open, or all
   are closed specs and the seed is not already a whole target. It walks the chain bottom-up,
   holding `below`, the row beneath the current layer, which starts as the canonical type of the
   seed. For an open layer it resolves the layer's bounds at `Self = target`, `Super = below`, runs
   the read clause and the write clause of the composition contract (`Contract.checkBounds`,
   `Contract.checkProvides`) and emits an instance.
3. The instance is `ATerm.retarget annotated arity (layer.instantiate σ)` with
   `σ = {Self ↦ target, Super ↦ below}`. `ATerm.instantiate` substitutes σ into the *type
   annotations* of the cached term and canonicalizes them, and does nothing else; `retarget`
   re-annotates the result type of the `arity`-parameter function as `annotated` (the layer's
   provided row, or the target variable itself for the last layer of a recursive record target).
   `arity` is 2 for an open spec and the parameter count for an open extension.
4. Instances are memoized by (declaration, target, `below`, `annotated`) and emitted as hidden knot
   fields named `key@n`, so one distinct row context gets one field. A closed spec in the chain is
   not instantiated at all: `layerAt` elaborates it afresh at (target, `below`, `annotated`). A
   closed extension is referenced as a global, and is refused `inherited-mismatch` if its declared
   `super` is not the row beneath.
5. After the last layer, `Contract.close` compares the final row with the target, the operands are
   joined with `mix` and the chain is tied with `fix` over the seed.

So the emitted instance is the checked template with its annotations rewritten, and the claim
that the template at σ equals the instance is made by a comment in the code ("holds by
construction"), not by a theorem. `ATerm.instantiate` acts on the front end's annotated terms and
types; `Discharges.check_instantiate` is about Core4's `AnnotatedTerm` and `Ty`; nothing in the tree
relates the two. The whole closed program, instances included, is then checked by `Check.check`, and
that check is the one that counts. No front-end corollary of `check_instantiate` is claimed, because
no check depends on one: a translation defect it would rule out is still caught by the
whole-program check, as an anonymous typing refusal.

### The composition contract

Each layer of `fix(compose(L1, ..., Ln), seed)` has a contract: what it *assumes* of the final self
(its `Self` bound and `requires`), what it *consumes* from the row beneath (its `Super` bound), and
what it *provides*. The front end decides every contract refusal by running one algebra,
`Obend.Spec.Contract`, and nothing else. With `F_L(S, I)` the row layer `L` leaves,

> C_{A;B}(S, I) = C_A(S, I) and C_B(S, F_A(S, I)),   F_{A;B} = F_B after F_A

which is `Obend.Spec.Contract.run_append`. Associativity of composition is therefore associativity of
`++` on chains (`Obend.Spec.Contract.run_assoc`); an admitted layer met every clause
(`Obend.Spec.Contract.checkLayer_ok`); and a discharged composition guarantees every member of the
final self has its declared type in the final row and nothing else is declared
(`Obend.Spec.Contract.discharge_ok`). The named refusals are `self-bound`, `inherited-unprovided`,
`replace-undeclared` (a layer may add a member or override one at the same type; a type change is a
replacement and no source form declares one), `requires-unprovided`, `seed-extra` and
`provided-mismatch`. For example, `lean/tests/obend-source/ltuo/RequiresUnprovided.obend` (a `spec Needs` that
`requires missing(...)`, which neither a layer nor the seed provides) is refused with
`refused (requires-unprovided)`, naming `Needs`.

The scope of these theorems is the contract algebra that the elaborator calls, not the source: they
say that the checks that run have the algebra's properties, not that the elaborator calls them on
every path. Ancestry specifications and non-plain operands in a `fix` chain keep the older
whole-target rule; instances across package roots are not addressed.

## 7. Activities: yield and resume

Effects are not reductions. An **activity** hands a typed Plan to its host, waits, and continues
with the typed response. `Activity<P, R, A>` yields Plans of the sum `P`, is resumed with data of
type `R`, and finishes with an `A`; in Core4 it is `computation P R A`. `match perform(plan):`
sequences, its arms being the handlers, and a pure tail is lifted with `done`.

```obend lean/tests/obend-source/examples/Counter.obend
edition ObjectiveBend 1

record Write:
  field: Nat
  before: Nat
  after: Nat

sum Plan:
  write: Write

sum Response:
  written: {}
  refused: {}

def bump(count: Nat) -> Activity<Plan, Response, Nat>:
  match perform(Plan.write({field: 0n, before: count, after: count + 1n})):
    case written(_): count + 1n
    case refused(_): count
```

The preview has no kernel; responses are supplied on the command line and checked against the
declared response type:

```sh
$ obend run tests/obend-source/examples/Counter.obend bump '["4"]'
status: yielded
type: Activity<sum {write: {field: Nat, before: Nat, after: Nat}}, sum {written: {}, refused: {}}, Nat>
turn 1: yield write({field: 0, before: 4, after: 5})  (waiting)
diagnostic: waiting for a response

$ obend run tests/obend-source/examples/Counter.obend bump '["4"]' '["written"]'
status: finished
type: Activity<sum {write: {field: Nat, before: Nat, after: Nat}}, sum {written: {}, refused: {}}, Nat>
turn 1: yield write({field: 0, before: 4, after: 5})  <- written({})
result: 5
```

Both executed. At the reference level `Step` has no rule for `perform`: a term
whose next redex is a `perform` has *yielded*, and `Obend.Core.Term.Yields` locates that redex in an
evaluation context. A yielded term takes no step and its context is unique
(`Obend.Core.Term.yields_no_step`, `Obend.Core.Term.yields_deterministic`), and
`Obend.Core.Term.Interaction` relates a program to a list of (plan, response) turns, one list entry
per admitted turn (`Obend.Core.Term.one_turn_interaction` exhibits the counter above).

On the machine, a `perform` under an `update` frame, which means a shared cell is being forced, is
refused `sharedEffect` (`Obend.Core.Machine.perform_under_update_refused`); otherwise the Plan
becomes a heap cell and the state is `yielded` (`Obend.Core.Machine.perform_yields`). `resume` is
defined only on a yielded state and changes nothing but the control
(`Obend.Core.Machine.resume_requires_yield`, `Obend.Core.Machine.resume_keeps_heap_and_stack`). The
reason an effect cannot run under a shared cell is that its effect would be cached and shared:
once for all, or once per demand, neither of which is a semantics anyone intended. The type system
makes the refusal unreachable for checked programs: an activity type is never shareable, so the
checker refuses an activity as an argument, a record or extended field, a specification or
prototype component, or a sum payload (`Obend.Core.Proofs.CheckTeeth.effect_as_argument_refused`,
`Obend.Core.Proofs.CheckTeeth.effect_in_record_field_refused`, and siblings), and the front end
refuses the same by name (`effect-as-argument`, `effect-in-field`, a parameterless activity as
`nullary-activity`, since it would be a shared value with its effect cached). A Plan must be a sum of
first-order data and a response first-order data (`Obend.Core.Ty.Ty.isPlan`).

Typed yields are safe points. `Obend.Core.Proofs.Preservation.typed_yield_quiescent`: a typed
yielded state forces no shared cell and has none half-evaluated.
`Obend.Core.Proofs.Preservation.typed_resume_preserved`: resuming it with a closed response typed at
the program's declared response type gives a typed state. The reference meaning of an activity is
the interaction tree of the program's *own* machine (`Obend.Core.Interaction`: a visible `vis`
node, a `ret`, faults, `malformed`, and `spin`, silent divergence as a node of its own, so that
ignoring internal steps never equates spinning forever with eventually yielding). Checkpoint
normalization is proved transparent against it up to resources only, and §8 lists those theorems.

Inside a turn, recursion is lazy `fix` and may diverge or exhaust its ticks. Across turns a
resident's self-call sits under a `perform`, so each unfolding costs one resume. No check yet
guarantees that a well-typed resident's pure segment terminates.

## 8. What is proved

Scope: closed Core4 terms and the front end's *output*; nothing here mentions the meaning of `.obend`.
I read each statement below at its source, by script (every `Obend.*` name in this paper resolves to a
declaration under `lean/Obend` on `origin/dev` at `e5fca29`), and did not rebuild the library; the
tree's own reports (`lean/docs/REPORT-20261031.md`, `REPORT-CHECKER-20261030.md`) record it green at
their commits.

On axioms. For Draft 1, at commit `c04c948`, I printed `#print axioms` for the 74 cited constants the
built library exports: none rests on more than `propext`, `Classical.choice` and `Quot.sound`, except
the four `native_decide` facts `pommette_vectors`, `ordered_presentation_invariance_4000`,
`twice_accepted` and `claim_spec_accepted`, which are *compiled*. The other 19 cited constants were
module-private there, so an importer could not print them. Since then the build has carried one
census, `Obend/Census.lean`: a non-module file importing every module of the library with its private
part, ending in `#assert_axioms_tree`, which fails the build on any constant, public or private,
resting on `sorryAx` or a declared axiom, and counts the 27 compiled theorems separately. So for every
cited constant, the 19 private ones and `Obend.Core.Collect.agree_runBounded` included, the evidence is
that census, which holds when the library builds; the per-module pins it replaced were removed.

| Theorem | Statement in words | Premises | Module |
| --- | --- | --- | --- |
| `Obend.Core.Proofs.Adequacy.sourceStep_deterministic`, `.source_evaluates_unique` | the reference step and evaluation are deterministic | none | `Core/Proofs/Adequacy` |
| `Obend.Core.Check.ignores_any_partial_argument` | `(λ. 7) a` evaluates to 7 for every term `a`, a divergent `fix` included | none | `Core/Check` |
| `Obend.Core.Proofs.Adequacy.runBounded_value_sound`, `.runBounded_observation_sound` | a finished bounded run's result is a reference evaluation of the term (any weak-head value, through the heap's meaning; ground observations) | closed term; run finished | `Core/Proofs/Adequacy` |
| `Obend.Core.Proofs.Adequacy.runBounded_resource_independent` | two finished runs under different limits observe the same | closed; both finished | `Core/Proofs/Adequacy` |
| `Obend.Core.Proofs.Completeness.rawRun_finite_completion`, `.machine_evaluation_complete`, `.coreRepresentation` | a closed term the reference evaluates to an observable value is finished by the machine in finitely many steps; the machine inhabits `Representation` | closed; `Evaluates`; `Observes` | `Core/Proofs/Completeness` |
| `Obend.Core.Proofs.Adequacy.unused_argument_executor`, `.shared_argument_executor` | an unused argument stays suspended; a second demand sees the first's cache at the same address | none (fixtures general in the argument and the number) | `Core/Proofs/Adequacy` |
| `Obend.Core.MachineFast.runBounded_eq_fast` | the compiled fast machine equals `runBounded` (`@[csimp]`) | none | `Core/MachineFast` |
| `Obend.Core.Proofs.Preservation.typed_stepRaw_preserved` | every raw machine step preserves typing of heap, control and stack | a typed state | `Core/Proofs/Preservation` |
| `Obend.Core.Proofs.Preservation.checked_reachable_no_refusal`, `.check_runBounded_no_refusal` | a checked closed term never reaches any refusal (wrong operand, missing field, unbound reference, `sharedEffect`) at any limits; divergence, blackholes and suspension remain possible | `Checked source []` | `Core/Proofs/Preservation` |
| `Obend.Core.Proofs.Preservation.typed_yield_quiescent`, `.typed_resume_preserved` | a typed yield forces no shared cell; resuming it with a typed response gives a typed state | a typed state; a typed response | `Core/Proofs/Preservation` |
| `Obend.Core.Proofs.Substitution.check_mono`, `.check_msubst` | more fuel never loses a result; closed fillings that check at their hypotheses' types keep a checked term checked, at fuel `n + m`, at the same type, with no more uses | the fillings check, closed, under the template's assumptions | `Core/Proofs/Substitution` |
| `Obend.Core.Proofs.Templates.canonical_instantiate`, `.Discharges.infer_instantiate`, `.Discharges.check_instantiate` | a template accepted under rigid bounds is accepted at every substitution that discharges them | `Discharges` | `Core/Proofs/Templates` |
| `Obend.Core.Check.sameType_equivalence`, `Obend.Core.Check.Assumptions.chase_bounded` | type agreement (canonical rows plus hereditary alias unfolding) is an equivalence; the bounded orbit test is exact | none | `Core/LegacyAgreement` |
| `Obend.Core.Bidirectional.checkAgainst_sound` | whatever the bidirectional checker accepts has a derivation at exactly the expected type | `checkAgainst … = .ok` | `Core/Bidirectional` |
| `Obend.Core.Proofs.BidirectionalCompleteness.complete`, `.checkAgainst_complete`, `.checked_covered_accepted` | a derivation of a term in the syntactic fragment makes `checkAgainst` succeed against every agreeing type, with the derivation's usage vector, whatever the annotations | `checkCovered`; the certificate's top-level premises | `Core/Proofs/BidirectionalCompleteness` |
| `Obend.Core.Proofs.BidirectionalCompleteness.appliedLambda_boundary`, `.coverage_premise_needed`, `.full_corollary_fails` | the fragment boundary bites; the unconditional annotatability corollary is false for this checker | none | `Core/Proofs/BidirectionalCompleteness` |
| `Obend.Core.Proofs.CheckCompletenessObstruction.checked_lambda_without_annotations_never_checks`, `.checked_does_not_imply_eventual_success`, `.annotated_empty_eliminator_still_incomplete` | the annotation-directed `check` is incomplete for `Checked`: a certified term it refuses at every fuel | none | `Core/Proofs/CheckCompletenessObstruction` |
| `Obend.Spec.Contract.run_append`, `.run_assoc`, `.checkLayer_ok`, `.discharge_ok` | the composition contract threads through a chain; composition is associative; an admitted layer met its clauses; a discharged chain fills the final self exactly | none | `Spec/Proofs/Contract` |
| `Obend.Spec.Proofs.SpecificationClosure.composeTy_closed`, `.compose_wrapper_typed` | `Specification<T>` is closed under `compose`, and the lowering is typable at every shareable `T` | `T.shareable` for the lowering | `Spec/Proofs/SpecificationClosure` |
| `Obend.Spec.Proofs.FrontEndAdequacy.accepted_typed`, `.accepted_never_refused`, `.accepted_execution_semantics` | a program the front end accepts is closed and carries the checker's derivation, is never refused by the bounded machine, and a finished run extracts the unique deep evaluation of its term | an `Accepted` value | `Spec/Proofs/FrontEndAdequacy` |
| `Obend.Core.Proofs.DataSoundness.execution_source_semantics`, `.deepEvaluates_unique`, `.execution_data_unique` | the Data of a successful execution is the deep reference evaluation, unique across policies, limits and budgets | closed; an `ExecutionWith` | `Core/Proofs/DataSoundness` |
| `Obend.Core.Proofs.CheckpointRoundTrip.state_roundTrip` | the checkpoint codec restores every machine state | none | `Core/Proofs/CheckpointRoundTrip` |
| `Obend.Core.Collect.related_collect`, `Obend.Core.Collect.agree_runBounded` | collecting a heap is a renaming of the state; settling cached origins changes no bounded run, capacity suspensions included | none | `Core/Proofs/Collect`, `Core/Proofs/Settle` |
| `Obend.Core.Proofs.Forcing.Chain.back`, `.Chain.resume`, `.Chain.spins` | whatever a normalized (forced, settled, collected) checkpoint commits, the lazy state commits alike under every resource vector above a threshold; every response resumes a chain to a chain; if the lazy run spins the normalized commits nothing | a `Chain` | `Core/Proofs/Forcing/Converse` |
| `Obend.Spec.Proofs.C4Vectors.pommette_vectors`, `.ordered_presentation_invariance_4000` | the published C4 precedence vectors; invariance under renaming of the ordered presentation on 4000 seeded DAGs with accepted and refused nodes | none | `Spec/Proofs/C4Vectors` (compiled) |
| `Obend.Slot.slot_repair`, `Obend.Slot.Core4.calculus_check_msubst` | a stored selection is usable iff its judge and every cited support hold, a blocked read names exactly the dead supports; the slot's substitution law at Core4, at twice the judge's fuel | as stated | `Slot`, `Slot/Core4` |

Three remarks on reading the table.

*Preservation is at the machine, not at the source step.* The development states that every raw
machine transition preserves typing and that checked terms never reach a refusal. It does not state
progress or preservation for the call-by-name `Step`, and a checked term may diverge. For a lazy
language with activities the useful form of progress is that a checked term is never refused (it
finishes, diverges, exhausts a bound or yields), and `checked_reachable_no_refusal` is that.

*The checker is not complete, and one checker is.* §8.1 states which result applies to which procedure.

*Things that read like proof but are not.* `Obend.Core.Check.checked_erasure` is a projection of the
certificate. `Obend.Core.Term.Representation` is a contract; the claim is its inhabitant
`coreRepresentation`. The `native_decide` fixtures of `Obend.Spec.Proofs.SpecificationClosure` show
the front end accepts or refuses one source string, not a property of all strings.

### 8.1 What is proved about the checker's completeness

There are two checking procedures in the tree, and the results differ.

**The annotation-directed checker is provably incomplete.** `Obend.Core.Check.check` reads a lambda's
annotation and checks a derivation with a granted fuel. For its certificate type `Checked` (a
`PartialTyping` derivation with the top-level premises)
`Obend.Core.Proofs.CheckCompletenessObstruction.checked_lambda_without_annotations_never_checks` and
`.checked_does_not_imply_eventual_success` give a certified term refused at every fuel (a lambda with
no annotations), and `.annotated_empty_eliminator_still_incomplete` gives one that stays refused even
with the right annotations (an empty case, which has a semantic eliminator at any result type but no
type to infer it from). Two obstructions the first draft listed no longer stand and are removed:
a correct annotation now suffices for a lambda whose branches meet through an alias, because branch
joins convert through `agree` (`.correct_lambda_annotation_now_checks` is the former counterexample
negated), and the duplicate-arm program has no certificate at all, because the relation itself
refuses repeated case labels (`.case_labels_distinct`, `.duplicate_arms_have_no_derivation`).

**A bidirectional checker exists, with a completeness theorem on a stated fragment.**
`Obend.Core.Bidirectional` has one structural function, `elaborate`, over a mode `synth | check E`;
it takes no fuel, returns `Except CheckRefusal` carrying the derivation, and has top levels
`checkAgainst` and `infer`. Soundness is by construction (`checkAgainst_sound`). Conversion happens at
the mode switch, annotations are read only in synthesis, and a refusal names its rule
(`.missingLambdaAnnotation`, `.duplicateLabels`). Completeness is
`Obend.Core.Proofs.BidirectionalCompleteness.complete`, by induction on `PartialTyping`: for a term
that `synthCovered` or `checkCovered` accepts, the checker succeeds against every type agreeing with
the derived one, with the same usage vector, *whatever the annotations*. The fragment is syntactic:
variables, literals and eliminations synthesize; every introduction form (`lam`, `inject`, `perform`,
`done`, a `record` with distinct labels, `specification`, `prototype`) and every branching form
(`ifBool`, `ifZero`, `case`, empty arms included) sits in checking position. `extend` and holes are
outside. The three former counterexamples check against their certificates' types by `decide`
(`.unannotatedConstant_checks`, `.aliasBranch_checks`, `.emptyCase_checks`, in the obstruction
module). The boundary is a theorem too: a lambda applied directly is certified at `Nat`, outside the
fragment, and refused naming the missing annotation (`appliedLambda_boundary`), so the coverage
premise cannot be dropped (`coverage_premise_needed`), while annotating the lambda is enough
(`appliedLambda_annotated_checks`). Usage vectors are determined by the term
(`uses_determined`), hence a certificate is determined by its type (`Checked.eq_of_type`).

**The full annotatability statement is false for this checker.** "Every certified term has some
annotations under which `checkAgainst` accepts it" is refuted by `full_corollary_fails`, through the
witness `shadowedLambdaRecord_refused`: a record with a repeated label forces the checker to
synthesize its fields; a lambda synthesizes an arrow whatever its annotation; and agreement does not
descend into rows, so a field converted to an alias of its arrow type never meets the expected row.
In the terms of Dunfield and Krishnaswami's criteria (§11) the system is complete on its fragment and
fails annotatability outside it; the cause the proof isolates is that agreement does not descend into
rows, not a missing mode.

**Where the bidirectional checker is used.** The Slot layer's Core4 judge is `fragmentJudge` (the
bidirectional checker restricted to the fragment, depth bounded by the grant) or `annotatedJudge`
(`Check.check` with the grant as fuel); `Obend.Slot.Core4.routes_agree` says the two certify the same
thing, and `extend_filling_admitted` shows an `extend` filling that only the second admits. The
front end does not use it: a program is admitted by `Check.check`.

**Equi-recursive type agreement is in progress, and the committed part is a foundation.** What is on
`origin/dev` (`lean/docs/REPORT-EQUIREC-20261031.md` is its own account): a finite-graph
bisimulation kernel whose visited-pair worklist accepts exactly when some bisimulation relates the
pair (`Obend.Core.FiniteBisimulation.visitedSame_iff`; Amadio and Cardelli's trail of assumed pairs
is the precedent), a type-graph decision proved equivalent to the graph meaning
(`Obend.Core.TypeGraph.candidate_iff`), and the assembled relation
`Obend.Core.EquiRecursiveAgreement.agrees` with `agrees_iff`, `agrees_equivalence`, congruence for
arrows, fields, specifications, prototypes, variants and computations (`agrees_arrow` and its
siblings), alias unfolding (`agrees_alias`), and the theorem that every old agreement is kept
(`legacy_sameType_extends`). **It is not the checker's agreement yet.** `Check.sameType` still
resolves to the legacy relation; `PartialTyping`, preservation, the bidirectional checker and the slot
judge have not been switched; and `full_corollary_fails` therefore remains true and present. Two
theorems record why the switch is not free: arrow congruence would equate `Nat → Nat` with its
alias-domain spelling (`Obend.Core.Proofs.EquiRecursiveBoundary.congruence_equates_arrows`), while the
current checker refuses `λx. x` at the latter under every annotation
(`identity_alias_check_refused`), because the alias is not shareable and the unrestricted binder is
invalid (`alias_shareability_differs`). Work in the tree beyond what is committed is not described
here.

## 9. Ancestry, method combination, and a correction to the book

`spec S extends A, B for T` is linearized by C4, which is C3 plus the *suffix property*
(ltuo §7.4; `Obend.Spec.C4`), in the elaborator. The extension is the `mix` chain of the ancestors'
hidden layers, with no new constructors. The precedence list is available to a program through the
interface label of the specification's metadata. Specifications are identified by the qualified
declaration key, so a diamond's shared ancestor counts once, while an explicit `compose(E, E)`
applies `E` twice. That is the calculus-level content of Faré's linearity as conservation (§2): one
generative identity, counted once.

(`lean/tests/obend-source/RepeatedExtension.obend` has `fix(compose(AddOne, AddOne), seed)` and
yields 7 at seed 5: `AddOne` applied twice.) A diamond counts its shared ancestor once. Here `Object`
is the common ancestor of `Timestamped` and `Audited`:

```obend lean/tests/obend-source/Ancestry.obend
edition ObjectiveBend 1
# Declared ancestry: C4 linearization, a diamond counted once, standard
# method combination (around outside every primary) and a `+` combination.
record Doc:
  save(n: Nat) -> Nat
  weight() -> Nat

spec Object for Doc:
  def save(n: Nat) -> Nat:
    n
  combine + weight() -> Nat:
    1n

spec Timestamped extends Object for Doc:
  def save(n: Nat) -> Nat:
    super.save(n) * 10n + 1n
  combine + weight() -> Nat:
    10n

spec Audited extends Object for Doc:
  def save(n: Nat) -> Nat:
    super.save(n) * 10n + 2n
  combine + weight() -> Nat:
    100n

spec Document extends Timestamped, Audited for Doc:
  def save(n: Nat) -> Nat:
    super.save(n) * 10n + 3n
  combine + weight() -> Nat:
    1000n

spec Logged extends Document for Doc:
  around save(n: Nat) -> Nat:
    super.save(n) + 100000n

spec Inner extends Logged for Doc:
  def save(n: Nat) -> Nat:
    super.save(n) * 10n + 4n

def blank() -> Doc:
  {save: fn(n: Nat) -> Nat: 0n, weight: 0n}

# Document -> Timestamped -> Audited -> Object: 0, 2, 21, 213.
def saved() -> Nat:
  fix(Document, blank()).save(0n)

# Object's weight is counted once through the diamond: 1000 + 10 + 100 + 1.
def weighed() -> Nat:
  fix(Document, blank()).weight

# The around method wraps every primary, including Inner's, which is more
# specific than Logged: 2134 + 100000 (a plain mixin chain would give 1002134).
def logged() -> Nat:
  fix(Inner, blank()).save(0n)

# Reflection reads the static precedence list from the spec's interface label.
def interface() -> String:
  match metadata(Inner):
    case declared(d): d.interface
    case composed(c): ""
    case extension(e): ""
```

```sh
$ obend run tests/obend-source/Ancestry.obend saved
result: 213
$ obend run tests/obend-source/Ancestry.obend weighed
result: 1111
$ obend run tests/obend-source/Ancestry.obend logged
result: 102134
```

All executed. `saved` follows the precedence list `Document, Timestamped, Audited, Object` from the bottom: 0, 2,
21, 213. `weighed` is `1000 + 10 + 100 + 1`: `Object`'s weight 1 is counted once through the
diamond, which is conservation of contributions. `logged` is `2134 + 100000`: the `around` method
wraps every primary including `Inner`'s, which is more specific than `Logged`; a plain mixin chain
would give 1002134. Qualifiers are `def` (primary), `suffix spec`, `around`, and the pure
combinations `combine +`, `combine *`, `combine and`. `before` and `after` are parsed and refused by
the elaborator.

**The correction.** The book states shape determinism of C4 for a bare DAG: equivalent partial
orders should select the same linearization. pommette, Faré's own implementation, does not support
that wording. It maps `((C A) (C B))` to `C A B O` and the reversed presentation to `C B A O`, though both
have the same partial order; and deterministic equivariance under the swap automorphism of a
symmetric bare poset *cannot* choose one strict total order. The defensible invariance is under
renaming of the **ordered presentation**, including the local parent sequences and suffix marks.
That is the statement `Obend.Spec.C4.OrderedPresentationInvariant`, a `Prop`, which commutes
linearization with every bijective renaming of specification identities. It is not proved. Its
evidence is `Obend.Spec.Proofs.C4Vectors.ordered_presentation_invariance_4000`, compiled, on 4000
seeded random DAGs with suffix marks, and the family is checked non-vacuous (both accepted and
refused nodes occur). A "canonical order from a bare DAG" must not be advertised.

## 10. What is open

Stated plainly, from the tree's own lists.

- **Surface semantics.** `.obend` has no meaning of its own. The front end, including compose order,
  C4 ancestry and method combination, is trusted. `OrderedPresentationInvariant` is a `Prop` nothing
  proves.
- **Behavioural equivalence.** The tree does not define `≈b` and states no associativity of
  `Term.mix` up to it. The plan in `METATHEORY.md` §2 is a step-indexed logical relation over the lazy heap in
  the style of improvement theory (Moran and Sands), which also gives the cost-sensitive equivalence
  a resource-priced world wants, to be done in Iris-Lean. No file in the tree does it yet, and the
  same goes for the claim that call-by-need costs no more than call-by-name.
- **Reflection.** A provenance-establishing prototype constructor; the choice between tying
  reflective self-reference inside the knot or outside it; resource observations as theorems.
- **Cross-package extension.** No surface form names another package's root, and a package cannot be
  extended from another. Instances across package roots are not addressed. Everything downstream of a
  stranger extending my specification, with my law inheriting yours, waits on this.
- **Laws.** `Obend/Law` has landed in five steps, with 167 theorems pinned to the standard three
  axioms by its own report (`lean/docs/REPORT-LAW-20261030.md`; I did not recount them). Among them,
  over Core4's substitution-based `Evaluates` and not over the machine: `Obend.Law.guardedBy_sound`,
  `Obend.Law.chain_keeps` (a claim of the `keeps` shape is preserved along a chain),
  `Obend.Law.effective_law_eval` and `Obend.Law.inherited_never_widens` (for closed laws, the
  effective law admits exactly when every law on the list admits), and
  `Obend.Law.effective_refuses_first` (a refusal names the first refusing ancestor). The report
  lists what is not done: no theorem that the generated laws type-check at their stated type, none
  connecting the machine to `Admits`, and no compilation of the `.obend` law fragment to Law terms.
  Spec `claim`s, in the front end, are elaborated into a hidden Boolean-typed knot field and recorded
  with status `unchecked`; they are typed and retained and never evaluated or proved, and are not
  re-checked at each template instance's types.
- **Guardedness.** No check that a well-typed resident's segment terminates.
- **Completeness of the machine** is finite, not bounded: no resource bound is proved. Quantities are
  static; use counts are not tracked at run time.
- **Completeness of the checker.** Neither procedure is complete for `PartialTyping`. `check` is
  provably incomplete, `checkAgainst` is complete on a syntactic fragment, the unconditional
  annotatability statement is refuted for it, and the front end uses `check` (§8.1). Closing the gap
  is the equi-recursive agreement lane, of which only a foundation is committed, and the
  `full_corollary_fails` witness remains true until `sameType` is switched.
- **Equi-recursive agreement.** `Check.sameType` does not descend into constructors; the relation that
  does (`EquiRecursiveAgreement.agrees`) is proved an equivalence and to extend the old one but is not
  wired into `PartialTyping`, preservation, the checker or the slot judge.
- **Language.** A digest primitive callable from source (`Obend.Core.Digest` exists; Core4 has no
  digest term); `before` and `after` methods, which the elaborator refuses.
- **The leaf.** Refinement of a Core4 run against Bend's own `Eval` of the emitted book is a stated
  future theorem (`METATHEORY.md` §2) that needs another tree's semantics and a toolchain decision;
  `Obend/Leaf` is not started. The library has one executor, the Lean machine, behind the
  `Obend.Core.Backend` typeclass; refinement to any other, and any private or oblivious backend, is
  unproved.

## 11. Related work

**Bend and BendTT.** Bend's live fragment is affine: a closure "can be called at most once, even
when everything it captures is Data", and the one freely reusable thing is a top-level definition.
That is what lets a `match` free its node and makes fork-join parallelism free; Taelin has said the
affine core is a placeholder pending an answer to higher-order contraction (`THESIS.md` §1, from
his posts). Core4 keeps the quantities, checks at-most-once for `affine` and exactly-once for `linear` variables,
and gives `self` a source semantics that is reusable on purpose, at the price that a reusable
closure captures only unrestricted, shareable bindings. Whether lazy `fix` and parallel leaves
compose in practice is a claim about cost that this paper does not prove.

**Contextual modal type theory, for the slot layer.** One layer up, `Obend.Slot` is a hole resolved
when a run reaches it, from candidates under live supports. Its typing is in the spirit of contextual
modal type theory (Nanevski, Pfenning and Pientka): a hole is a contextual variable with a declared
context, and a filling is a closed term substituted for it. The development proves one repair
theorem (`Obend.Slot.slot_repair`) and instantiates the calculus at Core4 through the substitution
lemma of §8. It is outside the subject of this paper.

**Open recursion and mixins.** Cook and Palsberg (1989; *Information and Computation*, 1994) model
inheritance as deriving modified versions of recursive definitions and prove that denotational model
equivalent to the operational method-lookup of Smalltalk. Bracha and Cook (1990) read Smalltalk, Beta
and CLOS inheritance as uses of one construct, the composition of mixins (abstract subclasses). Flatt,
Krishnamurthi and Felleisen (1998) treat mixins as class-to-class functions and give them a reduction
semantics for a Java subset, with type soundness theorems for it. Core4's `mix` generalizes
composition to different inherited, middle and provided types, and its `fix` is the fixed point.
Objective Bend adds, over these, a lazy reference semantics with effects as yields, a checker that
types an extension against the members it reads from a future self (§6), a reflection contract with
a stated observer table (§4), and statements checked in Lean for Core4 itself rather than for a
Java subset. It does not add a result about mixins in a class-based language.

**Linearization.** Barrett et al. (1996) give a monotonic linearization for Dylan, easily described,
strictly observing local precedence order and agreeing with CLOS whenever CLOS's order is monotonic.
C4 (§9) is that rule with the suffix property added. Objective Bend adds a method-combination
discipline over the linearization, a diamond counted once, and an invariance under renaming of the
ordered presentation checked on 4000 seeded DAGs. Neither monotonicity nor local precedence is stated
as a theorem here, and the invariance is checked, not proved.

**Call-by-need.** Launchbury (1993) defines a natural semantics for lazy evaluation with an explicit
heap, in order to be precise about sharing; Sestoft (1997) derives a lazy abstract machine from it,
updating the heap with each computed value; Ariola and Felleisen (1997) give an equational theory of
call-by-need with no heap and prove it correct with respect to the call-by-name lambda calculus;
Breitner (2014) machine-checked Launchbury's correctness proof, found it to fail, and gave two
repairs; Hackett and Hutton (2019) replace the heap by nondeterminism ("clairvoyant" evaluation) and
obtain simpler operational reasoning and a denotational cost semantics. The machine of §3.4 is a
call-by-need machine of this family, but Objective Bend does not derive it from a heap semantics:
the reference is call-by-name, and adequacy and finite completeness are proved against it in Lean
for a machine that checkpoints, suspends at yields and is typed (§8). What it does not have is a
cost theory: `METATHEORY.md` plans one from improvement theory (Moran and Sands, 1999), and the
text of that paper in my collection is not machine-readable, so I say nothing about its content here.

**Bidirectional typing and annotatability.** Pierce and Turner (2000) recover missing annotations
locally, from adjacent nodes of the syntax tree. Dunfield and Krishnaswami (2021) survey the field:
a bidirectional system should be mode-correct and *complete* with respect to a type-assignment
system, a theorem sometimes called annotatability because the bidirectional derivation may need
annotations added to the term, and the annotations required should be few. Lennon-Bertrand (2021)
gives a bidirectional system for the Calculus of Inductive Constructions with a completeness theorem
against the undirected system, proved in Coq, which needs a judgement between inference and checking
to handle computation in types. Abel, Öhman and Vezzosi (2018) formalize a conversion-checking
algorithm in Agda and prove it complete by a Kripke logical relation. Objective Bend adds a
completeness theorem in Lean for a fragment named syntactically, valid whatever the annotations,
alongside two machine-checked negative results: the annotation-directed `check` is incomplete, and the
annotatability statement itself is false for this calculus, because agreement does not descend into
rows (§8.1). It does not yet have what Lennon-Bertrand and Abel et al. have, a completeness result for
the whole system, and equi-recursive agreement is the step that would decide whether one is reachable.

**Quantitative types.** McBride (2016) tracks usage with annotations from an arbitrary rig, using the
rig's zero to mark information present only to be contemplated; Atkey (2018) gives that system a
realizability semantics; Wood and Atkey (2022) prove the metatheory of renaming and substitution for
usage-annotated terms by linear algebra over semirings, formalized in Agda; Orchard, Liepelt and
Eades (2019) put graded modal types in a working language, Granule; and Bernardy et al. (2018) attach
linearity to function arrows in GHC to keep backwards compatibility. Core4 attaches a quantity and a
reuse flag to arrows (§3.5) and synthesizes usage bottom-up, the shape Wood and Atkey exploit, and
the tree proves a certificate's usage vector is determined by the term (`uses_determined`). It adds
no dependent types and no usage-polymorphism over a semiring: its quantities are the fixed four
(erased, affine, linear, unrestricted), with at-most-once enforced for affine and exactly-once for linear (since 2026-11-01), and
the rule that a reusable closure captures only shareable bindings is its own.

**Recursive type equality.** Amadio and Cardelli (1993) relate equality and subtyping of recursive
types as induced by a model, an ordering on infinite trees, an algorithm and a set of rules, and show
soundness and completeness between the rules, the algorithm and the tree semantics; their algorithm
keeps a trail of assumed pairs. Gaster and Jones (1996) type extensible records and variants with
rows, using *lacks* predicates to keep labels from repeating. Core4's rows go the other way: a label
may repeat, the first wins, and a shadowed member is kept only if forgetting it could lose a resource
(§3.5). What the tree has today is hereditary alias unfolding that does not descend into
constructors; a visited-pair relation in the Amadio–Cardelli style is proved to be an equivalence
and to extend it, and is not yet the checker's (§8.1). Rigid template variables are nominal, and lookup through them
goes through their bound, which is the use of bounds that §6 describes and not an equality.

**Jsonnet and Nix.** Both are lazy and both compose a `self` with a `super`, which is the evidence
that the idea is usable. They split on conflation. A Jsonnet object is its own specification: `+`
re-binds `self` over an object that has already been built, so the specification cannot be
reflected as distinct from its result, and extending an object means re-instantiating it. A Nix
overlay (`final: prev:`, with `lib.fix`) keeps the specification a function, but a function carries
no metadata a program can read, so there is no provenance to observe, no ancestor identity to
count, and neither language types an extension against a future self. I make no comparison of
performance or ergonomics.

**Faré's own work** (poof, EOOMI, ltuo) remains the source of the design. It supplies powerful
constructions, examples and research conjectures; it does not supply a complete checked type
theory, which is what Core4's checker is for, nor a mechanized metatheory.

## Reproducing

Draft 1 was read against `/Users/ember/dev/obend` at commit `c04c948` plus uncommitted work of other
lanes. Draft 2 describes only what is committed on `origin/dev` at `e5fca29`: names were resolved
against `git archive origin/dev lean/Obend`, so the uncommitted files in the working tree (further
equi-recursive modules, edits to `Bidirectional.lean` and `Check.lean`) are not read. From `lean/`:
`LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log`, then `lake build obend` and
`python3 tests/run-obend-source.py` for the conformance cohorts. Every `.obend` block above is a
file under `lean/tests/obend-source/` byte for byte, spliced mechanically; every `lean` excerpt names
its file and line range. This paper was written without building: the example outputs were produced
by the already-built `lean/.lake/build/bin/obend` for Draft 1 and were not regenerated, and the build
of the library was not checked by this revision. Prior art in §11 is limited to papers whose text in
`~/paperbin` I opened; the sources `review/PRIOR-ART-20261030.md` names but could not fetch
(Brandt and Henglein 1998, Leijen 2005, Ducournau et al. 1994, Cardelli 1986, Birgisson et al. 2014)
are not cited.
