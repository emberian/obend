# `quote` for Core4: orientation in the staging and reflection literature

2026-11-01, answering `review/QUOTE-BRIEF-20261101.md`. Claims are tagged READ (from a paper or a
file in this tree, cited), INFERRED (a consequence I draw and can defend), PROPOSED (a design
choice). Papers are in `~/paperbin/` (PB) or `~/paperbin/obend-vision-20261031/` (V); §6 lists what
was fetched for this study, what was already there, and what could not be had in the form asked.

## 0. The orientation in one paragraph

INFERRED. Two decades of this literature converge on one discipline, stated first by Davies–Pfenning
and made exact by Kavvos: code and values are two regions, the modal operator is the wall between
them, nothing passes from value to code except by `lift` at data types, nothing passes from code to
value except by `run` of *closed* code, and no equivalence of values is a congruence through the
wall. Everything else (hygiene, scope extrusion, cross-stage persistence, erasure, pattern matching on
code, verified round trips, mirrors, boundaries) is a theorem about one of the two crossings or
about keeping the wall intact under some feature (effects, references, laziness, polymorphism,
separate compilation). Core4 already has the wall in three places without naming it: `Data` extraction
refuses closures (`Core/Data.lean`, `Failure.executableValue`), `resume` evaluates its response in the
empty environment (`Core/Machine.lean`, `resume_keeps_heap_and_stack`), and a slot filling must be
`Scoped 0` (`Slot/Core4.lean`, `calculus_typed_msubst`; `open_filling_tooth`). The design in §3
builds `quote` by naming those three walls as the two crossings of one modality, and the property we
are most likely to get wrong (§5, §7) is the first one: letting `quote` see a value of the lazy heap.

## 1. The properties the literature isolated

Each paragraph: the property, the paper that isolated it, the construction that secures it.

### 1.1 Well-typedness of quoted code (typed quotation)

READ. Davies–Pfenning, *A modal analysis of staged computation* (PB `davies2001-…`): code of type `A`
has type `□A`; `box E` is typable only when `E` uses modal variables alone (`∆; · ⊢ E : A`), so a
value of `□A` is closed code of type `A`; subject reduction (their Thm 3) is the typedness of
generated code, and eliminability (Thm 5: an irreducible closed term of type `□A` is `box E′`) is
"when a stage is complete no eliminable term remains". READ. Taha–Sheard, *MetaML* (PB
`taha-sheard2000-…`): "MetaML performs type-checking for all stages once and for all before the
execution of the first stage", Thm 1 (type preservation for the big-step semantics). READ.
Nanevski–Pfenning–Pientka, CMTT (PB `nanevski2008-…`): `[Ψ]A` is code open in exactly `Ψ`; a
meta-variable `u :: A[Ψ]` occurs as a closure `u[σ]` with `σ` a substitution for `Ψ`; Thm 4.3
(contextual substitution): if `∆; Ψ ⊢ M : A` and `(∆, u::A[Ψ], ∆′); Γ ⊢ N : C` then
`(∆, ∆′); Γ ⊢ [[Ψ.M/u]]N : C`. READ. Devriese–Piessens, *Typed syntactic meta-programming* (PB
`devriese-piessens2013-…`) separate two strengths: "generated code is type-checked upon completion
of the meta-program" versus "a meta-program's type can guarantee type-correctness of all programs
it will ever generate"; they take the second (Agda, term/type/context representations indexed by
derivations). READ. Altenkirch–Kaposi (PB `altenkirch-kaposi2016-…`) and Chapman (PB
`chapman2008-…`) make the representation itself intrinsically typed (`Tm : Con → Ty → Set`), so an
ill-typed term is not a term; Kaposi–Kovács–Kraus (PB `kaposi-kovacs-kraus2019-…`) prove that the
shallow (host-level) embedding is injective up to definitional equality, which is the licence to
reuse the host's conversion as the object's. The construction, in every case: a representation
indexed by context and type (intrinsic) or a representation plus a checker whose acceptance is the
index (extrinsic, MetaCoq's `tmUnquoteTyped A tm` "checks that it is indeed of type A", PB
`sozeau2020-the-metacoq-project` §3.1).

### 1.2 Hygiene under nested generators

READ. Dybvig–Hieb–Bruggeman (PB `dybvig-hieb-bruggeman1992-…`): the capture problem has two sides
(introduced references captured by existing bindings, introduced bindings capturing existing
references) and a third problem, source–object correlation; their construction is a syntax object
carrying marks and substitutions. READ. Adams, *Towards the essence of hygiene* (PB
`adams2015-…`): the first algorithm-independent definition. Criterion 1 (reference hygiene): "a
macro expansion step is hygienic with regard to references iff for any partially expanded
expressions e1, e2, e1′ where e1 ≃ e2 and e1 ⟶ e1′, there exists e2′ with e1′ ≃ e2′ and e2 ⟶ e2′"
(expansion respects α-equivalence); binder hygiene is equivariance of the transformer with respect to
binder atoms (nominal logic: `supp f = ∅`, so "a transformer that introduces a binder atom must use
`fresh`"). READ. Ullrich–de Moura (PB `ullrich-demoura-2020-…`, §3): macro scopes are appended per
expansion, "different expansions of the same macro introduce different annotations", and the full
ordered history is needed "to treat macro-producing macros correctly" — that is the nested-generator
case. READ. Bawden (PB `bawden1999-…`, §3.2–3.3): nested quasiquotation is level-counted; Stucki et
al. 2018 (PB `stucki-2018-…`, §3.1) state the same as the Phase Consistency Principle: "for any free
variable reference x, the number of quoted scopes and the number of spliced scopes between the
reference to x and the definition of x must be equal". The construction that makes hygiene a
non-problem rather than an algorithm: a nameless representation. Tan–Wei (V `tan-wei2026-…` §8) use
locally nameless with de Bruijn indices for bound variables because it "avoids α-equivalence" and
levels for free ones; Kovács 2022 (PB `kovacs-2022-…` §4) works in a presheaf model where every
construction is stable under object substitution, so there is nothing to capture.

### 1.3 No scope extrusion

READ. Taha–Sheard (§7.2): cross-stage safety, "when a variable is used at a level less than the level
of the lambda-abstraction in which it is bound, we say the use violates cross-stage safety". READ.
Moggi–Taha–Benaissa–Sheard, *An idealized MetaML* (PB `moggi1999-…`): the first sound integration of
open code `⟨t⟩` (Davies' `○`) with closed code `[t]` (Davies–Pfenning's `□`); "the Box rule ensures
that there are no 'late' free variables in the term being Boxed", `run e with xᵢ = eᵢ` may add
closed bindings. READ. Taha–Nielsen, *Environment classifiers* (PB `taha-nielsen2003-…`): `⟨t⟩^α`
names the environment the code originated in, `run e : (α)t` requires classifier-polymorphic code,
so running needs no closedness type; Calcagno–Moggi–Taha (PB `calcagno-moggi-taha2004-…`) then
observe "inference for the full classifier-based system fails" and keep an implicit-classifier
subset. READ. Nanevski–Pfenning, *Staged computation with names and necessity* (PB
`nanevski-pfenning2005-…`): `□_C A` is code whose free names are in `C`, its *support*; "partially
specified expressions cannot be evaluated before every name in the expression's support is provided
a definition" (§2). READ. Kameyama–Kiselyov–Shan 2011 (PB `kameyama-kiselyov-shan2011-…`):
"blindly adding effects renders multilevel types unsound"; their calculus "restricts the code
generator's effects to the scope of generated binders" and proves extrusion impossible (§4.2). READ.
Kameyama–Kiselyov–Shan 2015 (PB `kameyama-kiselyov-shan2015-…`, §5): "Scope extrusion may occur even
in a pure-functional generator, if the meta-programming system has a first-class operation to run or
print the generated code"; "environment classifiers are too coarse-grained to prevent scope
extrusion while still allow effectful manipulation of open code"; "It is inevitable that preventing
scope extrusion in the presence of effects while still permitting manipulations of open code requires
as precise as possible annotations of code types with free target variables." READ. Kiselyov 2026 (V
`kiselyov2026-…` §4.1): MetaOCaml detects extrusion dynamically "just when … was about to be spliced,
outside of the binder — at the earliest moment", and "scope extrusion may manifest in no compilation
errors: just wrong results". READ. Rhiger (PB `rhiger2005-…`): `[Γ]τ` carries the type environment
in the code type, `run : [ ]τ → τ`, and the dynamic fragment is deliberately not hygienic (captured
variables are visible in the type). The secure construction is the CMTT one: the free variables of
a code value are listed in its type, substitution for a meta-variable carries the local substitution
with it, and `run` is typed at the empty context only.

### 1.4 Cross-stage persistence, and what may cross

READ. Taha–Sheard §7.1: CSP is "a variable bound in a particular stage will be available in all
future stages"; §7.1 "Cross-Platform Portability": "being able to inject any value into the code
type means that some parts of this code fragment may not be printable … MetaML currently lacks
cross-platform portability. The loss of this property is the price paid for cross-stage persistence";
§6.1: "Function values cannot be lifted into code using Lift, as we cannot derive a high-level
intensional representation for them in general." READ. Davies–Pfenning Thm 6 (persistence):
"we can never construct code from terms which were not originally code" — and the dual (eliminable
images of persistent terms) deliberately fails, because `let box u = box E in u ⟶ E` is evaluation of
code. READ. Kiselyov 2026 §5 settles the question after twenty years: a global CSP is "a named
reference into the libraries available at the present stage and assumed available at a future stage",
a local CSP must be lifted *by value*; online lifting is "sharing of the value between the generator
and the generated code — which … only makes sense when the generated code is used while the generator
is still running"; offline lifting "means copying — or, to be more precise, serializing … not all
values are copyable/serializable: for example, open channels and mutable cells are not"; and the
resolution is `code_with_csp`, a "stage-separated closure" `C : (ε code → α code) × ε`, which is a
let-insertion whose bound expression is in the present stage and whose body is in the future one.
READ. Stucki–Brachthäuser–Odersky 2021 (PB `stucki-brachthauser-odersky2021-…` §2): "In the context of
macros and cross-platform portability, that is, macros compiled on one machine but potentially
executed on another, we cannot support cross-stage persistence of local variables." The construction:
`lift` exists at data types only; a non-data value crosses as a named reference (global) or as a
stage-separated let whose binding stays behind.

### 1.5 `run` safety

READ. Davies–Pfenning: `eval = λx:□A. let box y ⇐ x in y : □A → A` (axiom T) is typable because a
`□A` value is closed; Davies 1996 (PB `davies1996-…` §5): "Since λ○ does not express closed code, it
can not be directly extended with a construct … that expresses evaluation of generated code", and
(Davies–Pfenning §6) "the resulting languages are unsound when general references or value carrying
exceptions are added, since these features allow a code expression with free variables to escape the
binders for those variables". READ. Moggi et al.: `run` of MetaML needs closedness, obtained by
`Γ⁺¹ ⊢ e : ⟨t⟩ⁿ ⟹ Γ ⊢ run e : tⁿ` (every variable's level is raised, so none of the current stage
can be used). READ. Kameyama–Kiselyov–Shan 2015 §5: `lam (\x → runR x)` "does not type-check; the
error message essentially describes the attempt to run an open code". READ. Berger–Tratt (PB
`berger-tratt2015-…` §4): a program logic for run must handle that "a quasi-quote always terminates,
but the code it contains may not", and `let ⟨x⟩ = ⟨Ω⟩ in λy.x` converges. The construction: `run`
is typed only at closed code (`□A`, `[ ]τ`, empty support, or classifier-polymorphic), and the
evaluation of code happens in an empty environment.

### 1.6 What quotation does to extensional equivalence

READ. Barendregt, *Self-interpretation in lambda calculus* (PB `barendregt1991-…`, Remark 3(ii)): a
self-quote `Q` with `Q M = ⌜M⌝` cannot exist, since `⌜I⌝ = Q I = Q (I I) = ⌜I I⌝` equates two distinct
normal forms; a self-interpreter `E ⌜M⌝ = M` does (Kleene). READ. Kavvos, thesis (PB
`kavvos2017-semantics-intensionality-…` §1.3): Tale 1 (Barendregt's argument) and Tale 2, Wand's
theorem for a language with `eval`/`fexpr`: "M ≅ N if and only if M ≡α N … there can be no semantic
study of functional programming languages that are so strongly reflective that they can internally
define quoting. Such a language can internally distinguish any two terms in the language, as long
as they are not equal up to renaming." His §1.4: "the only true restriction is quoting, and
everything else is admissible" (`gnum : □A → □□A`, `app`, `E : □A → A` are definable on codes);
"Intensionality adheres to a typing discipline." READ. Kavvos 2017 (PB `kavvos2017-intensionality-…`):
the modality "separate[s] it into two regions … data in the first region, the modal one, are
available as code, and their description can be examined. In contrast, data in the second region are
only available as values up to ordinary equality"; intensional operations are constants
`f̃ : □A → □B` with `f̃ (box M) → box f(M)` for closed `M`; "we do not include the following congruence
rule for the modality: ∆; · ⊢ M = N : A ⟹ ∆; Γ ⊢ box M = box N : □A"; Thm 4.2 confluence, hence the
first consistency proof for intensional programming. The Gödel–Löb part: `fix z in M ⟶ M[box (fix z
in M)/z]` with `∆; z:□A ⊢ M : A` is Löb's rule; `Y_A : □(□A → A) → □A` is an intensional fixed point
(a program with access to its own code); "the combination of eval and intensional fixed points leads
to non-termination" (`Ω_A = fix z in eval z`), which is why GL is added to S4 as a *rule with a modal
context*, not as `□A → A` plus unrestricted quoting. READ. Berger–Tratt §4: the code-extensionality
axiom `(ext_q)` says "what it means for two quasi-quotes to be equal: they must contain
observationally indistinguishable code", valid only for non-modal `x, y`, "because Ext_q(xy) cannot
distinguish between e.g. appropriately typed Ω and ⟨Ω⟩". READ. Jay–Given-Wilson (PB
`jay-given-wilson2011-…`): the factorisation combinator `F` makes SF-calculus "structure complete …
including a function that decides structural equality of arbitrary normal forms", i.e. intensional
computation is consistent exactly when it is restricted to normal forms (there `F` is undefined on
redexes). READ. Xie et al. (PB `xie-2022-…` §6): the only laws a quotation obeys are `⟦$e⟧ = e` and
`$⟦e⟧ = e` (β and η for `Code`); nothing passes through brackets. What the observer ladder is, in
these terms: ≈q is Wand's α-equality (the finest relation any observer can induce), ≈b is the
extensional region; `quote` sits at the bottom because it is the observer that induces ≈q; the modal
law that makes the ladder sound is the *absence* of the □-congruence, and the law that makes
intensional recursion consistent is Löb's rule in a modal context (the recursing term receives its
own *code*, never quotes an arbitrary *value*).

### 1.7 Semantics preservation of staging annotations (erasure, let-insertion)

READ. Tan–Wei (V `tan-wei2026-…`): CBV staging does not preserve erasure (`k ⟨42⟩ ⟨loop ()⟩`
diverges unstaged, returns code staged; `twice` duplicates an effect); "staging in CBN calculi is
better behaved, since the semantics of quotation remains aligned with the underlying CBN semantics"
(their §1, citing Inoue–Taha and Taha–Sheard); the fix is automatic let-insertion, tracked as a
control effect, with Thm 5.10/6.4: if `⊢ t₁ : rep τ | ε` and `⟨∅, t₁⟩ →* ⟨∅, code t₂⟩` then
`|t₁| ≃ctx t₂ : τ`, by a binary logical relation; mutable references break it when they live in the
first stage (§6.1: "lifting a function forces static effects in its body to occur during first-stage
evaluation, whereas after erasure those same effects remain latent"; residualizing a conditional
"requires reifying both branches, along with the first-stage effects performed while reifying them"),
and are recovered by restricting references to the second stage; §7: "the main obstacle is that
λc-terms and 2nd-stage conditionals cease to be evaluation contexts after erasure". READ. Amin–Rompf
(PB `amin-2018-…`, Fig. 2): let-insertion is the rule `P[E[Reflect(Code e)]] ⟶ P[Letc(x, e, E[Code x])]`
with `x` fresh, which "preserves the execution order of future-stage expressions"; Tan–Wei adopt it.
READ. Kovács 2022: soundness `⌜Stage t⌝ = t` and stability `Stage ⌜t⌝ = t` (Thm 5.4, 4.15) together are
conservativity of 2LTT over the object theory; the price is that "every syntactic rule and
construction in 2LTT must be stable … we cannot make decisions based on sizes of the object-theoretic
scopes"; "our version of 2LTT" has no compile-time effects (§7). Kovács 2024 (PB `kovacs2024-…`):
"staging can be used instead of laziness to implement short-circuiting", let-insertion via a `Gen`
monad in CPS "without side effects in the metalanguage". READ. Kameyama–Kiselyov–Shan 2011: let-insertion
by delimited control, sound because effects are confined to the scope of the generated binder.
READ. Davies–Pfenning Thm 5/6 are the pure version: eliminability and persistence. The construction:
an erasure function plus a binary relation between the generator's result and the erased program,
with let-insertion as the device that keeps evaluation order, and first-stage effects forbidden.

### 1.8 Pattern matching on code without breaking the above

READ. Jang–Gélineau–Monnier–Pientka, Mœbius (PB `jang2021-moebius-…`): "As Taha [2000] observed,
adding intensional analysis to MetaML would make many optimizations unsound. Environment classifiers
also seem too coarse to characterize the dependencies"; contextual types "list the variables that may
occur" so pattern matching on open code is typed, matching on polymorphic code refines type variables
and "generate[s] and track[s] typing constraints", Thm 4.7 type preservation; also (§1) administrative
redexes in generated code are "particularly undesirable in Mœbius, where the program can inspect the
code". READ. Stucki et al. 2021 §2.2: "we only match on a `${..}` if its expression is closed under
the definitions within the pattern" (closed patterns), and HOAS patterns `$f(y)` η-expand the
sub-expression so "the variables that might have been extruded will be replaced by the arguments of
the lambda". READ. Beluga (PB `pientka-dunfield2010-…`) and Cocon (PB `pientka2019-cocon`): the
intensional function space (HOAS, LF) and the extensional one (computation) are separate types,
mediated by the contextual box; Jay–Given-Wilson: factorisation acts on normal forms only. The
construction: inspection is typed at contextual code types, binders in patterns are their own
variables, and what is extracted is closed under the pattern's binders or η-expanded over them.

### 1.9 Verified quote/unquote round trips

READ. MetaCoq (PB `sozeau2020-the-metacoq-project`): `tmQuote t` returns the syntax of `t`, `tmUnquote`
"returns the dependent pair (A; t)", `tmUnquoteTyped A tm` checks; quoting itself is an OCaml plugin
and trusted; the phase-split monad (§6) makes the extractable part manipulate "the completely
first-order datatype Ast.term". READ. Coq Coq Correct (PB `sozeau2020-coq-coq-correct`): a checker of
that reified syntax verified against the specification, "assuming strong normalisation", "we are not
claiming to prove the consistency of Coq in Coq". READ. Devriese–Piessens §5: their primitives "imply
the consistency of our object theory", so by Gödel they are not definable inside it; the object calculus
"does not contain the primitive itself, making it a fundamentally weaker theory". READ.
Christiansen–Brady (PB `christiansen-brady2016-…`): elaborator reflection runs metaprograms in the
elaborator "and safety is guaranteed by the core language's type checker". READ. Forster–Kunze (PB
`forster-kunze2019-…`): a *certifying* extraction, each extracted term related to its Coq function by
a logical relation that also carries a time bound. The construction: `unquote` is a checker run
(soundness is the checker's), `quote` is a reifier whose correctness is a round trip `decode (encode t)
= t` proved on the first-order representation, and the tower never checks itself.

### 1.10 Reflection as capability (mirrors)

READ. Bracha–Ungar (PB `bracha-ungar-2004-…`): three principles, encapsulation ("meta-level facilities
must encapsulate their implementation"), stratification ("meta-level facilities must be separated
from base-level functionality"), ontological correspondence (temporal: code versus computation, "some
reflective applications … actually manipulate a computation, others … only manipulate the structure
of a program"; structural: every construct mirrored); "the ability to dynamically add/remove reflection
support" follows from stratification, and a mirror is an object handed out, not a method on every
object. The construction: reflection is reached through a value one must hold.

### 1.11 Boundaries as EP pairs with graduality

READ. New–Ahmed (PB `new-ahmed-2018-…`): "casts between two types where one is 'more dynamic' than the
other necessarily form an ep pair"; graduality is "that giving components of a program more precise
types only adds runtime type checking, and does not otherwise change behavior", proved by an
error-approximation logical relation from the ep-pair property. READ. Perconti–Ahmed (V
`perconti-ahmed2014-…`): compiler correctness "stated as contextual equivalence in the combined
language" with Matthews–Findler boundaries. READ. Patterson–Ahmed (PB `patterson-ahmed-2017-…`):
linking types "annotate where in a program they can link with components inexpressible in their
unadulterated language". The construction: a boundary is a pair `embed`/`project` with `project ∘
embed = id` in a common model, and the guarantee is monotone in precision.

## 2. Each property against Core4 as it is

Ground truth used throughout (READ): `Core/Term.lean` (`Term`, 24 constructors, de Bruijn
`bound`, `hole n σ`, `reflect`/`metadata`/`project`, `perform`/`done`; weak-head call-by-name
`Step`; `Yields`/`Interaction`; `Observation` ground only); `Core/Machine.lean` (cells
`suspended|evaluating|cached`, `update` frames, `blackhole`, `sharedEffect` refusal for a `perform`
under an update frame, `yielded`/`resume` with `next.control = .evaluate response []`,
`.hole _ _ ⟹ refused .unresolvedHole`); `Core/Check.lean` (`PartialTyping assumptions Γ t A uses`,
no rule for `hole`, `infer … (.hole _ _) = none`; `safeUses`, `reusableAllowed`,
`argumentAllowed` with `!type.isComputation`); `Core/Ty.lean` (`Quantity`, `Reuse`, `Ty.shareable`,
`Ty.isData` with no closures/specifications/prototypes/custody/variables/activities); `Slot.lean`,
`Slot/Calculus.lean` (`Calculus`, `Decides`, `slotOf`, `admit`, `resolve_checks`); `Slot/Core4.lean`
(`calculus_typed_msubst`: fillings `Scoped 0`, same `assumptions`, typed at the hypothesis' type;
`checked_msubst` with `UsesLE c'.uses c.uses`; `open_filling_tooth`); `Core/Invariant.lean`
(`Scoped`); `Core/TermTraverse.lean` (`encode_injective`); `Law/Claim.lean` (`treeEq` on encodings);
`Core/Data.lean` (`Data`, `encoded`, `executableValue`); `Core/Digest.lean` (`binds_or_collides`);
`Core/Checkpoint.lean` and `Proofs/CheckpointRoundTrip.lean` (`state_roundTrip`); `Spec/Proofs/TermWire.lean`
(`decodePacket_term`, `decode_json`); `Equiv/*` (`Ahead`, `≈b`, `mix_assoc`); `minidregg …/REFLECTION.md`
(observer table, ≈r, associativity fails under ≈r on purpose); `review/EQUIV-PLAN-20261031.md`
(definitions 1–3; adding a constructor costs one `Ahead` arm in five places);
`review/ALGEBRAIC-SUBTYPING-20261031.md` §5 (quantities not orthogonal: `affine ≡ linear` under
coercion, dropping a non-shareable member type-checks).

### 2.1 Typed quotation

Secures (READ): the certificate already exists. `Checked t Ψ` (type, uses, derivation, `safe`,
`contextValid`, `assumptionsValid`) is the intrinsic index of §1.1, and `Calculus.Typed Ψ t A :=
∃ c : Checked t Ψ, c.type = A` is `Code Ψ A` in all but name; the checked importer exists too:
`Bidirectional.checkAgainst` with `checkAgainst_sound`, and the wire round trip `decodePacket_term`.
Threatens (INFERRED): (i) a term containing `hole n σ` has no derivation at all — `infer` returns
`none` on it — so "typed open code with holes" is not a thing the checker knows; the only typed
open code today is a term with *free hypotheses* (`bound i` at the root), which is CMTT with an
empty local context for the meta-variable (`u :: A[·]`). (ii) Typing is modulo `Assumptions`
(shareability premises, bounds): `calculus_typed_msubst` demands `f.assumptions = t.assumptions`, so
the type of a quotation must carry the theory it was checked under — Astra's `theory` index is
load-bearing, not decorative. Theorem (PROPOSED, T6 in §4): `Code Ψ A θ` is the subtype
`{ t : AnnotatedTerm // t.assumptions = θ ∧ Calculus.Typed Ψ t A }`; `import : Packet → Except Refusal
(Code Ψ A θ)` with `import_sound` (an `ok` carries a `Checked`) and `import_complete` (every
`Code` renders to a packet that imports to itself: `decodePacket_term` lifted to the subtype).

### 2.2 Hygiene under nested generators

Secures (READ): de Bruijn indices. α-equivalence is syntactic identity, `encode_injective` makes
`treeEq` a decision procedure for it, and `Term.substitute`/`liftSubstitution` are capture-avoiding
by construction; `Ahead` is a congruence through binders (`Ahead.lam`), so rewriting under a binder
is already handled. Adams' Criterion 1 is then: substitution commutes with the generator, which is
`ahead_substitute` and `steps_substitute` (`Equiv/Reduction.lean`). Threatens (INFERRED): a
generator written *in Core4* (a law or a slot candidate that builds a quotation as `Data`) builds a
*tree of labels*; the binder discipline of that tree is whatever the generator wrote, and nothing in
`Data` knows a `bound` from a `nat`. Hygiene for Core4-written generators is therefore a property of
the *importer* (decode refuses a tree whose indices escape: `Scoped`), not of the generator. Nested
generators (a quotation containing a quotation) need Bawden's level count only if quotations are
constructed by splicing *terms* into *terms*; if they are constructed as `Data` and imported once at
the end, there is one level. Theorem (PROPOSED, T8): `import_scoped`: an imported `Code Ψ A θ` is
`Scoped Ψ.length`, and `msubst` with fillings `Scoped |Ψ|` preserves `Scoped |Ψ|` (lifting
`liftSubstitution_fillTerm`, which exists for `Scoped 0`).

### 2.3 No scope extrusion

Secures (READ): three walls. `resume` evaluates the response in `[]`, so code that reaches the
machine through a turn is run closed; `calculus_typed_msubst` requires `Scoped 0` fillings, and
`open_filling_tooth` shows exactly the KKS-2015 example (`bound 1`, the linear hypothesis, filled
into a template, double-used, refused); `Scoped n (.hole k σ)` requires every term of `σ` scoped,
so a delayed substitution cannot carry an escaped index. Threatens (INFERRED): the lazy heap. A
`closure body environment` holds *addresses*; a quotation taken from a value (never from a term)
would have to reify addresses, and an address is a name that is neither bound in the quotation nor
global — scope extrusion of the heap into the code, Kiselyov's `CSP of Obj.t`. The reference
semantics avoids it only because `Data` extraction refuses closures (`executableValue`). Theorem
(PROPOSED, T9): `quote_no_address`: a quotation the kernel produces from any machine state is a
`Data` tree with no `Address` in it, and `Data.execute` refuses every `closure`/`specification`/
`prototype` — the first half exists; the second is a statement about the kernel's `quote`, which is
why `quote` must be defined on `Term`, not on `RuntimeValue` (§3.1).

### 2.4 Cross-stage persistence

Secures (READ): `Ty.isData` is the lift-able fragment (naturals, labels, booleans, rows, variants);
a Plan and a response are `Data` (`Ty.isPlan`); `resume (response : Term)` takes a closed term, so
the kernel's answer is lifted by value; a global is a `label` naming a package member (REFLECTION:
`M.S#claim#l`), Kiselyov's "named reference into the libraries assumed available at a future stage".
Threatens (INFERRED): custody (`Ty.custody`) and once-closures. `custody` is not shareable and not
data; it is exactly Kiselyov's open channel. Astra's rule ("move live resources only through an
explicit ownership/handle protocol") is the `code_with_csp` construction: the resource stays in the
present stage, the quotation mentions a *hypothesis* of custody type, and the stage-separated let is
a slot whose filling is supplied at the view where the resource is live. A quotation therefore
persists *hypotheses*, never values, of non-data type. Theorem (PROPOSED, T9 second half):
`csp_data_or_hypothesis`: every leaf of a quotation is a literal of `isData` type, a `bound` index
into `Ψ`, or a package-member label; nothing else. The `affine ≡ linear` collapse of
ALGEBRAIC-SUBTYPING §5.1 is a threat here specifically: a quotation that mentions a `linear` custody
hypothesis twice is refused by `safeUses` today, but a coercion wrapper relabelling it `affine` would
be accepted and dropped — the splice must count uses on the *original* binding.

### 2.5 `run` safety

Secures (READ): `resume_keeps_heap_and_stack` gives `.evaluate response []`; the yield/resume
protocol is the only way a term enters a running program after start (`Machine.initial`,
`resume`); `perform_under_update_refused`. So `run` in Core4 is a turn whose response is the code,
and it is closed by the machine's construction, not by a type. Threatens (INFERRED): the typing of
the response. `PartialTyping.perform` types `perform plan : computation planType response response`,
so a program expecting `response : Ty` and resumed with a spliced term of another type goes
`wrongValue` at runtime; `MachineTyping` does not yet relate `resume` to the activity's declared
response type. That is `tmUnquoteTyped`'s job and it is the kernel's. Theorem (PROPOSED, T6′):
`resume_typed`: if the yielded state's activity is typed `computation P R C` and `response ∈ Code [] R
θ`, the resumed state is well-typed (the `MachineTyping` invariant extends across `resume`); tooth: a
response of the wrong type is refused by name at import, never reaches `wrongValue`.

### 2.6 Intensionality and the observer ladder

Secures (READ): REFLECTION.md already states the law ("a rewrite justified by ≈b may be applied only
where no metadata observer can reach the rewritten specification") and the machine has no observer
of a closure's code; `≈b` is a congruence by definition (all contexts, `BEquiv`), and `mix_assoc`
holds under it while failing under ≈r (probes R01/R02). `Law/Claim.treeEq` is ≈q on closed terms
already, used by a checker. Threatens (INFERRED): (i) `quote` as a *constructor* with
`Step.quoteValue` (VISION §3.4) would be Kavvos's Tale 2: any context could then separate ≈b-equal
terms, and `bequiv_of_steps` (reduction is a ≈b-equivalence) would be false, since `quote t` and
`quote t'` for `t ⟶ t'` differ. The whole `Equiv/` spike rests on reduction being invisible. (ii)
The lazy heap makes a value's "code" time-dependent: the same closure's environment points at cells
that are `suspended` now and `cached` later, so a quote of a value is not even ≈q-stable across
ticks. (iii) Laws are judged by running a probe on the machine (`Law/Machine.judge`); a law that
compares quotations is sound only if the quotation it compares was produced by the kernel from the
candidate's *term*. Theorem (PROPOSED, T3–T5): `≈q` := equality of `encode` on closed terms;
`observer_ladder : ≈q ⊆ ≈r ⊆ ≈b` (first inclusion by `encode_injective` then `BEquiv.refl`; second
by REFLECTION's definition); `quote_not_congruent` (tooth, Barendregt's pair: `app (lam (bound 0))
(lam (bound 0))` and `lam (bound 0)` are ≈b by `bequiv_of_steps` and not ≈q); `rewrite_sound_below`
(§3.4), the Core4 form of "no congruence under box". The Gödel–Löb discipline (INFERRED): Core4's
intensional recursion is `instantiatePrototype` — `fix (λself. λseed. prototype spec (spec self
seed)) seed` — where `reflect self` returns the stored specification *unforced*
(`prototype_metadata_unforced`); that is `fix z in M ⟶ M[box(fix z in M)/z]` with `z` of modal type,
the term receives its own description and never a quote of its own value. REFLECTION's open question
(`Y(R∘M)` inside the knot or `R(Y M)` outside) is Löb's rule versus `□A → A`-plus-`Y`; the literature
says inside the knot, with the stored description a *term*, is the consistent one.

### 2.7 Semantics preservation of staging (erasure, let-insertion)

Secures (READ): the reference semantics is call-by-name, where "staging … is better behaved, since
the semantics of quotation remains aligned with the underlying CBN semantics" (Tan–Wei §1), so the
pure erasure theorem has Inoue–Taha's shape without let-insertion; `Ahead` is the relation Tan–Wei
build by hand (a splice step is a reduction in
context, `Ahead.run`); Core4 has no `let`, and sharing is expressed by the term's own binding sites
(β arguments, record fields, `inject` payloads, `self`/`super`), so "let-insertion" is allocating a
field or an argument thunk, which the machine already does (`allocateFields`, the `argument` frame).
Threatens (INFERRED): (i) cost. `≈b` is blind to sharing (EQUIV-PLAN §2.1), so a splice that
duplicates a quotation at two use sites is ≈b-sound and ≈c-unsound: `twice` without let-insertion is
exactly the loss of sharing Maziarz refuses to hash away ("let-expressions express operational
choices about object lifetimes and evaluation order"). (ii) Yields are Tan–Wei's first-stage
effects. A generator that `perform`s while reifying a branch does what their §6.1 conditional does;
and a splice under a shared cell is a cached effect — `sharedEffect` is already the refusal, and it
is the right one (KKS 2011's "effects confined to the scope of generated binders" is "no perform
under an update frame"). (iii) Blackholes: a quotation of a self-referential `fix` body spliced twice
creates two knots where the erased program had one (`EQUIV-PLAN` definition 3's "sharing-identity
test"). Theorem (PROPOSED, T10–T12): `splice_sound_pure` (for `perform`-free `Code`, `splice` is an
`Ahead` step, hence ≈b-sound, via `ahead_substitute`); `splice_sound_turns` (`Interaction` traces
agree: EQUIV-PLAN lane 1, `Yields` under `Ahead`); `splice_cost` (a splice that let-inserts every
quotation used more than once is within a constant of the erased program under definition 2,
`≈c`, with the constant the one `mix_assoc` already pays, `κ = 7` ticks).

### 2.8 Pattern matching on code

Secures (READ): `Data` is a sum, `case` is its eliminator, and a law written in Core4 can `case` on a
quotation's tree today (REFLECTION's "provenance inspectable by `match`"). Threatens (INFERRED): a
`case` arm that extracts a subtree under a binder and returns it is Stucki's non-closed pattern;
nothing in `Data` prevents it, and the importer would refuse the result as not `Scoped`, late and
without naming the pattern. Theorem (PROPOSED, T13): `pattern_closed`: the kernel's matcher on
`Code Ψ A θ` binds a subterm under `k` binders as `Code (Ψ ++ Δ) B θ` with `|Δ| = k` (Mœbius' rule:
the context grows by the binders crossed), never as `Code Ψ B θ`; the tooth is Stucki's
`'{ (x: Int) ⇒ x + 1 } match case '{ (y: Int) ⇒ $z }`.

### 2.9 Verified round trips

Secures (READ): `state_roundTrip` (checkpoint codec), `decodePacket_term`, `decode_json`,
`encode_injective`. Threatens (INFERRED): there are three encodings of a term in the tree
(`TermTraverse.encode : Term → Tree Tag`, the checkpoint `Tokens`, the JSON packet) and `Data` is a
fourth; `quote` needs one canonical one with a proved round trip and a digest over *that* encoding,
or two quotations of one term get two addresses. Theorem (PROPOSED, T1–T2): `quote_roundtrip :
unquote (quote t) = some t`; `digest_of_quote`: `address t := digest (encodedBytes (quote t))` and
`address t = address t' → t = t' ∨ Collision H` (`binds_or_collides` composed with
`quote_roundtrip`).

### 2.10 Mirrors

Secures (READ): nothing yet; `reflect` and `metadata` are ambient (VISION §4.1's "missing half").
Threatens (INFERRED): `quote` at the kernel level is *more* ambient than `reflect` — every law
could read every candidate's code — and GENERATED §3.2's confidential-refusal tension returns.
Theorem (PROPOSED, T14): `mirror_attenuates`: a `Mirror` is `Data` naming a target and a depth in
`structure ⊑ metadata ⊑ code`; the kernel's `quote` takes a mirror of depth `code`; a mirror derived
from a mirror has depth ≤ its parent's. This is Bracha–Ungar's stratification as a lattice, and it
lands without touching `Term`.

### 2.11 Boundaries

Secures (READ): the retracts exist (`state_roundTrip`, `decodePacket_term`), and the checker's
`sound` theorems are the semantic model of a certificate. Threatens (INFERRED): `project` for a
quotation is the importer, and an importer that *repairs* (prepares annotations, `Decides.Prepares`)
is a projection that is not the inverse of embedding on the nose — it is one up to `Reannotates`,
and that is the EP pair's "up to" that graduality needs. Theorem (PROPOSED, T15): `code_boundary :
Boundary (Code Ψ A θ) Packet` with `project ∘ embed = id` and `embed ∘ project ⊑ id` (an imported
packet re-rendered is the packet up to annotation preparation).

## 3. The design

### 3.1 `quote` is a function of the kernel on terms, not a step of the machine on values

PROPOSED, with the reasons of §1.4, §1.6, §2.3, §2.6. `quote : Term → Data` (Lean, kernel side) is
the canonical first-order rendering of a term: the `Tree Tag` of `TermTraverse.encode` written as a
`Data` variant row `Syntax` (a built-in sum like `SpecMeta`, declared by no module). It is total,
injective (`encode_injective`), and defined on *terms the kernel holds*: a slot's candidates, a law's
code, a page's cells, a package member. It is never applied to a `RuntimeValue`, and the machine has
no `quote` frame. A program that wants the code of something names it (a mirror of depth `code`) and
yields; the kernel answers with the quotation as `Data`. This keeps `Equiv/` true (`bequiv_of_steps`
survives, because no context sees reduction), keeps the heap out of the code (no address is data),
and makes CSP Kiselyov's: data by value, members by name, resources by hypothesis.

### 3.2 The representation

PROPOSED. Kernel side:

```
Code (Ψ : Context) (A : Ty) (θ : Assumptions) :=
  { t : AnnotatedTerm // t.assumptions = θ ∧ Calculus.Typed Ψ t A }
```

with the derived indices `uses : Uses` (the certificate's `c.uses`, bounded by `UsesLE` under
substitution), `observers : Level` (the greatest observer level any `metadata`/`reflect` position in
`t` demands of its operand; computed by a fold over the term, used by `rewrite_sound_below`), and
`stage : WorldView` (the view at which `θ` and the package members named in `t` are pinned; a
quotation is usable at a view only while those pins hold — the slot's `supports`, so stage is not a
new field but the existing `Slot.supports` of the quotation as a candidate). Astra's six-field
signature is therefore realized as: `stage` = supports, `theory` = `θ`, `Γ` = `Ψ`, `A`, `usage` =
`c.uses`, `observers` = the census; the only one that is a *new* computation is the census.

Program side: a quotation is a value of the built-in sum `Syntax` (so `Ty.isData`, shareable, a
valid Plan payload and response). The typed index lives in the kernel only. This is REFLECTION.md's
choice ("metadata as ordinary data needs no Core4 change, keeps every safety theorem as it is") made
again for code, and it is MetaCoq's phase split (the extractable part sees `Ast.term`, the typed
part sees `(A; t)`).

### 3.3 The checked importer and `splice`

PROPOSED. `import : Context → Ty → Assumptions → Data → Except Refusal (Code Ψ A θ)` = decode to
`AnnotatedTerm` (the packet decoder's term half), check `Scoped Ψ.length`, run `checkAgainst` under
`θ`; refusals name the index that escaped, the position that failed to check, or the assumption
that differs. `splice : Code Ψ A θ → (σ : Fillings Ψ) → Code Ψ′ A θ` is `msubst` guarded by
`calculus_typed_msubst` generalized (T7): a filling for hypothesis `x : Ψ[x]` is a `Code Ψ′ (Ψ[x]).type
θ` (today it must be `Code [] …`), and the uses of the result are `uses t` with each occurrence of
`x` replaced by the filling's uses — Astra's "substitution with usage composition", Ângelo et al.'s
side condition "`τ` linear or `Γ` unrestricted" (PB `angelo2026-…` §4: "prevents free variables of
linear types in σ from being duplicated or discarded"), stated for a uses vector rather than a
context split: a filling that uses a `linear`/`affine` hypothesis may be substituted for a hypothesis
used at most once. `open_filling_tooth` becomes the first tooth of the rule. At the Core4 level,
`splice` is a turn: the program yields `splice{code, fillings}` and is resumed with the imported
term, which the machine evaluates closed (§2.5); the kernel refuses the turn when `import` refuses,
by name.

### 3.4 The observer ladder and `rewrite_sound_below`

PROPOSED. `≈q t t′ := encode t = encode t′` (α-equality; with content address `address t = address
t′` as its decidable shadow under `binds_or_collides`); `≈r` as REFLECTION (≈b and equal `metadata`
on every specification position); `≈b` as `Equiv/Behaviour`. `observer_ladder : ≈q ⊆ ≈r ⊆ ≈b`.
`rewrite_sound_below (k) : a ≈k b → ∀ C, census C ≤ k → C[a] ≈k C[b]`, where `census C` is the
greatest level of an *intensional frame on the hole's path*: a `metadata`/`reflect` frame whose
operand is the hole gives level r; a `quote` *position* (a candidate slot, a law's code, the metadata
operand of `specification`) gives level q; every other frame gives b. Proof shape: for `k = b` it is
`BEquiv` being closed under contexts (definitional) plus `Ahead` congruence; for `k = r` it is the
same after showing no frame on the path can reach a `metadata` of the hole; for `k = q` the
hypothesis `census C ≤ q` is vacuous (every context has census ≤ q) and the conclusion is syntactic
congruence of `encode`. This is Davies–Pfenning's and Kavvos's "no congruence under box" written as
a theorem about contexts rather than an absent rule, and it is what a `RewriteJudge` cites per step.

### 3.5 Mirrors as the capability discipline

PROPOSED. `Mirror := Data {over : Name, depth : structure | metadata | code}`; the kernel's
`quote`, and the program's `reflect`/`metadata` once they take a mirror, check `depth`; a package
law on the `invoke` occasion decides which depths it grants to whom; `mirror_attenuates` is the
lattice fact. Confidential refusals (GENERATED §3.2) become "the mirror you hold has depth
`metadata`", named.

### 3.6 Where the lazy heap and yields force a different construction than the CBV literature

INFERRED, from §2.7.

- *Erasure is easier for divergence and harder for sharing.* Under CBN the pure erasure theorem is
  Inoue–Taha's and needs no let-insertion for *correctness*; it needs let-insertion for *cost*, and
  Core4's unit of cost is definition 2/3 of EQUIV-PLAN, not contextual equivalence. Tan–Wei's binary
  relation transfers as the shape of `splice_sound_pure`; their let-insertion transfers as the
  obligation of `splice_cost`, with "let" meaning a record field or an argument thunk.
- *First-stage effects are yields, and they are already refused where they would be cached.* Their
  references-in-stage-2-only restriction becomes: a `Code` may contain `perform` (the generated
  program may yield), but a generator (a law, a slot resolution) performs nothing except through the
  audited fold; a splice under an update frame is `sharedEffect`. What does not transfer: their store
  is a stack with deterministic allocation and no sharing; our `sharedEffect` rule has no analogue in
  their calculus and must be proved to be the right refusal (that a spliced `perform` inside a shared
  cell would duplicate or lose a turn), which is `splice_sound_turns`.
- *Blackholes are a new observation.* A quotation that mentions `self` and is spliced twice gives two
  knots; under ≈b that is invisible, under definition 3 it is a different `divergent` address. The
  literature has no counterpart; the theorem is EQUIV-PLAN's sharing-identity test restated for splice.
- *Checkpoints are the one place a value legitimately becomes data.* `Checkpoint.encodeState` reifies
  a whole heap, addresses included, and `state_roundTrip` is its round trip. That is Kiselyov's
  *online* lifting (sharing with a still-running generator), and it is sound exactly because the
  decoded state is the same program, not a quotation spliced into another. The design keeps the two
  apart: a checkpoint is not a `Code`, and `inspectCheckpoint` (Astra's table) is a capability, not a
  quote.
- *Stability (Kovács) is free at the kernel and false in the program.* The kernel may compute on de
  Bruijn depths; a Core4 program given a quotation as `Data` may not be given a way to observe depth
  that a later weakening would change — which the `Syntax` sum does not need to expose, since binders
  are positions, not numbers, in the tree the program sees.

### 3.7 The promotion criterion

PROPOSED. `quote`/`splice` enter `Term` only when these hold as theorems over the library:
(P1) `quote_roundtrip` and `digest_of_quote` (T1–T2); (P2) `observer_ladder`, `quote_not_congruent`,
`rewrite_sound_below` at all three levels (T3–T5); (P3) `import_sound/complete`, `resume_typed`
(T6, T6′); (P4) `contextual_msubst_uses` (T7) with `open_filling_tooth` as its tooth; (P5)
`splice_sound_pure`, `splice_sound_turns`, `splice_cost` (T10–T12). And then the promotion itself is
a *different* calculus with the following costs, each named: `Term` gains `code : Data → Term`?
No — it gains nothing for `quote` (the kernel keeps it) and gains `splice : Term → Term` typed
`Code A → A` only as sugar for a yield whose response is the imported term, so `Machine` gains no
frame (a splice is a `perform` with a kernel-recognized plan label), `Check` gains the typing rule
`splice e : computation Syntax A A` for `e : Syntax` (an activity, since it is a turn), `Equiv` gains
nothing (`Ahead` has a `perform` arm), `Law` gains `≈q` as a decidable probe atom (`treeEq`, which
exists). The only promotion that would touch `Term`'s constructors, and that I argue against until
(P1)–(P5) hold *and* a consumer needs it, is a program-level `quote` on values; §5 has the papers'
words. The honest statement: Core4 can have `quote` as a kernel function and `splice` as a turn
without a single new `Term` constructor, and that is Astra's order realized exactly.

## 4. The theorem list, in the order a lane should prove them

Each: property, shape (Lean-shaped prose), tooth (the mutation that must fail).

1. **T1 `quote_roundtrip`** (verified round trip, §1.9). `quote : Term → Data`, `unquote : Data →
   Option Term`, `unquote (quote t) = some t`; `quote` factors through `TermTraverse.encode`. Tooth:
   drop one constructor's tag and the round trip of a term using it fails.
2. **T2 `digest_of_quote`** (content address). `address t := digest (bytesOf (quote t)) 0`;
   `address t = address t′ → t = t′ ∨ Collision cshake256` by `binds_or_collides ∘ T1`. Tooth: a
   length-only hash (`lengthHash_binding_fails`) gives two terms one address.
3. **T3 `observer_ladder`** (intensionality). `QEquiv t t′ := encode t = encode t′`; `REquiv` per
   REFLECTION; `QEquiv ⊆ REquiv ⊆ BEquiv` (`encode_injective`, `BEquiv.refl`). Teeth: `mix_assoc`
   holds for ≈b (exists), fails for ≈r (R01/R02 ported), fails for ≈q (`decide` on `encode`).
4. **T4 `quote_not_congruent`** (intensionality). `app (lam (bound 0)) (lam (bound 0)) ≈b lam (bound
   0)` (`bequiv_of_steps`) and `¬ QEquiv` of them. Tooth: making ≈q coarser than `encode` equality
   (e.g. up to one β step) makes the pair equal and the tooth fail.
5. **T5 `rewrite_sound_below`** (intensionality; the rewriter's licence). `census : Context → Level`
   over the hole's frame path; `a ≈k b → census C ≤ k → C[a] ≈k C[b]` for `k ∈ {q, r, b}`. Tooth: a
   context with a `metadata` frame on the hole and `k = b` separates two ≈b specs (REFLECTION's probe).
6. **T6 `import_sound` / `import_complete`** (typed quotation, boundary). `import Ψ A θ d = .ok c →
   c : Code Ψ A θ`; `import Ψ A θ (quote c.val.term) = .ok c′` with `c′.val.term = c.val.term`. Tooth:
   `annotation_presence_not_coverage` (exists) shows an importer that trusts supplied annotations is
   not complete. **T6′ `resume_typed`** (`run` safety): the `MachineTyping` invariant crosses `resume`
   when the response is `Code [] R θ` for the activity's declared `R`. Tooth: a response of type `Nat`
   where `R` is a row reaches `wrongValue` without the premise.
7. **T7 `contextual_msubst_uses`** (typed quotation under quantities; the CMTT theorem with usage
   composition). For `c : Checked t Ψ` and fillings `σ x = some f` with `f : Code Ψ (Ψ[x].type) θ`
   (not `Code []`): `msubst σ t` is checked at `c.type` with uses `c.uses[x ↦ 0] + Σ_x c.uses[x] ·
   f_x.uses`, provided for every `x` with `c.uses[x] > 1` the filling's uses are all on
   `unrestricted` shareable hypotheses (Ângelo's "`τ` linear or `Γ` unrestricted"). Tooth:
   `open_filling_tooth` (exists) — a `bound 1` filling for a linear hypothesis used once in a template
   that uses hypothesis 0 twice is refused naming hypothesis 1.
8. **T8 `import_scoped` / `splice_scoped`** (no extrusion). An imported `Code Ψ A θ` is `Scoped
   Ψ.length`; `splice` with `Scoped |Ψ′|` fillings yields `Scoped |Ψ′|`. Tooth: a `Data` tree with
   index `Ψ.length` is refused naming the index.
9. **T9 `quote_no_address` / `csp_data_or_hypothesis`** (CSP). Every leaf of `quote t` is a literal
   of `isData` type, a `bound` index, or a member label; `Data.execute` refuses closures (exists,
   `executableValue`). Tooth: a `quote` extended to `RuntimeValue.closure` produces a tree whose
   `unquote` is `none` for every closure with a non-empty environment.
10. **T10 `splice_sound_pure`** (erasure, pure). For `perform`-free `c` and fillings, `splice c σ`'s
    term is `Ahead` of the erased term `instantiate`d, hence `≈b` (`ahead_substitute`,
    `bequiv_of_ahead`). Tooth: a splice that drops a filling's `fix` knot is not `Ahead`.
11. **T11 `splice_sound_turns`** (erasure with yields). `Interaction` traces of the spliced and erased
    programs agree (`Yields` is preserved by `Ahead`: EQUIV-PLAN lane 1), and a splice under an
    update frame is refused `sharedEffect`. Tooth: Tan–Wei's two-branch conditional, with
    `perform` for the write, gives one trace spliced and two erased unless the generator yields
    nothing while reifying.
12. **T12 `splice_cost`** (erasure under laziness). Under EQUIV-PLAN definition 2, a splice that
    allocates one thunk per quotation used more than once is within the `mix_assoc` constant of the
    erased program. Tooth: Tan–Wei's `twice` without the thunk is unbounded in the number of uses.
13. **T13 `pattern_closed`** (pattern matching). A match on `Code Ψ A θ` binds a subterm under `k`
    binders at `Code (Ψ ++ Δ) B θ`. Tooth: Stucki's `(x) ⇒ x + 1` against `(y) ⇒ $z`.
14. **T14 `mirror_attenuates`** (mirrors). `depth (derive m) ≤ depth m`; `quote` needs `code`. Tooth:
    a `metadata` mirror cannot `quote`.
15. **T15 `code_boundary`** (EP pair). `project ∘ embed = id` on `Code`, `embed ∘ project ⊑ id` up to
    `Reannotates`. Tooth: an importer that forges a shareable type for a `custody` member is refused
    (`agree_never_manufactures_shareability`'s shape).
16. **T16 `stage_collapse`** (VISION R3; last). Re-elaboration at a view where every pin a quotation
    cites is resolved yields a term ≈q to the genesis elaboration with pins substituted. Depends on
    T6, T7 and `Spec/Ecosystem`; not for the first lane.

**First lane's scope** (briefable): T1–T5 and T6 (not T6′), T8, T14, in `lean/Obend/Core/Code.lean`
(`quote`, `unquote`, `address`, `Code`, `import`, `Mirror`) and `lean/Obend/Equiv/Quote.lean`
(`QEquiv`, `REquiv`, `observer_ladder`, `quote_not_congruent`, `census`, `rewrite_sound_below`),
touching no `Term` constructor, no `Machine` step, no `Check` rule; `≈r` needs REFLECTION's probes
R01/R02 ported from minidregg's `AssociationProvenance.obend` as Lean terms. Ground truth for the
lane: `encode_injective` (`Core/TermTraverse.lean:144`), `binds_or_collides` (`Core/Digest.lean`),
`BEquiv`/`bequiv_of_steps`/`mix_assoc` (`Equiv/Behaviour.lean`), `calculus_typed_msubst`
(`Slot/Core4.lean:267`), `Checked` (`Core/Check.lean`), `Scoped` (`Core/Invariant.lean:16`). The
second lane is T7 (the usage-composed contextual substitution) alone, because it is the one that
changes a load-bearing premise (`Scoped 0`) and ALGEBRAIC-SUBTYPING §5 must be decided first
(whether `linear` separates from `affine` in the checker); the third is T10–T12 with EQUIV-PLAN's
lanes 1–2.

## 5. What I refuse, with the papers' words

- **`quote` on a value of the running machine** (VISION §3.4's `Step.quoteValue`). Taha–Sheard:
  "Function values cannot be lifted into code using Lift, as we cannot derive a high-level intensional
  representation for them in general." Kiselyov 2026: "how exactly one converts an opaque closure to
  the source code that evaluates to the same (intentionally equal or only extensional equal?)
  closure"; "It would be bizarre if running mutcode tried to resurrect the generator process." On the
  lazy heap it is worse than opaque: the environment is a set of addresses in `suspended`/`evaluating`/
  `cached` states, so the "code" of a value changes with the tick. Refused; `quote` is on terms.
- **`quote` as an ambient observer any context may apply.** Kavvos (Wand): "Such a language can
  internally distinguish any two terms in the language, as long as they are not equal up to renaming";
  it would falsify `bequiv_of_steps` and empty `Equiv/`. Refused; `quote` needs a mirror and is a
  kernel function.
- **≈b as a congruence through a quotation.** Davies–Pfenning/Kavvos: "we do not include the
  following congruence rule for the modality". Refused; `rewrite_sound_below` is the replacement.
- **A generator that yields while reifying, or a splice under a shared cell.** Tan–Wei §6.1: "the
  generated code may depend on the order in which the branches are reified"; §7: "the main obstacle
  is that λc-terms and 2nd-stage conditionals cease to be evaluation contexts after erasure";
  Kameyama–Kiselyov–Shan 2011: "blindly adding effects renders multilevel types unsound"; Inoue–Taha
  via Tan–Wei: "imperative MSP is not yet ready". Refused; `sharedEffect` stays, generators act only
  through the fold.
- **Environment classifiers as the open-code discipline.** Kameyama–Kiselyov–Shan 2015: "environment
  classifiers are too coarse-grained to prevent scope extrusion while still allow effectful
  manipulation of open code"; Calcagno–Moggi–Taha: "inference for the full classifier-based system
  fails"; Mœbius: classifiers do "not list the variables that may occur". Refused; `Code Ψ A θ` lists
  `Ψ`.
- **Dynamic extrusion detection as the only guard.** Kiselyov 2026: "scope extrusion may manifest in no
  compilation errors: just wrong results." Kept only as the importer's refusal name; the guarantee is
  `import_scoped`.
- **CSP of live resources, or `lift` at all types.** Kiselyov: "not all values are copyable/serializable:
  for example, open channels and mutable cells are not"; Stucki et al. 2021: "we cannot support
  cross-stage persistence of local variables" across machines. Refused for `custody` and once
  closures; they cross as hypotheses (stage-separated lets), never as data.
- **Graph equivalence for ≈q** (hashing a term modulo sharing). Maziarz et al.: "let-expressions express
  operational choices about object lifetimes and evaluation order, and so graph equivalence is too
  strong". Refused; ≈q is α, and sharing is syntactic in Core4's term, which is why `splice_cost` can
  be stated at all.
- **The tower checking its own admission change.** Coq Coq Correct: "we are not claiming to prove the
  consistency of Coq in Coq"; Devriese–Piessens: the primitives "imply the consistency of our object
  theory", hence live in a strictly stronger theory. Refused (Astra's §2.3 last paragraph stands): a
  `relaw` of the checker is judged by the current checker.
- **A program observing de Bruijn depth.** Kovács 2022: "we cannot make decisions based on sizes of the
  object-theoretic scopes, since these sizes may be changed by substitution." Refused for the
  program-side `Syntax` sum, which shows binders as positions.
- **`eval` plus unrestricted intensional fixed points.** Kavvos 2017: "the combination of eval and
  intensional fixed points leads to non-termination" (`Ω_A = fix z in eval z`). Core4's
  `instantiatePrototype` keeps the description unforced (`prototype_metadata_unforced`); refused is any
  `reflect` that forces its target to produce it.

## 6. Papers: fetched, present, missing

Fetched into `~/paperbin/` for this study (all with `.txt` siblings): Davies 1996 (BRICS RS-95-51
report, the LICS version; JACM 2017 not fetched), Nanevski 2002, Nanevski–Pfenning 2005, Kavvos thesis,
Gratzer–Kavvos–Nuyts–Birkedal MTT (LMCS 2021), Taha–Sheard 2000 (author preprint via Wayback, from
PostScript), Taha–Nielsen 2003, Calcagno–Moggi–Taha 2004, Moggi–Taha–Benaissa–Sheard 1999 (added: the
first sound open/closed integration and the `run with` rule), Bawden 1999 (added: nested
quasiquotation), Kameyama–Kiselyov–Shan 2011 (JFP) and 2015 (SCP), Rhiger 2005 (TFP 2005, not 2011/12),
Kovács 2024 (single author; not Kovács–Kaposi), Annenkov–Capriotti–Kraus–Sattler (arXiv v5 2026),
Rompf–Amin 2015, Stucki–Brachthäuser–Odersky 2021 (authors differ from the brief), Adams 2015,
Dybvig–Hieb–Bruggeman 1992 (IU TR 355), Devriese–Piessens 2013, Sozeau et al. MetaCoq (JAR offprint),
Coq Coq Correct (POPL 2020), Chapman 2008, Altenkirch–Kaposi 2016, Kaposi–Kovács–Kraus 2019 (not
Altenkirch), Christiansen–Brady 2016, Berger–Tratt 2015, Berger–Tratt–Urban 2017, Maziarz et al. 2021,
Barendregt 1991 (scan, OCR text), Jay–Given-Wilson 2011, Jay–Vergara 2014 (*Confusion in the
Church-Turing Thesis*; no paper titled *Confluence of extensional and intensional computation*
exists), Gratzer–Sterling–Birkedal 2019 (added, minor: NbE for □), Pientka–Dunfield 2010 (Beluga),
Forster–Kunze 2019 (added: certifying extraction with time bounds, the precedent for `splice_cost`).
Already present and read: Davies–Pfenning 2001, CMTT 2008, Mœbius 2021, Kavvos 2017, Kovács 2022,
Xie et al. 2022, Stucki et al. 2018, Ullrich–de Moura, New–Ahmed, Bracha–Ungar, Amin–Rompf, Lurk audit
(`.txt` made now), Tan–Wei 2026, Kiselyov 2026, Perconti–Ahmed, Patterson–Ahmed, Cocon, Murase et al.
2023 (polymorphic contexts), Ângelo et al. 2026 (added to the reading: linear CMTT, the only prior
substitution principle with quantities). Not obtained in the form named: Davies 1996 JACM version;
Rompf–Odersky LMS 2010 (the existing PDF is slides, as Astra noted; the project page was used);
Jay–Vergara under the brief's title (does not exist). Nothing on the list is missing outright.

## 7. The one property we are most likely to get wrong

INFERRED. Cross-stage persistence — what may cross from a run into code. Every other property has a
wall already standing in the tree (`Scoped 0`, `resume … []`, `treeEq`, `encode_injective`,
`sharedEffect`); this one has a wall (`executableValue`) that the vision's own design (`Step.quoteValue`,
a quote of a value content-addressed like Lurk's pointer digest) would knock down, and the failure
would be silent: a quote of a heap value is well-typed `Data`, hashes fine, round-trips to a term
with dangling addresses or with a forced thunk, and differs between two ≈b-equal programs by the
tick at which it was taken. The literature took twenty years to say what crosses (data by value,
globals by name, everything else as a hypothesis of a stage-separated let), and it said it after
building the other thing first. The runner-up is T7: the usage-composed contextual substitution,
where ALGEBRAIC-SUBTYPING §5's `affine ≡ linear` collapse means a splice can launder a once-resource
unless uses are counted on the original binding.
