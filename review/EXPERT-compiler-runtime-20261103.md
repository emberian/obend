# Expert read: compiler and runtime (`compiler-runtime`), 2026-11-03

The person in the chair has shipped a partial-evaluation JIT, has written a Futamura generator by
hand, and reads interaction nets. The bar Ember set for this part of the system is "a runtime so
trim but powerful it makes GraalVM weep" and "staged reflective metaprogramming the Harvard
metareflection lab would nod at". I read the working tree (not HEAD), ran only the already-built
`lean/.lake/build/bin/obend` and the Python runners, and edited nothing but this file.

Tags: **READ** (I opened it; `path:line`), **INFERRED** (from READ facts), **PROPOSED**. Every number
has its command.

---

## 0. Verdict in one paragraph

The reference semantics and its machine are real and better than most research runtimes get:
a weak-head call-by-name `Step` relation (`lean/Obend/Core/Term.lean:321-375`), a Sestoft-style
lazy machine (`lean/Obend/Core/Machine.lean:126-286`), a *proved* representation-adequacy
instance for every closed term (`lean/Obend/Core/Proofs/Completeness.lean:1167`
`coreRepresentation : Representation State (Scoped 0)`), a `@[csimp]`-installed fast path proved
equal to it (`lean/Obend/Core/MachineFast.lean`), a flattening compiler with a bisimulation-up-to
proof (`lean/Obend/Leaf/Flatten.lean:355 flatten_sound`, `UpTo.lean`), and a deoptimization story
that is literally a slot read (`lean/Obend/Leaf/Specialize.lean:165-226`). That is the tax
Gemini said was paid, and for the first Futamura projection and the fallback machine it is.

Everything that would make a JIT person look up from their coffee is not there. **The "2nd and
3rd Futamura projections" do not self-apply anything** (§2.1). **`Leaf/BendTT.lean` is not a
translation to BendTT**, and its C and interaction-net emitters produce text no tool could run
(§2.2). **No emitted artifact is executed by anything but the Lean binary**, except the tiny RTL
path through Verilator (§1). **The specializer (`dataPinSpecialize`/`specializeBook`) is reachable
from no CLI command**; `obend emit` succeeds on 9 of 713 definitions across 159 `.obend` files, all
of them in `tests/obend-source/` (§2.3). The lowering of `n + n` from Lean arrives at the machine
as dictionary-passing code with four erased-argument applications, and `sumTo 30000` exhausts the
10-million-tick budget (§2.3). The cost semantics is honest and narrow: a factor-4 tick bound on a
fragment of first-order objects, with the general completeness explicitly unproved (§2.5).

Gemini's two halves: the hard tax is paid for *flattening, one-shot specialization-as-slot, and
the fallback machine*; it is **not** paid for staging (no self-applicable specializer exists in
Core4), and the compiler that would collect on it is not merely unwritten, its advertised
pieces are placeholders wearing the names of the real thing.

---

## 1. What actually executes what (READ)

| Artifact | Produced by | Executed by | Evidence |
|---|---|---|---|
| Core4 `Term` of an `.obend` program | `Obend.Spec.Elaborate` | `Machine.runBounded` inside the `obend` binary (Lean-compiled interpreter) | `lean/Obend/Main.lean:175` (`run`), `:636-637` (`machineNat`, limits `⟨1000000,1000000⟩`, 10 M ticks) |
| `Leaf.Book` (JSON) | `obend emit` (`Main.lean:659-685`) | Only `Book.link` (a Core4 term, `Leaf/Emit.lean`) run on the same machine; the JSON is read back by `obend specialize` to rebuild pins, never executed | `Main.lean:681-682`, `:688-720` |
| `BBook` / `BTerm` ("BendTT") | `emitBendTT` (`Leaf/BendTT.lean:723`) | `runB` in Lean (`BendTT.lean:437`), used only by one `decide +kernel` theorem over `ReviewMember` | `lean/Obend/Teeth/Leaf/ReviewTeeth.lean:162-192`; no other consumer (`grep -rn "emitBendTT\|runB\b" Obend` excluding the defining file) |
| Interaction-net text `@main = net { CON(0, 1, 2) … }` | `emitBendINet` (`BendTT.lean:1847`) | Nothing. Zero consumers tree-wide | `grep -rn emitBendINet Obend` → only `BendTT.lean` |
| C99 text `uint64_t bend_entry(uint64_t v0)` | `emitBendNetToC` (`BendTT.lean:1896`) | Nothing. Zero consumers; never written to disk by any command | same grep |
| SystemVerilog from a Book | `obend lower NAME --rtl` → `compileBookToRtlSat` → `emitModuleSV` | **Verilator** (external), via `tests/lower/run-lower.py` and `Obend/Hardware/VerilateRunner.lean:2066-2070` | I ran it: `obend lower double --arg 21 --emit … --rtl …` prints `rtl: double 21 = 42`; `tests/lower/run-lower.py` → `112/112 checks hold` (3 min 50 s) |
| `.bendtt` text for `~/dev/bend/bend2/bendtt.lean` | **nothing produces it** | — | `grep -rn "bendtt\|\.bendtt\|λ{" lean/Obend/Leaf/BendTT.lean` → no hit; `bendtt.lean:1484` `main` reads a file path and runs `Book.parse >>= Book.check` |

So the only artifact that ever leaves the Lean process is RTL for first-order `Nat` functions of
arity ≤ 4 plus a recognised two-state linear recurrence (`Hardware/Compiler.lean:386-443`,
`:902-1127`). The emitted `double.sv` is `w_0 = (arg + arg)` (my scratchpad copy at
`/private/tmp/claude-501/-Users-ember-dev-obend/a43ef565-cc2f-412d-8808-6f075bdeea89/scratchpad/double.sv`).
That is the FPGA expert's territory; for this chair the point is that no *software* backend exists.

---

## 2. Suspicions, ranked by how much they would embarrass us

### 2.1 "Second and third Futamura projections" — self-application of what? (CONFIRMED, worst)

**What made me suspicious.** A Futamura-2 needs the specializer itself as a program in the object
language. `Futamura.lean`'s header promises `mix(⌜mix⌝, ⌜elab⌝)` and `mix(⌜mix⌝, ⌜mix⌝)`
(`lean/Obend/Leaf/Futamura.lean:31-45`). The specializer that does the work in that file is a
Lean function, `dataPinSpecialize` (`:303`, four rounds of a bottom-up constant folder
`dataPinPass` `:188-222`). For the projections to be real, there must be a Core4 term that *is*
a specializer and that gets specialized.

**What would clear it.** A Core4 term `⌜mix⌝` that, applied to a program-as-data and a static
input, *produces a residual program* under `Step`/the machine, and a theorem that specializing
`⌜mix⌝` yields a compiler whose output is run by the machine.

**What I found (READ).**
- `mixLExpr` (`:443-457`) and its lowering `quoteMixTerm` (`:460-474`) are
  `λspec. λenv. λx. case spec of addConst{bias} ↦ bias+(env+x) | mulConst{scale} ↦ scale·(env+x) | metaMix{b} ↦ b+env`.
  This is a three-arm arithmetic function. It takes no program as data and returns a number, never
  code. `futamura2SelfSpecialize progSpec := dataPinSpecialize (.app quoteMixTerm progSpec)` (`:498`)
  and `futamura3Cogen` (`:504`) constant-fold that function at a literal tag. The headline theorems
  `futamura2_self_specialize_sound` (`:529`) and `futamura3_cogen_sound` (`:563`) conclude that
  `10 + (32 + 5) = 47` and `100 + 23 = 123` evaluate correctly.
- The "book" versions are the same shape one level up. `bookMixLExpr`/`quoteBookMixTerm`
  (`:936-950`) is `λs. case s of bookStage{payload} ↦ λp. payload p`; `quoteMetaCogenTerm`
  (`:1320`) is the identical term with the tag renamed `cogenStage`. `cogenBookInCore_eq` (`:1342`)
  proves `mix(cogen, mix) = λx. quoteBookMixTerm x`, i.e. that constant-folding `apply` applied to
  `apply` gives `apply`. `futamura3_cogen_self_application_commutes` (`:1728`) is that fact plus
  the Futamura-2 one.
- "Executes all 4 passes **inside Core4**" (`:1241-1292`, docstring at `:1016-1018`) means: the
  Lean function `dataPinSpecialize` is applied to a Core4 term that encodes a book. Core4's `Step`
  never performs a `dataPinPass`; the machine cannot reduce under a λ and so cannot produce a
  residual program at all. Nothing in the file runs the generated "compiler" on the machine.
- The semantic side of every commuting diagram is the specializer again: `evalBookUnderPinsAt`,
  `evalResidualBookAt`, `evalBookAt` (`:1423-1432`) are all
  `dataPinSpecialize (.app (.app c {}) x)`. The diagram "compile then run = run" is "normalize
  then normalize = normalize" for the *same* normalizer. The theorems are correct, and they are
  about `dataPinSpecialize` being a function.
- The design documents cite `futamura1_sound`, `futamura3_cogen_deterministic`,
  `selfSpecializeFlatten`, `compilerGenerator` (`METATHEORY.md:134`, `PLAN.md:65`); none exists
  (`grep -rn` over `lean/Obend`, no hit). `SILICON-ELABORATOR.md:113-119` says the second
  projection lowers `Flatten.flatten` into Core4 "once `Obend/Lower` supports recursive
  inductives (`Term`)". It does not: `Lower/Fragment.lean:35-37` reads only non-recursive
  inductives, and nothing lowers `Term` or `dataPinPass`.

**Verdict.** No self-application exists. What exists is a sound, bounded constant folder
(`bequiv_dataPinSpecialize` `:306` is a real theorem via `Ahead`) applied to toy terms, with the
Futamura vocabulary painted on. A person who has written a cogen will see it in the first
minute, because the "specializer" has no case for `app`, `lam`, or `fix` of its *input program*:
it has cases for `addConst` and `mulConst`.

**Also note (READ).** `resolveApp` β-reduces every `(λb) a` unconditionally (`:68-70`). Under the
call-by-name reference this is `≈b`-sound, but it duplicates `a` syntactically wherever `b` uses
its variable more than once, and the demand machine then evaluates each copy separately. The
"specializer" can make a program asymptotically slower on the fallback machine; nothing bounds
this. `termRedexWeight` (`Specialize.lean:718-736`) is a `max` of per-constructor ranks, so it
cannot see duplication; `checkSpecCostMonotone` (`:775`) is therefore not a cost gate.

### 2.2 `Leaf/BendTT.lean` is not BendTT, and its backends are decorative (CONFIRMED)

**What made me suspicious.** The leaf target is named as `~/dev/bend/bend2/bendtt.lean`
(`GROUNDING.md:37`, `AMBITION.md` "Bend for the leaf"). That file's `Term` has
`Var/Ref/Ann/Let/Typ/Min/All/Lam/App/Sig/Tup/Prj/Enu/Lab/Mat/Efq/Eql/Rfl/Rwt` with quantities
`Q0|Q1|Q2` on every binder, application and pair (`bendtt.lean:70-98`), a bidirectional checker
(`:1085-1270`), a live/termination check (`:1397-1480`), and a parser for `.bendtt` text.

**What I found (READ).**
- `Obend.Leaf.BendTT.BTerm` (`lean/Obend/Leaf/BendTT.lean:45`) is
  `var/lam/app/fix/nat/bool/label/binOp/record/get/ifZero/inject/case/ifBool/split`: Core4 minus
  the object and effect constructors, with no quantities. `embedB : BTerm → Term` (`:89`) is the
  inclusion; `compileToBendTT_embedB` (`:190`) says the compiler is its partial inverse; `stepB?`
  (`:397`) is Core4's own `Step` restricted (`stepB?_sound : Step (embedB bt) (embedB bt')`,
  `:548`). `book_to_bendtt_sound` (`:773`) is therefore "a sub-syntax of Core4, run by Core4's
  rules, agrees with Core4". True and empty with respect to BendTT. No function in the tree
  produces `bendtt.lean`'s `Term`, `Def` or `Book`, or `.bendtt` text.
- The interaction-net "compiler" `compileBendToINet` (`:1727-1760`) emits a flat list of agents
  with the literal ports `0 1 2` on every node (`.con 0 1 2 :: …`). There is no wiring, no port
  numbering, no active pair; `emitBendINet` prints them one per line (`:1847`). `affine_bendTerm_inet_dup_free`
  (`:1773`) says a term with no multiply-used binder yields no `dup` label, which is the
  definition of the labelling function.
- The C emitter `emitBendExprToC` (`:1853-1894`): `.lam b` emits `b` with a comment (no function);
  `.app f a` emits `bend_con_app(f, a)`, an undefined symbol; `.record fs` emits the **field
  count** `{fs.length}ULL`; `.get t _` **drops the field name**; `.inject _ p` and `.case sc _`
  drop the tag and the arms. `emitBendNetToC_wf` (`:1916`) proves the string is non-empty.
  `WellFormedBendC` (`:1906`) is non-emptiness. No test compiles the output with a C compiler.
- The hardware interaction-net arena in `Hardware/ReductionMachine.lean:507-560, 2008-2075` has
  real `PortRef`s and an `ActivePair` step, but its `con × num` rule computes
  `slope * val + imm` (an affine *function* node, not an interaction combinator), and nothing
  converts `BTerm`/`INetAgent` into `INetNode` (no reference to either in `Hardware/`,
  `grep -n "INetAgent\|compileBendToINet\|BTerm" Obend/Hardware/*.lean` → only an import in
  `UserspacePhysical.lean`).
- `zero_wires_erased`, cited by `DESIGN.md:135` and `SILICON-ELABORATOR.md:62`, does not exist.
  `REPORT-LEAF-20261101.md`, cited by `Emit.lean:20` and `BendTT.lean:5`, does not exist
  (`ls lean/docs review | grep LEAF` is empty).

**Verdict.** There is no leaf target. The honest sentence is: "Books are closed Core4 terms of a
first-order shape; a translation to BendTT's affine calculus (quantities, Σ-encoded data,
case-tree descent for the live check) has not been started." That translation is the actual
leaf-compiler work, and it is nontrivial: Core4 `fix` on records is not a BendTT `Def` whose
calls descend.

### 2.3 Does the pipeline handle anything beyond `ReviewMember`? (CONFIRMED: barely)

**Method.** I wrote `/private/tmp/claude-501/-Users-ember-dev-obend/a43ef565-cc2f-412d-8808-6f075bdeea89/scratchpad/emit_sweep.py`:
for every `.obend` under `lean/tests/obend-source`, `apps`, `stdlib` (159 files), build the same
package spec `tests/run-leaf.py` builds, and run `obend emit --package … --object DEF --out …` for
every top-level `def` (713). Output in `…/scratchpad/emit_sweep.out`.

**Result (READ, from my run).** `emitted(rc=0)=9` of 713. The nine: `EvenOdd.evenTen`,
`LazySpecification.resultOfThree`, `ReviewMember.twiceOfThree`, `TwiceReview.twiceOfThree`,
`ltuo/LawImpossible.built`, `ltuo/LawSpecification.built`, `ltuo/RequiresPlaceholderSeed.placeholderOfThree`,
`ltuo/ReviewSelfSuper.{twiceOfThree,reviewOfThree}`. 622 refusals are
`no fix (compose …) {seed} is reached from X` (`Main.lean:631-633`: the entry must evaluate,
within 100000 fuel, to a composition whose layers are all named), 75 are elaboration or parse
diagnostics (26 `unexpected trailing expression token` from the swarm's uncommitted apps, 28
cross-module law refusals, the rest typing refusals the tests intend). `stdlib/core/Cell.obend`'s
`baseCell = fix(BaseCellSpec, seedCell())` (`stdlib/core/Cell.obend:33-34`) is refused: a single
spec is not a `compose`. Every one of the 29 `apps/**/*.obend` is refused.

**The specializer is unreachable (READ).** `dataPinSpecialize`, `specializeBook`,
`futamura2BookCompiler`, `inCoreBookCompiler` have no caller outside `Futamura.lean` except the
theorem `stdlib_futamura2_in_core` in `Obend/Stdlib.lean:128-140`
(`grep -rn … Obend Main.lean`). `obend emit` calls `Obend.Leaf.emit` only (`Main.lean:666`);
`obend lower --emit` wraps the lowered term in a one-layer composition (`Lower/Cli.lean`,
`Lower/Proofs/Book.lean:24`). Nothing in the binary folds a constant, inlines a method, or
eliminates a branch.

**What the lowering actually hands the machine (READ, from my run).** `obend lower double --arg 21`
prints the Core4 term: `λn. ((λλλλ. get (bound 0) "hAdd") {} {} {} ((λλ. {hAdd = λλ. ((λλ. get (bound 0) "add") {} …)}) {} {add = λλ. bound 1 + bound 0})) n n`.
That is `HAdd.hAdd Nat Nat Nat instHAdd n n` with the three types erased to `{}`, the instance
record built at every call, and two field projections before the primitive. The RTL path
produces `arg + arg` only because `compileTermSat` pattern-matches that exact spine. On the
machine: `sumTo 20000` finishes and `sumTo 30000` is `suspended (out of fuel)` at the 10-million
tick limit (`obend lower sumTo --arg N`), so `Nat.rec 0 (fun k acc => acc + k + 1)` costs
**more than 333 machine transitions per iteration**. `ackTwo 200` (`ack 2 200 = 403`) also
exhausts the budget. **INFERRED:** the 10 M transitions ran in roughly 0.1–0.3 s of wall time
beyond the ~2.1 s module import (total 2.3–2.5 s vs 2.07 s for `sumTo 1000`), so the interpreter
itself does on the order of 10⁷–10⁸ transitions/s; the problem is not the stepper, it is that
nothing between `Fragment.read` and `runBounded` removes a dictionary. Graal's whole trick is
that it does.

**Verdict.** One specialization strategy exists (flatten `compose`), reachable from nine toy
programs; the general specializer exists only as a theorem subject. The preview cap also
matters for the "runtime" claim: `obend run` refuses `--ticks` above 1 000 000
(`preview limits must be canonical positive decimal strings ≤1000000`, from my run) and a
300 000-iteration accumulator loop is "preview capacity refused: ticks" at 20 000 iterations.

### 2.4 The deoptimization story: cost and granularity (CONFIRMED as overstated; mechanism honest)

**What made me suspicious.** `README.md:21` says "1-cycle deoptimization on moved pins";
`DESIGN.md:138` says the guard "falls back in O(1)" on "pinned slot hashes" and "Epoch advances";
`SILICON-ELABORATOR.md:111,156` says `Supports = [(envSlotId, hash(E))]` and an `envEpoch`
comparator.

**What I found (READ).**
- A pin is the **whole code** of a layer or of the object's composition (`Specialize.lean:153-156`
  `Candidate.supports`: `⟨.object name, C.code⟩ :: C.layers.map (⟨.layer L.name, L.code⟩)`), and
  it holds when the view's term is structurally equal to it: `holdsOfPin … := Obend.Law.termEq t f.code`
  (`:58-60`), `termEq a b := treeEq (encode a) (encode b)` (`lean/Obend/Law/Claim.lean:43`). There
  is no hash and no epoch in the Lean. Checking usability is linear in the total size of every
  layer of the object, per read.
- The granularity is the whole object: any edit to any layer, or to the seed, blocks the whole
  book (`moved_pin_blocks` `:213`). The finer `Candidate.slotBook` with `coneSupports` (`:141-156`)
  exists but is not in `specOrder` (`:168` is `[.book name C, .machine]`) and is unused by the CLI;
  its only consumer is a theorem in `Spec/CrossPackage.lean:67`.
- The decision is made **once, before the run**, by `obend specialize` (`Main.lean:688-720`),
  rebuilding the view from source. There is no guard in the machine, no invalidation during a
  run, no on-stack replacement, no inline cache, no profile, no tiering. A compiled book is
  either used for the whole call or not at all.
- Nothing measures any of it: `grep -rn -i "bench\|ticks per\|throughput" Obend/Leaf Obend/Core/Machine*.lean lean/docs`
  returns nothing relevant. `run-leaf.py` is 14 string checks (`14/14 checks hold`, 0.6 s).

**Verdict.** The *idea* is right and the proofs are the right proofs (`specialize_choice` is
`incumbent_choice` instantiated; `moved_pin_blocks` is `read_blocked_exact` instantiated). The
runtime story around it is prose. A Truffle person would ask where the assumption is *checked
at the use site*, how a pin becomes a cheap guard (content address, not term equality), and what
happens to a running activation when a pin moves. None of these has an answer in code.

### 2.5 Do the cost results say anything about an implementation? (PARTLY CLEARED)

**READ.** `Equiv/Clairvoyant.lean` is Hackett–Hutton clairvoyant call-by-value on Core4 with a
two-stage rule for `fix` (header `:1-30`); `Equiv/Demand.lean` is the ICFP'24 demand semantics
for a fragment of objects whose fields are literals or `self.m` (`:1-22`, `FE` at `:34`);
`demand_is_least` (`:1096`) is real. `Core/Proofs/TickCost.lean` is the piece that touches the
machine: `ticks_within_fragment : TicksWithinDemandOn InFragment 4 0` (`:457`): on that fragment,
machine transitions ≤ 4 × least clairvoyant cost; `measured_within` (`:494`) instantiates it on
three programs. The header says plainly what is not proved: `CostIndexedCompleteness c` for
general programs (`:244`). `Equiv/Cost.lean` proves `mix_assoc_cost` within a factor 8 (`:658`).

**INFERRED.** This is a correct, narrow, honestly-labelled result about the *reference* machine's
transition count on first-order records. It says nothing about allocation, residency, GC (there
is none during a run: `Core/Collect.lean:1-12` collects only at a yield), environment lookup
(`Environment := List Address`, `Machine.lean:20`, so variable access is O(index)), or any
implementation other than `stepRaw`. `METATHEORY.md:37`'s "every terminating evaluation has a
unique least prefix demand" generalizes the fragment to "every". For a JIT designer the useful
cost theory would be about the *specialized* program versus the unspecialized one; the only such
statement is `termRedexWeight` (§2.1), which is syntactic.

### 2.6 The reference machine itself (CLEARED, with notes)

**READ.** Adequacy is proved, not promised: `Term.lean:507-523` states the `Representation`
contract (initialization, simulation with administrative rank, value adequacy, exact suspension,
completeness), `Core/Proofs/Completeness.lean:1165-1215` inhabits it for `Scoped 0` with the
machine's own `step`, and `lazyFixedSeed_supported_by_representation` shows non-vacuity.
`MachineFast.lean` fixes the four heap-sharing sites and the per-tick `List.length`, and installs
the fast path by `@[csimp]` with `#print axioms` guards. `perform` under an update frame is
refused (`Machine.lean:309-314`), which is the correct shared-thunk rule. This is the part a
runtime person would steal.

**Notes (READ).** Unbounded `Nat` everywhere with 64-bit primitives applied through `word64`
(`Term.lean:15, 247-254`); labels are the only strings and the only string primitive is equality
(`:36-40`); no arrays, floats, references, exceptions or continuations; `hole` has no `Step`
rule (`:321-375`) and the machine refuses it (`Machine.lean:136 .unresolvedHole`);
`Observation` is `natural | boolean | label` (`:478`), so every `≈b` theorem speaks only about
ground scalar results. `let` in the surface lowers to a β-redex (`Lets.obend` header; the
machine allocates one cell per argument, so sharing is right).

### 2.7 What `Lower` really covers (READ)

`Fragment.read` (`Lower/Fragment.lean:1-60`) is a genuine reader of kernel `Expr` with recursors,
structures, `f.eq_def` recursion and erasure; the test runner shows `halvings` (well-founded),
`greeting` (`String`), `countDown`, `propElim` refused as intended (`run-lower.py` teeth). `LCNF.lean`
is **not** a bridge to `Lean.Compiler.LCNF`: it imports no `Lean.Compiler` module (`:28-30`) and
defines its own `LcnfCode` inductive (`:112`); the theorems are over sample terms. `obend lower`
works only on declarations of a pre-built module (`Lower/Cli.lean:5-8, 87-91`, default `Programs`).

---

## 3. Gemini's two halves, checked

- **"The hard mathematical tax is paid."** Paid: `flatten_sound`, `book_sound`, `emit_of_digest`,
  `specialize_choice`/`moved_pin_blocks`, `coreRepresentation`, `lower_sound`/`lower_checks`/
  `lean_to_book`, `ticks_within_fragment`. Not paid: anything about staging (no object-level
  specializer, no residualization theorem of the form "the machine, run on the compiler's
  output, yields a program that the machine runs to the same result"), anything about the cost
  of a specialized program on the machine, and anything about an affine leaf.
- **"The compiler that collects on it is unwritten."** Confirmed and quantified: 9/713 entry
  points emit; the specializer has no caller; the lowering ships dictionaries; the leaf target
  has no translation; the two non-RTL backends emit text nothing can run.

---

## 4. What a native backend would actually need from this tree (PROPOSED)

1. **A first-order IR with explicit sharing.** Core4 has no `let`; the Book has one. A backend
   needs ANF with known-arity calls, closure conversion for the `lam`s that survive flattening,
   and a decision about `fix` on records (the dispatcher `Book.link` is a knot the machine ties
   with one cell; a strict leaf must tie it with a static table). `Leaf.Book` is already the right
   shape (`LeafDef.reads` is the call graph); what is missing is a type-directed arity/strictness
   pass and a term language below `Term`.
2. **A specializer that is an object-language program.** Either lower `dataPinPass` through
   `Fragment.read` (needs recursive inductives: `Term` itself) or write the specializer in
   `.obend` over the `Syntax` sum that `Core/Code.lean:204 quote` already produces. Only then do
   the projections mean anything. The theorem to aim for is
   `Evaluates (app ⌜mix⌝ ⌜p⌝ s) ⌜p_s⌝ ∧ p_s ≈b app p s`, with `Evaluates` the machine's relation,
   not `dataPinSpecialize`.
3. **Guards as content addresses.** `Core/Code.lean:434-447` already gives `address t` with
   `digest_of_quote`; a pin should carry `address L.code`, and `holdsAt` should compare 32 bytes.
   That is also what the FPGA story needs for its "epoch comparator".
4. **Erasure of dictionaries before the machine.** Today the one place that pays for `instHAdd`
   is the RTL pattern matcher. A `dataPinSpecialize` on the lowered term would fold the `{}`
   applications and the record projections (it has the rules); it is simply never called.
5. **Strings, arrays, and a numeric tower** or a documented decision that leaves never see them.
6. **An actual translation to `bendtt.lean`'s `Book`** if Bend remains the leaf: quantities on
   every binder (the `Ty.Quantity` annotations exist in `Core/Ty.lean`), Σ-encoded records and
   variants, and a case-tree form that `Term.live`/`Arg.descend` accepts. Or drop the name.

---

## 5. Three changes first

1. **Rename or delete the staging layer, then build the real one.** Rename `futamura2*`,
   `futamura3*`, `quoteMixTerm`, `quoteBookMixTerm`, `quoteMetaCogenTerm`, `cogenBookInCore` to
   what they are (`constFold_*`), move the `decide +kernel` instances to `Teeth/Leaf/Examples.lean`,
   strike the Futamura rows from `METATHEORY.md:134`, `PLAN.md:62-65`, `SILICON-ELABORATOR.md §4`,
   `DESIGN.md §4.2`, `THESIS.md:107-108`, `README.md:18-21`. Then make `obend emit` run
   `specializeBook` on the book it emits (the function exists; `specializeBook_eq_mapBookCode_bindBookPins`
   and `evalBook_specializeBook_eq_evalBook` are already there) and add `obend specialize --run`
   that executes the specialized book on the machine and prints the tick count beside the
   unspecialized one. Cost: a day of renaming and a few days to wire and measure; the only new
   theorem needed is "the machine's result on the specialized book equals the machine's result on
   the book", which follows from `bequiv_dataPinSpecialize` plus `coreRepresentation`.
2. **Delete `compileBendToINet`, `emitBendINet`, `emitBendExprToC`, `emitBendNetToC` and
   `WellFormedBendC`** (`BendTT.lean:1707-1925`), rename `Leaf/BendTT.lean` to `Leaf/FirstOrder.lean`
   with `BTerm` as `FOTerm`, and open a `Leaf/Bend.lean` whose first commit is
   `toBendTT : Book → Option Bend2.Book` producing text that `~/dev/bend/bend2/bendtt.lean`'s
   `main` accepts with `ALL PROOFS CHECK` for `ReviewMember`. Cost: deletion is an hour; the
   translation is real work (one to two weeks) because the affine live check will reject the
   dispatcher knot as written and force the design decision in §4.1.
3. **Make `obend emit` the default compile step for every `.obend`, not only `fix(compose …)`.**
   Accept `fix(Spec, seed)` (one layer), a bare record, and a closed first-order `def` (as
   `obend lower --emit` already does through `leanComposition`), and have the elaborator
   gate call `emit` on every closed definition, recording refusals by name. Then run my sweep
   as a test: the number is 9/713 today; it should be a census line. Cost: two to three days;
   `findObject` (`Logic/Program.lean:84`) and `leanComposition` are the two seams.

---

## 6. The one question for Ember

Is Bend still the leaf? Everything in `Leaf/` is a closed first-order *lazy* Core4 fragment
run by the same demand machine; nothing translates to Bend2's affine, strict, quantity-annotated
calculus, and the one place a leaf executes outside Lean is Verilator. If Bend is the leaf, the
next hard theorem is strictness and affinity of flattened books (the `Quantity` annotations
exist; the proof that a book's `self` reads are affine does not), and the Futamura work should
wait behind it. If the leaf is RTL and the machine, say so and retire the name, the C emitter,
and the interaction-net vocabulary in the same commit.
