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

---

## What landed (2026-11-04)

Ember's answer to §6: Bend is not the leaf; the phrase is retired; Bend compatibility is no longer a
goal; the BendTT and C emitters and the interaction-net vocabulary go. The plan in §5 was executed in
place. Builds ran on `bb2:~/lane-compiler` (a copy of the `07c04c1` export plus this lane's files)
with `swarm-build lake build <modules>`, never the `Obend` umbrella and never `Obend.Apps.ZkNtt`;
nothing was built on the Mac or hbox. The lane died once (quota, ~07:00) while waiting on a build and
resumed from its distilled transcript at 18:30; the second half of this section is that resumption.

### Commits (all unsigned)

- `2a91854` leaf: Static replaces Futamura; the Bend claims and the self-application are gone
  (`Leaf/{Static,Futamura,Specialize,Emit}`, `Teeth/Leaf/{StaticTeeth,ReviewTeeth}`,
  `Lower/Proofs/SiliconKernel`, `Obend.lean`, `Census.lean` import lines).
- `62f3d95` equiv, tick cost: keep the honest renames from the suspended S-1 lane
  (`Equiv/{Behaviour,Quote,Cost}`, `Core/Proofs/TickCost`).
- `c5cb3d5` leaf: the Futamura alias names the four surviving entry points (`Leaf/Futamura`,
  `Lower/Proofs/SiliconKernel` import).
- `c038b43` tactic: #silicon_check refuses what it cannot check (`Tactic/SiliconElab`, one
  `SiliconKernel` docstring).
- `1d32717` docs, written through a private index; `47e6adc` (another lane's plain commit) swept the
  shared index's stale entries for those five paths and put the old text back. `a1c67f7` carries the
  same hunks on the current text and the shared index was refreshed for those paths afterwards.
  PLAN's hunks had already reached HEAD inside `47e6adc` (it committed the working-tree PLAN).
- the review commit that adds this section and `review/compiler-lane-crosslane-20261104.patch`.

### What changed, by file

- **Deleted**: `lean/Obend/Leaf/BendTT.lean` (1512 lines; staged by this lane, swept into `fb35622`).
  With it: `compileToBendTT`, `BTerm`, `runB`, `book_to_bendtt_sound`, `compileBendToINet`,
  `emitBendINet`, `emitBendExprToC`, `emitBendNetToC`, `isAffineBendTerm`, `countVarUses`, and the
  three BendTT teeth in `Teeth/Leaf/ReviewTeeth.lean`.
- **New `lean/Obend/Leaf/Static.lean`** (replaces `Futamura.lean`, cut from HEAD's): §1-2 the folder as
  before; §3 `envLookup_folds` (the universal part of the old `data_pin_flatten_sound`, without the
  `.nat 50` fixture); §4 `staticApply`/`staticApply_slot_sound` (the old `futamura1Specialize`/
  `futamura1_env_specialize_sound`, renamed; the docstring says `f` and `a` are any terms); §5-6 the
  book encoding and its commutation with the folder; §7 `specializeBook` with
  `specializeBook_eq_mapBookCode_bindBookPins`; §8 the lookup functions, whose docstrings now say
  they are syntactic normal forms and not runs; §9 `optTermEq`; **§10 new**: `foldBook B :=
  mapBookCode dataPinSpecialize B`, `link_ahead_mapBookCode` (a reduction-in-context applied to every
  code of a book is a reduction-in-context of `Book.link`, by `Ahead` congruence over the dispatcher
  record), `link_bequiv_foldBook : B.link ≈b (foldBook B).link`, `foldBook_member_bequiv`,
  `foldBook_member_sound : .get (foldBook (emit C)).link m ≈b .get C.object m` for closed `C`, and
  `slots_foldBook`. This is the one specialization step proved at the level the machine sees, and
  the thing `obend emit --fold` should call (request to the frame lane below).
- **Deleted from the old Futamura module, not renamed**: `mixLExpr`, `quoteMixTerm`, `elabRuleSpec`,
  `quoteMixSpec`, `futamura2SelfSpecialize`, `futamura3Cogen`, `futamura2_elab10_folds`,
  `futamura2_self_specialize_sound`, `futamura3_cogen100_folds`, `futamura3_cogen_sound`,
  `specializeBookInCore` and its lemmas, `bookMixLExpr`, `quoteBookMixTerm`, `bookStageSpec`,
  `dataPinSpecialize_quoteBookMixTerm`, `stageMemberGetAt`, `encodeItemPinEntry`,
  `encodeItemsPinSpine`, `encodePinsRecordForBook`, `encodeStagedBookItemAt`, `encodeStagedBookItemsAt`,
  `encodeStagedBookTerm` and its lemmas, `futamura2BookCompiler`, `futamura2BookCompiler_eq`,
  `futamura2BookCompiler_specializes_in_core`, `runStagedCompiler`, `runStagedCompiler_futamura2`,
  `decodeBookTerm_futamura2BookCompiler`, `metaCogenLExpr`, `quoteMetaCogenTerm`, `cogenStageSpec`,
  `cogenBookInCore`, `cogenBookInCore_eq`, `cogenBookInCore_generates_compiler`, `emptyBaseView`,
  `holdsAll`, `holdsAll_nil`, `pins_eq_nil_of_holdsAll`, `futamura1_book_specializer_sound`,
  `futamura2_compiler_generator_commutes`, `futamura3_cogen_self_application_commutes`, all of §11
  (`encodePinsOnly` … `inCoreBookCompiler_specializes_from_pinsOnly` and its teeth), and Gemini's §12
  (`termRedexWeight` monotonicity). The §10 fixtures (`sampleSpecializableBook`, `sampleBookPins`,
  `specializeBook_sample_folds`) and the §3 sample (`envLookup_sample_folds`) moved to
  **`lean/Obend/Teeth/Leaf/StaticTeeth.lean`** (tier 2) with their two `#tooth`s.
- **`lean/Obend/Leaf/Futamura.lean`** is an alias of `Static`: it publicly imports it and its namespace
  holds four `abbrev`s (`dataPinSpecialize`, `specializeBook`, `foldBook`, `staticApply`) so that
  `open Obend.Leaf.Futamura` still parses in `Lower/MetaUnify.lean`, `Lower/SiliconElabFabric.lean`
  and `tests/metasystem/CoupledPhysicalTest.lean`, which reach it through
  `Lower/Proofs/SiliconKernel.lean`'s public import (an empty namespace and an `export` are both
  invisible to importers under the module system; measured, two builds). Delete it when the last
  `open` has moved.
- **`lean/Obend/Leaf/Specialize.lean`**: Gemini's +349 reverted (red; §2.1 note); the header states the
  deopt story as it is: a pin is the whole layer code, `holdsOfPin` is `termEq` on the encodings, the
  granularity is the whole object, `slotBook` is proved and unselected, the choice is made once before
  a run, no guard in the machine, no OSR, no hash.
- **`lean/Obend/Leaf/Emit.lean`**: the header no longer calls the book a Bend program.
- **`lean/Obend/Lower/Proofs/SiliconKernel.lean`**: uses `staticApply*`; its local lemmas are
  `residual*`; `silicon_elab_futamura_dpr_specialize_sound` is
  `silicon_elab_residual_dpr_specialize_sound`; its closed fixtures are `example`s.
- **`lean/Obend/Tactic/SiliconElab.lean`** (added to this lane by the coordinator; S-5's uncommitted base
  kept and built for the first time): `#silicon_check`'s verdict is `fullZ4Verified && roundTripOk`
  with `inSupportedFragment` inside `fullZ4Verified`; the command throws with the reason; the fixed
  `scaleAdd 10` Zone-3 probe is gone from the command and the telemetry; `selfHostTypePreservationInfo`
  is `selfHostIdentityProofInfo` and its docstring says it is `λ P h. h`. Three things in S-5's base
  had never elaborated: the environment-cone fold lacked binder types (`:635`), `hwCamCheckDecl` was
  called with the fuel in the environment-codes position (`:706`), and `selfHostKernelCheckDeclInfo`
  named `Nat.succ`, which `stdKernelEnv` does not declare, so the kernel check it exists to pass refused
  it (conjuncts 3 and 9 of `silicon_self_hosting_milestone_sound` were false). It is now
  `λ x. idNat (idNat x)`; all sixteen decidable conjuncts were evaluated on bb2 before the proof was
  rebuilt (`~/lane-compiler-logs/scratch-eval.txt`).
- **Kept from Gemini** (adjudicated in `review/GEMINI-HANDOFF-20261103.md`, built):
  `Equiv/{Behaviour,Quote,Cost}.lean`, `Core/Proofs/TickCost.lean`. **Reverted**:
  `Core/{Term,Nominal,Code,Check,Bidirectional,MachineFast}.lean`, `Lower/LCNF.lean`,
  `Leaf/Specialize.lean`.
- **`lean/Obend.lean`**: the `Obend.Leaf.BendTT` import is gone (HEAD had been red at the umbrella
  since `fb35622` deleted the file). **`lean/Obend/Census.lean`**: the same import gone, `Obend.Leaf.Static`
  and `Obend.Teeth.Leaf.StaticTeeth` added; committed as a HEAD-based copy carrying only those three
  lines, so the proof-engineering lane's classification rewrite stays theirs in the working tree.
- **Docs** (`a1c67f7`; PLAN's via `47e6adc`): `DESIGN.md` §4.2 and the Lower pipeline line; `METATHEORY.md` §1
  bullet 2, §2.3 rows, the Futamura row (gone) and the DiscrTree row; `PLAN.md` WS 5/15, WS 23 and the
  DiscrTree bullet (no "2nd Futamura specialization"); `NEXT-MATHEMATICA.md` items 3 and 9; the last
  `Obend/Leaf/BendTT.lean` path citation in `SILICON-ELABORATOR.md` (its §5.1 and Stage 3 rewrite had
  already been swept into `586590b`). The docs census (`Obend/Tactic/DocsCensus.lean`) was run on the
  committed texts: 7 docs, 614 path references, 0 stale. `DESIGN.md:224`, `PHYSICAL.md:309` and
  `THESIS.md:4,13,20` still say `BendTT` in the hardware and thesis rows, which are not this lane's.

### Verified

All on `bb2:~/lane-compiler` (logs in `bb2:~/lane-compiler-logs/build{6..10}.log`, `test-*.log`,
`scratch-eval.txt`), with `swarm-build lake build <modules>`; the umbrella, `Obend.Census` and
`Obend.Apps.ZkNtt` were never targets.

- Built green with the committed texts: `Obend.Leaf.{Static,Futamura,Specialize,Emit}`,
  `Obend.Teeth.Leaf.{StaticTeeth,ReviewTeeth,MachineSeven}`, `Obend.Lower.Proofs.SiliconKernel`,
  `Obend.Lower.{MetaUnify,SiliconElabFabric,ExprCAM,DiscrTreeLUT}`, `Obend.Tactic.{SiliconElab,DocsCensus}`,
  `Obend.Equiv.*`, `Obend.Core.Proofs.TickCost`, and the `obend` executable; with the cross-lane patch
  applied in the lane tree: `Obend.Hardware.UserspacePhysical`, `Obend.Stdlib`,
  `Obend.Apps.{SiliconKernelVerilator,FocHil,QuantumPhotonicMatter,SdrFt8}` and the old `FidgetCam`
  (build6; the CAD lane's rewrite and the regenerated hunks for it are unbuilt).
- `lake env lean` on the four patched tests: `silicon_elab/SiliconElabTest`, `silicon_elab/SiliconSelfHostTest`,
  `metasystem/FutamuraAndObjectsTest`, `metasystem/CoupledPhysicalTest`: 0 errors each.
- `silicon_self_hosting_milestone_sound`: its sixteen decidable conjuncts evaluated by `#eval` on bb2
  before the proof was rebuilt (`scratch-eval.txt`, 0 mismatches).
- `tests/run-leaf.py` 14/14; `tests/run-obend-source.py` probes 30/30, tutorial 71/71, preview cohort 161
  items with 0 failures (the one stale pin is minidregg's, pre-existing); both against the lane tree's
  rebuilt `obend`.
- `#check_docs_census` on the committed documents: 7 docs, 617 path references, 30 namespace references,
  0 stale.
- Not verified: `Apps.ZkNtt` (10196 s in build6, failed only on the names the patch removes) and
  `Apps.ObendRisc` (red on eight decide/omega fixtures unrelated to Leaf) with the patch; `Apps.SovereignDrex`
  (red on another lane's `Law/Contract.lean`, not in the lane tree); `Obend.Census` (the lane tree's
  lakefile predates the Apps-out-of-tier-1 change, so its census complains about imports, not content).

### Cross-lane patch (needs an owner's yes to land)

`review/compiler-lane-crosslane-20261104.patch` (`git apply -p1` from the repo root) removes every
remaining use of a deleted Leaf name outside this lane's files. It applies to the working tree as of
this commit (regenerated once this evening after the CAD lane rewrote `Apps/FidgetCam.lean` and
someone dropped the `BendTT` import from `Hardware/UserspacePhysical.lean`), and is **not** applied to
the shared tree. Contents, all mechanical:

- `lean/Obend/Stdlib.lean`: drop `stdlib_futamura2_in_core`, `stdlib_inCoreBookCompiler_pinsOnly`,
  `stdlib_quantum_photonic_inCore_futamura2`; import/open `Static`; header prose.
- `lean/Obend/Hardware/UserspacePhysical.lean`: the four `*_support_and_futamura2` theorems lose their
  4th conjunct (the staged-compiler identity) and are `*_support_and_specialize`; import/open `Static`.
- `lean/Obend/Apps/{SovereignDrex,FocHil,ZkNtt,FidgetCam,ObendRisc,SiliconKernelVerilator,QuantumPhotonicMatter,SdrFt8}.lean`:
  drop the `*_inCore_futamura2` theorem and its section header; import/open `Static`; header prose.
  `SiliconKernelVerilator` also renames `selfHostTypePreservationInfo` → `selfHostIdentityProofInfo`.
- `lean/Obend/Lower/DiscrTreeLUT.lean`: drop `futamura2DiscrTreeTerm` and its conjunct in
  `discrTree_lut_compile_sound`; header prose.
- `lean/Obend/Lower/{MetaUnify,SiliconElabFabric}.lean`, `lean/tests/metasystem/CoupledPhysicalTest.lean`:
  drop `open Obend.Leaf.Futamura` (nothing from it is used; with the alias these build either way).
- `lean/tests/silicon_elab/SiliconElabTest.lean`: drop the three Futamura conjuncts and the
  `data_pin_flatten_sound` tooth; rename the SiliconKernel references; `#print axioms` of the two real
  theorems instead.
- `lean/tests/silicon_elab/SiliconSelfHostTest.lean`: the six live `#silicon_check` invocations are
  removed (their targets are outside the Zone-4 fragment and the command now refuses them); the
  fixture is `selfHostIdentityProofInfo`.
- `lean/tests/metasystem/FutamuraAndObjectsTest.lean`: drop `test_true_futamura_1_2_3_commuting_diagrams`
  and the BendTT section; import the fixtures from `Teeth/Leaf/StaticTeeth`.

Until it lands, the eight Apps, `Stdlib`, `UserspacePhysical`, `DiscrTreeLUT` and the four tests do
not build against HEAD. Tier 1 (`Obend` library minus Apps, per the gate successor's lakefile) does.

### Requests routed to other lanes

**Frame lane (`lean/Obend/Main.lean`)**, two changes:
1. `obend emit … [--fold]`: after `let B := Obend.Leaf.emit C`, when `--fold` is given use
   `Obend.Leaf.Static.foldBook (Obend.Leaf.emit C)` for the printed defs, the JSON and the `--call`;
   print `folded: true` and the per-definition code sizes before and after (`(repr code).length` is
   enough for a first number). The theorem behind it is `Obend.Leaf.Static.foldBook_member_sound`.
   `tests/run-leaf.py` then gets one more check: `emit --fold … --call twice 3` prints `book: twice(3) = 7`.
2. The refusal text of `leafObject` ("no fix (compose …) {seed} is reached from X") should state the
   fragment: *"`obend emit` compiles the first `fix(compose(L₁, …, Lₙ), seed)` with named layers reached
   from ENTRY within 100000 steps, and only when that composition is closed (`Composition.closedB`).
   A `fix(Spec, seed)` with one layer, a bare record, and a plain `def` are not compiled by this
   command; `obend lower NAME --emit` compiles a closed first-order Lean definition."* My sweep (§2.3):
   9 of 713 definitions across 159 `.obend` files reach it; the number should become a census line.

**FPGA lane (`lean/Obend/Hardware/ReductionMachine.lean`)**: the interaction-net vocabulary to remove
(working-tree line numbers at 2026-11-04 05:00): section 5 "True Interaction-Net / Graph-Reduction Tile
Arena" (`INetNodeKind`, `PortRef`, `INetNode`, `ActivePair`, `INetRewriteOutcome`, `commuteSpawnedNodes`,
`mkEraNode`/`mkConNode`/`mkDupNode`, `externalBoundaryPorts`, `commutedBoundaryPorts`,
`findArenaNodeById`, `resolveWireSplice`, `resolveTwoWireSplices`, `InertNodeKind`, `InertPort`,
`InertNodeSlot`, `InteractionNetPeState`, `initInteractionNetPe`, `stepInteractionNetPe`,
`runInteractionNetCycles`, `inet_annihilation_exact`, `inet_commutation_port_count_preserved`,
`inet_dynamic_splice_cascading_reduction`, `golden_multicycle_inet_pe_reduction`, :507-1250) and
section 9 "Hardware BRAM `BendTT` Active-Pair Interaction-Net PE" (`inetNodeToInertKind` …
`stepActivePair`, `interaction_net_annihilation_zero_alloc_and_involutive` and its tooth,
`hasDupInPair_false_of_hasDupNode_false`, `affine_bendtt_net_zero_commutations` and its tooth,
`stepActivePairBadAlloc`, `stepActivePairSpuriousComm`, :1816-2277). `compileBookToNocFabric` and the
NoC (section 6) do not depend on them.

**Proof-engineering lane (`lean/Obend/Lower/Inductive.lean`)**: its dirty `export` list names the LCNF
symbols this lane reverted (`lcnfCtorTagId`, `packLcnfCtor`, `sampleLcnfAstMatchSort`,
`sampleLcnfAstMatchSort_runs_42`, `isClosedDecisionCode`, `evalLcnfCode_simulates_core4`,
`evalLcnfCode_app_cases_state_sound`); drop them or restore Gemini's LCNF and fix its two red proofs.
Also: `lean/Obend/Lower/LeanKernel.lean` is dirty (+218/−83) and unowned since S-1; the SiliconElab
fixtures above were evaluated against HEAD's `stdKernelEnv`.

### A naming proposal, not a rename

`Obend/Leaf/` holds `Flatten`, `Residual`, `UpTo`, `Emit`, `Static`, `Specialize`: the flattening
compiler, its bisimulation-up-to proof, the book, the folder, and the slot. None of it is a leaf of
anything now that Bend is gone. `Obend/Book/` names what the directory is about (`Book.link`,
`Book.slots`, `foldBook`, `emit : Composition → Book`); `Obend/Flatten/` names the theorem it exists
for. Either is better than `Leaf`; `Book` is the one the CLI and the hardware compiler already speak.
Ember's call; nothing was renamed.

### Still open after this

- `(specializeBook B pins).link ≈b B.link` when the dispatcher serves `pins`: the per-definition
  theorem exists; the link-level one needs the `Joins` base-pair technique from `UpTo.lean`.
- `foldBook` is reachable only from Lean until the frame lane lands `--fold`.
- The dictionary-passing output of `Lower` (`instHAdd` records with erased `{}` arguments, §2.3) is
  exactly what `foldBook`/`dataPinSpecialize` would remove on the lowered term; `obend lower` does not
  call it either. Same request, one more call site.
- In the bb2 lane tree `Apps/SovereignDrex.lean` is red on `checkContractCert` (another lane's
  `Law/Contract.lean`, not synced there) and `Apps/ObendRisc.lean` is red on eight decide/omega
  fixtures unrelated to Leaf; neither was touched here.

### Second quest (2026-11-04, evening): the specialized book's link, and the emit sweep

**The theorem.** `Obend.Leaf.Served.link_bequiv_bindBookPins` (`lean/Obend/Leaf/Served.lean`):
for a book `B` and pins `pins`, if `B.link` and `(bindBookPins B pins).link` are closed, every
definition's code is a lambda (`LamCodes B`), and every pin is *served* (`Served B pins`: its code is
closed and `Meets B p.cell.key p.code`, i.e. the read `.get B.link m` and the code run to one term),
then `B.link ≈b (bindBookPins B pins).link`. `Obend.Leaf.Static.link_bequiv_specializeBook` composes
it with the folder (`specializeBook B pins = foldBook (bindBookPins B pins)`): `B.link ≈b
(specializeBook B pins).link`; `specializeBook_member_sound` goes through `book_sound` to the object.
The proof is the up-to technique of `UpTo.lean` over the one base pair of the two links: `joins_bind`
is the unfolding, an induction on a definition's body with `self` substituted by `B.link` on the
left and by the bound link on the right (`Joins.base` at `self`, the two runs to the meeting term at a
replaced read, congruence elsewhere); `entry_join` opens each dispatcher entry (one β for a method,
one under the application for a cell); `pair_base` is `fix` then two βs on each side.

**The honest quantifier.** Not "the pins hold at a view": the counterexample is in
`Teeth/Leaf/StaticTeeth.lean` as `example`s. `a = λself. 1`, `b = λself. self.a + 1`; the pin `a := 5`
holds at a view whose cell `a` holds `5` (`holdsAt … = true`), yet `run` of `b` on the book is `2` and
on `specializeBook B [a := 5]` is `6`. The dispatcher serves `1` for `a`, so that pin is not served;
`a := 1` is, and `b` stays `2`. `HoldsForBookMember` (per member, syntactic `evalBook`) remains as
the per-definition statement; the link-level hypothesis is `Served`, over the pins the book uses.

**The slot carries the proof.** `Candidate.specialized name C pins` (`Specialize.lean`), supports as
`.book`, judge `C.closedB && specializedJudgeB (emit C) pins` where `specializedJudgeB` decides the
four hypotheses: `closedB` of both links, `lamCodesB`, and `servesB` per pin by running the dispatcher
and the pin to values with `Obend.Law.run` (sound by `run_sound`) and comparing with `termEq`.
`Served.served_of_judgeB` reads the judge back as the hypotheses; a `#tooth` refuses a judge that
does not run the dispatcher (`judgeWithoutServing`). The slot theorems for it are in `Static.lean`
§11: `specialized_usable_sound` (usable at `viewOf k name C'` ⇒ `emit C = emit C'`, the specialized
book's link is the view's book's link, and when `C'` is closed every member is the object's),
`specialized_choice` (incumbent-first) and `specialized_moved_pin_blocks`. The binding definitions
moved from `Static.lean` to `Specialize.lean` so the judge can name them; `Specialize.lean`'s
candidate section now comes last, unchanged otherwise. `.slotBook`, whose judge is still `closedB`
alone and which no theorem connects to behaviour, is left as it was (its consumers are
`Spec/CrossPackage` and `Stdlib`); it should go the same way or go.

Commit `1bdf049`; built on bb2 against HEAD (`build14`): `Leaf.*`, `Teeth/Leaf/*`,
`Lower/Proofs/SiliconKernel`, `Tactic/SiliconElab`, `Hardware/{ReductionMachine,Fabric,UserspacePhysical}`,
`Stdlib`, `Apps/SiliconKernelVerilator` (with its routed hunks), and `obend`.

**The emit sweep** (`scratchpad/emit_sweep.py`, every `def` of every `.obend` under
`lean/tests/obend-source`, `apps/`, `stdlib/`, as `obend emit --package … --object DEF`), on bb2 with
the lane tree's `obend`, per directory, no totals:

| directory | defs tried | emitted, `07c04c1` export binary (morning) | emitted at HEAD `20a0459` (before this change) | emitted after `objectRefusal` |
|---|---|---|---|---|
| `apps/fidget-cam` | 32 | 0 | 28 | 28 |
| `apps/foc-hil` | 19 | 0 | 14 | 14 |
| `apps/obend-risc` | 13 | 0 | 9 | 9 |
| `apps/quantum-photonic-matter` | 23 | 0 | 19 | 19 |
| `apps/sdr-ft8` | 19 | 0 | 14 | 14 |
| `apps/silicon-kernel-verilator` | 9 | 0 | 8 | 8 |
| `apps/sovereign-drex` | 31 | 0 | 20 | 20 |
| `apps/zk-ntt` | 13 | 0 | 9 | 9 |
| `lean/tests/obend-source` | 504 | 9 | 33 | 33 |
| `stdlib/core` | 12 | 0 | 10 | 10 |
| `stdlib/physical` | 39 | 0 | 32 | 32 |

Logs: `bb2:~/lane-compiler-logs/sweep-before.log`, `sweep-head.log`, `sweep-after2.log`.

The apps' and stdlib's objects emit at HEAD already: the frame lane's `8efc555` (a seed written as a
def call) and the single-spec `fix(Spec, seed)` case did that between the morning sweep and this one.
What does not emit is, by construction, not an object, and `obend emit` now says which constructor
it reached instead of "no fix (compose …) {seed} is reached" alone (`Main.lean`, `objectRefusal`:
reduce the entry as `findObject` does, report the first `fix` on the way that misses the fragment and
why, else what the entry runs to; the package knot's own unnamed layer is skipped, not reported).
The refusal classes after the change, over the 518 refusals:

| refusals | what `obend emit` says |
|---|---|
| 313 | the entry runs to a function |
| 47 | the entry runs to the natural N |
| 29 | the entry runs to a record with fields […], not a fix: a record literal has no layers to flatten (the `seed*` defs of every app) |
| 18 | a fix stands at the head, but its first operand is not a spec or compose(…) of specs (`fix` over a prototype or an extension, `tests/obend-source/Ancestry.obend` and kin) |
| 17 | the entry runs to the boolean b |
| 13 | the entry runs to the constructor L |
| 40 | the elaborator's own refusals (`refused (kind-mismatch)`, `self-rigid`, … the refusal cohorts) and a few labels |
| 7 | the package spec did not build (a `.obend` whose imports the sweep's package writer does not resolve) |

Not done here, routed: `obend emit --fold` (apply `foldBook`, proved by `foldBook_member_sound`) and an
`obend specialize --pins` that offers `Candidate.specialized` with the judge above; the CLI knows
`.book` only. The remaining reds of `tests/metasystem/AutoCertTest.lean` on bb2 are not this lane's:
a heartbeat timeout at `:272`, `AutoCertSuite.accepted` and `Obend.Stdlib.stdlib_all_accepted`
unknown (names other lanes renamed); its `#check_docs_census` passes once the tree has the review
documents and `Hardware/CurrentLoop.lean` (`29f42a7` took the untracked `review/DECISIONS-LEDGER.md`
out of the census's governed lists and the `BendTT` out of `DESIGN.md`'s hardware row).
