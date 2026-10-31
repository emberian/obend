# REPORT-SPEC 2026-10-30 — the `.obend` front end as `Obend.Spec`, so `obend` reads source (lane C)

Lane C (Claude Fable 5.1), on the brief `docs/LANE-C-BRIEF-20261030.md`. Tags as in the trees:
**MEASURED** (a command run here, output read), **READ** (a file opened), **INFERRED** (my reasoning).
Nothing in minidregg was edited, built, stashed or checked out; its sources were read with `cat`
and its history with `git log`/`git show`. Mini has no built oleans, so its front end was never run:
every conformance figure below is against outcomes Mini PINNED (its cohort files), never against a
fresh Mini run.

## 1. What landed (commits on `dev`, `24a62f5..` this commit; the Astra lane's `589d87b`, `dc29d01` sit between)

| commit | step | what |
|---|---|---|
| `24a62f5` | 1 | `Obend.Spec.Law` (Mini's `Compiler/ObjectiveBendLaw`: the fragment's syntax, parser, render, plus `LawExpr.denote` from `Kernel/ObjectLaw` over a four-field `Facts`; the `Pred` compile left to `Obend/Law` with a note), `Obend.Spec.Syntax` (the surface AST and `decodeModule`, split out of Mini's elaborator), `Obend.Spec.Parse` (Mini's parser, namespaces aside), `Obend.Spec.Proofs.Law` (the three compiled parser pins), `Obend/Spec.lean` with the trust boundary. |
| `18b4621` | 2 | `Obend.Spec.{Types,Annotated,Elaborate}` (Mini's elaborator split at the proposal types and the annotated core), `C4`, `Contract`, `Sha256`, `FrontEnd` (`lower`, `accept`); `Obend.Spec.Proofs.{Contract,C4Vectors,SpecificationClosure,FrontEndAdequacy}` as modules and `Proofs.TermWire` as a legacy leaf. Two Core theorems made `public` (§6). |
| `2731c39` | 3 | `Obend.Spec.Capture` (`package-input.v1` → `captured-package.v2`, `loadCapture`, the `parse`/`capture`/`elaborate` commands), `Obend.Spec.Preview` (the typed preview, `preview-input.v2` → `preview-result.v2`, `batch`), `Obend.Spec.DataWire` (structural, not `partial`), `Obend.Spec.Identity` (the fingerprint, an `elab` in a module). |
| `0252ac3` | 4 | `Obend.Main`: `obend check|run FILE.obend …` in the shape of Mini's `docs/tutorial/run.ts`, `--package`, Mini's `identity`/`parse`/`capture`/`elaborate`/`preview`/`batch`; lane A's packet path as `check-core`/`run-core`. |
| (this) | 5 | `lean/tests/obend-source/` (Mini's 36 test sources, the LTUO probe cohort — 29 rows by the brief, 30 in the file — 4 examples, 16 tutorial chapters and the tutorial text, the preview cohort with its `three-package`, `activity-factory` and `world/market` sources; all minidregg commit `092027a2`), `lean/tests/run-obend-source.py`, this report, the SHIP §2 row, the README map. |

**Preserved (MEASURED, a name census over Mini's eight proof-bearing files and `Obend/Spec/**`):** 53
of Mini's 54 theorem statements, every `#assert_axioms`/`#assert_compiled` pin among them, and every
refusal name (`inherited-unprovided`, `requires-unprovided`, `requires-signature`, `seed-extra`,
`provided-mismatch`, `inherited-mismatch`, `self-bound`, `self-conflict`, `self-undetermined`,
`self-rigid`, `super-rigid`, `self-unbound-member`, `replace-undeclared`, `seed-unresolved`,
`seed-not-record`, `template-typing`, `effect-as-argument`, `effect-in-field`, `effect-in-let`,
`effect-in-payload`, `effect-in-plan`, `perform-outside-activity`, `nullary-activity`,
`builtin-type`; `law-refuted` is Mini's target, not its current). Not ported: `replay_inhabited`
(Mini's `ObjectiveBendPublication`, §7). One statement changed shape: `Accepted.packetTerm`, a FIELD
in Mini proved inside `accept`, is a THEOREM here about every `Accepted` (D21). No `sorry`, no
axiom, no `partial`; every new theorem pinned standard or compiled.

**Green (MEASURED):** every `Obend.Spec.*` module, the proof leaves and `lake exe obend` build (77
jobs for those targets at the end); the whole tree was green at 95 jobs after step 2 (`lake build`,
2026-10-30). At the end it was NOT: another lane (the Astra commits) had, uncommitted in the same
checkout, a modified `Core/Proofs/Preservation/Base.lean` and a new
`Core/Proofs/TypedSubstitution.lean` that were red (`git status`, `build.log`); neither is mine and
I did not touch them (D26).

## 2. Conformance to Mini on Mini's own cohorts (MEASURED, `python3 tests/run-obend-source.py`)

- **LTUO probes: 30 of 30 at Mini's pinned `current` outcome** (the brief says 29; the file has 30
  rows). 29 `met`, `W08-LawImpossible` `pending LT6` exactly as in Mini (its `target` is
  `law-refuted`, its `current` `finished 41`; the port reproduces the current). Each refusal
  message starts with the pinned text; each finished value is equal.
- **Tutorial: 71 of 71 commands byte-equal** to the printed output in `OBJECTIVE-BEND-TUTORIAL.md`
  (the brief estimated 61), including the tick edges `shared --ticks 8219/8220` and `separate
  --ticks 16379/16380`, the interface labels with their byte spans, the activity turns, and the four
  refusals with their exit status 2, after ONE renaming: a machine diagnostic names
  `Obend.Core.Machine.Suspension.ticks` where Mini's names
  `Minidregg.Theory.ObjectiveBendDemandMachine.Suspension.ticks` (it is `reprStr` of the outcome).
- **Preview cohort: 161 items and the 4 request mutations green, with ONE stale pin held by name.**
  The driver is a port of Mini's `check-preview.ts` (capture, a `preview-input.v2` request,
  preview; `expectedData` with name-sorted records, the kernel Plan protocol, quiescent
  round-tripping checkpoints, `sameDecodedTerm` and empty `uses`). 33 `Market-*` rows import
  `../../world/market/*.obend` from Mini's `world/` tree (not in the brief's copy list); the seven
  files are copied under `tests/obend-source/world/market/`. The stale pin:
  `Structured-neverFinishing-no-partial-value` pins `expectedDataStatus: suspended`; the port prints
  `tickExhausted`. **READ** in Mini's history: the cohort was pinned on 2026-10-07; minidregg
  `1653897b6` (2026-10-08) split `Data.Failure.suspended` into `tickExhausted` (the forcing
  countdown) and `suspended` (capacity/policy), and its validation list has no `check-preview`.
  **MEASURED** here: heap 5000 trips capacity (`suspended`), heap 20000 and 100000 exhaust ticks
  (`tickExhausted`); the Core machine, fast machine and data modules are Mini's byte for byte modulo
  the rename (`diff` after `sed`). So Mini's current code prints `tickExhausted` too: not a port
  defect, a pin Mini's own later commit made stale. The script holds the row at `tickExhausted`
  under `STALE_PINS`, printing `STALE PIN … (minidregg 1653897b6)`, so a change in OUR behaviour is
  still red; nothing in the port was changed to pass it.

**Deviation from Mini, 2026-10-31 (Lane Elab, `lean/docs/REPORT-ELAB-20261031.md`): the checker's
grant is work, not nesting.** Mini's requests carry `typeFuel`, the historical checker's recursion
fuel, which bounds nesting and not the work done (a 1,000-field record nests 3 deep; Astra's
line-83 criticism). The front end now admits through preparation and `Bidirectional.checkAgainst`,
and its grant is `limits.checkWork`, the same measure and word as the slot judge's grant
(`Obend.Elab.Work.checkWork`: one per term node plus the constructors of every annotation the
checker reads). A request carrying `typeFuel` is refused by name. The re-pin, MEASURED by running
every cohort program through the gate:

| | Mini (before) | Obend (after) |
|---|---|---|
| grant key | `typeFuel` (nesting fuel) | `checkWork` (checker work) |
| preview cohort `LIMITS` | `typeFuel 4096` | `checkWork 43237`, the most any cohort program needs (`Market-book-*`); 43236 refuses those three by name (MEASURED) |
| budget mutation | `typeFuel 1` → `checker budget refused` | `checkWork 1` → `checker budget refused` |
| default (CLI, `lower`) | 4096 | 65536 |
| ceiling (`lower`, `preview`, packet decoder) | 16384 | 1048576 |
| probe cohort's largest program | — | 1405 (default suffices) |
| tutorial's largest program | — | 1755 (default suffices) |

The budget refusal now reads `checker budget refused: checkWork G is too small for this program (its
checker work is W); raise limits.checkWork`; the cohort pins only its prefix. The packet's `fuel`
field carries the grant; the open-template check, which still runs `Check.check` for
`check_instantiate`, takes it as fuel (work bounds nesting, so it is never short).

**Why the terms are Mini's (INFERRED from the tick edges):** `shared` finishing at 8220 ticks and
suspending at 8219 is a property of the exact elaborated term and the exact machine; both match
Mini to the tick on four edges, which no namespace rename could arrange.

## 3. The module map, and what each is

Definitional modules, `module` + `@[expose] public section` (D1's discipline): `Law` (387 lines),
`Syntax` (250), `Parse` (840), `Types` (120), `Annotated` (202), `C4` (200), `Contract` (121),
`Elaborate` (1712), `Sha256` (83), `FrontEnd` (334), `DataWire` (54), `Identity` (60), `Capture`
(308), `Preview` (291), the root `Spec` (41). Proof modules: `Proofs.Contract` (selective `public`;
the four laws are cited nowhere yet, kept public as statements the brief names),
`Proofs.{Law,C4Vectors,SpecificationClosure,FrontEndAdequacy}` as exposed-section leaves (D17's
shape: nothing imports them), `Proofs.TermWire` a legacy leaf (D21). `Obend.Main` 331 lines;
`tests/run-obend-source.py` 300.

Imports: Mini's, renamed, with the split's seams: `Syntax → Law`, `Parse → Law`, `Annotated →
Core.Term, Types`, `Elaborate → Syntax, Parse, Types, Annotated, C4, Contract, Core.Term`,
`FrontEnd → Elaborate, Sha256, Core.{Ty,Check,Packet}`, `Capture → FrontEnd, Identity`, `Preview →
Capture, DataWire, Core.{Machine,MachineFast,Data,Checkpoint,Packet}`, `Identity → every
definitional Spec module + meta Sha256`. No Spec module imports a Core proof module except
`Proofs.FrontEndAdequacy` (→ `Core.Proofs.{Preservation,DataSoundness}`).

## 4. The CLI

`obend run FILE.obend ENTRY [ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]` builds the package in
memory as `run.ts` does (module name from the file name: `[^A-Za-z0-9_]` → `_`, a leading digit
prefixed `M`; legacy argument encoding; heap 100000, stack 10000, checkWork 65536 (Mini: typeFuel 4096; §2); a bare response
label is that label with an empty payload), lowers in application mode, previews, and prints the
short form line for line (`typeText`/`dataText` are `run.ts`'s `ty`/`data`, including a label
printed as its JSON string literal and a weak-head variant as `label(...)`). `obend check FILE.obend
[ENTRY]` lowers each `def`/`spec`/`extension` (or the one named) in definition mode and runs
`accept`, one receipt per line, exit 2 on a refusal; a `record`/`sum` has no knot field and is
skipped. `--package PACKAGE.json` reads a `package-input.v1` through `captureSpec` for both. Mini's
file commands are unchanged (`Obend.Spec.Capture`/`Preview`), so Mini's `check-preview.ts` driver
is replayed by the test script against `obend capture` and `obend preview`. Lane A's packet path is
`check-core`/`run-core`, unchanged.

## 5. Decisions (each with a critique and a meta-critique)

**D19. `Law` lands in step 1 with `Parse`, and `denote` lives in `Law`.** *Why:* the parser refuses
a `law` line by calling `Law.parse`, so the brief's step-2 placement was impossible; `denote` is what
the brief asked for and it needs `Core.Data.Data`, so `Law` imports `Core.Data`. *Critique:* the
parser now transitively imports the demand machine (`Core.Data → Core.Machine`), a dependency Mini
avoided by keeping `denote` in its kernel. *Meta-critique:* I honoured the brief's "port `denote`
into `Law`" over Mini's layering; a `Law.Meaning` module would have kept the parser's closure small
at the cost of a module the brief did not name.

**D20. Mini's elaborator split three ways: `Types` (PTy), `Annotated` (ATerm, json, erase, depth,
mapTypes), `Elaborate` (the rest, 1712 lines).** *Why:* `Proofs.SpecificationClosure.composeTy_closed`
needs only `Types`; `Proofs.TermWire` only `Annotated` and `Core.Packet`; a proof edit there no
longer sits downstream of the 1700-line elaborator. *Critique:* `Elaborate` is still one exposed
module, so any edit to it rebuilds `FrontEnd`, `Identity`, `Capture`, `Preview`, `Main` and the
three leaves; the elaborator's own iteration time is unchanged from Mini. *Meta-critique:* a finer
split (synthesis / lowering / chains / knot) was visible and I did not do it, for the same reason as
D1: the mutual blocks cross those seams and the brief's first duty was behavioural identity.

**D21. `Proofs.TermWire` is a legacy leaf; `Accepted.packetTerm` is a theorem, not a field;
`Accepted`'s constructor is public.** *Why:* the proofs unfold `Lean.Json.mkObj`, `getObjVal?`,
`getStr?`, whose bodies Lean v4.30.0 exposes to no `module` (MEASURED: "Expected a definition with an
exposed body", with `import all Lean.Data.Json` too), and a module cannot import a legacy file. So
`accept` cannot cite `decode_json`; it records the depth bound it checked (`shallow`) and the leaf
proves `packetTerm` from `shallow`, `erasure`, `decoded` for every `Accepted`. The constructor is
public for D5's reason. *Critique:* Mini's "an `Accepted` carries a derivation for exactly the term
the elaborator produced" is now two steps: the structure, and a theorem in a leaf nothing imports.
A forged `Accepted` is type-correct, as D5 said of `ExecutionWith`. *Meta-critique:* this is the
one place the extraction changed what a value of a type says; the alternative (the whole front end
legacy, as Mini is) was available and I preferred keeping the front end's fourteen modules modular.
§8 puts it to Ember.

**D22. Compiled pins need `public import X` AND `public meta import X`; `Identity`'s manifest is an
`elab` in a module with `meta import Sha256`.** *Why:* MEASURED: `native_decide` in a module says
"`parse` is not accessible here; consider adding `public meta import`", and a `meta import` alone
makes ordinary definitions say "may not access declaration imported as `meta`". *Critique:* two
import lines per leaf, and `meta def sources` so the elab can read it. *Meta-critique:* lane A's
`DigestChecks` got away with one line because it defines nothing non-meta; I generalised from it and
paid a build cycle.

**D23. The two Core theorems made public: `Preservation.check_runBounded_no_refusal`,
`DataSoundness.execution_source_semantics`.** *Why:* `accepted_never_refused` and
`accepted_execution_semantics` are their instances at an `Accepted`; a private theorem cannot be
cited. One word each, no statement touched. *Critique:* their proof edits now rebuild
`Proofs.FrontEndAdequacy`, which is the iteration cost D2 warned of. *Meta-critique:* this is the
smallest change; the brief's clause was for the elaborator and I read it as covering the adequacy
theorems too.

**D24. `obend run` builds its package in memory; `check` iterates declarations in definition mode.**
*Alternative:* write a temp dir with `package.json`, capture, request and preview files as `run.ts`
does. *Why:* the in-memory path runs the same `captureModule`, `lower`, `preview` as the file path,
and the file path is still there (`capture`/`preview`) for the cohort driver. *Critique:* `run`'s
JSON (`--json`) is the typed preview without `binding` (`run.ts` printed `result.preview ?? result`,
so the same), but a caller wanting the capture hashes must use `capture` + `preview`; `check`'s
receipts are mine, not a Mini shape. *Meta-critique:* I chose the shape of the brief's "the shape of
`docs/tutorial/run.ts`" literally for `run` and invented `check`'s receipt, which no cohort pins.

**D25. Tests as a Python script over the built binary, with the preview cohort beyond the brief, the
Market sources copied, and the stale pin held by name.** *Why:* a `lake exe obend-tests` needs a
lakefile edit (D18's shared-file lesson), and the brief allowed a script; the preview cohort is the
same package shape and reaches `three-package`, `activity-factory` and the kernel Plan protocol,
which the probes do not. *Critique:* a Python driver is one more language in a Lean tree, and it
assumes `lake build obend` ran. *Meta-critique:* the stale-pin table is the kind of thing that
grows into a quiet allowlist; it has one row, with Mini's commit in it, and the report says so. If
Mini re-pins the row, the row is deleted.

**D26. The gate at the end is my targets, not `lake build`.** *Why:* the brief said I was alone in
the checkout; `git status` at step 5 showed another lane's uncommitted edits and two red modules of
its own. I built `obend`, `Obend.Spec` and the six proof leaves instead, and committed named files
only. *Critique:* "whole tree green at every commit" (REPORT-20261031 §1) does not hold for my last
commit, through no file of mine. *Meta-critique:* I noticed at step 5 because the job count moved
from 95 to 106; a `git status` before each build would have told me a step earlier.

## 6. Core definitions exposed (the brief's clause)

`public theorem check_runBounded_no_refusal` in `Obend/Core/Proofs/Preservation.lean` and
`public theorem execution_source_semantics` in `Obend/Core/Proofs/DataSoundness.lean`: one keyword
each, statements and proofs untouched (commit `18b4621`). No Core definition needed exposing for the
elaborator: `Core.Check`, `Core.Packet`, `Core.Ty`, `Core.Term`, `Core.Data`, `Core.Checkpoint`,
`Core.Machine` are definitional modules and already exposed.

## 7. Not done, and why

- **The `Pred` compile of the law fragment** (`compile`, `packageLaw`, `LawRef.slot`,
  `compile_sound`): no `Pred` in this tree; `Obend/Law`'s, as the brief says.
- **Mini's publication binding** (`ObjectiveBendPublication`, `example_package`,
  `replay_inhabited`, `admitted_front_end`): the receiver side; not in the brief's file list.
- **`Compiler/Sha256Vectors.lean`** (FIPS known-answer vectors): not in the list; the identity and
  the capture hashes are exercised by the cohorts (a wrong `captureSha256` refuses).
- **`obend run` flags for `argumentEncoding: typed-values-v1` and `projections`:** available only
  through `preview REQUEST`; `run.ts` had neither.
- **A byte comparison of `.core.json`/`.typed.json` against Mini:** Mini is unbuilt here; the
  conformance is against pins. Four tick edges matching to the tick is the strongest evidence I have
  that the terms are identical.
- **`lean/README.md` under 300 words:** the map grew by six lines; I did not re-cut it.

## 8. The one decision for Ember

**D21.** Lean v4.30.0's module system cannot see `Lean.Json`'s bodies, so every theorem about the
typed-core WIRE (`decode_json`, `decodePacket_term`, `Lowering.packet_term`, `Accepted.packetTerm`)
lives in a legacy leaf, and `accept` no longer carries "the packet's term is my erasure" inside the
value it returns: an `Accepted` holds the depth bound, and the theorem is one import away in a file
no module can import. Either accept this (the front end stays fourteen `module` files; the theorem
is stated and pinned, and `Accepted.sound` is still a theorem), or make `Obend.Spec.FrontEnd` and
everything downstream legacy files so `accept` proves `packetTerm` in place as Mini's did (losing
the module discipline for the Host layer), or take the wire off `Lean.Json` (an own JSON type whose
bodies a module exposes), which is a Spec design change the brief did not ask for. I chose the
first and said so at the top of `FrontEnd.lean`.
