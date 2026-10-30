# Lane C brief: the `.obend` front end (`Obend.Spec`), so `obend` reads source, not JSON

For a fresh agent. Ember, 2026-10-30: "stop reading typed-core JSON..? that's so slow/ugly etc let's
make sure we have a parsing frontend even if that part isn't assured! ;)" The front end is TRUSTED
(no theorem says the core means what the source says; minidregg's `docs/OBJECTIVE-BEND.md` §"What
is open" says so) and that is acceptable. What must hold: the port is byte-identical in behaviour to
Mini's front end on Mini's own test cohort, and its trust boundary is written at the top of its root.

Read, in this order:
1. `/Users/ember/dev/obend/lean/README.md`, `/Users/ember/dev/obend/lean/docs/REPORT-20261031.md`
   (lane A's: what `Obend.Core.Packet`, `Obend.Main` and the `obend` CLI are today), `SHIP.md` §2 row `Obend/Spec`.
2. `/Users/ember/dev/minidregg/docs/OBJECTIVE-BEND-FRONTEND.md` (the reference: stages, commands,
   capture format, preview wire, the surface-to-core lowering table, typing proposal, trust boundary).
3. `/Users/ember/dev/minidregg/docs/OBJECTIVE-BEND-TUTORIAL.md` and `docs/objective-bend/examples/*.obend`,
   `docs/tutorial/ch*.obend` (16 files), `tests/objective-bend-source/*.obend` (36) and
   `tests/objective-bend-source/ltuo/probe-cohort.json` (29 probes with pinned outcomes), and
   `docs/tutorial/run.ts` (how capture → preview is driven; the `preview-input.v2` request shape).
4. The code to port, in `/Users/ember/dev/minidregg` (read-only; use `cat`, never build there):
   `Compiler/ObjectiveBendParse.lean` (834 lines; imports `Lean`, `Compiler.ObjectiveBendLaw`),
   `Compiler/ObjectiveBendLaw.lean` (353; imports `Theory.AssertCompiled`, `Pred.Core`: the law
   fragment and its `Pred` compile), `Compiler/ObjectiveBendElaborate.lean` (2194; imports `Lean`,
   Parse, Law, `Std.Data.HashMap`, `Theory.ObjectiveBendOpenRecursion`, C4, Contract),
   `Compiler/ObjectiveBendC4.lean` (191; imports `Std.Data.HashMap`), `Compiler/ObjectiveBendContract.lean`
   (187; imports `Theory.AssertAxioms`), `Compiler/ObjectiveBendTermWire.lean` (294),
   `Compiler/ObjectiveBendFrontEnd.lean` (333; adds `Compiler.Sha256`, 76 lines, pure Lean),
   `Compiler/ObjectiveBendDataWire.lean` (44), `Compiler/ObjectiveBendC4Vectors.lean` (198),
   `Compiler/ObjectiveBendSpecificationClosure.lean` (306), `Compiler/ObjectiveBendFrontEndAdequacy.lean`
   (106), `Host/ObjectiveBendFrontEnd.lean` (459: `capture`, `preview`) and `Host/ObjectiveBendPreview.lean` (130).
   None has `@[extern]`. No `partial def` in Parse or Elaborate.

## Ground truth in the target tree

`/Users/ember/dev/obend/lean`: Lean v4.30.0, no Mathlib, every file a `module` (private by default;
`public import`, `public def`, `@[expose]`), 78 jobs green, build `LEAN_NUM_THREADS=2 lake build 2>&1
| tee build.log` (full ~80 s). `Obend.Core.Term` has the `Term` the elaborator targets (renamed from
`Minidregg.Theory.ObjectiveBendOpenRecursion`); `Obend.Core.Check` has `AnnotatedTerm`, `Context`,
`check`; `Obend.Core.Packet` is the typed-core packet decoder lane A split out; `Obend.Main` is the
CLI (`lake exe obend check|run FILE.json`). `Obend.AxiomPin` has `#assert_axioms`; `Obend.AssertCompiled`
has `#assert_compiled`. There is NO `Pred` library in this tree: `ObjectiveBendLaw` compiles the law
fragment to Mini's `Pred`; port the fragment's syntax, parser and `LawExpr.denote` meaning, and
leave the `Pred` compile out with a one-line note (it is `Obend.Law`'s, a later lane).

## Build, one commit each

1. **`Obend.Spec.Syntax`, `Obend.Spec.Parse`**: the AST and parser, module names `Obend.Spec.*`,
   namespaces `Obend.Spec.*`. Definitional modules in exposed sections as lane A did (REPORT-20261030 §2).
2. **`Obend.Spec.C4`, `Obend.Spec.Contract`, `Obend.Spec.Elaborate`, `Obend.Spec.Law`**: the lowering
   to `Obend.Core.Term` + typing proposal. Keep every refusal name (`inherited-unprovided`,
   `requires-unprovided`, `self-rigid`, `replace-undeclared`, …) exactly. Proofs that come with them
   (`run_append`, `run_assoc`, `checkLayer_ok`, `discharge_ok` in Contract; the C4 vector theorems;
   the specification-closure theorems `composeTy_closed`, `twice_accepted`, `claim_spec_accepted`;
   `FrontEndAdequacy`'s `accepted_typed`, `accepted_never_refused`, `accepted_execution_semantics`,
   `accept_inhabited`, `decode_json`, `decodePacket_term`) go to `Obend.Spec.Proofs.*` with every
   statement and `#assert_axioms` pin kept.
3. **Capture and preview** (`Obend.Spec.Capture`, `Obend.Spec.Preview`): the locked package
   (`package-input.v1` → `captured-package.v2`) and the preview that elaborates, checks and runs
   (`preview-input.v2` → `preview-result.v2`), as in `Host/ObjectiveBend{FrontEnd,Preview}.lean`.
   `Obend.Spec.Identity`: the front-end fingerprint over the ported modules' sources.
4. **The CLI reads source.** `lake exe obend check FILE.obend`, `obend run FILE.obend ENTRY [ARGS_JSON]
   [RESPONSES_JSON] [--ticks N] [--json]` (the shape of `docs/tutorial/run.ts`, single-module; a
   `--package package.json` form for multi-module). Keep the typed-core JSON path as `obend check-core`.
5. **Tests, as a `lake exe obend-tests` or a script under `lean/tests/`**: copy the 36 `.obend`
   test sources, the 29-probe `probe-cohort.json`, the 4 examples and 16 tutorial chapters into
   `lean/tests/obend-source/` (they are Mini's; cite the commit) and run every probe and every
   tutorial command, asserting the pinned `current` outcome and value. A probe whose outcome differs
   from Mini's is a port defect, not a new truth: fix the port. Record the run in
   `lean/docs/REPORT-SPEC-20261030.md`.

Write the trust boundary at the top of `Obend/Spec.lean` in Mini's words: trusted with no theorem are
the parser, the elaborator's choices and the C4 implementation; proved of the output are the
adequacy theorems. Update `SHIP.md` §2's `Obend/Spec` row and `lean/README.md`'s map. Report in the
style of `lean/docs/REPORT-20261030.md`: what landed, decisions with critique and meta-critique
(module granularity; what you exposed; where the port had to change a signature), not done and why.

## Rules (Ember's, verbatim where quoted)

- Yours: `lean/Obend/Spec.lean`, `lean/Obend/Spec/**`, `lean/tests/**`, `lean/Obend/Main.lean` (the
  CLI; lane A finished with it), your report, the `SHIP.md` row and README map lines. Do not touch
  `Obend/Core/**`, `Obend/Slot/**`, `Obend/Digest/**`, `Journal/**`, `tools/**`. If the elaborator
  needs a Core definition exposed that is not, expose it in the smallest change and name it in the report.
- Work only in `/Users/ember/dev/obend`; `~/dev/minidregg`, `~/dev/nanodregg`, `~/dev/bend` read-only.
  Commits: named files, branch `dev`, `git -c commit.gpgsign=false commit -F -`, trailer
  `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`, `git pull --rebase origin dev` before
  each push, never `git add -A`, never stash.
- "**Never kill by pattern.** No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no
  `kill -u`. **A process you started is stopped by the PID in its PID file**, and only that. Every
  detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead."
- "**ember is in charge of disk pressure.** When a disk is low you have exactly three moves: **stop
  writing to it, tell me, wait.**" Delete only files you created.
- NEVER QUICK FIX: no sorry, no axiom, no dropped pin, no refusal renamed to make a probe pass.
- No measurement harness; the probe cohort is a conformance check, not a benchmark.

Reply with: the commit range, the probe cohort result (n of 29 at Mini's pinned outcomes, each
difference named), which Core definitions you had to expose, and the one decision for Ember.
