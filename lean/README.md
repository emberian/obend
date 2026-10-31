# `lean/` — the Objective Bend library

**Toolchain.** Lean `v4.35.0`, Lake, no Mathlib, no Rust. Every file is a `module`, except the
legacy evaluation leaves under `Obend/Teeth/` and the census.

**Build.** Two tiers, from this directory:

    LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log          # tier 1: definitions and proofs
    LEAN_NUM_THREADS=2 lake build Obend.Census Teeth            # tier 2: teeth and the census, before a push

Tier 1 is the `Obend` library: every definition and proof. Tier 2 is the `Teeth` library
(`Obend/Teeth/`: the checker's `decide` fixtures, the `#tooth` mutation checks, the legacy evaluation
leaves) and `Obend/Census.lean`, the axiom check over every constant. Nothing in tier 1 imports tier 2,
so a tooth edit rebuilds one module and a proof edit never waits on a tooth. `tools/hooks/pre-push`
runs tier 2; `git config core.hooksPath lean/tools/hooks` installs it. A new top-level module or
directory under `Obend/` needs a glob in the `Obend` library (`lakefile.toml`); the census refuses one
that neither tier builds.

`lake build obend` then `python3 tests/run-obend-source.py` runs the front end's conformance cohorts,
and `python3 tests/run-receipts.py` the receipt tests. The `Journal` library and `lake exe journal`
(the obligation journal, `Journal/`, `tools/journal/`) build on demand.

**Library map** (`Obend.lean` re-exports the definitional modules).

- `Obend/Core/` — Core4: `Term`, `Ty`, the checker `Check`, the typed-core wire `Packet`, the
  demand `Machine` (`MachineFast`, `Invariant`, `MachineTyping`), `Data`, `Capacity`, `Collect`,
  `Checkpoint`, `Extensions`, `Interaction`, `Digest`.
- `Obend/Core/Proofs/` — the theorems about Core: `Adequacy`, `Completeness`, `Preservation.*`,
  `Forcing.*`, `Collect`, `Settle`, `Templates`, `DataSoundness`, `Substitution` (the substitution
  lemma for `check`), …
- `Obend/Teeth/` — tier 2: `Core/CheckTeeth` (the checker's `decide` fixtures), the evaluation leaves,
  the law and vault teeth, `Tactic/ToothChecks`.
- `Obend/Digest/` — `HashBytes`, cSHAKE256 (`Spec`, `Fast`, `Seam`).
- `Obend/Slot/` — the slot (`Obend.Slot`), open protocols (`Protocol`), their proofs, Core4's slot
  calculus (`Core4`: `Typed`, the checker as the slot's judge, `slotOf`), the abstract `World` and `Integrity`.
- `Obend/Spec/` — the `.obend` front end (trusted, no theorem: `Spec.lean` states the boundary):
  `Law`, `Syntax`, `Parse`, `Types`, `Annotated`, `C4`, `Contract`, `Elaborate`, `Sha256`, `FrontEnd`
  (`lower`, `accept`), `DataWire`, `Identity`, `Capture`, `Preview`.
- `Obend/Spec/Proofs/` — what is proved of its output: `Contract`, `C4Vectors`, `SpecificationClosure`,
  `FrontEndAdequacy`, `Law`; the legacy leaf `Teeth/Spec/TermWire` (`decode_json`: it unfolds `Lean.Json`).
- `Obend/Main.lean` — `lake exe obend check|run FILE.obend …` (the shape of Mini's `run.ts`; `--package`
  for multi-module), Mini's `capture`/`preview`/`identity` commands, and `check-core`/`run-core` on
  typed-core JSON.
- `tests/` — `run-obend-source.py` runs Mini's cohorts (`tests/obend-source/`: LTUO probes, tutorial,
  preview cohort) through the built `obend`; a differing outcome is a port defect.

**The module discipline.** A definitional module is `module` + `public section`, and a definition
carries `@[expose]` exactly when another module's `rfl`, `decide`, `simp`/`unfold` or kernel
reduction needs its body (an exposed body is interface: editing it rebuilds every importer; editing
an unexposed body rebuilds the module alone). Tier-2 teeth and runner examples that evaluate private
bodies `import all` the module instead. A derived `DecidableEq` that evaluation compares through is
`deriving @[expose] DecidableEq`. A proof module is `module`
with selective `public`: a theorem is public only if another module cites it, and a private
theorem's proof edit rebuilds nothing downstream. Imports are `public import` throughout, since a
public statement may mention anything its module imports.

**Census and teeth.** `Obend/Census.lean` (tier 2) runs `#assert_axioms_tree`
(`Obend/AssertAxioms.lean`) over every constant of the library, private ones included, and fails
the build on `sorryAx` or a declared axiom; it counts the `native_decide` theorems separately, and
each of those carries `#assert_compiled` (`Obend/AssertCompiled.lean`), which re-runs its claim
through the compiled evaluator. There are no per-theorem axiom lists. Teeth that need `Array.map`/`String.toUTF8` reduced are
legacy (non-`module`) leaves under `Obend/Teeth/`.

**Records.** `docs/`: the dated reports, module graphs, the one measurement. `tools/`: the split
scripts (`modularize.py`, `publicize.py`, `split.py`: a proof file into piece modules at declaration
boundaries), `modgraph.py`, `measure.sh`, `hooks/pre-push`.
