# `lean/` — the Objective Bend library

**Toolchain.** Lean `v4.30.0`, Lake, no Mathlib, no Rust. Every file is a `module`, except the
seven evaluation leaves named below.

**Build.** From this directory:

    LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log

A no-op is half a second; a full rebuild about 80 s. `lake build obend` then
`python3 tests/run-obend-source.py` runs the front end's conformance cohorts. The `Journal` library and `lake exe journal`
(the obligation journal, `Journal/`, `tools/journal/`) build on demand.

**Library map** (`Obend.lean` re-exports the definitional modules).

- `Obend/Core/` — Core4: `Term`, `Ty`, the checker `Check`, the typed-core wire `Packet`, the
  demand `Machine` (`MachineFast`, `Invariant`, `MachineTyping`), `Data`, `Capacity`, `Collect`,
  `Checkpoint`, `Extensions`, `Interaction`, `Digest`, the executor typeclass `Backend`.
- `Obend/Core/Proofs/` — the theorems about Core: `Adequacy`, `Completeness`, `Preservation.*`,
  `Forcing.*`, `Collect`, `Settle`, `Templates`, `DataSoundness`, `Substitution` (the substitution
  lemma for `check`), `CheckTeeth` (the checker's `decide` fixtures), …
- `Obend/Digest/` — `HashBytes`, cSHAKE256 (`Spec`, `Fast`, `Seam`), the `Digest` typeclass.
- `Obend/Slot/` — the slot (`Obend.Slot`), open protocols (`Protocol`), their proofs, the calculus
  typeclass (`Calculus`), Core4 as its instance (`Core4`), the abstract `World` and `Integrity`.
- `Obend/Spec/` — the `.obend` front end (trusted, no theorem: `Spec.lean` states the boundary):
  `Law`, `Syntax`, `Parse`, `Types`, `Annotated`, `C4`, `Contract`, `Elaborate`, `Sha256`, `FrontEnd`
  (`lower`, `accept`), `DataWire`, `Identity`, `Capture`, `Preview`.
- `Obend/Spec/Proofs/` — what is proved of its output: `Contract`, `C4Vectors`, `SpecificationClosure`,
  `FrontEndAdequacy`, `Law`, and the legacy leaf `TermWire` (`decode_json`: it unfolds `Lean.Json`).
- `Obend/Main.lean` — `lake exe obend check|run FILE.obend …` (the shape of Mini's `run.ts`; `--package`
  for multi-module), Mini's `capture`/`preview`/`identity` commands, and `check-core`/`run-core` on
  typed-core JSON.
- `tests/` — `run-obend-source.py` runs Mini's cohorts (`tests/obend-source/`: LTUO probes, tutorial,
  preview cohort) through the built `obend`; a differing outcome is a port defect.

**The module discipline.** A definitional module is `module` + `@[expose] public section`: its
bodies are its interface, so a change there rebuilds every importer. A proof module is `module`
with selective `public`: a theorem is public only if another module cites it, and a private
theorem's proof edit rebuilds nothing downstream. Imports are `public import` throughout, since a
public statement may mention anything its module imports.

**Pins and teeth.** `#assert_axioms` (standard axioms only) and `#assert_compiled` (re-runs a
`native_decide` claim) live in `Obend/AxiomPin.lean`, `AssertAxioms.lean`, `AssertCompiled.lean`;
every proof module ends with its pins. Teeth that need `Array.map`/`String.toUTF8` reduced are the
legacy (non-`module`) leaves `Obend/Core/Teeth/*.lean` and `Core/Proofs/DataBudget.lean`.

**Records.** `docs/`: the dated reports, module graphs, the one measurement. `tools/`: the split
scripts (`modularize.py`, `publicize.py`), `modgraph.py`, `measure.sh`.
