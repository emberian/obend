# `lean/` — the Objective Bend library

**Toolchain.** Lean `v4.30.0` (`lean-toolchain`), Lake, no Mathlib, no Rust. Every file is a Lean
4.30 `module`, except the seven evaluation leaves named below.

**Build.** From this directory:

    LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log

A no-op is half a second; a full rebuild about 80 s (72 jobs). `grind` and `decide +kernel` are
available. The `Journal` library and `lake exe journal` belong to the obligation journal
(`Journal/`, `tools/journal/`), built on demand.

**Library map** (`Obend.lean` re-exports the definitional modules).

- `Obend/Core/` — Core4: `Term`, `Ty`, the checker `Check`, the typed-core wire `Packet`, the
  demand `Machine` (and `MachineFast`, `Invariant`, `MachineTyping`), `Data`, `Capacity`,
  `Collect`, `Checkpoint`, `Extensions`, `Interaction`, `Digest`, the executor typeclass `Backend`.
- `Obend/Core/Proofs/` — the theorems about Core: `Adequacy`, `Completeness`, `Preservation.*`,
  `Forcing.*`, `Collect`, `Settle`, `Templates`, `DataSoundness`, `Substitution` (the substitution
  lemma for `check`), `CheckTeeth` (the checker's `decide` fixtures), …
- `Obend/Digest/` — `HashBytes`, cSHAKE256 (`Spec`, `Fast`, `Seam`), the `Digest` typeclass.
- `Obend/Slot/` — the slot (`Obend.Slot`), open protocols (`Protocol`), their proofs, the calculus
  typeclass (`Calculus`), Core4 as its instance (`Core4`), the abstract `World` and `Integrity`.
- `Obend/Main.lean` — `lake exe obend check FILE.json` / `obend run FILE.json [--ticks N …]`.

**The module discipline.** A definitional module is `module` + `@[expose] public section`: its
bodies are its interface, so a change there rebuilds every importer. A proof module is `module`
with selective `public`: a theorem is public only if another module cites it, and a private
theorem's proof edit rebuilds nothing downstream. Imports are `public import` throughout, because a
public statement may mention anything its module imports.

**Pins and teeth.** `#assert_axioms` (standard axioms only) and `#assert_compiled` (re-runs a
`native_decide` claim) live in `Obend/AxiomPin.lean`, `AssertAxioms.lean`, `AssertCompiled.lean`;
every proof module ends with its pins. Evaluation teeth that need `Array.map`/`String.toUTF8`
reduced are the legacy (non-`module`) leaves `Obend/Core/Teeth/*.lean` and
`Core/Proofs/DataBudget.lean`; nothing imports them.

**Records.** `docs/` holds the dated reports, the module graph and the one measurement; `tools/`
the scripts that made the split (`modularize.py`, `publicize.py`), `modgraph.py` and `measure.sh`.
