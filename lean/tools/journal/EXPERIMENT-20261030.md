# The one experiment (2026-10-30): the journal's repair set next to what Lake rebuilt

Run once by `experiment.sh` from `lean/` at commit `b3ddd73`, Lean v4.30.0, `LEAN_NUM_THREADS=2`,
on the live tree: lane A's uncommitted edits (`Obend/Core/Invariant.lean`,
`Obend/Core/Proofs/Adequacy.lean` modified, `Obend/Core/Proofs/Substitution.lean` new) were in the
tree throughout and unchanged between the exports (`git status` recorded before and after each
step, identical). Every export below is therefore of the same tree except for the one edit named.
The two edits are REPORT-20261030 §4's. No timing is claimed; the builds were all green (exit 0).
Export files were removed afterwards; the committed baseline is `env-b3ddd73.jsonl` (clean tree).

Columns: what Lake built (its `Built` lines, by name; a module Lake replayed from its trace is not
listed) against what the journal reports when the export before the edit is read against the
export after it.

## 0. Nothing edited

`lake build` on the live tree built 35 modules (lane A's `Invariant` edit is a definitional change
and cascades to everything downstream of it, as §4 step 2 found). Export before: 10735 rows, 71
modules (64 `module` files, 7 legacy), 6109 theorems.

## 1. A private trivial theorem appended to `Obend/Core/Proofs/Adequacy.lean`

`theorem measurement_private_tooth : (1 : Nat) + 1 = 2 := rfl` after the file's last line (a bare
`theorem` in a `module` file is private).

| Lake built (4) | journal |
|---|---|
| `Obend.Core.Proofs.Adequacy`, `Obend.Core.Teeth.BackFail`, `Obend.Core.Teeth.DataSoundness`, `Obend.Core.Teeth.Force` | withdrawn supports: **none**. STATEMENT-CITED: **none**. PROOF-CITED: **none**. revised: none. reproved: none. added theorems: `_private.Obend.Core.Proofs.Adequacy.0.measurement_private_tooth`. removed: none. unaffected: 6109 (every theorem of the before export). |

The root `Obend` did not rebuild this time (it became a `module` in `45c604f`; §4 measured it as a
legacy file). The three legacy leaves rebuilt, as §4 said they would by their nature.

## 2. An exposed `def` appended to `Obend/Core/Term.lean`

`def measurementScalar : Term → Bool | .nat _ | .boolean _ | .label _ => true | _ => false`,
inside the file's `@[expose] public section`, before `end Obend.Core.Term`.

| Lake built (52) | journal |
|---|---|
| `Obend`, `Obend.Core.Term`, `Obend.Core.Backend`, `Obend.Core.Capacity`, `Obend.Core.Check`, `Obend.Core.Checkpoint`, `Obend.Core.Collect`, `Obend.Core.Data`, `Obend.Core.Interaction`, `Obend.Core.Invariant`, `Obend.Core.Machine`, `Obend.Core.MachineFast`, `Obend.Core.MachineTyping`, `Obend.Core.Proofs.Adequacy`, `Obend.Core.Proofs.CheckpointRoundTrip`, `Obend.Core.Proofs.Collect`, `Obend.Core.Proofs.Completeness`, `Obend.Core.Proofs.DataBudget`, `Obend.Core.Proofs.DataSoundness`, `Obend.Core.Proofs.Force`, `Obend.Core.Proofs.Forcing.{Agree, Back, BackFail, Chain, Converse, Demand, Extract, Nest, Pend, Run, Segment, Switch}`, `Obend.Core.Proofs.LedgerPoles`, `Obend.Core.Proofs.Preservation`, `Obend.Core.Proofs.Preservation.Base`, `Obend.Core.Proofs.Preservation.Cases.{Activities, Arithmetic, Functions, Pairs, Records, Sums}`, `Obend.Core.Proofs.Settle`, `Obend.Core.Proofs.StepCases`, `Obend.Core.Proofs.Substitution`, `Obend.Core.Proofs.Templates`, `Obend.Core.Teeth.{BackFail, Collect, CollectTyping, CollectYield, DataSoundness, Force}`, `Obend.Slot.Core4` | withdrawn supports: **none**. STATEMENT-CITED: **none**. PROOF-CITED: **none**. revised: none. reproved: none. added theorems: none (the export gained 3 rows, all definitions: the `def` and its two match auxiliaries). removed: none. unaffected: 6109. |

Everything downstream of `Term` rebuilt, the whole `Core` tree and `Slot.Core4` (`Slot`,
`Slot.Protocol`, `Slot.Proofs.*`, `Slot.Calculus`, `Digest.*`, `AxiomPin`, `AssertAxioms`,
`AssertCompiled` do not import `Term` and were replayed). The journal's repair set is empty: a new
constant that nothing cites withdraws no support from any theorem.

## 3. Both edits removed

Lake printed no `Built` line at all (MEASURED; INFERRED: Lake 5 found the step-0 artifacts for the
reverted sources in its cache). Export: 10735 rows, 6109 theorems; against the
before export the journal reports nothing withdrawn, nothing added or removed, 6109 unaffected.

## Reading

The two repair sets are empty, by name: neither edit changes the meaning of any constant a
theorem's statement or proof reaches. Lake rebuilt 4 and 52 modules respectively, because its
unit is the module and its question is "did an input's trace change", not "did a meaning this
theorem depends on change". That is the gap PE1 names; this is one run that shows its size on
these two edits, nothing more. Step 3's 0 is Lake's cache, not a property of the edits.
An edit that does withdraw supports is the teeth's business (`teeth.sh` (a): a definition body
changed under a proof; the journal names the one theorem whose proof reaches it).
