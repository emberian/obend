# Journal — a declaration-level obligation journal over the `Obend` tree

**What it is.** `Journal.Export` walks the built environment and writes one JSONL row per
declaration whose module starts with `Obend`: name, module, kind, visibility, exposure, the
constants its type and value cite (tree constants only), 64-bit structural hashes of type and
value, the axiom set. `Journal.Journal` reads two such exports as two views of the library. Every
theorem of the first is an `Obend.Slot.Slot` whose single candidate is its recorded proof and whose
supports are `(name, meaning)` facts: the constants its statement reaches and the constants only its
proof reaches, closed transitively along meaning edges (types always; bodies except through theorem
proofs). A support holds at the second view when the name is there with the same meaning.
`Slot.read` gives the verdict: UNAFFECTED, STATEMENT-CITED (a statement-reached support
is dead: its meaning may have changed), or PROOF-CITED (only proof-reached supports are dead:
re-check the proof).
`verdict_unaffected_iff` and `verdict_blocked` prove the verdict is the slot's read.

**Running it** (from `lean/`, after `lake build`):

    lake exe journal export                    # tools/journal/env-<commit>[-dirty].jsonl
    lake exe journal export --out FILE.jsonl --only Obend.Slot   # a subtree
    lake exe journal diff OLD.jsonl NEW.jsonl [--names]

`OUT=<scratch dir> tools/journal/teeth.sh` runs the two teeth; `tools/journal/experiment.sh` is the
one experiment (`tools/journal/EXPERIMENT-20261030.md`).

**What it does not claim.** The verdict is a dependency reading, not a re-check: PROOF-CITED means
the kernel should look again, not that the proof fails; UNAFFECTED means no tree constant the
theorem reaches changed meaning, under this hash (64-bit structural, not cryptographic) and this
notion of meaning (toolchain constants are a fixed background; a `lean-toolchain` bump is not read). A theorem
whose own statement changed is REVISED, outside any slot: nothing says the new statement succeeds
the old. Exports of a tree with uncommitted edits compare those edits too.
