# Lane B brief: a declaration-level obligation journal over the obend tree

For a fresh agent. Read, in this order:

1. `/Users/ember/dev/redregg/work/HOLES-FOR-PROOF-ENGINEERING-20261020.md` (the memo; PE1 is the
   card you are building the first slice of) and `/Users/ember/dev/obend/THESIS.md` §1.5.
2. `/Users/ember/dev/obend/lean/docs/REPORT-20261030.md` §2 and §4 (the module discipline; the one
   measurement: a private proof edit in `Core.Proofs.Adequacy` rebuilt only Adequacy plus three legacy
   leaves; an exposed def appended to `Core.Term` rebuilt the whole tree).
3. `/Users/ember/dev/obend/lean/Obend/Slot.lean` (the slot you will instantiate) and
   `/Users/ember/dev/obend/lean/Obend/AxiomPin.lean` (an `elab` command over `collectAxioms`: the
   idiom for walking the environment in this tree).

## Ground truth

```lean
-- Obend/Slot.lean
structure Slot (Fact Cand : Type) where   -- :33  (supports : Cand → List Fact, judge : Cand → Bool)
def Slot.usable (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) : Bool
def Slot.read   (S : Slot Fact Cand) (holds : Fact → Bool) : Option Cand → Reading Fact Cand
def Permanent {V} (holdsAt : V → Fact → Bool) (later : V → V → Prop) (f : Fact) : Prop
theorem slot_repair {V} (S : Slot Fact Cand) (holdsAt : V → Fact → Bool) ...   -- :131, THE theorem
```

The tree: `/Users/ember/dev/obend/lean`, Lean v4.30.0, no Mathlib; `cd` there and
`LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log` (72 jobs, ~80 s full, half a second no-op).
Every file under `Obend/` is a `module` except 7 legacy leaves. Lean's environment API:
`Lean.Environment`, `ConstantInfo`, `Expr.getUsedConstants`, `Lean.collectAxioms`, `Lean.Name`;
hashing: `Expr.hash` is structural; for content hashes of a declaration's type and value use the
olean-independent route (hash of the `Expr` after instantiating level params to a canonical order,
or `toString` of the pretty-printed term if that is what you can defend; say which).

## Build

1. **Export** (`lean/Journal/Export.lean`, a `module`; driver as a `lean_exe journal` in
   `lean/lakefile.toml`, sources under `lean/tools/journal/`): for every declaration whose module
   name starts with `Obend`, write one JSONL row: name, module, kind, visibility (private/public in
   module files), constants cited by the type, constants cited by the value, a content hash of the
   type, a content hash of the value, the axiom set. Output `lean/tools/journal/env-<git-commit>.jsonl`.
2. **The journal** (`lean/Journal/Journal.lean`): each theorem is a `Slot` whose candidate is its
   current proof and whose supports are the `(name, typeHash)` of every constant the statement cites
   plus the `(name, valueHash)` of every constant the proof cites. Given two exports, compute the
   withdrawn supports and the exact repair set split into STATEMENT-CITED (meaning may have changed)
   and PROOF-CITED (proof must be re-checked, statement intact), and the theorems unaffected. Use
   `Obend.Slot` where it fits and say in the docstring where it does not.
3. **One experiment**, `lean/tools/journal/EXPERIMENT-20261030.md`: make the two edits REPORT §4
   made (a private trivial theorem appended to `Obend/Core/Proofs/Adequacy.lean`; an exposed def
   appended to `Obend/Core/Term.lean`), export before and after each, run the journal, and list the
   exact repair set versus the modules Lake rebuilt, by name. Revert both. One run; no timing claims.
4. **Teeth** as `lean/tools/journal/teeth.sh` or Lean tests: (a) change a definition body a theorem's
   proof unfolds but its statement never mentions: the journal lists that theorem under PROOF-CITED
   and nowhere else; (b) swap the order of two independent declarations: the journal flags nothing.

Write `lean/Journal/README.md` under 300 words: what it is, how to run it, what it does not claim.
Append a dated section to `lean/docs/REPORT-20261031.md` if it exists, else create
`lean/docs/REPORT-JOURNAL-20261030.md`, in the REPORT-20261030 style (decisions with critique and
meta-critique).

## Rules (Ember's, verbatim where quoted)

- Yours: `lean/Journal/`, `lean/tools/journal/`, one `[[lean_lib]]`/`[[lean_exe]]` stanza in
  `lean/lakefile.toml`, your report file. Everything else under `lean/` is lane A's: do not touch it
  except to read; your experiment's edits to `Adequacy.lean`/`Term.lean` are reverted before commit.
- Work only in `/Users/ember/dev/obend`; the other trees are read-only. Commits: named files, branch
  `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Fable 5.1
  <noreply@anthropic.com>`, `git pull --rebase origin dev` before each push, never `git add -A`,
  never stash. If lane A's work and yours both touched `lakefile.toml`, keep both stanzas.
- "**Never kill by pattern.** No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no
  `kill -u`. **A process you started is stopped by the PID in its PID file**, and only that. Every
  detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead."
- "**ember is in charge of disk pressure.** When a disk is low you have exactly three moves: **stop
  writing to it, tell me, wait.**" Delete only files you created.
- NEVER QUICK FIX; no sorry; no axiom. No harness beyond the one experiment; no inferences from counts.

Reply with: the commit range, the two repair sets by name, whether `Obend.Slot` fit and where not,
and the one decision you most want Ember to look at.
