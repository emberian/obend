# Lane A brief: tidy, the gating lemma, the abstract World, the CLI

For a fresh agent. Everything you need is in files; read them in this order, nothing else first:

1. `/Users/ember/dev/obend/lean/REPORT-20261030.md` (the predecessor's own report: what landed, the
   module discipline Lean 4.30 forced, decisions D1–D10, what was not done). This is your continuation.
2. `/Users/ember/dev/obend/lean/MODGRAPH-20261030.md` (one row per module).
3. `/Users/ember/dev/obend/SHIP.md` §1–§4 and `/Users/ember/dev/obend/DESIGN.md` §2.4 (the top clause
   you will state) via `/Users/ember/dev/redregg/work/promo/DESIGN-CTX.md` §2.1–§2.4.
4. The code: `/Users/ember/dev/obend/lean/Obend/Core/Check.lean` (1349 lines; `check` at :622,
   `Checked` at :614, `infer` above it, fuel-indexed), `Obend/Core/Ty.lean` (`Context := List Binding`
   at :184), `Obend/Slot.lean` (the slot: `Slot`, `usable`, `read`, `Permanent`, `slot_repair` at :131,
   `resolve`), `Obend/Slot/Calculus.lean` (the class, :23), `Obend/Slot/Core4.lean` (the instance at
   :174 and its docstring naming the owed lemma).

## Ground truth you will build against

```lean
-- Obend/Slot/Calculus.lean
class Calculus (Tm : Type) where
  Ty : Type
  Ctx : Type
  msubst : (Nat → Option Tm) → Tm → Tm
  check : Ctx → Tm → Ty → Bool
  uses : Tm → Nat → Bool
  drop : Ctx → Nat → Ctx
  strengthen : Nat → Tm → Tm
  weaken : Nat → Tm → Tm
  var : Nat → Tm
  lookup : Ctx → Nat → Option Ty

-- Obend/Core/Check.lean
structure Checked (source : AnnotatedTerm) (context : Context) where
  type : Ty
  uses : Uses
  derivation : PartialTyping source.assumptions context source.erase type uses
  safe : safeUses context uses = true
  contextValid : validContext source.assumptions.shareableVariables context = true
  assumptionsValid : source.assumptions.valid = true
def check (source : AnnotatedTerm) (context : Context) (fuel : Nat) : Option (Checked source context)

-- Obend/Slot/Core4.lean
instance : Obend.Slot.Calculus AnnotatedTerm   -- holes = free de Bruijn hypotheses, fillings closed
```

The build: `cd /Users/ember/dev/obend/lean && LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log`
(72 jobs; a no-op is half a second; a full rebuild ~80 s). Lean v4.30.0, no Mathlib, no Rust. Every
file is a `module`; 7 legacy leaves under `Obend/Core/Teeth/` and `Core/Proofs/DataBudget` are not
(REPORT §2 says why). `grind` and `decide +kernel` are available.

## Do, in this order, one commit each

1. **Tidy.** `mkdir lean/tools lean/docs`; move `modularize.py`, `publicize.py`, `modgraph.py`,
   `measure.sh` to `lean/tools/` (delete `modularize.py`/`publicize.py` if they are one-shot
   migrations nothing will run again, and say so); move `REPORT-20261030.md`, `MODGRAPH-20261030.md`,
   `MEASURE-20261030.log` to `lean/docs/`; fix links in `SHIP.md`. Write `lean/README.md` under 300
   words: toolchain, build, library map (Core, Core.Proofs, Digest, Slot), the module discipline in
   three sentences, where pins and teeth live.
2. **The gating lemma.** State and prove, in a new proof module `Obend/Core/Proofs/Substitution.lean`,
   the substitution lemma for `check`: a filling that checks at the type of a hypothesis, substituted
   for that hypothesis, keeps a checked term checked at the same type. First the fuel lemmas the
   fuel-indexed `infer` needs (monotonicity: more fuel never loses a result), as public theorems.
   Then discharge the owed law in `Obend/Slot/Core4.lean` and rewrite its docstring. If the lemma is
   false as stated for some corner (rigid rows, annotation merging under `msubst`, the fuel), say
   exactly which corner, state the lemma that is true, and keep the instance's four equations as
   they are. No sorry, no weakened statement, no new axiom.
3. **The abstract World.** `Obend/Slot/World.lean`: a typeclass for the history a slot's supports
   are judged against (views, a pin a view holds for a cell or row at a version, liveness, an audited
   step relation between views), with the laws the top clause needs as fields: a support false at a
   view stays false at every later view when its cell is retired (nano's `stale_behind_forever`
   shape: `git -C /Users/ember/dev/nanodregg show origin/main:Kernel/Proofs/Versions.lean`), and a
   derivation depends only on the pinned view (`receive_congr` shape, `origin/main:Kernel/Proofs/Receive.lean`).
   Then `Obend/Slot/Integrity.lean`: CONTEXTUAL INTEGRITY ∧ REPAIR (DESIGN-CTX §2.4, B4 and B4′)
   stated over that class, with the floor as named negative theorems `¬ Integrity credulousHoles`,
   `¬ Integrity firstCandidate`, `¬ Integrity blindRefusal`, and one non-trivial instance (a toy World
   with two members, one grant revoked) that satisfies it. Prove what follows from `slot_repair`,
   `read_blocked_names` and `resolve_ok`; what remains is a theorem with a documented premise.
4. **Finer `Core.Check` split** if step 2 showed the seams (REPORT §6 names the cascade); else say why not.
5. **CLI** `Main.lean` → `obend check FILE.json` / `obend run FILE.json [args]` over typed-core JSON,
   after a new small decoder (REPORT §6 says the Mini wire decoder is not small). Only after 1–3 are green.

Append `lean/docs/REPORT-20261031.md` in the predecessor's style: what landed, decisions each with a
critique and a meta-critique, what you did not do and why; update `SHIP.md` §2 rows for Core and Slot.

## Rules (Ember's, verbatim where quoted)

- Work only in `/Users/ember/dev/obend`. `~/dev/minidregg`, `~/dev/nanodregg`, `~/dev/bend` are
  read-only: never edit, build, stash or checkout there. Nothing under `lean/Journal/` or
  `lean/tools/journal/` is yours (lane B).
- Commits: named files only, branch `dev`, `git -c commit.gpgsign=false commit -F -` with the trailer
  `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`; `git pull --rebase origin dev` before
  each push; never `git add -A`; never stash.
- "**Never kill by pattern.** No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no
  `kill -u`. **A process you started is stopped by the PID in its PID file**, and only that. Every
  detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead."
- "**ember is in charge of disk pressure.** When a disk is low you have exactly three moves: **stop
  writing to it, tell me, wait.**" Delete only files you created under `lean/.lake` or your scratchpad.
- NEVER QUICK FIX. A green that cannot red is not evidence; every theorem keeps a tooth.
- No measurement harnesses; no inferences from counts.

Reply with: the commit range, which of steps 2 and 3 are fully proved versus stated with a premise,
and the one decision you most want Ember to look at.
