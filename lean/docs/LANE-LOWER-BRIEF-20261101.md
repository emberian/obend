# Lane Lower: verified lowering of a Lean fragment to Core4

Worktree: `/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/kinds`, branch `lane-lower` (already created from `origin/dev`). Build on hbox
(`~/obend/repo`, user `hbox`; make your own worktree there as the Ticks lane did, e.g. `~/obend/lower`)
per `lean/docs/BUILD-ON-BB2.md`; read `~/swarm/MACHINES.md` and `RULES.md` first.

## Why
Ember, 2026-11-01: a verified pipeline from Lean programs to silicon, through obend. The links that
exist: Core4 to the Leaf book (`Obend/Leaf/Flatten.lean` `flatten_sound`, `Emit.lean` `book_sound`),
the book to BendTT's `Eval` (stated, `REPORT-LEAF-20261101.md` §5). The missing link is the first:
Lean to Core4. Dependent types are not lowered, they are erased, as MetaCoq's verified erasure to λ□
does for Coq (Forster–Sozeau–Tabareau 2024; the λ□ language is described in
`~/paperbin/sdima2025-compiling-lean-with-rocq-extraction.txt` §3.3, a 2025 report that bridged Lean's
`Expr` to λ□ without verifying the bridge). The source semantics is Lean4Lean (Carneiro, TYPES 2025,
`~/paperbin/carneiro2025-lean4lean-types.txt`; repo `github.com/digama0/lean4lean`): Lean's kernel
language modeled in Lean, with typing, definitional equality and `whnf` as relations. Lean is not
strongly normalizing and the theorem does not need it: it is per term.

## Ground truth
`lean/Obend/Core/Term.lean`: `inductive Term` (line 22) with constructors `hole`, `bound`, `lam`,
`app`, `mix`, `fix`, `specification`, `prototype`, `reflect`, `metadata`, `project`, `nat`,
`boolean`, `label`, `binary prim l r` (primitives `add multiply subtract divide modulo equal less
lessEqual conjunction labelEqual`), `extend`, `record`, `get`, `ifZero`, `inject`, `case`, `ifBool`,
`perform`, `done`, and C2's `split target names function`; `inductive Steps` (line 349);
`Evaluates initial result := Steps initial result ∧ Value result` (353). `Core/Bidirectional.lean`
`checkAgainst` (881) is the one checker; `Core/Code.lean` `Code` is a held term the checker accepts;
`Logic/Claim.lean` `Holds`, `HoldsEq`, and the claim slot in `Logic/Obligation.lean`; the judges in
`Judge/`. Lean's own `Lean.Expr`, `Lean.Environment`, `ConstantInfo` come from `import Lean`
(acceptable in a tool module and the lowering module; keep it out of `Core`).

## Deliver, one commit each
1. **The fragment, Lean-lite** (`Obend/Lower/Fragment.lean`): a decidable predicate on `Lean.Expr`
   relative to an environment: closed terms over `Nat`, `Bool`, non-indexed, non-universe-polymorphic
   structures and inductives in `Type`, functions, `let`, the recursors `Nat.rec`, `Bool.rec`, the
   structure's `casesOn`/projections and each fragment inductive's `rec` (so structural recursion
   compiled by the elaborator to `brecOn`/`below`/`PProd` is in, after δ-unfolding through those
   definitions; well-founded recursion through `WellFounded.fix`/`Acc.rec` is out), `Nat` literals and
   the kernel's literal operations, `Decidable` eliminations (`ite`/`dite` on decidable props), and
   terms whose `Prop`-typed and `Sort`-typed subterms are erasable. State what is out and why.
2. **The source semantics** (`Obend/Lower/Semantics.lean`): a small-step reduction on fragment
   `Expr`s, rule for rule Lean4Lean's `whnf`/defeq reductions restricted to the fragment (β, δ for
   environment definitions, ι for recursors on constructors, ζ, projections, `Nat` literal operations
   and `Nat.succ` literal folding); with a note per rule citing Lean4Lean's. Do not import Lean4Lean
   this lane: assess whether it builds at Lean 4.35.0 and what adding it as a dependency would cost
   (our tree has none), and report; the connection theorem is the follow-up.
3. **The lowering** (`Obend/Lower/Lower.lean`): `lower : Env → Expr → Option Term` and
   `lowerTy : Expr → Option Ty`: proofs and types erased; structures to records (field names kept);
   inductives to labeled sums (`inject`/`case`), recursors to `fix` with `case`/`ifZero`; `Nat` to
   `nat` and the literal operations to `binary`; `Bool.rec`/`ite` to `ifBool`; `let` to `app (lam …)`.
   The erased term must check: `lower_checks`, the lowered term is accepted by `checkAgainst` at
   `lowerTy T` with reusable quantities (so `Code` and the judges apply).
4. **The theorem** (`Obend/Lower/Proofs/Sound.lean`): `lower_sound`: for a fragment term `e` of type
   `Nat` (or `Bool`, or a fragment inductive) that the source semantics reduces to a canonical form,
   `Evaluates (lower e) (lower canonical)`; by a simulation between the source steps and `Steps`
   (each source step matched by zero or more Core4 steps; erased steps are stutters, bounded by a
   measure you state). Plus `lower_value`: canonical forms lower to Core4 values. Teeth: a lowering
   that drops a recursor's minor premise, and one that maps `Nat.sub` to `add`, each refuted.
5. **The tool and the first programs** (`obend lower NAME`): a metaprogram in the `obend` executable
   that takes a declaration from the environment of a Lean file (use `Lean.Elab.runFrontend` or
   `importModules` on a small test module under `lean/tests/lower/`), checks the fragment, lowers,
   writes the Core4 term as a held `Code` and a certificate the kernel accepts (the simplest honest
   format: the lowered term plus the source's digest, judged by re-lowering; a `Judge` instance
   `lower@1`), and prints the Core4 term. First programs in `lean/tests/lower/Programs.lean`:
   `double`, `fib` (structural), a `structure Point` with a method, an `inductive Shape` with a
   `match`, and `Nat.add` itself through the kernel's literal rules; each lowered, evaluated by the
   machine, and compared with `#eval` of the Lean original in `tests/lower/run-lower.py`. Then the
   composition: `double` lowered, emitted as a Leaf book by `obend emit`, and the book's answer equal
   to the machine's (that is Lean to the Leaf book with `lower_sound` and `book_sound` composed; state
   the composed theorem `lean_to_book` for a closed fragment composition, or say exactly why it does
   not compose yet).

Report `lean/docs/REPORT-LOWER-20261101.md`: what is in the fragment and out; the rule table against
Lean4Lean; the Lean4Lean dependency assessment; what is proved; the one decision for Ember. Tier 1
green is the bar for pushing `dev` from the Mac (`--no-verify` when hbox built the identical commit);
tier 2 and every suite (cohorts, receipts, workspaces, logic, leaf, ledger, impact, lower) on hbox,
reported. Lean v4.35.0; every file a `module` (a tool module with `import Lean` may be a plain file
if the module system refuses it; say so); the census is the only axiom check; named-file commits,
`git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`,
rebase before each push; no other lane is live. No sorry, no axiom, no `Term` constructor added, no
former theorem changed. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare
word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and
only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell
me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range,
what is proved, the fragment's boundary in one paragraph, and the one decision for Ember.
