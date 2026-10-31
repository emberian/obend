# REPORT 2026-10-31: what the Law lane left owed

Lane LawFinish (Claude Opus), from `LANE-LAWFINISH-BRIEF-20261031.md`. I worked in my own worktree,
rebased on `origin/dev` before each push, and committed named files. Tags: **MEASURED** means a
command was run and its output read; **READ** means a file was opened; **INFERRED** is my reasoning.

## 1. What landed

| commit | what |
|---|---|
| `b8860b9` | `Core/Proofs/GroundExecution` (new), `Law/Machine`, `Law/Proofs/Machine`, `Run/LawJudge`, teeth leaves `Law/Proofs/{MachineTeeth,LawJudgeTeeth}`, Census entries |
| `643d792` | `Law/Inherit`, `Law/Proofs/Inherit`: validated precedence, `c3_tree_is_chain`, monotonicity and local precedence |
| `70de3d6` | `Law/Proofs/Typing`: `keeps` typed, plus a law in an outer context |
| `5c5d684` | `Law/Std`, `Law/Proofs/{Std,Eval,Typing,TypingTeeth}`: `eqAt` on records; `windowed`/`quorum` beyond scalars |
| (this) | this report |

**MEASURED:** `LEAN_NUM_THREADS=2 lake build` green after each rebase (233 jobs at the last one). The
census reports no `sorryAx` and no declared axiom, and the compiled-trust count is unchanged at 27.
`python3 tests/run-obend-source.py` gives probes 30/30, tutorial 71/71, and the preview cohort at
161 items with 0 failures; the one stale pin it holds (`Structured-neverFinishing-no-partial-value`)
belongs to the cohort. Every `#tooth` reports a rejected stored proof. I added no `#assert_axioms`.

## 2. The machine judges what the relation says (item 1)

A verdict is a sum, and the machine reads ground values out. A kernel therefore runs a probe:

    case (law old new req) [ok ↦ true, refused r ↦ asLabel r]

Here `asLabel r = ifBool (labelEqual r r) r r` is `r` when `r` is a label, and it is stuck
otherwise, so `true` and a reason cannot be confused. `judge` executes the probe with the kernel's
own `executeWith` and reads `true` as `ok` and a label as `refused why`.

- **Core (new file, `Core/Proofs/GroundExecution`).** `execute_ground_complete`: a closed term that
  evaluates to a ground observation has limits and a tick count past which `execute` succeeds with
  that observation. This holds at every limit covering them, with more ticks, one node and
  `groundBytes` bytes. The proof is `runBounded_finite_completion` plus `runBounded_finished_mono`
  (new: more room and more ticks never change a finished run) plus the extraction arithmetic.
  `execution_ground_iff`: under every policy, a successful execution extracts the observation exactly
  when the term evaluates to it. This file imports `Adequacy`/`Completeness` with `import all` and
  edits nothing there.
- **Law.** `Judged law o n rq : Verdict → Prop` means `Admits` for `ok`, and for `refused why` it
  means `RefusesAs` (the law refuses with a reason that evaluates to `why`; `Refuses`, a literal
  reason, is a case of it by `refuses_refusesAs`).
  - `judge_sound`: under every policy, limits and budget, a verdict the machine returns is `Judged`.
  - `judge_complete`: past a threshold, the unrestricted `judge` returns the `Judged` verdict.
  - `judged_unique`: the relation gives at most one verdict.
  - `machine_judges` bundles the three.
- **Effective laws.** `judgeEffective` runs a `by` probe and a `reason` probe.
  - `judgeEffective_names`: a machine `refusedBy name why` means `name` is on the precedence list,
    every law before it admitted, and its own law refused with `why`. A machine `ok` means every
    law on the list admitted.
  - `judgeEffective_complete` is the converse, at sufficient resources.
  - `effective_scoped`: the effective law of closed laws is closed.
- **Teeth (legacy leaf `MachineTeeth`).** The machine runs `bounded` (an admit and a refusal) and
  `boardLaws` (`ok`, `refusedBy room`, `refusedBy board`), and each result is read back through
  the general theorems. The `#tooth` mutations are a reader that maps a refusal to `ok`, and a
  `judgeEffective` that names the wrong ancestor.

**Restructuring.** The brief allowed extending adequacy to sums of records. I did not prove deep
completeness of `materializeWith`, which re-enters field cells from a settled heap. The probe makes
the verdict ground, so ground completeness is enough. The cost is that an effective law's refusal
is read in two runs, one per field.

## 3. Linearization facts (item 2)

`precedence` now validates C4's list with `precedenceOk`. The list must start at the head, have no
repeats, keep every local chain in order, and keep every parent's precedence list in order. A list
that fails is refused as `unordered`. Theorems in `Law/Proofs/Inherit`:

- `precedence_ok`, `precedence_monotone`, `precedence_local` (Barrett et al. 1996, stated over the
  produced list).
- `c3_tree_is_chain`, **proved of `Spec.C4.linearize` itself**: on a tree, the linearization of `x`
  with its one parent is the chain to the root.
- `precedence_tree`: the validation never refuses an acyclic tree. `effectiveVia_tree`: on a tree,
  the effective law is the conjunction along the chain.
- `effectiveVia_parent`: what a child's effective law admits, every law on every parent's
  precedence list admits. `child_never_widens`: likewise for a parent's effective law, at a parent
  where the graph is coherent.
- Teeth: a three-level tree; an incoherent oracle refused as `unordered`; `#tooth` on the
  validation.

The former statements are unchanged: `effectiveVia_eval` and `c4_tooth` hold as before.

## 4. Typing (item 3)

- **`keeps`.** An unannotated closed lambda does not synthesize, so the algorithmic checker refuses
  `keeps S I`. `Teeth.keeps_unannotated_refused` shows this, by `decide`.
  - `keepsOpen S` (the invariant as a variable of `S → boolean`) is checked by the checker itself:
    `keepsOpen_checked`, through the new `lawOf6_chk_in` (a law in an outer context) and `chk_app`.
  - `keeps_typed`: for every closed `I` checked at `S → boolean`, with any annotations of its own,
    `keeps S I` has a declarative derivation (`Typed`, i.e. `PartialTyping`) at `lawTy S`. The proof
    is `checked_msubst` followed by closed transport. `ChecksAt.typed`: what the checker accepts is
    `Typed`.
- **Generators beyond scalars.** `eqAt` at a record type is now a field-by-field conjunction.
  - `EqTy` (a scalar, or a record of `EqTy` fields) replaces `Scalar` in `windowed_checks`,
    `quorum_checks`, `windowed_ok_checks` and `quorum_ok_checks`. Each former statement is the
    instance at `EqTy.scalar`.
  - Meaning: `eqAt_data` says that `true` on data that fits the type (`EqFits`: exactly the row's
    labels, in order, each field fitting) means the data are equal.
  - `quorum_change_needs_k` gains `FieldEqFits` hypotheses. These are `.inl rfl` at every
    non-record type, so the former theorem is their instance there.
  - At a record type the former law compared records with `equal` and was ill-typed, so no former
    theorem about a well-typed law is lost.
  - Teeth: a quorum and a rate limit guarding a record field are typed. A record-guarded quorum is
    run: commit with and without quorum, a wrong pair, and an equal pair. `eqAt` on data with an
    unnamed extra field compares equal, which is why `EqFits` is a hypothesis. A `#tooth` uses the
    scalar-only `eqAt`.
  - Not done: sums (`variant`) still compare by `equal`.

## 5. Laws reach the runner (item 4, `Run/LawJudge`)

Nothing in the runner changes. The law enters as facts. A `LawJudge` embeds `LawFact.admitted o`
and `LawFact.clause o name` in the deployment's fact type, says which write an operation performs at
a world (`act`), and gives the object's resolved precedence list (`lin`). `lawHost` decides those
facts by running `judgeEffective` at the world. `lawSpec` adds, to each operation's requirements,
`admitted o` and one `clause o name` per ancestor. So `run`, `Legal` and `reachable_legal` apply
unchanged.

- `legal_law_admitted` / `reachable_law_admitted`: in every `Legal` log of the law-judged runner,
  every dispatched operation that performs a write was admitted, at its dispatch world, by every law
  on the precedence list and by the effective law, over `Evaluates`.
- `legal_base_authorized`: when its requirements are not law facts, the deployment's own `Authorized`
  still holds.
- `dispatch_refused_names`: when the machine refuses by `name` with `why`, the runner refuses the
  dispatch as `unadmitted`, `clause o name` is among the missing facts, and the named law refused
  with `why` after every earlier law admitted. `run_dispatch_log` is a helper lemma.
- Teeth (legacy leaf `LawJudgeTeeth`): an object guarded by `boardLaws`. Writing 9 is refused with
  missing facts `[admitted, clause room]`. Eve's write is refused naming `board`. Ann's write of 3
  is accepted, and through `reachable_law_admitted` every board law admitted it. `#tooth` with
  `lawRequires := []`.

I coordinated with SlotRun only through `origin/dev`. Its `Run.Adapter` landed while I worked, and
I touched no file of it.

## 6. Decisions taken

- **D1. A verdict is read by a probe**, not by deep extraction. *Critique:* an effective law costs two
  runs, and a kernel must run the probe rather than the bare law. *Meta-critique:* the probe is a
  closed Core4 term the kernel builds once. It needs no change to the machine, and the theorems
  cover any policy.
- **D2. Operations that write nothing are not judged** (`act = none` gives `ok`). The deployment
  declares which operations write. A wrong `act` exempts an operation, and nothing here can check
  the declaration.
- **D3. Two inherited names were made public** (`scopedB_sound`, `boardLaws_closed`), as was
  `fieldsTerm_find`. All three are Law files.

## 7. The one decision for Ember

**Is a validated C4 linearization acceptable for laws, or must `linearize` be proved?** C4's
`linearize` has no theorem. It is an imperative merge over hash maps in `Obend/Spec`, which the
Extends lane owns. I proved the tree case of `linearize` itself (`c3_tree_is_chain`). For DAGs I
did not prove it: `precedence` checks the output for monotonicity and local precedence, and refuses
a list that fails as `unordered`. Every inheritance theorem is therefore true of the list the
effective law is built from.

- (a) Keep the validation. It is cheap, and it never fires on trees (proved) or on the 4000 seeded
  DAGs and pommette vectors, where `C4Vectors.checkDag` checks the same properties of `linearize`.
  The cost: a C4 bug would surface as a refused law, not as a wrong one.
- (b) Commission a proof of the merge. That means rewriting `linearize` into a structurally
  recursive form in `Obend/Spec`, a lane of its own after Extends.

I recommend (a) now and (b) when Spec is free.
