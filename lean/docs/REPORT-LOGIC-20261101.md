# Report: lane Logic (2026-11-01)

Brief: `lean/docs/LANE-LOGIC-BRIEF-20261101.md`; design: `review/PROGRAM-LOGIC-20261101.md` §5, with
Gemini's checkpoint review `review/GEMINI-CHECKPOINT-20261101b.md` §1 absorbed before the first commit.

## What landed

| item | where | state |
|---|---|---|
| (1) the judgment, the lowered shapes, T1 | `Obend/Logic/{Claim,LateBinding}.lean` | proved; tooth (`Teeth/Logic/LateBindingTeeth`) |
| (2) derivations, the checker, T2 | `Obend/Logic/Rewrite.lean` | proved; planted derivation refused `stepMismatch [0]` |
| (3) the ground judge | `Obend/Logic/Ground.lean` | proved; refutes on `false` |
| (4) the claim judge, T3 | `Obend/Logic/Frame.lean` | proved; teeth (`Teeth/Logic/FrameTeeth`, `GroundTeeth`) |
| (5) slot, status, format, receipts, CLI, surface | `Obend/Logic/{Obligation,Program,Receipt}.lean`, `Main`, `Receipt/Cli`, `Spec/{Parse,Syntax}` | done, with the limits below |
| (6) ReviewMember end to end | `tests/run-logic.py`, `tests/logic/ReviewMember.Twice.repeated.json` | 20/20 |
| (7) T4 `caseSplit`, `Logic/Turn.lean` | — | not started |

**T1 `late_binding`** (`LateBinding.lean`): in `fix(compose …){seed}`, `O.m` reduces to the body of the
last layer providing `m` with `self := O`, `super := superAt j`. Both layer shapes Elaborate emits are
covered (`extend super {defs}`, and the flat delegating record over a recursive record target, which
hides the row beneath it from `providesLast`; its `super.f` entries are chased by `unfoldIn`). The
composition is `specification (composed{…}) (mix l u)` as of `1e039ff`, with the step metadata carried
per layer. The right-hand side is one parallel substitution (`open_sequential`,
`late_binding_parallel`); no closedness hypothesis. `late_binding_at` is the suffix form (the late
binding of `super.m` at a prefix). `object_bequiv_of_operands`: the program's own `fix`, whose operands
are knot references, is `≈b` the decoded composition's object.

**T2 `rewrite_sound`** (`Rewrite.lean`): an accepted derivation (`run`, `lateBinding`, `assoc`,
`composeAssoc`, `congr` with the census check, `trans`) gives `l ≈[b] r`; without `composeAssoc` it
gives full `≈b` (`rewrite_sound_r`). Proved once, generic in the resolver, at every observer-free
substitution (`replay_sound`). `holdsEq_of_rewrite` replaces `holds_equal_of_rewrite`.

**T3 `claim_frame`** (`Frame.lean`): a claim's derivation is replayed with `self` and `super` as the
variables they are in the claim's body; `lateBinding` at `self.m` asks the composition what its last
provider gives, with `self` still the variable. `replay_frame` shows the check reads the composition
only at the derivation's members, so an accepted derivation is accepted unchanged for every
well-formed composition (any layer index for the claim) that unfolds those members to the same
provider and body. In slot form, `usable_checks`: a usable read at a view is an accepted check there.

## The two judgments (Gemini §1, option A)

`Holds c d⃗ := Evaluates (c d⃗) true` is total: ground runs (`ground_sound`) and Lean proofs establish
it. A rewrite certificate establishes only `HoldsEq l r := ∀ o, Halts l o ↔ Halts r o` of the claim's
two sides at every instance (`claim_sound`); `claim_holds` turns that into `Holds` given a ground
observation of the left side, which no certificate of that regime manufactures. The receipt names
both: `judgment HoldsEq, regime semidecidable, shape forAll` for the certificate, and
`judgment Holds, regime decidable, shape existsRun` for each ground row. `equationSides` recognizes
the three `==` lowerings (Nat `equal`, String `labelEqual`, the Bool β-redex with the `$right` shift).

## ReviewMember (§5.4), on the elaborator's own output

`obend prove --package P ReviewMember.Twice.repeated --object twiceOfThree --out R` reads the claim's
code off the knot (`$globals` substituted by the reduction), reaches the object
`fix(compose(ReviewBase.Base, ReviewMember.Twice, ReviewMember.Augmented), seed)` from `twiceOfThree`,
runs ground 0, 3, 41 (true), and installs `[congr (□ value) self.twice [lateBinding twice
ReviewMember.Twice], run 1]` (3 steps counted with nesting) with support `twice ↦ ReviewMember.Twice`;
`review` is never unfolded. `obend verify R` re-checks it with no producer state. The three teeth, red
under their mutations (`tests/run-logic.py`, and in the kernel in `Teeth/Logic/*`):

1. ground: `twiceOfThree() == 7` holds; with Augmented at `+ 2n` it is refuted, while `repeated` stays
   certified (it is about open recursion);
2. frame: with `Override` composed last, the recorded certificate reads `blocked` naming `twice`
   (`status_blocked_exact`), `repeated` is refuted at 3 (`3 == 7`), and `twiceOfThree() == 7` is
   refuted;
3. statement: a statement with a wrong address is refused `malformed` by the format's decoder
   before any step runs; a certificate naming another claim's address `statementMismatch`; late
   binding through Augmented `stepMismatch`; a relabelled support is refused.

## Decisions and limits

- **Accepted design: `super` is inert in a claim.** A claim cannot unfold `super.m`; it would need its
  own late-binding step with the layers beneath as support (`late_binding_at` is the lemma for it).
- **`given`** lowers to `if COND then BODY else true` in Parse/Syntax (no new elaboration). Such a
  claim is not an `==` at the head, so the rewriter does not certify it (status `unchecked`); the
  ground judge runs it.
- **`keeps INV by LAW`** is parsed and decoded (`Module.keeps`, names checked) and listed by
  `check --obligations` as `unchecked`. The certifying-shape check (`Law.checkClaim`) needs the law
  compiled at the object's state type, which the installing kernel holds; it is not run here.
- **SpecMeta.claims** keeps the elaboration-time label `unchecked`, which is the slot's read with no
  candidate; the live status is `check --obligations` over a receipts directory. Changing the label in
  Elaborate is the OneChecker lane's file.
- **`obend check`** is unchanged; the obligations listing is `check --obligations`, so the cohorts'
  `check` output is untouched.
- **Trust** of a re-check is `compiled` (`obend verify` runs the kernel-proved checker as compiled
  code); the teeth run the same checkers by `decide +kernel`. To keep them kernel-reducible the
  checkers use `Law.termEq` and their own fuel-monotone ground run (`run_mono`) rather than
  `Judge.Cost.termBeq` / `Judge.deepen`, whose bodies are not exposed.
- **`#tooth` for T3** is not available: a recursive proof's structural helper is a definition, which
  `#tooth` does not credit. T3's teeth are the concrete frame refusals and the slot's `blocked` read.
- The ground judge runs the reference stepper, not the demand machine; it is the law probe's twin in
  shape (grade, refusal refutes), not in engine.

## Control

Cohorts (`tests/run-obend-source.py`): probes 30/30, tutorial 71/71, preview 161 with 0 failures (the one
stale pin as before). Receipts 32/32, workspaces 30/30, walkthrough 26/26, `tests/run-logic.py` 20/20.
Census: none on `sorryAx` or a declared axiom. Nothing under `Core/`, `Equiv/`, `Law/`,
`Judge/Class.lean` touched. Measurement: start `lake build` 3m11s (stale tree after the pull); end, a
comment edit to `Logic/LateBinding.lean` rebuilds that module alone (1.1s; nothing downstream).
