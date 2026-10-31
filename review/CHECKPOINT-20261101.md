# Checkpoint 2026-11-01, for outside review

Tag `checkpoint-20261101` on `dev` (`emberian/obend`). The 10-31 checkpoint was reviewed-for and
not yet reviewed; this one supersedes it. Everything below is committed; the tree is quiet.

## What the system is

A language with a Lean-checked core for objects anyone can extend without forking, laws judged on
every write, documents that remember why they say what they say, and a kernel that checks every
answer's evidence; built to become the symbolic core of what comes after Mathematica
(`AMBITION.md`). It is close in kind to a theorem prover: admission is re-execution of a certificate
the kernel never searched for, every refusal names what failed and where possible what would pass,
and the metatheory is mechanized (Lean 4.35, no Mathlib, about 300 modules, 3,000 theorems, a
whole-library axiom census in the build, mutation teeth that fail a theorem under a planted fault,
two build tiers with tier 2 run pre-push).

## What changed since 10-31

- The research converged (`review/GENERALIZATION-20261031.md`) and the vision was fixed
  (`AMBITION.md`, `review/VISION-CLAUDE-20261031.md`, `astra/ASTRA-VISION-20261031.md`).
- `quote` was oriented in the staging and reflection literature (`review/QUOTE-ORIENTATION-20261101.md`:
  eleven properties, each audited against Core4, sixteen theorems in lane order) and its first lane
  landed: a kernel function on held terms, `Code Ψ A θ` with a checked importer and four named
  refusals, the observer ladder `≈q ⊆ ≈r ⊆ ≈b`, `rewrite_sound_below`, mirrors; no new `Term`
  constructor (`lean/docs/REPORT-QUOTE1-20261101.md`).
- The judgment class with six instances and one foreign certificate format (LRAT from CaDiCaL,
  planted-deletion tooth) and the receipt type with a Merkle-committed view, re-checked by `obend
  verify` with no producer state (`REPORT-JUDGE-20261031.md`, `REPORT-RUNNER2-20261101.md`).
- `linear` separated from `affine` in the kernel: exactly once, branches agreeing, records consumed
  whole (`REPORT-LINEAR-20261101.md`).
- Nominal kinds, one `Intention` module with three instances, C4 linearization proved
  (`REPORT-KINDS-20261101.md`).
- Clairvoyant cost: `mix_assoc` within a factor of 8, the improvement judge, and a negative result
  against Hackett–Hutton for self-reading lazy fields (`REPORT-COST-20261101.md`).
- The ledger as a fold member, consensus time, durable commit with `exposed_once` across crashes,
  fork and stitch (`REPORT-RUNNER2-20261101.md`).
- The decisions and who took them: `review/DECISIONS-20261031.md`; the plan and its gates:
  `PLAN.md`; the four decisions pending are at its end.

## Read in this order

1. `AMBITION.md`, `README.md`, `THESIS.md`, `DESIGN.md`, `METATHEORY.md`, `PLAN.md`.
2. `review/DECISIONS-20261031.md`, `review/GENERALIZATION-20261031.md`, `review/QUOTE-ORIENTATION-20261101.md`.
3. The lane reports `lean/docs/REPORT-*.md`, each with decisions, critique and what is not proved.
4. The Lean under `lean/Obend/` where a claim needs checking.

## What to critique

- **The kernel's shape**: `quote` as a kernel function with no constructor; the ladder; mirrors.
  Is the promotion criterion (§3.7 of the orientation) right, and is "no program-level quote on
  values" the correct refusal for a lazy heap?
- **The judgment class and receipt**: is a `Judge` with `sound`/`complete`-on-a-fragment/`mono`
  the right abstraction for solver diversity, and is the receipt's `checked | attested` dial honest
  about what a stranger learns?
- **The slot, runner and ledger**: `refines`, `joint_reachable_ticket_exclusive`, `exposed_once`.
  Is the `World` law set (pins, retirement, versions with a collision stance) the right abstraction
  of a history? What does the shared layer still assume that a real network would not grant?
- **Quantities**: exactly-once `linear` with syntactic counting; branches by agreement; records
  consumed whole. Where is this unsound or too strict?
- **Cost**: is the clairvoyant cell table (pending decision) the right repair to Hackett–Hutton for
  objects, or is there a known semantics we should take instead?
- **Design bloat**: the laws, classes and reasoning principles (`Fold`, `Judge`, `Decides`,
  `Calculus`, `Graded`, `Integrity`'s floors, the selection presets, `Just`). Which earn their keep by
  reuse, which are premature, which should go?
- **The design phase**: what would a theorem prover's author insist on before building further?
