# Two focused experiments for Gemini (2026-11-01)

Each is a question with a refutable answer, not a review. Repo `emberian/obend`, branch `dev`.

## Experiment 1: does world resolution admit a monotone reading?

Context. A slot (`lean/Obend/Slot.lean`) holds candidates, each with supports (facts about cells at
pins) and a judge; `Slot.read`/`usable`/`alternatives` read it at a view. Stored selection
(`Slot/Selection.lean`, `Slot/Integrity.lean`: `incumbentTransition`) and the per-slot descriptor
with three presets, first-usable, incumbent-first, chooser-required (`Run/Control.lean`), decide
which usable candidate is chosen; `astra/ASTRA-SELECTION-20261031.md` §7 states the policy-independent
invariants. Claude's conjecture (`review/WORLD-ANALYSIS-20261101.md` and the conversation after it):
a cell's knowledge can be represented as a set of supports rather than a pin, a world with
unresolved cells is a constraint store, and resolution might be a closure operator in the
information order, so that the slot's resolution and a term's `fix` share a semantics and not only a
representation. Claude already suspects the second half is false because resolution is policy-bound.

Question. Define the information order on support sets (more supports known, or more supports
holding, is higher). For each preset, state resolution as a function of the store and the stored
choice. Prove or refute: (a) monotonicity: adding a holding support never un-selects a selected
candidate; (b) incumbent-first is a closure operator (extensive, idempotent, monotone) on stores;
(c) first-usable is monotone but not a closure; (d) whether the policy-independent invariants
(`Authorized`, `OnceSpent ∧ Paired ∧ ReplansUnentered ∧ Kept`) are exactly the monotone part. A
refutation with a concrete countermodel (four cells is probably enough; the early/chosen
countermodel in Astra's evaluation §19–27 is a start) settles whether "shared representation" can
become "shared semantics". Write it as Lean statements over the existing definitions where
possible, with the countermodel as a `decide`.

## Experiment 2: does the iterated-approximant `fixLet` compute what the machine computes?

Context. `lean/Obend/Equiv/Clairvoyant.lean` is Hackett–Hutton's clairvoyant call-by-value for
Core4; `lean/docs/REPORT-COST-20261101.md` and `Core/Proofs/TickCost.lean` prove that
`{a = 7, b = self.a}.b` evaluates to 7 on the machine in 24 ticks (`Core/Machine.lean`) but has no
clairvoyant derivation (`self_field_no_cv`), and `ticks_not_within_cv`. Gemini's own diagnosis
(`review/GEMINI-CHECKPOINT-20261101.md` §5.1): `fixLet` settles `selfBody` before substituting the
knot, so `self` is `.bound 0` when `b` is forced; repair by iterated approximants (`V₀ = skipped`,
`Vₘ₊₁` from running `selfBody` against `Vₘ`, paying for each field once) or by a Launchbury-style
local thunk environment.

Question. Write the approximant semantics in Lean beside the existing `Run` (new file, no edits to
`Clairvoyant.lean`'s existing definitions), and prove: (a) `{a = 7, b = self.a}.b` has a derivation,
and its cost (the report's prediction is 5); (b) the approximant sequence is monotone in the
`skipped`-order and stabilizes for any finite self-reading record; (c) `mix_assoc_cost`'s factor is
unchanged (or state the new one); (d) the relation to the machine: for the three measured programs
(`.good` 16 ticks, `.b` 24 ticks, `.bad` blackhole at 21), ticks are within a stated constant of the
approximant cost, or name the program where approximation and the heap diverge and why. If (b) or
(d) fails, say which construction (approximants or local thunk environment) survives, and what
Hackett–Hutton's Theorem 4.1 needs added to cover self-reading lazy fields.

Reply as a file Claude can read, with every claim tagged proved, refuted, or conjectured, and the
Lean in fenced blocks against the real signatures.
