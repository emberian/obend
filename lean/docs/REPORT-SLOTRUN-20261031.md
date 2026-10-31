# Lane SlotRun: the slot's open items and the runner's (Claude Opus, 2026-10-31)

Placed by the root session from the lane's closing report. Commits `622e20a` (items 1–2),
`bf0eba4` (item 3), `2895c8d` (item 4); full build 235 jobs, census clean, cohorts unchanged.

## 1. Version non-return law (`Slot/World.lean`)
`World` gains a version state per cell (`Ver`, `ver`), a strict order `Past`, the pin as a reading of
the version (`pinOf`, `pin_ver`), and `ver_step` (a step keeps a version or moves it strictly
forward). Collision stance: `Collides c a b`, two version states that differ but read as the same
pin (nano's `CollidesAmong` over concrete inputs); under `Exact` (injective `pinOf`) it vanishes.
Theorems: `ver_behind_forever`, `stale_behind_forever` (+ `_exact`), `stale_dead_forever` (dead
behind forever from the version law, no retirement special case), `stale_blocked_forever`.
Retirement stays its own law; every prior theorem kept. Tooth: `World.Returning`, a pin that
alternates, lawful only through the collision (`pin_returns`); `collision_needed` shows the law is
false without the disjunct; `no_exact_order` shows no exact version order exists for it.
Instances made lawful: `toyWorld` (exact), `pinWorld` (views carry version and value), the
negotiation world (a clock, so a restored grant is a new version; receipts unchanged).

## 2. Names
`slot_repair` split into `read_usable_supports`, `read_blocked_exact`, `permanent_blocked_forever`,
`read_of_usable`, each with a tooth; the old name a deprecated conjunction. `Integrity.transition`
is `Integrity.incumbentTransition`; old name a deprecated alias.

## 3. Runner authority (`Run/Control.lean`, `Run/Proofs/Control.lean`, `Run/ControlExample.lean`)
A layer over `run`. Per-slot descriptor: chooser office per principal (a host fact), preset, the
admitted domain in preference order with a version, override rights, tenure, suspension. A choice
needs an authenticated principal holding the office now, the slot's current revision, a permitted
and usable candidate, and override rights if it supersedes a still-usable choice; raw replans of a
controlled hole are refused. `whileInOffice` choices cite the office so the dispatch guard voids
them when the chooser leaves; `lasting` survives. Preset laws: `firstUsable_law`,
`incumbentFirst_law`, `chooserRequired_law`; `nothingAdmissible_iff` for every preset with exact
per-candidate diagnostics; reapproval latches. Of every controlled run: `creachable_reachable`,
`creachable_legal`, `creachable_authorized` (of the decision log alone), `creachable_revisions`,
`creachable_cites`, `office_rechecked`. Fixtures checked by `rfl` against `bare_accepts`.

## 4. Adapter (`Run/Adapter.lean`, `Run/Proofs/Adapter.lean`)
| gap | adapter | `Legal` clause | fixture |
|---|---|---|---|
| response typing | a nonconforming reply refused `illTyped` | `ResponsesTyped` | `typed_receipt` |
| depth stop | `deepen` re-bases deeper, replaying the log | log `Legal` for the deeper activity | `deepen_receipt` |
| ticks exhausted | `moreTicks` re-bases with more ticks per turn | log `Legal` at the new bound | `ticks_receipt` |
| no choice points | a yielded choice Plan is a frontier; `choose`/`chooseBy` picks, citations rechecked at dispatch | `ChoicesHeld` | `choice_receipt` |
Proved: `areachable_inv`/`areachable_legal`; `plain_trace` (without choice points every adapter run
is a machine run). Not proved: that a re-base is never refused (checked when made, refused `replay n`
on failure; needs a simulation over activities agreeing along the history). Choice points are
adapter-level slots, not runner holes (`subst` does not fill holes inside a filling). `#tooth` cannot
attach to `creachable_authorized` and `areachable_inv` (compiler-generated match splitter, as the Elab
report records); fixture teeth stand in.

## Decision (taken by Claude under standing approval)
Selection control is mandatory for every runner hole: the bare `chooseEvent`/`resolveEvent` entry
points retire, every decision is authenticated, revisioned and tenured. Reversal: one refusal in
`crun` and the negotiation fixtures back off descriptors.

## Follow-up (commits `f10d1e7`, `ccb6501`, `c32af5d`; 241 jobs green, 110 teeth, cohorts unchanged)

**Mandatory control.** Every hole has a slot, a descriptor and candidate bodies; every raw replan is
refused; `resolveEvent`, `resolveEventBy`, `chooseEvent` retired (`advance_installs`,
`incumbentFirst_law`, `choose_accepted` replace their theorems); `clost_reply_frozen` is the
lost-reply theorem over controlled events; the negotiation fixtures run on a descriptor.

**The audited fold** (`Obend/Fold.lean`): `Admission` with laws `keeps_world`, `step_of_reads`,
`observe_ok`; proved once: `receipt_sufficient`, `step_of_pins`, `Family.step` (interleaved members
sharing the world component), `project_run` (each member's own fold, under a per-row rely–guarantee
condition). Instances: `Legal` (`Run/Fold.lean`: `legal_iff_fold` both ways; `DecisionsHeld` is
per-row through the accumulator's `entered`) and the law judge (`Law/Fold.lean`, world `Unit`,
rows read nothing).

**The shared-World layer** (`Run/Shared.lean`): `Ledger` is the authoritative record with commit
laws as fields (consumption and grant recorded atomically; raw-world moves leave both); any number
of runners share it; dispatch syncs the runner's view to the ledger, lets the runner judge, commits,
propagates to every runner, then exposes. Proved: `joint_reachable_projects_legal`,
`joint_reachable_ticket_exclusive`, `joint_once` (global `OnceSpent`), `joint_coupled`,
`loser_refused_names_winner_and_epoch`. First instance: two buyers over one capability
(`local_legal_does_not_imply_global_once`, `alice_wins`, `bob_wins`, `lost_reply_receipt` with a
revived live flag and an abandonment). The three mutation teeth bite at fixtures: shared mask
removed gives a second grant; abandonment erasing consumption is rejected; omitted propagation is
rejected. The pass criterion held: once-spending is derived, not assumed; the wrapper instantiates
the runner; dispatch views are the shared view.

**Not covered.** Projection comes from each runner's own reachability, not from `project_run`
applied (the ledger's commit is the wrapper's update, not a member row; making the ledger a fold
member is designed, not done). Durability is a separate law (`Ledger.Durable`) rather than a
structure field, so that an erasing ledger can be stated as a tooth. All runners share one
signature. A token's liveness is the host's reading, not a pin. `#tooth` cannot attach to the
general theorems (compiler-generated match splitters); teeth sit at fixtures. No durable-commit or
network refinement. A re-base is still not proved never refused.
