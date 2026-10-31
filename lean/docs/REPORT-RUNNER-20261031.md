# REPORT 2026-10-31 — the guarded runner: admission-preserving replanning across revocation and lost replies

Lane RUNNER (Claude Opus), on `lean/docs/LANE-RUNNER-BRIEF-20261031.md`, building the contribution
theorem Astra named (`astra/ASTRA-EVAL-20261031.md` lines 97–111). Worked in a worktree of
`origin/dev` at `d37888a`. Tags as in the trees: **MEASURED** (a command run here, output read),
**PROVED** (a Lean theorem, checked, with its `#assert_axioms` pin), **READ**, **INFERRED**.

## 1. What landed

| file | what |
|---|---|
| `Obend/Run/Runner.lean` | `Host` (a world's decided step and view; `Host.ofWorld` from a `World`), `Event` (raw proposals: `world`, `replan`, `dispatch`, `respond`), `Refusal` (named), `Cfg` (open object, world, durable spent tokens, residual, log), `run`, `Reachable`, `session`, `drive` (handler-driven), `resolveEvent` (replan by a `Slot`). The guards are named definitions: `dispatchGuard`, `spendOn`, `frozenHole`, `awaiting`. |
| `Obend/Run/Spec.lean` | `Legal`: the declarative specification of an accepted log, stated of the log alone (§2). |
| `Obend/Run/Proofs/Invariant.lean` | `refines`, `reachable_legal`, `step_inv`; the continuation clauses; `run_replan_guard`; `entered_iff` (the executable guard is exactly `Dispatched`). |
| `Obend/Run/Proofs/Interpret.lean` | `drive_sound`, `drive_complete`, `resolveEvent_ok`. |
| `Obend/Run/Negotiation.lean` | the stranger's example, the fixture of Astra's line 105, the reservation retry, the durable-spending ticket, instances of the general theorems. |
| `Obend/Run.lean` | the root. |
| `Obend/Slot/Selection.lean` | `SelectionSound` and its policy laws (§8). |
| `Obend/Run/Core4.lean`, `Obend/Run/Proofs/Core4.lean`, `Obend/Run/Core4Example.lean` | the Core4 adapter (§9). |
| `Obend/Slot/Proofs/{Protocol,Negotiation}.lean` | `resubst_preserves_started` and `instantiations_hasProt` made `public` (the module discipline: public iff another module cites it). No statement or proof changed. |

**MEASURED:** `LEAN_NUM_THREADS=2 lake build` 183 jobs green (first pass); 190 jobs green after the
second (§7–9). No `sorry`, no axiom; every headline
theorem carries `#assert_axioms` (standard three only). Nothing in `Obend/Slot/Protocol.lean` changed:
`interpret`, `admitOp`, `commit`, `Open`, `Replan` are used as they are.

## 2. The theorem

**The transition system (READ: `Runner.lean`).** `run host sp c ev` takes a raw event and returns a
configuration or a refusal:

- `world v'`: accepted iff `host.allowed c.world v'`. Only the world moves. The spent state is the
  runner's, so a world that calls a spent token live again does not unspend it.
- `replan h f`: refused `notMine` unless `h` is a `.me` hole; refused `replacesInflight o h` (a call in
  flight) or `replacesAnswered h` when the history has entered `h` (`frozenHole`, the executable
  `Dispatched`); otherwise the plan becomes `setHole σ h f` and the residual is recomputed along the
  answered history (`advance`). The step is refused `inconsistent` when the new plan does not have
  that history. That cannot happen at a reachable configuration (`replan_accepted`).
- `dispatch o`: refused `busy` while a call is in flight (`awaiting`), and `notNext` unless `o` is the
  residual's next call. It is refused `unadmitted o missing dead` unless `admitOp` holds at the view
  current now: the host's view with every durably spent token dead (`Cfg.admitView`). The refusal
  names the facts that do not hold and the token that is not live. On acceptance the token is spent
  and the call is recorded in flight, in the same step that exposes it.
- `respond e`: accepted only when `e` answers the call in flight (`unsolicited` otherwise); the
  residual follows the reply.

**The specification (READ: `Spec.lean`), independent of `run` and of `Cfg`.** Positions of the log
(`AtEach`), with the world, spent tokens, history and plan at each position recomputed from the
prefix (`worldOf`, `spentBy`, `histOf`, `planOf`):
`WorldSteps` (every world event a step the host takes), `Authorized` (every dispatched call admitted
by `admitOp` at the view of its own dispatch), `OnceSpent` (`(spentBy sp log).Nodup`), `Paired`
(dispatch only with nothing in flight; a reply only to the call in flight), `ReplansUnentered` (no
replan touched a hole `Dispatched` at the time), `Kept` (`Started` of the plan in force).
`Legal` is their conjunction.

**PROVED, `Invariant.lean`.**

- `refines : Reachable host sp (Cfg.init O v₀) c → Inv host sp O v₀ c`, by induction on reachability.
  `Inv` is the five log clauses plus representation: `c.obj = {O with σ := planOf O.σ c.log, hist :=
  histOf c.log}`, `c.world = worldOf v₀ c.log`, `c.spent = spentBy sp c.log`,
  `Reach c.obj.current c.obj.hist.answered c.res`, and the call in flight is `IsCall c.res`. The
  induction step `step_inv` holds for ANY event the runner accepts. Nothing beyond acceptance is
  assumed of an update, and the world step is any `host.allowed` step.
- `reachable_legal`: every reachable log is `Legal`.
- Before dispatch, `replan_accepted`: at every reachable configuration, a replan of a `.me` hole the
  history has not entered is accepted, whatever the filling, with a call in flight or not. Its proof is
  `resubst_preserves_started` with `entered_iff`. `replace_then_dispatch`: if, in addition, nothing is
  in flight and the replanned protocol's next call is admitted now, that call's dispatch is accepted.
- After dispatch: `inflight_busy` (every dispatch refused, naming the call in flight),
  `inflight_replan_refused` (the entered hole's replan refused `replacesInflight`, by name),
  `answered_replan_refused`. `lost_reply_frozen`: from a reachable configuration with a call in
  flight, ANY list of events containing no reply (world moves, replans, proposed dispatches) leaves
  the history, the spent tokens and the log's dispatches unchanged, and the call in flight remains
  the residual's next call.
- `run_replan_guard`: an accepted replan satisfies the existing guard `Open.Replan` and keeps the
  history. The runner's guard and the library's guard are the same guard.

**PROVED, `Interpret.lean`: the reference handler is an instance.** `drive_sound`: whatever a
driven run delivers, `interpret` delivers from the same residual and state. `drive_complete`: on a
protocol judged by `HasProt` at `Γ`, `Δ` (`Δ.Nodup`), at a world where `Γ` holds and `Δ` is live and
unspent, some fuel makes the driven run deliver exactly `interpret`'s result. `resolveEvent_ok`: a
slot-resolved replan installs the body of the first usable candidate (`Slot.resolve_ok`).

## 3. The countermodel teeth (MEASURED: each `#tooth` reports its stored proof rejected)

| mutation | rejected at | what it would mean |
|---|---|---|
| `dispatchGuard := true` | `step_inv` (in `inv_dispatch`); `withdrawn_refused` | Astra's line-105 fixture is delivered unauthorized |
| `spendOn := spent` | `step_inv` (in `inv_dispatch`); `Ticket.second_use_refused`; `stayed` | the ticket the world calls live is used twice |
| `frozenHole := none` | `step_inv` (in `inv_replan`); `receipt` | the replan with the same first call (`planFlip p2`) is ACCEPTED while its call is in flight; cancelling and returning to `p1` become `inconsistent` instead of being refused by name (MEASURED by a probe outside the tree: `(false, false, true)`) |
| `awaiting := none` | `inflight_busy`; `reserve_retry_refused` | a reservation whose reply is missing is dispatched again (it needs no fact and no token, so admission alone lets it through) |
| `nextIs := false` | `replan_accepted` | the safe replacement is refused |
| `dispatchGuard := false` | `replace_then_dispatch`, `drive_complete` | the admitted replacement cannot take its step |

The mutated proofs are rejected in the lemma that uses each guard, not at an unfolding equation.
The proofs unfold the guards by `show`, not `rw [f]`. A tooth credited at `f.eq_1` would say only
that the definition changed. `refines` and `reachable_legal` cannot take a tooth themselves:
`Reachable` is an inductive over `run`, which `#tooth` refuses to clone. Their teeth are those of
`step_inv`, the whole of their induction step.

**Non-vacuity of the general theorems, by instance (PROVED):** `script_legal` (`reachable_legal` at
the stranger's run), `lost_instance` (`lost_reply_frozen` at its lost reply), `typed_instance`
(`drive_complete` at the negotiation, from `instantiations_hasProt`), `everything_delivers` (a driven
run equal to `interpret`'s).

## 4. The stranger's example (`Negotiation.lean`, PROVED by evaluation)

The negotiation starts with every grant held, planning on `p1`. The host world is a `World`: each
fact is its own cell, and the step is anything except un-passing the deadline. The provider hole is
also a `Slot` with candidates `p1`, `p2` and cancel, each citing its grant and the deadline.

| # | event | outcome |
|---|---|---|
| 0 | dispatch reserve | accepted |
| 1 | reply to reserve | accepted |
| 2 | world: `p1`'s grant revoked | accepted |
| 3 | dispatch commit `p1` | `unadmitted (commit p1) [auth p1] none` |
| 4 | replan the provider hole (the slot at this view: `resolves_p2`) | accepted: plan is `p2` |
| 5 | dispatch commit `p2` | accepted; `cap` spent |
| — | **the reply is lost** | |
| 6 | world: grant restored, capability called live again | accepted |
| 7 | replan to cancel | `replacesInflight (commit p2) provider` |
| 8 | replan back to `p1` | `replacesInflight (commit p2) provider` |
| 9 | replan to `planFlip p2` (same first call) | `replacesInflight (commit p2) provider` |
| 10 | dispatch commit `p1` | `busy (commit p2)` |
| 11 | late reply to commit `p1` | `unsolicited` |
| 12 | world: deadline passes | accepted |
| 13 | world: deadline un-passed | `worldStep` |

`receipt` is that column. `changed`: the plan went from `p1` to `p2` before anything was dispatched in
the hole, and the world ends past the deadline. `stayed`: the answered history is the reservation,
`commit p2` is in flight and is the residual's next call, `cap` is spent exactly once, the plan in
force is `p2`'s, and the log's dispatches are `[reserve, commit p2]`.

`withdrawn_refused` is Astra's line 105 run through the runner. At every-fact-false with the
capability live, `admitOp` says false and `interpret (env true)` delivers in two calls. The runner,
driven by the same handler, refuses `unadmitted (commit p1) [auth p1, beforeDeadline] none`, and the
handler has seen one call.

## 5. The boundary to the host (INFERRED; stated, not proved)

- **Serialization and durable commit.** One `run` step is atomic: admission, spending and recording
  in flight happen before the handler sees the operation. A real host must persist `spent` and the
  in-flight record (journal-first) before release, and must serialize steps per object. The theorem
  is about the runner's state, not about a crash between persistence and release.
- **Physical effects.** "No token dispatches twice" and "a lost reply licenses no new commitment" are
  facts about the runner's exposures. They are not exactly-once delivery in a network, which needs
  the peer's dedupe (`Hosting.Proofs.LostReply`).
- **The world is adversarial.** `Host.allowed` is whatever the host decides. The invariant assumes
  nothing else about updates: grants come and go, and the world may say a spent token is live.
- **Untyped plans.** The runner does not require `HasProt`/`Fills` of a replan's filling.
  Authorization is enforced at dispatch, so an ill-typed plan is refused when it acts, not when it
  is installed. Typing buys completeness (`drive_complete`), not safety.

## 6. Not done

- No adapter from emitted Core4 plans or inherited laws to the runner. That is Astra's next bridge.
  The runner is generic in `Sig`, so it takes an adapter, not a rewrite.
- `drive` is restricted to handler states constant across indices (`Handler S (fun _ => St)`, which
  `Negotiation.env` is). An indexed-state drive needs the residual's index in the configuration's type.
- The replan guard is per hole: once a hole is entered, its whole filling is frozen, including
  continuations not yet performed (`planFlip`). This is `guard_stricter_than_wf`, now enforced at
  run time.

## 7. The decision taken: `abandon` (second pass, MEASURED and PROVED)

Ember's option (b). `abandon o` is accepted only for the call in flight (`notInflight` otherwise).
The call stays in the history, dispatched and never answered, so `Hist.established` keeps its
obligation (`abandon_keeps_obligation`). The run is ended (`Cfg.ended`, guard `closedBy`): every
later replan, dispatch, reply or abandonment is refused `abandoned`, and only the world moves
(`ended_frozen`). `Legal` gains `Paired`'s third clause (abandon only the call in flight) and
`AfterAbandon` (after an abandonment, only world events). `Inv` tracks `c.ended = endedOf c.log`.
`step_inv` and `refines` cover the new event. Teeth on `closedBy`: `step_inv`, `ended_frozen`, and
the fixture `abandon_ends`. That fixture abandons the reservation in flight; its late reply and an
admissible commitment on `p1` are refused, and without the guard both go through. The stranger's
example now ends: rows 14–18 abandon `commit p2`, refuse its late reply, a cancellation and a
commitment on `p1`, and accept one last world move. `stayed` proves the run is ended by
`commit p2` and that the established obligations are `[holdDeposit, pay p2]`.

## 8. Selection: policy-independent soundness and the decision rechecked at dispatch

Coordinator's message, after `astra/ASTRA-SELECTION-20261031.md` §7–8.

**Taken (PROVED):**
- `Obend/Slot/Selection.lean` (a new file; `Integrity.lean` is unchanged). `SelectionSound` is §7.1
  as written. `transition_sound` (`Integrity.transition` implies it), `churn_sound` (first-usable is
  sound, though not incumbent-first), `slotAdvance_sound`, `sound_retired` (exclusion of retired
  supports from soundness alone: the policy-independent form of `transition_retired`),
  `incumbent_choice` (the preset's law: the stored selection is kept exactly while usable, else the
  first usable candidate is chosen), `not_sound_sticky`.
- **The runner is parametric over the policy.** `resolveEventBy (adv : Advance V Fact Cand)` takes
  any policy. `resolveEventBy_ok` needs only `SelectionSound`; `resolveEventBy_keeps` needs
  `Integrity.transition`. This was cheap: the runner never stored a candidate, so the policy enters
  only where a replan event is proposed. Astra's change of default touches nothing in `Run`.
  `resolvesBy_p2` is the incumbent-first instance.
- **The chooser's override.** `chooseEvent` and `override_accepted`: before dispatch, the chooser's
  choice of any candidate for an unentered hole is accepted, whether or not the choice it
  supersedes is still usable. Authority is the hole's `.me` chooser, checked by `run`.
- **Astra's §7.3 gap closed by the first route: carry the decision into dispatch and recheck it.**
  `Event.replan h f cites` installs the body and the facts its decision cites in one event, and
  both are frozen together once the hole is entered. A body cannot change under unchanged
  citations, because there is no candidate id, only the installed body. `Cfg.cites` records them.
  The dispatch guard `decisionDead` refuses `unsupported o hole dead` unless every fact cited by the
  decision of the hole the call enters (`owner`, the executable `Dispatched`) holds now.
  `resolveEvent`/`resolveEventBy`/`chooseEvent` cite the selected candidate's `supports`. `Legal`
  gains `DecisionsHeld`, stated with `Dispatched` and the log alone. `dispatch_usable_choice` is
  §7.3's `AdmitOperation ∧ UsesChoice → Usable`: a dispatched call in a hole decided for `cand`
  finds `cand` usable at the world of that dispatch, however the world moved since the selection.
- **Fixture and teeth.** `laxSpec` omits every requirement. The slot selects `p1` (`selects_p1`),
  `p1`'s grant is revoked, and the commitment that `laxSpec` admits is refused
  `unsupported (commit p1) provider [auth p1]` (`decision_rechecked`). The `#tooth` with
  `decisionDead := []` is rejected there and in `step_inv`.

**Left for a later lane:** `Permitted` beyond the hole's chooser (a versioned candidate domain);
`DecisionEffective` beyond `.me`: authenticated authority, decision revisions, office changes;
the per-slot `SelectionControl` descriptor and versioned policy events; the richer
`NoAdmissible`/diagnostic outcome; a first-usable preset with a rejected-prefix certificate;
hysteresis and leases. The initial plan's fillings (`O.σ`) cite nothing (`Cfg.init`): a decision
present at start is not rechecked until it is replaced. `Integrity.transition` is not renamed.

## 9. The Core4 adapter (PROVED)

`Obend/Run/Core4.lean` builds the activity as a protocol. `planSig` has one operation per Plan
(`Data`, with a decided equality written out, because `Data` derives only `Repr`) and one response
per `Data`. `turn` is the machine's own turn, `runBounded` then `yieldedPlan`, as
`Spec.Preview.runTurns` runs it. `unfold n s` is the activity to depth `n`: each yield is a call of
its Plan, continued for every response by `resume`. `activity` is the hole-free open object, and
`Transcript` is the machine's run of (Plan, response) pairs, stated without the runner. What a
Plan requires and spends is a deployment `Spec` over `Data`.

- `transcript_of_reach` / `reach_of_transcript`: a path of the protocol is exactly a machine
  transcript, and the residual is the activity resumed after it. `turn_vis_resumes`: a yielded
  state always takes a response, from `yieldedPlanWith_control`, so `unresumable` is never reached.
- `run_is_trace` (machine to runner): a transcript whose Plans are admitted at the world, each token
  spent once, is accepted event by event. The history is the transcript, the residual is the
  activity resumed, and the log is `Legal`.
- `trace_is_run` (runner to machine): at every configuration reachable from the activity, the log
  is `Legal`, the answered history is a machine transcript, the residual is the activity resumed,
  and the call in flight is the Plan the machine yields there. The runner exposes no Plan the
  program did not yield.
- Tooth: `session_of_transcript` by `dispatchGuard := false`.
- The instance at a real program is the legacy leaf `Obend/Run/Core4Example.lean` (`yieldingTerm`
  yields `5`). `turn_is_trace` instantiates `run_is_trace` with a one-use ticket, and
  `dead_ticket_refused` shows the same Plan refused when the ticket is not live. Preview admits
  nothing; the runner does. That file is not a `module`: a `module` copy of `yields` fails `rfl`
  (MEASURED), for the `Init` reason recorded in `REPORT-20261030.md` §2.5.

**What the adapter does not cover:**
- **The reference tree.** It is stated over the executable machine turns, not over the
  noncomputable `Interaction.observe` tree. The link exists (`node_of_chain_vis`: a machine yield is
  the reference `Vis` for states in a chain), but it is not composed into `trace_is_run`.
- **Depth.** `Prot` is inductive, so the activity is a depth-`n` unfolding. A run longer than `n`
  ends `.ret depth`, and there is no deepening mid-run.
- **Tick suspension.** Running out of ticks within a turn ends the protocol
  (`Stop.ended (.suspended …)`); there is no resumption with more ticks.
- **Response typing.** The runner does not check `conforms` against the declared response type,
  which Preview does.
- **Plan authority.** It comes only from the supplied `Spec`. No inherited law or Law fragment is
  connected yet.
- **No choice points.** An emitted plan has no holes, so the selection machinery of §8 does not yet
  reach Core4 plans. That needs `Slot.Core4`'s hole fragment as the protocol's holes.

## 10. The one decision for Ember

**Should a decision present at the start be rechecked?** `Cfg.init` gives the initial plan's
fillings no citations. Only replanned decisions are rechecked at dispatch, so a plan built with
`p1` from the start dispatches on `p1` under `laxSpec` after `p1`'s grant is gone. The fix is one
field: `Open` or `Cfg.init` carries the initial citations. It touches `Open`, which every slot
theorem shares. I left it, and recommend adding it to `Cfg.init` (runner-local), not to `Open`.
