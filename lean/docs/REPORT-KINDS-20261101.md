# Lane Kinds: kinds are nominal, one Intention, C4 proved (Claude Opus, 2026-11-01)

Placed by the root from the lane's closing report. Commits `d84c6c6` (C4), `85062ab`+`fc0df9f`
(teeth moved), `ccbcd13` (Intention), `ce43d93` (the kind cell and the `Syntax` built-ins). End build
464 jobs; census 34,466 constants, 27 on compiler trust; cohorts, receipts (22/22), workspaces
(30/30), walkthrough (26/26) at every commit.

## C4 `linearize`, structural and proved
Four steps, no hash map, no fuel: suffix tail joined along one chain; candidates cleaned of the tail;
C3 merge bounded by total candidate length (kernel-reducible); head, merge, tail. Proved for every
graph: `linearize_head`, `_nodup`, `_mem`, `_fresh`, `linearize_local` (local precedence),
`linearize_monotone`, `linearize_tail`; under `Coherent g`: `suffix_property`, `coherent_extend`.
`precedenceOk` and `unordered` retired; `precedence_ok`/`_monotone`/`_local` are corollaries;
`c3_tree_is_chain` gains an acyclicity hypothesis (the old form held only by a repeating list);
`fuel_is_not_inconsistency` becomes `c4_refusals`; the seeded vectors stay as tests (40,000 agree,
checked once). Not done: `OrderedPresentationInvariant` still checked, not proved; no package-level
suffix marks.

## `Obend/Intention.lean`
One structure (`ref`, `supports`, `holds`, `resolve` with soundness fields); generic
`stale_iff_blocked`, `resolve_fill`, `renew`/`renew_fill`/`renew_repairs`, `stays`, `blocked_names`,
`blocked_within`. Instances: package parents (`intentionSlot`, `Pin.current` retired into it), cites
(`recite` is `renew`; `recite_holds`, `cite_stale_iff_blocked`, `pinned_cite_stays`,
`following_cite_behind` as instances), kind references. Every former statement unchanged. Not yet:
leaf proofs, attestations, leases.

## The kind cell
`KindCell` (name, version, layout, initial state, own law, parents); every instance carries a
`KindPin`; `create --from K`; `effectiveOf` = own law then every kind on the C4 list; `dispatch` by
kind. Proved: `kind_law_inherited`, `instance_law_admitted`, `create_carries`,
`effective_refuses_stale`, `kind_stale_iff_blocked`, `renew_kind`, `dispatch_by_kind`,
`dispatch_sound`; `nominal_tooth` (equal layouts, own implementations), `stale_tooth`. Language:
protocol calls dispatch by declared kind (Mile/Kilo test; `unnamed-kind`, `kind-mismatch`
refusals). Vault: `_kind.md` is a real kind; `kind: K` on a page; `obend create --from K PAGE`;
`kind_law_inherited` via `judge_admits`. `Syntax`, `SyntaxList`, `SyntaxTag` registered as
front-end built-ins (`tests/obend-source/builtin/`).

Decisions: D1 nominal is static in the language, a carried tag in the cell and vault; D2 cycles
refused inside `linearize`; D3 Syntax checks in `run-workspace.py`; D4 `Elaborate` imports
`Core/Code`.

## Decision for Ember
Should nominal kinds govern *type checking* too? The checker accepts a Kilo as a Mile when fields
agree; only direct calls refuse. Nominal checking puts a name on record types in `PTy`, touching
the typing proposal, `Annotated` and `TermWire`. Recommended yes, as its own lane after Quote.
