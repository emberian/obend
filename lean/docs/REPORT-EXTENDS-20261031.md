# Lane Extends: a stranger extends my package (Claude Opus, 2026-10-31)

Placed by the root session from the lane's closing report; the harness refused the lane the write.
Commits `3b98eb8` (extends), `9db064f` (intentions as slots), `dcf1f1b` (package laws inherit),
`7f8802e` (orthogonal protocols). Full build 230 jobs, census clean; Mini's cohorts unchanged at
every commit; `tests/run-workspace.py` 22/22 over `tests/obend-source/three-package/` and `stranger/`.

The stranger's example runs end to end:

    $ obend run --package tests/obend-source/stranger/workspace.json
    result: 12002
    package: notes/garden > lab/review > kit/export > papers/report

## 1. `package NAME extends REF, …`
`NAME@^MAJOR` is an intention; `NAME@0xHASH` an extension (full 64-hex content hash). A workspace
file (`dregg.objective-bend.workspace.v1`, `Obend.Spec.Workspace`) is the ecosystem root: releases,
owners' record lines, entry package. `Ecosystem.close` resolves one release per name; two routes
reaching different content are refused by name, cycles refused naming both. The closure is lowered
as one fixed point, one layer per package in C4 order, keys `PKG::Module.decl` (the `(intention,
declaration)` identity). Four-package test: base applied once (`weighed` = 1111), `compose(E, E)`
still twice across the boundary (`twice(5)` = 7). A single package elaborates exactly as before.

## 2. Intentions as slots
`intentionSlot name major : Slot Named Pin`: versions as candidates, the owner's record line as
the choice, one support "the record names v at pin p". Proved: `turn_pins_every_root`,
`resolve_fill`, `stale_iff_blocked` (staleness is exactly the slot's blocked read naming that
support), `extension_current`, `admit_never_stale_extensions`, `admit_stale_names_moved`,
`admit_refuses_moved`, `admit_admitted`, `moved_pin_stale_forever`, `retired_stale_forever`,
`turn_stale_forever`; a kernel `decide` tooth and three `#tooth`s. `obend admit --package WS TURN`
reports `admitted` or `stale NAME`.

## 3. Package laws inherit
The effective law runs every package's clauses in C4 order, each named `PACKAGE law CLAUSE`.
Proved: `package_law_eval`, `package_never_widens` (a child only narrows across packages),
`package_refusal_names`, `closure_law_inherited`. `obend judge --package WS OLD NEW` prints
`refused: papers/report law cited`. Under `Obend/Spec` since LawFinish owns `Obend/Law`.

## 4. Orthogonal protocols
`protocol Export for P.Page:` makes each method a field keyed by (generic, kind) in the
implementing package's layer (LTUO §9.2.10, §9.3.7). A call dispatches to the most specific
package's implementation; two unrelated implementations are refused `competing-protocol`; a
package extending both settles it by implementing the method. Stranger: `kit/pdf` overrides
`kit/export` (120001); competing refused; resolved 840; ancestor laws refuse the stranger's write.

## Not done
Suffix property across packages; live migration or `adopt` when an ancestor's law changes (a stale
turn's repair is re-resolving the workspace); owners' records as law-governed kernel cells rather
than workspace lines; the diamond's C4 order checked only on the executable path (two-parent merge
is not kernel-reducible, string hashing is `extern`).

## Decision for Ember
Should kinds be nominal? Protocol calls dispatch on the instance's structural type, so two kinds
with the same fields are refused, never silently resolved. Nominal kinds mean the kind cell
(K-KIND-CELL): every instance carries its kind's identity, a tag per object, and the kind's law
becomes an ancestor of each instance's law, which item 3 already wants. Recommended: nominal.
