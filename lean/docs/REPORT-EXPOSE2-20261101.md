# Expose, round 2: `Check` unexposed; the Lean 4.35 `_unsafe_rec` limit (Claude Opus, 2026-11-01)

Placed by the root from the lane's closing report. Commit `23ebda5`. Both tiers green, cohorts,
receipts (32/32), workspaces, walkthrough unchanged.

`Check` keeps seven exposed definitions (`AnnotatedTerm.erase`, `Assumptions.valid`, `callable`,
`labelsDistinct`, `reusableAllowed`, `literalType`, `primitiveTypes`), reduced by exposed bodies or
by `Slot/Budget` and `Spec/Proofs/LawCompile`; everything else is unexposed including `infer`,
`check`, `isRowW`, `caseAllowed`, `caseQuantity`. `infer_zero` is proved by `cases term <;> rfl`
so its equation stays out of the `.olean`. 31 readers that unfold or evaluate the checker take
`import all Obend.Core.Check`.

**Gate (a `Check` edit within twenty modules): open.** An `infer` body edit rebuilds 112 modules
(142 s under load 280–300); a non-recursive unexposed definition (`planRow`) rebuilds 32. Cause,
confirmed by `.olean` diff and a scratch project: Lean 4.35 writes a recursive definition's body
into the public `.olean` as `<name>._unsafe_rec` whether or not it is exposed; in `Check` this
covers the `infer` block plus `overlay`, `callable`, `walkRow`, `lookupW`, `isRowW`,
`labelsDistinct`. `noncomputable` would remove it but `Core/Packet` runs `check` compiled. Two
further limits: `Check`'s own proofs `simp [f]` on `lookupW`, `walkRow`, `isRowW`, `labelsDistinct`,
`reusableAllowed`, writing those bodies too; and getting under twenty for `infer` would mean one
function recursing on a `Nat`, a rewrite inside the checker gate 2 is retiring.

Decision: gate 2 first; measure the single remaining checker; only then decide on the `Nat`-recursion
rewrite.
