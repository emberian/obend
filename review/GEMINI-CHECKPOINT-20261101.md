# Gemini's review of checkpoint-20261101 (pasted by Ember, 2026-11-01)

Verified against the code by Claude before acting; see `review/GEMINI-RESPONSE-20261101.md`.
Headline findings beyond Astra's review:

1. Four soundness holes in linear typing (`Core/Check.lean`), each dropping or duplicating a linear
   variable in one or two `Step`s: `specification` sums `mu` with no `linearFree` on the metadata, and
   `applySpecification` discards it; `case` binds the arm payload `.unrestricted` after `inject`
   consumed a linear scrutinee once; `ifZero` (and `ifBool`'s condition) binds the predecessor
   `.unrestricted` with no `linearFree` on the scrutinee; `extend` requires no `linearFree` on the
   target and `extendRecord` overwrites the field.
2. Receipt forging (`Receipt.lean`, `Receipt/Export.lean`): `capOpening` defaults to `true` when the
   capability opening is absent; `recheck` checks only the openings present and never that
   `R.openings.map Prod.fst` covers `A.reads`; `dated_sound` takes that coverage as an external
   hypothesis the verifier never computes. A producer omits the spent-capability opening and its
   proof and `verify` accepts. Also: `R.trust` is unchecked, so `[]` renders as `trust checked`; and
   `accepts` in `.cited` mode trusts `R.verdict.isOk` without `recheck`/`datedOpens`.
3. Fork stitch bypasses the runner (`Run/Fork.lean`): `forkStep` records `.defer i t` into
   `escalated` unchecked and `stitchRows` commits each through `ledgerStep` directly, bypassing
   `crun`'s protocol, law judge, authority and citations, and not atomically.
4. The Hackett–Hutton obstruction (`Equiv/Clairvoyant.lean`) is a staging artifact: `fixLet`
   evaluates `selfBody` to a settled record before substituting the knot, so `self` is still
   `.bound 0` when `b = self.a` is forced. Repair: iterate approximants (`V₀ = skipped`, `Vₘ₊₁` from
   `selfBody` against `Vₘ`), or a Launchbury-style local thunk environment; no heap addresses needed.

Further: `encodingVersion` hashes only `syntaxSchema` (not `Ty`, quantities, assumptions, checker
edition); `Code Ψ A θ` via `Checked` versus `importWith` via `checkAgainst` forces `import_complete`
to re-synthesize the tree; `importWith` has no work bound; `observes` raises the census only at
`.metadata`, not `.reflect` (correct for `compose_assoc_b`, misdescribed in the orientation §3.2);
`Admits .b ρ C` requires whole-term `ObsFree` on substitutions; the Gödel–Löb reading of
`instantiatePrototype` should be dropped; mirrors are forgeable `Data` records; the promotion
criterion needs a sixth clause for machine compilation and simulation; `Meaning` depends on `Cert`
so coercion's and improvement's completeness fragments are circular; four of six judges have
`refutes := false` where `c4` could refute; `Judge.deepen` is quadratic where `runBounded_mono`
would make the law judge linear; `Collides` conflates ABA content return with hash collision unless
`pinOf` commits to the version; `Kept` is not a state invariant because `Rest` drops abandoned
obligations; `propagate` swallows errors; `exposed_once` is at-least-once with idempotency keys;
records are linear black holes (`⊗` constructed, neither `⊗` nor `&` eliminated); `CostWithin` is a
symmetric `8ⁿ` factor, not improvement, and parallel `Sim` would make it flat 8; two checkers
(`Check.infer`, `Bidirectional`), two kind systems (`Kind`, `Vault/Law.kindChain`), four term
encodings. Five gates before building further: close the soundness and forging holes; retire
`Check.infer` before C1/C2; repair `fixLet` and discharge `Completeness`, prove `runBounded_mono`;
strip blanket `@[expose]` from Core; make PLAN's integration scenario a compiled theorem before WS 5–10.
