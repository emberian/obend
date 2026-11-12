<!-- obb-harness: v4 | id: rule:CLAUDE.md | sha256: 2b2c094c4c44fbdaa9c26d29b298d9c912de7ea98eb20c51f4cb3919cf3d34ab -->
# Claude Code Deputy Configuration (`CLAUDE.md`)

@AGENTS.md

## Claude Code Skills Index (`.claude/skills/`)

Read the relevant `SKILL.md` before editing Lean specs, runtime data structures, or Stage-A/Stage-B obligations:

- `.claude/skills/obend-anti-cosplay/SKILL.md` — **10 Mistakes Models Like to Make** & `obb lint --strict --strict-expose` audit gates.
- `.claude/skills/obend-spec-exec-refinement/SKILL.md` — `Spec ↔ Exec` refinement (`ByteArray`, `Array UInt64`, `BitVec`, sorted binary-search / $O(N)$ merge-scans, `Simulates`, `@[csimp]`).
- `.claude/skills/obend-proof-engineering/SKILL.md` — Lean 4.35 `module` encapsulation (`≤ 12` `@[expose]`), `0 Classical` `PSum` extractors, structural WHNF recursion, `#tooth`, `GPaco`, remote `bb2`/`hbox` broker builds.
- `.claude/skills/obend-trailblaze-promotion/SKILL.md` — Stage-A $\to$ Stage-B promotion workflow, pre-lock `Collision H` preimage injectivity, and `quarry/obend-apex.toml` registration.

## Deputy Execution Rules

1. **Zero Local Builds:** Never run `lake`, `lean`, `cargo`, `rustc`, or `Holmake` on macOS; execute all builds on `bb2` or `hbox` with `SWARM_MEM_MAX=12G` and `timeout --kill-after=10s 600s`.
2. **Never Weaken Specs to Close Goals:** Do not weaken theorem conclusions, shrink `Judge.Fragment` to `False`, set `refutes := false`, or spray `@[expose]` across `module` definitions to appease tactics.
3. **Pre-Report Gate:** Run `obb lint --repo <worktree> --strict --strict-expose` and remote `lake build` before reporting any slice ready.
