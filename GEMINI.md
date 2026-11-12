<!-- obb-harness: v4 | id: rule:GEMINI.md | sha256: c790121e3762f3c38a3322517b2c70debd9478b6816f060649bc6fb169afd561 -->
# Antigravity Workspace Configuration (`GEMINI.md`)

@[AGENTS.md](./AGENTS.md)

## Antigravity Progressive-Disclosure Skills (`.agents/skills/`)

Do not inline bulky runbooks into conversation turns; activate the matching workspace skill on demand:

| Skill | Activate When |
| :--- | :--- |
| `obend-anti-cosplay` | Designing or auditing `*Obligations` classes, `Judge` instances, Merkle/hash commitments, hardware structs, string-aware lexers, or AST compilers. |
| `obend-spec-exec-refinement` | Pairing `List`/inductive `Spec` models with `ByteArray`, `Array UInt64`, `BitVec`, sorted binary-search / merge-scan arrays, `Simulates`, or `@[csimp]`. |
| `obend-proof-engineering` | Fixing `LAW-M1` `@[expose]` bloat, eliminating `Classical.choice`, avoiding `WellFounded.fix` WHNF blowups, writing `#tooth` witnesses, or batching remote `bb2`/`hbox` builds. |
| `obend-trailblaze-promotion` | Promoting a Stage-A `Trailblaze` organ to Stage-B (`0` open obligations) and registering apex theorems in `quarry/obend-apex.toml`. |

## Multi-Agent Worktree & Swarm Discipline

- Partition parallel write lanes up front with `obb cone --repo . plan --propose <lane>=<files...>` so concurrent workers never contend on `public_fan_in > 25` hub headers.
- Isolate concurrent edits in `scratch/worktrees/<lane>` synced to `/home/build/obend/wt-<lane>` on `bb2`; never run `lake`, `lean`, `cargo`, `rustc`, or `Holmake` on macOS.
