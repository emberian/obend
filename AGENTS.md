<!-- obb-harness: v4 | id: rule:AGENTS.md | sha256: 7359f1126f33f46f38fef48ead8c9c776c23c3c099c2e4d6a7fa06411ae972c7 -->
# Obend Canonical Agent Engineering Rules (`AGENTS.md`)

Shared always-on engineering constitution for Codex, Antigravity, and Claude Code. Keep all edits aligned with every invariant below without exception.

## 1. Hard Remote-Only Build & Verification Rule (Zero macOS Builds)

- **NEVER execute `lake`, `lean`, `cargo`, `rustc`, or `Holmake` on macOS.** Local workstation CPUs and memory must never run Lean elaboration, Rust builds, or proof search.
- Execute **all** Lean 4.35, Rust, GPU, and RTL/HDL builds and tests remotely on `bb2` or `hbox` under hard memory and wall-clock caps (`SWARM_MEM_MAX=12G`, `timeout --kill-after=10s 600s`):
  ```bash
  obb broker probe --hosts bb2,hbox
  obb broker plan-build Obend.Trailblaze.CathedralApex --repo . --host bb2 --max-rss-gb 12 --timeout-secs 600 --exec
  ```
- When running direct SSH verification against a remote worktree on `bb2`, always wrap invocations in `SWARM_MEM_MAX=12G timeout --kill-after=10s 600s`.

## 2. Scar-Free In-Place Architecture (`AMBITION.md:62`)

- ***"Nothing lands beside; everything replaces."***
- Never introduce `*V2.lean`, `*New.lean`, `Mock*.lean`, `Golden*.lean`, `*Poles.lean`, or parallel wrapper structs to avoid repairing a broken carrier, compiler pass, or theorem.
- Upgrade flawed definitions **in place**, update every downstream caller across the import cone, and delete superseded scaffolding in the same commit.
- Maintain **zero retired-subsystem fossils** and **zero `.obb/` or `ledger/` state pollution** inside `Obend` git worktrees.

## 3. Kernel Soundness & Lean 4.35 Module Encapsulation (`LAW-M1`, `LAW-M2`)

- **Zero Trust Bypasses:**
  - `0 sorry` / `0 sorryAx` anywhere in the repository.
  - `0` custom `axiom` declarations.
  - `0 native_decide`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or `Lean.trustCompiler` in `lean/Obend/` library modules (`lean/native-decide-in-proof`).
  - `0 Classical.choice` in `Type`-valued computational extractors (branch constructively via `DecidableEq` / `PSum`).
- **`LAW-M1` Module Encapsulation:**
  - Every `.lean` file in `Obend/` begins with `module` and uses `public section` for exported signatures.
  - **Never** place `@[expose] public section` at top level in files `> 80` lines (`lean/file-wide-expose`).
  - **Never** exceed `12` per-declaration `@[expose]` attributes in a `> 80`-line `module` file (`lean/excessive-decl-expose`). Seal recursive/operational bodies inside `.olean.private` and export equational or soundness theorems (`*_eq`, `*_sound`) instead.
- **`LAW-M2` Meta-Import Hygiene:**
  - Restrict `public meta import Lean` strictly to `lean/Obend/Tactic/` and `lean/Obend/Elab/` (`lean/public-meta-import-leak`).

## 4. Anti-Cosplay & `Spec ↔ Exec` Data-Refinement Mandates

- **Stage-A `*Obligations` Honesty (`lean/obligation-tautological-field`):**
  - Never write tautological Stage-A obligation signatures (`P → Q → P ∧ Q`, `a = b → f a = f b`, `(φ.meet ψ).implies φ = true`, unused quantified binders, non-existential `*Extract` fields, or trivial `> 0` bounds under `Gkr`/`ZeroKnowledge`/`Attested`/`Refines`/`IsaEquiv` names).
  - Before locking any commitment-binding obligation (`digest H t₁ = digest H t₂ → t₁ = t₂ ∨ Collision H`), verify that **every** field of `t` is length-framed (`frameBytes`) in the preimage; omitting even one field makes Stage-B literally `False`.
- **Stage-B Instance Honesty (`lean/obligation-projection-cosplay`):**
  - Never discharge `*Obligations` or `*Ledger` instances via 1–3 line `rfl`, `congrArg`, `Bool.and_eq_true`, `And.left`/`And.right`, `fun _ => trivial`, or trivial carriers (`Unit`, `Bool`, `Nat`).
- **Inhabited `Judge` Completeness & Refusal (`lean/judge-empty-fragment`):**
  - Never set `Fragment := fun _ => False` or `refutes := fun _ => false` inside `Obend.Judge` instances or builders (`SilverWorkflow.toJudge`), and never restate `check` inside `Meaning` (`lean/tautological-judge-meaning`).
- **Environment Anti-Narrowing & Multi-Turn Completeness (`lean/single-sequence-harness`):**
  - Never claim apex protocol safety from a single-turn theorem (`apex_*_turn_safe` / `apex_*_turn_sound`) without a multi-turn trace/reachability invariant (`List *Turn`, `Reach`, `SafeWP`, `ValidTrace`, `MultiTurnHoare`) covering state accumulation (`RevokedSet` growth, `Mandate` budget depletion, persistent `UMem`), and pair open-world environment filters with completeness theorems (`skip_implies_contract_violation` / multi-handle reachability).
- **Full-Width Cryptographic Carriers & `Spec ↔ Exec` Efficiency:**
  - Ban `Nat` digests and `≤ 64`-bit scalar digest stand-ins (`lean/narrow-digest-weld`); use 256-bit carriers (`BitVec 256`, 32-byte `ByteArray`, or 4×`UInt64`).
  - Pair clean inductive/`List` `Spec` definitions with $O(N)$ / $O(N \log N)$ `ByteArray`, `Array UInt64`, `Array`, and `BitVec` `Exec` implementations connected by proved refinement theorems (`Simulates`, `@[csimp]`, `*_exec_eq_*`).

## 5. Mandatory Pre-Landing Verification Gates

Run all mechanical gates before landing or promoting any slice:

```bash
obb lint --repo <repo> --strict --strict-expose --strict-harnesses
obb cone --repo <repo>
obb pipeline check --repo <repo> --strict
obb apex check --repo <repo>
obb harness check --repo <repo>
```

Every load-bearing checker and soundness theorem must be paired with `#tooth` mutation-sensitivity witnesses and inhabitedness witnesses (`lean/uninhabited-premise-risk`).

## 6. Progressive-Disclosure Skills (Load On Demand)

Activate the dedicated runbooks under `.agents/skills/<name>/SKILL.md` (and `.claude/skills/<name>/SKILL.md`) when working in their domain:

1. **`obend-anti-cosplay`**: Field guide to the **10 Mistakes Models Like to Make** in `Obend` + `#tooth` / `#audit_claim_contract` verification runbook.
2. **`obend-spec-exec-refinement`**: Verified `Spec ↔ Exec` playbook (`ByteArray`, unboxed `Array UInt64`, `BitVec`, sorted binary-search & linear merge-scan arrays, `Simulates`, `@[csimp]`).
3. **`obend-proof-engineering`**: Lean 4.35 `LAW-M1` encapsulation, `0 Classical` `PSum` extractors, `termination_by structural` WHNF discipline, `GPaco`/`MultiTurnHoare`, remote `bb2`/`hbox` builds.
4. **`obend-trailblaze-promotion`**: Stage-A (`*Obligations`) $\to$ Stage-B (`0` open obligations) promotion runbook, pre-lock `Collision H` injectivity proofs, and `quarry/obend-apex.toml` wiring.
