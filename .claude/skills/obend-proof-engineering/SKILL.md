---
name: obend-proof-engineering
description: >-
  Provides Lean 4.35 proof-engineering patterns for Obend: LAW-M1 module encapsulation, 0-Classical PSum extractors, structural WHNF recursion, #tooth mutation guards, GPaco/MultiTurnHoare coinduction, and remote bb2/hbox broker builds. Use this skill when writing or debugging Lean 4 proofs and module headers.
---
<!-- obb-harness: v4 | id: skill:obend-proof-engineering | sha256: 4f8267d9bff3d9330d2289174f5611dd5ceef2271de6636b9a6301af3bc91744 -->
# Obend Lean 4.35 Proof Engineering Runbook

## 1. `LAW-M1` Module Encapsulation & `@[expose]` Discipline

Every `Obend/` module uses Lean 4.35's `module` system to isolate `.olean.private` implementation bodies from public `.olean` headers:

```lean
module
public import Obend.Judge.Class
import Obend.Core.InternalLemmas  -- private import: zero downstream cone leakage!

public section
namespace Obend.Subsystem
set_option autoImplicit false
```

- **Hard Caps:** Never use `@[expose] public section` in files `> 80` lines (`lean/file-wide-expose`), and keep per-declaration `@[expose]` attributes `≤ 12` per file (`lean/excessive-decl-expose`).
- **How to Drop `@[expose]` Without Breaking Callers:**
  - Keep carrier `inductive` / `structure` / `class` declarations in `public section` (their constructors/projections remain accessible without `@[expose]` on function defs).
  - Seal operational functions (`audit*`, `verify*`, `compile*`) without `@[expose]`, and export crisp `theorem` contracts (`verifyFoo_iff`, `auditFoo_sound`).
  - For smoke vectors, prefer `by decide` in `tests/` or keep at most 1–2 tiny fixture constants exposed if kernel `rfl` tests in another module require definitional unfolding.

## 2. `0 Classical` Constructive Proofs & `PSum` Extractors

Never pull `Classical.choice` or `Classical.em` into `Type`-valued extractors or kernel security theorems:
- When a `Prop` disjunction `t₁ = t₂ ∨ Collision H` is proved from `H pre₁ = H pre₂`, branch constructively using `DecidableEq` on `List UInt8` / `ByteArray`:
  ```lean
  if hPre : pre₁ = pre₂ then
    exact Or.inl (preimage_injective hCan₁ hCan₂ hPre)
  else
    exact Or.inr ⟨pre₁, pre₂, hPre, hHashEq⟩
  ```
  This constructs `Collision H` with **zero `Classical` axioms**.
- For computational witness/refusal extractors in `Type`, return `PSum Witness (RefusalClause × Trace)` or `Except Refusal Witness` paired with bidirectional soundness/refusal theorems.

## 3. Structural Recursion vs `WellFounded.fix` Kernel WHNF Traps

- On nested mutual inductives (`inductive HttpsSessionNode | mk ... (children : List HttpsSessionNode)`), **always** annotate mutual traversals with `termination_by structural n` / `termination_by structural ns`.
- Omitting `structural` causes Lean to compile via `WellFounded.fix` over `sizeOf` (which traverses `String` byte lists), causing kernel `decide` and WHNF reduction to stall or blow out `maxHeartbeats`.
- Never reach for `native_decide` in `lean/Obend/` to paper over a slow WHNF reduction; fix the `structural` recursion or prove the goal symbolically (`simp`, `omega`, induction).

## 4. `#tooth` Mutation Sensitivity & `GPaco` / `MultiTurnHoare`

- **`#tooth` Discipline:** Pair every checker (`verify*`, `audit*`, `check*`) with concrete accepted **and** planted-fault refused witnesses (`#tooth` / `example : audit pol plantedBad = .error (.specificClause ...)`), proving the refusal names the exact violated clause rather than vacuous `false`.
- **Reactive & Multi-Turn Protocols (`GPaco` / `MultiTurnHoare`):** Model unbounded multi-turn protocol safety (viability envelopes, governance state transitions, channel non-interference) via parameterized coinduction (`GPaco`) or `MultiTurnHoare` invariants rather than finite 1-step unrollings.

## 5. Remote-Only Build Execution (`bb2` / `hbox`)

**NEVER run `lake`, `lean`, `cargo`, `rustc`, or `Holmake` on macOS.**

```bash
# 1. Check remote load, free RAM (ZFS-ARC aware), and runaway processes:
obb broker probe --hosts bb2,hbox

# 2. Plan & execute a SHA-pinned, .olean-seeded, 12 GiB / 600s bounded build:
obb broker plan-build Obend.Trailblaze.Polis Obend.Trailblaze.CathedralApex \
  --repo /Users/ember/dev/obend --host bb2 --max-rss-gb 12 --timeout-secs 600 --exec

# 3. Direct remote worktree verification on bb2 (after rsyncing worktree):
ssh bb2 'cd /home/build/obend/wt-lane/lean && SWARM_MEM_MAX=12G timeout --kill-after=10s 600s lake build Obend.Trailblaze.Polis'
```
