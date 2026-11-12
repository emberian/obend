---
name: obend-spec-exec-refinement
description: >-
  Guides verified Spec-to-Exec data and algorithmic refinement in Obend Lean 4 modules. Use this skill when pairing inductive or List specifications with unboxed ByteArray, Array UInt64, BitVec, sorted binary-search or merge-scan arrays, Simulates relations, or @[csimp] theorems.
---
<!-- obb-harness: v4 | id: skill:obend-spec-exec-refinement | sha256: 717b1a3c6f6de67ac1c820f5963e2760825a67963887065ef819fcb547d715bd -->
# Obend `Spec ↔ Exec` Verified Efficiency Playbook

In `Obend`, proofs reason over clean inductive structures while runtime verifiers execute unboxed $O(N)$ / $O(N \log N)$ loops. Never sacrifice proof clarity for array index arithmetic, and never ship quadratic `List` traversals or `Nat` digests on hot runtime paths.

## 1. Canonical Two-Tier Carrier Pairing

| Domain Object | `Spec` Carrier (Proof-Friendly) | `Exec` Carrier (Unboxed Runtime) | Bridge Theorem |
| :--- | :--- | :--- | :--- |
| Wire / JSON / HTTP payloads | `List UInt8` | `ByteArray` | `(lexExec bs).toList = lexSpec bs.toList` |
| 256-bit Merkle / AEAD digests | `List UInt8` (len 32) / `BitVec 256` | `BitVec 256` / `ByteArray` / `Array UInt64` (size 4) | `toBytes_inj` + `Collision H` |
| Cubical 3-cube face ideals | `Fin 3 → Fin 3 → Fin 3 → Bool` | `BitVec 27` (`FaceIdeal3`) + dual-tile `BitVec 16 × BitVec 16` | `decode_encode` + `eval_eq` |
| Offline/online memory logs | `List MemOp` (`countMemOp`) | Sorted `Array MemOp` (`checkSortedBagEqExec`) | `verifyMemoryExec_sound` |
| Static key / capability tables | `List (Key × Val)` (`List.lookup`) | Sorted `Array (Key × Val)` (binary search) | `binSearch_eq_lookup` (under `Pairwise (· < ·)`) |
| Exact integer / fixed-point dot products | `List Int` (`intDot`, `sliceSum`) | `Array Int` / unboxed `Array UInt64` (`intDotExec`) | `intDotExec_eq_intDot` |

## 2. Sorted Binary Search & Linear Merge-Scan Over $O(N^2)$ `List.filter`

- **Multiset / Permutation Bag Checks:** Never run `List.filter` per element ($O(N^2)$). Define `countMemOp (target : MemOp) (log : List MemOp) : Nat` as the `Spec` multiplicity function, sort `(addr, timestamp)` into `Array MemOp` in $O(N \log N)$, and verify equality in a single $O(N)$ merge-scan (`checkSortedBagEqExec`) paired with `checkSortedBagEqExec a b = true → ∀ op, countMemOp op a.toList = countMemOp op b.toList`.
- **Dictionary / Allowlist Lookups:** Store static routing, capability, or symbol tables in strictly sorted `Array`s checked once for strict monotonicity (`isStrictlySorted arr = true`), then execute $O(\log N)$ binary search proven equivalent to `Spec` `List.lookup`.

## 3. Canonical Length-Prefixed Byte Framing

Never concatenate variable-length fields directly (`req ++ resp`) inside commitments. Always frame variable-width slices with explicit big-endian length prefixes and canonical width bounds:

```lean
def frameBytes (xs : List UInt8) : List UInt8 :=
  be 4 xs.length ++ xs
```

Pair `frameBytes` with `frameBytes_append_inj` (`xs₁.length < 2^32 → xs₂.length < 2^32 → frameBytes xs₁ ++ rest₁ = frameBytes xs₂ ++ rest₂ → xs₁ = xs₂ ∧ rest₁ = rest₂`) so composite Merkle preimages decompose deterministically.

## 4. `Simulates` & `@[csimp]` Wiring

- **Same-Type Fast Replacement (`@[csimp]`):** When `specFn : α → β` and `execFn : α → β` share identical signatures, prove `@[csimp] theorem specFn_eq_execFn : @specFn = @execFn` so compiled executables invoke `execFn` automatically while kernel proofs unfold `specFn`.
- **Refined-Carrier Simulation (`Simulates`):** When `Exec` changes representation (`ByteArray` vs `List UInt8`, `Array UInt64` vs `List Nat`), define an explicit abstraction map `α_abs : ExecState → SpecState` (or `Simulates : SpecMachine → ExecMachine → Prop`) and prove step/acceptance commutation:
  `α_abs (stepExec s) = stepSpec (α_abs s)` and `acceptExec s = acceptSpec (α_abs s)`.

## 5. Validation Checklist

1. Confirm zero narrow-digest or `Nat` digest regressions: `obb lint --repo <repo> --rule lean/narrow-digest-weld --strict`.
2. Confirm `Exec` helpers stay encapsulated behind `public section` (`≤ 12` `@[expose]` per file): `obb lint --repo <repo> --strict --strict-expose`.
3. Build and test equivalence theorems remotely on `bb2` (`SWARM_MEM_MAX=12G`, `timeout 600s`).
