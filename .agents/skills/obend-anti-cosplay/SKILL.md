---
name: obend-anti-cosplay
description: >-
  Identifies and eliminates the 10 formal-verification cosplay failure modes in Obend Lean 4 modules. Use this skill when authoring or auditing Stage-A *Obligations classes, Judge instances, cryptographic commitments, hardware structs, stateful lexers, runtime data structures, or compiler passes.
---
<!-- obb-harness: v4 | id: skill:obend-anti-cosplay | sha256: ad57e94052872193b873d411634f43de3eee2f1738d4d255081ec97707ac0d95 -->
# Obend Anti-Cosplay Field Guide: 10 Mistakes Models Like to Make

Every failure mode below arises when optimizing for surface compilation instead of genuine mathematical or operational content. Treat all 10 as hard blockers in `Obend`.

## The 10 Mistakes Models Like to Make

### 1. Tautological Stage-A `*Obligations` Fields (`lean/obligation-tautological-field`)
- **Failure Mode:** Writing placeholder propositions inside `class *Obligations : Prop` that sound ambitious in identifiers/docstrings while stating propositional tautologies or micro-bounds:
  - Equality congruence: `sameOpeningZeroKnowledge : ∀ (commitA commitB : BitVec 256), commitA = commitB → commitA.toNat = commitB.toNat`.
  - Conjunction repackaging: `teeHardwareRootAttested : ∀ step, step.flopsUsed ≤ step.flopsCap → step.batchCallTreeRoot ≠ 0 → step.flopsUsed ≤ step.flopsCap ∧ step.batchCallTreeRoot ≠ 0` (`P → Q → P ∧ Q`).
  - Lattice meet elimination: `siliconSimpKernelProofSound : ∀ (φ ψ : CofibLUT16), (φ.meet ψ).implies φ = true`.
  - Scalar `> 0` consequence under a `Gkr`/`ZeroKnowledge`/`Attested`/`IsaEquiv` name: `kernelArithmeticGkrSound : ∀ b, checkNoWrap b = true → b.modulusP > 0`.
  - Non-existential `*Extract` fields that universally quantify the witness (`∀ tree, verify tree = true → ...`) instead of extracting `∃ tree, ...`.
- **Fix:** Prove trivial algebraic facts directly as ordinary lemmas (never open obligations), and state the exact semantic, ISA, or cryptographic soundness/extraction statement in `*Obligations`.

### 2. Dropped-Field Commitments Making Stage-B Injectivity `False`
- **Failure Mode:** Omitting a structural field from a hash preimage (`HttpsSessionNode.serverDomain` dropped in `callTreeDigestBytes`) while locking Stage-A `callTreeDigest H t₁ = callTreeDigest H t₂ → t₁ = t₂ ∨ Collision H`. Two nodes differing only in `serverDomain` have **identical** preimages (`pre₁ = pre₂`), so `Collision H` (`pre₁ ≠ pre₂ ∧ H pre₁ = H pre₂`) is `False` AND `t₁ = t₂` is `False` — rendering Stage B mathematically uninhabitable.
- **Fix:** Length-frame **every** constructor tag and payload field (`frameBytes domain.toUTF8.toList` with canonical `< 2^32` / `< 2^64` width guards) and constructively prove `callTreeDigestBytes_binding` (`if hPre : pre₁ = pre₂` on `List UInt8`, `0 Classical`) *before* sealing Stage A.

### 3. Domain-Collapse Encodings (`∂𝕀 = 𝕀`)
- **Failure Mode:** Modeling cubical cofibration face lattices as 4-variable Boolean truth tables (`CofibLUT16` over `BitVec 16`, `{0,1}^4`), where `(varEq0 v).join (varEq1 v) = top` collapses the boundary `(i = 0) ∨ (i = 1)` onto the entire interval (`∂𝕀 = 𝕀`).
- **Fix:** Encode cubical face ideals over the 3-element partial cube `{0, 1, *}^3` (`FaceIdeal3` as `BitVec 27`, mapping `(p₀, p₁, p₂) : Fin 3 × Fin 3 × Fin 3` to `p₀ + 3*p₁ + 9*p₂` with interior `(2,2,2)` at bit `26`), and prove `(varEq0 v).join (varEq1 v) ≠ top` + `#tooth`.

### 4. Host-Ghost Fields Smuggled into Hardware Structs
- **Failure Mode:** Embedding unbounded Lean host heap types inside synthesizable hardware structures (e.g., `CamSlotEntry.expr : KExpr` alongside a 64-bit `CamWord64`, 1-character symbol hashes colliding `"a"` and `"b"`, or quadratic pairing encodings overflowing 64 bits at 181 nodes).
- **Fix:** Keep hardware carrier structs (`CamSlotEntry`, `TileConfig`, `DprSlot`) strictly fixed-width (`BitVec`, `UInt64`, bounded `Fin`) and relate them to host `KExpr` syntax via an external simulation/indexing table.

### 5. `False ∨ False` Cryptographic Reduction Vacuity & Narrow Welds
- **Failure Mode:** Discharging dual-assumption cryptographic reductions (`HashBinding ∨ LatticeHardness`) where uninhabited parameters collapse both branches, or comparing only limb `0` (`digest[0] == expected[0]`, `≤ 64`-bit scalar stand-in, `lean/narrow-digest-weld`).
- **Fix:** Bind full 256-bit commitments (`BitVec 256`, 32-byte `ByteArray`, or all 4×`UInt64` limbs) and accompany every reduction hypothesis with a constructive inhabitedness witness (`lean/uninhabited-premise-risk`).

### 6. Unbound Fiat-Shamir Public Instances
- **Failure Mode:** Computing Fiat-Shamir challenges from prover round commitments alone without absorbing the domain separator and complete length-framed public statement/instance into the transcript sponge.
- **Fix:** Absorb protocol domain tag + length-framed public statement + prior round commitments into the transcript state before squeezing every verifier challenge.

### 7. `Fragment := False` / `refutes := false` Judge Evasion (`lean/judge-empty-fragment`)
- **Failure Mode:** Implementing `Obend.Judge` (`SilverWorkflow.toJudge`) with `Fragment := fun _ => False` and `refutes := fun _ => false` so `complete` and `refuted` discharge by `cases` without proving completeness or refusal soundness on any input.
- **Fix:** Equip workflows with an inhabited `DecidableFragment : W → Prop` and `silverComplete : ∀ w, DecidableFragment w → Spec w → runValid w = true`, setting `Fragment := DecidableFragment` and `refutes := fun _ => true`.

### 8. Stateless Lexer / String-Escape Boundary Smuggling
- **Failure Mode:** Scanning raw `{`, `}`, `[`, `]` bytes in `lexJsonVpaSymbols` without string/escape state, falsely rejecting valid `{"note":"unmatched } inside string"}` and accepting malformed `{"bad":"\"}"}` where `\"` smuggles an unclosed string past structural framing.
- **Fix:** Track explicit `(inString : Bool, escaped : Bool)` state in both `Spec` (`List UInt8`) and `Exec` (`ByteArray`) lexers, and lock behavior with positive + negative `#tooth` witnesses.

### 9. $O(N^2)$ Linked-List Runtime Representations Without `Spec ↔ Exec`
- **Failure Mode:** Running quadratic `List.filter` multiset equality (`List MemOp`) or boxed `List Int` inner products on hot runtime audit paths.
- **Fix:** Keep `List` definitions as the `Spec` layer and pair them with $O(N)$ / $O(N \log N)$ `Array` / `ByteArray` `Exec` checkers (`checkSortedBagEqExec`, `intDotExec`, sorted binary-search tables) + proved `Spec ↔ Exec` equivalence.

### 10. Summary-Stub Compilers & Frame-Escape Blind Spots
- **Failure Mode:** Writing a "lowering" function (`lowerBookSummaryToDeltaNet`) that counts declaration headers and emits a static 2-node stub while ignoring `Obend.Leaf.Expr` AST bodies, or computing `LeafDef.reads` without a `NoEscapingSelf` guard rejecting bare `LeafExpr.var "self"`.
- **Fix:** Structurally compile every AST constructor (`nat`, `var`, `app`, `letE`, projections), wire bound variables linearly (`era` for 0 uses, `replicator` trees for $>1$ uses), and enforce syntactic non-escape guards in frame theorems.

## Precondition Narrowing / Bug-Steering & Single-Turn Harnesses (`lean/single-sequence-harness`)

- **Single-Turn Reset Blindness:** Proving `theorem apex_*_turn_safe` or `theorem apex_*_turn_sound` over a single `*Turn` carrier leaves multi-turn state-accumulation hazards completely unverified — growing `RevokedSet` tables, depleting `Mandate` budgets, and persistent `UMem` aliasing only manifest across arbitrary turn sequences. Always pair step lemmas with a multi-turn trace/reachability invariant (`List *Turn`, `Reach`, `SafeWP`, `ValidTrace`, or `MultiTurnHoare`) in the same module; `obb lint --strict-harnesses` and `obb apex check` reject isolated single-turn apex theorems.
- **Precondition Narrowing & Bug-Steering:** Never "close" an open-world environment harness by tightening transition filters to silently skip states where bugs trigger, or by restricting resource handles to singleton instances. Every open-world environment filter/harness must pair safety with an explicit **environment completeness theorem** (`skip_implies_contract_violation` and multi-handle reachability), proving that any skipped/rejected step genuinely violates the external caller contract and that distinct concurrent handles remain reachable.

## Verification Runbook

1. Run static anti-cosplay, harness-completeness & encapsulation lints locally (read-only Rust binary, zero Lean invocation):
   `obb lint --repo <repo> --strict --strict-expose --strict-harnesses`
2. Verify Stage-A / Stage-B obligation pipeline discipline and multi-turn apex wiring:
   `obb pipeline check --repo <repo> --strict && obb apex check --repo <repo>`
3. Verify `#tooth` mutation sensitivity and `#audit_claim_contract` / `#print axioms` remotely on `bb2`:
   `obb broker plan-build <Module> --repo <repo> --host bb2 --max-rss-gb 12 --timeout-secs 600 --exec`
