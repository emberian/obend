---
name: obend-trailblaze-promotion
description: >-
  Executes the Stage-A (*Obligations) to Stage-B (0 open obligations) Trailblaze organ promotion workflow, pre-lock Collision H injectivity proofs, scar-free in-place replacement, and quarry/obend-apex.toml registration. Use this skill when designing, overhauling, or sealing Trailblaze organs.
---
<!-- obb-harness: v4 | id: skill:obend-trailblaze-promotion | sha256: 0e2167e9ce0397ac0b242153fb3939e386a5de6905b7c6e8faf2006b4bfcb812 -->
# Obend Trailblaze Promotion Runbook (`Stage A` $\to$ `Stage B`)

Every `Obend.Trailblaze` organ begins at **Stage A** (`STAGE_A_LOCKED`: `0 sorry`, `0 axiom`, explicit `[<Organ>Obligations]` typeclass parameters) and retires by promotion to **Stage B** (`STAGE_B_SEALED`: `0` open unproved obligations).

## Step 1: Pre-Lock Satisfiability & Preimage Injectivity Audit

Before locking any Stage-A `class <Organ>Obligations : Prop`:
1. **Prove Commitment Preimage Injectivity First:** If any theorem claims `digest H x = digest H y → x = y ∨ Collision H`, write out the canonical domain guard (`CanonicalNode x`: bounded field widths `< 2^64` / `< 2^32`) and **prove** `digest_binding` constructively (`0 Classical`) right away. Never defer preimage framing to Stage B, or a dropped field (`HttpsSessionNode.serverDomain`) will make Stage B `False`.
2. **Witness Every Premise:** Include at least one constructive `example`, `#guard`, or `*_complete` theorem proving `audit*` / `verify*` admits valid multi-hop inputs (`lean/uninhabited-premise-risk`).
3. **Complete `SilverWorkflow` $\to$ `Judge` Bridge:** Populate `DecidableFragment` and `silverComplete` on `SilverWorkflow` instances so `SilverWorkflow.toJudge` carries a real `Fragment` and `refutes := fun _ => true` (`0` `lean/judge-empty-fragment` warnings).

## Step 2: Lock Stage-A Interface Cleanly

Verify the Stage-A lock passes every anti-cosplay and cone gate:

```bash
obb lint --repo <repo> --strict --strict-expose
obb pipeline check --repo <repo> --strict
obb cone --repo <repo>
```

- Confirm `0` `lean/obligation-tautological-field` errors, `0` `lean/excessive-decl-expose` errors, and `PipelineStage == STAGE_A_LOCKED`.
- Keep `<Organ>ObligationManifest` entries synchronized 1-to-1 with remaining open fields in `class <Organ>Obligations`.

## Step 3: Scar-Free In-Place Discharge (*"Nothing lands beside; everything replaces"*)

When promoting an obligation field from Stage A to Stage B:
1. **Prove the Unconditional Theorem In Place:** Prove the real theorem directly in the organ module (or a private `Proofs/` submodule) with `0 sorry`, `0` custom `axiom`s, and `0 native_decide`.
2. **Delete Discharged Obligation Fields:** Remove the proved field from `class <Organ>Obligations` and `<Organ>ObligationManifest`, wiring the proved theorem directly into `apex_<organ>_*` (prefer direct unconditional theorems over keeping wrapper typeclasses!).
3. **Or Seal via Non-Cosplay Production Instance:** When a multi-module boundary requires keeping the class (`STAGE_B_SEALED`), provide `instance : <Organ>Obligations ProdCarrier` backed by substantive multi-line domain theorems (`0` `lean/obligation-projection-cosplay` errors; never instantiate on `Unit`/`Bool`/`Nat`).

## Step 4: `quarry/obend-apex.toml` Registration & Final Seal

1. Register or update the organ's apex theorem in `<obebuilder>/quarry/obend-apex.toml` (`subsystem`, `module`, `theorem`, `organ`).
2. Run the full verification battery (static local `obb` + remote `bb2` kernel build):
   ```bash
   obb lint --repo <repo> --strict --strict-expose
   obb pipeline check --repo <repo> --strict
   obb apex check --repo <repo> --manifest <obebuilder>/quarry/obend-apex.toml
   obb harness check --repo <repo>
   ssh bb2 'cd /home/build/obend/dev/lean && SWARM_MEM_MAX=12G timeout --kill-after=10s 600s lake build Obend.Trailblaze.CathedralApex'
   ```
