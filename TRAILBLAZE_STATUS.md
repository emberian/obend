# Trailblaze consolidation status

This branch is not ready to claim STAGE_B_SEALED. Zero obligation classes does not establish completion of the security repairs.

## Implementation

- Eight modules consolidated into CathedralApex and StageBInstances; the six retired modules are deleted. Polis, LeanFpga, ZkStripe and ClusterGov namespaces remain.
- P0-01: dispatch checks decoded RDNA2 execution against reported and exact Ozaki outputs. VRAM openings check a verifier-pinned nonzero root, challenge-derived offsets and binary Merkle paths. Kernel execution inhabitedness remains under repair; this item is not fully verified.
- P0-06: disjoint symbol constructors, bounded injective interning, split-field projections, and length-framed graph serialization are implemented.
- P0-07: physical multi-net PIP paths and disjointness checks replace the precomputed bypass signal. Checked graph reduction starts at the lowered member; projection and erasure rules and a literal-member certificate are implemented, but the kernel disproves the current certificate after its first constructor step. P0-07 is therefore not complete.
- P1-04: exact 32-byte big-endian receipt encoding, injectivity, canonical payload checks and whole-struct uniqueness are implemented.
- P1-05: RFC 8259 response checking is enforced. Real notary/session authentication is still NOT threaded through auditZkStripeCallTree and auditCathedralTurn. The verifier adapter remains disconnected. This is an open security requirement.
- P1-06: pinned session mandate/root, accumulated new revocations, authority persistence, non-bypass and a pinned-budget trace bound are implemented. Persistent ramLog/memRoot and cross-turn Blum/Verkle continuity are still NOT implemented. This is an open security requirement.
- P1-07: explicit non-underflow guard and theorem, including named physical-audit refusal, are implemented.

## Verification

The two consolidated library modules passed remote kernel compilation at ec61eaa4. Subsequent graph erasure, authority persistence and execution inhabitedness changes require a new successful build. The latest narrow build at 4992935b failed in the RDNA2 execution inhabitedness proof. In the last build that reached StageBInstances, the authority proofs elaborated, but the two-step and full graph-reduction certificates evaluated to false. The full requested target set was attempted remotely at 90829cac and failed in CathedralApex. No local Lean or Rust build was run.

Pipeline check reports passed=true, total_obligations=0, open_stage_a_obligations=0, smuggled_sorry_count=0 and smuggled_axiom_count=0, but stage=UNDECLARED and ready_for_claimed=false.

Latest strict lint: 544 errors and 475 warnings repository-wide; zero errors in the two Trailblaze modules, whose only findings are two monolithic-module warnings. Repository-wide errors remain outside this lane. Newly broken documentation links were repointed. The two library modules have no file-wide expose or library test commands; declaration exposure is below the requested cap.

Harness check passed all 11 files. Apex check is 209/215 pending the reserved manifest replacements below. No reserved shared file was edited.

## M3 integration changes (not made in this lane)

- Obend.lean and Obend/Census.lean: replace retired Trailblaze imports with CathedralApex and StageBInstances, deduplicating existing imports.
- quarry/obend-apex.toml: module values for Polis, PolisBlum and LeanFpga become Obend.Trailblaze.StageBInstances; ZkStripe and ClusterGov become Obend.Trailblaze.CathedralApex. Preserve theorem namespaces.
- DeosSimplexOutboxSeamTest and Sel4MicrokitKernelTest: replace imports of Polis, PolisBlum and Obligations with StageBInstances.
- Teeth/Extracted/HardwareCryptoZkTeeth: replace imports of LeanFpga, Obligations and PolisBlum with StageBInstances. These reserved extracted teeth require coordinator integration.
- Worker 2 merge: swap StageBInstances' VerkleUmem import to BlumRam only after the replacement API is available.
- Stage-B trace callers must supply the new pinned-budget premise. The two-turn inhabitedness theorem now requires both 25 ≤ budget and budget ≤ 100. The FPGA normal-form wrapper takes an actual graph reduction certificate.

## Preserved apex names

- Obend.Trailblaze.Polis.apex_polis_deos_turn_safe
- Obend.Trailblaze.Polis.apex_polis_deos_trace_safe
- Obend.Trailblaze.LeanFpga.apex_lean_fpga_rung2_to_rung5
- Obend.Trailblaze.ZkStripe.apex_zkstripe_calltree_audit
- Obend.Trailblaze.ClusterGov.apex_verifiable_ai_cluster_step
- Obend.Trailblaze.CathedralApex.apex_cathedral_zkstripe_to_clustergov_sound
- Obend.Trailblaze.StageB.stageB_sel4_smmu_dma_noninterference
- Obend.Trailblaze.StageB.stageB_tulva_renyi_smudging_hiding
- Obend.Trailblaze.StageB.stageB_nextpnr_dual_tile_routing_sound
- Obend.Trailblaze.StageB.stageB_leaf_book_deltanet_normal_form
- Obend.Trailblaze.StageB.stageB_polis_deos_trace_sealed
- Obend.Trailblaze.StageB.stageB_lean_fpga_rung2_to_rung5_sealed
- Obend.Trailblaze.StageB.stageB_zkstripe_calltree_sealed
- Obend.Trailblaze.StageB.stageB_clustergov_ozaki_step_sealed
- Obend.Trailblaze.StageB.stageB_cathedral_seven_organ_trace_sealed

Additional authority theorem: Obend.Trailblaze.StageB.stageB_revocation_non_bypass.
