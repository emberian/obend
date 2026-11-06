---
branch: lane-widths2
agent: a024526b
brief: "briefs/lane-widths2.md"
briefed_at: "2026-11-05T22:29:27.646Z root msg 619"
worktree: "/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/build"
builds: true
state: merged
commit: "3e85d7b"
gate: "bash hardware/sim/verify_sim.sh; bash apps/zk-ntt/verilator/verify_zk_ntt.sh (the output shows: [PASS] hardware/sim, [PASS] 8-round sumcheck with the hardware transcript (255 pair cycles; challenges, accumulators and claims match the Lean golden), [PASS] apps/zk-ntt) (in the lane worktree, before the merge)"
gate_evidence: "cv 01a1ad7d root msg 687"
machv: 0
stash: 0
addall: 0
killpat: 0
nopid: 0
dev: "3457109"
ancestor: true
---
# lane-widths2

merge lane-widths2: Reflect reduces in the kernel inside a module; emitter starts; apps emit again; lower_to_rtl_sat_sound_width (3e85d7b)

Brief: [[briefs/lane-widths2]]. Builds on [[machines/mac]].
