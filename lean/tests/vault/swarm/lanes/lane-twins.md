---
branch: lane-twins
agent: a024526b
brief: "briefs/lane-twins.md"
briefed_at: "2026-11-05T23:26:04.852Z root msg 727"
worktree: "/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/build"
builds: true
state: merged
commit: "d28abcf"
gate: "lake build Obend.Hardware.HDL Obend.Hardware.Compiler obend-emit-sv obend; bash hardware/sim/verify_sim.sh; bash apps/obend-risc/verilator/verify_risc.sh (the output shows: Build completed successfully (647 jobs))"
gate_evidence: "cv 01a1ad7d root msg 762"
machv: 0
stash: 0
addall: 0
killpat: 0
nopid: 0
dev: "c187703"
ancestor: true
---
# lane-twins

merge lane-twins: the four executable twins under Hardware/ are csimp rewrites with proofs (d28abcf)

Brief: [[briefs/lane-twins]]. Builds on [[machines/mac]].
