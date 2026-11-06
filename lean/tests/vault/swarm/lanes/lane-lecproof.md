---
branch: lane-lecproof
agent: aee107e1
brief: "briefs/lane-lecproof.md"
briefed_at: "2026-11-05T23:13:00.996Z root msg 685"
worktree: "/private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/linear"
builds: true
state: merged
commit: "6fc22b2"
gate: "lake build Obend.Hardware.YosysLec obend-emit-sv; bash apps/zk-ntt/verilator/verify_zk_ntt.sh (the output shows: Build completed successfully (584 jobs), [PASS] apps/zk-ntt)"
gate_evidence: "cv 01a1ad7d root msg 750"
machv: 0
stash: 0
addall: 0
killpat: 0
nopid: 0
dev: "e222ea7"
ancestor: true
---
# lane-lecproof

merge lane-lecproof: the LEC's Lean half is a proved model, emitExprSmt2_sound (6fc22b2)

Brief: [[briefs/lane-lecproof]]. Builds on [[machines/mac]].
