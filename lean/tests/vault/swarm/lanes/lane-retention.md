---
branch: lane-retention
agent: afa4d151
brief: "briefs/lane-retention.md"
briefed_at: "2026-11-06T04:32:37.612Z root msg 1379"
worktree: "/private/tmp/claude-501/-Users-ember-dev-obend/01a192c9-1860-748c-997d-d11e7c79a5a2/scratchpad/c2t7"
builds: true
state: merged
commit: "b50f09d"
gate: "lake build Obend.Vault Obend.Vault.Retention obend; python3 tests/vault/walkthrough.py --doc $d; python3 tests/vault/walkthrough.py; python3 tests/vault/crash.py (the output shows: Build completed successfully (624 jobs), walkthrough: 12 steps ok, walkthrough: 24 steps ok, walkthrough: 19 steps ok, walkthrough: 44 steps ok, walkthrough: 14 steps ok)"
gate_evidence: "cv 01a1ad7d root msg 1437"
machv: 0
stash: 0
addall: 0
killpat: 0
nopid: 0
dev: "185a0fd"
ancestor: true
---
# lane-retention

merge lane-retention: the right to forget as a declared contract; compaction to a checkpoint record; forget_sound, forget_refused_when_needed, late_correction_refused (b50f09d)

Brief: [[briefs/lane-retention]]. Builds on [[machines/mac]], [[machines/hbox]].
