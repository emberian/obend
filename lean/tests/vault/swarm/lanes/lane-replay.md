---
branch: lane-replay
agent: a4c1c9cd
brief: "briefs/lane-replay.md"
briefed_at: "2026-11-06T00:26:54.954Z root msg 837"
worktree: "/private/tmp/claude-501/-Users-ember-dev-obend/01a192c9-1860-748c-997d-d11e7c79a5a2/scratchpad/c2t7"
builds: true
state: merged
commit: "ef8b52c"
gate: "lake build Obend.Vault Obend.Vault.Log Obend.Vault.Replay obend Obend.Ledger.Cli +vault.Branch; python3 tests/vault/walkthrough.py; python3 tests/vault/walkthrough.py --doc tests/vault/FORMS.md; python3 tests/vault/walkthrough.py --doc tests/ledger/WALKTHROUGH.md; python3 tests/vault/crash.py (the output shows: Build completed successfully (626 jobs), walkthrough: 44 steps ok, walkthrough: 19 steps ok, walkthrough: 24 steps ok, walkthrough: 14 steps ok)"
gate_evidence: "cv 01a1ad7d root msg 1259"
machv: 0
stash: 0
addall: 0
killpat: 0
nopid: 0
dev: "527d901"
ancestor: true
---
# lane-replay

merge lane-replay: the vault's world is the replay of its log; forms, merge and resolve are turns; crash recovery as replay of the well-linked prefix (ef8b52c)

Brief: [[briefs/lane-replay]]. Builds on [[machines/mac]], [[machines/hbox]].
