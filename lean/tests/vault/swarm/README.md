# The swarm's workspace, 2026-11-06

An obend vault (`obend open`) holding the swarm that builds obend: one page per lane (`lanes/`), the
brief each lane was sent (`briefs/`, verbatim from the root's transcript), the boxes it builds on
(`machines/`), the coordinator's seat (`seats/`), the lanes merged on dev (`DEV.md`), the quests
(`QUESTS.md`), the reasons the swarm keeps about itself (`obend reasons status`), the doctrine as a
genealogy of judges (`doctrine/`), and what the vault refused while it was being used (`FINDINGS.md`).

The data came from the harness transcripts (`tools/extract.py`, over `cv show --json` of session
01a1ad7d and its sub-agents) and from git; the vault was built in the order things happened
(`tools/populate.py`). Each lane's worktree is a declared fork under `../obend-swarm.forks/`.
