---
law states: new.state in ["idle", "running", "stopped", "away"]
law fields: not (new.fork == "") and not (new.worktree == "") and not (new.branch == "")
law pidfile: new.state == "running" implies not (new.pidfile == "")
---
A resident of the workshop: an agent with its own page, its own fork of this vault (its membrane:
it works there, disconnected, and comes back as a merge judged at the tip), its own worktree of
`~/swarm` on its own branch. Its page is its notebook: what it is doing, what it knows, what it would
do next. A running resident names its PID file.
