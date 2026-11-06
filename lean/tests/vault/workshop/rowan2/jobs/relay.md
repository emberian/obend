---
state: proposed
commit: "ad3a6dc965bdeaa0a94148274f591bc90a68e7f4"
on: "751b497"
suite: "evidence/relay/rowan-4"
assignee: rowan
open: 1
runs: 5
spent: 4
base: "751b497"
law suite: new.state in ["proposed", "landed"] implies not (new.suite == "")
---
# Kagi and Scry from a sandbox

`research.py`'s Kagi and Scry calls fail from inside a sandbox with no network, such as Codex's
workspace-write sandbox, which every Astra run uses:

    codex sandbox -c 'sandbox_mode="workspace-write"' -- python3 research.py scry whoami
    error: <urlopen error [Errno 8] nodename nor servname provided, or not known>

Both Astra runs of 2026-11-06 fell back to web search because of it. Inside that sandbox a process
can read everything, write its working directory and `/tmp`, and open no socket at all; outside it,
the same user has the network. Make the unchanged commands (`research.py scry …`,
`research.py kagi …`) work from inside such a sandbox, with something outside the sandbox carrying
the request: `python3 research.py relay serve` (foreground, run outside the sandbox; the acceptance
script starts it in the background and stops it by its PID). Direct calls keep working where there
is a network.

Proved by [[tests/relay/sandbox]] and, since [[jobs/harness]] landed, by [[tests/relay/suite]]: a
proposal names the evidence page of its passing suite run (`suite:`). Budget from the taker's share ([[resources/rowan]]). On landing,
its one `open` moves to [[landed/relay]].
