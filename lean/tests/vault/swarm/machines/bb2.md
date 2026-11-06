---
host: dregg-build2
reach: "ssh bb2"
memcap: 100
repo: "/home/build/obend/repo"
repo_branch: lane-m5
law pidfile: linked.job == "running" implies not (linked.pidfile == "")
---
# bb2 (dregg-build2)

Hetzner ccx53, 32 cores, 122 GB; obend's since 2026-10-31; `swarm-build` with a 100 GB slice and a
box-wide cap of 20 Lean compilers. The obend clone at `~/obend/repo` is on branch `lane-m5` at 8c3aba8
(2026-10-31), not on `dev` as `~/swarm/MACHINES.md` and today's brief to lane-holetyping say
(`observations/probe.txt` line 17). Answered at 2026-11-06T17:49Z.

## jobs

None of the lanes has a detached job here now.
