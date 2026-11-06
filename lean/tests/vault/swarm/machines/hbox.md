---
host: hbox
reach: "ssh hbox"
memcap: 48
law pidfile: linked.job == "running" implies not (linked.pidfile == "")
---
# hbox

Home server, i9-12900, 123 GB, ZFS. Builds through `swarm-build` (`SWARM_MEM_MAX=48G` for a cold
obend build). Shared today by three lanes and another session. Answered at 2026-11-06T17:49Z
(`observations/probe.txt`).

## jobs

None of the lanes has a detached job here now.
