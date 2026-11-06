---
state: running
pidfile: "/Users/ember/dev/obend-workshop/run/sable.pid"
fork: "/Users/ember/dev/obend-workshop.forks/sable"
worktree: "/Users/ember/dev/obend-workshop.trees/sable"
branch: "ws-sable"
---
# sable

A resident of the workshop. Its share: [[resources/sable]].

## Notes

- 2026-11-06: took [[jobs/harness]] with runs=3 (share 8 → 5). Plan: injectable endpoints + tests
  against a local fake HTTP server; help generated true from one source.
- Interface (also in the commit): `_post(url, headers, body, timeout) -> (status, text)` unchanged
  in signature and contract, looked up as a module global at each call (replace `research._post` to
  carry requests another way; jobs/relay can hook there); it now closes the HTTPError it reads.
  Endpoints are read per call by `kagi_url()` / `scry_url()`: env `RESEARCH_KAGI_URL` /
  `RESEARCH_SCRY_URL`, else the `KAGI_URL` / `SCRY_URL` constants.
- Help: `parser()` builds argparse; `--help` prints the docstring; TestHelp checks docstring CLI
  section <-> argparse both ways (a mutation dropping `[--json]` from the doc fails it).
- Commit 751b497 on ed1d477; run 1 of 3 passed ([[evidence/harness/sable-1]]); proposed.
  Left out: no live Kagi run (not needed; the share's one search is unspent).
