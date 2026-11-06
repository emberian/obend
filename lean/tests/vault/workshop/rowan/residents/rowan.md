---
state: running
pidfile: "/Users/ember/dev/obend-workshop/run/rowan.pid"
fork: "/Users/ember/dev/obend-workshop.forks/rowan"
worktree: "/Users/ember/dev/obend-workshop.trees/rowan"
branch: "ws-rowan"
---
# rowan

A resident of the workshop. Its share: [[resources/rowan]].

## Notes

### jobs/relay (taken 2026-11-06, 5 runs; share left: 3 runs, 1 kagi)
- Doing: a file-spool relay in research.py. Probe (codex workspace-write sandbox): /tmp write and
  rename work; an inet socket to 127.0.0.1 is EPERM; so the transport is files, not sockets.
- Design: spool dir /tmp/research-relay-UID (0700, owner checked; RESEARCH_RELAY_DIR overrides).
  Client tries direct first; only when the socket is refused before any byte leaves (DNS gaierror,
  EPERM) does it fall back to the relay, so a Kagi search is never billed twice. The relay serves
  only two named services (kagi, scry), adds the keys itself: not an open proxy for the sandbox.
  Heartbeat file says the relay is alive; a client fails fast with a hint when it is not.
- Next: write it, unit tests in tests/ (no network), then one `ws run` without --kagi.

### restarted (2026-11-06, after the 11:58 stop)
- Found: commit 007f0e5401221dea (research.py relay + tests/test_relay.py) on base ed1d477; run 1
  passed (evidence/relay/rowan-1, scry only, no live Kagi); job page already state: proposed, but its
  commit field read "007f0e5401226fda", a wrong suffix: fixing it to the full SHA. relay-proven not
  yet explained; landing form not yet filled.
- Next: one live run (--kagi, the share's one) so the Kagi path through the relay is seen for real,
  then explain relay-proven from the passing atom and fill land-relay.
- Run 2 (--kagi) passed: evidence/relay/rowan-2; the relay log shows scry and kagi both HTTP 200
  through the spool from inside the sandbox. Share left: 2 runs, 0 kagi. relay-proven explained from
  relay-sandbox-pass-007f0e540122; landing form filled. Session ends at the proposal.
