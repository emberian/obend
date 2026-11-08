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

### repair (2026-11-06, after the refusal; log/passage.log at the tip)
- jobs/harness landed at 751b497 (kagi_url()/scry_url(), _post looked up per call, tests/fakeserver.py);
  jobs/relay's base moved to 751b497 and gained law `suite` (tests/relay/suite = tools/accept/harness.sh).
  relay-proven was defeated by relay-base-moved; my commit conflicts in research.py.
- Plan: merge workshop (751b497) into ws-rowan (new merge commit; 007f0e5 stays reachable as a
  parent), relay resolves endpoints with kagi_url()/scry_url() and sends through the global _post;
  the no-network classification moves out of _post into _request so a replaced _post is still
  classified. Relay tests move onto tests/fakeserver.py. Then pull the tip into the fork
  (ws obend merge), run sandbox + suite (2 of the 3 left runs), propose with suite:.
- Done: ws obend merge of the tip pulled tests/relay/suite but not jobs/relay (my refused page
  stayed), so I wrote jobs/relay to the tip's terms by hand (base 751b497, law suite, the body's
  suite sentence), observed relay-base-moved and defeated my old explanation `rowan` by it.
- Code: ad3a6dc, a merge of workshop (751b497) into ws-rowan; 007f0e5 is its other parent.
  Relay through kagi_url()/scry_url() and _post; no-network judged in _request; tests on fakeserver.
- Runs 3 (sandbox, evidence/relay/rowan-3) and 4 (suite, evidence/relay/rowan-4) passed on ad3a6dc.
  One run left. Proposed with suite: evidence/relay/rowan-4; landing form filled again.
- Top-up: the reviewer's suite run at the tip was refused (budget spent by its sandbox run 5). Topped jobs/relay up by 1 run from my share (receipt d49e49f8917966a3): share 3 -> 2, job runs 5 -> 6. One run is all the reviewer's suite run needs.
