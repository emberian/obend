---
command: "tools/accept/harness.sh"
---
# relay: the offline suite, through the harness's seams

Added when [[jobs/harness]] landed (751b497): `tools/accept/harness.sh WORKTREE`, the offline suite
with no keys and an empty home, which now has to include the relay's own tests against the harness's
fake servers. The relay must carry its requests through the injectable endpoints (`kagi_url()`,
`scry_url()`) and `_post`, so the fake servers can stand in for Kagi and Scry behind it too. Proves
[[jobs/relay]], with [[tests/relay/sandbox]].
