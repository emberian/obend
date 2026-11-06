---
command: "tools/accept/relay.sh"
---
# relay: from inside the sandbox

`tools/accept/relay.sh WORKTREE` from this workshop: starts `python3 research.py relay serve` in the
background outside any sandbox, then inside `codex sandbox -c 'sandbox_mode="workspace-write"'` runs
`python3 research.py scry whoami` (a free Scry call; it must print the account) and, only when the
run is marked live (`--kagi`, one unit of the share's `kagi`), `python3 research.py kagi "obend" -n 1`
(it must print a result). Then `python3 -m unittest discover -s tests` if the worktree has tests.
The relay is stopped by its PID. Passing: every step exits 0. Proves [[jobs/relay]].
