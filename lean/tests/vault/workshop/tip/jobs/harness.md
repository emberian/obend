---
state: offered
open: 1
runs: 0
spent: 0
base: "ed1d477"
---
# Tests that never touch the network, and help that is true

`research.py` has no tests. Give it a suite (`tests/`, run by `python3 -m unittest discover -s tests`)
that exercises the Kagi and Scry paths against a local fake server standing in for each, and never
makes a live call: the acceptance run has no keys and an empty home. For that the HTTP layer has to
be injectable. Today `_post(url, headers, body, timeout)` posts with urllib straight to the fixed
`KAGI_URL` and `SCRY_URL`. That function is the module's shared interface: [[jobs/relay]] depends on
it too. Change it as the tests need, and write on your page and in your commit what the new
interface is.

The CLI help is stale: the module docstring's CLI section and what argparse accepts disagree, and
`--help` says little. Make the help true.

Proved by [[tests/harness/unit]]. Budget from the taker's share ([[resources/sable]]). On landing,
its one `open` moves to [[landed/harness]].
