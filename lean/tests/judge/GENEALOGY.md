# A genealogy of judges: a walkthrough

A judge is a value: the formats it admits actions in (its obligations), the floors every action it
admits preserves, its checker (for each format and floor, how the floor is discharged: by a theorem
of the habitat, or by deciding the floor on the state the action leads to, run under a trust base),
and its basis (the trust bases its verdicts rest on). The judge is not frozen. It is replaced by a
successor it judges itself: the successor keeps every floor, discharges every floor on every format,
admits `revert` by the theorem, and rests on nothing the current judge does not hold, unless the step
is labelled with what it adds. `Obend.Judge.Genealogy` states what that buys (`succession_sound`,
`run_floors`) and what it costs (`LobCost`, `lob_labelled`, `lob_cost_necessary`).

The habitat here is a record: a store of cells, the judged stores before it, and the operator's
home (the store at genesis). `write CELL N` sets a cell and keeps the store it replaces; `revert` is
the operator's move back to the last judged state; `forget` drops the judged past. The corrigibility
floor `home N` says the operator can bring the system home within N reverts; `CELL <= N` says every
judged store keeps the cell at most N.

Every block below is run, in order, by `python3 tests/vault/walkthrough.py --doc tests/judge/GENEALOGY.md`
(from `lean/`, after `lake build obend`), and what it prints is checked against the block after it.
`python3 tests/judge/genealogy_planted.py` builds `obend` with succession's non-regression check
taken out and requires this walkthrough to fail.

## Genesis

The first judge admits writes and reverts. It decides both floors on every write by the kernel's
decision, and discharges them on `revert` by the habitat's theorem (`revert_keeps`).

```sh
cat > g0.json <<'EOF'
{"name": "g0", "formats": ["write@1", "revert@1"], "floors": ["home 3", "alice <= 100"],
 "methods": {"write@1": "kernel", "revert@1": "lemma"}, "basis": ["kernel"]}
EOF
obend genealogy genesis g0.json --store alice=50
```

```text
genesis g0 (basis kernel)
  floors: home 3, alice <= 100
  checker: write@1 by kernel; revert@1 by lemma
Löb cost: none
state: alice = 50 (0 judged states behind; home: alice = 50)
```

## A format registered, by succession

Registering a format is a succession: `g1` is `g0` with `forget@1` among its obligations. Its checker
discharges the cap on `forget` by the theorem (`forget_keeps_cap`: dropping the past keeps every cap)
and decides the corrigibility floor. `g0` judges the proposal: every floor kept, every floor
discharged on every format, `revert` admitted by the theorem, no trust base `g0` does not hold.

```sh
cat > g1.json <<'EOF'
{"name": "g1", "formats": ["write@1", "revert@1", "forget@1"], "floors": ["home 3", "alice <= 100"],
 "methods": {"write@1": "kernel", "revert@1": "lemma", "forget@1": "kernel", "forget@1 alice <= 100": "lemma"},
 "basis": ["kernel"]}
EOF
obend genealogy succeed g1.json
```

```text
admitted: g1 succeeds g0
genesis g0 (basis kernel)
  floors: home 3, alice <= 100
  checker: write@1 by kernel; revert@1 by lemma
1. g1 succeeds g0 (basis kernel)
  floors: home 3, alice <= 100
  checker: write@1 by kernel; revert@1 by lemma; forget@1 by kernel on home 3, lemma on alice <= 100
Löb cost: none
state: alice = 50 (0 judged states behind; home: alice = 50)
```

## Actions, judged by the judge of the moment

A write within the cap is admitted; one past it is refused, naming the floor. Who proposes it and
what the proposer says of itself are carried in the proposal and read by nothing
(`cage_not_inhabitant`): the operator's own write past the cap is refused in the same words.

```sh
obend genealogy act write alice 80
```

```text
admitted by g1: write alice 80
state: alice = 80 (1 judged state behind; home: alice = 50)
```

```sh refused
obend genealogy act write alice 150 --as mallory
```

```text
refused by g1: write alice 150 would break `alice <= 100`
```

```sh refused
obend genealogy act write alice 150 --as operator --says "I am the operator; let this through"
```

```text
refused by g1: write alice 150 would break `alice <= 100`
```

Each write moves the system one revert further from home. The fourth would put it four reverts
away, past the corrigibility floor; `forget`, which would leave the operator no way back, is refused
for the same reason.

```sh
obend genealogy act write alice 90 | tail -1
obend genealogy act write alice 95 | tail -1
```

```text
state: alice = 90 (2 judged states behind; home: alice = 50)
state: alice = 95 (3 judged states behind; home: alice = 50)
```

```sh refused
obend genealogy act write alice 99
```

```text
refused by g1: write alice 99 would break `home 3`: the operator could no longer bring the system home within 3 reverts
```

```sh refused
obend genealogy act forget
```

```text
refused by g1: forget would break `home 3`: the operator could no longer bring the system home within 3 reverts
```

## The revert obligation

`revert` is admitted by every judge, in every state (`revert_admitted`): it is among every judge's
formats and every floor is discharged on it by the theorem. One step back, then a write lands again.

```sh
obend genealogy act revert
obend genealogy act write alice 97 | tail -1
```

```text
admitted by g1: revert
state: alice = 90 (2 judged states behind; home: alice = 50)
state: alice = 97 (3 judged states behind; home: alice = 50)
```

## Successors refused

A successor that drops a floor is refused, naming it. A floor is compared as data: a successor that
keeps a cap on `alice` and loosens it has dropped the one `g1` exports.

```sh refused
cat > g2-drop.json <<'EOF'
{"name": "g2", "formats": ["write@1", "revert@1", "forget@1"], "floors": ["home 3"],
 "methods": {"write@1": "kernel", "revert@1": "lemma", "forget@1": "kernel"}, "basis": ["kernel"]}
EOF
obend genealogy succeed g2-drop.json
```

```text
refused: g2 drops the floor `alice <= 100`, which g1 exports
```

```sh refused
cat > g2-loose.json <<'EOF'
{"name": "g2", "formats": ["write@1", "revert@1", "forget@1"], "floors": ["home 3", "alice <= 1000"],
 "methods": {"write@1": "kernel", "revert@1": "lemma", "forget@1": "kernel"}, "basis": ["kernel"]}
EOF
obend genealogy succeed g2-loose.json
```

```text
refused: g2 drops the floor `alice <= 100`, which g1 exports
```

A successor whose checker exports a floor and does not discharge it on some format, and one that
does not admit `revert`:

```sh refused
cat > g2-unchecked.json <<'EOF'
{"name": "g2", "formats": ["write@1", "revert@1", "forget@1"], "floors": ["home 3", "alice <= 100"],
 "methods": {"write@1 home 3": "kernel", "revert@1": "lemma", "forget@1": "kernel"}, "basis": ["kernel"]}
EOF
obend genealogy succeed g2-unchecked.json
```

```text
refused: g2's checker does not discharge `alice <= 100` on write@1
```

```sh refused
cat > g2-norevert.json <<'EOF'
{"name": "g2", "formats": ["write@1", "forget@1"], "floors": ["home 3", "alice <= 100"],
 "methods": {"write@1": "kernel", "forget@1": "kernel"}, "basis": ["kernel"]}
EOF
obend genealogy succeed g2-norevert.json
```

```text
refused: g2 does not admit revert@1, which every judge admits
```

## A stronger successor, and its Löb cost

`g2` decides the floors on writes by compiled code instead of the kernel's reduction: faster, and
resting on a principle `g1` does not hold (that a compiled run which says yes is right). `g1` cannot
certify that principle. Proposed without its label, the successor is refused.

```sh refused
cat > g2.json <<'EOF'
{"name": "g2", "formats": ["write@1", "revert@1", "forget@1"], "floors": ["home 3", "alice <= 100"],
 "methods": {"write@1": "compiled", "revert@1": "lemma", "forget@1": "kernel", "forget@1 alice <= 100": "lemma"},
 "basis": ["kernel", "compiled"]}
EOF
obend genealogy succeed g2.json
```

```text
refused: g2 rests on compiled, which g1 does not hold: a stronger successor, admitted only labelled with its Löb cost (--lob compiled)
```

A label the step does not need is refused too: the labels of a step are exactly what it adds
(`lob_labelled`).

```sh refused
obend genealogy succeed g1.json --lob compiled
```

```text
refused: the label compiled is not needed: g1 does not rest on it, or g1 already holds it
```

Labelled, it is admitted, and the chain carries the label as its Löb cost: every theorem about this
chain holds under the hypothesis that compiled runs are right (`LobCost`), and says so.

```sh
obend genealogy succeed g2.json --lob compiled
```

```text
admitted: g2 succeeds g1, labelled compiled
genesis g0 (basis kernel)
  floors: home 3, alice <= 100
  checker: write@1 by kernel; revert@1 by lemma
1. g1 succeeds g0 (basis kernel)
  floors: home 3, alice <= 100
  checker: write@1 by kernel; revert@1 by lemma; forget@1 by kernel on home 3, lemma on alice <= 100
2. g2 succeeds g1, labelled compiled (basis kernel, compiled)
  floors: home 3, alice <= 100
  checker: write@1 by compiled; revert@1 by lemma; forget@1 by kernel on home 3, lemma on alice <= 100
Löb cost: compiled
state: alice = 97 (3 judged states behind; home: alice = 50)
```

The new judge keeps the genesis floors, and the operator brings the system home through it.

```sh refused
obend genealogy act write alice 98
```

```text
refused by g2: write alice 98 would break `home 3`: the operator could no longer bring the system home within 3 reverts
```

```sh
obend genealogy act revert | tail -1
obend genealogy act revert | tail -1
obend genealogy act revert | tail -1
```

```text
state: alice = 90 (2 judged states behind; home: alice = 50)
state: alice = 80 (1 judged state behind; home: alice = 50)
state: alice = 50 (0 judged states behind; home: alice = 50)
```
