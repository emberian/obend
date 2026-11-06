# The swarm in its vault: a walkthrough

The swarm that builds obend keeps its day in an obend vault, `~/dev/obend-swarm`: one page per lane
(its branch, its agent's cv id, its brief, its worktree, its state, and once it reports, its commit,
the gate that passed and its doctrine counts), one page per box it builds on, the coordinator's seat,
`DEV.md` listing the lanes merged on dev, `QUESTS.md` pairing each brief with the lane that answers
it, the reasons the swarm keeps about itself, and the doctrine as a genealogy of judges. The pages
were written from the root's transcript and git, in the order things happened on 2026-11-05 and
2026-11-06 (`~/dev/obend-swarm/tools/`); `swarm/` beside this file is a copy of them, without the
vault's `.obend` world. This walkthrough opens that copy fresh and runs the swarm's verbs through it:
a lane forks, reports, comes back as a merge; boxes refuse jobs; the doctrine refuses a succession;
the end of the day's forget is refused while a lane is out. `~/dev/obend-swarm/FINDINGS.md` says what
each step exposed.

Every block below is run, in order, by `python3 tests/vault/walkthrough.py --doc tests/vault/SWARM.md`
(from `lean/`, after `lake build obend`), and what it prints is checked against the block after it.

## 1. The day, opened fresh

Thirty-nine lane pages, six boxes, the brief of every lane. Four lanes do not come in: their pages say
`merged`, and no gate passed for them (the root merged lane-lecscript, lane-fabric and lane-docs with no
gate whose success the transcript shows, and lane-fabric3 with its post-merge build red). A merged
lane must name its gate; the vault refuses each by name.

```sh
cp -R "$OBEND_ROOT/lean/tests/vault/swarm" swarm && cd swarm && obend open > ../open.txt
grep -c ': new page' ../open.txt; grep -v ': new page' ../open.txt
```

```text
87
lanes/lane-lecscript: not born: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-lecscript): `new.state in ["reported", "merged"] implies not (new.gate == "")` does not hold; a line `gate: …` with a value would pass (the page has no `gate:` line it reads)
rendered QUESTS.md
QUESTS: [[lanes/lane-lecscript]] (link) is missing: lanes/lane-lecscript has no version
```

DEV's laws read the lanes it lists: each is merged, names the dev commit it landed at, and that commit
is an ancestor of dev. What no law of the vault can read, git can: the merges on dev that DEV does
not hold.

```sh
cd swarm && obend status DEV | head -4 && python3 tools/check_dev.py . "$OBEND_ROOT" 0ae6ed8 9177beb
```

```text
DEV v1
  [[lanes/lane-hvm]] (link) ✓ current: lanes/lane-hvm exists
  [[lanes/lane-widths]] (link) ✓ current: lanes/lane-widths exists
  [[lanes/lane-eqy]] (link) ✓ current: lanes/lane-eqy exists
lane-fabric: merged on dev at b431f17, not on DEV (its page says state briefed)
lane-lecscript: merged on dev at b8a9446, not on DEV (its page says state merged)
lane-fabric3: merged on dev at 889a09d, not on DEV (its page says state briefed)
lane-docs: merged on dev at 158952e, not on DEV (its page says state briefed)
29 lanes on DEV, 33 merges on dev between 0ae6ed8 and 9177beb
```

## 2. A lane reports through its fork

Each lane's worktree is a declared fork of the vault. lane-cost (live today, agent aabeff96, in the
c2t7 worktree) fills its report in its fork. Without a gate line the report is refused, naming the law:

```sh
cd swarm && obend fork ../forks/lane-cost && obend fork ../forks/lane-holetyping && obend fork ../forks/lane-sdr
cd ../forks/lane-cost && sed -i.bak 's/^state: running$/state: reported\ncommit: "69e5983"/' lanes/lane-cost.md && rm lanes/lane-cost.md.bak
obend open | grep lane-cost
```

```text
forked lane-cost: a copy of this vault, declared here until it merges
forked lane-holetyping: a copy of this vault, declared here until it merges
forked lane-sdr: a copy of this vault, declared here until it merges
lanes/lane-cost: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-cost): `new.state in ["reported", "merged"] implies not (new.gate == "")` does not hold; a line `gate: …` with a value would pass (the page has no `gate:` line it reads)
```

A commit spelled without quotes and starting with a digit is not a label (`69e5983` is neither a
number nor a word); a law that requires it reads it as unset, and says so:

```sh
cd forks/lane-cost && sed -i.bak 's/^commit: "69e5983"$/commit: 69e5983\ngate: "tests\/vault\/walkthrough.py over every vault walkthrough against COST.baseline.tsv (its commit 69e5983 says so)"/' lanes/lane-cost.md && rm lanes/lane-cost.md.bak
obend open | grep lane-cost
```

```text
lanes/lane-cost: refused by lanes/_kind: commit (the kind of lanes/, an ancestor of lanes/lane-cost): `new.state in ["reported", "merged"] implies not (new.commit == "")` does not hold; a line `commit: …` with a value would pass (the page has no `commit:` line it reads)
```

Quoted, the report is born in the fork; it comes back to the vault as a merge, judged at the tip by
the same laws:

```sh
cd forks/lane-cost && sed -i.bak 's/^commit: 69e5983$/commit: "69e5983"/' lanes/lane-cost.md && rm lanes/lane-cost.md.bak
obend open | grep lane-cost
cd ../../swarm && obend merge ../forks/lane-cost | grep -v '^rendered' && grep -E '^(state|commit):' lanes/lane-cost.md
```

```text
lanes/lane-cost: v2 written
lanes/lane-cost: merged from lane-cost
QUESTS: [[lanes/lane-lecscript]] (link) is missing: lanes/lane-lecscript has no version
state: reported
commit: "69e5983"
```

A fork writes with the owner's authority: lane-holetyping's fork edits lane-cost's page, and the
merge imports the edit. Consent at the tip is the laws; no grant travels into a fork.

```sh
cd forks/lane-holetyping && printf 'Edited from lane-holetyping'"'"'s fork.\n' >> lanes/lane-cost.md && obend open | grep lane-cost
cd ../../swarm && obend merge ../forks/lane-holetyping | grep lane-cost && tail -1 lanes/lane-cost.md
```

```text
lanes/lane-cost: v2 written
lanes/lane-cost: merged from lane-holetyping
rendered lanes/lane-cost.md
Edited from lane-holetyping's fork.
```

A member's post cannot carry a report: the post opens a section over the changed frontmatter lines, the
settled text then has no `state:` line, and the lanes kind refuses the post.

```sh refused
cd swarm && obend member add lane-sdr --grant post:lanes/lane-sdr > /dev/null
sed 's/^state: running$/state: reported/' lanes/lane-sdr.md > ../sdr-report.md && obend post lanes/lane-sdr ../sdr-report.md --as lane-sdr
```

```text
refused: lanes/lane-sdr: refused by lanes/_kind: states (the kind of lanes/, an ancestor of lanes/lane-sdr): `new.state in ["briefed", "running", "reported", "merged"]` does not hold; the line `state: briefed` would pass (the page has `state: `)
```

A merge keeps a refused write. In the real day, lane-hvm2's fork was declared before lane-fabric3's
page was born; lane-fabric3's `merged` write was refused (no gate); when lane-hvm2's fork merged back,
the merge re-rendered lane-fabric3's page from the store, the refused text in its file was lost, and no
open said so again. The same order, replayed on the lanes alone: the file keeps the refused write after
the merge, and `obend status` still names the refusal.

```sh
mkdir replay && cp -R swarm/lanes swarm/machines swarm/briefs replay/ && cp replay/lanes/lane-fabric3.md fabric3.md && rm replay/lanes/lane-fabric3.md
cd replay && obend open > /dev/null && obend fork ../forks/lane-hvm2 && cp ../fabric3.md lanes/lane-fabric3.md && obend open | grep fabric3
sed -i.bak 's/^state: briefed$/state: merged\ncommit: "0380418"\ndev: "889a09d"/' lanes/lane-fabric3.md && rm lanes/lane-fabric3.md.bak && obend open | grep fabric3 | cut -c1-120
obend merge ../forks/lane-hvm2 | grep -c fabric3; grep '^state' lanes/lane-fabric3.md; obend status lanes/lane-fabric3 | head -1 | cut -c1-120
```

```text
forked lane-hvm2: a copy of this vault, declared here until it merges
lanes/lane-fabric3: new page (v1)
lanes/lane-fabric3: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-fabric3): `new.state in 
0
state: merged
lanes/lane-fabric3 v1; its last write was refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-fa
```

## 3. Boxes

A lane may not build on a box that does not answer (persvati, unreachable from the Mac and from hbox
at 2026-11-06T17:49Z) or on one that carries no builds (forge):

```sh
cd swarm && cp lanes/lane-sdr.md ../sdr.md
sed -i.bak 's/^Brief: \(.*\)\.$/Brief: \1, [[machines\/persvati]]./' lanes/lane-sdr.md && rm lanes/lane-sdr.md.bak && obend open | grep lane-sdr
sed -i.bak 's/machines\/persvati/machines\/forge/' lanes/lane-sdr.md && rm lanes/lane-sdr.md.bak && obend open | grep lane-sdr
cp ../sdr.md lanes/lane-sdr.md && obend open | grep -c lane-sdr || true
```

```text
lanes/lane-sdr: refused by lanes/_kind: reachable (the kind of lanes/, an ancestor of lanes/lane-sdr) over its links, at machines/persvati: `linked.unreachable == 0` does not hold there; the line `unreachable: 0` would pass (the page has `unreachable: 1`)
lanes/lane-sdr: refused by lanes/_kind: buildbox (the kind of lanes/, an ancestor of lanes/lane-sdr) over its links, at machines/forge: `linked.nobuild == 0` does not hold there; the line `nobuild: 0` would pass (the page has `nobuild: 1`)
0
```

forge's own law judges the jobs it lists; a detached job marked running must name its PID file:

```sh
cd swarm && cp machines/forge.md ../forge.md && printf '\nJobs: [[lanes/lane-sdr]].\n' >> machines/forge.md
obend open | grep forge; cp ../forge.md machines/forge.md && obend open > /dev/null
sed -i.bak 's/^state: running$/state: running\njob: running/' lanes/lane-sdr.md && rm lanes/lane-sdr.md.bak && obend open | grep lane-sdr
cp ../sdr.md lanes/lane-sdr.md && obend open > /dev/null
```

```text
machines/forge: refused by its law nobuild over its links, at lanes/lane-sdr: `linked.builds == 0` does not hold there; the line `builds: 0` would pass (the page has `builds: 1`)
lanes/lane-sdr: refused by lanes/_kind: pidfile (the kind of lanes/, an ancestor of lanes/lane-sdr): `new.job == "running" implies not (new.pidfile == "")` does not hold; a line `pidfile: …` with a value would pass (the page has no `pidfile:` line it reads)
```

A law refuses the record of a fact. If hbox drops off the network (as on 2026-10-31), the page that
says so is refused, because lanes build there:

```sh
cd swarm && cp machines/hbox.md ../hbox.md && sed -i.bak 's/^memcap: 48$/memcap: 48\nunreachable: true/' machines/hbox.md && rm machines/hbox.md.bak
obend open | grep 'machines/hbox' | cut -c1-200; cp ../hbox.md machines/hbox.md && obend open > /dev/null
```

```text
machines/hbox: refused by lanes/_kind: reachable (a law over lanes/lane-certcheap's links, of which machines/hbox is one): `linked.unreachable == 0` does not hold; the line `unreachable: 0` would pass
```

Two pages that link each other under laws over links cannot be born together. At 18:39Z bb2 held a
live job of lane-holetyping and two of lane-cost, each with its PID file (`observations/bb2-jobs.txt`);
in the vault each lane page says `job: running` and builds on `[[machines/bb2]]`, and bb2 lists both
lanes under its `pidfile` law. In the vault that was built in order, each page was born before the
other linked it. Written at once, as a fresh copy of that vault is, the lanes kind's laws over links
need bb2's version and bb2's law needs the lanes': none is born, and the refusal does not name its law.

```sh
cp -R "$OBEND_ROOT/lean/tests/vault/swarm" jobs && cd jobs && cp lanes/lane-cost.md ../cost.md && cp lanes/lane-holetyping.md ../holetyping.md
sed 's/^state: running$/state: running\njob: running\npidfile: "bb2:\/home\/build\/obend\/logs\/large1.pid"/; s/^\(Brief: .*\)\.$/\1, [[machines\/bb2]]./' ../cost.md > lanes/lane-cost.md
sed 's/^state: running$/state: running\njob: running\npidfile: "bb2:\/home\/build\/obend\/logs\/holetyping-t2.pid"/; s/^\(Brief: .*\)\.$/\1, [[machines\/bb2]]./' ../holetyping.md > lanes/lane-holetyping.md
printf -- '- [[lanes/lane-holetyping]]\n- [[lanes/lane-cost]]\n' >> machines/bb2.md
obend open | grep -e bb2 -e 'not born' | cut -c1-150
```

```text
lanes/lane-cost: not born: refused by  over its links, at machines/bb2: the linked page machines/bb2 has no version to judge
lanes/lane-holetyping: not born: refused by  over its links, at machines/bb2: the linked page machines/bb2 has no version to judge
lanes/lane-lecscript: not born: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-lecscript): `new.state in ["reported", "me
machines/bb2: not born: refused by  over its links, at lanes/lane-holetyping: the linked page lanes/lane-holetyping has no version to judge
```

## 4. Reasons

Is persvati down, or is the hop to it broken? Two explanations, each defeating the other, until the
second box answers.

```sh
cd swarm
obend reasons observe remote-timeout --line observations/probe.txt:4 | head -1
obend reasons observe lan-timeout --line observations/probe.txt:5 | head -1
obend reasons observe via-workhorse --line observations/MACHINES.md:39 | head -1
obend reasons explain P1 hop-broken --if remote-timeout --if via-workhorse --unless persvati-down | head -1
obend reasons explain P2 persvati-down --if remote-timeout --if lan-timeout --unless hop-broken | tail -3
obend reasons observe no-route-from-hbox --line observations/probe.txt:10 | head -1
obend reasons explain P3 persvati-down --if no-route-from-hbox | tail -3
obend reasons why persvati-down
```

```text
observed remote-timeout: persvati-remote: Connection to UNKNOWN port 65535 timed out
observed lan-timeout: persvati-lan: ssh: connect to host 192.168.50.120 port 22: Operation timed out
observed via-workhorse:   the first READY from the box. From the Mac it answers only as `persvati-remote` (via the workhorse, a slow hop);
explained P1: hop-broken ⇐ remote-timeout, via-workhorse unless persvati-down
  hop-broken: undefined (was supported)
  persvati-down: undefined (was unsupported)
  judged anew: 5 of 5 atoms
observed no-route-from-hbox: persvati: ssh: connect to host 192.168.50.120 port 22: No route to host
  hop-broken: unsupported (was undefined)
  persvati-down: supported (was undefined)
  judged anew: 6 of 6 atoms
persvati-down: supported by P2
```

## 5. The doctrine as a genealogy

The rules of 2026-11-05 as floors over the day's tallies (whole-tree builds on the Mac, stashes, `git
add -A`, kills by pattern, detached jobs without a PID file), at the start of the day. The coordinator's
six `git add -A` are refused when they are written as the day's tally; a doctrine edit that drops the
never-stash rule, or allows five whole-tree builds on the Mac, is refused; today's rule (no whole-tree
build on hbox) is admitted.

```sh
cd swarm/doctrine && obend genealogy genesis g0.json --store machv=0 --store stash=0 --store addall=0 --store killpat=0 --store nopid=0 --store hboxwhole=0 | head -2
```

```text
genesis rules-2026-11-05 (basis kernel)
  floors: home 3, machv <= 0, stash <= 0, addall <= 0, killpat <= 0, nopid <= 0
```

```sh refused
cd swarm/doctrine && obend genealogy act write addall 6 --as root --says "checkpoint commits"
```

```text
refused by rules-2026-11-05: write addall 6 would break `addall <= 0`
```

```sh refused
cd swarm/doctrine && obend genealogy succeed g1-drop-stash.json
```

```text
refused: rules-no-stash-rule drops the floor `stash <= 0`, which rules-2026-11-05 exports
```

```sh refused
cd swarm/doctrine && obend genealogy succeed g1-loosen-mac.json
```

```text
refused: rules-some-mac-builds drops the floor `machv <= 0`, which rules-2026-11-05 exports
```

```sh
cd swarm/doctrine && obend genealogy succeed g1-bb2.json | head -1
```

```text
admitted: rules-2026-11-06 succeeds rules-2026-11-05
```

## 6. The end of the day

A forget under a retention contract is refused while a lane's fork is out; lane-sdr has not reported.

```sh refused
cd swarm && obend forget eod
```

```text
refused: the branch lane-sdr forked from the prefix and has not merged; merge it or abandon it (--abandon lane-sdr)
```

```sh
cd swarm && obend forget eod --abandon lane-sdr && obend log | head -1 | cut -c1-120
```

```text
forgot 33 records (1055165 bytes) under the retention contract eod, abandoning lane-sdr: the log is one checkpoint record of 417360 bytes
log: 1 records, 417360 bytes, each following the one before it from the genesis sentinel through a checkpoint record: 33
```
