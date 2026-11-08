# The swarm in its vault: a walkthrough

The swarm that builds obend keeps its day in an obend vault, `~/dev/obend-swarm`: one page per lane
(its branch, its agent's cv id, its brief, its worktree, its state, and once it reports, its commit,
the gate that passed and its doctrine counts), one page per box it builds on, the coordinator's seat,
`DEV.md` listing the lanes merged on dev, `QUESTS.md` pairing each brief with the lane that answers
it, the reasons the swarm keeps about itself, and the doctrine as a genealogy of judges. The pages
were written from the root's transcript and git, in the order things happened on 2026-11-05 and
2026-11-06 (`~/dev/obend-swarm/tools/`); `swarm/` beside this file is a copy of them, without the
vault's `.obend` world. This walkthrough opens that copy fresh and runs the swarm's verbs through it:
a brief is a form and a lane's report its fill, judged by the lane page's laws; DEV reads the lanes
that link to it; four merges are gated after the fact, as the merge they were; boxes refuse jobs;
pages that need each other are written together; the doctrine refuses a succession; the end of the
day's forget is refused while a lane is out. A command whose write is refused exits 1 and says the
refusal on stderr, so a step that shows one is marked `refused`. `~/dev/obend-swarm/FINDINGS.md` says what
each step exposed.

Every block below is run, in order, by `python3 tests/vault/walkthrough.py --doc tests/vault/SWARM.md`
(from `lean/`, after `lake build obend`), and what it prints is checked against the block after it.

## 1. The day, opened fresh

Thirty-nine lane pages, six boxes, the brief of every lane. lane-lecscript does not come in: its
page says `merged`, and no gate stood before that merge (the vault keeps lane-fabric, lane-fabric3 and
lane-docs `briefed` for the same reason; section 4 gates them after the fact). A merged lane must name
its gate; the vault refuses it by name, on stderr, and the open exits 1.

```sh refused
cp -R "$OBEND_ROOT/lean/tests/vault/swarm" swarm && cd swarm && obend open > ../open.txt
e=$?; grep -c ': new page' ../open.txt; grep -v ': new page' ../open.txt; exit $e
```

```text
87
rendered QUESTS.md
QUESTS: [[lanes/lane-lecscript]] (link) is missing: lanes/lane-lecscript has no version
lanes/lane-lecscript: not born: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-lecscript): `new.state in ["reported", "merged"] implies not (new.gate == "")` does not hold; a line `gate: …` with a value would pass (the page has no `gate:` line it reads)
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
29 lanes on DEV (0 landed after 9177beb), 33 merges on dev between 0ae6ed8 and 9177beb
```

## 2. A brief is a form; the report is its fill

The root's brief to a lane is a form captured on the lane's page (`obend brief`): the report the lane
owes is one set of its page, its `state` set to `reported`, and holes for what only the lane can say:
its commit (a label), the gate that passed and what it left out (text). lane-cost (agent aabeff96,
live today, merged on dev at 6d100d1) is briefed; the form goes to it as a file.

```sh
cd swarm && obend brief lanes/lane-cost report-cost --for lane-cost --grant lanes/lane-cost --set state=reported --hole commit:label --hole gate:text --hole leftout:text
obend form report-cost --out ../cost.form > /dev/null
```

```text
briefed report-cost on lanes/lane-cost for lane-cost: 1 page(s) shown, 2 not shown to lane-cost
report-cost: a form for lane-cost (read, write on lanes/lane-cost)
  lanes/lane-cost: shown
  hole commit: a label
  hole gate: a text
  hole leftout: a text
  lanes/lane-cost.state := "reported"
  lanes/lane-cost.commit := commit
  lanes/lane-cost.gate := gate
  lanes/lane-cost.leftout := leftout
```

The lane fills the form where it works. A commit is one word; a fill that is not is refused before
anything is sent:

```sh refused
mkdir lane-cost && cd lane-cost && obend fill ../cost.form 'commit=8d65f93 and more' gate=x leftout=y --out ../bad.json
```

```text
refused: the hole commit is a label (one word); 8d65f93 and more is not
```

A report without a gate line is a fill the membrane admits (the lane may write its page) and the
lane page's laws refuse, by name, where the vault judges it:

```sh refused
cd lane-cost && obend fill ../cost.form commit=8d65f93 gate= 'leftout=nothing' --out ../nogate.json > /dev/null
cd ../swarm && obend judge ../nogate.json
```

```text
work: performed 0, retained 0 of 0
report-cost: at lanes/lane-cost: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-cost): `new.state in ["reported", "merged"] implies not (new.gate == "")` does not hold; a line `gate: …` with a value would pass (the page has no `gate:` line it reads)
```

The report lane-cost gave (root msg 1763), as its fill: judged by the lanes kind's laws, landed as one
turn on lane-cost's page.

```sh
cd lane-cost && obend fill ../cost.form commit=8d65f93 'gate=walkthrough.py on its final binary: vault, forms, crash, transport, retain, ledger, reasons and decisions pass; decisions/LEDGER step 3 fails, on dev as well' 'leftout=the 10,000-record run on bb2, still going at its report' --out ../report.json > /dev/null
cd ../swarm && obend judge ../report.json && grep -E '^(state|commit|gate|leftout):' lanes/lane-cost.md
```

```text
report-cost: landed as one turn over 1 pages by lane-cost, receipt e301776eb00833ab (1 in the chain)
rendered lanes/lane-cost.md
QUESTS: [[lanes/lane-lecscript]] (link) is missing: lanes/lane-lecscript has no version
work: performed 1, retained 0 of 0
state: "reported"
commit: "8d65f93"
gate: "walkthrough.py on its final binary: vault, forms, crash, transport, retain, ledger, reasons and decisions pass; decisions/LEDGER step 3 fails, on dev as well"
leftout: "the 10,000-record run on bb2, still going at its report"
```

Each lane's worktree is also a declared fork of the vault.

```sh
cd swarm && obend fork ../forks/lane-holetyping && obend fork ../forks/lane-sdr
```

```text
forked lane-holetyping: a copy of this vault, declared here until it merges
forked lane-sdr: a copy of this vault, declared here until it merges
```

A fork writes with the owner's authority: lane-holetyping's fork edits lane-cost's page, and the
merge imports the edit. Consent at the tip is the laws; no grant travels into a fork.

```sh
cd forks/lane-holetyping && printf 'Edited from lane-holetyping'"'"'s fork.\n' >> lanes/lane-cost.md && obend open | grep lane-cost
cd ../../swarm && obend merge ../forks/lane-holetyping | grep lane-cost && tail -1 lanes/lane-cost.md
```

```text
lanes/lane-cost: v3 written
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
0
lanes/lane-fabric3: no such page
lanes/lane-lecscript: not born: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-lecscript): `new.state in ["reported", "merged"] implies not (new.gate == "")` does not hold; a line `gate: …` with a value would pass (the page has no `gate:` line it reads)
sed: lanes/lane-fabric3.md: No such file or directory
grep: lanes/lane-fabric3.md: No such file or directory
```

## 3. DEV reads the lanes that link to it

DEV's laws over its links say that every lane it lists is merged, at a dev commit that is an ancestor
of dev. The converse, that every lane marked merged is listed on DEV, is a law over DEV's BACKLINKS:
`linked_by.F` reads a page that links to DEV, and `linked_by.listed` says whether DEV links back. Every
lane page now says where it lands; DEV gains the law. (lane-lecscript stays out: its own law still
refuses it, below.)

```sh
cd swarm && python3 - <<'PY'
import glob
p = 'DEV.md'; s = open(p).read()
open(p, 'w').write(s.replace('law ancestor: linked.ancestor == 1\n', 'law ancestor: linked.ancestor == 1\nlaw listed: linked_by.state == "merged" implies linked_by.listed == 1\n', 1))
for f in glob.glob('lanes/lane-*.md'):
    open(f, 'a').write('\nLands on [[DEV]].\n')
PY
obend open > ../links.txt; echo "exit $?"; grep -c ' written' ../links.txt
```

```text
exit 1
38
lanes/lane-lecscript: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-lecscript): `new.state in ["reported", "merged"] implies not (new.gate == "")` does not hold; a line `gate: …` with a value would pass (the page has no `gate:` line it reads)
```

A lane marked merged that DEV does not list is refused by DEV's law, at the lane:

```sh refused
cd swarm && python3 tools/setfields.py lanes/lane-cost.md state=merged dev=6d100d1 ancestor=true && obend open
```

```text
lanes/lane-lecscript: still not born: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-lecscript): `new.state in ["reported", "merged"] implies not (new.gate == "")` does not hold; a line `gate: …` with a value would pass (the page has no `gate:` line it reads)
QUESTS: [[lanes/lane-lecscript]] (link) is missing: lanes/lane-lecscript has no version
lanes/lane-cost: refused by DEV: listed over DEV's backlinks, at lanes/lane-cost (which links to DEV): `linked_by.state == "merged" implies linked_by.listed == 1` does not hold there; another `state:` value would pass (the page has `state: merged`)
```

DEV lists it: the lane's write and DEV's, each refused alone, are judged together as one turn on the
tip of both, and land at once.

```sh
cd swarm && printf -- '- [[lanes/lane-cost]] at 6d100d1\n' >> DEV.md && obend open
```

```text
DEV: v3 written
lanes/lane-cost: v5 written
lanes/lane-lecscript: still not born: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-lecscript): `new.state in ["reported", "merged"] implies not (new.gate == "")` does not hold; a line `gate: …` with a value would pass (the page has no `gate:` line it reads)
QUESTS: [[lanes/lane-lecscript]] (link) is missing: lanes/lane-lecscript has no version
```

DEV may not drop a lane that is merged:

```sh refused
cd swarm && cp DEV.md ../dev.md && sed -i.bak '/lanes\/lane-hvm]] at/d' DEV.md && rm DEV.md.bak && obend open; e=$?
cp ../dev.md DEV.md && obend open > /dev/null; exit $e
```

```text
lanes/lane-lecscript: still not born: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-lecscript): `new.state in ["reported", "merged"] implies not (new.gate == "")` does not hold; a line `gate: …` with a value would pass (the page has no `gate:` line it reads)
QUESTS: [[lanes/lane-lecscript]] (link) is missing: lanes/lane-lecscript has no version
DEV: refused by its law listed over its backlinks, at lanes/lane-hvm (which links to DEV): `linked_by.state == "merged" implies linked_by.listed == 1` does not hold there; another `state:` value would pass (the page has `state: merged`)
```

## 4. Gated after the fact

Four merges of 2026-11-05 showed no gate before they landed. Each gate was run green afterwards: the
root ran `verify_sim.sh` on dev at b8a9446 just after merging lane-lecscript (msg 807, read at 849),
`verify_fabric.sh` at 6183619 after lane-fabric (msg 900, read at 928) and at 889a09d after
lane-fabric3 (msg 972, read at 984, with the fabric modules built); lane-docs' gate, the docs census,
ran green in tier 2 on bb2 at 021a0b0 (lane-swarmvault's run, `~/obend/logs/swarmvault-t2.log`; the
root's transcript shows no census run of its own). Each is recorded as the merge it was: `merged`,
with its lane commit, the dev commit it landed at, the gate that passed, the dev commit the gate passed
on (`gate_dev:`) and `gated: after`; DEV lists it. Written in a fork, the five writes land in the
fork's open as one turn (each needs the others: DEV's row reads the lane merged, the lane's merge
reads DEV listing it), but the merge replays a fork's writes one page at a time, each against what it
read there, and refuses every one of them, each waiting on another:

```sh refused
cd swarm && obend fork ../forks/gates > /dev/null && cd ../forks/gates && sh "$OBEND_ROOT/lean/tests/vault/swarm/tools/gates.sh" && obend open | grep -c ' written\| new page'
cd ../../swarm && obend merge ../forks/gates > /dev/null 2> ../gates.err; e=$?; cut -c1-110 ../gates.err >&2; exit $e
```

```text
5
DEV: not merged: its write at gates read lanes/lane-fabric as it was there (ancestor 1 → none, bytes 648 → 462
lanes/lane-docs: not merged: its write at gates read DEV as it was there (bytes 1657 → 1515, lines 38 → 34, li
lanes/lane-fabric: not merged: its write at gates read DEV as it was there (bytes 1657 → 1515, lines 38 → 34, 
lanes/lane-fabric3: not merged: its write at gates read DEV as it was there (bytes 1657 → 1515, lines 38 → 34,
lanes/lane-lecscript: not merged: its write at gates read DEV as it was there (bytes 1657 → 1515, lines 38 → 3
```

Written in the vault itself, the same five writes are judged together and land at once; DEV holds every
merge on dev, and git agrees:

```sh
cd swarm && sh tools/gates.sh && obend open | grep -c ' written\| new page'
grep -E '^(state|gate_dev|gated):' lanes/lane-docs.md; python3 tools/check_dev.py . "$OBEND_ROOT" 0ae6ed8 9177beb
```

```text
5
state: "merged"
gate_dev: "021a0b0"
gated: "after"
34 lanes on DEV (1 landed after 9177beb), 33 merges on dev between 0ae6ed8 and 9177beb
```

## 5. Boxes

A lane may not build on a box that does not answer (persvati, unreachable from the Mac and from hbox
at 2026-11-06T17:49Z) or on one that carries no builds (forge):

```sh
cd swarm && cp lanes/lane-sdr.md ../sdr.md
sed -i.bak 's/^Brief: \(.*\)\.$/Brief: \1, [[machines\/persvati]]./' lanes/lane-sdr.md && rm lanes/lane-sdr.md.bak && obend open | grep lane-sdr
sed -i.bak 's/machines\/persvati/machines\/forge/' lanes/lane-sdr.md && rm lanes/lane-sdr.md.bak && obend open | grep lane-sdr
cp ../sdr.md lanes/lane-sdr.md && obend open | grep -c lane-sdr || true
```

```text
0
lanes/lane-sdr: refused by lanes/_kind: reachable (the kind of lanes/, an ancestor of lanes/lane-sdr) over its links, at machines/persvati: `linked.unreachable == 0` does not hold there; the line `unreachable: 0` would pass (the page has `unreachable: 1`)
lanes/lane-sdr: refused by lanes/_kind: buildbox (the kind of lanes/, an ancestor of lanes/lane-sdr) over its links, at machines/forge: `linked.nobuild == 0` does not hold there; the line `nobuild: 0` would pass (the page has `nobuild: 1`)
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
machines/hbox: refused by lanes/_kind: reachable (a law over lanes/lane-certcheap's links, of which machines/hbox is one): `linked.unreachable == 0` does not hold; the line `unreachable: 0` would pass (the page has `unreachable: 1`)
```

Pages that link each other under laws over links are born together. At 18:39Z bb2 held a live job of
lane-holetyping and two of lane-cost, each with its PID file (`observations/bb2-jobs.txt`); in the
vault each lane page says `job: running` and builds on `[[machines/bb2]]`, and bb2 lists both lanes
under its `pidfile` law. Written at once, as a fresh copy of that vault is, the lanes kind's laws over
links need bb2's version and bb2's law needs the lanes'. Each birth alone is refused; the births an
open refused are judged again as one turn, each by its laws on the tip of all of them, and land at
once. (Until 2026-11-06 none was born, and the refusal named no law.)

```sh
cp -R "$OBEND_ROOT/lean/tests/vault/swarm" jobs && cd jobs && cp lanes/lane-cost.md ../cost.md && cp lanes/lane-holetyping.md ../holetyping.md
sed 's/^state: running$/state: running\njob: running\npidfile: "bb2:\/home\/build\/obend\/logs\/large1.pid"/; s/^\(Brief: .*\)\.$/\1, [[machines\/bb2]]./' ../cost.md > lanes/lane-cost.md
sed 's/^state: running$/state: running\njob: running\npidfile: "bb2:\/home\/build\/obend\/logs\/holetyping-t2.pid"/; s/^\(Brief: .*\)\.$/\1, [[machines\/bb2]]./' ../holetyping.md > lanes/lane-holetyping.md
printf -- '- [[lanes/lane-holetyping]]\n- [[lanes/lane-cost]]\n' >> machines/bb2.md
obend open > ../jobs.txt 2>&1; echo "exit $?"; grep -e bb2 -e 'lane-cost' -e 'lane-holetyping' -e 'not born' ../jobs.txt | cut -c1-150
```

```text
exit 1
lanes/lane-lecscript: not born: refused by lanes/_kind: gate (the kind of lanes/, an ancestor of lanes/lane-lecscript): `new.state in ["reported", "me
briefs/lane-cost: new page (v1)
briefs/lane-holetyping: new page (v1)
lanes/lane-cost: new page (v1)
lanes/lane-holetyping: new page (v1)
machines/bb2: new page (v1)
```

## 6. Reasons

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

## 7. The doctrine as a genealogy

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

## 8. The end of the day

A forget under a retention contract is refused while anything resting on the prefix it drops stands:
lane-cost's brief, a form issued before it, and lane-sdr's fork, which has not reported.

```sh refused
cd swarm && obend forget eod
```

```text
refused: the form report-cost was issued against the prefix and stands; retire it (--retire report-cost) or keep the prefix
```

lane-cost's report has landed, so its brief is retired with the forget; lane-sdr's fork is abandoned:

```sh
cd swarm && obend forget eod --abandon lane-sdr --retire report-cost && obend log | head -1 | cut -c1-120
```

```text
forgot 45 records (1079900 bytes) under the retention contract eod, retiring report-cost, abandoning lane-sdr: the log is one checkpoint record of 440776 bytes
log: 1 records, 440776 bytes, each following the one before it from the genesis sentinel through a checkpoint record: 45
```
