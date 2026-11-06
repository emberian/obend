# A workshop inhabited by agents: a walkthrough

On 2026-11-06 two residents, rowan and sable (headless Opus sessions), maintained a real package,
`~/swarm/research.py`, in a workshop that is an obend vault (`~/dev/obend-workshop`; its REPORT.md and
FINDINGS.md say what happened and what it cost). Jobs were offered as forms a resident takes by filling
(the run budget it needs, moved from its share to the job); every test run spent one unit of its job's
budget; every run's result is an evidence page bound to the exact artifact it ran on; each resident
worked in its own fork of the vault and its own worktree of `~/swarm`; the reviewer landed what passed.
`workshop/` beside this file holds the pages: `tip/` as the workshop opened, `sable/` and `rowan/` the
pages each resident's fork held when it came back, `rowan2/` rowan's after its repair, `reviewer/` the
reviewer's evidence at the tip. This walkthrough replays the day on a fresh copy, with the residents'
own pages and evidence: the decisive passage (a resident works disconnected; the interface it builds on
and its job's acceptance law change; it returns, and the workshop says what is reusable, what evidence
expired, which effects already happened, what must be redone, and refuses or lands the result by name),
and the defects of the vault the day exposed, fixed.

Every block below is run, in order, by `python3 tests/vault/walkthrough.py --doc tests/vault/WORKSHOP.md`
(from `lean/`, after `lake build obend`), and what it prints is checked against the block after it.

## 1. The workshop opens; jobs are offered as forms

```sh
cp -R "$OBEND_ROOT/lean/tests/vault/workshop" fx && cp -R fx/tip ws && cd ws && obend open | tail -3
obend capture jobs/relay accept-relay --for rowan --grant resources/rowan --grant jobs/relay --move resources/rowan jobs/relay 4 --field runs | head -1
obend abstract accept-relay 4 runs > /dev/null && obend offer accept-relay runs 1..6 --promise 1..4
obend capture jobs/relay land-relay --for rowan --grant jobs/relay --grant landed/relay --move jobs/relay landed/relay 1 --field open | head -1
obend capture jobs/harness accept-harness --for sable --grant resources/sable --grant jobs/harness --move resources/sable jobs/harness 4 --field runs > /dev/null
obend abstract accept-harness 4 runs > /dev/null && obend offer accept-harness runs 1..6 --promise 1..4 > /dev/null
obend capture jobs/harness land-harness --for sable --grant jobs/harness --grant landed/harness --move jobs/harness landed/harness 1 --field open > /dev/null
for f in accept-relay land-relay accept-harness land-harness; do obend form $f --out ../$f.form > /dev/null; done
```

```text
tests/_kind: new page (v1)
tests/harness/unit: new page (v1)
tests/relay/sandbox: new page (v1)
captured accept-relay from jobs/relay for rowan: 2 page(s) shown, 2 not shown to rowan
accept-relay: offers runs = 1..6, promises 1..4 (each value judged by the laws as they stand: 6 admitted)
captured land-relay from jobs/relay for rowan: 2 page(s) shown, 2 not shown to rowan
```

The laws a form's pages are judged by are checked once at capture over the holed state, each named by
the page or kind that wrote it (a kind's law used to be cut by the page's length:
`tests/relay/sandbox:  at tests/relay/sandbox`), and a form with no natural hole says so:

```sh
cd ws && obend checked accept-relay | head -4 && obend checked land-relay | head -2
```

```text
accept-relay: 11 law(s) over its holed states, checked once with runs open:
  resources/_kind: kagi at resources/rowan (debited)
  resources/_kind: kagimono at resources/rowan (debited)
  jobs/_kind: states at jobs/relay (credited)
land-relay: 9 law(s) over its holed states, checked once (no natural hole open):
  jobs/_kind: states at jobs/relay (debited)
```

## 2. The residents take their jobs

Each fills its job's form in its own store; the reviewer judges at the tip, and the tip is forked for
the taker: its membrane, where it works from then on.

```sh
mkdir sable.store && cd sable.store && obend fill ../accept-harness.form runs=3 --out ../sable-accept.json | tail -1
mkdir ../rowan.store && cd ../rowan.store && obend fill ../accept-relay.form runs=5 --out ../rowan-accept.json | tail -1
cd ../ws && obend judge ../sable-accept.json --receipt ../sable-accept.receipt | head -3 && obend judge ../rowan-accept.json --receipt ../rowan-accept.receipt | head -3
obend fork ../sable && obend fork ../rowan
cd ../sable.store && obend confirm ../sable-accept.receipt && cd ../rowan.store && obend confirm ../rowan-accept.receipt
```

```text
wrote ../sable-accept.json (intent ac04df43a065099d)
wrote ../rowan-accept.json (intent 0029c24ddbc9e21e)
accept-harness: landed as one turn over 2 pages by sable, receipt d5ca3094f23d608d (1 in the chain)
  resources/sable: runs 8 → 5
  jobs/harness: runs 0 → 3
accept-relay: landed as one turn over 2 pages by rowan, receipt dd603fbba339fe78 (2 in the chain)
  resources/rowan: runs 8 → 3
  jobs/relay: runs 0 → 5
forked sable: a copy of this vault, declared here until it merges
forked rowan: a copy of this vault, declared here until it merges
confirmed intent ac04df43a065099d: its receipt names the proposal sent from here; nothing outstanding
confirmed intent 0029c24ddbc9e21e: its receipt names the proposal sent from here; nothing outstanding
```

## 3. Disconnected work: spends, evidence, an overdraft refused by name

What the residents' forks held when they came back, copied in: sable's harness proposed on 751b497;
rowan's relay proposed on 007f0e5, over the base the job was offered on, ed1d477, with two runs spent
(one of them a live Kagi search, paid from its share). Each run's evidence page is written once.

```sh
cp -R fx/sable/. sable/ && cd sable && obend open && obend fill ../land-harness.form --because harness-proven --out ../sable-land.json | tail -1
cd ../rowan && cp -R ../fx/rowan/. . && obend open && obend fill ../land-relay.form --because relay-proven --out ../rowan-land.json | tail -1
obend reasons observe relay-sandbox-pass-007f0e540122 --line evidence/relay/rowan-1.md:5 | head -1
grep -E '^(state|on|base|runs|spent):' jobs/relay.md
```

```text
jobs/harness: v3 written
residents/sable: v2 written
evidence/harness/sable-1: new page (v1)
wrote ../sable-land.json (intent d4700896df94b74b)
jobs/relay: v3 written
residents/rowan: v2 written
resources/rowan: v3 written
evidence/relay/rowan-1: new page (v1)
evidence/relay/rowan-2: new page (v1)
wrote ../rowan-land.json (intent 1fcef1ca77bea7b0)
observed relay-sandbox-pass-007f0e540122: result: "pass"
state: proposed
on: "ed1d477"
runs: 5
spent: 2
base: "ed1d477"
```

A seventh run of a job that holds five is refused before anything runs, and evidence cannot be
rewritten:

```sh
cd rowan && sed -i.bak 's/^spent: 2$/spent: 6/' jobs/relay.md && rm jobs/relay.md.bak && obend open
sed -i.bak 's/^spent: 6$/spent: 2/' jobs/relay.md && rm jobs/relay.md.bak && obend open
sed -i.bak 's/^result: "pass"$/result: "fail"/' evidence/relay/rowan-1.md && rm evidence/relay/rowan-1.md.bak && obend open
sed -i.bak 's/^result: "fail"$/result: "pass"/' evidence/relay/rowan-1.md && rm evidence/relay/rowan-1.md.bak && obend open
```

```text
nothing changed
nothing changed
jobs/relay: refused by jobs/_kind: budget (the kind of jobs/, an ancestor of jobs/relay): `new.spent <= new.runs` does not hold; the line `spent: 5` would pass (the page has `spent: 6`)
evidence/relay/rowan-1: refused by evidence/_kind: fixed (the kind of evidence/, an ancestor of evidence/relay/rowan-1): `writeOnce(result) and writeOnce(artifact) and writeOnce(test) and writeOnce(run)` does not hold; the line `result: pass` would pass (the page has `result: fail`)
```

## 4. Meanwhile at the tip: the harness lands, and the shared interface and the relay's acceptance law move

The reviewer merges sable's fork, runs the acceptance on sable's exact commit at the tip (its evidence
page), explains why the job is proven, and the landing is judged by the job's laws:

```sh
cd ws && obend merge ../sable | grep -v '^rendered'
cp -R ../fx/reviewer/evidence/harness/. evidence/harness/ && obend open
sed -i.bak 's/^spent: 1$/spent: 2/' jobs/harness.md && rm jobs/harness.md.bak && obend open
obend reasons observe harness-unit-pass-751b497f3fab --line evidence/harness/reviewer-1.md:5 | head -1
obend reasons explain R-harness-751b497 harness-proven --if harness-unit-pass-751b497f3fab --unless harness-base-moved | head -1
obend judge ../sable-land.json | head -3
```

```text
jobs/harness: merged from sable
residents/sable: merged from sable
evidence/harness/sable-1: imported from sable
evidence/harness/reviewer-1: new page (v1)
jobs/harness: v4 written
observed harness-unit-pass-751b497f3fab: result: "pass"
explained R-harness-751b497: harness-proven ⇐ harness-unit-pass-751b497f3fab unless harness-base-moved
land-harness: landed as one turn over 2 pages by sable, receipt d3f234dc3750e0ca (3 in the chain)
  jobs/harness: open 1 → 0
  landed/harness: open 0 → 1
```

751b497 is now `workshop`'s head: `_post` is looked up per call and the endpoints are `kagi_url()` and
`scry_url()`. The reviewer moves jobs/relay onto it and gives it a law: a proposal must name a passing
run of the offline suite through those seams.

```sh
cd ws && cp -R ../fx/reviewer/tests/. tests/ && mkdir -p data && cp ../fx/reviewer/data/landings.txt data/
python3 -c "
p='jobs/relay.md'; s=open(p).read()
s=s.replace('base: \"ed1d477\"\n','base: \"751b497\"\nlaw suite: new.state in [\"proposed\", \"landed\"] implies not (new.suite == \"\")\n',1)
open(p,'w').write(s)"
obend open && obend reasons observe relay-base-moved --line data/landings.txt:2 | head -1
```

```text
jobs/relay: v3 written
tests/relay/suite: new page (v1)
observed relay-base-moved: _post keeps its signature, looked up per call; endpoints are kagi_url() and scry_url() (RESEARCH_KAGI_URL, RESEARCH_SCRY_URL)
```

## 5. The return

Before it proposes, rowan asks the tip what moved since its fork left, and what a merge of its fork
and a judgment of its landing would say there now (`obend since`): the tip's own law and base on its
job page, which it has not seen; the harness's landing; the reasons; the refusals, by name. Nothing
lands and nothing is written at the tip. (On 2026-11-06 rowan had no such look: its first word on the
moved terms was the refusal, and the repair took a reviewer's message and a second session.)

```sh
cd rowan && obend since ../ws --proposal ../rowan-land.json
```

```text
since rowan left ../ws:
  jobs/harness: state offered → proposed, commit unset → "751b497", on unset → "ed1d477", assignee unset → sable, open 1 → 0, spent 0 → 2
  jobs/relay: its laws moved; base "ed1d477" → "751b497" (you wrote it too)
    + law suite: new.state in ["proposed", "landed"] implies not (new.suite == "")
  landed/harness: open 0 → 1
  residents/sable: its text moved
  evidence/harness/sable-1: new at the tip
  evidence/harness/reviewer-1: new at the tip
  tests/relay/suite: new at the tip
  you have not seen at jobs/relay: base, law suite
  the tip observes harness-unit-pass-751b497f3fab: result: "pass"
  the tip observes relay-base-moved: _post keeps its signature, looked up per call; endpoints are kagi_url() and scry_url() (RESEARCH_KAGI_URL, RESEARCH_SCRY_URL)
a merge of rowan now would land 4 page(s) and say:
  jobs/relay + jobs/relay: not merged: refused by jobs/_kind: onbase (the kind of jobs/, an ancestor of jobs/relay): `new.state in ["proposed", "landed"] implies new.on == new.base` does not hold; the line `base: ed1d477` would pass (the page has `base: `)
  jobs/relay: here's write stands (landed here before the merge)
  jobs/relay: kept from rowan: commit unset → "007f0e5401221dea20a481fafe3b90ce06bc973f", on unset → "ed1d477", assignee unset → rowan, spent 0 → 2
  jobs/relay: pending here, as rowan wrote it on this page as it is (state): refused by its law suite: `new.state in ["proposed", "landed"] implies not (new.suite == "")` does not hold; a line `suite: …` with a value would pass (the page has no `suite:` line it reads)
  behind-rowan: assumed here, rowan has not seen jobs/relay base, law suite; its explanations hold here only without it
  rowan's observation relay-sandbox-pass-007f0e540122: joined here
../rowan-land.json: would be refused, after that merge: land-relay: refused by its reasons: its justification relay-proven is unsupported now: nothing explains relay-proven
  outstanding here: land-relay intent 1fcef1ca77bea7b0 sent to ws
nothing landed; nothing written at the tip
```

rowan comes back as it was, to show what the tip does with it. Its fork's job page is refused at the tip by the job's law, by name (the suggestion
names the line that would pass); what it spent of its share came in; its evidence came in, and is
still evidence of what it was:

```sh
cd ws && obend merge ../rowan | grep -v '^rendered'
grep -E '^(kagi|kagispent):' resources/rowan.md
```

```text
residents/rowan: merged from rowan
resources/rowan: merged from rowan
evidence/relay/rowan-1: imported from rowan
evidence/relay/rowan-2: imported from rowan
jobs/relay: here's write stands (landed here before the merge)
jobs/relay: kept from rowan: commit unset → "007f0e5401221dea20a481fafe3b90ce06bc973f", on unset → "ed1d477", assignee unset → rowan, spent 0 → 2
jobs/relay: pending here, as rowan wrote it on this page as it is (state): refused by its law suite: `new.state in ["proposed", "landed"] implies not (new.suite == "")` does not hold; a line `suite: …` with a value would pass (the page has no `suite:` line it reads)
behind-rowan: assumed here, rowan has not seen jobs/relay base, law suite; its explanations hold here only without it
rowan's observation relay-sandbox-pass-007f0e540122: joined here
work: performed 0, retained 0 of 1
kagi: 1
kagispent: 1
jobs/relay + jobs/relay: not merged: refused by jobs/_kind: onbase (the kind of jobs/, an ancestor of jobs/relay): `new.state in ["proposed", "landed"] implies new.on == new.base` does not hold; the line `base: ed1d477` would pass (the page has `base: `)
```

Its evidence came back with it, observed in its fork; the reviewer's explanation that the relay is
proven by it holds unless the base moved, and the base moved: the evidence expired. The landing is
refused by its reasons, by name; its form was carried across the law change and still stands
(nothing to re-offer):

```sh
cd ws && obend reasons explain R-relay-007f0e5 relay-proven --if relay-sandbox-pass-007f0e540122 --unless relay-base-moved | head -1
obend reasons why relay-proven
```

```text
explained R-relay-007f0e5: relay-proven ⇐ relay-sandbox-pass-007f0e540122 unless relay-base-moved
relay-proven: unsupported: R-relay-007f0e5 is defeated by relay-base-moved (supported)
```

```sh refused
cd ws && obend judge ../rowan-land.json
```

```text
land-relay: transported over the laws of jobs/relay: nothing was promised; it continues
work: performed 0, retained 1 of 1
land-relay: refused by its reasons: its justification relay-proven is unsupported now: R-relay-007f0e5 is defeated by relay-base-moved (supported)
```

What already happened stays: the live Kagi search was paid (`kagispent: 1` at the tip), the two runs
rowan spent are on the job's page (kept from the refused page, field by field, each judged), the
landing intent is outstanding in rowan's fork until rowan releases it by name, and the refused rest of
rowan's page waits as the page's pending write, with why:

```sh
cd ws && grep -E '^(state|on|spent):' jobs/relay.md; obend status jobs/relay | head -1 | cut -c1-90
cd ../rowan && obend obligations && obend release 1fcef1ca77bea7b0
```

```text
state: proposed
spent: 2
on: "ed1d477"
jobs/relay v7; its last write was refused by its law suite: `new.state in ["proposed", "la
land-relay: intent 1fcef1ca77bea7b0 () sent to ws, awaiting its receipt
released intent 1fcef1ca77bea7b0: it awaits no receipt here; nothing outstanding
```

## 6. The repair lands, once

rowan rebuilds the relay on 751b497 through the harness's seams (ad3a6dc, a merge that keeps 007f0e5
reachable), writes its fork's job page to the tip's terms, runs both tests, explains in its fork why the
job is proven, and proposes again; its second fill is a new intent. Its explanation comes back with the
merge and is judged at the tip; it is no longer behind.

```sh
cd rowan && cp -R ../fx/rowan2/. . && cp -R ../fx/reviewer/tests/. tests/ && obend open | grep -v '^rendered'
obend reasons observe relay-sandbox-pass-ad3a6dc965bd --line evidence/relay/rowan-3.md:5 | head -1
obend reasons observe relay-suite-pass-ad3a6dc965bd --line evidence/relay/rowan-4.md:5 | head -1
obend reasons explain rowan-ad3a6dc relay-proven --if relay-sandbox-pass-ad3a6dc965bd --if relay-suite-pass-ad3a6dc965bd | head -1
obend fill ../land-relay.form --because relay-proven --out ../rowan-land2.json | tail -1
cd ../ws && obend merge ../rowan | grep -v '^rendered'
grep -E '^(state|on|base|suite|runs|spent):' jobs/relay.md
```

```text
jobs/relay: v4 written
residents/rowan: v3 written
evidence/relay/rowan-3: new page (v1)
evidence/relay/rowan-4: new page (v1)
tests/relay/suite: new page (v1)
observed relay-sandbox-pass-ad3a6dc965bd: result: "pass"
observed relay-suite-pass-ad3a6dc965bd: result: "pass"
explained rowan-ad3a6dc: relay-proven ⇐ relay-sandbox-pass-ad3a6dc965bd, relay-suite-pass-ad3a6dc965bd
wrote ../rowan-land2.json (intent 8e3b23be52ac5367)
residents/rowan: merged from rowan
evidence/relay/rowan-3: imported from rowan
evidence/relay/rowan-4: imported from rowan
jobs/relay: here's write stands (landed here before the merge)
jobs/relay: kept from rowan: commit "007f0e5401221dea20a481fafe3b90ce06bc973f" → "ad3a6dc965bdeaa0a94148274f591bc90a68e7f4", on "ed1d477" → "751b497", suite unset → "evidence/relay/rowan-4", spent 2 → 4
behind-rowan: withdrawn, rowan has seen what moved here
rowan's observation relay-sandbox-pass-ad3a6dc965bd: joined here
rowan's observation relay-suite-pass-ad3a6dc965bd: joined here
rowan's explanation rowan-ad3a6dc (relay-proven ⇐ relay-sandbox-pass-ad3a6dc965bd, relay-suite-pass-ad3a6dc965bd unless behind-rowan): joined here
  judged here: relay-proven: supported by rowan-ad3a6dc
work: performed 0, retained 0 of 1
state: proposed
runs: 5
spent: 4
base: "751b497"
on: "751b497"
suite: "evidence/relay/rowan-4"
jobs/relay + jobs/relay: not merged: refused by jobs/_kind: spent (the kind of jobs/, an ancestor of jobs/relay): `monotone(spent)` does not hold; spent = 2 would pass (this write has spent = 0)
```

The reviewer's runs on ad3a6dc are paid from the job too: the sandbox run is the fifth of five, and the
suite run is refused before it runs. rowan tops the job up from its share by a form:

```sh
cd ws && cp ../fx/reviewer/evidence/relay/reviewer-1.md evidence/relay/ && sed -i.bak 's/^spent: 4$/spent: 5/' jobs/relay.md && rm jobs/relay.md.bak && obend open
sed -i.bak 's/^spent: 5$/spent: 6/' jobs/relay.md && rm jobs/relay.md.bak && obend open
sed -i.bak 's/^spent: 6$/spent: 5/' jobs/relay.md && rm jobs/relay.md.bak && obend open
obend capture jobs/relay topup-relay --for rowan --grant resources/rowan --grant jobs/relay --move resources/rowan jobs/relay 1 --field runs > /dev/null
obend abstract topup-relay 1 runs > /dev/null && obend offer topup-relay runs 1..3 --promise 1..2 && obend form topup-relay --out ../topup.form > /dev/null
cd ../rowan.store && obend fill ../topup.form runs=1 --out ../topup.json | tail -1 && cd ../ws && obend judge ../topup.json | head -3
```

```text
jobs/relay: v13 written
evidence/relay/reviewer-1: new page (v1)
nothing changed
topup-relay: offers runs = 1..3, promises 1..2 (each value judged by the laws as they stand: 3 admitted)
wrote ../topup.json (intent c1142d078234f5ba)
topup-relay: landed as one turn over 2 pages by rowan, receipt 5d092c923777701b (4 in the chain)
  resources/rowan: runs 3 → 2
  jobs/relay: runs 5 → 6
jobs/relay: refused by jobs/_kind: budget (the kind of jobs/, an ancestor of jobs/relay): `new.spent <= new.runs` does not hold; the line `spent: 5` would pass (the page has `spent: 6`)
```

```sh
cd ws && cp ../fx/reviewer/evidence/relay/reviewer-2.md evidence/relay/ && sed -i.bak 's/^spent: 5$/spent: 6/' jobs/relay.md && rm jobs/relay.md.bak && obend open
obend reasons observe relay-sandbox-pass-ad3a6dc965bd --line evidence/relay/reviewer-1.md:5 | head -1
obend reasons observe relay-suite-pass-ad3a6dc965bd --line evidence/relay/reviewer-2.md:5 | head -1
obend reasons explain R-relay-ad3a6dc relay-proven --if relay-sandbox-pass-ad3a6dc965bd --if relay-suite-pass-ad3a6dc965bd | head -2
obend judge ../rowan-land2.json | head -4
```

```text
jobs/relay: v15 written
evidence/relay/reviewer-2: new page (v1)
explained R-relay-ad3a6dc: relay-proven ⇐ relay-sandbox-pass-ad3a6dc965bd, relay-suite-pass-ad3a6dc965bd
  no status changed
land-relay: landed as one turn over 2 pages by rowan, receipt b56292261a412fab (5 in the chain)
  jobs/relay: open 1 → 0
  landed/relay: open 0 → 1
rendered jobs/relay.md
refused: relay-sandbox-pass-ad3a6dc965bd is observed already
refused: relay-suite-pass-ad3a6dc965bd is observed already
```

```sh refused
cd ws && obend judge ../rowan-land2.json
```

```text
work: performed 0, retained 1 of 1
land-relay: refused: a duplicate: intent 8e3b23be52ac5367 has landed here as receipt b56292261a412fab (5 in the chain); it is not landed again
```

## 7. Retiring the finished jobs

Both jobs are landed and both forks merged. The forms that offered them have continuity contracts; a
fill of each landed here, so each promise is discharged, and the finished jobs' forms retire: the log
is compacted (on 2026-11-06 this was refused, "what it promised reaches past the horizon", and a vault
that offered work with promises could never forget):

```sh
cd ws && obend forget finished --retire accept-relay --retire land-relay --retire accept-harness --retire land-harness --retire topup-relay
```

```text
forgot 63 records (247044 bytes) under the retention contract finished, retiring accept-relay, land-relay, accept-harness, land-harness, topup-relay: the log is one checkpoint record of 206848 bytes
```

## 8. Defects the day exposed, fixed

A fork that pulls the tip after its taker's acceptance landed there, spends, and merges back: the
landing is ours come back, and the spend comes in (it used to be dropped as "not landed twice"):

```sh
cp -R fx/tip rt && cd rt && obend open > /dev/null
obend capture jobs/relay acc --for rowan --grant resources/rowan --grant jobs/relay --move resources/rowan jobs/relay 3 --field runs > /dev/null && obend form acc --out ../acc.form > /dev/null
obend fork ../rt-rowan && mkdir ../rt-store && cd ../rt-store && obend fill ../acc.form --out ../acc.json > /dev/null && cd ../rt && obend judge ../acc.json | head -1
cd ../rt-rowan && obend merge ../rt | grep -v '^rendered'
sed -i.bak 's/^spent: 0$/spent: 1/' jobs/relay.md && rm jobs/relay.md.bak && obend open
cd ../rt && obend merge ../rt-rowan | grep -v '^rendered'; grep -E '^(runs|spent):' jobs/relay.md
```

```text
forked rt-rowan: a copy of this vault, declared here until it merges
acc: landed as one turn over 2 pages by rowan, receipt dc4867402868159d (1 in the chain)
jobs/relay: merged from rt
resources/rowan: merged from rt
work: performed 0, retained 1 of 1
jobs/relay: v3 written
jobs/relay: merged from rt-rowan
runs: 3
spent: 1
```

A kind that gains `monotone(spent)` judges the next write that lowers `spent` (it used to be judged
as an adoption at its new state, and `monotone` held vacuously: a spent run could be taken back):

```sh refused
cd rt && sed -i.bak 's/^law spent: monotone(spent)$//' jobs/_kind.md && rm jobs/_kind.md.bak && obend open
sed -i.bak 's/^spent: .*$/spent: 2/' jobs/relay.md && rm jobs/relay.md.bak && obend open
python3 -c "p='jobs/_kind.md'; s=open(p).read(); open(p,'w').write(s.replace('law budget: new.spent <= new.runs', 'law budget: new.spent <= new.runs\\nlaw spent: monotone(spent)', 1))" && obend open
sed -i.bak 's/^spent: 2$/spent: 0/' jobs/relay.md && rm jobs/relay.md.bak && obend open
```

```text
jobs/_kind: v2 written
jobs/relay: v4 written
jobs/_kind: v3 written
jobs/relay: refused by jobs/_kind: spent (the kind of jobs/, an ancestor of jobs/relay): `monotone(spent)` does not hold; the line `spent: 2` would pass (the page has `spent: 0`)
```

A suggestion names a value that reads back as a label: quoted when it is not one word:

```sh refused
cd ws && sed -i.bak 's/^artifact: "007f0e540122"$/artifact: "9abc"/' evidence/relay/rowan-2.md && rm evidence/relay/rowan-2.md.bak && obend open | grep rowan-2
```

```text
evidence/relay/rowan-2: refused by evidence/_kind: fixed (the kind of evidence/, an ancestor of evidence/relay/rowan-2): `writeOnce(result) and writeOnce(artifact) and writeOnce(test) and writeOnce(run)` does not hold; the line `artifact: "007f0e540122"` would pass (the page has `artifact: "9abc"`)
```
