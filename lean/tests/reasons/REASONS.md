# Keeping reasons: a walkthrough

A process keeps its reasons in `Obend.Reasons`: what it observed (a line, verbatim, with where it was
read), what it assumed (a hypothesis it may withdraw), the explanations it proposed (a conclusion from
premises, unless a defeater is supported), the defeaters it declared, and the actions it proposed,
each with its justification. Nothing stores "this holds". Whether a conclusion is usable now is the
well-founded model of the observations, the assumptions held and the explanations (Van Gelder, Ross
and Schlipf 1991, by the alternating fixpoint): SUPPORTED, UNDEFINED or UNSUPPORTED. Whether an action
is admissible is whether its justification is supported now.

Every `obend reasons` command is one turn of the directory's log (`.obend/log`, the same log a vault
keeps; `Obend.Vault.Replay`'s `reasoned` turn). Each prints what changed status and how many atoms it
judged anew: an observation or an assumption recomputes only the atoms that depend on it, over what
they depend on, and keeps the rest (`Obend.Reasons.from_scratch_consistent`: what it keeps is what
recomputing everything would give).

Every block below is run, in order, by `python3 tests/vault/walkthrough.py --doc tests/reasons/REASONS.md`
(from `lean/`, after `lake build obend`), and what it prints is checked against the block after it.

## A stuck build, reasoned about from its own log

The first consumer is the swarm's own process. On 2026-11-05 the lane building the fabric's certificate
(`fabric5`) ran `lake build` of `Obend.Hardware.Fabulous.Mac8Tiles` on hbox, and one module,
`Obend.Hardware.Fabulous.Mac8CertCheck`, took 1818 s: three times the 600 s a tier-2 module may take.
Why? The observations are lines of the build's own log, `~/obend/logs/fabric5-tiles.log` on hbox,
copied here whole, and of the listing of that directory (`ls -l --time-style=+%Y-%m-%dT%H:%M:%S` of
the five files named), copied here as printed. Nothing below is made up but the names given to
things.

```sh
mkdir swarm && cd swarm
cat > fabric5-tiles.log <<'LOG'
⚠ [2/20] Replayed Obend.Hardware.HDL
warning: Obend/Hardware/HDL.lean:592:14: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: Obend/Hardware/HDL.lean:593:36: `if_false` has been deprecated: Use `ite_false` instead

Hint: Replace the deprecated name:
  i̵f̵_̵f̵a̵l̵s̵e̵i̲t̲e̲_̲f̲a̲l̲s̲e̲
✔ [19/20] Built Obend.Hardware.Fabulous.Mac8CertCheck (1818s)
✔ [20/20] Built Obend.Hardware.Fabulous.Mac8Tiles (312ms)
Build completed successfully (20 jobs).
LOG
cat > listing.txt <<'LS'
-rw-rw-r-- 1 hbox hbox     581 2026-11-05T23:17:14 fabric5-tiles.log
-rw-rw-r-- 1 hbox hbox       8 2026-11-05T22:46:55 fabric5-tiles.pid
-rw-rw-r-- 1 hbox hbox       7 2026-11-05T23:05:28 inet-run.pid
-rw-rw-r-- 1 hbox hbox 3150657 2026-11-05T23:12:25 inet-tier2.log
-rw-rw-r-- 1 hbox hbox 1557377 2026-11-05T22:36:41 replay-tier1b.log
LS
obend reasons observe slow --line fabric5-tiles.log:10
```

```text
observed slow: ✔ [19/20] Built Obend.Hardware.Fabulous.Mac8CertCheck (1818s)
  slow: supported (was unsupported)
  judged anew: 1 of 1 atoms
```

A first explanation that explains nothing: the box was contended because it was swapping, and it was
swapping because it was contended. Each rests on the other, and nothing observed or assumed enters
the loop. An unsupported cycle cannot create a conclusion (`Obend.Reasons.no_conclusion_from_cycles`):
both are unsupported, and each says why.

```sh
cd swarm
obend reasons explain L1 swapping --if contention
obend reasons explain L2 contention --if swapping
obend reasons status
```

```text
explained L1: swapping ⇐ contention
  no status changed
  judged anew: 3 of 3 atoms
explained L2: contention ⇐ swapping
  no status changed
  judged anew: 3 of 3 atoms
slow: supported (observed at fabric5-tiles.log:10)
swapping: unsupported: L1 lacks contention (unsupported; it rests on swapping itself, an unfounded cycle)
contention: unsupported: L2 lacks swapping (unsupported; it rests on contention itself, an unfounded cycle)
```

Two competing explanations, each with its abducible. Contention: other lanes' builds held the box
(assumed: `concurrent-builds`). Kernel-bound: the module is its own cost, every `decide +kernel` in
it one chunk of the certificate's table (assumed: `heavy-decides`). Each excludes the other: each is
defeated while the other is supported. Nothing yet tells them apart, and the well-founded model
declines to choose: both are UNDEFINED, and so is everything resting on either. (The stable models of
the same program would be two, one per choice.)

```sh
cd swarm
obend reasons assume concurrent-builds
obend reasons assume heavy-decides
obend reasons explain R1 contention --if slow --if concurrent-builds --unless kernel-bound
obend reasons explain R2 kernel-bound --if slow --if heavy-decides --unless contention
```

```text
assumed concurrent-builds
  concurrent-builds: supported (was unsupported)
  judged anew: 1 of 4 atoms
assumed heavy-decides
  heavy-decides: supported (was unsupported)
  judged anew: 1 of 5 atoms
explained R1: contention ⇐ slow, concurrent-builds unless kernel-bound
  swapping: supported (was unsupported)
  contention: supported (was unsupported)
  judged anew: 6 of 6 atoms
explained R2: kernel-bound ⇐ slow, heavy-decides unless contention
  swapping: undefined (was supported)
  contention: undefined (was supported)
  kernel-bound: undefined (was unsupported)
  judged anew: 6 of 6 atoms
```

Evidence attached to one. The listing shows lane `inet` starting at 23:05:28 (its PID file) and its
tier-2 log last written at 23:12:25: both inside the window of the slow build, whose PID file was
written at 22:46:55 and its log at 23:17:14. That is a second explanation of contention, resting on
two observations and on no assumption. Contention becomes supported, and kernel-bound, defeated by
it, unsupported.

```sh
cd swarm
obend reasons observe inet-started --line listing.txt:3
obend reasons observe inet-finished --line listing.txt:4
obend reasons explain R3 contention --if slow --if inet-started --if inet-finished
```

```text
observed inet-started: -rw-rw-r-- 1 hbox hbox       7 2026-11-05T23:05:28 inet-run.pid
  inet-started: supported (was unsupported)
  judged anew: 1 of 7 atoms
observed inet-finished: -rw-rw-r-- 1 hbox hbox 3150657 2026-11-05T23:12:25 inet-tier2.log
  inet-finished: supported (was unsupported)
  judged anew: 1 of 8 atoms
explained R3: contention ⇐ slow, inet-started, inet-finished
  swapping: supported (was undefined)
  contention: supported (was undefined)
  kernel-bound: unsupported (was undefined)
  judged anew: 8 of 8 atoms
```

An action, proposed with its justification: rebuild the module alone on an idle box. It is
admissible while contention is supported.

```sh
cd swarm
obend reasons propose rebuild-alone --because contention
```

```text
proposed rebuild-alone because contention
  no status changed
  judged anew: 0 of 8 atoms
  rebuild-alone: admissible now
```

The first support is withdrawn: nobody checked which other builds ran, so `concurrent-builds` goes.
Contention had two supports (R1 rested on the assumption, R3 on the listing); it stands on R3 and
does not change status. The step replaces the judgment whole, so there is no state in which
contention is absent (`Obend.Reasons.survives_one_support`).

```sh
cd swarm
obend reasons withdraw concurrent-builds
obend reasons why contention
obend reasons admit rebuild-alone
```

```text
withdrew concurrent-builds
  concurrent-builds: unsupported (was supported)
  judged anew: 8 of 8 atoms
contention: supported by R3
rebuild-alone: admitted (contention is supported by R3)
```

A defeater, declared before its evidence: if the build ran alone for its first part (no other obend
build between the previous one's end and `inet`'s start), the overlap cannot explain 1818 s, and R3
is defeated. Declaring it changes nothing: a defeat happens by evidence, and the evidence is not in
yet.

```sh
cd swarm
obend reasons explain A alone --if fabric-started --if replay-finished --if inet-started
obend reasons defeat R3 --by alone
```

```text
explained A: alone ⇐ fabric-started, replay-finished, inet-started
  no status changed
  judged anew: 11 of 11 atoms
R3 is defeated while alone is supported
  no status changed
  judged anew: 11 of 11 atoms
```

The evidence comes in from the same listing: the slow build's PID file at 22:46:55, and lane
`replay`'s tier-1 log last written at 22:36:41, before it. The build ran alone (among obend's lanes)
for its first eighteen minutes. R3 is defeated; R1 lost its assumption; the loop through swapping
cannot hold contention up. Contention is unsupported, and kernel-bound, no longer defeated, is
supported by R2.

```sh
cd swarm
obend reasons observe fabric-started --line listing.txt:2
obend reasons observe replay-finished --line listing.txt:5
```

```text
observed fabric-started: -rw-rw-r-- 1 hbox hbox       8 2026-11-05T22:46:55 fabric5-tiles.pid
  fabric-started: supported (was unsupported)
  judged anew: 11 of 11 atoms
observed replay-finished: -rw-rw-r-- 1 hbox hbox 1557377 2026-11-05T22:36:41 replay-tier1b.log
  replay-finished: supported (was unsupported)
  swapping: unsupported (was supported)
  contention: unsupported (was supported)
  kernel-bound: supported (was unsupported)
  alone: supported (was unsupported)
  judged anew: 11 of 11 atoms
```

The action is inadmissible now, by name, with every reason its justification fails.

```sh refused
cd swarm && obend reasons admit rebuild-alone
```

```text
refused: rebuild-alone is not admissible: its justification contention is unsupported now: L2 lacks swapping (unsupported; it rests on contention itself, an unfounded cycle); R1 lacks concurrent-builds (unsupported, withdrawn); R3 is defeated by alone (supported)
```

What the reasons now license instead, and the whole state.

```sh
cd swarm
obend reasons propose split-the-table --because kernel-bound
obend reasons status
```

```text
proposed split-the-table because kernel-bound
  no status changed
  judged anew: 0 of 11 atoms
  split-the-table: admissible now
slow: supported (observed at fabric5-tiles.log:10)
inet-started: supported (observed at listing.txt:3)
inet-finished: supported (observed at listing.txt:4)
fabric-started: supported (observed at listing.txt:2)
replay-finished: supported (observed at listing.txt:5)
concurrent-builds: unsupported: concurrent-builds was withdrawn
heavy-decides: supported (assumed)
swapping: unsupported: L1 lacks contention (unsupported; it rests on swapping itself, an unfounded cycle)
contention: unsupported: L2 lacks swapping (unsupported; it rests on contention itself, an unfounded cycle); R1 lacks concurrent-builds (unsupported, withdrawn); R3 is defeated by alone (supported)
kernel-bound: supported by R2
alone: supported by A
action rebuild-alone: inadmissible (because contention, unsupported)
action split-the-table: admissible (because kernel-bound)
```

The log can forget its prefix (`obend forget`, `Obend.Vault.Retention`): the reasons are world state,
not a reading of the log, so the checkpoint record carries them whole, and an action admissible
before the forget is admissible after it (`Obend.Vault.Replay.forget_keeps_reasons`). A standing
proposed action is therefore not something a retention contract must hold back: nothing its
justification rests on is in the prefix.

```sh
cd swarm
obend forget swarm-1
obend reasons admit split-the-table
```

```text
forgot 19 records (5429 bytes) under the retention contract swarm-1: the log is one checkpoint record of 2412 bytes
split-the-table: admitted (kernel-bound is supported by R2)
```

## A form's fill carries a justification

A fill's evidence is a justification in the same substrate, and the vault's judge consumes it: a
proposal whose fill says `--because X` is judged only while `X` is supported in the vault's own
reasons (`Obend.Vault.Replay.justified_needs_support`), and refused by its reasons, by name,
otherwise. Alice keeps two accounts and captures her payment to Carol as a form for Bob, its amount a
hole. Her reasons: an invoice observed, an assumption that it is genuine, and an explanation that
Carol is owed.

```sh
mkdir -p alice/ledger && cd alice
printf -- '---\nbalance: 100\n---\n# Alice\n' > ledger/alice.md
printf -- '---\nbalance: 5\n---\n# Carol\n' > ledger/carol.md
printf -- '# Budget\n\nThis month [[ledger/alice]] pays [[ledger/carol]] 30.\n' > Budget.md
obend open > /dev/null
obend capture Budget pay --for bob --grant 'ledger/*' --move ledger/alice ledger/carol 30 | head -1
obend abstract pay 30 amount > /dev/null
obend form pay --out ../pay.form | tail -1
obend reasons observe invoice 'Carol: invoice 17, 30 for October hosting'
obend reasons assume invoice-genuine
obend reasons explain owed carol-owed --if invoice --if invoice-genuine
```

```text
captured pay from Budget for bob: 2 page(s) shown, 1 not shown to bob
wrote ../pay.form
observed invoice: Carol: invoice 17, 30 for October hosting
  invoice: supported (was unsupported)
  judged anew: 1 of 1 atoms
assumed invoice-genuine
  invoice-genuine: supported (was unsupported)
  judged anew: 1 of 2 atoms
explained owed: carol-owed ⇐ invoice, invoice-genuine
  carol-owed: supported (was unsupported)
  judged anew: 3 of 3 atoms
```

Bob fills it in his own store, and the fill carries its justification.

```sh
mkdir bob && cd bob
obend fill ../pay.form amount=30 --because carol-owed --out ../pay.json
```

```text
pay: filled by bob: amount = 30
  ledger/alice.balance := 70
  ledger/carol.balance := 35
  because carol-owed
wrote ../pay.json (intent 7fdbb45ffae7ef38)
```

Before judging it, Alice learns that invoices of that series were forged, and withdraws the
assumption that this one is genuine. Bob's fill is refused by its reasons, naming the withdrawn
assumption; nothing lands, and a refused turn is not logged.

```sh refused
cd alice
obend reasons withdraw invoice-genuine
obend judge ../pay.json
```

```text
withdrew invoice-genuine
  invoice-genuine: unsupported (was supported)
  carol-owed: unsupported (was supported)
  judged anew: 3 of 3 atoms
work: performed 0, retained 1 of 1
pay: refused by its reasons: its justification carol-owed is unsupported now: owed lacks invoice-genuine (unsupported, withdrawn)
```

Carol confirms invoice 17 by phone: a new observation, and a second explanation of the debt that does
not rest on the withdrawn assumption. The same proposal is judged again, and lands.

```sh
cd alice
obend reasons observe confirmed 'Carol, by phone: invoice 17 is ours'
obend reasons explain owed-confirmed carol-owed --if invoice --if confirmed
obend judge ../pay.json
```

```text
observed confirmed: Carol, by phone: invoice 17 is ours
  confirmed: supported (was unsupported)
  judged anew: 1 of 4 atoms
explained owed-confirmed: carol-owed ⇐ invoice, confirmed
  carol-owed: supported (was unsupported)
  judged anew: 4 of 4 atoms
pay: landed as one turn over 2 pages by bob, receipt 86ea158d7dbd1341 (1 in the chain)
  ledger/alice: balance 100 → 70
  ledger/carol: balance 5 → 35
rendered ledger/alice.md
rendered ledger/carol.md
work: performed 1, retained 1 of 1
```

## The planted test

`python3 tests/reasons/reasons_planted.py` (from `lean/`) builds a mutant in which `Γ` starts from
every atom instead of from none: the greatest fixpoint, which lets a cycle support itself. Its
theorems are replaced by `sorry` (they are what catch the mutant at build time; the test asks the
walkthrough to catch it at run time too), its `obend` built, and this walkthrough run with it. A
mutant whose walkthrough passes fails the test.
