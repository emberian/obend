# The right to forget: a walkthrough

A vault's log is its truth, and it grows with every command; every command reads all of it. A vault
may forget a prefix of its log, but only by a declared judgment: a `forget` turn names a RETENTION
CONTRACT, is refused by name while anything still admissible needs the prefix (a proposal sent and not
confirmed, a form issued and not retired, a form whose continuity contract promised the future, a
branch declared and not merged), and, admitted, replaces the log by one CHECKPOINT RECORD carrying the
world, the number of records forgotten, the digest of their bytes, and the receipt digest they ended
at. The records after it follow that digest, so the chain is checked across it. A correction that
rests on the forgotten prefix arrives later than the contract allows: it is refused, naming the
contract (`Obend.Vault.Retention`; `forget_sound`, `forget_refused_when_needed`,
`late_correction_refused` in `Obend.Vault.Replay`).

Every block below is run, in order, by `python3 tests/vault/walkthrough.py --doc tests/vault/RETAIN.md`
(from `lean/`, after `lake build obend`), and what it prints is checked against the block after it.

## 1. A vault that has been used

Alice keeps two accounts and a budget, edits Carol's page a few times, opens the vault forty times
more (each command is a record of the log), and issues a form for Bob. She declares a branch, a copy
on her laptop, and also copies the vault by hand, undeclared.

```sh
mkdir -p alice/ledger && cd alice
printf -- '---\nbalance: 100\n---\n# Alice\n' > ledger/alice.md
printf -- '---\nbalance: 5\n---\n# Carol\n' > ledger/carol.md
printf -- '# Budget\n\nThis month [[ledger/alice]] pays [[ledger/carol]] 30.\n' > Budget.md
obend open > /dev/null
for i in 1 2 3 4 5; do printf -- "---\nbalance: 5\n---\n# Carol\n\nNote $i.\n" > ledger/carol.md; obend open > /dev/null; done
for i in $(seq 40); do obend status > /dev/null; done
obend capture Budget pay --for bob --grant 'ledger/*' --move ledger/alice ledger/carol 30 | head -1
obend abstract pay 30 amount > /dev/null && obend form pay --out ../pay.form > /dev/null
obend fork ../laptop && cp -R . ../old
cd .. && mkdir bob && cd bob && obend fill ../pay.form amount=10 --out ../pay.json | tail -1
```

```text
captured pay from Budget for bob: 2 page(s) shown, 1 not shown to bob
forked laptop: a copy of this vault, declared here until it merges
wrote ../pay.json (intent a03db6b12ca11e10)
```

What every command reads, before:

```sh
cd alice && obend log | head -2
```

```text
log: 52 records, 14381 bytes, each following the one before it from the genesis sentinel
a command reads: the log, 14381 bytes, and the checkpoint, 5213 bytes
```

## 2. Refused while something needs the prefix

Bob's store has sent a proposal it has no receipt for: it may not forget.

```sh refused
cd bob && obend forget tidy
```

```text
refused: the proposal a03db6b12ca11e10 of pay sent from here awaits its receipt: an obligation reaches into the prefix
```

Alice's vault has a form out, then a branch out: each is named, with what would let the forget go.

```sh refused
cd alice && obend forget q4
```

```text
refused: the form pay was issued against the prefix and stands; retire it (--retire pay) or keep the prefix
```

```sh refused
cd alice && obend forget q4 --retire pay
```

```text
refused: the branch laptop forked from the prefix and has not merged; merge it or abandon it (--abandon laptop)
```

## 3. Stopped in the middle of a forget

The forget turn is appended to the log, whole; then the new log, one checkpoint record, is written
beside it. The process is stopped by its PID 300 bytes into that write (`OBEND_TEST_COMPACT=K:PATH`,
the store's test-only barrier).

```sh
cd alice
OBEND_TEST_COMPACT=300:$PWD/../barrier nohup obend forget q4 --retire pay --abandon laptop > ../forget.out 2>&1 &
echo $! > ../obend.pid
for i in $(seq 200); do [ -e ../barrier ] && break; sleep 0.05; done
kill "$(cat ../obend.pid)"; wait "$(cat ../obend.pid)" 2>/dev/null; rm ../barrier ../obend.pid ../forget.out
ls -l .obend/log.new | awk '{print $5}'; obend log | tail -2
```

```text
300
world d85febf7826ed1ce: as record 56 commits to it
one world
```

The log is as it was, ending in the forget, and is one world. Opening the vault drops the torn new
log by name and compacts again.

```sh
cd alice && obend open && obend log
```

```text
recovered: an interrupted forget's new log (300 bytes) dropped; the log stands
recovered: the forget at record 56 was whole and the log was not compacted: compacted to one checkpoint record
nothing changed
log: 2 records, 5820 bytes, each following the one before it from the genesis sentinel through a checkpoint record: 56 forgotten records (prefix digest 7a36c466805daf8e), ending at receipt 3228e57856a97ce4
a command reads: the log, 5820 bytes, and the checkpoint, 0 bytes
last record: 2 (open), bytes 5548 to 5820
checkpoint: none; the world is replayed from genesis
world d85febf7826ed1ce: replayed from genesis
world d85febf7826ed1ce: the checkpoint and the records after it
world d85febf7826ed1ce: as record 2 commits to it
one world
```

What every command reads, after: the checkpoint record and the record after it; no checkpoint file is
written until the records after the checkpoint record outweigh it.

## 4. The chain goes on across the checkpoint record

Alice edits Carol's page. The record follows the anchor the checkpoint record carries; `obend log`
reads the log from genesis through it, and the world is one.

```sh
cd alice && printf -- "---\nbalance: 5\n---\n# Carol\n\nAfter the forget.\n" > ledger/carol.md && obend open && obend log records
```

```text
ledger/carol: v7 written
log: 3 records, 6142 bytes, each following the one before it from the genesis sentinel through a checkpoint record: 56 forgotten records (prefix digest 7a36c466805daf8e), ending at receipt 3228e57856a97ce4
a command reads: the log, 6142 bytes, and the checkpoint, 0 bytes
  record 1 (compacted): bytes 0 to 5548
  record 2 (open): bytes 5548 to 5820
  record 3 (open): bytes 5820 to 6142
last record: 3 (open), bytes 5820 to 6142
checkpoint: none; the world is replayed from genesis
world 4515703e2d4113e6: replayed from genesis
world 4515703e2d4113e6: the checkpoint and the records after it
world 4515703e2d4113e6: as record 3 commits to it
one world
```

## 5. Late corrections are refused by name

Bob's proposal fills a form the contract retired:

```sh refused
cd alice && obend judge ../pay.json
```

```text
pay: refused: late: the form was retired by the retention contract q4; a proposal for it rests on a forgotten prefix of the log
work: performed 0, retained 1 of 1
```

The laptop is a branch the contract abandoned:

```sh refused
cd alice && obend merge ../laptop
```

```text
not merged: late: laptop was abandoned by the retention contract q4
```

The copy made by hand forked before the forgotten prefix ended: its log does not reach the horizon.

```sh refused
cd alice && obend merge ../old
```

```text
not merged: late: old's log does not reach the horizon of the retention contract q4 (it forked before the prefix forgotten here); its corrections would arrive later than the contract allows
```

A branch forked after the forget starts from the same checkpoint record, reaches the horizon, and
merges.

```sh
cd alice && obend fork ../after && (cd ../after && printf -- '# Notes\n\nWritten after.\n' > Notes.md && obend open > /dev/null)
obend merge ../after && obend log | tail -1
```

```text
forked after: a copy of this vault, declared here until it merges
Notes: imported from after
rendered Notes.md
one world
```
