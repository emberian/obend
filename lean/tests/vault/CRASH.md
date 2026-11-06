# Power loss is an interruption: a walkthrough

A vault's world is a function of its log. Every command appends its turns to `.obend/log`, one
record each (the receipt of the record before it, the world's commitment before and after, the
digest of the turn, the turn, a seal), and only then writes files; `.obend/checkpoint` is a cache of
the world after the log's first records (`Obend.Vault.Log`, `Obend.Vault.Replay`). This walkthrough
stops `obend` in the middle of a write and opens the vault again: the world it serves is the replay
of the records that were whole, the bytes after them are dropped by name, and the books still
balance.

Every block below is run, in order, by `python3 tests/vault/crash.py` (from `lean/`, after `lake build
obend`); what it prints is checked against the block after it. A process is started detached with its
own PID file and stopped by that PID at a write barrier the store exposes to tests
(`OBEND_TEST_TEAR=N:K:PATH`: appending record `N`, write its first `K` bytes, or `all` of them and
none of its files, create `PATH`, and wait).

## 1. Books

Three accounts, a kind of invoice whose posting moves its amount, and a register that balances.

```sh
mkdir books && cd books && mkdir accounts invoices register
for a in Cash Receivables Revenue; do printf -- '---\ncode: 1000\n---\n# %s\n' $a > accounts/$a.md; done
cat > invoices/_kind.md <<'MD'
---
amount: 0
period: 0
---
An invoice: the customer owes us its amount.

- debit [[accounts/Receivables]] amount
- credit [[accounts/Revenue]] amount
MD
cat > register/_kind.md <<'MD'
---
law balanced: new.debits == new.credits
---
The register.
MD
printf -- '---\nkind: invoices\namount: 500\nperiod: 11\n---\nAcme Ltd.\n' > invoices/INV-1.md
printf -- '---\nkind: invoices\namount: 250\nperiod: 11\n---\nInitech.\n' > invoices/INV-2.md
obend open > /dev/null && obend ledger post invoices/INV-1 && obend ledger post invoices/INV-2
obend log records
```

```text
invoices/INV-1: posted as P-0001 (period 11): debit accounts/Receivables 500, credit accounts/Revenue 500
receipt .obend/receipts/P-0001.json
invoices/INV-2: posted as P-0002 (period 11): debit accounts/Receivables 250, credit accounts/Revenue 250
receipt .obend/receipts/P-0002.json
log: 7 records, 3983 bytes, each following the one before it from the genesis sentinel
  record 1 (open): bytes 0 to 821
  record 2 (open): bytes 821 to 1208
  record 3 (rows): bytes 1208 to 1668
  record 4 (open): bytes 1668 to 2377
  record 5 (open): bytes 2377 to 2789
  record 6 (rows): bytes 2789 to 3249
  record 7 (open): bytes 3249 to 3983
last record: 7 (open), bytes 3249 to 3983
checkpoint: the world after record 7
world 4da43ce1128ea676: replayed from genesis
world 4da43ce1128ea676: the checkpoint and the records after it
world 4da43ce1128ea676: as record 7 commits to it
one world
```

`obend log` reads the log and changes nothing. It says the world three ways, which must be one: the
replay of every record from genesis, the checkpoint with the records after it, and the commitment the
last record's receipt names.

## 2. Stopped in the middle of a record

A third invoice. `obend ledger post` appends an open (it reads the new page), the register's row,
and an open again (it reads the posting's page). The process is stopped after 100 bytes of the row's
record.

```sh
cd books
printf -- '---\nkind: invoices\namount: 125\nperiod: 11\n---\nGlobex.\n' > invoices/INV-3.md
n=$(obend log | sed -n 's/^log: \([0-9]*\) records.*/\1/p')
OBEND_TEST_TEAR=$((n + 2)):100:$PWD/../barrier nohup obend ledger post invoices/INV-3 > ../post.out 2>&1 &
echo $! > ../obend.pid
for i in $(seq 200); do [ -e ../barrier ] && break; sleep 0.05; done
kill "$(cat ../obend.pid)"; wait "$(cat ../obend.pid)" 2>/dev/null; rm ../barrier ../obend.pid ../post.out
ls register; obend log
```

```text
P-0001.md
P-0002.md
_kind.md
log: 8 records, 4502 bytes, each following the one before it from the genesis sentinel
last record: 8 (open), bytes 3983 to 4502
torn tail: 100 bytes after record 8, dropped (torn: the bytes end inside a record)
checkpoint: the world after record 8
world b5326434b2cbd9c2: replayed from genesis
world b5326434b2cbd9c2: the checkpoint and the records after it
world b5326434b2cbd9c2: as record 8 commits to it
one world
```

The log holds the records before the row (the last of them the open the stopped process committed,
and checkpointed, before it), then 100 bytes that are not a record: `obend log` names them and does
not read them as a turn.

Opening the vault again drops the torn tail (and says so), and the register is as it was: two
postings, the books balanced.

```sh
cd books && obend ledger status && obend report trial-balance 11 && obend log
```

```text
recovered: dropped a tail of 100 bytes after record 8 (torn: the bytes end inside a record)
register: 2 posting(s), closed through period 0
  number  document              period     amount
  P-0001  invoices/INV-1        period 11     500  live
  P-0002  invoices/INV-2        period 11     250  live
balances (every period):
  account                    debit  credit
  accounts/Receivables         750       0
  accounts/Revenue               0     750
  total                        750     750
trial balance, period 11 (register root b1d5cdfe0dc6…, 2 posting(s) in the register)
  account                    debit  credit
  accounts/Receivables         750       0
  accounts/Revenue               0     750
  total                        750     750
postings: P-0001, P-0002
checked (trial-balance@1, decidable, compiled): every posting of period 11 is in it
wrote reports/TB-11.md
log: 11 records, 6148 bytes, each following the one before it from the genesis sentinel
last record: 11 (open), bytes 5424 to 6148
checkpoint: the world after record 11
world 5296fdb046dc9584: replayed from genesis
world 5296fdb046dc9584: the checkpoint and the records after it
world 5296fdb046dc9584: as record 11 commits to it
one world
```

Posting the invoice again goes through.

```sh
cd books && obend ledger post invoices/INV-3 && obend log
```

```text
invoices/INV-3: posted as P-0003 (period 11): debit accounts/Receivables 125, credit accounts/Revenue 125
receipt .obend/receipts/P-0003.json
log: 14 records, 7898 bytes, each following the one before it from the genesis sentinel
last record: 14 (open), bytes 7092 to 7898
checkpoint: the world after record 14
world 038a0276379fc232: replayed from genesis
world 038a0276379fc232: the checkpoint and the records after it
world 038a0276379fc232: as record 14 commits to it
one world
```

## 3. Stopped at every byte of a record

A member is added: one small record at the end of the log. A copy of the vault is cut at every byte
of that record, from its first to its last, and each copy is opened again. A cut inside the record
recovers the records before it and names the bytes it dropped; a cut at either end drops nothing.
Every copy serves one world and keeps the register.

```sh
cd books && obend member add ann --grant post:invoices/* && obend log | sed -n 's/^last record/&/p'
```

```text
member ann may post invoices/*
last record: 15 (member), bytes 7898 to 8129
```

```sh
cd books
read start stop < <(obend log | sed -n 's/^last record: [0-9]* (member), bytes \([0-9]*\) to \([0-9]*\)$/\1 \2/p')
cp .obend/log ../log.whole
bad=0
for k in $(seq "$start" "$stop"); do
  rm -rf ../cut && cp -R . ../cut && head -c "$k" ../log.whole > ../cut/.obend/log
  got=$(cd ../cut && obend ledger status | head -2)
  if [ "$k" = "$start" ] || [ "$k" = "$stop" ]; then
    want="register: 3 posting(s), closed through period 0
  number  document              period     amount"
  else
    want="recovered: dropped a tail of $((k - start)) bytes after record 14 (torn: the bytes end inside a record)
register: 3 posting(s), closed through period 0"
  fi
  [ "$got" = "$want" ] || { bad=$((bad + 1)); echo "cut at $k: $got"; }
  (cd ../cut && obend log | tail -1 | grep -qx "one world") || { bad=$((bad + 1)); echo "cut at $k: not one world"; }
done
echo "$((stop - start + 1)) cuts of record 15, at bytes $start to $stop, each reopened: $bad failed"
rm -rf ../cut ../log.whole
```

```text
232 cuts of record 15, at bytes 7898 to 8129, each reopened: 0 failed
```

## 4. Stopped after a record and before its files

The record of a turn is whole, and the process stops before writing any file the turn makes: here a
posting's receipt and page. Opening again writes them from the replay of the log, where the files are
still what the turn found.

```sh
cd books
printf -- '---\nkind: invoices\namount: 75\nperiod: 11\n---\nHooli.\n' > invoices/INV-4.md
n=$(obend log | sed -n 's/^log: \([0-9]*\) records.*/\1/p')
OBEND_TEST_TEAR=$((n + 2)):all:$PWD/../barrier nohup obend ledger post invoices/INV-4 > ../post.out 2>&1 &
echo $! > ../obend.pid
for i in $(seq 200); do [ -e ../barrier ] && break; sleep 0.05; done
kill "$(cat ../obend.pid)"; wait "$(cat ../obend.pid)" 2>/dev/null; rm ../barrier ../obend.pid ../post.out
ls register .obend/receipts
obend ledger status && obend verify .obend/receipts/P-0004.json && obend report trial-balance 11 && obend log
```

```text
.obend/receipts:
P-0001.json
P-0002.json
P-0003.json

register:
P-0001.md
P-0002.md
P-0003.md
_kind.md
recovered: record 17 (rows) was whole and its files were not: wrote .obend/receipts/P-0004.json, register/P-0004.md
register: 4 posting(s), closed through period 0
  number  document              period     amount
  P-0001  invoices/INV-1        period 11     500  live
  P-0002  invoices/INV-2        period 11     250  live
  P-0003  invoices/INV-3        period 11     125  live
  P-0004  invoices/INV-4        period 11      75  live
balances (every period):
  account                    debit  credit
  accounts/Receivables         950       0
  accounts/Revenue               0     950
  total                        950     950
P-0004: invoices/INV-4 in period 11, admitted at closed-through 0 over 3 posting(s): debit accounts/Receivables 75, credit accounts/Revenue 75
verified (posting@1: the row re-judged under the register's law it carries)
trial balance, period 11 (register root d5d3385424e2…, 4 posting(s) in the register)
  account                    debit  credit
  accounts/Receivables         950       0
  accounts/Revenue               0     950
  total                        950     950
postings: P-0001, P-0002, P-0003, P-0004
checked (trial-balance@1, decidable, compiled): every posting of period 11 is in it
wrote reports/TB-11.md
log: 20 records, 11425 bytes, each following the one before it from the genesis sentinel
last record: 20 (open), bytes 10585 to 11425
checkpoint: the world after record 20
world 80c7ac454cdcf341: replayed from genesis
world 80c7ac454cdcf341: the checkpoint and the records after it
world 80c7ac454cdcf341: as record 20 commits to it
one world
```

## 5. A record cut out of the middle

Each record carries the digest of the one before it. A copy of the log with its third record cut out
reads as the first two: the fourth names a record that is not there, and is dropped as `link`. The
checkpoint does not hold against that log (its last record is not where it says), so the world is the
replay of those two records.

```sh
cd books && rm -rf ../gap && cp -R . ../gap
read a b < <(obend log records | sed -n 's/^  record 3 ([a-z]*): bytes \([0-9]*\) to \([0-9]*\)$/\1 \2/p')
{ head -c "$a" .obend/log; tail -c +$((b + 1)) .obend/log; } > ../gap/.obend/log
cd ../gap && obend log
```

```text
log: 2 records, 1208 bytes, each following the one before it from the genesis sentinel
last record: 2 (open), bytes 821 to 1208
torn tail: 9757 bytes after record 2, dropped (link: it does not follow the record before it)
checkpoint: dropped (it does not hold against the log); the world is replayed from genesis
world cb112acfc0a27c4c: replayed from genesis
world cb112acfc0a27c4c: the checkpoint and the records after it
world cb112acfc0a27c4c: as record 2 commits to it
one world
```

A byte of the third record's turn changed in place reads as the first two as well, the third dropped
as `digest`. Here the checkpoint still holds (its last record is whole where it says, and commits to
its world): an open trusts it for the records before it, and `obend log`, which replays from genesis
as well, says the log no longer reaches it.

```sh refused
cd books && rm -rf ../gap && cp -R . ../gap
read a b < <(obend log records | sed -n 's/^  record 3 ([a-z]*): bytes \([0-9]*\) to \([0-9]*\)$/\1 \2/p')
python3 -c "import sys; p=sys.argv[1]; k=int(sys.argv[2]); d=bytearray(open(p,'rb').read()); d[k]^=1; open(p,'wb').write(d)" ../gap/.obend/log $((a + 150))
cd ../gap && obend log
```

```text
log: 2 records, 1208 bytes, each following the one before it from the genesis sentinel
last record: 2 (open), bytes 821 to 1208
torn tail: 10217 bytes after record 2, dropped (digest: its turn is not the one its receipt names)
checkpoint: the world after record 20
world cb112acfc0a27c4c: replayed from genesis
world 80c7ac454cdcf341: the checkpoint and the records after it
world cb112acfc0a27c4c: as record 2 commits to it
NOT ONE WORLD
```

## 6. The checkpoint is a cache

Without it, the world is replayed from genesis, and is the same world.

```sh
cd books && obend log | tail -4 && rm .obend/checkpoint && obend log | tail -4 && rm -rf ../gap
```

```text
world 80c7ac454cdcf341: replayed from genesis
world 80c7ac454cdcf341: the checkpoint and the records after it
world 80c7ac454cdcf341: as record 20 commits to it
one world
world 80c7ac454cdcf341: replayed from genesis
world 80c7ac454cdcf341: the checkpoint and the records after it
world 80c7ac454cdcf341: as record 20 commits to it
one world
```
