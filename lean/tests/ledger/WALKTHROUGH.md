# A ledger in a vault: a walkthrough

A small firm keeps its books as a folder of markdown, opened with `obend open` like any vault (see
`lean/tests/vault/WALKTHROUGH.md`). Three things make the folder a ledger:

- **a catalog**: accounts are pages, `accounts/Cash.md` and the like;
- **documents**: an invoice, a payment, a supplier's bill are pages, each of a kind whose `_kind.md`
  says, in lines a person reads, what posting it makes;
- **a register**: `register/_kind.md`, whose `law` lines every posting must keep.

Posting a document is a write to the register, judged by those laws, with a receipt anyone can
re-check. A wrong posting is never edited: it is reversed. A closed period stays closed. A copy of
the books on a laptop can post while offline; merging it back replays its postings through the
register here, all or nothing, and says by name what it refused. A report says which postings it
took, and an auditor recomputes it and checks that none of the period's was left out.

Every block below is run, in order, by `python3 tests/ledger/walkthrough.py` (from `lean/`, after
`lake build obend`), and what it prints is checked against the block after it.

## 1. The books

The chart of accounts, four kinds of document, and the register.

```sh
mkdir books && cd books && mkdir accounts invoices payments bills outlays register
printf -- '---\nlaw coded: not (new.code <= 999) and new.code <= 9999\ncode: 1000\n---\nAn account of the chart, with its four-digit code.\n' > accounts/_kind.md
for a in Cash:1000 Receivables:1100 Payables:2000 TaxPayable:2100 Revenue:4000 Supplies:5100; do
  printf -- '---\ncode: %s\n---\n# %s\n' "${a#*:}" "${a%%:*}" > "accounts/${a%%:*}.md"
done
cat > invoices/_kind.md <<'MD'
---
amount: 0
period: 0
---
An invoice: the customer owes us its amount. Posting it moves the amount:

- debit [[accounts/Receivables]] amount
- credit [[accounts/Revenue]] amount
MD
cat > payments/_kind.md <<'MD'
---
amount: 0
period: 0
---
A customer's payment: cash comes in, the customer owes less.

- debit [[accounts/Cash]] amount
- credit [[accounts/Receivables]] amount
MD
cat > bills/_kind.md <<'MD'
---
amount: 0
net: 0
tax: 0
period: 0
---
A supplier's bill: supplies bought, the supplier to be paid.

- debit [[accounts/Supplies]] amount
- credit [[accounts/Payables]] net
MD
cat > outlays/_kind.md <<'MD'
---
amount: 0
period: 0
---
We pay a supplier: cash goes out, we owe less.

- debit [[accounts/Payables]] amount
- credit [[accounts/Cash]] amount
MD
cat > register/_kind.md <<'MD'
---
law balanced: new.debits == new.credits
law solvent: new.Cash_credits <= new.Cash_debits
law sealed: new.version == 0 or new.movements == 0
---
The register. Every posting balances; cash never goes out beyond what came in; a posting is
written once, and corrected by a reversing posting.
MD
obend open && obend ledger status
```

```text
accounts/Cash: new page (v1)
accounts/Payables: new page (v1)
accounts/Receivables: new page (v1)
accounts/Revenue: new page (v1)
accounts/Supplies: new page (v1)
accounts/TaxPayable: new page (v1)
accounts/_kind: new page (v1)
bills/_kind: new page (v1)
invoices/_kind: new page (v1)
outlays/_kind: new page (v1)
payments/_kind: new page (v1)
register/_kind: new page (v1)
register: 0 posting(s), closed through period 0
balances (every period):
  account                    debit  credit
  total                          0       0
```

## 2. Posting

An invoice for 500 in period 11, posted. Its kind's template makes the posting; the register's laws
judge it; the register numbers it.

```sh
cd books
printf -- '---\nkind: invoices\namount: 500\nperiod: 11\n---\nAcme Ltd, consulting in November.\n' > invoices/INV-1.md
obend open && obend ledger post invoices/INV-1 && cat register/P-0001.md
```

```text
invoices/INV-1: new page (v1)
invoices/INV-1: posted as P-0001 (period 11): debit accounts/Receivables 500, credit accounts/Revenue 500
receipt .obend/receipts/P-0001.json
---
period: 11
debits: 500
credits: 500
movements: 2
Receivables_debits: 500
Receivables_credits: 0
Revenue_debits: 0
Revenue_credits: 500
---
# P-0001

Posts invoices/INV-1 in period 11:

![[invoices/INV-1]]

- debit [[accounts/Receivables]] 500
- credit [[accounts/Revenue]] 500
```

The receipt is the posting's row of the register, with the register before it and the law it was
judged by. Anyone can re-judge it without the books:

```sh
cd books && obend verify .obend/receipts/P-0001.json
```

```text
P-0001: invoices/INV-1 in period 11, admitted at closed-through 0 over 0 posting(s): debit accounts/Receivables 500, credit accounts/Revenue 500
verified (posting@1: the row re-judged under the register's law it carries)
```

Acme pays 300 of it.

```sh
cd books
printf -- '---\nkind: payments\namount: 300\nperiod: 11\n---\nAcme Ltd, part payment.\n' > payments/PAY-1.md
obend open && obend ledger post payments/PAY-1
```

```text
payments/PAY-1: new page (v1)
payments/PAY-1: posted as P-0002 (period 11): debit accounts/Cash 300, credit accounts/Receivables 300
receipt .obend/receipts/P-0002.json
```

## 3. A refusal names its clause

A supplier's bill: 120 in all, 100 for the goods and 20 of tax. The bills kind's template debits the
whole amount and credits only the net, so the posting does not balance, and the register says which
law refused it and what would pass.

```sh refused
cd books
printf -- '---\nkind: bills\namount: 120\nnet: 100\ntax: 20\nperiod: 11\n---\nPaper and toner.\n' > bills/B-1.md
obend open && obend ledger post bills/B-1
```

```text
bills/B-1: new page (v1)
bills/B-1: refused by register/_kind: balanced (the kind of register/, an ancestor of register/P-0003): `new.debits == new.credits` does not hold; debits = 100 would pass (this write has debits = 120)
```

The template is wrong, not the bill: the tax is owed too. Add its line to the kind, and post again.

```sh
cd books
printf -- '- credit [[accounts/TaxPayable]] tax\n' >> bills/_kind.md
obend open && obend ledger post bills/B-1
```

```text
bills/_kind: v2 written
bills/B-1: posted as P-0003 (period 11): debit accounts/Supplies 120, credit accounts/Payables 100, credit accounts/TaxPayable 20
receipt .obend/receipts/P-0003.json
```

## 4. Posted once, and corrected by reversal

A document is posted once. Posting it again is refused, naming the posting it already has:

```sh refused
cd books && obend ledger post invoices/INV-1
```

```text
invoices/INV-1: refused (posted-once): invoices/INV-1 is posted already, as P-0001; correct it with a reversing posting first: obend ledger reverse P-0001
```

The invoice was wrong: it should have been 550. Editing it is an ordinary write; the posting that
embeds it is now behind, by name:

```sh
cd books && sed -i.bak 's/^amount: 500/amount: 550/' invoices/INV-1.md && rm invoices/INV-1.md.bak && obend open
```

```text
invoices/INV-1: v2 written
rendered register/P-0001.md
register/P-0001: ![[invoices/INV-1]] (embed) is behind: invoices/INV-1 moved on (v1 → v2) and the bytes it quotes changed
```

A posting is not edited. The register's `sealed` law refuses a change to a posting's page (the file
keeps what was typed; the world does not take it):

```sh
cd books && sed -i.bak 's/^- debit \[\[accounts\/Receivables\]\] 500/- debit [[accounts\/Receivables]] 550/' register/P-0001.md && rm register/P-0001.md.bak
obend open
sed -i.bak 's/^- debit \[\[accounts\/Receivables\]\] 550/- debit [[accounts\/Receivables]] 500/' register/P-0001.md && rm register/P-0001.md.bak
obend open
```

```text
register/P-0001: ![[invoices/INV-1]] (embed) is behind: invoices/INV-1 moved on (v1 → v2) and the bytes it quotes changed
nothing changed
register/P-0001: ![[invoices/INV-1]] (embed) is behind: invoices/INV-1 moved on (v1 → v2) and the bytes it quotes changed
register/P-0001: refused by register/_kind: sealed (the kind of register/, an ancestor of register/P-0001): `new.version == 0 or new.movements == 0` does not hold; version = 0 would pass (this write has version = 1)
```

The correction is a reversing posting, then the document posted again:

```sh
cd books && obend ledger reverse P-0001 && obend ledger post invoices/INV-1 && obend ledger status
```

```text
reversal of P-0001: posted as P-0004 (period 11): credit accounts/Receivables 500, debit accounts/Revenue 500
receipt .obend/receipts/P-0004.json
invoices/INV-1: posted as P-0005 (period 11): debit accounts/Receivables 550, credit accounts/Revenue 550
receipt .obend/receipts/P-0005.json
register: 5 posting(s), closed through period 0
  number  document              period     amount
  P-0001  invoices/INV-1        period 11     500  reversed by P-0004
  P-0002  payments/PAY-1        period 11     300  live
  P-0003  bills/B-1             period 11     120  live
  P-0004  invoices/INV-1        period 11     500  reverses P-0001
  P-0005  invoices/INV-1        period 11     550  live
balances (every period):
  account                    debit  credit
  accounts/Cash                300       0
  accounts/Payables              0     100
  accounts/Receivables        1050     800
  accounts/Revenue             500    1050
  accounts/Supplies            120       0
  accounts/TaxPayable            0      20
  total                       1970    1970
```

## 5. Closing a period

Period 11 is closed. Nothing more is posted into it, and closing never goes back.

```sh
cd books && obend ledger close 11 && obend ledger close 10
```

```text
closed through period 11: no posting into period 11 or before
the register is closed through period 11 already; closing never goes back
```

```sh refused
cd books
printf -- '---\nkind: payments\namount: 250\nperiod: 11\n---\nAcme Ltd, the rest, late.\n' > payments/PAY-2.md
obend open && obend ledger post payments/PAY-2
```

```text
payments/PAY-2: new page (v1)
register/P-0001: ![[invoices/INV-1]] (embed) is behind: invoices/INV-1 moved on (v1 → v2) and the bytes it quotes changed
payments/PAY-2: refused (closed-period): period 11 is closed (the register is closed through 11); post it into an open period: --period 12
```

```sh
cd books && obend ledger post payments/PAY-2 --period 12
```

```text
payments/PAY-2: posted as P-0006 (period 12): debit accounts/Cash 250, credit accounts/Receivables 250
receipt .obend/receipts/P-0006.json
```

## 6. Offline

The books are copied to a laptop. While it is away, the laptop takes a payment of 100, pays a
supplier 400, and invoices Bolt & Co for 70. Here, meanwhile, a supplier is paid 300, and the same
invoice to Bolt is written and posted.

```sh
cp -R books laptop
cd laptop
printf -- '---\nkind: payments\namount: 100\nperiod: 12\n---\nAcme Ltd, an advance.\n' > payments/PAY-3.md
printf -- '---\nkind: outlays\namount: 400\nperiod: 12\n---\nPaper Co, on account.\n' > outlays/OUT-1.md
printf -- '---\nkind: invoices\namount: 70\nperiod: 12\n---\nBolt & Co, a repair.\n' > invoices/INV-2.md
obend open && obend ledger post payments/PAY-3 && obend ledger post outlays/OUT-1 && obend ledger post invoices/INV-2
```

```text
invoices/INV-2: new page (v1)
outlays/OUT-1: new page (v1)
payments/PAY-3: new page (v1)
register/P-0001: ![[invoices/INV-1]] (embed) is behind: invoices/INV-1 moved on (v1 → v2) and the bytes it quotes changed
payments/PAY-3: posted as P-0007 (period 12): debit accounts/Cash 100, credit accounts/Receivables 100
receipt .obend/receipts/P-0007.json
outlays/OUT-1: posted as P-0008 (period 12): debit accounts/Payables 400, credit accounts/Cash 400
receipt .obend/receipts/P-0008.json
invoices/INV-2: posted as P-0009 (period 12): debit accounts/Receivables 70, credit accounts/Revenue 70
receipt .obend/receipts/P-0009.json
```

```sh
cd books
printf -- '---\nkind: outlays\namount: 300\nperiod: 12\n---\nToner Ltd.\n' > outlays/OUT-2.md
printf -- '---\nkind: invoices\namount: 70\nperiod: 12\n---\nBolt & Co, a repair.\n' > invoices/INV-2.md
obend open && obend ledger post outlays/OUT-2 && obend ledger post invoices/INV-2
```

```text
invoices/INV-2: new page (v1)
outlays/OUT-2: new page (v1)
register/P-0001: ![[invoices/INV-1]] (embed) is behind: invoices/INV-1 moved on (v1 → v2) and the bytes it quotes changed
outlays/OUT-2: posted as P-0007 (period 12): debit accounts/Payables 300, credit accounts/Cash 300
receipt .obend/receipts/P-0007.json
invoices/INV-2: posted as P-0008 (period 12): debit accounts/Receivables 70, credit accounts/Revenue 70
receipt .obend/receipts/P-0008.json
```

Back home, merge the laptop. The documents merge as pages do. The laptop's postings are replayed,
in order, through this register: each laptop posting is judged by this register's laws at this
register's state. Two are refused: paying 400 now would send more cash out than came in (each side's
cash was fine alone), and Bolt's invoice is posted here already. The stitch is all or nothing, so
the register takes none of the laptop's postings.

```sh refused
cd books && obend merge ../laptop
```

```text
outlays/OUT-1: imported from laptop
payments/PAY-3: imported from laptop
rendered outlays/OUT-1.md
rendered payments/PAY-3.md
register: not stitched; 2 of laptop's 3 new row(s) refused, so none is taken
  laptop's P-0008 (posting of outlays/OUT-1 in period 12): refused by register/_kind: solvent (the kind of register/, an ancestor of register/P-0010): `new.Cash_credits <= new.Cash_debits` does not hold; Cash_credits = 650 would pass (this write has Cash_credits = 700)
  laptop's P-0009 (posting of invoices/INV-2 in period 12): refused (posted-once): invoices/INV-2 is posted already, as P-0008; correct it with a reversing posting first: obend ledger reverse P-0008
to stitch the rest without a row: obend merge ../laptop --drop P-NNNN
```

The owner decides. The laptop's invoice to Bolt is the same as this one: leave it out. The laptop's
outlay cannot be paid in full: leave its posting out too, and post the outlay here for what the cash
allows. The laptop's payment comes in.

```sh
cd books && obend merge ../laptop --drop P-0008 --drop P-0009
```

```text
dropped by the owner: laptop's P-0008
dropped by the owner: laptop's P-0009
register: laptop's P-0007 (posting of payments/PAY-3 in period 12) is P-0009 here
register: stitched 1 row(s) from laptop
```

```sh
cd books && sed -i.bak 's/^amount: 400/amount: 350/' outlays/OUT-1.md && rm outlays/OUT-1.md.bak
obend open && obend ledger post outlays/OUT-1 && obend ledger status
```

```text
outlays/OUT-1: v2 written
register/P-0001: ![[invoices/INV-1]] (embed) is behind: invoices/INV-1 moved on (v1 → v2) and the bytes it quotes changed
outlays/OUT-1: posted as P-0010 (period 12): debit accounts/Payables 350, credit accounts/Cash 350
receipt .obend/receipts/P-0010.json
register: 10 posting(s), closed through period 11
  number  document              period     amount
  P-0001  invoices/INV-1        period 11     500  reversed by P-0004
  P-0002  payments/PAY-1        period 11     300  live
  P-0003  bills/B-1             period 11     120  live
  P-0004  invoices/INV-1        period 11     500  reverses P-0001
  P-0005  invoices/INV-1        period 11     550  live
  P-0006  payments/PAY-2        period 12     250  live
  P-0007  outlays/OUT-2         period 12     300  live
  P-0008  invoices/INV-2        period 12      70  live
  P-0009  payments/PAY-3        period 12     100  live
  P-0010  outlays/OUT-1         period 12     350  live
balances (every period):
  account                    debit  credit
  accounts/Cash                650     650
  accounts/Payables            650     100
  accounts/Receivables        1120    1150
  accounts/Revenue             500    1120
  accounts/Supplies            120       0
  accounts/TaxPayable            0      20
  total                       3040    3040
```

## 7. The trial balance, and the auditor

The trial balance of period 12: every posting of the period, added up by account. It is checked by
the `trial-balance@1` judge before it is printed, written as a page that links every posting it
took, and given to the auditor as a receipt.

```sh
cd books && obend report trial-balance 12 --out ../tb-12.json && cat reports/TB-12.md
```

```text
trial balance, period 12 (register root 58832c8412c3…, 10 posting(s) in the register)
  account                    debit  credit
  accounts/Cash                350     650
  accounts/Payables            650       0
  accounts/Receivables          70     350
  accounts/Revenue               0      70
  total                       1070    1070
postings: P-0006, P-0007, P-0008, P-0009, P-0010
checked (trial-balance@1, decidable, compiled): every posting of period 12 is in it
wrote reports/TB-12.md
wrote ../tb-12.json
---
period: 12
---
# Trial balance, period 12

| account | debit | credit |
|---|---|---|
| accounts/Cash | 350 | 650 |
| accounts/Payables | 650 | 0 |
| accounts/Receivables | 70 | 350 |
| accounts/Revenue | 0 | 70 |
| total | 1070 | 1070 |

Postings: [[register/P-0006]], [[register/P-0007]], [[register/P-0008]], [[register/P-0009]], [[register/P-0010]]
```

The auditor holds the register's root (from the books, or from the last posting receipt) and the
report. Re-checking needs nothing else: the postings in the report's book must have that root, the
report must take every posting of period 12 among them and no other, and its totals must be theirs.

```sh
cd books && obend verify ../tb-12.json --root "$(obend ledger root)"
```

```text
  account                    debit  credit
  accounts/Cash                350     650
  accounts/Payables            650       0
  accounts/Receivables          70     350
  accounts/Revenue               0      70
  total                       1070    1070
verified (trial-balance@1, decidable, compiled): the 5 posting(s) of period 12 among the register's 10, none left out; the register is the one whose root was given
```

A report that leaves a posting out is refused, naming it:

```sh refused
python3 - <<'PY'
import json
r = json.load(open("tb-12.json"))
r["certificate"]["postings"] = [k for k in r["certificate"]["postings"] if k != "P-0007"]
json.dump(r, open("tb-12-short.json", "w"))
PY
cd books && obend verify ../tb-12-short.json --root "$(obend ledger root)"
```

```text
refused (omitted): P-0007 is a posting of the period and is not in the report
```

And a posting receipt from the stitch re-checks like any other:

```sh
cd books && obend verify .obend/receipts/P-0009.json
```

```text
P-0009: payments/PAY-3 in period 12, admitted at closed-through 11 over 8 posting(s): debit accounts/Cash 100, credit accounts/Receivables 100
verified (posting@1: the row re-judged under the register's law it carries)
```

The closed period's trial balance takes the first posting of the invoice, its reversal and the
corrected posting: the invoice counts once, at 550.

```sh
cd books && obend report trial-balance 11
```

```text
trial balance, period 11 (register root 58832c8412c3…, 10 posting(s) in the register)
  account                    debit  credit
  accounts/Cash                300       0
  accounts/Payables              0     100
  accounts/Receivables        1050     800
  accounts/Revenue             500    1050
  accounts/Supplies            120       0
  accounts/TaxPayable            0      20
  total                       1970    1970
postings: P-0001, P-0002, P-0003, P-0004, P-0005
checked (trial-balance@1, decidable, compiled): every posting of period 11 is in it
wrote reports/TB-11.md
```

## 8. What a posting touches

If a posting of period 11 were taken away, what would notice? The trial balance of period 11 links
it, and its own page's law row reads it:

```sh
cd books && obend analyze impact register/P-0002@retired --world .
```

```text
impact of register/P-0002: v1 -> retired (vault .)
behind      cite      reports/TB-11: [[register/P-0002]]
            rests on: present register/P-0002 = false at register/P-0002@retired
rejudge     law       law of register/P-0002
            rests on: version of register/P-0002 (v1) = false at register/P-0002@retired
2 affected of 2 dependents reading register/P-0002 (82 indexed)
checked (impact@1, decidable, compiled)
```
