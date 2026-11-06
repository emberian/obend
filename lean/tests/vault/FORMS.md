# A screenshot is a form: a walkthrough

You take a screenshot of what you are looking at and send it to a friend; they cannot press any of
its buttons. The picture is dead. Here the capture stays live: it is a MEMBRANE, the part of your
vault a grant shows, at its state now, with the turn you were about to make still in it. Put
variables where some of its data was and it is a FORM. Your friend fills it in their own store,
offline, and sends back a PROPOSAL; your vault judges it as it judges any write, under the laws that
hold when it comes back, and refuses it by name or lands it as one turn with a receipt.

Every block below is run, in order, by `python3 tests/vault/walkthrough.py --doc tests/vault/FORMS.md`
(from `lean/`, after `lake build obend`), and what it prints is checked against the block after it.
`python3 tests/vault/forms_planted.py` builds the binary twice more with the membrane's checks taken
out, one at a time, and requires this walkthrough to fail both times.

## 1. Alice's vault

Alice keeps three accounts as pages, each with a `balance` in its frontmatter, and a private page
that is nobody else's business. `Accounts` lists the three, and its law over its links says no listed
account holds more than 100. `Budget` is the situation she is looking at: this month she means to pay
Carol 30.

```sh
mkdir -p alice/ledger alice/private && cd alice
printf -- '---\nbalance: 100\n---\n# Alice\n' > ledger/alice.md
printf -- '---\nbalance: 20\n---\n# Bob\n' > ledger/bob.md
printf -- '---\nbalance: 5\n---\n# Carol\n' > ledger/carol.md
printf -- '---\nbalance: 900\n---\n# Salary\n' > private/salary.md
printf -- '---\nlaw cap: linked.balance <= 100\n---\n# Accounts\n\n- [[ledger/alice]]\n- [[ledger/bob]]\n- [[ledger/carol]]\n' > Accounts.md
printf -- '# Budget\n\nThis month [[ledger/alice]] pays [[ledger/carol]] 30; [[ledger/bob]] waits; see [[private/salary]].\n' > Budget.md
obend open
```

```text
Accounts: new page (v1)
Budget: new page (v1)
ledger/alice: new page (v1)
ledger/bob: new page (v1)
ledger/carol: new page (v1)
private/salary: new page (v1)
```

## 2. The capture

Alice captures the situation for Bob, with a grant that reads and writes the pages under `ledger/`.
The capture is what that grant shows of `Budget` and every page it links to: the private page and
`Budget` itself are not shown, and they are not in the capture at all (not blanked, absent). The turn
she was about to make is in it, live: the form has no holes yet, so its residual is the turn itself.

```sh
cd alice && obend capture Budget pay --for bob --grant 'ledger/*' --move ledger/alice ledger/carol 30
```

```text
captured pay from Budget for bob: 3 page(s) shown, 2 not shown to bob
pay: a form for bob (read, write on ledger/*)
  ledger/alice: balance 100
  ledger/carol: balance 5
  ledger/bob: balance 20
  ledger/alice.balance := 70
  ledger/carol.balance := 35
```

## 3. Variables for data

The amount and the recipient become holes. The residual is the form evaluated as far as the capture
allows: Alice's balance is known, so her line is `100 - amount`; the recipient's balance is not known
until the recipient is, so it stays a read of the hole.

```sh
cd alice && obend abstract pay 30 amount && obend abstract pay ledger/carol to
```

```text
pay: 30 is now the hole amount
pay: a form for bob (read, write on ledger/*)
  ledger/alice: balance 100
  ledger/carol: balance 5
  ledger/bob: balance 20
  hole amount: a natural
  ledger/alice.balance := 100 - amount
  ledger/carol.balance := 5 + amount
pay: ledger/carol is now the hole to
pay: a form for bob (read, write on ledger/*)
  ledger/alice: balance 100
  ledger/carol: balance 5
  ledger/bob: balance 20
  hole amount: a natural
  hole to: a page
  ledger/alice.balance := 100 - amount
  to.balance := to.balance + amount
```

The form goes to Bob as a file. Nothing of the private page is in it.

```sh
cd alice && obend form pay --out ../pay.form >/dev/null && grep -c salary ../pay.form; grep -c '"page": "ledger/' ../pay.form
```

```text
0
4
```

## 4. Bob fills it, offline

Bob has his own store and no way to reach Alice's. Each fill substitutes into the residual and
evaluates what the capture allows; what it does not (a page the form did not capture) stays a read,
to be done where the form is judged. Bob tries a page he guesses exists:

```sh
mkdir -p bob && cd bob && obend fill ../pay.form amount=40 to=private/salary --out ../guess.json
```

```text
pay: filled by bob: amount = 40, to = private/salary
  ledger/alice.balance := 60
  private/salary.balance := private/salary.balance + 40
wrote ../guess.json
```

a payment to himself that would put him over the cap, one larger than Alice holds, and the one he
means:

```sh
cd bob && obend fill ../pay.form amount=90 to=ledger/bob --out ../over.json
obend fill ../pay.form amount=140 to=ledger/carol --out ../much.json
obend fill ../pay.form amount=96 to=ledger/carol --out ../low.json
obend fill ../pay.form amount=40 to=ledger/carol --out ../pay.json
ls .obend/forms/received .obend/forms/sent
```

```text
pay: filled by bob: amount = 90, to = ledger/bob
  ledger/alice.balance := 10
  ledger/bob.balance := 110
wrote ../over.json
pay: filled by bob: amount = 140, to = ledger/carol
  ledger/alice.balance := 100 - 140
  ledger/carol.balance := 145
wrote ../much.json
pay: filled by bob: amount = 96, to = ledger/carol
  ledger/alice.balance := 4
  ledger/carol.balance := 101
wrote ../low.json
pay: filled by bob: amount = 40, to = ledger/carol
  ledger/alice.balance := 60
  ledger/carol.balance := 45
wrote ../pay.json
.obend/forms/received:
pay.json

.obend/forms/sent:
pay.json
```

Bob hands the form on to Dave. A reshare that would give Dave more than Bob holds is refused; one
that lets Dave look and not write goes through, and Dave fills it anyway.

```sh refused
cd bob && obend reshare ../pay.form --for dave --grant 'ledger/*' --held read,write,grant --out ../dave.form
```

```text
pay: refused by the membrane: bob holds read, write; resharing read, write, grant to dave would amplify it
```

```sh
cd bob && obend reshare ../pay.form --for dave --grant 'ledger/*' --held read --out ../dave.form
mkdir -p ../dave && cd ../dave && obend fill ../dave.form amount=10 to=ledger/bob --out ../dave.json
```

```text
pay: reshared by bob to dave (read on ledger/*)
wrote ../dave.form
pay: filled by dave: amount = 10, to = ledger/bob
  ledger/alice.balance := 90
  ledger/bob.balance := 30
wrote ../dave.json
```

Anyone can write anything into a file they send back. Dave adds a hop to the chain that grants
himself the write Bob's reshare withheld:

```sh
python3 -c "
import json; p = json.load(open('dave.json'))
p['hops'].append({'holder': 'dave', 'held': ['read', 'write'], 'patterns': ['ledger/*']})
json.dump(p, open('forged.json', 'w'))"
```

```text
```

## 5. While Bob was away

Alice adds a law to `Accounts` after the form left: no listed account may fall to 4 or below.

```sh
cd alice && sed -i.bak 's/^law cap: linked.balance <= 100$/&\nlaw floor: not (linked.balance <= 4)/' Accounts.md && rm Accounts.md.bak && obend open
```

```text
Accounts: v2 written
```

## 6. The proposals come back

Each is judged against Alice's own copy of the form (the proposal names its digest), the membrane
first, then the form's resources, then the pins (the captured pages must be as captured), then each
page it writes as a write of that page under the laws as they stand now, laws over links included.

The guessed page is refused by the membrane before anything is read, in the words it would use
for a page that does not exist (`judgeProposal_gate_first`):

```sh refused
cd alice && obend judge ../guess.json
```

```text
pay: refused by the membrane: private/salary is not a page of this form (bob may name ledger/alice, ledger/carol, ledger/bob)
```

Dave's grant reads and does not write:

```sh refused
cd alice && obend judge ../dave.json
```

```text
pay: refused by the membrane: dave's grant does not let it write ledger/alice (it holds read)
```

The forged hop is a reshare from Dave's grant that would amplify it; the kernel reads the chain from
its own copy of the form, from the owner down:

```sh refused
cd alice && obend judge ../forged.json
```

```text
pay: refused by the membrane: dave holds read; resharing read, write to dave would amplify it
```

The payment to Bob is inside the membrane and inside Alice's balance, and `Accounts`' law over its
links refuses it at Bob's page:

```sh refused
cd alice && obend judge ../over.json
```

```text
pay: at ledger/bob: refused by Accounts: cap (a law over Accounts's links, of which ledger/bob is one): `linked.balance <= 100` does not hold; the line `balance: 100` would pass (the page has `balance: 110`)
```

The large one takes more than Alice holds: the amount was a hole, and the resources are discharged
at the fill.

```sh refused
cd alice && obend judge ../much.json
```

```text
pay: refused by the form's resources: ledger/alice holds balance 100; the fill moves 140
```

The one that would leave Alice at 4 is refused by the law she added after the form left:

```sh refused
cd alice && obend judge ../low.json
```

```text
pay: at ledger/alice: refused by Accounts: floor (a law over Accounts's links, of which ledger/alice is one): `not (linked.balance <= 4)` does not hold; the line `balance: 5` would pass (the page has `balance: 4`)
```

The one Bob meant lands as one turn: both pages written, the total moved conserved, a receipt linked
onto the chain.

```sh
cd alice && obend judge ../pay.json && cat ledger/alice.md ledger/carol.md && obend status ledger/carol
```

```text
pay: landed as one turn by bob, receipt e9f9ead2024462f9 (1 in the chain)
  ledger/alice: balance 100 → 60
  ledger/carol: balance 5 → 45
rendered ledger/alice.md
rendered ledger/carol.md
---
balance: 60
---
# Alice
---
balance: 45
---
# Carol
ledger/carol v2
```

## 7. A form reads the situation it captured

The capture pinned the pages it read. Now that Alice's page has moved, a second fill of the same form
is refused with what moved; Alice captures again to offer another.

```sh refused
cd bob && obend fill ../pay.form amount=10 to=ledger/bob --out ../again.json >/dev/null && cd ../alice && obend judge ../again.json
```

```text
pay: refused: stale: the form read ledger/alice as it was when captured (balance 100 → 60, bytes 29 → 28, version 0 → 1); capture it again
```
