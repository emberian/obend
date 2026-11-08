# A screenshot is a form: a walkthrough

You take a screenshot of what you are looking at and send it to a friend; they cannot press any of
its buttons. The picture is dead. Here the capture stays live: it is a MEMBRANE, the part of your
vault a grant shows, at its state now, with the turn you were about to make still in it. Put
variables where some of its data was and it is a FORM. Your friend fills it in their own store,
offline, and sends back a PROPOSAL; your vault judges it as it judges any write, under the laws that
hold when it comes back, and refuses it by name or lands it as one turn with a receipt.

Every block below is run, in order, by `python3 tests/vault/walkthrough.py --doc tests/vault/FORMS.md`
(from `lean/`, after `lake build obend`), and what it prints is checked against the block after it.
`python3 tests/vault/forms_planted.py` builds the binary three more times, with one of the membrane's
checks taken out, or with every judgment counted as checked at capture, and requires this walkthrough
to fail each time.

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

Every judgment a fill of the form will make (each page's own laws, and the laws over links of every
page linking to it: here `Accounts`' `cap`, at each page the fill may write) is a term of the
kernel's own language: the law applied to the page's state with the fields a write changes left as
declared holes (`PartialTyping.hole`: the moved `balance`, and the measures a write moves, such as
its bytes and its poster), and to the request, a hole too (who signs, the turn, the height). The
capture and each abstraction check every such term once, and the checks the checker accepts are part
of the vault's world: made by the turn that captured or abstracted the form, so made the same way by
every replay of its log. A judgment of a fill runs exactly such a term, filled with the values its
write holds there and with its request (`Obend.Vault.Form.judge_runs_checked`), and is typed by the
derivation that one check returned (`Obend.Vault.Form.kept_typed`, through
`Obend.Core.Proofs.FillTyping.fill_typed`); it is not checked again.

```sh
cd alice && obend checked pay
```

```text
pay: 3 law(s) over its holed states, checked once with amount open:
  Accounts: cap at ledger/alice
  Accounts: cap at ledger/carol
  Accounts: cap at ledger/bob
```

No file stands for a check. A vault that kept them in `.obend/checked/` (as this one once did) would
take a planted file for the checker's word; here a planted one is never read. The world keeps each
check's record, and a command that uses a form's checks makes them again from those records with the
checker (`Obend.Vault.Form.checksOf`; made again they are the capture's, `checksOf_records`):

```sh
cd alice && mkdir -p .obend/checked && echo '[]' > .obend/checked/pay.json && obend checked pay | head -1
```

```text
pay: 3 law(s) over its holed states, checked once with amount open:
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
wrote ../guess.json (intent d9a3610c01edc7ed)
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
wrote ../over.json (intent 222492e260d2c284)
pay: filled by bob: amount = 140, to = ledger/carol
  ledger/alice.balance := 100 - 140
  ledger/carol.balance := 145
wrote ../much.json (intent 3c2785c38617abea)
pay: filled by bob: amount = 96, to = ledger/carol
  ledger/alice.balance := 4
  ledger/carol.balance := 101
wrote ../low.json (intent 6451f3e1f803895c)
pay: filled by bob: amount = 40, to = ledger/carol
  ledger/alice.balance := 60
  ledger/carol.balance := 45
wrote ../pay.json (intent 10fdde8e5513805e)
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
wrote ../dave.json (intent 45e8764b022b95f9)
```

Before anything is judged, Alice can ask what a judgment of Bob's proposal would keep from the
capture and what it would check now (`obend checked FORM PROPOSAL` judges and lands nothing):

```sh
cd alice && obend checked pay ../pay.json
```

```text
work: laws over the holed states: 2 kept from the capture, 0 checked now, re-checked 0
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

The laws of `Accounts` changed, so the judgments the capture checked are not the ones a fill makes
now: a judgment of the same proposal checks them now, and keeps none.

```sh
cd alice && obend checked pay ../pay.json
```

```text
work: laws over the holed states: 0 kept from the capture, 4 checked now, re-checked 0
```

## 6. The proposals come back

Each is judged against Alice's own copy of the form (the proposal names its digest), the membrane
first, then the form's resources, then the pins (the captured pages must be as captured), then the
one turn over every page it writes: each page's write judged as any write of it is, under the laws as
they stand now, the laws over links read on the turn's tip (every page of the turn at its new state),
and all of it landed or none. Since the laws over the form's pages moved after it left, the first
judgment transports it first (`Obend.Vault.Transport`; `lean/tests/vault/TRANSPORT.md`): it promised
nothing, so it continues. Each judgment says the work it took (`work:`, explained there).

The guessed page is refused by the membrane before anything is read, in the words it would use
for a page that does not exist (`judgeProposal_gate_first`):

```sh refused
cd alice && obend judge ../guess.json
```

```text
pay: transported over the laws of ledger/alice, ledger/carol, ledger/bob: nothing was promised; it continues
work: performed 0, retained 1 of 1
pay: refused by the membrane: private/salary is not a page of this form (bob may name ledger/alice, ledger/carol, ledger/bob)
```

Dave's grant reads and does not write:

```sh refused
cd alice && obend judge ../dave.json
```

```text
work: performed 0, retained 1 of 1
pay: refused by the membrane: dave's grant does not let it write ledger/alice (it holds read)
```

The forged hop is a reshare from Dave's grant that would amplify it; the kernel reads the chain from
its own copy of the form, from the owner down:

```sh refused
cd alice && obend judge ../forged.json
```

```text
work: performed 0, retained 1 of 1
pay: refused by the membrane: dave holds read; resharing read, write to dave would amplify it
```

The payment to Bob is inside the membrane and inside Alice's balance, and `Accounts`' law over its
links refuses it at Bob's page:

```sh refused
cd alice && obend judge ../over.json
```

```text
work: performed 0, retained 1 of 1
pay: at ledger/bob: refused by Accounts: cap (a law over Accounts's links, of which ledger/bob is one): `linked.balance <= 100` does not hold; the line `balance: 100` would pass (the page has `balance: 110`)
```

The proposal is one turn: Alice's leg alone would have passed, and it did not land either.

```sh
cd alice && grep balance ledger/alice.md ledger/bob.md
```

```text
ledger/alice.md:balance: 100
ledger/bob.md:balance: 20
```

The large one takes more than Alice holds: the amount was a hole, and the resources are discharged
at the fill.

```sh refused
cd alice && obend judge ../much.json
```

```text
work: performed 0, retained 1 of 1
pay: refused by the form's resources: ledger/alice holds balance 100; the fill moves 140
```

The one that would leave Alice at 4 is refused by the law she added after the form left:

```sh refused
cd alice && obend judge ../low.json
```

```text
work: performed 0, retained 1 of 1
pay: at ledger/alice: refused by Accounts: floor (a law over Accounts's links, of which ledger/alice is one): `not (linked.balance <= 4)` does not hold; the line `balance: 5` would pass (the page has `balance: 4`)
```

The one Bob meant lands as one turn: both pages written at once, each judged by its laws and the
laws over links on the turn's tip, the total moved conserved, one receipt linked onto the chain. Of
the laws over the two pages it writes, `cap` at each was checked once at capture and is kept, its
fill typed by that check; `floor`, added after the form left, is checked here; nothing is checked
twice (the second `work:` line).

```sh
cd alice && obend judge ../pay.json && cat ledger/alice.md ledger/carol.md && obend status ledger/carol
```

```text
pay: landed as one turn over 2 pages by bob, receipt 2f06af57e712e4d3 (1 in the chain)
  ledger/alice: balance 100 → 60
  ledger/carol: balance 5 → 45
rendered ledger/alice.md
rendered ledger/carol.md
work: performed 1, retained 1 of 1
work: laws over the holed states: 0 kept from the capture, 4 checked now, re-checked 0
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

The capture read the values of the pages it captured. Now that Alice's and Carol's balances have
moved, a second fill of the same form is refused with the values that moved; Alice captures again to
offer another. (A page rewritten with the same values, a version later, is not a reason: its support
moved and its values did not.)

```sh refused
cd bob && obend fill ../pay.form amount=10 to=ledger/bob --out ../again.json >/dev/null && cd ../alice && obend judge ../again.json
```

```text
work: performed 0, retained 0 of 1
pay: refused: stale (value): the form read ledger/alice balance 100 → 60, ledger/carol balance 5 → 45; capture it again
```
