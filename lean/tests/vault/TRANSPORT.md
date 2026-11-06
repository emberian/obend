# A form out in the world, carried across changes: a walkthrough

A form leaves the vault that issued it and lives on in another store, offline, while the vault goes
on changing. Some changes leave it as it was; some leave it as it was for one reader and not for
another; some need it repaired; some must refuse it. `Obend.Vault.Transport` says which, as a
relation between a context, a residual, a published history and the obligations still outstanding:
the form is the residual (C), the log is the history (H), the tip of the store is the context (Γ'),
and the proposals sent and not yet confirmed are the obligations (O).

The experiment is one live object with two supports (a form for Bob, under two grants), one remote
observer (Bob's store, which received it), an editable implementation (a page's law), and one
external operation (Bob's fill landing on Alice's store). Seven perturbations follow. Each prints a
survival or a refusal by name, and the work it took: `work: performed P, retained R of T`, where T is
what the form carries (each move of its residual, each value its contract offers), P is what the step
judged anew, and R is what is still good without being redone. A stable form that redid everything
would show P = T; nothing here does.

Every block below is run, in order, by `python3 tests/vault/walkthrough.py --doc tests/vault/TRANSPORT.md`
(from `lean/`, after `lake build obend`), and what it prints is checked against the block after it.

## The live object

Alice keeps three accounts; `Accounts` caps every account it lists at 100. She captures the payment
she means to make to Carol as a form for Bob, makes its amount a hole, and declares its continuity
contract: it OFFERS any amount from 1 to 60 (each one judged now by the laws as they stand) and
PROMISES 1 to 40, whatever becomes of the laws while it is out. The capture's own grant is the form's
first support (`pay`); she issues Bob a second one (`g2`).

```sh
mkdir -p alice/ledger && cd alice
printf -- '---\nbalance: 100\n---\n# Alice\n' > ledger/alice.md
printf -- '---\nbalance: 20\n---\n# Bob\n' > ledger/bob.md
printf -- '---\nbalance: 5\n---\n# Carol\n' > ledger/carol.md
printf -- '---\nlaw cap: linked.balance <= 100\n---\n# Accounts\n\n- [[ledger/alice]]\n- [[ledger/bob]]\n- [[ledger/carol]]\n' > Accounts.md
printf -- '# Budget\n\nThis month [[ledger/alice]] pays [[ledger/carol]] 30.\n' > Budget.md
obend open > /dev/null
obend capture Budget pay --for bob --grant 'ledger/*' --move ledger/alice ledger/carol 30 | head -1
obend abstract pay 30 amount > /dev/null
obend offer pay amount 1..60 --promise 1..40
obend grant g2 --for bob --grant ledger/alice --grant ledger/carol
obend form pay --out ../pay.form | tail -4
```

```text
captured pay from Budget for bob: 2 page(s) shown, 1 not shown to bob
pay: offers amount = 1..60, promises 1..40 (each value judged by the laws as they stand: 60 admitted)
granted g2 to bob (read, write on ledger/alice, ledger/carol)
  ledger/alice.balance := 100 - amount
  ledger/carol.balance := 5 + amount
  offer amount: 1..60 (promised 1..40)
wrote ../pay.form
```

Bob fills it twice in his own store. Each fill is a proposal with the identity of its intent, and each
stays outstanding in his store until a receipt for it comes back. A value outside the offer is
refused where it is filled.

```sh
mkdir bob && cd bob
obend fill ../pay.form amount=30 --out ../pay.json
obend fill ../pay.form amount=20 --out ../pay-b.json | tail -1
obend obligations
```

```text
pay: filled by bob: amount = 30
  ledger/alice.balance := 70
  ledger/carol.balance := 35
wrote ../pay.json (intent 7fdbb45ffae7ef38)
wrote ../pay-b.json (intent 275ecb5241f29055)
pay: intent 7fdbb45ffae7ef38 (amount = 30) sent to alice, awaiting its receipt
pay: intent 275ecb5241f29055 (amount = 20) sent to alice, awaiting its receipt
```

```sh refused
cd bob && obend fill ../pay.form amount=70 --out ../no.json
```

```text
pay: refused: amount = 70 is outside its offer (1..60)
```

Alice takes a copy of her vault away on a laptop: an old branch, for later. `obend transport` says
what the form is now for each of its readers: a display, which shows it, and an effect, which lands
its fill.

```sh
cp -R alice laptop && cd alice && obend transport pay
```

```text
pay: display: as it was
pay: authority: pay (read, write on ledger/*), g2 (read, write on ledger/alice, ledger/carol) stand
pay: effect: as it was
work: performed 0, retained 61 of 61
```

## 1. A support disappears

Alice revokes the capture's grant. `g2` still lets Bob write both pages, so no one looking sees the
authority absent (`handoff_no_absence`): the form stands for both readers, and nothing is redone.

```sh
cd alice && obend revoke pay && obend transport pay
```

```text
revoked pay
pay: display: as it was
pay: authority: g2 (read, write on ledger/alice, ledger/carol) stands; pay revoked
pay: effect: as it was
work: performed 0, retained 61 of 61
```

## 2. The payload is equal and the authority changes

Alice replaces `g2` with a grant that lets Bob read the pages and not write them. Every value the
form read is as captured: for a display it is as it was; for an effect it is stale, by authority,
and the proposal is refused naming it. Nothing of the residual or the offer is lost: when Alice
grants Bob writing again, the form is an effect again, with nothing redone.

```sh
cd alice && obend revoke g2 && obend grant g2r --for bob --grant ledger/alice --grant ledger/carol --held read
obend transport pay
```

```text
revoked g2
granted g2r to bob (read on ledger/alice, ledger/carol)
pay: display: as it was
pay: authority: g2r (read on ledger/alice, ledger/carol) stands; pay, g2 revoked
pay: effect: stale (authority: no grant that stands lets bob write ledger/alice, ledger/carol)
work: performed 0, retained 61 of 61
```

```sh refused
cd alice && obend judge ../pay.json
```

```text
pay: refused: stale (authority): no grant that stands lets bob write ledger/alice, ledger/carol (g2r (read on ledger/alice, ledger/carol) stands; pay, g2 revoked)
work: performed 0, retained 61 of 61
```

```sh
cd alice && obend grant g3 --for bob --grant 'ledger/*' && obend transport pay | tail -2
```

```text
granted g3 to bob (read, write on ledger/*)
pay: effect: as it was
work: performed 0, retained 61 of 61
```

## 3. The code changes while the form is suspended

Alice gives her own page a law while Bob holds the form. The page's support moves (a version later;
the balance the form read is as captured), and the laws a write of it is judged by are not those the
form was issued under, so the form is TRANSPORTED (`transport_sound`): every offered amount is
judged under the new laws, by the form as it went out, which judges as a fresh capture would
(`admitsAt_recapture`). A floor of 5 admits every amount offered: the form continues.

```sh
cd alice && printf -- '---\nbalance: 100\nlaw floor: not (new.balance <= 4)\n---\n# Alice\n' > ledger/alice.md
obend open && obend transport pay
```

```text
ledger/alice: v2 written
pay: display: as it was
pay: support moved under ledger/alice (bytes 29 → 63, version 0 → 1); the values it read are as captured
pay: authority: g2r (read on ledger/alice, ledger/carol), g3 (read, write on ledger/*) stand; pay, g2 revoked
pay: transported over the laws of ledger/alice: they admit every value it offers (1..60); it continues
pay: effect: as transported
work: performed 60, retained 61 of 61
```

A floor of 50 admits 1 to 50 of the 60 offered, and every promised amount among them: the offer
narrows, the residual is kept, and nothing is recaptured.

```sh
cd alice && sed -i.bak 's/<= 4)/<= 49)/' ledger/alice.md && rm ledger/alice.md.bak && obend open && obend transport pay
```

```text
ledger/alice: v3 written
pay: display: as it was
pay: support moved under ledger/alice (bytes 29 → 64, version 0 → 2); the values it read are as captured
pay: authority: g2r (read on ledger/alice, ledger/carol), g3 (read, write on ledger/*) stand; pay, g2 revoked
pay: transported over the laws of ledger/alice: they admit amount = 1..50 of 1..60; the offer narrows to them, the residual kept
pay: effect: as transported
work: performed 60, retained 51 of 61
```

A floor of 70 would take 31 to 40 out of what Bob was promised: the contract refuses the change, and
the form stays as it was transported last.

```sh refused
cd alice && sed -i.bak 's/<= 49)/<= 69)/' ledger/alice.md && rm ledger/alice.md.bak && obend open && obend transport pay
```

```text
ledger/alice: v4 written
pay: display: as it was
pay: support moved under ledger/alice (bytes 29 → 64, version 0 → 3); the values it read are as captured
pay: authority: g2r (read on ledger/alice, ledger/carol), g3 (read, write on ledger/*) stand; pay, g2 revoked
pay: effect: stale (the laws over ledger/alice moved); refused by its contract: the laws over ledger/alice no longer admit amount = 31, which it promised (1..40)
work: performed 50, retained 0 of 51
```

Alice puts the floor back at 50. The laws are again those the form was last transported under: there
is nothing to judge again.

```sh
cd alice && sed -i.bak 's/<= 69)/<= 49)/' ledger/alice.md && rm ledger/alice.md.bak && obend open && obend transport pay
```

```text
ledger/alice: v5 written
pay: display: as it was
pay: support moved under ledger/alice (bytes 29 → 64, version 0 → 4); the values it read are as captured
pay: authority: g2r (read on ledger/alice, ledger/carol), g3 (read, write on ledger/*) stand; pay, g2 revoked
pay: effect: as it was
work: performed 0, retained 51 of 51
```

## 4. A referenced page comes back late

Carol's file goes away; the store keeps her page's history as a tomb. A page that may come back is
not a page known to be gone: the form WAITS, for a display and for an effect, and Bob's proposal is
neither landed nor refused for good.

```sh
cd alice && mv ledger/carol.md ../carol.md && obend open && obend transport pay
```

```text
ledger/carol: deleted (its file is gone; v1 kept; a file ledger/carol.md revives it)
Accounts: [[ledger/carol]] (link) is missing: ledger/carol has no version
Budget: [[ledger/carol]] (link) is missing: ledger/carol has no version
pay: display: waits (ledger/carol is not here now: its file is gone, its history kept)
pay: support moved under ledger/alice (bytes 29 → 64, version 0 → 4); the values it read are as captured
pay: authority: g2r (read on ledger/alice, ledger/carol), g3 (read, write on ledger/*) stand; pay, g2 revoked
pay: effect: waits
work: performed 0, retained 51 of 51
```

```sh refused
cd alice && obend judge ../pay.json --receipt ../pay.receipt
```

```text
pay: waits: ledger/carol is not here now: its file is gone, its history kept; nothing landed, and the proposal may be judged again when it returns
work: performed 0, retained 51 of 51
```

The file comes back. The same proposal, judged again, lands, with its receipt written for Bob.

```sh
cd alice && mv ../carol.md ledger/carol.md && obend open && obend judge ../pay.json --receipt ../pay.receipt
```

```text
ledger/carol: revived (v1)
pay: landed as one turn over 2 pages by bob, receipt 635fbfd1d6318377 (1 in the chain)
  ledger/alice: balance 100 → 70
  ledger/carol: balance 5 → 35
rendered ledger/alice.md
rendered ledger/carol.md
wrote ../pay.receipt
work: performed 1, retained 51 of 51
```

## 5. A revision after a published item

The receipt is published: it is in Alice's chain and written for Bob. Alice then revises Carol's page
by hand, the balance the receipt reported included. The revision is a later turn; it changes the
form's values (the display and the effect both see them moved), and it retracts nothing published:
Bob confirms the receipt against the proposal he sent, after the revision, and his obligation is
discharged.

```sh
cd alice && printf -- '---\nbalance: 36\n---\n# Carol\n\nCarol keeps the till.\n' > ledger/carol.md && obend open && obend transport pay
```

```text
ledger/carol: v3 written
pay: display: stale (value: ledger/alice balance 100 → 70, ledger/carol balance 5 → 36)
pay: authority: g2r (read on ledger/alice, ledger/carol), g3 (read, write on ledger/*) stand; pay, g2 revoked
pay: effect: stale (value)
work: performed 0, retained 0 of 51
```

```sh
cd bob && obend confirm ../pay.receipt && obend obligations
```

```text
confirmed intent 7fdbb45ffae7ef38: its receipt names the proposal sent from here; 1 outstanding
pay: intent 275ecb5241f29055 (amount = 20) sent to alice, awaiting its receipt
```

## 6. A lost confirmation

Alice issues a second form; Bob fills it. Alice's judge is stopped (by its PID, at the write barrier
the store exposes to tests, `OBEND_TEST_TEAR=N:all:PATH`) after the judgment's record is in the log
and before anything else: the proposal has landed, and its receipt never reaches Bob.

```sh
cd alice && obend capture Budget pay2 --for bob --grant 'ledger/*' --move ledger/alice ledger/carol 10 | head -1
obend abstract pay2 10 amount > /dev/null && obend form pay2 --out ../pay2.form > /dev/null
cd ../bob && obend fill ../pay2.form amount=10 --out ../pay2.json | tail -1
```

```text
captured pay2 from Budget for bob: 2 page(s) shown, 1 not shown to bob
wrote ../pay2.json (intent ece6c6ffe02a8294)
```

```sh
cd alice
n=$(obend log | sed -n 's/^log: \([0-9]*\) records.*/\1/p')
OBEND_TEST_TEAR=$((n + 2)):all:$PWD/../barrier nohup obend judge ../pay2.json --receipt ../pay2.receipt > ../judge.out 2>&1 &
echo $! > ../obend.pid
for i in $(seq 200); do [ -e ../barrier ] && break; sleep 0.05; done
kill "$(cat ../obend.pid)"; wait "$(cat ../obend.pid)" 2>/dev/null; rm ../barrier ../obend.pid ../judge.out
[ -e ../pay2.receipt ] || echo "no receipt reached bob"
cd ../bob && obend obligations
```

```text
no receipt reached bob
pay: intent 275ecb5241f29055 (amount = 20) sent to alice, awaiting its receipt
pay2: intent ece6c6ffe02a8294 (amount = 10) sent to alice, awaiting its receipt
```

The crash kept what was sent and what landed (`obligations_survive_crash`). Bob sends the same
proposal again. Its intent has landed: it is refused as a duplicate (`judge_refuses_duplicate`), it
does not land twice, and its receipt is written again. Bob confirms it.

```sh refused
cd alice && obend judge ../pay2.json --receipt ../pay2.receipt
```

```text
recovered: record 41 (judge) was whole and its files were not: wrote ledger/alice.md, ledger/carol.md
pay2: refused: a duplicate: intent ece6c6ffe02a8294 has landed here as receipt b1a06d2196b16752 (2 in the chain); it is not landed again
wrote ../pay2.receipt
work: performed 0, retained 1 of 1
```

```sh
cd bob && obend confirm ../pay2.receipt && obend fill ../pay2.form amount=10 --out ../pay2-again.json | tail -1
```

```text
confirmed intent ece6c6ffe02a8294: its receipt names the proposal sent from here; 1 outstanding
wrote ../pay2-again.json (intent 6e089f3fb703b6a2)
```

A second proposal alike in content is another intent: it is judged on what it says
(`judge_by_identity`), not taken for the first, and the form it fills has moved.

```sh refused
cd alice && obend judge ../pay2-again.json
```

```text
pay2: refused: stale (value): the form read ledger/alice balance 70 → 60, ledger/carol balance 36 → 46; capture it again
work: performed 0, retained 0 of 1
```

## 7. An old branch rejoins after a revocation

On the laptop, copied before any of this, both of the form's first supports still stand. There Alice
writes a note and lands Bob's other proposal.

```sh
cd laptop && printf -- '# Notes\n\nWritten on the laptop.\n' > Notes.md && obend open > /dev/null
obend judge ../pay-b.json | head -3 && obend grants
```

```text
pay: landed as one turn over 2 pages by bob, receipt 857220abad27790e (1 in the chain)
  ledger/alice: balance 100 → 80
  ledger/carol: balance 5 → 25
pay: bob (read, write on ledger/*)
g2: bob (read, write on ledger/alice, ledger/carol)
```

The laptop comes home. The grants join, and a revocation made on either side stands after
(`merge_revocation_wins`): the laptop does not bring `pay` or `g2` back. Its landing of Bob's proposal
rested on them alone, so its pages are not merged, by name; the note is.

```sh
cd alice && obend merge ../laptop && obend grants
```

```text
ledger/alice, ledger/carol: not merged from laptop: the landing of pay (intent 275ecb5241f29055, by bob) rested on pay, g2, revoked here
Notes: imported from laptop
rendered Notes.md
work: performed 0, retained 0 of 1
pay: bob (read, write on ledger/*), revoked
g2: bob (read, write on ledger/alice, ledger/carol), revoked
g2r: bob (read on ledger/alice, ledger/carol)
g3: bob (read, write on ledger/*)
pay2: bob (read, write on ledger/*)
```
