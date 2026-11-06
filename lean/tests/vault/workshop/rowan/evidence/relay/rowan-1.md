---
test: "tests/relay/sandbox"
run: 1
artifact: "007f0e540122"
result: "pass"
exit: 0
by: "rowan"
kagi: 0
seconds: 5
---
# run 1 of [[jobs/relay]]'s budget, by rowan

On `007f0e540122` in /Users/ember/dev/obend-workshop.trees/rowan:

    /Users/ember/dev/obend-workshop/tools/accept/relay.sh .

```text
    "spend_today_usd": 0.0,
    "wallet": {
      "jev_credit_balance_nanodollars": 1984392128,
      "money_unit": "nanodollars",
      "paid_balance_nanodollars": 100000000000,
      "promo_credit_balance_nanodollars": 0,
      "reserved_nanodollars": 0,
      "scry_credit_balance_nanodollars": 8556539079,
      "scry_credit_display_name": "Free credit",
      "spend_order": {
        "external_provider": [
          "promo_credit",
          "cash"
        ],
        "judgment": [
          "jev_credit",
          "promo_credit",
          "cash"
        ],
        "scry_query": [
          "scry_credit",
          "promo_credit",
          "cash"
        ]
      },
      "spendable_judgment_nanodollars": 101984392128,
      "spendable_provider_nanodollars": 100000000000,
      "spendable_scry_nanodollars": 108556539079,
      "user_id": "8e73c8fc-b4cc-45de-aa81-d057c10bcc19"
    }
  },
  "memory": {
    "slug": "main",
    "updated_at": null,
    "version": 0
  },
  "next": "Queries are free while the system has slack — every response reports billing_mode (free_slack under slack; a charged one reports credit_reservation), spend_nanodollars what the wallet paid, burden_nanodollars what the machine did — so ask your wildest curiosity directly. Opening move: schema mode=index for the catalog, one 
ok: scry whoami
(no live Kagi search in this run)
+ python3 -m unittest discover -s tests
.relay 11:58:26 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmp0fgzvdpe/spool (pid 27535)
relay 11:58:27 scry 27535-b86ac4b6b906e55a: HTTP 200 (0.0s)
relay 11:58:27 stopped
.relay 11:58:27 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpffdkjv5o/spool (pid 27535)
relay 11:58:27 kagi 27535-8f7b8993e4163591: NoNetwork: relay has no network either (0.0s)
relay 11:58:27 stopped
.relay 11:58:27 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpno66vu_o/spool (pid 27535)
relay 11:58:27 stopped
.relay 11:58:27 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpmyo_ahz3/spool (pid 27535)
relay 11:58:27 stopped
.
----------------------------------------------------------------------
Ran 12 tests in 0.528s

OK
ok: unit tests
+ relay log (tail)
relay 11:58:22 serving /tmp/research-relay-501 (pid 27420)
relay 11:58:26 scry 27517-11e64ab8a14ddbb4: HTTP 200 (0.2s)
relay 11:58:27 stopped
```
