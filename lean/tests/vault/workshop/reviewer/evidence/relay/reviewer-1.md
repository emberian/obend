---
test: "tests/relay/sandbox"
run: 5
artifact: "ad3a6dc965bd"
result: "pass"
exit: 0
by: "reviewer"
kagi: 0
seconds: 11
---
# run 5 of [[jobs/relay]]'s budget, by reviewer

On `ad3a6dc965bd` in /Users/ember/dev/obend-workshop.trees/review:

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
.relay 12:25:51 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpnva88hoc/spool (pid 56985)
relay 12:25:51 scry c1: HTTP 200 (0.0s)
relay 12:25:51 stopped
.relay 12:25:52 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpe8qwl617/spool (pid 56985)
relay 12:25:52 scry 56985-881dc90b01ce6996: HTTP 200 (0.0s)
relay 12:25:52 stopped
.relay 12:25:52 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpu3d2ck1f/spool (pid 56985)
relay 12:25:52 stopped
.relay 12:25:52 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpw1g_m2jy/spool (pid 56985)
relay 12:25:52 stopped
...........................
----------------------------------------------------------------------
Ran 41 tests in 6.489s

OK
ok: unit tests
+ relay log (tail)
relay 12:25:45 serving /tmp/research-relay-501 (pid 55965)
relay 12:25:50 scry 56877-e4f7debef1ecee72: HTTP 200 (0.1s)
relay 12:25:56 stopped
```
