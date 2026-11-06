---
test: "tests/relay/sandbox"
run: 3
artifact: "ad3a6dc965bd"
result: "pass"
exit: 0
by: "rowan"
kagi: 0
seconds: 13
---
# run 3 of [[jobs/relay]]'s budget, by rowan

On `ad3a6dc965bd` in /Users/ember/dev/obend-workshop.trees/rowan:

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
.relay 12:22:03 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmphmwptcu9/spool (pid 33899)
relay 12:22:03 scry c1: HTTP 200 (0.0s)
relay 12:22:03 stopped
.relay 12:22:03 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpxsrkpr50/spool (pid 33899)
relay 12:22:03 scry 33899-f5e913e23ea1fbc0: HTTP 200 (0.0s)
relay 12:22:03 stopped
.relay 12:22:03 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpsdgdgnjd/spool (pid 33899)
relay 12:22:03 stopped
.relay 12:22:04 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmp_q25o75i/spool (pid 33899)
relay 12:22:04 stopped
...........................
----------------------------------------------------------------------
Ran 41 tests in 7.448s

OK
ok: unit tests
+ relay log (tail)
relay 12:21:57 serving /tmp/research-relay-501 (pid 33650)
relay 12:22:01 scry 33874-87284ea6668a2977: HTTP 200 (0.2s)
relay 12:22:09 stopped
```
