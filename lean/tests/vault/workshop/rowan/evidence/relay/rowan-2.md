---
test: "tests/relay/sandbox"
run: 2
artifact: "007f0e540122"
result: "pass"
exit: 0
by: "rowan"
kagi: 1
seconds: 8
---
# run 2 of [[jobs/relay]]'s budget, by rowan

On `007f0e540122` in /Users/ember/dev/obend-workshop.trees/rowan:

    /Users/ember/dev/obend-workshop/tools/accept/relay.sh .

```text
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
+ (sandboxed, live Kagi: one search) python3 research.py kagi obend -n 1
oobend
https://oobend.com/
Health footwear that moves with your feet. Oobend shoes, socks, and insoles use Japan-Knit technology: soft, flexible, never tight. No pressure points. ...


ok: kagi
+ python3 -m unittest discover -s tests
.relay 12:01:26 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmp_aihv2fu/spool (pid 59462)
relay 12:01:26 scry 59462-b0b62ea095eee505: HTTP 200 (0.0s)
relay 12:01:26 stopped
.relay 12:01:26 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmp_pb3p5nr/spool (pid 59462)
relay 12:01:26 kagi 59462-4b29a805174f777d: NoNetwork: relay has no network either (0.0s)
relay 12:01:26 stopped
.relay 12:01:26 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmp0xso3rct/spool (pid 59462)
relay 12:01:26 stopped
.relay 12:01:26 serving /var/folders/r8/kfrtq04d5dq_f50zm3tx3phw0000gn/T/tmpcikwt_cz/spool (pid 59462)
relay 12:01:26 stopped
.
----------------------------------------------------------------------
Ran 12 tests in 0.595s

OK
ok: unit tests
+ relay log (tail)
relay 12:01:19 serving /tmp/research-relay-501 (pid 57279)
relay 12:01:23 scry 58437-bcdd94a962c89152: HTTP 200 (0.3s)
relay 12:01:25 kagi 58931-d3e10c1cfc8fe381: HTTP 200 (0.9s)
relay 12:01:26 stopped
```
