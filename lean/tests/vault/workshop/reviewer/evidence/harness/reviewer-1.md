---
test: "tests/harness/unit"
run: 2
artifact: "751b497f3fab"
result: "pass"
exit: 0
by: "reviewer"
kagi: 0
seconds: 6
---
# run 2 of [[jobs/harness]]'s budget, by reviewer

On `751b497f3fab` in /Users/ember/dev/obend-workshop.trees/review:

    /Users/ember/dev/obend-workshop/tools/accept/harness.sh .

```text
test_every_option_has_help (test_research.TestHelp.test_every_option_has_help) ... ok
test_kagi_cli_error_exits_1 (test_research.TestKagi.test_kagi_cli_error_exits_1) ... ok
test_kagi_cli_json (test_research.TestKagi.test_kagi_cli_json) ... ok
test_kagi_cli_no_results (test_research.TestKagi.test_kagi_cli_no_results) ... ok
test_kagi_cli_prints_hits (test_research.TestKagi.test_kagi_cli_prints_hits) ... ok
test_kagi_http_error_carries_the_message (test_research.TestKagi.test_kagi_http_error_carries_the_message) ... ok
test_kagi_http_error_without_json (test_research.TestKagi.test_kagi_http_error_without_json) ... ok
test_kagi_key_from_env_file (test_research.TestKagi.test_kagi_key_from_env_file) ... ok
test_kagi_no_key_makes_no_call (test_research.TestKagi.test_kagi_no_key_makes_no_call) ... ok
test_kagi_search_posts_v1_and_cleans_hits (test_research.TestKagi.test_kagi_search_posts_v1_and_cleans_hits) ... ok
test_scry_cli_call_prints_non_json_as_is (test_research.TestScry.test_scry_cli_call_prints_non_json_as_is) ... ok
test_scry_cli_error_exits_1 (test_research.TestScry.test_scry_cli_error_exits_1) ... ok
test_scry_cli_sql_needs_a_statement (test_research.TestScry.test_scry_cli_sql_needs_a_statement) ... ok
test_scry_cli_sql_options (test_research.TestScry.test_scry_cli_sql_options) ... ok
test_scry_cli_tools (test_research.TestScry.test_scry_cli_tools) ... ok
test_scry_key_from_file (test_research.TestScry.test_scry_key_from_file) ... ok
test_scry_no_key_makes_no_call (test_research.TestScry.test_scry_no_key_makes_no_call) ... ok
test_scry_rpc_error (test_research.TestScry.test_scry_rpc_error) ... ok
test_scry_rpc_json_reply (test_research.TestScry.test_scry_rpc_json_reply) ... ok
test_scry_rpc_sse_reply (test_research.TestScry.test_scry_rpc_sse_reply) ... ok
test_scry_schema_and_embed_arguments (test_research.TestScry.test_scry_schema_and_embed_arguments) ... ok
test_scry_tool_error (test_research.TestScry.test_scry_tool_error) ... ok

----------------------------------------------------------------------
Ran 26 tests in 3.824s

OK
+ python3 research.py  --help
+ python3 research.py kagi --help
+ python3 research.py scry --help
usage: research.py [-h] {kagi,scry} ...

Kagi web search and Scry (SQL over the public internet), for any agent.

Stdlib only: runs under any python3 without a venv. Import it or call it.

Keys, env var first, then the standing file:
  Kagi  KAGI_API_KEY   else KAGI_API_KEY= in ~/dev/allgame/.env (a v1 key)
  Scry  SCRY_API_KEY   else ~/.scry-key

Endpoints, read at each call: RESEARCH_KAGI_URL and RESEARCH_SCRY_URL from
the environment (a local fake server, in the tests), else KAGI_URL and
SCRY_URL below. Every request goes through _post(url, headers, body,
timeout) -> (status, text), looked up at call time: replace research._post
to carry requests some other way.

CLI (every command takes --help):
  research.py kagi QUERY [-n N] [--json]
  research.py scry sql SQL [--explain] [--limit N] [--max-seconds S]
  research.py scry sql --q LINE --relation REL [--explain] [--limit N] [--max-seconds S]
  research.py scry schema [--relation A,B] [--mode MODE]
  research.py scry embed NAME [--text TEXT] [--sql SQL] [--model MODEL]
  research.py scry whoami
  research.py scry tools
  research.py scry call TOOL [JSON]

Kagi bills per search; use it frugally. Scry queries are free while the
system has slack and metered under load; start at LIMIT 20 and read the
meter before widening. `research.py scry call guide` is Scry's own manual.

```
