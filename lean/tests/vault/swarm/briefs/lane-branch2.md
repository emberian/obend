# Brief of lane-branch2

Sent by the root (session 01a1ad7d, message 918, 2026-11-06T01:08:38.771Z) to agent a1fc6c77, verbatim:

    lane-branch is merged (dev 40cbbd7; `Obend.Vault` and the Branch walkthrough build on dev). The theorems are the right shape, and the channel exhibit (a law over links into a hidden page leaking whether a write lands) is exactly the honest statement I asked for.
    
    Next quest, from your own judgment calls:
    1. "Their laws agree" as a real third judgement rather than always-conflict. breadstuffs has I-confluence as a proved classifier (`guardGluing_iff_iconfluent` and the Live/LatticeOnly dichotomy under /Users/ember/dev/breadstuffs/metatheory/, and leanuweave's `Gluing.lean` under /Users/ember/dev/leanuweave/; read them for the shape, take nothing by copy). In the vault: a page law may declare its merge (a counter that adds, a set that unions, a max), and two overlapping writes whose page's law is I-confluent merge by that law instead of becoming a conflict, with the theorem that the merged value satisfies the law whenever both sides did (`iconfluent_merge_lawful`). Identical writes on both sides land once. Everything without a declared confluent law stays a conflict state, as now.
    2. Order independence: `merge base L R` and `merge base R L` give the same tip store and the same conflict set up to naming (state it exactly; if it is false for some reason the module should say which, with the counterexample as a test).
    3. The CLI and the walkthrough: `obend branch fork|merge|resolve` over real stores on disk, and a step in `lean/tests/vault/walkthrough.py` running the two-store scenario end to end through the binary, so the refusal texts in your report are printed by `obend` and not only checked by `#guard`.
    4. The stale-pin case: a refusal for a revoked sturdyref should name the uri even when a stale pin is also present; make the refusal carry every reason, or order them so the authority reason is never hidden, and say which.
    
    Keep `mergeFrom` untouched unless folding it into Branch is the honest thing (then do it and say so; "nothing lands beside"). Work from dev: `git fetch /Users/ember/dev/obend dev && git checkout -B lane-branch2 FETCH_HEAD` in your worktree. Same rules as before (box safety, PID file or nothing, never stash, never an unfiltered suite; the pre-push hook's 60 s module budget is not yours to bypass, report it instead). Commit named files unsigned if needed, do not merge; report the theorem statements verbatim, the CLI transcript, and what you left out.
