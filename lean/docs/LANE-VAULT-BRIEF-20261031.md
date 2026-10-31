# Lane Vault: `obend open ~/vault`

The product the design origin names: "living (o)bend bringing to life their obsidian and other
knowledge entities". `DESIGN.md` §5 says what day one is: open a folder of markdown as pages, every
wikilink a cite, every `law:` line in frontmatter a law, every folder a kind; nothing in the vault
changes shape; what changes is that a second author'"'"'s edit is a candidate in a section, a quote from
a moved source goes behind, a law refuses an edit and says which line would pass. Read `DESIGN.md`
§5, `lean/docs/REPORT-DOC-20261030.md` and `REPORT-LAWDOC-20261031.md` (identity and byte cites,
backlinks), `REPORT-LAW-20261030.md`, then the code: `Obend/Doc/Render.lean` (`Vault`, `Vault.read`,
`readPage`, `renderAt`), `Obend/Doc/{Section,Merge,Patch}.lean`, `Obend/Main.lean` (the CLI:
`check`, `run`, `--package`), `Obend/Law`, and `lean/tests/doc/` (the two-page vault round trip).

Build, one commit each: (1) `obend open DIR`: read a directory of `.md` files as a `Vault`, keep a
world beside it (a `.obend/` directory with the pinned pages, versions, cites and laws), render each
page at the current view back to the files, and report what is behind; `obend open` twice on an
unchanged vault is a no-op, proved as a round trip over any vault the reader accepts. (2) Edits: a
member'"'"'s change to a page (another `obend` process or a second directory) becomes a patch; two
patches merge by the pushout; a conflict is rendered as a section with alternatives, in the markdown,
readable by a person, with the command that selects one. (3) Laws: a `law:` line in frontmatter
(the `.obend` fragment, compiled by `Spec/LawCompile`) is judged on every write to that page, a
refusal names the clause and what would pass, and a folder'"'"'s `_kind.md` law is an ancestor of every
page'"'"'s in it. (4) Agents as members: an `obend member add NAME --grant …` and a page the member
may post candidates to but not select on, so the "second author" of day one is real. The acceptance
test is a stranger'"'"'s walkthrough in `lean/tests/vault/WALKTHROUGH.md` executed by a script: create a
vault of three pages, cite across them, write a law, invite a member, have the member post, merge
an offline edit, select a conflict, move a source and watch a byte cite go behind while the identity
cite stays.

Work in your own worktree (`git worktree add /private/tmp/claude-501/-Users-ember-dev-obend/01a18fe9-771b-71b2-b01f-da7ed6517d48/scratchpad/<lane> dev`); Lean v4.35.0; `LEAN_NUM_THREADS=2 lake build 2>&1 | tee build.log` (207 jobs). Every file a `module` (`lean/docs/REPORT-20261030.md` §2). The census in `Obend/Census.lean` is the only axiom check; do not add `#assert_axioms` lines. Mini's cohorts (`python3 lean/tests/run-obend-source.py`) are the control and must stay unchanged unless a change is recorded as a deviation. Named-file commits on `dev`, `git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before each push; a proof-engineering lane is restructuring proofs under `Obend/Core/Proofs` concurrently, so keep theirs on conflicts there. No sorry, no axiom; a theorem that could be vacuous gets a `#tooth`. Report in `lean/docs/`. Ember: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait. Reply with the commit range, what is proved, and the one decision for Ember.
