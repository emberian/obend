# Study: the sibling trees consuming `obend`

The reason the library exists (`SHIP.md` §3): minidregg, nanodregg and delvetalk `require obend` and
delete the modules they imported from it. Nobody has studied what that costs. This is a read-only
study; the trees under `~/dev/minidregg`, `~/dev/nanodregg`, `~/dev/delvetalk` are not to be edited,
built or checked out.

Read `SHIP.md` §2–3, `GROUNDING.md` §1, `lean/README.md`, then in each tree: its `lakefile.toml`,
`lean-toolchain`, and every module that corresponds to something now in `obend`:
minidregg `Theory/ObjectiveBend*.lean`, `Compiler/ObjectiveBend*.lean`, `Host/ObjectiveBend*.lean`,
`Kernel/Objective*.lean` and whatever imports them (`grep -rl "Theory.ObjectiveBend\|Compiler.ObjectiveBend"`);
nanodregg `Lang/Contextual/*`, `Lang/{Law,Claim,Std}.lean` and their proofs and consumers;
delvetalk's `spec/` edition. Produce `/Users/ember/dev/obend/review/ADOPTION-PLAN-20261031.md`: per tree,
the module-by-module map old name to `Obend.*` name (or "no counterpart", or "diverged since the
copy, at commit X"), the consumers that would change their imports, every definition the tree uses
that `obend` renamed or restructured (the 4.35 bump, the `Typed`/`Graded` split, `checkWork`, the
public/private visibility of module files, cSHAKE as a `Digest` instance with the tree's Rust
kernel reattached by `@[csimp]`), the toolchain gap (minidregg and nanodregg at 4.30, delvetalk at
4.34, obend at 4.35) and what the bump costs each tree judging by `lean/docs/REPORT-LEAN435-20261031.md`,
the order the migration should go (which tree first, which module first, what the first green
`require obend` build would be), and the theorems the tree would lose or gain. Tag claims READ or
INFERRED. Commit the one file on `dev` with `git -c commit.gpgsign=false commit -F -` and trailer
`Co-Authored-By: Claude Opus <noreply@anthropic.com>`, rebase before pushing. Reply with the commit
hash and the first migration step you would take.
