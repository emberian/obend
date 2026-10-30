# Lane Doc: the patch algebra and the page, as `Obend.Doc`

Goal: the document layer of `DESIGN.md` §5 as a Lean library, built on the slot. A page's content is
rows of runs; an edit is a patch; merge is a pushout with conflicts as alternatives; a section is a
slot whose candidates are runs and whose supports include cites. Read `DESIGN.md` §5, `SHIP.md` §2
row `Obend/Doc`, `METATHEORY.md` §2 (the Doc row), the paper Mimram and Di Giusto, *A Categorical
Theory of Patches* (`~/paperbin/mimram-digiusto2013-categorical-theory-of-patches.txt`), and
breadstuffs' Rust patch core for the operation grammar
(`/Users/ember/dev/breadstuffs/dregg-doc/src/lib.rs`, read-only: `Op::{Add,Delete,Connect,SetField}`,
`apply`, `compose`, `invert`, `merge`, `ConflictRegion`). The slot API you build on is
`lean/Obend/Slot.lean` (`Slot`, `usable`, `read`, `alternatives`, `slot_repair`); read its docstrings.

Work in your own git worktree (`git worktree add <scratchpad>/doc-lane dev`), because Astra is
rebuilding `Obend/Core` in the main checkout and two `lake build`s in one `.lake` collide. Build
with `LEAN_NUM_THREADS=2 lake build Obend.Doc 2>&1 | tee build.log` in the worktree. Every file a
`module` (see `lean/docs/REPORT-20261030.md` §2 for what Lean 4.30 requires of that).

Build, one commit each, under `lean/Obend/Doc/` with root `lean/Obend/Doc.lean` added to `Obend.lean`:

1. `Graph.lean`: the document as a graph of atoms with status (alive, dead) and order edges, with
   stable atom identities; `Patch.lean`: the four operations, `apply`, `compose`, `invert`, and the
   theorems `apply_compose`, `apply_invert` (round trip on the atoms the patch touches), stated and
   proved for the actual representation.
2. `Merge.lean`: the pushout of two patches from a common base in the category Mimram–Di Giusto
   describe, with the universal property proved for your representation (not asserted), and the
   case where no pushout exists in the plain category handled as they do: the free finite
   cocompletion, where a conflict is an object, an antichain of live alternatives.
3. `Section.lean`: a section as `Slot Fact Run` with candidates posted runs; a cite as a support
   `(page, range, version, byteCommitment)`; the theorem that a merge conflict's alternatives are
   exactly the section's `alternatives` reading under the slot's `read`; a pinned cite stays usable
   when its source moves, a following cite's currency fact fails (both as theorems with teeth).
4. `Render.lean`: a page's rendering to text at a view and a reader from a markdown file into pages
   and cites (wikilinks become cites), so `lean/tests/doc/` can hold a two-page vault round trip.

Every theorem that could be vacuous ships with a `decide` tooth or a `#tooth` (`Obend/Tactic`).
Write `lean/docs/REPORT-DOC-20261030.md` in the lane-report style. Commits: named files on `dev`,
`git -c commit.gpgsign=false commit -F -`, trailer `Co-Authored-By: Claude Opus <noreply@anthropic.com>`,
rebase on `origin/dev` before each push (Astra pushes often; your files do not overlap its). The
source trees are read-only. No sorry, no axiom.

Ember's safety paragraph, verbatim: "Never kill by pattern. No `pkill -f <anything>`, no `pkill -x
<bare word>`, no `killall`, no `kill -u`. A process you started is stopped by the PID in its PID
file, and only that. Every detached job writes one (`nohup ... & echo $! > job.pid`). No PID file,
no kill: tell me instead." When a disk is low: stop writing to it, tell Ember, wait.

Reply with the commit range, which theorems are proved, and the one decision for Ember.
