# Paper revision: prior art in, the three uncertain spots fixed, the checker story updated

`paper/objective-bend.md` was written before `review/PRIOR-ART-20261030.md` existed and before the
checker lane. Revise it in place.

1. Related work: use `review/PRIOR-ART-20261030.md` and the papers it names in `~/paperbin`
   (each has a `.txt`). Cite the precedents for each aspect the paper discusses (open recursion and
   mixins; linearization; call-by-need; bidirectional typing and annotatability; quantitative types;
   recursive type equality), by author and year, one or two sentences each, and say in one sentence
   per aspect what Objective Bend adds over it. No claim about a paper you did not open.
2. The three places the first draft was least sure of (its own closing note): trace the template
   instantiation path in `lean/Obend/Spec/Elaborate.lean` (`templateLayer`, `instantiate`,
   `chainFix`) and make §6 say what the code does; re-verify the §10 open items against the tree
   and drop or restate the ones that are no longer true; for the 19 private constants whose axioms
   could not be printed, say so plainly or cite their module's pin.
3. The checker: §8's "what is proved" must now say that the annotation-directed checker is
   provably incomplete for `PartialTyping` (`Core/Proofs/CheckCompletenessObstruction.lean`), that a
   bidirectional checker exists with a completeness theorem on a stated fragment
   (`Core/Proofs/BidirectionalCompleteness.lean`, `complete`, `full_corollary_fails`), and that
   equi-recursive type agreement is in progress (read `lean/docs/REPORT-CHECKER-20261030.md` and the
   `Core/EquiRecursiveAgreement.lean` module if it exists when you get there; describe only what is
   committed on `origin/dev`).

Keep the evidence words (compiled, proved, executed). Every theorem name must resolve under
`lean/Obend` on `origin/dev`; check with a script as the first draft did. You own `paper/**` only;
nothing to build. Commit on `dev` with `git -c commit.gpgsign=false commit -F -` and trailer
`Co-Authored-By: Claude Sonnet <noreply@anthropic.com>`; `git fetch` and rebase if the tree is clean,
otherwise commit and push directly. Reply with the commit hash and any claim you removed.
