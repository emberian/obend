# Code review brief for Kimi

Review the Lean code written in the last three days in `/Users/ember/dev/obend/lean/Obend` for
correctness, performance and engineering quality, as a Lean 4 expert who has not seen it before.
Read only; write one file, `/Users/ember/dev/obend/review/KIMI-CODE-20261101.md`.

The modules to read, newest first: `Obend/Core/Code.lean`, `Obend/Equiv/{Quote,Clairvoyant,Yields,Cost}.lean`,
`Obend/Judge/*.lean`, `Obend/Receipt.lean`, `Obend/Receipt/Merkle.lean`, `Obend/Fold.lean`,
`Obend/Run/{Shared,Fork,Durable,Control,Adapter}.lean`, `Obend/Intention.lean`, `Obend/Kind.lean`,
`Obend/Spec/C4.lean`, `Obend/Core/Bidirectional.lean`, `Obend/Core/Check.lean` (the quantity rules),
`Obend/Core/TypeGraph.lean`, `Obend/Vault/*.lean`, `Obend/Tactic/*.lean`, and their proofs under the
sibling `Proofs/` directories where a definition's correctness depends on them. Build if you want
(`cd lean && LEAN_NUM_THREADS=2 lake build`, two minutes); nobody else is editing the main checkout.

What I want:
1. **Correctness.** Definitions whose docstring claims more than the theorems prove; theorems whose
   hypotheses make them trivial; `decide`/`native_decide` facts that could be stated as theorems;
   places where a refusal is returned on the wrong branch; executable code (`Vault`, `Receipt`,
   `Judge/Lrat`, the CLI) that can disagree with the model it is proved against.
2. **Performance.** Definitions the kernel must reduce that will not scale (quadratic list code,
   non-structural recursion on fuel, `String` comparisons in hot paths, repeated `canonical` calls),
   and proofs that will slow the build as the tree grows (large `simp` sets, `grind` on big case
   splits, `decide` on big terms).
3. **Engineering.** Duplicated definitions across modules (the same resolution or fold written
   twice), typeclasses with one instance, structures whose laws are never used, naming that lies,
   `@[expose]` on things that need not be exposed, and anything a Lean maintainer would reject in
   review.
4. Ranked: the ten changes you would make first, each with the file and line.

Plain prose, one claim per sentence, no praise. Tag each claim READ (you opened it), RAN (you built
or evaluated it), INFERRED. The file is read by Ember and Claude.
