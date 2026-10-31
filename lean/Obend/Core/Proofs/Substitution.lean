module
/-
# Obend.Core.Proofs.Substitution — filling hypotheses keeps a checked term checked

The substitution lemma of the contextual calculus (`Obend.Slot.Core4`), stated of Core4's own
checker. A HOLE is a free de Bruijn hypothesis of an open term; a FILLING is a closed annotated
term; `msubst σ t` puts the fillings `σ` names in place of the hypotheses they name, in the term by
`Term.substitute` and in the annotations by `annotationsAt`, which walks the checker's positions
(`infer`'s numbering of children) and answers with a filling's own annotation below the position
where it lands. The lemma (`check_msubst`): if `t` checks in `Ψ` and every filling checks in `Ψ` at
exactly the type `Ψ` declares for its hypothesis, then `msubst σ t` checks in `Ψ` at `t`'s type,
with no more uses of any hypothesis than `t` had.

Three corners, each with a tooth (`*_tooth`, in tier 2: `Obend/Teeth/Core/SubstitutionTeeth.lean`): fillings must be CLOSED (an open filling that
shares a linear hypothesis with its surroundings is refused after substitution), fillings check
under the TEMPLATE'S assumptions (`msubst` keeps `t.assumptions`; the slot judges a filling under
its own), and the FUEL adds (a term that checks at fuel `n` with fillings at fuel `m` checks at
`n + m`; at a fixed fuel the lemma holds only within the budget, by monotonicity).

The lemmas on the way are of independent use: `infer` is monotone in its fuel (`infer_mono`,
`check_mono`), a checked term is scoped by its context (`typed_scoped`), and a closed term checks
the same in any valid context, at any position, with zero uses (`infer_transport`).
-/
public import Obend.Core.Proofs.Substitution.Defs
public import Obend.Core.Proofs.Substitution.Uses
public import Obend.Core.Proofs.Substitution.Transport
public import Obend.Core.Proofs.Substitution.Mono
public import Obend.Core.Proofs.Substitution.Msubst
