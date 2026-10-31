module
/-
# Obend.Core.Proofs.Substitution — filling hypotheses: the definitions

A HOLE is a free de Bruijn hypothesis of an open term; a FILLING is a closed annotated term;
`msubst σ t` puts the fillings `σ` names in place of the hypotheses they name, in the term by
`Term.substitute` and in the annotations by `annotationsAt`, which walks the checker's source
positions and answers with a filling's own annotation below the position where it lands. The use
vectors' order (`UsesLE`, `UsesMasked`) and the premise lemmas are in `Uses`. The substitution lemma
is `TypedSubstitution.checked_msubst` (on the typing relation) and
`CheckerTransport.checkAgainst_msubst` (on the checker); its three corners have teeth in tier 2
(`Obend/Teeth/Core/SubstitutionTeeth.lean`).
-/
public import Obend.Core.Proofs.Substitution.Defs
public import Obend.Core.Proofs.Substitution.Uses
