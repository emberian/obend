module
/- Compiled-evaluation audit adapted from Bread metatheory/Dregg2/Tactics.lean.
Re-runs actual closed Boolean oracle claims; rejects arbitrary named axioms.
This marks compiler trust and does not certify general source refinement. -/
public import Obend.AssertAxioms
public section

/- Lean v4.35 removed `Lean.ofReduceBool` and `Lean.ofReduceNat` (and `Lean.reduceBool`) from
`Init`. Until v4.30 this command accepted those two by name, sound only because the prelude
occupied the names; at v4.35 the names are free, so a user `axiom Lean.ofReduceBool : False` could
be declared and would have been accepted. Every oracle is now an axiom whose `<closed Bool> = true`
claim is re-run below; there is no by-name branch. -/

open Lean Elab Command in
/-- `#assert_compiled foo` — see the section note above. For every axiom `foo` rests on that is not
kernel-clean, this command requires an axiom asserting `<closed Bool expr> = true` whose
expression this command RE-RUNS through the compiled evaluator and watches return `true`. Anything
else is a hard ERROR. It ALSO errors if `foo` rests on no oracle at all (then it is kernel-clean and
the census `#assert_axioms_tree` already covers it). Each oracle is evaluated by the same checker used for the tree census. -/
elab "#assert_compiled" id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← Lean.collectAxioms name
  let candidates := axs.filter (fun a => !Obend.AssertAxioms.standard.contains a)
  for a in candidates do
    try Obend.AssertAxioms.replayOracle a
    catch ex => throwError "compiled-pin FAIL: {name}: {ex.toMessageData}"
  if candidates.isEmpty then
    throwError "compiled-pin REFUSED: {name} rests on NO compiled-evaluation oracle — it is \
      kernel-clean, so the census already covers it and it needs no compiled pin. \
      Labelling a kernel-clean fact 'compiled' throws away its real footing"

end
