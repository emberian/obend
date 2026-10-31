module
/- The tooth of the clairvoyant semantics' negative results (`Obend.Equiv.CostTests`): with the field
that reads `self` replaced by a constant, `{a = 7, b = 7}.b` has a derivation, and the stored proof
of `self_field_no_cv` no longer checks. So the theorem is not passing because the semantics derives
nothing. -/
public import Obend.Tactic.Tooth
import all Obend.Equiv.CostTests
open Obend.Core.Term

#tooth Obend.Equiv.CostTests.self_field_no_cv by mutation Obend.Equiv.CostTests.selfObject :=
  fun n1 n2 _ => Term.fix (.lam (.lam (.record [(n1, .nat 7), (n2, .nat 7)]))) (.record [])
