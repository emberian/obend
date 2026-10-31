module
/- The teeth of the demand semantics' results on objects (`Obend.Equiv.CostTests`). With the field
that reads itself replaced by a constant, `{good = 7, bad = 7}.bad` has a derivation, and the stored
proof of `bad_field_no_cv` no longer checks; with the field that reads its sibling made to read
itself, the stored derivation of `self_field_cost` no longer checks. So neither result passes
because the semantics derives nothing, or everything. -/
public import Obend.Tactic.Tooth
import all Obend.Equiv.CostTests
open Obend.Core.Term

#tooth Obend.Equiv.CostTests.bad_field_no_cv by mutation Obend.Equiv.CostTests.selfLam :=
  fun n1 n2 _ => Term.lam (.lam (.record [(n1, .nat 7), (n2, .nat 7)]))

#tooth Obend.Equiv.CostTests.self_field_cost by mutation Obend.Equiv.CostTests.selfLam :=
  fun n1 n2 _ => Term.lam (.lam (.record [(n1, .nat 7), (n2, .get (.bound 1) n2)]))
