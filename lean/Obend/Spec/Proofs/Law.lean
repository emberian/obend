module
/-
# Obend.Spec.Proofs.Law — the law parser decides (compiled evaluation of string functions)

The three compiled teeth of minidregg `Compiler/ObjectiveBendLaw.lean` (commit 092027a2): the
tally law parses, precedence is `implies` < `or` < `and` < `not`, and six constructs outside the
fragment refuse. Named `native_decide` claims, re-run by `#assert_compiled`.
-/
public meta import Obend.Spec.Law
public import Obend.AssertCompiled
namespace Obend.Spec.Law
set_option autoImplicit false

theorem parse_tally :
    (parse "new.total <= 1000 and monotone(total)").toOption =
      some (.and (.leC (.field "total") 1000) (.monotone "total")) := by native_decide

theorem parse_precedence :
    (parse "not new.a == 1 or new.b in [1, -2] implies request.caller == new.c and new.d <= new.e + 3").toOption =
      some (.implies (.or (.not (.eqC (.field "a") 1)) (.inC (.field "b") [1, -2]))
        (.and (.eqR .caller (.field "c")) (.leROff (.field "d") (.field "e") 3))) := by native_decide

theorem parse_refuses_nested :
    (parse "new.a.b == 1").toBool = false ∧ (parse "old.a == 1").toBool = false ∧
      (parse "new.a >= 1").toBool = false ∧ (parse "witnessed(x)").toBool = false ∧
      (parse "new.a == 1 claim").toBool = false ∧ (parse "request.target == 1").toBool = false := by
  native_decide

end Obend.Spec.Law

#assert_compiled Obend.Spec.Law.parse_tally
#assert_compiled Obend.Spec.Law.parse_precedence
#assert_compiled Obend.Spec.Law.parse_refuses_nested
