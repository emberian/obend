module
/-
# `extracted.SpecLawVectorsTest` — Law-parser, `FrontEndAdequacy`, and `SpecificationClosure` compiled vectors

Tier-2A home for compiled-trust surface `.obend` parsing/lowering/acceptance vectors:
1. The three compiled teeth of `Obend.Spec.Law` (`parse_tally`, `parse_precedence`, `parse_refuses_nested`).
2. `Obend.Spec.Proofs.FrontEndAdequacy.accept_inhabited` (open-recursive `Even`/`Odd` surface `.obend` acceptance).
3. The 13 `Obend.Spec.Proofs.SpecificationClosure` acceptance and refusal probes (`twice_accepted` through `builtin_parses`).
All re-run by `#assert_compiled`.
-/
public import Obend.Spec.Law
public meta import Obend.Spec.Law
public import Obend.Spec.FrontEnd
public meta import Obend.Spec.FrontEnd
public import Obend.AssertCompiled

namespace Obend.Spec.Law
set_option autoImplicit false

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem parse_tally :
    (parse "new.total <= 1000 and monotone(total)").toOption =
      some (.and (.leC (.field "total") 1000) (.monotone "total")) := by native_decide

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem parse_precedence :
    (parse "not new.a == 1 or new.b in [1, -2] implies request.caller == new.c and new.d <= new.e + 3").toOption =
      some (.implies (.or (.not (.eqC (.field "a") 1)) (.inC (.field "b") [1, -2]))
        (.and (.eqR .caller (.field "c")) (.leROff (.field "d") (.field "e") 3))) := by native_decide

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem parse_refuses_nested :
    (parse "new.a.b == 1").toBool = false ∧ (parse "old.a == 1").toBool = false ∧
      (parse "new.a >= 1").toBool = false ∧ (parse "witnessed(x)").toBool = false ∧
      (parse "new.a == 1 claim").toBool = false ∧ (parse "request.target == 1").toBool = false := by
  native_decide

end Obend.Spec.Law

#assert_compiled Obend.Spec.Law.parse_tally
#assert_compiled Obend.Spec.Law.parse_precedence
#assert_compiled Obend.Spec.Law.parse_refuses_nested

namespace Obend.Spec.Proofs.FrontEndAdequacy
open Lean (Json toJson)
open Obend.Spec.FrontEnd
set_option autoImplicit false

/-- Even/odd by open recursion over two specifications, tied by `fix`, and a `let`
(surface `.obend`). -/
def example_source : String :=
  "edition ObjectiveBend 1\n" ++
  "record Parity:\n  even(n: Nat) -> Bool\n  odd(n: Nat) -> Bool\n" ++
  "spec Even for Parity:\n  requires odd(n: Nat) -> Bool\n  def even(n: Nat) -> Bool:\n" ++
  "    match n:\n      case 0n: true\n      case 1n+p: self.odd(p)\n" ++
  "spec Odd for Parity:\n  requires even(n: Nat) -> Bool\n  def odd(n: Nat) -> Bool:\n" ++
  "    match n:\n      case 0n: false\n      case 1n+p: self.even(p)\n" ++
  "def ten(seed: Parity) -> Bool:\n  let parity = fix(compose(Even, Odd), seed)\n  parity.even(10n)\n"

def example_module : SourceModule := ⟨"Example", example_source, Sha256.hexString example_source, []⟩

def example_lowering : Except Diagnostic Lowering :=
  FrontEnd.lower [example_module] 0 "ten" (Json.arr #[]) (Json.arr #[])
    (Json.mkObj [("heap", toJson "100000"), ("stack", toJson "100000"), ("ticks", toJson "100000")]) "definition"

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem accept_inhabited :
    (match example_lowering with
      | .ok l => (FrontEnd.accept l).toBool
      | .error _ => false) = true := by
  native_decide
#assert_compiled accept_inhabited

end Obend.Spec.Proofs.FrontEndAdequacy

namespace Obend.Spec.Proofs.SpecificationClosure
open Lean (Json toJson)
open Obend.Spec.Elaborate
open Obend.Spec.FrontEnd
set_option autoImplicit false

def acceptsSource (source entry : String) : Bool :=
  let m : SourceModule := ⟨"Probe", source, Sha256.hexString source, []⟩
  match FrontEnd.lower [m] 0 entry (Json.arr #[]) (Json.arr #[])
      (Json.mkObj [("heap", toJson "100000"), ("stack", toJson "100000"), ("ticks", toJson "100000")]) "definition" with
  | .ok l => (FrontEnd.accept l).toBool
  | .error _ => false

def twiceSource : String :=
  "edition ObjectiveBend 1\n" ++
  "def twice(e: Extension<Nat>) -> Specification<Nat>:\n  compose(e, e)\n"

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem twice_accepted : acceptsSource twiceSource "twice" = true := by native_decide

def claimSpecSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\n" ++
  "spec Start for Counter:\n  claim positive: self.n == 41n\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Counter>:\n  Start\n"

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem claim_spec_accepted : acceptsSource claimSpecSource "asSpecification" = true := by native_decide

def badClaimSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\n" ++
  "spec Start for Counter:\n  claim positive: self.n + 1n\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Counter>:\n  Start\n"

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem non_boolean_claim_refused : acceptsSource badClaimSource "asSpecification" = false := by native_decide

def lawKeywordSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\n" ++
  "spec Start for Counter:\n  law positive: self.n == 41n\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Counter>:\n  Start\n"

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem law_keyword_refused : acceptsSource lawKeywordSource "asSpecification" = false := by native_decide

def wrongTargetSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\nrecord Other:\n  n: Nat\n  m: Nat\n" ++
  "spec Start for Counter:\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Other>:\n  Start\n"

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem wrong_target_refused : acceptsSource wrongTargetSource "asSpecification" = false := by native_decide

def reviewSpecs : String :=
  "edition ObjectiveBend 1\nrecord Review:\n  review(value: Nat) -> Nat\n  twice(value: Nat) -> Nat\n" ++
  "spec Base for Review:\n  def review(value: Nat) -> Nat:\n    value + 1n\n" ++
  "spec Twice for Review:\n  requires review(value: Nat) -> Nat\n  def twice(value: Nat) -> Nat:\n    self.review(self.review(value))\n" ++
  "spec Augmented for Review:\n  def review(value: Nat) -> Nat:\n    super.review(value) + 1n\n"

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem empty_seed_accepted :
    acceptsSource (reviewSpecs ++ "def run() -> Nat:\n  fix(compose(Base, Twice, Augmented), {}).twice(3n)\n") "run" = true := by
  native_decide

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem unprovided_requirement_refused :
    acceptsSource (reviewSpecs ++ "def run() -> Nat:\n  fix(compose(Twice, Augmented), {}).twice(3n)\n") "run" = false := by
  native_decide

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem inherited_unprovided_refused :
    acceptsSource (reviewSpecs ++ "def run() -> Nat:\n  fix(compose(Augmented, Base, Twice), {}).twice(3n)\n") "run" = false := by
  native_decide

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem requires_signature_refused :
    acceptsSource ("edition ObjectiveBend 1\nrecord R:\n  review(value: Nat) -> Nat\n" ++
      "spec S for R:\n  requires review(value: String) -> Nat\n  def review(value: Nat) -> Nat:\n    value\n" ++
      "def run() -> Nat:\n  fix(S, {}).review(1n)\n") "run" = false := by
  native_decide

def fourthFieldSource : String :=
  "edition ObjectiveBend 1\nrecord X:\n  x: Nat\nrecord XY:\n  x: Nat\n  y: Nat\n" ++
  "record XYZW:\n  x: Nat\n  y: Nat\n  z: Nat\n  w: Nat\n" ++
  "extension AddY[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:\n" ++
  "  extend(super, {y: 2n * self.x})\n" ++
  "extension AddZW(self: XYZW, super: XY) -> XYZW:\n  extend(super, {z: self.y, w: self.z + 1n})\n" ++
  "def run() -> Nat:\n  fix(compose(AddY, AddZW), {x: 5n}).w\n"

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem open_extension_reused_accepted : acceptsSource fourthFieldSource "run" = true := by native_decide

def heavierSpec : String :=
  "spec Heavier[Self has {weight: Nat, heavier(other: Self) -> Self}, Super has {weight: Nat}]:\n" ++
  "  def heavier(other: Self) -> Self:\n    if other.weight <= self.weight then self else other\n"

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem binary_self_accepted :
    acceptsSource ("edition ObjectiveBend 1\nrecord Node:\n  weight: Nat\n  heavier(other: Node) -> Node\n" ++
      heavierSpec ++ "def node(n: Nat) -> Node:\n  fix(Heavier, {weight: n})\n") "node" = true := by native_decide

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem f_bound_mismatch_refused :
    acceptsSource ("edition ObjectiveBend 1\nrecord Pair:\n  weight: Nat\n  heavier(other: Nat) -> Pair\n" ++
      heavierSpec ++ "def pair(n: Nat) -> Pair:\n  fix(Heavier, {weight: n})\n") "pair" = false := by native_decide

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem unbound_self_member_refused :
    acceptsSource ("edition ObjectiveBend 1\n" ++
      "extension Bad[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:\n" ++
      "  extend(super, {y: self.z})\ndef zero() -> Nat:\n  0n\n") "zero" = false := by native_decide

-- fixture kept (2026-11-04): compiled-trust vector, re-run by #assert_compiled
theorem builtin_parses : Elaborate.builtinModule.toBool = true := by native_decide

#assert_compiled twice_accepted
#assert_compiled claim_spec_accepted
#assert_compiled non_boolean_claim_refused
#assert_compiled law_keyword_refused
#assert_compiled wrong_target_refused
#assert_compiled builtin_parses
#assert_compiled empty_seed_accepted
#assert_compiled unprovided_requirement_refused
#assert_compiled inherited_unprovided_refused
#assert_compiled requires_signature_refused
#assert_compiled open_extension_reused_accepted
#assert_compiled binary_self_accepted
#assert_compiled f_bound_mismatch_refused
#assert_compiled unbound_self_member_refused

end Obend.Spec.Proofs.SpecificationClosure
