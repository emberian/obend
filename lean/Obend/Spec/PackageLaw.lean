module
/-
# Obend.Spec.PackageLaw — package laws inherit across the package boundary

A package's root module may declare `law NAME: EXPR` lines (`Obend.Spec.Law`), compiled per declared
state type (`Obend.Spec.LawCompile`). Across a workspace closure (`Obend.Spec.Ecosystem.close`) the
effective law of the entry package is `Obend.Law.effective` over the closure's precedence list,
each package contributing its clauses in source order, each clause named `PACKAGE law CLAUSE`
(`clauseName`). The parent's package law is therefore an ancestor of the child's effective law; a
refusal names the ancestor package and its clause; and a child only narrows
(`Obend.Spec.Proofs.PackageLaw`: `package_law_eval`, `package_never_widens`,
`package_refusal_names`). Overriding a parent's law is a new release of the parent, not a clause
of the child.
-/
public import Obend.Law.Inherit
public section
namespace Obend.Spec.PackageLaw
open Obend.Law
open Obend.Core.Term (Term)
set_option autoImplicit false

/-- The name a refusal gives clause `clause` of package `pkg`. -/
@[expose] def clauseName (pkg clause : String) : String := pkg ++ " law " ++ clause

/-- The named clauses of a precedence list of packages, each package's laws (`laws pkg`, in its
source order) under `clauseName`. -/
@[expose] def packageClauses (laws : String → List (String × Term)) (order : List String) : List (String × Term) :=
  order.flatMap fun pkg => (laws pkg).map fun (clause, t) => (clauseName pkg clause, t)

/-- Why the effective package law is not built: a clause with a free index would mean something
different in every position. -/
structure OpenClause where
  name : String
  deriving DecidableEq, Repr

/-- The effective law of a precedence list of packages: every clause closed, then `effective`. -/
@[expose] def effectivePackages (laws : String → List (String × Term)) (order : List String) : Except OpenClause Term :=
  let clauses := packageClauses laws order
  match clauses.find? (fun p => !closedB p.2) with
  | some p => .error ⟨p.1⟩
  | none => .ok (effective clauses)

end Obend.Spec.PackageLaw

end
