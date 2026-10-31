module
/-
# Obend.Spec.Proofs.PackageLaw — a child package only narrows

About `Obend.Spec.PackageLaw.effectivePackages` (the effective law over a precedence list of packages):

* `package_law_eval`: it admits a write exactly when every clause of every package on the list
  does;
* `package_never_widens`: what a clause of an ancestor package refuses, the effective law refuses
  (`inherited_never_widens` across packages);
* `package_refusal_names`: a refusal names the first refusing clause as `PACKAGE law CLAUSE`, with
  that clause's own reason, the package on the list and the clause among its laws.
-/
public import Obend.Spec.PackageLaw
public import Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Inherit
import all Obend.Law.Proofs.Std
import all Obend.Law.Proofs.Claim
import all Obend.Law.Proofs.Run
import all Obend.Law.Proofs.Eval
public import Obend.Law.Proofs.Eval
public import Obend.Law.Std
public import Obend.Tactic.Tooth
namespace Obend.Spec.PackageLaw
open Obend.Law
open Obend.Core.Term
open Obend.Core.Data (Data)
set_option autoImplicit false

theorem mem_packageClauses {laws : String → List (String × Term)} {order : List String} {q : String × Term} :
    q ∈ packageClauses laws order ↔ ∃ pkg ∈ order, ∃ c ∈ laws pkg, q = (clauseName pkg c.1, c.2) := by
  simp only [packageClauses, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨pkg, hp, c, hc, rfl⟩
    exact ⟨pkg, hp, c, hc, rfl⟩
  · rintro ⟨pkg, hp, c, hc, rfl⟩
    exact ⟨pkg, hp, c, hc, rfl⟩

theorem effectivePackages_ok {laws : String → List (String × Term)} {order : List String} {law : Term}
    (h : effectivePackages laws order = .ok law) :
    law = effective (packageClauses laws order) ∧ ∀ p ∈ packageClauses laws order, closedB p.2 = true := by
  unfold effectivePackages at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hf
    cases h
    refine ⟨rfl, fun p hp => ?_⟩
    rw [List.find?_eq_none] at hf
    simpa using hf p hp

/-- **The effective package law is the conjunction of every package's clauses.** -/
public theorem package_law_eval {laws : String → List (String × Term)} {order : List String} {law : Term}
    (h : effectivePackages laws order = .ok law) (o n rq : Data) :
    Admits law o n rq ↔ ∀ pkg ∈ order, ∀ c ∈ laws pkg, Admits c.2 o n rq := by
  obtain ⟨rfl, hc⟩ := effectivePackages_ok h
  rw [effective_law_eval hc]
  constructor
  · intro hall pkg hp c hcl
    exact hall (clauseName pkg c.1, c.2) (mem_packageClauses.2 ⟨pkg, hp, c, hcl, rfl⟩)
  · intro hall q hq
    obtain ⟨pkg, hp, c, hcl, rfl⟩ := mem_packageClauses.1 hq
    exact hall pkg hp c hcl

/-- **A child package only narrows**: a write an ancestor package's clause refuses is refused. -/
public theorem package_never_widens {laws : String → List (String × Term)} {order : List String} {law : Term}
    (h : effectivePackages laws order = .ok law) {pkg : String} (hp : pkg ∈ order) {c : String × Term}
    (hcl : c ∈ laws pkg) {o n rq : Data} (hn : ¬ Admits c.2 o n rq) : ¬ Admits law o n rq :=
  fun ha => hn ((package_law_eval h o n rq).1 ha pkg hp c hcl)

/-- **A refusal names the ancestor package and its clause.** -/
public theorem package_refusal_names {laws : String → List (String × Term)} {order : List String} {law : Term}
    (h : effectivePackages laws order = .ok law) {o n rq : Data} {r : Term}
    (hr : Evaluates (applyLaw law o n rq) (.inject "refused" r)) :
    ∃ pkg ∈ order, ∃ c ∈ laws pkg, ∃ why, Evaluates (applyLaw c.2 o n rq) (.inject "refused" why) ∧
      RefusedBy law o n rq (clauseName pkg c.1) why := by
  obtain ⟨rfl, hc⟩ := effectivePackages_ok h
  obtain ⟨pre, name, L, post, why, hlin, _, hL, hby⟩ := effective_refusal_names hc hr
  have hmem : (name, L) ∈ packageClauses laws order := by rw [hlin]; simp
  obtain ⟨pkg, hp, c, hcl, heq⟩ := mem_packageClauses.1 hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨pkg, hp, c, hcl, why, hL, hby⟩

/-! ## Teeth: a report and its reviewer, as packages -/

/-- `papers/report` bounds `total`; `lab/review`, extending it, admits only its members. -/
def reportLaws (pkg : String) : List (String × Term) :=
  if pkg = "papers/report" then [("bounded", bounded unitTy "total" 5)]
  else if pkg = "lab/review" then [("members", allowlistLaw unitTy ["ann", "bob"])]
  else []

theorem packages_tooth :
    (effectivePackages reportLaws ["lab/review", "papers/report"]).toOption.isSome = true ∧
      (match effectivePackages reportLaws ["lab/review", "papers/report"] with
        | .ok law => blameOf (run 500 (applyLaw law (totalIs 0) (totalIs 9) (rqBy "ann" "ann" writeO))) ==
            some ("papers/report law bounded", "total over the bound") &&
          blameOf (run 500 (applyLaw law (totalIs 0) (totalIs 3) (rqBy "eve" "eve" writeO))) ==
            some ("lab/review law members", "not on the allowlist") &&
          okB (run 500 (applyLaw law (totalIs 0) (totalIs 3) (rqBy "ann" "ann" writeO)))
        | .error _ => false) = true := by
  decide +kernel

#tooth package_law_eval by mutation packageClauses := fun _ _ => []

end Obend.Spec.PackageLaw
