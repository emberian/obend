/-
# Obend.Spec.Proofs.LawCompileTeeth — mutation teeth for `Obend.Spec.Proofs.LawCompile` (a legacy leaf)

The meaning and typing theorems re-check, under each mutation, proofs that go through the Law
library's and the checker's, whose bodies a `module` cannot see; a legacy file can. Nothing
imports this file.
-/
import Obend.Spec.Proofs.LawCompile
import Obend.Tactic.Tooth
open Obend.Law Obend.Spec.LawCompile

-- A boolean field reads as `1`/`0`; read raw, the meaning is lost.
#tooth compile_change by mutation scalarRead := fun _ t => t
-- A first write has no old state.
#tooth compile_birth by mutation clause := fun S name e _ a => guard (cond S .prior a e) name okT
-- An adoption is the identity write: judged as a first write, `monotone` would refuse it.
#tooth compile_adopt by mutation compile := fun S _ name e =>
  lawOf6 (clause S name e .none) (clause S name e .none) (fun _ => okT) (fun _ => okT)
    (clause S name e .prior) (clause S name e .prior)
-- A relaw of a package law is refused by name; admitting it breaks the theorem.
#tooth compile_relaw by mutation compile := fun S _ name e =>
  lawOf6 (clause S name e .none) (clause S name e .same) (fun _ => okT) (fun _ => okT)
    (clause S name e .prior) (clause S name e .prior)
-- The request's optional facts are sums the reads eliminate.
#tooth compile_checks by mutation optNatTy := .natural
