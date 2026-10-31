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
#tooth compile_first by mutation clause := fun S name e _ a => guard (cond S true a e) name okT
-- A relaw writes no state; judging it breaks the inert theorem.
#tooth compile_inert by mutation compile := fun S name e =>
  lawOf6 (clause S name e false) (clause S name e false) (clause S name e true) (fun _ => okT)
    (clause S name e true) (clause S name e true)
-- The request's optional facts are sums the reads eliminate.
#tooth compile_checks by mutation optNatTy := .natural
