/-
# Obend.Vault.Teeth — mutation teeth for the judge (a legacy leaf)

`judge_admits` and `judge_refuses` go through the Law library's and the law compiler's proofs, and
through `readVerdict`'s compiled matcher, whose bodies a `module` cannot see; a legacy file can
(REPORT-LAWDOC-20261031 D5). Nothing imports this file but the census.
-/
import Obend.Vault.Store
import Obend.Tactic.Tooth
open Obend.Law Obend.Spec.LawCompile Obend.Vault Obend.Doc

-- Each law compiled under its own name is what lets a refusal name it.
#tooth judge_refuses by mutation compiled := fun S pkg lin => lin.map fun p => (p.1, compile S pkg "another" p.2)
-- The verdict read off the run: reading every run as admitted breaks soundness.
#tooth judge_admits by mutation readVerdict := fun _ => .admitted
#tooth judge_refuses by mutation readVerdict := fun _ => .refused "law" "reason"
-- The judge refuses to decide a state that does not fit: deciding it anyway breaks soundness.
#tooth judge_admits by mutation Fits := fun _ _ _ => true
-- A write goes to a file only where the file differs from the store's text.
#tooth mem_writes by mutation writeOf := fun V p => V.lookup p.name
-- A selection deletes the other candidates' runs only: deleting the kept one's too breaks it.
#tooth select_keeps by mutation selectPatch := fun alts _ => (alts.flatMap fun x => segAtoms x.2).map Op.delete
