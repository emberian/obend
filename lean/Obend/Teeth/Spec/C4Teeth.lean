module
/-
# Obend.Teeth.Spec.C4Teeth — the C4 theorems' teeth (a leaf)

Each mutation breaks the stored proof: a cleaning that drops every candidate (monotonicity), a
repetition check that accepts everything (no repeats), a suffix tail that is always empty (the
suffix property).
-/
public import Obend.Spec.Proofs.C4
import all Obend.Spec.C4
import all Obend.Spec.Proofs.C4
public import Obend.Tactic.Tooth
namespace Obend.Spec.C4

#tooth linearize_monotone by mutation cleanAll := fun _ ls => some (ls.map fun _ => [])
#tooth linearize_nodup by mutation nodupB := fun _ => true
#tooth suffix_property by mutation tailOf := fun _ _ _ _ => .ok []

end Obend.Spec.C4
