module
public import Obend.Tactic.Tooth
@[expose] public section
namespace Obend.Tactic.ToothChecks
/-! The teeth here are aimed at universal statements over `f`, so each one says something about `f`
itself, not about one value of it (a closed statement is a fixture and `#tooth` warns on it). -/
def f (n : Nat) : Nat := n
theorem lemmaF : ∀ n, f n = n := fun _ => rfl
theorem transitive : ∀ n, f n = n := lemmaF
#tooth transitive by mutation f := fun n => n + 1
/-- error: #tooth: stored proof of Obend.Tactic.ToothChecks.transitive still succeeds under mutation of Obend.Tactic.ToothChecks.f -/
#guard_msgs in
#tooth transitive by mutation f := fun n => n
/-- error: Type mismatch
  true
has type
  Bool
but is expected to have type
  Nat → Nat -/
#guard_msgs in
#tooth transitive by mutation f := true
inductive Indexed : Nat → Type where
 | mk (n : Nat) : Indexed (f n)
theorem inductiveUse : ∀ n, Nonempty (Indexed (f n)) := fun n => ⟨.mk n⟩
/-- error: #tooth: unsupported affected declaration Obend.Tactic.ToothChecks.Indexed -/
#guard_msgs (substring := true) in
#tooth inductiveUse by mutation f := fun n => n + 1
/-- A proof-valued definition must reconstruct successfully before a later
 theorem rejection can count as a tooth. -/
def reconstructionHelper : ∀ n, f n = n := fun _ => rfl
theorem reconstructionTarget : ∀ n, f n = n := reconstructionHelper
/-- error: #tooth: mutation/reconstruction invalid at Obend.Tactic.ToothChecks.reconstructionHelper; no tooth credited -/
#guard_msgs (substring := true) in
#tooth reconstructionTarget by mutation f := fun n => n + 1

theorem restored : ∀ n, f n = n := fun _ => rfl
end Obend.Tactic.ToothChecks
