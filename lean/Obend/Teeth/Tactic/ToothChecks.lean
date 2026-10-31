module
public import Obend.Tactic.Tooth
@[expose] public section
namespace Obend.Tactic.ToothChecks
@[expose] def f : Nat := 0
theorem lemmaF : f = 0 := rfl
theorem transitive : f = 0 := lemmaF
#tooth transitive by mutation f := 1
/-- error: #tooth: stored proof of Obend.Tactic.ToothChecks.transitive still succeeds under mutation of Obend.Tactic.ToothChecks.f -/
#guard_msgs in
#tooth transitive by mutation f := 0
/-- error: Type mismatch
  true
has type
  Bool
but is expected to have type
  Nat -/
#guard_msgs in
#tooth transitive by mutation f := true
inductive Indexed : Nat → Type where
 | mk : Indexed f
theorem inductiveUse : Nonempty (Indexed f) := ⟨.mk⟩
/-- error: #tooth: unsupported affected declaration Obend.Tactic.ToothChecks.Indexed -/
#guard_msgs (substring := true) in
#tooth inductiveUse by mutation f := 1
/-- A proof-valued definition must reconstruct successfully before a later
 theorem rejection can count as a tooth. -/
@[expose] def reconstructionHelper : f = 0 := rfl
theorem reconstructionTarget : f = 0 := reconstructionHelper
/-- error: #tooth: mutation/reconstruction invalid at Obend.Tactic.ToothChecks.reconstructionHelper; no tooth credited -/
#guard_msgs (substring := true) in
#tooth reconstructionTarget by mutation f := 1

theorem restored : f = 0 := rfl
end Obend.Tactic.ToothChecks
