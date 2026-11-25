module
public import Obend.Lower.Pancake.PanSem
import all Obend.Lower.Pancake.PanSem

public section
namespace Obend.Lower.Pancake

/-- Actual PanSem FFI events, including calls which return an error status. -/
def events {θ} (s : PanState θ) := s.ffi.io_events.map IOEvent.name

def CommandTrace (c : PStmt) (names : List String) : Prop :=
  ∀ {θ : Type} (s : PanState θ),
    ((evaluate c s).1 = .normal → events (evaluate c s).2 = events s ++ names) ∧
    ∀ w : Word, (evaluate c s).1 = .ret (.word w) → w = 0

theorem seq_trace {a b left right} (ha : CommandTrace a left) (hb : CommandTrace b right) :
    CommandTrace (.seq a b) (left ++ right) := by
  intro θ s
  rw [evaluate_seq]
  dsimp only
  split
  · rename_i normal
    have eq : (evaluate a s).1 = .normal := eq_of_beq normal
    obtain ⟨rest,early⟩ := hb (evaluate a s).2
    exact ⟨fun h => by rw [rest h,(ha s).1 eq,List.append_assoc],early⟩
  · exact ⟨fun h => by simp_all, (ha s).2⟩

theorem skip_trace : CommandTrace .skip [] := by
  intro θ s
  simp [evaluate_skip]

theorem store_trace (a b : PExp) : CommandTrace (.storeByte a b) [] := by
  intro θ s
  rw [evaluate_storeByte]
  repeat' split <;> simp [events]

theorem status_trace (cond : PExp) : CommandTrace (.ite cond (.ret (.const 0)) .skip) [] := by
  intro θ s
  rw [evaluate_ite]
  repeat' split <;> simp [evaluate_ret,evaluate_skip,events]

private theorem ffi_events {θ} {ffi final : FFIState θ} {name conf input output}
    (named : name ≠ "") (success : call_FFI ffi name conf input = .FFI_return final output) :
    final.io_events.map IOEvent.name = ffi.io_events.map IOEvent.name ++ [name] := by
  simp [call_FFI,named] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  simp

/-- A returning named foreign call appends exactly one observation and cannot
return directly from its enclosing Pancake function. -/
theorem extCall_trace (name : String) (named : name ≠ "") (a b c d : PExp) :
    CommandTrace (.extCall name a b c d) [name] := by
  intro θ s
  rw [evaluate_eq_step]
  simp only [evaluateStep]
  split
  · split
    · split
      · rename_i final output good
        exact ⟨fun _ => ffi_events named good,by simp⟩
      · simp
    · simp
  · simp

theorem positive_return_trace {θ} (s f : PanState θ) (c : PStmt) (g : PExp) (names : List String)
    (w : Word) (positive : w ≠ 0) (contract : CommandTrace c names)
    (run : evaluate (.seq c (.ret g)) s = (.ret (.word w),f)) : events f = events s ++ names := by
  rw [evaluate_seq] at run
  dsimp only at run
  split at run
  next norm =>
    have recorded := (contract s).1 (eq_of_beq norm)
    rw [evaluate_ret] at run
    repeat' split at run <;> try contradiction
    all_goals cases run <;> exact recorded
  next => exact False.elim (positive ((contract s).2 w (congrArg Prod.fst run)))

end Obend.Lower.Pancake
