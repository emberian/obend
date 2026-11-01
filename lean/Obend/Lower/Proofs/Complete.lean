module
/-
# Obend.Lower.Proofs.Complete — Converse Simulation (`lower_complete`) and the `.erased` Boundary

1. **Refutation of untyped `lower_complete` (`raw_lower_complete_refuted`)**:
   - Because `lowerT .erased = box = .record []`, eliminating `.erased` as a 0-field structure
     (`erasedElim := .split [] (.lit 42) .erased`, corresponding to `@True.rec (fun _ => Nat) 42 h`)
     evaluates in 1 step to `.nat 42` in `Core4` (`erasedElim_evaluates_in_core4`), whereas it is
     stuck in the source semantics `SStep` (`erasedElim_stuck_in_source`).
   - This proves that `lower_complete` requires the fragment's sort/typing discipline (`Fragment`
     excluding `Prop`-to-`Type` recursors, and `CanonicalNat` / `CanonicalBool` on closed fragment
     terms).

2. **Verified `lower_complete_nat`, `lower_complete_bool`, and Bi-Simulation (`lower_iff_nat`, `lower_iff_bool`)**:
   - For any source term `e` satisfying `CanonicalNat e` (`∃ m, SSteps e (.lit m)`), `lower_sound_nat`
     combined with `Core4` determinism (`evaluates_unique`) yields `Evaluates (lowerT e) (.nat n) → SSteps e (.lit n)`.
   - Likewise for `Bool` (`lower_complete_bool`, `lower_iff_bool`), which is the exact bridge needed by
     `Obend.Lower.Transport`.
-/
public import Obend.Lower.Proofs.Sound
public import Obend.Lower.Typing
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term
set_option autoImplicit false

/-! ## 1. The `.erased` / `box` Boundary: Why Untyped `lower_complete` is Refuted -/

/-- Eliminating `.erased` as a 0-field record (`@True.rec (fun _ => Nat) 42 h`). -/
def erasedElim : LExpr := .split [] (.lit 42) .erased

/-- In `Core4`, `lowerT erasedElim = .split (.record []) [] (.nat 42)` steps to `.nat 42`. -/
theorem erasedElim_evaluates_in_core4 : Evaluates (lowerT erasedElim) (.nat 42) := by
  simp only [erasedElim, lowerT, box]
  exact ⟨.next (.splitRecord [] [] (.nat 42) [] rfl) (.refl _), .natural 42⟩

/-- In the source semantics `SStep`, `erasedElim` is stuck because `.erased` is not `.record []`. -/
theorem erasedElim_stuck_in_source : ¬ SSteps erasedElim (.lit 42) := by
  intro h
  cases h with
  | next s _ =>
    cases s with
    | splitMajor _ _ sm => cases sm

/-- **Refutation of raw untyped `lower_complete`**: without excluding `.erased` from computational
record/inductive elimination, `Evaluates (lowerT e) (.nat n)` does not imply `SSteps e (.lit n)`. -/
theorem raw_lower_complete_refuted :
    ¬ ∀ (e : LExpr) (n : Nat), Evaluates (lowerT e) (.nat n) → SSteps e (.lit n) := by
  intro h
  exact erasedElim_stuck_in_source (h erasedElim 42 erasedElim_evaluates_in_core4)

/-! ## 2. `lower_complete` and Exact Bi-Simulation under Source Canonicity -/

/-- A closed source term of type `Nat` reduces to some canonical `Nat` literal. -/
def CanonicalNat (e : LExpr) : Prop := ∃ m : Nat, SSteps e (.lit m)

/-- A closed source term of type `Bool` reduces to some canonical `Bool` literal. -/
def CanonicalBool (e : LExpr) : Prop := ∃ b : Bool, SSteps e (.boolLit b)

/-- **`lower_complete` at `Nat`**: if `e` is a canonical `Nat` term in the source fragment and
`lowerT e` evaluates to `.nat n` in `Core4`, then `e` reduces to `.lit n` in `SSteps`. -/
theorem lower_complete_nat {e : LExpr} {n : Nat}
    (hcan : CanonicalNat e) (hev : Evaluates (lowerT e) (.nat n)) :
    SSteps e (.lit n) := by
  obtain ⟨m, hm⟩ := hcan
  have hevm : Evaluates (lowerT e) (.nat m) := by simpa [lowerT] using lower_sound_nat hm
  have heq := evaluates_unique hevm hev
  cases heq
  exact hm

/-- **`lower_complete` at `Bool`**: if `e` is a canonical `Bool` term in the source fragment and
`lowerT e` evaluates to `.boolean b` in `Core4`, then `e` reduces to `.boolLit b` in `SSteps`. -/
theorem lower_complete_bool {e : LExpr} {b : Bool}
    (hcan : CanonicalBool e) (hev : Evaluates (lowerT e) (.boolean b)) :
    SSteps e (.boolLit b) := by
  obtain ⟨b', hb'⟩ := hcan
  have hevb' : Evaluates (lowerT e) (.boolean b') := by simpa [lowerT] using lower_sound_bool hb'
  have heq := evaluates_unique hevb' hev
  cases heq
  exact hb'

/-- **Exact `Nat` Bi-Simulation (`lower_iff_nat`)**: on canonical source terms, `Core4` evaluation
to `.nat n` and source reduction to `.lit n` coincide. -/
theorem lower_iff_nat {e : LExpr} {n : Nat} (hcan : CanonicalNat e) :
    Evaluates (lowerT e) (.nat n) ↔ SSteps e (.lit n) :=
  ⟨lower_complete_nat hcan, fun h => by simpa [lowerT] using lower_sound_nat h⟩

/-- **Exact `Bool` Bi-Simulation (`lower_iff_bool`)**: on canonical source terms, `Core4` evaluation
to `.boolean b` and source reduction to `.boolLit b` coincide. -/
theorem lower_iff_bool {e : LExpr} {b : Bool} (hcan : CanonicalBool e) :
    Evaluates (lowerT e) (.boolean b) ↔ SSteps e (.boolLit b) :=
  ⟨lower_complete_bool hcan, fun h => by simpa [lowerT] using lower_sound_bool h⟩

/-! ## 3. Structural Closure of `CanonicalNat` and `CanonicalBool` -/

theorem ssteps_trans {a b c : LExpr} (h1 : SSteps a b) (h2 : SSteps b c) : SSteps a c := by
  induction h1 with
  | refl => exact h2
  | next s _ ih => exact .next s (ih h2)

theorem ssteps_congr {a b : LExpr} (f : LExpr → LExpr)
    (hf : ∀ {x y : LExpr}, SStep x y → SStep (f x) (f y)) (h : SSteps a b) :
    SSteps (f a) (f b) := by
  induction h with
  | refl => exact .refl _
  | next s _ ih => exact .next (hf s) ih

theorem canonicalNat_lit (n : Nat) : CanonicalNat (.lit n) := ⟨n, .refl _⟩

theorem canonicalBool_lit (b : Bool) : CanonicalBool (.boolLit b) := ⟨b, .refl _⟩

theorem canonicalNat_const (name : String) {b : LExpr} (hb : CanonicalNat b) :
    CanonicalNat (.const name b) := by
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, .next (.delta name b) hn⟩

theorem canonicalBool_const (name : String) {b : LExpr} (hb : CanonicalBool b) :
    CanonicalBool (.const name b) := by
  obtain ⟨v, hv⟩ := hb
  exact ⟨v, .next (.delta name b) hv⟩

theorem canonicalNat_succ {a : LExpr} (ha : CanonicalNat a) : CanonicalNat (.natSucc a) := by
  obtain ⟨n, hn⟩ := ha
  exact ⟨n + 1, ssteps_trans (ssteps_congr .natSucc .succArg hn) (.next (.succFold n) (.refl _))⟩

theorem canonicalNat_bin (op : NatOp) (hop : op.resultTy = .natural)
    {l r : LExpr} (hl : CanonicalNat l) (hr : CanonicalNat r) :
    CanonicalNat (.natBin op l r) := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hr
  have s1 := ssteps_congr (fun x => .natBin op x r) (fun s => .binLeft op r s) ha
  have s2 := ssteps_congr (fun y => .natBin op (.lit a) y) (fun s => .binRight op a s) hb
  cases op <;> simp [NatOp.resultTy] at hop
  · exact ⟨a + b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .add a b) (.refl _)))⟩
  · exact ⟨a - b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .sub a b) (.refl _)))⟩
  · exact ⟨a * b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .mul a b) (.refl _)))⟩
  · exact ⟨a / b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .div a b) (.refl _)))⟩
  · exact ⟨a % b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .mod a b) (.refl _)))⟩

theorem canonicalBool_bin (op : NatOp) (hop : op.resultTy = .boolean)
    {l r : LExpr} (hl : CanonicalNat l) (hr : CanonicalNat r) :
    CanonicalBool (.natBin op l r) := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hr
  have s1 := ssteps_congr (fun x => .natBin op x r) (fun s => .binLeft op r s) ha
  have s2 := ssteps_congr (fun y => .natBin op (.lit a) y) (fun s => .binRight op a s) hb
  cases op <;> simp [NatOp.resultTy] at hop
  · exact ⟨a == b, ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .beq a b) (.refl _)))⟩
  · exact ⟨decide (a ≤ b), ssteps_trans s1 (ssteps_trans s2 (.next (.binLit .ble a b) (.refl _)))⟩

end Obend.Lower
end
