/-
# The closure tooth: Kimi's seven-row graph (KIMI-REVIEW-20261030, "The journal closure omits
reachable dependencies")

`R` cites `[A,B,C,D,Z]`, each of `A..D` cites only `X`, `X` and `Z` cite nothing. The closure the
journal shipped before 2026-10-30 (`oldClosureBy` below, its definition with the hash set and the
export abstracted) spent one unit of its `rows + seeds + 1 = 9` fuel on every pop, the three
repeat pops of `X` included, and returned with `Z` still on its stack. The kernel evaluates both
walks here by `decide`, on the list visited set (`String.hash` is opaque to it); `Journal.walk`
is the same function the journal runs on `hashVisit`.

`teeth.sh` (c) runs this file: `lake env lean tools/journal/ClosureTooth.lean`.
-/
import Journal.Journal

namespace Journal.ClosureTooth

open Journal

/-- The closure as it was (`Journal.lean` before the fix), over any visited set and edge function:
fuel `size + seeds.length + 1`, one unit per pop. -/
def oldClosureBy {α σ : Type} (V : VisitSet α σ) (edges : α → List α) (size : Nat)
    (seeds : List α) : List α :=
  let rec go (fuel : Nat) (stack : List α) (seen : σ) (acc : List α) : List α :=
    match fuel, stack with
    | 0, _ => acc.reverse
    | _, [] => acc.reverse
    | fuel + 1, n :: rest =>
      if V.contains seen n then go fuel rest seen acc
      else go fuel (edges n ++ rest) (V.insert seen n) (n :: acc)
  go (size + seeds.length + 1) seeds V.empty []

def kimi : List (String × List String) :=
  [("R", ["A", "B", "C", "D", "Z"]), ("A", ["X"]), ("B", ["X"]), ("C", ["X"]), ("D", ["X"]),
   ("X", []), ("Z", [])]

def edges (n : String) : List String := (kimi.lookup n).getD []

/-- Every edge target, with repetition: the bound `closure` computes as `E.targets.length`. -/
def targets : List String := kimi.flatMap (·.2)

def oldClosure : List String := oldClosureBy (listVisit String) edges kimi.length ["R"]
def newClosure : List String := closureBy (listVisit String) edges targets.length ["R"]

theorem reach_Z : Reach edges ["R"] "Z" := .step (n := "R") (.seed (by simp)) (by decide)

/-- The completeness statement, `Reach → ∈`, at this graph. -/
def Complete (cl : List String) : Prop := ∀ x, Reach edges ["R"] x → x ∈ cl

/-- The old closure fails it: `Z` is one edge from the seed and not in the closure. -/
theorem old_refuted : ¬ Complete oldClosure := by
  intro h
  have := h "Z" reach_Z
  revert this
  decide

/-- What the old walk returned, by the kernel. -/
example : oldClosure = ["R", "A", "X", "B", "C", "D"] := by decide

/-- The new walk, by the kernel: all seven rows, in depth-first preorder. -/
example : newClosure = ["R", "A", "X", "B", "C", "D", "Z"] := by decide

theorem lookup_sub (g : List (String × List String)) (n m : String)
    (h : m ∈ (g.lookup n).getD []) : m ∈ g.flatMap (·.2) := by
  induction g with
  | nil => simp at h
  | cons p g ih =>
    simp only [List.lookup] at h
    split at h
    · exact List.mem_flatMap.2 ⟨p, by simp, by simpa using h⟩
    · exact List.mem_flatMap.2 ((List.mem_flatMap.1 (ih h)).imp fun q hq => ⟨by simp [hq.1], hq.2⟩)

/-- The new closure passes: by `mem_closureBy_iff`, every edge target being in `targets`... -/
theorem new_complete : Complete newClosure := fun x hx =>
  (mem_closureBy_iff (listVisit String) edges targets.length ["R"] targets
    (fun n m hm => lookup_sub kimi n m hm) (Nat.le_refl _) x).2 hx

/-- ...and, independently of the theorem, `Z` is in it by `decide`. -/
example : "Z" ∈ newClosure := by decide

/-- info: 'Journal.mem_closure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Journal.mem_closure_iff

/-- info: 'Journal.ClosureTooth.old_refuted' depends on axioms: [propext] -/
#guard_msgs in #print axioms old_refuted

/-- info: 'Journal.ClosureTooth.new_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms new_complete

end Journal.ClosureTooth
