module
/-
# Obend.Ledger.Vault — the register's law is its kind's, judged by the vault's judge

In a vault the register is the folder `register/`, and its kind page `register/_kind.md` carries the
register's laws as `law NAME: EXPR` lines of the `.obend` law fragment, like any kind's
(`Obend.Vault.Law`). A posting is judged by those lines as the birth of its page: `kindLaw` builds
the posting's state (its totals, lines and period, `postingMeasures`, then every account's debits and
credits in the register after it, `accountMeasures`: `Cash_credits <= Cash_debits` is a law a
register may carry) and runs the vault's `judge` on it. So the law the register's fold calls
(`Obend.Ledger.Register.Law`) is the vault's, and the refusal is the vault's, naming the kind and
the clause.

`kindLaw_balanced`: when the kind's laws include `new.debits == new.credits` (under any name), every
posting `kindLaw` admits is balanced. With `Obend.Ledger.Register.conserved` and `reach_balanced`,
the register a vault keeps is balanced and conserved because its kind page says so.
-/
public import Obend.Ledger.Register
public import Obend.Vault.Law
@[expose] public section

namespace Obend.Ledger

set_option autoImplicit false

open Obend.Vault
open Obend.Spec.Law (LawExpr LawRef Facts fieldOf firstScalarField scalarOf)

/-- What the register's laws read of a posting first: its totals, its number of lines, its period,
and version 0 (a posting is born once). -/
def postingMeasures (p : Posting) : List (String × Nat) :=
  [("credits", p.credits), ("debits", p.debits), ("movements", p.lines.length), ("period", p.period), ("version", 0)]

/-- An account's short name: its page name's last part (`accounts/Cash` is `Cash`). -/
def shortName (a : String) : String := ((a.splitOn "/").getLast?).getD a

/-- The register's totals with the posting added: every account's debits and credits. -/
def totalsAfter (g : Reg) (p : Posting) : Totals := addPosting (g.postings.foldl addPosting []) p

/-- What the register's laws read of the register: for every account it has moved, with the
posting, `NAME_debits` and `NAME_credits`, its totals after the posting (NAME its short name). -/
def accountMeasures (g : Reg) (p : Posting) : List (String × Nat) :=
  (totalsAfter g p).flatMap fun (a, d, c) => [(shortName a ++ "_debits", d), (shortName a ++ "_credits", c)]

/-- The facts a posting is judged under: the owner posts. -/
def postFacts : Facts := ⟨some 0, some 0, 0, 0⟩

/-- The state of a posting, over its measures and the fields its laws read. -/
def postingKeys (lin : List (String × LawExpr)) (vals : List (String × Nat)) : List String :=
  sortNames (vals.map (·.1) ++ lin.flatMap fun l => l.2.fields)

/-- **The register's kind law, on a posting at a register**: its laws judged by the vault's judge as
the birth of the posting's page, over the posting's measures and the register's account totals after
it. -/
def kindLaw (lin : List (String × LawExpr)) : Law := fun g p =>
  let vals := postingMeasures p ++ accountMeasures g p
  let keys := postingKeys lin vals
  let st := stateOf keys vals
  match judge (stateTy keys) "register" lin st st (requestOf "owner" .birth postFacts) with
  | .admitted => none
  | .refused n r => some (n, r)
  | .undecided w => some ("undecided", w)

theorem mem_insertName (k x : String) : ∀ l : List String, x ∈ insertName k l ↔ x = k ∨ x ∈ l
  | [] => by simp [insertName]
  | y :: ys => by
    simp only [insertName]
    split
    · rename_i h
      have : k = y := by simpa using h
      subst this; simp
    · split
      · simp
      · simp only [List.mem_cons, mem_insertName k x ys]
        exact or_left_comm

theorem mem_sortNames (x : String) : ∀ ks : List String, x ∈ sortNames ks ↔ x ∈ ks
  | [] => by simp [sortNames]
  | k :: ks => by
    show x ∈ insertName k (sortNames ks) ↔ _
    rw [mem_insertName, mem_sortNames x ks]
    simp

theorem fieldOf_stateOf (vals : List (String × Nat)) (k : String) :
    ∀ keys : List String, k ∈ keys → fieldOf k (stateOf keys vals) = some (((vals.lookup k).getD 0 : Nat) : Int)
  | [], h => by cases h
  | y :: ys, h => by
    simp only [stateOf, fieldOf, List.map_cons, firstScalarField]
    by_cases e : y = k
    · subst e; simp [scalarOf]
    · simp only [e, ite_false]
      have : k ∈ ys := (List.mem_cons.1 h).resolve_left (Ne.symm e)
      exact fieldOf_stateOf vals k ys this

/-- **What the register's kind admits is balanced** when its laws say `new.debits == new.credits`. -/
theorem kindLaw_balanced (lin : List (String × LawExpr))
    (hb : ∃ name, (name, LawExpr.eqR (.field "debits") (.field "credits")) ∈ lin) (g : Reg) (p : Posting)
    (h : kindLaw lin g p = none) : p.debits = p.credits := by
  obtain ⟨name, hmem⟩ := hb
  simp only [kindLaw] at h
  split at h
  · rename_i hj
    have hall := judge_admits (k := .birth) (who := "owner") (facts := postFacts) hj
    have hd := hall _ hmem
    simp only [LawExpr.denote, LawRef.read] at hd
    have hkd : "debits" ∈ postingKeys lin (postingMeasures p ++ accountMeasures g p) := by
      rw [postingKeys, mem_sortNames]; simp [postingMeasures]
    have hkc : "credits" ∈ postingKeys lin (postingMeasures p ++ accountMeasures g p) := by
      rw [postingKeys, mem_sortNames]; simp [postingMeasures]
    rw [fieldOf_stateOf _ _ _ hkd, fieldOf_stateOf _ _ _ hkc] at hd
    simp [postingMeasures, List.lookup] at hd
    exact_mod_cast hd
  · cases h
  · cases h

/-- A kind's laws hold of a register's postings: every posting of a register reached from the empty
one under the kind's law that says it is balanced, is balanced, and the register is conserved. -/
theorem vault_conserved (lin : List (String × LawExpr))
    (hb : ∃ name, (name, LawExpr.eqR (.field "debits") (.field "credits")) ∈ lin) {rows : List Row}
    {w : Nat} {b : Nat × Reg} (h : runFrom (kindLaw lin) (w, ⟨[]⟩) rows = .ok b) :
    b.2.debits = b.2.credits :=
  conserved (fun g p hp => kindLaw_balanced lin hb g p hp) h

end Obend.Ledger

end
