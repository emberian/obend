module
/-
# Obend.Analysis.Replay — the fold replayed under an amended law

`review/WORLD-ANALYSIS-20261101.md` §2.2 (T3). Two admissions over the same rows from the same root
agree until the first row their steps judge differently (`replay_divergence`): before it the two
folds are equal, at it they differ, and after it the counterfactual history is another history (the
refused write never happened), so a replay reports the first divergence and does not continue as if
it had. When the amended law only refuses more (`Narrows`), the divergence is a write it refuses
(`amend_refuses`).

On a vault (`vaultReplay`): every write of every page the amended page's laws judge (the page
itself, and the pages it is a kind of) is re-judged by `Obend.Vault.commit`, once with the laws in
force and once with the amended page in their place, replayed as the owner at the write's version;
the first write the two judge differently is reported with the amended verdict.
-/
public import Obend.Analysis.Worlds
@[expose] public section

namespace Obend.Analysis

open Obend.Fold

set_option autoImplicit false

section
variable {W Rest Row Fact Clause : Type}

/-- **T3, the first divergence**: two admissions run over the same rows from the same root give the
same fold, or there is a first row their steps judge differently, at an accumulator both reached. -/
theorem replay_divergence (A A' : Admission W Rest Row Fact Clause) :
    ∀ (rows : List Row) (a : W × Rest), A.run a rows = A'.run a rows ∨
      ∃ pre r post b, rows = pre ++ r :: post ∧ A.run a pre = .ok b ∧ A'.run a pre = .ok b ∧
        A.step b r ≠ A'.step b r
  | [], _ => .inl rfl
  | r :: rs, a => by
    by_cases hs : A.step a r = A'.step a r
    · cases hst : A.step a r with
      | error e =>
        refine .inl ?_
        simp only [Admission.run, List.foldlM_cons, ← hs, hst]; rfl
      | ok b =>
        rcases replay_divergence A A' rs b with h | ⟨pre, r', post, b', he, h1, h2, hd⟩
        · refine .inl ?_
          simp only [Admission.run, List.foldlM_cons, ← hs, hst] at h ⊢
          exact h
        · refine .inr ⟨r :: pre, r', post, b', by rw [he]; rfl, ?_, ?_, hd⟩
          · simp only [Admission.run, List.foldlM_cons, hst] at h1 ⊢; exact h1
          · simp only [Admission.run, List.foldlM_cons, ← hs, hst] at h2 ⊢; exact h2
    · exact .inr ⟨[], r, rs, a, rfl, rfl, rfl, hs⟩

/-- The amended admission only refuses more. -/
def Narrows (A A' : Admission W Rest Row Fact Clause) : Prop :=
  ∀ b r x, A'.step b r = .ok x → A.step b r = .ok x

/-- **An amendment that narrows diverges by a refusal.** -/
theorem amend_refuses (A A' : Admission W Rest Row Fact Clause) (hn : Narrows A A') {b : W × Rest} {r : Row}
    (hd : A.step b r ≠ A'.step b r) : ∃ k, A'.step b r = .error k := by
  cases h : A'.step b r with
  | error k => exact ⟨k, rfl⟩
  | ok x => exact absurd (by rw [hn b r x h, h]) hd

end

namespace VaultWorld

open Obend.Doc Obend.Vault

/-- How one write is judged on replay. -/
def judgeWrite (es : List Entry) (p : Page) (i : Nat) (env : Environment := #[]) : Option (Except String Unit) :=
  p.history[i]?.map fun G =>
    (commit es { p with history := p.history.take i } G [] .owner i (env := env)).map fun _ => ()

def sameVerdict : Except String Unit → Except String Unit → Bool
  | .ok _, .ok _ => true
  | .error a, .error b => a == b
  | _, _ => false

/-- A page's replay: the writes judged alike, then the first the two laws judge differently (its
version, the verdict in force, the amended one). -/
structure PageReplay where
  page : String
  agreed : Nat
  divergence : Option (Nat × Except String Unit × Except String Unit)

/-- Replay one page's writes under the laws in force (`es`) and the amended ones (`es'`). -/
def replayPage (es es' : List Entry) (p : Page) (env : Environment := #[]) : PageReplay :=
  let rec go (i : Nat) (fuel : Nat) : PageReplay :=
    match fuel with
    | 0 => ⟨p.name, i, none⟩
    | fuel + 1 =>
      match judgeWrite es p i env, judgeWrite es' p i env with
      | some v, some v' => if sameVerdict v v' then go (i + 1) fuel else ⟨p.name, i, some (i + 1, v, v')⟩
      | _, _ => ⟨p.name, i, none⟩
  go 0 (p.history.length + 1)

/-- The pages a page's laws judge: itself, and every page it is a kind of. -/
def judgedBy (s : Store) (k : String) : List Page :=
  s.pages.filter fun p => p.name == k || match p.current with
    | some G => (kindChain s.entries p.name (settled G)).contains k
    | none => false

/-- **Replay a vault under an amended page**: the page's new version (the owner's write of `md`,
judged as any write), then every write of every page its laws judge, under both. -/
def replay (s : Store) (k : String) (md : String) : Except String (List PageReplay) := do
  let some p := s.page? k | throw ("no page named " ++ k)
  let ch := ownerWrite Obend.Vault.Cli.H s.entries s.turn p md (env := s.environment)
  if let some n := ch.note then throw ("the amendment itself is refused: " ++ n)
  let some G' := ch.history.getLast? | throw (k ++ " has no version")
  let es := s.entries
  let es' := es.map fun e => if e.name == k then { e with graph := G' } else e
  return (judgedBy s k).map fun p => replayPage es es' p s.environment

end VaultWorld

end Obend.Analysis

end
