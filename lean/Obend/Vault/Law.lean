module
/-
# Obend.Vault.Law — a page's `law:` lines, judged on every write

A page's frontmatter line `law NAME: EXPR` (or `law: EXPR`, named `law`) is a law of the `.obend`
fragment (`Obend.Spec.Law`: comparisons of `new.FIELD` and `request.FACT`, `monotone`, `writeOnce`,
`and`/`or`/`not`/`implies`). The state it reads is the page's (`Obend.Vault.Page.measures`: its
measures and its frontmatter's scalar fields), every field a natural, every field any law reads
present (at 0 where the page does not have it).

A folder's `_kind.md` is a KIND (the kind cell, `Obend.Kind`): its law lines are laws of every page
born under it, and its `key: value` lines the fields such a page starts with. A page carries its
kind's identity in its frontmatter (`kind: K`, written by `obend create --from K`); a page that names
none is an instance of its folder's kind and each enclosing folder's. The laws a write is judged by
are the page's own, then its kind's, then the kind's ancestors' (`Obend.Vault.kindChain`; the C4
precedence list of a chain is the chain), each compiled by
`Obend.Spec.LawCompile.compile` for the page's state type and combined by `Obend.Law.effective`: one
closed Core4 term, run by Core4's reference step (`Obend.Law.run`). A refusal names the law that
refused, the page or kind that wrote it, and (`suggest`) the change of one field that would pass, or
says that none does.

What is proved, for every list of laws, state type, pair of states and request: the vault's
`judge` ADMITS a write only when every law on the list holds of it by the fragment's meaning
(`judge_admits`), and when it REFUSES naming a law, that law is on the list and does not hold
(`judge_refuses`), at a write, a birth and an adoption alike.
-/
public import Obend.Vault.Page
public import Obend.Spec.Proofs.LawCompile
public import Obend.Law.Proofs.Inherit
public import Obend.Law.Proofs.Run
@[expose] public section

namespace Obend.Vault

set_option autoImplicit false

open Obend.Law Obend.Spec.LawCompile
open Obend.Spec.Law (LawExpr Facts)
open Obend.Core.Term (Term Evaluates)
open Obend.Core.Ty (Ty)
open Obend.Core.Data (Data)

/-! ## The state a law reads -/

/-- Insert into a sorted list of names. -/
def insertName (k : String) : List String → List String
  | [] => [k]
  | x :: xs => if k == x then x :: xs else if decide (k < x) then k :: x :: xs else x :: insertName k xs

/-- The names, sorted, without repeats. -/
def sortNames (ks : List String) : List String := ks.foldr insertName []

/-- The state type of a page: a record of naturals at the names `keys`. -/
def stateTy (keys : List String) : Ty := keys.foldr (fun k t => .field k .natural t) .emptyRow

/-- A page's state as data: each name its value, or 0. -/
def stateOf (keys : List String) (vals : List (String × Nat)) : Data :=
  .record (keys.map fun k => (k, .natural ((vals.lookup k).getD 0)))

/-! ## The occasions a page write is judged on -/

/-- A write of an existing page, the birth of a new one, or the adoption of changed laws over the
page as written (judged as the identity write, `compile_adopt`). -/
inductive Occ
  | write
  | birth
  | adopt
deriving DecidableEq, Repr

def Occ.data : Occ → Data
  | .write => writeO
  | .birth => birthO
  | .adopt => adoptO "page"

/-- The old state the fragment's meaning takes at an occasion. -/
def Occ.old (k : Occ) (o n : Data) : Option Data :=
  match k with
  | .write => some o
  | .birth => none
  | .adopt => some n

/-- The request of a page write: who signs (a member's name, or `owner`), the version it makes, the
turn. -/
def requestOf (who : String) (k : Occ) (facts : Facts) : Data := reqOf who who 0 0 k.data facts

/-! ## The judge -/

/-- What the vault says of a write. -/
inductive Verdict
  | admitted
  | refused (law reason : String)
  | undecided (why : String)
deriving DecidableEq, Repr

/-- The verdict a run of the effective law reached. -/
def readVerdict : Option Term → Verdict
  | some (.inject "ok" _) => .admitted
  | some (.inject "refused" (.record [("by", .label b), ("reason", .label r)])) => .refused b r
  | _ => .undecided "the law did not finish within its fuel"

/-- Steps a law may take. -/
def lawFuel : Nat := 200000

/-- The laws, compiled for the state type `S`, the page named `pkg`. -/
def compiled (S : Ty) (pkg : String) (lin : List (String × LawExpr)) : List (String × Term) :=
  lin.map fun p => (p.1, compile S pkg p.1 p.2)

/-- **The judge.** Every law on the list (in precedence order) compiled and combined by `effective`,
run on the old and new states and the request. A state that does not fit a law, or a compiled law
that is not closed, is undecided, never admitted. -/
def judge (S : Ty) (pkg : String) (lin : List (String × LawExpr)) (o n rq : Data) : Verdict :=
  if lin.all (fun p => Fits S p.2 o && Fits S p.2 n) then
    if (compiled S pkg lin).all (fun p => closedB p.2) then
      readVerdict (run lawFuel (applyLaw (effective (compiled S pkg lin)) o n rq))
    else .undecided "a compiled law is not closed"
  else .undecided "the page state does not fit a law"

theorem readVerdict_admitted {r : Option Term} (h : readVerdict r = .admitted) :
    ∃ w, r = some (.inject "ok" w) := by
  unfold readVerdict at h
  split at h <;> first | (exact ⟨_, rfl⟩) | (cases h)

theorem readVerdict_refused {r : Option Term} {b why : String} (h : readVerdict r = .refused b why) :
    r = some (.inject "refused" (.record [("by", .label b), ("reason", .label why)])) := by
  unfold readVerdict at h
  split at h <;> first | (cases h; rfl) | cases h

/-- The compiled law, at each occasion, evaluates to the verdict the fragment's meaning gives. -/
theorem compile_occ {S : Ty} {pkg name : String} {e : LawExpr} {o n : Data} {facts : Facts}
    {who : String} (k : Occ) (hfo : Fits S e o = true) (hfn : Fits S e n = true) :
    Evaluates (applyLaw (compile S pkg name e) o n (requestOf who k facts))
      (verdictOf name (e.denote facts (k.old o n) n)) := by
  cases k
  · exact compile_change (Or.inl ⟨_, rfl⟩) hfo hfn
  · exact compile_birth hfn
  · exact compile_adopt hfn

theorem mem_compiled {S : Ty} {pkg : String} {lin : List (String × LawExpr)} {name : String} {L : Term}
    (h : (name, L) ∈ compiled S pkg lin) : ∃ e, (name, e) ∈ lin ∧ L = compile S pkg name e := by
  obtain ⟨⟨nm, e⟩, hm, he⟩ := List.mem_map.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨e, hm, rfl⟩

/-- **What the vault admits, every law holds of.** If the judge admits a write (a write, a birth or an
adoption), every law on the list holds of it by the fragment's meaning. -/
theorem judge_admits {S : Ty} {pkg : String} {lin : List (String × LawExpr)} {o n : Data}
    {facts : Facts} {who : String} {k : Occ}
    (h : judge S pkg lin o n (requestOf who k facts) = .admitted) :
    ∀ p ∈ lin, p.2.denote facts (k.old o n) n = true := by
  unfold judge at h
  split at h
  · rename_i hfit
    split at h
    · rename_i hcl
      obtain ⟨w, hr⟩ := readVerdict_admitted h
      have hev := run_sound _ hr
      have hall := (effective_law_eval (fun p hp => by simpa using List.all_eq_true.1 hcl p hp) _ _ _).1
        ⟨w, hev⟩
      intro p hp
      have hf := List.all_eq_true.1 hfit p hp
      simp only [Bool.and_eq_true] at hf
      have hadm := hall (p.1, compile S pkg p.1 p.2) (List.mem_map.2 ⟨p, hp, rfl⟩)
      obtain ⟨w', hw'⟩ := hadm
      have := Obend.Law.evaluates_unique hw' (compile_occ (who := who) (facts := facts) (pkg := pkg) (name := p.1) k hf.1 hf.2)
      cases hd : p.2.denote facts (k.old o n) n
      · rw [hd] at this; simp [verdictOf, refusedT] at this
      · rfl
    · cases h
  · cases h

/-- **A refusal names a law that does not hold.** If the judge refuses a write naming `b`, then `b` is a
law on the list, every law before it holds, and `b` does not. -/
theorem judge_refuses {S : Ty} {pkg : String} {lin : List (String × LawExpr)} {o n : Data}
    {facts : Facts} {who : String} {k : Occ} {b why : String}
    (h : judge S pkg lin o n (requestOf who k facts) = .refused b why) :
    ∃ e, (b, e) ∈ lin ∧ e.denote facts (k.old o n) n = false := by
  unfold judge at h
  split at h
  · rename_i hfit
    split at h
    · rename_i hcl
      have hr := readVerdict_refused h
      have hev := run_sound _ hr
      have hclosed : ∀ p ∈ compiled S pkg lin, closedB p.2 = true := fun p hp => by
        simpa using List.all_eq_true.1 hcl p hp
      obtain ⟨pre, name, L, post, why', hlin, _, hL, hby⟩ := effective_refusal_names hclosed hev
      have heq := Obend.Law.evaluates_unique hev hby
      simp only [blamed, Term.inject.injEq, Term.record.injEq, List.cons.injEq, Prod.mk.injEq,
        Term.label.injEq, and_true, true_and] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hmem : (b, L) ∈ compiled S pkg lin := by rw [hlin]; simp
      obtain ⟨e, he, rfl⟩ := mem_compiled hmem
      refine ⟨e, he, ?_⟩
      have hf := List.all_eq_true.1 hfit (b, e) he
      simp only [Bool.and_eq_true] at hf
      have hv := compile_occ (who := who) (facts := facts) (pkg := pkg) (name := b) k hf.1 hf.2
      have := Obend.Law.evaluates_unique hL hv
      cases hd : e.denote facts (k.old o n) n
      · rfl
      · rw [hd] at this; simp [verdictOf, okT] at this
    · cases h
  · cases h


/-! ## What would pass -/

/-- A natural field of a state. -/
def natAt (d : Data) (f : String) : Nat :=
  match d with
  | .record fs => match fs.lookup f with
    | some (.natural v) => v
    | _ => 0
  | _ => 0

/-- A state with one field set. -/
def setNat (d : Data) (f : String) (v : Nat) : Data :=
  match d with
  | .record fs => .record (fs.map fun (k, x) => if k == f then (k, .natural v) else (k, x))
  | other => other

/-- The constants a law mentions. -/
def lawConsts : LawExpr → List Int
  | .eqC _ v | .leC _ v => [v]
  | .inC _ vs => vs
  | .leROff _ _ k => [k]
  | .eqR .. | .leR .. | .monotone _ | .writeOnce _ => []
  | .not e => lawConsts e
  | .and l r | .or l r | .implies l r => lawConsts l ++ lawConsts r

/-- The values tried for a field: near what it is, near what it was, near the law's constants. -/
def candidates (e : LawExpr) (cur old : Nat) : List Nat :=
  let near (v : Nat) : List Nat := [v, v + 1, v - 1]
  let cs : List Nat := ((lawConsts e).filter (0 ≤ ·)).map Int.toNat
  let dist (v : Nat) : Nat := if v ≤ cur then cur - v else v - cur
  ((near old ++ cs.flatMap near ++ [0, cur + 1, cur - 1]).eraseDups.filter (· != cur)).mergeSort
    fun a b => dist a ≤ dist b

/-- **What would pass**: the change of one field the law reads that makes it hold, said as the line
of frontmatter that would pass (for a field the page writes there) or as the measure that would
pass; else a request from the owner, if that passes; else that nothing near does. -/
def suggest (e : LawExpr) (facts : Facts) (old : Option Data) (new : Data) (front : List String) : String :=
  let fields := e.fields.eraseDups
  let found := fields.findSome? fun f =>
    let cur := natAt new f
    let was := (old.map (natAt · f)).getD cur
    ((candidates e cur was).find? fun v => e.denote facts (old.map fun o => o) (setNat new f v)).map
      fun v => (f, cur, v)
  match found with
  | some (f, cur, v) =>
    if front.contains f then
      "the line `" ++ f ++ ": " ++ toString v ++ "` would pass (the page has `" ++ f ++ ": " ++ toString cur ++ "`)"
    else f ++ " = " ++ toString v ++ " would pass (this write has " ++ f ++ " = " ++ toString cur ++ ")"
  | none =>
    if e.denote { facts with caller := some 0, subject := some 0 } old new then
      "the same write by the owner would pass"
    else "no change of one field passes"

end Obend.Vault

end
