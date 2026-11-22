module
/-
# Obend.Judge.Instances — the existing judges, as `Judge` instances

Each instance takes its `sound`/`complete` fields from theorems that already exist; nothing about
the checkers is re-proved here. Where a judge had no executable checker (the protocol envelope),
one is written and proved against the existing relation.

| judge | object | certificate | `sound` from | `complete` from, on |
|---|---|---|---|---|
| bidirectional checker | context, term, type | annotations | `checkAgainst_sound`, `reannotates_typed` | `full_annotated`, every typed term |
| law machine probe | law, old, new, request | none | `judge_sound`, `refusesAs_not_admits` | `judge_complete`, closed laws |
| `coerce` | assumptions, source, target | the emitted coercion | `checkAgainst_sound` | `coerce_checks`, where the emitter succeeds |
| C4 linearization | graph, head, parents | none | `precedence_ok` | `precedence_tree`, acyclic trees |
| protocol envelope | tokens, protocol | none | `checkProt_sound` (new) | `checkProt_complete` (new), every judgment |

The law probe is iteratively deepened (`Judge.deepen`) along a ladder of machine resources, so its
grade is monotone with no fuel-monotonicity theorem for the machine; `judged_unique` makes the
first answer the relation's.

What each judge refutes (a refusal after which no certificate can mean the object):

| judge | refuting clause | because |
|---|---|---|
| bidirectional checker, `coerce` | `TypingClause.invalidAssumptions` | every `Checked` carries `Assumptions.valid`; the judge decides it before the checker runs |
| law machine probe | `refused` | `refusesAs_not_admits` |
| C4 linearization | `inconsistent _ "no C3 candidate"` | `precedence_noCandidate`: a precedence list would order the candidates, so the merge could not stop |
| protocol envelope | `untyped` | `checkProt_complete` |

A refusal by the checker itself (`TypingClause.checker`) is about the certificate offered, and
refutes nothing: other annotations may be accepted.
-/
public import Obend.Judge.Class
public import Obend.Slot.Core4
public import Obend.Law.Proofs.Machine
public import Obend.Law.Proofs.Inherit
public import Obend.Elab.Coerce
public import Obend.Slot.Proofs.Protocol
import all Obend.Spec.C4
import all Obend.Spec.Proofs.C4
import Obend.Tactic.Tooth

public section
namespace Obend.Judge.Instances
open Obend.Core
set_option autoImplicit false

/-! ## The bidirectional checker: the certificate is the annotations -/

section Bidirectional
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional

/-- Where a refusal applies. -/
def CheckRefusal.path : CheckRefusal → List Nat
  | .unboundVariable p _ | .missingLambdaAnnotation p | .missingAnnotation p | .emptyCaseInSynthMode p
  | .typeMismatch p _ _ | .shapeMismatch p _ _ | .unknownLabel p _ _ | .duplicateLabels p
  | .binderOverused p _ _ _ | .linearBinderUnused p | .linearArgumentDropped p _ _ | .linearBranchesDisagree p _
  | .linearProjected p _ | .linearMetadata p _ | .linearOverwritten p _ | .linearScrutinee p
  | .capturesNotShareable p | .notShareable p _ | .activityMisplaced p _ | .fieldDropped p _
  | .invalidContext p => p
  | .invalidAssumptions => []
  | .undeclaredHole p _ | .holeArity p _ _ _ => p

/-- Why a typing judge refuses. `invalidAssumptions` is the judge's own premise, decided on the
object before the checker runs: it does not depend on the certificate. A `checker` refusal is the
checker's, on the certificate that was offered. The two are kept apart by the type, so that the
first can be a refutation without a theorem about every refusal the elaborator may report. -/
inductive TypingClause where
  /-- the term's assumptions are not valid (`Assumptions.valid`): no certificate is accepted -/
  | invalidAssumptions
  /-- the checker refused the term under the certificate offered -/
  | checker (refusal : CheckRefusal)
  deriving DecidableEq, Repr

/-- The checker's answer as a verdict: refusals keep the checker's clause and path. -/
def ofExcept {α : Type} : Except CheckRefusal α → Verdict TypingClause
  | .ok _ => .ok
  | .error e => .refused (.checker e) (CheckRefusal.path e)

theorem ofExcept_ok {α : Type} {x : Except CheckRefusal α} (h : ofExcept x = .ok) : ∃ a, x = .ok a := by
  cases x with
  | ok a => exact ⟨a, rfl⟩
  | error e => simp [ofExcept] at h

/-- The checker never reports the judge's own premise. -/
theorem ofExcept_ne_invalidAssumptions {α : Type} {x : Except CheckRefusal α} {p : List Nat} :
    ofExcept x ≠ .refused .invalidAssumptions p := by
  cases x with
  | ok a => simp [ofExcept]
  | error e => simp [ofExcept]

/-- A term whose assumptions are not valid has no `Checked` certificate, under any annotations. -/
theorem not_checked_of_invalid {Ψ : Context} {t : AnnotatedTerm} (h : t.assumptions.valid = false)
    (c : Checked t Ψ) : False := by
  have hv := c.assumptionsValid
  rw [h] at hv
  cases hv

/-- The checker on a term with the certificate's annotations, within a work grant. The term's
assumptions are decided first: when they are not valid the term has no typing at all. -/
def bidiCheck (r : Nat) (o : Context × AnnotatedTerm × Ty) (ann : Annotations) : Verdict TypingClause :=
  let u : AnnotatedTerm := { o.2.1 with annotations := ann }
  if Obend.Slot.Core4.checkWork u ≤ r then
    if o.2.1.assumptions.valid then ofExcept (checkAgainst u o.1 o.2.2)
    else .refused .invalidAssumptions []
  else .uncovered

/-- **`invalidAssumptions` is about the term alone**: the judge reports it only when the term's
assumptions are not valid, whatever the annotations offered. -/
theorem bidiCheck_invalidAssumptions {r : Nat} {o : Context × AnnotatedTerm × Ty} {ann : Annotations}
    {p : List Nat} (h : bidiCheck r o ann = .refused .invalidAssumptions p) :
    o.2.1.assumptions.valid = false := by
  simp only [bidiCheck] at h
  split at h
  · split at h
    · exact absurd h ofExcept_ne_invalidAssumptions
    · rename_i hv; exact Bool.eq_false_iff.2 hv
  · cases h

/-- The refusal is reached: within the grant, invalid assumptions are refused by that clause. -/
theorem bidiCheck_of_invalid {r : Nat} {o : Context × AnnotatedTerm × Ty} {ann : Annotations}
    (hw : Obend.Slot.Core4.checkWork { o.2.1 with annotations := ann } ≤ r)
    (hv : o.2.1.assumptions.valid = false) : bidiCheck r o ann = .refused .invalidAssumptions [] := by
  simp only [bidiCheck]
  split
  · split
    · rename_i hv'; rw [hv] at hv'; cases hv'
    · rfl
  · rename_i hw'; exact absurd hw hw'

/-- **The bidirectional checker** (`Obend.Core.Bidirectional.checkAgainst`, bounded by
`checkWork` as `Obend.Slot.Core4.judge` is). -/
instance bidirectional : Judge (Context × AnnotatedTerm × Ty) Annotations where
  Clause := TypingClause
  Meaning o _ := ∃ c : Checked o.2.1 o.1, c.type = o.2.2
  check := bidiCheck
  sound := by
    rintro r ⟨Ψ, t, A⟩ ann h
    simp only [bidiCheck] at h
    split at h
    · split at h
      · obtain ⟨c, hc⟩ := ofExcept_ok h
        have typed : Obend.Slot.Core4.Typed Ψ { t with annotations := ann } A :=
          ⟨c, (checkAgainst_sound hc).1⟩
        exact Obend.Slot.Core4.reannotates_typed (t := { t with annotations := ann }) (u := t) ⟨rfl, rfl⟩ typed
      · cases h
    · cases h
  refutes
    | .invalidAssumptions => true
    | _ => false
  refuted := by
    intro r o ann k p h hk ann' hm
    obtain ⟨c, _⟩ := hm
    cases k with
    | checker e => cases hk
    | invalidAssumptions => exact not_checked_of_invalid (bidiCheck_invalidAssumptions h) c
  Fragment _ := True
  complete := by
    rintro ⟨Ψ, t, A⟩ _ ⟨_, c, same⟩
    obtain ⟨annotations, checked, accepted⟩ :=
      Obend.Core.Proofs.BidirectionalCompleteness.full_annotated c
    have valid : t.assumptions.valid = true := c.assumptionsValid
    refine ⟨annotations, Obend.Slot.Core4.checkWork { t with annotations := annotations }, ?_⟩
    rw [same] at accepted
    dsimp only at accepted
    simp only [bidiCheck, Nat.le_refl, ↓reduceIte]
    rw [accepted]
    simp [valid, ofExcept]
  mono := by
    intro r r' o ann le hne
    simp only [bidiCheck] at hne ⊢
    split at hne
    · rename_i h; simp only [h, Nat.le_trans h le, ↓reduceIte]
    · exact absurd rfl hne

/-- **The slot's judge is this judge's check**: `Core4.judge` at a grant accepts a term exactly when
the bidirectional judge accepts it with its own annotations as the certificate. -/
theorem judge_iff_check (r : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) :
    Obend.Slot.Core4.judge r Ψ t A = true ↔ bidirectional.check r (Ψ, t, A) t.annotations = .ok := by
  show _ ↔ bidiCheck r (Ψ, t, A) t.annotations = .ok
  rcases t with ⟨term, ann, asm⟩
  simp only [Obend.Slot.Core4.judge, bidiCheck]
  by_cases w : Obend.Slot.Core4.checkWork ⟨term, ann, asm⟩ ≤ r
  · cases h : checkAgainst ⟨term, ann, asm⟩ Ψ A with
    | error e => by_cases valid : asm.valid = true <;> simp [w, valid, ofExcept, Except.toBool]
    | ok c =>
      have valid : asm.valid = true := c.assumptionsValid
      simp [w, valid, ofExcept, Except.toBool]
  · simp [w]

/-- Object extension is accepted by the typing judge at grant 4 (`Core4.extend_filling_admitted`). -/
theorem extend_filling_decided :
    bidirectional.check 4 (([] : Context), Obend.Slot.Core4.extendFilling, Obend.Slot.Core4.extendType)
      Obend.Slot.Core4.extendFilling.annotations = .ok :=
  (judge_iff_check _ _ _ _).1 Obend.Slot.Core4.extend_filling_admitted

/-- A term under assumptions that declare a shareable variable with no bound is refuted at every
type: no annotations make it typed. -/
example (Ψ : Context) (t : AnnotatedTerm) (A : Ty) (ann : Annotations) :
    ¬ bidirectional.Meaning (Ψ, { t with assumptions := { shareableVariables := [0] } }, A) ann :=
  bidirectional.refuted (c := t.annotations) (k := .invalidAssumptions) (p := [])
    (bidiCheck_of_invalid (o := (Ψ, { t with assumptions := { shareableVariables := [0] } }, A))
      (Nat.le_refl _) (by decide : ({ shareableVariables := [0] } : Assumptions).valid = false))
    rfl ann

#tooth bidiCheck_invalidAssumptions by mutation bidiCheck := fun _ _ _ => .refused .invalidAssumptions []

end Bidirectional

/-! ## The law machine probe, iteratively deepened -/

section Law
open Obend.Core.Term (Term)
open Obend.Core.Data (Data)
open Obend.Law

/-- A write to judge: the law, the old state, the new state, the request. -/
structure LawProblem where
  law : Term
  old : Data
  new : Data
  req : Data

inductive LawClause where
  /-- the law has a free index -/
  | openLaw
  /-- the law refused, with this reason -/
  | refused (why : String)
  deriving DecidableEq, Repr

/-- The `k`-th rung of machine resources. -/
def rungLimits (k : Nat) : Obend.Core.Machine.Limits := ⟨k, k⟩
def rungBudget (k : Nat) : Obend.Core.Data.Budget := ⟨k + 1, k, k⟩

/-- The probe at rung `k`. -/
def probeAt (p : LawProblem) (k : Nat) : Option Obend.Law.Verdict :=
  judge (fun _ => true) (rungLimits k) (rungBudget k) p.law p.old p.new p.req

def lawCheck (k : Nat) (p : LawProblem) (_ : Unit) : Judge.Verdict LawClause :=
  if closedB p.law then
    match Judge.deepen (probeAt p) k with
    | some .ok => .ok
    | some (.refused why) => .refused (.refused why) []
    | none => .uncovered
  else .refused .openLaw []

theorem lawCheck_judged {k : Nat} {p : LawProblem} {v : Obend.Law.Verdict} (closed : closedB p.law = true)
    (h : Judge.deepen (probeAt p) k = some v) : Judged p.law p.old p.new p.req v := by
  obtain ⟨i, _, hi⟩ := Judge.deepen_some _ h
  exact judge_sound closed hi

/-- **The law machine probe**: `ok` is `Admits`; a refusal by the law refutes it. -/
instance lawProbe : Judge LawProblem Unit where
  Clause := LawClause
  Meaning p _ := Admits p.law p.old p.new p.req
  check := lawCheck
  sound := by
    intro k p _ h
    simp only [lawCheck] at h
    split at h
    · rename_i closed
      split at h
      · rename_i hd; exact lawCheck_judged closed hd
      · cases h
      · cases h
    · cases h
  refutes
    | .refused _ => true
    | .openLaw => false
  refuted := by
    intro k p _ c path h hk _
    simp only [lawCheck] at h
    split at h
    · rename_i closed
      split at h
      · cases h
      · rename_i why hd
        cases h
        exact refusesAs_not_admits (lawCheck_judged closed hd)
      · cases h
    · cases h; cases hk
  Fragment p := closedB p.law = true
  complete := by
    intro p closed ⟨_, adm⟩
    obtain ⟨limits₀, ticks₀, hrun⟩ := judge_complete (v := Obend.Law.Verdict.ok) closed adm
    let K := limits₀.heap + limits₀.stack + ticks₀ + Obend.Core.Proofs.GroundExecution.groundBytes Obend.Law.Verdict.ok.obs
    have hK : probeAt p K = some .ok :=
      hrun (rungLimits K) (rungBudget K) ⟨by simp only [rungLimits, K]; omega, by simp only [rungLimits, K]; omega⟩
        (by simp only [rungBudget, K]; omega) (by simp only [rungBudget]; omega) (by simp only [rungBudget, K]; omega)
    obtain ⟨b, hb⟩ := Judge.deepen_isSome (probeAt p) hK
    have hj := lawCheck_judged closed hb
    have : b = Obend.Law.Verdict.ok := judged_unique hj adm
    subst this
    exact ⟨(), K, by simp [lawCheck, closed, hb]⟩
  mono := by
    intro k k' p _ le hne
    unfold lawCheck at hne ⊢
    by_cases closed : closedB p.law = true
    · simp only [closed, ↓reduceIte] at hne ⊢
      cases hd : Judge.deepen (probeAt p) k with
      | none => rw [hd] at hne; exact absurd rfl hne
      | some v => rw [Judge.deepen_mono _ hd le]
    · simp [closed]

end Law

/-! ## `coerce`: the certificate is the emitted coercion -/

section Coerce
open Obend.Core.Ty Obend.Core.Check Obend.Core.Bidirectional Obend.Elab.Coerce
open Obend.Core.Proofs.BidirectionalCompleteness (treeAnnotations)

/-- The emitted coercion as an annotated closed term. -/
def Emitted.source (a : Assumptions) (e : Emitted) : AnnotatedTerm := ⟨e.term, treeAnnotations e.tree, a⟩

def coerceCheck (r : Nat) (o : Assumptions × Ty × Ty) (e : Emitted) : Verdict TypingClause :=
  if Obend.Slot.Core4.checkWork (Emitted.source o.1 e) ≤ r then
    if o.1.valid then ofExcept (checkAgainst (Emitted.source o.1 e) [] (e.type o.2.1 o.2.2))
    else .refused .invalidAssumptions []
  else .uncovered

/-- **`invalidAssumptions` is about the assumptions alone**: `coerce`'s judge reports it only when
they are not valid, whatever coercion was offered. -/
theorem coerceCheck_invalidAssumptions {r : Nat} {o : Assumptions × Ty × Ty} {e : Emitted} {p : List Nat}
    (h : coerceCheck r o e = .refused .invalidAssumptions p) : o.1.valid = false := by
  simp only [coerceCheck] at h
  split at h
  · split at h
    · exact absurd h ofExcept_ne_invalidAssumptions
    · rename_i hv; exact Bool.eq_false_iff.2 hv
  · cases h

/-- The refusal is reached: within the grant, invalid assumptions are refused by that clause. -/
theorem coerceCheck_of_invalid {r : Nat} {o : Assumptions × Ty × Ty} {e : Emitted}
    (hw : Obend.Slot.Core4.checkWork (Emitted.source o.1 e) ≤ r) (hv : o.1.valid = false) :
    coerceCheck r o e = .refused .invalidAssumptions [] := by
  simp only [coerceCheck]
  split
  · split
    · rename_i hv'; rw [hv] at hv'; cases hv'
    · rfl
  · rename_i hw'; exact absurd hw hw'

/-- **`coerce`**: the producer is the emitter, the checker re-runs the bidirectional checker on
what it emitted. Assumptions that are not valid are refuted before the checker runs. -/
instance coercion : Judge (Assumptions × Ty × Ty) Emitted where
  Clause := TypingClause
  Meaning o e := ∃ c : Checked (Emitted.source o.1 e) [], c.type = e.type o.2.1 o.2.2
  check := coerceCheck
  sound := by
    rintro r ⟨a, s, t⟩ e h
    simp only [coerceCheck] at h
    split at h
    · split at h
      · obtain ⟨c, hc⟩ := ofExcept_ok h
        exact ⟨c, (checkAgainst_sound hc).1⟩
      · cases h
    · cases h
  refutes
    | .invalidAssumptions => true
    | _ => false
  refuted := by
    intro r o e k p h hk e' hm
    obtain ⟨c, _⟩ := hm
    cases k with
    | checker refusal => cases hk
    | invalidAssumptions =>
      exact not_checked_of_invalid (t := Emitted.source o.1 e') (coerceCheck_invalidAssumptions h) c
  Fragment o := ∃ c, coerce o.1 o.2.1 o.2.2 = .ok c
  complete := by
    rintro ⟨a, s, t⟩ ⟨c, hc⟩ _
    obtain ⟨checked, accepted⟩ := coerce_checks hc
    have valid : a.valid = true := checked.assumptionsValid
    refine ⟨c.emitted, Obend.Slot.Core4.checkWork (Emitted.source a c.emitted), ?_⟩
    simp only [coerceCheck, Nat.le_refl, ↓reduceIte, Emitted.type]
    simp only [Emitted.source]; rw [accepted]
    simp [valid, ofExcept]
  mono := by
    intro r r' o e le hne
    simp only [coerceCheck] at hne ⊢
    split at hne
    · rename_i h; simp only [h, Nat.le_trans h le, ↓reduceIte]
    · exact absurd rfl hne

/-- No coercion is typed under assumptions that declare a shareable variable with no bound. -/
example (source target : Ty) (e : Emitted) :
    ¬ coercion.Meaning (({ shareableVariables := [0] } : Assumptions), source, target) e :=
  coercion.refuted (c := e) (k := .invalidAssumptions) (p := [])
    (coerceCheck_of_invalid (o := (({ shareableVariables := [0] } : Assumptions), source, target))
      (Nat.le_refl _) (by decide : ({ shareableVariables := [0] } : Assumptions).valid = false))
    rfl e

#tooth coerceCheck_invalidAssumptions by mutation coerceCheck := fun _ _ _ => .refused .invalidAssumptions []

end Coerce

/-! ## C4's checked linearization -/

section C4
open Obend.Law
open Obend.Spec.C4

def c4Check (_ : Nat) (o : Obend.Spec.C4.Graph × String × List (List String)) (_ : Unit) : Verdict InheritRefusal :=
  match precedence o.1 o.2.1 o.2.2 with
  | .ok _ => .ok
  | .error e => .refused e []

/-- What a precedence list is (Barrett et al. 1996), as `precedence_ok` states it. -/
def PrecedenceList (g : Obend.Spec.C4.Graph) (head : String) (parents : List (List String)) (lin : List String) : Prop :=
  lin.head? = some head ∧ lin.Nodup ∧ (∀ chain ∈ parents, chain.Sublist lin) ∧
    ∀ chain ∈ parents, ∀ p ∈ chain, (g.precedence p).Sublist lin

/-! ### The C3 merge cannot stop while a precedence list exists

`linearize` reports `"no C3 candidate"` from one place: the merge, with candidates left and no head
eligible. Every candidate is a prefix of a parent's precedence list or of a local chain, so a
precedence list would contain each as a sublist; and candidates with a common duplicate-free order
always have an eligible head. -/

/-- A name at the front of a duplicate-free list is in the tail of none of its sublists. -/
theorem not_mem_tail_of_sublist_cons {z : String} {rest l : List String} (hz : z ∉ rest)
    (h : l.Sublist (z :: rest)) : z ∉ l.tail := by
  intro hm
  rcases List.sublist_cons_iff.1 h with h' | ⟨r, rfl, h'⟩
  · exact hz (h'.subset (List.mem_of_mem_tail hm))
  · exact hz (h'.subset hm)

/-- **C3 progress** (Barrett et al. 1996). Candidates that are all sublists of one duplicate-free
list, and not all exhausted, have a next head: the first name of that list heading a candidate is
in no candidate's tail. -/
theorem nextHead_of_common_order (lin : List String) (ls : List (List String)) (hnd : lin.Nodup)
    (hsub : ∀ l ∈ ls, l.Sublist lin) (hne : ls.all List.isEmpty = false) :
    ∃ c, nextHead ls = some c := by
  induction lin with
  | nil =>
    have hall : ls.all List.isEmpty = true :=
      List.all_eq_true.2 fun l hl => by rw [List.sublist_nil.1 (hsub l hl)]; rfl
    rw [hall] at hne; cases hne
  | cons z rest ih =>
    obtain ⟨hz, hrest⟩ := List.nodup_cons.1 hnd
    cases hh : ls.any (fun l => l.head? == some z) with
    | true =>
      obtain ⟨l, hl, hlz⟩ := List.any_eq_true.1 hh
      cases l with
      | nil => simp at hlz
      | cons y t =>
        have hy : y = z := by simpa using hlz
        subst hy
        cases hn : nextHead ls with
        | some c => exact ⟨c, rfl⟩
        | none =>
          exfalso
          unfold nextHead at hn
          have hf := List.findSome?_eq_none_iff.1 hn (y :: t) hl
          simp only at hf
          split at hf
          · rename_i hany
            obtain ⟨l', hl', hc⟩ := List.any_eq_true.1 hany
            exact not_mem_tail_of_sublist_cons hz (hsub l' hl') (by simpa using hc)
          · cases hf
    | false =>
      refine ih hrest fun l hl => ?_
      rcases List.sublist_cons_iff.1 (hsub l hl) with h | ⟨r, rfl, _⟩
      · exact h
      · have hno := List.any_eq_false.1 hh _ hl
        simp at hno

theorem popOne_sublist (c : String) (l : List String) : (popOne c l).Sublist l := by
  rcases popOne_cases c l with ⟨t, rfl, he⟩ | he
  · rw [he]; exact List.sublist_cons_self c t
  · rw [he]; exact List.Sublist.refl _

/-- The merge of candidates that share a duplicate-free order never runs out of C3 candidates. -/
theorem mergeN_candidate {head lin : List String} (hnd : lin.Nodup) (n : Nat) (ls : List (List String))
    (hsub : ∀ l ∈ ls, l.Sublist lin) {h : List String} {detail : String}
    (he : mergeN head n ls = .error (.inconsistent h detail)) : detail ≠ "no C3 candidate" := by
  induction n generalizing ls with
  | zero =>
    unfold mergeN at he
    split at he
    · cases he
    · simp only [inconsistent, Except.error.injEq, Refusal.inconsistent.injEq] at he
      rw [← he.2]; decide
  | succ n ih =>
    unfold mergeN at he
    split at he
    · cases he
    · rename_i hall
      split at he
      · rename_i hnone
        obtain ⟨c, hc⟩ := nextHead_of_common_order lin ls hnd hsub (Bool.eq_false_iff.2 hall)
        rw [hnone] at hc; cases hc
      · rename_i c _
        split at he
        · cases he
        · rename_i e hm
          cases he
          refine ih (pop c ls) (fun l hl => ?_) hm
          obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
          exact (popOne_sublist c l₀).trans (hsub l₀ hl₀)

theorem suffix_detail_ne (a b : String) :
    "suffix incompatibility: " ++ a ++ " is not on the suffix chain of " ++ b ≠ "no C3 candidate" := by
  intro h
  have hlen := congrArg String.length h
  simp only [String.length_append] at hlen
  have h1 : "suffix incompatibility: ".length = 24 := by decide
  have h2 : "no C3 candidate".length = 15 := by decide
  omega

/-- A refusal of the suffix tail is never the C3 merge's. -/
theorem tailOf_detail (g : Graph) (head : List String) (ps acc : List String) {h : List String}
    {detail : String} (he : tailOf g head acc ps = .error (.inconsistent h detail)) :
    detail ≠ "no C3 candidate" := by
  induction ps generalizing acc with
  | nil => simp [tailOf] at he
  | cons p ps ih =>
    simp only [tailOf] at he
    split at he
    · exact ih _ he
    · simp only [inconsistent, Except.error.injEq, Refusal.inconsistent.injEq] at he
      rw [← he.2]; exact suffix_detail_ne _ _

/-- **No C3 candidate, no precedence list** (Barrett et al. 1996). When the C3 merge stops with
candidates left and none eligible, no list starts at `head`, repeats nothing and keeps every local
chain and every parent's precedence list in order: such a list would order the candidates, and its
first name heading a candidate would be eligible (`nextHead_of_common_order`). -/
theorem precedence_noCandidate {g : Graph} {head : String} {parents : List (List String)}
    {h : List String} {detail : String}
    (he : precedence g head parents = .error (.c4 (.inconsistent h detail)))
    (hd : detail = "no C3 candidate") (lin : List String) : ¬ PrecedenceList g head parents lin := by
  rintro ⟨_, hnd, hlocal, hmono⟩
  unfold precedence at he
  split at he
  · cases he
  · rename_i e hlin
    cases he
    unfold linearize at hlin
    simp only at hlin
    split at hlin
    · rename_i e' htail
      cases hlin
      exact tailOf_detail g _ _ _ htail hd
    · rename_i tail htail
      split at hlin
      · simp only [inconsistent, Except.error.injEq, Refusal.inconsistent.injEq] at hlin
        rw [← hlin.2] at hd; revert hd; decide
      · rename_i cands hc
        split at hlin
        · split at hlin
          · cases hlin
          · rename_i e' hm
            cases hlin
            refine mergeN_candidate hnd _ cands (fun c hcm => ?_) hm hd
            obtain ⟨l, hl, r, hlr, _⟩ := (cleanAll_spec hc).2 c hcm
            have hl' : l.Sublist lin := by
              rcases List.mem_append.1 hl with hp | hp
              · obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hp
                obtain ⟨chain, hch, hpc⟩ := List.mem_flatten.1 hpm
                exact hmono chain hch p hpc
              · exact hlocal l hp
            rw [hlr] at hl'
            exact (List.sublist_append_left c r).trans hl'
        · simp only [inconsistent, Except.error.injEq, Refusal.inconsistent.injEq] at hlin
          rw [← hlin.2] at hd; revert hd; decide

/-- **C4's validated linearization**: `ok` means there exists a topological, duplicate-free,
local-order- and parent-monotonicity-preserving C4 precedence list starting at `head`. A refusal
for want of a C3 candidate means there is none (`precedence_noCandidate`). -/
instance c4 : Judge (Obend.Spec.C4.Graph × String × List (List String)) Unit where
  Clause := InheritRefusal
  Meaning o _ := ∃ lin, PrecedenceList o.1 o.2.1 o.2.2 lin
  check := c4Check
  sound := by
    rintro r ⟨g, head, parents⟩ _ h
    simp only [c4Check] at h
    split at h
    · rename_i lin hl; exact ⟨lin, precedence_ok hl⟩
    · cases h
  refutes
    | .c4 (.inconsistent _ detail) => detail == "no C3 candidate"
    | _ => false
  refuted := by
    rintro r ⟨g, head, parents⟩ _ k p h hk _ ⟨lin, hlin⟩
    simp only [c4Check] at h
    split at h
    · cases h
    · rename_i e he
      injection h with hke _
      subst hke
      cases e with
      | unknownLaw name => cases hk
      | openLaw name => cases hk
      | c4 refusal =>
        cases refusal with
        | inconsistent at_ detail =>
          exact precedence_noCandidate he (by simpa using hk) lin hlin
  Fragment o := ∃ (t : Tree) (n : Nat), o.1 = t.graph n ∧ o.2.2 = t.parents o.2.1 ∧ (t.chain (n + 1) o.2.1).Nodup
  complete := by
    rintro ⟨g, x, parents⟩ ⟨t, n, hg, hp, acyclic⟩ _
    simp only at hg hp acyclic
    subst hg hp
    exact ⟨(), 0, by simp [c4Check, precedence_tree t n x acyclic]⟩
  mono := by intros; rfl

/-- Unrelated names, each its own precedence list, none a suffix node. -/
def flatGraph : Obend.Spec.C4.Graph := ⟨fun x => [x], fun _ => false⟩

/-- One local chain is linearized. -/
example : c4.check 0 (flatGraph, "x", [["a", "b"]]) () = .ok := by rfl

/-- Two local chains in opposite orders are refuted: no precedence list keeps both. -/
example : ¬ ∃ lin, PrecedenceList flatGraph "x" [["a", "b"], ["b", "a"]] lin :=
  c4.refuted (r := 0) (o := (flatGraph, "x", [["a", "b"], ["b", "a"]])) (c := ())
    (k := .c4 (.inconsistent ["x"] "no C3 candidate")) (p := []) (by rfl) (by decide) ()

#tooth precedence_noCandidate by mutation Obend.Spec.C4.nextHead := fun _ => none

end C4

/-! ## The protocol envelope: `HasProt`, decided on a finite signature -/

section Protocol
open Obend.Slot.Protocol
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type} {Tok Fact Ob : Type}

/-- What the envelope judge is given: a finite signature, results and indices listed, the result
predicate as a Boolean, and each hole's declared post as one. -/
structure Envelope (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Tok Fact Ob : Type) where
  fin : Finite S
  ixs : List Ix
  ixs_complete : ∀ j, j ∈ ixs
  res : (j : Ix) → List (A j)
  res_complete : ∀ j a, a ∈ res j
  sp : Spec S Tok Fact Ob
  Ω : Ctx S Hole A Tok Fact Ob
  Γ : List Fact
  Qb : (j : Ix) → A j → Bool
  Φ : List Ob
  postB : (i : Ix) → Hole i → (j : Ix) → A j → Bool
  post_iff : ∀ i h I, Ω i h = some I → ∀ j a, I.post j a ↔ postB i h j a = true

@[expose] def subBagB [DecidableEq Tok] (Δ₁ Δ₂ : List Tok) : Bool := Δ₁.all fun t => Δ₁.count t ≤ Δ₂.count t

theorem subBagB_iff [DecidableEq Tok] (Δ₁ Δ₂ : List Tok) : subBagB Δ₁ Δ₂ = true ↔ SubBag Δ₁ Δ₂ := by
  unfold subBagB SubBag
  constructor
  · intro h t
    by_cases ht : t ∈ Δ₁
    · simpa using List.all_eq_true.1 h t ht
    · rw [List.count_eq_zero_of_not_mem ht]; exact Nat.zero_le _
  · intro h; exact List.all_eq_true.2 fun t _ => by simpa using h t

/-- The hole's declared post implies the result predicate, over every index and result. -/
@[expose] def Envelope.entails (E : Envelope S Hole A Tok Fact Ob) (i : Ix) (h : Hole i) : Bool :=
  E.ixs.all fun j => (E.res j).all fun a => !E.postB i h j a || E.Qb j a

theorem Envelope.entails_iff (E : Envelope S Hole A Tok Fact Ob) {i : Ix} {h : Hole i}
    {I : Iface S Hole A Tok Fact Ob i} (hI : E.Ω i h = some I) :
    E.entails i h = true ↔ ∀ j a, I.post j a → E.Qb j a = true := by
  unfold Envelope.entails
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro H j a hp
    rcases H j (E.ixs_complete j) a (E.res_complete j a) with h' | h'
    · rw [(E.post_iff i h I hI j a).1 hp] at h'; cases h'
    · exact h'
  · intro H j _ a _
    cases hb : E.postB i h j a
    · exact .inl rfl
    · exact .inr (H j a ((E.post_iff i h I hI j a).2 hb))

/-- The envelope check. -/
@[expose] def checkProt [DecidableEq Tok] [DecidableEq Fact] [DecidableEq Ob] (E : Envelope S Hole A Tok Fact Ob) : (Δ : List Tok) → {i : Ix} → Prot S Hole A i → Bool
  | _, _, .ret a => E.Qb _ a
  | Δ, _, .call op k =>
    (E.sp.requires op).all (· ∈ E.Γ) && (E.sp.establishes op).all (· ∈ E.Φ) &&
      match E.sp.consumes op with
      | none => (E.fin.resps op).all fun r => checkProt E Δ (k r)
      | some t => decide (t ∈ Δ) && (E.fin.resps op).all fun r => checkProt E (Δ.erase t) (k r)
  | Δ, i, .hole h =>
    match E.Ω i h with
    | none => false
    | some I => I.chooser == .me && I.ctx.all (· ∈ E.Γ) && subBagB I.need Δ && E.entails i h &&
        I.owes.all (· ∈ E.Φ)

/-- The envelope's judgment, with the result predicate the Boolean's. -/
abbrev Envelope.Typed [DecidableEq Tok] (E : Envelope S Hole A Tok Fact Ob) (Δ : List Tok) {i : Ix} (P : Prot S Hole A i) : Prop :=
  HasProt E.sp E.Ω E.Γ (fun j a => E.Qb j a = true) E.Φ Δ P

theorem checkProt_sound [DecidableEq Tok] [DecidableEq Fact] [DecidableEq Ob] (E : Envelope S Hole A Tok Fact Ob) :
    ∀ (Δ : List Tok) {i : Ix} (P : Prot S Hole A i), checkProt E Δ P = true → E.Typed Δ P
  | _, _, .ret a, h => .ret a h
  | Δ, _, .call op k, h => by
    simp only [checkProt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hreq, hest⟩, hk⟩ := h
    cases hc : E.sp.consumes op with
    | none =>
      rw [hc] at hk
      simp only [List.all_eq_true] at hk
      exact .call op k hc hreq hest fun r => checkProt_sound E Δ (k r) (hk r (E.fin.complete op r))
    | some t =>
      rw [hc] at hk
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk
      exact .spend op k t hc hk.1 hreq hest fun r => checkProt_sound E _ (k r) (hk.2 r (E.fin.complete op r))
  | Δ, i, .hole h, hc => by
    simp only [checkProt] at hc
    split at hc
    · cases hc
    · rename_i I hI
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨hme, hctx⟩, hneed⟩, hent⟩, howes⟩ := hc
      exact .hole h I hI hme hctx ((subBagB_iff _ _).1 hneed) ((E.entails_iff hI).1 hent) howes

theorem checkProt_complete [DecidableEq Tok] [DecidableEq Fact] [DecidableEq Ob] (E : Envelope S Hole A Tok Fact Ob) {Δ : List Tok} {i : Ix} {P : Prot S Hole A i}
    (h : E.Typed Δ P) : checkProt E Δ P = true := by
  induction h with
  | ret a hq => exact hq
  | call op k hc hreq hest _ ih =>
    simp only [checkProt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, hc]
    exact ⟨⟨hreq, hest⟩, fun r _ => ih r⟩
  | spend op k t hc ht hreq hest _ ih =>
    simp only [checkProt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, hc]
    exact ⟨⟨hreq, hest⟩, ht, fun r _ => ih r⟩
  | hole h I hI hme hctx hneed hpost howes =>
    simp only [checkProt, hI, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨hme, hctx⟩, (subBagB_iff _ _).2 hneed⟩, (E.entails_iff hI).2 hpost⟩, howes⟩

/-- A protocol to judge: the tokens available and the protocol at its index. -/
structure ProtObj (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Tok : Type) where
  Δ : List Tok
  i : Ix
  P : Prot S Hole A i

inductive EnvelopeClause where
  | untyped
  deriving DecidableEq, Repr

/-- **The protocol envelope** over an `Envelope`: decided, so a refusal refutes. The meaning is
`HasProt`; its consequences are `hasProt_runs`, `hasProt_reach` and `started_obligations`. -/
abbrev envelope [DecidableEq Tok] [DecidableEq Fact] [DecidableEq Ob] (E : Envelope S Hole A Tok Fact Ob) : Judge (ProtObj S Hole A Tok) Unit where
  Clause := EnvelopeClause
  Meaning o _ := E.Typed o.Δ o.P
  check _ o _ := if checkProt E o.Δ o.P then .ok else .refused .untyped []
  sound := by
    intro _ o _ h
    by_cases hc : checkProt E o.Δ o.P = true
    · exact checkProt_sound E o.Δ o.P hc
    · simp [hc] at h
  refutes _ := true
  refuted := by
    intro _ o _ _ _ h _ _ ht
    have := checkProt_complete E ht
    simp [this] at h
  Fragment _ := True
  complete := by
    intro o _ ⟨_, ht⟩
    exact ⟨(), 0, by simp [checkProt_complete E ht]⟩
  mono := by intros; rfl

end Protocol

end Obend.Judge.Instances
end
