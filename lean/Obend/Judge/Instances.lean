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
-/
public import Obend.Judge.Class
public import Obend.Slot.Core4
public import Obend.Law.Proofs.Machine
public import Obend.Law.Proofs.Inherit
public import Obend.Elab.Coerce
public import Obend.Slot.Proofs.Protocol

@[expose] public section
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
  | .affineBinderOverused p _ _ | .linearBinderUnused p | .linearArgumentDropped p _ _ | .linearBranchesDisagree p _
  | .linearProjected p _ | .capturesNotShareable p | .notShareable p _ | .activityMisplaced p _
  | .invalidContext p => p
  | .invalidAssumptions => []

/-- The checker's answer as a verdict: refusals keep the checker's clause and path. -/
def ofExcept {α : Type} : Except CheckRefusal α → Verdict CheckRefusal
  | .ok _ => .ok
  | .error e => .refused e (CheckRefusal.path e)

theorem ofExcept_ok {α : Type} {x : Except CheckRefusal α} (h : ofExcept x = .ok) : ∃ a, x = .ok a := by
  cases x with
  | ok a => exact ⟨a, rfl⟩
  | error e => simp [ofExcept] at h

/-- The checker on a term with the certificate's annotations, within a work grant. -/
def bidiCheck (r : Nat) (o : Context × AnnotatedTerm × Ty) (ann : Annotations) : Verdict CheckRefusal :=
  let u : AnnotatedTerm := { o.2.1 with annotations := ann }
  if Obend.Slot.Core4.checkWork u ≤ r then ofExcept (checkAgainst u o.1 o.2.2) else .uncovered

/-- **The bidirectional checker** (`Obend.Core.Bidirectional.checkAgainst`, bounded by
`checkWork` as `Obend.Slot.Core4.judge` is). -/
instance bidirectional : Judge (Context × AnnotatedTerm × Ty) Annotations where
  Clause := CheckRefusal
  Meaning o _ := ∃ c : Checked o.2.1 o.1, c.type = o.2.2
  check := bidiCheck
  sound := by
    rintro r ⟨Ψ, t, A⟩ ann h
    simp only [bidiCheck] at h
    split at h
    · obtain ⟨c, hc⟩ := ofExcept_ok h
      have typed : Obend.Slot.Core4.Typed Ψ { t with annotations := ann } A :=
        ⟨c, (checkAgainst_sound hc).1⟩
      exact Obend.Slot.Core4.reannotates_typed (t := { t with annotations := ann }) (u := t) ⟨rfl, rfl⟩ typed
    · cases h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment _ := True
  complete := by
    rintro ⟨Ψ, t, A⟩ _ ⟨_, c, same⟩
    obtain ⟨annotations, checked, accepted⟩ :=
      Obend.Core.Proofs.BidirectionalCompleteness.full_annotated c
    refine ⟨annotations, Obend.Slot.Core4.checkWork { t with annotations := annotations }, ?_⟩
    rw [same] at accepted
    dsimp only at accepted
    simp only [bidiCheck, Nat.le_refl, ↓reduceIte]
    rw [accepted]; rfl
  mono := by
    intro r r' o ann le hne
    simp only [bidiCheck] at hne ⊢
    split at hne
    · rename_i h; rw [if_pos h, if_pos (Nat.le_trans h le)]
    · exact absurd rfl hne

/-- **The slot's judge is this judge's check**: `Core4.judge` at a grant accepts a term exactly when
the bidirectional judge accepts it with its own annotations as the certificate. -/
theorem judge_iff_check (r : Nat) (Ψ : Context) (t : AnnotatedTerm) (A : Ty) :
    Obend.Slot.Core4.judge r Ψ t A = true ↔ bidirectional.check r (Ψ, t, A) t.annotations = .ok := by
  show _ ↔ bidiCheck r (Ψ, t, A) t.annotations = .ok
  rcases t with ⟨term, ann, asm⟩
  simp only [Obend.Slot.Core4.judge, bidiCheck]
  by_cases w : Obend.Slot.Core4.checkWork ⟨term, ann, asm⟩ ≤ r <;>
    cases h : checkAgainst ⟨term, ann, asm⟩ Ψ A <;> simp [w, h, ofExcept, Except.toBool]

/-- Object extension is accepted by the typing judge at grant 4 (`Core4.extend_filling_admitted`). -/
theorem extend_filling_decided :
    bidirectional.check 4 (([] : Context), Obend.Slot.Core4.extendFilling, Obend.Slot.Core4.extendType)
      Obend.Slot.Core4.extendFilling.annotations = .ok :=
  (judge_iff_check _ _ _ _).1 Obend.Slot.Core4.extend_filling_admitted

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

def coerceCheck (r : Nat) (o : Assumptions × Ty × Ty) (e : Emitted) : Verdict CheckRefusal :=
  if Obend.Slot.Core4.checkWork (Emitted.source o.1 e) ≤ r then
    ofExcept (checkAgainst (Emitted.source o.1 e) [] (e.type o.2.1 o.2.2))
  else .uncovered

/-- **`coerce`**: the producer is the emitter, the checker re-runs the bidirectional checker on
what it emitted. -/
instance coercion : Judge (Assumptions × Ty × Ty) Emitted where
  Clause := CheckRefusal
  Meaning o e := ∃ c : Checked (Emitted.source o.1 e) [], c.type = e.type o.2.1 o.2.2
  check := coerceCheck
  sound := by
    rintro r ⟨a, s, t⟩ e h
    simp only [coerceCheck] at h
    split at h
    · obtain ⟨c, hc⟩ := ofExcept_ok h
      exact ⟨c, (checkAgainst_sound hc).1⟩
    · cases h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment o := ∃ c, coerce o.1 o.2.1 o.2.2 = .ok c
  complete := by
    rintro ⟨a, s, t⟩ ⟨c, hc⟩ _
    obtain ⟨checked, accepted⟩ := coerce_checks hc
    refine ⟨c.emitted, Obend.Slot.Core4.checkWork (Emitted.source a c.emitted), ?_⟩
    simp only [coerceCheck, Nat.le_refl, ↓reduceIte, Emitted.type]
    simp only [Emitted.source]; rw [accepted]; rfl
  mono := by
    intro r r' o e le hne
    simp only [coerceCheck] at hne ⊢
    split at hne
    · rename_i h; rw [if_pos h, if_pos (Nat.le_trans h le)]
    · exact absurd rfl hne

end Coerce

/-! ## C4's checked linearization -/

section C4
open Obend.Law

def c4Check (_ : Nat) (o : Obend.Spec.C4.Graph × String × List (List String)) (_ : Unit) : Verdict InheritRefusal :=
  match precedence o.1 o.2.1 o.2.2 with
  | .ok _ => .ok
  | .error e => .refused e []

/-- What a precedence list is (Barrett et al. 1996), as `precedence_ok` states it. -/
def PrecedenceList (g : Obend.Spec.C4.Graph) (head : String) (parents : List (List String)) (lin : List String) : Prop :=
  lin.head? = some head ∧ lin.Nodup ∧ (∀ chain ∈ parents, chain.Sublist lin) ∧
    ∀ chain ∈ parents, ∀ p ∈ chain, (g.precedence p).Sublist lin

/-- **C4's validated linearization**: `ok` means the computed list is a precedence list. -/
instance c4 : Judge (Obend.Spec.C4.Graph × String × List (List String)) Unit where
  Clause := InheritRefusal
  Meaning o _ := ∃ lin, precedence o.1 o.2.1 o.2.2 = .ok lin ∧ PrecedenceList o.1 o.2.1 o.2.2 lin
  check := c4Check
  sound := by
    rintro r ⟨g, head, parents⟩ _ h
    simp only [c4Check] at h
    split at h
    · rename_i lin hl; exact ⟨lin, hl, precedence_ok hl⟩
    · cases h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment o := ∃ (t : Tree) (n : Nat), o.1 = t.graph n ∧ o.2.2 = t.parents o.2.1 ∧ (t.chain (n + 1) o.2.1).Nodup
  complete := by
    rintro ⟨g, x, parents⟩ ⟨t, n, hg, hp, acyclic⟩ _
    simp only at hg hp acyclic
    subst hg hp
    exact ⟨(), 0, by simp [c4Check, precedence_tree t n x acyclic]⟩
  mono := by intros; rfl

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

def subBagB [DecidableEq Tok] (Δ₁ Δ₂ : List Tok) : Bool := Δ₁.all fun t => Δ₁.count t ≤ Δ₂.count t

theorem subBagB_iff [DecidableEq Tok] (Δ₁ Δ₂ : List Tok) : subBagB Δ₁ Δ₂ = true ↔ SubBag Δ₁ Δ₂ := by
  unfold subBagB SubBag
  constructor
  · intro h t
    by_cases ht : t ∈ Δ₁
    · simpa using List.all_eq_true.1 h t ht
    · rw [List.count_eq_zero_of_not_mem ht]; exact Nat.zero_le _
  · intro h; exact List.all_eq_true.2 fun t _ => by simpa using h t

/-- The hole's declared post implies the result predicate, over every index and result. -/
def Envelope.entails (E : Envelope S Hole A Tok Fact Ob) (i : Ix) (h : Hole i) : Bool :=
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
def checkProt [DecidableEq Tok] [DecidableEq Fact] [DecidableEq Ob] (E : Envelope S Hole A Tok Fact Ob) : (Δ : List Tok) → {i : Ix} → Prot S Hole A i → Bool
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
def envelope [DecidableEq Tok] [DecidableEq Fact] [DecidableEq Ob] (E : Envelope S Hole A Tok Fact Ob) : Judge (ProtObj S Hole A Tok) Unit where
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
