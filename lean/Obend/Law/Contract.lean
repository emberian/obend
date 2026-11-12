module
/-
# Obend.Law.Contract — inductive proof-carrying cell contracts and goal equality

Provides:
- `Holds`: Semantic truth of a Core4 predicate term over `Data`.
- `keeps_eq_holds`: Definitional equivalence with the single-state `Claim.Keeps` checker.
- `Narrows`: Preorder of monotone law refinement (forever-crown attenuation).
- `CellContract`: Inductive 2-state cell contract bundling invariant preservation and relational step soundness.
- `cellContract_relaw_sound`: Forever-crown preservation theorem guaranteeing sound law evolution.
- `CellTrace` & `cellContract_trace_sound`: Multi-step inductive trace invariance.
- `ContractGoal` & `goalEq_sound`: Goal-bound contract obligation encoding and decidable syntactic equality.
-/
public import Obend.Core.Term
public import Obend.Core.Data
public import Obend.Core.Ty
public import Obend.Law.Syntax
public import Obend.Law.Claim
public import Obend.Logic.Receipt

@[expose] public section
namespace Obend.Law

open Obend.Core.Term (Term Evaluates Value Steps)
open Obend.Core.Data (Data)
open Obend.Core.Ty (Ty)

set_option autoImplicit false

/-! ## Semantic Truth: Holds -/

/-- Semantic predicate satisfaction on `Data`.
    A Core4 predicate term `P` holds on `d : Data` iff `P (Data.term d)` evaluates to `.boolean true`. -/
def Holds (P : Term) (d : Data) : Prop :=
  Evaluates (.app P d.term) (.boolean true)

/-- Definitional equivalence with the single-state `Keeps` predicate. -/
theorem keeps_eq_holds (I : Term) (d : Data) : Keeps I d ↔ Holds I d := by
  rfl

/-! ## Forever-Crown Refinement: Narrows -/

/-- Law refinement preorder (Forever-Crown / Monotone Attenuation):
    `law₂` narrows `law₁` (`law₂ ⊑ law₁`) iff every transition admitted by `law₂`
    is also admitted by `law₁`. -/
def Narrows (law₂ law₁ : Term) : Prop :=
  ∀ (old new req : Data), Admits law₂ old new req → Admits law₁ old new req

/-- `Narrows` is reflexive. -/
@[simp] theorem narrows_refl (law : Term) : Narrows law law :=
  fun _ _ _ h => h

/-- `Narrows` is transitive. -/
theorem narrows_trans {l₁ l₂ l₃ : Term} (h12 : Narrows l₁ l₂) (h23 : Narrows l₂ l₃) :
    Narrows l₁ l₃ :=
  fun old new req h => h23 old new req (h12 old new req h)

/-! ## Inductive Cell Contract -/

/-- A proof-carrying inductive contract for an Obend cell or Vault Kind. -/
structure CellContract where
  /-- The executable transition law (Core4 term of arity 3). -/
  law : Term
  /-- The single-state inductive invariant (Core4 predicate). -/
  invariant : Term
  /-- The relational transition specification (Core4 relation of arity 3). -/
  stepRel : Term
  /-- Inductive preservation: if `invariant` holds on `old` and `law` admits the transition,
      then `invariant` holds on `new`. -/
  inductive_preserves :
    ∀ (old new req : Data), Holds invariant old → Admits law old new req → Holds invariant new
  /-- Step soundness: every step admitted by the concrete executable `law` satisfies the
      abstract relational contract `stepRel`. -/
  step_sound :
    ∀ (old new req : Data), Holds invariant old → Admits law old new req → Admits stepRel old new req

/-- **Forever-Crown Preservation Theorem**:
    If cell contract `C₁` is active, and a transition updates the law to `law₂`
    such that `Narrows law₂ C₁.law`, then `law₂` inherits invariant preservation and step soundness
    for the exact same invariant and step specification. -/
def cellContract_relaw_sound (C₁ : CellContract) (law₂ : Term) (h_nar : Narrows law₂ C₁.law) :
    CellContract where
  law := law₂
  invariant := C₁.invariant
  stepRel := C₁.stepRel
  inductive_preserves := fun old new req h_inv h_adm =>
    C₁.inductive_preserves old new req h_inv (h_nar old new req h_adm)
  step_sound := fun old new req h_inv h_adm =>
    C₁.step_sound old new req h_inv (h_nar old new req h_adm)

/-! ## Multi-Step Trace Invariance -/

/-- Inductive trace of cell transitions starting from initial state `s₀`. -/
inductive CellTrace (law : Term) : Data → List (Data × Data) → Data → Prop where
  | nil (s₀ : Data) : CellTrace law s₀ [] s₀
  | snoc {s₀ s_curr s_next req : Data} {steps : List (Data × Data)} :
      CellTrace law s₀ steps s_curr →
      Admits law s_curr s_next req →
      CellTrace law s₀ (steps ++ [(req, s_next)]) s_next

/-- **Inductive Trace Soundness Theorem**:
    Along any execution history where each step is admitted by `C.law`,
    if the initial state satisfies `C.invariant`, the final state satisfies `C.invariant`. -/
theorem cellContract_trace_sound (C : CellContract) (s₀ s_final : Data) (steps : List (Data × Data))
    (h_init : Holds C.invariant s₀) (h_tr : CellTrace C.law s₀ steps s_final) :
    Holds C.invariant s_final := by
  induction h_tr with
  | nil => exact h_init
  | snoc _ h_adm ih =>
    exact C.inductive_preserves _ _ _ ih h_adm

/-! ## Contract Goal Obligations & Syntactic Equality -/

/-- Verification target obligation for a cell contract. -/
inductive ContractGoal where
  | preserves (law invariant : Term)
  | stepSound (law invariant stepRel : Term)
  | narrows (law₂ law₁ : Term)
  deriving Repr

/-- Semantic meaning of a contract goal. -/
def GoalMeaning : ContractGoal → Prop
  | .preserves law inv =>
      ∀ old new req, Holds inv old → Admits law old new req → Holds inv new
  | .stepSound law inv stepRel =>
      ∀ old new req, Holds inv old → Admits law old new req → Admits stepRel old new req
  | .narrows law₂ law₁ =>
      Narrows law₂ law₁

mutual
theorem treeEq_sound_local : ∀ {a b : Obend.Core.Traverse.Tree Obend.Core.TermTraverse.Tag},
    treeEq a b = true → a = b
  | .var _, .var _, h => by simp [treeEq] at h; subst h; rfl
  | .bind a, .bind b, h => by simp only [treeEq] at h; rw [treeEq_sound_local h]
  | .node _ cs, .node _ ds, h => by
      simp only [treeEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, treesEq_sound_local h.2]
  | .var _, .bind _, h | .var _, .node _ _, h | .bind _, .var _, h | .bind _, .node _ _, h
  | .node _ _, .var _, h | .node _ _, .bind _, h => by simp [treeEq] at h
theorem treesEq_sound_local : ∀ {as bs : List (Obend.Core.Traverse.Tree Obend.Core.TermTraverse.Tag)},
    treesEq as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [treesEq, Bool.and_eq_true] at h
      rw [treeEq_sound_local h.1, treesEq_sound_local h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [treesEq] at h
end

mutual
theorem treeEq_refl_local : ∀ (a : Obend.Core.Traverse.Tree Obend.Core.TermTraverse.Tag), treeEq a a = true
  | .var _ => by simp [treeEq]
  | .bind a => by simp only [treeEq]; exact treeEq_refl_local a
  | .node _ cs => by simp only [treeEq, decide_true, Bool.true_and]; exact treesEq_refl_local cs
theorem treesEq_refl_local : ∀ (as : List (Obend.Core.Traverse.Tree Obend.Core.TermTraverse.Tag)),
    treesEq as as = true
  | [] => rfl
  | a :: as => by simp only [treesEq, Bool.and_eq_true]; exact ⟨treeEq_refl_local a, treesEq_refl_local as⟩
end

theorem termEq_sound_local {a b : Term} (h : termEq a b = true) : a = b :=
  Obend.Core.TermTraverse.encode_injective (treeEq_sound_local h)

@[simp] theorem termEq_refl_local (a : Term) : termEq a a = true :=
  treeEq_refl_local _

/-- Canonical kind tag of a `ContractGoal`. -/
def ContractGoal.kind : ContractGoal → String
  | .preserves _ _ => "preserves"
  | .stepSound _ _ _ => "stepSound"
  | .narrows _ _ => "narrows"

/-- Authoritative `law` operand of a `ContractGoal`. -/
def ContractGoal.law : ContractGoal → Term
  | .preserves l _ => l
  | .stepSound l _ _ => l
  | .narrows l2 _ => l2

/-- Authoritative `invariant` (or parent law for `narrows`) operand of a `ContractGoal`. -/
def ContractGoal.invariant : ContractGoal → Term
  | .preserves _ i => i
  | .stepSound _ i _ => i
  | .narrows _ l1 => l1

/-- Authoritative `step` operand of a `ContractGoal` (equals `invariant` when no separate `stepRel` is present). -/
def ContractGoal.step : ContractGoal → Term
  | .preserves _ i => i
  | .stepSound _ _ s => s
  | .narrows _ l1 => l1

/-- Syntactic equality of two `ContractGoal` values via `(kind, law, invariant, step)`. -/
def goalEq (a b : ContractGoal) : Bool :=
  (a.kind == b.kind) &&
  termEq a.law b.law &&
  termEq a.invariant b.invariant &&
  termEq a.step b.step

instance : BEq ContractGoal where
  beq := goalEq

@[simp] theorem goalEq_refl (g : ContractGoal) : goalEq g g = true := by
  simp [goalEq]

theorem goalEq_sound {a b : ContractGoal} (h : goalEq a b = true) : a = b := by
  unfold goalEq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hk, hl⟩, hi⟩, hs⟩ := h
  have hlaw := termEq_sound_local hl
  have hinv := termEq_sound_local hi
  have hstep := termEq_sound_local hs
  cases a <;> cases b <;> simp [ContractGoal.kind, ContractGoal.law, ContractGoal.invariant, ContractGoal.step] at hk hlaw hinv hstep
  · subst hlaw; subst hinv; rfl
  · subst hlaw; subst hinv; subst hstep; rfl
  · subst hlaw; subst hinv; rfl

instance : DecidableEq ContractGoal := fun a b =>
  if h : goalEq a b = true then
    isTrue (goalEq_sound h)
  else
    isFalse (fun heq => by subst heq; exact h (goalEq_refl a))

/-- Canonical Core4 `Term` encoding of a `ContractGoal`. -/
def ContractGoal.toTerm : ContractGoal → Term
  | .preserves l i =>
    .record [("kind", .label "preserves"), ("law", l), ("invariant", i), ("step", i)]
  | .stepSound l i s =>
    .record [("kind", .label "stepSound"), ("law", l), ("invariant", i), ("step", s)]
  | .narrows l2 l1 =>
    .record [("kind", .label "narrows"), ("law", l2), ("invariant", l1), ("step", l1)]

/-- Decode a `ContractGoal` from its canonical Core4 `Term` encoding. -/
def ContractGoal.ofTerm? : Term → Option ContractGoal
  | .record [("kind", .label "preserves"), ("law", l), ("invariant", i), ("step", s)] =>
    if termEq i s then some (.preserves l i) else none
  | .record [("kind", .label "stepSound"), ("law", l), ("invariant", i), ("step", s)] =>
    some (.stepSound l i s)
  | .record [("kind", .label "narrows"), ("law", l2), ("invariant", l1), ("step", s)] =>
    if termEq l1 s then some (.narrows l2 l1) else none
  | _ => none

@[simp] theorem ContractGoal.ofTerm?_toTerm (g : ContractGoal) :
    ContractGoal.ofTerm? g.toTerm = some g := by
  cases g <;> simp [ContractGoal.toTerm, ContractGoal.ofTerm?]

/-- Serialize a `ContractGoal` to JSON via `Obend.Logic.termJson`. -/
def ContractGoal.toJson (g : ContractGoal) : Lean.Json :=
  Obend.Logic.termJson g.toTerm

/-- Deserialize a `ContractGoal` from JSON via `Obend.Logic.termOf`. -/
def ContractGoal.ofJson? (j : Lean.Json) : Option ContractGoal :=
  match Obend.Logic.termOf j with
  | .ok t => ContractGoal.ofTerm? t
  | .error _ => none

end Obend.Law

end
