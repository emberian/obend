module
/-
# Obend.Tactic.DataRefinement — `Spec ↔ Exec` data refinement, three refinements, `refine_exec`
A `DataRefinement Spec Exec` is a partial abstraction function: a well-formedness predicate `WF` on
the executable representation and `alpha`, which reads a well-formed representation as its
specification value. `Refines R s e` is its graph, `PackedExec R` the subtype of well-formed
representations with the total `toSpec`. Refinements compose (`id`, `comp`, `prod`, `option`), and so
do the operations they relate (`UnaryRefines`, `BinaryRefines`, `ObsRefines`).
Three instances are carried end to end.
* **Finite sets as strictly sorted arrays.** `FinSetSpec α` is an extensional finite set (a `Bool`
  membership predicate with a finiteness witness), so `union`/`inter`/`diff` are `||`/`&&`/`&& !`
  pointwise. `SortedArraySet α` is an `Array α`, well formed when strictly increasing in a
  `StrictLinearOrder α`. `containsFast` is a binary search; `unionFast`, `interFast`, `diffFast` are
  one two-pointer loop (`mergeLoop`) pushing onto a preallocated array. Each is proved equal to its
  specification (`containsFast_eq_spec`, `unionFast_toSpec`, `interFast_toSpec`, `diffFast_toSpec`),
  and the representation is canonical (`SortedArraySet.toSpec_injective`).
* **Word lists as little-endian bytes.** `packU64LE` writes eight bytes a word, `readU64LE` reads
  word `i` back in constant time (`readU64LE_packU64LE`), and `u64BytesRefinement` reads a
  `ByteArray` of size a multiple of eight as a `List UInt64`.
* **Cofibrations of the 3-cube as 27-bit words.** `FaceIdealSpec3` is a downward-closed set of the
  27 faces `{0,1,*}^3`; `FaceIdeal3` is a `BitVec 27` with one bit a face, `|||` for `∨` and `&&&`
  for `∧`. The boundary `(i = 0) ∨ (i = 1)` is not `⊤` (`FaceIdeal3.boundary_ne_top`), which a truth
  table over the 8 vertices cannot say.
`refine_exec` rewrites executable expressions to their specification with these theorems (and any
tagged `@[refine_exec_simp]` in a later module), then decides the remaining `Bool` identity by cases
on its atoms. The algebra of the representations (§8) is proved by it.
-/
public import Lean
public meta import Lean.Meta.Tactic.Generalize
public meta import Lean.Meta.Tactic.Cases
public section
namespace Obend.Tactic.DataRefinement
set_option autoImplicit false
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

/-! ## 1. The refinement algebra -/
/-- A data refinement of `Spec` by `Exec`: which representations are well formed, and the
specification value each well-formed one stands for. -/
structure DataRefinement (Spec : Type u) (Exec : Type v) where
  /-- the representation invariant -/
  WF : Exec → Prop
  /-- the abstraction function, on well-formed representations -/
  alpha : (e : Exec) → WF e → Spec
/-- `e` is well formed and stands for `s`. -/
@[expose] def Refines {Spec : Type u} {Exec : Type v} (R : DataRefinement Spec Exec) (s : Spec) (e : Exec) :
    Prop := ∃ h : R.WF e, R.alpha e h = s
/-- The well-formed representations. -/
@[expose] def PackedExec {Spec : Type u} {Exec : Type v} (R : DataRefinement Spec Exec) : Type v :=
  { e : Exec // R.WF e }

namespace PackedExec
variable {Spec : Type u} {Exec : Type v} {R : DataRefinement Spec Exec}
/-- The specification value of a well-formed representation. -/
@[expose] def toSpec (p : PackedExec R) : Spec := R.alpha p.val p.property
theorem refines (p : PackedExec R) : Refines R p.toSpec p.val := ⟨p.property, rfl⟩
end PackedExec

namespace Refines
variable {Spec : Type u} {Exec : Type v} {R : DataRefinement Spec Exec}
theorem wf {s : Spec} {e : Exec} (h : Refines R s e) : R.WF e :=
  match h with
  | ⟨hw, _⟩ => hw
theorem alpha_eq {s : Spec} {e : Exec} (h : Refines R s e) : R.alpha e h.wf = s :=
  match h with
  | ⟨_, he⟩ => he
/-- A representation stands for at most one specification value. -/
theorem unique {s s' : Spec} {e : Exec} (h : Refines R s e) (h' : Refines R s' e) : s = s' :=
  h.alpha_eq.symm.trans h'.alpha_eq
/-- Pack a refined representation. -/
@[expose] def pack {s : Spec} {e : Exec} (h : Refines R s e) : PackedExec R := ⟨e, h.wf⟩
theorem pack_toSpec {s : Spec} {e : Exec} (h : Refines R s e) : h.pack.toSpec = s := h.alpha_eq
end Refines
theorem refines_iff_packed {Spec : Type u} {Exec : Type v} (R : DataRefinement Spec Exec) (s : Spec)
    (e : Exec) : Refines R s e ↔ ∃ p : PackedExec R, p.val = e ∧ p.toSpec = s :=
  ⟨fun h => ⟨h.pack, rfl, h.pack_toSpec⟩, fun ⟨p, he, hs⟩ => he ▸ hs ▸ p.refines⟩

namespace DataRefinement
/-- Every value represents itself. -/
@[expose] protected def id (α : Type u) : DataRefinement α α where
  WF _ := True
  alpha e _ := e
theorem refines_id {α : Type u} (s e : α) : Refines (DataRefinement.id α) s e ↔ e = s :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩
/-- Refinements compose: `C` represents `B` represents `A`. -/
@[expose] def comp {A : Type u} {B : Type v} {C : Type w} (R₁ : DataRefinement A B)
    (R₂ : DataRefinement B C) : DataRefinement A C where
  WF c := ∃ h : R₂.WF c, R₁.WF (R₂.alpha c h)
  alpha c h := R₁.alpha (R₂.alpha c (match h with | ⟨h₂, _⟩ => h₂)) (match h with | ⟨_, h₁⟩ => h₁)
theorem refines_comp {A : Type u} {B : Type v} {C : Type w} (R₁ : DataRefinement A B)
    (R₂ : DataRefinement B C) (a : A) (c : C) :
    Refines (R₁.comp R₂) a c ↔ ∃ b, Refines R₁ a b ∧ Refines R₂ b c := by
  constructor
  · rintro ⟨⟨h₂, h₁⟩, he⟩
    exact ⟨R₂.alpha c h₂, ⟨h₁, he⟩, ⟨h₂, rfl⟩⟩
  · rintro ⟨b, ⟨h₁, he₁⟩, ⟨h₂, he₂⟩⟩
    subst he₂
    exact ⟨⟨h₂, h₁⟩, he₁⟩
/-- Refinements of the two components refine the pair. -/
@[expose] def prod {S₁ : Type u₁} {E₁ : Type v₁} {S₂ : Type u₂} {E₂ : Type v₂}
    (R₁ : DataRefinement S₁ E₁) (R₂ : DataRefinement S₂ E₂) : DataRefinement (S₁ × S₂) (E₁ × E₂) where
  WF p := R₁.WF p.1 ∧ R₂.WF p.2
  alpha p h := (R₁.alpha p.1 h.1, R₂.alpha p.2 h.2)
theorem refines_prod {S₁ : Type u₁} {E₁ : Type v₁} {S₂ : Type u₂} {E₂ : Type v₂}
    (R₁ : DataRefinement S₁ E₁) (R₂ : DataRefinement S₂ E₂) (s : S₁ × S₂) (e : E₁ × E₂) :
    Refines (R₁.prod R₂) s e ↔ Refines R₁ s.1 e.1 ∧ Refines R₂ s.2 e.2 := by
  constructor
  · rintro ⟨⟨h₁, h₂⟩, he⟩
    subst he
    exact ⟨⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩
  · rintro ⟨⟨h₁, he₁⟩, ⟨h₂, he₂⟩⟩
    exact ⟨⟨h₁, h₂⟩, Prod.ext he₁ he₂⟩
/-- A refinement of the payload refines the option. -/
@[expose] def option {Spec : Type u} {Exec : Type v} (R : DataRefinement Spec Exec) :
    DataRefinement (Option Spec) (Option Exec) where
  WF o := ∀ e, o = some e → R.WF e
  alpha o h :=
    match o, h with
    | none, _ => none
    | some e, h => some (R.alpha e (h e rfl))
theorem refines_option_none {Spec : Type u} {Exec : Type v} (R : DataRefinement Spec Exec)
    (s : Option Spec) : Refines R.option s none ↔ s = none :=
  ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨fun _ he => (nomatch he), h.symm⟩⟩
theorem refines_option_some {Spec : Type u} {Exec : Type v} (R : DataRefinement Spec Exec)
    (s : Option Spec) (e : Exec) : Refines R.option s (some e) ↔ ∃ s', s = some s' ∧ Refines R s' e := by
  constructor
  · rintro ⟨h, he⟩
    exact ⟨R.alpha e (h e rfl), he.symm, ⟨h e rfl, rfl⟩⟩
  · rintro ⟨s', rfl, ⟨h, he⟩⟩
    exact ⟨fun e' he' => Option.some.inj he' ▸ h, congrArg some he⟩
end DataRefinement
/-- `g` on representations refines `f` on specifications. -/
@[expose] def UnaryRefines {S₁ : Type u₁} {E₁ : Type v₁} {S₂ : Type u₂} {E₂ : Type v₂}
    (R₁ : DataRefinement S₁ E₁) (R₂ : DataRefinement S₂ E₂) (f : S₁ → S₂) (g : E₁ → E₂) : Prop :=
  ∀ s e, Refines R₁ s e → Refines R₂ (f s) (g e)
/-- A binary operation on representations refines one on specifications. -/
@[expose] def BinaryRefines {S₁ : Type u₁} {E₁ : Type v₁} {S₂ : Type u₂} {E₂ : Type v₂} {S₃ : Type u₃}
    {E₃ : Type v₃} (R₁ : DataRefinement S₁ E₁) (R₂ : DataRefinement S₂ E₂) (R₃ : DataRefinement S₃ E₃)
    (f : S₁ → S₂ → S₃) (g : E₁ → E₂ → E₃) : Prop :=
  ∀ s₁ e₁ s₂ e₂, Refines R₁ s₁ e₁ → Refines R₂ s₂ e₂ → Refines R₃ (f s₁ s₂) (g e₁ e₂)
/-- An observation of a representation is the observation of what it stands for. -/
@[expose] def ObsRefines {Spec : Type u} {Exec : Type v} {Val : Type w} (R : DataRefinement Spec Exec)
    (f : Spec → Val) (g : Exec → Val) : Prop := ∀ s e, Refines R s e → g e = f s
/-- An observation into `Bool`. -/
abbrev PredRefines {Spec : Type u} {Exec : Type v} (R : DataRefinement Spec Exec) (f : Spec → Bool)
    (g : Exec → Bool) : Prop :=
  ObsRefines R f g

namespace UnaryRefines
variable {S₁ : Type u₁} {E₁ : Type v₁} {S₂ : Type u₂} {E₂ : Type v₂} {S₃ : Type u₃} {E₃ : Type v₃}
protected theorem id (R : DataRefinement S₁ E₁) : UnaryRefines R R (fun s => s) (fun e => e) := fun _ _ h => h
/-- Operations compose. -/
theorem comp {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂} {R₃ : DataRefinement S₃ E₃}
    {f₁ : S₁ → S₂} {g₁ : E₁ → E₂} {f₂ : S₂ → S₃} {g₂ : E₂ → E₃} (h₂ : UnaryRefines R₂ R₃ f₂ g₂)
    (h₁ : UnaryRefines R₁ R₂ f₁ g₁) : UnaryRefines R₁ R₃ (fun s => f₂ (f₁ s)) (fun e => g₂ (g₁ e)) :=
  fun s e h => h₂ _ _ (h₁ s e h)
/-- Refinement stacks: an operation refined twice is refined along the composite refinement. -/
theorem stack {A₁ : Type u₁} {B₁ : Type v₁} {C₁ : Type w} {A₂ : Type u₂} {B₂ : Type v₂} {C₂ : Type u₃}
    {R₁ : DataRefinement A₁ B₁} {R₁' : DataRefinement B₁ C₁} {R₂ : DataRefinement A₂ B₂}
    {R₂' : DataRefinement B₂ C₂} {f : A₁ → A₂} {g : B₁ → B₂} {k : C₁ → C₂}
    (hfg : UnaryRefines R₁ R₂ f g) (hgk : UnaryRefines R₁' R₂' g k) :
    UnaryRefines (R₁.comp R₁') (R₂.comp R₂') f k := by
  intro a c h
  obtain ⟨b, hab, hbc⟩ := (DataRefinement.refines_comp R₁ R₁' a c).1 h
  exact (DataRefinement.refines_comp R₂ R₂' _ _).2 ⟨g b, hfg a b hab, hgk b c hbc⟩
/-- The operation on packed representations. -/
@[expose] def lift {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂} {f : S₁ → S₂} {g : E₁ → E₂}
    (h : UnaryRefines R₁ R₂ f g) (p : PackedExec R₁) : PackedExec R₂ := ⟨g p.val, (h _ _ p.refines).wf⟩
theorem lift_toSpec {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂} {f : S₁ → S₂} {g : E₁ → E₂}
    (h : UnaryRefines R₁ R₂ f g) (p : PackedExec R₁) : (h.lift p).toSpec = f p.toSpec := (h _ _ p.refines).alpha_eq
/-- Operations on the components refine the operation on pairs. -/
theorem prod {S₁' : Type u₁} {E₁' : Type v₁} {S₂' : Type u₂} {E₂' : Type v₂}
    {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂} {R₁' : DataRefinement S₁' E₁'}
    {R₂' : DataRefinement S₂' E₂'} {f : S₁ → S₂} {g : E₁ → E₂} {f' : S₁' → S₂'} {g' : E₁' → E₂'}
    (h : UnaryRefines R₁ R₂ f g) (h' : UnaryRefines R₁' R₂' f' g') :
    UnaryRefines (R₁.prod R₁') (R₂.prod R₂') (fun s => (f s.1, f' s.2)) (fun e => (g e.1, g' e.2)) := by
  intro s e hse
  obtain ⟨h₁, h₂⟩ := (DataRefinement.refines_prod R₁ R₁' s e).1 hse
  exact (DataRefinement.refines_prod R₂ R₂' _ _).2 ⟨h _ _ h₁, h' _ _ h₂⟩
end UnaryRefines

namespace BinaryRefines
variable {S₁ : Type u₁} {E₁ : Type v₁} {S₂ : Type u₂} {E₂ : Type v₂} {S₃ : Type u₃} {E₃ : Type v₃}
/-- A binary operation followed by a unary one. -/
theorem comp {S₄ : Type u} {E₄ : Type v} {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂}
    {R₃ : DataRefinement S₃ E₃} {R₄ : DataRefinement S₄ E₄} {f : S₁ → S₂ → S₃} {g : E₁ → E₂ → E₃}
    {f' : S₃ → S₄} {g' : E₃ → E₄} (h' : UnaryRefines R₃ R₄ f' g') (h : BinaryRefines R₁ R₂ R₃ f g) :
    BinaryRefines R₁ R₂ R₄ (fun s₁ s₂ => f' (f s₁ s₂)) (fun e₁ e₂ => g' (g e₁ e₂)) :=
  fun _ _ _ _ h₁ h₂ => h' _ _ (h _ _ _ _ h₁ h₂)
/-- A binary operation applied to the results of two unary ones. -/
theorem comp₂ {S₁' : Type u} {E₁' : Type v} {S₂' : Type u} {E₂' : Type v} {R₁ : DataRefinement S₁ E₁}
    {R₂ : DataRefinement S₂ E₂} {R₃ : DataRefinement S₃ E₃} {R₁' : DataRefinement S₁' E₁'}
    {R₂' : DataRefinement S₂' E₂'} {f : S₁ → S₂ → S₃} {g : E₁ → E₂ → E₃} {f₁ : S₁' → S₁} {g₁ : E₁' → E₁}
    {f₂ : S₂' → S₂} {g₂ : E₂' → E₂} (h : BinaryRefines R₁ R₂ R₃ f g) (h₁ : UnaryRefines R₁' R₁ f₁ g₁)
    (h₂ : UnaryRefines R₂' R₂ f₂ g₂) :
    BinaryRefines R₁' R₂' R₃ (fun s₁ s₂ => f (f₁ s₁) (f₂ s₂)) (fun e₁ e₂ => g (g₁ e₁) (g₂ e₂)) :=
  fun _ _ _ _ k₁ k₂ => h _ _ _ _ (h₁ _ _ k₁) (h₂ _ _ k₂)
/-- A binary operation is a unary one on pairs. -/
theorem uncurry {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂} {R₃ : DataRefinement S₃ E₃}
    {f : S₁ → S₂ → S₃} {g : E₁ → E₂ → E₃} (h : BinaryRefines R₁ R₂ R₃ f g) :
    UnaryRefines (R₁.prod R₂) R₃ (fun s => f s.1 s.2) (fun e => g e.1 e.2) := by
  intro s e hse
  obtain ⟨h₁, h₂⟩ := (DataRefinement.refines_prod R₁ R₂ s e).1 hse
  exact h _ _ _ _ h₁ h₂
/-- The operation on packed representations. -/
@[expose] def lift {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂} {R₃ : DataRefinement S₃ E₃}
    {f : S₁ → S₂ → S₃} {g : E₁ → E₂ → E₃} (h : BinaryRefines R₁ R₂ R₃ f g) (p : PackedExec R₁)
    (q : PackedExec R₂) : PackedExec R₃ := ⟨g p.val q.val, (h _ _ _ _ p.refines q.refines).wf⟩
theorem lift_toSpec {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂} {R₃ : DataRefinement S₃ E₃}
    {f : S₁ → S₂ → S₃} {g : E₁ → E₂ → E₃} (h : BinaryRefines R₁ R₂ R₃ f g) (p : PackedExec R₁)
    (q : PackedExec R₂) : (h.lift p q).toSpec = f p.toSpec q.toSpec := (h _ _ _ _ p.refines q.refines).alpha_eq
end BinaryRefines

namespace ObsRefines
variable {S₁ : Type u₁} {E₁ : Type v₁} {S₂ : Type u₂} {E₂ : Type v₂} {S₃ : Type u₃} {E₃ : Type v₃}
  {Val : Type w}
/-- An observation after a refined operation is a refined observation. -/
theorem of_unary {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂} {f : S₁ → S₂} {g : E₁ → E₂}
    {o : S₂ → Val} {o' : E₂ → Val} (ho : ObsRefines R₂ o o') (h : UnaryRefines R₁ R₂ f g) :
    ObsRefines R₁ (fun s => o (f s)) (fun e => o' (g e)) := fun s e hse => ho _ _ (h s e hse)
/-- An observation after a refined binary operation, at refined arguments. -/
theorem of_binary {R₁ : DataRefinement S₁ E₁} {R₂ : DataRefinement S₂ E₂} {R₃ : DataRefinement S₃ E₃}
    {f : S₁ → S₂ → S₃} {g : E₁ → E₂ → E₃} {o : S₃ → Val} {o' : E₃ → Val} (ho : ObsRefines R₃ o o')
    (h : BinaryRefines R₁ R₂ R₃ f g) {s₁ : S₁} {e₁ : E₁} {s₂ : S₂} {e₂ : E₂} (h₁ : Refines R₁ s₁ e₁)
    (h₂ : Refines R₂ s₂ e₂) : o' (g e₁ e₂) = o (f s₁ s₂) := ho _ _ (h _ _ _ _ h₁ h₂)
/-- A function of a refined observation. -/
theorem map {Val' : Type u} {R : DataRefinement S₁ E₁} {o : S₁ → Val} {o' : E₁ → Val}
    (ho : ObsRefines R o o') (k : Val → Val') : ObsRefines R (fun s => k (o s)) (fun e => k (o' e)) :=
  fun s e h => congrArg k (ho s e h)
/-- On a packed representation the observation is the specification's, with no hypothesis. -/
theorem packed {R : DataRefinement S₁ E₁} {o : S₁ → Val} {o' : E₁ → Val} (ho : ObsRefines R o o')
    (p : PackedExec R) : o' p.val = o p.toSpec := ho _ _ p.refines
/-- Along a composite refinement, an observation of the middle representation that is itself
refined is refined. -/
theorem stack {A : Type u₁} {B : Type v₁} {C : Type u₂} {R₁ : DataRefinement A B}
    {R₂ : DataRefinement B C} {o : A → Val} {o' : B → Val} {o'' : C → Val} (h₁ : ObsRefines R₁ o o')
    (h₂ : ObsRefines R₂ o' o'') : ObsRefines (R₁.comp R₂) o o'' := by
  intro a c h
  obtain ⟨b, hab, hbc⟩ := (DataRefinement.refines_comp R₁ R₂ a c).1 h
  exact (h₂ b c hbc).trans (h₁ a b hab)
end ObsRefines

/-! ## 2. Strict linear orders -/
/-- A decidable strict linear order: irreflexive, transitive, and trichotomous. -/
class StrictLinearOrder (α : Type u) where
  lt : α → α → Bool
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  tri : ∀ a b, lt a b = false → lt b a = false → a = b

namespace StrictLinearOrder
variable {α : Type u} [StrictLinearOrder α]
theorem asymm {a b : α} (h : lt a b = true) : lt b a = false := by
  cases hba : lt b a
  · rfl
  · have := trans a b a h hba
    rw [irrefl] at this
    cases this
/-- Neither is below the other: equality, decided by the order. -/
@[expose] def eqv (a b : α) : Bool := !lt a b && !lt b a
theorem eqv_iff {a b : α} : eqv a b = true ↔ a = b := by
  constructor
  · intro h
    simp only [eqv, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact tri a b h.1 h.2
  · rintro rfl
    simp [eqv, irrefl]
theorem eqv_self (a : α) : eqv a a = true := eqv_iff.2 rfl
theorem eqv_eq_false_of_lt {a b : α} (h : lt a b = true) : eqv a b = false := by simp [eqv, h]
theorem eqv_eq_false_of_gt {a b : α} (h : lt b a = true) : eqv a b = false := by simp [eqv, h]
end StrictLinearOrder
open StrictLinearOrder (lt eqv eqv_iff eqv_self)
instance : StrictLinearOrder Nat where
  lt a b := decide (a < b)
  irrefl a := by simp
  trans a b c := by
    simp only [decide_eq_true_eq]; omega
  tri a b := by
    simp only [decide_eq_false_iff_not]; omega
instance : StrictLinearOrder UInt64 where
  lt a b := decide (a < b)
  irrefl a := by simp
  trans a b c := by
    simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt]; omega
  tri a b := by
    simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt]
    intro h₁ h₂
    exact UInt64.toNat_inj.1 (by omega)
instance : StrictLinearOrder UInt8 where
  lt a b := decide (a < b)
  irrefl a := by simp
  trans a b c := by
    simp only [decide_eq_true_eq, UInt8.lt_iff_toNat_lt]; omega
  tri a b := by
    simp only [decide_eq_false_iff_not, UInt8.lt_iff_toNat_lt]
    intro h₁ h₂
    exact UInt8.toNat_inj.1 (by omega)
/-- The lexicographic order on lists; a proper prefix is below its extensions. -/
@[expose] def lexLt {α : Type u} [StrictLinearOrder α] : List α → List α → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => lt a b || (!lt b a && lexLt as bs)
theorem lexLt_irrefl {α : Type u} [StrictLinearOrder α] (l : List α) : lexLt l l = false := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [lexLt, StrictLinearOrder.irrefl, ih]
theorem lexLt_trans {α : Type u} [StrictLinearOrder α] :
    ∀ (l₁ l₂ l₃ : List α), lexLt l₁ l₂ = true → lexLt l₂ l₃ = true → lexLt l₁ l₃ = true
  | [], [], _, h, _ => by cases h
  | [], _ :: _, [], _, h => by cases h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, h => by cases h
  | a :: as, b :: bs, c :: cs, h₁, h₂ => by
    simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h₁ h₂ ⊢
    rcases h₁ with hab | ⟨hba, hl₁⟩
    · rcases h₂ with hbc | ⟨hcb, _⟩
      · exact .inl (StrictLinearOrder.trans a b c hab hbc)
      · cases hbc : lt b c
        · exact .inl (StrictLinearOrder.tri b c hbc hcb ▸ hab)
        · exact .inl (StrictLinearOrder.trans a b c hab hbc)
    · cases hab : lt a b
      · have e : a = b := StrictLinearOrder.tri a b hab hba
        subst e
        rcases h₂ with hbc | ⟨hcb, hl₂⟩
        · exact .inl hbc
        · exact .inr ⟨hcb, lexLt_trans as bs cs hl₁ hl₂⟩
      · rcases h₂ with hbc | ⟨hcb, _⟩
        · exact .inl (StrictLinearOrder.trans a b c hab hbc)
        · cases hbc : lt b c
          · exact .inl (StrictLinearOrder.tri b c hbc hcb ▸ hab)
          · exact .inl (StrictLinearOrder.trans a b c hab hbc)
theorem lexLt_tri {α : Type u} [StrictLinearOrder α] :
    ∀ (l₁ l₂ : List α), lexLt l₁ l₂ = false → lexLt l₂ l₁ = false → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], _, h => by cases h
  | a :: as, b :: bs, h₁, h₂ => by
    simp only [lexLt, Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false'] at h₁ h₂
    obtain ⟨hab, h₁⟩ := h₁
    obtain ⟨hba, h₂⟩ := h₂
    have e : a = b := StrictLinearOrder.tri a b hab hba
    subst e
    have h₁' : lexLt as bs = false := by
      rcases h₁ with h | h
      · rw [StrictLinearOrder.irrefl] at h; cases h
      · exact h
    have h₂' : lexLt bs as = false := by
      rcases h₂ with h | h
      · rw [StrictLinearOrder.irrefl] at h; cases h
      · exact h
    rw [lexLt_tri as bs h₁' h₂']
instance {α : Type u} [StrictLinearOrder α] : StrictLinearOrder (List α) where
  lt := lexLt
  irrefl := lexLt_irrefl
  trans := lexLt_trans
  tri := lexLt_tri
theorem uint8_lt_def (a b : UInt8) : lt a b = decide (a < b) := rfl
/-- Lexicographic comparison of two byte strings from index `i`, reading both in place. -/
def byteLtLoop (a b : ByteArray) (i : Nat) : Bool :=
  if ha : i < a.size then
    if hb : i < b.size then
      if a[i] < b[i] then true
      else if b[i] < a[i] then false
      else byteLtLoop a b (i + 1)
    else false
  else decide (i < b.size)
termination_by a.size - i
theorem byteArray_drop_cons (a : ByteArray) (i : Nat) (h : i < a.size) :
    a.data.toList.drop i = a[i] :: a.data.toList.drop (i + 1) := by
  have h' : i < a.data.toList.length := by simpa using h
  rw [List.drop_eq_getElem_cons h']; rfl
theorem byteArray_drop_nil (a : ByteArray) (i : Nat) (h : ¬i < a.size) : a.data.toList.drop i = [] := by
  apply List.drop_eq_nil_of_le
  have : a.data.toList.length = a.size := (by rw [Array.length_toList]; rfl); omega
theorem byteLtLoop_eq (a b : ByteArray) (i : Nat) :
    byteLtLoop a b i = lexLt (a.data.toList.drop i) (b.data.toList.drop i) := by
  fun_induction byteLtLoop a b i with
  | case1 i ha hb hlt =>
    rw [byteArray_drop_cons a i ha, byteArray_drop_cons b i hb]
    simp [lexLt, uint8_lt_def, hlt]
  | case2 i ha hb hlt hgt =>
    rw [byteArray_drop_cons a i ha, byteArray_drop_cons b i hb]
    simp [lexLt, uint8_lt_def, hlt, hgt]
  | case3 i ha hb hlt hgt ih =>
    rw [byteArray_drop_cons a i ha, byteArray_drop_cons b i hb, ih]
    simp [lexLt, uint8_lt_def, hlt, hgt]
  | case4 i ha hb =>
    rw [byteArray_drop_cons a i ha, byteArray_drop_nil b i hb]; rfl
  | case5 i ha =>
    rw [byteArray_drop_nil a i ha]
    by_cases hb : i < b.size
    · rw [byteArray_drop_cons b i hb]
      simp [lexLt, hb]
    · rw [byteArray_drop_nil b i hb]
      simp [lexLt, hb]
theorem byteLtLoop_zero (a b : ByteArray) : byteLtLoop a b 0 = lexLt a.data.toList b.data.toList := by
  rw [byteLtLoop_eq]; rfl
/-- Byte strings in lexicographic order, compared in place. -/
instance : StrictLinearOrder ByteArray where
  lt a b := byteLtLoop a b 0
  irrefl a := by rw [byteLtLoop_zero]; exact lexLt_irrefl _
  trans a b c := by
    simp only [byteLtLoop_zero]
    exact lexLt_trans _ _ _
  tri a b := by
    simp only [byteLtLoop_zero]
    intro h₁ h₂
    have := lexLt_tri _ _ h₁ h₂
    exact ByteArray.ext (Array.toList_inj.1 this)

/-! ## 3. Sorted lists: membership and the merge that models the two-pointer loop -/

section Lists
variable {α : Type u} [StrictLinearOrder α]
/-- Strictly increasing. -/
abbrev SortedList (l : List α) : Prop := l.Pairwise fun a b => lt a b = true
/-- Membership in a list, decided by the order. -/
@[expose] def memB (z : α) (l : List α) : Bool := l.any fun y => eqv z y
theorem memB_iff {z : α} {l : List α} : memB z l = true ↔ z ∈ l := by
  simp only [memB, List.any_eq_true, eqv_iff]
  exact ⟨fun ⟨_, h, e⟩ => e ▸ h, fun h => ⟨z, h, rfl⟩⟩
theorem memB_nil (z : α) : memB z ([] : List α) = false := rfl
theorem memB_cons (z x : α) (l : List α) : memB z (x :: l) = (eqv z x || memB z l) := by simp [memB]
theorem memB_eq_false_of_lt_all {w : α} {l : List α} (h : ∀ z ∈ l, lt w z = true) : memB w l = false := by
  cases hm : memB w l
  · rfl
  · have := h w (memB_iff.1 hm)
    rw [StrictLinearOrder.irrefl] at this
    cases this
theorem SortedList.head_lt {x : α} {l : List α} (h : SortedList (x :: l)) : ∀ z ∈ l, lt x z = true :=
  (List.pairwise_cons.1 h).1
theorem SortedList.tail {x : α} {l : List α} (h : SortedList (x :: l)) : SortedList l := (List.pairwise_cons.1 h).2
theorem SortedList.lt_trans_all {w x : α} {l : List α} (h : SortedList (x :: l)) (hw : lt w x = true) :
    ∀ z ∈ x :: l, lt w z = true := by
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hz
  · exact hw
  · exact StrictLinearOrder.trans w x z hw (h.head_lt z hz)
/-- Prepend `x` when the flag is set. -/
@[expose] def emit (k : Bool) (x : α) (l : List α) : List α := if k then x :: l else l
theorem memB_emit (z : α) (k : Bool) (x : α) (l : List α) :
    memB z (emit k x l) = ((k && eqv z x) || memB z l) := by cases k <;> simp [emit, memB_cons]
omit [StrictLinearOrder α] in
theorem mem_emit {z : α} {k : Bool} {x : α} {l : List α} (h : z ∈ emit k x l) : z = x ∨ z ∈ l := by
  cases k
  · exact .inr h
  · exact List.mem_cons.1 h
theorem sorted_emit {k : Bool} {x : α} {l : List α} (hl : SortedList l) (hx : ∀ z ∈ l, lt x z = true) :
    SortedList (emit k x l) := by
  cases k
  · exact hl
  · exact List.pairwise_cons.2 ⟨hx, hl⟩
/-- The list when the flag is set, else nothing. -/
@[expose] def keepIf (k : Bool) (l : List α) : List α := if k then l else []
/-- The merge of two sorted lists that keeps an element found only on the left when `kl`, only on
the right when `kr`, and on both sides when `kb`. Union is `true true true`, intersection
`false false true`, difference `true false false`. -/
@[expose] def mergeL (kl kr kb : Bool) : List α → List α → List α
  | [], ys => keepIf kr ys
  | x :: xs, [] => keepIf kl (x :: xs)
  | x :: xs, y :: ys =>
    if lt x y then emit kl x (mergeL kl kr kb xs (y :: ys))
    else if lt y x then emit kr y (mergeL kl kr kb (x :: xs) ys)
    else emit kb x (mergeL kl kr kb xs ys)
termination_by xs ys => xs.length + ys.length
theorem mergeL_nil_right (kl kr kb : Bool) (xs : List α) :
    mergeL kl kr kb xs [] = keepIf kl xs := by
  cases xs with
  | nil => rw [mergeL]; cases kl <;> cases kr <;> rfl
  | cons x xs => rw [mergeL]
/-- What a membership test of a merge says, from the two tests of its arguments. -/
@[expose] def keep (kl kr kb a b : Bool) : Bool := (kl && a && !b) || (kr && !a && b) || (kb && a && b)
theorem mem_mergeL_sub (kl kr kb : Bool) (xs ys : List α) :
    ∀ z ∈ mergeL kl kr kb xs ys, z ∈ xs ∨ z ∈ ys := by
  fun_induction mergeL kl kr kb xs ys with
  | case1 ys =>
    intro z hz
    cases kr
    · cases hz
    · exact .inr hz
  | case2 x xs =>
    intro z hz
    cases kl
    · cases hz
    · exact .inl hz
  | case3 x xs y ys hlt ih =>
    intro z hz
    rcases mem_emit hz with rfl | hz
    · exact .inl List.mem_cons_self
    · rcases ih z hz with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr h
  | case4 x xs y ys hlt hgt ih =>
    intro z hz
    rcases mem_emit hz with rfl | hz
    · exact .inr List.mem_cons_self
    · rcases ih z hz with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
  | case5 x xs y ys hlt hgt ih =>
    intro z hz
    rcases mem_emit hz with rfl | hz
    · exact .inl List.mem_cons_self
    · rcases ih z hz with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr (List.mem_cons_of_mem _ h)
/-- A merge of sorted lists is sorted. -/
theorem sorted_mergeL (kl kr kb : Bool) (xs ys : List α) (hx : SortedList xs) (hy : SortedList ys) :
    SortedList (mergeL kl kr kb xs ys) := by
  fun_induction mergeL kl kr kb xs ys with
  | case1 ys => cases kr <;> first | exact hy | exact List.Pairwise.nil
  | case2 x xs => cases kl <;> first | exact hx | exact List.Pairwise.nil
  | case3 x xs y ys hlt ih =>
    refine sorted_emit (ih hx.tail hy) fun z hz => ?_
    rcases mem_mergeL_sub _ _ _ _ _ z hz with h | h
    · exact hx.head_lt z h
    · exact hy.lt_trans_all hlt z h
  | case4 x xs y ys hlt hgt ih =>
    refine sorted_emit (ih hx hy.tail) fun z hz => ?_
    rcases mem_mergeL_sub _ _ _ _ _ z hz with h | h
    · exact hx.lt_trans_all hgt z h
    · exact hy.head_lt z h
  | case5 x xs y ys hlt hgt ih =>
    have e : x = y := StrictLinearOrder.tri x y (by simpa using hlt) (by simpa using hgt)
    subst e
    refine sorted_emit (ih hx.tail hy.tail) fun z hz => ?_
    rcases mem_mergeL_sub _ _ _ _ _ z hz with h | h
    · exact hx.head_lt z h
    · exact hy.head_lt z h
/-- **Membership in a merge of sorted lists** is `keep` of the two memberships. -/
theorem memB_mergeL (kl kr kb : Bool) (xs ys : List α) (hx : SortedList xs) (hy : SortedList ys) (z : α) :
    memB z (mergeL kl kr kb xs ys) = keep kl kr kb (memB z xs) (memB z ys) := by
  fun_induction mergeL kl kr kb xs ys with
  | case1 ys => cases kr <;> cases kl <;> cases kb <;> simp [keep, keepIf, memB_nil]
  | case2 x xs => cases kr <;> cases kl <;> cases kb <;> simp [keep, keepIf, memB_nil]
  | case3 x xs y ys hlt ih =>
    rw [memB_emit, ih hx.tail hy, memB_cons z x xs]
    cases e : eqv z x
    · simp
    · have ez : z = x := eqv_iff.1 e
      subst ez
      have h₁ : memB z xs = false := memB_eq_false_of_lt_all hx.head_lt
      have h₂ : memB z (y :: ys) = false := memB_eq_false_of_lt_all (hy.lt_trans_all hlt)
      rw [h₁, h₂]
      cases kl <;> cases kr <;> cases kb <;> rfl
  | case4 x xs y ys hlt hgt ih =>
    rw [memB_emit, ih hx hy.tail, memB_cons z y ys]
    cases e : eqv z y
    · simp
    · have ez : z = y := eqv_iff.1 e
      subst ez
      have h₁ : memB z ys = false := memB_eq_false_of_lt_all hy.head_lt
      have h₂ : memB z (x :: xs) = false := memB_eq_false_of_lt_all (hx.lt_trans_all hgt)
      rw [h₁, h₂]
      cases kl <;> cases kr <;> cases kb <;> rfl
  | case5 x xs y ys hlt hgt ih =>
    have e : x = y := StrictLinearOrder.tri x y (by simpa using hlt) (by simpa using hgt)
    subst e
    rw [memB_emit, ih hx.tail hy.tail, memB_cons z x xs, memB_cons z x ys]
    cases e : eqv z x
    · simp
    · have ez : z = x := eqv_iff.1 e
      subst ez
      have h₁ : memB z xs = false := memB_eq_false_of_lt_all hx.head_lt
      have h₂ : memB z ys = false := memB_eq_false_of_lt_all hy.head_lt
      rw [h₁, h₂]
      cases kl <;> cases kr <;> cases kb <;> rfl
/-- Two strictly increasing lists with the same members are the same list. -/
theorem SortedList.ext_memB : ∀ {xs ys : List α}, SortedList xs → SortedList ys →
    (∀ z, memB z xs = memB z ys) → xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, h => by
    have := h y
    rw [memB_nil, memB_cons, eqv_self] at this
    cases this
  | x :: xs, [], _, _, h => by
    have := h x
    rw [memB_nil, memB_cons, eqv_self] at this
    cases this
  | x :: xs, y :: ys, hx, hy, h => by
    have exy : x = y := by
      cases e : eqv x y
      · have hxy : memB x ys = true := by
          have := h x
          rw [memB_cons, memB_cons, eqv_self, e] at this
          simpa using this.symm
        have hyx : memB y xs = true := by
          have := h y
          rw [memB_cons, memB_cons, eqv_self] at this
          have e' : eqv y x = false := by
            cases e' : eqv y x
            · rfl
            · rw [eqv_iff.1 e', eqv_self] at e; cases e
          rw [e'] at this
          simpa using this
        have h₁ := hy.head_lt x (memB_iff.1 hxy)
        have h₂ := hx.head_lt y (memB_iff.1 hyx)
        rw [StrictLinearOrder.asymm h₁] at h₂
        cases h₂
      · exact eqv_iff.1 e
    subst exy
    have ht : xs = ys := SortedList.ext_memB hx.tail hy.tail fun z => by
      have := h z
      rw [memB_cons, memB_cons] at this
      cases e : eqv z x
      · simpa [e] using this
      · have ez : z = x := eqv_iff.1 e
        subst ez
        rw [memB_eq_false_of_lt_all hx.head_lt, memB_eq_false_of_lt_all hy.head_lt]
    rw [ht]
end Lists

/-! ## 4. Finite sets as strictly sorted arrays -/
/-- An extensional finite set: a membership predicate that is false off some list. -/
structure FinSetSpec (α : Type u) where
  /-- membership -/
  mem : α → Bool
  /-- the members lie in a list -/
  finite : ∃ l : List α, ∀ a, mem a = true → a ∈ l

namespace FinSetSpec
variable {α : Type u}
/-- Sets with the same members are equal. -/
theorem ext {s t : FinSetSpec α} (h : ∀ a, s.mem a = t.mem a) : s = t := by
  cases s
  cases t
  have e : _ = _ := funext h
  cases e; rfl
theorem ext_iff {s t : FinSetSpec α} : s = t ↔ ∀ a, s.mem a = t.mem a := ⟨fun h _ => h ▸ rfl, ext⟩
/-- The empty set. -/
@[expose] def empty : FinSetSpec α := ⟨fun _ => false, ⟨[], fun _ h => nomatch h⟩⟩
/-- `s ∪ t`, pointwise `||`. -/
@[expose] def union (s t : FinSetSpec α) : FinSetSpec α where
  mem a := s.mem a || t.mem a
  finite :=
    match s.finite, t.finite with
    | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, fun a h => by
      rcases Bool.or_eq_true_iff.1 h with h | h
      · exact List.mem_append_left _ (h₁ a h)
      · exact List.mem_append_right _ (h₂ a h)⟩
/-- `s ∩ t`, pointwise `&&`. -/
@[expose] def inter (s t : FinSetSpec α) : FinSetSpec α where
  mem a := s.mem a && t.mem a
  finite :=
    match s.finite with
    | ⟨l, h⟩ => ⟨l, fun a ha => h a (Bool.and_eq_true_iff.1 ha).1⟩
/-- `s \ t`, pointwise `&& !`. -/
@[expose] def diff (s t : FinSetSpec α) : FinSetSpec α where
  mem a := s.mem a && !t.mem a
  finite :=
    match s.finite with
    | ⟨l, h⟩ => ⟨l, fun a ha => h a (Bool.and_eq_true_iff.1 ha).1⟩
theorem mem_empty (a : α) : (empty : FinSetSpec α).mem a = false := rfl
theorem mem_union (s t : FinSetSpec α) (a : α) : (s.union t).mem a = (s.mem a || t.mem a) := rfl
theorem mem_inter (s t : FinSetSpec α) (a : α) : (s.inter t).mem a = (s.mem a && t.mem a) := rfl
theorem mem_diff (s t : FinSetSpec α) (a : α) : (s.diff t).mem a = (s.mem a && !t.mem a) := rfl
/-- The members of a list. -/
@[expose] def ofList [StrictLinearOrder α] (l : List α) : FinSetSpec α :=
  ⟨fun z => memB z l, ⟨l, fun _ h => memB_iff.1 h⟩⟩
theorem mem_ofList [StrictLinearOrder α] (l : List α) (z : α) : (ofList l).mem z = memB z l := rfl
end FinSetSpec

section Arrays
variable {α : Type u} [StrictLinearOrder α]
/-- Strictly increasing. -/
abbrev SortedArray (a : Array α) : Prop := SortedList a.toList
theorem SortedArray.lt_of_lt {a : Array α} (hs : SortedArray a) {i j : Nat} (hij : i < j) (hj : j < a.size) :
    lt (a[i]'(Nat.lt_trans hij hj)) a[j] = true :=
  List.pairwise_iff_getElem.1 hs i j (by simpa using Nat.lt_trans hij hj) (by simpa using hj) hij
/-- **The refinement**: a strictly increasing array stands for the set of its elements. -/
@[expose] def sortedArraySetRefinement : DataRefinement (FinSetSpec α) (Array α) where
  WF := SortedArray
  alpha a _ := FinSetSpec.ofList a.toList
/-- A strictly sorted array, read as a finite set. -/
abbrev SortedArraySet (α : Type u) [StrictLinearOrder α] : Type u := PackedExec (sortedArraySetRefinement (α := α))
theorem refines_sortedArraySet {s : FinSetSpec α} {a : Array α} :
    Refines sortedArraySetRefinement s a ↔ SortedArray a ∧ FinSetSpec.ofList a.toList = s :=
  ⟨fun ⟨h, e⟩ => ⟨h, e⟩, fun ⟨h, e⟩ => ⟨h, e⟩⟩
/-- Binary search for `x` in `a[lo, hi)`. -/
def bsearch (a : Array α) (x : α) (lo hi : Nat) (hhi : hi ≤ a.size) : Bool :=
  if h : lo < hi then
    if lt (a[(lo + hi) / 2]'(by omega)) x then bsearch a x ((lo + hi) / 2 + 1) hi hhi
    else if lt x (a[(lo + hi) / 2]'(by omega)) then bsearch a x lo ((lo + hi) / 2) (by omega)
    else true
  else false
termination_by hi - lo
decreasing_by all_goals omega
/-- Membership by binary search: `O(log n)` comparisons, reading the array in place. -/
@[expose] def containsFast (a : Array α) (x : α) : Bool := bsearch a x 0 a.size (Nat.le_refl _)
theorem bsearch_iff {a : Array α} (hs : SortedArray a) (x : α) (lo hi : Nat) (hhi : hi ≤ a.size) :
    bsearch a x lo hi hhi = true ↔ ∃ i, ∃ h : i < a.size, lo ≤ i ∧ i < hi ∧ a[i] = x := by
  rw [bsearch]
  split
  · rename_i hlo
    have hm : (lo + hi) / 2 < a.size := by omega
    split
    · rename_i hlt
      rw [bsearch_iff hs x ((lo + hi) / 2 + 1) hi hhi]
      constructor
      · rintro ⟨i, h, h₁, h₂, e⟩
        exact ⟨i, h, by omega, h₂, e⟩
      · rintro ⟨i, h, h₁, h₂, e⟩
        refine ⟨i, h, ?_, h₂, e⟩
        apply Nat.lt_of_not_le
        intro hle
        have hix : lt a[i] (a[(lo + hi) / 2]'hm) = true ∨ i = (lo + hi) / 2 := by
          rcases Nat.lt_or_eq_of_le hle with hl | he
          · exact .inl (hs.lt_of_lt hl hm)
          · exact .inr he
        have hxx : lt x x = true := by
          rcases hix with hl | he
          · have := StrictLinearOrder.trans _ _ _ hl hlt
            rwa [e] at this
          · subst he
            rwa [e] at hlt
        rw [StrictLinearOrder.irrefl] at hxx
        cases hxx
    · split
      · rename_i hlt hgt
        rw [bsearch_iff hs x lo ((lo + hi) / 2) (by omega)]
        constructor
        · rintro ⟨i, h, h₁, h₂, e⟩
          exact ⟨i, h, h₁, by omega, e⟩
        · rintro ⟨i, h, h₁, h₂, e⟩
          refine ⟨i, h, h₁, ?_, e⟩
          apply Nat.lt_of_not_le
          intro hle
          have hix : lt (a[(lo + hi) / 2]'hm) a[i] = true ∨ i = (lo + hi) / 2 := by
            rcases Nat.lt_or_eq_of_le hle with hl | he
            · exact .inl (hs.lt_of_lt hl h)
            · exact .inr he.symm
          have hxx : lt x x = true := by
            rcases hix with hl | he
            · rw [e] at hl
              exact StrictLinearOrder.trans _ _ _ hgt hl
            · subst he
              rwa [e] at hgt
          rw [StrictLinearOrder.irrefl] at hxx
          cases hxx
      · rename_i hlt hgt
        have e : a[(lo + hi) / 2]'hm = x := StrictLinearOrder.tri _ _ (by simpa using hlt) (by simpa using hgt)
        exact ⟨fun _ => ⟨(lo + hi) / 2, hm, by omega, by omega, e⟩, fun _ => rfl⟩
  · rename_i hlo
    constructor
    · intro h; cases h
    · rintro ⟨i, _, h₁, h₂, _⟩
      omega
termination_by hi - lo
decreasing_by all_goals omega
/-- On a sorted array the binary search is membership. -/
theorem containsFast_eq_memB {a : Array α} (hs : SortedArray a) (x : α) :
    containsFast a x = memB x a.toList := by
  rw [Bool.eq_iff_iff, containsFast, bsearch_iff hs, memB_iff, Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, h, _, _, e⟩
    exact ⟨i, h, e⟩
  · rintro ⟨i, h, e⟩
    exact ⟨i, h, Nat.zero_le _, h, e⟩
/-- **`containsFast` refines membership.** -/
theorem containsFast_eq_spec (x : α) :
    PredRefines sortedArraySetRefinement (fun s : FinSetSpec α => s.mem x) (fun a => containsFast a x) := by
  rintro s a ⟨hs, rfl⟩
  exact containsFast_eq_memB hs x
omit [StrictLinearOrder α] in
theorem array_drop_cons (a : Array α) (i : Nat) (h : i < a.size) :
    a.toList.drop i = a[i] :: a.toList.drop (i + 1) := by
  have h' : i < a.toList.length := by simpa using h
  rw [List.drop_eq_getElem_cons h']; rfl
omit [StrictLinearOrder α] in
theorem array_drop_nil (a : Array α) (i : Nat) (h : ¬i < a.size) : a.toList.drop i = [] := by
  apply List.drop_eq_nil_of_le
  have : a.toList.length = a.size := Array.length_toList; omega
/-- Push `a[i], a[i+1], …` onto `out`. -/
def pushFrom (a : Array α) (i : Nat) (out : Array α) : Array α :=
  if h : i < a.size then pushFrom a (i + 1) (out.push a[i]) else out
termination_by a.size - i
omit [StrictLinearOrder α] in
theorem pushFrom_toList (a : Array α) (i : Nat) (out : Array α) :
    (pushFrom a i out).toList = out.toList ++ a.toList.drop i := by
  rw [pushFrom]
  split
  · rename_i h
    rw [pushFrom_toList a (i + 1), Array.toList_push, array_drop_cons a i h, List.append_assoc]; rfl
  · rename_i h
    rw [array_drop_nil a i h, List.append_nil]
termination_by a.size - i
/-- Push when the flag is set. -/
@[expose] def pushIf (k : Bool) (out : Array α) (x : α) : Array α := if k then out.push x else out
omit [StrictLinearOrder α] in
theorem pushIf_toList (k : Bool) (out : Array α) (x : α) (l : List α) :
    (pushIf k out x).toList ++ l = out.toList ++ emit k x l := by
  cases k
  · rfl
  · simp [pushIf, emit]
/-- The two-pointer merge: one pass over `a` from `i` and `b` from `j`, pushing onto `out` an element
found only in `a` when `kl`, only in `b` when `kr`, in both when `kb`. `O(n + m)` comparisons. -/
def mergeLoop (kl kr kb : Bool) (a b : Array α) (i j : Nat) (out : Array α) : Array α :=
  if hi : i < a.size then
    if hj : j < b.size then
      if lt a[i] b[j] then mergeLoop kl kr kb a b (i + 1) j (pushIf kl out a[i])
      else if lt b[j] a[i] then mergeLoop kl kr kb a b i (j + 1) (pushIf kr out b[j])
      else mergeLoop kl kr kb a b (i + 1) (j + 1) (pushIf kb out a[i])
    else if kl then pushFrom a i out else out
  else if kr then pushFrom b j out else out
termination_by (a.size - i) + (b.size - j)
decreasing_by all_goals omega
/-- **The loop is the list merge**, appended to what was already pushed. -/
theorem mergeLoop_toList (kl kr kb : Bool) (a b : Array α) (i j : Nat) (out : Array α) :
    (mergeLoop kl kr kb a b i j out).toList =
      out.toList ++ mergeL kl kr kb (a.toList.drop i) (b.toList.drop j) := by
  rw [mergeLoop]
  split
  · rename_i hi
    split
    · rename_i hj
      have ea := array_drop_cons a i hi
      have eb := array_drop_cons b j hj
      split
      · rename_i hlt
        rw [mergeLoop_toList kl kr kb a b (i + 1) j, pushIf_toList, ea, eb, mergeL]
        simp only [hlt, ↓reduceIte]
      · split
        · rename_i hlt hgt
          rw [mergeLoop_toList kl kr kb a b i (j + 1), pushIf_toList, ea, eb, mergeL]
          simp [hlt, hgt]
        · rename_i hlt hgt
          rw [mergeLoop_toList kl kr kb a b (i + 1) (j + 1), pushIf_toList, ea, eb, mergeL]
          simp [hlt, hgt]
    · rename_i hj
      rw [array_drop_nil b j hj, mergeL_nil_right]
      cases kl
      · simp [keepIf]
      · simp [keepIf, pushFrom_toList]
  · rename_i hi
    rw [array_drop_nil a i hi, mergeL]
    cases kr
    · simp [keepIf]
    · simp [keepIf, pushFrom_toList]
termination_by (a.size - i) + (b.size - j)
decreasing_by all_goals omega
/-- The merge of two arrays into a fresh array of capacity `a.size + b.size`. -/
@[expose] def mergeFast (kl kr kb : Bool) (a b : Array α) : Array α :=
  mergeLoop kl kr kb a b 0 0 (Array.emptyWithCapacity (a.size + b.size))
theorem mergeFast_toList (kl kr kb : Bool) (a b : Array α) :
    (mergeFast kl kr kb a b).toList = mergeL kl kr kb a.toList b.toList := by
  rw [mergeFast, mergeLoop_toList]; rfl
/-- `a ∪ b` in one pass. -/
@[expose] def unionFast (a b : Array α) : Array α := mergeFast true true true a b
/-- `a ∩ b` in one pass. -/
@[expose] def interFast (a b : Array α) : Array α := mergeFast false false true a b
/-- `a \ b` in one pass. -/
@[expose] def diffFast (a b : Array α) : Array α := mergeFast true false false a b
/-- The set a merge computes, from its two arguments. -/
@[expose] def FinSetSpec.merge (kl kr kb : Bool) (s t : FinSetSpec α) : FinSetSpec α where
  mem z := keep kl kr kb (s.mem z) (t.mem z)
  finite := (s.union t).finite.imp fun l h a ha => h a (by
    change (s.mem a || t.mem a) = true
    revert ha
    unfold keep
    cases s.mem a <;> cases t.mem a <;> simp)
/-- **Every merge refines its pointwise set operation.** -/
theorem mergeFast_refines (kl kr kb : Bool) :
    BinaryRefines (sortedArraySetRefinement (α := α)) sortedArraySetRefinement sortedArraySetRefinement
      (FinSetSpec.merge kl kr kb) (mergeFast kl kr kb) := by
  rintro s a t b ⟨ha, rfl⟩ ⟨hb, rfl⟩
  have hw : SortedArray (mergeFast kl kr kb a b) := by
    unfold SortedArray
    rw [mergeFast_toList]
    exact sorted_mergeL kl kr kb _ _ ha hb
  refine ⟨hw, FinSetSpec.ext fun z => ?_⟩
  change memB z (mergeFast kl kr kb a b).toList = _
  rw [mergeFast_toList, memB_mergeL kl kr kb _ _ ha hb]; rfl
omit [StrictLinearOrder α] in
theorem FinSetSpec.merge_union (s t : FinSetSpec α) : FinSetSpec.merge true true true s t = s.union t :=
  FinSetSpec.ext fun z => by
    change keep true true true (s.mem z) (t.mem z) = (s.mem z || t.mem z)
    cases s.mem z <;> cases t.mem z <;> rfl
omit [StrictLinearOrder α] in
theorem FinSetSpec.merge_inter (s t : FinSetSpec α) : FinSetSpec.merge false false true s t = s.inter t :=
  FinSetSpec.ext fun z => by
    change keep false false true (s.mem z) (t.mem z) = (s.mem z && t.mem z)
    cases s.mem z <;> cases t.mem z <;> rfl
omit [StrictLinearOrder α] in
theorem FinSetSpec.merge_diff (s t : FinSetSpec α) : FinSetSpec.merge true false false s t = s.diff t :=
  FinSetSpec.ext fun z => by
    change keep true false false (s.mem z) (t.mem z) = (s.mem z && !t.mem z)
    cases s.mem z <;> cases t.mem z <;> rfl
/-- **`unionFast` refines `∪`.** -/
theorem unionFast_eq_spec :
    BinaryRefines (sortedArraySetRefinement (α := α)) sortedArraySetRefinement sortedArraySetRefinement
      FinSetSpec.union unionFast :=
  fun s a t b ha hb => FinSetSpec.merge_union s t ▸ mergeFast_refines true true true s a t b ha hb
/-- **`interFast` refines `∩`.** -/
theorem interFast_eq_spec :
    BinaryRefines (sortedArraySetRefinement (α := α)) sortedArraySetRefinement sortedArraySetRefinement
      FinSetSpec.inter interFast :=
  fun s a t b ha hb => FinSetSpec.merge_inter s t ▸ mergeFast_refines false false true s a t b ha hb
/-- **`diffFast` refines `\`.** -/
theorem diffFast_eq_spec :
    BinaryRefines (sortedArraySetRefinement (α := α)) sortedArraySetRefinement sortedArraySetRefinement
      FinSetSpec.diff diffFast :=
  fun s a t b ha hb => FinSetSpec.merge_diff s t ▸ mergeFast_refines true false false s a t b ha hb

namespace SortedArraySet
/-- The empty set. -/
@[expose] def empty : SortedArraySet α := ⟨#[], List.Pairwise.nil⟩
/-- Membership, by binary search. -/
@[expose] def contains (p : SortedArraySet α) (x : α) : Bool := containsFast p.val x
/-- Union, by one merge. -/
@[expose] def union (p q : SortedArraySet α) : SortedArraySet α := unionFast_eq_spec.lift p q
/-- Intersection, by one merge. -/
@[expose] def inter (p q : SortedArraySet α) : SortedArraySet α := interFast_eq_spec.lift p q
/-- Difference, by one merge. -/
@[expose] def diff (p q : SortedArraySet α) : SortedArraySet α := diffFast_eq_spec.lift p q
theorem empty_toSpec : (empty : SortedArraySet α).toSpec = FinSetSpec.empty := rfl
theorem contains_eq_spec (p : SortedArraySet α) (x : α) : p.contains x = p.toSpec.mem x :=
  (containsFast_eq_spec x).packed p
/-- **`(p ∪ q)` stands for the union of what `p` and `q` stand for.** -/
theorem unionFast_toSpec (p q : SortedArraySet α) : (p.union q).toSpec = p.toSpec.union q.toSpec :=
  unionFast_eq_spec.lift_toSpec p q
theorem interFast_toSpec (p q : SortedArraySet α) : (p.inter q).toSpec = p.toSpec.inter q.toSpec :=
  interFast_eq_spec.lift_toSpec p q
theorem diffFast_toSpec (p q : SortedArraySet α) : (p.diff q).toSpec = p.toSpec.diff q.toSpec :=
  diffFast_eq_spec.lift_toSpec p q
/-- **The representation is canonical**: sorted arrays standing for the same set are equal. -/
theorem toSpec_injective {p q : SortedArraySet α} (h : p.toSpec = q.toSpec) : p = q := by
  apply Subtype.ext
  apply Array.toList_inj.1
  exact SortedList.ext_memB p.property q.property fun z => congrArg (fun s : FinSetSpec α => s.mem z) h
theorem eq_iff_toSpec {p q : SortedArraySet α} : p = q ↔ p.toSpec = q.toSpec := ⟨fun h => h ▸ rfl, toSpec_injective⟩
end SortedArraySet
end Arrays

/-! ## 5. Word lists as little-endian bytes -/
/-- Byte `k` of a word, least significant first. -/
@[expose] def u64Byte (w : UInt64) (k : Nat) : UInt8 := (w >>> (8 * k).toUInt64).toUInt8
/-- The eight bytes of a word, least significant first. -/
@[expose] def u64Bytes (w : UInt64) : List UInt8 :=
  [u64Byte w 0, u64Byte w 1, u64Byte w 2, u64Byte w 3, u64Byte w 4, u64Byte w 5, u64Byte w 6, u64Byte w 7]
/-- The word with these bytes, least significant first. -/
@[expose] def u64OfBytes (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : UInt8) : UInt64 :=
  (((((((b₇.toUInt64 <<< 8 + b₆.toUInt64) <<< 8 + b₅.toUInt64) <<< 8 + b₄.toUInt64) <<< 8 +
    b₃.toUInt64) <<< 8 + b₂.toUInt64) <<< 8 + b₁.toUInt64) <<< 8) + b₀.toUInt64
theorem u64Byte_toNat (w : UInt64) (k : Nat) (hk : k < 8) :
    (u64Byte w k).toNat = w.toNat / 2 ^ (8 * k) % 256 := by
  have h8 : (8 * k).toUInt64.toNat = 8 * k := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [u64Byte, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h8, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : 8 * k < 64)]
/-- **A word is its eight bytes.** -/
theorem u64OfBytes_u64Byte (w : UInt64) :
    u64OfBytes (u64Byte w 0) (u64Byte w 1) (u64Byte w 2) (u64Byte w 3) (u64Byte w 4) (u64Byte w 5)
      (u64Byte w 6) (u64Byte w 7) = w := by
  apply UInt64.toNat_inj.1
  have hw := w.toNat_lt
  simp only [u64OfBytes, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, Nat.shiftLeft_eq,
    u64Byte_toNat w _ (by decide : 0 < 8), u64Byte_toNat w _ (by decide : 1 < 8),
    u64Byte_toNat w _ (by decide : 2 < 8), u64Byte_toNat w _ (by decide : 3 < 8),
    u64Byte_toNat w _ (by decide : 4 < 8), u64Byte_toNat w _ (by decide : 5 < 8),
    u64Byte_toNat w _ (by decide : 6 < 8), u64Byte_toNat w _ (by decide : 7 < 8)]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow, Nat.reduceMul]; omega
theorem u64Byte_zero (k : Nat) (hk : k < 8) : u64Byte 0 k = 0 := by
  apply UInt8.toNat_inj.1
  rw [u64Byte_toNat 0 k hk]; simp
/-- Append the eight bytes of a word. -/
@[expose] def pushU64LE (out : ByteArray) (w : UInt64) : ByteArray :=
  (((((((out.push (u64Byte w 0)).push (u64Byte w 1)).push (u64Byte w 2)).push (u64Byte w 3)).push
    (u64Byte w 4)).push (u64Byte w 5)).push (u64Byte w 6)).push (u64Byte w 7)
/-- The words, eight little-endian bytes each. -/
@[expose] def packU64LE (l : List UInt64) : ByteArray :=
  l.foldl pushU64LE (ByteArray.emptyWithCapacity (8 * l.length))
/-- Byte `j`, `0` past the end. -/
@[expose] def byteAt (b : ByteArray) (j : Nat) : UInt8 := if h : j < b.size then b[j] else 0
/-- Word `i` of a little-endian byte string: eight reads at `8 * i`, in constant time. -/
@[expose] def readU64LE (b : ByteArray) (i : Nat) : UInt64 :=
  u64OfBytes (byteAt b (8 * i)) (byteAt b (8 * i + 1)) (byteAt b (8 * i + 2)) (byteAt b (8 * i + 3))
    (byteAt b (8 * i + 4)) (byteAt b (8 * i + 5)) (byteAt b (8 * i + 6)) (byteAt b (8 * i + 7))
theorem byteAt_eq_getD (b : ByteArray) (j : Nat) : byteAt b j = b.data.toList.getD j 0 := by
  unfold byteAt
  split
  · rename_i h
    have h' : j < b.data.toList.length := by rw [Array.length_toList]; exact h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h']; rfl
  · rename_i h
    have h' : b.data.toList.length ≤ j := by
      have : b.data.toList.length = b.size := (by rw [Array.length_toList]; rfl); omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h']; rfl
theorem byteAt_of_size_le {b : ByteArray} {j : Nat} (h : b.size ≤ j) : byteAt b j = 0 := by
  unfold byteAt
  split
  · omega
  · rfl
theorem pushU64LE_toList (out : ByteArray) (w : UInt64) :
    (pushU64LE out w).data.toList = out.data.toList ++ u64Bytes w := by
  simp [pushU64LE, u64Bytes, ByteArray.data_push]
theorem foldl_pushU64LE_toList (l : List UInt64) (out : ByteArray) :
    (l.foldl pushU64LE out).data.toList = out.data.toList ++ l.flatMap u64Bytes := by
  induction l generalizing out with
  | nil => simp
  | cons w l ih => rw [List.foldl_cons, ih, pushU64LE_toList, List.flatMap_cons, List.append_assoc]
theorem packU64LE_toList (l : List UInt64) : (packU64LE l).data.toList = l.flatMap u64Bytes := by
  rw [packU64LE, foldl_pushU64LE_toList]; rfl
theorem length_flatMap_u64Bytes (l : List UInt64) : (l.flatMap u64Bytes).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [u64Bytes, List.length_cons, List.length_nil]; omega
theorem packU64LE_size (l : List UInt64) : (packU64LE l).size = 8 * l.length := by
  have : (packU64LE l).size = (packU64LE l).data.toList.length := by rw [Array.length_toList]; rfl
  rw [this, packU64LE_toList, length_flatMap_u64Bytes]
theorem getD_cons8 {β : Type u} (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : β) (r : List β) (n : Nat) (d : β) :
    (a₀ :: a₁ :: a₂ :: a₃ :: a₄ :: a₅ :: a₆ :: a₇ :: r).getD (n + 8) d = r.getD n d := rfl
theorem getD_flatMap_u64Bytes (l : List UInt64) (i k : Nat) (hk : k < 8) :
    (l.flatMap u64Bytes).getD (8 * i + k) 0 = u64Byte (l.getD i 0) k := by
  induction l generalizing i with
  | nil => exact (u64Byte_zero k hk).symm
  | cons w l ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    | succ i =>
      have e : 8 * (i + 1) + k = 8 * i + k + 8 := by omega
      rw [e]
      exact (getD_cons8 _ _ _ _ _ _ _ _ _ _ _).trans (ih i)
theorem byteAt_packU64LE (l : List UInt64) (i k : Nat) (hk : k < 8) :
    byteAt (packU64LE l) (8 * i + k) = u64Byte (l.getD i 0) k := by
  rw [byteAt_eq_getD, packU64LE_toList, getD_flatMap_u64Bytes l i k hk]
/-- **Reading word `i` of a packed list gives its `i`-th word** (`0` past the end). -/
theorem readU64LE_packU64LE (l : List UInt64) (i : Nat) : readU64LE (packU64LE l) i = l.getD i 0 := by
  unfold readU64LE
  rw [show 8 * i = 8 * i + 0 from rfl, byteAt_packU64LE l i 0 (by decide), byteAt_packU64LE l i 1 (by decide),
    byteAt_packU64LE l i 2 (by decide), byteAt_packU64LE l i 3 (by decide), byteAt_packU64LE l i 4 (by decide),
    byteAt_packU64LE l i 5 (by decide), byteAt_packU64LE l i 6 (by decide), byteAt_packU64LE l i 7 (by decide)]
  exact u64OfBytes_u64Byte _
/-- The words of a byte string whose size is a multiple of eight. -/
@[expose] def unpackU64LE (b : ByteArray) : List UInt64 := (List.range (b.size / 8)).map (readU64LE b)
/-- **The refinement**: a byte string of size a multiple of eight stands for its little-endian
words. -/
@[expose] def u64BytesRefinement : DataRefinement (List UInt64) ByteArray where
  WF b := b.size % 8 = 0
  alpha b _ := unpackU64LE b
theorem unpackU64LE_length (b : ByteArray) : (unpackU64LE b).length = b.size / 8 := by simp [unpackU64LE]
theorem unpackU64LE_getD (b : ByteArray) (hb : b.size % 8 = 0) (i : Nat) :
    (unpackU64LE b).getD i 0 = readU64LE b i := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < b.size / 8
  · rw [List.getElem?_eq_getElem (by rw [unpackU64LE_length]; exact hi)]
    simp [unpackU64LE]
  · rw [List.getElem?_eq_none (by rw [unpackU64LE_length]; omega)]
    unfold readU64LE
    rw [byteAt_of_size_le (by omega), byteAt_of_size_le (by omega), byteAt_of_size_le (by omega),
      byteAt_of_size_le (by omega), byteAt_of_size_le (by omega), byteAt_of_size_le (by omega),
      byteAt_of_size_le (by omega), byteAt_of_size_le (by omega)]
    rfl
/-- **`packU64LE` builds a representation of its argument.** -/
theorem packU64LE_refines (l : List UInt64) : Refines u64BytesRefinement l (packU64LE l) := by
  have hs := packU64LE_size l
  refine ⟨by change (packU64LE l).size % 8 = 0; omega, ?_⟩
  change unpackU64LE (packU64LE l) = l
  apply List.ext_getElem
  · rw [unpackU64LE_length, hs]; omega
  · intro i h₁ h₂
    simp only [unpackU64LE, List.getElem_map, List.getElem_range, readU64LE_packU64LE]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]; rfl
/-- **Constant-time indexing refines list indexing.** -/
theorem readU64LE_eq_spec (i : Nat) :
    ObsRefines u64BytesRefinement (fun l : List UInt64 => l.getD i 0) (fun b => readU64LE b i) := by
  rintro l b ⟨hb, rfl⟩
  exact (unpackU64LE_getD b hb i).symm
/-- The packed word list. -/
@[expose] def U64Bytes.ofList (l : List UInt64) : PackedExec u64BytesRefinement := (packU64LE_refines l).pack
theorem U64Bytes.ofList_toSpec (l : List UInt64) : (U64Bytes.ofList l).toSpec = l :=
  (packU64LE_refines l).pack_toSpec

/-! ## 6. Face ideals of the 3-cube
A face of the 3-cube fixes each of three interval variables at `0`, at `1`, or leaves it free (`*`):
`{0,1,*}^3`, 27 faces, ordered by inclusion (`0 ≤ *`, `1 ≤ *`). A cofibration is a union of faces, so
it is a downward-closed set of them. A truth table over the 8 vertices cannot tell the boundary
`(i = 0) ∨ (i = 1)` from the whole interval, since every vertex has `i = 0` or `i = 1`; a set of faces
can, because the face with `i` free is in neither `(i = 0)` nor `(i = 1)` (`boundary_ne_top`). -/
/-- A coordinate of a face: fixed at an endpoint, or free. -/
inductive Trit where
  | zero
  | one
  | star
  deriving @[expose] DecidableEq, Repr

namespace Trit
/-- `0 ≤ *`, `1 ≤ *`, and each is below itself. -/
@[expose] def le : Trit → Trit → Bool
  | _, .star => true
  | .zero, .zero => true
  | .one, .one => true
  | _, _ => false
@[expose] def isZero : Trit → Bool
  | .zero => true
  | _ => false
@[expose] def isOne : Trit → Bool
  | .one => true
  | _ => false
@[expose] def code : Trit → Nat
  | .zero => 0
  | .one => 1
  | .star => 2
/-- The coordinate a base-3 digit stands for. -/
@[expose] def ofCode (n : Nat) : Trit := if n % 3 = 0 then .zero else if n % 3 = 1 then .one else .star
theorem code_lt (t : Trit) : t.code < 3 := by cases t <;> decide
theorem le_refl (a : Trit) : a.le a = true := by cases a <;> rfl
theorem le_trans {a b c : Trit} : a.le b = true → b.le c = true → a.le c = true := by
  cases a <;> cases b <;> cases c <;> decide
theorem le_antisymm {a b : Trit} : a.le b = true → b.le a = true → a = b := by cases a <;> cases b <;> decide
theorem isZero_of_le {a b : Trit} : a.le b = true → b.isZero = true → a.isZero = true := by
  cases a <;> cases b <;> decide
theorem isOne_of_le {a b : Trit} : a.le b = true → b.isOne = true → a.isOne = true := by
  cases a <;> cases b <;> decide
theorem isZero_and_isOne (a : Trit) : (a.isZero && a.isOne) = false := by cases a <;> rfl
end Trit
/-- A face of the 3-cube. -/
abbrev Trit3 : Type := Fin 3 → Trit
theorem fin3_cases {P : Fin 3 → Prop} (h₀ : P 0) (h₁ : P 1) (h₂ : P 2) : ∀ v, P v
  | ⟨0, _⟩ => h₀
  | ⟨1, _⟩ => h₁
  | ⟨2, _⟩ => h₂
  | ⟨n + 3, h⟩ => absurd h (by omega)

namespace Trit3
/-- Inclusion of faces, coordinatewise. -/
@[expose] def le (f g : Trit3) : Bool := (f 0).le (g 0) && (f 1).le (g 1) && (f 2).le (g 2)
/-- The bit a face has in a `BitVec 27`: its coordinates as base-3 digits. -/
@[expose] def index (f : Trit3) : Nat := (f 0).code + 3 * (f 1).code + 9 * (f 2).code
/-- The whole cube: every variable free. Bit 26. -/
@[expose] def generic : Trit3 := fun _ => .star
end Trit3
/-- Coordinate `v` of the face at bit `i`. -/
@[expose] def tritAt (i : Nat) (v : Fin 3) : Trit := Trit.ofCode (i / 3 ^ v.val)
/-- The face at bit `i`. -/
@[expose] def Trit3.ofIndex (i : Nat) : Trit3 := tritAt i

namespace Trit3
theorem index_lt (f : Trit3) : index f < 27 := by
  have h₀ := (f 0).code_lt
  have h₁ := (f 1).code_lt
  have h₂ := (f 2).code_lt
  unfold index; omega
theorem le_apply {f g : Trit3} (h : le f g = true) : ∀ v, (f v).le (g v) = true := by
  simp only [le, Bool.and_eq_true] at h
  exact fin3_cases h.1.1 h.1.2 h.2
theorem le_refl (f : Trit3) : le f f = true := by simp [le, Trit.le_refl]
theorem tritAt_index (f : Trit3) : ∀ v, tritAt (index f) v = f v := by
  unfold index
  apply fin3_cases
  all_goals
    generalize f 0 = a
    generalize f 1 = b
    generalize f 2 = c
    cases a <;> cases b <;> cases c <;> rfl
/-- A face is the face at its bit. -/
theorem ofIndex_index (f : Trit3) : ofIndex (index f) = f := funext (tritAt_index f)
/-- Bit `i < 27` is the bit of the face at it. -/
theorem index_ofIndex : ∀ i : Fin 27, index (ofIndex i.val) = i.val := by decide +kernel
theorem index_generic : index generic = 26 := rfl
end Trit3
/-- A cofibration of the 3-cube: a downward-closed set of faces. -/
structure FaceIdealSpec3 where
  /-- the faces it contains -/
  mem : Trit3 → Bool
  /-- with a face, every face inside it -/
  down : ∀ f g, Trit3.le f g = true → mem g = true → mem f = true

namespace FaceIdealSpec3
theorem ext {s t : FaceIdealSpec3} (h : ∀ f, s.mem f = t.mem f) : s = t := by
  cases s
  cases t
  have e : _ = _ := funext h
  cases e; rfl
theorem ext_iff {s t : FaceIdealSpec3} : s = t ↔ ∀ f, s.mem f = t.mem f := ⟨fun h _ => h ▸ rfl, ext⟩
/-- `⊥`: no face. -/
@[expose] def bot : FaceIdealSpec3 := ⟨fun _ => false, fun _ _ _ h => h⟩
/-- `⊤`: every face. -/
@[expose] def top : FaceIdealSpec3 := ⟨fun _ => true, fun _ _ _ h => h⟩
/-- `φ ∨ ψ`: the union. -/
@[expose] def join (s t : FaceIdealSpec3) : FaceIdealSpec3 where
  mem f := s.mem f || t.mem f
  down f g hfg h := by
    rw [Bool.or_eq_true] at h ⊢
    exact h.imp (s.down f g hfg) (t.down f g hfg)
/-- `φ ∧ ψ`: the intersection. -/
@[expose] def meet (s t : FaceIdealSpec3) : FaceIdealSpec3 where
  mem f := s.mem f && t.mem f
  down f g hfg h := by
    rw [Bool.and_eq_true] at h ⊢
    exact ⟨s.down f g hfg h.1, t.down f g hfg h.2⟩
/-- `(i_v = 0)`: the faces with variable `v` fixed at `0`. -/
@[expose] def varEq0 (v : Fin 3) : FaceIdealSpec3 where
  mem f := (f v).isZero
  down _ _ hfg h := Trit.isZero_of_le (Trit3.le_apply hfg v) h
/-- `(i_v = 1)`: the faces with variable `v` fixed at `1`. -/
@[expose] def varEq1 (v : Fin 3) : FaceIdealSpec3 where
  mem f := (f v).isOne
  down _ _ hfg h := Trit.isOne_of_le (Trit3.le_apply hfg v) h
theorem mem_bot (f : Trit3) : bot.mem f = false := rfl
theorem mem_top (f : Trit3) : top.mem f = true := rfl
theorem mem_join (s t : FaceIdealSpec3) (f : Trit3) : (s.join t).mem f = (s.mem f || t.mem f) := rfl
theorem mem_meet (s t : FaceIdealSpec3) (f : Trit3) : (s.meet t).mem f = (s.mem f && t.mem f) := rfl
theorem mem_varEq0 (v : Fin 3) (f : Trit3) : (varEq0 v).mem f = (f v).isZero := rfl
theorem mem_varEq1 (v : Fin 3) (f : Trit3) : (varEq1 v).mem f = (f v).isOne := rfl
end FaceIdealSpec3
/-- The number whose bit `i < n` is `p i`. -/
@[expose] def maskNat (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => maskNat p n ||| (if p n then 2 ^ n else 0)
theorem testBit_maskNat (p : Nat → Bool) (n i : Nat) : (maskNat p n).testBit i = (decide (i < n) && p i) := by
  induction n with
  | zero => simp [maskNat]
  | succ n ih =>
    rw [maskNat, Nat.testBit_or, ih]
    by_cases hin : i = n
    · subst hin
      cases hp : p i <;> simp
    · have hne : ¬n = i := fun h => hin h.symm
      have h1 : decide (i < n + 1) = decide (i < n) := by
        rw [decide_eq_decide]; omega
      rw [h1]
      cases hp : p n <;> simp [hne]
/-- The 27-bit word whose bit at each face is `p` of the face. -/
@[expose] def faceMask (p : Trit3 → Bool) : BitVec 27 := BitVec.ofNat 27 (maskNat (fun i => p (Trit3.ofIndex i)) 27)
theorem getLsbD_faceMask (p : Trit3 → Bool) (f : Trit3) : (faceMask p).getLsbD (Trit3.index f) = p f := by
  rw [faceMask, BitVec.getLsbD_ofNat, testBit_maskNat, Trit3.ofIndex_index]
  simp [Trit3.index_lt f]
/-- Downward closed: with the bit of a face, the bit of every face inside it. -/
@[expose] def FaceWF (b : BitVec 27) : Prop :=
  ∀ f g : Trit3, Trit3.le f g = true → b.getLsbD (Trit3.index g) = true → b.getLsbD (Trit3.index f) = true
/-- **The refinement**: a downward-closed 27-bit word stands for the set of faces whose bits it has. -/
@[expose] def faceIdeal3Refinement : DataRefinement FaceIdealSpec3 (BitVec 27) where
  WF := FaceWF
  alpha b h := ⟨fun f => b.getLsbD (Trit3.index f), h⟩
/-- A cofibration of the 3-cube as a 27-bit word. -/
abbrev FaceIdeal3 : Type := PackedExec faceIdeal3Refinement
theorem refines_faceIdeal3 {s : FaceIdealSpec3} {b : BitVec 27} :
    Refines faceIdeal3Refinement s b ↔ FaceWF b ∧ ∀ f, b.getLsbD (Trit3.index f) = s.mem f :=
  ⟨fun ⟨h, e⟩ => ⟨h, fun _ => e ▸ rfl⟩, fun ⟨h, e⟩ => ⟨h, FaceIdealSpec3.ext e⟩⟩
/-- **`|||` refines `∨`.** -/
theorem faceJoin_refines :
    BinaryRefines faceIdeal3Refinement faceIdeal3Refinement faceIdeal3Refinement FaceIdealSpec3.join
      (fun a b : BitVec 27 => a ||| b) := by
  rintro s a t b ⟨ha, rfl⟩ ⟨hb, rfl⟩
  refine refines_faceIdeal3.2 ⟨fun f g hfg hg => ?_, fun f => BitVec.getLsbD_or⟩
  rw [BitVec.getLsbD_or, Bool.or_eq_true] at hg ⊢
  exact hg.imp (ha f g hfg) (hb f g hfg)
/-- **`&&&` refines `∧`.** -/
theorem faceMeet_refines :
    BinaryRefines faceIdeal3Refinement faceIdeal3Refinement faceIdeal3Refinement FaceIdealSpec3.meet
      (fun a b : BitVec 27 => a &&& b) := by
  rintro s a t b ⟨ha, rfl⟩ ⟨hb, rfl⟩
  refine refines_faceIdeal3.2 ⟨fun f g hfg hg => ?_, fun f => BitVec.getLsbD_and⟩
  rw [BitVec.getLsbD_and, Bool.and_eq_true] at hg ⊢
  exact ⟨ha f g hfg hg.1, hb f g hfg hg.2⟩
theorem faceBot_refines : Refines faceIdeal3Refinement FaceIdealSpec3.bot 0#27 :=
  refines_faceIdeal3.2 ⟨fun _ _ _ h => (by rw [BitVec.getLsbD_zero] at h; cases h), fun _ => BitVec.getLsbD_zero⟩
theorem faceTop_refines : Refines faceIdeal3Refinement FaceIdealSpec3.top (BitVec.allOnes 27) :=
  have h : ∀ f : Trit3, (BitVec.allOnes 27).getLsbD (Trit3.index f) = true := fun f => by
    rw [BitVec.getLsbD_allOnes]
    exact decide_eq_true (Trit3.index_lt f)
  refines_faceIdeal3.2 ⟨fun f _ _ _ => h f, h⟩
/-- **Every cofibration has a word**: its mask. -/
theorem faceMask_refines (s : FaceIdealSpec3) : Refines faceIdeal3Refinement s (faceMask s.mem) :=
  refines_faceIdeal3.2 ⟨fun f g hfg hg => by
    rw [getLsbD_faceMask] at hg ⊢
    exact s.down f g hfg hg, getLsbD_faceMask s.mem⟩
/-- The word of `(i_v = 0)`. -/
@[expose] def varEq0Mask (v : Fin 3) : BitVec 27 := faceMask (FaceIdealSpec3.varEq0 v).mem
/-- The word of `(i_v = 1)`. -/
@[expose] def varEq1Mask (v : Fin 3) : BitVec 27 := faceMask (FaceIdealSpec3.varEq1 v).mem
/-- **The boundary is not the interval**, on the words: `(i_v = 0) ∨ (i_v = 1)` lacks bit 26, the
face with every variable free. Evaluated by the kernel. -/
theorem boundaryMask_ne_allOnes : ∀ v : Fin 3, varEq0Mask v ||| varEq1Mask v ≠ BitVec.allOnes 27 := by
  decide +kernel

namespace FaceIdeal3
/-- `⊥`, the word `0`. -/
@[expose] def bot : FaceIdeal3 := faceBot_refines.pack
/-- `⊤`, the word of all ones. -/
@[expose] def top : FaceIdeal3 := faceTop_refines.pack
/-- `φ ∨ ψ`, one `|||`. -/
@[expose] def join (a b : FaceIdeal3) : FaceIdeal3 := faceJoin_refines.lift a b
/-- `φ ∧ ψ`, one `&&&`. -/
@[expose] def meet (a b : FaceIdeal3) : FaceIdeal3 := faceMeet_refines.lift a b
/-- The word of a cofibration. -/
@[expose] def ofSpec (s : FaceIdealSpec3) : FaceIdeal3 := (faceMask_refines s).pack
/-- `(i_v = 0)`. -/
@[expose] def varEq0 (v : Fin 3) : FaceIdeal3 := ofSpec (FaceIdealSpec3.varEq0 v)
/-- `(i_v = 1)`. -/
@[expose] def varEq1 (v : Fin 3) : FaceIdeal3 := ofSpec (FaceIdealSpec3.varEq1 v)
theorem bot_toSpec : bot.toSpec = FaceIdealSpec3.bot := faceBot_refines.pack_toSpec
theorem top_toSpec : top.toSpec = FaceIdealSpec3.top := faceTop_refines.pack_toSpec
theorem join_toSpec (a b : FaceIdeal3) : (a.join b).toSpec = a.toSpec.join b.toSpec :=
  faceJoin_refines.lift_toSpec a b
theorem meet_toSpec (a b : FaceIdeal3) : (a.meet b).toSpec = a.toSpec.meet b.toSpec :=
  faceMeet_refines.lift_toSpec a b
theorem ofSpec_toSpec (s : FaceIdealSpec3) : (ofSpec s).toSpec = s := (faceMask_refines s).pack_toSpec
theorem varEq0_toSpec (v : Fin 3) : (varEq0 v).toSpec = FaceIdealSpec3.varEq0 v := ofSpec_toSpec _
theorem varEq1_toSpec (v : Fin 3) : (varEq1 v).toSpec = FaceIdealSpec3.varEq1 v := ofSpec_toSpec _
/-- **The word is canonical**: words standing for the same cofibration are equal. -/
theorem toSpec_injective {a b : FaceIdeal3} (h : a.toSpec = b.toSpec) : a = b := by
  apply Subtype.ext
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun s : FaceIdealSpec3 => s.mem (Trit3.ofIndex i)) h
  change a.val.getLsbD (Trit3.index (Trit3.ofIndex i)) = b.val.getLsbD (Trit3.index (Trit3.ofIndex i)) at this
  rwa [Trit3.index_ofIndex ⟨i, hi⟩] at this
theorem eq_iff_toSpec {a b : FaceIdeal3} : a = b ↔ a.toSpec = b.toSpec := ⟨fun h => h ▸ rfl, toSpec_injective⟩
theorem toSpec_ofSpec (a : FaceIdeal3) : ofSpec a.toSpec = a := toSpec_injective (ofSpec_toSpec _)
/-- **`∂𝕀 ≠ 𝕀`**: the boundary `(i_v = 0) ∨ (i_v = 1)` is not `⊤`. -/
theorem boundary_ne_top (v : Fin 3) : (varEq0 v).join (varEq1 v) ≠ top :=
  fun h => boundaryMask_ne_allOnes v (congrArg Subtype.val h)
/-- The face that tells them apart: the whole cube is in `⊤` and not in the boundary. -/
theorem generic_not_mem_boundary (v : Fin 3) :
    ((varEq0 v).join (varEq1 v)).toSpec.mem Trit3.generic = false := by
  rw [join_toSpec, varEq0_toSpec, varEq1_toSpec]; rfl
/-- `(i_v = 0) ∧ (i_v = 1) = ⊥`: the endpoints are disjoint. -/
theorem varEq0_meet_varEq1 (v : Fin 3) : (varEq0 v).meet (varEq1 v) = bot := by
  apply toSpec_injective
  rw [meet_toSpec, varEq0_toSpec, varEq1_toSpec, bot_toSpec]
  exact FaceIdealSpec3.ext fun f => Trit.isZero_and_isOne (f v)
end FaceIdeal3

/-! ## 7. `refine_exec` -/
/-- Rewrite rules `refine_exec` uses besides its own: tag a refinement theorem of a later module
(`(op p q).toSpec = specOp p.toSpec q.toSpec`, `obs p = specObs p.toSpec`, an extensionality `↔`). -/
register_simp_attr refine_exec_simp
theorem bitVec_eq_iff_getElem {w : Nat} {x y : BitVec w} : x = y ↔ ∀ (i : Nat) (h : i < w), x[i] = y[i] :=
  ⟨fun h _ _ => h ▸ rfl, BitVec.eq_of_getElem_eq⟩
theorem containsFast_mergeFast {α : Type u} [StrictLinearOrder α] (kl kr kb : Bool) {a b : Array α}
    (ha : SortedArray a) (hb : SortedArray b) (z : α) :
    containsFast (mergeFast kl kr kb a b) z = keep kl kr kb (containsFast a z) (containsFast b z) := by
  have h := mergeFast_refines kl kr kb _ a _ b ⟨ha, rfl⟩ ⟨hb, rfl⟩
  refine (containsFast_eq_spec z _ _ h).trans ?_
  change keep kl kr kb (memB z a.toList) (memB z b.toList) = _
  rw [containsFast_eq_memB ha, containsFast_eq_memB hb]
theorem sortedArray_mergeFast {α : Type u} [StrictLinearOrder α] (kl kr kb : Bool) {a b : Array α}
    (ha : SortedArray a) (hb : SortedArray b) : SortedArray (mergeFast kl kr kb a b) :=
  (mergeFast_refines kl kr kb _ a _ b ⟨ha, rfl⟩ ⟨hb, rfl⟩).wf

section RefineExec
open Lean Meta Elab Tactic
/-- The `Bool` operations `refine_exec` looks through for atoms. -/
meta def boolConnectives : List Name :=
  [`and, `or, `not, `xor, `Bool.and, `Bool.or, `Bool.not, `Bool.xor, `cond, `ite]
/-- A `Bool` subterm of `e` that is not built by a `Bool` operation: an atom of the identity. -/
meta partial def findBoolAtom? (e : Expr) : MetaM (Option Expr) := do
  if e.hasLooseBVars then return none
  let isBool (e : Expr) : MetaM Bool := do return (← whnfR (← inferType e)).isConstOf ``Bool
  match e with
  | .mdata _ b => findBoolAtom? b
  | .app .. =>
    let args := e.getAppArgs
    let visitArgs : MetaM (Option Expr) := do
      for a in args do
        if let some r ← findBoolAtom? a then return some r
      return none
    if ← isBool e then
      match e.getAppFn with
      | .const n _ =>
        if boolConnectives.contains n then visitArgs
        else if (n == ``BEq.beq || n == ``bne) && args.size > 0 && args[0]!.isConstOf ``Bool then visitArgs
        else return some e
      | _ => return some e
    else visitArgs
  | .fvar _ => if ← isBool e then return some e else return none
  | .const n _ =>
    if n == ``Bool.true || n == ``Bool.false then return none
    else if ← isBool e then return some e
    else return none
  | .forallE _ d b _ =>
    if let some r ← findBoolAtom? d then return some r
    findBoolAtom? b
  | _ => return none
/-- Split on the atoms of the goal one at a time; a goal with none left is closed by evaluation. -/
meta partial def splitBoolAtoms (g : MVarId) : TacticM Unit := do
  let atom? ← g.withContext do findBoolAtom? (← instantiateMVars (← g.getType))
  match atom? with
  | none =>
    setGoals [g]
    evalTactic (← `(tactic| first | rfl | decide))
  | some a =>
    let (xs, g') ← g.withContext <| g.generalize #[{ expr := a }]
    for s in ← g'.cases xs[0]! do
      splitBoolAtoms s.mvarId
/-- A closed goal is evaluated as it stands (its atoms are values, not unknowns); any other is
proved by cases on its atoms. -/
meta def decideBoolAtoms (g : MVarId) : TacticM Unit := do
  setGoals [g]
  unless ← tryTactic (evalTactic (← `(tactic| first | rfl | decide))) do
    splitBoolAtoms g
/-- `bool_atoms` proves a `Bool` identity by cases on its atoms: the `Bool` subterms that no `Bool`
operation builds. A closed identity is evaluated. -/
elab "bool_atoms" : tactic => do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  let (_, g) ← g.intros
  decideBoolAtoms g
  setGoals rest
/-- The refinement theorems of this module, as rewrite rules from executable to specification. -/
meta def refineExecLemmas : List Name :=
  [``SortedArraySet.eq_iff_toSpec, ``SortedArraySet.contains_eq_spec, ``SortedArraySet.unionFast_toSpec,
    ``SortedArraySet.interFast_toSpec, ``SortedArraySet.diffFast_toSpec, ``SortedArraySet.empty_toSpec,
    ``FinSetSpec.ext_iff, ``FinSetSpec.mem_union, ``FinSetSpec.mem_inter, ``FinSetSpec.mem_diff,
    ``FinSetSpec.mem_empty, ``containsFast_mergeFast, ``sortedArray_mergeFast,
    ``readU64LE_packU64LE, ``U64Bytes.ofList_toSpec,
    ``FaceIdeal3.eq_iff_toSpec, ``FaceIdeal3.join_toSpec, ``FaceIdeal3.meet_toSpec, ``FaceIdeal3.bot_toSpec,
    ``FaceIdeal3.top_toSpec, ``FaceIdeal3.varEq0_toSpec, ``FaceIdeal3.varEq1_toSpec, ``FaceIdeal3.ofSpec_toSpec,
    ``FaceIdealSpec3.ext_iff, ``FaceIdealSpec3.mem_join, ``FaceIdealSpec3.mem_meet, ``FaceIdealSpec3.mem_bot,
    ``FaceIdealSpec3.mem_top, ``FaceIdealSpec3.mem_varEq0, ``FaceIdealSpec3.mem_varEq1,
    ``bitVec_eq_iff_getElem, ``BitVec.getElem_or, ``BitVec.getElem_and, ``BitVec.getElem_xor,
    ``BitVec.getElem_zero, ``BitVec.getElem_allOnes]
/-- Definitions `refine_exec` unfolds. -/
meta def refineExecUnfold : List Name := [``keep, ``unionFast, ``interFast, ``diffFast]
/-- `refine_exec` proves an identity between executable expressions from the specification they
refine. It rewrites with the refinement theorems of this module, the theorems tagged
`@[refine_exec_simp]` and the hypotheses in scope (a representation invariant `SortedArray a`
discharges the side condition of a rule about `a`), which turns an equation of representations into
one of specification values and that into a `Bool` identity at each point; then it proves the
identity by cases on its atoms (`bool_atoms`). -/
elab "refine_exec" : tactic => withMainContext do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  let mut thms : SimpTheorems := {}
  for n in refineExecLemmas do
    thms ← thms.addConst n
  for n in refineExecUnfold do
    thms ← thms.addDeclToUnfold n
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    if ← isProp h.type then
      thms ← thms.add (.fvar h.fvarId) #[] h.toExpr
  let tagged ← match ← getSimpExtension? `refine_exec_simp with
    | some ext => ext.getTheorems
    | none => pure {}
  let ctx ← Simp.mkContext (simpTheorems := #[thms, tagged]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx
  match r with
  | none => pure ()
  | some (_, g) =>
    let (_, g) ← g.intros
    decideBoolAtoms g
  setGoals rest
end RefineExec

/-! ## 8. The algebra of the representations, by `refine_exec` -/

namespace SortedArraySet
variable {α : Type u} [StrictLinearOrder α]
theorem union_comm (p q : SortedArraySet α) : p.union q = q.union p := by refine_exec
theorem union_assoc (p q r : SortedArraySet α) : (p.union q).union r = p.union (q.union r) := by refine_exec
theorem union_idem (p : SortedArraySet α) : p.union p = p := by refine_exec
theorem inter_comm (p q : SortedArraySet α) : p.inter q = q.inter p := by refine_exec
theorem inter_assoc (p q r : SortedArraySet α) : (p.inter q).inter r = p.inter (q.inter r) := by refine_exec
theorem inter_union_distrib (p q r : SortedArraySet α) :
    p.inter (q.union r) = (p.inter q).union (p.inter r) := by refine_exec
theorem union_inter_distrib (p q r : SortedArraySet α) :
    p.union (q.inter r) = (p.union q).inter (p.union r) := by refine_exec
theorem diff_union (p q r : SortedArraySet α) : p.diff (q.union r) = (p.diff q).diff r := by refine_exec
theorem diff_self (p : SortedArraySet α) : p.diff p = empty := by refine_exec
theorem contains_union (p q : SortedArraySet α) (z : α) :
    (p.union q).contains z = (p.contains z || q.contains z) := by refine_exec
end SortedArraySet

namespace FaceIdeal3
theorem join_comm (a b : FaceIdeal3) : a.join b = b.join a := by refine_exec
theorem join_assoc (a b c : FaceIdeal3) : (a.join b).join c = a.join (b.join c) := by refine_exec
theorem meet_comm (a b : FaceIdeal3) : a.meet b = b.meet a := by refine_exec
theorem meet_assoc (a b c : FaceIdeal3) : (a.meet b).meet c = a.meet (b.meet c) := by refine_exec
theorem join_idem (a : FaceIdeal3) : a.join a = a := by refine_exec
theorem meet_idem (a : FaceIdeal3) : a.meet a = a := by refine_exec
theorem join_meet_absorb (a b : FaceIdeal3) : a.join (a.meet b) = a := by refine_exec
theorem meet_join_absorb (a b : FaceIdeal3) : a.meet (a.join b) = a := by refine_exec
/-- **Distributivity**, `∧` over `∨`. -/
theorem meet_join_distrib (a b c : FaceIdeal3) : a.meet (b.join c) = (a.meet b).join (a.meet c) := by refine_exec
/-- **Distributivity**, `∨` over `∧`. -/
theorem join_meet_distrib (a b c : FaceIdeal3) : a.join (b.meet c) = (a.join b).meet (a.join c) := by refine_exec
theorem bot_join (a : FaceIdeal3) : bot.join a = a := by refine_exec
theorem top_meet (a : FaceIdeal3) : top.meet a = a := by refine_exec
theorem bot_meet (a : FaceIdeal3) : bot.meet a = bot := by refine_exec
theorem top_join (a : FaceIdeal3) : top.join a = top := by refine_exec
end FaceIdeal3
end Obend.Tactic.DataRefinement
end
