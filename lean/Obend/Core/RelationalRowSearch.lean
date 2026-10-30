module
public import Obend.Core.RowHit
@[expose] public section
namespace Obend.Core.RowSearch
set_option autoImplicit false

inductive StepLift {α β γ δ : Type} (R : α → γ → Prop) (S : β → δ → Prop) :
    Step α β → Step γ δ → Prop where
  | stop : StepLift R S .stop .stop
  | emit {p q} : S p q → StepLift R S (.emit p) (.emit q)
  | skip {x y} : R x y → StepLift R S (.skip x) (.skip y)

theorem StepLift.symm {α β γ δ : Type} {R : α → γ → Prop} {S : β → δ → Prop}
    {left : Step α β} {right : Step γ δ} (related : StepLift R S left right) :
    StepLift (fun y x => R x y) (fun q p => S p q) right left := by
  cases related with
  | stop => exact .stop
  | emit h => exact .emit h
  | skip h => exact .skip h

/-- A finite deterministic emission path transports through a relational
scanner simulation, preserving the emission's payload relation. -/
theorem Hit.related {α β γ δ : Type} {left : α → Step α β} {right : γ → Step γ δ}
    {R : α → γ → Prop} {S : β → δ → Prop}
    (closed : ∀ x y, R x y → StepLift R S (left x) (right y))
    {x : α} {p : β} {n : Nat} (hit : Hit left x p n)
    {y : γ} (root : R x y) : ∃ q, Hit right y q n ∧ S p q := by
  induction hit generalizing y with
  | emit x p observed =>
    have next := closed x y root
    rw [observed] at next
    cases observedRight : right y with
    | stop => rw [observedRight] at next; cases next
    | skip other => rw [observedRight] at next; cases next
    | emit q =>
      rw [observedRight] at next
      cases next with
      | emit related => exact ⟨q,.emit y q observedRight,related⟩
  | skip x next p n observed nested ih =>
    have step := closed x y root
    rw [observed] at step
    cases observedRight : right y with
    | stop => rw [observedRight] at step; cases step
    | emit q => rw [observedRight] at step; cases step
    | skip other =>
      rw [observedRight] at step
      cases step with
      | skip related =>
        obtain ⟨q,emitted,payload⟩ := ih related
        exact ⟨q,.skip y other q n observedRight emitted,payload⟩

inductive OptionLift {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop where
  | none : OptionLift R none none
  | some {x y} : R x y → OptionLift R (some x) (some y)

/-- Finite support selection does not interfere with relational scanner
equivalence: both visited searches realize exactly their finite hit paths. -/
theorem find_related {α β γ δ : Type} [DecidableEq α] [DecidableEq γ]
    (left : α → Step α β) (right : γ → Step γ δ)
    (R : α → γ → Prop) (S : β → δ → Prop)
    (closed : ∀ x y, R x y → StepLift R S (left x) (right y))
    (leftNodes : List α) (rightNodes : List γ)
    (leftClosed : ∀ x y, x ∈ leftNodes → left x = .skip y → y ∈ leftNodes)
    (rightClosed : ∀ x y, x ∈ rightNodes → right x = .skip y → y ∈ rightNodes)
    {x : α} {y : γ} (leftRoot : x ∈ leftNodes) (rightRoot : y ∈ rightNodes) (root : R x y) :
    OptionLift S (find left leftNodes x) (find right rightNodes y) := by
  cases one : find left leftNodes x with
  | some p =>
    obtain ⟨n,hit⟩ := find_sound left leftNodes x p one
    obtain ⟨q,other,related⟩ := hit.related closed root
    have found := (find_iff_hit right rightNodes rightClosed rightRoot).mpr ⟨n,other⟩
    rw [found]
    exact .some related
  | none =>
    cases two : find right rightNodes y with
    | none => exact .none
    | some q =>
      obtain ⟨n,hit⟩ := find_sound right rightNodes y q two
      have reversed : ∀ y x, R x y →
          StepLift (fun y x => R x y) (fun q p => S p q) (right y) (left x) := by
        intro y x link
        exact (closed x y link).symm
      obtain ⟨p,other,_⟩ := hit.related reversed root
      have found := (find_iff_hit left leftNodes leftClosed leftRoot).mpr ⟨n,other⟩
      rw [one] at found
      contradiction

#assert_axioms StepLift.symm Hit.related find_related
end Obend.Core.RowSearch
