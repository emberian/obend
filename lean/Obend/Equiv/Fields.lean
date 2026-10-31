module
/- Pointwise relations on the field, arm and hole lists of `Term`: two lists are related when
they carry the same names in the same order and their bodies are related position by position.
Lookup (`find?`) and record extension (`extendFields`) respect such a relation. -/
public import Obend.Core.Term
@[expose] public section
namespace Obend.Equiv
open Obend.Core.Term
set_option autoImplicit false

theorem zip_self {α : Type} : ∀ (l : List α) (p : α × α), p ∈ l.zip l → p.1 = p.2 ∧ p.1 ∈ l
  | [], _, h => by simp at h
  | a :: l, p, h => by
    simp only [List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2⟩ := zip_self l p h
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem zip_refl {α : Type} (R : α → α → Prop) (l : List α) (h : ∀ x ∈ l, R x x) :
    ∀ p ∈ l.zip l, R p.1 p.2 := by
  intro p hp
  obtain ⟨h1, h2⟩ := zip_self l p hp
  rw [← h1]; exact h _ h2

theorem zip_map_rel {α β : Type} {R : α → α → Prop} {S : β → β → Prop} (f g : α → β)
    {l l' : List α} (h : ∀ p ∈ l.zip l', R p.1 p.2) (hfg : ∀ x y, R x y → S (f x) (g y)) :
    ∀ p ∈ (l.map f).zip (l'.map g), S p.1 p.2 := by
  intro p hp
  rw [List.zip_map] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact hfg _ _ (h q hq)

theorem names_map (g : Term → Term) (fs : List (String × Term)) :
    (fs.map fun field => (field.1, g field.2)).map Prod.fst = fs.map Prod.fst := by
  simp [List.map_map, Function.comp_def]

theorem length_of_names {fs fs' : List (String × Term)}
    (names : fs.map Prod.fst = fs'.map Prod.fst) : fs.length = fs'.length := by
  have := congrArg List.length names; simpa using this

/-- Lookup in the right list is matched by lookup in the left list. -/
theorem find_right {R : Term → Term → Prop} :
    ∀ {fs fs' : List (String × Term)} {name : String} {body' : Term},
    fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', R p.1.2 p.2.2) →
    fs'.find? (fun field => field.1 == name) = some (name, body') →
    ∃ body, fs.find? (fun field => field.1 == name) = some (name, body) ∧ R body body'
  | [], [], _, _, _, _, hit => by simp at hit
  | [], _ :: _, _, _, names, _, _ => by simp at names
  | _ :: _, [], _, _, names, _, _ => by simp at names
  | (n, b) :: fs, (n', b') :: fs', name, body', names, rel, hit => by
    simp only [List.map_cons, List.cons.injEq] at names
    obtain ⟨rfl, names⟩ := names
    have relHead : R b b' := rel ((n, b), (n, b')) (by simp)
    have relTail : ∀ p ∈ fs.zip fs', R p.1.2 p.2.2 := fun p hp => rel p (by simp [hp])
    by_cases hc : n = name
    · subst hc
      simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq] at hit
      cases hit
      exact ⟨b, by simp, relHead⟩
    · have miss : (n == name) = false := by simpa using hc
      simp only [List.find?_cons, miss] at hit ⊢
      exact find_right names relTail hit

/-- Lookup in the left list is matched by lookup in the right list. -/
theorem find_left {R : Term → Term → Prop} :
    ∀ {fs fs' : List (String × Term)} {name : String} {body : Term},
    fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', R p.1.2 p.2.2) →
    fs.find? (fun field => field.1 == name) = some (name, body) →
    ∃ body', fs'.find? (fun field => field.1 == name) = some (name, body') ∧ R body body'
  | [], _, _, _, _, _, hit => by simp at hit
  | _ :: _, [], _, _, names, _, _ => by simp at names
  | (n, b) :: fs, (n', b') :: fs', name, body, names, rel, hit => by
    simp only [List.map_cons, List.cons.injEq] at names
    obtain ⟨rfl, names⟩ := names
    have relHead : R b b' := rel ((n, b), (n, b')) (by simp)
    have relTail : ∀ p ∈ fs.zip fs', R p.1.2 p.2.2 := fun p hp => rel p (by simp [hp])
    by_cases hc : n = name
    · subst hc
      simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq] at hit
      cases hit
      exact ⟨b', by simp, relHead⟩
    · have miss : (n == name) = false := by simpa using hc
      simp only [List.find?_cons, miss] at hit ⊢
      exact find_left names relTail hit

theorem filter_names_rel {R : Term → Term → Prop} (P : String → Bool) :
    ∀ {fs fs' : List (String × Term)},
    fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', R p.1.2 p.2.2) →
    (fs.filter (fun f => P f.1)).map Prod.fst = (fs'.filter (fun f => P f.1)).map Prod.fst ∧
    ∀ p ∈ (fs.filter (fun f => P f.1)).zip (fs'.filter (fun f => P f.1)), R p.1.2 p.2.2
  | [], [], _, _ => by simp
  | [], _ :: _, names, _ => by simp at names
  | _ :: _, [], names, _ => by simp at names
  | (n, b) :: fs, (n', b') :: fs', names, rel => by
    simp only [List.map_cons, List.cons.injEq] at names
    obtain ⟨rfl, names⟩ := names
    have relHead : R b b' := rel ((n, b), (n, b')) (by simp)
    have relTail : ∀ p ∈ fs.zip fs', R p.1.2 p.2.2 := fun p hp => rel p (by simp [hp])
    obtain ⟨n1, r1⟩ := filter_names_rel P names relTail
    by_cases hp : P n = true
    · simp only [List.filter_cons, hp, ite_true, List.map_cons, n1, List.zip_cons_cons,
        List.mem_cons]
      refine ⟨trivial, ?_⟩
      intro p hmem
      rcases hmem with rfl | hmem
      · exact relHead
      · exact r1 p hmem
    · simp only [List.filter_cons, hp]
      exact ⟨n1, r1⟩

theorem any_names {fs fs' : List (String × Term)} (names : fs.map Prod.fst = fs'.map Prod.fst)
    (k : String) : (fs.any fun field => field.1 == k) = (fs'.any fun field => field.1 == k) := by
  have h1 : (fs.any fun field => field.1 == k) = ((fs.map Prod.fst).any fun n => n == k) := by
    simp [List.any_map, Function.comp_def]
  have h2 : (fs'.any fun field => field.1 == k) = ((fs'.map Prod.fst).any fun n => n == k) := by
    simp [List.any_map, Function.comp_def]
  rw [h1, h2, names]

theorem extendFields_rel {R : Term → Term → Prop} {inh inh' fs fs' : List (String × Term)}
    (namesI : inh.map Prod.fst = inh'.map Prod.fst) (relI : ∀ p ∈ inh.zip inh', R p.1.2 p.2.2)
    (namesF : fs.map Prod.fst = fs'.map Prod.fst) (relF : ∀ p ∈ fs.zip fs', R p.1.2 p.2.2) :
    (extendFields inh fs).map Prod.fst = (extendFields inh' fs').map Prod.fst ∧
    ∀ p ∈ (extendFields inh fs).zip (extendFields inh' fs'), R p.1.2 p.2.2 := by
  have same : (fun prior : String × Term => !(fs.any fun field => field.1 == prior.1)) =
      (fun prior : String × Term => !(fs'.any fun field => field.1 == prior.1)) := by
    funext prior; rw [any_names namesF]
  obtain ⟨n1, r1⟩ := filter_names_rel (R := R) (fun k => !(fs'.any fun field => field.1 == k))
    namesI relI
  unfold extendFields
  rw [same]
  refine ⟨by simp only [List.map_append, namesF, n1], ?_⟩
  rw [List.zip_append (length_of_names namesF)]
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact relF p hp
  · exact r1 p hp

end Obend.Equiv
end
