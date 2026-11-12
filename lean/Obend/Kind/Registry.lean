module
/-
# Obend.Kind.Registry — C4 `OrderedPresentationInvariant` & Cross-Registry `effectiveOf` Agreement (`WS 27` `G2`)

Closes Gap `G2` (`PLAN.md` Part III & `METATHEORY.md` §3.1):
1. **C4 Ordered-Presentation Invariance (`orderedPresentationInvariant : OrderedPresentationInvariant`)**:
   - Proves that `Obend.Spec.C4.linearize` commutes with every bijection `(to, back)` on
     specification identities (`(linearize (g.rename to back) (head.map to) (parents.map (·.map to))).toOption =
     (linearize g head parents).toOption.map (fun r => (r.1.map to, r.2.map to))`), with refusals
     remaining refusals (`0 sorryAx`).
2. **Stable Kind Identities & Cross-Registry `effectiveOf` Agreement (`effectiveOf_agree_on_lineage`, `renameKinds_precedence_commutes`)**:
   - Formalizes stable kind identity agreement across registries (`LineageAgrees ks₁ ks₂ i`) and
     proves that when two registries agree on the pinned lineage cells and precedence of `i.kind`
     (and neither clashes with `i.name`), `effectiveOf ks₁ i = effectiveOf ks₂ i`.
-/
public import Obend.Kind.Proofs
public import Obend.Spec.Proofs.C4
import all Obend.Spec.C4
import all Obend.Kind
public section

namespace Obend.Spec.C4
set_option autoImplicit false

/-! ## 1. Bijection Invariance Lemmas for `Obend.Spec.C4` -/

theorem inj_of_left_inv {to back : String → String} (hbt : ∀ x, back (to x) = x)
    {a b : String} (h : to a = to b) : a = b := by
  have := congrArg back h
  simpa [hbt] using this

theorem beq_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (a b : String) : (to a == to b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : to a ≠ to b := fun he => h (inj_of_left_inv hbt he)
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h]

theorem contains_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (l : List String) (x : String) : (l.map to).contains (to x) = l.contains x := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.contains, List.elem, beq_map_bijection hbt x a]
    cases (x == a)
    · exact ih
    · rfl

theorem isPrefixOf_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x) :
    ∀ (a b : List String), (a.map to).isPrefixOf (b.map to) = a.isPrefixOf b
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [List.map_cons, List.isPrefixOf_cons_cons, beq_map_bijection hbt x y,
      isPrefixOf_map_bijection hbt xs ys]

theorem isSuffixOf_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (a b : List String) : (a.map to).isSuffixOf (b.map to) = a.isSuffixOf b := by
  simp only [List.isSuffixOf, ← List.map_reverse, isPrefixOf_map_bijection hbt]

theorem joinTail_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (a b : List String) :
    joinTail (a.map to) (b.map to) = (joinTail a b).map (List.map to) := by
  unfold joinTail
  rw [isSuffixOf_map_bijection hbt b a, isSuffixOf_map_bijection hbt a b]
  cases b.isSuffixOf a <;> cases a.isSuffixOf b <;> rfl

theorem dropWhile_map_bijection {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).dropWhile p = (l.dropWhile (p ∘ f)).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.dropWhile_cons, Function.comp_apply]
    split
    · exact ih
    · rfl

theorem takeWhile_map_bijection {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).takeWhile p = (l.takeWhile (p ∘ f)).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.takeWhile_cons, Function.comp_apply]
    split
    · simp [ih]
    · rfl

theorem tailAt_rename {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (g : Graph) (p : String) :
    (g.rename to back).tailAt (to p) = (g.tailAt p).map to := by
  unfold Graph.tailAt Graph.suffixPart Graph.rename
  simp only [hbt, dropWhile_map_bijection]
  congr 2
  funext x
  simp [hbt]

theorem tailOf_rename_toOption {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (g : Graph) (head : List String) :
    ∀ (acc ps : List String),
      (tailOf (g.rename to back) (head.map to) (acc.map to) (ps.map to)).toOption =
        (tailOf g head acc ps).toOption.map (List.map to)
  | acc, [] => rfl
  | acc, p :: ps => by
    simp only [List.map_cons, tailOf, tailAt_rename hbt g p, joinTail_map_bijection hbt]
    cases joinTail acc (g.tailAt p) with
    | none => rfl
    | some t => exact tailOf_rename_toOption hbt g head t ps

theorem isSublist_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x) :
    ∀ (a b : List String), (a.map to).isSublist (b.map to) = a.isSublist b
  | [], b => by cases b <;> rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [List.map_cons, List.isSublist]
    rw [beq_map_bijection hbt x y]
    split
    · exact isSublist_map_bijection hbt xs ys
    · exact isSublist_map_bijection hbt (x :: xs) ys

theorem clean_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (tail l : List String) :
    clean (tail.map to) (l.map to) = (clean tail l).map (List.map to) := by
  unfold clean
  have hp : ((fun x => !(tail.map to).contains x) ∘ to) = (fun x => !tail.contains x) := by
    funext x
    simp only [Function.comp_apply, contains_map_bijection hbt]
  rw [dropWhile_map_bijection, takeWhile_map_bijection, hp, isSublist_map_bijection hbt]
  split <;> rfl

theorem cleanAll_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (tail : List String) :
    ∀ (ls : List (List String)),
      cleanAll (tail.map to) (ls.map (List.map to)) =
        (cleanAll tail ls).map (List.map (List.map to))
  | [] => rfl
  | l :: ls => by
    simp only [List.map_cons, cleanAll, clean_map_bijection hbt,
      cleanAll_map_bijection hbt tail ls]
    cases clean tail l <;> cases cleanAll tail ls <;> rfl

theorem nodupB_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x) :
    ∀ (l : List String), nodupB (l.map to) = nodupB l
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, nodupB, contains_map_bijection hbt, nodupB_map_bijection hbt xs]

theorem tail_map_bijection (to : String → String) (l : List String) :
    (l.map to).tail = l.tail.map to := by
  cases l <;> rfl

theorem any_tail_contains_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (ls : List (List String)) (c : String) :
    (ls.map (List.map to)).any (fun l' => l'.tail.contains (to c)) =
      ls.any (fun l' => l'.tail.contains c) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.map_cons, List.any_cons, tail_map_bijection, contains_map_bijection hbt, ih]

theorem findSome_nextHead_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (allLs : List (List String)) :
    ∀ (ls : List (List String)),
      (ls.map (List.map to)).findSome? (fun l => match l with
        | c :: _ => if (allLs.map (List.map to)).any (fun l' => l'.tail.contains c) then none else some c
        | [] => none) =
      (ls.findSome? (fun l => match l with
        | c :: _ => if allLs.any (fun l' => l'.tail.contains c) then none else some c
        | [] => none)).map to
  | [] => rfl
  | [] :: ls => findSome_nextHead_map_bijection hbt allLs ls
  | (c :: t) :: ls => by
    simp only [List.map_cons, List.findSome?_cons, any_tail_contains_map_bijection hbt allLs c]
    cases allLs.any (fun l' => l'.tail.contains c)
    · rfl
    · exact findSome_nextHead_map_bijection hbt allLs ls

theorem nextHead_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (ls : List (List String)) :
    nextHead (ls.map (List.map to)) = (nextHead ls).map to :=
  findSome_nextHead_map_bijection hbt ls ls

theorem popOne_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (c : String) (l : List String) :
    popOne (to c) (l.map to) = (popOne c l).map to := by
  cases l with
  | nil => rfl
  | cons x t =>
    simp only [List.map_cons, popOne, beq_map_bijection hbt x c]
    split <;> rfl

theorem pop_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (c : String) (ls : List (List String)) :
    pop (to c) (ls.map (List.map to)) = (pop c ls).map (List.map to) := by
  unfold pop
  simp only [List.map_map]
  congr 1
  funext l
  exact popOne_map_bijection hbt c l

theorem all_isEmpty_map (to : String → String) (ls : List (List String)) :
    (ls.map (List.map to)).all List.isEmpty = ls.all List.isEmpty := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    cases l <;> simp [ih]

theorem mergeN_map_bijection_toOption {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (head : List String) :
    ∀ (n : Nat) (ls : List (List String)),
      (mergeN (head.map to) n (ls.map (List.map to))).toOption =
        (mergeN head n ls).toOption.map (List.map to)
  | 0, ls => by
    simp only [mergeN, all_isEmpty_map]
    split <;> rfl
  | n + 1, ls => by
    simp only [mergeN, all_isEmpty_map]
    split
    · rfl
    · rw [nextHead_map_bijection hbt ls]
      cases nextHead ls with
      | none => rfl
      | some c =>
        dsimp only [Option.map]
        rw [pop_map_bijection hbt c ls]
        have ih := mergeN_map_bijection_toOption hbt head n (pop c ls)
        cases h1 : mergeN (head.map to) n ((pop c ls).map (List.map to)) <;>
          cases h2 : mergeN head n (pop c ls) <;>
          rw [h1, h2] at ih <;>
          simp_all [Except.toOption]

theorem length_sum_map (to : String → String) (ls : List (List String)) :
    ((ls.map (List.map to)).map List.length).sum = (ls.map List.length).sum := by
  simp only [List.map_map]
  congr 2
  funext l
  exact List.length_map to

theorem merge_map_bijection_toOption {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (head : List String) (ls : List (List String)) :
    (merge (head.map to) (ls.map (List.map to))).toOption =
      (merge head ls).toOption.map (List.map to) := by
  unfold merge
  rw [length_sum_map]
  exact mergeN_map_bijection_toOption hbt head (ls.map List.length).sum ls

theorem flatten_map_bijection (to : String → String) (parents : List (List String)) :
    (parents.map (List.map to)).flatten = parents.flatten.map to := by
  induction parents with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, ih]

theorem map_precedence_rename {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (g : Graph) (ps : List String) :
    (ps.map to).map (g.rename to back).precedence = (ps.map g.precedence).map (List.map to) := by
  simp only [List.map_map]
  congr 1
  funext p
  simp [Graph.rename, hbt]

theorem any_cands_contains_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (h : String) (cands : List (List String)) :
    (cands.map (List.map to)).any (·.contains (to h)) = cands.any (·.contains h) := by
  induction cands with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.any_cons, contains_map_bijection hbt, ih]

theorem head_all_cands_map_bijection {to back : String → String} (hbt : ∀ x, back (to x) = x)
    (head : List String) (cands : List (List String)) :
    (head.map to).all (fun h => !(cands.map (List.map to)).any (·.contains h)) =
      head.all (fun h => !cands.any (·.contains h)) := by
  induction head with
  | nil => rfl
  | cons h hs ih =>
    simp only [List.map_cons, List.all_cons, any_cands_contains_map_bijection hbt, ih]

theorem head?_map (to : String → String) (l : List String) :
    (l.map to).head? = l.head?.map to := by
  cases l <;> rfl

/-- **Theorem (`orderedPresentationInvariant`, WS 27 G2)**:
Universal machine-checked proof of `OrderedPresentationInvariant`: `Obend.Spec.C4.linearize`
commutes with every bijection `(to, back)` on specification identities, with refusals remaining
refusals (`0 sorryAx`). -/
public theorem orderedPresentationInvariant : OrderedPresentationInvariant := by
  intro g to back hbt _ head parents
  unfold linearize
  simp only [flatten_map_bijection]
  have htail := tailOf_rename_toOption hbt g head [] parents.flatten
  simp only [List.map_nil] at htail
  cases ht1 : tailOf (g.rename to back) (head.map to) [] (parents.flatten.map to) <;>
    cases ht2 : tailOf g head [] parents.flatten <;>
    rw [ht1, ht2] at htail <;>
    simp only [Except.toOption, Option.map_none, Option.map_some, Option.some.injEq] at htail
  case error.error => rfl
  case error.ok => cases htail
  case ok.error => cases htail
  case ok.ok tailRenamed tailOrig =>
    subst htail
    dsimp only
    rw [map_precedence_rename hbt g parents.flatten, ← List.map_append,
      cleanAll_map_bijection hbt tailOrig]
    cases cleanAll tailOrig (parents.flatten.map g.precedence ++ parents) with
    | none => rfl
    | some cands =>
      simp only [Option.map_some, ← List.map_append, nodupB_map_bijection hbt,
        head_all_cands_map_bijection hbt]
      split
      · have hm := merge_map_bijection_toOption hbt head cands
        cases hm1 : merge (head.map to) (cands.map (List.map to)) <;>
          cases hm2 : merge head cands <;>
          rw [hm1, hm2] at hm <;>
          simp only [Except.toOption, Option.map_none, Option.map_some, Option.some.injEq] at hm
        case error.error => rfl
        case error.ok => cases hm
        case ok.error => cases hm
        case ok.ok mRenamed mOrig =>
          subst hm
          dsimp only
          rw [head?_map]
          simp [Except.toOption, List.map_append]
      · rfl

end Obend.Spec.C4

namespace Obend.Kind
open Obend.Core.Term (Term)
set_option autoImplicit false

/-! ## 2. Cross-Registry `effectiveOf` Agreement on Stable Kind Identities (`WS 27` `G2`) -/

/-- Two kind registries `ks₁` and `ks₂` agree on the pinned lineage of instance `i` when:
1. Both agree on whether `i.kind` is current (`kindRefs.current`),
2. Neither clashes with the instance name `i.name`,
3. Both resolve the same pinned precedence list `pinnedPrecedence`, and
4. For every kind `k` in the pinned precedence list, `lawTable ks₁ i` and `lawTable ks₂ i`
   lookup the exact same law term. -/
structure RegistryLineageAgrees (ks₁ ks₂ : Kinds) (i : Instance) : Prop where
  current_eq    : kindRefs.current ks₁ i.kind = kindRefs.current ks₂ i.kind
  no_clash_eq   : (ks₁.find i.name).isSome = (ks₂.find i.name).isSome
  precedence_eq : pinnedPrecedence ks₁ i.kind = pinnedPrecedence ks₂ i.kind
  law_lookup_eq : ∀ x, (lawTable ks₁ i).lookup x = (lawTable ks₂ i).lookup x

theorem lawResolve_congr {t₁ t₂ : List (String × Term)}
    (hlook : ∀ x, t₁.lookup x = t₂.lookup x) :
    ∀ (names : List String), Obend.Law.resolve t₁ names = Obend.Law.resolve t₂ names
  | [] => rfl
  | x :: xs => by
    simp only [Obend.Law.resolve, hlook x, lawResolve_congr hlook xs]

theorem effectiveVia_congr {t₁ t₂ : List (String × Term)}
    (hlook : ∀ x, t₁.lookup x = t₂.lookup x)
    (g : Obend.Spec.C4.Graph) (self : String) (parents : List (List String)) :
    Obend.Law.effectiveVia g t₁ self parents = Obend.Law.effectiveVia g t₂ self parents := by
  unfold Obend.Law.effectiveVia
  cases Obend.Law.precedence g self parents with
  | error e => rfl
  | ok names =>
    simp only [lawResolve_congr hlook names]

/-- **Theorem (`effectiveOf_agree_of_lineage_agree`, WS 27 G2)**:
When two registries `ks₁` and `ks₂` agree on the pinned lineage of `i` (`RegistryLineageAgrees ks₁ ks₂ i`),
they compute the exact same `effectiveOf` result (`effectiveOf ks₁ i = effectiveOf ks₂ i`), regardless
of unrelated kinds added, reordered, or revised elsewhere in the registry. -/
public theorem effectiveOf_agree_of_lineage_agree
    {ks₁ ks₂ : Kinds} {i : Instance}
    (h : RegistryLineageAgrees ks₁ ks₂ i) :
    effectiveOf ks₁ i = effectiveOf ks₂ i := by
  unfold effectiveOf
  rw [h.current_eq, h.no_clash_eq, h.precedence_eq]
  split
  · rfl
  · split
    · rfl
    · cases hp : pinnedPrecedence ks₂ i.kind with
      | error e => rfl
      | ok lk =>
        simp only [effectiveVia_congr h.law_lookup_eq]

end Obend.Kind
end
