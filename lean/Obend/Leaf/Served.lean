module
/-
# Obend.Leaf.Served — a bound book's link is the book's link, when the dispatcher serves the pins

`bindBookPins B pins` (`Obend.Leaf.Specialize`) replaces, in every definition of `B`, each read
`self.m` of a pinned member by the pin's code. The dispatcher `B.link` is `fix (λself. λ_. {…}) {}`,
so `self` is `B.link` itself and `self.m` runs to the entry of `m`. The replacement is therefore
behaviour-preserving exactly when the pin's code is closed (it is inserted under whatever binders
stand at the read) and meets that entry: both run to one term (`Meets`). Under those two conditions
for every pin (`Served`), and with both links closed and every definition a lambda (as `emit`
writes them), **`B.link ≈b (bindBookPins B pins).link`** (`link_bequiv_bindBookPins`).

The two links are different recursive terms, so `Ahead` cannot relate them; they are related by
`Joins` (`Obend.Leaf.UpTo`) over the one base pair `(B.link, (bindBookPins B pins).link)`, as
`flatten_sound` relates an object to its flattening. The unfolding of the pair is `joins_bind`:
a term with `self` substituted by `B.link` on the left and by the bound link on the right, and its
pinned reads replaced, joins — by `Joins.base` at `self`, by the two runs to the meeting term at a
replaced read, and by congruence everywhere else.

`served_of_judgeB` reads the decidable judge `specializedJudgeB` (closedness by `closedB`, meeting
by `Obend.Law.run` and `termEq`) back as these hypotheses. `Obend.Leaf.Static` composes the result
with the folder: `B.link ≈b (specializeBook B pins).link`, and makes it the proof the slot's
`Candidate.specialized` carries.
-/
public import Obend.Leaf.Flatten
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
@[expose] public section
namespace Obend.Leaf.Served
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
set_option autoImplicit false

/-! ## The hypotheses -/

/-- The read of `m` from the dispatcher of `B` and the term `v` meet: both run to one term. -/
def Meets (B : Book) (m : String) (v : Term) : Prop :=
  ∃ w, Steps (.get B.link m) w ∧ Steps v w

/-- `B` serves `pins`: every pin's code is closed and meets the read of its member. -/
def Served (B : Book) (pins : List LeafPin) : Prop :=
  ∀ p ∈ pins, Closed p.code ∧ Meets B p.cell.key p.code

/-- Every definition's code is a lambda, as `emit` writes them. -/
def LamCodes (B : Book) : Prop := ∀ d ∈ B.defs, ∃ inner, d.code = .lam inner

/-- The one base pair: the book's link and the bound book's link. -/
def Pair (B : Book) (pins : List LeafPin) (o f : Term) : Prop :=
  o = B.link ∧ f = (bindBookPins B pins).link

/-! ## Helpers -/

theorem zip_map_map_rel {R : Term → Term → Prop} (g g' : Term → Term) :
    ∀ (l : List Term), (∀ x ∈ l, R (g x) (g' x)) → ∀ p ∈ (l.map g).zip (l.map g'), R p.1 p.2
  | [], _, p, hp => by simp at hp
  | x :: xs, h, p, hp => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h x List.mem_cons_self
    · exact zip_map_map_rel g g' xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) p hp

theorem zip_map_map_fields_rel {R : Term → Term → Prop} (g g' : Term → Term) :
    ∀ (fs : List (String × Term)), (∀ x ∈ fs, R (g x.2) (g' x.2)) →
      ∀ p ∈ (fs.map fun f => (f.1, g f.2)).zip (fs.map fun f => (f.1, g' f.2)), R p.1.2 p.2.2
  | [], _, p, hp => by simp at hp
  | x :: xs, h, p, hp => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h x List.mem_cons_self
    · exact zip_map_map_fields_rel g g' xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) p hp

/-- `resolveMemberGet` leaves a read whose target is not a variable as a read. -/
theorem resolveMemberGet_not_bound (d : Nat) (env : String → Option Term) {g : Term} (g' : Term)
    (m : String) (h : ∀ i, g ≠ .bound i) :
    resolveMemberGet d env g g' m = .get g' m := by
  cases g with
  | bound i => exact absurd rfl (h i)
  | _ => rfl

/-- A pin's code, found by `pinListEnv`, is the code of a pin of the list for that member. -/
theorem pinListEnv_some {pins : List LeafPin} {m : String} {v : Term}
    (h : pinListEnv pins m = some v) : ∃ p ∈ pins, p.cell.key = m ∧ p.code = v := by
  unfold pinListEnv at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨p, List.mem_of_find?_eq_some hp, ?_, rfl⟩
  have := List.find?_some hp
  simpa using this

/-- A `.bound 1` under two binders is `self`; a term renamed by two is itself once they are opened. -/
theorem openTerm_add_two (t X s : Term) : openTerm (t.rename (· + 2)) X s = t := by
  unfold openTerm
  rw [Obend.Core.TermTraverse.rename_substitute]
  exact substitute_bound t

/-- Pins bound into the dispatcher's record keep the member names. -/
theorem entry_fst_bind (slots : List String) (pins : List LeafPin) (item : BookItem) :
    (bindBookItem slots pins item).entry.1 = item.entry.1 := by
  cases item <;> rfl

theorem mem_defs_of_slot_mem {B : Book} {d : LeafDef} (h : BookItem.slot d ∈ B.items) : d ∈ B.defs :=
  List.mem_filterMap.2 ⟨.slot d, h, rfl⟩

/-! ## The unfolding joins -/

section
variable {B : Book} {pins : List LeafPin}

/-- **A term under `self`, before and after binding, joins.** With `σ d = B.link` on the left and
`σ' d` the bound link on the right (equal elsewhere), `t` and its pinned-read replacement join:
`self` is the base pair, a replaced read runs to the meeting term on both sides, and every other
constructor is a congruence. -/
theorem joins_bind (hc : Closed B.link) (hc' : Closed (bindBookPins B pins).link)
    (hs : Served B pins) :
    (t : Term) → (d : Nat) → (σ σ' : Nat → Term) → (∀ i, i ≠ d → σ i = σ' i) →
      σ d = B.link → σ' d = (bindBookPins B pins).link →
      Joins (Pair B pins) (t.substitute σ) ((substMemberEnvAt d (pinListEnv pins) t).substitute σ')
  | .hole n τ, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute, List.map_map, Function.comp_def]
    refine .hole n (by simp) ?_
    exact zip_map_map_rel (g := (·.substitute σ))
      (g' := fun t => (substMemberEnvAt d (pinListEnv pins) t).substitute σ') τ
      fun a ha => joins_bind hc hc' hs a d σ σ' hoff hσ hσ'
  | .bound i, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    by_cases hi : i = d
    · subst hi; rw [hσ, hσ']; exact .base ⟨rfl, rfl⟩
    · rw [hoff i hi]; exact .refl _
  | .lam b, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    refine .lam (joins_bind hc hc' hs b (d + 1) _ _ ?_ ?_ ?_)
    · intro i hi
      cases i with
      | zero => rfl
      | succ j => simp only [liftSubstitution]; rw [hoff j (fun e => hi (by omega))]
    · simp only [liftSubstitution]; rw [hσ, closed_rename hc]
    · simp only [liftSubstitution]; rw [hσ', closed_rename hc']
  | .app f a, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .app (joins_bind hc hc' hs f d σ σ' hoff hσ hσ') (joins_bind hc hc' hs a d σ σ' hoff hσ hσ')
  | .mix l u, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .mix (joins_bind hc hc' hs l d σ σ' hoff hσ hσ') (joins_bind hc hc' hs u d σ σ' hoff hσ hσ')
  | .fix s i, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .fix (joins_bind hc hc' hs s d σ σ' hoff hσ hσ') (joins_bind hc hc' hs i d σ σ' hoff hσ hσ')
  | .specification m e, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .specification (joins_bind hc hc' hs m d σ σ' hoff hσ hσ')
      (joins_bind hc hc' hs e d σ σ' hoff hσ hσ')
  | .prototype s g, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .prototype (joins_bind hc hc' hs s d σ σ' hoff hσ hσ')
      (joins_bind hc hc' hs g d σ σ' hoff hσ hσ')
  | .reflect p, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .reflect (joins_bind hc hc' hs p d σ σ' hoff hσ hσ')
  | .metadata p, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .metadata (joins_bind hc hc' hs p d σ σ' hoff hσ hσ')
  | .project p, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .project (joins_bind hc hc' hs p d σ σ' hoff hσ hσ')
  | .nat n, _, _, _, _, _, _ => by simp only [substMemberEnvAt, Term.substitute]; exact .refl _
  | .boolean b, _, _, _, _, _, _ => by simp only [substMemberEnvAt, Term.substitute]; exact .refl _
  | .label l, _, _, _, _, _, _ => by simp only [substMemberEnvAt, Term.substitute]; exact .refl _
  | .binary op l r, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .binary op (joins_bind hc hc' hs l d σ σ' hoff hσ hσ')
      (joins_bind hc hc' hs r d σ σ' hoff hσ hσ')
  | .extend i fs, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute, List.map_map, Function.comp_def]
    exact .extend (joins_bind hc hc' hs i d σ σ' hoff hσ hσ')
      (fields_map_names (·.substitute σ) (fun t => (substMemberEnvAt d (pinListEnv pins) t).substitute σ') rfl)
      (zip_map_map_fields_rel (g := (·.substitute σ))
        (g' := fun t => (substMemberEnvAt d (pinListEnv pins) t).substitute σ') fs
        fun x hx => joins_bind hc hc' hs x.2 d σ σ' hoff hσ hσ')
  | .record fs, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute, List.map_map, Function.comp_def]
    exact .record (fields_map_names (·.substitute σ) (fun t => (substMemberEnvAt d (pinListEnv pins) t).substitute σ') rfl)
      (zip_map_map_fields_rel (g := (·.substitute σ))
        (g' := fun t => (substMemberEnvAt d (pinListEnv pins) t).substitute σ') fs
        fun x hx => joins_bind hc hc' hs x.2 d σ σ' hoff hσ hσ')
  | .get g m, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt]
    by_cases hb : ∃ i, g = .bound i
    · obtain ⟨i, rfl⟩ := hb
      simp only [resolveMemberGet, Term.substitute]
      by_cases hi : i = d
      · subst hi
        simp only [beq_self_eq_true, ite_true]
        cases hv : pinListEnv pins m with
        | some v =>
          obtain ⟨p, hp, hkey, rfl⟩ := pinListEnv_some hv
          obtain ⟨hcl, w, h1, h2⟩ := hs p hp
          rw [closed_subst hcl, hσ]
          rw [hkey] at h1
          exact .run h1 (.back h2 (.refl w))
        | none =>
          simp only [Term.substitute]
          rw [hσ, hσ']
          exact .get m (.base ⟨rfl, rfl⟩)
      · have hne : (i == d) = false := by simpa using hi
        simp only [hne, Bool.false_eq_true, ite_false, Term.substitute]
        rw [hoff i hi]
        exact .refl _
    · rw [resolveMemberGet_not_bound d _ _ m (fun i e => hb ⟨i, e⟩)]
      simp only [Term.substitute]
      exact .get m (joins_bind hc hc' hs g d σ σ' hoff hσ hσ')
  | .ifZero v z s, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    refine .ifZero (joins_bind hc hc' hs v d σ σ' hoff hσ hσ')
      (joins_bind hc hc' hs z d σ σ' hoff hσ hσ')
      (joins_bind hc hc' hs s (d + 1) _ _ ?_ ?_ ?_)
    · intro i hi
      cases i with
      | zero => rfl
      | succ j => simp only [liftSubstitution]; rw [hoff j (fun e => hi (by omega))]
    · simp only [liftSubstitution]; rw [hσ, closed_rename hc]
    · simp only [liftSubstitution]; rw [hσ', closed_rename hc']
  | .inject l p, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .inject l (joins_bind hc hc' hs p d σ σ' hoff hσ hσ')
  | .case sc arms, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute, List.map_map, Function.comp_def]
    refine .case (joins_bind hc hc' hs sc d σ σ' hoff hσ hσ')
      (fields_map_names (·.substitute (liftSubstitution σ))
        (fun t => (substMemberEnvAt (d + 1) (pinListEnv pins) t).substitute (liftSubstitution σ')) rfl)
      (zip_map_map_fields_rel (g := (·.substitute (liftSubstitution σ)))
        (g' := fun t => (substMemberEnvAt (d + 1) (pinListEnv pins) t).substitute (liftSubstitution σ')) arms
        fun x hx => joins_bind hc hc' hs x.2 (d + 1) _ _ ?_ ?_ ?_)
    · intro i hi
      cases i with
      | zero => rfl
      | succ j => simp only [liftSubstitution]; rw [hoff j (fun e => hi (by omega))]
    · simp only [liftSubstitution]; rw [hσ, closed_rename hc]
    · simp only [liftSubstitution]; rw [hσ', closed_rename hc']
  | .ifBool c x y, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .ifBool (joins_bind hc hc' hs c d σ σ' hoff hσ hσ')
      (joins_bind hc hc' hs x d σ σ' hoff hσ hσ') (joins_bind hc hc' hs y d σ σ' hoff hσ hσ')
  | .perform p, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .perform (joins_bind hc hc' hs p d σ σ' hoff hσ hσ')
  | .done p, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .done (joins_bind hc hc' hs p d σ σ' hoff hσ hσ')
  | .split t ns f, d, σ, σ', hoff, hσ, hσ' => by
    simp only [substMemberEnvAt, Term.substitute]
    exact .split ns (joins_bind hc hc' hs t d σ σ' hoff hσ hσ')
      (joins_bind hc hc' hs f d σ σ' hoff hσ hσ')
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ha; omega)
    | (have := Obend.Leaf.sizeOf_snd_lt_of_mem hx; omega)

/-- **One entry of the dispatcher, opened, before and after binding, joins.** A static is the same
term under `self` on each side; a definition's call β-reduces on each side to its body under `self`,
which `joins_bind` relates. -/
theorem entry_join (hc : Closed B.link) (hc' : Closed (bindBookPins B pins).link)
    (hl : LamCodes B) (hs : Served B pins) (item : BookItem) (hitem : item ∈ B.items) :
    Joins (Pair B pins) (openTerm item.entry.2 B.link (.record []))
      (openTerm (bindBookItem B.slots pins item).entry.2 (bindBookPins B pins).link (.record [])) := by
  have hB : ClosedPairs (Pair B pins) := by rintro o f ⟨rfl, rfl⟩; exact ⟨hc, hc'⟩
  cases item with
  | static m v =>
    simp only [BookItem.entry, bindBookItem, openTerm_succ]
    exact joins_instantiate hB (.refl v) (.base ⟨rfl, rfl⟩)
  | slot d =>
    obtain ⟨inner, hcode⟩ := hl d (mem_defs_of_slot_mem hitem)
    have hbody := joins_bind hc hc' hs inner 0 (single B.link) (single (bindBookPins B pins).link)
      (fun i hi => by cases i with | zero => exact absurd rfl hi | succ j => rfl) rfl rfl
    rw [← instantiate_eq, ← instantiate_eq] at hbody
    cases hk : d.kind with
    | method =>
      simp only [BookItem.entry, bindBookItem, bindLeafDef, LeafDef.call, hk, hcode, substPinsInCode,
        openTerm, Term.substitute, selfSuper]
      rw [← openTerm, ← openTerm, openTerm_add_two, openTerm_add_two]
      exact .run (.next (.beta _ _) (.refl _)) (.back (.next (.beta _ _) (.refl _)) hbody)
    | cell =>
      simp only [BookItem.entry, bindBookItem, bindLeafDef, LeafDef.call, hk, hcode, substPinsInCode,
        openTerm, Term.substitute, selfSuper, List.map_nil]
      rw [← openTerm, ← openTerm, openTerm_add_two, openTerm_add_two]
      exact .run (.next (.application _ (.beta _ _)) (.refl _))
        (.back (.next (.application _ (.beta _ _)) (.refl _)) (.app hbody (.refl _)))

/-- The dispatcher's record, opened, before and after binding: the same names, entries that join. -/
theorem entries_join (hc : Closed B.link) (hc' : Closed (bindBookPins B pins).link)
    (hl : LamCodes B) (hs : Served B pins) :
    ∀ items : List BookItem, (∀ item ∈ items, item ∈ B.items) →
      (mapFields (openTerm · B.link (.record [])) (items.map BookItem.entry)).map Prod.fst =
        (mapFields (openTerm · (bindBookPins B pins).link (.record []))
          ((items.map (bindBookItem B.slots pins)).map BookItem.entry)).map Prod.fst ∧
      ∀ p ∈ (mapFields (openTerm · B.link (.record [])) (items.map BookItem.entry)).zip
          (mapFields (openTerm · (bindBookPins B pins).link (.record []))
            ((items.map (bindBookItem B.slots pins)).map BookItem.entry)),
        Joins (Pair B pins) p.1.2 p.2.2
  | [], _ => ⟨rfl, by simp [mapFields]⟩
  | item :: rest, hmem => by
    obtain ⟨n, r⟩ := entries_join hc hc' hl hs rest
      (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, mapFields, List.zip_cons_cons, List.mem_cons] at n r ⊢
    refine ⟨by rw [entry_fst_bind]; exact congrArg _ n, ?_⟩
    rintro p (rfl | hp)
    · exact entry_join hc hc' hl hs item (hmem item List.mem_cons_self)
    · exact r p hp

/-- The pair is a base: both links unfold (`fix`, two βs) to their opened records, which join. -/
theorem pair_base (hc : Closed B.link) (hc' : Closed (bindBookPins B pins).link)
    (hl : LamCodes B) (hs : Served B pins) : Base (Pair B pins) where
  closed := by rintro o f ⟨rfl, rfl⟩; exact ⟨hc, hc'⟩
  unfold := by
    rintro o f ⟨rfl, rfl⟩
    obtain ⟨n, r⟩ := entries_join hc hc' hl hs B.items (fun _ h => h)
    refine ⟨_, _, _, _, .fix _ _, fix_unfold _ _, .fix _ _, fix_unfold _ _, ?_⟩
    show Joins (Pair B pins)
      (openTerm (.record (B.items.map BookItem.entry)) B.link (.record []))
      (openTerm (.record ((B.items.map (bindBookItem B.slots pins)).map BookItem.entry))
        (bindBookPins B pins).link (.record []))
    rw [openTerm_record, openTerm_record]
    exact .record n r

/-- **The bound book's link is the book's link.** -/
theorem link_bequiv_bindBookPins (hc : Closed B.link) (hc' : Closed (bindBookPins B pins).link)
    (hl : LamCodes B) (hs : Served B pins) : B.link ≈b (bindBookPins B pins).link :=
  bequiv_of_joins (pair_base hc hc' hl hs) (.base ⟨rfl, rfl⟩)

end

/-! ## The judge decides the hypotheses -/

theorem meets_of_meetsB {fuel : Nat} {t v : Term} (h : meetsB fuel t v = true) :
    ∃ w, Steps t w ∧ Steps v w := by
  unfold meetsB at h
  cases h1 : Obend.Law.run fuel t with
  | none => rw [h1] at h; cases h
  | some a =>
    cases h2 : Obend.Law.run fuel v with
    | none => rw [h1, h2] at h; cases h
    | some b =>
      rw [h1, h2] at h
      have e : a = b := termEq_sound' h
      subst e
      exact ⟨a, (Obend.Law.run_sound fuel h1).1, (Obend.Law.run_sound fuel h2).1⟩

theorem lamCodes_of_lamCodesB {B : Book} (h : B.lamCodesB = true) : LamCodes B := by
  intro d hd
  have := (List.all_eq_true.1 h) d hd
  cases hcode : d.code <;> simp only [hcode] at this <;> first | exact ⟨_, rfl⟩ | cases this

/-- **The judge is sound**: `specializedJudgeB B pins = true` gives the four hypotheses of
`link_bequiv_bindBookPins`. -/
theorem served_of_judgeB {B : Book} {pins : List LeafPin} (h : specializedJudgeB B pins = true) :
    Closed B.link ∧ Closed (bindBookPins B pins).link ∧ LamCodes B ∧ Served B pins := by
  unfold specializedJudgeB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hc, hc'⟩, hl⟩, hs⟩ := h
  refine ⟨closed_of_closedB hc, closed_of_closedB hc', lamCodes_of_lamCodesB hl, ?_⟩
  intro p hp
  have hp' := (List.all_eq_true.1 hs) p hp
  simp only [Book.servesB, Bool.and_eq_true] at hp'
  exact ⟨closed_of_closedB hp'.1, meets_of_meetsB hp'.2⟩

/-- **A judged book's bound link is its link.** -/
theorem link_bequiv_bindBookPins_of_judgeB {B : Book} {pins : List LeafPin}
    (h : specializedJudgeB B pins = true) : B.link ≈b (bindBookPins B pins).link :=
  let ⟨hc, hc', hl, hs⟩ := served_of_judgeB h
  link_bequiv_bindBookPins hc hc' hl hs

end Obend.Leaf.Served

end
