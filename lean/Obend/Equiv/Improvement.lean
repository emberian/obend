module
/- The cost relation behind `mix_assoc_cost`. `Sim t t'` relates two terms that agree except that,
at any depth and under binders, an association `mix (mix a b) c` may stand against
`mix a (mix b c)` (either way round), and so may the bodies the two associations unfold to once
applied to a settled `self`. It is a congruence, closed under renaming and under the substitution of
settled terms (the only substitutions the clairvoyant semantics performs), and it preserves the
settled and value forms in both directions.

`Obend.Equiv.Cost` proves that it is a cost simulation within a factor of 8 in each direction. -/
public import Obend.Equiv.Clairvoyant
@[expose] public section
namespace Obend.Equiv
open Obend.Core.Term
set_option autoImplicit false

inductive Sim : Term → Term → Prop where
  | hole (n : Nat) {σ σ' : List Term} : σ.length = σ'.length →
      (∀ p ∈ σ.zip σ', Sim p.1 p.2) → Sim (.hole n σ) (.hole n σ')
  | bound (i : Nat) : Sim (.bound i) (.bound i)
  | lam {b b' : Term} : Sim b b' → Sim (.lam b) (.lam b')
  | app {f f' a a' : Term} : Sim f f' → Sim a a' → Sim (.app f a) (.app f' a')
  | mix {l l' u u' : Term} : Sim l l' → Sim u u' → Sim (.mix l u) (.mix l' u')
  | fix {s s' i i' : Term} : Sim s s' → Sim i i' → Sim (.fix s i) (.fix s' i')
  | specification {m m' e e' : Term} : Sim m m' → Sim e e' →
      Sim (.specification m e) (.specification m' e')
  | prototype {s s' g g' : Term} : Sim s s' → Sim g g' → Sim (.prototype s g) (.prototype s' g')
  | reflect {p p' : Term} : Sim p p' → Sim (.reflect p) (.reflect p')
  | metadata {p p' : Term} : Sim p p' → Sim (.metadata p) (.metadata p')
  | project {p p' : Term} : Sim p p' → Sim (.project p) (.project p')
  | nat (n : Nat) : Sim (.nat n) (.nat n)
  | boolean (b : Bool) : Sim (.boolean b) (.boolean b)
  | label (l : String) : Sim (.label l) (.label l)
  | binary (op : Primitive) {l l' r r' : Term} : Sim l l' → Sim r r' →
      Sim (.binary op l r) (.binary op l' r')
  | extend {i i' : Term} {fs fs' : List (String × Term)} : Sim i i' →
      fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', Sim p.1.2 p.2.2) →
      Sim (.extend i fs) (.extend i' fs')
  | record {fs fs' : List (String × Term)} :
      fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', Sim p.1.2 p.2.2) →
      Sim (.record fs) (.record fs')
  | get (name : String) {g g' : Term} : Sim g g' → Sim (.get g name) (.get g' name)
  | ifZero {v v' z z' s s' : Term} : Sim v v' → Sim z z' → Sim s s' →
      Sim (.ifZero v z s) (.ifZero v' z' s')
  | inject (l : String) {p p' : Term} : Sim p p' → Sim (.inject l p) (.inject l p')
  | case {sc sc' : Term} {arms arms' : List (String × Term)} : Sim sc sc' →
      arms.map Prod.fst = arms'.map Prod.fst → (∀ p ∈ arms.zip arms', Sim p.1.2 p.2.2) →
      Sim (.case sc arms) (.case sc' arms')
  | ifBool {c c' x x' y y' : Term} : Sim c c' → Sim x x' → Sim y y' →
      Sim (.ifBool c x y) (.ifBool c' x' y')
  | perform {p p' : Term} : Sim p p' → Sim (.perform p) (.perform p')
  | done {v v' : Term} : Sim v v' → Sim (.done v) (.done v')
  /-- The two associations. -/
  | assocLR {a a' b b' c c' : Term} : Sim a a' → Sim b b' → Sim c c' →
      Sim (.mix (.mix a b) c) (.mix a' (.mix b' c'))
  | assocRL {a a' b b' c c' : Term} : Sim a a' → Sim b b' → Sim c c' →
      Sim (.mix a (.mix b c)) (.mix (.mix a' b') c')
  /-- Their bodies, applied to a settled `self` and any `super`. -/
  | bodyLR {a a' b b' c c' s s' u u' : Term} : Settled s → Sim a a' → Sim b b' → Sim c c' →
      Sim s s' → Sim u u' →
      Sim (.app (.app c s) (.app (.app (.mix a b) s) u)) (.app (.app (.mix b' c') s') (.app (.app a' s') u'))
  | bodyRL {a a' b b' c c' s s' u u' : Term} : Settled s → Sim a a' → Sim b b' → Sim c c' →
      Sim s s' → Sim u u' →
      Sim (.app (.app (.mix b c) s) (.app (.app a s) u)) (.app (.app c' s') (.app (.app (.mix a' b') s') u'))

namespace Sim

set_option linter.unusedVariables false in
theorem refl : (t : Term) → Sim t t
  | .hole n σ => .hole n rfl (zip_refl (fun a b => Sim a b) σ (fun x _ => refl x))
  | .bound i => .bound i
  | .lam b => .lam (refl b)
  | .app f a => .app (refl f) (refl a)
  | .mix l u => .mix (refl l) (refl u)
  | .fix s i => .fix (refl s) (refl i)
  | .specification m e => .specification (refl m) (refl e)
  | .prototype s g => .prototype (refl s) (refl g)
  | .reflect p => .reflect (refl p)
  | .metadata p => .metadata (refl p)
  | .project p => .project (refl p)
  | .nat n => .nat n
  | .boolean b => .boolean b
  | .label l => .label l
  | .binary op l r => .binary op (refl l) (refl r)
  | .extend i fs => .extend (refl i) rfl
      (zip_refl (fun a b => Sim a.2 b.2) fs (fun x _ => refl x.2))
  | .record fs => .record rfl (zip_refl (fun a b => Sim a.2 b.2) fs (fun x _ => refl x.2))
  | .get g name => .get name (refl g)
  | .ifZero v z s => .ifZero (refl v) (refl z) (refl s)
  | .inject l p => .inject l (refl p)
  | .case sc arms => .case (refl sc) rfl
      (zip_refl (fun a b => Sim a.2 b.2) arms (fun x _ => refl x.2))
  | .ifBool c x y => .ifBool (refl c) (refl x) (refl y)
  | .perform p => .perform (refl p)
  | .done v => .done (refl v)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i x hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf x.snd < sizeOf x := by cases x; simp +arith
       omega)

theorem rename {t t' : Term} (h : Sim t t') : ∀ f : Nat → Nat, Sim (t.rename f) (t'.rename f) := by
  induction h with
  | hole n len _ ih =>
    intro f; simp only [Term.rename]
    exact .hole n (by simp [len]) (zip_map_rel (R := fun x y => ∀ f : Nat → Nat, Sim (Term.rename f x) (Term.rename f y)) _ _ ih (fun x y h => h f))
  | bound i => intro f; exact .refl _
  | lam _ ih => intro f; simp only [Term.rename]; exact .lam (ih _)
  | app _ _ i1 i2 => intro f; simp only [Term.rename]; exact .app (i1 f) (i2 f)
  | mix _ _ i1 i2 => intro f; simp only [Term.rename]; exact .mix (i1 f) (i2 f)
  | fix _ _ i1 i2 => intro f; simp only [Term.rename]; exact .fix (i1 f) (i2 f)
  | specification _ _ i1 i2 => intro f; simp only [Term.rename]; exact .specification (i1 f) (i2 f)
  | prototype _ _ i1 i2 => intro f; simp only [Term.rename]; exact .prototype (i1 f) (i2 f)
  | reflect _ ih => intro f; simp only [Term.rename]; exact .reflect (ih f)
  | metadata _ ih => intro f; simp only [Term.rename]; exact .metadata (ih f)
  | project _ ih => intro f; simp only [Term.rename]; exact .project (ih f)
  | nat n => intro f; exact .refl _
  | boolean b => intro f; exact .refl _
  | label l => intro f; exact .refl _
  | binary op _ _ i1 i2 => intro f; simp only [Term.rename]; exact .binary op (i1 f) (i2 f)
  | extend _ names _ i1 i2 =>
    intro f; simp only [Term.rename]
    exact .extend (i1 f) (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ f : Nat → Nat, Sim (Term.rename f x) (Term.rename f y)) _ _ i2 (fun x y h => h f))
  | record names _ ih =>
    intro f; simp only [Term.rename]
    exact .record (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ f : Nat → Nat, Sim (Term.rename f x) (Term.rename f y)) _ _ ih (fun x y h => h f))
  | get name _ ih => intro f; simp only [Term.rename]; exact .get name (ih f)
  | ifZero _ _ _ i1 i2 i3 => intro f; simp only [Term.rename]; exact .ifZero (i1 f) (i2 f) (i3 _)
  | inject l _ ih => intro f; simp only [Term.rename]; exact .inject l (ih f)
  | case _ names _ i1 i2 =>
    intro f; simp only [Term.rename]
    exact .case (i1 f) (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ f : Nat → Nat, Sim (Term.rename f x) (Term.rename f y)) _ _ i2 (fun x y h => h _))
  | ifBool _ _ _ i1 i2 i3 => intro f; simp only [Term.rename]; exact .ifBool (i1 f) (i2 f) (i3 f)
  | perform _ ih => intro f; simp only [Term.rename]; exact .perform (ih f)
  | done _ ih => intro f; simp only [Term.rename]; exact .done (ih f)
  | assocLR _ _ _ i1 i2 i3 => intro f; simp only [Term.rename]; exact .assocLR (i1 f) (i2 f) (i3 f)
  | assocRL _ _ _ i1 i2 i3 => intro f; simp only [Term.rename]; exact .assocRL (i1 f) (i2 f) (i3 f)
  | bodyLR hs _ _ _ _ _ i1 i2 i3 i4 i5 =>
    intro f; simp only [Term.rename]; exact .bodyLR (hs.rename f) (i1 f) (i2 f) (i3 f) (i4 f) (i5 f)
  | bodyRL hs _ _ _ _ _ i1 i2 i3 i4 i5 =>
    intro f; simp only [Term.rename]; exact .bodyRL (hs.rename f) (i1 f) (i2 f) (i3 f) (i4 f) (i5 f)

theorem lift {σ σ' : Nat → Term} (h : ∀ n, Sim (σ n) (σ' n)) :
    ∀ n, Sim (liftSubstitution σ n) (liftSubstitution σ' n)
  | 0 => .bound 0
  | n + 1 => (h n).rename _

/-- Substituting related settled terms into related terms gives related terms. -/
theorem subst {t t' : Term} (h : Sim t t') :
    ∀ {σ σ' : Nat → Term}, (∀ n, Sim (σ n) (σ' n)) → (∀ n, Settled (σ n)) →
      Sim (t.substitute σ) (t'.substitute σ') := by
  induction h with
  | hole n len _ ih =>
    intro σ σ' hσ hs; simp only [Term.substitute]
    exact .hole n (by simp [len]) (zip_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Sim (σ n) (σ' n)) → (∀ n, Settled (σ n)) → Sim (x.substitute σ) (y.substitute σ')) _ _ ih (fun x y h => h hσ hs))
  | bound i => intro σ σ' hσ hs; simp only [Term.substitute]; exact hσ i
  | lam _ ih => intro σ σ' hσ hs; simp only [Term.substitute]; exact .lam (ih (lift hσ) (settled_lift hs))
  | app _ _ i1 i2 => intro σ σ' hσ hs; simp only [Term.substitute]; exact .app (i1 hσ hs) (i2 hσ hs)
  | mix _ _ i1 i2 => intro σ σ' hσ hs; simp only [Term.substitute]; exact .mix (i1 hσ hs) (i2 hσ hs)
  | fix _ _ i1 i2 => intro σ σ' hσ hs; simp only [Term.substitute]; exact .fix (i1 hσ hs) (i2 hσ hs)
  | specification _ _ i1 i2 =>
    intro σ σ' hσ hs; simp only [Term.substitute]; exact .specification (i1 hσ hs) (i2 hσ hs)
  | prototype _ _ i1 i2 =>
    intro σ σ' hσ hs; simp only [Term.substitute]; exact .prototype (i1 hσ hs) (i2 hσ hs)
  | reflect _ ih => intro σ σ' hσ hs; simp only [Term.substitute]; exact .reflect (ih hσ hs)
  | metadata _ ih => intro σ σ' hσ hs; simp only [Term.substitute]; exact .metadata (ih hσ hs)
  | project _ ih => intro σ σ' hσ hs; simp only [Term.substitute]; exact .project (ih hσ hs)
  | nat n => intro σ σ' hσ hs; simp only [Term.substitute]; exact .refl _
  | boolean b => intro σ σ' hσ hs; simp only [Term.substitute]; exact .refl _
  | label l => intro σ σ' hσ hs; simp only [Term.substitute]; exact .refl _
  | binary op _ _ i1 i2 =>
    intro σ σ' hσ hs; simp only [Term.substitute]; exact .binary op (i1 hσ hs) (i2 hσ hs)
  | extend _ names _ i1 i2 =>
    intro σ σ' hσ hs; simp only [Term.substitute]
    exact .extend (i1 hσ hs) (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Sim (σ n) (σ' n)) → (∀ n, Settled (σ n)) → Sim (x.substitute σ) (y.substitute σ')) _ _ i2 (fun x y h => h hσ hs))
  | record names _ ih =>
    intro σ σ' hσ hs; simp only [Term.substitute]
    exact .record (fields_map_names _ _ names) (fields_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Sim (σ n) (σ' n)) → (∀ n, Settled (σ n)) → Sim (x.substitute σ) (y.substitute σ')) _ _ ih (fun x y h => h hσ hs))
  | get name _ ih => intro σ σ' hσ hs; simp only [Term.substitute]; exact .get name (ih hσ hs)
  | ifZero _ _ _ i1 i2 i3 =>
    intro σ σ' hσ hs; simp only [Term.substitute]
    exact .ifZero (i1 hσ hs) (i2 hσ hs) (i3 (lift hσ) (settled_lift hs))
  | inject l _ ih => intro σ σ' hσ hs; simp only [Term.substitute]; exact .inject l (ih hσ hs)
  | case _ names _ i1 i2 =>
    intro σ σ' hσ hs; simp only [Term.substitute]
    exact .case (i1 hσ hs) (fields_map_names _ _ names)
      (fields_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term}, (∀ n, Sim (σ n) (σ' n)) → (∀ n, Settled (σ n)) → Sim (x.substitute σ) (y.substitute σ')) _ _ i2 (fun x y h => h (lift hσ) (settled_lift hs)))
  | ifBool _ _ _ i1 i2 i3 =>
    intro σ σ' hσ hs; simp only [Term.substitute]; exact .ifBool (i1 hσ hs) (i2 hσ hs) (i3 hσ hs)
  | perform _ ih => intro σ σ' hσ hs; simp only [Term.substitute]; exact .perform (ih hσ hs)
  | done _ ih => intro σ σ' hσ hs; simp only [Term.substitute]; exact .done (ih hσ hs)
  | assocLR _ _ _ i1 i2 i3 =>
    intro σ σ' hσ hs; simp only [Term.substitute]; exact .assocLR (i1 hσ hs) (i2 hσ hs) (i3 hσ hs)
  | assocRL _ _ _ i1 i2 i3 =>
    intro σ σ' hσ hs; simp only [Term.substitute]; exact .assocRL (i1 hσ hs) (i2 hσ hs) (i3 hσ hs)
  | bodyLR hset _ _ _ _ _ i1 i2 i3 i4 i5 =>
    intro σ σ' hσ hs; simp only [Term.substitute]
    exact .bodyLR (hset.substitute hs) (i1 hσ hs) (i2 hσ hs) (i3 hσ hs) (i4 hσ hs) (i5 hσ hs)
  | bodyRL hset _ _ _ _ _ i1 i2 i3 i4 i5 =>
    intro σ σ' hσ hs; simp only [Term.substitute]
    exact .bodyRL (hset.substitute hs) (i1 hσ hs) (i2 hσ hs) (i3 hσ hs) (i4 hσ hs) (i5 hσ hs)

theorem instantiate {b b' x x' : Term} (hb : Sim b b') (hx : Sim x x') (hs : Settled x) :
    Sim (Obend.Core.Term.instantiate b x) (Obend.Core.Term.instantiate b' x') := by
  rw [instantiate_eq, instantiate_eq]
  exact hb.subst (fun n => match n with | 0 => hx | n + 1 => .bound n) (settled_single hs)

set_option linter.unusedVariables false in
/-- A context related to itself, with related terms (settled or not) substituted for its
variables. No base case of `Sim` is needed, so no settledness is. -/
theorem substRefl : (C : Term) → ∀ {σ σ' : Nat → Term}, (∀ n, Sim (σ n) (σ' n)) →
    Sim (C.substitute σ) (C.substitute σ')
  | .hole n ts, σ, σ', h => by
    simp only [Term.substitute]
    exact .hole n (by simp) (by
      intro p hp
      rw [List.zip_map] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      obtain ⟨e, mem⟩ := zip_self ts q hq
      show Sim (q.1.substitute σ) (q.2.substitute σ')
      rw [← e]; exact substRefl q.1 h)
  | .bound i, σ, σ', h => by simp only [Term.substitute]; exact h i
  | .lam b, σ, σ', h => by simp only [Term.substitute]; exact .lam (substRefl b (lift h))
  | .app f a, σ, σ', h => by simp only [Term.substitute]; exact .app (substRefl f h) (substRefl a h)
  | .mix l u, σ, σ', h => by simp only [Term.substitute]; exact .mix (substRefl l h) (substRefl u h)
  | .fix s i, σ, σ', h => by simp only [Term.substitute]; exact .fix (substRefl s h) (substRefl i h)
  | .specification m e, σ, σ', h => by
    simp only [Term.substitute]; exact .specification (substRefl m h) (substRefl e h)
  | .prototype s g, σ, σ', h => by
    simp only [Term.substitute]; exact .prototype (substRefl s h) (substRefl g h)
  | .reflect p, σ, σ', h => by simp only [Term.substitute]; exact .reflect (substRefl p h)
  | .metadata p, σ, σ', h => by simp only [Term.substitute]; exact .metadata (substRefl p h)
  | .project p, σ, σ', h => by simp only [Term.substitute]; exact .project (substRefl p h)
  | .nat n, σ, σ', h => by simp only [Term.substitute]; exact .nat n
  | .boolean b, σ, σ', h => by simp only [Term.substitute]; exact .boolean b
  | .label l, σ, σ', h => by simp only [Term.substitute]; exact .label l
  | .binary op l r, σ, σ', h => by
    simp only [Term.substitute]; exact .binary op (substRefl l h) (substRefl r h)
  | .extend i fs, σ, σ', h => by
    simp only [Term.substitute]
    refine .extend (substRefl i h) (fields_map_names _ _ rfl) ?_
    intro p hp
    rw [List.zip_map] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨e, mem⟩ := zip_self fs q hq
    show Sim (q.1.2.substitute σ) (q.2.2.substitute σ')
    rw [← e]; exact substRefl q.1.2 h
  | .record fs, σ, σ', h => by
    simp only [Term.substitute]
    refine .record (fields_map_names _ _ rfl) ?_
    intro p hp
    rw [List.zip_map] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨e, mem⟩ := zip_self fs q hq
    show Sim (q.1.2.substitute σ) (q.2.2.substitute σ')
    rw [← e]; exact substRefl q.1.2 h
  | .get g name, σ, σ', h => by simp only [Term.substitute]; exact .get name (substRefl g h)
  | .ifZero v z s, σ, σ', h => by
    simp only [Term.substitute]; exact .ifZero (substRefl v h) (substRefl z h) (substRefl s (lift h))
  | .inject l p, σ, σ', h => by simp only [Term.substitute]; exact .inject l (substRefl p h)
  | .case sc arms, σ, σ', h => by
    simp only [Term.substitute]
    refine .case (substRefl sc h) (fields_map_names _ _ rfl) ?_
    intro p hp
    rw [List.zip_map] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨e, mem⟩ := zip_self arms q hq
    show Sim (q.1.2.substitute (liftSubstitution σ)) (q.2.2.substitute (liftSubstitution σ'))
    rw [← e]; exact substRefl q.1.2 (lift h)
  | .ifBool c x y, σ, σ', h => by
    simp only [Term.substitute]; exact .ifBool (substRefl c h) (substRefl x h) (substRefl y h)
  | .perform p, σ, σ', h => by simp only [Term.substitute]; exact .perform (substRefl p h)
  | .done v, σ, σ', h => by simp only [Term.substitute]; exact .done (substRefl v h)
termination_by C => sizeOf C
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem mem; omega)
    | (have hlist := List.sizeOf_lt_of_mem mem
       have hpair : sizeOf q.1.snd < sizeOf q.1 := by cases q.1; simp +arith
       omega)

end Sim

/-! ## Settled terms and values correspond -/

theorem zip_right_of_mem {α : Type} : ∀ {l l' : List α}, l.length = l'.length → ∀ {y : α}, y ∈ l' →
    ∃ x ∈ l, (x, y) ∈ l.zip l'
  | [], [], _, _, h => by simp at h
  | [], _ :: _, len, _, _ => by simp at len
  | _ :: _, [], len, _, _ => by simp at len
  | x :: l, y' :: l', len, y, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨x, by simp, by simp⟩
    · obtain ⟨z, hz, hzip⟩ := zip_right_of_mem (by simpa using len) h
      exact ⟨z, List.mem_cons_of_mem _ hz, by simp [hzip]⟩

theorem zip_left_of_mem {α : Type} : ∀ {l l' : List α}, l.length = l'.length → ∀ {x : α}, x ∈ l →
    ∃ y ∈ l', (x, y) ∈ l.zip l'
  | [], [], _, _, h => by simp at h
  | [], _ :: _, len, _, _ => by simp at len
  | _ :: _, [], len, _, _ => by simp at len
  | x' :: l, y :: l', len, x, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨y, by simp, by simp⟩
    · obtain ⟨z, hz, hzip⟩ := zip_left_of_mem (by simpa using len) h
      exact ⟨z, List.mem_cons_of_mem _ hz, by simp [hzip]⟩

theorem Sim.ready_fwd {b : Bool} {t : Term} (h : Ready b t) : ∀ {t' : Term}, Sim t t' → Ready b t' := by
  induction h with
  | lam b => intro t' hs; cases hs; exact .lam _
  | nat n => intro t' hs; cases hs; exact .nat n
  | boolean b => intro t' hs; cases hs; exact .boolean b
  | label l => intro t' hs; cases hs; exact .label l
  | record _ ih =>
    intro t' hs
    cases hs with
    | record names rel =>
      refine .record ?_
      intro f hf
      obtain ⟨g, hg, hzip⟩ := zip_right_of_mem (length_of_names names) hf
      exact ih g hg (rel _ hzip)
  | specification _ _ i1 i2 => intro t' hs; cases hs with | specification h1 h2 => exact .specification (i1 h1) (i2 h2)
  | prototype _ _ i1 i2 => intro t' hs; cases hs with | prototype h1 h2 => exact .prototype (i1 h1) (i2 h2)
  | inject l _ ih => intro t' hs; cases hs with | inject _ h1 => exact .inject l (ih h1)
  | value _ ih => intro t' hs; exact .value (ih hs)
  | skipped =>
    intro t' hs
    cases hs with
    | hole n len rel =>
      rename_i σ'
      cases σ' with
      | nil => exact .skipped
      | cons _ _ => simp at len
  | bound i => intro t' hs; cases hs; exact .bound i
  | knot _ _ i1 i2 =>
    intro t' hs
    cases hs with
    | fix h1 h2 =>
      cases h1 with
      | lam h3 => cases h3 with | lam h4 => exact .knot (i1 h4) (i2 h2)

theorem Sim.ready_bwd {b : Bool} {t' : Term} (h : Ready b t') : ∀ {t : Term}, Sim t t' → Ready b t := by
  induction h with
  | lam b => intro t hs; cases hs; exact .lam _
  | nat n => intro t hs; cases hs; exact .nat n
  | boolean b => intro t hs; cases hs; exact .boolean b
  | label l => intro t hs; cases hs; exact .label l
  | record _ ih =>
    intro t hs
    cases hs with
    | record names rel =>
      refine .record ?_
      intro f hf
      obtain ⟨g, hg, hzip⟩ := zip_left_of_mem (length_of_names names) hf
      exact ih g hg (rel _ hzip)
  | specification _ _ i1 i2 => intro t hs; cases hs with | specification h1 h2 => exact .specification (i1 h1) (i2 h2)
  | prototype _ _ i1 i2 => intro t hs; cases hs with | prototype h1 h2 => exact .prototype (i1 h1) (i2 h2)
  | inject l _ ih => intro t hs; cases hs with | inject _ h1 => exact .inject l (ih h1)
  | value _ ih => intro t hs; exact .value (ih hs)
  | skipped =>
    intro t hs
    cases hs with
    | hole n len rel =>
      rename_i σ
      cases σ with
      | nil => exact .skipped
      | cons _ _ => simp at len
  | bound i => intro t hs; cases hs; exact .bound i
  | knot _ _ i1 i2 =>
    intro t hs
    cases hs with
    | fix h1 h2 =>
      cases h1 with
      | lam h3 => cases h3 with | lam h4 => exact .knot (i1 h4) (i2 h2)

theorem Sim.ready_iff {b : Bool} {t t' : Term} (hs : Sim t t') : Ready b t ↔ Ready b t' :=
  ⟨fun h => Sim.ready_fwd h hs, fun h => Sim.ready_bwd h hs⟩

end Obend.Equiv
end
