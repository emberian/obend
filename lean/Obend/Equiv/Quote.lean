module
/-
# Obend.Equiv.Quote — the observer ladder: `≈q ⊆ ≈r ⊆ ≈b`, and the rewriter's licence

Three equivalences, each induced by a class of observers (orientation §3.4,
`review/QUOTE-ORIENTATION-20261101.md`; minidregg `docs/objective-bend/REFLECTION.md`):

* `≈b` — contexts of census `b`: no `metadata` observer outside a specification's own metadata
  field. They see specifications only by running them, so specifications that differ only in
  metadata are `≈b` (`blind_observed`).
* `≈r` — every Core4 context, `metadata` included. This is `Equiv/Behaviour`'s `BEquiv`
  (`observed_r_iff`): that relation quantifies over all contexts, so it is the reflective one.
* `≈q` — equality of `encode` (α-equality): what the kernel's `quote` observes.

`observer_ladder : ≈q ⊆ ≈r ⊆ ≈b`, strict at both steps: Barendregt's pair `(λx.x)(λx.x)` and
`λx.x` is `≈r` and not `≈q` (`quote_not_congruent`), and REFLECTION's probes R01/R02 make the two
associations of `compose` `≈b` and not `≈r` (`compose_assoc_b`, `compose_not_assoc_r`).

`rewrite_sound_below k`: an observer of census at most `k` preserves `≈k`. It is the Core4 form of
"no congruence under box": a `metadata` frame (census `r`) does not preserve `≈b`, and a `quote`
(census `q`) does not preserve even `≈r`; both refutations are proved here.

The census is a syntactic fold (`observes`); its meaning is `Blind`, the relation "equal up to the
metadata of specifications, with no `metadata` observer", which is a weak-head simulation.
-/
public import Obend.Equiv.Behaviour
public import Obend.Core.Code
public import Obend.Law.Proofs.Run
@[expose] public section
namespace Obend.Equiv
open Obend.Core.Term
open Obend.Core.TermTraverse (encode encode_injective substitute_comp)
set_option autoImplicit false

/-! ## §1. `Blind`: equal up to specification metadata, with no `metadata` observer -/

/-- `Blind t t'`: the same term except in the metadata field of specifications, and with no
`metadata` node anywhere else. There is no `metadata` constructor: a blind term never asks. -/
inductive Blind : Term → Term → Prop where
  | hole (n : Nat) {σ σ' : List Term} : σ.length = σ'.length →
      (∀ p ∈ σ.zip σ', Blind p.1 p.2) → Blind (.hole n σ) (.hole n σ')
  | bound (i : Nat) : Blind (.bound i) (.bound i)
  | lam {b b' : Term} : Blind b b' → Blind (.lam b) (.lam b')
  | app {f f' a a' : Term} : Blind f f' → Blind a a' → Blind (.app f a) (.app f' a')
  | mix {l l' u u' : Term} : Blind l l' → Blind u u' → Blind (.mix l u) (.mix l' u')
  | fix {s s' i i' : Term} : Blind s s' → Blind i i' → Blind (.fix s i) (.fix s' i')
  | specification (m m' : Term) {e e' : Term} : Blind e e' →
      Blind (.specification m e) (.specification m' e')
  | prototype {s s' g g' : Term} : Blind s s' → Blind g g' →
      Blind (.prototype s g) (.prototype s' g')
  | reflect {p p' : Term} : Blind p p' → Blind (.reflect p) (.reflect p')
  | project {p p' : Term} : Blind p p' → Blind (.project p) (.project p')
  | nat (n : Nat) : Blind (.nat n) (.nat n)
  | boolean (b : Bool) : Blind (.boolean b) (.boolean b)
  | label (l : String) : Blind (.label l) (.label l)
  | binary (op : Primitive) {l l' r r' : Term} : Blind l l' → Blind r r' →
      Blind (.binary op l r) (.binary op l' r')
  | extend {i i' : Term} {fs fs' : List (String × Term)} : Blind i i' →
      fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', Blind p.1.2 p.2.2) →
      Blind (.extend i fs) (.extend i' fs')
  | record {fs fs' : List (String × Term)} :
      fs.map Prod.fst = fs'.map Prod.fst → (∀ p ∈ fs.zip fs', Blind p.1.2 p.2.2) →
      Blind (.record fs) (.record fs')
  | get (name : String) {g g' : Term} : Blind g g' → Blind (.get g name) (.get g' name)
  | ifZero {v v' z z' s s' : Term} : Blind v v' → Blind z z' → Blind s s' →
      Blind (.ifZero v z s) (.ifZero v' z' s')
  | inject (l : String) {p p' : Term} : Blind p p' → Blind (.inject l p) (.inject l p')
  | case {sc sc' : Term} {arms arms' : List (String × Term)} : Blind sc sc' →
      arms.map Prod.fst = arms'.map Prod.fst → (∀ p ∈ arms.zip arms', Blind p.1.2 p.2.2) →
      Blind (.case sc arms) (.case sc' arms')
  | ifBool {c c' x x' y y' : Term} : Blind c c' → Blind x x' → Blind y y' →
      Blind (.ifBool c x y) (.ifBool c' x' y')
  | perform {p p' : Term} : Blind p p' → Blind (.perform p) (.perform p')
  | done {v v' : Term} : Blind v v' → Blind (.done v) (.done v')

/-- A term no context of census `b` could tell from itself by metadata: it never asks. -/
def ObsFree (t : Term) : Prop := Blind t t

theorem zip_swap_rel {α : Type} {R : α → α → Prop} :
    ∀ {l l' : List α}, (∀ p ∈ l.zip l', R p.1 p.2) → ∀ p ∈ l'.zip l, R p.2 p.1
  | [], _, _, _, hp => by simp at hp
  | _ :: _, [], _, _, hp => by simp at hp
  | a :: l, b :: l', h, p, hp => by
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h (a, b) (by simp)
    · exact zip_swap_rel (fun q hq => h q (by simp [hq])) p hp

theorem Blind.symm {t t' : Term} (h : Blind t t') : Blind t' t := by
  induction h with
  | hole n len _ ih => exact .hole n len.symm (zip_swap_rel (R := fun a b => Blind b a) ih)
  | bound i => exact .bound i
  | lam _ ih => exact .lam ih
  | app _ _ i1 i2 => exact .app i1 i2
  | mix _ _ i1 i2 => exact .mix i1 i2
  | fix _ _ i1 i2 => exact .fix i1 i2
  | specification m m' _ ih => exact .specification m' m ih
  | prototype _ _ i1 i2 => exact .prototype i1 i2
  | reflect _ ih => exact .reflect ih
  | project _ ih => exact .project ih
  | nat n => exact .nat n
  | boolean b => exact .boolean b
  | label l => exact .label l
  | binary op _ _ i1 i2 => exact .binary op i1 i2
  | extend _ names _ i1 i2 =>
    exact .extend i1 names.symm (zip_swap_rel (R := fun (a b : String × Term) => Blind b.2 a.2) i2)
  | record names _ ih => exact .record names.symm (zip_swap_rel (R := fun (a b : String × Term) => Blind b.2 a.2) ih)
  | get name _ ih => exact .get name ih
  | ifZero _ _ _ i1 i2 i3 => exact .ifZero i1 i2 i3
  | inject l _ ih => exact .inject l ih
  | case _ names _ i1 i2 =>
    exact .case i1 names.symm (zip_swap_rel (R := fun (a b : String × Term) => Blind b.2 a.2) i2)
  | ifBool _ _ _ i1 i2 i3 => exact .ifBool i1 i2 i3
  | perform _ ih => exact .perform ih
  | done _ ih => exact .done ih

/-! ### Closure under renaming and substitution -/

theorem blind_rename {t t' : Term} (h : Blind t t') :
    ∀ f : Nat → Nat, Blind (t.rename f) (t'.rename f) := by
  induction h with
  | hole n len _ ih =>
    intro f; simp only [Term.rename]
    exact .hole n (by simp [len]) (zip_map_rel (R := fun x y => ∀ f : Nat → Nat,
      Blind (Term.rename f x) (Term.rename f y)) _ _ ih (fun x y h => h f))
  | bound i => intro f; simp only [Term.rename]; exact .bound _
  | lam _ ih => intro f; simp only [Term.rename]; exact .lam (ih _)
  | app _ _ i1 i2 => intro f; simp only [Term.rename]; exact .app (i1 f) (i2 f)
  | mix _ _ i1 i2 => intro f; simp only [Term.rename]; exact .mix (i1 f) (i2 f)
  | fix _ _ i1 i2 => intro f; simp only [Term.rename]; exact .fix (i1 f) (i2 f)
  | specification m m' _ ih => intro f; simp only [Term.rename]; exact .specification _ _ (ih f)
  | prototype _ _ i1 i2 => intro f; simp only [Term.rename]; exact .prototype (i1 f) (i2 f)
  | reflect _ ih => intro f; simp only [Term.rename]; exact .reflect (ih f)
  | project _ ih => intro f; simp only [Term.rename]; exact .project (ih f)
  | nat n => intro f; simp only [Term.rename]; exact .nat n
  | boolean b => intro f; simp only [Term.rename]; exact .boolean b
  | label l => intro f; simp only [Term.rename]; exact .label l
  | binary op _ _ i1 i2 => intro f; simp only [Term.rename]; exact .binary op (i1 f) (i2 f)
  | extend _ names _ i1 i2 =>
    intro f; simp only [Term.rename]
    exact .extend (i1 f) (fields_map_names _ _ names) (fields_map_rel (R := fun x y =>
      ∀ f : Nat → Nat, Blind (Term.rename f x) (Term.rename f y)) _ _ i2 (fun x y h => h f))
  | record names _ ih =>
    intro f; simp only [Term.rename]
    exact .record (fields_map_names _ _ names) (fields_map_rel (R := fun x y =>
      ∀ f : Nat → Nat, Blind (Term.rename f x) (Term.rename f y)) _ _ ih (fun x y h => h f))
  | get name _ ih => intro f; simp only [Term.rename]; exact .get name (ih f)
  | ifZero _ _ _ i1 i2 i3 => intro f; simp only [Term.rename]; exact .ifZero (i1 f) (i2 f) (i3 _)
  | inject l _ ih => intro f; simp only [Term.rename]; exact .inject l (ih f)
  | case _ names _ i1 i2 =>
    intro f; simp only [Term.rename]
    exact .case (i1 f) (fields_map_names _ _ names) (fields_map_rel (R := fun x y =>
      ∀ f : Nat → Nat, Blind (Term.rename f x) (Term.rename f y)) _ _ i2 (fun x y h => h _))
  | ifBool _ _ _ i1 i2 i3 => intro f; simp only [Term.rename]; exact .ifBool (i1 f) (i2 f) (i3 f)
  | perform _ ih => intro f; simp only [Term.rename]; exact .perform (ih f)
  | done _ ih => intro f; simp only [Term.rename]; exact .done (ih f)

theorem blind_lift {σ σ' : Nat → Term} (h : ∀ n, Blind (σ n) (σ' n)) :
    ∀ n, Blind (liftSubstitution σ n) (liftSubstitution σ' n)
  | 0 => .bound 0
  | n + 1 => blind_rename (h n) _

theorem blind_substitute {t t' : Term} (h : Blind t t') :
    ∀ {σ σ' : Nat → Term}, (∀ n, Blind (σ n) (σ' n)) → Blind (t.substitute σ) (t'.substitute σ') := by
  induction h with
  | hole n len _ ih =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .hole n (by simp [len]) (zip_map_rel (R := fun x y => ∀ {σ σ' : Nat → Term},
      (∀ n, Blind (σ n) (σ' n)) → Blind (x.substitute σ) (y.substitute σ')) _ _ ih (fun x y h => h hσ))
  | bound i => intro σ σ' hσ; simp only [Term.substitute]; exact hσ i
  | lam _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .lam (ih (blind_lift hσ))
  | app _ _ i1 i2 => intro σ σ' hσ; simp only [Term.substitute]; exact .app (i1 hσ) (i2 hσ)
  | mix _ _ i1 i2 => intro σ σ' hσ; simp only [Term.substitute]; exact .mix (i1 hσ) (i2 hσ)
  | fix _ _ i1 i2 => intro σ σ' hσ; simp only [Term.substitute]; exact .fix (i1 hσ) (i2 hσ)
  | specification m m' _ ih =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .specification _ _ (ih hσ)
  | prototype _ _ i1 i2 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .prototype (i1 hσ) (i2 hσ)
  | reflect _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .reflect (ih hσ)
  | project _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .project (ih hσ)
  | nat n => intro σ σ' hσ; simp only [Term.substitute]; exact .nat n
  | boolean b => intro σ σ' hσ; simp only [Term.substitute]; exact .boolean b
  | label l => intro σ σ' hσ; simp only [Term.substitute]; exact .label l
  | binary op _ _ i1 i2 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .binary op (i1 hσ) (i2 hσ)
  | extend _ names _ i1 i2 =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .extend (i1 hσ) (fields_map_names _ _ names) (fields_map_rel (R := fun x y =>
      ∀ {σ σ' : Nat → Term}, (∀ n, Blind (σ n) (σ' n)) → Blind (x.substitute σ) (y.substitute σ'))
      _ _ i2 (fun x y h => h hσ))
  | record names _ ih =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .record (fields_map_names _ _ names) (fields_map_rel (R := fun x y =>
      ∀ {σ σ' : Nat → Term}, (∀ n, Blind (σ n) (σ' n)) → Blind (x.substitute σ) (y.substitute σ'))
      _ _ ih (fun x y h => h hσ))
  | get name _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .get name (ih hσ)
  | ifZero _ _ _ i1 i2 i3 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .ifZero (i1 hσ) (i2 hσ) (i3 (blind_lift hσ))
  | inject l _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .inject l (ih hσ)
  | case _ names _ i1 i2 =>
    intro σ σ' hσ; simp only [Term.substitute]
    exact .case (i1 hσ) (fields_map_names _ _ names) (fields_map_rel (R := fun x y =>
      ∀ {σ σ' : Nat → Term}, (∀ n, Blind (σ n) (σ' n)) → Blind (x.substitute σ) (y.substitute σ'))
      _ _ i2 (fun x y h => h (blind_lift hσ)))
  | ifBool _ _ _ i1 i2 i3 =>
    intro σ σ' hσ; simp only [Term.substitute]; exact .ifBool (i1 hσ) (i2 hσ) (i3 hσ)
  | perform _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .perform (ih hσ)
  | done _ ih => intro σ σ' hσ; simp only [Term.substitute]; exact .done (ih hσ)

theorem blind_single {a a' : Term} (h : Blind a a') : ∀ n, Blind (single a n) (single a' n)
  | 0 => h
  | n + 1 => .bound n

theorem blind_instantiate {b b' a a' : Term} (hb : Blind b b') (ha : Blind a a') :
    Blind (instantiate b a) (instantiate b' a') := by
  rw [instantiate_eq, instantiate_eq]; exact blind_substitute hb (blind_single ha)

theorem blind_mixBody {l l' u u' : Term} (hl : Blind l l') (hu : Blind u u') :
    Blind (mixBody l u) (mixBody l' u') :=
  .lam (.lam (.app (.app (blind_rename hu _) (.bound 1))
    (.app (.app (blind_rename hl _) (.bound 1)) (.bound 0))))

/-! ### `Blind` is a weak-head simulation -/

theorem blind_literal {v v' : Term} (lit : Literal v) (h : Blind v v') : v' = v := by
  cases lit <;> cases h <;> rfl

theorem blind_value {v v' : Term} (value : Value v) (h : Blind v v') : Value v' := by
  cases value <;> cases h <;> constructor

/-- A step of one blind term is matched by a step of the other. -/
theorem step_blind {t t' : Term} (h : Blind t t') :
    ∀ {u : Term}, Step t u → ∃ u', Step t' u' ∧ Blind u u' := by
  induction h with
  | hole => intro u st; cases st
  | bound => intro u st; cases st
  | lam => intro u st; cases st
  | app hf ha ihf _ =>
    intro u st
    cases st with
    | beta => cases hf with | lam hb => exact ⟨_, .beta _ _, blind_instantiate hb ha⟩
    | application _ st' => obtain ⟨_, s, b⟩ := ihf st'; exact ⟨_, .application _ s, .app b ha⟩
    | applySpecification =>
      cases hf with | specification _ _ he => exact ⟨_, .applySpecification _ _ _, .app he ha⟩
  | mix hl hu _ _ => intro u st; cases st; exact ⟨_, .mix _ _, blind_mixBody hl hu⟩
  | fix hs hi _ _ => intro u st; cases st; exact ⟨_, .fix _ _, .app (.app hs (.fix hs hi)) hi⟩
  | specification => intro u st; cases st
  | prototype => intro u st; cases st
  | reflect hp ihp =>
    intro u st
    cases st with
    | reflectPrototype => cases hp with | prototype hs _ => exact ⟨_, .reflectPrototype _ _, hs⟩
    | reflectStep st' => obtain ⟨_, s, b⟩ := ihp st'; exact ⟨_, .reflectStep s, .reflect b⟩
  | project hp ihp =>
    intro u st
    cases st with
    | projectPrototype => cases hp with | prototype _ hg => exact ⟨_, .projectPrototype _ _, hg⟩
    | projectStep st' => obtain ⟨_, s, b⟩ := ihp st'; exact ⟨_, .projectStep s, .project b⟩
  | nat => intro u st; cases st
  | boolean => intro u st; cases st
  | label => intro u st; cases st
  | binary op hl hr ihl ihr =>
    intro u st
    cases st with
    | binaryLeft _ _ st' => obtain ⟨_, s, b⟩ := ihl st'; exact ⟨_, .binaryLeft _ _ s, .binary op b hr⟩
    | binaryRight _ _ value st' =>
      obtain ⟨_, s, b⟩ := ihr st'
      exact ⟨_, .binaryRight _ _ (blind_value value hl) s, .binary op hl b⟩
    | primitive _ _ _ _ vl vr res =>
      obtain ⟨ll, lr, lres⟩ := primitiveResult_literal res
      rw [blind_literal ll hl, blind_literal lr hr]
      exact ⟨_, .primitive _ _ _ _ vl vr res, by cases lres <;> constructor⟩
  | extend hi names hfs ihi _ =>
    intro u st
    cases st with
    | extendTarget _ st' => obtain ⟨_, s, b⟩ := ihi st'; exact ⟨_, .extendTarget _ s, .extend b names hfs⟩
    | extendRecord =>
      cases hi with
      | record namesI relI =>
        obtain ⟨n, r⟩ := extendFields_rel namesI relI names hfs
        exact ⟨_, .extendRecord _ _, .record n r⟩
  | record => intro u st; cases st
  | get name hg ihg =>
    intro u st
    cases st with
    | target _ st' => obtain ⟨_, s, b⟩ := ihg st'; exact ⟨_, .target _ s, .get name b⟩
    | field _ _ _ hit =>
      cases hg with
      | record names rel =>
        obtain ⟨_, hit', b⟩ := find_left names rel hit
        exact ⟨_, .field _ _ _ hit', b⟩
  | ifZero hv hz hs ihv _ _ =>
    intro u st
    cases st with
    | condition _ _ st' => obtain ⟨_, s, b⟩ := ihv st'; exact ⟨_, .condition _ _ s, .ifZero b hz hs⟩
    | zero => cases hv; exact ⟨_, .zero _ _, hz⟩
    | successor n => cases hv; exact ⟨_, .successor _ _ _, blind_instantiate hs (.nat n)⟩
  | inject => intro u st; cases st
  | case hsc names harms ihsc _ =>
    intro u st
    cases st with
    | caseTarget _ st' => obtain ⟨_, s, b⟩ := ihsc st'; exact ⟨_, .caseTarget _ s, .case b names harms⟩
    | caseInject _ _ _ _ hit =>
      cases hsc with
      | inject _ hp =>
        obtain ⟨_, hit', b⟩ := find_left names harms hit
        exact ⟨_, .caseInject _ _ _ _ hit', blind_instantiate b hp⟩
  | ifBool hc hx hy ihc _ _ =>
    intro u st
    cases st with
    | ifCondition _ _ st' => obtain ⟨_, s, b⟩ := ihc st'; exact ⟨_, .ifCondition _ _ s, .ifBool b hx hy⟩
    | ifTrue => cases hc; exact ⟨_, .ifTrue _ _, hx⟩
    | ifFalse => cases hc; exact ⟨_, .ifFalse _ _, hy⟩
  | perform => intro u st; cases st
  | done hv _ => intro u st; cases st; exact ⟨_, .done _, hv⟩

theorem steps_blind {t t' u : Term} (h : Blind t t') (s : Steps t u) : ∃ u', Steps t' u' ∧ Blind u u' := by
  induction s generalizing t' with
  | refl => exact ⟨_, .refl _, h⟩
  | next st _ ih =>
    obtain ⟨_, st', b⟩ := step_blind h st
    obtain ⟨u', s', b'⟩ := ih b
    exact ⟨u', .next st' s', b'⟩

theorem evaluates_blind {t t' v : Term} (h : Blind t t') (e : Evaluates t v) :
    ∃ v', Evaluates t' v' ∧ Blind v v' := by
  obtain ⟨v', s, b⟩ := steps_blind h e.1
  exact ⟨v', ⟨s, blind_value e.2 b⟩, b⟩

/-- Blind terms have the same completed runs. -/
theorem sameRuns_of_blind {t t' : Term} (h : Blind t t') : SameRuns t t' where
  halts o := by
    constructor
    · rintro ⟨v, e, obs⟩
      obtain ⟨v', e', b⟩ := evaluates_blind h e
      exact ⟨v', e', blind_literal (observes_literal obs) b ▸ obs⟩
    · rintro ⟨v', e', obs⟩
      obtain ⟨v, e, b⟩ := evaluates_blind h.symm e'
      exact ⟨v, e, blind_literal (observes_literal obs) b ▸ obs⟩
  converges := by
    constructor
    · rintro ⟨v, e⟩; obtain ⟨v', e', _⟩ := evaluates_blind h e; exact ⟨v', e'⟩
    · rintro ⟨v', e'⟩; obtain ⟨v, e, _⟩ := evaluates_blind h.symm e'; exact ⟨v, e⟩

/-! ## §2. The census: which observer a context is -/

/-- Does `t` hold a `metadata` observer outside a specification's own metadata field? -/
def observes : Term → Bool
  | .hole _ σ => (σ.map observes).any id
  | .bound _ | .nat _ | .boolean _ | .label _ => false
  | .lam b => observes b
  | .app a b | .mix a b | .fix a b | .prototype a b | .binary _ a b => observes a || observes b
  | .specification _ e => observes e
  | .reflect a | .project a | .get a _ | .inject _ a | .perform a | .done a => observes a
  | .metadata _ => true
  | .extend a fs => observes a || (fs.map fun f => observes f.2).any id
  | .record fs => (fs.map fun f => observes f.2).any id
  | .ifZero a b c | .ifBool a b c => observes a || observes b || observes c
  | .case a arms => observes a || (arms.map fun f => observes f.2).any id
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf f.snd < sizeOf f := by cases f; simp +arith
       omega)

/-- The three observer levels, weakest first: `b` runs what it is given, `r` may also read a
specification's metadata, `q` reads the whole term (the kernel's `quote`). -/
inductive Level where
  | b | r | q
  deriving DecidableEq, Repr

def Level.rank : Level → Nat
  | .b => 0 | .r => 1 | .q => 2

instance : LE Level := ⟨fun x y => x.rank ≤ y.rank⟩
instance (x y : Level) : Decidable (x ≤ y) := inferInstanceAs (Decidable (x.rank ≤ y.rank))

/-- **The census** of a Core4 context: `r` if it holds a `metadata` observer, else `b`. -/
def census (t : Term) : Level := if observes t then .r else .b

theorem any_false {xs : List Term} (h : (xs.map observes).any id = false) :
    ∀ x ∈ xs, observes x = false := by
  intro x hx
  simp only [List.any_eq_false, List.mem_map, id] at h
  cases hobs : observes x
  · rfl
  · exact absurd hobs (fun e => h true ⟨x, hx, e⟩ rfl)

theorem any_fields_false {fs : List (String × Term)} (h : (fs.map fun f => observes f.2).any id = false) :
    ∀ f ∈ fs, observes f.2 = false := by
  intro f hf
  simp only [List.any_eq_false, List.mem_map, id] at h
  cases hobs : observes f.2
  · rfl
  · exact absurd hobs (fun e => h true ⟨f, hf, e⟩ rfl)

/-- What the census means: a context of census `b` asks no metadata. -/
theorem obsFree_of_observes : (t : Term) → observes t = false → ObsFree t
  | .hole n σ, h => by
    have hσ := any_false (by simpa [observes] using h)
    exact .hole n rfl (zip_refl (fun a b => Blind a b) σ (fun x hx => obsFree_of_observes x (hσ x hx)))
  | .bound i, _ => .bound i
  | .nat n, _ => .nat n
  | .boolean b, _ => .boolean b
  | .label l, _ => .label l
  | .lam b, h => .lam (obsFree_of_observes b (by simpa [observes] using h))
  | .app a b, h => by
    simp only [observes, Bool.or_eq_false_iff] at h
    exact .app (obsFree_of_observes a h.1) (obsFree_of_observes b h.2)
  | .mix a b, h => by
    simp only [observes, Bool.or_eq_false_iff] at h
    exact .mix (obsFree_of_observes a h.1) (obsFree_of_observes b h.2)
  | .fix a b, h => by
    simp only [observes, Bool.or_eq_false_iff] at h
    exact .fix (obsFree_of_observes a h.1) (obsFree_of_observes b h.2)
  | .prototype a b, h => by
    simp only [observes, Bool.or_eq_false_iff] at h
    exact .prototype (obsFree_of_observes a h.1) (obsFree_of_observes b h.2)
  | .binary op a b, h => by
    simp only [observes, Bool.or_eq_false_iff] at h
    exact .binary op (obsFree_of_observes a h.1) (obsFree_of_observes b h.2)
  | .specification m e, h => .specification m m (obsFree_of_observes e (by simpa [observes] using h))
  | .reflect a, h => .reflect (obsFree_of_observes a (by simpa [observes] using h))
  | .project a, h => .project (obsFree_of_observes a (by simpa [observes] using h))
  | .get a n, h => .get n (obsFree_of_observes a (by simpa [observes] using h))
  | .inject l a, h => .inject l (obsFree_of_observes a (by simpa [observes] using h))
  | .perform a, h => .perform (obsFree_of_observes a (by simpa [observes] using h))
  | .done a, h => .done (obsFree_of_observes a (by simpa [observes] using h))
  | .metadata _, h => by simp [observes] at h
  | .extend a fs, h => by
    simp only [observes, Bool.or_eq_false_iff] at h
    have hfs := any_fields_false h.2
    exact .extend (obsFree_of_observes a h.1) rfl
      (zip_refl (fun (x y : String × Term) => Blind x.2 y.2) fs (fun f hf => obsFree_of_observes f.2 (hfs f hf)))
  | .record fs, h => by
    have hfs := any_fields_false (by simpa [observes] using h)
    exact .record rfl (zip_refl (fun (x y : String × Term) => Blind x.2 y.2) fs (fun f hf => obsFree_of_observes f.2 (hfs f hf)))
  | .ifZero a b c, h => by
    simp only [observes, Bool.or_eq_false_iff] at h
    exact .ifZero (obsFree_of_observes a h.1.1) (obsFree_of_observes b h.1.2) (obsFree_of_observes c h.2)
  | .ifBool a b c, h => by
    simp only [observes, Bool.or_eq_false_iff] at h
    exact .ifBool (obsFree_of_observes a h.1.1) (obsFree_of_observes b h.1.2) (obsFree_of_observes c h.2)
  | .case a arms, h => by
    simp only [observes, Bool.or_eq_false_iff] at h
    have harms := any_fields_false h.2
    exact .case (obsFree_of_observes a h.1) rfl
      (zip_refl (fun (x y : String × Term) => Blind x.2 y.2) arms (fun f hf => obsFree_of_observes f.2 (harms f hf)))
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have hlist := List.sizeOf_lt_of_mem hf
       have hpair : sizeOf f.snd < sizeOf f := by cases f; simp +arith
       omega)

theorem census_le_b {t : Term} (h : census t ≤ .b) : ObsFree t := by
  unfold census at h
  cases hobs : observes t
  · exact obsFree_of_observes t hobs
  · rw [hobs] at h; exact absurd h (by decide)

theorem census_le_r (t : Term) : census t ≤ .r := by
  unfold census; split <;> decide

/-! ## §3. The three equivalences and the ladder -/

/-- Which (closing substitution, context) pairs an observer of level `k` may use. -/
def Admits : Level → (Nat → Term) → Term → Prop
  | .b, ρ, C => (∀ n, ObsFree (ρ n)) ∧ ObsFree C
  | .r, _, _ => True
  | .q, _, _ => True

/-- Indistinguishable by every Core4 observer of level `k`. -/
def Observed (k : Level) (t t' : Term) : Prop :=
  ∀ (ρ : Nat → Term) (C : Term), Admits k ρ C →
    SameRuns (instantiate C (t.substitute ρ)) (instantiate C (t'.substitute ρ))

/-- `≈q`: α-equality, what the kernel's `quote` sees. -/
def QEquiv (t t' : Term) : Prop := encode t = encode t'

/-- The ladder's equivalences: `≈[q]`, `≈[r]`, `≈[b]`. -/
def LEquiv : Level → Term → Term → Prop
  | .q => QEquiv
  | .r => Observed .r
  | .b => Observed .b

@[inherit_doc] notation:50 t " ≈[" k "] " t' => LEquiv k t t'

theorem qequiv_iff {t t' : Term} : QEquiv t t' ↔ t = t' :=
  ⟨encode_injective, fun h => h ▸ rfl⟩

/-- `Equiv/Behaviour`'s `≈b` quantifies over every context, `metadata` included: it is `≈[r]`. -/
theorem observed_r_iff {t t' : Term} : (t ≈[.r] t') ↔ t ≈b t' :=
  ⟨fun h ρ C => h ρ C trivial, fun h ρ C _ => h ρ C⟩

theorem Observed.refl (k : Level) (t : Term) : Observed k t t := fun _ _ _ =>
  ⟨fun _ => Iff.rfl, Iff.rfl⟩

theorem Observed.symm {k : Level} {t t' : Term} (h : Observed k t t') : Observed k t' t :=
  fun ρ C a => ⟨fun o => ((h ρ C a).halts o).symm, (h ρ C a).converges.symm⟩

theorem Observed.trans {k : Level} {t t' t'' : Term} (h : Observed k t t') (h' : Observed k t' t'') :
    Observed k t t'' := fun ρ C a =>
  ⟨fun o => ((h ρ C a).halts o).trans ((h' ρ C a).halts o), (h ρ C a).converges.trans (h' ρ C a).converges⟩

/-- A finer observer class gives a finer equivalence. -/
theorem observed_mono {k k' : Level} (hk : k ≤ k') {t t' : Term} (h : Observed k' t t') :
    Observed k t t' := by
  intro ρ C a
  apply h ρ C
  cases k' with
  | b => cases k with
    | b => exact a
    | r => exact absurd hk (by decide)
    | q => exact absurd hk (by decide)
  | r => trivial
  | q => trivial

/-- **T3 `observer_ladder`.** `≈q ⊆ ≈r ⊆ ≈b`. -/
theorem observer_ladder {t t' : Term} :
    ((t ≈[.q] t') → t ≈[.r] t') ∧ ((t ≈[.r] t') → t ≈[.b] t') := by
  refine ⟨fun h => ?_, fun h => observed_mono (k' := .r) (by decide) h⟩
  have := qequiv_iff.1 h
  subst this
  exact Observed.refl .r t

/-- Blind terms are `≈b`: no observer of census `b` reads the metadata they differ in. -/
theorem blind_observed {t t' : Term} (h : Blind t t') : t ≈[.b] t' := fun _ _ a =>
  sameRuns_of_blind (blind_instantiate a.2 (blind_substitute h a.1))

/-! ## §4. Observers and the rewriter's licence -/

/-- An observer: a Core4 context (its hole is variable 0), or the kernel's `quote` handing the
quotation of what is plugged to a Core4 context, as `Data`. -/
inductive Observer where
  | run (C : Term)
  | quote (C : Term)

def Observer.plug : Observer → Term → Term
  | .run C, t => instantiate C t
  | .quote C, t => instantiate C (Obend.Core.Data.Data.term (Obend.Core.Code.quote t))

/-- A `quote` position has census `q`; a Core4 context has its own census. -/
def Observer.census : Observer → Level
  | .run C => Obend.Equiv.census C
  | .quote _ => .q

/-- Plug `D` into the hole of `C'`, keeping every other variable of `C'` where it was. -/
def plugContext (C' D : Term) : Term :=
  C'.substitute (fun i => match i with | 0 => D | n + 1 => .bound (n + 1))

theorem instantiate_plugContext (C' D x : Term) :
    instantiate (plugContext C' D) x = instantiate C' (instantiate D x) := by
  simp only [plugContext, instantiate_eq, substitute_comp]
  congr 1; funext i
  cases i with
  | zero => rfl
  | succ n => simp [single, Term.substitute]

theorem obsFree_plugContext {C' D : Term} (hC : ObsFree C') (hD : ObsFree D) :
    ObsFree (plugContext C' D) :=
  blind_substitute hC (fun i => match i with | 0 => hD | n + 1 => .bound (n + 1))

/-- `≈k` is closed under Core4 contexts the level admits. -/
theorem observed_plug {k : Level} {a b : Term} (h : Observed k a b) (C : Term)
    (hC : k = .b → ObsFree C) : Observed k (instantiate C a) (instantiate C b) := by
  intro ρ C' adm
  rw [instantiate_substitute, instantiate_substitute, ← instantiate_plugContext,
    ← instantiate_plugContext]
  apply h ρ
  cases k with
  | b =>
    exact ⟨adm.1, obsFree_plugContext adm.2 (blind_substitute (hC rfl) (blind_lift adm.1))⟩
  | r => trivial
  | q => trivial

/-- **T5 `rewrite_sound_below`.** An observer whose census is at most `k` preserves `≈k`. At `q`
the premise is vacuous and the conclusion is congruence of syntax; at `r` and `b` it is closure of
`Observed` under the contexts the level admits. -/
theorem rewrite_sound_below (k : Level) {a b : Term} (h : a ≈[k] b) (O : Observer)
    (hO : O.census ≤ k) : O.plug a ≈[k] O.plug b := by
  cases k with
  | q =>
    have := qequiv_iff.1 h
    subst this
    exact qequiv_iff.2 rfl
  | r =>
    cases O with
    | run C => exact observed_plug h C (fun e => by cases e)
    | quote C => simp only [Observer.census] at hO; exact absurd hO (by decide)
  | b =>
    cases O with
    | run C => exact observed_plug h C (fun _ => census_le_b hO)
    | quote C => simp only [Observer.census] at hO; exact absurd hO (by decide)

/-! ## §5. The ladder is strict, and the licence's premise is necessary -/

theorem steps_values_unique {t v v' : Term} (s : Steps t v) (hv : Value v) (s' : Steps t v')
    (hv' : Value v') : v = v' := by
  induction s generalizing v' with
  | refl => exact (value_steps_eq hv s').symm
  | next st _ ih =>
    cases s' with
    | refl => exact absurd st (value_no_step hv')
    | next st' s'' =>
      rw [step_deterministic st st'] at ih
      exact ih hv s'' hv'

theorem evaluates_unique {t v v' : Term} (e : Evaluates t v) (e' : Evaluates t v') : v = v' :=
  steps_values_unique e.1 e.2 e'.1 e'.2

/-- Two terms that evaluate to different ground observations are not `≈b`, hence `≈` at no level. -/
theorem not_observed_b {t t' : Term} {o o' : Observation} {v v' : Term}
    (e : Evaluates t v) (ov : Observes v o) (e' : Evaluates t' v') (ov' : Observes v' o')
    (differ : o ≠ o') : ¬ (t ≈[.b] t') := by
  intro h
  have same : SameRuns t t' := by
    have := h Term.bound (.bound 0) ⟨fun n => .bound n, .bound 0⟩
    simpa [instantiate, Term.substitute, substitute_bound] using this
  obtain ⟨w, ew, ow⟩ := (same.halts o).1 ⟨v, e, ov⟩
  have := evaluates_unique ew e'
  subst this
  cases ow <;> cases ov' <;> simp_all

/-- A Bool read-back of a run, for `decide`. -/
def natOf : Option Term → Option Nat
  | some (.nat n) => some n
  | _ => none

def boolOf : Option Term → Option Bool
  | some (.boolean b) => some b
  | _ => none

theorem natOf_eval {t : Term} {n : Nat} (fuel : Nat) (h : natOf (Obend.Law.run fuel t) = some n) :
    Evaluates t (.nat n) := by
  unfold natOf at h
  split at h
  · cases h; exact Obend.Law.run_sound fuel (by assumption)
  · cases h

theorem boolOf_eval {t : Term} {b : Bool} (fuel : Nat) (h : boolOf (Obend.Law.run fuel t) = some b) :
    Evaluates t (.boolean b) := by
  unfold boolOf at h
  split at h
  · cases h; exact Obend.Law.run_sound fuel (by assumption)
  · cases h

/-! ### Barendregt's pair: `≈r` and not `≈q`, and a `quote` observer separates them -/

/-- `(λx. x)(λx. x)`. -/
def selfApplied : Term := .app (.lam (.bound 0)) (.lam (.bound 0))
/-- `λx. x`. -/
def identityTerm : Term := .lam (.bound 0)

/-- A program that reads the head of a quotation: `var ↦ 0`, `bind ↦ 1`, `node ↦ 2`. -/
def headReader : Term := .case (.bound 0) [("var", .nat 0), ("bind", .nat 1), ("node", .nat 2)]

theorem headReader_selfApplied : Evaluates ((Observer.quote headReader).plug selfApplied) (.nat 2) :=
  natOf_eval 10 (by decide +kernel)

theorem headReader_identity : Evaluates ((Observer.quote headReader).plug identityTerm) (.nat 1) :=
  natOf_eval 10 (by decide +kernel)

/-- **T4 `quote_not_congruent`.** Barendregt's pair is `≈r` (one β step) and not `≈q`; and the
`quote` observer `headReader` separates their pluggings even at `≈b`. So no equivalence coarser
than `≈q` is preserved by `quote`: there is no congruence under the box. -/
theorem quote_not_congruent :
    (selfApplied ≈[.r] identityTerm) ∧ ¬ (selfApplied ≈[.q] identityTerm) ∧
      (Observer.quote headReader).census = .q ∧
      ¬ ((Observer.quote headReader).plug selfApplied ≈[.b] (Observer.quote headReader).plug identityTerm) := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · apply observed_r_iff.2
    apply bequiv_of_steps
    have := Step.beta (.bound 0) (.lam (.bound 0))
    simp only [instantiate, Term.substitute] at this
    exact steps_one this
  · intro h
    have := qequiv_iff.1 h
    cases this
  · exact not_observed_b headReader_selfApplied (.natural 2) headReader_identity (.natural 1)
      (by decide)

/-! ### REFLECTION's probes R01/R02: `compose` is associative for `≈b` and not for `≈r`

Ported from minidregg `tests/objective-bend-source/ltuo/AssociationProvenance.obend` (read-only):
three counter specifications `A`, `B`, `C`; `compose(a, b)` is
`specification(SpecMeta.composed{inherited: metadata(a), wrapping: metadata(b)}, mix a b)`;
`leftNested` asks whether the inherited provenance of `compose(compose(A, B), C)` is composed. -/

/-- `SpecMeta.declared{name, interface, claims: SpecClaims.none{}}`. -/
def declared (name : String) : Term :=
  .inject "declared" (.record [("name", .label name), ("interface", .label "Counter"),
    ("claims", .inject "none" (.record []))])

/-- `λself. λsuper. super with n = super.n op k`. -/
def counterExtension (op : Primitive) (k : Nat) : Term :=
  .lam (.lam (.extend (.bound 0) [("n", .binary op (.get (.bound 0) "n") (.nat k))]))

def specA : Term := .specification (declared "AssociationProvenance.A") (counterExtension .add 1)
def specB : Term := .specification (declared "AssociationProvenance.B") (counterExtension .multiply 2)
def specC : Term := .specification (declared "AssociationProvenance.C") (counterExtension .add 3)

/-- `compose(a, b)`, as the elaborator lowers it for two specification operands. -/
def compose (a b : Term) : Term :=
  .specification (.inject "composed" (.record [("inherited", .metadata a), ("wrapping", .metadata b)]))
    (.mix a b)

/-- `isComposed(inheritedOf(metadata(·)))`: the probes' observer, a context with its hole at 0. -/
def provenanceProbe : Term :=
  .case (.case (.metadata (.bound 0))
      [("declared", .metadata (.bound 1)), ("composed", .get (.bound 0) "inherited"),
        ("extension", .metadata (.bound 1))])
    [("declared", .boolean false), ("composed", .boolean true), ("extension", .boolean false)]

def leftNested : Term := compose (compose specA specB) specC
def rightNested : Term := compose specA (compose specB specC)

/-- **R01**: `leftNested()` is `true`. -/
theorem probe_R01 : Evaluates ((Observer.run provenanceProbe).plug leftNested) (.boolean true) :=
  boolOf_eval 40 (by decide +kernel)

/-- **R02**: `rightNested()` is `false`. -/
theorem probe_R02 : Evaluates ((Observer.run provenanceProbe).plug rightNested) (.boolean false) :=
  boolOf_eval 40 (by decide +kernel)

theorem provenanceProbe_census : (Observer.run provenanceProbe).census = .r := by
  decide +kernel

/-- Both associations are ahead of `λself. λsuper. c self (b self (a self super))`, through the
inner specification's application. -/
theorem compose_left_ahead (a b c : Term) :
    Ahead (.mix (compose a b) c) (mixAssocBody a b c) := by
  refine .run (steps_one (.mix _ _)) ?_
  simp only [mixBody, mixAssocBody, compose, Term.rename]
  refine .lam (.lam (.app (.refl _) ?_))
  exact Ahead.ofStepsRefl (.next (.application _ (.applySpecification _ _ _)) (mix_apply _ _ _ _))

theorem compose_right_ahead (a b c : Term) :
    Ahead (.mix a (compose b c)) (mixAssocBody a b c) := by
  refine .run (steps_one (.mix _ _)) ?_
  simp only [mixBody, mixAssocBody, compose, Term.rename]
  exact .lam (.lam (Ahead.ofStepsRefl
    (.next (.application _ (.applySpecification _ _ _)) (mix_apply _ _ _ _))))

theorem obsFree_mixAssocBody {a b c : Term} (ha : ObsFree a) (hb : ObsFree b) (hc : ObsFree c) :
    ObsFree (mixAssocBody a b c) :=
  .lam (.lam (.app (.app (blind_rename hc _) (.bound 1))
    (.app (.app (blind_rename hb _) (.bound 1)) (.app (.app (blind_rename ha _) (.bound 1)) (.bound 0)))))

/-- **`compose` is associative up to `≈b`**, for any observer-free operands: the two associations
run alike and differ only in their metadata, which no census-`b` observer reads. -/
theorem compose_assoc_b {a b c : Term} (ha : ObsFree a) (hb : ObsFree b) (hc : ObsFree c) :
    compose (compose a b) c ≈[.b] compose a (compose b c) := by
  have left : compose (compose a b) c ≈[.b]
      .specification (.inject "composed" (.record [("inherited", .metadata (compose a b)),
        ("wrapping", .metadata c)])) (mixAssocBody a b c) :=
    observed_mono (k' := .r) (by decide) (observed_r_iff.2 (bequiv_of_ahead
      (.specification (Ahead.refl _) (compose_left_ahead a b c))))
  have right : compose a (compose b c) ≈[.b]
      .specification (.inject "composed" (.record [("inherited", .metadata a),
        ("wrapping", .metadata (compose b c))])) (mixAssocBody a b c) :=
    observed_mono (k' := .r) (by decide) (observed_r_iff.2 (bequiv_of_ahead
      (.specification (Ahead.refl _) (compose_right_ahead a b c))))
  exact Observed.trans left (Observed.trans
    (blind_observed (.specification _ _ (obsFree_mixAssocBody ha hb hc))) (Observed.symm right))

theorem specs_obsFree : ObsFree specA ∧ ObsFree specB ∧ ObsFree specC :=
  ⟨obsFree_of_observes _ (by decide +kernel), obsFree_of_observes _ (by decide +kernel),
    obsFree_of_observes _ (by decide +kernel)⟩

theorem compose_assoc_probe : leftNested ≈[.b] rightNested :=
  compose_assoc_b specs_obsFree.1 specs_obsFree.2.1 specs_obsFree.2.2

/-- **`compose` is not associative up to `≈r`**: the probe `provenanceProbe` (R01/R02) tells the
two associations apart. -/
theorem compose_not_assoc_r : ¬ (leftNested ≈[.r] rightNested) := by
  intro h
  have := rewrite_sound_below .r h (.run provenanceProbe) (census_le_r _)
  exact not_observed_b probe_R01 (.boolean true) probe_R02 (.boolean false) (by decide)
    (observer_ladder.2 this)

/-- **The `k = b` tooth of T5**: without its census premise the licence is false. A `metadata`
frame on the hole (census `r`) separates two `≈b` specifications. -/
theorem metadata_frame_breaks_b :
    (leftNested ≈[.b] rightNested) ∧ (Observer.run provenanceProbe).census = .r ∧
      ¬ ((Observer.run provenanceProbe).plug leftNested ≈[.b]
        (Observer.run provenanceProbe).plug rightNested) :=
  ⟨compose_assoc_probe, provenanceProbe_census,
    not_observed_b probe_R01 (.boolean true) probe_R02 (.boolean false) (by decide)⟩

/-- **The `k = r` tooth of T5**: a `quote` observer (census `q`) does not preserve `≈r`. -/
theorem quote_breaks_r :
    (selfApplied ≈[.r] identityTerm) ∧ (Observer.quote headReader).census = .q ∧
      ¬ ((Observer.quote headReader).plug selfApplied ≈[.r]
        (Observer.quote headReader).plug identityTerm) :=
  ⟨quote_not_congruent.1, rfl, fun h => quote_not_congruent.2.2.2 (observer_ladder.2 h)⟩

/-- The raw `mix` stays associative even for `≈r`: it carries no metadata (`mix_assoc`). The
failure above is `compose`'s, through the provenance it records. And `≈q` refuses both. -/
theorem mix_assoc_r (a b c : Term) : .mix (.mix a b) c ≈[.r] .mix a (.mix b c) :=
  observed_r_iff.2 (mix_assoc a b c)

theorem mix_not_assoc_q (a b c : Term) : ¬ (.mix (.mix a b) c ≈[.q] .mix a (.mix b c)) := by
  intro h
  have := qequiv_iff.1 h
  simp only [Term.mix.injEq] at this
  have hsize := congrArg sizeOf this.1
  simp at hsize
  omega

end Obend.Equiv
end
