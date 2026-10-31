module
/- Clairvoyant call-by-value for Core4 (`review/EQUIV-PLAN-20261031.md` §2, definition 2;
Hackett–Hutton 2019, Fig. 3). A big-step relation `Run .eval t v k`, "`t` evaluates to `v` at
cost `k`", in which every binding site either evaluates its term first (Let′) or discards it
(Skip). Call-by-need cost is the least cost over derivations (H&H Thm 4.1), so the nondeterminism
is the oracle that knows which bindings will be demanded.

Core4 has no `let`. Its binding sites are the β argument, the fields of a record or an extension,
the components of a specification or prototype, the payload of an injection (which `case` then
binds), the `self` of `fix`, and `super` inside `mixBody` (a β argument once the extension is
applied). A binding (`Run .bind`) keeps a term that is already settled (cost 0), evaluates one that
is not (Let′, cost +1) or skips it (Skip, cost 1, leaving `skipped`, a term with no derivation).

`fix s i` is H&H's recursive `let`: its body is evaluated with `self` not yet bound (the open
variable `.bound 0`, a pointer that may be passed but never entered, as Launchbury's blackholing
removes the cell under evaluation), and the value `V` that results is tied by substituting a
`knot` for `self` (Let′), or `skipped` (Skip). A knot is `fix (λself. λsuper. V) {}` with `V` a
value: entering it costs 3 (`knot_unfold`), the source-level analogue of H&H's `Var′`.

The value forms (`CValue`) are the weak-head values of `Value` whose lazy components are settled:
a record's fields, a specification's or prototype's components and an injection's payload are
values, knots, pointers or `skipped`. A value evaluates only to itself, at cost 0. -/
public import Obend.Equiv.Behaviour
@[expose] public section
namespace Obend.Equiv
open Obend.Core.Term
open Obend.Core.TermTraverse (rename_substitute substitute_comp substitute_rename rename_comp)
set_option autoImplicit false

/-! ## Settled terms and values -/

/-- What a skipped binding leaves behind: a closed term with no derivation. -/
def skipped : Term := .hole 0 []

/-- Under `λself. λsuper.`, an index of a body whose `self` is index 0. -/
def shiftSelf : Nat → Nat
  | 0 => 1
  | n + 1 => n + 2

/-- The body of `fix s i`, evaluated with `self` open as index 0. -/
def selfBody (s i : Term) : Term := .app (.app (s.rename .succ) (.bound 0)) (i.rename .succ)

/-- The knot tying the value `V` of a `fix` body (`self` at index 0) to itself. -/
def knot (V : Term) : Term := .fix (.lam (.lam (V.rename shiftSelf))) (.record [])

/-- `Ready true t`: `t` is a value of the clairvoyant semantics. `Ready false t`: `t` is settled,
a value, a knot, a pointer to a cell under evaluation, or `skipped`. -/
inductive Ready : Bool → Term → Prop where
  | lam (b : Term) : Ready true (.lam b)
  | nat (n : Nat) : Ready true (.nat n)
  | boolean (b : Bool) : Ready true (.boolean b)
  | label (l : String) : Ready true (.label l)
  | record {fs : List (String × Term)} : (∀ f ∈ fs, Ready false f.2) → Ready true (.record fs)
  | specification {m e : Term} : Ready false m → Ready false e → Ready true (.specification m e)
  | prototype {s g : Term} : Ready false s → Ready false g → Ready true (.prototype s g)
  | inject (l : String) {p : Term} : Ready false p → Ready true (.inject l p)
  | value {t : Term} : Ready true t → Ready false t
  | skipped : Ready false skipped
  | bound (i : Nat) : Ready false (.bound i)
  | knot {W i : Term} : Ready true W → Ready false i → Ready false (.fix (.lam (.lam W)) i)

abbrev CValue (t : Term) : Prop := Ready true t
abbrev Settled (t : Term) : Prop := Ready false t

theorem Ready.settled {b : Bool} {t : Term} (h : Ready b t) : Settled t := by
  cases b
  · exact h
  · exact .value h

theorem rename_skipped (f : Nat → Nat) : skipped.rename f = skipped := by
  simp [skipped, Term.rename]

theorem substitute_skipped (σ : Nat → Term) : skipped.substitute σ = skipped := by
  simp [skipped, Term.substitute]

theorem Ready.rename {b : Bool} {t : Term} (h : Ready b t) : ∀ f : Nat → Nat, Ready b (t.rename f) := by
  induction h with
  | lam b => intro f; simp only [Term.rename]; exact .lam _
  | nat n => intro f; simp only [Term.rename]; exact .nat n
  | boolean b => intro f; simp only [Term.rename]; exact .boolean b
  | label l => intro f; simp only [Term.rename]; exact .label l
  | record _ ih =>
    intro f; simp only [Term.rename]
    refine .record ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ih y hy f
  | specification _ _ i1 i2 => intro f; simp only [Term.rename]; exact .specification (i1 f) (i2 f)
  | prototype _ _ i1 i2 => intro f; simp only [Term.rename]; exact .prototype (i1 f) (i2 f)
  | inject l _ ih => intro f; simp only [Term.rename]; exact .inject l (ih f)
  | value _ ih => intro f; exact .value (ih f)
  | skipped => intro f; rw [rename_skipped]; exact .skipped
  | bound i => intro f; simp only [Term.rename]; exact .bound _
  | knot _ _ i1 i2 => intro f; simp only [Term.rename]; exact .knot (i1 _) (i2 f)

theorem settled_lift {σ : Nat → Term} (h : ∀ n, Settled (σ n)) : ∀ n, Settled (liftSubstitution σ n)
  | 0 => .bound 0
  | n + 1 => (h n).rename _

theorem Ready.substitute {b : Bool} {t : Term} (h : Ready b t) :
    ∀ {σ : Nat → Term}, (∀ n, Settled (σ n)) → Ready b (t.substitute σ) := by
  induction h with
  | lam b => intro σ _; simp only [Term.substitute]; exact .lam _
  | nat n => intro σ _; simp only [Term.substitute]; exact .nat n
  | boolean b => intro σ _; simp only [Term.substitute]; exact .boolean b
  | label l => intro σ _; simp only [Term.substitute]; exact .label l
  | record _ ih =>
    intro σ hσ; simp only [Term.substitute]
    refine .record ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ih y hy hσ
  | specification _ _ i1 i2 => intro σ hσ; simp only [Term.substitute]; exact .specification (i1 hσ) (i2 hσ)
  | prototype _ _ i1 i2 => intro σ hσ; simp only [Term.substitute]; exact .prototype (i1 hσ) (i2 hσ)
  | inject l _ ih => intro σ hσ; simp only [Term.substitute]; exact .inject l (ih hσ)
  | value _ ih => intro σ hσ; exact .value (ih hσ)
  | skipped => intro σ _; rw [substitute_skipped]; exact .skipped
  | bound i => intro σ hσ; simp only [Term.substitute]; exact hσ i
  | knot _ _ i1 i2 =>
    intro σ hσ; simp only [Term.substitute]
    exact .knot (i1 (settled_lift (settled_lift hσ))) (i2 hσ)

theorem settled_single {x : Term} (h : Settled x) : ∀ n, Settled (single x n)
  | 0 => h
  | n + 1 => .bound n

theorem settled_bound : ∀ n, Settled (Term.bound n) := fun n => .bound n

theorem knot_settled {V : Term} (h : CValue V) : Settled (knot V) :=
  .knot (h.rename _) (.value (.record (by simp)))

theorem skipped_not_value : ¬ CValue skipped := by intro h; cases h

theorem app_not_ready {b : Bool} {f a : Term} : ¬ Ready b (.app f a) := by
  intro h; cases h with | value h => cases h

theorem mix_not_ready {b : Bool} {l u : Term} : ¬ Ready b (.mix l u) := by
  intro h; cases h with | value h => cases h

/-! ## The clairvoyant relation -/

/-- What a derivation produces: an evaluation, one binding, or the bindings of a field list. -/
inductive Mode where
  | eval | bind | fields
  deriving DecidableEq

/-- `Run .eval t v k`: `t` evaluates to the value `v` at cost `k`. `Run .bind a x k`: the binding
of `a` leaves `x` at cost `k`. `Run .fields (.record fs) (.record fs') k`: binding each field. -/
inductive Run : Mode → Term → Term → Nat → Prop where
  | value {v : Term} : CValue v → Run .eval v v 0
  | apply {f a b x v : Term} {k1 k2 k3 : Nat} :
      Run .eval f (.lam b) k1 → Run .bind a x k2 → Run .eval (instantiate b x) v k3 →
      Run .eval (.app f a) v (k1 + k2 + k3 + 1)
  | applySpec {f a m e v : Term} {k1 k2 : Nat} :
      Run .eval f (.specification m e) k1 → Run .eval (.app e a) v k2 → Run .eval (.app f a) v (k1 + k2 + 1)
  | mix (l u : Term) : Run .eval (.mix l u) (mixBody l u) 1
  /-- Let′ at `self`: the value is tied to itself through a knot. -/
  | fixLet {s i V : Term} {k : Nat} :
      Run .eval (selfBody s i) V k → Run .eval (.fix s i) (V.substitute (single (knot V))) (k + 1)
  /-- Skip at `self`. -/
  | fixSkip {s i V : Term} {k : Nat} :
      Run .eval (selfBody s i) V k → Run .eval (.fix s i) (V.substitute (single skipped)) (k + 1)
  | specification {m e m' e' : Term} {k1 k2 : Nat} : ¬ CValue (.specification m e) →
      Run .bind m m' k1 → Run .bind e e' k2 → Run .eval (.specification m e) (.specification m' e') (k1 + k2 + 1)
  | prototype {s g s' g' : Term} {k1 k2 : Nat} : ¬ CValue (.prototype s g) →
      Run .bind s s' k1 → Run .bind g g' k2 → Run .eval (.prototype s g) (.prototype s' g') (k1 + k2 + 1)
  | reflect {p s g v : Term} {k1 k2 : Nat} :
      Run .eval p (.prototype s g) k1 → Run .eval s v k2 → Run .eval (.reflect p) v (k1 + k2 + 1)
  | metadata {p m e v : Term} {k1 k2 : Nat} :
      Run .eval p (.specification m e) k1 → Run .eval m v k2 → Run .eval (.metadata p) v (k1 + k2 + 1)
  | project {p s g v : Term} {k1 k2 : Nat} :
      Run .eval p (.prototype s g) k1 → Run .eval g v k2 → Run .eval (.project p) v (k1 + k2 + 1)
  | record {fs fs' : List (String × Term)} {k : Nat} : ¬ CValue (.record fs) →
      Run .fields (.record fs) (.record fs') k → Run .eval (.record fs) (.record fs') (k + 1)
  | get {g x v : Term} {fs : List (String × Term)} {name : String} {k1 k2 : Nat} :
      Run .eval g (.record fs) k1 → fs.find? (fun f => f.1 == name) = some (name, x) →
      Run .eval x v k2 → Run .eval (.get g name) v (k1 + k2 + 1)
  | extend {i : Term} {inh fs fs' : List (String × Term)} {k1 k2 : Nat} :
      Run .eval i (.record inh) k1 → Run .fields (.record fs) (.record fs') k2 →
      Run .eval (.extend i fs) (.record (extendFields inh fs')) (k1 + k2 + 1)
  | binary {op : Primitive} {l r lv rv res : Term} {k1 k2 : Nat} :
      Run .eval l lv k1 → Run .eval r rv k2 → primitiveResult op lv rv = some res →
      Run .eval (.binary op l r) res (k1 + k2 + 1)
  | zero {c z s v : Term} {k1 k2 : Nat} :
      Run .eval c (.nat 0) k1 → Run .eval z v k2 → Run .eval (.ifZero c z s) v (k1 + k2 + 1)
  | succ {c z s v : Term} {n k1 k2 : Nat} :
      Run .eval c (.nat (n + 1)) k1 → Run .eval (instantiate s (.nat n)) v k2 →
      Run .eval (.ifZero c z s) v (k1 + k2 + 1)
  | inject {l : String} {p p' : Term} {k : Nat} : ¬ CValue (.inject l p) →
      Run .bind p p' k → Run .eval (.inject l p) (.inject l p') (k + 1)
  | case {sc p body v : Term} {l : String} {arms : List (String × Term)} {k1 k2 : Nat} :
      Run .eval sc (.inject l p) k1 → arms.find? (fun a => a.1 == l) = some (l, body) →
      Run .eval (instantiate body p) v k2 → Run .eval (.case sc arms) v (k1 + k2 + 1)
  | ifTrue {c x y v : Term} {k1 k2 : Nat} :
      Run .eval c (.boolean true) k1 → Run .eval x v k2 → Run .eval (.ifBool c x y) v (k1 + k2 + 1)
  | ifFalse {c x y v : Term} {k1 k2 : Nat} :
      Run .eval c (.boolean false) k1 → Run .eval y v k2 → Run .eval (.ifBool c x y) v (k1 + k2 + 1)
  | done {x v : Term} {k : Nat} : Run .eval x v k → Run .eval (.done x) v (k + 1)
  /-- A settled term is bound as it is. -/
  | keep {a : Term} : Settled a → Run .bind a a 0
  /-- Skip: the binding is discarded. -/
  | skip (a : Term) : Run .bind a skipped 1
  /-- Let′: a bound term that is not settled is evaluated first. A knot is kept, and entered
  only where it is demanded. -/
  | eval {a v : Term} {k : Nat} : ¬ Settled a → Run .eval a v k → Run .bind a v (k + 1)
  | nil : Run .fields (.record []) (.record []) 0
  | cons {n : String} {t t' : Term} {fs fs' : List (String × Term)} {k1 k2 : Nat} :
      Run .bind t t' k1 → Run .fields (.record fs) (.record fs') k2 →
      Run .fields (.record ((n, t) :: fs)) (.record ((n, t') :: fs')) (k1 + k2 + 1)

/-- `t` evaluates to `v` at clairvoyant cost `k`. -/
abbrev CV (t v : Term) (k : Nat) : Prop := Run .eval t v k

/-- The clairvoyant cost of `t` is at most `k`: some derivation costs `k`. Call-by-need cost is the
least such `k` (H&H Thm 4.1). -/
def CostAtMost (t : Term) (k : Nat) : Prop := ∃ v k', CV t v k' ∧ k' ≤ k

/-! ## What a derivation produces -/

/-- The shape of a result in each mode. -/
def Produced : Mode → Term → Prop
  | .eval, v => CValue v
  | .bind, x => Settled x
  | .fields, w => ∃ fs, w = .record fs ∧ ∀ f ∈ fs, Settled f.2

theorem extendFields_settled {inh fs : List (String × Term)} (hi : ∀ f ∈ inh, Settled f.2)
    (hf : ∀ f ∈ fs, Settled f.2) : ∀ f ∈ extendFields inh fs, Settled f.2 := by
  intro f hm
  simp only [extendFields, List.mem_append, List.mem_filter] at hm
  rcases hm with h | ⟨h, _⟩
  · exact hf f h
  · exact hi f h

theorem ready_literal {t : Term} (h : Literal t) : CValue t := by
  cases h <;> constructor

theorem record_value_fields {fs : List (String × Term)} (h : CValue (.record fs)) : ∀ f ∈ fs, Settled f.2 := by
  cases h with | record h => exact h

theorem spec_value_parts {m e : Term} (h : CValue (.specification m e)) : Settled m ∧ Settled e := by
  cases h with | specification hm he => exact ⟨hm, he⟩

theorem proto_value_parts {s g : Term} (h : CValue (.prototype s g)) : Settled s ∧ Settled g := by
  cases h with | prototype hs hg => exact ⟨hs, hg⟩

theorem inject_value_payload {l : String} {p : Term} (h : CValue (.inject l p)) : Settled p := by
  cases h with | inject _ hp => exact hp

theorem run_produced {mode : Mode} {t v : Term} {k : Nat} (h : Run mode t v k) : Produced mode v := by
  induction h with
  | value hv => exact hv
  | apply _ _ _ _ _ ih => exact ih
  | applySpec _ _ _ ih => exact ih
  | mix l u => exact .lam _
  | fixLet _ ih =>
    exact Ready.substitute ih (settled_single (knot_settled ih))
  | fixSkip _ ih => exact Ready.substitute ih (settled_single .skipped)
  | specification _ _ _ i1 i2 => exact .specification i1 i2
  | prototype _ _ _ i1 i2 => exact .prototype i1 i2
  | reflect _ _ _ ih => exact ih
  | metadata _ _ _ ih => exact ih
  | project _ _ _ ih => exact ih
  | record _ _ ih =>
    obtain ⟨fs, eq, h⟩ := ih
    cases eq; exact .record h
  | get _ _ _ _ ih => exact ih
  | extend _ _ i1 i2 =>
    obtain ⟨fs, eq, h⟩ := i2
    cases eq
    exact .record (extendFields_settled (record_value_fields i1) h)
  | binary _ _ hit _ _ =>
    exact ready_literal (primitiveResult_literal hit).2.2
  | zero _ _ _ ih => exact ih
  | succ _ _ _ ih => exact ih
  | inject _ _ ih => exact .inject _ ih
  | case _ _ _ _ ih => exact ih
  | ifTrue _ _ _ ih => exact ih
  | ifFalse _ _ _ ih => exact ih
  | done _ ih => exact ih
  | keep h => exact h
  | skip a => exact .skipped
  | eval _ _ ih => exact ih.settled
  | nil => exact ⟨[], rfl, by simp⟩
  | cons _ _ i1 i2 =>
    obtain ⟨fs, eq, h⟩ := i2
    cases eq
    refine ⟨_, rfl, ?_⟩
    intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact i1
    · exact h f hf

theorem cv_value {t v : Term} {k : Nat} (h : CV t v k) : CValue v := run_produced h
theorem bind_settled {a x : Term} {k : Nat} (h : Run .bind a x k) : Settled x := run_produced h

/-! ## Inversions -/

/-- A value evaluates only to itself, at no cost. -/
theorem cv_of_value {t v : Term} {k : Nat} (hv : CValue t) (h : CV t v k) : v = t ∧ k = 0 := by
  cases h with
  | value _ => exact ⟨rfl, rfl⟩
  | specification hn => exact absurd hv hn
  | prototype hn => exact absurd hv hn
  | record hn => exact absurd hv hn
  | inject hn => exact absurd hv hn
  | apply => cases hv
  | applySpec => cases hv
  | mix => cases hv
  | fixLet => cases hv
  | fixSkip => cases hv
  | reflect => cases hv
  | metadata => cases hv
  | project => cases hv
  | get => cases hv
  | extend => cases hv
  | binary => cases hv
  | zero => cases hv
  | succ => cases hv
  | case => cases hv
  | ifTrue => cases hv
  | ifFalse => cases hv
  | done => cases hv

theorem cv_bound_false {i : Nat} {v : Term} {k : Nat} : ¬ CV (.bound i) v k := by
  intro h; cases h with | value h => cases h

theorem cv_skipped_false {v : Term} {k : Nat} : ¬ CV skipped v k := by
  intro h; cases h with | value h => cases h

theorem cv_lam {b v : Term} {k : Nat} (h : CV (.lam b) v k) : v = .lam b ∧ k = 0 :=
  cv_of_value (.lam b) h

theorem cv_mix {l u v : Term} {k : Nat} (h : CV (.mix l u) v k) : v = mixBody l u ∧ k = 1 := by
  cases h with
  | mix => exact ⟨rfl, rfl⟩
  | value h => cases h

/-- Binding a settled term keeps it or skips it. -/
theorem bind_of_settled {a x : Term} {k : Nat} (ha : Settled a) (h : Run .bind a x k) :
    (x = a ∧ k = 0) ∨ (x = skipped ∧ k = 1) := by
  cases h with
  | keep _ => exact .inl ⟨rfl, rfl⟩
  | skip => exact .inr ⟨rfl, rfl⟩
  | eval hn _ => exact absurd ha hn

/-- Binding a term that is not settled evaluates it or skips it. -/
theorem bind_of_unsettled {a x : Term} {k : Nat} (ha : ¬ Settled a) (h : Run .bind a x k) :
    (x = skipped ∧ k = 1) ∨ (∃ j, CV a x j ∧ k = j + 1) := by
  cases h with
  | keep hs => exact absurd hs ha
  | skip => exact .inl ⟨rfl, rfl⟩
  | eval _ e => exact .inr ⟨_, e, rfl⟩

/-- The result of a binding is bound as it is, and costs nothing more. -/
theorem bind_value_keep {a x : Term} {k : Nat} (h : Run .bind a x k) : Run .bind x x 0 :=
  .keep (bind_settled h)

/-! ## Hoisting a binding out of an application

When an argument is bound does not change its cost (H&H §3: "a term will take as long to evaluate
today as it will tomorrow"). Each lemma moves the binding of an argument out of the derivation of an
application and back. -/

theorem hoist_arg {F X v : Term} {k : Nat} (h : CV (.app F X) v k) :
    ∃ x kx k1, Run .bind X x kx ∧ CV (.app F x) v k1 ∧ k = kx + k1 := by
  change Run Mode.eval _ _ _ at h
  generalize e : Term.app F X = t at h
  generalize em : Mode.eval = m at h
  induction h generalizing F with
  | apply hf hb hbody _ _ _ =>
    cases e
    exact ⟨_, _, _, hb, .apply hf (bind_value_keep hb) hbody, by omega⟩
  | applySpec hf _ _ ih =>
    cases e
    obtain ⟨x, kx, k1, hb, run, eq⟩ := ih rfl rfl
    exact ⟨x, kx, _, hb, .applySpec hf run, by omega⟩
  | value hv => cases e; exact absurd hv app_not_ready
  | _ => first | (cases em; done) | (cases e; done)

theorem hoist_fun {F S U v : Term} {k : Nat} (h : CV (.app (.app F S) U) v k) :
    ∃ x kx k1, Run .bind S x kx ∧ CV (.app (.app F x) U) v k1 ∧ k = kx + k1 := by
  cases h with
  | apply hf hb hbody =>
    obtain ⟨x, kx, k1, hs, run, eq⟩ := hoist_arg hf
    exact ⟨x, kx, _, hs, .apply run hb hbody, by omega⟩
  | applySpec hf hrest =>
    obtain ⟨x, kx, k1, hs, run, eq⟩ := hoist_arg hf
    exact ⟨x, kx, _, hs, .applySpec run hrest, by omega⟩
  | value hv => exact absurd hv app_not_ready

/-- A binding moved back into an application, where the application binds its result (or skips
it): the cost is at most the two costs together. -/
theorem unhoist_arg {F X x v : Term} {kx k1 : Nat} (hb : Run .bind X x kx) (h : CV (.app F x) v k1) :
    ∃ k, CV (.app F X) v k ∧ k ≤ kx + k1 := by
  change Run Mode.eval _ _ _ at h
  generalize e : Term.app F x = t at h
  generalize em : Mode.eval = m at h
  induction h generalizing F with
  | @apply f a b x2 w k1 k2 k3 hf hb2 hbody _ _ _ =>
    cases e
    rcases bind_of_settled (bind_settled hb) hb2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, .apply hf hb hbody, by omega⟩
    · exact ⟨_, .apply hf (.skip _) hbody, by omega⟩
  | applySpec hf _ _ ih =>
    cases e
    obtain ⟨k, run, le⟩ := ih rfl rfl
    exact ⟨_, .applySpec hf run, by omega⟩
  | value hv => cases e; exact absurd hv app_not_ready
  | _ => first | (cases em; done) | (cases e; done)

theorem unhoist_fun {F S U x v : Term} {kx k1 : Nat} (hb : Run .bind S x kx)
    (h : CV (.app (.app F x) U) v k1) : ∃ k, CV (.app (.app F S) U) v k ∧ k ≤ kx + k1 := by
  cases h with
  | apply hf hb2 hbody =>
    obtain ⟨k, run, le⟩ := unhoist_arg hb hf
    exact ⟨_, .apply run hb2 hbody, by omega⟩
  | applySpec hf hrest =>
    obtain ⟨k, run, le⟩ := unhoist_arg hb hf
    exact ⟨_, .applySpec run hrest, by omega⟩
  | value hv => exact absurd hv app_not_ready

/-! ## `mix` applied to two settled arguments -/

theorem mixBody_inner (l u s : Term) :
    instantiate (.lam (.app (.app (u.rename (fun n => n + 2)) (.bound 1))
      (.app (.app (l.rename (fun n => n + 2)) (.bound 1)) (.bound 0)))) s =
    .lam ((Term.app (.app (u.rename (fun n => n + 2)) (.bound 1))
      (.app (.app (l.rename (fun n => n + 2)) (.bound 1)) (.bound 0))).substitute
        (liftSubstitution (single s))) := by
  rw [instantiate_eq]; simp only [Term.substitute]

theorem mixBody_outer (l u s x : Term) :
    instantiate ((Term.app (.app (u.rename (fun n => n + 2)) (.bound 1))
      (.app (.app (l.rename (fun n => n + 2)) (.bound 1)) (.bound 0))).substitute
        (liftSubstitution (single s))) x =
    .app (.app u s) (.app (.app l s) x) := by
  rw [instantiate_eq]
  simp only [Term.substitute]
  rw [shift_two_cancel, shift_two_cancel]
  simp only [liftSubstitution, single, shift_one_cancel, Term.substitute]

/-- The value of `mix l u` applied to a settled `s`. -/
def mixPartial (l u s : Term) : Term :=
  .lam ((Term.app (.app (u.rename (fun n => n + 2)) (.bound 1))
      (.app (.app (l.rename (fun n => n + 2)) (.bound 1)) (.bound 0))).substitute
        (liftSubstitution (single s)))

/-- `mix l u` applied to one argument: the extension is unfolded and `self` bound. -/
theorem cv_mix_app {l u s w : Term} {k : Nat} (h : CV (.app (.mix l u) s) w k) :
    ∃ s1 ks, Run .bind s s1 ks ∧ w = mixPartial l u s1 ∧ k = ks + 2 := by
  cases h with
  | apply hf hb hbody =>
    obtain ⟨he, rfl⟩ := cv_mix hf
    simp only [mixBody, Term.lam.injEq] at he
    subst he
    rw [mixBody_inner] at hbody
    obtain ⟨rfl, rfl⟩ := cv_lam hbody
    exact ⟨_, _, hb, rfl, by omega⟩
  | applySpec hf _ => obtain ⟨he, _⟩ := cv_mix hf; simp [mixBody] at he
  | value hv => exact absurd hv app_not_ready

/-- `mix l u` applied to two arguments: three rules, two bindings, then `u s (l s x)`. -/
theorem cv_mix_app_app {l u s X v : Term} {k : Nat} (h : CV (.app (.app (.mix l u) s) X) v k) :
    ∃ s1 ks x kx kb, Run .bind s s1 ks ∧ Run .bind X x kx ∧
      CV (.app (.app u s1) (.app (.app l s1) x)) v kb ∧ k = ks + kx + kb + 3 := by
  cases h with
  | apply hf hb hbody =>
    obtain ⟨s1, ks, hs, hw, rfl⟩ := cv_mix_app hf
    simp only [mixPartial, Term.lam.injEq] at hw
    subst hw
    rw [mixBody_outer] at hbody
    exact ⟨s1, ks, _, _, _, hs, hb, hbody, by omega⟩
  | applySpec hf _ => obtain ⟨_, _, _, hw, _⟩ := cv_mix_app hf; simp [mixPartial] at hw
  | value hv => exact absurd hv app_not_ready

theorem mk_mix_app_app {l u s X s1 x v : Term} {ks kx kb : Nat} (hs : Run .bind s s1 ks)
    (hx : Run .bind X x kx) (hb : CV (.app (.app u s1) (.app (.app l s1) x)) v kb) :
    CV (.app (.app (.mix l u) s) X) v (ks + kx + kb + 3) := by
  let BODY : Term := .app (.app (u.rename (fun n => n + 2)) (.bound 1))
      (.app (.app (l.rename (fun n => n + 2)) (.bound 1)) (.bound 0))
  have hm : CV (.mix l u) (.lam (.lam BODY)) 1 := Run.mix l u
  have h3 : CV (instantiate (.lam BODY) s1) (.lam (BODY.substitute (liftSubstitution (single s1)))) 0 := by
    rw [mixBody_inner]; exact .value (.lam _)
  have inner := Run.apply hm hs h3
  have h4 : CV (instantiate (BODY.substitute (liftSubstitution (single s1))) x) v kb := by
    rw [mixBody_outer]; exact hb
  have := Run.apply inner hx h4
  have e : 1 + ks + 0 + 1 + kx + kb + 1 = ks + kx + kb + 3 := by omega
  rw [e] at this; exact this

end Obend.Equiv
end
