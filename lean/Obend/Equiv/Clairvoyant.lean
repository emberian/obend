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

`fix s i` is a recursive `let`, given the two-stage demand semantics of contract C4 (Xia, Israel,
Kramarz, Coltharp, Claessen, Weirich, Li, ICFP 2024, extended to knots). Its body is settled once,
with `self` the open index 0 (a pointer that may be passed but never entered), into a template
(`Run .head`): evaluation that leaves the head record's fields unbound, so work outside the record
is paid once. The template's fields are then filled in waves (`Run .knot`): the first reads `self`
as `skipped`, each later one as the approximant the last produced; a field is evaluated (Let′, its
cost plus 1) in the first wave where it can be, and kept afterwards at no cost, so each field is
paid once; a field that never can be (`self.bad` reading itself) stays `skipped`, as need
blackholes it. A template that is already a value (a recursive function) is unrolled at no cost,
each approximant reading the one before. Hackett and Hutton's `Let′` at `fix`, which evaluated the
body before `self` was bound and so could not derive `{a = 7, b = self.a}.b`, is gone.

A knot, `fix (λself. λsuper. V) {}` with `V` a value, is still a settled form: entering it costs 3
(`knot_unfold`).

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

/-- The two modes whose rules end in a premise of their own mode: evaluating a term, and settling
the template of a recursive body (evaluation that leaves the head record's fields unbound). -/
inductive Tail where
  | eval | head
  deriving DecidableEq

/-- What a derivation produces: an evaluation or a template, one binding, a field list, one cell of
a wave, one wave, or the approximant a knot reaches. -/
inductive Mode where
  | tail (r : Tail) | bind | fields | cell | wave | knot
  deriving DecidableEq

@[match_pattern, reducible] def Mode.eval : Mode := .tail .eval
@[match_pattern, reducible] def Mode.head : Mode := .tail .head

/-- No field of the record is known yet: Xia et al.'s least approximation of a record. -/
def pending (fs : List (String × Term)) : Term := .record (fs.map fun f => (f.1, skipped))

/-- `Run .eval t v k`: `t` evaluates to the value `v` at cost `k`. `Run .bind a x k`: the binding
of `a` leaves `x` at cost `k`. `Run .fields (.record fs) (.record fs') k`: binding each field.

The knot of `fix s i` takes four more modes. `Run .head t T k`: `t` (the body, `self` the open
index 0) settles to the template `T`, a value or a record whose fields are left unbound.
`Run .cell (.app (.app t S) p) p' k`: one field `t` of the template, read against the approximant
`S` of `self`, moves from `p` to `p'`. `Run .wave (.app (.app (.record fs) S) (.record ps))
(.record ps') k`: every field once. `Run .knot (.app T S) V k`: from the approximant `S`, the waves
reach `V`. -/
inductive Run : Mode → Term → Term → Nat → Prop where
  | value {v : Term} : CValue v → Run .eval v v 0
  | apply {r : Tail} {f a b x v : Term} {k1 k2 k3 : Nat} :
      Run .eval f (.lam b) k1 → Run .bind a x k2 → Run (.tail r) (instantiate b x) v k3 →
      Run (.tail r) (.app f a) v (k1 + k2 + k3 + 1)
  | applySpec {r : Tail} {f a me e v : Term} {k1 k2 : Nat} :
      Run .eval f (.specification me e) k1 → Run (.tail r) (.app e a) v k2 → Run (.tail r) (.app f a) v (k1 + k2 + 1)
  | mix (l u : Term) : Run .eval (.mix l u) (mixBody l u) 1
  /-- The two-stage rule at `self`: the body is settled once, with `self` open, into a template;
  the template's fields are then filled in waves from `skipped`, each read against the last. -/
  | fix {s i T V : Term} {k1 k2 : Nat} :
      Run .head (selfBody s i) T k1 → Run .knot (.app T skipped) V k2 →
      Run .eval (.fix s i) V (k1 + k2 + 1)
  | specification {m e m' e' : Term} {k1 k2 : Nat} : ¬ CValue (.specification m e) →
      Run .bind m m' k1 → Run .bind e e' k2 → Run .eval (.specification m e) (.specification m' e') (k1 + k2 + 1)
  | prototype {s g s' g' : Term} {k1 k2 : Nat} : ¬ CValue (.prototype s g) →
      Run .bind s s' k1 → Run .bind g g' k2 → Run .eval (.prototype s g) (.prototype s' g') (k1 + k2 + 1)
  | reflect {r : Tail} {p s g v : Term} {k1 k2 : Nat} :
      Run .eval p (.prototype s g) k1 → Run (.tail r) s v k2 → Run (.tail r) (.reflect p) v (k1 + k2 + 1)
  | metadata {r : Tail} {p me e v : Term} {k1 k2 : Nat} :
      Run .eval p (.specification me e) k1 → Run (.tail r) me v k2 → Run (.tail r) (.metadata p) v (k1 + k2 + 1)
  | project {r : Tail} {p s g v : Term} {k1 k2 : Nat} :
      Run .eval p (.prototype s g) k1 → Run (.tail r) g v k2 → Run (.tail r) (.project p) v (k1 + k2 + 1)
  | record {fs fs' : List (String × Term)} {k : Nat} : ¬ CValue (.record fs) →
      Run .fields (.record fs) (.record fs') k → Run .eval (.record fs) (.record fs') (k + 1)
  | get {r : Tail} {g x v : Term} {fs : List (String × Term)} {name : String} {k1 k2 : Nat} :
      Run .eval g (.record fs) k1 → fs.find? (fun f => f.1 == name) = some (name, x) →
      Run (.tail r) x v k2 → Run (.tail r) (.get g name) v (k1 + k2 + 1)
  | extend {i : Term} {inh fs fs' : List (String × Term)} {k1 k2 : Nat} :
      Run .eval i (.record inh) k1 → Run .fields (.record fs) (.record fs') k2 →
      Run .eval (.extend i fs) (.record (extendFields inh fs')) (k1 + k2 + 1)
  | binary {op : Primitive} {l r lv rv res : Term} {k1 k2 : Nat} :
      Run .eval l lv k1 → Run .eval r rv k2 → primitiveResult op lv rv = some res →
      Run .eval (.binary op l r) res (k1 + k2 + 1)
  | zero {r : Tail} {c z s v : Term} {k1 k2 : Nat} :
      Run .eval c (.nat 0) k1 → Run (.tail r) z v k2 → Run (.tail r) (.ifZero c z s) v (k1 + k2 + 1)
  | succ {r : Tail} {c z s v : Term} {n k1 k2 : Nat} :
      Run .eval c (.nat (n + 1)) k1 → Run (.tail r) (instantiate s (.nat n)) v k2 →
      Run (.tail r) (.ifZero c z s) v (k1 + k2 + 1)
  | inject {l : String} {p p' : Term} {k : Nat} : ¬ CValue (.inject l p) →
      Run .bind p p' k → Run .eval (.inject l p) (.inject l p') (k + 1)
  | case {r : Tail} {sc p body v : Term} {l : String} {arms : List (String × Term)} {k1 k2 : Nat} :
      Run .eval sc (.inject l p) k1 → arms.find? (fun a => a.1 == l) = some (l, body) →
      Run (.tail r) (instantiate body p) v k2 → Run (.tail r) (.case sc arms) v (k1 + k2 + 1)
  | ifTrue {r : Tail} {c x y v : Term} {k1 k2 : Nat} :
      Run .eval c (.boolean true) k1 → Run (.tail r) x v k2 → Run (.tail r) (.ifBool c x y) v (k1 + k2 + 1)
  | ifFalse {r : Tail} {c x y v : Term} {k1 k2 : Nat} :
      Run .eval c (.boolean false) k1 → Run (.tail r) y v k2 → Run (.tail r) (.ifBool c x y) v (k1 + k2 + 1)
  | done {r : Tail} {x v : Term} {k : Nat} : Run (.tail r) x v k → Run (.tail r) (.done x) v (k + 1)
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
  /-- Any evaluation settles a template (its lazy parts bound, with `self` open). -/
  | headEval {t v : Term} {k : Nat} : Run .eval t v k → Run .head t v k
  /-- The head record of the body: its fields are left for the waves. -/
  | headRecord {fs : List (String × Term)} : ¬ CValue (.record fs) → Run .head (.record fs) (.record fs) 1
  /-- An extension at the head: its own fields, like the inherited ones, are left for the waves. -/
  | headExtend {i : Term} {inh fs : List (String × Term)} {k : Nat} :
      Run .head i (.record inh) k → Run .head (.extend i fs) (.record (extendFields inh fs)) (k + 1)
  /-- A field that is settled once `self` is read is taken as it is (a value, a pointer). -/
  | cellValue {t S p : Term} : Settled (t.substitute (single S)) →
      Run .cell (.app (.app t S) p) (t.substitute (single S)) 0
  /-- A field already evaluated in an earlier wave keeps its value: it is paid once. -/
  | cellKeep {t S p : Term} : ¬ Settled (t.substitute (single S)) → Settled p → p ≠ skipped →
      Run .cell (.app (.app t S) p) p 0
  /-- A field not yet evaluated waits for a later wave. -/
  | cellWait {t S : Term} : ¬ Settled (t.substitute (single S)) →
      Run .cell (.app (.app t S) skipped) skipped 0
  /-- A field not yet evaluated is evaluated now, reading `self` as the last approximant (Let′). -/
  | cellEval {t S v : Term} {k : Nat} : ¬ Settled (t.substitute (single S)) →
      Run .eval (t.substitute (single S)) v k → Run .cell (.app (.app t S) skipped) v (k + 1)
  | waveNil {S : Term} : Run .wave (.app (.app (.record []) S) (.record [])) (.record []) 0
  | waveCons {n : String} {t S p p' : Term} {fs ps ps' : List (String × Term)} {k1 k2 : Nat} :
      Run .cell (.app (.app t S) p) p' k1 →
      Run .wave (.app (.app (.record fs) S) (.record ps)) (.record ps') k2 →
      Run .wave (.app (.app (.record ((n, t) :: fs)) S) (.record ((n, p) :: ps)))
        (.record ((n, p') :: ps')) (k1 + k2)
  /-- The waves stop at a value. -/
  | knotDone {T P : Term} : CValue P → Run .knot (.app T P) P 0
  /-- The first wave of a record template reads `self` as `skipped`; no field is known. -/
  | knotFirst {fs : List (String × Term)} {P V : Term} {k1 k2 : Nat} :
      Run .wave (.app (.app (.record fs) skipped) (pending fs)) P k1 → Run .knot (.app (.record fs) P) V k2 →
      Run .knot (.app (.record fs) skipped) V (k1 + k2)
  /-- A later wave reads `self` as the last approximant, and starts from its fields. -/
  | knotWave {fs ps : List (String × Term)} {P V : Term} {k1 k2 : Nat} :
      Run .wave (.app (.app (.record fs) (.record ps)) (.record ps)) P k1 →
      Run .knot (.app (.record fs) P) V k2 → Run .knot (.app (.record fs) (.record ps)) V (k1 + k2)
  /-- A template that is already a value is unrolled once more, at no cost: a recursive function's
  approximant reads the one before it. -/
  | knotUnroll {T S V : Term} {k : Nat} : CValue T → Run .knot (.app T (T.substitute (single S))) V k →
      Run .knot (.app T S) V k

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
  | .head, T => CValue T ∨ ∃ fs, T = .record fs
  | .cell, x => Settled x
  | .wave, w => ∃ fs, w = .record fs ∧ ∀ f ∈ fs, Settled f.2
  | .knot, v => CValue v

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
  | fix _ _ _ ih => exact ih
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
  | headEval _ ih => exact .inl ih
  | headRecord _ => exact .inr ⟨_, rfl⟩
  | headExtend _ _ => exact .inr ⟨_, rfl⟩
  | cellValue h => exact h
  | cellKeep _ h _ => exact h
  | cellWait _ => exact .skipped
  | cellEval _ _ ih => exact ih.settled
  | waveNil => exact ⟨[], rfl, by simp⟩
  | waveCons _ _ i1 i2 =>
    obtain ⟨fs, eq, h⟩ := i2
    cases eq
    refine ⟨_, rfl, ?_⟩
    intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact i1
    · exact h f hf
  | knotDone h => exact h
  | knotFirst _ _ _ ih => exact ih
  | knotWave _ _ _ ih => exact ih
  | knotUnroll _ _ ih => exact ih

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
  | fix => cases hv
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

/-- A value settles only to itself, at no cost, in either tail mode. -/
theorem run_of_value {r : Tail} {t v : Term} {k : Nat} (hv : CValue t) (h : Run (.tail r) t v k) :
    v = t ∧ k = 0 := by
  cases h with
  | headEval h => exact cv_of_value hv h
  | headRecord hn => exact absurd hv hn
  | headExtend => cases hv
  | value _ => exact ⟨rfl, rfl⟩
  | specification hn => exact absurd hv hn
  | prototype hn => exact absurd hv hn
  | record hn => exact absurd hv hn
  | inject hn => exact absurd hv hn
  | apply => cases hv
  | applySpec => cases hv
  | mix => cases hv
  | fix => cases hv
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
application and back, in either tail mode. -/

theorem hoist_arg_aux {m : Mode} {t v : Term} {k : Nat} (h : Run m t v k) : ∀ {r : Tail}, m = .tail r →
    ∀ {F X : Term}, t = .app F X → ∃ x kx k1, Run .bind X x kx ∧ Run m (.app F x) v k1 ∧ k = kx + k1 := by
  induction h with
  | apply hf hb hbody _ _ _ =>
    intro _ _ F X e; cases e
    exact ⟨_, _, _, hb, .apply hf (bind_value_keep hb) hbody, by omega⟩
  | applySpec hf _ _ ih =>
    intro _ hm F X e; cases e
    obtain ⟨x, kx, k1, hb, run, eq⟩ := ih hm rfl
    exact ⟨x, kx, _, hb, .applySpec hf run, by omega⟩
  | headEval _ ih =>
    intro _ _ F X e
    obtain ⟨x, kx, k1, hb, run, eq⟩ := ih rfl e
    exact ⟨x, kx, k1, hb, .headEval run, eq⟩
  | value hv => intro _ _ F X e; cases e; exact absurd hv app_not_ready
  | _ => intro _ hm F X e; first | (cases hm; done) | (cases e; done)

theorem hoist_arg {r : Tail} {F X v : Term} {k : Nat} (h : Run (.tail r) (.app F X) v k) :
    ∃ x kx k1, Run .bind X x kx ∧ Run (.tail r) (.app F x) v k1 ∧ k = kx + k1 :=
  hoist_arg_aux h rfl rfl

theorem hoist_fun {r : Tail} {F S U v : Term} {k : Nat} (h : Run (.tail r) (.app (.app F S) U) v k) :
    ∃ x kx k1, Run .bind S x kx ∧ Run (.tail r) (.app (.app F x) U) v k1 ∧ k = kx + k1 := by
  cases h with
  | apply hf hb hbody =>
    obtain ⟨x, kx, k1, hs, run, eq⟩ := hoist_arg hf
    exact ⟨x, kx, _, hs, .apply run hb hbody, by omega⟩
  | applySpec hf hrest =>
    obtain ⟨x, kx, k1, hs, run, eq⟩ := hoist_arg hf
    exact ⟨x, kx, _, hs, .applySpec run hrest, by omega⟩
  | headEval h =>
    cases h with
    | apply hf hb hbody =>
      obtain ⟨x, kx, k1, hs, run, eq⟩ := hoist_arg hf
      exact ⟨x, kx, _, hs, .headEval (.apply run hb hbody), by omega⟩
    | applySpec hf hrest =>
      obtain ⟨x, kx, k1, hs, run, eq⟩ := hoist_arg hf
      exact ⟨x, kx, _, hs, .headEval (.applySpec run hrest), by omega⟩
    | value hv => exact absurd hv app_not_ready
  | value hv => exact absurd hv app_not_ready

theorem unhoist_arg_aux {m : Mode} {t v : Term} {k1 : Nat} (h : Run m t v k1) : ∀ {r : Tail}, m = .tail r →
    ∀ {F X x : Term} {kx : Nat}, Run .bind X x kx → t = .app F x →
      ∃ k, Run m (.app F X) v k ∧ k ≤ kx + k1 := by
  induction h with
  | @apply _ f a b x2 w k1 k2 k3 hf hb2 hbody _ _ _ =>
    intro _ _ F X x kx hb e; cases e
    rcases bind_of_settled (bind_settled hb) hb2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, .apply hf hb hbody, by omega⟩
    · exact ⟨_, .apply hf (.skip _) hbody, by omega⟩
  | applySpec hf _ _ ih =>
    intro _ hm F X x kx hb e; cases e
    obtain ⟨k, run, le⟩ := ih hm hb rfl
    exact ⟨_, .applySpec hf run, by omega⟩
  | headEval _ ih =>
    intro _ _ F X x kx hb e
    obtain ⟨k, run, le⟩ := ih rfl hb e
    exact ⟨k, .headEval run, le⟩
  | value hv => intro _ _ F X x kx hb e; cases e; exact absurd hv app_not_ready
  | _ => intro _ hm F X x kx hb e; first | (cases hm; done) | (cases e; done)

/-- A binding moved back into an application, where the application binds its result (or skips
it): the cost is at most the two costs together. -/
theorem unhoist_arg {r : Tail} {F X x v : Term} {kx k1 : Nat} (hb : Run .bind X x kx)
    (h : Run (.tail r) (.app F x) v k1) : ∃ k, Run (.tail r) (.app F X) v k ∧ k ≤ kx + k1 :=
  unhoist_arg_aux h rfl hb rfl

theorem unhoist_fun {r : Tail} {F S U x v : Term} {kx k1 : Nat} (hb : Run .bind S x kx)
    (h : Run (.tail r) (.app (.app F x) U) v k1) : ∃ k, Run (.tail r) (.app (.app F S) U) v k ∧ k ≤ kx + k1 := by
  cases h with
  | apply hf hb2 hbody =>
    obtain ⟨k, run, le⟩ := unhoist_arg hb hf
    exact ⟨_, .apply run hb2 hbody, by omega⟩
  | applySpec hf hrest =>
    obtain ⟨k, run, le⟩ := unhoist_arg hb hf
    exact ⟨_, .applySpec run hrest, by omega⟩
  | headEval h =>
    cases h with
    | apply hf hb2 hbody =>
      obtain ⟨k, run, le⟩ := unhoist_arg hb hf
      exact ⟨_, .headEval (.apply run hb2 hbody), by omega⟩
    | applySpec hf hrest =>
      obtain ⟨k, run, le⟩ := unhoist_arg hb hf
      exact ⟨_, .headEval (.applySpec run hrest), by omega⟩
    | value hv => exact absurd hv app_not_ready
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
theorem cv_mix_app_app_eval {l u s X v : Term} {k : Nat} (h : CV (.app (.app (.mix l u) s) X) v k) :
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

/-- `mix l u` applied to two arguments: three rules, two bindings, then `u s (l s x)`. -/
theorem cv_mix_app_app {r : Tail} {l u s X v : Term} {k : Nat}
    (h : Run (.tail r) (.app (.app (.mix l u) s) X) v k) :
    ∃ s1 ks x kx kb, Run .bind s s1 ks ∧ Run .bind X x kx ∧
      Run (.tail r) (.app (.app u s1) (.app (.app l s1) x)) v kb ∧ k = ks + kx + kb + 3 := by
  cases h with
  | apply hf hb hbody =>
    obtain ⟨s1, ks, hs, hw, rfl⟩ := cv_mix_app hf
    simp only [mixPartial, Term.lam.injEq] at hw
    subst hw
    rw [mixBody_outer] at hbody
    exact ⟨s1, ks, _, _, _, hs, hb, hbody, by omega⟩
  | applySpec hf _ => obtain ⟨_, _, _, hw, _⟩ := cv_mix_app hf; simp [mixPartial] at hw
  | headEval h =>
    obtain ⟨s1, ks, x, kx, kb, hs, hx, hb, rfl⟩ := cv_mix_app_app_eval h
    exact ⟨s1, ks, x, kx, kb, hs, hx, .headEval hb, rfl⟩
  | value hv => exact absurd hv app_not_ready

theorem mk_mix_app_app {r : Tail} {l u s X s1 x v : Term} {ks kx kb : Nat} (hs : Run .bind s s1 ks)
    (hx : Run .bind X x kx) (hb : Run (.tail r) (.app (.app u s1) (.app (.app l s1) x)) v kb) :
    Run (.tail r) (.app (.app (.mix l u) s) X) v (ks + kx + kb + 3) := by
  let BODY : Term := .app (.app (u.rename (fun n => n + 2)) (.bound 1))
      (.app (.app (l.rename (fun n => n + 2)) (.bound 1)) (.bound 0))
  have hm : CV (.mix l u) (.lam (.lam BODY)) 1 := Run.mix l u
  have h3 : CV (instantiate (.lam BODY) s1) (.lam (BODY.substitute (liftSubstitution (single s1)))) 0 := by
    rw [mixBody_inner]; exact .value (.lam _)
  have inner := Run.apply hm hs h3
  have h4 : Run (.tail r) (instantiate (BODY.substitute (liftSubstitution (single s1))) x) v kb := by
    rw [mixBody_outer]; exact hb
  have := Run.apply inner hx h4
  have e : 1 + ks + 0 + 1 + kx + kb + 1 = ks + kx + kb + 3 := by omega
  rw [e] at this; exact this

end Obend.Equiv
end
