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
public import Obend.Tactic.Tooth
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

/-! ## Executable Clairvoyant Minimum-Cost Evaluator -/

mutual
/-- Executable decision procedure for `CValue t` (`Ready true t`). -/
def isCValue : Term → Bool
  | .lam _ => true
  | .nat _ => true
  | .boolean _ => true
  | .label _ => true
  | .record fs => isSettledFields fs
  | .specification m e => isSettled m && isSettled e
  | .prototype s g => isSettled s && isSettled g
  | .inject _ p => isSettled p
  | _ => false
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Executable decision procedure for `Settled t` (`Ready false t`). -/
def isSettled : Term → Bool
  | .lam _ => true
  | .nat _ => true
  | .boolean _ => true
  | .label _ => true
  | .record fs => isSettledFields fs
  | .specification m e => isSettled m && isSettled e
  | .prototype s g => isSettled s && isSettled g
  | .inject _ p => isSettled p
  | .hole 0 [] => true
  | .bound _ => true
  | .fix (.lam (.lam W)) i => isCValue W && isSettled i
  | _ => false
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Executable decision procedure for `∀ f ∈ fs, Settled f.2`. -/
def isSettledFields : List (String × Term) → Bool
  | [] => true
  | (_, t) :: fs => isSettled t && isSettledFields fs
termination_by fs => sizeOf fs
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (simp +arith; omega)
end

mutual
theorem isCValue_sound : (t : Term) → isCValue t = true → CValue t
  | .lam b, _ => .lam b
  | .nat n, _ => .nat n
  | .boolean b, _ => .boolean b
  | .label l, _ => .label l
  | .record fs, h => by
    unfold isCValue at h
    exact .record (isSettledFields_sound fs h)
  | .specification m e, h => by
    unfold isCValue at h
    rw [Bool.and_eq_true] at h
    exact .specification (isSettled_sound m h.1) (isSettled_sound e h.2)
  | .prototype s g, h => by
    unfold isCValue at h
    rw [Bool.and_eq_true] at h
    exact .prototype (isSettled_sound s h.1) (isSettled_sound g h.2)
  | .inject l p, h => by
    unfold isCValue at h
    exact .inject l (isSettled_sound p h)
  | .hole _ _, h | .bound _, h | .app _ _, h | .mix _ _, h | .fix _ _, h
  | .reflect _, h | .metadata _, h | .project _, h | .binary _ _ _, h
  | .extend _ _, h | .get _ _, h | .ifZero _ _ _, h | .case _ _, h
  | .ifBool _ _ _, h | .perform _, h | .done _, h | .split _ _ _, h => by
    unfold isCValue at h; cases h
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem isSettled_sound : (t : Term) → isSettled t = true → Settled t
  | .lam b, _ => .value (.lam b)
  | .nat n, _ => .value (.nat n)
  | .boolean b, _ => .value (.boolean b)
  | .label l, _ => .value (.label l)
  | .record fs, h => by
    unfold isSettled at h
    exact .value (.record (isSettledFields_sound fs h))
  | .specification m e, h => by
    unfold isSettled at h
    rw [Bool.and_eq_true] at h
    exact .value (.specification (isSettled_sound m h.1) (isSettled_sound e h.2))
  | .prototype s g, h => by
    unfold isSettled at h
    rw [Bool.and_eq_true] at h
    exact .value (.prototype (isSettled_sound s h.1) (isSettled_sound g h.2))
  | .inject l p, h => by
    unfold isSettled at h
    exact .value (.inject l (isSettled_sound p h))
  | .hole 0 [], _ => .skipped
  | .hole 0 (_ :: _), h => by unfold isSettled at h; cases h
  | .hole (_ + 1) _, h => by unfold isSettled at h; cases h
  | .bound i, _ => .bound i
  | .fix (.lam (.lam W)) i, h => by
    unfold isSettled at h
    rw [Bool.and_eq_true] at h
    exact .knot (isCValue_sound W h.1) (isSettled_sound i h.2)
  | .fix (.lam (.hole _ _)) _, h | .fix (.lam (.bound _)) _, h | .fix (.lam (.app _ _)) _, h
  | .fix (.lam (.mix _ _)) _, h | .fix (.lam (.fix _ _)) _, h | .fix (.lam (.specification _ _)) _, h
  | .fix (.lam (.prototype _ _)) _, h | .fix (.lam (.reflect _)) _, h | .fix (.lam (.metadata _)) _, h
  | .fix (.lam (.project _)) _, h | .fix (.lam (.nat _)) _, h | .fix (.lam (.boolean _)) _, h
  | .fix (.lam (.label _)) _, h | .fix (.lam (.binary _ _ _)) _, h | .fix (.lam (.extend _ _)) _, h
  | .fix (.lam (.record _)) _, h | .fix (.lam (.get _ _)) _, h | .fix (.lam (.ifZero _ _ _)) _, h
  | .fix (.lam (.inject _ _)) _, h | .fix (.lam (.case _ _)) _, h | .fix (.lam (.ifBool _ _ _)) _, h
  | .fix (.lam (.perform _)) _, h | .fix (.lam (.done _)) _, h | .fix (.lam (.split _ _ _)) _, h
  | .fix (.hole _ _) _, h | .fix (.bound _) _, h | .fix (.app _ _) _, h | .fix (.mix _ _) _, h
  | .fix (.fix _ _) _, h | .fix (.specification _ _) _, h | .fix (.prototype _ _) _, h
  | .fix (.reflect _) _, h | .fix (.metadata _) _, h | .fix (.project _) _, h | .fix (.nat _) _, h
  | .fix (.boolean _) _, h | .fix (.label _) _, h | .fix (.binary _ _ _) _, h
  | .fix (.extend _ _) _, h | .fix (.record _) _, h | .fix (.get _ _) _, h
  | .fix (.ifZero _ _ _) _, h | .fix (.inject _ _) _, h | .fix (.case _ _) _, h
  | .fix (.ifBool _ _ _) _, h | .fix (.perform _) _, h | .fix (.done _) _, h
  | .fix (.split _ _ _) _, h
  | .app _ _, h | .mix _ _, h | .reflect _, h | .metadata _, h | .project _, h
  | .binary _ _ _, h | .extend _ _, h | .get _ _, h | .ifZero _ _ _, h | .case _ _, h
  | .ifBool _ _ _, h | .perform _, h | .done _, h | .split _ _ _, h => by
    unfold isSettled at h; cases h
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem isSettledFields_sound : (fs : List (String × Term)) → isSettledFields fs = true →
    ∀ f ∈ fs, Settled f.2
  | [], _, f, hf => by simp at hf
  | (name, t) :: rest, h, f, hf => by
    unfold isSettledFields at h
    rw [Bool.and_eq_true] at h
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact isSettled_sound t h.1
    · exact isSettledFields_sound rest h.2 f hf
termination_by fs => sizeOf fs
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (simp +arith; omega)
end

theorem isSettledFields_of_all {fs : List (String × Term)}
    (h : ∀ f ∈ fs, isSettled f.2 = true) : isSettledFields fs = true := by
  induction fs with
  | nil => unfold isSettledFields; rfl
  | cons f rest ih =>
    obtain ⟨n, t⟩ := f
    unfold isSettledFields
    rw [Bool.and_eq_true]
    exact ⟨h (n, t) List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem isReady_of_ready {b : Bool} {t : Term} (h : Ready b t) :
    (if b then isCValue t else isSettled t) = true := by
  induction h with
  | lam _ | nat _ | boolean _ | label _ => simp [isCValue]
  | record _ ih =>
    simp only [ite_true]
    unfold isCValue
    exact isSettledFields_of_all (fun f hf => by simpa using ih f hf)
  | specification _ _ i1 i2 =>
    simp only [ite_true]
    unfold isCValue
    rw [Bool.and_eq_true]
    exact ⟨by simpa using i1, by simpa using i2⟩
  | prototype _ _ i1 i2 =>
    simp only [ite_true]
    unfold isCValue
    rw [Bool.and_eq_true]
    exact ⟨by simpa using i1, by simpa using i2⟩
  | inject _ _ ih =>
    simp only [ite_true]
    unfold isCValue
    simpa using ih
  | value ht ih =>
    simp only [ite_true] at ih
    simp only [Bool.false_eq_true, ite_false]
    cases ht <;> (unfold isCValue at ih; unfold isSettled; exact ih)
  | skipped =>
    simp only [Bool.false_eq_true, ite_false, skipped]
    unfold isSettled; rfl
  | bound _ =>
    simp only [Bool.false_eq_true, ite_false]
    unfold isSettled; rfl
  | knot _ _ i1 i2 =>
    simp only [ite_true] at i1
    simp only [Bool.false_eq_true, ite_false] at i2 ⊢
    unfold isSettled
    rw [Bool.and_eq_true]
    exact ⟨i1, i2⟩

theorem CValue.isCValue_eq_true {t : Term} (h : CValue t) : isCValue t = true := by
  simpa using isReady_of_ready h

theorem Settled.isSettled_eq_true {t : Term} (h : Settled t) : isSettled t = true := by
  simpa using isReady_of_ready h

theorem isCValue_iff (t : Term) : isCValue t = true ↔ CValue t :=
  ⟨isCValue_sound t, CValue.isCValue_eq_true⟩

theorem isSettled_iff (t : Term) : isSettled t = true ↔ Settled t :=
  ⟨isSettled_sound t, Settled.isSettled_eq_true⟩

theorem not_cvalue_of_isCValue_false {t : Term} (h : isCValue t = false) : ¬ CValue t := by
  intro hc; rw [hc.isCValue_eq_true] at h; cases h

theorem not_settled_of_isSettled_false {t : Term} (h : isSettled t = false) : ¬ Settled t := by
  intro hs; rw [hs.isSettled_eq_true] at h; cases h

theorem isCValue_app (f a : Term) : isCValue (.app f a) = false := by
  unfold isCValue; rfl

/-- Pick the minimum-cost result when both branches succeed, or whichever succeeds. -/
def pickMinCost : Option (Term × Nat) → Option (Term × Nat) → Option (Term × Nat)
  | some (v1, k1), some (v2, k2) => if k1 ≤ k2 then some (v1, k1) else some (v2, k2)
  | some r1, none => some r1
  | none, some r2 => some r2
  | none, none => none

theorem pickMinCost_sound {P : Term → Nat → Prop} {o1 o2 : Option (Term × Nat)} {v : Term} {k : Nat}
    (h1 : ∀ v1 k1, o1 = some (v1, k1) → P v1 k1)
    (h2 : ∀ v2 k2, o2 = some (v2, k2) → P v2 k2)
    (h : pickMinCost o1 o2 = some (v, k)) : P v k := by
  cases o1 with
  | none =>
    cases o2 with
    | none => cases h
    | some r2 =>
      obtain ⟨v2, k2⟩ := r2
      simp only [pickMinCost, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact h2 v2 k2 rfl
  | some r1 =>
    obtain ⟨v1, k1⟩ := r1
    cases o2 with
    | none =>
      simp only [pickMinCost, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact h1 v1 k1 rfl
    | some r2 =>
      obtain ⟨v2, k2⟩ := r2
      simp only [pickMinCost] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact h1 v1 k1 rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact h2 v2 k2 rfl

theorem pickMinCost_le_right {o1 : Option (Term × Nat)} {v2 : Term} {k2 : Nat} :
    ∃ v k, pickMinCost o1 (some (v2, k2)) = some (v, k) ∧ k ≤ k2 := by
  cases o1 with
  | none => exact ⟨v2, k2, rfl, Nat.le_refl k2⟩
  | some r1 =>
    obtain ⟨v1, k1⟩ := r1
    simp only [pickMinCost]
    split
    · rename_i hle
      exact ⟨v1, k1, rfl, hle⟩
    · exact ⟨v2, k2, rfl, Nat.le_refl k2⟩

theorem pickMinCost_le_left {o2 : Option (Term × Nat)} {v1 : Term} {k1 : Nat} :
    ∃ v k, pickMinCost (some (v1, k1)) o2 = some (v, k) ∧ k ≤ k1 := by
  cases o2 with
  | none => exact ⟨v1, k1, rfl, Nat.le_refl k1⟩
  | some r2 =>
    obtain ⟨v2, k2⟩ := r2
    simp only [pickMinCost]
    split
    · exact ⟨v1, k1, rfl, Nat.le_refl k1⟩
    · rename_i hgt
      exact ⟨v2, k2, rfl, by omega⟩

/-- Demand hint propagated from a consumer (`.get`, `.case`, `.project`, `.reflect`, `.metadata`)
to an unsettled value constructor (`.record`, `.extend`, `.inject`, `.prototype`, `.specification`, `.fix`). -/
inductive DemandHint where
  | full
  | skipInjectPayload
  | fieldOnly (name : String)
  | skipAllFields
  | protoReflect
  | protoProject
  | specMetadata
  | specApply
  deriving DecidableEq, Repr

/-- Minimum-cost `Run .bind` when a bound term is not demanded downstream:
`keep` (cost 0) if settled, or `skip` (cost 1) if unsettled. -/
def skipClairvoyantBind (t : Term) : Term × Nat :=
  if isSettled t then (t, 0) else (skipped, 1)

theorem skipClairvoyantBind_sound (t : Term) :
    Run .bind t (skipClairvoyantBind t).1 (skipClairvoyantBind t).2 := by
  unfold skipClairvoyantBind
  split
  · rename_i hs
    exact .keep (isSettled_sound t hs)
  · exact .skip t

/-- Clairvoyant `Run .bind` when a bound term is demanded: `keep` (cost 0) if settled,
`eval` (`Let′`, cost `k + 1`) if evaluation succeeds, or `skip` (cost 1) otherwise. -/
def evalClairvoyantBind (eval : Term → Option (Term × Nat)) (t : Term) : Term × Nat :=
  if isSettled t then
    (t, 0)
  else
    match eval t with
    | some (vt, kt) => (vt, kt + 1)
    | none => (skipped, 1)

theorem evalClairvoyantBind_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) (t : Term) :
    Run .bind t (evalClairvoyantBind eval t).1 (evalClairvoyantBind eval t).2 := by
  unfold evalClairvoyantBind
  split
  · rename_i hs
    exact .keep (isSettled_sound t hs)
  · rename_i hns
    have hnot : ¬ Settled t := fun hs => hns hs.isSettled_eq_true
    split
    · rename_i vt kt ht
      exact .eval hnot (heval t vt kt ht)
    · exact .skip t

def bindForSpecM (eval : Term → Option (Term × Nat)) (hint : DemandHint) (m : Term) : Term × Nat :=
  match hint with
  | .specApply => skipClairvoyantBind m
  | _ => evalClairvoyantBind eval m

theorem bindForSpecM_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) (hint : DemandHint) (m : Term) :
    Run .bind m (bindForSpecM eval hint m).1 (bindForSpecM eval hint m).2 := by
  cases hint <;> first | exact skipClairvoyantBind_sound m | exact evalClairvoyantBind_sound heval m

def bindForSpecE (eval : Term → Option (Term × Nat)) (hint : DemandHint) (e : Term) : Term × Nat :=
  match hint with
  | .specMetadata => skipClairvoyantBind e
  | _ => evalClairvoyantBind eval e

theorem bindForSpecE_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) (hint : DemandHint) (e : Term) :
    Run .bind e (bindForSpecE eval hint e).1 (bindForSpecE eval hint e).2 := by
  cases hint <;> first | exact skipClairvoyantBind_sound e | exact evalClairvoyantBind_sound heval e

def bindForProtoS (eval : Term → Option (Term × Nat)) (hint : DemandHint) (s : Term) : Term × Nat :=
  match hint with
  | .protoProject => skipClairvoyantBind s
  | _ => evalClairvoyantBind eval s

theorem bindForProtoS_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) (hint : DemandHint) (s : Term) :
    Run .bind s (bindForProtoS eval hint s).1 (bindForProtoS eval hint s).2 := by
  cases hint <;> first | exact skipClairvoyantBind_sound s | exact evalClairvoyantBind_sound heval s

def bindForProtoG (eval : Term → Option (Term × Nat)) (hint : DemandHint) (g : Term) : Term × Nat :=
  match hint with
  | .protoReflect => skipClairvoyantBind g
  | _ => evalClairvoyantBind eval g

theorem bindForProtoG_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) (hint : DemandHint) (g : Term) :
    Run .bind g (bindForProtoG eval hint g).1 (bindForProtoG eval hint g).2 := by
  cases hint <;> first | exact skipClairvoyantBind_sound g | exact evalClairvoyantBind_sound heval g

def bindForInjectP (eval : Term → Option (Term × Nat)) (hint : DemandHint) (p : Term) : Term × Nat :=
  match hint with
  | .skipInjectPayload => skipClairvoyantBind p
  | _ => evalClairvoyantBind eval p

theorem bindForInjectP_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) (hint : DemandHint) (p : Term) :
    Run .bind p (bindForInjectP eval hint p).1 (bindForInjectP eval hint p).2 := by
  cases hint <;> first | exact skipClairvoyantBind_sound p | exact evalClairvoyantBind_sound heval p

/-- Evaluate record fields under a fuel-bounded clairvoyant evaluator. -/
def evalClairvoyantFields (eval : Term → Option (Term × Nat)) :
    List (String × Term) → Option (List (String × Term) × Nat)
  | [] => some ([], 0)
  | (name, field) :: rest =>
    match evalClairvoyantFields eval rest with
    | none => none
    | some (rest', k2) =>
      if isSettled field then
        some ((name, field) :: rest', 0 + k2 + 1)
      else
        match eval field with
        | some (vf, kf) => some ((name, vf) :: rest', (kf + 1) + k2 + 1)
        | none => some ((name, skipped) :: rest', 1 + k2 + 1)

theorem evalClairvoyantFields_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) :
    ∀ (fs fs' : List (String × Term)) (k : Nat),
      evalClairvoyantFields eval fs = some (fs', k) →
      Run .fields (.record fs) (.record fs') k
  | [], fs', k, h => by
    simp only [evalClairvoyantFields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil
  | (name, field) :: rest, fs', k, h => by
    simp only [evalClairvoyantFields] at h
    split at h
    · cases h
    · rename_i rest' k2 hrest
      have ih := evalClairvoyantFields_sound heval rest rest' k2 hrest
      split at h
      · rename_i hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .cons (.keep (isSettled_sound field hs)) ih
      · rename_i hns
        have hnot : ¬ Settled field := fun hs => hns hs.isSettled_eq_true
        split at h
        · rename_i vf kf hf
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .cons (.eval hnot (heval field vf kf hf)) ih
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .cons (.skip field) ih

/-- Selective record-field binding: when `optTarget = some target`, evaluates only the first field
matching `target` (`Let′` / `keep`) and skips all other unsettled fields (`Skip` / `keep`); when
`optTarget = none`, skips all unsettled fields (`Skip` / `keep`). -/
def evalClairvoyantFieldsFor (eval : Term → Option (Term × Nat)) :
    Option String → List (String × Term) → List (String × Term) × Nat
  | _, [] => ([], 0)
  | some target, (name, field) :: rest =>
    if name == target then
      let (field', k1) := evalClairvoyantBind eval field
      let (rest', k2) := evalClairvoyantFieldsFor eval none rest
      ((name, field') :: rest', k1 + k2 + 1)
    else
      let (field', k1) := skipClairvoyantBind field
      let (rest', k2) := evalClairvoyantFieldsFor eval (some target) rest
      ((name, field') :: rest', k1 + k2 + 1)
  | none, (name, field) :: rest =>
    let (field', k1) := skipClairvoyantBind field
    let (rest', k2) := evalClairvoyantFieldsFor eval none rest
    ((name, field') :: rest', k1 + k2 + 1)

theorem evalClairvoyantFieldsFor_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) :
    ∀ (optTarget : Option String) (fs : List (String × Term)),
      Run .fields (.record fs)
        (.record (evalClairvoyantFieldsFor eval optTarget fs).1)
        (evalClairvoyantFieldsFor eval optTarget fs).2
  | _, [] => .nil
  | some target, (name, field) :: rest => by
    unfold evalClairvoyantFieldsFor
    split
    · exact .cons (evalClairvoyantBind_sound heval field)
        (evalClairvoyantFieldsFor_sound heval none rest)
    · exact .cons (skipClairvoyantBind_sound field)
        (evalClairvoyantFieldsFor_sound heval (some target) rest)
  | none, (name, field) :: rest => by
    unfold evalClairvoyantFieldsFor
    exact .cons (skipClairvoyantBind_sound field)
      (evalClairvoyantFieldsFor_sound heval none rest)

def evalRecordForHint (eval : Term → Option (Term × Nat)) (hint : DemandHint)
    (fs : List (String × Term)) : Option (List (String × Term) × Nat) :=
  match hint with
  | .fieldOnly target => some (evalClairvoyantFieldsFor eval (some target) fs)
  | .skipAllFields => some (evalClairvoyantFieldsFor eval none fs)
  | _ => evalClairvoyantFields eval fs

theorem evalRecordForHint_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (hint : DemandHint) (fs fs' : List (String × Term)) (k : Nat)
    (h : evalRecordForHint eval hint fs = some (fs', k)) :
    Run .fields (.record fs) (.record fs') k := by
  unfold evalRecordForHint at h
  cases hint with
  | fieldOnly target =>
    simp only [Option.some.injEq] at h
    have h1 : (evalClairvoyantFieldsFor eval (some target) fs).1 = fs' := congrArg Prod.fst h
    have h2 : (evalClairvoyantFieldsFor eval (some target) fs).2 = k := congrArg Prod.snd h
    subst h1; subst h2
    exact evalClairvoyantFieldsFor_sound heval (some target) fs
  | skipAllFields =>
    simp only [Option.some.injEq] at h
    have h1 : (evalClairvoyantFieldsFor eval none fs).1 = fs' := congrArg Prod.fst h
    have h2 : (evalClairvoyantFieldsFor eval none fs).2 = k := congrArg Prod.snd h
    subst h1; subst h2
    exact evalClairvoyantFieldsFor_sound heval none fs
  | full | skipInjectPayload | protoReflect | protoProject | specMetadata | specApply =>
    exact evalClairvoyantFields_sound heval fs fs' k h

def evalExtendForHint (evalWithHint : DemandHint → Term → Option (Term × Nat)) (hint : DemandHint)
    (i : Term) (fs : List (String × Term)) : Option (Term × Nat) :=
  match hint with
  | .fieldOnly target =>
    if fs.any (fun f => f.1 == target) then
      let bfs := evalClairvoyantFieldsFor (evalWithHint .full) (some target) fs
      match evalWithHint .skipAllFields i with
      | some (.record inh, k1) => some (.record (extendFields inh bfs.1), k1 + bfs.2 + 1)
      | _ => none
    else
      let bfs := evalClairvoyantFieldsFor (evalWithHint .full) none fs
      match evalWithHint (.fieldOnly target) i with
      | some (.record inh, k1) => some (.record (extendFields inh bfs.1), k1 + bfs.2 + 1)
      | _ => none
  | .skipAllFields =>
    let bfs := evalClairvoyantFieldsFor (evalWithHint .full) none fs
    match evalWithHint .skipAllFields i with
    | some (.record inh, k1) => some (.record (extendFields inh bfs.1), k1 + bfs.2 + 1)
    | _ => none
  | _ =>
    match evalWithHint .full i, evalClairvoyantFields (evalWithHint .full) fs with
    | some (.record inh, k1), some (fs', k2) =>
      some (.record (extendFields inh fs'), k1 + k2 + 1)
    | _, _ => none

theorem evalExtendForHint_sound {evalWithHint : DemandHint → Term → Option (Term × Nat)}
    (heval : ∀ dh t v k, evalWithHint dh t = some (v, k) → CV t v k)
    (hint : DemandHint) (i : Term) (fs : List (String × Term)) (v : Term) (k : Nat)
    (h : evalExtendForHint evalWithHint hint i fs = some (v, k)) :
    CV (.extend i fs) v k := by
  unfold evalExtendForHint at h
  cases hint with
  | fieldOnly target =>
    simp only at h
    split at h
    · split at h
      · rename_i inh k1 hi
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .extend (heval .skipAllFields i (.record inh) k1 hi)
          (evalClairvoyantFieldsFor_sound (heval .full) (some target) fs)
      · cases h
    · split at h
      · rename_i inh k1 hi
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .extend (heval (.fieldOnly target) i (.record inh) k1 hi)
          (evalClairvoyantFieldsFor_sound (heval .full) none fs)
      · cases h
  | skipAllFields =>
    simp only at h
    split at h
    · rename_i inh k1 hi
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .extend (heval .skipAllFields i (.record inh) k1 hi)
        (evalClairvoyantFieldsFor_sound (heval .full) none fs)
    · cases h
  | full | skipInjectPayload | protoReflect | protoProject | specMetadata | specApply =>
    simp only at h
    split at h
    · rename_i inh k1 fs' k2 hi hfs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .extend (heval .full i (.record inh) k1 hi)
        (evalClairvoyantFields_sound (heval .full) fs fs' k2 hfs)
    · cases h

/-- Executable check for `t = skipped` (`.hole 0 []`). -/
def isSkipped : Term → Bool
  | .hole 0 [] => true
  | _ => false

theorem isSkipped_sound {t : Term} (h : isSkipped t = true) : t = skipped := by
  cases t with
  | hole n args =>
    cases n with
    | zero =>
      cases args with
      | nil => rfl
      | cons _ _ => cases h
    | succ _ => cases h
  | _ => cases h

theorem not_skipped_of_isSkipped_false {t : Term} (h : isSkipped t = false) : t ≠ skipped := by
  intro heq
  subst heq
  cases h

/-- Settle the template of a `fix` body (`Run .head`). -/
def evalClairvoyantHead (eval : Term → Option (Term × Nat)) (fuel : Nat) (t : Term) :
    Option (Term × Nat) :=
  match t with
  | .record fs =>
    if isCValue (.record fs) then
      some (.record fs, 0)
    else
      some (.record fs, 1)
  | .extend i fs =>
    match fuel with
    | 0 => eval (.extend i fs)
    | n + 1 =>
      match evalClairvoyantHead eval n i with
      | some (.record inh, k) => some (.record (extendFields inh fs), k + 1)
      | _ => eval (.extend i fs)
  | .app f a =>
    match fuel with
    | 0 => eval (.app f a)
    | n + 1 =>
      match eval f with
      | some (.lam b, k1) =>
        let bx := evalClairvoyantBind eval a
        match evalClairvoyantHead eval n (instantiate b bx.1) with
        | some (v, k3) => some (v, k1 + bx.2 + k3 + 1)
        | none => eval (.app f a)
      | _ => eval (.app f a)
  | _ => eval t
termination_by fuel

theorem evalClairvoyantHead_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) :
    ∀ (fuel : Nat) (t T : Term) (k : Nat),
      evalClairvoyantHead eval fuel t = some (T, k) → Run .head t T k
  | fuel, t, T, k, h => by
    unfold evalClairvoyantHead at h
    split at h
    · rename_i fs
      split at h
      · rename_i hcv
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .headEval (.value (isCValue_sound (.record fs) hcv))
      · rename_i hncv
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .headRecord (not_cvalue_of_isCValue_false (by simpa using hncv))
    · rename_i i fs
      split at h
      · exact .headEval (heval _ T k h)
      · rename_i n
        split at h
        · rename_i inh k1 hi
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .headExtend (evalClairvoyantHead_sound heval n i (.record inh) k1 hi)
        · exact .headEval (heval _ T k h)
    · rename_i f a
      split at h
      · exact .headEval (heval _ T k h)
      · rename_i n
        split at h
        · rename_i b k1 hf
          dsimp only at h
          split at h
          · rename_i v k3 hbody
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .apply (heval f (.lam b) k1 hf)
              (evalClairvoyantBind_sound heval a)
              (evalClairvoyantHead_sound heval n _ v k3 hbody)
          · exact .headEval (heval _ T k h)
        · exact .headEval (heval _ T k h)
    · exact .headEval (heval t T k h)
termination_by fuel => fuel

/-- Evaluate one cell of a knot wave (`Run .cell`). -/
def evalClairvoyantCell (eval : Term → Option (Term × Nat)) (shouldEval : Bool)
    (t S p : Term) : Option (Term × Nat) :=
  let tSub := t.substitute (single S)
  if isSettled tSub then
    some (tSub, 0)
  else if isSkipped p then
    if shouldEval then
      match eval tSub with
      | some (v, k) => some (v, k + 1)
      | none => some (skipped, 0)
    else
      some (skipped, 0)
  else if isSettled p then
    some (p, 0)
  else
    none

theorem evalClairvoyantCell_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (shouldEval : Bool) (t S p p' : Term) (k : Nat)
    (h : evalClairvoyantCell eval shouldEval t S p = some (p', k)) :
    Run .cell (.app (.app t S) p) p' k := by
  unfold evalClairvoyantCell at h
  dsimp only at h
  split at h
  · rename_i hset
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .cellValue (isSettled_sound _ hset)
  · rename_i hnset
    have hnot_sub : ¬ Settled (t.substitute (single S)) :=
      not_settled_of_isSettled_false (by simpa using hnset)
    split at h
    · rename_i hskip
      have hp_eq : p = skipped := isSkipped_sound hskip
      subst hp_eq
      split at h
      · split at h
        · rename_i v kv hev
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .cellEval hnot_sub (heval _ v kv hev)
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .cellWait hnot_sub
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .cellWait hnot_sub
    · rename_i hnskip
      have hp_ne : p ≠ skipped := not_skipped_of_isSkipped_false (by simpa using hnskip)
      split at h
      · rename_i hsetp
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .cellKeep hnot_sub (isSettled_sound p hsetp) hp_ne
      · cases h

def shouldEvalField (optTarget : Option String) (n : String) : Bool :=
  match optTarget with
  | some target => n == target
  | none => true

/-- Evaluate one wave across all record fields (`Run .wave`). -/
def evalClairvoyantWave (eval : Term → Option (Term × Nat)) (optTarget : Option String)
    (S : Term) : List (String × Term) → List (String × Term) → Option (List (String × Term) × Nat)
  | [], [] => some ([], 0)
  | (n, t) :: fs, (n', p) :: ps =>
    if n == n' then
      match evalClairvoyantCell eval (shouldEvalField optTarget n) t S p,
            evalClairvoyantWave eval optTarget S fs ps with
      | some (p', k1), some (ps', k2) => some ((n, p') :: ps', k1 + k2)
      | _, _ => none
    else
      none
  | _, _ => none

theorem evalClairvoyantWave_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (optTarget : Option String) (S : Term) :
    ∀ (fs ps ps' : List (String × Term)) (k : Nat),
      evalClairvoyantWave eval optTarget S fs ps = some (ps', k) →
      Run .wave (.app (.app (.record fs) S) (.record ps)) (.record ps') k
  | [], [], ps', k, h => by
    simp only [evalClairvoyantWave, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .waveNil
  | (n, t) :: fs, (n', p) :: ps, ps', k, h => by
    unfold evalClairvoyantWave at h
    split at h
    · rename_i hname
      have hn : n' = n := (beq_iff_eq.1 hname).symm
      subst hn
      split at h
      · rename_i p' k1 ps_rest k2 hcell hwave
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .waveCons
          (evalClairvoyantCell_sound heval _ t S p p' k1 hcell)
          (evalClairvoyantWave_sound heval optTarget S fs ps ps_rest k2 hwave)
      · cases h
    · cases h
  | [], _ :: _, _, _, h => by simp [evalClairvoyantWave] at h
  | _ :: _, [], _, _, h => by simp [evalClairvoyantWave] at h

def isFieldResolved (ps : List (String × Term)) (target : String) : Bool :=
  match ps.find? (fun f => f.1 == target) with
  | some (_, p) => !isSkipped p
  | none => true

def isWaveComplete (optTarget : Option String) (ps : List (String × Term)) : Bool :=
  match optTarget with
  | some target => isFieldResolved ps target
  | none => ps.all (fun f => !isSkipped f.2)

/-- Step one wave: if `optTarget = some target`, first try evaluating only `target`; if `target`
is still `skipped` (because it depends on another `self` field), fall back to `optTarget = none`. -/
def evalClairvoyantStepWave (eval : Term → Option (Term × Nat)) (optTarget : Option String)
    (S : Term) (fs ps : List (String × Term)) : Option (List (String × Term) × Nat) :=
  match optTarget with
  | some target =>
    match evalClairvoyantWave eval (some target) S fs ps with
    | some (ps', k) =>
      if isFieldResolved ps' target then
        some (ps', k)
      else
        evalClairvoyantWave eval none S fs ps
    | none => evalClairvoyantWave eval none S fs ps
  | none => evalClairvoyantWave eval none S fs ps

theorem evalClairvoyantStepWave_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (optTarget : Option String) (S : Term) (fs ps ps' : List (String × Term)) (k : Nat)
    (h : evalClairvoyantStepWave eval optTarget S fs ps = some (ps', k)) :
    Run .wave (.app (.app (.record fs) S) (.record ps)) (.record ps') k := by
  unfold evalClairvoyantStepWave at h
  cases optTarget with
  | none => exact evalClairvoyantWave_sound heval none S fs ps ps' k h
  | some target =>
    simp only at h
    split at h
    · rename_i ps1 k1 hw1
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact evalClairvoyantWave_sound heval (some target) S fs ps ps1 k1 hw1
      · exact evalClairvoyantWave_sound heval none S fs ps ps' k h
    · exact evalClairvoyantWave_sound heval none S fs ps ps' k h

/-- Run subsequent knot waves (`Run.knotWave` / `Run.knotDone`). -/
def evalClairvoyantKnotWaves (eval : Term → Option (Term × Nat)) (optTarget : Option String) :
    Nat → List (String × Term) → List (String × Term) → Option (Term × Nat)
  | 0, _, ps =>
    if isCValue (.record ps) then some (.record ps, 0) else none
  | w + 1, fs, ps =>
    if isWaveComplete optTarget ps && isCValue (.record ps) then
      some (.record ps, 0)
    else
      match evalClairvoyantStepWave eval optTarget (.record ps) fs ps with
      | some (ps', k1) =>
        match evalClairvoyantKnotWaves eval optTarget w fs ps' with
        | some (V, k2) => some (V, k1 + k2)
        | none => if isCValue (.record ps) then some (.record ps, 0) else none
      | none =>
        if isCValue (.record ps) then some (.record ps, 0) else none

theorem evalClairvoyantKnotWaves_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (optTarget : Option String) :
    ∀ (waves : Nat) (fs ps : List (String × Term)) (V : Term) (k : Nat),
      evalClairvoyantKnotWaves eval optTarget waves fs ps = some (V, k) →
      Run .knot (.app (.record fs) (.record ps)) V k
  | 0, _, ps, V, k, h => by
    unfold evalClairvoyantKnotWaves at h
    split at h
    · rename_i hcv
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .knotDone (isCValue_sound (.record ps) hcv)
    · cases h
  | w + 1, fs, ps, V, k, h => by
    unfold evalClairvoyantKnotWaves at h
    split at h
    · rename_i hdone
      rw [Bool.and_eq_true] at hdone
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .knotDone (isCValue_sound (.record ps) hdone.2)
    · split at h
      · rename_i ps' k1 hwave
        have hrun_wave := evalClairvoyantStepWave_sound heval optTarget (.record ps) fs ps ps' k1 hwave
        split at h
        · rename_i V' k2 hrest
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .knotWave hrun_wave (evalClairvoyantKnotWaves_sound heval optTarget w fs ps' V' k2 hrest)
        · split at h
          · rename_i hcv
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .knotDone (isCValue_sound (.record ps) hcv)
          · cases h
      · split at h
        · rename_i hcv
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .knotDone (isCValue_sound (.record ps) hcv)
        · cases h

/-- Evaluate a knot from `skipped` (`Run .knot (.app T skipped) V k`). -/
def evalClairvoyantKnot (eval : Term → Option (Term × Nat)) (optTarget : Option String)
    (waves : Nat) (T : Term) : Option (Term × Nat) :=
  if isCValue T then
    let P := T.substitute (single skipped)
    if isCValue P then
      some (P, 0)
    else
      none
  else
    match T with
    | .record fs =>
      let pend := fs.map fun f => (f.1, skipped)
      match evalClairvoyantStepWave eval optTarget skipped fs pend with
      | some (ps1, k1) =>
        match evalClairvoyantKnotWaves eval optTarget waves fs ps1 with
        | some (V, k2) => some (V, k1 + k2)
        | none => none
      | none => none
    | _ => none

theorem evalClairvoyantKnot_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (optTarget : Option String) (waves : Nat) (T V : Term) (k : Nat)
    (h : evalClairvoyantKnot eval optTarget waves T = some (V, k)) :
    Run .knot (.app T skipped) V k := by
  unfold evalClairvoyantKnot at h
  split at h
  · rename_i hcvT
    dsimp only at h
    split at h
    · rename_i hcvP
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .knotUnroll (isCValue_sound T hcvT) (.knotDone (isCValue_sound _ hcvP))
    · cases h
  · cases T with
    | record fs =>
      dsimp only at h
      split at h
      · rename_i ps1 k1 hwave1
        split at h
        · rename_i V' k2 hwaves
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hw1 : Run .wave (.app (.app (.record fs) skipped) (pending fs)) (.record ps1) k1 :=
            evalClairvoyantStepWave_sound heval optTarget skipped fs
              (fs.map fun (f : String × Term) => (f.1, skipped)) ps1 k1 hwave1
          exact .knotFirst hw1 (evalClairvoyantKnotWaves_sound heval optTarget waves fs ps1 V' k2 hwaves)
        · cases h
      · cases h
    | bound _ | hole _ _ | label _ | lam _ | app _ _ | mix _ _ | fix _ _
    | specification _ _ | prototype _ _ | project _ | reflect _ | metadata _
    | get _ _ | extend _ _ | nat _ | binary _ _ _ | ifZero _ _ _ | inject _ _
    | case _ _ | boolean _ | ifBool _ _ _ | done _ | perform _ | split _ _ => cases h

def hintTargetField : DemandHint → Option String
  | .fieldOnly name => some name
  | _ => none

/-- Demand-hinted fuel-bounded clairvoyant oracle evaluator (`evalClairvoyantWithHint`). -/
def evalClairvoyantWithHint (hint : DemandHint) (fuel : Nat) (t : Term) : Option (Term × Nat) :=
  if isCValue t then
    some (t, 0)
  else
    match fuel with
    | 0 => none
    | n + 1 =>
      match t with
      | .app f a =>
        match evalClairvoyantWithHint .full n f with
        | some (.lam b, k1) =>
          let letBranch :=
            if isSettled a then
              match evalClairvoyantWithHint hint n (instantiate b a) with
              | some (v, k3) => some (v, k1 + 0 + k3 + 1)
              | none => none
            else
              match evalClairvoyantWithHint .full n a with
              | some (va, ka) =>
                match evalClairvoyantWithHint hint n (instantiate b va) with
                | some (v, k3) => some (v, k1 + (ka + 1) + k3 + 1)
                | none => none
              | none => none
          let skipBranch :=
            match evalClairvoyantWithHint hint n (instantiate b skipped) with
            | some (v, k3) => some (v, k1 + 1 + k3 + 1)
            | none => none
          pickMinCost letBranch skipBranch
        | some (.specification _ e, k1) =>
          let fullSpecBranch :=
            match evalClairvoyantWithHint hint n (.app e a) with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          let skipMetaBranch :=
            match evalClairvoyantWithHint .specApply n f with
            | some (.specification _ e', k1') =>
              match evalClairvoyantWithHint hint n (.app e' a) with
              | some (v, k2) => some (v, k1' + k2 + 1)
              | none => none
            | _ => none
          pickMinCost fullSpecBranch skipMetaBranch
        | _ => none
      | .mix l u => some (mixBody l u, 1)
      | .fix s i =>
        match evalClairvoyantHead (evalClairvoyantWithHint .full n) n (selfBody s i) with
        | some (T, k1) =>
          match evalClairvoyantKnot (evalClairvoyantWithHint .full n) (hintTargetField hint) n T with
          | some (V, k2) => some (V, k1 + k2 + 1)
          | none => none
        | none => none
      | .specification m e =>
        let (m', k1) := bindForSpecM (evalClairvoyantWithHint .full n) hint m
        let (e', k2) := bindForSpecE (evalClairvoyantWithHint .full n) hint e
        some (.specification m' e', k1 + k2 + 1)
      | .prototype s g =>
        let (s', k1) := bindForProtoS (evalClairvoyantWithHint .full n) hint s
        let (g', k2) := bindForProtoG (evalClairvoyantWithHint .full n) hint g
        some (.prototype s' g', k1 + k2 + 1)
      | .project p =>
        let projBranch :=
          match evalClairvoyantWithHint .protoProject n p with
          | some (.prototype _ g, k1) =>
            match evalClairvoyantWithHint hint n g with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          | _ => none
        let fullBranch :=
          match evalClairvoyantWithHint .full n p with
          | some (.prototype _ g, k1) =>
            match evalClairvoyantWithHint hint n g with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          | _ => none
        pickMinCost projBranch fullBranch
      | .reflect p =>
        let reflBranch :=
          match evalClairvoyantWithHint .protoReflect n p with
          | some (.prototype s _, k1) =>
            match evalClairvoyantWithHint hint n s with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          | _ => none
        let fullBranch :=
          match evalClairvoyantWithHint .full n p with
          | some (.prototype s _, k1) =>
            match evalClairvoyantWithHint hint n s with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          | _ => none
        pickMinCost reflBranch fullBranch
      | .metadata p =>
        let metaBranch :=
          match evalClairvoyantWithHint .specMetadata n p with
          | some (.specification me _, k1) =>
            match evalClairvoyantWithHint hint n me with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          | _ => none
        let fullBranch :=
          match evalClairvoyantWithHint .full n p with
          | some (.specification me _, k1) =>
            match evalClairvoyantWithHint hint n me with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          | _ => none
        pickMinCost metaBranch fullBranch
      | .record fs =>
        match evalRecordForHint (evalClairvoyantWithHint .full n) hint fs with
        | some (fs', k) => some (.record fs', k + 1)
        | none => none
      | .get g name =>
        let focusedBranch :=
          match evalClairvoyantWithHint (.fieldOnly name) n g with
          | some (.record fs, k1) =>
            match fs.find? (fun f => f.1 == name) with
            | some (_, x) =>
              match evalClairvoyantWithHint hint n x with
              | some (v, k2) => some (v, k1 + k2 + 1)
              | none => none
            | none => none
          | _ => none
        let fullBranch :=
          match evalClairvoyantWithHint .full n g with
          | some (.record fs, k1) =>
            match fs.find? (fun f => f.1 == name) with
            | some (_, x) =>
              match evalClairvoyantWithHint hint n x with
              | some (v, k2) => some (v, k1 + k2 + 1)
              | none => none
            | none => none
          | _ => none
        pickMinCost focusedBranch fullBranch
      | .extend i fs =>
        evalExtendForHint (fun dh => evalClairvoyantWithHint dh n) hint i fs
      | .binary op l r =>
        match evalClairvoyantWithHint .full n l, evalClairvoyantWithHint .full n r with
        | some (lv, k1), some (rv, k2) =>
          match primitiveResult op lv rv with
          | some res => some (res, k1 + k2 + 1)
          | none => none
        | _, _ => none
      | .ifZero c z s =>
        match evalClairvoyantWithHint .full n c with
        | some (.nat 0, k1) =>
          match evalClairvoyantWithHint hint n z with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | some (.nat (m + 1), k1) =>
          match evalClairvoyantWithHint hint n (instantiate s (.nat m)) with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | _ => none
      | .inject l p =>
        let (p', kp) := bindForInjectP (evalClairvoyantWithHint .full n) hint p
        some (.inject l p', kp + 1)
      | .case sc arms =>
        let stdBranch :=
          match evalClairvoyantWithHint .full n sc with
          | some (.inject l p, k1) =>
            match arms.find? (fun a => a.1 == l) with
            | some (_, body) =>
              match evalClairvoyantWithHint hint n (instantiate body p) with
              | some (v, k2) => some (v, k1 + k2 + 1)
              | none => none
            | none => none
          | _ => none
        let skipScBranch :=
          match evalClairvoyantWithHint .skipInjectPayload n sc with
          | some (.inject l p, k1) =>
            match arms.find? (fun a => a.1 == l) with
            | some (_, body) =>
              match evalClairvoyantWithHint hint n (instantiate body p) with
              | some (v, k2) => some (v, k1 + k2 + 1)
              | none => none
            | none => none
          | _ => none
        pickMinCost stdBranch skipScBranch
      | .ifBool c x y =>
        match evalClairvoyantWithHint .full n c with
        | some (.boolean true, k1) =>
          match evalClairvoyantWithHint hint n x with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | some (.boolean false, k1) =>
          match evalClairvoyantWithHint hint n y with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | _ => none
      | .done x =>
        match evalClairvoyantWithHint hint n x with
        | some (v, k) => some (v, k + 1)
        | none => none
      | _ => none
termination_by fuel

/-- Executable fuel-bounded clairvoyant oracle evaluator (`evalClairvoyantMinCost`).
At `.app f a`, computes both the `Let′`/`keep` branch and the `Skip` branch (replacing
an unused argument with `skipped` at cost `1`), and picks the minimum-cost derivation.
Also propagates demand hints across `.get`, `.case`, `.project`, `.reflect`, `.metadata`,
and executes two-stage wave evaluation for `.fix`. -/
def evalClairvoyantMinCost (fuel : Nat) (t : Term) : Option (Term × Nat) :=
  evalClairvoyantWithHint .full fuel t

theorem evalClairvoyantWithHint_sound : ∀ (fuel : Nat) (hint : DemandHint) (t v : Term) (k : Nat),
    evalClairvoyantWithHint hint fuel t = some (v, k) → CV t v k
  | fuel, hint, t, v, k, h => by
    unfold evalClairvoyantWithHint at h
    split at h
    · rename_i hcv
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .value (isCValue_sound t hcv)
    · rename_i hncv
      have hnotcv : ¬ CValue t := fun hc => hncv hc.isCValue_eq_true
      cases fuel with
      | zero => simp at h
      | succ n =>
        simp only at h
        have ih := evalClairvoyantWithHint_sound n
        split at h
        · -- .app f a
          rename_i f a
          split at h
          · rename_i b k1 hf
            have hrunf : CV f (.lam b) k1 := ih .full f (.lam b) k1 hf
            refine pickMinCost_sound ?_ ?_ h
            · intro v1 k_let hlet
              split at hlet
              · rename_i hsa
                split at hlet
                · rename_i v3 k3 hbody
                  simp only [Option.some.injEq, Prod.mk.injEq] at hlet
                  obtain ⟨rfl, rfl⟩ := hlet
                  exact .apply hrunf (.keep (isSettled_sound a hsa)) (ih hint _ v3 k3 hbody)
                · cases hlet
              · rename_i hnsa
                have hnot_sa : ¬ Settled a := fun hs => hnsa hs.isSettled_eq_true
                split at hlet
                · rename_i va ka ha
                  split at hlet
                  · rename_i v3 k3 hbody
                    simp only [Option.some.injEq, Prod.mk.injEq] at hlet
                    obtain ⟨rfl, rfl⟩ := hlet
                    exact .apply hrunf (.eval hnot_sa (ih .full a va ka ha)) (ih hint _ v3 k3 hbody)
                  · cases hlet
                · cases hlet
            · intro v2 k_skip hskip
              split at hskip
              · rename_i v3 k3 hbody
                simp only [Option.some.injEq, Prod.mk.injEq] at hskip
                obtain ⟨rfl, rfl⟩ := hskip
                exact .apply hrunf (.skip a) (ih hint _ v3 k3 hbody)
              · cases hskip
          · rename_i me e k1 hf
            have hrunf : CV f (.specification me e) k1 := ih .full f (.specification me e) k1 hf
            refine pickMinCost_sound ?_ ?_ h
            · intro v1 k_full hfull
              split at hfull
              · rename_i v2 k2 hbody
                simp only [Option.some.injEq, Prod.mk.injEq] at hfull
                obtain ⟨rfl, rfl⟩ := hfull
                exact .applySpec hrunf (ih hint (.app e a) v2 k2 hbody)
              · cases hfull
            · intro v2 k_skip hskip
              split at hskip
              · rename_i me' e' k1' hf'
                split at hskip
                · rename_i v3 k2 hbody
                  simp only [Option.some.injEq, Prod.mk.injEq] at hskip
                  obtain ⟨rfl, rfl⟩ := hskip
                  exact .applySpec (ih .specApply f (.specification me' e') k1' hf')
                    (ih hint (.app e' a) v3 k2 hbody)
                · cases hskip
              · cases hskip
          · cases h
        · -- .mix l u
          rename_i l u
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .mix l u
        · -- .fix s i
          rename_i s i
          split at h
          · rename_i T k1 hhead
            split at h
            · rename_i V k2 hknot
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .fix
                (evalClairvoyantHead_sound (ih .full) n (selfBody s i) T k1 hhead)
                (evalClairvoyantKnot_sound (ih .full) (hintTargetField hint) n T V k2 hknot)
            · cases h
          · cases h
        · -- .specification m e
          rename_i m e
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .specification hnotcv
            (bindForSpecM_sound (ih .full) hint m)
            (bindForSpecE_sound (ih .full) hint e)
        · -- .prototype s g
          rename_i s g
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .prototype hnotcv
            (bindForProtoS_sound (ih .full) hint s)
            (bindForProtoG_sound (ih .full) hint g)
        · -- .project p
          rename_i p
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_proj hproj
            split at hproj
            · rename_i s g k1 hp
              split at hproj
              · rename_i v2 k2 hg
                simp only [Option.some.injEq, Prod.mk.injEq] at hproj
                obtain ⟨rfl, rfl⟩ := hproj
                exact .project (ih .protoProject p (.prototype s g) k1 hp) (ih hint g v2 k2 hg)
              · cases hproj
            · cases hproj
          · intro v2 k_full hfull
            split at hfull
            · rename_i s g k1 hp
              split at hfull
              · rename_i v3 k2 hg
                simp only [Option.some.injEq, Prod.mk.injEq] at hfull
                obtain ⟨rfl, rfl⟩ := hfull
                exact .project (ih .full p (.prototype s g) k1 hp) (ih hint g v3 k2 hg)
              · cases hfull
            · cases hfull
        · -- .reflect p
          rename_i p
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_refl hrefl
            split at hrefl
            · rename_i s g k1 hp
              split at hrefl
              · rename_i v2 k2 hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hrefl
                obtain ⟨rfl, rfl⟩ := hrefl
                exact .reflect (ih .protoReflect p (.prototype s g) k1 hp) (ih hint s v2 k2 hs)
              · cases hrefl
            · cases hrefl
          · intro v2 k_full hfull
            split at hfull
            · rename_i s g k1 hp
              split at hfull
              · rename_i v3 k2 hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hfull
                obtain ⟨rfl, rfl⟩ := hfull
                exact .reflect (ih .full p (.prototype s g) k1 hp) (ih hint s v3 k2 hs)
              · cases hfull
            · cases hfull
        · -- .metadata p
          rename_i p
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_meta hmeta
            split at hmeta
            · rename_i me e k1 hp
              split at hmeta
              · rename_i v2 k2 hm
                simp only [Option.some.injEq, Prod.mk.injEq] at hmeta
                obtain ⟨rfl, rfl⟩ := hmeta
                exact .metadata (ih .specMetadata p (.specification me e) k1 hp) (ih hint me v2 k2 hm)
              · cases hmeta
            · cases hmeta
          · intro v2 k_full hfull
            split at hfull
            · rename_i me e k1 hp
              split at hfull
              · rename_i v3 k2 hm
                simp only [Option.some.injEq, Prod.mk.injEq] at hfull
                obtain ⟨rfl, rfl⟩ := hfull
                exact .metadata (ih .full p (.specification me e) k1 hp) (ih hint me v3 k2 hm)
              · cases hfull
            · cases hfull
        · -- .record fs
          rename_i fs
          split at h
          · rename_i fs' kf hfs
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .record hnotcv (evalRecordForHint_sound (ih .full) hint fs fs' kf hfs)
          · cases h
        · -- .get g name
          rename_i g name
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_foc hfoc
            split at hfoc
            · rename_i fs k1 hg
              split at hfoc
              · rename_i f_name x hfind
                have hname : f_name = name := by
                  have := List.find?_some hfind
                  simpa using this
                subst hname
                split at hfoc
                · rename_i v2 k2 hx
                  simp only [Option.some.injEq, Prod.mk.injEq] at hfoc
                  obtain ⟨rfl, rfl⟩ := hfoc
                  exact .get (ih (.fieldOnly f_name) g (.record fs) k1 hg) hfind (ih hint x v2 k2 hx)
                · cases hfoc
              · cases hfoc
            · cases hfoc
          · intro v2 k_full hfull
            split at hfull
            · rename_i fs k1 hg
              split at hfull
              · rename_i f_name x hfind
                have hname : f_name = name := by
                  have := List.find?_some hfind
                  simpa using this
                subst hname
                split at hfull
                · rename_i v3 k2 hx
                  simp only [Option.some.injEq, Prod.mk.injEq] at hfull
                  obtain ⟨rfl, rfl⟩ := hfull
                  exact .get (ih .full g (.record fs) k1 hg) hfind (ih hint x v3 k2 hx)
                · cases hfull
              · cases hfull
            · cases hfull
        · -- .extend i fs
          rename_i i fs
          exact evalExtendForHint_sound ih hint i fs v k h
        · -- .binary op l r
          rename_i op l r
          split at h
          · rename_i lv k1 rv k2 hl hr
            split at h
            · rename_i res hprim
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .binary (ih .full l lv k1 hl) (ih .full r rv k2 hr) hprim
            · cases h
          · cases h
        · -- .ifZero c z s
          rename_i c z s
          split at h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hz
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .zero (ih .full c (.nat 0) k1 hc) (ih hint z v2 k2 hz)
            · cases h
          · rename_i m k1 hc
            split at h
            · rename_i v2 k2 hs
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .succ (ih .full c (.nat (m + 1)) k1 hc) (ih hint (instantiate s (.nat m)) v2 k2 hs)
            · cases h
          · cases h
        · -- .inject l p
          rename_i l p
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .inject hnotcv (bindForInjectP_sound (ih .full) hint p)
        · -- .case sc arms
          rename_i sc arms
          refine pickMinCost_sound ?_ ?_ h
          · intro v1 k_std hstd
            split at hstd
            · rename_i l p k1 hsc
              split at hstd
              · rename_i arm_l body hfind
                have hl : arm_l = l := by
                  have := List.find?_some hfind
                  simpa using this
                subst hl
                split at hstd
                · rename_i v2 k2 hbody
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstd
                  obtain ⟨rfl, rfl⟩ := hstd
                  exact .case (ih .full sc (.inject arm_l p) k1 hsc) hfind
                    (ih hint (instantiate body p) v2 k2 hbody)
                · cases hstd
              · cases hstd
            · cases hstd
          · intro v2 k_skip hskip
            split at hskip
            · rename_i l p k1 hsc
              split at hskip
              · rename_i arm_l body hfind
                have hl : arm_l = l := by
                  have := List.find?_some hfind
                  simpa using this
                subst hl
                split at hskip
                · rename_i v3 k2 hbody
                  simp only [Option.some.injEq, Prod.mk.injEq] at hskip
                  obtain ⟨rfl, rfl⟩ := hskip
                  exact .case (ih .skipInjectPayload sc (.inject arm_l p) k1 hsc) hfind
                    (ih hint (instantiate body p) v3 k2 hbody)
                · cases hskip
              · cases hskip
            · cases hskip
        · -- .ifBool c x y
          rename_i c x y
          split at h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hx
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .ifTrue (ih .full c (.boolean true) k1 hc) (ih hint x v2 k2 hx)
            · cases h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hy
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .ifFalse (ih .full c (.boolean false) k1 hc) (ih hint y v2 k2 hy)
            · cases h
          · cases h
        · -- .done x
          rename_i x
          split at h
          · rename_i v2 k2 hx
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .done (ih hint x v2 k2 hx)
          · cases h
        · cases h

/-- Soundness of `evalClairvoyantMinCost`: every result `some (v, k)` is backed by a
clairvoyant derivation `CV t v k` (`Run .eval t v k`). -/
theorem evalClairvoyantMinCost_sound (fuel : Nat) (t v : Term) (k : Nat)
    (h : evalClairvoyantMinCost fuel t = some (v, k)) : CV t v k :=
  evalClairvoyantWithHint_sound fuel .full t v k h

/-- Soundness of `evalClairvoyantMinCost` on closed values (`CValue v`): returns `some (v, 0)`
at any fuel budget, backed by `CV v v 0`. -/
theorem evalClairvoyantMinCost_value_sound {v : Term} (hv : CValue v) (fuel : Nat) :
    evalClairvoyantMinCost fuel v = some (v, 0) ∧ CV v v 0 := by
  refine ⟨?_, .value hv⟩
  unfold evalClairvoyantMinCost evalClairvoyantWithHint
  simp [hv.isCValue_eq_true]

/-- Soundness of `evalClairvoyantMinCost` on β-redexes where the `Skip` branch succeeds:
if `evalClairvoyantMinCost fuel (instantiate b skipped) = some (v, k3)`, then
`evalClairvoyantMinCost (fuel + 1) (.app (.lam b) a)` succeeds with some `(v', k')`
satisfying `k' ≤ k3 + 2` and `CV (.app (.lam b) a) v' k'`. -/
theorem evalClairvoyantMinCost_skip_app_sound (b a v : Term) (k3 fuel : Nat)
    (hskip : evalClairvoyantMinCost fuel (instantiate b skipped) = some (v, k3)) :
    ∃ v' k', evalClairvoyantMinCost (fuel + 1) (.app (.lam b) a) = some (v', k') ∧
      k' ≤ k3 + 2 ∧ CV (.app (.lam b) a) v' k' := by
  have hncv : isCValue (.app (.lam b) a) = false := isCValue_app (.lam b) a
  have hlam : evalClairvoyantWithHint .full fuel (.lam b) = some (.lam b, 0) :=
    (evalClairvoyantMinCost_value_sound (.lam b) fuel).1
  have hskip' : evalClairvoyantWithHint .full fuel (instantiate b skipped) = some (v, k3) := hskip
  obtain ⟨v', k', hpick, hle⟩ :=
    pickMinCost_le_right (o1 :=
      if isSettled a then
        match evalClairvoyantWithHint .full fuel (instantiate b a) with
        | some (v, k3) => some (v, 0 + 0 + k3 + 1)
        | none => none
      else
        match evalClairvoyantWithHint .full fuel a with
        | some (va, ka) =>
          match evalClairvoyantWithHint .full fuel (instantiate b va) with
          | some (v, k3) => some (v, 0 + (ka + 1) + k3 + 1)
          | none => none
        | none => none)
      (v2 := v) (k2 := 0 + 1 + k3 + 1)
  have heval : evalClairvoyantMinCost (fuel + 1) (.app (.lam b) a) = some (v', k') := by
    unfold evalClairvoyantMinCost evalClairvoyantWithHint
    simp only [hncv, Bool.false_eq_true, ite_false, hlam, hskip']
    exact hpick
  exact ⟨v', k', heval, by omega, evalClairvoyantMinCost_sound (fuel + 1) _ v' k' heval⟩

/-- For any constant function `λ x => .nat n` applied to any argument `a`, the `Skip`
derivation in `Run .eval` achieves cost `2` (`1` for `Skip` + `1` for β). -/
theorem cv_skip_const_app (n : Nat) (a : Term) :
    CV (.app (.lam (.nat n)) a) (.nat n) 2 := by
  have hbody : instantiate (.nat n) skipped = .nat n := by
    simp [instantiate, Term.substitute]
  have := Run.apply (Run.value (.lam (.nat n))) (Run.skip a) (by rw [hbody]; exact Run.value (.nat n))
  simpa using this

/-- **`evalClairvoyant_skip_unused_arg_saves_cost`**: For the constant function `λ x => .nat 42`
applied to any expensive or non-settled argument `a` (`¬ Settled a`), `Run .eval` achieves cost `2`
via `Skip`, and `evalClairvoyantMinCost (fuel + 1) (.app (.lam (.nat 42)) a)` returns
`some (.nat 42, 2)` regardless of the complexity or divergence of `a`. -/
theorem evalClairvoyant_skip_unused_arg_saves_cost (a : Term) (ha : ¬ Settled a) (fuel : Nat) :
    evalClairvoyantMinCost (fuel + 1) (.app (.lam (.nat 42)) a) = some (.nat 42, 2) ∧
      CV (.app (.lam (.nat 42)) a) (.nat 42) 2 := by
  refine ⟨?_, cv_skip_const_app 42 a⟩
  have hnsa : isSettled a = false := by
    cases h : isSettled a with
    | false => rfl
    | true => exact absurd (isSettled_sound a h) ha
  have hncv : isCValue (.app (.lam (.nat 42)) a) = false := isCValue_app (.lam (.nat 42)) a
  have hlam : evalClairvoyantWithHint .full fuel (.lam (.nat 42)) = some (.lam (.nat 42), 0) :=
    (evalClairvoyantMinCost_value_sound (.lam (.nat 42)) fuel).1
  have hinst : ∀ x, instantiate (.nat 42) x = .nat 42 := fun x => by
    simp [instantiate, Term.substitute]
  have hnat : evalClairvoyantWithHint .full fuel (.nat 42) = some (.nat 42, 0) :=
    (evalClairvoyantMinCost_value_sound (.nat 42) fuel).1
  conv => lhs; unfold evalClairvoyantMinCost evalClairvoyantWithHint
  simp only [hncv, Bool.false_eq_true, ite_false, hlam, hnsa, hinst, hnat]
  cases evalClairvoyantWithHint .full fuel a with
  | none => rfl
  | some r =>
    obtain ⟨va, ka⟩ := r
    simp only [pickMinCost]
    split
    · rename_i hle
      have hka : ka = 0 := by omega
      subst hka
      rfl
    · rfl

/-- Eager Call-By-Value binding (`Let′` / `keep`, never `Skip`). -/
def evalCBVBind (eval : Term → Option (Term × Nat)) (t : Term) : Option (Term × Nat) :=
  if isSettled t then
    some (t, 0)
  else
    match eval t with
    | some (vt, kt) => some (vt, kt + 1)
    | none => none

theorem evalCBVBind_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k)
    (t t' : Term) (k : Nat) (h : evalCBVBind eval t = some (t', k)) :
    Run .bind t t' k := by
  unfold evalCBVBind at h
  split at h
  · rename_i hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .keep (isSettled_sound t hs)
  · rename_i hns
    have hnot : ¬ Settled t := fun hs => hns hs.isSettled_eq_true
    split at h
    · rename_i vt kt ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .eval hnot (heval t vt kt ht)
    · cases h

/-- Eager Call-By-Value record field evaluation (`Run .fields` without `Skip`). -/
def evalCBVFields (eval : Term → Option (Term × Nat)) :
    List (String × Term) → Option (List (String × Term) × Nat)
  | [] => some ([], 0)
  | (name, field) :: rest =>
    match evalCBVBind eval field, evalCBVFields eval rest with
    | some (field', k1), some (rest', k2) => some ((name, field') :: rest', k1 + k2 + 1)
    | _, _ => none

theorem evalCBVFields_sound {eval : Term → Option (Term × Nat)}
    (heval : ∀ t v k, eval t = some (v, k) → CV t v k) :
    ∀ (fs fs' : List (String × Term)) (k : Nat),
      evalCBVFields eval fs = some (fs', k) →
      Run .fields (.record fs) (.record fs') k
  | [], fs', k, h => by
    simp only [evalCBVFields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil
  | (name, field) :: rest, fs', k, h => by
    unfold evalCBVFields at h
    split at h
    · rename_i field' k1 rest' k2 hf hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .cons (evalCBVBind_sound heval field field' k1 hf)
        (evalCBVFields_sound heval rest rest' k2 hr)
    · cases h

/-- Executable fuel-bounded Call-By-Value evaluator (`evalCBV`): evaluates arguments and fields
eagerly (`Let′` / `keep`) and never uses `Skip`. -/
def evalCBV (fuel : Nat) (t : Term) : Option (Term × Nat) :=
  if isCValue t then
    some (t, 0)
  else
    match fuel with
    | 0 => none
    | n + 1 =>
      match t with
      | .app f a =>
        match evalCBV n f with
        | some (.lam b, k1) =>
          if isSettled a then
            match evalCBV n (instantiate b a) with
            | some (v, k3) => some (v, k1 + 0 + k3 + 1)
            | none => none
          else
            match evalCBV n a with
            | some (va, ka) =>
              match evalCBV n (instantiate b va) with
              | some (v, k3) => some (v, k1 + (ka + 1) + k3 + 1)
              | none => none
            | none => none
        | some (.specification _ e, k1) =>
          match evalCBV n (.app e a) with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | _ => none
      | .mix l u => some (mixBody l u, 1)
      | .specification m e =>
        match evalCBVBind (evalCBV n) m, evalCBVBind (evalCBV n) e with
        | some (m', k1), some (e', k2) => some (.specification m' e', k1 + k2 + 1)
        | _, _ => none
      | .prototype s g =>
        match evalCBVBind (evalCBV n) s, evalCBVBind (evalCBV n) g with
        | some (s', k1), some (g', k2) => some (.prototype s' g', k1 + k2 + 1)
        | _, _ => none
      | .project p =>
        match evalCBV n p with
        | some (.prototype _ g, k1) =>
          match evalCBV n g with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | _ => none
      | .reflect p =>
        match evalCBV n p with
        | some (.prototype s _, k1) =>
          match evalCBV n s with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | _ => none
      | .metadata p =>
        match evalCBV n p with
        | some (.specification me _, k1) =>
          match evalCBV n me with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | _ => none
      | .record fs =>
        match evalCBVFields (evalCBV n) fs with
        | some (fs', k) => some (.record fs', k + 1)
        | none => none
      | .get g name =>
        match evalCBV n g with
        | some (.record fs, k1) =>
          match fs.find? (fun f => f.1 == name) with
          | some (_, x) =>
            match evalCBV n x with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          | none => none
        | _ => none
      | .extend i fs =>
        match evalCBV n i, evalCBVFields (evalCBV n) fs with
        | some (.record inh, k1), some (fs', k2) =>
          some (.record (extendFields inh fs'), k1 + k2 + 1)
        | _, _ => none
      | .binary op l r =>
        match evalCBV n l, evalCBV n r with
        | some (lv, k1), some (rv, k2) =>
          match primitiveResult op lv rv with
          | some res => some (res, k1 + k2 + 1)
          | none => none
        | _, _ => none
      | .ifZero c z s =>
        match evalCBV n c with
        | some (.nat 0, k1) =>
          match evalCBV n z with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | some (.nat (m + 1), k1) =>
          match evalCBV n (instantiate s (.nat m)) with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | _ => none
      | .inject l p =>
        if isSettled p then
          some (.inject l p, 0 + 1)
        else
          match evalCBV n p with
          | some (vp, kp) => some (.inject l vp, (kp + 1) + 1)
          | none => none
      | .case sc arms =>
        match evalCBV n sc with
        | some (.inject l p, k1) =>
          match arms.find? (fun a => a.1 == l) with
          | some (_, body) =>
            match evalCBV n (instantiate body p) with
            | some (v, k2) => some (v, k1 + k2 + 1)
            | none => none
          | none => none
        | _ => none
      | .ifBool c x y =>
        match evalCBV n c with
        | some (.boolean true, k1) =>
          match evalCBV n x with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | some (.boolean false, k1) =>
          match evalCBV n y with
          | some (v, k2) => some (v, k1 + k2 + 1)
          | none => none
        | _ => none
      | .done x =>
        match evalCBV n x with
        | some (v, k) => some (v, k + 1)
        | none => none
      | _ => none

theorem evalCBV_sound : ∀ (fuel : Nat) (t v : Term) (k : Nat),
    evalCBV fuel t = some (v, k) → CV t v k
  | fuel, t, v, k, h => by
    unfold evalCBV at h
    split at h
    · rename_i hcv
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .value (isCValue_sound t hcv)
    · rename_i hncv
      have hnotcv : ¬ CValue t := fun hc => hncv hc.isCValue_eq_true
      cases fuel with
      | zero => simp at h
      | succ n =>
        simp only at h
        have ih := evalCBV_sound n
        split at h
        · rename_i f a
          split at h
          · rename_i b k1 hf
            have hrunf : CV f (.lam b) k1 := ih f (.lam b) k1 hf
            split at h
            · rename_i hsa
              split at h
              · rename_i v3 k3 hbody
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .apply hrunf (.keep (isSettled_sound a hsa)) (ih _ v3 k3 hbody)
              · cases h
            · rename_i hnsa
              have hnot_sa : ¬ Settled a := fun hs => hnsa hs.isSettled_eq_true
              split at h
              · rename_i va ka ha
                split at h
                · rename_i v3 k3 hbody
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact .apply hrunf (.eval hnot_sa (ih a va ka ha)) (ih _ v3 k3 hbody)
                · cases h
              · cases h
          · rename_i me e k1 hf
            split at h
            · rename_i v2 k2 hbody
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .applySpec (ih f (.specification me e) k1 hf) (ih (.app e a) v2 k2 hbody)
            · cases h
          · cases h
        · rename_i l u
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .mix l u
        · rename_i m e
          split at h
          · rename_i m' k1 e' k2 hm he
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .specification hnotcv (evalCBVBind_sound ih m m' k1 hm) (evalCBVBind_sound ih e e' k2 he)
          · cases h
        · rename_i s g
          split at h
          · rename_i s' k1 g' k2 hs hg
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .prototype hnotcv (evalCBVBind_sound ih s s' k1 hs) (evalCBVBind_sound ih g g' k2 hg)
          · cases h
        · rename_i p
          split at h
          · rename_i s g k1 hp
            split at h
            · rename_i v2 k2 hg
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .project (ih p (.prototype s g) k1 hp) (ih g v2 k2 hg)
            · cases h
          · cases h
        · rename_i p
          split at h
          · rename_i s g k1 hp
            split at h
            · rename_i v2 k2 hs
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .reflect (ih p (.prototype s g) k1 hp) (ih s v2 k2 hs)
            · cases h
          · cases h
        · rename_i p
          split at h
          · rename_i me e k1 hp
            split at h
            · rename_i v2 k2 hm
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .metadata (ih p (.specification me e) k1 hp) (ih me v2 k2 hm)
            · cases h
          · cases h
        · rename_i fs
          split at h
          · rename_i fs' kf hfs
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .record hnotcv (evalCBVFields_sound ih fs fs' kf hfs)
          · cases h
        · rename_i g name
          split at h
          · rename_i fs k1 hg
            split at h
            · rename_i f_name x hfind
              have hname : f_name = name := by
                have := List.find?_some hfind
                simpa using this
              subst hname
              split at h
              · rename_i v2 k2 hx
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .get (ih g (.record fs) k1 hg) hfind (ih x v2 k2 hx)
              · cases h
            · cases h
          · cases h
        · rename_i i fs
          split at h
          · rename_i inh k1 fs' k2 hi hfs
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .extend (ih i (.record inh) k1 hi) (evalCBVFields_sound ih fs fs' k2 hfs)
          · cases h
        · rename_i op l r
          split at h
          · rename_i lv k1 rv k2 hl hr
            split at h
            · rename_i res hprim
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .binary (ih l lv k1 hl) (ih r rv k2 hr) hprim
            · cases h
          · cases h
        · rename_i c z s
          split at h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hz
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .zero (ih c (.nat 0) k1 hc) (ih z v2 k2 hz)
            · cases h
          · rename_i m k1 hc
            split at h
            · rename_i v2 k2 hs
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .succ (ih c (.nat (m + 1)) k1 hc) (ih (instantiate s (.nat m)) v2 k2 hs)
            · cases h
          · cases h
        · rename_i l p
          split at h
          · rename_i hsp
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .inject hnotcv (.keep (isSettled_sound p hsp))
          · rename_i hnsp
            have hnot_sp : ¬ Settled p := fun hs => hnsp hs.isSettled_eq_true
            split at h
            · rename_i vp kp hp
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .inject hnotcv (.eval hnot_sp (ih p vp kp hp))
            · cases h
        · rename_i sc arms
          split at h
          · rename_i l p k1 hsc
            split at h
            · rename_i arm_l body hfind
              have hl : arm_l = l := by
                have := List.find?_some hfind
                simpa using this
              subst hl
              split at h
              · rename_i v2 k2 hbody
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .case (ih sc (.inject arm_l p) k1 hsc) hfind (ih (instantiate body p) v2 k2 hbody)
              · cases h
            · cases h
          · cases h
        · rename_i c x y
          split at h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hx
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .ifTrue (ih c (.boolean true) k1 hc) (ih x v2 k2 hx)
            · cases h
          · rename_i k1 hc
            split at h
            · rename_i v2 k2 hy
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .ifFalse (ih c (.boolean false) k1 hc) (ih y v2 k2 hy)
            · cases h
          · cases h
        · rename_i x
          split at h
          · rename_i v2 k2 hx
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .done (ih x v2 k2 hx)
          · cases h
        · cases h

/-! ## Dead-`let` Elimination in Prototype Methods (`clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper`) -/

/-- A dead `let` binding `let _ := deadExpr in body` in `Core4`: the bound variable `.bound 0`
does not occur in `body.rename Nat.succ`. -/
def deadLetBind (deadExpr body : Term) : Term :=
  .app (.lam (body.rename Nat.succ)) deadExpr

theorem instantiate_deadLet_body (body arg : Term) :
    instantiate (body.rename Nat.succ) arg = body := by
  rw [instantiate_eq, shift_one_cancel]

/-- In `Core4`'s reference reduction, `deadLetBind deadExpr body` steps in 1 β-step to `body`. -/
theorem steps_deadLetBind (deadExpr body : Term) :
    Steps (deadLetBind deadExpr body) body := by
  unfold deadLetBind
  have hstep : Step (.app (.lam (body.rename Nat.succ)) deadExpr)
      (instantiate (body.rename Nat.succ) deadExpr) :=
    Step.beta (body.rename Nat.succ) deadExpr
  rw [instantiate_deadLet_body] at hstep
  exact steps_one hstep

/-- `deadLetBind deadExpr body` is `Ahead` of `body`, both at the top level and under method binders. -/
theorem ahead_deadLetBind (deadExpr body : Term) :
    Ahead (deadLetBind deadExpr body) body ∧
    Ahead (.lam (deadLetBind deadExpr body)) (.lam body) :=
  ⟨Ahead.ofStepsRefl (steps_deadLetBind deadExpr body),
   .lam (Ahead.ofStepsRefl (steps_deadLetBind deadExpr body))⟩

/-- Eliminating a dead `let` binding preserves `Core4` behavioral equivalence (`≈b`),
both for the body and for the enclosing prototype method closure `.lam (...)`. -/
theorem bEquiv_deadLetBind (deadExpr body : Term) :
    (deadLetBind deadExpr body ≈b body) ∧
    (.lam (deadLetBind deadExpr body) ≈b .lam body) :=
  ⟨bequiv_of_ahead (ahead_deadLetBind deadExpr body).1,
   bequiv_of_ahead (ahead_deadLetBind deadExpr body).2⟩

/-- Any Clairvoyant derivation `CV body v k` lifts via `Run.skip deadExpr` to a derivation
`CV (deadLetBind deadExpr body) v (k + 2)` at cost `k + 2`. -/
theorem cv_deadLetBind_of_cv (deadExpr : Term) {body v : Term} {k : Nat}
    (h : CV body v k) :
    CV (deadLetBind deadExpr body) v (k + 2) := by
  unfold deadLetBind
  have hbody : CV (instantiate (body.rename Nat.succ) skipped) v k := by
    rwa [instantiate_deadLet_body]
  have happ := Run.apply (Run.value (.lam (body.rename Nat.succ))) (Run.skip deadExpr) hbody
  have heq : 0 + 1 + k + 1 = k + 2 := by omega
  rwa [heq] at happ

/-- Conversely, every Clairvoyant derivation `CV (deadLetBind deadExpr body) v k_unpruned`
induces a strictly cheaper derivation `CV body v k_pruned` with `k_pruned < k_unpruned`
(and `k_pruned + 2 ≤ k_unpruned` whenever `¬ Settled deadExpr`). -/
theorem cv_of_cv_deadLetBind {deadExpr body v : Term} {k_unpruned : Nat}
    (h : CV (deadLetBind deadExpr body) v k_unpruned) :
    ∃ k_pruned, CV body v k_pruned ∧
      k_pruned < k_unpruned ∧
      (¬ Settled deadExpr → k_pruned + 2 ≤ k_unpruned) := by
  unfold deadLetBind at h
  cases h with
  | value hv => exact absurd hv app_not_ready
  | applySpec hf _ =>
    obtain ⟨heq, _⟩ := cv_lam hf
    cases heq
  | @apply _ _ _ b x _ k1 k2 k3 hf hb hbody =>
    obtain ⟨hb_eq, rfl⟩ := cv_lam hf
    simp only [Term.lam.injEq] at hb_eq
    subst hb_eq
    rw [instantiate_deadLet_body] at hbody
    refine ⟨k3, hbody, by omega, fun hns => ?_⟩
    rcases bind_of_unsettled hns hb with ⟨_, rfl⟩ | ⟨j, _, rfl⟩
    · omega
    · omega

/-- **`clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper`**:
Eliminating a dead `let` binding in a `Core4` prototype method (`deadLetBind deadExpr body → body`):
1. Preserves behavioral equivalence (`deadLetBind deadExpr body ≈b body` and `.lam (deadLetBind deadExpr body) ≈b .lam body`),
2. Preserves all ground halting observations (`Halts (deadLetBind deadExpr body) o ↔ Halts body o`),
3. Strictly reduces Clairvoyant heap/step cost on every terminating derivation (`k_pruned < k_unpruned`,
   and saves at least `2` steps whenever `¬ Settled deadExpr`),
4. Evaluates in `evalClairvoyantMinCost` at cost `0` after elimination vs cost `2` before elimination
   on `deadLetBind (.binary .add (.nat 10) (.nat 20)) (.nat 42)`. -/
theorem clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper (deadExpr body : Term) :
    (deadLetBind deadExpr body ≈b body) ∧
    (.lam (deadLetBind deadExpr body) ≈b .lam body) ∧
    (∀ o : Observation, Halts (deadLetBind deadExpr body) o ↔ Halts body o) ∧
    (∀ v k, CV body v k → CV (deadLetBind deadExpr body) v (k + 2) ∧ k < k + 2) ∧
    (∀ v k_unpruned, CV (deadLetBind deadExpr body) v k_unpruned →
      ∃ k_pruned, CV body v k_pruned ∧ k_pruned < k_unpruned ∧
        (¬ Settled deadExpr → k_pruned + 2 ≤ k_unpruned)) ∧
    evalClairvoyantMinCost 2 (deadLetBind (.binary .add (.nat 10) (.nat 20)) (.nat 42)) =
      some (.nat 42, 2) ∧
    evalClairvoyantMinCost 2 (.nat 42) = some (.nat 42, 0) := by
  have hbeq := bEquiv_deadLetBind deadExpr body
  have hns : ¬ Settled (.binary .add (.nat 10) (.nat 20)) := by
    intro h; cases h with | value hv => cases hv
  have hev1 : evalClairvoyantMinCost 2 (deadLetBind (.binary .add (.nat 10) (.nat 20)) (.nat 42)) =
      some (.nat 42, 2) := by
    simpa [deadLetBind, Term.rename] using
      (evalClairvoyant_skip_unused_arg_saves_cost (.binary .add (.nat 10) (.nat 20)) hns 1).1
  have hev2 : evalClairvoyantMinCost 2 (.nat 42) = some (.nat 42, 0) :=
    (evalClairvoyantMinCost_value_sound (.nat 42) 2).1
  exact ⟨hbeq.1, hbeq.2, fun o => hbeq.1.sameRuns.halts o,
    fun v k hcv => ⟨cv_deadLetBind_of_cv deadExpr hcv, by omega⟩,
    fun v k_unpruned hcv => cv_of_cv_deadLetBind hcv,
    hev1, hev2⟩

/-- Mutated `deadLetBind` that returns `deadExpr` instead of `body`, breaking dead-let elimination soundness. -/
def deadLetBindBroken (deadExpr _body : Term) : Term := deadExpr

#tooth Obend.Equiv.clairvoyant_dead_let_elim_bEquiv_and_strictly_cheaper by mutation
  Obend.Equiv.deadLetBind := deadLetBindBroken

end Obend.Equiv
end

