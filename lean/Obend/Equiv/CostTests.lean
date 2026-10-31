module
/- Faré's tests and the objects that read `self`, costed by the two-stage demand semantics.

- `keep(7, y)` costs 3 for every `y`, divergent or not: the argument is skipped (`keep_cost`).
- `{good = 7, bad = self.bad}.good` costs 5 (`good_cost`): the template once (3), the knot and the
  selection; `.bad` has no derivation (`bad_field_no_cv`, from `selfObject_loop_no_cv`): it reads
  itself, is stuck in every wave, and stays `skipped`, as need blackholes it.
- `{a = 7, b = self.a}.b` costs 7 (`self_field_cost`): `b` is evaluated in the second wave, reading
  `a` from the first. Under Hackett and Hutton's `Let′` at `fix` it had no derivation (the retired
  `self_field_no_cv`); the reference semantics and the machine both give 7.
- A knot is entered at cost 3 (`knot_unfold`).
That these costs are the least is `Obend.Equiv.Demand.measured_least`. -/
public import Obend.Equiv.Cost
public import Obend.Equiv.FareTests
public import Obend.Core.Machine
@[expose] public section
namespace Obend.Equiv.CostTests
open Obend.Core.Term
open Obend.Equiv
open Obend.Equiv.FareTests (keep object goodBad loop)
open Obend.Core.TermTraverse (rename_substitute substitute_comp substitute_rename rename_comp)
set_option autoImplicit false

/-! ## Knots -/

theorem knot_body (V : Term) :
    ((((V.rename shiftSelf).rename (liftRename (liftRename Nat.succ))).substitute
      (liftSubstitution (single (.bound 0)))).substitute (single (.record []))) = V := by
  rw [rename_comp, rename_substitute, substitute_comp]
  conv => rhs; rw [← substitute_bound V]
  congr 1; funext i
  cases i with
  | zero => simp [shiftSelf, liftRename, liftSubstitution, single, Term.rename, Term.substitute]
  | succ n => simp [shiftSelf, liftRename, liftSubstitution, single, Term.rename, Term.substitute]

theorem record_nil_settled : Settled (.record []) := .value (.record (fs := []) (by simp))

theorem cv_beta_value {W x : Term} (hx : Settled x) (hv : CValue (instantiate W x)) :
    CV (.app (.lam W) x) (instantiate W x) 1 := by
  have := Run.apply (Run.value (.lam W)) (Run.keep hx) (Run.value hv)
  simpa using this

/-- The body of a knot evaluates to its value, `self` open, in two β steps. -/
theorem knot_selfBody {V : Term} (hV : CValue V) :
    CV (selfBody (.lam (.lam (V.rename shiftSelf))) (.record [])) V 2 := by
  let W1 : Term := (V.rename shiftSelf).rename (liftRename (liftRename Nat.succ))
  have inner : CV (.app (.lam (.lam W1)) (.bound 0)) (instantiate (.lam W1) (.bound 0)) 1 :=
    cv_beta_value (.bound 0) (by rw [instantiate_eq]; simp only [Term.substitute]; exact .lam _)
  have e1 : instantiate (.lam W1) (.bound 0) = .lam (W1.substitute (liftSubstitution (single (.bound 0)))) := by
    rw [instantiate_eq]; simp only [Term.substitute]
  rw [e1] at inner
  have e2 : instantiate (W1.substitute (liftSubstitution (single (.bound 0)))) (.record []) = V := by
    rw [instantiate_eq]; exact knot_body V
  have outer := Run.apply inner (Run.keep record_nil_settled) (by rw [e2]; exact Run.value hV)
  have e3 : selfBody (.lam (.lam (V.rename shiftSelf))) (.record []) =
      .app (.app (.lam (.lam W1)) (.bound 0)) (.record []) := by
    simp [selfBody, Term.rename, W1]
  rw [e3]; simpa using outer

/-- Entering a knot costs 3: its body settles to the value, which is a template already, and is
read once against `skipped`. -/
theorem knot_unfold {V : Term} (hV : CValue V) :
    CV (knot V) (V.substitute (single skipped)) 3 := by
  have hS : CValue (V.substitute (single skipped)) := Ready.substitute hV (settled_single .skipped)
  exact Run.fix (.headEval (knot_selfBody hV)) (.knotUnroll hV (.knotDone hS))

/-- and, read against its own first approximant, unrolls once more at no further cost. -/
theorem knot_unfold_twice {V : Term} (hV : CValue V) :
    CV (knot V) (V.substitute (single (V.substitute (single skipped)))) 3 := by
  have hS : CValue (V.substitute (single skipped)) := Ready.substitute hV (settled_single .skipped)
  have hS2 := Ready.substitute hV (settled_single hS.settled)
  exact Run.fix (.headEval (knot_selfBody hV)) (.knotUnroll hV (.knotUnroll hV (.knotDone hS2)))

/-! ## Faré's first test -/

/-- `keep(7, y)` costs 3 for every `y`: the argument is skipped. -/
theorem keep_cost (y : Term) : CV (.app (.app keep (.nat 7)) y) (.nat 7) 3 := by
  have e : instantiate (.lam (.bound 1)) (.nat 7) = .lam (.nat 7) := by
    simp [instantiate, Term.substitute, liftSubstitution, Term.rename]
  have inner : CV (.app keep (.nat 7)) (.lam (.nat 7)) 1 := by
    have := cv_beta_value (W := .lam (.bound 1)) (.value (.nat 7)) (by rw [e]; exact .lam _)
    rw [e] at this; exact this
  have e2 : instantiate (.nat 7) skipped = .nat 7 := by simp [instantiate, Term.substitute]
  have := Run.apply inner (Run.skip y) (by rw [e2]; exact Run.value (.nat 7))
  simpa using this

theorem keep_loop_cost : CV (.app (.app keep (.nat 7)) loop) (.nat 7) 3 := keep_cost loop

/-! ## Objects whose second field reads `self` -/

/-- `λself. λsuper. {n1 = 7, n2 = self.m}`. -/
def selfLam (n1 n2 m : String) : Term := .lam (.lam (.record [(n1, .nat 7), (n2, .get (.bound 1) m)]))

/-- `fix (λself. λsuper. {n1 = 7, n2 = self.m}) {}`. -/
def selfObject (n1 n2 m : String) : Term := .fix (selfLam n1 n2 m) (.record [])

/-- Its template: the record with `self` open. -/
def selfTemplate (n1 n2 m : String) : Term := .record [(n1, .nat 7), (n2, .get (.bound 0) m)]

theorem object_eq : object = selfObject "good" "bad" "bad" := rfl

theorem selfObject_selfBody (n1 n2 m : String) :
    selfBody (selfLam n1 n2 m) (.record []) = .app (.app (selfLam n1 n2 m) (.bound 0)) (.record []) := by
  simp [selfBody, selfLam, Term.rename, liftRename]

theorem selfObject_inner (n1 n2 m : String) (x : Term) :
    instantiate (.lam (.record [(n1, .nat 7), (n2, .get (.bound 1) m)])) x =
      .lam (.record [(n1, .nat 7), (n2, .get (x.rename .succ) m)]) := by
  simp [instantiate, Term.substitute, liftSubstitution]

theorem selfObject_outer (n1 n2 m : String) (x y : Term) :
    instantiate (.record [(n1, .nat 7), (n2, .get (x.rename .succ) m)]) y =
      .record [(n1, .nat 7), (n2, .get x m)] := by
  rw [instantiate_eq]
  simp only [Term.substitute, List.map_cons, List.map_nil, shift_one_cancel]

theorem get_not_settled {g : Term} {n : String} : ¬ Settled (.get g n) := by
  intro h; cases h with | value h => cases h

theorem selfTemplate_not_value (n1 n2 m : String) : ¬ CValue (selfTemplate n1 n2 m) := by
  intro h
  exact get_not_settled (record_value_fields h (n2, .get (.bound 0) m) (by simp [selfTemplate]))

/-- The template settles once, at cost 3: two β steps and the head record. -/
theorem selfObject_head (n1 n2 m : String) :
    Run .head (selfBody (selfLam n1 n2 m) (.record [])) (selfTemplate n1 n2 m) 3 := by
  have inner := cv_beta_value (W := .lam (.record [(n1, .nat 7), (n2, .get (.bound 1) m)]))
    (.bound 0) (by rw [selfObject_inner]; exact .lam _)
  rw [selfObject_inner] at inner
  have h3 : Run .head (instantiate (.record [(n1, .nat 7), (n2, .get ((Term.bound 0).rename .succ) m)])
      (.record [])) (selfTemplate n1 n2 m) 1 := by
    rw [selfObject_outer]; exact .headRecord (selfTemplate_not_value n1 n2 m)
  rw [selfObject_selfBody]
  exact Run.apply inner (Run.keep record_nil_settled) h3

theorem cell_nat (n : Nat) (S p : Term) : Run .cell (.app (.app (.nat n) S) p) (.nat n) 0 := by
  have := Run.cellValue (t := .nat n) (S := S) (p := p) (by simp only [Term.substitute]; exact .value (.nat n))
  simpa only [Term.substitute] using this

theorem cell_get_wait (g S : Term) (n : String) :
    Run .cell (.app (.app (.get g n) S) skipped) skipped 0 :=
  .cellWait (by simp only [Term.substitute]; exact get_not_settled)

/-- The first wave: the constant field is known, the field reading `self` waits. -/
theorem selfObject_first_wave (n1 n2 m : String) :
    Run .wave (.app (.app (selfTemplate n1 n2 m) skipped) (pending [(n1, .nat 7), (n2, .get (.bound 0) m)]))
      (.record [(n1, .nat 7), (n2, skipped)]) 0 := by
  have := Run.waveCons (n := n1) (cell_nat 7 skipped skipped)
    (Run.waveCons (n := n2) (cell_get_wait (.bound 0) skipped m) Run.waveNil)
  simpa [selfTemplate, pending] using this

/-! ## Faré's second test, and the field that reads a sibling -/

theorem first_approx_value (n1 n2 : String) : CValue (.record [(n1, .nat 7), (n2, skipped)]) := by
  refine .record ?_
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact .value (.nat 7)
  · exact .skipped

/-- The object settles at cost 4 with only its constant field known. -/
theorem selfObject_first (n1 n2 m : String) :
    CV (selfObject n1 n2 m) (.record [(n1, .nat 7), (n2, skipped)]) 4 :=
  Run.fix (selfObject_head n1 n2 m) (.knotFirst (selfObject_first_wave n1 n2 m) (.knotDone (first_approx_value n1 n2)))

/-- **Faré's second test, costed**: `{good = 7, bad = self.bad}.good` costs 5. -/
theorem good_cost : CV (.get object "good") (.nat 7) 5 :=
  Run.get (selfObject_first "good" "bad" "bad") (by simp) (Run.value (.nat 7))

/-- The second wave of `{a = 7, b = self.a}`: `b` reads `a` from the first approximant (cost 2). -/
theorem selfField_second_wave :
    Run .wave (.app (.app (selfTemplate "a" "b" "a") (.record [("a", .nat 7), ("b", skipped)]))
      (.record [("a", .nat 7), ("b", skipped)])) (.record [("a", .nat 7), ("b", .nat 7)]) 2 := by
  have get : CV (.get (.record [("a", .nat 7), ("b", skipped)]) "a") (.nat 7) 1 :=
    Run.get (Run.value (first_approx_value "a" "b")) (by simp) (Run.value (.nat 7))
  have cellB : Run .cell (.app (.app (.get (.bound 0) "a") (.record [("a", .nat 7), ("b", skipped)])) skipped)
      (.nat 7) 2 := by
    have := Run.cellEval (t := .get (.bound 0) "a") (S := .record [("a", .nat 7), ("b", skipped)])
      (by simp only [Term.substitute, single]; exact get_not_settled)
      (by simp only [Term.substitute, single]; exact get)
    simpa using this
  have := Run.waveCons (n := "a") (cell_nat 7 (.record [("a", .nat 7), ("b", skipped)]) (.nat 7))
    (Run.waveCons (n := "b") cellB Run.waveNil)
  simpa [selfTemplate] using this

/-- `{a = 7, b = self.a}`. -/
abbrev selfField : Term := selfObject "a" "b" "a"

theorem selfField_value : CV selfField (.record [("a", .nat 7), ("b", .nat 7)]) 6 := by
  have done : CValue (.record [("a", .nat 7), ("b", .nat 7)]) := by
    refine .record ?_
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact .value (.nat 7)
  exact Run.fix (selfObject_head "a" "b" "a")
    (.knotFirst (selfObject_first_wave "a" "b" "a") (.knotWave selfField_second_wave (.knotDone done)))

/-- **The field that reads a sibling through `self` has a derivation**: `{a = 7, b = self.a}.b`
evaluates to 7 at cost 7, the template settled once (3), `b` evaluated in the second wave (2), the
knot (1) and the selection (1). This is the derivation Hackett and Hutton's `Let′` at `fix` lacks. -/
theorem self_field_cost : CV (.get selfField "b") (.nat 7) 7 :=
  Run.get selfField_value (by simp) (Run.value (.nat 7))

/-! ## The field that reads itself has none -/

/-- The approximants of `{n1 = 7, n2 = self.n2}`: nothing is known of `n2`. -/
def LoopApprox (n1 n2 : String) (S : Term) : Prop := S = skipped ∨ ∃ g, S = .record [(n1, g), (n2, skipped)]

theorem loop_record_eval {n1 n2 : String} {g w : Term} {k : Nat}
    (h : CV (.record [(n1, g), (n2, skipped)]) w k) : ∃ g', w = .record [(n1, g'), (n2, skipped)] := by
  cases h with
  | value _ => exact ⟨g, rfl⟩
  | record _ hf =>
    cases hf with
    | cons _ hr =>
      cases hr with
      | cons hb hn =>
        cases hn
        rcases bind_of_settled .skipped hb with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact ⟨_, rfl⟩

theorem loop_get_stuck {n1 n2 : String} (ne : n1 ≠ n2) {S v : Term} {k : Nat} (hS : LoopApprox n1 n2 S) :
    ¬ CV (.get S n2) v k := by
  intro h
  cases h with
  | value h0 => cases h0
  | get h1 hit h2 =>
    rcases hS with rfl | ⟨g, rfl⟩
    · exact cv_skipped_false h1
    · obtain ⟨g', e⟩ := loop_record_eval h1
      cases e
      have miss : (n1 == n2) = false := by simpa using ne
      simp [List.find?, miss] at hit
      obtain ⟨_, rfl⟩ := hit
      exact cv_skipped_false h2

/-- What the template's `n2` can be: the selection from `self` (open or skipped), or `skipped`. -/
def LoopField (n2 : String) (t : Term) : Prop :=
  t = skipped ∨ ∃ x, (x = .bound 0 ∨ x = skipped) ∧ t = .get x n2

theorem loop_cell {n1 n2 : String} (ne : n1 ≠ n2) {t S q : Term} {k : Nat} (ht : LoopField n2 t)
    (hS : LoopApprox n1 n2 S) (h : Run .cell (.app (.app t S) skipped) q k) : q = skipped := by
  have sub : t.substitute (single S) = skipped ∨ ∃ y, LoopApprox n1 n2 y ∧ t.substitute (single S) = .get y n2 := by
    rcases ht with rfl | ⟨x, hx, rfl⟩
    · exact .inl (substitute_skipped _)
    · rcases hx with rfl | rfl
      · exact .inr ⟨S, hS, by simp [Term.substitute, single]⟩
      · exact .inr ⟨skipped, .inl rfl, by simp [Term.substitute, substitute_skipped]⟩
  cases h with
  | cellValue hset =>
    rcases sub with e | ⟨y, _, e⟩
    · exact e
    · rw [e] at hset; exact absurd hset get_not_settled
  | cellKeep _ _ hne => exact absurd rfl hne
  | cellWait _ => rfl
  | cellEval hn e =>
    rcases sub with e2 | ⟨y, hy, e2⟩
    · rw [e2] at hn; exact absurd .skipped hn
    · rw [e2] at e; exact absurd e (loop_get_stuck ne hy)

theorem loop_wave {n1 n2 : String} (ne : n1 ≠ n2) {t1 t2 S p1 P : Term} {k : Nat} (ht : LoopField n2 t2)
    (hS : LoopApprox n1 n2 S)
    (h : Run .wave (.app (.app (.record [(n1, t1), (n2, t2)]) S) (.record [(n1, p1), (n2, skipped)])) P k) :
    ∃ g, P = .record [(n1, g), (n2, skipped)] := by
  cases h with
  | waveCons _ hw =>
    cases hw with
    | waveCons hc hn =>
      cases hn
      rw [loop_cell ne ht hS hc]
      exact ⟨_, rfl⟩

/-- The templates of `{n1 = 7, n2 = self.n2}`. -/
def LoopTemplate (n1 n2 : String) (T : Term) : Prop := ∃ t1 t2, T = .record [(n1, t1), (n2, t2)] ∧ LoopField n2 t2

theorem loop_knot_aux {n1 n2 : String} (ne : n1 ≠ n2) {mo : Mode} {a V : Term} {k : Nat} (h : Run mo a V k) :
    mo = .knot → ∀ {T S : Term}, a = .app T S → LoopTemplate n1 n2 T → LoopApprox n1 n2 S →
      ∃ g, V = .record [(n1, g), (n2, skipped)] := by
  induction h with
  | knotDone hP =>
    intro _ T S e _ hS
    cases e
    rcases hS with rfl | ⟨g, rfl⟩
    · exact absurd hP skipped_not_value
    · exact ⟨g, rfl⟩
  | knotFirst hw _ _ ihk =>
    intro _ T S e hT _
    cases e
    obtain ⟨t1, t2, e, ht⟩ := hT
    cases e
    have hw' := hw
    simp only [pending, List.map_cons, List.map_nil] at hw'
    obtain ⟨g, rfl⟩ := loop_wave ne ht (.inl rfl) hw'
    exact ihk rfl rfl ⟨t1, t2, rfl, ht⟩ (.inr ⟨g, rfl⟩)
  | knotWave hw _ _ ihk =>
    intro _ T S e hT hS
    cases e
    obtain ⟨t1, t2, e, ht⟩ := hT
    cases e
    rcases hS with e | ⟨g0, e⟩
    · cases e
    · cases e
      obtain ⟨g, rfl⟩ := loop_wave ne ht (.inr ⟨g0, rfl⟩) hw
      exact ihk rfl rfl ⟨t1, t2, rfl, ht⟩ (.inr ⟨g, rfl⟩)
  | @knotUnroll T0 S0 V0 k0 hT0 _ ihk =>
    intro _ T S e hT hS
    injection e with e1 e2
    subst e1 e2
    obtain ⟨t1, t2, rfl, ht⟩ := hT
    have h2 : Settled t2 := record_value_fields hT0 (n2, t2) (by simp)
    have e2 : t2 = skipped := by
      rcases ht with e | ⟨x, _, rfl⟩
      · exact e
      · exact absurd h2 get_not_settled
    subst e2
    refine ihk rfl rfl ⟨t1, skipped, rfl, ht⟩ (.inr ⟨t1.substitute (single S0), ?_⟩)
    simp [Term.substitute, substitute_skipped]
  | _ => intro hm; cases hm

theorem loop_inner_head {n1 n2 : String} {x T : Term} {k : Nat} (hx : x = .bound 0 ∨ x = skipped)
    (h : Run .head (.record [(n1, .nat 7), (n2, .get x n2)]) T k) : LoopTemplate n1 n2 T := by
  have stuck : ∀ w j, ¬ CV x w j := by
    rcases hx with rfl | rfl
    · exact fun _ _ => cv_bound_false
    · exact fun _ _ => cv_skipped_false
  cases h with
  | headRecord _ => exact ⟨_, _, rfl, .inr ⟨x, hx, rfl⟩⟩
  | headEval h =>
    cases h with
    | value h0 =>
      exact absurd (record_value_fields h0 (n2, .get x n2) (by simp)) get_not_settled
    | record _ hf =>
      cases hf with
      | cons _ hr =>
        cases hr with
        | cons hb hn =>
          cases hn
          rcases bind_of_unsettled get_not_settled hb with ⟨rfl, _⟩ | ⟨j, e, _⟩
          · exact ⟨_, _, rfl, .inl rfl⟩
          · cases e with
            | value h0 => cases h0
            | get e1 _ _ => exact absurd e1 (stuck _ _)

theorem loop_lam_value {n1 n2 : String} {y b : Term} {k : Nat}
    (h : CV (.app (selfLam n1 n2 n2) y) (.lam b) k) :
    ∃ x, Run .bind y x (k - 1) ∧ b = .record [(n1, .nat 7), (n2, .get (x.rename .succ) n2)] := by
  cases h with
  | apply ha hb hc =>
    obtain ⟨e, rfl⟩ := cv_lam ha
    cases e
    rw [selfObject_inner] at hc
    obtain ⟨e, rfl⟩ := cv_lam hc
    cases e
    exact ⟨_, by simpa using hb, rfl⟩
  | applySpec ha _ => obtain ⟨e, _⟩ := cv_lam ha; cases e

theorem loop_head {n1 n2 : String} {T : Term} {k : Nat}
    (h : Run .head (selfBody (selfLam n1 n2 n2) (.record [])) T k) : LoopTemplate n1 n2 T := by
  rw [selfObject_selfBody] at h
  have selfArg : ∀ {x j}, Run .bind (.bound 0) x j → x = .bound 0 ∨ x = skipped := by
    intro x j hb
    rcases bind_of_settled (.bound 0) hb with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact .inl rfl
    · exact .inr rfl
  cases h with
  | headEval h =>
    cases h with
    | value h0 => exact absurd h0 app_not_ready
    | applySpec h1 _ =>
      cases h1 with
      | apply ha _ hc =>
        obtain ⟨e, _⟩ := cv_lam ha; cases e
        rw [selfObject_inner] at hc; obtain ⟨e, _⟩ := cv_lam hc; cases e
      | applySpec ha _ => obtain ⟨e, _⟩ := cv_lam ha; cases e
    | apply h1 _ h3 =>
      obtain ⟨x, hb, rfl⟩ := loop_lam_value h1
      rw [selfObject_outer] at h3
      exact loop_inner_head (selfArg hb) (.headEval h3)
  | apply h1 _ h3 =>
    obtain ⟨x, hb, rfl⟩ := loop_lam_value h1
    rw [selfObject_outer] at h3
    exact loop_inner_head (selfArg hb) h3
  | applySpec h1 _ =>
    cases h1 with
    | apply ha _ hc =>
      obtain ⟨e, _⟩ := cv_lam ha; cases e
      rw [selfObject_inner] at hc; obtain ⟨e, _⟩ := cv_lam hc; cases e
    | applySpec ha _ => obtain ⟨e, _⟩ := cv_lam ha; cases e

/-- **A field that reads itself has no derivation**: `{n1 = 7, n2 = self.n2}.n2` is stuck in every
wave, as need blackholes it. -/
theorem selfObject_loop_no_cv {n1 n2 : String} (ne : n1 ≠ n2) {v : Term} {k : Nat} :
    ¬ CV (.get (selfObject n1 n2 n2) n2) v k := by
  intro h
  cases h with
  | value h0 => cases h0
  | get h1 hit h2 =>
    cases h1 with
    | fix hh hk =>
      obtain ⟨g, e⟩ := loop_knot_aux ne hk rfl rfl (loop_head hh) (.inl rfl)
      cases e
      have miss : (n1 == n2) = false := by simpa using ne
      simp [List.find?, miss] at hit
      obtain ⟨_, rfl⟩ := hit
      exact cv_skipped_false h2

/-- and `.bad` has no derivation: need blackholes it, and the demand semantics agrees. -/
theorem bad_field_no_cv {v : Term} {k : Nat} : ¬ CV (.get object "bad") v k :=
  selfObject_loop_no_cv (by decide)

theorem selfField_steps (name : String) :
    Steps (.get selfField name) (.get (.record [("a", .nat 7), ("b", .get selfField "a")]) name) := by
  have s0 : Step (.get selfField name)
      (.get (.app (.app (.lam (.lam (.record [("a", .nat 7), ("b", .get (.bound 1) "a")]))) selfField)
        (.record [])) name) := .target _ (.fix _ _)
  have s1 := Step.target name (Step.application (.record []) (Step.beta
    (.lam (.record [("a", .nat 7), ("b", .get (.bound 1) "a")])) selfField))
  rw [selfObject_inner] at s1
  have s2 := Step.target name (Step.beta
    (.record [("a", .nat 7), ("b", .get (selfField.rename .succ) "a")]) (.record []))
  rw [selfObject_outer] at s2
  exact .next s0 (.next s1 (.next s2 (.refl _)))

/-- The reference semantics evaluates `{a = 7, b = self.a}.b` to 7. -/
theorem self_field_evaluates : Evaluates (.get selfField "b") (.nat 7) := by
  refine ⟨steps_trans (selfField_steps "b") (.next (.field _ _ (.get selfField "a") (by simp)) ?_), .natural 7⟩
  exact steps_trans (selfField_steps "a") (.next (.field _ _ (.nat 7) (by simp)) (.refl _))

/-! ## `mix_assoc_cost` is not vacuous -/

/-- An extension that ignores `self` and `super`. -/
def constant7 : Term := .lam (.lam (.nat 7))

theorem constant7_app (s : Term) (hs : Settled s) : CV (.app constant7 s) (.lam (.nat 7)) 1 := by
  have e : instantiate (.lam (.nat 7)) s = .lam (.nat 7) := by
    simp [instantiate, Term.substitute]
  have := cv_beta_value (W := .lam (.nat 7)) hs (by rw [e]; exact .lam _)
  rw [e] at this; exact this

/-- `mix (mix a b) constant7` applied to `{}` and `{}` evaluates to 7 (the inner `mix` is
skipped), so the context `(·) {} {}` inhabits `mix_assoc_cost`'s hypothesis. -/
theorem assoc_left_runs (a b : Term) :
    CV (.app (.app (.mix (.mix a b) constant7) (.record [])) (.record [])) (.nat 7) 6 := by
  have body : CV (.app (.app constant7 (.record [])) (.app (.app (.mix a b) (.record [])) (.record [])))
      (.nat 7) 3 := by
    have e : instantiate (.nat 7) skipped = .nat 7 := by simp [instantiate, Term.substitute]
    have := Run.apply (constant7_app _ record_nil_settled)
      (Run.skip (Term.app (.app (.mix a b) (.record [])) (.record []))) (by rw [e]; exact Run.value (.nat 7))
    simpa using this
  have := mk_mix_app_app (Run.keep record_nil_settled) (Run.keep record_nil_settled) body
  simpa using this

/-- and so the other association evaluates to 7 within a factor of 8 (at most 48). -/
theorem assoc_right_runs (a b : Term) :
    ∃ k, CV (.app (.app (.mix a (.mix b constant7)) (.record [])) (.record [])) (.nat 7) k ∧ k ≤ 48 := by
  have h := (mix_assoc_cost a b constant7).1 Term.bound (.app (.app (.bound 0) (.record [])) (.record []))
    (.nat 7) 6 (by simpa [instantiate, Term.substitute, substitute_bound] using assoc_left_runs a b)
  obtain ⟨v', k', r, le, lit⟩ := h
  rw [lit (.nat 7)] at r
  exact ⟨k', by simpa [instantiate, Term.substitute, substitute_bound] using r, by omega⟩

end Obend.Equiv.CostTests
end
