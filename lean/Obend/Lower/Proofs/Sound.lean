module
/-
# Obend.Lower.Proofs.Sound — the lowering preserves what a fragment term computes

**The simulation** (`lower_step`): every source step `s → s'` is matched by Core4 on the lowered
terms in one of two ways.

* A *stutter*: `lowerT s' = lowerT s`. Only δ is a stutter (the lowering inlines definitions), and it
  strictly decreases the source term's size (`sizeOf`): this is the measure that bounds a run of
  stutters, so a source run of `k` steps from `s` has at most `sizeOf s` stutters before each
  non-stuttering step.
* A *positive* run: `lowerT s` takes one or more Core4 steps to a term `m` that is `lowerT s'` with
  some of its subterms run ahead (`Ahead (lowerT s') m`, `Obend.Equiv.Ahead`). β, ζ, the literal
  operations, the eliminators on constructors are matched exactly (`m = lowerT s'`); a step inside the
  major premise of `Nat.rec` is matched after the lowered `fix` has unrolled once (`natRec_unfold`),
  which `Ahead` absorbs: the unrolled `ifZero` is `lowerT s'` run ahead.

**The theorem** (`lower_sound`): a fragment term the source semantics reduces to a canonical form `v`
has a lowered term that evaluates in Core4 to a value related to `lowerT v` by a chain of `Ahead` links
(`AheadChain`), so with the same completed runs (`Obend.Equiv.sameRuns_of_ahead`); for a literal and a
Boolean the value is exactly the lowered one: `Evaluates (lowerT e) (lowerT v)` (`lower_sound_nat`,
`lower_sound_bool`). `lower_value`: canonical forms lower to values.

**Teeth**: a lowering that drops `Nat.rec`'s minor premise (`lowerDropMinor`) and one that maps
`Nat.sub` to `add` (`lowerSubAdd`) each fail the theorem on a two-line program
(`dropMinor_refuted`, `subAdd_refuted`).
-/
public import Obend.Lower.Proofs.Subst
public import Obend.Equiv.Behaviour
@[expose] public section
namespace Obend.Lower
open Obend.Core.Term
open Obend.Core.TermTraverse (rename_comp rename_substitute substitute_rename substitute_comp)
open Obend.Equiv
set_option autoImplicit false

/-! ## Core4 facts -/

theorem positive_steps {a b : Term} (h : PositiveSteps a b) : Steps a b := by
  cases h with | begin s r => exact .next s r

theorem positive_trans {a b c : Term} (h : PositiveSteps a b) (r : Steps b c) : PositiveSteps a c := by
  cases h with | begin s r' => exact .begin s (steps_trans r' r)

theorem positive_of_steps_trans {a b c : Term} (r : Steps a b) (h : PositiveSteps b c) : PositiveSteps a c := by
  cases r with
  | refl => exact h
  | next s r' => exact .begin s (steps_trans r' (positive_steps h))

theorem positive_one {a b : Term} (s : Step a b) : PositiveSteps a b := .begin s (.refl _)

theorem positive_congr {a b : Term} (frame : Term → Term)
    (lift : ∀ {x y : Term}, Step x y → Step (frame x) (frame y)) (h : PositiveSteps a b) :
    PositiveSteps (frame a) (frame b) := by
  cases h with | begin s r => exact .begin (lift s) (steps_congr frame lift r)

/-- An applied lowered `Nat.rec` unrolls in four steps to its `ifZero`. -/
theorem natRec_unfold (Z S K : Term) :
    Steps (.app (.fix (natRecSpec Z S) box) K)
      (.ifZero K Z (.app (.app (S.rename Nat.succ) (.bound 0))
        (.app ((Term.fix (natRecSpec Z S) box).rename Nat.succ) (.bound 0)))) := by
  refine .next (.application _ (.fix _ _)) ?_
  refine .next (.application _ (.application _ (.beta _ _))) ?_
  rw [instantiate_eq]; simp only [Term.substitute]
  refine .next (.application _ (.beta _ _)) ?_
  rw [instantiate_eq]; simp only [Term.substitute]
  refine .next (.beta _ _) ?_
  rw [instantiate_eq]; simp only [Term.substitute]
  simp only [rename_substitute, substitute_comp]
  simp [liftSubstitution, single, Term.rename, Term.substitute, substitute_bound, rename_substitute]
  rw [rename_eq_substitute S, rename_eq_substitute (natRecSpec Z S), rename_eq_substitute box]
  exact .refl _

theorem natRec_unfold_positive (Z S K : Term) :
    PositiveSteps (.app (.fix (natRecSpec Z S) box) K)
      (.ifZero K Z (.app (.app (S.rename Nat.succ) (.bound 0))
        (.app ((Term.fix (natRecSpec Z S) box).rename Nat.succ) (.bound 0)))) := by
  have h := natRec_unfold Z S K
  cases h with
  | next s r => exact .begin s r

theorem natOp_result (op : NatOp) (a b : Nat) :
    primitiveResult op.prim (.nat a) (.nat b) = some (lowerT (op.eval a b)) := by
  cases op <;> simp [NatOp.prim, NatOp.eval, primitiveResult, lowerT]

theorem lowerFields_splitValues (fs : List (String × LExpr)) (names : List String) (values : List LExpr)
    (h : splitValues fs names = some values) :
    splitValues (fs.map fun x => (x.1, lowerT x.2)) names = some (values.map lowerT) := by
  rw [splitValues_map lowerT fs names, h]; rfl

theorem find_lowered {α : Type} (g : α → Term) (fs : List (String × α)) (name : String) (value : α)
    (h : fs.find? (fun field => field.1 == name) = some (name, value)) :
    (fs.map fun x => (x.1, g x.2)).find? (fun field => field.1 == name) = some (name, g value) := by
  rw [find?_map_snd g name fs, h]; rfl

theorem caseArm_open (names : List String) (M P : Term) :
    instantiate (caseArm names M) P = .split P names M := by
  simp only [caseArm, instantiate_eq, Term.substitute, single]
  rw [rename_substitute]
  have : (fun i => single P (Nat.succ i)) = Term.bound := by funext i; rfl
  rw [this, substitute_bound]

/-! ## The simulation -/

theorem ahead_case_target {sc sc' : Term} (arms : List (String × Term)) (h : Ahead sc sc') :
    Ahead (.case sc arms) (.case sc' arms) :=
  .case h rfl (zip_refl (fun a b => Ahead a.2 b.2) arms (fun x _ => Ahead.refl x.2))

/-- **One source step, matched**: a stutter that shrinks the source, or a positive Core4 run to a
term the step's lowering is behind. -/
theorem lower_step {s s' : LExpr} (h : SStep s s') :
    (lowerT s' = lowerT s ∧ sizeOf s' < sizeOf s) ∨
      ∃ m, PositiveSteps (lowerT s) m ∧ Ahead (lowerT s') m := by
  induction h with
  | beta T body argument =>
    simp only [lowerT]
    right; refine ⟨_, positive_one (.beta _ _), ?_⟩
    rw [lowerT_inst]; exact Ahead.refl _
  | appFun a _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right; refine ⟨_, positive_congr (fun x => .app x (lowerT a)) (fun s => .application _ s) pos, ?_⟩
      exact .app ah (Ahead.refl _)
  | zeta T value body =>
    simp only [lowerT]
    right; refine ⟨_, positive_one (.beta _ _), ?_⟩
    rw [lowerT_inst]; exact Ahead.refl _
  | delta name body =>
    simp only [lowerT]
    left; exact ⟨by simp, by simp; omega⟩
  | succFold n =>
    simp only [lowerT]
    right; refine ⟨_, positive_one (.primitive _ _ _ _ (.natural _) (.natural _) rfl), ?_⟩
    exact Ahead.refl _
  | succArg _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .binary .add x (.nat 1)) (fun s => .binaryLeft _ _ s) pos, ?_⟩
      exact .binary _ ah (Ahead.refl _)
  | binLit op a b =>
    simp only [lowerT]
    right; refine ⟨_, positive_one (.primitive _ _ _ _ (.natural _) (.natural _) (natOp_result op a b)), ?_⟩
    exact Ahead.refl _
  | binLeft op r _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .binary op.prim x (lowerT r)) (fun s => .binaryLeft _ _ s) pos, ?_⟩
      exact .binary _ ah (Ahead.refl _)
  | binRight op a _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .binary op.prim (.nat a) x)
        (fun s => .binaryRight _ _ (.natural a) s) pos, ?_⟩
      exact .binary _ (Ahead.refl _) ah
  | natRecZero T z s =>
    simp only [lowerT]
    right
    refine ⟨_, positive_trans (natRec_unfold_positive _ _ _) (.next (.zero _ _) (.refl _)), ?_⟩
    exact Ahead.refl _
  | natRecSucc T z s n =>
    simp only [lowerT]
    right
    refine ⟨_, positive_trans (natRec_unfold_positive _ _ _) (.next (.successor _ _ _) (.refl _)), ?_⟩
    simp only [instantiate_eq, Term.substitute, single]
    rw [rename_substitute, rename_substitute]
    have : (fun i => single (Term.nat n) (Nat.succ i)) = Term.bound := by funext i; rfl
    rw [this, substitute_bound, substitute_bound]
    exact Ahead.refl _
  | natRecMajor T z s _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_trans (natRec_unfold_positive _ _ _) (steps_ifZero _ _ (positive_steps pos)), ?_⟩
      exact .run (natRec_unfold _ _ _) (.ifZero ah (Ahead.refl _) (Ahead.refl _))
  | boolRecFalse T x y =>
    simp only [lowerT]
    right; exact ⟨_, positive_one (.ifFalse _ _), Ahead.refl _⟩
  | boolRecTrue T x y =>
    simp only [lowerT]
    right; exact ⟨_, positive_one (.ifTrue _ _), Ahead.refl _⟩
  | boolRecMajor T x y _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun c => .ifBool c (lowerT y) (lowerT x)) (fun s => .ifCondition _ _ s) pos, ?_⟩
      exact .ifBool ah (Ahead.refl _) (Ahead.refl _)
  | splitRecord names F fields values hit =>
    simp only [lowerT]
    right
    refine ⟨_, positive_one (.splitRecord _ _ _ _ (lowerFields_splitValues fields names values hit)), ?_⟩
    rw [lowerT_spine]; exact Ahead.refl _
  | splitMajor names F _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .split x names (lowerT F)) (fun s => .splitTarget _ _ s) pos, ?_⟩
      exact .split names ah (Ahead.refl _)
  | projRecord name fields value hit =>
    simp only [lowerT]
    right
    exact ⟨_, positive_one (.field _ _ _ (find_lowered lowerT fields name value hit)), Ahead.refl _⟩
  | projTarget name _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .get x name) (fun s => .target _ s) pos, ?_⟩
      exact .get name ah
  | casesInject T arms label fields names minor values armHit hit =>
    simp only [lowerT]
    right
    have found := find_lowered (fun p => caseArm p.1 (lowerT p.2)) arms label (names, minor) armHit
    refine ⟨applyAll (lowerT minor) (values.map lowerT), .begin (.caseInject _ _ _ _ found) ?_, ?_⟩
    · rw [caseArm_open]
      exact .next (.splitRecord _ _ _ _ (lowerFields_splitValues fields names values hit)) (.refl _)
    · rw [lowerT_spine]; exact Ahead.refl _
  | casesMajor T arms _ ih =>
    simp only [lowerT]
    rcases ih with ⟨e, lt⟩ | ⟨m, pos, ah⟩
    · left; refine ⟨by simp only [e], by simp; omega⟩
    · right
      refine ⟨_, positive_congr (fun x => .case x _) (fun s => .caseTarget _ s) pos, ?_⟩
      exact ahead_case_target _ ah

/-! ## The theorem -/

/-- `lowerT v` and a value reached by a chain of `Ahead` links. -/
inductive AheadChain : Term → Term → Prop where
  | refl (t : Term) : AheadChain t t
  | snoc {t m u : Term} : AheadChain t m → Ahead m u → AheadChain t u

theorem AheadChain.literal {v w : Term} (lit : Literal v) (h : AheadChain v w) : w = v := by
  induction h with
  | refl => rfl
  | snoc _ a ih => subst ih; exact inv_literal_behind lit a

theorem AheadChain.sameRuns {t u : Term} (h : AheadChain t u) : SameRuns t u := by
  induction h with
  | refl => exact ⟨fun _ => Iff.rfl, Iff.rfl⟩
  | snoc _ a ih =>
    have s := sameRuns_of_ahead a
    exact ⟨fun o => (ih.halts o).trans (s.halts o), ih.converges.trans s.converges⟩

/-- **`lower_value`**: canonical forms lower to Core4 values. -/
theorem lower_value {v : LExpr} (h : Canonical v) : Value (lowerT v) := by
  cases h <;> simp only [lowerT] <;> constructor

/-- **`lower_sound`, general form**: a source run to a canonical form is matched by a Core4 evaluation
of the lowered term, to a value that is the lowered canonical form up to a chain of `Ahead` links. -/
theorem lower_sound {e v : LExpr} (run : SSteps e v) (canonical : Canonical v) :
    ∃ w, Evaluates (lowerT e) w ∧ AheadChain (lowerT v) w := by
  induction run with
  | refl => exact ⟨_, ⟨.refl _, lower_value canonical⟩, .refl _⟩
  | next st _ ih =>
    obtain ⟨w, ⟨steps, value⟩, chain⟩ := ih canonical
    rcases lower_step st with ⟨e, _⟩ | ⟨m, pos, ah⟩
    · rw [e] at steps; exact ⟨w, ⟨steps, value⟩, chain⟩
    · obtain ⟨w', ev, a⟩ := evaluates_behind ah ⟨steps, value⟩
      exact ⟨w', ⟨steps_trans (positive_steps pos) ev.1, ev.2⟩, chain.snoc a⟩

/-- **`lower_sound` at `Nat`**: `Evaluates (lowerT e) (lowerT (lit n))`. -/
theorem lower_sound_nat {e : LExpr} {n : Nat} (run : SSteps e (.lit n)) :
    Evaluates (lowerT e) (lowerT (.lit n)) := by
  obtain ⟨w, ev, chain⟩ := lower_sound run (.lit n)
  simp only [lowerT] at chain ⊢
  rw [chain.literal (.nat n)] at ev; exact ev

/-- **`lower_sound` at `Bool`**. -/
theorem lower_sound_bool {e : LExpr} {b : Bool} (run : SSteps e (.boolLit b)) :
    Evaluates (lowerT e) (lowerT (.boolLit b)) := by
  obtain ⟨w, ev, chain⟩ := lower_sound run (.boolLit b)
  simp only [lowerT] at chain ⊢
  rw [chain.literal (.boolean b)] at ev; exact ev

/-- **`lower_sound` at a fragment inductive**: the lowered term evaluates to the same constructor,
whose payload has the completed runs of the lowered fields. -/
theorem lower_sound_inject {e : LExpr} {label : String} {fields : List (String × LExpr)}
    (run : SSteps e (.inject label fields)) :
    ∃ P, Evaluates (lowerT e) (.inject label P) ∧ AheadChain (.record (lowerFields fields)) P := by
  obtain ⟨w, ev, chain⟩ := lower_sound run (.inject label fields)
  simp only [lowerT] at chain
  suffices ∀ {t u : Term}, AheadChain t u → ∀ R, t = .inject label R →
      ∃ P, u = .inject label P ∧ AheadChain R P by
    obtain ⟨P, rfl, c⟩ := this chain _ rfl; exact ⟨P, ev, c⟩
  intro t u c
  induction c with
  | refl => intro R h; exact ⟨R, h, .refl _⟩
  | snoc _ a ih =>
    intro R h
    obtain ⟨P, rfl, c⟩ := ih R h
    obtain ⟨P', rfl, a'⟩ := inv_inject_behind a
    exact ⟨P', rfl, c.snoc a'⟩

/-! ## Teeth -/

theorem evaluates_unique {t v v' : Term} (h : Evaluates t v) (h' : Evaluates t v') : v = v' := by
  obtain ⟨s, val⟩ := h
  obtain ⟨s', val'⟩ := h'
  induction s with
  | refl => exact (value_steps_eq val s').symm
  | next st _ ih =>
    cases s' with
    | refl => exact absurd st (value_no_step val')
    | next st' r' => cases step_deterministic st st'; exact ih val r'

/-- A lowering that drops `Nat.rec`'s minor premise (its successor case keeps only the recursive result). -/
def lowerDropMinor : LExpr → Term
  | .natRec T z _ m => lowerT (.natRec T z (.lam .natural (.lam .natural (.bvar 0))) m)
  | e => lowerT e

/-- A lowering that maps `Nat.sub` to `add`. -/
def lowerSubAdd : LExpr → Term
  | .natBin .sub l r => lowerT (.natBin .add l r)
  | e => lowerT e

/-- `Nat.rec 7 (fun _ ih => ih + 1) 1`. -/
def succOnce : LExpr :=
  .natRec .natural (.lit 7) (.lam .natural (.lam .natural (.natSucc (.bvar 0)))) (.lit 1)

theorem succOnce_runs : SSteps succOnce (.lit 8) := by
  have e1 : (LExpr.lam .natural (.natSucc (.bvar 0))).inst (.lit 0) = .lam .natural (.natSucc (.bvar 0)) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst]
  have e2 : ∀ R : LExpr, (LExpr.natSucc (.bvar 0)).inst R = .natSucc R := fun R => by
    simp [LExpr.inst, LExpr.subst, LExpr.single]
  refine .next (.natRecSucc _ _ _ 0) ?_
  refine .next (.appFun _ (.beta _ _ _)) ?_
  rw [e1]
  refine .next (.beta _ _ _) ?_
  rw [e2]
  refine .next (.succArg (.natRecZero _ _ _)) ?_
  exact .next (.succFold 7) (.refl _)

theorem dropped_runs :
    SSteps (.natRec .natural (.lit 7) (.lam .natural (.lam .natural (.bvar 0))) (.lit 1)) (.lit 7) := by
  have e1 : (LExpr.lam .natural (.bvar 0)).inst (.lit 0) = .lam .natural (.bvar 0) := by
    simp [LExpr.inst, LExpr.subst, LExpr.liftSubst]
  have e2 : ∀ R : LExpr, (LExpr.bvar 0).inst R = R := fun R => by simp [LExpr.inst, LExpr.subst, LExpr.single]
  refine .next (.natRecSucc _ _ _ 0) ?_
  refine .next (.appFun _ (.beta _ _ _)) ?_
  rw [e1]
  refine .next (.beta _ _ _) ?_
  rw [e2]
  exact .next (.natRecZero _ _ _) (.refl _)

/-- **Tooth**: dropping the minor premise is refused by `lower_sound`: `Nat.rec 7 (fun _ ih => ih + 1) 1`
reduces to `8`, its mis-lowering evaluates to `7`. -/
theorem dropMinor_refuted :
    ¬ ∀ (e : LExpr) (n : Nat), SSteps e (.lit n) → Evaluates (lowerDropMinor e) (.nat n) := by
  intro claim
  have bad := claim succOnce 8 succOnce_runs
  have good := lower_sound_nat dropped_runs
  simp only [lowerDropMinor, succOnce] at bad
  simp only [lowerT] at bad good
  have := evaluates_unique bad good
  simp at this

/-- **Tooth**: `Nat.sub` lowered to `add` is refused: `5 - 3` reduces to `2`, its mis-lowering to `8`. -/
theorem subAdd_refuted :
    ¬ ∀ (e : LExpr) (n : Nat), SSteps e (.lit n) → Evaluates (lowerSubAdd e) (.nat n) := by
  intro claim
  have bad := claim (.natBin .sub (.lit 5) (.lit 3)) 2 (.next (.binLit .sub 5 3) (.refl _))
  have good := lower_sound_nat (e := .natBin .add (.lit 5) (.lit 3)) (n := 8) (.next (.binLit .add 5 3) (.refl _))
  simp only [lowerSubAdd] at bad
  simp only [lowerT] at bad good
  have := evaluates_unique bad good
  simp at this

end Obend.Lower
end
