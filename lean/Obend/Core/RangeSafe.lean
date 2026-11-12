module
/-
# Obend.Core.RangeSafe — Static Interval Abstract Interpreter & `Nat` ↔ `BitVec 64` ↔ `ℤ/Mℤ` Bridge

Closes Chasm 1 across unbounded `Obend.Core.Term` (`Nat`), `Obend.Hardware.Compiler` (`BitVec 64`),
and Sable `F_O` ZK prime-field circuits (`ℤ/Mℤ`, KoalaBear & Goldilocks):
1. `inferRange` + `inferRange_sound`: decidable interval inference over the compilable Core4 fragment.
2. `evaluates_eq_evalTermHw_of_rangeSafe` + `compileTerm_evaluates_sound`: exact `Core.Term` → `RtlExpr` bridge.
3. `evaluates_mod_prime_exact_of_rangeSafe`: exact `ℤ/Mℤ` integer reconstruction (`M > 1`).
4. `wrap_counterexample_without_rangeSafe` + `mod_wrap_counterexample_without_rangeSafe` + `underflow_counterexample_without_rangeSafe`.
-/
public import Obend.Core.Term
public import Obend.Core.TermTraverse
public import Obend.Hardware.Compiler
public import Obend.Apps.ZkNtt.Goldilocks

public section
namespace Obend.Core.RangeSafe

open Obend.Core.Term
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Apps.ZkNtt (goldilocksPrime)

set_option autoImplicit false
set_option maxHeartbeats 200000

/-! ## 1. Scalar Sorts, Certified Intervals, and Value Membership -/

/-- Scalar sort tracked alongside numeric bounds so `Core.Term`'s disjoint `.nat` and `.boolean`
    value constructors never get conflated at primitives or branch eliminators. -/
inductive ScalarSort where
  | nat
  | bool
  deriving @[expose] DecidableEq, Repr

/-- Certified closed interval `[lo, hi]` tagged with its Core4 scalar sort (`nat` or `bool`). -/
structure Interval where
  lo : Nat
  hi : Nat
  sort : ScalarSort := .nat
  wf : lo ≤ hi := by omega
  deriving DecidableEq

instance : Repr Interval where
  reprPrec i _ :=
    let tag := match i.sort with | .nat => "nat" | .bool => "bool"
    s!"Interval({tag}: [{i.lo}, {i.hi}])"

/-- Construct a `Nat` interval `[lo, hi]` given `lo ≤ hi`. -/
@[expose] def Interval.mkNat (lo hi : Nat) (h : lo ≤ hi := by omega) : Interval :=
  { lo := lo, hi := hi, sort := .nat, wf := h }

/-- Construct the canonical `[0, 1]` boolean interval. -/
@[expose] def Interval.bool01 : Interval :=
  { lo := 0, hi := 1, sort := .bool, wf := by decide }

/-- Join two intervals of matching `ScalarSort` by taking `[min lo, max hi]`. -/
@[expose] def Interval.join (a b : Interval) : Option Interval :=
  if a.sort == b.sort then
    some { lo := min a.lo b.lo, hi := max a.hi b.hi, sort := a.sort, wf := by have := a.wf; omega }
  else
    none

/-- Predecessor interval `[lo - 1, hi - 1]` bound at de Bruijn index `0` in `.ifZero v z s`. -/
@[expose] def Interval.pred (a : Interval) : Interval :=
  { lo := a.lo - 1, hi := a.hi - 1, sort := .nat, wf := by have := a.wf; omega }

/-- Numeric code of a Core4 scalar value (`.nat n ↦ n`, `.boolean true ↦ 1`, `.boolean false ↦ 0`). -/
@[expose] def scalarToNat : Term → Nat
  | .nat n => n
  | .boolean b => if b then 1 else 0
  | _ => 0

/-- Membership of a Core4 value `v` in interval `I` (respecting `.nat` vs `.boolean` sort). -/
@[expose] def ValueInInterval (I : Interval) (v : Term) : Prop :=
  match I.sort with
  | .nat => ∃ n : Nat, v = .nat n ∧ I.lo ≤ n ∧ n ≤ I.hi
  | .bool =>
    ∃ b : Bool, v = .boolean b ∧
      I.lo ≤ (if b then 1 else 0) ∧ (if b then 1 else 0) ≤ I.hi

theorem valueInInterval_is_value {I : Interval} {v : Term} (h : ValueInInterval I v) : Value v := by
  cases hs : I.sort <;> simp only [ValueInInterval, hs] at h
  · obtain ⟨n, rfl, _, _⟩ := h; exact .natural n
  · obtain ⟨b, rfl, _, _⟩ := h; exact .boolean b

theorem valueInInterval_bounds {I : Interval} {v : Term} (h : ValueInInterval I v) :
    I.lo ≤ scalarToNat v ∧ scalarToNat v ≤ I.hi := by
  cases hs : I.sort <;> simp only [ValueInInterval, hs] at h
  · obtain ⟨n, rfl, hlo, hhi⟩ := h; exact ⟨hlo, hhi⟩
  · obtain ⟨b, rfl, hlo, hhi⟩ := h; exact ⟨hlo, hhi⟩

theorem valueInInterval_join_left {a b j : Interval} {v : Term}
    (hj : Interval.join a b = some j) (hv : ValueInInterval a v) : ValueInInterval j v := by
  unfold Interval.join at hj
  by_cases hEq : a.sort == b.sort
  · simp only [hEq, ↓reduceIte, Option.some.injEq] at hj; subst hj
    cases hs : a.sort <;> simp only [ValueInInterval, hs] at hv ⊢ <;>
      (obtain ⟨x, rfl, hlo, hhi⟩ := hv; exact ⟨x, rfl, by omega, by omega⟩)
  · simp [hEq] at hj

theorem valueInInterval_join_right {a b j : Interval} {v : Term}
    (hj : Interval.join a b = some j) (hv : ValueInInterval b v) : ValueInInterval j v := by
  unfold Interval.join at hj
  by_cases hEq : a.sort == b.sort
  · simp only [hEq, ↓reduceIte, Option.some.injEq] at hj
    have hSort : a.sort = b.sort := of_decide_eq_true hEq; subst hj
    cases hs : b.sort <;>
      (simp only [ValueInInterval, hs] at hv; simp only [ValueInInterval, hSort.trans hs];
       obtain ⟨x, rfl, hlo, hhi⟩ := hv; exact ⟨x, rfl, by omega, by omega⟩)
  · simp [hEq] at hj

/-! ## 2. De Bruijn Closing Substitution & Deterministic `Core.Term` Reduction Lemmas -/

@[expose] def envSubst (env : List Term) (idx : Nat) : Term :=
  match env[idx]? with | some e => e | none => .bound (idx - env.length)

@[expose] def closeTerm (env : List Term) (t : Term) : Term := t.substitute (envSubst env)

private theorem closeTerm_nat (env : List Term) (n : Nat) : closeTerm env (.nat n) = .nat n := by
  unfold closeTerm; rw [Term.substitute]
private theorem closeTerm_bool (env : List Term) (b : Bool) : closeTerm env (.boolean b) = .boolean b := by
  unfold closeTerm; rw [Term.substitute]

theorem term_substitute_id (t : Term) : t.substitute (fun j => .bound j) = t := by
  apply Obend.Core.TermTraverse.encode_injective; rw [Obend.Core.TermTraverse.encode_substitute]
  have hVar : (fun i => Obend.Core.TermTraverse.encode (.bound i)) = Obend.Core.Traverse.Tree.var := by
    funext i; simp [Obend.Core.TermTraverse.encode]
  rw [hVar]; exact Obend.Core.Traverse.Tree.substitute_id (Obend.Core.TermTraverse.encode t)

theorem instantiate_closeTerm_lift (subBody argTerm : Term) (env : List Term) :
    instantiate (subBody.substitute (liftSubstitution (envSubst env))) argTerm =
      closeTerm (argTerm :: env) subBody := by
  unfold instantiate closeTerm; rw [Obend.Core.TermTraverse.substitute_comp]; congr 1; funext i
  cases i with
  | zero => simp [liftSubstitution, envSubst]
  | succ k =>
    simp only [liftSubstitution]; rw [Obend.Core.TermTraverse.rename_substitute]
    change (envSubst env k).substitute (fun j => .bound j) = envSubst (argTerm :: env) (k + 1)
    rw [term_substitute_id]; simp [envSubst]

theorem steps_trans {a b c : Term} (h1 : Steps a b) (h2 : Steps b c) : Steps a c := by
  induction h1 with | refl _ => exact h2 | next s _ ih => exact .next s (ih h2)

theorem steps_binaryLeft {op : Primitive} {l l' : Term} (r : Term) (h : Steps l l') :
    Steps (.binary op l r) (.binary op l' r) := by
  induction h with | refl _ => exact .refl _ | next s _ ih => exact .next (.binaryLeft op r s) ih

theorem steps_binaryRight {op : Primitive} {l r r' : Term} (hl : Value l) (h : Steps r r') :
    Steps (.binary op l r) (.binary op l r') := by
  induction h with | refl _ => exact .refl _ | next s _ ih => exact .next (.binaryRight op l hl s) ih

theorem steps_ifCondition {c c' : Term} (t f : Term) (h : Steps c c') :
    Steps (.ifBool c t f) (.ifBool c' t f) := by
  induction h with | refl _ => exact .refl _ | next s _ ih => exact .next (.ifCondition t f s) ih

theorem steps_zeroCondition {v v' : Term} (z s : Term) (h : Steps v v') :
    Steps (.ifZero v z s) (.ifZero v' z s) := by
  induction h with | refl _ => exact .refl _ | next st _ ih => exact .next (.condition z s st) ih

/-- `Core.Term.Step` is deterministic: every term has at most one next weak-head reduct. -/
theorem step_deterministic {t u₁ u₂ : Term} (h₁ : Step t u₁) (h₂ : Step t u₂) : u₁ = u₂ := by
  induction h₁ generalizing u₂ with
  | beta => cases h₂ with | beta => rfl | application _ hs => cases hs
  | application _ s₁ ih =>
    cases h₂ with | beta => cases s₁ | application _ s₂ => rw [ih s₂] | applySpecification => cases s₁
  | mix => cases h₂; rfl
  | fix => cases h₂; rfl
  | applySpecification => cases h₂ with | applySpecification => rfl | application _ hs => cases hs
  | reflectPrototype => cases h₂ with | reflectPrototype => rfl | reflectStep hs => cases hs
  | metadataSpecification => cases h₂ with | metadataSpecification => rfl | metadataStep hs => cases hs
  | projectPrototype => cases h₂ with | projectPrototype => rfl | projectStep hs => cases hs
  | reflectStep s₁ ih => cases h₂ with | reflectPrototype => cases s₁ | reflectStep s₂ => rw [ih s₂]
  | metadataStep s₁ ih => cases h₂ with | metadataSpecification => cases s₁ | metadataStep s₂ => rw [ih s₂]
  | projectStep s₁ ih => cases h₂ with | projectPrototype => cases s₁ | projectStep s₂ => rw [ih s₂]
  | target _ s₁ ih => cases h₂ with | target _ s₂ => rw [ih s₂] | field => cases s₁
  | field _ _ _ hf₁ =>
    cases h₂ with
    | target _ hs => cases hs
    | field _ _ _ hf₂ => rw [hf₁] at hf₂; injection hf₂ with hPair; injection hPair
  | extendTarget _ s₁ ih => cases h₂ with | extendTarget _ s₂ => rw [ih s₂] | extendRecord => cases s₁
  | extendRecord => cases h₂ with | extendTarget _ hs => cases hs | extendRecord => rfl
  | binaryLeft _ _ s₁ ih =>
    cases h₂ with
    | binaryLeft _ _ s₂ => rw [ih s₂]
    | binaryRight _ _ hv _ => exact False.elim (value_no_step hv s₁)
    | primitive _ _ _ _ hv _ _ => exact False.elim (value_no_step hv s₁)
  | binaryRight _ _ hvl s₁ ih =>
    cases h₂ with
    | binaryLeft _ _ s₂ => exact False.elim (value_no_step hvl s₂)
    | binaryRight _ _ _ s₂ => rw [ih s₂]
    | primitive _ _ _ _ _ hvr _ => exact False.elim (value_no_step hvr s₁)
  | primitive _ _ _ _ hvl hvr hp₁ =>
    cases h₂ with
    | binaryLeft _ _ s₂ => exact False.elim (value_no_step hvl s₂)
    | binaryRight _ _ _ s₂ => exact False.elim (value_no_step hvr s₂)
    | primitive _ _ _ _ _ _ hp₂ => rw [hp₁] at hp₂; injection hp₂
  | condition _ _ s₁ ih =>
    cases h₂ with | condition _ _ s₂ => rw [ih s₂] | zero => cases s₁ | successor => cases s₁
  | zero => cases h₂ with | condition _ _ hs => cases hs | zero => rfl
  | successor => cases h₂ with | condition _ _ hs => cases hs | successor => rfl
  | caseTarget _ s₁ ih => cases h₂ with | caseTarget _ s₂ => rw [ih s₂] | caseInject => cases s₁
  | caseInject _ _ _ _ hf₁ =>
    cases h₂ with
    | caseTarget _ hs => cases hs
    | caseInject _ _ _ _ hf₂ =>
      rw [hf₁] at hf₂; injection hf₂ with hPair; injection hPair with _ hBody; rw [hBody]
  | ifCondition _ _ s₁ ih =>
    cases h₂ with | ifCondition _ _ s₂ => rw [ih s₂] | ifTrue => cases s₁ | ifFalse => cases s₁
  | ifTrue => cases h₂ with | ifCondition _ _ hs => cases hs | ifTrue => rfl
  | ifFalse => cases h₂ with | ifCondition _ _ hs => cases hs | ifFalse => rfl
  | done => cases h₂; rfl
  | splitTarget _ _ s₁ ih => cases h₂ with | splitTarget _ _ s₂ => rw [ih s₂] | splitRecord => cases s₁
  | splitRecord _ _ _ _ hs₁ =>
    cases h₂ with
    | splitTarget _ _ hs => cases hs
    | splitRecord _ _ _ _ hs₂ => rw [hs₁] at hs₂; injection hs₂ with hEq; rw [hEq]

/-- `Core.Term.Evaluates` is deterministic: any term evaluates to at most one `Value`. -/
theorem evaluates_deterministic {t v₁ v₂ : Term} (h₁ : Evaluates t v₁) (h₂ : Evaluates t v₂) :
    v₁ = v₂ := by
  rcases h₁ with ⟨s₁, hv₁⟩; rcases h₂ with ⟨s₂, hv₂⟩
  induction s₁ with
  | refl _ =>
    cases s₂ with
    | refl _ => rfl
    | next st _ => exact False.elim (value_no_step hv₁ st)
  | next st₁ rest₁ ih =>
    cases s₂ with
    | refl _ => exact False.elim (value_no_step hv₂ st₁)
    | next st₂ rest₂ =>
      obtain rfl := step_deterministic st₁ st₂
      exact ih hv₁ rest₂

private theorem eval_close_let {env : List Term} {subBody arg v : Term}
    (hBody : Evaluates (closeTerm (closeTerm env arg :: env) subBody) v) :
    Evaluates (closeTerm env (.app (.lam subBody) arg)) v := by
  refine ⟨?_, hBody.2⟩; simp only [closeTerm, Term.substitute]
  have st : Step
      (.app (.lam (subBody.substitute (liftSubstitution (envSubst env)))) (arg.substitute (envSubst env)))
      (instantiate (subBody.substitute (liftSubstitution (envSubst env))) (arg.substitute (envSubst env))) := .beta _ _
  rw [instantiate_closeTerm_lift] at st; exact .next st hBody.1

private theorem eval_close_binary {env : List Term} {op : Primitive} {l r vl vr vOut : Term}
    (hl : Evaluates (closeTerm env l) vl) (hr : Evaluates (closeTerm env r) vr)
    (hp : primitiveResult op vl vr = some vOut) (hvOut : Value vOut) :
    Evaluates (closeTerm env (.binary op l r)) vOut := by
  refine ⟨?_, hvOut⟩; simp only [closeTerm, Term.substitute]
  exact steps_trans (steps_binaryLeft _ hl.1) (steps_trans (steps_binaryRight hl.2 hr.1)
    (.next (.primitive op vl vr vOut hl.2 hr.2 hp) (.refl vOut)))

private theorem eval_close_ifTrue {env : List Term} {c t f vt : Term}
    (hc : Evaluates (closeTerm env c) (.boolean true)) (ht : Evaluates (closeTerm env t) vt) :
    Evaluates (closeTerm env (.ifBool c t f)) vt := by
  refine ⟨?_, ht.2⟩; simp only [closeTerm, Term.substitute]
  exact steps_trans (steps_ifCondition _ _ hc.1) (.next (.ifTrue _ _) ht.1)

private theorem eval_close_ifFalse {env : List Term} {c t f vf : Term}
    (hc : Evaluates (closeTerm env c) (.boolean false)) (hf : Evaluates (closeTerm env f) vf) :
    Evaluates (closeTerm env (.ifBool c t f)) vf := by
  refine ⟨?_, hf.2⟩; simp only [closeTerm, Term.substitute]
  exact steps_trans (steps_ifCondition _ _ hc.1) (.next (.ifFalse _ _) hf.1)

private theorem eval_close_ifZero_zero {env : List Term} {v z s vz : Term}
    (hv : Evaluates (closeTerm env v) (.nat 0)) (hz : Evaluates (closeTerm env z) vz) :
    Evaluates (closeTerm env (.ifZero v z s)) vz := by
  refine ⟨?_, hz.2⟩; simp only [closeTerm, Term.substitute]
  exact steps_trans (steps_zeroCondition _ _ hv.1) (.next (.zero _ _) hz.1)

private theorem eval_close_ifZero_succ {env : List Term} {v z s vs : Term} {n : Nat}
    (hv : Evaluates (closeTerm env v) (.nat (n + 1)))
    (hs : Evaluates (closeTerm (.nat n :: env) s) vs) :
    Evaluates (closeTerm env (.ifZero v z s)) vs := by
  refine ⟨?_, hs.2⟩; simp only [closeTerm, Term.substitute]
  have st : Step
      (.ifZero (.nat (n + 1)) (z.substitute (envSubst env)) (s.substitute (liftSubstitution (envSubst env))))
      (instantiate (s.substitute (liftSubstitution (envSubst env))) (.nat n)) := .successor n _ _
  rw [instantiate_closeTerm_lift] at st
  exact steps_trans (steps_zeroCondition _ _ hv.1) (.next st hs.1)

/-! ## 3. Decidable Interval Abstract Interpreter (`inferRange`) & Soundness (`inferRange_sound`) -/

private theorem div_le_div_of_le_of_pos {a b c d : Nat}
    (hab : a ≤ b) (hcd : c ≤ d) (hc : 0 < c) :
    a / d ≤ b / c := by
  have h1 : a / d ≤ b / d := Nat.div_le_div_right hab
  suffices h2 : b / d ≤ b / c from Nat.le_trans h1 h2
  by_cases hlt : b / c < b / d
  · have hstep : b / c + 1 ≤ b / d := hlt
    have hm1 : (b / c + 1) * c ≤ (b / c + 1) * d := Nat.mul_le_mul_left _ hcd
    have hm2 : (b / c + 1) * d ≤ (b / d) * d := Nat.mul_le_mul_right d hstep
    have hm3 : (b / d) * d ≤ b := Nat.div_mul_le_self b d
    have hgt : b < (b / c + 1) * c := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.lt_div_mul_add hc
    omega
  · omega

private def natOut (il ir : Interval) (lo hi : Nat) (hwf : lo ≤ hi) : Option Interval :=
  if il.sort == .nat && ir.sort == .nat then
    some { lo := lo, hi := hi, sort := .nat, wf := hwf }
  else none

private def natBoolOut (il ir : Interval) : Option Interval :=
  if il.sort == .nat && ir.sort == .nat then some Interval.bool01 else none

private theorem natOut_eq_some {il ir iOut : Interval} {lo hi : Nat} {hwf : lo ≤ hi}
    (h : natOut il ir lo hi hwf = some iOut) :
    il.sort = .nat ∧ ir.sort = .nat ∧ iOut = { lo := lo, hi := hi, sort := .nat, wf := hwf } := by
  unfold natOut at h
  by_cases hs : il.sort == .nat && ir.sort == .nat
  · simp only [hs, ↓reduceIte, Option.some.injEq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    exact ⟨hs.1, hs.2, h.symm⟩
  · simp [hs] at h

private theorem natBoolOut_eq_some {il ir iOut : Interval}
    (h : natBoolOut il ir = some iOut) :
    il.sort = .nat ∧ ir.sort = .nat ∧ iOut = Interval.bool01 := by
  unfold natBoolOut at h
  by_cases hs : il.sort == .nat && ir.sort == .nat
  · simp only [hs, ↓reduceIte, Option.some.injEq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    exact ⟨hs.1, hs.2, h.symm⟩
  · simp [hs] at h

/-- Interval transfer function for Core4 binary primitives. -/
def inferPrimRange (op : Primitive) (a b : Interval) : Option Interval :=
  match op with
  | .add => natOut a b (a.lo + b.lo) (a.hi + b.hi) (Nat.add_le_add a.wf b.wf)
  | .multiply => natOut a b (a.lo * b.lo) (a.hi * b.hi) (Nat.mul_le_mul a.wf b.wf)
  | .subtract => natOut a b (a.lo - b.hi) (a.hi - b.lo) (by have := a.wf; have := b.wf; omega)
  | .divide =>
    if hpos : 0 < b.lo then
      natOut a b (a.lo / b.hi) (a.hi / b.lo) (div_le_div_of_le_of_pos a.wf b.wf hpos)
    else
      natOut a b 0 a.hi (Nat.zero_le _)
  | .modulo =>
    if 0 < b.lo then natOut a b 0 (min a.hi (b.hi - 1)) (Nat.zero_le _)
    else natOut a b 0 a.hi (Nat.zero_le _)
  | .equal | .less | .lessEqual | .slt => natBoolOut a b
  | .conjunction =>
    if a.sort == .bool && b.sort == .bool then some Interval.bool01 else none
  | .lshr =>
    if a.hi < 2 ^ 64 then natOut a b 0 a.hi (Nat.zero_le _)
    else natOut a b 0 (2 ^ 64 - 1) (Nat.zero_le _)
  | .bitAnd | .bitOr | .bitXor | .shl | .ashr | .qmul32 =>
    natOut a b 0 (2 ^ 64 - 1) (Nat.zero_le _)
  | .labelEqual => none

def inferRange (Γ : List Interval) : Term → Option Interval
  | .nat n => some { lo := n, hi := n, sort := .nat, wf := Nat.le_refl n }
  | .boolean b => let k := if b then 1 else 0; some { lo := k, hi := k, sort := .bool, wf := Nat.le_refl k }
  | .bound idx => Γ[idx]?
  | .app (.lam subBody) arg =>
    match inferRange Γ arg with | some iArg => inferRange (iArg :: Γ) subBody | none => none
  | .binary op l r =>
    match inferRange Γ l, inferRange Γ r with | some il, some ir => inferPrimRange op il ir | _, _ => none
  | .ifBool c t f =>
    match inferRange Γ c, inferRange Γ t, inferRange Γ f with
    | some ic, some it, some iff => if ic.sort == .bool then Interval.join it iff else none
    | _, _, _ => none
  | .ifZero v z s =>
    match inferRange Γ v, inferRange Γ z with
    | some iv, some iz =>
      if iv.sort == .nat then
        match inferRange (Interval.pred iv :: Γ) s with | some is => Interval.join iz is | none => none
      else none
    | _, _ => none
  | _ => none

def EnvInIntervals (Γ : List Interval) (env : List Term) : Prop :=
  Γ.length ≤ env.length ∧
    ∀ (idx : Nat) (I : Interval), Γ[idx]? = some I →
      ∃ e v, env[idx]? = some e ∧ Evaluates e v ∧ ValueInInterval I v

theorem envInIntervals_nil : EnvInIntervals [] [] := ⟨Nat.le_refl 0, fun _ _ h => by simp at h⟩

theorem envInIntervals_cons {I : Interval} {Γ : List Interval} {e v : Term} {env : List Term}
    (he : Evaluates e v) (hv : ValueInInterval I v) (hEnv : EnvInIntervals Γ env) :
    EnvInIntervals (I :: Γ) (e :: env) := by
  refine ⟨Nat.succ_le_succ hEnv.1, fun idx J hJ => ?_⟩
  cases idx with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hJ; subst hJ; exact ⟨e, v, rfl, he, hv⟩
  | succ k => simp only [List.getElem?_cons_succ] at hJ ⊢; exact hEnv.2 k J hJ

private theorem bv64_toNat_le_max (w : BitVec 64) : w.toNat ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt w.isLt

theorem inferPrimRange_sound {op : Primitive} {il ir iOut : Interval} {vl vr : Term}
    (hPrim : inferPrimRange op il ir = some iOut)
    (hvl : ValueInInterval il vl) (hvr : ValueInInterval ir vr) :
    ∃ vOut, primitiveResult op vl vr = some vOut ∧ ValueInInterval iOut vOut := by
  cases op with
  | labelEqual => simp [inferPrimRange] at hPrim
  | conjunction =>
    simp only [inferPrimRange] at hPrim
    by_cases hs : il.sort == .bool && ir.sort == .bool
    · simp only [hs, ↓reduceIte, Option.some.injEq] at hPrim; simp only [Bool.and_eq_true, beq_iff_eq] at hs; subst hPrim
      simp only [ValueInInterval, hs.1] at hvl; simp only [ValueInInterval, hs.2] at hvr
      obtain ⟨ba, rfl, _, _⟩ := hvl; obtain ⟨bb, rfl, _, _⟩ := hvr
      refine ⟨.boolean (ba && bb), rfl, ba && bb, rfl, ?_, ?_⟩ <;> cases ba <;> cases bb <;> decide
    · simp [hs] at hPrim
  | add =>
    obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, hal, hah⟩ := hvl; obtain ⟨nb, rfl, hbl, hbh⟩ := hvr
    exact ⟨.nat (na + nb), rfl, na + nb, rfl, Nat.add_le_add hal hbl, Nat.add_le_add hah hbh⟩
  | multiply =>
    obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, hal, hah⟩ := hvl; obtain ⟨nb, rfl, hbl, hbh⟩ := hvr
    exact ⟨.nat (na * nb), rfl, na * nb, rfl, Nat.mul_le_mul hal hbl, Nat.mul_le_mul hah hbh⟩
  | subtract =>
    obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, hal, hah⟩ := hvl; obtain ⟨nb, rfl, hbl, hbh⟩ := hvr
    refine ⟨.nat (na - nb), rfl, na - nb, rfl, ?_, ?_⟩ <;> dsimp only <;> omega
  | divide =>
    simp only [inferPrimRange] at hPrim
    split at hPrim
    · rename_i hpos; obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
      simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
      obtain ⟨na, rfl, hal, hah⟩ := hvl; obtain ⟨nb, rfl, hbl, hbh⟩ := hvr
      exact ⟨.nat (na / nb), rfl, na / nb, rfl,
        div_le_div_of_le_of_pos hal hbh (by omega), div_le_div_of_le_of_pos hah hbl hpos⟩
    · obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
      simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
      obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
      exact ⟨.nat (na / nb), rfl, na / nb, rfl, Nat.zero_le _, Nat.le_trans (Nat.div_le_self na nb) hah⟩
  | modulo =>
    simp only [inferPrimRange] at hPrim
    split at hPrim
    · rename_i hpos; obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
      simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
      obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, hbl, hbh⟩ := hvr
      have hlt : na % nb < nb := Nat.mod_lt na (by omega)
      have hle : na % nb ≤ na := Nat.mod_le na nb
      exact ⟨.nat (na % nb), rfl, na % nb, rfl, Nat.zero_le _, by dsimp only; omega⟩
    · obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
      simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
      obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
      exact ⟨.nat (na % nb), rfl, na % nb, rfl, Nat.zero_le _, Nat.le_trans (Nat.mod_le na nb) hah⟩
  | equal =>
    obtain ⟨hsl, hsr, rfl⟩ := natBoolOut_eq_some hPrim
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    refine ⟨_, rfl, _, rfl, ?_, ?_⟩ <;> cases (na == nb) <;> decide
  | less =>
    obtain ⟨hsl, hsr, rfl⟩ := natBoolOut_eq_some hPrim
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    refine ⟨_, rfl, _, rfl, ?_, ?_⟩ <;> cases decide (na < nb) <;> decide
  | lessEqual =>
    obtain ⟨hsl, hsr, rfl⟩ := natBoolOut_eq_some hPrim
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    refine ⟨_, rfl, _, rfl, ?_, ?_⟩ <;> cases decide (na ≤ nb) <;> decide
  | slt =>
    obtain ⟨hsl, hsr, rfl⟩ := natBoolOut_eq_some hPrim
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    refine ⟨_, rfl, _, rfl, ?_, ?_⟩ <;> cases BitVec.slt (word64 na) (word64 nb) <;> decide
  | lshr =>
    simp only [inferPrimRange] at hPrim
    split at hPrim
    · rename_i hlt64
      obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
      simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
      obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
      have hna : na < 2 ^ 64 := Nat.lt_of_le_of_lt hah hlt64
      let res := (word64 na >>> ((word64 nb).toNat % 64)).toNat
      have hsh : res ≤ na := by
        simp only [res, word64, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna,
          Nat.shiftRight_eq_div_pow]
        exact Nat.div_le_self na _
      exact ⟨.nat res, rfl, res, rfl, Nat.zero_le _, Nat.le_trans hsh hah⟩
    · obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
      simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
      obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
      exact ⟨_, rfl, _, rfl, Nat.zero_le _, bv64_toNat_le_max _⟩
  | bitAnd | bitOr | bitXor | shl | ashr | qmul32 =>
    obtain ⟨hsl, hsr, rfl⟩ := natOut_eq_some hPrim
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    exact ⟨_, rfl, _, rfl, Nat.zero_le _, bv64_toNat_le_max _⟩

/-- **Soundness of `inferRange` (`inferRange_sound`)**:
    Whenever `inferRange Γ t = some I` and `EnvInIntervals Γ env`, closing `t` under `env` evaluates
    in `Core.Term` to a unique scalar value `v` satisfying `ValueInInterval I v`. -/
theorem inferRange_sound
    (Γ : List Interval) (t : Term) (I : Interval) (env : List Term)
    (hRange : inferRange Γ t = some I)
    (hEnv : EnvInIntervals Γ env) :
    ∃ v : Term, Evaluates (closeTerm env t) v ∧ ValueInInterval I v := by
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .record _ | .get _ _ | .inject _ _ | .case _ _
  | .perform _ | .done _ | .split _ _ _ => simp [inferRange] at hRange
  | .nat n =>
    simp only [inferRange, Option.some.injEq] at hRange; subst hRange; rw [closeTerm_nat]
    exact ⟨.nat n, ⟨.refl _, .natural n⟩, n, rfl, Nat.le_refl n, Nat.le_refl n⟩
  | .boolean b =>
    simp only [inferRange, Option.some.injEq] at hRange; subst hRange; rw [closeTerm_bool]
    exact ⟨.boolean b, ⟨.refl _, .boolean b⟩, b, rfl, Nat.le_refl _, Nat.le_refl _⟩
  | .bound idx =>
    obtain ⟨e, v, hGet, hEval, hVal⟩ := hEnv.2 idx I hRange
    simp only [closeTerm, Term.substitute, envSubst, hGet]; exact ⟨v, hEval, hVal⟩
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [inferRange] at hRange
      cases hArg : inferRange Γ arg with
      | none => simp [hArg] at hRange
      | some iArg =>
        simp only [hArg] at hRange
        obtain ⟨vArg, hEvalArg, hInArg⟩ := inferRange_sound Γ arg iArg env hArg hEnv
        obtain ⟨vBody, hEvalBody, hInBody⟩ :=
          inferRange_sound (iArg :: Γ) subBody I (closeTerm env arg :: env) hRange
            (envInIntervals_cons hEvalArg hInArg hEnv)
        exact ⟨vBody, eval_close_let hEvalBody, hInBody⟩
    | _ => simp [inferRange] at hRange
  | .binary op l r =>
    simp only [inferRange] at hRange
    cases hl : inferRange Γ l with
    | none => simp [hl] at hRange
    | some il =>
      cases hr : inferRange Γ r with
      | none => simp [hl, hr] at hRange
      | some ir =>
        simp only [hl, hr] at hRange
        obtain ⟨vl, hEvalL, hInL⟩ := inferRange_sound Γ l il env hl hEnv
        obtain ⟨vr, hEvalR, hInR⟩ := inferRange_sound Γ r ir env hr hEnv
        obtain ⟨vOut, hPrimRes, hInOut⟩ := inferPrimRange_sound hRange hInL hInR
        exact ⟨vOut, eval_close_binary hEvalL hEvalR hPrimRes (valueInInterval_is_value hInOut), hInOut⟩
  | .ifBool c tBranch fBranch =>
    simp only [inferRange] at hRange
    cases hc : inferRange Γ c with
    | none => simp [hc] at hRange
    | some ic =>
      cases ht : inferRange Γ tBranch with
      | none => simp [hc, ht] at hRange
      | some it =>
        cases hf : inferRange Γ fBranch with
        | none => simp [hc, ht, hf] at hRange
        | some iff =>
          simp only [hc, ht, hf] at hRange
          by_cases hSort : ic.sort == .bool
          · simp only [hSort, ↓reduceIte] at hRange
            obtain ⟨vc, hEvalC, hInC⟩ := inferRange_sound Γ c ic env hc hEnv
            simp only [ValueInInterval, of_decide_eq_true hSort] at hInC
            obtain ⟨b, rfl, _, _⟩ := hInC
            cases b with
            | true =>
              obtain ⟨vt, hEvalT, hInT⟩ := inferRange_sound Γ tBranch it env ht hEnv
              exact ⟨vt, eval_close_ifTrue hEvalC hEvalT, valueInInterval_join_left hRange hInT⟩
            | false =>
              obtain ⟨vf, hEvalF, hInF⟩ := inferRange_sound Γ fBranch iff env hf hEnv
              exact ⟨vf, eval_close_ifFalse hEvalC hEvalF, valueInInterval_join_right hRange hInF⟩
          · simp [hSort] at hRange
  | .ifZero v z s =>
    simp only [inferRange] at hRange
    cases hv : inferRange Γ v with
    | none => simp [hv] at hRange
    | some iv =>
      cases hz : inferRange Γ z with
      | none => simp [hv, hz] at hRange
      | some iz =>
        simp only [hv, hz] at hRange
        by_cases hSort : iv.sort == .nat
        · simp only [hSort, ↓reduceIte] at hRange
          cases hs : inferRange (Interval.pred iv :: Γ) s with
          | none => simp [hs] at hRange
          | some is =>
            simp only [hs] at hRange
            obtain ⟨vv, hEvalV, hInV⟩ := inferRange_sound Γ v iv env hv hEnv
            simp only [ValueInInterval, of_decide_eq_true hSort] at hInV
            obtain ⟨k, rfl, hlo, hhi⟩ := hInV
            cases k with
            | zero =>
              obtain ⟨vz, hEvalZ, hInZ⟩ := inferRange_sound Γ z iz env hz hEnv
              exact ⟨vz, eval_close_ifZero_zero hEvalV hEvalZ, valueInInterval_join_left hRange hInZ⟩
            | succ n =>
              have hPredIn : ValueInInterval (Interval.pred iv) (.nat n) :=
                ⟨n, rfl, by simp [Interval.pred]; omega, by simp [Interval.pred]; omega⟩
              obtain ⟨vs, hEvalS, hInS⟩ :=
                inferRange_sound (Interval.pred iv :: Γ) s is (.nat n :: env) hs
                  (envInIntervals_cons ⟨.refl _, .natural n⟩ hPredIn hEnv)
              exact ⟨vs, eval_close_ifZero_succ hEvalV hEvalS, valueInInterval_join_right hRange hInS⟩
        · simp [hSort] at hRange

/-! ## 4. Unified `RangeSafe` Checker & End-to-End `Core.Term` → `evalTermHw` → `RtlExpr` Bridge -/

/-- Primitives compiled by `Obend.Hardware.Compiler.compilePrim`. -/
@[expose] def isHwPrim : Primitive → Bool
  | .add | .multiply | .subtract | .equal | .conjunction | .less | .lessEqual
  | .bitAnd | .bitOr | .bitXor | .shl | .lshr | .ashr | .slt | .qmul32 => true
  | .divide | .modulo | .labelEqual => false

/-- Primitives in the Sable `F_O` integer/boolean arithmetic circuit fragment over `ℤ/Mℤ`. -/
@[expose] def isModPrim : Primitive → Bool
  | .add | .multiply | .subtract | .equal | .conjunction | .less | .lessEqual => true
  | _ => false

/-- Structural range-safety check parameterized by an allowed primitive set and upper modulus `bound`:
    certifies `hi < bound` at every subexpression and underflow-freedom (`ir.hi ≤ il.lo`) at every
    `.subtract` node. -/
def checkRangeSafeWith (primOk : Primitive → Bool) (bound : Nat) (Γ : List Interval) : Term → Bool
  | .nat n => decide (n < bound)
  | .boolean _ => decide (1 < bound)
  | .bound idx =>
    match Γ[idx]? with
    | some I => decide (I.hi < bound) && (match I.sort with | .nat => true | .bool => decide (I.hi ≤ 1 && 1 < bound))
    | none => false
  | .app (.lam subBody) arg =>
    match inferRange Γ arg with
    | some iArg =>
      decide (iArg.hi < bound) &&
      checkRangeSafeWith primOk bound Γ arg &&
      checkRangeSafeWith primOk bound (iArg :: Γ) subBody
    | none => false
  | .binary op l r =>
    primOk op &&
    checkRangeSafeWith primOk bound Γ l &&
    checkRangeSafeWith primOk bound Γ r &&
    match inferRange Γ l, inferRange Γ r with
    | some il, some ir =>
      match inferPrimRange op il ir with
      | some iOut => decide (iOut.hi < bound) && (if op == .subtract then decide (ir.hi ≤ il.lo) else true)
      | none => false
    | _, _ => false
  | .ifBool c t f =>
    checkRangeSafeWith primOk bound Γ c &&
    checkRangeSafeWith primOk bound Γ t &&
    checkRangeSafeWith primOk bound Γ f &&
    match inferRange Γ (.ifBool c t f) with
    | some iOut => decide (iOut.hi < bound)
    | none => false
  | .ifZero v z s =>
    match inferRange Γ v, inferRange Γ (.ifZero v z s) with
    | some iv, some iOut =>
      decide (iOut.hi < bound) &&
      checkRangeSafeWith primOk bound Γ v &&
      checkRangeSafeWith primOk bound Γ z &&
      checkRangeSafeWith primOk bound (Interval.pred iv :: Γ) s
    | _, _ => false
  | _ => false

/-- 64-bit hardware `RangeSafe` checker (`bound = 2^64`, underflow-free subtraction). -/
@[expose] def checkRangeSafeHw (Γ : List Interval) (t : Term) : Bool :=
  checkRangeSafeWith isHwPrim (2 ^ 64) Γ t

/-- Modular / prime-field `RangeSafe` checker for modulus `M > 1` (`bound = M`, underflow-free subtraction). -/
@[expose] def checkRangeSafeMod (M : Nat) (Γ : List Interval) (t : Term) : Bool :=
  decide (1 < M) && checkRangeSafeWith isModPrim M Γ t

theorem checkRangeSafeWith_implies_inferRange
    {primOk : Primitive → Bool} {bound : Nat} {Γ : List Interval} {t : Term}
    (hSafe : checkRangeSafeWith primOk bound Γ t = true) :
    ∃ I : Interval, inferRange Γ t = some I ∧ I.hi < bound := by
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .record _ | .get _ _ | .inject _ _ | .case _ _
  | .perform _ | .done _ | .split _ _ _ => simp [checkRangeSafeWith] at hSafe
  | .nat n => simp only [checkRangeSafeWith, decide_eq_true_eq] at hSafe; exact ⟨_, rfl, hSafe⟩
  | .boolean b =>
    simp only [checkRangeSafeWith, decide_eq_true_eq] at hSafe
    cases b
    · exact ⟨{ lo := 0, hi := 0, sort := .bool, wf := Nat.le_refl 0 }, rfl, Nat.zero_lt_of_lt hSafe⟩
    · exact ⟨{ lo := 1, hi := 1, sort := .bool, wf := Nat.le_refl 1 }, rfl, hSafe⟩
  | .bound idx =>
    simp only [checkRangeSafeWith] at hSafe
    cases hGet : Γ[idx]? with
    | none => simp [hGet] at hSafe
    | some I =>
      simp only [hGet, Bool.and_eq_true, decide_eq_true_eq] at hSafe
      exact ⟨I, by simp [inferRange, hGet], hSafe.1⟩
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [checkRangeSafeWith] at hSafe
      cases hArg : inferRange Γ arg with
      | none => simp [hArg] at hSafe
      | some iArg =>
        simp only [hArg, Bool.and_eq_true] at hSafe
        obtain ⟨iBody, hBody, hLt⟩ := checkRangeSafeWith_implies_inferRange hSafe.2
        exact ⟨iBody, by simp [inferRange, hArg, hBody], hLt⟩
    | _ => simp [checkRangeSafeWith] at hSafe
  | .binary op l r =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafe
    obtain ⟨⟨⟨_, hSafeL⟩, hSafeR⟩, hRest⟩ := hSafe
    obtain ⟨il, hl, _⟩ := checkRangeSafeWith_implies_inferRange hSafeL
    obtain ⟨ir, hr, _⟩ := checkRangeSafeWith_implies_inferRange hSafeR
    simp only [hl, hr] at hRest
    cases hOut : inferPrimRange op il ir with
    | none => simp [hOut] at hRest
    | some iOut =>
      simp only [hOut, Bool.and_eq_true, decide_eq_true_eq] at hRest
      exact ⟨iOut, by simp [inferRange, hl, hr, hOut], hRest.1⟩
  | .ifBool c tBranch fBranch =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafe
    cases hOut : inferRange Γ (.ifBool c tBranch fBranch) with
    | none => simp [hOut] at hSafe
    | some iOut => have hJoin := hSafe.2; simp only [hOut, decide_eq_true_eq] at hJoin; exact ⟨iOut, rfl, hJoin⟩
  | .ifZero v z s =>
    simp only [checkRangeSafeWith] at hSafe
    cases hv : inferRange Γ v with
    | none => simp [hv] at hSafe
    | some iv =>
      cases hOut : inferRange Γ (.ifZero v z s) with
      | none => simp [hv, hOut] at hSafe
      | some iOut => simp only [hv, hOut, Bool.and_eq_true, decide_eq_true_eq] at hSafe; exact ⟨iOut, rfl, hSafe.1.1.1⟩

def HwEnvAgrees (Γ : List Interval) (env : List Term) (varVals : List (BitVec 64)) : Prop :=
  EnvInIntervals Γ env ∧ Γ.length ≤ varVals.length ∧
    ∀ (idx : Nat) (I : Interval), Γ[idx]? = some I →
      ∃ e v, env[idx]? = some e ∧ Evaluates e v ∧ ValueInInterval I v ∧
        varVals[idx]? = some (BitVec.ofNat 64 (scalarToNat v))

theorem hwEnvAgrees_nil : HwEnvAgrees [] [] [] := ⟨envInIntervals_nil, Nat.le_refl 0, fun _ _ h => by simp at h⟩

theorem hwEnvAgrees_cons {I : Interval} {Γ : List Interval}
    {e v : Term} {env : List Term} {varVals : List (BitVec 64)}
    (he : Evaluates e v) (hv : ValueInInterval I v) (hAgree : HwEnvAgrees Γ env varVals) :
    HwEnvAgrees (I :: Γ) (e :: env) (BitVec.ofNat 64 (scalarToNat v) :: varVals) := by
  refine ⟨envInIntervals_cons he hv hAgree.1, Nat.succ_le_succ hAgree.2.1, fun idx J hJ => ?_⟩
  cases idx with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hJ; subst hJ; exact ⟨e, v, rfl, he, hv, rfl⟩
  | succ k => simp only [List.getElem?_cons_succ] at hJ ⊢; exact hAgree.2.2 k J hJ

/-- Completeness of `compileTerm` on `checkRangeSafeHw`-accepted terms. -/
theorem compileTerm_complete_of_rangeSafeHw
    (slots : List String) (slotBodies : List RtlExpr)
    (selfDepth : Nat) (Γ : List Interval) (varEnv : List RtlExpr) (t : Term)
    (hSafe : checkRangeSafeHw Γ t = true) (hLen : Γ.length ≤ varEnv.length) :
    ∃ rtl : RtlExpr, compileTerm slots slotBodies selfDepth varEnv t = some rtl := by
  unfold checkRangeSafeHw at hSafe
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .record _ | .get _ _ | .inject _ _ | .case _ _
  | .perform _ | .done _ | .split _ _ _ => simp [checkRangeSafeWith] at hSafe
  | .nat _ | .boolean _ => exact ⟨_, rfl⟩
  | .bound idx =>
    simp only [checkRangeSafeWith] at hSafe
    cases hGet : Γ[idx]? with
    | none => simp [hGet] at hSafe
    | some _ =>
      have hVarLt : idx < varEnv.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hGet).1 hLen
      exact ⟨varEnv[idx], by simp [compileTerm, hVarLt]⟩
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [checkRangeSafeWith] at hSafe
      cases hArg : inferRange Γ arg with
      | none => simp [hArg] at hSafe
      | some iArg =>
        simp only [hArg, Bool.and_eq_true] at hSafe
        obtain ⟨eArg, heArg⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies selfDepth Γ varEnv arg hSafe.1.2 hLen
        obtain ⟨eBody, heBody⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies
          (selfDepth + 1) (iArg :: Γ) (eArg :: varEnv) subBody hSafe.2 (Nat.succ_le_succ hLen)
        exact ⟨eBody, by simp [compileTerm, heArg, heBody]⟩
    | _ => simp [checkRangeSafeWith] at hSafe
  | .binary op l r =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafe
    obtain ⟨⟨⟨hPrimOk, hSafeL⟩, hSafeR⟩, _⟩ := hSafe
    obtain ⟨el, hel⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies selfDepth Γ varEnv l hSafeL hLen
    obtain ⟨er, her⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies selfDepth Γ varEnv r hSafeR hLen
    simp only [compileTerm, hel, her]; cases op <;> simp [isHwPrim, compilePrim] at hPrimOk ⊢
  | .ifBool c tBranch fBranch =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafe
    obtain ⟨⟨⟨hSafeC, hSafeT⟩, hSafeF⟩, _⟩ := hSafe
    obtain ⟨ec, hec⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies selfDepth Γ varEnv c hSafeC hLen
    obtain ⟨et, het⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies selfDepth Γ varEnv tBranch hSafeT hLen
    obtain ⟨ef, hef⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies selfDepth Γ varEnv fBranch hSafeF hLen
    exact ⟨.mux ec et ef, by simp [compileTerm, hec, het, hef]⟩
  | .ifZero v z s =>
    simp only [checkRangeSafeWith] at hSafe
    cases hv : inferRange Γ v with
    | none => simp [hv] at hSafe
    | some iv =>
      cases hOut : inferRange Γ (.ifZero v z s) with
      | none => simp [hv, hOut] at hSafe
      | some _ =>
        simp only [hv, hOut, Bool.and_eq_true] at hSafe
        obtain ⟨⟨⟨_, hSafeV⟩, hSafeZ⟩, hSafeS⟩ := hSafe
        obtain ⟨ev, hev⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies selfDepth Γ varEnv v hSafeV hLen
        obtain ⟨ez, hez⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies selfDepth Γ varEnv z hSafeZ hLen
        obtain ⟨es, hes⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies
          (selfDepth + 1) (Interval.pred iv :: Γ) (RtlExpr.alu .sub ev (.const 1#64) :: varEnv)
          s hSafeS (Nat.succ_le_succ hLen)
        exact ⟨.mux (.alu .eq ev (.const 0#64)) ez es, by simp [compileTerm, hev, hez, hes]⟩

/-- Totality of `evalTermHw` on any `checkRangeSafeHw`-accepted term. -/
theorem evalTermHw_total_of_rangeSafeHw
    (slots : List String) (slotBodies : List RtlExpr) (inputs wires regs : Nat → BitVec 64)
    (selfDepth : Nat) (Γ : List Interval) (varVals : List (BitVec 64)) (t : Term)
    (hSafe : checkRangeSafeHw Γ t = true) (hLen : Γ.length ≤ varVals.length) :
    ∃ w : BitVec 64, evalTermHw slots slotBodies inputs wires regs selfDepth varVals t = some w := by
  let varEnv := varVals.map RtlExpr.const
  obtain ⟨rtl, hComp⟩ := compileTerm_complete_of_rangeSafeHw slots slotBodies selfDepth Γ varEnv t hSafe (by simp [varEnv, hLen])
  have hSound := compileTerm_sound inputs wires regs slots slotBodies t selfDepth varEnv rtl hComp
  have hMap : varEnv.map (evalRtlExpr inputs wires regs) = varVals := by simp [varEnv, List.map_map]; exact List.map_id varVals
  rw [hMap] at hSound; exact ⟨evalRtlExpr inputs wires regs rtl, hSound⟩

private theorem bv64_ofNat_toNat (w : BitVec 64) : BitVec.ofNat 64 w.toNat = w :=
  BitVec.eq_of_toNat_eq (by simp)

private theorem evalPrimHw_agrees_of_rangeSafe
    {op : Primitive} {il ir iOut : Interval} {vl vr vOut : Term}
    (hHwOk : isHwPrim op = true) (hPrimRange : inferPrimRange op il ir = some iOut)
    (hLtL : il.hi < 2 ^ 64) (hLtR : ir.hi < 2 ^ 64)
    (hSubSafe : (if op == .subtract then decide (ir.hi ≤ il.lo) else true) = true)
    (hvl : ValueInInterval il vl) (hvr : ValueInInterval ir vr)
    (hPrimRes : primitiveResult op vl vr = some vOut) :
    evalPrimHw op (BitVec.ofNat 64 (scalarToNat vl)) (BitVec.ofNat 64 (scalarToNat vr)) =
      some (BitVec.ofNat 64 (scalarToNat vOut)) := by
  cases op with
  | divide | modulo | labelEqual => simp [isHwPrim] at hHwOk
  | conjunction =>
    simp only [inferPrimRange] at hPrimRange
    by_cases hs : il.sort == .bool && ir.sort == .bool
    · simp only [Bool.and_eq_true, beq_iff_eq] at hs
      simp only [ValueInInterval, hs.1] at hvl; simp only [ValueInInterval, hs.2] at hvr
      obtain ⟨ba, rfl, _, _⟩ := hvl; obtain ⟨bb, rfl, _, _⟩ := hvr
      simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
      cases ba <;> cases bb <;> rfl
    · simp [hs] at hPrimRange
  | add =>
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    dsimp only [scalarToNat, evalPrimHw]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]
  | multiply =>
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    dsimp only [scalarToNat, evalPrimHw]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod]
  | subtract =>
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    have hNoUnderflow : ir.hi ≤ il.lo := by simpa using hSubSafe
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, hal, hah⟩ := hvl; obtain ⟨nb, rfl, _, hbh⟩ := hvr
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    have hna : na < 2 ^ 64 := Nat.lt_of_le_of_lt hah hLtL
    have hnb : nb < 2 ^ 64 := Nat.lt_of_le_of_lt hbh hLtR
    have hsub : na - nb < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le na nb) hna
    have hle : nb ≤ na := Nat.le_trans hbh (Nat.le_trans hNoUnderflow hal)
    dsimp only [scalarToNat, evalPrimHw]; congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna, Nat.mod_eq_of_lt hnb, Nat.mod_eq_of_lt hsub]
    have hEq : 2 ^ 64 - nb + na = (na - nb) + 2 ^ 64 * 1 := by omega
    rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsub]
  | equal =>
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, _, hbh⟩ := hvr
    have hna : na < 2 ^ 64 := Nat.lt_of_le_of_lt hah hLtL; have hnb : nb < 2 ^ 64 := Nat.lt_of_le_of_lt hbh hLtR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    dsimp only [scalarToNat, evalPrimHw]; congr 1
    by_cases hEq : na = nb
    · subst hEq; simp
    · have hBvNe : (BitVec.ofNat 64 na == BitVec.ofNat 64 nb) = false := by
        apply Bool.eq_false_iff.2; intro hBv; have ht := congrArg BitVec.toNat (of_decide_eq_true hBv)
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna, Nat.mod_eq_of_lt hnb] at ht; exact hEq ht
      rw [hBvNe, beq_eq_false_iff_ne.2 hEq]; rfl
  | less =>
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, _, hbh⟩ := hvr
    have hna : na < 2 ^ 64 := Nat.lt_of_le_of_lt hah hLtL; have hnb : nb < 2 ^ 64 := Nat.lt_of_le_of_lt hbh hLtR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes; dsimp only [scalarToNat, evalPrimHw]; congr 1
    have hUlt : BitVec.ult (BitVec.ofNat 64 na) (BitVec.ofNat 64 nb) = decide (na < nb) := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna, Nat.mod_eq_of_lt hnb]
    rw [hUlt]; cases decide (na < nb) <;> rfl
  | lessEqual =>
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, _, hbh⟩ := hvr
    have hna : na < 2 ^ 64 := Nat.lt_of_le_of_lt hah hLtL; have hnb : nb < 2 ^ 64 := Nat.lt_of_le_of_lt hbh hLtR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes; dsimp only [scalarToNat, evalPrimHw]; congr 1
    have hUlt : BitVec.ult (BitVec.ofNat 64 nb) (BitVec.ofNat 64 na) = decide (nb < na) := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hna, Nat.mod_eq_of_lt hnb]
    rw [hUlt]; by_cases hle : na ≤ nb
    · have hnot : ¬ (nb < na) := by omega
      simp [hle, hnot]
    · have hlt : nb < na := by omega
      simp [hle, hlt]
  | slt =>
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    dsimp only [scalarToNat, evalPrimHw, word64]; cases BitVec.slt (BitVec.ofNat 64 na) (BitVec.ofNat 64 nb) <;> rfl
  | lshr =>
    simp only [inferPrimRange] at hPrimRange
    have hSorts : il.sort = .nat ∧ ir.sort = .nat := by
      split at hPrimRange <;> (obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange; exact ⟨hsl, hsr⟩)
    simp only [ValueInInterval, hSorts.1] at hvl; simp only [ValueInInterval, hSorts.2] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    dsimp only [evalPrimHw, scalarToNat, word64]; rw [bv64_ofNat_toNat]
  | bitAnd | bitOr | bitXor | shl | ashr | qmul32 =>
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    dsimp only [evalPrimHw, scalarToNat, word64, qmul32Bv]; rw [bv64_ofNat_toNat]

/-- **Exact `Core.Term` ↔ `evalTermHw` Bridge (`evaluates_eq_evalTermHw_of_rangeSafe`)**:
    When `checkRangeSafeHw Γ t = true` and `HwEnvAgrees Γ env varVals`, closing `t` under `env`
    evaluates in unbounded `Core.Term` to a scalar value `v` with `scalarToNat v < 2^64` whose
    64-bit word `BitVec.ofNat 64 (scalarToNat v)` agrees identically with `evalTermHw`
    (`w.toNat = scalarToNat v`). -/
theorem evaluates_eq_evalTermHw_of_rangeSafe
    (slots : List String) (slotBodies : List RtlExpr) (inputs wires regs : Nat → BitVec 64)
    (selfDepth : Nat) (Γ : List Interval) (env : List Term) (varVals : List (BitVec 64)) (t : Term)
    (hSafe : checkRangeSafeHw Γ t = true) (hAgree : HwEnvAgrees Γ env varVals) :
    ∃ (I : Interval) (v : Term) (w : BitVec 64),
      inferRange Γ t = some I ∧ Evaluates (closeTerm env t) v ∧ ValueInInterval I v ∧
      evalTermHw slots slotBodies inputs wires regs selfDepth varVals t = some w ∧
      w = BitVec.ofNat 64 (scalarToNat v) ∧ w.toNat = scalarToNat v := by
  obtain ⟨I, hInfer, hHiLt⟩ := checkRangeSafeWith_implies_inferRange hSafe
  obtain ⟨v, hEval, hValIn⟩ := inferRange_sound Γ t I env hInfer hAgree.1
  have hValLt : scalarToNat v < 2 ^ 64 := Nat.lt_of_le_of_lt (valueInInterval_bounds hValIn).2 hHiLt
  suffices hHw : evalTermHw slots slotBodies inputs wires regs selfDepth varVals t =
      some (BitVec.ofNat 64 (scalarToNat v)) by
    refine ⟨I, v, BitVec.ofNat 64 (scalarToNat v), hInfer, hEval, hValIn, hHw, rfl, ?_⟩
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hValLt]
  unfold checkRangeSafeHw at hSafe
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .record _ | .get _ _ | .inject _ _ | .case _ _
  | .perform _ | .done _ | .split _ _ _ => simp [checkRangeSafeWith] at hSafe
  | .nat n => rw [closeTerm_nat] at hEval; obtain rfl := evaluates_deterministic hEval ⟨.refl _, .natural n⟩; rfl
  | .boolean b => rw [closeTerm_bool] at hEval; obtain rfl := evaluates_deterministic hEval ⟨.refl _, .boolean b⟩; cases b <;> rfl
  | .bound idx =>
    simp only [inferRange] at hInfer
    obtain ⟨e, vEnv, hEnvGet, hEnvEval, _, hVarGet⟩ := hAgree.2.2 idx I hInfer
    simp only [closeTerm, Term.substitute, envSubst, hEnvGet] at hEval
    obtain rfl := evaluates_deterministic hEval hEnvEval; simp [evalTermHw, hVarGet]
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [checkRangeSafeWith] at hSafe
      cases hArg : inferRange Γ arg with
      | none => simp [hArg] at hSafe
      | some iArg =>
        simp only [hArg, Bool.and_eq_true] at hSafe
        obtain ⟨iArg', vArg, wArg, hArg', hEvalArg, hInArg, hHwArg, rfl, _⟩ :=
          evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs selfDepth Γ env varVals arg hSafe.1.2 hAgree
        rw [hArg] at hArg'; injection hArg' with hEqI; subst hEqI
        obtain ⟨_, vBody, wBody, _, hEvalBody, _, hHwBody, rfl, _⟩ :=
          evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs (selfDepth + 1)
            (iArg :: Γ) (closeTerm env arg :: env) (BitVec.ofNat 64 (scalarToNat vArg) :: varVals)
            subBody hSafe.2 (hwEnvAgrees_cons hEvalArg hInArg hAgree)
        obtain rfl := evaluates_deterministic hEval (eval_close_let hEvalBody); simp [evalTermHw, hHwArg, hHwBody]
    | _ => simp [checkRangeSafeWith] at hSafe
  | .binary op l r =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafe; obtain ⟨⟨⟨hPrimOk, hSafeL⟩, hSafeR⟩, hRest⟩ := hSafe
    obtain ⟨il, vl, wl, hl, hEvalL, hInL, hHwL, rfl, _⟩ :=
      evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs selfDepth Γ env varVals l hSafeL hAgree
    obtain ⟨ir, vr, wr, hr, hEvalR, hInR, hHwR, rfl, _⟩ :=
      evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs selfDepth Γ env varVals r hSafeR hAgree
    obtain ⟨_, hl', hLtL⟩ := checkRangeSafeWith_implies_inferRange hSafeL
    obtain ⟨_, hr', hLtR⟩ := checkRangeSafeWith_implies_inferRange hSafeR
    rw [hl] at hl'; injection hl' with hEqL; subst hEqL; rw [hr] at hr'; injection hr' with hEqR; subst hEqR
    simp only [inferRange, hl, hr] at hInfer; simp only [hl, hr, hInfer, Bool.and_eq_true] at hRest
    obtain ⟨vOut, hPrimRes, hInOut⟩ := inferPrimRange_sound hInfer hInL hInR
    obtain rfl := evaluates_deterministic hEval (eval_close_binary hEvalL hEvalR hPrimRes (valueInInterval_is_value hInOut))
    simp only [evalTermHw, hHwL, hHwR]
    exact evalPrimHw_agrees_of_rangeSafe hPrimOk hInfer hLtL hLtR hRest.2 hInL hInR hPrimRes
  | .ifBool c tBranch fBranch =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafe
    obtain ⟨⟨⟨hSafeC, hSafeT⟩, hSafeF⟩, _⟩ := hSafe
    obtain ⟨ic, vc, wc, hc, hEvalC, hInC, hHwC, rfl, _⟩ :=
      evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs selfDepth Γ env varVals c hSafeC hAgree
    obtain ⟨it, vt, wt, ht, hEvalT, _, hHwT, rfl, _⟩ :=
      evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs selfDepth Γ env varVals tBranch hSafeT hAgree
    obtain ⟨iff, vf, wf, hf, hEvalF, _, hHwF, rfl, _⟩ :=
      evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs selfDepth Γ env varVals fBranch hSafeF hAgree
    simp only [inferRange, hc, ht, hf] at hInfer
    by_cases hSort : ic.sort == .bool
    · simp only [ValueInInterval, of_decide_eq_true hSort] at hInC; obtain ⟨b, rfl, _, _⟩ := hInC
      cases b
      · obtain rfl := evaluates_deterministic hEval (eval_close_ifFalse hEvalC hEvalF)
        simp [evalTermHw, hHwC, hHwT, hHwF, scalarToNat]
      · obtain rfl := evaluates_deterministic hEval (eval_close_ifTrue hEvalC hEvalT)
        simp [evalTermHw, hHwC, hHwT, hHwF, scalarToNat]
    · simp [hSort] at hInfer
  | .ifZero vCond z s =>
    simp only [checkRangeSafeWith] at hSafe
    cases hv : inferRange Γ vCond with
    | none => simp [hv] at hSafe
    | some iv =>
      rw [hInfer] at hSafe; simp only [hv, Bool.and_eq_true] at hSafe
      obtain ⟨⟨⟨_, hSafeV⟩, hSafeZ⟩, hSafeS⟩ := hSafe
      obtain ⟨iv', vv, wv, hv', hEvalV, hInV, hHwV, rfl, _⟩ :=
        evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs selfDepth Γ env varVals vCond hSafeV hAgree
      rw [hv] at hv'; injection hv' with hEqIv; subst hEqIv
      obtain ⟨_, vz, wz, hz, hEvalZ, _, hHwZ, rfl, _⟩ :=
        evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs selfDepth Γ env varVals z hSafeZ hAgree
      obtain ⟨_, hv'', hLtV⟩ := checkRangeSafeWith_implies_inferRange hSafeV
      rw [hv] at hv''; injection hv'' with hEqIv2; subst hEqIv2
      simp only [inferRange, hv, hz] at hInfer
      by_cases hSort : iv.sort == .nat
      · simp only [ValueInInterval, of_decide_eq_true hSort] at hInV; obtain ⟨k, rfl, hlo, hhi⟩ := hInV
        cases k with
        | zero =>
          obtain ⟨ws, hHwS⟩ := evalTermHw_total_of_rangeSafeHw slots slotBodies inputs wires regs
            (selfDepth + 1) (Interval.pred iv :: Γ) (18446744073709551615#64 :: varVals) s hSafeS (Nat.succ_le_succ hAgree.2.1)
          obtain rfl := evaluates_deterministic hEval (eval_close_ifZero_zero hEvalV hEvalZ)
          dsimp only [scalarToNat] at hHwV; simp [evalTermHw, hHwV, hHwZ, hHwS]
        | succ n =>
          have hSuccLt : n + 1 < 2 ^ 64 := Nat.lt_of_le_of_lt hhi hLtV
          have hPredLt : n < 2 ^ 64 := Nat.lt_of_succ_lt hSuccLt
          have hPredIn : ValueInInterval (Interval.pred iv) (.nat n) :=
            ⟨n, rfl, by simp [Interval.pred]; omega, by simp [Interval.pred]; omega⟩
          obtain ⟨_, vs, ws, _, hEvalS, _, hHwS, rfl, _⟩ :=
            evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs (selfDepth + 1)
              (Interval.pred iv :: Γ) (.nat n :: env) (BitVec.ofNat 64 n :: varVals)
              s hSafeS (hwEnvAgrees_cons ⟨.refl _, .natural n⟩ hPredIn hAgree)
          have hSub1 : BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSuccLt, Nat.mod_eq_of_lt hPredLt]
            have h1lt : 1 < 2 ^ 64 := by decide
            rw [Nat.mod_eq_of_lt h1lt]
            have hEq : 2 ^ 64 - 1 + (n + 1) = n + 2 ^ 64 * 1 := by omega
            rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hPredLt]
          have hNeZero : (BitVec.ofNat 64 (n + 1) == 0#64) = false := by
            apply Bool.eq_false_iff.2; intro hEq0
            have ht := congrArg BitVec.toNat (of_decide_eq_true hEq0)
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hSuccLt] at ht; omega
          obtain rfl := evaluates_deterministic hEval (eval_close_ifZero_succ hEvalV hEvalS)
          dsimp only [scalarToNat] at hHwV hHwS ⊢
          simp [evalTermHw, hHwV, hHwZ, hSub1, hHwS, hNeZero]
      · simp [hSort] at hInfer

/-- **Full End-to-End `Core.Term` → `RtlExpr` Soundness Bridge (`compileTerm_evaluates_sound`)**. -/
theorem compileTerm_evaluates_sound
    (inputs wires regs : Nat → BitVec 64) (slots : List String) (slotBodies : List RtlExpr)
    (selfDepth : Nat) (Γ : List Interval) (env : List Term) (varEnv : List RtlExpr)
    (t : Term) (rtl : RtlExpr)
    (hSafe : checkRangeSafeHw Γ t = true)
    (hCompile : compileTerm slots slotBodies selfDepth varEnv t = some rtl)
    (hAgree : HwEnvAgrees Γ env (varEnv.map (evalRtlExpr inputs wires regs))) :
    ∃ (I : Interval) (v : Term),
      inferRange Γ t = some I ∧ Evaluates (closeTerm env t) v ∧ ValueInInterval I v ∧
      evalRtlExpr inputs wires regs rtl = BitVec.ofNat 64 (scalarToNat v) ∧
      (evalRtlExpr inputs wires regs rtl).toNat = scalarToNat v := by
  have hRtl := compileTerm_sound inputs wires regs slots slotBodies t selfDepth varEnv rtl hCompile
  obtain ⟨I, v, w, hInfer, hEval, hValIn, hHw, hwEq, hToNat⟩ :=
    evaluates_eq_evalTermHw_of_rangeSafe slots slotBodies inputs wires regs selfDepth
      Γ env (varEnv.map (evalRtlExpr inputs wires regs)) t hSafe hAgree
  rw [hRtl] at hHw; injection hHw with hwRtl; subst hwRtl
  exact ⟨I, v, hInfer, hEval, hValIn, hwEq, hToNat⟩

/-! ## 5. Sable `F_O` ZK No-Wrap Prime-Field Bridge (`evalMod`, `evaluates_mod_prime_exact_of_rangeSafe`) -/

/-- The 31-bit KoalaBear STARK prime `p = 2^31 - 2^24 + 1 = 2130706433` (`Sable` `arXiv:2611.14083`). -/
@[expose] def koalaBearPrime : Nat := 2130706433
/-- The 31-bit BabyBear STARK prime `p = 2^31 - 2^27 + 1 = 2013265921`. -/
@[expose] def babyBearPrime : Nat := 2013265921

theorem koalaBearPrime_spec :
    koalaBearPrime = 2 ^ 31 - 2 ^ 24 + 1 ∧ 1 < koalaBearPrime ∧
    babyBearPrime = 2 ^ 31 - 2 ^ 27 + 1 ∧ 1 < babyBearPrime :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Modular primitive semantics in `ℤ/Mℤ` for the Sable `F_O` arithmetic/comparison fragment.
    Notice `.subtract` performs ring subtraction `(vl % M + M - vr % M) % M` (never truncated `Nat.sub`),
    and `.conjunction` performs polynomial multiplication `(vl * vr) % M`. -/
def evalPrimMod (M : Nat) (op : Primitive) (vl vr : Nat) : Option Nat :=
  match op with
  | .add         => some ((vl + vr) % M)
  | .multiply    => some ((vl * vr) % M)
  | .subtract    => some ((vl % M + M - vr % M) % M)
  | .conjunction => some ((vl * vr) % M)
  | .equal       => some (if vl % M == vr % M then 1 % M else 0)
  | .less        => some (if decide (vl % M < vr % M) then 1 % M else 0)
  | .lessEqual   => some (if decide (vl % M ≤ vr % M) then 1 % M else 0)
  | _            => none

def evalMod (M : Nat) (modVals : List Nat) : Term → Option Nat
  | .nat n => some (n % M)
  | .boolean b => some ((if b then 1 else 0) % M)
  | .bound idx => match modVals[idx]? with | some v => some (v % M) | none => none
  | .app (.lam subBody) arg =>
    match evalMod M modVals arg with | some vArg => evalMod M (vArg :: modVals) subBody | none => none
  | .binary op l r =>
    match evalMod M modVals l, evalMod M modVals r with | some vl, some vr => evalPrimMod M op vl vr | _, _ => none
  | .ifBool c t f =>
    match evalMod M modVals c, evalMod M modVals t, evalMod M modVals f with
    | some vc, some vt, some vf => some ((vc * vt + (M + 1 - vc % M) * vf) % M)
    | _, _, _ => none
  | .ifZero v z s =>
    match evalMod M modVals v, evalMod M modVals z with
    | some vv, some vz =>
      match evalMod M (((vv % M + M - 1) % M) :: modVals) s with
      | some vs => let zBit := if vv % M == 0 then 1 else 0; some ((zBit * vz + (M + 1 - zBit) * vs) % M)
      | none => none
    | _, _ => none
  | _ => none

def ModEnvAgrees (M : Nat) (Γ : List Interval) (env : List Term) (modVals : List Nat) : Prop :=
  EnvInIntervals Γ env ∧ Γ.length ≤ modVals.length ∧
    ∀ (idx : Nat) (I : Interval), Γ[idx]? = some I →
      ∃ e v, env[idx]? = some e ∧ Evaluates e v ∧ ValueInInterval I v ∧
        modVals[idx]? = some (scalarToNat v % M)

theorem modEnvAgrees_nil (M : Nat) : ModEnvAgrees M [] [] [] :=
  ⟨envInIntervals_nil, Nat.le_refl 0, fun _ _ h => by simp at h⟩

theorem modEnvAgrees_cons {M : Nat} {I : Interval} {Γ : List Interval}
    {e v : Term} {env : List Term} {modVals : List Nat}
    (he : Evaluates e v) (hv : ValueInInterval I v) (hAgree : ModEnvAgrees M Γ env modVals) :
    ModEnvAgrees M (I :: Γ) (e :: env) ((scalarToNat v % M) :: modVals) := by
  refine ⟨envInIntervals_cons he hv hAgree.1, Nat.succ_le_succ hAgree.2.1, fun idx J hJ => ?_⟩
  cases idx with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hJ; subst hJ; exact ⟨e, v, rfl, he, hv, rfl⟩
  | succ k => simp only [List.getElem?_cons_succ] at hJ ⊢; exact hAgree.2.2 k J hJ

/-- Totality of `evalMod M` on any `checkRangeSafeMod M`-accepted term. -/
theorem evalMod_total_of_rangeSafeMod
    (M : Nat) (Γ : List Interval) (modVals : List Nat) (t : Term)
    (hSafe : checkRangeSafeMod M Γ t = true) (hLen : Γ.length ≤ modVals.length) :
    ∃ r : Nat, evalMod M modVals t = some r := by
  simp only [checkRangeSafeMod, Bool.and_eq_true, decide_eq_true_eq] at hSafe
  rcases hSafe with ⟨hM, hSafeW⟩
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .record _ | .get _ _ | .inject _ _ | .case _ _
  | .perform _ | .done _ | .split _ _ _ => simp [checkRangeSafeWith] at hSafeW
  | .nat _ | .boolean _ => exact ⟨_, rfl⟩
  | .bound idx =>
    simp only [checkRangeSafeWith] at hSafeW
    cases hGet : Γ[idx]? with
    | none => simp [hGet] at hSafeW
    | some _ =>
      have hModLt : idx < modVals.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hGet).1 hLen
      exact ⟨modVals[idx] % M, by simp [evalMod, hModLt]⟩
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [checkRangeSafeWith] at hSafeW
      cases hArg : inferRange Γ arg with
      | none => simp [hArg] at hSafeW
      | some iArg =>
        simp only [hArg, Bool.and_eq_true] at hSafeW
        obtain ⟨rArg, hrArg⟩ := evalMod_total_of_rangeSafeMod M Γ modVals arg (by simp [checkRangeSafeMod, hM, hSafeW.1.2]) hLen
        obtain ⟨rBody, hrBody⟩ := evalMod_total_of_rangeSafeMod M (iArg :: Γ) (rArg :: modVals) subBody (by simp [checkRangeSafeMod, hM, hSafeW.2]) (Nat.succ_le_succ hLen)
        exact ⟨rBody, by simp [evalMod, hrArg, hrBody]⟩
    | _ => simp [checkRangeSafeWith] at hSafeW
  | .binary op l r =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafeW
    obtain ⟨⟨⟨hPrimOk, hSafeL⟩, hSafeR⟩, _⟩ := hSafeW
    obtain ⟨rl, hrl⟩ := evalMod_total_of_rangeSafeMod M Γ modVals l (by simp [checkRangeSafeMod, hM, hSafeL]) hLen
    obtain ⟨rr, hrr⟩ := evalMod_total_of_rangeSafeMod M Γ modVals r (by simp [checkRangeSafeMod, hM, hSafeR]) hLen
    simp only [evalMod, hrl, hrr]; cases op <;> simp [isModPrim, evalPrimMod] at hPrimOk ⊢
  | .ifBool c tBranch fBranch =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafeW
    obtain ⟨⟨⟨hSafeC, hSafeT⟩, hSafeF⟩, _⟩ := hSafeW
    obtain ⟨rc, hrc⟩ := evalMod_total_of_rangeSafeMod M Γ modVals c (by simp [checkRangeSafeMod, hM, hSafeC]) hLen
    obtain ⟨rt, hrt⟩ := evalMod_total_of_rangeSafeMod M Γ modVals tBranch (by simp [checkRangeSafeMod, hM, hSafeT]) hLen
    obtain ⟨rf, hrf⟩ := evalMod_total_of_rangeSafeMod M Γ modVals fBranch (by simp [checkRangeSafeMod, hM, hSafeF]) hLen
    exact ⟨_, by simp only [evalMod, hrc, hrt, hrf]; rfl⟩
  | .ifZero v z s =>
    simp only [checkRangeSafeWith] at hSafeW
    cases hv : inferRange Γ v with
    | none => simp [hv] at hSafeW
    | some iv =>
      cases hOut : inferRange Γ (.ifZero v z s) with
      | none => simp [hv, hOut] at hSafeW
      | some _ =>
        simp only [hv, hOut, Bool.and_eq_true] at hSafeW; obtain ⟨⟨⟨_, hSafeV⟩, hSafeZ⟩, hSafeS⟩ := hSafeW
        obtain ⟨rv, hrv⟩ := evalMod_total_of_rangeSafeMod M Γ modVals v (by simp [checkRangeSafeMod, hM, hSafeV]) hLen
        obtain ⟨rz, hrz⟩ := evalMod_total_of_rangeSafeMod M Γ modVals z (by simp [checkRangeSafeMod, hM, hSafeZ]) hLen
        obtain ⟨rs, hrs⟩ := evalMod_total_of_rangeSafeMod M (Interval.pred iv :: Γ) (((rv % M + M - 1) % M) :: modVals) s (by simp [checkRangeSafeMod, hM, hSafeS]) (Nat.succ_le_succ hLen)
        exact ⟨_, by simp only [evalMod, hrv, hrz, hrs]; rfl⟩

private theorem evalPrimMod_exact_of_rangeSafe
    {M : Nat} {op : Primitive} {il ir iOut : Interval} {vl vr vOut : Term}
    (hM : 1 < M) (hModOk : isModPrim op = true) (hPrimRange : inferPrimRange op il ir = some iOut)
    (hLtL : il.hi < M) (hLtR : ir.hi < M) (hLtOut : iOut.hi < M)
    (hSubSafe : (if op == .subtract then decide (ir.hi ≤ il.lo) else true) = true)
    (hvl : ValueInInterval il vl) (hvr : ValueInInterval ir vr)
    (hPrimRes : primitiveResult op vl vr = some vOut) (hOutIn : ValueInInterval iOut vOut) :
    evalPrimMod M op (scalarToNat vl) (scalarToNat vr) = some (scalarToNat vOut) := by
  have hOutLt : scalarToNat vOut < M := Nat.lt_of_le_of_lt (valueInInterval_bounds hOutIn).2 hLtOut
  cases op with
  | divide | modulo | labelEqual | bitAnd | bitOr | bitXor | shl | lshr | ashr | slt | qmul32 => simp [isModPrim] at hModOk
  | conjunction =>
    simp only [inferPrimRange] at hPrimRange
    by_cases hs : il.sort == .bool && ir.sort == .bool
    · simp only [Bool.and_eq_true, beq_iff_eq] at hs
      simp only [ValueInInterval, hs.1] at hvl; simp only [ValueInInterval, hs.2] at hvr
      obtain ⟨ba, rfl, _, _⟩ := hvl; obtain ⟨bb, rfl, _, _⟩ := hvr
      simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
      cases ba <;> cases bb <;> simp [evalPrimMod, scalarToNat, Nat.mod_eq_of_lt hM]
    · simp [hs] at hPrimRange
  | add =>
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    dsimp only [scalarToNat] at hOutLt ⊢; simp [evalPrimMod, Nat.mod_eq_of_lt hOutLt]
  | multiply =>
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, _⟩ := hvl; obtain ⟨nb, rfl, _, _⟩ := hvr
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    dsimp only [scalarToNat] at hOutLt ⊢; simp [evalPrimMod, Nat.mod_eq_of_lt hOutLt]
  | subtract =>
    obtain ⟨hsl, hsr, _⟩ := natOut_eq_some hPrimRange
    have hNoUnderflow : ir.hi ≤ il.lo := by simpa using hSubSafe
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, hal, hah⟩ := hvl; obtain ⟨nb, rfl, _, hbh⟩ := hvr
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes
    have hna : na < M := Nat.lt_of_le_of_lt hah hLtL; have hnb : nb < M := Nat.lt_of_le_of_lt hbh hLtR
    have hle : nb ≤ na := Nat.le_trans hbh (Nat.le_trans hNoUnderflow hal)
    have hsub : na - nb < M := Nat.lt_of_le_of_lt (Nat.sub_le na nb) hna
    dsimp only [scalarToNat, evalPrimMod]; congr 1; rw [Nat.mod_eq_of_lt hna, Nat.mod_eq_of_lt hnb]
    have hEq : na + M - nb = (na - nb) + M * 1 := by omega
    rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsub]
  | equal =>
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, _, hbh⟩ := hvr
    have hna : na < M := Nat.lt_of_le_of_lt hah hLtL; have hnb : nb < M := Nat.lt_of_le_of_lt hbh hLtR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes; dsimp only [scalarToNat, evalPrimMod]
    rw [Nat.mod_eq_of_lt hna, Nat.mod_eq_of_lt hnb, Nat.mod_eq_of_lt hM]
  | less =>
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, _, hbh⟩ := hvr
    have hna : na < M := Nat.lt_of_le_of_lt hah hLtL; have hnb : nb < M := Nat.lt_of_le_of_lt hbh hLtR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes; dsimp only [scalarToNat, evalPrimMod]
    rw [Nat.mod_eq_of_lt hna, Nat.mod_eq_of_lt hnb, Nat.mod_eq_of_lt hM]
  | lessEqual =>
    obtain ⟨hsl, hsr, _⟩ := natBoolOut_eq_some hPrimRange
    simp only [ValueInInterval, hsl] at hvl; simp only [ValueInInterval, hsr] at hvr
    obtain ⟨na, rfl, _, hah⟩ := hvl; obtain ⟨nb, rfl, _, hbh⟩ := hvr
    have hna : na < M := Nat.lt_of_le_of_lt hah hLtL; have hnb : nb < M := Nat.lt_of_le_of_lt hbh hLtR
    simp only [primitiveResult, Option.some.injEq] at hPrimRes; subst hPrimRes; dsimp only [scalarToNat, evalPrimMod]
    rw [Nat.mod_eq_of_lt hna, Nat.mod_eq_of_lt hnb, Nat.mod_eq_of_lt hM]

/-- **Sable `F_O` ZK No-Wrap Prime-Field Bridge (`evaluates_mod_prime_exact_of_rangeSafe`)**:
    For any modulus `M > 1`, when `checkRangeSafeMod M Γ t = true` and `ModEnvAgrees M Γ env modVals`,
    evaluating `t` in `ℤ/Mℤ` via `evalMod M` reconstructs the **exact** unbounded `Core.Term` integer
    result (`evalMod M modVals t = some (scalarToNat v)`) with zero modular wrap-around! -/
theorem evaluates_mod_prime_exact_of_rangeSafe
    (M : Nat) (Γ : List Interval) (env : List Term) (modVals : List Nat) (t : Term)
    (hSafe : checkRangeSafeMod M Γ t = true) (hAgree : ModEnvAgrees M Γ env modVals) :
    ∃ (I : Interval) (v : Term),
      inferRange Γ t = some I ∧ Evaluates (closeTerm env t) v ∧ ValueInInterval I v ∧
      scalarToNat v < M ∧ evalMod M modVals t = some (scalarToNat v) := by
  simp only [checkRangeSafeMod, Bool.and_eq_true, decide_eq_true_eq] at hSafe; rcases hSafe with ⟨hM, hSafeW⟩
  obtain ⟨I, hInfer, hHiLt⟩ := checkRangeSafeWith_implies_inferRange hSafeW
  obtain ⟨v, hEval, hValIn⟩ := inferRange_sound Γ t I env hInfer hAgree.1
  have hValLt : scalarToNat v < M := Nat.lt_of_le_of_lt (valueInInterval_bounds hValIn).2 hHiLt
  refine ⟨I, v, hInfer, hEval, hValIn, hValLt, ?_⟩
  match t with
  | .hole _ _ | .lam _ | .mix _ _ | .fix _ _ | .specification _ _
  | .prototype _ _ | .reflect _ | .metadata _ | .project _ | .label _
  | .extend _ _ | .record _ | .get _ _ | .inject _ _ | .case _ _
  | .perform _ | .done _ | .split _ _ _ => simp [checkRangeSafeWith] at hSafeW
  | .nat n =>
    rw [closeTerm_nat] at hEval; obtain rfl := evaluates_deterministic hEval ⟨.refl _, .natural n⟩
    dsimp only [evalMod, scalarToNat] at hValLt ⊢; rw [Nat.mod_eq_of_lt hValLt]
  | .boolean b =>
    rw [closeTerm_bool] at hEval; obtain rfl := evaluates_deterministic hEval ⟨.refl _, .boolean b⟩
    dsimp only [evalMod, scalarToNat] at hValLt ⊢; rw [Nat.mod_eq_of_lt hValLt]
  | .bound idx =>
    simp only [inferRange] at hInfer
    obtain ⟨e, vEnv, hEnvGet, hEnvEval, _, hModGet⟩ := hAgree.2.2 idx I hInfer
    simp only [closeTerm, Term.substitute, envSubst, hEnvGet] at hEval
    obtain rfl := evaluates_deterministic hEval hEnvEval; simp [evalMod, hModGet, Nat.mod_eq_of_lt hValLt]
  | .app fn arg =>
    cases fn with
    | lam subBody =>
      simp only [checkRangeSafeWith] at hSafeW
      cases hArg : inferRange Γ arg with
      | none => simp [hArg] at hSafeW
      | some iArg =>
        simp only [hArg, Bool.and_eq_true] at hSafeW
        obtain ⟨iArg', vArg, hArg', hEvalArg, hInArg, hLtArg, hModArg⟩ :=
          evaluates_mod_prime_exact_of_rangeSafe M Γ env modVals arg (by simp [checkRangeSafeMod, hM, hSafeW.1.2]) hAgree
        rw [hArg] at hArg'; injection hArg' with hEqI; subst hEqI
        have hAgree' := modEnvAgrees_cons (M := M) hEvalArg hInArg hAgree; rw [Nat.mod_eq_of_lt hLtArg] at hAgree'
        obtain ⟨_, vBody, _, hEvalBody, _, _, hModBody⟩ :=
          evaluates_mod_prime_exact_of_rangeSafe M (iArg :: Γ) (closeTerm env arg :: env)
            (scalarToNat vArg :: modVals) subBody (by simp [checkRangeSafeMod, hM, hSafeW.2]) hAgree'
        obtain rfl := evaluates_deterministic hEval (eval_close_let hEvalBody); simp [evalMod, hModArg, hModBody]
    | _ => simp [checkRangeSafeWith] at hSafeW
  | .binary op l r =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafeW
    obtain ⟨⟨⟨hPrimOk, hSafeL⟩, hSafeR⟩, hRest⟩ := hSafeW
    obtain ⟨il, vl, hl, hEvalL, hInL, _, hModL⟩ :=
      evaluates_mod_prime_exact_of_rangeSafe M Γ env modVals l (by simp [checkRangeSafeMod, hM, hSafeL]) hAgree
    obtain ⟨ir, vr, hr, hEvalR, hInR, _, hModR⟩ :=
      evaluates_mod_prime_exact_of_rangeSafe M Γ env modVals r (by simp [checkRangeSafeMod, hM, hSafeR]) hAgree
    obtain ⟨_, hl', hLtL⟩ := checkRangeSafeWith_implies_inferRange hSafeL
    obtain ⟨_, hr', hLtR⟩ := checkRangeSafeWith_implies_inferRange hSafeR
    rw [hl] at hl'; injection hl' with hEqL; subst hEqL; rw [hr] at hr'; injection hr' with hEqR; subst hEqR
    simp only [inferRange, hl, hr] at hInfer; simp only [hl, hr, hInfer, Bool.and_eq_true] at hRest
    obtain ⟨vOut, hPrimRes, hInOut⟩ := inferPrimRange_sound hInfer hInL hInR
    obtain rfl := evaluates_deterministic hEval (eval_close_binary hEvalL hEvalR hPrimRes (valueInInterval_is_value hInOut))
    simp only [evalMod, hModL, hModR]
    exact evalPrimMod_exact_of_rangeSafe hM hPrimOk hInfer hLtL hLtR hHiLt hRest.2 hInL hInR hPrimRes hInOut
  | .ifBool c tBranch fBranch =>
    simp only [checkRangeSafeWith, Bool.and_eq_true] at hSafeW; obtain ⟨⟨⟨hSafeC, hSafeT⟩, hSafeF⟩, _⟩ := hSafeW
    obtain ⟨ic, vc, hc, hEvalC, hInC, _, hModC⟩ :=
      evaluates_mod_prime_exact_of_rangeSafe M Γ env modVals c (by simp [checkRangeSafeMod, hM, hSafeC]) hAgree
    obtain ⟨it, vt, ht, hEvalT, _, _, hModT⟩ :=
      evaluates_mod_prime_exact_of_rangeSafe M Γ env modVals tBranch (by simp [checkRangeSafeMod, hM, hSafeT]) hAgree
    obtain ⟨iff, vf, hf, hEvalF, _, _, hModF⟩ :=
      evaluates_mod_prime_exact_of_rangeSafe M Γ env modVals fBranch (by simp [checkRangeSafeMod, hM, hSafeF]) hAgree
    simp only [inferRange, hc, ht, hf] at hInfer
    by_cases hSort : ic.sort == .bool
    · simp only [ValueInInterval, of_decide_eq_true hSort] at hInC; obtain ⟨b, rfl, _, _⟩ := hInC
      cases b with
      | true =>
        obtain rfl := evaluates_deterministic hEval (eval_close_ifTrue hEvalC hEvalT)
        have hC : evalMod M modVals c = some 1 := by simpa [scalarToNat] using hModC
        simp only [evalMod, hC, hModT, hModF, Nat.mod_eq_of_lt hM, Nat.one_mul, Option.some.injEq]
        have hSub : M + 1 - 1 = M := by omega
        rw [hSub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hValLt]
      | false =>
        obtain rfl := evaluates_deterministic hEval (eval_close_ifFalse hEvalC hEvalF)
        have hC : evalMod M modVals c = some 0 := by simpa [scalarToNat] using hModC
        simp only [evalMod, hC, hModT, hModF, Nat.zero_mod, Nat.zero_mul, Nat.sub_zero, Nat.zero_add, Option.some.injEq]
        have hDistr : (M + 1) * scalarToNat v = scalarToNat v + M * scalarToNat v := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rw [hDistr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hValLt]
    · simp [hSort] at hInfer
  | .ifZero vCond z s =>
    simp only [checkRangeSafeWith] at hSafeW
    cases hv : inferRange Γ vCond with
    | none => simp [hv] at hSafeW
    | some iv =>
      rw [hInfer] at hSafeW; simp only [hv, Bool.and_eq_true] at hSafeW
      obtain ⟨⟨⟨_, hSafeV⟩, hSafeZ⟩, hSafeS⟩ := hSafeW
      obtain ⟨iv', vv, hv', hEvalV, hInV, _, hModV⟩ :=
        evaluates_mod_prime_exact_of_rangeSafe M Γ env modVals vCond (by simp [checkRangeSafeMod, hM, hSafeV]) hAgree
      rw [hv] at hv'; injection hv' with hEqIv; subst hEqIv
      obtain ⟨_, vz, hz, hEvalZ, _, _, hModZ⟩ :=
        evaluates_mod_prime_exact_of_rangeSafe M Γ env modVals z (by simp [checkRangeSafeMod, hM, hSafeZ]) hAgree
      obtain ⟨_, hv'', hLtV⟩ := checkRangeSafeWith_implies_inferRange hSafeV
      rw [hv] at hv''; injection hv'' with hEqIv2; subst hEqIv2; simp only [inferRange, hv, hz] at hInfer
      by_cases hSort : iv.sort == .nat
      · simp only [ValueInInterval, of_decide_eq_true hSort] at hInV; obtain ⟨k, rfl, hlo, hhi⟩ := hInV
        cases k with
        | zero =>
          obtain ⟨rs, hModS⟩ := evalMod_total_of_rangeSafeMod M (Interval.pred iv :: Γ)
            (((0 % M + M - 1) % M) :: modVals) s (by simp [checkRangeSafeMod, hM, hSafeS]) (Nat.succ_le_succ hAgree.2.1)
          simp only [Nat.zero_mod] at hModS
          obtain rfl := evaluates_deterministic hEval (eval_close_ifZero_zero hEvalV hEvalZ)
          have hV0 : evalMod M modVals vCond = some 0 := by simpa [scalarToNat] using hModV
          simp only [evalMod, hV0, hModZ, Nat.zero_mod, hModS, beq_self_eq_true, ↓reduceIte, Nat.one_mul, Option.some.injEq]
          have hSub : M + 1 - 1 = M := by omega
          rw [hSub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hValLt]
        | succ n =>
          have hSuccLt : n + 1 < M := Nat.lt_of_le_of_lt hhi hLtV; have hPredLt : n < M := Nat.lt_of_succ_lt hSuccLt
          have hPredIn : ValueInInterval (Interval.pred iv) (.nat n) := ⟨n, rfl, by simp [Interval.pred]; omega, by simp [Interval.pred]; omega⟩
          have hAgree' := modEnvAgrees_cons (M := M) ⟨.refl _, .natural n⟩ hPredIn hAgree
          dsimp only [scalarToNat] at hAgree'; rw [Nat.mod_eq_of_lt hPredLt] at hAgree'
          obtain ⟨_, vs, _, hEvalS, _, _, hModS⟩ :=
            evaluates_mod_prime_exact_of_rangeSafe M (Interval.pred iv :: Γ) (.nat n :: env)
              (n :: modVals) s (by simp [checkRangeSafeMod, hM, hSafeS]) hAgree'
          have hPredMod : ((n + 1) % M + M - 1) % M = n := by
            rw [Nat.mod_eq_of_lt hSuccLt]; have hEq : n + 1 + M - 1 = n + M * 1 := by omega
            rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hPredLt]
          have hNeZero : ((n + 1) % M == 0) = false := by rw [Nat.mod_eq_of_lt hSuccLt]; exact beq_eq_false_iff_ne.2 (by omega)
          obtain rfl := evaluates_deterministic hEval (eval_close_ifZero_succ hEvalV hEvalS)
          dsimp only [scalarToNat] at hModV
          simp only [evalMod, hModV, hModZ, hPredMod, hModS, hNeZero, Bool.false_eq_true, ↓reduceIte,
            Nat.zero_mul, Nat.sub_zero, Nat.zero_add, Option.some.injEq]
          have hDistr : (M + 1) * scalarToNat v = scalarToNat v + M * scalarToNat v := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [hDistr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hValLt]
      · simp [hSort] at hInfer

/-- Specialization of `evaluates_mod_prime_exact_of_rangeSafe` to KoalaBear (`p = 2130706433`). -/
theorem evaluates_koalaBear_exact_of_rangeSafe
    (Γ : List Interval) (env : List Term) (modVals : List Nat) (t : Term)
    (hSafe : checkRangeSafeMod koalaBearPrime Γ t = true)
    (hAgree : ModEnvAgrees koalaBearPrime Γ env modVals) :
    ∃ (I : Interval) (v : Term),
      inferRange Γ t = some I ∧ Evaluates (closeTerm env t) v ∧ ValueInInterval I v ∧
      scalarToNat v < koalaBearPrime ∧ evalMod koalaBearPrime modVals t = some (scalarToNat v) :=
  evaluates_mod_prime_exact_of_rangeSafe koalaBearPrime Γ env modVals t hSafe hAgree

/-- Specialization of `evaluates_mod_prime_exact_of_rangeSafe` to BabyBear (`p = 2013265921`). -/
theorem evaluates_babyBear_exact_of_rangeSafe
    (Γ : List Interval) (env : List Term) (modVals : List Nat) (t : Term)
    (hSafe : checkRangeSafeMod babyBearPrime Γ t = true)
    (hAgree : ModEnvAgrees babyBearPrime Γ env modVals) :
    ∃ (I : Interval) (v : Term),
      inferRange Γ t = some I ∧ Evaluates (closeTerm env t) v ∧ ValueInInterval I v ∧
      scalarToNat v < babyBearPrime ∧ evalMod babyBearPrime modVals t = some (scalarToNat v) :=
  evaluates_mod_prime_exact_of_rangeSafe babyBearPrime Γ env modVals t hSafe hAgree

/-- Specialization of `evaluates_mod_prime_exact_of_rangeSafe` to Goldilocks (`p = 18446744069414584321`). -/
theorem evaluates_goldilocks_exact_of_rangeSafe
    (Γ : List Interval) (env : List Term) (modVals : List Nat) (t : Term)
    (hSafe : checkRangeSafeMod goldilocksPrime Γ t = true)
    (hAgree : ModEnvAgrees goldilocksPrime Γ env modVals) :
    ∃ (I : Interval) (v : Term),
      inferRange Γ t = some I ∧ Evaluates (closeTerm env t) v ∧ ValueInInterval I v ∧
      scalarToNat v < goldilocksPrime ∧ evalMod goldilocksPrime modVals t = some (scalarToNat v) :=
  evaluates_mod_prime_exact_of_rangeSafe goldilocksPrime Γ env modVals t hSafe hAgree

/-! ## 6. Necessity Counterexamples & Satisfiability Witnesses (`HypothesisLedger` Anti-Vacuity) -/

def hwOverflowTerm : Term := .binary .equal (.binary .add (.nat (2 ^ 64 - 1)) (.nat 1)) (.nat 0)

theorem wrap_counterexample_without_rangeSafe
    (slots : List String) (slotBodies : List RtlExpr)
    (inputs wires regs : Nat → BitVec 64) (selfDepth : Nat) :
    inferRange [] hwOverflowTerm = some Interval.bool01 ∧
    checkRangeSafeHw [] hwOverflowTerm = false ∧
    Evaluates hwOverflowTerm (.boolean false) ∧
    evalTermHw slots slotBodies inputs wires regs selfDepth [] hwOverflowTerm = some 1#64 ∧
    (1#64 : BitVec 64).toNat ≠ scalarToNat (.boolean false) := by
  refine ⟨by decide, by decide, ⟨?_, .boolean false⟩, by rfl, by decide⟩
  exact .next (.binaryLeft .equal (.nat 0) (.primitive .add _ _ _ (.natural _) (.natural _) rfl))
    (.next (.primitive .equal _ _ _ (.natural _) (.natural _) rfl) (.refl _))

def modOverflowTerm (M : Nat) : Term := .binary .equal (.binary .add (.nat (M - 1)) (.nat 1)) (.nat 0)

theorem mod_wrap_counterexample_without_rangeSafe (M : Nat) (hM : 1 < M) :
    checkRangeSafeMod M [] (modOverflowTerm M) = false ∧
    Evaluates (modOverflowTerm M) (.boolean false) ∧
    evalMod M [] (modOverflowTerm M) = some 1 ∧
    (1 : Nat) ≠ scalarToNat (.boolean false) := by
  have hAddEq : (M - 1) + 1 = M := by omega
  have hFalse : (M == 0) = false := beq_eq_false_iff_ne.2 (by omega)
  refine ⟨?_, ⟨?_, .boolean false⟩, ?_, by decide⟩
  · unfold checkRangeSafeMod modOverflowTerm
    simp [checkRangeSafeWith, inferRange, inferPrimRange, natOut, natBoolOut, hAddEq]
  · have sAdd : Step (.binary .add (.nat (M - 1)) (.nat 1)) (.nat M) :=
      .primitive .add _ _ _ (.natural _) (.natural _) (by simp [primitiveResult, hAddEq])
    have sEq : Step (.binary .equal (.nat M) (.nat 0)) (.boolean false) :=
      .primitive .equal _ _ _ (.natural _) (.natural _) (by simp [primitiveResult, hFalse])
    exact .next (.binaryLeft .equal (.nat 0) sAdd) (.next sEq (.refl _))
  · have hM1 : M - 1 < M := by omega
    simp only [evalMod, modOverflowTerm, evalPrimMod, Nat.mod_eq_of_lt hM1, Nat.mod_eq_of_lt hM,
      hAddEq, Nat.mod_self, Nat.zero_mod, beq_self_eq_true, ↓reduceIte]

def subtractUnderflowTerm : Term := .binary .subtract (.nat 0) (.nat 1)

theorem underflow_counterexample_without_rangeSafe (M : Nat) (hM : 1 < M) :
    inferRange [] subtractUnderflowTerm = some { lo := 0, hi := 0, sort := .nat, wf := Nat.le_refl 0 } ∧
    checkRangeSafeHw [] subtractUnderflowTerm = false ∧
    checkRangeSafeMod M [] subtractUnderflowTerm = false ∧
    Evaluates subtractUnderflowTerm (.nat 0) ∧
    evalTermHw [] [] (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) 0 [] subtractUnderflowTerm =
      some (BitVec.ofNat 64 (2 ^ 64 - 1)) ∧
    evalMod M [] subtractUnderflowTerm = some (M - 1) ∧ M - 1 ≠ 0 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, ?_, by omega⟩
  · unfold checkRangeSafeMod subtractUnderflowTerm
    simp [checkRangeSafeWith, inferRange, inferPrimRange, natOut]
  · exact ⟨.next (.primitive .subtract _ _ _ (.natural 0) (.natural 1) rfl) (.refl _), .natural 0⟩
  · have hM1 : M - 1 < M := by omega
    simp [evalMod, subtractUnderflowTerm, evalPrimMod, Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt hM1]

def boundedOffsetSubTerm : Term :=
  .app (.lam (.ifBool (.binary .lessEqual (.bound 0) (.nat 100)) (.binary .subtract (.bound 0) (.nat 5)) (.nat 0)))
       (.binary .add (.bound 0) (.nat 10))

theorem rangeSafe_pipeline_inhabited :
    (∃ iAdd, inferPrimRange .add (Interval.mkNat 0 50) (Interval.mkNat 10 10) = some iAdd) ∧
    (∃ I, inferRange [Interval.mkNat 0 50] boundedOffsetSubTerm = some I ∧ I.lo = 0 ∧ I.hi = 55) ∧
    checkRangeSafeHw [Interval.mkNat 0 50] boundedOffsetSubTerm = true ∧
    checkRangeSafeMod koalaBearPrime [Interval.mkNat 0 50] boundedOffsetSubTerm = true ∧
    checkRangeSafeMod babyBearPrime [Interval.mkNat 0 50] boundedOffsetSubTerm = true ∧
    checkRangeSafeMod goldilocksPrime [Interval.mkNat 0 50] boundedOffsetSubTerm = true ∧
    (∃ rtl, compileTerm [] [] 0 [.inputPort 0] boundedOffsetSubTerm = some rtl) ∧
    EnvInIntervals [Interval.mkNat 0 50] [.nat 20] ∧
    HwEnvAgrees [Interval.mkNat 0 50] [.nat 20] [20#64] ∧
    ModEnvAgrees koalaBearPrime [Interval.mkNat 0 50] [.nat 20] [20] :=
  ⟨⟨Interval.mkNat 10 60, by decide⟩, ⟨Interval.mkNat 0 55, by decide, rfl, rfl⟩,
   by decide, by decide, by decide, by decide, ⟨_, rfl⟩,
   envInIntervals_cons ⟨.refl _, .natural 20⟩ ⟨20, rfl, by decide, by decide⟩ envInIntervals_nil,
   hwEnvAgrees_cons ⟨.refl _, .natural 20⟩ ⟨20, rfl, by decide, by decide⟩ hwEnvAgrees_nil,
   modEnvAgrees_cons (M := koalaBearPrime) ⟨.refl _, .natural 20⟩ ⟨20, rfl, by decide, by decide⟩
     (modEnvAgrees_nil koalaBearPrime)⟩

end Obend.Core.RangeSafe
end
