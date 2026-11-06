module
/-
# Obend.Hardware.Hvm.Lower — Leaf terms lowered to `FExp`, and the lowering's soundness against Core4

See `Obend.Hardware.Hvm` for what is lowered, what is refused, and the theorem.
-/
public import Obend.Hardware.Hvm.Net
public import Obend.Leaf.Static
@[expose] public section
namespace Obend.Hardware.Hvm
open Obend.Core.Term
open Obend.Leaf
open Obend.Leaf.Static
open Obend.Equiv
set_option autoImplicit false

/-! ## 1. Exact evaluation -/

def ck (v : Nat) : Option Nat := if v < u24Mod then some v else none

/-- The exact operation on naturals, where it agrees with Core4 (`none`: underflow, a zero divisor,
or an operator the lowering does not use). -/
def exactOp : HOp → Nat → Nat → Option Nat
  | .add, a, b => some (a + b)
  | .mul, a, b => some (a * b)
  | .sub, a, b => if b ≤ a then some (a - b) else none
  | .div, a, b => if b = 0 then none else some (a / b)
  | .rem, a, b => if b = 0 then none else some (a % b)
  | .eq, a, b => some (if a = b then 1 else 0)
  | .lt, a, b => some (if a < b then 1 else 0)
  | .gt, a, b => some (if b < a then 1 else 0)
  | .and, a, b => some (a &&& b)
  | .xor, a, b => some (a ^^^ b)
  | _, _, _ => none

/-- **The exact evaluation** at fuel `f`: every value it computes is the Core4 value and lies below
`2^24`; `none` when one would not, when the fuel runs out, or when a call does not match. A switch
evaluates the taken branch only. Where it answers, `evalF` answers the same (`evalE_evalF`). -/
def evalE (D : List FDef) : Nat → (Nat → Option Nat) → FExp → Option Nat
  | _, _, .lit v => ck v
  | _, η, .var i => (η i).bind ck
  | f, η, .op o a b => match evalE D f η a, evalE D f η b with
    | some x, some y => (exactOp o x y).bind ck
    | _, _ => none
  | f, η, .let_ a b => match evalE D f η a with
    | some x => evalE D f (cons (some x) η) b
    | none => none
  | f, η, .ifz v z s => match evalE D f η v with
    | some 0 => evalE D f η z
    | some (k + 1) => evalE D f (cons (some k) η) s
    | none => none
  | f, η, .ifzL d _ _ v z s =>
    if d = 0 then none else
    match evalE D f η v with
    | some 0 => evalE D f (restrict d η) z
    | some (k + 1) => evalE D f (cons (some k) (restrict d η)) s
    | none => none
  | 0, _, .call _ _ => none
  | f + 1, η, .call g idxs => match D.find? (·.name == g) with
    | some d => if idxs.length = d.params.length ∧ idxs ≠ [] then
        evalE D f (bindEnv d.params (idxs.map η)) d.body else none
    | none => none
termination_by f _ e => (f, sizeOf e)

theorem ck_some {v w : Nat} (h : ck v = some w) : v = w ∧ w < u24Mod := by
  unfold ck at h; split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem exactOp_u24 {o : HOp} {x y r : Nat} (h : exactOp o x y = some r) (hy : y < u24Mod)
    (hr : r < u24Mod) : o.u24 x y = r := by
  cases o
  case sub =>
    simp only [exactOp] at h
    by_cases hle : y ≤ x
    · simp only [hle, ite_true, Option.some.injEq] at h
      subst h
      simp only [HOp.u24]
      rw [Nat.mod_eq_of_lt hy, show x + u24Mod - y = (x - y) + u24Mod by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hr]
    · simp [hle] at h
  case div =>
    simp only [exactOp] at h
    by_cases hy0 : y = 0
    · simp [hy0] at h
    · simp only [hy0, ite_false, Option.some.injEq] at h
      subst h; simp [HOp.u24, hy0, Nat.mod_eq_of_lt hr]
  case rem =>
    simp only [exactOp] at h
    by_cases hy0 : y = 0
    · simp [hy0] at h
    · simp only [hy0, ite_false, Option.some.injEq] at h
      subst h; simp [HOp.u24, hy0, Nat.mod_eq_of_lt hr]
  all_goals simp only [exactOp] at h
  all_goals first
    | (cases h; done)
    | (cases h; simp only [HOp.u24]; exact Nat.mod_eq_of_lt hr)
    | (cases h; rfl)

/-- No call and no lifted switch. -/
def callFree : FExp → Bool
  | .lit _ | .var _ => true
  | .op _ a b | .let_ a b => callFree a && callFree b
  | .ifz v z s => callFree v && callFree z && callFree s
  | .ifzL .. | .call .. => false

/-- Every inline switch has call-free branches (so building its untaken branch terminates). -/
def wellLifted : FExp → Bool
  | .op _ a b | .let_ a b => wellLifted a && wellLifted b
  | .ifz v z s => wellLifted v && callFree z && callFree s
  | .ifzL _ _ _ v z s => wellLifted v && wellLifted z && wellLifted s
  | _ => true

theorem evalF_callFree (D : List FDef) (f : Nat) : ∀ (e : FExp) (ρ : Nat → Option Nat), callFree e = true →
    ∃ v, evalF D f ρ e = some v
  | .lit v, _, _ => ⟨some v, by simp [evalF]⟩
  | .var i, ρ, _ => ⟨ρ i, by simp [evalF]⟩
  | .op o a b, ρ, h => by
    simp only [callFree, Bool.and_eq_true] at h
    obtain ⟨x, hx⟩ := evalF_callFree D f a ρ h.1
    obtain ⟨y, hy⟩ := evalF_callFree D f b ρ h.2
    exact ⟨opW o x y, by simp [evalF, hx, hy]⟩
  | .let_ a b, ρ, h => by
    simp only [callFree, Bool.and_eq_true] at h
    obtain ⟨x, hx⟩ := evalF_callFree D f a ρ h.1
    obtain ⟨y, hy⟩ := evalF_callFree D f b (cons x ρ) h.2
    exact ⟨y, by simp [evalF, hx, hy]⟩
  | .ifz v z s, ρ, h => by
    simp only [callFree, Bool.and_eq_true] at h
    obtain ⟨x, hx⟩ := evalF_callFree D f v ρ h.1.1
    obtain ⟨y, hy⟩ := evalF_callFree D f z ρ h.1.2
    obtain ⟨u, hu⟩ := evalF_callFree D f s (cons (predOf x) ρ) h.2
    exact ⟨selectZ x y u, by simp [evalF, hx, hy, hu]⟩
  | .ifzL .., _, h => by simp [callFree] at h
  | .call .., _, h => by simp [callFree] at h

/-- **Exact is wrapping where exact answers.** -/
theorem evalE_evalF (D : List FDef) (hD : ∀ d ∈ D, wellLifted d.body = true) : ∀ (f : Nat) (e : FExp)
    (η : Nat → Option Nat) (w : Nat), wellLifted e = true → evalE D f η e = some w →
    evalF D f η e = some (some w) ∧ w < u24Mod
  | _, .lit v, η, w, _, h => by
    simp only [evalE] at h
    obtain ⟨rfl, hw⟩ := ck_some h; exact ⟨by simp [evalF], hw⟩
  | _, .var i, η, w, _, h => by
    simp only [evalE] at h
    cases hi : η i with
    | none => simp [hi] at h
    | some u =>
      simp only [hi, Option.bind_some] at h
      obtain ⟨rfl, hw⟩ := ck_some h; exact ⟨by simp [evalF, hi], hw⟩
  | f, .op o a b, η, w, hl, h => by
    simp only [wellLifted, Bool.and_eq_true] at hl
    simp only [evalE] at h
    cases ha : evalE D f η a with
    | none => simp [ha] at h
    | some x =>
      cases hb : evalE D f η b with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb] at h
        cases hr : exactOp o x y with
        | none => simp [hr] at h
        | some r =>
          simp only [hr, Option.bind_some] at h
          obtain ⟨rfl, hw⟩ := ck_some h
          obtain ⟨wa, -⟩ := evalE_evalF D hD f a η x hl.1 ha
          obtain ⟨wb, hyb⟩ := evalE_evalF D hD f b η y hl.2 hb
          exact ⟨by simp [evalF, wa, wb, opW, exactOp_u24 hr hyb hw], hw⟩
  | f, .let_ a b, η, w, hl, h => by
    simp only [wellLifted, Bool.and_eq_true] at hl
    simp only [evalE] at h
    cases ha : evalE D f η a with
    | none => simp [ha] at h
    | some x =>
      simp only [ha] at h
      obtain ⟨wa, -⟩ := evalE_evalF D hD f a η x hl.1 ha
      obtain ⟨wb, hw⟩ := evalE_evalF D hD f b _ w hl.2 h
      exact ⟨by simp [evalF, wa, wb], hw⟩
  | f, .ifz v z s, η, w, hl, h => by
    simp only [wellLifted, Bool.and_eq_true] at hl
    obtain ⟨⟨hlv, hlz⟩, hls⟩ := hl
    simp only [evalE] at h
    cases hv : evalE D f η v with
    | none => simp [hv] at h
    | some k =>
      obtain ⟨wv, -⟩ := evalE_evalF D hD f v η k hlv hv
      cases k with
      | zero =>
        simp only [hv] at h
        obtain ⟨wz, hw⟩ := evalE_evalF D hD f z η w (by
          clear h; induction z <;> simp_all [wellLifted, callFree]) h
        obtain ⟨u, hu⟩ := evalF_callFree D f s (cons (predOf (some 0)) η) hls
        exact ⟨by simp [evalF, wv, wz, hu, selectZ], hw⟩
      | succ k =>
        simp only [hv] at h
        obtain ⟨ws, hw⟩ := evalE_evalF D hD f s _ w (by
          clear h; induction s <;> simp_all [wellLifted, callFree]) h
        obtain ⟨u, hu⟩ := evalF_callFree D f z η hlz
        exact ⟨by simp [evalF, wv, ws, hu, selectZ, predOf], hw⟩
  | f, .ifzL d nz ns v z s, η, w, hl, h => by
    simp only [wellLifted, Bool.and_eq_true] at hl
    obtain ⟨⟨hlv, hlz⟩, hls⟩ := hl
    simp only [evalE] at h
    by_cases hd : d = 0
    · simp [hd] at h
    simp only [hd, ite_false] at h
    cases hv : evalE D f η v with
    | none => simp [hv] at h
    | some k =>
      obtain ⟨wv, -⟩ := evalE_evalF D hD f v η k hlv hv
      cases k with
      | zero =>
        simp only [hv] at h
        obtain ⟨wz, hw⟩ := evalE_evalF D hD f z _ w hlz h
        exact ⟨by simp [evalF, hd, wv, wz], hw⟩
      | succ k =>
        simp only [hv] at h
        obtain ⟨ws, hw⟩ := evalE_evalF D hD f s _ w hls h
        exact ⟨by simp [evalF, hd, wv, ws], hw⟩
  | 0, .call g idxs, η, w, _, h => by simp [evalE] at h
  | f + 1, .call g idxs, η, w, _, h => by
    simp only [evalE] at h
    cases hd : D.find? (·.name == g) with
    | none => simp [hd] at h
    | some d =>
      simp only [hd] at h
      split at h
      · rename_i hc
        obtain ⟨wb, hw⟩ := evalE_evalF D hD f d.body _ w (hD d (List.mem_of_find?_eq_some hd)) h
        exact ⟨by simp [evalF, hd, hc, wb], hw⟩
      · cases h
termination_by f e => (f, sizeOf e)

theorem evalE_lt (D : List FDef) : ∀ (f : Nat) (e : FExp) (η : Nat → Option Nat) (w : Nat),
    evalE D f η e = some w → w < u24Mod
  | _, .lit v, η, w, h => by simp only [evalE] at h; exact (ck_some h).2
  | _, .var i, η, w, h => by
    simp only [evalE] at h
    cases hi : η i with
    | none => simp [hi] at h
    | some u => simp only [hi, Option.bind_some] at h; exact (ck_some h).2
  | f, .op o a b, η, w, h => by
    simp only [evalE] at h
    cases ha : evalE D f η a with
    | none => simp [ha] at h
    | some x =>
      cases hb : evalE D f η b with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb] at h
        cases hr : exactOp o x y with
        | none => simp [hr] at h
        | some r => simp only [hr, Option.bind_some] at h; exact (ck_some h).2
  | f, .let_ a b, η, w, h => by
    simp only [evalE] at h
    cases ha : evalE D f η a with
    | none => simp [ha] at h
    | some x => simp only [ha] at h; exact evalE_lt D f b _ w h
  | f, .ifz v z s, η, w, h => by
    simp only [evalE] at h
    cases hv : evalE D f η v with
    | none => simp [hv] at h
    | some k =>
      cases k with
      | zero => simp only [hv] at h; exact evalE_lt D f z _ w h
      | succ k => simp only [hv] at h; exact evalE_lt D f s _ w h
  | f, .ifzL d _ _ v z s, η, w, h => by
    simp only [evalE] at h
    by_cases hd : d = 0
    · simp [hd] at h
    simp only [hd, ite_false] at h
    cases hv : evalE D f η v with
    | none => simp [hv] at h
    | some k =>
      cases k with
      | zero => simp only [hv] at h; exact evalE_lt D f z _ w h
      | succ k => simp only [hv] at h; exact evalE_lt D f s _ w h
  | 0, .call _ _, _, _, h => by simp [evalE] at h
  | f + 1, .call g idxs, η, w, h => by
    simp only [evalE] at h
    cases hd : D.find? (·.name == g) with
    | none => simp [hd] at h
    | some d =>
      simp only [hd] at h
      split at h
      · exact evalE_lt D f d.body _ w h
      · cases h
termination_by f e => (f, sizeOf e)

/-! ## 2. Lifting an expression under a new variable -/

/-- Lift the variables at or above `c`. A lifted switch whose environment the new variable enters
gets new definitions (its branches lifted), named after the old ones and `c`. -/
def FExp.lift (c : Nat) : FExp → FExp
  | .lit v => .lit v
  | .var i => .var (if i < c then i else i + 1)
  | .op o a b => .op o (a.lift c) (b.lift c)
  | .let_ a b => .let_ (a.lift c) (b.lift (c + 1))
  | .ifz v z s => .ifz (v.lift c) (z.lift c) (s.lift (c + 1))
  | .ifzL d nz ns v z s =>
    if c < d then .ifzL (d + 1) s!"{nz}.l{c}" s!"{ns}.l{c}" (v.lift c) (z.lift c) (s.lift (c + 1))
    else .ifzL d nz ns (v.lift c) z s
  | .call g idxs => .call g (idxs.map fun i => if i < c then i else i + 1)

def ins (c : Nat) (x : Option Nat) (η : Nat → Option Nat) : Nat → Option Nat :=
  fun i => if i < c then η i else if i = c then x else η (i - 1)

theorem ins_cons (c : Nat) (x y : Option Nat) (η : Nat → Option Nat) :
    ins (c + 1) x (cons y η) = cons y (ins c x η) := by
  funext i
  cases i with
  | zero => simp [ins]
  | succ i =>
    simp only [ins, cons_succ]
    by_cases h1 : i < c
    · simp [h1]
    · by_cases h2 : i = c
      · subst h2; simp
      · have h3 : ¬ i + 1 < c + 1 := by omega
        have h4 : ¬ i + 1 = c + 1 := by omega
        simp only [h3, h4, h1, h2, ite_false]
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp

theorem restrict_ins (c d : Nat) (x : Option Nat) (η : Nat → Option Nat) (h : c < d) :
    restrict (d + 1) (ins c x η) = ins c x (restrict d η) := by
  funext i
  simp only [restrict, ins]
  by_cases h1 : i < c
  · simp [h1, show i < d + 1 by omega, show i < d by omega]
  · by_cases h2 : i = c
    · subst h2; simp [show i < d + 1 by omega]
    · by_cases h3 : i < d + 1
      · simp [h1, h2, h3, show i - 1 < d by omega]
      · simp [h1, h2, h3, show ¬ i - 1 < d by omega]

theorem restrict_ins_ge (c d : Nat) (x : Option Nat) (η : Nat → Option Nat) (h : d ≤ c) :
    restrict d (ins c x η) = restrict d η := by
  funext i
  simp only [restrict, ins]
  by_cases h1 : i < d
  · simp [h1, show i < c by omega]
  · simp [h1]

theorem map_ins (c : Nat) (x : Option Nat) (η : Nat → Option Nat) (idxs : List Nat) :
    (idxs.map fun i => if i < c then i else i + 1).map (ins c x η) = idxs.map η := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, ins]
  by_cases h : i < c
  · simp [h]
  · simp [h, show ¬ i + 1 < c by omega, show i + 1 ≠ c by omega]

theorem evalE_lift (D : List FDef) : ∀ (f : Nat) (e : FExp) (c : Nat) (x : Option Nat) (η : Nat → Option Nat),
    evalE D f (ins c x η) (e.lift c) = evalE D f η e
  | _, .lit _, _, _, _ => by simp [FExp.lift, evalE]
  | _, .var i, c, x, η => by
    simp only [FExp.lift, evalE, ins]
    by_cases h : i < c
    · simp [h]
    · have h1 : ¬ i + 1 < c := by omega
      have h2 : ¬ i + 1 = c := by omega
      simp [h, h1, h2]
  | f, .op o a b, c, x, η => by simp only [FExp.lift, evalE, evalE_lift D f a, evalE_lift D f b]
  | f, .let_ a b, c, x, η => by
    simp only [FExp.lift, evalE, evalE_lift D f a]
    cases evalE D f η a with
    | none => rfl
    | some y => simp only; rw [← ins_cons, evalE_lift D f b]
  | f, .ifz v z s, c, x, η => by
    simp only [FExp.lift, evalE, evalE_lift D f v, evalE_lift D f z]
    cases evalE D f η v with
    | none => rfl
    | some k =>
      cases k with
      | zero => rfl
      | succ k => simp only; rw [← ins_cons, evalE_lift D f s]
  | f, .ifzL d nz ns v z s, c, x, η => by
    by_cases hc : c < d
    · simp only [FExp.lift, hc, ite_true, evalE, evalE_lift D f v, Nat.add_one_ne_zero, ite_false]
      by_cases hd : d = 0
      · omega
      simp only [hd, ite_false]
      cases evalE D f η v with
      | none => rfl
      | some k =>
        cases k with
        | zero => simp only; rw [restrict_ins c d x η hc, evalE_lift D f z]
        | succ k => simp only; rw [restrict_ins c d x η hc, ← ins_cons, evalE_lift D f s]
    · simp only [FExp.lift, hc, ite_false, evalE, evalE_lift D f v]
      by_cases hd : d = 0
      · simp [hd]
      simp only [hd, ite_false]
      cases evalE D f η v with
      | none => rfl
      | some k =>
        cases k with
        | zero => simp only; rw [restrict_ins_ge c d x η (by omega)]
        | succ k => simp only; rw [restrict_ins_ge c d x η (by omega)]
  | 0, .call g idxs, c, x, η => by simp [FExp.lift, evalE]
  | f + 1, .call g idxs, c, x, η => by
    simp only [FExp.lift, evalE, map_ins, List.length_map]
    split <;> simp_all
termination_by f e => (f, sizeOf e)

theorem ins_zero (x : Option Nat) (η : Nat → Option Nat) : ins 0 x η = cons x η := by
  funext i; cases i <;> simp [ins]

/-- Lift `k` times at `0`: `e` moved under `k` new variables. -/
def liftBy : Nat → FExp → FExp
  | 0, e => e
  | k + 1, e => liftBy k (e.lift 0)

/-- `η` with `xs` pushed, the last of them at index 0. -/
def pushAll : List (Option Nat) → (Nat → Option Nat) → Nat → Option Nat
  | [], η => η
  | x :: xs, η => pushAll xs (cons x η)

theorem evalE_liftBy (D : List FDef) (f : Nat) : ∀ (xs : List (Option Nat)) (e : FExp) (η : Nat → Option Nat),
    evalE D f (pushAll xs η) (liftBy xs.length e) = evalE D f η e
  | [], _, _ => rfl
  | x :: xs, e, η => by
    simp only [pushAll, List.length_cons, liftBy]
    rw [evalE_liftBy D f xs (e.lift 0) (cons x η), ← ins_zero, evalE_lift]

inductive Fa2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Fa2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Fa2 R as bs → Fa2 R (a :: as) (b :: bs)

/-- Let-bind `as` one after the other (each under the ones before), then `b`. -/
def letChainAux : Nat → List FExp → FExp → FExp
  | _, [], b => b
  | i, a :: as, b => .let_ (liftBy i a) (letChainAux (i + 1) as b)

def letChain (as : List FExp) (b : FExp) : FExp := letChainAux 0 as b

theorem pushAll_snoc (x : Option Nat) : ∀ (xs : List (Option Nat)) (η : Nat → Option Nat),
    pushAll (xs ++ [x]) η = cons x (pushAll xs η)
  | [], _ => rfl
  | y :: xs, η => by simp only [List.cons_append, pushAll, pushAll_snoc x xs (cons y η)]

theorem evalE_letChainAux (D : List FDef) (f : Nat) (η₀ : Nat → Option Nat) (b : FExp) :
    ∀ (as : List FExp) (prev : List (Option Nat)) (w : Nat),
    evalE D f (pushAll prev η₀) (letChainAux prev.length as b) = some w →
    ∃ xs : List Nat, Fa2 (fun a x => evalE D f η₀ a = some x) as xs ∧
      evalE D f (pushAll (prev ++ xs.map some) η₀) b = some w
  | [], prev, w, h => ⟨[], .nil, by simpa [letChainAux] using h⟩
  | a :: as, prev, w, h => by
    simp only [letChainAux, evalE, evalE_liftBy] at h
    cases ha : evalE D f η₀ a with
    | none => simp [ha] at h
    | some x =>
      simp only [ha] at h
      rw [← pushAll_snoc, show prev.length + 1 = (prev ++ [some x]).length by simp] at h
      obtain ⟨xs, hxs, hb⟩ := evalE_letChainAux D f η₀ b as (prev ++ [some x]) w h
      exact ⟨x :: xs, .cons ha hxs, by simpa using hb⟩

theorem evalE_letChain (D : List FDef) (f : Nat) (η : Nat → Option Nat) (as : List FExp) (b : FExp) (w : Nat)
    (h : evalE D f η (letChain as b) = some w) :
    ∃ xs : List Nat, Fa2 (fun a x => evalE D f η a = some x) as xs ∧
      evalE D f (pushAll (xs.map some) η) b = some w := by
  have := evalE_letChainAux D f η b as [] w (by simpa [letChain, pushAll] using h)
  simpa using this

/-! ## 3. Sorts, and what a slot vector says about a Core4 term -/

inductive Scalar where
  | nat | bool
  deriving DecidableEq, Repr

/-- A value sort: a scalar, or a record of scalars. -/
inductive VSort where
  | sc (s : Scalar)
  | rcd (fs : List (String × Scalar))
  deriving DecidableEq, Repr

/-- A sort: a value, or a sum whose arms carry values. -/
inductive HSort where
  | val (v : VSort)
  | sum (arms : List (String × VSort))
  deriving DecidableEq, Repr

def VSort.width : VSort → Nat
  | .sc _ => 1
  | .rcd fs => fs.length

def maxW : List (String × VSort) → Nat
  | [] => 0
  | a :: as => max a.2.width (maxW as)

/-- The slots a value of the sort occupies: a scalar one, a record one per field, a sum its tag and
the widest arm's payload. -/
def HSort.width : HSort → Nat
  | .val v => v.width
  | .sum arms => 1 + maxW arms

def Scalar.lit : Scalar → Nat → Term
  | .nat, w => .nat w
  | .bool, w => .boolean (w != 0)

def Scalar.valid : Scalar → Nat → Prop
  | .nat, _ => True
  | .bool, w => w ≤ 1

def Scalar.observe : Scalar → Nat → Observation
  | .nat, w => .natural w
  | .bool, w => .boolean (w != 0)

theorem Scalar.lit_value (s : Scalar) (w : Nat) : Value (s.lit w) := by
  cases s
  · exact .natural w
  · exact .boolean _

theorem Scalar.observes (s : Scalar) (w : Nat) : Observes (s.lit w) (s.observe w) := by
  cases s
  · exact .natural w
  · exact .boolean _

/-- A scalar slot says: the term reaches the literal. -/
def DecS (s : Scalar) (w : Nat) (t : Term) : Prop := Obend.Core.Term.Steps t (s.lit w) ∧ s.valid w

/-- A value's slots say: a scalar as `DecS`; a record: the term reaches a record whose field of each
name (the first, as `get` selects it) carries its slot. -/
def DecV : VSort → List Nat → Term → Prop
  | .sc s, ws, t => ∃ w, ws = [w] ∧ DecS s w t
  | .rcd fs, ws, t => ∃ flds, Obend.Core.Term.Steps t (.record flds) ∧ ws.length = fs.length ∧
      ∀ (j : Nat) name s w, fs[j]? = some (name, s) → ws[j]? = some w →
        ∃ body, flds.find? (fun f => f.1 == name) = some (name, body) ∧ DecS s w body

/-- A sum's slots say: the term reaches the injection of the tag's arm, whose payload the next
slots describe. -/
def DecH : HSort → List Nat → Term → Prop
  | .val v, ws, t => DecV v ws t
  | .sum arms, ws, t => ∃ tag rest l v p, ws = tag :: rest ∧ rest.length = maxW arms ∧
      arms[tag]? = some (l, v) ∧ Obend.Core.Term.Steps t (.inject l p) ∧ DecV v (rest.take v.width) p

/-! ## 4. The primitives

A binary primitive lowers to `let x = l in let y = r in body`, `body` over `x` (index 1) and `y`
(index 0). Truncated subtraction, floor division and Lean's `%` are derived forms over HVM2's wrapping
operators: a guard on `<`, and a divisor `y + (y = 0)` that is never zero, because HVM2's Rust
runtime panics on a zero divisor and eager evaluation runs a guarded quotient's untaken branch. -/

def safeDivisor : FExp := .op .add (.var 1) (.op .eq (.var 1) (.lit 0))

/-- The primitives the lowering accepts: operand sorts, result sort, body. -/
def binOp : Primitive → Option (Scalar × Scalar × Scalar × FExp)
  | .add => some (.nat, .nat, .nat, .op .add (.var 1) (.var 0))
  | .multiply => some (.nat, .nat, .nat, .op .mul (.var 1) (.var 0))
  | .subtract => some (.nat, .nat, .nat, .ifz (.op .lt (.var 1) (.var 0)) (.op .sub (.var 1) (.var 0)) (.lit 0))
  | .divide => some (.nat, .nat, .nat, .ifz (.var 0) (.lit 0) (.op .div (.var 2) safeDivisor))
  | .modulo => some (.nat, .nat, .nat, .ifz (.var 0) (.var 1) (.op .rem (.var 2) safeDivisor))
  | .equal => some (.nat, .nat, .bool, .op .eq (.var 1) (.var 0))
  | .less => some (.nat, .nat, .bool, .op .lt (.var 1) (.var 0))
  | .lessEqual => some (.nat, .nat, .bool, .op .xor (.op .gt (.var 1) (.var 0)) (.lit 1))
  | .conjunction => some (.bool, .bool, .bool, .op .and (.var 1) (.var 0))
  | _ => none

theorem ck_of_lt {v : Nat} (h : v < u24Mod) : ck v = some v := by simp [ck, h]

/-- **The primitives are sound**: where the body evaluates exactly, Core4's primitive gives the
decoded result. -/
theorem binOp_sound {op : Primitive} {sl sr s : Scalar} {body : FExp} (hb : binOp op = some (sl, sr, s, body))
    (D : List FDef) (f : Nat) (η : Nat → Option Nat) {x y w : Nat} (hx : x < u24Mod) (hy : y < u24Mod)
    (vx : sl.valid x) (vy : sr.valid y)
    (h : evalE D f (cons (some y) (cons (some x) η)) body = some w) :
    primitiveResult op (sl.lit x) (sr.lit y) = some (s.lit w) ∧ s.valid w := by
  have c0 := ck_of_lt (show 0 < u24Mod by decide)
  have c1 := ck_of_lt (show 1 < u24Mod by decide)
  cases op <;> simp only [binOp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb
  all_goals obtain ⟨rfl, rfl, rfl, rfl⟩ := hb
  · -- add
    simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt hx, ck_of_lt hy, exactOp] at h
    obtain ⟨rfl, -⟩ := ck_some h
    exact ⟨by simp [primitiveResult, Scalar.lit], trivial⟩
  · -- multiply
    simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt hx, ck_of_lt hy, exactOp] at h
    obtain ⟨rfl, -⟩ := ck_some h
    exact ⟨by simp [primitiveResult, Scalar.lit], trivial⟩
  · -- equal
    simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt hx, ck_of_lt hy, exactOp] at h
    obtain ⟨rfl, -⟩ := ck_some h
    refine ⟨?_, ?_⟩
    · by_cases hxy : x = y <;> simp [primitiveResult, Scalar.lit, hxy]
    · simp only [Scalar.valid]; split <;> omega
  · -- conjunction
    simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt hx, ck_of_lt hy, exactOp] at h
    obtain ⟨rfl, -⟩ := ck_some h
    simp only [Scalar.valid] at vx vy
    rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
      rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;>
      simp [primitiveResult, Scalar.lit, Scalar.valid]
  · -- subtract
    simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt hx, ck_of_lt hy, exactOp] at h
    refine ⟨?_, trivial⟩
    by_cases hxy : x < y
    · simp only [hxy, ite_true, c1, Option.bind_some, c0] at h
      cases h
      simp [primitiveResult, Scalar.lit, Nat.sub_eq_zero_of_le (Nat.le_of_lt hxy)]
    · simp only [hxy, ite_false, c0, Option.bind_some] at h
      simp only [show y ≤ x by omega, ite_true, Option.bind_some] at h
      obtain ⟨rfl, -⟩ := ck_some h
      simp [primitiveResult, Scalar.lit]
  · -- divide
    refine ⟨?_, trivial⟩
    cases y with
    | zero =>
      simp only [evalE, cons_zero, Option.bind_some, c0] at h
      cases h
      simp [primitiveResult, Scalar.lit]
    | succ k =>
      simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt hy, ck_of_lt hx, safeDivisor,
        exactOp, c0, Nat.add_one_ne_zero, ite_false, Nat.add_zero] at h
      try simp only [c0, Option.bind_some, ck_of_lt hy, Nat.add_zero, Nat.add_one_ne_zero, ite_false] at h
      obtain ⟨rfl, -⟩ := ck_some h
      simp [primitiveResult, Scalar.lit]
  · -- less
    simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt hx, ck_of_lt hy, exactOp] at h
    obtain ⟨rfl, -⟩ := ck_some h
    refine ⟨?_, ?_⟩
    · by_cases hxy : x < y <;> simp [primitiveResult, Scalar.lit, hxy]
    · simp only [Scalar.valid]; split <;> omega
  · -- lessEqual
    simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt hx, ck_of_lt hy, exactOp, c1] at h
    simp only [show (if y < x then 1 else 0) < u24Mod by split <;> decide, ck_of_lt, Option.bind_some] at h
    obtain ⟨rfl, -⟩ := ck_some h
    refine ⟨?_, ?_⟩
    · by_cases hxy : y < x
      · have : ¬ x ≤ y := by omega
        simp [primitiveResult, Scalar.lit, hxy, this]
      · have : x ≤ y := by omega
        simp [primitiveResult, Scalar.lit, hxy, this]
    · simp only [Scalar.valid]; split <;> decide
  · -- modulo
    refine ⟨?_, trivial⟩
    cases y with
    | zero =>
      simp only [evalE, cons_zero, cons_succ, Option.bind_some, c0, ck_of_lt hx] at h
      cases h
      simp [primitiveResult, Scalar.lit]
    | succ k =>
      simp only [evalE, cons_succ, cons_zero, Option.bind_some, ck_of_lt hy, ck_of_lt hx, safeDivisor,
        exactOp, c0, Nat.add_one_ne_zero, ite_false, Nat.add_zero] at h
      try simp only [c0, Option.bind_some, ck_of_lt hy, Nat.add_zero, Nat.add_one_ne_zero, ite_false] at h
      obtain ⟨rfl, -⟩ := ck_some h
      simp [primitiveResult, Scalar.lit]

/-! ## 5. The translation -/

/-- What a Core4 variable is to the lowering: a value in the slots at these levels, the recursion of
a fixpoint (its definition, the levels it captures, its argument and result sorts), or nothing
usable (a fixpoint's inherited argument). -/
inductive CEnt where
  | val (s : HSort) (lvls : List Nat)
  | fn (g : String) (cap : List Nat) (arg : HSort) (res : Scalar)
  | none
  deriving Repr

/-- `[a, a+1, …, a+k-1]`. -/
def lvlRange (a : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => a :: lvlRange (a + 1) k

/-- The translation monad: a counter for fresh names, and the definitions emitted. -/
def Tr (α : Type) : Type := Nat → Except String (α × List FDef × Nat)

instance : Monad Tr where
  pure a := fun k => Except.ok (a, [], k)
  bind m f := fun k => match m k with
    | Except.ok (a, ds, k') => match f a k' with
      | Except.ok (b, ds', k'') => Except.ok (b, ds ++ ds', k'')
      | Except.error e => Except.error e
    | Except.error e => Except.error e

def Tr.fail {α : Type} (e : String) : Tr α := fun _ => Except.error e
def Tr.fresh : Tr Nat := fun k => Except.ok (k, [], k + 1)
def Tr.emit (d : FDef) : Tr Unit := fun k => Except.ok ((), [d], k)
def Tr.ofExcept {α : Type} : Except String α → Tr α
  | .ok a => fun k => Except.ok (a, [], k)
  | .error e => fun _ => Except.error e

theorem Tr.bind_ok {α β : Type} {m : Tr α} {f : α → Tr β} {k : Nat} {b : β} {ds : List FDef} {k'' : Nat}
    (h : (m >>= f) k = .ok (b, ds, k'')) :
    ∃ a ds₁ k' ds₂, m k = .ok (a, ds₁, k') ∧ f a k' = .ok (b, ds₂, k'') ∧ ds = ds₁ ++ ds₂ := by
  change (match m k with
    | Except.ok (a, ds, k') => match f a k' with
      | Except.ok (b, ds', k'') => (Except.ok (b, ds ++ ds', k'') : Except String (β × List FDef × Nat))
      | Except.error e => Except.error e
    | Except.error e => Except.error e) = _ at h
  split at h
  · rename_i a ds₁ k' hm
    split at h
    · rename_i b' ds₂ k₂ hf
      cases h
      exact ⟨a, ds₁, k', ds₂, hm, hf, rfl⟩
    · cases h
  · cases h

theorem Tr.pure_ok {α : Type} {a b : α} {k k' : Nat} {ds : List FDef} (h : (pure a : Tr α) k = .ok (b, ds, k')) :
    a = b ∧ ds = [] ∧ k = k' := by
  change (Except.ok (a, [], k) : Except String (α × List FDef × Nat)) = _ at h
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem Tr.fail_ok {α : Type} {e : String} {k : Nat} {r : α × List FDef × Nat} (h : (Tr.fail e : Tr α) k = .ok r) :
    False := by
  cases h

/-- Switches over one condition, one per slot: all inline when every branch is call-free, all with
their branches lifted to definitions otherwise (so the untaken branch is voided before it is
expanded). One decision for all slots keeps them evaluating in one environment. -/
def mkIfs (pfx : String) (d : Nat) (v : FExp) (zs ss : List FExp) : Tr (List FExp) :=
  if zs.all callFree && ss.all callFree then pure ((zs.zip ss).map fun p => .ifz v p.1 p.2)
  else liftIfs pfx d v zs ss
where
  liftIfs (pfx : String) (d : Nat) (v : FExp) : List FExp → List FExp → Tr (List FExp)
    | z :: zs, s :: ss => do
      let k ← Tr.fresh
      let es ← liftIfs pfx d v zs ss
      pure (.ifzL d s!"{pfx}.b{k}z" s!"{pfx}.b{k}s" v z s :: es)
    | _, _ => pure []

/-- The switch chains over a sum's tag, one per slot: arm `k`'s slots under `k` predecessors. -/
def swChains (pfx : String) : Nat → FExp → List (List FExp) → Tr (List FExp)
  | _, _, [] => Tr.fail "case: no arm"
  | _, _, [a] => pure a
  | d, scr, a :: rest => do
    let r ← swChains pfx (d + 1) (.var 0) rest
    mkIfs pfx d scr a r

/-- The arm of a label, and its index. -/
def armIdx {β : Type} : List (String × β) → String → Option (Nat × β)
  | [], _ => none
  | (l, v) :: rest, n => if l = n then some (0, v) else (armIdx rest n).map fun p => (p.1 + 1, p.2)

def joinS : HSort → HSort → Except String HSort
  | .val v, .val v' => if v = v' then .ok (.val v) else .error "branches of different sorts"
  | .sum a, .sum b =>
    (b.foldl (fun (acc : Except String (List (String × VSort))) lv => acc.bind fun arms => match arms.lookup lv.1 with
      | some v' => if lv.2 = v' then .ok arms else .error s!"arm {lv.1} at two sorts"
      | none => .ok (arms ++ [lv])) (.ok a)).map .sum
  | _, _ => .error "a value and a sum in two branches"

mutual
/-- A best-effort sort of a term (unproved: `toS` checks what it is given). -/
def sortOf (Γ : List CEnt) : Term → Except String HSort
  | .nat _ => .ok (.val (.sc .nat))
  | .boolean _ => .ok (.val (.sc .bool))
  | .bound i => match Γ[i]? with
    | some (.val s _) => .ok s
    | _ => .error s!"variable {i}: not a value"
  | .binary op _ _ => match binOp op with
    | some (_, _, s, _) => .ok (.val (.sc s))
    | none => .error s!"primitive {repr op}"
  | .ifZero _ z s => do joinS (← sortOf Γ z) (← sortOf (.val (.val (.sc .nat)) [] :: Γ) s)
  | .ifBool _ t f => do joinS (← sortOf Γ t) (← sortOf Γ f)
  | .app (.lam b) a => do sortOf (.val (← sortOf Γ a) [] :: Γ) b
  | .app (.fix (.lam (.lam (.lam body))) _) a => do
    let sa ← sortOf Γ a
    match sortOf (.val sa [] :: .none :: .fn "" [] sa .nat :: Γ) body with
    | .ok (.val (.sc .nat)) => .ok (.val (.sc .nat))
    | _ => match sortOf (.val sa [] :: .none :: .fn "" [] sa .bool :: Γ) body with
      | .ok (.val (.sc .bool)) => .ok (.val (.sc .bool))
      | _ => .error "fix: the result is not a scalar"
  | .app (.bound i) _ => match Γ[i]? with
    | some (.fn _ _ _ r) => .ok (.val (.sc r))
    | _ => .error "application of a variable that is not the recursion"
  | .record fs => (sortFields Γ fs).map fun sfs => .val (.rcd sfs)
  | .get t n => do
    match ← sortOf Γ t with
    | .val (.rcd sfs) => match sfs.lookup n with
      | some s => .ok (.val (.sc s))
      | none => .error s!"get {n}: no such field"
    | _ => .error s!"get {n} on a non-record"
  | .inject l p => do
    match ← sortOf Γ p with
    | .val v => .ok (.sum [(l, v)])
    | _ => .error "inject: a sum as a payload"
  | .case sc arms => do
    match ← sortOf Γ sc with
    | .sum sarms => sortArms Γ sarms arms
    | _ => .error "case on a non-sum"
  | .label l => .error s!"label {l}: labels are not in the fragment"
  | .lam _ => .error "a λ-abstraction as a value inside a body (only a method's curried result is handled)"
  | .fix _ _ => .error "fix not applied to its argument"
  | .app _ _ => .error "application of a non-literal function: higher-order, not in the fragment"
  | .perform _ | .done _ => .error "an activity (perform, done)"
  | .split .. => .error "split: a record destructor, not in the fragment"
  | .hole .. => .error "a hole"
  | _ => .error "an object form (mix, specification, prototype, reflect, metadata, project, extend)"
termination_by t => sizeOf t
decreasing_by all_goals simp_wf; all_goals omega

/-- The sorts of record fields (scalars). -/
def sortFields (Γ : List CEnt) : List (String × Term) → Except String (List (String × Scalar))
  | [] => .ok []
  | (n, t) :: fs => do
    match ← sortOf Γ t with
    | .val (.sc s) => .ok ((n, s) :: (← sortFields Γ fs))
    | _ => .error s!"field {n}: not a scalar"
termination_by fs => sizeOf fs

def sortArms (Γ : List CEnt) (sarms : List (String × VSort)) : List (String × Term) → Except String HSort
  | [] => .error "case: no arm"
  | [(l, b)] => match sarms.lookup l with
    | some v => sortOf (.val (.val v) [] :: Γ) b
    | none => .error s!"case: arm {l} of no injection"
  | (l, b) :: arms => do
    let s ← match sarms.lookup l with
      | some v => sortOf (.val (.val v) [] :: Γ) b
      | none => .error s!"case: arm {l} of no injection"
    joinS s (← sortArms Γ sarms arms)
termination_by arms => sizeOf arms
end

mutual
/-- **The translation of a term** at sort `σ`: one `FExp` per slot, at FExp depth `dep`, or the
reason it is refused. -/
def toS (pfx : String) (Γ : List CEnt) (dep : Nat) : Term → HSort → Tr (List FExp)
  | .nat v, σ => if σ = .val (.sc .nat) ∧ v < u24Mod then pure [.lit v]
      else Tr.fail s!"literal {v}: not a natural below 2^24 here"
  | .boolean b, σ => if σ = .val (.sc .bool) then pure [.lit (if b then 1 else 0)]
      else Tr.fail "a Boolean where another sort is expected"
  | .bound i, σ => match Γ[i]? with
    | some (.val s lvls) => if s = σ ∧ lvls.all (· < dep) then pure (lvls.map fun ℓ => .var (dep - 1 - ℓ))
        else Tr.fail s!"variable {i} at the wrong sort"
    | some (.fn ..) => Tr.fail "a fixpoint's recursion used as a value"
    | some .none => Tr.fail "a fixpoint's inherited argument"
    | none => Tr.fail s!"variable {i} out of scope: a `self` read the folder did not resolve, or a free variable"
  | .binary op l r, σ => match binOp op with
    | some (sl, sr, s, body) => if σ = .val (.sc s) then (do
        let fl ← toS pfx Γ dep l (.val (.sc sl))
        let fr ← toS pfx Γ (dep + 1) r (.val (.sc sr))
        match fl, fr with
        | [a], [b] => pure [.let_ a (.let_ b body)]
        | _, _ => Tr.fail "an operand of more than one slot")
      else Tr.fail s!"primitive {repr op} at the wrong sort"
    | none => Tr.fail s!"primitive {repr op}: outside the fragment (bitwise, shift, signed, fixed-point, labels)"
  | .ifZero v z s, σ => if σ.width = 0 then Tr.fail "a conditional of no slots" else do
    let fv ← toS pfx Γ dep v (.val (.sc .nat))
    let zs ← toS pfx Γ dep z σ
    let ss ← toS pfx (.val (.val (.sc .nat)) [dep] :: Γ) (dep + 1) s σ
    match fv with
    | [a] => if zs.length = ss.length ∧ zs ≠ [] then mkIfs pfx dep a zs ss else Tr.fail "ifZero: branch widths"
    | _ => Tr.fail "ifZero: a condition of more than one slot"
  | .ifBool c t f, σ => if σ.width = 0 then Tr.fail "a conditional of no slots" else do
    let fc ← toS pfx Γ dep c (.val (.sc .bool))
    let ts ← toS pfx Γ (dep + 1) t σ
    let fs ← toS pfx Γ dep f σ
    match fc with
    | [a] => if fs.length = ts.length ∧ fs ≠ [] then mkIfs pfx dep a fs ts else Tr.fail "ifBool: branch widths"
    | _ => Tr.fail "ifBool: a condition of more than one slot"
  | .app (.lam b) a, σ => if σ.width = 0 then Tr.fail "a let of no slots" else do
    let sa ← Tr.ofExcept (sortOf Γ a)
    let as ← toS pfx Γ dep a sa
    let bs ← toS pfx (.val sa (lvlRange dep as.length) :: Γ) (dep + as.length) b σ
    if bs = [] then Tr.fail "a let of no slots" else pure (bs.map (letChain as))
  | .app (.fix (.lam (.lam (.lam body))) _) a, σ => match σ with
    | .val (.sc res) => do
      let sa ← Tr.ofExcept (sortOf Γ a)
      let as ← toS pfx Γ dep a sa
      if as.length ≠ sa.width then Tr.fail "fix: argument slots" else do
      let k ← Tr.fresh
      let fb ← toS pfx (.val sa (lvlRange dep as.length) :: .none ::
        .fn s!"{pfx}.f{k}" (lvlRange 0 dep) sa res :: Γ) (dep + as.length) body σ
      match fb with
      | [b] => (do
        Tr.emit ⟨s!"{pfx}.f{k}", revRange (dep + as.length), b⟩
        pure [letChain as (.call s!"{pfx}.f{k}" (revRange (dep + as.length)))])
      | _ => Tr.fail "fix: a body of more than one slot"
    | _ => Tr.fail "fix: a result that is not a scalar (records and sums are not returned by recursion)"
  | .app (.bound i) a, σ => match Γ[i]? with
    | some (.fn g cap sa res) => if σ = .val (.sc res) then (do
        let as ← toS pfx Γ dep a sa
        pure [letChain as (.call g ((cap ++ lvlRange dep as.length).map fun ℓ => dep + as.length - 1 - ℓ))])
      else Tr.fail "recursive call at the wrong sort"
    | _ => Tr.fail "application of a variable that is not a fixpoint's recursion: higher-order"
  | .app (.fix _ _) _, _ => Tr.fail "fix: a specification that is not `λrec. λsup. λx. body` applied to one argument"
  | .app _ _, _ => Tr.fail "application of a non-literal function: higher-order, not in the fragment"
  | .record fs, σ => match σ with
    | .val (.rcd sfs) => if (sfs.map (·.1)).Nodup then toFields pfx Γ dep fs sfs
        else Tr.fail "a record with a repeated field"
    | _ => Tr.fail "a record where another sort is expected"
  | .get t n, σ => Tr.ofExcept (sortOf Γ t) >>= fun st => match st with
    | .val (.rcd sfs) => match armIdx sfs n with
      | some (j, s) => if σ = .val (.sc s) ∧ (sfs.map (·.1)).Nodup then
          toS pfx Γ dep t st >>= fun ts => if j < ts.length then pure [letChain ts (.var (ts.length - 1 - j))]
            else Tr.fail "get: a record of too few slots"
        else Tr.fail s!"get {n} at the wrong sort"
      | none => Tr.fail s!"get {n}: no such field"
    | _ => Tr.fail s!"get {n} on a term that is not a record of scalars"
  | .inject l p, σ => match σ with
    | .sum arms => if (arms.map (·.1)).Nodup then match armIdx arms l with
        | some (j, v) => (do
          let ps ← toS pfx Γ dep p (.val v)
          pure (.lit j :: ps ++ List.replicate (maxW arms - ps.length) (.lit 0)))
        | none => Tr.fail s!"inject {l}: not an arm of the sum"
      else Tr.fail "a sum with a repeated arm"
    | _ => Tr.fail s!"inject {l} where a sum is not expected"
  | .case sc arms, σ => if σ.width = 0 then Tr.fail "a case of no slots" else
    Tr.ofExcept (sortOf Γ sc) >>= fun ss => match ss with
    | .sum sarms => if (sarms.map (·.1)).Nodup ∧ sarms ≠ [] then
        toS pfx Γ dep sc (.sum sarms) >>= fun fsc =>
        toArms pfx Γ (dep + 1) (dep + fsc.length) sarms σ arms >>= fun tr =>
        match sarms.mapM (fun lv => tr.lookup lv.1) with
        | some perArm =>
          if perArm.all (·.length = σ.width) ∧ fsc.length = 1 + maxW sarms then
            swChains pfx (dep + fsc.length) (.var (fsc.length - 1)) perArm >>= fun sw =>
            pure (sw.map (letChain fsc))
          else Tr.fail "case: arm widths"
        | none => Tr.fail "case: an injection without an arm"
      else Tr.fail "case: a sum with a repeated arm"
    | _ => Tr.fail "case on a term that is not a sum"
  | .lam _, _ => Tr.fail "a λ-abstraction as a value inside a body (only a method's curried result is handled)"
  | .fix _ _, _ => Tr.fail "fix not applied to its argument"
  | .hole _ _, _ => Tr.fail "a hole"
  | .mix _ _, _ => Tr.fail "mix: an object form"
  | .specification _ _, _ => Tr.fail "specification: an object form"
  | .prototype _ _, _ => Tr.fail "prototype: an object form"
  | .reflect _, _ => Tr.fail "reflect: an object form"
  | .metadata _, _ => Tr.fail "metadata: an object form"
  | .project _, _ => Tr.fail "project: an object form"
  | .extend _ _, _ => Tr.fail "extend: an object form"
  | .label l, _ => Tr.fail s!"label {l}: labels are not in the fragment"
  | .perform _, _ => Tr.fail "perform: an activity"
  | .done _, _ => Tr.fail "done: an activity"
  | .split _ _ _, _ => Tr.fail "split: a record destructor, not in the fragment"
termination_by t => sizeOf t

/-- A record's fields, each a scalar slot. -/
def toFields (pfx : String) (Γ : List CEnt) (dep : Nat) :
    List (String × Term) → List (String × Scalar) → Tr (List FExp)
  | [], [] => pure []
  | (n, t) :: fs, (n', s) :: sfs => if n = n' then (do
      let ft ← toS pfx Γ dep t (.val (.sc s))
      let rest ← toFields pfx Γ dep fs sfs
      match ft with
      | [e] => pure (e :: rest)
      | _ => Tr.fail "a field of more than one slot")
    else Tr.fail s!"record field {n} where {n'} is expected"
  | _, _ => Tr.fail "a record of the wrong fields"
termination_by fs => sizeOf fs

/-- The arms of a `case` whose labels the scrutinee's sort has: arm `k` translated at depth
`base + k` with its payload in the slots from level `pl`. -/
def toArms (pfx : String) (Γ : List CEnt) (pl base : Nat) (sarms : List (String × VSort)) (σ : HSort) :
    List (String × Term) → Tr (List (String × List FExp))
  | [] => pure []
  | (l, b) :: rest => match armIdx sarms l with
    | some (k, v) => do
      let e ← toS pfx (.val (.val v) (lvlRange pl v.width) :: Γ) (base + k) b σ
      let es ← toArms pfx Γ pl base sarms σ rest
      pure ((l, e) :: es)
    | none => toArms pfx Γ pl base sarms σ rest
termination_by arms => sizeOf arms
end

/-! ## 6. Facts the soundness proof uses -/

theorem Tr.ofExcept_ok {α : Type} {e : Except String α} {k k' : Nat} {a : α} {ds : List FDef}
    (h : Tr.ofExcept e k = .ok (a, ds, k')) : e = .ok a ∧ ds = [] := by
  cases e with
  | ok b => change (Except.ok (b, [], k) : Except String (α × List FDef × Nat)) = _ at h; cases h; exact ⟨rfl, rfl⟩
  | error e => cases h

theorem Tr.fresh_ok {k k' a : Nat} {ds : List FDef} (h : Tr.fresh k = .ok (a, ds, k')) : ds = [] := by
  change (Except.ok (k, [], k + 1) : Except String (Nat × List FDef × Nat)) = _ at h; cases h; rfl

theorem Tr.emit_ok {d : FDef} {k k' : Nat} {u : Unit} {ds : List FDef} (h : Tr.emit d k = .ok (u, ds, k')) :
    ds = [d] := by
  change (Except.ok ((), [d], k) : Except String (Unit × List FDef × Nat)) = _ at h; cases h; rfl

theorem fa2_length {α β : Type} {R : α → β → Prop} : ∀ {as : List α} {bs : List β}, Fa2 R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [fa2_length h]

theorem fa2_det {D : List FDef} {f : Nat} {η : Nat → Option Nat} : ∀ {es : List FExp} {ws ws' : List Nat},
    Fa2 (fun e w => evalE D f η e = some w) es ws → Fa2 (fun e w => evalE D f η e = some w) es ws' → ws = ws'
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h hs, .cons h' hs' => by rw [h] at h'; cases h'; rw [fa2_det hs hs']

theorem fa2_map_of {α : Type} {R : α → Nat → Prop} : ∀ {as : List α} {ws : List Nat},
    Fa2 R as ws → ∀ (i : Nat) a w, as[i]? = some a → ws[i]? = some w → R a w
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons hr hs, 0, _, _, ha, hw => by simp at ha hw; subst ha hw; exact hr
  | _, _, .cons _ hs, i + 1, a, w, ha, hw => fa2_map_of hs i a w (by simpa using ha) (by simpa using hw)

/-- The value at a level, at FExp depth `dep`. -/
def lvlVal (dep : Nat) (η : Nat → Option Nat) (ℓ : Nat) : Option Nat := η (dep - 1 - ℓ)

theorem pushAll_get : ∀ (xs : List (Option Nat)) (η : Nat → Option Nat) (i : Nat),
    pushAll xs η i = if i < xs.length then xs.getD (xs.length - 1 - i) none else η (i - xs.length)
  | [], η, i => by simp [pushAll]
  | x :: xs, η, i => by
    simp only [pushAll, pushAll_get xs (cons x η) i, List.length_cons]
    by_cases h : i < xs.length
    · rw [if_pos h, if_pos (by omega)]
      rw [show xs.length + 1 - 1 - i = (xs.length - 1 - i) + 1 by omega]
      simp
    · rw [if_neg h]
      by_cases h' : i = xs.length
      · subst h'; simp
      · rw [if_neg (by omega)]
        obtain ⟨j, hj⟩ : ∃ j, i - xs.length = j + 1 := ⟨i - xs.length - 1, by omega⟩
        rw [hj]; simp only [cons_succ]; congr 1; omega

theorem lvlVal_push (xs : List (Option Nat)) (η : Nat → Option Nat) (dep ℓ : Nat) (h : ℓ < dep) :
    lvlVal (dep + xs.length) (pushAll xs η) ℓ = lvlVal dep η ℓ := by
  simp only [lvlVal, pushAll_get]
  rw [if_neg (by omega)]; congr 1; omega

theorem lvlVal_push_new (xs : List (Option Nat)) (η : Nat → Option Nat) (dep i : Nat) (h : i < xs.length) :
    lvlVal (dep + xs.length) (pushAll xs η) (dep + i) = xs.getD i none := by
  simp only [lvlVal, pushAll_get]
  rw [if_pos (by omega)]; congr 1; omega

theorem lvlVal_restrict (d : Nat) (η : Nat → Option Nat) (ℓ : Nat) (h : ℓ < d) :
    lvlVal d (restrict d η) ℓ = lvlVal d η ℓ := by
  simp [lvlVal, restrict, show d - 1 - ℓ < d by omega]

/-- What a fixpoint's recursion is good for, at fuel `f`: applied to an argument its slots describe,
it reaches the literal its body's exact value decodes to. -/
def FunOk (D : List FDef) (f : Nat) (g : String) (capv : List (Option Nat)) (sa : HSort) (res : Scalar)
    (R : Term) : Prop :=
  ∀ (a : Term) (ws : List Nat) (d : FDef) (w : Nat), DecH sa ws a → D.find? (·.name == g) = some d →
    evalE D f (bindEnv d.params (capv ++ ws.map some)) d.body = some w → DecS res w (.app R a)

def EntOk (D : List FDef) (fuel dep : Nat) (η : Nat → Option Nat) (t : Term) : CEnt → Prop
  | .val s lvls => (∀ ℓ ∈ lvls, ℓ < dep) ∧ ∃ ws, lvls.map (lvlVal dep η) = ws.map some ∧ DecH s ws t
  | .fn g cap sa res => (∀ ℓ ∈ cap, ℓ < dep) ∧ ∀ f' < fuel, FunOk D f' g (cap.map (lvlVal dep η)) sa res t
  | .none => True

/-- **The environment invariant**: each Core4 variable's term is what its entry says. -/
def EnvOk (D : List FDef) (fuel : Nat) (Γ : List CEnt) (dep : Nat) (η : Nat → Option Nat)
    (σc : Nat → Term) : Prop :=
  ∀ i e, Γ[i]? = some e → EntOk D fuel dep η (σc i) e

theorem EntOk.move {D : List FDef} {fuel fuel' dep dep' : Nat} {η η' : Nat → Option Nat} {t : Term} {e : CEnt}
    (hf : fuel' ≤ fuel) (hd : dep ≤ dep') (hv : ∀ ℓ < dep, lvlVal dep' η' ℓ = lvlVal dep η ℓ)
    (h : EntOk D fuel dep η t e) : EntOk D fuel' dep' η' t e := by
  cases e with
  | val s lvls =>
    obtain ⟨hl, ws, hw, hd'⟩ := h
    refine ⟨fun ℓ hℓ => by have := hl ℓ hℓ; omega, ws, ?_, hd'⟩
    rw [← hw]; apply List.map_congr_left; intro ℓ hℓ; exact hv ℓ (hl ℓ hℓ)
  | fn g cap sa res =>
    obtain ⟨hl, hfun⟩ := h
    refine ⟨fun ℓ hℓ => by have := hl ℓ hℓ; omega, fun f' hf' => ?_⟩
    have : cap.map (lvlVal dep' η') = cap.map (lvlVal dep η) := by
      apply List.map_congr_left; intro ℓ hℓ; exact hv ℓ (hl ℓ hℓ)
    rw [this]; exact hfun f' (by omega)
  | none => trivial

theorem EnvOk.move {D : List FDef} {fuel fuel' : Nat} {Γ : List CEnt} {dep dep' : Nat} {η η' : Nat → Option Nat}
    {σc : Nat → Term} (hf : fuel' ≤ fuel) (hd : dep ≤ dep') (hv : ∀ ℓ < dep, lvlVal dep' η' ℓ = lvlVal dep η ℓ)
    (h : EnvOk D fuel Γ dep η σc) : EnvOk D fuel' Γ dep' η' σc :=
  fun i e hi => (h i e hi).move hf hd hv

theorem EnvOk.push {D : List FDef} {fuel : Nat} {Γ : List CEnt} {dep : Nat} {η : Nat → Option Nat}
    {σc : Nat → Term} (xs : List (Option Nat)) (h : EnvOk D fuel Γ dep η σc) :
    EnvOk D fuel Γ (dep + xs.length) (pushAll xs η) σc :=
  h.move (Nat.le_refl _) (by omega) (fun ℓ hℓ => lvlVal_push xs η dep ℓ hℓ)

theorem EnvOk.cons1 {D : List FDef} {fuel : Nat} {Γ : List CEnt} {dep : Nat} {η : Nat → Option Nat}
    {σc : Nat → Term} (x : Option Nat) (h : EnvOk D fuel Γ dep η σc) : EnvOk D fuel Γ (dep + 1) (cons x η) σc :=
  h.push [x]

theorem EnvOk.restrict {D : List FDef} {fuel : Nat} {Γ : List CEnt} {dep : Nat} {η : Nat → Option Nat}
    {σc : Nat → Term} (R : (Nat → Option Nat) → Nat → Option Nat)
    (hR : ∀ ρ i, i < dep → R ρ i = ρ i) (h : EnvOk D fuel Γ dep η σc) : EnvOk D fuel Γ dep (R η) σc :=
  h.move (Nat.le_refl _) (Nat.le_refl _) (fun ℓ hℓ => by simp only [lvlVal]; exact hR η _ (by omega))

theorem DecS.steps {s : Scalar} {w : Nat} {t t' : Term} (h : Obend.Core.Term.Steps t t') (d : DecS s w t') :
    DecS s w t := ⟨steps_trans h d.1, d.2⟩

theorem DecV.steps {v : VSort} {ws : List Nat} {t t' : Term} (h : Obend.Core.Term.Steps t t') (d : DecV v ws t') :
    DecV v ws t := by
  cases v with
  | sc s => obtain ⟨w, hw, hd⟩ := d; exact ⟨w, hw, hd.steps h⟩
  | rcd fs => obtain ⟨flds, hs, hl, hf⟩ := d; exact ⟨flds, steps_trans h hs, hl, hf⟩

theorem DecH.steps {σ : HSort} {ws : List Nat} {t t' : Term} (h : Obend.Core.Term.Steps t t') (d : DecH σ ws t') :
    DecH σ ws t := by
  cases σ with
  | val v => exact DecV.steps h d
  | sum arms =>
    obtain ⟨tag, rest, l, v, p, hws, hl, ha, hs, hd⟩ := d
    exact ⟨tag, rest, l, v, p, hws, hl, ha, steps_trans h hs, hd⟩

theorem DecV.length {v : VSort} {ws : List Nat} {t : Term} (d : DecV v ws t) : ws.length = v.width := by
  cases v with
  | sc s => obtain ⟨w, rfl, -⟩ := d; rfl
  | rcd fs => obtain ⟨_, _, hl, _⟩ := d; exact hl

theorem DecH.length {σ : HSort} {ws : List Nat} {t : Term} (d : DecH σ ws t) : ws.length = σ.width := by
  cases σ with
  | val v => exact DecV.length d
  | sum arms =>
    obtain ⟨tag, rest, l, v, p, rfl, hl, -, -, -⟩ := d
    simp [HSort.width, hl]; omega

/-- Extend a Core4 substitution at index 0. -/
theorem inst_lift (s u : Term) (σ : Nat → Term) :
    instantiate (s.substitute (liftSubstitution σ)) u = s.substitute (cons u σ) := by
  rw [instantiate_eq, Obend.Core.TermTraverse.substitute_comp]
  congr 1; funext i
  cases i with
  | zero => simp [liftSubstitution, Term.substitute, single]
  | succ i => simp only [liftSubstitution, cons_succ]; exact shift_one_cancel _ _

theorem ifz_eval_aux (D : List FDef) (f : Nat) (η : Nat → Option Nat) (v : FExp) (x : Nat)
    (hx : evalE D f η v = some x) : ∀ (zs ss : List FExp) (ws : List Nat), zs.length = ss.length →
    Fa2 (fun e w => evalE D f η e = some w) ((zs.zip ss).map fun p => .ifz v p.1 p.2) ws →
    (x = 0 → Fa2 (fun e w => evalE D f η e = some w) zs ws) ∧
    (∀ k, x = k + 1 → Fa2 (fun e w => evalE D f (cons (some k) η) e = some w) ss ws)
  | [], [], ws, _, h => by cases h; exact ⟨fun _ => .nil, fun _ _ => .nil⟩
  | z :: zs, s :: ss, ws, hl, h => by
    simp only [List.zip_cons_cons, List.map_cons] at h
    cases h with
    | cons hh ht =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      obtain ⟨h1, h2⟩ := ifz_eval_aux D f η v x hx zs ss _ hl ht
      simp only [evalE, hx] at hh
      refine ⟨fun h0 => ?_, fun k hk => ?_⟩
      · subst h0; exact .cons hh (h1 rfl)
      · subst hk; exact .cons hh (h2 k rfl)
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

theorem liftIfs_eval (pfx : String) (D : List FDef) (f : Nat) (η : Nat → Option Nat) (d : Nat) (v : FExp) (x : Nat)
    (hx : evalE D f η v = some x) : ∀ (zs ss : List FExp) (k : Nat) (es : List FExp) (ds : List FDef) (k' : Nat)
    (ws : List Nat), zs.length = ss.length → mkIfs.liftIfs pfx d v zs ss k = .ok (es, ds, k') →
    Fa2 (fun e w => evalE D f η e = some w) es ws →
    ds = [] ∧ (x = 0 → Fa2 (fun e w => evalE D f (restrict d η) e = some w) zs ws) ∧
    (∀ k, x = k + 1 → Fa2 (fun e w => evalE D f (cons (some k) (restrict d η)) e = some w) ss ws)
  | [], [], k, es, ds, k', ws, _, h, he => by
    simp only [mkIfs.liftIfs] at h
    obtain ⟨rfl, rfl, -⟩ := Tr.pure_ok h
    cases he; exact ⟨rfl, fun _ => .nil, fun _ _ => .nil⟩
  | z :: zs, s :: ss, k, es, ds, k', ws, hl, h, he => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [mkIfs.liftIfs] at h
    obtain ⟨n, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
    obtain ⟨es', ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
    obtain ⟨rfl, rfl, -⟩ := Tr.pure_ok h4
    rw [Tr.fresh_ok h1]
    cases he with
    | cons hh ht =>
      obtain ⟨hd3, r1, r2⟩ := liftIfs_eval pfx D f η d v x hx zs ss k1 es' ds3 _ _ hl h3 ht
      simp only [evalE] at hh
      by_cases hd : d = 0
      · simp [hd] at hh
      simp only [hd, ite_false, hx] at hh
      refine ⟨by simp [hd3], fun h0 => ?_, fun k hk => ?_⟩
      · subst h0; exact .cons hh (r1 rfl)
      · subst hk; exact .cons hh (r2 k rfl)
  | [], _ :: _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _, _ => by simp at hl

/-- **A switch per slot, evaluated**: the condition's value, and the branch slots evaluated in one
environment that agrees with the switch's below its depth. -/
theorem mkIfs_eval {pfx : String} {d : Nat} {v : FExp} {zs ss : List FExp} {k : Nat} {es : List FExp}
    {ds : List FDef} {k' : Nat} (h : mkIfs pfx d v zs ss k = .ok (es, ds, k')) (hl : zs.length = ss.length)
    {D : List FDef} {f : Nat} {η : Nat → Option Nat} {ws : List Nat}
    (he : Fa2 (fun e w => evalE D f η e = some w) es ws) (hne : zs ≠ []) :
    ds = [] ∧ ∃ x, evalE D f η v = some x ∧ ∃ R : (Nat → Option Nat) → Nat → Option Nat,
      (∀ ρ i, i < d → R ρ i = ρ i) ∧
      (x = 0 → Fa2 (fun e w => evalE D f (R η) e = some w) zs ws) ∧
      (∀ k, x = k + 1 → Fa2 (fun e w => evalE D f (cons (some k) (R η)) e = some w) ss ws) := by
  obtain ⟨z, zs', rfl⟩ : ∃ z zs', zs = z :: zs' := by cases zs with | nil => exact absurd rfl hne | cons z zs' => exact ⟨z, zs', rfl⟩
  obtain ⟨s, ss', rfl⟩ : ∃ s ss', ss = s :: ss' := by cases ss with | nil => simp at hl | cons s ss' => exact ⟨s, ss', rfl⟩
  unfold mkIfs at h
  split at h
  · obtain ⟨rfl, rfl, -⟩ := Tr.pure_ok h
    simp only [List.zip_cons_cons, List.map_cons] at he
    cases he with
    | cons hh ht =>
      simp only [evalE] at hh
      cases hx : evalE D f η v with
      | none => simp [hx] at hh
      | some x =>
        have := ifz_eval_aux D f η v x hx (z :: zs') (s :: ss') _ hl (by
          simp only [List.zip_cons_cons, List.map_cons]; exact .cons (by simp only [evalE]; exact hh) ht)
        exact ⟨rfl, x, rfl, fun ρ => ρ, fun _ _ _ => rfl, this.1, this.2⟩
  · have he0 := he
    obtain ⟨n, ds1, k1, ds2, h1, h2, -⟩ := Tr.bind_ok (by simpa only [mkIfs.liftIfs] using h)
    obtain ⟨es', ds3, k2, ds4, h3, h4, -⟩ := Tr.bind_ok h2
    obtain ⟨hes, -, -⟩ := Tr.pure_ok h4
    rw [← hes] at he
    cases he with
    | cons hh ht =>
      simp only [evalE] at hh
      by_cases hd : d = 0
      · simp [hd] at hh
      simp only [hd, ite_false] at hh
      cases hx : evalE D f η v with
      | none => simp [hx] at hh
      | some x =>
        have := liftIfs_eval pfx D f η d v x hx (z :: zs') (s :: ss') k es ds k' _ hl h he0
        exact ⟨this.1, x, rfl, restrict d, fun ρ i hi => by simp [restrict, hi], this.2.1, this.2.2⟩

theorem liftIfs_length (pfx : String) (d : Nat) (v : FExp) : ∀ (zs ss : List FExp) (k : Nat) (es : List FExp)
    (ds : List FDef) (k' : Nat), mkIfs.liftIfs pfx d v zs ss k = .ok (es, ds, k') → es.length = min zs.length ss.length
  | z :: zs, s :: ss, k, es, ds, k', h => by
    simp only [mkIfs.liftIfs] at h
    obtain ⟨n, ds1, k1, ds2, h1, h2, -⟩ := Tr.bind_ok h
    obtain ⟨es', ds3, k2, ds4, h3, h4, -⟩ := Tr.bind_ok h2
    obtain ⟨rfl, -, -⟩ := Tr.pure_ok h4
    simp [liftIfs_length pfx d v zs ss k1 es' ds3 k2 h3, Nat.min_def]; split <;> omega
  | [], _, k, es, ds, k', h => by simp only [mkIfs.liftIfs] at h; obtain ⟨rfl, -, -⟩ := Tr.pure_ok h; simp
  | _ :: _, [], k, es, ds, k', h => by simp only [mkIfs.liftIfs] at h; obtain ⟨rfl, -, -⟩ := Tr.pure_ok h; simp

theorem mkIfs_length {pfx : String} {d : Nat} {v : FExp} {zs ss : List FExp} {k : Nat} {es : List FExp}
    {ds : List FDef} {k' : Nat} (h : mkIfs pfx d v zs ss k = .ok (es, ds, k')) :
    es.length = min zs.length ss.length := by
  unfold mkIfs at h
  split at h
  · obtain ⟨rfl, -, -⟩ := Tr.pure_ok h; simp
  · exact liftIfs_length pfx d v zs ss k es ds k' h

theorem swChains_length (pfx : String) (L : Nat) : ∀ (arms : List (List FExp)) (d : Nat) (scr : FExp) (k : Nat)
    (sw : List FExp) (ds : List FDef) (k' : Nat), (∀ a ∈ arms, a.length = L) →
    swChains pfx d scr arms k = .ok (sw, ds, k') → sw.length = L
  | [], _, _, _, _, _, _, _, h => absurd h (by simp [swChains]; exact fun h => Tr.fail_ok h)
  | [a], _, _, k, sw, ds, k', hl, h => by
    simp only [swChains] at h; obtain ⟨rfl, -, -⟩ := Tr.pure_ok h; exact hl a (by simp)
  | a :: b :: rest, d, scr, k, sw, ds, k', hl, h => by
    simp only [swChains] at h
    obtain ⟨r, ds1, k1, ds2, h1, h2, -⟩ := Tr.bind_ok h
    have hr := swChains_length pfx L (b :: rest) (d + 1) (.var 0) k r ds1 k1
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h1
    rw [mkIfs_length h2, hr, hl a (by simp)]; simp

theorem liftIfs_ds (pfx : String) (d : Nat) (v : FExp) : ∀ (zs ss : List FExp) (k : Nat) (es : List FExp)
    (ds : List FDef) (k' : Nat), mkIfs.liftIfs pfx d v zs ss k = .ok (es, ds, k') → ds = []
  | z :: zs, s :: ss, k, es, ds, k', h => by
    simp only [mkIfs.liftIfs] at h
    obtain ⟨n, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
    obtain ⟨es', ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
    obtain ⟨-, rfl, -⟩ := Tr.pure_ok h4
    simp [Tr.fresh_ok h1, liftIfs_ds pfx d v zs ss k1 es' ds3 k2 h3]
  | [], _, k, es, ds, k', h => by simp only [mkIfs.liftIfs] at h; exact (Tr.pure_ok h).2.1
  | _ :: _, [], k, es, ds, k', h => by simp only [mkIfs.liftIfs] at h; exact (Tr.pure_ok h).2.1

theorem mkIfs_ds {pfx : String} {d : Nat} {v : FExp} {zs ss : List FExp} {k : Nat} {es : List FExp}
    {ds : List FDef} {k' : Nat} (h : mkIfs pfx d v zs ss k = .ok (es, ds, k')) : ds = [] := by
  unfold mkIfs at h
  split at h
  · exact (Tr.pure_ok h).2.1
  · exact liftIfs_ds pfx d v zs ss k es ds k' h

theorem swChains_ds (pfx : String) : ∀ (d : Nat) (scr : FExp) (arms : List (List FExp)) (k : Nat)
    (sw : List FExp) (ds : List FDef) (k' : Nat), swChains pfx d scr arms k = .ok (sw, ds, k') → ds = []
  | _, _, [], _, _, _, _, h => absurd h (by simp [swChains]; exact fun h => Tr.fail_ok h)
  | _, _, [a], k, sw, ds, k', h => by simp only [swChains] at h; exact (Tr.pure_ok h).2.1
  | d, scr, a :: b :: rest, k, sw, ds, k', h => by
    simp only [swChains] at h
    obtain ⟨r, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
    simp [swChains_ds pfx (d + 1) (.var 0) (b :: rest) k r ds1 k1 h1, mkIfs_ds h2]

/-- **The switch chain over a tag, evaluated**: the taken arm's slots, in an environment that agrees
with the chain's below its depth, shifted by the predecessors. -/
theorem swChains_eval (pfx : String) (D : List FDef) (f L : Nat) (hL : L ≠ 0) :
    ∀ (arms : List (List FExp)) (d : Nat) (scr : FExp) (k : Nat) (sw : List FExp) (ds : List FDef) (k' : Nat)
    (E : Nat → Option Nat) (ws : List Nat) (t : Nat), (∀ a ∈ arms, a.length = L) →
    swChains pfx d scr arms k = .ok (sw, ds, k') → Fa2 (fun e w => evalE D f E e = some w) sw ws →
    (2 ≤ arms.length → evalE D f E scr = some t) → t < arms.length →
    ds = [] ∧ ∃ a E', arms[t]? = some a ∧ Fa2 (fun e w => evalE D f E' e = some w) a ws ∧
      ∀ i < d, E' (i + t) = E i
  | [], _, _, _, _, _, _, _, _, _, _, h, _, _, _ => absurd h (by simp [swChains]; exact fun h => Tr.fail_ok h)
  | [a], d, scr, k, sw, ds, k', E, ws, t, hl, h, he, _, ht => by
    simp only [swChains] at h; obtain ⟨rfl, rfl, -⟩ := Tr.pure_ok h
    simp only [List.length_singleton] at ht
    obtain rfl : t = 0 := by omega
    exact ⟨rfl, _, E, rfl, he, fun i _ => rfl⟩
  | a :: b :: rest, d, scr, k, sw, ds, k', E, ws, t, hl, h, he, hscr, ht => by
    simp only [swChains] at h
    obtain ⟨r, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
    have hrl := swChains_length pfx L (b :: rest) (d + 1) (.var 0) k r ds1 k1
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h1
    have hal := hl a (by simp)
    have hne : a ≠ [] := by intro h; rw [h] at hal; exact hL hal.symm
    obtain ⟨hds2, x, hx, R, hR, h0, hs⟩ := mkIfs_eval h2 (by rw [hal, hrl]) he hne
    have hxt : x = t := by rw [hscr (by simp)] at hx; cases hx; rfl
    subst hxt
    cases x with
    | zero => exact ⟨by simp [hds2, swChains_ds pfx _ _ _ _ _ _ _ h1], a, R E, rfl, h0 rfl, fun i hi => hR E i hi⟩
    | succ k0 =>
      have hk0 : k0 < u24Mod := by have := evalE_lt D f scr E (k0 + 1) hx; omega
      obtain ⟨hds1, a', E', ha', he', hE'⟩ := swChains_eval pfx D f L hL (b :: rest) (d + 1) (.var 0) k r ds1 k1
        (cons (some k0) (R E)) ws k0 (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h1 (hs k0 rfl)
        (fun _ => by simp [evalE, ck_of_lt hk0]) (by simp at ht ⊢; omega)
      refine ⟨by simp [hds1, hds2], a', E', by simpa using ha', he', fun i hi => ?_⟩
      have := hE' (i + 1) (by omega)
      rw [show i + (k0 + 1) = i + 1 + k0 by omega, this]
      simp only [cons_succ]; exact hR E i hi

/-! ### β under several binders -/

def liftN : Nat → (Nat → Term) → Nat → Term
  | 0, σ => σ
  | k + 1, σ => liftSubstitution (liftN k σ)

def lams : Nat → Term → Term
  | 0, b => b
  | k + 1, b => .lam (lams k b)

theorem liftN_succ' : ∀ (k : Nat) (σ : Nat → Term), liftN (k + 1) σ = liftN k (liftSubstitution σ)
  | 0, _ => rfl
  | k + 1, σ => by simp only [liftN] at *; rw [← liftN_succ' k σ]; rfl

theorem lams_subst : ∀ (k : Nat) (b : Term) (σ : Nat → Term),
    (lams k b).substitute σ = lams k (b.substitute (liftN k σ))
  | 0, _, _ => rfl
  | k + 1, b, σ => by
    simp only [lams, Term.substitute]
    rw [lams_subst k b (liftSubstitution σ), liftN_succ']

theorem liftN_bound : ∀ k : Nat, liftN k Term.bound = Term.bound
  | 0 => rfl
  | k + 1 => by
    simp only [liftN, liftN_bound k]
    funext i; cases i <;> simp [liftSubstitution, Term.rename]

theorem liftN_inst (τ : Nat → Term) (a : Term) : ∀ (j i : Nat),
    (liftN j (liftSubstitution τ) i).substitute (liftN j (single a)) = liftN j (cons a τ) i
  | 0, 0 => by simp [liftN, liftSubstitution, single]
  | 0, i + 1 => by simp only [liftN, liftSubstitution, cons_succ]; exact shift_one_cancel _ _
  | j + 1, 0 => by simp [liftN, liftSubstitution, Term.substitute]
  | j + 1, i + 1 => by
    simp only [liftN, liftSubstitution]
    rw [Obend.Core.TermTraverse.rename_substitute, ← liftN_inst τ a j i,
      Obend.Core.TermTraverse.substitute_rename]
    rfl

theorem inst_lams (k : Nat) (B a : Term) (τ : Nat → Term) :
    instantiate (lams k (B.substitute (liftN (k + 1) τ))) a = lams k (B.substitute (liftN k (cons a τ))) := by
  rw [instantiate_eq, lams_subst, Obend.Core.TermTraverse.substitute_comp, liftN_succ']
  congr 2; funext i
  exact liftN_inst τ a k i

theorem steps_applyAll {f g : Term} : ∀ (args : List Term), Obend.Core.Term.Steps f g →
    Obend.Core.Term.Steps (applyAll f args) (applyAll g args)
  | [], h => h
  | a :: args, h => steps_applyAll args (steps_app a h)

/-- Push arguments onto a substitution, the last at index 0. -/
def consAll : List Term → (Nat → Term) → Nat → Term
  | [], τ => τ
  | a :: as, τ => consAll as (cons a τ)

/-- **β under `m` binders**: `(λ…λ. B[τ]) a₁ … aₘ` reaches `B` with the arguments pushed onto `τ`. -/
theorem steps_lams (B : Term) : ∀ (args : List Term) (τ : Nat → Term),
    Obend.Core.Term.Steps (applyAll (lams args.length (B.substitute (liftN args.length τ))) args)
      (B.substitute (consAll args τ))
  | [], τ => by simp [lams, liftN, consAll, applyAll]; exact .refl _
  | a :: args, τ => by
    simp only [List.length_cons, lams, applyAll, consAll]
    refine steps_trans (steps_applyAll args (steps_one (.beta _ _))) ?_
    rw [inst_lams]
    exact steps_lams B args (cons a τ)

/-! ## 7. The translation is sound -/

/-- Every definition emitted is the one `D` finds by its name. -/
def DefsIn (D : List FDef) (ds : List FDef) : Prop := ∀ d ∈ ds, D.find? (·.name == d.name) = some d

theorem DefsIn.append {D ds₁ ds₂ : List FDef} (h : DefsIn D (ds₁ ++ ds₂)) : DefsIn D ds₁ ∧ DefsIn D ds₂ :=
  ⟨fun d hd => h d (List.mem_append_left _ hd), fun d hd => h d (List.mem_append_right _ hd)⟩

/-- What a translation's slots say about the term: wherever the environment invariant holds and the
slots evaluate exactly, the term (under the Core4 substitution) is described by the slot values. -/
def SoundAt (D : List FDef) (fuel : Nat) (Γ : List CEnt) (dep : Nat) (t : Term) (σ : HSort) (slots : List FExp) :
    Prop :=
  ∀ η σc, EnvOk D fuel Γ dep η σc → ∀ ws, Fa2 (fun e w => evalE D fuel η e = some w) slots ws →
    DecH σ ws (t.substitute σc)

def TrSound (pfx : String) (D : List FDef) (fuel : Nat) : Prop :=
  ∀ (t : Term) (Γ : List CEnt) (dep : Nat) (σ : HSort) (k : Nat) (slots : List FExp) (ds : List FDef) (k' : Nat),
    toS pfx Γ dep t σ k = .ok (slots, ds, k') → DefsIn D ds → SoundAt D fuel Γ dep t σ slots

theorem fa2_single {R : FExp → Nat → Prop} {e : FExp} {ws : List Nat} (h : Fa2 R [e] ws) : ∃ w, ws = [w] ∧ R e w := by
  cases h with
  | cons hr ht => cases ht; exact ⟨_, rfl, hr⟩

theorem Tr.fail_ok' {α : Type} {e : String} {k : Nat} {r : α × List FDef × Nat} :
    (Tr.fail e : Tr α) k ≠ .ok r := fun h => Tr.fail_ok h

theorem fa2_vars (D : List FDef) (f : Nat) (η : Nat → Option Nat) (dep : Nat) : ∀ (lvls : List Nat) (ws : List Nat),
    Fa2 (fun e w => evalE D f η e = some w) (lvls.map fun ℓ => FExp.var (dep - 1 - ℓ)) ws →
    lvls.map (lvlVal dep η) = ws.map some
  | [], _, h => by cases h; rfl
  | ℓ :: lvls, _, h => by
    cases h with
    | cons hh ht =>
      simp only [evalE] at hh
      cases hη : η (dep - 1 - ℓ) with
      | none => simp [hη] at hh
      | some u =>
        simp only [hη, Option.bind_some] at hh
        obtain ⟨rfl, -⟩ := ck_some hh
        simp [lvlVal, hη, fa2_vars D f η dep lvls _ ht]

theorem map_some_inj : ∀ {as bs : List Nat}, as.map some = bs.map some → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h; rw [h.1, map_some_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem armIdx_spec {β : Type} : ∀ {l : List (String × β)} {n : String} {j : Nat} {v : β},
    armIdx l n = some (j, v) → l[j]? = some (n, v) ∧ l.find? (fun p => p.1 == n) = some (n, v)
  | [], _, _, _, h => by simp [armIdx] at h
  | (l, v') :: rest, n, j, v, h => by
    simp only [armIdx] at h
    split at h
    · rename_i hl; cases h; subst hl; simp
    · rename_i hl
      cases hr : armIdx rest n with
      | none => simp [hr] at h
      | some p =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        obtain ⟨j', v''⟩ := p
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := armIdx_spec hr
        simp [h1, h2, hl]

theorem maxW_ge : ∀ {arms : List (String × VSort)} {j : Nat} {l : String} {v : VSort},
    arms[j]? = some (l, v) → v.width ≤ maxW arms
  | [], _, _, _, h => by simp at h
  | a :: arms, 0, l, v, h => by simp at h; subst h; exact Nat.le_max_left _ _
  | a :: arms, j + 1, l, v, h => by
    have := maxW_ge (arms := arms) (by simpa using h); simp only [maxW]; omega

theorem EnvOk.consEnt {D : List FDef} {fuel : Nat} {Γ : List CEnt} {dep : Nat} {η : Nat → Option Nat}
    {σc : Nat → Term} {t : Term} {e : CEnt} (h : EnvOk D fuel Γ dep η σc) (he : EntOk D fuel dep η t e) :
    EnvOk D fuel (e :: Γ) dep η (cons t σc) := by
  intro i e' hi
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact he
  | succ i => simp only [List.getElem?_cons_succ] at hi; exact h i e' hi

theorem letChain_all (D : List FDef) (f : Nat) (η : Nat → Option Nat) (as : List FExp) (xs : List Nat)
    (hxs : Fa2 (fun e w => evalE D f η e = some w) as xs) : ∀ (bs : List FExp) (ws : List Nat),
    Fa2 (fun e w => evalE D f η e = some w) (bs.map (letChain as)) ws →
    Fa2 (fun e w => evalE D f (pushAll (xs.map some) η) e = some w) bs ws
  | [], _, h => by cases h; exact .nil
  | b :: bs, _, h => by
    cases h with
    | cons hh ht =>
      obtain ⟨xs', hxs', hb⟩ := evalE_letChain D f η as b _ hh
      rw [fa2_det hxs' hxs] at hb
      exact .cons hb (letChain_all D f η as xs hxs bs _ ht)

theorem lvlRange_length : ∀ (a m : Nat), (lvlRange a m).length = m
  | _, 0 => rfl
  | a, m + 1 => by simp [lvlRange, lvlRange_length (a + 1) m]

theorem mem_lvlRange {a m ℓ : Nat} : ℓ ∈ lvlRange a m ↔ a ≤ ℓ ∧ ℓ < a + m := by
  induction m generalizing a with
  | zero => simp [lvlRange]
  | succ m ih => simp only [lvlRange, List.mem_cons, ih]; omega

theorem lvlRange_vals (η : Nat → Option Nat) (dep : Nat) : ∀ (xs : List (Option Nat)) (i : Nat), i ≤ xs.length →
    (lvlRange (dep + i) (xs.length - i)).map (lvlVal (dep + xs.length) (pushAll xs η)) = xs.drop i := by
  intro xs i hi
  obtain ⟨m, hm⟩ : ∃ m, xs.length - i = m := ⟨_, rfl⟩
  induction m generalizing i with
  | zero =>
    rw [hm]; simp only [lvlRange, List.map_nil]
    rw [List.drop_eq_nil_of_le (by omega)]
  | succ m ih =>
    rw [hm]; simp only [lvlRange, List.map_cons]
    have ih' := ih (i + 1) (by omega) (by omega)
    rw [show xs.length - (i + 1) = m by omega] at ih'
    rw [show dep + i + 1 = dep + (i + 1) by omega, ih', lvlVal_push_new xs η dep i (by omega)]
    rw [List.drop_eq_getElem_cons (show i < xs.length by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < xs.length by omega)]

theorem lvlRange_vals0 (η : Nat → Option Nat) (dep : Nat) (xs : List (Option Nat)) :
    (lvlRange dep xs.length).map (lvlVal (dep + xs.length) (pushAll xs η)) = xs := by
  simpa using lvlRange_vals η dep xs 0 (Nat.zero_le _)

theorem bindEnv_revRange_get : ∀ (N : Nat) (vs : List (Option Nat)), vs.length = N → ∀ i,
    bindEnv (revRange N) vs i = if i < N then vs.getD (N - 1 - i) none else none
  | 0, [], _, i => by simp [bindEnv, revRange]
  | N + 1, v :: vs, hl, i => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [revRange, bindEnv]
    by_cases h : i = N
    · subst h; simp
    · rw [if_neg h, bindEnv_revRange_get N vs hl i]
      by_cases h' : i < N
      · rw [if_pos h', if_pos (by omega), show N + 1 - 1 - i = (N - 1 - i) + 1 by omega]; simp
      · rw [if_neg h', if_neg (by omega)]
  | 0, _ :: _, hl, _ => by simp at hl
  | _ + 1, [], hl, _ => by simp at hl

theorem lvlVal_bindEnv (N : Nat) (vs : List (Option Nat)) (hl : vs.length = N) (ℓ : Nat) (hℓ : ℓ < N) :
    lvlVal N (bindEnv (revRange N) vs) ℓ = vs.getD ℓ none := by
  simp only [lvlVal, bindEnv_revRange_get N vs hl]
  rw [if_pos (by omega)]; congr 1; omega

theorem lvlRange_split : ∀ (a m₁ m₂ : Nat), lvlRange a (m₁ + m₂) = lvlRange a m₁ ++ lvlRange (a + m₁) m₂
  | a, 0, m₂ => by simp [lvlRange]
  | a, m₁ + 1, m₂ => by
    rw [show m₁ + 1 + m₂ = (m₁ + m₂) + 1 by omega]
    simp only [lvlRange, List.cons_append, lvlRange_split (a + 1) m₁ m₂]
    rw [show a + 1 + m₁ = a + (m₁ + 1) by omega]

theorem getD_lvlRange_map (f : Nat → Option Nat) : ∀ (a m ℓ : Nat), ℓ < m →
    ((lvlRange a m).map f).getD ℓ none = f (a + ℓ)
  | a, m + 1, 0, _ => by simp [lvlRange]
  | a, m + 1, ℓ + 1, h => by
    simp only [lvlRange, List.map_cons, List.getD_cons_succ]
    rw [getD_lvlRange_map f (a + 1) m ℓ (by omega)]; congr 1; omega

theorem getD_app {α : Type} (l₁ l₂ : List α) (i : Nat) (d : α) :
    (l₁ ++ l₂).getD i d = if i < l₁.length then l₁.getD i d else l₂.getD (i - l₁.length) d := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by assumption)]
  · rw [List.getElem?_append_right (by omega)]

/-- The environment a recursive call's body sees, at the call site's values. -/
theorem restrict_push_eq (η : Nat → Option Nat) (dep : Nat) (xs : List (Option Nat)) :
    restrict (dep + xs.length) (pushAll xs η) =
      bindEnv (revRange (dep + xs.length)) ((lvlRange 0 dep).map (lvlVal dep η) ++ xs) := by
  funext i
  rw [bindEnv_revRange_get _ _ (by simp [lvlRange_length])]
  simp only [restrict]
  by_cases hi : i < dep + xs.length
  · rw [if_pos hi, if_pos hi, pushAll_get]
    by_cases hx : i < xs.length
    · rw [if_pos hx, getD_app, if_neg (by simp [lvlRange_length]; omega)]
      simp only [List.length_map, lvlRange_length]; congr 1; omega
    · rw [if_neg hx, getD_app, if_pos (by simp [lvlRange_length]; omega),
        getD_lvlRange_map _ 0 dep _ (by omega)]
      simp only [lvlVal]; congr 1; omega
  · rw [if_neg hi, if_neg hi]

theorem lvlRange_map_eq (f : Nat → Option Nat) : ∀ (a m : Nat) (l : List (Option Nat)), l.length = m →
    (∀ i < m, f (a + i) = l.getD i none) → (lvlRange a m).map f = l
  | _, 0, [], _, _ => rfl
  | a, m + 1, x :: l, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [lvlRange, List.map_cons, List.cons.injEq]
    refine ⟨by simpa using h 0 (by omega), lvlRange_map_eq f (a + 1) m l hl (fun i hi => ?_)⟩
    have := h (i + 1) (by omega)
    rw [show a + (i + 1) = a + 1 + i by omega] at this
    simpa using this
  | _, 0, _ :: _, hl, _ => by simp at hl
  | _, _ + 1, [], hl, _ => by simp at hl

/-- **A fixpoint applied**: `fix (λrec. λsup. λx. body) i` applied to `a` reaches `body` with `a`, `i`
and the fixpoint itself bound. -/
theorem steps_fix (body I a : Term) (σc : Nat → Term) :
    Obend.Core.Term.Steps (.app ((Term.fix (.lam (.lam (.lam body))) I).substitute σc) a)
      (body.substitute (cons a (cons (I.substitute σc)
        (cons ((Term.fix (.lam (.lam (.lam body))) I).substitute σc) σc)))) := by
  have h := steps_lams body [(Term.fix (.lam (.lam (.lam body))) I).substitute σc, I.substitute σc, a] σc
  simp only [Term.substitute] at h ⊢
  exact .next (.application a (.fix _ _)) h

theorem find?_nodup_get {β : Type} : ∀ {l : List (String × β)} {j : Nat} {n : String} {b : β},
    (l.map (·.1)).Nodup → l[j]? = some (n, b) → l.find? (fun p => p.1 == n) = some (n, b)
  | [], _, _, _, _, h => by simp at h
  | (m, c) :: l, 0, n, b, _, h => by simp at h; obtain ⟨rfl, rfl⟩ := h; simp
  | (m, c) :: l, j + 1, n, b, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.getElem?_cons_succ] at h
    have hm : m ≠ n := by
      intro e; subst e
      exact hnd.1 ⟨(m, b), List.mem_of_getElem? h, rfl⟩
    simp [hm, find?_nodup_get hnd.2 h]

theorem armIdx_of_get {β : Type} : ∀ {l : List (String × β)} {j : Nat} {n : String} {b : β},
    (l.map (·.1)).Nodup → l[j]? = some (n, b) → armIdx l n = some (j, b)
  | [], _, _, _, _, h => by simp at h
  | (m, c) :: l, 0, n, b, _, h => by simp at h; obtain ⟨rfl, rfl⟩ := h; simp [armIdx]
  | (m, c) :: l, j + 1, n, b, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.getElem?_cons_succ] at h
    have hm : m ≠ n := by
      intro e; subst e
      exact hnd.1 ⟨(m, b), List.mem_of_getElem? h, rfl⟩
    simp [armIdx, hm, armIdx_of_get hnd.2 h]

theorem fa2_append {R : FExp → Nat → Prop} : ∀ {l₁ l₂ : List FExp} {ws : List Nat}, Fa2 R (l₁ ++ l₂) ws →
    ∃ ws₁ ws₂, ws = ws₁ ++ ws₂ ∧ Fa2 R l₁ ws₁ ∧ Fa2 R l₂ ws₂
  | [], _, ws, h => ⟨[], ws, rfl, .nil, h⟩
  | e :: l₁, l₂, _, .cons hh ht => by
    obtain ⟨ws₁, ws₂, rfl, h1, h2⟩ := fa2_append ht
    exact ⟨_ :: ws₁, ws₂, rfl, .cons hh h1, h2⟩

theorem mapM_get {α β : Type} (f : α → Option β) : ∀ {l : List α} {r : List β}, l.mapM f = some r →
    ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, f a = some b ∧ r[i]? = some b
  | [], r, h, i, a, ha => by simp at ha
  | x :: l, r, h, i, a, ha => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hl : l.mapM f with
      | none => simp [hx, hl] at h
      | some ys =>
        simp [hx, hl] at h
        subst h
        cases i with
        | zero => simp at ha; subst ha; exact ⟨y, hx, rfl⟩
        | succ i => simpa using mapM_get f hl i a (by simpa using ha)

theorem mapM_length {α β : Type} (f : α → Option β) : ∀ {l : List α} {r : List β}, l.mapM f = some r →
    r.length = l.length
  | [], r, h => by simp at h; subst h; rfl
  | x :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hl : l.mapM f with
      | none => simp [hx, hl] at h
      | some ys => simp [hx, hl] at h; subst h; simp [mapM_length f hl]

theorem toFields_sound (pfx : String) (D : List FDef) (fuel : Nat) (Γ : List CEnt) (dep : Nat) :
    ∀ (fs : List (String × Term)) (sfs : List (String × Scalar)) (k : Nat) (slots : List FExp) (ds : List FDef)
      (k' : Nat), (∀ p ∈ fs, ∀ (σ : HSort) (k : Nat) (slots : List FExp) (ds : List FDef) (k' : Nat),
        toS pfx Γ dep p.2 σ k = .ok (slots, ds, k') → DefsIn D ds → SoundAt D fuel Γ dep p.2 σ slots) →
      toFields pfx Γ dep fs sfs k = .ok (slots, ds, k') → DefsIn D ds →
      fs.map (·.1) = sfs.map (·.1) ∧ slots.length = sfs.length ∧
      ∀ η σc, EnvOk D fuel Γ dep η σc → ∀ ws, Fa2 (fun e w => evalE D fuel η e = some w) slots ws →
        ∀ (j : Nat) (p : String × Term) (q : String × Scalar) (w : Nat), fs[j]? = some p → sfs[j]? = some q →
          ws[j]? = some w → DecS q.2 w (p.2.substitute σc)
  | [], [], k, slots, ds, k', _, h, _ => by
    unfold toFields at h; obtain ⟨rfl, -, -⟩ := Tr.pure_ok h
    exact ⟨rfl, rfl, fun _ _ _ _ _ _ j p q w hp => by simp at hp⟩
  | (n, t) :: fs, (n', s) :: sfs, k, slots, ds, k', IHfs, h, hD => by
    unfold toFields at h
    split at h
    · rename_i hn
      subst hn
      obtain ⟨ft, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
      obtain ⟨rest, ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
      obtain ⟨hD1, hD2⟩ := hD.append
      obtain ⟨hD3, -⟩ := hD2.append
      split at h4
      · rename_i e
        obtain ⟨rfl, -, -⟩ := Tr.pure_ok h4
        have st := IHfs (n, t) (by simp) _ k _ _ _ h1 hD1
        obtain ⟨hnm, hlen, hrest⟩ := toFields_sound pfx D fuel Γ dep fs sfs k1 rest ds3 k2
          (fun p hp => IHfs p (List.mem_cons_of_mem _ hp)) h3 hD3
        refine ⟨by simp [hnm], by simp [hlen], fun η σc hE ws hws j p q w hp hq hw => ?_⟩
        cases hws with
        | cons hh ht =>
          cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hq hw
            subst hp hq hw
            obtain ⟨w', hw', dS⟩ := st η σc hE [_] (.cons hh .nil)
            simp only [List.cons.injEq, and_true] at hw'; subst hw'; exact dS
          | succ j =>
            exact hrest η σc hE _ ht j p q w (by simpa using hp) (by simpa using hq) (by simpa using hw)
      · exact absurd h4 Tr.fail_ok'
    · exact absurd h Tr.fail_ok'
  | [], _ :: _, k, slots, ds, k', _, h, _ => by unfold toFields at h; exact absurd h Tr.fail_ok'
  | _ :: _, [], k, slots, ds, k', _, h, _ => by unfold toFields at h; exact absurd h Tr.fail_ok'

theorem toArms_sound (pfx : String) (D : List FDef) (fuel : Nat) (Γ : List CEnt) (pl base : Nat)
    (sarms : List (String × VSort)) (σ : HSort) :
    ∀ (arms : List (String × Term)) (k : Nat) (tr : List (String × List FExp)) (ds : List FDef) (k' : Nat),
      (∀ p ∈ arms, ∀ (Γ' : List CEnt) (dep' : Nat) (σ' : HSort) (k : Nat) (slots : List FExp) (ds : List FDef)
        (k' : Nat), toS pfx Γ' dep' p.2 σ' k = .ok (slots, ds, k') → DefsIn D ds → SoundAt D fuel Γ' dep' p.2 σ' slots) →
      toArms pfx Γ pl base sarms σ arms k = .ok (tr, ds, k') → DefsIn D ds →
      ∀ l e, tr.lookup l = some e → ∃ body kk v, arms.find? (fun p => p.1 == l) = some (l, body) ∧
        armIdx sarms l = some (kk, v) ∧ SoundAt D fuel (.val (.val v) (lvlRange pl v.width) :: Γ) (base + kk) body σ e
  | [], k, tr, ds, k', _, h, _, l, e, he => by
    unfold toArms at h; obtain ⟨rfl, -, -⟩ := Tr.pure_ok h; simp at he
  | (l0, b0) :: rest, k, tr, ds, k', IHa, h, hD, l, e, he => by
    unfold toArms at h
    cases hi : armIdx sarms l0 with
    | none =>
      simp only [hi] at h
      obtain ⟨body, kk, v, hf, hidx, hs⟩ := toArms_sound pfx D fuel Γ pl base sarms σ rest k tr ds k'
        (fun p hp => IHa p (List.mem_cons_of_mem _ hp)) h hD l e he
      have hne : l0 ≠ l := by intro e; subst e; rw [hi] at hidx; cases hidx
      exact ⟨body, kk, v, by simp [hne, hf], hidx, hs⟩
    | some q =>
      obtain ⟨kk0, v0⟩ := q
      simp only [hi] at h
      obtain ⟨e0, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
      obtain ⟨es, ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
      obtain ⟨rfl, -, -⟩ := Tr.pure_ok h4
      obtain ⟨hD1, hD2⟩ := hD.append
      obtain ⟨hD3, -⟩ := hD2.append
      by_cases hl : l0 = l
      · subst hl
        simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at he
        subst he
        exact ⟨b0, kk0, v0, by simp, hi, IHa (l0, b0) (by simp) _ _ _ k _ _ _ h1 hD1⟩
      · have hl' : (l == l0) = false := by simp [Ne.symm hl]
        simp only [List.lookup_cons, hl'] at he
        obtain ⟨body, kk, v, hf, hidx, hs⟩ := toArms_sound pfx D fuel Γ pl base sarms σ rest k1 es ds3 k2
          (fun p hp => IHa p (List.mem_cons_of_mem _ hp)) h3 hD3 l e he
        exact ⟨body, kk, v, by simp [hl, hf], hidx, hs⟩

theorem toS_sound_aux (pfx : String) (D : List FDef) (fuel : Nat) (IHf : ∀ f' < fuel, TrSound pfx D f') :
    ∀ (n : Nat) (t : Term), sizeOf t < n → ∀ (Γ : List CEnt) (dep : Nat) (σ : HSort) (k : Nat) (slots : List FExp)
      (ds : List FDef) (k' : Nat), toS pfx Γ dep t σ k = .ok (slots, ds, k') → DefsIn D ds →
      SoundAt D fuel Γ dep t σ slots
  | 0, t, ht => absurd ht (Nat.not_lt_zero _)
  | n + 1, t, ht => by
    intro Γ dep σ k slots ds k' h hD
    have IH := toS_sound_aux pfx D fuel IHf n
    cases t with
    | nat v =>
      unfold toS at h
      split at h
      · rename_i hc
        obtain ⟨rfl, -, -⟩ := Tr.pure_ok h
        obtain ⟨rfl, -⟩ := hc
        intro η σc _ ws hws
        obtain ⟨w, rfl, hw⟩ := fa2_single hws
        simp only [evalE] at hw
        obtain ⟨rfl, -⟩ := ck_some hw
        exact ⟨_, rfl, by simp only [Term.substitute, Scalar.lit]; exact .refl _, trivial⟩
      · exact absurd h Tr.fail_ok'
    | boolean b =>
      unfold toS at h
      split at h
      · rename_i hc
        obtain ⟨rfl, -, -⟩ := Tr.pure_ok h
        subst hc
        intro η σc _ ws hws
        obtain ⟨w, rfl, hw⟩ := fa2_single hws
        simp only [evalE] at hw
        obtain ⟨rfl, -⟩ := ck_some hw
        refine ⟨_, rfl, ?_, ?_⟩
        · cases b <;> simp only [Term.substitute, Scalar.lit] <;> exact .refl _
        · cases b <;> simp [Scalar.valid]
      · exact absurd h Tr.fail_ok'
    | bound i =>
      unfold toS at h
      cases hi : Γ[i]? with
      | none => simp only [hi] at h; exact absurd h Tr.fail_ok'
      | some e =>
      cases e with
      | fn => simp only [hi] at h; exact absurd h Tr.fail_ok'
      | none => simp only [hi] at h; exact absurd h Tr.fail_ok'
      | val s lvls =>
        simp only [hi] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, -, -⟩ := Tr.pure_ok h
          obtain ⟨rfl, -⟩ := hc
          intro η σc hE ws hws
          obtain ⟨-, ws', hw', hdec⟩ := hE i _ hi
          rw [fa2_vars D fuel η dep lvls ws hws] at hw'
          rw [map_some_inj hw']
          simpa only [Term.substitute] using hdec
        · exact absurd h Tr.fail_ok'
    | binary op l r =>
      unfold toS at h
      cases hb : binOp op with
      | none => simp only [hb] at h; exact absurd h Tr.fail_ok'
      | some q =>
        obtain ⟨sl, sr, s, body⟩ := q
        simp only [hb] at h
        split at h
        · rename_i hσ
          subst hσ
          obtain ⟨fl, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
          obtain ⟨fr, ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
          obtain ⟨hD1, hD2⟩ := hD.append
          obtain ⟨hD3, -⟩ := hD2.append
          split at h4
          · rename_i a b
            obtain ⟨rfl, -, -⟩ := Tr.pure_ok h4
            simp only [Term.binary.sizeOf_spec] at ht
            have sl' := IH l (by omega) Γ dep _ k _ _ _ h1 hD1
            have sr' := IH r (by omega) Γ (dep + 1) _ k1 _ _ _ h3 hD3
            intro η σc hE ws hws
            obtain ⟨w, rfl, hw⟩ := fa2_single hws
            simp only [evalE] at hw
            cases ha : evalE D fuel η a with
            | none => simp [ha] at hw
            | some x =>
              simp only [ha] at hw
              cases hb' : evalE D fuel (cons (some x) η) b with
              | none => simp [hb'] at hw
              | some y =>
                simp only [hb'] at hw
                obtain ⟨x', hx', dl⟩ := sl' η σc hE [x] (.cons ha .nil)
                obtain ⟨y', hy', dr⟩ := sr' (cons (some x) η) σc (hE.cons1 _) [y] (.cons hb' .nil)
                simp only [List.cons.injEq, and_true] at hx' hy'
                subst hx' hy'
                obtain ⟨hp, hv⟩ := binOp_sound hb D fuel η (evalE_lt D fuel a η _ ha)
                  (evalE_lt D fuel b _ _ hb') dl.2 dr.2 hw
                refine ⟨w, rfl, ?_, hv⟩
                simp only [Term.substitute]
                exact steps_trans (steps_binaryLeft op _ dl.1)
                  (steps_trans (steps_binaryRight op (sl.lit_value _) dr.1)
                    (steps_one (.primitive op _ _ _ (sl.lit_value _) (sr.lit_value _) hp)))
          · exact absurd h4 Tr.fail_ok'
        · exact absurd h Tr.fail_ok'
    | ifZero v z s' =>
      unfold toS at h
      split at h
      · exact absurd h Tr.fail_ok'
      · obtain ⟨fv, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
        obtain ⟨zs, ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
        obtain ⟨ss, ds5, k3, ds6, h5, h6, rfl⟩ := Tr.bind_ok h4
        obtain ⟨hD1, hD2⟩ := hD.append
        obtain ⟨hD3, hD4⟩ := hD2.append
        obtain ⟨hD5, -⟩ := hD4.append
        split at h6
        · rename_i a
          split at h6
          · rename_i hl
            simp only [Term.ifZero.sizeOf_spec] at ht
            have sv := IH v (by omega) Γ dep _ k _ _ _ h1 hD1
            have sz := IH z (by omega) Γ dep _ k1 _ _ _ h3 hD3
            have ss' := IH s' (by omega) _ (dep + 1) _ k2 _ _ _ h5 hD5
            intro η σc hE ws hws
            obtain ⟨-, x, hx, R, hR, h0, hsucc⟩ := mkIfs_eval h6 hl.1 hws hl.2
            obtain ⟨x', hx', dv⟩ := sv η σc hE [x] (.cons hx .nil)
            simp only [List.cons.injEq, and_true] at hx'
            subst hx'
            simp only [Term.substitute]
            cases x with
            | zero =>
              have dz := sz (R η) σc (hE.restrict R hR) ws (h0 rfl)
              exact DecH.steps (steps_trans (steps_ifZero _ _ dv.1) (steps_one (.zero _ _))) dz
            | succ k0 =>
              have hE' : EnvOk D fuel (.val (.val (.sc .nat)) [dep] :: Γ) (dep + 1) (cons (some k0) (R η))
                  (cons (.nat k0) σc) :=
                ((hE.restrict R hR).cons1 _).consEnt ⟨by simp, [k0], by simp [lvlVal], ⟨k0, rfl, .refl _, trivial⟩⟩
              have ds' := ss' _ _ hE' ws (hsucc k0 rfl)
              refine DecH.steps (steps_trans (steps_ifZero _ _ dv.1) (steps_one (.successor _ _ _))) ?_
              rw [inst_lift]; exact ds'
          · exact absurd h6 Tr.fail_ok'
        · exact absurd h6 Tr.fail_ok'
    | ifBool c t' f =>
      unfold toS at h
      split at h
      · exact absurd h Tr.fail_ok'
      · obtain ⟨fc, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
        obtain ⟨ts, ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
        obtain ⟨fs, ds5, k3, ds6, h5, h6, rfl⟩ := Tr.bind_ok h4
        obtain ⟨hD1, hD2⟩ := hD.append
        obtain ⟨hD3, hD4⟩ := hD2.append
        obtain ⟨hD5, -⟩ := hD4.append
        split at h6
        · rename_i a
          split at h6
          · rename_i hl
            simp only [Term.ifBool.sizeOf_spec] at ht
            have sc := IH c (by omega) Γ dep _ k _ _ _ h1 hD1
            have st := IH t' (by omega) Γ (dep + 1) _ k1 _ _ _ h3 hD3
            have sf := IH f (by omega) Γ dep _ k2 _ _ _ h5 hD5
            intro η σc hE ws hws
            obtain ⟨-, x, hx, R, hR, h0, hsucc⟩ := mkIfs_eval h6 hl.1 hws hl.2
            obtain ⟨x', hx', dc⟩ := sc η σc hE [x] (.cons hx .nil)
            simp only [List.cons.injEq, and_true] at hx'
            subst hx'
            simp only [Term.substitute]
            have vx := dc.2
            simp only [Scalar.valid] at vx
            cases x with
            | zero =>
              have df := sf (R η) σc (hE.restrict R hR) ws (h0 rfl)
              exact DecH.steps (steps_trans (steps_ifBool _ _ dc.1) (steps_one (.ifFalse _ _))) df
            | succ k0 =>
              have dt := st _ σc ((hE.restrict R hR).cons1 (some k0)) ws (hsucc k0 rfl)
              exact DecH.steps (steps_trans (steps_ifBool _ _ dc.1) (by simp [Scalar.lit]; exact steps_one (.ifTrue _ _))) dt
          · exact absurd h6 Tr.fail_ok'
        · exact absurd h6 Tr.fail_ok'
    | app f a =>
      cases f with
      | lam b =>
        unfold toS at h
        split at h
        · exact absurd h Tr.fail_ok'
        · obtain ⟨sa, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
          obtain ⟨-, rfl⟩ := Tr.ofExcept_ok h1
          obtain ⟨as, ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
          obtain ⟨bs, ds5, k3, ds6, h5, h6, rfl⟩ := Tr.bind_ok h4
          split at h6
          · exact absurd h6 Tr.fail_ok'
          · rename_i hbs
            obtain ⟨rfl, -, -⟩ := Tr.pure_ok h6
            obtain ⟨-, hD2⟩ := hD.append
            obtain ⟨hD3, hD4⟩ := hD2.append
            obtain ⟨hD5, -⟩ := hD4.append
            simp only [Term.app.sizeOf_spec, Term.lam.sizeOf_spec] at ht
            have sa' := IH a (by omega) Γ dep sa k1 as ds3 k2 h3 hD3
            have sb' := IH b (by omega) _ (dep + as.length) σ k2 bs ds5 k3 h5 hD5
            intro η σc hE ws hws
            obtain ⟨b0, bs', rfl⟩ : ∃ b0 bs', bs = b0 :: bs' := by
              cases bs with | nil => exact absurd rfl hbs | cons b0 bs' => exact ⟨b0, bs', rfl⟩
            cases hws with
            | cons hh ht' =>
              obtain ⟨xs, hxs, -⟩ := evalE_letChain D fuel η as b0 _ hh
              have hall := letChain_all D fuel η as xs hxs (b0 :: bs') _ (.cons hh ht')
              have da := sa' η σc hE xs hxs
              have hlen : (xs.map some).length = as.length := by simp [fa2_length hxs]
              have hE' : EnvOk D fuel (.val sa (lvlRange dep as.length) :: Γ) (dep + as.length)
                  (pushAll (xs.map some) η) (cons (a.substitute σc) σc) := by
                refine (hlen ▸ hE.push (xs.map some)).consEnt ⟨fun ℓ hℓ => ?_, xs, ?_, da⟩
                · have := mem_lvlRange.1 hℓ; omega
                · rw [← hlen, lvlRange_vals0]
              have db := sb' _ _ hE' _ hall
              simp only [Term.substitute]
              refine DecH.steps (steps_one (.beta _ _)) ?_
              rw [inst_lift]; exact db
      | bound i =>
        unfold toS at h
        cases hi : Γ[i]? with
        | none => simp only [hi] at h; exact absurd h Tr.fail_ok'
        | some e =>
        cases e with
        | val => simp only [hi] at h; exact absurd h Tr.fail_ok'
        | none => simp only [hi] at h; exact absurd h Tr.fail_ok'
        | fn g cap sa res =>
          simp only [hi] at h
          split at h
          · rename_i hσ
            subst hσ
            obtain ⟨as, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
            obtain ⟨rfl, rfl, -⟩ := Tr.pure_ok h2
            obtain ⟨hD1, -⟩ := hD.append
            simp only [Term.app.sizeOf_spec] at ht
            have sa' := IH a (by omega) Γ dep sa k as ds1 k1 h1 hD1
            intro η σc hE ws hws
            obtain ⟨w, rfl, hw⟩ := fa2_single hws
            obtain ⟨xs, hxs, hcall⟩ := evalE_letChain D fuel η as _ w hw
            have da := sa' η σc hE xs hxs
            obtain ⟨hcap, hfun⟩ := hE i _ hi
            cases fuel with
            | zero => simp [evalE] at hcall
            | succ f =>
              simp only [evalE] at hcall
              cases hd : D.find? (·.name == g) with
              | none => simp [hd] at hcall
              | some d =>
                simp only [hd] at hcall
                split at hcall
                · have hlen : (xs.map some).length = as.length := by simp [fa2_length hxs]
                  have hargs : ((cap ++ lvlRange dep as.length).map fun ℓ => dep + as.length - 1 - ℓ).map
                      (pushAll (xs.map some) η) = cap.map (lvlVal dep η) ++ xs.map some := by
                    rw [List.map_map, List.map_append]
                    congr 1
                    · apply List.map_congr_left; intro ℓ hℓ
                      have := lvlVal_push (xs.map some) η dep ℓ (hcap ℓ hℓ)
                      rw [hlen] at this; exact this
                    · have := lvlRange_vals0 η dep (xs.map some)
                      rw [hlen] at this
                      exact this
                  rw [hargs] at hcall
                  have := hfun f (Nat.lt_succ_self _) (a.substitute σc) xs d w da hd hcall
                  exact ⟨w, rfl, by simpa only [Term.substitute] using this⟩
                · exact absurd hcall (by simp)
          · exact absurd h Tr.fail_ok'
      | fix sp i0 =>
        cases sp with
        | lam sp1 =>
          cases sp1 with
          | lam sp2 =>
            cases sp2 with
            | lam body =>
              unfold toS at h
              cases σ with
              | sum _ => exact absurd h Tr.fail_ok'
              | val v =>
              cases v with
              | rcd _ => exact absurd h Tr.fail_ok'
              | sc res =>
                obtain ⟨sa, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
                obtain ⟨-, rfl⟩ := Tr.ofExcept_ok h1
                obtain ⟨as, ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
                split at h4
                · exact absurd h4 Tr.fail_ok'
                · rename_i has
                  obtain ⟨kk, ds5, k3, ds6, h5, h6, rfl⟩ := Tr.bind_ok h4
                  rw [Tr.fresh_ok h5] at hD
                  obtain ⟨fb, ds7, k4, ds8, h7, h8, rfl⟩ := Tr.bind_ok h6
                  split at h8
                  · rename_i b
                    obtain ⟨u, ds9, k5, ds10, h9, h10, rfl⟩ := Tr.bind_ok h8
                    rw [Tr.emit_ok h9] at hD
                    obtain ⟨rfl, rfl, -⟩ := Tr.pure_ok h10
                    obtain ⟨-, hD2⟩ := hD.append
                    obtain ⟨hD3, hD4⟩ := hD2.append
                    obtain ⟨-, hD6⟩ := hD4.append
                    obtain ⟨hD7, hD8⟩ := hD6.append
                    obtain ⟨hD9, -⟩ := hD8.append
                    have hfd := hD9 _ (List.mem_singleton_self _)
                    simp only at hfd
                    simp only [Term.app.sizeOf_spec, Term.fix.sizeOf_spec, Term.lam.sizeOf_spec] at ht
                    have sa' := IH a (by omega) Γ dep sa k1 as ds3 k2 h3 hD3
                    have has' : as.length = sa.width := by simpa using has
                    intro η σc hE ws hws
                    have hcapl : ((lvlRange 0 dep).map (lvlVal dep η)).length = dep := by simp [lvlRange_length]
                    -- the function's soundness, at every fuel below this one
                    have key : ∀ f', (∀ f'' < f', f'' < fuel → FunOk D f'' s!"{pfx}.f{kk}"
                          ((lvlRange 0 dep).map (lvlVal dep η)) sa res
                          ((Term.fix (.lam (.lam (.lam body))) i0).substitute σc)) → f' < fuel →
                        FunOk D f' s!"{pfx}.f{kk}" ((lvlRange 0 dep).map (lvlVal dep η)) sa res
                          ((Term.fix (.lam (.lam (.lam body))) i0).substitute σc) := by
                      intro f' hlower hlt a0 ws0 d0 w0 hda hd0 hev
                      rw [hfd] at hd0; cases hd0
                      simp only at hev
                      have hws0 : (ws0.map some).length = as.length := by simp [DecH.length hda, has']
                      have hvl : ((lvlRange 0 dep).map (lvlVal dep η) ++ ws0.map some).length = dep + as.length := by
                        simp [lvlRange_length, hws0]
                      have hlv : ∀ ℓ < dep, lvlVal (dep + as.length)
                          (bindEnv (revRange (dep + as.length)) ((lvlRange 0 dep).map (lvlVal dep η) ++ ws0.map some)) ℓ =
                          lvlVal dep η ℓ := by
                        intro ℓ hℓ
                        rw [lvlVal_bindEnv _ _ hvl ℓ (by omega), getD_app, if_pos (by simp [lvlRange_length]; omega),
                          getD_lvlRange_map _ 0 dep ℓ hℓ, Nat.zero_add]
                      have sb := IHf f' hlt body _ (dep + as.length) _ k3 [b] ds7 k4 h7 hD7
                      have hbase : EnvOk D f' Γ (dep + as.length)
                          (bindEnv (revRange (dep + as.length)) ((lvlRange 0 dep).map (lvlVal dep η) ++ ws0.map some))
                          σc := hE.move (by omega) (by omega) hlv
                      have hfn : EntOk D f' (dep + as.length)
                          (bindEnv (revRange (dep + as.length)) ((lvlRange 0 dep).map (lvlVal dep η) ++ ws0.map some))
                          ((Term.fix (.lam (.lam (.lam body))) i0).substitute σc)
                          (.fn s!"{pfx}.f{kk}" (lvlRange 0 dep) sa res) := by
                        refine ⟨fun ℓ hℓ => by have := mem_lvlRange.1 hℓ; omega, fun f'' hf'' => ?_⟩
                        have : (lvlRange 0 dep).map (lvlVal (dep + as.length) (bindEnv (revRange (dep + as.length))
                            ((lvlRange 0 dep).map (lvlVal dep η) ++ ws0.map some))) = (lvlRange 0 dep).map (lvlVal dep η) := by
                          apply List.map_congr_left; intro ℓ hℓ; exact hlv ℓ (by have := mem_lvlRange.1 hℓ; omega)
                        rw [this]; exact hlower f'' hf'' (by omega)
                      have hval : EntOk D f' (dep + as.length)
                          (bindEnv (revRange (dep + as.length)) ((lvlRange 0 dep).map (lvlVal dep η) ++ ws0.map some))
                          a0 (.val sa (lvlRange dep as.length)) := by
                        refine ⟨fun ℓ hℓ => by have := mem_lvlRange.1 hℓ; omega, ws0, ?_, hda⟩
                        refine lvlRange_map_eq _ dep as.length _ hws0 (fun i hi => ?_)
                        rw [lvlVal_bindEnv _ _ hvl _ (by omega), getD_app, if_neg (by simp [lvlRange_length])]
                        simp [lvlRange_length]
                      have hE' := ((hbase.consEnt hfn).consEnt (t := i0.substitute σc) (e := .none) trivial).consEnt hval
                      obtain ⟨w', hw', dS⟩ := sb _ _ hE' [w0] (.cons hev .nil)
                      simp only [List.cons.injEq, and_true] at hw'
                      subst hw'
                      exact dS.steps (steps_fix body i0 a0 σc)
                    have hfunAll : ∀ f₀ f', f' ≤ f₀ → f' < fuel →
                        FunOk D f' s!"{pfx}.f{kk}" ((lvlRange 0 dep).map (lvlVal dep η)) sa res
                          ((Term.fix (.lam (.lam (.lam body))) i0).substitute σc) := by
                      intro f₀
                      induction f₀ with
                      | zero => intro f' hf' hlt; exact key f' (fun f'' h _ => absurd h (by omega)) hlt
                      | succ f₀ ihf => intro f' hf' hlt; exact key f' (fun f'' h h2 => ihf f'' (by omega) h2) hlt
                    obtain ⟨w, rfl, hw⟩ := fa2_single hws
                    obtain ⟨xs, hxs, hcall⟩ := evalE_letChain D fuel η as _ w hw
                    have da := sa' η σc hE xs hxs
                    cases fuel with
                    | zero => simp [evalE] at hcall
                    | succ f =>
                      simp only [evalE, hfd] at hcall
                      split at hcall
                      · have hlen : (xs.map some).length = as.length := by simp [fa2_length hxs]
                        rw [bindEnv_revRange, ← hlen, restrict_push_eq, hlen] at hcall
                        have := hfunAll f f (Nat.le_refl _) (Nat.lt_succ_self _) (a.substitute σc) xs _ w da hfd hcall
                        exact ⟨w, rfl, by simpa only [Term.substitute] using this⟩
                      · exact absurd hcall (by simp)
                  · exact absurd h8 Tr.fail_ok'
            | _ => unfold toS at h; exact absurd h Tr.fail_ok'
          | _ => unfold toS at h; exact absurd h Tr.fail_ok'
        | _ => unfold toS at h; exact absurd h Tr.fail_ok'
      | _ => unfold toS at h; exact absurd h Tr.fail_ok'
    | record fs =>
      unfold toS at h
      cases σ with
      | sum _ => exact absurd h Tr.fail_ok'
      | val v =>
      cases v with
      | sc _ => exact absurd h Tr.fail_ok'
      | rcd sfs =>
        dsimp only at h
        by_cases hnd : (sfs.map (·.1)).Nodup
        · rw [if_pos hnd] at h
          simp only [Term.record.sizeOf_spec] at ht
          have IHfs : ∀ p ∈ fs, ∀ (σ : HSort) (k : Nat) (slots : List FExp) (ds : List FDef) (k' : Nat),
              toS pfx Γ dep p.2 σ k = .ok (slots, ds, k') → DefsIn D ds → SoundAt D fuel Γ dep p.2 σ slots :=
            fun p hp σ' k₁ s₁ d₁ k₂ h' hd' => IH p.2 (by have := sizeOf_snd_lt_of_mem hp; omega) Γ dep σ' k₁ s₁ d₁ k₂ h' hd'
          obtain ⟨hnm, hlen, hf⟩ := toFields_sound pfx D fuel Γ dep fs sfs k slots ds k' IHfs h hD
          intro η σc hE ws hws
          have hwl : ws.length = sfs.length := by rw [← fa2_length hws, hlen]
          refine ⟨fs.map fun f => (f.1, f.2.substitute σc), by simp only [Term.substitute]; exact .refl _, hwl,
            fun j name s w hq hw => ?_⟩
          have hj : j < fs.length := by
            have := congrArg List.length hnm; simp at this
            have := (List.getElem?_eq_some_iff.1 hq).1; omega
          obtain ⟨p, hp⟩ : ∃ p, fs[j]? = some p := ⟨fs[j], List.getElem?_eq_getElem hj⟩
          have hpn : p.1 = name := by
            have := congrArg (·[j]?) hnm
            simp only [List.getElem?_map, hp, hq, Option.map_some, Option.some.injEq] at this
            exact this
          refine ⟨p.2.substitute σc, ?_, hf η σc hE ws hws j p (name, s) w hp hq hw⟩
          apply find?_nodup_get (j := j)
          · rw [List.map_map]; simp only [Function.comp_def]; rw [show (fs.map fun x => x.1) = sfs.map (·.1) from hnm]
            exact hnd
          · simp [hp, ← hpn]
        · rw [if_neg hnd] at h; exact absurd h Tr.fail_ok'
    | get t n =>
      unfold toS at h
      obtain ⟨st, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
      obtain ⟨hst, rfl⟩ := Tr.ofExcept_ok h1
      cases st with
      | sum _ => exact absurd h2 Tr.fail_ok'
      | val v =>
      cases v with
      | sc _ => exact absurd h2 Tr.fail_ok'
      | rcd sfs =>
        simp only at h2
        cases hi : armIdx sfs n with
        | none => simp only [hi] at h2; exact absurd h2 Tr.fail_ok'
        | some q =>
          obtain ⟨j, s⟩ := q
          simp only [hi] at h2
          split at h2
          · rename_i hc
            obtain ⟨rfl, hnd⟩ := hc
            obtain ⟨ts, ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
            split at h4
            · rename_i hj
              obtain ⟨rfl, -, -⟩ := Tr.pure_ok h4
              simp only [Term.get.sizeOf_spec] at ht
              have st' := IH t (by omega) Γ dep _ k1 ts ds3 k2 h3 (DefsIn.append (by simpa using hD)).1
              intro η σc hE ws hws
              obtain ⟨w, rfl, hw⟩ := fa2_single hws
              obtain ⟨xs, hxs, hv⟩ := evalE_letChain D fuel η ts _ w hw
              have hxl := fa2_length hxs
              obtain ⟨flds, hsteps, hlen, hfield⟩ := st' η σc hE xs hxs
              have hjx : j < xs.length := by omega
              -- the selected slot is the variable that holds field `j`
              simp only [evalE, pushAll_get, List.length_map] at hv
              rw [if_pos (by omega), show xs.length - 1 - (ts.length - 1 - j) = j by omega] at hv
              simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjx,
                Option.map_some, Option.getD_some, Option.bind_some] at hv
              obtain ⟨rfl, -⟩ := ck_some hv
              obtain ⟨hq, -⟩ := armIdx_spec hi
              obtain ⟨body, hfind, dS⟩ := hfield j n s _ hq (List.getElem?_eq_getElem hjx)
              refine ⟨_, rfl, DecS.steps ?_ dS⟩
              simp only [Term.substitute]
              exact steps_trans (steps_get n hsteps) (steps_one (.field _ _ _ hfind))
            · exact absurd h4 Tr.fail_ok'
          · exact absurd h2 Tr.fail_ok'
    | inject l p =>
      unfold toS at h
      cases σ with
      | val _ => exact absurd h Tr.fail_ok'
      | sum arms =>
        dsimp only at h
        by_cases hnd : (arms.map (·.1)).Nodup
        · rw [if_pos hnd] at h
          cases hi : armIdx arms l with
          | none => simp only [hi] at h; exact absurd h Tr.fail_ok'
          | some q =>
            obtain ⟨j, v⟩ := q
            simp only [hi] at h
            obtain ⟨ps, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
            obtain ⟨rfl, -, -⟩ := Tr.pure_ok h2
            simp only [Term.inject.sizeOf_spec] at ht
            have sp := IH p (by omega) Γ dep _ k ps ds1 k1 h1 hD.append.1
            obtain ⟨hq, -⟩ := armIdx_spec hi
            intro η σc hE ws hws
            cases hws with
            | cons hh ht' =>
              obtain ⟨wp, wz, rfl, hwp, hwz⟩ := fa2_append ht'
              simp only [evalE] at hh
              obtain ⟨rfl, -⟩ := ck_some hh
              have dp : DecV v wp (p.substitute σc) := sp η σc hE wp hwp
              have hwl := DecV.length dp
              have hpl := fa2_length hwp
              have hzl := fa2_length hwz
              simp only [List.length_replicate] at hzl
              have hmax := maxW_ge hq
              refine ⟨j, wp ++ wz, l, v, p.substitute σc, rfl, by simp; omega, hq,
                by simp only [Term.substitute]; exact .refl _, ?_⟩
              rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
              exact dp
        · rw [if_neg hnd] at h; exact absurd h Tr.fail_ok'
    | case sc arms =>
      unfold toS at h
      by_cases hw0 : σ.width = 0
      · rw [if_pos hw0] at h; exact absurd h Tr.fail_ok'
      rw [if_neg hw0] at h
      obtain ⟨ss, ds1, k1, ds2, h1, h2, rfl⟩ := Tr.bind_ok h
      obtain ⟨-, rfl⟩ := Tr.ofExcept_ok h1
      cases ss with
      | val _ => exact absurd h2 Tr.fail_ok'
      | sum sarms =>
        dsimp only at h2
        by_cases hc : (sarms.map (·.1)).Nodup ∧ sarms ≠ []
        · rw [if_pos hc] at h2
          obtain ⟨fsc, ds3, k2, ds4, h3, h4, rfl⟩ := Tr.bind_ok h2
          obtain ⟨tr, ds5, k3, ds6, h5, h6, rfl⟩ := Tr.bind_ok h4
          cases hm : sarms.mapM (fun lv => tr.lookup lv.1) with
          | none => simp only [hm] at h6; exact absurd h6 Tr.fail_ok'
          | some perArm =>
            simp only [hm] at h6
            by_cases hc2 : perArm.all (·.length = σ.width) ∧ fsc.length = 1 + maxW sarms
            · rw [if_pos hc2] at h6
              obtain ⟨sw, ds7, k4, ds8, h7, h8, rfl⟩ := Tr.bind_ok h6
              obtain ⟨rfl, -, -⟩ := Tr.pure_ok h8
              obtain ⟨-, hD2⟩ := hD.append
              obtain ⟨hD3, hD4⟩ := hD2.append
              obtain ⟨hD5, hD6⟩ := hD4.append
              obtain ⟨hD7, -⟩ := hD6.append
              simp only [Term.case.sizeOf_spec] at ht
              have ssc := IH sc (by omega) Γ dep _ k1 fsc ds3 k2 h3 hD3
              have IHarms : ∀ p ∈ arms, ∀ (Γ' : List CEnt) (dep' : Nat) (σ' : HSort) (k : Nat) (slots : List FExp)
                  (ds : List FDef) (k' : Nat), toS pfx Γ' dep' p.2 σ' k = .ok (slots, ds, k') → DefsIn D ds →
                  SoundAt D fuel Γ' dep' p.2 σ' slots :=
                fun p hp Γ' dep' σ' k₁ s₁ d₁ k₂ h' hd' =>
                  IH p.2 (by have := sizeOf_snd_lt_of_mem hp; omega) Γ' dep' σ' k₁ s₁ d₁ k₂ h' hd'
              have hall : ∀ a ∈ perArm, a.length = σ.width := by
                intro a ha; have := List.all_eq_true.1 hc2.1 a ha; simpa using this
              intro η σc hE ws hws
              have hswl := swChains_length pfx σ.width perArm _ _ k3 sw ds7 k4 hall h7
              obtain ⟨s0, sw', rfl⟩ : ∃ s0 sw', sw = s0 :: sw' := by
                cases sw with
                | nil => simp at hswl; exact absurd hswl.symm hw0
                | cons s0 sw' => exact ⟨s0, sw', rfl⟩
              cases hws with
              | cons hh ht' =>
                obtain ⟨xs, hxs, -⟩ := evalE_letChain D fuel η fsc s0 _ hh
                have hall' := letChain_all D fuel η fsc xs hxs (s0 :: sw') _ (.cons hh ht')
                have hxl := fa2_length hxs
                obtain ⟨t0, rest, l, v, p, hxeq, hrest, hsa, hsteps, dpay⟩ := ssc η σc hE xs hxs
                subst hxeq
                have ht0M : t0 < u24Mod := by
                  cases hxs with | cons hh0 _ => exact evalE_lt D fuel _ η t0 hh0
                have hscr : evalE D fuel (pushAll ((t0 :: rest).map some) η) (.var (fsc.length - 1)) = some t0 := by
                  simp only [evalE, pushAll_get, List.length_map]
                  rw [if_pos (by simp at hxl ⊢; omega), show (t0 :: rest).length - 1 - (fsc.length - 1) = 0 by
                    simp at hxl ⊢; omega]
                  simp [ck_of_lt ht0M]
                have ht0 : t0 < perArm.length := by
                  rw [mapM_length _ hm]; exact (List.getElem?_eq_some_iff.1 hsa).1
                obtain ⟨-, a, E', ha, hfa, hE'⟩ := swChains_eval pfx D fuel σ.width hw0 perArm (dep + fsc.length)
                  _ k3 _ _ k4 _ _ t0 hall h7 hall' (fun _ => hscr) ht0
                obtain ⟨e, he, hpa⟩ := mapM_get _ hm t0 (l, v) hsa
                rw [ha] at hpa; cases hpa
                obtain ⟨body, kk, v', hfind, hidx, hsound⟩ := toArms_sound pfx D fuel Γ (dep + 1) (dep + fsc.length)
                  sarms σ arms k2 tr ds5 k3 IHarms h5 hD5 l a he
                have hkk := armIdx_of_get hc.1 hsa
                rw [hidx] at hkk
                simp only [Option.some.injEq, Prod.mk.injEq] at hkk
                obtain ⟨rfl, rfl⟩ := hkk
                have hlen : ((kk :: rest).map some).length = fsc.length := by simp [hxl]
                have hvw := maxW_ge hsa
                have hagree : ∀ ℓ < dep + fsc.length, lvlVal (dep + fsc.length + kk) E' ℓ =
                    lvlVal (dep + fsc.length) (pushAll ((kk :: rest).map some) η) ℓ := by
                  intro ℓ hℓ
                  simp only [lvlVal]
                  rw [show dep + fsc.length + kk - 1 - ℓ = (dep + fsc.length - 1 - ℓ) + kk by omega]
                  exact hE' _ (by omega)
                have hbase : EnvOk D fuel Γ (dep + fsc.length + kk) E' σc :=
                  ((hlen ▸ hE.push ((kk :: rest).map some)) : EnvOk D fuel Γ (dep + fsc.length) _ σc).move
                    (Nat.le_refl _) (by omega) (fun ℓ hℓ => by rw [hagree ℓ (by omega)])
                have hval : EntOk D fuel (dep + fsc.length + kk) E' p
                    (.val (.val v') (lvlRange (dep + 1) v'.width)) := by
                  refine ⟨fun ℓ hℓ => by have := mem_lvlRange.1 hℓ; simp at hxl; omega, rest.take v'.width, ?_, dpay⟩
                  refine lvlRange_map_eq _ (dep + 1) v'.width _ (by simp; omega) (fun i hi => ?_)
                  rw [hagree _ (by simp at hxl; omega)]
                  have := lvlVal_push_new ((kk :: rest).map some) η dep (i + 1) (by simp; omega)
                  rw [hlen, show dep + (i + 1) = dep + 1 + i by omega] at this
                  rw [this]
                  simp [List.getD_eq_getElem?_getD, hi]
                have db := hsound E' (cons p σc) (hbase.consEnt hval) _ hfa
                simp only [Term.substitute]
                have hf' : (arms.map fun field => (field.1, field.2.substitute (liftSubstitution σc))).find?
                    (fun arm => arm.1 == l) = some (l, body.substitute (liftSubstitution σc)) := by
                  rw [find?_map_snd, hfind]; rfl
                refine DecH.steps (steps_trans (steps_case _ hsteps)
                  (steps_one (.caseInject l p _ (body.substitute (liftSubstitution σc)) hf'))) ?_
                rw [inst_lift]; exact db
            · rw [if_neg hc2] at h6; exact absurd h6 Tr.fail_ok'
        · rw [if_neg hc] at h2; exact absurd h2 Tr.fail_ok'
    | _ => unfold toS at h; exact absurd h Tr.fail_ok'

/-- **The translation is sound, at every fuel.** -/
theorem trSound (pfx : String) (D : List FDef) : ∀ fuel, TrSound pfx D fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro t Γ dep σ k slots ds k' h hD
    exact toS_sound_aux pfx D fuel ih (sizeOf t + 1) t (Nat.lt_succ_self _) Γ dep σ k slots ds k' h hD

/-! ## 8. What a result shows: probes -/

/-- One observation step: apply to an argument, select a field, read a sum's tag (as a label), take
its payload, or a field of its payload. -/
inductive PStep where
  | unit
  | arg (x : Nat)
  | get (n : String)
  | tag (labels : List String)
  | pay (l : String)
  | payGet (l n : String)
  deriving DecidableEq, Repr

def PStep.apply : PStep → Term → Term
  | .unit, h => .app h (.record [])
  | .arg x, h => .app h (.nat x)
  | .get n, h => .get h n
  | .tag ls, h => .case h (ls.map fun l => (l, .label l))
  | .pay l, h => .case h [(l, .bound 0)]
  | .payGet l n, h => .case h [(l, .get (.bound 0) n)]

def applyPath : List PStep → Term → Term
  | [], t => t
  | s :: P, t => applyPath P (s.apply t)

/-- **The observations a slot vector stands for**, each a probe and the ground observation its run
completes with: the scalar itself; each field of a record; a sum's tag (the label) and its payload's
scalar or fields. -/
def HSort.observe : HSort → List Nat → List (List PStep × Observation)
  | .val (.sc s), [w] => [([], s.observe w)]
  | .val (.rcd fs), ws => (fs.zip ws).map fun p => ([.get p.1.1], p.1.2.observe p.2)
  | .sum arms, tag :: rest => match arms[tag]? with
    | some (l, .sc s) => [([.tag (arms.map (·.1))], .label l), ([.pay l], s.observe (rest.headD 0))]
    | some (l, .rcd fs) => ([.tag (arms.map (·.1))], .label l) ::
        (fs.zip rest).map fun p => ([.payGet l p.1.1], p.1.2.observe p.2)
    | none => []
  | _, _ => []

theorem halts_of_steps {t v : Term} (h : Obend.Core.Term.Steps t v) (hv : Value v) {o : Observation}
    (ho : Observes v o) : Halts t o := ⟨v, ⟨h, hv⟩, ho⟩

theorem find?_tag (l : String) : ∀ (ls : List String), l ∈ ls →
    (ls.map fun l => (l, Term.label l)).find? (fun arm => arm.1 == l) = some (l, .label l)
  | m :: ls, h => by
    by_cases hm : m = l
    · subst hm; simp
    · have : l ∈ ls := by simp only [List.mem_cons] at h; exact h.resolve_left (Ne.symm hm)
      simp [hm, find?_tag l ls this]

theorem DecS.halts {s : Scalar} {w : Nat} {t : Term} (d : DecS s w t) : Halts t (s.observe w) :=
  halts_of_steps d.1 (s.lit_value w) (s.observes w)

theorem decRcd_probe {fs : List (String × Scalar)} {ws : List Nat} {t : Term} (d : DecV (.rcd fs) ws t) :
    ∀ p ∈ (fs.zip ws), Halts (.get t p.1.1) (p.1.2.observe p.2) := by
  obtain ⟨flds, hs, hl, hf⟩ := d
  intro p hp
  obtain ⟨j, hj'⟩ := List.mem_iff_getElem?.1 hp
  rw [List.getElem?_zip_eq_some] at hj'
  obtain ⟨hfj, hwj⟩ := hj'
  obtain ⟨body, hfind, dS⟩ := hf j p.1.1 p.1.2 p.2 (by simpa using hfj) hwj
  exact (dS.steps (steps_trans (steps_get _ hs) (steps_one (.field _ _ _ hfind)))).halts

/-- **A slot vector's observations hold**: each probe's run completes with its observation. -/
theorem DecH.probes {σ : HSort} {ws : List Nat} {t : Term} (d : DecH σ ws t) :
    ∀ po ∈ σ.observe ws, Halts (applyPath po.1 t) po.2 := by
  cases σ with
  | val v =>
    cases v with
    | sc s =>
      obtain ⟨w, rfl, dS⟩ := d
      intro po hpo; simp [HSort.observe] at hpo; subst hpo; exact dS.halts
    | rcd fs =>
      intro po hpo
      simp only [HSort.observe, List.mem_map] at hpo
      obtain ⟨p, hp, rfl⟩ := hpo
      exact decRcd_probe d p hp
  | sum arms =>
    obtain ⟨tag, rest, l, v, p, rfl, hrest, ha, hs, dp⟩ := d
    have htag : Halts (applyPath [.tag (arms.map (·.1))] t) (.label l) := by
      simp only [applyPath, PStep.apply]
      have hl : l ∈ arms.map (·.1) := List.mem_map.2 ⟨(l, v), List.mem_of_getElem? ha, rfl⟩
      have hst := steps_trans (steps_case _ hs) (steps_one (.caseInject l p _ _ (find?_tag l _ hl)))
      rw [show instantiate (Term.label l) p = .label l by simp [instantiate, Term.substitute]] at hst
      exact halts_of_steps hst (.label l) (.label l)
    intro po hpo
    simp only [HSort.observe, ha] at hpo
    cases v with
    | sc s =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpo
      rcases hpo with rfl | rfl
      · exact htag
      · obtain ⟨w, hw, dS⟩ := dp
        have : rest.headD 0 = w := by
          cases rest with
          | nil => simp [VSort.width] at hw
          | cons r rs => simp [VSort.width] at hw; simp [hw]
        simp only [applyPath, PStep.apply, this]
        have hst := steps_trans (steps_case _ hs) (steps_one (.caseInject l p [(l, .bound 0)] (.bound 0) (by simp)))
        rw [show instantiate (Term.bound 0) p = p by simp [instantiate, Term.substitute]] at hst
        exact (dS.steps hst).halts
    | rcd fs =>
      simp only [List.mem_cons, List.mem_map] at hpo
      rcases hpo with rfl | ⟨q, hq, rfl⟩
      · exact htag
      · have hq' : q ∈ fs.zip (rest.take (VSort.rcd fs).width) := by
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hq
          rw [List.getElem?_zip_eq_some] at hj
          have hjl : j < fs.length := (List.getElem?_eq_some_iff.1 hj.1).1
          refine List.mem_iff_getElem?.2 ⟨j, ?_⟩
          rw [List.getElem?_zip_eq_some]
          exact ⟨hj.1, by simp [VSort.width, List.getElem?_take, hjl, hj.2]⟩
        have := decRcd_probe dp q hq'
        simp only [applyPath, PStep.apply]
        obtain ⟨v', hev, hob⟩ := this
        refine ⟨v', ⟨steps_trans (steps_trans (steps_case _ hs) (steps_one (.caseInject l p _ (.get (.bound 0) q.1.1)
          (by simp)))) ?_, hev.2⟩, hob⟩
        simpa [instantiate, Term.substitute] using hev.1

theorem PStep.apply_subst (s : PStep) (h : Term) (σ : Nat → Term) :
    (s.apply h).substitute σ = s.apply (h.substitute σ) := by
  cases s <;> simp [PStep.apply, Term.substitute, liftSubstitution, List.map_map, Function.comp_def]

theorem applyPath_subst : ∀ (P : List PStep) (h : Term) (σ : Nat → Term),
    (applyPath P h).substitute σ = applyPath P (h.substitute σ)
  | [], _, _ => rfl
  | s :: P, h, σ => by simp only [applyPath, applyPath_subst P, PStep.apply_subst]

theorem applyPath_inst (P : List PStep) (t : Term) : instantiate (applyPath P (.bound 0)) t = applyPath P t := by
  simp only [instantiate, applyPath_subst, Term.substitute]

theorem steps_applyPath : ∀ (P : List PStep) {t t' : Term}, Obend.Core.Term.Steps t t' →
    Obend.Core.Term.Steps (applyPath P t) (applyPath P t')
  | [], _, _, h => h
  | s :: P, t, t', h => by
    apply steps_applyPath P
    cases s with
    | unit => exact steps_app _ h
    | arg x => exact steps_app _ h
    | get n => exact steps_get n h
    | tag ls => exact steps_case _ h
    | pay l => exact steps_case _ h
    | payGet l n => exact steps_case _ h

theorem halts_prefix {P : List PStep} {t t' : Term} {o : Observation} (h : Obend.Core.Term.Steps t t')
    (ho : Halts (applyPath P t') o) : Halts (applyPath P t) o := by
  obtain ⟨v, ⟨hs, hv⟩, hob⟩ := ho
  exact ⟨v, ⟨steps_trans (steps_applyPath P h) hs, hv⟩, hob⟩

theorem halts_bequiv {P : List PStep} {t u : Term} {o : Observation} (h : t ≈b u)
    (ho : Halts (applyPath P t) o) : Halts (applyPath P u) o := by
  have := (h Term.bound (applyPath P (.bound 0))).halts o
  rw [substitute_bound, substitute_bound, applyPath_inst, applyPath_inst] at this
  exact this.1 ho

/-! ## 9. The book, and `lowerBookToHvm_sound` -/

/-- The definitions an expression's lifted switches need. -/
def liftedDefs : FExp → List HDef
  | .op _ a b | .let_ a b => liftedDefs a ++ liftedDefs b
  | .ifz v z s => liftedDefs v ++ liftedDefs z ++ liftedDefs s
  | .ifzL d nz ns v z s => defNet nz (revRange d) [z] :: defNet ns (0 :: (revRange d).map (· + 1)) [s] ::
      (liftedDefs v ++ liftedDefs z ++ liftedDefs s)
  | _ => []

def defOkB (ps : List Nat) (fs : List FExp) : Bool :=
  !ps.isEmpty && decide ps.Nodup && (compAll fs 0 fs.length).occ.all (fun p => decide (p.1 ∈ ps))

theorem defOk_of (ps : List Nat) (fs : List FExp) (h : defOkB ps fs = true) : DefOk ps fs := by
  simp only [defOkB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq,
    List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Every lifted switch's two definitions are well formed. -/
def liftOkB : FExp → Bool
  | .op _ a b | .let_ a b => liftOkB a && liftOkB b
  | .ifz v z s => liftOkB v && liftOkB z && liftOkB s
  | .ifzL d _ _ v z s => defOkB (revRange d) [z] && defOkB (0 :: (revRange d).map (· + 1)) [s] &&
      liftOkB v && liftOkB z && liftOkB s
  | _ => true

theorem find?_of_mem_nodup {l : List HDef} {d : HDef} (hnd : (l.map (·.name)).Nodup) (hd : d ∈ l) :
    l.find? (·.name == d.name) = some d := by
  induction l with
  | nil => cases hd
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.1 hd with rfl | hd
    · simp
    · have : (x.name == d.name) = false := by
        simp only [beq_eq_false_iff_ne]; intro e; exact hnd.1 ⟨d, hd, e.symm⟩
      simp [this, ih hnd.2 hd]

theorem good_of (book : List HDef) (hnd : (book.map (·.name)).Nodup) :
    ∀ e : FExp, liftOkB e = true → (∀ x ∈ liftedDefs e, x ∈ book) → Good book e
  | .lit _, _, _ => trivial
  | .var _, _, _ => trivial
  | .call _ _, _, _ => trivial
  | .op _ a b, h, hm => by
    simp only [liftOkB, Bool.and_eq_true] at h
    exact ⟨good_of book hnd a h.1 (fun x hx => hm x (by simp [liftedDefs, hx])),
      good_of book hnd b h.2 (fun x hx => hm x (by simp [liftedDefs, hx]))⟩
  | .let_ a b, h, hm => by
    simp only [liftOkB, Bool.and_eq_true] at h
    exact ⟨good_of book hnd a h.1 (fun x hx => hm x (by simp [liftedDefs, hx])),
      good_of book hnd b h.2 (fun x hx => hm x (by simp [liftedDefs, hx]))⟩
  | .ifz v z s, h, hm => by
    simp only [liftOkB, Bool.and_eq_true] at h
    exact ⟨good_of book hnd v h.1.1 (fun x hx => hm x (by simp [liftedDefs, hx])),
      good_of book hnd z h.1.2 (fun x hx => hm x (by simp [liftedDefs, hx])),
      good_of book hnd s h.2 (fun x hx => hm x (by simp [liftedDefs, hx]))⟩
  | .ifzL d nz ns v z s, h, hm => by
    simp only [liftOkB, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hz, hs⟩, hv⟩, hz'⟩, hs'⟩ := h
    refine ⟨good_of book hnd v hv (fun x hx => hm x (by simp [liftedDefs, hx])),
      good_of book hnd z hz' (fun x hx => hm x (by simp [liftedDefs, hx])),
      good_of book hnd s hs' (fun x hx => hm x (by simp [liftedDefs, hx])),
      ?_, defOk_of _ _ hz, ?_, defOk_of _ _ hs⟩
    · exact find?_of_mem_nodup (d := defNet nz (revRange d) [z]) hnd (hm _ (by simp [liftedDefs]))
    · exact find?_of_mem_nodup (d := defNet ns (0 :: (revRange d).map (· + 1)) [s]) hnd (hm _ (by simp [liftedDefs]))

/-- A lowered member: its name, its arity (the curried arguments after `self`), the sort of its
result, its result's slots, and its HVM2 net. -/
structure HvmMember where
  member : String
  arity : Nat
  sort : HSort
  slots : List FExp
  hdef : HDef

/-- HVM2's names are letters, digits and the characters `_`, `.`, `-` and `/`; the lowering keeps
member names as they are, so it takes those of letters, digits and `_`, and leaves `main` to the entry
point. Its own definitions are named after the member with a `.`, so they meet no member. -/
def nameOk (m : String) : Bool := !m.isEmpty && m != "main" && m.all (fun c => c.isAlphanum || c == '_')

/-- The leading λ-abstractions. -/
def peelLams : Term → Nat × Term
  | .lam b => ((peelLams b).1 + 1, (peelLams b).2)
  | t => (0, t)

theorem peelLams_spec : ∀ t : Term, lams (peelLams t).1 (peelLams t).2 = t
  | .lam b => by simp only [peelLams, lams]; rw [peelLams_spec b]
  | .hole .. | .bound _ | .app .. | .mix .. | .fix .. | .specification .. | .prototype .. | .reflect _
  | .metadata _ | .project _ | .nat _ | .boolean _ | .label _ | .binary .. | .extend .. | .record _
  | .get .. | .ifZero .. | .inject .. | .case .. | .ifBool .. | .perform _ | .done _ | .split .. => rfl

/-- The environment of a member's body: its `k` natural arguments (the last at index 0), then `self`,
which nothing may read. -/
def natEnv : Nat → List CEnt
  | 0 => []
  | k + 1 => .val (.val (.sc .nat)) [k] :: natEnv k

def memberEnv (k : Nat) : List CEnt := natEnv k ++ [.none]

/-- **The lowering of a member**: the code `evalBookAt` folds, `dataPinSpecialize (evalBook B m)`,
as `λself. λx₁ … λxₖ. body`, `body` translated at the sort `sortOf` gives it; the refusal by name
otherwise. With it, the fixpoint definitions the translation emitted. -/
def lowerMember (B : Book) (m : String) : Except String (HvmMember × List FDef) :=
  if nameOk m then
    match evalBook B m with
    | none => .error s!"{m}: no such member"
    | some c => match dataPinSpecialize c with
      | .lam code =>
        if (peelLams code).1 = 0 then .error s!"{m}: not a method (`λself. body` with no argument)" else
        match sortOf (memberEnv (peelLams code).1) (peelLams code).2 with
        | .error e => .error s!"{m}: {e}"
        | .ok σ => match toS m (memberEnv (peelLams code).1) (peelLams code).1 (peelLams code).2 σ 0 with
          | .ok (slots, ds, _) => if slots = [] then .error s!"{m}: a result of no slots" else
              .ok (⟨m, (peelLams code).1, σ, slots, defNet m (revRange (peelLams code).1) slots⟩, ds)
          | .error e => .error s!"{m}: {e}"
      | _ => .error s!"{m}: the folded code is not `λself. …` (a static member)"
  else .error s!"{m}: a member name outside [A-Za-z0-9_], or `main`"

def lowerAll (B : Book) : List String → Except String (List HvmMember × List FDef)
  | [] => .ok ([], [])
  | m :: ms => match lowerMember B m, lowerAll B ms with
    | .ok (d, ds), .ok (rs, dss) => .ok (d :: rs, ds ++ dss)
    | .error e, _ => .error e
    | _, .error e => .error e

/-- An HVM2 book lowered from a Leaf book: one net per slot, the fixpoint definitions, and the
lifted branches. -/
structure HvmBook where
  members : List HvmMember
  fdefs : List FDef

def HvmBook.exprs (H : HvmBook) : List FExp := H.members.flatMap (·.slots) ++ H.fdefs.map (·.body)

def HvmBook.defs (H : HvmBook) : List HDef :=
  H.members.map (·.hdef) ++ H.fdefs.map (fun d => defNet d.name d.params [d.body]) ++ H.exprs.flatMap liftedDefs

def HvmBook.member? (H : HvmBook) (m : String) : Option HvmMember := H.members.find? (·.member == m)

/-- The book's own checks: names unique, every lifted switch and definition well formed, every
inline switch's branches call-free. -/
def HvmBook.checkB (H : HvmBook) : Bool :=
  decide ((H.defs.map (·.name)).Nodup) && H.exprs.all (fun e => liftOkB e && wellLifted e) &&
    H.fdefs.all (fun d => defOkB d.params [d.body]) && H.members.all (fun d => defOkB (revRange d.arity) d.slots)

/-- The lowering of a book, with the first refusal by name. -/
def lowerBookToHvmE (B : Book) : Except String HvmBook :=
  match lowerAll B B.slots with
  | .ok (ms, ds) => if (HvmBook.mk ms ds).checkB then .ok ⟨ms, ds⟩ else .error "the lowered book failed its own checks"
  | .error e => .error e

/-- **The lowering of a book**: every slot lowered, or `none`. -/
def lowerBookToHvm (B : Book) : Option HvmBook :=
  match lowerBookToHvmE B with
  | .ok H => some H
  | .error _ => none

/-- `@main = r & @m ~ (#x₁ (… (#xₖ r)))`. -/
def mainDef (d : HvmMember) (xs : List Nat) : HDef :=
  ⟨"main", .var 0, [(.ref d.member, argTree (xs.map fun x => nul (some x)) (.var 0))]⟩

/-- The file `hvm run` reads for member `d` at arguments `xs`. -/
def emitMain (H : HvmBook) (d : HvmMember) (xs : List Nat) (p : Plant := .none) : String :=
  emitHvmWith p (mainDef d xs :: H.defs)

theorem lowerMember_ok {B : Book} {m : String} {d : HvmMember} {ds : List FDef} (h : lowerMember B m = .ok (d, ds)) :
    d.member = m ∧ d.arity ≠ 0 ∧ d.hdef = defNet m (revRange d.arity) d.slots ∧ d.slots ≠ [] ∧
    ∃ c code k', evalBook B m = some c ∧ dataPinSpecialize c = .lam code ∧ (peelLams code).1 = d.arity ∧
      toS m (memberEnv d.arity) d.arity (peelLams code).2 d.sort 0 = .ok (d.slots, ds, k') := by
  unfold lowerMember at h
  split at h
  · split at h
    · cases h
    · rename_i c hc
      split at h
      · rename_i code hcode
        split at h
        · cases h
        · rename_i hk
          split at h
          · cases h
          · rename_i σ hσ
            split at h
            · rename_i slots ds' k' hs
              split at h
              · cases h
              · rename_i hne
                cases h
                exact ⟨rfl, hk, rfl, hne, c, code, k', hc, hcode, rfl, hs⟩
            · cases h
      · cases h
  · cases h

theorem lowerAll_ok {B : Book} : ∀ {ms : List String} {rs : List HvmMember} {dss : List FDef},
    lowerAll B ms = .ok (rs, dss) → ∀ d ∈ rs, ∃ ds, lowerMember B d.member = .ok (d, ds) ∧ ∀ x ∈ ds, x ∈ dss
  | [], rs, dss, h, d, hd => by simp only [lowerAll, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1] at hd; cases hd
  | m :: ms, rs, dss, h, d, hd => by
    simp only [lowerAll] at h
    cases h1 : lowerMember B m with
    | error e => simp [h1] at h
    | ok p =>
      obtain ⟨d', ds'⟩ := p
      cases h2 : lowerAll B ms with
      | error e => simp [h1, h2] at h
      | ok q =>
        obtain ⟨rs', dss'⟩ := q
        simp only [h1, h2, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases List.mem_cons.1 hd with rfl | hd
        · rw [(lowerMember_ok h1).1]; exact ⟨ds', h1, fun x hx => List.mem_append_left _ hx⟩
        · obtain ⟨ds, h3, h4⟩ := lowerAll_ok h2 d hd
          exact ⟨ds, h3, fun x hx => List.mem_append_right _ (h4 x hx)⟩

theorem consAll_get : ∀ (as : List Term) (τ : Nat → Term) (i : Nat),
    consAll as τ i = if i < as.length then as.getD (as.length - 1 - i) (.bound 0) else τ (i - as.length)
  | [], τ, i => by simp [consAll]
  | a :: as, τ, i => by
    simp only [consAll, consAll_get as (cons a τ) i, List.length_cons]
    by_cases h : i < as.length
    · rw [if_pos h, if_pos (by omega), show as.length + 1 - 1 - i = (as.length - 1 - i) + 1 by omega]; simp
    · rw [if_neg h]
      by_cases h' : i = as.length
      · subst h'; simp
      · rw [if_neg (by omega)]
        obtain ⟨j, hj⟩ : ∃ j, i - as.length = j + 1 := ⟨i - as.length - 1, by omega⟩
        rw [hj]; simp only [cons_succ]; congr 1; omega

theorem natEnv_length : ∀ k, (natEnv k).length = k
  | 0 => rfl
  | k + 1 => by simp [natEnv, natEnv_length k]

theorem natEnv_get : ∀ (k i : Nat), i < k → (natEnv k)[i]? = some (.val (.val (.sc .nat)) [k - 1 - i])
  | k + 1, 0, _ => by simp [natEnv]
  | k + 1, i + 1, h => by
    simp only [natEnv, List.getElem?_cons_succ]
    rw [natEnv_get k i (by omega)]; congr 3; omega

theorem memberEnv_get (k i : Nat) : (memberEnv k)[i]? =
    if i < k then some (.val (.val (.sc .nat)) [k - 1 - i]) else if i = k then some .none else none := by
  simp only [memberEnv]
  by_cases h : i < k
  · rw [if_pos h, List.getElem?_append_left (by simp [natEnv_length]; omega), natEnv_get k i h]
  · rw [if_neg h, List.getElem?_append_right (by simp [natEnv_length]; omega)]
    simp only [natEnv_length]
    by_cases h' : i = k
    · subst h'; simp
    · rw [if_neg h']; simp; omega

theorem applyAll_nats : ∀ (t : Term) (xs : List Nat), applyAll t (xs.map .nat) = applyPath (xs.map .arg) t
  | _, [] => rfl
  | t, x :: xs => by simp only [List.map_cons, applyAll, applyPath, PStep.apply, applyAll_nats _ xs]

theorem applyPath_append : ∀ (P Q : List PStep) (t : Term), applyPath (P ++ Q) t = applyPath Q (applyPath P t)
  | [], _, _ => rfl
  | s :: P, Q, t => by simp only [List.cons_append, applyPath, applyPath_append P Q]

theorem find?_mem_nodup_fdef {l : List FDef} {d : FDef} (hnd : (l.map (·.name)).Nodup) (hd : d ∈ l) :
    l.find? (·.name == d.name) = some d := by
  induction l with
  | nil => cases hd
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.1 hd with rfl | hd
    · simp
    · have : (x.name == d.name) = false := by
        simp only [beq_eq_false_iff_ne]; intro e; exact hnd.1 ⟨d, hd, e.symm⟩
      simp [this, ih hnd.2 hd]

/-- **`lowerBookToHvm_sound`.** For a book the lowering accepts, a member `m` it lowered to `d` (of
arity `k`, result sort `d.sort`), arguments `x :: rest` (`k` of them), and a fuel at which every
result slot evaluates exactly (`evalE`: every intermediate value the Core4 one, below `2^24`):

1. the model of HVM2 reduces `@main = r & @m ~ (#x (… r))` (`mainCfgOf`), against the lowered book,
   to the normal form whose root is the tuple of the slot values and whose bag is empty;
2. `evalBookAt B m (.nat x)` is a term `r` such that, for every observation `d.sort.observe ws`
   names (the scalar; each record field; a sum's tag as its label, and its payload's scalar or
   fields), the probe applied to `r` after the remaining arguments halts, under Core4's reference
   reduction, with that observation.

So the net's normal form decodes, slot by slot, to what `evalBookAt` evaluates to. -/
theorem lowerBookToHvm_sound {B : Book} {H : HvmBook} (hH : lowerBookToHvm B = some H) {m : String}
    {d : HvmMember} (hd : H.member? m = some d) (x : Nat) (rest : List Nat) (hlen : rest.length + 1 = d.arity)
    (fuel : Nat) (ws : List Nat)
    (hw : Fa2 (fun e w => evalE H.fdefs fuel (bindEnv (revRange d.arity) ((x :: rest).map some)) e = some w)
      d.slots ws) :
    Steps H.defs (mainCfgOf m ((x :: rest).map some)) ⟨tup (ws.map fun w => nul (some w)), []⟩ ∧
    ∃ r, evalBookAt B m (.nat x) = some r ∧
      ∀ po ∈ d.sort.observe ws, Halts (applyPath (rest.map .arg ++ po.1) r) po.2 := by
  unfold lowerBookToHvm at hH
  cases hEx : lowerBookToHvmE B with
  | error e => rw [hEx] at hH; cases hH
  | ok H' =>
    rw [hEx] at hH
    simp only [Option.some.injEq] at hH
    subst hH
    unfold lowerBookToHvmE at hEx
    cases hall : lowerAll B B.slots with
    | error e => rw [hall] at hEx; cases hEx
    | ok p =>
    obtain ⟨ms, dss⟩ := p
    rw [hall] at hEx
    dsimp only at hEx
    by_cases hchk : (HvmBook.mk ms dss).checkB = true
    · rw [if_pos hchk] at hEx
      cases hEx
      simp only [HvmBook.checkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
      obtain ⟨⟨⟨hnd, hex⟩, hfd⟩, hmem⟩ := hchk
      have hdm : d ∈ ms := List.mem_of_find?_eq_some hd
      have hname : d.member = m := by simpa using List.find?_some hd
      obtain ⟨ds, hlow, hsub⟩ := lowerAll_ok hall d hdm
      obtain ⟨-, hk0, hdef, hne, c, code, k', hc, hcode, hk, htoS⟩ := lowerMember_ok hlow
      rw [hname] at hc hdef htoS
      -- the book's facts
      have hfnd : ((dss.map (fun f => defNet f.name f.params [f.body])).map (·.name)).Nodup := by
        have := hnd.sublist ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _) |>.map _)
        simpa [HvmBook.defs, List.map_append] using this
      have hfnd' : (dss.map (·.name)).Nodup := by simpa [List.map_map, Function.comp_def, defNet] using hfnd
      have hinbook : ∀ e ∈ (HvmBook.mk ms dss).exprs, ∀ x ∈ liftedDefs e, x ∈ (HvmBook.mk ms dss).defs :=
        fun e he x hx => List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, hx⟩)
      have hgood : ∀ e ∈ (HvmBook.mk ms dss).exprs, Good (HvmBook.mk ms dss).defs e :=
        fun e he => good_of _ hnd e (hex e he).1 (hinbook e he)
      have hwl : ∀ e ∈ (HvmBook.mk ms dss).exprs, wellLifted e = true :=
        fun e he => (hex e he).2
      have hbookok : BookOk (HvmBook.mk ms dss).defs dss := by
        intro g fd hfind
        have hfm : fd ∈ dss := List.mem_of_find?_eq_some hfind
        have hfn : fd.name = g := by simpa using List.find?_some hfind
        refine ⟨?_, defOk_of _ _ (hfd fd hfm), hgood fd.body (by simp [HvmBook.exprs]; exact .inr ⟨fd, hfm, rfl⟩)⟩
        have := find?_of_mem_nodup (d := defNet fd.name fd.params [fd.body]) hnd
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨fd, hfm, rfl⟩)))
        rw [← hfn]; exact this
      have hwlD : ∀ fd ∈ dss, wellLifted fd.body = true :=
        fun fd hfm => hwl fd.body (by simp [HvmBook.exprs]; exact .inr ⟨fd, hfm, rfl⟩)
      have hslot : ∀ e ∈ d.slots, e ∈ (HvmBook.mk ms dss).exprs :=
        fun e he => by simp [HvmBook.exprs]; exact .inl ⟨d, hdm, he⟩
      refine ⟨?_, ?_⟩
      · -- the net
        have hb : (HvmBook.mk ms dss).defs.find? (·.name == m) = some (defNet m (revRange d.arity) d.slots) := by
          rw [← hdef]
          have := find?_of_mem_nodup (d := d.hdef) hnd (List.mem_append_left _ (List.mem_append_left _
            (List.mem_map.2 ⟨d, hdm, rfl⟩)))
          rwa [hdef] at this ⊢
        have := main_reduces _ m (revRange d.arity) d.slots ((x :: rest).map some) (ws.map some) hb
          (defOk_of _ _ (hmem d hdm)) (by simp [revRange_length, hlen]) (by simp [fa2_length hw])
          (fun i f v hf hv => by
            obtain ⟨w, hwi, rfl⟩ : ∃ w, ws[i]? = some w ∧ v = some w := by
              simp only [List.getElem?_map] at hv
              cases hwi : ws[i]? with
              | none => simp [hwi] at hv
              | some w => simp [hwi] at hv; exact ⟨w, rfl, hv.symm⟩
            have he := fa2_map_of hw i f w hf hwi
            exact comp_reduces _ dss hbookok fuel f _ _ (hgood f (hslot f (List.mem_of_getElem? hf)))
              (evalE_evalF dss hwlD fuel f _ w (hwl f (hslot f (List.mem_of_getElem? hf))) he).1)
        simpa [List.map_map, Function.comp_def] using this
      · -- Core4
        have hDefs : DefsIn dss ds := fun x hx => find?_mem_nodup_fdef hfnd' (hsub x hx)
        have sound := trSound m dss fuel _ (memberEnv d.arity) d.arity d.sort 0 d.slots ds k' htoS hDefs
        have hargl : ((x :: rest).map some).length = d.arity := by simp [hlen]
        have hE : EnvOk dss fuel (memberEnv d.arity) d.arity (bindEnv (revRange d.arity) ((x :: rest).map some))
            (consAll (.record [] :: (x :: rest).map .nat) Term.bound) := by
          intro i e hi
          rw [memberEnv_get] at hi
          split at hi
          · rename_i hik
            simp only [Option.some.injEq] at hi
            subst hi
            have hj : d.arity - 1 - i < (x :: rest).length := by simp; omega
            refine ⟨by simp; omega, [(x :: rest)[d.arity - 1 - i]], ?_, ⟨_, rfl, ?_, trivial⟩⟩
            · have hv := lvlVal_bindEnv d.arity ((x :: rest).map some) hargl (d.arity - 1 - i) (by omega)
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv ⊢
              rw [hv, List.getD_eq_getElem?_getD,
                show some x :: List.map some rest = (x :: rest).map some from rfl, List.getElem?_map,
                List.getElem?_eq_getElem hj]
              rfl
            · rw [consAll_get]
              rw [if_pos (by simp; omega)]
              simp only [List.length_cons, List.length_map]
              rw [show rest.length + 1 + 1 - 1 - i = (d.arity - 1 - i) + 1 by omega]
              simp only [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_map]
              rw [List.getElem?_eq_getElem (by simpa using hj)]
              simp only [Option.map_some, Option.getD_some, Scalar.lit, List.getElem_map, List.getElem_cons_succ]
              exact .refl _
          · split at hi
            · simp only [Option.some.injEq] at hi; subst hi; trivial
            · cases hi
        have dec := sound _ _ hE ws hw
        have hcode' : dataPinSpecialize c = lams ((Term.record [] :: (x :: rest).map Term.nat).length)
            (((peelLams code).2).substitute (liftN ((Term.record [] :: (x :: rest).map Term.nat).length) Term.bound)) := by
          rw [liftN_bound, substitute_bound, hcode]
          simp only [List.length_cons, List.length_map]
          rw [show rest.length + 1 + 1 = (peelLams code).1 + 1 by omega]
          simp only [lams]; rw [peelLams_spec]
        have hrun := steps_lams ((peelLams code).2) (Term.record [] :: (x :: rest).map Term.nat) Term.bound
        rw [← hcode'] at hrun
        refine ⟨dataPinSpecialize (.app (.app c (.record [])) (.nat x)), by simp [evalBookAt, hc], fun po hpo => ?_⟩
        have h1 := halts_prefix (P := po.1) hrun (dec.probes po hpo)
        have e1 : applyAll (dataPinSpecialize c) (Term.record [] :: (x :: rest).map Term.nat) =
            applyPath (rest.map PStep.arg) (applyPath [.unit, .arg x] (dataPinSpecialize c)) := by
          simp only [List.map_cons, applyAll, applyAll_nats]; rfl
        rw [e1, ← applyPath_append, ← applyPath_append] at h1
        have h2 := halts_bequiv (BEquiv.symm (bequiv_dataPinSpecialize c)) h1
        simp only [List.cons_append, applyPath, PStep.apply, List.nil_append] at h2
        exact halts_bequiv (bequiv_dataPinSpecialize _) h2
    · rw [if_neg hchk] at hEx; cases hEx
