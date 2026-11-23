module
/-
# `Obend.Core.CanonicityDefs` — Total Fragment Carriers & Finite Tait–Girard Reducibility Skeletons

Companion carrier & shape-realization module for `Obend.Core.Canonicity`:
- `PositiveBounds` & `IsTotalTerm` (structurally recursive total fragment predicate)
- `natIter` & `CanonicalValue`
- `RedShape`, structurally recursive `RedVal` / `RedExp`, `HasShape`, `redVal_congr`,
  `hasShape_sameType`, and unconditional shape realization `exists_hasShape`.
-/
public import Obend.Core.Check
public import Obend.Core.Invariant
public import Obend.Core.TypeGraphHead
public import Obend.Core.EquiRecursiveLookup
import all Obend.Core.TypeGraph

public section
namespace Obend.Core.Canonicity

open Obend.Core.Ty Obend.Core.Term Obend.Core.Check Obend.Core.AliasExposure
set_option autoImplicit false

/-! ## §1. Decidable `PositiveBounds` & `IsTotalTerm` Predicates -/

/-- Duplicate-free check on `Nat` keys. -/
def nodupNatB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupNatB xs

/-- Check that every type variable referenced in `τ` belongs to `allowed`. -/
def varsInAllowed (allowed : List Nat) : Ty → Bool
  | .natural | .boolean | .label | .emptyRow | .custody _ => true
  | .variable i => allowed.contains i
  | .arrow _ _ d c | .field _ d c | .specification d c | .prototype d c =>
      varsInAllowed allowed d && varsInAllowed allowed c
  | .variant r => varsInAllowed allowed r
  | .computation p r a =>
      varsInAllowed allowed p && varsInAllowed allowed r && varsInAllowed allowed a

/-- Rigid variables that carry no lower-bound entry in `θ.bounds`. -/
def unaliasedRigids (θ : Assumptions) : List Nat :=
  θ.rigid.filter fun r => !(θ.bounds.map Prod.fst).contains r

/-- Topologically acyclic bound table: each bound `(idx, b)` is non-computation and mentions only
unaliased rigids or variables declared strictly later in `bounds`. Blocks negative self-referential
aliases such as `0 ↦ (0 → Nat)` (Curry's paradox without `.fix`). -/
def AcyclicBoundsList (freeRigids : List Nat) : Bounds → Bool
  | [] => true
  | (_, b) :: rest =>
      !b.isComputation &&
      varsInAllowed (freeRigids ++ rest.map Prod.fst) b &&
      AcyclicBoundsList freeRigids rest

/-- Decidable check that `θ` is valid and has strictly acyclic, non-computation bounds. -/
@[expose] def PositiveBounds (θ : Assumptions) : Bool :=
  θ.valid && nodupNatB (θ.bounds.map Prod.fst) && AcyclicBoundsList (unaliasedRigids θ) θ.bounds

mutual
/-- Syntactic predicate for the pure, hole-free, `.fix`-free, `.perform`-free total kernel fragment
(covering 22/25 `Term` constructors), written by structural recursion so WHNF reduces on constructors. -/
@[expose] def IsTotalTerm (t : Term) : Bool :=
  match t with
  | .hole .. | .fix .. | .perform .. => false
  | .bound _ | .nat _ | .boolean _ | .label _ => true
  | .lam b | .reflect b | .metadata b | .project b | .inject _ b | .done b | .get b _ =>
      IsTotalTerm b
  | .app f a | .mix f a | .specification f a | .prototype f a | .binary _ f a | .split f _ a =>
      IsTotalTerm f && IsTotalTerm a
  | .ifBool c tr fl | .ifZero c tr fl =>
      IsTotalTerm c && IsTotalTerm tr && IsTotalTerm fl
  | .record fs => isTotalFields fs
  | .extend tr fs => IsTotalTerm tr && isTotalFields fs
  | .case s arms => IsTotalTerm s && isTotalFields arms
termination_by structural t

@[expose] def isTotalFields (fs : List (String × Term)) : Bool :=
  match fs with
  | [] => true
  | (_, b) :: rest => IsTotalTerm b && isTotalFields rest
termination_by structural fs
end

/-- Bounded structural `Nat` iterator inside `IsTotalTerm`: iterates `stepFn` `n` times from `z`. -/
@[expose] def natIter : Nat → Term → Term → Term
  | 0, z, _ => z
  | n + 1, z, stepFn => .app stepFn (natIter n z stepFn)

theorem natIter_isTotal (n : Nat) {z stepFn : Term}
    (hz : IsTotalTerm z = true) (hs : IsTotalTerm stepFn = true) :
    IsTotalTerm (natIter n z stepFn) = true := by
  induction n with
  | zero => exact hz
  | succ _ ih => simp [natIter, IsTotalTerm, hs, ih]

/-- Canonical closed value shapes classified by `AliasExposure.expose θ τ`. -/
@[expose] def CanonicalValue (θ : Assumptions) (τ : Ty) (v : Term) : Prop :=
  Value v ∧ Obend.Core.Invariant.Scoped 0 v ∧
  match expose θ τ with
  | .constructor ⟨.natural, _⟩ => ∃ n, v = .nat n
  | .constructor ⟨.boolean, _⟩ => ∃ b, v = .boolean b
  | .constructor ⟨.label, _⟩ => ∃ s, v = .label s
  | .constructor ⟨.variant, _⟩ => ∃ tag payload, v = .inject tag payload
  | .constructor ⟨.emptyRow, _⟩ | .constructor ⟨.field _, _⟩ => ∃ fs, v = .record fs
  | .constructor ⟨.arrow _ _, _⟩ => ∃ b, v = .lam b
  | .constructor ⟨.specification, _⟩ => ∃ m e, v = .specification m e
  | .constructor ⟨.prototype, _⟩ => ∃ s t, v = .prototype s t
  | _ => True

/-! ## §2. Finite Type Skeletons (`RedShape`) & Tait–Girard Reducibility -/

/-- Well-founded finite skeleton of an exposed type under `PositiveBounds θ`. -/
inductive RedShape where
  | nat
  | bool
  | label
  | custody (id : Nat)
  | rigid (idx : Nat) (fields : List (String × RedShape)) (isRow : Bool)
  | arrow (reuse : Reuse) (qty : Quantity) (dom cod : RedShape)
  | spec (metaS extS : RedShape)
  | proto (specS targetS : RedShape)
  | row (fields : List (String × RedShape))
  | variant (cases : List (String × RedShape))
  | comp (resS : RedShape)

mutual
/-- Tait–Girard value reducibility predicate, structurally recursive on `S : RedShape`. -/
@[expose] def RedVal (S : RedShape) (v : Term) : Prop :=
  match S with
  | .nat => ∃ n, v = .nat n
  | .bool => ∃ b, v = .boolean b
  | .label => ∃ s, v = .label s
  | .custody _ => Value v ∧ Obend.Core.Invariant.Scoped 0 v
  | .rigid _ fs isR =>
      Value v ∧ Obend.Core.Invariant.Scoped 0 v ∧
      (isR = true → ∃ rfs, v = .record rfs) ∧
      RedRigidFields fs v
  | .arrow _ qty domS codS =>
      ∃ b, v = .lam b ∧ Obend.Core.Invariant.Scoped 1 b ∧
        ∀ a, Obend.Core.Invariant.Scoped 0 a →
          (qty = .erased ∨ ∃ va, Evaluates a va ∧ RedVal domS va) →
          ∃ vr, Evaluates (instantiate b a) vr ∧ RedVal codS vr
  | .spec mS eS =>
      ∃ m e vm ve, v = .specification m e ∧
        Obend.Core.Invariant.Scoped 0 m ∧ Obend.Core.Invariant.Scoped 0 e ∧
        Evaluates m vm ∧ RedVal mS vm ∧ Evaluates e ve ∧ RedVal eS ve
  | .proto sS tS =>
      ∃ s t vs vt, v = .prototype s t ∧
        Obend.Core.Invariant.Scoped 0 s ∧ Obend.Core.Invariant.Scoped 0 t ∧
        Evaluates s vs ∧ RedVal sS vs ∧ Evaluates t vt ∧ RedVal tS vt
  | .row fs =>
      ∃ rfs, v = .record rfs ∧ Obend.Core.Invariant.Scoped 0 v ∧
        RedRowFields fs rfs
  | .variant cs =>
      ∃ tag payload, v = .inject tag payload ∧ Obend.Core.Invariant.Scoped 0 payload ∧
        RedVariantCases cs tag payload
  | .comp resS => RedVal resS v
termination_by structural S

def RedRigidFields (fs : List (String × RedShape)) (v : Term) : Prop :=
  match fs with
  | [] => True
  | (nm, fS) :: rest =>
      (∃ rfs body u, v = .record rfs ∧
        rfs.find? (·.1 == nm) = some (nm, body) ∧ Evaluates body u ∧ RedVal fS u) ∧
      RedRigidFields rest v
termination_by structural fs

def RedRowFields (fs : List (String × RedShape)) (rfs : List (String × Term)) : Prop :=
  match fs with
  | [] => True
  | (nm, fS) :: rest =>
      (∃ body u, rfs.find? (·.1 == nm) = some (nm, body) ∧ Evaluates body u ∧ RedVal fS u) ∧
      RedRowFields rest rfs
termination_by structural fs

def RedVariantCases (cs : List (String × RedShape)) (tag : String) (payload : Term) : Prop :=
  match cs with
  | [] => False
  | (nm, cS) :: rest =>
      (nm = tag ∧ ∃ u, Evaluates payload u ∧ RedVal cS u) ∨
      RedVariantCases rest tag payload
termination_by structural cs
end

theorem redRigidFields_iff : ∀ (fs : List (String × RedShape)) (v : Term),
    RedRigidFields fs v ↔
      ∀ p ∈ fs, ∃ rfs body u, v = .record rfs ∧
        rfs.find? (·.1 == p.1) = some (p.1, body) ∧ Evaluates body u ∧ RedVal p.2 u
  | [], _ => ⟨by simp, fun _ => trivial⟩
  | (nm, fS) :: rest, v => by
      simp only [RedRigidFields, redRigidFields_iff rest v]
      constructor
      · intro ⟨h0, hr⟩ p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact h0
        · exact hr p hp'
      · intro hall
        exact ⟨hall (nm, fS) (List.mem_cons_self ..), fun p hp => hall p (List.mem_cons_of_mem _ hp)⟩

theorem redRowFields_iff : ∀ (fs : List (String × RedShape)) (rfs : List (String × Term)),
    RedRowFields fs rfs ↔
      ∀ p ∈ fs, ∃ body u,
        rfs.find? (·.1 == p.1) = some (p.1, body) ∧ Evaluates body u ∧ RedVal p.2 u
  | [], _ => ⟨by simp, fun _ => trivial⟩
  | (nm, fS) :: rest, rfs => by
      simp only [RedRowFields, redRowFields_iff rest rfs]
      constructor
      · intro ⟨h0, hr⟩ p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact h0
        · exact hr p hp'
      · intro hall
        exact ⟨hall (nm, fS) (List.mem_cons_self ..), fun p hp => hall p (List.mem_cons_of_mem _ hp)⟩

theorem redVariantCases_iff : ∀ (cs : List (String × RedShape)) (tag : String) (payload : Term),
    RedVariantCases cs tag payload ↔
      ∃ p ∈ cs, p.1 = tag ∧ ∃ u, Evaluates payload u ∧ RedVal p.2 u
  | [], _, _ => ⟨False.elim, by rintro ⟨_, h, _⟩; cases h⟩
  | (nm, cS) :: rest, tag, payload => by
      simp only [RedVariantCases, redVariantCases_iff rest tag payload]
      constructor
      · rintro (h0 | ⟨p, hp, hrest⟩)
        · exact ⟨(nm, cS), List.mem_cons_self .., h0⟩
        · exact ⟨p, List.mem_cons_of_mem _ hp, hrest⟩
      · rintro ⟨p, hp, hrest⟩
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact .inl hrest
        · exact .inr ⟨p, hp', hrest⟩

/-- Tait–Girard expression reducibility: closed term evaluating to a reducible value. -/
def RedExp (S : RedShape) (e : Term) : Prop :=
  Obend.Core.Invariant.Scoped 0 e ∧ ∃ v, Evaluates e v ∧ RedVal S v

theorem redVal_value_scoped : ∀ {S : RedShape} {v : Term},
    RedVal S v → Value v ∧ Obend.Core.Invariant.Scoped 0 v
  | .nat, _, ⟨n, rfl⟩ => ⟨.natural n, .natural n⟩
  | .bool, _, ⟨b, rfl⟩ => ⟨.boolean b, .boolean b⟩
  | .label, _, ⟨s, rfl⟩ => ⟨.label s, .label s⟩
  | .custody _, _, ⟨hv, hs⟩ => ⟨hv, hs⟩
  | .rigid _ _ _, _, ⟨hv, hs, _, _⟩ => ⟨hv, hs⟩
  | .arrow _ _ _ _, _, ⟨b, rfl, hb, _⟩ => ⟨.function b, .lam hb⟩
  | .spec _ _, _, ⟨m, e, _, _, rfl, hm, he, _⟩ => ⟨.specification m e, .specification hm he⟩
  | .proto _ _, _, ⟨s, t, _, _, rfl, hs, ht, _⟩ => ⟨.prototype s t, .prototype hs ht⟩
  | .row _, _, ⟨rfs, rfl, hs, _⟩ => ⟨.record rfs, hs⟩
  | .variant _, _, ⟨tag, payload, rfl, hp, _⟩ => ⟨.inject tag payload, .inject hp⟩
  | .comp resS, _, h => redVal_value_scoped (S := resS) h

/-- Strictly-positive relational connection between an `Obend.Core.Ty` under `θ` and its `RedShape` skeleton. -/
inductive HasShape (θ : Assumptions) : Ty → RedShape → Prop where
  | nat {τ} : expose θ τ = .constructor ⟨.natural, []⟩ → HasShape θ τ .nat
  | bool {τ} : expose θ τ = .constructor ⟨.boolean, []⟩ → HasShape θ τ .bool
  | label {τ} : expose θ τ = .constructor ⟨.label, []⟩ → HasShape θ τ .label
  | custody {τ c} : expose θ τ = .constructor ⟨.custody c, []⟩ → HasShape θ τ (.custody c)
  | rigid {τ idx fs isR} :
      expose θ τ = .nominal idx →
      isRowV θ.bounds [] τ = isR →
      (∀ name m, lookupV θ.bounds [] τ name = some m → ∃ s, (name, s) ∈ fs) →
      (∀ p ∈ fs, ∃ m, lookupV θ.bounds [] τ p.1 = some m) →
      (∀ p ∈ fs, ∀ m, lookupV θ.bounds [] τ p.1 = some m → HasShape θ m p.2) →
      HasShape θ τ (.rigid idx fs isR)
  | arrow {τ r q d c dS cS} :
      expose θ τ = .constructor ⟨.arrow r q, [d, c]⟩ →
      HasShape θ d dS → HasShape θ c cS →
      HasShape θ τ (.arrow r q dS cS)
  | spec {τ m e mS eS} :
      expose θ τ = .constructor ⟨.specification, [m, e]⟩ →
      HasShape θ m mS → HasShape θ e eS →
      HasShape θ τ (.spec mS eS)
  | proto {τ s t sS tS} :
      expose θ τ = .constructor ⟨.prototype, [s, t]⟩ →
      HasShape θ s sS → HasShape θ t tS →
      HasShape θ τ (.proto sS tS)
  | row {τ obs fs} :
      expose θ τ = .constructor obs →
      Obend.Core.TypeGraph.rowTag obs.tag = true →
      (∀ name m, lookupV θ.bounds [] τ name = some m → ∃ s, (name, s) ∈ fs) →
      (∀ p ∈ fs, ∃ m, lookupV θ.bounds [] τ p.1 = some m) →
      (∀ p ∈ fs, ∀ m, lookupV θ.bounds [] τ p.1 = some m → HasShape θ m p.2) →
      HasShape θ τ (.row fs)
  | variant {τ r cs} :
      expose θ τ = .constructor ⟨.variant, [r]⟩ →
      (∀ tag m, lookupV θ.bounds [] r tag = some m → ∃ s, (tag, s) ∈ cs) →
      (∀ p ∈ cs, ∃ m, lookupV θ.bounds [] r p.1 = some m) →
      (∀ p ∈ cs, ∀ m, lookupV θ.bounds [] r p.1 = some m → HasShape θ m p.2) →
      HasShape θ τ (.variant cs)
  | comp {τ p r a aS} :
      expose θ τ = .constructor ⟨.computation, [p, r, a]⟩ →
      HasShape θ a aS →
      HasShape θ τ (.comp aS)

/-! ### Shape Congruence & `sameType` Invariance -/

theorem redVal_congr {θ : Assumptions} {S₁ S₂ : RedShape} {τ : Ty}
    (h₁ : HasShape θ τ S₁) (h₂ : HasShape θ τ S₂) {v : Term} (hv : RedVal S₁ v) :
    RedVal S₂ v := by
  induction hMeas : sizeOf S₁ + sizeOf S₂ using Nat.strongRecOn generalizing S₁ S₂ τ v with
  | ind n ih =>
    cases h₁ with
    | nat e₁ => cases h₂ <;> simp_all [Obend.Core.TypeGraph.rowTag]
    | bool e₁ => cases h₂ <;> simp_all [Obend.Core.TypeGraph.rowTag]
    | label e₁ => cases h₂ <;> simp_all [Obend.Core.TypeGraph.rowTag]
    | custody e₁ => cases h₂ <;> simp_all [Obend.Core.TypeGraph.rowTag]
    | @rigid _ _ fs₁ _ e₁ hr₁ hf₁ _ hs₁ =>
      cases h₂ with
      | @rigid _ _ fs₂ _ _ hr₂ _ hg₂ hs₂ =>
        obtain ⟨hval, hsc, hisR, hmem⟩ := hv
        rw [redRigidFields_iff] at hmem
        refine ⟨hval, hsc, fun h => hisR (hr₁.symm.trans (hr₂.trans h)),
          (redRigidFields_iff _ _).mpr fun p₂ hmem₂ => ?_⟩
        obtain ⟨m, hlk⟩ := hg₂ p₂ hmem₂
        obtain ⟨s₁, hmem₁⟩ := hf₁ p₂.1 m hlk
        obtain ⟨rfs, body, u, heq, hfind, hev, hred⟩ := hmem (p₂.1, s₁) hmem₁
        have hlt : sizeOf s₁ + sizeOf p₂.2 < n := by
          subst hMeas
          have l1 := List.sizeOf_lt_of_mem hmem₁
          have l2 := List.sizeOf_lt_of_mem hmem₂
          cases p₂; simp only [Prod.mk.sizeOf_spec] at l1 l2; simp +arith at l1 l2 ⊢; omega
        exact ⟨rfs, body, u, heq, hfind, hev,
          ih _ hlt (hs₁ (p₂.1, s₁) hmem₁ m hlk) (hs₂ p₂ hmem₂ m hlk) hred rfl⟩
      | _ => simp_all
    | @arrow _ _ q₁ _ _ dS₁ cS₁ e₁ hd₁ hc₁ =>
      cases h₂ with
      | @arrow _ _ _ _ _ dS₂ cS₂ e₂ hd₂ hc₂ =>
        rw [e₁] at e₂; injection e₂ with hc; injection hc with htag hch
        injection htag with hr hq; subst hr hq
        simp only [List.cons.injEq] at hch; obtain ⟨rfl, rfl, _⟩ := hch
        obtain ⟨b, rfl, hsc, hbody⟩ := hv
        refine ⟨b, rfl, hsc, fun a ha harg => ?_⟩
        have harg' : q₁ = .erased ∨ ∃ va, Evaluates a va ∧ RedVal dS₁ va := by
          rcases harg with hq | ⟨va, hva, hrva⟩
          · exact .inl hq
          · exact .inr ⟨va, hva, ih _ (by subst hMeas; simp +arith) hd₂ hd₁ hrva rfl⟩
        obtain ⟨vr, hev, hrv⟩ := hbody a ha harg'
        exact ⟨vr, hev, ih _ (by subst hMeas; simp +arith) hc₁ hc₂ hrv rfl⟩
      | row e₂ hrt _ _ _ => rw [e₁] at e₂; cases e₂; simp [Obend.Core.TypeGraph.rowTag] at hrt
      | _ => simp_all
    | @spec _ _ _ mS₁ eS₁ e₁ hm₁ he₁ =>
      cases h₂ with
      | @spec _ _ _ mS₂ eS₂ e₂ hm₂ he₂ =>
        rw [e₁] at e₂; injection e₂ with hc; injection hc with _ hch
        simp only [List.cons.injEq] at hch; obtain ⟨rfl, rfl, _⟩ := hch
        obtain ⟨m, e, vm, ve, rfl, hsm, hse, em, rm, ee, re⟩ := hv
        exact ⟨m, e, vm, ve, rfl, hsm, hse,
          em, ih _ (by subst hMeas; simp +arith) hm₁ hm₂ rm rfl,
          ee, ih _ (by subst hMeas; simp +arith) he₁ he₂ re rfl⟩
      | row e₂ hrt _ _ _ => rw [e₁] at e₂; cases e₂; simp [Obend.Core.TypeGraph.rowTag] at hrt
      | _ => simp_all
    | @proto _ _ _ sS₁ tS₁ e₁ hs₁ ht₁ =>
      cases h₂ with
      | @proto _ _ _ sS₂ tS₂ e₂ hs₂ ht₂ =>
        rw [e₁] at e₂; injection e₂ with hc; injection hc with _ hch
        simp only [List.cons.injEq] at hch; obtain ⟨rfl, rfl, _⟩ := hch
        obtain ⟨s, t, vs, vt, rfl, hss, hst, es, rs, et, rt⟩ := hv
        exact ⟨s, t, vs, vt, rfl, hss, hst,
          es, ih _ (by subst hMeas; simp +arith) hs₁ hs₂ rs rfl,
          et, ih _ (by subst hMeas; simp +arith) ht₁ ht₂ rt rfl⟩
      | row e₂ hrt _ _ _ => rw [e₁] at e₂; cases e₂; simp [Obend.Core.TypeGraph.rowTag] at hrt
      | _ => simp_all
    | @row _ _ fs₁ e₁ _ hf₁ _ hs₁ =>
      cases h₂ with
      | @row _ _ fs₂ _ _ _ hg₂ hs₂ =>
        obtain ⟨rfs, rfl, hsc, hmem⟩ := hv
        rw [redRowFields_iff] at hmem
        refine ⟨rfs, rfl, hsc, (redRowFields_iff _ _).mpr fun p₂ hmem₂ => ?_⟩
        obtain ⟨m, hlk⟩ := hg₂ p₂ hmem₂
        obtain ⟨s₁, hmem₁⟩ := hf₁ p₂.1 m hlk
        obtain ⟨body, u, hfind, hev, hred⟩ := hmem (p₂.1, s₁) hmem₁
        have hlt : sizeOf s₁ + sizeOf p₂.2 < n := by
          subst hMeas
          have l1 := List.sizeOf_lt_of_mem hmem₁
          have l2 := List.sizeOf_lt_of_mem hmem₂
          cases p₂; simp only [Prod.mk.sizeOf_spec] at l1 l2; simp +arith at l1 l2 ⊢; omega
        exact ⟨body, u, hfind, hev, ih _ hlt (hs₁ (p₂.1, s₁) hmem₁ m hlk) (hs₂ p₂ hmem₂ m hlk) hred rfl⟩
      | _ => rw [e₁] at *; simp_all [Obend.Core.TypeGraph.rowTag]
    | @variant _ _ cs₁ e₁ _ hg₁ hs₁ =>
      cases h₂ with
      | @variant _ _ cs₂ e₂ hf₂ _ hs₂ =>
        rw [e₁] at e₂; injection e₂ with hc; injection hc with _ hch
        simp only [List.cons.injEq] at hch; obtain ⟨rfl, _⟩ := hch
        obtain ⟨tag, payload, rfl, hsc, hvc⟩ := hv
        obtain ⟨p₁, hmem₁, htag, u, hev, hred⟩ := (redVariantCases_iff _ _ _).mp hvc
        obtain ⟨m, hlk⟩ := hg₁ p₁ hmem₁
        obtain ⟨s₂, hmem₂⟩ := hf₂ p₁.1 m hlk
        have hlt : sizeOf p₁.2 + sizeOf s₂ < n := by
          subst hMeas
          have l1 := List.sizeOf_lt_of_mem hmem₁
          have l2 := List.sizeOf_lt_of_mem hmem₂
          cases p₁; simp only [Prod.mk.sizeOf_spec] at l1 l2; simp +arith at l1 l2 ⊢; omega
        exact ⟨tag, payload, rfl, hsc,
          (redVariantCases_iff _ _ _).mpr ⟨(p₁.1, s₂), hmem₂, htag, u, hev,
            ih _ hlt (hs₁ p₁ hmem₁ m hlk) (hs₂ (p₁.1, s₂) hmem₂ m hlk) hred rfl⟩⟩
      | row e₂ hrt _ _ _ => rw [e₁] at e₂; cases e₂; simp [Obend.Core.TypeGraph.rowTag] at hrt
      | _ => simp_all
    | @comp _ _ _ _ aS₁ e₁ ha₁ =>
      cases h₂ with
      | @comp _ _ _ _ aS₂ e₂ ha₂ =>
        rw [e₁] at e₂; injection e₂ with hc; injection hc with _ hch
        simp only [List.cons.injEq] at hch; obtain ⟨_, _, rfl, _⟩ := hch
        exact ih _ (by subst hMeas; simp +arith) ha₁ ha₂ hv rfl
      | row e₂ hrt _ _ _ => rw [e₁] at e₂; cases e₂; simp [Obend.Core.TypeGraph.rowTag] at hrt
      | _ => simp_all

private theorem not_rowTag_of_ordinary {θ : Assumptions} {τ₁ τ₂ : Ty} {tg₁ : Tag} {ch₁ : List Ty}
    {obs₂ : Constructor}
    (rel : Obend.Core.TypeGraph.Equivalent θ τ₁ τ₂)
    (hex₁ : expose θ τ₁ = .constructor ⟨tg₁, ch₁⟩)
    (hrt₁ : Obend.Core.TypeGraph.rowTag tg₁ = false)
    (hex₂ : expose θ τ₂ = .constructor obs₂) :
    Obend.Core.TypeGraph.rowTag obs₂.tag = false := by
  have heq := Obend.Core.TypeGraph.equivalent_head rel
  cases hr₂ : Obend.Core.TypeGraph.rowTag obs₂.tag
  · rfl
  · simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, hrt₁, hr₂,
      Obend.Core.TypeGraph.rowObservation, Obend.Core.TypeGraph.labelHead] at heq

theorem hasShape_sameType {θ : Assumptions} {S : RedShape} :
    ∀ {τ₁ τ₂ : Ty}, HasShape θ τ₁ S → sameType θ τ₁ τ₂ = true → HasShape θ τ₂ S := by
  induction hMeas : sizeOf S using Nat.strongRecOn generalizing S with
  | ind n ih =>
    intro τ₁ τ₂ hs hsame
    have rel := (sameType_iff θ τ₁ τ₂).mp hsame
    have heq := Obend.Core.TypeGraph.equivalent_head rel
    cases hs with
    | nat hex₁ =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, Obend.Core.TypeGraph.rowTag, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs =>
        have hr := not_rowTag_of_ordinary rel hex₁ rfl hex₂
        obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components rel hex₁ hex₂
          (by simp [Obend.Core.TypeGraph.rowTag]) (by simp [hr])
        cases obs with | mk tg ch =>
        simp only at htag hch; subst htag
        cases ch with | nil => exact .nat hex₂ | cons _ _ => cases hch
    | bool hex₁ =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, Obend.Core.TypeGraph.rowTag, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs =>
        have hr := not_rowTag_of_ordinary rel hex₁ rfl hex₂
        obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components rel hex₁ hex₂
          (by simp [Obend.Core.TypeGraph.rowTag]) (by simp [hr])
        cases obs with | mk tg ch =>
        simp only at htag hch; subst htag
        cases ch with | nil => exact .bool hex₂ | cons _ _ => cases hch
    | label hex₁ =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, Obend.Core.TypeGraph.rowTag, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs =>
        have hr := not_rowTag_of_ordinary rel hex₁ rfl hex₂
        obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components rel hex₁ hex₂
          (by simp [Obend.Core.TypeGraph.rowTag]) (by simp [hr])
        cases obs with | mk tg ch =>
        simp only at htag hch; subst htag
        cases ch with | nil => exact .label hex₂ | cons _ _ => cases hch
    | custody hex₁ =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, Obend.Core.TypeGraph.rowTag, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs =>
        have hr := not_rowTag_of_ordinary rel hex₁ rfl hex₂
        obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components rel hex₁ hex₂
          (by simp [Obend.Core.TypeGraph.rowTag]) (by simp [hr])
        cases obs with | mk tg ch =>
        simp only at htag hch; subst htag
        cases ch with | nil => exact .custody hex₂ | cons _ _ => cases hch
    | @rigid _ idx fs isR hex₁ hisR hf hg hsh =>
      have hex₂ : expose θ τ₂ = .nominal idx := by
        cases h2 : expose θ τ₂ with
        | nominal j =>
          simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, h2, Obend.Core.TypeGraph.labelHead] at heq
          subst heq; rfl
        | unproductive j =>
          simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, h2, Obend.Core.TypeGraph.labelHead] at heq
        | constructor obs =>
          by_cases hr : Obend.Core.TypeGraph.rowTag obs.tag = true <;>
            simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, h2, hr, Obend.Core.TypeGraph.rowObservation, Obend.Core.TypeGraph.labelHead] at heq
      have hisR₂ : isRowV θ.bounds [] τ₂ = isR := by
        rw [← hisR]; apply Bool.eq_iff_iff.mpr
        rw [isRowV_iff, isRowV_iff]
        exact (Obend.Core.TypeGraph.equivalent_finite_row_iff rel).symm
      refine .rigid hex₂ hisR₂ (fun name m₂ hlk₂ => ?_) (fun p hp => ?_) (fun p hp m₂ hlk₂ => ?_)
      · obtain ⟨f₂, hlk₂'⟩ := (lookupV_iff θ.bounds τ₂ name m₂).mp hlk₂
        obtain ⟨f₁, m₁, hlk₁', _⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport rel f₂ name m₂ hlk₂'
        exact hf name m₁ ((lookupV_iff θ.bounds τ₁ name m₁).mpr ⟨f₁, hlk₁'⟩)
      · obtain ⟨m₁, hlk₁⟩ := hg p hp
        obtain ⟨f₁, hlk₁'⟩ := (lookupV_iff θ.bounds τ₁ p.1 m₁).mp hlk₁
        obtain ⟨f₂, m₂, hlk₂', _⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport ((Obend.Core.TypeGraph.equivalent_equivalence θ).symm rel) f₁ p.1 m₁ hlk₁'
        exact ⟨m₂, (lookupV_iff θ.bounds τ₂ p.1 m₂).mpr ⟨f₂, hlk₂'⟩⟩
      · obtain ⟨f₂, hlk₂'⟩ := (lookupV_iff θ.bounds τ₂ p.1 m₂).mp hlk₂
        obtain ⟨f₁, m₁, hlk₁', hmrel⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport rel f₂ p.1 m₂ hlk₂'
        have hmS := hsh p hp m₁ ((lookupV_iff θ.bounds τ₁ p.1 m₁).mpr ⟨f₁, hlk₁'⟩)
        have hlt : sizeOf p.2 < n := by
          subst hMeas; have := List.sizeOf_lt_of_mem hp; cases p; simp +arith at this ⊢; omega
        exact ih _ hlt rfl hmS ((sameType_iff θ m₁ m₂).mpr hmrel)
    | @arrow _ r q _ _ dS cS hex₁ hd hc =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, Obend.Core.TypeGraph.rowTag, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs =>
        have hr := not_rowTag_of_ordinary rel hex₁ rfl hex₂
        obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components rel hex₁ hex₂
          (by simp [Obend.Core.TypeGraph.rowTag]) (by simp [hr])
        cases obs with | mk tg ch =>
        simp only at htag hch; subst htag
        rcases ch with _ | ⟨d₂, _ | ⟨c₂, _ | _⟩⟩
        · cases hch
        · cases hch.2
        · exact .arrow hex₂
            (ih _ (by subst hMeas; simp +arith) rfl hd ((sameType_iff θ _ _).mpr hch.1))
            (ih _ (by subst hMeas; simp +arith) rfl hc ((sameType_iff θ _ _).mpr hch.2.1))
        · cases hch.2.2
    | @spec _ _ _ mS eS hex₁ hm he =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, Obend.Core.TypeGraph.rowTag, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs =>
        have hr := not_rowTag_of_ordinary rel hex₁ rfl hex₂
        obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components rel hex₁ hex₂
          (by simp [Obend.Core.TypeGraph.rowTag]) (by simp [hr])
        cases obs with | mk tg ch =>
        simp only at htag hch; subst htag
        rcases ch with _ | ⟨m₂, _ | ⟨e₂, _ | _⟩⟩
        · cases hch
        · cases hch.2
        · exact .spec hex₂
            (ih _ (by subst hMeas; simp +arith) rfl hm ((sameType_iff θ _ _).mpr hch.1))
            (ih _ (by subst hMeas; simp +arith) rfl he ((sameType_iff θ _ _).mpr hch.2.1))
        · cases hch.2.2
    | @proto _ _ _ sS tS hex₁ hs' ht' =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, Obend.Core.TypeGraph.rowTag, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs =>
        have hr := not_rowTag_of_ordinary rel hex₁ rfl hex₂
        obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components rel hex₁ hex₂
          (by simp [Obend.Core.TypeGraph.rowTag]) (by simp [hr])
        cases obs with | mk tg ch =>
        simp only at htag hch; subst htag
        rcases ch with _ | ⟨s₂, _ | ⟨t₂, _ | _⟩⟩
        · cases hch
        · cases hch.2
        · exact .proto hex₂
            (ih _ (by subst hMeas; simp +arith) rfl hs' ((sameType_iff θ _ _).mpr hch.1))
            (ih _ (by subst hMeas; simp +arith) rfl ht' ((sameType_iff θ _ _).mpr hch.2.1))
        · cases hch.2.2
    | @row _ _ fs hex₁ hrt₁ hf hg hsh =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, hrt₁, Obend.Core.TypeGraph.rowObservation, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs₂ =>
        by_cases hr₂ : Obend.Core.TypeGraph.rowTag obs₂.tag = true
        · refine .row hex₂ hr₂ (fun name m₂ hlk₂ => ?_) (fun p hp => ?_) (fun p hp m₂ hlk₂ => ?_)
          · obtain ⟨f₂, hlk₂'⟩ := (lookupV_iff θ.bounds τ₂ name m₂).mp hlk₂
            obtain ⟨f₁, m₁, hlk₁', _⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport rel f₂ name m₂ hlk₂'
            exact hf name m₁ ((lookupV_iff θ.bounds τ₁ name m₁).mpr ⟨f₁, hlk₁'⟩)
          · obtain ⟨m₁, hlk₁⟩ := hg p hp
            obtain ⟨f₁, hlk₁'⟩ := (lookupV_iff θ.bounds τ₁ p.1 m₁).mp hlk₁
            obtain ⟨f₂, m₂, hlk₂', _⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport ((Obend.Core.TypeGraph.equivalent_equivalence θ).symm rel) f₁ p.1 m₁ hlk₁'
            exact ⟨m₂, (lookupV_iff θ.bounds τ₂ p.1 m₂).mpr ⟨f₂, hlk₂'⟩⟩
          · obtain ⟨f₂, hlk₂'⟩ := (lookupV_iff θ.bounds τ₂ p.1 m₂).mp hlk₂
            obtain ⟨f₁, m₁, hlk₁', hmrel⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport rel f₂ p.1 m₂ hlk₂'
            have hmS := hsh p hp m₁ ((lookupV_iff θ.bounds τ₁ p.1 m₁).mpr ⟨f₁, hlk₁'⟩)
            have hlt : sizeOf p.2 < n := by
              subst hMeas; have := List.sizeOf_lt_of_mem hp; cases p; simp +arith at this ⊢; omega
            exact ih _ hlt rfl hmS ((sameType_iff θ m₁ m₂).mpr hmrel)
        · simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, hrt₁, hr₂, Obend.Core.TypeGraph.rowObservation, Obend.Core.TypeGraph.labelHead] at heq
    | @variant _ r₁ cs hex₁ hf hg hsh =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, Obend.Core.TypeGraph.rowTag, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs =>
        have hr := not_rowTag_of_ordinary rel hex₁ rfl hex₂
        obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components rel hex₁ hex₂
          (by simp [Obend.Core.TypeGraph.rowTag]) (by simp [hr])
        cases obs with | mk tg ch =>
        simp only at htag hch; subst htag
        rcases ch with _ | ⟨r₂, _ | _⟩
        · cases hch
        · have rrel := hch.1
          refine .variant hex₂ (fun tag m₂ hlk₂ => ?_) (fun p hp => ?_) (fun p hp m₂ hlk₂ => ?_)
          · obtain ⟨f₂, hlk₂'⟩ := (lookupV_iff θ.bounds r₂ tag m₂).mp hlk₂
            obtain ⟨f₁, m₁, hlk₁', _⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport rrel f₂ tag m₂ hlk₂'
            exact hf tag m₁ ((lookupV_iff θ.bounds r₁ tag m₁).mpr ⟨f₁, hlk₁'⟩)
          · obtain ⟨m₁, hlk₁⟩ := hg p hp
            obtain ⟨f₁, hlk₁'⟩ := (lookupV_iff θ.bounds r₁ p.1 m₁).mp hlk₁
            obtain ⟨f₂, m₂, hlk₂', _⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport ((Obend.Core.TypeGraph.equivalent_equivalence θ).symm rrel) f₁ p.1 m₁ hlk₁'
            exact ⟨m₂, (lookupV_iff θ.bounds r₂ p.1 m₂).mpr ⟨f₂, hlk₂'⟩⟩
          · obtain ⟨f₂, hlk₂'⟩ := (lookupV_iff θ.bounds r₂ p.1 m₂).mp hlk₂
            obtain ⟨f₁, m₁, hlk₁', hmrel⟩ := Obend.Core.TypeGraph.equivalent_lookup_transport rrel f₂ p.1 m₂ hlk₂'
            have hmS := hsh p hp m₁ ((lookupV_iff θ.bounds r₁ p.1 m₁).mpr ⟨f₁, hlk₁'⟩)
            have hlt : sizeOf p.2 < n := by
              subst hMeas; have := List.sizeOf_lt_of_mem hp; cases p; simp +arith at this ⊢; omega
            exact ih _ hlt rfl hmS ((sameType_iff θ m₁ m₂).mpr hmrel)
        · cases hch.2
    | @comp _ _ _ _ aS hex₁ ha =>
      cases hex₂ : expose θ τ₂ with
      | nominal _ | unproductive _ =>
        simp [Obend.Core.TypeGraph.graph, Obend.Core.TypeGraph.observe, hex₁, hex₂, Obend.Core.TypeGraph.rowTag, Obend.Core.TypeGraph.labelHead] at heq
      | constructor obs =>
        have hr := not_rowTag_of_ordinary rel hex₁ rfl hex₂
        obtain ⟨htag, hch⟩ := Obend.Core.TypeGraph.equivalent_exposed_components rel hex₁ hex₂
          (by simp [Obend.Core.TypeGraph.rowTag]) (by simp [hr])
        cases obs with | mk tg ch =>
        simp only at htag hch; subst htag
        rcases ch with _ | ⟨p₂, _ | ⟨r₂, _ | ⟨a₂, _ | _⟩⟩⟩
        · cases hch
        · cases hch.2
        · cases hch.2.2
        · exact .comp hex₂ (ih _ (by subst hMeas; simp +arith) rfl ha ((sameType_iff θ _ _).mpr hch.2.2.1))
        · cases hch.2.2.2

/-! ### Existence of `HasShape` Under `PositiveBounds` -/

private def tyMeasure (vRank : Nat → Nat) : Ty → Nat
  | .natural | .boolean | .label | .emptyRow | .custody _ => 1
  | .variable i => vRank i + 1
  | .arrow _ _ d c => tyMeasure vRank d + tyMeasure vRank c + 2
  | .specification m e => tyMeasure vRank m + tyMeasure vRank e + 2
  | .prototype s t => tyMeasure vRank s + tyMeasure vRank t + 2
  | .field _ m tl => max (tyMeasure vRank m + 1) (tyMeasure vRank tl + 1)
  | .variant r => tyMeasure vRank r + 2
  | .computation p r a => tyMeasure vRank p + tyMeasure vRank r + tyMeasure vRank a + 2

private def buildVarRank : Bounds → Nat → Nat
  | [], _ => 1
  | (idx, b) :: rest, i =>
      let rRest := buildVarRank rest
      if i = idx then tyMeasure rRest b + 1 else rRest i

private theorem varsInAllowed_mono {a₁ a₂ : List Nat}
    (hs : ∀ x, a₁.contains x = true → a₂.contains x = true)
    {t : Ty} (ht : varsInAllowed a₁ t = true) : varsInAllowed a₂ t = true := by
  induction t with
  | natural | boolean | label | emptyRow | custody _ => exact ht
  | «variable» _ => exact hs _ ht
  | arrow _ _ _ _ ih1 ih2 | field _ _ _ ih1 ih2 | specification _ _ ih1 ih2 | prototype _ _ ih1 ih2 =>
    simp only [varsInAllowed, Bool.and_eq_true] at ht ⊢
    exact ⟨ih1 ht.1, ih2 ht.2⟩
  | variant _ ih => exact ih ht
  | computation _ _ _ ih1 ih2 ih3 =>
    simp only [varsInAllowed, Bool.and_eq_true] at ht ⊢
    exact ⟨⟨ih1 ht.1.1, ih2 ht.1.2⟩, ih3 ht.2⟩

private theorem tyMeasure_congr {r₁ r₂ : Nat → Nat} {allowed : List Nat}
    (heq : ∀ i ∈ allowed, r₁ i = r₂ i)
    {τ : Ty} (ht : varsInAllowed allowed τ = true) : tyMeasure r₁ τ = tyMeasure r₂ τ := by
  induction τ with
  | natural | boolean | label | emptyRow | custody _ => rfl
  | «variable» i =>
    simp only [varsInAllowed, List.contains_iff_mem] at ht
    simp [tyMeasure, heq i ht]
  | arrow _ _ _ _ ih1 ih2 | specification _ _ ih1 ih2 | prototype _ _ ih1 ih2 | field _ _ _ ih1 ih2 =>
    simp only [varsInAllowed, Bool.and_eq_true] at ht
    simp [tyMeasure, ih1 ht.1, ih2 ht.2]
  | variant _ ih =>
    simp only [varsInAllowed] at ht; simp [tyMeasure, ih ht]
  | computation _ _ _ ih1 ih2 ih3 =>
    simp only [varsInAllowed, Bool.and_eq_true] at ht
    simp [tyMeasure, ih1 ht.1.1, ih2 ht.1.2, ih3 ht.2]

private theorem nodupNatB_sound : ∀ {xs : List Nat}, nodupNatB xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => by
      simp only [nodupNatB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
      exact List.nodup_cons.mpr ⟨h.1, nodupNatB_sound h.2⟩

private theorem nodupNatB_inhabited :
    ∃ xs : List Nat, 0 < xs.length ∧ nodupNatB xs = true ∧ xs.Nodup :=
  ⟨[7, 2, 11], by decide, by decide, nodupNatB_sound (by decide)⟩

private theorem acyclic_lookup_vars {freeRigids : List Nat} :
    ∀ {bounds : Bounds}, AcyclicBoundsList freeRigids bounds = true →
      ∀ {idx : Nat} {b : Ty}, bounds.lookup idx = some b →
        varsInAllowed (freeRigids ++ bounds.map Prod.fst) b = true
  | [], _, _, _, h => by simp at h
  | hd :: tl, hacyc, idx, b, hlk => by
      simp only [AcyclicBoundsList, Bool.and_eq_true] at hacyc
      have hsub : ∀ v, (freeRigids ++ tl.map Prod.fst).contains v = true →
          (freeRigids ++ (hd :: tl).map Prod.fst).contains v = true := by
        intro v hv; simp only [List.contains_iff_mem, List.mem_append, List.map_cons, List.mem_cons] at hv ⊢
        exact hv.imp id .inr
      by_cases heq : idx = hd.1
      · subst idx
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hlk
        subst b; exact varsInAllowed_mono hsub hacyc.1.2
      · have hbeq : (idx == hd.1) = false := beq_false_of_ne heq
        simp only [List.lookup, hbeq] at hlk
        exact varsInAllowed_mono hsub (acyclic_lookup_vars hacyc.2 hlk)

private theorem buildVarRank_lookup {freeRigids : List Nat} :
    ∀ {bounds : Bounds}, (bounds.map Prod.fst).Nodup →
      AcyclicBoundsList freeRigids bounds = true →
      (∀ r ∈ freeRigids, r ∉ bounds.map Prod.fst) →
      ∀ {idx : Nat} {b : Ty}, bounds.lookup idx = some b →
        tyMeasure (buildVarRank bounds) b < buildVarRank bounds idx
  | [], _, _, _, _, _, h => by simp at h
  | (k, bk) :: rest, hnd, hacyc, hfree, idx, b, hlk => by
      obtain ⟨hk_notin, hnd_rest⟩ := List.nodup_cons.mp hnd
      simp only [AcyclicBoundsList, Bool.and_eq_true] at hacyc
      obtain ⟨⟨_, hvars⟩, hacyc_rest⟩ := hacyc
      have hfree_rest : ∀ r ∈ freeRigids, r ∉ rest.map Prod.fst :=
        fun r hr hm => hfree r hr (List.mem_cons_of_mem _ hm)
      have hne_k : ∀ j ∈ freeRigids ++ rest.map Prod.fst, j ≠ k := by
        intro j hj hjk; subst j
        rcases List.mem_append.mp hj with hf | hr
        · exact hfree k hf (List.mem_cons_self ..)
        · exact hk_notin hr
      by_cases heq : idx = k
      · subst idx
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hlk
        subst b
        have hcongr : tyMeasure (buildVarRank ((k, bk) :: rest)) bk = tyMeasure (buildVarRank rest) bk :=
          tyMeasure_congr (fun j hj => by simp [buildVarRank, hne_k j hj]) hvars
        have hrhs : buildVarRank ((k, bk) :: rest) k = tyMeasure (buildVarRank rest) bk + 1 := by
          simp [buildVarRank]
        rw [hcongr, hrhs]; omega
      · have hbeq : (idx == k) = false := beq_false_of_ne heq
        simp only [List.lookup, hbeq] at hlk
        have ih := buildVarRank_lookup hnd_rest hacyc_rest hfree_rest hlk
        have hb_vars := acyclic_lookup_vars hacyc_rest hlk
        have hcongr : tyMeasure (buildVarRank ((k, bk) :: rest)) b = tyMeasure (buildVarRank rest) b :=
          tyMeasure_congr (fun j hj => by simp [buildVarRank, hne_k j hj]) hb_vars
        have hrhs : buildVarRank ((k, bk) :: rest) idx = buildVarRank rest idx := by
          simp [buildVarRank, heq]
        rw [hcongr, hrhs]; exact ih

private theorem lookup_measure_lt {θ : Assumptions} (hPos : PositiveBounds θ = true) :
    ∀ {fuel : Nat} {τ : Ty} {name : String} {m : Ty},
      τ.lookup θ.bounds fuel name = some m →
      tyMeasure (buildVarRank θ.bounds) m < tyMeasure (buildVarRank θ.bounds) τ
  | 0, _, _, _, h => by simp [Ty.lookup] at h
  | _ + 1, .field _ _ _, _, _, h => by
      simp only [Ty.lookup] at h
      split at h
      · injection h with hm; subst hm; simp [tyMeasure]; omega
      · have ih := lookup_measure_lt hPos h
        simp [tyMeasure] at ih ⊢; omega
  | _ + 1, .variable idx, _, _, h => by
      simp only [Ty.lookup, Option.bind_eq_bind] at h
      cases hlk : θ.bounds.lookup idx with
      | none => simp [hlk] at h
      | some b =>
        simp only [hlk, Option.bind_some] at h
        have ih := lookup_measure_lt hPos h
        simp only [PositiveBounds, Bool.and_eq_true] at hPos
        have hfree : ∀ r ∈ unaliasedRigids θ, r ∉ θ.bounds.map Prod.fst := by
          intro r hr; simp only [unaliasedRigids, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hr
          exact hr.2
        have hstep := buildVarRank_lookup (nodupNatB_sound hPos.1.2) hPos.2 hfree hlk
        simp [tyMeasure]; omega
  | _ + 1, .natural, _, _, h | _ + 1, .boolean, _, _, h | _ + 1, .label, _, _, h
  | _ + 1, .emptyRow, _, _, h | _ + 1, .arrow .., _, _, h | _ + 1, .specification .., _, _, h
  | _ + 1, .prototype .., _, _, h | _ + 1, .custody _, _, _, h | _ + 1, .variant _, _, _, h
  | _ + 1, .computation .., _, _, h => by simp [Ty.lookup] at h

private def candidateLabels (θ : Assumptions) (τ : Ty) : List String :=
  Obend.Core.RecursiveRows.fieldLabels (support θ τ τ)

private theorem lookup_mem_candidateLabels {θ : Assumptions} {root : Ty} :
    ∀ {fuel : Nat} {τ : Ty} {name : String} {m : Ty},
      τ ∈ support θ root root →
      τ.lookup θ.bounds fuel name = some m →
      name ∈ Obend.Core.RecursiveRows.fieldLabels (support θ root root)
  | 0, _, _, _, _, h => by simp [Ty.lookup] at h
  | _ + 1, .field prior _ tl, name, _, hsup, h => by
      by_cases hit : prior = name
      · subst hit; exact Obend.Core.RecursiveRows.field_name_mem_fieldLabels hsup
      · simp only [Ty.lookup, hit, ↓reduceIte] at h
        have htl : tl ∈ support θ root root :=
          support_subterms hsup (by simp [subterms, self_mem_subterms])
        exact lookup_mem_candidateLabels htl h
  | _ + 1, .variable idx, _, _, _, h => by
      simp only [Ty.lookup, Option.bind_eq_bind] at h
      cases hlk : θ.bounds.lookup idx with
      | none => simp [hlk] at h
      | some b =>
        simp only [hlk, Option.bind_some] at h
        obtain ⟨_, _, heq, _⟩ := List.lookup_eq_some_iff.mp hlk
        have hb : b ∈ support θ root root :=
          bound_subterm_mem_support θ root root (idx, b) (by rw [heq]; simp) b (self_mem_subterms b)
        exact lookup_mem_candidateLabels hb h
  | _ + 1, .natural, _, _, _, h | _ + 1, .boolean, _, _, _, h | _ + 1, .label, _, _, _, h
  | _ + 1, .emptyRow, _, _, _, h | _ + 1, .arrow .., _, _, _, h | _ + 1, .specification .., _, _, _, h
  | _ + 1, .prototype .., _, _, _, h | _ + 1, .custody _, _, _, _, h | _ + 1, .variant _, _, _, _, h
  | _ + 1, .computation .., _, _, _, h => by simp [Ty.lookup] at h

private theorem aliasChain_measure_le {θ : Assumptions} (hPos : PositiveBounds θ = true) :
    ∀ {start finish : Ty} {path : List Nat},
      AliasChain θ start path finish →
      (path = [] ∧ start = finish) ∨
        tyMeasure (buildVarRank θ.bounds) finish < tyMeasure (buildVarRank θ.bounds) start
  | _, _, _, .nil _ => .inl ⟨rfl, rfl⟩
  | _, _, _, .cons found _ rest => by
      have hbound := Assumptions.alias_bound found
      simp only [PositiveBounds, Bool.and_eq_true] at hPos
      have hfree : ∀ r ∈ unaliasedRigids θ, r ∉ θ.bounds.map Prod.fst := by
        intro r hr; simp only [unaliasedRigids, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hr
        exact hr.2
      have hstep := buildVarRank_lookup (nodupNatB_sound hPos.1.2) hPos.2 hfree hbound
      rcases aliasChain_measure_le (by simp [PositiveBounds, hPos]) rest with ⟨_, rfl⟩ | hlt
      · exact .inr (by simp [tyMeasure]; omega)
      · exact .inr (by simp [tyMeasure] at hlt ⊢; omega)

private theorem positiveBounds_no_unproductive {θ : Assumptions} (hPos : PositiveBounds θ = true)
    (τ : Ty) (rep : Nat) : expose θ τ ≠ .unproductive rep := by
  intro hunp
  obtain ⟨path, finish, chain, _, _, stopped⟩ :=
    exposeWalk_trace θ (θ.bounds.map Prod.fst) [] (initial_covers θ) τ
  change Stopped θ (visitPath [] path) finish (expose θ τ) at stopped
  rw [hunp] at stopped
  generalize heq : Head.unproductive rep = h at stopped
  cases stopped with
  | productive _ =>
    cases finish <;> simp [constructorHead] at heq
  | unbound _ _ => cases heq
  | activity _ _ _ => cases heq
  | @cycle idx seen =>
    have hmem : idx ∈ path := by simpa [visitPath_reverse] using seen
    obtain ⟨p₁, p₂, hp⟩ := List.append_of_mem hmem
    have splitChain : ∀ {s : Ty} {l₁ : List Nat},
        AliasChain θ s (l₁ ++ idx :: p₂) (.variable idx) →
        AliasChain θ (.variable idx) (idx :: p₂) (.variable idx) := by
      intro s l₁ hc
      induction l₁ generalizing s with
      | nil => have hs := chain_nonempty_start hc; subst hs; exact hc
      | cons _ _ ih => cases hc with | cons _ _ tail => exact ih tail
    rw [hp] at chain
    rcases aliasChain_measure_le hPos (splitChain chain) with ⟨hgd, _⟩ | hlt
    · cases hgd
    · exact Nat.lt_irrefl _ hlt

/-- Unconditional shape realization: every `τ : Ty` under `PositiveBounds θ` has a `RedShape`. -/
theorem exists_hasShape {θ : Assumptions} (hPos : PositiveBounds θ = true) (τ : Ty) :
    ∃ (S : RedShape), HasShape θ τ S := by
  induction hM : tyMeasure (buildVarRank θ.bounds) τ using Nat.strongRecOn generalizing τ with
  | ind n ih =>
    have collectFields : ∀ (rowTy : Ty),
        tyMeasure (buildVarRank θ.bounds) rowTy ≤ n →
        ∀ (lbls : List String),
        ∃ fs : List (String × RedShape),
          (∀ name ∈ lbls, ∀ m, lookupV θ.bounds [] rowTy name = some m → ∃ s, (name, s) ∈ fs) ∧
          (∀ p ∈ fs, ∃ m, lookupV θ.bounds [] rowTy p.1 = some m) ∧
          (∀ p ∈ fs, ∀ m, lookupV θ.bounds [] rowTy p.1 = some m → HasShape θ m p.2) := by
      intro rowTy hle lbls
      induction lbls with
      | nil => exact ⟨[], by simp, by simp, by simp⟩
      | cons l ls ihl =>
        obtain ⟨fsRest, hfw, hbw, hsh⟩ := ihl
        cases hlk : lookupV θ.bounds [] rowTy l with
        | none =>
          refine ⟨fsRest, fun name hmem m hm => ?_, hbw, hsh⟩
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · rw [hlk] at hm; cases hm
          · exact hfw name hmem' m hm
        | some m =>
          obtain ⟨fuel, hlkFuel⟩ := (lookupV_iff θ.bounds rowTy l m).mp hlk
          have hlt : tyMeasure (buildVarRank θ.bounds) m < n :=
            Nat.lt_of_lt_of_le (lookup_measure_lt hPos hlkFuel) hle
          obtain ⟨mS, hmS⟩ := ih _ hlt m rfl
          refine ⟨(l, mS) :: fsRest, fun name hmem m' hm' => ?_, fun p hp => ?_, fun p hp m' hm' => ?_⟩
          · rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact ⟨mS, List.mem_cons_self ..⟩
            · obtain ⟨s', hs'⟩ := hfw name hmem' m' hm'
              exact ⟨s', List.mem_cons_of_mem _ hs'⟩
          · rcases List.mem_cons.mp hp with rfl | hp'
            · exact ⟨m, hlk⟩
            · exact hbw p hp'
          · rcases List.mem_cons.mp hp with rfl | hp'
            · rw [hlk] at hm'; cases hm'; exact hmS
            · exact hsh p hp' m' hm'
    cases hex : expose θ τ with
    | unproductive rep => exact absurd hex (positiveBounds_no_unproductive hPos τ rep)
    | nominal idx =>
      obtain ⟨fs, hfw, hbw, hsh⟩ := collectFields τ (Nat.le_of_eq hM) (candidateLabels θ τ)
      refine ⟨RedShape.rigid idx fs (isRowV θ.bounds [] τ),
        HasShape.rigid hex rfl (fun name m hlk => ?_) hbw hsh⟩
      obtain ⟨fuel, hlkFuel⟩ := (lookupV_iff θ.bounds τ name m).mp hlk
      exact hfw name (lookup_mem_candidateLabels (left_mem_support θ τ τ) hlkFuel) m hlk
    | constructor obs =>
      by_cases hrt : Obend.Core.TypeGraph.rowTag obs.tag = true
      · obtain ⟨fs, hfw, hbw, hsh⟩ := collectFields τ (Nat.le_of_eq hM) (candidateLabels θ τ)
        refine ⟨RedShape.row fs, HasShape.row hex hrt (fun name m hlk => ?_) hbw hsh⟩
        obtain ⟨fuel, hlkFuel⟩ := (lookupV_iff θ.bounds τ name m).mp hlk
        exact hfw name (lookup_mem_candidateLabels (left_mem_support θ τ τ) hlkFuel) m hlk
      · obtain ⟨source, _, chain, hraw⟩ := Obend.Core.TypeGraph.expose_constructor_chain θ τ obs hex
        have hle_src : tyMeasure (buildVarRank θ.bounds) source ≤ n := by
          rcases aliasChain_measure_le hPos chain with ⟨_, rfl⟩ | hlt
          · exact Nat.le_of_eq hM
          · omega
        cases source with
        | natural => simp [constructorHead] at hraw; subst hraw; exact ⟨RedShape.nat, .nat hex⟩
        | boolean => simp [constructorHead] at hraw; subst hraw; exact ⟨RedShape.bool, .bool hex⟩
        | label => simp [constructorHead] at hraw; subst hraw; exact ⟨RedShape.label, .label hex⟩
        | custody c => simp [constructorHead] at hraw; subst hraw; exact ⟨RedShape.custody c, .custody hex⟩
        | emptyRow => simp [constructorHead] at hraw; subst hraw; simp [Obend.Core.TypeGraph.rowTag] at hrt
        | field _ _ _ => simp [constructorHead] at hraw; subst hraw; simp [Obend.Core.TypeGraph.rowTag] at hrt
        | «variable» _ => simp [constructorHead] at hraw
        | arrow r q d c =>
          simp [constructorHead] at hraw; subst hraw
          simp [tyMeasure] at hle_src
          obtain ⟨dS, hdS⟩ := ih _ (by omega) d rfl
          obtain ⟨cS, hcS⟩ := ih _ (by omega) c rfl
          exact ⟨RedShape.arrow r q dS cS, .arrow hex hdS hcS⟩
        | specification m e =>
          simp [constructorHead] at hraw; subst hraw
          simp [tyMeasure] at hle_src
          obtain ⟨mS, hmS⟩ := ih _ (by omega) m rfl
          obtain ⟨eS, heS⟩ := ih _ (by omega) e rfl
          exact ⟨RedShape.spec mS eS, .spec hex hmS heS⟩
        | prototype s t =>
          simp [constructorHead] at hraw; subst hraw
          simp [tyMeasure] at hle_src
          obtain ⟨sS, hsS⟩ := ih _ (by omega) s rfl
          obtain ⟨tS, htS⟩ := ih _ (by omega) t rfl
          exact ⟨RedShape.proto sS tS, .proto hex hsS htS⟩
        | variant r =>
          simp [constructorHead] at hraw; subst hraw
          simp [tyMeasure] at hle_src
          obtain ⟨cs, hfw, hbw, hsh⟩ := collectFields r (by omega) (candidateLabels θ r)
          refine ⟨RedShape.variant cs, .variant hex (fun tag m hlk => ?_) hbw hsh⟩
          obtain ⟨fuel, hlkFuel⟩ := (lookupV_iff θ.bounds r tag m).mp hlk
          exact hfw tag (lookup_mem_candidateLabels (left_mem_support θ r r) hlkFuel) m hlk
        | computation p r a =>
          simp [constructorHead] at hraw; subst hraw
          simp [tyMeasure] at hle_src
          obtain ⟨aS, haS⟩ := ih _ (by omega) a rfl
          exact ⟨RedShape.comp aS, .comp hex haS⟩

end Obend.Core.Canonicity
end
