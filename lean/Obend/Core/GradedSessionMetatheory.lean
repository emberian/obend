module
/-
# Obend.Core.GradedSessionMetatheory — graded resources and session-typed channels

A graded term calculus with synchronous session communication and capability settlement.
**Quantitative typing (McBride 2016, Atkey 2018).** A `ResourceRig` is an ordered semiring with no
zero divisors and no additive inverses. `HasTy Γ t A U` types a term in the type context `Γ` and
synthesizes the usage `U : Nat → R` it makes of each variable; context addition is `Usage.add`,
scaling is `Usage.scale`. A binder annotated `π` accepts a body that uses it `ρ ⊑ π` times. Over the
rig `ZeroOneOmega` (`0` erased, `1` exactly once, `ω` unrestricted) the order is `0 ⊑ ω`, `1 ⊑ ω`
and nothing else, so a `1` binder is used exactly once at run time and a `0` binder never
(`linear_cap_used_exactly_once`). The substitution lemma (`qtt_subst_preserves_grades`), subject
reduction (`HasTy.step`) and erasure (`qtt_zero_grade_erasure_sound`) hold over every rig.

**Binary session types (Honda 1993; Wadler 2012; Gay and Hole 2005).** `SessionTy` with `dual`,
a labelled transition `SStep`, fidelity, and progress of two linked dual endpoints. The statements
are pairwise: there is no global type and no projection here, so multiparty deadlock freedom is not
claimed.
**Communication.** Tensor introduction/elimination and graded send/receive are term constructors.
`Rendezvous` transfers a payload between dual endpoints, retags their continuation slots,
and consumes both slots at close/wait. Typing, exact linear usage, and ghost erasure
are preserved, including delegation of a third live endpoint.

**Settlement.** A session endpoint is a linear capability; `Obend.Polis.CapTP` settles a promise at
most once. `sessionEvents` is the promise trace of one endpoint, and `session_capTP_settlement`
says it resolves exactly once when the session reached `endS` and not at all otherwise.
-/
public import Obend.Polis.CapTP
import all Obend.Polis.CapTP

public section
namespace Obend.Core.GradedSessionMetatheory
open Obend.Polis.CapTP
set_option autoImplicit false
/-! ## Resource rigs -/

/-- An ordered semiring of usage grades. `add_eq_zero` and `mul_eq_zero` are the two conditions
erasure needs (Atkey 2018, Definition 2.1): a sum or a product is `0` only when its parts are. -/
class ResourceRig (R : Type) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  le : R → R → Prop
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  zero_mul : ∀ a, mul zero a = zero
  mul_zero : ∀ a, mul a zero = zero
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  le_refl : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  add_le_add : ∀ a a' b b', le a a' → le b b' → le (add a b) (add a' b')
  mul_le_mul : ∀ a a' b b', le a a' → le b b' → le (mul a b) (mul a' b')
  add_eq_zero : ∀ a b, add a b = zero → a = zero ∧ b = zero
  mul_eq_zero : ∀ a b, mul a b = zero → a = zero ∨ b = zero
  le_zero : ∀ a, le a zero → a = zero
  one_ne_zero : one ≠ zero
local infixl:65 " ⊞ " => ResourceRig.add
local infixl:70 " ⊠ " => ResourceRig.mul
local infix:50 " ⊑ " => ResourceRig.le
local notation "𝟘" => ResourceRig.zero
local notation "𝟙" => ResourceRig.one

section Rig
variable {R : Type} [ResourceRig R]
theorem rig_add_zero (a : R) : a ⊞ 𝟘 = a := by
  rw [ResourceRig.add_comm]; exact ResourceRig.zero_add a

theorem rig_add_shuffle (a b c d : R) : (a ⊞ b) ⊞ (c ⊞ d) = (a ⊞ c) ⊞ (b ⊞ d) := by
  rw [ResourceRig.add_assoc a b (c ⊞ d), ← ResourceRig.add_assoc b c d, ResourceRig.add_comm b c,
    ResourceRig.add_assoc c b d, ← ResourceRig.add_assoc a c (b ⊞ d)]
/-- The pointwise identity behind substitution into an application. -/
theorem rig_subst_app (a b u v x π : R) :
    (a ⊞ π ⊠ b) ⊞ (u ⊞ π ⊠ v) ⊠ x = (a ⊞ u ⊠ x) ⊞ π ⊠ (b ⊞ v ⊠ x) := by
  rw [ResourceRig.right_distrib u (π ⊠ v) x, ResourceRig.mul_assoc π v x,
    ResourceRig.left_distrib π b (v ⊠ x)]
  exact rig_add_shuffle a (π ⊠ b) (u ⊠ x) (π ⊠ (v ⊠ x))

/-- The pointwise identity behind substitution into a conditional. -/
theorem rig_subst_ite (a b u v x : R) :
    (a ⊞ b) ⊞ (u ⊞ v) ⊠ x = (a ⊞ u ⊠ x) ⊞ (b ⊞ v ⊠ x) := by
  rw [ResourceRig.right_distrib u v x]
  exact rig_add_shuffle a b (u ⊠ x) (v ⊠ x)
end Rig

/-! ## The rig `0, 1, ω` -/
/-- `zero`: a ghost, erased at run time. `one`: a linear capability, used exactly once.
`omega`: an unrestricted value. -/
inductive ZeroOneOmega where
  | zero | one | omega
  deriving DecidableEq, Repr

def ZeroOneOmega.add : ZeroOneOmega → ZeroOneOmega → ZeroOneOmega
  | .zero, g => g
  | .one, .zero => .one
  | .one, .one => .omega
  | .one, .omega => .omega
  | .omega, _ => .omega
def ZeroOneOmega.mul : ZeroOneOmega → ZeroOneOmega → ZeroOneOmega
  | .zero, _ => .zero
  | .one, g => g
  | .omega, .zero => .zero
  | .omega, .one => .omega
  | .omega, .omega => .omega

/-- `a` uses fit an allowance of `b`: equal, or the allowance is unrestricted. `0 ⊑ 1` is absent:
a linear capability may not go unused. -/
def ZeroOneOmega.le (a b : ZeroOneOmega) : Prop := a = b ∨ b = .omega
instance (a b : ZeroOneOmega) : Decidable (ZeroOneOmega.le a b) :=
  inferInstanceAs (Decidable (a = b ∨ b = .omega))

instance : ResourceRig ZeroOneOmega where
  zero := .zero
  one := .one
  add := ZeroOneOmega.add
  mul := ZeroOneOmega.mul
  le := ZeroOneOmega.le
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; rfl
  zero_mul := by intro a; rfl
  mul_zero := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  le_refl := by intro a; exact .inl rfl
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  add_le_add := by intro a a' b b'; cases a <;> cases a' <;> cases b <;> cases b' <;> decide
  mul_le_mul := by intro a a' b b'; cases a <;> cases a' <;> cases b <;> cases b' <;> decide
  add_eq_zero := by intro a b; cases a <;> cases b <;> decide
  mul_eq_zero := by intro a b; cases a <;> cases b <;> decide
  le_zero := by intro a; cases a <;> decide
  one_ne_zero := by decide
@[simp] theorem ZeroOneOmega.rig_zero : (ResourceRig.zero : ZeroOneOmega) = .zero := by rfl
@[simp] theorem ZeroOneOmega.rig_one : (ResourceRig.one : ZeroOneOmega) = .one := by rfl
@[simp] theorem ZeroOneOmega.rig_add (a b : ZeroOneOmega) : ResourceRig.add a b = a.add b := by rfl
@[simp] theorem ZeroOneOmega.rig_mul (a b : ZeroOneOmega) : ResourceRig.mul a b = a.mul b := by rfl
@[simp] theorem ZeroOneOmega.rig_le (a b : ZeroOneOmega) : ResourceRig.le a b ↔ a.le b := Iff.rfl

/-- Weakening: an allowance admits zero uses only when it is `0` or `ω`. -/
theorem ZeroOneOmega.weakenable_iff (g : ZeroOneOmega) :
    ZeroOneOmega.le .zero g ↔ g = .zero ∨ g = .omega := by cases g <;> decide
/-- Contraction: two uses fit one allowance only at `0` (a ghost, which never runs) or `ω`. -/
theorem ZeroOneOmega.contractible_iff (g : ZeroOneOmega) :
    ZeroOneOmega.le (g.add g) g ↔ g = .zero ∨ g = .omega := by cases g <;> decide

/-- Context split: a linear resource goes to exactly one side of a sum. -/
theorem ZeroOneOmega.linear_split (a b : ZeroOneOmega) :
    a.add b = .one ↔ (a = .one ∧ b = .zero) ∨ (a = .zero ∧ b = .one) := by
  cases a <;> cases b <;> decide
/-- Nothing fits a linear allowance but exactly one use. -/
theorem ZeroOneOmega.le_one (g : ZeroOneOmega) : ZeroOneOmega.le g .one ↔ g = .one := by
  cases g <;> decide

/-! ## Types: functions and session-typed channels -/
mutual
/-- Types. `arr π A B` takes its argument at grade `π`; `chan S` is a channel endpoint at session
type `S`, held as a capability. -/
inductive Ty (R : Type) where
  | unit
  | bool
  | arr (π : R) (dom cod : Ty R)
  | tensor (q : R) (left right : Ty R)
  | chan (session : SessionTy R)
/-- Binary session types. -/
inductive SessionTy (R : Type) where
  | endS
  | send (q : R) (payload : Ty R) (cont : SessionTy R)
  | recv (q : R) (payload : Ty R) (cont : SessionTy R)
  | offer (branches : Branches R)
  | select (branches : Branches R)
/-- Labelled branches of a choice, in source order; the first of a label is the one taken. -/
inductive Branches (R : Type) where
  | nil
  | cons (label : String) (cont : SessionTy R) (rest : Branches R)
end

deriving instance DecidableEq for Ty, SessionTy, Branches

section Sessions
variable {R : Type}
mutual
def SessionTy.dual : SessionTy R → SessionTy R
  | .endS => .endS
  | .send q T S => .recv q T S.dual
  | .recv q T S => .send q T S.dual
  | .offer B => .select B.dual
  | .select B => .offer B.dual
def Branches.dual : Branches R → Branches R
  | .nil => .nil
  | .cons l S B => .cons l S.dual B.dual
end

mutual
theorem SessionTy.dual_dual : ∀ S : SessionTy R, S.dual.dual = S
  | .endS => by simp only [SessionTy.dual]
  | .send q T S => by simp only [SessionTy.dual, SessionTy.dual_dual S]
  | .recv q T S => by simp only [SessionTy.dual, SessionTy.dual_dual S]
  | .offer B => by simp only [SessionTy.dual, Branches.dual_dual B]
  | .select B => by simp only [SessionTy.dual, Branches.dual_dual B]
theorem Branches.dual_dual : ∀ B : Branches R, B.dual.dual = B
  | .nil => by simp only [Branches.dual]
  | .cons l S B => by simp only [Branches.dual, SessionTy.dual_dual S, Branches.dual_dual B]
end
def SessionTy.isEnd : SessionTy R → Bool
  | .endS => true
  | _ => false

theorem SessionTy.isEnd_dual (S : SessionTy R) : S.dual.isEnd = S.isEnd := by
  cases S <;> simp only [SessionTy.dual, SessionTy.isEnd]
def Branches.find : Branches R → String → Option (SessionTy R)
  | .nil, _ => none
  | .cons l S B, x => if l = x then some S else B.find x

theorem Branches.find_dual : ∀ (B : Branches R) (x : String) (S : SessionTy R),
    B.find x = some S → B.dual.find x = some S.dual
  | .nil, _, _, h => by simp [Branches.find] at h
  | .cons l S' B, x, S, h => by
    simp only [Branches.find] at h
    simp only [Branches.dual, Branches.find]
    by_cases hl : l = x
    · simp only [hl, ↓reduceIte, Option.some.injEq] at h ⊢
      rw [h]
    · simp only [hl, ↓reduceIte] at h ⊢
      exact Branches.find_dual B x S h
mutual
/-- Every choice has a branch. An empty `offer` facing an empty `select` is a pair that has not
ended and cannot move; this is the one shape progress has to exclude. -/
def SessionTy.WellFormed : SessionTy R → Prop
  | .endS => True
  | .send _ _ S => S.WellFormed
  | .recv _ _ S => S.WellFormed
  | .offer B => B ≠ .nil ∧ B.WellFormed
  | .select B => B ≠ .nil ∧ B.WellFormed
def Branches.WellFormed : Branches R → Prop
  | .nil => True
  | .cons _ S B => S.WellFormed ∧ B.WellFormed
end

theorem Branches.find_wellFormed : ∀ (B : Branches R) (x : String) (S : SessionTy R),
    B.WellFormed → B.find x = some S → S.WellFormed
  | .nil, _, _, _, h => by simp [Branches.find] at h
  | .cons l S' B, x, S, wf, h => by
    simp only [Branches.WellFormed] at wf
    simp only [Branches.find] at h
    by_cases hl : l = x
    · simp only [hl, ↓reduceIte, Option.some.injEq] at h
      rw [← h]; exact wf.1
    · simp only [hl, ↓reduceIte] at h
      exact Branches.find_wellFormed B x S wf.2 h
/-- What one endpoint does in one communication. -/
inductive Action (R : Type) where
  | send (q : R) (payload : Ty R)
  | recv (q : R) (payload : Ty R)
  | select (label : String)
  | offer (label : String)

/-- What the peer does in the same communication. -/
def Action.co : Action R → Action R
  | .send q T => .recv q T
  | .recv q T => .send q T
  | .select l => .offer l
  | .offer l => .select l
/-- One endpoint's transition. -/
inductive SStep : SessionTy R → Action R → SessionTy R → Prop where
  | send {q : R} {T : Ty R} {S : SessionTy R} : SStep (.send q T S) (.send q T) S
  | recv {q : R} {T : Ty R} {S : SessionTy R} : SStep (.recv q T S) (.recv q T) S
  | select {B : Branches R} {l : String} {S : SessionTy R} :
      B.find l = some S → SStep (.select B) (.select l) S
  | offer {B : Branches R} {l : String} {S : SessionTy R} :
      B.find l = some S → SStep (.offer B) (.offer l) S

theorem SStep.deterministic {S S₁ S₂ : SessionTy R} {a : Action R}
    (h₁ : SStep S a S₁) (h₂ : SStep S a S₂) : S₁ = S₂ := by
  cases h₁ with
  | send => cases h₂; rfl
  | recv => cases h₂; rfl
  | select f₁ => cases h₂ with | select f₂ => exact Option.some.inj (f₁.symm.trans f₂)
  | offer f₁ => cases h₂ with | offer f₂ => exact Option.some.inj (f₁.symm.trans f₂)
/-- Whatever one endpoint does, its dual can answer with the co-action, and the two stay dual. -/
theorem SStep.dual {S S' : SessionTy R} {a : Action R} (h : SStep S a S') :
    SStep S.dual a.co S'.dual := by
  cases h with
  | send => simp only [SessionTy.dual, Action.co]; exact .recv
  | recv => simp only [SessionTy.dual, Action.co]; exact .send
  | select f => simp only [SessionTy.dual, Action.co]; exact .offer (Branches.find_dual _ _ _ f)
  | offer f => simp only [SessionTy.dual, Action.co]; exact .select (Branches.find_dual _ _ _ f)

theorem SStep.wellFormed {S S' : SessionTy R} {a : Action R} (h : SStep S a S')
    (wf : S.WellFormed) : S'.WellFormed := by
  cases h with
  | send => simpa only [SessionTy.WellFormed] using wf
  | recv => simpa only [SessionTy.WellFormed] using wf
  | select f => simp only [SessionTy.WellFormed] at wf; exact Branches.find_wellFormed _ _ _ wf.2 f
  | offer f => simp only [SessionTy.WellFormed] at wf; exact Branches.find_wellFormed _ _ _ wf.2 f
/-- **Session fidelity.** Two linked endpoints that take a communication step together are still
linked: the peer's continuation is the dual of ours. -/
theorem session_step_preserves_duality {S T S' T' : SessionTy R} {a : Action R}
    (linked : T = S.dual) (ours : SStep S a S') (theirs : SStep T a.co T') : T' = S'.dual := by
  subst linked
  exact SStep.deterministic theirs ours.dual

/-- No type mismatch: what the peer of a sender expects to receive is what was sent. -/
theorem session_send_payload_agrees {S S' S'' : SessionTy R} {q q' : R} {T T' : Ty R}
    (ours : SStep S (.send q T) S') (theirs : SStep S.dual (.recv q' T') S'') : T' = T := by
  cases ours
  simp only [SessionTy.dual] at theirs
  cases theirs
  rfl
/-- A well-formed session type that has not ended can act. -/
theorem SessionTy.canStep : ∀ (S : SessionTy R), S.WellFormed →
    S.isEnd = true ∨ ∃ a S', SStep S a S'
  | .endS, _ => .inl (by simp only [SessionTy.isEnd])
  | .send q T S, _ => .inr ⟨.send q T, S, .send⟩
  | .recv q T S, _ => .inr ⟨.recv q T, S, .recv⟩
  | .offer .nil, wf => by simp [SessionTy.WellFormed] at wf
  | .select .nil, wf => by simp [SessionTy.WellFormed] at wf
  | .offer (.cons l S B), _ => .inr ⟨.offer l, S, .offer (by simp [Branches.find])⟩
  | .select (.cons l S B), _ => .inr ⟨.select l, S, .select (by simp [Branches.find])⟩

/-- **Pairwise progress.** Two linked dual endpoints of a well-formed session have either both
ended, or can take a communication step together after which they are again linked. Neither is
left holding a channel the other has closed. -/
theorem wellTyped_dual_endpoints_progress {S T : SessionTy R} (wf : S.WellFormed)
    (linked : T = S.dual) :
    (S.isEnd = true ∧ T.isEnd = true) ∨
      ∃ a S' T', SStep S a S' ∧ SStep T a.co T' ∧ T' = S'.dual := by
  subst linked
  rcases SessionTy.canStep S wf with ended | ⟨a, S', step⟩
  · exact .inl ⟨ended, by rw [SessionTy.isEnd_dual]; exact ended⟩
  · exact .inr ⟨a, S', S'.dual, step, step.dual, rfl⟩
/-- A run of communications of one endpoint. -/
inductive Trace : SessionTy R → List (Action R) → SessionTy R → Prop where
  | done (S : SessionTy R) : Trace S [] S
  | step {S S' S'' : SessionTy R} {a : Action R} {rest : List (Action R)} :
      SStep S a S' → Trace S' rest S'' → Trace S (a :: rest) S''

/-- A run exists: send a Boolean, then end. -/
example : Trace (SessionTy.send .one (.bool : Ty ZeroOneOmega) .endS) [.send .one .bool] .endS :=
  .step .send (.done _)
theorem Trace.dual {S S' : SessionTy R} {actions : List (Action R)} (h : Trace S actions S') :
    Trace S.dual (actions.map Action.co) S'.dual := by
  induction h with
  | done S => exact .done _
  | step s _ ih => exact .step s.dual ih

theorem Trace.deterministic {S S₁ S₂ : SessionTy R} {actions : List (Action R)}
    (h₁ : Trace S actions S₁) (h₂ : Trace S actions S₂) : S₁ = S₂ := by
  induction h₁ with
  | done S => cases h₂; rfl
  | step s _ ih =>
    cases h₂ with
    | step s' rest => cases SStep.deterministic s s'; exact ih rest
theorem Trace.wellFormed {S S' : SessionTy R} {actions : List (Action R)} (h : Trace S actions S')
    (wf : S.WellFormed) : S'.WellFormed := by
  induction h with
  | done S => exact wf
  | step s _ ih => exact ih (s.wellFormed wf)

/-- **Trace soundness.** Along any run, however long, two linked endpoints stay linked, and at
the state they reach they have both ended or can both move. -/
theorem session_trace_sound {S T S' T' : SessionTy R} {actions : List (Action R)}
    (wf : S.WellFormed) (linked : T = S.dual)
    (ours : Trace S actions S') (theirs : Trace T (actions.map Action.co) T') :
    T' = S'.dual ∧
      ((S'.isEnd = true ∧ T'.isEnd = true) ∨
        ∃ a S'' T'', SStep S' a S'' ∧ SStep T' a.co T'' ∧ T'' = S''.dual) := by
  subst linked
  have same : T' = S'.dual := Trace.deterministic theirs ours.dual
  exact ⟨same, wellTyped_dual_endpoints_progress (ours.wellFormed wf) same⟩
/-! ## The weld to CapTP: an endpoint settles its promise once -/

/-- The promise trace of one endpoint held under the pending id `k`: the promise is allocated,
each communication is a delivery that depends on it, and it is resolved when the session has
reached `endS`. An endpoint abandoned before `endS` never resolves. -/
def sessionEvents (k : PendingId) (actions : List (Action R)) (final : SessionTy R) :
    List PromiseEvent :=
  .allocate k :: (actions.map (fun _ => PromiseEvent.deliver k) ++
    (if final.isEnd then [PromiseEvent.resolve k] else []))
theorem countResolved_deliveries {α : Type} (s : GuardedHole) (k : PendingId) (xs : List α)
    (rest : List PromiseEvent) :
    countResolved s (xs.map (fun _ => PromiseEvent.deliver k) ++ rest) k = countResolved s rest k := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countResolved, promiseStep, ih]

theorem resolve_open (t : GuardedHole) (k : PendingId) (isOpen : t.openPromises.spec k)
    (unspent : ¬ t.spentNullifiers.spec k) : ∃ t', resolvePromise t k = some t' := by
  have h₁ : t.spentNullifiers.contains k = false := by
    cases hc : t.spentNullifiers.contains k with
    | false => rfl
    | true => exact absurd ((SortedU64Set.contains_eq_spec _ _).mp hc) unspent
  have h₂ : t.openPromises.contains k = true := (SortedU64Set.contains_eq_spec _ _).mpr isOpen
  simp [resolvePromise, h₁, h₂]
/-- **Settlement.** From a state where `k` is not spent, the endpoint's promise trace resolves
`k` once if the session ended and never if it did not. -/
theorem session_capTP_settlement (s : GuardedHole) (k : PendingId)
    (fresh : ¬ s.spentNullifiers.spec k) (actions : List (Action R)) (final : SessionTy R) :
    countResolved s (sessionEvents k actions final) k = if final.isEnd then 1 else 0 := by
  have unspent : s.spentNullifiers.contains k = false := by
    cases hc : s.spentNullifiers.contains k with
    | false => rfl
    | true => exact absurd ((SortedU64Set.contains_eq_spec _ _).mp hc) fresh
  have allocated : allocatePromise s k = { s with openPromises := s.openPromises.insert k } := by
    simp [allocatePromise, unspent]
  have head : countResolved s (sessionEvents k actions final) k =
      countResolved (allocatePromise s k) (if final.isEnd then [PromiseEvent.resolve k] else []) k := by
    simp only [sessionEvents, countResolved, promiseStep]
    rw [countResolved_deliveries]
    simp
  rw [head]
  cases final.isEnd with
  | false => rfl
  | true =>
    obtain ⟨t', resolved⟩ := resolve_open (allocatePromise s k) k
      (by rw [allocated]; exact (SortedU64Set.spec_insert _ _ _).mpr (.inl rfl))
      (by rw [allocated]; exact fresh)
    simp [countResolved, promiseStep, resolved]

/-- **No orphaned endpoint.** Both ends of a linked session settle their promises together: ours
resolves exactly once precisely when the peer's does. -/
theorem linked_endpoints_settle_together {S S' : SessionTy R} {actions : List (Action R)}
    (s s' : GuardedHole) (k k' : PendingId) (fresh : ¬ s.spentNullifiers.spec k)
    (fresh' : ¬ s'.spentNullifiers.spec k') (ours : Trace S actions S') :
    Trace S.dual (actions.map Action.co) S'.dual ∧
    (countResolved s (sessionEvents k actions S') k = 1 ↔
      countResolved s' (sessionEvents k' (actions.map Action.co) S'.dual) k' = 1) := by
  refine ⟨ours.dual, ?_⟩
  rw [session_capTP_settlement s k fresh, session_capTP_settlement s' k' fresh',
    SessionTy.isEnd_dual]
/-- A linear endpoint replayed or duplicated on the wire still settles at most once. -/
theorem session_capTP_at_most_once (s : GuardedHole) (k : PendingId) (actions : List (Action R))
    (final : SessionTy R) (replay : List PromiseEvent) :
    countResolved s (sessionEvents k actions final ++ replay) k ≤ 1 :=
  guardedHole_resolve_at_most_once s _ k

end Sessions
/-! ## Usages: graded contexts -/

/-- The grade a term assigns to each de Bruijn variable. With the type context this is the
graded context `Γ`; `Usage.add` is `Γ₁ + Γ₂` and `Usage.scale` is `π · Γ`. -/
abbrev Usage (R : Type) := Nat → R
namespace Usage
variable {R : Type} [ResourceRig R]

def zero : Usage R := fun _ => 𝟘
def add (U V : Usage R) : Usage R := fun n => U n ⊞ V n
def scale (π : R) (U : Usage R) : Usage R := fun n => π ⊠ U n
def single (i : Nat) : Usage R := fun n => if n = i then 𝟙 else 𝟘
def tail (U : Usage R) : Usage R := fun n => U (n + 1)
/-- A new variable at position `k`, used `ρ` times. -/
def insertAt (k : Nat) (ρ : R) (U : Usage R) : Usage R :=
  fun n => if n < k then U n else if n = k then ρ else U (n - 1)
/-- The variable at position `k` is gone. -/
def removeAt (k : Nat) (U : Usage R) : Usage R := fun n => if n < k then U n else U (n + 1)
def le (U V : Usage R) : Prop := ∀ n, U n ⊑ V n
theorem insertAt_zero (k : Nat) : insertAt k 𝟘 (zero : Usage R) = zero := by
  funext n
  by_cases h₁ : n < k <;> by_cases h₂ : n = k <;> simp [insertAt, zero, h₁, h₂]

theorem insertAt_single_lt {i k : Nat} (h : i < k) :
    insertAt k 𝟘 (single i : Usage R) = single i := by
  funext n
  by_cases h₁ : n < k
  · simp [insertAt, single, h₁]
  · by_cases h₂ : n = k
    · subst h₂
      have ne : ¬ n = i := by omega
      simp [insertAt, single, ne]
    · have ne : ¬ n = i := by omega
      have ne' : ¬ n - 1 = i := by omega
      simp [insertAt, single, h₁, h₂, ne, ne']
theorem insertAt_single_ge {i k : Nat} (h : k ≤ i) :
    insertAt k 𝟘 (single i : Usage R) = single (i + 1) := by
  funext n
  by_cases h₁ : n < k
  · have ne : ¬ n = i := by omega
    have ne' : ¬ n = i + 1 := by omega
    simp [insertAt, single, h₁, ne, ne']
  · by_cases h₂ : n = k
    · subst h₂
      have ne' : ¬ n = i + 1 := by omega
      simp [insertAt, single, ne']
    · by_cases h₃ : n = i + 1
      · subst h₃
        have a : ¬ i + 1 < k := by omega
        have b : ¬ i + 1 = k := by omega
        simp [insertAt, single, a, b]
      · have ne : ¬ n - 1 = i := by omega
        simp [insertAt, single, h₁, h₂, h₃, ne]

theorem insertAt_add (k : Nat) (U V : Usage R) :
    insertAt k 𝟘 (add U V) = add (insertAt k 𝟘 U) (insertAt k 𝟘 V) := by
  funext n
  by_cases h₁ : n < k
  · simp [insertAt, add, h₁]
  · by_cases h₂ : n = k
    · simp [insertAt, add, h₂, ResourceRig.zero_add]
    · simp [insertAt, add, h₁, h₂]
theorem insertAt_scale (k : Nat) (π : R) (U : Usage R) :
    insertAt k 𝟘 (scale π U) = scale π (insertAt k 𝟘 U) := by
  funext n
  by_cases h₁ : n < k
  · simp [insertAt, scale, h₁]
  · by_cases h₂ : n = k
    · simp [insertAt, scale, h₂, ResourceRig.mul_zero]
    · simp [insertAt, scale, h₁, h₂]

omit [ResourceRig R] in
theorem tail_insertAt_succ (k : Nat) (ρ : R) (W : Usage R) :
    tail (insertAt (k + 1) ρ W) = insertAt k ρ (tail W) := by
  funext n
  by_cases h₁ : n < k
  · simp [tail, insertAt, h₁]
  · by_cases h₂ : n = k
    · simp [tail, insertAt, h₂]
    · have e : n - 1 + 1 = n := by omega
      simp [tail, insertAt, h₁, h₂, e]
omit [ResourceRig R] in
theorem insertAt_succ_head (k : Nat) (ρ : R) (W : Usage R) : insertAt (k + 1) ρ W 0 = W 0 := by
  simp [insertAt]

theorem insertAt_le (k : Nat) {U V : Usage R} (h : le U V) :
    le (insertAt k 𝟘 U) (insertAt k 𝟘 V) := by
  intro n
  by_cases h₁ : n < k
  · simpa [insertAt, h₁] using h n
  · by_cases h₂ : n = k
    · simpa [insertAt, h₂] using ResourceRig.le_refl (𝟘 : R)
    · simpa [insertAt, h₁, h₂] using h (n - 1)
theorem subst_zero (k : Nat) (V : Usage R) :
    add (removeAt k zero) (scale ((zero : Usage R) k) V) = zero := by
  funext n
  simp [add, removeAt, scale, zero, ResourceRig.zero_mul, ResourceRig.zero_add]

theorem subst_single_lt {i k : Nat} (h : i < k) (V : Usage R) :
    add (removeAt k (single i)) (scale ((single i : Usage R) k) V) = single i := by
  funext n
  have nk : ¬ k = i := by omega
  by_cases h₁ : n < k
  · simp [add, removeAt, scale, single, h₁, nk, ResourceRig.zero_mul, rig_add_zero]
  · have ne : ¬ n + 1 = i := by omega
    have ne' : ¬ n = i := by omega
    simp [add, removeAt, scale, single, h₁, nk, ne, ne', ResourceRig.zero_mul, rig_add_zero]
theorem subst_single_eq (k : Nat) (V : Usage R) :
    add (removeAt k (single k)) (scale ((single k : Usage R) k) V) = V := by
  funext n
  by_cases h₁ : n < k
  · have ne : ¬ n = k := by omega
    simp [add, removeAt, scale, single, h₁, ne, ResourceRig.one_mul, ResourceRig.zero_add]
  · have ne : ¬ n + 1 = k := by omega
    simp [add, removeAt, scale, single, h₁, ne, ResourceRig.one_mul, ResourceRig.zero_add]

theorem subst_single_gt {j k : Nat} (h : k ≤ j) (V : Usage R) :
    add (removeAt k (single (j + 1))) (scale ((single (j + 1) : Usage R) k) V) = single j := by
  funext n
  have nk : ¬ k = j + 1 := by omega
  by_cases h₁ : n < k
  · have ne : ¬ n = j + 1 := by omega
    have ne' : ¬ n = j := by omega
    simp [add, removeAt, scale, single, h₁, nk, ne, ne', ResourceRig.zero_mul, rig_add_zero]
  · simp [add, removeAt, scale, single, h₁, nk, ResourceRig.zero_mul, rig_add_zero]
theorem subst_lam_head (k : Nat) (W V : Usage R) :
    add (removeAt (k + 1) W) (scale (W (k + 1)) (insertAt 0 𝟘 V)) 0 = W 0 := by
  simp [add, removeAt, scale, insertAt, ResourceRig.mul_zero, rig_add_zero]

theorem subst_lam_tail (k : Nat) (W V : Usage R) :
    tail (add (removeAt (k + 1) W) (scale (W (k + 1)) (insertAt 0 𝟘 V))) =
      add (removeAt k (tail W)) (scale (tail W k) V) := by
  funext n
  simp [tail, add, removeAt, scale, insertAt]
theorem subst_app (k : Nat) (π : R) (U V₂ V : Usage R) :
    add (removeAt k (add U (scale π V₂))) (scale (add U (scale π V₂) k) V) =
      add (add (removeAt k U) (scale (U k) V))
        (scale π (add (removeAt k V₂) (scale (V₂ k) V))) := by
  funext n
  by_cases h₁ : n < k
  · simp only [add, removeAt, scale, h₁, ↓reduceIte]; exact rig_subst_app _ _ _ _ _ _
  · simp only [add, removeAt, scale, h₁, ↓reduceIte]; exact rig_subst_app _ _ _ _ _ _

theorem subst_ite (k : Nat) (U V₂ V : Usage R) :
    add (removeAt k (add U V₂)) (scale (add U V₂ k) V) =
      add (add (removeAt k U) (scale (U k) V)) (add (removeAt k V₂) (scale (V₂ k) V)) := by
  funext n
  by_cases h₁ : n < k
  · simp only [add, removeAt, scale, h₁, ↓reduceIte]; exact rig_subst_ite _ _ _ _ _
  · simp only [add, removeAt, scale, h₁, ↓reduceIte]; exact rig_subst_ite _ _ _ _ _
theorem subst_le (k : Nat) (V : Usage R) {W W' : Usage R} (h : le W W') :
    le (add (removeAt k W) (scale (W k) V)) (add (removeAt k W') (scale (W' k) V)) := by
  intro n
  have left : removeAt k W n ⊑ removeAt k W' n := by
    by_cases h₁ : n < k
    · simpa [removeAt, h₁] using h n
    · simpa [removeAt, h₁] using h (n + 1)
  exact ResourceRig.add_le_add _ _ _ _ left
    (ResourceRig.mul_le_mul _ _ _ _ (h k) (ResourceRig.le_refl _))

/-- A β-step may only lower the usage: the body used its binder `W 0 ⊑ π` times. -/
theorem beta_le {W U V : Usage R} {π : R} (fits : W 0 ⊑ π) (body : le (tail W) U) :
    le (add (removeAt 0 W) (scale (W 0) V)) (add U (scale π V)) := by
  intro n
  have e : removeAt 0 W n = W (n + 1) := by simp [removeAt]
  have left : removeAt 0 W n ⊑ U n := by rw [e]; exact body n
  exact ResourceRig.add_le_add _ _ _ _ left
    (ResourceRig.mul_le_mul _ _ _ _ fits (ResourceRig.le_refl _))
theorem le_add_of_zero_le {U V : Usage R} (h : le zero U) : le V (add U V) := by
  intro n
  have := ResourceRig.add_le_add _ _ _ _ (h n) (ResourceRig.le_refl (V n))
  simpa only [zero, add, ResourceRig.zero_add] using this

end Usage
/-! ## Terms, typing, reduction -/

/-- Terms, de Bruijn. An application records the grade of its argument, which is what erasure
reads. `ghost` is what an erased argument leaves behind; no typing rule types it. -/
inductive Tm (R : Type) where
  | var (index : Nat)
  | unit
  | bool (value : Bool)
  | lam (π : R) (dom : Ty R) (body : Tm R)
  | app (π : R) (fn arg : Tm R)
  | ite (cond thenB elseB : Tm R)
  | ghost
  | pair (q : R) (payload continuation : Tm R)
  /-- The consumer is a curried linear continuation, binding payload at q and channel at 1. -/
  | letPair (q : R) (consumer pair : Tm R)
  | send (q : R) (channel payload : Tm R)
  | recv (channel : Tm R)
  | close (channel : Tm R)
  | wait (channel : Tm R)
section Terms
variable {R : Type}

def Tm.shift : Tm R → Nat → Tm R
  | .var i, k => .var (if i < k then i else i + 1)
  | .lam π A b, k => .lam π A (b.shift (k + 1))
  | .app π f a, k => .app π (f.shift k) (a.shift k)
  | .ite c t e, k => .ite (c.shift k) (t.shift k) (e.shift k)
  | .unit, _ => .unit
  | .bool b, _ => .bool b
  | .ghost, _ => .ghost
  | .pair q a b, k => .pair q (a.shift k) (b.shift k)
  | .letPair q a b, k => .letPair q (a.shift k) (b.shift k)
  | .send q a b, k => .send q (a.shift k) (b.shift k)
  | .recv a, k => .recv (a.shift k)
  | .close a, k => .close (a.shift k)
  | .wait a, k => .wait (a.shift k)
/-- `t.subst k s`: `s` for variable `k`, the variables above `k` moved down. -/
def Tm.subst : Tm R → Nat → Tm R → Tm R
  | .var i, k, s => if i < k then .var i else if i = k then s else .var (i - 1)
  | .lam π A b, k, s => .lam π A (b.subst (k + 1) (s.shift 0))
  | .app π f a, k, s => .app π (f.subst k s) (a.subst k s)
  | .ite c t e, k, s => .ite (c.subst k s) (t.subst k s) (e.subst k s)
  | .unit, _, _ => .unit
  | .bool b, _, _ => .bool b
  | .ghost, _, _ => .ghost
  | .pair q a b, k, s => .pair q (a.subst k s) (b.subst k s)
  | .letPair q a b, k, s => .letPair q (a.subst k s) (b.subst k s)
  | .send q a b, k, s => .send q (a.subst k s) (b.subst k s)
  | .recv a, k, s => .recv (a.subst k s)
  | .close a, k, s => .close (a.subst k s)
  | .wait a, k, s => .wait (a.subst k s)

variable [ResourceRig R]
/-- Weak head reduction. -/
inductive Step : Tm R → Tm R → Prop where
  | beta {π π' : R} {A : Ty R} {b a : Tm R} : Step (.app π (.lam π' A b) a) (b.subst 0 a)
  | appFun {π : R} {f f' a : Tm R} : Step f f' → Step (.app π f a) (.app π f' a)
  | iteCond {c c' t e : Tm R} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | iteTrue {t e : Tm R} : Step (.ite (.bool true) t e) t
  | iteFalse {t e : Tm R} : Step (.ite (.bool false) t e) e
  | pairBeta {q : R} {f a b : Tm R} :
      Step (.letPair q f (.pair q a b)) (.app 𝟙 (.app q f a) b)

inductive Steps : Tm R → Tm R → Prop where
  | refl (t : Tm R) : Steps t t
  | head {t t' t'' : Tm R} : Step t t' → Steps t' t'' → Steps t t''

/-- `HasTy Γ t A U`: in the type context `Γ` the term `t` has type `A` and uses the variables as
`U` says. `sub` relaxes a usage upward in the rig's order. -/
inductive HasTy : List (Ty R) → Tm R → Ty R → Usage R → Prop where
  | var {Γ : List (Ty R)} {i : Nat} {A : Ty R} : Γ[i]? = some A → HasTy Γ (.var i) A (Usage.single i)
  | unit {Γ : List (Ty R)} : HasTy Γ .unit .unit Usage.zero
  | bool {Γ : List (Ty R)} {v : Bool} : HasTy Γ (.bool v) .bool Usage.zero
  | lam {Γ : List (Ty R)} {π : R} {A B : Ty R} {b : Tm R} {W : Usage R} :
      HasTy (A :: Γ) b B W → W 0 ⊑ π → HasTy Γ (.lam π A b) (.arr π A B) (Usage.tail W)
  | app {Γ : List (Ty R)} {π : R} {A B : Ty R} {f a : Tm R} {U V : Usage R} :
      HasTy Γ f (.arr π A B) U → HasTy Γ a A V →
      HasTy Γ (.app π f a) B (Usage.add U (Usage.scale π V))
  | ite {Γ : List (Ty R)} {A : Ty R} {c t e : Tm R} {U V : Usage R} :
      HasTy Γ c .bool U → HasTy Γ t A V → HasTy Γ e A V →
      HasTy Γ (.ite c t e) A (Usage.add U V)
  | pair {Γ : List (Ty R)} {q : R} {A B : Ty R} {a b : Tm R} {U V : Usage R} :
      HasTy Γ b B U → HasTy Γ a A V →
      HasTy Γ (.pair q a b) (.tensor q A B) (Usage.add U (Usage.scale q V))
  | letPair {Γ : List (Ty R)} {q : R} {A B C : Ty R} {f p : Tm R} {U V : Usage R} :
      HasTy Γ f (.arr q A (.arr 𝟙 B C)) U → HasTy Γ p (.tensor q A B) V →
      HasTy Γ (.letPair q f p) C (Usage.add U V)
  | send {Γ : List (Ty R)} {q : R} {A : Ty R} {S : SessionTy R} {c a : Tm R} {U V : Usage R} :
      HasTy Γ c (.chan (.send q A S)) U → HasTy Γ a A V →
      HasTy Γ (.send q c a) (.chan S) (Usage.add U (Usage.scale q V))
  | recv {Γ : List (Ty R)} {q : R} {A : Ty R} {S : SessionTy R} {c : Tm R} {U : Usage R} :
      HasTy Γ c (.chan (.recv q A S)) U → HasTy Γ (.recv c) (.tensor q A (.chan S)) U
  | close {Γ : List (Ty R)} {c : Tm R} {U : Usage R} :
      HasTy Γ c (.chan .endS) U → HasTy Γ (.close c) .unit U
  | wait {Γ : List (Ty R)} {c : Tm R} {U : Usage R} :
      HasTy Γ c (.chan .endS) U → HasTy Γ (.wait c) .unit U
  | sub {Γ : List (Ty R)} {t : Tm R} {A : Ty R} {U U' : Usage R} :
      HasTy Γ t A U → Usage.le U U' → HasTy Γ t A U'
/-- The judgment is inhabited: `fun (x :¹ bool) => if x then () else ()` reads its linear
argument once, in the condition. -/
example : HasTy ([] : List (Ty ZeroOneOmega)) (.lam .one .bool (.ite (.var 0) .unit .unit))
    (.arr .one .bool .unit) (Usage.tail (Usage.add (Usage.single 0) Usage.zero)) :=
  .lam (.ite (.var (by simp)) .unit .unit)
    (by simp [Usage.add, Usage.single, Usage.zero, ZeroOneOmega.add, ZeroOneOmega.le])

/-- Reduction is inhabited: a conditional on `true` takes its first branch. -/
example : Steps (Tm.ite (.bool true) .unit (.bool false) : Tm ZeroOneOmega) .unit :=
  .head .iteTrue (.refl _)
/-! ### Context lookups around an inserted binding -/

theorem lookup_insert_lt {α : Type} : ∀ (Γ₁ Γ₂ : List α) (C : α) (i : Nat), i < Γ₁.length →
    (Γ₁ ++ C :: Γ₂)[i]? = (Γ₁ ++ Γ₂)[i]?
  | [], _, _, _, h => by simp at h
  | _ :: _, _, _, 0, _ => by simp
  | _ :: Γ₁, Γ₂, C, i + 1, h => by
    simpa using lookup_insert_lt Γ₁ Γ₂ C i (by simpa using h)
theorem lookup_insert_eq {α : Type} : ∀ (Γ₁ Γ₂ : List α) (C : α),
    (Γ₁ ++ C :: Γ₂)[Γ₁.length]? = some C
  | [], _, _ => by simp
  | _ :: Γ₁, Γ₂, C => by simp

theorem lookup_insert_ge {α : Type} : ∀ (Γ₁ Γ₂ : List α) (C : α) (i : Nat), Γ₁.length ≤ i →
    (Γ₁ ++ C :: Γ₂)[i + 1]? = (Γ₁ ++ Γ₂)[i]?
  | [], _, _, _, _ => by simp
  | _ :: _, _, _, 0, h => by simp at h
  | _ :: Γ₁, Γ₂, C, i + 1, h => by
    simpa using lookup_insert_ge Γ₁ Γ₂ C i (by simpa using h)
/-! ### Weakening by an unused binding -/

/-- A binding nobody uses may be inserted anywhere, at grade `0`. -/
theorem HasTy.weaken {Γ₁ Γ₂ : List (Ty R)} {t : Tm R} {A : Ty R} {U : Usage R} (C : Ty R)
    (h : HasTy (Γ₁ ++ Γ₂) t A U) :
    HasTy (Γ₁ ++ C :: Γ₂) (t.shift Γ₁.length) A (Usage.insertAt Γ₁.length 𝟘 U) := by
  generalize hΓ : Γ₁ ++ Γ₂ = Γ at h
  induction h generalizing Γ₁ with
  | @var Γ i T found =>
    subst hΓ
    by_cases hi : i < Γ₁.length
    · have e : (Tm.var i : Tm R).shift Γ₁.length = .var i := by simp [Tm.shift, hi]
      rw [e, Usage.insertAt_single_lt hi]
      exact .var (by rw [lookup_insert_lt _ _ _ _ hi]; exact found)
    · have hk : Γ₁.length ≤ i := Nat.le_of_not_lt hi
      have e : (Tm.var i : Tm R).shift Γ₁.length = .var (i + 1) := by simp [Tm.shift, hi]
      rw [e, Usage.insertAt_single_ge hk]
      exact .var (by rw [lookup_insert_ge _ _ _ _ hk]; exact found)
  | unit => simp only [Tm.shift]; rw [Usage.insertAt_zero]; exact .unit
  | bool => simp only [Tm.shift]; rw [Usage.insertAt_zero]; exact .bool
  | @lam Γ π T B b W _ fits ih =>
    subst hΓ
    simp only [Tm.shift]
    have body : HasTy (T :: (Γ₁ ++ C :: Γ₂)) (b.shift (Γ₁.length + 1)) B
        (Usage.insertAt (Γ₁.length + 1) 𝟘 W) := ih (Γ₁ := T :: Γ₁) rfl
    have typed := HasTy.lam (π := π) body (by rw [Usage.insertAt_succ_head]; exact fits)
    rw [Usage.tail_insertAt_succ] at typed
    exact typed
  | @app Γ π T B f a U V _ _ ihf iha =>
    subst hΓ
    simp only [Tm.shift]
    rw [Usage.insertAt_add, Usage.insertAt_scale]
    exact .app (ihf rfl) (iha rfl)
  | @ite Γ T c t e U V _ _ _ ihc iht ihe =>
    subst hΓ
    simp only [Tm.shift]
    rw [Usage.insertAt_add]
    exact .ite (ihc rfl) (iht rfl) (ihe rfl)
  | @pair Γ q A B a b U V _ _ ihf iha =>
    subst hΓ
    simp only [Tm.shift]
    rw [Usage.insertAt_add, Usage.insertAt_scale]
    exact .pair (ihf rfl) (iha rfl)
  | @send Γ q A S c a U V _ _ ihf iha =>
    subst hΓ
    simp only [Tm.shift]
    rw [Usage.insertAt_add, Usage.insertAt_scale]
    exact .send (ihf rfl) (iha rfl)
  | @letPair Γ q A B C f p U V _ _ ihf iha =>
    subst hΓ
    simp only [Tm.shift]
    rw [Usage.insertAt_add]
    exact .letPair (ihf rfl) (iha rfl)
  | recv _ ih =>
    subst hΓ
    exact .recv (ih rfl)
  | close _ ih =>
    subst hΓ
    exact .close (ih rfl)
  | wait _ ih =>
    subst hΓ
    exact .wait (ih rfl)
  | @sub Γ t T U U' _ relaxed ih =>
    subst hΓ
    exact .sub (ih rfl) (Usage.insertAt_le _ relaxed)
/-! ### The substitution lemma -/

/-- **Quantitative substitution.** If `t` uses the variable at position `k` with grade `π = W k`
and `s` has usage `V`, then `t[s]` has usage `W` without `k`, plus `π · V`: the context of the
result is `Γ + π · Δ`. -/
theorem qtt_subst_preserves_grades {Γ₁ Γ₂ : List (Ty R)} {A B : Ty R} {t s : Tm R}
    {W V : Usage R} (typed : HasTy (Γ₁ ++ A :: Γ₂) t B W) (arg : HasTy (Γ₁ ++ Γ₂) s A V) :
    HasTy (Γ₁ ++ Γ₂) (t.subst Γ₁.length s) B
      (Usage.add (Usage.removeAt Γ₁.length W) (Usage.scale (W Γ₁.length) V)) := by
  generalize hΓ : Γ₁ ++ A :: Γ₂ = Γ at typed
  induction typed generalizing Γ₁ s V with
  | @var Γ i T found =>
    subst hΓ
    by_cases h₁ : i < Γ₁.length
    · have e : (Tm.var i : Tm R).subst Γ₁.length s = .var i := by simp [Tm.subst, h₁]
      rw [e, Usage.subst_single_lt h₁]
      exact .var (by rw [← lookup_insert_lt _ _ A _ h₁]; exact found)
    · by_cases h₂ : i = Γ₁.length
      · subst h₂
        have e : (Tm.var Γ₁.length : Tm R).subst Γ₁.length s = s := by simp [Tm.subst]
        rw [e, Usage.subst_single_eq]
        rw [lookup_insert_eq] at found
        cases Option.some.inj found
        exact arg
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hk : Γ₁.length ≤ j := by omega
        have e : (Tm.var (j + 1) : Tm R).subst Γ₁.length s = .var j := by
          simp [Tm.subst, h₁, h₂]
        rw [e, Usage.subst_single_gt hk]
        exact .var (by rw [← lookup_insert_ge _ _ A _ hk]; exact found)
  | unit => simp only [Tm.subst]; rw [Usage.subst_zero]; exact .unit
  | bool => simp only [Tm.subst]; rw [Usage.subst_zero]; exact .bool
  | @lam Γ π T B' b W' _ fits ih =>
    subst hΓ
    simp only [Tm.subst]
    have arg' : HasTy ((T :: Γ₁) ++ Γ₂) (s.shift 0) A (Usage.insertAt 0 𝟘 V) :=
      HasTy.weaken (Γ₁ := []) (Γ₂ := Γ₁ ++ Γ₂) T arg
    have body : HasTy (T :: (Γ₁ ++ Γ₂)) (b.subst (Γ₁.length + 1) (s.shift 0)) B'
        (Usage.add (Usage.removeAt (Γ₁.length + 1) W')
          (Usage.scale (W' (Γ₁.length + 1)) (Usage.insertAt 0 𝟘 V))) :=
      ih (Γ₁ := T :: Γ₁) arg' rfl
    have typed := HasTy.lam (π := π) body (by rw [Usage.subst_lam_head]; exact fits)
    rw [Usage.subst_lam_tail] at typed
    exact typed
  | @app Γ π T B' f a U V₂ _ _ ihf iha =>
    subst hΓ
    simp only [Tm.subst]
    rw [Usage.subst_app]
    exact .app (ihf arg rfl) (iha arg rfl)
  | @ite Γ T c t e U V₂ _ _ _ ihc iht ihe =>
    subst hΓ
    simp only [Tm.subst]
    rw [Usage.subst_ite]
    exact .ite (ihc arg rfl) (iht arg rfl) (ihe arg rfl)
  | @pair Γ q A B a b U V _ _ ihf iha =>
    subst hΓ
    simp only [Tm.subst]
    rw [Usage.subst_app]
    exact .pair (ihf arg rfl) (iha arg rfl)
  | @send Γ q A S c a U V _ _ ihf iha =>
    subst hΓ
    simp only [Tm.subst]
    rw [Usage.subst_app]
    exact .send (ihf arg rfl) (iha arg rfl)
  | @letPair Γ q A B C f p U V _ _ ihf iha =>
    subst hΓ
    simp only [Tm.subst]
    rw [Usage.subst_ite]
    exact .letPair (ihf arg rfl) (iha arg rfl)
  | recv _ ih =>
    subst hΓ
    exact .recv (ih arg rfl)
  | close _ ih =>
    subst hΓ
    exact .close (ih arg rfl)
  | wait _ ih =>
    subst hΓ
    exact .wait (ih arg rfl)
  | @sub Γ t T U U' _ relaxed ih =>
    subst hΓ
    exact .sub (ih arg rfl) (Usage.subst_le _ _ relaxed)
/-! ### Inversion and subject reduction -/

theorem HasTy.lam_inv {Γ : List (Ty R)} {π : R} {A T : Ty R} {b : Tm R} {U : Usage R}
    (h : HasTy Γ (.lam π A b) T U) :
    ∃ B W, T = .arr π A B ∧ HasTy (A :: Γ) b B W ∧ W 0 ⊑ π ∧ Usage.le (Usage.tail W) U := by
  generalize ht : Tm.lam π A b = t at h
  induction h with
  | @lam Γ π' A' B b' W body fits _ =>
    cases ht
    exact ⟨B, W, rfl, body, fits, fun n => ResourceRig.le_refl _⟩
  | @sub Γ t T U U' _ relaxed ih =>
    obtain ⟨B, W, e, body, fits, below⟩ := ih ht
    exact ⟨B, W, e, body, fits, fun n => ResourceRig.le_trans _ _ _ (below n) (relaxed n)⟩
  | var => cases ht
  | unit => cases ht
  | bool => cases ht
  | app => cases ht
  | ite => cases ht
  | pair => cases ht
  | letPair => cases ht
  | send => cases ht
  | recv => cases ht
  | close => cases ht
  | wait => cases ht
theorem HasTy.bool_inv {Γ : List (Ty R)} {v : Bool} {T : Ty R} {U : Usage R}
    (h : HasTy Γ (.bool v) T U) : T = .bool ∧ Usage.le Usage.zero U := by
  generalize ht : Tm.bool v = t at h
  induction h with
  | bool => exact ⟨rfl, fun n => ResourceRig.le_refl _⟩
  | @sub Γ t T U U' _ relaxed ih =>
    obtain ⟨e, below⟩ := ih ht
    exact ⟨e, fun n => ResourceRig.le_trans _ _ _ (below n) (relaxed n)⟩
  | var => cases ht
  | unit => cases ht
  | lam => cases ht
  | app => cases ht
  | ite => cases ht
  | pair => cases ht
  | letPair => cases ht
  | send => cases ht
  | recv => cases ht
  | close => cases ht
  | wait => cases ht

theorem HasTy.pair_inv {Γ : List (Ty R)} {q : R} {a b : Tm R} {T : Ty R} {W : Usage R}
    (h : HasTy Γ (.pair q a b) T W) :
    ∃ A B U V, T = .tensor q A B ∧ HasTy Γ b B U ∧ HasTy Γ a A V ∧
      Usage.le (Usage.add U (Usage.scale q V)) W := by
  generalize ht : Tm.pair q a b = t at h
  induction h with
  | @pair Γ q' A B a' b' U V hb ha _ _ =>
    cases ht
    exact ⟨A, B, U, V, rfl, hb, ha, fun _ => ResourceRig.le_refl _⟩
  | sub _ relaxed ih =>
    obtain ⟨A, B, U, V, eq, hb, ha, le⟩ := ih ht
    exact ⟨A, B, U, V, eq, hb, ha, fun n => ResourceRig.le_trans _ _ _ (le n) (relaxed n)⟩
  | var => cases ht
  | unit => cases ht
  | bool => cases ht
  | lam => cases ht
  | app => cases ht
  | ite => cases ht
  | letPair => cases ht
  | send => cases ht
  | recv => cases ht
  | close => cases ht
  | wait => cases ht
/-- **Subject reduction.** A step keeps the type and the usage: no variable is used more after
the step than the typing allowed before it. -/
theorem HasTy.step {Γ : List (Ty R)} {t t' : Tm R} {A : Ty R} {U : Usage R}
    (h : HasTy Γ t A U) (s : Step t t') : HasTy Γ t' A U := by
  induction h generalizing t' with
  | @app Γ π T B f a U V hf ha ihf _ =>
    cases s with
    | beta =>
      obtain ⟨B', W, e, body, fits, below⟩ := hf.lam_inv
      obtain ⟨e₁, e₂, e₃⟩ := Ty.arr.inj e
      subst e₁ e₂ e₃
      exact .sub (qtt_subst_preserves_grades (Γ₁ := []) body ha) (Usage.beta_le fits below)
    | appFun s' => exact .app (ihf s') ha
  | @ite Γ T c t e U V hc ht he ihc _ _ =>
    cases s with
    | iteCond s' => exact .ite (ihc s') ht he
    | iteTrue => exact .sub ht (Usage.le_add_of_zero_le hc.bool_inv.2)
    | iteFalse => exact .sub he (Usage.le_add_of_zero_le hc.bool_inv.2)
  | @letPair Γ q A B C f p U V hf hp _ _ =>
    cases s with
    | pairBeta =>
      obtain ⟨A', B', X, Y, eq, hb, ha, le⟩ := hp.pair_inv
      obtain ⟨_, ea, eb⟩ := Ty.tensor.inj eq
      cases ea; cases eb
      apply HasTy.sub (.app (.app hf ha) hb)
      intro n
      have hle := ResourceRig.add_le_add _ _ _ _ (ResourceRig.le_refl (U n)) (le n)
      simpa only [Usage.add, Usage.scale, ResourceRig.one_mul, ResourceRig.add_assoc,
        ResourceRig.add_comm (X n) (q ⊠ Y n)] using hle
  | pair => cases s
  | send => cases s
  | recv => cases s
  | close => cases s
  | wait => cases s
  | @sub Γ t T U U' _ relaxed ih => exact .sub (ih s) relaxed
  | var => cases s
  | unit => cases s
  | bool => cases s
  | lam => cases s

theorem HasTy.steps {Γ : List (Ty R)} {t t' : Tm R} {A : Ty R} {U : Usage R}
    (h : HasTy Γ t A U) (s : Steps t t') : HasTy Γ t' A U := by
  induction s with
  | refl => exact h
  | head first _ ih => exact ih (h.step first)
/-! ### Erasure -/

variable [DecidableEq R]
/-- An argument at grade `0` does not exist at run time. -/
def erasable (π : R) : Bool := decide (π = 𝟘)

/-- The run-time term: every `0`-graded argument replaced by `ghost`. -/
def Tm.erase : Tm R → Tm R
  | .lam π A b => .lam π A b.erase
  | .app π f a => if erasable π then .app π f.erase .ghost else .app π f.erase a.erase
  | .ite c t e => .ite c.erase t.erase e.erase
  | .var i => .var i
  | .unit => .unit
  | .bool b => .bool b
  | .ghost => .ghost
  | .pair q a b => if erasable q then .pair q .ghost b.erase else .pair q a.erase b.erase
  | .letPair q f p => .letPair q f.erase p.erase
  | .send q c a => if erasable q then .send q c.erase .ghost else .send q c.erase a.erase
  | .recv c => .recv c.erase
  | .close c => .close c.erase
  | .wait c => .wait c.erase
theorem erasable_iff (π : R) : erasable π = true ↔ π = 𝟘 := by simp [erasable]

theorem Tm.erase_shift (t : Tm R) : ∀ k, (t.shift k).erase = t.erase.shift k := by
  induction t with
  | lam π A b ih => intro k; simp [Tm.shift, Tm.erase, ih]
  | app π f a ihf iha =>
    intro k
    by_cases h : erasable π = true <;> simp [Tm.shift, Tm.erase, h, ihf, iha]
  | ite c t e ihc iht ihe => intro k; simp [Tm.shift, Tm.erase, ihc, iht, ihe]
  | var i => intro k; simp [Tm.shift, Tm.erase]
  | unit => intro k; simp [Tm.shift, Tm.erase]
  | bool b => intro k; simp [Tm.shift, Tm.erase]
  | ghost => intro k; simp [Tm.shift, Tm.erase]
  | pair q a b iha ihb =>
    intro k
    by_cases h : erasable q = true <;> simp [Tm.shift, Tm.erase, h, iha, ihb]
  | send q a b iha ihb =>
    intro k
    by_cases h : erasable q = true <;> simp [Tm.shift, Tm.erase, h, iha, ihb]
  | letPair q f p ihf ihp => intro k; simp [Tm.shift, Tm.erase, ihf, ihp]
  | recv c ih => intro k; simp [Tm.shift, Tm.erase, ih]
  | close c ih => intro k; simp [Tm.shift, Tm.erase, ih]
  | wait c ih => intro k; simp [Tm.shift, Tm.erase, ih]
theorem Tm.erase_subst (t : Tm R) : ∀ k s, (t.subst k s).erase = t.erase.subst k s.erase := by
  induction t with
  | lam π A b ih => intro k s; simp [Tm.subst, Tm.erase, ih, Tm.erase_shift]
  | app π f a ihf iha =>
    intro k s
    by_cases h : erasable π = true <;> simp [Tm.subst, Tm.erase, h, ihf, iha]
  | ite c t e ihc iht ihe => intro k s; simp [Tm.subst, Tm.erase, ihc, iht, ihe]
  | var i =>
    intro k s
    by_cases h₁ : i < k <;> by_cases h₂ : i = k <;> simp [Tm.subst, Tm.erase, h₁, h₂]
  | unit => intro k s; simp [Tm.subst, Tm.erase]
  | bool b => intro k s; simp [Tm.subst, Tm.erase]
  | ghost => intro k s; simp [Tm.subst, Tm.erase]
  | pair q a b iha ihb =>
    intro k s
    by_cases h : erasable q = true <;> simp [Tm.subst, Tm.erase, h, iha, ihb]
  | send q a b iha ihb =>
    intro k s
    by_cases h : erasable q = true <;> simp [Tm.subst, Tm.erase, h, iha, ihb]
  | letPair q f p ihf ihp => intro k s; simp [Tm.subst, Tm.erase, ihf, ihp]
  | recv c ih => intro k s; simp [Tm.subst, Tm.erase, ih]
  | close c ih => intro k s; simp [Tm.subst, Tm.erase, ih]
  | wait c ih => intro k s; simp [Tm.subst, Tm.erase, ih]

/-- A variable the typing grades `0` does not occur in the erased term: what is substituted for
it cannot matter. This is where erasure uses the typing. -/
theorem HasTy.erase_subst_irrelevant {Γ : List (Ty R)} {t : Tm R} {A : Ty R} {U : Usage R}
    (h : HasTy Γ t A U) :
    ∀ k, U k = 𝟘 → ∀ s s' : Tm R, t.erase.subst k s = t.erase.subst k s' := by
  induction h with
  | @var Γ i T _ =>
    intro k hk s s'
    have ne : ¬ i = k := by
      intro e
      subst e
      have one : (𝟙 : R) = 𝟘 := by simpa [Usage.single] using hk
      exact ResourceRig.one_ne_zero one
    by_cases h₁ : i < k <;> simp [Tm.erase, Tm.subst, h₁, ne]
  | unit => intro k _ s s'; simp [Tm.erase, Tm.subst]
  | bool => intro k _ s s'; simp [Tm.erase, Tm.subst]
  | @lam Γ π T B b W _ _ ih =>
    intro k hk s s'
    simp only [Tm.erase, Tm.subst]
    rw [ih (k + 1) hk (s.shift 0) (s'.shift 0)]
  | @app Γ π T B f a U V _ _ ihf iha =>
    intro k hk s s'
    obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    by_cases hπ : erasable π = true
    · simp only [Tm.erase, hπ, ↓reduceIte, Tm.subst]
      rw [ihf k hU s s']
    · rcases ResourceRig.mul_eq_zero _ _ hV with h0 | h0
      · exact absurd ((erasable_iff π).mpr h0) hπ
      · simp only [Tm.erase, hπ, Bool.false_eq_true, ↓reduceIte, Tm.subst]
        rw [ihf k hU s s', iha k h0 s s']
  | @ite Γ T c t e U V _ _ _ ihc iht ihe =>
    intro k hk s s'
    obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    simp only [Tm.erase, Tm.subst]
    rw [ihc k hU s s', iht k hV s s', ihe k hV s s']
  | @send Γ π T B f a U V _ _ ihf iha =>
    intro k hk s s'
    obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    by_cases hπ : erasable π = true
    · simp only [Tm.erase, hπ, ↓reduceIte, Tm.subst]
      rw [ihf k hU s s']
    · rcases ResourceRig.mul_eq_zero _ _ hV with h0 | h0
      · exact absurd ((erasable_iff π).mpr h0) hπ
      · simp only [Tm.erase, hπ, Bool.false_eq_true, ↓reduceIte, Tm.subst]
        rw [ihf k hU s s', iha k h0 s s']
  | @pair Γ π T B a f U V _ _ ihf iha =>
    intro k hk s s'
    obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    by_cases hπ : erasable π = true
    · simp only [Tm.erase, hπ, ↓reduceIte, Tm.subst]
      rw [ihf k hU s s']
    · rcases ResourceRig.mul_eq_zero _ _ hV with h0 | h0
      · exact absurd ((erasable_iff π).mpr h0) hπ
      · simp only [Tm.erase, hπ, Bool.false_eq_true, ↓reduceIte, Tm.subst]
        rw [ihf k hU s s', iha k h0 s s']
  | letPair _ _ ihf ihp =>
    intro k hk s s'
    obtain ⟨hU, hV⟩ := ResourceRig.add_eq_zero _ _ hk
    simp only [Tm.erase, Tm.subst]
    rw [ihf k hU s s', ihp k hV s s']
  | recv _ ih =>
    intro k hk s s'
    simp only [Tm.erase, Tm.subst]
    rw [ih k hk s s']
  | close _ ih =>
    intro k hk s s'
    simp only [Tm.erase, Tm.subst]
    rw [ih k hk s s']
  | wait _ ih =>
    intro k hk s s'
    simp only [Tm.erase, Tm.subst]
    rw [ih k hk s s']
  | @sub Γ t T U U' _ relaxed ih =>
    intro k hk s s'
    have below := relaxed k
    rw [hk] at below
    exact ih k (ResourceRig.le_zero _ below) s s'
/-- One step of a typed term is one step of its erasure. -/
theorem HasTy.erase_step {Γ : List (Ty R)} {t t' : Tm R} {A : Ty R} {U : Usage R}
    (h : HasTy Γ t A U) (s : Step t t') : Step t.erase t'.erase := by
  induction h generalizing t' with
  | @app Γ π T B f a U V hf ha ihf _ =>
    cases s with
    | beta =>
      obtain ⟨B', W, e, body, fits, _⟩ := hf.lam_inv
      obtain ⟨e₁, e₂, e₃⟩ := Ty.arr.inj e
      subst e₁ e₂ e₃
      rw [Tm.erase_subst]
      by_cases hπ : erasable π = true
      · have unused : W 0 = 𝟘 := by
          rw [(erasable_iff π).mp hπ] at fits
          exact ResourceRig.le_zero _ fits
        simp only [Tm.erase, hπ, ↓reduceIte]
        rw [← body.erase_subst_irrelevant 0 unused .ghost a.erase]
        exact .beta
      · simp only [Tm.erase, hπ, Bool.false_eq_true, ↓reduceIte]
        exact .beta
    | appFun s' =>
      by_cases hπ : erasable π = true
      · simp only [Tm.erase, hπ, ↓reduceIte]; exact .appFun (ihf s')
      · simp only [Tm.erase, hπ, Bool.false_eq_true, ↓reduceIte]; exact .appFun (ihf s')
  | @ite Γ T c t e U V _ _ _ ihc _ _ =>
    cases s with
    | iteCond s' => simp only [Tm.erase]; exact .iteCond (ihc s')
    | iteTrue => simp only [Tm.erase]; exact .iteTrue
    | iteFalse => simp only [Tm.erase]; exact .iteFalse
  | @letPair Γ q A B C f p U V _ _ _ _ =>
    cases s with
    | pairBeta =>
      have hOne : erasable (𝟙 : R) = false := by simp [erasable, ResourceRig.one_ne_zero]
      by_cases hq : erasable q = true
      · simp only [Tm.erase, hq, hOne, ↓reduceIte]; exact .pairBeta
      · have hq' : erasable q = false := Bool.eq_false_iff.mpr hq
        simp only [Tm.erase, hq', hOne, Bool.false_eq_true, ↓reduceIte]; exact .pairBeta
  | pair => cases s
  | send => cases s
  | recv => cases s
  | close => cases s
  | wait => cases s
  | @sub Γ t T U U' _ _ ih => exact ih s
  | var => cases s
  | unit => cases s
  | bool => cases s
  | lam => cases s

/-- **Erasure is sound.** Whatever a typed term reduces to, its erasure reduces to the erasure of
that, step for step: dropping every `0`-graded argument changes nothing the program computes. -/
theorem qtt_zero_grade_erasure_sound {Γ : List (Ty R)} {t t' : Tm R} {A : Ty R} {U : Usage R}
    (h : HasTy Γ t A U) (s : Steps t t') : Steps t.erase t'.erase := by
  induction s with
  | refl => exact .refl _
  | head first _ ih => exact .head (h.erase_step first) (ih (h.step first))
/-- **Non-interference of ghosts.** Two programs that differ only in a `0`-graded argument have
the same erasure, so when one evaluates to a Boolean the other's run-time term does too. -/
theorem qtt_zero_grade_noninterference {Γ : List (Ty R)} {f a a' : Tm R} {U : Usage R} {v : Bool}
    (h : HasTy Γ (.app 𝟘 f a) .bool U) (s : Steps (.app 𝟘 f a) (.bool v)) :
    Steps (Tm.app 𝟘 f a').erase (.bool v) := by
  have same : (Tm.app 𝟘 f a').erase = (Tm.app 𝟘 f a).erase := by
    simp [Tm.erase, erasable]
  rw [same]
  simpa [Tm.erase] using qtt_zero_grade_erasure_sound h s

/-- Run-time occurrences of variable `k`: an erased argument has none, and of two branches the
larger count runs. -/
def Tm.occ : Tm R → Nat → Nat
  | .var i, k => if i = k then 1 else 0
  | .lam _ _ b, k => b.occ (k + 1)
  | .app π f a, k => f.occ k + (if erasable π then 0 else a.occ k)
  | .ite c t e, k => c.occ k + max (t.occ k) (e.occ k)
  | .unit, _ => 0
  | .bool _, _ => 0
  | .ghost, _ => 0
  | .pair q a b, k => b.occ k + (if erasable q then 0 else a.occ k)
  | .send q c a, k => c.occ k + (if erasable q then 0 else a.occ k)
  | .letPair _ f p, k => f.occ k + p.occ k
  | .recv c, k => c.occ k
  | .close c, k => c.occ k
  | .wait c, k => c.occ k
end Terms

/-! ## The linear discipline over `0, 1, ω` -/
/-- **A linear capability is used exactly once; a ghost never.** A variable graded `1` has one
run-time occurrence (it is neither dropped nor duplicated), and one graded `0` has none. -/
theorem linear_cap_used_exactly_once {Γ : List (Ty ZeroOneOmega)} {t : Tm ZeroOneOmega}
    {A : Ty ZeroOneOmega} {U : Usage ZeroOneOmega} (h : HasTy Γ t A U) :
    ∀ k, (U k = .zero → t.occ k = 0) ∧ (U k = .one → t.occ k = 1) := by
  induction h with
  | @var Γ i T _ =>
    intro k
    by_cases e : i = k
    · subst e; simp [Usage.single, Tm.occ]
    · have e' : ¬ k = i := fun h => e h.symm
      simp [Usage.single, Tm.occ, e, e']
  | unit => intro k; simp [Usage.zero, Tm.occ]
  | bool => intro k; simp [Usage.zero, Tm.occ]
  | @lam Γ π T B b W _ _ ih => intro k; exact ih (k + 1)
  | @app Γ π T B f a U V _ _ ihf iha =>
    intro k
    have hf := ihf k
    have ha := iha k
    simp only [Usage.add, Usage.scale, Tm.occ, ZeroOneOmega.rig_add, ZeroOneOmega.rig_mul]
    generalize U k = u at hf ⊢
    generalize V k = v at ha ⊢
    cases π <;> cases u <;> cases v <;>
      simp_all [ZeroOneOmega.add, ZeroOneOmega.mul, erasable]
  | @ite Γ T c t e U V _ _ _ ihc iht ihe =>
    intro k
    have hc := ihc k
    have ht := iht k
    have he := ihe k
    simp only [Usage.add, Tm.occ, ZeroOneOmega.rig_add]
    generalize U k = u at hc ⊢
    generalize V k = v at ht he ⊢
    cases u <;> cases v <;> simp_all [ZeroOneOmega.add]
  | @send Γ π T B f a U V _ _ ihf iha =>
    intro k
    have hf := ihf k
    have ha := iha k
    simp only [Usage.add, Usage.scale, Tm.occ, ZeroOneOmega.rig_add, ZeroOneOmega.rig_mul]
    generalize U k = u at hf ⊢
    generalize V k = v at ha ⊢
    cases π <;> cases u <;> cases v <;>
      simp_all [ZeroOneOmega.add, ZeroOneOmega.mul, erasable]
  | @pair Γ π T B a f U V _ _ ihf iha =>
    intro k
    have hf := ihf k
    have ha := iha k
    simp only [Usage.add, Usage.scale, Tm.occ, ZeroOneOmega.rig_add, ZeroOneOmega.rig_mul]
    generalize U k = u at hf ⊢
    generalize V k = v at ha ⊢
    cases π <;> cases u <;> cases v <;>
      simp_all [ZeroOneOmega.add, ZeroOneOmega.mul, erasable]
  | @letPair Γ q A B C f p U V _ _ ihf ihp =>
    intro k
    have hf := ihf k
    have hp := ihp k
    simp only [Usage.add, Tm.occ, ZeroOneOmega.rig_add]
    generalize U k = u at hf ⊢
    generalize V k = v at hp ⊢
    cases u <;> cases v <;> simp_all [ZeroOneOmega.add]
  | recv _ ih => exact ih
  | close _ ih => exact ih
  | wait _ ih => exact ih
  | @sub Γ t T U U' _ relaxed ih =>
    intro k
    have hk := ih k
    have below : (U k).le (U' k) := (ZeroOneOmega.rig_le _ _).mp (relaxed k)
    generalize U k = u at hk below
    generalize U' k = u' at below ⊢
    cases u <;> cases u' <;> simp_all [ZeroOneOmega.le]

/-- No weakening and no contraction at grade `1`; no run-time use at grade `0`: what a binder's
annotation promises about its body. -/
theorem binder_discipline {Γ : List (Ty ZeroOneOmega)} {π : ZeroOneOmega}
    {A T : Ty ZeroOneOmega} {b : Tm ZeroOneOmega} {U : Usage ZeroOneOmega}
    (h : HasTy Γ (.lam π A b) T U) :
    (π = .one → b.occ 0 = 1) ∧ (π = .zero → b.occ 0 = 0) := by
  obtain ⟨B, W, _, body, fits, _⟩ := h.lam_inv
  have exact := linear_cap_used_exactly_once body 0
  have below : (W 0).le π := (ZeroOneOmega.rig_le _ _).mp fits
  generalize W 0 = w at exact below
  cases π <;> cases w <;> simp_all [ZeroOneOmega.le]
/-- **Subject reduction with linear capability conservation.** A step keeps the typing, and every
capability the context grades `1` has exactly one run-time occurrence before the step and exactly
one after it. -/
theorem qtt_step_preserves_typing_and_linear_caps {Γ : List (Ty ZeroOneOmega)}
    {t t' : Tm ZeroOneOmega} {A : Ty ZeroOneOmega} {U : Usage ZeroOneOmega}
    (h : HasTy Γ t A U) (s : Step t t') :
    HasTy Γ t' A U ∧ ∀ k, U k = .one → t.occ k = 1 ∧ t'.occ k = 1 :=
  ⟨h.step s, fun k linear =>
    ⟨(linear_cap_used_exactly_once h k).2 linear,
      (linear_cap_used_exactly_once (h.step s) k).2 linear⟩⟩

/-- A synchronous communication exposes the received payload and both continuation
endpoints. The endpoint slots are retagged, not copied; payload resources stay in Γ. -/
inductive Rendezvous : List (Ty ZeroOneOmega) → Tm ZeroOneOmega →
    List (Ty ZeroOneOmega) → Tm ZeroOneOmega → Prop where
  | communicate (Γ : List (Ty ZeroOneOmega)) (q : ZeroOneOmega) (A : Ty ZeroOneOmega)
      (S : SessionTy ZeroOneOmega) (payload : Tm ZeroOneOmega) :
      Rendezvous (.chan (.send q A S) :: .chan (.recv q A S.dual) :: Γ)
        (.pair .one (.send q (.var 0) (payload.shift 0 |>.shift 0)) (.recv (.var 1)))
        (.chan S :: .chan S.dual :: Γ)
        (.pair .one (.var 0) (.pair q (payload.shift 0 |>.shift 0) (.var 1)))
  | close (Γ : List (Ty ZeroOneOmega)) :
      Rendezvous (.chan .endS :: .chan .endS :: Γ)
        (.pair .one (.close (.var 0)) (.wait (.var 1))) Γ (.pair .one .unit .unit)

/-- Closing a linked pair consumes both endpoint slots. The residual context survives. -/
def closePair : Tm ZeroOneOmega := .pair .one (.close (.var 0)) (.wait (.var 1))
def closedPair : Tm ZeroOneOmega := .pair .one .unit .unit

theorem close_wait_subject_reduction (Γ : List (Ty ZeroOneOmega)) :
    Rendezvous (.chan .endS :: .chan .endS :: Γ) closePair Γ closedPair ∧
    HasTy (.chan .endS :: .chan .endS :: Γ) closePair (.tensor .one .unit .unit)
      (Usage.add (Usage.single 1) (Usage.scale .one (Usage.single 0))) ∧
    HasTy Γ closedPair (.tensor .one .unit .unit) Usage.zero := by
  refine ⟨.close Γ, .pair (.wait (.var rfl)) (.close (.var rfl)), ?_⟩
  have h := HasTy.pair (q := ZeroOneOmega.one) (Γ := Γ) HasTy.unit HasTy.unit
  have eq : Usage.add Usage.zero (Usage.scale ZeroOneOmega.one Usage.zero) = Usage.zero := by
    funext n; rfl
  rw [eq] at h
  exact h

/-- The exact global usage of a communication: each endpoint once and the payload at q. -/
def communicationUsage (q : ZeroOneOmega) (U : Usage ZeroOneOmega) : Usage ZeroOneOmega :=
  Usage.add (Usage.single 1) (Usage.scale .one
    (Usage.add (Usage.single 0) (Usage.scale q (Usage.insertAt 0 .zero (Usage.insertAt 0 .zero U)))))

/-- Concrete delegated subject reduction. The payload may itself be any linear session
endpoint. Both sides have the same grade vector; no duplicated or leaked payload resource. -/
theorem rendezvous_subject_reduction {Γ : List (Ty ZeroOneOmega)}
    {payload : Tm ZeroOneOmega} {q : ZeroOneOmega} {A : Ty ZeroOneOmega} {S : SessionTy ZeroOneOmega} {U : Usage ZeroOneOmega}
    (typed : HasTy Γ payload A U) :
    let before := Tm.pair .one (.send q (.var 0) (payload.shift 0 |>.shift 0)) (.recv (.var 1))
    let after := Tm.pair .one (.var 0) (.pair q (payload.shift 0 |>.shift 0) (.var 1))
    let Γ₀ := .chan (.send q A S) :: .chan (.recv q A S.dual) :: Γ
    let Γ₁ := .chan S :: .chan S.dual :: Γ
    let T := Ty.tensor .one (.chan S) (.tensor q A (.chan S.dual))
    Rendezvous Γ₀ before Γ₁ after ∧
      HasTy Γ₀ before T (communicationUsage q U) ∧
      HasTy Γ₁ after T (communicationUsage q U) ∧
      ∀ k, communicationUsage q U k = .one → before.occ k = 1 ∧ after.occ k = 1 := by
  dsimp
  have weaken (X Y : Ty ZeroOneOmega) :
      HasTy (X :: Y :: Γ) (payload.shift 0 |>.shift 0) A
        (Usage.insertAt 0 .zero (Usage.insertAt 0 .zero U)) :=
    (typed.weaken (Γ₁ := []) Y).weaken (Γ₁ := []) X
  have before := HasTy.pair (q := ZeroOneOmega.one)
    (HasTy.recv (HasTy.var (Γ := .chan (.send q A S) ::
      .chan (.recv q A S.dual) :: Γ) (i := 1) rfl))
    (HasTy.send (HasTy.var (i := 0) rfl) (weaken _ _))
  have after := HasTy.pair (q := ZeroOneOmega.one)
    (HasTy.pair (q := q) (HasTy.var (Γ := .chan S :: .chan S.dual :: Γ) (i := 1) rfl)
      (weaken _ _)) (HasTy.var (i := 0) rfl)
  have same : Usage.add (Usage.add (Usage.single 1)
      (Usage.scale q (Usage.insertAt 0 .zero (Usage.insertAt 0 .zero U))))
      (Usage.scale ZeroOneOmega.one (Usage.single 0)) = communicationUsage q U := by
    funext n
    simp only [communicationUsage, Usage.add, Usage.scale, ZeroOneOmega.rig_mul, ZeroOneOmega.mul,
      ResourceRig.add_assoc]
    rw [ResourceRig.add_comm (_ : ZeroOneOmega) (Usage.single 0 n)]
  rw [same] at after
  exact ⟨.communicate Γ q A S payload, before, after,
    fun k hk => ⟨(linear_cap_used_exactly_once before k).2 hk,
      (linear_cap_used_exactly_once after k).2 hk⟩⟩
theorem delegated_channel_subject_reduction {Γ : List (Ty ZeroOneOmega)}
    {payload : Tm ZeroOneOmega} {D S : SessionTy ZeroOneOmega} {U : Usage ZeroOneOmega}
    (typed : HasTy Γ payload (.chan D) U) :
    let before := Tm.pair .one (.send .one (.var 0) (payload.shift 0 |>.shift 0)) (.recv (.var 1))
    let after := Tm.pair .one (.var 0) (.pair .one (payload.shift 0 |>.shift 0) (.var 1))
    let Γ₀ := .chan (.send .one (.chan D) S) :: .chan (.recv .one (.chan D) S.dual) :: Γ
    let Γ₁ := .chan S :: .chan S.dual :: Γ
    let T := Ty.tensor .one (.chan S) (.tensor .one (.chan D) (.chan S.dual))
    Rendezvous Γ₀ before Γ₁ after ∧
      HasTy Γ₀ before T (communicationUsage .one U) ∧
      HasTy Γ₁ after T (communicationUsage .one U) ∧
      ∀ k, communicationUsage .one U k = .one → before.occ k = 1 ∧ after.occ k = 1 :=
  rendezvous_subject_reduction typed

/-- Communication commutes with erasure, including zero-grade payload transfer. -/
theorem Rendezvous.erase {Γ Γ' : List (Ty ZeroOneOmega)} {t t' : Tm ZeroOneOmega}
    (step : Rendezvous Γ t Γ' t') : Rendezvous Γ t.erase Γ' t'.erase := by
  cases step with
  | communicate Γ q A S payload =>
    cases q with
    | zero =>
      simpa [Tm.erase, erasable, Tm.shift] using Rendezvous.communicate Γ .zero A S .ghost
    | one =>
      simpa [Tm.erase, erasable, Tm.erase_shift] using Rendezvous.communicate Γ .one A S payload.erase
    | omega =>
      simpa [Tm.erase, erasable, Tm.erase_shift] using Rendezvous.communicate Γ .omega A S payload.erase
  | close =>
    simpa [Tm.erase, erasable] using Rendezvous.close Γ'

/-- The same along a whole run. -/
theorem qtt_steps_preserve_linear_caps {Γ : List (Ty ZeroOneOmega)}
    {t t' : Tm ZeroOneOmega} {A : Ty ZeroOneOmega} {U : Usage ZeroOneOmega}
    (h : HasTy Γ t A U) (s : Steps t t') :
    HasTy Γ t' A U ∧ ∀ k, U k = .one → t'.occ k = 1 :=
  ⟨h.steps s, fun k linear => (linear_cap_used_exactly_once (h.steps s) k).2 linear⟩

end Obend.Core.GradedSessionMetatheory
end
