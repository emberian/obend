module
/-
# Obend.Judge.Cost — the improvement judge

A candidate optimization is a pair of terms, the original and the rewritten. Its certificate is a
cost derivation: a list of steps, each re-associating one `mix` inside a context (either way
round). The checker runs the steps from the original and accepts when it reaches the candidate. An
accepted certificate of `n` steps means the two terms are within a factor of `8 ^ n` of each other
in clairvoyant cost, in every context and under every substitution (`Obend.Equiv.CostWithin`), in
both directions, with the same literal result: the charge difference of the rewrite is a theorem
(`charge_bound`).

Each step is `mix_assoc_cost` placed in its context (`CostWithin.context`); the steps compose with
their factors multiplied (`CostWithin.trans`). A context plugs its argument capture-avoidingly
(`instantiate`), so a step can rewrite under a binder only an association whose parts do not mention
that binder; `mix_assoc_cost` itself holds in every context, and the restriction is the certificate
language's. The judge never refutes: a rejected certificate says nothing about the pair.
-/
public import Obend.Judge.Class
public import Obend.Equiv.Cost
public import Obend.Core.TermTraverse

@[expose] public section
namespace Obend.Judge.Cost
open Obend.Core Obend.Core.Term Obend.Equiv
open Obend.Core.Traverse (Tree)
open Obend.Core.TermTraverse (Tag encode encode_injective substitute_comp)
set_option autoImplicit false

/-! ## Term equality, decided -/

deriving instance DecidableEq for Tag

mutual
def treeBeq : Tree Tag → Tree Tag → Bool
  | .var i, .var j => i == j
  | .bind a, .bind b => treeBeq a b
  | .node t cs, .node u ds => t == u && listBeq cs ds
  | _, _ => false
def listBeq : List (Tree Tag) → List (Tree Tag) → Bool
  | [], [] => true
  | a :: as, b :: bs => treeBeq a b && listBeq as bs
  | _, _ => false
end

mutual
theorem treeBeq_sound : (a b : Tree Tag) → treeBeq a b = true → a = b
  | .var i, .var j, h => by simp [treeBeq] at h; rw [h]
  | .bind a, .bind b, h => by simp only [treeBeq] at h; rw [treeBeq_sound a b h]
  | .node t cs, .node u ds, h => by
    simp only [treeBeq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, listBeq_sound cs ds h.2]
  | .var _, .bind _, h | .var _, .node _ _, h | .bind _, .var _, h | .bind _, .node _ _, h
  | .node _ _, .var _, h | .node _ _, .bind _, h => by simp [treeBeq] at h
theorem listBeq_sound : (as bs : List (Tree Tag)) → listBeq as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [listBeq, Bool.and_eq_true] at h
    rw [treeBeq_sound a b h.1, listBeq_sound as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [listBeq] at h
end

mutual
theorem treeBeq_refl : (a : Tree Tag) → treeBeq a a = true
  | .var i => by simp [treeBeq]
  | .bind a => by simp only [treeBeq]; exact treeBeq_refl a
  | .node t cs => by simp only [treeBeq, beq_self_eq_true, Bool.true_and]; exact listBeq_refl cs
theorem listBeq_refl : (as : List (Tree Tag)) → listBeq as as = true
  | [] => rfl
  | a :: as => by simp only [listBeq, Bool.and_eq_true]; exact ⟨treeBeq_refl a, listBeq_refl as⟩
end

/-- Equality of terms, decided through their traversal encoding. -/
def termBeq (t t' : Term) : Bool := treeBeq (encode t) (encode t')

theorem termBeq_refl (t : Term) : termBeq t t = true := treeBeq_refl _

theorem termBeq_sound {t t' : Term} (h : termBeq t t' = true) : t = t' :=
  encode_injective (treeBeq_sound _ _ h)

/-! ## `CostWithin` composes -/

theorem CostWithin.refl (t : Term) : CostWithin 1 t t := fun _ _ v k h =>
  ⟨v, k, h, by omega, fun _ => rfl⟩

theorem CostWithin.trans {A B : Nat} {t t' t'' : Term} (h : CostWithin A t t') (h' : CostWithin B t' t'') :
    CostWithin (B * A) t t'' := by
  intro ρ C v k run
  obtain ⟨v1, k1, r1, b1, l1⟩ := h ρ C v k run
  obtain ⟨v2, k2, r2, b2, l2⟩ := h' ρ C v1 k1 r1
  refine ⟨v2, k2, r2, ?_, fun lit => ?_⟩
  · calc k2 ≤ B * k1 := b2
      _ ≤ B * (A * k) := Nat.mul_le_mul_left B b1
      _ = B * A * k := by rw [Nat.mul_assoc]
  · have e1 := l1 lit
    subst e1
    exact l2 lit

/-- The context that plugs `D[x]` into `C`. -/
def compose (C D : Term) : Term :=
  C.substitute fun | 0 => D | n + 1 => .bound (n + 1)

theorem compose_instantiate (C D x : Term) :
    instantiate (compose C D) x = instantiate C (instantiate D x) := by
  rw [instantiate_eq, instantiate_eq, compose, substitute_comp]
  congr 1; funext i
  cases i with
  | zero => rw [instantiate_eq]; rfl
  | succ n => simp [single, Term.substitute]

/-- A cost relation in a context. -/
theorem CostWithin.context {A : Nat} {t t' : Term} (h : CostWithin A t t') (D : Term) :
    CostWithin A (instantiate D t) (instantiate D t') := by
  intro ρ C v k run
  rw [instantiate_substitute, ← compose_instantiate] at run
  obtain ⟨v', k', r, b, l⟩ := h ρ (compose C (D.substitute (liftSubstitution ρ))) v k run
  refine ⟨v', k', ?_, b, l⟩
  rw [instantiate_substitute, ← compose_instantiate]; exact r

/-! ## Certificates -/

/-- One step: in `context`, re-associate `mix` over `a`, `b`, `c`; left to right turns
`mix (mix a b) c` into `mix a (mix b c)`. -/
structure Step where
  context : Term
  a : Term
  b : Term
  c : Term
  leftToRight : Bool

def Step.left (s : Step) : Term := .mix (.mix s.a s.b) s.c
def Step.right (s : Step) : Term := .mix s.a (.mix s.b s.c)
def Step.source (s : Step) : Term := instantiate s.context (if s.leftToRight then s.left else s.right)
def Step.target (s : Step) : Term := instantiate s.context (if s.leftToRight then s.right else s.left)

theorem Step.sound (s : Step) : CostWithin 8 s.source s.target ∧ CostWithin 8 s.target s.source := by
  obtain ⟨h1, h2⟩ := mix_assoc_cost s.a s.b s.c
  cases hd : s.leftToRight <;> simp only [Step.source, Step.target, hd, Bool.false_eq_true, ite_true, ite_false]
  · exact ⟨CostWithin.context h2 _, CostWithin.context h1 _⟩
  · exact ⟨CostWithin.context h1 _, CostWithin.context h2 _⟩

/-- Run the steps from a term: each must start where the previous one ended. -/
def runSteps : Term → List Step → Option Term
  | t, [] => some t
  | t, s :: rest => if termBeq t s.source then runSteps s.target rest else none

theorem runSteps_sound : ∀ (steps : List Step) {t t' : Term}, runSteps t steps = some t' →
    CostWithin (8 ^ steps.length) t t' ∧ CostWithin (8 ^ steps.length) t' t
  | [], t, t', h => by
    simp only [runSteps, Option.some.injEq] at h
    subst h
    exact ⟨CostWithin.refl t, CostWithin.refl t⟩
  | s :: rest, t, t', h => by
    simp only [runSteps] at h
    split at h
    · rename_i hb
      have e := termBeq_sound hb
      subst e
      obtain ⟨r1, r2⟩ := runSteps_sound rest h
      obtain ⟨s1, s2⟩ := s.sound
      have f : 8 ^ (s :: rest).length = 8 ^ rest.length * 8 := by
        simp [List.length_cons, Nat.pow_succ]
      rw [f]
      exact ⟨CostWithin.trans s1 r1, by have := CostWithin.trans r2 s2; rwa [Nat.mul_comm] at this⟩
    · cases h

/-! ## The judge -/

/-- Why a certificate is rejected. -/
inductive Clause where
  /-- step `i` does not start where the previous one ended -/
  | stepMismatch
  /-- the steps end elsewhere than the candidate -/
  | endMismatch
  deriving DecidableEq, Repr

def check (r : Nat) (o : Term × Term) (steps : List Step) : Verdict Clause :=
  if steps.length ≤ r then
    match runSteps o.1 steps with
    | some t => if termBeq t o.2 then .ok else .refused .endMismatch []
    | none => .refused .stepMismatch []
  else .uncovered

/-- What an accepted certificate establishes: the charge difference, both ways. -/
def Meaning (o : Term × Term) (steps : List Step) : Prop :=
  CostWithin (8 ^ steps.length) o.1 o.2 ∧ CostWithin (8 ^ steps.length) o.2 o.1

/-- **The improvement judge.** Objects are an original term and a candidate; certificates are
re-association derivations; the grade bounds their length. -/
instance improvement : Judge (Term × Term) (List Step) where
  Clause := Clause
  Meaning := Meaning
  check := check
  sound := by
    intro r o steps h
    simp only [check] at h
    split at h
    · split at h
      · rename_i t ht
        split at h
        · rename_i hb
          have e := termBeq_sound hb
          subst e
          exact runSteps_sound steps ht
        · cases h
      · cases h
    · cases h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment o := ∃ steps, runSteps o.1 steps = some o.2
  complete := by
    rintro o ⟨steps, hrun⟩ _
    exact ⟨steps, steps.length, by simp [check, hrun, termBeq_refl]⟩
  mono := by
    intro r r' o steps le hne
    simp only [check] at hne ⊢
    split at hne
    · rename_i h; simp [Nat.le_trans h le, h]
    · exact absurd rfl hne

/-- **A member's charge difference is a theorem**: an accepted rewrite bounds the clairvoyant cost
of the candidate by `8 ^ n` times the original's, in every context, with the same literal result
(and the original by the candidate's, the same way). -/
theorem charge_bound {r : Nat} {t t' : Term} {steps : List Step}
    (h : improvement.check r (t, t') steps = .ok) (ρ : Nat → Term) (C v : Term) (k : Nat)
    (run : CV (instantiate C (t.substitute ρ)) v k) :
    ∃ v' k', CV (instantiate C (t'.substitute ρ)) v' k' ∧ k' ≤ 8 ^ steps.length * k ∧
      (Literal v → v' = v) :=
  (improvement.sound h).1 ρ C v k run

/-! ## A certificate, accepted and planted -/

/-- `mix (mix (mix 1 2) 3) 4`, re-associated in two steps to `mix 1 (mix 2 (mix 3 4))`. -/
def original : Term := .mix (.mix (.mix (.nat 1) (.nat 2)) (.nat 3)) (.nat 4)
def candidate : Term := .mix (.nat 1) (.mix (.nat 2) (.mix (.nat 3) (.nat 4)))

def twoSteps : List Step :=
  [⟨.bound 0, .mix (.nat 1) (.nat 2), .nat 3, .nat 4, true⟩,
   ⟨.bound 0, .nat 1, .nat 2, .mix (.nat 3) (.nat 4), true⟩]

theorem twoSteps_accepted : check 2 (original, candidate) twoSteps = .ok := by
  simp [check, runSteps, twoSteps, original, candidate, Step.source, Step.target, Step.left, Step.right,
    instantiate, Term.substitute, termBeq, encode, treeBeq, listBeq]

/-- Its meaning: within a factor of 64 both ways. -/
theorem original_candidate : CostWithin 64 original candidate ∧ CostWithin 64 candidate original :=
  improvement.sound (r := 2) twoSteps_accepted

/-- A planted bad certificate: the second step re-associates the wrong way round. -/
def badSteps : List Step :=
  [⟨.bound 0, .mix (.nat 1) (.nat 2), .nat 3, .nat 4, true⟩,
   ⟨.bound 0, .nat 1, .nat 2, .mix (.nat 3) (.nat 4), false⟩]

theorem badSteps_refused : check 2 (original, candidate) badSteps = .refused .stepMismatch [] := by
  simp [check, runSteps, badSteps, original, Step.source, Step.target, Step.left, Step.right,
    instantiate, Term.substitute, termBeq, encode, treeBeq, listBeq]

end Obend.Judge.Cost
end
