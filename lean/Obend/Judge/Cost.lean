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
public import Obend.Equiv.Demand
public import Obend.Core.TermTraverse
public import Obend.Core.Proofs.TickCost

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

/-- Executable equality test on `Option (Term × Nat)` results from `evalClairvoyantMinCost` and `evalCBV`. -/
def optTermNatBeq : Option (Term × Nat) → Option (Term × Nat) → Bool
  | some (t1, k1), some (t2, k2) => termBeq t1 t2 && (k1 == k2)
  | none, none => true
  | _, _ => false

theorem optTermNatBeq_sound {o1 o2 : Option (Term × Nat)} (h : optTermNatBeq o1 o2 = true) : o1 = o2 := by
  cases o1 with
  | none =>
    cases o2 with
    | none => rfl
    | some _ => cases h
  | some r1 =>
    obtain ⟨t1, k1⟩ := r1
    cases o2 with
    | none => cases h
    | some r2 =>
      obtain ⟨t2, k2⟩ := r2
      simp only [optTermNatBeq, Bool.and_eq_true, beq_iff_eq] at h
      rw [termBeq_sound h.1, h.2]

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

/-! ## Parallel rounds: a flat factor per round -/

/-- Directional improvement within a factor (Moran–Sands Def. 4.1, one way): in every substitution
and context, the candidate `t'` costs at most `A` times the original `t`, with the same literal
result. -/
def Improves (A : Nat) (t t' : Term) : Prop := CostWithin A t t'

/-- One association to re-associate, and which way. -/
structure Assoc where
  a : Term
  b : Term
  c : Term
  leftToRight : Bool

def Assoc.source (s : Assoc) : Term := if s.leftToRight then .mix (.mix s.a s.b) s.c else .mix s.a (.mix s.b s.c)
def Assoc.target (s : Assoc) : Term := if s.leftToRight then .mix s.a (.mix s.b s.c) else .mix (.mix s.a s.b) s.c

/-- One round: a context whose indices `0 … n-1` are holes, and an association for each, all
re-associated at once. -/
structure Round where
  context : Term
  assocs : List Assoc

/-- The `n`-th hole's filler, one side; the context's other free indices are shifted down. -/
def pick (l : List Assoc) (side : Assoc → Term) (n : Nat) : Term :=
  match l[n]? with
  | some s => side s
  | none => .bound (n - l.length)

def Round.source (r : Round) : Term := r.context.substitute (pick r.assocs Assoc.source)
def Round.target (r : Round) : Term := r.context.substitute (pick r.assocs Assoc.target)

theorem pick_sim (l : List Assoc) (ρ : Nat → Term) (n : Nat) :
    Sim ((pick l Assoc.source n).substitute ρ) ((pick l Assoc.target n).substitute ρ) := by
  unfold pick
  split
  · rename_i s _
    cases hd : s.leftToRight <;> simp only [Assoc.source, Assoc.target, hd, Bool.false_eq_true, ite_true,
      ite_false, Term.substitute]
    · exact .assocRL (.refl _) (.refl _) (.refl _)
    · exact .assocLR (.refl _) (.refl _) (.refl _)
  · exact .refl _

/-- **A round is within a flat 8**, however many associations it re-associates. -/
theorem Round.sound (r : Round) : Improves 8 r.source r.target := by
  refine CostWithin.of_sim fun ρ => ?_
  simp only [Round.source, Round.target, substitute_comp]
  exact Sim.substRefl r.context (pick_sim r.assocs ρ)

/-- Run the rounds from a term: each must start where the previous one ended. -/
def runRounds : Term → List Round → Option Term
  | t, [] => some t
  | t, r :: rest => if termBeq t r.source then runRounds r.target rest else none

theorem runRounds_sound : ∀ (rounds : List Round) {t t' : Term}, runRounds t rounds = some t' →
    Improves (8 ^ rounds.length) t t'
  | [], t, t', h => by
    simp only [runRounds, Option.some.injEq] at h
    subst h
    exact CostWithin.refl t
  | r :: rest, t, t', h => by
    simp only [runRounds] at h
    split at h
    · rename_i hb
      have e := termBeq_sound hb
      subst e
      have f : 8 ^ (r :: rest).length = 8 ^ rest.length * 8 := by
        simp [List.length_cons, Nat.pow_succ]
      rw [f]
      exact CostWithin.trans r.sound (runRounds_sound rest h)
    · cases h

/-! ## The judge -/

/-- Why a certificate is rejected. -/
inductive Clause where
  /-- round `i` does not start where the previous one ended -/
  | stepMismatch
  /-- the rounds end elsewhere than the candidate -/
  | endMismatch
  deriving DecidableEq, Repr

def check (r : Nat) (o : Term × Term) (rounds : List Round) : Verdict Clause :=
  if rounds.length ≤ r then
    match runRounds o.1 rounds with
    | some t => if termBeq t o.2 then .ok else .refused .endMismatch []
    | none => .refused .stepMismatch []
  else .uncovered

/-- What an accepted certificate establishes: the candidate improves on the original within `8`
per round. -/
def Meaning (o : Term × Term) (rounds : List Round) : Prop := Improves (8 ^ rounds.length) o.1 o.2

/-- **The improvement judge.** Objects are an original term and a candidate; certificates are
rounds of parallel re-association; the grade bounds the number of rounds. -/
instance improvement : Judge (Term × Term) (List Round) where
  Clause := Clause
  Meaning := Meaning
  check := check
  sound := by
    intro r o rounds h
    simp only [check] at h
    split at h
    · split at h
      · rename_i t ht
        split at h
        · rename_i hb
          have e := termBeq_sound hb
          subst e
          exact runRounds_sound rounds ht
        · cases h
      · cases h
    · cases h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment o := ∃ rounds, runRounds o.1 rounds = some o.2
  complete := by
    rintro o ⟨rounds, hrun⟩ _
    exact ⟨rounds, rounds.length, by simp [check, hrun, termBeq_refl]⟩
  mono := by
    intro r r' o rounds le hne
    simp only [check] at hne ⊢
    split at hne
    · rename_i h; simp [Nat.le_trans h le, h]
    · exact absurd rfl hne

/-- **A member's charge is a theorem**: an accepted rewrite bounds the clairvoyant cost of the
candidate by `8` per round times the original's, in every context, with the same literal result. -/
theorem charge_bound {r : Nat} {t t' : Term} {rounds : List Round}
    (h : improvement.check r (t, t') rounds = .ok) (ρ : Nat → Term) (C v : Term) (k : Nat)
    (run : CV (instantiate C (t.substitute ρ)) v k) :
    ∃ v' k', CV (instantiate C (t'.substitute ρ)) v' k' ∧ k' ≤ 8 ^ rounds.length * k ∧
      (Literal v → v' = v) :=
  (improvement.sound h) ρ C v k run

/-! ## Certificates, accepted and planted -/

/-- `mix (mix (mix 1 2) 3) 4`, re-associated in two steps to `mix 1 (mix 2 (mix 3 4))`. -/
def original : Term := .mix (.mix (.mix (.nat 1) (.nat 2)) (.nat 3)) (.nat 4)
def candidate : Term := .mix (.nat 1) (.mix (.nat 2) (.mix (.nat 3) (.nat 4)))

def twoSteps : List Step :=
  [⟨.bound 0, .mix (.nat 1) (.nat 2), .nat 3, .nat 4, true⟩,
   ⟨.bound 0, .nat 1, .nat 2, .mix (.nat 3) (.nat 4), true⟩]

theorem twoSteps_accepted : runSteps original twoSteps = some candidate := by
  simp [runSteps, twoSteps, original, candidate, Step.source, Step.target, Step.left, Step.right,
    instantiate, Term.substitute, termBeq, encode, treeBeq, listBeq]

/-- Sequential steps, both ways: within a factor of 64. -/
theorem original_candidate : CostWithin 64 original candidate ∧ CostWithin 64 candidate original :=
  runSteps_sound twoSteps twoSteps_accepted

/-- A planted bad sequence: the second step re-associates the wrong way round. -/
def badSteps : List Step :=
  [⟨.bound 0, .mix (.nat 1) (.nat 2), .nat 3, .nat 4, true⟩,
   ⟨.bound 0, .nat 1, .nat 2, .mix (.nat 3) (.nat 4), false⟩]

theorem badSteps_refused : runSteps original badSteps = none := by
  simp [runSteps, badSteps, original, Step.source, Step.target, Step.left, Step.right,
    instantiate, Term.substitute, termBeq, encode, treeBeq, listBeq]

/-- The same rewrite as two rounds (the second association exists only after the first). -/
def twoRounds : List Round :=
  [⟨.bound 0, [⟨.mix (.nat 1) (.nat 2), .nat 3, .nat 4, true⟩]⟩,
   ⟨.bound 0, [⟨.nat 1, .nat 2, .mix (.nat 3) (.nat 4), true⟩]⟩]

theorem twoRounds_accepted : check 2 (original, candidate) twoRounds = .ok := by
  simp [check, runRounds, twoRounds, original, candidate, Round.source, Round.target, pick, Assoc.source,
    Assoc.target, Term.substitute, termBeq, encode, treeBeq, listBeq]

theorem original_improves : Improves 64 original candidate :=
  improvement.sound (r := 2) twoRounds_accepted

/-- Two independent associations in one record. -/
def pairOriginal : Term :=
  .record [("x", .mix (.mix (.nat 1) (.nat 2)) (.nat 3)), ("y", .mix (.mix (.nat 4) (.nat 5)) (.nat 6))]
def pairCandidate : Term :=
  .record [("x", .mix (.nat 1) (.mix (.nat 2) (.nat 3))), ("y", .mix (.nat 4) (.mix (.nat 5) (.nat 6)))]

/-- Both re-associated in one round. -/
def pairRound : List Round :=
  [⟨.record [("x", .bound 0), ("y", .bound 1)],
    [⟨.nat 1, .nat 2, .nat 3, true⟩, ⟨.nat 4, .nat 5, .nat 6, true⟩]⟩]

theorem pairRound_accepted : check 1 (pairOriginal, pairCandidate) pairRound = .ok := by
  simp [check, runRounds, pairRound, pairOriginal, pairCandidate, Round.source, Round.target, pick,
    Assoc.source, Assoc.target, Term.substitute, termBeq, encode, treeBeq, listBeq]

/-- **A flat factor**: two re-associations in one round cost a factor of 8, where two sequential
steps cost 64. -/
theorem pair_flat : Improves 8 pairOriginal pairCandidate := by
  have h : Meaning (pairOriginal, pairCandidate) pairRound := improvement.sound (r := 1) pairRound_accepted
  exact h

/-- A planted bad round: the second association is the wrong way round. -/
def badRound : List Round :=
  [⟨.record [("x", .bound 0), ("y", .bound 1)],
    [⟨.nat 1, .nat 2, .nat 3, true⟩, ⟨.nat 4, .nat 5, .nat 6, false⟩]⟩]

theorem badRound_refused : check 1 (pairOriginal, pairCandidate) badRound = .refused .stepMismatch [] := by
  simp [check, runRounds, badRound, pairOriginal, Round.source, pick, Assoc.source,
    Term.substitute, termBeq, encode, treeBeq, listBeq]

/-! ## The cost judge: a demand run as the certificate -/

open Obend.Equiv.Demand (FE obj demand demand_exists demand_minimal)
open Obend.Core.Proofs.TickCost (Finishes fragment_within)

/-- A certificate that `t` costs at most `k`: `t` is the selection of `field` from the object with
these fields, whose demand run is total. -/
structure DemandCert where
  fields : List (String × FE)
  field : String

inductive CostClause where
  /-- the selection has no demand run: no derivation exists -/
  | noDemand
  /-- the demand exceeds the bound: no derivation is that cheap -/
  | overBudget
  deriving DecidableEq, Repr

/-- The checker: on the object fragment (the certificate's selection, distinct names) it runs the
demand semantics; off it, the verdict is `uncovered`. -/
def costCheck (_ : Nat) (o : Term × Nat) (c : DemandCert) : Verdict CostClause :=
  if termBeq o.1 (.get (obj c.fields) c.field) then
    if (c.fields.map Prod.fst).Nodup then
      match demand c.fields c.field with
      | some (_, n) => if n ≤ o.2 then .ok else .refused .overBudget []
      | none => .refused .noDemand []
    else .uncovered
  else .uncovered

def costRefutes : CostClause → Bool
  | .noDemand | .overBudget => true

/-- The raw machine has completed `t` with a number within `T` transitions. -/
def TicksAtMost (t : Term) (T : Nat) : Prop := ∃ n, Finishes t T n

/-- What an accepted cost certificate establishes: `t` costs at most `k`, and the raw machine
completes it within `4·k` transitions (`Obend.Core.Proofs.TickCost.ticks_within_fragment`). -/
def CostMeaning (o : Term × Nat) : Prop := CostAtMost o.1 o.2 ∧ TicksAtMost o.1 (4 * o.2)

theorem cost_sound {r : Nat} {o : Term × Nat} {c : DemandCert} (h : costCheck r o c = .ok) : CostMeaning o := by
  simp only [costCheck] at h
  split at h
  · rename_i hb
    have e := termBeq_sound hb
    split at h
    · rename_i nd
      split at h
      · rename_i v n hd
        split at h
        · rename_i le
          unfold CostMeaning TicksAtMost
          rw [e]
          exact ⟨⟨_, n, demand_exists nd hd, le⟩, v, fragment_within hd (by omega)⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- Constructive `CostAtMost` projection from `costCheck` (`0 Classical.choice`). -/
theorem costCheck_costAtMost {r : Nat} {o : Term × Nat} {c : DemandCert}
    (h : costCheck r o c = .ok) : CostAtMost o.1 o.2 := by
  simp only [costCheck] at h
  split at h
  · rename_i hb
    have e := termBeq_sound hb
    split at h
    · rename_i nd
      split at h
      · rename_i v n hd
        split at h
        · rename_i le
          rw [e]
          exact ⟨_, n, demand_exists nd hd, le⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- A refusal refutes the cost bound itself: no derivation is that cheap, or none exists. -/
theorem cost_refuted {r : Nat} {o : Term × Nat} {c : DemandCert} {k : CostClause} {p : List Nat}
    (h : costCheck r o c = .refused k p) : ¬ CostAtMost o.1 o.2 := by
  intro hm
  obtain ⟨w, j, run, le⟩ := hm
  simp only [costCheck] at h
  split at h
  · rename_i hb
    have e := termBeq_sound hb
    rw [e] at run
    split at h
    · rename_i nd
      obtain ⟨v, n, hd, _, low⟩ := demand_minimal nd run
      split at h
      · rename_i v' n' hd'
        split at h
        · cases h
        · rename_i gt
          rw [hd] at hd'; cases hd'
          exact gt (by omega)
      · rename_i hd'
        rw [hd] at hd'; cases hd'
    · cases h
  · cases h

/-- **The cost judge.** Objects are a term and a bound; a certificate names the object and the
field; the checker runs the demand semantics, which is total, so `cost t ≤ k` is checkable, and a
demand above `k` (or none) refutes it, by minimality. The receipt of an accepted certificate also
says the raw machine completes within `4·k` transitions; off the fragment the verdict is
`uncovered`. -/
instance cost : Judge (Term × Nat) DemandCert where
  Clause := CostClause
  Meaning o _ := CostMeaning o
  check := costCheck
  sound := cost_sound
  refutes := costRefutes
  refuted := by
    intro r o c k p h _ c' hm
    exact cost_refuted h hm.1
  Fragment o := ∃ fs x, (fs.map Prod.fst).Nodup ∧ o.1 = .get (obj fs) x
  complete := by
    rintro o ⟨fs, x, nd, e⟩ ⟨_, ⟨w, j, run, le⟩, _⟩
    rw [e] at run
    obtain ⟨v, n, hd, _, low⟩ := demand_minimal nd run
    refine ⟨⟨fs, x⟩, 0, ?_⟩
    simp only [costCheck, e, termBeq_refl, ite_true, nd, hd]
    simp [show n ≤ o.2 by omega]
  mono := by
    intro r r' o c _ _
    rfl

/-- Off the fragment the judge says nothing: a term that is not the certificate's selection is
`uncovered`. -/
theorem costCheck_off (r : Nat) (o : Term × Nat) (c : DemandCert)
    (h : termBeq o.1 (.get (obj c.fields) c.field) = false) : costCheck r o c = .uncovered := by
  simp [costCheck, h]

/-- `{a = 7, b = self.a}.b` costs at most 7, checked; at most 6 is refuted. -/
theorem selfField_cost_checked :
    costCheck 0 (.get CostTests.selfField "b", 7) ⟨Demand.selfFieldFields, "b"⟩ = .ok ∧
      costCheck 0 (.get CostTests.selfField "b", 6) ⟨Demand.selfFieldFields, "b"⟩ = .refused .overBudget [] := by
  constructor <;> simp [costCheck, Demand.selfField_is_obj, termBeq_refl] <;> decide

/-- **Its receipt**: `{a = 7, b = self.a}.b` costs at most 7 and the raw machine completes it within
28 transitions. -/
theorem selfField_receipt : CostMeaning (.get CostTests.selfField "b", 7) :=
  cost_sound selfField_cost_checked.1

/-! ## Clairvoyant Sharing Cost Certificate (`SharingCostCert`, `verifySharingCostCert`) -/

/-- Clairvoyant Sharing Cost Certificate (`SharingCostCert`):
certifies that `term` evaluates under `evalClairvoyantMinCost fuel` to `expectedValue`
within `clairvoyantBound` ticks, and verifies Call-By-Value tick bounds (`cbvBound`). -/
structure SharingCostCert where
  term : Term
  expectedValue : Term
  fuel : Nat
  clairvoyantBound : Nat
  cbvBound : Nat

/-- Verify a `SharingCostCert`:
1. `evalClairvoyantMinCost c.fuel c.term` returns `some (v, k)` with `termBeq v c.expectedValue`
   and `k ≤ c.clairvoyantBound`.
2. `c.clairvoyantBound ≤ c.cbvBound`.
3. `evalCBV c.fuel c.term` converges with `some (vCbv, kCbv)`, verifying `termBeq vCbv c.expectedValue`,
   `k ≤ kCbv` (clairvoyant call-by-need cost is at most CBV cost), and `kCbv ≤ c.cbvBound`. -/
def verifySharingCostCert (c : SharingCostCert) : Bool :=
  match evalClairvoyantMinCost c.fuel c.term, evalCBV c.fuel c.term with
  | some (v, k), some (vCbv, kCbv) =>
    termBeq v c.expectedValue && decide (k ≤ c.clairvoyantBound) &&
      decide (c.clairvoyantBound ≤ c.cbvBound) &&
      termBeq vCbv c.expectedValue && decide (k ≤ kCbv) && decide (kCbv ≤ c.cbvBound)
  | _, _ => false

/-- Semantic meaning established by `verifySharingCostCert c = true`. -/
def SharingCostMeaning (c : SharingCostCert) : Prop :=
  ∃ k kCbv,
    evalClairvoyantMinCost c.fuel c.term = some (c.expectedValue, k) ∧
    evalCBV c.fuel c.term = some (c.expectedValue, kCbv) ∧
    CV c.term c.expectedValue k ∧
    CV c.term c.expectedValue kCbv ∧
    k ≤ c.clairvoyantBound ∧
    c.clairvoyantBound ≤ c.cbvBound ∧
    k ≤ kCbv ∧
    kCbv ≤ c.cbvBound ∧
    CostAtMost c.term c.clairvoyantBound ∧
    CostAtMost c.term c.cbvBound

/-- **`verifySharingCostCert_sound`**: An accepted `SharingCostCert` establishes sound
clairvoyant and CBV derivations `CV c.term c.expectedValue k` and `CV c.term c.expectedValue kCbv`
with `k ≤ c.clairvoyantBound ≤ c.cbvBound` and `k ≤ kCbv ≤ c.cbvBound`
(`0 Classical.choice`, `0 sorry`). -/
theorem verifySharingCostCert_sound {c : SharingCostCert}
    (h : verifySharingCostCert c = true) : SharingCostMeaning c := by
  unfold verifySharingCostCert at h
  split at h
  · rename_i v k vCbv kCbv heval hcbv_eval
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hv_beq, hk_le⟩, hcbv_bound⟩, hv_cbv_beq⟩, hk_le_cbv⟩, hkcbv_le⟩ := h
    have hv_eq : v = c.expectedValue := termBeq_sound hv_beq
    have hv_cbv_eq : vCbv = c.expectedValue := termBeq_sound hv_cbv_beq
    subst hv_eq; subst hv_cbv_eq
    have hcv : CV c.term c.expectedValue k :=
      evalClairvoyantMinCost_sound c.fuel c.term c.expectedValue k heval
    have hcv_cbv : CV c.term c.expectedValue kCbv :=
      evalCBV_sound c.fuel c.term c.expectedValue kCbv hcbv_eval
    exact ⟨k, kCbv, heval, hcbv_eval, hcv, hcv_cbv, hk_le, hcbv_bound, hk_le_cbv, hkcbv_le,
      ⟨c.expectedValue, k, hcv, hk_le⟩, ⟨c.expectedValue, kCbv, hcv_cbv, hkcbv_le⟩⟩
  · cases h

inductive SharingCostClause where
  | checkFailed
  deriving DecidableEq, Repr

def sharingCostCheck (_ : Nat) (c : SharingCostCert) (_ : Unit) : Verdict SharingCostClause :=
  if verifySharingCostCert c then .ok else .refused .checkFailed []

/-- Kernel `Judge` instance for `SharingCostCert`. -/
instance sharingCostJudge : Judge SharingCostCert Unit where
  Clause := SharingCostClause
  Meaning c _ := SharingCostMeaning c
  check := sharingCostCheck
  sound := by
    intro _ c _ h
    unfold sharingCostCheck at h
    split at h
    · rename_i hv
      exact verifySharingCostCert_sound hv
    · cases h
  refutes _ := false
  refuted := by intro _ _ _ _ _ _ h; cases h
  Fragment c := verifySharingCostCert c = true
  complete := by
    intro c hc _
    exact ⟨(), 0, by simp [sharingCostCheck, hc]⟩
  mono := by
    intro _ _ _ _ _ _
    rfl

end Obend.Judge.Cost
end
