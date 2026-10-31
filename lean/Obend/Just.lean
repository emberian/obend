module
/-
# Obend.Just — justifications as a bounded distributive lattice, and the polynomials they evaluate

A justification of a candidate's eligibility is a conjunction of facts; a justification of a choice
among alternatives is a disjunction. `Just K` is the algebra of such values: a bounded distributive
lattice, written as a commutative semiring whose addition absorbs (`a + a·b = a`) and whose
multiplication is idempotent (`a·a = a`). Both laws are needed: absorption alone is satisfied by
the three-element structure `astra3` below, where `1·1 = 2`, so no map from set-valued monomials
into it can be a homomorphism (`astra3_absorptive`, `astra3_not_idem`; Astra's countermodel,
`astra/ASTRA-EVAL-20261031.md` line 15).

`Raw X` is a polynomial over tokens `X` as written: a list of monomials, each a list of tokens. Its
evaluation in any `Just K` (`Raw.eval`) needs no equality on tokens and is a homomorphism from the
written operations (`eval_append`, `eval_mul`). `Poly X` is the normal form: given a decidable
equality on tokens, `Raw.norm` removes repeated tokens and every monomial that contains another, and
the result is an antichain of duplicate-free token sets (`norm_antichain`, `norm_nodup`) with the same
value in every `Just K` (`eval_norm`). Normal forms are canonical: two antichains with the same Boolean
function have the same monomials up to token order (`canonical`), which is what fails for a written
`List (List X)` (`raw_not_canonical`).

The DUAL evaluation substitutes, for each token, `1` if it holds and the token itself if it does not
(`Raw.missing`). For one monomial, that is the monomial of the tokens that do not hold
(`missing_mono_mem`): what remains unsatisfied, by name. It is not a proof of the negation (a
failed product is refuted by any one failed factor, and a failed sum needs every alternative
refuted); and its Boolean image at "nothing restored" is the Boolean evaluation (`missing_bool`).
-/
public import Obend.AxiomPin
public import Obend.Tactic.Tooth
@[expose] public section

namespace Obend.Just

/-- A bounded distributive lattice, as an absorptive semiring with idempotent multiplication. -/
class Just (K : Type) where
  zero : K
  one : K
  add : K → K → K
  mul : K → K → K
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  absorb : ∀ a b, add a (mul a b) = a
  mul_idem : ∀ a, mul a a = a

namespace Just
variable {K : Type} [Just K]

scoped infixl:65 " ⊔ " => Just.add
scoped infixl:70 " ⊓ " => Just.mul

theorem mul_one (a : K) : a ⊓ one = a := by rw [mul_comm, one_mul]
theorem add_zero (a : K) : a ⊔ zero = a := by rw [add_comm, zero_add]
theorem add_idem (a : K) : a ⊔ a = a := by
  have := absorb a one; rwa [mul_one] at this
theorem zero_mul (a : K) : zero ⊓ a = (zero : K) := by
  have := absorb (zero : K) a; rwa [zero_add] at this
theorem mul_zero (a : K) : a ⊓ zero = (zero : K) := by rw [mul_comm, zero_mul]
theorem add_left_comm (a b c : K) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) := by
  rw [← add_assoc, add_comm a b, add_assoc]
theorem mul_left_comm (a b c : K) : a ⊓ (b ⊓ c) = b ⊓ (a ⊓ c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]
theorem add_mul (a b c : K) : (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) := by
  rw [mul_comm, distrib, mul_comm c, mul_comm c]
/-- `b ≤ a` in the lattice order is `a ⊓ b = b`; then `a` absorbs `b`. -/
theorem absorb_le {a b : K} (h : b = a ⊓ b) : a ⊔ b = a := by rw [h, absorb]

end Just

open Just

/-- The Boolean lattice: eligibility. -/
instance : Just Bool where
  zero := false
  one := true
  add := (· || ·)
  mul := (· && ·)
  add_comm := by decide
  add_assoc := by decide
  zero_add := by decide
  mul_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  distrib := by decide
  absorb := by decide
  mul_idem := by decide

/-! ## Absorption is not idempotence (Astra's countermodel) -/

/-- The three-element structure: zero `2`, one `0`, `min`, and `min 2 (a + b)`. -/
def astra3Add (a b : Fin 3) : Fin 3 := min a b
def astra3Mul (a b : Fin 3) : Fin 3 := if h : a.val + b.val ≥ 2 then 2 else ⟨a.val + b.val, by omega⟩

/-- `astra3` satisfies every law of the synthesis's `Just` (`review/SYNTHESIS-20261031.md` §3.1). -/
theorem astra3_absorptive :
    (∀ a b, astra3Add a b = astra3Add b a) ∧
    (∀ a b c, astra3Add (astra3Add a b) c = astra3Add a (astra3Add b c)) ∧
    (∀ a, astra3Add 2 a = a) ∧
    (∀ a b, astra3Mul a b = astra3Mul b a) ∧
    (∀ a b c, astra3Mul (astra3Mul a b) c = astra3Mul a (astra3Mul b c)) ∧
    (∀ a, astra3Mul 0 a = a) ∧ (∀ a, astra3Mul 2 a = 2) ∧
    (∀ a b c, astra3Mul a (astra3Add b c) = astra3Add (astra3Mul a b) (astra3Mul a c)) ∧
    (∀ a b, astra3Add a (astra3Mul a b) = a) := by
  unfold astra3Add astra3Mul; decide

/-- …and is not a lattice: `1 · 1 = 2`. -/
theorem astra3_not_idem : astra3Mul 1 1 ≠ 1 := by decide

/-! ## Written polynomials and their evaluation -/

/-- A polynomial as written: a sum of monomials, each a product of tokens. -/
abbrev Raw (X : Type) := List (List X)

section
variable {X K : Type} [Just K]

/-- The product of a monomial's tokens. -/
def Mono.eval (ν : X → K) : List X → K
  | [] => one
  | x :: m => ν x ⊓ Mono.eval ν m

/-- The sum of a polynomial's monomials. -/
def Raw.eval (ν : X → K) : Raw X → K
  | [] => zero
  | m :: ms => Mono.eval ν m ⊔ Raw.eval ν ms

/-- The product of two written polynomials: every pair of monomials, concatenated. -/
def Raw.mul (p q : Raw X) : Raw X := p.flatMap fun a => q.map (a ++ ·)

theorem Mono.eval_append (ν : X → K) (a b : List X) :
    Mono.eval ν (a ++ b) = Mono.eval ν a ⊓ Mono.eval ν b := by
  induction a with
  | nil => simp [Mono.eval, one_mul]
  | cons x a ih => simp [Mono.eval, ih, mul_assoc]

/-- A token of a monomial is absorbed by it. -/
theorem Mono.eval_mem (ν : X → K) {x : X} {m : List X} (h : x ∈ m) :
    Mono.eval ν m = ν x ⊓ Mono.eval ν m := by
  induction m with
  | nil => cases h
  | cons y m ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp only [Mono.eval]; rw [← mul_assoc, mul_idem]
    · simp only [Mono.eval]; conv => rhs; rw [mul_left_comm, ← ih h]

/-- A monomial containing another is below it. -/
theorem Mono.eval_subset (ν : X → K) {a m : List X} (h : a ⊆ m) :
    Mono.eval ν m = Mono.eval ν a ⊓ Mono.eval ν m := by
  induction a with
  | nil => simp [Mono.eval, one_mul]
  | cons x a ih =>
    simp only [Mono.eval]
    rw [mul_assoc, ← ih (fun y hy => h (List.mem_cons_of_mem _ hy)),
      ← Mono.eval_mem ν (h List.mem_cons_self)]

theorem Mono.eval_seteq (ν : X → K) {a b : List X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) :
    Mono.eval ν a = Mono.eval ν b := by
  rw [Mono.eval_subset ν h₁, Mono.eval_subset ν h₂, mul_comm, mul_assoc, mul_idem]

theorem Raw.eval_append (ν : X → K) (p q : Raw X) :
    Raw.eval ν (p ++ q) = Raw.eval ν p ⊔ Raw.eval ν q := by
  induction p with
  | nil => simp [Raw.eval, zero_add]
  | cons m p ih => simp [Raw.eval, ih, add_assoc]

theorem Raw.eval_map_append (ν : X → K) (a : List X) (q : Raw X) :
    Raw.eval ν (q.map (a ++ ·)) = Mono.eval ν a ⊓ Raw.eval ν q := by
  induction q with
  | nil => simp [Raw.eval, mul_zero]
  | cons m q ih => simp [Raw.eval, ih, Mono.eval_append, distrib]

/-- Evaluation is a homomorphism for the written product. -/
theorem Raw.eval_mul (ν : X → K) (p q : Raw X) :
    Raw.eval ν (Raw.mul p q) = Raw.eval ν p ⊓ Raw.eval ν q := by
  induction p with
  | nil => simp [Raw.mul, Raw.eval, zero_mul]
  | cons a p ih =>
    simp only [Raw.mul, List.flatMap_cons, Raw.eval_append, Raw.eval_map_append] at ih ⊢
    rw [ih, Raw.eval, add_mul]

/-- A monomial already in the sum adds nothing. -/
theorem Raw.eval_mem (ν : X → K) {a : List X} {p : Raw X} (h : a ∈ p) :
    Raw.eval ν p = Mono.eval ν a ⊔ Raw.eval ν p := by
  induction p with
  | nil => cases h
  | cons b p ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp only [Raw.eval]; rw [← add_assoc, add_idem]
    · simp only [Raw.eval]; conv => rhs; rw [add_left_comm, ← ih h]

/-- A monomial contained in every monomial of a sum absorbs the sum. -/
theorem Raw.eval_absorb (ν : X → K) {a : List X} {p : Raw X} (h : ∀ m ∈ p, a ⊆ m) :
    Mono.eval ν a ⊔ Raw.eval ν p = Mono.eval ν a := by
  induction p with
  | nil => simp [Raw.eval, add_zero]
  | cons m p ih =>
    simp only [Raw.eval]
    rw [← add_assoc, absorb_le (Mono.eval_subset ν (h m List.mem_cons_self)),
      ih fun m' hm' => h m' (List.mem_cons_of_mem _ hm')]

theorem Raw.eval_filter (ν : X → K) (P : List X → Bool) (p : Raw X) :
    Raw.eval ν p = Raw.eval ν (p.filter P) ⊔ Raw.eval ν (p.filter fun m => !P m) := by
  induction p with
  | nil => simp [Raw.eval, add_zero]
  | cons m p ih =>
    by_cases hm : P m = true
    · simp [hm, Raw.eval, ih, add_assoc]
    · simp [hm, Raw.eval, ih, add_left_comm]

/-- Evaluation depends only on the valuation of the tokens that occur. -/
theorem Raw.eval_congr {ν ν' : X → K} {p : Raw X} (h : ∀ m ∈ p, ∀ x ∈ m, ν x = ν' x) :
    Raw.eval ν p = Raw.eval ν' p := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    have hm : Mono.eval ν m = Mono.eval ν' m := by
      have hm := h m List.mem_cons_self
      clear h ih
      induction m with
      | nil => rfl
      | cons x m ihm =>
        simp only [Mono.eval]
        rw [hm x List.mem_cons_self, ihm fun y hy => hm y (List.mem_cons_of_mem _ hy)]
    simp only [Raw.eval]
    rw [hm, ih fun m' hm' => h m' (List.mem_cons_of_mem _ hm')]

/-- A token valued `0` zeroes every monomial that contains it. -/
theorem Mono.eval_zero_tok (ν : X → K) {x : X} {m : List X} (hx : x ∈ m) (h0 : ν x = zero) :
    Mono.eval ν m = zero := by
  rw [Mono.eval_mem ν hx, h0, zero_mul]

end

/-! ## Boolean evaluation -/

section
variable {X : Type}

theorem Mono.eval_bool (ν : X → Bool) (m : List X) :
    Mono.eval ν m = true ↔ ∀ x ∈ m, ν x = true := by
  induction m with
  | nil => simp [Mono.eval, Just.one]
  | cons x m ih => simp [Mono.eval, ← ih, Just.mul]

theorem Raw.eval_bool (ν : X → Bool) (p : Raw X) :
    Raw.eval ν p = true ↔ ∃ m ∈ p, ∀ x ∈ m, ν x = true := by
  induction p with
  | nil => simp [Raw.eval, Just.zero]
  | cons m p ih => simp [Raw.eval, ih, Mono.eval_bool, Just.add]

end

/-! ## The normal form: an antichain of token sets -/

section
variable {X : Type} [DecidableEq X]

/-- `a ⊆ b` as a test. -/
def sub (a b : List X) : Bool := a.all fun x => decide (x ∈ b)

theorem sub_iff {a b : List X} : sub a b = true ↔ a ⊆ b := by
  simp [sub, List.subset_def]

/-- The tokens of a monomial, each once. -/
def dedup : List X → List X
  | [] => []
  | x :: m => if x ∈ dedup m then dedup m else x :: dedup m

theorem mem_dedup {x : X} {m : List X} : x ∈ dedup m ↔ x ∈ m := by
  induction m with
  | nil => simp [dedup]
  | cons y m ih => unfold dedup; split <;> simp_all <;> grind

theorem nodup_dedup (m : List X) : (dedup m).Nodup := by
  induction m with
  | nil => exact List.nodup_nil
  | cons y m ih =>
    unfold dedup; split
    · exact ih
    · exact List.nodup_cons.2 ⟨by assumption, ih⟩

/-- Insert a monomial into an antichain: dropped if it contains a member, else added and every
member containing it dropped. -/
def insertMin (m : List X) (acc : Raw X) : Raw X :=
  if acc.any (fun a => sub a m) then acc else m :: acc.filter fun a => !sub m a

/-- The normal form of a written polynomial. -/
def Raw.norm (p : Raw X) : Raw X := p.foldr (fun m acc => insertMin (dedup m) acc) []

/-- No monomial contains another (and none is repeated). -/
def Antichain (p : Raw X) : Prop := p.Pairwise fun a b => ¬ a ⊆ b ∧ ¬ b ⊆ a

theorem insertMin_mem {m a : List X} {acc : Raw X} (h : a ∈ insertMin m acc) : a = m ∨ a ∈ acc := by
  unfold insertMin at h; split at h
  · exact .inr h
  · rcases List.mem_cons.1 h with h | h
    · exact .inl h
    · exact .inr (List.mem_filter.1 h).1

theorem insertMin_antichain (m : List X) {acc : Raw X} (h : Antichain acc) :
    Antichain (insertMin m acc) := by
  unfold insertMin; split
  · exact h
  · rename_i hany
    refine List.pairwise_cons.2 ⟨fun b hb => ?_, h.filter _⟩
    obtain ⟨hb, hmb⟩ := List.mem_filter.1 hb
    refine ⟨fun hs => by simp [sub_iff.2 hs] at hmb, fun hs => hany ?_⟩
    exact List.any_eq_true.2 ⟨b, hb, sub_iff.2 hs⟩

theorem insertMin_eval {K : Type} [Just K] (ν : X → K) (m : List X) (acc : Raw X) :
    Raw.eval ν (insertMin m acc) = Mono.eval ν m ⊔ Raw.eval ν acc := by
  unfold insertMin; split
  · rename_i hany
    obtain ⟨a, ha, hs⟩ := List.any_eq_true.1 hany
    rw [Raw.eval_mem ν ha, ← add_assoc, add_comm (Mono.eval ν m),
      absorb_le (Mono.eval_subset ν (sub_iff.1 hs)), ← Raw.eval_mem ν ha]
  · rw [Raw.eval, Raw.eval_filter ν (fun a => !sub m a) acc, add_comm (Raw.eval ν _), ← add_assoc]
    congr 1
    refine (Raw.eval_absorb ν fun b hb => ?_).symm
    simpa [sub_iff] using (List.mem_filter.1 hb).2

theorem norm_antichain (p : Raw X) : Antichain (Raw.norm p) := by
  induction p with
  | nil => exact List.Pairwise.nil
  | cons m p ih => exact insertMin_antichain _ ih

theorem norm_nodup (p : Raw X) : ∀ m ∈ Raw.norm p, m.Nodup := by
  induction p with
  | nil => intro m h; cases h
  | cons m p ih =>
    intro a ha
    rcases insertMin_mem ha with rfl | ha
    · exact nodup_dedup m
    · exact ih a ha

/-- Normalization preserves the value in every bounded distributive lattice. -/
theorem eval_norm {K : Type} [Just K] (ν : X → K) (p : Raw X) :
    Raw.eval ν (Raw.norm p) = Raw.eval ν p := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    simp only [Raw.norm, List.foldr_cons] at ih ⊢
    rw [insertMin_eval, ih, Raw.eval,
      Mono.eval_seteq ν (fun _ h => mem_dedup.1 h) (fun _ h => mem_dedup.2 h)]

omit [DecidableEq X] in
theorem antichain_eq {p : Raw X} (h : Antichain p) {a b : List X} (ha : a ∈ p) (hb : b ∈ p)
    (hs : a ⊆ b) : a = b := by
  induction p with
  | nil => cases ha
  | cons c p ih =>
    obtain ⟨hc, hp⟩ := List.pairwise_cons.1 h
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd hs (hc b hb').1
    · subst hb'; exact absurd hs (hc a ha').2
    · exact ih hp ha' hb'

/-- CANONICITY. Two antichains with the same Boolean function have the same monomials, up to the
order of their tokens. With `eval_norm`, the normal form is the free bounded distributive lattice's
element: the polynomial is determined by what it says about every view. -/
theorem canonical {p q : Raw X} (hp : Antichain p) (_hq : Antichain q)
    (h : ∀ ν : X → Bool, Raw.eval ν p = Raw.eval ν q) :
    ∀ a ∈ p, ∃ b ∈ q, a ⊆ b ∧ b ⊆ a := by
  intro a ha
  have hqa := (Raw.eval_bool _ q).1 ((h fun x => decide (x ∈ a)) ▸
    (Raw.eval_bool _ p).2 ⟨a, ha, fun x hx => by simpa using hx⟩)
  obtain ⟨b, hb, hba⟩ := hqa
  have hba : b ⊆ a := fun x hx => by simpa using hba x hx
  have hpb := (Raw.eval_bool _ p).1 ((h fun x => decide (x ∈ b)).symm ▸
    (Raw.eval_bool _ q).2 ⟨b, hb, fun x hx => by simpa using hx⟩)
  obtain ⟨a', ha', hab⟩ := hpb
  have hab : a' ⊆ b := fun x hx => by simpa using hab x hx
  have := antichain_eq hp ha' ha (fun x hx => hba (hab hx))
  subst this
  exact ⟨b, hb, hab, hba⟩

#tooth canonical by mutation Antichain := fun _ => True

/-- Without the normal form the written list is not canonical: `a + a·b` and `a` agree at every
view and differ in their monomials. -/
theorem raw_not_canonical :
    (∀ ν : Bool → Bool, Raw.eval ν [[true], [true, false]] = Raw.eval ν [[true]]) ∧
    ¬ ∀ a ∈ ([[true], [true, false]] : Raw Bool), ∃ b ∈ ([[true]] : Raw Bool), a ⊆ b ∧ b ⊆ a := by
  refine ⟨fun ν => ?_, fun h => ?_⟩
  · cases h : ν true <;> cases ν false <;>
      simp [Raw.eval, Mono.eval, h, Just.add, Just.mul, Just.one, Just.zero]
  · obtain ⟨b, hb, hs, -⟩ := h [true, false] (by simp)
    simp at hb; subst hb; simpa using hs (List.mem_cons_of_mem _ List.mem_cons_self)

/-- A polynomial in normal form. -/
structure Poly (X : Type) [DecidableEq X] where
  ms : Raw X
  antichain : Antichain ms
  nodup : ∀ m ∈ ms, m.Nodup

namespace Poly

def ofRaw (p : Raw X) : Poly X := ⟨Raw.norm p, norm_antichain p, norm_nodup p⟩
def zero : Poly X := ofRaw []
def one : Poly X := ofRaw [[]]
def var (x : X) : Poly X := ofRaw [[x]]
def add (p q : Poly X) : Poly X := ofRaw (p.ms ++ q.ms)
def mul (p q : Poly X) : Poly X := ofRaw (Raw.mul p.ms q.ms)
def eval {K : Type} [Just K] (ν : X → K) (p : Poly X) : K := Raw.eval ν p.ms

variable {K : Type} [Just K] (ν : X → K)

theorem eval_ofRaw (p : Raw X) : (ofRaw p).eval ν = Raw.eval ν p := eval_norm ν p
theorem eval_zero : (zero : Poly X).eval ν = Just.zero := rfl
theorem eval_one : (one : Poly X).eval ν = Just.one := by
  simp [one, eval_ofRaw, Raw.eval, Mono.eval, add_zero]
theorem eval_var (x : X) : (var x).eval ν = ν x := by
  simp [var, eval_ofRaw, Raw.eval, Mono.eval, add_zero, mul_one]
theorem eval_add (p q : Poly X) : (add p q).eval ν = p.eval ν ⊔ q.eval ν := by
  rw [add, eval_ofRaw, Raw.eval_append]; rfl
theorem eval_mul (p q : Poly X) : (mul p q).eval ν = p.eval ν ⊓ q.eval ν := by
  rw [mul, eval_ofRaw, Raw.eval_mul]; rfl

/-- Normal forms with the same Boolean function name the same token sets. -/
theorem canonical {p q : Poly X} (h : ∀ ν : X → Bool, p.eval ν = q.eval ν) :
    ∀ a ∈ p.ms, ∃ b ∈ q.ms, a ⊆ b ∧ b ⊆ a :=
  Obend.Just.canonical p.antichain q.antichain h

end Poly
end

/-! ## The dual evaluation: what is missing, by name -/

section
variable {X : Type}

/-- Substitute a written polynomial for every token. -/
def Raw.subst {Y : Type} (σ : X → Raw Y) (p : Raw X) : Raw Y :=
  p.flatMap fun m => m.foldr (fun x acc => Raw.mul (σ x) acc) [[]]

theorem Raw.eval_subst {Y K : Type} [Just K] (ν : Y → K) (σ : X → Raw Y) (p : Raw X) :
    Raw.eval ν (Raw.subst σ p) = Raw.eval (fun x => Raw.eval ν (σ x)) p := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    have hm : Raw.eval ν (m.foldr (fun x acc => Raw.mul (σ x) acc) [[]]) =
        Mono.eval (fun x => Raw.eval ν (σ x)) m := by
      induction m with
      | nil => simp [Raw.eval, Mono.eval, add_zero]
      | cons x m ihm => simp [Raw.eval_mul, Mono.eval, ihm]
    simp only [Raw.subst, List.flatMap_cons, Raw.eval_append] at ih ⊢
    rw [ih, hm, Raw.eval]

/-- The dual valuation of a Boolean view: a token that holds is `1`, one that does not is itself. -/
def missingVal (ν : X → Bool) (x : X) : Raw X := if ν x then [[]] else [[x]]

/-- What remains unsatisfied of a polynomial at a view. -/
def Raw.missing (ν : X → Bool) (p : Raw X) : Raw X := Raw.subst (missingVal ν) p

/-- The Boolean image of the dual evaluation, with nothing restored, is the Boolean evaluation. -/
theorem missing_bool (ν : X → Bool) (p : Raw X) :
    Raw.eval (fun _ => false) (Raw.missing ν p) = Raw.eval ν p := by
  rw [Raw.missing, Raw.eval_subst]
  refine Raw.eval_congr fun _ _ x _ => ?_
  unfold missingVal; cases ν x <;> rfl

/-- The dual evaluation of one monomial is one monomial: its tokens that do not hold. -/
theorem missing_mono (ν : X → Bool) (m : List X) :
    Raw.missing ν [m] = [m.filter fun x => !ν x] := by
  simp only [Raw.missing, Raw.subst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  induction m with
  | nil => rfl
  | cons x m ih =>
    rw [List.foldr_cons, ih]; unfold missingVal
    cases h : ν x <;> simp [Raw.mul, h]

theorem missing_mono_mem (ν : X → Bool) (m : List X) :
    ∃ a, Raw.missing ν [m] = [a] ∧ ∀ x, x ∈ a ↔ x ∈ m ∧ ν x = false :=
  ⟨_, missing_mono ν m, fun x => by simp⟩

#tooth missing_mono_mem by mutation missingVal := fun _ _ => [[]]

end

#assert_axioms Just.add_idem Just.zero_mul astra3_absorptive astra3_not_idem Mono.eval_subset
  Raw.eval_mul Raw.eval_congr Mono.eval_zero_tok Mono.eval_bool Raw.eval_bool insertMin_antichain
  insertMin_eval norm_antichain norm_nodup eval_norm canonical raw_not_canonical Poly.eval_add
  Poly.eval_mul Poly.eval_one Poly.eval_var Poly.canonical Raw.eval_subst missing_bool missing_mono
  missing_mono_mem

end Obend.Just
end
