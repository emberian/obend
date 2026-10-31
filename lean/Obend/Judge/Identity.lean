module
/-
# Obend.Judge.Identity — conditional Boolean-algebra identities, encoded into CNF with a theorem

The vision study's first rule for a solver row (§6.3 (a)): a format needs an `encode` from an obend
object, and `encode_sound` is where the real work is. The object here is a CONDITIONAL IDENTITY over
bits (`Identity`): a hypothesis and two lists of expressions over input variables, claiming that
wherever the hypothesis holds the two lists agree (`Holds`). `encode` is the Tseitin encoding of
"the hypothesis holds and some pair differs"; `encode_sound` says an unsatisfiable encoding means
the identity holds, so `translation` makes every LRAT refutation of `encode d` a proof of `Holds d`
(`Judge.Translation.sound`).

- `tseitin_spec`: the encoding of an expression, from a fresh-variable counter, has a model
  extending any assignment of the variables below the counter, in which the expression's literal
  has the expression's value; `tseitin_bounds`: every literal it emits is a variable in range.
- `encode_sound`: a refutation of `encode d` is a proof of `Holds d`. An identity that is not
  well-formed (a variable out of range) is encoded as the empty formula, which nothing refutes.

The instance exercised (`noCarry n`): for `n`-bit `x` and `y` with `x AND y = 0`, the ripple-carry sum
`x + y` (with its carry out) is `x OR y` (with a zero bit): the conditional identity
`x &&& y = 0 → x + y = x ||| y`, stated over the adder's bits.
-/
public import Obend.Judge.Lrat

@[expose] public section
namespace Obend.Judge.Identity
open Obend.Judge.Lrat
set_option autoImplicit false

/-! ## Expressions -/

inductive BExp where
  | var (i : Nat)
  | const (b : Bool)
  | not (a : BExp)
  | and (a b : BExp)
  | or (a b : BExp)
  | xor (a b : BExp)
  deriving DecidableEq, Repr, Inhabited

def BExp.eval (σ : Nat → Bool) : BExp → Bool
  | .var i => σ i
  | .const b => b
  | .not a => !a.eval σ
  | .and a b => a.eval σ && b.eval σ
  | .or a b => a.eval σ || b.eval σ
  | .xor a b => Bool.xor (a.eval σ) (b.eval σ)

/-- Every variable is in `[1, n)`. -/
def BExp.varsIn (n : Nat) : BExp → Bool
  | .var i => 0 < i && i < n
  | .const _ => true
  | .not a => a.varsIn n
  | .and a b | .or a b | .xor a b => a.varsIn n && b.varsIn n

/-! ## The Tseitin encoding -/

def andGate (o a b : Int) : List Lrat.Clause := [[-o, a], [-o, b], [o, -a, -b]]
def orGate (o a b : Int) : List Lrat.Clause := [[o, -a], [o, -b], [-o, a, b]]
def xorGate (o a b : Int) : List Lrat.Clause := [[-o, a, b], [-o, -a, -b], [o, -a, b], [o, a, -b]]

/-- The literal standing for an expression, its clauses, and the next fresh variable. -/
def tseitin : BExp → Nat → Int × List Lrat.Clause × Nat
  | .var i, n => ((i : Int), [], n)
  | .const b, n => ((n : Int), [[if b then (n : Int) else -(n : Int)]], n + 1)
  | .not a, n =>
    let r := tseitin a n
    (-r.1, r.2.1, r.2.2)
  | .and a b, n =>
    let ra := tseitin a n
    let rb := tseitin b ra.2.2
    ((rb.2.2 : Int), ra.2.1 ++ rb.2.1 ++ andGate rb.2.2 ra.1 rb.1, rb.2.2 + 1)
  | .or a b, n =>
    let ra := tseitin a n
    let rb := tseitin b ra.2.2
    ((rb.2.2 : Int), ra.2.1 ++ rb.2.1 ++ orGate rb.2.2 ra.1 rb.1, rb.2.2 + 1)
  | .xor a b, n =>
    let ra := tseitin a n
    let rb := tseitin b ra.2.2
    ((rb.2.2 : Int), ra.2.1 ++ rb.2.1 ++ xorGate rb.2.2 ra.1 rb.1, rb.2.2 + 1)

/-! ## Assignments that agree below a bound -/

def Agree (σ σ' : Nat → Bool) (n : Nat) : Prop := ∀ v, v < n → σ v = σ' v

/-- A literal names a variable in `[1, m)`. -/
def InRange (m : Nat) (l : Int) : Prop := 0 < l.natAbs ∧ l.natAbs < m

theorem agree_mono {σ σ' : Nat → Bool} {n m : Nat} (h : Agree σ σ' m) (le : n ≤ m) : Agree σ σ' n :=
  fun v hv => h v (Nat.lt_of_lt_of_le hv le)

theorem agree_trans {σ σ' σ'' : Nat → Bool} {n : Nat} (h : Agree σ σ' n) (h' : Agree σ' σ'' n) : Agree σ σ'' n :=
  fun v hv => (h v hv).trans (h' v hv)

theorem litTrue_congr {σ σ' : Nat → Bool} {m : Nat} {l : Int} (h : Agree σ σ' m) (hl : InRange m l) :
    litTrue σ l = litTrue σ' l := by
  unfold litTrue; rw [h _ hl.2]

theorem sat_congr {σ σ' : Nat → Bool} {m : Nat} {c : Lrat.Clause} (h : Agree σ σ' m) (hc : ∀ x ∈ c, InRange m x)
    (hs : Sat σ c) : Sat σ' c := by
  obtain ⟨l, hl, ht⟩ := hs
  exact ⟨l, hl, (litTrue_congr h (hc l hl)).symm.trans ht⟩

theorem eval_congr {σ σ' : Nat → Bool} {n : Nat} (h : Agree σ σ' n) : ∀ (e : BExp), e.varsIn n = true → e.eval σ = e.eval σ'
  | .var i, hv => by simp only [BExp.varsIn, Bool.and_eq_true, decide_eq_true_eq] at hv; exact h i hv.2
  | .const _, _ => rfl
  | .not a, hv => by simp only [BExp.eval]; rw [eval_congr h a hv]
  | .and a b, hv | .or a b, hv | .xor a b, hv => by
    simp only [BExp.varsIn, Bool.and_eq_true] at hv
    simp only [BExp.eval]; rw [eval_congr h a hv.1, eval_congr h b hv.2]

theorem varsIn_mono {n m : Nat} (le : n ≤ m) : ∀ (e : BExp), e.varsIn n = true → e.varsIn m = true
  | .var i, hv => by simp only [BExp.varsIn, Bool.and_eq_true, decide_eq_true_eq] at hv ⊢; omega
  | .const _, _ => rfl
  | .not a, hv => varsIn_mono le a hv
  | .and a b, hv | .or a b, hv | .xor a b, hv => by
    simp only [BExp.varsIn, Bool.and_eq_true] at hv ⊢; exact ⟨varsIn_mono le a hv.1, varsIn_mono le b hv.2⟩

/-- Update one variable. -/
def set (σ : Nat → Bool) (x : Nat) (b : Bool) : Nat → Bool := fun v => if v = x then b else σ v

theorem agree_set (σ : Nat → Bool) {x n : Nat} (b : Bool) (le : n ≤ x) : Agree σ (set σ x b) n := by
  intro v hv; simp [set, show v ≠ x by omega]

theorem inRange_neg {m : Nat} {l : Int} (h : InRange m l) : InRange m (-l) := by
  unfold InRange at *; rw [Int.natAbs_neg]; exact h

theorem inRange_mono {m m' : Nat} {l : Int} (h : InRange m l) (le : m ≤ m') : InRange m' l :=
  ⟨h.1, Nat.lt_of_lt_of_le h.2 le⟩

theorem inRange_var {m : Nat} (x : Nat) (h0 : 0 < x) (h : x < m) : InRange m (x : Int) := by
  unfold InRange; omega

/-! ## Bounds -/

/-- **Bounds**: the counter grows, and every literal emitted names a variable below the new counter. -/
theorem tseitin_bounds : ∀ (e : BExp) (n : Nat), 0 < n → e.varsIn n = true →
    n ≤ (tseitin e n).2.2 ∧ InRange (tseitin e n).2.2 (tseitin e n).1 ∧
      ∀ c ∈ (tseitin e n).2.1, ∀ x ∈ c, InRange (tseitin e n).2.2 x
  | .var i, n, _, hv => by
    simp only [BExp.varsIn, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [tseitin]
    exact ⟨Nat.le_refl _, inRange_var i hv.1 hv.2, by simp⟩
  | .const b, n, hn, _ => by
    simp only [tseitin]
    refine ⟨Nat.le_succ _, inRange_var n hn (Nat.lt_succ_self _), ?_⟩
    intro c hc x hx
    simp only [List.mem_singleton] at hc; subst hc
    simp only [List.mem_singleton] at hx; subst hx
    cases b
    · exact inRange_neg (inRange_var n hn (Nat.lt_succ_self _))
    · exact inRange_var n hn (Nat.lt_succ_self _)
  | .not a, n, hn, hv => by
    obtain ⟨le, hl, hc⟩ := tseitin_bounds a n hn hv
    simp only [tseitin]
    exact ⟨le, inRange_neg hl, hc⟩
  | .and a b, n, hn, hv | .or a b, n, hn, hv | .xor a b, n, hn, hv => by
    simp only [BExp.varsIn, Bool.and_eq_true] at hv
    obtain ⟨le₁, hl₁, hc₁⟩ := tseitin_bounds a n hn hv.1
    obtain ⟨le₂, hl₂, hc₂⟩ := tseitin_bounds b (tseitin a n).2.2 (Nat.lt_of_lt_of_le hn le₁)
      (varsIn_mono le₁ b hv.2)
    have hpos : 0 < (tseitin b (tseitin a n).2.2).2.2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hn le₁) le₂
    have ho : InRange ((tseitin b (tseitin a n).2.2).2.2 + 1) ((tseitin b (tseitin a n).2.2).2.2 : Int) :=
      inRange_var _ hpos (Nat.lt_succ_self _)
    have ha : InRange ((tseitin b (tseitin a n).2.2).2.2 + 1) (tseitin a n).1 :=
      inRange_mono hl₁ (Nat.le_trans le₂ (Nat.le_succ _))
    have hb : InRange ((tseitin b (tseitin a n).2.2).2.2 + 1) (tseitin b (tseitin a n).2.2).1 :=
      inRange_mono hl₂ (Nat.le_succ _)
    simp only [tseitin]
    refine ⟨Nat.le_trans le₁ (Nat.le_trans le₂ (Nat.le_succ _)), ho, ?_⟩
    intro c hc x hx
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact inRange_mono (hc₁ c hc x hx) (Nat.le_trans le₂ (Nat.le_succ _))
    · exact inRange_mono (hc₂ c hc x hx) (Nat.le_succ _)
    · simp only [andGate, orGate, xorGate, List.mem_cons, List.mem_nil_iff, or_false] at hc
      repeat' (first | (rcases hc with rfl | hc) | (subst hc))
      all_goals
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        repeat' (first | (rcases hx with rfl | hx) | (subst hx))
        all_goals first | exact ho | exact inRange_neg ho | exact ha | exact inRange_neg ha | exact hb | exact inRange_neg hb

/-! ## The model -/

theorem sat_of_any {σ : Nat → Bool} {c : Lrat.Clause} (h : c.any (litTrue σ) = true) : Sat σ c := by
  obtain ⟨l, hl, ht⟩ := List.any_eq_true.1 h
  exact ⟨l, hl, ht⟩

theorem and_sat (σ : Nat → Bool) {o a b : Int} (h0a : a ≠ 0) (h0b : b ≠ 0) (h0o : o ≠ 0)
    (ho : litTrue σ o = (litTrue σ a && litTrue σ b)) : ∀ c ∈ andGate o a b, Sat σ c := by
  intro c hc
  simp only [andGate, List.mem_cons, List.mem_nil_iff, or_false] at hc
  have na := litTrue_neg σ h0a; have nb := litTrue_neg σ h0b; have no := litTrue_neg σ h0o
  cases hA : litTrue σ a <;> cases hB : litTrue σ b <;> rw [hA, hB] at ho <;>
    rcases hc with rfl | rfl | rfl <;> apply sat_of_any <;> simp [na, nb, no, hA, hB, ho]

theorem or_sat (σ : Nat → Bool) {o a b : Int} (h0a : a ≠ 0) (h0b : b ≠ 0) (h0o : o ≠ 0)
    (ho : litTrue σ o = (litTrue σ a || litTrue σ b)) : ∀ c ∈ orGate o a b, Sat σ c := by
  intro c hc
  simp only [orGate, List.mem_cons, List.mem_nil_iff, or_false] at hc
  have na := litTrue_neg σ h0a; have nb := litTrue_neg σ h0b; have no := litTrue_neg σ h0o
  cases hA : litTrue σ a <;> cases hB : litTrue σ b <;> rw [hA, hB] at ho <;>
    rcases hc with rfl | rfl | rfl <;> apply sat_of_any <;> simp [na, nb, no, hA, hB, ho]

theorem xor_sat (σ : Nat → Bool) {o a b : Int} (h0a : a ≠ 0) (h0b : b ≠ 0) (h0o : o ≠ 0)
    (ho : litTrue σ o = Bool.xor (litTrue σ a) (litTrue σ b)) : ∀ c ∈ xorGate o a b, Sat σ c := by
  intro c hc
  simp only [xorGate, List.mem_cons, List.mem_nil_iff, or_false] at hc
  have na := litTrue_neg σ h0a; have nb := litTrue_neg σ h0b; have no := litTrue_neg σ h0o
  cases hA : litTrue σ a <;> cases hB : litTrue σ b <;> rw [hA, hB] at ho <;>
    rcases hc with rfl | rfl | rfl | rfl <;> apply sat_of_any <;> simp [na, nb, no, hA, hB, ho]

theorem inRange_ne_zero {m : Nat} {l : Int} (h : InRange m l) : l ≠ 0 := by
  intro e; subst e; exact absurd h.1 (by simp)

/-- The binary case of the model, for any gate whose clauses are satisfied when its output has
the operation's value. -/
theorem tseitin_spec_bin (op : Bool → Bool → Bool) (gate : Int → Int → Int → List Lrat.Clause)
    (gate_sat : ∀ (σ : Nat → Bool) {o a b : Int}, a ≠ 0 → b ≠ 0 → o ≠ 0 →
      litTrue σ o = op (litTrue σ a) (litTrue σ b) → ∀ c ∈ gate o a b, Sat σ c)
    (a b : BExp) (n : Nat) (hn : 0 < n) (hva : a.varsIn n = true) (hvb : b.varsIn n = true)
    (iha : ∀ σ : Nat → Bool, ∃ σ', Agree σ σ' n ∧ (∀ c ∈ (tseitin a n).2.1, Sat σ' c) ∧
      litTrue σ' (tseitin a n).1 = a.eval σ)
    (ihb : ∀ σ : Nat → Bool, ∃ σ', Agree σ σ' (tseitin a n).2.2 ∧ (∀ c ∈ (tseitin b (tseitin a n).2.2).2.1, Sat σ' c) ∧
      litTrue σ' (tseitin b (tseitin a n).2.2).1 = b.eval σ)
    (σ : Nat → Bool) :
    let ra := tseitin a n
    let rb := tseitin b ra.2.2
    ∃ σ', Agree σ σ' n ∧ (∀ c ∈ ra.2.1 ++ rb.2.1 ++ gate rb.2.2 ra.1 rb.1, Sat σ' c) ∧
      litTrue σ' (rb.2.2 : Int) = op (a.eval σ) (b.eval σ) := by
  intro ra rb
  obtain ⟨le₁, hl₁, hc₁⟩ := tseitin_bounds a n hn hva
  obtain ⟨le₂, hl₂, hc₂⟩ := tseitin_bounds b ra.2.2 (Nat.lt_of_lt_of_le hn le₁) (varsIn_mono le₁ b hvb)
  obtain ⟨σa, ag₁, sat₁, lit₁⟩ := iha σ
  obtain ⟨σb, ag₂, sat₂, lit₂⟩ := ihb σa
  let o := rb.2.2
  let σo := set σb o (op (litTrue σb ra.1) (litTrue σb rb.1))
  have agbo : Agree σb σo o := agree_set σb _ (Nat.le_refl _)
  have hpos : 0 < o := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hn le₁) le₂
  refine ⟨σo, ?_, ?_, ?_⟩
  · exact agree_trans (agree_trans ag₁ (agree_mono ag₂ le₁)) (agree_mono agbo (Nat.le_trans le₁ le₂))
  · intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact sat_congr (agree_trans (agree_mono ag₂ (Nat.le_refl _)) (agree_mono agbo le₂)) (hc₁ c hc) (sat₁ c hc)
    · exact sat_congr agbo (hc₂ c hc) (sat₂ c hc)
    · apply gate_sat σo (inRange_ne_zero hl₁) (inRange_ne_zero hl₂) (by omega) _ c hc
      have ho : litTrue σo (o : Int) = op (litTrue σb ra.1) (litTrue σb rb.1) := by
        simp [litTrue, σo, set, show o ≠ 0 by omega]
      rw [ho, litTrue_congr agbo (inRange_mono hl₁ le₂), litTrue_congr agbo hl₂]
  · have ho : litTrue σo (o : Int) = op (litTrue σb ra.1) (litTrue σb rb.1) := by
      simp [litTrue, σo, set, show o ≠ 0 by omega]
    rw [ho, lit₂, ← litTrue_congr ag₂ hl₁, lit₁, eval_congr ag₁ b hvb]

/-- **The encoding has a model with the expression's value**: from any assignment of the variables
below the counter, an assignment agreeing with it there satisfies every emitted clause and gives
the expression's literal the expression's value. -/
theorem tseitin_spec : ∀ (e : BExp) (n : Nat), 0 < n → e.varsIn n = true → ∀ σ : Nat → Bool,
    ∃ σ', Agree σ σ' n ∧ (∀ c ∈ (tseitin e n).2.1, Sat σ' c) ∧ litTrue σ' (tseitin e n).1 = e.eval σ
  | .var i, n, _, hv, σ => by
    simp only [BExp.varsIn, Bool.and_eq_true, decide_eq_true_eq] at hv
    refine ⟨σ, fun _ _ => rfl, by simp [tseitin], ?_⟩
    simp [tseitin, litTrue, BExp.eval, show i ≠ 0 by omega]
  | .const b, n, _, _, σ => by
    refine ⟨set σ n b, agree_set σ b (Nat.le_refl _), ?_, ?_⟩
    · intro c hc
      simp only [tseitin, List.mem_singleton] at hc; subst hc
      refine ⟨if b then (n : Int) else -(n : Int), List.mem_singleton_self _, ?_⟩
      cases b <;> simp [litTrue, set] <;> omega
    · cases b <;> simp [tseitin, litTrue, set, BExp.eval] <;> omega
  | .not a, n, hn, hv, σ => by
    obtain ⟨σ', ag, sat, lit⟩ := tseitin_spec a n hn hv σ
    obtain ⟨_, hl, _⟩ := tseitin_bounds a n hn hv
    refine ⟨σ', ag, sat, ?_⟩
    simp only [tseitin, BExp.eval]
    rw [litTrue_neg σ' (inRange_ne_zero hl), lit]
  | .and a b, n, hn, hv, σ => by
    simp only [BExp.varsIn, Bool.and_eq_true] at hv
    obtain ⟨le₁, _, _⟩ := tseitin_bounds a n hn hv.1
    exact tseitin_spec_bin (· && ·) andGate (fun σ _ _ _ h0a h0b h0o ho => and_sat σ h0a h0b h0o ho) a b n hn hv.1 hv.2
      (tseitin_spec a n hn hv.1)
      (tseitin_spec b _ (Nat.lt_of_lt_of_le hn le₁) (varsIn_mono le₁ b hv.2)) σ
  | .or a b, n, hn, hv, σ => by
    simp only [BExp.varsIn, Bool.and_eq_true] at hv
    obtain ⟨le₁, _, _⟩ := tseitin_bounds a n hn hv.1
    exact tseitin_spec_bin (· || ·) orGate (fun σ _ _ _ h0a h0b h0o ho => or_sat σ h0a h0b h0o ho) a b n hn hv.1 hv.2
      (tseitin_spec a n hn hv.1)
      (tseitin_spec b _ (Nat.lt_of_lt_of_le hn le₁) (varsIn_mono le₁ b hv.2)) σ
  | .xor a b, n, hn, hv, σ => by
    simp only [BExp.varsIn, Bool.and_eq_true] at hv
    obtain ⟨le₁, _, _⟩ := tseitin_bounds a n hn hv.1
    exact tseitin_spec_bin Bool.xor xorGate (fun σ _ _ _ h0a h0b h0o ho => xor_sat σ h0a h0b h0o ho) a b n hn hv.1 hv.2
      (tseitin_spec a n hn hv.1)
      (tseitin_spec b _ (Nat.lt_of_lt_of_le hn le₁) (varsIn_mono le₁ b hv.2)) σ

/-! ## Conditional identities -/

/-- Wherever `hyp` holds, `lhs` and `rhs` agree, over the input variables `1 … inputs`. -/
structure Identity where
  name : String
  inputs : Nat
  hyp : BExp
  lhs : List BExp
  rhs : List BExp
  deriving DecidableEq, Repr, Inhabited

def Identity.Holds (d : Identity) : Prop :=
  ∀ σ : Nat → Bool, d.hyp.eval σ = true → d.lhs.map (BExp.eval σ) = d.rhs.map (BExp.eval σ)

/-- Some pair differs (or the lists have different lengths). -/
def differ : List BExp → List BExp → BExp
  | [], [] => .const false
  | a :: as, b :: bs => .or (.xor a b) (differ as bs)
  | _, _ => .const true

theorem differ_false (σ : Nat → Bool) : ∀ (l r : List BExp),
    (differ l r).eval σ = false ↔ l.map (BExp.eval σ) = r.map (BExp.eval σ)
  | [], [] => by simp [differ, BExp.eval]
  | [], _ :: _ => by simp [differ, BExp.eval]
  | _ :: _, [] => by simp [differ, BExp.eval]
  | a :: as, b :: bs => by
    simp only [differ, BExp.eval, Bool.or_eq_false_iff, List.map_cons, List.cons.injEq, differ_false σ as bs]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨by cases ha : a.eval σ <;> cases hb : b.eval σ <;> simp_all, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨by rw [h]; simp, h'⟩

/-- The violation: the hypothesis holds and some pair differs. -/
def Identity.violation (d : Identity) : BExp := .and d.hyp (differ d.lhs d.rhs)

def differ_varsIn (n : Nat) : List BExp → List BExp → Bool
  | l, r => (l ++ r).all (·.varsIn n)

def Identity.wellFormed (d : Identity) : Bool := d.violation.varsIn (d.inputs + 1)

/-- **The encoding**: the violation's Tseitin clauses and its literal asserted; the empty formula for
an identity that is not well-formed. -/
def encode (d : Identity) : Cnf :=
  if d.wellFormed then
    let r := tseitin d.violation (d.inputs + 1)
    ⟨r.2.2 - 1, r.2.1 ++ [[r.1]]⟩
  else ⟨0, []⟩

/-- **The encoding is sound**: an unsatisfiable encoding means the identity holds. -/
theorem encode_sound (d : Identity) (h : Unsat (encode d)) : d.Holds := by
  unfold encode at h
  split at h
  · rename_i wf
    intro σ hyp
    apply (differ_false σ d.lhs d.rhs).1
    cases hd : (differ d.lhs d.rhs).eval σ
    · rfl
    · exfalso
      obtain ⟨σ', _, sat, lit⟩ := tseitin_spec d.violation (d.inputs + 1) (Nat.succ_pos _) wf σ
      apply h σ'
      intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact sat c hc
      · refine ⟨_, List.mem_singleton_self _, ?_⟩
        rw [lit]; simp [Identity.violation, BExp.eval, hyp, hd]
  · exact absurd (fun _ h => by cases h) (h (fun _ => false))

/-- The translation of conditional identities into LRAT's objects. -/
def translation : Judge.Translation Lrat.format Identity Identity.Holds where
  encode := encode
  encode_sound d _ h := encode_sound d h

/-! ## The instance: no-carry addition is OR -/

/-- Bit `i` of `x` (variables `1 … n`) and of `y` (variables `n+1 … 2n`). -/
def xBit (i : Nat) : BExp := .var (i + 1)
def yBit (n i : Nat) : BExp := .var (n + i + 1)

/-- The ripple-carry sum bits of `x + y` and the carry out. -/
def adder (n : Nat) : List BExp :=
  let step := fun (acc : List BExp × BExp) (i : Nat) =>
    let x := xBit i; let y := yBit n i; let c := acc.2
    (acc.1 ++ [.xor (.xor x y) c], .or (.and x y) (.and c (.xor x y)))
  let r := (List.range n).foldl step ([], .const false)
  r.1 ++ [r.2]

/-- `x &&& y = 0`. -/
def disjoint (n : Nat) : BExp :=
  (List.range n).foldl (fun acc i => .and acc (.not (.and (xBit i) (yBit n i)))) (.const true)

/-- `x ||| y` with a zero top bit. -/
def orBits (n : Nat) : List BExp := (List.range n).map (fun i => .or (xBit i) (yBit n i)) ++ [.const false]

/-- **`x &&& y = 0 → x + y = x ||| y`** for `n`-bit `x` and `y`. -/
def noCarry (n : Nat) : Identity := ⟨s!"no-carry-add-is-or-{n}", 2 * n, disjoint n, adder n, orBits n⟩

end Obend.Judge.Identity
end
