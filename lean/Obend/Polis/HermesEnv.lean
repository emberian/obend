module
/-
# Obend.Polis.HermesEnv — Explainable `WhyTrue` / `WhyFalse` Policy Algebra & Multi-Turn Hermes Rooms

Formalizes the Polisware / Hermes communication & room-governance policy substrate:
1. Boolean-closed + `k`-of-`n` threshold `PolicyPred` / `PolicyList` with WHNF-clean `evalPolicy`.
2. Mutual `WhyTrue` / `WhyFalse` trees with `strictlyIncreasing` threshold indices preventing forgery.
3. Constructive `0 Classical` `evalWhy` (`PSum (WhyTrue Atom) (WhyFalse Atom)`), `evalWhy_sound_and_complete`.
4. Multi-turn Hermes room attenuation, `SortedU64Set` revocation, and `hermesRoom_multi_turn_attenuation_sound`.
-/
public import Obend.Logic.EnvHarness
public import Obend.Core.SortedArray
public section
namespace Obend.Polis.HermesEnv
open Obend.Core.SortedArray (SortedU64Set SimulatesSet insertKey)
set_option autoImplicit false
/-! ## 1. Boolean-Closed + `k`-of-`n` Threshold Policy Syntax & Evaluation -/
mutual
/-- First-order explainable room/governance policy predicate over atomic facts `Atom`. -/
inductive PolicyPred (Atom : Type) where
  | atom (a : Atom)
  | tt
  | ff
  | neg (p : PolicyPred Atom)
  | conj (p q : PolicyPred Atom)
  | disj (p q : PolicyPred Atom)
  | threshold (k : Nat) (ps : PolicyList Atom)
/-- Explicit mutual list of `PolicyPred` children for WHNF-clean structural recursion. -/
inductive PolicyList (Atom : Type) where
  | nil
  | cons (head : PolicyPred Atom) (tail : PolicyList Atom)
end
deriving instance DecidableEq, Repr for PolicyPred, PolicyList
@[expose] def PolicyList.ofList {Atom : Type} : List (PolicyPred Atom) → PolicyList Atom
  | [] => .nil
  | p :: ps => .cons p (PolicyList.ofList ps)
@[expose] def PolicyList.length {Atom : Type} : PolicyList Atom → Nat
  | .nil => 0
  | .cons _ tl => 1 + tl.length
@[expose] def PolicyList.get? {Atom : Type} : PolicyList Atom → Nat → Option (PolicyPred Atom)
  | .nil, _ => none
  | .cons hd _, 0 => some hd
  | .cons _ tl, i + 1 => tl.get? i
mutual
/-- Reference boolean evaluator for `PolicyPred`. -/
@[expose] def evalPolicy {Atom : Type} (env : Atom → Bool) : PolicyPred Atom → Bool
  | .atom a => env a
  | .tt => true
  | .ff => false
  | .neg p => !(evalPolicy env p)
  | .conj p q => evalPolicy env p && evalPolicy env q
  | .disj p q => evalPolicy env p || evalPolicy env q
  | .threshold k ps => decide (k ≤ countTruePolicy env ps)
termination_by structural p => p
/-- Count satisfied children in a `PolicyList`. -/
@[expose] def countTruePolicy {Atom : Type} (env : Atom → Bool) : PolicyList Atom → Nat
  | .nil => 0
  | .cons hd tl => (if evalPolicy env hd then 1 else 0) + countTruePolicy env tl
termination_by structural ps => ps
end
def countFalsePolicy {Atom : Type} (env : Atom → Bool) : PolicyList Atom → Nat
  | .nil => 0
  | .cons hd tl => (if evalPolicy env hd then 0 else 1) + countFalsePolicy env tl
theorem countTrue_add_countFalse {Atom : Type} (env : Atom → Bool) :
    ∀ (ps : PolicyList Atom), countTruePolicy env ps + countFalsePolicy env ps = ps.length
  | .nil => rfl
  | .cons hd tl => by
    have ih := countTrue_add_countFalse env tl
    cases h : evalPolicy env hd <;> simp [countTruePolicy, countFalsePolicy, PolicyList.length, h] <;> omega
/-! ## 2. Mutual `WhyTrue` & `WhyFalse` Proof/Refusal Trees with Strictly Increasing Thresholds -/
/-- Decidable strict-monotonicity check `idx₀ < idx₁ < ...` preventing duplicate-index threshold forgery. -/
@[expose] def strictlyIncreasingFrom : Nat → List Nat → Bool
  | _, [] => true
  | lb, i :: is => decide (lb ≤ i) && strictlyIncreasingFrom (i + 1) is
@[expose] def strictlyIncreasing (idxs : List Nat) : Bool :=
  strictlyIncreasingFrom 0 idxs
theorem strictlyIncreasingFrom_mono {lb₁ lb₂ : Nat} (hLe : lb₁ ≤ lb₂) :
    ∀ (idxs : List Nat), strictlyIncreasingFrom lb₂ idxs = true → strictlyIncreasingFrom lb₁ idxs = true
  | [], _ => rfl
  | i :: is, h => by
    simp only [strictlyIncreasingFrom, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨by omega, h.2⟩
mutual
/-- Positive auditable explanation tree witnessing why a `PolicyPred Atom` evaluated to `true`. -/
inductive WhyTrue (Atom : Type) where
  | atomTrue (a : Atom)
  | ttIntro
  | negFalse (sub : WhyFalse Atom)
  | conjBoth (left right : WhyTrue Atom)
  | disjLeft (left : WhyTrue Atom)
  | disjRight (right : WhyTrue Atom)
  | thresholdSat (entries : WhyTrueThreshold Atom)
/-- Negative counterfactual explanation tree witnessing why a `PolicyPred Atom` evaluated to `false`. -/
inductive WhyFalse (Atom : Type) where
  | atomFalse (a : Atom)
  | ffIntro
  | negTrue (sub : WhyTrue Atom)
  | conjFailLeft (left : WhyFalse Atom)
  | conjFailRight (right : WhyFalse Atom)
  | disjNeither (left right : WhyFalse Atom)
  | thresholdShortfall (entries : WhyFalseThreshold Atom)
/-- Indexed child-witness list for `WhyTrue.thresholdSat`. -/
inductive WhyTrueThreshold (Atom : Type) where
  | nil
  | cons (idx : Nat) (witness : WhyTrue Atom) (rest : WhyTrueThreshold Atom)
/-- Indexed child-refusal list for `WhyFalse.thresholdShortfall`. -/
inductive WhyFalseThreshold (Atom : Type) where
  | nil
  | cons (idx : Nat) (witness : WhyFalse Atom) (rest : WhyFalseThreshold Atom)
end
deriving instance DecidableEq, Repr for WhyTrue, WhyFalse, WhyTrueThreshold, WhyFalseThreshold
def WhyTrueThreshold.indices {Atom : Type} : WhyTrueThreshold Atom → List Nat
  | .nil => []
  | .cons idx _ rest => idx :: rest.indices
def WhyTrueThreshold.length {Atom : Type} : WhyTrueThreshold Atom → Nat
  | .nil => 0
  | .cons _ _ rest => 1 + rest.length
def WhyFalseThreshold.indices {Atom : Type} : WhyFalseThreshold Atom → List Nat
  | .nil => []
  | .cons idx _ rest => idx :: rest.indices
def WhyFalseThreshold.length {Atom : Type} : WhyFalseThreshold Atom → Nat
  | .nil => 0
  | .cons _ _ rest => 1 + rest.length
mutual
/-- Executable verifier checking that `WhyTrue Atom` validly proves `p` under `env`. -/
@[expose] def checkWhyTrue {Atom : Type} [DecidableEq Atom] (env : Atom → Bool) :
    PolicyPred Atom → WhyTrue Atom → Bool
  | .atom a, .atomTrue a' => (a == a') && env a
  | .tt, .ttIntro => true
  | .neg p, .negFalse sub => checkWhyFalse env p sub
  | .conj p q, .conjBoth wl wr => checkWhyTrue env p wl && checkWhyTrue env q wr
  | .disj p _, .disjLeft wl => checkWhyTrue env p wl
  | .disj _ q, .disjRight wr => checkWhyTrue env q wr
  | .threshold k ps, .thresholdSat es =>
    decide (k ≤ es.length) && strictlyIncreasing es.indices && checkWhyTrueEntries 0 env ps es
  | _, _ => false
termination_by structural p _ => p
/-- Executable verifier checking that `WhyFalse Atom` validly refutes `p` under `env`. -/
@[expose] def checkWhyFalse {Atom : Type} [DecidableEq Atom] (env : Atom → Bool) :
    PolicyPred Atom → WhyFalse Atom → Bool
  | .atom a, .atomFalse a' => (a == a') && !(env a)
  | .ff, .ffIntro => true
  | .neg p, .negTrue sub => checkWhyTrue env p sub
  | .conj p _, .conjFailLeft wl => checkWhyFalse env p wl
  | .conj _ q, .conjFailRight wr => checkWhyFalse env q wr
  | .disj p q, .disjNeither wl wr => checkWhyFalse env p wl && checkWhyFalse env q wr
  | .threshold k ps, .thresholdShortfall es =>
    decide (ps.length < k + es.length) && strictlyIncreasing es.indices && checkWhyFalseEntries 0 env ps es
  | _, _ => false
termination_by structural p _ => p
/-- Verify strictly ordered positive threshold entries starting at child offset `offset`. -/
def checkWhyTrueEntries {Atom : Type} [DecidableEq Atom] (offset : Nat) (env : Atom → Bool) :
    PolicyList Atom → WhyTrueThreshold Atom → Bool
  | _, .nil => true
  | .nil, .cons _ _ _ => false
  | .cons hd tl, .cons idx w rest =>
    if idx == offset then
      checkWhyTrue env hd w && checkWhyTrueEntries (offset + 1) env tl rest
    else if decide (offset + 1 ≤ idx) then
      checkWhyTrueEntries (offset + 1) env tl (.cons idx w rest)
    else false
termination_by structural ps _ => ps
/-- Verify strictly ordered negative threshold entries starting at child offset `offset`. -/
def checkWhyFalseEntries {Atom : Type} [DecidableEq Atom] (offset : Nat) (env : Atom → Bool) :
    PolicyList Atom → WhyFalseThreshold Atom → Bool
  | _, .nil => true
  | .nil, .cons _ _ _ => false
  | .cons hd tl, .cons idx w rest =>
    if idx == offset then
      checkWhyFalse env hd w && checkWhyFalseEntries (offset + 1) env tl rest
    else if decide (offset + 1 ≤ idx) then
      checkWhyFalseEntries (offset + 1) env tl (.cons idx w rest)
    else false
termination_by structural ps _ => ps
end
mutual
/-- Declarative validity of a positive explanation `WhyTrue Atom` (independent of `DecidableEq Atom`). -/
inductive ValidWhyTrue {Atom : Type} (env : Atom → Bool) : PolicyPred Atom → WhyTrue Atom → Prop where
  | atomTrue {a : Atom} : env a = true → ValidWhyTrue env (.atom a) (.atomTrue a)
  | ttIntro : ValidWhyTrue env .tt .ttIntro
  | negFalse {p : PolicyPred Atom} {sub : WhyFalse Atom} :
      ValidWhyFalse env p sub → ValidWhyTrue env (.neg p) (.negFalse sub)
  | conjBoth {p q : PolicyPred Atom} {wl wr : WhyTrue Atom} :
      ValidWhyTrue env p wl → ValidWhyTrue env q wr → ValidWhyTrue env (.conj p q) (.conjBoth wl wr)
  | disjLeft {p q : PolicyPred Atom} {wl : WhyTrue Atom} :
      ValidWhyTrue env p wl → ValidWhyTrue env (.disj p q) (.disjLeft wl)
  | disjRight {p q : PolicyPred Atom} {wr : WhyTrue Atom} :
      ValidWhyTrue env q wr → ValidWhyTrue env (.disj p q) (.disjRight wr)
  | thresholdSat {k : Nat} {ps : PolicyList Atom} {es : WhyTrueThreshold Atom} :
      k ≤ es.length →
      strictlyIncreasing es.indices = true →
      ValidWhyTrueEntries env 0 ps es →
      ValidWhyTrue env (.threshold k ps) (.thresholdSat es)
/-- Declarative validity of a counterfactual refusal `WhyFalse Atom`. -/
inductive ValidWhyFalse {Atom : Type} (env : Atom → Bool) : PolicyPred Atom → WhyFalse Atom → Prop where
  | atomFalse {a : Atom} : env a = false → ValidWhyFalse env (.atom a) (.atomFalse a)
  | ffIntro : ValidWhyFalse env .ff .ffIntro
  | negTrue {p : PolicyPred Atom} {sub : WhyTrue Atom} :
      ValidWhyTrue env p sub → ValidWhyFalse env (.neg p) (.negTrue sub)
  | conjFailLeft {p q : PolicyPred Atom} {wl : WhyFalse Atom} :
      ValidWhyFalse env p wl → ValidWhyFalse env (.conj p q) (.conjFailLeft wl)
  | conjFailRight {p q : PolicyPred Atom} {wr : WhyFalse Atom} :
      ValidWhyFalse env q wr → ValidWhyFalse env (.conj p q) (.conjFailRight wr)
  | disjNeither {p q : PolicyPred Atom} {wl wr : WhyFalse Atom} :
      ValidWhyFalse env p wl → ValidWhyFalse env q wr → ValidWhyFalse env (.disj p q) (.disjNeither wl wr)
  | thresholdShortfall {k : Nat} {ps : PolicyList Atom} {es : WhyFalseThreshold Atom} :
      ps.length < k + es.length →
      strictlyIncreasing es.indices = true →
      ValidWhyFalseEntries env 0 ps es →
      ValidWhyFalse env (.threshold k ps) (.thresholdShortfall es)
inductive ValidWhyTrueEntries {Atom : Type} (env : Atom → Bool) :
    Nat → PolicyList Atom → WhyTrueThreshold Atom → Prop where
  | nil {offset : Nat} {ps : PolicyList Atom} : ValidWhyTrueEntries env offset ps .nil
  | hit {offset : Nat} {hd : PolicyPred Atom} {tl : PolicyList Atom}
      {w : WhyTrue Atom} {rest : WhyTrueThreshold Atom} :
      ValidWhyTrue env hd w →
      ValidWhyTrueEntries env (offset + 1) tl rest →
      ValidWhyTrueEntries env offset (.cons hd tl) (.cons offset w rest)
  | skip {offset idx : Nat} {hd : PolicyPred Atom} {tl : PolicyList Atom}
      {w : WhyTrue Atom} {rest : WhyTrueThreshold Atom} :
      offset + 1 ≤ idx →
      ValidWhyTrueEntries env (offset + 1) tl (.cons idx w rest) →
      ValidWhyTrueEntries env offset (.cons hd tl) (.cons idx w rest)
inductive ValidWhyFalseEntries {Atom : Type} (env : Atom → Bool) :
    Nat → PolicyList Atom → WhyFalseThreshold Atom → Prop where
  | nil {offset : Nat} {ps : PolicyList Atom} : ValidWhyFalseEntries env offset ps .nil
  | hit {offset : Nat} {hd : PolicyPred Atom} {tl : PolicyList Atom}
      {w : WhyFalse Atom} {rest : WhyFalseThreshold Atom} :
      ValidWhyFalse env hd w →
      ValidWhyFalseEntries env (offset + 1) tl rest →
      ValidWhyFalseEntries env offset (.cons hd tl) (.cons offset w rest)
  | skip {offset idx : Nat} {hd : PolicyPred Atom} {tl : PolicyList Atom}
      {w : WhyFalse Atom} {rest : WhyFalseThreshold Atom} :
      offset + 1 ≤ idx →
      ValidWhyFalseEntries env (offset + 1) tl (.cons idx w rest) →
      ValidWhyFalseEntries env offset (.cons hd tl) (.cons idx w rest)
end
/-! ## 3. Soundness of `WhyTrue` / `WhyFalse` & Constructive `0 Classical` `evalWhy` -/
mutual
theorem validWhyTrue_sound {Atom : Type} {env : Atom → Bool} :
    ∀ {p : PolicyPred Atom} {w : WhyTrue Atom}, ValidWhyTrue env p w → evalPolicy env p = true
  | .atom _, .atomTrue _, .atomTrue ha => ha
  | .tt, .ttIntro, .ttIntro => rfl
  | .neg p, .negFalse sub, .negFalse hSub => by
    simp [evalPolicy, validWhyFalse_sound hSub]
  | .conj p q, .conjBoth wl wr, .conjBoth hl hr => by
    simp [evalPolicy, validWhyTrue_sound hl, validWhyTrue_sound hr]
  | .disj p _, .disjLeft wl, .disjLeft hl => by
    simp [evalPolicy, validWhyTrue_sound hl]
  | .disj _ q, .disjRight wr, .disjRight hr => by
    simp [evalPolicy, validWhyTrue_sound hr]
  | .threshold k ps, .thresholdSat es, .thresholdSat hLen _ hEntries => by
    have hBound := validWhyTrueEntries_le_count hEntries
    simp only [evalPolicy, decide_eq_true_eq]; omega
termination_by structural p _ _ => p
theorem validWhyFalse_sound {Atom : Type} {env : Atom → Bool} :
    ∀ {p : PolicyPred Atom} {w : WhyFalse Atom}, ValidWhyFalse env p w → evalPolicy env p = false
  | .atom _, .atomFalse _, .atomFalse ha => ha
  | .ff, .ffIntro, .ffIntro => rfl
  | .neg p, .negTrue sub, .negTrue hSub => by
    simp [evalPolicy, validWhyTrue_sound hSub]
  | .conj p _, .conjFailLeft wl, .conjFailLeft hl => by
    simp [evalPolicy, validWhyFalse_sound hl]
  | .conj _ q, .conjFailRight wr, .conjFailRight hr => by
    simp [evalPolicy, validWhyFalse_sound hr]
  | .disj p q, .disjNeither wl wr, .disjNeither hl hr => by
    simp [evalPolicy, validWhyFalse_sound hl, validWhyFalse_sound hr]
  | .threshold k ps, .thresholdShortfall es, .thresholdShortfall hShort _ hEntries => by
    have hBound := validWhyFalseEntries_le_count hEntries
    have hSum := countTrue_add_countFalse env ps
    simp only [evalPolicy, decide_eq_false_iff_not]; omega
termination_by structural p _ _ => p
theorem validWhyTrueEntries_le_count {Atom : Type} {env : Atom → Bool} :
    ∀ {offset : Nat} {ps : PolicyList Atom} {es : WhyTrueThreshold Atom},
      ValidWhyTrueEntries env offset ps es → es.length ≤ countTruePolicy env ps
  | _, _, .nil, .nil => Nat.zero_le _
  | _, .cons hd tl, .cons _ w rest, .hit hw hrest => by
    have hHd := validWhyTrue_sound hw
    have ih := validWhyTrueEntries_le_count hrest
    simp only [WhyTrueThreshold.length, countTruePolicy, hHd, ↓reduceIte]; omega
  | _, .cons hd tl, .cons _ _ _, .skip _ hrest => by
    have ih := validWhyTrueEntries_le_count hrest
    cases h : evalPolicy env hd <;> simp [countTruePolicy, h] <;> omega
termination_by structural _ ps _ _ => ps
theorem validWhyFalseEntries_le_count {Atom : Type} {env : Atom → Bool} :
    ∀ {offset : Nat} {ps : PolicyList Atom} {es : WhyFalseThreshold Atom},
      ValidWhyFalseEntries env offset ps es → es.length ≤ countFalsePolicy env ps
  | _, _, .nil, .nil => Nat.zero_le _
  | _, .cons hd tl, .cons _ w rest, .hit hw hrest => by
    have hHd := validWhyFalse_sound hw
    have ih := validWhyFalseEntries_le_count hrest
    simp [WhyFalseThreshold.length, countFalsePolicy, hHd]; omega
  | _, .cons hd tl, .cons _ _ _, .skip _ hrest => by
    have ih := validWhyFalseEntries_le_count hrest
    cases h : evalPolicy env hd <;> simp [countFalsePolicy, h] <;> omega
termination_by structural _ ps _ _ => ps
end
example : ∃ (env : Nat → Bool) (p : PolicyPred Nat) (w : WhyTrue Nat), ValidWhyTrue env p w :=
  ⟨fun _ => true, .tt, .ttIntro, .ttIntro⟩
example : ∃ (env : Nat → Bool) (p : PolicyPred Nat) (w : WhyFalse Nat), ValidWhyFalse env p w :=
  ⟨fun _ => false, .ff, .ffIntro, .ffIntro⟩
mutual
theorem checkWhyTrue_sound {Atom : Type} [DecidableEq Atom] {env : Atom → Bool} :
    ∀ {p : PolicyPred Atom} {w : WhyTrue Atom}, checkWhyTrue env p w = true → ValidWhyTrue env p w
  | .atom a, .atomTrue a', h => by
    simp only [checkWhyTrue, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, ha⟩; exact .atomTrue ha
  | .tt, .ttIntro, _ => .ttIntro
  | .neg p, .negFalse sub, h => .negFalse (checkWhyFalse_sound (by simpa [checkWhyTrue] using h))
  | .conj p q, .conjBoth wl wr, h => by
    simp only [checkWhyTrue, Bool.and_eq_true] at h
    exact .conjBoth (checkWhyTrue_sound h.1) (checkWhyTrue_sound h.2)
  | .disj p _, .disjLeft wl, h => .disjLeft (checkWhyTrue_sound (by simpa [checkWhyTrue] using h))
  | .disj _ q, .disjRight wr, h => .disjRight (checkWhyTrue_sound (by simpa [checkWhyTrue] using h))
  | .threshold k ps, .thresholdSat es, h => by
    simp only [checkWhyTrue, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .thresholdSat h.1.1 h.1.2 (checkWhyTrueEntries_sound h.2)
  | .atom _, .ttIntro, h | .atom _, .negFalse _, h | .atom _, .conjBoth _ _, h
  | .atom _, .disjLeft _, h | .atom _, .disjRight _, h | .atom _, .thresholdSat _, h
  | .tt, .atomTrue _, h | .tt, .negFalse _, h | .tt, .conjBoth _ _, h
  | .tt, .disjLeft _, h | .tt, .disjRight _, h | .tt, .thresholdSat _, h
  | .ff, _, h
  | .neg _, .atomTrue _, h | .neg _, .ttIntro, h | .neg _, .conjBoth _ _, h
  | .neg _, .disjLeft _, h | .neg _, .disjRight _, h | .neg _, .thresholdSat _, h
  | .conj _ _, .atomTrue _, h | .conj _ _, .ttIntro, h | .conj _ _, .negFalse _, h
  | .conj _ _, .disjLeft _, h | .conj _ _, .disjRight _, h | .conj _ _, .thresholdSat _, h
  | .disj _ _, .atomTrue _, h | .disj _ _, .ttIntro, h | .disj _ _, .negFalse _, h
  | .disj _ _, .conjBoth _ _, h | .disj _ _, .thresholdSat _, h
  | .threshold _ _, .atomTrue _, h | .threshold _ _, .ttIntro, h | .threshold _ _, .negFalse _, h
  | .threshold _ _, .conjBoth _ _, h | .threshold _ _, .disjLeft _, h | .threshold _ _, .disjRight _, h => by
    cases h
termination_by structural p _ _ => p
theorem checkWhyFalse_sound {Atom : Type} [DecidableEq Atom] {env : Atom → Bool} :
    ∀ {p : PolicyPred Atom} {w : WhyFalse Atom}, checkWhyFalse env p w = true → ValidWhyFalse env p w
  | .atom a, .atomFalse a', h => by
    simp only [checkWhyFalse, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    rcases h with ⟨rfl, ha⟩; exact .atomFalse ha
  | .ff, .ffIntro, _ => .ffIntro
  | .neg p, .negTrue sub, h => .negTrue (checkWhyTrue_sound (by simpa [checkWhyFalse] using h))
  | .conj p _, .conjFailLeft wl, h => .conjFailLeft (checkWhyFalse_sound (by simpa [checkWhyFalse] using h))
  | .conj _ q, .conjFailRight wr, h => .conjFailRight (checkWhyFalse_sound (by simpa [checkWhyFalse] using h))
  | .disj p q, .disjNeither wl wr, h => by
    simp only [checkWhyFalse, Bool.and_eq_true] at h
    exact .disjNeither (checkWhyFalse_sound h.1) (checkWhyFalse_sound h.2)
  | .threshold k ps, .thresholdShortfall es, h => by
    simp only [checkWhyFalse, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .thresholdShortfall h.1.1 h.1.2 (checkWhyFalseEntries_sound h.2)
  | .atom _, .ffIntro, h | .atom _, .negTrue _, h | .atom _, .conjFailLeft _, h
  | .atom _, .conjFailRight _, h | .atom _, .disjNeither _ _, h | .atom _, .thresholdShortfall _, h
  | .tt, _, h
  | .ff, .atomFalse _, h | .ff, .negTrue _, h | .ff, .conjFailLeft _, h
  | .ff, .conjFailRight _, h | .ff, .disjNeither _ _, h | .ff, .thresholdShortfall _, h
  | .neg _, .atomFalse _, h | .neg _, .ffIntro, h | .neg _, .conjFailLeft _, h
  | .neg _, .conjFailRight _, h | .neg _, .disjNeither _ _, h | .neg _, .thresholdShortfall _, h
  | .conj _ _, .atomFalse _, h | .conj _ _, .ffIntro, h | .conj _ _, .negTrue _, h
  | .conj _ _, .disjNeither _ _, h | .conj _ _, .thresholdShortfall _, h
  | .disj _ _, .atomFalse _, h | .disj _ _, .ffIntro, h | .disj _ _, .negTrue _, h
  | .disj _ _, .conjFailLeft _, h | .disj _ _, .conjFailRight _, h | .disj _ _, .thresholdShortfall _, h
  | .threshold _ _, .atomFalse _, h | .threshold _ _, .ffIntro, h | .threshold _ _, .negTrue _, h
  | .threshold _ _, .conjFailLeft _, h | .threshold _ _, .conjFailRight _, h | .threshold _ _, .disjNeither _ _, h => by
    cases h
termination_by structural p _ _ => p
theorem checkWhyTrueEntries_sound {Atom : Type} [DecidableEq Atom] {offset : Nat} {env : Atom → Bool} :
    ∀ {ps : PolicyList Atom} {es : WhyTrueThreshold Atom},
      checkWhyTrueEntries offset env ps es = true → ValidWhyTrueEntries env offset ps es
  | _, .nil, _ => .nil
  | .nil, .cons _ _ _, h => by cases h
  | .cons hd tl, .cons idx w rest, h => by
    simp only [checkWhyTrueEntries] at h
    by_cases hEq : idx = offset
    · subst hEq; simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at h
      exact .hit (checkWhyTrue_sound h.1) (checkWhyTrueEntries_sound h.2)
    · have hNe : (idx == offset) = false := beq_eq_false_iff_ne.mpr hEq
      simp only [hNe, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i hGe
        exact .skip (of_decide_eq_true hGe) (checkWhyTrueEntries_sound h)
      · cases h
termination_by structural ps _ _ => ps
theorem checkWhyFalseEntries_sound {Atom : Type} [DecidableEq Atom] {offset : Nat} {env : Atom → Bool} :
    ∀ {ps : PolicyList Atom} {es : WhyFalseThreshold Atom},
      checkWhyFalseEntries offset env ps es = true → ValidWhyFalseEntries env offset ps es
  | _, .nil, _ => .nil
  | .nil, .cons _ _ _, h => by cases h
  | .cons hd tl, .cons idx w rest, h => by
    simp only [checkWhyFalseEntries] at h
    by_cases hEq : idx = offset
    · subst hEq; simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at h
      exact .hit (checkWhyFalse_sound h.1) (checkWhyFalseEntries_sound h.2)
    · have hNe : (idx == offset) = false := beq_eq_false_iff_ne.mpr hEq
      simp only [hNe, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i hGe
        exact .skip (of_decide_eq_true hGe) (checkWhyFalseEntries_sound h)
      · cases h
termination_by structural ps _ _ => ps
end
mutual
/-- Constructive `0 Classical` evaluator returning either a positive `WhyTrue Atom` proof tree or a
negative `WhyFalse Atom` counterfactual refusal tree. -/
@[expose] def evalWhy {Atom : Type} (env : Atom → Bool) :
    PolicyPred Atom → PSum (WhyTrue Atom) (WhyFalse Atom)
  | .atom a =>
    if env a then .inl (.atomTrue a) else .inr (.atomFalse a)
  | .tt => .inl .ttIntro
  | .ff => .inr .ffIntro
  | .neg p =>
    match evalWhy env p with
    | .inl wt => .inr (.negTrue wt)
    | .inr wf => .inl (.negFalse wf)
  | .conj p q =>
    match evalWhy env p with
    | .inr wfl => .inr (.conjFailLeft wfl)
    | .inl wtl =>
      match evalWhy env q with
      | .inl wtr => .inl (.conjBoth wtl wtr)
      | .inr wfr => .inr (.conjFailRight wfr)
  | .disj p q =>
    match evalWhy env p with
    | .inl wtl => .inl (.disjLeft wtl)
    | .inr wfl =>
      match evalWhy env q with
      | .inl wtr => .inl (.disjRight wtr)
      | .inr wfr => .inr (.disjNeither wfl wfr)
  | .threshold k ps =>
    let (ts, fs) := collectThresholdWhy 0 env ps
    if decide (k ≤ ts.length) then .inl (.thresholdSat ts)
    else .inr (.thresholdShortfall fs)
termination_by structural p => p
/-- Single-pass partition of `ps` into strictly increasing positive and negative child explanations. -/
def collectThresholdWhy {Atom : Type} (offset : Nat) (env : Atom → Bool) :
    PolicyList Atom → WhyTrueThreshold Atom × WhyFalseThreshold Atom
  | .nil => (.nil, .nil)
  | .cons hd tl =>
    let (ts, fs) := collectThresholdWhy (offset + 1) env tl
    match evalWhy env hd with
    | .inl wt => (.cons offset wt ts, fs)
    | .inr wf => (ts, .cons offset wf fs)
termination_by structural ps => ps
end
mutual
private theorem evalWhy_valid {Atom : Type} (env : Atom → Bool) :
    ∀ (p : PolicyPred Atom),
      match evalWhy env p with
      | .inl wt => ValidWhyTrue env p wt
      | .inr wf => ValidWhyFalse env p wf
  | .atom a => by
    unfold evalWhy
    cases ha : env a
    · simp; exact .atomFalse ha
    · simp; exact .atomTrue ha
  | .tt => .ttIntro
  | .ff => .ffIntro
  | .neg p => by
    unfold evalWhy
    have ih := evalWhy_valid env p
    cases h : evalWhy env p with
    | inl wt => rw [h] at ih; exact .negTrue ih
    | inr wf => rw [h] at ih; exact .negFalse ih
  | .conj p q => by
    unfold evalWhy
    have ihP := evalWhy_valid env p
    cases hp : evalWhy env p with
    | inr wfl => rw [hp] at ihP; exact .conjFailLeft ihP
    | inl wtl =>
      rw [hp] at ihP
      have ihQ := evalWhy_valid env q
      cases hq : evalWhy env q with
      | inl wtr => rw [hq] at ihQ; exact .conjBoth ihP ihQ
      | inr wfr => rw [hq] at ihQ; exact .conjFailRight ihQ
  | .disj p q => by
    unfold evalWhy
    have ihP := evalWhy_valid env p
    cases hp : evalWhy env p with
    | inl wtl => rw [hp] at ihP; exact .disjLeft ihP
    | inr wfl =>
      rw [hp] at ihP
      have ihQ := evalWhy_valid env q
      cases hq : evalWhy env q with
      | inl wtr => rw [hq] at ihQ; exact .disjRight ihQ
      | inr wfr => rw [hq] at ihQ; exact .disjNeither ihP ihQ
  | .threshold k ps => by
    unfold evalWhy
    have hCol := collectThresholdWhy_spec 0 env ps
    rcases hC : collectThresholdWhy 0 env ps with ⟨ts, fs⟩
    rw [hC] at hCol; dsimp only at hCol ⊢
    rcases hCol with ⟨hIncT, hValT, hLenT, hIncF, hValF, hLenF⟩
    have hSum := countTrue_add_countFalse env ps
    by_cases hk : k ≤ ts.length
    · simp only [decide_eq_true hk, ↓reduceIte]
      exact .thresholdSat hk hIncT hValT
    · simp only [decide_eq_false hk, Bool.false_eq_true, ↓reduceIte]
      exact .thresholdShortfall (by omega) hIncF hValF
termination_by structural p => p
private theorem collectThresholdWhy_spec {Atom : Type} (offset : Nat) (env : Atom → Bool) :
    ∀ (ps : PolicyList Atom),
      let (ts, fs) := collectThresholdWhy offset env ps
      strictlyIncreasingFrom offset ts.indices = true ∧
      ValidWhyTrueEntries env offset ps ts ∧
      ts.length = countTruePolicy env ps ∧
      strictlyIncreasingFrom offset fs.indices = true ∧
      ValidWhyFalseEntries env offset ps fs ∧
      fs.length = countFalsePolicy env ps
  | .nil => ⟨rfl, .nil, rfl, rfl, .nil, rfl⟩
  | .cons hd tl => by
    have ihHd := evalWhy_valid env hd
    have ihTl := collectThresholdWhy_spec (offset + 1) env tl
    unfold collectThresholdWhy
    rcases hRec : collectThresholdWhy (offset + 1) env tl with ⟨ts, fs⟩
    rw [hRec] at ihTl; dsimp only at ihTl ⊢
    rcases ihTl with ⟨hIncT, hValT, hLenT, hIncF, hValF, hLenF⟩
    cases hHd : evalWhy env hd with
    | inl wt =>
      rw [hHd] at ihHd; dsimp only
      have hEvTrue : evalPolicy env hd = true := validWhyTrue_sound ihHd
      refine ⟨?_, .hit ihHd hValT, ?_, strictlyIncreasingFrom_mono (by omega) fs.indices hIncF,
        ?_, ?_⟩
      · simp [WhyTrueThreshold.indices, strictlyIncreasingFrom, hIncT]
      · simp only [WhyTrueThreshold.length, countTruePolicy, hEvTrue, ↓reduceIte, hLenT]
      · cases fs with
        | nil => exact .nil
        | cons idx wf rest =>
          simp only [WhyFalseThreshold.indices, strictlyIncreasingFrom, Bool.and_eq_true,
            decide_eq_true_eq] at hIncF
          exact .skip hIncF.1 hValF
      · simp only [countFalsePolicy, hEvTrue, ↓reduceIte, hLenF]; omega
    | inr wf =>
      rw [hHd] at ihHd; dsimp only
      have hEvFalse : evalPolicy env hd = false := validWhyFalse_sound ihHd
      refine ⟨strictlyIncreasingFrom_mono (by omega) ts.indices hIncT, ?_, ?_, ?_, .hit ihHd hValF, ?_⟩
      · cases ts with
        | nil => exact .nil
        | cons idx wt rest =>
          simp only [WhyTrueThreshold.indices, strictlyIncreasingFrom, Bool.and_eq_true,
            decide_eq_true_eq] at hIncT
          exact .skip hIncT.1 hValT
      · simp only [countTruePolicy, hEvFalse, Bool.false_eq_true, ↓reduceIte, hLenT]; omega
      · simp [WhyFalseThreshold.indices, strictlyIncreasingFrom, hIncF]
      · simp only [WhyFalseThreshold.length, countFalsePolicy, hEvFalse, Bool.false_eq_true, ↓reduceIte, hLenF]
termination_by structural ps => ps
end
mutual
theorem validWhyTrue_checks {Atom : Type} [DecidableEq Atom] {env : Atom → Bool} :
    ∀ {p : PolicyPred Atom} {w : WhyTrue Atom}, ValidWhyTrue env p w → checkWhyTrue env p w = true
  | .atom a, .atomTrue _, .atomTrue ha => by simp [checkWhyTrue, ha]
  | .tt, .ttIntro, .ttIntro => rfl
  | .neg _, .negFalse _, .negFalse hSub => by simp [checkWhyTrue, validWhyFalse_checks hSub]
  | .conj _ _, .conjBoth _ _, .conjBoth hl hr => by
    simp [checkWhyTrue, validWhyTrue_checks hl, validWhyTrue_checks hr]
  | .disj _ _, .disjLeft _, .disjLeft hl => by simp [checkWhyTrue, validWhyTrue_checks hl]
  | .disj _ _, .disjRight _, .disjRight hr => by simp [checkWhyTrue, validWhyTrue_checks hr]
  | .threshold _ _, .thresholdSat _, .thresholdSat hLen hInc hEs => by
    simp [checkWhyTrue, decide_eq_true hLen, hInc, validWhyTrueEntries_checks hEs]
termination_by structural p _ _ => p
theorem validWhyFalse_checks {Atom : Type} [DecidableEq Atom] {env : Atom → Bool} :
    ∀ {p : PolicyPred Atom} {w : WhyFalse Atom}, ValidWhyFalse env p w → checkWhyFalse env p w = true
  | .atom a, .atomFalse _, .atomFalse ha => by simp [checkWhyFalse, ha]
  | .ff, .ffIntro, .ffIntro => rfl
  | .neg _, .negTrue _, .negTrue hSub => by simp [checkWhyFalse, validWhyTrue_checks hSub]
  | .conj _ _, .conjFailLeft _, .conjFailLeft hl => by simp [checkWhyFalse, validWhyFalse_checks hl]
  | .conj _ _, .conjFailRight _, .conjFailRight hr => by simp [checkWhyFalse, validWhyFalse_checks hr]
  | .disj _ _, .disjNeither _ _, .disjNeither hl hr => by
    simp [checkWhyFalse, validWhyFalse_checks hl, validWhyFalse_checks hr]
  | .threshold _ _, .thresholdShortfall _, .thresholdShortfall hShort hInc hEs => by
    simp [checkWhyFalse, decide_eq_true hShort, hInc, validWhyFalseEntries_checks hEs]
termination_by structural p _ _ => p
private theorem validWhyTrueEntries_checks {Atom : Type} [DecidableEq Atom] {env : Atom → Bool} :
    ∀ {offset : Nat} {ps : PolicyList Atom} {es : WhyTrueThreshold Atom},
      ValidWhyTrueEntries env offset ps es → checkWhyTrueEntries offset env ps es = true
  | _, .nil, .nil, .nil => rfl
  | _, .cons _ _, .nil, .nil => rfl
  | _, .cons _ _, .cons _ _ _, .hit hw hrest => by
    simp [checkWhyTrueEntries, validWhyTrue_checks hw, validWhyTrueEntries_checks hrest]
  | offset, .cons _ _, .cons idx _ _, .skip hGe hrest => by
    have hNe : (idx == offset) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp [checkWhyTrueEntries, hNe, decide_eq_true hGe, validWhyTrueEntries_checks hrest]
termination_by structural _ ps _ _ => ps
private theorem validWhyFalseEntries_checks {Atom : Type} [DecidableEq Atom] {env : Atom → Bool} :
    ∀ {offset : Nat} {ps : PolicyList Atom} {es : WhyFalseThreshold Atom},
      ValidWhyFalseEntries env offset ps es → checkWhyFalseEntries offset env ps es = true
  | _, .nil, .nil, .nil => rfl
  | _, .cons _ _, .nil, .nil => rfl
  | _, .cons _ _, .cons _ _ _, .hit hw hrest => by
    simp [checkWhyFalseEntries, validWhyFalse_checks hw, validWhyFalseEntries_checks hrest]
  | offset, .cons _ _, .cons idx _ _, .skip hGe hrest => by
    have hNe : (idx == offset) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp [checkWhyFalseEntries, hNe, decide_eq_true hGe, validWhyFalseEntries_checks hrest]
termination_by structural _ ps _ _ => ps
end
/-- **Constructive `WhyTrue`/`WhyFalse` Soundness, Completeness & Exclusivity (`evalWhy_sound_and_complete`)**:
`evalWhy` constructively partitions every `(env, p)` (`0 Classical.choice`) into either a valid
`WhyTrue Atom` proof tree or a valid `WhyFalse Atom` counterfactual refusal tree, matching `evalPolicy`
and `checkWhyTrue` / `checkWhyFalse` with mutual exclusivity. -/
theorem evalWhy_sound_and_complete {Atom : Type} [DecidableEq Atom]
    (env : Atom → Bool) (p : PolicyPred Atom) :
    (match evalWhy env p with
     | .inl wt =>
       checkWhyTrue env p wt = true ∧ ValidWhyTrue env p wt ∧
       evalPolicy env p = true ∧ ¬ (∃ wf, ValidWhyFalse env p wf)
     | .inr wf =>
       checkWhyFalse env p wf = true ∧ ValidWhyFalse env p wf ∧
       evalPolicy env p = false ∧ ¬ (∃ wt, ValidWhyTrue env p wt)) ∧
    ((∃ wt, checkWhyTrue env p wt = true) ↔ evalPolicy env p = true) ∧
    ((∃ wf, checkWhyFalse env p wf = true) ↔ evalPolicy env p = false) := by
  have hVal := evalWhy_valid env p
  refine ⟨?_, ?_, ?_⟩
  · cases hEv : evalWhy env p with
    | inl wt =>
      rw [hEv] at hVal
      have hT := validWhyTrue_sound hVal
      refine ⟨validWhyTrue_checks hVal, hVal, hT, ?_⟩
      rintro ⟨wf, hwf⟩
      have hF := validWhyFalse_sound hwf
      rw [hT] at hF; cases hF
    | inr wf =>
      rw [hEv] at hVal
      have hF := validWhyFalse_sound hVal
      refine ⟨validWhyFalse_checks hVal, hVal, hF, ?_⟩
      rintro ⟨wt, hwt⟩
      have hT := validWhyTrue_sound hwt
      rw [hT] at hF; cases hF
  · constructor
    · rintro ⟨wt, hChk⟩; exact validWhyTrue_sound (checkWhyTrue_sound hChk)
    · intro hTrue
      cases hEv : evalWhy env p with
      | inl wt => rw [hEv] at hVal; exact ⟨wt, validWhyTrue_checks hVal⟩
      | inr wf =>
        rw [hEv] at hVal
        have hF := validWhyFalse_sound hVal
        rw [hTrue] at hF; cases hF
  · constructor
    · rintro ⟨wf, hChk⟩; exact validWhyFalse_sound (checkWhyFalse_sound hChk)
    · intro hFalse
      cases hEv : evalWhy env p with
      | inr wf => rw [hEv] at hVal; exact ⟨wf, validWhyFalse_checks hVal⟩
      | inl wt =>
        rw [hEv] at hVal
        have hT := validWhyTrue_sound hVal
        rw [hFalse] at hT; cases hT
/-! ## 4. Multi-Turn Hermes Room Capability Attenuation & Explainable Moderation -/
/-- Semantic policy narrowing (`sub` entails `sup` under all atomic environments). -/
def PolicyEntails {Atom : Type} (sub sup : PolicyPred Atom) : Prop :=
  ∀ env : Atom → Bool, evalPolicy env sub = true → evalPolicy env sup = true
/-- Delegated Hermes room/channel capability entry. -/
structure HermesRoomCap (Atom : Type) where
  capId : UInt64
  policy : PolicyPred Atom
  deriving DecidableEq, Repr
/-- Auditable room moderation outcome carrying a 256-bit message digest and constructive explanation. -/
inductive HermesPostReceipt (Atom : Type) where
  | admitted (capId : UInt64) (msgDigest256 : BitVec 256) (whyTrue : WhyTrue Atom)
  | refusedByPolicy (capId : UInt64) (msgDigest256 : BitVec 256) (whyFalse : WhyFalse Atom)
  | refusedRevokedOrMissing (capId : UInt64)
  deriving DecidableEq, Repr
/-- Multi-turn Hermes room environment state. -/
structure HermesRoomState (Atom : Type) where
  rootPolicy : PolicyPred Atom
  nextCapId : UInt64
  caps : List (HermesRoomCap Atom)
  revoked : SortedU64Set
  revokedSpec : List UInt64
  log : List (UInt64 × BitVec 256 × WhyTrue Atom)
/-- Open-world turns on a Hermes room. -/
inductive HermesTurn (Atom : Type) where
  | delegateSubRoom (parentCap : UInt64) (caveat : PolicyPred Atom)
  | revokeSubRoom (targetCap : UInt64)
  | postMessage (capId : UInt64) (msgDigest256 : BitVec 256) (env : Atom → Bool)
def findRoomCap {Atom : Type} (cid : UInt64) : List (HermesRoomCap Atom) → Option (HermesRoomCap Atom)
  | [] => none
  | c :: cs => if c.capId == cid then some c else findRoomCap cid cs
theorem findRoomCap_mem {Atom : Type} {cid : UInt64} {c : HermesRoomCap Atom} :
    ∀ {cs : List (HermesRoomCap Atom)}, findRoomCap cid cs = some c → c ∈ cs ∧ c.capId = cid
  | [], h => by cases h
  | hd :: tl, h => by
    unfold findRoomCap at h
    by_cases hk : hd.capId = cid
    · simp [hk] at h; subst h; exact ⟨List.mem_cons_self, hk⟩
    · have hB : (hd.capId == cid) = false := beq_eq_false_iff_ne.mpr hk
      rw [hB] at h; obtain ⟨hm, hi⟩ := findRoomCap_mem h
      exact ⟨List.mem_cons_of_mem _ hm, hi⟩
/-- Initial Hermes room state seeded with capability `0` carrying `rootPolicy`. -/
@[expose] def initHermesRoom {Atom : Type} (rootPolicy : PolicyPred Atom) : HermesRoomState Atom where
  rootPolicy := rootPolicy
  nextCapId := 1
  caps := [⟨0, rootPolicy⟩]
  revoked := SortedU64Set.empty
  revokedSpec := []
  log := []
/-- Execute one Hermes room turn, emitting a new state and an optional `HermesPostReceipt`. -/
@[expose] def stepHermesRoom {Atom : Type} (st : HermesRoomState Atom) (t : HermesTurn Atom) :
    HermesRoomState Atom × Option (HermesPostReceipt Atom) :=
  match t with
  | .delegateSubRoom parentId caveat =>
    if st.revoked.contains parentId || !decide (st.nextCapId.toNat + 1 < UInt64.size) then
      (st, none)
    else
      match findRoomCap parentId st.caps with
      | none => (st, none)
      | some parent =>
        let cid := st.nextCapId
        let child : HermesRoomCap Atom := ⟨cid, .conj parent.policy caveat⟩
        ({ st with
            nextCapId := UInt64.ofNat (cid.toNat + 1)
            caps := child :: st.caps }, none)
  | .revokeSubRoom targetId =>
    ({ st with
        revoked := st.revoked.insert targetId
        revokedSpec := insertKey targetId st.revokedSpec }, none)
  | .postMessage cid msgDigest256 env =>
    if st.revoked.contains cid then
      (st, some (.refusedRevokedOrMissing cid))
    else
      match findRoomCap cid st.caps with
      | none => (st, some (.refusedRevokedOrMissing cid))
      | some cap =>
        match evalWhy env cap.policy with
        | .inl wt =>
          ({ st with log := (cid, msgDigest256, wt) :: st.log },
           some (.admitted cid msgDigest256 wt))
        | .inr wf =>
          (st, some (.refusedByPolicy cid msgDigest256 wf))
def runHermesTurns {Atom : Type} :
    HermesRoomState Atom → List (HermesTurn Atom) →
    HermesRoomState Atom × List (Option (HermesPostReceipt Atom))
  | st, [] => (st, [])
  | st, t :: ts =>
    let (st₁, r) := stepHermesRoom st t
    let (stF, rs) := runHermesTurns st₁ ts
    (stF, r :: rs)
/-- Inductive invariant of `HermesRoomState`. -/
structure HermesRoomInv {Atom : Type} (st : HermesRoomState Atom) : Prop where
  revoked_sim : SimulatesSet st.revokedSpec st.revoked
  caps_narrow_root : ∀ c ∈ st.caps, PolicyEntails c.policy st.rootPolicy
  log_witnesses_root : ∀ entry ∈ st.log,
    ∃ cap ∈ st.caps, cap.capId = entry.1 ∧
      ∀ env : Atom → Bool, ValidWhyTrue env cap.policy entry.2.2 → evalPolicy env st.rootPolicy = true
theorem initHermesRoom_inv {Atom : Type} (root : PolicyPred Atom) :
    HermesRoomInv (initHermesRoom root) where
  revoked_sim := SortedU64Set.simulates_empty
  caps_narrow_root := by
    intro c hc; simp [initHermesRoom] at hc; subst hc; exact fun _ h => h
  log_witnesses_root := by intro _ h; cases h
/-- **Multi-Turn Hermes Room Attenuation & Explainable Moderation (`hermesRoom_multi_turn_attenuation_sound`)**:
Across ANY sequence of `HermesTurn`s starting from `initHermesRoom rootPolicy`:
1. **Monotonic Attenuation**: every delegated sub-room capability `c ∈ stFinal.caps` semantically
   narrows `rootPolicy` (`evalPolicy env c.policy = true → evalPolicy env rootPolicy = true`),
2. **Permanent Revocation**: once revoked, a room capability stays in `stFinal.revoked` and is
   refused on all subsequent post attempts,
3. **Explainable Admitted & Refused Posts**: every `postMessage` on a live unrevoked capability
   emits either `.admitted` with a valid `WhyTrue` tree entailing `evalPolicy env rootPolicy = true`,
   or `.refusedByPolicy` with a valid `WhyFalse` tree! -/
theorem hermesRoom_multi_turn_attenuation_sound {Atom : Type} [DecidableEq Atom]
    (rootPolicy : PolicyPred Atom) (turns : List (HermesTurn Atom)) :
    let (stFinal, _) := runHermesTurns (initHermesRoom rootPolicy) turns
    HermesRoomInv stFinal ∧
    stFinal.rootPolicy = rootPolicy ∧
    (∀ c ∈ stFinal.caps, PolicyEntails c.policy rootPolicy) ∧
    (∀ cid msg env,
      let (_, rec?) := stepHermesRoom stFinal (.postMessage cid msg env)
      (stFinal.revoked.contains cid = true → rec? = some (.refusedRevokedOrMissing cid)) ∧
      (∀ cap, stFinal.revoked.contains cid = false → findRoomCap cid stFinal.caps = some cap →
        (∃ wt, rec? = some (.admitted cid msg wt) ∧
          checkWhyTrue env cap.policy wt = true ∧ evalPolicy env rootPolicy = true) ∨
        (∃ wf, rec? = some (.refusedByPolicy cid msg wf) ∧
          checkWhyFalse env cap.policy wf = true ∧ evalPolicy env cap.policy = false))) := by
  suffices hStep : ∀ (st : HermesRoomState Atom) (ts : List (HermesTurn Atom)),
      HermesRoomInv st →
      HermesRoomInv (runHermesTurns st ts).1 ∧ (runHermesTurns st ts).1.rootPolicy = st.rootPolicy by
    obtain ⟨hInvF, hRootEq⟩ := hStep (initHermesRoom rootPolicy) turns (initHermesRoom_inv rootPolicy)
    rcases hRun : runHermesTurns (initHermesRoom rootPolicy) turns with ⟨stF, _⟩
    rw [hRun] at hInvF hRootEq; dsimp only [initHermesRoom] at hInvF hRootEq ⊢
    refine ⟨hInvF, hRootEq, fun c hc => hRootEq ▸ hInvF.caps_narrow_root c hc, ?_⟩
    intro cid msg env
    refine ⟨fun hRev => by simp [stepHermesRoom, hRev], ?_⟩
    intro cap hNotRev hFind
    have hCapMem : cap ∈ stF.caps := (findRoomCap_mem hFind).1
    have hEntails : PolicyEntails cap.policy rootPolicy := hRootEq ▸ hInvF.caps_narrow_root cap hCapMem
    have hWhy := (evalWhy_sound_and_complete env cap.policy).1
    simp only [stepHermesRoom, hNotRev, Bool.false_eq_true, ↓reduceIte, hFind]
    cases hEv : evalWhy env cap.policy with
    | inl wt =>
      rw [hEv] at hWhy
      exact .inl ⟨wt, rfl, hWhy.1, hEntails env hWhy.2.2.1⟩
    | inr wf =>
      rw [hEv] at hWhy
      exact .inr ⟨wf, rfl, hWhy.1, hWhy.2.2.1⟩
  intro st ts
  induction ts generalizing st with
  | nil => intro hInv; exact ⟨hInv, rfl⟩
  | cons t rest ih =>
    intro hInv
    have hOne : HermesRoomInv (stepHermesRoom st t).1 ∧ (stepHermesRoom st t).1.rootPolicy = st.rootPolicy := by
      cases t with
      | delegateSubRoom parentId caveat =>
        dsimp only [stepHermesRoom]
        by_cases hCond : (st.revoked.contains parentId || !decide (st.nextCapId.toNat + 1 < UInt64.size)) = true
        · simp only [hCond, ↓reduceIte]; exact ⟨hInv, trivial⟩
        · simp only [hCond, ↓reduceIte]
          cases hF : findRoomCap parentId st.caps with
          | none => exact ⟨hInv, rfl⟩
          | some parent =>
            dsimp only
            have hPMem := (findRoomCap_mem hF).1
            have hPNarrow := hInv.caps_narrow_root parent hPMem
            refine ⟨⟨hInv.revoked_sim, ?_, ?_⟩, rfl⟩
            · intro c hc
              rcases List.mem_cons.mp hc with rfl | hcr
              · intro env hConj
                simp only [evalPolicy, Bool.and_eq_true] at hConj
                exact hPNarrow env hConj.1
              · exact hInv.caps_narrow_root c hcr
            · intro entry he
              obtain ⟨cap, hcMem, hcId, hcRoot⟩ := hInv.log_witnesses_root entry he
              exact ⟨cap, List.mem_cons_of_mem _ hcMem, hcId, hcRoot⟩
      | revokeSubRoom targetId =>
        dsimp only [stepHermesRoom]
        exact ⟨⟨st.revoked.simulates_insert hInv.revoked_sim targetId,
          hInv.caps_narrow_root, hInv.log_witnesses_root⟩, rfl⟩
      | postMessage cid msg env =>
        dsimp only [stepHermesRoom]
        cases hRev : st.revoked.contains cid
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hF : findRoomCap cid st.caps with
          | none => exact ⟨hInv, rfl⟩
          | some cap =>
            dsimp only
            obtain ⟨hCapMem, hCapId⟩ := findRoomCap_mem hF
            have hCapNarrow := hInv.caps_narrow_root cap hCapMem
            cases evalWhy env cap.policy with
            | inr _ => exact ⟨hInv, rfl⟩
            | inl wt =>
              dsimp only
              refine ⟨⟨hInv.revoked_sim, hInv.caps_narrow_root, ?_⟩, rfl⟩
              intro entry he
              rcases List.mem_cons.mp he with rfl | her
              · exact ⟨cap, hCapMem, hCapId, fun env' hV => hCapNarrow env' (validWhyTrue_sound hV)⟩
              · exact hInv.log_witnesses_root entry her
        · simp only [↓reduceIte]; exact ⟨hInv, trivial⟩
    obtain ⟨hInvF, hRootRest⟩ := ih (stepHermesRoom st t).1 hOne.1
    exact ⟨hInvF, hRootRest.trans hOne.2⟩
end Obend.Polis.HermesEnv
end
