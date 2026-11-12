module
public import Obend.Slot.SupportSheaf
public import Obend.Judge.CertifierRatchet
public import Obend.Logic.SeparationFrame
public import Obend.Hardware.SiliconOuroboros
import all Obend.Judge.CertifierRatchet
import all Obend.Judge.SvenvsCorrigibility
import all Obend.Hardware.SiliconOuroboros
import all Obend.Hardware.DprStutter

public section
namespace Obend.Law.PointwiseRevise
open Obend.Judge.SvenvsCorrigibility Obend.Judge.CertifierRatchet
open Obend.Hardware.DprStutter Obend.Hardware.SiliconOuroboros
open Obend.Slot.SupportSheaf
set_option autoImplicit false

/-! Finite, independently owned slots. A clause is a truth table over the slot's
transition-model configurations, not a truth value supplied by its proposer.
Positive weights encode constitutional priority. Equal optima choose the first
configuration in numerical order. Search is O(n * clauses), not a powerset search.
Cross-slot constraints must share an owning slot; falsely declaring them disjoint
is not supported by this representation. -/
structure Clause (n : Nat) where
  name : String
  priority : Nat
  allowed : BitVec n
  deriving DecidableEq, Repr

abbrev SpecTheory (n : Nat) := List (Clause n)

def holds {n : Nat} (c : Clause n) (v : Fin n) : Bool := c.allowed.getLsbD v.val
def weight {n : Nat} (cs : SpecTheory n) : Nat :=
  cs.foldr (fun c k => c.priority + 1 + k) 0
def loss {n : Nat} (cs : SpecTheory n) (v : Fin n) : Nat :=
  cs.foldr (fun c k => (if holds c v then 0 else c.priority + 1) + k) 0
def retain {n : Nat} (cs : SpecTheory n) (v : Fin n) : SpecTheory n :=
  cs.filter (fun c => holds c v)
def models {n : Nat} (cs : SpecTheory n) (v : Fin n) : Bool := cs.all (fun c => holds c v)

/-- Minimum-cost search with stable ties; the executable output carries no oracle. -/
def best {α : Type} (valid : α → Bool) (cost : α → Nat) : List α → Option α
  | [] => none
  | x :: xs =>
    match best valid cost xs with
    | none => if valid x then some x else none
    | some y => if valid x && decide (cost x ≤ cost y) then some x else some y

theorem best_none {α : Type} (valid : α → Bool) (cost : α → Nat) (xs : List α) :
    best valid cost xs = none ↔ ∀ u ∈ xs, valid u = false := by
  induction xs with
  | nil => simp [best]
  | cons x xs ih =>
    cases ht : best valid cost xs with
    | none =>
      have hn := ih.mp ht
      cases hx : valid x <;> simp [best, ht, hx]
      exact hn
    | some y =>
      have hn : ¬ (∀ u ∈ xs, valid u = false) := by
        intro hh
        have := ih.mpr hh
        rw [ht] at this
        cases this
      constructor
      · intro h
        simp only [best, ht] at h
        split at h <;> cases h
      · intro h
        exact (hn (fun u hu => h u (List.mem_cons_of_mem _ hu))).elim

theorem best_some {α : Type} (valid : α → Bool) (cost : α → Nat)
    (xs : List α) (v : α) (h : best valid cost xs = some v) :
    v ∈ xs ∧ valid v = true ∧ ∀ u ∈ xs, valid u = true → cost v ≤ cost u := by
  induction xs generalizing v with
  | nil => simp [best] at h
  | cons x xs ih =>
    simp only [best] at h
    cases ht : best valid cost xs with
    | none =>
      simp only [ht] at h
      split at h
      · next hx =>
        have he : x = v := Option.some.inj h
        subst v
        refine ⟨by simp, hx, ?_⟩
        intro u hu hv
        rcases List.mem_cons.mp hu with he | hu
        · rw [he]; exact Nat.le_refl _
        · have := (best_none valid cost xs).mp ht u hu
          rw [this] at hv
          cases hv
      · cases h
    | some y =>
      have hy := ih y ht
      simp only [ht] at h
      split at h
      · next hx =>
        have he : x = v := Option.some.inj h
        subst v
        obtain ⟨hv, hc⟩ := Bool.and_eq_true_iff.mp hx
        have hc' : cost x ≤ cost y := of_decide_eq_true hc
        refine ⟨by simp, hv, ?_⟩
        intro u hu hvu
        rcases List.mem_cons.mp hu with he | hu
        · rw [he]; exact Nat.le_refl _
        · exact Nat.le_trans hc' (hy.2.2 u hu hvu)
      · next hx =>
        have he : y = v := Option.some.inj h
        subst v
        refine ⟨by simp [hy.1], hy.2.1, ?_⟩
        intro u hu hvu
        rcases List.mem_cons.mp hu with he | hu
        · subst u
          have hn : ¬ cost x ≤ cost y := by
            intro hc
            exact hx (by simp [hvu, hc])
          omega
        · exact hy.2.2 u hu hvu

structure Bedrock (n : Nat) where
  check : Fin n → Bool
  seed : Fin n
  seed_safe : check seed = true

/-- All finite configurations are searched, including configurations absent from S. -/
def choose {n : Nat} (valid : Fin n → Bool) (cs : SpecTheory n) : Option (Fin n) :=
  best valid (loss cs) (List.finRange n)

theorem choose_sound {n : Nat} {valid : Fin n → Bool} {cs : SpecTheory n} {v : Fin n}
    (h : choose valid cs = some v) :
    valid v = true ∧ ∀ u, valid u = true → loss cs v ≤ loss cs u := by
  have hs := best_some valid (loss cs) (List.finRange n) v h
  exact ⟨hs.2.1, fun u hu => hs.2.2 u (by simp) hu⟩

theorem choose_none {n : Nat} (valid : Fin n → Bool) (cs : SpecTheory n) :
    choose valid cs = none ↔ ∀ u, valid u = false := by
  simp [choose, best_none]

def repairWitness {n : Nat} (B : Bedrock n) (N : SpecTheory n) : Fin n :=
  (choose B.check N).getD B.seed

theorem repairWitness_optimal {n : Nat} (B : Bedrock n) (N : SpecTheory n) :
    B.check (repairWitness B N) = true ∧
    ∀ u, B.check u = true → loss N (repairWitness B N) ≤ loss N u := by
  cases h : choose B.check N with
  | none => have := (choose_none _ _).mp h B.seed; simp [B.seed_safe] at this
  | some v => simpa [repairWitness, h] using choose_sound h

inductive Revision (n : Nat) where
  | accepted (witness : Fin n) (preserved : SpecTheory n)
  | refused (witness : Fin n) (counter : SpecTheory n) (cost : Nat)
  deriving DecidableEq, Repr

def pointwiseRevise {n : Nat} (B : Bedrock n) (S N : SpecTheory n) : Revision n :=
  match choose (fun v => B.check v && models N v) S with
  | some v => .accepted v (retain S v)
  | none => let v := repairWitness B N; .refused v (retain N v) (loss N v)

theorem retain_models {n : Nat} (S : SpecTheory n) (v : Fin n) :
    models (retain S v) v = true := by
  simp [models, retain, List.all_eq_true]

theorem loss_zero_iff {n : Nat} (S : SpecTheory n) (v : Fin n) :
    loss S v = 0 ↔ models S v = true := by
  induction S with
  | nil => simp [loss, models]
  | cons c cs ih =>
    cases h : holds c v <;> simp [loss, models, h] at ih ⊢ <;> omega

theorem retain_of_models {n : Nat} (S : SpecTheory n) (v : Fin n)
    (h : models S v = true) : retain S v = S := by
  exact List.filter_eq_self.mpr (by simpa [models, List.all_eq_true] using h)

theorem weight_partition {n : Nat} (S : SpecTheory n) (v : Fin n) :
    weight (retain S v) + loss S v = weight S := by
  induction S with
  | nil => rfl
  | cons c cs ih =>
    cases h : holds c v <;> simp [weight, retain, loss, h] at ih ⊢ <;> omega

/-- Any satisfiable deletion relaxation is dominated by retaining all clauses
true at its witness. Multiplicities are tracked by Sublist, not set membership. -/
theorem relaxation_bound {n : Nat} {R N : SpecTheory n} (sub : R.Sublist N)
    (u : Fin n) (hu : models R u = true) : weight R + loss N u ≤ weight N := by
  induction sub with
  | slnil => simp [weight, loss]
  | @cons l₁ l₂ c sub ih =>
    have hi := ih hu
    cases h : holds c u <;> simp [weight, loss, h] at hi ⊢ <;> omega
  | @cons_cons l₁ l₂ c sub ih =>
    have hh : holds c u = true ∧ models l₁ u = true := by simpa [models] using hu
    have hi := ih hh.2
    simp [weight, loss, hh.1] at hi ⊢
    omega

theorem accepted_iff {n : Nat} (B : Bedrock n) (S N : SpecTheory n)
    (v : Fin n) (R : SpecTheory n) :
    pointwiseRevise B S N = .accepted v R ↔
    choose (fun w => B.check w && models N w) S = some v ∧ R = retain S v := by
  unfold pointwiseRevise
  cases choose (fun w => B.check w && models N w) S <;> simp
  intro he; subst v; exact eq_comm

theorem pointwiseRevise_entails_bedrock {n : Nat} {B : Bedrock n} {S N R : SpecTheory n}
    {v : Fin n} (h : pointwiseRevise B S N = .accepted v R) : B.check v = true :=
  (Bool.and_eq_true_iff.mp (choose_sound ((accepted_iff _ _ _ _ _).mp h).1).1).1

theorem pointwiseRevise_entails_amendment {n : Nat} {B : Bedrock n} {S N R : SpecTheory n}
    {v : Fin n} (h : pointwiseRevise B S N = .accepted v R) : models N v = true :=
  (Bool.and_eq_true_iff.mp (choose_sound ((accepted_iff _ _ _ _ _).mp h).1).1).2

/-- No model of B and N admits a strictly heavier retained subset. -/
theorem pointwiseRevise_maximal_preservation {n : Nat} {B : Bedrock n} {S N R : SpecTheory n}
    {v : Fin n} (h : pointwiseRevise B S N = .accepted v R)
    (T : SpecTheory n) (sub : T.Sublist S) (u : Fin n)
    (hb : B.check u = true) (hn : models N u = true) (ht : models T u = true) :
    weight T ≤ weight R := by
  obtain ⟨hc, rfl⟩ := (accepted_iff _ _ _ _ _).mp h
  have hm := (choose_sound hc).2 u (by simp [hb, hn])
  have hp := weight_partition S v
  have hr := relaxation_bound sub u ht
  omega

theorem pointwiseRevise_vacuous_persistence {n : Nat} {B : Bedrock n} {S N R : SpecTheory n}
    {v : Fin n} (h : pointwiseRevise B S N = .accepted v R)
    (u : Fin n) (hb : B.check u = true) (hn : models N u = true) (hs : models S u = true) :
    R = S := by
  obtain ⟨hc, rfl⟩ := (accepted_iff _ _ _ _ _).mp h
  have hm := (choose_sound hc).2 u (by simp [hb, hn])
  have hz := (loss_zero_iff S u).mpr hs
  exact retain_of_models S v ((loss_zero_iff S v).mp (by omega))

theorem pointwiseRevise_refusal_optimal {n : Nat} {B : Bedrock n} {S N R : SpecTheory n}
    {v : Fin n} {cost : Nat} (h : pointwiseRevise B S N = .refused v R cost) :
    (∀ u, B.check u = true → models N u = false) ∧
    B.check v = true ∧ models R v = true ∧ R.Sublist N ∧
    cost = weight N - weight R ∧
    ∀ T, T.Sublist N → ∀ u, B.check u = true → models T u = true →
      cost ≤ weight N - weight T := by
  unfold pointwiseRevise at h
  cases hc : choose (fun w => B.check w && models N w) S with
  | some w => simp [hc] at h
  | none =>
    simp only [hc, Revision.refused.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    have hr := repairWitness_optimal B N
    refine ⟨?_, hr.1, retain_models _ _, List.filter_sublist, ?_, ?_⟩
    · intro u hb
      have := (choose_none _ _).mp hc u
      simpa [hb] using this
    · have := weight_partition N (repairWitness B N); omega
    · intro T sub u hb ht
      have hm := hr.2 u hb
      have hl := relaxation_bound sub u ht
      omega

/-- The denotation includes the immutable bedrock, all incoming clauses, and
all selected old clauses; it does not collapse to the optimization witness. -/
def revisedModels {n : Nat} (B : Bedrock n) (N R : SpecTheory n) (u : Fin n) : Bool :=
  B.check u && models N u && models R u

theorem revised_success {n : Nat} {B : Bedrock n} {S N R : SpecTheory n} {v : Fin n}
    (h : pointwiseRevise B S N = .accepted v R) : revisedModels B N R v = true := by
  obtain ⟨_, rfl⟩ := (accepted_iff _ _ _ _ _).mp h
  simp [revisedModels, pointwiseRevise_entails_bedrock h,
    pointwiseRevise_entails_amendment h, retain_models]

/-- Acceptance is complete for the entire finite configuration universe. -/
theorem pointwiseRevise_accepts_iff {n : Nat} (B : Bedrock n) (S N : SpecTheory n) :
    (∃ v R, pointwiseRevise B S N = .accepted v R) ↔
    ∃ u, B.check u = true ∧ models N u = true := by
  constructor
  · rintro ⟨v, R, h⟩
    exact ⟨v, pointwiseRevise_entails_bedrock h, pointwiseRevise_entails_amendment h⟩
  · rintro ⟨u, hb, hn⟩
    cases hc : choose (fun v => B.check v && models N v) S with
    | none =>
      have hh := (choose_none _ _).mp hc u
      simp [hb, hn] at hh
    | some v => exact ⟨v, retain S v, by simp [pointwiseRevise, hc]⟩

theorem pointwiseRevise_vacuous_equivalence {n : Nat} (B : Bedrock n)
    (S N : SpecTheory n) (u : Fin n)
    (hb : B.check u = true) (hn : models N u = true) (hs : models S u = true) :
    ∃ v, pointwiseRevise B S N = .accepted v S ∧
      ∀ w, revisedModels B N S w = (B.check w && models (S ++ N) w) := by
  obtain ⟨v, R, h⟩ := (pointwiseRevise_accepts_iff B S N).mpr ⟨u, hb, hn⟩
  have he := pointwiseRevise_vacuous_persistence h u hb hn hs
  subst R
  refine ⟨v, h, ?_⟩
  intro w
  simp [revisedModels, models, Bool.and_comm, Bool.and_left_comm]

/-- Semantic interpretation of a finite model table. These are interpretation
proofs, not fields accepted from an amendment bundle. -/
structure ProtocolMeaning {n : Nat} (B : Bedrock n) (State Act : Type) where
  step : Fin n → State → Act → State
  safe : State → Prop
  home : State → Prop
  recover : Fin n → State → Act
  latency : Nat
  recovery : ∀ v, B.check v = true → ∀ s, safe s →
    DemonicRecovWithin (Det (step v)) (recover v) home latency s
  viable : ∀ v, B.check v = true → ∀ s, safe s → ViableKernel (step v) safe s
  value : Fin n → Obend.Logic.ConservedValue

structure SlotState (n : Nat) where
  model : Fin n
  clauses : SpecTheory n

abbrev World (n : Nat) := Nat → SlotState n
structure AmendmentTurn (n : Nat) where
  slot : Nat
  clauses : SpecTheory n

def applyTurn {n : Nat} (B : Bedrock n) (w : World n) (t : AmendmentTurn n) : World n :=
  match pointwiseRevise B (w t.slot).clauses t.clauses with
  | .accepted v R => fun k => if k = t.slot then ⟨v, t.clauses ++ R⟩ else w k
  | .refused _ _ _ => w

def runTurns {n : Nat} (B : Bedrock n) : World n → List (AmendmentTurn n) → World n
  | w, [] => w
  | w, t :: ts => runTurns B (applyTurn B w t) ts

theorem applyTurn_frame {n : Nat} (B : Bedrock n) (w : World n) (t : AmendmentTurn n)
    (k : Nat) (h : k ≠ t.slot) : applyTurn B w t k = w k := by
  unfold applyTurn
  cases pointwiseRevise B (w t.slot).clauses t.clauses <;> simp [h]

/-- A cached proof object names exactly the slots it reads. The skip path returns
the very same object; disjointness checking itself is linear in its footprint. -/
structure ModuleCert (n : Nat) where
  footprint : List Nat
  expected : Nat → Fin n
  payload : String

def moduleUsable {n : Nat} (w : World n) (c : ModuleCert n) : Bool :=
  c.footprint.all (fun k => decide ((w k).model = c.expected k))

instance {n : Nat} : SupportSheaf (World n) (Nat × Fin n) (ModuleCert n) where
  supports c := c.footprint.map (fun k => (k, c.expected k))
  holds w f := decide ((w f.1).model = f.2)
  usable := moduleUsable
  usable_supports w c h f hf := by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hf
    exact (List.all_eq_true.mp h) k hk
  holds_frame {w₁ w₂ c} h := by
    unfold moduleUsable
    have hh : ∀ k ∈ c.footprint,
        decide ((w₁ k).model = c.expected k) = decide ((w₂ k).model = c.expected k) := by
      intro k hk
      exact h (k, c.expected k) (List.mem_map.mpr ⟨k, hk, rfl⟩)
    have aux : ∀ ks : List Nat,
        (∀ k ∈ ks, decide ((w₁ k).model = c.expected k) = decide ((w₂ k).model = c.expected k)) →
        (ks.all fun k => decide ((w₁ k).model = c.expected k)) =
        (ks.all fun k => decide ((w₂ k).model = c.expected k)) := by
      intro ks
      induction ks with
      | nil => intro _; rfl
      | cons k ks ih =>
        intro hh'
        simp only [List.all_cons]
        rw [hh' k (by simp), ih (fun j hj => hh' j (by simp [hj]))]
    exact aux c.footprint hh

def skipModule {n : Nat} (t : AmendmentTurn n) (c : ModuleCert n) : Option (ModuleCert n) :=
  if t.slot ∈ c.footprint then none else some c

theorem pointwiseRevise_supportSheaf_frame_skip {n : Nat} (B : Bedrock n)
    (w : World n) (t : AmendmentTurn n) (c : ModuleCert n)
    (hd : t.slot ∉ c.footprint) (hu : moduleUsable w c = true) :
    skipModule t c = some c ∧ moduleUsable (applyTurn B w t) c = true ∧
    ∀ k ∈ c.footprint, (applyTurn B w t k).clauses = (w k).clauses := by
  refine ⟨by simp [skipModule, hd], ?_, ?_⟩
  · have he : moduleUsable (applyTurn B w t) c = moduleUsable w c := by
      apply (SupportSheaf.holds_frame (W := World n) (Fact := Nat × Fin n) (x := c))
      intro f hf
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hf
      have hn : k ≠ t.slot := by intro h; subst k; exact hd hk
      change decide ((applyTurn B w t k).model = c.expected k) =
        decide ((w k).model = c.expected k)
      rw [applyTurn_frame B w t k hn]
    rw [he]; exact hu
  · intro k hk
    rw [applyTurn_frame B w t k (by intro h; subst k; exact hd hk)]

theorem applyTurn_safe {n : Nat} (B : Bedrock n) (w : World n) (t : AmendmentTurn n)
    (h : ∀ k, B.check (w k).model = true) : ∀ k, B.check (applyTurn B w t k).model = true := by
  intro k
  unfold applyTurn
  cases hv : pointwiseRevise B (w t.slot).clauses t.clauses with
  | accepted v R =>
    by_cases hk : k = t.slot
    · simpa [hk] using pointwiseRevise_entails_bedrock hv
    · simpa [hk] using h k
  | refused v R cost => exact h k

theorem runTurns_safe {n : Nat} (B : Bedrock n) (w : World n) (ts : List (AmendmentTurn n))
    (h : ∀ k, B.check (w k).model = true) : ∀ k, B.check (runTurns B w ts k).model = true := by
  induction ts generalizing w with
  | nil => exact h
  | cons t ts ih => exact ih _ (applyTurn_safe B w t h)

theorem pointwiseRevise_multiTurn_trace_safe {n : Nat} (B : Bedrock n)
    {State Act : Type} (P : ProtocolMeaning B State Act)
    (w : World n) (ts : List (AmendmentTurn n)) (h : ∀ k, B.check (w k).model = true)
    (k : Nat) (s : State) (hs : P.safe s) :
    let v := (runTurns B w ts k).model
    ViableKernel (P.step v) P.safe s ∧
    DemonicRecovWithin (Det (P.step v)) (P.recover v) P.home P.latency s ∧
    Obend.Logic.sumDeltas (P.value v).entries = 0 := by
  have hb := runTurns_safe B w ts h k
  exact ⟨P.viable _ hb s hs, P.recovery _ hb s hs, (P.value _).conserved⟩

end Obend.Law.PointwiseRevise
