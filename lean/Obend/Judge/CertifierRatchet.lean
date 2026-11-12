module
public import Obend.Judge.SvenvsCorrigibility
public import Obend.Judge.Genealogy
import all Obend.Judge.SvenvsCorrigibility

public section
namespace Obend.Judge.CertifierRatchet
open SvenvsCorrigibility

/-- An obligation need only imply the fact consumed by its gate. -/
def EncodesObligation {O : Type} (sem : O → Prop) (ob : O) (P : Prop) : Prop := sem ob → P
def EncodesObligationIff {O : Type} (sem : O → Prop) (ob : O) (P : Prop) : Prop := sem ob ↔ P
def SoundCertifier {O : Type} (chk : O → Bool) (sem : O → Prop) : Prop :=
  ∀ ob, chk ob = true → sem ob

theorem sound_certifier_iff_transfers {O : Type} (chk : O → Bool) (sem : O → Prop) :
    SoundCertifier chk sem ↔ ∀ ob P, chk ob = true → EncodesObligation sem ob P → P :=
  ⟨fun h ob _ hc he => he (h ob hc), fun h ob hc => h ob (sem ob) hc id⟩

theorem sound_certifier_curried {α β : Type} (kchk : α → β → Bool) (ksem : α → β → Prop) :
    (∀ a b, kchk a b = true → ksem a b) ↔
      SoundCertifier (fun p : α × β => kchk p.1 p.2) (fun p => ksem p.1 p.2) :=
  ⟨fun h p => h p.1 p.2, fun h a b => h (a,b)⟩

abbrev cgate := @SvenvsCorrigibility.cgate

theorem cgate_installs {X : Type} (b : Bool) (old cand : X) (h : b = true) :
    cgate b old cand = cand := by simp [cgate, SvenvsCorrigibility.cgate, h]
theorem cgate_rejects {X : Type} (b : Bool) (old cand : X) (h : b = false) :
    cgate b old cand = old := by simp [cgate, SvenvsCorrigibility.cgate, h]
theorem cgate_keeps {X : Type} (J : X → Prop) (b : Bool) (old cand : X)
    (hc : b = true → J cand) (ho : J old) : J (cgate b old cand) := by
  cases b <;> simp_all [cgate, SvenvsCorrigibility.cgate]

theorem cgate_safe {O X : Type} {chk : O → Bool} {sem : O → Prop} {J : X → Prop}
    (ob : O) (old cand : X) (hc : SoundCertifier chk sem)
    (he : EncodesObligation sem ob (J cand)) (ho : J old) : J (cgate (chk ob) old cand) :=
  cgate_keeps J _ _ _ (fun h => he (hc ob h)) ho

theorem sound_certifier_iff_cgate_safe {O X : Type} (chk : O → Bool) (sem : O → Prop)
    (J : X → Prop) {good bad : X} (hg : J good) (hb : ¬ J bad) :
    SoundCertifier chk sem ↔ ∀ ob old cand, J old →
      EncodesObligation sem ob (J cand) → J (cgate (chk ob) old cand) := by
  constructor
  · intro h ob old cand ho he; exact cgate_safe ob old cand h he ho
  · intro h ob hc
    classical
    apply Classical.byContradiction
    intro hn
    have hx := h ob good bad hg (fun hs => (hn hs).elim)
    exact hb (by simpa [cgate, SvenvsCorrigibility.cgate, hc] using hx)

theorem unsound_certifier_admits_bad {O X : Type} (chk : O → Bool) (sem : O → Prop)
    (J : X → Prop) (good bad : X) (ob : O) (hg : J good) (hb : ¬ J bad)
    (hc : chk ob = true) (hn : ¬ sem ob) :
    EncodesObligation sem ob (J bad) ∧ J good ∧ ¬ J (cgate (chk ob) good bad) := by
  exact ⟨fun h => (hn h).elim, hg, by simpa [cgate, SvenvsCorrigibility.cgate, hc] using hb⟩

def Ratchet {X : Type} (J : X → Prop) (R : X → X → Prop) : Prop := ∀ x y, J x → R x y → J y
def ratchetStream {X : Type} (R : X → X → Prop) (s : Nat → X) : Prop := ∀ n, R (s n) (s (n+1))

theorem ratchet_stream_safe {X : Type} {J : X → Prop} {R : X → X → Prop} (s : Nat → X)
    (hr : Ratchet J R) (h0 : J (s 0)) (hs : ratchetStream R s) : ∀ n, J (s n)
  | 0 => h0
  | n+1 => hr _ _ (ratchet_stream_safe s hr h0 hs n) (hs n)

theorem ratchet_stream_iff {X : Type} (J : X → Prop) (R : X → X → Prop)
    (total : ∀ x, ∃ y, R x y) :
    Ratchet J R ↔ ∀ s, J (s 0) → ratchetStream R s → ∀ n, J (s n) := by
  constructor
  · exact fun h s => ratchet_stream_safe s h
  · intro h x y hx hxy
    classical
    let f := fun x => Classical.choose (total x)
    let tail : Nat → X := fun n => Nat.rec y (fun _ z => f z) n
    let s : Nat → X := fun n => match n with | 0 => x | n+1 => tail n
    have hs : ratchetStream R s := by
      intro n; cases n with
      | zero => exact hxy
      | succ n => exact Classical.choose_spec (total (tail n))
    exact h s hx hs 1

def ratchetStep {O X : Type} (chk : O → Bool) (sem : O → Prop) (J : X → Prop)
    (old next : X) : Prop := next = old ∨ ∃ ob cand,
      EncodesObligation sem ob (J cand) ∧ next = cgate (chk ob) old cand

theorem ratchetStep_ratchet {O X : Type} {chk : O → Bool} {sem : O → Prop} (J : X → Prop)
    (hc : SoundCertifier chk sem) : Ratchet J (ratchetStep chk sem J) := by
  rintro x y hx (rfl | ⟨ob, cand, he, rfl⟩)
  · exact hx
  · exact cgate_safe ob x cand hc he hx

theorem sound_certifier_iff_ratchetStep {O X : Type} (chk : O → Bool) (sem : O → Prop)
    (J : X → Prop) {good bad : X} (hg : J good) (hb : ¬ J bad) :
    SoundCertifier chk sem ↔ Ratchet J (ratchetStep chk sem J) := by
  constructor
  · exact ratchetStep_ratchet J
  · intro h
    apply (sound_certifier_iff_cgate_safe chk sem J hg hb).2
    exact fun ob old cand ho he => h _ _ ho (.inr ⟨ob, cand, he, rfl⟩)

theorem sound_certifier_iff_stream_safe {O X : Type} (chk : O → Bool) (sem : O → Prop)
    (J : X → Prop) {good bad : X} (hg : J good) (hb : ¬ J bad) :
    SoundCertifier chk sem ↔ ∀ s, J (s 0) →
      ratchetStream (ratchetStep chk sem J) s → ∀ n, J (s n) :=
  (sound_certifier_iff_ratchetStep chk sem J hg hb).trans
    (ratchet_stream_iff J _ (fun x => ⟨x, .inl rfl⟩))

@[expose] def cgateRunOffers {O X : Type} (chk : O → Bool) (x₀ : X) : List (O × X) → X
  | [] => x₀
  | (ob,cand)::rest => cgateRunOffers chk (cgate (chk ob) x₀ cand) rest

theorem cgate_run_safe {O X : Type} (chk : O → Bool) (J : X → Prop) (offers : List (O × X))
    (x₀ : X) (h0 : J x₀) (h : ∀ p ∈ offers, chk p.1 = true → J p.2) :
    J (cgateRunOffers chk x₀ offers) := by
  induction offers generalizing x₀ with
  | nil => exact h0
  | cons p ps ih =>
    exact ih _ (cgate_keeps J _ _ _ (h p (by simp)) h0) (fun q hq => h q (by simp [hq]))

theorem cgate_run_append {O X : Type} (chk : O → Bool) (xs ys : List (O × X)) (x : X) :
    cgateRunOffers chk x (xs ++ ys) = cgateRunOffers chk (cgateRunOffers chk x xs) ys := by
  induction xs generalizing x with
  | nil => rfl
  | cons p ps ih => exact ih _

theorem cgate_run_follows {O X : Type} (chk : O → Bool) (sem : O → Prop) (J : X → Prop)
    (offers : List (O × X)) (x : X) (he : ∀ p ∈ offers, EncodesObligation sem p.1 (J p.2)) :
    ratchetStream (ratchetStep chk sem J) (fun n => cgateRunOffers chk x (offers.take n)) := by
  intro n
  dsimp only
  by_cases hn : n < offers.length
  · rw [List.take_succ_eq_append_getElem hn, cgate_run_append]
    exact .inr ⟨offers[n].1, offers[n].2, he _ (List.getElem_mem hn), rfl⟩
  · have hle : offers.length ≤ n := by omega
    rw [List.take_of_length_le hle, List.take_of_length_le (by omega)]
    exact .inl rfl

theorem cgate_run_safe_iff {O X : Type} (chk : O → Bool) (J : X → Prop)
    (offers : List (O × X)) {good : X} (hg : J good) :
    (∀ p ∈ offers, chk p.1 = true → J p.2) ↔
      ∀ x₀, J x₀ → ∀ n, J (cgateRunOffers chk x₀ (offers.take n)) := by
  constructor
  · intro h x hx n
    exact cgate_run_safe chk J _ x hx (fun p hp => h p (List.mem_of_mem_take hp))
  · intro h p hp hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    have ht := h good hg (i+1)
    rw [List.take_succ_eq_append_getElem hi, cgate_run_append] at ht
    simpa [cgateRunOffers, cgate, SvenvsCorrigibility.cgate, hc] using ht

/-- The viability kernel is the union of controlled invariant subsets. -/
def Viable {S A : Type} (step : S → A → S) (V : S → Prop) : Prop :=
  ∀ s, V s → ∃ a, V (step s a)
def ViableKernel {S A : Type} (step : S → A → S) (safe : S → Prop) (s : S) : Prop :=
  ∃ V, V s ∧ (∀ t, V t → safe t) ∧ Viable step V

theorem viableKernel_viable {S A : Type} (step : S → A → S) (safe : S → Prop) :
    Viable step (ViableKernel step safe) := by
  rintro s ⟨V, hs, hsub, hv⟩
  obtain ⟨a, ha⟩ := hv s hs
  exact ⟨a, V, ha, hsub, hv⟩
theorem viableKernel_sub_safe {S A : Type} {step : S → A → S} {safe : S → Prop}
    (s : S) (h : ViableKernel step safe s) : safe s := by
  obtain ⟨_, hs, hsub, _⟩ := h; exact hsub s hs

theorem viableKernel_greatest {S A : Type} (step : S → A → S) (safe V : S → Prop)
    (sub : ∀ t, V t → safe t) (hv : Viable step V) (s : S) (hs : V s) :
    ViableKernel step safe s := ⟨V, hs, sub, hv⟩

theorem viable_iff_viableKernel {S A : Type} (step : S → A → S) (safe : S → Prop) :
    Viable step safe ↔ ∀ s, safe s → ViableKernel step safe s := by
  constructor
  · exact fun hv s hs => ⟨safe, hs, fun _ h => h, hv⟩
  · intro h s hs
    obtain ⟨a, ha⟩ := viableKernel_viable step safe s (h s hs)
    exact ⟨a, viableKernel_sub_safe _ ha⟩

theorem viable_greatest_tight (n : Nat) :
    (Viable (fun (s : Nat) (_ : Nat) => s) (fun _ => True) ∧
      ¬ ViableKernel (fun s (_ : Nat) => s) (fun s => s = n) (n+1)) ∧
    ¬ ViableKernel (fun (_ : Nat) (_ : Nat) => n+1) (fun s => s = n) n := by
  refine ⟨⟨fun _ _ => ⟨0, trivial⟩, fun h => ?_⟩, ?_⟩
  · have := viableKernel_sub_safe _ h; omega
  · rintro ⟨V, hs, sub, hv⟩
    obtain ⟨_, ha⟩ := hv n hs
    have hh : n+1 = n := sub _ ha; omega

theorem shield_exists_iff_viable {S A : Type} [Inhabited A]
    (step : S → A → S) (safe : S → Prop) :
    (∃ shield : S → A, SafeShield step safe shield) ↔ Viable step safe := by
  classical
  constructor
  · rintro ⟨sh, h⟩ s hs; exact ⟨sh s, h s hs⟩
  · intro h
    refine ⟨fun s => if hs : safe s then Classical.choose (h s hs) else default, ?_⟩
    intro s hs
    simp only [dite_eq_left hs]
    exact Classical.choose_spec (h s hs)

theorem viableKernel_shield_exists {S A : Type} [Inhabited A]
    (step : S → A → S) (safe : S → Prop) :
    ∃ shield : S → A, SafeShield step (ViableKernel step safe) shield :=
  (shield_exists_iff_viable _ _).2 (viableKernel_viable step safe)

theorem viability_kernel_envelope {S A : Type} [Inhabited A] (step : S → A → S)
    (safe init : S → Prop) (pol : Policy S A) (hi : InitSafe init (ViableKernel step safe))
    (hp : SoundPolicy step (ViableKernel step safe) pol) :
    ∃ shield, ∀ ctrl, Invariant step init (enveloped pol shield ctrl) safe := by
  obtain ⟨sh, hs⟩ := viableKernel_shield_exists step safe
  exact ⟨sh, fun ctrl s hr => viableKernel_sub_safe s (safety_preservation hi hp hs ctrl s hr)⟩

def AdmissibleUpgrade {S A : Type} (step : S → A → S) (safe : S → Prop)
    (oldp newp : Policy S A) : Prop := SoundPolicy step safe newp ∧ Weaker newp oldp

theorem gate_certificate_iff {S A : Type} (step : S → A → S) (safe : S → Prop)
    (cert : Bool) (newp : Policy S A) (viable : ∃ sh, SafeShield step safe sh) :
    (cert = true → SoundPolicy step safe newp) ↔
    ∀ init shield oldp ctrl, InitSafe init safe → SafeShield step safe shield →
      SoundPolicy step safe oldp →
      Invariant step init (enveloped (cgate cert oldp newp) shield ctrl) safe := by
  constructor
  · intro h init sh old ctrl hi hs ho
    exact safety_preservation hi (cgate_keeps _ cert old newp h ho) hs ctrl
  · intro h hc s a hs hp
    obtain ⟨sh, hsh⟩ := viable
    have inv := h (fun t => t = s) sh (fun _ _ => false) (fun _ => a)
      (fun _ ht => ht ▸ hs) hsh (fun _ _ _ hf => Bool.noConfusion hf)
    have next := inv _ (Reach.step (Reach.init rfl))
    simpa [cgate, SvenvsCorrigibility.cgate, hc, enveloped, hp] using next

theorem gate_iff_needs_viability (n : Nat) :
    ¬ (∃ sh : Nat → Nat, SafeShield (fun _ _ => n+1) (fun s => s = n) sh) ∧
    ¬ SoundPolicy (fun (_ : Nat) (_ : Nat) => n+1) (fun s => s = n) (fun _ _ => true) ∧
    ¬ (SoundPolicy (fun (_ : Nat) (_ : Nat) => n+1) (fun s => s = n) (fun _ _ => true) ↔
      ∀ (init : Nat → Prop) (sh : Nat → Nat) (old : Policy Nat Nat) (ctrl : Nat → Nat),
        InitSafe init (fun s => s = n) → SafeShield (fun _ _ => n+1) (fun s => s = n) sh →
        SoundPolicy (fun _ _ => n+1) (fun s => s = n) old →
        Invariant (fun _ _ => n+1) init (enveloped (cgate true old (fun _ _ => true)) sh ctrl)
          (fun s => s = n)) := by
  have hsh : ¬ (∃ sh : Nat → Nat, SafeShield (fun _ _ => n+1) (fun s => s = n) sh) := by
    rintro ⟨sh,h⟩; have hh : n+1 = n := h n rfl; omega
  have hp : ¬ SoundPolicy (fun (_ : Nat) (_ : Nat) => n+1) (fun s => s = n) (fun _ _ => true) := by
    intro h; have hh : n+1 = n := h n 0 rfl rfl; omega
  exact ⟨hsh,hp,fun he => hp (he.2 (fun _ sh _ _ _ hs _ => (hsh ⟨sh,hs⟩).elim))⟩

abbrev maxpol_intervenes_iff_unsafe := @SvenvsCorrigibility.maxpol_intervenes_iff_unsafe

def maxPolR {S A : Type} (stepr : PlantR S A) (safe : S → Prop)
    [∀ s a, Decidable (safe s → ∀ s', stepr s a s' → safe s')] : Policy S A :=
  fun s a => decide (safe s → ∀ s', stepr s a s' → safe s')

theorem maxPolR_sound {S A : Type} (r : PlantR S A) (safe : S → Prop)
    [∀ s a, Decidable (safe s → ∀ s', r s a s' → safe s')] :
    SoundPolicyR r safe (maxPolR r safe) :=
  fun _s _a t hs hp ht => (of_decide_eq_true hp) hs t ht

theorem maxPolR_is_greatest_sound {S A : Type} (r : PlantR S A) (safe : S → Prop)
    [∀ s a, Decidable (safe s → ∀ s', r s a s' → safe s')]
    (pol : Policy S A) (hp : SoundPolicyR r safe pol) : Weaker (maxPolR r safe) pol :=
  fun s a ha => decide_eq_true (fun hs t ht => hp s a t hs ha ht)

theorem maxPolR_intervenes_iff_unsafe {S A : Type} (r : PlantR S A) (safe : S → Prop)
    [∀ s a, Decidable (safe s → ∀ s', r s a s' → safe s')]
    (sh ctrl : S → A) (hsh : SafeShieldR r safe sh) (s : S) (hs : safe s) :
    Intervenes (maxPolR r safe) sh ctrl s ↔ ∃ t, r s (ctrl s) t ∧ ¬ safe t := by
  classical
  by_cases h : ∀ t, r s (ctrl s) t → safe t
  · have hm : maxPolR r safe s (ctrl s) = true := decide_eq_true (fun _ => h)
    simp [Intervenes, enveloped, hm, show ¬ (∃ t, r s (ctrl s) t ∧ ¬ safe t) from
      fun ⟨t, ht, hn⟩ => hn (h t ht)]
  · have hm : maxPolR r safe s (ctrl s) = false := decide_eq_false (fun hh => h (hh hs))
    have he : sh s ≠ ctrl s := by
      intro he; apply h; intro t ht; exact hsh s t hs (he ▸ ht)
    simp only [Intervenes, enveloped, hm, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro _
      apply Classical.byContradiction
      intro hn
      apply h
      intro t ht
      apply Classical.byContradiction
      intro hnSafe
      exact hn ⟨t, ht, hnSafe⟩
    · exact fun _ => he

theorem envelope_transparent_runr {S A : Type} (r : PlantR S A) (init safe : S → Prop)
    [∀ s a, Decidable (safe s → ∀ s', r s a s' → safe s')]
    (sh ctrl : S → A) (hi : InvariantR r init ctrl safe) :
    ∀ s, ReachR r init (enveloped (maxPolR r safe) sh ctrl) s ↔ ReachR r init ctrl s := by
  have agree : ∀ s, ReachR r init ctrl s → enveloped (maxPolR r safe) sh ctrl s = ctrl s := by
    intro s hr
    have hm : maxPolR r safe s (ctrl s) = true :=
      decide_eq_true (fun _ t ht => hi t (.step hr ht))
    simp [enveloped, hm]
  intro s; constructor
  · intro hr; induction hr with
    | init h => exact .init h
    | @step s t _ ht ih => exact .step ih (by simpa [agree s ih] using ht)
  · intro hr; induction hr with
    | init h => exact .init h
    | @step s t hr ht ih => exact .step ih (by simpa [agree s hr] using ht)

theorem envelope_transparent_iffr {S A : Type} (r : PlantR S A) (init safe : S → Prop)
    [∀ s a, Decidable (safe s → ∀ s', r s a s' → safe s')]
    (sh ctrl : S → A) (hi : InitSafe init safe) (hs : SafeShieldR r safe sh) :
    InvariantR r init ctrl safe ↔
    ∀ s, ReachR r init (enveloped (maxPolR r safe) sh ctrl) s ↔ ReachR r init ctrl s := by
  constructor
  · exact envelope_transparent_runr r init safe sh ctrl
  · intro h s hr
    exact safety_preservationR hi (maxPolR_sound r safe) hs ctrl s ((h s).2 hr)

abbrev VouchSound {J : Type} (jsound : J → Prop) (vouches : J → J → Prop) := Ratchet jsound vouches
abbrev ForwardCertified {J : Type} (vouches : J → J → Prop) (line : Nat → J) := ratchetStream vouches line
abbrev genealogy_sound := @ratchet_stream_safe

theorem identity_vouch_unconditional {J : Type} (jsound : J → Prop) : VouchSound jsound Eq :=
  fun _ _ h he => he ▸ h
abbrev vouch_sound_is_necessary := @ratchet_stream_iff

theorem genealogy_irrelevant_to_vouch_sound (n : Nat) :
    ForwardCertified (fun A B : Nat => B = A+1) (fun k => n+k) ∧
    ¬ VouchSound (fun k : Nat => k = 0) (fun A B => B = A+1) := by
  exact ⟨fun _ => by dsimp; omega, fun h => Nat.noConfusion (h 0 1 rfl rfl)⟩

/-- This is the concrete genealogy relation, with the execution trust bases discharged. -/
theorem habitat_succession_vouch_sound (H : Genealogy.Habitat) (X : Genealogy.Exec)
    (hx : ∀ t, X.Holds t) :
    VouchSound (Genealogy.GateSound X)
      (fun A B : Genealogy.Gate H => ∃ s labels, Genealogy.Succeeds A s B labels) := by
  rintro A B _ ⟨s, labels, h⟩
  exact h.sound X (fun t _ => hx t) (fun t _ => hx t)

def FrozenCheckerSound {P B : Type} (checks : P → B → Bool) (sound : B → Prop) : Prop :=
  ∀ p b, checks p b = true → sound b
def BuildCertifies {B S A : Type} (sound : B → Prop) (b : B) (step : S → A → S)
    (safe : S → Prop) (oldp newp : Policy S A) : Prop :=
  sound b → AdmissibleUpgrade step safe oldp newp
@[expose] def proverGate {P B X : Type} (checks : P → B → Bool) (p : P) (b : B)
    (verdict : Bool) (old cand : X) : X := cgate (checks p b && verdict) old cand

theorem frozen_checker_sound_iff_sound_certifier {P B : Type}
    (checks : P → B → Bool) (sound : B → Prop) :
    FrozenCheckerSound checks sound ↔
    SoundCertifier (fun ob : P × B × Bool => checks ob.1 ob.2.1 && ob.2.2)
      (fun ob => sound ob.2.1 ∧ ob.2.2 = true) := by
  constructor
  · intro h ob hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨h1,h2⟩ := hc
    exact ⟨h _ _ h1, h2⟩
  · intro h p b hc
    exact (h (p,b,true) (by simp [hc])).1

theorem prover_self_improvement_is_safe {P B S A : Type} (checks : P → B → Bool)
    (sound : B → Prop) (p : P) (b : B) (verdict : Bool) (step : S → A → S)
    (init safe : S → Prop) (sh : S → A) (oldp newp : Policy S A)
    (hc : FrozenCheckerSound checks sound)
    (hb : verdict = true → BuildCertifies sound b step safe oldp newp)
    (hi : InitSafe init safe) (hs : SafeShield step safe sh) (ho : SoundPolicy step safe oldp) :
    ∀ ctrl, Invariant step init (enveloped (proverGate checks p b verdict oldp newp) sh ctrl) safe := by
  apply safety_preservation hi _ hs
  apply cgate_keeps _ _ _ _ _ ho
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1,h2⟩ := h
  exact (hb h2 (hc p b h1)).1

theorem frozen_checker_sound_iff_prover_gate_safe {P B X : Type}
    (checks : P → B → Bool) (sound : B → Prop) (J : X → Prop)
    {good bad : X} (hg : J good) (hb : ¬ J bad) :
    FrozenCheckerSound checks sound ↔ ∀ p b verdict old cand, J old →
    (sound b ∧ verdict = true → J cand) → J (proverGate checks p b verdict old cand) := by
  rw [frozen_checker_sound_iff_sound_certifier checks sound,
    sound_certifier_iff_cgate_safe _ _ J hg hb]
  exact ⟨fun h p b v => h (p,b,v), fun h ob => h ob.1 ob.2.1 ob.2.2⟩

theorem unvouched_prover_swap_is_inert {P B X : Type} (checks : P → B → Bool)
    (p : P) (b : B) (verdict : Bool) (old cand : X) (h : checks p b = false) :
    proverGate checks p b verdict old cand = old := by
  simp [proverGate, h, cgate, SvenvsCorrigibility.cgate]

/-- The fixed root certifies a different, mutable artifact. The stream theorem
requires ordinary external soundness and faithful offers, not self-reflection. -/
theorem prover_then_unbounded_policy_self_improvement_is_safe {P B S A : Type}
    (checks : P → B → Bool) (sound : B → Prop) (step : S → A → S) (safe : S → Prop)
    (line : Nat → Policy S A) (offers : Nat → P × B × Bool × Policy S A)
    (hc : FrozenCheckerSound checks sound) (h0 : SoundPolicy step safe (line 0))
    (hb : ∀ n, (offers n).2.2.1 = true →
      BuildCertifies sound (offers n).2.1 step safe (line n) (offers n).2.2.2)
    (hl : ∀ n, line (n+1) = proverGate checks (offers n).1 (offers n).2.1
      (offers n).2.2.1 (line n) (offers n).2.2.2) :
    ∀ n, SoundPolicy step safe (line n) := by
  intro n; induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hl n]
    apply cgate_keeps _ _ _ _ _ ih
    intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1,h2⟩ := h
    exact (hb n h2 (hc _ _ h1)).1

end Obend.Judge.CertifierRatchet
