module
/-
# Obend.Judge.SvenvsCorrigibility — Policy Weakening, Least-Restrictive `MaxPol`, Demonic $B$-Step Corrigibility, 3-Tier `SpecNeg` & `PcaEnvelope`

Completes the Lean 4 uptake of `svenvs` (`sv_weakening`, `liberty`, `transparency`, `relSystem`,
`relEnvelope`, `corrigibility`, `specNeg`, `pca`, `embodiment`) with zero custom axioms, zero
classical choice, paired sufficiency + necessity (`iff` & counterexample) theorems, and direct
wiring into `Obend.Judge.Genealogy.Habitat` and `Obend.Law.Narrows`:

1. **Safe Policy Weakening & Least-Restrictive `MaxPol` Shield**:
   - Order-theoretic duality between `Weaker` (authority expansion) and `Obend.Law.Narrows`
     (attenuation), `authority_monotone`, `safe_weakening_iff`, `safe_weakening_needs_weaker`,
     `maxPol`, `envelope_is_least_restrictive`, `maxpol_transparent_run` (+ `_iff`), and
     `override_iff_burned_bridge`.
2. **Demonic $B$-Step Latency-Bounded Corrigibility over Nondeterministic & Disturbed Plants**:
   - Game-tree recoverability `DemonicRecovWithin stepr recov home B`, deterministic collapse to
     `CWithin`, relational safety + non-blocking liveness, disturbance runs (`Disturbed`, `drun`),
     `angelic_recoverability_insufficient`, self-modifying off-switch latency gate
     `self_mod_preserves_latency_B` (+ `_iff`), and N-version operator `disjoint_homes_empty_floor`.
3. **3-Tier Constitutional Stack (`Bedrock → Meta → Spec`) on `Obend.Judge.Genealogy.Habitat`**:
   - Abstract and `Habitat`-concrete 3-tier constitutional evolution (`spec_negotiation_safe`,
     `meta_amendment_safe`, `bedrock_is_eternal`, `habitat_bedrock_is_eternal`), enabling lateral
     Tier-2 task-spec renegotiation while keeping Tier-1 meta-floors and Tier-0 corrigibility
     bedrock inviolate.
4. **Proof-Carrying Actions (`PcaEnvelope`) & Voluntary Testimony (`VoluntaryTestimony`)**:
   - Per-turn certificate-checked envelope (`pca_enveloped_safe`, `pca_certifier_sound_iff`,
     `pca_strictly_subsumes_static_shield`) and optional internal-activation testimony channel
     (`nondisclosure_is_inert`, `disclosure_unlocks_authority`, `voluntary_testimony_faithful_iff`).
-/
public import Obend.Judge.Genealogy
public import Obend.Law.Contract
public import Obend.Law.Run

public section

namespace Obend.Judge.SvenvsCorrigibility

open Obend.Judge.Genealogy (Habitat Gate Exec)
open Obend.Law (Narrows Admits)
open Obend.Core.Term (Term)
open Obend.Core.Data (Data)

set_option autoImplicit false

/-! ## 1. Safe Policy Weakening, Duality to `Law.Narrows`, and Least-Restrictive `MaxPol` -/

/-- Runtime-checkable policy over state space `S` and action space `A`. -/
abbrev Policy (S A : Type) := S → A → Bool

/-- Runtime policy envelope: pass the controller's action iff `pol` permits it, else invoke `shield`. -/
@[expose] def enveloped {S A : Type} (pol : Policy S A) (shield ctrl : S → A) (s : S) : A :=
  if pol s (ctrl s) then ctrl s else shield s

/-- Deterministic reachability from `init` under selector `sel`. -/
inductive Reach {S A : Type} (step : S → A → S) (init : S → Prop) (sel : S → A) : S → Prop
  | init {s : S} : init s → Reach step init sel s
  | step {s : S} : Reach step init sel s → Reach step init sel (step s (sel s))

/-- Every initial state satisfies `safe`. -/
def InitSafe {S : Type} (init safe : S → Prop) : Prop :=
  ∀ s, init s → safe s

/-- One-step closure of `safe` under selector `sel`. -/
def StepClosed {S A : Type} (step : S → A → S) (sel : S → A) (safe : S → Prop) : Prop :=
  ∀ s, safe s → safe (step s (sel s))

/-- Trace invariance: every state reachable under `sel` satisfies `safe`. -/
def Invariant {S A : Type} (step : S → A → S) (init : S → Prop) (sel : S → A) (safe : S → Prop) : Prop :=
  ∀ s, Reach step init sel s → safe s

theorem invariant_intro {S A : Type} {step : S → A → S} {init : S → Prop} {sel : S → A} {safe : S → Prop}
    (hInit : InitSafe init safe) (hStep : StepClosed step sel safe) :
    Invariant step init sel safe := by
  intro s hr
  induction hr with
  | init hi => exact hInit _ hi
  | step _ ih => exact hStep _ ih

/-- A policy is safety-sound when every action it permits from a safe state lands in a safe state. -/
def SoundPolicy {S A : Type} (step : S → A → S) (safe : S → Prop) (pol : Policy S A) : Prop :=
  ∀ s a, safe s → pol s a = true → safe (step s a)

/-- A fallback shield is safe when it preserves `safe` from every safe state. -/
def SafeShield {S A : Type} (step : S → A → S) (safe : S → Prop) (shield : S → A) : Prop :=
  ∀ s, safe s → safe (step s (shield s))

theorem enveloped_step_closed {S A : Type} {step : S → A → S} {safe : S → Prop}
    {pol : Policy S A} {shield : S → A} (ctrl : S → A)
    (hPol : SoundPolicy step safe pol) (hSh : SafeShield step safe shield) :
    StepClosed step (enveloped pol shield ctrl) safe := by
  intro s hs
  unfold enveloped
  cases hp : pol s (ctrl s) with
  | true => exact hPol s (ctrl s) hs hp
  | false => exact hSh s hs

/-- Universal controller-agnostic safety preservation under an envelope. -/
theorem safety_preservation {S A : Type} {step : S → A → S} {init safe : S → Prop}
    {pol : Policy S A} {shield : S → A}
    (hInit : InitSafe init safe) (hPol : SoundPolicy step safe pol) (hSh : SafeShield step safe shield) :
    ∀ ctrl, Invariant step init (enveloped pol shield ctrl) safe :=
  fun ctrl => invariant_intro hInit (enveloped_step_closed ctrl hPol hSh)

/-- **Policy Weakening** (`sv_weakening : weaker p q`): `p` is at least as permissive as `q`
    (every action permitted by `q` is permitted by `p`). -/
def Weaker {S A : Type} (p q : Policy S A) : Prop :=
  ∀ s a, q s a = true → p s a = true

/-- Dual attenuation preorder on policies (`q` narrows `p`). -/
def PolicyNarrows {S A : Type} (q p : Policy S A) : Prop :=
  ∀ s a, q s a = true → p s a = true

@[simp] theorem weaker_refl {S A : Type} (p : Policy S A) : Weaker p p :=
  fun _ _ h => h

theorem weaker_trans {S A : Type} {p q r : Policy S A} (hpq : Weaker p q) (hqr : Weaker q r) :
    Weaker p r :=
  fun s a h => hpq s a (hqr s a h)

/-- **Order-Theoretic Duality to `Obend.Law.Narrows`**:
    `Weaker p q` (self-improvement authority loosening) is the exact order-dual of attenuation
    (`PolicyNarrows q p`), and on bounded-evaluated Core4 cell laws (`evalAdmitsBounded`),
    loosening from `law₂` to `law₁` (`Weaker`) is dual to `law₂` narrowing `law₁`. -/
theorem weaker_dual_narrows (law₁ law₂ : Term) :
    let polOf (l : Term) : Policy (Data × Data) Data :=
      fun pair req => Obend.Law.okB (Obend.Law.run 64 (.app (.app (.app l pair.1.term) pair.2.term) req.term))
    (Weaker (polOf law₁) (polOf law₂) ↔ PolicyNarrows (polOf law₂) (polOf law₁)) ∧
    (Narrows law₂ law₁ → ∀ old new req, Admits law₂ old new req → Admits law₁ old new req) := by
  exact ⟨⟨fun h s a hq => h s a hq, fun h s a hq => h s a hq⟩, fun h old new req ha => h old new req ha⟩

/-- Soundness transfers downward from a permissive policy `p` to any restriction `q`. -/
theorem sound_policy_weaker {S A : Type} {step : S → A → S} {safe : S → Prop} {p q : Policy S A}
    (hWeak : Weaker p q) (hSound : SoundPolicy step safe p) :
    SoundPolicy step safe q :=
  fun s a hs hq => hSound s a hs (hWeak s a hq)

/-- **Monotonicity of Controller Authority**: wherever `q` permitted `ctrl s`, any weaker `p`
    also passes `ctrl s` through untouched without shield override. -/
theorem authority_monotone {S A : Type} {p q : Policy S A} (hWeak : Weaker p q)
    (shield ctrl : S → A) (s : S) (hq : q s (ctrl s) = true) :
    enveloped p shield ctrl s = ctrl s := by
  simp [enveloped, hWeak s (ctrl s) hq]

/-- **Exact Sufficiency & Necessity of Safe Policy Weakening (`safe_weakening_iff`)**:
    Given a safe fallback `shield` and at least two distinct actions `a₀ ≠ a₁`, a candidate
    policy `p` both (1) preserves `safe` from every `InitSafe` start for every controller and
    (2) never revokes controller authority previously granted by `q` **if and only if**
    `SoundPolicy step safe p ∧ Weaker p q`. -/
theorem safe_weakening_iff {S A : Type} [DecidableEq A]
    {step : S → A → S} {safe : S → Prop} {shield : S → A}
    (hSh : SafeShield step safe shield) {a₀ a₁ : A} (hDist : a₀ ≠ a₁)
    (p q : Policy S A) :
    (SoundPolicy step safe p ∧ Weaker p q) ↔
      ((∀ (init : S → Prop) (ctrl : S → A),
          InitSafe init safe → Invariant step init (enveloped p shield ctrl) safe) ∧
       (∀ (sh ctrl : S → A) (s : S),
          q s (ctrl s) = true → enveloped p sh ctrl s = ctrl s)) := by
  constructor
  · rintro ⟨hSound, hWeak⟩
    exact ⟨fun _ ctrl hInit => safety_preservation hInit hSound hSh ctrl,
      fun sh ctrl s hq => authority_monotone hWeak sh ctrl s hq⟩
  · rintro ⟨hSafeAll, hAuthAll⟩
    refine ⟨?_, ?_⟩
    · intro s a hs hp
      have hInit : InitSafe (fun x => x = s) safe := fun x hx => hx ▸ hs
      have hInv := hSafeAll (fun x => x = s) (fun _ => a) hInit
      have hReach1 : Reach step (fun x => x = s) (enveloped p shield (fun _ => a))
          (step s (enveloped p shield (fun _ => a) s)) :=
        .step (.init rfl)
      have hSafeNext := hInv _ hReach1
      simpa [enveloped, hp] using hSafeNext
    · intro s a hq
      let alt : A := if a = a₀ then a₁ else a₀
      have halt_ne : alt ≠ a := by
        dsimp only [alt]
        split
        · rename_i heq; subst heq; exact hDist.symm
        · rename_i hne; exact Ne.symm hne
      have hEq := hAuthAll (fun _ => alt) (fun _ => a) s hq
      cases hp : p s a with
      | true => rfl
      | false =>
        simp only [enveloped, hp] at hEq
        exact absurd hEq halt_ne

/-- Concrete necessity witness (`sv_weakening : safe_weakening_needs_weaker`): two sound policies
    `p, q` with `¬ Weaker p q` where `ctrl` ran freely under `q` at `s = 0` (`ctrl 0 = 1`)
    but is overridden by the shield under `p`. -/
theorem safe_weakening_needs_weaker :
    ∃ (step : Nat → Nat → Nat) (safe init : Nat → Prop) (shield : Nat → Nat)
      (p q : Policy Nat Nat) (ctrl : Nat → Nat) (s : Nat),
      InitSafe init safe ∧ SafeShield step safe shield ∧
      SoundPolicy step safe p ∧ SoundPolicy step safe q ∧
      ¬ Weaker p q ∧
      enveloped q shield ctrl s = ctrl s ∧ q s (ctrl s) = true ∧
      enveloped p shield ctrl s ≠ ctrl s := by
  refine ⟨fun s _ => s, fun _ => True, fun _ => True, fun _ => 0,
    fun _ _ => false, fun _ _ => true, fun _ => 1, 0,
    fun _ _ => trivial, fun _ _ => trivial,
    fun _ _ _ h => False.elim (Bool.false_ne_true h), fun _ _ _ _ => trivial,
    ?_, rfl, rfl, by decide⟩
  intro hWeak
  have := hWeak 0 1 rfl
  cases this

/-! ### Least-Restrictive `MaxPol` Shield & Transparency (`liberty` + `transparency`) -/

/-- **Maximal Sound Policy (`MaxPol`)**: permits an action `a` at `s` iff `safe s → safe (step s a)`. -/
@[expose] def maxPol {S A : Type} (step : S → A → S) (safe : S → Prop) [DecidablePred safe] :
    Policy S A :=
  fun s a => decide (safe s → safe (step s a))

/-- Whether the envelope overrides the controller at state `s`. -/
def Intervenes {S A : Type} (pol : Policy S A) (shield ctrl : S → A) (s : S) : Prop :=
  enveloped pol shield ctrl s ≠ ctrl s

theorem maxPol_sound {S A : Type} (step : S → A → S) (safe : S → Prop) [DecidablePred safe] :
    SoundPolicy step safe (maxPol step safe) := by
  intro s a hs hm
  exact (of_decide_eq_true hm) hs

theorem maxPol_is_greatest_sound {S A : Type} {step : S → A → S} {safe : S → Prop}
    [DecidablePred safe] {pol : Policy S A} (hSound : SoundPolicy step safe pol) :
    Weaker (maxPol step safe) pol := by
  intro s a hp
  exact decide_eq_true (fun hs => hSound s a hs hp)

/-- **Least-Restrictive Envelope Theorem (`liberty : envelope_is_least_restrictive`)**:
    `maxPol` is sound, contains every sound policy, and every restriction it imposes is load-bearing
    (any policy admitting from a safe state an action `maxPol` refuses is unsound). -/
theorem envelope_is_least_restrictive {S A : Type} (step : S → A → S) (safe : S → Prop)
    [DecidablePred safe] :
    SoundPolicy step safe (maxPol step safe) ∧
    (∀ pol, SoundPolicy step safe pol → Weaker (maxPol step safe) pol) ∧
    (∀ q s a, safe s → q s a = true → maxPol step safe s a = false → ¬ SoundPolicy step safe q) := by
  refine ⟨maxPol_sound step safe, fun _ h => maxPol_is_greatest_sound h, ?_⟩
  intro q s a hs hq hm hSound
  have hImp : safe s → safe (step s a) := fun h => hSound s a h hq
  have hm_true : maxPol step safe s a = true := decide_eq_true hImp
  rw [hm_true] at hm
  cases hm

theorem reach_agree {S A : Type} {step : S → A → S} {init : S → Prop} {sel ctrl : S → A}
    (hAgree : ∀ t, Reach step init ctrl t → sel t = ctrl t) :
    ∀ s, Reach step init sel s ↔ Reach step init ctrl s := by
  intro s
  constructor
  · intro hr
    induction hr with
    | init hi => exact .init hi
    | @step x _ ih =>
      rw [hAgree x ih]
      exact .step ih
  · intro hr
    induction hr with
    | init hi => exact .init hi
    | @step x _ ih =>
      rw [← hAgree x ‹_›]
      exact .step ih

/-- **Transparent Run Theorem (`transparency : maxpol_transparent_run`)**:
    Any controller whose bare run stays inside `safe` is NEVER overridden by `maxPol` along its
    run, and its `maxPol`-enveloped reachable set coincides identically with its bare reachable set. -/
theorem maxpol_transparent_run {S A : Type} {step : S → A → S} {init safe : S → Prop}
    [DecidablePred safe] (shield : S → A) {ctrl : S → A}
    (hBareSafe : Invariant step init ctrl safe) :
    (∀ s, Reach step init ctrl s → enveloped (maxPol step safe) shield ctrl s = ctrl s) ∧
    (∀ s, Reach step init (enveloped (maxPol step safe) shield ctrl) s ↔ Reach step init ctrl s) := by
  have hNoOverride : ∀ s, Reach step init ctrl s →
      enveloped (maxPol step safe) shield ctrl s = ctrl s := by
    intro s hr
    have hsNext : safe (step s (ctrl s)) := hBareSafe _ (.step hr)
    have hm : maxPol step safe s (ctrl s) = true := decide_eq_true (fun _ => hsNext)
    simp [enveloped, hm]
  exact ⟨hNoOverride, reach_agree hNoOverride⟩

/-- **Exact Characterization of Transparent Runs (`maxpol_transparent_run_iff`)**:
    Under `InitSafe` and `SafeShield`, a bare controller is safe on its own **if and only if**
    its `maxPol`-enveloped reachable states coincide with its bare reachable states. -/
theorem maxpol_transparent_run_iff {S A : Type} {step : S → A → S} {init safe : S → Prop}
    [DecidablePred safe] {shield : S → A} (ctrl : S → A)
    (hInit : InitSafe init safe) (hSh : SafeShield step safe shield) :
    Invariant step init ctrl safe ↔
      (∀ s, Reach step init (enveloped (maxPol step safe) shield ctrl) s ↔ Reach step init ctrl s) := by
  constructor
  · intro hBare
    exact (maxpol_transparent_run shield hBare).2
  · intro hEq s hrBare
    have hEnvInv := safety_preservation hInit (maxPol_sound step safe) hSh ctrl
    exact hEnvInv s ((hEq s).mpr hrBare)

theorem maxpol_intervenes_iff_unsafe {S A : Type} {step : S → A → S} {safe : S → Prop}
    [DecidablePred safe] {shield : S → A} (ctrl : S → A)
    (hSh : SafeShield step safe shield) {s : S} (hs : safe s) :
    Intervenes (maxPol step safe) shield ctrl s ↔ ¬ safe (step s (ctrl s)) := by
  unfold Intervenes enveloped
  by_cases hNext : safe (step s (ctrl s))
  · have hm : maxPol step safe s (ctrl s) = true := decide_eq_true (fun _ => hNext)
    simp [hm, hNext]
  · have hm : maxPol step safe s (ctrl s) = false :=
      decide_eq_false (fun hImp => hNext (hImp hs))
    simp only [hm, Bool.false_eq_true, ↓reduceIte, ne_eq, hNext, not_false_eq_true, iff_true]
    intro hEq
    have hShSafe : safe (step s (shield s)) := hSh s hs
    rw [hEq] at hShSafe
    exact hNext hShSafe

/-! ### Deterministic $B$-Step Corrigibility & `override_iff_burned_bridge` -/

/-- Iterate recovery operator `recov` for `n` steps from `s`. -/
def recovIter {S A : Type} (step : S → A → S) (recov : S → A) : Nat → S → S
  | 0, s => s
  | n + 1, s => recovIter step recov n (step s (recov s))

/-- Deterministic $B$-step latency-bounded corrigibility (`corrigibility : cwithin`). -/
def CWithin {S A : Type} (step : S → A → S) (recov : S → A) (home : S → Prop) (B : Nat) (s : S) : Prop :=
  ∃ n ≤ B, home (recovIter step recov n s)

/-- Executable decision procedure for `CWithin` whenever `home` is decidable. -/
@[expose] def cwithinBool {S A : Type} (step : S → A → S) (recov : S → A)
    (home : S → Prop) [DecidablePred home] (B : Nat) (s : S) : Bool :=
  (List.range (B + 1)).any fun n => decide (home (recovIter step recov n s))

theorem cwithinBool_iff {S A : Type} (step : S → A → S) (recov : S → A)
    (home : S → Prop) [DecidablePred home] (B : Nat) (s : S) :
    cwithinBool step recov home B s = true ↔ CWithin step recov home B s := by
  unfold cwithinBool CWithin
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨n, hlt, hh⟩
    exact ⟨n, by omega, hh⟩
  · rintro ⟨n, hle, hh⟩
    exact ⟨n, by omega, hh⟩

instance instDecidableCWithin {S A : Type} (step : S → A → S) (recov : S → A)
    (home : S → Prop) [DecidablePred home] (B : Nat) :
    DecidablePred (CWithin step recov home B) :=
  fun s =>
    if h : cwithinBool step recov home B s = true then
      isTrue ((cwithinBool_iff step recov home B s).mp h)
    else
      isFalse (fun hc => h ((cwithinBool_iff step recov home B s).mpr hc))

/-- `home` is parked under `recov`: applying `recov` at `home` stays in `home`. -/
def HomeRecovParked {S A : Type} (step : S → A → S) (recov : S → A) (home : S → Prop) : Prop :=
  ∀ s, home s → home (step s (recov s))

theorem recov_is_safe_shield_within {S A : Type} {step : S → A → S} {recov : S → A}
    {home : S → Prop} (B : Nat) (hParked : HomeRecovParked step recov home) :
    SafeShield step (CWithin step recov home B) recov := by
  intro s ⟨n, hle, hh⟩
  cases n with
  | zero =>
    exact ⟨0, Nat.zero_le B, hParked s hh⟩
  | succ m =>
    exact ⟨m, by omega, hh⟩

/-- **Burned-Bridge Characterization (`override_iff_burned_bridge`)**:
    Under `maxPol` for $B$-step corrigibility (`CWithin step recov home B`) with a parked `home`,
    from any $B$-corrigible state `s`, the shield `recov` overrides `ctrl s` **if and only if**
    `ctrl s` would burn the operator's $B$-step recovery bridge (`¬ CWithin ... (step s (ctrl s))`). -/
theorem override_iff_burned_bridge {S A : Type} {step : S → A → S} {recov : S → A}
    {home : S → Prop} [DecidablePred home] (B : Nat) (ctrl : S → A)
    (hParked : HomeRecovParked step recov home) {s : S}
    (hs : CWithin step recov home B s) :
    enveloped (maxPol step (CWithin step recov home B)) recov ctrl s ≠ ctrl s ↔
      ¬ CWithin step recov home B (step s (ctrl s)) :=
  maxpol_intervenes_iff_unsafe ctrl (recov_is_safe_shield_within B hParked) hs

/-! ## 2. Demonic $B$-Step Latency-Bounded Corrigibility over Relational & Disturbed Plants -/

/-- Nondeterministic / adversarial plant transition relation. -/
abbrev PlantR (S A : Type) := S → A → S → Prop

/-- Action `a` has at least one successor from `s` in `stepr`. -/
def Enabled {S A : Type} (stepr : PlantR S A) (s : S) (a : A) : Prop :=
  ∃ s', stepr s a s'

/-- Every `(s, a)` is enabled in `stepr`. -/
def TotalR {S A : Type} (stepr : PlantR S A) : Prop :=
  ∀ s a, Enabled stepr s a

/-- Graph of a deterministic `step` as a relational plant. -/
def Det {S A : Type} (step : S → A → S) : PlantR S A :=
  fun s a s' => s' = step s a

/-- Relational reachability under selector `sel`. -/
inductive ReachR {S A : Type} (stepr : PlantR S A) (init : S → Prop) (sel : S → A) : S → Prop
  | init {s : S} : init s → ReachR stepr init sel s
  | step {s s' : S} : ReachR stepr init sel s → stepr s (sel s) s' → ReachR stepr init sel s'

def StepClosedR {S A : Type} (stepr : PlantR S A) (sel : S → A) (safe : S → Prop) : Prop :=
  ∀ s s', safe s → stepr s (sel s) s' → safe s'

def InvariantR {S A : Type} (stepr : PlantR S A) (init : S → Prop) (sel : S → A) (safe : S → Prop) : Prop :=
  ∀ s, ReachR stepr init sel s → safe s

theorem invariantR_intro {S A : Type} {stepr : PlantR S A} {init : S → Prop}
    {sel : S → A} {safe : S → Prop}
    (hInit : InitSafe init safe) (hClosed : StepClosedR stepr sel safe) :
    InvariantR stepr init sel safe := by
  intro s hr
  induction hr with
  | init hi => exact hInit _ hi
  | step _ hst ih => exact hClosed _ _ ih hst

/-- Demonic relational policy soundness: every successor of a permitted action from `safe` is `safe`. -/
def SoundPolicyR {S A : Type} (stepr : PlantR S A) (safe : S → Prop) (pol : Policy S A) : Prop :=
  ∀ s a s', safe s → pol s a = true → stepr s a s' → safe s'

/-- Angelic relational policy soundness (`relEnvelope : angelic_soundr`): SOME successor is `safe`. -/
def AngelicSoundR {S A : Type} (stepr : PlantR S A) (safe : S → Prop) (pol : Policy S A) : Prop :=
  ∀ s a, safe s → pol s a = true → ∃ s', stepr s a s' ∧ safe s'

def SafeShieldR {S A : Type} (stepr : PlantR S A) (safe : S → Prop) (shield : S → A) : Prop :=
  ∀ s s', safe s → stepr s (shield s) s' → safe s'

def LivePolicyR {S A : Type} (stepr : PlantR S A) (safe : S → Prop) (pol : Policy S A) : Prop :=
  ∀ s a, safe s → pol s a = true → Enabled stepr s a

def LiveShieldR {S A : Type} (stepr : PlantR S A) (safe : S → Prop) (shield : S → A) : Prop :=
  ∀ s, safe s → Enabled stepr s (shield s)

theorem safety_preservationR {S A : Type} {stepr : PlantR S A} {init safe : S → Prop}
    {pol : Policy S A} {shield : S → A}
    (hInit : InitSafe init safe) (hPol : SoundPolicyR stepr safe pol) (hSh : SafeShieldR stepr safe shield) :
    ∀ ctrl, InvariantR stepr init (enveloped pol shield ctrl) safe := by
  intro ctrl
  apply invariantR_intro hInit
  intro s s' hs hst
  unfold enveloped at hst
  cases hp : pol s (ctrl s) with
  | true =>
    rw [hp] at hst
    exact hPol s (ctrl s) s' hs hp hst
  | false =>
    rw [hp] at hst
    exact hSh s s' hs hst

theorem enveloped_nonblocking {S A : Type} {stepr : PlantR S A} {init safe : S → Prop}
    {pol : Policy S A} {shield : S → A}
    (hInit : InitSafe init safe) (hPol : SoundPolicyR stepr safe pol) (hSh : SafeShieldR stepr safe shield)
    (hLivePol : LivePolicyR stepr safe pol) (hLiveSh : LiveShieldR stepr safe shield) :
    ∀ ctrl s, ReachR stepr init (enveloped pol shield ctrl) s →
      Enabled stepr s (enveloped pol shield ctrl s) := by
  intro ctrl s hr
  have hs : safe s := safety_preservationR hInit hPol hSh ctrl s hr
  unfold enveloped
  cases hp : pol s (ctrl s) with
  | true => exact hLivePol s (ctrl s) hs hp
  | false => exact hLiveSh s hs

/-- **Demonic $B$-Step Game-Tree Corrigibility (`DemonicRecovWithin stepr recov home B`)**:
    Within at most `B` steps of applying `recov`, the system is guaranteed to reach `home`
    against **every** adversarial or nondeterministic environment transition, without deadlocking. -/
def DemonicRecovWithin {S A : Type} (stepr : PlantR S A) (recov : S → A) (home : S → Prop) :
    Nat → S → Prop
  | 0, s => home s
  | B + 1, s =>
    home s ∨ (Enabled stepr s (recov s) ∧ ∀ s', stepr s (recov s) s' → DemonicRecovWithin stepr recov home B s')

/-- Angelic $B$-step recoverability (existential over plant transitions — proved insufficient below!). -/
def AngelicRecovWithin {S A : Type} (stepr : PlantR S A) (recov : S → A) (home : S → Prop) :
    Nat → S → Prop
  | 0, s => home s
  | B + 1, s =>
    home s ∨ ∃ s', stepr s (recov s) s' ∧ AngelicRecovWithin stepr recov home B s'

/-- Relational parkedness of `home` under `recov`. -/
def HomeRecovParkedR {S A : Type} (stepr : PlantR S A) (recov : S → A) (home : S → Prop) : Prop :=
  ∀ s, home s → Enabled stepr s (recov s) ∧ ∀ s', stepr s (recov s) s' → home s'

theorem demonicRecovWithin_mono {S A : Type} {stepr : PlantR S A} {recov : S → A} {home : S → Prop} :
    ∀ {B B' : Nat} {s : S}, B ≤ B' →
      DemonicRecovWithin stepr recov home B s → DemonicRecovWithin stepr recov home B' s
  | 0, 0, _, _, h => h
  | 0, _ + 1, _, _, h => .inl h
  | _ + 1, 0, _, hle, _ => by omega
  | B + 1, B' + 1, s, hle, h => by
    rcases h with hh | ⟨hen, hall⟩
    · exact .inl hh
    · exact .inr ⟨hen, fun s' hst => demonicRecovWithin_mono (by omega) (hall s' hst)⟩

/-- Deterministic Collapse: on `Det step`, `DemonicRecovWithin` is equivalent to `CWithin`. -/
theorem demonicRecovWithin_det_iff {S A : Type} (step : S → A → S) (recov : S → A)
    (home : S → Prop) :
    ∀ (B : Nat) (s : S),
      DemonicRecovWithin (Det step) recov home B s ↔ CWithin step recov home B s
  | 0, s => by
    simp only [DemonicRecovWithin, CWithin]
    constructor
    · intro hh; exact ⟨0, Nat.le_refl 0, hh⟩
    · rintro ⟨n, hle, hh⟩
      have hn0 : n = 0 := by omega
      subst hn0
      exact hh
  | B + 1, s => by
    simp only [DemonicRecovWithin, Det, Enabled]
    constructor
    · rintro (hh | ⟨_, hall⟩)
      · exact ⟨0, Nat.zero_le _, hh⟩
      · have hd := hall (step s (recov s)) rfl
        obtain ⟨m, hm, hh⟩ := (demonicRecovWithin_det_iff step recov home B (step s (recov s))).mp hd
        exact ⟨m + 1, by omega, hh⟩
    · rintro ⟨n, hle, hh⟩
      cases n with
      | zero => exact .inl hh
      | succ m =>
        right
        refine ⟨⟨step s (recov s), rfl⟩, fun s' hs' => ?_⟩
        subst hs'
        exact (demonicRecovWithin_det_iff step recov home B (step s (recov s))).mpr ⟨m, by omega, hh⟩

/-- `recov` is simultaneously a `SafeShieldR` and a `LiveShieldR` for `DemonicRecovWithin ... B`. -/
theorem recov_is_safe_and_live_shield_B {S A : Type} {stepr : PlantR S A} {recov : S → A}
    {home : S → Prop} (B : Nat) (hParked : HomeRecovParkedR stepr recov home) :
    SafeShieldR stepr (DemonicRecovWithin stepr recov home B) recov ∧
    LiveShieldR stepr (DemonicRecovWithin stepr recov home B) recov := by
  constructor
  · intro s s' hd hst
    cases B with
    | zero =>
      exact (hParked s hd).2 s' hst
    | succ m =>
      rcases hd with hh | ⟨_, hall⟩
      · exact .inl ((hParked s hh).2 s' hst)
      · exact demonicRecovWithin_mono (Nat.le_succ m) (hall s' hst)
  · intro s hd
    cases B with
    | zero => exact (hParked s hd).1
    | succ m =>
      rcases hd with hh | ⟨hen, _⟩
      · exact (hParked s hh).1
      · exact hen

/-- **Relational $B$-Latency Corrigibility & Non-Blocking Theorem**:
    Against any nondeterministic/adversarial plant `stepr`, an envelope with a demonically sound
    and live policy keeps every reachable state demonically $B$-corrigible AND deadlock-free. -/
theorem demonic_corrigibility_B_floor_holds {S A : Type} {stepr : PlantR S A}
    {init home : S → Prop} {recov : S → A} {pol : Policy S A} (B : Nat)
    (hParked : HomeRecovParkedR stepr recov home)
    (hInit : InitSafe init (DemonicRecovWithin stepr recov home B))
    (hSound : SoundPolicyR stepr (DemonicRecovWithin stepr recov home B) pol)
    (hLive : LivePolicyR stepr (DemonicRecovWithin stepr recov home B) pol) :
    ∀ ctrl,
      InvariantR stepr init (enveloped pol recov ctrl) (DemonicRecovWithin stepr recov home B) ∧
      (∀ s, ReachR stepr init (enveloped pol recov ctrl) s →
        Enabled stepr s (enveloped pol recov ctrl s)) := by
  obtain ⟨hShSafe, hShLive⟩ := recov_is_safe_and_live_shield_B B hParked
  exact fun ctrl =>
    ⟨safety_preservationR hInit hSound hShSafe ctrl,
     enveloped_nonblocking hInit hSound hShSafe hLive hShLive ctrl⟩

/-! ### Disturbed Plants (`relEnvelope : disturbed`, `drun`) -/

/-- Plant driven by an adversary picking disturbance `d` satisfying `admD d` at each step. -/
def Disturbed {S A D : Type} (dstep : S → A → D → S) (admD : D → Prop) : PlantR S A :=
  fun s a s' => ∃ d, admD d ∧ s' = dstep s a d

/-- Trajectory under disturbance stream `ds : Nat → D`. -/
def drun {S A D : Type} (dstep : S → A → D → S) (sel : S → A) (ds : Nat → D) (x₀ : S) : Nat → S
  | 0 => x₀
  | n + 1 =>
    let cur := drun dstep sel ds x₀ n
    dstep cur (sel cur) (ds n)

theorem drun_reachR {S A D : Type} (dstep : S → A → D → S) (admD : D → Prop)
    (init : S → Prop) (sel : S → A) (ds : Nat → D) (x₀ : S) (h₀ : init x₀) :
    ∀ n, (∀ m < n, admD (ds m)) → ReachR (Disturbed dstep admD) init sel (drun dstep sel ds x₀ n)
  | 0, _ => .init h₀
  | n + 1, hAdm =>
    .step (drun_reachR dstep admD init sel ds x₀ h₀ n (fun m hm => hAdm m (by omega)))
      ⟨ds n, hAdm n (Nat.lt_succ_self n), rfl⟩

/-- **Disturbed Plant $B$-Latency Corrigibility**: every disturbance sequence `ds` keeps the
    enveloped state demonically $B$-corrigible at every step `n`. -/
theorem disturbed_demonic_corrigibility_B_safe {S A D : Type}
    {dstep : S → A → D → S} {admD : D → Prop} {init home : S → Prop}
    {recov : S → A} {pol : Policy S A} (B : Nat)
    (hParked : HomeRecovParkedR (Disturbed dstep admD) recov home)
    (hInit : InitSafe init (DemonicRecovWithin (Disturbed dstep admD) recov home B))
    (hSound : SoundPolicyR (Disturbed dstep admD) (DemonicRecovWithin (Disturbed dstep admD) recov home B) pol)
    (ctrl : S → A) (ds : Nat → D) (x₀ : S) (hx₀ : init x₀) (n : Nat)
    (hDs : ∀ m < n, admD (ds m)) :
    DemonicRecovWithin (Disturbed dstep admD) recov home B
      (drun dstep (enveloped pol recov ctrl) ds x₀ n) := by
  obtain ⟨hShSafe, _⟩ := recov_is_safe_and_live_shield_B B hParked
  exact safety_preservationR hInit hSound hShSafe ctrl _
    (drun_reachR dstep admD init _ ds x₀ hx₀ n hDs)

/-! ### Necessity Counterexample: `angelic_recoverability_insufficient` -/

theorem not_demonic_at_one :
    let stepr : PlantR Nat Nat := fun s a s' => if s = 0 then s' = a else s' ≤ 1
    let home : Nat → Prop := fun s => s = 0
    let recov : Nat → Nat := fun _ => 0
    ∀ B, ¬ DemonicRecovWithin stepr recov home B 1 := by
  intro stepr home recov B
  induction B with
  | zero =>
    simp [DemonicRecovWithin, home]
  | succ m ih =>
    simp only [DemonicRecovWithin, home]
    rintro (h10 | ⟨_, hall⟩)
    · cases h10
    · exact ih (hall 1 (by simp [stepr]))

/-- **Angelic Recoverability & Angelic Policy Soundness Are Insufficient (`angelic_recoverability_insufficient`)**:
    There exists a total nondeterministic plant over `Nat` where:
    1. `home` (`s = 0`) is parked (`HomeRecovParkedR`),
    2. State `1` is **angelically** 1-step recoverable (`AngelicRecovWithin ... 1 1`) because
       the environment *could* transition `1 → 0`,
    3. Policy `pol := fun _ _ => true` is **angelically sound** for `home` from `0` on a plant
       allowing `s' ≤ a`,
    YET state `1` fails `DemonicRecovWithin` for **every** finite latency bound `B : Nat` (an
    adversary picks `1 → 1` forever), and `AngelicSoundR` fails `InvariantR` in 1 step! -/
theorem angelic_recoverability_insufficient :
    ∃ (stepr : PlantR Nat Nat) (home init : Nat → Prop) (recov ctrl : Nat → Nat)
      (pol : Policy Nat Nat),
      HomeRecovParkedR stepr recov home ∧
      AngelicRecovWithin stepr recov home 1 1 ∧
      (∀ B, ¬ DemonicRecovWithin stepr recov home B 1) ∧
      InitSafe init home ∧
      AngelicSoundR (fun _ a s' => s' ≤ a) home pol ∧
      SafeShieldR (fun _ a s' => s' ≤ a) home recov ∧
      ¬ InvariantR (fun _ a s' => s' ≤ a) init (enveloped pol recov ctrl) home := by
  let stepr : PlantR Nat Nat := fun s a s' => if s = 0 then s' = a else s' ≤ 1
  let home : Nat → Prop := fun s => s = 0
  let init : Nat → Prop := fun s => s = 0
  let recov : Nat → Nat := fun _ => 0
  let ctrl : Nat → Nat := fun _ => 1
  let pol : Policy Nat Nat := fun _ _ => true
  refine ⟨stepr, home, init, recov, ctrl, pol, ?_, ?_, not_demonic_at_one, ?_, ?_, ?_, ?_⟩
  · intro s hs
    subst hs
    exact ⟨⟨0, by simp [stepr, recov]⟩, fun s' hs' => by simpa [stepr, recov] using hs'⟩
  · right
    exact ⟨0, by simp [stepr], rfl⟩
  · intro s hs; exact hs
  · intro s a _ _
    exact ⟨0, Nat.zero_le a, rfl⟩
  · intro s s' _ hs'
    simpa [recov] using hs'
  · intro hInv
    have hr1 : ReachR (fun _ a s' => s' ≤ a) init (enveloped pol recov ctrl) 1 :=
      .step (.init rfl) (by simp [enveloped, pol, ctrl])
    have h0 : (1 : Nat) = 0 := hInv 1 hr1
    cases h0

/-! ### Self-Modifying Off-Switch Latency Gate (`self_mod_preserves_latency_B`) & Disjoint Homes -/

/-- Certified gate (`certifier : cgate`): installs `cand` iff `yes = true`, else keeps `cur`. -/
@[expose] def cgate {α : Type} (yes : Bool) (cur cand : α) : α :=
  if yes then cand else cur

/-- Fold `cgate` across a sequence of `(cert, candidate)` upgrade offers. -/
def cgateRun {α : Type} (x₀ : α) : List (Bool × α) → α
  | [] => x₀
  | (yes, cand) :: rest => cgateRun (cgate yes x₀ cand) rest

/-- Admissibility of a proposed new recovery policy `newrec` at latency deadline `B`:
    `newrec` keeps `home` parked AND never increases demonic recovery latency past `B`. -/
def RecovAdmissibleB {S A : Type} (stepr : PlantR S A) (home : S → Prop) (B : Nat)
    (oldrec newrec : S → A) : Prop :=
  HomeRecovParkedR stepr newrec home ∧
  ∀ s, DemonicRecovWithin stepr oldrec home B s → DemonicRecovWithin stepr newrec home B s

theorem cgate_recov_preserves_B {S A : Type} {stepr : PlantR S A} {home : S → Prop} {B : Nat}
    {oldrec newrec : S → A} {yes : Bool}
    (hCert : yes = true → RecovAdmissibleB stepr home B oldrec newrec)
    (hParked : HomeRecovParkedR stepr oldrec home) :
    HomeRecovParkedR stepr (cgate yes oldrec newrec) home ∧
    (∀ s, DemonicRecovWithin stepr oldrec home B s →
      DemonicRecovWithin stepr (cgate yes oldrec newrec) home B s) := by
  cases yes with
  | false => exact ⟨hParked, fun _ h => h⟩
  | true => exact hCert rfl

/-- **Self-Modification Never Increases Recovery Latency Past $B$ (`self_mod_preserves_latency_B`)**:
    Across any finite sequence of off-switch self-modification offers `offers` whose accepted
    verdicts satisfy `RecovAdmissibleB`, the final recovery shield keeps `home` parked AND
    preserves `DemonicRecovWithin ... B` on every state that was $B$-corrigible at genesis. -/
theorem self_mod_preserves_latency_B {S A : Type} {stepr : PlantR S A} {home : S → Prop} (B : Nat) :
    ∀ (offers : List (Bool × (S → A))) (rec₀ : S → A),
      HomeRecovParkedR stepr rec₀ home →
      (∀ ( idx : Nat ) (pair : Bool × (S → A)),
        offers[idx]? = some pair →
        pair.1 = true →
        RecovAdmissibleB stepr home B (cgateRun rec₀ (offers.take idx)) pair.2) →
      HomeRecovParkedR stepr (cgateRun rec₀ offers) home ∧
      (∀ s, DemonicRecovWithin stepr rec₀ home B s →
        DemonicRecovWithin stepr (cgateRun rec₀ offers) home B s)
  | [], rec₀, hParked, _ => ⟨hParked, fun _ h => h⟩
  | (yes, cand) :: rest, rec₀, hParked, hOffers => by
    have h0 : yes = true → RecovAdmissibleB stepr home B rec₀ cand :=
      fun hy => hOffers 0 (yes, cand) rfl hy
    obtain ⟨hParked1, hSub1⟩ := cgate_recov_preserves_B h0 hParked
    have hRest : ∀ (idx : Nat) (pair : Bool × (S → A)),
        rest[idx]? = some pair → pair.1 = true →
        RecovAdmissibleB stepr home B (cgateRun (cgate yes rec₀ cand) (rest.take idx)) pair.2 := by
      intro idx pair hget hy
      simpa [cgateRun, List.take_succ_cons] using hOffers (idx + 1) pair hget hy
    obtain ⟨hParkedFinal, hSubFinal⟩ :=
      self_mod_preserves_latency_B B rest (cgate yes rec₀ cand) hParked1 hRest
    exact ⟨hParkedFinal, fun s hs => hSubFinal s (hSub1 s hs)⟩

/-- Conjunctive N-version operator home (`corrigibility : home_and`). -/
def HomeAnd {S : Type} (h₁ h₂ : S → Prop) (s : S) : Prop :=
  h₁ s ∧ h₂ s

theorem demonicRecovWithin_homeAnd_imp_both {S A : Type} {stepr : PlantR S A} {recov : S → A}
    {h₁ h₂ : S → Prop} :
    ∀ (B : Nat) (s : S),
      DemonicRecovWithin stepr recov (HomeAnd h₁ h₂) B s →
      DemonicRecovWithin stepr recov h₁ B s ∧ DemonicRecovWithin stepr recov h₂ B s
  | 0, _, ⟨hh1, hh2⟩ => ⟨hh1, hh2⟩
  | B + 1, s, h => by
    rcases h with ⟨hh1, hh2⟩ | ⟨hen, hall⟩
    · exact ⟨.inl hh1, .inl hh2⟩
    · exact ⟨.inr ⟨hen, fun s' hst => (demonicRecovWithin_homeAnd_imp_both B s' (hall s' hst)).1⟩,
             .inr ⟨hen, fun s' hst => (demonicRecovWithin_homeAnd_imp_both B s' (hall s' hst)).2⟩⟩

/-- **Disjoint Operator Homes Empty the Corrigibility Floor (`disjoint_homes_empty_floor`)**:
    If two operators specify mutually incompatible `home` predicates (`∀ s, ¬ (h₁ s ∧ h₂ s)`),
    then `DemonicRecovWithin stepr recov (HomeAnd h₁ h₂) B s` is uninhabited for every `B` and `s`. -/
theorem disjoint_homes_empty_floor {S A : Type} (stepr : PlantR S A) (recov : S → A)
    {h₁ h₂ : S → Prop} (hDisj : ∀ s, ¬ (h₁ s ∧ h₂ s)) :
    ∀ (B : Nat) (s : S), ¬ DemonicRecovWithin stepr recov (HomeAnd h₁ h₂) B s
  | 0, s, hh => hDisj s hh
  | _ + 1, s, .inl hh => hDisj s hh
  | B + 1, _, .inr ⟨⟨s', hst⟩, hall⟩ =>
    disjoint_homes_empty_floor stepr recov hDisj B s' (hall s' hst)

/-! ## 3. 3-Tier Constitutional Stack (`Bedrock → Meta → Spec`) & `Genealogy.Habitat` Integration -/

/-- State-predicate refinement (`specNeg : spec_refines`): `sub` entails `sup`. -/
def SpecRefines {S : Type} (sub sup : S → Prop) : Prop :=
  ∀ s, sub s → sup s

@[simp] theorem specRefines_refl {S : Type} (p : S → Prop) : SpecRefines p p :=
  fun _ h => h

theorem specRefines_trans {S : Type} {a b c : S → Prop}
    (hab : SpecRefines a b) (hbc : SpecRefines b c) : SpecRefines a c :=
  fun s ha => hbc s (hab s ha)

theorem invariantR_transports_to_meta {S A : Type} {stepr : PlantR S A}
    {init : S → Prop} {sel : S → A} {spec metaSpec : S → Prop}
    (hInv : InvariantR stepr init sel spec) (hRef : SpecRefines spec metaSpec) :
    InvariantR stepr init sel metaSpec :=
  fun s hr => hRef s (hInv s hr)

/-- Exact `iff` characterization of certified spec gates (`specNeg : spec_gate_keeps_refining_iff`). -/
theorem spec_gate_keeps_refining_iff {S : Type} (cert : Bool) (newspec metaSpec : S → Prop) :
    (∀ curspec, SpecRefines curspec metaSpec → SpecRefines (cgate cert curspec newspec) metaSpec) ↔
      (cert = true → SpecRefines newspec metaSpec) := by
  cases cert with
  | false => simp [cgate]
  | true =>
    simp only [cgate, ↓reduceIte, true_implies]
    exact ⟨fun h => h metaSpec (specRefines_refl metaSpec), fun h _ _ => h⟩

theorem cgateRun_keeps_refining {S : Type} (target : S → Prop) :
    ∀ (offers : List (Bool × (S → Prop))) (s₀ : S → Prop),
      SpecRefines s₀ target →
      (∀ pair ∈ offers, pair.1 = true → SpecRefines pair.2 target) →
      SpecRefines (cgateRun s₀ offers) target
  | [], _, hRef, _ => hRef
  | (yes, cand) :: rest, s₀, hRef, hAll => by
    have hStep : SpecRefines (cgate yes s₀ cand) target := by
      cases yes with
      | false => exact hRef
      | true => exact hAll (true, cand) List.mem_cons_self rfl
    exact cgateRun_keeps_refining target rest (cgate yes s₀ cand) hStep
      (fun p hp => hAll p (List.mem_cons_of_mem _ hp))

/-- Meta-amendment fold (`specNeg : amended_meta`). -/
def amendedMeta {S : Type} (meta₀ : S → Prop) (mproposals : List (Bool × (S → Prop))) : S → Prop :=
  cgateRun meta₀ mproposals

/-- **Tier-0 Immovability (`bedrock_is_eternal`)**:
    Across arbitrarily many certified constitutional meta-amendments `mproposals`, if `meta₀`
    refines `bedrock` and every accepted meta-amendment refines `bedrock`, the resulting
    `amendedMeta` always refines `bedrock`. -/
theorem bedrock_is_eternal {S : Type} {bedrock meta₀ : S → Prop}
    (hBase : SpecRefines meta₀ bedrock)
    (mproposals : List (Bool × (S → Prop)))
    (hCerts : ∀ pair ∈ mproposals, pair.1 = true → SpecRefines pair.2 bedrock) :
    SpecRefines (amendedMeta meta₀ mproposals) bedrock :=
  cgateRun_keeps_refining bedrock mproposals meta₀ hBase hCerts

/-- **Tier-2 Spec Negotiation Safety (`spec_negotiation_safe`)**:
    Across any sequence of certified spec negotiations `sproposals` under `metaSpec`, any controller
    wrapped in an envelope sound for the negotiated spec preserves `metaSpec` on all reachable states. -/
theorem spec_negotiation_safe {S A : Type} {stepr : PlantR S A}
    {init metaSpec spec₀ : S → Prop} {pol : Policy S A} {shield : S → A}
    (sproposals : List (Bool × (S → Prop)))
    (hSpec₀ : SpecRefines spec₀ metaSpec)
    (hCerts : ∀ pair ∈ sproposals, pair.1 = true → SpecRefines pair.2 metaSpec)
    (hInit : InitSafe init (cgateRun spec₀ sproposals))
    (hPol : SoundPolicyR stepr (cgateRun spec₀ sproposals) pol)
    (hSh : SafeShieldR stepr (cgateRun spec₀ sproposals) shield) :
    ∀ ctrl, InvariantR stepr init (enveloped pol shield ctrl) metaSpec := by
  intro ctrl
  have hNegotiatedRef := cgateRun_keeps_refining metaSpec sproposals spec₀ hSpec₀ hCerts
  have hInvSpec := safety_preservationR hInit hPol hSh ctrl
  exact invariantR_transports_to_meta hInvSpec hNegotiatedRef

/-- **3-Tier Constitutional Stack Safety (`meta_amendment_safe`)**:
    Combining constitutional meta-amendments `mproposals` over `bedrock` AND operational spec
    negotiations `sproposals` over `amendedMeta meta₀ mproposals`, every enveloped controller
    preserves the eternal `bedrock` on all reachable states. -/
theorem meta_amendment_safe {S A : Type} {stepr : PlantR S A}
    {init bedrock meta₀ spec₀ : S → Prop} {pol : Policy S A} {shield : S → A}
    (mproposals : List (Bool × (S → Prop)))
    (sproposals : List (Bool × (S → Prop)))
    (hMeta₀ : SpecRefines meta₀ bedrock)
    (hMetaCerts : ∀ pair ∈ mproposals, pair.1 = true → SpecRefines pair.2 bedrock)
    (hSpec₀ : SpecRefines spec₀ (amendedMeta meta₀ mproposals))
    (hSpecCerts : ∀ pair ∈ sproposals, pair.1 = true → SpecRefines pair.2 (amendedMeta meta₀ mproposals))
    (hInit : InitSafe init (cgateRun spec₀ sproposals))
    (hPol : SoundPolicyR stepr (cgateRun spec₀ sproposals) pol)
    (hSh : SafeShieldR stepr (cgateRun spec₀ sproposals) shield) :
    ∀ ctrl, InvariantR stepr init (enveloped pol shield ctrl) bedrock := by
  intro ctrl
  have hInvMeta := spec_negotiation_safe sproposals hSpec₀ hSpecCerts hInit hPol hSh ctrl
  have hBedrock := bedrock_is_eternal hMeta₀ mproposals hMetaCerts
  exact invariantR_transports_to_meta hInvMeta hBedrock

/-! ### Direct Wiring into `Obend.Judge.Genealogy.Habitat` -/

/-- Decidable syntactic containment check `required ⊆ exported` on `H.Floor` lists. -/
@[expose] def floorsContainAll (H : Habitat) (exported required : List H.Floor) : Bool :=
  required.all fun φ => exported.contains φ

theorem floorsContainAll_iff (H : Habitat) (exported required : List H.Floor) :
    floorsContainAll H exported required = true ↔ ∀ φ ∈ required, φ ∈ exported := by
  simp [floorsContainAll, List.all_eq_true]

/-- **3-Tier Constitutional Stack over `H : Genealogy.Habitat`**:
    - `bedrockFloors` (Tier 0): eternal corrigibility floors (`H.bedrock φ = true`),
    - `metaFloors` (Tier 1): constitutional meta-floors containing `bedrockFloors`,
    - `specGate` (Tier 2): active `Gate H` whose `floors` contain `metaFloors`, permitting
      lateral renegotiation of non-meta task floors while keeping `metaFloors` and `bedrockFloors`
      inviolate. -/
structure ConstitutionalStack (H : Habitat) where
  bedrockFloors : List H.Floor
  metaFloors : List H.Floor
  specGate : Gate H
  state : H.State
  spentLabels : List TrustBase

/-- Moves proposed to a `ConstitutionalStack H`. -/
inductive ConstitutionalMove (H : Habitat) where
  | act (a : H.Act)
  /-- Lateral Tier-2 spec negotiation: may drop old task-only floors and adopt new task-only
      floors, provided `metaFloors` remain covered and `newGate` is well-formed & holds now. -/
  | negotiateSpec (newGate : Gate H) (labels : List TrustBase)
  /-- Tier-1 constitutional meta-amendment: updates `metaFloors` and `specGate` together,
      provided `bedrockFloors` remain covered by `newMeta` and `newMeta` is covered by `newGate`. -/
  | amendMeta (newMeta : List H.Floor) (newGate : Gate H) (labels : List TrustBase)

/-- Well-formedness check for a Tier-2 spec negotiation on `stack`. -/
def checkSpecNegotiation {H : Habitat} (stack : ConstitutionalStack H)
    (newGate : Gate H) (labels : List TrustBase) : Bool :=
  (Genealogy.wellFormed newGate).toBool &&
  floorsContainAll H newGate.floors stack.metaFloors &&
  (newGate.floors.all fun φ => decide (H.holds φ stack.state)) &&
  (newGate.basis.all fun t => stack.specGate.basis.contains t || labels.contains t)

/-- Well-formedness check for a Tier-1 meta-amendment on `stack`. -/
def checkMetaAmendment {H : Habitat} (stack : ConstitutionalStack H)
    (newMeta : List H.Floor) (newGate : Gate H) (labels : List TrustBase) : Bool :=
  floorsContainAll H newMeta stack.bedrockFloors &&
  (Genealogy.wellFormed newGate).toBool &&
  floorsContainAll H newGate.floors newMeta &&
  (newGate.floors.all fun φ => decide (H.holds φ stack.state)) &&
  (newGate.basis.all fun t => stack.specGate.basis.contains t || labels.contains t)

/-- One step of a `ConstitutionalStack H` under execution model `X`. -/
def ConstitutionalStack.step {H : Habitat} (X : Exec) (stack : ConstitutionalStack H)
    (mv : ConstitutionalMove H) : ConstitutionalStack H :=
  match mv with
  | .act a =>
    if Genealogy.admits X stack.specGate stack.state a then
      { stack with state := H.step a stack.state }
    else stack
  | .negotiateSpec newGate labels =>
    if checkSpecNegotiation stack newGate labels then
      { stack with specGate := newGate, spentLabels := stack.spentLabels ++ labels }
    else stack
  | .amendMeta newMeta newGate labels =>
    if checkMetaAmendment stack newMeta newGate labels then
      { stack with metaFloors := newMeta, specGate := newGate, spentLabels := stack.spentLabels ++ labels }
    else stack

/-- Run a `ConstitutionalStack H` driven by an arbitrary actor (with optional testimony string). -/
def runConstitutional {H : Habitat} {Actor : Type} (X : Exec)
    (actor : Nat → ConstitutionalStack H → Actor × ConstitutionalMove H × String)
    (stack₀ : ConstitutionalStack H) : Nat → ConstitutionalStack H
  | 0 => stack₀
  | n + 1 =>
    let cur := runConstitutional X actor stack₀ n
    cur.step X (actor n cur).2.1

/-- Inductive invariant of `ConstitutionalStack H`. -/
structure ConstitutionalInv {H : Habitat} (G_basis₀ : List TrustBase) (bedrock₀ : List H.Floor)
    (stack : ConstitutionalStack H) : Prop where
  bedrock_eq : stack.bedrockFloors = bedrock₀
  meta_keeps_bedrock : ∀ φ ∈ bedrock₀, φ ∈ stack.metaFloors
  spec_keeps_meta : ∀ φ ∈ stack.metaFloors, φ ∈ stack.specGate.floors
  gate_wf : Genealogy.wellFormed stack.specGate = .ok ()
  floors_hold : ∀ φ ∈ stack.specGate.floors, H.holds φ stack.state
  basis_tracked : ∀ t ∈ stack.specGate.basis, t ∈ G_basis₀ ∨ t ∈ stack.spentLabels

theorem runConstitutional_spent_mono {H : Habitat} {Actor : Type} (X : Exec)
    (actor : Nat → ConstitutionalStack H → Actor × ConstitutionalMove H × String)
    (stack₀ : ConstitutionalStack H) :
    ∀ n t, t ∈ (runConstitutional X actor stack₀ n).spentLabels →
      t ∈ (runConstitutional X actor stack₀ (n + 1)).spentLabels := by
  intro n t ht
  simp only [runConstitutional, ConstitutionalStack.step]
  split
  · split <;> exact ht
  · split
    · exact List.mem_append_left _ ht
    · exact ht
  · split
    · exact List.mem_append_left _ ht
    · exact ht

/-- **Keystone `Habitat` 3-Tier Theorem (`habitat_bedrock_is_eternal`)**:
    Along ANY run of a `ConstitutionalStack H` interleaving arbitrary actions, lateral Tier-2
    spec negotiations, and Tier-1 meta-amendments, every Tier-0 `bedrock` floor holds at every
    step `n`, AND `H.revert` remains unconditionally admitted at every step `n`. -/
theorem habitat_bedrock_is_eternal {H : Habitat} {Actor : Type} (X : Exec)
    (actor : Nat → ConstitutionalStack H → Actor × ConstitutionalMove H × String)
    (stack₀ : ConstitutionalStack H)
    (hWf₀ : Genealogy.wellFormed stack₀.specGate = .ok ())
    (hMeta₀ : ∀ φ ∈ stack₀.bedrockFloors, φ ∈ stack₀.metaFloors)
    (hSpec₀ : ∀ φ ∈ stack₀.metaFloors, φ ∈ stack₀.specGate.floors)
    (hHold₀ : ∀ φ ∈ stack₀.specGate.floors, H.holds φ stack₀.state)
    (hTrusted₀ : ∀ t ∈ stack₀.specGate.basis, X.Holds t) :
    ∀ n, Genealogy.LobCost X (runConstitutional X actor stack₀ n).spentLabels →
      ConstitutionalInv stack₀.specGate.basis stack₀.bedrockFloors
        (runConstitutional X actor stack₀ n) ∧
      (∀ φ ∈ stack₀.bedrockFloors, H.holds φ (runConstitutional X actor stack₀ n).state) ∧
      Genealogy.admits X (runConstitutional X actor stack₀ n).specGate
        (runConstitutional X actor stack₀ n).state H.revert = true := by
  suffices hInv : ∀ n, Genealogy.LobCost X (runConstitutional X actor stack₀ n).spentLabels →
      ConstitutionalInv stack₀.specGate.basis stack₀.bedrockFloors
        (runConstitutional X actor stack₀ n) by
    intro n hLob
    have I := hInv n hLob
    refine ⟨I, fun φ hφ => I.floors_hold φ (I.spec_keeps_meta φ (I.meta_keeps_bedrock φ hφ)),
      Genealogy.revert_admitted X _ I.gate_wf _⟩
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨rfl, hMeta₀, hSpec₀, hWf₀, hHold₀, fun t ht => .inl ht⟩
  | succ m ih =>
    intro hLob
    have I := ih (fun t ht => hLob t (runConstitutional_spent_mono X actor stack₀ m t ht))
    have hCurBasis : ∀ t ∈ (runConstitutional X actor stack₀ m).specGate.basis, X.Holds t := by
      intro t ht
      rcases I.basis_tracked t ht with h0 | hs
      · exact hTrusted₀ t h0
      · exact hLob t (runConstitutional_spent_mono X actor stack₀ m t hs)
    simp only [runConstitutional, ConstitutionalStack.step]
    cases hmv : (actor m (runConstitutional X actor stack₀ m)).2.1 with
    | act a =>
      dsimp only
      split
      · rename_i hAdm
        exact ⟨I.bedrock_eq, I.meta_keeps_bedrock, I.spec_keeps_meta, I.gate_wf,
          fun φ hφ => Genealogy.wellFormed_sound X _ I.gate_wf hCurBasis _ a hAdm φ hφ (I.floors_hold φ hφ),
          I.basis_tracked⟩
      · exact I
    | negotiateSpec newGate labels =>
      dsimp only
      split
      · rename_i hChk
        simp only [checkSpecNegotiation, Bool.and_eq_true, List.all_eq_true] at hChk
        obtain ⟨⟨⟨hwfB, hCont⟩, hNow⟩, hBas⟩ := hChk
        have hWf' := Genealogy.ok_of_toBool hwfB
        have hKeepMeta := (floorsContainAll_iff H newGate.floors _).mp hCont
        refine ⟨I.bedrock_eq, I.meta_keeps_bedrock, hKeepMeta, hWf',
          fun φ hφ => of_decide_eq_true (hNow φ hφ), ?_⟩
        intro t ht
        have hbt := hBas t ht
        simp only [Bool.or_eq_true, List.contains_iff_mem] at hbt
        rcases hbt with hOld | hNew
        · rcases I.basis_tracked t hOld with h0 | hs
          · exact .inl h0
          · exact .inr (List.mem_append_left _ hs)
        · exact .inr (List.mem_append_right _ hNew)
      · exact I
    | amendMeta newMeta newGate labels =>
      dsimp only
      split
      · rename_i hChk
        simp only [checkMetaAmendment, Bool.and_eq_true, List.all_eq_true] at hChk
        obtain ⟨⟨⟨⟨hBed, hwfB⟩, hCont⟩, hNow⟩, hBas⟩ := hChk
        have hWf' := Genealogy.ok_of_toBool hwfB
        have hKeepBed : ∀ φ ∈ stack₀.bedrockFloors, φ ∈ newMeta := by
          rw [← I.bedrock_eq]
          exact (floorsContainAll_iff H newMeta _).mp hBed
        have hKeepMeta := (floorsContainAll_iff H newGate.floors newMeta).mp hCont
        refine ⟨I.bedrock_eq, hKeepBed, hKeepMeta, hWf',
          fun φ hφ => of_decide_eq_true (hNow φ hφ), ?_⟩
        intro t ht
        have hbt := hBas t ht
        simp only [Bool.or_eq_true, List.contains_iff_mem] at hbt
        rcases hbt with hOld | hNew
        · rcases I.basis_tracked t hOld with h0 | hs
          · exact .inl h0
          · exact .inr (List.mem_append_left _ hs)
        · exact .inr (List.mem_append_right _ hNew)
      · exact I

/-! ## 4. Proof-Carrying Actions (`PcaEnvelope`) & Voluntary Testimony (`VoluntaryTestimony`) -/

/-- Runtime certificate verifier on `(state, action, certificate)`. -/
abbrev Certifier (S A C : Type) := S → A → C → Bool

/-- Proof-Carrying Action Envelope (`pca : pca_enveloped`): executes the controller's proposed
    action iff its accompanying ephemeral certificate passes `certOk`, else invokes `shield`. -/
structure PcaEnvelope (S A C : Type) where
  certOk : Certifier S A C
  shield : S → A

/-- Select the action for state `s` from a proof-carrying controller `pcc : S → A × C`. -/
@[expose] def PcaEnvelope.select {S A C : Type} (env : PcaEnvelope S A C)
    (pcc : S → A × C) (s : S) : A :=
  let (a, c) := pcc s
  if env.certOk s a c then a else env.shield s

/-- Embed any static `Policy S A` into a `PcaEnvelope S A Unit`. -/
@[expose] def PcaEnvelope.ofPolicy {S A : Type} (pol : Policy S A) (shield : S → A) :
    PcaEnvelope S A Unit :=
  ⟨fun s a _ => pol s a, shield⟩

/-- Soundness of a runtime action certifier (`pca : certifier_sound`). -/
def CertifierSound {S A C : Type} (step : S → A → S) (safe : S → Prop)
    (certOk : Certifier S A C) : Prop :=
  ∀ s a c, safe s → certOk s a c = true → safe (step s a)

/-- Relational soundness of a runtime action certifier. -/
def CertifierSoundR {S A C : Type} (stepr : PlantR S A) (safe : S → Prop)
    (certOk : Certifier S A C) : Prop :=
  ∀ s a c s', safe s → certOk s a c = true → stepr s a s' → safe s'

/-- **Proof-Carrying Action Safety (`pca_enveloped_safe`)**:
    For ANY unconstrained controller `pcc : S → A × C` emitting arbitrary `(action, certificate)`
    pairs, `env.select pcc` preserves `safe` along every trajectory (both deterministic and
    relational) whenever `init` is safe, `env.certOk` is sound, and `env.shield` is safe. -/
theorem pca_enveloped_safe {S A C : Type} {step : S → A → S} {init safe : S → Prop}
    (env : PcaEnvelope S A C)
    (hInit : InitSafe init safe)
    (hCert : CertifierSound step safe env.certOk)
    (hSh : SafeShield step safe env.shield) :
    ∀ (pcc : S → A × C), Invariant step init (env.select pcc) safe := by
  intro pcc
  apply invariant_intro hInit
  intro s hs
  unfold PcaEnvelope.select
  dsimp only
  cases hc : env.certOk s (pcc s).1 (pcc s).2 with
  | true => exact hCert s (pcc s).1 (pcc s).2 hs hc
  | false => exact hSh s hs

/-- Exact `iff` characterization: `CertifierSound` is both sufficient and necessary for
    `PcaEnvelope` to keep `safe` across all `InitSafe` starts and controllers. -/
theorem pca_certifier_sound_iff {S A C : Type} {step : S → A → S} {safe : S → Prop}
    (env : PcaEnvelope S A C) (hSh : SafeShield step safe env.shield) :
    CertifierSound step safe env.certOk ↔
      ∀ (init : S → Prop) (pcc : S → A × C),
        InitSafe init safe → Invariant step init (env.select pcc) safe := by
  constructor
  · intro hCert init pcc hInit
    exact pca_enveloped_safe env hInit hCert hSh pcc
  · intro hAll s a c hs hc
    have hInv := hAll (fun x => x = s) (fun _ => (a, c)) (fun x hx => hx ▸ hs)
    have hNext := hInv _ (.step (.init rfl))
    simpa [PcaEnvelope.select, hc] using hNext

/-- **PCA Strictly Subsumes Static Policy Shields (`pca_strictly_subsumes_static_shield`)**:
    1. **Universal Subsumption**: Every static policy `pol : Policy S A` embeds via
       `PcaEnvelope.ofPolicy pol shield` with identical step behavior and `SoundPolicy ↔ CertifierSound`.
    2. **Strict Ephemeral Per-Turn Separation**: There exists a deterministic plant (`step s a = s + a`),
       invariant `safe s := ∃ r, r * r = s`, and $O(1)$ root-witness certifier
       `certOk s a r := (r * r == s + a)` that is `CertifierSound`, where on the **exact same**
       state-action pair `(s = 4, a = 5)`:
       - presenting ephemeral witness `c = 3` unlocks `4 → 9` (`select = 5`),
       - presenting bad/missing witness `c = 0` is safely shielded (`select = 0`), and
       - the conservative identity static guard `staticPol s a := (a == 0)` refuses `(4, 5)`. -/
theorem pca_strictly_subsumes_static_shield :
    (∀ {S A : Type} (step : S → A → S) (safe : S → Prop) (pol : Policy S A) (shield ctrl : S → A),
      (SoundPolicy step safe pol ↔ CertifierSound step safe (PcaEnvelope.ofPolicy pol shield).certOk) ∧
      (∀ s, (PcaEnvelope.ofPolicy pol shield).select (fun x => (ctrl x, ())) s =
        enveloped pol shield ctrl s)) ∧
    (∃ (step : Nat → Nat → Nat) (safe : Nat → Prop) (env : PcaEnvelope Nat Nat Nat)
       (staticPol : Policy Nat Nat),
      CertifierSound step safe env.certOk ∧
      SafeShield step safe env.shield ∧
      SoundPolicy step safe staticPol ∧
      safe 4 ∧
      staticPol 4 5 = false ∧
      env.select (fun _ => (5, 3)) 4 = 5 ∧
      env.select (fun _ => (5, 0)) 4 = 0) := by
  refine ⟨?_, ?_⟩
  · intro S A step safe pol shield ctrl
    refine ⟨⟨fun h s a _ hs hp => h s a hs hp, fun h s a hs hp => h s a () hs hp⟩, fun _ => rfl⟩
  · let step : Nat → Nat → Nat := fun s a => s + a
    let safe : Nat → Prop := fun s => ∃ r, r * r = s
    let env : PcaEnvelope Nat Nat Nat :=
      { certOk := fun s a r => r * r == step s a
        shield := fun _ => 0 }
    let staticPol : Policy Nat Nat := fun _ a => a == 0
    refine ⟨step, safe, env, staticPol, ?_, ?_, ?_, ⟨2, rfl⟩, rfl, rfl, rfl⟩
    · intro s a r _ hc
      exact ⟨r, beq_iff_eq.mp hc⟩
    · intro s ⟨r, hr⟩
      exact ⟨r, by simpa [step, env] using hr⟩
    · intro s a ⟨r, hr⟩ hp
      have ha0 : a = 0 := beq_iff_eq.mp hp
      subst ha0
      exact ⟨r, by simpa [step] using hr⟩

/-! ### Voluntary Testimony Channel (`embodiment : VoluntaryTestimony`) -/

/-- Voluntary attestation / internal-activation testimony channel (`embodimentScript.sml`).
    An actor may submit `none` (withholding internal activations / remaining silent) or `some w`
    (voluntarily presenting an attested witness `w : W`). -/
structure VoluntaryTestimony (W : Type) where
  attest : W → Bool
  meaning : W → Bool

/-- Faithfulness of the attestation channel (`attestation_faithful` ↔ `sound_certifier`). -/
def VoluntaryTestimony.Faithful {W : Type} (vt : VoluntaryTestimony W) : Prop :=
  ∀ w, vt.attest w = true → vt.meaning w = true

/-- Gated policy update driven by optional voluntary testimony `optW : Option W`. -/
@[expose] def embodiedAdmit {S A W : Type} (vt : VoluntaryTestimony W)
    (oldp newp : Policy S A) : Option W → Policy S A
  | none => oldp
  | some w => cgate (vt.attest w) oldp newp

/-- Optional per-turn PCA testimony selector: if the actor withholds its certificate (`none`),
    the envelope falls back cleanly to `basePol`; if it discloses `some c` passing `certOk`,
    per-turn authority is unlocked even where `basePol` was `false`. -/
@[expose] def embodiedTurnSelect {S A C : Type} (basePol : Policy S A)
    (certOk : Certifier S A C) (shield : S → A) (actor : S → A × Option C) (s : S) : A :=
  let (a, optC) := actor s
  match optC with
  | none => if basePol s a then a else shield s
  | some c => if basePol s a || certOk s a c then a else shield s

/-- **Nondisclosure Is Inert & Safe (`nondisclosure_is_inert`)**:
    1. Withholding policy testimony (`optW = none`) or using an unattested channel (`attest = false`)
       leaves `oldp` completely unchanged and preserves `Invariant step init ... safe`.
    2. Withholding per-turn internal activations/certificates (`optC = none` in `embodiedTurnSelect`)
       behaves identically to `enveloped basePol shield` and never violates safety floors, while
       presenting a valid ephemeral certificate `some c` unlocks per-turn authority.
    3. On `ConstitutionalStack H`, varying the actor's testimony string never alters the state or judge. -/
theorem nondisclosure_is_inert :
    (∀ {S A W : Type} (vt : VoluntaryTestimony W) (oldp newp : Policy S A),
      embodiedAdmit vt oldp newp none = oldp) ∧
    (∀ {S A W : Type} (sem : W → Bool) (oldp newp : Policy S A) (optW : Option W),
      embodiedAdmit ⟨fun _ => false, sem⟩ oldp newp optW = oldp) ∧
    (∀ {S A C : Type} {step : S → A → S} {init safe : S → Prop}
       {basePol : Policy S A} {certOk : Certifier S A C} {shield : S → A},
      InitSafe init safe →
      SoundPolicy step safe basePol →
      CertifierSound step safe certOk →
      SafeShield step safe shield →
      ∀ (actor : S → A × Option C),
        Invariant step init (embodiedTurnSelect basePol certOk shield actor) safe) ∧
    (∀ {H : Habitat} {Actor : Type} (X : Exec)
       (actor₁ actor₂ : Nat → ConstitutionalStack H → Actor × ConstitutionalMove H × String),
       (∀ n st, (actor₁ n st).2.1 = (actor₂ n st).2.1) →
       ∀ (stack₀ : ConstitutionalStack H) (n : Nat),
         runConstitutional X actor₁ stack₀ n = runConstitutional X actor₂ stack₀ n) := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro S A W sem oldp newp optW
    cases optW <;> rfl
  · intro S A C step init safe basePol certOk shield hInit hBase hCert hSh actor
    apply invariant_intro hInit
    intro s hs
    unfold embodiedTurnSelect
    dsimp only
    cases (actor s).2 with
    | none =>
      cases hb : basePol s (actor s).1 with
      | true => exact hBase s (actor s).1 hs hb
      | false => exact hSh s hs
    | some c =>
      cases hb : basePol s (actor s).1 with
      | true => simp; exact hBase s (actor s).1 hs hb
      | false =>
        simp only [Bool.false_or]
        cases hc : certOk s (actor s).1 c with
        | true => exact hCert s (actor s).1 c hs hc
        | false => exact hSh s hs
  · intro H Actor X actor₁ actor₂ hSame stack₀ n
    induction n with
    | zero => rfl
    | succ m ih =>
      simp only [runConstitutional]
      rw [ih, hSame m _]

/-- Disclosing an attested witness `some w` unlocks `newp`, and `vt.Faithful` is both sufficient
    and necessary (`↔`) for `embodiedAdmit` to preserve `SoundPolicy` across all faithfully-encoded
    policy upgrades. -/
theorem voluntary_testimony_faithful_iff {S A W : Type} {step : S → A → S} {safe : S → Prop}
    (vt : VoluntaryTestimony W)
    {goodPol badPol : Policy S A}
    (hGood : SoundPolicy step safe goodPol) (hBad : ¬ SoundPolicy step safe badPol) :
    vt.Faithful ↔
      ∀ (w : W) (oldp newp : Policy S A),
        SoundPolicy step safe oldp →
        (vt.meaning w = true → SoundPolicy step safe newp) →
        SoundPolicy step safe (embodiedAdmit vt oldp newp (some w)) := by
  constructor
  · intro hFaith w oldp newp hOld hEnc
    unfold embodiedAdmit cgate
    dsimp only
    cases ha : vt.attest w with
    | false => simpa using hOld
    | true => simpa using hEnc (hFaith w ha)
  · intro hGate w ha
    cases hm : vt.meaning w with
    | true => rfl
    | false =>
      have hSoundRes := hGate w goodPol badPol hGood (fun h => by rw [hm] at h; cases h)
      simp only [embodiedAdmit, cgate, ha, ↓reduceIte] at hSoundRes
      exact absurd hSoundRes hBad

/-! ## 5. Concrete Inhabited Module Witnesses -/

def demoGateSpecA : Gate Genealogy.record :=
  { name := "specA"
    formats := ["write@1", "revert@1"]
    floors := [.home 3, .cap "a" 100, .cap "a" 50]
    methods :=
      [ ("write@1", .home 3, .eval .kernel)
      , ("write@1", .cap "a" 100, .eval .kernel)
      , ("write@1", .cap "a" 50, .eval .kernel)
      , ("revert@1", .home 3, .lemma)
      , ("revert@1", .cap "a" 100, .lemma)
      , ("revert@1", .cap "a" 50, .lemma) ]
    basis := [.kernel] }

/-- Lateral Tier-2 spec negotiation target: drops task-only `.cap "a" 50` (which `Genealogy.succeed`
    would refuse!) and adopts `.cap "b" 80`, while keeping Tier-1 `.cap "a" 100` and Tier-0 `.home 3`. -/
def demoGateSpecB : Gate Genealogy.record :=
  { name := "specB"
    formats := ["write@1", "revert@1"]
    floors := [.home 3, .cap "a" 100, .cap "b" 80]
    methods :=
      [ ("write@1", .home 3, .eval .kernel)
      , ("write@1", .cap "a" 100, .eval .kernel)
      , ("write@1", .cap "b" 80, .eval .kernel)
      , ("revert@1", .home 3, .lemma)
      , ("revert@1", .cap "a" 100, .lemma)
      , ("revert@1", .cap "b" 80, .lemma) ]
    basis := [.kernel] }

def demoRec0 : Genealogy.Rec := ⟨[("a", 0), ("b", 0)], [], [("a", 0), ("b", 0)]⟩

def demoStack0 : ConstitutionalStack Genealogy.record :=
  { bedrockFloors := [.home 3]
    metaFloors := [.home 3, .cap "a" 100]
    specGate := demoGateSpecA
    state := demoRec0
    spentLabels := [] }

example : (Genealogy.succeed demoGateSpecA demoRec0 demoGateSpecB []).isOk = false := by decide
example : checkSpecNegotiation demoStack0 demoGateSpecB [] = true := by decide
example : cwithinBool (fun (s : Nat) (a : Nat) => if a == 0 then s - 1 else s + 1)
  (fun _ => 0) (fun s => s = 0) 3 2 = true := by decide

end Obend.Judge.SvenvsCorrigibility

end
