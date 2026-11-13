module
/-
# Obend.Tactic.Compositional — smart constructors, simulation/VCG tactics & scar-free elaborator checks

Boilerplate-slashing proof engineering and metaprogramming infrastructure over `Obend.Judge`,
`Obend.Category`, and `Obend.Repair`:

1. **`Judge.ofSoundCheck`, `Judge.ofCounterexampleCheck` & `Judge.Format.ofCodec` (`Format.ofCodec`)**:
   - `Judge.deepenVerdict`: lifts any fuel-indexed checker `Nat → Obj → Cert → Judge.Verdict Clause`
     into a monotone iterative-deepening checker, discharging `mono` once and for all.
   - `Judge.ofSoundCheck` & `Judge.ofCounterexampleCheck`: build a complete lawful `Obend.Judge`
     from soundness, no-false-rejection, fragment completeness, and optional counterexample refutation
     in a single compact declaration.
   - `Codec α` & `Judge.Format.ofCodec` (aliased as `Format.ofCodec`): build a lawful byte-level
     `Obend.Judge.Format` from roundtrip codecs and a `Bool`-checked planted bad certificate, with
     automatic roundtrip acceptance (`ofCodec_checkBytes_encode`).
2. **`by compose_sim`**:
   - Goal-directed `TacticM` structural synthesizer chaining `Simulates.refl`, `Simulates.trans`,
     `Simulates.prod`, `Simulates.indepProd`, and local `Simulates` hypotheses, reducing slack
     obligations (`δ₁ + δ₂ ≤ δ`, `0 ≤ δ`) to linear arithmetic (`omega`).
3. **`by graded_vcg`**:
   - Symbolic-execution `TacticM` verification-condition generator over `GradedTriple P cmd g Q`
     decomposing `do`-notation (`>>=`), `GradedM.bind`, `pure`, `tick`, `get`, `modifyCost`,
     `actionCost`, and modular `GradedTriple` sub-specifications, discharging 5-axis
     `CompositeGrade` and numeric budgets via `omega`.
4. **`#assert_no_scar Ident in ConstName`**:
   - Kernel-expression dependency-closure auditor (`CommandElabM`) verifying that a repaired
     definition or proof over target carrier `D` contains zero transitive occurrences of retired
     carrier `C` (Plante et al. `arXiv:2610.36669v1` scar-free guarantee).
-/
public import Lean
public import Obend.Judge.Class
import all Obend.Judge.Class
public import Obend.Category.Refines
public import Obend.Category.OpenSystem
public import Obend.Category.GradedLogic
public import Obend.Repair.AlgConfig
public import Obend.Repair.CoalgConfig
public import Obend.Repair.QuotAssembly

public section
namespace Obend

set_option autoImplicit false

/-! ## 1. `Judge.ofSoundCheck` and `Format.ofCodec` Smart Constructors -/

namespace Judge.Verdict

/-- Boolean test for whether a verdict is `.refused k p`. -/
@[expose] def isRefused {Clause : Type} : Verdict Clause → Bool
  | .refused _ _ => true
  | _ => false

theorem isRefused_iff {Clause : Type} (v : Verdict Clause) :
    v.isRefused = true ↔ ∃ (k : Clause) (p : List Nat), v = .refused k p := by
  cases v with
  | ok =>
    constructor
    · intro h; cases h
    · rintro ⟨_, _, h⟩; cases h
  | uncovered =>
    constructor
    · intro h; cases h
    · rintro ⟨_, _, h⟩; cases h
  | refused k p =>
    exact ⟨fun _ => ⟨k, p, rfl⟩, fun _ => rfl⟩

/-- Convert a decided verdict to `some v` and `.uncovered` to `none` for `Judge.deepen`. -/
@[expose] def toDecided? {Clause : Type} : Verdict Clause → Option (Verdict Clause)
  | .uncovered => none
  | .ok => some .ok
  | .refused k p => some (.refused k p)

/-- Recover a `Verdict` from `Option (Verdict Clause)`. -/
@[expose] def ofOption {Clause : Type} : Option (Verdict Clause) → Verdict Clause
  | some v => v
  | none => .uncovered

theorem toDecided?_eq_some_ok {Clause : Type} {v : Verdict Clause} :
    v.toDecided? = some .ok ↔ v = .ok := by
  cases v <;> simp [toDecided?]

theorem toDecided?_eq_some_refused {Clause : Type} {v : Verdict Clause} {k : Clause} {p : List Nat} :
    v.toDecided? = some (.refused k p) ↔ v = .refused k p := by
  cases v <;> simp [toDecided?]

theorem toDecided?_ne_uncovered {Clause : Type} {v w : Verdict Clause}
    (h : v.toDecided? = some w) : w ≠ .uncovered := by
  cases v <;> simp [toDecided?] at h
  · subst h; intro hc; cases hc
  · subst h; intro hc; cases hc

end Judge.Verdict

namespace Judge

/-- Iterative-deepening wrapper turning any fuel-indexed `Verdict` procedure into a monotone one. -/
@[expose] def deepenVerdict {Obj Cert Clause : Type}
    (step : Nat → Obj → Cert → Verdict Clause) (r : Nat) (o : Obj) (c : Cert) : Verdict Clause :=
  Verdict.ofOption (deepen (fun i => (step i o c).toDecided?) r)

theorem deepen_never_uncovered {Obj Cert Clause : Type}
    (step : Nat → Obj → Cert → Verdict Clause) (r : Nat) (o : Obj) (c : Cert) :
    deepen (fun i => (step i o c).toDecided?) r ≠ some .uncovered := by
  intro h
  obtain ⟨i, _, hi⟩ := deepen_some (fun j => (step j o c).toDecided?) h
  exact Verdict.toDecided?_ne_uncovered hi rfl

theorem deepenVerdict_mono {Obj Cert Clause : Type}
    (step : Nat → Obj → Cert → Verdict Clause)
    {r r' : Nat} {o : Obj} {c : Cert}
    (hle : r ≤ r') (hdec : deepenVerdict step r o c ≠ .uncovered) :
    deepenVerdict step r' o c = deepenVerdict step r o c := by
  unfold deepenVerdict at hdec ⊢
  cases hd : deepen (fun i => (step i o c).toDecided?) r with
  | none =>
    rw [hd] at hdec
    exact False.elim (hdec rfl)
  | some v =>
    rw [deepen_mono (fun i => (step i o c).toDecided?) hd hle]

theorem deepenVerdict_eq_ok {Obj Cert Clause : Type}
    (step : Nat → Obj → Cert → Verdict Clause)
    {r : Nat} {o : Obj} {c : Cert}
    (hok : deepenVerdict step r o c = .ok) :
    ∃ i : Nat, i ≤ r ∧ step i o c = .ok := by
  unfold deepenVerdict at hok
  cases hd : deepen (fun i => (step i o c).toDecided?) r with
  | none =>
    rw [hd] at hok
    cases hok
  | some v =>
    rw [hd] at hok
    dsimp only [Verdict.ofOption] at hok
    subst hok
    obtain ⟨i, hle, hi⟩ := deepen_some (fun j => (step j o c).toDecided?) hd
    exact ⟨i, hle, (Verdict.toDecided?_eq_some_ok).1 hi⟩

theorem deepenVerdict_eq_refused {Obj Cert Clause : Type}
    (step : Nat → Obj → Cert → Verdict Clause)
    {r : Nat} {o : Obj} {c : Cert} {k : Clause} {p : List Nat}
    (href : deepenVerdict step r o c = .refused k p) :
    ∃ i : Nat, i ≤ r ∧ step i o c = .refused k p := by
  unfold deepenVerdict at href
  cases hd : deepen (fun i => (step i o c).toDecided?) r with
  | none =>
    rw [hd] at href
    cases href
  | some v =>
    rw [hd] at href
    dsimp only [Verdict.ofOption] at href
    subst href
    obtain ⟨i, hle, hi⟩ := deepen_some (fun j => (step j o c).toDecided?) hd
    exact ⟨i, hle, (Verdict.toDecided?_eq_some_refused).1 hi⟩

theorem deepenVerdict_ok_of_no_false_reject {Obj Cert Clause : Type}
    (step : Nat → Obj → Cert → Verdict Clause)
    {r : Nat} {o : Obj} {c : Cert}
    (hStepOk : step r o c = .ok)
    (hNoReject : ∀ (j : Nat) (k : Clause) (p : List Nat), step j o c ≠ .refused k p) :
    deepenVerdict step r o c = .ok := by
  have hSome : (step r o c).toDecided? = some .ok :=
    (Verdict.toDecided?_eq_some_ok).2 hStepOk
  obtain ⟨b, hb⟩ := deepen_isSome (fun j => (step j o c).toDecided?) hSome
  obtain ⟨j, _, hj⟩ := deepen_some (fun i => (step i o c).toDecided?) hb
  unfold deepenVerdict
  rw [hb]
  cases b with
  | ok => rfl
  | uncovered =>
    exact False.elim (Verdict.toDecided?_ne_uncovered hj rfl)
  | refused k p =>
    have hRef : step j o c = .refused k p := (Verdict.toDecided?_eq_some_refused).1 hj
    exact False.elim (hNoReject j k p hRef)

/-- **Smart Constructor `Judge.ofSoundCheck`.**
    Builds a lawful `Obend.Judge Obj Cert` from any fuel-indexed `step` procedure by automatically
    applying `Judge.deepenVerdict` to discharge grade monotonicity (`mono`), lifting `step_sound`,
    `step_refutes`, and `step_complete` without manual fuel-induction boilerplate. -/
@[expose, instance_reducible]
def ofSoundCheck {Obj Cert Clause : Type}
    (Meaning : Obj → Cert → Prop)
    (step : Nat → Obj → Cert → Verdict Clause)
    (step_sound : ∀ {r : Nat} {o : Obj} {c : Cert}, step r o c = .ok → Meaning o c)
    (Fragment : Obj → Prop := fun _ => False)
    (step_no_false_reject :
      ∀ {r : Nat} {o : Obj} {c : Cert} {k : Clause} {p : List Nat},
        Fragment o → Meaning o c → step r o c ≠ .refused k p := by
      intro _ _ _ _ _ hf _; cases hf)
    (step_complete :
      ∀ {o : Obj}, Fragment o → (∃ c, Meaning o c) → ∃ c r, step r o c = .ok := by
      intro _ hf _; cases hf)
    (refutes : Clause → Bool := fun _ => false)
    (step_refutes :
      ∀ {r : Nat} {o : Obj} {c : Cert} {k : Clause} {p : List Nat},
        step r o c = .refused k p → refutes k = true → ∀ c', ¬ Meaning o c' := by
      intro _ _ _ _ _ _ href; cases href) :
    Judge Obj Cert where
  Clause := Clause
  Meaning := Meaning
  check := deepenVerdict step
  sound hok := by
    obtain ⟨_, _, hi⟩ := deepenVerdict_eq_ok step hok
    exact step_sound hi
  refutes := refutes
  refuted href hk c' := by
    obtain ⟨_, _, hi⟩ := deepenVerdict_eq_refused step href
    exact step_refutes hi hk c'
  Fragment := Fragment
  complete := fun {o} hFrag ⟨cWitness, hMean⟩ => by
    obtain ⟨c, r, hrOk⟩ := step_complete hFrag ⟨cWitness, hMean⟩
    have hMeanC : Meaning o c := step_sound hrOk
    exact ⟨c, r, deepenVerdict_ok_of_no_false_reject step hrOk
      (fun _ _ _ => step_no_false_reject hFrag hMeanC)⟩
  mono hle hdec := deepenVerdict_mono step hle hdec

/-- **Counterexample-Driven Smart Constructor `Judge.ofCounterexampleCheck`.**
    Specializes `Judge.ofSoundCheck` when refuting clauses witness a semantic `Counterexample o k`
    incompatible with `Meaning o c'`, automatically discharging `mono` and `refuted`. -/
@[expose, instance_reducible]
def ofCounterexampleCheck {Obj Cert Clause : Type}
    (Meaning : Obj → Cert → Prop)
    (Counterexample : Obj → Clause → Prop)
    (step : Nat → Obj → Cert → Verdict Clause)
    (refutes : Clause → Bool)
    (step_sound : ∀ {r : Nat} {o : Obj} {c : Cert}, step r o c = .ok → Meaning o c)
    (step_counterexample :
      ∀ {r : Nat} {o : Obj} {c : Cert} {k : Clause} {p : List Nat},
        step r o c = .refused k p → refutes k = true → Counterexample o k)
    (counterexample_disjoint :
      ∀ {o : Obj} {k : Clause} {c' : Cert}, Counterexample o k → ¬ Meaning o c')
    (Fragment : Obj → Prop)
    (step_no_false_reject :
      ∀ {r : Nat} {o : Obj} {c : Cert} {k : Clause} {p : List Nat},
        Fragment o → Meaning o c → step r o c ≠ .refused k p)
    (step_complete :
      ∀ {o : Obj}, Fragment o → (∃ c, Meaning o c) → ∃ c r, step r o c = .ok) :
    Judge Obj Cert :=
  ofSoundCheck Meaning step step_sound Fragment step_no_false_reject step_complete refutes
    (fun href hk _ => counterexample_disjoint (step_counterexample href hk))

end Judge

/-- Lawful roundtrip wire codec `encode` / `decode` (`decode (encode a) = .ok a`). -/
structure Codec (α : Type) where
  encode : α → String
  decode : String → Except String α
  decode_encode : ∀ a : α, decode (encode a) = .ok a

/-- Alias `Obend.Format` for `Obend.Judge.Format` so `Format.ofCodec` resolves directly. -/
abbrev Format := Judge.Format

namespace Judge.Format

/-- **Smart Constructor `Judge.Format.ofCodec` (aliased as `Format.ofCodec`).**
    Builds a registered `Obend.Judge.Format` from roundtrip codecs for `Obj` and `Cert` plus a
    planted `bad : Obj × Cert` whose refusal `(J.check badGrade bad.1 bad.2).isRefused = true`
    can be discharged directly by `rfl` or `decide`. -/
@[expose] def ofCodec {Obj Cert : Type} [J : Judge Obj Cert]
    (name : String)
    (version : String)
    (objCodec : Codec Obj)
    (certCodec : Codec Cert)
    (bad : Obj × Cert)
    (badGrade : Nat := 0)
    (hBad : (J.check badGrade bad.1 bad.2).isRefused = true := by rfl)
    (trust : Judge.TrustBase := .kernel)
    (regime : Judge.Regime := .decidable)
    (bindsClaim : Obend.Core.Term.Term → Nat → String → Bool := fun _ _ _ => false)
    (explain : Nat → String → String → String := fun _ _ _ => "") :
    Judge.Format where
  name := name
  version := version
  Obj := Obj
  Cert := Cert
  judge := J
  decodeObj := objCodec.decode
  decodeCert := certCodec.decode
  trust := trust
  regime := regime
  bad := bad
  badGrade := badGrade
  bad_refused := (Judge.Verdict.isRefused_iff _).1 hBad
  bindsClaim := bindsClaim
  explain := explain

/-- Roundtrip byte-checking law for `Format.ofCodec`: encoded objects and certificates evaluate
    directly to `(J.check r o c).map .judge` with zero decode failure. -/
theorem ofCodec_checkBytes_encode {Obj Cert : Type} [J : Judge Obj Cert]
    (name version : String) (objCodec : Codec Obj) (certCodec : Codec Cert)
    (bad : Obj × Cert) (badGrade : Nat)
    (hBad : (J.check badGrade bad.1 bad.2).isRefused = true)
    (trust : Judge.TrustBase) (regime : Judge.Regime)
    (bindsClaim : Obend.Core.Term.Term → Nat → String → Bool)
    (explain : Nat → String → String → String)
    (r : Nat) (o : Obj) (c : Cert) :
    (ofCodec name version objCodec certCodec bad badGrade hBad trust regime bindsClaim explain).checkBytes
        r (objCodec.encode o) (certCodec.encode c) =
      (J.check r o c).map .judge := by
  unfold checkBytes ofCodec
  dsimp only
  rw [objCodec.decode_encode o, certCodec.decode_encode c]

/--Encoded acceptance under `Format.ofCodec` immediately establishes `J.Meaning o c`. -/
theorem ofCodec_encode_sound {Obj Cert : Type} [J : Judge Obj Cert]
    (name version : String) (objCodec : Codec Obj) (certCodec : Codec Cert)
    (bad : Obj × Cert) (badGrade : Nat)
    (hBad : (J.check badGrade bad.1 bad.2).isRefused = true)
    (trust : Judge.TrustBase) (regime : Judge.Regime)
    (bindsClaim : Obend.Core.Term.Term → Nat → String → Bool)
    (explain : Nat → String → String → String)
    {r : Nat} {o : Obj} {c : Cert}
    (hOk :
      (ofCodec name version objCodec certCodec bad badGrade hBad trust regime bindsClaim explain).checkBytes
        r (objCodec.encode o) (certCodec.encode c) = .ok) :
    J.Meaning o c := by
  rw [ofCodec_checkBytes_encode] at hOk
  exact J.sound (Judge.Verdict.map_eq_ok hOk)

end Judge.Format

/-- Direct `Format.ofCodec` alias so callers can write either `Format.ofCodec` or `Judge.Format.ofCodec`. -/
abbrev Format.ofCodec := @Judge.Format.ofCodec

end Obend

/-! ## 2. Supporting Lemmas for `compose_sim` and `graded_vcg` -/

namespace Obend.Tactic.Compositional

open Obend.Category

universe u v w w' u₁ u₂ v₁ v₂

/-- Interleaved product simulation with slack relaxation, complementing `Simulates.prod_of_le`. -/
theorem indepProd_of_le {S₁ T₁ : Type u₁} {S₂ T₂ : Type u₂}
    {Act₁ : Type v₁} {Act₂ : Type v₂} {V₁ V₂ : Type w} {ε : Type u}
    [GradeMonoid ε] [ObsMetric V₁ ε] [ObsMetric V₂ ε]
    {C₁ : StepSystem S₁ Act₁ V₁} {A₁ : StepSystem S₂ Act₁ V₁}
    {C₂ : StepSystem T₁ Act₂ V₂} {A₂ : StepSystem T₂ Act₂ V₂}
    {R₁ : S₁ → S₂ → Prop} {R₂ : T₁ → T₂ → Prop} {δ₁ δ₂ δ : ε}
    (h₁ : Simulates C₁ A₁ R₁ δ₁) (h₂ : Simulates C₂ A₂ R₂ δ₂) (hle : δ₁ + δ₂ ≤ δ) :
    Simulates (C₁.indepProd C₂) (A₁.indepProd A₂) (RelProd R₁ R₂) δ :=
  (h₁.indepProd h₂).weaken_err hle

@[simp] theorem gradedM_bind_eq {G : Type u} [GradeMonoid G] {σ : Type v} {α β : Type w}
    (m : GradedM G σ α) (k : α → GradedM G σ β) :
    (m >>= k) = m.bind k := rfl

@[simp] theorem gradedM_pure_eq {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    (a : α) :
    (pure a : GradedM G σ α) = GradedM.pure a := rfl

/-- Reduce any `GradedTriple P cmd g Q` to symbolic execution from an exact state `s = s₀`. -/
theorem gradedTriple_of_symExec {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    {P : σ → Prop} {cmd : GradedM G σ α} {g : G} {Q : α → σ → Prop}
    (h : ∀ s₀ : σ, P s₀ → GradedTriple (fun s => s = s₀) cmd g Q) :
    GradedTriple P cmd g Q :=
  fun s₀ hp => h s₀ hp s₀ rfl

theorem sym_reassoc_bind {G : Type u} [GradeMonoid G] {σ : Type v} {α β γ : Type w}
    {st : σ} {m : GradedM G σ α} {f : α → GradedM G σ β} {k : β → GradedM G σ γ}
    {g : G} {Q : γ → σ → Prop}
    (h : GradedTriple (fun s => s = st) (m.bind (fun a => (f a).bind k)) g Q) :
    GradedTriple (fun s => s = st) ((m.bind f).bind k) g Q := by
  rw [GradedM.bind_assoc]
  exact h

theorem sym_pure_bind {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w} {β : Type w'}
    {st : σ} {a : α} {k : α → GradedM G σ β} {g : G} {Q : β → σ → Prop}
    (hk : GradedTriple (fun s => s = st) (k a) g Q) :
    GradedTriple (fun s => s = st) ((GradedM.pure a).bind k) g Q := by
  rw [GradedM.pure_bind]
  exact hk

theorem sym_tick_bind {G : Type u} [GradeMonoid G] {σ : Type v} {β : Type w}
    {st : σ} {c g₂ g : G} {k : Unit → GradedM G σ β} {Q : β → σ → Prop}
    (hk : GradedTriple (fun s => s = st) (k ()) g₂ Q)
    (hGrade : c + g₂ ≤ g) :
    GradedTriple (fun s => s = st) ((GradedM.tick c).bind k) g Q := by
  intro s hs
  rw [hs]
  have ⟨hq, hc₂⟩ := hk st rfl
  exact ⟨hq, GradeMonoid.le_trans (GradeMonoid.add_mono (GradeMonoid.le_refl c) hc₂) hGrade⟩

theorem sym_get_bind {G : Type u} [GradeMonoid G] {σ : Type v} {β : Type w}
    {st : σ} {g : G} {k : σ → GradedM G σ β} {Q : β → σ → Prop}
    (hk : GradedTriple (fun s => s = st) (k st) g Q) :
    GradedTriple (fun s => s = st) (GradedM.get.bind k) g Q := by
  intro s hs
  rw [hs]
  have ⟨hq, hc⟩ := hk st rfl
  dsimp only [GradedM.bind, GradedM.get]
  rw [GradeMonoid.zero_add]
  exact ⟨hq, hc⟩

theorem sym_modifyCost_bind {G : Type u} [GradeMonoid G] {σ : Type v} {β : Type w}
    {st : σ} {f : σ → σ} {c g₂ g : G} {k : Unit → GradedM G σ β} {Q : β → σ → Prop}
    (hk : GradedTriple (fun s => s = f st) (k ()) g₂ Q)
    (hGrade : c + g₂ ≤ g) :
    GradedTriple (fun s => s = st) ((GradedM.modifyCost f c).bind k) g Q := by
  intro s hs
  rw [hs]
  have ⟨hq, hc₂⟩ := hk (f st) rfl
  exact ⟨hq, GradeMonoid.le_trans (GradeMonoid.add_mono (GradeMonoid.le_refl c) hc₂) hGrade⟩

theorem sym_actionCost_bind {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w} {β : Type w'}
    {st : σ} {step : σ → α × σ} {c g₂ g : G} {k : α → GradedM G σ β} {Q : β → σ → Prop}
    (hk : GradedTriple (fun s => s = (step st).2) (k (step st).1) g₂ Q)
    (hGrade : c + g₂ ≤ g) :
    GradedTriple (fun s => s = st) ((GradedM.actionCost step c).bind k) g Q := by
  intro s hs
  rw [hs]
  have ⟨hq, hc₂⟩ := hk (step st).2 rfl
  exact ⟨hq, GradeMonoid.le_trans (GradeMonoid.add_mono (GradeMonoid.le_refl c) hc₂) hGrade⟩

theorem sym_call_bind {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w} {β : Type w'}
    {st : σ} {P_sub : σ → Prop} {m : GradedM G σ α} {g₁ g₂ g : G}
    {R_sub : α → σ → Prop} {k : α → GradedM G σ β} {Q : β → σ → Prop}
    (hm : GradedTriple P_sub m g₁ R_sub)
    (hPre : P_sub st)
    (hk : ∀ (a : α) (st' : σ), R_sub a st' → GradedTriple (fun s => s = st') (k a) g₂ Q)
    (hGrade : g₁ + g₂ ≤ g) :
    GradedTriple (fun s => s = st) (m.bind k) g Q := by
  intro s hs
  rw [hs]
  have ⟨hr, hc₁⟩ := hm st hPre
  have ⟨hq, hc₂⟩ := hk (m.run st).1 (m.run st).2.1 hr (m.run st).2.1 rfl
  exact ⟨hq, GradeMonoid.le_trans (GradeMonoid.add_mono hc₁ hc₂) hGrade⟩

theorem sym_pure_tail {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    {st : σ} {a : α} {g : G} {Q : α → σ → Prop}
    (hPost : Q a st) (hGrade : (0 : G) ≤ g) :
    GradedTriple (fun s => s = st) (GradedM.pure a) g Q := by
  intro s hs
  cases hs
  exact ⟨hPost, hGrade⟩

theorem sym_tick_tail {G : Type u} [GradeMonoid G] {σ : Type v}
    {st : σ} {c g : G} {Q : Unit → σ → Prop}
    (hPost : Q () st) (hGrade : c ≤ g) :
    GradedTriple (fun s => s = st) (GradedM.tick c) g Q := by
  intro s hs
  cases hs
  exact ⟨hPost, hGrade⟩

theorem sym_get_tail {G : Type u} [GradeMonoid G] {σ : Type v}
    {st : σ} {g : G} {Q : σ → σ → Prop}
    (hPost : Q st st) (hGrade : (0 : G) ≤ g) :
    GradedTriple (fun s => s = st) GradedM.get g Q := by
  intro s hs
  cases hs
  exact ⟨hPost, hGrade⟩

theorem sym_modifyCost_tail {G : Type u} [GradeMonoid G] {σ : Type v}
    {st : σ} {f : σ → σ} {c g : G} {Q : Unit → σ → Prop}
    (hPost : Q () (f st)) (hGrade : c ≤ g) :
    GradedTriple (fun s => s = st) (GradedM.modifyCost f c) g Q := by
  intro s hs
  cases hs
  exact ⟨hPost, hGrade⟩

theorem sym_actionCost_tail {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    {st : σ} {step : σ → α × σ} {c g : G} {Q : α → σ → Prop}
    (hPost : Q (step st).1 (step st).2) (hGrade : c ≤ g) :
    GradedTriple (fun s => s = st) (GradedM.actionCost step c) g Q := by
  intro s hs
  cases hs
  exact ⟨hPost, hGrade⟩

theorem sym_call_tail {G : Type u} [GradeMonoid G] {σ : Type v} {α : Type w}
    {st : σ} {P_sub : σ → Prop} {cmd : GradedM G σ α} {g₀ g : G}
    {R_sub : α → σ → Prop} {Q : α → σ → Prop}
    (hm : GradedTriple P_sub cmd g₀ R_sub)
    (hPre : P_sub st)
    (hPost : ∀ (a : α) (st' : σ), R_sub a st' → Q a st')
    (hGrade : g₀ ≤ g) :
    GradedTriple (fun s => s = st) cmd g Q := by
  intro s hs
  rw [hs]
  have ⟨hr, hc⟩ := hm st hPre
  exact ⟨hPost (cmd.run st).1 (cmd.run st).2.1 hr, GradeMonoid.le_trans hc hGrade⟩

/-! ## 3. `by compose_sim` — Compositional Quantitative Simulation Tactic -/

open Lean Meta Elab Tactic Command

/-- Strip `Expr.mdata` wrappers recursively at the outer spine. -/
meta partial def stripOuterMData (e : Expr) : Expr :=
  match e with
  | .mdata _ inner => stripOuterMData inner
  | _ => e

/-- Extract the head constant name of an application, stripping outer `mdata` and `lam` binders. -/
meta partial def headConstName? (e : Expr) : Option Name :=
  match stripOuterMData e with
  | .lam _ _ body _ => headConstName? body
  | e' => (stripOuterMData e'.getAppFn).constName?

/-- Discharge a quantitative grade/slack inequality or postcondition obligation via `CompositeGrade`
    projection normalization, `GradeMonoid` laws, and `omega`. -/
meta def dischargeObligation (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    let rem ← evalTacticAt
      (← `(tactic| (
        try intros
        try exact GradeMonoid.le_refl _
        try simp only [
          CompositeGrade.le_iff,
          CompositeGrade.add_uses, CompositeGrade.add_errorNum,
          CompositeGrade.add_noise, CompositeGrade.add_cycles, CompositeGrade.add_exergy,
          CompositeGrade.nsmul_uses, CompositeGrade.nsmul_errorNum,
          CompositeGrade.nsmul_noise, CompositeGrade.nsmul_cycles, CompositeGrade.nsmul_exergy,
          GradeMonoid.nsmul_zero, GradeMonoid.nsmul_succ, GradeMonoid.nsmul_one,
          GradeMonoid.add_zero, GradeMonoid.zero_add,
          RatSlack.denInt,
          true_and, and_true
        ] at *
        try dsimp only [Zero.zero] at *
        try trivial
        try (constructor <;> first | trivial | omega)
        try (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | omega)
        try omega
      )))
      goal
    return rem

/-- Search local context for a hypothesis `h : Simulates C' A' R' δ₀` matching `(C, A, R)`. -/
meta def findMatchingSimHyp? (cExpr aExpr rExpr : Expr) : MetaM (Option Expr) := do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hTy := stripOuterMData (← instantiateMVars ldecl.type)
    if headConstName? hTy == some ``Obend.Category.Simulates then
      let args := hTy.getAppArgs
      if args.size >= 4 then
        let n := args.size
        let ok ← withoutModifyingState do
          let mc ← isDefEq cExpr args[n - 4]!
          let ma ← isDefEq aExpr args[n - 3]!
          let mr ← isDefEq rExpr args[n - 2]!
          pure (mc && ma && mr)
        if ok then
          let _ ← isDefEq cExpr args[n - 4]!
          let _ ← isDefEq aExpr args[n - 3]!
          let _ ← isDefEq rExpr args[n - 2]!
          return some ldecl.toExpr
  return none

/-- Keep only unassigned metavariables from a subgoal list. -/
meta def filterUnassigned (gs : List MVarId) : MetaM (List MVarId) :=
  gs.filterM fun g => return !(← g.isAssigned)

mutual
  /-- Solve all `Simulates` subgoals first (assigning intermediate systems & defect variables),
      then discharge arithmetic slack subgoals. -/
  meta partial def solveSimSubgoals (fuel : Nat) (subgoals : List MVarId) : TacticM (List MVarId) := do
    let mut simRem : List MVarId := []
    let mut otherGoals : List MVarId := []
    for sg in subgoals do
      if !(← sg.isAssigned) then
        let sgTy := stripOuterMData (← instantiateMVars (← sg.getType))
        if headConstName? sgTy == some ``Obend.Category.Simulates then
          simRem := simRem ++ (← composeSimCore fuel sg)
        else
          otherGoals := otherGoals ++ [sg]
    let mut arithRem : List MVarId := []
    for sg in otherGoals do
      if !(← sg.isAssigned) then
        arithRem := arithRem ++ (← dischargeObligation sg)
    return (← filterUnassigned (simRem ++ arithRem))

  /-- Recursive goal-directed proof builder for `Simulates C A R δ`. -/
  meta partial def composeSimCore (fuel : Nat) (goal : MVarId) : TacticM (List MVarId) :=
    goal.withContext do
      if ← goal.isAssigned then return []
      match fuel with
      | 0 => return [goal]
      | fuel' + 1 =>
        let tgt := stripOuterMData (← instantiateMVars (← goal.getType))
        let args := tgt.getAppArgs
        unless headConstName? tgt == some ``Obend.Category.Simulates && args.size >= 4 do
          return (← dischargeObligation goal)
        let n := args.size
        let cExpr := stripOuterMData args[n - 4]!
        let aExpr := stripOuterMData args[n - 3]!
        let rExpr := stripOuterMData args[n - 2]!
        let dExpr := stripOuterMData args[n - 1]!
        -- 1. Match local `Simulates` hypothesis (exact if `δ` is an mvar, otherwise via `weaken_err`).
        if let some hSim ← findMatchingSimHyp? cExpr aExpr rExpr then
          if dExpr.isMVar then
            if ← isDefEq (← goal.getType) (← inferType hSim) then
              goal.assign hSim
              return []
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``Obend.Category.Simulates.weaken_err)
          match subgoals with
          | gSim :: rest =>
            let _ ← isDefEq (← gSim.getType) (← inferType hSim)
            gSim.assign hSim
            return (← solveSimSubgoals fuel' rest)
          | _ => return subgoals
        let rHead := headConstName? rExpr
        -- 2. Reflexive simulation (`R` is `Eq` and `C = A`).
        if rHead == some ``Eq then
          let sameSys ← withoutModifyingState (isDefEq cExpr aExpr)
          if sameSys then
            if dExpr.isMVar then
              let reflThm ← mkConstWithFreshMVarLevels ``Obend.Category.Simulates.refl
              return (← filterUnassigned (← goal.apply reflThm))
            else
              let reflLeThm ← mkConstWithFreshMVarLevels ``Obend.Category.Simulates.refl_of_le
              let subgoals ← goal.apply reflLeThm
              return (← solveSimSubgoals fuel' subgoals)
        -- 3. Horizontal product (`RelProd R₁ R₂` over `StepSystem.prod` or `StepSystem.indepProd`).
        if rHead == some ``Obend.Category.RelProd then
          let isIndep :=
            headConstName? cExpr == some ``Obend.Category.StepSystem.indepProd ||
            headConstName? aExpr == some ``Obend.Category.StepSystem.indepProd
          let thmName :=
            if dExpr.isMVar then
              if isIndep then ``Obend.Category.Simulates.indepProd else ``Obend.Category.Simulates.prod
            else
              if isIndep then ``indepProd_of_le else ``Obend.Category.Simulates.prod_of_le
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels thmName)
          return (← solveSimSubgoals fuel' subgoals)
        -- 4. Vertical transitivity (`RelComp R₁ R₂`).
        if rHead == some ``Obend.Category.RelComp then
          let thmName :=
            if dExpr.isMVar then
              ``Obend.Category.Simulates.trans
            else
              ``Obend.Category.Simulates.trans_of_le
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels thmName)
          return (← solveSimSubgoals fuel' subgoals)
        return [goal]
end

/-- **`by compose_sim`**: automatically synthesizes compositional `Simulates` derivations across
    `refl`, `trans`, `prod`, `indepProd`, and local simulation hypotheses, discharging slack bounds
    via `GradeMonoid` simplification and `omega`. -/
elab "compose_sim" : tactic => do
  let goal ← getMainGoal
  let remaining ← composeSimCore 32 goal
  replaceMainGoal remaining

/-! ## 4. `by graded_vcg` — Symbolic Verification-Condition Generator for `GradedTriple` -/

/-- Normalize surface `>>=` and `pure` in a `GradedTriple` command position before structural dispatch. -/
meta def normalizeCmdHead (cmd : Expr) : MetaM Expr := do
  let cmd := stripOuterMData (← instantiateMVars cmd)
  if (stripOuterMData cmd.getAppFn).isConstOf ``Bind.bind && cmd.getAppArgs.size == 6 then
    let bArgs := cmd.getAppArgs
    return (← mkAppM ``Obend.Category.GradedM.bind #[bArgs[4]!, bArgs[5]!])
  if (stripOuterMData cmd.getAppFn).isConstOf ``Pure.pure && cmd.getAppArgs.size == 4 then
    let pArgs := cmd.getAppArgs
    return (← mkAppM ``Obend.Category.GradedM.pure #[pArgs[3]!])
  return cmd

/-- Find a local `GradedTriple P_sub m' g₀ R_sub` hypothesis whose command unifies with `mTarget`. -/
meta def findMatchingTripleHyp? (mTarget : Expr) : MetaM (Option Expr) := do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hTy := stripOuterMData (← instantiateMVars ldecl.type)
    if (stripOuterMData hTy.getAppFn).isConstOf ``Obend.Category.GradedTriple && hTy.getAppArgs.size >= 4 then
      let n := hTy.getAppArgs.size
      let mHyp := hTy.getAppArgs[n - 3]!
      let ok ← withoutModifyingState (isDefEq mTarget mHyp)
      if ok then
        let _ ← isDefEq mTarget mHyp
        return some ldecl.toExpr
  return none

/-- Symbolic-execution VCG loop on goals of shape `GradedTriple (fun s => s = st) cmd g Q`. -/
meta partial def gradedVcgSym (fuel : Nat) (goal : MVarId) : TacticM (List MVarId) :=
  goal.withContext do
    if ← goal.isAssigned then return []
    match fuel with
    | 0 => return [goal]
    | fuel' + 1 =>
      -- Normalize surface `>>=` / `pure` inside the goal first so `goal.apply` unifies cleanly.
      let normGoals ← evalTacticAt
        (← `(tactic| try simp only [gradedM_bind_eq, gradedM_pure_eq]))
        goal
      let [goal] := normGoals | return normGoals
      goal.withContext do
        let tgt := stripOuterMData (← instantiateMVars (← goal.getType))
        unless (stripOuterMData tgt.getAppFn).isConstOf ``Obend.Category.GradedTriple && tgt.getAppArgs.size >= 4 do
          return (← dischargeObligation goal)
        let tArgs := tgt.getAppArgs
        let cmd ← normalizeCmdHead tArgs[tArgs.size - 3]!
        let cmdFn := stripOuterMData cmd.getAppFn
        -- Case 1: `GradedM.bind m k`
        if cmdFn.isConstOf ``Obend.Category.GradedM.bind && cmd.getAppArgs.size >= 2 then
          let bArgs := cmd.getAppArgs
          let mExpr ← normalizeCmdHead bArgs[bArgs.size - 2]!
          let mFn := stripOuterMData mExpr.getAppFn
          -- 1a. Nested `(m₁.bind m₂).bind k` -> reassociate right
          if mFn.isConstOf ``Obend.Category.GradedM.bind then
            let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_reassoc_bind)
            let mut openGoals : List MVarId := []
            for sg in subgoals do
              if !(← sg.isAssigned) then
                openGoals := openGoals ++ (← gradedVcgSym fuel' sg)
            return (← filterUnassigned openGoals)
          -- 1b. `(GradedM.pure a).bind k`
          if mFn.isConstOf ``Obend.Category.GradedM.pure then
            let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_pure_bind)
            let mut openGoals : List MVarId := []
            for sg in subgoals do
              if !(← sg.isAssigned) then
                openGoals := openGoals ++ (← gradedVcgSym fuel' sg)
            return (← filterUnassigned openGoals)
          -- 1c. `GradedM.get.bind k`
          if mFn.isConstOf ``Obend.Category.GradedM.get then
            let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_get_bind)
            let mut openGoals : List MVarId := []
            for sg in subgoals do
              if !(← sg.isAssigned) then
                openGoals := openGoals ++ (← gradedVcgSym fuel' sg)
            return (← filterUnassigned openGoals)
          -- 1d. `(GradedM.tick c).bind k`
          if mFn.isConstOf ``Obend.Category.GradedM.tick then
            let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_tick_bind)
            match subgoals with
            | gNext :: gLe :: rest =>
              let rNext ← gradedVcgSym fuel' gNext
              let rLe ← dischargeObligation gLe
              return rNext ++ rLe ++ (← filterUnassigned rest)
            | _ => return subgoals
          -- 1e. `(GradedM.modifyCost f c).bind k`
          if mFn.isConstOf ``Obend.Category.GradedM.modifyCost then
            let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_modifyCost_bind)
            match subgoals with
            | gNext :: gLe :: rest =>
              let rNext ← gradedVcgSym fuel' gNext
              let rLe ← dischargeObligation gLe
              return rNext ++ rLe ++ (← filterUnassigned rest)
            | _ => return subgoals
          -- 1f. `(GradedM.actionCost step c).bind k`
          if mFn.isConstOf ``Obend.Category.GradedM.actionCost then
            let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_actionCost_bind)
            match subgoals with
            | gNext :: gLe :: rest =>
              let rNext ← gradedVcgSym fuel' gNext
              let rLe ← dischargeObligation gLe
              return rNext ++ rLe ++ (← filterUnassigned rest)
            | _ => return subgoals
          -- 1g. Sub-specification hypothesis `hm : GradedTriple P_sub m g₁ R_sub`
          if let some hm ← findMatchingTripleHyp? mExpr then
            let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_call_bind)
            match subgoals with
            | gHm :: gPre :: gCont :: gLe :: rest =>
              let _ ← isDefEq (← gHm.getType) (← inferType hm)
              gHm.assign hm
              let rPre ← dischargeObligation gPre
              let (_, gContBody) ← gCont.introNP 3
              let rCont ← gradedVcgSym fuel' gContBody
              let rLe ← dischargeObligation gLe
              return rPre ++ rCont ++ rLe ++ (← filterUnassigned rest)
            | _ => return subgoals
          return [goal]
        -- Case 2: Tail commands (not `bind`)
        if cmdFn.isConstOf ``Obend.Category.GradedM.pure then
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_pure_tail)
          let mut openGoals : List MVarId := []
          for sg in subgoals do
            if !(← sg.isAssigned) then
              openGoals := openGoals ++ (← dischargeObligation sg)
          return (← filterUnassigned openGoals)
        if cmdFn.isConstOf ``Obend.Category.GradedM.tick then
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_tick_tail)
          let mut openGoals : List MVarId := []
          for sg in subgoals do
            if !(← sg.isAssigned) then
              openGoals := openGoals ++ (← dischargeObligation sg)
          return (← filterUnassigned openGoals)
        if cmdFn.isConstOf ``Obend.Category.GradedM.get then
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_get_tail)
          let mut openGoals : List MVarId := []
          for sg in subgoals do
            if !(← sg.isAssigned) then
              openGoals := openGoals ++ (← dischargeObligation sg)
          return (← filterUnassigned openGoals)
        if cmdFn.isConstOf ``Obend.Category.GradedM.modifyCost then
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_modifyCost_tail)
          let mut openGoals : List MVarId := []
          for sg in subgoals do
            if !(← sg.isAssigned) then
              openGoals := openGoals ++ (← dischargeObligation sg)
          return (← filterUnassigned openGoals)
        if cmdFn.isConstOf ``Obend.Category.GradedM.actionCost then
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_actionCost_tail)
          let mut openGoals : List MVarId := []
          for sg in subgoals do
            if !(← sg.isAssigned) then
              openGoals := openGoals ++ (← dischargeObligation sg)
          return (← filterUnassigned openGoals)
        if let some hm ← findMatchingTripleHyp? cmd then
          let subgoals ← goal.apply (← mkConstWithFreshMVarLevels ``sym_call_tail)
          match subgoals with
          | gHm :: gPre :: gPost :: gLe :: rest =>
            let _ ← isDefEq (← gHm.getType) (← inferType hm)
            gHm.assign hm
            let rPre ← dischargeObligation gPre
            let rPost ← dischargeObligation gPost
            let rLe ← dischargeObligation gLe
            return rPre ++ rPost ++ rLe ++ (← filterUnassigned rest)
          | _ => return subgoals
        return [goal]

/-- **`by graded_vcg`**: symbolic-execution VCG tactic discharging sequential `GradedTriple`
    `bind_triple` + `conseq_triple` chains and grade-monoid arithmetic obligations via `omega`. -/
elab "graded_vcg" : tactic => do
  let goal ← getMainGoal
  let symGoals ← goal.apply (← mkConstWithFreshMVarLevels ``gradedTriple_of_symExec)
  let mut remaining : List MVarId := []
  for sg in symGoals do
    let (_, sgBody) ← sg.introNP 2
    remaining := remaining ++ (← gradedVcgSym 64 sgBody)
  replaceMainGoal remaining

/-! ## 5. `#assert_no_scar` — Elaborator Audit for Scar-Free Proof Repair -/

/-- `n` was declared in a module strictly before `scarName`'s module (topological import order),
    so `n` cannot transitively reference `scarName`. -/
private meta def declaredStrictlyBefore (env : Environment) (n scarName : Name) : Bool :=
  match env.getModuleIdxFor? n, env.getModuleIdxFor? scarName with
  | some ni, some si => ni.toNat < si.toNat
  | some _, none => true
  | _, _ => false

/-- Direct constant dependencies of `info` across both its elaborated type and kernel body. -/
private meta def directConstDeps (info : ConstantInfo) : NameSet := Id.run do
  let mut ds := info.type.getUsedConstantsAsSet
  if let some val := info.value? (allowOpaque := true) then
    ds := ds ++ val.getUsedConstantsAsSet
  match info with
  | .inductInfo v => ds := ds ++ .ofList v.all
  | .ctorInfo v => ds := ds.insert v.induct
  | .recInfo v => ds := ds ++ .ofList v.all
  | _ => ()
  return ds

/-- Breadth-first search over the kernel constant closure of `targetName` (in `env.setExporting false`)
    returning `some [targetName, ..., scarName]` if `scarName` occurs anywhere in `targetName` or
    its unfolded transitive dependencies, and `none` when `targetName` is completely scar-free. -/
meta def findScarPath? (env : Environment) (scarName targetName : Name) :
    CoreM (Option (List Name)) := do
  let fullEnv := env.setExporting false
  if scarName == targetName then
    return some [targetName]
  let mut queue : Array (Name × List Name) := #[(targetName, [targetName])]
  let mut head : Nat := 0
  let mut visited : NameSet := ({} : NameSet).insert targetName
  while h : head < queue.size do
    let (curr, revPath) := queue[head]
    head := head + 1
    if declaredStrictlyBefore fullEnv curr scarName then
      continue
    let some info := fullEnv.find? curr
      | throwError "#assert_no_scar: missing constant '{curr}' in environment"
    if let .axiomInfo _ := info then
      if getOriginalConstKind? fullEnv curr != some .axiom then
        throwError "#assert_no_scar: body of '{curr}' is hidden behind module boundary; use `import all` or `@[expose]`"
    let deps := directConstDeps info
    if deps.contains scarName then
      return some (revPath.reverse ++ [scarName])
    for d in deps.toList do
      if !visited.contains d then
        visited := visited.insert d
        queue := queue.push (d, d :: revPath)
  return none

/-- **`#assert_no_scar RetiredType in RepairedDecl`**:
    Fails compilation if `RetiredType` appears anywhere in the kernel type or transitive unfolded
    body of `RepairedDecl`, mechanizing Plante et al.'s scar-free proof repair guarantee. -/
elab "#assert_no_scar " scar:ident " in " target:ident : command => do
  let scarName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo scar
  let targetName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  let env ← getEnv
  match ← liftCoreM <| findScarPath? env scarName targetName with
  | some chain =>
    let rendered := String.intercalate " → " (chain.map Name.toString)
    throwError "#assert_no_scar failed: retired declaration '{scarName}' still appears in '{targetName}' via:\n  {rendered}"
  | none =>
    logInfo m!"#assert_no_scar: '{targetName}' is scar-free of '{scarName}'"

end Obend.Tactic.Compositional
end
