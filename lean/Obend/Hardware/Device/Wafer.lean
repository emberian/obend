module
/-
# Obend.Hardware.Device.Wafer — a 1D wafer and the process operators that move it

The wafer is the state a fabrication recipe acts on: a film stack above the silicon, the net doping
of the substrate, and the dopant that has been put into it, in depth `x` (cm) from the current silicon
surface. Each process step is an operator on that state, with its physical parameters as arguments.

**The profile representation.** Every implant is a Gaussian in depth, `N(x) = Q/√(2πσ²) ·
[e^{−(x−R_p)²/2σ²} + e^{−(x+R_p)²/2σ²}]`, the second term the image that makes the surface a
zero-flux (reflecting) boundary. The representation is chosen because Fick's law with a constant
diffusivity maps it to itself exactly: after a time `t` at diffusivity `D`, `σ² ↦ σ² + 2Dt` with `Q` and
`R_p` unchanged (Plummer eq. 7-?, 8-?: the Gaussian is the Green's function of the diffusion equation and
the image term is preserved by the symmetry). So the anneal operator is exact on the state and carries
no discretisation; the *only* discretisation in the chain is the mesh the device solver samples the
profile on, and that sampling is checked, not assumed (`dopingEnclosure`: an interval the sampled value
must lie in). What the representation cannot express, and this module says so: the skewed (Pearson IV)
as-implanted shape of boron, concentration-dependent diffusion of the `10²⁰ cm⁻³` layers,
dopant segregation into a growing oxide, and loss of the dose that stops in a screen film (the image
folds it back instead; for a screen film thinner than `R_p − 2ΔR_p` this is under 3 % of the dose).

**Where numbers enter.** `R_p`, `ΔR_p` from `rangeTable` (Plummer ch. 8) by energy; `D` per species as a
value the producer supplies and the operator checks against `D₀ exp(−E_A/kT)` (`Arrhenius.ok`,
Plummer Table 7-5); Deal–Grove `B`, `B/A` the same way (Plummer Table 6-?), and the new oxide
thickness as a value checked against `x² + Ax = B(t + τ)` to a stated residual (`oxidize`), with
`dealGrove_root_pinned` saying how far two such values can be apart. The exponential and the square
root never appear as functions: only their enclosures (`Device/Enclosure.lean`).

**The theorems.** `anneal_var_mono` (a positive `D` and `t` widen every profile), `anneal_dose`
(diffusion conserves dose), `dealGrove_limits` (the oxide obeys both the parabolic and the linear
bound), `dealGrove_root_pinned` (the thickness is determined by the residual to `2ε/A`),
`oxidize_consumes` (silicon consumed is `0.44` of the oxide grown), `etch_deposit` (etching what was
deposited restores the stack), `sqrtEnclosure_spec` (the root enclosure brackets its argument). Each
has the process parameters free and false for some value of them.
-/
public import Obend.Hardware.Device.Constants
public section

namespace Obend.Hardware.Device
open Obend.Analysis
set_option autoImplicit false

/-! ## 1. The state -/

/-- Films above the silicon. -/
inductive FilmMaterial where
  | oxide
  | nitride
  | polysilicon
  | metal
  deriving @[expose] DecidableEq, Repr

/-- A film: material and thickness (cm). -/
structure Film where
  material : FilmMaterial
  thicknessCm : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- A Gaussian dopant distribution: dose `Q` (cm⁻²), projected range `R_p` (cm, from the current
silicon surface; negative after the surface has been consumed past it) and variance `σ²` (cm²). -/
structure GaussianDopant where
  species : Species
  doseCm2 : CanonicalRat
  rpCm : CanonicalRat
  varCm2 : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- The wafer: substrate net doping (cm⁻³, donors positive), the film stack (top first), the
dopants, and the silicon consumed so far (cm; bookkeeping of where the original surface was). -/
structure WaferState where
  background : CanonicalRat
  films : List Film
  dopants : List GaussianDopant
  siliconRemovedCm : CanonicalRat
  deriving @[expose] DecidableEq, Repr

/-- A bare substrate. -/
@[expose] def WaferState.bare (background : CanonicalRat) : WaferState :=
  ⟨background, [], [], 0⟩

@[expose] def filmsThickness (films : List Film) : CanonicalRat :=
  films.foldl (fun acc f => acc + f.thicknessCm) 0

/-- The thickness of the oxide on top, `0` if the top film is not oxide (or there is none). -/
@[expose] def WaferState.topOxide (w : WaferState) : CanonicalRat :=
  match w.films with
  | ⟨.oxide, t⟩ :: _ => t
  | _ => 0

/-- Oxidation proceeds only through bare silicon or an existing oxide. -/
@[expose] def WaferState.oxidizable (w : WaferState) : Bool :=
  match w.films with
  | [] => true
  | ⟨.oxide, _⟩ :: _ => true
  | _ => false

/-- Total dose of a species in the wafer (cm⁻²). -/
@[expose] def WaferState.dose (w : WaferState) (sp : Species) : CanonicalRat :=
  w.dopants.foldl (fun acc g => if g.species = sp then acc + g.doseCm2 else acc) 0

/-! ## 2. Implant -/

/-- Implant `sp` at `keV` with dose `Q`: a Gaussian at `R_p − t_films` with variance `ΔR_p²` (the films
are taken to stop like silicon; `none` outside the table's energies). -/
@[expose] def WaferState.implant (w : WaferState) (sp : Species) (keV dose : CanonicalRat) : Option WaferState :=
  match rangeAt sp keV with
  | none => none
  | some (rp, drp) =>
    some { w with dopants := ⟨sp, dose, rp - filmsThickness w.films, drp * drp⟩ :: w.dopants }

/-- The dose fold is additive in its accumulator. -/
theorem dose_foldl_acc (sp : Species) (l : List GaussianDopant) (acc : CanonicalRat) :
    l.foldl (fun acc g => if g.species = sp then acc + g.doseCm2 else acc) acc
      = acc + l.foldl (fun acc g => if g.species = sp then acc + g.doseCm2 else acc) 0 := by
  induction l generalizing acc with
  | nil => simp only [List.foldl]; grind
  | cons g l ih =>
    simp only [List.foldl]
    rw [ih, ih (if g.species = sp then 0 + g.doseCm2 else 0)]
    split <;> grind

theorem implant_dose {w w' : WaferState} {sp : Species} {keV dose : CanonicalRat}
    (h : w.implant sp keV dose = some w') : w'.dose sp = w.dose sp + dose := by
  unfold WaferState.implant at h
  split at h
  · cases h
  · cases h
    simp only [WaferState.dose, List.foldl]
    rw [dose_foldl_acc]
    simp
    grind

/-! ## 3. Anneal -/

/-- Diffusivities (cm²/s) at a step's temperature, one per species, supplied by the producer. -/
structure Diffusivities where
  boron : CanonicalRat
  phosphorus : CanonicalRat
  arsenic : CanonicalRat
  antimony : CanonicalRat
  deriving @[expose] DecidableEq, Repr

@[expose] def Diffusivities.get (d : Diffusivities) : Species → CanonicalRat
  | .boron => d.boron
  | .phosphorus => d.phosphorus
  | .arsenic => d.arsenic
  | .antimony => d.antimony

/-- Each supplied diffusivity lies in `D₀ exp(−E_A/kT)` of its species (`intrinsicDiffusivity`). -/
@[expose] def Diffusivities.ok (d : Diffusivities) (kBEv tempK : CanonicalRat) : Bool :=
  (intrinsicDiffusivity .boron).ok kBEv tempK d.boron &&
  (intrinsicDiffusivity .phosphorus).ok kBEv tempK d.phosphorus &&
  (intrinsicDiffusivity .arsenic).ok kBEv tempK d.arsenic &&
  (intrinsicDiffusivity .antimony).ok kBEv tempK d.antimony

/-- Fick's law for time `t` at diffusivities `d`: `σ² ↦ σ² + 2Dt`, exact. -/
@[expose] def WaferState.anneal (w : WaferState) (d : Diffusivities) (timeS : CanonicalRat) : WaferState :=
  { w with dopants := w.dopants.map fun g => { g with varCm2 := g.varCm2 + 2 * d.get g.species * timeS } }

/-- A positive diffusivity for a positive time widens every profile. -/
theorem anneal_var_mono (w : WaferState) (d : Diffusivities) {timeS : CanonicalRat} (ht : 0 < timeS)
    (hd : ∀ sp, 0 < d.get sp) :
    ∀ g ∈ (w.anneal d timeS).dopants, ∃ g₀ ∈ w.dopants, g₀.varCm2 < g.varCm2 := by
  intro g hg
  simp only [WaferState.anneal, List.mem_map] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  refine ⟨g₀, hg₀, ?_⟩
  have := Rat.mul_pos (Rat.mul_pos (show (0 : CanonicalRat) < 2 by decide) (hd g₀.species)) ht
  simp only
  grind

/-- Diffusion conserves dose. -/
theorem anneal_dose (w : WaferState) (d : Diffusivities) (timeS : CanonicalRat) (sp : Species) :
    (w.anneal d timeS).dose sp = w.dose sp := by
  simp [WaferState.dose, WaferState.anneal, List.foldl_map]

/-! ## 4. Oxidation -/

/-- The producer's data for an oxidation step: `B` (cm²/s), `B/A` (cm/s), the new oxide thickness
(cm), and the diffusivities of the species during the step. -/
structure OxidationCert where
  bCm2PerS : CanonicalRat
  baCmPerS : CanonicalRat
  xNewCm : CanonicalRat
  diff : Diffusivities
  deriving @[expose] DecidableEq, Repr

/-- `x² + Ax − B(t + τ)`. -/
@[expose] def dealGroveResidual (A target x : CanonicalRat) : CanonicalRat :=
  x * x + A * x - target

/-- Deal–Grove: with `A = B/(B/A)` and `τ = (x₀² + Ax₀)/B` from the oxide already present, the new
thickness `x` is accepted when `x ≥ x₀` and `|x² + Ax − B(t+τ)| ≤ tol · B(t+τ)`. The step also
anneals (it is a thermal step), consumes `0.44` of the grown oxide from the silicon and shifts every
profile up by that much (segregation of dopant into the oxide is not modelled). `none` when the rate
constants are not Arrhenius-consistent, the surface is masked, or the thickness does not solve the
equation. -/
@[expose] def WaferState.oxidize (w : WaferState) (amb : OxidationAmbient) (kBEv tempK timeS : CanonicalRat)
    (c : OxidationCert) (tol : CanonicalRat) : Option WaferState :=
  let rates := dealGrove100 amb
  if !(rates.parabolic.ok kBEv tempK c.bCm2PerS && rates.linear.ok kBEv tempK c.baCmPerS &&
        c.diff.ok kBEv tempK && w.oxidizable) then none
  else
    let x0 := w.topOxide
    let A := c.bCm2PerS / c.baCmPerS
    let tau := (x0 * x0 + A * x0) / c.bCm2PerS
    let target := c.bCm2PerS * (timeS + tau)
    if 0 < c.bCm2PerS ∧ 0 < c.baCmPerS ∧ 0 ≤ timeS ∧ x0 ≤ c.xNewCm ∧
        ratAbs (dealGroveResidual A target c.xNewCm) ≤ tol * target then
      let grown := c.xNewCm - x0
      let consumed := siliconPerOxide * grown
      let annealed := w.anneal c.diff timeS
      let films := match w.films with
        | ⟨.oxide, _⟩ :: rest => ⟨.oxide, c.xNewCm⟩ :: rest
        | fs => ⟨.oxide, c.xNewCm⟩ :: fs
      some { annealed with
        films := films
        dopants := annealed.dopants.map fun g => { g with rpCm := g.rpCm - consumed }
        siliconRemovedCm := w.siliconRemovedCm + consumed }
    else none

/-- **Both Deal–Grove limits**: a nonnegative thickness within `ε` of the equation obeys the parabolic
bound `x² ≤ B(t+τ) + ε` and the linear bound `A x ≤ B(t+τ) + ε`. -/
theorem dealGrove_limits {A target x ε : CanonicalRat} (hx : 0 ≤ x) (hA : 0 ≤ A)
    (hres : ratAbs (dealGroveResidual A target x) ≤ ε) :
    x * x ≤ target + ε ∧ A * x ≤ target + ε := by
  unfold dealGroveResidual ratAbs at hres
  have hxx : 0 ≤ x * x := Rat.mul_nonneg hx hx
  have hAx : 0 ≤ A * x := Rat.mul_nonneg hA hx
  split at hres <;> grind

/-- **The thickness is pinned by the residual**: two nonnegative thicknesses each within `ε` of the
equation satisfy `(x − x')(x + x' + A) ∈ [−2ε, 2ε]`, hence `A·|x − x'| ≤ 2ε`. -/
theorem dealGrove_root_pinned {A target x x' ε : CanonicalRat} (hx : 0 ≤ x) (hx' : 0 ≤ x') (hA : 0 ≤ A)
    (h : ratAbs (dealGroveResidual A target x) ≤ ε) (h' : ratAbs (dealGroveResidual A target x') ≤ ε) :
    A * (x - x') ≤ 2 * ε ∧ A * (x' - x) ≤ 2 * ε := by
  unfold dealGroveResidual ratAbs at h h'
  have hprod : (x - x') * (x + x' + A) = (x * x + A * x - target) - (x' * x' + A * x' - target) := by grind
  have hsum : 0 ≤ x + x' := by grind
  constructor
  · rcases @Rat.le_total x' x with hle | hle
    · have h1 : (x - x') * A ≤ (x - x') * (x + x' + A) :=
        Rat.mul_le_mul_of_nonneg_left (by grind) (by grind)
      split at h <;> split at h' <;> grind
    · have : A * (x - x') ≤ 0 := by
        have := Rat.mul_le_mul_of_nonneg_left (show x - x' ≤ 0 by grind) hA
        grind
      have hε : 0 ≤ ε := by split at h <;> grind
      grind
  · rcases @Rat.le_total x x' with hle | hle
    · have h1 : (x' - x) * A ≤ (x' - x) * (x + x' + A) :=
        Rat.mul_le_mul_of_nonneg_left (by grind) (by grind)
      split at h <;> split at h' <;> grind
    · have : A * (x' - x) ≤ 0 := by
        have := Rat.mul_le_mul_of_nonneg_left (show x' - x ≤ 0 by grind) hA
        grind
      have hε : 0 ≤ ε := by split at h <;> grind
      grind

/-- The silicon consumed by an oxidation is `0.44` of the oxide grown. -/
theorem oxidize_consumes {w w' : WaferState} {amb : OxidationAmbient} {kBEv tempK timeS tol : CanonicalRat}
    {c : OxidationCert} (h : w.oxidize amb kBEv tempK timeS c tol = some w') :
    w'.siliconRemovedCm = w.siliconRemovedCm + siliconPerOxide * (c.xNewCm - w.topOxide) := by
  unfold WaferState.oxidize at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

/-! ## 5. Etch and deposition -/

/-- Deposit a film of `m`, thickness `t` (merged with a top film of the same material). -/
@[expose] def WaferState.deposit (w : WaferState) (m : FilmMaterial) (t : CanonicalRat) : WaferState :=
  match w.films with
  | ⟨m', t'⟩ :: rest => if m' = m then { w with films := ⟨m, t' + t⟩ :: rest } else { w with films := ⟨m, t⟩ :: w.films }
  | [] => { w with films := [⟨m, t⟩] }

/-- Etch `depth` of the top film, which must be `m` and at least that thick; a film etched to zero is
removed. -/
@[expose] def WaferState.etch (w : WaferState) (m : FilmMaterial) (depth : CanonicalRat) : Option WaferState :=
  match w.films with
  | ⟨m', t⟩ :: rest =>
    if m' = m ∧ depth ≤ t then
      some { w with films := if t - depth = 0 then rest else ⟨m, t - depth⟩ :: rest }
    else none
  | [] => none

/-- Strip the top film entirely; it must be `m`. -/
@[expose] def WaferState.strip (w : WaferState) (m : FilmMaterial) : Option WaferState :=
  match w.films with
  | ⟨m', _⟩ :: rest => if m' = m then some { w with films := rest } else none
  | [] => none

/-- Etch `depth` of bare silicon: every profile moves up by `depth`. -/
@[expose] def WaferState.etchSilicon (w : WaferState) (depth : CanonicalRat) : Option WaferState :=
  match w.films with
  | [] => some { w with dopants := w.dopants.map fun g => { g with rpCm := g.rpCm - depth },
                        siliconRemovedCm := w.siliconRemovedCm + depth }
  | _ => none

/-- Etching what was just deposited restores the stack, whatever is under it, for any `t ≥ 0`
(when the top film has positive thickness). -/
theorem etch_deposit (w : WaferState) (m : FilmMaterial) {t : CanonicalRat} (_ht : 0 ≤ t)
    (hpos : ∀ f ∈ w.films, 0 < f.thicknessCm) :
    (w.deposit m t).etch m t = some w := by
  obtain ⟨bg, films, dops, rem⟩ := w
  unfold WaferState.deposit WaferState.etch
  cases films with
  | nil =>
    simp; grind
  | cons f rest =>
    obtain ⟨m', t'⟩ := f
    have ht' : 0 < t' := hpos ⟨m', t'⟩ (List.mem_cons_self ..)
    by_cases hm : m' = m
    · subst hm
      have h1 : t ≤ t' + t := by grind
      have h2 : ¬ (t' + t - t = 0) := by grind
      simp [h1, h2]; grind
    · simp [hm]; grind

/-! ## 6. The sampled profile: an interval the mesh doping must lie in -/

/-- A root enclosure: `lo² ≤ v ≤ hi²`, `0 ≤ lo`, by Newton from above (`hi₀ = max 1 v`), rounding
`hi` up to `roundScale` each step and taking `lo = v/hi`. -/
@[expose] def sqrtEnclosure (v : CanonicalRat) (iters : Nat := 48) : Interval :=
  let s : CanonicalRat := (roundScale : Nat)
  let hi := go (max 1 v) iters s
  ⟨v / hi, hi⟩
where
  go (hi : CanonicalRat) : Nat → CanonicalRat → CanonicalRat
    | 0, _ => hi
    | k + 1, s =>
      let h' := (hi + v / hi) / 2
      go ((((h' * s).ceil : Int) : CanonicalRat) / s) k s

private theorem rat_sq_nonneg (x : CanonicalRat) : 0 ≤ x * x := by
  rcases @Rat.le_total 0 x with hx | hx
  · exact Rat.mul_nonneg hx hx
  · have hnx : 0 ≤ -x := by grind
    have hmul := Rat.mul_nonneg hnx hnx
    grind

private theorem sqrtEnclosure_go_spec {v hi s : CanonicalRat} (hv : 0 ≤ v) (hs : 0 < s)
    (hpos : 0 < hi) (hhi : v ≤ hi * hi) :
    ∀ k, 0 < sqrtEnclosure.go v hi k s ∧ v ≤ sqrtEnclosure.go v hi k s * sqrtEnclosure.go v hi k s
  | 0 => ⟨hpos, hhi⟩
  | k + 1 => by
    simp only [sqrtEnclosure.go]
    let q := v / hi
    let h' := (hi + q) / 2
    let hi₁ := (((h' * s).ceil : Int) : CanonicalRat) / s
    have hinv : 0 ≤ hi⁻¹ := Rat.le_of_lt (Rat.inv_pos.2 hpos)
    have hq_nonneg : 0 ≤ q := by rw [show q = v * hi⁻¹ from Rat.div_def v hi]; exact Rat.mul_nonneg hv hinv
    have hh'_pos : 0 < h' := by
      rw [show h' = (hi + q) * (2 : CanonicalRat)⁻¹ from Rat.div_def (hi + q) 2]
      exact Rat.mul_pos (by grind) (Rat.inv_pos.2 (by decide))
    have hhi_q : hi * q = v := by
      rw [show q = v * hi⁻¹ from Rat.div_def v hi, Rat.mul_comm v hi⁻¹, ← Rat.mul_assoc,
          Rat.mul_inv_cancel hi (Rat.ne_of_gt hpos), Rat.one_mul]
    have h2h' : 2 * h' = hi + q := by
      rw [show h' = (hi + q) * (2 : CanonicalRat)⁻¹ from Rat.div_def (hi + q) 2]
      grind
    have hdiff_sq : 0 ≤ (hi - q) * (hi - q) := rat_sq_nonneg (hi - q)
    have hamgm : v ≤ h' * h' := by
      have hid : (2 * h') * (2 * h') = (hi - q) * (hi - q) + 4 * (hi * q) := by
        rw [h2h']
        grind
      rw [hhi_q] at hid
      grind
    have hle₁ : h' ≤ hi₁ := Interval.le_div_of_mul_le hs Rat.le_ceil
    have hpos₁ : 0 < hi₁ := by grind
    have hsq₁ : h' * h' ≤ hi₁ * hi₁ := by
      have hh'_nn : 0 ≤ h' := Rat.le_of_lt hh'_pos
      have h1 : h' * h' ≤ h' * hi₁ := Rat.mul_le_mul_of_nonneg_left hle₁ hh'_nn
      have h2 : h' * hi₁ ≤ hi₁ * hi₁ := Rat.mul_le_mul_of_nonneg_right hle₁ (Rat.le_of_lt hpos₁)
      exact Rat.le_trans h1 h2
    exact sqrtEnclosure_go_spec hv hs hpos₁ (Rat.le_trans hamgm hsq₁) k

/-- **The root enclosure brackets its argument (`sqrtEnclosure_spec`)**: for every `v ≥ 0` and
iteration count `iters`, `0 ≤ lo`, `0 < hi`, `lo² ≤ v ≤ hi²`, and any non-negative square root `r`
with `v ∈ [r², r²]` (or `lo_v ≤ r² ≤ hi_v`) lies inside `[lo, hi]`. -/
theorem sqrtEnclosure_spec {v : CanonicalRat} (hv : 0 ≤ v) (iters : Nat := 48) :
    0 ≤ (sqrtEnclosure v iters).lo ∧
    0 < (sqrtEnclosure v iters).hi ∧
    (sqrtEnclosure v iters).lo * (sqrtEnclosure v iters).lo ≤ v ∧
    v ≤ (sqrtEnclosure v iters).hi * (sqrtEnclosure v iters).hi ∧
    (∀ r : CanonicalRat, 0 ≤ r → r * r = v → r ∈ sqrtEnclosure v iters) := by
  unfold sqrtEnclosure
  have hs_nat : (0 : CanonicalRat) < (roundScale : Nat) := by exact_mod_cast roundScale_pos
  let s : CanonicalRat := (roundScale : Nat)
  have hs : 0 < s := hs_nat
  have h0_pos : 0 < max (1 : CanonicalRat) v := by
    rw [Rat.max_def]; split <;> grind
  have h0_sq : v ≤ max (1 : CanonicalRat) v * max (1 : CanonicalRat) v := by
    rw [Rat.max_def]
    split
    · rename_i hge1
      have hmul : 1 * v ≤ v * v := Rat.mul_le_mul_of_nonneg_right hge1 hv
      rwa [Rat.one_mul] at hmul
    · grind
  obtain ⟨hhi_pos, hhi_sq⟩ := sqrtEnclosure_go_spec hv hs h0_pos h0_sq iters
  let hi := sqrtEnclosure.go v (max 1 v) iters s
  have hlo_nn : 0 ≤ v / hi := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hv (Rat.le_of_lt (Rat.inv_pos.2 hhi_pos))
  have hlo_le_hi : v / hi ≤ hi := Interval.div_le_of_le_mul hhi_pos hhi_sq
  have hlo_hi : (v / hi) * hi = v := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel hi (Rat.ne_of_gt hhi_pos), Rat.mul_one]
  have hlo_sq : (v / hi) * (v / hi) ≤ v := by
    have h1 : (v / hi) * (v / hi) ≤ (v / hi) * hi :=
      Rat.mul_le_mul_of_nonneg_left hlo_le_hi hlo_nn
    rw [hlo_hi] at h1
    exact h1
  refine ⟨hlo_nn, hhi_pos, hlo_sq, hhi_sq, ?_⟩
  intro r hr hrv
  rw [Interval.mem_iff]
  dsimp only
  constructor
  · apply le_of_ratPow_le hr (k := 1)
    simpa [ratPow, hrv] using hlo_sq
  · apply le_of_ratPow_le (Rat.le_of_lt hhi_pos) (k := 1)
    simpa [ratPow, hrv] using hhi_sq

/-- Interval-monotone root bracket: if `0 ≤ a`, `0 ≤ r`, and `a ≤ r² ≤ b`, then `r` lies in
`[(sqrtEnclosure a iters).lo, (sqrtEnclosure b iters).hi]`. -/
theorem sqrtEnclosure_bracket_mem {a b r : CanonicalRat} (ha : 0 ≤ a) (hr : 0 ≤ r)
    (har : a ≤ r * r) (hrb : r * r ≤ b) (iters : Nat := 48) :
    r ∈ (⟨(sqrtEnclosure a iters).lo, (sqrtEnclosure b iters).hi⟩ : Interval) := by
  have hb : 0 ≤ b := Rat.le_trans ha (Rat.le_trans har hrb)
  obtain ⟨_, _, hlo_a, _, _⟩ := sqrtEnclosure_spec ha iters
  obtain ⟨_, hhi_b_pos, _, hhi_b, _⟩ := sqrtEnclosure_spec hb iters
  rw [Interval.mem_iff]
  dsimp only
  constructor
  · apply le_of_ratPow_le hr (k := 1)
    simpa [ratPow] using Rat.le_trans hlo_a har
  · apply le_of_ratPow_le (Rat.le_of_lt hhi_b_pos) (k := 1)
    simpa [ratPow] using Rat.le_trans hrb hhi_b

/-- `[π]` to 15 digits. -/
@[expose] def piInterval : Interval := ⟨3.14159265358979, 3.14159265358980⟩

/-- `1/√(2πσ²)` as an interval; `none` for `σ² ≤ 0`. -/
@[expose] def invSqrt2PiVar? (var : CanonicalRat) : Option Interval :=
  let twoPiVar := Interval.scale (2 * var) piInterval
  if 0 < twoPiVar.lo then
    Interval.divPos? (Interval.ofPoint 1) ⟨(sqrtEnclosure twoPiVar.lo).lo, (sqrtEnclosure twoPiVar.hi).hi⟩
  else none

/-- `e^{−(x−R_p)²/2σ²} + e^{−(x+R_p)²/2σ²}`. -/
@[expose] def gaussPair (rp var x : CanonicalRat) : Interval :=
  Interval.add (expEnclosure (-((x - rp) * (x - rp)) / (2 * var)))
               (expEnclosure (-((x + rp) * (x + rp)) / (2 * var)))

/-- One dopant's contribution at depth `x`, signed (donors positive). -/
@[expose] def GaussianDopant.enclosure? (g : GaussianDopant) (x : CanonicalRat) : Option Interval :=
  (invSqrt2PiVar? g.varCm2).map fun inv =>
    let sign : CanonicalRat := if g.species.isDonor then 1 else -1
    Interval.scale (sign * g.doseCm2) (Interval.mul inv (gaussPair g.rpCm g.varCm2 x))

/-- **The net doping at depth `x`**, as the interval the real `N(x)` lies in given the enclosures;
`none` if any profile is degenerate. -/
@[expose] def WaferState.dopingEnclosure? (w : WaferState) (x : CanonicalRat) : Option Interval :=
  w.dopants.foldl (fun acc g => do
      let a ← acc
      let e ← g.enclosure? x
      pure (Interval.add a e))
    (some (Interval.ofPoint w.background))

/-- One dopant's contribution at depth `x`, unsigned. -/
@[expose] def GaussianDopant.absEnclosure? (g : GaussianDopant) (x : CanonicalRat) : Option Interval :=
  (invSqrt2PiVar? g.varCm2).map fun inv =>
    Interval.scale (ratAbs g.doseCm2) (Interval.mul inv (gaussPair g.rpCm g.varCm2 x))

/-- **The total ionised impurity at depth `x`**, `|N_bg| + Σ |component|` (what mobility sees;
compensation counts both species). -/
@[expose] def WaferState.totalDopingEnclosure? (w : WaferState) (x : CanonicalRat) : Option Interval :=
  w.dopants.foldl (fun acc g => do
      let a ← acc
      let e ← g.absEnclosure? x
      pure (Interval.add a e))
    (some (Interval.ofPoint (ratAbs w.background)))

/-! ## 7. Recipes -/

/-- A process step with its parameters. Temperatures in K, times in s, energies in keV, doses in
cm⁻², thicknesses in cm. -/
inductive ProcessStep where
  | implant (sp : Species) (keV dose : CanonicalRat)
  | anneal (tempK timeS : CanonicalRat)
  | oxidize (amb : OxidationAmbient) (tempK timeS : CanonicalRat)
  | deposit (m : FilmMaterial) (t : CanonicalRat)
  | etch (m : FilmMaterial) (depth : CanonicalRat)
  | strip (m : FilmMaterial)
  | etchSilicon (depth : CanonicalRat)
  deriving @[expose] DecidableEq, Repr

/-- What the producer supplies per step: nothing for geometry and implant, the diffusivities for an
anneal, the rate constants and thickness for an oxidation. -/
inductive StepCert where
  | none
  | anneal (d : Diffusivities)
  | oxidize (c : OxidationCert)
  deriving @[expose] DecidableEq, Repr

/-- Run a recipe from a wafer, step by step, each step's certificate checked by its operator. -/
@[expose] def runRecipe (kBEv tol : CanonicalRat) : WaferState → List ProcessStep → List StepCert → Option WaferState
  | w, [], _ => some w
  | w, step :: steps, certs =>
    let cert := certs.headD .none
    let rest := certs.tailD []
    let w? : Option WaferState :=
      match step, cert with
      | .implant sp keV dose, _ => w.implant sp keV dose
      | .anneal tempK timeS, .anneal d => if d.ok kBEv tempK ∧ 0 ≤ timeS then some (w.anneal d timeS) else none
      | .oxidize amb tempK timeS, .oxidize c => w.oxidize amb kBEv tempK timeS c tol
      | .deposit m t, _ => if 0 ≤ t then some (w.deposit m t) else none
      | .etch m depth, _ => if 0 ≤ depth then w.etch m depth else none
      | .strip m, _ => w.strip m
      | .etchSilicon depth, _ => if 0 ≤ depth then w.etchSilicon depth else none
      | _, _ => none
    match w? with
    | some w' => runRecipe kBEv tol w' steps rest
    | none => none

end Obend.Hardware.Device
end
