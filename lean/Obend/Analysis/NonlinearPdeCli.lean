module
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Digest.HashBytes
public import Lean.Data.Json
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Hardware.Gpu.StencilTile
import Obend.Elab.PdeSolverElab
import Obend.Hardware.PdeSolvers
import Obend.Hardware.HDL
import Obend.Hardware.YosysLec
import Obend.Receipt.Merkle
import Obend.Core.Digest
import Obend.Codec.Hex

/-!
# `obend pde`: the nonlinear conservation-law solver, checker and emitter

`runPdeCli` is the whole `obend pde check|solve` adapter. The linear formats
(`hyperbolic-fvm@1`, `pde-approx-defect@1`) keep their behaviour; `nonlinear-conservation@1` runs a
`(conservation-law …)` S-expression accepted by `validatePdeSolverSexpr`.

* **Scheme.** One turn is a Lie or Strang schedule of directional MUSCL/Rusanov sweeps
  (`cellUpdate`), each materialized into an array before the next. The exact backend is `Rat`
  (`rolloutRat`); the `q32` backend runs `evalNonlinearFluxCellQ32` over the same ghost cells.
* **Boundaries.** `ghostIndex` resolves the five cells of a directional stencil under a
  `PdeBoundaryPolicy`: toroidal, zero-gradient, or mirrored with sign-flipped components.
  `rolloutRat_periodic_conserves_integral` is conservation of the executed periodic rollout for
  either limiter; `reflectiveWallFace_zero_flux` is the vanishing of the executed wall-face flux of
  a component whose flux is odd under the mirror, and `rolloutRat_reflective_conserves_component`
  proves multi-step conservation of odd-flux un-negated components on reflective boxes with
  `∀ N ∈ dims, 2 ≤ N` (outflow transmissive boundaries need not conserve total mass).
* **Receipt.** `pdeTrajectoryBytes` frames every field of a `PdeTrajectoryStatement` with
  `Receipt.Merkle.encodeFields`; it is injective with no width hypothesis, so
  `pdeTrajectoryDigest_binding` ends in the statement's equality or a collision among the two
  preimages hashed.
* **Surrogate mode.** With a `tolerance`, `check` accepts a trajectory whose declared tube
  `t₀ = ‖u₀ - initial‖`, `t_{k+1} = L·t_k + ‖u_{k+1} - step u_k‖` and whose true final max-norm
  error against the exact `Rat` rollout are both within it. `L` (`amplification`, default 1) is the
  caller's declared amplification, not a derived Lipschitz constant; the true final error is what
  acceptance means.
-/

public section
namespace Obend.Analysis.NonlinearPdeCli
open Lean (Json toJson)
open Obend.Analysis.HyperbolicPde Obend.Analysis.PdeSexprAndApprox Obend.Analysis.NonlinearMultiDPde
open Obend.Hardware.Gpu.StencilTile (StencilBoundary resolveStencilIdx)
open Obend.Hardware.MultiDStencilTile
open Obend.Digest.HashBytes (Hash CollisionAmong ofBE)
open Obend.Receipt.Merkle (leb128 leb128_injective encodeFields encodeFields_injective)
set_option autoImplicit false

/-! ## 1. Boundary policies and the directional stencil -/

inductive PdeBoundaryPolicy where
  | periodic | transmissive | reflective (negVars : List Nat)
  deriving DecidableEq, Repr

def PdeBoundaryPolicy.negVars : PdeBoundaryPolicy → List Nat
  | .reflective ns => ns
  | _ => []

def PdeBoundaryPolicy.tag : PdeBoundaryPolicy → String
  | .periodic => "periodic" | .transmissive => "transmissive" | .reflective _ => "reflective"

/-- The mirror image of a state: the listed components change sign. -/
def negateVars (negVars : List Nat) (u : Vec) : Vec := fun c => if c ∈ negVars then -u c else u c

/-- The cell a stencil offset `off ∈ [-2, 2]` along `axis` reads, and whether it is a mirror image. -/
def ghostIndex (pol : PdeBoundaryPolicy) (dims : List Nat) (axis idx : Nat) (off : Int) : Nat × Bool :=
  match pol with
  | .periodic =>
    let prev := axisPeriodicNeighbor dims axis false
    let next := axisPeriodicNeighbor dims axis true
    (if off = -2 then prev (prev idx) else if off = -1 then prev idx else if off = 1 then next idx
      else if off = 2 then next (next idx) else idx, false)
  | pol =>
    let f := axisFiberDims dims axis
    let coord := idx % (f.axisLen * f.inner) / f.inner
    let i : Int := (coord : Int) + off
    let r : Nat × Bool :=
      if pol = .transmissive then (resolveStencilIdx .clamp f.axisLen i, false)
      else if i < 0 then (resolveStencilIdx .clamp f.axisLen (-i - 1), true)
      else if (f.axisLen : Int) ≤ i then
        (resolveStencilIdx .clamp f.axisLen (2 * (f.axisLen : Int) - 1 - i), true)
      else (i.toNat, false)
    (idx - coord * f.inner + r.1 * f.inner, r.2)

def sampleRat (pol : PdeBoundaryPolicy) (U : MultiDGrid) (g : Nat × Bool) : Vec :=
  if g.2 then negateVars pol.negVars (U g.1) else U g.1

/-- Left state of the face between `s0` and `s1`. -/
def reconL (spec : ConservationLawSpec) (sm s0 s1 : Vec) : Vec := fun j =>
  if spec.limiter = .firstOrder then s0 j else musclReconstructRight (sm j) (s0 j) (s1 j)

/-- Right state of the face between `s0` and `s1`. -/
def reconR (spec : ConservationLawSpec) (s0 s1 sp : Vec) : Vec := fun j =>
  if spec.limiter = .firstOrder then s1 j else musclReconstructLeft (s0 j) (s1 j) (sp j)

/-- Rusanov flux through the face between `s0` and `s1`, from the four cells around it. -/
def faceFlux (spec : ConservationLawSpec) (axis : Nat) (sm s0 s1 sp : Vec) : Vec :=
  rusanovNonlinearFlux (getOr spec.fluxes axis []) spec.paramEnv spec.aMax
    (reconL spec sm s0 s1) (reconR spec s0 s1 sp)

def cellUpdate (spec : ConservationLawSpec) (pol : PdeBoundaryPolicy) (dims : List Nat)
    (axis : Nat) (ν : Rat) (U : MultiDGrid) (idx c : Nat) : Rat :=
  let s : Int → Vec := fun off => sampleRat pol U (ghostIndex pol dims axis idx off)
  s 0 c - ν * (faceFlux spec axis (s (-1)) (s 0) (s 1) (s 2) c -
    faceFlux spec axis (s (-2)) (s (-1)) (s 0) (s 1) c)

def sweepFn (spec : ConservationLawSpec) (pol : PdeBoundaryPolicy) (dims : List Nat)
    (axis : Nat) (ν : Rat) (U : MultiDGrid) : MultiDGrid :=
  if axis < dims.length then fun idx c => cellUpdate spec pol dims axis ν U idx c else U

/-! ## 2. Periodic conservation

A MUSCL face reads four cells, where `directionalSweep_conserves_integral` is stated for a
two-cell flux. Packing each cell with its two axis neighbours turns the four-cell face into a
two-cell flux on the packed grid, whose component `3 * c` is the original component `c`. -/

private def pack3 (p s n : Vec) : Vec := fun j =>
  if j % 3 = 0 then s (j / 3) else if j % 3 = 1 then p (j / 3) else n (j / 3)

private theorem pack3_self (p s n : Vec) (c : Nat) : pack3 p s n (3 * c) = s c := by
  have h1 : 3 * c % 3 = 0 := by omega
  have h2 : 3 * c / 3 = c := by omega
  simp [pack3, h1, h2]

private theorem pack3_prev (p s n : Vec) (c : Nat) : pack3 p s n (3 * c + 1) = p c := by
  have h1 : (3 * c + 1) % 3 = 1 := by omega
  have h2 : (3 * c + 1) / 3 = c := by omega
  simp [pack3, h1, h2]

private theorem pack3_next (p s n : Vec) (c : Nat) : pack3 p s n (3 * c + 2) = n c := by
  have h1 : (3 * c + 2) % 3 = 2 := by omega
  have h2 : (3 * c + 2) / 3 = c := by omega
  simp [pack3, h1, h2]

private def packGrid (dims : List Nat) (axis : Nat) (U : MultiDGrid) : MultiDGrid := fun i =>
  pack3 (U (axisPeriodicNeighbor dims axis false i)) (U i) (U (axisPeriodicNeighbor dims axis true i))

private def packedFlux (spec : ConservationLawSpec) (axis : Nat) (a b : Vec) : Vec := fun j =>
  faceFlux spec axis (fun c => a (3 * c + 1)) (fun c => a (3 * c)) (fun c => b (3 * c))
    (fun c => b (3 * c + 2)) (j / 3)

private theorem cellUpdate_periodic (spec : ConservationLawSpec) (dims : List Nat) (axis : Nat)
    (ν : Rat) (U : MultiDGrid) (idx c : Nat) (hAxis : axis < dims.length) :
    cellUpdate spec .periodic dims axis ν U idx c =
      evalDirectionalSweep dims axis ν (packedFlux spec axis) (packGrid dims axis U) idx (3 * c) := by
  have h2 : 3 * c / 3 = c := by omega
  simp [cellUpdate, evalDirectionalSweep, hAxis, packedFlux, packGrid, pack3_self, pack3_prev,
    pack3_next, ghostIndex, sampleRat, h2]

theorem periodicSweep_conserves_integral (spec : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (axis : Nat) (ν : Rat) (U : MultiDGrid) (c : Nat) :
    totalGridIntegral dims (sweepFn spec .periodic dims axis ν U) c = totalGridIntegral dims U c := by
  unfold sweepFn
  by_cases hAxis : axis < dims.length
  · simp only [hAxis, ↓reduceIte]
    have h := directionalSweep_conserves_integral dims hPos axis ν (packedFlux spec axis)
      (packGrid dims axis U) (3 * c)
    unfold totalGridIntegral at h ⊢
    rw [sumTo_congr fun idx _ => cellUpdate_periodic spec dims axis ν U idx c hAxis, h]
    exact sumTo_congr fun idx _ => pack3_self _ _ _ c
  · simp [hAxis]

/-! ## 3. The materialized `Rat` rollout -/

abbrev RatGrid := Array (Array Rat)

def gridFn (G : RatGrid) : MultiDGrid := fun idx c => ((G[idx]?).getD #[])[c]?.getD 0

def tabulate (n m : Nat) (U : MultiDGrid) : RatGrid :=
  Array.ofFn (n := n) fun i => Array.ofFn (n := m) fun c => U i c

private theorem gridFn_tabulate (n m : Nat) (U : MultiDGrid) (idx c : Nat) (hi : idx < n)
    (hc : c < m) : gridFn (tabulate n m U) idx c = U idx c := by
  simp [gridFn, tabulate, hi, hc]

/-- The directional sweeps of one turn: every axis at `ν`, or the Strang palindrome at `ν / 2`. -/
def sweepSchedule (dims : List Nat) (ν : Rat) (useStrang : Bool) : List (Nat × Rat) :=
  let axes := List.range dims.length
  if useStrang then axes.map (·, ν / 2) ++ (axes.map (·, ν / 2)).reverse else axes.map (·, ν)

def sweepRat (spec : ConservationLawSpec) (pol : PdeBoundaryPolicy) (dims : List Nat)
    (G : RatGrid) (step : Nat × Rat) : RatGrid :=
  tabulate (gridCellCount dims) spec.numVars (sweepFn spec pol dims step.1 step.2 (gridFn G))

def sourceStepRat (spec : ConservationLawSpec) (dims : List Nat) (dt : Rat) (G : RatGrid) :
    RatGrid :=
  if spec.sources.isEmpty then G
  else tabulate (gridCellCount dims) spec.numVars fun idx c =>
    gridFn G idx c + dt * evalFlux (getOr spec.sources c (.const 0)) ⟨gridFn G idx, spec.paramEnv⟩

def turnRat (spec : ConservationLawSpec) (pol : PdeBoundaryPolicy) (dims : List Nat)
    (useStrang : Bool) (G : RatGrid) : RatGrid :=
  if spec.sources.isEmpty then
    (sweepSchedule dims spec.cfl useStrang).foldl (sweepRat spec pol dims) G
  else if useStrang then
    let g1 := sourceStepRat spec dims (spec.cfl / 2) G
    let g2 := (sweepSchedule dims spec.cfl true).foldl (sweepRat spec pol dims) g1
    sourceStepRat spec dims (spec.cfl / 2) g2
  else
    let g1 := (sweepSchedule dims spec.cfl false).foldl (sweepRat spec pol dims) G
    sourceStepRat spec dims spec.cfl g1

def rolloutRat (spec : ConservationLawSpec) (pol : PdeBoundaryPolicy) (dims : List Nat)
    (useStrang : Bool) : Nat → RatGrid → RatGrid
  | 0, G => G
  | k + 1, G => rolloutRat spec pol dims useStrang k (turnRat spec pol dims useStrang G)

private theorem sourceStepRat_conserves_sourceless (spec : ConservationLawSpec) (dims : List Nat)
    (dt : Rat) (c : Nat) (hc : c < spec.numVars)
    (hSrc : spec.sources.isEmpty = true ∨ getOr spec.sources c (.const 0) = .const 0)
    (G : RatGrid) :
    totalGridIntegral dims (gridFn (sourceStepRat spec dims dt G)) c =
      totalGridIntegral dims (gridFn G) c := by
  unfold sourceStepRat
  split
  · rfl
  · next hne =>
    rcases hSrc with he | hz
    · exact absurd he hne
    · unfold totalGridIntegral
      refine sumTo_congr fun idx hi => ?_
      rw [gridFn_tabulate _ _ _ idx c hi hc, hz]
      simp only [evalFlux]; grind

private theorem sweepRat_periodic_conserves (spec : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (c : Nat) (hc : c < spec.numVars) (G : RatGrid) (step : Nat × Rat) :
    totalGridIntegral dims (gridFn (sweepRat spec .periodic dims G step)) c =
      totalGridIntegral dims (gridFn G) c := by
  rw [← periodicSweep_conserves_integral spec dims hPos step.1 step.2 (gridFn G) c]
  unfold totalGridIntegral sweepRat
  exact sumTo_congr fun idx hi => gridFn_tabulate _ _ _ idx c hi hc

private theorem turnRat_periodic_conserves (spec : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (c : Nat) (hc : c < spec.numVars) (sched : List (Nat × Rat))
    (G : RatGrid) :
    totalGridIntegral dims (gridFn (sched.foldl (sweepRat spec .periodic dims) G)) c =
      totalGridIntegral dims (gridFn G) c := by
  induction sched generalizing G with
  | nil => rfl
  | cons s rest ih =>
    rw [List.foldl_cons, ih, sweepRat_periodic_conserves spec dims hPos c hc]

private theorem fullTurnRat_periodic_conserves (spec : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (useStrang : Bool) (c : Nat) (hc : c < spec.numVars)
    (hSrc : spec.sources.isEmpty = true ∨ getOr spec.sources c (.const 0) = .const 0)
    (G : RatGrid) :
    totalGridIntegral dims (gridFn (turnRat spec .periodic dims useStrang G)) c =
      totalGridIntegral dims (gridFn G) c := by
  unfold turnRat
  split
  · exact turnRat_periodic_conserves spec dims hPos c hc _ G
  · split
    · dsimp only []
      rw [sourceStepRat_conserves_sourceless spec dims _ c hc hSrc,
          turnRat_periodic_conserves spec dims hPos c hc,
          sourceStepRat_conserves_sourceless spec dims _ c hc hSrc]
    · dsimp only []
      rw [sourceStepRat_conserves_sourceless spec dims _ c hc hSrc,
          turnRat_periodic_conserves spec dims hPos c hc]

/-- **The executed periodic rollout conserves every sourceless component's integral**, for either
limiter, Lie or Strang turns, any dimension count and any number of steps. -/
theorem rolloutRat_periodic_conserves_integral (spec : ConservationLawSpec) (dims : List Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (useStrang : Bool) (steps : Nat) (G : RatGrid) (c : Nat)
    (hc : c < spec.numVars)
    (hSrc : spec.sources.isEmpty = true ∨ getOr spec.sources c (.const 0) = .const 0 :=
      by left; decide) :
    totalGridIntegral dims (gridFn (rolloutRat spec .periodic dims useStrang steps G)) c =
      totalGridIntegral dims (gridFn G) c := by
  induction steps generalizing G with
  | zero => rfl
  | succ k ih =>
    rw [rolloutRat, ih]
    exact fullTurnRat_periodic_conserves spec dims hPos useStrang c hc hSrc G

/-! ## 4. Reflective walls -/

/-- A component that is not mirrored, and whose flux is odd under the mirror, has zero Rusanov
flux between a state and its mirror image, on either side. -/
theorem reflectiveWall_zero_normal_flux (fluxD : List FluxExpr) (pEnv : Nat → Rat) (aMax : Rat)
    (negVars : List Nat) (uInt : Vec) (c : Nat) (hc : c ∉ negVars)
    (hOdd : evalFlux (getOr fluxD c (.const 0)) ⟨negateVars negVars uInt, pEnv⟩ =
      -evalFlux (getOr fluxD c (.const 0)) ⟨uInt, pEnv⟩) :
    rusanovNonlinearFlux fluxD pEnv aMax (negateVars negVars uInt) uInt c = 0 ∧
    rusanovNonlinearFlux fluxD pEnv aMax uInt (negateVars negVars uInt) c = 0 := by
  have hSame : negateVars negVars uInt c = uInt c := by simp [negateVars, hc]
  simp only [rusanovNonlinearFlux, hOdd, hSame]
  constructor <;> grind

private theorem musclReconstructRight_neg (a b c : Rat) :
    musclReconstructRight (-a) (-b) (-c) = -musclReconstructRight a b c := by
  unfold musclReconstructRight
  rw [show -b - -a = -(b - a) by grind, show -c - -b = -(c - b) by grind, minmod_neg]; grind

private theorem muscl_mirror_neg (a b : Rat) :
    musclReconstructRight (-b) (-a) a = -musclReconstructRight b a (-a) := by
  rw [← musclReconstructRight_neg]; congr 1; grind

/-- **The executed wall faces carry no flux** of such a component: at the low wall the two ghost
cells mirror `u0, u1`, at the high wall they mirror the last two cells, and the reconstructed
states on the two sides of the wall are again mirror images. -/
theorem reflectiveWallFace_zero_flux (spec : ConservationLawSpec) (axis : Nat)
    (negVars : List Nat) (u0 u1 : Vec) (c : Nat) (hc : c ∉ negVars)
    (hOdd : ∀ u : Vec,
      evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨negateVars negVars u, spec.paramEnv⟩ =
        -evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨u, spec.paramEnv⟩) :
    faceFlux spec axis (negateVars negVars u1) (negateVars negVars u0) u0 u1 c = 0 ∧
    faceFlux spec axis u1 u0 (negateVars negVars u0) (negateVars negVars u1) c = 0 := by
  have hLow : reconL spec (negateVars negVars u1) (negateVars negVars u0) u0 =
      negateVars negVars (reconR spec (negateVars negVars u0) u0 u1) := by
    funext j
    by_cases hl : spec.limiter = .firstOrder
    · simp [reconL, reconR, negateVars, hl]
    · by_cases hj : j ∈ negVars
      · simp only [reconL, reconR, negateVars, hl, hj, ↓reduceIte]
        rw [muscl_minmod_mirror_symm (u1 j) (u0 j) (-u0 j)]; exact muscl_mirror_neg _ _
      · simp only [reconL, reconR, negateVars, hl, hj, ↓reduceIte]
        exact (muscl_minmod_mirror_symm (u1 j) (u0 j) (u0 j)).symm
  have hHigh : reconR spec u0 (negateVars negVars u0) (negateVars negVars u1) =
      negateVars negVars (reconL spec u1 u0 (negateVars negVars u0)) := by
    funext j
    by_cases hl : spec.limiter = .firstOrder
    · simp [reconL, reconR, negateVars, hl]
    · by_cases hj : j ∈ negVars
      · simp only [reconL, reconR, negateVars, hl, hj, ↓reduceIte]
        rw [muscl_minmod_mirror_symm (-u1 j) (-u0 j) (u0 j)]; exact muscl_mirror_neg _ _
      · simp only [reconL, reconR, negateVars, hl, hj, ↓reduceIte]
        exact muscl_minmod_mirror_symm (u1 j) (u0 j) (u0 j)
  unfold faceFlux
  rw [hLow, hHigh]
  exact ⟨(reflectiveWall_zero_normal_flux _ _ _ negVars _ c hc (hOdd _)).1,
    (reflectiveWall_zero_normal_flux _ _ _ negVars _ c hc (hOdd _)).2⟩

private def mirrorIndex1D (N : Nat) (i : Int) : Nat × Bool :=
  if i < 0 then (resolveStencilIdx .clamp N (-i - 1), true)
  else if (N : Int) ≤ i then (resolveStencilIdx .clamp N (2 * (N : Int) - 1 - i), true)
  else (i.toNat, false)

private def mirrorSample1D (negVars : List Nat) (N : Nat) (u : Nat → Vec) (i : Int) : Vec :=
  let g := mirrorIndex1D N i
  if g.2 then negateVars negVars (u g.1) else u g.1

private theorem ghostIndex_reflective_fiber (negVars : List Nat) (dims : List Nat) (axis : Nat)
    (hPos : ∀ N ∈ dims, 0 < N)
    (o k r : Nat) (hk : k < (axisFiberDims dims axis).axisLen)
    (hr : r < (axisFiberDims dims axis).inner) (off : Int) :
    let f := axisFiberDims dims axis
    let cellAt := fun m => o * (f.axisLen * f.inner) + (m * f.inner + r)
    let g := mirrorIndex1D f.axisLen ((k : Int) + off)
    ghostIndex (.reflective negVars) dims axis (cellAt k) off = (cellAt g.1, g.2) := by
  intro f cellAt g
  have hk' : k < f.axisLen := hk
  have hr' : r < f.inner := hr
  have hInnerPos : 0 < f.inner :=
    gridCellCount_pos _ fun M hM => hPos M (List.mem_of_mem_drop hM)
  have hrem_lt : k * f.inner + r < f.axisLen * f.inner := by
    have h2 := Nat.mul_le_mul_right f.inner (show k + 1 ≤ f.axisLen by omega)
    rw [Nat.add_mul, Nat.one_mul] at h2; omega
  have hmod1 : (o * (f.axisLen * f.inner) + (k * f.inner + r)) % (f.axisLen * f.inner) =
      k * f.inner + r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem_lt]
  have hdiv2 : (k * f.inner + r) / f.inner = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hInnerPos, Nat.div_eq_of_lt hr', Nat.zero_add]
  have hCoord : cellAt k % (f.axisLen * f.inner) / f.inner = k := by
    dsimp only [cellAt]; rw [hmod1, hdiv2]
  have hNeq : (PdeBoundaryPolicy.reflective negVars = .transmissive) = False := by simp
  unfold ghostIndex
  dsimp only []
  simp only [hNeq, ↓reduceIte]
  change (cellAt k - (cellAt k % (f.axisLen * f.inner) / f.inner) * f.inner +
      (mirrorIndex1D f.axisLen (Int.ofNat (cellAt k % (f.axisLen * f.inner) / f.inner) + off)).1 * f.inner,
    (mirrorIndex1D f.axisLen (Int.ofNat (cellAt k % (f.axisLen * f.inner) / f.inner) + off)).2) =
    (cellAt g.1, g.2)
  rw [hCoord]
  refine Prod.ext ?_ rfl
  dsimp only [cellAt, g]
  simp only [Int.ofNat_eq_natCast]
  omega

private theorem sampleRat_reflective_fiber (negVars : List Nat) (dims : List Nat) (axis : Nat)
    (hPos : ∀ N ∈ dims, 0 < N) (U : MultiDGrid)
    (o k r : Nat) (hk : k < (axisFiberDims dims axis).axisLen)
    (hr : r < (axisFiberDims dims axis).inner) (off : Int) :
    let f := axisFiberDims dims axis
    let cellAt := fun m => o * (f.axisLen * f.inner) + (m * f.inner + r)
    sampleRat (.reflective negVars) U (ghostIndex (.reflective negVars) dims axis (cellAt k) off) =
      mirrorSample1D negVars f.axisLen (fun m => U (cellAt m)) ((k : Int) + off) := by
  intro f cellAt
  rw [ghostIndex_reflective_fiber negVars dims axis hPos o k r hk hr off]
  rfl

private theorem resolveStencilIdx_clamp_of_lt (N : Nat) (i : Int) (h0 : 0 ≤ i) (hi : i < (N : Int)) :
    resolveStencilIdx .clamp N i = i.toNat := by
  simp only [resolveStencilIdx]
  split <;> (try split) <;> omega

private theorem mirrorSample1D_inBounds (negVars : List Nat) (N : Nat) (u : Nat → Vec)
    (k : Nat) (hk : k < N) :
    mirrorSample1D negVars N u (k : Int) = u k := by
  have h1 : ¬ ((k : Int) < 0) := by omega
  have h2 : ¬ ((N : Int) ≤ (k : Int)) := by omega
  simp [mirrorSample1D, mirrorIndex1D, h1, h2]

private theorem mirrorSample1D_low_m2 (negVars : List Nat) (N : Nat) (hN : 2 ≤ N) (u : Nat → Vec) :
    mirrorSample1D negVars N u (-2) = negateVars negVars (u 1) := by
  have hcl : resolveStencilIdx .clamp N 1 = 1 := by
    rw [resolveStencilIdx_clamp_of_lt N 1 (by omega) (by omega)]; rfl
  simp [mirrorSample1D, mirrorIndex1D, hcl]

private theorem mirrorSample1D_low_m1 (negVars : List Nat) (N : Nat) (hN : 2 ≤ N) (u : Nat → Vec) :
    mirrorSample1D negVars N u (-1) = negateVars negVars (u 0) := by
  have hcl : resolveStencilIdx .clamp N 0 = 0 := by
    rw [resolveStencilIdx_clamp_of_lt N 0 (by omega) (by omega)]; rfl
  simp [mirrorSample1D, mirrorIndex1D, hcl]

private theorem mirrorSample1D_high_0 (negVars : List Nat) (N : Nat) (hN : 2 ≤ N) (u : Nat → Vec) :
    mirrorSample1D negVars N u (N : Int) = negateVars negVars (u (N - 1)) := by
  have h1 : ¬ ((N : Int) < 0) := by omega
  have hcl : resolveStencilIdx .clamp N (2 * (N : Int) - 1 - (N : Int)) = N - 1 := by
    rw [resolveStencilIdx_clamp_of_lt N (2 * (N : Int) - 1 - (N : Int)) (by omega) (by omega)]; omega
  simp [mirrorSample1D, mirrorIndex1D, h1, hcl]

private theorem mirrorSample1D_high_1 (negVars : List Nat) (N : Nat) (hN : 2 ≤ N) (u : Nat → Vec) :
    mirrorSample1D negVars N u ((N : Int) + 1) = negateVars negVars (u (N - 2)) := by
  have h1 : ¬ ((N : Int) + 1 < 0) := by omega
  have h2 : (N : Int) ≤ (N : Int) + 1 := by omega
  have hcl : resolveStencilIdx .clamp N (2 * (N : Int) - 1 - ((N : Int) + 1)) = N - 2 := by
    rw [resolveStencilIdx_clamp_of_lt N (2 * (N : Int) - 1 - ((N : Int) + 1)) (by omega) (by omega)]; omega
  simp [mirrorSample1D, mirrorIndex1D, h1, h2, hcl]

private theorem sumTo_telescope (N : Nat) (g : Nat → Rat) :
    sumTo N (fun k => g (k + 1) - g k) = g N - g 0 := by
  induction N with
  | zero => simp [sumTo]; grind
  | succ n ih => simp only [sumTo, ih]; grind

/-- **One reflective directional sweep conserves every odd-flux un-negated component** on any box
with at least two cells along every axis, under either limiter. -/
theorem reflectiveSweep_conserves_component (spec : ConservationLawSpec)
    (negVars : List Nat) (dims : List Nat) (hDims2 : ∀ N ∈ dims, 2 ≤ N)
    (axis : Nat) (ν : Rat) (U : MultiDGrid) (c : Nat)
    (hcNotNeg : c ∉ negVars)
    (hOdd : ∀ u : Vec,
      evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨negateVars negVars u, spec.paramEnv⟩ =
        -evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨u, spec.paramEnv⟩) :
    totalGridIntegral dims (sweepFn spec (.reflective negVars) dims axis ν U) c =
      totalGridIntegral dims U c := by
  unfold sweepFn
  by_cases hAxis : axis < dims.length
  · simp only [hAxis, ↓reduceIte]
    unfold totalGridIntegral
    let f := axisFiberDims dims axis
    have hPos : ∀ N ∈ dims, 0 < N := fun N hN => by have := hDims2 N hN; omega
    have hAxisGe2 : 2 ≤ f.axisLen := hDims2 _ (getOr_mem_of_lt dims axis 1 hAxis)
    rw [axisFiberDims_prod dims axis hAxis,
        sumTo_mul_split f.outer (f.axisLen * f.inner),
        sumTo_mul_split f.outer (f.axisLen * f.inner)]
    refine sumTo_congr fun o _ => ?_
    rw [sumTo_mul_split f.axisLen f.inner, sumTo_mul_split f.axisLen f.inner,
        sumTo_comm f.axisLen f.inner, sumTo_comm f.axisLen f.inner]
    refine sumTo_congr fun r hr => ?_
    let cellAt : Nat → Nat := fun m => o * (f.axisLen * f.inner) + (m * f.inner + r)
    let u : Nat → Vec := fun m => U (cellAt m)
    let s1D : Int → Vec := mirrorSample1D negVars f.axisLen u
    let F_face : Nat → Rat := fun j =>
      faceFlux spec axis (s1D ((j : Int) - 2)) (s1D ((j : Int) - 1)) (s1D (j : Int)) (s1D ((j : Int) + 1)) c
    have hCell : ∀ k, k < f.axisLen →
        cellUpdate spec (.reflective negVars) dims axis ν U (cellAt k) c =
          u k c + (-ν) * (F_face (k + 1) - F_face k) := by
      intro k hk
      unfold cellUpdate
      have hs : ∀ off : Int,
          sampleRat (.reflective negVars) U (ghostIndex (.reflective negVars) dims axis (cellAt k) off) =
            s1D ((k : Int) + off) := fun off =>
        sampleRat_reflective_fiber negVars dims axis hPos U o k r hk hr off
      simp only [hs]
      have h0 : (k : Int) + 0 = (k : Int) := by omega
      have h0u : s1D ((k : Int) + 0) = u k := by rw [h0]; exact mirrorSample1D_inBounds negVars f.axisLen u k hk
      have hR : faceFlux spec axis (s1D ((k : Int) + (-1))) (s1D ((k : Int) + 0))
          (s1D ((k : Int) + 1)) (s1D ((k : Int) + 2)) c = F_face (k + 1) := by
        dsimp only [F_face]
        rw [show (k : Int) + (-1) = ((k + 1 : Nat) : Int) - 2 by omega,
            show (k : Int) + 0 = ((k + 1 : Nat) : Int) - 1 by omega,
            show (k : Int) + 1 = ((k + 1 : Nat) : Int) by omega,
            show (k : Int) + 2 = ((k + 1 : Nat) : Int) + 1 by omega]
      have hL : faceFlux spec axis (s1D ((k : Int) + (-2))) (s1D ((k : Int) + (-1)))
          (s1D ((k : Int) + 0)) (s1D ((k : Int) + 1)) c = F_face k := by
        dsimp only [F_face]
        rw [show (k : Int) + (-2) = (k : Int) - 2 by omega,
            show (k : Int) + (-1) = (k : Int) - 1 by omega,
            h0]
      rw [hR, hL, h0u]; grind
    have hF0 : F_face 0 = 0 := by
      dsimp only [F_face, s1D]
      rw [show ((0 : Nat) : Int) - 2 = -2 by omega,
          show ((0 : Nat) : Int) - 1 = -1 by omega,
          show ((0 : Nat) : Int) + 1 = ((1 : Nat) : Int) by omega,
          mirrorSample1D_low_m2 negVars f.axisLen hAxisGe2 u,
          mirrorSample1D_low_m1 negVars f.axisLen hAxisGe2 u,
          mirrorSample1D_inBounds negVars f.axisLen u 0 (by omega),
          mirrorSample1D_inBounds negVars f.axisLen u 1 (by omega)]
      exact (reflectiveWallFace_zero_flux spec axis negVars (u 0) (u 1) c hcNotNeg hOdd).1
    have hFN : F_face f.axisLen = 0 := by
      dsimp only [F_face, s1D]
      rw [show (f.axisLen : Int) - 2 = ((f.axisLen - 2 : Nat) : Int) by omega,
          show (f.axisLen : Int) - 1 = ((f.axisLen - 1 : Nat) : Int) by omega,
          mirrorSample1D_inBounds negVars f.axisLen u (f.axisLen - 2) (by omega),
          mirrorSample1D_inBounds negVars f.axisLen u (f.axisLen - 1) (by omega),
          mirrorSample1D_high_0 negVars f.axisLen hAxisGe2 u,
          mirrorSample1D_high_1 negVars f.axisLen hAxisGe2 u]
      exact (reflectiveWallFace_zero_flux spec axis negVars (u (f.axisLen - 1)) (u (f.axisLen - 2))
        c hcNotNeg hOdd).2
    rw [sumTo_congr hCell, sumTo_add, sumTo_mul_left, sumTo_telescope, hFN, hF0]
    grind
  · simp [hAxis]

private theorem sweepSchedule_axes_lt (dims : List Nat) (ν : Rat) (useStrang : Bool) :
    ∀ s ∈ sweepSchedule dims ν useStrang, s.1 < dims.length := by
  unfold sweepSchedule
  split <;> intro s hs
  · rcases List.mem_append.mp hs with h1 | h2
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h1; exact List.mem_range.mp ha
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp h2); exact List.mem_range.mp ha
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs; exact List.mem_range.mp ha

private theorem sweepRat_reflective_conserves (spec : ConservationLawSpec)
    (negVars : List Nat) (dims : List Nat) (hDims2 : ∀ N ∈ dims, 2 ≤ N)
    (c : Nat) (hcVar : c < spec.numVars) (hcNotNeg : c ∉ negVars) (G : RatGrid) (step : Nat × Rat)
    (hOdd : ∀ u : Vec,
      evalFlux (getOr (getOr spec.fluxes step.1 []) c (.const 0)) ⟨negateVars negVars u, spec.paramEnv⟩ =
        -evalFlux (getOr (getOr spec.fluxes step.1 []) c (.const 0)) ⟨u, spec.paramEnv⟩) :
    totalGridIntegral dims (gridFn (sweepRat spec (.reflective negVars) dims G step)) c =
      totalGridIntegral dims (gridFn G) c := by
  rw [← reflectiveSweep_conserves_component spec negVars dims hDims2 step.1 step.2 (gridFn G) c
    hcNotNeg hOdd]
  unfold totalGridIntegral sweepRat
  exact sumTo_congr fun idx hi => gridFn_tabulate _ _ _ idx c hi hcVar

private theorem turnRat_reflective_conserves (spec : ConservationLawSpec)
    (negVars : List Nat) (dims : List Nat) (hDims2 : ∀ N ∈ dims, 2 ≤ N)
    (c : Nat) (hcVar : c < spec.numVars) (hcNotNeg : c ∉ negVars)
    (hOdd : ∀ axis, axis < dims.length → ∀ u : Vec,
      evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨negateVars negVars u, spec.paramEnv⟩ =
        -evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨u, spec.paramEnv⟩)
    (sched : List (Nat × Rat)) (hSched : ∀ s ∈ sched, s.1 < dims.length) (G : RatGrid) :
    totalGridIntegral dims (gridFn (sched.foldl (sweepRat spec (.reflective negVars) dims) G)) c =
      totalGridIntegral dims (gridFn G) c := by
  induction sched generalizing G with
  | nil => rfl
  | cons s rest ih =>
    rw [List.foldl_cons, ih (fun x hx => hSched x (List.mem_cons_of_mem _ hx)),
        sweepRat_reflective_conserves spec negVars dims hDims2 c hcVar hcNotNeg G s
          (hOdd s.1 (hSched s List.mem_cons_self))]

private theorem fullTurnRat_reflective_conserves (spec : ConservationLawSpec)
    (negVars : List Nat) (dims : List Nat) (hDims2 : ∀ N ∈ dims, 2 ≤ N) (useStrang : Bool)
    (c : Nat) (hcVar : c < spec.numVars) (hcNotNeg : c ∉ negVars)
    (hOdd : ∀ axis, axis < dims.length → ∀ u : Vec,
      evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨negateVars negVars u, spec.paramEnv⟩ =
        -evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨u, spec.paramEnv⟩)
    (hSrc : spec.sources.isEmpty = true ∨ getOr spec.sources c (.const 0) = .const 0)
    (G : RatGrid) :
    totalGridIntegral dims (gridFn (turnRat spec (.reflective negVars) dims useStrang G)) c =
      totalGridIntegral dims (gridFn G) c := by
  unfold turnRat
  split
  · exact turnRat_reflective_conserves spec negVars dims hDims2 c hcVar hcNotNeg hOdd _
      (sweepSchedule_axes_lt dims spec.cfl useStrang) G
  · split
    · dsimp only []
      rw [sourceStepRat_conserves_sourceless spec dims _ c hcVar hSrc,
          turnRat_reflective_conserves spec negVars dims hDims2 c hcVar hcNotNeg hOdd _
            (sweepSchedule_axes_lt dims spec.cfl true),
          sourceStepRat_conserves_sourceless spec dims _ c hcVar hSrc]
    · dsimp only []
      rw [sourceStepRat_conserves_sourceless spec dims _ c hcVar hSrc,
          turnRat_reflective_conserves spec negVars dims hDims2 c hcVar hcNotNeg hOdd _
            (sweepSchedule_axes_lt dims spec.cfl false)]

/-- **The executed reflective rollout conserves every sourceless odd-flux un-negated component** on
boxes with `∀ N ∈ dims, 2 ≤ N`, for either limiter, Lie or Strang turns, any dimension count, and
any number of steps. -/
theorem rolloutRat_reflective_conserves_component (spec : ConservationLawSpec)
    (negVars : List Nat) (dims : List Nat) (hDims2 : ∀ N ∈ dims, 2 ≤ N)
    (useStrang : Bool) (steps : Nat) (G : RatGrid) (c : Nat)
    (hcVar : c < spec.numVars) (hcNotNeg : c ∉ negVars)
    (hOdd : ∀ axis, axis < dims.length → ∀ u : Vec,
      evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨negateVars negVars u, spec.paramEnv⟩ =
        -evalFlux (getOr (getOr spec.fluxes axis []) c (.const 0)) ⟨u, spec.paramEnv⟩)
    (hSrc : spec.sources.isEmpty = true ∨ getOr spec.sources c (.const 0) = .const 0 :=
      by left; decide) :
    totalGridIntegral dims (gridFn (rolloutRat spec (.reflective negVars) dims useStrang steps G)) c =
      totalGridIntegral dims (gridFn G) c := by
  induction steps generalizing G with
  | zero => rfl
  | succ k ih =>
    rw [rolloutRat, ih]
    exact fullTurnRat_reflective_conserves spec negVars dims hDims2 useStrang c hcVar hcNotNeg
      hOdd hSrc G

/-! ## 5. The trajectory statement and its 256-bit commitment -/

/-- What a receipt commits to: the law as written, the grid, the boundary, the schedule, and the
two ends of the trajectory. -/
structure PdeTrajectoryStatement where
  specName : String
  law : String
  dims : List Nat
  boundaryTag : String
  reflectNegVars : List Nat
  steps : Nat
  backend : String
  useStrang : Bool
  initialRat : List (List Rat)
  finalRat : List (List Rat)

def strBytes (s : String) : List UInt8 := s.toByteArray.data.toList

private theorem strBytes_injective {s₁ s₂ : String} (h : strBytes s₁ = strBytes s₂) : s₁ = s₂ := by
  cases s₁ with
  | ofByteArray b₁ v₁ =>
    cases s₂ with
    | ofByteArray b₂ v₂ =>
      cases b₁ with
      | mk a₁ =>
        cases b₂ with
        | mk a₂ =>
          cases a₁ with
          | mk l₁ =>
            cases a₂ with
            | mk l₂ =>
              change l₁ = l₂ at h
              subst h
              rfl

/-- Zigzag, then LEB128. -/
def intBytes (z : Int) : List UInt8 :=
  leb128 (if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1)

private theorem intBytes_injective {a b : Int} (h : intBytes a = intBytes b) : a = b := by
  have h := leb128_injective h
  split at h <;> split at h <;> omega

def ratBytes (q : Rat) : List UInt8 := encodeFields [intBytes q.num, leb128 q.den]

private theorem ratBytes_injective {p q : Rat} (h : ratBytes p = ratBytes q) : p = q := by
  have h := encodeFields_injective _ _ h
  simp only [List.cons.injEq, and_true] at h
  exact Rat.ext (intBytes_injective h.1) (leb128_injective h.2)

def listBytes {α : Type} (e : α → List UInt8) (xs : List α) : List UInt8 :=
  encodeFields (xs.map e)

private theorem map_injective {α β : Type} {e : α → β} (he : ∀ a b, e a = e b → a = b) :
    ∀ {xs ys : List α}, xs.map e = ys.map e → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [he _ _ h.1, map_injective he h.2]

private theorem listBytes_injective {α : Type} {e : α → List UInt8}
    (he : ∀ a b, e a = e b → a = b) {xs ys : List α} (h : listBytes e xs = listBytes e ys) :
    xs = ys :=
  map_injective he (encodeFields_injective _ _ h)

/-- Every field length-framed, under a domain tag. -/
def pdeTrajectoryBytes (s : PdeTrajectoryStatement) : List UInt8 :=
  encodeFields [strBytes "obend.pde.trajectory/v1", strBytes s.specName, strBytes s.law,
    listBytes leb128 s.dims, strBytes s.boundaryTag, listBytes leb128 s.reflectNegVars,
    leb128 s.steps, strBytes s.backend, leb128 (if s.useStrang then 1 else 0),
    listBytes (listBytes ratBytes) s.initialRat, listBytes (listBytes ratBytes) s.finalRat]

theorem pdeTrajectoryBytes_injective {s₁ s₂ : PdeTrajectoryStatement}
    (h : pdeTrajectoryBytes s₁ = pdeTrajectoryBytes s₂) : s₁ = s₂ := by
  have h := encodeFields_injective _ _ h
  cases s₁ with
  | mk n₁ l₁ d₁ b₁ r₁ k₁ e₁ u₁ i₁ f₁ =>
  cases s₂ with
  | mk n₂ l₂ d₂ b₂ r₂ k₂ e₂ u₂ i₂ f₂ =>
  simp only [List.cons.injEq, and_true, true_and] at h
  obtain ⟨hn, hl, hd, hb, hr, hk, he, hu, hi, hf⟩ := h
  have hu' : u₁ = u₂ := by
    have hu := leb128_injective hu
    cases u₁ <;> cases u₂ <;> simp_all
  have hNat : ∀ a b : Nat, leb128 a = leb128 b → a = b := fun _ _ h => leb128_injective h
  have hRow : ∀ a b : List Rat, listBytes ratBytes a = listBytes ratBytes b → a = b :=
    fun _ _ h => listBytes_injective (fun _ _ h => ratBytes_injective h) h
  rw [strBytes_injective hn, strBytes_injective hl, listBytes_injective hNat hd,
    strBytes_injective hb, listBytes_injective hNat hr, leb128_injective hk,
    strBytes_injective he, hu', listBytes_injective hRow hi, listBytes_injective hRow hf]

def pdeTrajectoryDigest (H : Hash) (s : PdeTrajectoryStatement) : List UInt8 :=
  H (pdeTrajectoryBytes s)

/-- **The digest binds the statement**: two statements with one digest are equal, or their two
preimages, the only inputs hashed, are distinct and collide under `H`. -/
theorem pdeTrajectoryDigest_binding (H : Hash) (s₁ s₂ : PdeTrajectoryStatement)
    (h : pdeTrajectoryDigest H s₁ = pdeTrajectoryDigest H s₂) :
    s₁ = s₂ ∨ CollisionAmong H (fun x => x = pdeTrajectoryBytes s₁ ∨ x = pdeTrajectoryBytes s₂) :=
  if hb : pdeTrajectoryBytes s₁ = pdeTrajectoryBytes s₂ then .inl (pdeTrajectoryBytes_injective hb)
  else .inr ⟨_, _, .inl rfl, .inr rfl, hb, congrArg ofBE h⟩

/-- The receipt: the deployed 256-bit digest of the statement, as 64 hex digits. -/
def pdeReceiptHex (s : PdeTrajectoryStatement) : String :=
  Obend.Codec.Hex.bytesToHex (pdeTrajectoryDigest Obend.Core.Digest.deployed s)

/-! ## 6. The Q32.32 backend -/

abbrev Q32Grid := Array (Array (BitVec 64))

def q32OfRat (g : List (List Rat)) : Q32Grid :=
  (g.map fun row => (row.map fun q => (ratToQ32Checked q).getD 0#64).toArray).toArray

def q32Rats (G : Q32Grid) : List (List Rat) :=
  (G.map fun row => (row.map fun w => (w.toInt : Rat) / 4294967296).toList).toList

def q32Representable (g : List (List Rat)) : Bool :=
  g.all fun row => row.all fun q => (ratToQ32Checked q).isSome

/-- One directional sweep of `evalNonlinearFluxCellQ32` over the policy's ghost cells. -/
def sweepQ32 (spec : ConservationLawSpec) (pol : PdeBoundaryPolicy) (dims : List Nat)
    (G : Q32Grid) (step : Nat × Rat) : Q32Grid :=
  if step.1 < dims.length then
    let dag := compileFluxSsaDag (some spec.paramEnv) (getOr spec.fluxes step.1 [])
    let scaled := { spec with cfl := step.2 }
    let negs := pol.negVars
    Array.ofFn (n := gridCellCount dims) fun idx =>
      (evalNonlinearFluxCellQ32 scaled dag fun off c =>
        let g := ghostIndex pol dims step.1 idx.val off
        let w := ((G[g.1]?).getD #[])[c]?.getD 0#64
        if g.2 && negs.contains c then -w else w).toArray
  else G

def sourceStepQ32 (spec : ConservationLawSpec) (dims : List Nat) (dt : Rat) (G : Q32Grid) :
    Q32Grid :=
  if spec.sources.isEmpty then G
  else
    let dag := compileFluxSsaDag (some spec.paramEnv) spec.sources
    let dtW := (ratToQ32Checked dt).getD 0#64
    Array.ofFn (n := gridCellCount dims) fun idx =>
      let uIn : Nat → BitVec 64 := fun c => ((G[idx.val]?).getD #[])[c]?.getD 0#64
      let sOut := evalFluxSsaDagQ32 uIn spec.paramEnv dag
      Array.ofFn (n := spec.numVars) fun c =>
        uIn c.val + Obend.Hardware.HDL.evalAluOp .qmul32 dtW (sOut.getD c.val 0#64)

def turnQ32 (spec : ConservationLawSpec) (pol : PdeBoundaryPolicy) (dims : List Nat)
    (useStrang : Bool) (G : Q32Grid) : Q32Grid :=
  if spec.sources.isEmpty then
    (sweepSchedule dims spec.cfl useStrang).foldl (sweepQ32 spec pol dims) G
  else if useStrang then
    let g1 := sourceStepQ32 spec dims (spec.cfl / 2) G
    let g2 := (sweepSchedule dims spec.cfl true).foldl (sweepQ32 spec pol dims) g1
    sourceStepQ32 spec dims (spec.cfl / 2) g2
  else
    let g1 := (sweepSchedule dims spec.cfl false).foldl (sweepQ32 spec pol dims) G
    sourceStepQ32 spec dims spec.cfl g1

private def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => iter f k (f a)

private def trace {α : Type} (f : α → α) : Nat → α → List α
  | 0, a => [a]
  | k + 1, a => a :: trace f k (f a)

/-! ## 7. JSON, `solve` and `check` -/

def rat (j : Json) : Except String Rat := do
  if let .ok n := j.getInt? then return n
  let n ← j.getObjValAs? Int "num"
  let d ← j.getObjValAs? Nat "den"
  if d == 0 then throw "zero rational denominator"
  return (n : Rat) / (d : Rat)

def ratJson (q : Rat) : Json := Json.mkObj [("num", toJson q.num), ("den", toJson q.den)]

private def matrix (j : Json) : Except String (List (List Rat)) := do
  (← j.getArr?).toList.mapM fun r => do (← r.getArr?).toList.mapM rat

private def matrixJson (m : List (List Rat)) : Json :=
  .arr (m.toArray.map fun r => .arr (r.toArray.map ratJson))

private def optional {α : Type} (j : Json) (k : String) (dec : Json → Except String α) :
    Except String (Option α) :=
  match j.getObjVal? k with
  | .ok v => some <$> dec v
  | .error _ => pure none

/-- A malformed request (exit 2), or a refusal with its exit code, stage and reason. -/
inductive PdeFail where
  | decode (msg : String)
  | refuse (code : UInt32) (stage reason : String)

private def dec {α : Type} (e : Except String α) : Except PdeFail α := e.mapError .decode

private def refuse {α : Type} (code : UInt32) (stage reason : String) : Except PdeFail α :=
  throw (.refuse code stage reason)

structure PdeProblem where
  spec : ConservationLawSpec
  law : String
  dims : List Nat
  steps : Nat
  q32 : Bool
  policy : PdeBoundaryPolicy
  useStrang : Bool
  initial : List (List Rat)

namespace PdeProblem

def shapeOk (p : PdeProblem) (g : List (List Rat)) : Bool :=
  g.length == gridCellCount p.dims && g.all (·.length == p.spec.numVars)

def statement (p : PdeProblem) (final : List (List Rat)) : PdeTrajectoryStatement :=
  { specName := p.spec.name, law := p.law, dims := p.dims, boundaryTag := p.policy.tag
    reflectNegVars := p.policy.negVars, steps := p.steps
    backend := if p.q32 then "q32" else "rat", useStrang := p.useStrang
    initialRat := p.initial, finalRat := final }

def ratTurn (p : PdeProblem) (g : List (List Rat)) : List (List Rat) :=
  ((turnRat p.spec p.policy p.dims p.useStrang ((g.map List.toArray).toArray)).map Array.toList).toList

def ratFinal (p : PdeProblem) : List (List Rat) :=
  ((rolloutRat p.spec p.policy p.dims p.useStrang p.steps
    ((p.initial.map List.toArray).toArray)).map Array.toList).toList

def q32Final (p : PdeProblem) : List (List Rat) :=
  q32Rats (iter (turnQ32 p.spec p.policy p.dims p.useStrang) p.steps (q32OfRat p.initial))

def exactFinal (p : PdeProblem) : List (List Rat) := if p.q32 then p.q32Final else p.ratFinal

/-- The `steps + 1` grids of the chosen backend. -/
def exactTrace (p : PdeProblem) : List (List (List Rat)) :=
  if p.q32 then
    (trace (turnQ32 p.spec p.policy p.dims p.useStrang) p.steps (q32OfRat p.initial)).map q32Rats
  else trace p.ratTurn p.steps p.initial

def integrals (p : PdeProblem) (g : List (List Rat)) : List Rat :=
  (List.range p.spec.numVars).map
    (totalGridIntegral p.dims (gridFn ((g.map List.toArray).toArray)))

end PdeProblem

private def ratMax (a b : Rat) : Rat := if a ≤ b then b else a

private def gridMaxDiff (a b : List (List Rat)) : Rat :=
  (a.zip b).foldl (fun m rs =>
    (rs.1.zip rs.2).foldl (fun m xy => ratMax m (ratAbs (xy.1 - xy.2))) m) 0

/-- The declared tube: `t ↦ L * t + ‖u_{k+1} - step u_k‖` along the trajectory. -/
private def surrogateTube (p : PdeProblem) (L : Rat) : Rat → List (List (List Rat)) → Rat
  | t, a :: b :: rest => surrogateTube p L (L * t + gridMaxDiff b (p.ratTurn a)) (b :: rest)
  | t, _ => t

def pdeProblem (j : Json) : Except PdeFail PdeProblem := do
  let (spec, law) ← match ← dec (optional j "solver" Json.getStr?),
      ← dec (optional j "sexpr" Json.getStr?) with
    | some name, none =>
      match Obend.Hardware.PdeSolvers.lookupCanonicalPdeSolver name with
      | some spec => pure (spec, s!"catalog:{name}")
      | none => refuse 1 "lookup-pde-solver" s!"unknown canonical PDE solver `{name}`"
    | none, some law =>
      match Obend.Elab.PdeSolverElab.validatePdeSolverSexpr law with
      | .ok (spec, _) => pure (spec, law)
      | .error msg => refuse 1 "validate-pde-sexpr" msg
    | some _, some _ => throw (.decode "provide either `solver` or `sexpr`, not both")
    | none, none => throw (.decode "expected `solver` or `sexpr`")
  let dims ← dec (j.getObjValAs? (List Nat) "dims")
  let steps ← dec (j.getObjValAs? Nat "steps")
  let backend := (← dec (optional j "backend" Json.getStr?)).getD "rat"
  let boundary := (← dec (optional j "boundary" Json.getStr?)).getD "periodic"
  let negs := (← dec (optional j "reflectNegVars" fun v => Lean.fromJson? (α := List Nat) v)).getD []
  let useStrang := (← dec (optional j "strang" Json.getBool?)).getD false
  let initial ← dec (j.getObjVal? "initial" >>= matrix)
  if dims.isEmpty || dims.any (· == 0) || dims.length != spec.numDims then
    refuse 3 "shape" "dims must be non-empty, positive, and one per coordinate"
  if gridCellCount dims > 4096 then refuse 3 "limits" "more than 4096 cells"
  if steps > 2000 then refuse 3 "limits" "more than 2000 steps"
  if backend != "rat" && backend != "q32" then refuse 3 "backend" "backend must be rat or q32"
  let policy ← match boundary with
    | "periodic" => pure PdeBoundaryPolicy.periodic
    | "transmissive" => pure PdeBoundaryPolicy.transmissive
    | "reflective" => pure (PdeBoundaryPolicy.reflective negs)
    | _ => refuse 3 "boundary" "boundary must be periodic, transmissive or reflective"
  if negs.any (· ≥ spec.numVars) then refuse 3 "boundary" "reflectNegVars names no state variable"
  let p : PdeProblem := { spec, law, dims, steps, q32 := backend == "q32", policy, useStrang, initial }
  if !p.shapeOk initial then refuse 3 "shape" "initial must hold one row of state per cell"
  if p.q32 && !q32Representable initial then
    refuse 3 "q32-range" "an initial value is outside the Q32.32 guard-bit range"
  return p

def pdeSolve (p : PdeProblem) (j : Json) : Except PdeFail Json := do
  let record := (← dec (optional j "recordTrajectory" Json.getBool?)).getD false
  let compare := (← dec (optional j "compareQ32" Json.getBool?)).getD false
  if compare && !q32Representable p.initial then
    refuse 3 "q32-range" "an initial value is outside the Q32.32 guard-bit range"
  let trajectory := if record then some p.exactTrace else none
  let final := match trajectory with
    | some t => t.getLastD []
    | none => p.exactFinal
  let start := if p.q32 then q32Rats (q32OfRat p.initial) else p.initial
  let i0 := p.integrals start
  let i1 := p.integrals final
  let drift := (i0.zip i1).foldl (fun m ab => ratMax m (ratAbs (ab.2 - ab.1))) 0
  let mut out := j.setObjVal! "status" (toJson "accepted") |>.setObjVal! "ok" (toJson true)
    |>.setObjVal! "final" (matrixJson final)
    |>.setObjVal! "initialIntegrals" (.arr (i0.toArray.map ratJson))
    |>.setObjVal! "finalIntegrals" (.arr (i1.toArray.map ratJson))
    |>.setObjVal! "maxIntegralDrift" (ratJson drift)
    |>.setObjVal! "receiptHex" (toJson (pdeReceiptHex (p.statement final)))
  if let some t := trajectory then
    out := out.setObjVal! "trajectory" (.arr (t.toArray.map matrixJson))
  if compare || p.q32 then
    let other := if p.q32 then p.ratFinal else p.q32Final
    out := out.setObjVal! "q32VsRatMaxDiff" (ratJson (gridMaxDiff final other))
  return out

def pdeCheck (p : PdeProblem) (j : Json) : Except PdeFail (Bool × Json) := do
  let trajectory ← dec (optional j "trajectory" fun v => do (← v.getArr?).toList.mapM matrix)
  let finalField ← dec (optional j "final" matrix)
  let final ← match trajectory, finalField with
    | some t, some f =>
      if t.getLast? != some f then refuse 3 "trajectory" "final is not the last trajectory grid"
      else pure f
    | some t, none => pure (t.getLastD [])
    | none, some f => pure f
    | none, none => throw (.decode "expected `trajectory` or `final`")
  if !p.shapeOk final then refuse 3 "shape" "final must hold one row of state per cell"
  if let some t := trajectory then
    if t.length != p.steps + 1 || !t.all p.shapeOk then
      refuse 3 "shape" "trajectory must hold steps + 1 grids of the initial shape"
  if let some h ← dec (optional j "receiptHex" Json.getStr?) then
    if h != pdeReceiptHex (p.statement final) then
      refuse 3 "receipt" "receiptHex does not commit to this statement"
  let verdict := fun (ok : Bool) (reason : String) => Json.mkObj
    [("ok", toJson ok), ("status", toJson (if ok then "accepted" else "refused")), ("reason", toJson reason)]
  match ← dec (optional j "tolerance" rat) with
  | none =>
    let ok := match trajectory with
      | some t => t == p.exactTrace
      | none => final == p.exactFinal
    return (ok, verdict ok "exact nonlinear rollout residual")
  | some tolerance =>
    let some t := trajectory | refuse 3 "trajectory" "a tolerance needs the whole trajectory"
    let L := (← dec (optional j "amplification" rat)).getD 1
    let tube := surrogateTube p L (gridMaxDiff (t.headD []) p.initial) t
    let actual := gridMaxDiff final p.ratFinal
    let ok := decide (tube ≤ tolerance) && decide (actual ≤ tolerance)
    return (ok, (verdict ok "surrogate defect tube").setObjVal! "tube" (ratJson tube)
      |>.setObjVal! "actualFinalError" (ratJson actual))

/-- The pure adapter: `.error` is a malformed request, otherwise an exit code and its JSON. -/
def pdeNonlinear (solve : Bool) (j : Json) : Except String (UInt32 × Json) :=
  let run : Except PdeFail (UInt32 × Json) := do
    let p ← pdeProblem j
    if solve then return (0, ← pdeSolve p j)
    let (ok, out) ← pdeCheck p j
    return (if ok then 0 else 3, out)
  match run with
  | .ok r => .ok r
  | .error (.decode msg) => .error msg
  | .error (.refuse code stage reason) => .ok (code, Json.mkObj
      [("ok", toJson false), ("status", toJson "refused"), ("stage", toJson stage), ("reason", toJson reason)])

private def decodeIO {α : Type} (e : Except String α) : IO α :=
  match e with | .ok a => pure a | .error e => throw (IO.userError e)

private def output (args : List String) (j : Json) : IO Unit := do
  match args with
  | [] => IO.println j.compress
  | ["--out", p] => IO.FS.writeFile p (j.compress ++ "\n")
  | _ => throw (IO.userError "expected [--out FILE]")

private def finish (args : List String) (ok : Bool) (j : Json) : IO UInt32 := do
  output args j
  if !ok then IO.eprintln "refused: verification failed"
  return if ok then 0 else 3

private def takeOpt (flag : String) : List String → Option String × List String
  | f :: rest => match f == flag, rest with
    | true, v :: tail => (some v, tail)
    | _, _ => let (o, r) := takeOpt flag rest; (o, f :: r)
  | [] => (none, [])

/-- The linear formats: exact Rusanov trajectories and the a posteriori defect tube. -/
private def linearPde (solve : Bool) (fmt : String) (j : Json) (args : List String) : IO UInt32 := do
  let verdict := fun (ok : Bool) (reason : String) => Json.mkObj
    [("status", toJson (if ok then "accepted" else "refused")), ("reason", toJson reason)]
  if fmt != "hyperbolic-fvm@1" && fmt != "pde-approx-defect@1" then throw (IO.userError "unknown PDE format")
  let o ← decodeIO (j.getObjVal? "system" >>= fun x => decodeHyperbolicFvmObj x.compress)
  let c ← decodeIO (j.getObjVal? "certificate" >>= fun x => decodeHyperbolicFvmCert x.compress)
  if check o c != .ok then return ← finish args false (verdict false "geometry/CFL/conservation")
  let initial ← decodeIO (j.getObjVal? "initial" >>= matrix)
  let steps ← decodeIO (j.getObjValAs? Nat "steps")
  if steps > 10000 || initial.isEmpty || initial.any (fun r => r.length != o.dim) then
    return ← finish args false (verdict false "grid shape or step limit")
  let exact := fun k => (List.range initial.length).map fun i => (List.range o.dim).map fun d =>
    rusanovRun o.dim o.jacobian o.aMax o.cfl initial.length k (listGrid initial) i d
  if solve then
    let trajectory := (List.range (steps + 1)).map exact
    let out := j.setObjVal! "trajectory" (.arr (trajectory.toArray.map matrixJson))
    return ← finish args true (out.setObjVal! "status" (toJson "accepted"))
  let trajectory ← decodeIO (do (← (← j.getObjVal? "trajectory").getArr?).toList.mapM matrix)
  if fmt == "hyperbolic-fvm@1" then
    let ok := trajectory == (List.range (steps + 1)).map exact
    finish args ok (verdict ok "exact Rusanov trajectory residual")
  else
    let eta ← decodeIO (j.getObjVal? "eta" >>= rat)
    let tolerance ← decodeIO (j.getObjVal? "tolerance" >>= rat)
    let q : ApproxQuery := ⟨o, c, initial.length, steps, eta, tolerance, initial, trajectory⟩
    let ok := checkApprox q == .ok
    finish args ok ((verdict ok "a posteriori defect tube").setObjVal! "tube" (ratJson q.tube))

/-- The axis-0 artifacts of an accepted solve: the WGSL array kernel, the systolic flux cell, and
its Yosys equivalence query. -/
private def emitArtifacts (p : PdeProblem) (wgsl sv lec : Option String) : IO Unit := do
  let rtl := Obend.Tactic.SymDiffAndFlux.buildSpecSystolicRtl p.spec 0
  if let some dir := wgsl then
    let boundary ← match p.policy with
      | .periodic => pure StencilBoundary.periodic
      | .transmissive => pure StencilBoundary.clamp
      | .reflective _ => throw (IO.userError
          "--emit-wgsl: the array kernel gathers periodic or clamped cells only, not mirrored ones")
    let plan ← IO.ofExcept (Obend.Hardware.Gpu.ArrayPrograms.compileSource p.spec.name
      (List.replicate p.spec.numVars (gridCellCount p.dims))
      (compileMultiDNonlinearFluxSweepSource p.spec boundary p.dims 0))
    let _ ← Obend.Hardware.Gpu.ArrayEmit.write p.spec.name plan.lower dir
  if let some file := sv then IO.FS.writeFile file (Obend.Hardware.HDL.emitModuleSV rtl)
  if let some file := lec then
    IO.FS.writeFile file (Obend.Hardware.YosysLec.emitYosysLecSmt2 rtl)

/-- `obend pde check|solve INPUT [--out FILE] [--emit-wgsl DIR] [--emit-sv FILE] [--emit-lec FILE]`. -/
def runPdeCli (solve : Bool) (j : Json) (args : List String) : IO UInt32 := do
  let fmt ← decodeIO (j.getObjValAs? String "format")
  if fmt != "nonlinear-conservation@1" then return ← linearPde solve fmt j args
  let (wgsl, args) := takeOpt "--emit-wgsl" args
  let (sv, args) := takeOpt "--emit-sv" args
  let (lec, args) := takeOpt "--emit-lec" args
  if !solve && (wgsl.isSome || sv.isSome || lec.isSome) then
    throw (IO.userError "the --emit flags belong to `pde solve`")
  let (code, out) ← decodeIO (pdeNonlinear solve j)
  if code == 0 && solve then
    match pdeProblem j with
    | .ok p => emitArtifacts p wgsl sv lec
    | .error _ => pure ()
  output args out
  if code != 0 then IO.eprintln "refused: verification failed"
  return code

end Obend.Analysis.NonlinearPdeCli
