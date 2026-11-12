module
/-
# Obend.Category.OpenSystem — Port-Hamiltonian & dissipative open systems composition

Discrete-time dissipative / passive open systems (`OpenDissipativeSys State PortIn PortOut`)
and compositional interconnection laws:

- `OpenDissipativeSys`: storage function `energy : State → Int` (`0 ≤ energy s`), port supply
  rate `supply : PortIn → PortOut → Int`, causal dynamics `step : State → PortIn → State × PortOut`,
  and discrete passivity inequality `energy s' - energy s ≤ supply u y`.
- `energy_bounded_along_trajectory`: universal global Lyapunov energy bound across arbitrary-length
  input trajectories (`0 ≤ energy s_T ≤ energy s_0 + trajectorySupply`), proved once for all
  `OpenDissipativeSys` instances so interconnected plants require zero per-system re-proving.
- `parallelCompose`: additive storage `H₁ + H₂` and additive supply `w₁ + w₂` over decoupled ports.
- `feedbackInterconnect`: general power-conserving / lossless or dissipative junction
  (`supply₁ u₁ y₁ + supply₂ u₂ y₂ ≤ supplyExt uExt yExt`) yielding a certified `OpenDissipativeSys`.
- `skewFeedbackInterconnect`: concrete standard negative-feedback gyrator junction
  (`u₁ = e₁ - k * y₂`, `u₂ = e₂ + k * y₁`) for Port-Hamiltonian systems with state-readout effort
  ports (`yᵢ = portOutᵢ sᵢ`), where internal cross-power `-k * y₂ * y₁ + k * y₁ * y₂ = 0` cancels
  identically.
-/
public section
namespace Obend.Category
set_option autoImplicit false

/-! ## 1. Discrete-Time Dissipative Open Systems -/

/-- A certified discrete-time dissipative open system with non-negative storage `energy`
    and supply rate `supply`. -/
structure OpenDissipativeSys (State PortIn PortOut : Type) where
  energy : State → Int
  energy_nonneg : ∀ s : State, 0 ≤ energy s
  supply : PortIn → PortOut → Int
  step : State → PortIn → State × PortOut
  dissipative : ∀ (s : State) (u : PortIn),
    energy (step s u).1 - energy s ≤ supply u (step s u).2

namespace OpenDissipativeSys

/-- Run an open system from `s` across a finite sequence of port inputs `us`, returning the
    terminal state. -/
@[expose] def runTrajectory {State PortIn PortOut : Type}
    (sys : OpenDissipativeSys State PortIn PortOut) : State → List PortIn → State
  | s, [] => s
  | s, u :: us => runTrajectory sys (sys.step s u).1 us

/-- Cumulative external supply injected along the trajectory starting at `s` under inputs `us`. -/
@[expose] def trajectorySupply {State PortIn PortOut : Type}
    (sys : OpenDissipativeSys State PortIn PortOut) : State → List PortIn → Int
  | _, [] => 0
  | s, u :: us =>
      sys.supply u (sys.step s u).2 + trajectorySupply sys (sys.step s u).1 us

/-- **Global Passivity & Lyapunov Bound Along Arbitrary Trajectories.**
    Terminal stored energy is non-negative and bounded above by initial stored energy plus
    cumulative external port supply. -/
theorem energy_bounded_along_trajectory {State PortIn PortOut : Type}
    (sys : OpenDissipativeSys State PortIn PortOut) (s₀ : State) (us : List PortIn) :
    0 ≤ sys.energy (sys.runTrajectory s₀ us) ∧
      sys.energy (sys.runTrajectory s₀ us) ≤ sys.energy s₀ + sys.trajectorySupply s₀ us := by
  refine ⟨sys.energy_nonneg (sys.runTrajectory s₀ us), ?_⟩
  induction us generalizing s₀ with
  | nil =>
    simp [runTrajectory, trajectorySupply]
  | cons u rest ih =>
    simp only [runTrajectory, trajectorySupply]
    have hstep := sys.dissipative s₀ u
    have hrest := ih (sys.step s₀ u).1
    omega

/-- When external supply is non-positive along every step (e.g. autonomous / zero-input or resistive
    boundary termination), `sys.energy` is a global non-increasing Lyapunov function. -/
theorem autonomous_lyapunov_nonincreasing {State PortIn PortOut : Type}
    (sys : OpenDissipativeSys State PortIn PortOut) (s₀ : State) (us : List PortIn)
    (hPassiveBoundary : ∀ (s : State) (u : PortIn), u ∈ us → sys.supply u (sys.step s u).2 ≤ 0) :
    0 ≤ sys.energy (sys.runTrajectory s₀ us) ∧
      sys.energy (sys.runTrajectory s₀ us) ≤ sys.energy s₀ := by
  refine ⟨sys.energy_nonneg _, ?_⟩
  induction us generalizing s₀ with
  | nil =>
    simp [runTrajectory]
  | cons u rest ih =>
    simp only [runTrajectory]
    have hu : sys.supply u (sys.step s₀ u).2 ≤ 0 :=
      hPassiveBoundary s₀ u List.mem_cons_self
    have hstep := sys.dissipative s₀ u
    have hrest := ih (sys.step s₀ u).1 (fun s v hv =>
      hPassiveBoundary s v (List.mem_cons_of_mem u hv))
    omega

/-! ## 2. Parallel Composition (`H = H₁ + H₂`) -/

/-- Parallel composition of two open dissipative systems with total storage `H₁ + H₂` and
    total supply `w₁ + w₂`. -/
@[expose] def parallelCompose {S₁ U₁ Y₁ S₂ U₂ Y₂ : Type}
    (sys₁ : OpenDissipativeSys S₁ U₁ Y₁)
    (sys₂ : OpenDissipativeSys S₂ U₂ Y₂) :
    OpenDissipativeSys (S₁ × S₂) (U₁ × U₂) (Y₁ × Y₂) where
  energy s := sys₁.energy s.1 + sys₂.energy s.2
  energy_nonneg s := Int.add_nonneg (sys₁.energy_nonneg s.1) (sys₂.energy_nonneg s.2)
  supply u y := sys₁.supply u.1 y.1 + sys₂.supply u.2 y.2
  step s u :=
    let r₁ := sys₁.step s.1 u.1
    let r₂ := sys₂.step s.2 u.2
    ((r₁.1, r₂.1), (r₁.2, r₂.2))
  dissipative s u := by
    have h₁ := sys₁.dissipative s.1 u.1
    have h₂ := sys₂.dissipative s.2 u.2
    dsimp only
    omega

/-! ## 3. Power-Conserving & Skew-Symmetric Feedback Interconnection -/

/-- A causal interconnection junction coupling `sys₁` and `sys₂` to external ports
    `(ExtIn, ExtOut)` whose internal routing neither creates nor amplifies net power:
    `supply₁ u₁ y₁ + supply₂ u₂ y₂ ≤ supplyExt uExt yExt`. -/
structure PassiveJunction {S₁ U₁ Y₁ S₂ U₂ Y₂ : Type}
    (sys₁ : OpenDissipativeSys S₁ U₁ Y₁)
    (sys₂ : OpenDissipativeSys S₂ U₂ Y₂)
    (ExtIn ExtOut : Type) where
  resolveInputs : S₁ → S₂ → ExtIn → U₁ × U₂
  mergeOutputs : ExtIn → Y₁ → Y₂ → ExtOut
  supplyExt : ExtIn → ExtOut → Int
  power_conserving : ∀ (s₁ : S₁) (s₂ : S₂) (uExt : ExtIn),
    let u₁ := (resolveInputs s₁ s₂ uExt).1
    let u₂ := (resolveInputs s₁ s₂ uExt).2
    let y₁ := (sys₁.step s₁ u₁).2
    let y₂ := (sys₂.step s₂ u₂).2
    sys₁.supply u₁ y₁ + sys₂.supply u₂ y₂ ≤ supplyExt uExt (mergeOutputs uExt y₁ y₂)

/-- Interconnect `sys₁` and `sys₂` across any `PassiveJunction`, automatically producing a
    certified `OpenDissipativeSys` with storage `H₁ + H₂` (and hence an immediate global
    trajectory Lyapunov bound via `energy_bounded_along_trajectory`). -/
@[expose] def feedbackInterconnect {S₁ U₁ Y₁ S₂ U₂ Y₂ ExtIn ExtOut : Type}
    (sys₁ : OpenDissipativeSys S₁ U₁ Y₁)
    (sys₂ : OpenDissipativeSys S₂ U₂ Y₂)
    (J : PassiveJunction sys₁ sys₂ ExtIn ExtOut) :
    OpenDissipativeSys (S₁ × S₂) ExtIn ExtOut where
  energy s := sys₁.energy s.1 + sys₂.energy s.2
  energy_nonneg s := Int.add_nonneg (sys₁.energy_nonneg s.1) (sys₂.energy_nonneg s.2)
  supply := J.supplyExt
  step s uExt :=
    let u₁ := (J.resolveInputs s.1 s.2 uExt).1
    let u₂ := (J.resolveInputs s.1 s.2 uExt).2
    let r₁ := sys₁.step s.1 u₁
    let r₂ := sys₂.step s.2 u₂
    ((r₁.1, r₂.1), J.mergeOutputs uExt r₁.2 r₂.2)
  dissipative s uExt := by
    have hp := J.power_conserving s.1 s.2 uExt
    have h₁ := sys₁.dissipative s.1 (J.resolveInputs s.1 s.2 uExt).1
    have h₂ := sys₂.dissipative s.2 (J.resolveInputs s.1 s.2 uExt).2
    dsimp only at hp ⊢
    omega

/-- Exact skew-symmetric gyrator power cancellation identity:
    `(e₁ - k * y₂) * y₁ + (e₂ + k * y₁) * y₂ = e₁ * y₁ + e₂ * y₂`. -/
theorem skew_gyrator_power_cancels (k e₁ e₂ y₁ y₂ : Int) :
    (e₁ - k * y₂) * y₁ + (e₂ + k * y₁) * y₂ = e₁ * y₁ + e₂ * y₂ := by
  rw [Int.sub_mul, Int.add_mul]
  have hcomm : (k * y₂) * y₁ = (k * y₁) * y₂ := by
    rw [Int.mul_assoc, Int.mul_comm y₂ y₁, ← Int.mul_assoc]
  omega

/-- A Port-Hamiltonian state-output subsystem with scalar `Int` effort/flow ports and bilinear
    port power `u * y`, where port readout `portOut s` depends causally on state `s`. -/
structure StatePortHamiltonianSys (State : Type) where
  energy : State → Int
  energy_nonneg : ∀ s : State, 0 ≤ energy s
  portOut : State → Int
  nextState : State → Int → State
  dissipative : ∀ (s : State) (u : Int),
    energy (nextState s u) - energy s ≤ u * portOut s

/-- View a `StatePortHamiltonianSys` as an `OpenDissipativeSys State Int Int`. -/
@[expose] def StatePortHamiltonianSys.toOpenSys {State : Type}
    (P : StatePortHamiltonianSys State) : OpenDissipativeSys State Int Int where
  energy := P.energy
  energy_nonneg := P.energy_nonneg
  supply u y := u * y
  step s u := (P.nextState s u, P.portOut s)
  dissipative := P.dissipative

/-- Standard skew-symmetric negative-feedback interconnection (`u₁ = e₁ - k * y₂`,
    `u₂ = e₂ + k * y₁`) of two Port-Hamiltonian systems with coupling gain `k : Int`:
    internal gyrator power cancels identically, yielding a certified `OpenDissipativeSys`
    with zero user proof obligations. -/
@[expose] def skewFeedbackInterconnect {S₁ S₂ : Type}
    (P₁ : StatePortHamiltonianSys S₁)
    (P₂ : StatePortHamiltonianSys S₂)
    (k : Int) :
    OpenDissipativeSys (S₁ × S₂) (Int × Int) (Int × Int) :=
  feedbackInterconnect P₁.toOpenSys P₂.toOpenSys
    { resolveInputs := fun s₁ s₂ ⟨e₁, e₂⟩ =>
        (e₁ - k * P₂.portOut s₂, e₂ + k * P₁.portOut s₁)
      mergeOutputs := fun _ y₁ y₂ => (y₁, y₂)
      supplyExt := fun ⟨e₁, e₂⟩ ⟨y₁, y₂⟩ => e₁ * y₁ + e₂ * y₂
      power_conserving := fun s₁ s₂ ⟨e₁, e₂⟩ => by
        dsimp only [StatePortHamiltonianSys.toOpenSys]
        rw [skew_gyrator_power_cancels k e₁ e₂ (P₁.portOut s₁) (P₂.portOut s₂)]
        exact Int.le_refl _ }

end OpenDissipativeSys

end Obend.Category
end
