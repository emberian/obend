module
/-
# Obend.Hardware.Kinematics — Featherstone 6D Spatial Vector Algebra ($\mathfrak{se}(3) / \mathfrak{se}(3)^*$), Ruckig 3rd-Order Jerk-Limited Trajectory Generation & 5-Axis CNC Abbe Volumetric Error Compensation

Formalizes the mathematical and physical foundations of **articulated multi-axis robotics, 5-axis CNC
machine-tool kinematics, and jerk-limited trajectory generation** within `Obend.Hardware`, grounded in:

* **Roy Featherstone's 6D Spatial Vector Algebra & Differentiable Articulated Body Dynamics**
  (Qiao et al., *Efficient Differentiable Simulation of Articulated Bodies*, ICML 2021, `arXiv:2109.07719`;
  Singh, Russell & Wensing, `arXiv:2203.01497`; Opitz et al., `arXiv:2105.05102`; Werling et al., `arXiv:2103.16021`):
  - Models 6D Plücker motion twists $v = (\boldsymbol{\omega}, \mathbf{v}) \in \mathfrak{se}(3)$ (`SpatialTwist6D`)
    and 6D force wrenches $f = (\boldsymbol{\tau}, \mathbf{f}) \in \mathfrak{se}(3)^*$ (`SpatialWrench6D`),
  - Defines the virtual power pairing $\langle f, v \rangle = \boldsymbol{\tau} \cdot \boldsymbol{\omega} + \mathbf{f} \cdot \mathbf{v}$,
    the spatial Lie bracket $u \times_m v = \operatorname{ad}_u(v)$, and the spatial coadjoint force cross-product
    $u \times_f f = \operatorname{ad}_u^*(f)$,
  - Proves **`spatial_motion_cross_self_zero`** ($v \times_m v = 0$), **`featherstone_spatial_adjoint_duality`**
    ($\langle f, u \times_m v \rangle + \langle u \times_f f, v \rangle = 0$), and
    **`rnea_gyroscopic_coriolis_power_zero`** ($\langle v \times_f p, v \rangle = 0$ for all twists $v$ and
    spatial momenta $p = I v$, proving that Coriolis/centrifugal terms in Recursive Newton-Euler `RNEA`
    and Articulated-Body `ABA` dynamics conserve mechanical energy!).
* **Ruckig 3rd-Order Jerk-Limited Online Trajectory Generation (`arXiv:2105.04830`)**
  (Berscheid & Kröger, *Jerk-limited Real-time Trajectory Generation with Arbitrary Target States*, RSS 2021):
  - Models exact integer-scaled 3rd-order kinematic state integration $(p, v, a) \xrightarrow{j, \Delta t} (p', v', a')$,
  - Proves **`ruckig_symmetric_pulse_exact`** (a symmetric $+j$ / $0$ / $-j$ S-curve profile restores
    exact initial acceleration while advancing velocity by $2 j\,\Delta t^2$),
  - Proves **`ruckig_directional_limits_sound`** (enforcing asymmetric/directional velocity and acceleration
    bounds $[v_{\min}, v_{\max}]$, $[a_{\min}, a_{\max}]$).
* **5-Axis CNC 21-Parameter Volumetric Geometric Error & Abbe Lever-Arm Compensation**:
  - Models carriage translational errors $\boldsymbol{\delta} = (\delta_x, \delta_y, \delta_z)$ coupled with
    angular roll/pitch/yaw errors $\boldsymbol{\epsilon} = (\epsilon_x, \epsilon_y, \epsilon_z)$ across a
    spindle/tool-holder Abbe offset vector $\mathbf{L} = (L_x, L_y, L_z)$:
    $$\mathbf{e}_{\text{vol}} = \boldsymbol{\delta} + \boldsymbol{\epsilon} \times \mathbf{L},$$
  - Proves **`abbe_volumetric_compensation_exact`**: pre-compensating the CNC axis command by $-\mathbf{e}_{\text{vol}}$
    cancels both translational error and 3D angular Abbe lever-arm error across all three axes simultaneously.
-/
public import Obend.Hardware.GeometryCAM
@[expose] public section

namespace Obend.Hardware.Kinematics
set_option autoImplicit false

/-! ## 1. 3D Integer-Scaled Vector Algebra (`Vec3`, `dot3`, `cross3`) -/

/-- A 3D vector in integer-scaled physical coordinates (e.g. nanometers, microradians/s, or milli-Newtons). -/
structure Vec3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

/-- Zero 3D vector $(0, 0, 0)$. -/
def Vec3.zero : Vec3 := { x := 0, y := 0, z := 0 }

/-- Componentwise 3D vector addition $\mathbf{a} + \mathbf{b}$. -/
def Vec3.add (a b : Vec3) : Vec3 where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

/-- Componentwise 3D vector subtraction $\mathbf{a} - \mathbf{b}$. -/
def Vec3.sub (a b : Vec3) : Vec3 where
  x := a.x - b.x
  y := a.y - b.y
  z := a.z - b.z

/-- Componentwise 3D vector negation $-\mathbf{a}$. -/
def Vec3.neg (a : Vec3) : Vec3 where
  x := -a.x
  y := -a.y
  z := -a.z

/-- Euclidean inner product $\mathbf{a} \cdot \mathbf{b} = a_x b_x + a_y b_y + a_z b_z$. -/
def dot3 (a b : Vec3) : Int :=
  a.x * b.x + a.y * b.y + a.z * b.z

/-- 3D vector cross product $\mathbf{a} \times \mathbf{b}$. -/
def cross3 (a b : Vec3) : Vec3 where
  x := a.y * b.z - a.z * b.y
  y := a.z * b.x - a.x * b.z
  z := a.x * b.y - a.y * b.x

/-- Cross product of any 3D vector with itself vanishes (`cross3_self_zero`). -/
theorem cross3_self_zero (a : Vec3) :
    cross3 a a = Vec3.zero := by
  cases a with | mk ax ay az =>
  dsimp only [cross3, Vec3.zero]
  rw [Int.mul_comm ay az, Int.mul_comm az ax, Int.mul_comm ax ay]
  congr 1 <;> omega

/-- Skew-symmetry of the 3D cross product (`cross3_anticomm`): $\mathbf{a} \times \mathbf{b} + \mathbf{b} \times \mathbf{a} = \mathbf{0}$. -/
theorem cross3_anticomm (a b : Vec3) :
    Vec3.add (cross3 a b) (cross3 b a) = Vec3.zero := by
  cases a with | mk ax ay az =>
  cases b with | mk bx by_ bz =>
  dsimp only [Vec3.add, cross3, Vec3.zero]
  rw [Int.mul_comm by_ az, Int.mul_comm bz ay,
      Int.mul_comm bz ax, Int.mul_comm bx az,
      Int.mul_comm bx ay, Int.mul_comm by_ ax]
  congr 1 <;> omega

/-- Scalar triple product adjoint identity (`dot3_cross3_adjoint`):
For all $\mathbf{w}, \mathbf{a}, \mathbf{f} \in \mathbb{Z}^3$,
$$\mathbf{f} \cdot (\boldsymbol{\omega} \times \mathbf{a}) + (\boldsymbol{\omega} \times \mathbf{f}) \cdot \mathbf{a} = 0.$$ -/
theorem dot3_cross3_adjoint (w a f : Vec3) :
    dot3 f (cross3 w a) + dot3 (cross3 w f) a = 0 := by
  dsimp only [dot3, cross3]
  simp only [Int.mul_sub, Int.sub_mul]
  have h1 : f.x * (w.y * a.z) = (w.y * f.x) * a.z := by
    rw [← Int.mul_assoc f.x w.y a.z, Int.mul_comm f.x w.y]
  have h2 : f.x * (w.z * a.y) = (w.z * f.x) * a.y := by
    rw [← Int.mul_assoc f.x w.z a.y, Int.mul_comm f.x w.z]
  have h3 : f.y * (w.z * a.x) = (w.z * f.y) * a.x := by
    rw [← Int.mul_assoc f.y w.z a.x, Int.mul_comm f.y w.z]
  have h4 : f.y * (w.x * a.z) = (w.x * f.y) * a.z := by
    rw [← Int.mul_assoc f.y w.x a.z, Int.mul_comm f.y w.x]
  have h5 : f.z * (w.x * a.y) = (w.x * f.z) * a.y := by
    rw [← Int.mul_assoc f.z w.x a.y, Int.mul_comm f.z w.x]
  have h6 : f.z * (w.y * a.x) = (w.y * f.z) * a.x := by
    rw [← Int.mul_assoc f.z w.y a.x, Int.mul_comm f.z w.y]
  rw [h1, h2, h3, h4, h5, h6]
  omega

/-! ## 2. Featherstone 6D Spatial Vector Algebra ($\mathfrak{se}(3)$ Twists & $\mathfrak{se}(3)^*$ Wrenches) -/

/-- A 6D spatial motion vector (twist $v \in M^6 \cong \mathfrak{se}(3)$) in Plücker coordinates:
* `ang`: 3D angular velocity $\boldsymbol{\omega}$,
* `lin`: 3D linear velocity $\mathbf{v}_O$ at the frame origin. -/
structure SpatialTwist6D where
  ang : Vec3
  lin : Vec3
  deriving DecidableEq, Repr

/-- Zero 6D twist. -/
def SpatialTwist6D.zero : SpatialTwist6D :=
  { ang := Vec3.zero, lin := Vec3.zero }

/-- A 6D spatial force vector (wrench $f \in F^6 \cong \mathfrak{se}(3)^*$) in Plücker coordinates:
* `torque`: 3D moment/couple $\boldsymbol{\tau}_O$ about the frame origin,
* `force`: 3D linear force $\mathbf{f}$. -/
structure SpatialWrench6D where
  torque : Vec3
  force  : Vec3
  deriving DecidableEq, Repr

/-- Spatial duality pairing (virtual mechanical power $\langle f, v \rangle = \boldsymbol{\tau} \cdot \boldsymbol{\omega} + \mathbf{f} \cdot \mathbf{v}$). -/
def spatialPower (f : SpatialWrench6D) (v : SpatialTwist6D) : Int :=
  dot3 f.torque v.ang + dot3 f.force v.lin

/-- Featherstone spatial motion cross-product ($\operatorname{ad}_u(v) = u \times_m v$, the Lie bracket on $\mathfrak{se}(3)$):
$$(\boldsymbol{\omega}_1, \mathbf{v}_1) \times_m (\boldsymbol{\omega}_2, \mathbf{v}_2) =
  (\boldsymbol{\omega}_1 \times \boldsymbol{\omega}_2,\; \boldsymbol{\omega}_1 \times \mathbf{v}_2 + \mathbf{v}_1 \times \boldsymbol{\omega}_2).$$ -/
def spatialCrossMotion (u v : SpatialTwist6D) : SpatialTwist6D where
  ang := cross3 u.ang v.ang
  lin := Vec3.add (cross3 u.ang v.lin) (cross3 u.lin v.ang)

/-- Featherstone spatial force cross-product ($\operatorname{ad}_u^*(f) = u \times_f f$, the coadjoint action on $\mathfrak{se}(3)^*$):
$$(\boldsymbol{\omega}_1, \mathbf{v}_1) \times_f (\boldsymbol{\tau}, \mathbf{f}) =
  (\boldsymbol{\omega}_1 \times \boldsymbol{\tau} + \mathbf{v}_1 \times \mathbf{f},\; \boldsymbol{\omega}_1 \times \mathbf{f}).$$ -/
def spatialCrossForce (u : SpatialTwist6D) (f : SpatialWrench6D) : SpatialWrench6D where
  torque := Vec3.add (cross3 u.ang f.torque) (cross3 u.lin f.force)
  force  := cross3 u.ang f.force

/-- **Self Lie Bracket Vanishes (`spatial_motion_cross_self_zero`)**:
For every 6D spatial twist $v \in \mathfrak{se}(3)$, $v \times_m v = 0$. -/
theorem spatial_motion_cross_self_zero (v : SpatialTwist6D) :
    spatialCrossMotion v v = SpatialTwist6D.zero := by
  dsimp only [spatialCrossMotion, SpatialTwist6D.zero]
  rw [cross3_self_zero, cross3_anticomm]

/-- Bilinearity helper for `dot3` over `Vec3.add` on the left. -/
theorem dot3_add_left (a b c : Vec3) :
    dot3 (Vec3.add a b) c = dot3 a c + dot3 b c := by
  dsimp only [dot3, Vec3.add]
  simp only [Int.add_mul]
  omega

/-- Bilinearity helper for `dot3` over `Vec3.add` on the right. -/
theorem dot3_add_right (a b c : Vec3) :
    dot3 a (Vec3.add b c) = dot3 a b + dot3 a c := by
  dsimp only [dot3, Vec3.add]
  simp only [Int.mul_add]
  omega

/-- **Fundamental Adjoint–Coadjoint Duality of Featherstone Spatial Algebra (`featherstone_spatial_adjoint_duality`)**:
For all 6D twists $u, v \in \mathfrak{se}(3)$ and all 6D wrenches $f \in \mathfrak{se}(3)^*$:
$$\langle f,\; u \times_m v \rangle + \langle u \times_f f,\; v \rangle = 0.$$
This is the foundational operator-adjoint identity underlying $O(N)$ analytical derivatives in
differentiable articulated body simulation (`arXiv:2109.07719`, `arXiv:2105.05102`). -/
theorem featherstone_spatial_adjoint_duality
    (u v : SpatialTwist6D) (f : SpatialWrench6D) :
    spatialPower f (spatialCrossMotion u v) + spatialPower (spatialCrossForce u f) v = 0 := by
  dsimp only [spatialPower, spatialCrossMotion, spatialCrossForce]
  rw [dot3_add_right, dot3_add_left]
  have h1 := dot3_cross3_adjoint u.ang v.ang f.torque
  have h2 := dot3_cross3_adjoint u.ang v.lin f.force
  have h3 := dot3_cross3_adjoint u.lin v.ang f.force
  omega

/-- **Conservation of Mechanical Power Under Gyroscopic / Coriolis Spatial Forces (`rnea_gyroscopic_coriolis_power_zero`)**:
In Featherstone's Recursive Newton-Euler (`RNEA`) and Articulated-Body (`ABA`) equations of motion
$f = I a + v \times_f (I v)$, the velocity-dependent Coriolis/centrifugal spatial wrench $v \times_f p$
(for any spatial momentum $p = I v \in \mathfrak{se}(3)^*$) performs **identically zero mechanical work**
along the link's own twist $v$:
$$\langle v \times_f p,\; v \rangle = 0.$$ -/
theorem rnea_gyroscopic_coriolis_power_zero
    (v : SpatialTwist6D) (p : SpatialWrench6D) :
    spatialPower (spatialCrossForce v p) v = 0 := by
  have hDual := featherstone_spatial_adjoint_duality v v p
  rw [spatial_motion_cross_self_zero] at hDual
  have hZero : spatialPower p SpatialTwist6D.zero = 0 := by
    dsimp only [spatialPower, SpatialTwist6D.zero, dot3, Vec3.zero]
    omega
  omega

/-! ## 3. Ruckig 3rd-Order Jerk-Limited Trajectory Generation (`arXiv:2105.04830`) -/

/-- Kinematic state of a 1D axis in integer-scaled Ruckig units (`arXiv:2105.04830`, Section III):
* `posScaled6`: $6 \times p(t)$,
* `velScaled2`: $2 \times v(t)$,
* `acc`: $a(t)$. -/
structure RuckigState1D where
  posScaled6 : Int
  velScaled2 : Int
  acc        : Int
  deriving DecidableEq, Repr

/-- Exact 3rd-order constant-jerk integration step (`arXiv:2105.04830`, Eq. 1) over duration `dt`
with constant jerk `j`. -/
def stepRuckigSegment (st : RuckigState1D) (j dt : Int) : RuckigState1D where
  posScaled6 := st.posScaled6 + 3 * st.velScaled2 * dt + 3 * st.acc * dt * dt + j * dt * dt * dt
  velScaled2 := st.velScaled2 + 2 * st.acc * dt + j * dt * dt
  acc        := st.acc + j * dt

/-- **Ruckig Symmetric Jerk-Pulse Acceleration Restoration & Velocity Gain Theorem (`ruckig_symmetric_pulse_exact`)**:
Applying a positive jerk pulse $(+j, \Delta t)$ and a symmetric negative jerk pulse $(-j, \Delta t)$
starting from $a_0 = 0$ restores $a_2 = 0$ and advances $2 v$ by $2 j\,\Delta t^2$. -/
theorem ruckig_symmetric_pulse_exact (p0 v0 j dt : Int) :
    let st0 : RuckigState1D := { posScaled6 := p0, velScaled2 := v0, acc := 0 }
    let st1 := stepRuckigSegment st0 j dt
    let st2 := stepRuckigSegment st1 (-j) dt
    st2.acc = 0 ∧ st2.velScaled2 = v0 + 2 * j * dt * dt := by
  dsimp only [stepRuckigSegment]
  rw [Int.neg_mul, Int.neg_mul]
  constructor
  · omega
  · rw [Int.zero_add, ← Int.mul_assoc 2 j dt]
    omega

/-- Directional kinematic constraint checker (`arXiv:2105.04830`, Section III-B). -/
def checkRuckigDirectionalLimits
    (st : RuckigState1D) (j vMinScaled2 vMaxScaled2 aMin aMax jMax : Int) : Bool :=
  decide (vMinScaled2 ≤ st.velScaled2 ∧ st.velScaled2 ≤ vMaxScaled2) &&
  decide (aMin ≤ st.acc ∧ st.acc ≤ aMax) &&
  decide (-jMax ≤ j ∧ j ≤ jMax)

/-- **Soundness of Ruckig Directional Kinematic Envelope (`ruckig_directional_limits_sound`)**. -/
theorem ruckig_directional_limits_sound
    (st : RuckigState1D) (j vMinScaled2 vMaxScaled2 aMin aMax jMax : Int)
    (h : checkRuckigDirectionalLimits st j vMinScaled2 vMaxScaled2 aMin aMax jMax = true) :
    (vMinScaled2 ≤ st.velScaled2 ∧ st.velScaled2 ≤ vMaxScaled2) ∧
    (aMin ≤ st.acc ∧ st.acc ≤ aMax) ∧
    (-jMax ≤ j ∧ j ≤ jMax) := by
  unfold checkRuckigDirectionalLimits at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## 4. 5-Axis CNC 21-Parameter Volumetric Geometric Error & Abbe Lever-Arm Compensation -/

/-- Evaluates the 3D volumetric geometric error vector $\mathbf{e}_{\text{vol}} = \boldsymbol{\delta} + \boldsymbol{\epsilon} \times \mathbf{L}$. -/
def evalVolumetricError3D (linErr angErr abbeArm : Vec3) : Vec3 :=
  Vec3.add linErr (cross3 angErr abbeArm)

/-- Evaluates the physical cutter-tip position $\mathbf{p}_{\text{actual}} = \mathbf{p}_{\text{cmd}} + \mathbf{e}_{\text{vol}}$. -/
def evalUncompensatedTipPos3D (pCmd linErr angErr abbeArm : Vec3) : Vec3 :=
  Vec3.add pCmd (evalVolumetricError3D linErr angErr abbeArm)

/-- Pre-compensates the CNC axis command by subtracting the calibrated volumetric error model:
$\mathbf{p}_{\text{comp}} = \mathbf{p}_{\text{target}} - (\boldsymbol{\delta} + \boldsymbol{\epsilon} \times \mathbf{L})$. -/
def evalAbbeCompensatedCmd3D (pTarget linErr angErr abbeArm : Vec3) : Vec3 :=
  Vec3.sub pTarget (evalVolumetricError3D linErr angErr abbeArm)

/-- **Exact 3D Abbe Volumetric Error Cancellation Theorem (`abbe_volumetric_compensation_exact`)**. -/
theorem abbe_volumetric_compensation_exact (pTarget linErr angErr abbeArm : Vec3) :
    evalUncompensatedTipPos3D (evalAbbeCompensatedCmd3D pTarget linErr angErr abbeArm) linErr angErr abbeArm =
      pTarget := by
  cases pTarget; cases linErr; cases angErr; cases abbeArm
  dsimp only [evalUncompensatedTipPos3D, evalAbbeCompensatedCmd3D, evalVolumetricError3D,
              Vec3.add, Vec3.sub, cross3]
  congr 1 <;> omega

/-- Golden Verification of Featherstone Spatial Algebra, Ruckig S-Curve & 5-Axis Abbe Compensation. -/
theorem golden_kinematics_featherstone_ruckig_verified :
    let twist : SpatialTwist6D := { ang := { x := 3, y := -4, z := 12 }, lin := { x := 50, y := -20, z := 10 } }
    let mom   : SpatialWrench6D := { torque := { x := 90, y := -80, z := 240 }, force := { x := 250, y := -100, z := 50 } }
    let st0   : RuckigState1D := { posScaled6 := 0, velScaled2 := 0, acc := 0 }
    let st2   := stepRuckigSegment (stepRuckigSegment st0 5 4) (-5) 4
    let target : Vec3 := { x := 100000, y := 200000, z := 50000 }
    let linErr : Vec3 := { x := 12, y := -8, z := 5 }
    let angErr : Vec3 := { x := 2, y := -3, z := 1 }
    let arm    : Vec3 := { x := 0, y := 0, z := 150 }
    spatialPower (spatialCrossForce twist mom) twist = 0 ∧
    st2.acc = 0 ∧
    st2.velScaled2 = 160 ∧
    evalUncompensatedTipPos3D (evalAbbeCompensatedCmd3D target linErr angErr arm) linErr angErr arm = target := by
  decide +kernel

end Obend.Hardware.Kinematics
end
