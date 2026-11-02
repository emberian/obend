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

/-! ## 5. Multi-Link Articulated Kinematic Chain & Recursive Newton-Euler (`RNEA`) Dynamics -/

/-- Scalar multiplication $s \cdot \mathbf{a}$ of a 3D vector. -/
def Vec3.scale (s : Int) (a : Vec3) : Vec3 where
  x := s * a.x
  y := s * a.y
  z := s * a.z

/-- Componentwise addition of two 6D spatial twists $u + v \in \mathfrak{se}(3)$. -/
def SpatialTwist6D.add (u v : SpatialTwist6D) : SpatialTwist6D where
  ang := Vec3.add u.ang v.ang
  lin := Vec3.add u.lin v.lin

/-- Scalar multiplication $s \cdot v \in \mathfrak{se}(3)$ of a 6D spatial twist (e.g. $S_i \dot{q}_i$). -/
def SpatialTwist6D.scale (s : Int) (v : SpatialTwist6D) : SpatialTwist6D where
  ang := Vec3.scale s v.ang
  lin := Vec3.scale s v.lin

/-- Zero 6D spatial wrench $(0, 0) \in \mathfrak{se}(3)^*$. -/
def SpatialWrench6D.zero : SpatialWrench6D :=
  { torque := Vec3.zero, force := Vec3.zero }

/-- Componentwise addition of two 6D spatial wrenches $f + g \in \mathfrak{se}(3)^*$. -/
def SpatialWrench6D.add (f g : SpatialWrench6D) : SpatialWrench6D where
  torque := Vec3.add f.torque g.torque
  force  := Vec3.add f.force g.force

/-- Componentwise subtraction of two 6D spatial wrenches $f - g \in \mathfrak{se}(3)^*$. -/
def SpatialWrench6D.sub (f g : SpatialWrench6D) : SpatialWrench6D where
  torque := Vec3.sub f.torque g.torque
  force  := Vec3.sub f.force g.force

/-- **Left Bilinearity of Spatial Duality Pairing (`spatialPower_bilinear_add_left`)**:
$$\langle f + g,\; v \rangle = \langle f, v \rangle + \langle g, v \rangle.$$ -/
theorem spatialPower_bilinear_add_left
    (f g : SpatialWrench6D) (v : SpatialTwist6D) :
    spatialPower (SpatialWrench6D.add f g) v = spatialPower f v + spatialPower g v := by
  dsimp only [spatialPower, SpatialWrench6D.add]
  rw [dot3_add_left, dot3_add_left]
  omega

/-- **Right Bilinearity of Spatial Duality Pairing (`spatialPower_bilinear_add_right`)**:
$$\langle f,\; u + v \rangle = \langle f, u \rangle + \langle f, v \rangle.$$ -/
theorem spatialPower_bilinear_add_right
    (f : SpatialWrench6D) (u v : SpatialTwist6D) :
    spatialPower f (SpatialTwist6D.add u v) = spatialPower f u + spatialPower f v := by
  dsimp only [spatialPower, SpatialTwist6D.add]
  rw [dot3_add_right, dot3_add_right]
  omega

/-- Dynamic state of a single articulated body link $i$ in a Featherstone Recursive Newton-Euler
(`RNEA`) serial kinematic chain (`arXiv:2109.07719`, `arXiv:2105.05102`, `arXiv:2203.01497`):
* `jointAxis`: joint motion subspace twist $S_i \in \mathfrak{se}(3)$,
* `qDot`: generalized joint velocity $\dot{q}_i$,
* `linkMomentum`: spatial momentum $p_i = I_i v_i \in \mathfrak{se}(3)^*$,
* `inertialAccelWrench`: inertial D'Alembert acceleration wrench $f_{\text{inertial},i} = I_i a_i \in \mathfrak{se}(3)^*$. -/
structure RneaChainLink where
  jointAxis           : SpatialTwist6D
  qDot                : Int
  linkMomentum        : SpatialWrench6D
  inertialAccelWrench : SpatialWrench6D
  deriving DecidableEq, Repr

/-- Alias `LinkDynamicState` for `RneaChainLink`. -/
abbrev LinkDynamicState := RneaChainLink

/-- Forward kinematic twist propagation across a single joint:
$$v_i = v_{\lambda(i)} + S_i \dot{q}_i.$$ -/
def stepForwardLinkTwist (parentTwist : SpatialTwist6D) (link : RneaChainLink) : SpatialTwist6D :=
  SpatialTwist6D.add parentTwist (SpatialTwist6D.scale link.qDot link.jointAxis)

/-- Forward `RNEA` pass (`forwardChainTwists`): propagates 6D spatial twists $v_1, \dots, v_N$
from base twist `parentTwist` outward along an $N$-link articulated kinematic chain. -/
def forwardChainTwists (parentTwist : SpatialTwist6D) : List RneaChainLink → List SpatialTwist6D
  | [] => []
  | link :: rest =>
    let vLink := stepForwardLinkTwist parentTwist link
    vLink :: forwardChainTwists vLink rest

/-- Evaluates the net rigid-body Euler-Poincaré / Newton-Euler spatial wrench on a link with twist $v$,
inertial acceleration wrench $f_{\text{inertial}} = I a$, and spatial momentum $p = I v$:
$$f_{\text{net}} = f_{\text{inertial}} + v \times_f p.$$ -/
def evalLinkNetWrench
    (v : SpatialTwist6D) (fInertial pMomentum : SpatialWrench6D) : SpatialWrench6D :=
  SpatialWrench6D.add fInertial (spatialCrossForce v pMomentum)

/-- Backward `RNEA` pass (`backwardChainWrenches`): accumulates transmitted joint wrenches
$f_i = f_{\text{net},i} + f_{i+1}$ from distal tip wrench `tipWrench` inward to the base. -/
def backwardChainWrenches : List (SpatialTwist6D × RneaChainLink) → SpatialWrench6D → List SpatialWrench6D
  | [], _ => []
  | (v, link) :: rest, tipWrench =>
    let childWrenches := backwardChainWrenches rest tipWrench
    let fChild := childWrenches.headD tipWrench
    let fNet := evalLinkNetWrench v link.inertialAccelWrench link.linkMomentum
    SpatialWrench6D.add fNet fChild :: childWrenches

/-- Projects the transmitted spatial joint wrench $f_i \in \mathfrak{se}(3)^*$ onto the joint motion
subspace axis $S_i \in \mathfrak{se}(3)$ to obtain generalized actuator torque/force $\tau_i = S_i^\top f_i$:
$$\tau_i = \langle f_i, S_i \rangle.$$ -/
def evalRneaJointTorque (jointAxis : SpatialTwist6D) (jointWrench : SpatialWrench6D) : Int :=
  spatialPower jointWrench jointAxis

/-- **Single-Link RNEA Coriolis Power Neutrality (`rnea_link_coriolis_power_neutral`)**:
For any link with twist $v$, inertial acceleration wrench $f_{\text{inertial}} = I a$, and spatial
momentum $p = I v$, the virtual mechanical power of the net RNEA wrench
$f_{\text{net}} = f_{\text{inertial}} + v \times_f p$ equals purely the inertial acceleration power
$\langle f_{\text{inertial}}, v \rangle$ (the gyroscopic/Coriolis wrench $v \times_f p$ contributes
identically zero net power!). -/
theorem rnea_link_coriolis_power_neutral
    (v : SpatialTwist6D) (fInertial pMomentum : SpatialWrench6D) :
    spatialPower (evalLinkNetWrench v fInertial pMomentum) v = spatialPower fInertial v := by
  unfold evalLinkNetWrench
  rw [spatialPower_bilinear_add_left, rnea_gyroscopic_coriolis_power_zero, Int.add_zero]

/-- Sums the gyroscopic/Coriolis virtual mechanical power $\sum_i \langle v_i \times_f p_i, v_i \rangle$
across an arbitrary multi-link articulated kinematic chain. -/
def evalMultiLinkCoriolisPower : List (SpatialTwist6D × SpatialWrench6D) → Int
  | [] => 0
  | (v, p) :: rest =>
    spatialPower (spatialCrossForce v p) v + evalMultiLinkCoriolisPower rest

/-- **Multi-Link Articulated Chain Total Coriolis Power Cancellation (`multi_link_rnea_total_coriolis_power_zero`)**:
Summing the gyroscopic/Coriolis virtual mechanical power across any arbitrary multi-link articulated
kinematic chain `chain : List (SpatialTwist6D × SpatialWrench6D)` vanishes identically (`= 0`),
regardless of the number of links, joint velocities, or link inertias. -/
theorem multi_link_rnea_total_coriolis_power_zero
    (chain : List (SpatialTwist6D × SpatialWrench6D)) :
    evalMultiLinkCoriolisPower chain = 0 := by
  induction chain with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨v, p⟩
    dsimp only [evalMultiLinkCoriolisPower]
    rw [rnea_gyroscopic_coriolis_power_zero, ih, Int.add_zero]

/-- Pairs each propagated link twist from `forwardChainTwists` with its link spatial momentum `linkMomentum`
along an $N$-link articulated kinematic chain. -/
def forwardChainTwistMomentumPairs (parentTwist : SpatialTwist6D) :
    List RneaChainLink → List (SpatialTwist6D × SpatialWrench6D)
  | [] => []
  | link :: rest =>
    let vLink := stepForwardLinkTwist parentTwist link
    (vLink, link.linkMomentum) :: forwardChainTwistMomentumPairs vLink rest

/-- **Forward-Propagated Multi-Link RNEA Coriolis Power Conservation (`forward_chain_rnea_coriolis_power_zero`)**:
For ANY base twist `parentTwist` and ANY articulated kinematic chain `links : List RneaChainLink`,
propagating joint velocities outward via `forwardChainTwistMomentumPairs` yields identically zero
total gyroscopic/Coriolis virtual mechanical power across the entire chain. -/
theorem forward_chain_rnea_coriolis_power_zero
    (parentTwist : SpatialTwist6D) (links : List RneaChainLink) :
    evalMultiLinkCoriolisPower (forwardChainTwistMomentumPairs parentTwist links) = 0 :=
  multi_link_rnea_total_coriolis_power_zero (forwardChainTwistMomentumPairs parentTwist links)

/-! ## 6. 7-Phase Ruckig Jerk-Limited Trajectory Profile (`RuckigProfile7`, `UDDU` / `UDUD`) -/

/-- Jerk sign sequence (`ControlSigns` in `ruckig/include/ruckig/profile.hpp`, `arXiv:2105.04830`):
* `.uddu`: Up-Down-Down-Up (`+jMax, 0, -jMax, 0, -jMax, 0, +jMax`),
* `.udud`: Up-Down-Up-Down (`+jMax, 0, -jMax, 0, +jMax, 0, -jMax`). -/
inductive RuckigControlSigns where
  | uddu
  | udud
  deriving DecidableEq, Repr

/-- Alias `ControlSigns` matching `ruckig::Profile::ControlSigns`. -/
abbrev ControlSigns := RuckigControlSigns

/-- Complete 7-segment 3rd-order jerk-limited Ruckig trajectory profile (`arXiv:2105.04830`, Fig. 2). -/
structure RuckigProfile7 where
  jMax  : Int
  t1    : Int
  t2    : Int
  t3    : Int
  t4    : Int
  t5    : Int
  t6    : Int
  t7    : Int
  signs : RuckigControlSigns
  deriving DecidableEq, Repr

/-- Integrates all 7 phases of a 3rd-order jerk-limited Ruckig profile starting from `st0`:
* Phases 1–3 (acceleration profile): `(+jMax, t1) -> (0, t2) -> (-jMax, t3)`,
* Phase 4 (constant-velocity cruise): `(0, t4)`,
* Phases 5–7 (deceleration profile):
  - `.uddu`: `(-jMax, t5) -> (0, t6) -> (+jMax, t7)`,
  - `.udud`: `(+jMax, t5) -> (0, t6) -> (-jMax, t7)`. -/
def evalRuckigProfile7
    (st0 : RuckigState1D) (jMax : Int) (t1 t2 t3 t4 t5 t6 t7 : Int)
    (signs : RuckigControlSigns) : RuckigState1D :=
  let st1 := stepRuckigSegment st0 jMax t1
  let st2 := stepRuckigSegment st1 0 t2
  let st3 := stepRuckigSegment st2 (-jMax) t3
  let st4 := stepRuckigSegment st3 0 t4
  match signs with
  | .uddu =>
    let st5 := stepRuckigSegment st4 (-jMax) t5
    let st6 := stepRuckigSegment st5 0 t6
    stepRuckigSegment st6 jMax t7
  | .udud =>
    let st5 := stepRuckigSegment st4 jMax t5
    let st6 := stepRuckigSegment st5 0 t6
    stepRuckigSegment st6 (-jMax) t7

/-- **Exact Closed-Form Identity for Symmetric 7-Phase Rest-to-Rest `UDDU` Ruckig Profile
(`ruckig_7phase_symmetric_rest_to_rest_identity`)**:
For any symmetric 7-phase `.uddu` profile with jerk-ramp duration $t_1 = t_3 = t_5 = t_7 = \tau$,
constant-acceleration hold duration $t_2 = t_6 = \tau_{\text{acc}}$, and constant-velocity cruise
duration $t_4 = \tau_{\text{cruise}}$, starting from rest $(v_0 = 0, a_0 = 0)$ at position $p_0$:
1. Final acceleration at the end of phase 7 is identically zero ($a_7 = 0$),
2. Final velocity at the end of phase 7 is identically zero ($2 v_7 = 0$),
3. Final scaled position $6 p_7$ equals
   $$6 p_0 + 6 j_{\max} \tau (\tau + \tau_{\text{acc}})(2\tau + \tau_{\text{acc}} + \tau_{\text{cruise}}).$$ -/
theorem ruckig_7phase_symmetric_rest_to_rest_identity
    (p0 jMax tau tAcc tCruise : Int) :
    let st0 : RuckigState1D := { posScaled6 := p0, velScaled2 := 0, acc := 0 }
    let st7 := evalRuckigProfile7 st0 jMax tau tAcc tau tCruise tau tAcc tau .uddu
    st7.acc = 0 ∧
    st7.velScaled2 = 0 ∧
    st7.posScaled6 = p0 + 6 * jMax * tau * (tau + tAcc) * (2 * tau + tAcc + tCruise) := by
  dsimp only [evalRuckigProfile7, stepRuckigSegment]
  refine ⟨by grind, by grind, by grind⟩

/-- **Ruckig 7-Phase Symmetric Rest-to-Rest Theorem (`ruckig_7phase_symmetric_rest_to_rest`)**:
For any symmetric 7-phase `UDDU` profile with $t_1 = t_3 = t_5 = t_7 = \tau > 0$,
$t_2 = t_6 = \tau_{\text{acc}} \ge 0$, $t_4 = \tau_{\text{cruise}} \ge 0$, and $j_{\max} > 0$,
starting from rest $(v_0 = 0, a_0 = 0)$ reaches exact rest $(v_7 = 0, a_7 = 0)$ at the end of
phase 7 while strictly advancing position ($p_0 < p_7$). -/
theorem ruckig_7phase_symmetric_rest_to_rest
    (p0 jMax tau tAcc tCruise : Int)
    (hj : 0 < jMax) (hTau : 0 < tau) (hAcc : 0 ≤ tAcc) (hCruise : 0 ≤ tCruise) :
    let st0 : RuckigState1D := { posScaled6 := p0, velScaled2 := 0, acc := 0 }
    let st7 := evalRuckigProfile7 st0 jMax tau tAcc tau tCruise tau tAcc tau .uddu
    st7.acc = 0 ∧ st7.velScaled2 = 0 ∧ p0 < st7.posScaled6 := by
  have hId := ruckig_7phase_symmetric_rest_to_rest_identity p0 jMax tau tAcc tCruise
  dsimp only at hId
  refine ⟨hId.1, hId.2.1, ?_⟩
  rw [hId.2.2]
  have h6j : 0 < 6 * jMax := Int.mul_pos (by omega) hj
  have h6jt : 0 < 6 * jMax * tau := Int.mul_pos h6j hTau
  have hTauAcc : 0 < tau + tAcc := by omega
  have hPeakVel : 0 < 6 * jMax * tau * (tau + tAcc) := Int.mul_pos h6jt hTauAcc
  have hDur : 0 < 2 * tau + tAcc + tCruise := by omega
  have hDisp : 0 < 6 * jMax * tau * (tau + tAcc) * (2 * tau + tAcc + tCruise) :=
    Int.mul_pos hPeakVel hDur
  omega

end Obend.Hardware.Kinematics
end

