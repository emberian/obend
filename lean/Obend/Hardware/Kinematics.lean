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
* **Small-angle rigid-body error of one carriage (six of the 21 parameters; Abbe lever arm)**:
  - The 21-parameter model of a three-axis machine is six errors per axis plus three squareness
    terms, each a function of position; this section has one carriage's six, constant, to first
    order. Models carriage translational errors $\boldsymbol{\delta} = (\delta_x, \delta_y, \delta_z)$ coupled with
    angular roll/pitch/yaw errors $\boldsymbol{\epsilon} = (\epsilon_x, \epsilon_y, \epsilon_z)$ across a
    spindle/tool-holder Abbe offset vector $\mathbf{L} = (L_x, L_y, L_z)$:
    $$\mathbf{e}_{\text{vol}} = \boldsymbol{\delta} + \boldsymbol{\epsilon} \times \mathbf{L},$$
  - Proves **`abbe_volumetric_compensation_exact`**: pre-compensating the CNC axis command by $-\mathbf{e}_{\text{vol}}$
    cancels both translational error and 3D angular Abbe lever-arm error across all three axes simultaneously.
* **A post-processor for an A/C trunnion with TCPM (§8)**: typed NC moves, `postNgc` text in the Fanuc
  30i dialect, and **`postMoves_rotarySafe`**: for every list of 3+2 operations, no feed changes the
  tool axis and every re-orientation is a rapid on or above the clearance plane.
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
example :
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

/-! ## 7. Serial Kinematic Chain Forward Twist Propagator (`propagateSerialChainTwists`) -/

/-- Propagates and accumulates relative 6D joint motion twists $v_{\text{tip}} = \sum_{i=1}^N v_i \in \mathfrak{se}(3)$
along an $N$-link serial kinematic chain (`List SpatialTwist6D`). -/
def propagateSerialChainTwists : List SpatialTwist6D → SpatialTwist6D
  | [] => SpatialTwist6D.zero
  | v :: rest => SpatialTwist6D.add v (propagateSerialChainTwists rest)

theorem Vec3.add_zero (a : Vec3) : Vec3.add a Vec3.zero = a := by
  cases a
  dsimp only [Vec3.add, Vec3.zero]
  congr 1 <;> omega

theorem Vec3.zero_add (a : Vec3) : Vec3.add Vec3.zero a = a := by
  cases a
  dsimp only [Vec3.add, Vec3.zero]
  congr 1 <;> omega

theorem Vec3.add_assoc (a b c : Vec3) :
    Vec3.add (Vec3.add a b) c = Vec3.add a (Vec3.add b c) := by
  cases a; cases b; cases c
  dsimp only [Vec3.add]
  congr 1 <;> omega

theorem Vec3.scale_zero (s : Int) : Vec3.scale s Vec3.zero = Vec3.zero := by
  dsimp only [Vec3.scale, Vec3.zero]
  congr 1 <;> omega

theorem Vec3.scale_add (s : Int) (a b : Vec3) :
    Vec3.scale s (Vec3.add a b) = Vec3.add (Vec3.scale s a) (Vec3.scale s b) := by
  cases a; cases b
  dsimp only [Vec3.scale, Vec3.add]
  congr 1 <;> grind

theorem SpatialTwist6D.add_zero (v : SpatialTwist6D) :
    SpatialTwist6D.add v SpatialTwist6D.zero = v := by
  cases v
  dsimp only [SpatialTwist6D.add, SpatialTwist6D.zero]
  rw [Vec3.add_zero, Vec3.add_zero]

theorem SpatialTwist6D.zero_add (v : SpatialTwist6D) :
    SpatialTwist6D.add SpatialTwist6D.zero v = v := by
  cases v
  dsimp only [SpatialTwist6D.add, SpatialTwist6D.zero]
  rw [Vec3.zero_add, Vec3.zero_add]

theorem SpatialTwist6D.add_assoc (u v w : SpatialTwist6D) :
    SpatialTwist6D.add (SpatialTwist6D.add u v) w =
      SpatialTwist6D.add u (SpatialTwist6D.add v w) := by
  cases u; cases v; cases w
  dsimp only [SpatialTwist6D.add]
  rw [Vec3.add_assoc, Vec3.add_assoc]

theorem SpatialTwist6D.scale_zero (s : Int) :
    SpatialTwist6D.scale s SpatialTwist6D.zero = SpatialTwist6D.zero := by
  dsimp only [SpatialTwist6D.scale, SpatialTwist6D.zero]
  rw [Vec3.scale_zero]

theorem SpatialTwist6D.scale_add (s : Int) (u v : SpatialTwist6D) :
    SpatialTwist6D.scale s (SpatialTwist6D.add u v) =
      SpatialTwist6D.add (SpatialTwist6D.scale s u) (SpatialTwist6D.scale s v) := by
  cases u; cases v
  dsimp only [SpatialTwist6D.scale, SpatialTwist6D.add]
  rw [Vec3.scale_add, Vec3.scale_add]

/-- **Serial Chain Twist Concatenation Additivity (`propagateSerialChainTwists_append`)**:
Propagating joint twists along a concatenated kinematic chain `chain1 ++ chain2` equals the
spatial sum of the sub-chain twists. -/
theorem propagateSerialChainTwists_append
    (chain1 chain2 : List SpatialTwist6D) :
    propagateSerialChainTwists (chain1 ++ chain2) =
      SpatialTwist6D.add (propagateSerialChainTwists chain1) (propagateSerialChainTwists chain2) := by
  induction chain1 with
  | nil =>
    dsimp only [List.nil_append, propagateSerialChainTwists]
    rw [SpatialTwist6D.zero_add]
  | cons v rest ih =>
    dsimp only [List.cons_append, propagateSerialChainTwists]
    rw [ih, SpatialTwist6D.add_assoc]

/-- **Serial Chain Twist Velocity Scaling Linearity (`propagateSerialChainTwists_scale`)**:
Uniformly scaling all joint twists in `chain` by `s` scales the propagated end-effector twist by `s`. -/
theorem propagateSerialChainTwists_scale
    (s : Int) (chain : List SpatialTwist6D) :
    propagateSerialChainTwists (chain.map (SpatialTwist6D.scale s)) =
      SpatialTwist6D.scale s (propagateSerialChainTwists chain) := by
  induction chain with
  | nil =>
    dsimp only [List.map, propagateSerialChainTwists]
    rw [SpatialTwist6D.scale_zero]
  | cons v rest ih =>
    dsimp only [List.map, propagateSerialChainTwists]
    rw [ih, SpatialTwist6D.scale_add]

theorem Vec3.add_comm (a b : Vec3) : Vec3.add a b = Vec3.add b a := by
  cases a; cases b
  dsimp only [Vec3.add]
  congr 1 <;> omega

theorem SpatialTwist6D.add_comm (u v : SpatialTwist6D) :
    SpatialTwist6D.add u v = SpatialTwist6D.add v u := by
  dsimp only [SpatialTwist6D.add]
  rw [Vec3.add_comm u.ang v.ang, Vec3.add_comm u.lin v.lin]

theorem SpatialTwist6D.add_add_add_comm (a b c d : SpatialTwist6D) :
    SpatialTwist6D.add (SpatialTwist6D.add a b) (SpatialTwist6D.add c d) =
      SpatialTwist6D.add (SpatialTwist6D.add a c) (SpatialTwist6D.add b d) := by
  rw [SpatialTwist6D.add_assoc, ← SpatialTwist6D.add_assoc b c d,
      SpatialTwist6D.add_comm b c, SpatialTwist6D.add_assoc c b d,
      ← SpatialTwist6D.add_assoc]

/-- **Pointwise Joint-Twist Superposition Additivity (`propagateSerialChainTwists_zipWith_add`)**:
For any two joint-twist profiles `chain1` and `chain2` of equal length (`chain1.length = chain2.length`),
propagating the pointwise sum `List.zipWith SpatialTwist6D.add chain1 chain2` equals the spatial sum
of the individually propagated end-effector twists. -/
theorem propagateSerialChainTwists_zipWith_add
    (chain1 chain2 : List SpatialTwist6D)
    (hLen : chain1.length = chain2.length) :
    propagateSerialChainTwists (List.zipWith SpatialTwist6D.add chain1 chain2) =
      SpatialTwist6D.add (propagateSerialChainTwists chain1) (propagateSerialChainTwists chain2) := by
  induction chain1 generalizing chain2 with
  | nil =>
    cases chain2 with
    | nil =>
      dsimp only [List.zipWith, propagateSerialChainTwists]
      rw [SpatialTwist6D.zero_add]
    | cons _ _ => contradiction
  | cons u1 rest1 ih =>
    cases chain2 with
    | nil => contradiction
    | cons u2 rest2 =>
      dsimp only [List.zipWith, propagateSerialChainTwists]
      have hRestLen : rest1.length = rest2.length := by
        simp only [List.length_cons] at hLen
        omega
      rw [ih rest2 hRestLen, SpatialTwist6D.add_add_add_comm]

/-- **Virtual Mechanical Power Additivity Across Serial Kinematic Chains
(`spatialPower_propagateSerialChainTwists_append`)**:
For any tip wrench `f` and concatenated serial twist chain `chain1 ++ chain2`, the virtual
mechanical power $\langle f, v_{\text{tip}} \rangle$ distributes additively across `chain1` and `chain2`. -/
theorem spatialPower_propagateSerialChainTwists_append
    (f : SpatialWrench6D) (chain1 chain2 : List SpatialTwist6D) :
    spatialPower f (propagateSerialChainTwists (chain1 ++ chain2)) =
      spatialPower f (propagateSerialChainTwists chain1) +
      spatialPower f (propagateSerialChainTwists chain2) := by
  rw [propagateSerialChainTwists_append, spatialPower_bilinear_add_right]


/-! ## 8. A five-axis post-processor with TCPM (`postNgc`) and the rotary-safety theorem

The CAM side (`Obend.Hardware.GeometryCAM`) produces cutter locations: a tip point in the part frame
and an integer tool axis. This section turns operations of such points into an NC program for an
A/C trunnion (C on the table about Z, A tilting the table about X, spindle fixed along machine +Z) in
the Fanuc 30i dialect with tool centre point management on (`G43.4 H…`): the control, not the post,
does the inverse kinematics, so the programmed X/Y/Z are tip coordinates in the part frame and
A/C only orient the tool. (Haas calls this `G234`, Heidenhain `M128`/`FUNCTION TCPM`, Siemens `TRAORI`.)

Each operation is 3+2: the tool axis is fixed while cutting, and the table re-orients only at the
clearance plane. `postMoves_rotarySafe` proves that of every program the post can emit: a feed never
changes the tool axis, and any move that does is a rapid between two points on or above the
clearance plane. The unwind the hand-written fidget program did (C from 345 to 0 under `G01` at
cutting depth) is therefore not expressible.

Angles are printed from the axis vector (`axisAnglesMilliDeg`, `Float`, printing only); A is the
tilt from +Z, C the azimuth of the tilt measured from +X. A machine whose rotary signs differ needs
those two lines changed, which is what a post's machine configuration is. -/

open Obend.Hardware.GeometryCAM (ToolAxis)

/-- A typed NC motion block; coordinates are lattice units of the part frame. -/
inductive NcMove where
  | rapid (x y z : Int) (axis : ToolAxis)
  | feed  (x y z : Int) (axis : ToolAxis) (mmPerMin : Nat)
  deriving DecidableEq, Repr

def NcMove.z : NcMove → Int
  | .rapid _ _ z _ => z
  | .feed _ _ z _ _ => z

def NcMove.axis : NcMove → ToolAxis
  | .rapid _ _ _ a => a
  | .feed _ _ _ a _ => a

def NcMove.isFeed : NcMove → Bool
  | .rapid .. => false
  | .feed .. => true

/-- A rapid at or above the clearance plane `clear`. -/
def NcMove.clearRapid (clear : Int) : NcMove → Bool
  | .rapid _ _ z _ => decide (clear ≤ z)
  | .feed .. => false

/-- Two consecutive moves are rotary-safe when the axis is unchanged, or when the second is a rapid
and both are on or above the clearance plane. -/
def movePairSafe (clear : Int) (m₁ m₂ : NcMove) : Bool :=
  m₂.axis == m₁.axis || (!m₂.isFeed && decide (clear ≤ m₁.z) && decide (clear ≤ m₂.z))

def movesRotarySafe (clear : Int) : List NcMove → Bool
  | m₁ :: m₂ :: rest => movePairSafe clear m₁ m₂ && movesRotarySafe clear (m₂ :: rest)
  | _ => true

/-- One 3+2 operation: a constant tool axis and the tip polyline to cut. -/
structure CamPass where
  axis : ToolAxis
  pts  : List (Int × Int × Int)
  deriving Repr

structure PostConfig where
  clearanceZ : Int
  plungeFeed : Nat
  cutFeed    : Nat
  spindleRpm : Nat
  tool       : Nat
  unitMicron : Nat
  deriving Repr

/-- Moves of one pass: rapid to above the first point (re-orienting there), plunge, cut, rapid
straight up to the clearance plane. -/
def passMoves (cfg : PostConfig) (p : CamPass) : List NcMove :=
  match p.pts with
  | [] => []
  | q :: rest =>
    let l := (q :: rest).getLast (List.cons_ne_nil _ _)
    .rapid q.1 q.2.1 cfg.clearanceZ p.axis :: .feed q.1 q.2.1 q.2.2 p.axis cfg.plungeFeed ::
      ((rest.map fun r => NcMove.feed r.1 r.2.1 r.2.2 p.axis cfg.cutFeed) ++
        [.rapid l.1 l.2.1 cfg.clearanceZ p.axis])

def postMoves (cfg : PostConfig) (passes : List CamPass) : List NcMove :=
  passes.flatMap (passMoves cfg)

theorem movesRotarySafe_of_sameAxis (clear : Int) (a : ToolAxis) :
    ∀ ms : List NcMove, (∀ m ∈ ms, m.axis = a) → movesRotarySafe clear ms = true
  | [] , _ => rfl
  | [_], _ => rfl
  | m₁ :: m₂ :: rest, h => by
    simp only [movesRotarySafe, Bool.and_eq_true]
    refine ⟨?_, movesRotarySafe_of_sameAxis clear a (m₂ :: rest) (fun m hm => h m (List.mem_cons_of_mem _ hm))⟩
    have h1 := h m₁ (List.mem_cons_self ..)
    have h2 := h m₂ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp [movePairSafe, h1, h2]

theorem movesRotarySafe_append (clear : Int) :
    ∀ (xs ys : List NcMove),
      movesRotarySafe clear xs = true → movesRotarySafe clear ys = true →
      (∀ m₁ m₂, xs.getLast? = some m₁ → ys.head? = some m₂ → movePairSafe clear m₁ m₂ = true) →
      movesRotarySafe clear (xs ++ ys) = true
  | [], _, _, hy, _ => by simpa using hy
  | [m], ys, _, hy, hb => by
    cases ys with
    | nil => rfl
    | cons n ys' =>
      simp only [List.cons_append, List.nil_append, movesRotarySafe, Bool.and_eq_true]
      exact ⟨hb m n rfl rfl, hy⟩
  | m₁ :: m₂ :: rest, ys, hx, hy, hb => by
    simp only [movesRotarySafe, Bool.and_eq_true] at hx
    simp only [List.cons_append, movesRotarySafe, Bool.and_eq_true]
    refine ⟨hx.1, ?_⟩
    have := movesRotarySafe_append clear (m₂ :: rest) ys hx.2 hy (by
      intro a b ha hbh
      exact hb a b (by simpa [List.getLast?_cons_cons] using ha) hbh)
    simpa using this

theorem passMoves_axis (cfg : PostConfig) (p : CamPass) : ∀ m ∈ passMoves cfg p, m.axis = p.axis := by
  unfold passMoves
  split
  · simp
  · intro m hm
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_singleton] at hm
    rcases hm with h | h | ⟨r, _, h⟩ | h | h <;> first | (subst h; rfl) | cases h

theorem passMoves_head (cfg : PostConfig) (p : CamPass) (m : NcMove)
    (h : (passMoves cfg p).head? = some m) : m.clearRapid cfg.clearanceZ = true := by
  unfold passMoves at h
  split at h
  · cases h
  · simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp [NcMove.clearRapid]

theorem passMoves_last (cfg : PostConfig) (p : CamPass) (m : NcMove)
    (h : (passMoves cfg p).getLast? = some m) : m.clearRapid cfg.clearanceZ = true := by
  unfold passMoves at h
  split at h
  · cases h
  · dsimp only at h
    rw [← List.cons_append, ← List.cons_append, List.getLast?_append] at h
    simp only [List.getLast?_singleton, Option.some_or, Option.some.injEq] at h
    subst h
    simp [NcMove.clearRapid]

theorem movePairSafe_of_clearRapid (clear : Int) (m₁ m₂ : NcMove)
    (h₁ : m₁.clearRapid clear = true) (h₂ : m₂.clearRapid clear = true) :
    movePairSafe clear m₁ m₂ = true := by
  cases m₁ <;> cases m₂ <;> simp_all [NcMove.clearRapid, movePairSafe, NcMove.isFeed, NcMove.z]

theorem postMoves_head (cfg : PostConfig) :
    ∀ (ps : List CamPass) (m : NcMove), (postMoves cfg ps).head? = some m →
      m.clearRapid cfg.clearanceZ = true
  | [], _, h => by cases h
  | p :: ps, m, h => by
    unfold postMoves at h
    rw [List.flatMap_cons] at h
    cases hp : passMoves cfg p with
    | nil => rw [hp, List.nil_append] at h; exact postMoves_head cfg ps m h
    | cons a l =>
      rw [hp, List.cons_append, List.head?_cons] at h
      exact passMoves_head cfg p m (by rw [hp]; exact h)

/-- **`postMoves_rotarySafe`**: every program the post emits is rotary-safe at its clearance plane,
for every list of operations. -/
theorem postMoves_rotarySafe (cfg : PostConfig) :
    ∀ ps : List CamPass, movesRotarySafe cfg.clearanceZ (postMoves cfg ps) = true
  | [] => rfl
  | p :: ps => by
    have hRest := postMoves_rotarySafe cfg ps
    unfold postMoves at hRest ⊢
    rw [List.flatMap_cons]
    refine movesRotarySafe_append _ _ _
      (movesRotarySafe_of_sameAxis _ p.axis _ (passMoves_axis cfg p)) hRest ?_
    intro m₁ m₂ h₁ h₂
    exact movePairSafe_of_clearRapid _ _ _ (passMoves_last cfg p m₁ h₁) (postMoves_head cfg ps m₂ h₂)

/-- A post that unwinds the rotaries at cutting depth: it re-orients on the plunge feed instead of on
the rapid above the first point. -/
def passMovesBroken (cfg : PostConfig) (p : CamPass) : List NcMove :=
  match p.pts with
  | [] => []
  | q :: rest =>
    .rapid q.1 q.2.1 cfg.clearanceZ ⟨0, 0, 1, 1⟩ :: .feed q.1 q.2.1 q.2.2 p.axis cfg.plungeFeed ::
      (rest.map fun r => NcMove.feed r.1 r.2.1 r.2.2 p.axis cfg.cutFeed)

#tooth postMoves_rotarySafe by mutation
  passMoves := passMovesBroken

/-- Every emitted program starts with a rapid at the clearance plane (so the first motion after the
tool change and `G43.4` is never a cut). -/
theorem postMoves_starts_clear (cfg : PostConfig) (ps : List CamPass) (m : NcMove)
    (h : (postMoves cfg ps).head? = some m) : m.clearRapid cfg.clearanceZ = true :=
  postMoves_head cfg ps m h

/-! ### Text -/

/-- Lattice units to millimetres with three decimals. -/
def fmtMm (unitMicron : Nat) (v : Int) : String :=
  let um := v * unitMicron
  let a := um.natAbs
  let frac := toString (a % 1000)
  let frac := String.ofList (List.replicate (3 - frac.length) '0') ++ frac
  (if um < 0 then "-" else "") ++ s!"{a / 1000}.{frac}"

/-- `Float` degrees with three decimals. -/
def fmtDeg (d : Float) : String :=
  let m := (d * 1000.0).round
  let neg := m < 0.0
  let a := (if neg then -m else m).toUInt64.toNat
  let frac := toString (a % 1000)
  let frac := String.ofList (List.replicate (3 - frac.length) '0') ++ frac
  (if neg && a != 0 then "-" else "") ++ s!"{a / 1000}.{frac}"

/-- Rotary angles that bring part-frame axis `u` onto the spindle: A the tilt from +Z, C the azimuth
of the tilt from +X (0 when the axis is vertical). -/
def axisAngles (u : ToolAxis) : Float × Float :=
  let n := Float.ofNat u.n
  let uz := Float.ofInt u.uz
  let a := Float.acos (uz / n) * 180.0 / 3.141592653589793
  let c := if u.ux == 0 && u.uy == 0 then 0.0
    else Float.atan2 (Float.ofInt u.uy) (Float.ofInt u.ux) * 180.0 / 3.141592653589793
  (a, c)

def NcMove.toLine (unitMicron : Nat) : NcMove → String
  | .rapid x y z a =>
    let (ad, cd) := axisAngles a
    s!"G00 X{fmtMm unitMicron x} Y{fmtMm unitMicron y} Z{fmtMm unitMicron z} A{fmtDeg ad} C{fmtDeg cd}"
  | .feed x y z a f =>
    let (ad, cd) := axisAngles a
    s!"G01 X{fmtMm unitMicron x} Y{fmtMm unitMicron y} Z{fmtMm unitMicron z} A{fmtDeg ad} C{fmtDeg cd} F{f}"

/-- The program text: safe start, tool change, spindle, TCPM on, the moves, TCPM off at the
clearance plane, machine-coordinate retract and rotary home, spindle off, end. The safe-start line
cancels any length offset before the tool change, where `G49` belongs; TCPM is cancelled by the
second `G49` only after the final rapid to clearance. -/
def postNgc (cfg : PostConfig) (title : String) (passes : List CamPass) : String :=
  let header :=
    [ "%"
    , s!"({title})"
    , "(Fanuc 30i dialect, A/C trunnion, tool centre point management G43.4)"
    , "G21 G90 G94 G17 G40 G80 G49"
    , s!"T{cfg.tool} M06"
    , "G54"
    , s!"S{cfg.spindleRpm} M03"
    , s!"G43.4 H{cfg.tool}" ]
  let body := (postMoves cfg passes).map (NcMove.toLine cfg.unitMicron)
  let footer := [ "G49", "G53 G00 Z0.", "G53 G00 A0. C0.", "M05", "M30", "%" ]
  String.intercalate "\n" (header ++ body ++ footer) ++ "\n"

end Obend.Hardware.Kinematics
end

