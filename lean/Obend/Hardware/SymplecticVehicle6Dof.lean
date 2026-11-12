module
public import Obend.Hardware.Kinematics
public import Obend.Analysis.Flowpipe
public import Obend.Judge.Class
import Std.Tactic
public section

/-! Exact rational discrete vehicle mechanics. No floating-point orthogonalization is used.
The thermal model has three unit-heat-capacity nodes and integrated heat/conductance inputs.
Radiation is to a zero-Kelvin sink; the CFL condition includes the explicit sink-energy budget.
Tank stations use a fixed body construction datum; moment arms subtract the recomputed CoM.
The pose position tracks the spatial CoM. Separation is the common-point lumped-stage model.
External force/torque and aerodynamic q/alpha are scenario inputs; axial load is checked against
integrator force. Corridor claims concern discrete samples, not continuous ODE trajectories.
The Array checker refines the linked List semantics, including the initial and final states. -/
namespace Obend.Hardware.SymplecticVehicle6Dof
set_option autoImplicit false

structure Vec3Q where
  x : Rat
  y : Rat
  z : Rat
  deriving DecidableEq, Repr

structure Mat3Q where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  e : Rat
  f : Rat
  g : Rat
  h : Rat
  i : Rat
  deriving DecidableEq, Repr

def zero : Vec3Q := ⟨0, 0, 0⟩
def add (u v : Vec3Q) : Vec3Q := ⟨u.x+v.x, u.y+v.y, u.z+v.z⟩
def sub (u v : Vec3Q) : Vec3Q := ⟨u.x-v.x, u.y-v.y, u.z-v.z⟩
def scale (s : Rat) (u : Vec3Q) : Vec3Q := ⟨s*u.x, s*u.y, s*u.z⟩
def dot (u v : Vec3Q) : Rat := u.x*v.x + u.y*v.y + u.z*v.z
def normSq (u : Vec3Q) : Rat := dot u u
def cross (u v : Vec3Q) : Vec3Q :=
  ⟨u.y*v.z-u.z*v.y, u.z*v.x-u.x*v.z, u.x*v.y-u.y*v.x⟩
def eye : Mat3Q := ⟨1,0,0,0,1,0,0,0,1⟩
def transpose (m : Mat3Q) : Mat3Q := ⟨m.a,m.d,m.g,m.b,m.e,m.h,m.c,m.f,m.i⟩
def matAdd (m n : Mat3Q) : Mat3Q :=
  ⟨m.a+n.a,m.b+n.b,m.c+n.c,m.d+n.d,m.e+n.e,m.f+n.f,m.g+n.g,m.h+n.h,m.i+n.i⟩
def matScale (s : Rat) (m : Mat3Q) : Mat3Q :=
  ⟨s*m.a,s*m.b,s*m.c,s*m.d,s*m.e,s*m.f,s*m.g,s*m.h,s*m.i⟩
def mul (m n : Mat3Q) : Mat3Q :=
  ⟨m.a*n.a+m.b*n.d+m.c*n.g, m.a*n.b+m.b*n.e+m.c*n.h, m.a*n.c+m.b*n.f+m.c*n.i,
   m.d*n.a+m.e*n.d+m.f*n.g, m.d*n.b+m.e*n.e+m.f*n.h, m.d*n.c+m.e*n.f+m.f*n.i,
   m.g*n.a+m.h*n.d+m.i*n.g, m.g*n.b+m.h*n.e+m.i*n.h, m.g*n.c+m.h*n.f+m.i*n.i⟩
def act (m : Mat3Q) (u : Vec3Q) : Vec3Q :=
  ⟨m.a*u.x+m.b*u.y+m.c*u.z,m.d*u.x+m.e*u.y+m.f*u.z,m.g*u.x+m.h*u.y+m.i*u.z⟩
def det3 (m : Mat3Q) : Rat :=
  m.a*(m.e*m.i-m.f*m.h)-m.b*(m.d*m.i-m.f*m.g)+m.c*(m.d*m.h-m.e*m.g)
def skew3 (u : Vec3Q) : Mat3Q := ⟨0,-u.z,u.y,u.z,0,-u.x,-u.y,u.x,0⟩
def outer (u : Vec3Q) : Mat3Q :=
  ⟨u.x*u.x,u.x*u.y,u.x*u.z,u.y*u.x,u.y*u.y,u.y*u.z,u.z*u.x,u.z*u.y,u.z*u.z⟩

theorem square_nonneg (x : Rat) : 0 ≤ x*x := by
  have h := Rat.nonneg_total x
  rcases h with h | h
  · exact Rat.mul_nonneg h h
  · have := Rat.mul_nonneg h h; grind

theorem normSq_nonneg (v : Vec3Q) : 0 ≤ normSq v := by
  have := square_nonneg v.x; have := square_nonneg v.y; have := square_nonneg v.z
  unfold normSq dot; grind

theorem mul_assoc (a b c : Mat3Q) : mul (mul a b) c = mul a (mul b c) := by
  simp only [mul]; congr 1 <;> grind

theorem transpose_mul (a b : Mat3Q) : transpose (mul a b) = mul (transpose b) (transpose a) := by
  simp only [mul, transpose]; congr 1 <;> grind

theorem mul_eye (a : Mat3Q) : mul a eye = a := by
  cases a; simp [mul, eye] <;> grind
theorem eye_mul (a : Mat3Q) : mul eye a = a := by
  cases a; simp [mul, eye] <;> grind
theorem act_mul (a b : Mat3Q) (v : Vec3Q) : act (mul a b) v = act a (act b v) := by
  simp only [act, mul]; congr 1 <;> grind
theorem act_eye (v : Vec3Q) : act eye v = v := by
  cases v; simp [act, eye] <;> grind
theorem dot_adjoint (a : Mat3Q) (u v : Vec3Q) : dot (act a u) v = dot u (act (transpose a) v) := by
  simp only [dot, act, transpose]; grind

theorem det3_mul (a b : Mat3Q) : det3 (mul a b) = det3 a * det3 b := by
  simp only [det3, mul]; grind

@[expose] def SO3 (r : Mat3Q) : Prop := mul (transpose r) r = eye ∧ det3 r = 1
instance (r : Mat3Q) : Decidable (SO3 r) := by unfold SO3; infer_instance

def cayleyDenom (u : Vec3Q) : Rat := 1 + normSq u
/-- Numerator of (I - hat u)(I + hat u)⁻¹, with the negative hat convention. -/
def cayleyNumerator (u : Vec3Q) : Mat3Q :=
  matAdd (matAdd (matScale (1-normSq u) eye) (matScale (-2) (skew3 u)))
    (matScale 2 (outer u))
def cayleyDelta (u : Vec3Q) : Mat3Q := matScale (cayleyDenom u)⁻¹ (cayleyNumerator u)

theorem cayleyDelta_denom_pos (u : Vec3Q) : 0 < cayleyDenom u := by
  have := normSq_nonneg u; unfold cayleyDenom; grind

theorem cayleyNumerator_orthogonal (u : Vec3Q) :
    mul (transpose (cayleyNumerator u)) (cayleyNumerator u) =
      matScale (cayleyDenom u * cayleyDenom u) eye := by
  simp only [cayleyNumerator, cayleyDenom, normSq, dot, matAdd, matScale, skew3, outer, eye, mul, transpose]
  congr 1 <;> grind

theorem cayleyNumerator_det (u : Vec3Q) :
    det3 (cayleyNumerator u) = cayleyDenom u * cayleyDenom u * cayleyDenom u := by
  simp only [cayleyNumerator, cayleyDenom, normSq, dot, matAdd, matScale, skew3, outer, eye, det3]
  grind

theorem scale_orthogonal (s : Rat) (m : Mat3Q) :
    mul (transpose (matScale s m)) (matScale s m) = matScale (s*s) (mul (transpose m) m) := by
  simp only [matScale, mul, transpose]; congr 1 <;> grind

theorem det3_scale (s : Rat) (m : Mat3Q) : det3 (matScale s m) = s*s*s*det3 m := by
  simp only [det3, matScale]; grind

theorem cayleyDelta_so3 (u : Vec3Q) : SO3 (cayleyDelta u) := by
  have hi := Rat.inv_mul_cancel (cayleyDenom u) (Rat.ne_of_gt (cayleyDelta_denom_pos u))
  constructor
  · rw [cayleyDelta, scale_orthogonal, cayleyNumerator_orthogonal]
    simp only [matScale, eye]; congr 1 <;> grind
  · rw [cayleyDelta, det3_scale, cayleyNumerator_det]; grind

theorem cayleyDelta_right_inverse (u : Vec3Q) :
    mul (cayleyDelta u) (transpose (cayleyDelta u)) = eye := by
  have hi := Rat.inv_mul_cancel (cayleyDenom u) (Rat.ne_of_gt (cayleyDelta_denom_pos u))
  simp only [cayleyDelta, cayleyNumerator, matScale, matAdd, eye, skew3, outer, mul, transpose]
  simp only [cayleyDenom, normSq, dot] at hi ⊢
  congr 1 <;> grind

theorem cayleyDelta_equation (u : Vec3Q) :
    mul (matAdd eye (skew3 u)) (cayleyDelta u) = matAdd eye (matScale (-1) (skew3 u)) := by
  have hi := Rat.inv_mul_cancel (cayleyDenom u) (Rat.ne_of_gt (cayleyDelta_denom_pos u))
  simp only [cayleyDelta, cayleyNumerator, matScale, matAdd, eye, skew3, outer, mul]
  simp only [cayleyDenom, normSq, dot] at hi ⊢
  congr 1 <;> grind

def cayleyStep (r : Mat3Q) (u : Vec3Q) : Mat3Q := mul r (cayleyDelta u)
theorem cayleyStep_exact_orthogonality (r : Mat3Q) (u : Vec3Q) (hr : SO3 r) :
    SO3 (cayleyStep r u) := by
  have hd := cayleyDelta_so3 u
  constructor
  · simp only [cayleyStep, transpose_mul, mul_assoc]
    rw [← mul_assoc (transpose r), hr.1, eye_mul, hd.1]
  · rw [cayleyStep, det3_mul, hr.2, hd.2]; grind

def cayleyTrace (r : Mat3Q) : List Vec3Q → Mat3Q
  | [] => r
  | u :: us => cayleyTrace (cayleyStep r u) us

theorem cayleyTrace_exact_so3 (us : List Vec3Q) (r : Mat3Q) (hr : SO3 r) : SO3 (cayleyTrace r us) := by
  induction us generalizing r with
  | nil => exact hr
  | cons u us ih => exact ih _ (cayleyStep_exact_orthogonality r u hr)

def eulerAttitude (r : Mat3Q) (u : Vec3Q) : Mat3Q := mul r (matAdd eye (skew3 u))

theorem eulerAttitude_drifts_off_so3 (r : Mat3Q) (u : Vec3Q)
    (hr : SO3 r) (hu : u ≠ zero) :
    mul (transpose (eulerAttitude r u)) (eulerAttitude r u) ≠ eye := by
  intro h
  simp only [eulerAttitude, transpose_mul, mul_assoc] at h
  rw [← mul_assoc (transpose r), hr.1, eye_mul] at h
  have hx := congrArg Mat3Q.a h
  have hy := congrArg Mat3Q.e h
  have hz := congrArg Mat3Q.i h
  simp only [mul, transpose, matAdd, eye, skew3] at hx hy hz
  have := square_nonneg u.x; have := square_nonneg u.y; have := square_nonneg u.z
  have hxx : u.x*u.x = 0 := by grind
  have hyy : u.y*u.y = 0 := by grind
  have hzz : u.z*u.z = 0 := by grind
  have ux : u.x = 0 := by grind
  have uy : u.y = 0 := by grind
  have uz : u.z = 0 := by grind
  apply hu; cases u; simp_all [zero]

structure RigidBody where
  attitude : Mat3Q
  bodyMomentum : Vec3Q
  deriving DecidableEq, Repr

def freeRigidBody (s : RigidBody) (u : Vec3Q) : RigidBody :=
  ⟨cayleyStep s.attitude u, act (transpose (cayleyDelta u)) s.bodyMomentum⟩
def spatialMomentum (s : RigidBody) : Vec3Q := act s.attitude s.bodyMomentum

theorem freeRigidBody_conserves_spatial_momentum (s : RigidBody) (u : Vec3Q) :
    spatialMomentum (freeRigidBody s u) = spatialMomentum s ∧
    normSq (freeRigidBody s u).bodyMomentum = normSq s.bodyMomentum := by
  constructor
  · simp only [spatialMomentum, freeRigidBody, cayleyStep]
    rw [act_mul, ← act_mul (cayleyDelta u), cayleyDelta_right_inverse, act_eye]
  · simp only [normSq, freeRigidBody, dot_adjoint]
    have htt (m : Mat3Q) : transpose (transpose m) = m := by cases m; rfl
    rw [htt, ← act_mul, cayleyDelta_right_inverse, act_eye]

def freeRigidTrace (s : RigidBody) : List Vec3Q → RigidBody
  | [] => s
  | u :: us => freeRigidTrace (freeRigidBody s u) us

theorem freeRigidTrace_conserves (us : List Vec3Q) (s : RigidBody) :
    spatialMomentum (freeRigidTrace s us) = spatialMomentum s ∧
    normSq (freeRigidTrace s us).bodyMomentum = normSq s.bodyMomentum := by
  induction us generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons u us ih =>
    obtain ⟨hp, hn⟩ := ih (freeRigidBody s u)
    obtain ⟨sp, sn⟩ := freeRigidBody_conserves_spatial_momentum s u
    exact ⟨hp.trans sp, hn.trans sn⟩

structure Pose where
  rotation : Mat3Q
  pos : Vec3Q
  deriving DecidableEq, Repr

def transformPoint (p : Pose) (v : Vec3Q) : Vec3Q := add (act p.rotation v) p.pos
/-- Exact embedding of the existing integer-scaled spatial-vector convention. -/
def fromKinematics (v : Kinematics.Vec3) : Vec3Q := ⟨v.x, v.y, v.z⟩
def transformKinematicPoint (p : Pose) (v : Kinematics.Vec3) : Vec3Q := transformPoint p (fromKinematics v)
theorem fromKinematics_add (u v : Kinematics.Vec3) :
    fromKinematics (Kinematics.Vec3.add u v) = add (fromKinematics u) (fromKinematics v) := by
  simp only [fromKinematics, Kinematics.Vec3.add, add, Rat.intCast_add]

structure PointMass where
  mass : Rat
  station : Vec3Q
  deriving DecidableEq, Repr

def totalMass (dry : PointMass) (tanks : List PointMass) : Rat :=
  dry.mass + (tanks.map PointMass.mass).sum
def firstMoment : List PointMass → Vec3Q
  | [] => zero
  | p :: ps => add (scale p.mass p.station) (firstMoment ps)
def centerOfMass (dry : PointMass) (tanks : List PointMass) : Vec3Q :=
  scale (totalMass dry tanks)⁻¹ (firstMoment (dry :: tanks))

def parallelAxis (r : Vec3Q) : Mat3Q := matAdd (matScale (normSq r) eye) (matScale (-1) (outer r))
def compositeInertia (base : Mat3Q) (com : Vec3Q) : List PointMass → Mat3Q
  | [] => base
  | p :: ps => matAdd (matScale p.mass (parallelAxis (sub p.station com))) (compositeInertia base com ps)
structure SPD (m : Mat3Q) : Prop where
  symmetric : transpose m = m
  positive : ∀ v : Vec3Q, v ≠ zero → 0 < dot v (act m v)

theorem lagrange_identity (r v : Vec3Q) :
    normSq r * normSq v - dot r v * dot r v = normSq (cross r v) := by
  simp only [normSq, dot, cross]; grind

theorem parallelAxis_quadratic (r v : Vec3Q) :
    dot v (act (parallelAxis r) v) = normSq (cross r v) := by
  rw [← lagrange_identity]
  simp only [dot, act, parallelAxis, matAdd, matScale, eye, normSq, outer]; grind

theorem compositeInertia_symmetric (base : Mat3Q) (com : Vec3Q) (ps : List PointMass)
    (hb : transpose base = base) : transpose (compositeInertia base com ps) = compositeInertia base com ps := by
  induction ps with
  | nil => exact hb
  | cons p ps ih =>
    have hadd (a b : Mat3Q) : transpose (matAdd a b) = matAdd (transpose a) (transpose b) := rfl
    simp only [compositeInertia, hadd, ih]
    congr 1
    simp only [transpose, matScale, parallelAxis, matAdd, eye, outer]; congr 1 <;> grind

theorem quadratic_add (a b : Mat3Q) (v : Vec3Q) :
    dot v (act (matAdd a b) v) = dot v (act a v) + dot v (act b v) := by
  simp only [dot, act, matAdd]; grind

theorem quadratic_scale (s : Rat) (a : Mat3Q) (v : Vec3Q) :
    dot v (act (matScale s a) v) = s * dot v (act a v) := by
  simp only [dot, act, matScale]; grind

theorem compositeInertia_lower_bound (base : Mat3Q) (com : Vec3Q) (ps : List PointMass)
    (hm : ∀ p ∈ ps, 0 ≤ p.mass) (v : Vec3Q) :
    dot v (act base v) ≤ dot v (act (compositeInertia base com ps) v) := by
  induction ps with
  | nil => exact Rat.le_refl
  | cons p ps ih =>
    have hp := hm p (by simp)
    have hi := ih (fun q hq => hm q (by simp [hq]))
    have hn := Rat.mul_nonneg hp (normSq_nonneg (cross (sub p.station com) v))
    simp only [compositeInertia, quadratic_add, quadratic_scale, parallelAxis_quadratic]
    grind

theorem compositeInertia_spd (base : Mat3Q) (com : Vec3Q) (ps : List PointMass)
    (hb : SPD base) (hm : ∀ p ∈ ps, 0 ≤ p.mass) : SPD (compositeInertia base com ps) := by
  refine ⟨compositeInertia_symmetric base com ps hb.symmetric, ?_⟩
  intro v hv
  have := compositeInertia_lower_bound base com ps hm v
  have := hb.positive v hv
  grind

structure TankState where
  oxidizer : Rat
  fuel : Rat
  station : Vec3Q
  pressure : Rat
  deriving DecidableEq, Repr
structure TankDraw where
  oxidizer : Rat
  fuel : Rat
  deriving DecidableEq, Repr

def tankPointMass (t : TankState) : PointMass := ⟨t.oxidizer+t.fuel,t.station⟩
def depleteTank (t : TankState) (d : TankDraw) : TankState :=
  { t with oxidizer := t.oxidizer-d.oxidizer, fuel := t.fuel-d.fuel }
@[expose] def DrawValid (t : TankState) (d : TankDraw) : Prop :=
  0 ≤ d.oxidizer ∧ d.oxidizer ≤ t.oxidizer ∧ 0 ≤ d.fuel ∧ d.fuel ≤ t.fuel
instance (t : TankState) (d : TankDraw) : Decidable (DrawValid t d) := by unfold DrawValid; infer_instance

theorem depleteTank_nonneg (t : TankState) (d : TankDraw) (h : DrawValid t d) :
    0 ≤ (depleteTank t d).oxidizer ∧ 0 ≤ (depleteTank t d).fuel ∧
    (tankPointMass (depleteTank t d)).mass ≤ (tankPointMass t).mass := by
  simp only [depleteTank, tankPointMass]; unfold DrawValid at h; grind

def drawTanks (ts : List TankState) (ds : List TankDraw) : List TankState := List.zipWith depleteTank ts ds

def nozzleThrust (flow exhaust exitPressure ambient area : Rat) : Rat :=
  flow * exhaust + (exitPressure-ambient)*area

def gimbalDirection (u : Vec3Q) : Vec3Q := act (cayleyDelta u) ⟨0,0,1⟩
theorem gimbalDirection_unit (u : Vec3Q) : normSq (gimbalDirection u) = 1 := by
  simp only [gimbalDirection, normSq, dot_adjoint]
  rw [← act_mul, (cayleyDelta_so3 u).1, act_eye]
  simp only [dot]; grind

structure StageBody where
  mass : Rat
  momentum : Vec3Q
  pos : Vec3Q
  deriving DecidableEq, Repr
/-- Split at a common separation point. Velocities may jump; position cannot. -/
def separateStage (pre : StageBody) (upperMass : Rat) (impulse : Vec3Q) : StageBody × StageBody :=
  (⟨upperMass, add (scale (upperMass/pre.mass) pre.momentum) impulse, pre.pos⟩,
   ⟨pre.mass-upperMass, sub pre.momentum (add (scale (upperMass/pre.mass) pre.momentum) impulse), pre.pos⟩)

def pairCOM (a b : StageBody) : Vec3Q :=
  scale (a.mass+b.mass)⁻¹ (add (scale a.mass a.pos) (scale b.mass b.pos))

theorem staging_conserves_total_mass_and_linear_momentum
    (pre : StageBody) (m : Rat) (impulse : Vec3Q) (hp : 0 < pre.mass) :
    let (a,b) := separateStage pre m impulse
    a.mass+b.mass = pre.mass ∧ add a.momentum b.momentum = pre.momentum ∧ pairCOM a b = pre.pos := by
  have hi := Rat.inv_mul_cancel pre.mass (Rat.ne_of_gt hp)
  dsimp only [separateStage]
  refine ⟨by grind, ?_, ?_⟩
  · cases pre.momentum
    simp only [add, sub, scale]; congr 1 <;> grind
  · simp only [pairCOM, add, scale]
    have he : m + (pre.mass-m) = pre.mass := by grind
    rw [he]; cases pre.pos; congr 1 <;> grind

structure ThermalState where
  kelvin : Vec3Q
  ablator : Rat
  deriving DecidableEq, Repr
structure ThermalCommand where
  /-- Integrated conductances, divided by unit nodal heat capacity. -/
  outerBond : Rat
  bondWall : Rat
  aero : Rat
  /-- Integrated Stefan–Boltzmann coefficient dt * sigma * emissivity * area. -/
  radiation : Rat
  latent : Rat
  recession : Rat
  deriving DecidableEq, Repr

def radiationLoss (c : ThermalCommand) (s : ThermalState) : Rat :=
  c.radiation * (s.kelvin.x*s.kelvin.x) * (s.kelvin.x*s.kelvin.x)
def shieldLoss (c : ThermalCommand) (s : ThermalState) : Rat := radiationLoss c s + c.latent*c.recession

def stepThermalNetwork (s : ThermalState) (c : ThermalCommand) : ThermalState :=
  ⟨⟨s.kelvin.x+c.outerBond*(s.kelvin.y-s.kelvin.x)+c.aero-shieldLoss c s,
     s.kelvin.y+c.outerBond*(s.kelvin.x-s.kelvin.y)+c.bondWall*(s.kelvin.z-s.kelvin.y),
     s.kelvin.z+c.bondWall*(s.kelvin.y-s.kelvin.z)⟩, s.ablator-c.recession⟩

@[expose] def ThermalCFL (s : ThermalState) (c : ThermalCommand) : Prop :=
  0 ≤ c.outerBond ∧ 0 ≤ c.bondWall ∧ c.outerBond+c.bondWall ≤ 1 ∧
  0 ≤ c.aero ∧ 0 ≤ c.radiation ∧ 0 ≤ c.latent ∧ 0 ≤ c.recession ∧ c.recession ≤ s.ablator ∧
  shieldLoss c s ≤ (1-c.outerBond)*s.kelvin.x+c.aero
instance (s : ThermalState) (c : ThermalCommand) : Decidable (ThermalCFL s c) := by
  unfold ThermalCFL; infer_instance

@[expose] def Nonneg3 (v : Vec3Q) : Prop := 0 ≤ v.x ∧ 0 ≤ v.y ∧ 0 ≤ v.z
instance (v : Vec3Q) : Decidable (Nonneg3 v) := by unfold Nonneg3; infer_instance

theorem stepThermalNetwork_nonneg_kelvin (s : ThermalState) (c : ThermalCommand)
    (ht : Nonneg3 s.kelvin) (hc : ThermalCFL s c) :
    Nonneg3 (stepThermalNetwork s c).kelvin ∧ 0 ≤ (stepThermalNetwork s c).ablator := by
  obtain ⟨hg, hh, hsum, ha, _, _, _, hm, hloss⟩ := hc
  have hgy := Rat.mul_nonneg hg ht.2.1
  have hgx := Rat.mul_nonneg hg ht.1
  have hhz := Rat.mul_nonneg hh ht.2.2
  have hhy := Rat.mul_nonneg hh ht.2.1
  have hmid := Rat.mul_nonneg (show 0 ≤ 1-c.outerBond-c.bondWall by grind) ht.2.1
  have hwall := Rat.mul_nonneg (show 0 ≤ 1-c.bondWall by grind) ht.2.2
  simp only [stepThermalNetwork, Nonneg3]; grind

def thermalEnergy (s : ThermalState) : Rat := s.kelvin.x+s.kelvin.y+s.kelvin.z

theorem stepThermalNetwork_energy_balance (s : ThermalState) (c : ThermalCommand) :
    thermalEnergy (stepThermalNetwork s c) = thermalEnergy s+c.aero-shieldLoss c s := by
  simp only [thermalEnergy, stepThermalNetwork]; grind

theorem stepThermalNetwork_passive (s : ThermalState) (c : ThermalCommand)
    (hc : ThermalCFL s c) (ha : c.aero = 0) : thermalEnergy (stepThermalNetwork s c) ≤ thermalEnergy s := by
  have hr := Rat.mul_nonneg (Rat.mul_nonneg hc.2.2.2.2.1 (square_nonneg s.kelvin.x)) (square_nonneg s.kelvin.x)
  have hl := Rat.mul_nonneg hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1
  rw [stepThermalNetwork_energy_balance]; simp only [shieldLoss, radiationLoss]; grind

structure StructuralLoad where
  dynamicPressure : Rat
  incidenceMagnitude : Rat
  lever : Rat
  axialForceMagnitude : Rat
  capacity : Rat
  minimumFactor : Rat
  deriving DecidableEq, Repr

def structuralDemand (l : StructuralLoad) : Rat := l.dynamicPressure*l.incidenceMagnitude*l.lever+l.axialForceMagnitude
@[expose] def StructuralSafe (l : StructuralLoad) : Prop :=
  0 ≤ l.dynamicPressure ∧ 0 ≤ l.incidenceMagnitude ∧ 0 ≤ l.lever ∧ 0 ≤ l.axialForceMagnitude ∧
  0 < l.capacity ∧ 1 ≤ l.minimumFactor ∧ l.minimumFactor*structuralDemand l ≤ l.capacity
instance (l : StructuralLoad) : Decidable (StructuralSafe l) := by unfold StructuralSafe; infer_instance

theorem structural_margin_sound (l : StructuralLoad) (h : StructuralSafe l) (hd : 0 < structuralDemand l) :
    l.minimumFactor ≤ l.capacity / structuralDemand l := by
  have hi := Rat.inv_mul_cancel (structuralDemand l) (Rat.ne_of_gt hd)
  have hn : 0 ≤ (structuralDemand l)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hd)
  have hm := Rat.mul_le_mul_of_nonneg_right h.2.2.2.2.2.2 hn
  have he : l.minimumFactor * structuralDemand l * (structuralDemand l)⁻¹ = l.minimumFactor := by grind
  rw [he] at hm
  simpa only [Rat.div_def] using hm

structure Box3Q where
  x : Analysis.Interval
  y : Analysis.Interval
  z : Analysis.Interval
  deriving DecidableEq, Repr

@[expose] def InBox (v : Vec3Q) (b : Box3Q) : Prop := v.x ∈ b.x ∧ v.y ∈ b.y ∧ v.z ∈ b.z
private instance (v : Vec3Q) (b : Box3Q) : Decidable (InBox v b) := by unfold InBox; infer_instance

def discreteFlowpipe (p v : Vec3Q) (dt : Rat) : Box3Q :=
  ⟨Analysis.stepFlowpipe1D (.ofPoint p.x) (.ofPoint v.x) dt (.ofPoint 0),
   Analysis.stepFlowpipe1D (.ofPoint p.y) (.ofPoint v.y) dt (.ofPoint 0),
   Analysis.stepFlowpipe1D (.ofPoint p.z) (.ofPoint v.z) dt (.ofPoint 0)⟩

theorem discreteFlowpipe_encloses (p v : Vec3Q) (dt : Rat) : InBox (add p (scale dt v)) (discreteFlowpipe p v dt) := by
  have hx := Analysis.stepFlowpipe1D_mem dt (Analysis.Interval.ofPoint_mem p.x)
    (Analysis.Interval.ofPoint_mem v.x) (Analysis.Interval.ofPoint_mem 0)
  have hy := Analysis.stepFlowpipe1D_mem dt (Analysis.Interval.ofPoint_mem p.y)
    (Analysis.Interval.ofPoint_mem v.y) (Analysis.Interval.ofPoint_mem 0)
  have hz := Analysis.stepFlowpipe1D_mem dt (Analysis.Interval.ofPoint_mem p.z)
    (Analysis.Interval.ofPoint_mem v.z) (Analysis.Interval.ofPoint_mem 0)
  simpa only [Rat.add_zero, InBox, add, scale, discreteFlowpipe] using And.intro hx (And.intro hy hz)

structure VehiclePolicy where
  corridor : Box3Q
  maxKelvin : Vec3Q
  minimumAblator : Rat
  feedFloor : Rat
  mixtureMin : Rat
  mixtureMax : Rat
  gimbalCosMin : Rat
  structuralCapacity : Rat
  minimumFactor : Rat
  bendingLever : Rat
  deriving DecidableEq, Repr

structure VehicleState where
  pose : Pose
  bodyMomentum : Vec3Q
  momentum : Vec3Q
  dry : PointMass
  /-- Principal dry inertia about its own center, strictly positive in safe states. -/
  dryInertia : Vec3Q
  tanks : List TankState
  thermal : ThermalState
  deriving DecidableEq, Repr

/-- The shield is a point mass at the dry reference station, in addition to the tanks. -/
def variableMasses (s : VehicleState) : List PointMass :=
  ⟨s.thermal.ablator,s.dry.station⟩ :: s.tanks.map tankPointMass
def vehicleMass (s : VehicleState) : Rat := totalMass s.dry (variableMasses s)
def vehicleCOM (s : VehicleState) : Vec3Q := centerOfMass s.dry (variableMasses s)
def diagonal (v : Vec3Q) : Mat3Q := ⟨v.x,0,0,0,v.y,0,0,0,v.z⟩
def vehicleInertia (s : VehicleState) : Mat3Q :=
  compositeInertia (diagonal s.dryInertia) (vehicleCOM s) (s.dry :: variableMasses s)

structure Separation where
  upperDryMass : Rat
  upperDryInertia : Vec3Q
  impulse : Vec3Q
  jettison : StageBody
  deriving DecidableEq, Repr

structure VehicleCommand where
  dt : Rat
  omega : Vec3Q
  increment : Vec3Q
  draws : List TankDraw
  exhaust : Rat
  exitPressure : Rat
  ambientPressure : Rat
  exitArea : Rat
  gimbal : Vec3Q
  nozzleStation : Vec3Q
  externalForce : Vec3Q
  externalTorque : Vec3Q
  heat : ThermalCommand
  load : StructuralLoad
  separation : Option Separation
  deriving DecidableEq, Repr

def consumedOx (c : VehicleCommand) : Rat := (c.draws.map TankDraw.oxidizer).sum
def consumedFuel (c : VehicleCommand) : Rat := (c.draws.map TankDraw.fuel).sum
def bodyThrust (c : VehicleCommand) : Vec3Q :=
  scale (nozzleThrust ((consumedOx c+consumedFuel c)/c.dt) c.exhaust c.exitPressure c.ambientPressure c.exitArea)
    (gimbalDirection c.gimbal)

def resultantForce (s : VehicleState) (c : VehicleCommand) : Vec3Q :=
  add (act s.pose.rotation (bodyThrust c)) c.externalForce
/-- Body-axis load implied by the force used by the translational integrator. -/
def axialDemand (s : VehicleState) (c : VehicleCommand) : Rat :=
  Analysis.ratAbs (act (transpose s.pose.rotation) (resultantForce s c)).z

def poweredStep (s : VehicleState) (c : VehicleCommand) : VehicleState :=
  let ts := drawTanks s.tanks c.draws
  let thermal := stepThermalNetwork s.thermal c.heat
  let m := totalMass s.dry (⟨thermal.ablator,s.dry.station⟩ :: ts.map tankPointMass)
  let force := resultantForce s c
  -- Lost material carries the old translational velocity; thrust supplies relative exhaust impulse.
  let p := add (scale (m/vehicleMass s) s.momentum) (scale c.dt force)
  let torque := add (cross (sub c.nozzleStation (vehicleCOM s)) (bodyThrust c)) c.externalTorque
  { s with
    pose := ⟨cayleyStep s.pose.rotation c.increment, add s.pose.pos (scale c.dt (scale m⁻¹ p))⟩
    bodyMomentum := act (transpose (cayleyDelta c.increment)) (add s.bodyMomentum (scale c.dt torque))
    momentum := p
    tanks := ts
    thermal := thermal }

def stageView (s : VehicleState) : StageBody := ⟨vehicleMass s, s.momentum, s.pose.pos⟩

def stepVehicle (s : VehicleState) (c : VehicleCommand) : VehicleState :=
  let p := poweredStep s c
  match c.separation with
  | none => p
  | some sep =>
    let upperMass := sep.upperDryMass + ((variableMasses p).map PointMass.mass).sum
    let pair := separateStage (stageView p) upperMass sep.impulse
    { p with dry := { p.dry with mass := sep.upperDryMass }
             dryInertia := sep.upperDryInertia
             momentum := pair.1.momentum }

structure VehicleTurn where
  command : VehicleCommand
  after : VehicleState
  deriving DecidableEq, Repr

/-- State safety is independent of the checker; constraints include the initial state. -/
@[expose] def StateSafe (p : VehiclePolicy) (s : VehicleState) : Prop :=
  SO3 s.pose.rotation ∧ 0 < s.dry.mass ∧
  (∀ t ∈ s.tanks, 0 ≤ t.oxidizer ∧ 0 ≤ t.fuel) ∧
  0 < s.dryInertia.x ∧ 0 < s.dryInertia.y ∧ 0 < s.dryInertia.z ∧
  Nonneg3 s.thermal.kelvin ∧ s.thermal.kelvin.x ≤ p.maxKelvin.x ∧
  s.thermal.kelvin.y ≤ p.maxKelvin.y ∧ s.thermal.kelvin.z ≤ p.maxKelvin.z ∧
  0 ≤ p.minimumAblator ∧ p.minimumAblator < s.thermal.ablator ∧ InBox s.pose.pos p.corridor
private instance (p : VehiclePolicy) (s : VehicleState) : Decidable (StateSafe p s) := by
  unfold StateSafe; infer_instance

theorem square_positive (x : Rat) (hx : x ≠ 0) : 0 < x*x := by
  have hn := square_nonneg x
  have he : x*x ≠ 0 := by intro h; apply hx; grind
  exact Rat.lt_of_le_of_ne hn (Ne.symm he)

theorem diagonal_spd (d : Vec3Q) (hx : 0 < d.x) (hy : 0 < d.y) (hz : 0 < d.z) : SPD (diagonal d) := by
  refine ⟨rfl, ?_⟩
  intro v hv
  have he : dot v (act (diagonal d) v) = d.x*(v.x*v.x)+d.y*(v.y*v.y)+d.z*(v.z*v.z) := by
    simp only [dot, act, diagonal]; grind
  rw [he]
  have hxx := Rat.mul_nonneg (Rat.le_of_lt hx) (square_nonneg v.x)
  have hyy := Rat.mul_nonneg (Rat.le_of_lt hy) (square_nonneg v.y)
  have hzz := Rat.mul_nonneg (Rat.le_of_lt hz) (square_nonneg v.z)
  by_cases vx : v.x = 0
  · by_cases vy : v.y = 0
    · have vz : v.z ≠ 0 := by intro vz; apply hv; cases v; simp_all [zero]
      have := Rat.mul_pos hz (square_positive v.z vz); grind
    · have := Rat.mul_pos hy (square_positive v.y vy); grind
  · have := Rat.mul_pos hx (square_positive v.x vx); grind

theorem vehicleInertia_spd (p : VehiclePolicy) (s : VehicleState) (h : StateSafe p s) : SPD (vehicleInertia s) := by
  apply compositeInertia_spd
  · exact diagonal_spd s.dryInertia h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
  · intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst q; exact Rat.le_of_lt h.2.1
    · simp only [variableMasses, List.mem_cons, List.mem_map] at hq
      rcases hq with he | ⟨t,ht,he⟩
      · subst q
        have hmin := h.2.2.2.2.2.2.2.2.2.2.1
        have hab := h.2.2.2.2.2.2.2.2.2.2.2.1
        dsimp; grind
      · subst q
        have ht := h.2.2.1 t ht
        exact Rat.add_nonneg ht.1 ht.2

/-- The endpoint tube is computed by the shared Flowpipe interval operation. -/
theorem poweredStep_flowpipe (s : VehicleState) (c : VehicleCommand) :
    InBox (poweredStep s c).pose.pos
      (discreteFlowpipe s.pose.pos
        (scale (vehicleMass (poweredStep s c))⁻¹ (poweredStep s c).momentum) c.dt) := by
  exact discreteFlowpipe_encloses _ _ _

def checkState (p : VehiclePolicy) (s : VehicleState) : Bool := decide (StateSafe p s)

@[expose] def PropulsionSafe (p : VehiclePolicy) (s : VehicleState) (c : VehicleCommand) : Prop :=
  0 < c.dt ∧ 0 ≤ c.exhaust ∧ 0 ≤ c.exitArea ∧ 0 ≤ c.ambientPressure ∧ c.ambientPressure ≤ c.exitPressure ∧
  0 ≤ p.mixtureMin ∧ p.mixtureMin ≤ p.mixtureMax ∧
  p.mixtureMin*consumedFuel c ≤ consumedOx c ∧ consumedOx c ≤ p.mixtureMax*consumedFuel c ∧
  0 ≤ p.feedFloor ∧ (∀ t ∈ s.tanks, p.feedFloor ≤ t.pressure) ∧
  0 ≤ p.gimbalCosMin ∧ p.gimbalCosMin ≤ 1 ∧ p.gimbalCosMin ≤ (gimbalDirection c.gimbal).z
private instance (p : VehiclePolicy) (s : VehicleState) (c : VehicleCommand) : Decidable (PropulsionSafe p s c) := by
  unfold PropulsionSafe; infer_instance

@[expose] def StageConserved (s : VehicleState) (t : VehicleTurn) : Prop :=
  match t.command.separation with
  | none => t.after.dry = s.dry ∧ t.after.dryInertia = s.dryInertia
  | some sep =>
    let pre := stageView (poweredStep s t.command)
    let upper := stageView t.after
    0 < sep.jettison.mass ∧ 0 < sep.upperDryMass ∧
    upper.mass+sep.jettison.mass = pre.mass ∧
    add upper.momentum sep.jettison.momentum = pre.momentum ∧
    pairCOM upper sep.jettison = pre.pos ∧
    (upper,sep.jettison) = separateStage pre upper.mass sep.impulse
private instance (s : VehicleState) (t : VehicleTurn) : Decidable (StageConserved s t) := by
  unfold StageConserved; split <;> infer_instance

inductive VehicleClause where
  | initial | attitude | mass | propulsion | thermal | structural | staging | corridor | dynamics
  deriving DecidableEq, Repr

/-- Semantic constraints, separated by refusal clause. No checker occurs in this definition. -/
@[expose] def ClauseHolds (p : VehiclePolicy) (s : VehicleState) (t : VehicleTurn) : VehicleClause → Prop
  | .initial => StateSafe p s
  | .attitude => SO3 t.after.pose.rotation
  | .mass =>
    0 < t.after.dry.mass ∧ (∀ tank ∈ t.after.tanks, 0 ≤ tank.oxidizer ∧ 0 ≤ tank.fuel) ∧
    s.tanks.length = t.command.draws.length ∧
    (∀ td ∈ s.tanks.zip t.command.draws, DrawValid td.1 td.2) ∧
    0 < t.after.dryInertia.x ∧ 0 < t.after.dryInertia.y ∧ 0 < t.after.dryInertia.z
  | .propulsion => PropulsionSafe p s t.command
  | .thermal =>
    ThermalCFL s.thermal t.command.heat ∧ Nonneg3 t.after.thermal.kelvin ∧
    t.after.thermal.kelvin.x ≤ p.maxKelvin.x ∧ t.after.thermal.kelvin.y ≤ p.maxKelvin.y ∧
    t.after.thermal.kelvin.z ≤ p.maxKelvin.z ∧ 0 ≤ p.minimumAblator ∧ p.minimumAblator < t.after.thermal.ablator
  | .structural => StructuralSafe t.command.load ∧
    t.command.load.capacity = p.structuralCapacity ∧ p.minimumFactor ≤ t.command.load.minimumFactor ∧ 1 ≤ p.minimumFactor ∧
    t.command.load.lever = p.bendingLever ∧ axialDemand s t.command ≤ t.command.load.axialForceMagnitude
  | .staging => StageConserved s t
  | .corridor => InBox t.after.pose.pos p.corridor ∧
    InBox (poweredStep s t.command).pose.pos
      (discreteFlowpipe s.pose.pos
        (scale (vehicleMass (poweredStep s t.command))⁻¹ (poweredStep s t.command).momentum) t.command.dt)
  | .dynamics => t.after = stepVehicle s t.command ∧
    act (vehicleInertia s) t.command.omega = s.bodyMomentum ∧
    scale 2 t.command.increment = scale t.command.dt t.command.omega
private instance (p : VehiclePolicy) (s : VehicleState) (t : VehicleTurn) (k : VehicleClause) :
    Decidable (ClauseHolds p s t k) := by cases k <;> unfold ClauseHolds <;> infer_instance

def clauses : List VehicleClause := [.initial,.attitude,.mass,.propulsion,.thermal,.structural,.staging,.corridor,.dynamics]
theorem mem_clauses (k : VehicleClause) : k ∈ clauses := by cases k <;> simp [clauses]

def checkClause (p : VehiclePolicy) (s : VehicleState) (t : VehicleTurn) (k : VehicleClause) : Bool :=
  decide (ClauseHolds p s t k)

@[expose] def TurnSafe (p : VehiclePolicy) (s : VehicleState) (t : VehicleTurn) : Prop :=
  ∀ k, ClauseHolds p s t k

def checkTurn (p : VehiclePolicy) (s : VehicleState) (t : VehicleTurn) : Bool :=
  clauses.all (checkClause p s t)

theorem checkTurn_iff (p : VehiclePolicy) (s : VehicleState) (t : VehicleTurn) :
    checkTurn p s t = true ↔ TurnSafe p s t := by
  simp only [checkTurn, List.all_eq_true, checkClause, decide_eq_true_eq]
  exact ⟨fun h k => h k (mem_clauses k), fun h k _ => h k⟩

theorem checkTurn_sound (p : VehiclePolicy) (s : VehicleState) (t : VehicleTurn)
    (h : checkTurn p s t = true) : TurnSafe p s t := (checkTurn_iff p s t).mp h

theorem turn_after_safe (p : VehiclePolicy) (s : VehicleState) (t : VehicleTurn) (h : TurnSafe p s t) : StateSafe p t.after := by
  have ha := h .attitude; have hm := h .mass; have ht := h .thermal; have hc := h .corridor
  exact ⟨ha, hm.1, hm.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2,
    ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2, hc.1⟩

theorem accepted_axial_margin (p : VehiclePolicy) (s : VehicleState) (t : VehicleTurn)
    (h : TurnSafe p s t) : t.command.load.minimumFactor * axialDemand s t.command ≤ p.structuralCapacity := by
  obtain ⟨hs, hcap, _, _, _, ha⟩ := h .structural
  have hq := Rat.mul_nonneg (Rat.mul_nonneg hs.1 hs.2.1) hs.2.2.1
  have hd : axialDemand s t.command ≤ structuralDemand t.command.load := by
    unfold structuralDemand; grind
  have hf : 0 ≤ t.command.load.minimumFactor := by have := hs.2.2.2.2.2.1; grind
  have hx := Rat.mul_le_mul_of_nonneg_left hd hf
  have hm := hs.2.2.2.2.2.2
  rw [← hcap]; exact Rat.le_trans hx hm

/-- Recursive semantics links each claimed poststate to the next turn's prestate. -/
@[expose] def SafeTrace (p : VehiclePolicy) (s : VehicleState) : List VehicleTurn → Prop
  | [] => StateSafe p s
  | t :: ts => TurnSafe p s t ∧ SafeTrace p t.after ts

def checkTrace (p : VehiclePolicy) (s : VehicleState) : List VehicleTurn → Bool
  | [] => checkState p s
  | t :: ts => checkTurn p s t && checkTrace p t.after ts

theorem checkTrace_iff (p : VehiclePolicy) (s : VehicleState) (ts : List VehicleTurn) :
    checkTrace p s ts = true ↔ SafeTrace p s ts := by
  induction ts generalizing s with
  | nil => simp [checkTrace, SafeTrace, checkState]
  | cons t ts ih => simp only [checkTrace, SafeTrace, Bool.and_eq_true, checkTurn_iff, ih]

theorem safeTrace_every_state (p : VehiclePolicy) (s : VehicleState) (ts : List VehicleTurn)
    (h : SafeTrace p s ts) : StateSafe p s ∧ ∀ t ∈ ts, StateSafe p t.after := by
  induction ts generalizing s with
  | nil => exact ⟨h, by simp⟩
  | cons t ts ih =>
    obtain ⟨hs, htail⟩ := ih t.after h.2
    refine ⟨h.1 .initial, ?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with he | he
    · simpa [he] using hs
    · exact htail u he

/-- Array traversal uses the previous accepted state as accumulator; no repeated list indexing. -/
def traceFold (p : VehiclePolicy) (acc : Bool × VehicleState) (t : VehicleTurn) : Bool × VehicleState :=
  (acc.1 && checkTurn p acc.2 t, t.after)
def checkTraceExec (p : VehiclePolicy) (s : VehicleState) (ts : Array VehicleTurn) : Bool :=
  let result := ts.foldl (traceFold p) (true,s)
  result.1 && checkState p result.2

theorem traceFold_refines (p : VehiclePolicy) (ts : List VehicleTurn) (b : Bool) (s : VehicleState) :
    let result := ts.foldl (traceFold p) (b,s)
    (result.1 && checkState p result.2) = (b && checkTrace p s ts) := by
  induction ts generalizing b s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons, traceFold, checkTrace]
    rw [ih]; simp only [Bool.and_assoc]

theorem checkTraceExec_eq_spec (p : VehiclePolicy) (s : VehicleState) (ts : Array VehicleTurn) :
    checkTraceExec p s ts = checkTrace p s ts.toList := by
  unfold checkTraceExec
  rw [← Array.foldl_toList]
  simpa only [Bool.true_and] using traceFold_refines p ts.toList true s

structure VehicleMission where
  policy : VehiclePolicy
  initial : VehicleState
  turns : Array VehicleTurn
  deriving Repr

/-- The complete trajectory is carried by the mission object; this certificate selects its format. -/
structure VehicleCertificate where
  format : String
  deriving DecidableEq, Repr

def firstFault (p : VehiclePolicy) (s : VehicleState) : Nat → List VehicleTurn → VehicleClause × List Nat
  | n, [] => (.initial,[n])
  | n, t :: ts =>
    if checkTurn p s t then firstFault p t.after (n+1) ts
    else ((clauses.find? (fun k => !(checkClause p s t k))).getD .dynamics,[n])

def judgeVehicle (m : VehicleMission) : Judge.Verdict VehicleClause :=
  if checkTraceExec m.policy m.initial m.turns then .ok
  else let fault := firstFault m.policy m.initial 0 m.turns.toList
       .refused fault.1 fault.2

def wireTag : String := "se3-vehicle-6dof@1"

@[instance_reducible] def se3Vehicle6DofJudge : Obend.Judge VehicleMission VehicleCertificate where
  Clause := VehicleClause
  Meaning := fun m _ => SafeTrace m.policy m.initial m.turns.toList
  check := fun _ m c => if c.format == wireTag then judgeVehicle m else .uncovered
  sound := by
    intro r m c h
    split at h
    · unfold judgeVehicle at h
      split at h
      · rename_i ht; exact (checkTrace_iff _ _ _).mp ((checkTraceExec_eq_spec _ _ _).symm ▸ ht)
      · contradiction
    · contradiction
  refutes := fun _ => true
  refuted := by
    intro r m c k path h _ c' hs
    have ht := (checkTrace_iff _ _ _).mpr hs
    have he : checkTraceExec m.policy m.initial m.turns = true := (checkTraceExec_eq_spec _ _ _).trans ht
    split at h
    · simp [judgeVehicle, he] at h
    · contradiction
  Fragment := fun _ => True
  complete := by
    intro m _ hm
    obtain ⟨_,hc⟩ := hm
    refine ⟨⟨wireTag⟩,0,?_⟩
    have ht := (checkTrace_iff _ _ _).mpr hc
    have he : checkTraceExec m.policy m.initial m.turns = true := (checkTraceExec_eq_spec _ _ _).trans ht
    simp [judgeVehicle, he]
  mono := by intros; rfl

theorem se3Vehicle6DofJudge_fragment_inhabited (m : VehicleMission) : se3Vehicle6DofJudge.Fragment m := True.intro

theorem se3Vehicle6DofJudge_sound (m : VehicleMission) (c : VehicleCertificate) (grade : Nat)
    (h : se3Vehicle6DofJudge.check grade m c = .ok) :
    SafeTrace m.policy m.initial m.turns.toList ∧
    StateSafe m.policy m.initial ∧ ∀ t ∈ m.turns.toList, StateSafe m.policy t.after := by
  have hs := se3Vehicle6DofJudge.sound h
  exact ⟨hs, safeTrace_every_state m.policy m.initial m.turns.toList hs⟩

end Obend.Hardware.SymplecticVehicle6Dof
