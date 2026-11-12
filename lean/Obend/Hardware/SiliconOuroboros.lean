module
public import Obend.Judge.CertifierRatchet
public import Obend.Judge.ReflectiveGate
public import Obend.Hardware.HDL
public import Obend.Hardware.RtlFold
public import Obend.Hardware.DprStutter
import all Obend.Judge.SvenvsCorrigibility
import all Obend.Judge.CertifierRatchet
import all Obend.Judge.ReflectiveGate
import all Obend.Hardware.DprStutter

public section
namespace Obend.Hardware.SiliconOuroboros
open HDL DprStutter Obend.Category
open Obend.Judge.SvenvsCorrigibility Obend.Judge.CertifierRatchet Obend.Judge.ReflectiveGate

def gateCount : RtlExpr → Nat
  | .const _ | .inputPort _ | .wireRef _ | .regRead _ => 0
  | .alu _ a b => 1 + gateCount a + gateCount b
  | .mux c t f => 1 + gateCount c + gateCount t + gateCount f
  | .bitNot a | .resize _ a => 1 + gateCount a

/-- Algebraic rewrites act on already optimized children. All comparisons are
syntactic; no runtime environment is consulted by the compiler. -/
def algebraicAlu (op : RtlAluOp) (a b : RtlExpr) : RtlExpr :=
  match op with
  | .add => if b = .const 0 then a else if a = .const 0 then b else .alu op a b
  | .sub => if b = .const 0 then a else if a = b then .const 0 else .alu op a b
  | .mul => if a = .const 0 ∨ b = .const 0 then .const 0
      else if b = .const 1 then a else if a = .const 1 then b else .alu op a b
  | .bitAnd => if a = .const 0 ∨ b = .const 0 then .const 0
      else if b = .const (BitVec.allOnes 64) then a
      else if a = .const (BitVec.allOnes 64) then b
      else if a = b then a else .alu op a b
  | .bitOr => if a = .const (BitVec.allOnes 64) ∨ b = .const (BitVec.allOnes 64)
      then .const (BitVec.allOnes 64)
      else if b = .const 0 then a else if a = .const 0 then b
      else if a = b then a else .alu op a b
  | .bitXor => if b = .const 0 then a else if a = .const 0 then b
      else if a = b then .const 0 else .alu op a b
  | _ => .alu op a b

private theorem and_mask_right (x : BitVec 64) : x &&& 18446744073709551615#64 = x := BitVec.and_allOnes
private theorem and_mask_left (x : BitVec 64) : 18446744073709551615#64 &&& x = x := BitVec.allOnes_and
private theorem or_mask_right (x : BitVec 64) : x ||| 18446744073709551615#64 = 18446744073709551615#64 := BitVec.or_allOnes
private theorem or_mask_left (x : BitVec 64) : 18446744073709551615#64 ||| x = 18446744073709551615#64 := BitVec.allOnes_or

theorem algebraicAlu_eval (op : RtlAluOp) (a b : RtlExpr) (inp wires regs : Nat → BitVec 64) :
    evalRtlExpr inp wires regs (algebraicAlu op a b) =
      evalAluOp op (evalRtlExpr inp wires regs a) (evalRtlExpr inp wires regs b) := by
  cases op <;> unfold algebraicAlu
  all_goals repeat' first | split
  all_goals simp_all [evalRtlExpr, evalAluOp, and_mask_right, and_mask_left]
  all_goals first | (rename_i h; rcases h with rfl | rfl <;> simp [evalRtlExpr, or_mask_right, or_mask_left]) | rfl

theorem algebraicAlu_count (op : RtlAluOp) (a b : RtlExpr) :
    gateCount (algebraicAlu op a b) ≤ 1 + gateCount a + gateCount b := by
  cases op <;> unfold algebraicAlu
  all_goals repeat' first | split
  all_goals simp_all [gateCount] <;> omega

theorem algebraicAlu_dag (op : RtlAluOp) (a b : RtlExpr) (ni nr nw : Nat)
    (ha : checkExprDAG ni nr nw a = true) (hb : checkExprDAG ni nr nw b = true) :
    checkExprDAG ni nr nw (algebraicAlu op a b) = true := by
  cases op <;> unfold algebraicAlu
  all_goals repeat' first | split
  all_goals simp_all [checkExprDAG]

def foldAlu (op : RtlAluOp) (a b : RtlExpr) : RtlExpr :=
  match a,b with
  | .const x, .const y => .const (evalAluOp op x y)
  | _,_ => algebraicAlu op a b

def foldNot : RtlExpr → RtlExpr
  | .const v => .const (~~~v)
  | .bitNot a => a
  | a => .bitNot a

def foldResize (op : RtlWidthOp) : RtlExpr → RtlExpr
  | .const v => .const (evalWidthOp op v)
  | a => .resize op a

def foldMux (c t f : RtlExpr) : RtlExpr :=
  if t = f then t else match c with
  | .const v => if v != 0#64 then t else f
  | _ => .mux c t f

@[expose] def rtlOuroOpt : RtlExpr → RtlExpr
  | .alu op a b => foldAlu op (rtlOuroOpt a) (rtlOuroOpt b)
  | .bitNot a => foldNot (rtlOuroOpt a)
  | .resize op a => foldResize op (rtlOuroOpt a)
  | .mux c t f => foldMux (rtlOuroOpt c) (rtlOuroOpt t) (rtlOuroOpt f)
  | e => e

theorem foldAlu_eval (op : RtlAluOp) (a b : RtlExpr) (inp wires regs : Nat → BitVec 64) :
    evalRtlExpr inp wires regs (foldAlu op a b) =
      evalAluOp op (evalRtlExpr inp wires regs a) (evalRtlExpr inp wires regs b) := by
  unfold foldAlu; split
  · rfl
  · exact algebraicAlu_eval _ _ _ _ _ _

theorem foldNot_eval (a : RtlExpr) (inp wires regs : Nat → BitVec 64) :
    evalRtlExpr inp wires regs (foldNot a) = ~~~(evalRtlExpr inp wires regs a) := by
  cases a <;> simp [foldNot, evalRtlExpr, BitVec.not_not]

theorem foldResize_eval (op : RtlWidthOp) (a : RtlExpr) (inp wires regs : Nat → BitVec 64) :
    evalRtlExpr inp wires regs (foldResize op a) = evalWidthOp op (evalRtlExpr inp wires regs a) := by
  cases a <;> rfl

theorem foldMux_eval (c t f : RtlExpr) (inp wires regs : Nat → BitVec 64) :
    evalRtlExpr inp wires regs (foldMux c t f) =
      evalRtlExpr inp wires regs (.mux c t f) := by
  unfold foldMux; split
  · next h => simp [evalRtlExpr, h]
  · cases c <;> simp [evalRtlExpr]
    split <;> rfl

theorem evalRtlExpr_rtlOuroOpt (inp wires regs : Nat → BitVec 64) (e : RtlExpr) :
    evalRtlExpr inp wires regs (rtlOuroOpt e) = evalRtlExpr inp wires regs e := by
  induction e <;> simp_all [rtlOuroOpt, foldAlu_eval, foldNot_eval, foldResize_eval, foldMux_eval, evalRtlExpr]

theorem foldAlu_count (op : RtlAluOp) (a b : RtlExpr) :
    gateCount (foldAlu op a b) ≤ 1 + gateCount a + gateCount b := by
  unfold foldAlu; split
  · simp [gateCount]
  · exact algebraicAlu_count _ _ _

theorem foldNot_count (a : RtlExpr) : gateCount (foldNot a) ≤ 1 + gateCount a := by
  cases a <;> simp [foldNot, gateCount] <;> omega

theorem foldResize_count (op : RtlWidthOp) (a : RtlExpr) : gateCount (foldResize op a) ≤ 1 + gateCount a := by
  cases a <;> simp [foldResize, gateCount]

theorem foldMux_count (c t f : RtlExpr) :
    gateCount (foldMux c t f) ≤ 1 + gateCount c + gateCount t + gateCount f := by
  unfold foldMux; split
  · omega
  · cases c <;> simp only
    · split <;> simp [gateCount] <;> omega
    all_goals simp [gateCount]

theorem gateCount_rtlOuroOpt_le (e : RtlExpr) : gateCount (rtlOuroOpt e) ≤ gateCount e := by
  induction e with
  | alu op a b iha ihb => exact Nat.le_trans (foldAlu_count _ _ _) (by simp only [gateCount]; omega)
  | bitNot a ih => exact Nat.le_trans (foldNot_count _) (by simp only [gateCount]; omega)
  | resize op a ih => exact Nat.le_trans (foldResize_count _ _) (by simp only [gateCount]; omega)
  | mux c t f ihc iht ihf => exact Nat.le_trans (foldMux_count _ _ _) (by simp only [gateCount]; omega)
  | const v => exact Nat.le_refl _
  | inputPort i => exact Nat.le_refl _
  | wireRef i => exact Nat.le_refl _
  | regRead i => exact Nat.le_refl _

theorem foldAlu_dag (op : RtlAluOp) (a b : RtlExpr) (ni nr nw : Nat)
    (ha : checkExprDAG ni nr nw a = true) (hb : checkExprDAG ni nr nw b = true) :
    checkExprDAG ni nr nw (foldAlu op a b) = true := by
  unfold foldAlu; split
  · rfl
  · exact algebraicAlu_dag _ _ _ _ _ _ ha hb

theorem foldNot_dag (a : RtlExpr) (ni nr nw : Nat) (h : checkExprDAG ni nr nw a = true) :
    checkExprDAG ni nr nw (foldNot a) = true := by
  cases a <;> simp_all [foldNot, checkExprDAG]

theorem foldResize_dag (op : RtlWidthOp) (a : RtlExpr) (ni nr nw : Nat) (h : checkExprDAG ni nr nw a = true) :
    checkExprDAG ni nr nw (foldResize op a) = true := by
  cases a <;> simp_all [foldResize, checkExprDAG]

theorem foldMux_dag (c t f : RtlExpr) (ni nr nw : Nat)
    (hc : checkExprDAG ni nr nw c = true) (ht : checkExprDAG ni nr nw t = true)
    (hf : checkExprDAG ni nr nw f = true) : checkExprDAG ni nr nw (foldMux c t f) = true := by
  unfold foldMux; split
  · exact ht
  · cases c <;> simp_all [checkExprDAG]
    split <;> assumption

theorem checkExprDAG_rtlOuroOpt (ni nr nw : Nat) (e : RtlExpr) (h : checkExprDAG ni nr nw e = true) :
    checkExprDAG ni nr nw (rtlOuroOpt e) = true := by
  induction e with
  | alu op a b iha ihb =>
    simp only [checkExprDAG, Bool.and_eq_true] at h
    exact foldAlu_dag _ _ _ _ _ _ (iha h.1) (ihb h.2)
  | bitNot a ih => exact foldNot_dag _ _ _ _ (ih h)
  | resize op a ih => exact foldResize_dag _ _ _ _ _ (ih h)
  | mux c t f ihc iht ihf =>
    simp only [checkExprDAG, Bool.and_eq_true] at h
    exact foldMux_dag _ _ _ _ _ _ (ihc h.1.1) (iht h.1.2) (ihf h.2)
  | const v => exact h
  | inputPort i => exact h
  | wireRef i => exact h
  | regRead i => exact h

theorem foldAlu_add_zero (e : RtlExpr) : foldAlu .add e (.const 0) = e := by
  cases e <;> simp [foldAlu, algebraicAlu, evalAluOp]

theorem rtlOuroOpt_strict_reduction (e : RtlExpr) :
    gateCount (rtlOuroOpt (.alu .add e (.const 0))) < gateCount (.alu .add e (.const 0)) := by
  simp only [rtlOuroOpt, foldAlu_add_zero, gateCount]
  have := gateCount_rtlOuroOpt_le e
  omega

theorem foldNot_twice_count (e : RtlExpr) : gateCount (foldNot (foldNot e)) ≤ gateCount e := by
  cases e <;> simp only [foldNot, gateCount]
  all_goals first | omega | exact foldNot_count _

theorem rtlOuroOpt_double_not_strict (e : RtlExpr) :
    gateCount (rtlOuroOpt (.bitNot (.bitNot e))) < gateCount (.bitNot (.bitNot e)) := by
  have h1 := foldNot_twice_count (rtlOuroOpt e)
  have h2 := gateCount_rtlOuroOpt_le e
  simp only [rtlOuroOpt, gateCount]
  omega

theorem rtlOuroOpt_mux_strict (c e : RtlExpr) :
    gateCount (rtlOuroOpt (.mux c e e)) < gateCount (.mux c e e) := by
  simp only [rtlOuroOpt, foldMux, ↓reduceIte, gateCount]
  have := gateCount_rtlOuroOpt_le e
  omega

def optDefs (defs : RtlFold.Defs) : RtlFold.Defs := defs.map fun w => { w with expr := rtlOuroOpt w.expr }

theorem optDefs_eval (defs : RtlFold.Defs) (inp regs : Nat → BitVec 64) :
    evalWireTable inp regs (optDefs defs).toList = evalWireTable inp regs defs.toList := by
  unfold optDefs evalWireTable
  simp only [Array.toList_map, List.foldl_map]
  congr 1
  funext env w
  simp only [evalRtlExpr_rtlOuroOpt]

abbrev HWState := BitVec 2
abbrev HWAct := BitVec 2

/-- State occupies the two low LUT address bits, action the two high bits. -/
def policyLut (pol : Policy HWState HWAct) : BitVec 16 :=
  BitVec.ofBoolListLE [pol 0 0, pol 1 0, pol 2 0, pol 3 0,
    pol 0 1, pol 1 1, pol 2 1, pol 3 1,
    pol 0 2, pol 1 2, pol 2 2, pol 3 2,
    pol 0 3, pol 1 3, pol 2 3, pol 3 3]

@[expose] def lowerPolicyToTiles (pol : Policy HWState HWAct) : Array TechmappedTile :=
  #[⟨policyLut pol, false, 0, 1, 2, 3⟩]

def compilePolicyFrames (pol : Policy HWState HWAct) : Array TileFrame := encodeTileFrames (lowerPolicyToTiles pol)
def packInputs (s : HWState) (a : HWAct) : Array Bool :=
  #[s.getLsbD 0, s.getLsbD 1, a.getLsbD 0, a.getLsbD 1]

theorem decode_compilePolicyFrames (pol : Policy HWState HWAct) :
    decodeTileFrames (lowerPolicyToTiles pol).size (compilePolicyFrames pol) = some (lowerPolicyToTiles pol) :=
  decodeTileFrames_encodeTileFrames _

theorem bv2_cases (v : BitVec 2) : v = 0#2 ∨ v = 1#2 ∨ v = 2#2 ∨ v = 3#2 := by
  have hv := v.isLt
  simp only [← BitVec.toNat_inj]
  change v.toNat = 0 ∨ v.toNat = 1 ∨ v.toNat = 2 ∨ v.toNat = 3
  omega

theorem evalDecodedFabric_lowerPolicyToTiles (pol : Policy HWState HWAct) (s : HWState) (a : HWAct)
    (regs : Array Bool) :
    (evalDecodedFabric (lowerPolicyToTiles pol) (packInputs s a) regs)[0]? = some (pol s a) := by
  rcases bv2_cases s with rfl | rfl | rfl | rfl <;>
    rcases bv2_cases a with rfl | rfl | rfl | rfl <;>
    simp [evalDecodedFabric, lowerPolicyToTiles, evalDecodedTile, tileInputs, packInputs,
      policyLut, - BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofBoolListLE, show (3 : Fin 6).val = 3 from rfl]

theorem compiled_policy_techmap (pol : Policy HWState HWAct) (inputs regs : Array Bool) :
    (evalDecodedFabric (lowerPolicyToTiles pol) inputs regs).toList =
      evalTechmappedSpec (lowerPolicyToTiles pol).toList inputs regs :=
  (evalDecodedFabric_eq_techmapped _ (compilePolicyFrames pol) _ _ inputs regs
    (decode_compilePolicyFrames pol) (by simp [verifyDecodedAgainstTechmap])).2

@[expose] def siliconDoInstall (dpr : DprFabric) (frames : Array TileFrame) : DprFabric :=
  stepDprFabric (stepDprFabric (stepDprFabric dpr .isolateClamped) (.loadFrames frames)) .releaseFence

def installActions (s : DprFabric) (frames : Array TileFrame) : List FabricAction :=
  let isolated := stepDprFabric s .isolateClamped
  let loaded := stepDprFabric isolated (.loadFrames frames)
  [⟨.isolateClamped, s.inputs, observedBoundaryPort s⟩,
   ⟨.loadFrames frames, isolated.inputs, observedBoundaryPort isolated⟩,
   ⟨.releaseFence, loaded.inputs, observedBoundaryPort loaded⟩]

theorem install_trace (s : DprFabric) (frames : Array TileFrame) :
    StepTrace dprFabricStepSys s (installActions s frames) (siliconDoInstall s frames) :=
  .cons ⟨rfl,rfl,rfl⟩ (.cons ⟨rfl,rfl,rfl⟩ (.cons ⟨rfl,rfl,rfl⟩ (.nil _)))

theorem install_neighbors (s : DprFabric) (frames : Array TileFrame) :
    StepTrace abstractNeighborStepSys s.neighbors (installActions s frames) (siliconDoInstall s frames).neighbors :=
  dpr_neighbor_trace (install_trace s frames)

theorem silicon_do_install_stutter_safe (s : DprFabric) (tiles : Array TechmappedTile)
    (active : s.phase = .active) (size : tiles.size = s.activeTiles.size) :
    (siliconDoInstall s (encodeTileFrames tiles)).phase = .active ∧
    (siliconDoInstall s (encodeTileFrames tiles)).activeTiles = tiles ∧
    observedBoundaryPort (stepDprFabric (stepDprFabric s .isolateClamped) (.loadFrames (encodeTileFrames tiles))) =
      observedBoundaryPort s ∧
    StepTrace abstractNeighborStepSys s.neighbors (installActions s (encodeTileFrames tiles))
      (siliconDoInstall s (encodeTileFrames tiles)).neighbors ∧
    StutterSimulates abstractNeighborStepSys dprFabricStepSys (fun n d => n = d.neighbors) 1 (0 : Nat) := by
  have hd : decodeTileFrames s.activeTiles.size (encodeTileFrames tiles) = some tiles := by
    rw [← size]; exact decodeTileFrames_encodeTileFrames tiles
  refine ⟨?_, ?_, ?_, install_neighbors _ _, ?_⟩
  · simp [siliconDoInstall, stepDprFabric, administer, active, hd]
  · simp [siliconDoInstall, stepDprFabric, administer, active, hd]
  · simp [stepDprFabric, administer, active, hd, observedBoundaryPort]
  · exact (dpr_preserves_neighbor_tiles_stutter (stepDprFabric s .isolateClamped)
      (encodeTileFrames tiles) (by simp [stepDprFabric, administer, active])).1

theorem silicon_do_install_quarantines (s : DprFabric) (frames : Array TileFrame)
    (active : s.phase = .active) (bad : decodeTileFrames s.activeTiles.size frames = none) :
    (siliconDoInstall s frames).phase = .isolateClamped ∧
    (siliconDoInstall s frames).activeTiles = s.activeTiles ∧
    observedBoundaryPort (siliconDoInstall s frames) = observedBoundaryPort s := by
  simp [siliconDoInstall, stepDprFabric, administer, active, bad, observedBoundaryPort]

/-- The live output tile, not a software shadow of the policy, gates actions. -/
def FabricRealizesPolicy (dpr : DprFabric) (pol : Policy HWState HWAct) : Prop :=
  ∀ s a, (evalDecodedFabric dpr.activeTiles (packInputs s a) dpr.targetRegs)[0]?.getD false = pol s a

structure SiliconCageState where
  plant : HWState
  dpr : DprFabric
  rootShield : HWState → HWAct

@[expose] def cageAction (cage : SiliconCageState) (agentAction : HWAct) : HWAct :=
  if cage.dpr.phase = .active &&
    (evalDecodedFabric cage.dpr.activeTiles (packInputs cage.plant agentAction) cage.dpr.targetRegs)[0]?.getD false
  then agentAction else cage.rootShield cage.plant

theorem cage_fails_closed (cage : SiliconCageState) (a : HWAct) (h : cage.dpr.phase ≠ .active) :
    cageAction cage a = cage.rootShield cage.plant := by simp [cageAction, h]

/-- The same fixed floor includes both absolute safety and bounded demonic
recoverability. It is never derived from the inhabitant's changing allowlist. -/
def CageFloor (plant : PlantR HWState HWAct) (safe home : HWState → Prop)
    (root : HWState → HWAct) (B : Nat) (s : HWState) : Prop :=
  safe s ∧ DemonicRecovWithin plant root home B s

theorem toolAgent_silicon_cage_safe (plant : PlantR HWState HWAct) (safe home : HWState → Prop)
    (root : HWState → HWAct) (B : Nat) (cage : SiliconCageState) (pol : Policy HWState HWAct)
    (rootFixed : cage.rootShield = root) (realizes : FabricRealizesPolicy cage.dpr pol)
    (hp : SoundPolicyR plant (CageFloor plant safe home root B) pol)
    (hr : SafeShieldR plant (CageFloor plant safe home root B) root)
    (h0 : CageFloor plant safe home root B cage.plant) (agent : SiliconCageState → HWAct)
    (next : HWState) (edge : plant cage.plant (cageAction cage (agent cage)) next) :
    safe next ∧ DemonicRecovWithin plant root home B next := by
  unfold cageAction at edge
  rw [realizes] at edge
  split at edge
  · next h =>
    have ha : pol cage.plant (agent cage) = true := (Bool.and_eq_true_iff.mp h).2
    exact hp _ _ _ h0 ha edge
  · rw [rootFixed] at edge
    exact hr _ _ h0 edge

theorem toolAgent_silicon_cage_reachR_safe (plant : PlantR HWState HWAct)
    (init safe home : HWState → Prop) (root : HWState → HWAct) (B : Nat)
    (dpr : DprFabric) (pol : Policy HWState HWAct)
    (hi : InitSafe init (CageFloor plant safe home root B))
    (realizes : FabricRealizesPolicy dpr pol)
    (hp : SoundPolicyR plant (CageFloor plant safe home root B) pol)
    (hr : SafeShieldR plant (CageFloor plant safe home root B) root)
    (agent : SiliconCageState → HWAct) :
    InvariantR plant init
      (fun s => cageAction ⟨s, dpr, root⟩ (agent ⟨s, dpr, root⟩))
      (CageFloor plant safe home root B) := by
  intro s hreach
  induction hreach with
  | init hs => exact hi _ hs
  | @step u v _ hedge ih =>
    exact toolAgent_silicon_cage_safe plant safe home root B ⟨u, dpr, root⟩ pol
      rfl realizes hp hr ih agent v hedge

def hwStep (s : HWState) (a : HWAct) : HWState := if a = 1 then 0 else s+1
def hwSafe (s : HWState) : Prop := s.toNat ≤ 2
instance (s : HWState) : Decidable (hwSafe s) := inferInstanceAs (Decidable (s.toNat ≤ 2))
def hwRoot (_ : HWState) : HWAct := 1

theorem hw_root_recovery (s : HWState) : DemonicRecovWithin (Det hwStep) hwRoot (fun x => x = 0) 1 s := by
  right
  refine ⟨⟨0, by simp [Det, hwStep, hwRoot]⟩, ?_⟩
  intro t ht
  simpa [Det, hwStep, hwRoot, DemonicRecovWithin] using ht

def hwPolicySequent (oldp newp : Policy HWState HWAct) : Sequent :=
  reflectAdmissibleSequent
    (fun s a => (hwStep (s.setWidth 2) (a.setWidth 2)).setWidth 4)
    (fun s => decide (hwSafe (s.setWidth 2)))
    (fun s a => oldp (s.setWidth 2) (a.setWidth 2))
    (fun s a => newp (s.setWidth 2) (a.setWidth 2))

theorem hwPolicySequent_encodes (oldp newp : Policy HWState HWAct)
    (h : SemValid (hwPolicySequent oldp newp)) : AdmissibleUpgrade hwStep hwSafe oldp newp := by
  have hh := (reflectAdmissible_iff _ _ _ _).1 h
  constructor
  · intro s a hs hp
    have ht := hh.1 (s.setWidth 4) (a.setWidth 4)
    simpa using ht (by simpa using hs) (by simpa using hp)
  · intro s a hp
    have ht := hh.2 (s.setWidth 4) (a.setWidth 4)
    simpa using ht (by simpa using hp)

/-- Input ports 0 and 1 carry the finite state and proposed tool action. -/
def policyOfRtl (e : RtlExpr) : Policy HWState HWAct := fun s a =>
  evalRtlExpr (fun i => if i = 0 then s.setWidth 64 else if i = 1 then a.setWidth 64 else 0)
    (fun _ => 0) (fun _ => 0) e != 0

def SoundRtlPass (pass : RtlExpr → RtlExpr) : Prop :=
  ∀ inp wires regs e, evalRtlExpr inp wires regs (pass e) = evalRtlExpr inp wires regs e

theorem policyOfRtl_pass (pass : RtlExpr → RtlExpr) (h : SoundRtlPass pass) (e : RtlExpr) :
    policyOfRtl (pass e) = policyOfRtl e := by
  funext s a
  dsimp only [policyOfRtl]
  rw [h _ _ _ e]

structure SiliconOuroStage where
  verifier : KernelChecker
  rtlPass : RtlExpr → RtlExpr
  activePol : Policy HWState HWAct
  cage : SiliconCageState

structure SiliconStageSound (st : SiliconOuroStage) : Prop where
  kernel : SoundKernel st.verifier
  compiler : SoundRtlPass st.rtlPass
  policy : SoundPolicy hwStep hwSafe st.activePol
  phase : st.cage.dpr.phase = .active
  bank : st.cage.dpr.activeTiles = lowerPolicyToTiles st.activePol
  root : st.cage.rootShield = hwRoot
  plant : hwSafe st.cage.plant
  corrigible : DemonicRecovWithin (Det hwStep) hwRoot (fun s => s = 0) 1 st.cage.plant

theorem SiliconStageSound.fabric {st : SiliconOuroStage} (h : SiliconStageSound st) :
    FabricRealizesPolicy st.cage.dpr st.activePol := by
  intro s a
  rw [h.bank, evalDecodedFabric_lowerPolicyToTiles]
  rfl

/-- The frozen upgrade menu contains two proved implementations. Policy RTL
and certificates remain arbitrary untrusted inputs. Promoting the kernel or
compiler selects checked code; it never evaluates an arbitrary claimed law. -/
structure GenerationProposal where
  promoteVerifier : Bool
  promoteCompiler : Bool
  candPolRtl : RtlExpr
  cert : FastProofCert

@[expose] def stepOuroGeneration (st : SiliconOuroStage) (p : GenerationProposal) : SiliconOuroStage :=
  if st.verifier p.cert (hwPolicySequent st.activePol (policyOfRtl p.candPolRtl)) then
    let pass := if p.promoteCompiler then rtlOuroOpt else st.rtlPass
    let pol := policyOfRtl (pass p.candPolRtl)
    { st with
        verifier := if p.promoteVerifier then FastKernel else st.verifier
        rtlPass := pass
        activePol := pol
        cage := { st.cage with dpr := siliconDoInstall st.cage.dpr (compilePolicyFrames pol) } }
  else st

theorem generation_refused_before_icap (st : SiliconOuroStage) (p : GenerationProposal)
    (h : st.verifier p.cert (hwPolicySequent st.activePol (policyOfRtl p.candPolRtl)) = false) :
    stepOuroGeneration st p = st := by simp [stepOuroGeneration, h]

theorem silicon_ouroboros_generation_safe (st : SiliconOuroStage) (p : GenerationProposal)
    (h : SiliconStageSound st) :
    SiliconStageSound (stepOuroGeneration st p) ∧ Weaker (stepOuroGeneration st p).activePol st.activePol := by
  unfold stepOuroGeneration
  split
  · next accepted =>
    have ha := hwPolicySequent_encodes _ _ (h.kernel _ _ accepted)
    let pass := if p.promoteCompiler then rtlOuroOpt else st.rtlPass
    have hc : SoundRtlPass pass := by
      dsimp only [pass]; split
      · exact evalRtlExpr_rtlOuroOpt
      · exact h.compiler
    have he := policyOfRtl_pass pass hc p.candPolRtl
    have size : (lowerPolicyToTiles (policyOfRtl (pass p.candPolRtl))).size = st.cage.dpr.activeTiles.size := by
      rw [h.bank]; rfl
    have install := silicon_do_install_stutter_safe st.cage.dpr
      (lowerPolicyToTiles (policyOfRtl (pass p.candPolRtl))) h.phase size
    refine ⟨⟨?_, hc, ?_, install.1, install.2.1, h.root, h.plant, h.corrigible⟩, ?_⟩
    · dsimp only; split
      · exact fastKernel_sound
      · exact h.kernel
    · simpa only [← he] using ha.1
    · simpa only [← he] using ha.2
  · exact ⟨h, weaker_refl _⟩

theorem generation_neighbor_trace (st : SiliconOuroStage) (p : GenerationProposal)
    (h : st.verifier p.cert (hwPolicySequent st.activePol (policyOfRtl p.candPolRtl)) = true) :
    let pass := if p.promoteCompiler then rtlOuroOpt else st.rtlPass
    let frames := compilePolicyFrames (policyOfRtl (pass p.candPolRtl))
    StepTrace abstractNeighborStepSys st.cage.dpr.neighbors (installActions st.cage.dpr frames)
      (stepOuroGeneration st p).cage.dpr.neighbors := by
  simp only [stepOuroGeneration, h, ↓reduceIte]
  exact install_neighbors _ _

/-- Ordinary compute edges run the live silicon envelope and tick every
neighbor. The adversary controls the proposed action on each edge. -/
def stepOuroClock (st : SiliconOuroStage) (a : HWAct) : SiliconOuroStage :=
  { st with cage := { st.cage with
      plant := hwStep st.cage.plant (cageAction st.cage a),
      dpr := stepDprFabric st.cage.dpr .compute } }

theorem silicon_clock_preserves (st : SiliconOuroStage) (a : HWAct) (h : SiliconStageSound st) :
    SiliconStageSound (stepOuroClock st a) := by
  have hs : hwSafe (hwStep st.cage.plant (cageAction st.cage a)) := by
    unfold cageAction
    rw [h.fabric _ _, h.root]
    split
    · next hp => exact h.policy _ _ h.plant (Bool.and_eq_true_iff.mp hp).2
    · simp [hwSafe, hwStep, hwRoot]
  refine ⟨h.kernel, h.compiler, h.policy, ?_, ?_, h.root, hs, hw_root_recovery _⟩
  · simp [stepOuroClock, stepDprFabric, administer, h.phase]
  · simpa [stepOuroClock, stepDprFabric, administer, h.phase] using h.bank

inductive OuroEvent where
  | generation (p : GenerationProposal)
  | compute (a : HWAct)

def stepOuroEvent (st : SiliconOuroStage) : OuroEvent → SiliconOuroStage
  | .generation p => stepOuroGeneration st p
  | .compute a => stepOuroClock st a

def ouroRun (initial : SiliconOuroStage) (events : Nat → OuroEvent) : Nat → SiliconOuroStage
  | 0 => initial
  | n+1 => stepOuroEvent (ouroRun initial events n) (events n)

theorem recursive_silicon_mutual_optimization_unconditional (initial : SiliconOuroStage)
    (events : Nat → OuroEvent) (h0 : SiliconStageSound initial) :
    ∀ n, SiliconStageSound (ouroRun initial events n) ∧
      Weaker (ouroRun initial events n).activePol initial.activePol := by
  intro n; induction n with
  | zero => exact ⟨h0, weaker_refl _⟩
  | succ n ih =>
    simp only [ouroRun, stepOuroEvent]
    cases events n with
    | generation p =>
      have h := silicon_ouroboros_generation_safe _ p ih.1
      exact ⟨h.1, weaker_trans h.2 ih.2⟩
    | compute a => exact ⟨silicon_clock_preserves _ a ih.1, ih.2⟩

theorem recursive_silicon_ouroboros_unconditional (initial : SiliconOuroStage)
    (events : Nat → OuroEvent) (h0 : SiliconStageSound initial) (n i : Nat) :
    let st := ouroRun initial events n
    SiliconStageSound st ∧ FabricRealizesPolicy st.cage.dpr st.activePol ∧
    hwSafe st.cage.plant ∧ DemonicRecovWithin (Det hwStep) hwRoot (fun x => x = 0) 1 st.cage.plant ∧
    neighborCoordinate st.cage.dpr.specSlot i ≠ st.cage.dpr.specSlot ∧
    StutterSimulates abstractNeighborStepSys dprFabricStepSys (fun neighbor dpr => neighbor = dpr.neighbors) 1 (0 : Nat) := by
  have h := (recursive_silicon_mutual_optimization_unconditional initial events h0 n).1
  refine ⟨h, h.fabric, h.plant, h.corrigible, neighborCoordinate_ne _ i, ?_⟩
  exact (dpr_preserves_neighbor_tiles_stutter
    (stepDprFabric (ouroRun initial events n).cage.dpr .isolateClamped) #[]
    (by simp [stepDprFabric, administer, h.phase])).1

/-- Clock-level soundness permits quarantine. Generation boundaries additionally
require the active phase, as recorded by SiliconStageSound. -/
structure SiliconClockSound (st : SiliconOuroStage) : Prop where
  kernel : SoundKernel st.verifier
  compiler : SoundRtlPass st.rtlPass
  policy : SoundPolicy hwStep hwSafe st.activePol
  bank : st.cage.dpr.activeTiles = lowerPolicyToTiles st.activePol
  root : st.cage.rootShield = hwRoot
  plant : hwSafe st.cage.plant
  corrigible : DemonicRecovWithin (Det hwStep) hwRoot (fun s => s = 0) 1 st.cage.plant

theorem SiliconStageSound.clock {st : SiliconOuroStage} (h : SiliconStageSound st) : SiliconClockSound st :=
  ⟨h.kernel,h.compiler,h.policy,h.bank,h.root,h.plant,h.corrigible⟩

theorem SiliconClockSound.fabric {st : SiliconOuroStage} (h : SiliconClockSound st) :
    FabricRealizesPolicy st.cage.dpr st.activePol := by
  intro s a
  rw [h.bank, evalDecodedFabric_lowerPolicyToTiles]
  rfl

theorem silicon_install_recovers (s : DprFabric) (tiles : Array TechmappedTile)
    (size : tiles.size = s.activeTiles.size) :
    (siliconDoInstall s (encodeTileFrames tiles)).phase = .active ∧
    (siliconDoInstall s (encodeTileFrames tiles)).activeTiles = tiles := by
  have hd : decodeTileFrames s.activeTiles.size (encodeTileFrames tiles) = some tiles := by
    rw [← size]; exact decodeTileFrames_encodeTileFrames tiles
  by_cases h : s.phase = .active
  · exact ⟨(silicon_do_install_stutter_safe s tiles h size).1,
      (silicon_do_install_stutter_safe s tiles h size).2.1⟩
  · simp [siliconDoInstall, stepDprFabric, administer, h, hd]

theorem silicon_bad_frames_preserve_bank (s : DprFabric) (frames : Array TileFrame)
    (bad : decodeTileFrames s.activeTiles.size frames = none) :
    (siliconDoInstall s frames).phase = .isolateClamped ∧
    (siliconDoInstall s frames).activeTiles = s.activeTiles := by
  by_cases h : s.phase = .active
  · exact ⟨(silicon_do_install_quarantines s frames h bad).1,
      (silicon_do_install_quarantines s frames h bad).2.1⟩
  · simp [siliconDoInstall, stepDprFabric, administer, h, bad]

/-- Fault injection is a separate physical channel. CRC-failing bus traffic
quarantines the slot. A well-formed but unauthenticated bank is never installed;
normal installation still requires the reflective policy certificate. -/
def stepBusFault (st : SiliconOuroStage) (frames : Array TileFrame) : SiliconOuroStage :=
  if decodeTileFrames st.cage.dpr.activeTiles.size frames = none then
    { st with cage := { st.cage with dpr := siliconDoInstall st.cage.dpr frames } }
  else st

theorem bus_fault_preserves (st : SiliconOuroStage) (frames : Array TileFrame) (h : SiliconClockSound st) :
    SiliconClockSound (stepBusFault st frames) := by
  unfold stepBusFault
  split
  · next bad =>
    refine ⟨h.kernel,h.compiler,h.policy,?_,h.root,h.plant,h.corrigible⟩
    exact (silicon_bad_frames_preserve_bank _ _ bad).2.trans h.bank
  · exact h

theorem generation_clock_preserves (st : SiliconOuroStage) (p : GenerationProposal)
    (h : SiliconClockSound st) : SiliconClockSound (stepOuroGeneration st p) := by
  unfold stepOuroGeneration
  split
  · next accepted =>
    have ha := hwPolicySequent_encodes _ _ (h.kernel _ _ accepted)
    let pass := if p.promoteCompiler then rtlOuroOpt else st.rtlPass
    have hc : SoundRtlPass pass := by
      dsimp only [pass]; split
      · exact evalRtlExpr_rtlOuroOpt
      · exact h.compiler
    have he := policyOfRtl_pass pass hc p.candPolRtl
    have size : (lowerPolicyToTiles (policyOfRtl (pass p.candPolRtl))).size = st.cage.dpr.activeTiles.size := by
      rw [h.bank]; rfl
    have installed := silicon_install_recovers st.cage.dpr
      (lowerPolicyToTiles (policyOfRtl (pass p.candPolRtl))) size
    refine ⟨?_,hc,?_,installed.2,h.root,h.plant,h.corrigible⟩
    · dsimp only; split
      · exact fastKernel_sound
      · exact h.kernel
    · simpa only [← he] using ha.1
  · exact h

theorem compute_clock_preserves (st : SiliconOuroStage) (a : HWAct) (h : SiliconClockSound st) :
    SiliconClockSound (stepOuroClock st a) := by
  have hs : hwSafe (hwStep st.cage.plant (cageAction st.cage a)) := by
    unfold cageAction
    rw [h.fabric _ _, h.root]
    split
    · next hp => exact h.policy _ _ h.plant (Bool.and_eq_true_iff.mp hp).2
    · simp [hwSafe, hwStep, hwRoot]
  refine ⟨h.kernel,h.compiler,h.policy,?_,h.root,hs,hw_root_recovery _⟩
  simp only [stepOuroClock, stepDprFabric, administer]
  split <;> exact h.bank

inductive CageEvent where
  | generation (p : GenerationProposal)
  | compute (a : HWAct)
  | busFault (frames : Array TileFrame)

def stepCageEvent (st : SiliconOuroStage) : CageEvent → SiliconOuroStage
  | .generation p => stepOuroGeneration st p
  | .compute a => stepOuroClock st a
  | .busFault frames => stepBusFault st frames

def cageRun (initial : SiliconOuroStage) (events : Nat → CageEvent) : Nat → SiliconOuroStage
  | 0 => initial
  | n+1 => stepCageEvent (cageRun initial events n) (events n)

theorem recursive_silicon_cage_unconditional (initial : SiliconOuroStage)
    (events : Nat → CageEvent) (h0 : SiliconClockSound initial) :
    ∀ n, SiliconClockSound (cageRun initial events n) := by
  intro n; induction n with
  | zero => exact h0
  | succ n ih =>
    simp only [cageRun, stepCageEvent]
    cases events n with
    | generation p => exact generation_clock_preserves _ p ih
    | compute a => exact compute_clock_preserves _ a ih
    | busFault frames => exact bus_fault_preserves _ frames ih

/-- The isolate and load edges themselves preserve the floor: they freeze the
plant while ticking neighbors, and both expose the same latched boundary. -/
theorem install_intermediate_clocks (st : SiliconOuroStage) (frames : Array TileFrame)
    (h : SiliconStageSound st) :
    let isolated := stepDprFabric st.cage.dpr .isolateClamped
    let loaded := stepDprFabric isolated (.loadFrames frames)
    SiliconClockSound { st with cage := { st.cage with dpr := isolated } } ∧
    SiliconClockSound { st with cage := { st.cage with dpr := loaded } } ∧
    observedBoundaryPort isolated = observedBoundaryPort st.cage.dpr ∧
    observedBoundaryPort loaded = observedBoundaryPort st.cage.dpr := by
  have hi : (stepDprFabric st.cage.dpr .isolateClamped).phase ≠ .active := by
    simp [stepDprFabric, administer, h.phase]
  have hb : (stepDprFabric st.cage.dpr .isolateClamped).activeTiles = st.cage.dpr.activeTiles := by
    simp [stepDprFabric, administer, h.phase]
  refine ⟨⟨h.kernel,h.compiler,h.policy,hb.trans h.bank,h.root,h.plant,h.corrigible⟩,
    ⟨h.kernel,h.compiler,h.policy,?_,h.root,h.plant,h.corrigible⟩,?_,?_⟩
  · cases hd : decodeTileFrames st.cage.dpr.activeTiles.size frames <;>
      simpa [stepDprFabric, administer, h.phase, hd] using h.bank
  · simp [stepDprFabric, administer, h.phase, observedBoundaryPort]
  · rw [(clampedPortStable _ frames hi).2]
    simp [stepDprFabric, administer, h.phase]

theorem dpr_root_layout (s : DprFabric) (cmd : DprCommand) :
    (stepDprFabric s cmd).specSlot = s.specSlot ∧
    (stepDprFabric s cmd).neighbors.tiles = s.neighbors.tiles := by
  cases cmd <;> unfold stepDprFabric administer
  all_goals repeat' first | split
  all_goals exact ⟨rfl,rfl⟩

theorem install_root_layout (s : DprFabric) (frames : Array TileFrame) :
    (siliconDoInstall s frames).specSlot = s.specSlot ∧
    (siliconDoInstall s frames).neighbors.tiles = s.neighbors.tiles := by
  simp only [siliconDoInstall, (dpr_root_layout _ _).1, (dpr_root_layout _ _).2, and_self]

def cageEventActions (st : SiliconOuroStage) : CageEvent → List FabricAction
  | .generation p =>
    if st.verifier p.cert (hwPolicySequent st.activePol (policyOfRtl p.candPolRtl)) then
      let pass := if p.promoteCompiler then rtlOuroOpt else st.rtlPass
      installActions st.cage.dpr (compilePolicyFrames (policyOfRtl (pass p.candPolRtl)))
    else []
  | .compute _ => [⟨.compute, st.cage.dpr.inputs, observedBoundaryPort st.cage.dpr⟩]
  | .busFault frames =>
    if decodeTileFrames st.cage.dpr.activeTiles.size frames = none then installActions st.cage.dpr frames else []

theorem cage_event_neighbor_trace (st : SiliconOuroStage) (event : CageEvent) :
    StepTrace abstractNeighborStepSys st.cage.dpr.neighbors (cageEventActions st event)
      (stepCageEvent st event).cage.dpr.neighbors := by
  cases event with
  | generation p =>
    simp only [stepCageEvent, cageEventActions]
    unfold stepOuroGeneration
    split
    · exact install_neighbors _ _
    · exact .nil _
  | compute a => exact .cons rfl (.nil _)
  | busFault frames =>
    simp only [stepCageEvent, cageEventActions]
    unfold stepBusFault
    split
    · exact install_neighbors _ _
    · exact .nil _

theorem cage_event_root_layout (st : SiliconOuroStage) (event : CageEvent) :
    (stepCageEvent st event).cage.dpr.specSlot = st.cage.dpr.specSlot ∧
    (stepCageEvent st event).cage.dpr.neighbors.tiles = st.cage.dpr.neighbors.tiles := by
  cases event with
  | generation p =>
    simp only [stepCageEvent]
    unfold stepOuroGeneration
    split
    · exact install_root_layout _ _
    · exact ⟨rfl,rfl⟩
  | compute a => exact dpr_root_layout _ _
  | busFault frames =>
    simp only [stepCageEvent]
    unfold stepBusFault
    split
    · exact install_root_layout _ _
    · exact ⟨rfl,rfl⟩

def cageActions (initial : SiliconOuroStage) (events : Nat → CageEvent) : Nat → List FabricAction
  | 0 => []
  | n+1 => cageActions initial events n ++ cageEventActions (cageRun initial events n) (events n)

private theorem neighborTrace_append {s t u : NeighborState} {xs ys : List FabricAction}
    (h1 : StepTrace abstractNeighborStepSys s xs t) (h2 : StepTrace abstractNeighborStepSys t ys u) :
    StepTrace abstractNeighborStepSys s (xs ++ ys) u := by
  induction h1 with
  | nil => exact h2
  | cons edge _ ih => exact .cons edge (ih h2)

theorem cage_run_neighbor_trace (initial : SiliconOuroStage) (events : Nat → CageEvent) (n : Nat) :
    StepTrace abstractNeighborStepSys initial.cage.dpr.neighbors (cageActions initial events n)
      (cageRun initial events n).cage.dpr.neighbors := by
  induction n with
  | zero => exact .nil _
  | succ n ih => exact neighborTrace_append ih (cage_event_neighbor_trace _ _)

theorem cage_run_root_immutable (initial : SiliconOuroStage) (events : Nat → CageEvent) (n : Nat) :
    (cageRun initial events n).cage.dpr.specSlot = initial.cage.dpr.specSlot ∧
    (cageRun initial events n).cage.dpr.neighbors.tiles = initial.cage.dpr.neighbors.tiles := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have h := cage_event_root_layout (cageRun initial events n) (events n)
    exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

theorem recursive_silicon_cage_trace (initial : SiliconOuroStage) (events : Nat → CageEvent)
    (h0 : SiliconClockSound initial) (n i : Nat) :
    let st := cageRun initial events n
    SiliconClockSound st ∧ FabricRealizesPolicy st.cage.dpr st.activePol ∧
    StepTrace abstractNeighborStepSys initial.cage.dpr.neighbors (cageActions initial events n)
      st.cage.dpr.neighbors ∧
    st.cage.dpr.neighbors.tiles = initial.cage.dpr.neighbors.tiles ∧
    neighborCoordinate initial.cage.dpr.specSlot i ≠ st.cage.dpr.specSlot := by
  have hs := recursive_silicon_cage_unconditional initial events h0 n
  have hr := cage_run_root_immutable initial events n
  refine ⟨hs,hs.fabric,cage_run_neighbor_trace initial events n,hr.2,?_⟩
  rw [hr.1]
  exact neighborCoordinate_ne _ i

end Obend.Hardware.SiliconOuroboros
