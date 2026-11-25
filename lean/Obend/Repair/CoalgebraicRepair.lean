module
public import Obend.Repair.CoalgConfig
public import Obend.Repair.UpgradeEnvelope
import all Obend.Repair.UpgradeEnvelope
import all Obend.Repair.DeltaLensRenew
import all Obend.Judge.Genealogy

public section
namespace Obend.Repair
set_option autoImplicit false

/-- The finite interaction schema has one nullary constructor and one unary
constructor for each machine input. It uses the repair library's polynomial. -/
abbrev PathPos {I : Type} : Option I → Type
  | none => Empty
  | some _ => Unit

def pathConstruct {I : Type} : PAlg (Option I) PathPos (List I) where
  op
    | ⟨none, _⟩ => []
    | ⟨some i, tail⟩ => i :: tail ()

def pathFold {I X : Type} (a : PAlg (Option I) PathPos X) : List I → X
  | [] => a.op ⟨none, Empty.elim⟩
  | i :: rest => a.op ⟨some i, fun _ => pathFold a rest⟩

/-- Constructor eta for traces, directly by induction, without function extensionality. -/
theorem path_eta {I : Type} (path : List I) : pathFold pathConstruct path = path := by
  induction path with
  | nil => rfl
  | cons i rest ih => exact congrArg (i :: ·) ih

def pathInitial (I : Type) : InitPAlg (Option I) PathPos (List I) where
  alg := pathConstruct
  fold := pathFold
  fold_beta a t := by
    obtain ⟨_ | i, f⟩ := t
    · apply congrArg a.op
      apply congrArg (Sigma.mk none)
      funext e; exact Empty.elim e
    · rfl
  fold_eta a h law path := by
    induction path with
    | nil =>
      refine (law ⟨none, Empty.elim⟩).trans ?_
      apply congrArg a.op
      apply congrArg (Sigma.mk none)
      funext e; exact Empty.elim e
    | cons i rest ih =>
      exact (law ⟨some i, fun _ => rest⟩).trans (congrArg (fun x => a.op ⟨some i, fun _ => x⟩) ih)

/-- A Moore machine is the existing polynomial coalgebra with a constant input
position type. Each history selects one observation in the final behavior. -/
abbrev Moore (I O X : Type) := PCoalg O (fun _ => I) X

def afterInputs {I O X : Type} (src : Moore I O X) : X → List I → X
  | x, [] => x
  | x, i :: rest => afterInputs src (src.pos x i) rest

def behavior {I O X : Type} (src : Moore I O X) (x : X) (path : List I) : O :=
  src.shape (afterInputs src x path)

def behaviorCoalg (I O : Type) : Moore I O (List I → O) where
  out b := ⟨b [], fun i rest => b (i :: rest)⟩

theorem behavior_unique {I O X : Type} (src : Moore I O X) (h : X → List I → O)
    (law : ∀ x, (behaviorCoalg I O).out (h x) = PolyF.map h (src.out x))
    (x : X) (path : List I) : h x path = behavior src x path := by
  induction path generalizing x with
  | nil => exact congrArg Sigma.fst (law x)
  | cons i rest ih =>
    have child := congrArg (fun layer : PolyF O (fun _ => I) (List I → O) => layer.2 i rest) (law x)
    exact child.trans (ih (src.pos x i))

def behaviorFinal (I O : Type) : FinalPCoalg O (fun _ => I) (List I → O) where
  coalg := behaviorCoalg I O
  corec := behavior
  corec_out _ _ := rfl
  corec_uniq src h law x := funext (behavior_unique src h law x)

/-- A bisimulation can relate different state representations. Each input indexes
a successor obligation, including inputs at yielded or terminal states. -/
structure InputBisim {I O X Y : Type} (a : Moore I O X)
    (b : Moore I O Y) (R : X → Y → Prop) : Prop where
  observe : ∀ {x y}, R x y → a.shape x = b.shape y
  advance : ∀ {x y}, R x y → ∀ i, R (a.pos x i) (b.pos y i)

theorem InputBisim.after {I O X Y : Type} {a : Moore I O X}
    {b : Moore I O Y} {R : X → Y → Prop} (sim : InputBisim a b R)
    (path : List I) {x y} (xy : R x y) : R (afterInputs a x path) (afterInputs b y path) := by
  induction path generalizing x y with
  | nil => exact xy
  | cons i _ ih => exact ih (sim.advance xy i)

/-- Sample the initial state and every successor along the actual input sequence. -/
def observations {I O X : Type} (a : Moore I O X) : X → List I → List O
  | x, [] => [a.shape x]
  | x, i :: rest => a.shape x :: observations a (a.pos x i) rest

theorem InputBisim.trace {I O X Y : Type} {a : Moore I O X}
    {b : Moore I O Y} {R : X → Y → Prop} (sim : InputBisim a b R)
    (path : List I) {x y} (xy : R x y) : observations a x path = observations b y path := by
  induction path generalizing x y with
  | nil => exact congrArg (fun o => [o]) (sim.observe xy)
  | cons i rest ih =>
    exact (congrArg (· :: observations a (a.pos x i) rest) (sim.observe xy)).trans
      (congrArg (b.shape y :: ·) (ih (sim.advance xy i)))

def holds_forever {I O X : Type} (a : Moore I O X) (safe : X → Prop) (x : X) :=
  ∀ path, safe (afterInputs a x path)

theorem coinductiveUpgradeTransport {I O X Y : Type} {a : Moore I O X}
    {b : Moore I O Y} {R : X → Y → Prop} (sim : InputBisim a b R)
    {x y} (xy : R x y) {old : X → Prop} {new : Y → Prop}
    (floor : ∀ {s t}, R s t → old s → new t) :
    (∀ path, behavior a x path = behavior b y path) ∧
    (∀ path, observations a x path = observations b y path) ∧
    (holds_forever a old x → holds_forever b new y) :=
  ⟨fun path => sim.observe (sim.after path xy), fun path => sim.trace path xy,
   fun safe path => floor (sim.after path xy) (safe path)⟩

open Obend.Core.Machine Obend.Core.Term Obend.Core.Collect

inductive MachineInput where
  | tick
  | respond (reply : Term)

inductive MachineObservation where
  | running | waiting | finished | divergent | refused (reason : Refusal)
  | natural (n : Nat) | boolean (v : Bool) | label (s : String)
  deriving Repr

def machineObservation : Control → MachineObservation
  | .complete (.natural n) => .natural n
  | .complete (.boolean b) => .boolean b
  | .complete (.label s) => .label s
  | .complete _ => .finished
  | .yielded _ => .waiting
  | .refused r => .refused r
  | .blackhole _ => .divergent
  | _ => .running

def machineCoalgebra : Moore MachineInput MachineObservation State where
  out s := ⟨machineObservation s.control, fun
    | .tick => stepRaw s
    | .respond r => (resume r s).getD s⟩

theorem relocatedMachineBisim (pre : Array Cell) :
    InputBisim machineCoalgebra machineCoalgebra (fun s t => t = liftContinuationState pre s) where
  observe := by
    rintro ⟨heap, ctrl, stk⟩ _ rfl
    cases ctrl <;> first | rfl | (rename_i v; cases v <;> rfl)
  advance := by
    rintro s _ rfl input
    cases input with
    | tick => exact stepRaw_liftContinuationState pre s
    | respond reply =>
      obtain ⟨heap, ctrl, stk⟩ := s
      cases ctrl <;> rfl

theorem relocatedTrace (pre : Array Cell) (s : State) (inputs : List MachineInput) :
    observations machineCoalgebra s inputs =
      observations machineCoalgebra (liftContinuationState pre s) inputs :=
  (relocatedMachineBisim pre).trace inputs rfl

open Obend.Judge.Genealogy

/-- A target interpreter executes its own transitions. Its one-step proof relates
them to the source through the upgrade's persistent lens complement. -/
theorem UpgradeEnvelope.floor_forever {H K : Habitat} {C E F I O : Type}
    (env : UpgradeEnvelope H K C E F) (a : Moore I O H.State)
    (b : Moore I O (K.State × C))
    (sim : InputBisim a b (fun x y => env.lens.Consistent x y.2 y.1))
    (x : H.State) (φ : H.Floor) (safe : holds_forever a (H.holds φ) x) :
    holds_forever b (fun y => K.holds (env.liftFloor φ) y.1) (env.lens.initRight x) :=
  (coinductiveUpgradeTransport sim (env.lens.initRight_consistent x)
    (fun h => (env.liftFloor_iff h).2)).2.2 safe

/-- The exercise of the epoch envelope on actual gated record actions. The target
maintains its audit count and interprets the admitted action in the new habitat. -/
def recordEpoch (φ : RecFloor) : Moore RecAct Bool Rec where
  out s := ⟨decide (record.holds φ s), fun a =>
    if admits Exec.faithful genesisRecordGate s a then record.step a s else s⟩

def auditedEpoch (gate : Gate auditedRecordHabitat) (φ : RecFloor) : Moore RecAct Bool (AuditedRec × AuditedRec) where
  out st := ⟨decide (auditedRecordHabitat.holds φ st.1), fun a =>
    if admits Exec.faithful gate st.1 a then
      let next := auditedRecordHabitat.step a st.1
      (next, next)
    else st⟩

theorem recordEpochBisim (φ : RecFloor) : InputBisim (recordEpoch φ) (auditedEpoch (anchorAuditedGate genesisRecordGate) φ)
    (fun s t => recordCrossHabitatEnvelope.lens.Consistent s t.2 t.1) where
  observe := by rintro s ⟨t,c⟩ ⟨_, rfl⟩; rfl
  advance := by
    rintro s ⟨t,c⟩ hc a
    change c = t ∧ t.1 = s at hc
    obtain ⟨rfl, rfl⟩ := hc
    have anchor : admits Exec.faithful (anchorAuditedGate genesisRecordGate) c a =
        admits Exec.faithful genesisRecordGate c.1 a := by cases a <;> rfl
    by_cases ok : admits Exec.faithful genesisRecordGate c.1 a = true
    · simp only [PCoalg.pos, recordEpoch, auditedEpoch, anchor, ok, ↓reduceIte]
      cases a <;> exact ⟨rfl, rfl⟩
    · simp [PCoalg.pos, recordEpoch, auditedEpoch, anchor, ok, recordCrossHabitatEnvelope,
        recToAuditedEditLens, DeltaLens.toSymmetricEditLens, SymmetricEditLens.symm, DeltaLens.fst]

theorem audited_home_forever :
    holds_forever (auditedEpoch (anchorAuditedGate genesisRecordGate) (.home 4)) (fun st => RecFloor.holds (.home 4) st.1.1)
      (recordCrossHabitatEnvelope.lens.initRight ⟨[], [], []⟩) := by
  apply recordCrossHabitatEnvelope.floor_forever _ _ (recordEpochBisim (.home 4)) _ (.home 4)
  intro path
  have runEq (s : Rec) : afterInputs (recordEpoch (.home 4)) s path =
      replayEpochSegment Exec.faithful genesisRecordGate s path := by
    induction path generalizing s with
    | nil => rfl
    | cons _ _ ih => exact ih _
  rw [runEq]
  apply replayEpochSegment_preserves_floors Exec.faithful genesisRecordGate
    (by rfl) (fun t _ => Exec.faithful_holds t)
  · intro φ member
    change φ ∈ [RecFloor.home 4] at member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨rfl, by decide⟩
  · exact List.Mem.head _

private theorem audited_after (gate : Gate auditedRecordHabitat) (φ : RecFloor)
    (s : AuditedRec × AuditedRec) (inputs : List RecAct) :
    (afterInputs (auditedEpoch gate φ) s inputs).1 =
      replayEpochSegment Exec.faithful gate s.1 inputs := by
  induction inputs generalizing s with
  | nil => rfl
  | cons a rest ih =>
    rw [afterInputs, ih, replayEpochSegment]
    by_cases ok : admits Exec.faithful gate s.1 a = true <;> simp [PCoalg.pos, auditedEpoch, ok]

/-- Replay an arbitrary historical prefix, switch to the actual strengthened gate,
and preserve both floors for every subsequent input sequence. The extra cap
must hold at migration because epoch one admitted writes above it. -/
theorem upgraded_floors_forever (prefixInputs : List RecAct)
    (capAtMigration : RecFloor.holds (.cap "x" 50)
      (afterInputs (recordEpoch (.home 4)) ⟨[], [], []⟩ prefixInputs)) :
    let start := recordCrossHabitatEnvelope.lens.initRight ⟨[], [], []⟩
    let migrated := afterInputs (auditedEpoch (anchorAuditedGate genesisRecordGate) (.home 4)) start prefixInputs
    holds_forever (auditedEpoch recordCrossHabitatEnvelope.nextGate (.home 4))
      (fun t => RecFloor.holds (.home 4) t.1.1 ∧ RecFloor.holds (.cap "x" 50) t.1.1) migrated := by
  intro start migrated inputs
  have same := (recordEpochBisim (.home 4)).after prefixInputs
    (recordCrossHabitatEnvelope.lens.initRight_consistent (⟨[], [], []⟩ : Rec))
  have underlying : migrated.1.1 = _ := same.2
  have atCap : RecFloor.holds (.cap "x" 50) migrated.1.1 := underlying.symm ▸ capAtMigration
  have atHome := audited_home_forever prefixInputs
  have floors : ∀ f ∈ upgradedAuditedGate.floors, auditedRecordHabitat.holds f migrated.1 := by
    intro f hf
    change f ∈ [RecFloor.home 4, .cap "x" 50] at hf
    rcases List.mem_cons.mp hf with rfl | last
    · exact atHome
    · obtain rfl := List.mem_singleton.mp last
      exact atCap
  have safe := replayEpochSegment_preserves_floors Exec.faithful upgradedAuditedGate
    (by rfl) (fun t _ => Exec.faithful_holds t) inputs migrated.1 floors
  rw [audited_after]
  exact ⟨safe _ (.head _), safe _ (.tail _ (.head _))⟩

end Obend.Repair
