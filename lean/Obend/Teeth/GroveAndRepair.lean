module
meta import all Obend.Repair.CoalgebraicRepair
meta import all Obend.Doc.GroveEvaluation
meta import all Obend.Vault.Replay
import all Obend.Doc.GroveEvaluation
import all Obend.Doc.Grove
import all Obend.Doc.GroveLiveObject
import all Obend.Vault.Replay
import all Obend.Vault.LiveObject
import all Obend.Vault.WorldTree.ShardedWorld
import all Obend.Repair.CoalgebraicRepair
import Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Preservation
import all Obend.Core.Machine
import all Obend.Core.Check
import all Obend.Core.Ty
import Obend.Tactic.Tooth

public section
namespace Obend.Teeth.GroveAndRepair
open Obend.Doc Obend.Doc.Grove Obend.Core.Term Obend.Core.Ty Obend.Core.Check
open Obend.Core.Machine Obend.Core.MachineTyping Obend.Repair
set_option autoImplicit false

private abbrev fnType (a b : Ty) := Ty.arrow .reusable .unrestricted a b
private abbrev methodType := Ty.prototype .natural .natural
private abbrev planTy := Ty.variant (.field "ask" .natural .emptyRow)
private abbrev replyTy := Ty.variant (.field "reply" .natural .emptyRow)
private abbrev activity := Ty.computation planTy replyTy .natural
private abbrev annotation (a b : Ty) : LambdaAnnotation := ⟨a, b, .unrestricted, .reusable⟩

/-- The guard forces the open-recursive object before the activity yields. On reply,
reflection calls the method, which reads the inherited target through self. -/
private def method : Term := .fix (.lam (.lam (.prototype (.project (.bound 1)) (.bound 0)))) (.nat 42)
private def actorSource : AnnotatedTerm :=
  ⟨.app (.lam (.ifZero (.binary .subtract (.project (.bound 0)) (.nat 42))
    (.case (.perform (.inject "ask" (.nat 0)))
    [("reply", .done (.binary .add (.reflect (.bound 1)) (.bound 0)))]) (.done (.nat 0)))) method, fun _ => none, {}⟩

private def checkedActor : Checked actorSource [] where
  type := activity
  uses := []
  derivation := by
    apply PartialTyping.application (functionType := fnType methodType activity)
      (functionUses := []) (argumentUses := []) (quantity := .unrestricted) (reuse := .reusable)
      (domain := methodType) (argumentType := methodType)
    · apply PartialTyping.lambda (annotation := annotation methodType activity) (uses := [2])
      · apply PartialTyping.ifZero (vu := [1]) (zu := [1]) (su := [0,0])
        · exact .binary (primitive := .subtract) (input := .natural) (lu := [1]) (ru := [0]) rfl
            (.project (specType := .natural) (.bound (index := 0) (binding := ⟨methodType, .unrestricted⟩) rfl) rfl)
            (.natural _ 42)
        · apply PartialTyping.effectCase (row := .field "reply" .natural .emptyRow)
            (q := .unrestricted) (su := [0]) (au := [1])
          · exact .perform (.inject (fuel := 1) (.natural _ _) (by decide) rfl) rfl rfl
          · apply ArmsTyping.cons (bu := [1, 1]) (ru := [0])
            · apply PartialTyping.done
              · exact .binary (primitive := .add) (input := .natural) (lu := [0,1]) (ru := [1,0]) rfl
                  (.reflect (targetType := .natural) (.bound (index := 1) (binding := ⟨methodType, .unrestricted⟩) rfl) rfl)
                  (.bound (index := 0) (binding := ⟨.natural, .unrestricted⟩) rfl)
              · rfl
            all_goals first | exact .nil _ _ _ | rfl
          all_goals rfl
        · exact .done (.natural _ 0) rfl
        all_goals rfl
      all_goals rfl
    · apply PartialTyping.fix (specType := fnType methodType (fnType .natural methodType))
          (inherited := .natural) (su := []) (iu := [])
      · apply PartialTyping.lambda (annotation := annotation methodType (fnType .natural methodType))
          (uses := [1])
        · apply PartialTyping.lambda (annotation := annotation .natural methodType) (uses := [1, 1])
          · exact .prototype
              (.project (specType := .natural) (.bound (binding := ⟨methodType, .unrestricted⟩) (index := 1) rfl) rfl)
              (.bound (binding := ⟨.natural, .unrestricted⟩) (index := 0) rfl) rfl rfl
          all_goals rfl
        all_goals rfl
      all_goals first | exact .natural [] 42 | rfl
    all_goals rfl
  safe := rfl
  contextValid := rfl
  assumptionsValid := rfl

private def waiting := Obend.Core.Proofs.Adequacy.rawRun 48 (initial actorSource.erase)

private theorem waiting_typed : ∃ types, Nonempty (StateTyping {} types waiting activity) :=
  Obend.Core.Proofs.Preservation.checked_reachable_typed actorSource checkedActor
    (Obend.Core.Proofs.Adequacy.rawRun_reachable .start 48)

private def planAddress : Control → Option Nat
  | .yielded addr => some addr
  | _ => none

private theorem waiting_yielded : waiting.control = .yielded (waiting.heap.size - 1) := by
  have known : planAddress waiting.control = some (waiting.heap.size - 1) := by decide +kernel
  cases hc : waiting.control <;> simp [hc, planAddress] at known
  exact congrArg Control.yielded known

private def cachedPrototype : Bool := waiting.heap.any fun cell => match cell with
  | .cached _ (.prototype _ _) => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval cachedPrototype

private def limits : Limits := ⟨128, 128⟩
private def reply : Term := .inject "reply" (.nat 5)

private def world : Obend.Vault.Replay.World :=
  { Obend.Vault.Replay.genesis with store :=
    { Obend.Vault.Replay.genesis.store with pages := [⟨"objects", 1, [Graph.empty], none, [], none, none⟩] } }

private def replayObject : Except String Nat := do
  let op : Obend.Vault.LiveObject.Write := ⟨"objects", 1, root, "counter", waiting⟩
  let turn := Obend.Vault.Replay.Turn.ext "core4.checkpoint" op.encode
  let decoded ← Obend.Vault.Replay.decodeTurn (Obend.Vault.Replay.encodeTurn turn)
  let (landed, _) ← Obend.Vault.Replay.stepTurn world decoded
  let restored ← Obend.Vault.ChunkedWorld.decodeShardedWorld
    (Obend.Vault.ChunkedWorld.encodeShardedWorld landed)
  let some s := Obend.Vault.LiveObject.readAt restored.store "objects" 1 | throw "missing object"
  let some resumed := resume reply s | throw "missing yield"
  match runBounded limits 64 resumed with
  | .finished (.natural n) _ => return n
  | _ => throw "unexpected machine outcome"

/-- info: Except.ok 47 -/
#guard_msgs in
#eval replayObject

private def entries : List (AtomId × {v : Vertex // v.Valid}) :=
  [(1, ⟨.app .reusable .unrestricted .natural .natural, rfl⟩),
    (2, ⟨.leaf (fnType .natural .natural) (.lam (.bound 0)),
      (PartialTyping.lambda (annotation := annotation .natural .natural) (.bound (binding := ⟨.natural, .unrestricted⟩) (index := 0) rfl) rfl rfl rfl rfl)⟩),
    (3, ⟨.leaf .natural (.nat 17), PartialTyping.natural [] 17⟩),
    (4, ⟨.leaf .natural (.nat 23), PartialTyping.natural [] 23⟩),
    (5, ⟨.leaf .boolean (.boolean false), PartialTyping.boolean [] false⟩)]

private def vertices : Catalog := catalogOf entries

private def entry : Edge := (0, (0, 0), 1)
private def fn : Edge := (1, (1, 0), 2)
private def arg : Edge := (2, (1, 1), 3)
private def alternate : Edge := (3, (1, 1), 4)
private def base : StructurePatch := apply (insert entry) (apply (insert fn) (insert arg))

private def view (g : StructurePatch) := liveRoot vertices (fun _ => .natural) (0, 0) g

private def result (m : Marked) : String :=
  match evaluate m limits 32 with
  | .machine (.finished (.natural n) _) => toString n
  | .conflict h _ _ => reprStr h.reason
  | _ => "unexpected machine outcome"

private def groveExamples : List String :=
  let clean := view base
  let two := view (apply (insert alternate) base)
  let splice := view (apply (insert (4, (9, 0), 3)) base)
  let wrong := view (apply (remove base arg) (apply (insert (5, (1, 1), 5)) base))
  let cut := view (apply (remove base entry) (apply (insert alternate) base))
  [result clean.demand, result two.demand, result splice.demand, result wrong.demand, result cut.demand]

/-- info: ["17", "Obend.Doc.Grove.Conflict.alternatives [(2, (1, 1), 3), (3, (1, 1), 4)]",
  "Obend.Doc.Grove.Conflict.multiParent 3 [(2, (1, 1), 3), (4, (9, 0), 3)]",
  "Obend.Doc.Grove.Conflict.mismatch 5 (Obend.Core.Ty.Ty.boolean)",
  "Obend.Doc.Grove.Conflict.deletedParentModifiedChild (0, (0, 0), 1) (3, (1, 1), 4)"] -/
#guard_msgs in
#eval groveExamples

private def deeperEdits : List String :=
  let deep : Edge := (11, (3,0), 8)
  let addition := view (apply (remove base entry) (apply (insert deep) base))
  let withdrawal := view (apply (remove base entry) (apply (remove base arg) base))
  [result addition.demand, result withdrawal.demand]

/-- info: ["Obend.Doc.Grove.Conflict.deletedParentModifiedChild (0, (0, 0), 1) (11, (3, 0), 8)",
  "Obend.Doc.Grove.Conflict.deletedParentModifiedChild (0, (0, 0), 1) (2, (1, 1), 3)"] -/
#guard_msgs in
#eval deeperEdits

private def otherDemands : List String :=
  let conflict := apply (insert alternate) base
  let quiet := view (apply (remove base entry) base)
  let moved := view (apply (insert (7, (0,0), 1)) (apply (remove base entry) conflict))
  let stranded := view (apply (insert (7, (6,0), 1)) (apply (remove base entry) conflict))
  let sibling : Edge := (8, (6,1), 4)
  let siblingAt := fun g => (liveRoot vertices (fun _ => .natural) (6,1) (apply (insert sibling) g)).program
  let h : ConflictHole := ⟨(1,1), .natural, .empty⟩
  [result (.app (.code (.lam (.nat 8))) (.hole h)),
   result (siblingAt base), result (siblingAt (apply (remove base entry) base)),
   toString quiet.detached.length, toString moved.detached.length, toString stranded.detached.length]

/-- info: ["8", "23", "23", "0", "0", "1"] -/
#guard_msgs in
#eval otherDemands

/-- An ordinary Core4 hole and a generated conflict can have the same local index. -/
private def foreignHoleRefused : Bool :=
  match evaluate (.app (.code (.hole 0 [])) (.hole ⟨(2,0), .natural, .empty⟩)) limits 16 with
  | .machine (.refused .unresolvedHole _) => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval foreignHoleRefused

private def freezeAndReplay (g : StructurePatch) : Except String Nat := do
  let c ← (freezeRoot vertices (catalogOf_valid entries) (fun _ => .natural) (0, 0) g).mapError
    (fun h => reprStr h.reason)
  let t := Obend.Vault.Replay.checkpointTurn "objects" 2 root "function application" c
  let (landed, _) ← Obend.Vault.Replay.stepTurn world t
  let some state := Obend.Vault.LiveObject.readAt landed.store "objects" 2 | throw "missing cell"
  let .finished (.natural n) _ := runBounded limits 32 state | throw "unexpected result"
  return n

/-- info: Except.ok 17 -/
#guard_msgs in
#eval freezeAndReplay base

/-- info: Except.error "Obend.Doc.Grove.Conflict.deletedParentModifiedChild (0, (0, 0), 1) (3, (1, 1), 4)" -/
#guard_msgs in
#eval freezeAndReplay (apply (remove base entry) (apply (insert alternate) base))

private def upgradedReply : MachineObservation :=
  let relocated := liftContinuationState #[.suspended ⟨.nat 100, []⟩] waiting
  behavior machineCoalgebra relocated (.respond reply :: List.replicate 64 .tick)

/-- info: Obend.Repair.MachineObservation.natural 47 -/
#guard_msgs in
#eval upgradedReply

private def gatedWrites : Nat × Nat := Id.run do
  let start := recordCrossHabitatEnvelope.lens.initRight ⟨[], [], []⟩
  let path : List Obend.Judge.Genealogy.RecAct := [.write "x" 12, .write "x" 80, .forget]
  let historical := afterInputs (auditedEpoch (anchorAuditedGate genesisRecordGate) (.home 4)) start path
  let strengthened := afterInputs (auditedEpoch recordCrossHabitatEnvelope.nextGate (.home 4)) start path
  return (historical.1.2.1, strengthened.1.2.1)

/-- info: (2, 1) -/
#guard_msgs in
#eval gatedWrites

#tooth apply_comm by mutation Obend.Doc.Grove.apply := fun p _ => p
#tooth evaluate_hole by mutation observe := fun _ limits ticks s => .machine (runBounded limits ticks s)
#tooth DeleteModifyCover by mutation liveRoot := fun nodes expected port g =>
  ⟨project nodes (indexEdges (liveEdges g)) nodes.size [] port (expected port), []⟩
#tooth project_typed by mutation project := fun _ _ _ _ _ _ => .code (.nat 0)
#tooth Obend.Vault.LiveObject.readAt_land by mutation Obend.Vault.LiveObject.readAt :=
  fun _ _ _ => none
#tooth recordEpochBisim by mutation auditedEpoch := fun _ _ => ⟨fun s => ⟨false, fun _ => s⟩⟩
#tooth relocatedMachineBisim by mutation machineCoalgebra := ⟨fun s =>
  ⟨machineObservation s.control, fun _ => initial (.nat 0)⟩⟩
#tooth Obend.Doc.LiveObject.load_allocate by mutation Obend.Doc.LiveObject.restore := fun _ => none

-- Keep graph execution, raw image operations and the transport kernel choice-free.
run_cmd
  for name in [``Obend.Doc.Grove.apply, ``apply_comm, ``apply_idem, ``Obend.Doc.Grove.insert, ``Obend.Doc.Grove.remove, ``liveEdges,
      ``indexEdges, ``project, ``liveRoot, ``evaluate, ``Obend.Doc.LiveObject.decodeImageText,
      ``Obend.Doc.LiveObject.load_allocate, ``Obend.Doc.LiveObject.resumeAt, ``Obend.Vault.LiveObject.readAt,
      ``path_eta, ``behavior_unique, ``coinductiveUpgradeTransport, ``machineCoalgebra,
      ``UpgradeEnvelope.floor_forever] do
    let axioms ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    unless axioms.all (fun ax => ax == ``propext || ax == ``Quot.sound) do
      throwError "unexpected axioms for {name}: {axioms.toList}"

end Obend.Teeth.GroveAndRepair
