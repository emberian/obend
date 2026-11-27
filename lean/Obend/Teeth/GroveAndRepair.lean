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
import all Obend.Repair.TrackedFiber
import all Obend.Repair.QuotAssembly
import Obend.Core.Proofs.Adequacy.Run
import all Obend.Core.Proofs.Preservation
import all Obend.Core.Machine
import all Obend.Core.Check
import all Obend.Core.Ty
import Obend.Tactic.Tooth

public section
namespace Obend.Teeth.GroveAndRepair
open Obend.Doc Obend.Doc.Grove Obend.Doc.LiveObject Obend.Core.Term Obend.Core.Ty Obend.Core.Check
open Obend.Core.Machine Obend.Core.MachineTyping Obend.Repair
set_option autoImplicit false

private abbrev fnType (a b : Ty) := Ty.arrow .reusable .unrestricted a b
private abbrev methodType := Ty.prototype .natural .natural
private abbrev planTy := Ty.variant (.field "ask" .natural .emptyRow)
private abbrev replyRow := Ty.field "reply" .natural .emptyRow
private abbrev replyTy := Ty.variant replyRow
private abbrev activity := Ty.computation planTy replyTy .natural
private abbrev annotation (a b : Ty) : LambdaAnnotation := ⟨a, b, .unrestricted, .reusable⟩

/-- The guard forces the open-recursive object before the activity yields. On reply,
reflection calls the method, which reads the inherited target through self. -/
private def method : Term := .fix (.lam (.lam (.prototype (.project (.bound 1)) (.bound 0)))) (.nat 42)
private def actorSource : AnnotatedTerm :=
  ⟨.app (.lam (.ifZero (.binary .subtract (.project (.bound 0)) (.nat 42))
    (.case (.perform (.inject "ask" (.nat 0)))
    [("reply", .done (.binary .add (.reflect (.bound 1)) (.bound 0)))]) (.done (.nat 0)))) method, fun _ => none, {}⟩

private def waiting := Obend.Core.Proofs.Adequacy.rawRun 48 (initial actorSource.erase)
private def reply : Term := .inject "reply" (.nat 5)
private def finished : State :=
  match resume reply waiting with
  | some s => Obend.Core.Proofs.Adequacy.rawRun 64 s
  | none => waiting

private abbrev methodBind : Binding := ⟨methodType, .unrestricted⟩
private abbrev natBind : Binding := ⟨.natural, .unrestricted⟩
private abbrev outerMethodAnn : LambdaAnnotation := annotation methodType (fnType .natural methodType)
private abbrev innerMethodAnn : LambdaAnnotation := annotation .natural methodType

/-- Executable `StateCert` for the yielded open-recursive prototype actor `waiting`. -/
private def waitingCert : StateCert where
  assumptions := {}
  cells := [
    ⟨methodType, ⟨[], [([0], outerMethodAnn), ([0, 0], innerMethodAnn)]⟩, some .direct⟩,
    ⟨methodType, ⟨[methodBind], [([0, 0], outerMethodAnn), ([0, 0, 0], innerMethodAnn)]⟩, some .direct⟩,
    ⟨methodType, ⟨[methodBind], []⟩, none⟩,
    ⟨.natural, ⟨[methodBind], []⟩, some .direct⟩,
    ⟨.natural, ⟨[natBind, methodBind, methodBind], []⟩, none⟩,
    ⟨.natural, ⟨[natBind, methodBind, methodBind], []⟩, some .direct⟩,
    ⟨planTy, ⟨[methodBind], []⟩, none⟩
  ]
  current := .computation planTy replyTy replyTy
  control := .yielded planTy replyTy
  stack := [.frame (.computation planTy replyTy replyTy) activity
    (.effectCase [methodBind] [] .unrestricted planTy replyTy replyRow .natural)]
  result := activity

/-- Executable `StateCert` for the post-reply completed actor `finished` (`.complete (.natural 47)`). -/
private def finishedCert : StateCert where
  assumptions := {}
  cells := [
    ⟨methodType, ⟨[], [([0], outerMethodAnn), ([0, 0], innerMethodAnn)]⟩, some .direct⟩,
    ⟨methodType, ⟨[methodBind], [([0, 0], outerMethodAnn), ([0, 0, 0], innerMethodAnn)]⟩, some .direct⟩,
    ⟨methodType, ⟨[methodBind], []⟩, some .direct⟩,
    ⟨.natural, ⟨[methodBind], []⟩, some .direct⟩,
    ⟨.natural, ⟨[natBind, methodBind, methodBind], []⟩, some .direct⟩,
    ⟨.natural, ⟨[natBind, methodBind, methodBind], []⟩, some .direct⟩,
    ⟨planTy, ⟨[methodBind], []⟩, none⟩,
    ⟨.natural, ⟨[], []⟩, some .direct⟩,
    ⟨.natural, ⟨[natBind], []⟩, some .direct⟩
  ]
  current := .natural
  control := .complete .direct
  stack := []
  result := .natural

private theorem waiting_cert_ok : checkStateCert waitingCert waiting = true := by decide +kernel
private theorem finished_cert_ok : checkStateCert finishedCert finished = true := by decide +kernel

private def waitingCheckpoint : Checkpoint {} waitingCert.addressTypes activity :=
  ⟨waiting, waitingCert, rfl, rfl, rfl, waiting_cert_ok⟩

private def finishedCheckpoint : Checkpoint {} finishedCert.addressTypes .natural :=
  ⟨finished, finishedCert, rfl, rfl, rfl, finished_cert_ok⟩

private def cachedPrototype : Bool := waiting.heap.any fun cell => match cell with
  | .cached _ (.prototype _ _) => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval cachedPrototype

private def limits : Limits := ⟨128, 128⟩

private def world : Obend.Vault.Replay.World :=
  { Obend.Vault.Replay.genesis with store :=
    { Obend.Vault.Replay.genesis.store with pages := [⟨"objects", 1, [Graph.empty], none, [], none, none⟩] } }

/-- Multi-turn living object lifecycle on the SAME atom (`atom = 1`):
Turn 1 persists `waiting` through Replay wire encode/decode + sharded world round-trip,
resumes with `reply = 5` to compute `47`, and Turn 2 supersedes `atom = 1` IN PLACE
with the completed certified checkpoint `finished`. -/
private def replayAndAdvanceObject : Except String (Nat × Nat × Nat) := do
  let t1 := Obend.Vault.Replay.checkpointTurn "objects" 1 root "counter" waitingCheckpoint
  let dec1 ← Obend.Vault.Replay.decodeTurn (Obend.Vault.Replay.encodeTurn t1)
  let (w1, _) ← Obend.Vault.Replay.stepTurn world dec1
  let restored ← Obend.Vault.ChunkedWorld.decodeShardedWorld
    (Obend.Vault.ChunkedWorld.encodeShardedWorld w1)
  let some s1 := Obend.Vault.LiveObject.readAt restored.store "objects" 1 | throw "missing turn-1 object"
  let some resumed := resume reply s1 | throw "missing yield"
  let .finished (.natural n1) _ := runBounded limits 64 resumed | throw "unexpected resumed outcome"
  -- Turn 2: advance/supersede the SAME atom 1 in place on w1
  let t2 := Obend.Vault.Replay.checkpointTurn "objects" 1 root "counter" finishedCheckpoint
  let dec2 ← Obend.Vault.Replay.decodeTurn (Obend.Vault.Replay.encodeTurn t2)
  let (w2, _) ← Obend.Vault.Replay.stepTurn w1 dec2
  let some s2 := Obend.Vault.LiveObject.readAt w2.store "objects" 1 | throw "missing turn-2 object"
  let .complete (.natural n2) := s2.control | throw "expected completed natural"
  let historyLen := (w2.store.page? "objects").map (fun p => p.history.length) |>.getD 0
  return (n1, n2, historyLen)

/-- info: Except.ok (47, 47, 3) -/
#guard_msgs in
#eval replayAndAdvanceObject

/-- Untrusted wire payloads failing typing or invariants are actively rejected on `liveObjectExt.decode`
and `stepTurn` (closing the erased-ghost typing bypass). -/
private def untypedWireRejected : Bool × Bool × Bool :=
  let badRefused : State := ⟨#[], .refused .unbound, []⟩
  let badScoped : State := initial (.bound 9)
  let badTyped : State := initial (.boolean false)
  let goodWrite : Obend.Vault.LiveObject.Write :=
    ⟨"objects", 1, root, "good", initial (.nat 7), StateCert.ofInitial {} .natural [], by decide +kernel⟩
  let tamperHex (st : State) : Lean.Json :=
    match goodWrite.encode with
    | .arr a => .arr (a.set! 4 (.str (encodeImageText st)))
    | other => other
  let r1 := match Obend.Vault.Replay.stepTurn world (.ext "core4.checkpoint" (tamperHex badRefused)) with
    | .error _ => true | .ok _ => false
  let r2 := match Obend.Vault.Replay.stepTurn world (.ext "core4.checkpoint" (tamperHex badScoped)) with
    | .error _ => true | .ok _ => false
  let r3 := match Obend.Vault.Replay.stepTurn world (.ext "core4.checkpoint" (tamperHex badTyped)) with
    | .error _ => true | .ok _ => false
  (r1, r2, r3)

/-- info: (true, true, true) -/
#guard_msgs in
#eval untypedWireRejected

/-! ## Grove Collaborative Full-Core.Term & Localized Demand Witnesses -/

private def entries : List (AtomId × {v : Vertex // v.Valid}) :=
  [(1, ⟨.app .reusable .unrestricted .natural .natural, rfl⟩),
    (2, ⟨.leaf (fnType .natural .natural) (.lam (.bound 0)) [([], annotation .natural .natural)],
      (PartialTyping.lambda (annotation := annotation .natural .natural)
        (.bound (binding := ⟨.natural, .unrestricted⟩) (index := 0) rfl) rfl rfl rfl rfl)⟩),
    (3, ⟨.leaf .natural (.nat 17), PartialTyping.natural [] 17⟩),
    (4, ⟨.leaf .natural (.nat 23), PartialTyping.natural [] 23⟩),
    (5, ⟨.leaf .boolean (.boolean false), PartialTyping.boolean [] false⟩),
    (6, ⟨.leaf .boolean (.boolean true), PartialTyping.boolean [] true⟩),
    (7, ⟨.leaf .natural (.nat 17), PartialTyping.natural [] 17⟩),
    -- Full Core4 structural vertices: ifBool, letBind, lam, var, binary, record, get, prototype, projectProto, fix, mix
    (10, ⟨.ifBool .natural, trivial⟩),
    (11, ⟨.letBind .natural .natural, rfl⟩),
    (12, ⟨.binary .add, trivial⟩),
    (13, ⟨.var 0 .natural, trivial⟩),
    (14, ⟨.record [("ok", .natural), ("cut", .natural)],
      ⟨by decide, by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; rcases hf with rfl | rfl <;> rfl⟩⟩),
    (15, ⟨.get (recordRow [("ok", .natural), ("cut", .natural)]) "ok" .natural, ⟨1, rfl⟩⟩),
    (16, ⟨.get (recordRow [("ok", .natural), ("cut", .natural)]) "cut" .natural, ⟨2, rfl⟩⟩),
    (17, ⟨.fix .natural methodType, ⟨rfl, rfl⟩⟩),
    (18, ⟨.lam .reusable methodType (fnType .natural methodType), rfl⟩),
    (19, ⟨.lam .reusable .natural methodType, rfl⟩),
    (20, ⟨.prototype .natural .natural, ⟨rfl, rfl⟩⟩),
    (21, ⟨.projectProto .natural .natural, trivial⟩),
    (22, ⟨.var 1 methodType, trivial⟩),
    (23, ⟨.var 0 .natural, trivial⟩),
    (24, ⟨.reflectProto .natural .natural, trivial⟩),
    (25, ⟨.mix .natural .natural .natural .natural, ⟨rfl, rfl, rfl⟩⟩),
    (26, ⟨.lam .reusable .natural (fnType .natural .natural), rfl⟩),
    (27, ⟨.lam .reusable .natural .natural, rfl⟩)]

private def vertices : Catalog := catalogOf entries

private def entry : Edge := (0, (0, 0), 1)
private def fn : Edge := (1, (1, 0), 2)
private def arg : Edge := (2, (1, 1), 3)
private def alternate : Edge := (3, (1, 1), 4)
private def base : StructurePatch := apply (insert entry) (apply (insert fn) (insert arg))

private def view (g : StructurePatch) := liveRoot vertices (fun _ => .natural) (0, 0) g

private def result (m : Marked) : String :=
  match evaluate m limits 64 with
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
  let deep : Edge := (11, (3, 0), 8)
  let addition := view (apply (remove base entry) (apply (insert deep) base))
  let withdrawal := view (apply (remove base entry) (apply (remove base arg) base))
  [result addition.demand, result withdrawal.demand]

/-- info: ["Obend.Doc.Grove.Conflict.deletedParentModifiedChild (0, (0, 0), 1) (11, (3, 0), 8)",
  "Obend.Doc.Grove.Conflict.deletedParentModifiedChild (0, (0, 0), 1) (2, (1, 1), 3)"] -/
#guard_msgs in
#eval deeperEdits

/-- Localized `LiveRoot.demand` non-wipeout over full Core4 `ifBool` & `record`/`get`!
The `else` branch (port `(10, 2)`) has edge `cutBranch = (22, (10, 2), 1)` deleted concurrently
with a 2-hop descendant insertion `deepEdit = (25, (3, 0), 8)` beneath `1 → 3`:
- `r.detached` is NON-EMPTY (`length = 1`), containing the 2-hop conflict at port `(10, 2)`.
- Evaluating `r.demand` when `cond = true` evaluates the unaffected `then` branch and returns `17`!
- Flipping `cond = false` forces port `(10, 2)` and surfaces the EXACT localized 2-hop conflict! -/
private def localizedDemandTest : Nat × String × String :=
  let cutBranch : Edge := (22, (10, 2), 1)
  let ifBase : StructurePatch :=
    apply (insert (20, (0, 0), 10))
      (apply (insert (21, (10, 0), 6))
        (apply (insert (23, (10, 1), 7))
          (apply (insert cutBranch) (apply (insert fn) (insert arg)))))
  let deepEdit : Edge := (25, (3, 0), 8)
  let conflicted := apply (remove ifBase cutBranch) (apply (insert deepEdit) ifBase)
  let rTrue := view conflicted
  let flipped := apply (remove conflicted (21, (10, 0), 6)) (apply (insert (26, (10, 0), 5)) conflicted)
  let rFalse := view flipped
  (rTrue.detached.length, result rTrue.demand, result rFalse.demand)

/-- info: (1, "17", "Obend.Doc.Grove.Conflict.deletedParentModifiedChild (22, (10, 2), 1) (25, (3, 0), 8)") -/
#guard_msgs in
#eval localizedDemandTest

/-- Full Core4 Grove collaboration across `letBind`, `binary`, `var`, `record`/`get`,
and open-recursive `fix` + `lam` + `prototype` + `projectProto` + `reflectProto`. -/
private def fullCoreGroveExamples : List String :=
  -- 1. `let x = 17 in x + x` -> 34
  let letPatch : StructurePatch :=
    apply (insert (30, (0, 0), 11))
      (apply (insert (31, (11, 0), 3))
        (apply (insert (32, (11, 1), 12))
          (apply (insert (33, (12, 0), 13)) (insert (34, (12, 1), 23)))))
  -- 2. `get { ok := 17, cut := <detached 2-hop cut> } "ok"` -> 17 (while `"cut"` hits localized conflict!)
  let recCut : Edge := (43, (14, 1), 1)
  let recBase : StructurePatch :=
    apply (insert (40, (0, 0), 15))
      (apply (insert (41, (15, 0), 14))
        (apply (insert (42, (14, 0), 7))
          (apply (insert recCut) (apply (insert fn) (insert arg)))))
  let recConflicted := apply (remove recBase recCut) (apply (insert (44, (1, 1), 4)) recBase)
  let recStep1 := apply (remove recConflicted (41, (15, 0), 14)) recConflicted
  let recCutRead := apply (remove recStep1 (40, (0, 0), 15))
    (apply (insert (45, (0, 0), 16)) (apply (insert (46, (16, 0), 14)) recStep1))
  -- 3. Open-recursive prototype built solely from Grove vertices:
  --    `reflect (fix (λ self. λ super. prototype (project self) super) 23)` -> 23
  let protoPatch : StructurePatch :=
    apply (insert (50, (0, 0), 24))
      (apply (insert (51, (24, 0), 17))
        (apply (insert (52, (17, 0), 18))
          (apply (insert (53, (17, 1), 4))
            (apply (insert (54, (18, 0), 19))
              (apply (insert (55, (19, 0), 20))
                (apply (insert (56, (20, 0), 21))
                  (apply (insert (57, (21, 0), 22)) (insert (58, (20, 1), 23)))))))))
  -- 4. `StructurePatch ↔ Obend.Doc.Graph` round-trip check
  let rtOk := match ofDocGraph (toDocGraph recConflicted) with
    | some g' => toString (liveEdges g' == liveEdges recConflicted)
    | none => "none"
  [result (view letPatch).demand,
   result (view recConflicted).demand,
   result (view recCutRead).demand,
   result (view protoPatch).demand,
   rtOk]

/-- info: ["34", "17", "Obend.Doc.Grove.Conflict.deletedParentModifiedChild (43, (14, 1), 1) (44, (1, 1), 4)", "23", "true"] -/
#guard_msgs in
#eval fullCoreGroveExamples

private def foreignHoleRefused : Bool :=
  match evaluate (.app (.code (.hole 0 [])) (.hole ⟨(2, 0), .natural, .empty⟩)) limits 16 with
  | .machine (.refused .unresolvedHole _) => true
  | _ => false

/-- info: true -/
#guard_msgs in
#eval foreignHoleRefused

private def freezeAndReplay (g : StructurePatch) : Except String Nat := do
  let c ← (freezeRoot vertices (fun _ => .natural) (0, 0) g).mapError fun
    | .conflict h => reprStr h.reason
    | .uncertified msg => msg
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

/-! ## `#tooth` Mutation-Sensitivity Witnesses -/

open Obend.Category.Projection (forallAlong_iff)

/-- Both a retained copy and a fresh copy accept the value actually returned by identity. -/
example (n : Nat) : TrackedFiber.Serves
    (Obend.Category.FiberGrowth.insert (fun _ : Unit => ()) ())
    (fun _ out => out = CanonVal.nat n) () CanonCode.id (CanonVal.nat n) := by
  apply (TrackedFiber.serves_insert_of_run_iff _ _ _ _ _ (CanonVal.nat n) rfl ?_).mpr rfl
  exact (forallAlong_iff ..).mpr fun _ _ => rfl

/-- A first, unconstrained copy of a previously empty name forces exactly definedness. -/
private theorem first_copy_demands_run (code : CanonCode) (input : CanonVal) :
    TrackedFiber.Serves (Obend.Category.FiberGrowth.insert (fun _ : Empty => ()) ())
      (fun _ _ => True) () code input ↔ ∃ out, CanonCode.eval code input = some out := by
  rw [TrackedFiber.serves_insert_iff]
  exact ⟨fun ⟨out, run, _⟩ => ⟨out, run⟩,
    fun ⟨out, run⟩ => ⟨out, run, (forallAlong_iff ..).mpr (fun _ _ => trivial), trivial⟩⟩

-- Accepting any one copy would let an old success hide a fresh refusal.
#tooth TrackedFiber.serves_insert_of_run_iff by mutation TrackedFiber.Serves :=
  fun p accept b code input => ∃ e, p e = b ∧
    ∃ out, CodeTracker.eval code input = some out ∧ accept e out

-- Checking only outputs that happen to exist would let an undefined suspension pass.
#tooth first_copy_demands_run by mutation TrackedFiber.Serves :=
  fun p accept b code input => ∀ e, p e = b →
    ∀ out, CodeTracker.eval code input = some out → accept e out

#tooth apply_comm by mutation Obend.Doc.Grove.apply := fun p _ => p
#tooth evaluate_hole by mutation observe := fun _ limits ticks s => .machine (runBounded limits ticks s)
#tooth DeleteModifyCover by mutation liveRoot := fun nodes expected port g =>
  ⟨project nodes (indexEdges (liveEdges g)) ∅ nodes.size [] [] port (expected port), []⟩
#tooth project_typed by mutation project := fun _ _ _ _ _ _ _ _ => .code (.nat 0)
#tooth ofDocGraph_toDocGraph by mutation ofDocGraph := fun _ => none
#tooth Obend.Vault.LiveObject.readAt_land by mutation Obend.Vault.LiveObject.readAt :=
  fun _ _ _ => none
#tooth Obend.Doc.LiveObject.load_allocate by mutation Obend.Doc.LiveObject.restore := fun _ => none
#tooth Obend.Doc.LiveObject.checkStateCert_sound by mutation Obend.Doc.LiveObject.checkStateCert :=
  fun _ _ => true
#tooth recordEpochBisim by mutation auditedEpoch := fun _ _ => ⟨fun s => ⟨false, fun _ => s⟩⟩
#tooth relocatedMachineBisim by mutation machineCoalgebra := ⟨fun s =>
  ⟨machineObservation s.control, fun _ => initial (.nat 0)⟩⟩
#tooth relocatedMachineTransport by mutation machineCoalgebra := ⟨fun s =>
  ⟨machineObservation s.control, fun _ => initial (.nat 0)⟩⟩

-- Keep graph execution, ByteArray image codecs, and the coinductive transport kernel choice-free.
run_cmd
  for name in [``Obend.Doc.Grove.apply, ``apply_comm, ``apply_idem, ``Obend.Doc.Grove.insert,
      ``Obend.Doc.Grove.remove, ``liveEdges, ``indexEdges, ``project, ``liveRoot, ``toDocGraph,
      ``ofDocGraph, ``evaluate, ``encodeImageHex, ``decodeImageHex, ``encodeImageText,
      ``decodeImageText, ``loadRaw_allocate, ``allocate_advances_live, ``resumeAtRaw,
      ``Obend.Vault.LiveObject.readAtRaw, ``behavior_unique, ``coinductiveUpgradeTransport,
      ``machineCoalgebra, ``UpgradeEnvelope.floor_forever] do
    let axioms ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    unless axioms.all (fun ax => ax == ``propext || ax == ``Quot.sound) do
      throwError "unexpected axioms for {name}: {axioms.toList}"

end Obend.Teeth.GroveAndRepair
