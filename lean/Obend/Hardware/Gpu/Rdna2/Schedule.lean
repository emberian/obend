/-
# Obend.Hardware.Gpu.Rdna2.Schedule — a graph's emitted schedule as certified stages

What the emitter dispatches for a graph is `ArrayEmit.compile`'s action list (`ArrayEmit.Schedule`): an
elementwise action is one dispatch of the plan's ordinary kernels (`runStage`), a collective is an admitted
block program (`ArrayKernel.Program`, its dispatches emitted by `BlockEmit`). Both are read here as
certificate stages (`Cert.Spec`) over one flat memory (`BlockLower.FlatMemory`) whose device space is the
wire buffer: `elemSpec` is a plan stage (its table `gpuTableUpTo`, its meaning the action's), and a
collective's dispatches are `Block.blockSpec`. The host's index buffer is `ArrayEmit.scheduleTables`, the
function the plan's `tables` is written from, so each collective's descriptor tables sit where its shaders
read them.

`certifySchedule_sound`: if the certificate accepts and its residuals hold, then for every wire buffer the
dumped programs, run on the model as the host dispatches them, succeed and leave in every word of the
buffer what `ArrayEmit.evalActions` (the semantics `ArrayEmitCorrect.compile_runProgram` relates to the
plan) leaves in the device space.
-/
module

public import Obend.Hardware.Gpu.Rdna2.Block
public import Obend.Hardware.Gpu.ArrayEmit
import all Obend.Hardware.Gpu.Rdna2.Encodings
import all Obend.Hardware.Gpu.Rdna2.Decode
import all Obend.Hardware.Gpu.Rdna2.Block
import all Obend.Hardware.Gpu.Rdna2.Cert
import all Obend.Hardware.Gpu.Rdna2.Host
import all Obend.Hardware.Gpu.Rdna2.Join
import all Obend.Hardware.Gpu.Rdna2.Lower
import all Obend.Hardware.Gpu.Rdna2.Equiv
import all Obend.Hardware.Gpu.Rdna2.Sym
import all Obend.Hardware.Gpu.Rdna2.Term
import all Obend.Hardware.Gpu.Rdna2.Semantics
import all Init.Data.Array.QSort.Basic
import all Init.Data.Array.QSort
import Init.Data.String.Search
import Init.Data.String.Lemmas
import Init.Data.String.TakeDrop

public section

namespace Obend.Hardware.Gpu.Rdna2.Schedule

open Obend.Hardware.Gpu Obend.Hardware.ArrayHypergraph Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.BlockLower
open Obend.Hardware.Gpu.ArrayEmit Obend.Hardware.Gpu.ArraySchedule
open Obend.Hardware.Gpu.Rdna2 Obend.Hardware.Gpu.Rdna2.Block Tm

/-- The flat memory whose device space is `f`, every other space zero. -/
@[expose] def ofDevice (f : Nat → Word) : FlatMemory := fun a => if a.1 = .device then f a.2 else 0

/-- The stages of one action, each awaiting the LDS its dump allocates: an elementwise action is one
dispatch meaning `Action.eval`; a collective is one `blockSpec` per dispatch, with no constants. -/
def actionSpecs (p : GpuProgram) (words : Nat) : Action → List (Nat → Spec FlatMemory)
  | a@(.elementwise _ stage) => [fun lds =>
      { threads := stage.threads, lds := lds,
        table := fun rd => gpuTableUpTo p.consts.toArray p.tables.toArray stage rd (foldCache rd stage) words,
        den := a.eval p.consts p.tables }]
  | .collective b => b.dispatches.map fun d lds => blockSpec b d words #[] lds

def specsOf (p : GpuProgram) (words : Nat) (acts : List Action) : List (Nat → Spec FlatMemory) :=
  acts.flatMap (actionSpecs p words)

/-- Every dispatch of the schedule with the LDS dwords its dump states. -/
def scheduleSpecs (p : GpuProgram) (words : Nat) (acts : List Action) (ldss : List Nat) : List (Spec FlatMemory) :=
  ((specsOf p words acts).zip ldss).map fun y => y.1 y.2

/-- An elementwise action reads and writes only inside the buffer (`ArraySchedule.checkBounds`). -/
def actionBounded (p : GpuProgram) (words : Nat) : Action → Bool
  | .elementwise _ stage => checkBounds words p.tables stage
  | .collective _ => true

/-- The certificate of a schedule's dumps `progs` (dispatch `k` with `ldss[k]` dwords of LDS). -/
@[expose] def certifySchedule (p : GpuProgram) (sched : Schedule) (ldss : List Nat) (progs : List Program)
    (rs : List Residual) : Bool :=
  let acts := sched.actions.toList
  sched.words < 2 ^ 29 && p.words ≤ sched.words && (specsOf p sched.words acts).length == ldss.length &&
  acts.all (actionBounded p sched.words) &&
  match checkProgram sched.words (layoutMem sched.words p.consts (scheduleTables p acts))
      (scheduleSpecs p sched.words acts ldss) progs {} {} with
  | some need => need.toList.all rs.contains
  | none => false

/-- The residuals the schedule's dumps need (for the generator of the module that proves them). -/
def neededSchedule (p : GpuProgram) (sched : Schedule) (ldss : List Nat) (progs : List Program) :
    Option (List Residual) :=
  let acts := sched.actions.toList
  (checkProgram sched.words (layoutMem sched.words p.consts (scheduleTables p acts))
    (scheduleSpecs p sched.words acts ldss) progs {} {}).map (·.toList)

/-! ## Each stage keeps its promise -/

theorem elem_sound (p : GpuProgram) (words : Nat) (k : Nat) (stage : GpuStage) (lds : Nat)
    (hb : checkBounds words p.tables stage = true) :
    ({ threads := stage.threads, lds := lds,
       table := fun rd => gpuTableUpTo p.consts.toArray p.tables.toArray stage rd (foldCache rd stage) words,
       den := (Action.elementwise k stage).eval p.consts p.tables } : Spec FlatMemory).Sound words
      (projB words) (ConstsOk #[]) := by
  refine ⟨?_, fun part h => nomatch h⟩
  intro rd env x T _ hrd hT
  let E := projB words x
  have hrd' : (fun j => (rd j).ev env) = E := funext hrd
  have hkb := checkBounds_sound words p.tables stage hb
  have hagree : AgreeBelow words (runStage p.consts p.tables (fun i => x (.device, i)) stage)
      (runStage p.consts p.tables E stage) :=
    runStage_agreeBelow _ _ words _ _ stage (fun i hi => by simp [E, projB, hi]) hkb
  have hden : ∀ i, i < words → projB words ((Action.elementwise k stage).eval p.consts p.tables x) i
      = runStage p.consts p.tables E stage i := by
    intro i hi
    simp only [projB, hi, ite_true, Action.eval]
    exact hagree i hi
  have spec := gpuTableUpTo_spec _ _ stage rd _ words T hT
  refine ⟨fun j h => absurd h (Nat.not_lt_zero _), fun i t ht => ?_, fun i hi => ?_⟩
  · obtain ⟨hi, kk, hf, hkv⟩ := (spec i).1 t ht
    refine ⟨hi, ?_⟩
    rw [hden i hi]
    have hk := pKernel_sound env _ _ _ kk _ t (kvOf_sound (foldCache_mem rd stage) _ _ _ hkv)
    rw [List.toList_toArray, List.toList_toArray, hrd'] at hk
    show t.ev env = runStage p.consts p.tables E stage i
    unfold runStage; rw [hf]; exact hk
  · by_cases h : i < words
    · rw [hden i h]
      have hn := (spec i).2 hi h
      show runStage p.consts p.tables E stage i = E i
      unfold runStage; rw [hn]
    · simp [projB, h]

theorem specs_sound (p : GpuProgram) (words : Nat) (acts : List Action) (ldss : List Nat)
    (hb : acts.all (actionBounded p words) = true) :
    ∀ s ∈ scheduleSpecs p words acts ldss, s.Sound words (projB words) (ConstsOk #[]) := by
  intro s hs
  obtain ⟨⟨f, l⟩, hm, rfl⟩ := List.mem_map.mp hs
  obtain ⟨a, ha, hf⟩ := List.mem_flatMap.mp (List.of_mem_zip hm).1
  have hba := List.all_eq_true.mp hb a ha
  cases a with
  | elementwise k stage =>
    simp only [actionSpecs, List.mem_singleton] at hf
    subst hf
    exact elem_sound p words k stage l hba
  | collective b =>
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hf
    exact blockSpec_sound b d words #[] l

/-! ## The stages compose to the schedule's meaning -/

theorem zip_den {σ : Type} : ∀ (fs : List (Nat → Spec σ)) (ls : List Nat) (x : σ), fs.length = ls.length →
    (∀ f ∈ fs, ∀ l, (f l).den = (f 0).den) →
    ((fs.zip ls).map fun y => y.1 y.2).foldl (fun x s => s.den x) x = fs.foldl (fun x f => (f 0).den x) x
  | [], [], _, _, _ => rfl
  | f :: fs, l :: ls, x, h, hd => by
    simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons]
    rw [hd f List.mem_cons_self l]
    exact zip_den fs ls _ (by simpa using h) fun g hg => hd g (List.mem_cons_of_mem _ hg)
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

theorem actionSpecs_den (p : GpuProgram) (words : Nat) (a : Action) :
    ∀ f ∈ actionSpecs p words a, ∀ l, (f l).den = (f 0).den := by
  intro f hf l
  cases a with
  | elementwise k stage => simp only [actionSpecs, List.mem_singleton] at hf; subst hf; rfl
  | collective b => obtain ⟨d, -, rfl⟩ := List.mem_map.mp hf; rfl

theorem actionSpecs_foldl (p : GpuProgram) (words : Nat) (a : Action) (x : FlatMemory) :
    (actionSpecs p words a).foldl (fun x f => (f 0).den x) x = a.eval p.consts p.tables x := by
  cases a with
  | elementwise k stage => rfl
  | collective b =>
    simp only [actionSpecs, List.foldl_map, Action.eval, lowerProgram]
    rfl

theorem specsOf_foldl (p : GpuProgram) (words : Nat) :
    ∀ (acts : List Action) (x : FlatMemory),
      (specsOf p words acts).foldl (fun x f => (f 0).den x) x = evalActions p acts x
  | [], _ => rfl
  | a :: acts, x => by
    simp only [specsOf, List.flatMap_cons, List.foldl_append] at *
    rw [actionSpecs_foldl]
    exact specsOf_foldl p words acts _

/-! ## The certificate -/

/-- If the certificate is accepted and every residual it names holds, then for every content `f` of the
wire buffer, the decoded programs, run on the model as the host dispatches the schedule, succeed and leave
in every word of the buffer what the schedule's actions leave in the device space. -/
theorem certifySchedule_sound (p : GpuProgram) (sched : Schedule) (ldss : List Nat) (progs : List Program)
    (rs : List Residual) (hc : certifySchedule p sched ldss progs rs = true) (hrs : ∀ r ∈ rs, r.Holds)
    (f : Nat → Word) :
    ∃ m, runDispatch (dispatchesOf (scheduleSpecs p sched.words sched.actions.toList ldss) progs)
        (memOf sched.words p.consts (scheduleTables p sched.actions.toList) f) = some m ∧
      ∀ i, i < sched.words → wordAt m i = evalActions p sched.actions.toList (ofDevice f) (.device, i) := by
  unfold certifySchedule at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hw, -⟩, hlen⟩, hb⟩, hcp⟩ := hc
  split at hcp
  · rename_i need hneed
    have hfin : ∀ r, need.contains r = true → r.Holds := by
      intro r hr
      apply hrs
      have := List.all_eq_true.mp hcp r (by rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]; exact hr)
      simpa using this
    have hss := specs_sound p sched.words sched.actions.toList ldss hb
    have h0 := memOf_start sched.words p.consts (scheduleTables p sched.actions.toList) hw f
    have hproj : projB sched.words (ofDevice f) = fun j => if j < sched.words then f j else 0 := by
      funext j; simp [projB, ofDevice]
    rw [← hproj] at h0
    obtain ⟨m, known', hrun, hend, -⟩ := checkProgram_sound (x := ofDevice f) hw _ progs {} {} need _ hss
      hneed hfin h0 (fun j h => absurd h (Nat.not_lt_zero _))
    refine ⟨m, hrun, fun i hi => ?_⟩
    obtain ⟨lo, hi', e0, e1, e⟩ := hend.word i hi
    have a0 : wDw + UInt64.ofNat (2 * i) = dwLo i := rfl
    unfold wordAt
    rw [a0, e0, e1]
    simp only [Option.getD_some]
    rw [e]
    unfold scheduleSpecs
    rw [zip_den _ _ _ hlen (fun g hg => by
      obtain ⟨a, -, ha⟩ := List.mem_flatMap.mp hg
      exact actionSpecs_den p _ a g ha), specsOf_foldl]
    simp only [projB, hi, ite_true]
  · simp at hcp

/-! ## Schedule certificate witnesses -/

/-- A stage inside its buffer: four words, `[0, 2)` then `[2, 4)`, concatenated into `[4, 8)` of eight. -/
example : ∃ (p : GpuProgram) (words : Nat) (a : Action), actionBounded p words a = true :=
  ⟨{ words := 8, wireBase := [], wireLen := [], consts := [], tables := [], inputs := [], outputs := [],
     stages := [⟨[⟨4, 4, .concat 0 2 2⟩]⟩] }, 8, .elementwise 0 ⟨[⟨4, 4, .concat 0 2 2⟩]⟩, by decide⟩

/-- The same stage in a buffer of seven words writes past its end. -/
example : actionBounded
    { words := 8, wireBase := [], wireLen := [], consts := [], tables := [], inputs := [], outputs := [],
      stages := [⟨[⟨4, 4, .concat 0 2 2⟩]⟩] } 7 (.elementwise 0 ⟨[⟨4, 4, .concat 0 2 2⟩]⟩) = false := by
  decide

/-- That stage's schedule is one dispatch: its four threads, with the LDS its dump states. -/
example : ∃ (p : GpuProgram) (words : Nat) (acts : List Action) (ldss : List Nat),
    (scheduleSpecs p words acts ldss).map (fun s => (s.threads, s.lds)) = [(4, 16)] :=
  ⟨{ words := 8, wireBase := [], wireLen := [], consts := [], tables := [], inputs := [], outputs := [],
     stages := [⟨[⟨4, 4, .concat 0 2 2⟩]⟩] }, 8, [.elementwise 0 ⟨[⟨4, 4, .concat 0 2 2⟩]⟩], [16],
   by decide⟩

/-- A zero-length output still compiles to one dispatch, as in stage zero of the
`soac-empty` dump. The wire buffer remains allocated. No wave launches, so any
instruction stream suffices, but the dump must contain a program for that dispatch. -/
example (prog : Program) :
    ∃ (p : GpuProgram) (sched : Schedule) (ldss : List Nat) (progs : List Program) (rs : List Residual),
      p.stages ≠ [] ∧ compile p = .ok sched ∧
      certifySchedule p sched ldss progs rs = true ∧
      certifySchedule p sched ldss [] rs = false := by
  let stage : GpuStage := ⟨[⟨0, 0, .const 0⟩]⟩
  let p : GpuProgram :=
    { words := 1, wireBase := [0], wireLen := [0], consts := [],
      tables := [], inputs := [], outputs := [0], stages := [stage] }
  refine ⟨p, ⟨1, #[.elementwise 0 stage]⟩, [0], [prog], [], by simp [p], rfl, ?_, rfl⟩
  simp [p, stage, certifySchedule, scheduleSpecs, specsOf, actionSpecs, checkProgram, checkStage,
    checkStageW, show (⟨[⟨0, 0, .const 0⟩]⟩ : GpuStage).threads = 0 from rfl,
    gpuTableUpTo, Kernel.owns, groupsOf, lanes, parMap_eq, mergeWaves, tableStored,
    Std.HashSet.fold_eq_foldl_toList, actionBounded] <;> decide

/-- A schedule with a dispatch is refused against a dump that lacks its stage. -/
example : certifySchedule
    { words := 8, wireBase := [], wireLen := [], consts := [], tables := [], inputs := [], outputs := [],
      stages := [⟨[⟨4, 4, .concat 0 2 2⟩]⟩] }
    ⟨8, #[.elementwise 0 ⟨[⟨4, 4, .concat 0 2 2⟩]⟩]⟩ [16] [] [] = false := by
  decide

private def decGoFast (ws : List UInt32) (w0 : UInt32) : List Encoding → Option (Inst × Nat)
  | [] => none
  | e :: es =>
    if !encodingMatches w0 e then decGoFast ws w0 es else
    let k := e.bitCount / 32
    if ws.length < k then decGoFast ws w0 es else
    let taken := ws.take k
    let fs := fieldsOf e taken
    match lookupField fs "OP" with
    | none => decGoFast ws w0 es
    | some op =>
      let entries := instructionEntries (e.name, op)
      let hit := entries.find? fun (_, ie) =>
        match e.conditions.find? (·.name == ie.condition) with
        | some c => c.expr.eval fs
        | none => e.conditions.isEmpty && ie.condition == "default"
      match hit with
      | some (i, ie) => some (⟨i, e, ie, fs, taken⟩, k)
      | none => decGoFast ws w0 es

private def decodeInstFast (ws : List UInt32) : Option (Inst × Nat) :=
  match ws with
  | [] => none
  | w0 :: _ => decGoFast ws w0 encodings

set_option maxRecDepth 100000 in
private theorem encOrd_eq_encodings : encodingsInOrder = encodings := by
  set_option cbv.maxSteps 2000000 in cbv

set_option maxRecDepth 200000 in
private theorem decodeInst_go_cons (ws : List UInt32) (w0 : UInt32) (e : Encoding) (es : List Encoding) :
    decodeInst.go ws w0 (e :: es) =
      if !encodingMatches w0 e then decodeInst.go ws w0 es else
      let k := e.bitCount / 32
      if ws.length < k then decodeInst.go ws w0 es else
      let taken := ws.take k
      let fs := fieldsOf e taken
      match lookupField fs "OP" with
      | none => decodeInst.go ws w0 es
      | some op =>
        let entries := instructionEntries (e.name, op)
        let hit := entries.find? fun (_, ie) =>
          match e.conditions.find? (·.name == ie.condition) with
          | some c => c.expr.eval fs
          | none => e.conditions.isEmpty && ie.condition == "default"
        match hit with
        | some (i, ie) => some (⟨i, e, ie, fs, taken⟩, k)
        | none => decodeInst.go ws w0 es := by
  rw [decodeInst.go.eq_def]
  dsimp only
  by_cases h1 : (!encodingMatches w0 e) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1]
    by_cases h2 : ws.length < e.bitCount / 32
    · simp only [h2, ↓reduceIte]
    · simp only [h2, ↓reduceIte]
      cases lookupField (fieldsOf e (ws.take (e.bitCount / 32))) "OP" with
      | none => rfl
      | some op => dsimp only; rw [instIndex_getD]; rfl

set_option maxRecDepth 200000 in
private theorem decGoFast_cons (ws : List UInt32) (w0 : UInt32) (e : Encoding) (es : List Encoding) :
    decGoFast ws w0 (e :: es) =
      if !encodingMatches w0 e then decGoFast ws w0 es else
      let k := e.bitCount / 32
      if ws.length < k then decGoFast ws w0 es else
      let taken := ws.take k
      let fs := fieldsOf e taken
      match lookupField fs "OP" with
      | none => decGoFast ws w0 es
      | some op =>
        let entries := instructionEntries (e.name, op)
        let hit := entries.find? fun (_, ie) =>
          match e.conditions.find? (·.name == ie.condition) with
          | some c => c.expr.eval fs
          | none => e.conditions.isEmpty && ie.condition == "default"
        match hit with
        | some (i, ie) => some (⟨i, e, ie, fs, taken⟩, k)
        | none => decGoFast ws w0 es := rfl

private theorem decodeInst_go_eq_fast (ws : List UInt32) (w0 : UInt32) (es : List Encoding) :
    decodeInst.go ws w0 es = decGoFast ws w0 es := by
  induction es with
  | nil => rw [decodeInst.go.eq_def]; rfl
  | cons e es ih =>
    rw [decodeInst_go_cons, decGoFast_cons, ih]

private theorem decodeInst_eq_fast (ws : List UInt32) :
    decodeInst ws = decodeInstFast ws := by
  cases ws with
  | nil => rfl
  | cons w0 rest =>
    unfold decodeInst decodeInstFast
    dsimp only
    rw [encOrd_eq_encodings]
    exact decodeInst_go_eq_fast (w0 :: rest) w0 encodings

private def decodeProgFast (ws : Array UInt32) : Except String Program :=
  go ws.size 0 (Array.replicate ws.size none)
where
  go : Nat → Nat → Program → Except String Program
    | fuel, d, out =>
      if d ≥ ws.size then .ok out else
      match fuel with
      | 0 => .error "decodeProgram ran out of fuel"
      | fuel + 1 =>
        match decodeInstFast (ws.extract d (min ws.size (d + 5))).toList with
        | none => .error "no inst"
        | some (i, k) =>
          if k == 0 then .error "zero"
          else go fuel (d + k) (out.set! d (some i))

private theorem decodeProgram_go_eq_fast_ok (ws : Array UInt32) (p : Program) :
    ∀ fuel d out, decodeProgFast.go ws fuel d out = .ok p → decodeProgram.go ws fuel d out = .ok p
  | 0, d, out, hgo => by
    unfold decodeProgram.go
    unfold decodeProgFast.go at hgo
    split at hgo
    · simp_all
    · cases hgo
  | fuel + 1, d, out, hgo => by
    unfold decodeProgram.go
    unfold decodeProgFast.go at hgo
    by_cases hge : d ≥ ws.size
    · simp only [hge, ↓reduceIte] at hgo ⊢; exact hgo
    · simp only [hge, ↓reduceIte, decodeInst_eq_fast] at hgo ⊢
      revert hgo
      cases decodeInstFast (ws.extract d (min ws.size (d + 5))).toList with
      | none => intro hgo; cases hgo
      | some ik =>
        intro hgo
        dsimp only at hgo ⊢
        by_cases hk : (ik.2 == 0) = true
        · simp only [hk, ↓reduceIte] at hgo; cases hgo
        · simp only [hk] at hgo ⊢
          exact decodeProgram_go_eq_fast_ok ws p fuel _ _ hgo

private theorem decodeProgram_eq_fast_ok (ws : Array UInt32) (p : Program)
    (h : decodeProgFast ws = .ok p) : decodeProgram ws = .ok p := by
  unfold decodeProgram
  unfold decodeProgFast at h
  exact decodeProgram_go_eq_fast_ok ws p ws.size 0 (Array.replicate ws.size none) h

private def storeConst7Words : Array UInt32 :=
  #[0x7da80081, 0xb0038000, 0xf4080001, 0xfa000000, 0xbf8cc07f,
    0x7e080287, 0x7e0a0280, 0xe0741000, 0x80000400, 0xbbfd0000, 0xbf810000]

private def storeConst7Prog : Program :=
  (decodeProgFast storeConst7Words).toOption.getD #[]

set_option maxRecDepth 200000 in
private theorem decodeProgram_storeConst7 :
    decodeProgram storeConst7Words = .ok storeConst7Prog := by
  apply decodeProgram_eq_fast_ok
  unfold storeConst7Prog
  have hOk : (decodeProgFast storeConst7Words).isOk = true := by
    set_option cbv.maxSteps 2000000 in cbv
  cases h : decodeProgFast storeConst7Words with
  | error e => rw [h] at hOk; cases hOk
  | ok p => rfl

private theorem hashMap_getElem?_insert_cbv {α β : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (m : Std.HashMap α β) (k a : α) (v : β) :
    (m.insert k v)[a]? = if k == a then some v else m[a]? :=
  Std.HashMap.getElem?_insert

private theorem hashMap_getElem?_empty_cbv {α β : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] {c : Nat} (a : α) :
    (Std.HashMap.emptyWithCapacity c : Std.HashMap α β)[a]? = none :=
  Std.HashMap.getElem?_emptyWithCapacity

private theorem hashMap_get?_insert_cbv {α β : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (m : Std.HashMap α β) (k a : α) (v : β) :
    (m.insert k v).get? a = if k == a then some v else m.get? a :=
  Std.HashMap.getElem?_insert

private theorem hashMap_get?_empty_cbv {α β : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] {c : Nat} (a : α) :
    (Std.HashMap.emptyWithCapacity c : Std.HashMap α β).get? a = none :=
  Std.HashMap.getElem?_emptyWithCapacity

private theorem hashSet_contains_insert_cbv {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (s : Std.HashSet α) (k a : α) :
    (s.insert k).contains a = ((k == a) || s.contains a) :=
  Std.HashSet.contains_insert

private theorem hashSet_contains_empty_cbv {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] {c : Nat} (a : α) :
    (Std.HashSet.emptyWithCapacity c : Std.HashSet α).contains a = false :=
  Std.HashSet.contains_emptyWithCapacity

private theorem srun_succ_cbv (prog : Program) (n : Nat) (s : SymWave) :
    srun prog (n + 1) s =
      if s.halted || s.err.isSome then s else
      match joinTarget prog s with
      | none => srun prog n (step prog s)
      | some T =>
        let s1 : SymWave := { s with pc := s.pc + 1 }
        let fall := runTo prog T n s1
        let zero := runTo prog T n { s1 with exec := (Dom.lit 0, Dom.lit 0) }
        if joinOk T s fall.1 zero.1 then
          srun prog (n - fall.2) (mergeG (fun a b => decide (a = b)) (execzV s) s fall.1 T)
        else s.fail "S_CBRANCH_EXECZ on an unknown EXEC: the region does not join, or writes with EXEC zero" := by
  rw [srun.eq_def]; rfl

attribute [local cbv_eval] hashMap_getElem?_insert_cbv hashMap_getElem?_empty_cbv
  hashMap_get?_insert_cbv hashMap_get?_empty_cbv
  hashSet_contains_insert_cbv hashSet_contains_empty_cbv

private theorem hashMap_toList_one {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (k : α) (v : β) :
    (({} : Std.HashMap α β).insert k v).toList = [(k, v)] := by
  apply List.Perm.eq_singleton
  simpa [Std.HashMap.toList_empty] using
    (Std.HashMap.toList_insert_perm (m := ({} : Std.HashMap α β)) (k := k) (v := v))

private theorem hashMap_toList_two {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (k1 k2 : α) (v1 v2 : β) (hne : (k2 == k1) = false) :
    let m := (({} : Std.HashMap α β).insert k1 v1).insert k2 v2
    m.toList = [(k1, v1), (k2, v2)] ∨ m.toList = [(k2, v2), (k1, v1)] := by
  intro m
  have h1 := hashMap_toList_one k1 v1
  have h2 : m.toList.Perm [(k2, v2), (k1, v1)] := by
    have hp := Std.HashMap.toList_insert_perm (m := ({} : Std.HashMap α β).insert k1 v1) (k := k2) (v := v2)
    simpa [m, h1, hne] using hp
  cases hL : m.toList with
  | nil => rw [hL] at h2; have := h2.length_eq; simp at this
  | cons a rest =>
    cases rest with
    | nil => rw [hL] at h2; have := h2.length_eq; simp at this
    | cons b rest2 =>
      cases rest2 with
      | nil =>
        rw [hL] at h2
        have ha : a ∈ [(k2, v2), (k1, v1)] := h2.subset (by simp)
        have hb : b ∈ [(k2, v2), (k1, v1)] := h2.subset (by simp)
        have hnd : [a, b].Nodup := by
          have hnd' : [(k2, v2), (k1, v1)].Nodup := by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
            refine ⟨fun heq => ?_, not_false⟩
            have hk : k2 = k1 := congrArg Prod.fst heq
            subst hk
            simp at hne
          exact (h2.nodup_iff).mpr hnd'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · simp at hnd
        · exact Or.inr rfl
        · exact Or.inl rfl
        · simp at hnd
      | cons _ _ => rw [hL] at h2; have := h2.length_eq; simp at this

private theorem srun_step_eq (prog : Program) (n : Nat) (s : SymWave)
    (hH : s.halted = false) (hE : s.err = none) (hJ : joinTarget prog s = none) :
    srun prog (n + 1) s = srun prog n (step prog s) := by
  rw [srun_succ_cbv]
  simp only [hH, hE, Option.isSome_none, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hJ]

private theorem srun_halted_eq (prog : Program) (n : Nat) (s : SymWave)
    (hH : s.halted = true) :
    srun prog (n + 1) s = s := by
  rw [srun_succ_cbv]
  simp only [hH, Bool.true_or, ↓reduceIte]

private def stripInst (i : Inst) : Inst :=
  ⟨⟨i.inst.name, i.inst.isBranch, i.inst.isConditionalBranch, i.inst.isTerminator, i.inst.isImmediatelyExecuted, []⟩,
   ⟨i.enc.name, 0, 0, 0, [], [], []⟩,
   ⟨"", "", 0, i.ie.operands.filter (fun o => o.field == "VDATA" || o.field == "SDATA")⟩,
   i.fields, i.words⟩

private theorem find?_filter_keep {α : Type} (p q : α → Bool) (h : ∀ a, p a = true → q a = true) :
    ∀ xs : List α, (xs.filter q).find? p = xs.find? p
  | [] => rfl
  | x :: xs => by
    simp only [List.filter_cons, List.find?_cons]
    cases hq : q x with
    | true =>
      simp only [↓reduceIte, List.find?_cons]
      cases hp : p x with
      | true => rfl
      | false => exact find?_filter_keep p q h xs
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hp : p x = false := by
        cases hp' : p x with
        | false => rfl
        | true => have := h x hp'; rw [this] at hq; cases hq
      rw [hp]
      exact find?_filter_keep p q h xs

private theorem execInst_stripInst (i : Inst) (s : SymWave) :
    execInst (stripInst i) s = execInst i s := by
  have hV : (stripInst i).ie.operands.find? (·.field == "VDATA") = i.ie.operands.find? (·.field == "VDATA") :=
    find?_filter_keep _ _ (fun a ha => by simp [ha]) i.ie.operands
  have hS : (stripInst i).ie.operands.find? (·.field == "SDATA") = i.ie.operands.find? (·.field == "SDATA") :=
    find?_filter_keep _ _ (fun a ha => by simp [ha]) i.ie.operands
  have hMod : modifiersClear (stripInst i) = modifiersClear i := rfl
  have hName : (stripInst i).name = i.name := rfl
  unfold execInst
  rw [hMod, hName]
  cases (!modifiersClear i) with
  | true => rfl
  | false =>
    dsimp only
    cases instOp i.name <;> try rfl
    · unfold execSmem; rw [hS]; rfl
    · unfold execMubuf; rw [hV]; rfl
    · unfold execMubuf; rw [hV]; rfl

private theorem step_map_stripInst (prog : Program) (s : SymWave) :
    step (prog.map (Option.map stripInst)) s = step prog s := by
  unfold step
  split
  · rfl
  · simp only [Array.getElem?_map]
    cases prog[s.pc]? with
    | none => rfl
    | some oi =>
      cases oi with
      | none => rfl
      | some i => exact execInst_stripInst i _

private theorem joinTarget_map_stripInst (prog : Program) (s : SymWave) :
    joinTarget (prog.map (Option.map stripInst)) s = joinTarget prog s := by
  unfold joinTarget
  simp only [Array.getElem?_map]
  cases prog[s.pc]? with
  | none => rfl
  | some oi =>
    cases oi with
    | none => rfl
    | some i => rfl

private theorem run_map_stripInst (prog : Program) :
    ∀ (n : Nat) (s : SymWave), run (prog.map (Option.map stripInst)) n s = run prog n s
  | 0, s => rfl
  | n + 1, s => by
    unfold run
    split
    · rfl
    · rw [step_map_stripInst, run_map_stripInst]

private theorem runTo_map_stripInst (prog : Program) (T : Nat) :
    ∀ (n : Nat) (s : SymWave), runTo (prog.map (Option.map stripInst)) T n s = runTo prog T n s
  | 0, s => rfl
  | n + 1, s => by
    unfold runTo
    split
    · rfl
    · rw [step_map_stripInst, runTo_map_stripInst]

private theorem srun_map_stripInst (prog : Program) :
    ∀ (n : Nat) (s : SymWave), srun (prog.map (Option.map stripInst)) n s = srun prog n s := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s
    cases n with
    | zero => rw [srun.eq_def, srun.eq_def]; exact run_map_stripInst prog 0 s
    | succ k =>
      rw [srun_succ_cbv, srun_succ_cbv, joinTarget_map_stripInst]
      split
      · rfl
      · cases joinTarget prog s with
        | none => rw [step_map_stripInst]; exact ih k (Nat.lt_succ_self k) _
        | some T =>
          simp only [runTo_map_stripInst]
          split
          · exact ih (k - (runTo prog T k { s with pc := s.pc + 1 }).2) (by omega) _
          · rfl

private theorem symWave_map_stripInst (words : Nat) (lay : Memory) (prog : Program)
    (lds : Nat) (known : Known) (ex : UInt64 → Bool) (g : Nat) :
    symWave words lay (prog.map (Option.map stripInst)) lds known ex g =
      symWave words lay prog lds known ex g := by
  unfold symWave fuelOf
  simp only [Array.size_map]
  exact srun_map_stripInst prog _ _

private def mkCompactInst (name : String) (isTerm isImm : Bool) (encName : String)
    (ops : List Operand) (fields : List (String × Nat)) (words : List UInt32) : Inst :=
  ⟨⟨name, false, false, isTerm, isImm, []⟩, ⟨encName, 0, 0, 0, [], [], []⟩, ⟨"", "", 0, ops⟩, fields, words⟩

private def sc7_i0 : Inst := mkCompactInst "V_CMPX_GT_U32" false false "ENC_VOPC" [] [("ENCODING", 62), ("OP", 212), ("SRC0", 129), ("VSRC1", 0)] [2108162177]
private def sc7_i1 : Inst := mkCompactInst "S_MOVK_I32" false false "ENC_SOPK" [] [("ENCODING", 11), ("OP", 0), ("SDST", 3), ("SIMM16", 32768)] [2953019392]
private def sc7_i2 : Inst := mkCompactInst "S_LOAD_DWORDX4" false false "ENC_SMEM" [⟨"SDATA", "OPR_SREG", "FMT_ANY", 128, false, true, false, true⟩]
    [("DLC", 0), ("ENCODING", 61), ("GLC", 0), ("OFFSET", 0), ("OP", 2), ("SBASE", 1), ("SDATA", 0), ("SOFFSET", 125)] [4094164993, 4194304000]
private def sc7_i4 : Inst := mkCompactInst "S_WAITCNT" false true "ENC_SOPP" [] [("ENCODING", 383), ("OP", 12), ("SIMM16", 49279)] [3213672575]
private def sc7_i5 : Inst := mkCompactInst "V_MOV_B32" false false "ENC_VOP1" [] [("ENCODING", 63), ("OP", 1), ("SRC0", 135), ("VDST", 4)] [2114454151]
private def sc7_i6 : Inst := mkCompactInst "V_MOV_B32" false false "ENC_VOP1" [] [("ENCODING", 63), ("OP", 1), ("SRC0", 128), ("VDST", 5)] [2114585216]
private def sc7_i7 : Inst := mkCompactInst "BUFFER_STORE_DWORDX2" false false "ENC_MUBUF" [⟨"VDATA", "OPR_VGPR", "FMT_ANY", 64, true, false, false, true⟩]
    [("DLC", 0), ("ENCODING", 56), ("GLC", 0), ("IDXEN", 0), ("LDS", 0), ("OFFEN", 1), ("OFFSET", 0), ("OP", 29), ("SLC", 0), ("SOFFSET", 128), ("SRSRC", 0), ("TFE", 0), ("VADDR", 0), ("VDATA", 4)] [3765702656, 2147484672]
private def sc7_i9 : Inst := mkCompactInst "S_WAITCNT_VSCNT" false true "ENC_SOPK" [] [("ENCODING", 11), ("OP", 23), ("SDST", 125), ("SIMM16", 0)] [3153920000]
private def sc7_i10 : Inst := mkCompactInst "S_ENDPGM" true false "ENC_SOPP" [] [("ENCODING", 383), ("OP", 1), ("SIMM16", 0)] [3212902400]

private def sc7Compact : Program :=
  #[some sc7_i0, some sc7_i1, some sc7_i2, none, some sc7_i4, some sc7_i5, some sc7_i6, some sc7_i7, none, some sc7_i9, some sc7_i10]

set_option maxRecDepth 200000 in
private theorem storeConst7Prog_strip : storeConst7Prog.map (Option.map stripInst) = sc7Compact := by
  set_option cbv.maxSteps 2000000 in cbv

private theorem list_mapM_eq_some {α β : Type} (f : α → Option β) (g : α → β) (xs : List α)
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.mapM_cons, h x List.mem_cons_self, bind, Option.bind, ih (fun y hy => h y (List.mem_cons_of_mem _ hy)), pure, List.map_cons]

private theorem array_getD_setBang_eq {α : Type} (a : Array α) (i : Nat) (v d : α) (hi : i < a.size) :
    (a.set! i v).getD i d = v := by simp [Array.getD_eq_getD_getElem?, hi]

private theorem array_getD_setBang_ne {α : Type} (a : Array α) (i j : Nat) (v d : α) (hne : i ≠ j) :
    (a.set! i v).getD j d = a.getD j d := by simp [Array.getD_eq_getD_getElem?, hne]

private theorem writeSgpr_size (s : SymWave) (n : Nat) (v : Tm) : (writeSgpr s n v).sgpr.size = s.sgpr.size := by
  unfold writeSgpr; split <;> simp

private theorem readSgpr_writeSgpr_eq (s : SymWave) (n : Nat) (v : Tm) (h1 : n < sgprCount) (h2 : n < s.sgpr.size) :
    readSgpr (writeSgpr s n v) n = v := by
  unfold readSgpr writeSgpr; simp only [h1, ↓reduceIte]; exact array_getD_setBang_eq s.sgpr n v (Dom.lit 0) h2

private theorem readSgpr_writeSgpr_ne (s : SymWave) (n m : Nat) (v : Tm) (hne : n ≠ m) :
    readSgpr (writeSgpr s n v) m = readSgpr s m := by
  unfold readSgpr writeSgpr; split; exact array_getD_setBang_ne s.sgpr n m v (Dom.lit 0) hne; rfl

private theorem writeVgpr_size (s : SymWave) (r lane : Nat) (v : Tm) : (writeVgpr s r lane v).vgpr.size = s.vgpr.size := by
  unfold writeVgpr; split <;> simp

private theorem writeVgpr_ctrl (s : SymWave) (r lane : Nat) (v : Tm) :
    (writeVgpr s r lane v).sgpr = s.sgpr ∧ (writeVgpr s r lane v).exec = s.exec ∧
    (writeVgpr s r lane v).pc = s.pc ∧ (writeVgpr s r lane v).mem = s.mem ∧
    (writeVgpr s r lane v).halted = s.halted ∧ (writeVgpr s r lane v).err = s.err ∧
    (writeVgpr s r lane v).vgpr.size = s.vgpr.size := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, writeVgpr_size _ _ _ _⟩ <;> (unfold writeVgpr; split <;> rfl)

private theorem readVgpr_writeVgpr_eq (s : SymWave) (r lane : Nat) (v : Tm)
    (h1 : r < vgprCount) (h2 : r * lanes + lane < s.vgpr.size) : readVgpr (writeVgpr s r lane v) r lane = v := by
  unfold readVgpr writeVgpr; simp only [h1, ↓reduceIte]; exact array_getD_setBang_eq s.vgpr (r * lanes + lane) v (Dom.lit 0) h2

private theorem readVgpr_writeVgpr_ne (s : SymWave) (r lane r' lane' : Nat) (v : Tm)
    (hne : r * lanes + lane ≠ r' * lanes + lane') : readVgpr (writeVgpr s r lane v) r' lane' = readVgpr s r' lane' := by
  unfold readVgpr writeVgpr; split; exact array_getD_setBang_ne s.vgpr (r * lanes + lane) (r' * lanes + lane') v (Dom.lit 0) hne; rfl

private theorem writeLanes_ctrl (s : SymWave) (dst : Nat) (rs : List (Nat × Tm)) :
    (writeLanes s dst rs).sgpr = s.sgpr ∧ (writeLanes s dst rs).exec = s.exec ∧
    (writeLanes s dst rs).pc = s.pc ∧ (writeLanes s dst rs).mem = s.mem ∧
    (writeLanes s dst rs).halted = s.halted ∧ (writeLanes s dst rs).err = s.err ∧
    (writeLanes s dst rs).vgpr.size = s.vgpr.size := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons p rs ih =>
    simp only [writeLanes, List.foldl_cons]
    have hc := writeVgpr_ctrl s dst p.1 p.2
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (writeVgpr s dst p.1 p.2)
    exact ⟨h1.trans hc.1, h2.trans hc.2.1, h3.trans hc.2.2.1, h4.trans hc.2.2.2.1, h5.trans hc.2.2.2.2.1, h6.trans hc.2.2.2.2.2.1, h7.trans hc.2.2.2.2.2.2⟩

private theorem writeLanes_cons (s : SymWave) (dst lane : Nat) (v : Tm) (rs : List (Nat × Tm)) :
    writeLanes s dst ((lane, v) :: rs) = writeLanes (writeVgpr s dst lane v) dst rs := rfl

private theorem readVgpr_writeLanes_of_ne (s : SymWave) (dst r' lane' : Nat) (rs : List (Nat × Tm))
    (hne : ∀ p ∈ rs, dst * lanes + p.1 ≠ r' * lanes + lane') :
    readVgpr (writeLanes s dst rs) r' lane' = readVgpr s r' lane' := by
  induction rs generalizing s with
  | nil => rfl
  | cons p rs ih =>
    change readVgpr (writeLanes (writeVgpr s dst p.1 p.2) dst rs) r' lane' = readVgpr s r' lane'
    rw [ih _ (fun q hq => hne q (List.mem_cons_of_mem _ hq))]
    exact readVgpr_writeVgpr_ne s dst p.1 r' lane' p.2 (hne p List.mem_cons_self)

private theorem initWave_fold_ctrl (s : SymWave) (ls : List Nat) :
    let st := ls.foldl (fun st lane => writeVgpr st 0 lane (Dom.lit (UInt32.ofNat lane))) s
    st.sgpr = s.sgpr ∧ st.exec = s.exec ∧ st.pc = s.pc ∧ st.mem = s.mem ∧
    st.halted = s.halted ∧ st.err = s.err ∧ st.vgpr.size = s.vgpr.size := by
  induction ls generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons l ls ih =>
    simp only [List.foldl_cons]
    have hc := writeVgpr_ctrl s 0 l (Dom.lit (UInt32.ofNat l))
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (writeVgpr s 0 l (Dom.lit (UInt32.ofNat l)))
    exact ⟨h1.trans hc.1, h2.trans hc.2.1, h3.trans hc.2.2.1, h4.trans hc.2.2.2.1, h5.trans hc.2.2.2.2.1, h6.trans hc.2.2.2.2.2.1, h7.trans hc.2.2.2.2.2.2⟩

private theorem initWave_fold_readVgpr (s : SymWave) (ls : List Nat) (hnd : ls.Nodup)
    (hsize : ∀ l ∈ ls, l < s.vgpr.size) :
    ∀ l ∈ ls, readVgpr (ls.foldl (fun st lane => writeVgpr st 0 lane (Dom.lit (UInt32.ofNat lane))) s) 0 l =
      Dom.lit (UInt32.ofNat l) := by
  induction ls generalizing s with
  | nil => intro l hl; cases hl
  | cons a ls ih =>
    simp only [List.nodup_cons] at hnd; intro l hl; simp only [List.foldl_cons]
    rcases List.mem_cons.mp hl with rfl | hmem
    · have hPres : ∀ (s' : SymWave) (ys : List Nat), l ∉ ys →
          readVgpr (ys.foldl (fun st lane => writeVgpr st 0 lane (Dom.lit (UInt32.ofNat lane))) s') 0 l = readVgpr s' 0 l := by
        intro s' ys hna; induction ys generalizing s' with
        | nil => rfl
        | cons y ys ihy =>
          simp only [List.foldl_cons]; rw [ihy _ (fun hm => hna (List.mem_cons_of_mem _ hm))]
          exact readVgpr_writeVgpr_ne s' 0 y 0 l _ (by have : y ≠ l := fun h => hna (h ▸ List.mem_cons_self); omega)
      rw [hPres _ ls hnd.1]
      exact readVgpr_writeVgpr_eq s 0 l _ (by decide) (by simpa using hsize l List.mem_cons_self)
    · exact ih _ hnd.2 (fun x hx => by rw [writeVgpr_size]; exact hsize x (List.mem_cons_of_mem _ hx)) l hmem

private theorem writeSgpr_ctrl (s : SymWave) (n : Nat) (v : Tm) :
    (writeSgpr s n v).exec = s.exec ∧ (writeSgpr s n v).pc = s.pc ∧ (writeSgpr s n v).mem = s.mem ∧
    (writeSgpr s n v).halted = s.halted ∧ (writeSgpr s n v).err = s.err ∧
    (writeSgpr s n v).vgpr = s.vgpr ∧ (writeSgpr s n v).sgpr.size = s.sgpr.size := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, writeSgpr_size _ _ _⟩ <;> (unfold writeSgpr; split <;> rfl)

private theorem initWave_props (mem : SymMem) (setLo : UInt32) (g : Nat) (ldsB : UInt64) (ldsD : Nat) :
    let w : SymWave := initWave mem setLo g ldsB ldsD
    w.pc = 0 ∧ w.halted = false ∧ w.err = none ∧ w.exec = (Tm.lit 0xFFFFFFFF, Tm.lit 0xFFFFFFFF) ∧
    w.mem = mem ∧ w.vgpr.size = vgprCount * lanes ∧ w.sgpr.size = sgprCount ∧
    readSgpr w 2 = Tm.lit setLo ∧ (∀ l < lanes, readVgpr w 0 l = Tm.lit (UInt32.ofNat l)) := by
  let s0 : SymWave := GWave.init mem ldsB ldsD
  let s1 : SymWave := writeSgpr s0 2 (Dom.lit setLo)
  let s2 : SymWave := writeSgpr s1 3 (Dom.lit (UInt32.ofNat g))
  have hs0_vsize : s0.vgpr.size = vgprCount * lanes := Array.size_replicate
  have hs0_ssize : s0.sgpr.size = sgprCount := Array.size_replicate
  have hs1c := writeSgpr_ctrl s0 2 (Dom.lit setLo)
  have hs2c := writeSgpr_ctrl s1 3 (Dom.lit (UInt32.ofNat g))
  have hFold := initWave_fold_ctrl s2 (List.range lanes)
  have hs2_vsize : s2.vgpr.size = vgprCount * lanes := by rw [hs2c.2.2.2.2.2.1, hs1c.2.2.2.2.2.1, hs0_vsize]
  have hs2_ssize : s2.sgpr.size = sgprCount := by rw [hs2c.2.2.2.2.2.2, hs1c.2.2.2.2.2.2, hs0_ssize]
  have hs2_s2 : readSgpr s2 2 = Tm.lit setLo := by
    rw [show s2 = writeSgpr s1 3 (Dom.lit (UInt32.ofNat g)) from rfl, readSgpr_writeSgpr_ne s1 3 2 _ (by decide)]
    exact readSgpr_writeSgpr_eq s0 2 (Dom.lit setLo) (by decide) (by rw [hs0_ssize]; decide)
  refine ⟨hFold.2.2.1.trans (hs2c.2.1.trans hs1c.2.1), hFold.2.2.2.2.1.trans (hs2c.2.2.2.1.trans hs1c.2.2.2.1),
    hFold.2.2.2.2.2.1.trans (hs2c.2.2.2.2.1.trans hs1c.2.2.2.2.1),
    (hFold.2.1.trans (hs2c.1.trans hs1c.1)).trans (show s0.exec = (Tm.lit 0xFFFFFFFF, Tm.lit 0xFFFFFFFF) from rfl),
    hFold.2.2.2.1.trans (hs2c.2.2.1.trans hs1c.2.2.1), hFold.2.2.2.2.2.2.trans hs2_vsize,
    by change (List.foldl (fun st lane => writeVgpr st 0 lane (Dom.lit (UInt32.ofNat lane))) s2 (List.range lanes)).sgpr.size = sgprCount; rw [hFold.1]; exact hs2_ssize,
    by unfold readSgpr; change (List.foldl (fun st lane => writeVgpr st 0 lane (Dom.lit (UInt32.ofNat lane))) s2 (List.range lanes)).sgpr.getD 2 (Dom.lit 0) = Tm.lit setLo; rw [hFold.1]; exact hs2_s2,
    fun l hl => (initWave_fold_readVgpr s2 (List.range lanes) List.nodup_range
      (fun x hx => by rw [List.mem_range] at hx; rw [hs2_vsize]; unfold vgprCount lanes at *; omega) l (List.mem_range.mpr hl)).trans rfl⟩

private theorem tm_bit_lit (x : UInt32) (k : Nat) :
    (Dom.bit (Tm.lit x) k : Tm) = Tm.lit ((x >>> k.toUInt32) &&& 1) := rfl

private theorem tm_conc_lit (x : UInt32) : (Dom.conc (Tm.lit x) : Option UInt32) = some x := rfl

private theorem tm_ite_lit_one (a b : Tm) :
    (Dom.ite (Tm.lit 1) a b : Tm) = a := rfl

private theorem tm_mapM_litVal (xs : List UInt32) :
    (xs.map Tm.lit).mapM Tm.litVal? = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, Tm.litVal?, Tm.lit, Tm.node, bind, Option.bind, ih, pure]

private theorem tm_pack_map_lit (xs : List UInt32) :
    (Dom.pack (xs.map Tm.lit) : Tm) = Tm.lit (packWord xs) := by
  change Tm.fold .pack (xs.map Tm.lit) = Tm.lit (packWord xs)
  unfold Tm.fold
  simp only [TOp.pure, ↓reduceIte, tm_mapM_litVal, TOp.sem]

private theorem u32_allones_bit (k : Nat) (hk : k < 32) :
    ((0xFFFFFFFF : UInt32) >>> k.toUInt32) &&& 1 = 1 :=
  (by decide : ∀ n < 32, ((0xFFFFFFFF : UInt32) >>> n.toUInt32) &&& 1 = 1) k hk

private theorem u32_one_bit_pos (k : Nat) (h1 : 1 ≤ k) (h2 : k < 32) :
    ((1 : UInt32) >>> k.toUInt32) &&& 1 = 0 :=
  (by decide : ∀ n < 32, 1 ≤ n → ((1 : UInt32) >>> n.toUInt32) &&& 1 = 0) k h2 h1

private theorem u32_zero_bit (k : Nat) (hk : k < 32) :
    ((0 : UInt32) >>> k.toUInt32) &&& 1 = 0 :=
  (by decide : ∀ n < 32, ((0 : UInt32) >>> n.toUInt32) &&& 1 = 0) k hk

private theorem u32_one_bit_eq_zero (k : Nat) (h : k < 32) :
    ((((1 : UInt32) >>> k.toUInt32) &&& 1) != 0) = (k == 0) :=
  (by decide : ∀ n < 32, ((((1 : UInt32) >>> n.toUInt32) &&& 1) != 0) = (n == 0)) k h

private theorem activeLanes_exec_one (s : SymWave) (hs : s.exec = (.lit 1, .lit 0)) :
    activeLanes? s = some [0] := by
  unfold activeLanes?
  have hM : ((List.range lanes).mapM fun l => (Dom.conc (execBit s l)).map fun v => (l, v != 0)) =
      some ((List.range lanes).map fun l => (l, l == 0)) := by
    apply list_mapM_eq_some
    intro l hl; rw [List.mem_range] at hl; unfold execBit maskBit; simp only [hs]
    split
    · rename_i hlt32
      rw [tm_bit_lit, tm_conc_lit, Option.map_some, u32_one_bit_eq_zero l hlt32]
    · rename_i hge32
      rw [tm_bit_lit, u32_zero_bit (l - 32) (by unfold lanes at hl; omega), tm_conc_lit, Option.map_some]
      have hne0 : (l == 0) = false := by cases l with | zero => omega | succ _ => rfl
      simp only [hne0]; rfl
  rw [hM]; rfl

private theorem tm_ugt_lit_one (lane : Nat) (hl : lane < 64) :
    (Dom.ugt (Tm.lit 1) (Tm.lit (UInt32.ofNat lane)) : Tm) =
      if lane == 0 then Tm.lit 1 else Tm.lit 0 := by
  change Tm.mkUgt (Tm.lit 1) (Tm.lit (UInt32.ofNat lane)) = _
  unfold Tm.mkUgt
  by_cases hEq : (Tm.lit 1 == Tm.lit (UInt32.ofNat lane)) = true
  · simp only [hEq, ↓reduceIte]
    have hEq' : Tm.lit 1 = Tm.lit (UInt32.ofNat lane) := beq_iff_eq.mp hEq
    have hVal : (1 : UInt32) = UInt32.ofNat lane := Option.some.inj (congrArg Tm.litVal? hEq')
    have hNe0 : (lane == 0) = false := by
      cases lane with
      | zero => exact absurd hVal (by decide)
      | succ _ => rfl
    simp [hNe0]
  · simp only [hEq, Bool.false_eq_true, ↓reduceIte]
    unfold Tm.mkUgt'
    have hNot0 : Tm.isLit (Tm.lit 1) 0 = false := rfl
    have hNotF1 : Tm.isLit (Tm.lit 1) 0xFFFFFFFF = false := rfl
    have hNotF2 : Tm.isLit (Tm.lit (UInt32.ofNat lane)) 0xFFFFFFFF = false := by
      change (UInt32.ofNat lane == 0xFFFFFFFF) = false
      have h : ∀ l < 64, (UInt32.ofNat l == 0xFFFFFFFF) = false := by decide
      exact h lane hl
    simp only [hNot0, hNotF1, hNotF2, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    cases lane with
    | zero => rfl
    | succ k =>
      have hk : k < 63 := by omega
      have hNot0v : Tm.isLit (Tm.lit (UInt32.ofNat (k + 1))) 0 = false := by
        change (UInt32.ofNat (k + 1) == 0) = false
        have h : ∀ j < 63, (UInt32.ofNat (j + 1) == 0) = false := by decide
        exact h k hk
      have hGt : b2w ((1 : UInt32) > UInt32.ofNat (k + 1)) = 0 := by
        have h : ∀ j < 63, b2w ((1 : UInt32) > UInt32.ofNat (j + 1)) = 0 := by decide
        exact h k hk
      simp only [hNot0v, Bool.false_eq_true, ↓reduceIte]
      change Tm.fold .ugt [Tm.lit 1, Tm.lit (UInt32.ofNat (k + 1))] = Tm.lit 0
      unfold Tm.fold
      simp only [TOp.pure, ↓reduceIte, List.mapM_cons, List.mapM_nil, Tm.litVal?, Tm.lit, Tm.node,
        bind, Option.bind, pure, TOp.sem, List.getD_cons_zero, List.getD_cons_succ, hGt]

private theorem str_startsWith_eq (s p : String) :
    s.startsWith p = decide (p.toList <+: s.toList) := by
  apply Bool.eq_iff_iff.mpr
  simp only [String.startsWith_string_iff, decide_eq_true_eq]

private theorem str_contains_eq (s t : String) :
    s.contains t = decide (t.toList <:+: s.toList) := by
  apply Bool.eq_iff_iff.mpr
  simp only [String.contains_string_iff, decide_eq_true_eq]

private theorem str_drop_cbv (s : String) (n : Nat) :
    (s.drop n).toString = String.ofList (s.toList.drop n) := by
  apply String.ext; simp

attribute [local cbv_eval] str_startsWith_eq str_contains_eq str_drop_cbv

private theorem sc7_flags :
    ((!modifiersClear sc7_i0) = false) ∧ ((!modifiersClear sc7_i1) = false) ∧
    ((!modifiersClear sc7_i2) = false) ∧ ((!modifiersClear sc7_i4) = false) ∧
    ((!modifiersClear sc7_i5) = false) ∧ ((!modifiersClear sc7_i6) = false) ∧
    ((!modifiersClear sc7_i7) = false) ∧ ((!modifiersClear sc7_i9) = false) ∧
    ((!modifiersClear sc7_i10) = false) ∧ (isSdwa sc7_i0 = false) ∧
    ("ENC_VOP1".contains "SDWA" = false) ∧ (sc7_i0.name.startsWith "V_CMPX" = true) ∧
    (sc7_i2.name.startsWith "S_BUFFER_LOAD" = false) ∧
    (srcCode sc7_i0 0 = 129) ∧ (srcCode sc7_i0 1 = 256) := by
  have h :
      (!modifiersClear sc7_i0, !modifiersClear sc7_i1, !modifiersClear sc7_i2,
       !modifiersClear sc7_i4, !modifiersClear sc7_i5, !modifiersClear sc7_i6,
       !modifiersClear sc7_i7, !modifiersClear sc7_i9, !modifiersClear sc7_i10,
       isSdwa sc7_i0, "ENC_VOP1".contains "SDWA", sc7_i0.name.startsWith "V_CMPX",
       sc7_i2.name.startsWith "S_BUFFER_LOAD", srcCode sc7_i0 0, srcCode sc7_i0 1) =
      (false, false, false, false, false, false, false, false, false,
       false, false, true, false, 129, 256) := by
    set_option cbv.maxSteps 500000 in cbv
  simp only [Prod.mk.injEq] at h
  exact h

private theorem sc7_addrs :
    ((((join64 descSetLo 0xFFFF8000 + UInt64.ofNat (signed21 0).toNat + UInt64.ofNat 0 + UInt64.ofNat (4 * 0)) &&& 0xFFFFFFFFFFFFFFFC) >>> 2) = descSetAddr >>> 2) ∧
    ((((join64 descSetLo 0xFFFF8000 + UInt64.ofNat (signed21 0).toNat + UInt64.ofNat 0 + UInt64.ofNat (4 * 1)) &&& 0xFFFFFFFFFFFFFFFC) >>> 2) = (descSetAddr >>> 2) + 1) ∧
    ((((join64 descSetLo 0xFFFF8000 + UInt64.ofNat (signed21 0).toNat + UInt64.ofNat 0 + UInt64.ofNat (4 * 2)) &&& 0xFFFFFFFFFFFFFFFC) >>> 2) = (descSetAddr >>> 2) + 2) ∧
    ((((join64 descSetLo 0xFFFF8000 + UInt64.ofNat (signed21 0).toNat + UInt64.ofNat 0 + UInt64.ofNat (4 * 3)) &&& 0xFFFFFFFFFFFFFFFC) >>> 2) = (descSetAddr >>> 2) + 3) ∧
    (mubufAddrs sc7_i7 (resourceOfWords 0 1 8 0x31000000) 0 (0 : UInt32).toNat 2 = [some (dwLo 0), some (dwLo 0 + 1)]) ∧
    (packWord (List.take 32 (List.map (fun lane => if (lane == 0) = true then (1 : UInt32) else 0) (List.range lanes))) = 1) ∧
    (packWord (List.drop 32 (List.map (fun lane => if (lane == 0) = true then (1 : UInt32) else 0) (List.range lanes))) = 0) ∧
    (((resourceOfWords 0 1 8 0x31000000).swizzle || (resourceOfWords 0 1 8 0x31000000).addTid || (0 == 1) || (0 == 1) || (0 == 1)) = false) := by
  have h :
      ((((join64 descSetLo 0xFFFF8000 + UInt64.ofNat (signed21 0).toNat + UInt64.ofNat 0 + UInt64.ofNat (4 * 0)) &&& 0xFFFFFFFFFFFFFFFC) >>> 2),
       (((join64 descSetLo 0xFFFF8000 + UInt64.ofNat (signed21 0).toNat + UInt64.ofNat 0 + UInt64.ofNat (4 * 1)) &&& 0xFFFFFFFFFFFFFFFC) >>> 2),
       (((join64 descSetLo 0xFFFF8000 + UInt64.ofNat (signed21 0).toNat + UInt64.ofNat 0 + UInt64.ofNat (4 * 2)) &&& 0xFFFFFFFFFFFFFFFC) >>> 2),
       (((join64 descSetLo 0xFFFF8000 + UInt64.ofNat (signed21 0).toNat + UInt64.ofNat 0 + UInt64.ofNat (4 * 3)) &&& 0xFFFFFFFFFFFFFFFC) >>> 2),
       mubufAddrs sc7_i7 (resourceOfWords 0 1 8 0x31000000) 0 (0 : UInt32).toNat 2,
       packWord (List.take 32 (List.map (fun lane => if (lane == 0) = true then (1 : UInt32) else 0) (List.range lanes))),
       packWord (List.drop 32 (List.map (fun lane => if (lane == 0) = true then (1 : UInt32) else 0) (List.range lanes))),
       ((resourceOfWords 0 1 8 0x31000000).swizzle || (resourceOfWords 0 1 8 0x31000000).addTid || (0 == 1) || (0 == 1) || (0 == 1))) =
      (descSetAddr >>> 2, (descSetAddr >>> 2) + 1, (descSetAddr >>> 2) + 2, (descSetAddr >>> 2) + 3,
       [some (dwLo 0), some (dwLo 0 + 1)], 1, 0, false) := by
    set_option cbv.maxSteps 500000 in cbv
  simp only [Prod.mk.injEq] at h
  exact h

private theorem step_at (prog : Program) (s : SymWave) (i : Inst)
    (hH : s.halted = false) (hE : s.err = none) (hI : prog[s.pc]? = some (some i)) :
    step prog s = execInst i { s with pc := s.pc + i.words.length } := by
  unfold step
  simp only [hH, hE, Option.isSome_none, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hI]

private theorem joinTarget_none_of (prog : Program) (s : SymWave) (i : Inst)
    (hI : prog[s.pc]? = some (some i)) (hNe : (instOp i.name == .s_cbranch_execz) = false) :
    joinTarget prog s = none := by
  unfold joinTarget
  simp only [hI, hNe, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

private theorem valuLanes_vmov_lit (s : SymWave) (dst srcCodeVal : Nat) (val : UInt32) (wrd : UInt32)
    (hDstLt : dst < vgprCount) (hVsz : s.vgpr.size = vgprCount * lanes)
    (hExec : s.exec = (.lit 1, .lit 0)) (hSk : srcKind srcCodeVal = .lit val)
    (hNotV : (256 ≤ srcCodeVal && srcCodeVal ≤ 511) = false) :
    ∃ w' : SymWave,
      valuLanes (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
        [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]) s 1 (fun src _ => src0 src) = w' ∧
      w'.sgpr = s.sgpr ∧ w'.exec = s.exec ∧ w'.pc = s.pc ∧ w'.mem = s.mem ∧
      w'.halted = s.halted ∧ w'.err = s.err ∧ w'.vgpr.size = vgprCount * lanes ∧
      readVgpr w' dst 0 = Tm.lit val ∧
      (∀ r', r' ≠ dst → readVgpr w' r' 0 = readVgpr s r' 0) := by
  have hSdwaV := sc7_flags.2.2.2.2.2.2.2.2.2.2.1
  let rest := (List.range 63).map fun k => (k + 1, readVgpr s dst (k + 1))
  let w' := writeLanes s dst ((0, Tm.lit val) :: rest)
  have hValu : valuLanes (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
      [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]) s 1 (fun src _ => src0 src) = w' := by
    unfold valuLanes
    have hSdwa : isSdwa (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
        [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]) = false := hSdwaV
    have hRange : List.range lanes = 0 :: (List.range 63).map (· + 1) := by decide
    have hMapM : ((List.range lanes).mapM fun lane =>
        laneStep s lane
          (laneSources (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
            [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]) s 1 lane)
          (readVgpr s dst lane) (fun src => src0 src) Dom.ite) =
        some ((0, Tm.lit val) :: rest) := by
      rw [hRange, List.mapM_cons]
      have h0 : laneStep s 0
          (laneSources (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
            [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]) s 1 0)
          (readVgpr s dst 0) (fun src => src0 src) Dom.ite = some (0, Tm.lit val) := by
        have hOff0 : laneOff s 0 = false := by
          unfold laneOff execBit maskBit; rw [hExec]
          simp only [show (0 : Nat) < 32 from by decide, ↓reduceIte, tm_bit_lit]
          change (some (((1 : UInt32) >>> (0 : Nat).toUInt32) &&& 1) == some 0) = false; decide
        have hBit0 : execBit s 0 = Tm.lit 1 := by
          unfold execBit maskBit; rw [hExec]
          simp only [show (0 : Nat) < 32 from by decide, ↓reduceIte, tm_bit_lit]
          exact congrArg Tm.lit (by decide)
        have hSrc0 : laneSources (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
            [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]) s 1 0 = some [Tm.lit val] := by
          have hSC0' : srcCode (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
              [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]) 0 = srcCodeVal := by
            unfold srcCode; rw [hSdwa]; rfl
          simp only [laneSources, List.range, List.range.loop, List.mapM_cons, List.mapM_nil,
            hSC0', vectorSource, hNotV, Bool.false_eq_true, ↓reduceIte, scalarSource, hSk,
            bind, Option.bind, pure]; rfl
        unfold laneStep; rw [hOff0, hSrc0, hBit0]
        simp only [Bool.false_eq_true, ↓reduceIte, Option.map_some, src0, List.getD_cons_zero, tm_ite_lit_one]
      have hRest : ((List.range 63).map (· + 1)).mapM (fun lane =>
          laneStep s lane
            (laneSources (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
              [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]) s 1 lane)
            (readVgpr s dst lane) (fun src => src0 src) Dom.ite) =
          some rest := by
        have hM := list_mapM_eq_some
          (fun lane => laneStep s lane
            (laneSources (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
              [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]) s 1 lane)
            (readVgpr s dst lane) (fun src => src0 src) Dom.ite)
          (fun lane => (lane, readVgpr s dst lane))
          ((List.range 63).map (· + 1)) (by
            intro lane hlane; rw [List.mem_map] at hlane; obtain ⟨k, hk, rfl⟩ := hlane; rw [List.mem_range] at hk
            have hOffK : laneOff s (k + 1) = true := by
              unfold laneOff execBit maskBit; simp only [hExec]
              split
              · rename_i hlt32
                rw [tm_bit_lit, u32_one_bit_pos (k + 1) (by omega) hlt32]; rfl
              · rw [tm_bit_lit, u32_zero_bit (k + 1 - 32) (by omega)]; rfl
            simp [laneStep, hOffK])
        rw [hM]; simp [rest, List.map_map, Function.comp]
      rw [h0, hRest]; rfl
    simp only [hSdwa, Bool.false_eq_true, ↓reduceIte, Bool.false_and, GWave.withSome]
    have hDst : (mkCompactInst "V_MOV_B32" false false "ENC_VOP1" []
        [("ENCODING", 63), ("OP", 1), ("SRC0", srcCodeVal), ("VDST", dst)] [wrd]).field "VDST" = dst := rfl
    rw [hDst, hMapM]
  have hc := writeLanes_ctrl s dst ((0, Tm.lit val) :: rest)
  refine ⟨w', hValu, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.trans hVsz, ?_, ?_⟩
  · show readVgpr (writeLanes s dst ((0, Tm.lit val) :: rest)) dst 0 = Tm.lit val
    rw [writeLanes_cons, readVgpr_writeLanes_of_ne]
    · exact readVgpr_writeVgpr_eq s dst 0 (Tm.lit val) hDstLt
        (by rw [hVsz]; unfold vgprCount lanes at *; omega)
    · intro p hp; rw [List.mem_map] at hp; obtain ⟨k, hk, rfl⟩ := hp; rw [List.mem_range] at hk; unfold lanes; omega
  · intro r' hne
    exact readVgpr_writeLanes_of_ne s dst r' 0 ((0, Tm.lit val) :: rest) (by
      intro p hp; rcases List.mem_cons.mp hp with rfl | hmem
      · unfold lanes; omega
      · rw [List.mem_map] at hmem; obtain ⟨k, hk, rfl⟩ := hmem; rw [List.mem_range] at hk; unfold lanes; omega)

set_option maxRecDepth 200000 in
private theorem symWave_sc7_steps0to3 (f : Nat) (bv : UInt64 → Option Tm) (w0 : SymWave)
    (hB0 : bv (descSetAddr >>> 2) = some (.lit 0))
    (hB1 : bv ((descSetAddr >>> 2) + 1) = some (.lit 1))
    (hB2 : bv ((descSetAddr >>> 2) + 2) = some (.lit 8))
    (hB3 : bv ((descSetAddr >>> 2) + 3) = some (.lit 0x31000000))
    (hw0_pc : w0.pc = 0) (hw0_halted : w0.halted = false) (hw0_err : w0.err = none)
    (hw0_exec : w0.exec = (Tm.lit 0xFFFFFFFF, Tm.lit 0xFFFFFFFF))
    (hw0_mem : w0.mem = ⟨{}, bv⟩)
    (hw0_vsize : w0.vgpr.size = vgprCount * lanes)
    (hw0_ssize : w0.sgpr.size = sgprCount)
    (hw0_s2 : readSgpr w0 2 = Tm.lit descSetLo)
    (hw0_v0 : ∀ l < lanes, readVgpr w0 0 l = Tm.lit (UInt32.ofNat l)) :
    ∃ w4 : SymWave,
      srun sc7Compact (f + 10) w0 = srun sc7Compact (f + 6) w4 ∧
      w4.pc = 5 ∧ w4.halted = false ∧ w4.err = none ∧
      w4.exec = (.lit 1, .lit 0) ∧ w4.mem = ⟨{}, bv⟩ ∧
      w4.vgpr.size = vgprCount * lanes ∧
      readVgpr w4 0 0 = Tm.lit 0 ∧
      readSgpr w4 0 = Tm.lit 0 ∧ readSgpr w4 1 = Tm.lit 1 ∧
      readSgpr w4 2 = Tm.lit 8 ∧ readSgpr w4 3 = Tm.lit 0x31000000 := by
  have hG0 : sc7Compact[0]? = some (some sc7_i0) := by simp [sc7Compact]
  have hG1 : sc7Compact[1]? = some (some sc7_i1) := by simp [sc7Compact]
  have hG2 : sc7Compact[2]? = some (some sc7_i2) := by simp [sc7Compact]
  have hG4 : sc7Compact[4]? = some (some sc7_i4) := by simp [sc7Compact]
  have ⟨hMod0, hMod1, hMod2, hMod4, _, _, _, _, _, hSdwa0, _, hCmpx, hNotBuf, hSC0, hSC1⟩ := sc7_flags
  have ⟨hAddr0, hAddr1, hAddr2, hAddr3, _, hp1, hp0, _⟩ := sc7_addrs
  let w1 : SymWave := { w0 with pc := 1, exec := (.lit 1, .lit 0) }
  have hStep0 : step sc7Compact w0 = w1 := by
    rw [step_at sc7Compact w0 sc7_i0 hw0_halted hw0_err (by rw [hw0_pc]; exact hG0), hw0_pc]
    change execInst sc7_i0 { w0 with pc := 1 } = w1
    unfold execInst
    have hOp : instOp sc7_i0.name = .v_cmpx_gt_u32 := rfl
    simp only [hMod0, Bool.false_eq_true, ↓reduceIte, hOp]
    unfold valuCompare
    have hMapM : ((List.range lanes).mapM fun lane =>
        laneStep { w0 with pc := 1 } lane (laneSources sc7_i0 { w0 with pc := 1 } 2 lane)
          (Dom.lit 0) (fun src => Dom.ugt (src0 src) (src1 src)) Dom.ite) =
        some ((List.range lanes).map fun lane => (lane, if lane == 0 then Tm.lit 1 else Tm.lit 0)) := by
      apply list_mapM_eq_some
      intro lane hlane
      rw [List.mem_range] at hlane
      have hOff : laneOff { w0 with pc := 1 } lane = false := by
        unfold laneOff execBit maskBit; simp only [hw0_exec]
        split
        · rename_i hlt32; rw [tm_bit_lit, u32_allones_bit lane hlt32]; rfl
        · rename_i hge32; rw [tm_bit_lit, u32_allones_bit (lane - 32) (by unfold lanes at hlane; omega)]; rfl
      have hBit : execBit { w0 with pc := 1 } lane = Tm.lit 1 := by
        unfold execBit maskBit; simp only [hw0_exec]
        split
        · rename_i hlt32; rw [tm_bit_lit, u32_allones_bit lane hlt32]
        · rename_i hge32; rw [tm_bit_lit, u32_allones_bit (lane - 32) (by unfold lanes at hlane; omega)]
      have hSrc : laneSources sc7_i0 { w0 with pc := 1 } 2 lane =
          some [Tm.lit 1, Tm.lit (UInt32.ofNat lane)] := by
        have hRead : readVgpr { w0 with pc := 1 } 0 lane = Tm.lit (UInt32.ofNat lane) := hw0_v0 lane hlane
        simp only [laneSources, List.range, List.range.loop, List.mapM_cons, List.mapM_nil,
          hSC0, hSC1, vectorSource, scalarSource, srcKind, hRead, bind, Option.bind, pure]
        rfl
      unfold laneStep
      rw [hOff, hSrc, hBit]
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_some, src0, src1,
        List.getD_cons_zero, List.getD_cons_succ, tm_ite_lit_one, tm_ugt_lit_one lane hlane]
    simp only [hSdwa0, Bool.false_eq_true, ↓reduceIte, hMapM, GWave.withSome]
    have hMask : maskOfBits (((List.range lanes).map fun lane => (lane, if lane == 0 then Tm.lit 1 else Tm.lit 0)).map (·.2)) =
        (Tm.lit 1, Tm.lit 0) := by
      unfold maskOfBits
      have hEq : (((List.range lanes).map fun lane => (lane, if lane == 0 then Tm.lit 1 else Tm.lit 0)).map (·.2)) =
          ((List.range lanes).map fun lane => if lane == 0 then (1 : UInt32) else 0).map Tm.lit := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left; intro l _; cases l <;> rfl
      rw [hEq, ← List.map_take, ← List.map_drop, tm_pack_map_lit, tm_pack_map_lit, hp1, hp0]
    rw [hMask, hCmpx]; rfl
  let w2 : SymWave := writeSgpr { w1 with pc := 2 } 3 (Tm.lit 0xFFFF8000)
  have hStep1 : step sc7Compact w1 = w2 := by
    rw [step_at sc7Compact w1 sc7_i1 hw0_halted hw0_err hG1]
    unfold execInst
    have hMovk : movkValue 32768 = 0xFFFF8000 := by decide
    have hOp1 : instOp sc7_i1.name = .s_movk_i32 := rfl
    have hFsdst : sc7_i1.field "SDST" = 3 := rfl
    have hFsimm : sc7_i1.field "SIMM16" = 32768 := rfl
    simp only [hMod1, Bool.false_eq_true, ↓reduceIte, hOp1, hFsdst, hFsimm, hMovk,
      writeScalarDst, dstKind]
    rfl
  have hw2_s2 : readSgpr w2 2 = Tm.lit descSetLo := by
    rw [show w2 = writeSgpr { w1 with pc := 2 } 3 (Tm.lit 0xFFFF8000) from rfl,
        readSgpr_writeSgpr_ne _ 3 2 _ (by decide)]
    exact hw0_s2
  have hw2_s3 : readSgpr w2 3 = Tm.lit 0xFFFF8000 :=
    readSgpr_writeSgpr_eq _ 3 _ (by decide) (by show 3 < w0.sgpr.size; rw [hw0_ssize]; decide)
  have hw2_ssize : w2.sgpr.size = sgprCount := (writeSgpr_size _ _ _).trans hw0_ssize
  have hw2_ctrl := writeSgpr_ctrl { w1 with pc := 2 } 3 (Tm.lit 0xFFFF8000)
  have hH2 : w2.halted = false := hw2_ctrl.2.2.2.1.trans hw0_halted
  have hE2 : w2.err = none := hw2_ctrl.2.2.2.2.1.trans hw0_err
  have hP2 : w2.pc = 2 := hw2_ctrl.2.1
  have hM2 : w2.mem = ⟨{}, bv⟩ := hw2_ctrl.2.2.1.trans hw0_mem
  let w3 : SymWave := writeSgprs { w2 with pc := 4 } [(0, .lit 0), (1, .lit 1), (2, .lit 8), (3, .lit 0x31000000)]
  have hStep2 : step sc7Compact w2 = w3 := by
    rw [step_at sc7Compact w2 sc7_i2 hH2 hE2 (by rw [hP2]; exact hG2), hP2]
    change execInst sc7_i2 { w2 with pc := 4 } = w3
    unfold execInst execSmem
    have hRS2 : readSgpr { w2 with pc := 4 } 2 = Tm.lit descSetLo := hw2_s2
    have hRS3 : readSgpr { w2 with pc := 4 } 3 = Tm.lit 0xFFFF8000 := hw2_s3
    have hL0 : MemDom.load ({ w2 with pc := 4 }.mem) (descSetAddr >>> 2) = some (Tm.lit 0) := by
      change SymMem.load w2.mem _ = _; rw [hM2]; simp [SymMem.load, hB0]
    have hL1 : MemDom.load ({ w2 with pc := 4 }.mem) ((descSetAddr >>> 2) + 1) = some (Tm.lit 1) := by
      change SymMem.load w2.mem _ = _; rw [hM2]; simp [SymMem.load, hB1]
    have hL2 : MemDom.load ({ w2 with pc := 4 }.mem) ((descSetAddr >>> 2) + 2) = some (Tm.lit 8) := by
      change SymMem.load w2.mem _ = _; rw [hM2]; simp [SymMem.load, hB2]
    have hL3 : MemDom.load ({ w2 with pc := 4 }.mem) ((descSetAddr >>> 2) + 3) = some (Tm.lit 0x31000000) := by
      change SymMem.load w2.mem _ = _; rw [hM2]; simp [SymMem.load, hB3]
    have hOp : instOp sc7_i2.name = .smem := rfl
    have hSdata : sc7_i2.ie.operands.find? (·.field == "SDATA") =
        some ⟨"SDATA", "OPR_SREG", "FMT_ANY", 128, false, true, false, true⟩ := rfl
    have hFsd : sc7_i2.field "SDATA" = 0 := rfl
    have hFsoff : sc7_i2.field "SOFFSET" = 125 := rfl
    have hFoff : sc7_i2.field "OFFSET" = 0 := rfl
    have hFsb : sc7_i2.field "SBASE" = 1 := rfl
    have hNeg : ¬(signed21 0 < 0) := by decide
    have hAlign : ((128 / 32 == 2 && 0 % 2 != 0) || (128 / 32 ≥ 4 && 0 % 4 != 0)) = false := by decide
    simp only [hMod2, hOp, hSdata, hFsd, hFsoff, hFoff, hFsb, hNotBuf, hAlign, hNeg,
      show (125 == 125) = true from rfl, show 2 * 1 = 2 from rfl, show 2 * 1 + 1 = 3 from rfl,
      show 128 / 32 = 4 from rfl, show List.range 4 = [0, 1, 2, 3] from rfl,
      Bool.false_eq_true, ↓reduceIte, GWave.withSome,
      hRS2, hRS3, tm_conc_lit, Option.map_some,
      List.mapM_cons, List.mapM_nil,
      hAddr0, hAddr1, hAddr2, hAddr3, hL0, hL1, hL2, hL3, bind, Option.bind, pure]
    rfl
  have hw3_s0 : readSgpr w3 0 = Tm.lit 0 := by
    simp only [w3, writeSgprs, List.foldl_cons, List.foldl_nil]
    rw [readSgpr_writeSgpr_ne _ 3 0 _ (by decide), readSgpr_writeSgpr_ne _ 2 0 _ (by decide),
        readSgpr_writeSgpr_ne _ 1 0 _ (by decide)]
    exact readSgpr_writeSgpr_eq _ 0 _ (by decide) (by rw [hw2_ssize]; decide)
  have hw3_s1 : readSgpr w3 1 = Tm.lit 1 := by
    simp only [w3, writeSgprs, List.foldl_cons, List.foldl_nil]
    rw [readSgpr_writeSgpr_ne _ 3 1 _ (by decide), readSgpr_writeSgpr_ne _ 2 1 _ (by decide)]
    exact readSgpr_writeSgpr_eq _ 1 _ (by decide) (by rw [writeSgpr_size, hw2_ssize]; decide)
  have hw3_s2 : readSgpr w3 2 = Tm.lit 8 := by
    simp only [w3, writeSgprs, List.foldl_cons, List.foldl_nil]
    rw [readSgpr_writeSgpr_ne _ 3 2 _ (by decide)]
    exact readSgpr_writeSgpr_eq _ 2 _ (by decide) (by rw [writeSgpr_size, writeSgpr_size, hw2_ssize]; decide)
  have hw3_s3 : readSgpr w3 3 = Tm.lit 0x31000000 := by
    simp only [w3, writeSgprs, List.foldl_cons, List.foldl_nil]
    exact readSgpr_writeSgpr_eq _ 3 _ (by decide)
      (by rw [writeSgpr_size, writeSgpr_size, writeSgpr_size, hw2_ssize]; decide)
  have hw3_ctrl : w3.pc = 4 ∧ w3.halted = false ∧ w3.err = none ∧
      w3.exec = (.lit 1, .lit 0) ∧ w3.mem = ⟨{}, bv⟩ ∧ w3.vgpr = w0.vgpr := by
    have c0 := writeSgpr_ctrl { w2 with pc := 4 } 0 (.lit 0)
    have c1 := writeSgpr_ctrl (writeSgpr { w2 with pc := 4 } 0 (.lit 0)) 1 (.lit 1)
    have c2 := writeSgpr_ctrl (writeSgpr (writeSgpr { w2 with pc := 4 } 0 (.lit 0)) 1 (.lit 1)) 2 (.lit 8)
    have c3 := writeSgpr_ctrl (writeSgpr (writeSgpr (writeSgpr { w2 with pc := 4 } 0 (.lit 0)) 1 (.lit 1)) 2 (.lit 8)) 3 (.lit 0x31000000)
    exact ⟨c3.2.1.trans (c2.2.1.trans (c1.2.1.trans c0.2.1)),
      c3.2.2.2.1.trans (c2.2.2.2.1.trans (c1.2.2.2.1.trans (c0.2.2.2.1.trans hH2))),
      c3.2.2.2.2.1.trans (c2.2.2.2.2.1.trans (c1.2.2.2.2.1.trans (c0.2.2.2.2.1.trans hE2))),
      c3.1.trans (c2.1.trans (c1.1.trans (c0.1.trans hw2_ctrl.1))),
      c3.2.2.1.trans (c2.2.2.1.trans (c1.2.2.1.trans (c0.2.2.1.trans hM2))),
      c3.2.2.2.2.2.1.trans (c2.2.2.2.2.2.1.trans (c1.2.2.2.2.2.1.trans (c0.2.2.2.2.2.1.trans hw2_ctrl.2.2.2.2.2.1)))⟩
  let w4 : SymWave := { w3 with pc := 5 }
  have hStep3 : step sc7Compact w3 = w4 := by
    rw [step_at sc7Compact w3 sc7_i4 hw3_ctrl.2.1 hw3_ctrl.2.2.1 (by rw [hw3_ctrl.1]; exact hG4), hw3_ctrl.1]
    unfold execInst
    have hOp4 : instOp sc7_i4.name = .s_waitcnt := rfl
    simp only [hMod4, Bool.false_eq_true, ↓reduceIte, hOp4]; rfl
  have hRun03 : srun sc7Compact (f + 10) w0 = srun sc7Compact (f + 6) w4 := by
    rw [show f + 10 = (f + 9) + 1 from rfl,
        srun_step_eq sc7Compact (f + 9) w0 hw0_halted hw0_err (joinTarget_none_of sc7Compact w0 sc7_i0 (by rw [hw0_pc]; exact hG0) rfl), hStep0]
    rw [show f + 9 = (f + 8) + 1 from rfl,
        srun_step_eq sc7Compact (f + 8) w1 hw0_halted hw0_err (joinTarget_none_of sc7Compact w1 sc7_i1 hG1 rfl), hStep1]
    rw [show f + 8 = (f + 7) + 1 from rfl,
        srun_step_eq sc7Compact (f + 7) w2 hH2 hE2 (joinTarget_none_of sc7Compact w2 sc7_i2 (by rw [hP2]; exact hG2) rfl), hStep2]
    rw [show f + 7 = (f + 6) + 1 from rfl,
        srun_step_eq sc7Compact (f + 6) w3 hw3_ctrl.2.1 hw3_ctrl.2.2.1 (joinTarget_none_of sc7Compact w3 sc7_i4 (by rw [hw3_ctrl.1]; exact hG4) rfl), hStep3]
  refine ⟨w4, hRun03, rfl, hw3_ctrl.2.1, hw3_ctrl.2.2.1, hw3_ctrl.2.2.2.1, hw3_ctrl.2.2.2.2.1,
    by change w3.vgpr.size = _; rw [hw3_ctrl.2.2.2.2.2]; exact hw0_vsize,
    by unfold readVgpr; change w3.vgpr.getD 0 (Dom.lit 0) = Tm.lit 0; rw [hw3_ctrl.2.2.2.2.2]; exact hw0_v0 0 (by decide),
    hw3_s0, hw3_s1, hw3_s2, hw3_s3⟩

set_option maxRecDepth 200000 in
private theorem symWave_storeConst7_base (consts : List Word) (ex : UInt64 → Bool)
    (hLay0 : (layoutMem 1 consts [])[descSetAddr >>> 2]? = some 0)
    (hLay1 : (layoutMem 1 consts [])[(descSetAddr >>> 2) + 1]? = some 1)
    (hLay2 : (layoutMem 1 consts [])[(descSetAddr >>> 2) + 2]? = some 8)
    (hLay3 : (layoutMem 1 consts [])[(descSetAddr >>> 2) + 3]? = some 0x31000000)
    (hEx0 : ex (descSetAddr >>> 2) = false) (hEx1 : ex ((descSetAddr >>> 2) + 1) = false)
    (hEx2 : ex ((descSetAddr >>> 2) + 2) = false) (hEx3 : ex ((descSetAddr >>> 2) + 3) = false) :
    let st := symWave 1 (layoutMem 1 consts []) storeConst7Prog 0 {} ex 0
    st.err = none ∧ st.halted = true ∧
    st.mem.stores = (({} : Std.HashMap UInt64 Tm).insert (dwLo 0) (.lit 7) |>.insert (dwLo 0 + 1) (.lit 0)) := by
  rw [← symWave_map_stripInst, storeConst7Prog_strip]
  dsimp only [symWave]
  obtain ⟨f, hf⟩ : ∃ f, fuelOf sc7Compact = f + 10 := ⟨16 * sc7Compact.size + 2 ^ 28 - 10, by unfold fuelOf; omega⟩
  rw [hf]
  let bv := baseView 1 (layoutMem 1 consts []) {} ex
  have mkB : ∀ (a : UInt64) (v : UInt32), ex a = false → inW 1 a = false → inLds a = false →
      (layoutMem 1 consts [])[a]? = some v → bv a = some (.lit v) := by
    intro a v hex hin hlds hlay; unfold bv baseView viewStart
    simp only [hex, hin, hlds, Bool.false_eq_true, ↓reduceIte]
    change Option.map Tm.lit (layoutMem 1 consts [])[a]? = some (.lit v); rw [hlay]; rfl
  have hB0 := mkB _ 0 hEx0 (by decide) (by decide) hLay0
  have hB1 := mkB _ 1 hEx1 (by decide) (by decide) hLay1
  have hB2 := mkB _ 8 hEx2 (by decide) (by decide) hLay2
  have hB3 := mkB _ 0x31000000 hEx3 (by decide) (by decide) hLay3
  have ⟨hw0_pc, hw0_halted, hw0_err, hw0_exec, hw0_mem, hw0_vsize, hw0_ssize, hw0_s2, hw0_v0⟩ :=
    initWave_props (⟨{}, bv⟩ : SymMem) descSetLo 0 (ldsBaseOf 0) 0
  obtain ⟨w4, hRun03, hw4_pc, hw4_h, hw4_e, hw4_ex, hw4_m, hw4_vsz, hw4_v0, hw4_s0, hw4_s1, hw4_s2, hw4_s3⟩ :=
    symWave_sc7_steps0to3 f bv (initWave (⟨{}, bv⟩ : SymMem) descSetLo 0 (ldsBaseOf 0) 0)
      hB0 hB1 hB2 hB3 hw0_pc hw0_halted hw0_err hw0_exec hw0_mem hw0_vsize hw0_ssize hw0_s2 hw0_v0
  rw [hRun03]
  have hG5 : sc7Compact[5]? = some (some sc7_i5) := by simp [sc7Compact]
  have hG6 : sc7Compact[6]? = some (some sc7_i6) := by simp [sc7Compact]
  have hG7 : sc7Compact[7]? = some (some sc7_i7) := by simp [sc7Compact]
  have hG9 : sc7Compact[9]? = some (some sc7_i9) := by simp [sc7Compact]
  have hG10 : sc7Compact[10]? = some (some sc7_i10) := by simp [sc7Compact]
  have ⟨_, _, _, _, hMod5, hMod6, hMod7, hMod9, hMod10, _, _, _, _, _, _⟩ := sc7_flags
  have ⟨_, _, _, _, hMA, _, _, hRflags⟩ := sc7_addrs
  obtain ⟨w5, h5⟩ := valuLanes_vmov_lit { w4 with pc := 6 } 4 135 7 2114454151 (by decide) hw4_vsz hw4_ex rfl rfl
  have hStep4 : step sc7Compact w4 = w5 := by
    rw [step_at sc7Compact w4 sc7_i5 hw4_h hw4_e (by rw [hw4_pc]; exact hG5), hw4_pc]
    change execInst sc7_i5 { w4 with pc := 6 } = w5
    unfold execInst; have hOp5 : instOp sc7_i5.name = .v_mov_b32 := rfl
    simp only [hMod5, Bool.false_eq_true, ↓reduceIte, hOp5]; exact h5.1
  have hw5_v0 : readVgpr w5 0 0 = Tm.lit 0 := (h5.2.2.2.2.2.2.2.2.2 0 (by decide)).trans hw4_v0
  have hw5_exec' : ({ w5 with pc := 7 } : SymWave).exec = (.lit 1, .lit 0) := h5.2.2.1.trans hw4_ex
  obtain ⟨w6, h6⟩ := valuLanes_vmov_lit { w5 with pc := 7 } 5 128 0 2114585216 (by decide) h5.2.2.2.2.2.2.2.1 hw5_exec' rfl rfl
  have hStep5 : step sc7Compact w5 = w6 := by
    rw [step_at sc7Compact w5 sc7_i6 (h5.2.2.2.2.2.1.trans hw4_h) (h5.2.2.2.2.2.2.1.trans hw4_e) (by rw [h5.2.2.2.1]; exact hG6), h5.2.2.2.1]
    change execInst sc7_i6 { w5 with pc := 7 } = w6
    unfold execInst; have hOp6 : instOp sc7_i6.name = .v_mov_b32 := rfl
    simp only [hMod6, Bool.false_eq_true, ↓reduceIte, hOp6]; exact h6.1
  have hw6_v0 : readVgpr w6 0 0 = Tm.lit 0 := (h6.2.2.2.2.2.2.2.2.2 0 (by decide)).trans hw5_v0
  have hw6_v4 : readVgpr w6 4 0 = Tm.lit 7 := (h6.2.2.2.2.2.2.2.2.2 4 (by decide)).trans h5.2.2.2.2.2.2.2.2.1
  have hw6_v5 : readVgpr w6 5 0 = Tm.lit 0 := h6.2.2.2.2.2.2.2.2.1
  have hw5_pc : w5.pc = 6 := h5.2.2.2.1
  have hw6_pc : w6.pc = 7 := h6.2.2.2.1
  have hw5_h : w5.halted = false := h5.2.2.2.2.2.1.trans hw4_h
  have hw5_e : w5.err = none := h5.2.2.2.2.2.2.1.trans hw4_e
  have hw6_h : w6.halted = false := h6.2.2.2.2.2.1.trans hw5_h
  have hw6_e : w6.err = none := h6.2.2.2.2.2.2.1.trans hw5_e
  have hw6_ex : w6.exec = (.lit 1, .lit 0) := h6.2.2.1.trans hw5_exec'
  have hw6_sg : w6.sgpr = w4.sgpr := h6.2.1.trans h5.2.1
  have hw6_m : w6.mem = ⟨{}, bv⟩ := h6.2.2.2.2.1.trans (h5.2.2.2.2.1.trans hw4_m)
  let stFinal : Std.HashMap UInt64 Tm :=
    (({} : Std.HashMap UInt64 Tm).insert (dwLo 0) (.lit 7)).insert (dwLo 0 + 1) (.lit 0)
  let w7 : SymWave := { w6 with pc := 9, mem := { w6.mem with stores := stFinal } }
  have hStep6 : step sc7Compact w6 = w7 := by
    rw [step_at sc7Compact w6 sc7_i7 hw6_h hw6_e (by rw [hw6_pc]; exact hG7), hw6_pc]
    change execInst sc7_i7 { w6 with pc := 9 } = w7
    unfold execInst execMubuf
    have hRes : readResource { w6 with pc := 9 } 0 = some (resourceOfWords 0 1 8 0x31000000) := by
      unfold readResource readSgpr
      simp only [hw6_sg]
      rw [show w4.sgpr.getD 0 (Dom.lit 0) = Tm.lit 0 from hw4_s0,
          show w4.sgpr.getD 1 (Dom.lit 0) = Tm.lit 1 from hw4_s1,
          show w4.sgpr.getD 2 (Dom.lit 0) = Tm.lit 8 from hw4_s2,
          show w4.sgpr.getD 3 (Dom.lit 0) = Tm.lit 0x31000000 from hw4_s3]
      rfl
    have hAct : activeLanes? { w6 with pc := 9 } = some [0] := activeLanes_exec_one _ hw6_ex
    have hAddrs : mubufLaneAddrs sc7_i7 { w6 with pc := 9 } [0] (resourceOfWords 0 1 8 0x31000000) 0 2 =
        some [(0, [some (dwLo 0), some (dwLo 0 + 1)])] := by
      unfold mubufLaneAddrs
      have hv0 : readVgpr { w6 with pc := 9 } 0 0 = Tm.lit 0 := hw6_v0
      have hFoffen : sc7_i7.field "OFFEN" = 1 := rfl
      have hFvaddr : sc7_i7.field "VADDR" = 0 := rfl
      simp only [hFoffen, hFvaddr, List.mapM_cons, List.mapM_nil, hv0,
        tm_conc_lit, Option.map_some, bind, Option.bind, pure, hMA]
      rfl
    have hv4 : readVgpr { w6 with pc := 9 } 4 0 = Tm.lit 7 := hw6_v4
    have hv5 : readVgpr { w6 with pc := 9 } 5 0 = Tm.lit 0 := hw6_v5
    have hOp7 : instOp sc7_i7.name = .mubuf_store := rfl
    have hVdata : sc7_i7.ie.operands.find? (·.field == "VDATA") =
        some ⟨"VDATA", "OPR_VGPR", "FMT_ANY", 64, true, false, false, true⟩ := rfl
    have hFsrsrc : sc7_i7.field "SRSRC" = 0 := rfl
    have hFidxen : sc7_i7.field "IDXEN" = 0 := rfl
    have hFlds : sc7_i7.field "LDS" = 0 := rfl
    have hFtfe : sc7_i7.field "TFE" = 0 := rfl
    have hFsoff : sc7_i7.field "SOFFSET" = 128 := rfl
    have hFvdata : sc7_i7.field "VDATA" = 4 := rfl
    have hZip : ([some (dwLo 0), some (dwLo 0 + 1)] : List (Option UInt64)).zipIdx =
        [(some (dwLo 0), 0), (some (dwLo 0 + 1), 1)] := rfl
    have hStAll : storeAll { w6 with pc := 9 } [(dwLo 0, Tm.lit 7), (dwLo 0 + 1, Tm.lit 0)] = w7 := by
      simp only [storeAll, List.foldl_cons, List.foldl_nil, w7, stFinal, hw6_m]
      rfl
    simp only [hMod7, hOp7, hVdata, hFsrsrc, hFidxen, hFlds, hFtfe, hFsoff, hFvdata,
      show 64 / 32 = 2 from rfl, show 4 * 0 = 0 from rfl, show 4 + 0 = 4 from rfl, show 4 + 1 = 5 from rfl,
      GWave.withSome, hRes, hRflags, hAct, hAddrs, scalarSource, show srcKind 128 = .lit 0 from rfl,
      show (Dom.conc (Dom.lit 0 : Tm) : Option UInt32) = some 0 from rfl,
      Option.bind_some, ↓reduceIte, Bool.false_eq_true,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      hZip, List.filterMap_cons, List.filterMap_nil, Option.map_some,
      hv4, hv5, hStAll]
  let w8 : SymWave := { w7 with pc := 10 }
  have hStep7 : step sc7Compact w7 = w8 := by
    rw [step_at sc7Compact w7 sc7_i9 hw6_h hw6_e hG9]
    unfold execInst
    have hOp9 : instOp sc7_i9.name = .s_waitcnt_vscnt := rfl
    simp only [hMod9, Bool.false_eq_true, ↓reduceIte, hOp9]; rfl
  let w9 : SymWave := { w8 with pc := 11, halted := true }
  have hStep8 : step sc7Compact w8 = w9 := by
    rw [step_at sc7Compact w8 sc7_i10 hw6_h hw6_e hG10]
    unfold execInst
    have hOp10 : instOp sc7_i10.name = .s_endpgm := rfl
    simp only [hMod10, Bool.false_eq_true, ↓reduceIte, hOp10]; rfl
  have hRun48 : srun sc7Compact (f + 6) w4 = w9 := by
    rw [show f + 6 = (f + 5) + 1 from rfl,
        srun_step_eq sc7Compact (f + 5) w4 hw4_h hw4_e (joinTarget_none_of sc7Compact w4 sc7_i5 (by rw [hw4_pc]; exact hG5) rfl), hStep4]
    rw [show f + 5 = (f + 4) + 1 from rfl,
        srun_step_eq sc7Compact (f + 4) w5 hw5_h hw5_e (joinTarget_none_of sc7Compact w5 sc7_i6 (by rw [hw5_pc]; exact hG6) rfl), hStep5]
    rw [show f + 4 = (f + 3) + 1 from rfl,
        srun_step_eq sc7Compact (f + 3) w6 hw6_h hw6_e (joinTarget_none_of sc7Compact w6 sc7_i7 (by rw [hw6_pc]; exact hG7) rfl), hStep6]
    rw [show f + 3 = (f + 2) + 1 from rfl,
        srun_step_eq sc7Compact (f + 2) w7 hw6_h hw6_e (joinTarget_none_of sc7Compact w7 sc7_i9 hG9 rfl), hStep7]
    rw [show f + 2 = (f + 1) + 1 from rfl,
        srun_step_eq sc7Compact (f + 1) w8 hw6_h hw6_e (joinTarget_none_of sc7Compact w8 sc7_i10 hG10 rfl), hStep8]
    exact srun_halted_eq sc7Compact f w9 rfl
  dsimp only
  rw [hRun48]
  exact ⟨hw6_e, rfl, rfl⟩

private theorem checkStageW_storeConst7 {σ : Type} (consts : List Word) (s : Spec σ)
    (hs_th : s.threads = 1) (hs_lds : s.lds = 0)
    (hs_tab : s.table (readWord 1 (layoutMem 1 consts []) {}) = some (({} : Std.HashMap Nat TP).insert 0 (pLit 7)))
    (hLay0 : (layoutMem 1 consts [])[descSetAddr >>> 2]? = some 0)
    (hLay1 : (layoutMem 1 consts [])[(descSetAddr >>> 2) + 1]? = some 1)
    (hLay2 : (layoutMem 1 consts [])[(descSetAddr >>> 2) + 2]? = some 8)
    (hLay3 : (layoutMem 1 consts [])[(descSetAddr >>> 2) + 3]? = some 0x31000000) :
    ∃ kn, checkStageW 1 (layoutMem 1 consts []) s storeConst7Prog {} = some (kn, {}) := by
  let T : Std.HashMap Nat TP := ({} : Std.HashMap Nat TP).insert 0 (pLit 7)
  have hEx0 : (fun a => inW 1 a && T.contains (wordOf a)) (descSetAddr >>> 2) = false := by
    simp [show inW 1 (descSetAddr >>> 2) = false by decide]
  have hEx1 : (fun a => inW 1 a && T.contains (wordOf a)) ((descSetAddr >>> 2) + 1) = false := by
    simp [show inW 1 ((descSetAddr >>> 2) + 1) = false by decide]
  have hEx2 : (fun a => inW 1 a && T.contains (wordOf a)) ((descSetAddr >>> 2) + 2) = false := by
    simp [show inW 1 ((descSetAddr >>> 2) + 2) = false by decide]
  have hEx3 : (fun a => inW 1 a && T.contains (wordOf a)) ((descSetAddr >>> 2) + 3) = false := by
    simp [show inW 1 ((descSetAddr >>> 2) + 3) = false by decide]
  have hWave := symWave_storeConst7_base consts (fun a => inW 1 a && T.contains (wordOf a))
    hLay0 hLay1 hLay2 hLay3 hEx0 hEx1 hEx2 hEx3
  have hSpec0 : specAt 1 T (dwLo 0) = some (.lit 7) := by
    unfold specAt
    rw [show (!inW 1 (dwLo 0)) = false by decide, show (dwLo 0 - wDw).toNat = 0 by decide]
    simp [T, pLit]; rfl
  have hSpec1 : specAt 1 T (dwLo 0 + 1) = some (.lit 0) := by
    unfold specAt
    rw [show (!inW 1 (dwLo 0 + 1)) = false by decide, show (dwLo 0 + 1 - wDw).toNat = 1 by decide]
    simp [T, pLit]; rfl
  have hOk7 : storeOkX (.lit 7) (some (.lit 7)) = some none := by simp [storeOkX]
  have hOk0 : storeOkX (.lit 0) (some (.lit 0)) = some none := by simp [storeOkX]
  have hInLds0 : inLds (dwLo 0) = false := by decide
  have hInLds1 : inLds (dwLo 0 + 1) = false := by decide
  have hNe01 : (dwLo 0 == dwLo 0 + 1) = false := by decide
  have hNe10 : (dwLo 0 + 1 == dwLo 0) = false := by decide
  have hTabList : T.toList = [(0, pLit 7)] := hashMap_toList_one 0 (pLit 7)
  dsimp only [T] at hWave hSpec0 hSpec1 hTabList
  unfold checkStageW
  rw [hs_tab, hs_th, hs_lds]
  have hGs : List.range (groupsOf 1) = [0] := rfl
  simp only [hGs, parMap_eq, List.map_cons, List.map_nil, Option.bind_some, waveOutT,
    hWave.1, hWave.2.1, hWave.2.2, Option.isNone_none, Bool.and_self, ↓reduceIte]
  rcases hashMap_toList_two (dwLo 0) (dwLo 0 + 1) (Tm.lit 7) (Tm.lit 0) hNe10 with hSt | hSt
  · refine ⟨applyUpdates {} [(dwLo 0 + 1, some 0), (dwLo 0, some 7)], ?_⟩
    simp only [sharedStores, hSt, List.map_cons, List.map_nil, hSpec0, hSpec1,
      ShareCommon.shareCommon', storePre, hOk7, hOk0, mergeWaves, checkStoresY,
      hInLds0, hInLds1, Bool.false_eq_true, ↓reduceIte, Std.HashSet.contains_empty,
      Std.HashSet.contains_insert, hNe01, Bool.or_self, Option.bind_some, Option.orElse,
      tableStored, hTabList, beq_self_eq_true, Bool.true_or, Bool.or_true, List.all_cons, List.all_nil, Bool.and_self,
      show (Tm.lit 7).litVal? = some 7 from rfl, show (Tm.lit 0).litVal? = some 0 from rfl]
  · refine ⟨applyUpdates {} [(dwLo 0, some 7), (dwLo 0 + 1, some 0)], ?_⟩
    simp only [sharedStores, hSt, List.map_cons, List.map_nil, hSpec0, hSpec1,
      ShareCommon.shareCommon', storePre, hOk7, hOk0, mergeWaves, checkStoresY,
      hInLds0, hInLds1, Bool.false_eq_true, ↓reduceIte, Std.HashSet.contains_empty,
      Std.HashSet.contains_insert, hNe10, Bool.or_self, Option.bind_some, Option.orElse,
      tableStored, hTabList, beq_self_eq_true, Bool.true_or, Bool.or_true, List.all_cons, List.all_nil, Bool.and_self,
      show (Tm.lit 7).litVal? = some 7 from rfl, show (Tm.lit 0).litVal? = some 0 from rfl]

set_option maxRecDepth 200000 in
private theorem certifySchedule_inhabited :
    ∃ (p : GpuProgram) (sched : Schedule) (ldss : List Nat) (progs : List Program) (rs : List Residual),
      0 < p.stages.length ∧ 0 < (p.stages.headD ⟨[]⟩).threads ∧ progs = [storeConst7Prog] ∧
      decodeProgram storeConst7Words = .ok storeConst7Prog ∧ compile p = .ok sched ∧
      certifySchedule p sched ldss progs rs = true := by
  let stage : GpuStage := ⟨[⟨0, 1, .const 0⟩]⟩
  let p : GpuProgram :=
    { words := 1, wireBase := [0], wireLen := [1], consts := [7#64], tables := [], inputs := [], outputs := [0], stages := [stage] }
  let sched : Schedule := ⟨1, #[.elementwise 0 stage]⟩
  have hLay :
      ((layoutMem 1 [7#64] [])[descSetAddr >>> 2]?, (layoutMem 1 [7#64] [])[(descSetAddr >>> 2) + 1]?,
       (layoutMem 1 [7#64] [])[(descSetAddr >>> 2) + 2]?, (layoutMem 1 [7#64] [])[(descSetAddr >>> 2) + 3]?) =
      (some 0, some 1, some 8, some 0x31000000) := by
    set_option cbv.maxSteps 500000 in cbv
  simp only [Prod.mk.injEq] at hLay
  have hTabEq : gpuTableUpTo #[7#64] #[] stage (readWord 1 (layoutMem 1 [7#64] []) {})
      (foldCache (readWord 1 (layoutMem 1 [7#64] []) {}) stage) 1 =
      some (({} : Std.HashMap Nat TP).insert 0 (pLit 7)) := by
    set_option cbv.maxSteps 500000 in cbv
  obtain ⟨kn, hStg⟩ := checkStageW_storeConst7 [7#64]
    { threads := stage.threads, lds := 0,
      table := fun rd => gpuTableUpTo #[7#64] #[] stage rd (foldCache rd stage) 1,
      den := (Action.elementwise 0 stage).eval [7#64] [] }
    rfl rfl hTabEq hLay.1 hLay.2.1 hLay.2.2.1 hLay.2.2.2
  refine ⟨p, sched, [0], [storeConst7Prog], [], by decide, by decide, rfl, decodeProgram_storeConst7, rfl, ?_⟩
  have hAct : actionBounded p 1 (.elementwise 0 stage) = true := by decide
  simp only [certifySchedule, p, sched, hAct, List.all_cons, List.all_nil, Bool.and_true,
    scheduleSpecs, specsOf, actionSpecs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    scheduleTables, List.foldl_cons, List.foldl_nil, actionTables, List.zip_cons_cons,
    List.zip_nil_right, List.map_cons, List.map_nil, checkProgram, checkStage, hStg,
    Option.bind_some, Std.HashSet.fold_eq_foldl_toList, Std.HashSet.toList_empty, List.foldl_nil]
  decide

end Obend.Hardware.Gpu.Rdna2.Schedule
