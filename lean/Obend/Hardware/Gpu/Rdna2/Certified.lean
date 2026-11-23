/-
# Obend.Hardware.Gpu.Rdna2.Certified — a dumped graph, certified

`certifyDump g isa` is the check run once per artifact: the graph is well formed with a checked layout,
every load is waited for before its destination is touched (`Waitcnt`), vector stores complete at
barriers and global/flat stores complete before exit, every stage of the dump `isa`
(`hardware/gpu/isa/<graph>.txt`, RADV's machine code) decodes, and `Schedule.certifySchedule` accepts the
decoded programs against the schedule the emitter dispatches (`ArrayEmit.compile` of `lowerArrayToGpu g`:
elementwise stages and block collectives), with the residuals of `Residuals` (generated, each proved).
`certifyDump_sound` is what an accepted check means, for every input: the programs, run on the model as
the host dispatches them, succeed and leave on the output wires what `evalGraph` computes. The waitcnt
conjunct is what lets that be read as the device's behaviour: the model completes a load when it issues,
which is the device's only once every consumer waits for it (manual 4.4; `Waitcnt`'s header). It is a
hypothesis about the device, checked; everything else is proved.

A block program (the NTT) is checked the same way by `certifyBlockDump`: its admission check
(`ArrayKernel.Program.check`), the waits, the decode, and `Block.certifyBlock` with each dispatch's LDS as
RADV allocated it (the dump's `LDS:` line); `certifyBlockDump_sound` says the model's final wire buffer
holds every device array element `evalProgram` computes, for every memory the host binds.
-/
module
import all Obend.Hardware.ArrayKernel
import all Obend.Hardware.ArrayHypergraph
import all Obend.Hardware.ArrayTyping
import all Obend.Hardware.SquareGraphs
import all Obend.Hardware.Gpu
import all Obend.Hardware.Gpu.ArrayEmit
import all Obend.Hardware.Gpu.ArraySchedule
import all Obend.Hardware.Gpu.Rdna2.Encodings
import all Obend.Hardware.Gpu.Rdna2.Decode
import all Obend.Hardware.Gpu.Rdna2.Check
import all Obend.Hardware.Gpu.Rdna2.Waitcnt
import all Obend.Hardware.Gpu.Rdna2.Block
import all Obend.Hardware.Gpu.Rdna2.Cert
import all Obend.Hardware.Gpu.Rdna2.Host
import all Obend.Hardware.Gpu.Rdna2.Join
import all Obend.Hardware.Gpu.Rdna2.Lower
import all Obend.Hardware.Gpu.Rdna2.Equiv
import all Obend.Hardware.Gpu.Rdna2.Sym
import all Obend.Hardware.Gpu.Rdna2.Term
import all Obend.Hardware.Gpu.Rdna2.Semantics
import all Obend.Hardware.Gpu.Rdna2.Schedule
import all Init.Data.Range.Basic
import all Init.Data.Range.Lemmas
import all Init.Data.String.Basic
import all Init.Data.String.Defs
import all Init.Data.String.Slice
import all Init.Data.String.Extra
import all Init.Data.String.Iterate
import all Init.Data.String.Legacy
import all Init.Data.String.Lemmas
import all Init.Data.String.Search
import all Init.Data.String.TakeDrop
import all Init.Data.Array.QSort.Basic
import all Init.Data.Array.QSort
import all Init.Data.List.Sublist
public import Obend.Hardware.Gpu.Rdna2.CertSound
public import Obend.Hardware.Gpu.Rdna2.Residuals
public import Obend.Hardware.Gpu.Rdna2.Check
public import Obend.Hardware.Gpu.Rdna2.Waitcnt
public import Obend.Hardware.SquareGraphs
public import Obend.Hardware.Gpu.Rdna2.Block
public import Obend.Hardware.Gpu.Rdna2.Schedule
public import Obend.Hardware.Gpu.ArrayEmitCorrect
public import Obend.Hardware.Gpu.NttKernel

public section

namespace Obend.Hardware.Gpu.Rdna2
open Obend.Hardware.Gpu Obend.Hardware.ArrayHypergraph Tm

/-- Every stage of a dump, decoded; `none` if one does not decode. -/
def progsOf (isa : String) : Option (List Program) :=
  (parseDump isa).toList.mapM fun ws => (decodeProgram (ws.flatMap id)).toOption

/-- Each dispatch's LDS in dwords, from the dump's resource lines. -/
def ldssOf (isa : String) : List Nat := (parseDumpLds isa).toList.map (· / 4)

open Schedule ArrayEmit in
/-- The check of one dumped graph: well formed, a checked layout, the waits, and the schedule the emitter
dispatches (`ArrayEmit.compile` of the lowering) certified against the decoded dump. -/
def certifyDump (g : ArrayGraph) (isa : String) : Bool :=
  g.wf && layoutOk g && checkWaitcntDump isa && checkVscntDump isa &&
    match compile (lowerArrayToGpu g), progsOf isa with
    | .ok sched, some progs => certifySchedule (lowerArrayToGpu g) sched (ldssOf isa) progs Residuals.all
    | _, _ => false

open Schedule ArrayEmit ArrayEmitCorrect in
/-- An accepted dump computes the graph: for every input `env` and every wire buffer `flat` that lays out
its live wires, the dumped programs, run on the model as the host dispatches the schedule, succeed, and the
output wires read from the final memory are `evalGraph`'s. -/
theorem certifyDump_sound (g : ArrayGraph) (isa : String) (h : certifyDump g isa = true) :
    checkWaitcntDump isa = true ∧ ∃ sched progs, compile (lowerArrayToGpu g) = .ok sched ∧ progsOf isa = some progs ∧
      ∀ (env : Nat → Vec) (flat : Nat → Word), Good g.lengths env →
        Flat g.lengths (gpuLayout g).base (liveAt (layerGraph (fuseGraph g)) g.outputs) env flat →
        let p := lowerArrayToGpu g
        ∃ m, runDispatch (dispatchesOf (scheduleSpecs p sched.words sched.actions.toList (ldssOf isa)) progs)
            (memOf sched.words p.consts (scheduleTables p sched.actions.toList) flat) = some m ∧
          p.outputs.map (fun w => (List.range (p.wireLen.getD w 0)).map fun e => wordAt m (p.wireBase.getD w 0 + e))
            = evalGraph g env := by
  unfold certifyDump at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hwf, hlay⟩, hwait⟩, _⟩, hc⟩ := h
  refine ⟨hwait, ?_⟩
  split at hc
  · rename_i sched progs hs hp
    refine ⟨sched, progs, hs, hp, fun env flat hGood hFlat => ?_⟩
    obtain ⟨m, hrun, hw⟩ := certifySchedule_sound _ sched _ progs _ hc Residuals.all_hold flat
    refine ⟨m, hrun, ?_⟩
    have hpw : (lowerArrayToGpu g).words ≤ sched.words := by
      unfold certifySchedule at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1.1.1.2
    rw [← lowerArrayToGpu_sound g hwf hlay env flat hGood hFlat]
    have hdev : (fun a => ofDevice flat (.device, a)) = flat := by funext a; simp [ofDevice]
    rw [← hdev, ← compile_runProgram _ sched hs (ofDevice flat)]
    unfold compiledOutputs
    apply List.map_congr_left
    intro w hwo
    have hb := checkBoundaries_sound _ (compile_boundaries _ sched hs) w (List.mem_append_right _ hwo)
    apply List.map_congr_left
    intro e he
    rw [List.mem_range] at he
    exact hw _ (by omega)
  · simp at hc

/-- The check of a graph of `SquareGraphs.graphs` by name (what the pins and the gate run): its typed
graph, built as the emitter builds it, certified against the dump. -/
def certifyNamed (name : String) (isa : String) : Bool :=
  match Obend.Hardware.SquareGraphs.graphs.find? (·.name == name) with
  | some c => match c.build () with
    | .ok tg => certifyDump tg.graph isa
    | .error _ => false
  | none => false

theorem certifyNamed_sound (name isa : String) (h : certifyNamed name isa = true) :
    ∃ c tg, Obend.Hardware.SquareGraphs.graphs.find? (·.name == name) = some c ∧ c.build () = .ok tg ∧
      certifyDump tg.graph isa = true := by
  unfold certifyNamed at h
  split at h
  · rename_i c hf
    split at h
    · rename_i tg hb; exact ⟨c, tg, hf, hb, h⟩
    · simp at h
  · simp at h

/-! ## Block programs -/

open Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.BlockLower Block in
/-- The check of one dumped block program: admitted, waited for, decoded, certified with each dispatch's
LDS (the dump's resource line, in dwords). -/
def certifyBlockDump (p : ArrayKernel.Program) (isa : String) : Bool :=
  (match p.check with | .ok () => true | .error _ => false) && checkWaitcntDump isa && checkVscntBlockDump isa &&
    match progsOf isa with
    | some progs => certifyBlock p (ldssOf isa) progs Residuals.all
    | none => false

open Obend.Hardware.ArrayKernel Obend.Hardware.Gpu.BlockLower Block in
theorem certifyBlockDump_sound (p : ArrayKernel.Program) (isa : String) (h : certifyBlockDump p isa = true) :
    checkWaitcntDump isa = true ∧ ∃ progs, progsOf isa = some progs ∧
      ∀ (mem : ArrayKernel.Memory) (flat : FlatMemory), BlockLower.Good p mem → Represents p mem flat →
        ConstsOk (BlockEmit.constWords p).toArray flat →
        ∃ m, runDispatch (dispatchesOf (blockSpecs p (ldssOf isa)) progs)
            (memOf (blockWords p) (BlockEmit.constWords p) [] (fun j => flat (.device, j))) = some m ∧
          ∀ a i, Valid p a i → (buffer p a).storage = .device →
            wordAt m (bufferBase p a + i) = ((evalProgram p mem).getD a #[]).getD i 0#64 := by
  unfold certifyBlockDump at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hchk, hw⟩, _⟩, hc⟩ := h
  have hchk' : p.check = .ok () := by
    revert hchk; cases p.check with
    | ok u => intro _; rfl
    | error e => intro h; simp at h
  refine ⟨hw, ?_⟩
  split at hc
  · rename_i progs hp
    exact ⟨progs, hp, fun mem flat hg hf hk =>
      certifyBlock_eval p hchk' _ progs _ hc Residuals.all_hold mem flat hg hf hk⟩
  · simp at hc

/-- A block graph by name (`SquareGraphs.blockGraphs`): `Ntt.nttBlockProgram`, the emitter's sole NTT. -/
def certifyBlockNamed (name : String) (isa : String) : Bool :=
  match Obend.Hardware.SquareGraphs.blockGraphs.find? (·.1 == name) with
  | some (_, n) => certifyBlockDump (Obend.Hardware.Gpu.Ntt.nttBlockProgram n) isa
  | none => false

theorem certifyDump_vscnt (g : ArrayGraph) (isa : String) (h : certifyDump g isa = true) :
    checkVscntDump isa = true := by
  simp only [certifyDump, Bool.and_eq_true] at h
  exact h.1.2

theorem certifyBlockDump_vscnt (p : ArrayKernel.Program) (isa : String)
    (h : certifyBlockDump p isa = true) : checkVscntBlockDump isa = true := by
  simp only [certifyBlockDump, Bool.and_eq_true] at h
  exact h.1.2

/-- Real ENC_FLAT_GLBL global_store_dword v[0:1], v2, off, then endpgm. -/
@[expose] def unawaitedGlobalStoreDump : String :=
  "## stage 0\n\tglobal_store_dword v[0:1], v2, off\t; dc708000 007f0200\n\ts_endpgm\t; bf810000\n"

@[expose] def awaitedGlobalStoreDump : String :=
  "## stage 0\n\tglobal_store_dword v[0:1], v2, off\t; dc708000 007f0200\n\ts_waitcnt_vscnt null, 0x0\t; bbfd0000\n\ts_endpgm\t; bf810000\n"

private theorem foldl_cbv {α : Type} (f : α → Char → α) (init : α) (s : String) :
    s.foldl f init = s.toList.foldl f init :=
  String.foldl_eq_foldl_toList

private theorem forIn'_range_0_1_except {β : Type} (init : β)
    (f : (a : Nat) → a ∈ [:1] → β → Except String (ForInStep β)) :
    [:1].forIn' init f = (do
      match ← f 0 ⟨Nat.zero_le 0, Nat.zero_lt_one, by decide⟩ init with
      | .done b => pure b
      | .yield b => pure b) := by
  simp [Std.Legacy.Range.forIn', Std.Legacy.Range.forIn'.loop]; rfl

private theorem hashSet_emptyWithCapacity_toList {α : Type} [BEq α] [Hashable α] {c : Nat} :
    (Std.HashSet.emptyWithCapacity c : Std.HashSet α).toList = [] :=
  Std.HashSet.toList_emptyWithCapacity (α := α) (c := c)

private theorem hashSet_toList_insert_empty {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {c : Nat} (a : α) :
    ((Std.HashSet.emptyWithCapacity c : Std.HashSet α).insert a).toList = [a] := by
  have hLen : ((Std.HashSet.emptyWithCapacity c : Std.HashSet α).insert a).toList.length = 1 := by
    rw [Std.HashSet.length_toList, Std.HashSet.size_insert]
    simp [Std.HashSet.not_mem_emptyWithCapacity, Std.HashSet.size_emptyWithCapacity]
  have hMem : a ∈ ((Std.HashSet.emptyWithCapacity c : Std.HashSet α).insert a).toList :=
    Std.HashSet.mem_toList.mpr (Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true a)))
  cases hL : ((Std.HashSet.emptyWithCapacity c : Std.HashSet α).insert a).toList with
  | nil => simp [hL] at hLen
  | cons x rest =>
    cases rest with
    | nil => rw [hL] at hMem; simp at hMem; subst hMem; rfl
    | cons _ _ => simp [hL] at hLen

attribute [local cbv_eval] foldl_cbv forIn'_range_0_1_except
  hashSet_emptyWithCapacity_toList hashSet_toList_insert_empty
  Schedule.str_startsWith_eq Schedule.str_contains_eq Schedule.str_drop_cbv
  Schedule.hashMap_getElem?_insert_cbv Schedule.hashMap_getElem?_empty_cbv
  Schedule.hashMap_get?_insert_cbv Schedule.hashMap_get?_empty_cbv
  Schedule.hashSet_contains_insert_cbv Schedule.hashSet_contains_empty_cbv

private def storeConst7Dump : String :=
  "## stage 0, LDS: 0\n" ++
  "\tv_cmpx_gt_u32_e32 1, v0\t; 7da80081\n" ++
  "\ts_movk_i32 s3, 0x8000\t; b0038000\n" ++
  "\ts_load_dwordx4 s[0:3], s[2:3], null\t; f4080001 fa000000\n" ++
  "\ts_waitcnt lgkmcnt(0)\t; bf8cc07f\n" ++
  "\tv_mov_b32_e32 v4, 7\t; 7e080287\n" ++
  "\tv_mov_b32_e32 v5, 0\t; 7e0a0280\n" ++
  "\tbuffer_store_dwordx2 v[4:5], v0, s[0:3], 0 offen\t; e0741000 80000400\n" ++
  "\ts_waitcnt_vscnt null, 0x0\t; bbfd0000\n" ++
  "\ts_endpgm\t; bf810000\n"

private theorem instructionPcs_map_stripInst (prog : Program) :
    instructionPcs (prog.map (Option.map Schedule.stripInst)) = instructionPcs prog := by
  unfold instructionPcs
  simp only [Array.size_map]
  congr 1; funext d
  simp only [Array.getElem?_map]
  cases prog[d]? with
  | none => rfl
  | some oi => cases oi <;> rfl

private theorem leadersOf_map_stripInst (prog : Program) :
    leadersOf (prog.map (Option.map Schedule.stripInst)) = leadersOf prog := by
  unfold leadersOf
  dsimp only
  rw [instructionPcs_map_stripInst]
  congr 1
  have hFold : ∀ (pcs acc : List Nat),
      pcs.foldl (fun acc pc =>
        match (prog.map (Option.map Schedule.stripInst))[pc]! with
        | some i => if isBranch i then acc ++ [branchTarget pc i, pc + i.words.length] else acc
        | none => acc) acc =
      pcs.foldl (fun acc pc =>
        match prog[pc]! with
        | some i => if isBranch i then acc ++ [branchTarget pc i, pc + i.words.length] else acc
        | none => acc) acc := by
    intro pcs
    induction pcs with
    | nil => intro acc; rfl
    | cons pc rest ih =>
      intro acc
      simp only [List.foldl_cons]
      have hGet : (prog.map (Option.map Schedule.stripInst))[pc]! = (prog[pc]!).map Schedule.stripInst := by
        by_cases hlt : pc < prog.size
        · simp [hlt]
        · simp [hlt]; rfl
      rw [hGet]
      cases prog[pc]! with
      | none => exact ih acc
      | some i => exact ih _
  exact hFold (instructionPcs prog) [0]

private theorem runVscntBlock_map_stripInst (strict : Bool) (prog : Program) (leaders : List Nat) :
    ∀ fuel pc p,
      runVscntBlock strict (prog.map (Option.map Schedule.stripInst)) leaders fuel pc p =
      (runVscntBlock strict prog leaders fuel pc p).map fun (p', n, oi) => (p', n, oi.map Schedule.stripInst)
  | 0, _, _ => rfl
  | fuel + 1, pc, p => by
    unfold runVscntBlock
    simp only [Array.getElem?_map]
    cases prog[pc]? with
    | none => rfl
    | some oi =>
      cases oi with
      | none => rfl
      | some i =>
        dsimp only [Option.map]
        have hStep : stepVscnt strict p (Schedule.stripInst i) = stepVscnt strict p i := rfl
        rw [hStep]
        cases hq : stepVscnt strict p i with
        | error e => rfl
        | ok q =>
          dsimp only [bind, Except.bind]
          change (if isBranch i || i.inst.isTerminator then pure (q, pc + i.words.length, some (Schedule.stripInst i))
            else if leaders.contains (pc + i.words.length) then pure (q, pc + i.words.length, none)
            else runVscntBlock strict (prog.map (Option.map Schedule.stripInst)) leaders fuel (pc + i.words.length) q) = _
          split
          · rfl
          · split
            · rfl
            · exact runVscntBlock_map_stripInst strict prog leaders fuel (pc + i.words.length) q

private theorem vscntFixpoint_map_stripInst (strict : Bool) (prog : Program) (leaders : List Nat) :
    ∀ fuel entry work,
      vscntFixpoint strict (prog.map (Option.map Schedule.stripInst)) leaders fuel entry work =
      vscntFixpoint strict prog leaders fuel entry work
  | 0, _, [] => rfl
  | _ + 1, _, [] => rfl
  | 0, _, _ :: _ => rfl
  | fuel + 1, entry, pc :: rest => by
    unfold vscntFixpoint
    simp only [Array.size_map, runVscntBlock_map_stripInst]
    cases runVscntBlock strict prog leaders (prog.size + 1) pc ((entry.find? (·.1 == pc)).map (·.2) |>.getD {}) with
    | error e => rfl
    | ok res =>
      rcases res with ⟨pOut, next, last⟩
      have hBind : ∀ (succs : List Nat) (body : Nat → List (Nat × VsPending) × List Nat →
          Except String (ForInStep (List (Nat × VsPending) × List Nat))),
          (do let r ← forIn succs (entry, rest) body; vscntFixpoint strict (prog.map (Option.map Schedule.stripInst)) leaders fuel r.1 r.2) =
          (do let r ← forIn succs (entry, rest) body; vscntFixpoint strict prog leaders fuel r.1 r.2) := by
        intro succs body
        dsimp only [bind, Except.bind]
        cases forIn succs (entry, rest) body with
        | error e => rfl
        | ok v => exact vscntFixpoint_map_stripInst strict prog leaders fuel v.1 v.2
      cases last with
      | none =>
        dsimp only [Except.map, Option.map, bind, Except.bind]
        exact hBind [next] _
      | some i =>
        dsimp only [Except.map, Option.map, bind, Except.bind]
        exact hBind (if i.inst.isTerminator then []
          else if isUncondBranch i then [branchTarget (next - i.words.length) i]
          else [branchTarget (next - i.words.length) i, next]) _

private theorem checkVscntProg_map_stripInst (strict : Bool) (prog : Program) :
    checkVscntProg strict (prog.map (Option.map Schedule.stripInst)) = checkVscntProg strict prog := by
  unfold checkVscntProg
  rw [leadersOf_map_stripInst, vscntFixpoint_map_stripInst]

set_option maxRecDepth 100000 in
private theorem parseDump_storeConst7 :
    parseDump storeConst7Dump = #[#[#[0x7da80081], #[0xb0038000], #[0xf4080001, 0xfa000000],
      #[0xbf8cc07f], #[0x7e080287], #[0x7e0a0280], #[0xe0741000, 0x80000400],
      #[0xbbfd0000], #[0xbf810000]]] := by
  set_option cbv.maxSteps 500000 in
  cbv

set_option maxRecDepth 100000 in
private theorem parseDumpLds_storeConst7 :
    parseDumpLds storeConst7Dump = #[0] := by
  set_option cbv.maxSteps 500000 in
  cbv

private theorem storeConst7_flatMap :
    (#[#[0x7da80081], #[0xb0038000], #[0xf4080001, 0xfa000000], #[0xbf8cc07f],
       #[0x7e080287], #[0x7e0a0280], #[0xe0741000, 0x80000400],
       #[0xbbfd0000], #[0xbf810000]] : Array (Array UInt32)).flatMap id =
    Schedule.storeConst7Words := rfl

private theorem progsOf_storeConst7 :
    progsOf storeConst7Dump = some [Schedule.storeConst7Prog] := by
  unfold progsOf
  rw [parseDump_storeConst7]
  change [#[#[0x7da80081], #[0xb0038000], #[0xf4080001, 0xfa000000], #[0xbf8cc07f],
       #[0x7e080287], #[0x7e0a0280], #[0xe0741000, 0x80000400],
       #[0xbbfd0000], #[0xbf810000]]].mapM (fun ws => (decodeProgram (ws.flatMap id)).toOption) = _
  simp only [List.mapM_cons, List.mapM_nil, storeConst7_flatMap, Schedule.decodeProgram_storeConst7,
    Except.toOption, bind, Option.bind, pure]

private theorem ldssOf_storeConst7 : ldssOf storeConst7Dump = [0] := by
  simp [ldssOf, parseDumpLds_storeConst7]

private theorem checkVscntDumpReport_storeConst7 (block : Bool)
    (hCheck : checkVscntProg block Schedule.sc7Compact = .ok ()) :
    (checkVscntDumpReport storeConst7Dump block).toBool = true := by
  have hCheckProg : checkVscntProg block Schedule.storeConst7Prog = .ok () := by
    rw [← checkVscntProg_map_stripInst, Schedule.storeConst7Prog_strip]; exact hCheck
  unfold checkVscntDumpReport
  rw [parseDump_storeConst7]
  dsimp only
  have hIsEmpty : (#[#[#[0x7da80081], #[0xb0038000], #[0xf4080001, 0xfa000000], #[0xbf8cc07f],
      #[0x7e080287], #[0x7e0a0280], #[0xe0741000, 0x80000400], #[0xbbfd0000], #[0xbf810000]]] :
      Array (Array (Array UInt32))).isEmpty = false := rfl
  have hZip : (#[#[#[0x7da80081], #[0xb0038000], #[0xf4080001, 0xfa000000], #[0xbf8cc07f],
      #[0x7e080287], #[0x7e0a0280], #[0xe0741000, 0x80000400], #[0xbbfd0000], #[0xbf810000]]] :
      Array (Array (Array UInt32))).zipIdx =
      #[(#[#[0x7da80081], #[0xb0038000], #[0xf4080001, 0xfa000000], #[0xbf8cc07f],
      #[0x7e080287], #[0x7e0a0280], #[0xe0741000, 0x80000400], #[0xbbfd0000], #[0xbf810000]], 0)] := rfl
  rw [hIsEmpty, hZip]
  simp only [Bool.false_eq_true, ↓reduceIte, List.forIn_toArray, List.forIn_cons, List.forIn_nil,
    storeConst7_flatMap, Schedule.decodeProgram_storeConst7, bind, Except.bind, pure, Except.pure, hCheckProg]
  rfl

set_option maxRecDepth 100000 in
private theorem checkVscntDump_storeConst7 : checkVscntDump storeConst7Dump = true :=
  checkVscntDumpReport_storeConst7 false (by set_option cbv.maxSteps 500000 in cbv)

set_option maxRecDepth 100000 in
private theorem checkVscntBlockDump_storeConst7 : checkVscntBlockDump storeConst7Dump = true :=
  checkVscntDumpReport_storeConst7 true (by set_option cbv.maxSteps 500000 in cbv)

private def witnessConst7Graph : ArrayGraph :=
  { lengths := [1], inputs := [], outputs := [0], edges := [⟨0, .const [7#64], [], 0⟩] }

private def witnessConst7Stage : GpuStage := ⟨[⟨0, 1, .const 0⟩]⟩

private def witnessConst7Sched : ArrayEmit.Schedule :=
  { words := 1, actions := #[.elementwise 0 witnessConst7Stage] }

/- Constructive inhabitedness witness for `certifyDump` on a real 1-thread, 1-wave, 9-instruction
RDNA2 machine-code shader (`storeConst7Dump`) storing `7#64` to output wire 0. Every kernel-reducible
check (`g.wf`, `layoutOk`, `checkVscntDump`, `compile`, `progsOf`, `ldssOf`, `certifySchedule` via
full 9-step symbolic execution) is discharged unconditionally; `hWait` is parameterized solely because
unowned `Waitcnt.runBlock` (`Waitcnt.lean:209`, `partial def`) and `Waitcnt.checkWaitcnt`
(`Waitcnt.lean:241`, `while` loop) are opaque to Lean's kernel (`#eval checkWaitcntDump storeConst7Dump = true`). -/
open Schedule ArrayEmit ArrayEmitCorrect in
set_option maxRecDepth 200000 in
private theorem certifyDump_inhabited
    (hWait : checkWaitcntDump storeConst7Dump = true) :
    0 < witnessConst7Graph.edges.length ∧
    0 < (lowerArrayToGpu witnessConst7Graph).stages.length ∧
    0 < ((lowerArrayToGpu witnessConst7Graph).stages.headD ⟨[]⟩).threads ∧
    progsOf storeConst7Dump = some [Schedule.storeConst7Prog] ∧
    checkVscntDump storeConst7Dump = true ∧
    certifyDump witnessConst7Graph storeConst7Dump = true := by
  have hWf : witnessConst7Graph.wf = true := by cbv
  have hLay : layoutOk witnessConst7Graph = true := by cbv
  have hLower : lowerArrayToGpu witnessConst7Graph =
      { words := 1, wireBase := [0], wireLen := [1], consts := [7#64],
        tables := [], inputs := [], outputs := [0], stages := [witnessConst7Stage] } := by
    set_option cbv.maxSteps 500000 in cbv
  have hComp : compile (lowerArrayToGpu witnessConst7Graph) = .ok witnessConst7Sched := by
    rw [hLower]; rfl
  have hMemLay :
      ((layoutMem 1 [7#64] [])[descSetAddr >>> 2]?, (layoutMem 1 [7#64] [])[(descSetAddr >>> 2) + 1]?,
       (layoutMem 1 [7#64] [])[(descSetAddr >>> 2) + 2]?, (layoutMem 1 [7#64] [])[(descSetAddr >>> 2) + 3]?) =
      (some 0, some 1, some 8, some 0x31000000) := by
    set_option cbv.maxSteps 500000 in cbv
  simp only [Prod.mk.injEq] at hMemLay
  have hTabEq : gpuTableUpTo #[7#64] #[] witnessConst7Stage (readWord 1 (layoutMem 1 [7#64] []) {})
      (foldCache (readWord 1 (layoutMem 1 [7#64] []) {}) witnessConst7Stage) 1 =
      some (({} : Std.HashMap Nat TP).insert 0 (pLit 7)) := by
    set_option cbv.maxSteps 500000 in cbv
  obtain ⟨kn, hStg⟩ := Schedule.checkStageW_storeConst7 [7#64]
    { threads := witnessConst7Stage.threads, lds := 0,
      table := fun rd => gpuTableUpTo #[7#64] #[] witnessConst7Stage rd (foldCache rd witnessConst7Stage) 1,
      den := (Action.elementwise 0 witnessConst7Stage).eval [7#64] [] }
    rfl rfl hTabEq hMemLay.1 hMemLay.2.1 hMemLay.2.2.1 hMemLay.2.2.2
  have hSched : certifySchedule (lowerArrayToGpu witnessConst7Graph) witnessConst7Sched [0]
      [Schedule.storeConst7Prog] Residuals.all = true := by
    simp only [certifySchedule, hLower, witnessConst7Sched, List.all_cons, List.all_nil, Bool.and_true,
      scheduleSpecs, specsOf, actionSpecs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      scheduleTables, List.foldl_cons, List.foldl_nil, actionTables, List.zip_cons_cons,
      List.zip_nil_right, List.map_cons, List.map_nil, checkProgram, checkStage, hStg,
      Option.bind_some, Std.HashSet.fold_eq_foldl_toList, Std.HashSet.toList_empty, List.foldl_nil]
    decide
  refine ⟨by decide, by rw [hLower]; decide, by rw [hLower]; decide,
    progsOf_storeConst7, checkVscntDump_storeConst7, ?_⟩
  simp [certifyDump, hWf, hLay, hWait, checkVscntDump_storeConst7, hComp, progsOf_storeConst7,
    ldssOf_storeConst7, hSched]

private def diamondSched : ArrayEmit.Schedule :=
  { words := 4
  , actions := #[.elementwise 0
      { kernels := [⟨0, 1, .prog
          [⟨.scalar .add, [.read 0, .read 1], 4⟩,
           ⟨.scalar .add, [.read 2, .read 3], 5⟩,
           ⟨.scalar .mul, [.tmp 4, .tmp 5], 6⟩,
           ⟨.scalar .add, [.cst 0], 7⟩,
           ⟨.scalar .add, [.tmp 6, .tmp 7], 8⟩] 8⟩] }] }

/- Inhabitedness witness for `certifyNamed "diamond"`: discharges graph lookup, Core4 typed-graph
construction (`GraphTyping`, `layoutOk`, `wf`), and `ArrayEmit.compile` unconditionally in the kernel.
The dump-dependent checks (`hWait` via opaque `partial def Waitcnt.runBlock` plus the 38-instruction
RADV `diamond.txt` decode/schedule) remain hypotheses; end-to-end kernel certification of a live
RDNA2 dump is discharged unconditionally (bar `hWait`) in `certifyDump_inhabited` and
`certifyBlockDump_inhabited`. -/
open Schedule ArrayEmit ArrayEmitCorrect in
set_option maxRecDepth 100000 in
private theorem certifyNamed_diamond_inhabited {isa : String} {progs : List Program}
    (hWait : checkWaitcntDump isa = true) (hVscnt : checkVscntDump isa = true)
    (hProgs : progsOf isa = some progs)
    (hSched : certifySchedule (lowerArrayToGpu (Obend.Hardware.ArrayHypergraph.ofScalar
        Obend.Hardware.OpenHypergraph.diamondAddMulConstHypergraph)) diamondSched
        (ldssOf isa) progs Residuals.all = true) :
    certifyNamed "diamond" isa = true := by
  let g := Obend.Hardware.ArrayHypergraph.ofScalar Obend.Hardware.OpenHypergraph.diamondAddMulConstHypergraph
  let c := Obend.Hardware.SquareGraphs.scalarCase "diamond"
    "Obend.Hardware.OpenHypergraph.diamondAddMulConstHypergraph"
    Obend.Hardware.OpenHypergraph.diamondAddMulConstHypergraph
  have hTyp : Obend.Hardware.ArrayTyping.GraphTyping (Obend.Hardware.ArrayTyping.wordTypes g) g := by
    decide +kernel
  have hLay : layoutOk g = true := by cbv
  let tg : Obend.Hardware.ArrayTyping.TypedGraph :=
    ⟨g, Obend.Hardware.ArrayTyping.wordTypes g, hTyp, hLay⟩
  have hFind : Obend.Hardware.SquareGraphs.graphs.find? (·.name == "diamond") = some c := rfl
  have hBuild : c.build () = .ok tg := by cbv
  have hWf : g.wf = true := hTyp.wf
  have hComp : compile (lowerArrayToGpu g) = .ok diamondSched := by
    set_option cbv.maxSteps 500000 in
    cbv
  have hDump : certifyDump g isa = true := by
    simp only [certifyDump, hWf, hLay, hWait, hVscnt, hComp, hProgs]
    exact hSched
  have hDumpTg : certifyDump tg.graph isa = true := hDump
  simp [certifyNamed, hFind, hBuild, hDumpTg]

/- Constructive inhabitedness witness for `certifyBlockDump` on a non-empty 1-dispatch, 1-phase
block program (`0 < ph.code.length ∧ 0 < ph.writes.length`) storing `7#64` to device buffer 0,
certified against the real 1-wave 9-instruction RDNA2 shader `storeConst7Dump`. Only `hWait`
remains a hypothesis due to kernel-opaque `partial def Waitcnt.runBlock` (`Waitcnt.lean:209`)
and `while` loop in `Waitcnt.checkWaitcnt` (`Waitcnt.lean:241`); `#eval checkWaitcntDump storeConst7Dump = true`. -/
open Obend.Hardware.ArrayKernel Block in
set_option maxRecDepth 200000 in
private theorem certifyBlockDump_inhabited
    (hWait : checkWaitcntDump storeConst7Dump = true) :
    let ph : Phase := ⟨1, [], [⟨.scalar (.const 7), [], 0⟩], [⟨0, .lane, 0⟩]⟩
    let p : ArrayKernel.Program := ⟨[⟨1, .device, []⟩], [], [0], [⟨1, [ph]⟩]⟩
    0 < p.dispatches.length ∧ 0 < ph.code.length ∧ 0 < ph.writes.length ∧
    progsOf storeConst7Dump = some [Schedule.storeConst7Prog] ∧
    checkVscntBlockDump storeConst7Dump = true ∧
    certifyBlockDump p storeConst7Dump = true := by
  intro ph p
  have hChk : p.check = .ok () := by
    set_option cbv.maxSteps 500000 in cbv
  have hMemLay :
      ((layoutMem 1 [] [])[descSetAddr >>> 2]?, (layoutMem 1 [] [])[(descSetAddr >>> 2) + 1]?,
       (layoutMem 1 [] [])[(descSetAddr >>> 2) + 2]?, (layoutMem 1 [] [])[(descSetAddr >>> 2) + 3]?) =
      (some 0, some 1, some 8, some 0x31000000) := by
    set_option cbv.maxSteps 500000 in cbv
  simp only [Prod.mk.injEq] at hMemLay
  let T : Std.HashMap Nat TP := ({} : Std.HashMap Nat TP).insert 0 (pLit 7)
  let O : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert 0 0
  let I : Std.HashMap Nat (List Nat) := ({} : Std.HashMap Nat (List Nat)).insert 0 [0]
  have hPart : ∀ (rd : Nat → TP) (has : Nat → Bool),
      blockPart p ⟨1, [ph]⟩ 1 #[] rd has 0 = some T := by
    intro rd has
    have hEntries : (({} : WMap).insert (key (.device, 0)) (pLit 7)).toList = [(key (.device, 0), pLit 7)] :=
      Schedule.hashMap_toList_one (key (.device, 0)) (pLit 7)
    have hRg : rget (({} : Regs).insert 0 (pLit 7)) 0 = pLit 7 := by simp [rget]
    change (merge 1 (({} : WMap).insert (key (.device, 0)) (rget (({} : Regs).insert 0 (pLit 7)) 0)).toList {}) = some T
    rw [hRg, hEntries]
    simp [key, scode, merge, T]
  have hTList : T.toList = [(0, pLit 7)] := Schedule.hashMap_toList_one 0 (pLit 7)
  have hTKeys : T.keys = [0] := by
    have hLen : T.keys.length = 1 := by rw [Std.HashMap.length_keys, ← Std.HashMap.length_toList, hTList]; rfl
    have hMem : 0 ∈ T.keys := Std.HashMap.mem_keys.mpr (by simp [T])
    cases hK : T.keys with
    | nil => simp [hK] at hLen
    | cons a rest =>
      cases rest with
      | nil => rw [hK] at hMem; simp at hMem; subst hMem; rfl
      | cons _ _ => simp [hK] at hLen
  have hOList : O.toList = [(0, 0)] := Schedule.hashMap_toList_one 0 0
  have hOwners : ownersGuess (blockPart p ⟨1, [ph]⟩ 1 #[] (readWord 1 (layoutMem 1 [] []) {})) [0] = O := by
    unfold ownersGuess
    simp only [parMap_eq, List.map_cons, List.map_nil, hPart, Option.map_some, hTKeys,
      List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, O]
  have hOwnedBy : ownedBy O = I := by
    unfold ownedBy
    simp only [hOList, List.foldl_cons, List.foldl_nil, Std.HashMap.getD_empty, I]
  have hEx0 : (fun a => inW 1 a && hasOf O 0 (wordOf a)) (descSetAddr >>> 2) = false := by
    simp [show inW 1 (descSetAddr >>> 2) = false by decide]
  have hEx1 : (fun a => inW 1 a && hasOf O 0 (wordOf a)) ((descSetAddr >>> 2) + 1) = false := by
    simp [show inW 1 ((descSetAddr >>> 2) + 1) = false by decide]
  have hEx2 : (fun a => inW 1 a && hasOf O 0 (wordOf a)) ((descSetAddr >>> 2) + 2) = false := by
    simp [show inW 1 ((descSetAddr >>> 2) + 2) = false by decide]
  have hEx3 : (fun a => inW 1 a && hasOf O 0 (wordOf a)) ((descSetAddr >>> 2) + 3) = false := by
    simp [show inW 1 ((descSetAddr >>> 2) + 3) = false by decide]
  have hWave := Schedule.symWave_storeConst7_base [] (fun a => inW 1 a && hasOf O 0 (wordOf a))
    hMemLay.1 hMemLay.2.1 hMemLay.2.2.1 hMemLay.2.2.2 hEx0 hEx1 hEx2 hEx3
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
  have hStg : ∃ kn, checkStage 1 (layoutMem 1 [] []) (blockSpec p ⟨1, [ph]⟩ 1 #[] 0)
      Schedule.storeConst7Prog {} = some (kn, {}) := by
    unfold checkStage
    dsimp only [blockSpec]
    have hGs : List.range (groupsOf (1 * lanes)) = [0] := rfl
    have hO0 : O[0]? = some 0 := by simp [O]
    have hI0 : I.getD 0 [] = [0] := by simp [I]
    have hT0 : T.contains 0 = true := by simp [T]
    simp only [hGs, hOwners, hOList, ↓reduceIte, hOwnedBy, parMap_eq, List.map_cons, List.map_nil,
      waveOut, hPart, Option.bind_some, hTList, hO0, hI0, hT0, beq_self_eq_true, Bool.and_self,
      List.all_cons, List.all_nil, Bool.and_true, hWave.1, hWave.2.1, hWave.2.2, Option.isNone_none]
    rcases Schedule.hashMap_toList_two (dwLo 0) (dwLo 0 + 1) (Tm.lit 7) (Tm.lit 0) hNe10 with hSt | hSt
    · refine ⟨applyUpdates {} [(dwLo 0 + 1, some 0), (dwLo 0, some 7)], ?_⟩
      simp only [sharedStores, hSt, List.map_cons, List.map_nil, hSpec0, hSpec1,
        ShareCommon.shareCommon', storePre, hOk7, hOk0, mergeWaves, checkStoresY,
        hInLds0, hInLds1, Bool.false_eq_true, ↓reduceIte, Std.HashSet.contains_empty,
        Std.HashSet.contains_insert, hNe01, Bool.or_self, Option.bind_some,
        ownedStored, hOList, beq_self_eq_true, Bool.true_or, Bool.or_true, List.all_cons, List.all_nil, Bool.and_self,
        show (Tm.lit 7).litVal? = some 7 from rfl, show (Tm.lit 0).litVal? = some 0 from rfl]
      split
      · rfl
      · next h => exact absurd (by decide : 0 < groupsOf (1 * lanes)) (by simpa [decide_eq_true_eq] using h)
    · refine ⟨applyUpdates {} [(dwLo 0, some 7), (dwLo 0 + 1, some 0)], ?_⟩
      simp only [sharedStores, hSt, List.map_cons, List.map_nil, hSpec0, hSpec1,
        ShareCommon.shareCommon', storePre, hOk7, hOk0, mergeWaves, checkStoresY,
        hInLds0, hInLds1, Bool.false_eq_true, ↓reduceIte, Std.HashSet.contains_empty,
        Std.HashSet.contains_insert, hNe10, Bool.or_self, Option.bind_some,
        ownedStored, hOList, beq_self_eq_true, Bool.true_or, Bool.or_true, List.all_cons, List.all_nil, Bool.and_self,
        show (Tm.lit 7).litVal? = some 7 from rfl, show (Tm.lit 0).litVal? = some 0 from rfl]
      split
      · rfl
      · next h => exact absurd (by decide : 0 < groupsOf (1 * lanes)) (by simpa [decide_eq_true_eq] using h)
  obtain ⟨kn, hStgEq⟩ := hStg
  have hBlk : certifyBlock p [0] [Schedule.storeConst7Prog] Residuals.all = true := by
    have hBW : blockWords p = 1 := rfl
    have hCW : BlockEmit.constWords p = [] := rfl
    have hSpecs : blockSpecs p [0] = [blockSpec p ⟨1, [ph]⟩ 1 #[] 0] := by
      unfold blockSpecs; rw [hBW, hCW]; rfl
    simp only [certifyBlock, hBW, hCW, hSpecs, checkProgram, hStgEq, Option.bind_some,
      Std.HashSet.fold_eq_foldl_toList, Std.HashSet.toList_empty, List.foldl_nil]
    decide
  refine ⟨by decide, by decide, by decide, progsOf_storeConst7, checkVscntBlockDump_storeConst7, ?_⟩
  simp [certifyBlockDump, hChk, hWait, checkVscntBlockDump_storeConst7, progsOf_storeConst7,
    ldssOf_storeConst7, hBlk]

end Obend.Hardware.Gpu.Rdna2
