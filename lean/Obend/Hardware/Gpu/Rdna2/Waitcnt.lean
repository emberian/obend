/-
# Obend.Hardware.Gpu.Rdna2.Waitcnt — are the dump's `s_waitcnt`s sufficient?

The model of `Semantics` completes every memory access when it issues, so a program that read a load's
destination before waiting for it would compute the right answer there and a stale one on the device.
This module closes that gap statically: it walks a decoded program tracking the outstanding loads and
refuses it if any instruction reads or writes a register that an outstanding load still writes.

The counters are the manual's (RDNA 2 ISA, 4.4 "Data Dependency Resolution"): `VM_CNT` counts vector
memory loads, which return in issue order, so `s_waitcnt vmcnt(k)` guarantees all but the last `k`
have completed; `LGKM_CNT` counts LDS reads and writes, which return in issue order, and scalar memory
loads, which "can return out-of-order (in which case only S_WAITCNT 0 is the only legitimate value)"
(4.4, 7.3), so `lgkmcnt(k)` retires all but the last `k` LDS events while no scalar load is outstanding
and only `lgkmcnt(0)` completes anything otherwise; `VS_CNT` counts stores, whose completion no register depends on; `EXP_CNT` counts exports, of
which these programs have none. The hazard rules are those of LLVM's `SIInsertWaitcnts` pass
(llvm/lib/Target/AMDGPU/SIInsertWaitcnts.cpp, release 19.x, the pass that inserted the waits RADV's
dumps carry, since ACO follows the same hardware rules): every use and every def of an instruction is
checked against the counter that scores it (`generateWaitcntInstBefore`: VGPRs against the vector
memory counter, SGPRs against the scalar memory counter; "RAW always needs an s_waitcnt. WAW needs an
s_waitcnt unless the previous write and this write are the same type of VMEM instruction", which on
gfx10 write in order, `hasVmemWriteVgprInOrder`); a wait of `k` on an in-order counter retires all but
the last `k` events (`applyWaitcnt`: `LB := UB - k`) and nothing on an out-of-order one
(`counterOutOfOrder`: scalar memory pending); a store's data VGPRs need no wait on gfx10
(`vmemWriteNeedsExpWaitcnt` is false there); at a join of control flow the pending events are merged
most-recent-first (`WaitcntBrackets::merge`, scores shifted to the new upper bound). The walk is a
dataflow over the basic blocks to a fixpoint, as the pass does.

The independent VS_CNT analysis joins bounded store counts across every reachable CFG edge.
All stores must complete before barriers. Global/flat stores must also complete before kernel exit;
block certification requires buffer stores to complete there too. Graph certification retains the
RADV elementwise convention of allowing buffer stores at exit. Only S_WAITCNT_VSCNT drains VS_CNT.

`hardware/gpu/isa_check.sh` stage 6 runs `checkWaitcntDump` on every dump and requires that a dump with
one `s_waitcnt` replaced by `s_nop 0` (same width, so no branch moves) is refused.
-/
module
public import Obend.Hardware.Gpu.Rdna2.Check
public section

namespace Obend.Hardware.Gpu.Rdna2

/-! ## 1. What an instruction reads and writes -/

/-- A register: a VGPR, or an SGPR by its 7-bit scalar code (106/107 VCC, 124 M0, 126/127 EXEC). -/
inductive Reg where
  | v (n : Nat)
  | s (n : Nat)
  deriving DecidableEq, Repr

def Reg.toString : Reg → String
  | .v n => s!"v{n}"
  | .s n => if n == 106 then "vcc_lo" else if n == 107 then "vcc_hi" else if n == 126 then "exec_lo" else if n == 127 then "exec_hi" else s!"s{n}"

instance : ToString Reg := ⟨Reg.toString⟩

/-- The registers a source code names, `k` dwords wide: SGPRs, VCC, EXEC, M0 and VGPRs; inline constants
and the literal name none (manual Tables 10 and 20). -/
@[expose] def regsOfCode (code k : Nat) : List Reg :=
  if code ≤ 107 || code == 124 || code == 126 || code == 127 then (List.range k).map fun j => .s (code + j)
  else if 256 ≤ code && code ≤ 511 then (List.range k).map fun j => .v (code - 256 + j)
  else []

def vregs (n k : Nat) : List Reg := (List.range k).map fun j => .v (n + j)
def sregs (n k : Nat) : List Reg := (List.range k).map fun j => .s (n + j)

@[cbv_eval] theorem vregs_eq (n k : Nat) : vregs n k = (List.range k).map (fun j => Reg.v (n+j)) := by rfl
@[cbv_eval] theorem sregs_eq (n k : Nat) : sregs n k = (List.range k).map (fun j => Reg.s (n+j)) := by rfl

structure Access where
  reads : List Reg
  writes : List Reg
  deriving Repr

/-- From the XML's operand list (field, type, size, Input/Output) and the decoded fields: VGPR fields by
number, source fields by code, the implicit VCC of VOP2/VOPC, EXEC for V_CMPX and the branches, MUBUF's
address VGPRs by IDXEN/OFFEN and resource quad, SMEM's base pair or quad. A VALU reads EXEC. -/
@[expose] def Inst.access (i : Inst) : Access := Id.run do
  let fam := family i.enc.name
  let mut reads : List Reg := []
  let mut writes : List Reg := []
  let isVop := fam == "VOP1" || fam == "VOP2" || fam == "VOPC" || fam == "VOP3"
  if isVop then reads := reads ++ [.s 126, .s 127]
  for op in i.ie.operands do
    let k := (op.size + 31) / 32
    let regs : List Reg :=
      match op.field with
      | "" =>
        if op.type == "OPR_VCC" then [.s 106, .s 107]
        else if op.type == "OPR_EXEC" || op.type == "OPR_SDST_EXEC" then [.s 126, .s 127]
        else []
      | "LITERAL" => []
      | "VDST" => if op.type == "OPR_VGPR" then vregs (i.field "VDST") k
                  else if op.type == "OPR_EXEC" then [.s 126, .s 127]
                  else regsOfCode (i.field "VDST") k
      | "VSRC1" | "VSRC0" => vregs (i.field op.field) k
      | "VDATA" => vregs (i.field "VDATA") k
      | "ADDR" | "DATA" | "DATA0" | "DATA1" => vregs (i.field op.field) k
      | "VADDR" => vregs (i.field "VADDR") ((if i.field "IDXEN" == 1 then 1 else 0) + (if i.field "OFFEN" == 1 then 1 else 0))
      | "SRSRC" => sregs (4 * i.field "SRSRC") 4
      | "SBASE" => sregs (2 * i.field "SBASE") k
      | "SDATA" => sregs (i.field "SDATA") k
      | "SOFFSET" => let c := i.field "SOFFSET"; if c == 125 then [] else regsOfCode c 1
      | "SIMM16" => []
      | f => regsOfCode (i.field f) k
    if op.input then reads := reads ++ regs
    if op.output then writes := writes ++ regs
  return { reads := reads, writes := writes }

/-! ## 2. The counters -/

/-- The outstanding loads of a counter, oldest first; each the registers it will write. -/
abbrev Events := List (List Reg)

structure Pending where
  /-- vector memory loads (VM_CNT), returning in order -/
  vm : Events
  /-- scalar memory loads and LDS accesses (LGKM_CNT) -/
  lgkm : Events
  /-- an SMEM load is among them: the counter is then out of order (manual 4.4; SIInsertWaitcnts
  `counterOutOfOrder`), and only `lgkmcnt(0)` completes anything -/
  smem : Bool
  deriving Repr, DecidableEq

@[expose] def Pending.empty : Pending := { vm := [], lgkm := [], smem := false }

/-- `s_waitcnt` SIMM16 (manual 12.5): vmcnt `{[15:14],[3:0]}`, expcnt `[6:4]`, lgkmcnt `[13:8]`. -/
@[expose] def waitVm (simm : Nat) : Nat := (simm % 16) ||| (((simm >>> 14) % 4) <<< 4)
@[expose] def waitLgkm (simm : Nat) : Nat := (simm >>> 8) % 64

/-- The oldest events that await no register (LDS writes) are dropped: a wait of `k` retires the oldest
`n - k` events, and which of the register-carrying ones it retires does not depend on how many
register-less events precede them all. This keeps a loop's pending state finite. -/
def Events.trim (es : Events) : Events := es.dropWhile (·.isEmpty)

/-- A wait: all but the last `k` vector loads complete; of LGKM, all but the last `k` when only LDS reads
are outstanding (they return in order), and only at `lgkmcnt(0)` when a scalar load is among them. -/
def Pending.wait (p : Pending) (simm : Nat) : Pending :=
  let k := waitVm simm
  let vm := if k < p.vm.length then p.vm.drop (p.vm.length - k) else p.vm
  let kl := waitLgkm simm
  let lgkm := if kl == 0 then [] else if !p.smem && kl < p.lgkm.length then p.lgkm.drop (p.lgkm.length - kl) else p.lgkm
  { vm := vm, lgkm := Events.trim lgkm, smem := p.smem && kl != 0 }

/-- Join at a control-flow merge: events aligned from the most recent, registers unioned. -/
def joinEvents (a b : Events) : Events :=
  let n := max a.length b.length
  let pad (e : Events) : Events := List.replicate (n - e.length) [] ++ e
  (pad a).zipWith (fun x y => x ++ y.filter (fun r => !x.contains r)) (pad b)

def Pending.join (a b : Pending) : Pending :=
  { vm := joinEvents a.vm b.vm, lgkm := Events.trim (joinEvents a.lgkm b.lgkm), smem := a.smem || b.smem }

/-- A register still awaited by some event. -/
@[expose] def Events.hits (es : Events) (r : Reg) : Bool := es.any (·.contains r)

/-! ## 3. One instruction -/

@[expose] def isVmemLoad (i : Inst) : Bool := i.enc.name == "ENC_MUBUF" && i.name.startsWith "BUFFER_LOAD"
@[expose] def isVmemStore (i : Inst) : Bool := i.enc.name == "ENC_MUBUF" && i.name.startsWith "BUFFER_STORE"
@[expose] def isSmemLoad (i : Inst) : Bool := i.enc.name == "ENC_SMEM" && (i.name.startsWith "S_LOAD" || i.name.startsWith "S_BUFFER_LOAD")
@[expose] def isDsLoad (i : Inst) : Bool := i.enc.name == "ENC_DS" && i.name.startsWith "DS_READ"
@[expose] def isDsStore (i : Inst) : Bool := i.enc.name == "ENC_DS" && i.name.startsWith "DS_WRITE"

/-- Global and flat stores use VS_CNT, independently of VM_CNT. -/
def isGlobalOrFlatStore (i : Inst) : Bool :=
  (i.enc.name == "ENC_FLAT_GLBL" && i.name.startsWith "GLOBAL_STORE") ||
  (i.enc.name == "ENC_FLAT" && i.name.startsWith "FLAT_STORE")

/-- The families whose counters this module knows: scalar and vector ALU, SMEM loads, MUBUF loads and
stores, LDS reads/writes, and global/flat stores. Other memory families are refused. -/
def knownFamily (i : Inst) : Bool :=
  let fam := family i.enc.name
  fam == "SOP1" || fam == "SOP2" || fam == "SOPC" || fam == "SOPP" || fam == "SOPK" || fam == "VOP1" || fam == "VOP2"
    || fam == "VOPC" || fam == "VOP3" || isVmemLoad i || isVmemStore i || isSmemLoad i || isDsLoad i || isDsStore i || isGlobalOrFlatStore i

/-- Check one instruction against the pending loads, then issue it. -/
def stepPending (p : Pending) (i : Inst) : Except String Pending := do
  if !knownFamily i then throw s!"{i.name}: counters of this family are not modelled"
  if i.name == "S_WAITCNT" then return p.wait (i.field "SIMM16")
  let a := i.access
  for r in a.reads do
    match r with
    | .v _ =>
      if p.vm.hits r then throw s!"{i.name} reads {r} while a vector load to it is outstanding"
      if p.lgkm.hits r then throw s!"{i.name} reads {r} while an LDS read to it is outstanding"
    | .s _ => if p.lgkm.hits r then throw s!"{i.name} reads {r} while a scalar load to it is outstanding"
  for r in a.writes do
    match r with
    | .v _ =>
      if p.vm.hits r && !isVmemLoad i then throw s!"{i.name} writes {r} while a vector load to it is outstanding"
      if p.lgkm.hits r && !isDsLoad i then throw s!"{i.name} writes {r} while an LDS read to it is outstanding"
    | .s _ => if p.lgkm.hits r then throw s!"{i.name} writes {r} while a scalar load to it is outstanding"
  if isVmemLoad i then return { p with vm := p.vm ++ [a.writes] }
  if isSmemLoad i then return { p with lgkm := p.lgkm ++ [a.writes], smem := true }
  if isDsLoad i then return { p with lgkm := p.lgkm ++ [a.writes] }
  -- an LDS write is an LGKM event too (manual 4.4: decremented "when data is written"; LLVM scores every
  -- DS access as `LDS_ACCESS`): it awaits no register, but a later `lgkmcnt(k)` counts it
  if isDsStore i then return { p with lgkm := Events.trim (p.lgkm ++ [[]]) }
  return p

/-! ## 4. The program, as a dataflow over its basic blocks -/

def isBranch (i : Inst) : Bool := i.inst.isBranch
def branchTarget (pc : Nat) (i : Inst) : Nat := (Int.ofNat (pc + i.words.length) + signed16 (i.field "SIMM16")).toNat
def isUncondBranch (i : Inst) : Bool := i.name == "S_BRANCH"

/-- The pending state at the end of a straight run from `pc` to the next branch, terminator or
`stop` (the next leader), with the pc reached. -/
partial def runBlock (prog : Program) (leaders : List Nat) (pc : Nat) (p : Pending) : Except String (Pending × Nat × Option Inst) := do
  match prog[pc]? with
  | none => throw s!"dword {pc}: outside the program"
  | some none => throw s!"dword {pc}: inside an instruction"
  | some (some i) =>
    let p' ← match stepPending p i with
      | .ok q => pure q
      | .error e => throw s!"dword {pc}: {e}"
    let next := pc + i.words.length
    if isBranch i || i.inst.isTerminator then return (p', next, some i)
    if leaders.contains next then return (p', next, none)
    runBlock prog leaders next p'

/-- Every instruction's dword index. -/
def instructionPcs (prog : Program) : List Nat :=
  (List.range prog.size).filter fun d => (prog[d]?.getD none).isSome

/-- The block leaders: dword 0, every branch target, every dword after a branch. -/
def leadersOf (prog : Program) : List Nat :=
  let ls := (instructionPcs prog).foldl (fun acc pc =>
    match prog[pc]! with
    | some i => if isBranch i then acc ++ [branchTarget pc i, pc + i.words.length] else acc
    | none => acc) [0]
  ls.eraseDups

/-- The fixpoint: the pending state at every leader, joined over its predecessors, until nothing
changes (bounded; a program with more iterations than blocks times the counter width is refused). -/
def checkWaitcnt (prog : Program) : Except String Unit := do
  let leaders := leadersOf prog
  let mut entry : List (Nat × Pending) := [(0, Pending.empty)]
  let mut work : List Nat := [0]
  let mut rounds := 0
  while !work.isEmpty do
    rounds := rounds + 1
    if rounds > 64 * leaders.length + 64 then throw "the waitcnt dataflow did not converge"
    let pc := work.head!
    work := work.tail
    let p := (entry.find? (·.1 == pc)).map (·.2) |>.getD Pending.empty
    let (pOut, next, last) ← runBlock prog leaders pc p
    let succs : List Nat :=
      match last with
      | some i => if i.inst.isTerminator then [] else if isUncondBranch i then [branchTarget (next - i.words.length) i]
                  else [branchTarget (next - i.words.length) i, next]
      | none => [next]
    for s in succs do
      let old := (entry.find? (·.1 == s)).map (·.2)
      let new := match old with | some q => q.join pOut | none => pOut
      if old != some new then
        entry := (s, new) :: entry.filter (·.1 != s)
        if !work.contains s then work := work ++ [s]
  pure ()

/-- Every stage of a dump (`hardware/gpu/isa/<g>.txt`); with `nop`, the instruction at that stage and
index is replaced by `s_nop 0` first (the gate's planted fault: a removed wait). -/
def checkWaitcntDumpReport (isa : String) (nop : Option (Nat × Nat)) : Except String String := do
  let mut dumps := parseDump isa
  if let some (st, ins) := nop then
    let some block := dumps[st]? | throw s!"nop: no stage {st}"
    let some ws := block[ins]? | throw s!"nop: no instruction {ins} in stage {st}"
    if ws.size != 1 then throw s!"nop: instruction {ins} of stage {st} is not one dword"
    dumps := dumps.set! st (block.set! ins #[0xbf800000])
  let mut n := 0
  for (ws, k) in dumps.zipIdx do
    let prog ← match decodeProgram (ws.flatMap id) with | .ok p => pure p | .error e => throw s!"stage {k}: {e}"
    match checkWaitcnt prog with
    | .ok () => n := n + 1
    | .error e => throw s!"stage {k}: {e}"
  pure s!"{n} stages: every load is waited for before its destination is touched"

def checkWaitcntDump (isa : String) : Bool := (checkWaitcntDumpReport isa none).toBool

/-! ## 5. Vector-store completion over every reachable CFG path -/

structure VsPending where
  vsAll : Nat := 0
  vsGlobal : Nat := 0
  deriving BEq, Repr

def VsPending.join (a b : VsPending) : VsPending :=
  ⟨max a.vsAll b.vsAll, max a.vsGlobal b.vsGlobal⟩

/-- Conservative supported operand domain: RDNA2 null SDST and an unreserved six-bit threshold. -/
@[expose] def validVscntOperands (i : Inst) : Bool :=
  i.field "SDST" == 125 && i.field "SIMM16" < 64

def stepVscnt (requireAllStoresOnExit : Bool) (p : VsPending) (i : Inst) : Except String VsPending := do
  if !knownFamily i then throw s!"{i.name}: counters of this family are not modelled"
  if (i.inst.isBranch && i.enc.name != "ENC_SOPP") ||
      ["S_CALL_B64", "S_RFE_B64", "S_TRAP", "S_CODE_END"].contains i.name ||
      (i.inst.isTerminator && i.name != "S_ENDPGM") then
    throw s!"{i.name}: unsupported control flow in vscnt analysis"
  if i.name == "S_BARRIER" && p.vsAll != 0 then
    throw "unawaited vector store before barrier"
  if i.inst.isTerminator then
    if p.vsGlobal != 0 then throw "unawaited global/flat store before kernel exit"
    if requireAllStoresOnExit && p.vsAll != 0 then
      throw "unawaited vector store before block-kernel exit"
  if i.name == "S_WAITCNT_VSCNT" then
    if !validVscntOperands i then throw "S_WAITCNT_VSCNT: requires null SDST and SIMM16 < 64"
    let k := i.field "SIMM16"
    return ⟨min p.vsAll k, min p.vsGlobal k⟩
  if isGlobalOrFlatStore i then return ⟨min 63 (p.vsAll + 1), min 63 (p.vsGlobal + 1)⟩
  if isVmemStore i then return { p with vsAll := min 63 (p.vsAll + 1) }
  return p

/-- A successful strict boundary check forces the incoming all-store count to zero,
regardless of the outgoing state or the instruction's other fields. -/
theorem stepVscnt_boundary_zero (p q : VsPending) (i : Inst)
    (boundary : i.name = "S_BARRIER" ∨ i.inst.isTerminator = true)
    (accepted : stepVscnt true p i = .ok q) : p.vsAll = 0 := by
  by_cases dirty : p.vsAll = 0
  · exact dirty
  · rcases boundary with barrier | exit
    all_goals simp [stepVscnt, *, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
    all_goals repeat' (split at accepted <;> simp_all [bind, Except.bind, throw, throwThe, MonadExceptOf.throw])


/-- Structural fuel also refuses malformed zero-width instructions and fallthrough outside code. -/
def runVscntBlock (strict : Bool) (prog : Program) (leaders : List Nat) :
    Nat → Nat → VsPending → Except String (VsPending × Nat × Option Inst)
  | 0, _, _ => .error "vscnt block exceeded program size"
  | fuel + 1, pc, p => do
    let some (some i) := prog[pc]? | throw s!"dword {pc}: not an instruction"
    let p' ← stepVscnt strict p i
    let next := pc + i.words.length
    if isBranch i || i.inst.isTerminator then return (p', next, some i)
    if leaders.contains next then return (p', next, none)
    runVscntBlock strict prog leaders fuel next p'

/-- Monotone componentwise joins. Each reachable entry can increase at most 126 times;
exhaustion refuses, never accepts an unfinished analysis. -/
def vscntFixpoint (strict : Bool) (prog : Program) (leaders : List Nat) :
    Nat → List (Nat × VsPending) → List Nat → Except String Unit
  | _, _, [] => .ok ()
  | 0, _, _ :: _ => .error "the vscnt dataflow did not converge"
  | fuel + 1, entry, pc :: rest => do
    let p := (entry.find? (·.1 == pc)).map (·.2) |>.getD {}
    let (pOut, next, last) ← runVscntBlock strict prog leaders (prog.size + 1) pc p
    let succs : List Nat := match last with
      | some i => if i.inst.isTerminator then []
        else if isUncondBranch i then [branchTarget (next - i.words.length) i]
        else [branchTarget (next - i.words.length) i, next]
      | none => [next]
    let mut entries := entry
    let mut work := rest
    for s in succs do
      let old := (entries.find? (·.1 == s)).map (·.2)
      let new := match old with | some q => q.join pOut | none => pOut
      if old != some new then
        entries := (s, new) :: entries.filter (·.1 != s)
        if !work.contains s then work := work ++ [s]
    vscntFixpoint strict prog leaders fuel entries work

def checkVscntProg (requireAllStoresOnExit : Bool) (prog : Program) : Except String Unit :=
  let leaders := leadersOf prog
  vscntFixpoint requireAllStoresOnExit prog leaders (128 * leaders.length + 1) [(0, {})] [0]

def checkVscntDumpReport (isa : String) (requireAllStoresOnExit : Bool := false) : Except String String := do
  let dumps := parseDump isa
  if dumps.isEmpty then throw "no stages in vscnt dump"
  for (ws, k) in dumps.zipIdx do
    let prog ← match decodeProgram (ws.flatMap id) with
      | .ok p => pure p
      | .error e => throw s!"stage {k}: {e}"
    match checkVscntProg requireAllStoresOnExit prog with
    | .ok () => pure ()
    | .error e => throw s!"stage {k}: {e}"
  pure s!"{dumps.size} stages: vector stores completed at required boundaries"

def checkVscntDump (isa : String) : Bool := (checkVscntDumpReport isa false).toBool

def checkVscntBlockDumpReport (isa : String) : Except String String := checkVscntDumpReport isa true

def checkVscntBlockDump (isa : String) : Bool := (checkVscntBlockDumpReport isa).toBool

end Obend.Hardware.Gpu.Rdna2
