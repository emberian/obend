/-
# Obend.Hardware.Gpu.Rdna2.Waitcnt — are the dump's `s_waitcnt`s sufficient?

The model of `Semantics` completes every memory access when it issues, so a program that read a load's
destination before waiting for it would compute the right answer there and a stale one on the device.
This module closes that gap statically: it walks a decoded program tracking the outstanding loads and
refuses it if any instruction reads or writes a register that an outstanding load still writes.

The counters are the manual's (RDNA 2 ISA, 4.4 "Data Dependency Resolution"): `VM_CNT` counts vector
memory loads, which return in issue order, so `s_waitcnt vmcnt(k)` guarantees all but the last `k`
have completed; `LGKM_CNT` counts scalar memory loads, which "can return out-of-order (in which case
only S_WAITCNT 0 is the only legitimate value)" (4.4, 7.3), so only `lgkmcnt(0)` completes anything
here; `VS_CNT` counts stores, whose completion no register depends on; `EXP_CNT` counts exports, of
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

`hardware/gpu/isa_check.sh` stage 6 runs `checkWaitcntDump` on every dump and requires that a dump with
one `s_waitcnt` replaced by `s_nop 0` (same width, so no branch moves) is refused.
-/
module
public import Obend.Hardware.Gpu.Rdna2.Check
@[expose] public section

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
def regsOfCode (code k : Nat) : List Reg :=
  if code ≤ 107 || code == 124 || code == 126 || code == 127 then (List.range k).map fun j => .s (code + j)
  else if 256 ≤ code && code ≤ 511 then (List.range k).map fun j => .v (code - 256 + j)
  else []

def vregs (n k : Nat) : List Reg := (List.range k).map fun j => .v (n + j)
def sregs (n k : Nat) : List Reg := (List.range k).map fun j => .s (n + j)

structure Access where
  reads : List Reg
  writes : List Reg
  deriving Repr

/-- From the XML's operand list (field, type, size, Input/Output) and the decoded fields: VGPR fields by
number, source fields by code, the implicit VCC of VOP2/VOPC, EXEC for V_CMPX and the branches, MUBUF's
address VGPRs by IDXEN/OFFEN and resource quad, SMEM's base pair or quad. A VALU reads EXEC. -/
def Inst.access (i : Inst) : Access := Id.run do
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
  /-- scalar memory loads (LGKM_CNT), returning out of order -/
  lgkm : Events
  deriving Repr, DecidableEq

def Pending.empty : Pending := { vm := [], lgkm := [] }

/-- `s_waitcnt` SIMM16 (manual 12.5): vmcnt `{[15:14],[3:0]}`, expcnt `[6:4]`, lgkmcnt `[13:8]`. -/
def waitVm (simm : Nat) : Nat := (simm % 16) ||| (((simm >>> 14) % 4) <<< 4)
def waitLgkm (simm : Nat) : Nat := (simm >>> 8) % 64

/-- A wait: all but the last `k` vector loads complete; scalar loads complete only for `lgkmcnt(0)`. -/
def Pending.wait (p : Pending) (simm : Nat) : Pending :=
  let k := waitVm simm
  let vm := if k < p.vm.length then p.vm.drop (p.vm.length - k) else p.vm
  let lgkm := if waitLgkm simm == 0 then [] else p.lgkm
  { vm := vm, lgkm := lgkm }

/-- Join at a control-flow merge: events aligned from the most recent, registers unioned. -/
def joinEvents (a b : Events) : Events :=
  let n := max a.length b.length
  let pad (e : Events) : Events := List.replicate (n - e.length) [] ++ e
  (pad a).zipWith (fun x y => x ++ y.filter (fun r => !x.contains r)) (pad b)

def Pending.join (a b : Pending) : Pending := { vm := joinEvents a.vm b.vm, lgkm := joinEvents a.lgkm b.lgkm }

/-- A register still awaited by some event. -/
def Events.hits (es : Events) (r : Reg) : Bool := es.any (·.contains r)

/-! ## 3. One instruction -/

def isVmemLoad (i : Inst) : Bool := i.enc.name == "ENC_MUBUF" && i.name.startsWith "BUFFER_LOAD"
def isVmemStore (i : Inst) : Bool := i.enc.name == "ENC_MUBUF" && i.name.startsWith "BUFFER_STORE"
def isSmemLoad (i : Inst) : Bool := i.enc.name == "ENC_SMEM" && (i.name.startsWith "S_LOAD" || i.name.startsWith "S_BUFFER_LOAD")

/-- The families whose counters this module knows: scalar and vector ALU, SMEM loads, MUBUF loads and
stores. Anything else (LDS, GDS, exports, images, flat, messages) is refused. -/
def knownFamily (i : Inst) : Bool :=
  let fam := family i.enc.name
  fam == "SOP1" || fam == "SOP2" || fam == "SOPC" || fam == "SOPP" || fam == "SOPK" || fam == "VOP1" || fam == "VOP2"
    || fam == "VOPC" || fam == "VOP3" || isVmemLoad i || isVmemStore i || isSmemLoad i

/-- Check one instruction against the pending loads, then issue it. -/
def stepPending (p : Pending) (i : Inst) : Except String Pending := do
  if !knownFamily i then throw s!"{i.name}: counters of this family are not modelled"
  if i.name == "S_WAITCNT" then return p.wait (i.field "SIMM16")
  let a := i.access
  for r in a.reads do
    match r with
    | .v _ => if p.vm.hits r then throw s!"{i.name} reads {r} while a vector load to it is outstanding"
    | .s _ => if p.lgkm.hits r then throw s!"{i.name} reads {r} while a scalar load to it is outstanding"
  for r in a.writes do
    match r with
    | .v _ => if p.vm.hits r && !isVmemLoad i then throw s!"{i.name} writes {r} while a vector load to it is outstanding"
    | .s _ => if p.lgkm.hits r then throw s!"{i.name} writes {r} while a scalar load to it is outstanding"
  if isVmemLoad i then return { p with vm := p.vm ++ [a.writes] }
  if isSmemLoad i then return { p with lgkm := p.lgkm ++ [a.writes] }
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

end Obend.Hardware.Gpu.Rdna2
