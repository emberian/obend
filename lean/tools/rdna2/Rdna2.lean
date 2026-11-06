/-
# obend-rdna2 — the RDNA2 decoder and model on RADV's dumps (rung G2)

    obend-rdna2 decode ISA.txt         every instruction of hardware/gpu/isa/<graph>.txt, decoded from its
                                       machine code and written in LLVM's syntax, one per line, in order
                                       (`hardware/gpu/isa_check.sh` diffs this against `llvm-mc --disassemble`)
    obend-rdna2 flip ISA.txt           for every instruction, every bit of its machine code flipped once: the
                                       decoding must change or fail unless the bit lies in no field of the
                                       encoding (a bit the specification does not name); exits 1 otherwise
    obend-rdna2 waitcnt ISA.txt [--nop STAGE:INSTR]
                                       every stage's waits are sufficient (Obend.Hardware.Gpu.Rdna2.Waitcnt);
                                       with --nop, that instruction (an s_waitcnt) is replaced by s_nop 0
                                       first and the check must refuse (isa_check.sh stage 6)
    obend-rdna2 gem5 VECTORS.tsv       every row of hardware/gpu/rdna2/gem5_vectors.tsv replayed through the
                                       model's step and compared register by register (isa_check.sh stage 5)
    obend-rdna2 run GRAPH_DIR [--flip STAGE:INSTR:BIT]
                                       the model: every stage's program from GRAPH_DIR/../../isa/<graph>.txt
                                       run on every vector of expected.tsv (Obend.Hardware.Gpu.Rdna2.Check);
                                       with --flip, one bit of one instruction is flipped first and the
                                       comparison must fail (the gate's tooth)
-/
import Obend.Hardware.Gpu.Rdna2.Decode
import Obend.Hardware.Gpu.Rdna2.Check
import Obend.Hardware.Gpu.Rdna2.Waitcnt

open Obend.Hardware.Gpu.Rdna2

def usage : String :=
  "obend-rdna2 decode ISA.txt | flip ISA.txt | waitcnt ISA.txt [--nop STAGE:INSTR] | gem5 VECTORS.tsv | run GRAPH_DIR [--flip STAGE:INSTR:BIT]"

/-- `(text, words)` for every instruction line (`\t<text>\t; <hex>...`) of a dump, in order. -/
def instructionLines (s : String) : List (String × List UInt32) :=
  s.splitOn "\n" |>.filterMap fun ln =>
    if ln.startsWith "\t" then
      match ln.splitOn "\t; " with
      | [text, hexes] =>
        some ((text.drop 1).toString, (hexes.splitOn " ").filterMap fun h =>
          if h.isEmpty then none else some (UInt32.ofNat (hexToNat h)))
      | _ => none
    else none
where
  hexToNat (h : String) : Nat := h.foldl (fun acc c => acc * 16 + (c.toNat - (if c.isDigit then '0'.toNat else 'a'.toNat - 10))) 0

def renderWords (ws : List UInt32) : String :=
  match decodeInst ws with
  | none => "<undecoded>"
  | some (i, k) =>
    if k != ws.length then s!"<width {k} of {ws.length} dwords: {i.name}>"
    else (i.render).getD s!"<unrendered {i.name} in {i.enc.name}>"

def cmdDecode (path : String) : IO UInt32 := do
  let s ← IO.FS.readFile path
  for (_, ws) in instructionLines s do
    IO.println (renderWords ws)
  return 0

/-- Is bit `b` (of the whole instruction, first dword lowest) inside some field of `e`? -/
def inSomeField (e : Encoding) (b : Nat) : Bool :=
  e.fields.any fun f => f.ranges.any fun r => r.offset ≤ b && b < r.offset + r.count

def cmdFlip (path : String) : IO UInt32 := do
  let s ← IO.FS.readFile path
  let mut changed := 0
  let mut failed := 0
  let mut unnamed := 0
  let mut bad : List String := []
  for (text, ws) in instructionLines s do
    let some (orig, _) := decodeInst ws | bad := bad ++ [s!"undecoded: {text}"]; continue
    let origR := orig.render
    for w in [0:ws.length] do
      for b in [0:32] do
        let ws' := ws.set w (ws[w]! ^^^ (1 <<< b.toUInt32))
        let bit := 32 * w + b
        match decodeInst ws' with
        | none => failed := failed + 1
        | some (i', k') =>
          if k' != ws.length || i'.fields != orig.fields || i'.inst.name != orig.inst.name || i'.enc.name != orig.enc.name || i'.render != origR then
            changed := changed + 1
          else if !inSomeField orig.enc bit then
            unnamed := unnamed + 1
          else
            bad := bad ++ [s!"bit {bit} of `{text}` ({orig.enc.name}) flipped and nothing changed"]
  IO.println s!"flip: {changed} bit flips changed the decoding, {failed} made it fail, {unnamed} lay in no field of their encoding"
  for b in bad.take 20 do IO.eprintln s!"[FAIL] {b}"
  return if bad.isEmpty then 0 else 1

def cmdRun (dir : String) (flip : Option String) : IO UInt32 := do
  let graph := (System.FilePath.mk dir).fileName.getD dir
  let isaPath := (System.FilePath.mk dir) / ".." / ".." / "isa" / (graph ++ ".txt")
  let isa ← IO.FS.readFile isaPath
  let plan ← IO.FS.readFile ((System.FilePath.mk dir) / "plan.json")
  let expected ← IO.FS.readFile ((System.FilePath.mk dir) / "expected.tsv")
  let flipSpec : Option (Nat × Nat × Nat) := flip.bind fun f =>
    match f.splitOn ":" |>.map String.toNat? with
    | [some a, some b, some c] => some (a, b, c)
    | _ => none
  match checkGraphReport isa plan expected flipSpec with
  | .ok report =>
    IO.println s!"{graph}: {report}"
    return if flipSpec.isSome then 1 else 0
  | .error e =>
    if flipSpec.isSome then
      IO.println s!"{graph}: planted flip {flip.getD ""} caught: {e}"
      return 0
    IO.eprintln s!"[FAIL] {graph}: {e}"
    return 1

def cmdGem5 (path : String) : IO UInt32 := do
  let s ← IO.FS.readFile path
  match checkGem5Report s with
  | .ok r => IO.println r; return 0
  | .error e => IO.eprintln s!"[FAIL] {e}"; return 1

def cmdWaitcnt (path : String) (nop : Option String) : IO UInt32 := do
  let s ← IO.FS.readFile path
  let spec : Option (Nat × Nat) := nop.bind fun f =>
    match f.splitOn ":" |>.map String.toNat? with
    | [some a, some b] => some (a, b)
    | _ => none
  let graph := (System.FilePath.mk path).fileStem.getD path
  match checkWaitcntDumpReport s spec with
  | .ok r =>
    IO.println s!"{graph}: {r}"
    return if spec.isSome then 1 else 0
  | .error e =>
    if spec.isSome then
      IO.println s!"{graph}: wait replaced by s_nop at {nop.getD ""} refused: {e}"
      return 0
    IO.eprintln s!"[FAIL] {graph}: {e}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["waitcnt", p] => cmdWaitcnt p none
  | ["waitcnt", p, "--nop", f] => cmdWaitcnt p (some f)
  | ["gem5", p] => cmdGem5 p
  | ["decode", p] => cmdDecode p
  | ["flip", p] => cmdFlip p
  | ["run", d] => cmdRun d none
  | ["run", d, "--flip", f] => cmdRun d (some f)
  | _ => IO.eprintln usage; return 2
