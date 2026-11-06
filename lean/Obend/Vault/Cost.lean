module


/-!
# Obend.Vault.Cost — what a command cost, said by the binary

Every byte a vault or ledger command reads or writes goes through the functions here, which count it;
recovery counts the records it replays and the checkpoint it reads. With `OBEND_COST` set, the binary
says the counts after every command, one line:

    cost: read B bytes, wrote W bytes, T ms, replayed R records, checkpoint C bytes [COMMAND]
    cost phases: read A ms, judge J ms, land L ms, write W ms, other O ms [COMMAND]

to the standard error when `OBEND_COST` is `1`, else appended to the file it names
(`lean/tests/vault/walkthrough.py` collects them into `COST.tsv` and compares each step against
`COST.baseline.tsv`).
-/

public section

namespace Obend.Vault.Cost

set_option autoImplicit false

structure Counts where
  read : Nat := 0
  wrote : Nat := 0
  replayed : Nat := 0
  checkpoint : Nat := 0
  /-- milliseconds by phase: `read` (the log, the checkpoint, the vault's files), `judge` (the step),
  `land` (the world's commitment and the record appended), `write` (files, exports, checkpoint) -/
  phases : List (String × Nat) := []
  /-- the phase running now and since when (a phase inside another pauses it: each millisecond is
  counted to one phase) -/
  current : Option (String × Nat) := none
deriving Inhabited, Nonempty

initialize counts : IO.Ref Counts ← IO.mkRef {}

def addRead (n : Nat) : IO Unit := counts.modify fun c => { c with read := c.read + n }
def addWrote (n : Nat) : IO Unit := counts.modify fun c => { c with wrote := c.wrote + n }
def addReplayed (n : Nat) : IO Unit := counts.modify fun c => { c with replayed := c.replayed + n }
def addCheckpoint (n : Nat) : IO Unit := counts.modify fun c => { c with checkpoint := c.checkpoint + n }

def addPhase (name : String) (ms : Nat) : IO Unit := counts.modify fun c =>
  { c with phases := match c.phases.find? (·.1 == name) with
    | some _ => c.phases.map fun (k, v) => if k == name then (k, v + ms) else (k, v)
    | none => c.phases ++ [(name, ms)] }

/-- Run `act`, its time counted to the phase `name` (not to the phase it runs inside). -/
def phase {α : Type} (name : String) (act : IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let outer := (← counts.get).current
  if let some (n, s) := outer then addPhase n (t0 - s)
  counts.modify fun c => { c with current := some (name, t0) }
  try act finally
    let t1 ← IO.monoMsNow
    if let some (n, s) := (← counts.get).current then addPhase n (t1 - s)
    counts.modify fun c => { c with current := outer.map fun (n, _) => (n, t1) }

/-- A pure computation, run when this action runs (not before it: it is not inlined, so the
computation is not moved out of the phase that times it). -/
@[noinline] def compute {α : Type} (f : Unit → α) : IO α := pure (f ())

def readBinFile (f : System.FilePath) : IO ByteArray := do
  let b ← IO.FS.readBinFile f
  addRead b.size
  return b

def readFile (f : System.FilePath) : IO String := do
  let s ← IO.FS.readFile f
  addRead s.utf8ByteSize
  return s

def writeBinFile (f : System.FilePath) (b : ByteArray) : IO Unit := do
  IO.FS.writeBinFile f b
  addWrote b.size

def writeFile (f : System.FilePath) (s : String) : IO Unit := do
  IO.FS.writeFile f s
  addWrote s.utf8ByteSize

/-- Write to a handle, counted. -/
def write (h : IO.FS.Handle) (b : ByteArray) : IO Unit := do
  h.write b
  addWrote b.size

def line (c : Counts) (ms : Nat) (cmd : String) : String :=
  "cost: read " ++ toString c.read ++ " bytes, wrote " ++ toString c.wrote ++ " bytes, " ++ toString ms ++
    " ms, replayed " ++ toString c.replayed ++ " records, checkpoint " ++ toString c.checkpoint ++ " bytes [" ++
    cmd ++ "]"

/-- Say what the command cost, when `OBEND_COST` asks. -/
def emit (ms : Nat) (cmd : String) : IO Unit := do
  let some dest ← IO.getEnv "OBEND_COST" | return
  if dest.isEmpty then return
  let c ← counts.get
  let l := line c ms cmd
  let of k := (c.phases.find? (·.1 == k)).map (·.2) |>.getD 0
  let named := ["read", "judge", "land", "write"]
  let ps := named.map (fun k => k ++ " " ++ toString (of k) ++ " ms") ++
    ["other " ++ toString (ms - (named.map of).sum) ++ " ms"]
  let ls := [l, "cost phases: " ++ ", ".intercalate ps ++ " [" ++ cmd ++ "]"]
  if dest == "1" then for l in ls do IO.eprintln l
  else
    let h ← IO.FS.Handle.mk dest .append
    for l in ls do h.putStrLn l
    h.flush

end Obend.Vault.Cost

end
