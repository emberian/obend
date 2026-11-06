module


/-!
# Obend.Vault.Cost — what a command cost, said by the binary

Every byte a vault or ledger command reads or writes goes through the functions here, which count it;
recovery counts the records it replays and the checkpoint it reads. With `OBEND_COST` set, the binary
says the counts after every command, one line:

    cost: read B bytes, wrote W bytes, T ms, replayed R records, checkpoint C bytes [COMMAND]

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
deriving Inhabited, Nonempty

initialize counts : IO.Ref Counts ← IO.mkRef {}

def addRead (n : Nat) : IO Unit := counts.modify fun c => { c with read := c.read + n }
def addWrote (n : Nat) : IO Unit := counts.modify fun c => { c with wrote := c.wrote + n }
def addReplayed (n : Nat) : IO Unit := counts.modify fun c => { c with replayed := c.replayed + n }
def addCheckpoint (n : Nat) : IO Unit := counts.modify fun c => { c with checkpoint := c.checkpoint + n }

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
  let l := line (← counts.get) ms cmd
  if dest == "1" then IO.eprintln l
  else
    let h ← IO.FS.Handle.mk dest .append
    h.putStrLn l
    h.flush

end Obend.Vault.Cost

end
