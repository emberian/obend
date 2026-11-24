module
/- The executable adapters; public imports are restricted to the vault census contract. -/
public import Obend.Core.Packet
public import Obend.Elab.Gate
public import Obend.Core.Machine
public import Obend.Core.MachineFast
public import Obend.Spec.Capture
public import Obend.Spec.Preview
public import Obend.Vault.Cli
import Obend.Vault.BranchCli
public import Obend.Spec.Workspace
import Obend.Receipt.Cli
public import Obend.Logic.Receipt
import Obend.Leaf.Specialize
import Obend.Analysis.Cli
import Obend.Ledger.Cli
import Obend.Hardware.Cli
import Obend.Lower.Cli
import Obend.Judge.GenealogyCli

import Obend.Law.AmendCli
import Obend.Polis.GrainCustodyHost
import Obend.Crypto.DarkBazaar
import Obend.Crypto.ThresholdHashMpc
import Obend.Crypto.PqHashSignatures
import Obend.Analysis.NonlinearPdeCli
import Obend.FFI.Bridge
import Obend.FFI.BridgeTypes
import Obend.Doc.WorkbookEngine
import Obend.Codec.Hex
import Obend.Leaf.BytecodeRegisterJit
import Lean.Data.Json

open Lean (Json toJson)
open Obend.Core
open Obend.Spec.FrontEnd
open Obend.Spec.Capture
open Obend.Spec.Preview

def usage : String :=
  "usage: obend amend live|trace|zk-prove|zk-verify|zk-bench|zk-tamper-test … | custody init|prepare|reopen|event …\n" ++
  "       obend bazaar clear … | mpc sign|verify … | pde check|solve … | notebook eval|project|verify …\n" ++
  "       obend run/run-core … [--jit|--jit=cc] [--emit-c99 FILE]\n" ++
  "       obend check FILE.obend [ENTRY] | obend run FILE.obend ENTRY [ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]\n" ++
  "       obend check --package PACKAGE.json [ENTRY] | obend run --package PACKAGE.json [ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]\n" ++
  "       obend check DIR [ENTRY] | obend run DIR ENTRY …   (every .obend file of DIR, in name order, as one package;\n" ++
  "             a DIR holding workspace.json or package.json is read through it; PACKAGE may replace --package PACKAGE below)\n" ++
  "       obend judge --package SPEC OLD_JSON NEW_JSON   (a write of the declared state judged by every law: a workspace's packages\n" ++
  "             in precedence order, or one package's, its imported modules' laws named Module.NAME)\n" ++
  "       obend admit --package WORKSPACE.json TURN.json          (a recorded turn re-derived at the workspace's records)\n" ++
  "       obend identity | parse FILE.obend | capture PACKAGE_SPEC NEW_DIR [--objective-edition-1]\n" ++
  "             | elaborate CAPTURE PREFIX [ARGS] [PROJECTIONS] [LIMITS] [application|definition] | preview REQUEST NEW_DIR | batch JOBS OUT\n" ++
  "       obend check-core FILE.json | obend run-core FILE.json [--ticks N] [--heap N] [--stack N]\n" ++
  "       obend open [DIR] | status [PAGE] | merge OTHER_DIR | member add NAME --grant VERB:PATTERN… | member list\n" ++
  "             | post PAGE FILE --as NAME | select PAGE SECTION CANDIDATE [--as NAME] | recite PAGE [--as NAME]\n" ++
  "             | create --from KIND PAGE   [-C DIR]\n" ++
  "       obend reasons observe NAME (--line FILE:N | TEXT) | assume NAME | withdraw NAME | explain NAME CONCL --if P… [--unless D…]\n" ++
  "             | defeat EXPLANATION --by ATOM | propose ACTION --because CONCL | admit ACTION | status | why ATOM   [-C DIR]\n" ++
  "       obend ledger post DOC [--period N] | ledger reverse P-NNNN [--period N] | ledger close N | ledger status | ledger root\n" ++
  "             | report trial-balance P [--out FILE]   (a vault with register/_kind.md; merge stitches its register)\n" ++
  "       obend check --obligations --package PACKAGE.json --object ENTRY [--receipts DIR]\n" ++
  "       obend prove --package PACKAGE.json SPEC.CLAIM --object ENTRY --out RECEIPT.json [--ground N,N,…]\n" ++
  "       obend ground --package PACKAGE.json ENTRY EXPECTED_NAT\n" ++
  "       obend emit --package PACKAGE.json --object ENTRY --out BOOK.json [--call MEMBER NAT]\n" ++
  "       obend specialize --package PACKAGE.json --object ENTRY --book BOOK.json [--call MEMBER NAT]\n" ++
  "       obend verify RECEIPT.json [--prev PREV.json] [--root ROOT] | obend lrat CNF PROOF\n" ++
  "       obend genealogy genesis JUDGE.json [--store CELL=N]… | genealogy show | genealogy succeed JUDGE.json [--lob TRUST]…\n" ++
  "             | genealogy act (write CELL N | revert | forget) [--as NAME] [--says TEXT]   (in a directory holding genealogy.json)\n" ++
  "       obend analyze impact CELL@PIN --world PATH [--turn TURN.json] [--out RECEIPT.json] | analyze replay PAGE@FILE --world DIR\n" ++
  "       obend receipt identity N CERT.lrat OUT.json [--prev PREV.json] | receipt negotiation OUT.json [--full] [--prev PREV.json] | receipt cnf N OUT.cnf\n" ++
  "       obend verilate <FILE.obend> [--top NAME] [--vectors N] [--cycles C] [--vcd OUT.vcd]"
def usage64 : IO UInt32 := do IO.eprintln usage; return 64

/-! ## The typed-core packet path (lane A) -/

/-- Expose the package knot and entry application before testing the scalar fragment. -/
def jitTerm : Nat → Obend.Core.Term.Term → Option Obend.Core.Term.Term
  | 0, _ => none
  | fuel + 1, t =>
    let clean := Obend.Leaf.BytecodeRegisterJit.specializeDictTerm 8 t
    if Obend.Leaf.BytecodeRegisterJit.checkRangeSafeBytecode [] clean then some clean
    else (Obend.Law.step? clean).bind (jitTerm fuel)

/-- Run the checked scalar fragment; absence is the ordinary demand-machine fallback. -/
def runJit (t : Obend.Core.Term.Term) (mode : String) (emit : Option String) : IO (Option Nat) := do
  if mode.isEmpty && emit.isNone then return none
  let compiled := (jitTerm 64 t).bind (Obend.Leaf.BytecodeRegisterJit.compileExprToBytecode 0 [] 0)
  let some (code, regs, fuel) := compiled | do
    if emit.isSome then throw (IO.userError "outside the range-safe scalar/register fragment; cannot emit C99")
    return none
  let c := Obend.Leaf.BytecodeRegisterJit.emitRegisterBytecodeC99 code
  if let some p := emit then IO.FS.writeFile p c
  if mode != "cc" then
    return (Obend.Leaf.BytecodeRegisterJit.execBytecode code (Array.replicate regs 0) fuel).map UInt64.toNat
  let tmp ← IO.Process.output { cmd := "mktemp", args := #["-d", "/tmp/obend-s2d-jit-XXXXXXXX"] }
  if tmp.exitCode != 0 then throw (IO.userError tmp.stderr)
  let dir := tmp.stdout.trimAscii.toString
  try
    let src := dir ++ "/run.c"
    let bin := dir ++ "/run"
    let harness := "\n#include <stdio.h>\n#include <inttypes.h>\nint main(void) { int ok = 0; uint64_t regs[" ++ toString (max regs 1) ++ "] = {0}; " ++
      "uint64_t v = obend_bytecode_jit_run(regs," ++ toString regs ++ "," ++ toString fuel ++ ",&ok); " ++
      "if (!ok) return 3; printf(\"%\" PRIu64 \"\\n\", v); return 0; }\n"
    IO.FS.writeFile src (c ++ harness)
    let cc ← IO.Process.output { cmd := "cc", args := #["-std=c99", "-O2", src, "-o", bin] }
    if cc.exitCode != 0 then throw (IO.userError ("C99 compilation failed: " ++ cc.stderr))
    let out ← IO.Process.output { cmd := bin }
    if out.exitCode != 0 then throw (IO.userError ("C99 execution failed: " ++ out.stderr))
    let some n := out.stdout.trimAscii.toString.toNat? | throw (IO.userError "invalid C99 result")
    return some n
  finally IO.FS.removeDirAll dir

structure RunOptions where
  (jit : String := "") (emitC99 : Option String := none) (ticks : Nat := 100000) (heap : Nat := 65536) (stack : Nat := 4096)
def parseOptions : List String → RunOptions → Except String RunOptions
  | [], options => .ok options
  | "--jit" :: rest, options => parseOptions rest { options with jit := "vm" }
  | "--jit=cc" :: rest, options => parseOptions rest { options with jit := "cc" }
  | "--emit-c99" :: p :: rest, options => parseOptions rest { options with emitC99 := some p }
  | ["--emit-c99"], _ => .error "refused: --emit-c99 needs a path"
  | flag :: value :: rest, options =>
    if flag.startsWith "--jit" then .error s!"refused: unknown JIT mode {flag}" else
    match flag, value.toNat? with
    | _, none => .error s!"{flag} needs a number, got {value}"
    | "--ticks", some n => parseOptions rest { options with ticks := n }
    | "--heap", some n => parseOptions rest { options with heap := n }
    | "--stack", some n => parseOptions rest { options with stack := n }
    | _, _ => .error s!"unknown option {flag}"
  | [flag], _ => .error (if flag.startsWith "--jit" then s!"refused: unknown JIT mode {flag}" else s!"{flag} needs a value")
def packetValueJson : Machine.RuntimeValue → Json
  | .natural n => toJson n
  | .boolean b => toJson b
  | .label s => toJson s
  | other => toJson (toString (repr other))
def receipt (status : String) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("schema", toJson "dregg.objective-bend.run-receipt.v1"), ("status", toJson status)] ++ fields)
def refusePacket (stage message : String) : IO UInt32 := do
  IO.eprintln (receipt "refused" [("stage", toJson stage), ("message", toJson message)]).compress
  return 2
def runPacket (path : String) (options : RunOptions) : IO UInt32 := do
  let input ← IO.FS.readFile path
  match Json.parse input >>= Packet.decodePacket with
  | .error message => refusePacket "decode" message
  | .ok packet =>
    if packet.context ≠ [] then
      refusePacket "closed" "run needs a closed program: the packet's context is not empty"
    else
      match Obend.Elab.Gate.admit packet with
      | .error _ => refusePacket "objective-source-type-check" (Obend.Elab.Gate.refusalReason packet)
      | .ok admitted =>
        let checked := admitted.checked
        if checked.type == .natural then
          if let some n ← runJit packet.source.term options.jit options.emitC99 then
            IO.println (receipt "finished" [("type", Packet.typeJson checked.type), ("ticks", toJson options.ticks), ("value", toJson n)]).compress
            return 0
        else if options.emitC99.isSome then throw (IO.userError "C99 emission requires a natural scalar result")
        let limits : Machine.Limits := ⟨options.heap, options.stack⟩
        let outcome := Machine.runBounded limits options.ticks (Machine.initial packet.source.term)
        let (status, detail) : String × List (String × Json) :=
          match outcome with
          | .finished value _ => ("finished", [("value", packetValueJson value)])
          | .suspended .ticks _ => ("suspended", [("reason", toJson "ticks")])
          | .suspended .capacity _ => ("suspended", [("reason", toJson "capacity")])
          | .divergent address _ => ("divergent", [("address", toJson address)])
          | .refused reason _ => ("refused", [("reason", toJson (toString (repr reason)))])
          | .yielded plan _ => ("yielded", [("plan", toJson plan)])
        IO.println (receipt status ([("type", Packet.typeJson checked.type), ("ticks", toJson options.ticks)] ++ detail)).compress
        return (if status == "finished" then 0 else 3)

/-! ## The source path: a package in memory -/

/-- The module name `run.ts` gives a file: its base name without `.obend`, every character outside
`[A-Za-z0-9_]` replaced by `_`, a leading run of digits prefixed with `M`. -/
def moduleNameOf (file : String) : String :=
  let base := (System.FilePath.mk file).fileName.getD file
  let stem := if base.endsWith ".obend" then String.ofList (base.toList.take (base.length - 6)) else base
  let cleaned := String.ofList (stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')
  let digits := cleaned.toList.takeWhile Char.isDigit
  if digits.isEmpty then cleaned else "M" ++ cleaned

/-- A package read into memory: its modules (captured in order, every import edge locked) and
its entry. -/
structure Package where
  modules : List SourceModule
  entryModule : Nat
  entryDefinition : String
  /-- The entry module's declaration names (for `check` without an ENTRY). -/
  declarations : List String
  /-- A workspace's closure, when the package is one (`Obend.Spec.Workspace`). -/
  closed : Option Obend.Spec.Workspace.Closed := none

/-- The `import` lines of a source (`import ./X.obend as Y`), by a line scan: enough to say, before
capture refuses `import count differs`, that a module with imports is checked as a package. -/
def importLines (bytes : ByteArray) : List String :=
  match String.fromUTF8? bytes with
  | some src => (src.splitOn "\n").filter (·.startsWith "import ")
  | none => []

/-- One `.obend` file as a package, as `run.ts` builds it. A file with `import` lines is not a
package on its own: the refusal names the two ways to check it. -/
def packageOfObendFile (file : String) (entry : Option String) : FE Package := do
  let bytes ← readBytes file
  match importLines bytes with
  | [] => pure ()
  | imports =>
    refuse (s!"{file} imports {imports.length} module(s) ({", ".intercalate imports}); a module with imports is " ++
      "checked as a package: `obend check DIR` reads every .obend file of DIR in name order (an import " ++
      "names an earlier file), or `obend check --package PACKAGE.json` names the modules") "package-input"
  let (m, names) ← captureModule #[] (moduleNameOf file) bytes none [] false
  return ⟨[m], 0, entry.getD "", names, none⟩

/-- A string without its trailing whitespace. -/
def rstrip (s : String) : String := String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse

/-- The sibling imports of a source, `import ./X.obend as Y`, as `(alias, file)` pairs; an import
of another shape (a package path) is returned under `none` so the caller can name it. -/
def siblingImports (bytes : ByteArray) : List (Option (String × String) × String) :=
  (importLines bytes).map fun line =>
    let rest : String := String.ofList (line.toList.drop "import ".length)
    match rest.splitOn " as " with
    | [path, alias] =>
      let path : String := rstrip path
      let alias : String := rstrip alias
      if path.startsWith "./" then (some (alias, String.ofList (path.toList.drop 2)), line) else (none, line)
    | _ => (none, line)

def packageOfObendDir (dir : String) (entry : Option String) : FE Package := do
  let entries ← (do
    try
      let es ← (System.FilePath.mk dir).readDir
      let files := (es.filter fun e => e.fileName.endsWith ".obend").map (·.fileName)
      return .ok (files.qsort (· < ·)).toList
    catch e =>
      return .error (Diagnostic.mk "package-input" e.toString none none) : IO (Except Diagnostic (List String)))
  let files ← match entries with
    | [] => refuse ("no .obend files found in directory " ++ dir) "package-input"
    | fs => pure fs
  -- read every file once and note its sibling imports
  let mut sources : List (String × ByteArray × List (String × String)) := []
  for f in files do
    let bytes ← readBytes (dir ++ "/" ++ f)
    let mut deps : List (String × String) := []
    for (imp, line) in siblingImports bytes do
      match imp with
      | some (alias, target) =>
        if !files.contains target then
          refuse (s!"{dir}/{f} imports {target}, which is not a file of {dir}; a directory package holds every module it " ++
            "imports, or is described by a workspace.json / package.json") "package-input"
        deps := deps ++ [(alias, target)]
      | none =>
        refuse (s!"{dir}/{f}: `{line}` imports a package path; a directory of files holds sibling imports " ++
          "(`import ./X.obend as Y`) only: describe this package by a workspace.json") "package-input"
    sources := sources ++ [(f, bytes, deps)]
  -- place files in dependency order, ties by name
  let mut placed : List String := []
  let mut remaining := sources
  while !remaining.isEmpty do
    match remaining.find? (fun (_, _, deps) => deps.all fun (_, t) => placed.contains t) with
    | some (f, _, _) =>
      placed := placed ++ [f]
      remaining := remaining.filter (·.1 != f)
    | none =>
      refuse (s!"{dir}: the imports of {", ".intercalate (remaining.map (·.1))} form a cycle") "package-input"
  -- capture in that order, each import locked to the module captured for its file
  let mut acc : Array SourceModule := #[]
  let mut lastNames : List String := []
  for f in placed do
    let some (_, bytes, deps) := sources.find? (·.1 == f) | pure ()
    let locks := deps.map fun (alias, target) =>
      Lock.ofJson (Json.mkObj [("alias", toJson alias), ("path", toJson ("./" ++ target)),
        ("module", toJson (toString (placed.idxOf target)))])
    let (m, names) ← captureModule acc (moduleNameOf f) bytes none locks false
    acc := acc.push m
    lastNames := names
  return ⟨acc.toList, acc.size - 1, entry.getD "", lastNames, none⟩

def resolveSourcePath (specPath : String) (p : String) : IO String := do
  if ← System.FilePath.pathExists p then return p
  let mut dir : Option System.FilePath := (System.FilePath.mk specPath).parent
  let mut fuel := 32
  while fuel > 0 do
    fuel := fuel - 1
    match dir with
    | none => break
    | some d =>
      let cand := d / p
      if ← cand.pathExists then return cand.toString
      dir := d.parent
  return p

/-- A `package.json` with every module's `sourcePath` resolved (`resolveSourcePath`): written to a
temporary file for `captureSpec`, which reads its request from disk. -/
def resolvedSpec (specPath : String) (j : Json) : IO String := do
  let modules := ((j.getObjVal? "modules").bind Json.getArr?).toOption.getD #[]
  let mut changed := false
  let mut out : Array Json := #[]
  for m in modules do
    match m.getObjValAs? String "sourcePath" with
    | .ok p =>
      let r ← resolveSourcePath specPath p
      if r != p then changed := true
      out := out.push (m.setObjVal! "sourcePath" (toJson r))
    | .error _ => out := out.push m
  if !changed then return specPath
  let (h, tmp) ← IO.FS.createTempFile
  h.putStr (j.setObjVal! "modules" (Json.arr out)).compress
  h.flush
  return tmp.toString

/-- A workspace as a package: its closure's modules, the entry the workspace names. -/
def packageOfWorkspace (spec : String) (entry : Option String) : FE Package := do
  let c ← Obend.Spec.Workspace.readClosed spec
  let entryDefinition := entry.getD c.entryDefinition
  let m := c.modules[c.entryModule]!
  let ast ← liftFE (parseSource m.name m.source)
  let decls := ((ast.getObjVal? "declarations").bind Json.getArr?).toOption.getD #[]
  return ⟨c.modules, c.entryModule, entryDefinition, decls.toList.map declarationName, some c⟩

/-- Auto-detect `.obend` source files, workspace/package directories, `workspace.v1` JSON, or
`dregg.objective-bend.package-input.v1` JSON specs. -/
partial def packageOfSpec (spec : String) (entry : Option String) : FE Package := do
  let fp := System.FilePath.mk spec
  if ← (fp.isDir : IO Bool) then
    for manifest in ["workspace.json", "package.json"] do
      if ← ((fp / manifest).pathExists : IO Bool) then return ← packageOfSpec (fp / manifest).toString entry
    return ← packageOfObendDir spec entry
  if spec.endsWith ".obend" then
    return ← packageOfObendFile spec entry
  let (_, j) ← readJson spec
  if (j.getObjValAs? String "schema").toOption == some Obend.Spec.Workspace.workspaceSchema then
    return ← packageOfWorkspace spec entry
  let specPath ← (do return .ok (← resolvedSpec spec j) : IO (Except Diagnostic String))
  let c ← captureSpec specPath false
  if specPath != spec then (do try IO.FS.removeFile specPath catch _ => pure () : IO Unit)
  let entryDefinition := entry.getD c.entryDefinition
  let m := c.modules[c.entryModule]!
  let ast ← liftFE (parseSource m.name m.source)
  let decls := ((ast.getObjVal? "declarations").bind Json.getArr?).toOption.getD #[]
  return ⟨c.modules.toList, c.entryModule, entryDefinition, decls.toList.map declarationName, none⟩

def hostLimits (ticks : String) : Json :=
  Json.mkObj [("ticks", toJson ticks), ("heap", toJson "100000"), ("stack", toJson "10000"), ("checkWork", toJson "65536")]

/-- `run.ts`'s response shorthand: a string is that label with an empty record payload. -/
def responseOf (r : Json) : Json :=
  match r with
  | .str label => Json.mkObj [("tag", toJson "variant"), ("label", toJson label),
      ("payload", Json.mkObj [("tag", toJson "record"), ("fields", Json.arr #[])])]
  | other => other

/-- Lower a package: a workspace's closure with its packages, else the package alone. -/
def lowerPackage (p : Package) (entryDefinition : String) (args : Json) (limits : Json) (mode : String) :
    Except Diagnostic Lowering :=
  match p.closed with
  | some c => lowerDecoded p.modules c.decoded p.entryModule entryDefinition args (Json.arr #[]) limits mode c.packages
  | none => lower p.modules p.entryModule entryDefinition args (Json.arr #[]) limits mode

/-- The preview of `entry` applied to `args`, resumed with `responses`: the typed-preview JSON, or
the diagnostic that refused. The same stages `previewCommand` reports. -/
def previewPackage (p : Package) (args responses : Json) (ticks : String) : FE Json := do
  let lowered ← liftFE (lowerPackage p p.entryDefinition args (hostLimits ticks) "application")
  if let .error message := lowered.proposal then refuse message "objective-source-type-proposal"
  let limits := Json.mkObj [("ticks", toJson ticks), ("heap", toJson "100000"), ("stack", toJson "10000")]
  match preview lowered.packet limits responses with
  | .ok r => pure r
  | .error message => refuse message "objective-typed-preview"

/-! ### The short form of `run.ts`, line for line -/

def typeText (t : Json) : String :=
  let rec go : Nat → Json → String
    | 0, t => t.compress
    | fuel + 1, t =>
      match (t.getObjValAs? String "tag").toOption with
      | some "natural" => "Nat" | some "boolean" => "Bool" | some "label" => "String" | some "emptyRow" => "{}"
      | some "variable" => "variable " ++ ((t.getObjValAs? String "index").toOption.getD "")
      | some "field" =>
        let rec fields : Nat → Json → List String
          | 0, _ => []
          | fuel' + 1, r =>
            if (r.getObjValAs? String "tag").toOption == some "field" then
              let name := (r.getObjValAs? String "name").toOption.getD ""
              -- a kind's brand is its identity, not a field a person reads
              if Obend.Core.Brand.isBrand name then fields fuel' ((r.getObjVal? "tail").toOption.getD .null) else
              (name ++ ": " ++ go fuel ((r.getObjVal? "member").toOption.getD .null)) ::
                fields fuel' ((r.getObjVal? "tail").toOption.getD .null)
            else []
        "{" ++ ", ".intercalate (fields (fuel + 1) t) ++ "}"
      | some "variant" => "sum " ++ go fuel ((t.getObjVal? "row").toOption.getD .null)
      | some "computation" => "Activity<" ++ go fuel ((t.getObjVal? "plan").toOption.getD .null) ++ ", " ++
          go fuel ((t.getObjVal? "response").toOption.getD .null) ++ ", " ++ go fuel ((t.getObjVal? "result").toOption.getD .null) ++ ">"
      | _ => t.compress
  go 4096 t

def dataText (d : Json) : String :=
  let rec go : Nat → Json → String
    | 0, d => d.compress
    | fuel + 1, d =>
      match (d.getObjValAs? String "tag").toOption with
      | some "natural" => (d.getObjValAs? String "value").toOption.getD ""
      | some "boolean" => toString ((d.getObjValAs? Bool "value").toOption.getD false)
      | some "label" => (toJson ((d.getObjValAs? String "value").toOption.getD "")).compress
      | some "record" =>
        let fields := ((d.getObjVal? "fields").bind Json.getArr?).toOption.getD #[]
        "{" ++ ", ".intercalate (fields.toList.map fun f => match f with
          | .str name => name
          | f => ((f.getObjValAs? String "name").toOption.getD "") ++ ": " ++ go fuel ((f.getObjVal? "value").toOption.getD .null)) ++ "}"
      | some "variant" =>
        ((d.getObjValAs? String "label").toOption.getD "") ++ "(" ++
          (match d.getObjVal? "payload" with
            | .ok payload => go fuel payload
            | .error _ => "...") ++ ")"
      | _ => d.compress
  go 4096 d

/-- `status`, `type`, one `turn` line per yield, `result` (the deep view when there is one, else the
weak-head view), `diagnostic`. -/
def shortForm (p : Json) (status : String) : String :=
  let lines : List String := ["status: " ++ status, "type: " ++ typeText ((p.getObjVal? "type").toOption.getD .null)]
  let turns := ((p.getObjVal? "turns").bind Json.getArr?).toOption.getD #[]
  let turnLines := turns.toList.zipIdx.map fun (t, i) =>
    "turn " ++ toString (i + 1) ++ ": yield " ++ dataText ((t.getObjVal? "plan").toOption.getD .null) ++
      (match t.getObjVal? "response" with
        | .ok r => "  <- " ++ dataText r
        | .error _ => "  (waiting)")
  let result := (p.getObjVal? "result").toOption.getD .null
  let resultLines := if result.isNull then [] else
    ["result: " ++ dataText (match (p.getObjVal? "resultData").toOption with
      | some d => if d.isNull then result else d
      | none => result)]
  let diagnostic := (p.getObjVal? "diagnostic").toOption.getD .null
  let diagnosticLines := if diagnostic.isNull then [] else
    ["diagnostic: " ++ (match diagnostic with | .str s => s | other => other.compress)]
  "\n".intercalate (lines ++ turnLines ++ resultLines ++ diagnosticLines)

/-- `status: refused`, `stage`, `message`, as `run.ts` prints a diagnostic. -/
def refusedForm (d : Diagnostic) : String :=
  "status: refused\nstage: " ++ d.stage ++ "\nmessage: " ++ d.message

structure RunArgs where
  jit : String := ""
  emitC99 : Option String := none
  args : Json := Json.arr #[]
  responses : Json := Json.arr #[]
  ticks : String := "100000"
  json : Bool := false
  /-- `--entry NAME`: run another definition of the entry module than the package names. -/
  entry : Option String := none

/-- `[ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]` in any order of flags, as `run.ts` reads them. -/
def parseRunArgs : List String → RunArgs → List String → Except String (RunArgs × List String)
  | [], r, positional => .ok (r, positional.reverse)
  | "--jit" :: rest, r, positional => parseRunArgs rest { r with jit := "vm" } positional
  | "--jit=cc" :: rest, r, positional => parseRunArgs rest { r with jit := "cc" } positional
  | "--emit-c99" :: p :: rest, r, positional => parseRunArgs rest { r with emitC99 := some p } positional
  | ["--emit-c99"], _, _ => .error "refused: --emit-c99 needs a path"
  | "--json" :: rest, r, positional => parseRunArgs rest { r with json := true } positional
  | "--ticks" :: n :: rest, r, positional => parseRunArgs rest { r with ticks := n } positional
  | ["--ticks"], _, _ => .error "--ticks needs a value"
  | "--entry" :: e :: rest, r, positional => parseRunArgs rest { r with entry := some e } positional
  | ["--entry"], _, _ => .error "--entry needs a definition name"
  | x :: rest, r, positional =>
    if x.startsWith "--jit" then .error s!"refused: unknown JIT mode {x}" else parseRunArgs rest r (x :: positional)
def runSource (package : FE Package) (rest : List String) : IO UInt32 := do
  let (options, positional) ← match parseRunArgs rest {} [] with
    | .ok v => pure v
    | .error e => do IO.eprintln e; return (if e.startsWith "refused" then 2 else 64)
  let parsed : Except String (Json × Json) := do
    let args ← Json.parse (positional.getD 0 "[]")
    let responses ← Json.parse (positional.getD 1 "[]") >>= Json.getArr?
    pure (args, Json.arr (responses.map responseOf))
  let (args, responses) ← match parsed with
    | .ok v => pure v
    | .error e => do IO.eprintln ("arguments and responses must be JSON arrays: " ++ e); return 64
  let result ← (do
    let p ← package
    let p := match options.entry with
      | some e => { p with entryDefinition := e }
      | none => p
    if p.entryDefinition.isEmpty then refuse "usage: run needs an ENTRY (one def of the file)" "preview-request"
    if !options.jit.isEmpty || options.emitC99.isSome then
      let lowered ← liftFE (lowerPackage p p.entryDefinition args (hostLimits options.ticks) "application")
      let accepted ← liftFE (accept lowered)
      if accepted.typed.type == .natural then
        if let some n ← (runJit accepted.erased options.jit options.emitC99 : IO (Option Nat)) then
          let value := Obend.Spec.Preview.valueJson (.natural n)
          return (Json.mkObj [("status", toJson "finished"), ("type", Packet.typeJson accepted.typed.type),
            ("result", value), ("resultData", value), ("turns", .arr #[]), ("diagnostic", .null)], p.closed)
      else if options.emitC99.isSome then refuse "C99 emission requires a natural scalar result" "jit"
    return (← previewPackage p args responses options.ticks, p.closed) : FE (Json × Option Obend.Spec.Workspace.Closed)).run
  match result with
  | .ok (p, closed) =>
    let status := (p.getObjValAs? String "status").toOption.getD ""
    match closed with
    | none => if options.json then IO.println p.pretty else IO.println (shortForm p status)
    | some c =>
      let cl := c.closure
      if options.json then
        IO.println (p.setObjVal! "turn" (Obend.Spec.Workspace.turnJson cl)).pretty
      else
        IO.println (shortForm p status)
        IO.println ("package: " ++ " > ".intercalate cl.order)
        for pin in cl.pins do IO.println ("pin: " ++ Obend.Spec.Workspace.pinText pin)
    return 0
  | .error d =>
    if options.json then
      IO.println (Json.mkObj [("status", toJson "refused"), ("diagnostic", d.json)]).pretty
    else IO.println (refusedForm d)
    return 2

/-- `check`: every named declaration lowered in definition mode and accepted by the checker on
the front end's own packet. -/
def checkSource (package : FE Package) : IO UInt32 := do
  match ← package.run with
  | .error d => IO.eprintln d.json.compress; return 2
  | .ok p =>
    let names := if p.entryDefinition.isEmpty then p.declarations else [p.entryDefinition]
    let entryName := (p.modules[p.entryModule]?.map (·.name)).getD ""
    let mut failed := false
    for name in names do
      let key := entryName ++ "." ++ name
      let outcome : Except Diagnostic Json := do
        let lowered ← lowerPackage p name (Json.arr #[]) (hostLimits "100000") "definition"
        let accepted ← accept lowered
        pure (Json.mkObj [("declaration", toJson key), ("status", toJson "accepted"),
          ("type", Packet.typeJson accepted.typed.type), ("uses", toJson accepted.typed.uses)])
      match outcome with
      | .ok receipt => IO.println receipt.compress
      | .error d =>
        -- A record or sum has no knot field: not a refusal of the program.
        if d.message == "missing selected entry" then
          if p.entryDefinition.isEmpty then continue
          IO.eprintln (refusedForm d)
          return 2
        failed := true
        IO.println (Json.mkObj [("declaration", toJson key), ("status", toJson "refused"), ("diagnostic", d.json)]).compress
    return (if failed then 2 else 0)

/-! ## Workspace commands -/
def admitCommand (spec turnPath : String) : IO UInt32 := do
  let result ← (do
    let w ← Obend.Spec.Workspace.readWorkspace spec
    let (_, j) ← readJson turnPath
    let j := (j.getObjVal? "turn").toOption.getD j
    let t ← Obend.Spec.Workspace.turnOfJson w j
    return Obend.Spec.Ecosystem.admit w.view t : FE Obend.Spec.Ecosystem.Admission).run
  match result with
  | .error d => IO.println (Json.mkObj [("status", toJson "refused"), ("diagnostic", d.json)]).pretty; return 2
  | .ok a =>
    IO.println (Obend.Spec.Workspace.admissionJson a).pretty
    return (match a with | .admitted _ => 0 | _ => 3)

/-- The name a single package is judged under: a directory's or a manifest's directory's name, a
file's module name. -/
def packageNameOf (spec : String) : String :=
  if spec.endsWith ".obend" then moduleNameOf spec
  else if spec.endsWith ".json" then (((System.FilePath.mk spec).parent.bind (·.fileName)).getD spec)
  else ((System.FilePath.mk spec).fileName.getD spec)

def judgeCommand (spec old new : String) : IO UInt32 := do
  let result ← (do
    let isWs ← (do
      if !spec.endsWith ".json" then return .ok false
      try return .ok (((Json.parse (← IO.FS.readFile spec)).bind (·.getObjValAs? String "schema")).toOption ==
        some Obend.Spec.Workspace.workspaceSchema)
      catch _ => return .ok false : IO (Except Diagnostic Bool))
    let laws ← if isWs then
        let c ← Obend.Spec.Workspace.readClosed spec
        pure (c.laws, c.closure.order)
      else
        let p ← packageOfSpec spec none
        -- the laws are the package's whatever the entry: the first definition that lowers serves
        let candidates := if p.entryDefinition.isEmpty then p.declarations.reverse else [p.entryDefinition]
        let mut found : Option Obend.Spec.FrontEnd.Lowering := none
        for name in candidates do
          if found.isNone then
            match lowerPackage p name (Json.arr #[]) (hostLimits "100000") "definition" with
            | .ok l => found := some l
            | .error _ => pure ()
        let some l := found | refuse "no definition of the entry module lowers; name one with --entry" "objective-law"
        let pkg := packageNameOf spec
        pure ([(pkg, l.laws)], [pkg])
    let parsed : Except String Json := do
      let o ← Json.parse old
      let n ← Json.parse new
      Obend.Spec.Workspace.judgeWith laws.1 laws.2 o n
    match parsed with
    | .ok j => pure j
    | .error e => refuse e "objective-law" : FE Json).run
  match result with
  | .error d => IO.println (Json.mkObj [("status", toJson "refused"), ("diagnostic", d.json)]).pretty; return 2
  | .ok j =>
    IO.println j.pretty
    return (if (j.getObjValAs? String "status").toOption == some "admitted" then 0 else 3)

/-! ## Claims: obligations, proofs, ground runs (lane Logic, `Obend.Logic`) -/

/-- The erased selection `get knot ENTRY` of a package, in definition mode. -/
def selection (p : Package) (entry : String) : Except Diagnostic Obend.Core.Term.Term := do
  let lowered ← lowerPackage p entry (Json.arr #[]) (hostLimits "100000") "definition"
  match lowered.term.erase with
  | .ok t => pure t
  | .error e => throw (elaborationRefusal e)

/-- `SPEC.CLAIM` split at its last dot. -/
def splitClaim (name : String) : Option (String × String) :=
  match (name.splitOn ".").reverse with
  | claim :: spec@(_ :: _) => some (".".intercalate spec.reverse, claim)
  | _ => none

/-- The package of `spec` and its erased selection of `entry`, or the refusal's JSON. -/
def loadSelection (spec entry : String) : IO (Except String (Package × Obend.Core.Term.Term)) := do
  match ← (packageOfSpec spec none).run with
  | .error d => return .error d.json.compress
  | .ok p => return ((selection p entry).mapError (·.json.compress)).map (p, ·)

/-- `obend check --obligations`: every claim of the package, its object, and its status, the slot's
read of the certificate in `DIR/SPEC.CLAIM.json` (when given) at this program's object. -/
def obligationsCommand (spec entry : String) (receipts : Option String) : IO UInt32 := do
  let (p, t) ← match ← loadSelection spec entry with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 2
  let some root := Obend.Logic.Program.knotOf t | IO.eprintln "the selection is not a knot field"; return 2
  -- `keeps INV by LAW` lines: listed; their certifying-shape check (`Law.checkClaim`) needs the
  -- compiled law at the object's state type, which the installing kernel holds, not this listing.
  for m in p.modules do
    if let .ok decoded := parseModule m then
      for (inv, law) in decoded.keeps do
        IO.println (Json.mkObj [("keeps", toJson (m.name ++ "." ++ inv)), ("law", toJson (m.name ++ "." ++ law)),
          ("status", toJson "unchecked")]).compress
  for (specKey, name) in Obend.Logic.Program.claimFields root do
    let full := specKey ++ "." ++ name
    match Obend.Logic.Program.objectFor specKey t with
    | none => IO.println (Json.mkObj [("claim", toJson full), ("status", toJson "no-object"),
        ("entry", toJson entry)]).compress
    | some C =>
      match Obend.Logic.Program.claimObj root C specKey name with
      | .error e => IO.println (Json.mkObj [("claim", toJson full), ("status", toJson "refused"), ("message", toJson e)]).compress
      | .ok o =>
        let receipt : Option Json ← match receipts with
          | some dir => do
            let path := dir ++ "/" ++ full ++ ".json"
            if ← System.FilePath.pathExists path then pure (Json.parse (← IO.FS.readFile path)).toOption else pure none
          | none => pure none
        -- The slot is the certified claim's (its statement), read at this program's object, when the
        -- statement is this claim's (its code, arity and the layer `specKey` names; the layer's index
        -- moves under composition) and the certificate is addressed to it. Any other receipt is no
        -- candidate: the obligation stays a hole.
        let bound : Option (Obend.Logic.ClaimObj × List Obend.Logic.RStep) := receipt.bind fun j => do
          let cert ← (j.getObjVal? "certificate").toOption
          let st ← (Obend.Logic.statementOf (← (j.getObjVal? "statement").toOption).compress).toOption
          let steps ← (Obend.Logic.certificateOf cert.compress).toOption
          let addr ← (cert.getObjValAs? String "address").toOption
          if st.claim == o.claim && st.arity == o.arity && st.comp.layers[st.layer]?.map (·.name) == some specKey
              && addr == toString (Obend.Core.Code.address o.claim) then some (st, steps) else none
        let (certified, selected) := match bound with
          | some (st, steps) => (st, some steps)
          | none => (o, none)
        let status := Obend.Logic.readStatus certified 1000000 C selected none none
        let extra : List (String × Json) := match status with
          | .blocked ms => [("blocked", toJson ms)]
          | .checked f tr a => [("format", toJson f), ("trust", toJson tr), ("address", toJson (toString a))]
          | _ => []
        let layers := C.layers.map (·.name)
        IO.println (Json.mkObj ([("claim", toJson full), ("status", toJson status.label),
          ("object", toJson layers)] ++ extra)).compress
  return 0
def parseNats (s : String) : Option (List Nat) := (s.splitOn ",").mapM String.toNat?

/-- `obend prove`: ground instances first (a `false` refutes and stops), then the rewriter; the
first certificate the claim checker accepts is installed as the receipt. -/
def proveCommand (spec name entry out : String) (ground : List Nat) : IO UInt32 := do
  let (_, t) ← match ← loadSelection spec entry with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 2
  let some root := Obend.Logic.Program.knotOf t | IO.eprintln "the selection is not a knot field"; return 2
  let some (specKey, claim) := splitClaim name | IO.eprintln s!"{name}: name a claim as SPEC.CLAIM"; return 64
  let some C := Obend.Logic.Program.objectFor specKey t
    | IO.eprintln s!"no object of {specKey} is reached from {entry}"; return 2
  let o ← match Obend.Logic.Program.claimObj root C specKey claim with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  IO.println s!"object: fix(compose({", ".intercalate (C.layers.reverse.map (·.name))}), seed) from {entry}"
  let instances := if o.arity == 1 then ground.map (fun n => [n]) else if o.arity == 0 then [[]] else []
  for ds in instances do
    match Obend.Logic.groundCheck Obend.Logic.Receipt.groundFuel
        ⟨Obend.Logic.instantiateClaim o.claim o.comp o.layer, ds.map .natural⟩ () with
    | .refused _ _ =>
      IO.FS.writeFile out ((Obend.Logic.Receipt.refutedReceipt name o ds).pretty ++ "\n")
      IO.println s!"refuted: {name} runs to false at {ds}; wrote {out}"
      return 3
    | .ok => IO.println s!"ground {ds}: true"
    | .uncovered => IO.println s!"ground {ds}: uncovered"
  match Obend.Logic.Program.proposeDerivation o with
  | none => IO.println s!"unchecked: no producer found a certificate for {name}"; return 3
  | some steps =>
    match Obend.Logic.claimCheck (Obend.Logic.sizeList steps) o steps with
    | .ok =>
      IO.FS.writeFile out ((Obend.Logic.Receipt.checkedReceipt name o steps instances).pretty ++ "\n")
      IO.println s!"checked: {name} by rewrite@1 ({Obend.Logic.sizeList steps} steps); wrote {out}"
      return 0
    | _ => IO.println s!"unchecked: the proposed derivation for {name} is refused"; return 3

/-- `obend ground`: the ground judge on `ENTRY() == EXPECTED`. -/
def groundCommand (spec entry expected : String) : IO UInt32 := do
  let (_, t) ← match ← loadSelection spec entry with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 2
  let some n := expected.toNat? | IO.eprintln "EXPECTED must be a natural"; return 64
  let claim := Obend.Core.Term.Term.binary .equal t (.nat n)
  match Obend.Logic.groundCheck Obend.Logic.Receipt.groundFuel ⟨claim, []⟩ () with
  | .ok => IO.println s!"ok: {entry}() == {n} (ground, decidable, Holds)"; return 0
  | .refused _ _ => IO.println s!"refuted: {entry}() == {n} runs to false (ground, decidable)"; return 3
  | .uncovered => IO.println s!"uncovered: {entry}() == {n} did not finish within the grade"; return 3

/-! ## The leaf emitter (lane Leaf, `Obend.Leaf`) -/

/-- What a value is, for a refusal. -/
def describeValue : Obend.Core.Term.Term → String
  | .nat n => s!"the natural {n}"
  | .boolean b => s!"the boolean {b}"
  | .label l => s!"the label {l}"
  | .lam _ => "a function"
  | .record fs => s!"a record with fields {fs.map (·.1)}, not a fix: a record literal has no layers to flatten"
  | .inject l _ => s!"the constructor {l}"
  | .specification _ _ => "a spec (a layer, not an object: an object is fix(Spec, seed))"
  | .prototype _ _ => "a prototype value"
  | _ => "a term that is not an object"

/-- Why the `fix` at the head of `t`, if one stands there under applications, reads, extensions and
binary operators, is not an object `obend emit` compiles: which part of the fragment it misses. -/
def headFixRefusal : Nat → Obend.Core.Term.Term → Option String
  | 0, _ => none
  | fuel + 1, t =>
    match t with
    | .fix S seed =>
      match Obend.Logic.Program.decodeOperands 64 S with
        | none =>
          some "a fix stands at the head, but its first operand is not a spec or compose(…) of specs (every operand must run to specification(meta, λself. λsuper. …))"
        | some (top, below) =>
          match Obend.Logic.Program.seedRecord seed with
          | none =>
            some s!"fix(compose({", ".intercalate ((top :: below).reverse.map (·.name))}), seed) stands at the head, but its seed does not run to a record within {Obend.Logic.Program.readFuel} steps (a seed is a record literal or a def that returns one)"
          | some _ =>
            let namedLayers := (top :: below).filter (·.name != "")
            if namedLayers.isEmpty then
              -- the package knot's own fix: not an object, keep reducing
              none
            else
              let unnamed := (top :: below).length - namedLayers.length
              some s!"fix(compose({", ".intercalate (namedLayers.reverse.map (·.name))}), seed) stands at the head with {unnamed} unnamed layer(s) beside the named ones; only named spec layers are compiled"
    | .app f _ | .get f _ | .extend f _ | .binary _ f _ => headFixRefusal fuel f
    | _ => none

/-- The reason `findObject` reached no object from `t`: the first `fix` met on the way that misses
the fragment, or else what `t` runs to. -/
def objectRefusal (t : Obend.Core.Term.Term) : String :=
  go 100000 t
where
  go : Nat → Obend.Core.Term.Term → String
    | 0, _ => "the entry does not run to a value within 100000 steps, and no fix stands at its head on the way"
    | fuel + 1, t =>
      match headFixRefusal 64 t with
      | some why => why
      | none =>
        match Obend.Law.step? t with
        | some t' => go fuel t'
        | none =>
          if Obend.Law.isValueB t then s!"the entry runs to {describeValue t}"
          else "the entry is stuck on a term the reducer does not step"

/-- The program's selection and the composition of spec layers reached from it. -/
def leafObject (spec entry : String) : IO (Except String (Obend.Core.Term.Term × Obend.Logic.Composition)) := do
  let (_, t) ← match ← loadSelection spec entry with
    | .ok r => pure r
    | .error e => return .error e
  -- the first composition of named spec layers (the package knot's own layer is unnamed)
  match Obend.Logic.Program.findObject (fun C => C.layers.all (·.name != "")) 100000 t with
  | some C => return .ok (t, C)
  | none => return .error s!"no fix (compose …) {"{"}seed{"}"} is reached from {entry}: {objectRefusal t}"

/-- The natural the demand machine finishes `t` with. -/
def machineNat (t : Obend.Core.Term.Term) : Option Nat :=
  match Obend.Core.Machine.runBounded ⟨1000000, 1000000⟩ 10000000 (Obend.Core.Machine.initial t) with
  | .finished (.natural n) _ => some n
  | _ => none
def showNat (n : Option Nat) : String := (n.map toString).getD "no natural"
def kindName : Obend.Leaf.DefKind → String | .method => "method" | .cell => "cell"
def cellName : Obend.Leaf.LeafCell → String | .layer k => "layer " ++ k | .object n => "object " ++ n

/-- `MEMBER(N)` read from the term `obj` and run on the demand machine. -/
def callOn (obj : Obend.Core.Term.Term) (m : String) (n : Nat) : Option Nat :=
  machineNat (.app (.get obj m) (.nat n))

/-- `obend emit`: flatten the composition reached from ENTRY, emit its book, write it with the
composition it pins. -/
def emitCommand (spec entry out : String) (call : Option (String × Nat)) : IO UInt32 := do
  let (t, C) ← match ← leafObject spec entry with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 2
  IO.println s!"object: fix(compose({", ".intercalate (C.layers.reverse.map (·.name))}), seed) from {entry}"
  unless C.closedB do
    IO.println "refused: the composition is not closed, outside flatten_sound's scope"; return 3
  let B := Obend.Leaf.emit C
  IO.println s!"slots: {B.slots}"
  for d in B.defs do IO.println s!"def {d.slot} {d.member}: {kindName d.kind}, reads {d.reads}"
  for (m, _) in B.statics do IO.println s!"static {m}"
  IO.println s!"closed: {B.closedB}"
  let defs := B.defs.map fun d => Json.mkObj [("member", toJson d.member), ("slot", toJson d.slot),
    ("kind", toJson (kindName d.kind)), ("reads", toJson d.reads), ("code", Obend.Logic.termJson d.code)]
  IO.FS.writeFile out ((Json.mkObj [("object", toJson entry), ("composition", Obend.Logic.termJson C.code),
    ("slots", toJson B.slots), ("defs", Json.arr defs.toArray),
    ("statics", Json.arr (B.statics.map fun (m, v) => Json.mkObj [("member", toJson m),
      ("value", Obend.Logic.termJson v)]).toArray)]).pretty ++ "\n")
  IO.println s!"wrote {out}"
  if let some (m, n) := call then
    IO.println s!"book: {m}({n}) = {showNat (callOn B.link m n)}"
    IO.println s!"machine: {m}({n}) = {showNat (callOn C.object m n)}; {entry}() = {showNat (machineNat t)}"
  return 0
def specializeCommand (spec entry bookPath : String) (call : Option (String × Nat)) : IO UInt32 := do
  let (_, now) ← match ← leafObject spec entry with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 2
  let j ← match Json.parse (← IO.FS.readFile bookPath) with
    | .ok j => pure j
    | .error e => IO.eprintln e; return 2
  let some name := (j.getObjValAs? String "object").toOption | IO.eprintln "the book names no object"; return 2
  let some code := ((j.getObjVal? "composition").toOption).bind fun c => (Obend.Logic.termOf c).toOption
    | IO.eprintln "the book pins no composition"; return 2
  let some C := Obend.Leaf.compositionOfCode code | IO.eprintln "the pinned composition does not decode"; return 2
  let v := Obend.Leaf.viewOf 0 entry now
  let book := Obend.Leaf.Candidate.book name C
  match Obend.Leaf.specSlot.read (Obend.Slot.World.holdsAt v) (some book) with
  | .usable _ _ => IO.println "book: usable"
  | .blocked _ d => IO.println s!"book: blocked by {", ".intercalate (d.map (cellName ·.cell))}"
  | .rejected _ => IO.println "book: rejected (outside flatten_sound's scope)"
  | .empty => pure ()
  let selected := (Obend.Slot.slotAdvance : Obend.Slot.Advance Obend.Leaf.LeafView Obend.Leaf.LeafPin
    Obend.Leaf.Candidate).advance Obend.Leaf.specSlot v (Obend.Leaf.specOrder name C) (some book)
  match selected with
  | .ok (.book _ C') =>
    IO.println "selected: book"
    if let some (m, n) := call then IO.println s!"book: {m}({n}) = {showNat (callOn (Obend.Leaf.emit C').link m n)}"
  | .ok .machine =>
    IO.println "selected: machine"
    if let some (m, n) := call then IO.println s!"machine: {m}({n}) = {showNat (callOn now.object m n)}"
  | _ => IO.println "selected: none"
  return 0
def leafCall : List String → Option (Option (String × Nat))
  | [] => some none
  | ["--call", m, n] => n.toNat?.map fun n => some (m, n)
  | _ => none
def proveArgs (spec name : String) : List String → Option (IO UInt32)
  | ["--object", entry, "--out", out] => some (proveCommand spec name entry out [0, 3, 41])
  | ["--object", entry, "--out", out, "--ground", g] => (parseNats g).map (proveCommand spec name entry out ·)
  | _ => none

/-! JSON adapters keep decoding failures separate from semantic refusals. -/
namespace LiveCli
open Lean
open Obend.Codec.Hex (bytesToHex byteArrayToHex hexCharsToNat?)
def field (j : Json) (k : String) : Except String Json := j.getObjVal? k
def nat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k
def text (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def decodeIO {α : Type} (e : Except String α) : IO α :=
  match e with | .ok a => pure a | .error e => throw (IO.userError e)
def load (p : String) : IO Json := IO.FS.readFile p >>= fun s => decodeIO (Json.parse s)
def output (args : List String) (j : Json) : IO Unit := do
  match args with
  | [] => IO.println j.compress
  | ["--out", p] => IO.FS.writeFile p (j.compress ++ "\n")
  | _ => throw (IO.userError "expected [--out FILE]")
def verdict (ok : Bool) (reason : String) : Json := Json.mkObj
  [("status", toJson (if ok then "accepted" else "refused")), ("reason", toJson reason)]
def finish (args : List String) (ok : Bool) (j : Json) : IO UInt32 := do
  output args j
  if !ok then IO.eprintln "refused: verification failed"
  return if ok then 0 else 3
def hex256 (n : Nat) : String := bytesToHex (Obend.Digest.HashBytes.be 32 n)
/-- 64 hex digits of either case. -/
def unhex256 (s : String) : Except String Nat :=
  match s.length == 64, hexCharsToNat? s.toList with
  | true, some n => pure n
  | _, _ => throw "expected 64 hex digits"
/-- `flag VALUE` taken out of an argument list, wherever it stands. -/
def takeOpt (flag : String) : List String → Option String × List String
  | f :: rest => match f == flag, rest with
    | true, v :: tail => (some v, tail)
    | _, _ => let (o, r) := takeOpt flag rest; (o, f :: r)
  | [] => (none, [])
/-- The Rust receipt binary; `quiet` keeps its report off stdout, which then carries one JSON value. -/
def zk (cmd : String) (args : List String) (quiet := false) : IO UInt32 := do
  let override := (← IO.getEnv "OBEND_ZK_RECEIPT_BIN").getD ""
  let sibling := ((← IO.appPath).parent.getD ".") / "obend-zk-receipt"
  let candidates := if override.isEmpty then [sibling.toString, "./target/release/obend-zk-receipt", "../target/release/obend-zk-receipt"] else [override]
  for p in candidates do
    if ← (System.FilePath.mk p).pathExists then
      let out ← IO.Process.output { cmd := p, args := (cmd :: args).toArray }
      (← if quiet then IO.getStderr else IO.getStdout).putStr out.stdout
      (← IO.getStderr).putStr out.stderr
      return out.exitCode
  IO.eprintln "refused: obend-zk-receipt binary not found (set OBEND_ZK_RECEIPT_BIN)"
  return 2
open Obend.Law.AmendCli Obend.Law.PointwiseRevise in
 def amend (trace : Bool) (j : Json) (args : List String) : IO UInt32 := do
  let requests ← decodeIO (if trace then field j "steps" >>= Json.getArr? else .ok #[j])
  let turns ← decodeIO (requests.toList.mapM fun r => do
    let fields ← ["version", "slot", "clauses"].mapM fun key => return (key, ← field r key)
    parseAmendBundleJson (Json.mkObj fields).compress)
  let initial : LiveState := {
    world := fun _ => ⟨6, []⟩, transferred := 0, generations := 0
    fabric := fun k => { (default : Obend.Hardware.DprStutter.DprFabric) with specSlot := k, phase := .active, activeTiles := modelTiles 6 } }
  let (st, receipts) := if trace then executeTraceWithReceipts initial (turns.map (·, [])) else
    match turns with | [t] => let (s, r) := executeLiveAmendment initial t []; (s, [r]) | _ => (initial, [])
  let mut prior := ""
  let mut ok := true
  let mut rows := #[]
  for (r, req) in receipts.zip requests.toList do
    let expected ← match field req "prevReceipt" with
      | .error _ => pure none
      | .ok v => pure (some (← decodeIO v.getStr?))
    if expected.isSome && expected != some prior then ok := false
    let digest := byteArrayToHex r.digest
    let row ← decodeIO (Json.parse (renderAmendReceiptJson r))
    let accepted := match r.revision with | .accepted _ _ => true | _ => false
    ok := ok && accepted
    rows := rows.push ((row.setObjVal! "receiptHex" (toJson digest)).setObjVal! "previousReceiptHex" (toJson prior)
      |>.setObjVal! "turnDigestHex" (toJson (byteArrayToHex r.turnDigest))
      |>.setObjVal! "bedrockDigestHex" (toJson (byteArrayToHex r.bedrockDigest))
      |>.setObjVal! "supportDigestHex" (toJson (byteArrayToHex r.supportDigest)))
    prior := digest
  let summary := (verdict ok (if ok then "law admitted" else "law or receipt chain refused"))
    |>.setObjVal! "receipts" (.arr rows) |>.setObjVal! "generations" (toJson st.generations)
    |>.setObjVal! "transferred" (toJson st.transferred)
  finish args ok summary
def rat (j : Json) : Except String Rat := Obend.Analysis.NonlinearPdeCli.rat j
def pde (solve : Bool) (j : Json) (args : List String) : IO UInt32 :=
  Obend.Analysis.NonlinearPdeCli.runPdeCli solve j args
open Obend.Crypto.PqHashSignatures
instance : ToJson UInt8 := ⟨fun b => toJson b.toNat⟩
instance : FromJson UInt8 := ⟨fun j => do
  let n ← j.getNat?
  if n < 256 then return UInt8.ofNat n else throw "byte outside [0,255]"⟩
instance : FromJson PqHashParams := ⟨fun j => return ⟨← j.getObjValAs? _ "w", ← j.getObjValAs? _ "ell1", ← j.getObjValAs? _ "subtreeHeight", ← j.getObjValAs? _ "numLayers", ← j.getObjValAs? _ "forsTrees", ← j.getObjValAs? _ "forsHeight", ← j.getObjValAs? _ "maxSigsLog2", ← j.getObjValAs? _ "statefulLeanSig"⟩⟩
instance : ToJson PqHashParams := ⟨fun x => Json.mkObj [("w", toJson x.w), ("ell1", toJson x.ell1), ("subtreeHeight", toJson x.subtreeHeight), ("numLayers", toJson x.numLayers), ("forsTrees", toJson x.forsTrees), ("forsHeight", toJson x.forsHeight), ("maxSigsLog2", toJson x.maxSigsLog2), ("statefulLeanSig", toJson x.statefulLeanSig)]⟩
instance : FromJson PqSecretKey := ⟨fun j => return ⟨← j.getObjValAs? _ "skSeed", ← j.getObjValAs? _ "skPrf", ← j.getObjValAs? _ "pkSeed"⟩⟩
instance : ToJson PqSecretKey := ⟨fun x => Json.mkObj [("skSeed", toJson x.skSeed), ("skPrf", toJson x.skPrf), ("pkSeed", toJson x.pkSeed)]⟩
instance : FromJson PqPublicKey := ⟨fun j => return ⟨← j.getObjValAs? _ "pkSeed", ← j.getObjValAs? _ "pkRoot"⟩⟩
instance : ToJson PqPublicKey := ⟨fun x => Json.mkObj [("pkSeed", toJson x.pkSeed), ("pkRoot", toJson x.pkRoot)]⟩
instance : FromJson LayerXmssSig := ⟨fun j => return ⟨← j.getObjValAs? _ "tswCtr", ← j.getObjValAs? _ "wotsChains", ← j.getObjValAs? _ "authPath"⟩⟩
instance : ToJson LayerXmssSig := ⟨fun x => Json.mkObj [("tswCtr", toJson x.tswCtr), ("wotsChains", toJson x.wotsChains), ("authPath", toJson x.authPath)]⟩
instance : FromJson ForsTreeOpening := ⟨fun j => return ⟨← j.getObjValAs? _ "secretVal", ← j.getObjValAs? _ "authPath"⟩⟩
instance : ToJson ForsTreeOpening := ⟨fun x => Json.mkObj [("secretVal", toJson x.secretVal), ("authPath", toJson x.authPath)]⟩
instance : FromJson PqHashSig := ⟨fun j => return ⟨← j.getObjValAs? _ "rRand", ← j.getObjValAs? _ "msgTswCtr", ← j.getObjValAs? _ "leafGlobalIdx", ← j.getObjValAs? _ "forsOpenings", ← j.getObjValAs? _ "layerSigs"⟩⟩
instance : ToJson PqHashSig := ⟨fun x => Json.mkObj [("rRand", toJson x.rRand), ("msgTswCtr", toJson x.msgTswCtr), ("leafGlobalIdx", toJson x.leafGlobalIdx), ("forsOpenings", toJson x.forsOpenings), ("layerSigs", toJson x.layerSigs)]⟩
def mpc (sign : Bool) (j : Json) (args : List String) : IO UInt32 := do
  let params : PqHashParams ← decodeIO (j.getObjValAs? PqHashParams "params")
  let msg : List UInt8 ← decodeIO (j.getObjValAs? (List UInt8) "message")
  if !params.wellFormed then return ← finish args false (verdict false "invalid signing parameters")
  if !sign then
    let pk ← decodeIO (j.getObjValAs? PqPublicKey "publicKey")
    let sig ← decodeIO (j.getObjValAs? PqHashSig "signature")
    let ok := pk.pkSeed.length == 32 && pk.pkRoot.length == 32 &&
      verifyPqHashSig cshake256Suite params pk msg sig
    return ← finish args ok (verdict ok "hash signature verification")
  let shares ← decodeIO (j.getObjValAs? (List PqSecretKey) "shares")
  let threshold ← decodeIO (nat j "threshold")
  if threshold != 2 || shares.length != 3 || shares.any (fun s =>
      s.skSeed.length != 32 || s.skPrf.length != 32 || s.pkSeed.length != 32) then
    return ← finish args false (verdict false "RSS signing requires three 32-byte shares and threshold 2")
  let [a, b, c] := shares | return ← finish args false (verdict false "three shares required")
  if shares.any (fun s => s.pkSeed != a.pkSeed) then return ← finish args false (verdict false "public seed disagreement")
  let xor := Obend.Crypto.ThresholdHashMpc.reconstructXorBytes
  let sk : PqSecretKey := ⟨xor a.skSeed b.skSeed c.skSeed,
    xor a.skPrf b.skPrf c.skPrf, a.pkSeed⟩
  let leaf ← decodeIO (nat j "leafGlobalIdx")
  let random ← decodeIO (j.getObjValAs? (List UInt8) "optRand")
  let grind ← decodeIO (nat j "maxGrind")
  let some sig := Obend.Crypto.ThresholdHashMpc.evalCutBatchSign cshake256Suite params sk msg random leaf grind
    | return ← finish args false (verdict false "signing cut/grind refused")
  let pk := derivePublicKey cshake256Suite params sk
  let ok := verifyPqHashSig cshake256Suite params pk msg sig
  finish args ok (Json.mkObj [("params", toJson params), ("message", toJson msg),
    ("publicKey", toJson pk), ("signature", toJson sig), ("status", toJson (if ok then "accepted" else "refused"))])
open Obend.Polis.Custody
instance : ToJson ByteArray := ⟨fun b => toJson b.data⟩
instance : FromJson ByteArray := ⟨fun j => return ⟨← fromJson? j⟩⟩
instance : ToJson UInt64 := ⟨fun n => toJson n.toNat⟩
instance : FromJson UInt64 := ⟨fun j => do
  let n ← j.getNat?
  if n < 2^64 then return UInt64.ofNat n else throw "uint64 overflow"⟩
instance : FromJson SignedGrainPackage := ⟨fun j => return ⟨← j.getObjValAs? _ "publisher", ← j.getObjValAs? _ "code", ← j.getObjValAs? _ "signature", ← j.getObjValAs? _ "programDigest"⟩⟩
instance : ToJson SignedGrainPackage := ⟨fun x => Json.mkObj [("publisher", toJson x.publisher), ("code", toJson x.code), ("signature", toJson x.signature), ("programDigest", toJson x.programDigest)]⟩
instance : FromJson VarEntry := ⟨fun j => return ⟨← j.getObjValAs? _ "pathBytes", ← j.getObjValAs? _ "contents"⟩⟩
instance : ToJson VarEntry := ⟨fun x => Json.mkObj [("pathBytes", toJson x.pathBytes), ("contents", toJson x.contents)]⟩
instance : FromJson Obend.Polis.Custody.PrepaidLease := ⟨fun j => return ⟨← j.getObjValAs? _ "leaseId", ← j.getObjValAs? _ "startPeriod", ← j.getObjValAs? _ "nextDue", ← j.getObjValAs? _ "rent", ← j.getObjValAs? _ "initialBudget", ← j.getObjValAs? _ "remaining", ← j.getObjValAs? _ "drawn"⟩⟩
instance : ToJson Obend.Polis.Custody.PrepaidLease := ⟨fun x => Json.mkObj [("leaseId", toJson x.leaseId), ("startPeriod", toJson x.startPeriod), ("nextDue", toJson x.nextDue), ("rent", toJson x.rent), ("initialBudget", toJson x.initialBudget), ("remaining", toJson x.remaining), ("drawn", toJson x.drawn)]⟩
instance : FromJson SettlementLedger := ⟨fun j => return ⟨← j.getObjValAs? _ "lease", ← j.getObjValAs? _ "records"⟩⟩
instance : ToJson SettlementLedger := ⟨fun x => Json.mkObj [("lease", toJson x.lease), ("records", toJson x.records)]⟩
instance : FromJson GrainCustodyAnchor := ⟨fun j => return ⟨← j.getObjValAs? _ "generation", ← j.getObjValAs? _ "packageDigest", ← j.getObjValAs? _ "varDataRoot", ← j.getObjValAs? _ "receiptHead", ← j.getObjValAs? _ "leaseRoot", ← j.getObjValAs? _ "ingressRoot"⟩⟩
instance : ToJson GrainCustodyAnchor := ⟨fun x => Json.mkObj [("generation", toJson x.generation), ("packageDigest", toJson x.packageDigest), ("varDataRoot", toJson x.varDataRoot), ("receiptHead", toJson x.receiptHead), ("leaseRoot", toJson x.leaseRoot), ("ingressRoot", toJson x.ingressRoot)]⟩
/-- This host has no powerbox or ingress CLI; reject archives from those unsupported extensions. -/
instance : FromJson GrainArchive := ⟨fun j => do
  let extensions ← j.getObjValAs? (List Json) "extensions"
  if !extensions.isEmpty then throw "unsupported custody extensions"
  return {
    package := ← j.getObjValAs? _ "package", entries := ← j.getObjValAs? _ "entries",
    anchor := ← j.getObjValAs? _ "anchor", previousHead := ← j.getObjValAs? _ "previousHead",
    frozenGrain := ⟨← nat j "grainId", #[]⟩, lease := ← j.getObjValAs? _ "lease",
    settlements := ← j.getObjValAs? _ "settlements", ingress := IngressMmr.empty,
    executions := [], transitionSignature := ← j.getObjValAs? _ "transitionSignature" }⟩
instance : ToJson GrainArchive := ⟨fun a => Json.mkObj [
  ("package", toJson a.package), ("entries", toJson a.entries), ("anchor", toJson a.anchor),
  ("previousHead", toJson a.previousHead), ("grainId", toJson a.frozenGrain.grain), ("extensions", .arr #[]),
  ("lease", toJson a.lease), ("settlements", toJson a.settlements), ("transitionSignature", toJson a.transitionSignature)]⟩
def custodyFiles (dir : System.FilePath) : IO (Array VarEntry) := do
  let mut entries := #[]
  for e in ← (dir / "var").readDir do
    if ← e.path.isDir then throw (IO.userError "custody var entries must be regular files")
    entries := entries.push ⟨e.fileName.toUTF8.toList, ← IO.FS.readBinFile e.path⟩
  return entries
def custodySave (dir : System.FilePath) (s : GrainCustodyHost) : IO Unit := do
  -- WAL first: interrupted installation leaves the authenticated one-ahead image recoverable.
  let writes := if s.wal.isSome then [("wal", toJson s.wal), ("durable", toJson s.durable), ("volatile", toJson s.volatile)]
    else [("durable", toJson s.durable), ("volatile", toJson s.volatile), ("wal", Json.null)]
  for (name, j) in writes do
    let path := dir / (name ++ ".json")
    IO.FS.writeFile (dir / (name ++ ".pending")) j.compress
    IO.FS.rename (dir / (name ++ ".pending")) path
def custody (cmd dirName : String) (args : List String) : IO UInt32 := do
  let dir := System.FilePath.mk dirName
  let mut epoch := 0
  let mut grain := 0
  let mut nextEpoch : Option Nat := none
  if cmd == "init" || cmd == "prepare" then
    let mut rest := args
    while !rest.isEmpty do
      let flag :: value :: tail := rest | throw (IO.userError "custody option needs a value")
      let parsed := if flag == "--grain-id" && value.length == 64 then (unhex256 value).toOption else value.toNat?
      let n ← decodeIO (match parsed with | some n => .ok n | none => .error "expected natural number or 64-digit grain hex")
      match flag with
      | "--epoch" => epoch := n
      | "--grain-id" => grain := n
      | "--next-epoch" => nextEpoch := some n
      | _ => throw (IO.userError ("unknown custody option " ++ flag))
      rest := tail
  if cmd == "init" then
    if ← (dir / "durable.json").pathExists then return ← finish [] false (verdict false "custody already initialized")
    IO.FS.createDirAll (dir / "var")
    let h ← IO.FS.Handle.mk "/dev/urandom" .read
    let bytes ← h.read 96
    if bytes.size != 96 then throw (IO.userError "cannot obtain signing randomness")
    let sk : PqSecretKey := ⟨bytes.toList.take 32, (bytes.toList.drop 32).take 32, bytes.toList.drop 64⟩
    IO.FS.writeFile (dir / "signing-key.json") (toJson sk).compress
    let permissions ← IO.Process.output { cmd := "chmod", args := #["600", (dir / "signing-key.json").toString] }
    if permissions.exitCode != 0 then throw (IO.userError permissions.stderr)
  let sk : PqSecretKey ← decodeIO (fromJson? (← load (dir / "signing-key.json").toString))
  let params := thincsCustody128Params
  let pk := derivePublicKey cshake256Suite params sk
  let sign := fun (msg : ByteArray) => match Obend.Crypto.ThresholdHashMpc.evalCutBatchSign cshake256Suite params sk msg.toList [] 0 10000 with
    | none => ByteArray.empty | some sig => (toJson sig).compress.toUTF8
  let verify := fun (msg sig : ByteArray) => match String.fromUTF8? sig >>= fun s => (Json.parse s >>= fromJson? (α := PqHashSig)).toOption with
    | none => false | some sig => verifyPqHashSig cshake256Suite params pk msg.toList sig
  let auth := fun p => verify (packageDigest p) p.signature
  let entries ← custodyFiles dir
  let liveRoot := computeVarDataRootExec entries
  let mut s : GrainCustodyHost ← if cmd == "init" then do
      let p : SignedGrainPackage := ⟨(toJson pk).compress.toUTF8, "custody".toUTF8, ByteArray.empty, ByteArray.empty⟩
      let p := { p with signature := sign (packageDigest p) }
      let lease := Obend.Polis.Custody.openLease 0 0 0 0
      let a := sealArchive sign {
        package := p, entries := entries.toList,
        anchor := ⟨epoch, ByteArray.empty, liveRoot, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩,
        previousHead := ByteArray.empty, frozenGrain := ⟨grain, #[]⟩, lease := lease,
        settlements := ⟨lease, []⟩, ingress := IngressMmr.empty, executions := [], transitionSignature := ByteArray.empty }
      pure (⟨a, none, some a⟩ : GrainCustodyHost)
    else do
      pure (⟨← decodeIO (fromJson? (← load (dir / "durable.json").toString)),
        ← decodeIO (fromJson? (← load (dir / "wal.json").toString)),
        ← decodeIO (fromJson? (← load (dir / "volatile.json").toString))⟩ : GrainCustodyHost)
  let candidate := s.wal.getD s.durable
  let status := reopenCustody auth verify (some {candidate with entries := entries.toList}) (some s.durable.anchor)
  let status := if s.wal.isNone then status else
    (match reopenCustody auth verify (some s.durable) (some s.durable.anchor) with | .ready => status | bad => bad)
  if status != .ready && status != .recoveryRequired then
    s := { s with volatile := none }
    custodySave dir s
    return ← finish [] false (verdict false (reprStr status))
  match cmd with
  | "init" => pure ()
  | "prepare" =>
    if nextEpoch.isSome && nextEpoch != some (s.durable.anchor.generation + 1) then return ← finish [] false (verdict false "next epoch must be exactly one ahead")
    let some next := prepareCustody auth verify sign s | return ← finish [] false (verdict false "pending WAL or missing volatile state")
    s := next
  | "reopen" =>
    if !args.isEmpty then throw (IO.userError "reopen takes only DIR")
    s := custodyEvent auth verify s .restart
  | "event" =>
    let event ← decodeIO (match args with
      | ["crash"] => .ok CustodyHostEvent.crash
      | ["restart"] => .ok .restart
      | ["settle", p] => match p.toNat? with | some n => .ok (.settle n) | none => .error "invalid period"
      | _ => .error "custody events: crash | restart | settle PERIOD")
    if let .settle period := event then
      let some a := s.volatile | return ← finish [] false (verdict false "no volatile custody state")
      if (settleOrReplay a.settlements period).records == a.settlements.records then
        return ← finish [] false (verdict false "settlement period refused or already settled")
    s := custodyEvent auth verify s event
  | _ => throw (IO.userError "custody commands: init | prepare | reopen | event")
  custodySave dir s
  finish [] true ((verdict true (reprStr status)).setObjVal! "varDataRootHex" (toJson (byteArrayToHex liveRoot)))
open Obend.Crypto Obend.Judge Obend.Ledger
instance : FromJson Rat := ⟨rat⟩
instance : FromJson Side := ⟨fun j => do
  match ← j.getStr? with | "bid" => return .bid | "ask" => return .ask | _ => throw "expected bid or ask"⟩
instance : FromJson Goldilocks := ⟨fun j => do
  let n ← j.getNat?
  if h : n < Obend.Apps.ZkNtt.goldilocksPrime then return ⟨n, h⟩ else throw "noncanonical field element"⟩
instance {α : Type} [FromJson α] {d : Nat} : FromJson (Obend.Crypto.Fast.Sized α d) := ⟨fun j => do
  let xs : Array α ← fromJson? j
  if h : xs.size = d then return ⟨xs, h⟩ else throw "polynomial dimension mismatch"⟩
instance : FromJson AjtaiParams := ⟨fun j => do
  let rows ← nat j "rows"; let cols ← nat j "cols"; let modulus ← nat j "modulus"
  let matrix : List (List Int) ← j.getObjValAs? _ "matrix"
  if h : 0 < rows ∧ 0 < modulus ∧ matrix.length = rows ∧ ∀ row ∈ matrix, row.length = cols then
    return ⟨rows, cols, h.1, modulus, h.2.1, matrix, h.2.2.1, h.2.2.2⟩
  else throw "Ajtai rows, modulus or matrix dimensions"⟩
instance : FromJson GoldilocksExt2 := ⟨fun j => return ⟨← j.getObjValAs? _ "c0", ← j.getObjValAs? _ "c1"⟩⟩
instance : FromJson Obend.Analysis.Interval := ⟨fun j => return ⟨← j.getObjValAs? _ "lo", ← j.getObjValAs? _ "hi"⟩⟩
instance : FromJson Obend.Analysis.TaylorModel := ⟨fun j => return ⟨← j.getObjValAs? _ "coeffs", ← j.getObjValAs? _ "center", ← j.getObjValAs? _ "domain", ← j.getObjValAs? _ "rem"⟩⟩
instance : FromJson TraderUtilityCert := ⟨fun j => return ⟨← j.getObjValAs? _ "tm", ← j.getObjValAs? _ "feature", ← j.getObjValAs? _ "tickScale", ← j.getObjValAs? _ "side", ← j.getObjValAs? _ "submittedTotal"⟩⟩
instance : FromJson RlweParams := ⟨fun j => return ⟨← j.getObjValAs? _ "d", ← j.getObjValAs? _ "q", ← j.getObjValAs? _ "t"⟩⟩
instance : FromJson ThresholdDecryptConfig := ⟨fun j => return ⟨← j.getObjValAs? _ "params", ← j.getObjValAs? _ "quorum", ← j.getObjValAs? _ "encNoiseBound", ← j.getObjValAs? _ "smudgeBound", ← j.getObjValAs? _ "secBits"⟩⟩
instance : FromJson OrderBitWitness := ⟨fun j => return ⟨← j.getObjValAs? _ "qtyBits", ← j.getObjValAs? _ "totalBits", ← j.getObjValAs? _ "salt"⟩⟩
instance : FromJson Market := ⟨fun j => return ⟨← j.getObjValAs? _ "currency", ← j.getObjValAs? _ "goods", ← j.getObjValAs? _ "epsilon"⟩⟩
instance : FromJson ResourcePosting := ⟨fun j => return ⟨← j.getObjValAs? _ "source", ← j.getObjValAs? _ "destination", ← j.getObjValAs? _ "asset", ← j.getObjValAs? _ "amount"⟩⟩
instance : FromJson Certificate := ⟨fun j => return ⟨← j.getObjValAs? _ "price", ← j.getObjValAs? _ "potentials", ← j.getObjValAs? _ "slacks"⟩⟩
instance {d : Nat} : FromJson (SableLinearWitness d) := ⟨fun j => return ⟨← j.getObjValAs? _ "weights", ← j.getObjValAs? _ "features", ← j.getObjValAs? _ "bias"⟩⟩
instance {d : Nat} : FromJson (RlweCiphertext d) := ⟨fun j => return ⟨← j.getObjValAs? _ "c0", ← j.getObjValAs? _ "c1"⟩⟩
instance {d : Nat} : FromJson (PartialDecryptionShare d) := ⟨fun j => return ⟨← j.getObjValAs? _ "guardianId", ← j.getObjValAs? _ "sharePoly"⟩⟩
def bazaarBatch (cfg : ThresholdDecryptConfig) (dim : Nat) (j : Json) : Except String (DarkBazaarEpochBatch dim cfg) := do
  let pp : AjtaiParams ← j.getObjValAs? _ "ajtaiParams"
  let orders ← (← field j "orders").getArr?
  let ws : List OrderBitWitness ← orders.toList.mapM (fun o => o.getObjValAs? _ "witness")
  let specs ← (orders.toList.zip ws).mapM fun (o, w) => do
    return commitPrivateOrder pp (← nat o "account") (← o.getObjValAs? Side "side") (← nat o "maxBits") w.salt w
  return { epochNullifier := ← nat j "epochNullifier"
           utilityCerts := ← orders.toList.mapM (fun o => o.getObjValAs? _ "utility")
           sableWitnesses := ← orders.toList.mapM (fun o => o.getObjValAs? _ "sable")
           encryptedOrders := ← orders.toList.mapM (fun o => o.getObjValAs? _ "ciphertext")
           thresholdShares := ← j.getObjValAs? _ "thresholdShares"
           openingQuery := ⟨← j.getObjValAs? _ "market", pp, cfg.encNoiseBound, cfg.smudgeBound, cfg.secBits, specs, 0, 2^128⟩
           openingWitness := ⟨ws, ← j.getObjValAs? _ "transfers", ← j.getObjValAs? _ "kkt"⟩ }
def bazaar (path : String) (args : List String) : IO UInt32 := do
  let (receipt, args) := takeOpt "--zk-receipt" args
  let (key, args) := takeOpt "--root-secret" args
  if receipt.isSome != key.isSome || (args != [] && !(args.length == 2 && args.head? == some "--out")) then
    throw (IO.userError "usage: bazaar clear INPUT [--zk-receipt RECEIPT.cbor --root-secret KEY.bin] [--out FILE]")
  let j ← load path
  let cfg : ThresholdDecryptConfig ← decodeIO (j.getObjValAs? _ "config")
  let dim ← decodeIO (nat j "sableDim")
  let committee ← decodeIO (j.getObjValAs? (List Nat) "committee")
  let budget ← decodeIO (nat j "budget")
  let historyPath := path ++ ".state.json"
  let history ← if ← (System.FilePath.mk historyPath).pathExists then load historyPath else pure (.arr #[])
  let previous ← decodeIO history.getArr?
  let mut st : DarkBazaarAuthState := ⟨DarkBazaarState.init budget, committee, []⟩
  for prior in previous do
    if (field prior "config").toOption != (field j "config").toOption || (field prior "committee").toOption != (field j "committee").toOption || (field prior "budget").toOption != (field j "budget").toOption then
      return ← finish args false (verdict false "persistent market context mismatch")
    let b ← decodeIO (bazaarBatch cfg dim prior)
    match stepDarkBazaarEpochAuth cfg st b with
    | .error e => return ← finish args false (verdict false (reprStr e))
    | .ok (next, _) => st := next
  let b ← decodeIO (bazaarBatch cfg dim j)
  match stepDarkBazaarEpochAuth cfg st b with
  | .error e => finish args false (verdict false (reprStr e))
  | .ok (next, out) =>
    -- Only a clearing every Lean stage accepted reaches the Rust prover. Its receipt attests the
    -- dark_bazaar organ's authority envelope at this epoch and nullifier, not the clearing itself.
    let mut attested : List (String × Json) := []
    if let (some receiptPath, some keyPath) := (receipt, key) then
      let rc ← zk "prove" ["--target-organ", "dark_bazaar", "--root-secret", keyPath, "--epoch", toString next.base.epoch,
        "--nonce", toString b.epochNullifier, "--out", receiptPath] true
      if rc != 0 then
        IO.eprintln "refused: obend-zk-receipt issued no dark_bazaar authority receipt"
        return rc
      attested := [("zkAuthorityReceipt", toJson receiptPath), ("zkReceiptStatement", toJson "organ-authority-envelope(dark_bazaar)")]
    IO.FS.writeFile (historyPath ++ ".pending") (Json.arr (previous.push j)).compress
    IO.FS.rename (historyPath ++ ".pending") historyPath
    let digest := deriveOrderBatchNullifier256 b.openingQuery.market b.openingQuery.committedOrders b.encryptedOrders
    finish args true (Json.mkObj ([("status", toJson "accepted"), ("epoch", toJson next.base.epoch),
      ("nullifierHex", toJson (bytesToHex (Obend.Digest.HashBytes.be 32 digest.toNat))),
      ("decryptedBook", toJson out.decryptedBook.coeffs), ("currency", toJson out.currencySettlement.entries),
      ("goods", toJson out.goodsSettlement.entries)] ++ attested))
section
open Obend.Doc.WorkbookEngine (RedactedWorkbook ExportedWorkbookCell CachedWorkbookCell WorkbookSection CellVisibility
  projectWorkbookForViewer verifyRedactedWorkbook)
open Obend.Doc.Reactive (Opcode)
instance : ToJson (BitVec 256) := ⟨fun b => toJson (hex256 b.toNat)⟩
instance : FromJson (BitVec 256) := ⟨fun j => return BitVec.ofNat 256 (← unhex256 (← j.getStr?))⟩
def opName : Opcode → String | .literal => "literal" | .input => "input" | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"
/-- A cell a viewer is cleared for, whole: what `verifyRedactedWorkbook` re-evaluates and re-commits. -/
def cachedJson (c : CachedWorkbookCell) : Json :=
  let (w, s, r) := (c.entry, c.entry.structured, c.entry.reactive)
  Json.mkObj [("cellKey", toJson w.cellKey), ("citedKeys", toJson w.citedKeys), ("values", toJson c.result.values),
    ("receiptHex", toJson c.result.receipt), ("visibility", match w.visibility with
      | .publicCell => toJson "public"
      | .sealedPrivate tag salt => Json.mkObj [("sealed", toJson tag), ("saltHex", toJson salt)]),
    ("structured", Json.mkObj [("id", toJson s.id), ("kind", toJson s.kind.toLabel), ("ast", Obend.Spec.DataWire.dataJson s.ast),
      ("pins", toJson s.pins), ("receipt", toJson s.receipt)]),
    ("reactive", Json.mkObj [("id", toJson r.id), ("kind", toJson r.kind.toLabel), ("reads", toJson r.reads), ("defs", toJson r.defs),
      ("note", toJson r.note), ("body", toJson (r.body.map (·.map fun i => Json.mkObj [("op", toJson (opName i.op)), ("arg", toJson i.arg)])))])]
def cachedOf (j : Json) : Except String CachedWorkbookCell := do
  let kind := fun (o : Json) => do
    match Obend.Doc.ProjectionKind.ofLabel (← text o "kind") with | some k => pure k | none => throw "unknown projection kind"
  let s ← field j "structured"
  let r ← field j "reactive"
  let visibility ← match ← field j "visibility" with
    | .str "public" => pure CellVisibility.publicCell
    | v => pure (.sealedPrivate (← text v "sealed") (← v.getObjValAs? _ "saltHex"))
  let body ← (← r.getObjValAs? (List (List Json)) "body").mapM (·.mapM fun i => do
    let name ← text i "op"
    match [Opcode.literal, .input, .add, .sub, .mul, .div].find? (opName · == name) with
    | some op => pure (⟨op, ← i.getObjValAs? Int "arg"⟩ : Obend.Doc.Reactive.Instruction) | none => throw "unknown opcode")
  return ⟨⟨← text j "cellKey", ⟨← text s "id", ← kind s, ← field s "ast" >>= Obend.Spec.DataWire.decodeData 64,
      ← s.getObjValAs? _ "pins", ← s.getObjValAs? _ "receipt"⟩,
    ⟨← nat r "id", ← kind r, ← r.getObjValAs? _ "reads", ← r.getObjValAs? _ "defs", body, ← text r "note"⟩,
    ← j.getObjValAs? _ "citedKeys", visibility⟩, ⟨← j.getObjValAs? _ "values", ← j.getObjValAs? _ "receiptHex"⟩⟩
def redactedSchema := "obend.cli.workbook_redacted.v1"
/-- The proof-carrying export. A redacted entry carries its id, key, kind label and exported names,
its commitment and its opening: no cached cell, value, AST, body or salt. -/
def redactedJson (rwb : RedactedWorkbook) : Json := Json.mkObj [("schema", toJson redactedSchema), ("title", toJson rwb.title),
  ("sections", toJson (rwb.sections.map fun s => Json.mkObj [("sectionKey", toJson s.sectionKey), ("markdown", toJson s.markdown),
    ("blocks", toJson s.blocks)])), ("merkleRootHex", toJson (hex256 rwb.merkleRoot)),
  ("entries", toJson (rwb.entries.map fun e => Json.mkObj ((match e with
    | .visible c _ _ => [("mode", toJson "visible"), ("cached", cachedJson c)]
    | .redacted cid ck kind defs _ _ => [("mode", toJson "redacted"), ("cellId", toJson cid), ("cellKey", toJson ck),
        ("kind", toJson kind.toLabel), ("exportedDefs", toJson defs)]) ++
    [("commitmentHex", toJson e.commitmentOf), ("opening", Json.mkObj [("size", toJson e.openingOf.size),
      ("index", toJson e.openingOf.index), ("valueHex", toJson (hex256 e.openingOf.value)),
      ("pathHex", toJson (e.openingOf.path.map hex256))])])))]
def redactedOf (j : Json) : Except String RedactedWorkbook := do
  if (← text j "schema") != redactedSchema then throw "unknown redacted workbook schema"
  let sections ← (← j.getObjValAs? (List Json) "sections").mapM fun s =>
    return (⟨← text s "sectionKey", ← text s "markdown", ← s.getObjValAs? _ "blocks"⟩ : WorkbookSection)
  let entries ← (← j.getObjValAs? (List Json) "entries").mapM fun e => do
    let cm : BitVec 256 ← e.getObjValAs? _ "commitmentHex"
    let o ← field e "opening"
    let op : Obend.Receipt.Merkle.Opening := ⟨← nat o "size", ← nat o "index", ← text o "valueHex" >>= unhex256,
      ← (← o.getObjValAs? (List String) "pathHex").mapM unhex256⟩
    match ← text e "mode" with
    | "visible" => pure (ExportedWorkbookCell.visible (← field e "cached" >>= cachedOf) cm op)
    | "redacted" => match Obend.Doc.ProjectionKind.ofLabel (← text e "kind") with
      | some kind => pure (.redacted (← nat e "cellId") (← text e "cellKey") kind (← e.getObjValAs? _ "exportedDefs") cm op)
      | none => throw "unknown projection kind"
    | _ => throw "entry mode must be visible or redacted"
  return ⟨← text j "title", sections, ← text j "merkleRootHex" >>= unhex256, entries⟩
/-- `notebook verify`: the entries' commitments must be exactly the leaves of the stated root (an
export with entries left out is refused), and the engine's verifier must accept the schedule. -/
def notebookVerify (j : Json) (args : List String) : IO UInt32 := do
  let rwb ← decodeIO (redactedOf j)
  let H := Obend.Core.Digest.deployed
  let covered := Obend.Receipt.Merkle.mapRoot H (rwb.entries.map (·.commitmentOf.toNat)) == rwb.merkleRoot
  let ok := covered && verifyRedactedWorkbook Obend.Doc.Reactive.scientificKernel H rwb
  finish args ok ((verdict ok (if ok then "openings, commitments and visible cells verified" else if covered then
    "an opening, commitment or visible cell does not verify" else "the entries are not the leaves of the Merkle root"))
    |>.setObjVal! "merkleRootHex" (toJson (hex256 rwb.merkleRoot)) |>.setObjVal! "entries" (toJson rwb.entries.length))
def notebook (cmd : String) (j : Json) (args : List String) : IO UInt32 := do
  let mut wb := Obend.FFI.defaultSessionWorkbook
  let mut response := Json.null
  let requests ← decodeIO (match field j "requests" with
    | .ok xs => xs.getArr?
    | .error _ => match j with
      | .arr cells => .ok #[Json.mkObj [("op", toJson "init"), ("cells", .arr cells)]]
      | _ => .ok #[if (text j "op").isOk then j else j.setObjVal! "op" (toJson "init")])
  for request in requests do
    match Obend.FFI.stepWorkbookJsonBytes wb request.compress.toUTF8 with
    | .error (_, e) => return ← finish [] false (verdict false e)
    | .ok (next, bytes) =>
      wb := next
      response ← decodeIO (Json.parse (String.fromUTF8! bytes))
  if cmd == "eval" then return ← finish args true (response.setObjVal! "requests" (.arr requests))
  let (viewer, opts) := takeOpt "--viewer" args
  let (salt, opts) := takeOpt "--salt" opts
  let some clearance := viewer.bind String.toNat? | throw (IO.userError "project requires --viewer NAT [--salt NAT] [--out FILE]")
  if let some value := salt then
    let some salt := value.toNat? | throw (IO.userError "salt must be a natural number")
    wb := { wb with cells := wb.cells.map fun c => { c with entry := { c.entry with visibility :=
      match c.entry.visibility with | .publicCell => .publicCell | .sealedPrivate tag _ => .sealedPrivate tag (BitVec.ofNat 256 salt) } } }
  output opts (redactedJson (projectWorkbookForViewer Obend.Core.Digest.deployed
    ((List.range clearance).map fun n => toString (n + 1)) wb))
  return 0
end

end LiveCli

def subUsage (cmd : String) : String := "usage: obend " ++ cmd ++ " " ++ match cmd with
  | "amend" => "live|trace INPUT [--out FILE] | zk-prove|zk-verify|zk-bench|zk-tamper-test ARGS"
  | "custody" => "init DIR [--grain-id N] [--epoch N] | prepare DIR [--next-epoch N] | reopen DIR | event DIR crash|restart|settle [PERIOD]"
  | "mpc" => "sign INPUT [--out FILE] | verify SIGNATURE"
  | "bazaar" => "clear INPUT [--zk-receipt RECEIPT.cbor --root-secret KEY.bin] [--out FILE] (replay state: INPUT.state.json)"
  | "pde" => "check INPUT [--out CERT] | solve INPUT [--out CERT] [--emit-wgsl DIR] [--emit-sv FILE] [--emit-lec FILE]"
  | "notebook" => "eval INPUT [--out STATE] | project STATE --viewer N [--salt N] [--out REDACTED] | verify REDACTED [--out VERDICT]"
  | "run" | "run-core" => "FILE [ENTRY] [--jit|--jit=cc] [--emit-c99 FILE]"
  | _ => "(see obend --help)"
def refuseUsage (cmd : String) : IO UInt32 := do IO.eprintln ("refused: " ++ subUsage cmd); return 2

/-! ## Dispatch -/

def dispatch (args : List String) : IO UInt32 :=
  let args := match args with
    | "check" :: "--obligations" :: "--package" :: rest => "check" :: "--obligations" :: rest
    | cmd :: "--package" :: rest => if ["check", "prove", "ground", "emit", "specialize"].contains cmd then cmd :: rest else args
    | cmd :: "--emit-c99" :: out :: path :: rest =>
      if cmd == "run" || cmd == "run-core" then cmd :: path :: (rest ++ ["--emit-c99", out]) else args
    | cmd :: flag :: path :: rest =>
      if (cmd == "run" || cmd == "run-core") && (flag == "--jit" || flag == "--jit=cc") then cmd :: path :: (rest ++ [flag]) else args
    | _ => args
  match args with
  | ["--help"] | ["-h"] | ["help"] => do IO.println usage; return 0
  | [cmd, "--help"] | [cmd, "-h"] => do IO.println (subUsage cmd); return 0
  | "amend" :: cmd :: rest =>
    if cmd.startsWith "zk-" then LiveCli.zk (cmd.drop 3).toString rest else
    match cmd, rest with
    | "live", p :: opts => do LiveCli.amend false (← LiveCli.load p) opts
    | "trace", p :: opts => do LiveCli.amend true (← LiveCli.load p) opts
    | _, _ => refuseUsage "amend"
  | "notebook" :: cmd :: p :: opts => do
    if cmd == "verify" then return ← LiveCli.notebookVerify (← LiveCli.load p) opts
    if cmd != "eval" && cmd != "project" then return ← refuseUsage "notebook"
    LiveCli.notebook cmd (← LiveCli.load p) opts
  | "bazaar" :: "clear" :: p :: opts => LiveCli.bazaar p opts
  | "custody" :: cmd :: dir :: opts => LiveCli.custody cmd dir opts
  | "mpc" :: cmd :: p :: opts => do
    if cmd != "sign" && cmd != "verify" then return ← refuseUsage "mpc"
    LiveCli.mpc (cmd == "sign") (← LiveCli.load p) opts
  | "pde" :: cmd :: p :: opts => do
    if cmd != "check" && cmd != "solve" then return ← refuseUsage "pde"
    LiveCli.pde (cmd == "solve") (← LiveCli.load p) opts
  | ["identity"] => do IO.println identityJson.compress; return 0
  | ["parse", path] => parseCommand path
  | ["capture", spec, dir] => captureCommand spec dir false
  | ["capture", spec, dir, "--objective-edition-1"] => captureCommand spec dir true
  | "elaborate" :: capture :: prefix_ :: rest => do
    let a := rest.getD 0 "[]"
    let projections := rest.getD 1 "[]"
    let limits := rest.getD 2 "{\"heap\":\"100000\",\"stack\":\"100000\",\"ticks\":\"100000\"}"
    let mode := rest.getD 3 "application"
    if rest.length > 4 then IO.eprintln usage; return 2
    elaborateCommand capture prefix_ a projections limits mode
  | ["preview", request, dir] => previewCommand request dir
  | ["batch", jobs, out] => batchCommand jobs out
  | ["check-core", path] => Obend.Elab.Gate.checkPacketFile path
  | "run-core" :: path :: rest =>
    match parseOptions rest {} with
    | .ok options => runPacket path options
    | .error message => do IO.eprintln message; return (if message.startsWith "refused" then 2 else 1)
  | ["check", "--obligations", spec, "--object", entry] => obligationsCommand spec entry none
  | ["check", "--obligations", spec, "--object", entry, "--receipts", dir] => obligationsCommand spec entry (some dir)
  | "prove" :: spec :: name :: rest => (proveArgs spec name rest).getD usage64
  | ["ground", spec, entry, expected] => groundCommand spec entry expected
  | "emit" :: spec :: "--object" :: entry :: "--out" :: out :: rest => ((leafCall rest).map (emitCommand spec entry out)).getD usage64
  | "specialize" :: spec :: "--object" :: entry :: "--book" :: book :: rest =>
    ((leafCall rest).map (specializeCommand spec entry book)).getD usage64
  | ["check", file] => checkSource (packageOfSpec file none)
  | ["check", file, entry] => checkSource (packageOfSpec file (some entry))
  | "run" :: "--package" :: spec :: rest => runSource (packageOfSpec spec none) rest
  | ["admit", "--package", spec, turn] => admitCommand spec turn
  | ["judge", "--package", spec, old, new] => judgeCommand spec old new
  | "run" :: file :: "--entry" :: entry :: rest => runSource (packageOfSpec file (some entry)) rest
  | "run" :: file :: entry :: rest => runSource (packageOfSpec file (some entry)) rest
  | ["run", file] => runSource (packageOfSpec file none) []
  | "verify" :: path :: rest =>
    Obend.Ledger.Cli.verifyOr path rest <|
      Obend.Analysis.Cli.verifyOr path <|
        Obend.Hardware.Cli.verifyOr path
          ((Obend.Receipt.Cli.main? ("verify" :: path :: rest)).getD usage64)
  | "analyze" :: _ => (Obend.Analysis.Cli.main? args).getD usage64
  | "lower" :: _ => (Obend.Lower.Cli.main? args).getD usage64
  | _ => if ["amend", "custody", "bazaar", "mpc", "pde", "notebook"].contains (args.headD "") then refuseUsage (args.headD "")
    else ((Obend.Receipt.Cli.main? args).orElse fun _ => (Obend.Ledger.Cli.main? args).orElse fun _ =>
      (Obend.Hardware.Cli.main? args).orElse fun _ => (Obend.Judge.GenealogyCli.main? args).orElse fun _ =>
      (Obend.Vault.BranchCli.main? args).orElse fun _ => Obend.Vault.Cli.main? args).getD usage64

def safeDispatch (args : List String) : IO UInt32 := do
  try dispatch args
  catch e =>
    IO.eprintln ("refused: " ++ e.toString)
    return 2

public section
/-- Every command, then what it cost (`Obend.Vault.Cost`: said only when `OBEND_COST` is set). -/
public def main (args : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  try safeDispatch args
  finally
    let words := args.filter (fun a => !a.startsWith "-")
    let cmd := match words with
      | w :: v :: _ => if w == "ledger" || w == "branch" || w == "report" then w ++ " " ++ v else w
      | [w] => w
      | [] => ""
    Obend.Vault.Cost.emit ((← IO.monoMsNow) - t0) cmd
