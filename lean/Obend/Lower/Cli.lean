module
/-
# Obend.Lower.Cli — `obend lower NAME` / `obend lower --transport THM`

    obend lower NAME [--module M] [--arg N] [--out DIR] [--emit BOOK.json] [--rtl OUT.sv]
        import the built module M (default `Programs`, `tests/lower/Programs.lean`, built by
        `lake build LowerPrograms`; run from `lean/`), read the declaration NAME into Lean-lite (`Fragment.read`; refused with the reason
        when it is outside the fragment), lower it, run Core4's checker on it at the type its Lean type
        lowers to (with the annotations `annotate` computes), and print the Core4 term. With `--out`,
        write `DIR/NAME.code.json` (the held term, its annotation tree and assumptions: a `Code` when the
        checker accepted it) and `DIR/NAME.lower.json` (the `lower@1` certificate: the source's wire form,
        its digest, the lowered term). With `--arg N`, run `NAME N` on the demand machine. With
        `--emit`, emit the one-layer composition holding the lowered program as a Leaf book
        (`Obend.Lower.leanComposition`, `Obend.Leaf.emit`), write it, and with `--arg` run the book's
        member too. With `--rtl`, compile the Leaf book via `compileBookToRtlSat` into a verified
        SystemVerilog RTL module, write `OUT.sv`, and with `--arg` simulate `evalModuleOutputs`.
    obend lower --verify CERT.json SOURCE.json
        judge a certificate with the registered `lower@1` format (re-lowering the source): exit 0 when
        accepted, 3 when refused.
    obend lower --transport THM [--module M] [--arg N] [--out DIR]
        read the theorem THM's `Decidable` decision procedure via `Fragment.readTheoremDecider`
        (refusing `sorryAx` or custom axioms), lower it to a `Core4` claim term, judge it with the
        registered `transport@1` format (`checkL` + `nonEmptySplits`), and with `--out` write
        `DIR/THM.transport.json` and `DIR/THM.statement.json`.
    obend lower --verify-transport CERT.json STATEMENT.json
        judge a transported certificate with the registered `transport@1` format: exit 0 when
        accepted, 3 when refused.
-/
public import Lean
public import Obend.Lower.Fragment
public import Obend.Lower.Judge
public import Obend.Lower.Transport
public import Obend.Lower.Proofs.Book
public import Obend.Lower.Proofs.Hardware
public import Obend.Core.Machine
public section
namespace Obend.Lower.Cli
open Lean Meta Elab
open Obend.Core.Term Obend.Core.Ty
open Obend.Core.Check (AnnotatedTerm)
open Obend.Core.Proofs.BidirectionalCompleteness (treeAnnotations AnnotationTree)
open Obend.Hardware.HDL Obend.Hardware.Compiler
set_option autoImplicit false


/-- The run of a closed term on the demand machine, as a ground observation. -/
def machine (t : Obend.Core.Term.Term) : String :=
  match Obend.Core.Machine.runBounded ⟨1000000, 1000000⟩ 10000000 (Obend.Core.Machine.initial t) with
  | .finished (.natural n) _ => toString n
  | .finished (.boolean b) _ => toString b
  | .finished (.variant l _) _ => s!"{l} …"
  | .finished (.record _) _ => "{…}"
  | .finished _ _ => "a value"
  | .suspended _ _ => "suspended (out of fuel)"
  | .divergent _ _ => "divergent"
  | .refused r _ => s!"refused {repr r}"
  | .yielded _ _ => "yielded"

structure Options where
  module : String := "Programs"
  arg : Option Nat := none
  out : Option String := none
  emit : Option String := none
  rtl : Option String := none

def parse : List String → Options → Except String Options
  | [], o => .ok o
  | "--module" :: m :: rest, o => parse rest { o with module := m }
  | "--arg" :: n :: rest, o => match n.toNat? with
    | some n => parse rest { o with arg := some n }
    | none => .error s!"--arg needs a natural, not {n}"
  | "--out" :: d :: rest, o => parse rest { o with out := some d }
  | "--emit" :: b :: rest, o => parse rest { o with emit := some b }
  | "--rtl" :: r :: rest, o => parse rest { o with rtl := some r }
  | flag :: _, _ => .error s!"unknown argument {flag}"

/-- The environment of a built module (`importModules`; the build directory on the search path). -/
def importModule (module : String) : IO Environment := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean"]
  importModules #[{ module := module.toName }] {} (level := .private)

def runMeta {α : Type} (env : Environment) (x : MetaM α) : IO α := do
  let (a, _) ← (x.run' {}).toIO { fileName := "obend-lower", fileMap := default } { env := env }
  return a

def lowerCommand (name : String) (o : Options) : IO UInt32 := do
  let env ← importModule o.module
  let decl := name.toName
  let some info := env.find? decl | do IO.eprintln s!"no declaration {name} in {o.module}"; return 2
  let (read, ty) ← runMeta env do
    let r ← Obend.Lower.Fragment.read (mkConst decl (info.levelParams.map fun _ => Level.zero))
    let t ← Obend.Lower.Fragment.binderTy info.type
    return (r, t)
  let src ← match read with
    | .ok s => pure s
    | .error m => do IO.println s!"refused: outside the fragment: {m}"; return 3
  let term := Obend.Lower.lowerT src
  let tree := Obend.Lower.annotate [] src
  IO.println s!"type: {(repr ty).pretty 1000000000}"
  let verdict := Obend.Core.Bidirectional.checkAgainst ⟨term, treeAnnotations tree, {}⟩ [] ty
  let accepted := match verdict with | .ok _ => true | .error _ => false
  match verdict with
  | .ok _ => IO.println "checked: accepted by checkAgainst (a Code)"
  | .error e => IO.println s!"checked: refused {repr e}"
  IO.println s!"core4: {(repr term).pretty 1000000000}"
  let digest := Obend.Lower.sourceDigest src
  IO.println s!"source digest: {digest}"
  let cert : Obend.Lower.Cert := ⟨digest, term⟩
  match Obend.Lower.format.judge.check 0 src cert with
  | .ok => IO.println "lower@1: accepted"
  | _ => IO.println "lower@1: refused"
  if let some dir := o.out then
    IO.FS.createDirAll dir
    let held : Obend.Core.Code.Held := { term := term, tree := tree, assumptions := {} }
    IO.FS.writeFile s!"{dir}/{name}.code.json" ((Json.mkObj [("checked", toJson accepted), ("type",
      Obend.Spec.DataWire.dataJson (Obend.Core.Code.tyData ty)),
      ("held", Obend.Spec.DataWire.dataJson (Obend.Core.Code.heldData held))]).pretty ++ "\n")
    IO.FS.writeFile s!"{dir}/{name}.lower.json" ((Obend.Lower.certJson cert).pretty ++ "\n")
    IO.FS.writeFile s!"{dir}/{name}.source.json" ((Obend.Lower.sourceJson src).compress ++ "\n")
    IO.println s!"wrote {dir}/{name}.code.json {dir}/{name}.lower.json {dir}/{name}.source.json"
  if let some n := o.arg then
    IO.println s!"machine: {name} {n} = {machine (.app term (.nat n))}"
  if let some bookPath := o.emit then
    let C := Obend.Lower.leanComposition name term
    unless C.closedB do IO.println "refused: the composition is not closed"; return 3
    let B := Obend.Leaf.emit C
    IO.println s!"book: slots {B.slots}, closed {B.closedB}"
    let defs := B.defs.map fun d => Json.mkObj [("member", toJson d.member), ("slot", toJson d.slot),
      ("code", Obend.Logic.termJson d.code)]
    IO.FS.writeFile bookPath ((Json.mkObj [("object", toJson name), ("composition", Obend.Logic.termJson C.code),
      ("slots", toJson B.slots), ("defs", Json.arr defs.toArray)]).pretty ++ "\n")
    IO.println s!"wrote {bookPath}"
    if let some n := o.arg then
      IO.println s!"book: {name} {n} = {machine (.app (.get B.link name) (.nat n))}"
  if let some rtlPath := o.rtl then
    let C := Obend.Lower.leanComposition name term
    unless C.closedB do IO.println "refused: the composition is not closed"; return 3
    let B := Obend.Leaf.emit C
    let some rtlMod := compileBookToRtlSat s!"lean_{name}_rtl" B
      | do IO.println "refused: outside the combinational hardware fragment"; return 3
    unless checkRtlModule rtlMod do
      IO.println "refused: RtlModule failed DAG/CDC verification"
      return 3
    IO.println s!"rtl: module {rtlMod.name} verified (DAG + CDC)"
    IO.FS.writeFile rtlPath (emitModuleSV rtlMod)
    IO.println s!"wrote {rtlPath}"
    if let some n := o.arg then
      let outs := evalModuleOutputs rtlMod (fun _ => BitVec.ofNat 64 n) (fun _ => 0#64)
      match outs with
      | [(_, v)] => IO.println s!"rtl: {name} {n} = {v.toNat}"
      | _ => pure ()
  return 0

def verifyCommand (certPath sourcePath : String) : IO UInt32 := do
  let verdict := Obend.Lower.format.checkBytes 0 (← IO.FS.readFile sourcePath) (← IO.FS.readFile certPath)
  match verdict with
  | .ok => IO.println "lower@1: accepted"; return 0
  | .refused (.judge _) _ => IO.println "lower@1: refused by the judge"; return 3
  | .refused (.malformed m) _ => IO.println s!"lower@1: malformed, {m}"; return 3
  | .uncovered => IO.println "lower@1: uncovered"; return 3

def transportCommand (thmName : String) (o : Options) : IO UInt32 := do
  let env ← importModule o.module
  let decl := thmName.toName
  let res ← runMeta env (Obend.Lower.Fragment.readTheoremDecider decl)
  let (decideExpr, argTys) ← match res with
    | .ok p => pure p
    | .error m => do IO.println s!"refused: {m}"; return 3
  let claim := Obend.Lower.lowerProp decideExpr
  let digest := Obend.Lower.sourceDigest decideExpr
  let obj : Obend.Lower.TransportObj := ⟨decideExpr, argTys⟩
  let cert : Obend.Lower.TransportCert := ⟨digest, claim, argTys, []⟩
  IO.println s!"argTys: {(repr argTys).pretty 1000000000}"
  IO.println s!"claim: {(repr claim).pretty 1000000000}"
  IO.println s!"source digest: {digest}"
  match Obend.Lower.transportCheck 0 obj cert with
  | .ok => IO.println "transport@1: accepted"
  | .refused cl _ => do
    IO.println s!"transport@1: refused ({repr cl})"
    return 3
  | .uncovered => do
    IO.println "transport@1: uncovered"
    return 3
  if let some dir := o.out then
    IO.FS.createDirAll dir
    IO.FS.writeFile s!"{dir}/{thmName}.transport.json" ((Obend.Lower.transportCertJson cert).pretty ++ "\n")
    IO.FS.writeFile s!"{dir}/{thmName}.statement.json" ((Obend.Lower.transportObjJson obj).pretty ++ "\n")
    IO.println s!"wrote {dir}/{thmName}.transport.json {dir}/{thmName}.statement.json"
  if let some n := o.arg then
    IO.println s!"claim: {thmName} {n} = {machine (.app claim (.nat n))}"
  return 0

def verifyTransportCommand (certPath objPath : String) : IO UInt32 := do
  let verdict := Obend.Lower.transportFormat.checkBytes 0 (← IO.FS.readFile objPath) (← IO.FS.readFile certPath)
  match verdict with
  | .ok => IO.println "transport@1: accepted"; return 0
  | .refused (.judge _) _ => IO.println "transport@1: refused by the judge"; return 3
  | .refused (.malformed m) _ => IO.println s!"transport@1: malformed, {m}"; return 3
  | .uncovered => IO.println "transport@1: uncovered"; return 3

/-- The `lower` subcommands, or `none` when `args` is not one. -/
def main? : List String → Option (IO UInt32)
  | ["lower", "--verify", cert, source] => some (verifyCommand cert source)
  | ["lower", "--verify-transport", cert, stmt] => some (verifyTransportCommand cert stmt)
  | "lower" :: "--transport" :: thm :: rest => some (match parse rest {} with
    | .ok o => transportCommand thm o
    | .error m => do IO.eprintln m; return 64)
  | "lower" :: name :: rest => some (match parse rest {} with
    | .ok o => lowerCommand name o
    | .error m => do IO.eprintln m; return 64)
  | _ => none

end Obend.Lower.Cli
end
