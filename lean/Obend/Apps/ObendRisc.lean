module
/-
# Obend.Apps.ObendRisc — Flagship App #1: 3-Layer Open-Recursive RISC Softcore

Elaborates and proves the 3-layer open-recursive RISC softcore (`apps/obend-risc/`):
1. `BaseRiscCore.obend`: In-core instruction bit-slice decoders (`decodeOpcode`, `decodeRd`,
   `decodeFunct3`, `decodeRs1`, `decodeRs2`, `decodeImm12`, `decodeFunct7`) and base RV64I/M
   ALU, branch, jump, and load/store execution.
2. `PrivilegeCsrOverride.obend`: Machine-mode CSR synchronous trap (`ECALL`) and return (`MRET`)
   override layer preempting base/extension execution on trap entry and redirecting `pc` to `mtvec`.
3. `CustomSimdZkExt.obend`: Custom opcode `0x2B` (`43`) SIMD/ZK Goldilocks multiply-accumulate
   extension delegating non-extension opcodes to `super`.
4. `ComposedRiscCpu.obend`: Complete 3-layer open-recursive composition + Fibonacci/MAC test points.

Also formalizes the sequential `always_ff @(posedge clk)` SystemVerilog softcore
`obendRiscCpuRtlModule : RtlModule` (holding `pc`, `mstatus`, `mepc`, `mcause`, `cycle_cnt`, and
`x1..x15` in synchronous hardware registers and driving `imem_addr` and `dmem_addr`/`dmem_wdata`/`dmem_we`),
whose `emitModuleSV` output is compiled by Verilator in `apps/obend-risc/verilator/`.
-/
public import Lean
public import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public import Obend.Spec.Sha256
public import Obend.Logic.Program
public import Obend.Logic.Obligation
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Leaf.Futamura
public import Obend.Spec.CrossPackage
public import Obend.Hardware.HDL
public import Obend.Hardware.Synth
public import Obend.Tactic.Weave
public meta import Lean
public meta import Obend.Core.Term
public meta import Obend.Law
public meta import Obend.Spec.Syntax
public meta import Obend.Spec.Parse
public meta import Obend.Spec.Elaborate
public meta import Obend.Spec.FrontEnd
public meta import Obend.Spec.Capture
public meta import Obend.Spec.Sha256
public meta import Obend.Logic.LateBinding
public meta import Obend.Logic.Claim
public meta import Obend.Logic.Rewrite
public meta import Obend.Logic.Frame
public meta import Obend.Logic.Obligation
public meta import Obend.Logic.Program
public meta import Obend.Leaf.Flatten
public meta import Obend.Leaf.Emit

@[expose] public section
namespace Obend.Apps.ObendRisc

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Spec.CrossPackage
open Obend.Hardware
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Tactic.Weave

set_option autoImplicit false

/-- Local alias allowing `by weave` alongside `by weave_chain` and `by obend_law`. -/
macro "weave" : tactic => `(tactic| weave_chain)

/-! ## 0. Module-Compatible Multi-File `#import_obend` Elaborator -/

def mkRiscByteArrayOfNatList (xs : List Nat) : ByteArray :=
  ByteArray.mk (xs.map UInt8.ofNat).toArray

meta instance : Quote Primitive where
  quote
    | .add         => mkIdent ``Primitive.add
    | .multiply    => mkIdent ``Primitive.multiply
    | .equal       => mkIdent ``Primitive.equal
    | .conjunction => mkIdent ``Primitive.conjunction
    | .labelEqual  => mkIdent ``Primitive.labelEqual
    | .subtract    => mkIdent ``Primitive.subtract
    | .divide      => mkIdent ``Primitive.divide
    | .less        => mkIdent ``Primitive.less
    | .lessEqual   => mkIdent ``Primitive.lessEqual
    | .modulo      => mkIdent ``Primitive.modulo
    | .bitAnd      => mkIdent ``Primitive.bitAnd
    | .bitOr       => mkIdent ``Primitive.bitOr
    | .bitXor      => mkIdent ``Primitive.bitXor
    | .shl         => mkIdent ``Primitive.shl
    | .lshr        => mkIdent ``Primitive.lshr
    | .ashr        => mkIdent ``Primitive.ashr
    | .slt         => mkIdent ``Primitive.slt
    | .qmul32      => mkIdent ``Primitive.qmul32

mutual
  meta partial def quoteRiscTermAux : Term → TSyntax `term
    | .hole n σ =>
      let sArr := (σ.map quoteRiscTermAux).toArray
      Lean.Unhygienic.run `(Term.hole $(quote n) [ $[$sArr],* ])
    | .bound i => Lean.Unhygienic.run `(Term.bound $(quote i))
    | .lam b => Lean.Unhygienic.run `(Term.lam $(quoteRiscTermAux b))
    | .app f a => Lean.Unhygienic.run `(Term.app $(quoteRiscTermAux f) $(quoteRiscTermAux a))
    | .mix l u => Lean.Unhygienic.run `(Term.mix $(quoteRiscTermAux l) $(quoteRiscTermAux u))
    | .fix s i => Lean.Unhygienic.run `(Term.fix $(quoteRiscTermAux s) $(quoteRiscTermAux i))
    | .specification m e => Lean.Unhygienic.run `(Term.specification $(quoteRiscTermAux m) $(quoteRiscTermAux e))
    | .prototype s g => Lean.Unhygienic.run `(Term.prototype $(quoteRiscTermAux s) $(quoteRiscTermAux g))
    | .reflect p => Lean.Unhygienic.run `(Term.reflect $(quoteRiscTermAux p))
    | .metadata p => Lean.Unhygienic.run `(Term.metadata $(quoteRiscTermAux p))
    | .project p => Lean.Unhygienic.run `(Term.project $(quoteRiscTermAux p))
    | .nat n => Lean.Unhygienic.run `(Term.nat $(quote n))
    | .boolean b => Lean.Unhygienic.run `(Term.boolean $(quote b))
    | .label l => Lean.Unhygienic.run `(Term.label $(quote l))
    | .binary op l r => Lean.Unhygienic.run `(Term.binary $(quote op) $(quoteRiscTermAux l) $(quoteRiscTermAux r))
    | .extend i fs =>
      let qfs := (fs.map quoteRiscFieldAux).toArray
      Lean.Unhygienic.run `(Term.extend $(quoteRiscTermAux i) [ $[$qfs],* ])
    | .record fs =>
      let qfs := (fs.map quoteRiscFieldAux).toArray
      Lean.Unhygienic.run `(Term.record [ $[$qfs],* ])
    | .get g p => Lean.Unhygienic.run `(Term.get $(quoteRiscTermAux g) $(quote p))
    | .ifZero v z s => Lean.Unhygienic.run `(Term.ifZero $(quoteRiscTermAux v) $(quoteRiscTermAux z) $(quoteRiscTermAux s))
    | .inject l p => Lean.Unhygienic.run `(Term.inject $(quote l) $(quoteRiscTermAux p))
    | .case sc arms =>
      let qarms := (arms.map quoteRiscFieldAux).toArray
      Lean.Unhygienic.run `(Term.case $(quoteRiscTermAux sc) [ $[$qarms],* ])
    | .ifBool c x y => Lean.Unhygienic.run `(Term.ifBool $(quoteRiscTermAux c) $(quoteRiscTermAux x) $(quoteRiscTermAux y))
    | .perform p => Lean.Unhygienic.run `(Term.perform $(quoteRiscTermAux p))
    | .done v => Lean.Unhygienic.run `(Term.done $(quoteRiscTermAux v))
    | .split t names f =>
      Lean.Unhygienic.run `(Term.split $(quoteRiscTermAux t) $(quote names) $(quoteRiscTermAux f))

  meta partial def quoteRiscFieldAux (kv : String × Term) : TSyntax `term :=
    Lean.Unhygienic.run `(($(quote kv.1), $(quoteRiscTermAux kv.2)))
end

meta instance : Quote Term where
  quote := quoteRiscTermAux

meta instance : Quote Layer where
  quote L :=
    Lean.Unhygienic.run `(Layer.mk $(quote L.name) $(quote L.metadata) $(quote L.fields) $(quote L.flat) $(quote L.composeMeta))

meta instance : Quote Composition where
  quote C :=
    Lean.Unhygienic.run `(Composition.mk $(quote C.top) $(quote C.below) $(quote C.seed))

meta instance : Quote DefKind where
  quote
    | .method => mkIdent ``DefKind.method
    | .cell   => mkIdent ``DefKind.cell

meta instance : Quote LeafDef where
  quote d :=
    Lean.Unhygienic.run `(LeafDef.mk $(quote d.member) $(quote d.slot) $(quote d.kind) $(quote d.code) $(quote d.reads))

meta instance : Quote BookItem where
  quote
    | .slot d => Lean.Unhygienic.run `(BookItem.slot $(quote d))
    | .static m v => Lean.Unhygienic.run `(BookItem.static $(quote m) $(quote v))

meta instance : Quote Book where
  quote B :=
    Lean.Unhygienic.run `(Book.mk $(quote B.items))

meta partial def quoteRiscRStepAux : RStep → TSyntax `term
  | .run n => Lean.Unhygienic.run `(RStep.run $(quote n))
  | .lateBinding m L => Lean.Unhygienic.run `(RStep.lateBinding $(quote m) $(quote L))
  | .assoc d => Lean.Unhygienic.run `(RStep.assoc $(quote d))
  | .composeAssoc d => Lean.Unhygienic.run `(RStep.composeAssoc $(quote d))
  | .congr ctx focus sub =>
    let qsub := (sub.map quoteRiscRStepAux).toArray
    Lean.Unhygienic.run `(RStep.congr $(quote ctx) $(quote focus) [ $[$qsub],* ])
  | .trans f s =>
    let qf := (f.map quoteRiscRStepAux).toArray
    let qs := (s.map quoteRiscRStepAux).toArray
    Lean.Unhygienic.run `(RStep.trans [ $[$qf],* ] [ $[$qs],* ])

meta instance : Quote RStep where
  quote := quoteRiscRStepAux

meta instance : Quote ClaimObj where
  quote c :=
    Lean.Unhygienic.run `(ClaimObj.mk $(quote c.comp) $(quote c.layer) $(quote c.claim) $(quote c.arity))

meta instance : Quote Support where
  quote sp :=
    Lean.Unhygienic.run `(Support.mk $(quote sp.member) $(quote sp.unfolded))

meta instance : Quote Justification where
  quote
    | .byDerivation steps => Lean.Unhygienic.run `(Justification.byDerivation $(quote steps))
    | .byLoweredLean lowered sups receipt =>
      Lean.Unhygienic.run `(Justification.byLoweredLean $(quote lowered) $(quote sups) (mkRiscByteArrayOfNatList $(quote (receipt.toList.map UInt8.toNat))))
    | .byExternalJudge fmt bs =>
      Lean.Unhygienic.run `(Justification.byExternalJudge $(quote fmt) (mkRiscByteArrayOfNatList $(quote (bs.toList.map UInt8.toNat))))
    | .byEval rows => Lean.Unhygienic.run `(Justification.byEval $(quote rows))

meta def defaultRiscLimits : Json :=
  Json.mkObj [
    ("heap", toJson "100000"),
    ("stack", toJson "100000"),
    ("ticks", toJson "100000"),
    ("checkWork", toJson "65536")
  ]

meta def normalizeRiscSource (src : String) : String :=
  let s := src.replace "\r\n" "\n"
  if s.endsWith "\n" then s else s ++ "\n"

meta def sanitizeRiscModName (stem : String) : String :=
  let chars := stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  match chars with
  | [] => "Main"
  | c :: _ =>
    let s := String.ofList (if c.isAlpha || c == '_' then chars else '_' :: chars)
    if Obend.Spec.Parse.isIdent s.toList then s else "Main"

meta def stripRiscImportQuotes (raw : String) : String :=
  let s := raw.trimAscii.toString
  if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
    ((s.drop 1).dropEnd 1).toString
  else
    s

meta def resolveRiscObendPath (path : System.FilePath) : IO System.FilePath := do
  if ← path.pathExists then return path
  let s := path.toString
  let parentPath := System.FilePath.mk ("../" ++ s)
  if ← parentPath.pathExists then return parentPath
  if s.startsWith "lean/" then
    let stripped := System.FilePath.mk (s.drop 5).toString
    if ← stripped.pathExists then return stripped
  let prefixed := System.FilePath.mk ("lean/" ++ s)
  if ← prefixed.pathExists then return prefixed
  return path

meta def resolveImportedRiscObendPath (parentFile : System.FilePath) (rawImportPath : String) :
    IO System.FilePath := do
  let clean := stripRiscImportQuotes rawImportPath
  let rel1 := match parentFile.parent with
    | some dir => dir / clean
    | none => System.FilePath.mk clean
  let r1 ← resolveRiscObendPath rel1
  if ← r1.pathExists then return r1
  let stripped := if clean.startsWith "./" then (clean.drop 2).toString else clean
  let rel2 := match parentFile.parent with
    | some dir => dir / stripped
    | none => System.FilePath.mk stripped
  let r2 ← resolveRiscObendPath rel2
  if ← r2.pathExists then return r2
  let r3 ← resolveRiscObendPath (System.FilePath.mk stripped)
  if ← r3.pathExists then return r3
  let fileName := (System.FilePath.mk stripped).fileName.getD stripped
  for sub in ["apps/obend-risc/", "stdlib/physical/", "stdlib/core/"] do
    let cand ← resolveRiscObendPath (System.FilePath.mk (sub ++ fileName))
    if ← cand.pathExists then return cand
  return r1

meta def parseAndCheckRiscObendModule (src : String) (moduleName : String)
    (prior : List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)) :
    Except String (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) := do
  let normSrc := normalizeRiscSource src
  let sha256 := Obend.Spec.Sha256.hex normSrc.toUTF8
  let ast ← match Obend.Spec.FrontEnd.parseSource moduleName normSrc with
    | .ok a => pure a
    | .error d => throw s!"{d.stage}: {d.message}"
  let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
  let mut lockedImports : List Obend.Spec.FrontEnd.LockedImport := []
  for edge in parsedEdges.toList do
    let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
    let edgeAlias := (edge.getObjValAs? String "alias").toOption.getD ""
    let edgeSpan := (edge.getObjVal? "span").toOption.getD .null
    let cleanPath := stripRiscImportQuotes edgePath
    let stemMod := sanitizeRiscModName ((System.FilePath.mk cleanPath).fileStem.getD edgeAlias)
    let found? := prior.zipIdx.find? fun ((sm, _), _) =>
      sm.name == stemMod || (edgeAlias != "" && sm.name == edgeAlias)
    let some ((targetSm, _), targetIdx) := found?
      | throw s!"module {moduleName}: imported module for '{edgePath}' (alias '{edgeAlias}') not found in loaded closure"
    lockedImports := lockedImports ++ [{
      path := edgePath
      importAlias := edgeAlias
      span := edgeSpan
      target := targetIdx
      moduleName := targetSm.name
      sha256 := targetSm.sha256
    }]
  let srcMod : Obend.Spec.FrontEnd.SourceModule := {
    name := moduleName
    source := normSrc
    sha256 := sha256
    imports := lockedImports
  }
  let decodedMod ← match Obend.Spec.FrontEnd.checkParsed srcMod ast with
    | .ok m => pure m
    | .error d => throw s!"{d.stage}: {d.message}"
  return (srcMod, decodedMod)

meta def loadRiscObendModuleClosure :
    Nat → System.FilePath →
    List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) →
    IO (Except String (List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)))
  | 0, path, _ => return .error s!"import depth limit exceeded while loading {path}"
  | fuel + 1, path, acc => do
    let resolved ← resolveRiscObendPath path
    let modName := sanitizeRiscModName (resolved.fileStem.getD "Main")
    if acc.any (fun (sm, _) => sm.name == modName) then
      return .ok acc
    match ← (IO.FS.readBinFile resolved).toBaseIO with
    | .error e => return .error (toString e)
    | .ok bytes =>
      let some rawSrc := Obend.Spec.Parse.decodeSource bytes
        | return .error s!"{resolved}: invalid UTF-8"
      let normSrc := normalizeRiscSource rawSrc
      let ast ← match Obend.Spec.FrontEnd.parseSource modName normSrc with
        | .ok a => pure a
        | .error d => return .error s!"{d.stage}: {d.message}"
      let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
      let mut curAcc := acc
      for edge in parsedEdges.toList do
        let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
        let impFile ← resolveImportedRiscObendPath resolved edgePath
        match ← loadRiscObendModuleClosure fuel impFile curAcc with
        | .error err => return .error err
        | .ok nextAcc => curAcc := nextAcc
      match parseAndCheckRiscObendModule normSrc modName curAcc with
      | .error err => return .error err
      | .ok pair => return .ok (curAcc ++ [pair])

meta def resolveRiscKnotTerm (root : Term) (rawFields : List (String × Term)) (visiting : List String) :
    Nat → Term → Term
  | 0, t => t
  | fuel + 1, .get target name =>
    if Obend.Law.termEq target root then
      if visiting.contains name then .get root name
      else
        match rawFields.lookup name with
        | some rawBody =>
          let opened := Obend.Logic.openTerm rawBody root (.record [])
          resolveRiscKnotTerm root rawFields (name :: visiting) fuel opened
        | none => .get root name
    else
      .get (resolveRiscKnotTerm root rawFields visiting fuel target) name
  | fuel + 1, .lam b => .lam (resolveRiscKnotTerm root rawFields visiting fuel b)
  | fuel + 1, .app f a =>
    .app (resolveRiscKnotTerm root rawFields visiting fuel f) (resolveRiscKnotTerm root rawFields visiting fuel a)
  | fuel + 1, .mix l u =>
    .mix (resolveRiscKnotTerm root rawFields visiting fuel l) (resolveRiscKnotTerm root rawFields visiting fuel u)
  | fuel + 1, .fix s i =>
    .fix (resolveRiscKnotTerm root rawFields visiting fuel s) (resolveRiscKnotTerm root rawFields visiting fuel i)
  | fuel + 1, .specification m e =>
    .specification (resolveRiscKnotTerm root rawFields visiting fuel m) (resolveRiscKnotTerm root rawFields visiting fuel e)
  | fuel + 1, .prototype s g =>
    .prototype (resolveRiscKnotTerm root rawFields visiting fuel s) (resolveRiscKnotTerm root rawFields visiting fuel g)
  | fuel + 1, .reflect p => .reflect (resolveRiscKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .metadata p => .metadata (resolveRiscKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .project p => .project (resolveRiscKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .binary op l r =>
    .binary op (resolveRiscKnotTerm root rawFields visiting fuel l) (resolveRiscKnotTerm root rawFields visiting fuel r)
  | fuel + 1, .extend i fs =>
    .extend (resolveRiscKnotTerm root rawFields visiting fuel i)
      (fs.map fun (k, v) => (k, resolveRiscKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .record fs =>
    .record (fs.map fun (k, v) => (k, resolveRiscKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifZero v z s =>
    .ifZero (resolveRiscKnotTerm root rawFields visiting fuel v)
      (resolveRiscKnotTerm root rawFields visiting fuel z)
      (resolveRiscKnotTerm root rawFields visiting fuel s)
  | fuel + 1, .inject l p => .inject l (resolveRiscKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .case sc arms =>
    .case (resolveRiscKnotTerm root rawFields visiting fuel sc)
      (arms.map fun (k, v) => (k, resolveRiscKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifBool c x y =>
    .ifBool (resolveRiscKnotTerm root rawFields visiting fuel c)
      (resolveRiscKnotTerm root rawFields visiting fuel x)
      (resolveRiscKnotTerm root rawFields visiting fuel y)
  | fuel + 1, .perform p => .perform (resolveRiscKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .done v => .done (resolveRiscKnotTerm root rawFields visiting fuel v)
  | fuel + 1, .split t names f =>
    .split (resolveRiscKnotTerm root rawFields visiting fuel t) names
      (resolveRiscKnotTerm root rawFields visiting fuel f)
  | _ + 1, t => t

meta def decodeRiscWithSeed (want : Composition → Bool) : Term → Option Composition
  | .fix S (.record seed) =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      let C : Composition := ⟨top, below, seed⟩
      if want C then some C else none
  | .fix S seedTerm =>
    (Obend.Logic.Program.decodeOperands 64 S).bind fun (top, below) =>
      if top.name == "" then none
      else
        match Obend.Law.run 20000 seedTerm with
        | some (.record seed) =>
          let C : Composition := ⟨top, below, seed⟩
          if want C then some C else none
        | _ => none
  | _ => none

meta def findRiscObject (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match decodeRiscWithSeed want t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (findRiscObject want fuel)

meta def findRiscSelfGetCtx (selfIdx : Nat) : Term → Option (Term × String)
  | .get (.bound i) m =>
    if i == selfIdx then some (.bound 0, m) else none
  | .app f a =>
    match findRiscSelfGetCtx selfIdx f with
    | some (ctxF, m) => some (.app ctxF (a.rename Nat.succ), m)
    | none =>
      (findRiscSelfGetCtx selfIdx a).map fun (ctxA, m) => (.app (f.rename Nat.succ) ctxA, m)
  | .binary op l r =>
    match findRiscSelfGetCtx selfIdx l with
    | some (ctxL, m) => some (.binary op ctxL (r.rename Nat.succ), m)
    | none =>
      (findRiscSelfGetCtx selfIdx r).map fun (ctxR, m) => (.binary op (l.rename Nat.succ) ctxR, m)
  | _ => none

meta def deriveRiscClaim (o : ClaimObj) (r : Term) : Nat → Term → List RStep → Option (List RStep)
  | 0, _, _ => none
  | fuel + 1, t, acc =>
    if Obend.Law.termEq t r then some acc.reverse
    else match Obend.Law.step? t with
    | some t' => deriveRiscClaim o r fuel t' (Obend.Logic.Program.pushRun acc)
    | none =>
      match findRiscSelfGetCtx o.self t with
      | some (ctx, m) =>
        match Obend.Logic.symUnfold o.comp o.self m with
        | some (L, _) =>
          let step : RStep :=
            if Obend.Law.termEq ctx (.bound 0) then .lateBinding m L
            else .congr ctx (.get (.bound o.self) m) [.lateBinding m L]
          match Obend.Logic.apply (Obend.Logic.claimResolver o.comp o.self) step t with
          | .ok t' => deriveRiscClaim o r fuel t' (step :: acc)
          | .error _ => none
        | none => none
      | none => none

meta def proposeRiscDerivation (o : ClaimObj) : Option (List RStep) :=
  match Obend.Logic.Program.proposeDerivation o with
  | some steps => some steps
  | none =>
    match o.sides with
    | some (_, l, r) => deriveRiscClaim o r 4096 l []
    | none => none

meta structure RiscElaboratedDef where
  name         : String
  reducedVal?  : Option Term
  composition? : Option Composition
  book?        : Option Book

meta structure RiscElaboratedClaim where
  name     : String
  claimObj : ClaimObj
  just?    : Option Justification
  verified : Bool

meta structure RiscElaboratedModule where
  moduleName : String
  defs       : List RiscElaboratedDef
  claims     : List RiscElaboratedClaim

meta def compactRiscLayerForKernel (L : Layer) : Layer :=
  { L with
    metadata := .record [("name", .label L.name)]
    fields := L.fields.filter (fun kv => kv.1 != "#kind")
    composeMeta := .record [] }

meta def compactRiscCompositionForKernel (C : Composition) : Composition :=
  { C with
    top := compactRiscLayerForKernel C.top
    below := C.below.map compactRiscLayerForKernel
    seed := C.seed.filter (fun kv => kv.1 != "#kind") }

meta def elaborateRiscObendFile (pathStr : String) : IO (Except String RiscElaboratedModule) := do
  let closure ← match ← loadRiscObendModuleClosure 32 (System.FilePath.mk pathStr) [] with
    | .ok c => pure c
    | .error err => return .error err
  let some (srcMod, decodedMod) := closure.getLast?
    | return .error s!"empty module closure for {pathStr}"
  let prior := closure.dropLast
  let modName := srcMod.name
  let callables := decodedMod.decls.filter fun (d : Obend.Spec.Syntax.Decl) =>
    match d with
    | .function .. | .extension .. | .spec .. => true
    | _ => false
  let some (lastDecl : Obend.Spec.Syntax.Decl) := callables.getLast?
    | return .error s!"module {modName} contains no callable declarations"
  let entryDef := lastDecl.name
  let allSrcMods := prior.map Prod.fst ++ [srcMod]
  let allDecodedMods := prior.map Prod.snd ++ [decodedMod]
  let entryIdx := prior.length
  let allLaws := (allDecodedMods.map (·.laws)).flatten
  let decodedForLower := allDecodedMods.zipIdx.map fun (dm, idx) =>
    if idx == entryIdx then { dm with laws := allLaws } else { dm with laws := [] }
  match Obend.Spec.FrontEnd.lowerDecoded allSrcMods decodedForLower entryIdx entryDef
      (Json.arr #[]) (Json.arr #[]) defaultRiscLimits "definition" [] with
  | .error d => return .error s!"{d.stage}: {d.message}"
  | .ok lowering =>
    match Obend.Spec.FrontEnd.accept lowering with
    | .error d => return .error s!"{d.stage}: {d.message}"
    | .ok acc =>
      let erasedTerm := acc.erased
      let rootTerm := (Obend.Logic.Program.knotOf erasedTerm).getD erasedTerm
      let rawFields := Obend.Logic.Program.knotFields rootTerm
      let mut pdefs : List RiscElaboratedDef := []
      for d in callables do
        let shortName := d.name
        let fullKey := modName ++ "." ++ shortName
        let knotTerm : Term := .get rootTerm fullKey
        let opened := match rawFields.lookup fullKey with
          | some rb => Obend.Logic.openTerm rb rootTerm (.record [])
          | none => knotTerm
        let wantNamed : Composition → Bool := fun C => C.top.name != ""
        let rawComp? :=
          match findRiscObject wantNamed 64 knotTerm with
          | some c => some c
          | none =>
            match findRiscObject wantNamed 64 (.app knotTerm (.record [])) with
            | some c => some c
            | none =>
              let inlined := resolveRiscKnotTerm rootTerm rawFields [fullKey] 8 opened
              decodeRiscWithSeed wantNamed inlined
        let foundComp? := rawComp?.map compactRiscCompositionForKernel
        let book? := foundComp?.map Obend.Leaf.emit
        let reducedVal? :=
          if foundComp?.isSome then none
          else
            match Obend.Law.run 50000 knotTerm with
            | some (.nat n) => some (.nat n)
            | some (.boolean b) => some (.boolean b)
            | some (.label s) => some (.label s)
            | _ =>
              match Obend.Law.run 50000 (.app knotTerm (.record [])) with
              | some (.nat n) => some (.nat n)
              | some (.boolean b) => some (.boolean b)
              | some (.label s) => some (.label s)
              | _ => none
        pdefs := pdefs ++ [{
          name := shortName
          reducedVal? := reducedVal?
          composition? := foundComp?
          book? := book?
        }]
      let rawClaimPairs := Obend.Logic.Program.claimFields rootTerm
      let mut pclaims : List RiscElaboratedClaim := []
      for (specKey, claimName) in rawClaimPairs do
        let matchingDefs := pdefs.filter fun wd =>
          match wd.composition? with
          | some comp => (Obend.Logic.Program.layerIndex comp specKey).isSome
          | none => false
        let chosenDef? :=
          match matchingDefs.find? (fun wd => wd.composition?.any (fun c => c.top.name == specKey)) with
          | some wd => some wd
          | none => matchingDefs.head?
        if let some wd := chosenDef? then
          if let some comp := wd.composition? then
            if let .ok co := Obend.Logic.Program.claimObj rootTerm comp specKey claimName then
              let steps? := proposeRiscDerivation co
              let just? := steps?.map Justification.byDerivation
              let ok := match just? with
                | some j => Obend.Logic.obligationCheck 256 co j == .ok
                | none => false
              pclaims := pclaims ++ [{
                name := claimName
                claimObj := co
                just? := just?
                verified := ok
              }]
      return .ok {
        moduleName := modName
        defs := pdefs
        claims := pclaims
      }

theorem riscObligationMeaning_of_check_beq
    (formats : List Judge.Format) {k : Nat} {o : ClaimObj} {j : Justification}
    (h : (Obend.Logic.obligationCheckWithJudges formats k o j == .ok) = true) :
    Obend.Logic.obligationMeaningWithJudges formats o j :=
  Obend.Logic.obligationWithJudges_sound formats (beq_iff_eq.1 h)

local elab "#import_obend " pathLit:str " as " nsId:ident : command => do
  let pathStr := pathLit.getString
  let res ← IO.toEIO
    (fun e => Lean.Exception.error Lean.Syntax.missing (Lean.MessageData.ofFormat (Std.Format.text (toString e))))
    (elaborateRiscObendFile pathStr)
  match res with
  | .error err =>
    Lean.throwError m!"#import_obend failed on {pathStr}: {err}"
  | .ok pkg =>
    let ns := nsId.getId
    let accId := mkIdent (ns ++ `accepted)
    let accEqId := mkIdent (ns ++ `accepted_eq)
    elabCommand (← `(@[expose] public def $accId : Bool := true))
    elabCommand (← `(public theorem $accEqId : $accId = true := rfl))
    for d in pkg.defs do
      if let some rv := d.reducedVal? then
        let valId := mkIdent (ns ++ Name.mkSimple (d.name ++ "_val"))
        elabCommand (← `(@[expose] public def $valId : Term := $(quote rv)))
      if let some comp := d.composition? then
        let compId := mkIdent (ns ++ Name.mkSimple (d.name ++ "_comp"))
        elabCommand (← `(@[expose] public def $compId : Composition := $(quote comp)))
      if let some bk := d.book? then
        let bookId := mkIdent (ns ++ Name.mkSimple (d.name ++ "_book"))
        elabCommand (← `(@[expose] public def $bookId : Book := $(quote bk)))
    for c in pkg.claims do
      let objId := mkIdent (ns ++ Name.mkSimple ("claim_" ++ c.name ++ "_obj"))
      elabCommand (← `(@[expose] public def $objId : ClaimObj := $(quote c.claimObj)))
      if let some just := c.just? then
        let justId := mkIdent (ns ++ Name.mkSimple ("claim_" ++ c.name ++ "_just"))
        elabCommand (← `(@[expose] public def $justId : Justification := $(quote just)))
        if c.verified then
          let holdsId := mkIdent (ns ++ Name.mkSimple ("claim_" ++ c.name ++ "_holds"))
          elabCommand (← `(
            public theorem $holdsId : Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats $objId $justId :=
              riscObligationMeaning_of_check_beq Obend.Logic.defaultExternalFormats (k := 256) (o := $objId) (j := $justId) (by decide +kernel)
          ))

/-! ## 1. Elaborating the 3-Layer `.obend` RISC Softcore Hierarchy via `#import_obend` -/

#import_obend "apps/obend-risc/BaseRiscCore.obend" as BaseRisc
#import_obend "apps/obend-risc/PrivilegeCsrOverride.obend" as PrivRisc
#import_obend "apps/obend-risc/CustomSimdZkExt.obend" as ExtRisc
#import_obend "apps/obend-risc/ComposedRiscCpu.obend" as ComposedRisc

/-- Theorem: All 4 `.obend` RISC softcore modules parse, typecheck, elaborate, and auto-verify
    every open-recursive layer claim (`accepted = true`). -/
theorem obend_risc_layers_accepted_and_claims_hold :
    BaseRisc.accepted = true ∧
    PrivRisc.accepted = true ∧
    ExtRisc.accepted = true ∧
    ComposedRisc.accepted = true ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      BaseRisc.claim_base_decode_addi_opcode_obj BaseRisc.claim_base_decode_addi_opcode_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      BaseRisc.claim_base_exec_add_obj BaseRisc.claim_base_exec_add_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      PrivRisc.claim_priv_ecall_redirects_to_mtvec_obj PrivRisc.claim_priv_ecall_redirects_to_mtvec_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      PrivRisc.claim_priv_mret_restores_mepc_obj PrivRisc.claim_priv_mret_restores_mepc_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      PrivRisc.claim_priv_preserves_base_add_obj PrivRisc.claim_priv_preserves_base_add_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      ExtRisc.claim_custom_simd_zk_mac_exec_obj ExtRisc.claim_custom_simd_zk_mac_exec_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      ExtRisc.claim_custom_ext_non_interference_add_obj ExtRisc.claim_custom_ext_non_interference_add_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      ExtRisc.claim_custom_ext_respects_trap_preemption_obj ExtRisc.claim_custom_ext_respects_trap_preemption_just :=
  ⟨BaseRisc.accepted_eq,
   PrivRisc.accepted_eq,
   ExtRisc.accepted_eq,
   ComposedRisc.accepted_eq,
   BaseRisc.claim_base_decode_addi_opcode_holds,
   BaseRisc.claim_base_exec_add_holds,
   PrivRisc.claim_priv_ecall_redirects_to_mtvec_holds,
   PrivRisc.claim_priv_mret_restores_mepc_holds,
   PrivRisc.claim_priv_preserves_base_add_holds,
   ExtRisc.claim_custom_simd_zk_mac_exec_holds,
   ExtRisc.claim_custom_ext_non_interference_add_holds,
   ExtRisc.claim_custom_ext_respects_trap_preemption_holds⟩

/-- Theorem: Evaluating the 8-element Fibonacci sequence sum (`1+1+2+3+5+8+13+21 = 54`) and
    4-instruction custom SIMD/ZK MAC chain (`1282`) on the 3-layer `composedRiscCpu()` in `.obend`
    reduces to their exact expected values. -/
theorem obend_risc_workbook_fibonacci_and_mac_eval :
    ComposedRisc.evalFibonacci8Sum_val = .nat 54 ∧
    ComposedRisc.evalCustomSimdMac4_val = .nat 1282 :=
  ⟨rfl, rfl⟩

/-! ## 2. Sequential `always_ff @(posedge clk)` SystemVerilog RISC Softcore (`obendRiscCpuRtlModule`) -/

/-- Clock domain for the sequential RISC softcore. -/
def riscClkDomain : ClkDomain :=
  .coreClk

/-- Build a 15-way register file read mux tree over `x1..x15` (registers `5..19`),
    returning `64'd0` for `x0` (`idx == 0`). -/
def buildRegReadMux (selWire : Nat) : List (Nat × Nat) → RtlExpr
  | [] => .const 0#64
  | (regNum, regSlot) :: rest =>
    .mux (.alu .eq (.wireRef selWire) (.const (BitVec.ofNat 64 regNum)))
      (.regRead regSlot)
      (buildRegReadMux selWire rest)

/-- Standard mapping from architectural register numbers `1..15` to `RtlModule` register slots `5..19`. -/
def archRegSlots : List (Nat × Nat) :=
  [(1, 5), (2, 6), (3, 7), (4, 8), (5, 9), (6, 10), (7, 11), (8, 12),
   (9, 13), (10, 14), (11, 15), (12, 16), (13, 17), (14, 18), (15, 19)]

/-- Build the architectural register writeback `RegSpec` for `x_k` at slot `4 + k`. -/
def buildArchRegSpec (k : Nat) : RegSpec :=
  let slot := 4 + k
  { regIdx := slot
    name := s!"x{k}"
    domain := riscClkDomain
    resetKind := .syncReset 0#64
    isSynchronizer := false
    nextExpr :=
      .mux (.alu .bitAnd (.wireRef 16) (.alu .eq (.wireRef 1) (.const (BitVec.ofNat 64 k))))
        (.wireRef 15)
        (.regRead slot) }

/-- Complete sequential `always_ff @(posedge clk)` SystemVerilog RISC softcore (`obend_risc_cpu`).
    Performs in-core bit-slice instruction decode from raw `imem_rdata` (`inputPort 0`),
    holds `pc`, `mstatus`, `mepc`, `mcause`, `cycle_cnt`, and `x1..x15` in synchronous registers,
    and drives `imem_addr` and `dmem_addr`/`dmem_wdata`/`dmem_we`. -/
def obendRiscCpuRtlModule : RtlModule :=
  { name := "obend_risc_cpu"
    inputNames := ["imem_rdata", "dmem_rdata"]
    wires := [
      -- w_0..w_6: In-core instruction bit-slice decoders from raw imem_rdata (inputPort 0)
      { wireIdx := 0, name := "opcode",
        expr := .alu .bitAnd (.inputPort 0) (.const 127#64) },
      { wireIdx := 1, name := "rd",
        expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 7#64)) (.const 31#64) },
      { wireIdx := 2, name := "funct3",
        expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 12#64)) (.const 7#64) },
      { wireIdx := 3, name := "rs1",
        expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 15#64)) (.const 31#64) },
      { wireIdx := 4, name := "rs2",
        expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 20#64)) (.const 31#64) },
      { wireIdx := 5, name := "imm12",
        expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 20#64)) (.const 4095#64) },
      { wireIdx := 6, name := "funct7",
        expr := .alu .bitAnd (.alu .lshr (.inputPort 0) (.const 25#64)) (.const 127#64) },
      -- w_7..w_8: Architectural register file read ports (rs1_val, rs2_val)
      { wireIdx := 7, name := "rs1_val",
        expr := buildRegReadMux 3 archRegSlots },
      { wireIdx := 8, name := "rs2_val",
        expr := buildRegReadMux 4 archRegSlots },
      -- w_9..w_11: Layer 2 (PrivilegeCsrOverride) & Layer 3 (CustomSimdZkExt) decode strobes
      { wireIdx := 9, name := "is_trap",
        expr := .alu .bitAnd (.alu .eq (.wireRef 0) (.const 115#64))
                             (.alu .eq (.wireRef 5) (.const 0#64)) },
      { wireIdx := 10, name := "is_mret",
        expr := .alu .bitAnd (.alu .eq (.wireRef 0) (.const 115#64))
                             (.alu .eq (.wireRef 5) (.const 770#64)) },
      { wireIdx := 11, name := "is_custom_ext",
        expr := .alu .eq (.wireRef 0) (.const 43#64) },
      -- w_12..w_13: Layer 1 (BaseRiscCore) ALU datapath
      { wireIdx := 12, name := "base_alu_rhs",
        expr := .mux (.alu .eq (.wireRef 0) (.const 19#64)) (.wireRef 5) (.wireRef 8) },
      { wireIdx := 13, name := "base_alu_out",
        expr := .mux (.alu .eq (.wireRef 2) (.const 0#64))
                  (.alu .add (.wireRef 7) (.wireRef 12))
                  (.mux (.alu .eq (.wireRef 2) (.const 1#64))
                    (.alu .sub (.wireRef 7) (.wireRef 12))
                    (.mux (.alu .eq (.wireRef 2) (.const 2#64))
                      (.alu .mul (.wireRef 7) (.wireRef 12))
                      (.alu .add (.wireRef 7) (.wireRef 12)))) },
      -- w_14: Layer 3 (CustomSimdZkExt) MAC & Goldilocks datapath
      { wireIdx := 14, name := "custom_ext_out",
        expr := .mux (.alu .eq (.wireRef 2) (.const 0#64))
                  (.alu .add (.alu .mul (.wireRef 7) (.wireRef 8)) (.wireRef 6))
                  (.mux (.alu .eq (.wireRef 2) (.const 1#64))
                    (.alu .add (.alu .mul (.wireRef 7) (.const 4294967295#64)) (.wireRef 8))
                    (.alu .add (.wireRef 7) (.alu .shl (.wireRef 8) (.const 1#64)))) },
      -- w_15..w_16: Composed writeback value and writeback enable
      { wireIdx := 15, name := "wb_val",
        expr := .mux (.wireRef 9)
                  (.alu .add (.regRead 0) (.const 4#64))
                  (.mux (.wireRef 11)
                    (.wireRef 14)
                    (.mux (.alu .eq (.wireRef 0) (.const 3#64))
                      (.inputPort 1)
                      (.mux (.alu .eq (.wireRef 0) (.const 111#64))
                        (.alu .add (.regRead 0) (.const 4#64))
                        (.wireRef 13)))) },
      { wireIdx := 16, name := "wb_en",
        expr := .alu .bitOr
                  (.alu .bitOr
                    (.alu .bitOr
                      (.alu .bitOr
                        (.alu .bitOr (.wireRef 9) (.wireRef 11))
                        (.alu .eq (.wireRef 0) (.const 19#64)))
                      (.alu .eq (.wireRef 0) (.const 51#64)))
                    (.alu .eq (.wireRef 0) (.const 3#64)))
                  (.alu .eq (.wireRef 0) (.const 111#64)) },
      -- w_17: Composed next_pc (Privilege trap/mret overrides base branch/jal/step)
      { wireIdx := 17, name := "next_pc",
        expr := .mux (.wireRef 9)
                  (.const 64#64)
                  (.mux (.wireRef 10)
                    (.regRead 2)
                    (.mux (.alu .eq (.wireRef 0) (.const 99#64))
                      (.mux (.alu .eq (.wireRef 7) (.wireRef 8))
                        (.alu .add (.regRead 0) (.alu .shl (.wireRef 6) (.const 2#64)))
                        (.alu .add (.regRead 0) (.const 4#64)))
                      (.mux (.alu .eq (.wireRef 0) (.const 111#64))
                        (.alu .add (.regRead 0) (.alu .shl (.wireRef 5) (.const 2#64)))
                        (.alu .add (.regRead 0) (.const 4#64))))) },
      -- w_18..w_19: Data memory address & trap-preempted write enable
      { wireIdx := 18, name := "dmem_addr_w",
        expr := .mux (.alu .eq (.wireRef 0) (.const 35#64))
                  (.alu .add (.wireRef 7) (.wireRef 6))
                  (.alu .add (.wireRef 7) (.wireRef 5)) },
      { wireIdx := 19, name := "dmem_we_w",
        expr := .mux (.wireRef 9)
                  (.const 0#64)
                  (.mux (.alu .eq (.wireRef 0) (.const 35#64)) (.const 1#64) (.const 0#64)) }
    ]
    regs := [
      { regIdx := 0, name := "pc", domain := riscClkDomain,
        resetKind := .syncReset 0#64, isSynchronizer := false, nextExpr := .wireRef 17 },
      { regIdx := 1, name := "mstatus", domain := riscClkDomain,
        resetKind := .syncReset 0#64, isSynchronizer := false,
        nextExpr := .mux (.wireRef 9) (.const 24#64)
                      (.mux (.wireRef 10) (.const 8#64) (.regRead 1)) },
      { regIdx := 2, name := "mepc", domain := riscClkDomain,
        resetKind := .syncReset 0#64, isSynchronizer := false,
        nextExpr := .mux (.wireRef 9) (.alu .add (.regRead 0) (.const 4#64)) (.regRead 2) },
      { regIdx := 3, name := "mcause", domain := riscClkDomain,
        resetKind := .syncReset 0#64, isSynchronizer := false,
        nextExpr := .mux (.wireRef 9) (.const 11#64) (.regRead 3) },
      { regIdx := 4, name := "cycle_cnt", domain := riscClkDomain,
        resetKind := .syncReset 0#64, isSynchronizer := false,
        nextExpr := .alu .add (.regRead 4) (.const 1#64) }
    ] ++ (List.range 15).map (fun i => buildArchRegSpec (i + 1))
    outputs := [
      { name := "imem_addr", expr := .regRead 0 },
      { name := "dmem_addr", expr := .wireRef 18 },
      { name := "dmem_wdata", expr := .wireRef 8 },
      { name := "dmem_we", expr := .wireRef 19 },
      { name := "pc_out", expr := .regRead 0 },
      { name := "mstatus_out", expr := .regRead 1 },
      { name := "mepc_out", expr := .regRead 2 },
      { name := "mcause_out", expr := .regRead 3 },
      { name := "cycle_cnt_out", expr := .regRead 4 },
      { name := "x1_out", expr := .regRead 5 },
      { name := "x2_out", expr := .regRead 6 },
      { name := "x3_out", expr := .regRead 7 },
      { name := "x4_out", expr := .regRead 8 },
      { name := "x5_out", expr := .regRead 9 },
      { name := "x6_out", expr := .regRead 10 },
      { name := "x7_out", expr := .regRead 11 },
      { name := "x8_out", expr := .regRead 12 },
      { name := "x9_out", expr := .regRead 13 },
      { name := "x10_out", expr := .regRead 14 },
      { name := "x11_out", expr := .regRead 15 },
      { name := "x12_out", expr := .regRead 16 },
      { name := "x13_out", expr := .regRead 17 },
      { name := "x14_out", expr := .regRead 18 },
      { name := "x15_out", expr := .regRead 19 }
    ] }

/-- Theorem: `obendRiscCpuRtlModule` is a well-formed topological DAG and passes CDC checks. -/
theorem obendRiscCpuRtlModule_valid :
    checkRtlModule obendRiscCpuRtlModule = true := by
  decide +kernel

/-- Theorem: `obendRiscCpuRtlModule` synthesizes cleanly to a valid FPGA BEL netlist (`LUT6`/`CARRY8`/`FDRE`). -/
theorem obendRiscCpuRtlModule_bel_valid :
    checkBelNetlistValid (synthesizeModuleToBels obendRiscCpuRtlModule) = true := by
  decide +kernel

/-- Firmware ROM lookup matching `apps/obend-risc/firmware/test_prog.hex` (indexed by `pc >> 2`). -/
def riscFirmwareRom : Nat → BitVec 64
  | 0  => 0x00100093#64 -- ADDI x1, x0, 1
  | 1  => 0x00100113#64 -- ADDI x2, x0, 1
  | 2  => 0x002081B3#64 -- ADD  x3, x1, x2
  | 3  => 0x00310233#64 -- ADD  x4, x2, x3
  | 4  => 0x004182B3#64 -- ADD  x5, x3, x4
  | 5  => 0x00520333#64 -- ADD  x6, x4, x5
  | 6  => 0x006283B3#64 -- ADD  x7, x5, x6
  | 7  => 0x00730433#64 -- ADD  x8, x6, x7
  | 8  => 0x000004F3#64 -- ECALL x9
  | 9  => 0x027305AB#64 -- ZK.MAC x11, x6, x7, 1
  | 10 => 0x0435862B#64 -- ZK.MAC x12, x11, x3, 2
  | 11 => 0x064606AB#64 -- ZK.MAC x13, x12, x4, 3
  | 12 => 0x0836872B#64 -- ZK.MAC x14, x13, x3, 4
  | 13 => 0x00A407B3#64 -- ADD  x15, x8, x10
  | 14 => 0x00E787B3#64 -- ADD  x15, x15, x14
  | 15 => 0x00F02023#64 -- SW   x15, 0(x0)
  | 16 => 0x02A00513#64 -- ADDI x10, x0, 42 (MTVEC handler)
  | 17 => 0x30200073#64 -- MRET
  | _  => 0#64

/-- Step `obendRiscCpuRtlModule` coupled to `riscFirmwareRom` for `n` clock cycles. -/
def runRiscFirmwareCycles : Nat → (Nat → BitVec 64) → (Nat → BitVec 64)
  | 0, st => st
  | k + 1, st =>
    let pcIdx := (st 0).toNat / 4
    let inputs : Nat → BitVec 64 := fun p => if p == 0 then riscFirmwareRom pcIdx else 0#64
    let st' := stepModuleRegs obendRiscCpuRtlModule false inputs st
    runRiscFirmwareCycles k st'

/-- Theorem: Running 18 cycles of `riscFirmwareRom` (`test_prog.hex`) on `obendRiscCpuRtlModule`
    inside Lean produces the exact same cycle-accurate architectural state as the Verilator
    simulation (`x8 = 21`, `mepc = 36`, `mcause = 11`, `mstatus = 8`, `x10 = 42`,
    `x11 = 105`, `x12 = 212`, `x13 = 639`, `x14 = 1282`, `x15 = 1345`). -/
theorem obendRiscCpuRtlModule_firmware_sim_sound :
    let finalSt := runRiscFirmwareCycles 18 (fun _ => 0#64)
    finalSt 1 = 8#64 ∧     -- mstatus = 8 after MRET
    finalSt 2 = 36#64 ∧    -- mepc = 0x24
    finalSt 3 = 11#64 ∧    -- mcause = 11
    finalSt 4 = 18#64 ∧    -- cycle_cnt = 18
    finalSt 12 = 21#64 ∧   -- x8 = Fib(8) = 21
    finalSt 14 = 42#64 ∧   -- x10 = trap marker = 42
    finalSt 15 = 105#64 ∧  -- x11 = ZK_MAC #1 = 105
    finalSt 16 = 212#64 ∧  -- x12 = ZK_MAC #2 = 212
    finalSt 17 = 639#64 ∧  -- x13 = ZK_MAC #3 = 639
    finalSt 18 = 1282#64 ∧ -- x14 = ZK_MAC #4 = 1282
    finalSt 19 = 1345#64   -- x15 = final checksum = 1345
    := by
  decide +kernel

/-! ## 3. Core Deliverable Theorems (`risc_base_opcode_non_interference`, `risc_privilege_trap_preempts_base_and_ext`, `risc_read_set_monotonicity`, `risc_inCore_futamura2`) -/

/-- Pure combinational writeback specification for Layer 1 (`BaseRiscCore`). -/
def baseLayerWriteback (opcode funct3 imm12 rs1Val rs2Val pc dmemRdata : BitVec 64) : BitVec 64 :=
  let rhs := if opcode == 19#64 then imm12 else rs2Val
  let aluOut :=
    if funct3 == 0#64 then rs1Val + rhs
    else if funct3 == 1#64 then rs1Val - rhs
    else if funct3 == 2#64 then rs1Val * rhs
    else rs1Val + rhs
  if opcode == 3#64 then dmemRdata
  else if opcode == 111#64 then pc + 4#64
  else aluOut

/-- Pure combinational writeback specification for the 3-layer `ComposedRiscCpu`
    (`BaseRiscCore + PrivilegeCsrOverride + CustomSimdZkExt`). -/
def composedLayerWriteback (opcode funct3 imm12 funct7 rs1Val rs2Val pc dmemRdata : BitVec 64) : BitVec 64 :=
  let isTrap := (opcode == 115#64) && (imm12 == 0#64)
  let isCustom := opcode == 43#64
  let customOut :=
    if funct3 == 0#64 then rs1Val * rs2Val + funct7
    else if funct3 == 1#64 then rs1Val * 4294967295#64 + rs2Val
    else rs1Val + (rs2Val <<< 1#64)
  if isTrap then pc + 4#64
  else if isCustom then customOut
  else baseLayerWriteback opcode funct3 imm12 rs1Val rs2Val pc dmemRdata

/-- Deliverable Theorem 1: `risc_base_opcode_non_interference`.
    Proves that adding `PrivilegeCsrOverride` (`0x73`) and `CustomSimdZkExt` (`0x2B`) preserves
    both the open-recursive `.obend` base instruction claims and the universal 64-bit hardware
    writeback semantics for all base opcodes (`opcode ≠ 43#64` and `opcode ≠ 115#64`). -/
theorem risc_base_opcode_non_interference
    (opcode funct3 imm12 funct7 rs1Val rs2Val pc dmemRdata : BitVec 64)
    (hNotExt : (opcode == 43#64) = false)
    (hNotTrapOp : (opcode == 115#64) = false) :
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      BaseRisc.claim_base_exec_add_obj BaseRisc.claim_base_exec_add_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      PrivRisc.claim_priv_preserves_base_add_obj PrivRisc.claim_priv_preserves_base_add_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      ExtRisc.claim_custom_ext_non_interference_add_obj ExtRisc.claim_custom_ext_non_interference_add_just ∧
    composedLayerWriteback opcode funct3 imm12 funct7 rs1Val rs2Val pc dmemRdata =
      baseLayerWriteback opcode funct3 imm12 rs1Val rs2Val pc dmemRdata := by
  refine ⟨BaseRisc.claim_base_exec_add_holds,
          PrivRisc.claim_priv_preserves_base_add_holds,
          ExtRisc.claim_custom_ext_non_interference_add_holds, ?_⟩
  unfold composedLayerWriteback
  simp [hNotExt, hNotTrapOp]

/-- Pure next-state transition of the 3-layer `ComposedRiscCpu` control registers
    (`pc`, `mstatus`, `mepc`, `mcause`, `dmem_we`). -/
def composedControlStep (opcode imm12 funct7 rs1Val rs2Val pc mstatus mepc mcause : BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let isTrap := (opcode == 115#64) && (imm12 == 0#64)
  let isMret := (opcode == 115#64) && (imm12 == 770#64)
  let nextPc :=
    if isTrap then 64#64
    else if isMret then mepc
    else if opcode == 99#64 then
      if rs1Val == rs2Val then pc + (funct7 <<< 2#64) else pc + 4#64
    else if opcode == 111#64 then pc + (imm12 <<< 2#64)
    else pc + 4#64
  let nextMstatus := if isTrap then 24#64 else if isMret then 8#64 else mstatus
  let nextMepc := if isTrap then pc + 4#64 else mepc
  let nextMcause := if isTrap then 11#64 else mcause
  let dmemWe := if isTrap then 0#64 else if opcode == 35#64 then 1#64 else 0#64
  (nextPc, nextMstatus, nextMepc, nextMcause, dmemWe)

/-- Deliverable Theorem 2: `risc_privilege_trap_preempts_base_and_ext`.
    Proves that synchronous CSR trap entry (`opcode == 115#64` and `imm12 == 0#64`) preempts
    both base and custom-extension execution, redirecting `pc` to `mtvec = 64#64`, saving
    `mepc = pc + 4#64`, recording `mcause = 11#64` and `mstatus = 24#64`, and forcing `dmem_we = 0#64`. -/
theorem risc_privilege_trap_preempts_base_and_ext
    (opcode imm12 funct7 rs1Val rs2Val pc mstatus mepc mcause : BitVec 64)
    (hTrapOp : (opcode == 115#64) = true)
    (hTrapImm : (imm12 == 0#64) = true) :
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      PrivRisc.claim_priv_ecall_redirects_to_mtvec_obj PrivRisc.claim_priv_ecall_redirects_to_mtvec_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      ExtRisc.claim_custom_ext_respects_trap_preemption_obj ExtRisc.claim_custom_ext_respects_trap_preemption_just ∧
    composedControlStep opcode imm12 funct7 rs1Val rs2Val pc mstatus mepc mcause =
      (64#64, 24#64, pc + 4#64, 11#64, 0#64) := by
  refine ⟨PrivRisc.claim_priv_ecall_redirects_to_mtvec_holds,
          ExtRisc.claim_custom_ext_respects_trap_preemption_holds, ?_⟩
  unfold composedControlStep
  simp [hTrapOp, hTrapImm]

/-- Extract the inner method body (under the outer `λself.` binder) from a `Leaf.Book` slot. -/
def extractRiscBookMethodInner (B : Book) (m : String) : Term :=
  match lookupBookCode B m with
  | some (.lam inner) => inner
  | _ => .nat 0

def privStepPcBody : Term :=
  extractRiscBookMethodInner PrivRisc.privilegeRiscCore_book "stepPc"

def privExecBody : Term :=
  extractRiscBookMethodInner PrivRisc.privilegeRiscCore_book "execInstruction"

def composedExecStepBody : Term :=
  extractRiscBookMethodInner ComposedRisc.composedRiscCpu_book "execStep"

def composedNextPcBody : Term :=
  extractRiscBookMethodInner ComposedRisc.composedRiscCpu_book "nextPc"

/-- Deliverable Theorem 3: `risc_read_set_monotonicity`.
    Proves that:
    1. Every member read by `PrivRisc` (`"mtvecAddr"` in `stepPc` and `"trapCauseCode"` in `execInstruction`)
       is preserved in the 3-layer `ComposedRiscCpu` read-member cone (`composedNextPcBody` and `composedExecStepBody`),
    2. By `extractReadMembers_mutation_invariant`, mutating any disjoint member (`"goldilocksEpsilon"` or `"customExtOpcode"`)
       leaves `substMemberEnv` on `composedNextPcBody` and `composedExecStepBody` identically unchanged. -/
theorem risc_read_set_monotonicity (env : String → Option Term) (newVal : Option Term) :
    extractReadMembers privStepPcBody = ["mtvecAddr"] ∧
    extractReadMembers privExecBody = ["trapCauseCode"] ∧
    (∀ m ∈ extractReadMembers privStepPcBody ++ extractReadMembers privExecBody,
      m ∈ extractReadMembers composedNextPcBody ++ extractReadMembers composedExecStepBody) ∧
    substMemberEnv (mutateMemberEnv env "goldilocksEpsilon" newVal) composedNextPcBody =
      substMemberEnv env composedNextPcBody ∧
    substMemberEnv (mutateMemberEnv env "customExtOpcode" newVal) composedExecStepBody =
      substMemberEnv env composedExecStepBody := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · exact (extractReadMembers_mutation_invariant composedNextPcBody env newVal (by decide +kernel)).1
  · exact (extractReadMembers_mutation_invariant composedExecStepBody env newVal (by decide +kernel)).1

/-- Deliverable Theorem 4: `risc_inCore_futamura2`.
    Proves that all three open-recursive RISC softcore layer books (`BaseRiscCore`,
    `PrivilegeCsrOverride`, and `ComposedRiscCpu`) specialize in-core via both
    `inCoreBookCompiler` (`inCoreBookCompiler_specializes_from_pinsOnly`) and
    `futamura2BookCompiler` (`futamura2BookCompiler_specializes_in_core`). -/
theorem risc_inCore_futamura2 (pins : List LeafPin) :
    let B1 := BaseRisc.baseRiscCore_book
    let B2 := PrivRisc.privilegeRiscCore_book
    let B3 := ComposedRisc.composedRiscCpu_book
    dataPinSpecialize (.app (inCoreBookCompiler B1) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook B1 pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler B2) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook B2 pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler B3) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook B3 pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler B1) (encodePinsRecordForBook B1 pins)) =
      encodeBookTerm (specializeBook B1 pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler B2) (encodePinsRecordForBook B2 pins)) =
      encodeBookTerm (specializeBook B2 pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler B3) (encodePinsRecordForBook B3 pins)) =
      encodeBookTerm (specializeBook B3 pins) :=
  ⟨(inCoreBookCompiler_specializes_from_pinsOnly BaseRisc.baseRiscCore_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly PrivRisc.privilegeRiscCore_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly ComposedRisc.composedRiscCpu_book pins).1,
   futamura2BookCompiler_specializes_in_core BaseRisc.baseRiscCore_book pins,
   futamura2BookCompiler_specializes_in_core PrivRisc.privilegeRiscCore_book pins,
   futamura2BookCompiler_specializes_in_core ComposedRisc.composedRiscCpu_book pins⟩

end Obend.Apps.ObendRisc
end
