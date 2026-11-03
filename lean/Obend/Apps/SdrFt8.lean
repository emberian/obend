module

public import Lean
public import Obend.Core.Term
public import Obend.Core.Check
public import Obend.Equiv.Cost
public import Obend.Equiv.Improvement
public import Obend.Logic.Obligation
public import Obend.Logic.Program
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Leaf.Futamura
public import Obend.Spec.Parse
public import Obend.Spec.Elaborate
public import Obend.Spec.Workspace
public import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public import Obend.Spec.Sha256
public import Obend.Spec.CrossPackage
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.Accelerators
public import Obend.Hardware.RF
public import Obend.Hardware.DSP
public import Obend.Lower.Proofs.SelfAccelerate
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

/-!
# Flagship App #3: All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver (`Obend.Apps.SdrFt8`)

End-to-end formalization, multi-layer `.obend` elaboration, RF/DSP signoff proofs,
in-core Futamura 2nd projection specialization, stateful `always_ff` 3-stage CIC + folded
symmetric FIR + 4-stage CORDIC + $\Delta\phi[n] = \phi[n] - \phi[n-1]$ 8-FSK FT8 hardware
synthesis, 64-bit AMD `VOP64` GPU equivalence, and cross-package dependency cone verification
for **Flagship App #3 (`apps/sdr-ft8/`)**:

* `apps/sdr-ft8/TayloeQuadratureMixer.obend` — 40m ($7.074\text{ MHz}$) 4-phase ($0^\circ, 90^\circ, 180^\circ, 270^\circ$)
  Tayloe quadrature switching mixer & Hartley/Weaver image-sideband cancellation (`TayloeQuadratureMixer`,
  `UncalibratedTayloeMixer` $\to$ `Calibrated4PhaseTayloeOverride`).
* `apps/sdr-ft8/CicDecimatorFir.obend` — Stateful `always_ff` 3-stage Hogenauer CIC decimator
  ($R = 64, M = 1, N = 3$) and folded symmetric compensation FIR filter (`CicDecimatorFirChain`,
  `BaseCicDecimatorFirSpec` $\to$ `HogenauerCompensatedCicFirOverride`).
* `apps/sdr-ft8/CordicFt8Demod.obend` — 4-stage unrolled vectoring CORDIC `atan2`/`hypot` + stateful
  `always_ff` $\Delta\phi[n] = \phi[n] - \phi[n-1]$ 8-FSK FT8 tone discriminator (`CordicFt8Demodulator`,
  `BaseCordicFt8Spec` $\to$ `Unrolled4StageCordicFt8Override`).
* `apps/sdr-ft8/SdrFt8Top.obend` — Top-level all-digital 40m FT8 SDR transceiver (`SdrFt8Transceiver`,
  `Nominal40mSdrFt8Transceiver` $\to$ `Calibrated40mFt8TransceiverOverride`) importing `TayloeQuadratureMixer`,
  `CicDecimatorFir`, and `CordicFt8Demod`.
-/

@[expose] public section

namespace Obend.Apps.SdrFt8

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Spec.CrossPackage
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Synth
open Obend.Hardware.PlaceRoute
open Obend.Hardware.Accelerators
open Obend.Hardware.RF
open Obend.Hardware.DSP

set_option autoImplicit false

/-! ## 1. Module-Compatible Multi-File `#import_obend` Elaborator -/

def mkSdrByteArrayOfNatList (xs : List Nat) : ByteArray :=
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
    | _            => mkIdent ``Primitive.add

mutual
  meta partial def quoteSdrTermAux : Term → TSyntax `term
    | .hole n σ =>
      let sArr := (σ.map quoteSdrTermAux).toArray
      Lean.Unhygienic.run `(Term.hole $(quote n) [ $[$sArr],* ])
    | .bound i => Lean.Unhygienic.run `(Term.bound $(quote i))
    | .lam b => Lean.Unhygienic.run `(Term.lam $(quoteSdrTermAux b))
    | .app f a => Lean.Unhygienic.run `(Term.app $(quoteSdrTermAux f) $(quoteSdrTermAux a))
    | .mix l u => Lean.Unhygienic.run `(Term.mix $(quoteSdrTermAux l) $(quoteSdrTermAux u))
    | .fix s i => Lean.Unhygienic.run `(Term.fix $(quoteSdrTermAux s) $(quoteSdrTermAux i))
    | .specification m e => Lean.Unhygienic.run `(Term.specification $(quoteSdrTermAux m) $(quoteSdrTermAux e))
    | .prototype s g => Lean.Unhygienic.run `(Term.prototype $(quoteSdrTermAux s) $(quoteSdrTermAux g))
    | .reflect p => Lean.Unhygienic.run `(Term.reflect $(quoteSdrTermAux p))
    | .metadata p => Lean.Unhygienic.run `(Term.metadata $(quoteSdrTermAux p))
    | .project p => Lean.Unhygienic.run `(Term.project $(quoteSdrTermAux p))
    | .nat n => Lean.Unhygienic.run `(Term.nat $(quote n))
    | .boolean b => Lean.Unhygienic.run `(Term.boolean $(quote b))
    | .label l => Lean.Unhygienic.run `(Term.label $(quote l))
    | .binary op l r => Lean.Unhygienic.run `(Term.binary $(quote op) $(quoteSdrTermAux l) $(quoteSdrTermAux r))
    | .extend i fs =>
      let qfs := (fs.map quoteSdrFieldAux).toArray
      Lean.Unhygienic.run `(Term.extend $(quoteSdrTermAux i) [ $[$qfs],* ])
    | .record fs =>
      let qfs := (fs.map quoteSdrFieldAux).toArray
      Lean.Unhygienic.run `(Term.record [ $[$qfs],* ])
    | .get g p => Lean.Unhygienic.run `(Term.get $(quoteSdrTermAux g) $(quote p))
    | .ifZero v z s => Lean.Unhygienic.run `(Term.ifZero $(quoteSdrTermAux v) $(quoteSdrTermAux z) $(quoteSdrTermAux s))
    | .inject l p => Lean.Unhygienic.run `(Term.inject $(quote l) $(quoteSdrTermAux p))
    | .case sc arms =>
      let qarms := (arms.map quoteSdrFieldAux).toArray
      Lean.Unhygienic.run `(Term.case $(quoteSdrTermAux sc) [ $[$qarms],* ])
    | .ifBool c x y => Lean.Unhygienic.run `(Term.ifBool $(quoteSdrTermAux c) $(quoteSdrTermAux x) $(quoteSdrTermAux y))
    | .perform p => Lean.Unhygienic.run `(Term.perform $(quoteSdrTermAux p))
    | .done v => Lean.Unhygienic.run `(Term.done $(quoteSdrTermAux v))
    | .split t names f =>
      Lean.Unhygienic.run `(Term.split $(quoteSdrTermAux t) $(quote names) $(quoteSdrTermAux f))

  meta partial def quoteSdrFieldAux (kv : String × Term) : TSyntax `term :=
    Lean.Unhygienic.run `(($(quote kv.1), $(quoteSdrTermAux kv.2)))
end

meta instance : Quote Term where
  quote := quoteSdrTermAux

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

meta partial def quoteSdrRStepAux : RStep → TSyntax `term
  | .run n => Lean.Unhygienic.run `(RStep.run $(quote n))
  | .lateBinding m L => Lean.Unhygienic.run `(RStep.lateBinding $(quote m) $(quote L))
  | .assoc d => Lean.Unhygienic.run `(RStep.assoc $(quote d))
  | .composeAssoc d => Lean.Unhygienic.run `(RStep.composeAssoc $(quote d))
  | .congr ctx focus sub =>
    let qsub := (sub.map quoteSdrRStepAux).toArray
    Lean.Unhygienic.run `(RStep.congr $(quote ctx) $(quote focus) [ $[$qsub],* ])
  | .trans f s =>
    let qf := (f.map quoteSdrRStepAux).toArray
    let qs := (s.map quoteSdrRStepAux).toArray
    Lean.Unhygienic.run `(RStep.trans [ $[$qf],* ] [ $[$qs],* ])

meta instance : Quote RStep where
  quote := quoteSdrRStepAux

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
      Lean.Unhygienic.run `(Justification.byLoweredLean $(quote lowered) $(quote sups) (mkSdrByteArrayOfNatList $(quote (receipt.toList.map UInt8.toNat))))
    | .byExternalJudge fmt bs =>
      Lean.Unhygienic.run `(Justification.byExternalJudge $(quote fmt) (mkSdrByteArrayOfNatList $(quote (bs.toList.map UInt8.toNat))))
    | .byEval rows => Lean.Unhygienic.run `(Justification.byEval $(quote rows))

meta def defaultSdrLimits : Json :=
  Json.mkObj [
    ("heap", toJson "100000"),
    ("stack", toJson "100000"),
    ("ticks", toJson "100000"),
    ("checkWork", toJson "65536")
  ]

meta def normalizeSdrSource (src : String) : String :=
  let s := src.replace "\r\n" "\n"
  if s.endsWith "\n" then s else s ++ "\n"

meta def sanitizeSdrModName (stem : String) : String :=
  let chars := stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  match chars with
  | [] => "Main"
  | c :: _ =>
    let s := String.ofList (if c.isAlpha || c == '_' then chars else '_' :: chars)
    if Obend.Spec.Parse.isIdent s.toList then s else "Main"

meta def stripSdrImportQuotes (raw : String) : String :=
  let s := raw.trimAscii.toString
  if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
    ((s.drop 1).dropEnd 1).toString
  else
    s

meta def resolveSdrObendPath (path : System.FilePath) : IO System.FilePath := do
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

meta def resolveImportedSdrObendPath (parentFile : System.FilePath) (rawImportPath : String) :
    IO System.FilePath := do
  let clean := stripSdrImportQuotes rawImportPath
  let rel1 := match parentFile.parent with
    | some dir => dir / clean
    | none => System.FilePath.mk clean
  let r1 ← resolveSdrObendPath rel1
  if ← r1.pathExists then return r1
  let stripped := if clean.startsWith "./" then (clean.drop 2).toString else clean
  let rel2 := match parentFile.parent with
    | some dir => dir / stripped
    | none => System.FilePath.mk stripped
  let r2 ← resolveSdrObendPath rel2
  if ← r2.pathExists then return r2
  let r3 ← resolveSdrObendPath (System.FilePath.mk stripped)
  if ← r3.pathExists then return r3
  let fileName := (System.FilePath.mk stripped).fileName.getD stripped
  for sub in ["apps/sdr-ft8/", "stdlib/physical/", "stdlib/core/"] do
    let cand ← resolveSdrObendPath (System.FilePath.mk (sub ++ fileName))
    if ← cand.pathExists then return cand
  return r1

meta def parseAndCheckSdrObendModule (src : String) (moduleName : String)
    (prior : List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)) :
    Except String (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) := do
  let normSrc := normalizeSdrSource src
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
    let cleanPath := stripSdrImportQuotes edgePath
    let stemMod := sanitizeSdrModName ((System.FilePath.mk cleanPath).fileStem.getD edgeAlias)
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

meta def loadSdrObendModuleClosure :
    Nat → System.FilePath →
    List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) →
    IO (Except String (List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)))
  | 0, path, _ => return .error s!"import depth limit exceeded while loading {path}"
  | fuel + 1, path, acc => do
    let resolved ← resolveSdrObendPath path
    let modName := sanitizeSdrModName (resolved.fileStem.getD "Main")
    if acc.any (fun (sm, _) => sm.name == modName) then
      return .ok acc
    match ← (IO.FS.readBinFile resolved).toBaseIO with
    | .error e => return .error (toString e)
    | .ok bytes =>
      let some rawSrc := Obend.Spec.Parse.decodeSource bytes
        | return .error s!"{resolved}: invalid UTF-8"
      let normSrc := normalizeSdrSource rawSrc
      let ast ← match Obend.Spec.FrontEnd.parseSource modName normSrc with
        | .ok a => pure a
        | .error d => return .error s!"{d.stage}: {d.message}"
      let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
      let mut curAcc := acc
      for edge in parsedEdges.toList do
        let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
        let impFile ← resolveImportedSdrObendPath resolved edgePath
        match ← loadSdrObendModuleClosure fuel impFile curAcc with
        | .error err => return .error err
        | .ok nextAcc => curAcc := nextAcc
      match parseAndCheckSdrObendModule normSrc modName curAcc with
      | .error err => return .error err
      | .ok pair => return .ok (curAcc ++ [pair])

meta def resolveSdrKnotTerm (root : Term) (rawFields : List (String × Term)) (visiting : List String) :
    Nat → Term → Term
  | 0, t => t
  | fuel + 1, .get target name =>
    if Obend.Law.termEq target root then
      if visiting.contains name then .get root name
      else
        match rawFields.lookup name with
        | some rawBody =>
          let opened := Obend.Logic.openTerm rawBody root (.record [])
          resolveSdrKnotTerm root rawFields (name :: visiting) fuel opened
        | none => .get root name
    else
      .get (resolveSdrKnotTerm root rawFields visiting fuel target) name
  | fuel + 1, .lam b => .lam (resolveSdrKnotTerm root rawFields visiting fuel b)
  | fuel + 1, .app f a =>
    .app (resolveSdrKnotTerm root rawFields visiting fuel f) (resolveSdrKnotTerm root rawFields visiting fuel a)
  | fuel + 1, .mix l u =>
    .mix (resolveSdrKnotTerm root rawFields visiting fuel l) (resolveSdrKnotTerm root rawFields visiting fuel u)
  | fuel + 1, .fix s i =>
    .fix (resolveSdrKnotTerm root rawFields visiting fuel s) (resolveSdrKnotTerm root rawFields visiting fuel i)
  | fuel + 1, .specification m e =>
    .specification (resolveSdrKnotTerm root rawFields visiting fuel m) (resolveSdrKnotTerm root rawFields visiting fuel e)
  | fuel + 1, .prototype s g =>
    .prototype (resolveSdrKnotTerm root rawFields visiting fuel s) (resolveSdrKnotTerm root rawFields visiting fuel g)
  | fuel + 1, .reflect p => .reflect (resolveSdrKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .metadata p => .metadata (resolveSdrKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .project p => .project (resolveSdrKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .binary op l r =>
    .binary op (resolveSdrKnotTerm root rawFields visiting fuel l) (resolveSdrKnotTerm root rawFields visiting fuel r)
  | fuel + 1, .extend i fs =>
    .extend (resolveSdrKnotTerm root rawFields visiting fuel i)
      (fs.map fun (k, v) => (k, resolveSdrKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .record fs =>
    .record (fs.map fun (k, v) => (k, resolveSdrKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifZero v z s =>
    .ifZero (resolveSdrKnotTerm root rawFields visiting fuel v)
      (resolveSdrKnotTerm root rawFields visiting fuel z)
      (resolveSdrKnotTerm root rawFields visiting fuel s)
  | fuel + 1, .inject l p => .inject l (resolveSdrKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .case sc arms =>
    .case (resolveSdrKnotTerm root rawFields visiting fuel sc)
      (arms.map fun (k, v) => (k, resolveSdrKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifBool c x y =>
    .ifBool (resolveSdrKnotTerm root rawFields visiting fuel c)
      (resolveSdrKnotTerm root rawFields visiting fuel x)
      (resolveSdrKnotTerm root rawFields visiting fuel y)
  | fuel + 1, .perform p => .perform (resolveSdrKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .done v => .done (resolveSdrKnotTerm root rawFields visiting fuel v)
  | fuel + 1, .split t names f =>
    .split (resolveSdrKnotTerm root rawFields visiting fuel t) names
      (resolveSdrKnotTerm root rawFields visiting fuel f)
  | _ + 1, t => t

meta def decodeSdrWithSeed (want : Composition → Bool) : Term → Option Composition
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

meta def findSdrObject (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match decodeSdrWithSeed want t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (findSdrObject want fuel)

meta def findSdrSelfGetCtx (selfIdx : Nat) : Term → Option (Term × String)
  | .get (.bound i) m =>
    if i == selfIdx then some (.bound 0, m) else none
  | .app f a =>
    match findSdrSelfGetCtx selfIdx f with
    | some (ctxF, m) => some (.app ctxF (a.rename Nat.succ), m)
    | none =>
      (findSdrSelfGetCtx selfIdx a).map fun (ctxA, m) => (.app (f.rename Nat.succ) ctxA, m)
  | .binary op l r =>
    match findSdrSelfGetCtx selfIdx l with
    | some (ctxL, m) => some (.binary op ctxL (r.rename Nat.succ), m)
    | none =>
      (findSdrSelfGetCtx selfIdx r).map fun (ctxR, m) => (.binary op (l.rename Nat.succ) ctxR, m)
  | _ => none

meta def deriveSdrClaim (o : ClaimObj) (r : Term) : Nat → Term → List RStep → Option (List RStep)
  | 0, _, _ => none
  | fuel + 1, t, acc =>
    if Obend.Law.termEq t r then some acc.reverse
    else match Obend.Law.step? t with
    | some t' => deriveSdrClaim o r fuel t' (Obend.Logic.Program.pushRun acc)
    | none =>
      match findSdrSelfGetCtx o.self t with
      | some (ctx, m) =>
        match Obend.Logic.symUnfold o.comp o.self m with
        | some (L, _) =>
          let step : RStep :=
            if Obend.Law.termEq ctx (.bound 0) then .lateBinding m L
            else .congr ctx (.get (.bound o.self) m) [.lateBinding m L]
          match Obend.Logic.apply (Obend.Logic.claimResolver o.comp o.self) step t with
          | .ok t' => deriveSdrClaim o r fuel t' (step :: acc)
          | .error _ => none
        | none => none
      | none => none

meta def proposeSdrDerivation (o : ClaimObj) : Option (List RStep) :=
  match Obend.Logic.Program.proposeDerivation o with
  | some steps => some steps
  | none =>
    match o.sides with
    | some (_, l, r) => deriveSdrClaim o r 4096 l []
    | none => none

meta structure SdrElaboratedDef where
  name         : String
  composition? : Option Composition
  book?        : Option Book

meta structure SdrElaboratedClaim where
  name     : String
  claimObj : ClaimObj
  just?    : Option Justification
  verified : Bool

meta structure SdrElaboratedModule where
  moduleName : String
  defs       : List SdrElaboratedDef
  claims     : List SdrElaboratedClaim

meta def compactSdrLayerForKernel (L : Layer) : Layer :=
  { L with
    metadata := .record [("name", .label L.name)]
    fields := L.fields.filter (fun kv => kv.1 != "#kind")
    composeMeta := .record [] }

meta def compactSdrCompositionForKernel (C : Composition) : Composition :=
  { C with
    top := compactSdrLayerForKernel C.top
    below := C.below.map compactSdrLayerForKernel
    seed := C.seed.filter (fun kv => kv.1 != "#kind") }

meta def elaborateSdrObendFile (pathStr : String) : IO (Except String SdrElaboratedModule) := do
  let closure ← match ← loadSdrObendModuleClosure 32 (System.FilePath.mk pathStr) [] with
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
      (Json.arr #[]) (Json.arr #[]) defaultSdrLimits "definition" [] with
  | .error d => return .error s!"{d.stage}: {d.message}"
  | .ok lowering =>
    match Obend.Spec.FrontEnd.accept lowering with
    | .error d => return .error s!"{d.stage}: {d.message}"
    | .ok acc =>
      let erasedTerm := acc.erased
      let rootTerm := (Obend.Logic.Program.knotOf erasedTerm).getD erasedTerm
      let rawFields := Obend.Logic.Program.knotFields rootTerm
      let mut pdefs : List SdrElaboratedDef := []
      for d in callables do
        let shortName := d.name
        let fullKey := modName ++ "." ++ shortName
        let knotTerm : Term := .get rootTerm fullKey
        let opened := match rawFields.lookup fullKey with
          | some rb => Obend.Logic.openTerm rb rootTerm (.record [])
          | none => knotTerm
        let wantNamed : Composition → Bool := fun C => C.top.name != ""
        let rawComp? :=
          match findSdrObject wantNamed 64 knotTerm with
          | some c => some c
          | none =>
            match findSdrObject wantNamed 64 (.app knotTerm (.record [])) with
            | some c => some c
            | none =>
              let inlined := resolveSdrKnotTerm rootTerm rawFields [fullKey] 4 opened
              decodeSdrWithSeed wantNamed inlined
        let foundComp? := rawComp?.map compactSdrCompositionForKernel
        let book? := foundComp?.map Obend.Leaf.emit
        pdefs := pdefs ++ [{
          name := shortName
          composition? := foundComp?
          book? := book?
        }]
      let rawClaimPairs := Obend.Logic.Program.claimFields rootTerm
      let mut pclaims : List SdrElaboratedClaim := []
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
              let steps? := proposeSdrDerivation co
              let just? := steps?.map Justification.byDerivation
              let ok := match just? with
                | some j => Obend.Logic.obligationCheck 64 co j == .ok
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

theorem sdrObligationMeaning_of_check_beq
    (formats : List Judge.Format) {k : Nat} {o : ClaimObj} {j : Justification}
    (h : (Obend.Logic.obligationCheckWithJudges formats k o j == .ok) = true) :
    Obend.Logic.obligationMeaningWithJudges formats o j :=
  Obend.Logic.obligationWithJudges_sound formats (beq_iff_eq.1 h)

local elab "#import_obend " pathLit:str " as " nsId:ident : command => do
  let pathStr := pathLit.getString
  let res ← IO.toEIO
    (fun e => Lean.Exception.error Lean.Syntax.missing (Lean.MessageData.ofFormat (Std.Format.text (toString e))))
    (elaborateSdrObendFile pathStr)
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
              sdrObligationMeaning_of_check_beq Obend.Logic.defaultExternalFormats (k := 64) (o := $objId) (j := $justId) (by decide +kernel)
          ))

/-! ## 2. Compile-Time Elaboration of `apps/sdr-ft8/*.obend` -/

#import_obend "apps/sdr-ft8/TayloeQuadratureMixer.obend" as SdrTayloe
#import_obend "apps/sdr-ft8/CicDecimatorFir.obend" as SdrCicFir
#import_obend "apps/sdr-ft8/CordicFt8Demod.obend" as SdrCordicFt8
#import_obend "apps/sdr-ft8/SdrFt8Top.obend" as SdrFt8Top

/-- **Master `.obend` Acceptance & Open-Recursion Theorem for `apps/sdr-ft8/`**:
    All four `.obend` modules in `apps/sdr-ft8/` pass `FrontEnd.accept` at Lean compile time,
    and all seven open-recursive `claim` declarations hold in `Obend.Logic.obligationMeaningWithJudges`. -/
theorem sdr_ft8_all_accepted_and_claims_hold :
    SdrTayloe.accepted = true ∧
    SdrCicFir.accepted = true ∧
    SdrCordicFt8.accepted = true ∧
    SdrFt8Top.accepted = true ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SdrTayloe.claim_image_cancel_open_recursion_obj
      SdrTayloe.claim_image_cancel_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SdrCicFir.claim_cic_comb_open_recursion_obj
      SdrCicFir.claim_cic_comb_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SdrCicFir.claim_folded_fir_open_recursion_obj
      SdrCicFir.claim_folded_fir_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SdrCordicFt8.claim_cordic_mag_open_recursion_obj
      SdrCordicFt8.claim_cordic_mag_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SdrCordicFt8.claim_ft8_tone_bin_open_recursion_obj
      SdrCordicFt8.claim_ft8_tone_bin_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SdrFt8Top.claim_demod_ft8_open_recursion_obj
      SdrFt8Top.claim_demod_ft8_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SdrFt8Top.claim_rx_sensitivity_open_recursion_obj
      SdrFt8Top.claim_rx_sensitivity_open_recursion_just :=
  ⟨ SdrTayloe.accepted_eq
  , SdrCicFir.accepted_eq
  , SdrCordicFt8.accepted_eq
  , SdrFt8Top.accepted_eq
  , SdrTayloe.claim_image_cancel_open_recursion_holds
  , SdrCicFir.claim_cic_comb_open_recursion_holds
  , SdrCicFir.claim_folded_fir_open_recursion_holds
  , SdrCordicFt8.claim_cordic_mag_open_recursion_holds
  , SdrCordicFt8.claim_ft8_tone_bin_open_recursion_holds
  , SdrFt8Top.claim_demod_ft8_open_recursion_holds
  , SdrFt8Top.claim_rx_sensitivity_open_recursion_holds ⟩

/-! ## 3. Open-Recursive Compositions, Vtable Flattening & `Leaf.Book` Soundness -/

def tayloeMixerComp : Composition :=
  SdrTayloe.calibratedTayloeMixer_comp

def cicFirChainComp : Composition :=
  SdrCicFir.compensatedCicFirChain_comp

def cordicFt8DemodComp : Composition :=
  SdrCordicFt8.unrolled4StageCordicFt8Demod_comp

def nominal40mSdrFt8Comp : Composition :=
  SdrFt8Top.nominal40mSdrFt8_comp

def sdrFt8TopComp : Composition :=
  SdrFt8Top.calibrated40mSdrFt8_comp

theorem tayloeMixerComp_closed : tayloeMixerComp.closedB = true := by decide +kernel
theorem cicFirChainComp_closed : cicFirChainComp.closedB = true := by decide +kernel
theorem cordicFt8DemodComp_closed : cordicFt8DemodComp.closedB = true := by decide +kernel
theorem nominal40mSdrFt8Comp_closed : nominal40mSdrFt8Comp.closedB = true := by decide +kernel
theorem sdrFt8TopComp_closed : sdrFt8TopComp.closedB = true := by decide +kernel

/-- **Vtable Flattening & Leaf Book Soundness across all 4 `apps/sdr-ft8/` Layers**. -/
theorem sdr_ft8_flatten_and_book_sound (m : String) :
    (.get tayloeMixerComp.flatten m ≈b .get tayloeMixerComp.object m) ∧
    (.get (emit tayloeMixerComp).link m ≈b .get tayloeMixerComp.object m) ∧
    (.get cicFirChainComp.flatten m ≈b .get cicFirChainComp.object m) ∧
    (.get (emit cicFirChainComp).link m ≈b .get cicFirChainComp.object m) ∧
    (.get cordicFt8DemodComp.flatten m ≈b .get cordicFt8DemodComp.object m) ∧
    (.get (emit cordicFt8DemodComp).link m ≈b .get cordicFt8DemodComp.object m) ∧
    (.get sdrFt8TopComp.flatten m ≈b .get sdrFt8TopComp.object m) ∧
    (.get (emit sdrFt8TopComp).link m ≈b .get sdrFt8TopComp.object m) :=
  ⟨ flatten_sound tayloeMixerComp tayloeMixerComp_closed m
  , book_sound tayloeMixerComp tayloeMixerComp_closed m
  , flatten_sound cicFirChainComp cicFirChainComp_closed m
  , book_sound cicFirChainComp cicFirChainComp_closed m
  , flatten_sound cordicFt8DemodComp cordicFt8DemodComp_closed m
  , book_sound cordicFt8DemodComp cordicFt8DemodComp_closed m
  , flatten_sound sdrFt8TopComp sdrFt8TopComp_closed m
  , book_sound sdrFt8TopComp sdrFt8TopComp_closed m ⟩

/-- **Static `super` Elimination & Slot Dependency Certificate for `SdrFt8Top.obend`**. -/
theorem sdrFt8Top_book_shape_verified :
    let B := emit sdrFt8TopComp
    B.slots = [ "imageRejectionDb"
              , "friisNoiseFactorMilli"
              , "ddcFilteredMag"
              , "carrierFreqKhz"
              , "demodFt8SymbolStream"
              , "rxSensitivityMarginDb" ] ∧
    B.defs.map (fun d => (d.member, d.slot, d.kind, d.reads)) =
      [ ("imageRejectionDb", 0, .cell, [])
      , ("friisNoiseFactorMilli", 1, .cell, [])
      , ("ddcFilteredMag", 2, .method, [])
      , ("carrierFreqKhz", 3, .cell, [])
      , ("demodFt8SymbolStream", 4, .method, [0])
      , ("rxSensitivityMarginDb", 5, .method, [1])
      ] ∧
    B.closedB = true := by
  decide +kernel

/-! ## 4. In-Core Futamura 2nd Projection (`sdr_ft8_inCore_futamura2`) -/

/-- **In-Core Futamura 2nd Projection for `apps/sdr-ft8/` (`sdr_ft8_inCore_futamura2`)**:
    1. `inCoreBookCompiler` specializes the pins-only encoding of `SdrFt8Top`, `SdrCicFir`,
       and `SdrCordicFt8` directly inside Core4 (`inCoreBookCompiler_specializes_from_pinsOnly`).
    2. `futamura2BookCompiler` specializes the full `Book` encoding in Core4 (`futamura2BookCompiler_specializes_in_core`). -/
theorem sdr_ft8_inCore_futamura2 (pins : List LeafPin) :
    let Btop := SdrFt8Top.calibrated40mSdrFt8_book
    let Bcic := SdrCicFir.compensatedCicFirChain_book
    let Bcordic := SdrCordicFt8.unrolled4StageCordicFt8Demod_book
    dataPinSpecialize (.app (inCoreBookCompiler Btop) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook Btop pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler Bcic) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook Bcic pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler Bcordic) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook Bcordic pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler Btop) (encodePinsRecordForBook Btop pins)) =
      encodeBookTerm (specializeBook Btop pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler Bcic) (encodePinsRecordForBook Bcic pins)) =
      encodeBookTerm (specializeBook Bcic pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler Bcordic) (encodePinsRecordForBook Bcordic pins)) =
      encodeBookTerm (specializeBook Bcordic pins) :=
  ⟨ (inCoreBookCompiler_specializes_from_pinsOnly SdrFt8Top.calibrated40mSdrFt8_book pins).1
  , (inCoreBookCompiler_specializes_from_pinsOnly SdrCicFir.compensatedCicFirChain_book pins).1
  , (inCoreBookCompiler_specializes_from_pinsOnly SdrCordicFt8.unrolled4StageCordicFt8Demod_book pins).1
  , futamura2BookCompiler_specializes_in_core SdrFt8Top.calibrated40mSdrFt8_book pins
  , futamura2BookCompiler_specializes_in_core SdrCicFir.compensatedCicFirChain_book pins
  , futamura2BookCompiler_specializes_in_core SdrCordicFt8.unrolled4StageCordicFt8Demod_book pins ⟩

/-! ## 5. Tayloe IQ Image Rejection, Hogenauer CIC Bit-Width, Folded Symmetric FIR & 4-Stage CORDIC Proofs -/

/-- **3-stage Hogenauer CIC specification (`sdrFt8Cic3Spec`)** for the 40m FT8 SDR DDC:
$B_{\text{in}} = 16\text{ bits}$, $N = 3\text{ stages}$, $R = 64$ ($\lceil\log_2(64 \times 1)\rceil = 6$),
requiring $B_{\text{out}} = 16 + 3 \times 6 = 34\text{ bits}$ (allocated inside 36-bit / 64-bit registers). -/
def sdrFt8Cic3Spec : CicFilterSpec where
  filterName      := "sdr_ft8_cic3_r64_m1"
  inputWidthBits  := 16
  numStages       := 3
  decimationRatio := 64
  diffDelay       := 1
  ceilLog2Rm      := 6

/-- **Theorem (`sdr_ft8_image_rejection_and_ddc_signoff_sound`)**:
Connects the `apps/sdr-ft8/` `.obend` transceiver stack to the RF and DSP mathematical theorems:
1. **Tayloe Quadrature Image-Sideband Cancellation (`tayloe_iq_cancels_image_sideband`)**:
   When $I/Q$ conversion gains match (`gainI = gainQ`) and quadrature phase skew is zero (`phaseErr = 0`),
   the opposite-sideband image cancels identically (`evalQuadratureImagePhaseCancel = 0`) while the
   desired sideband coherently doubles (`evalQuadratureDesiredSideband = 2 * gainI * sigAmp`).
2. **40m FT8 RF Front-End & Cascaded Friis Noise Signoff (`rf_transceiver_signoff_poles`, `golden3StageSdrRxChain_verified`)**:
   `checkRfTransceiverSignoff golden40mFt8TransceiverCert = true`, refusing unfiltered PA harmonic
   violations and $6:1$ VSWR mismatches, while the 3-stage LNA + Tayloe + PGA receiver front-end
   achieves $+38.0\text{ dB}$ (`380` tenths dB) gain and $1410$ milli-NF ($\approx 1.49\text{ dB}$ NF).
3. **3-Stage Hogenauer CIC Bit-Growth Bound (`cic_register_width_sound`)**:
   `sdrFt8Cic3Spec` requires $16 + 3 \times 6 = 34\text{ bits}$ and passes `checkCicOverflowFree`
   at $36\text{ bits}$.
4. **Folded Symmetric FIR Multiplier Halving (`firSymmetric_folds_multipliers`)**:
   Pre-adding symmetric delay-line samples `coeff * (xEarly + xLate)` equals the 2-multiplier
   direct form `coeff * xEarly + coeff * xLate` identically for all `coeff, xEarly, xLate`.
5. **4-Stage Unrolled CORDIC Convergence (`cordic_4stage_pipeline_verified`)**:
   `runCordicMicroPipeline 1000 0 442 goldenCordic4Stages = (1484, 704, 0)` with zero residual
   angle error (`z4 = 0`).
6. **End-to-End SDR DDC Signoff (`sdrDdcChain_signoff_sound`, `sdrDdcChain_signoff_poles`)**:
   `checkSdrDdcSignoff goldenSdrDdcChainSpec = true`, guaranteeing NCO phase bounds, $10\times$
   2-stage CORDIC LO norm scaling, zero image residual, overflow-free CIC accumulators, and
   exact folded symmetric FIR sample equivalence. -/
theorem sdr_ft8_image_rejection_and_ddc_signoff_sound :
    (∀ (gainI gainQ phaseErr sigAmp : Int),
      gainI = gainQ → phaseErr = 0 →
      evalQuadratureImagePhaseCancel gainI gainQ phaseErr sigAmp = 0 ∧
      evalQuadratureDesiredSideband gainI gainQ sigAmp = 2 * gainI * sigAmp) ∧
    checkRfTransceiverSignoff golden40mFt8TransceiverCert = true ∧
    checkRfTransceiverSignoff unfilteredPaTransceiverCert = false ∧
    checkRfTransceiverSignoff highVswrTransceiverCert = false ∧
    evalCascadedGainDbTenths golden3StageSdrRxChain = 380 ∧
    evalCascadedFriisMilliNf golden3StageSdrRxChain = 1410 ∧
    evalCicRequiredWidthBits sdrFt8Cic3Spec = 34 ∧
    checkCicOverflowFree sdrFt8Cic3Spec 36 = true ∧
    (sdrFt8Cic3Spec.inputWidthBits ≤ evalCicRequiredWidthBits sdrFt8Cic3Spec ∧
     evalCicRequiredWidthBits sdrFt8Cic3Spec ≤ 36) ∧
    (∀ (coeff xEarly xLate : Int),
      evalFoldedSymmetricFirTapPair coeff xEarly xLate =
      evalDirectFirTapPair coeff xEarly xLate) ∧
    runCordicMicroPipeline 1000 0 442 goldenCordic4Stages = (1484, 704, 0) ∧
    checkSdrDdcSignoff goldenSdrDdcChainSpec = true ∧
    checkSdrDdcSignoff unbalancedIqSdrDdcSpec = false ∧
    checkSdrDdcSignoff underAllocatedCicSdrDdcSpec = false ∧
    (∀ (rfSigAmp xEarly xLate : Int),
      (stepNco goldenSdrDdcChainSpec.nco).phaseWord < goldenSdrDdcChainSpec.nco.phaseModulus ∧
      evalQuadratureImagePhaseCancel goldenSdrDdcChainSpec.iqGainI goldenSdrDdcChainSpec.iqGainQ
        goldenSdrDdcChainSpec.iqPhaseErr rfSigAmp = 0 ∧
      evalSymmetricFirTapPair goldenSdrDdcChainSpec.firTapCoeff xEarly xLate =
        evalDirectFirTapPair goldenSdrDdcChainSpec.firTapCoeff xEarly xLate) := by
  refine ⟨ tayloe_iq_cancels_image_sideband
         , rf_transceiver_signoff_poles.1
         , rf_transceiver_signoff_poles.2.1
         , rf_transceiver_signoff_poles.2.2
         , golden3StageSdrRxChain_verified.1
         , golden3StageSdrRxChain_verified.2.1
         , rfl
         , rfl
         , cic_register_width_sound sdrFt8Cic3Spec 36 rfl
         , firSymmetric_folds_multipliers
         , cordic_4stage_pipeline_verified.1
         , sdrDdcChain_signoff_poles.1
         , sdrDdcChain_signoff_poles.2.1
         , sdrDdcChain_signoff_poles.2.2.2
         , ?_ ⟩
  intro rfSigAmp xEarly xLate
  have hDdc := sdrDdcChain_signoff_sound goldenSdrDdcChainSpec rfSigAmp xEarly xLate rfl
  exact ⟨hDdc.1, hDdc.2.2.1, hDdc.2.2.2.2.2.1⟩

/-! ## 6. Hardware Synthesis: `.obend` Books, Stateful `always_ff` 3-Stage CIC + Folded FIR + CORDIC $\Delta\phi$ FT8 Demodulator & AMD `VOP64` GPU -/

/-- Compile all 4 `apps/sdr-ft8/` `.obend` `Book`s to `RtlModule`s via `compileBookToRtl`. -/
def tayloeMixerRtl? : Option RtlModule :=
  compileBookToRtl "sdr_tayloe_mixer" SdrTayloe.calibratedTayloeMixer_book

def cicFirRtl? : Option RtlModule :=
  compileBookToRtl "sdr_cic_fir" SdrCicFir.compensatedCicFirChain_book

def cordicFt8Rtl? : Option RtlModule :=
  compileBookToRtl "sdr_cordic_ft8" SdrCordicFt8.unrolled4StageCordicFt8Demod_book

def sdrFt8TopRtl? : Option RtlModule :=
  compileBookToRtl "sdr_ft8_top_book" SdrFt8Top.calibrated40mSdrFt8_book

/-- **Stateful `always_ff` 40m Tayloe IQ + 3-Stage CIC + Folded FIR + CORDIC $\Delta\phi$ FT8 RTL Module
(`sdrFt8SequentialRtlModule`)**:

Inputs (`inputPorts`):
* `in 0` (`i_mix_mv`): In-phase Tayloe quadrature mixer output sample $I[n]$,
* `in 1` (`q_mix_mv`): Quadrature Tayloe mixer output sample $Q[n]$ (shifted by $+90^\circ$ Hilbert path),
* `in 2` (`cordic_phase_mrad`): Instantaneous 4-stage CORDIC unwrapped phase $\phi[n]$ in mrad,
* `in 3` (`decim_strobe`): Decimation strobe ($1$ on $R=64$ decimated symbol boundary, $0$ between),
* `in 4` (`clk_en`): Master synchronous clock enable (`inputPorts.length - 1 = 4`).

Synchronous `always_ff` Registers (`regs`):
* `reg 0` (`cic_int1`, init `0`): 1st-stage Hogenauer CIC integrator $z^{-1}$ register,
* `reg 1` (`cic_int2`, init `0`): 2nd-stage Hogenauer CIC integrator $z^{-1}$ register,
* `reg 2` (`cic_int3`, init `0`): 3rd-stage Hogenauer CIC integrator $z^{-1}$ register,
* `reg 3` (`cic_comb_d1`, init `0`): CIC comb stage $z^{-1}$ delay register,
* `reg 4` (`fir_tap_d1`, init `0`): Folded symmetric FIR delay-line register,
* `reg 5` (`prev_phase_mrad`, init `0`): Previous symbol CORDIC phase register $\phi[n-1]$ for
  stateful $\Delta\phi[n] = \phi[n] - \phi[n-1]$ FT8 8-FSK tone discrimination. -/
def sdrFt8SequentialRtlModule : RtlModule where
  name := "sdr_ft8_top"
  inputNames := ["i_mix_mv", "q_mix_mv", "cordic_phase_mrad", "decim_strobe"]
  wires :=
    [ { wireIdx := 0
        name := "desired_usb_comb"
        expr := .alu .add (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 1
        name := "image_cancel_comb"
        expr := .alu .sub (.inputPort 0) (.inputPort 1) }
    , { wireIdx := 2
        name := "comb_diff_comb"
        expr := .alu .sub (.regRead 2) (.regRead 3) }
    ]
  regs :=
    [ { regIdx := 0
        name := "cic_int1"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .alu .add (.regRead 0) (.wireRef 0) }
    , { regIdx := 1
        name := "cic_int2"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .alu .add (.regRead 1) (.alu .add (.regRead 0) (.wireRef 0)) }
    , { regIdx := 2
        name := "cic_int3"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr :=
          .alu .add (.regRead 2)
            (.alu .add (.regRead 1)
              (.alu .add (.regRead 0) (.wireRef 0))) }
    , { regIdx := 3
        name := "cic_comb_d1"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .mux (.inputPort 3) (.regRead 2) (.regRead 3) }
    , { regIdx := 4
        name := "fir_tap_d1"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .mux (.inputPort 3) (.wireRef 2) (.regRead 4) }
    , { regIdx := 5
        name := "prev_phase_mrad"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .mux (.inputPort 3) (.inputPort 2) (.regRead 5) }
    ]
  outputs :=
    [ { name := "desired_usb_mv"
        expr := .wireRef 0 }
    , { name := "image_cancel_mv"
        expr := .wireRef 1 }
    , { name := "folded_fir_out"
        expr := .alu .mul (.alu .add (.wireRef 2) (.regRead 4)) (.const 256#64) }
    , { name := "delta_phase_mrad"
        expr := .alu .sub (.inputPort 2) (.regRead 5) }
    ]

/-- **Theorem (`sdr_ft8_rtl_and_bel_synthesis_verified`)**:
1. All 4 `apps/sdr-ft8/` `.obend` `Book`s (`TayloeQuadratureMixer`, `CicDecimatorFir`,
   `CordicFt8Demod`, `SdrFt8Top`) compile to well-formed `RtlModule`s (`checkRtlModule = true`)
   and valid FPGA `BelNetlist`s (`checkBelNetlistValid = true`), and
2. The stateful `always_ff` 3-stage CIC + folded symmetric FIR + CORDIC $\Delta\phi$ FT8 module
   `sdrFt8SequentialRtlModule` passes `checkRtlModule` and lowers to a valid `BelNetlist` with
   6 `FDRE` flip-flop registers. -/
theorem sdr_ft8_rtl_and_bel_synthesis_verified :
    checkRtlModule sdrFt8SequentialRtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels sdrFt8SequentialRtlModule) = true ∧
    sdrFt8SequentialRtlModule.regs.length = 6 ∧
    (match tayloeMixerRtl?, cicFirRtl?, cordicFt8Rtl?, sdrFt8TopRtl? with
     | some m1, some m2, some m3, some m4 =>
       checkRtlModule m1 &&
       checkRtlModule m2 &&
       checkRtlModule m3 &&
       checkRtlModule m4 &&
       checkBelNetlistValid (synthesizeModuleToBels m1) &&
       checkBelNetlistValid (synthesizeModuleToBels m2) &&
       checkBelNetlistValid (synthesizeModuleToBels m3) &&
       checkBelNetlistValid (synthesizeModuleToBels m4)
     | _, _, _, _ => false) = true := by
  decide +kernel

/-- Concrete 4-cycle SDR DDC + CORDIC $\Delta\phi$ FT8 input stimulus:
* **Cycle 0**: Matched Tayloe IQ (`i_mix = 500`, `q_mix = 500`), initial CORDIC phase $\phi[0] = 100\text{ mrad}$, `decim_strobe = 1`
* **Cycle 1**: Matched Tayloe IQ (`i_mix = 500`, `q_mix = 500`), CORDIC phase $\phi[1] = 350\text{ mrad}$ ($\Delta\phi = 250\text{ mrad}$, FT8 tone 2), `decim_strobe = 1`
* **Cycle 2**: Matched Tayloe IQ (`i_mix = 500`, `q_mix = 500`), CORDIC phase $\phi[2] = 975\text{ mrad}$ ($\Delta\phi = 625\text{ mrad}$, FT8 tone 5), `decim_strobe = 1`
* **Cycle 3**: Matched Tayloe IQ (`i_mix = 500`, `q_mix = 500`), CORDIC phase $\phi[3] = 1850\text{ mrad}$ ($\Delta\phi = 875\text{ mrad}$, FT8 tone 7), `decim_strobe = 1`. -/
def sdrFt8Cycle0Inputs : Nat → BitVec 64
  | 0 => 500#64
  | 1 => 500#64
  | 2 => 100#64
  | 3 => 1#64
  | _ => 0#64

def sdrFt8Cycle1Inputs : Nat → BitVec 64
  | 0 => 500#64
  | 1 => 500#64
  | 2 => 350#64
  | 3 => 1#64
  | _ => 0#64

def sdrFt8Cycle2Inputs : Nat → BitVec 64
  | 0 => 500#64
  | 1 => 500#64
  | 2 => 975#64
  | 3 => 1#64
  | _ => 0#64

def sdrFt8Cycle3Inputs : Nat → BitVec 64
  | 0 => 500#64
  | 1 => 500#64
  | 2 => 1850#64
  | 3 => 1#64
  | _ => 0#64

/-- **Theorem (`sdr_ft8_sequential_cic_cordic_trace_verified`)**:
Simulates `sdrFt8SequentialRtlModule` across the 4-cycle FT8 symbol trace and proves:
1. **Tayloe Image Cancellation (`image_cancel_mv = 0`) & Coherent Desired Sideband (`desired_usb_mv = 1000`)**
   hold across all cycles,
2. **3-Stage Hogenauer CIC Integrator Accumulation**:
   - After Cycle 0: `cic_int1 = 1000`, `cic_int2 = 1000`, `cic_int3 = 1000`,
   - After Cycle 1: `cic_int1 = 2000`, `cic_int2 = 3000`, `cic_int3 = 4000`,
   - After Cycle 2: `cic_int1 = 3000`, `cic_int2 = 6000`, `cic_int3 = 10000`,
   - After Cycle 3: `cic_int1 = 4000`, `cic_int2 = 10000`, `cic_int3 = 20000`,
3. **Folded Symmetric FIR Output (`folded_fir_out`)**:
   At Cycle 2 (with `cic_int3 = 4000`, `cic_comb_d1 = 1000`, `fir_tap_d1 = 1000`),
   `folded_fir_out = ((4000 - 1000) + 1000) * 256 = 1024000`, and
4. **Stateful $\Delta\phi[n] = \phi[n] - \phi[n-1]$ 8-FSK FT8 Tone Discrimination**:
   - Cycle 1 output `delta_phase_mrad = 350 - 100 = 250#64`,
   - Cycle 2 output `delta_phase_mrad = 975 - 350 = 625#64`,
   - Cycle 3 output `delta_phase_mrad = 1850 - 975 = 875#64`. -/
theorem sdr_ft8_sequential_cic_cordic_trace_verified :
    let initRegs : Nat → BitVec 64 := fun _ => 0#64
    let regsAfter1 := stepModuleRegs sdrFt8SequentialRtlModule false sdrFt8Cycle0Inputs initRegs
    let regsAfter2 := stepModuleRegs sdrFt8SequentialRtlModule false sdrFt8Cycle1Inputs regsAfter1
    let regsAfter3 := stepModuleRegs sdrFt8SequentialRtlModule false sdrFt8Cycle2Inputs regsAfter2
    let regsAfter4 := stepModuleRegs sdrFt8SequentialRtlModule false sdrFt8Cycle3Inputs regsAfter3
    evalModuleOutputs sdrFt8SequentialRtlModule sdrFt8Cycle1Inputs regsAfter1 =
      [ ("desired_usb_mv", 1000#64)
      , ("image_cancel_mv", 0#64)
      , ("folded_fir_out", 256000#64)
      , ("delta_phase_mrad", 250#64) ] ∧
    evalModuleOutputs sdrFt8SequentialRtlModule sdrFt8Cycle2Inputs regsAfter2 =
      [ ("desired_usb_mv", 1000#64)
      , ("image_cancel_mv", 0#64)
      , ("folded_fir_out", 1024000#64)
      , ("delta_phase_mrad", 625#64) ] ∧
    evalModuleOutputs sdrFt8SequentialRtlModule sdrFt8Cycle3Inputs regsAfter3 =
      [ ("desired_usb_mv", 1000#64)
      , ("image_cancel_mv", 0#64)
      , ("folded_fir_out", 2304000#64)
      , ("delta_phase_mrad", 875#64) ] ∧
    regsAfter4 0 = 4000#64 ∧
    regsAfter4 1 = 10000#64 ∧
    regsAfter4 2 = 20000#64 ∧
    regsAfter4 5 = 1850#64 := by
  decide +kernel

/-- **64-Bit AMD `VOP64` GPU Co-Execution Certificate for `SdrFt8Top.obend`**:
    Compiles `SdrFt8Top`'s `ddcFilteredMag`, `demodFt8SymbolStream`, and `rxSensitivityMarginDb`
    hardware wires via `compileRtlExprToAmdGpu` and verifies exact 64-bit `runAmdGpuVop64Prog`
    equivalence with FPGA RTL evaluation, plus universal `evalAmdGpuExpr_nested_sound`. -/
def sdrFt8DdcCordicGpuExpr : RtlExpr :=
  .alu .add
    (.alu .mul
      (.alu .add (.alu .sub (.regRead 2) (.regRead 3)) (.regRead 4))
      (.const 256#64))
    (.alu .sub (.inputPort 2) (.regRead 5))

theorem sdr_ft8_amdgpu_vop64_equivalence :
    (match sdrFt8TopRtl? with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 100#64) (fun _ => 0#64) ==
         [ ("out_imageRejectionDb", 68#64)
         , ("out_friisNoiseFactorMilli", 1410#64)
         , ("out_ddcFilteredMag", 828#64)
         , ("out_carrierFreqKhz", 7074#64)
         , ("out_demodFt8SymbolStream", 8050#64)
         , ("out_rxSensitivityMarginDb", 2410#64)
         ]) &&
       (match m.wires[2]?, m.wires[4]?, m.wires[5]? with
        | some wDdc, some wDemod, some wSens =>
          let (rDdc, _, codeDdc) := compileRtlExprToAmdGpu 1 wDdc.expr
          let (rDemod, _, codeDemod) := compileRtlExprToAmdGpu 1 wDemod.expr
          let (rSens, _, codeSens) := compileRtlExprToAmdGpu 1 wSens.expr
          let vgprsDdc :=
            runAmdGpuVop64Prog (fun _ => 100#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeDdc
          let vgprsDemod :=
            runAmdGpuVop64Prog (fun _ => 100#64) (fun _ => 68#64) (fun _ => 0#64) (fun _ => 0#64) codeDemod
          let vgprsSens :=
            runAmdGpuVop64Prog (fun _ => 100#64) (fun _ => 1410#64) (fun _ => 0#64) (fun _ => 0#64) codeSens
          vgprsDdc rDdc == 828#64 &&
          vgprsDemod rDemod == 8050#64 &&
          vgprsSens rSens == 2410#64
        | _, _, _ => false)
     | none => false) = true ∧
    (∀ (inputs wires regs : Nat → BitVec 64),
      evalAmdGpuExpr inputs wires regs sdrFt8DdcCordicGpuExpr =
        evalRtlExpr inputs wires regs sdrFt8DdcCordicGpuExpr) :=
  ⟨by decide +kernel, fun inputs wires regs => evalAmdGpuExpr_nested_sound inputs wires regs sdrFt8DdcCordicGpuExpr⟩

/-! ## 7. Cross-Package Dependency Cone Survival & Calibration Hot-Swap Guard (`sdr_ft8_crossPackage_cone_survives`) -/

def extractSdrBookMethodInner (B : Book) (m : String) : Term :=
  match lookupBookCode B m with
  | some (.lam inner) => inner
  | _ => .nat 0

def sdrDemodFt8Body : Term :=
  extractSdrBookMethodInner (emit sdrFt8TopComp) "demodFt8SymbolStream"

def sdrRxSensitivityBody : Term :=
  extractSdrBookMethodInner (emit sdrFt8TopComp) "rxSensitivityMarginDb"

/-- **Cross-Package Dependency Cone Survival (`sdr_ft8_crossPackage_cone_survives`)**:
    1. `extractReadMembers sdrDemodFt8Body = ["imageRejectionDb"]` and
       `extractReadMembers sdrRxSensitivityBody = ["friisNoiseFactorMilli"]`.
    2. By `extractReadMembers_mutation_invariant`, mutating any disjoint member (such as
       `"carrierFreqKhz"` or `"ddcFilteredMag"`) leaves `substMemberEnv` of both
       `sdrDemodFt8Body` and `sdrRxSensitivityBody` identically unchanged. -/
theorem sdr_ft8_crossPackage_cone_survives
    (env : String → Option Term) (newVal : Option Term) :
    extractReadMembers sdrDemodFt8Body = ["imageRejectionDb"] ∧
    extractReadMembers sdrRxSensitivityBody = ["friisNoiseFactorMilli"] ∧
    substMemberEnv (mutateMemberEnv env "carrierFreqKhz" newVal) sdrDemodFt8Body =
      substMemberEnv env sdrDemodFt8Body ∧
    substMemberEnv (mutateMemberEnv env "ddcFilteredMag" newVal) sdrRxSensitivityBody =
      substMemberEnv env sdrRxSensitivityBody :=
  ⟨ by decide +kernel
  , by decide +kernel
  , (extractReadMembers_mutation_invariant sdrDemodFt8Body env newVal (by decide +kernel)).1
  , (extractReadMembers_mutation_invariant sdrRxSensitivityBody env newVal (by decide +kernel)).1 ⟩

end Obend.Apps.SdrFt8
end
