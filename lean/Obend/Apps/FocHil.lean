module

public import Lean
public import Obend.Spec.FrontEnd
public import Obend.Spec.Capture
public import Obend.Spec.Sha256
public import Obend.Logic.Program
public import Obend.Logic.Obligation
public import Obend.Leaf.Emit
public import Obend.Leaf.Specialize
public import Obend.Leaf.Futamura
public import Obend.Lower.Proofs.SelfAccelerate
public import Obend.Hardware.HDL
public import Obend.Hardware.Compiler
public import Obend.Hardware.Synth
public import Obend.Hardware.PowerElectronics
public import Obend.Hardware.DigitalTwin
public import Obend.Analysis.SosLyapunov
public import Obend.Analysis.EqSatHypergraph
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
# Obend.Apps.FocHil — Flagship App #2: Closed-Loop 20 kHz FOC Motor Drive & 6-Level SiC FCML HIL

Formalizes and verifies **Flagship Application #2** (`apps/foc-hil/`) from
`QUALIFICATION-AND-SILICON-LEAN.md` §4:

1. **Multi-Layer `.obend` Motor-Control & Power-Electronics Stack (`#import_obend`)**:
   Elaborates all four `.obend` modules in `apps/foc-hil/` at Lean compile time:
   - `apps/foc-hil/ClarkePark.obend` (`FocClarkePark`)
   - `apps/foc-hil/PiCurrentLoop.obend` (`FocPiCurrentLoop`)
   - `apps/foc-hil/SicFcmlInverterLeg.obend` (`FocSicFcmlLeg`)
   - `apps/foc-hil/FocDriveTop.obend` (`FocDriveTop`)
   including transitive multi-file `import ./....obend as ...` closure resolution,
   `FrontEnd.accept`, open-recursive `Composition` extraction, `Leaf.Book` emission, and
   machine-checked `obligationMeaningWithJudges` proofs for all 6 open-recursive `.obend` claims.

2. **Closed-Loop 20 kHz Sampled-Data ISS Contraction, Thermal/Current CBF & Coupled Adjoint**:
   Connects the elaborated `.obend` FOC + 6-level SiC FCML controller to:
   - `Obend.Hardware.DigitalTwin.sampled_data_current_loop_iss_contraction`
   - `Obend.Hardware.DigitalTwin.sampled_data_closed_loop_powertrain_safety_invariant`
   - `Obend.Hardware.PowerElectronics.fcml_active_balancing_lyapunov_contraction`
   - `Obend.Analysis.statorCoupledLoss_adjoint_eqSat_sound`
   - `Obend.Analysis.sos_lyapunov_cbf_dae_showcase_sound` (`"sos-lyapunov-cbf@1"`)
   in the master theorem `foc_hil_closed_loop_iss_and_thermal_safe`.

3. **In-Core Futamura 2nd Projection (`foc_hil_inCore_futamura2`)**:
   Proves that `inCoreBookCompiler` and `futamura2BookCompiler` specialize the FOC + FCML
   `.obend` compositions inside Core4 (`inCoreBookCompiler_specializes_from_pinsOnly`,
   `futamura2BookCompiler_specializes_in_core`, `futamura2_compiler_generator_commutes`).

4. **Sequential `always_ff` Hardware Synthesis, Live Mid-Run ICAP DPR Hot-Swap & 64-Bit AMD `VOP64` GPU**:
   Synthesizes the `.obend` `Book`s and sequential `always_ff` FOC + FCML controller
   (`int_d`, `int_q`, `fcml_cap_err`, `thermal_trip_latch`, `skid_vq_hold`) to verified
   `RtlModule`s, FPGA `BelNetlist`s, SystemVerilog, and 64-bit AMD `VOP64` GPU kernels,
   and proves cross-package dependency cone survival (`foc_hil_crossPackage_dpr_hotswap_and_cone_survives`).
-/

@[expose] public section

namespace Obend.Apps.FocHil

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Synth
open Obend.Hardware.Accelerators
open Obend.Hardware.PowerElectronics
open Obend.Hardware.DigitalTwin
open Obend.Hardware.Analog
open Obend.Hardware.Magnetics
open Obend.Hardware.OpenHypergraph
open Obend.Analysis

set_option autoImplicit false

/-! ## 1. Module-Compatible Multi-File `#import_obend` Elaborator -/

def mkFocByteArrayOfNatList (xs : List Nat) : ByteArray :=
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
  meta partial def quoteFocTermAux : Term → TSyntax `term
    | .hole n σ =>
      let sArr := (σ.map quoteFocTermAux).toArray
      Lean.Unhygienic.run `(Term.hole $(quote n) [ $[$sArr],* ])
    | .bound i => Lean.Unhygienic.run `(Term.bound $(quote i))
    | .lam b => Lean.Unhygienic.run `(Term.lam $(quoteFocTermAux b))
    | .app f a => Lean.Unhygienic.run `(Term.app $(quoteFocTermAux f) $(quoteFocTermAux a))
    | .mix l u => Lean.Unhygienic.run `(Term.mix $(quoteFocTermAux l) $(quoteFocTermAux u))
    | .fix s i => Lean.Unhygienic.run `(Term.fix $(quoteFocTermAux s) $(quoteFocTermAux i))
    | .specification m e => Lean.Unhygienic.run `(Term.specification $(quoteFocTermAux m) $(quoteFocTermAux e))
    | .prototype s g => Lean.Unhygienic.run `(Term.prototype $(quoteFocTermAux s) $(quoteFocTermAux g))
    | .reflect p => Lean.Unhygienic.run `(Term.reflect $(quoteFocTermAux p))
    | .metadata p => Lean.Unhygienic.run `(Term.metadata $(quoteFocTermAux p))
    | .project p => Lean.Unhygienic.run `(Term.project $(quoteFocTermAux p))
    | .nat n => Lean.Unhygienic.run `(Term.nat $(quote n))
    | .boolean b => Lean.Unhygienic.run `(Term.boolean $(quote b))
    | .label l => Lean.Unhygienic.run `(Term.label $(quote l))
    | .binary op l r => Lean.Unhygienic.run `(Term.binary $(quote op) $(quoteFocTermAux l) $(quoteFocTermAux r))
    | .extend i fs =>
      let qfs := (fs.map quoteFocFieldAux).toArray
      Lean.Unhygienic.run `(Term.extend $(quoteFocTermAux i) [ $[$qfs],* ])
    | .record fs =>
      let qfs := (fs.map quoteFocFieldAux).toArray
      Lean.Unhygienic.run `(Term.record [ $[$qfs],* ])
    | .get g p => Lean.Unhygienic.run `(Term.get $(quoteFocTermAux g) $(quote p))
    | .ifZero v z s => Lean.Unhygienic.run `(Term.ifZero $(quoteFocTermAux v) $(quoteFocTermAux z) $(quoteFocTermAux s))
    | .inject l p => Lean.Unhygienic.run `(Term.inject $(quote l) $(quoteFocTermAux p))
    | .case sc arms =>
      let qarms := (arms.map quoteFocFieldAux).toArray
      Lean.Unhygienic.run `(Term.case $(quoteFocTermAux sc) [ $[$qarms],* ])
    | .ifBool c x y => Lean.Unhygienic.run `(Term.ifBool $(quoteFocTermAux c) $(quoteFocTermAux x) $(quoteFocTermAux y))
    | .perform p => Lean.Unhygienic.run `(Term.perform $(quoteFocTermAux p))
    | .done v => Lean.Unhygienic.run `(Term.done $(quoteFocTermAux v))
    | .split t names f =>
      Lean.Unhygienic.run `(Term.split $(quoteFocTermAux t) $(quote names) $(quoteFocTermAux f))

  meta partial def quoteFocFieldAux (kv : String × Term) : TSyntax `term :=
    Lean.Unhygienic.run `(($(quote kv.1), $(quoteFocTermAux kv.2)))
end

meta instance : Quote Term where
  quote := quoteFocTermAux

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

meta partial def quoteFocRStepAux : RStep → TSyntax `term
  | .run n => Lean.Unhygienic.run `(RStep.run $(quote n))
  | .lateBinding m L => Lean.Unhygienic.run `(RStep.lateBinding $(quote m) $(quote L))
  | .assoc d => Lean.Unhygienic.run `(RStep.assoc $(quote d))
  | .composeAssoc d => Lean.Unhygienic.run `(RStep.composeAssoc $(quote d))
  | .congr ctx focus sub =>
    let qsub := (sub.map quoteFocRStepAux).toArray
    Lean.Unhygienic.run `(RStep.congr $(quote ctx) $(quote focus) [ $[$qsub],* ])
  | .trans f s =>
    let qf := (f.map quoteFocRStepAux).toArray
    let qs := (s.map quoteFocRStepAux).toArray
    Lean.Unhygienic.run `(RStep.trans [ $[$qf],* ] [ $[$qs],* ])

meta instance : Quote RStep where
  quote := quoteFocRStepAux

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
      Lean.Unhygienic.run `(Justification.byLoweredLean $(quote lowered) $(quote sups) (mkFocByteArrayOfNatList $(quote (receipt.toList.map UInt8.toNat))))
    | .byExternalJudge fmt bs =>
      Lean.Unhygienic.run `(Justification.byExternalJudge $(quote fmt) (mkFocByteArrayOfNatList $(quote (bs.toList.map UInt8.toNat))))
    | .byEval rows => Lean.Unhygienic.run `(Justification.byEval $(quote rows))

meta def defaultFocLimits : Json :=
  Json.mkObj [
    ("heap", toJson "100000"),
    ("stack", toJson "100000"),
    ("ticks", toJson "100000"),
    ("checkWork", toJson "65536")
  ]

meta def normalizeFocSource (src : String) : String :=
  let s := src.replace "\r\n" "\n"
  if s.endsWith "\n" then s else s ++ "\n"

meta def sanitizeFocModName (stem : String) : String :=
  let chars := stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  match chars with
  | [] => "Main"
  | c :: _ =>
    let s := String.ofList (if c.isAlpha || c == '_' then chars else '_' :: chars)
    if Obend.Spec.Parse.isIdent s.toList then s else "Main"

meta def stripFocImportQuotes (raw : String) : String :=
  let s := raw.trimAscii.toString
  if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
    ((s.drop 1).dropEnd 1).toString
  else
    s

meta def resolveFocObendPath (path : System.FilePath) : IO System.FilePath := do
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

meta def resolveImportedFocObendPath (parentFile : System.FilePath) (rawImportPath : String) :
    IO System.FilePath := do
  let clean := stripFocImportQuotes rawImportPath
  let rel1 := match parentFile.parent with
    | some dir => dir / clean
    | none => System.FilePath.mk clean
  let r1 ← resolveFocObendPath rel1
  if ← r1.pathExists then return r1
  let stripped := if clean.startsWith "./" then (clean.drop 2).toString else clean
  let rel2 := match parentFile.parent with
    | some dir => dir / stripped
    | none => System.FilePath.mk stripped
  let r2 ← resolveFocObendPath rel2
  if ← r2.pathExists then return r2
  let r3 ← resolveFocObendPath (System.FilePath.mk stripped)
  if ← r3.pathExists then return r3
  let fileName := (System.FilePath.mk stripped).fileName.getD stripped
  for sub in ["apps/foc-hil/", "stdlib/physical/", "stdlib/core/"] do
    let cand ← resolveFocObendPath (System.FilePath.mk (sub ++ fileName))
    if ← cand.pathExists then return cand
  return r1

meta def parseAndCheckFocObendModule (src : String) (moduleName : String)
    (prior : List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)) :
    Except String (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) := do
  let normSrc := normalizeFocSource src
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
    let cleanPath := stripFocImportQuotes edgePath
    let stemMod := sanitizeFocModName ((System.FilePath.mk cleanPath).fileStem.getD edgeAlias)
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

meta def loadFocObendModuleClosure :
    Nat → System.FilePath →
    List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) →
    IO (Except String (List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)))
  | 0, path, _ => return .error s!"import depth limit exceeded while loading {path}"
  | fuel + 1, path, acc => do
    let resolved ← resolveFocObendPath path
    let modName := sanitizeFocModName (resolved.fileStem.getD "Main")
    if acc.any (fun (sm, _) => sm.name == modName) then
      return .ok acc
    match ← (IO.FS.readBinFile resolved).toBaseIO with
    | .error e => return .error (toString e)
    | .ok bytes =>
      let some rawSrc := Obend.Spec.Parse.decodeSource bytes
        | return .error s!"{resolved}: invalid UTF-8"
      let normSrc := normalizeFocSource rawSrc
      let ast ← match Obend.Spec.FrontEnd.parseSource modName normSrc with
        | .ok a => pure a
        | .error d => return .error s!"{d.stage}: {d.message}"
      let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
      let mut curAcc := acc
      for edge in parsedEdges.toList do
        let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
        let impFile ← resolveImportedFocObendPath resolved edgePath
        match ← loadFocObendModuleClosure fuel impFile curAcc with
        | .error err => return .error err
        | .ok nextAcc => curAcc := nextAcc
      match parseAndCheckFocObendModule normSrc modName curAcc with
      | .error err => return .error err
      | .ok pair => return .ok (curAcc ++ [pair])

meta def resolveFocKnotTerm (root : Term) (rawFields : List (String × Term)) (visiting : List String) :
    Nat → Term → Term
  | 0, t => t
  | fuel + 1, .get target name =>
    if Obend.Law.termEq target root then
      if visiting.contains name then .get root name
      else
        match rawFields.lookup name with
        | some rawBody =>
          let opened := Obend.Logic.openTerm rawBody root (.record [])
          resolveFocKnotTerm root rawFields (name :: visiting) fuel opened
        | none => .get root name
    else
      .get (resolveFocKnotTerm root rawFields visiting fuel target) name
  | fuel + 1, .lam b => .lam (resolveFocKnotTerm root rawFields visiting fuel b)
  | fuel + 1, .app f a =>
    .app (resolveFocKnotTerm root rawFields visiting fuel f) (resolveFocKnotTerm root rawFields visiting fuel a)
  | fuel + 1, .mix l u =>
    .mix (resolveFocKnotTerm root rawFields visiting fuel l) (resolveFocKnotTerm root rawFields visiting fuel u)
  | fuel + 1, .fix s i =>
    .fix (resolveFocKnotTerm root rawFields visiting fuel s) (resolveFocKnotTerm root rawFields visiting fuel i)
  | fuel + 1, .specification m e =>
    .specification (resolveFocKnotTerm root rawFields visiting fuel m) (resolveFocKnotTerm root rawFields visiting fuel e)
  | fuel + 1, .prototype s g =>
    .prototype (resolveFocKnotTerm root rawFields visiting fuel s) (resolveFocKnotTerm root rawFields visiting fuel g)
  | fuel + 1, .reflect p => .reflect (resolveFocKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .metadata p => .metadata (resolveFocKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .project p => .project (resolveFocKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .binary op l r =>
    .binary op (resolveFocKnotTerm root rawFields visiting fuel l) (resolveFocKnotTerm root rawFields visiting fuel r)
  | fuel + 1, .extend i fs =>
    .extend (resolveFocKnotTerm root rawFields visiting fuel i)
      (fs.map fun (k, v) => (k, resolveFocKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .record fs =>
    .record (fs.map fun (k, v) => (k, resolveFocKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifZero v z s =>
    .ifZero (resolveFocKnotTerm root rawFields visiting fuel v)
      (resolveFocKnotTerm root rawFields visiting fuel z)
      (resolveFocKnotTerm root rawFields visiting fuel s)
  | fuel + 1, .inject l p => .inject l (resolveFocKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .case sc arms =>
    .case (resolveFocKnotTerm root rawFields visiting fuel sc)
      (arms.map fun (k, v) => (k, resolveFocKnotTerm root rawFields visiting fuel v))
  | fuel + 1, .ifBool c x y =>
    .ifBool (resolveFocKnotTerm root rawFields visiting fuel c)
      (resolveFocKnotTerm root rawFields visiting fuel x)
      (resolveFocKnotTerm root rawFields visiting fuel y)
  | fuel + 1, .perform p => .perform (resolveFocKnotTerm root rawFields visiting fuel p)
  | fuel + 1, .done v => .done (resolveFocKnotTerm root rawFields visiting fuel v)
  | fuel + 1, .split t names f =>
    .split (resolveFocKnotTerm root rawFields visiting fuel t) names
      (resolveFocKnotTerm root rawFields visiting fuel f)
  | _ + 1, t => t

meta def decodeFocWithSeed (want : Composition → Bool) : Term → Option Composition
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

meta def findFocObject (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match decodeFocWithSeed want t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (findFocObject want fuel)

meta def findFocSelfGetCtx (selfIdx : Nat) : Term → Option (Term × String)
  | .get (.bound i) m =>
    if i == selfIdx then some (.bound 0, m) else none
  | .app f a =>
    match findFocSelfGetCtx selfIdx f with
    | some (ctxF, m) => some (.app ctxF (a.rename Nat.succ), m)
    | none =>
      (findFocSelfGetCtx selfIdx a).map fun (ctxA, m) => (.app (f.rename Nat.succ) ctxA, m)
  | .binary op l r =>
    match findFocSelfGetCtx selfIdx l with
    | some (ctxL, m) => some (.binary op ctxL (r.rename Nat.succ), m)
    | none =>
      (findFocSelfGetCtx selfIdx r).map fun (ctxR, m) => (.binary op (l.rename Nat.succ) ctxR, m)
  | _ => none

meta def deriveFocClaim (o : ClaimObj) (r : Term) : Nat → Term → List RStep → Option (List RStep)
  | 0, _, _ => none
  | fuel + 1, t, acc =>
    if Obend.Law.termEq t r then some acc.reverse
    else match Obend.Law.step? t with
    | some t' => deriveFocClaim o r fuel t' (Obend.Logic.Program.pushRun acc)
    | none =>
      match findFocSelfGetCtx o.self t with
      | some (ctx, m) =>
        match Obend.Logic.symUnfold o.comp o.self m with
        | some (L, _) =>
          let step : RStep :=
            if Obend.Law.termEq ctx (.bound 0) then .lateBinding m L
            else .congr ctx (.get (.bound o.self) m) [.lateBinding m L]
          match Obend.Logic.apply (Obend.Logic.claimResolver o.comp o.self) step t with
          | .ok t' => deriveFocClaim o r fuel t' (step :: acc)
          | .error _ => none
        | none => none
      | none => none

meta def proposeFocDerivation (o : ClaimObj) : Option (List RStep) :=
  match Obend.Logic.Program.proposeDerivation o with
  | some steps => some steps
  | none =>
    match o.sides with
    | some (_, l, r) => deriveFocClaim o r 4096 l []
    | none => none

meta structure FocElaboratedDef where
  name         : String
  composition? : Option Composition
  book?        : Option Book

meta structure FocElaboratedClaim where
  name     : String
  claimObj : ClaimObj
  just?    : Option Justification
  verified : Bool

meta structure FocElaboratedModule where
  moduleName : String
  defs       : List FocElaboratedDef
  claims     : List FocElaboratedClaim

meta def compactFocLayerForKernel (L : Layer) : Layer :=
  { L with
    metadata := .record [("name", .label L.name)]
    fields := L.fields.filter (fun kv => kv.1 != "#kind")
    composeMeta := .record [] }

meta def compactFocCompositionForKernel (C : Composition) : Composition :=
  { C with
    top := compactFocLayerForKernel C.top
    below := C.below.map compactFocLayerForKernel
    seed := C.seed.filter (fun kv => kv.1 != "#kind") }

meta def elaborateFocObendFile (pathStr : String) : IO (Except String FocElaboratedModule) := do
  let closure ← match ← loadFocObendModuleClosure 32 (System.FilePath.mk pathStr) [] with
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
      (Json.arr #[]) (Json.arr #[]) defaultFocLimits "definition" [] with
  | .error d => return .error s!"{d.stage}: {d.message}"
  | .ok lowering =>
    match Obend.Spec.FrontEnd.accept lowering with
    | .error d => return .error s!"{d.stage}: {d.message}"
    | .ok acc =>
      let erasedTerm := acc.erased
      let rootTerm := (Obend.Logic.Program.knotOf erasedTerm).getD erasedTerm
      let rawFields := Obend.Logic.Program.knotFields rootTerm
      let mut pdefs : List FocElaboratedDef := []
      for d in callables do
        let shortName := d.name
        let fullKey := modName ++ "." ++ shortName
        let knotTerm : Term := .get rootTerm fullKey
        let opened := match rawFields.lookup fullKey with
          | some rb => Obend.Logic.openTerm rb rootTerm (.record [])
          | none => knotTerm
        let wantNamed : Composition → Bool := fun C => C.top.name != ""
        let rawComp? :=
          match findFocObject wantNamed 64 knotTerm with
          | some c => some c
          | none =>
            match findFocObject wantNamed 64 (.app knotTerm (.record [])) with
            | some c => some c
            | none =>
              let inlined := resolveFocKnotTerm rootTerm rawFields [fullKey] 4 opened
              decodeFocWithSeed wantNamed inlined
        let foundComp? := rawComp?.map compactFocCompositionForKernel
        let book? := foundComp?.map Obend.Leaf.emit
        pdefs := pdefs ++ [{
          name := shortName
          composition? := foundComp?
          book? := book?
        }]
      let rawClaimPairs := Obend.Logic.Program.claimFields rootTerm
      let mut pclaims : List FocElaboratedClaim := []
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
              let steps? := proposeFocDerivation co
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

theorem focObligationMeaning_of_check_beq
    (formats : List Judge.Format) {k : Nat} {o : ClaimObj} {j : Justification}
    (h : (Obend.Logic.obligationCheckWithJudges formats k o j == .ok) = true) :
    Obend.Logic.obligationMeaningWithJudges formats o j :=
  Obend.Logic.obligationWithJudges_sound formats (beq_iff_eq.1 h)

local elab "#import_obend " pathLit:str " as " nsId:ident : command => do
  let pathStr := pathLit.getString
  let res ← IO.toEIO
    (fun e => Lean.Exception.error Lean.Syntax.missing (Lean.MessageData.ofFormat (Std.Format.text (toString e))))
    (elaborateFocObendFile pathStr)
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
              focObligationMeaning_of_check_beq Obend.Logic.defaultExternalFormats (k := 64) (o := $objId) (j := $justId) (by decide +kernel)
          ))

/-! ## 2. Compile-Time Elaboration of `apps/foc-hil/*.obend` -/

#import_obend "apps/foc-hil/ClarkePark.obend" as FocClarkePark
#import_obend "apps/foc-hil/PiCurrentLoop.obend" as FocPiCurrentLoop
#import_obend "apps/foc-hil/SicFcmlInverterLeg.obend" as FocSicFcmlLeg
#import_obend "apps/foc-hil/FocDriveTop.obend" as FocDriveTop

/-- **Master `.obend` Acceptance & Open-Recursion Theorem for `apps/foc-hil/`**:
    All four `.obend` modules in `apps/foc-hil/` pass `FrontEnd.accept` at Lean compile time,
    and all six open-recursive `claim` declarations hold in `Obend.Logic.obligationMeaningWithJudges`. -/
theorem foc_hil_all_accepted_and_claims_hold :
    FocClarkePark.accepted = true ∧
    FocPiCurrentLoop.accepted = true ∧
    FocSicFcmlLeg.accepted = true ∧
    FocDriveTop.accepted = true ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      FocClarkePark.claim_direct_axis_open_recursion_obj
      FocClarkePark.claim_direct_axis_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      FocPiCurrentLoop.claim_integral_q_open_recursion_obj
      FocPiCurrentLoop.claim_integral_q_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      FocPiCurrentLoop.claim_vq_decoupling_open_recursion_obj
      FocPiCurrentLoop.claim_vq_decoupling_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      FocSicFcmlLeg.claim_lyapunov_cap_balance_open_recursion_obj
      FocSicFcmlLeg.claim_lyapunov_cap_balance_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      FocDriveTop.claim_closed_loop_vq_open_recursion_obj
      FocDriveTop.claim_closed_loop_vq_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      FocDriveTop.claim_stator_temp_open_recursion_obj
      FocDriveTop.claim_stator_temp_open_recursion_just :=
  ⟨FocClarkePark.accepted_eq,
   FocPiCurrentLoop.accepted_eq,
   FocSicFcmlLeg.accepted_eq,
   FocDriveTop.accepted_eq,
   FocClarkePark.claim_direct_axis_open_recursion_holds,
   FocPiCurrentLoop.claim_integral_q_open_recursion_holds,
   FocPiCurrentLoop.claim_vq_decoupling_open_recursion_holds,
   FocSicFcmlLeg.claim_lyapunov_cap_balance_open_recursion_holds,
   FocDriveTop.claim_closed_loop_vq_open_recursion_holds,
   FocDriveTop.claim_stator_temp_open_recursion_holds⟩

/-! ## 3. Open-Recursive Compositions, Vtable Flattening & `Leaf.Book` Soundness -/

/-- Open-recursive `Composition` for `compensatedClarkePark()` in `ClarkePark.obend`. -/
def clarkeParkComp : Composition :=
  FocClarkePark.compensatedClarkePark_comp

/-- Open-recursive `Composition` for `decoupledPiCurrentController()` in `PiCurrentLoop.obend`. -/
def piCurrentLoopComp : Composition :=
  FocPiCurrentLoop.decoupledPiCurrentController_comp

/-- Open-recursive `Composition` for `lyapunovBalancedSicFcmlLeg()` in `SicFcmlInverterLeg.obend`. -/
def sicFcmlLegComp : Composition :=
  FocSicFcmlLeg.lyapunovBalancedSicFcmlLeg_comp

/-- Nominal 20 kHz FOC `Composition` (`nominalFocDrive()`) before ICAP DPR hot-swap. -/
def nominalFocDriveComp : Composition :=
  FocDriveTop.nominalFocDrive_comp

/-- Hot-swapped high-bandwidth ICAP DPR FOC `Composition` (`icapDprHotSwappedFocDrive()`). -/
def focDriveTopComp : Composition :=
  FocDriveTop.icapDprHotSwappedFocDrive_comp

theorem clarkeParkComp_closed : clarkeParkComp.closedB = true := by decide +kernel
theorem piCurrentLoopComp_closed : piCurrentLoopComp.closedB = true := by decide +kernel
theorem sicFcmlLegComp_closed : sicFcmlLegComp.closedB = true := by decide +kernel
theorem nominalFocDriveComp_closed : nominalFocDriveComp.closedB = true := by decide +kernel
theorem focDriveTopComp_closed : focDriveTopComp.closedB = true := by decide +kernel

/-- **Vtable Flattening & Leaf Book Soundness across all 4 `apps/foc-hil/` Layers**. -/
theorem foc_hil_flatten_and_book_sound (m : String) :
    (.get clarkeParkComp.flatten m ≈b .get clarkeParkComp.object m) ∧
    (.get (emit clarkeParkComp).link m ≈b .get clarkeParkComp.object m) ∧
    (.get piCurrentLoopComp.flatten m ≈b .get piCurrentLoopComp.object m) ∧
    (.get (emit piCurrentLoopComp).link m ≈b .get piCurrentLoopComp.object m) ∧
    (.get sicFcmlLegComp.flatten m ≈b .get sicFcmlLegComp.object m) ∧
    (.get (emit sicFcmlLegComp).link m ≈b .get sicFcmlLegComp.object m) ∧
    (.get focDriveTopComp.flatten m ≈b .get focDriveTopComp.object m) ∧
    (.get (emit focDriveTopComp).link m ≈b .get focDriveTopComp.object m) :=
  ⟨flatten_sound clarkeParkComp clarkeParkComp_closed m,
   book_sound clarkeParkComp clarkeParkComp_closed m,
   flatten_sound piCurrentLoopComp piCurrentLoopComp_closed m,
   book_sound piCurrentLoopComp piCurrentLoopComp_closed m,
   flatten_sound sicFcmlLegComp sicFcmlLegComp_closed m,
   book_sound sicFcmlLegComp sicFcmlLegComp_closed m,
   flatten_sound focDriveTopComp focDriveTopComp_closed m,
   book_sound focDriveTopComp focDriveTopComp_closed m⟩

/-- **Static `super` Elimination & Slot Dependency Certificate for `FocDriveTop.obend`**. -/
theorem focDriveTop_book_shape_verified :
    let B := emit focDriveTopComp
    B.slots = [ "icapDprBandwidthGain"
              , "statorThermalResPermille"
              , "activeFcmlBalanceMv"
              , "controlFreqKhz"
              , "closedLoopVqMv"
              , "statorWindingTempC" ] ∧
    B.defs.map (fun d => (d.member, d.slot, d.kind, d.reads)) =
      [ ("icapDprBandwidthGain", 0, .cell, [])
      , ("statorThermalResPermille", 1, .cell, [])
      , ("activeFcmlBalanceMv", 2, .method, [])
      , ("controlFreqKhz", 3, .cell, [])
      , ("closedLoopVqMv", 4, .method, [0])
      , ("statorWindingTempC", 5, .method, [1])
      ] ∧
    B.closedB = true := by
  decide +kernel

/-! ## 4. In-Core Futamura 2nd Projection (`foc_hil_inCore_futamura2`) -/

/-- **In-Core Futamura 2nd Projection for `apps/foc-hil/` (`foc_hil_inCore_futamura2`)**:
    1. `inCoreBookCompiler` specializes the pins-only encoding of `FocDriveTop`, `FocPiCurrentLoop`,
       and `FocSicFcmlLeg` directly inside Core4 (`inCoreBookCompiler_specializes_from_pinsOnly`).
    2. `futamura2BookCompiler` specializes the full `Book` encoding in Core4 (`futamura2BookCompiler_specializes_in_core`). -/
theorem foc_hil_inCore_futamura2 (pins : List LeafPin) :
    let Btop := FocDriveTop.icapDprHotSwappedFocDrive_book
    let Bpi := FocPiCurrentLoop.decoupledPiCurrentController_book
    let Bfcml := FocSicFcmlLeg.lyapunovBalancedSicFcmlLeg_book
    dataPinSpecialize (.app (inCoreBookCompiler Btop) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook Btop pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler Bpi) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook Bpi pins) ∧
    dataPinSpecialize (.app (inCoreBookCompiler Bfcml) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook Bfcml pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler Btop) (encodePinsRecordForBook Btop pins)) =
      encodeBookTerm (specializeBook Btop pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler Bpi) (encodePinsRecordForBook Bpi pins)) =
      encodeBookTerm (specializeBook Bpi pins) ∧
    dataPinSpecialize (.app (futamura2BookCompiler Bfcml) (encodePinsRecordForBook Bfcml pins)) =
      encodeBookTerm (specializeBook Bfcml pins) :=
  ⟨(inCoreBookCompiler_specializes_from_pinsOnly FocDriveTop.icapDprHotSwappedFocDrive_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly FocPiCurrentLoop.decoupledPiCurrentController_book pins).1,
   (inCoreBookCompiler_specializes_from_pinsOnly FocSicFcmlLeg.lyapunovBalancedSicFcmlLeg_book pins).1,
   futamura2BookCompiler_specializes_in_core FocDriveTop.icapDprHotSwappedFocDrive_book pins,
   futamura2BookCompiler_specializes_in_core FocPiCurrentLoop.decoupledPiCurrentController_book pins,
   futamura2BookCompiler_specializes_in_core FocSicFcmlLeg.lyapunovBalancedSicFcmlLeg_book pins⟩

/-! ## 5. Closed-Loop 20 kHz Sampled-Data ISS Contraction, Thermal/Current CBF & Coupled Adjoint -/

/-- **Master Closed-Loop ISS Contraction, Thermal/Current CBF & Coupled Electro-Thermal Adjoint Theorem
    (`foc_hil_closed_loop_iss_and_thermal_safe`)**:
    1. **20 kHz Sampled-Data ISS Contraction & SAR ADC Quantization Bounds**:
       `sampled_data_current_loop_iss_contraction` proves strict homogeneous difference contraction
       $(1000 - \kappa)(i_{q,1} - i_{q,2}) < 1000 (i_{q,1} - i_{q,2})$ together with exact $1\text{-LSB}$
       SAR ADC quantization bounds.
    2. **Closed-Loop Powertrain Safety Barrier (CBF)**:
       `sampled_data_closed_loop_powertrain_safety_invariant` and
       `golden_ms350_ipm_digital_twin_trajectory_verified` prove that the coupled `MS350` FCML + `LC Drives`
       IPM trajectory stays inside the Class-H thermal limit ($122^\circ\text{C} \le 180^\circ\text{C}$),
       maintains rotor-stator air-gap clearance ($850\,\mu\text{m} \ge 500\,\mu\text{m}$), and contracts
       FCML capacitor unbalance ($100\text{ mV} \to 80\text{ mV} \to 64\text{ mV}$).
    3. **6-Level SiC FCML Active Lyapunov Capacitor Balancing**:
       `fcml_active_balancing_lyapunov_contraction` proves quadratic Lyapunov energy contraction
       $(e_k - c_k)^2 \le e_k^2$ across all damped feedback corrections.
    4. **Coupled Electro-Thermal Stator Loss Adjoint Soundness**:
       `statorCoupledLoss_adjoint_eqSat_sound` proves that E-Graph optimization reduces hardware cost
       from $96 \to 76$ while preserving exact forward peak temperature and all 4 reverse-mode adjoint
       sensitivities.
    5. **SOS Lyapunov, Control Barrier & DAE Certificate (`"sos-lyapunov-cbf@1"`)**:
       `checkSosLyapunovProblem 1 goldenSosProblem goldenSosCert = .ok`. -/
theorem foc_hil_closed_loop_iss_and_thermal_safe :
    (∀ (iqRefAmp iq1 iq2 kpPermille qDistAmp : Int) (bits vInMv vLsbMv : Nat),
      0 < kpPermille → kpPermille < 1000 → iq2 < iq1 → 0 < vLsbMv →
      stepQuantizedCurrentLoop iqRefAmp iq1 kpPermille qDistAmp -
        stepQuantizedCurrentLoop iqRefAmp iq2 kpPermille qDistAmp =
        (1000 - kpPermille) * (iq1 - iq2) ∧
      0 < (1000 - kpPermille) * (iq1 - iq2) ∧
      (1000 - kpPermille) * (iq1 - iq2) < 1000 * (iq1 - iq2) ∧
      (runSarAdcN bits 0 vInMv vLsbMv) * vLsbMv ≤ vInMv) ∧
    (∀ (spec : PowertrainPlantSpec) (st : PowertrainTwinState),
      checkPowertrainTwinSafety spec st = true →
      spec.minShaftTorqueScaled ≤ evalIpmTorqueScaled spec.motor st.idAmp st.iqAmp ∧
      st.tWindingMilliC ≤ spec.maxClassHInsulationMilliC ∧
      st.tMagnetMilliC ≤ spec.maxMagnetDemagMilliC ∧
      0 < st.hotAirGapUm ∧
      (evalActiveBalancingStep st.fcmlCapErrMv spec.activeBalGainPermille) *
        (evalActiveBalancingStep st.fcmlCapErrMv spec.activeBalGainPermille) ≤
        st.fcmlCapErrMv * st.fcmlCapErrMv) ∧
    (∀ (vErrMv corrMv : Int),
      0 ≤ corrMv * (2 * vErrMv - corrMv) →
      (vErrMv - corrMv) * (vErrMv - corrMv) ≤ vErrMv * vErrMv) ∧
    (∀ (currentA toothWidthUm channelAspect fcmlFreqKhz dOut : Int),
      let gAdj := compileGraphAdjoint statorCoupledLossHypergraph
      let gOpt := optimizeAdjointHypergraph defaultRtlCostModel statorCoupledLossHypergraph
      let env := statorCoupledLossAdjointEnv currentA toothWidthUm channelAspect fcmlFreqKhz dOut
      evalHypergraphCost defaultRtlCostModel gOpt < evalHypergraphCost defaultRtlCostModel gAdj ∧
      evalHypergraphComb gOpt env = evalHypergraphComb gAdj env) ∧
    checkPowertrainTwinSafety goldenMs350IpmPlantSpec goldenTwinState0 = true ∧
    checkSosLyapunovProblem 1 goldenSosProblem goldenSosCert = .ok := by
  refine ⟨?_, ?_, (fun vErrMv corrMv h => (fcml_active_balancing_lyapunov_contraction vErrMv corrMv h).2), ?_,
          golden_ms350_ipm_digital_twin_trajectory_verified.2.2.2.2.2.2.2.2.2.2.2.1,
          sos_lyapunov_cbf_dae_showcase_sound.2.2.2⟩
  · intro iqRefAmp iq1 iq2 kpPermille qDistAmp bits vInMv vLsbMv hKpPos hKpSub hOrder hLsbPos
    have h := sampled_data_current_loop_iss_contraction iqRefAmp iq1 iq2 kpPermille qDistAmp
      bits vInMv vLsbMv hKpPos hKpSub hOrder hLsbPos
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · intro spec st hSafe
    have h := sampled_data_closed_loop_powertrain_safety_invariant spec st hSafe
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1⟩
  · intro currentA toothWidthUm channelAspect fcmlFreqKhz dOut
    have h := statorCoupledLoss_adjoint_eqSat_sound currentA toothWidthUm channelAspect fcmlFreqKhz dOut
    exact ⟨h.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1⟩

/-! ## 6. Hardware Synthesis, Sequential `always_ff` Controller, ICAP DPR Hot-Swap & 64-Bit AMD `VOP64` GPU -/

/-- Compile all 4 `apps/foc-hil/` `.obend` `Book`s to `RtlModule`s via `compileBookToRtl`. -/
def clarkeParkRtl? : Option RtlModule :=
  compileBookToRtl "foc_clarke_park" FocClarkePark.compensatedClarkePark_book

def piCurrentLoopRtl? : Option RtlModule :=
  compileBookToRtl "foc_pi_current_loop" FocPiCurrentLoop.decoupledPiCurrentController_book

def sicFcmlLegRtl? : Option RtlModule :=
  compileBookToRtl "foc_sic_fcml_leg" FocSicFcmlLeg.lyapunovBalancedSicFcmlLeg_book

def focDriveTopRtl? : Option RtlModule :=
  compileBookToRtl "foc_drive_top_comb" FocDriveTop.icapDprHotSwappedFocDrive_book

/-- Explicit sequential `always_ff` `RtlModule` (`foc_drive_top`) implementing the 20 kHz
    FOC + 6-level SiC FCML controller with:
    - Input 0 (`id_err_ma`), Input 1 (`iq_err_ma`), Input 2 (`cap_err_mv`),
      Input 3 (`winding_temp_c`), Input 4 (`dpr_isolate_en`), Input 5 (`dpr_high_bw_sel`)
    - Reg 0 (`int_d`): stateful `always_ff` $d$-axis PI integral accumulator
    - Reg 1 (`int_q`): stateful `always_ff` $q$-axis PI integral accumulator
    - Reg 2 (`fcml_cap_err`): stateful `always_ff` active Lyapunov flying-capacitor balance state
    - Reg 3 (`thermal_trip_latch`): stateful `always_ff` write-once $155^\circ\text{C}$ over-temperature gate-kill latch
    - Reg 4 (`skid_vq_hold`): live mid-run ICAP DPR isolation skid-buffer output hold -/
def focHilSequentialRtlModule : RtlModule where
  name := "foc_drive_top"
  inputNames :=
    [ "id_err_ma"
    , "iq_err_ma"
    , "cap_err_mv"
    , "winding_temp_c"
    , "dpr_isolate_en"
    , "dpr_high_bw_sel"
    ]
  wires :=
    [ { wireIdx := 0
        name := "kp_gain"
        expr := .mux (.inputPort 5) (.const 480#64) (.const 400#64) }
    , { wireIdx := 1
        name := "vq_active_mv"
        expr := .alu .add
          (.alu .mul (.inputPort 1) (.wireRef 0))
          (.regRead 1) }
    , { wireIdx := 2
        name := "overtemp_now"
        expr := .alu .ult (.const 154#64) (.inputPort 3) }
    , { wireIdx := 3
        name := "fault_trip_comb"
        expr := .alu .bitOr (.regRead 3) (.wireRef 2) }
    ]
  regs :=
    [ { regIdx := 0
        name := "int_d"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr :=
          .mux (.inputPort 4)
            (.regRead 0)
            (.alu .add (.regRead 0)
              (.alu .mul (.inputPort 0) (.const 65#64))) }
    , { regIdx := 1
        name := "int_q"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr :=
          .mux (.inputPort 4)
            (.regRead 1)
            (.alu .add (.regRead 1)
              (.alu .mul (.inputPort 1) (.const 65#64))) }
    , { regIdx := 2
        name := "fcml_cap_err"
        domain := .coreClk
        resetKind := .syncReset 15000#64
        isSynchronizer := false
        nextExpr :=
          .mux (.inputPort 4)
            (.regRead 2)
            (.alu .mul (.inputPort 2) (.const 800#64)) }
    , { regIdx := 3
        name := "thermal_trip_latch"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr := .wireRef 3 }
    , { regIdx := 4
        name := "skid_vq_hold"
        domain := .coreClk
        resetKind := .syncReset 0#64
        isSynchronizer := false
        nextExpr :=
          .mux (.inputPort 4)
            (.regRead 4)
            (.wireRef 1) }
    ]
  outputs :=
    [ { name := "vq_cmd_mv"
        expr :=
          .mux (.inputPort 4)
            (.regRead 4)
            (.wireRef 1) }
    , { name := "vd_cmd_mv"
        expr :=
          .alu .add
            (.alu .mul (.inputPort 0) (.const 400#64))
            (.regRead 0) }
    , { name := "cap_bal_mv"
        expr := .regRead 2 }
    , { name := "fault_trip"
        expr := .wireRef 3 }
    , { name := "pwm_gate_en"
        expr := .mux (.wireRef 3) (.const 0#64) (.const 1#64) }
    ]

/-- **Hardware Well-Formedness & FPGA `BelNetlist` Synthesis Certificate for `apps/foc-hil/`**. -/
theorem foc_hil_rtl_and_bel_synthesis_verified :
    checkRtlModule focHilSequentialRtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels focHilSequentialRtlModule) = true ∧
    (match clarkeParkRtl?, piCurrentLoopRtl?, sicFcmlLegRtl?, focDriveTopRtl? with
     | some m1, some m2, some m3, some m4 =>
       checkRtlModule m1 &&
       checkRtlModule m2 &&
       checkRtlModule m3 &&
       checkRtlModule m4 &&
       checkBelNetlistValid (synthesizeModuleToBels m4)
     | _, _, _, _ => false) = true := by
  decide +kernel

/-- **Multi-Cycle Sequential `always_ff` HIL Trace Verification**:
    Verifies across a 4-tick sequence covering:
    1. Tick 0 (`focIn0`): Rated torque step ($i_q = 250\text{ A}$, $T = 85^\circ\text{C}$, nominal gain $400$).
    2. Tick 1 (`focIn1`): Live mid-run ICAP DPR isolation (`dpr_isolate_en = 1`), holding `int_q` and outputting
       the glitch-free held `skid_vq_hold` command without dropping a control tick.
    3. Tick 2 (`focIn2`): Post-DPR hot-swap release (`dpr_isolate_en = 0`, `dpr_high_bw_sel = 1`, gain $480$).
    4. Tick 3 (`focIn3`): $155^\circ\text{C}$ over-temperature injection (`winding_temp_c = 155`), triggering
       an immediate 1-cycle hardware gate-kill trip (`fault_trip = 1`, `pwm_gate_en = 0`). -/
def focInitRegs : Nat → BitVec 64
  | 2 => 15000#64
  | _ => 0#64

def focIn0 : Nat → BitVec 64
  | 0 => 100#64
  | 1 => 250#64
  | 2 => 15#64
  | 3 => 85#64
  | _ => 0#64

def focIn1 : Nat → BitVec 64
  | 0 => 100#64
  | 1 => 250#64
  | 2 => 12#64
  | 3 => 90#64
  | 4 => 1#64
  | _ => 0#64

def focIn2 : Nat → BitVec 64
  | 0 => 50#64
  | 1 => 250#64
  | 2 => 5#64
  | 3 => 110#64
  | 5 => 1#64
  | _ => 0#64

def focIn3 : Nat → BitVec 64
  | 0 => 0#64
  | 1 => 250#64
  | 2 => 0#64
  | 3 => 155#64
  | 5 => 1#64
  | _ => 0#64

theorem foc_hil_sequential_4tick_trace_verified :
    let regs1 := stepModuleRegs focHilSequentialRtlModule false focIn0 focInitRegs
    let regs2 := stepModuleRegs focHilSequentialRtlModule false focIn1 regs1
    let regs3 := stepModuleRegs focHilSequentialRtlModule false focIn2 regs2
    -- Tick 0: nominal gain 400 * 250 = 100,000 mV, fault_trip = 0, pwm_gate_en = 1
    evalModuleOutputs focHilSequentialRtlModule focIn0 focInitRegs =
      [ ("vq_cmd_mv", 100000#64)
      , ("vd_cmd_mv", 40000#64)
      , ("cap_bal_mv", 15000#64)
      , ("fault_trip", 0#64)
      , ("pwm_gate_en", 1#64) ] ∧
    -- Tick 1: ICAP DPR isolation active (`dpr_isolate_en = 1`), glitch-free held output 100,000 mV
    evalModuleOutputs focHilSequentialRtlModule focIn1 regs1 =
      [ ("vq_cmd_mv", 100000#64)
      , ("vd_cmd_mv", 46500#64)
      , ("cap_bal_mv", 12000#64)
      , ("fault_trip", 0#64)
      , ("pwm_gate_en", 1#64) ] ∧
    -- Tick 2: ICAP DPR hot-swap complete (`dpr_high_bw_sel = 1`), gain 480 * 250 + int_q(16250) = 136,250 mV
    evalModuleOutputs focHilSequentialRtlModule focIn2 regs2 =
      [ ("vq_cmd_mv", 136250#64)
      , ("vd_cmd_mv", 26500#64)
      , ("cap_bal_mv", 12000#64)
      , ("fault_trip", 0#64)
      , ("pwm_gate_en", 1#64) ] ∧
    -- Tick 3: 155°C over-temperature injection triggers 1-cycle gate-kill (`fault_trip = 1`, `pwm_gate_en = 0`)
    evalModuleOutputs focHilSequentialRtlModule focIn3 regs3 =
      [ ("vq_cmd_mv", 152500#64)
      , ("vd_cmd_mv", 9750#64)
      , ("cap_bal_mv", 4000#64)
      , ("fault_trip", 1#64)
      , ("pwm_gate_en", 0#64) ] := by
  decide +kernel

/-- **64-Bit AMD `VOP64` GPU Co-Execution Certificate for `FocDriveTop.obend`**:
    Compiles `FocDriveTop`'s `activeFcmlBalanceMv`, `closedLoopVqMv`, and `statorWindingTempC`
    hardware wires via `compileRtlExprToAmdGpu` and verifies exact 64-bit `runAmdGpuVop64Prog`
    equivalence with FPGA RTL evaluation. -/
theorem foc_hil_amdgpu_vop64_equivalence :
    (match focDriveTopRtl? with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 250#64) (fun _ => 0#64) ==
         [ ("out_icapDprBandwidthGain", 480#64)
         , ("out_statorThermalResPermille", 4#64)
         , ("out_activeFcmlBalanceMv", 5025#64)
         , ("out_controlFreqKhz", 20#64)
         , ("out_closedLoopVqMv", 120250#64)
         , ("out_statorWindingTempC", 1045#64)
         ]) &&
       (match m.wires[2]?, m.wires[4]?, m.wires[5]? with
        | some wBal, some wVq, some wTemp =>
          let (rBal, _, codeBal) := compileRtlExprToAmdGpu 1 wBal.expr
          let (rVq, _, codeVq) := compileRtlExprToAmdGpu 1 wVq.expr
          let (rTemp, _, codeTemp) := compileRtlExprToAmdGpu 1 wTemp.expr
          let vgprsBal :=
            runAmdGpuVop64Prog (fun _ => 250#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeBal
          let vgprsVq :=
            runAmdGpuVop64Prog (fun _ => 250#64) (fun _ => 480#64) (fun _ => 0#64) (fun _ => 0#64) codeVq
          let vgprsTemp :=
            runAmdGpuVop64Prog (fun _ => 250#64) (fun _ => 4#64) (fun _ => 0#64) (fun _ => 0#64) codeTemp
          vgprsBal rBal == 5025#64 &&
          vgprsVq rVq == 120250#64 &&
          vgprsTemp rTemp == 1045#64
        | _, _, _ => false)
     | none => false) = true := by
  decide +kernel

/-! ## 7. Cross-Package Dependency Cone Survival & Live ICAP DPR Hot-Swap Guard -/

/-- Extract the inner method body (under the outer `λself.` binder) from a `Leaf.Book` slot. -/
def extractFocBookMethodInner (B : Book) (m : String) : Term :=
  match lookupBookCode B m with
  | some (.lam inner) => inner
  | _ => .nat 0

def focClosedLoopVqBody : Term :=
  extractFocBookMethodInner (emit focDriveTopComp) "closedLoopVqMv"

def focStatorTempBody : Term :=
  extractFocBookMethodInner (emit focDriveTopComp) "statorWindingTempC"

/-- **Cross-Package Dependency Cone Survival & Live ICAP DPR Hot-Swap Guard
    (`foc_hil_crossPackage_dpr_hotswap_and_cone_survives`)**:
    1. `slotReadCone focDriveTopComp "closedLoopVqMv"` depends only on
       `["closedLoopVqMv", "icapDprBandwidthGain"]`, and `slotReadCone focDriveTopComp "statorWindingTempC"`
       depends only on `["statorWindingTempC", "statorThermalResPermille"]`.
    2. By `extractReadMembers_mutation_invariant`, mutating any disjoint member (such as
       `"controlFreqKhz"` or `"activeFcmlBalanceMv"`) leaves `substMemberEnv` of both
       `focClosedLoopVqBody` and `focStatorTempBody` identically unchanged. -/
theorem foc_hil_crossPackage_dpr_hotswap_and_cone_survives
    (env : String → Option Term) (newVal : Option Term) :
    extractReadMembers focClosedLoopVqBody = ["icapDprBandwidthGain"] ∧
    extractReadMembers focStatorTempBody = ["statorThermalResPermille"] ∧
    substMemberEnv (mutateMemberEnv env "controlFreqKhz" newVal) focClosedLoopVqBody =
      substMemberEnv env focClosedLoopVqBody ∧
    substMemberEnv (mutateMemberEnv env "activeFcmlBalanceMv" newVal) focStatorTempBody =
      substMemberEnv env focStatorTempBody :=
  ⟨by decide +kernel,
   by decide +kernel,
   (extractReadMembers_mutation_invariant focClosedLoopVqBody env newVal (by decide +kernel)).1,
   (extractReadMembers_mutation_invariant focStatorTempBody env newVal (by decide +kernel)).1⟩

end Obend.Apps.FocHil
end
