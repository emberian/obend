module
/-
# Obend.Hardware.UserspacePhysical — Verified `.obend` Userspace Open-Recursive Physical Standard Library Lowered Through `#import_obend` & `Obend.Leaf` Into FPGA SystemVerilog RTL & AMD `CDNA3` 64-Bit VOP64 GPU ISA

Elaborates the 4 canonical `.obend` physical standard library modules in `stdlib/physical/`
at compile time via `#import_obend` (with zero manual de Bruijn `Layer` transcription):
1. `stdlib/physical/LcDrivesStator.obend` (`PhysicalStator`: `OuterJacketStator` -> `LcDrivesInSlotUpgrade` -> `FiveAxisFinishMilled`)
2. `stdlib/physical/Ms350FcmlPhaseLeg.obend` (`Ms350PhaseLeg`: `SicBaseSwitch` -> `DeadtimeProtectionOverride`)
3. `stdlib/physical/CleanroomTcadStack.obend` (`CleanroomTcadStack`: `PlanarBulkMosfetBase` -> `HighKMetalGateFinFetUpgrade`, plus `Q3PhotonicCouplerArray`: `PlanarWaveguideBase` -> `KrawtchoukCouplingOverride`)
4. `stdlib/physical/Cnc5AxisMill.obend` (`Cnc5AxisMill`: `Uncompensated5AxisMill` -> `AbbeAndRuckigCompensatedMill`)

Connects the `#import_obend`-elaborated `Composition`s and `Book`s directly to:
- `Obend.Logic.Composition` & `Obend.Leaf.Flatten` (`flatten_sound`, `fix_mix_flatten_sound`),
- `Obend.Leaf.Emit` (`book_sound`),
- `Obend.Leaf.Futamura` (`futamura2_compiler_generator_commutes`) & `Obend.Leaf.Specialize` (`extractReadMembers_mutation_invariant`),
- `Obend.Hardware.Compiler` (`compileBookToRtl`) & `Obend.Lower.Proofs.SelfAccelerate` (64-bit `compileRtlExprToAmdGpu` + `runAmdGpuVop64Prog`).
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
public import Obend.Leaf.BendTT
public import Obend.Lower.Proofs.SelfAccelerate
public import Obend.Hardware.Kinematics
public import Obend.Hardware.OpenUSD
public import Obend.Hardware.FluidThermal
public import Obend.Hardware.GeometryCAM
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

namespace Obend.Hardware.UserspacePhysical
open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Leaf.BendTT
open Obend.Lower
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators

set_option autoImplicit false

/-! ## 0. Compile-Time `#import_obend` Elaborator for `stdlib/physical/*.obend` -/

def mkByteArrayOfNatList (xs : List Nat) : ByteArray :=
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

mutual
  meta partial def quoteTermAux : Term → TSyntax `term
    | .hole n σ =>
      let sArr := (σ.map quoteTermAux).toArray
      Lean.Unhygienic.run `(Term.hole $(quote n) [ $[$sArr],* ])
    | .bound i => Lean.Unhygienic.run `(Term.bound $(quote i))
    | .lam b => Lean.Unhygienic.run `(Term.lam $(quoteTermAux b))
    | .app f a => Lean.Unhygienic.run `(Term.app $(quoteTermAux f) $(quoteTermAux a))
    | .mix l u => Lean.Unhygienic.run `(Term.mix $(quoteTermAux l) $(quoteTermAux u))
    | .fix s i => Lean.Unhygienic.run `(Term.fix $(quoteTermAux s) $(quoteTermAux i))
    | .specification m e => Lean.Unhygienic.run `(Term.specification $(quoteTermAux m) $(quoteTermAux e))
    | .prototype s g => Lean.Unhygienic.run `(Term.prototype $(quoteTermAux s) $(quoteTermAux g))
    | .reflect p => Lean.Unhygienic.run `(Term.reflect $(quoteTermAux p))
    | .metadata p => Lean.Unhygienic.run `(Term.metadata $(quoteTermAux p))
    | .project p => Lean.Unhygienic.run `(Term.project $(quoteTermAux p))
    | .nat n => Lean.Unhygienic.run `(Term.nat $(quote n))
    | .boolean b => Lean.Unhygienic.run `(Term.boolean $(quote b))
    | .label l => Lean.Unhygienic.run `(Term.label $(quote l))
    | .binary op l r => Lean.Unhygienic.run `(Term.binary $(quote op) $(quoteTermAux l) $(quoteTermAux r))
    | .extend i fs =>
      let qfs := (fs.map quoteFieldAux).toArray
      Lean.Unhygienic.run `(Term.extend $(quoteTermAux i) [ $[$qfs],* ])
    | .record fs =>
      let qfs := (fs.map quoteFieldAux).toArray
      Lean.Unhygienic.run `(Term.record [ $[$qfs],* ])
    | .get g p => Lean.Unhygienic.run `(Term.get $(quoteTermAux g) $(quote p))
    | .ifZero v z s => Lean.Unhygienic.run `(Term.ifZero $(quoteTermAux v) $(quoteTermAux z) $(quoteTermAux s))
    | .inject l p => Lean.Unhygienic.run `(Term.inject $(quote l) $(quoteTermAux p))
    | .case sc arms =>
      let qarms := (arms.map quoteFieldAux).toArray
      Lean.Unhygienic.run `(Term.case $(quoteTermAux sc) [ $[$qarms],* ])
    | .ifBool c x y => Lean.Unhygienic.run `(Term.ifBool $(quoteTermAux c) $(quoteTermAux x) $(quoteTermAux y))
    | .perform p => Lean.Unhygienic.run `(Term.perform $(quoteTermAux p))
    | .done v => Lean.Unhygienic.run `(Term.done $(quoteTermAux v))
    | .split t names f =>
      Lean.Unhygienic.run `(Term.split $(quoteTermAux t) $(quote names) $(quoteTermAux f))

  meta partial def quoteFieldAux (kv : String × Term) : TSyntax `term :=
    Lean.Unhygienic.run `(($(quote kv.1), $(quoteTermAux kv.2)))
end

meta instance : Quote Term where
  quote := quoteTermAux

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

meta partial def quoteRStepAux : RStep → TSyntax `term
  | .run n => Lean.Unhygienic.run `(RStep.run $(quote n))
  | .lateBinding m L => Lean.Unhygienic.run `(RStep.lateBinding $(quote m) $(quote L))
  | .assoc d => Lean.Unhygienic.run `(RStep.assoc $(quote d))
  | .composeAssoc d => Lean.Unhygienic.run `(RStep.composeAssoc $(quote d))
  | .congr ctx focus sub =>
    let qsub := (sub.map quoteRStepAux).toArray
    Lean.Unhygienic.run `(RStep.congr $(quote ctx) $(quote focus) [ $[$qsub],* ])
  | .trans f s =>
    let qf := (f.map quoteRStepAux).toArray
    let qs := (s.map quoteRStepAux).toArray
    Lean.Unhygienic.run `(RStep.trans [ $[$qf],* ] [ $[$qs],* ])

meta instance : Quote RStep where
  quote := quoteRStepAux

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
      Lean.Unhygienic.run `(Justification.byLoweredLean $(quote lowered) $(quote sups) (mkByteArrayOfNatList $(quote (receipt.toList.map UInt8.toNat))))
    | .byExternalJudge fmt bs =>
      Lean.Unhygienic.run `(Justification.byExternalJudge $(quote fmt) (mkByteArrayOfNatList $(quote (bs.toList.map UInt8.toNat))))
    | .byEval rows => Lean.Unhygienic.run `(Justification.byEval $(quote rows))

meta def defaultPhysicalLimits : Json :=
  Json.mkObj [
    ("heap", toJson "100000"),
    ("stack", toJson "100000"),
    ("ticks", toJson "100000"),
    ("checkWork", toJson "65536")
  ]

meta def resolveKnotTermPhys (root : Term) (rawFields : List (String × Term)) (visiting : List String) :
    Nat → Term → Term
  | 0, t => t
  | fuel + 1, .get target name =>
    if Obend.Law.termEq target root then
      if visiting.contains name then .get root name
      else
        match rawFields.lookup name with
        | some rawBody =>
          let opened := Obend.Logic.openTerm rawBody root (.record [])
          resolveKnotTermPhys root rawFields (name :: visiting) fuel opened
        | none => .get root name
    else
      .get (resolveKnotTermPhys root rawFields visiting fuel target) name
  | fuel + 1, .lam b => .lam (resolveKnotTermPhys root rawFields visiting fuel b)
  | fuel + 1, .app f a =>
    .app (resolveKnotTermPhys root rawFields visiting fuel f) (resolveKnotTermPhys root rawFields visiting fuel a)
  | fuel + 1, .mix l u =>
    .mix (resolveKnotTermPhys root rawFields visiting fuel l) (resolveKnotTermPhys root rawFields visiting fuel u)
  | fuel + 1, .fix s i =>
    .fix (resolveKnotTermPhys root rawFields visiting fuel s) (resolveKnotTermPhys root rawFields visiting fuel i)
  | fuel + 1, .specification m e =>
    .specification (resolveKnotTermPhys root rawFields visiting fuel m) (resolveKnotTermPhys root rawFields visiting fuel e)
  | fuel + 1, .prototype s g =>
    .prototype (resolveKnotTermPhys root rawFields visiting fuel s) (resolveKnotTermPhys root rawFields visiting fuel g)
  | fuel + 1, .reflect p => .reflect (resolveKnotTermPhys root rawFields visiting fuel p)
  | fuel + 1, .metadata p => .metadata (resolveKnotTermPhys root rawFields visiting fuel p)
  | fuel + 1, .project p => .project (resolveKnotTermPhys root rawFields visiting fuel p)
  | fuel + 1, .binary op l r =>
    .binary op (resolveKnotTermPhys root rawFields visiting fuel l) (resolveKnotTermPhys root rawFields visiting fuel r)
  | fuel + 1, .extend i fs =>
    .extend (resolveKnotTermPhys root rawFields visiting fuel i)
      (fs.map fun (k, v) => (k, resolveKnotTermPhys root rawFields visiting fuel v))
  | fuel + 1, .record fs =>
    .record (fs.map fun (k, v) => (k, resolveKnotTermPhys root rawFields visiting fuel v))
  | fuel + 1, .ifZero v z s =>
    .ifZero (resolveKnotTermPhys root rawFields visiting fuel v)
      (resolveKnotTermPhys root rawFields visiting fuel z)
      (resolveKnotTermPhys root rawFields visiting fuel s)
  | fuel + 1, .inject l p => .inject l (resolveKnotTermPhys root rawFields visiting fuel p)
  | fuel + 1, .case sc arms =>
    .case (resolveKnotTermPhys root rawFields visiting fuel sc)
      (arms.map fun (k, v) => (k, resolveKnotTermPhys root rawFields visiting fuel v))
  | fuel + 1, .ifBool c x y =>
    .ifBool (resolveKnotTermPhys root rawFields visiting fuel c)
      (resolveKnotTermPhys root rawFields visiting fuel x)
      (resolveKnotTermPhys root rawFields visiting fuel y)
  | fuel + 1, .perform p => .perform (resolveKnotTermPhys root rawFields visiting fuel p)
  | fuel + 1, .done v => .done (resolveKnotTermPhys root rawFields visiting fuel v)
  | fuel + 1, .split t names f =>
    .split (resolveKnotTermPhys root rawFields visiting fuel t) names
      (resolveKnotTermPhys root rawFields visiting fuel f)
  | _ + 1, t => t

meta def decodeWorkbookWithSeedPhys (want : Composition → Bool) : Term → Option Composition
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

meta def findWorkbookObjectPhys (want : Composition → Bool) : Nat → Term → Option Composition
  | 0, _ => none
  | fuel + 1, t =>
    match decodeWorkbookWithSeedPhys want t with
    | some C => some C
    | none => (Obend.Law.step? t).bind (findWorkbookObjectPhys want fuel)

meta def findSelfGetCtxPhys (selfIdx : Nat) : Term → Option (Term × String)
  | .get (.bound i) m =>
    if i == selfIdx then some (.bound 0, m) else none
  | .app f a =>
    match findSelfGetCtxPhys selfIdx f with
    | some (ctxF, m) => some (.app ctxF (a.rename Nat.succ), m)
    | none =>
      (findSelfGetCtxPhys selfIdx a).map fun (ctxA, m) => (.app (f.rename Nat.succ) ctxA, m)
  | .binary op l r =>
    match findSelfGetCtxPhys selfIdx l with
    | some (ctxL, m) => some (.binary op ctxL (r.rename Nat.succ), m)
    | none =>
      (findSelfGetCtxPhys selfIdx r).map fun (ctxR, m) => (.binary op (l.rename Nat.succ) ctxR, m)
  | _ => none

meta def deriveWorkbookPhys (o : ClaimObj) (r : Term) : Nat → Term → List RStep → Option (List RStep)
  | 0, _, _ => none
  | fuel + 1, t, acc =>
    if Obend.Law.termEq t r then some acc.reverse
    else match Obend.Law.step? t with
    | some t' => deriveWorkbookPhys o r fuel t' (Obend.Logic.Program.pushRun acc)
    | none =>
      match findSelfGetCtxPhys o.self t with
      | some (ctx, m) =>
        match Obend.Logic.symUnfold o.comp o.self m with
        | some (L, _) =>
          let step : RStep :=
            if Obend.Law.termEq ctx (.bound 0) then .lateBinding m L
            else .congr ctx (.get (.bound o.self) m) [.lateBinding m L]
          match Obend.Logic.apply (Obend.Logic.claimResolver o.comp o.self) step t with
          | .ok t' => deriveWorkbookPhys o r fuel t' (step :: acc)
          | .error _ => none
        | none => none
      | none => none

meta def proposeWorkbookDerivationPhys (o : ClaimObj) : Option (List RStep) :=
  match Obend.Logic.Program.proposeDerivation o with
  | some steps => some steps
  | none =>
    match o.sides with
    | some (_, l, r) => deriveWorkbookPhys o r 4096 l []
    | none => none

meta def resolvePhysicalObendPath (path : System.FilePath) : IO System.FilePath := do
  if ← path.pathExists then
    return path
  let s := path.toString
  let parentPath := System.FilePath.mk ("../" ++ s)
  if ← parentPath.pathExists then
    return parentPath
  if s.startsWith "lean/" then
    let stripped := System.FilePath.mk (s.drop 5).toString
    if ← stripped.pathExists then
      return stripped
  let prefixed := System.FilePath.mk ("lean/" ++ s)
  if ← prefixed.pathExists then
    return prefixed
  return path

meta structure PhysicalElaboratedDef where
  name         : String
  composition? : Option Composition
  book?        : Option Book

meta structure PhysicalElaboratedClaim where
  name     : String
  claimObj : ClaimObj
  just?    : Option Justification
  verified : Bool

meta structure PhysicalElaboratedModule where
  moduleName : String
  defs       : List PhysicalElaboratedDef
  claims     : List PhysicalElaboratedClaim

meta def compactLayerForKernel (L : Layer) : Layer :=
  { L with
    metadata := .record [("name", .label L.name)]
    fields := L.fields.filter (fun kv => kv.1 != "#kind")
    composeMeta := .record [] }

meta def compactCompositionForKernel (C : Composition) : Composition :=
  { C with
    top := compactLayerForKernel C.top
    below := C.below.map compactLayerForKernel
    seed := C.seed.filter (fun kv => kv.1 != "#kind") }

meta def elaboratePhysicalObendFile (pathStr : String) : IO (Except String PhysicalElaboratedModule) := do
  let resolved ← resolvePhysicalObendPath (System.FilePath.mk pathStr)
  let modName := resolved.fileStem.getD "Main"
  match ← (IO.FS.readBinFile resolved).toBaseIO with
  | .error e => return .error (toString e)
  | .ok bytes =>
    let capRes ← (Obend.Spec.Capture.captureModule #[] modName bytes none [] false).run
    match capRes with
    | .error d => return .error s!"{d.stage}: {d.message}"
    | .ok (srcMod, _) =>
      let ast ← match Obend.Spec.FrontEnd.parseSource modName srcMod.source with
        | .ok a => pure a
        | .error d => return .error s!"{d.stage}: {d.message}"
      let decodedMod ← match Obend.Spec.FrontEnd.checkParsed srcMod ast with
        | .ok m => pure m
        | .error d => return .error s!"{d.stage}: {d.message}"
      let callables := decodedMod.decls.filter fun (d : Obend.Spec.Syntax.Decl) =>
        match d with
        | .function .. | .extension .. | .spec .. => true
        | _ => false
      let some (lastDecl : Obend.Spec.Syntax.Decl) := callables.getLast?
        | return .error s!"module {modName} contains no callable declarations"
      let entryDef := lastDecl.name
      match Obend.Spec.FrontEnd.lowerDecoded [srcMod] [decodedMod] 0 entryDef
          (Json.arr #[]) (Json.arr #[]) defaultPhysicalLimits "definition" [] with
      | .error d => return .error s!"{d.stage}: {d.message}"
      | .ok lowering =>
        match Obend.Spec.FrontEnd.accept lowering with
        | .error d => return .error s!"{d.stage}: {d.message}"
        | .ok acc =>
          let erasedTerm := acc.erased
          let rootTerm := (Obend.Logic.Program.knotOf erasedTerm).getD erasedTerm
          let rawFields := Obend.Logic.Program.knotFields rootTerm
          let mut pdefs : List PhysicalElaboratedDef := []
          for d in callables do
            let shortName := d.name
            let fullKey := modName ++ "." ++ shortName
            let knotTerm : Term := .get rootTerm fullKey
            let opened := match rawFields.lookup fullKey with
              | some rb => Obend.Logic.openTerm rb rootTerm (.record [])
              | none => knotTerm
            let wantNamed : Composition → Bool := fun C => C.top.name != ""
            let rawComp? :=
              match findWorkbookObjectPhys wantNamed 64 knotTerm with
              | some c => some c
              | none =>
                match findWorkbookObjectPhys wantNamed 64 (.app knotTerm (.record [])) with
                | some c => some c
                | none =>
                  let inlined := resolveKnotTermPhys rootTerm rawFields [fullKey] 4 opened
                  decodeWorkbookWithSeedPhys wantNamed inlined
            let foundComp? := rawComp?.map compactCompositionForKernel
            let book? := foundComp?.map Obend.Leaf.emit
            pdefs := pdefs ++ [{
              name := shortName
              composition? := foundComp?
              book? := book?
            }]
          let rawClaimPairs := Obend.Logic.Program.claimFields rootTerm
          let mut pclaims : List PhysicalElaboratedClaim := []
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
                  let steps? := proposeWorkbookDerivationPhys co
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

theorem obligationMeaning_of_check_beq
    (formats : List Judge.Format) {k : Nat} {o : ClaimObj} {j : Justification}
    (h : (Obend.Logic.obligationCheckWithJudges formats k o j == .ok) = true) :
    Obend.Logic.obligationMeaningWithJudges formats o j :=
  Obend.Logic.obligationWithJudges_sound formats (beq_iff_eq.1 h)

/-- Compile-time `.obend` physical library elaborator `#import_obend "stdlib/physical/..." as Ns`.
    Parses, typechecks, lowers (`FrontEnd.lowerDecoded`), verifies `FrontEnd.accept`, extracts all
    open-recursive `Composition`s and `Leaf.Book`s, and emits kernel-checked `@[expose] public def`
    and `public theorem` declarations into namespace `Ns`. -/
local elab "#import_obend " pathLit:str " as " nsId:ident : command => do
  let pathStr := pathLit.getString
  let res ← IO.toEIO
    (fun e => Lean.Exception.error Lean.Syntax.missing (Lean.MessageData.ofFormat (Std.Format.text (toString e))))
    (elaboratePhysicalObendFile pathStr)
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
              obligationMeaning_of_check_beq Obend.Logic.defaultExternalFormats (k := 64) (o := $objId) (j := $justId) (by decide +kernel)
          ))

/-! ## 1. Compile-Time Elaboration of the 4 Canonical `stdlib/physical/*.obend` Modules via `#import_obend` -/

#import_obend "stdlib/physical/LcDrivesStator.obend" as StdLcDrivesStator
#import_obend "stdlib/physical/Ms350FcmlPhaseLeg.obend" as StdMs350FcmlPhaseLeg
#import_obend "stdlib/physical/CleanroomTcadStack.obend" as StdCleanroomTcadStack
#import_obend "stdlib/physical/Cnc5AxisMill.obend" as StdCnc5AxisMill

/-- All 4 `stdlib/physical/*.obend` modules pass `FrontEnd.accept` and discharge their open-recursion claims! -/
theorem stdlib_physical_all_accepted_and_claims_hold :
    StdLcDrivesStator.accepted = true ∧
    StdMs350FcmlPhaseLeg.accepted = true ∧
    StdCleanroomTcadStack.accepted = true ∧
    StdCnc5AxisMill.accepted = true ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      StdLcDrivesStator.claim_peak_temp_open_recursion_obj
      StdLcDrivesStator.claim_peak_temp_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      StdMs350FcmlPhaseLeg.claim_switching_loss_open_recursion_obj
      StdMs350FcmlPhaseLeg.claim_switching_loss_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      StdCleanroomTcadStack.claim_drain_current_open_recursion_obj
      StdCleanroomTcadStack.claim_drain_current_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      StdCleanroomTcadStack.claim_transferred_power_open_recursion_obj
      StdCleanroomTcadStack.claim_transferred_power_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      StdCnc5AxisMill.claim_volumetric_decomposition_obj
      StdCnc5AxisMill.claim_volumetric_decomposition_just :=
  ⟨StdLcDrivesStator.accepted_eq,
   StdMs350FcmlPhaseLeg.accepted_eq,
   StdCleanroomTcadStack.accepted_eq,
   StdCnc5AxisMill.accepted_eq,
   StdLcDrivesStator.claim_peak_temp_open_recursion_holds,
   StdMs350FcmlPhaseLeg.claim_switching_loss_open_recursion_holds,
   StdCleanroomTcadStack.claim_drain_current_open_recursion_holds,
   StdCleanroomTcadStack.claim_transferred_power_open_recursion_holds,
   StdCnc5AxisMill.claim_volumetric_decomposition_holds⟩

/-! ## 2. `stdlib/physical/LcDrivesStator.obend` as an Open-Recursive `Obend.Logic.Composition` -/

/-- Seed record for `PhysicalStator`, elaborated directly from `stdlib/physical/LcDrivesStator.obend`. -/
def seedStatorFields : List (String × Term) :=
  StdLcDrivesStator.lcDrivesProductionStator_comp.seed

/-- Layer 0 (innermost): `spec OuterJacketStator for PhysicalStator`, elaborated from `stdlib/physical/LcDrivesStator.obend`. -/
def outerJacketStatorLayer : Layer :=
  StdLcDrivesStator.outerJacketStator_comp.top

/-- Layer 1 (middle): `spec LcDrivesInSlotUpgrade for PhysicalStator`, elaborated from `stdlib/physical/LcDrivesStator.obend`. -/
def lcDrivesInSlotUpgradeLayer : Layer :=
  StdLcDrivesStator.statorInSlot_comp.top

/-- Layer 2 (outermost): `spec FiveAxisFinishMilled for PhysicalStator`, elaborated from `stdlib/physical/LcDrivesStator.obend`. -/
def fiveAxisFinishMilledLayer : Layer :=
  StdLcDrivesStator.lcDrivesProductionStator_comp.top

/-- The full 3-layer open-recursive `Composition` for `lcDrivesProductionStator()`,
    matching `StdLcDrivesStator.lcDrivesProductionStator_comp` identically. -/
def lcDrivesStatorUsdComp : Composition where
  top := fiveAxisFinishMilledLayer
  below := [lcDrivesInSlotUpgradeLayer, outerJacketStatorLayer]
  seed := seedStatorFields

theorem lcDrivesStatorUsdComp_eq_imported :
    lcDrivesStatorUsdComp = StdLcDrivesStator.lcDrivesProductionStator_comp := rfl

/-- **Closedness Certificate**: `lcDrivesStatorUsdComp` and its unresolved flattening are closed. -/
theorem lcDrivesStatorUsdComp_closed : lcDrivesStatorUsdComp.closedB = true := by
  decide +kernel

/-- **Vtable Flattening Soundness (`flatten_sound`)**. -/
theorem lcDrivesStatorUsd_flatten_sound (m : String) :
    .get lcDrivesStatorUsdComp.flatten m ≈b .get lcDrivesStatorUsdComp.object m :=
  flatten_sound lcDrivesStatorUsdComp lcDrivesStatorUsdComp_closed m

/-- **Leaf Book Emission Soundness (`book_sound`)**. -/
theorem lcDrivesStatorUsd_book_sound (m : String) :
    .get (emit lcDrivesStatorUsdComp).link m ≈b .get lcDrivesStatorUsdComp.object m :=
  book_sound lcDrivesStatorUsdComp lcDrivesStatorUsdComp_closed m

/-- **Static `super` Elimination & Slot Dependency Certificate**. -/
theorem lcDrivesStatorUsd_book_shape_verified :
    let B := emit lcDrivesStatorUsdComp
    B.slots = ["massKg", "camSurfaceErrorUm", "thermalResistance", "sdfMargin", "peakWindingTemp"] ∧
    B.defs.map (fun d => (d.member, d.slot, d.kind, d.reads)) =
      [ ("massKg", 0, .cell, [])
      , ("camSurfaceErrorUm", 1, .method, [])
      , ("thermalResistance", 2, .cell, [])
      , ("sdfMargin", 3, .method, [])
      , ("peakWindingTemp", 4, .method, [2])
      ] ∧
    B.closedB = true := by
  decide +kernel

/-! ## 3. `stdlib/physical/Cnc5AxisMill.obend` as an Open-Recursive `Obend.Logic.Composition` -/

/-- Seed record for `Cnc5AxisMill`, elaborated directly from `stdlib/physical/Cnc5AxisMill.obend`. -/
def seedMillFields : List (String × Term) :=
  StdCnc5AxisMill.compensated5AxisMill_comp.seed

/-- Layer 0 (innermost): `spec Uncompensated5AxisMill for Cnc5AxisMill`, elaborated from `stdlib/physical/Cnc5AxisMill.obend`. -/
def uncompensated5AxisMillLayer : Layer :=
  StdCnc5AxisMill.raw5AxisMill_comp.top

/-- Layer 1 (outermost): `spec AbbeAndRuckigCompensatedMill for Cnc5AxisMill`, elaborated from `stdlib/physical/Cnc5AxisMill.obend`. -/
def abbeAndRuckigCompensatedMillLayer : Layer :=
  StdCnc5AxisMill.compensated5AxisMill_comp.top

/-- The 2-layer open-recursive `Composition` for `compensated5AxisMill()` in `stdlib/physical/Cnc5AxisMill.obend`. -/
def cnc5AxisMillComp : Composition where
  top := abbeAndRuckigCompensatedMillLayer
  below := [uncompensated5AxisMillLayer]
  seed := seedMillFields

theorem cnc5AxisMillComp_eq_imported :
    cnc5AxisMillComp = StdCnc5AxisMill.compensated5AxisMill_comp := rfl

/-- **Closedness Certificate**: `cnc5AxisMillComp` and its unresolved flattening are closed. -/
theorem cnc5AxisMillComp_closed : cnc5AxisMillComp.closedB = true := by
  decide +kernel

/-- **Vtable Flattening Soundness (`flatten_sound`)**. -/
theorem cnc5AxisMill_flatten_sound (m : String) :
    .get cnc5AxisMillComp.flatten m ≈b .get cnc5AxisMillComp.object m :=
  flatten_sound cnc5AxisMillComp cnc5AxisMillComp_closed m

/-- **Leaf Book Emission Soundness (`book_sound`)**. -/
theorem cnc5AxisMill_book_sound (m : String) :
    .get (emit cnc5AxisMillComp).link m ≈b .get cnc5AxisMillComp.object m :=
  book_sound cnc5AxisMillComp cnc5AxisMillComp_closed m

/-! ## 4. Whole-Book Synthesis of `stdlib/physical/*.obend` Parts to FPGA RTL & 64-Bit AMD `CDNA3` VOP64 GPU ISA -/

/-- **End-to-End Userspace `stdlib/physical/LcDrivesStator.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` VOP64 GPU Theorem**. -/
theorem userspace_physical_stator_to_fpga_verified :
    (match compileBookToRtl "lc_drives_userspace_stator" (emit lcDrivesStatorUsdComp) with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 8#64) (fun _ => 0#64) ==
         [ ("out_massKg", 395#64)
         , ("out_camSurfaceErrorUm", 34#64)
         , ("out_thermalResistance", 9#64)
         , ("out_sdfMargin", 24#64)
         , ("out_peakWindingTemp", 122#64)
         ]) &&
       (match m.wires[3]? with
        | some wSdf =>
          let (rSdf, _, codeSdf) := compileRtlExprToAmdGpu 1 wSdf.expr
          let finalVgprs :=
            runAmdGpuVop64Prog (fun _ => 8#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeSdf
          finalVgprs rSdf == 24#64
        | none => false)
     | none => false) = true := by
  decide +kernel

/-- **End-to-End Userspace `stdlib/physical/Cnc5AxisMill.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` VOP64 GPU Theorem**. -/
theorem userspace_cnc_5axis_to_fpga_and_amd_gpu_verified :
    (match compileBookToRtl "cnc_5axis_userspace_mill" (emit cnc5AxisMillComp) with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 6#64) (fun _ => 0#64) ==
         [ ("out_servoLagUm", 6#64)
         , ("out_endMillDeflectionUm", 12#64)
         , ("out_abbeAngularDriftUm", 6#64)
         , ("out_commandedAxisAt10mmUm", 10024#64)
         , ("out_totalVolumetricErrorUm", 26#64)
         ]) &&
       (match m.wires[3]?, m.wires[4]? with
        | some wCmd, some wErr =>
          let (rCmd, _, codeCmd) := compileRtlExprToAmdGpu 1 wCmd.expr
          let (rErr, _, codeErr) := compileRtlExprToAmdGpu 1 wErr.expr
          let vgprsCmd :=
            runAmdGpuVop64Prog (fun _ => 6#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeCmd
          let vgprsErr :=
            runAmdGpuVop64Prog (fun _ => 6#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeErr
          vgprsCmd rCmd == 10024#64 &&
          vgprsErr rErr == 26#64
        | _, _ => false)
     | none => false) = true := by
  decide +kernel

/-! ## 5. General Bridge from `Term.fix (Term.mix baseLayer.term overrideLayer.term) (.record seed)` to `Leaf.flatten_sound` -/

/-- A 2-layer `Core4` prototype hierarchy closed directly via `Term.fix (Term.mix baseSpec overrideSpec) (.record seed)`. -/
def fixMixObject (baseLayer overrideLayer : Layer) (seed : List (String × Term)) : Term :=
  .fix (.mix baseLayer.term overrideLayer.term) (.record seed)

/-- The corresponding 2-layer `Obend.Logic.Composition`. -/
def fixMixComp (baseLayer overrideLayer : Layer) (seed : List (String × Term)) : Composition where
  top := overrideLayer
  below := [baseLayer]
  seed := seed

/-- Closedness check for `fixMixObject` and its unresolved flattening. -/
def fixMixClosedB (baseLayer overrideLayer : Layer) (seed : List (String × Term)) : Bool :=
  Obend.Law.closedB (fixMixObject baseLayer overrideLayer seed) &&
  Obend.Law.closedB (flatObject (fixMixComp baseLayer overrideLayer seed).flatRaw)

/-- Base pair relating `fixMixObject` and `flatObject C.flatRaw`. -/
def fixMixPair (baseLayer overrideLayer : Layer) (seed : List (String × Term)) (o f : Term) : Prop :=
  o = fixMixObject baseLayer overrideLayer seed ∧
  f = flatObject (fixMixComp baseLayer overrideLayer seed).flatRaw

theorem fixMixObject_unfold (baseLayer overrideLayer : Layer) (seed : List (String × Term)) :
    Step (fixMixObject baseLayer overrideLayer seed)
      (.app (.app (.mix baseLayer.term overrideLayer.term) (fixMixObject baseLayer overrideLayer seed)) (.record seed)) :=
  .fix _ _

theorem fixMix_layers_record (baseLayer overrideLayer : Layer) (O : Term) (seed : List (String × Term)) :
    Steps (.app (.app (.mix baseLayer.term overrideLayer.term) O) (.record seed))
      (.record (rowOf O seed [overrideLayer, baseLayer])) := by
  refine steps_trans (mix_apply _ _ _ _) ?_
  refine steps_trans (layer_apply overrideLayer O (superBelow O seed [baseLayer])) ?_
  unfold Layer.provide
  simp only [rowOf]
  cases overrideLayer.flat
  · simp only [Bool.false_eq_true, ite_false]
    exact steps_trans (Obend.Logic.steps_extend _ (superBelow_record O seed [baseLayer]))
      (steps_one (.extendRecord _ _))
  · exact .refl _

theorem fixMixPair_closed {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) :
    ClosedPairs (fixMixPair baseLayer overrideLayer seed) := by
  rintro o f ⟨rfl, rfl⟩
  simp only [fixMixClosedB, Bool.and_eq_true] at hc
  exact ⟨closed_of_closedB hc.1, closed_of_closedB hc.2⟩

theorem fixMixPair_base {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) :
    Base (fixMixPair baseLayer overrideLayer seed) where
  closed := fixMixPair_closed hc
  unfold := by
    rintro o f ⟨rfl, rfl⟩
    let C := fixMixComp baseLayer overrideLayer seed
    obtain ⟨f₁, sf, sf'⟩ := flatObject_unfold C.flatRaw
    have ⟨names, rel⟩ := row_joins (fixMixPair_closed hc)
      (O := fixMixObject baseLayer overrideLayer seed)
      (F := flatObject C.flatRaw)
      (.base ⟨rfl, rfl⟩) seed [overrideLayer, baseLayer]
    exact ⟨_, _, f₁, _, fixMixObject_unfold baseLayer overrideLayer seed,
      fixMix_layers_record baseLayer overrideLayer _ seed, sf, sf', .record names rel⟩

/-- **`fix_mix_flatten_sound`**:
For any closed 2-layer prototype hierarchy `Term.fix (Term.mix baseLayer.term overrideLayer.term) (.record seed)`,
every member projection `.get (Term.fix (Term.mix baseLayer.term overrideLayer.term) (.record seed)) m`
is behaviorally equivalent (`≈b`) to `.get (fixMixComp baseLayer overrideLayer seed).flatten m`! -/
theorem fix_mix_flatten_sound {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) (m : String) :
    .get (fixMixObject baseLayer overrideLayer seed) m ≈b
      .get (fixMixComp baseLayer overrideLayer seed).flatten m := by
  let C := fixMixComp baseLayer overrideLayer seed
  exact BEquiv.trans
    (bequiv_of_joins (fixMixPair_base hc) (.get m (.base ⟨rfl, rfl⟩)))
    (bequiv_of_ahead (.get m (resolve_ahead C.flatRaw)))

/-- Transfer a `Nat` evaluation from `C.flatten` to `Term.fix (Term.mix baseSpec overrideSpec) (.record seed)` via `fix_mix_flatten_sound`. -/
theorem evaluates_nat_of_fix_mix_flatten {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) (m : String) (x res : Nat)
    (hev : Evaluates (.app (.get (fixMixComp baseLayer overrideLayer seed).flatten m) (.nat x)) (.nat res)) :
    Evaluates (.app (.get (fixMixObject baseLayer overrideLayer seed) m) (.nat x)) (.nat res) := by
  have hbeq := fix_mix_flatten_sound hc m
  have hruns := sameRuns_app_of_bequiv hbeq (.nat x)
  have hhalts : Halts (.app (.get (fixMixComp baseLayer overrideLayer seed).flatten m) (.nat x)) (.natural res) :=
    ⟨.nat res, hev, .natural res⟩
  obtain ⟨v, hev', hobs⟩ := (hruns.halts (.natural res)).2 hhalts
  cases hobs
  exact hev'

/-- Transfer a `Bool` evaluation from `C.flatten` to `Term.fix (Term.mix baseSpec overrideSpec) (.record seed)` via `fix_mix_flatten_sound`. -/
theorem evaluates_bool_of_fix_mix_flatten {baseLayer overrideLayer : Layer} {seed : List (String × Term)}
    (hc : fixMixClosedB baseLayer overrideLayer seed = true) (m : String) (x : Nat) (res : Bool)
    (hev : Evaluates (.app (.get (fixMixComp baseLayer overrideLayer seed).flatten m) (.nat x)) (.boolean res)) :
    Evaluates (.app (.get (fixMixObject baseLayer overrideLayer seed) m) (.nat x)) (.boolean res) := by
  have hbeq := fix_mix_flatten_sound hc m
  have hruns := sameRuns_app_of_bequiv hbeq (.nat x)
  have hhalts : Halts (.app (.get (fixMixComp baseLayer overrideLayer seed).flatten m) (.nat x)) (.boolean res) :=
    ⟨.boolean res, hev, .boolean res⟩
  obtain ⟨v, hev', hobs⟩ := (hruns.halts (.boolean res)).2 hhalts
  cases hobs
  exact hev'

theorem steps_binary_right {op : Primitive} {l r r' : Term} (hl : Value l) (hr : Steps r r') :
    Steps (.binary op l r) (.binary op l r') :=
  steps_congr (fun x => .binary op l x) (fun s => .binaryRight _ _ hl s) hr

theorem steps_binary_left {op : Primitive} {l l' r : Term} (hl : Steps l l') :
    Steps (.binary op l r) (.binary op l' r) :=
  steps_congr (fun x => .binary op x r) (fun s => .binaryLeft _ _ s) hl

theorem run_steps_of_termEq {fuel : Nat} {t v : Term}
    (h : (match Obend.Law.run fuel t with | some w => Obend.Law.termEq w v | none => false) = true) :
    Steps t v := by
  have hrun : Obend.Law.run fuel t = some v := by
    revert h
    cases Obend.Law.run fuel t with
    | none => intro h; cases h
    | some w =>
      intro h
      rw [Obend.Law.termEq_sound h]
  exact (Obend.Law.run_sound (fuel := fuel) (t := t) (v := v) hrun).1

/-- Extract the inner method body (under the outer `λself.` binder) from a `Leaf.Book` slot. -/
def extractBookMethodInner (B : Book) (m : String) : Term :=
  match lookupBookCode B m with
  | some (.lam inner) => inner
  | _ => .nat 0

/-! ## 6. Domain Object 1: Multi-Layer LC Drives In-Slot Stator (`stdlib/physical/LcDrivesStator.obend`) -/

/-- Base `Core4` specification term `statorBaseSpec` (`OuterJacketStator`). -/
def statorBaseSpec : Term := outerJacketStatorLayer.term

/-- Override `Core4` specification term `inSlotCoolingOverrideSpec` (`LcDrivesInSlotUpgrade`). -/
def inSlotCoolingOverrideSpec : Term := lcDrivesInSlotUpgradeLayer.term

/-- **Domain Object 1 (`statorInSlotCore4Object`)**:
`Term.fix (Term.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)`. -/
def statorInSlotCore4Object : Term :=
  .fix (.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)

/-- The 2-layer `Composition` for `statorInSlotCore4Object`, matching `StdLcDrivesStator.statorInSlot_comp`. -/
def statorInSlotComp : Composition :=
  fixMixComp outerJacketStatorLayer lcDrivesInSlotUpgradeLayer seedStatorFields

theorem statorInSlotComp_eq_imported :
    statorInSlotComp = StdLcDrivesStator.statorInSlot_comp := rfl

theorem statorInSlot_closed :
    fixMixClosedB outerJacketStatorLayer lcDrivesInSlotUpgradeLayer seedStatorFields = true := by
  decide +kernel

@[simp] theorem statorInSlotFlatten_subst (σ : Nat → Term) :
    statorInSlotComp.flatten.substitute σ = statorInSlotComp.flatten :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

@[simp] theorem statorInSlotObject_subst (σ : Nat → Term) :
    statorInSlotCore4Object.substitute σ = statorInSlotCore4Object :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

def statorBaseSuperTerm : Term :=
  .app (.app statorBaseSpec statorInSlotCore4Object) (.record seedStatorFields)

@[simp] theorem statorBaseSuperTerm_subst (σ : Nat → Term) :
    statorBaseSuperTerm.substitute σ = statorBaseSuperTerm :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

/-- **`statorInSlot_flatten_sound`**: `.get statorInSlotCore4Object m ≈b .get statorInSlotComp.flatten m`. -/
theorem statorInSlot_flatten_sound (m : String) :
    .get statorInSlotCore4Object m ≈b .get statorInSlotComp.flatten m :=
  fix_mix_flatten_sound statorInSlot_closed m

/-- **Universal Parametric Theorem 1a (`stator_in_slot_peak_temp_forall`)**:
For EVERY copper loss `loss : Nat`, evaluating `.app (.get statorInSlotCore4Object "peakWindingTemp") (.nat loss)`
on the open-recursive `Core4` object `Term.fix (Term.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)`
late-binds `self.thermalResistance = 9` from `inSlotCoolingOverrideSpec` inside `statorBaseSpec`'s
`peakWindingTemp` method and evaluates constructively in `Core4` (`Evaluates`, `0 Classical.choice`) to `.nat (50 + loss * 9)`! -/
theorem stator_in_slot_peak_temp_forall (loss : Nat) :
    Evaluates (.app (.get statorInSlotCore4Object "peakWindingTemp") (.nat loss))
      (.nat (50 + loss * 9)) := by
  have hfn : Steps (.get statorInSlotCore4Object "peakWindingTemp")
      (.lam (.binary .add (.nat 50)
        (.binary .multiply (.bound 0) (.get statorInSlotCore4Object "thermalResistance")))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have htr : Steps (.get statorInSlotCore4Object "thermalResistance") (.nat 9) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (50 + loss * 9)⟩
  refine steps_trans (steps_app (.nat loss) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, statorInSlotObject_subst]
  refine steps_trans
    (steps_binary_right (.natural 50) (steps_binary_right (.natural loss) htr)) ?_
  refine .next (.binaryRight _ _ (.natural 50)
    (.primitive .multiply (.nat loss) (.nat 9) (.nat (loss * 9)) (.natural loss) (.natural 9) rfl)) ?_
  exact steps_one (.primitive .add (.nat 50) (.nat (loss * 9)) (.nat (50 + loss * 9))
    (.natural 50) (.natural (loss * 9)) rfl)

/-- **Universal Parametric Theorem 1b (`stator_in_slot_sdf_margin_forall`)**:
For EVERY radial coordinate `r : Nat`, evaluating `.app (.get statorInSlotCore4Object "sdfMargin") (.nat r)`
on `Term.fix (Term.mix statorBaseSpec inSlotCoolingOverrideSpec) (.record seedStatorFields)`
chains `inSlotCoolingOverrideSpec`'s `super.sdfMargin(r) + 6` with `statorBaseSpec`'s `r + 10`
and evaluates constructively in `Core4` (`0 Classical.choice`) to `.nat ((r + 10) + 6)`! -/
theorem stator_in_slot_sdf_margin_forall (r : Nat) :
    Evaluates (.app (.get statorInSlotCore4Object "sdfMargin") (.nat r))
      (.nat ((r + 10) + 6)) := by
  have hfn : Steps (.get statorInSlotCore4Object "sdfMargin")
      (.lam (.binary .add (.app (.get statorBaseSuperTerm "sdfMargin") (.bound 0)) (.nat 6))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsup : Steps (.get statorBaseSuperTerm "sdfMargin")
      (.lam (.binary .add (.bound 0) (.nat 10))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural ((r + 10) + 6)⟩
  refine steps_trans (steps_app (.nat r) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, statorBaseSuperTerm_subst]
  refine steps_trans (steps_binary_left (steps_app (.nat r) hsup)) ?_
  refine .next (.binaryLeft _ _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute]
  refine .next (.binaryLeft _ _
    (.primitive .add (.nat r) (.nat 10) (.nat (r + 10)) (.natural r) (.natural 10) rfl)) ?_
  exact steps_one (.primitive .add (.nat (r + 10)) (.nat 6) (.nat ((r + 10) + 6))
    (.natural (r + 10)) (.natural 6) rfl)

def statorPeakBody : Term :=
  extractBookMethodInner (emit statorInSlotComp) "peakWindingTemp"

/-- **Support Extraction Conservatism & Futamura 2 Commutation for Domain Object 1 (`stator_in_slot_support_and_futamura2`)**. -/
theorem stator_in_slot_support_and_futamura2 (env : String → Option Term) (newMass : Option Term) (loss : Nat) :
    let peakBody : Term := statorPeakBody
    let B := emit statorInSlotComp
    let pins := bookCanonicalPins B
    extractReadMembers peakBody = ["thermalResistance"] ∧
    substMemberEnv (mutateMemberEnv env "massKg" newMass) peakBody = substMemberEnv env peakBody ∧
    evalBook (specializeBook B pins) "peakWindingTemp" = evalBook B "peakWindingTemp" ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B) (encodePinsRecordForBook B pins))).bind
      (fun B_res => evalResidualBookAt B_res "peakWindingTemp" (.nat loss))) =
      evalBookUnderPinsAt B pins "peakWindingTemp" (.nat loss) := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant statorPeakBody env newMass (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel),
    (futamura2_compiler_generator_commutes (emit statorInSlotComp)
      (bookCanonicalPins (emit statorInSlotComp)) "peakWindingTemp" (.nat loss)).2.2.2⟩

/-! ## 7. Domain Object 2: `MS350` SiC Half-Bridge Phase Leg (`stdlib/physical/Ms350FcmlPhaseLeg.obend`) -/

/-- Seed record for the `MS350` SiC Half-Bridge Phase Leg, elaborated from `stdlib/physical/Ms350FcmlPhaseLeg.obend`. -/
def seedSicSwitchFields : List (String × Term) :=
  StdMs350FcmlPhaseLeg.ms350ProtectedPhaseLeg_comp.seed

/-- Base layer: `spec SicBaseSwitch for Ms350PhaseLeg`, elaborated from `stdlib/physical/Ms350FcmlPhaseLeg.obend`. -/
def sicBaseSwitchLayer : Layer :=
  StdMs350FcmlPhaseLeg.sicBasePhaseLeg_comp.top

/-- Override layer: `spec DeadtimeProtectionOverride for Ms350PhaseLeg`, elaborated from `stdlib/physical/Ms350FcmlPhaseLeg.obend`. -/
def deadtimeProtectionOverrideLayer : Layer :=
  StdMs350FcmlPhaseLeg.ms350ProtectedPhaseLeg_comp.top

/-- Base `Core4` specification term `sicBaseSwitchSpec`. -/
def sicBaseSwitchSpec : Term := sicBaseSwitchLayer.term

/-- Override `Core4` specification term `deadtimeProtectionOverrideSpec`. -/
def deadtimeProtectionOverrideSpec : Term := deadtimeProtectionOverrideLayer.term

/-- **Domain Object 2 (`ms350PhaseLegCore4Object`)**:
`Term.fix (Term.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)`. -/
def ms350PhaseLegCore4Object : Term :=
  .fix (.mix sicBaseSwitchSpec deadtimeProtectionOverrideSpec) (.record seedSicSwitchFields)

/-- The 2-layer `Composition` for `ms350PhaseLegCore4Object`, matching `StdMs350FcmlPhaseLeg.ms350ProtectedPhaseLeg_comp`. -/
def ms350PhaseLegComp : Composition :=
  fixMixComp sicBaseSwitchLayer deadtimeProtectionOverrideLayer seedSicSwitchFields

theorem ms350PhaseLegComp_eq_imported :
    ms350PhaseLegComp = StdMs350FcmlPhaseLeg.ms350ProtectedPhaseLeg_comp := rfl

theorem ms350PhaseLeg_closed :
    fixMixClosedB sicBaseSwitchLayer deadtimeProtectionOverrideLayer seedSicSwitchFields = true := by
  decide +kernel

@[simp] theorem ms350PhaseLegFlatten_subst (σ : Nat → Term) :
    ms350PhaseLegComp.flatten.substitute σ = ms350PhaseLegComp.flatten :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

@[simp] theorem ms350PhaseLegObject_subst (σ : Nat → Term) :
    ms350PhaseLegCore4Object.substitute σ = ms350PhaseLegCore4Object :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

def sicBaseSuperTerm : Term :=
  .app (.app sicBaseSwitchSpec ms350PhaseLegCore4Object) (.record seedSicSwitchFields)

@[simp] theorem sicBaseSuperTerm_subst (σ : Nat → Term) :
    sicBaseSuperTerm.substitute σ = sicBaseSuperTerm :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

/-- **`ms350PhaseLeg_flatten_sound`**: `.get ms350PhaseLegCore4Object m ≈b .get ms350PhaseLegComp.flatten m`. -/
theorem ms350PhaseLeg_flatten_sound (m : String) :
    .get ms350PhaseLegCore4Object m ≈b .get ms350PhaseLegComp.flatten m :=
  fix_mix_flatten_sound ms350PhaseLeg_closed m

/-- **`ms350PhaseLeg_book_sound`**: `.get (emit ms350PhaseLegComp).link m ≈b .get ms350PhaseLegComp.object m`. -/
theorem ms350PhaseLeg_book_sound (m : String) :
    .get (emit ms350PhaseLegComp).link m ≈b .get ms350PhaseLegComp.object m :=
  book_sound ms350PhaseLegComp (by decide +kernel) m

/-- **Universal Parametric Theorem 2a (`ms350_switching_loss_forall`)**. -/
theorem ms350_switching_loss_forall (currentA : Nat) :
    Evaluates (.app (.get ms350PhaseLegCore4Object "switchingLossUj") (.nat currentA))
      (.nat (currentA * 3 + 120)) := by
  have hfn : Steps (.get ms350PhaseLegCore4Object "switchingLossUj")
      (.lam (.binary .add (.binary .multiply (.bound 0) (.nat 3))
        (.get ms350PhaseLegCore4Object "deadtimeNs"))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hdt : Steps (.get ms350PhaseLegCore4Object "deadtimeNs") (.nat 120) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (currentA * 3 + 120)⟩
  refine steps_trans (steps_app (.nat currentA) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, ms350PhaseLegObject_subst]
  refine .next (.binaryLeft _ _
    (.primitive .multiply (.nat currentA) (.nat 3) (.nat (currentA * 3))
      (.natural currentA) (.natural 3) rfl)) ?_
  refine steps_trans (steps_binary_right (.natural (currentA * 3)) hdt) ?_
  exact steps_one (.primitive .add (.nat (currentA * 3)) (.nat 120) (.nat (currentA * 3 + 120))
    (.natural (currentA * 3)) (.natural 120) rfl)

/-- **Universal Parametric Theorem 2b (`ms350_shoot_through_safe_forall`)**. -/
theorem ms350_shoot_through_safe_forall (diDt : Nat) :
    Evaluates (.app (.get ms350PhaseLegCore4Object "shootThroughSafe") (.nat diDt))
      (.boolean (decide (diDt ≤ 80))) := by
  have hfn : Steps (.get ms350PhaseLegCore4Object "shootThroughSafe")
      (.lam (.binary .lessEqual (.bound 0)
        (.get ms350PhaseLegCore4Object "slewRateLimitVPerNs"))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsl : Steps (.get ms350PhaseLegCore4Object "slewRateLimitVPerNs") (.nat 80) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .boolean (decide (diDt ≤ 80))⟩
  refine steps_trans (steps_app (.nat diDt) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, ms350PhaseLegObject_subst]
  refine steps_trans (steps_binary_right (.natural diDt) hsl) ?_
  exact steps_one (.primitive .lessEqual (.nat diDt) (.nat 80) (.boolean (decide (diDt ≤ 80)))
    (.natural diDt) (.natural 80) rfl)

/-- **Universal Parametric Theorem 2c (`ms350_gate_delay_forall`)**. -/
theorem ms350_gate_delay_forall (margin : Nat) :
    Evaluates (.app (.get ms350PhaseLegCore4Object "effectiveGateDelayNs") (.nat margin))
      (.nat ((margin + 12) + 25)) := by
  have hfn : Steps (.get ms350PhaseLegCore4Object "effectiveGateDelayNs")
      (.lam (.binary .add (.app (.get sicBaseSuperTerm "effectiveGateDelayNs") (.bound 0)) (.nat 25))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsup : Steps (.get sicBaseSuperTerm "effectiveGateDelayNs")
      (.lam (.binary .add (.bound 0) (.nat 12))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural ((margin + 12) + 25)⟩
  refine steps_trans (steps_app (.nat margin) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, sicBaseSuperTerm_subst]
  refine steps_trans (steps_binary_left (steps_app (.nat margin) hsup)) ?_
  refine .next (.binaryLeft _ _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute]
  refine .next (.binaryLeft _ _
    (.primitive .add (.nat margin) (.nat 12) (.nat (margin + 12)) (.natural margin) (.natural 12) rfl)) ?_
  exact steps_one (.primitive .add (.nat (margin + 12)) (.nat 25) (.nat ((margin + 12) + 25))
    (.natural (margin + 12)) (.natural 25) rfl)

def ms350LossBody : Term :=
  extractBookMethodInner (emit ms350PhaseLegComp) "switchingLossUj"

/-- **Support Extraction Conservatism & Futamura 2 Commutation for Domain Object 2 (`ms350_support_and_futamura2`)**. -/
theorem ms350_support_and_futamura2 (env : String → Option Term) (newGate : Option Term) (currentA : Nat) :
    let lossBody : Term := ms350LossBody
    let B := emit ms350PhaseLegComp
    let pins := bookCanonicalPins B
    extractReadMembers lossBody = ["deadtimeNs"] ∧
    substMemberEnv (mutateMemberEnv env "effectiveGateDelayNs" newGate) lossBody = substMemberEnv env lossBody ∧
    evalBook (specializeBook B pins) "switchingLossUj" = evalBook B "switchingLossUj" ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B) (encodePinsRecordForBook B pins))).bind
      (fun B_res => evalResidualBookAt B_res "switchingLossUj" (.nat currentA))) =
      evalBookUnderPinsAt B pins "switchingLossUj" (.nat currentA) := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant ms350LossBody env newGate (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel),
    (futamura2_compiler_generator_commutes (emit ms350PhaseLegComp)
      (bookCanonicalPins (emit ms350PhaseLegComp)) "switchingLossUj" (.nat currentA)).2.2.2⟩

/-- **End-to-End Userspace `stdlib/physical/Ms350FcmlPhaseLeg.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` VOP64 GPU Theorem**. -/
theorem userspace_ms350_phase_leg_to_fpga_and_amd_gpu_verified :
    (match compileBookToRtl "ms350_fcml_userspace_phase_leg" (emit ms350PhaseLegComp) with
     | some m =>
       checkRtlModule m &&
       (evalModuleOutputs m (fun _ => 100#64) (fun _ => 0#64) ==
         [ ("out_deadtimeNs", 120#64)
         , ("out_slewRateLimitVPerNs", 80#64)
         , ("out_effectiveGateDelayNs", 137#64)
         , ("out_shootThroughSafe", 0#64)
         , ("out_switchingLossUj", 420#64)
         ]) &&
       (match m.wires[2]?, m.wires[3]?, m.wires[4]? with
        | some wGate, some wSafe, some wLoss =>
          let (rGate, _, codeGate) := compileRtlExprToAmdGpu 1 wGate.expr
          let (rSafe, _, codeSafe) := compileRtlExprToAmdGpu 1 wSafe.expr
          let (rLoss, _, codeLoss) := compileRtlExprToAmdGpu 1 wLoss.expr
          let vgprsGate :=
            runAmdGpuVop64Prog (fun _ => 10#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeGate
          let vgprsSafe60 :=
            runAmdGpuVop64Prog (fun _ => 60#64) (fun _ => 80#64) (fun _ => 0#64) (fun _ => 0#64) codeSafe
          let vgprsLoss100 :=
            runAmdGpuVop64Prog (fun _ => 100#64) (fun _ => 120#64) (fun _ => 0#64) (fun _ => 0#64) codeLoss
          vgprsGate rGate == 47#64 &&
          vgprsSafe60 rSafe == 1#64 &&
          vgprsLoss100 rLoss == 420#64
        | _, _, _ => false)
     | none => false) = true := by
  decide +kernel

/-! ## 8. Domain Object 3: $Q_3$ Photonic Coupler Array (`stdlib/physical/CleanroomTcadStack.obend`) -/

/-- Seed record for the $Q_3$ Photonic Coupler Array, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def seedPhotonicFields : List (String × Term) :=
  StdCleanroomTcadStack.q3KrawtchoukArray_comp.seed

/-- Base layer: `spec PlanarWaveguideBase for Q3PhotonicCouplerArray`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def planarWaveguideBaseLayer : Layer :=
  StdCleanroomTcadStack.planarWaveguideCoupler_comp.top

/-- Override layer: `spec KrawtchoukCouplingOverride for Q3PhotonicCouplerArray`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def krawtchoukCouplingOverrideLayer : Layer :=
  StdCleanroomTcadStack.q3KrawtchoukArray_comp.top

/-- Base `Core4` specification term `planarWaveguideBaseSpec`. -/
def planarWaveguideBaseSpec : Term := planarWaveguideBaseLayer.term

/-- Override `Core4` specification term `krawtchoukCouplingOverrideSpec`. -/
def krawtchoukCouplingOverrideSpec : Term := krawtchoukCouplingOverrideLayer.term

/-- **Domain Object 3 (`q3PhotonicCore4Object`)**:
`Term.fix (Term.mix planarWaveguideBaseSpec krawtchoukCouplingOverrideSpec) (.record seedPhotonicFields)`. -/
def q3PhotonicCore4Object : Term :=
  .fix (.mix planarWaveguideBaseSpec krawtchoukCouplingOverrideSpec) (.record seedPhotonicFields)

/-- The 2-layer `Composition` for `q3PhotonicCore4Object`, matching `StdCleanroomTcadStack.q3KrawtchoukArray_comp`. -/
def q3PhotonicComp : Composition :=
  fixMixComp planarWaveguideBaseLayer krawtchoukCouplingOverrideLayer seedPhotonicFields

theorem q3PhotonicComp_eq_imported :
    q3PhotonicComp = StdCleanroomTcadStack.q3KrawtchoukArray_comp := rfl

theorem q3Photonic_closed :
    fixMixClosedB planarWaveguideBaseLayer krawtchoukCouplingOverrideLayer seedPhotonicFields = true := by
  decide +kernel

@[simp] theorem q3PhotonicFlatten_subst (σ : Nat → Term) :
    q3PhotonicComp.flatten.substitute σ = q3PhotonicComp.flatten :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

@[simp] theorem q3PhotonicObject_subst (σ : Nat → Term) :
    q3PhotonicCore4Object.substitute σ = q3PhotonicCore4Object :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

def planarWaveguideSuperTerm : Term :=
  .app (.app planarWaveguideBaseSpec q3PhotonicCore4Object) (.record seedPhotonicFields)

@[simp] theorem planarWaveguideSuperTerm_subst (σ : Nat → Term) :
    planarWaveguideSuperTerm.substitute σ = planarWaveguideSuperTerm :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

/-- **`q3Photonic_flatten_sound`**: `.get q3PhotonicCore4Object m ≈b .get q3PhotonicComp.flatten m`. -/
theorem q3Photonic_flatten_sound (m : String) :
    .get q3PhotonicCore4Object m ≈b .get q3PhotonicComp.flatten m :=
  fix_mix_flatten_sound q3Photonic_closed m

/-- **`q3Photonic_book_sound`**: `.get (emit q3PhotonicComp).link m ≈b .get q3PhotonicComp.object m`. -/
theorem q3Photonic_book_sound (m : String) :
    .get (emit q3PhotonicComp).link m ≈b .get q3PhotonicComp.object m :=
  book_sound q3PhotonicComp (by decide +kernel) m

/-- **Universal Parametric Theorem 3a (`q3_photonic_transferred_power_forall`)**. -/
theorem q3_photonic_transferred_power_forall (pIn : Nat) :
    Evaluates (.app (.get q3PhotonicCore4Object "transferredPowerMw") (.nat pIn))
      (.nat (pIn * 7 + 3)) := by
  have hfn : Steps (.get q3PhotonicCore4Object "transferredPowerMw")
      (.lam (.binary .add
        (.binary .multiply (.bound 0) (.get q3PhotonicCore4Object "couplingWeight"))
        (.get q3PhotonicCore4Object "hypercubeDim"))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hcw : Steps (.get q3PhotonicCore4Object "couplingWeight") (.nat 7) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hdim : Steps (.get q3PhotonicCore4Object "hypercubeDim") (.nat 3) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (pIn * 7 + 3)⟩
  refine steps_trans (steps_app (.nat pIn) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, q3PhotonicObject_subst]
  refine steps_trans
    (steps_binary_left (steps_binary_right (.natural pIn) hcw)) ?_
  refine .next (.binaryLeft _ _
    (.primitive .multiply (.nat pIn) (.nat 7) (.nat (pIn * 7)) (.natural pIn) (.natural 7) rfl)) ?_
  refine steps_trans (steps_binary_right (.natural (pIn * 7)) hdim) ?_
  exact steps_one (.primitive .add (.nat (pIn * 7)) (.nat 3) (.nat (pIn * 7 + 3))
    (.natural (pIn * 7)) (.natural 3) rfl)

/-- **Universal Parametric Theorem 3b (`q3_photonic_phase_shift_forall`)**. -/
theorem q3_photonic_phase_shift_forall (modeIdx : Nat) :
    Evaluates (.app (.get q3PhotonicCore4Object "krawtchoukPhaseShiftMrad") (.nat modeIdx))
      (.nat (modeIdx * 15 + 45)) := by
  have hfn : Steps (.get q3PhotonicCore4Object "krawtchoukPhaseShiftMrad")
      (.lam (.binary .add (.app (.get planarWaveguideSuperTerm "krawtchoukPhaseShiftMrad") (.bound 0)) (.nat 45))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsup : Steps (.get planarWaveguideSuperTerm "krawtchoukPhaseShiftMrad")
      (.lam (.binary .multiply (.bound 0) (.nat 15))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (modeIdx * 15 + 45)⟩
  refine steps_trans (steps_app (.nat modeIdx) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, planarWaveguideSuperTerm_subst]
  refine steps_trans (steps_binary_left (steps_app (.nat modeIdx) hsup)) ?_
  refine .next (.binaryLeft _ _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute]
  refine .next (.binaryLeft _ _
    (.primitive .multiply (.nat modeIdx) (.nat 15) (.nat (modeIdx * 15))
      (.natural modeIdx) (.natural 15) rfl)) ?_
  exact steps_one (.primitive .add (.nat (modeIdx * 15)) (.nat 45) (.nat (modeIdx * 15 + 45))
    (.natural (modeIdx * 15)) (.natural 45) rfl)

def q3PowerBody : Term :=
  extractBookMethodInner (emit q3PhotonicComp) "transferredPowerMw"

/-- **Support Extraction Conservatism & Futamura 2 Commutation for Domain Object 3 (`q3_photonic_support_and_futamura2`)**. -/
theorem q3_photonic_support_and_futamura2 (env : String → Option Term) (newPhase : Option Term) (pIn : Nat) :
    let powerBody : Term := q3PowerBody
    let B := emit q3PhotonicComp
    let pins := bookCanonicalPins B
    extractReadMembers powerBody = ["couplingWeight", "hypercubeDim"] ∧
    substMemberEnv (mutateMemberEnv env "krawtchoukPhaseShiftMrad" newPhase) powerBody = substMemberEnv env powerBody ∧
    evalBook (specializeBook B pins) "transferredPowerMw" = evalBook B "transferredPowerMw" ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B) (encodePinsRecordForBook B pins))).bind
      (fun B_res => evalResidualBookAt B_res "transferredPowerMw" (.nat pIn))) =
      evalBookUnderPinsAt B pins "transferredPowerMw" (.nat pIn) := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant q3PowerBody env newPhase (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel),
    (futamura2_compiler_generator_commutes (emit q3PhotonicComp)
      (bookCanonicalPins (emit q3PhotonicComp)) "transferredPowerMw" (.nat pIn)).2.2.2⟩

/-! ## 9. Domain Object 4: Cleanroom-to-TCAD Semiconductor Wafer Stack (`stdlib/physical/CleanroomTcadStack.obend`) -/

/-- Seed record for `CleanroomTcadStack`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def seedTcadStackFields : List (String × Term) :=
  StdCleanroomTcadStack.cleanroomTcadStack_comp.seed

/-- Base layer: `spec PlanarBulkMosfetBase for CleanroomTcadStack`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def planarBulkMosfetBaseLayer : Layer :=
  StdCleanroomTcadStack.planarBulkTcadStack_comp.top

/-- Override layer: `spec HighKMetalGateFinFetUpgrade for CleanroomTcadStack`, elaborated from `stdlib/physical/CleanroomTcadStack.obend`. -/
def highKMetalGateFinFetUpgradeLayer : Layer :=
  StdCleanroomTcadStack.cleanroomTcadStack_comp.top

/-- Base `Core4` specification term `planarBulkMosfetBaseSpec`. -/
def planarBulkMosfetBaseSpec : Term := planarBulkMosfetBaseLayer.term

/-- Override `Core4` specification term `highKMetalGateFinFetUpgradeSpec`. -/
def highKMetalGateFinFetUpgradeSpec : Term := highKMetalGateFinFetUpgradeLayer.term

/-- **Domain Object 4 (`cleanroomTcadCore4Object`)**:
`Term.fix (Term.mix planarBulkMosfetBaseSpec highKMetalGateFinFetUpgradeSpec) (.record seedTcadStackFields)`. -/
def cleanroomTcadCore4Object : Term :=
  .fix (.mix planarBulkMosfetBaseSpec highKMetalGateFinFetUpgradeSpec) (.record seedTcadStackFields)

/-- The 2-layer `Composition` for `cleanroomTcadCore4Object`, matching `StdCleanroomTcadStack.cleanroomTcadStack_comp`. -/
def cleanroomTcadStackComp : Composition :=
  fixMixComp planarBulkMosfetBaseLayer highKMetalGateFinFetUpgradeLayer seedTcadStackFields

theorem cleanroomTcadStackComp_eq_imported :
    cleanroomTcadStackComp = StdCleanroomTcadStack.cleanroomTcadStack_comp := rfl

theorem cleanroomTcadStack_closed :
    fixMixClosedB planarBulkMosfetBaseLayer highKMetalGateFinFetUpgradeLayer seedTcadStackFields = true := by
  decide +kernel

@[simp] theorem cleanroomTcadFlatten_subst (σ : Nat → Term) :
    cleanroomTcadStackComp.flatten.substitute σ = cleanroomTcadStackComp.flatten :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

@[simp] theorem cleanroomTcadObject_subst (σ : Nat → Term) :
    cleanroomTcadCore4Object.substitute σ = cleanroomTcadCore4Object :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

def planarBulkSuperTerm : Term :=
  .app (.app planarBulkMosfetBaseSpec cleanroomTcadCore4Object) (.record seedTcadStackFields)

@[simp] theorem planarBulkSuperTerm_subst (σ : Nat → Term) :
    planarBulkSuperTerm.substitute σ = planarBulkSuperTerm :=
  closed_subst (closed_of_closedB (by decide +kernel)) σ

/-- **`cleanroomTcadStack_flatten_sound`**: `.get cleanroomTcadCore4Object m ≈b .get cleanroomTcadStackComp.flatten m`. -/
theorem cleanroomTcadStack_flatten_sound (m : String) :
    .get cleanroomTcadCore4Object m ≈b .get cleanroomTcadStackComp.flatten m :=
  fix_mix_flatten_sound cleanroomTcadStack_closed m

/-- **`cleanroomTcadStack_book_sound`**: `.get (emit cleanroomTcadStackComp).link m ≈b .get cleanroomTcadStackComp.object m`. -/
theorem cleanroomTcadStack_book_sound (m : String) :
    .get (emit cleanroomTcadStackComp).link m ≈b .get cleanroomTcadStackComp.object m :=
  book_sound cleanroomTcadStackComp (by decide +kernel) m

/-- **Universal Parametric Theorem 4a (`cleanroom_tcad_drain_current_forall`)**:
For EVERY gate overdrive `vov : Nat`, evaluating `.app (.get cleanroomTcadCore4Object "drainCurrentUa") (.nat vov)`
late-binds `self.vthMilliV = 250` from `highKMetalGateFinFetUpgradeLayer` inside `planarBulkMosfetBaseLayer`'s
`drainCurrentUa` method and evaluates constructively in `Core4` (`0 Classical.choice`) to `.nat (vov * 5 + 250)`! -/
theorem cleanroom_tcad_drain_current_forall (vov : Nat) :
    Evaluates (.app (.get cleanroomTcadCore4Object "drainCurrentUa") (.nat vov))
      (.nat (vov * 5 + 250)) := by
  have hfn : Steps (.get cleanroomTcadCore4Object "drainCurrentUa")
      (.lam (.binary .add (.binary .multiply (.bound 0) (.nat 5))
        (.get cleanroomTcadCore4Object "vthMilliV"))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hvth : Steps (.get cleanroomTcadCore4Object "vthMilliV") (.nat 250) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural (vov * 5 + 250)⟩
  refine steps_trans (steps_app (.nat vov) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, cleanroomTcadObject_subst]
  refine .next (.binaryLeft _ _
    (.primitive .multiply (.nat vov) (.nat 5) (.nat (vov * 5))
      (.natural vov) (.natural 5) rfl)) ?_
  refine steps_trans (steps_binary_right (.natural (vov * 5)) hvth) ?_
  exact steps_one (.primitive .add (.nat (vov * 5)) (.nat 250) (.nat (vov * 5 + 250))
    (.natural (vov * 5)) (.natural 250) rfl)

/-- **Universal Parametric Theorem 4b (`cleanroom_tcad_gate_delay_forall`)**:
For EVERY fanout `fanout : Nat`, evaluating `.app (.get cleanroomTcadCore4Object "gateDelayPs") (.nat fanout)`
chains `super.gateDelayPs(fanout) + 4` with `fanout * 8 + 20` and evaluates constructively in `Core4`
(`0 Classical.choice`) to `.nat ((fanout * 8 + 20) + 4)`! -/
theorem cleanroom_tcad_gate_delay_forall (fanout : Nat) :
    Evaluates (.app (.get cleanroomTcadCore4Object "gateDelayPs") (.nat fanout))
      (.nat ((fanout * 8 + 20) + 4)) := by
  have hfn : Steps (.get cleanroomTcadCore4Object "gateDelayPs")
      (.lam (.binary .add (.app (.get planarBulkSuperTerm "gateDelayPs") (.bound 0)) (.nat 4))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  have hsup : Steps (.get planarBulkSuperTerm "gateDelayPs")
      (.lam (.binary .add (.binary .multiply (.bound 0) (.nat 8)) (.nat 20))) :=
    run_steps_of_termEq (fuel := 30) (by decide +kernel)
  refine ⟨?_, .natural ((fanout * 8 + 20) + 4)⟩
  refine steps_trans (steps_app (.nat fanout) hfn) ?_
  refine .next (.beta _ _) ?_
  simp only [instantiate, Term.substitute, planarBulkSuperTerm_subst]
  refine steps_trans (steps_binary_left (steps_app (.nat fanout) hsup)) ?_
  refine .next (.binaryLeft _ _ (.beta _ _)) ?_
  simp only [instantiate, Term.substitute]
  refine .next (.binaryLeft _ _
    (.binaryLeft _ _
      (.primitive .multiply (.nat fanout) (.nat 8) (.nat (fanout * 8)) (.natural fanout) (.natural 8) rfl))) ?_
  refine .next (.binaryLeft _ _
    (.primitive .add (.nat (fanout * 8)) (.nat 20) (.nat (fanout * 8 + 20))
      (.natural (fanout * 8)) (.natural 20) rfl)) ?_
  exact steps_one (.primitive .add (.nat (fanout * 8 + 20)) (.nat 4) (.nat ((fanout * 8 + 20) + 4))
    (.natural (fanout * 8 + 20)) (.natural 4) rfl)

def tcadDrainCurrentBody : Term :=
  extractBookMethodInner (emit cleanroomTcadStackComp) "drainCurrentUa"

/-- **Support Extraction Conservatism & Futamura 2 Commutation for Domain Object 4 (`cleanroom_tcad_support_and_futamura2`)**. -/
theorem cleanroom_tcad_support_and_futamura2 (env : String → Option Term) (newEot : Option Term) (vov : Nat) :
    let drainBody : Term := tcadDrainCurrentBody
    let B := emit cleanroomTcadStackComp
    let pins := bookCanonicalPins B
    extractReadMembers drainBody = ["vthMilliV"] ∧
    substMemberEnv (mutateMemberEnv env "oxideEotPicometers" newEot) drainBody = substMemberEnv env drainBody ∧
    evalBook (specializeBook B pins) "drainCurrentUa" = evalBook B "drainCurrentUa" ∧
    ((decodeBookTerm? (runStagedCompiler (futamura2BookCompiler B) (encodePinsRecordForBook B pins))).bind
      (fun B_res => evalResidualBookAt B_res "drainCurrentUa" (.nat vov))) =
      evalBookUnderPinsAt B pins "drainCurrentUa" (.nat vov) := by
  dsimp only
  refine ⟨by decide +kernel,
    (extractReadMembers_mutation_invariant tcadDrainCurrentBody env newEot (by decide +kernel)).1,
    optTermEq_sound (by decide +kernel),
    (futamura2_compiler_generator_commutes (emit cleanroomTcadStackComp)
      (bookCanonicalPins (emit cleanroomTcadStackComp)) "drainCurrentUa" (.nat vov)).2.2.2⟩

/-- **End-to-End Userspace `stdlib/physical/CleanroomTcadStack.obend` -> `Leaf.Book` -> FPGA RTL -> AMD `CDNA3` VOP64 GPU Theorem**. -/
theorem userspace_cleanroom_tcad_and_q3_to_fpga_and_amd_gpu_verified :
    (match compileBookToRtl "cleanroom_tcad_userspace_stack" (emit cleanroomTcadStackComp),
           compileBookToRtl "q3_photonic_userspace_array" (emit q3PhotonicComp) with
     | some mTcad, some mQ3 =>
       checkRtlModule mTcad &&
       checkRtlModule mQ3 &&
       (evalModuleOutputs mTcad (fun _ => 200#64) (fun _ => 0#64) ==
         [ ("out_oxideEotPicometers", 700#64)
         , ("out_vthMilliV", 250#64)
         , ("out_gateDelayPs", 1624#64)
         , ("out_drainCurrentUa", 1250#64)
         ]) &&
       (evalModuleOutputs mQ3 (fun _ => 20#64) (fun _ => 0#64) ==
         [ ("out_couplingWeight", 7#64)
         , ("out_krawtchoukPhaseShiftMrad", 345#64)
         , ("out_hypercubeDim", 3#64)
         , ("out_transferredPowerMw", 143#64)
         ]) &&
       (match mTcad.wires[2]?, mQ3.wires[1]? with
        | some wDelay, some wPhase =>
          let (rDelay, _, codeDelay) := compileRtlExprToAmdGpu 1 wDelay.expr
          let (rPhase, _, codePhase) := compileRtlExprToAmdGpu 1 wPhase.expr
          let vgprsDelay :=
            runAmdGpuVop64Prog (fun _ => 4#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codeDelay
          let vgprsPhase :=
            runAmdGpuVop64Prog (fun _ => 3#64) (fun _ => 0#64) (fun _ => 0#64) (fun _ => 0#64) codePhase
          vgprsDelay rDelay == 56#64 &&
          vgprsPhase rPhase == 90#64
        | _, _ => false)
     | _, _ => false) = true := by
  decide +kernel

end Obend.Hardware.UserspacePhysical
end
