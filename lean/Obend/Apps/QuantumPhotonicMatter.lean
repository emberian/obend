module
/-
# Obend.Apps.QuantumPhotonicMatter — Flagship App #8: Quantum Photonic & Topological Matter Co-Processor

Connects the canonical `.obend` standard library `stdlib/physical/QuantumPhotonicMatter.obend`
and the 4-module `.obend` application package in `apps/quantum-photonic-matter/`:
1. `apps/quantum-photonic-matter/ClementsKrawtchoukArray.obend` (`QPMClements`: `BaseKrawtchoukBusSpec` -> `SymmetryPreservingKrawtchoukOverride`)
2. `apps/quantum-photonic-matter/ThermoOpticCrosstalkComp.obend` (`QPMCrosstalk`: `BaseFaddeevLeVerrierCompSpec` -> `ClosedLoopCrosstalkOverride`)
3. `apps/quantum-photonic-matter/MajoranaTetronSyndromes.obend` (`QPMTetron`: `BaseTetronBraidSpec` -> `ParityCooledTetronOverride`)
4. `apps/quantum-photonic-matter/QuantumPhotonicTop.obend` (`QPMCoProcTop`: `BaseQuantumPhotonicCoProcSpec` -> `FaultTolerantCoProcOverride`)

directly to the mechanized quantum/photonic/topological hardware & spectral analysis stack:
- `Obend.Hardware.QuantumMatter`:
  * 1-WL quotient-hypergraph compression & reverse-AD intertwining (`quotientOpenHypergraph_intertwines_eval_and_adjoint`),
  * DPR guard slot (`quotientHypergraphSlot`) and 1-cycle symmetry-breaking pin fallback (`quotientHypergraph_moved_pin_blocks`),
  * Planar Clements $4 \times 4$ optical power conservation (`planarClements4x4_conserves_optical_power`) and quantitative disorder leakage (`perturbative_disorder_leakage_bound`),
  * Faddeev–LeVerrier $4 \times 4$ exact thermal crosstalk cancellation (`compensateThermalCrosstalk_exact_4x4`),
  * Majorana tetron Artin braid group relation (`majoranaBraid_artin_relation`) and Lindblad parity cooling (`parityCoolingJumpOp_dark_on_even_and_corrects_odd`),
- `Obend.Hardware.Photonics`:
  * Coupled-Mode Theory (CMT) Taylor interval enclosure & Krawtchouk length synthesis (`cmt_phase_5050_encloses_3db_split`, `cmt_unitarity_interval_encloses_one`, `cmt_krawtchouk_length_synthesis_sound`),
- `Obend.Analysis.Equitable` & `Obend.Analysis.QuantumWalk`:
  * 1-WL partition stabilization (`wlStabilize_fixedPoint_iff_equitable`),
  * Universal Lagrange–Sylvester spectral projectors (`computeLagrangeProjector_2x2_and_3x3_universal`, `computed_lagrange_projectors_k2_p3_q3_exact`),
  * Szegedy bipartite quantum walk intertwining (`szegedy_intertwining_power`, `cellUniformSzegedyPST_iff_quotient`),
  * Matrix Taylor propagator & $\ell_\infty$ remainder bound (`matrixTaylorPropagator_intertwines_quotient`, `matrixTaylorPropagator_encloses_k2_and_q3_pst`),
- `Obend.Leaf.Futamura`, `Obend.Spec.CrossPackage`, `Obend.Hardware.Compiler`:
  * Vtable flattening (`flatten_sound`), `Leaf.Book` emission (`book_sound`), in-core pins-only 2nd Futamura specialization (`inCoreBookCompiler_specializes_from_pinsOnly`), cross-package cone survival (`coneSupports_linkComposition_of_disjoint`), and verified RTL + AMD `CDNA3` `VOP64` GPU synthesis.
-/
public import Lean
public import Obend.Hardware.UserspacePhysical
public import Obend.Hardware.QuantumMatter
public import Obend.Hardware.Photonics
public import Obend.Analysis.Equitable
public import Obend.Analysis.QuantumWalk
public import Obend.Leaf.Futamura
public import Obend.Spec.CrossPackage
public import Obend.Tactic.Tooth
public meta import Lean
public meta import Obend.Hardware.UserspacePhysical
@[expose] public section

namespace Obend.Apps.QuantumPhotonicMatter

open Lean (Json toJson Name Ident Syntax TSyntax Quote quote mkIdent)
open Lean.Elab.Command (CommandElabM elabCommand)
open Obend.Core.Term
open Obend.Equiv
open Obend.Logic
open Obend.Leaf
open Obend.Leaf.Futamura
open Obend.Lower
open Obend.Slot
open Obend.Slot.World
open Obend.Spec.CrossPackage
open Obend.Analysis
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
open Obend.Hardware.OpenHypergraph
open Obend.Hardware.QuantumMatter
open Obend.Hardware.Photonics
open Obend.Hardware.UserspacePhysical

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 0. Multi-Module `#import_obend` Elaborator for `apps/quantum-photonic-matter/*.obend` -/

meta def sanitizeQpmModuleName (stem : String) : String :=
  let chars := stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  match chars with
  | [] => "Main"
  | c :: _ =>
    let s := String.ofList (if c.isAlpha || c == '_' then chars else '_' :: chars)
    if Obend.Spec.Parse.isIdent s.toList then s else "Main"

meta def stripQpmImportQuotes (raw : String) : String :=
  let s := raw.trimAscii.toString
  if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
    ((s.drop 1).dropEnd 1).toString
  else
    s

meta def resolveQpmImportedObendPath (parentFile : System.FilePath) (rawImportPath : String) :
    IO System.FilePath := do
  let clean := stripQpmImportQuotes rawImportPath
  let rel1 := match parentFile.parent with
    | some dir => dir / clean
    | none => System.FilePath.mk clean
  let r1 ← resolvePhysicalObendPath rel1
  if ← r1.pathExists then return r1
  let stripped := if clean.startsWith "./" then (clean.drop 2).toString else clean
  let rel2 := match parentFile.parent with
    | some dir => dir / stripped
    | none => System.FilePath.mk stripped
  let r2 ← resolvePhysicalObendPath rel2
  if ← r2.pathExists then return r2
  let fileName := (System.FilePath.mk stripped).fileName.getD stripped
  for sub in ["apps/quantum-photonic-matter/", "stdlib/physical/", "stdlib/core/", "stdlib/ledger/", "stdlib/usd/"] do
    let cand ← resolvePhysicalObendPath (System.FilePath.mk (sub ++ fileName))
    if ← cand.pathExists then return cand
  return r1

meta def parseAndCheckQpmObendModule (src : String) (moduleName : String)
    (prior : List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)) :
    Except String (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) := do
  let sha256 := Obend.Spec.Sha256.hex src.toUTF8
  let ast ← match Obend.Spec.FrontEnd.parseSource moduleName src with
    | .ok a => pure a
    | .error d => throw s!"{d.stage}: {d.message}"
  let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
  let mut lockedImports : List Obend.Spec.FrontEnd.LockedImport := []
  for edge in parsedEdges.toList do
    let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
    let edgeAlias := (edge.getObjValAs? String "alias").toOption.getD ""
    let edgeSpan := (edge.getObjVal? "span").toOption.getD .null
    let cleanPath := stripQpmImportQuotes edgePath
    let stemMod := sanitizeQpmModuleName ((System.FilePath.mk cleanPath).fileStem.getD edgeAlias)
    let found? := prior.zipIdx.find? fun ((sm, _), _) =>
      sm.name == stemMod || (edgeAlias != "" && sm.name == edgeAlias)
    let some ((targetSm, _), targetIdx) := found?
      | throw s!"module {moduleName}: imported module '{edgePath}' (alias '{edgeAlias}') not found"
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
    source := src
    sha256 := sha256
    imports := lockedImports
  }
  let decodedMod ← match Obend.Spec.FrontEnd.checkParsed srcMod ast with
    | .ok m => pure m
    | .error d => throw s!"{d.stage}: {d.message}"
  return (srcMod, decodedMod)

meta def loadQpmObendClosure :
    Nat → System.FilePath →
    List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) →
    IO (Except String (List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)))
  | 0, path, _ => return .error s!"import depth limit exceeded while loading {path}"
  | fuel + 1, path, acc => do
    let resolved ← resolvePhysicalObendPath path
    let modName := sanitizeQpmModuleName (resolved.fileStem.getD "Main")
    if acc.any (fun (sm, _) => sm.name == modName) then
      return .ok acc
    match ← (IO.FS.readBinFile resolved).toBaseIO with
    | .error e => return .error (toString e)
    | .ok bytes =>
      let some rawSrc := Obend.Spec.Parse.decodeSource bytes
        | return .error s!"{resolved}: invalid UTF-8"
      let ast ← match Obend.Spec.FrontEnd.parseSource modName rawSrc with
        | .ok a => pure a
        | .error d => return .error s!"{d.stage}: {d.message}"
      let parsedEdges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
      let mut curAcc := acc
      for edge in parsedEdges.toList do
        let edgePath := (edge.getObjValAs? String "path").toOption.getD ""
        let impFile ← resolveQpmImportedObendPath resolved edgePath
        match ← loadQpmObendClosure fuel impFile curAcc with
        | .error err => return .error err
        | .ok nextAcc => curAcc := nextAcc
      match parseAndCheckQpmObendModule rawSrc modName curAcc with
      | .error err => return .error err
      | .ok pair => return .ok (curAcc ++ [pair])

meta structure QpmElaboratedDef where
  name         : String
  reducedVal?  : Option Term
  composition? : Option Composition
  book?        : Option Book

meta structure QpmElaboratedModule where
  moduleName : String
  lawsCount  : Nat
  defs       : List QpmElaboratedDef
  claims     : List PhysicalElaboratedClaim

meta def elaborateQpmObendFile (pathStr : String) : IO (Except String QpmElaboratedModule) := do
  match ← loadQpmObendClosure 32 (System.FilePath.mk pathStr) [] with
  | .error err => return .error err
  | .ok closure =>
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
        (Json.arr #[]) (Json.arr #[]) defaultPhysicalLimits "definition" [] with
    | .error d => return .error s!"{d.stage}: {d.message}"
    | .ok lowering =>
      match Obend.Spec.FrontEnd.accept lowering with
      | .error d => return .error s!"{d.stage}: {d.message}"
      | .ok acc =>
        let erasedTerm := acc.erased
        let rootTerm := (Obend.Logic.Program.knotOf erasedTerm).getD erasedTerm
        let rawFields := Obend.Logic.Program.knotFields rootTerm
        let mut pdefs : List QpmElaboratedDef := []
        for d in callables do
          let shortName := d.name
          let fullKey := modName ++ "." ++ shortName
          let knotTerm : Term := .get rootTerm fullKey
          let opened := match rawFields.lookup fullKey with
            | some rb => Obend.Logic.openTerm rb rootTerm (.record [])
            | none => knotTerm
          let rawReduced? := Obend.Law.run 50000 opened
          let reducedVal? := match rawReduced? with
            | some (.nat n) => some (.nat n)
            | some (.boolean b) => some (.boolean b)
            | some (.label s) => some (.label s)
            | _ => none
          let wantNamed : Composition → Bool := fun C => C.top.name != ""
          let rawComp? :=
            if reducedVal?.isSome then none
            else
              match d with
              | .function .. =>
                match findWorkbookObjectPhys wantNamed 64 knotTerm with
                | some c => some c
                | none =>
                  match findWorkbookObjectPhys wantNamed 64 (.app knotTerm (.record [])) with
                  | some c => some c
                  | none =>
                    let inlined := resolveKnotTermPhys rootTerm rawFields [fullKey] 8 opened
                    decodeWorkbookWithSeedPhys wantNamed inlined
              | _ => none
          let foundComp? := rawComp?.map compactCompositionForKernel
          let book? := foundComp?.map Obend.Leaf.emit
          pdefs := pdefs ++ [{
            name := shortName
            reducedVal? := reducedVal?
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
          lawsCount := lowering.laws.length
          defs := pdefs
          claims := pclaims
        }

local elab "#import_obend " pathLit:str " as " nsId:ident : command => do
  let pathStr := pathLit.getString
  let res ← IO.toEIO
    (fun e => Lean.Exception.error Lean.Syntax.missing (Lean.MessageData.ofFormat (Std.Format.text (toString e))))
    (elaborateQpmObendFile pathStr)
  match res with
  | .error err =>
    Lean.throwError m!"#import_obend failed on {pathStr}: {err}"
  | .ok pkg =>
    let ns := nsId.getId
    let accId := mkIdent (ns ++ `accepted)
    let accEqId := mkIdent (ns ++ `accepted_eq)
    let lawsCntId := mkIdent (ns ++ `laws_count)
    elabCommand (← `(@[expose] public def $accId : Bool := true))
    elabCommand (← `(public theorem $accEqId : $accId = true := rfl))
    elabCommand (← `(@[expose] public def $lawsCntId : Nat := $(quote pkg.lawsCount)))
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
              obligationMeaning_of_check_beq Obend.Logic.defaultExternalFormats (k := 256) (o := $objId) (j := $justId) (by decide +kernel)
          ))

/-! ## 1. Compile-Time Elaboration of `stdlib/physical/QuantumPhotonicMatter.obend` & `apps/quantum-photonic-matter/*.obend` -/

#import_obend "stdlib/physical/QuantumPhotonicMatter.obend" as QPMStdlib
#import_obend "apps/quantum-photonic-matter/ClementsKrawtchoukArray.obend" as QPMClements
#import_obend "apps/quantum-photonic-matter/ThermoOpticCrosstalkComp.obend" as QPMCrosstalk
#import_obend "apps/quantum-photonic-matter/MajoranaTetronSyndromes.obend" as QPMTetron
#import_obend "apps/quantum-photonic-matter/QuantumPhotonicTop.obend" as QPMCoProcTop

/-- **`quantumPhotonicMatter_all_accepted_and_claims_hold`**:
All 5 `.obend` modules (`stdlib/physical/QuantumPhotonicMatter.obend` plus the 4 application
modules in `apps/quantum-photonic-matter/`) pass `FrontEnd.accept = true`, discharge their
open-recursion claims (`clements_power_open_recursion`, `tetron_braid_open_recursion`,
`krawtchouk_quotient_open_recursion`, `faddeev_drive_open_recursion`,
`tetron_syndrome_braid_open_recursion`, and `coproc_quotient_adjoint_open_recursion`), inherit
package laws across multi-file `import` boundaries (`QPMCoProcTop.laws_count = 9`), and evaluate
concrete open-recursive quantum/photonic co-processor methods:
- `krawtchoukMacsAt16 = 3206` (`16 * 4 + 3142`),
- `krawtchoukFidelityAt4 = 2004` (`(4 * 250 + 4) + 1000`),
- `precompDriveAt50 = 9319` (`50 * 11 + 8769`),
- `residualMetricAt3 = 125` (`(3 * 0 + 110) + 15`),
- `tetronBraidDepthAt10 = 200` (`10 * 4 + 160`),
- `tetronRecoveryAt3 = 64` (`(3 * 16 + 4) + 12`),
- `coprocAdjointOpsAt25 = 8869` (`25 * 4 + 8769`),
- `coprocBudgetAt6 = 132` (`(6 * 16 + 4) + 32`). -/
theorem quantumPhotonicMatter_all_accepted_and_claims_hold :
    QPMStdlib.accepted = true ∧
    QPMClements.accepted = true ∧
    QPMCrosstalk.accepted = true ∧
    QPMTetron.accepted = true ∧
    QPMCoProcTop.accepted = true ∧
    QPMCoProcTop.laws_count = 9 ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      QPMStdlib.claim_clements_power_open_recursion_obj
      QPMStdlib.claim_clements_power_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      QPMStdlib.claim_tetron_braid_open_recursion_obj
      QPMStdlib.claim_tetron_braid_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      QPMClements.claim_krawtchouk_quotient_open_recursion_obj
      QPMClements.claim_krawtchouk_quotient_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      QPMCrosstalk.claim_faddeev_drive_open_recursion_obj
      QPMCrosstalk.claim_faddeev_drive_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      QPMTetron.claim_tetron_syndrome_braid_open_recursion_obj
      QPMTetron.claim_tetron_syndrome_braid_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      QPMCoProcTop.claim_coproc_quotient_adjoint_open_recursion_obj
      QPMCoProcTop.claim_coproc_quotient_adjoint_open_recursion_just ∧
    QPMClements.krawtchoukMacsAt16_val = .nat 3206 ∧
    QPMClements.krawtchoukFidelityAt4_val = .nat 2004 ∧
    QPMCrosstalk.precompDriveAt50_val = .nat 9319 ∧
    QPMCrosstalk.residualMetricAt3_val = .nat 125 ∧
    QPMTetron.tetronBraidDepthAt10_val = .nat 200 ∧
    QPMTetron.tetronRecoveryAt3_val = .nat 64 ∧
    QPMCoProcTop.coprocAdjointOpsAt25_val = .nat 8869 ∧
    QPMCoProcTop.coprocBudgetAt6_val = .nat 132 :=
  ⟨QPMStdlib.accepted_eq,
   QPMClements.accepted_eq,
   QPMCrosstalk.accepted_eq,
   QPMTetron.accepted_eq,
   QPMCoProcTop.accepted_eq,
   rfl,
   QPMStdlib.claim_clements_power_open_recursion_holds,
   QPMStdlib.claim_tetron_braid_open_recursion_holds,
   QPMClements.claim_krawtchouk_quotient_open_recursion_holds,
   QPMCrosstalk.claim_faddeev_drive_open_recursion_holds,
   QPMTetron.claim_tetron_syndrome_braid_open_recursion_holds,
   QPMCoProcTop.claim_coproc_quotient_adjoint_open_recursion_holds,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Vtable Flattening, `Leaf.Book` Emission, Pins-Only Futamura & Cross-Package Cone Survival -/

theorem quantumPhotonicMatter_compositions_closed :
    QPMClements.calibratedKrawtchoukBus_comp.closedB = true ∧
    QPMCrosstalk.closedLoopThermoOpticComp_comp.closedB = true ∧
    QPMTetron.parityCooledTetronDecoder_comp.closedB = true ∧
    QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.closedB = true := by
  decide +kernel

theorem quantumPhotonicMatter_flatten_and_book_sound (m : String) :
    (.get QPMClements.calibratedKrawtchoukBus_comp.flatten m ≈b
      .get QPMClements.calibratedKrawtchoukBus_comp.object m) ∧
    (.get (emit QPMClements.calibratedKrawtchoukBus_comp).link m ≈b
      .get QPMClements.calibratedKrawtchoukBus_comp.object m) ∧
    (.get QPMCrosstalk.closedLoopThermoOpticComp_comp.flatten m ≈b
      .get QPMCrosstalk.closedLoopThermoOpticComp_comp.object m) ∧
    (.get (emit QPMCrosstalk.closedLoopThermoOpticComp_comp).link m ≈b
      .get QPMCrosstalk.closedLoopThermoOpticComp_comp.object m) ∧
    (.get QPMTetron.parityCooledTetronDecoder_comp.flatten m ≈b
      .get QPMTetron.parityCooledTetronDecoder_comp.object m) ∧
    (.get (emit QPMTetron.parityCooledTetronDecoder_comp).link m ≈b
      .get QPMTetron.parityCooledTetronDecoder_comp.object m) ∧
    (.get QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.flatten m ≈b
      .get QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.object m) ∧
    (.get (emit QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp).link m ≈b
      .get QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.object m) := by
  have ⟨hc1, hc2, hc3, hc4⟩ := quantumPhotonicMatter_compositions_closed
  exact ⟨flatten_sound _ hc1 m, book_sound _ hc1 m,
         flatten_sound _ hc2 m, book_sound _ hc2 m,
         flatten_sound _ hc3 m, book_sound _ hc3 m,
         flatten_sound _ hc4 m, book_sound _ hc4 m⟩

theorem quantumPhotonicMatter_inCore_futamura2 (pins : List LeafPin) :
    dataPinSpecialize
      (.app (inCoreBookCompiler QPMClements.calibratedKrawtchoukBus_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook QPMClements.calibratedKrawtchoukBus_book pins) ∧
    dataPinSpecialize
      (.app (inCoreBookCompiler QPMCrosstalk.closedLoopThermoOpticComp_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook QPMCrosstalk.closedLoopThermoOpticComp_book pins) ∧
    dataPinSpecialize
      (.app (inCoreBookCompiler QPMTetron.parityCooledTetronDecoder_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook QPMTetron.parityCooledTetronDecoder_book pins) ∧
    dataPinSpecialize
      (.app (inCoreBookCompiler QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_book pins) ∧
    coneSupports
      (linkComposition QPMCoProcTop.baseQuantumPhotonicCoProc_comp QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.top)
      ["wlCompressedShells", "faddeevCrosstalkDet"] =
      coneSupports QPMCoProcTop.baseQuantumPhotonicCoProc_comp ["wlCompressedShells", "faddeevCrosstalkDet"] := by
  have hflat : QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.top.flat = false := by decide +kernel
  have hdisj : ∀ m ∈ ["wlCompressedShells", "faddeevCrosstalkDet"],
      m ∉ overlayModifiedFields QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.top := by
    decide +kernel
  exact ⟨(inCoreBookCompiler_specializes_from_pinsOnly QPMClements.calibratedKrawtchoukBus_book pins).1,
         (inCoreBookCompiler_specializes_from_pinsOnly QPMCrosstalk.closedLoopThermoOpticComp_book pins).1,
         (inCoreBookCompiler_specializes_from_pinsOnly QPMTetron.parityCooledTetronDecoder_book pins).1,
         (inCoreBookCompiler_specializes_from_pinsOnly QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_book pins).1,
         coneSupports_linkComposition_of_disjoint
           QPMCoProcTop.baseQuantumPhotonicCoProc_comp
           QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_comp.top
           ["wlCompressedShells", "faddeevCrosstalkDet"] hflat hdisj⟩

/-- **`quantumPhotonicMatter_rtl_and_amd_gpu_verified`**:
Compiles `QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_book` and
`QPMClements.calibratedKrawtchoukBus_book` into verified `RtlModule`s (`checkRtlModule = true`)
and 64-bit AMD `CDNA3` `VOP64` GPU instructions (`compileRtlExprToAmdGpu` + `runAmdGpuVop64Prog`). -/
theorem quantumPhotonicMatter_rtl_and_amd_gpu_verified :
    (match compileBookToRtl "qpm_coproc_top" QPMCoProcTop.faultTolerantQuantumPhotonicCoProc_book,
           compileBookToRtl "qpm_krawtchouk_bus" QPMClements.calibratedKrawtchoukBus_book with
     | some mTop, some mBus =>
       checkRtlModule mTop &&
       checkRtlModule mBus &&
       (evalModuleOutputs mTop (fun _ => 25#64) (fun _ => 0#64) ==
         [ ("out_cmtKrawtchoukLength2Nm", 3142#64)
         , ("out_coProcessorCycleBudget", 436#64)
         , ("out_wlCompressedShells", 4#64)
         , ("out_faddeevCrosstalkDet", 8769#64)
         , ("out_quotientReverseAdjointOps", 8869#64)
         ]) &&
       (evalModuleOutputs mBus (fun _ => 16#64) (fun _ => 0#64) ==
         [ ("out_krawtchoukCouplingLength2Nm", 3142#64)
         , ("out_pstTransferFidelityPpm", 5004#64)
         , ("out_fullModes", 8#64)
         , ("out_quotientShells", 4#64)
         , ("out_krawtchoukCouplingLength0Nm", 1571#64)
         , ("out_krawtchoukCouplingLength1Nm", 2721#64)
         , ("out_quotientAdjointMacs", 3206#64)
         ]) &&
       (match mTop.wires[4]? with
        | some wAdj =>
          let (rAdj, _, codeAdj) := compileRtlExprToAmdGpu 1 wAdj.expr
          let wires := evalWireTable (fun _ => 25#64) (fun _ => 0#64) mTop.wires
          let vgprs :=
            runAmdGpuVop64Prog (fun _ => 25#64) wires (fun _ => 0#64) (fun _ => 0#64) codeAdj
          vgprs rAdj == 8869#64
        | none => false)
     | _, _ => false) = true := by
  decide +kernel

/-! ## 3. 1-WL Quotient Compression, DPR Guard Fallback, Clements Unitarity & CMT Synthesis -/

/-- **`quantumPhotonicMatter_wl_quotient_clements_and_cmt_sound`**:
1. **Universal 1-WL Quotient Compression & Reverse-AD Intertwining (`quotientOpenHypergraph_intertwines_eval_and_adjoint`)**:
   Compresses `buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2` (24 wires) and its `compileGraphAdjoint`
   reverse-AD graph to `quotientOpenHypergraph W0 W1 op2` (12 wires) with exact forward & reverse-AD
   intertwining across all cell-constant inputs `x0, y0, x1, y1` and cotangents `dOut0, dOut1`.
2. **DPR Guard Slot & 1-Cycle Symmetry-Breaking Pin Fallback (`quotientHypergraph_moved_pin_blocks`)**:
   `quotientHypergraphSlot` accepts the symmetric candidate at `vSym = mkChannelWeightView 0 5 5 7 7`
   (`usable = true`) and blocks it in 1 cycle at `vBroken = mkChannelWeightView 1 5 99 7 7`
   (`usable = false`, dead pin `[.layer "weights.w1"]`).
3. **Planar Clements $4 \times 4$ Unitarity & Faddeev–LeVerrier Crosstalk Cancellation (`QuantumMatter.lean`, `Equitable.lean`)**:
   - `planarClements4x4_conserves_optical_power` holds universally for all coupler parameters `t, kappa`
     and complex optical fields `e0, e1, e2, e3 : ComplexField`,
   - `compensateThermalCrosstalk_exact_4x4` cancels `goldenThermalCrosstalk4x4` to `8769 * target`
     (matching `QPMCrosstalk`'s `faddeevDetScale = 8769`).
4. **Physical CMT Directional-Coupler Taylor Interval & Krawtchouk Length Synthesis (`Photonics.lean`)**:
   - `cmt_phase_5050_encloses_3db_split` and `cmt_krawtchouk_length_synthesis_sound` verify physical
     interaction lengths ($L_{01} = 11\,\mu\text{m}$, $L_{12} = 14\,\mu\text{m}$) and enclose the
     exact $3 : 4 : 3$ Krawtchouk coupling invariant $4 \times 375000 = 3 \times 500000 = 1500000$. -/
theorem quantumPhotonicMatter_wl_quotient_clements_and_cmt_sound
    (W0 W1 : Int) (op2 : OpticOp)
    (x0 y0 x1 y1 dOut0 dOut1 : Int)
    (t kappa : Int) (e0 e1 e2 e3 : ComplexField)
    (phi0 phi1 phi2 phi3 : Int) :
    let gFull := buildSymmetric4LaneHypergraph W0 W0 W1 W1 op2
    let gQuot := quotientOpenHypergraph W0 W1 op2
    let envFull := liftSymmetric4LaneInitEnv x0 y0 x1 y1 dOut0 dOut1
    let envQuot := quotientHypergraphInitEnv x0 y0 x1 y1 dOut0 dOut1
    (gFull.wf = true ∧
     gQuot.wf = true ∧
     gFull.nodeTypes.length = 24 ∧
     gQuot.nodeTypes.length = 12 ∧
     evalHypergraphLayered gFull envFull = liftQuotientFwdOutputs (evalHypergraphLayered gQuot envQuot) ∧
     evalHypergraphLayered (compileGraphAdjoint gFull) envFull =
       liftQuotientAdjointOutputs (evalHypergraphLayered (compileGraphAdjoint gQuot) envQuot)) ∧
    (let gFullConcrete := buildSymmetric4LaneHypergraph 5 5 7 7 .add
     let gQuotConcrete := quotientOpenHypergraph 5 7 .add
     let pinsConcrete := sym4LaneWeightPins 5 7
     let candConcrete := QuotientHypergraphCandidate.quotientCompressed
                           gFullConcrete gQuotConcrete pinsConcrete true
     let vSym := mkChannelWeightView 0 5 5 7 7
     let vBroken := mkChannelWeightView 1 5 99 7 7
     quotientHypergraphSlot.usable (holdsAt vSym) candConcrete = true ∧
     quotientHypergraphSlot.usable (holdsAt vBroken) candConcrete = false ∧
     (quotientHypergraphSlot.dead (holdsAt vBroken) candConcrete).map LeafPin.cell =
       [.layer "weights.w1"]) ∧
    (let s := t * t + kappa * kappa
     let (p0, p1, p2, p3) := evalPlanarClements4x4 t kappa e0 e1 e2 e3
     s * p0.normSq + p1.normSq + p2.normSq + s * p3.normSq =
       s * (s * (e0.normSq + e1.normSq + e2.normSq + e3.normSq))) ∧
    (let res := compensateThermalCrosstalk goldenThermalCrosstalk4x4 [phi0, phi1, phi2, phi3]
     res.2 = 8769 ∧
     goldenThermalCrosstalk4x4.mulVec res.1 =
       [res.2 * phi0, res.2 * phi1, res.2 * phi2, res.2 * phi3]) ∧
    (cmtCouplerKrawtchouk01 0).interactionLengthUm = couplerKrawtchouk375.couplingLenUm ∧
    (cmtCoupler3dBSoi14Um 0).interactionLengthUm = coupler3dB.couplingLenUm ∧
    (CmtInterval.scaleNonneg 4 (evalCmtTransferPowerInterval (cmtCouplerKrawtchouk01 0))).contains 1500000 = true ∧
    (CmtInterval.scaleNonneg 3 (evalCmtTransferPowerInterval (cmtCoupler3dBSoi14Um 0))).contains 1500000 = true := by
  have hInter := quotientOpenHypergraph_intertwines_eval_and_adjoint W0 W1 op2 x0 y0 x1 y1 dOut0 dOut1
  have hDpr :
      (let gFullConcrete := buildSymmetric4LaneHypergraph 5 5 7 7 .add
       let gQuotConcrete := quotientOpenHypergraph 5 7 .add
       let pinsConcrete := sym4LaneWeightPins 5 7
       let candConcrete := QuotientHypergraphCandidate.quotientCompressed
                             gFullConcrete gQuotConcrete pinsConcrete true
       let vSym := mkChannelWeightView 0 5 5 7 7
       let vBroken := mkChannelWeightView 1 5 99 7 7
       quotientHypergraphSlot.usable (holdsAt vSym) candConcrete = true ∧
       quotientHypergraphSlot.usable (holdsAt vBroken) candConcrete = false ∧
       (quotientHypergraphSlot.dead (holdsAt vBroken) candConcrete).map LeafPin.cell =
         [.layer "weights.w1"]) := by decide +kernel
  have hClem := (planarClements4x4_conserves_optical_power t kappa e0 e1 e2 e3).1
  have hCrossDet : (compensateThermalCrosstalk goldenThermalCrosstalk4x4 [phi0, phi1, phi2, phi3]).2 = 8769 :=
    faddeevAdjugate_cancels_crosstalk_4x4.1
  have hCrossVec := compensateThermalCrosstalk_exact_4x4 phi0 phi1 phi2 phi3
  have hCmt := cmt_krawtchouk_length_synthesis_sound
  exact ⟨⟨hInter.1, hInter.2.1, hInter.2.2.1, hInter.2.2.2.1, hInter.2.2.2.2.2.1, hInter.2.2.2.2.2.2.2⟩,
         hDpr, hClem, ⟨hCrossDet, hCrossVec⟩,
         hCmt.1, hCmt.2.2.1, hCmt.2.2.2.2.2.2.2.2.2.1, hCmt.2.2.2.2.2.2.2.2.2.2.1⟩

/-! ## 4. Szegedy Walk Intertwining, Matrix Taylor PST & Majorana Parity-Cooling Stabilizers -/

/-- **`quantumPhotonicMatter_szegedy_taylor_and_majorana_sound`**:
1. **Universal Lagrange–Sylvester Projectors & Matrix Taylor PST (`QuantumWalk.lean`)**:
   - `computed_lagrange_projectors_k2_p3_q3_exact` verifies that executable Lagrange interpolation
     recovers the exact spectral projectors of $K_2$, $P_3$, and the 4-shell Krawtchouk $Q_3$ quotient,
   - `matrixTaylorPropagator_encloses_k2_and_q3_pst` verifies that the 8-vertex $Q_3$ matrix Taylor
     propagator matches the 4-cell Krawtchouk quotient propagator at antipodal vertex $7$ (cell $3$),
     and `evalQ3KrawtchoukAntipodalProbTube 157 100` encloses exact unit transfer probability $1$ while
     strictly excluding $9 / 10$.
2. **Topological Majorana Tetron Braiding & Lindblad Parity-Cooling (`QuantumMatter.lean`)**:
   - Non-Abelian Majorana braiding operators $T_{0,1}, T_{1,2}$ satisfy the Artin braid group relation
     $T_{0,1} T_{1,2} T_{0,1} = T_{1,2} T_{0,1} T_{1,2}$ while failing to commute (`majoranaBraid_artin_relation`),
   - For every Majorana mode $a \in \text{Fin } 4$, the dissipative parity-cooling jump operator
     $L_{\text{cool}}(a) = \rho(\gamma_a)\Pi_{\text{odd}}$ is dark on the even-parity computational
     sector ($L_{\text{cool}}(a)\Pi_{\text{even}} = 0_4$) and resets the odd-parity poisoned sector
     back to $\Pi_{\text{even}}$ (`parityCoolingJumpOp_dark_on_even_and_corrects_odd`). -/
theorem quantumPhotonicMatter_szegedy_taylor_and_majorana_sound (a : Fin 4) :
    let wQ3 : Nat → Int := fun i => if i == 0 then 1 else 0
    let q3Prob7 := evalQ3KrawtchoukAntipodalProbTube 157 100
    let m0 : Fin 4 := ⟨0, by decide⟩
    let m1 : Fin 4 := ⟨1, by decide⟩
    let m2 : Fin 4 := ⟨2, by decide⟩
    computeScaledLagrangeProjectors k2Matrix [1, -1] 2 = [k2ProjPlus, k2ProjMinus] ∧
    computeScaledLagrangeProjectors hypercubeQ3QuotientMatrix [3, 1, -1, -3] 48 =
      q3QuotientSylvesterProjectors ∧
    checkSpectralDecomposition hypercubeQ3QuotientMatrix 48 [3, 1, -1, -3]
      (computeScaledLagrangeProjectors hypercubeQ3QuotientMatrix [3, 1, -1, -3] 48) = true ∧
    evalScaledMatrixTaylorImag hypercubeQ3Matrix 157 100 4 (liftQuotientVec hypercubeQ3Part wQ3) 7 =
      evalScaledMatrixTaylorImag hypercubeQ3QuotientMatrix 157 100 4 wQ3 3 ∧
    Interval.containsRat q3Prob7 1 = true ∧
    Interval.containsRat q3Prob7 (CanonicalRat.mk 9 10) = false ∧
    cliffordMul (cliffordMul (majoranaBraidElem m0 m1) (majoranaBraidElem m1 m2)) (majoranaBraidElem m0 m1) =
      cliffordMul (cliffordMul (majoranaBraidElem m1 m2) (majoranaBraidElem m0 m1)) (majoranaBraidElem m1 m2) ∧
    cliffordMul (majoranaBraidElem m0 m1) (majoranaBraidElem m1 m2) ≠
      cliffordMul (majoranaBraidElem m1 m2) (majoranaBraidElem m0 m1) ∧
    (parityCoolingJumpOp a).mul spinorEvenParityProjector = GaussianMatrix.zero 4 ∧
    ((parityCoolingJumpOp a).mul spinorOddParityProjector).mul (parityCoolingJumpOp a).conjTranspose =
      spinorEvenParityProjector ∧
    spinorEvenParityProjector.mul (parityCoolingJumpOp a) = parityCoolingJumpOp a := by
  have hProj := computed_lagrange_projectors_k2_p3_q3_exact
  have hTaylor := matrixTaylorPropagator_encloses_k2_and_q3_pst
  have hBraid := majoranaBraid_artin_relation ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
    (by decide) (by decide) (by decide)
  have hCool := parityCoolingJumpOp_dark_on_even_and_corrects_odd a
  exact ⟨hProj.1,
         hProj.2.2.2.2.2.2.2.2.2.2.2.1,
         hProj.2.2.2.2.2.2.2.2.2.2.2.2,
         hTaylor.2.2.2.2.2.2.2.2.2.2.2.1,
         hTaylor.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hTaylor.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
         hBraid.1, hBraid.2.2,
         hCool.1, hCool.2.2.1, hCool.2.2.2.1⟩

/-- Broken `coprocAdjointOpsAt25` value for `#tooth` mutation check. -/
def brokenCoprocAdjointVal : Term := .nat 0

#tooth quantumPhotonicMatter_all_accepted_and_claims_hold by mutation
  QPMCoProcTop.coprocAdjointOpsAt25_val := brokenCoprocAdjointVal

end Obend.Apps.QuantumPhotonicMatter
end
