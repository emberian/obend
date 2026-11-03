module
/-
# Obend.Apps.SovereignDrex — Flagship App #7: 4-Validator Sovereign `DReX` + `K-CARRY` Live Exchange & Consensus Engine

Connects the 4-module `.obend` sovereign multi-asset exchange package in `apps/sovereign-drex/`:
1. `apps/sovereign-drex/Seat.obend` (`SovereignDrexSeat`: `BaseZoeSeatSpec` -> `InstitutionalMandateSeatOverride`)
2. `apps/sovereign-drex/OrderBook.obend` (`SovereignDrexOrderBook`: `BaseUniformOrderBookSpec` -> `WholesaleDvPOrderBookOverride`)
3. `apps/sovereign-drex/BatchClearing.obend` (`SovereignDrexClearing`: `BaseBatchClearingSpec` -> `SovereignCarryClearingOverride`)
4. `apps/sovereign-drex/SovereignDrexTop.obend` (`SovereignDrexTop`: `BaseSovereignDrexSpec` -> `CarryUpgradeSovereignDrexOverride`)

directly to the mechanized sovereign vault, live `K-CARRY` upgrade, and 4-validator BFT consensus stack:
- `Obend.Vault.Carry`:
  * Registered external judge format `"world-carry@1"` (`worldCarryFormat`) with non-trivial JSON wire rejection (`worldCarryFormat_refuses_empty_json`, `sampleBadCarryPlan_refused`),
  * Live world upgrade execution (`executeWorldCarry`) with total-book asset conservation (`carry_conserves_total_book`), `"forever"` crown preservation (`carry_preserves_forever_crowns`), and Agoric/Zoe offer-safety preservation (`carry_preserves_zoe_offer_safety`),
- `Obend.Vault.Hyperedge`:
  * State-bound half-edge conservation (`stateBoundTurn_conserves_actual_state_balances`) and unreported state-balance inflation refusal (`unreported_state_inflation_refused`),
- `Obend.Vault.SovereignEngine`:
  * Full oracle-validated turn gate (`checkOracleTurnValidAt`, `stepSovereignEngine`) with multi-asset conservation (`sovereignEngine_step_conserves_all_assets`), Zoe offer-safety + mandate enforcement (`sovereignEngine_enforces_zoe_and_mandates`), and stale-pin refusal (`stepSovereignEngine_oracleTurn_refuses_stale_pin`),
- `Obend.Consensus.SovereignFinality`:
  * Tier 1 disjoint fast-path commutativity (`tier1_disjoint_fast_path_commutes`),
  * 4-validator ($N = 4, f = 1$, quorum $2f + 1 = 3$) Tier 2 Simplex quorum promotion & accountable slashing (`tier2_simplex_quorum_and_accountable_safety`),
  * Durable BFT WAL crash-recovery anti-equivocation (`durable_recovery_prevents_equivocation`) and expose-once settlement externalization across crashes (`durable_expose_once_across_crashes`),
- `Obend.Leaf.Futamura`, `Obend.Spec.CrossPackage`, `Obend.Hardware.HDL`, `Obend.Hardware.Synth`, `Obend.Hardware.Compiler`:
  * Vtable flattening (`flatten_sound`), `Leaf.Book` emission (`book_sound`), in-core pins-only 2nd Futamura specialization (`inCoreBookCompiler_specializes_from_pinsOnly`), cross-package cone survival (`coneSupports_linkComposition_of_disjoint`), and verified synchronous batch-clearing + WAL anti-replay `RtlModule` (`sovereignDrexBatchTopRtlModule`, `emitModuleSV`) + AMD `CDNA3` `VOP64` GPU synthesis.
-/
public import Lean
public import Obend.Hardware.UserspacePhysical
public import Obend.Hardware.Synth
public import Obend.Vault.Carry
public import Obend.Vault.Hyperedge
public import Obend.Vault.SovereignEngine
public import Obend.Consensus.SovereignFinality
public import Obend.Leaf.Futamura
public import Obend.Spec.CrossPackage
public import Obend.Tactic.Tooth
public meta import Lean
public meta import Obend.Hardware.UserspacePhysical
@[expose] public section

namespace Obend.Apps.SovereignDrex

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
open Obend.Slot.Protocol
open Obend.Run.Control
open Obend.Run.Shared
open Obend.Run.Durable
open Obend.Fold.Collapse
open Obend.Spec.CrossPackage
open Obend.Vault
open Obend.Consensus
open Obend.Consensus.Finality
open Obend.Consensus.SovereignFinality
open Obend.Hardware.HDL
open Obend.Hardware.Synth
open Obend.Hardware.Compiler
open Obend.Hardware.Accelerators
open Obend.Hardware.UserspacePhysical

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 0. Multi-Module `#import_obend` Elaborator for `apps/sovereign-drex/*.obend` -/

meta def sanitizeDrexModuleName (stem : String) : String :=
  let chars := stem.toList.map fun c => if c.isAlphanum || c == '_' then c else '_'
  match chars with
  | [] => "Main"
  | c :: _ =>
    let s := String.ofList (if c.isAlpha || c == '_' then chars else '_' :: chars)
    if Obend.Spec.Parse.isIdent s.toList then s else "Main"

meta def resolveDrexImportedObendPath (parentFile : System.FilePath) (rawImportPath : String) :
    IO System.FilePath := do
  let clean := rawImportPath.trimAscii.toString
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
  for sub in ["apps/sovereign-drex/", "stdlib/core/", "stdlib/ledger/", "stdlib/usd/", "stdlib/physical/"] do
    let cand ← resolvePhysicalObendPath (System.FilePath.mk (sub ++ fileName))
    if ← cand.pathExists then return cand
  return r1

meta def parseAndCheckDrexObendModule (src : String) (moduleName : String)
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
    if !Obend.Spec.Capture.sealedPath edgePath then
      throw s!"module {moduleName}: unsealed import path '{edgePath}' (expected ./NAME.obend)"
    let stemMod := sanitizeDrexModuleName ((System.FilePath.mk edgePath).fileStem.getD edgeAlias)
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

meta def loadDrexObendClosure :
    Nat → System.FilePath →
    List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module) →
    IO (Except String (List (Obend.Spec.FrontEnd.SourceModule × Obend.Spec.Syntax.Module)))
  | 0, path, _ => return .error s!"import depth limit exceeded while loading {path}"
  | fuel + 1, path, acc => do
    let resolved ← resolvePhysicalObendPath path
    let modName := sanitizeDrexModuleName (resolved.fileStem.getD "Main")
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
        let impFile ← resolveDrexImportedObendPath resolved edgePath
        match ← loadDrexObendClosure fuel impFile curAcc with
        | .error err => return .error err
        | .ok nextAcc => curAcc := nextAcc
      match parseAndCheckDrexObendModule rawSrc modName curAcc with
      | .error err => return .error err
      | .ok pair => return .ok (curAcc ++ [pair])

meta structure DrexElaboratedDef where
  name         : String
  reducedVal?  : Option Term
  composition? : Option Composition
  book?        : Option Book

meta structure DrexElaboratedModule where
  moduleName : String
  lawsCount  : Nat
  defs       : List DrexElaboratedDef
  claims     : List PhysicalElaboratedClaim

meta def elaborateDrexObendFile (pathStr : String) : IO (Except String DrexElaboratedModule) := do
  match ← loadDrexObendClosure 32 (System.FilePath.mk pathStr) [] with
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
    match Obend.Spec.FrontEnd.lowerDecoded allSrcMods allDecodedMods entryIdx entryDef
        (Json.arr #[]) (Json.arr #[]) defaultPhysicalLimits "definition" [] with
    | .error d => return .error s!"{d.stage}: {d.message}"
    | .ok lowering =>
      match Obend.Spec.FrontEnd.accept lowering with
      | .error d => return .error s!"{d.stage}: {d.message}"
      | .ok acc =>
        let erasedTerm := acc.erased
        let rootTerm := (Obend.Logic.Program.knotOf erasedTerm).getD erasedTerm
        let rawFields := Obend.Logic.Program.knotFields rootTerm
        let mut pdefs : List DrexElaboratedDef := []
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
    (elaborateDrexObendFile pathStr)
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

/-! ## 1. Compile-Time Elaboration of `apps/sovereign-drex/*.obend` via `#import_obend` -/

#import_obend "apps/sovereign-drex/Seat.obend" as SovereignDrexSeat
#import_obend "apps/sovereign-drex/OrderBook.obend" as SovereignDrexOrderBook
#import_obend "apps/sovereign-drex/BatchClearing.obend" as SovereignDrexClearing
#import_obend "apps/sovereign-drex/SovereignDrexTop.obend" as SovereignDrexTop

/-- **`sovereignDrex_all_accepted_and_claims_hold`**:
All 4 `.obend` modules in `apps/sovereign-drex/` (`Seat`, `OrderBook`, `BatchClearing`,
and `SovereignDrexTop`) pass unmodified `FrontEnd.lower` + `FrontEnd.accept = true`
(matching `obend check --package apps/sovereign-drex/package.json`), discharge their open-recursion
claims (`zoe_offer_safety_open_recursion`, `orderbook_volume_open_recursion`,
`batch_clearing_open_recursion`, and `drex_settlement_open_recursion`), enforce all 6 entry-module
package laws (`SovereignDrexTop.laws_count = 6`), and evaluate concrete open-recursive exchange methods:
- `institutionalSafetyAt80 = 95000` (`75000 + 80 * 250`),
- `institutionalMandateAt15 = 1650` (`(15 * 10 + 1000) + 500`),
- `wholesaleVolumeAt20 = 127000` (`125000 + 20 * 100`),
- `wholesaleSlackAt10 = 10040` (`(10 * 4 + 9850) + 150`),
- `sovereignClearedAt12 = 7000` (`12 * 500 + 1000`),
- `sovereignDigestAt5 = 182` (`(5 * 32 + 6) + 16`),
- `drexSettlementAt8 = 5000` (`8 * 500 + 1000`),
- `drexFinalityTagAt3 = 227` (`(3 * 64 + 3) + 32`),
- `crossModuleDrexSummary = 110222` (`95000 + 10040 + 182 + 5000`). -/
theorem sovereignDrex_all_accepted_and_claims_hold :
    SovereignDrexSeat.accepted = true ∧
    SovereignDrexOrderBook.accepted = true ∧
    SovereignDrexClearing.accepted = true ∧
    SovereignDrexTop.accepted = true ∧
    SovereignDrexTop.laws_count = 6 ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SovereignDrexSeat.claim_zoe_offer_safety_open_recursion_obj
      SovereignDrexSeat.claim_zoe_offer_safety_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SovereignDrexOrderBook.claim_orderbook_volume_open_recursion_obj
      SovereignDrexOrderBook.claim_orderbook_volume_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SovereignDrexClearing.claim_batch_clearing_open_recursion_obj
      SovereignDrexClearing.claim_batch_clearing_open_recursion_just ∧
    Obend.Logic.obligationMeaningWithJudges Obend.Logic.defaultExternalFormats
      SovereignDrexTop.claim_drex_settlement_open_recursion_obj
      SovereignDrexTop.claim_drex_settlement_open_recursion_just ∧
    SovereignDrexSeat.institutionalSafetyAt80_val = .nat 95000 ∧
    SovereignDrexSeat.institutionalMandateAt15_val = .nat 1650 ∧
    SovereignDrexOrderBook.wholesaleVolumeAt20_val = .nat 127000 ∧
    SovereignDrexOrderBook.wholesaleSlackAt10_val = .nat 10040 ∧
    SovereignDrexClearing.sovereignClearedAt12_val = .nat 7000 ∧
    SovereignDrexClearing.sovereignDigestAt5_val = .nat 182 ∧
    SovereignDrexTop.drexSettlementAt8_val = .nat 5000 ∧
    SovereignDrexTop.drexFinalityTagAt3_val = .nat 227 ∧
    SovereignDrexTop.crossModuleDrexSummary_val = .nat 110222 :=
  ⟨SovereignDrexSeat.accepted_eq,
   SovereignDrexOrderBook.accepted_eq,
   SovereignDrexClearing.accepted_eq,
   SovereignDrexTop.accepted_eq,
   rfl,
   SovereignDrexSeat.claim_zoe_offer_safety_open_recursion_holds,
   SovereignDrexOrderBook.claim_orderbook_volume_open_recursion_holds,
   SovereignDrexClearing.claim_batch_clearing_open_recursion_holds,
   SovereignDrexTop.claim_drex_settlement_open_recursion_holds,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Vtable Flattening, `Leaf.Book` Emission, Pins-Only Futamura & Cross-Package Cone Survival -/

theorem sovereignDrex_compositions_closed :
    SovereignDrexSeat.institutionalZoeSeat_comp.closedB = true ∧
    SovereignDrexOrderBook.wholesaleDvPOrderBook_comp.closedB = true ∧
    SovereignDrexClearing.sovereignCarryClearing_comp.closedB = true ∧
    SovereignDrexTop.carryUpgradedSovereignDrex_comp.closedB = true := by
  decide +kernel

theorem sovereignDrex_flatten_and_book_sound (m : String) :
    (.get SovereignDrexSeat.institutionalZoeSeat_comp.flatten m ≈b
      .get SovereignDrexSeat.institutionalZoeSeat_comp.object m) ∧
    (.get (emit SovereignDrexSeat.institutionalZoeSeat_comp).link m ≈b
      .get SovereignDrexSeat.institutionalZoeSeat_comp.object m) ∧
    (.get SovereignDrexOrderBook.wholesaleDvPOrderBook_comp.flatten m ≈b
      .get SovereignDrexOrderBook.wholesaleDvPOrderBook_comp.object m) ∧
    (.get (emit SovereignDrexOrderBook.wholesaleDvPOrderBook_comp).link m ≈b
      .get SovereignDrexOrderBook.wholesaleDvPOrderBook_comp.object m) ∧
    (.get SovereignDrexClearing.sovereignCarryClearing_comp.flatten m ≈b
      .get SovereignDrexClearing.sovereignCarryClearing_comp.object m) ∧
    (.get (emit SovereignDrexClearing.sovereignCarryClearing_comp).link m ≈b
      .get SovereignDrexClearing.sovereignCarryClearing_comp.object m) ∧
    (.get SovereignDrexTop.carryUpgradedSovereignDrex_comp.flatten m ≈b
      .get SovereignDrexTop.carryUpgradedSovereignDrex_comp.object m) ∧
    (.get (emit SovereignDrexTop.carryUpgradedSovereignDrex_comp).link m ≈b
      .get SovereignDrexTop.carryUpgradedSovereignDrex_comp.object m) := by
  have ⟨hc1, hc2, hc3, hc4⟩ := sovereignDrex_compositions_closed
  exact ⟨flatten_sound _ hc1 m, book_sound _ hc1 m,
         flatten_sound _ hc2 m, book_sound _ hc2 m,
         flatten_sound _ hc3 m, book_sound _ hc3 m,
         flatten_sound _ hc4 m, book_sound _ hc4 m⟩

theorem sovereignDrex_inCore_futamura2 (pins : List LeafPin) :
    dataPinSpecialize
      (.app (inCoreBookCompiler SovereignDrexSeat.institutionalZoeSeat_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook SovereignDrexSeat.institutionalZoeSeat_book pins) ∧
    dataPinSpecialize
      (.app (inCoreBookCompiler SovereignDrexOrderBook.wholesaleDvPOrderBook_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook SovereignDrexOrderBook.wholesaleDvPOrderBook_book pins) ∧
    dataPinSpecialize
      (.app (inCoreBookCompiler SovereignDrexClearing.sovereignCarryClearing_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook SovereignDrexClearing.sovereignCarryClearing_book pins) ∧
    dataPinSpecialize
      (.app (inCoreBookCompiler SovereignDrexTop.carryUpgradedSovereignDrex_book) (encodePinsOnly pins)) =
      encodeBookTerm (inCoreSpecializeBook SovereignDrexTop.carryUpgradedSovereignDrex_book pins) ∧
    coneSupports
      (linkComposition SovereignDrexTop.baseSovereignDrex_comp SovereignDrexTop.carryUpgradedSovereignDrex_comp.top)
      ["validatorQuorum", "protectedWelfareCrown"] =
      coneSupports SovereignDrexTop.baseSovereignDrex_comp ["validatorQuorum", "protectedWelfareCrown"] := by
  have hflat : SovereignDrexTop.carryUpgradedSovereignDrex_comp.top.flat = false := by decide +kernel
  have hdisj : ∀ m ∈ ["validatorQuorum", "protectedWelfareCrown"],
      m ∉ overlayModifiedFields SovereignDrexTop.carryUpgradedSovereignDrex_comp.top := by
    decide +kernel
  exact ⟨(inCoreBookCompiler_specializes_from_pinsOnly SovereignDrexSeat.institutionalZoeSeat_book pins).1,
         (inCoreBookCompiler_specializes_from_pinsOnly SovereignDrexOrderBook.wholesaleDvPOrderBook_book pins).1,
         (inCoreBookCompiler_specializes_from_pinsOnly SovereignDrexClearing.sovereignCarryClearing_book pins).1,
         (inCoreBookCompiler_specializes_from_pinsOnly SovereignDrexTop.carryUpgradedSovereignDrex_book pins).1,
         coneSupports_linkComposition_of_disjoint
           SovereignDrexTop.baseSovereignDrex_comp
           SovereignDrexTop.carryUpgradedSovereignDrex_comp.top
           ["validatorQuorum", "protectedWelfareCrown"] hflat hdisj⟩

/-- **`sovereignDrex_rtl_and_amd_gpu_verified`**:
Compiles `SovereignDrexTop.carryUpgradedSovereignDrex_book` and
`SovereignDrexClearing.sovereignCarryClearing_book` into verified `RtlModule`s
(`checkRtlModule = true`) and 64-bit AMD `CDNA3` `VOP64` GPU instructions
(`compileRtlExprToAmdGpu` + `runAmdGpuVop64Prog`). -/
theorem sovereignDrex_rtl_and_amd_gpu_verified :
    (match compileBookToRtl "sovereign_drex_top" SovereignDrexTop.carryUpgradedSovereignDrex_book,
           compileBookToRtl "sovereign_drex_clearing" SovereignDrexClearing.sovereignCarryClearing_book with
     | some mTop, some mClear =>
       checkRtlModule mTop &&
       checkRtlModule mClear &&
       (evalModuleOutputs mTop (fun _ => 8#64) (fun _ => 0#64) ==
         [ ("out_settledCbdcLiquidity", 125000#64)
         , ("out_finalityCommitTag", 547#64)
         , ("out_validatorQuorum", 3#64)
         , ("out_protectedWelfareCrown", 1000#64)
         , ("out_batchSettlementCbdc", 5000#64)
         ]) &&
       (evalModuleOutputs mClear (fun _ => 5#64) (fun _ => 0#64) ==
         [ ("out_halfEdgeDeltaCount", 6#64)
         , ("out_carryPinDigest", 182#64)
         , ("out_quorumThreshold", 3#64)
         , ("out_welfareCrownFloor", 1000#64)
         , ("out_clearedCbdcAmount", 3500#64)
         ]) &&
       (match mTop.wires[4]? with
        | some wSettle =>
          let (rSettle, _, codeSettle) := compileRtlExprToAmdGpu 1 wSettle.expr
          let wires := evalWireTable (fun _ => 8#64) (fun _ => 0#64) mTop.wires
          let vgprs :=
            runAmdGpuVop64Prog (fun _ => 8#64) wires (fun _ => 0#64) (fun _ => 0#64) codeSettle
          vgprs rSettle == 5000#64
        | none => false)
     | _, _ => false) = true := by
  decide +kernel

/-! ## 3. `"world-carry@1"` Live Upgrade, Forever-Crowns & State-Bound Half-Edges (`Carry.lean`, `Hyperedge.lean`) -/

/-- **`sovereignDrex_world_carry_and_state_bound_hyperedge_sound`**:
1. **Non-Trivial `"world-carry@1"` Wire Rejection (`worldCarryFormat_refuses_empty_json`, `sampleBadCarryPlan_refused`)**:
   `Obend.Vault.worldCarryFormat.checkBytes 0 "{}" "{}"` refuses empty JSON with `.malformed`, and
   `worldCarryJudge` refuses `sampleBadCarryPlan` for silently dropping `"cell.deprecated"`.
2. **Universal `K-CARRY` Total-Book Conservation, `"forever"` Crown Preservation & Zoe Offer-Safety (`Carry.lean`)**:
   For ANY `W W' : LiveWorld` and `plan : CarryPlan` with `executeWorldCarry W plan = .ok W'`:
   - `W'.ledger.totalAsset a = W.ledger.totalAsset a` (`carry_conserves_total_book`),
   - Every carried cell `c ∈ W.cells` (`applyCellCarry plan c = some c'`) carries verified narrowing/preservation
     certificates and preserves `c.foreverCrown = true → c'.foreverCrown = true ∧ c'.invariant = c.invariant`
     (`carry_preserves_forever_crowns`),
   - Every active Zoe seat `s ∈ W.seats` is either preserved with `safeAt W'.ledger s.account s.proposal = true`
     or refunded and closed with zero remaining escrow (`carry_preserves_zoe_offer_safety`).
3. **State-Bound Half-Edge Conservation & Unreported Inflation Refusal (`Hyperedge.lean`)**:
   - `stateBoundTurn_conserves_actual_state_balances` and `unreported_state_inflation_refused`. -/
theorem sovereignDrex_world_carry_and_state_bound_hyperedge_sound
    {W W' : LiveWorld} {plan : CarryPlan}
    (hCarryOk : executeWorldCarry W plan = .ok W')
    (a : Obend.Ledger.AssetId) :
    Obend.Vault.worldCarryFormat.checkBytes 0 "{}" "{}" =
      Judge.Verdict.refused (Judge.FormatClause.malformed "object: invalid LiveWorld JSON: missing required fields (epoch, cells)") [] ∧
    worldCarryJudge.check 0 sampleValidLiveWorld sampleBadCarryPlan =
      Judge.Verdict.refused (.silentCellDrop "cell.deprecated") [] ∧
    W'.ledger.totalAsset a = W.ledger.totalAsset a ∧
    (∀ {c c' : LiveCell}, c ∈ W.cells → applyCellCarry plan c = some c' →
      (c'.law = c.law ∨
        ∃ narrowsCert preservesCert,
          checkContractCert (.narrows c'.law c.law) narrowsCert = Obend.Law.CertVerdict.valid ∧
          checkContractCert (.preserves c'.law c'.invariant) preservesCert = Obend.Law.CertVerdict.valid) ∧
      (c.foreverCrown = true → c'.foreverCrown = true ∧ c'.invariant = c.invariant)) ∧
    (∀ {s : Obend.Ledger.Seat}, s ∈ W.seats →
      (s ∈ W'.seats ∧ Obend.Ledger.safeAt W'.ledger s.account s.proposal = true) ∨
      (s ∉ W'.seats ∧ ∀ ast ∈ W.assets, W'.ledger.balance s.account ast = 0)) ∧
    (∀ (turn : VaultTurn) (assets : List String) (ast : String),
      ast ∈ assets →
      checkTurnStateBalancesBound assets turn = true →
      (turn.writeCells.map (fun d => extractCellAssetBalance d.postState ast - extractCellAssetBalance d.preState ast)).foldl (· + ·) 0 = 0 ∧
      (turn.writeCells.map (fun d => extractCellAssetBalance d.postState ast)).foldl (· + ·) 0 =
        (turn.writeCells.map (fun d => extractCellAssetBalance d.preState ast)).foldl (· + ·) 0) ∧
    (sumAssetDelta [unreportedInflationDelta] "USDC" = 0 ∧
     cellStateBalanceDelta unreportedInflationDelta "USDC" = 900 ∧
     checkDeltaMatchesStateBalances ["USDC"] unreportedInflationDelta = false) := by
  refine ⟨Obend.Vault.worldCarryFormat_refuses_empty_json,
          sampleBadCarryPlan_refused,
          carry_conserves_total_book hCarryOk a,
          fun hc hCarried =>
            let hCrown := carry_preserves_forever_crowns hCarryOk hc hCarried
            ⟨hCrown.1, hCrown.2.1⟩,
          fun hs => carry_preserves_zoe_offer_safety hCarryOk hs,
          fun turn assets ast hMem hBound =>
            stateBoundTurn_conserves_actual_state_balances turn assets ast hMem hBound,
          unreported_state_inflation_refused⟩

/-! ## 4. Oracle Turn Gate (`checkOracleTurnValidAt`), Sovereign Engine & 4-Validator BFT Finality -/

/-- 4-validator committee (`V0..V3`, $N = 4, f = 1$, quorum $2f + 1 = 3$) for `apps/sovereign-drex/`. -/
def drexCommittee4 : List Nat := [0, 1, 2, 3]

/-- Attested finality gate for Epoch 3 (`faults = 1`, `stateRoot = 118` matching `K-CARRY` pin digest). -/
def drexAttestedGate : QuorumBoundFinalityGate :=
  { turnId        := 3
    currentTier   := .attested
    faults        := 1
    stateRoot     := 118
    attestSigners := [0]
    qcSigners     := []
    qcDigest      := none
    merkleRoot    := none }

/-- Promoted `.quorum_final` gate signed by 3-of-4 validators `[0, 1, 2]` (`qcDigest = 227`). -/
def drexQuorumFinalGate : QuorumBoundFinalityGate :=
  { drexAttestedGate with
    currentTier := .quorum_final
    qcSigners   := [0, 1, 2]
    qcDigest    := some 227 }

/-- **`sovereignDrex_engine_and_bft_finality_sound`**:
1. **Oracle-Validated Sovereign Engine Step (`checkOracleTurnValidAt`, `stepSovereignEngine`)**:
   - Every admitted `stepSovereignEngine W tx = some W'` conserves all assets (`W'.ledger.totalAsset a = W.ledger.totalAsset a`),
     preserves `DragonsExchangeInvariant`, and enforces Zoe offer safety across `W'.seats`,
   - Every admitted `.executeOracleTurn cid env turn postings` necessarily passed `checkOracleTurnValidAt W turn = true`
     (guaranteeing `(admitFootprint W.store turn.readPins).isOk = true` and `turn.conservedB = true`),
   - Any stale read pin `(admitFootprint W.store turn.readPins).isOk = false` forces `checkOracleTurnValidAt W turn = false`
     and `stepSovereignEngine W (.executeOracleTurn cid env turn postings) = none`.
2. **4-Validator ($N = 4, f = 1$, Quorum $= 3$) Tier 1 & Tier 2 `SovereignFinality` (`SovereignFinality.lean`)**:
   - Disjoint fast-path `VaultTurn`s commute and collapse to identical Merkle roots (`tier1_disjoint_fast_path_commutes`),
   - `drexAttestedGate` promotes to `drexQuorumFinalGate` (`.quorum_final`, `admitsOp .quorum_final .stateWrite = true`)
     under 3-of-4 signers `[0, 1, 2]`, and any conflicting 3-of-4 quorums `blockA ≠ blockB` on `drexCommittee4`
     yield a constructive slashing receipt catching $\ge f + 1 = 2$ equivocating validators (`tier2_simplex_quorum_and_accountable_safety`). -/
theorem sovereignDrex_engine_and_bft_finality_sound
    (W W' : SovereignWorldState) (tx : SovereignTransaction)
    (hStep : stepSovereignEngine W tx = some W') :
    (∀ a : Obend.Ledger.AssetId, W'.ledger.totalAsset a = W.ledger.totalAsset a) ∧
    (DragonsExchangeInvariant W.dragons →
      DragonsExchangeInvariant W'.dragons ∧ W'.dragons.balances = W.dragons.balances) ∧
    (∀ s ∈ W'.seats, Obend.Ledger.safeAt W'.ledger s.account s.proposal = true) ∧
    (∀ cid env turn postings W_out,
      stepSovereignEngine W (.executeOracleTurn cid env turn postings) = some W_out →
      checkOracleTurnValidAt W turn = true ∧
      (admitFootprint W.store turn.readPins).isOk = true ∧
      turn.conservedB = true) ∧
    (∀ cid env turn postings,
      (admitFootprint W.store turn.readPins).isOk = false →
      checkOracleTurnValidAt W turn = false ∧
      stepSovereignEngine W (.executeOracleTurn cid env turn postings) = none) ∧
    advanceQuorumBoundGate drexAttestedGate (.formQC 227 [0, 1, 2] 118) = some drexQuorumFinalGate ∧
    (∀ (view blockA blockB : Nat) (votedA votedB : Nat → Bool),
      blockA ≠ blockB →
      3 ≤ (drexCommittee4.filter votedA).length →
      3 ≤ (drexCommittee4.filter votedB).length →
      let receipt := Obend.Consensus.Simplex.extractSlashingReceipt view blockA blockB drexCommittee4 votedA votedB
      drexQuorumFinalGate.currentTier = .quorum_final ∧
      admitsOp drexQuorumFinalGate.currentTier .stateWrite = true ∧
      2 ≤ receipt.equivocatingVoters.length ∧
      (∀ v ∈ receipt.equivocatingVoters, v ∈ drexCommittee4 ∧ votedA v = true ∧ votedB v = true)) := by
  have hAssets := sovereignEngine_step_conserves_all_assets W W' tx hStep
  have hZoe := sovereignEngine_enforces_zoe_and_mandates W W' tx hStep
  have hOracleAdmit :
      ∀ cid env turn postings W_out,
        stepSovereignEngine W (.executeOracleTurn cid env turn postings) = some W_out →
        checkOracleTurnValidAt W turn = true ∧
        (admitFootprint W.store turn.readPins).isOk = true ∧
        turn.conservedB = true := by
    intro cid env turn postings W_out hOk
    unfold stepSovereignEngine at hOk
    split at hOk
    · cases hOk
    · cases hFind : W.contracts.find? (fun c => c.contractId == cid) with
      | none => simp [hFind] at hOk
      | some c =>
        simp [hFind] at hOk
        have hGate : checkOracleTurnValidAt W turn = true := hOk.1.1.1.1.2
        have hUnf := hGate
        unfold checkOracleTurnValidAt at hUnf
        simp only [Bool.and_eq_true] at hUnf
        exact ⟨hGate, hUnf.1.1, hUnf.1.2⟩
  have hOracleRefuse :
      ∀ cid env turn postings,
        (admitFootprint W.store turn.readPins).isOk = false →
        checkOracleTurnValidAt W turn = false ∧
        stepSovereignEngine W (.executeOracleTurn cid env turn postings) = none := by
    intro cid env turn postings hStale
    refine ⟨?_, stepSovereignEngine_oracleTurn_refuses_stale_pin W cid env turn postings hStale⟩
    unfold checkOracleTurnValidAt
    rw [hStale]
    rfl
  have hGatePromote :
      advanceQuorumBoundGate drexAttestedGate (.formQC 227 [0, 1, 2] 118) = some drexQuorumFinalGate := by
    decide +kernel
  have hCommLen : drexCommittee4.length ≤ 3 * drexAttestedGate.faults + 1 := by decide +kernel
  refine ⟨hAssets.1, hAssets.2, hZoe.1, hOracleAdmit, hOracleRefuse, hGatePromote, ?_⟩
  intro view blockA blockB votedA votedB hNe hQA hQB
  have hT2 := tier2_simplex_quorum_and_accountable_safety
    drexAttestedGate drexQuorumFinalGate 227 [0, 1, 2] 118 hGatePromote
    view blockA blockB drexCommittee4 votedA votedB hNe hCommLen hQA hQB
  exact ⟨hT2.1, hT2.2.1, hT2.2.2.2.2.2.1, hT2.2.2.2.2.2.2⟩

/-- **`sovereignDrex_durable_wal_crash_recovery_sound`**:
Welds `tier1_disjoint_fast_path_commutes`, `durable_recovery_prevents_equivocation`, and
`durable_expose_once_across_crashes` (`Obend.Consensus.SovereignFinality`):
1. Disjoint `VaultTurn`s `T₁, T₂` commute on `VaultStore` and yield identical collapsed Merkle roots,
2. After crashing (`crashSimplexHost`) and replaying the durable WAL (`recoverSimplexHost`) across
   `crashes ≥ 1` failures, any previously voted view `v` rejects conflicting votes `b'` (`castVote restoredState v b' = restoredState`),
3. Once a settlement effect `n` is exposed (`hstep ... s (.expose n) = .ok s₁`), post-crash recovery
   retains `n ∈ s_rec.outbox` and refuses duplicate execution (`hstep ... s_rec (.expose n) = .error (.exposed n)`). -/
theorem sovereignDrex_durable_wal_crash_recovery_sound
    {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
    {ι P Cred Cand Tok Fact Ob W : Type}
    [DecidableEq ι] [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] [DecidableEq Tok]
    [DecidableEq Cand] [DecidableEq (Σ i, S.Op i)]
    (L : Ledger ι W Tok)
    (base : W → View Tok Fact)
    (sp : ι → Spec S Tok Fact Ob)
    (au : ι → Authority P Cred)
    (k : ι → (j : Ix) → Hole j → SlotCtl S Hole A P Fact Cand j)
    {i₀ : Ix}
    (J₀ : JCfg L S Hole A P Cand Fact Ob i₀)
    (s s₁ : DState L S Hole A P Cred Cand Fact Ob i₀)
    (n crashes : Nat) (hc : 1 ≤ crashes)
    (h_exp : hstep L base sp au k J₀ s (.expose n) = .ok s₁)
    (host : DurableSimplexHost) (v : Obend.Consensus.Simplex.View) (b' : Obend.Consensus.Simplex.Block)
    (hv_voted : ((host.journaledViews.find? (fun vr => vr.number == v)).getD { number := v }).voted = true)
    (H : Obend.Digest.HashBytes.Hash) (schema : List String) (val : StoreValuation)
    (store₀ : VaultStore) (T₁ T₂ : VaultTurn)
    (contracts : String → Option Obend.Law.CellContract)
    (formats : List Obend.Judge.Format)
    (h_disj : DisjointTurns T₁ T₂)
    (h₁ : ValidAt store₀ T₁ contracts formats)
    (h₂ : ValidAt store₀ T₂ contracts formats) :
    let restoredState : Obend.Consensus.Simplex.State :=
      { self := host.self, deadline := host.deadline, views := host.journaledViews }
    let trace : List (HEvent L S Hole A P Cred Cand Fact) := List.replicate crashes .crash ++ [.recover]
    let s_rec := runDurableTrace L base sp au k J₀ s₁ trace
    applyTurn (applyTurn store₀ T₁) T₂ = applyTurn (applyTurn store₀ T₂) T₁ ∧
    Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₁) T₂) =
      Obend.Fold.Collapse.collapseRoot H schema val (applyTurn (applyTurn store₀ T₂) T₁) ∧
    (recoverSimplexHost (crashSimplexHost host)).volatileState = some restoredState ∧
    Obend.Consensus.Simplex.castVote restoredState v b' = restoredState ∧
    n ∈ s_rec.outbox ∧
    n ∉ pending L s_rec ∧
    hstep L base sp au k J₀ s_rec (.expose n) = .error (.exposed n) := by
  have hT1 := tier1_disjoint_fast_path_commutes H schema val store₀ T₁ T₂ contracts formats h_disj h₁ h₂
  have hEqv := durable_recovery_prevents_equivocation L base sp au k J₀ s₁ crashes hc host v b' hv_voted
  have hExpOnce := durable_expose_once_across_crashes L base sp au k J₀ s s₁ n crashes hc h_exp
  exact ⟨hT1.2.2.1, hT1.2.2.2, hEqv.1, hEqv.2.2.1, hExpOnce.1, hExpOnce.2.1, hExpOnce.2.2.2⟩

/-! ## 5. Verified Synchronous Hardware Batch-Clearing & WAL Anti-Replay `RtlModule` -/

/-- Complete verified synchronous `RtlModule` (`sovereign_drex_batch_top`) for Flagship App #7:
1. Evaluates 3-of-4 BFT validator quorum (`vote_cnt >= 3`),
2. Computes exact `BatchClearing.obend` `carryPinDigest` in BOTH base (`epoch * 32 + 4`) and
   `K-CARRY`-upgraded (`(epoch * 32 + 6) + 16`) modes,
3. Enforces `pin_fresh_ok` (`in_tx_pin_digest == carry_pin_digest`) so stale-pin transactions after
   a live `K-CARRY` hot-upgrade are deterministically refused in 1 cycle,
4. Enforces `epoch_monotone_ok` (`reg_last_committed_epoch <u in_epoch_id`) in `always_ff` WAL state
   so replayed or out-of-order epochs after validator crash/recovery achieve **zero double-execution**,
5. Enforces state-bound half-edge conservation (`in_delta_debit == in_delta_credit`), Zoe offer safety,
   and `"forever"` welfare-crown preservation. -/
def sovereignDrexBatchTopRtlModule : RtlModule :=
  { name := "sovereign_drex_batch_top"
  , inputNames :=
      [ "in_lot_count"
      , "in_epoch_id"
      , "in_validator_votes"
      , "in_carry_upgrade_en"
      , "in_old_cbdc_total"
      , "in_delta_debit"
      , "in_delta_credit"
      , "in_seat_cbdc_after"
      , "in_seat_want_floor"
      , "in_forever_crown_drop_req"
      , "in_tx_pin_digest" ]
  , wires :=
      [ { wireIdx := 0,  name := "v0",
          expr := .alu .bitAnd (.inputPort 2) (.const 1#64) }
      , { wireIdx := 1,  name := "v1",
          expr := .alu .bitAnd (.alu .lshr (.inputPort 2) (.const 1#64)) (.const 1#64) }
      , { wireIdx := 2,  name := "v2",
          expr := .alu .bitAnd (.alu .lshr (.inputPort 2) (.const 2#64)) (.const 1#64) }
      , { wireIdx := 3,  name := "v3",
          expr := .alu .bitAnd (.alu .lshr (.inputPort 2) (.const 3#64)) (.const 1#64) }
      , { wireIdx := 4,  name := "vote_cnt",
          expr := .alu .add (.alu .add (.wireRef 0) (.wireRef 1))
                            (.alu .add (.wireRef 2) (.wireRef 3)) }
      , { wireIdx := 5,  name := "quorum_ok",
          expr := .mux (.alu .ult (.wireRef 4) (.const 3#64)) (.const 0#64) (.const 1#64) }
      , { wireIdx := 6,  name := "base_half_edges",
          expr := .mux (.inputPort 3) (.const 6#64) (.const 4#64) }
      , { wireIdx := 7,  name := "carry_pin_digest",
          expr := .alu .add (.alu .add (.alu .mul (.inputPort 1) (.const 32#64)) (.wireRef 6))
                            (.mux (.inputPort 3) (.const 16#64) (.const 0#64)) }
      , { wireIdx := 8,  name := "epoch_monotone_ok",
          expr := .alu .ult (.regRead 1) (.inputPort 1) }
      , { wireIdx := 9,  name := "pin_fresh_ok",
          expr := .alu .eq (.inputPort 10) (.wireRef 7) }
      , { wireIdx := 10, name := "half_edge_balanced",
          expr := .alu .eq (.inputPort 5) (.inputPort 6) }
      , { wireIdx := 11, name := "zoe_offer_safe",
          expr := .mux (.alu .ult (.inputPort 7) (.inputPort 8)) (.const 0#64) (.const 1#64) }
      , { wireIdx := 12, name := "crown_preserved",
          expr := .alu .eq (.inputPort 9) (.const 0#64) }
      , { wireIdx := 13, name := "guards_a",
          expr := .alu .bitAnd (.alu .bitAnd (.wireRef 5) (.wireRef 8)) (.wireRef 9) }
      , { wireIdx := 14, name := "guards_b",
          expr := .alu .bitAnd (.alu .bitAnd (.wireRef 10) (.wireRef 11)) (.wireRef 12) }
      , { wireIdx := 15, name := "turn_ok",
          expr := .alu .bitAnd (.wireRef 13) (.wireRef 14) }
      , { wireIdx := 16, name := "new_cbdc_total",
          expr := .mux (.wireRef 15)
                       (.alu .sub (.alu .add (.inputPort 4) (.inputPort 6)) (.inputPort 5))
                       (.inputPort 4) }
      ]
  , regs :=
      [ { regIdx := 0, name := "reg_wal_committed_count", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .mux (.wireRef 15) (.alu .add (.regRead 0) (.const 1#64)) (.regRead 0) }
      , { regIdx := 1, name := "reg_last_committed_epoch", domain := .coreClk,
          resetKind := .syncReset 0#64, isSynchronizer := false,
          nextExpr := .mux (.wireRef 15) (.inputPort 1) (.regRead 1) }
      ]
  , outputs :=
      [ { name := "out_validator_quorum",        expr := .const 3#64 }
      , { name := "out_vote_count",              expr := .wireRef 4 }
      , { name := "out_quorum_reached",          expr := .wireRef 5 }
      , { name := "out_protected_welfare_crown", expr := .const 1000#64 }
      , { name := "out_settled_cbdc_liquidity",
          expr := .mux (.inputPort 3) (.const 125000#64) (.const 100000#64) }
      , { name := "out_batch_settlement_cbdc",
          expr := .alu .add (.alu .mul (.inputPort 0) (.const 500#64)) (.const 1000#64) }
      , { name := "out_finality_commit_tag",
          expr := .alu .add (.alu .add (.alu .mul (.inputPort 1) (.const 64#64)) (.const 3#64))
                            (.mux (.inputPort 3) (.const 32#64) (.const 0#64)) }
      , { name := "out_carry_pin_digest",        expr := .wireRef 7 }
      , { name := "out_pin_fresh_ok",            expr := .wireRef 9 }
      , { name := "out_epoch_monotone_ok",       expr := .wireRef 8 }
      , { name := "out_new_cbdc_total",          expr := .wireRef 16 }
      , { name := "out_turn_admitted",           expr := .wireRef 15 }
      , { name := "out_wal_committed_count",     expr := .regRead 0 }
      , { name := "out_last_committed_epoch",    expr := .regRead 1 }
      ]
  }

/-- Input port environment builder for `sovereignDrexBatchTopRtlModule`. -/
def mkDrexRtlInputs
    (lots epoch votes carryEn oldTotal debit credit seatAfter wantFloor dropCrown txPin : Nat) :
    Nat → BitVec 64
  | 0  => BitVec.ofNat 64 lots
  | 1  => BitVec.ofNat 64 epoch
  | 2  => BitVec.ofNat 64 votes
  | 3  => BitVec.ofNat 64 carryEn
  | 4  => BitVec.ofNat 64 oldTotal
  | 5  => BitVec.ofNat 64 debit
  | 6  => BitVec.ofNat 64 credit
  | 7  => BitVec.ofNat 64 seatAfter
  | 8  => BitVec.ofNat 64 wantFloor
  | 9  => BitVec.ofNat 64 dropCrown
  | 10 => BitVec.ofNat 64 txPin
  | _  => 0#64

/-- **`sovereignDrexBatchTopRtlModule_verified`**:
Kernel-checked (`decide +kernel`) verification of `sovereignDrexBatchTopRtlModule`:
1. Passes `checkRtlModule = true` and `checkBelNetlistValid (synthesizeModuleToBels ...) = true`,
2. Base Epoch 3 (`carryEn = 0`) computes `out_carry_pin_digest = 100#64` (`3 * 32 + 4`, matching
   `BatchClearing.baseBatchClearing().carryPinDigest(3)`) and admits the turn (`st1 = [1, 3]`),
3. Replaying already-committed Epoch 3 (`epoch = 3`) is **refused** by the monotone WAL guard
   (`out_epoch_monotone_ok = 0#64`, `out_turn_admitted = 0#64`, `st2 0 = 1#64` — zero double-execution!),
4. After live `K-CARRY` upgrade (`carryEn = 1`) at Epoch 5, a stale-pin transaction carrying old base
   pin `164` (`5 * 32 + 4`) is **refused** (`out_pin_fresh_ok = 0#64`, `out_turn_admitted = 0#64`),
   whereas a fresh-pin transaction carrying `182` (`(5 * 32 + 6) + 16`) is **admitted** (`st4 = [2, 5]`). -/
theorem sovereignDrexBatchTopRtlModule_verified :
    checkRtlModule sovereignDrexBatchTopRtlModule = true ∧
    checkBelNetlistValid (synthesizeModuleToBels sovereignDrexBatchTopRtlModule) = true ∧
    (let st0 : Nat → BitVec 64 := fun _ => 0#64
     let inEp3Base := mkDrexRtlInputs 8 3 0b0111 0 1000000 50000 50000 95000 75000 0 100
     let outEp3Base := evalModuleOutputs sovereignDrexBatchTopRtlModule inEp3Base st0
     let st1 := stepModuleRegs sovereignDrexBatchTopRtlModule false inEp3Base st0
     let outReplay := evalModuleOutputs sovereignDrexBatchTopRtlModule inEp3Base st1
     let st2 := stepModuleRegs sovereignDrexBatchTopRtlModule false inEp3Base st1
     let inEp5Stale := mkDrexRtlInputs 12 5 0b1111 1 1000000 50000 50000 95000 75000 0 164
     let outStale := evalModuleOutputs sovereignDrexBatchTopRtlModule inEp5Stale st2
     let st3 := stepModuleRegs sovereignDrexBatchTopRtlModule false inEp5Stale st2
     let inEp5Fresh := mkDrexRtlInputs 12 5 0b1111 1 1000000 50000 50000 95000 75000 0 182
     let outFresh := evalModuleOutputs sovereignDrexBatchTopRtlModule inEp5Fresh st3
     let st4 := stepModuleRegs sovereignDrexBatchTopRtlModule false inEp5Fresh st3
     outEp3Base.lookup "out_carry_pin_digest" = some 100#64 ∧
     outEp3Base.lookup "out_turn_admitted" = some 1#64 ∧
     st1 0 = 1#64 ∧ st1 1 = 3#64 ∧
     outReplay.lookup "out_epoch_monotone_ok" = some 0#64 ∧
     outReplay.lookup "out_turn_admitted" = some 0#64 ∧
     st2 0 = 1#64 ∧ st2 1 = 3#64 ∧
     outStale.lookup "out_carry_pin_digest" = some 182#64 ∧
     outStale.lookup "out_pin_fresh_ok" = some 0#64 ∧
     outStale.lookup "out_turn_admitted" = some 0#64 ∧
     st3 0 = 1#64 ∧ st3 1 = 3#64 ∧
     outFresh.lookup "out_pin_fresh_ok" = some 1#64 ∧
     outFresh.lookup "out_turn_admitted" = some 1#64 ∧
     st4 0 = 2#64 ∧ st4 1 = 5#64) := by
  decide +kernel

/-! ## 6. `#tooth` Mutation-Killing Guards -/

def brokenSafetyVal : Term := .nat 0

#tooth sovereignDrex_all_accepted_and_claims_hold by mutation
  SovereignDrexSeat.institutionalSafetyAt80_val := brokenSafetyVal

def brokenDrexRtlModule : RtlModule :=
  { name := "sovereign_drex_batch_top"
  , inputNames := ["in_lot_count"]
  , wires := []
  , regs := []
  , outputs := [{ name := "out_turn_admitted", expr := .const 1#64 }] }

#tooth sovereignDrexBatchTopRtlModule_verified by mutation
  sovereignDrexBatchTopRtlModule := brokenDrexRtlModule

def brokenDrexCommittee4 : List Nat := [0, 1, 2, 3, 4, 5]

#tooth sovereignDrex_engine_and_bft_finality_sound by mutation
  drexCommittee4 := brokenDrexCommittee4

end Obend.Apps.SovereignDrex
end

