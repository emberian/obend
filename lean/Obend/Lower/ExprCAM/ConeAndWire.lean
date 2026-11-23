module
/-
# Obend.Lower.ExprCAM.ConeAndWire — Live Declaration-Cone Ingestion, Fast CAM Interning & `OBCAMv1` Wire Protocol

Implements `§6` (live `Lean.ConstantInfo` / `KInductDecl` / `KRecRule` dependency-cone extraction and
`Std.HashMap`-backed `FastHwExprCAM` interning) and `§8` (88-bit `BitVec 88` `PackedNodeWord` packing
and the 7-section `OBCAMv1` binary wire protocol with exact round-trip theorems).
-/
public import Std.Data.HashMap
public import Std.Data.HashSet
public import Std.Tactic.BVDecide
public import Obend.Lower.LeanKernel
public import Obend.Lower.Proofs.SiliconKernel
public import Obend.Lower.ExprCAM.HwTypes
public section

namespace Obend.Lower.ExprCAM
open Obend.Core.Term
open Obend.Leaf
open Obend.Lower
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
open Obend.Lower.Proofs.SiliconKernel
open Obend.Hardware.HDL
open Obend.Hardware.Compiler
open Obend.Hardware.ReductionMachine
set_option autoImplicit false

/-! ## 6. Live Declaration-Cone Ingestion, `Std.HashMap` Fast CAM Interning & Recursor Extraction (`WS 24`) -/

/-- Structural hash on `KName` for `Std.HashSet` / `Std.HashMap` indexing. -/
def hashKName : KName → UInt64
  | .anonymous => 17
  | .str p s   => mixHash 31 (mixHash (hashKName p) (hash s))
  | .num p k   => mixHash 47 (mixHash (hashKName p) (hash k))

instance : Hashable KName := ⟨hashKName⟩

/-- Structural hash on `KLevel`. -/
def hashKLevel : KLevel → UInt64
  | .zero      => 11
  | .succ u    => mixHash 23 (hashKLevel u)
  | .max u v   => mixHash 37 (mixHash (hashKLevel u) (hashKLevel v))
  | .imax u v  => mixHash 53 (mixHash (hashKLevel u) (hashKLevel v))
  | .param n   => mixHash 71 (hashKName n)

instance : Hashable KLevel := ⟨hashKLevel⟩

instance : Hashable KLiteral where
  hash
    | .natVal n => mixHash 13 (hash n)
    | .strVal s => mixHash 29 (hash s)

instance : Hashable HwCamSymbolEntry where
  hash
    | .sortEntry u     => mixHash 3 (hash u)
    | .constEntry n us => mixHash 5 (mixHash (hash n) (hash us))
    | .litEntry l      => mixHash 7 (hash l)
    | .projEntry s idx => mixHash 11 (mixHash (hash s) (hash idx))

instance : Hashable PackedNodeWord where
  hash w :=
    mixHash (hash w.tag)
      (mixHash (hash w.h0)
        (mixHash (hash w.h1)
          (mixHash (hash w.h2)
            (mixHash (hash w.symIdx)
              (mixHash (hash w.hasLooseBVar)
                (mixHash (hash w.hasFVar)
                  (mixHash (hash w.hasMVar) (hash w.maxLooseBVar))))))))

/-- Extract a self-hosted `KConstInfo` from a live host `Lean.ConstantInfo` via `fromLeanName` and `fromLeanExpr`.
Note: `.opaqueInfo` translates `val.value` into `.thmInfo` so `sorryAx` or ill-typed opaque bodies
are checked by the kernel while remaining opaque to $\delta$-unfolding during WHNF. -/
def extractLeanConstInfo? : Lean.ConstantInfo → Option KConstInfo
  | .axiomInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)
  | .defnInfo val => do
    let ty ← fromLeanExpr val.type
    let v  ← fromLeanExpr val.value
    pure (.defnInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty v)
  | .thmInfo val => do
    let ty ← fromLeanExpr val.type
    let v  ← fromLeanExpr val.value
    pure (.thmInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty v)
  | .inductInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.inductInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)
  | .ctorInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.ctorInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty (fromLeanName val.induct))
  | .recInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)
  | .opaqueInfo val => do
    let ty ← fromLeanExpr val.type
    let v  ← fromLeanExpr val.value
    pure (.thmInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty v)
  | .quotInfo val => do
    let ty ← fromLeanExpr val.type
    pure (.axiomInfo (fromLeanName val.name) (val.levelParams.map fromLeanName) ty)

/-- Canonical `Lean.Expr → Option KExpr` translator (`fromLeanExprWithProjShift`):
Preserves Lean's 0-based structure field index `i` on `.proj s i e` without pre-shifting by `numParams`
(eliminating the `.proj` double-offset against `LeanKernel.kernelWhnf` and `LeanKernel.inferProjFieldType?`,
which apply `env.inductDecls`'s `numParams` offset once), and maps `.mvar` to first-class `KExpr.mvar`. -/
def fromLeanExprWithProjShift (_numParamsOf : Lean.Name → Nat := fun _ => 0) : Lean.Expr → Option KExpr :=
  fromLeanExpr

/-- Environment-aware `KConstInfo` extractor (`extractLeanConstInfoWith?`). -/
def extractLeanConstInfoWith?
    (_findConst? : Lean.Name → Option Lean.ConstantInfo)
    (info : Lean.ConstantInfo) : Option KConstInfo :=
  extractLeanConstInfo? info

/-- Extract the list of universe-polymorphic `KRecRule` $\iota$-reduction rules from a live host
`Lean.RecursorVal` (`extractLeanRecRules`), populating `levelParams := rval.levelParams.map fromLeanName`,
`numPrefixArgs := rval.numParams + rval.numMotives + rval.numMinors`, `numFields := rule.nfields`,
and translating `rule.rhs` via `fromLeanExpr` (stripping `.mdata` annotations transparently). -/
def extractLeanRecRules (rval : Lean.RecursorVal) : Option (List KRecRule) :=
  rval.rules.mapM fun rule => do
    let rhsExpr ← fromLeanExpr rule.rhs
    pure
      { recName       := fromLeanName rval.name
      , ctorName      := fromLeanName rule.ctor
      , levelParams   := rval.levelParams.map fromLeanName
      , numPrefixArgs := rval.numParams + rval.numMotives + rval.numMinors
      , numFields     := rule.nfields
      , rhs           := rhsExpr }

/-- Environment-aware `KRecRule` extractor (`extractLeanRecRulesWith`). -/
def extractLeanRecRulesWith
    (_findConst? : Lean.Name → Option Lean.ConstantInfo)
    (rval : Lean.RecursorVal) : Option (List KRecRule) :=
  extractLeanRecRules rval

/-- Extract a `KInductDecl` (including `numParams`, `numIndices`, constructors, and recursor rules)
from a live host `Lean.InductiveVal` so parameterized `.proj` reduction and type inference have
exact `numParams` metadata in `KEnv.inductDecls`. -/
def extractLeanInductDeclWith?
    (findConst? : Lean.Name → Option Lean.ConstantInfo)
    (iv : Lean.InductiveVal) : Option KInductDecl := do
  let ty ← fromLeanExpr iv.type
  let ctors ← iv.ctors.mapM fun cName => do
    match findConst? cName with
    | some (.ctorInfo cv) =>
      let cTy ← fromLeanExpr cv.type
      pure (fromLeanName cv.name, cTy, cv.numFields)
    | _ => none
  let recRules :=
    match findConst? (.str iv.name "rec") with
    | some (.recInfo rv) => (extractLeanRecRules rv).getD []
    | _ => []
  pure
    { name        := fromLeanName iv.name
    , levelParams := iv.levelParams.map fromLeanName
    , numParams   := iv.numParams
    , numIndices  := iv.numIndices
    , type        := ty
    , ctors       := ctors
    , recRules    := recRules }

/-- Collect all `Lean.Name` constants referenced inside a `Lean.Expr` (stripping `.mdata`). -/
def collectLeanExprConsts : Lean.Expr → List Lean.Name
  | .const n _       => [n]
  | .app f a         => collectLeanExprConsts f ++ collectLeanExprConsts a
  | .lam _ d b _     => collectLeanExprConsts d ++ collectLeanExprConsts b
  | .forallE _ d b _ => collectLeanExprConsts d ++ collectLeanExprConsts b
  | .letE _ t v b _  => collectLeanExprConsts t ++ collectLeanExprConsts v ++ collectLeanExprConsts b
  | .mdata _ e       => collectLeanExprConsts e
  | .proj s _ e      => s :: collectLeanExprConsts e
  | _                => []

/-- Collect all immediate constant dependencies of a `Lean.ConstantInfo`, including inductive
constructors, recursor `.str val.name "rec"`, and recursor rule RHS constants. -/
def collectConstInfoDeps (info : Lean.ConstantInfo) : List Lean.Name :=
  match info with
  | .defnInfo val =>
    collectLeanExprConsts val.type ++ collectLeanExprConsts val.value
  | .thmInfo val =>
    collectLeanExprConsts val.type ++ collectLeanExprConsts val.value
  | .inductInfo val =>
    [.str val.name "rec"] ++ val.ctors ++ collectLeanExprConsts val.type
  | .ctorInfo val =>
    [val.induct, .str val.induct "rec"] ++ collectLeanExprConsts val.type
  | .recInfo val =>
    val.all ++ (val.rules.flatMap fun r => r.ctor :: collectLeanExprConsts r.rhs) ++ collectLeanExprConsts val.type
  | .axiomInfo val =>
    collectLeanExprConsts val.type
  | .opaqueInfo val =>
    collectLeanExprConsts val.type ++ collectLeanExprConsts val.value
  | .quotInfo val =>
    collectLeanExprConsts val.type

/-- $O(1)$ `Std.HashSet`-backed worklist insertion so every BFS step in `extractEnvConeAux`
processes a distinct declaration without $O(N^2)$ list scans. -/
def enqueueUnvisitedDepsFast (seen : Std.HashSet KName) (queue : List Lean.Name) :
    List Lean.Name → Std.HashSet KName × List Lean.Name
  | [] => (seen, queue)
  | d :: ds =>
    let kd := fromLeanName d
    if seen.contains kd then
      enqueueUnvisitedDepsFast seen queue ds
    else
      enqueueUnvisitedDepsFast (seen.insert kd) (queue ++ [d]) ds

/-- Bounded BFS helper extracting all transitive `KConstInfo` declarations, `KRecRule` recursor
rules, and `KInductDecl` inductive metadata reachable from a `Std.HashSet`-deduplicated worklist. -/
def extractEnvConeAux
    (findConst? : Lean.Name → Option Lean.ConstantInfo) :
    Nat → List Lean.Name → Std.HashSet KName →
    Array KConstInfo → Array KRecRule → Array KInductDecl →
    Array KConstInfo × Array KRecRule × Array KInductDecl
  | 0, _, _, accConsts, accRules, accInducts => (accConsts, accRules, accInducts)
  | _ + 1, [], _, accConsts, accRules, accInducts => (accConsts, accRules, accInducts)
  | fuel + 1, n :: rest, seen, accConsts, accRules, accInducts =>
    match findConst? n with
    | none =>
      extractEnvConeAux findConst? fuel rest seen accConsts accRules accInducts
    | some info =>
      let accConsts' :=
        match extractLeanConstInfo? info with
        | some kc => accConsts.push kc
        | none    => accConsts
      let accRules' :=
        match info with
        | .recInfo rval =>
          match extractLeanRecRules rval with
          | some rs => accRules ++ rs.toArray
          | none    => accRules
        | _ => accRules
      let accInducts' :=
        match info with
        | .inductInfo iv =>
          match extractLeanInductDeclWith? findConst? iv with
          | some idcl => accInducts.push idcl
          | none      => accInducts
        | _ => accInducts
      let deps := collectConstInfoDeps info
      let (seen', nextQueue) := enqueueUnvisitedDepsFast seen rest deps
      extractEnvConeAux findConst? fuel nextQueue seen' accConsts' accRules' accInducts'

/-- Extract a self-contained `(KEnv × KConstInfo)` transitive dependency cone rooted at `rootName`
using a lookup function `findConst? : Lean.Name → Option Lean.ConstantInfo`. -/
def extractEnvConeWith
    (findConst? : Lean.Name → Option Lean.ConstantInfo)
    (rootName : Lean.Name)
    (fuel : Nat) : Option (KEnv × KConstInfo) := do
  let rootInfo ← findConst? rootName
  let rootDecl ← extractLeanConstInfo? rootInfo
  let initSeen := (Std.HashSet.emptyWithCapacity 64).insert (fromLeanName rootName)
  let (consts, recRules, inductDecls) :=
    extractEnvConeAux findConst? fuel [rootName] initSeen #[] #[] #[]
  pure ({ constants   := consts.toList
        , recRules    := recRules.toList
        , inductDecls := inductDecls.toList }, rootDecl)

/-- Extract a self-contained `(KEnv × KConstInfo)` transitive dependency cone rooted at `rootName`
directly from a live host `Lean.Environment` (`extractLeanEnvCone`). -/
def extractLeanEnvCone
    (env : Lean.Environment)
    (rootName : Lean.Name)
    (fuel : Nat) : Option (KEnv × KConstInfo) :=
  extractEnvConeWith env.find? rootName fuel

/-- Construct and intern a `.sort u` (`tag = 2`) node in `HwExprCAM`. -/
@[expose] def mkHwCamSort (u : KLevel) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let (sIdx, cam1) := allocPackedSymbol (.sortEntry u) cam
  allocPackedNode { tag := 2, h0 := 0, h1 := 0, symIdx := sIdx } cam1

/-- Construct and intern a `.const n us` (`tag = 3`) node in `HwExprCAM`. -/
@[expose] def mkHwCamConst (n : KName) (us : List KLevel) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let (sIdx, cam1) := allocPackedSymbol (.constEntry n us) cam
  allocPackedNode { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx } cam1

/-- Construct and intern a `.lit l` (`tag = 8`) node in `HwExprCAM`. -/
@[expose] def mkHwCamLit (l : KLiteral) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let (sIdx, cam1) := allocPackedSymbol (.litEntry l) cam
  allocPackedNode { tag := 8, h0 := 0, h1 := 0, symIdx := sIdx } cam1

/-- Pure handle-level universe level parameter instantiation (`hwCamInstantiateLevelParams`) over
`HwExprCAM` (`cam.nodes` and `cam.symbols`) with zero `KExpr` AST reconstruction! -/
@[expose] def hwCamInstantiateLevelParams :
    Nat → List (KName × KLevel) → Nat → HwExprCAM → Nat × HwExprCAM
  | 0, _, h, cam => (h, cam)
  | fuel + 1, subst, h, cam =>
    if subst.isEmpty then
      (h, cam)
    else
      match cam.nodes[h]? with
      | none => (h, cam)
      | some w =>
        if w.tag == 0 || w.tag == 1 || w.tag == 8 || w.tag == 10 then
          (h, cam)
        else if w.tag == 2 then
          match cam.symbols[w.symIdx]? with
          | some (.sortEntry u) =>
            let u' := KLevel.substParams subst u
            if u' == u then (h, cam) else mkHwCamSort u' cam
          | _ => (h, cam)
        else if w.tag == 3 then
          match cam.symbols[w.symIdx]? with
          | some (.constEntry n us) =>
            let us' := us.map (KLevel.substParams subst)
            if us' == us then (h, cam) else mkHwCamConst n us' cam
          | _ => (h, cam)
        else if w.tag == 4 then
          let (hf', cam1) := hwCamInstantiateLevelParams fuel subst w.h0 cam
          let (ha', cam2) := hwCamInstantiateLevelParams fuel subst w.h1 cam1
          if hf' == w.h0 && ha' == w.h1 then (h, cam2) else mkHwCamApp hf' ha' cam2
        else if w.tag == 5 || w.tag == 6 then
          let (hd', cam1) := hwCamInstantiateLevelParams fuel subst w.h0 cam
          let (hb', cam2) := hwCamInstantiateLevelParams fuel subst w.h1 cam1
          if hd' == w.h0 && hb' == w.h1 then (h, cam2) else mkHwCamBinder w.tag hd' hb' cam2
        else if w.tag == 7 then
          let (ht', cam1) := hwCamInstantiateLevelParams fuel subst w.h0 cam
          let (hv', cam2) := hwCamInstantiateLevelParams fuel subst w.h1 cam1
          let (hb', cam3) := hwCamInstantiateLevelParams fuel subst w.h2 cam2
          if ht' == w.h0 && hv' == w.h1 && hb' == w.h2 then (h, cam3)
          else mkHwCamLetE ht' hv' hb' cam3
        else if w.tag == 9 then
          let (hs', cam1) := hwCamInstantiateLevelParams fuel subst w.h0 cam
          if hs' == w.h0 then (h, cam1) else mkHwCamProj hs' w.symIdx cam1
        else
          (h, cam)

/-- Intern a `KConstInfo` declaration into `HwExprCAM` (`consts`, `nodes`, `symbols`).
Only `.defnInfo` populates `valHandle? := some valH` for Zone-1 $\delta$-unfolding; `.thmInfo`
remains proof-irrelevant/opaque to WHNF unfolding matching Lean 4 kernel semantics. -/
def internKConstInfoToHwExprCAM (c : KConstInfo) (cam : HwExprCAM) : HwExprCAM :=
  let (symIdx, cam1) := allocPackedSymbol (.constEntry c.name (c.levelParams.map KLevel.param)) cam
  let (tyH, cam2) := internToHwExprCAM c.type cam1
  match c with
  | .defnInfo _ _ _ val =>
    let (valH, cam3) := internToHwExprCAM val cam2
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH, valHandle? := some valH }
    { cam3 with consts := cam3.consts ++ [entry] }
  | .thmInfo _ _ _ val =>
    let (_, cam3) := internToHwExprCAM val cam2
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH, valHandle? := none }
    { cam3 with consts := cam3.consts ++ [entry] }
  | .ctorInfo _ _ _ indName =>
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH, isCtor := true, inductName? := some indName }
    { cam2 with consts := cam2.consts ++ [entry] }
  | _ =>
    let entry : HwCamConstEntry :=
      { name := c.name, symIdx := symIdx, typeHandle := tyH }
    { cam2 with consts := cam2.consts ++ [entry] }

/-- Intern a `KRecRule` $\iota$-reduction rule into `HwExprCAM` (`recRules`, `recLevelParams`, `nodes`, `symbols`). -/
def internKRecRuleToHwExprCAM (r : KRecRule) (cam : HwExprCAM) : HwExprCAM :=
  let (rhsH, cam1) := internToHwExprCAM r.rhs cam
  let entry : HwCamRecRuleEntry :=
    { recName   := r.recName
    , ctorName  := r.ctorName
    , numParams := r.numPrefixArgs
    , numFields := r.numFields
    , rhsHandle := rhsH }
  let recLP :=
    if r.levelParams.isEmpty || cam1.recLevelParams.any (fun p => p.1 == r.recName) then
      cam1.recLevelParams
    else
      cam1.recLevelParams ++ [(r.recName, r.levelParams)]
  { cam1 with recRules := cam1.recRules ++ [entry], recLevelParams := recLP }

/-- Intern an entire `KEnv` declaration cone (`constants`, `recRules`, and `inductDecls`) into `HwExprCAM`. -/
def internKEnvConeToHwExprCAM (env : KEnv) (cam : HwExprCAM) : HwExprCAM :=
  let cam1 := env.constants.foldl (fun acc c => internKConstInfoToHwExprCAM c acc) cam
  let cam2 := env.recRules.foldl (fun acc r => internKRecRuleToHwExprCAM r acc) cam1
  let indParams := env.inductDecls.foldl
    (fun acc d => if acc.any (fun p => p.1 == d.name) then acc else acc ++ [(d.name, d.numParams)])
    cam2.inductNumParams
  { cam2 with inductNumParams := indParams }

/-- $O(1)$ `Std.HashMap`-indexed hardware CAM builder (`FastHwExprCAM`) for linear-time interning of
large live Lean 4 declaration cones without $O(|DAG|^2)$ list scans. -/
structure FastHwExprCAM where
  nodes           : Array PackedNodeWord := #[]
  symbols         : Array HwCamSymbolEntry := #[]
  consts          : Array HwCamConstEntry := #[]
  recRules        : Array HwCamRecRuleEntry := #[]
  inductNumParams : List (KName × Nat) := []
  recLevelParams  : List (KName × List KName) := []
  nodeIndex       : Std.HashMap PackedNodeWord Nat := {}
  symIndex        : Std.HashMap HwCamSymbolEntry Nat := {}

@[expose] def FastHwExprCAM.empty : FastHwExprCAM := {}

@[expose] def FastHwExprCAM.toHwExprCAM (fc : FastHwExprCAM) : HwExprCAM :=
  { nodes           := fc.nodes.toList
  , symbols         := fc.symbols.toList
  , consts          := fc.consts.toList
  , recRules        := fc.recRules.toList
  , inductNumParams := fc.inductNumParams
  , recLevelParams  := fc.recLevelParams }

@[expose] def allocFastSymbol (s : HwCamSymbolEntry) (fc : FastHwExprCAM) : Nat × FastHwExprCAM :=
  match fc.symIndex[s]? with
  | some idx => (idx, fc)
  | none =>
    let idx := fc.symbols.size
    (idx, { fc with symbols := fc.symbols.push s, symIndex := fc.symIndex.insert s idx })

@[expose] def allocFastNode (w : PackedNodeWord) (fc : FastHwExprCAM) : Nat × FastHwExprCAM :=
  match fc.nodeIndex[w]? with
  | some h => (h, fc)
  | none =>
    let h := fc.nodes.size
    (h, { fc with nodes := fc.nodes.push w, nodeIndex := fc.nodeIndex.insert w h })

def getFastNode (fc : FastHwExprCAM) (h : Nat) : PackedNodeWord :=
  fc.nodes[h]?.getD { tag := 99, h0 := 0, h1 := 0 }

/-- Intern a `KExpr` into `FastHwExprCAM` in $O(|e|)$ amortized hash-table operations. -/
@[expose] def internToFastHwExprCAM : KExpr → FastHwExprCAM → Nat × FastHwExprCAM
  | .bvar idx, fc =>
    allocFastNode { tag := 0, h0 := idx, h1 := 0, hasLooseBVar := true, maxLooseBVar := idx + 1 } fc
  | .fvar id, fc =>
    allocFastNode { tag := 1, h0 := id, h1 := 0, hasFVar := true, hasMVar := false } fc
  | .mvar id, fc =>
    allocFastNode { tag := 10, h0 := id, h1 := 0, hasFVar := false, hasMVar := true } fc
  | .sort u, fc =>
    let (sIdx, fc1) := allocFastSymbol (.sortEntry u) fc
    allocFastNode { tag := 2, h0 := 0, h1 := 0, symIdx := sIdx } fc1
  | .const n us, fc =>
    let (sIdx, fc1) := allocFastSymbol (.constEntry n us) fc
    allocFastNode { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx } fc1
  | .app f a, fc =>
    let (hf, fc1) := internToFastHwExprCAM f fc
    let (ha, fc2) := internToFastHwExprCAM a fc1
    let wf := getFastNode fc2 hf
    let wa := getFastNode fc2 ha
    let maxB := Nat.max wf.maxLooseBVar wa.maxLooseBVar
    allocFastNode
      { tag := 4, h0 := hf, h1 := ha, hasLooseBVar := decide (maxB > 0)
      , hasFVar := wf.hasFVar || wa.hasFVar, hasMVar := wf.hasMVar || wa.hasMVar
      , maxLooseBVar := maxB } fc2
  | .lam d b, fc =>
    let (hd, fc1) := internToFastHwExprCAM d fc
    let (hb, fc2) := internToFastHwExprCAM b fc1
    let wd := getFastNode fc2 hd
    let wb := getFastNode fc2 hb
    let maxB := Nat.max wd.maxLooseBVar (wb.maxLooseBVar - 1)
    allocFastNode
      { tag := 5, h0 := hd, h1 := hb, hasLooseBVar := decide (maxB > 0)
      , hasFVar := wd.hasFVar || wb.hasFVar, hasMVar := wd.hasMVar || wb.hasMVar
      , maxLooseBVar := maxB } fc2
  | .forallE d b, fc =>
    let (hd, fc1) := internToFastHwExprCAM d fc
    let (hb, fc2) := internToFastHwExprCAM b fc1
    let wd := getFastNode fc2 hd
    let wb := getFastNode fc2 hb
    let maxB := Nat.max wd.maxLooseBVar (wb.maxLooseBVar - 1)
    allocFastNode
      { tag := 6, h0 := hd, h1 := hb, hasLooseBVar := decide (maxB > 0)
      , hasFVar := wd.hasFVar || wb.hasFVar, hasMVar := wd.hasMVar || wb.hasMVar
      , maxLooseBVar := maxB } fc2
  | .letE t v b, fc =>
    let (ht, fc1) := internToFastHwExprCAM t fc
    let (hv, fc2) := internToFastHwExprCAM v fc1
    let (hb, fc3) := internToFastHwExprCAM b fc2
    let wt := getFastNode fc3 ht
    let wv := getFastNode fc3 hv
    let wb := getFastNode fc3 hb
    let maxB := Nat.max (Nat.max wt.maxLooseBVar wv.maxLooseBVar) (wb.maxLooseBVar - 1)
    allocFastNode
      { tag := 7, h0 := ht, h1 := hv, h2 := hb, hasLooseBVar := decide (maxB > 0)
      , hasFVar := wt.hasFVar || wv.hasFVar || wb.hasFVar
      , hasMVar := wt.hasMVar || wv.hasMVar || wb.hasMVar
      , maxLooseBVar := maxB } fc3
  | .lit l, fc =>
    let (sIdx, fc1) := allocFastSymbol (.litEntry l) fc
    allocFastNode { tag := 8, h0 := 0, h1 := 0, symIdx := sIdx } fc1
  | .proj structName idx s, fc =>
    let (hs, fc1) := internToFastHwExprCAM s fc
    let (sIdx, fc2) := allocFastSymbol (.projEntry structName idx) fc1
    let ws := getFastNode fc2 hs
    allocFastNode
      { tag := 9, h0 := hs, h1 := 0, symIdx := sIdx, hasLooseBVar := decide (ws.maxLooseBVar > 0)
      , hasFVar := ws.hasFVar, hasMVar := ws.hasMVar, maxLooseBVar := ws.maxLooseBVar } fc2

/-- Intern an entire `KEnv` cone in $O(|DAG|)$ via `FastHwExprCAM` and convert to `HwExprCAM`. -/
@[expose] def internKEnvConeFast (env : KEnv) : HwExprCAM :=
  let fc1 := env.constants.foldl
    (fun fc c =>
      let (symIdx, fcA) := allocFastSymbol (.constEntry c.name (c.levelParams.map KLevel.param)) fc
      let (tyH, fcB) := internToFastHwExprCAM c.type fcA
      match c with
      | .defnInfo _ _ _ val =>
        let (valH, fcC) := internToFastHwExprCAM val fcB
        { fcC with consts := fcC.consts.push { name := c.name, symIdx := symIdx, typeHandle := tyH, valHandle? := some valH } }
      | .thmInfo _ _ _ val =>
        let (_, fcC) := internToFastHwExprCAM val fcB
        { fcC with consts := fcC.consts.push { name := c.name, symIdx := symIdx, typeHandle := tyH, valHandle? := none } }
      | .ctorInfo _ _ _ indName =>
        { fcB with consts := fcB.consts.push { name := c.name, symIdx := symIdx, typeHandle := tyH, isCtor := true, inductName? := some indName } }
      | _ =>
        { fcB with consts := fcB.consts.push { name := c.name, symIdx := symIdx, typeHandle := tyH } })
    FastHwExprCAM.empty
  let fc2 := env.recRules.foldl
    (fun fc r =>
      let (rhsH, fcA) := internToFastHwExprCAM r.rhs fc
      let entry : HwCamRecRuleEntry :=
        { recName := r.recName, ctorName := r.ctorName, numParams := r.numPrefixArgs, numFields := r.numFields, rhsHandle := rhsH }
      let recLP :=
        if r.levelParams.isEmpty || fcA.recLevelParams.any (fun p => p.1 == r.recName) then fcA.recLevelParams
        else fcA.recLevelParams ++ [(r.recName, r.levelParams)]
      { fcA with recRules := fcA.recRules.push entry, recLevelParams := recLP })
    fc1
  let indParams := env.inductDecls.foldl
    (fun acc d => if acc.any (fun p => p.1 == d.name) then acc else acc ++ [(d.name, d.numParams)])
    []
  { fc2 with inductNumParams := indParams }.toHwExprCAM

/-- Sample host `Lean.ConstantInfo` declaration (`Lean.Declaration.defnDecl` for `liveIdNat : Nat → Nat := λ x : Nat => x`). -/
def sampleLiveLeanDefnInfo : Lean.ConstantInfo :=
  let natExpr : Lean.Expr := .const (.str .anonymous "Nat") []
  let arrowType : Lean.Expr := .forallE (.str .anonymous "x") natExpr natExpr .default
  let lamVal : Lean.Expr := .lam (.str .anonymous "x") natExpr (.bvar 0) .default
  .defnInfo
    { name        := .str .anonymous "liveIdNat"
    , levelParams := []
    , type        := arrowType
    , value       := lamVal
    , hints       := .abbrev
    , safety      := .safe }

/-- Sample invalid host `Lean.ConstantInfo` declaration contaminated with `sorryAx`. -/
def sampleLiveLeanSorryInfo : Lean.ConstantInfo :=
  let propSort : Lean.Expr := .sort .zero
  let falseClaim : Lean.Expr := .forallE (.str .anonymous "P") propSort (.bvar 0) .default
  let sorryProof : Lean.Expr := .const (.str .anonymous "sorryAx") [.zero]
  .thmInfo
    { name        := .str .anonymous "liveBadSorry"
    , levelParams := []
    , type        := falseClaim
    , value       := sorryProof }

/-- Sample invalid host `.opaqueInfo` declaration hiding `sorryAx` in its body. -/
def sampleLiveOpaqueSorryInfo : Lean.ConstantInfo :=
  let propSort : Lean.Expr := .sort .zero
  let falseClaim : Lean.Expr := .forallE (.str .anonymous "P") propSort (.bvar 0) .default
  let sorryProof : Lean.Expr := .const (.str .anonymous "sorryAx") [.zero]
  .opaqueInfo
    { name        := .str .anonymous "liveBadOpaqueSorry"
    , levelParams := []
    , type        := falseClaim
    , value       := sorryProof
    , isUnsafe    := false
    , all         := [.str .anonymous "liveBadOpaqueSorry"] }

/-- Sample host `Lean.RecursorVal` for a 2-constructor inductive `MyBool` (`MyBool.false`, `MyBool.true`)
with its genuine dependent recursor $\Pi$-type
`(motive : MyBool → Type) → motive MyBool.false → motive MyBool.true → (t : MyBool) → motive t`
and `.mdata` annotations on its rule RHSs. -/
def sampleLiveMyBoolRecVal : Lean.RecursorVal :=
  let myBoolName : Lean.Name := .str .anonymous "MyBool"
  let falseName  : Lean.Name := .str myBoolName "false"
  let trueName   : Lean.Name := .str myBoolName "true"
  let recName    : Lean.Name := .str myBoolName "rec"
  let type0      : Lean.Expr := .sort (.succ .zero)
  let myBoolExpr : Lean.Expr := .const myBoolName []
  let motiveTy   : Lean.Expr := .forallE (.str .anonymous "b") myBoolExpr type0 .default
  let recType    : Lean.Expr :=
    .forallE (.str .anonymous "motive") motiveTy
      (.forallE (.str .anonymous "hFalse") (.app (.bvar 0) (.const falseName []))
        (.forallE (.str .anonymous "hTrue") (.app (.bvar 1) (.const trueName []))
          (.forallE (.str .anonymous "t") myBoolExpr
            (.app (.bvar 3) (.bvar 0)) .default) .default) .default) .default
  -- RHS for `MyBool.false`: λ (motive : MyBool → Type) (hFalse : motive false) (hTrue : motive true) => .mdata {} (.bvar 1)
  let rhsFalse : Lean.Expr :=
    .lam (.str .anonymous "motive") motiveTy
      (.lam (.str .anonymous "hFalse") (.app (.bvar 0) (.const falseName []))
        (.lam (.str .anonymous "hTrue") (.app (.bvar 1) (.const trueName []))
          (.mdata {} (.bvar 1)) .default) .default) .default
  -- RHS for `MyBool.true`: λ (motive : MyBool → Type) (hFalse : motive false) (hTrue : motive true) => .mdata {} (.bvar 0)
  let rhsTrue : Lean.Expr :=
    .lam (.str .anonymous "motive") motiveTy
      (.lam (.str .anonymous "hFalse") (.app (.bvar 0) (.const falseName []))
        (.lam (.str .anonymous "hTrue") (.app (.bvar 1) (.const trueName []))
          (.mdata {} (.bvar 0)) .default) .default) .default
  { name        := recName
  , levelParams := []
  , type        := recType
  , all         := [myBoolName]
  , numParams   := 0
  , numIndices  := 0
  , numMotives  := 1
  , numMinors   := 2
  , rules       :=
      [ { ctor := falseName, nfields := 0, rhs := rhsFalse }
      , { ctor := trueName,  nfields := 0, rhs := rhsTrue } ]
  , k           := false
  , isUnsafe    := false }

/-- Sample host `Lean.ConstantInfo` table for `MyBool`, `MyBool.false`, `MyBool.true`, `MyBool.rec`,
and `flipMyBool : MyBool → MyBool`. -/
def sampleLiveConeFindConst? (n : Lean.Name) : Option Lean.ConstantInfo :=
  let kn         : KName     := fromLeanName n
  let myBoolName : Lean.Name := .str .anonymous "MyBool"
  let falseName  : Lean.Name := .str myBoolName "false"
  let trueName   : Lean.Name := .str myBoolName "true"
  let recName    : Lean.Name := .str myBoolName "rec"
  let flipName   : Lean.Name := .str .anonymous "flipMyBool"
  let type0      : Lean.Expr := .sort (.succ .zero)
  let myBoolExpr : Lean.Expr := .const myBoolName []
  let motiveExpr : Lean.Expr := .lam (.str .anonymous "b") myBoolExpr myBoolExpr .default
  if kn == fromLeanName myBoolName then
    some (.inductInfo
      { name := myBoolName, levelParams := [], type := type0
      , numParams := 0, numIndices := 0, all := [myBoolName]
      , ctors := [falseName, trueName], numNested := 0
      , isRec := false, isUnsafe := false, isReflexive := false })
  else if kn == fromLeanName falseName then
    some (.ctorInfo
      { name := falseName, levelParams := [], type := myBoolExpr
      , induct := myBoolName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false })
  else if kn == fromLeanName trueName then
    some (.ctorInfo
      { name := trueName, levelParams := [], type := myBoolExpr
      , induct := myBoolName, cidx := 1, numParams := 0, numFields := 0, isUnsafe := false })
  else if kn == fromLeanName recName then
    some (.recInfo sampleLiveMyBoolRecVal)
  else if kn == fromLeanName flipName then
    let flipBody : Lean.Expr :=
      .lam (.str .anonymous "x") myBoolExpr
        (.app (.app (.app (.app (.const recName []) motiveExpr) (.const trueName [])) (.const falseName [])) (.bvar 0))
        .default
    some (.defnInfo
      { name := flipName, levelParams := []
      , type := .forallE (.str .anonymous "x") myBoolExpr myBoolExpr .default
      , value := flipBody, hints := .abbrev, safety := .safe })
  else
    none

/-- **Universal Theorem (`fromLeanExprWithProjShift_no_double_offset`)**:
For every structure name `s`, field index `i`, structure expression `e`, and parameter-count oracle
`numParamsOf`, `fromLeanExprWithProjShift` preserves the exact 0-based field index `i` without
pre-adding `numParamsOf s` (preventing double-offset against `LeanKernel.kernelWhnf` and
`LeanKernel.inferProjFieldType?`), and maps `Lean.Expr.mvar id` to first-class `KExpr.mvar`. -/
theorem fromLeanExprWithProjShift_no_double_offset
    (numParamsOf : Lean.Name → Nat) (s : Lean.Name) (i : Nat) (e : Lean.Expr) (mvid : Lean.MVarId) :
    fromLeanExprWithProjShift numParamsOf (.proj s i e) =
      (fromLeanExpr e).map (KExpr.proj (fromLeanName s) i) ∧
    fromLeanExprWithProjShift numParamsOf (.mvar mvid) =
      some (.mvar (fromLeanName mvid.name).toCleanId) := by
  refine ⟨?_, rfl⟩
  simp only [fromLeanExprWithProjShift, fromLeanExpr]
  cases fromLeanExpr e <;> rfl

/-! ## 8. 88-Bit Hardware `PackedNodeWord` Bit-Packing (`BitVec 88`) & 7-Section `OBCAMv1` Wire Protocol -/

/-- Well-formedness predicate for an 88-bit hardware-packable `PackedNodeWord`:
all 4 child/symbol/bvar handles fit in 16-bit unsigned fields (`< 65536`) and `tag < 16`. -/
def PackedNodeWord.Wf88 (w : PackedNodeWord) : Prop :=
  w.tag < 16 ∧
  w.h0 < 65536 ∧
  w.h1 < 65536 ∧
  w.h2 < 65536 ∧
  w.symIdx < 65536 ∧
  w.maxLooseBVar < 65536

/-- Pack a `PackedNodeWord` into an 88-bit hardware CAM word (`BitVec 88`):
* `[15:0]`  : `h0` (16b)
* `[31:16]` : `h1` (16b)
* `[47:32]` : `h2` (16b)
* `[63:48]` : `symIdx` (16b)
* `[79:64]` : `maxLooseBVar` (16b)
* `[80]`    : `hasFVar` (1b)
* `[81]`    : `hasMVar` (1b)
* `[82]`    : `hasLooseBVar` (1b)
* `[83]`    : `0` (reserved 1b)
* `[87:84]` : `tag` (4b) -/
def packNodeWord88 (w : PackedNodeWord) : BitVec 88 :=
  let bTag   : BitVec 4  := BitVec.ofNat 4 w.tag
  let bPad   : BitVec 1  := 0#1
  let bLoose : BitVec 1  := if w.hasLooseBVar then 1#1 else 0#1
  let bMVar  : BitVec 1  := if w.hasMVar then 1#1 else 0#1
  let bFVar  : BitVec 1  := if w.hasFVar then 1#1 else 0#1
  let hi8    : BitVec 8  := (((bTag ++ bPad) ++ bLoose) ++ bMVar) ++ bFVar
  let bMaxB  : BitVec 16 := BitVec.ofNat 16 w.maxLooseBVar
  let bSym   : BitVec 16 := BitVec.ofNat 16 w.symIdx
  let bh2    : BitVec 16 := BitVec.ofNat 16 w.h2
  let bh1    : BitVec 16 := BitVec.ofNat 16 w.h1
  let bh0    : BitVec 16 := BitVec.ofNat 16 w.h0
  ((((hi8 ++ bMaxB) ++ bSym) ++ bh2) ++ bh1) ++ bh0

/-- Unpack an 88-bit hardware CAM word (`BitVec 88`) back into a `PackedNodeWord`. -/
def unpackNodeWord88 (bv : BitVec 88) : PackedNodeWord where
  tag          := (bv.extractLsb' 84 4).toNat
  h0           := (bv.extractLsb' 0 16).toNat
  h1           := (bv.extractLsb' 16 16).toNat
  h2           := (bv.extractLsb' 32 16).toNat
  symIdx       := (bv.extractLsb' 48 16).toNat
  hasLooseBVar := bv.getLsbD 82
  hasFVar      := bv.getLsbD 80
  hasMVar      := bv.getLsbD 81
  maxLooseBVar := (bv.extractLsb' 64 16).toNat

/-- **88-Bit Hardware `PackedNodeWord` Round-Trip Theorem (`unpack_packNodeWord88`)**:
For every well-formed `w : PackedNodeWord` (`w.Wf88`), packing `w` into `BitVec 88` and unpacking
recovers `w` identically. -/
theorem unpack_packNodeWord88 (w : PackedNodeWord) (hWf : w.Wf88) :
    unpackNodeWord88 (packNodeWord88 w) = w := by
  rcases w with ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩
  rcases hWf with ⟨hTag, hh0, hh1, hh2, hSym, hMaxB⟩
  have hSliceTag : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 84 4 = BitVec.ofNat 4 tag := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceH0 : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 0 16 = BitVec.ofNat 16 h0 := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceH1 : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 16 16 = BitVec.ofNat 16 h1 := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceH2 : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 32 16 = BitVec.ofNat 16 h2 := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceSym : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 48 16 = BitVec.ofNat 16 symIdx := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hSliceMaxB : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).extractLsb' 64 16 = BitVec.ofNat 16 maxB := by
    unfold packNodeWord88; dsimp only; bv_decide
  have hBitLoose : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).getLsbD 82 = hasLoose := by
    unfold packNodeWord88; dsimp only; cases hasLoose <;> bv_decide
  have hBitF : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).getLsbD 80 = hasF := by
    unfold packNodeWord88; dsimp only; cases hasF <;> bv_decide
  have hBitM : (packNodeWord88 ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩).getLsbD 81 = hasM := by
    unfold packNodeWord88; dsimp only; cases hasM <;> bv_decide
  unfold unpackNodeWord88
  rw [hSliceTag, hSliceH0, hSliceH1, hSliceH2, hSliceSym, hSliceMaxB, hBitLoose, hBitF, hBitM]
  simp only [PackedNodeWord.mk.injEq, BitVec.toNat_ofNat]
  refine ⟨Nat.mod_eq_of_lt hTag, Nat.mod_eq_of_lt hh0, Nat.mod_eq_of_lt hh1,
          Nat.mod_eq_of_lt hh2, Nat.mod_eq_of_lt hSym, trivial, trivial, trivial,
          Nat.mod_eq_of_lt hMaxB⟩

/-- `OBCAMv1` binary DMA wire header for streaming a `Lean.Environment` declaration cone into the
Verilated `silicon_elab_top.sv` / Cloud-FPGA co-processor. -/
structure SiliconElabWireHeader where
  magic            : UInt64 := 0x31564D4143424F00 -- "\0OBCAMV1"
  version          : UInt32 := 1
  flags            : UInt32 := 0
  nodeCount        : UInt32
  symbolCount      : UInt32 := 0
  levelCount       : UInt32 := 0
  constCount       : UInt32
  recRuleCount     : UInt32
  lutEntryCount    : UInt32 := 0
  icapFrameCount   : UInt32 := 0
  targetDeclSymIdx : UInt32
  targetExprHandle : UInt32
  targetTypeHandle : UInt32
  fuelBudget       : UInt32 := 65536
  envPinDigest64   : UInt64 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Hardware universe-level DAG entry (`HwCamLevelEntry`) for Section 3 of the `OBCAMv1` wire frame:
`tag`: `0` = `.zero`, `1` = `.succ`, `2` = `.max`, `3` = `.imax`, `4` = `.param`. -/
structure HwCamLevelEntry where
  tag       : Nat
  l0        : Nat := 0
  l1        : Nat := 0
  paramName : KName := .anonymous
  deriving DecidableEq, Repr, Inhabited

/-- Hardware Zone-3 `DiscrTreeLUT` entry (`DiscrTreeLutEntry`) for Section 6 of the `OBCAMv1` wire frame. -/
structure DiscrTreeLutEntry where
  pathKeys  : List Nat := []
  rhsHandle : Nat := 0
  lutTag    : Nat := 0
  gain      : Nat := 0
  offset    : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Complete 7-section `OBCAMv1` binary DMA wire frame (`SiliconElabWireFrame`) for streaming a
`Lean.Environment` declaration cone into `silicon_elab_top.sv` / Cloud-FPGA co-processors:
* `header`     : `SiliconElabWireHeader`
* `nodes`      : Section 1 (`PackedNodeWord` array)
* `symbols`    : Section 2 (`HwCamSymbolEntry` symbol/literal table)
* `levels`     : Section 3 (`HwCamLevelEntry` universe-level DAG table)
* `consts`     : Section 4 (`HwCamConstEntry` environment constant table)
* `recRules`   : Section 5 (`HwCamRecRuleEntry` recursor $\iota$-rule table)
* `lutEntries` : Section 6 (`DiscrTreeLutEntry` specialized `@[simp]` / typeclass LUT entries)
* `icapFrames` : Section 7 (`IcapBitstreamFrame` signed eFPGA configuration frames) -/
structure SiliconElabWireFrame where
  header     : SiliconElabWireHeader
  nodes      : List PackedNodeWord := []
  symbols    : List HwCamSymbolEntry := []
  levels     : List HwCamLevelEntry := []
  consts     : List HwCamConstEntry := []
  recRules   : List HwCamRecRuleEntry := []
  lutEntries : List DiscrTreeLutEntry := []
  icapFrames : List IcapBitstreamFrame := []
  deriving DecidableEq, Repr, Inhabited

/-- Encode a `Nat` into unsigned LEB128 varint bytes (`natToVarBytes`). -/
def natToVarBytes (n : Nat) : List UInt8 :=
  if n < 128 then
    [UInt8.ofNat n]
  else
    UInt8.ofNat (128 + (n % 128)) :: natToVarBytes (n / 128)
termination_by n

/-- Decode an unsigned LEB128 varint from a byte stream (`decodeVarBytes`), structurally recursive on `List UInt8`. -/
def decodeVarBytes : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then
      some (b.toNat, bs)
    else
      match decodeVarBytes bs with
      | some (hi, rest) => some (hi * 128 + (b.toNat - 128), rest)
      | none => none

@[simp] theorem decodeVarBytes_natToVarBytes (n : Nat) (rest : List UInt8) :
    decodeVarBytes (natToVarBytes n ++ rest) = some (n, rest) := by
  induction n using natToVarBytes.induct with
  | case1 n hlt =>
    unfold natToVarBytes
    simp only [hlt, ↓reduceIte, List.singleton_append, decodeVarBytes]
    have hToNat : (UInt8.ofNat n).toNat = n := by
      change n % 256 = n
      omega
    simp [hToNat, hlt]
  | case2 n hnlt ih =>
    have hArith : n / 128 * 128 + (128 + n % 128 - 128) = n := by omega
    have hGe : ¬ (128 + n % 128 < 128) := by omega
    have hToNat : (UInt8.ofNat (128 + n % 128)).toNat = 128 + n % 128 := by
      change (128 + n % 128) % 256 = 128 + n % 128
      omega
    unfold natToVarBytes
    simp only [hnlt, ↓reduceIte, List.cons_append, decodeVarBytes, hToNat, hGe, ih]
    rw [hArith]

/-- Encode a `Bool` as a 1-byte varint (`0` or `1`). -/
def encodeWireBool (b : Bool) : List UInt8 :=
  natToVarBytes (if b then 1 else 0)

/-- Decode a `Bool` from a byte stream. -/
def decodeWireBool (bs : List UInt8) : Option (Bool × List UInt8) :=
  match decodeVarBytes bs with
  | some (n, rest) => some (n != 0, rest)
  | none => none

@[simp] theorem decodeWireBool_encodeWireBool (b : Bool) (rest : List UInt8) :
    decodeWireBool (encodeWireBool b ++ rest) = some (b, rest) := by
  cases b <;> simp [encodeWireBool, decodeWireBool]

/-- Encode a `UInt32` into varint bytes. -/
def encodeWireUInt32 (u : UInt32) : List UInt8 :=
  natToVarBytes u.toNat

/-- Decode a `UInt32` from varint bytes. -/
def decodeWireUInt32 (bs : List UInt8) : Option (UInt32 × List UInt8) :=
  match decodeVarBytes bs with
  | none => none
  | some (n, rest) =>
    if h : n < UInt32.size then
      some (⟨⟨n, h⟩⟩, rest)
    else none

@[simp] theorem decodeWireUInt32_encodeWireUInt32 (u : UInt32) (rest : List UInt8) :
    decodeWireUInt32 (encodeWireUInt32 u ++ rest) = some (u, rest) := by
  rcases u with ⟨⟨n, h⟩⟩
  unfold encodeWireUInt32 decodeWireUInt32
  rw [decodeVarBytes_natToVarBytes]
  simp [UInt32.toNat, h]

/-- Encode a `UInt64` into varint bytes. -/
def encodeWireUInt64 (u : UInt64) : List UInt8 :=
  natToVarBytes u.toNat

/-- Decode a `UInt64` from varint bytes. -/
def decodeWireUInt64 (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  match decodeVarBytes bs with
  | none => none
  | some (n, rest) =>
    if h : n < UInt64.size then
      some (⟨⟨n, h⟩⟩, rest)
    else none

@[simp] theorem decodeWireUInt64_encodeWireUInt64 (u : UInt64) (rest : List UInt8) :
    decodeWireUInt64 (encodeWireUInt64 u ++ rest) = some (u, rest) := by
  rcases u with ⟨⟨n, h⟩⟩
  unfold encodeWireUInt64 decodeWireUInt64
  rw [decodeVarBytes_natToVarBytes]
  simp [UInt64.toNat, h]

/-- Encode a `BitVec 64` into varint bytes. -/
def encodeWireBitVec64 (bv : BitVec 64) : List UInt8 :=
  natToVarBytes bv.toNat

/-- Decode a `BitVec 64` from varint bytes. -/
def decodeWireBitVec64 (bs : List UInt8) : Option (BitVec 64 × List UInt8) :=
  match decodeVarBytes bs with
  | none => none
  | some (n, rest) =>
    if h : n < 2 ^ 64 then
      some (⟨⟨n, h⟩⟩, rest)
    else none

@[simp] theorem decodeWireBitVec64_encodeWireBitVec64 (bv : BitVec 64) (rest : List UInt8) :
    decodeWireBitVec64 (encodeWireBitVec64 bv ++ rest) = some (bv, rest) := by
  rcases bv with ⟨⟨n, h⟩⟩
  unfold encodeWireBitVec64 decodeWireBitVec64
  rw [decodeVarBytes_natToVarBytes]
  simp [BitVec.toNat, h]

/-- Encode a `Char` into varint bytes. -/
def encodeWireChar (c : Char) : List UInt8 :=
  encodeWireUInt32 c.val

/-- Decode a `Char` from varint bytes. -/
def decodeWireChar (bs : List UInt8) : Option (Char × List UInt8) :=
  match decodeWireUInt32 bs with
  | none => none
  | some (u, rest) =>
    if h2 : u.isValidChar then
      some (⟨u, h2⟩, rest)
    else none

@[simp] theorem decodeWireChar_encodeWireChar (c : Char) (rest : List UInt8) :
    decodeWireChar (encodeWireChar c ++ rest) = some (c, rest) := by
  rcases c with ⟨u, h2⟩
  unfold encodeWireChar decodeWireChar
  rw [decodeWireUInt32_encodeWireUInt32]
  simp [h2]

/-- Encode a homogeneous list by prefixing its length followed by each encoded element. -/
def encodeWireListItems {α : Type} (enc : α → List UInt8) : List α → List UInt8
  | []      => []
  | x :: xs => enc x ++ encodeWireListItems enc xs

/-- Decode exactly `k` elements of type `α` from a byte stream. -/
def decodeWireListItems {α : Type} (dec : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | k + 1, bs =>
    match dec bs with
    | none => none
    | some (x, bs1) =>
      match decodeWireListItems dec k bs1 with
      | none => none
      | some (xs, bs2) => some (x :: xs, bs2)

theorem decodeWireListItems_encodeWireListItems {α : Type}
    (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (hElem : ∀ (x : α) (r : List UInt8), dec (enc x ++ r) = some (x, r)) :
    ∀ (xs : List α) (rest : List UInt8),
      decodeWireListItems dec xs.length (encodeWireListItems enc xs ++ rest) = some (xs, rest)
  | [], rest => rfl
  | x :: xs, rest => by
    simp only [List.length_cons, encodeWireListItems, List.append_assoc, decodeWireListItems]
    rw [hElem x (encodeWireListItems enc xs ++ rest)]
    dsimp only
    rw [decodeWireListItems_encodeWireListItems enc dec hElem xs rest]

/-- Encode a `List α` with its length prefix. -/
def encodeWireList {α : Type} (enc : α → List UInt8) (xs : List α) : List UInt8 :=
  natToVarBytes xs.length ++ encodeWireListItems enc xs

/-- Decode a length-prefixed `List α`. -/
def decodeWireList {α : Type} (dec : List UInt8 → Option (α × List UInt8)) (bs : List UInt8) :
    Option (List α × List UInt8) :=
  match decodeVarBytes bs with
  | none => none
  | some (len, bs1) => decodeWireListItems dec len bs1

theorem decodeWireList_encodeWireList {α : Type}
    (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (hElem : ∀ (x : α) (r : List UInt8), dec (enc x ++ r) = some (x, r))
    (xs : List α) (rest : List UInt8) :
    decodeWireList dec (encodeWireList enc xs ++ rest) = some (xs, rest) := by
  unfold encodeWireList decodeWireList
  rw [List.append_assoc, decodeVarBytes_natToVarBytes]
  dsimp only
  exact decodeWireListItems_encodeWireListItems enc dec hElem xs rest

/-- Encode an `Option α`. -/
def encodeWireOption {α : Type} (enc : α → List UInt8) : Option α → List UInt8
  | none   => natToVarBytes 0
  | some x => natToVarBytes 1 ++ enc x

/-- Decode an `Option α`. -/
def decodeWireOption {α : Type} (dec : List UInt8 → Option (α × List UInt8)) (bs : List UInt8) :
    Option (Option α × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, rest) => some (none, rest)
  | some (1, rest) =>
    match dec rest with
    | some (x, rest2) => some (some x, rest2)
    | none => none
  | _ => none

theorem decodeWireOption_encodeWireOption {α : Type}
    (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (hElem : ∀ (x : α) (r : List UInt8), dec (enc x ++ r) = some (x, r))
    (o : Option α) (rest : List UInt8) :
    decodeWireOption dec (encodeWireOption enc o ++ rest) = some (o, rest) := by
  cases o with
  | none =>
    unfold encodeWireOption decodeWireOption
    rw [decodeVarBytes_natToVarBytes]
    rfl
  | some x =>
    unfold encodeWireOption decodeWireOption
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp [hElem x rest]

/-- Encode a `String` via its `List Char` codepoints. -/
def encodeWireString (s : String) : List UInt8 :=
  encodeWireList encodeWireChar s.toList

/-- Decode a `String` from its `List Char` codepoints. -/
def decodeWireString (bs : List UInt8) : Option (String × List UInt8) :=
  match decodeWireList decodeWireChar bs with
  | some (cs, rest) => some (String.ofList cs, rest)
  | none => none

@[simp] theorem decodeWireString_encodeWireString (s : String) (rest : List UInt8) :
    decodeWireString (encodeWireString s ++ rest) = some (s, rest) := by
  unfold encodeWireString decodeWireString
  rw [decodeWireList_encodeWireList encodeWireChar decodeWireChar decodeWireChar_encodeWireChar s.toList rest]
  simp

/-- Flatten a `KName` into a list of components (`Sum String Nat`) from root to leaf. -/
def knameToComponents : KName → List (Sum String Nat)
  | .anonymous => []
  | .str p s   => knameToComponents p ++ [Sum.inl s]
  | .num p i   => knameToComponents p ++ [Sum.inr i]

/-- Fold a list of `Sum String Nat` components onto an accumulator `KName`. -/
def componentsToKNameAcc : KName → List (Sum String Nat) → KName
  | acc, []               => acc
  | acc, Sum.inl s :: xs  => componentsToKNameAcc (.str acc s) xs
  | acc, Sum.inr i :: xs  => componentsToKNameAcc (.num acc i) xs

theorem componentsToKNameAcc_append (acc : KName) :
    ∀ (xs ys : List (Sum String Nat)),
      componentsToKNameAcc acc (xs ++ ys) = componentsToKNameAcc (componentsToKNameAcc acc xs) ys
  | [], _ => rfl
  | Sum.inl s :: xs, ys => componentsToKNameAcc_append (.str acc s) xs ys
  | Sum.inr i :: xs, ys => componentsToKNameAcc_append (.num acc i) xs ys

@[simp] theorem componentsToKNameAcc_knameToComponents :
    ∀ (n : KName), componentsToKNameAcc .anonymous (knameToComponents n) = n
  | .anonymous => rfl
  | .str p s => by
    simp only [knameToComponents, componentsToKNameAcc_append,
      componentsToKNameAcc_knameToComponents p, componentsToKNameAcc]
  | .num p i => by
    simp only [knameToComponents, componentsToKNameAcc_append,
      componentsToKNameAcc_knameToComponents p, componentsToKNameAcc]

/-- Encode a `Sum String Nat` name component. -/
def encodeNameComp : Sum String Nat → List UInt8
  | Sum.inl s => natToVarBytes 0 ++ encodeWireString s
  | Sum.inr i => natToVarBytes 1 ++ natToVarBytes i

/-- Decode a `Sum String Nat` name component. -/
def decodeNameComp (bs : List UInt8) : Option (Sum String Nat × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, rest) =>
    match decodeWireString rest with
    | some (s, rest2) => some (Sum.inl s, rest2)
    | none => none
  | some (1, rest) =>
    match decodeVarBytes rest with
    | some (i, rest2) => some (Sum.inr i, rest2)
    | none => none
  | _ => none

@[simp] theorem decodeNameComp_encodeNameComp (c : Sum String Nat) (rest : List UInt8) :
    decodeNameComp (encodeNameComp c ++ rest) = some (c, rest) := by
  cases c with
  | inl s =>
    unfold encodeNameComp decodeNameComp
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | inr i =>
    unfold encodeNameComp decodeNameComp
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp

/-- Encode a `KName` into bytes. -/
def encodeWireKName (n : KName) : List UInt8 :=
  encodeWireList encodeNameComp (knameToComponents n)

/-- Decode a `KName` from bytes. -/
def decodeWireKName (bs : List UInt8) : Option (KName × List UInt8) :=
  match decodeWireList decodeNameComp bs with
  | some (comps, rest) => some (componentsToKNameAcc .anonymous comps, rest)
  | none => none

@[simp] theorem decodeWireKName_encodeWireKName (n : KName) (rest : List UInt8) :
    decodeWireKName (encodeWireKName n ++ rest) = some (n, rest) := by
  unfold encodeWireKName decodeWireKName
  rw [decodeWireList_encodeWireList encodeNameComp decodeNameComp decodeNameComp_encodeNameComp]
  simp

/-- Postfix RPN token for lossless fuel-free serialization of `KLevel`. -/
inductive LevelRpnToken where
  | zero
  | succ
  | max
  | imax
  | param (n : KName)
  deriving DecidableEq, Repr

/-- Convert a `KLevel` into a non-empty postfix RPN token list. -/
def klevelToRpn : KLevel → List LevelRpnToken
  | .zero       => [.zero]
  | .succ l     => klevelToRpn l ++ [.succ]
  | .max l1 l2  => klevelToRpn l1 ++ klevelToRpn l2 ++ [.max]
  | .imax l1 l2 => klevelToRpn l1 ++ klevelToRpn l2 ++ [.imax]
  | .param n    => [.param n]

/-- Execute a postfix `LevelRpnToken` stream on a stack `stk : List KLevel`. -/
def evalLevelRpn : List KLevel → List LevelRpnToken → Option (List KLevel)
  | stk, [] => some stk
  | stk, .zero :: ts => evalLevelRpn (.zero :: stk) ts
  | l :: stk, .succ :: ts => evalLevelRpn (.succ l :: stk) ts
  | l2 :: l1 :: stk, .max :: ts => evalLevelRpn (.max l1 l2 :: stk) ts
  | l2 :: l1 :: stk, .imax :: ts => evalLevelRpn (.imax l1 l2 :: stk) ts
  | stk, .param n :: ts => evalLevelRpn (.param n :: stk) ts
  | _, _ => none

theorem evalLevelRpn_klevelToRpn :
    ∀ (l : KLevel) (stk : List KLevel) (more : List LevelRpnToken),
      evalLevelRpn stk (klevelToRpn l ++ more) = evalLevelRpn (l :: stk) more
  | .zero, _, _ => rfl
  | .succ l, stk, more => by
    unfold klevelToRpn
    rw [List.append_assoc, List.singleton_append, evalLevelRpn_klevelToRpn l stk (.succ :: more)]
    rfl
  | .max l1 l2, stk, more => by
    unfold klevelToRpn
    rw [List.append_assoc, List.append_assoc, List.singleton_append,
        evalLevelRpn_klevelToRpn l1 stk (klevelToRpn l2 ++ (.max :: more)),
        evalLevelRpn_klevelToRpn l2 (l1 :: stk) (.max :: more)]
    rfl
  | .imax l1 l2, stk, more => by
    unfold klevelToRpn
    rw [List.append_assoc, List.append_assoc, List.singleton_append,
        evalLevelRpn_klevelToRpn l1 stk (klevelToRpn l2 ++ (.imax :: more)),
        evalLevelRpn_klevelToRpn l2 (l1 :: stk) (.imax :: more)]
    rfl
  | .param _, _, _ => rfl

/-- Encode a `LevelRpnToken`. -/
def encodeLevelRpnToken : LevelRpnToken → List UInt8
  | .zero    => natToVarBytes 0
  | .succ    => natToVarBytes 1
  | .max     => natToVarBytes 2
  | .imax    => natToVarBytes 3
  | .param n => natToVarBytes 4 ++ encodeWireKName n

/-- Decode a `LevelRpnToken`. -/
def decodeLevelRpnToken (bs : List UInt8) : Option (LevelRpnToken × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, rest) => some (.zero, rest)
  | some (1, rest) => some (.succ, rest)
  | some (2, rest) => some (.max, rest)
  | some (3, rest) => some (.imax, rest)
  | some (4, rest) =>
    match decodeWireKName rest with
    | some (n, rest2) => some (.param n, rest2)
    | none => none
  | _ => none

@[simp] theorem decodeLevelRpnToken_encodeLevelRpnToken (t : LevelRpnToken) (rest : List UInt8) :
    decodeLevelRpnToken (encodeLevelRpnToken t ++ rest) = some (t, rest) := by
  cases t with
  | zero | succ | max | imax =>
    unfold encodeLevelRpnToken decodeLevelRpnToken
    rw [decodeVarBytes_natToVarBytes]
    rfl
  | param n =>
    unfold encodeLevelRpnToken decodeLevelRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp

/-- Encode a `KLevel` into bytes via its postfix RPN token stream. -/
def encodeWireKLevel (l : KLevel) : List UInt8 :=
  encodeWireList encodeLevelRpnToken (klevelToRpn l)

/-- Decode a `KLevel` from bytes. -/
def decodeWireKLevel (bs : List UInt8) : Option (KLevel × List UInt8) :=
  match decodeWireList decodeLevelRpnToken bs with
  | some (toks, rest) =>
    match evalLevelRpn [] toks with
    | some [l] => some (l, rest)
    | _        => none
  | none => none

@[simp] theorem decodeWireKLevel_encodeWireKLevel (l : KLevel) (rest : List UInt8) :
    decodeWireKLevel (encodeWireKLevel l ++ rest) = some (l, rest) := by
  unfold encodeWireKLevel decodeWireKLevel
  rw [decodeWireList_encodeWireList encodeLevelRpnToken decodeLevelRpnToken decodeLevelRpnToken_encodeLevelRpnToken]
  dsimp only
  have hRpn := evalLevelRpn_klevelToRpn l [] []
  rw [List.append_nil] at hRpn
  rw [hRpn]
  rfl

/-- Encode a `KLiteral` into bytes. -/
def encodeWireKLiteral : KLiteral → List UInt8
  | .natVal n => natToVarBytes 0 ++ natToVarBytes n
  | .strVal s => natToVarBytes 1 ++ encodeWireString s

/-- Decode a `KLiteral` from bytes. -/
def decodeWireKLiteral (bs : List UInt8) : Option (KLiteral × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, rest) =>
    match decodeVarBytes rest with
    | some (n, rest2) => some (.natVal n, rest2)
    | none => none
  | some (1, rest) =>
    match decodeWireString rest with
    | some (s, rest2) => some (.strVal s, rest2)
    | none => none
  | _ => none

@[simp] theorem decodeWireKLiteral_encodeWireKLiteral (lit : KLiteral) (rest : List UInt8) :
    decodeWireKLiteral (encodeWireKLiteral lit ++ rest) = some (lit, rest) := by
  cases lit with
  | natVal n =>
    unfold encodeWireKLiteral decodeWireKLiteral
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | strVal s =>
    unfold encodeWireKLiteral decodeWireKLiteral
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp

/-- Encode a `SiliconElabWireHeader`. -/
def encodeWireHeader (h : SiliconElabWireHeader) : List UInt8 :=
  encodeWireUInt64 h.magic ++
  encodeWireUInt32 h.version ++
  encodeWireUInt32 h.flags ++
  encodeWireUInt32 h.nodeCount ++
  encodeWireUInt32 h.symbolCount ++
  encodeWireUInt32 h.levelCount ++
  encodeWireUInt32 h.constCount ++
  encodeWireUInt32 h.recRuleCount ++
  encodeWireUInt32 h.lutEntryCount ++
  encodeWireUInt32 h.icapFrameCount ++
  encodeWireUInt32 h.targetDeclSymIdx ++
  encodeWireUInt32 h.targetExprHandle ++
  encodeWireUInt32 h.targetTypeHandle ++
  encodeWireUInt32 h.fuelBudget ++
  encodeWireUInt64 h.envPinDigest64

/-- Decode a `SiliconElabWireHeader`. -/
def decodeWireHeader (bs : List UInt8) : Option (SiliconElabWireHeader × List UInt8) := do
  let (magic, bs1)            ← decodeWireUInt64 bs
  let (version, bs2)          ← decodeWireUInt32 bs1
  let (flags, bs3)            ← decodeWireUInt32 bs2
  let (nodeCount, bs4)        ← decodeWireUInt32 bs3
  let (symbolCount, bs5)      ← decodeWireUInt32 bs4
  let (levelCount, bs6)       ← decodeWireUInt32 bs5
  let (constCount, bs7)       ← decodeWireUInt32 bs6
  let (recRuleCount, bs8)     ← decodeWireUInt32 bs7
  let (lutEntryCount, bs9)    ← decodeWireUInt32 bs8
  let (icapFrameCount, bs10)  ← decodeWireUInt32 bs9
  let (targetDeclSymIdx, bs11) ← decodeWireUInt32 bs10
  let (targetExprHandle, bs12) ← decodeWireUInt32 bs11
  let (targetTypeHandle, bs13) ← decodeWireUInt32 bs12
  let (fuelBudget, bs14)      ← decodeWireUInt32 bs13
  let (envPinDigest64, bs15)  ← decodeWireUInt64 bs14
  pure ({ magic := magic
        , version := version
        , flags := flags
        , nodeCount := nodeCount
        , symbolCount := symbolCount
        , levelCount := levelCount
        , constCount := constCount
        , recRuleCount := recRuleCount
        , lutEntryCount := lutEntryCount
        , icapFrameCount := icapFrameCount
        , targetDeclSymIdx := targetDeclSymIdx
        , targetExprHandle := targetExprHandle
        , targetTypeHandle := targetTypeHandle
        , fuelBudget := fuelBudget
        , envPinDigest64 := envPinDigest64 }, bs15)

@[simp] theorem decodeWireHeader_encodeWireHeader (h : SiliconElabWireHeader) (rest : List UInt8) :
    decodeWireHeader (encodeWireHeader h ++ rest) = some (h, rest) := by
  rcases h with ⟨m, v, fl, nc, sc, lc, cc, rc, ltc, ic, tds, teh, tth, fb, epd⟩
  simp [encodeWireHeader, decodeWireHeader, List.append_assoc]

/-- Encode a Section-1 `PackedNodeWord`. -/
def encodeWirePackedNode (w : PackedNodeWord) : List UInt8 :=
  natToVarBytes w.tag ++
  natToVarBytes w.h0 ++
  natToVarBytes w.h1 ++
  natToVarBytes w.h2 ++
  natToVarBytes w.symIdx ++
  encodeWireBool w.hasLooseBVar ++
  encodeWireBool w.hasFVar ++
  encodeWireBool w.hasMVar ++
  natToVarBytes w.maxLooseBVar

/-- Decode a Section-1 `PackedNodeWord`. -/
def decodeWirePackedNode (bs : List UInt8) : Option (PackedNodeWord × List UInt8) := do
  let (tag, bs1)      ← decodeVarBytes bs
  let (h0, bs2)       ← decodeVarBytes bs1
  let (h1, bs3)       ← decodeVarBytes bs2
  let (h2, bs4)       ← decodeVarBytes bs3
  let (symIdx, bs5)   ← decodeVarBytes bs4
  let (hasLoose, bs6) ← decodeWireBool bs5
  let (hasF, bs7)     ← decodeWireBool bs6
  let (hasM, bs8)     ← decodeWireBool bs7
  let (maxB, bs9)     ← decodeVarBytes bs8
  pure ({ tag := tag, h0 := h0, h1 := h1, h2 := h2, symIdx := symIdx
        , hasLooseBVar := hasLoose, hasFVar := hasF, hasMVar := hasM, maxLooseBVar := maxB }, bs9)

@[simp] theorem decodeWirePackedNode_encodeWirePackedNode (w : PackedNodeWord) (rest : List UInt8) :
    decodeWirePackedNode (encodeWirePackedNode w ++ rest) = some (w, rest) := by
  rcases w with ⟨tag, h0, h1, h2, symIdx, hasLoose, hasF, hasM, maxB⟩
  simp [encodeWirePackedNode, decodeWirePackedNode, List.append_assoc]

/-- Encode a Section-2 `HwCamSymbolEntry`. -/
def encodeWireSymbolEntry : HwCamSymbolEntry → List UInt8
  | .sortEntry u         => natToVarBytes 0 ++ encodeWireKLevel u
  | .constEntry n us     => natToVarBytes 1 ++ encodeWireKName n ++ encodeWireList encodeWireKLevel us
  | .litEntry l          => natToVarBytes 2 ++ encodeWireKLiteral l
  | .projEntry sName idx => natToVarBytes 3 ++ encodeWireKName sName ++ natToVarBytes idx

/-- Decode a Section-2 `HwCamSymbolEntry`. -/
def decodeWireSymbolEntry (bs : List UInt8) : Option (HwCamSymbolEntry × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, bs1) => do
    let (u, bs2) ← decodeWireKLevel bs1
    pure (.sortEntry u, bs2)
  | some (1, bs1) => do
    let (n, bs2) ← decodeWireKName bs1
    let (us, bs3) ← decodeWireList decodeWireKLevel bs2
    pure (.constEntry n us, bs3)
  | some (2, bs1) => do
    let (l, bs2) ← decodeWireKLiteral bs1
    pure (.litEntry l, bs2)
  | some (3, bs1) => do
    let (sName, bs2) ← decodeWireKName bs1
    let (idx, bs3) ← decodeVarBytes bs2
    pure (.projEntry sName idx, bs3)
  | _ => none

@[simp] theorem decodeWireSymbolEntry_encodeWireSymbolEntry (s : HwCamSymbolEntry) (rest : List UInt8) :
    decodeWireSymbolEntry (encodeWireSymbolEntry s ++ rest) = some (s, rest) := by
  cases s with
  | sortEntry u =>
    unfold encodeWireSymbolEntry decodeWireSymbolEntry
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | constEntry n us =>
    unfold encodeWireSymbolEntry decodeWireSymbolEntry
    simp only [List.append_assoc, decodeVarBytes_natToVarBytes, decodeWireKName_encodeWireKName,
      Option.bind_eq_bind, Option.bind_some]
    rw [decodeWireList_encodeWireList encodeWireKLevel decodeWireKLevel decodeWireKLevel_encodeWireKLevel]
    rfl
  | litEntry l =>
    unfold encodeWireSymbolEntry decodeWireSymbolEntry
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | projEntry sName idx =>
    unfold encodeWireSymbolEntry decodeWireSymbolEntry
    simp [List.append_assoc]

/-- Encode a Section-3 `HwCamLevelEntry`. -/
def encodeWireLevelEntry (e : HwCamLevelEntry) : List UInt8 :=
  natToVarBytes e.tag ++
  natToVarBytes e.l0 ++
  natToVarBytes e.l1 ++
  encodeWireKName e.paramName

/-- Decode a Section-3 `HwCamLevelEntry`. -/
def decodeWireLevelEntry (bs : List UInt8) : Option (HwCamLevelEntry × List UInt8) := do
  let (tag, bs1)  ← decodeVarBytes bs
  let (l0, bs2)   ← decodeVarBytes bs1
  let (l1, bs3)   ← decodeVarBytes bs2
  let (pName, bs4) ← decodeWireKName bs3
  pure ({ tag := tag, l0 := l0, l1 := l1, paramName := pName }, bs4)

@[simp] theorem decodeWireLevelEntry_encodeWireLevelEntry (e : HwCamLevelEntry) (rest : List UInt8) :
    decodeWireLevelEntry (encodeWireLevelEntry e ++ rest) = some (e, rest) := by
  rcases e with ⟨tag, l0, l1, pName⟩
  simp [encodeWireLevelEntry, decodeWireLevelEntry, List.append_assoc]

/-- Encode a Section-4 `HwCamConstEntry`. -/
def encodeWireConstEntry (c : HwCamConstEntry) : List UInt8 :=
  encodeWireKName c.name ++
  natToVarBytes c.symIdx ++
  natToVarBytes c.typeHandle ++
  encodeWireOption natToVarBytes c.valHandle? ++
  encodeWireBool c.isCtor ++
  encodeWireOption encodeWireKName c.inductName?

/-- Decode a Section-4 `HwCamConstEntry`. -/
def decodeWireConstEntry (bs : List UInt8) : Option (HwCamConstEntry × List UInt8) := do
  let (name, bs1)       ← decodeWireKName bs
  let (symIdx, bs2)     ← decodeVarBytes bs1
  let (typeHandle, bs3) ← decodeVarBytes bs2
  let (valHandle?, bs4) ← decodeWireOption decodeVarBytes bs3
  let (isCtor, bs5)     ← decodeWireBool bs4
  let (indName?, bs6)   ← decodeWireOption decodeWireKName bs5
  pure ({ name := name, symIdx := symIdx, typeHandle := typeHandle
        , valHandle? := valHandle?, isCtor := isCtor, inductName? := indName? }, bs6)

@[simp] theorem decodeWireConstEntry_encodeWireConstEntry (c : HwCamConstEntry) (rest : List UInt8) :
    decodeWireConstEntry (encodeWireConstEntry c ++ rest) = some (c, rest) := by
  rcases c with ⟨name, symIdx, typeHandle, valHandle?, isCtor, indName?⟩
  unfold encodeWireConstEntry decodeWireConstEntry
  simp only [List.append_assoc, decodeWireKName_encodeWireKName, decodeVarBytes_natToVarBytes,
    Option.bind_eq_bind, Option.bind_some]
  rw [decodeWireOption_encodeWireOption natToVarBytes decodeVarBytes decodeVarBytes_natToVarBytes]
  simp only [Option.bind_some, decodeWireBool_encodeWireBool]
  rw [decodeWireOption_encodeWireOption encodeWireKName decodeWireKName decodeWireKName_encodeWireKName]
  rfl

/-- Encode a Section-5 `HwCamRecRuleEntry`. -/
def encodeWireRecRuleEntry (r : HwCamRecRuleEntry) : List UInt8 :=
  encodeWireKName r.recName ++
  encodeWireKName r.ctorName ++
  natToVarBytes r.numParams ++
  natToVarBytes r.numFields ++
  natToVarBytes r.rhsHandle

/-- Decode a Section-5 `HwCamRecRuleEntry`. -/
def decodeWireRecRuleEntry (bs : List UInt8) : Option (HwCamRecRuleEntry × List UInt8) := do
  let (recName, bs1)   ← decodeWireKName bs
  let (ctorName, bs2)  ← decodeWireKName bs1
  let (numParams, bs3) ← decodeVarBytes bs2
  let (numFields, bs4) ← decodeVarBytes bs3
  let (rhsHandle, bs5) ← decodeVarBytes bs4
  pure ({ recName := recName, ctorName := ctorName, numParams := numParams
        , numFields := numFields, rhsHandle := rhsHandle }, bs5)

@[simp] theorem decodeWireRecRuleEntry_encodeWireRecRuleEntry (r : HwCamRecRuleEntry) (rest : List UInt8) :
    decodeWireRecRuleEntry (encodeWireRecRuleEntry r ++ rest) = some (r, rest) := by
  rcases r with ⟨recName, ctorName, numParams, numFields, rhsHandle⟩
  simp [encodeWireRecRuleEntry, decodeWireRecRuleEntry, List.append_assoc]

/-- Encode a Section-6 `DiscrTreeLutEntry`. -/
def encodeWireLutEntry (e : DiscrTreeLutEntry) : List UInt8 :=
  encodeWireList natToVarBytes e.pathKeys ++
  natToVarBytes e.rhsHandle ++
  natToVarBytes e.lutTag ++
  natToVarBytes e.gain ++
  natToVarBytes e.offset

/-- Decode a Section-6 `DiscrTreeLutEntry`. -/
def decodeWireLutEntry (bs : List UInt8) : Option (DiscrTreeLutEntry × List UInt8) := do
  let (pathKeys, bs1)  ← decodeWireList decodeVarBytes bs
  let (rhsHandle, bs2) ← decodeVarBytes bs1
  let (lutTag, bs3)    ← decodeVarBytes bs2
  let (gain, bs4)      ← decodeVarBytes bs3
  let (offset, bs5)    ← decodeVarBytes bs4
  pure ({ pathKeys := pathKeys, rhsHandle := rhsHandle, lutTag := lutTag
        , gain := gain, offset := offset }, bs5)

@[simp] theorem decodeWireLutEntry_encodeWireLutEntry (e : DiscrTreeLutEntry) (rest : List UInt8) :
    decodeWireLutEntry (encodeWireLutEntry e ++ rest) = some (e, rest) := by
  rcases e with ⟨pathKeys, rhsHandle, lutTag, gain, offset⟩
  unfold encodeWireLutEntry decodeWireLutEntry
  simp only [List.append_assoc]
  rw [decodeWireList_encodeWireList natToVarBytes decodeVarBytes decodeVarBytes_natToVarBytes]
  simp

/-- Encode an `RtlAluOp`. -/
def encodeWireRtlAluOp : RtlAluOp → List UInt8
  | .add    => natToVarBytes 0
  | .sub    => natToVarBytes 1
  | .mul    => natToVarBytes 2
  | .bitAnd => natToVarBytes 3
  | .bitOr  => natToVarBytes 4
  | .bitXor => natToVarBytes 5
  | .shl    => natToVarBytes 6
  | .lshr   => natToVarBytes 7
  | .ashr   => natToVarBytes 8
  | .eq     => natToVarBytes 9
  | .ult    => natToVarBytes 10
  | .slt    => natToVarBytes 11
  | .qmul32 => natToVarBytes 12

/-- Decode an `RtlAluOp`. -/
def decodeWireRtlAluOp (bs : List UInt8) : Option (RtlAluOp × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, r)  => some (.add, r)
  | some (1, r)  => some (.sub, r)
  | some (2, r)  => some (.mul, r)
  | some (3, r)  => some (.bitAnd, r)
  | some (4, r)  => some (.bitOr, r)
  | some (5, r)  => some (.bitXor, r)
  | some (6, r)  => some (.shl, r)
  | some (7, r)  => some (.lshr, r)
  | some (8, r)  => some (.ashr, r)
  | some (9, r)  => some (.eq, r)
  | some (10, r) => some (.ult, r)
  | some (11, r) => some (.slt, r)
  | some (12, r) => some (.qmul32, r)
  | _            => none

@[simp] theorem decodeWireRtlAluOp_encodeWireRtlAluOp (op : RtlAluOp) (rest : List UInt8) :
    decodeWireRtlAluOp (encodeWireRtlAluOp op ++ rest) = some (op, rest) := by
  cases op <;> { unfold encodeWireRtlAluOp decodeWireRtlAluOp; rw [decodeVarBytes_natToVarBytes]; rfl }

/-- Postfix RPN token for lossless fuel-free serialization of `RtlExpr`. -/
inductive RtlExprRpnToken where
  | const     (val : BitVec 64)
  | inputPort (idx : Nat)
  | wireRef   (idx : Nat)
  | regRead   (idx : Nat)
  | alu       (op : RtlAluOp)
  | mux
  | bitNot
  | resize    (op : RtlWidthOp)
  deriving DecidableEq, Repr

/-- Convert an `RtlExpr` into a postfix RPN token list. -/
def rtlExprToRpn : RtlExpr → List RtlExprRpnToken
  | .const v       => [.const v]
  | .inputPort idx => [.inputPort idx]
  | .wireRef idx   => [.wireRef idx]
  | .regRead idx   => [.regRead idx]
  | .alu op a b    => rtlExprToRpn a ++ rtlExprToRpn b ++ [.alu op]
  | .mux c t f     => rtlExprToRpn c ++ rtlExprToRpn t ++ rtlExprToRpn f ++ [.mux]
  | .bitNot a      => rtlExprToRpn a ++ [.bitNot]
  | .resize op a   => rtlExprToRpn a ++ [.resize op]

/-- Execute a postfix `RtlExprRpnToken` stream on a stack `stk : List RtlExpr`. -/
def evalRtlExprRpn : List RtlExpr → List RtlExprRpnToken → Option (List RtlExpr)
  | stk, []                      => some stk
  | stk, .const v :: ts          => evalRtlExprRpn (.const v :: stk) ts
  | stk, .inputPort idx :: ts    => evalRtlExprRpn (.inputPort idx :: stk) ts
  | stk, .wireRef idx :: ts      => evalRtlExprRpn (.wireRef idx :: stk) ts
  | stk, .regRead idx :: ts      => evalRtlExprRpn (.regRead idx :: stk) ts
  | b :: a :: stk, .alu op :: ts => evalRtlExprRpn (.alu op a b :: stk) ts
  | f :: t :: c :: stk, .mux :: ts => evalRtlExprRpn (.mux c t f :: stk) ts
  | a :: stk, .bitNot :: ts      => evalRtlExprRpn (.bitNot a :: stk) ts
  | a :: stk, .resize op :: ts   => evalRtlExprRpn (.resize op a :: stk) ts
  | _, _                         => none

theorem evalRtlExprRpn_rtlExprToRpn :
    ∀ (e : RtlExpr) (stk : List RtlExpr) (more : List RtlExprRpnToken),
      evalRtlExprRpn stk (rtlExprToRpn e ++ more) = evalRtlExprRpn (e :: stk) more
  | .const _, _, _ => rfl
  | .inputPort _, _, _ => rfl
  | .wireRef _, _, _ => rfl
  | .regRead _, _, _ => rfl
  | .alu op a b, stk, more => by
    unfold rtlExprToRpn
    rw [List.append_assoc, List.append_assoc, List.singleton_append,
        evalRtlExprRpn_rtlExprToRpn a stk (rtlExprToRpn b ++ (.alu op :: more)),
        evalRtlExprRpn_rtlExprToRpn b (a :: stk) (.alu op :: more)]
    rfl
  | .mux c t f, stk, more => by
    unfold rtlExprToRpn
    rw [List.append_assoc, List.append_assoc, List.append_assoc, List.singleton_append,
        evalRtlExprRpn_rtlExprToRpn c stk (rtlExprToRpn t ++ (rtlExprToRpn f ++ (.mux :: more))),
        evalRtlExprRpn_rtlExprToRpn t (c :: stk) (rtlExprToRpn f ++ (.mux :: more)),
        evalRtlExprRpn_rtlExprToRpn f (t :: c :: stk) (.mux :: more)]
    rfl
  | .bitNot a, stk, more => by
    unfold rtlExprToRpn
    rw [List.append_assoc, List.singleton_append,
        evalRtlExprRpn_rtlExprToRpn a stk (.bitNot :: more)]
    rfl
  | .resize op a, stk, more => by
    unfold rtlExprToRpn
    rw [List.append_assoc, List.singleton_append,
        evalRtlExprRpn_rtlExprToRpn a stk (.resize op :: more)]
    rfl

/-- Encode an `RtlWidthOp`. -/
def encodeWireRtlWidthOp : RtlWidthOp → List UInt8
  | .slice hi lo => natToVarBytes 0 ++ natToVarBytes hi ++ natToVarBytes lo
  | .zext w      => natToVarBytes 1 ++ natToVarBytes w
  | .sext f t    => natToVarBytes 2 ++ natToVarBytes f ++ natToVarBytes t
  | .trunc w     => natToVarBytes 3 ++ natToVarBytes w

/-- Decode an `RtlWidthOp`. -/
def decodeWireRtlWidthOp (bs : List UInt8) : Option (RtlWidthOp × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, r) => do let (hi, r2) ← decodeVarBytes r; let (lo, r3) ← decodeVarBytes r2; pure (.slice hi lo, r3)
  | some (1, r) => do let (w, r2) ← decodeVarBytes r; pure (.zext w, r2)
  | some (2, r) => do let (f, r2) ← decodeVarBytes r; let (t, r3) ← decodeVarBytes r2; pure (.sext f t, r3)
  | some (3, r) => do let (w, r2) ← decodeVarBytes r; pure (.trunc w, r2)
  | _           => none

@[simp] theorem decodeWireRtlWidthOp_encodeWireRtlWidthOp (op : RtlWidthOp) (rest : List UInt8) :
    decodeWireRtlWidthOp (encodeWireRtlWidthOp op ++ rest) = some (op, rest) := by
  cases op <;>
    simp [encodeWireRtlWidthOp, decodeWireRtlWidthOp, List.append_assoc, decodeVarBytes_natToVarBytes] <;> rfl

/-- Encode an `RtlExprRpnToken`. -/
def encodeRtlExprRpnToken : RtlExprRpnToken → List UInt8
  | .const v       => natToVarBytes 0 ++ encodeWireBitVec64 v
  | .inputPort idx => natToVarBytes 1 ++ natToVarBytes idx
  | .wireRef idx   => natToVarBytes 2 ++ natToVarBytes idx
  | .regRead idx   => natToVarBytes 3 ++ natToVarBytes idx
  | .alu op        => natToVarBytes 4 ++ encodeWireRtlAluOp op
  | .mux           => natToVarBytes 5
  | .bitNot        => natToVarBytes 6
  | .resize op     => natToVarBytes 7 ++ encodeWireRtlWidthOp op

/-- Decode an `RtlExprRpnToken`. -/
def decodeRtlExprRpnToken (bs : List UInt8) : Option (RtlExprRpnToken × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, r) => do let (v, r2) ← decodeWireBitVec64 r; pure (.const v, r2)
  | some (1, r) => do let (idx, r2) ← decodeVarBytes r; pure (.inputPort idx, r2)
  | some (2, r) => do let (idx, r2) ← decodeVarBytes r; pure (.wireRef idx, r2)
  | some (3, r) => do let (idx, r2) ← decodeVarBytes r; pure (.regRead idx, r2)
  | some (4, r) => do let (op, r2) ← decodeWireRtlAluOp r; pure (.alu op, r2)
  | some (5, r) => some (.mux, r)
  | some (6, r) => some (.bitNot, r)
  | some (7, r) => do let (op, r2) ← decodeWireRtlWidthOp r; pure (.resize op, r2)
  | _           => none

@[simp] theorem decodeRtlExprRpnToken_encodeRtlExprRpnToken (t : RtlExprRpnToken) (rest : List UInt8) :
    decodeRtlExprRpnToken (encodeRtlExprRpnToken t ++ rest) = some (t, rest) := by
  cases t with
  | const v =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | inputPort idx | wireRef idx | regRead idx =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | alu op =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | resize op =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [List.append_assoc, decodeVarBytes_natToVarBytes]
    simp
  | mux | bitNot =>
    unfold encodeRtlExprRpnToken decodeRtlExprRpnToken
    rw [decodeVarBytes_natToVarBytes]
    rfl

/-- Encode an `RtlExpr` via its postfix RPN token list. -/
def encodeWireRtlExpr (e : RtlExpr) : List UInt8 :=
  encodeWireList encodeRtlExprRpnToken (rtlExprToRpn e)

/-- Decode an `RtlExpr` from bytes. -/
def decodeWireRtlExpr (bs : List UInt8) : Option (RtlExpr × List UInt8) :=
  match decodeWireList decodeRtlExprRpnToken bs with
  | some (toks, rest) =>
    match evalRtlExprRpn [] toks with
    | some [e] => some (e, rest)
    | _        => none
  | none => none

@[simp] theorem decodeWireRtlExpr_encodeWireRtlExpr (e : RtlExpr) (rest : List UInt8) :
    decodeWireRtlExpr (encodeWireRtlExpr e ++ rest) = some (e, rest) := by
  unfold encodeWireRtlExpr decodeWireRtlExpr
  rw [decodeWireList_encodeWireList encodeRtlExprRpnToken decodeRtlExprRpnToken decodeRtlExprRpnToken_encodeRtlExprRpnToken]
  dsimp only
  have hRpn := evalRtlExprRpn_rtlExprToRpn e [] []
  rw [List.append_nil] at hRpn
  rw [hRpn]
  rfl

/-- Encode a `TileOpKind`. -/
def encodeWireTileOpKind : TileOpKind → List UInt8
  | .methodSlot      => natToVarBytes 0
  | .cellSlot        => natToVarBytes 1
  | .loweredLeanLite => natToVarBytes 2

/-- Decode a `TileOpKind`. -/
def decodeWireTileOpKind (bs : List UInt8) : Option (TileOpKind × List UInt8) :=
  match decodeVarBytes bs with
  | some (0, r) => some (.methodSlot, r)
  | some (1, r) => some (.cellSlot, r)
  | some (2, r) => some (.loweredLeanLite, r)
  | _           => none

@[simp] theorem decodeWireTileOpKind_encodeWireTileOpKind (k : TileOpKind) (rest : List UInt8) :
    decodeWireTileOpKind (encodeWireTileOpKind k ++ rest) = some (k, rest) := by
  cases k <;> { unfold encodeWireTileOpKind decodeWireTileOpKind; rw [decodeVarBytes_natToVarBytes]; rfl }

/-- Encode a Section-7 `IcapBitstreamFrame`. -/
def encodeWireIcapFrame (f : IcapBitstreamFrame) : List UInt8 :=
  natToVarBytes f.targetTileId ++
  natToVarBytes f.newTile.slotIdx ++
  encodeWireString f.newTile.memberName ++
  encodeWireTileOpKind f.newTile.opKind ++
  encodeWireRtlExpr f.newTile.datapath ++
  encodeWireList natToVarBytes f.newTile.readsSlots ++
  encodeWireBitVec64 f.expectedCrc64 ++
  encodeWireBitVec64 f.computedCrc64

/-- Decode a Section-7 `IcapBitstreamFrame`. -/
def decodeWireIcapFrame (bs : List UInt8) : Option (IcapBitstreamFrame × List UInt8) := do
  let (targetTileId, bs1)   ← decodeVarBytes bs
  let (slotIdx, bs2)        ← decodeVarBytes bs1
  let (memberName, bs3)     ← decodeWireString bs2
  let (opKind, bs4)         ← decodeWireTileOpKind bs3
  let (datapath, bs5)       ← decodeWireRtlExpr bs4
  let (readsSlots, bs6)     ← decodeWireList decodeVarBytes bs5
  let (expectedCrc64, bs7)  ← decodeWireBitVec64 bs6
  let (computedCrc64, bs8)  ← decodeWireBitVec64 bs7
  pure ({ targetTileId := targetTileId
        , newTile :=
            { slotIdx    := slotIdx
            , memberName := memberName
            , opKind     := opKind
            , datapath   := datapath
            , readsSlots := readsSlots }
        , expectedCrc64 := expectedCrc64
        , computedCrc64 := computedCrc64 }, bs8)

@[simp] theorem decodeWireIcapFrame_encodeWireIcapFrame (f : IcapBitstreamFrame) (rest : List UInt8) :
    decodeWireIcapFrame (encodeWireIcapFrame f ++ rest) = some (f, rest) := by
  rcases f with ⟨targetTileId, ⟨slotIdx, memberName, opKind, datapath, readsSlots⟩, expectedCrc64, computedCrc64⟩
  unfold encodeWireIcapFrame decodeWireIcapFrame
  simp only [List.append_assoc, decodeVarBytes_natToVarBytes, decodeWireString_encodeWireString,
    decodeWireTileOpKind_encodeWireTileOpKind, decodeWireRtlExpr_encodeWireRtlExpr,
    Option.bind_eq_bind, Option.bind_some]
  rw [decodeWireList_encodeWireList natToVarBytes decodeVarBytes decodeVarBytes_natToVarBytes]
  simp

/-- Encode a complete 7-section `SiliconElabWireFrame` into a `List UInt8` byte stream. -/
def encodeSiliconWireFrameBytes (f : SiliconElabWireFrame) : List UInt8 :=
  encodeWireHeader f.header ++
  encodeWireList encodeWirePackedNode f.nodes ++
  encodeWireList encodeWireSymbolEntry f.symbols ++
  encodeWireList encodeWireLevelEntry f.levels ++
  encodeWireList encodeWireConstEntry f.consts ++
  encodeWireList encodeWireRecRuleEntry f.recRules ++
  encodeWireList encodeWireLutEntry f.lutEntries ++
  encodeWireList encodeWireIcapFrame f.icapFrames

/-- Decode a complete 7-section `SiliconElabWireFrame` from a `List UInt8` byte stream. -/
def decodeSiliconWireFrameBytes (bs : List UInt8) : Option (SiliconElabWireFrame × List UInt8) := do
  let (header, bs1)     ← decodeWireHeader bs
  let (nodes, bs2)      ← decodeWireList decodeWirePackedNode bs1
  let (symbols, bs3)    ← decodeWireList decodeWireSymbolEntry bs2
  let (levels, bs4)     ← decodeWireList decodeWireLevelEntry bs3
  let (consts, bs5)     ← decodeWireList decodeWireConstEntry bs4
  let (recRules, bs6)   ← decodeWireList decodeWireRecRuleEntry bs5
  let (lutEntries, bs7) ← decodeWireList decodeWireLutEntry bs6
  let (icapFrames, bs8) ← decodeWireList decodeWireIcapFrame bs7
  pure ({ header := header
        , nodes := nodes
        , symbols := symbols
        , levels := levels
        , consts := consts
        , recRules := recRules
        , lutEntries := lutEntries
        , icapFrames := icapFrames }, bs8)

@[simp] theorem decodeSiliconWireFrameBytes_encodeSiliconWireFrameBytes
    (f : SiliconElabWireFrame) (rest : List UInt8) :
    decodeSiliconWireFrameBytes (encodeSiliconWireFrameBytes f ++ rest) = some (f, rest) := by
  rcases f with ⟨header, nodes, symbols, levels, consts, recRules, lutEntries, icapFrames⟩
  unfold encodeSiliconWireFrameBytes decodeSiliconWireFrameBytes
  simp only [List.append_assoc, decodeWireHeader_encodeWireHeader,
    Option.bind_eq_bind, Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWirePackedNode decodeWirePackedNode decodeWirePackedNode_encodeWirePackedNode]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireSymbolEntry decodeWireSymbolEntry decodeWireSymbolEntry_encodeWireSymbolEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireLevelEntry decodeWireLevelEntry decodeWireLevelEntry_encodeWireLevelEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireConstEntry decodeWireConstEntry decodeWireConstEntry_encodeWireConstEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireRecRuleEntry decodeWireRecRuleEntry decodeWireRecRuleEntry_encodeWireRecRuleEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireLutEntry decodeWireLutEntry decodeWireLutEntry_encodeWireLutEntry]
  simp only [Option.bind_some]
  rw [decodeWireList_encodeWireList encodeWireIcapFrame decodeWireIcapFrame decodeWireIcapFrame_encodeWireIcapFrame]
  rfl

/-- Serialize a 7-section `SiliconElabWireFrame` (`OBCAMv1`) into a `ByteArray`. -/
def serializeSiliconWireFrame (f : SiliconElabWireFrame) : ByteArray :=
  ByteArray.mk (Array.mk (encodeSiliconWireFrameBytes f))

/-- Deserialize a 7-section `SiliconElabWireFrame` (`OBCAMv1`) from a `ByteArray`. -/
def deserializeSiliconWireFrame (ba : ByteArray) : Option SiliconElabWireFrame :=
  match decodeSiliconWireFrameBytes ba.data.toList with
  | some (f, []) => some f
  | _            => none

/-- **7-Section `OBCAMv1` Wire Frame Round-Trip Theorem (`deserialize_serialize_siliconWireFrame`)**:
For every 7-section `SiliconElabWireFrame` (`header`, `nodes`, `symbols`, `levels`, `consts`,
`recRules`, `lutEntries`, `icapFrames`), serializing to `ByteArray` via `serializeSiliconWireFrame`
and deserializing via `deserializeSiliconWireFrame` recovers `some f` losslessly (`0 sorryAx`). -/
theorem deserialize_serialize_siliconWireFrame (f : SiliconElabWireFrame) :
    deserializeSiliconWireFrame (serializeSiliconWireFrame f) = some f := by
  have hData : (serializeSiliconWireFrame f).data.toList = encodeSiliconWireFrameBytes f := rfl
  unfold deserializeSiliconWireFrame
  rw [hData]
  have h := decodeSiliconWireFrameBytes_encodeSiliconWireFrameBytes f []
  rw [List.append_nil] at h
  rw [h]

/-- Allocate or reuse a `HwCamLevelEntry` in a Section-3 universe level DAG table. -/
def allocHwCamLevelEntry (e : HwCamLevelEntry) (tbl : List HwCamLevelEntry) :
    Nat × List HwCamLevelEntry :=
  match findElemIdx? tbl e with
  | some idx => (idx, tbl)
  | none => (tbl.length, tbl ++ [e])

/-- Intern a `KLevel` into a deduplicated Section-3 `List HwCamLevelEntry` DAG table. -/
def internKLevelToHwCam : KLevel → List HwCamLevelEntry → Nat × List HwCamLevelEntry
  | .zero, tbl =>
    allocHwCamLevelEntry { tag := 0 } tbl
  | .succ u, tbl =>
    let (uIdx, tbl1) := internKLevelToHwCam u tbl
    allocHwCamLevelEntry { tag := 1, l0 := uIdx } tbl1
  | .max u v, tbl =>
    let (uIdx, tbl1) := internKLevelToHwCam u tbl
    let (vIdx, tbl2) := internKLevelToHwCam v tbl1
    allocHwCamLevelEntry { tag := 2, l0 := uIdx, l1 := vIdx } tbl2
  | .imax u v, tbl =>
    let (uIdx, tbl1) := internKLevelToHwCam u tbl
    let (vIdx, tbl2) := internKLevelToHwCam v tbl1
    allocHwCamLevelEntry { tag := 3, l0 := uIdx, l1 := vIdx } tbl2
  | .param n, tbl =>
    allocHwCamLevelEntry { tag := 4, paramName := n } tbl

/-- Reconstruct a `KLevel` from a Section-3 `List HwCamLevelEntry` DAG table. -/
def reconstructHwCamLevel : Nat → List HwCamLevelEntry → Nat → Option KLevel
  | 0, _, _ => none
  | fuel + 1, tbl, idx =>
    match tbl[idx]? with
    | none => none
    | some e =>
      if e.tag == 0 then some .zero
      else if e.tag == 1 then (reconstructHwCamLevel fuel tbl e.l0).map .succ
      else if e.tag == 2 then
        match reconstructHwCamLevel fuel tbl e.l0, reconstructHwCamLevel fuel tbl e.l1 with
        | some u, some v => some (.max u v)
        | _, _ => none
      else if e.tag == 3 then
        match reconstructHwCamLevel fuel tbl e.l0, reconstructHwCamLevel fuel tbl e.l1 with
        | some u, some v => some (.imax u v)
        | _, _ => none
      else if e.tag == 4 then some (.param e.paramName)
      else none

/-- Extract the deduplicated Section-3 `List HwCamLevelEntry` table from `cam.symbols`. -/
def extractCamLevelEntries (cam : HwExprCAM) : List HwCamLevelEntry :=
  cam.symbols.foldl
    (fun tbl sym =>
      match sym with
      | .sortEntry u => (internKLevelToHwCam u tbl).2
      | .constEntry _ us => us.foldl (fun acc u => (internKLevelToHwCam u acc).2) tbl
      | _ => tbl)
    []

/-- Check `OBCAMv1` magic (`0x31564D4143424F00`), `version == 1`, and exact agreement between
`header` section counts and the 7 payload section lengths. -/
def SiliconElabWireFrame.hasValidHeader (f : SiliconElabWireFrame) : Bool :=
  f.header.magic == 0x31564D4143424F00 &&
  f.header.version == 1 &&
  f.header.nodeCount.toNat == f.nodes.length &&
  f.header.symbolCount.toNat == f.symbols.length &&
  f.header.levelCount.toNat == f.levels.length &&
  f.header.constCount.toNat == f.consts.length &&
  f.header.recRuleCount.toNat == f.recRules.length &&
  f.header.lutEntryCount.toNat == f.lutEntries.length &&
  f.header.icapFrameCount.toNat == f.icapFrames.length

/-- Construct a canonical, header-validated 7-section `SiliconElabWireFrame` (`OBCAMv1`) directly
from an interned `HwExprCAM`, populating Section 3 (`levels`) from `cam.symbols` and synchronizing
all 7 section count fields in `SiliconElabWireHeader`. -/
def buildSiliconWireFrameFromCam
    (cam : HwExprCAM)
    (targetDeclSymIdx targetExprHandle targetTypeHandle : Nat)
    (lutEntries : List DiscrTreeLutEntry := [])
    (icapFrames : List IcapBitstreamFrame := [])
    (fuelBudget : UInt32 := 65536)
    (envPinDigest64 : UInt64 := 0) : SiliconElabWireFrame :=
  let levels := extractCamLevelEntries cam
  { header :=
      { magic            := 0x31564D4143424F00
      , version          := 1
      , flags            := 0
      , nodeCount        := UInt32.ofNat cam.nodes.length
      , symbolCount      := UInt32.ofNat cam.symbols.length
      , levelCount       := UInt32.ofNat levels.length
      , constCount       := UInt32.ofNat cam.consts.length
      , recRuleCount     := UInt32.ofNat cam.recRules.length
      , lutEntryCount    := UInt32.ofNat lutEntries.length
      , icapFrameCount   := UInt32.ofNat icapFrames.length
      , targetDeclSymIdx := UInt32.ofNat targetDeclSymIdx
      , targetExprHandle := UInt32.ofNat targetExprHandle
      , targetTypeHandle := UInt32.ofNat targetTypeHandle
      , fuelBudget       := fuelBudget
      , envPinDigest64   := envPinDigest64 }
  , nodes      := cam.nodes
  , symbols    := cam.symbols
  , levels     := levels
  , consts     := cam.consts
  , recRules   := cam.recRules
  , lutEntries := lutEntries
  , icapFrames := icapFrames }


end Obend.Lower.ExprCAM
end
