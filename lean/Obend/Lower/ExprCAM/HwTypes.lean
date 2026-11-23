module
/-
# Obend.Lower.ExprCAM.HwTypes — Shared Hardware CAM Types & Core DAG Builders

Core fixed-width hardware expression CAM carriers (`HwCamSymbolEntry`, `PackedNodeWord`,
`HwCamRecRuleEntry`, `HwCamConstEntry`, `HwExprCAM`) and associative lookup / allocation
builders shared between `Obend.Lower.ExprCAM` and `Obend.Lower.ExprCAM.ConeAndWire`.
-/
public import Obend.Lower.LeanKernel
public section

namespace Obend.Lower.ExprCAM
open Obend.Lower.Inductive
open Obend.Lower.LeanKernel
set_option autoImplicit false

/-- Auxiliary symbol/literal/universe table entry (`HwCamSymbolEntry`) referenced by 32-bit `symId` / `symIdx`.
Contains NO `KExpr` AST nodes! -/
inductive HwCamSymbolEntry where
  | sortEntry  (u : KLevel)
  | constEntry (name : KName) (us : List KLevel)
  | litEntry   (lit : KLiteral)
  | projEntry  (structName : KName) (fieldIdx : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Associative index lookup in a hardware table (`findElemIdx?`), returning `some idx` when
`target` is already present in `xs` (enabling 1-cycle CAM deduplication). -/
@[expose] def findElemIdx? {α : Type} [DecidableEq α] : List α → α → Option Nat
  | [], _ => none
  | x :: xs, target =>
    if x = target then some 0
    else (findElemIdx? xs target).map (· + 1)


/-- Enriched Hardware CAM Node Word (`PackedNodeWord`):
Augments the structural child handles `(tag, h0, h1, h2, symIdx)` with the hardware summary bit-flags
required by Zone 1 (`hasLooseBVar`, `maxLooseBVar`) and Zone 2 (`hasFVar`, `hasMVar` = Bit 58):
* `hasLooseBVar`: `true` iff any loose `.bvar` escapes this subtree (`Bit 59`),
* `hasMVar`: `true` iff any metavariable (`.mvar`, `tag = 10`) occurs in this subtree (`Bit 58`),
* `hasFVar`: `true` iff any free variable (`.fvar`, `tag = 1`) occurs in this subtree (`Bit 57`),
* `maxLooseBVar`: `0` if closed, else `1 + max_loose_bvar_idx`. -/
structure PackedNodeWord where
  tag          : Nat
  h0           : Nat
  h1           : Nat
  h2           : Nat := 0
  symIdx       : Nat := 0
  hasLooseBVar : Bool := false
  hasFVar      : Bool := false
  hasMVar      : Bool := false
  maxLooseBVar : Nat := 0
  deriving DecidableEq, Repr, Inhabited


/-- Hardware recursor $\iota$-reduction rule entry in `HwExprCAM`. -/
structure HwCamRecRuleEntry where
  recName   : KName
  ctorName  : KName
  numParams : Nat
  numFields : Nat
  rhsHandle : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Hardware constant table entry in `HwExprCAM` for 1-cycle $\delta$-unfolding and constructor lookup. -/
structure HwCamConstEntry where
  name        : KName
  symIdx      : Nat
  typeHandle  : Nat
  valHandle?  : Option Nat := none
  isCtor      : Bool := false
  inductName? : Option KName := none
  deriving DecidableEq, Repr, Inhabited

/-- Complete Hardware Hash-Consed DAG / CAM State (`HwExprCAM`) for the 4-Zone Spatial Silicon Elaborator:
Stores `PackedNodeWord` entries, symbol entries, constant entries, recursor rules, inductive parameter
counts (`inductNumParams`), and recursor universe parameter names (`recLevelParams`) with zero `KExpr`
AST side-channel. -/
structure HwExprCAM where
  nodes           : List PackedNodeWord := []
  symbols         : List HwCamSymbolEntry := []
  consts          : List HwCamConstEntry := []
  recRules        : List HwCamRecRuleEntry := []
  inductNumParams : List (KName × Nat) := []
  recLevelParams  : List (KName × List KName) := []
  deriving DecidableEq, Repr, Inhabited

/-- Empty `HwExprCAM`. -/
@[expose] def HwExprCAM.empty : HwExprCAM := {}

/-- Allocate or reuse a symbol entry in `cam.symbols`. -/
@[expose] def allocPackedSymbol (s : HwCamSymbolEntry) (cam : HwExprCAM) : Nat × HwExprCAM :=
  match findElemIdx? cam.symbols s with
  | some idx => (idx, cam)
  | none =>
    let idx := cam.symbols.length
    (idx, { cam with symbols := cam.symbols ++ [s] })

/-- Allocate or reuse a `PackedNodeWord` in `cam.nodes` via associative CAM lookup. -/
@[expose] def allocPackedNode (w : PackedNodeWord) (cam : HwExprCAM) : Nat × HwExprCAM :=
  match findElemIdx? cam.nodes w with
  | some h => (h, cam)
  | none =>
    let h := cam.nodes.length
    (h, { cam with nodes := cam.nodes ++ [w] })

/-- Look up a `PackedNodeWord` by handle (defaulting to a closed dummy word if out of bounds). -/
@[expose] def getPackedNode (cam : HwExprCAM) (h : Nat) : PackedNodeWord :=
  cam.nodes[h]?.getD { tag := 99, h0 := 0, h1 := 0 }

/-- Construct and intern an `.app` node from two existing handles `(hf, ha)`, computing its summary
bit-flags in $O(1)$ from the child words `(wf, wa)`. -/
@[expose] def mkHwCamApp (hf ha : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let wf := getPackedNode cam hf
  let wa := getPackedNode cam ha
  let maxB := Nat.max wf.maxLooseBVar wa.maxLooseBVar
  allocPackedNode
    { tag          := 4
    , h0           := hf
    , h1           := ha
    , h2           := 0
    , symIdx       := 0
    , hasLooseBVar := decide (maxB > 0)
    , hasFVar      := wf.hasFVar || wa.hasFVar
    , hasMVar      := wf.hasMVar || wa.hasMVar
    , maxLooseBVar := maxB }
    cam

/-- Construct and intern a `.lam` (`tag = 5`) or `.forallE` (`tag = 6`) binder node from `(hd, hb)`,
decrementing the body's `maxLooseBVar` across the binder in $O(1)$. -/
@[expose] def mkHwCamBinder (tag hd hb : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let wd := getPackedNode cam hd
  let wb := getPackedNode cam hb
  let maxB := Nat.max wd.maxLooseBVar (wb.maxLooseBVar - 1)
  allocPackedNode
    { tag          := tag
    , h0           := hd
    , h1           := hb
    , h2           := 0
    , symIdx       := 0
    , hasLooseBVar := decide (maxB > 0)
    , hasFVar      := wd.hasFVar || wb.hasFVar
    , hasMVar      := wd.hasMVar || wb.hasMVar
    , maxLooseBVar := maxB }
    cam

/-- Construct and intern a `.letE` (`tag = 7`) node from `(ht, hv, hb)`, decrementing `hb`'s
`maxLooseBVar` across the let-binder in $O(1)$. -/
@[expose] def mkHwCamLetE (ht hv hb : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let wt := getPackedNode cam ht
  let wv := getPackedNode cam hv
  let wb := getPackedNode cam hb
  let maxB := Nat.max (Nat.max wt.maxLooseBVar wv.maxLooseBVar) (wb.maxLooseBVar - 1)
  allocPackedNode
    { tag          := 7
    , h0           := ht
    , h1           := hv
    , h2           := hb
    , symIdx       := 0
    , hasLooseBVar := decide (maxB > 0)
    , hasFVar      := wt.hasFVar || wv.hasFVar || wb.hasFVar
    , hasMVar      := wt.hasMVar || wv.hasMVar || wb.hasMVar
    , maxLooseBVar := maxB }
    cam

/-- Construct and intern a `.proj` (`tag = 9`) node from `(hs, symIdx)`. -/
@[expose] def mkHwCamProj (hs symIdx : Nat) (cam : HwExprCAM) : Nat × HwExprCAM :=
  let ws := getPackedNode cam hs
  allocPackedNode
    { tag          := 9
    , h0           := hs
    , h1           := 0
    , h2           := 0
    , symIdx       := symIdx
    , hasLooseBVar := decide (ws.maxLooseBVar > 0)
    , hasFVar      := ws.hasFVar
    , hasMVar      := ws.hasMVar
    , maxLooseBVar := ws.maxLooseBVar }
    cam

/-- Intern a `KExpr` into `HwExprCAM`, populating `hasLooseBVar`, `hasFVar`, `hasMVar`, and
`maxLooseBVar` bottom-up in $O(1)$ per node. -/
@[expose] def internToHwExprCAM : KExpr → HwExprCAM → Nat × HwExprCAM
  | .bvar idx, cam =>
    allocPackedNode
      { tag := 0, h0 := idx, h1 := 0, hasLooseBVar := true, maxLooseBVar := idx + 1 }
      cam
  | .fvar id, cam =>
    allocPackedNode
      { tag := 1, h0 := id, h1 := 0, hasFVar := true, hasMVar := false }
      cam
  | .mvar id, cam =>
    allocPackedNode
      { tag := 10, h0 := id, h1 := 0, hasFVar := false, hasMVar := true }
      cam
  | .sort u, cam =>
    let (sIdx, cam1) := allocPackedSymbol (.sortEntry u) cam
    allocPackedNode { tag := 2, h0 := 0, h1 := 0, symIdx := sIdx } cam1
  | .const n us, cam =>
    let (sIdx, cam1) := allocPackedSymbol (.constEntry n us) cam
    allocPackedNode { tag := 3, h0 := 0, h1 := 0, symIdx := sIdx } cam1
  | .app f a, cam =>
    let (hf, cam1) := internToHwExprCAM f cam
    let (ha, cam2) := internToHwExprCAM a cam1
    mkHwCamApp hf ha cam2
  | .lam d b, cam =>
    let (hd, cam1) := internToHwExprCAM d cam
    let (hb, cam2) := internToHwExprCAM b cam1
    mkHwCamBinder 5 hd hb cam2
  | .forallE d b, cam =>
    let (hd, cam1) := internToHwExprCAM d cam
    let (hb, cam2) := internToHwExprCAM b cam1
    mkHwCamBinder 6 hd hb cam2
  | .letE t v b, cam =>
    let (ht, cam1) := internToHwExprCAM t cam
    let (hv, cam2) := internToHwExprCAM v cam1
    let (hb, cam3) := internToHwExprCAM b cam2
    mkHwCamLetE ht hv hb cam3
  | .lit l, cam =>
    let (sIdx, cam1) := allocPackedSymbol (.litEntry l) cam
    allocPackedNode { tag := 8, h0 := 0, h1 := 0, symIdx := sIdx } cam1
  | .proj structName idx s, cam =>
    let (hs, cam1) := internToHwExprCAM s cam
    let (sIdx, cam2) := allocPackedSymbol (.projEntry structName idx) cam1
    mkHwCamProj hs sIdx cam2


end Obend.Lower.ExprCAM
end
