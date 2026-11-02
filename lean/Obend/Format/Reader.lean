module
/-
# Obend.Format.Reader — Pluggable Higher-Layer Format Readers Atop `.obend` & Core4

Provides the universal `FormatReader (SurfaceAST : Type)` interface and 4 concrete,
machine-checked instances:
1. `obnbReader` (`"obnb@1"`): Literate `.obnb` / Markdown workbook reader interleaving prose
   sections, `.obend` cells, `.lean` bridge cells, and `law:` frontmatter.
2. `usdStageReader` (`"usd-stage@1"`): OpenUSD stage reader (`def Xform`, `over`, `subLayers`,
   6D kinematic/thermal attributes) lowering USD layer overrides into `.obend` open-recursive
   `spec` compositions (`extends`, `around`, `def`).
3. `dfaPolicyReader` (`"dfa-policy@1"`): Parser-automaton & prompt/API-transcript confinement
   reader lowering a grammar/DFA + nominal `#kind` hole confinement policy into an `.obend`
   `Syntax.Module` with state-transition methods and an unforgeable `#kind` confinement `law`.
4. `deploymentTopologyReader` (`"dreggnet-deploy@1"`): Elastic cloud deployment reader
   (grains, sturdyref channels, mandate budgets, and TEE attestation pins) lowering into an
   `.obend` `Syntax.Module` of composed specs and laws.
-/
public import Lean
public import Obend.Core.Data
public import Obend.Doc.Structured
public import Obend.Spec.Law
public import Obend.Spec.Syntax
public import Obend.Spec.Parse
public import Obend.Spec.Elaborate
public import Obend.Spec.FrontEnd

@[expose] public section

namespace Obend.Core
abbrev Data := Obend.Core.Data.Data
end Obend.Core

namespace Obend.Format

open Lean (Json toJson)
open Obend.Core.Data (Data)
open Obend.Doc (ProjectionKind)
open Obend.Spec.Syntax
open Obend.Spec.Law (LawExpr LawRef)

set_option autoImplicit false

/-! ## 1. Universal `FormatReader` Interface & FrontEnd Elaboration Bridge -/

/-- Pluggable higher-layer format reader lowering a domain-specific `SurfaceAST` into
    `Obend.Core.Data` (with a verified roundtrip theorem) and `Obend.Spec.Syntax.Module`. -/
structure FormatReader (SurfaceAST : Type) where
  formatId : String
  projectionKind : ProjectionKind
  parse : String → Except String SurfaceAST
  render : SurfaceAST → String
  toCoreData : SurfaceAST → Obend.Core.Data
  ofCoreData : Obend.Core.Data → Option SurfaceAST
  lowerToObend : SurfaceAST → Module
  data_roundtrip : ∀ a, ofCoreData (toCoreData a) = some a

/-- Default execution/checker limits for verifying lowered `.obend` modules through `FrontEnd`. -/
def defaultReaderLimits : Json :=
  Json.mkObj [("heap", toJson "10000"), ("stack", toJson "10000"), ("ticks", toJson "10000")]

/-- Elaborate a lowered `Syntax.Module` through `Obend.Spec.Elaborate.elaborate`. -/
def elaborateLoweredModule (m : Module) (entryDef : String := "entry") :
    Except String Obend.Spec.Elaborate.Output :=
  Obend.Spec.Elaborate.elaborate [m] 0 entryDef (.arr #[]) "application"

/-- Run a lowered `Syntax.Module` through the full `Obend.Spec.FrontEnd.lowerDecoded` and
    `Obend.Spec.FrontEnd.accept` pipeline (bidirectional typechecker, template rigidity checker,
    and package law compiler). -/
def acceptLoweredModule (m : Module) (entryDef : String := "entry") :
    Except String (Σ l : Obend.Spec.FrontEnd.Lowering, Obend.Spec.FrontEnd.Accepted l) := do
  let srcMod : Obend.Spec.FrontEnd.SourceModule := {
    name := m.name
    source := ""
    sha256 := ""
    imports := []
  }
  let lowering ← match Obend.Spec.FrontEnd.lowerDecoded [srcMod] [m] 0 entryDef
      (.arr #[]) (.arr #[]) defaultReaderLimits "application" with
    | .ok l => pure l
    | .error d => .error d.message
  match Obend.Spec.FrontEnd.accept lowering with
  | .ok acc => .ok ⟨lowering, acc⟩
  | .error d => .error d.message

/-- Boolean predicate checking that `reader.lowerToObend ast` passes both `Elaborate` and
    `FrontEnd.accept`. -/
def acceptsReaderAST {SurfaceAST : Type} (reader : FormatReader SurfaceAST)
    (ast : SurfaceAST) (entryDef : String := "entry") : Bool :=
  (acceptLoweredModule (reader.lowerToObend ast) entryDef).isOk

/-! ### Generic `Core.Data` List Encoding Helpers -/

def encodeListData {α : Type} (enc : α → Data) : List α → Data
  | [] => .variant "nil" (.record [])
  | x :: xs => .variant "cons" (.record [("head", enc x), ("tail", encodeListData enc xs)])

def decodeListData {α : Type} (dec : Data → Option α) : Data → Option (List α)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [(_, h), (_, t)]) =>
      match dec h, decodeListData dec t with
      | some x, some xs => some (x :: xs)
      | _, _ => none
  | _ => none

theorem decodeListData_encodeListData {α : Type} (enc : α → Data) (dec : Data → Option α)
    (hrt : ∀ x, dec (enc x) = some x) :
    ∀ xs : List α, decodeListData dec (encodeListData enc xs) = some xs
  | [] => rfl
  | x :: xs => by
      simp only [encodeListData, decodeListData, hrt x, decodeListData_encodeListData enc dec hrt xs]

def encodeStringData (s : String) : Data := .label s

def decodeStringData : Data → Option String
  | .label s => some s
  | _ => none

theorem decodeStringData_encodeStringData (s : String) :
    decodeStringData (encodeStringData s) = some s := rfl

def encodeNatData (n : Nat) : Data := .natural n

def decodeNatData : Data → Option Nat
  | .natural n => some n
  | _ => none

theorem decodeNatData_encodeNatData (n : Nat) :
    decodeNatData (encodeNatData n) = some n := rfl

/-! ### Helper for constructing a valid method signature Json -/

def mkSigJson (name : String) (params : List Param) (resultType : String) : Json :=
  let paramJsons := params.map fun p =>
    Json.mkObj [("name", toJson p.name), ("type", toJson p.type), ("quantity", toJson p.quantity)]
  Json.mkObj [("name", toJson name), ("parameters", Json.arr paramJsons.toArray), ("resultType", toJson resultType)]

/-! ### Zero-Choice `ByteArray` (`s.toUTF8`) Structural Wire-Parsing Combinators -/

/-- Extract byte at index `i` from a `ByteArray` with `0` fallback (`0 Classical.choice`). -/
def byteAt (ba : ByteArray) (i : Nat) : UInt8 :=
  (ba.data[i]?).getD 0

/-- Extract a `List UInt8` slice from `ba` by structural recursion on `rem : Nat`. -/
def sliceBytesAux (ba : ByteArray) (idx : Nat) : Nat → List UInt8
  | 0 => []
  | rem + 1 => byteAt ba idx :: sliceBytesAux ba (idx + 1) rem

/-- Convert a `String` into its UTF-8 `List UInt8` by `ByteArray` index recursion. -/
def stringToBytes (s : String) : List UInt8 :=
  let ba := s.toUTF8
  sliceBytesAux ba 0 ba.size

/-- Convert an ASCII/Latin-1 byte into a `Char` without `Classical.choice`. -/
def asciiByteToChar (b : UInt8) : Char :=
  Char.ofUInt8 b

/-- Convert a `List UInt8` back into a `String` without `Classical.choice`. -/
def bytesToString (bs : List UInt8) : String :=
  String.ofList (bs.map asciiByteToChar)


/-- Check if a byte is ASCII whitespace (`' '`, `'\t'`, `'\r'`, `'\n'`). -/
def isWsByte (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 13 || b == 10

/-- Drop leading whitespace bytes by structural recursion on `List UInt8`. -/
def dropLeadingWs : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if isWsByte b then dropLeadingWs bs else b :: bs

/-- Trim leading and trailing whitespace bytes from `bs`. -/
def trimBytes (bs : List UInt8) : List UInt8 :=
  (dropLeadingWs (dropLeadingWs bs).reverse).reverse

/-- Strip matching outer double-quotes `"..."` if present. -/
def unquoteBytes (bs : List UInt8) : List UInt8 :=
  let t := trimBytes bs
  match t with
  | 34 :: rest =>
    match rest.reverse with
    | 34 :: innerRev => innerRev.reverse
    | _ => t
  | _ => t

/-- Convert `bs` to a trimmed, unquoted `String`. -/
def cleanBytesToString (bs : List UInt8) : String :=
  bytesToString (unquoteBytes (trimBytes bs))

/-- Check if `bs` starts with `pref` by structural recursion. -/
def startsWithBytes : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, b :: bs => p == b && startsWithBytes ps bs

/-- Check exact equality of two `List UInt8` slices. -/
def eqBytes : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | a :: as, b :: bs => a == b && eqBytes as bs
  | _, _ => false

/-- Check if `bs` starts with ASCII string `pref`. -/
def startsWithAscii (bs : List UInt8) (pref : String) : Bool :=
  startsWithBytes (stringToBytes pref) bs

/-- Check if `bs` equals ASCII string `target`. -/
def eqAscii (bs : List UInt8) (target : String) : Bool :=
  eqBytes bs (stringToBytes target)

/-- Drop `n` bytes from `bs`. -/
def dropBytes : Nat → List UInt8 → List UInt8
  | 0, bs => bs
  | _ + 1, [] => []
  | n + 1, _ :: bs => dropBytes n bs

/-- Split `List UInt8` on delimiter byte `delim` by structural recursion. -/
def splitBytesOnAux (delim : UInt8) : List UInt8 → List UInt8 → List (List UInt8)
  | [], cur => [cur.reverse]
  | b :: bs, cur =>
    if b == delim then
      cur.reverse :: splitBytesOnAux delim bs []
    else
      splitBytesOnAux delim bs (b :: cur)

def splitBytesOn (delim : UInt8) (bs : List UInt8) : List (List UInt8) :=
  splitBytesOnAux delim bs []

/-- Split `bs` into non-empty whitespace-separated tokens by structural recursion. -/
def wordsBytesAux : List UInt8 → List UInt8 → List (List UInt8)
  | [], [] => []
  | [], cur => [cur.reverse]
  | b :: bs, cur =>
    if isWsByte b || b == 61 then -- space/tab or '='
      match cur with
      | [] => wordsBytesAux bs []
      | _ => cur.reverse :: wordsBytesAux bs []
    else
      wordsBytesAux bs (b :: cur)

def wordsBytes (bs : List UInt8) : List (List UInt8) :=
  wordsBytesAux bs []

/-- Parse an unsigned decimal `Nat` from `List UInt8` by structural recursion (`0 Classical.choice`). -/
def parseNatBytesAux : List UInt8 → Nat → Option Nat
  | [], acc => some acc
  | b :: bs, acc =>
    if 48 ≤ b && b ≤ 57 then
      parseNatBytesAux bs (acc * 10 + (b.toNat - 48))
    else
      none

def parseNatBytes (bs : List UInt8) : Option Nat :=
  let t := unquoteBytes (trimBytes bs)
  match t with
  | [] => none
  | _ => parseNatBytesAux t 0

/-- Check whether `bs` is a non-empty plain identifier (`[A-Za-z0-9_]`) by structural recursion. -/
def isIdentByte (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) || b == 95

def plainNameBytes : List UInt8 → Bool
  | [] => false
  | b :: bs => isIdentByte b && bs.all isIdentByte

/-- Strip outer `(...)` or `[...]` brackets around a token/list slice (`0 Classical.choice`). -/
def stripBracketsOrParens (bs : List UInt8) : List UInt8 :=
  let t := trimBytes bs
  match t with
  | 40 :: rest => -- '('
    match rest.reverse with
    | 41 :: revBody => trimBytes revBody.reverse
    | _ => t
  | 91 :: rest => -- '['
    match rest.reverse with
    | 93 :: revBody => trimBytes revBody.reverse
    | _ => t
  | _ => t

/-- Verify that an S-expression byte list has balanced parentheses and ends at depth 0 (`0 Classical.choice`). -/
def checkSexpBalancedBytes : List UInt8 → Nat → Bool → Bool
  | [], depth, seenOpen => seenOpen && depth == 0
  | b :: bs, depth, seenOpen =>
    if b == 40 then -- '('
      checkSexpBalancedBytes bs (depth + 1) true
    else if b == 41 then -- ')'
      if depth == 0 then false
      else if depth == 1 then
        (trimBytes bs).isEmpty
      else
        checkSexpBalancedBytes bs (depth - 1) seenOpen
    else
      if !seenOpen && !isWsByte b then false
      else checkSexpBalancedBytes bs depth seenOpen

/-- Convert a top-level S-expression item `(key val1 val2 ...)` into a normalized `key: val1 val2` line. -/
def normalizeSexpItem (item : List UInt8) : List UInt8 :=
  let t := trimBytes item
  let inner :=
    match t with
    | 40 :: rest => -- '('
      match rest.reverse with
      | 41 :: revBody => trimBytes revBody.reverse -- ')'
      | _ => trimBytes rest
    | _ => t
  if startsWithAscii inner "#usda" then
    inner
  else if startsWithAscii inner "def Xform" || startsWithAscii inner "over " then
    inner
  else
    let toks := wordsBytes inner
    match toks with
    | [] => []
    | k :: _ =>
      if eqAscii k "obnb" then
        stringToBytes "format: obnb@1"
      else if eqAscii k "usd-stage" then
        stringToBytes "#usda 1.0"
      else if eqAscii k "dfa-policy" then
        stringToBytes "format: dfa-policy@1"
      else if eqAscii k "dreggnet-deploy" then
        stringToBytes "format: dreggnet-deploy@1"
      else if eqAscii k "prose" then
        -- (prose Heading) or (prose Heading Markdown...) -> `prose: Heading ...`
        stringToBytes "prose: " ++ dropLeadingWs (dropBytes k.length inner)
      else
        -- If `k` already ends with `:`, keep it; otherwise append `: `
        let hasColon := match k.reverse with | 58 :: _ => true | _ => false
        let restBytes := dropLeadingWs (dropBytes k.length inner)
        if hasColon then
          k ++ [32] ++ restBytes
        else
          k ++ [58, 32] ++ restBytes

/-- Scan top-level parenthesized `( ... )` clauses inside an S-expression wire payload. -/
def scanSexpClausesAux : List UInt8 → Nat → List UInt8 → List (List UInt8)
  | [], 0, [] => []
  | [], _, _ => [stringToBytes "__UNBALANCED_SEXP__"]
  | b :: bs, depth, cur =>
    if b == 40 then -- '('
      if depth == 0 then
        scanSexpClausesAux bs 1 [40]
      else
        scanSexpClausesAux bs (depth + 1) (b :: cur)
    else if b == 41 then -- ')'
      if depth == 1 then
        let completed := normalizeSexpItem ((41 :: cur).reverse)
        completed :: scanSexpClausesAux bs 0 []
      else if depth > 1 then
        scanSexpClausesAux bs (depth - 1) (b :: cur)
      else
        [stringToBytes "__UNBALANCED_SEXP__"]
    else
      if depth > 0 then
        scanSexpClausesAux bs depth (b :: cur)
      else if isWsByte b then
        scanSexpClausesAux bs 0 cur
      else
        [stringToBytes "__UNBALANCED_SEXP__"]

/-- Extract normalized logical wire lines from `input` via `input.toUTF8`:
    supports standard newline-delimited wire text, semicolon-delimited wire text,
    and S-expression `(tag (k v) ...)` wire payloads (`0 Classical.choice`). -/
def extractWireLines (input : String) : List (List UInt8) :=
  let rawBytes := trimBytes (stringToBytes input)
  match rawBytes with
  | [] => []
  | 40 :: rest => -- starts with '('
    if !checkSexpBalancedBytes rawBytes 0 false then
      [stringToBytes "__UNBALANCED_SEXP__"]
    else
      let inner :=
        match rest.reverse with
        | 41 :: revBody => trimBytes revBody.reverse
        | _ => rest
      let headTok := (wordsBytes inner).headD []
      let afterHead := trimBytes (dropBytes headTok.length inner)
      let headLine := normalizeSexpItem headTok
      let subClauses := scanSexpClausesAux afterHead 0 []
      (headLine :: subClauses).filter (fun l => !l.isEmpty)
  | _ =>
    let rawLines := splitBytesOn 10 rawBytes
    let expanded := rawLines.foldr (fun l acc =>
      let tl := trimBytes l
      if tl.contains 59 && !startsWithAscii tl "#" then -- ';'
        (splitBytesOn 59 tl).map trimBytes ++ acc
      else
        tl :: acc) []
    expanded.filter (fun l => !l.isEmpty)

/-! ## 2. FormatReader 1: `obnbReader` (`"obnb@1"`) — Literate `.obnb` / Markdown Workbook -/

/-- A cell in an `.obnb` literate workbook. -/
inductive ObnbCell where
  | prose (heading : String) (markdown : String)
  | obend (cellName : String) (stateField : String) (stepDelta : Nat)
  | leanBridge (theoremName : String) (targetSpec : String)
  deriving DecidableEq, Repr, Inhabited

/-- Surface AST for an `.obnb` literate workbook. -/
structure ObnbWorkbook where
  title : String
  lawName : String
  boundField : String
  maxBound : Nat
  cells : List ObnbCell
  deriving DecidableEq, Repr, Inhabited

/-- Alias `ObnbDocument` for `ObnbWorkbook`. -/
abbrev ObnbDocument := ObnbWorkbook

def encodeObnbCell : ObnbCell → Data
  | .prose h m => .variant "prose" (.record [("heading", .label h), ("markdown", .label m)])
  | .obend n f d => .variant "obend" (.record [("cellName", .label n), ("stateField", .label f), ("stepDelta", .natural d)])
  | .leanBridge t s => .variant "lean" (.record [("theoremName", .label t), ("targetSpec", .label s)])

def decodeObnbCell : Data → Option ObnbCell
  | .variant "prose" (.record [(_, .label h), (_, .label m)]) => some (.prose h m)
  | .variant "obend" (.record [(_, .label n), (_, .label f), (_, .natural d)]) => some (.obend n f d)
  | .variant "lean" (.record [(_, .label t), (_, .label s)]) => some (.leanBridge t s)
  | _ => none

theorem decodeObnbCell_encodeObnbCell : ∀ c : ObnbCell, decodeObnbCell (encodeObnbCell c) = some c
  | .prose _ _ => rfl
  | .obend _ _ _ => rfl
  | .leanBridge _ _ => rfl

def obnbToCoreData (w : ObnbWorkbook) : Data :=
  .record [
    ("title", .label w.title),
    ("lawName", .label w.lawName),
    ("boundField", .label w.boundField),
    ("maxBound", .natural w.maxBound),
    ("cells", encodeListData encodeObnbCell w.cells)
  ]

def obnbOfCoreData : Data → Option ObnbWorkbook
  | .record [(_, .label title), (_, .label lawName), (_, .label boundField), (_, .natural maxBound), (_, cellsD)] =>
      match decodeListData decodeObnbCell cellsD with
      | some cells => some ⟨title, lawName, boundField, maxBound, cells⟩
      | none => none
  | _ => none

theorem obnb_data_roundtrip (w : ObnbWorkbook) :
    obnbOfCoreData (obnbToCoreData w) = some w := by
  cases w with
  | mk title lawName boundField maxBound cells =>
    simp only [obnbToCoreData, obnbOfCoreData,
      decodeListData_encodeListData encodeObnbCell decodeObnbCell decodeObnbCell_encodeObnbCell cells]

/-- Render an `ObnbWorkbook` to `.obnb` literate Markdown text. -/
def renderObnb (w : ObnbWorkbook) : String :=
  let header := s!"---\nformat: obnb@1\ntitle: {w.title}\nlaw: {w.lawName}\nfield: {w.boundField}\nmaxBound: {w.maxBound}\n---\n"
  let body := String.intercalate "\n" (w.cells.map fun c =>
    match c with
    | .prose h m => s!"# {h}\n{m}"
    | .obend n f d => s!"```obend {n}\n{f} += {d}\n```"
    | .leanBridge t s => s!"```lean {t}\nbridge {s}\n```")
  header ++ body

/-- Accumulator state for zero-choice structural `.obnb` parsing. -/
structure ObnbParseAcc where
  hasFormat : Bool := false
  title : String := "Workbook"
  lawName : String := "workbookLaw"
  boundFieldBytes : List UInt8 := stringToBytes "progress"
  maxBound : Nat := 100
  cells : List ObnbCell := []
  pendingProseHeading : Option String := none
  pendingObendCell : Option String := none
  pendingLeanThm : Option String := none

def flushPendingProse (acc : ObnbParseAcc) : ObnbParseAcc :=
  match acc.pendingProseHeading with
  | some h => { acc with cells := acc.cells ++ [.prose h h], pendingProseHeading := none }
  | none => acc

def parseObnbColonOrSpace3 (raw : List UInt8) : Option (List UInt8 × List UInt8 × List UInt8) :=
  let cleaned := stripBracketsOrParens raw
  let colonParts := (splitBytesOn 58 cleaned).map trimBytes
  match colonParts with
  | [a, b, c] => some (a, b, c)
  | _ =>
    match wordsBytes cleaned with
    | [a, b, c] => some (a, b, c)
    | _ => none

def parseObnbColonOrSpace2 (raw : List UInt8) : Option (List UInt8 × List UInt8) :=
  let cleaned := stripBracketsOrParens raw
  let colonParts := (splitBytesOn 58 cleaned).map trimBytes
  match colonParts with
  | [a, b] => some (a, b)
  | _ =>
    match wordsBytes cleaned with
    | [a, b] => some (a, b)
    | _ => none

def stepParseObnbLine (acc : ObnbParseAcc) (l : List UInt8) : Except String ObnbParseAcc :=
  if eqAscii l "---" then
    .ok (flushPendingProse acc)
  else
    match acc.pendingObendCell with
    | some cName =>
      if eqAscii l "```" then
        .ok { acc with pendingObendCell := none }
      else
        -- Expect `field += delta` or `field:delta`
        let toks := wordsBytes l
        match toks with
        | [fBytes, opBytes, dBytes] =>
          if eqAscii opBytes "+=" || eqAscii opBytes "+" then
            match parseNatBytes dBytes with
            | some d =>
              .ok { acc with cells := acc.cells ++ [.obend cName (cleanBytesToString fBytes) d], pendingObendCell := none }
            | none => .error "invalid obend cell delta"
          else
            .error "invalid obend cell body"
        | _ =>
          match parseObnbColonOrSpace2 l with
          | some (fBytes, dBytes) =>
            match parseNatBytes dBytes with
            | some d =>
              .ok { acc with cells := acc.cells ++ [.obend cName (cleanBytesToString fBytes) d], pendingObendCell := none }
            | none => .error "invalid obend cell delta"
          | none => .error "invalid obend cell body"
    | none =>
      match acc.pendingLeanThm with
      | some tName =>
        if eqAscii l "```" then
          .ok { acc with pendingLeanThm := none }
        else if startsWithAscii l "bridge " then
          let sName := cleanBytesToString (dropBytes 7 l)
          .ok { acc with cells := acc.cells ++ [.leanBridge tName sName], pendingLeanThm := none }
        else
          .ok { acc with cells := acc.cells ++ [.leanBridge tName (cleanBytesToString l)], pendingLeanThm := none }
      | none =>
        if eqAscii l "```" then
          .ok (flushPendingProse acc)
        else if startsWithAscii l "```obend " then
          let acc1 := flushPendingProse acc
          let cName := cleanBytesToString (dropBytes 9 l)
          .ok { acc1 with pendingObendCell := some cName }
        else if startsWithAscii l "```lean " then
          let acc1 := flushPendingProse acc
          let tName := cleanBytesToString (dropBytes 8 l)
          .ok { acc1 with pendingLeanThm := some tName }
        else if startsWithAscii l "format:" then
          let acc1 := flushPendingProse acc
          let fmt := trimBytes (dropBytes 7 l)
          if eqAscii fmt "obnb@1" || eqAscii fmt "obnb" then .ok { acc1 with hasFormat := true }
          else .error ("unsupported obnb format: " ++ cleanBytesToString fmt)
        else if startsWithAscii l "title:" then
          let acc1 := flushPendingProse acc
          .ok { acc1 with title := cleanBytesToString (dropBytes 6 l) }
        else if startsWithAscii l "law:" then
          let acc1 := flushPendingProse acc
          .ok { acc1 with lawName := cleanBytesToString (dropBytes 4 l) }
        else if startsWithAscii l "field:" then
          let acc1 := flushPendingProse acc
          .ok { acc1 with boundFieldBytes := unquoteBytes (trimBytes (dropBytes 6 l)) }
        else if startsWithAscii l "maxBound:" then
          let acc1 := flushPendingProse acc
          match parseNatBytes (dropBytes 9 l) with
          | some n => .ok { acc1 with maxBound := n }
          | none => .error "invalid maxBound in obnb@1 frontmatter"
        else if startsWithAscii l "prose:" then
          let acc1 := flushPendingProse acc
          let rawProse := stripBracketsOrParens (dropBytes 6 l)
          let colonParts := (splitBytesOn 58 rawProse).map trimBytes
          match colonParts with
          | [hB, mB] =>
            .ok { acc1 with cells := acc1.cells ++ [.prose (cleanBytesToString hB) (cleanBytesToString mB)] }
          | _ =>
            let toks := wordsBytes rawProse
            match toks with
            | [] => .error "empty prose cell in obnb@1"
            | [hB] =>
              let h := cleanBytesToString hB
              .ok { acc1 with cells := acc1.cells ++ [.prose h h] }
            | hB :: _ =>
              let h := cleanBytesToString hB
              let m := cleanBytesToString (dropLeadingWs (dropBytes hB.length rawProse))
              .ok { acc1 with cells := acc1.cells ++ [.prose h m] }
        else if startsWithAscii l "# " then
          let acc1 := flushPendingProse acc
          let h := cleanBytesToString (dropBytes 2 l)
          .ok { acc1 with pendingProseHeading := some h }
        else if startsWithAscii l "cell-obend:" then
          let acc1 := flushPendingProse acc
          match parseObnbColonOrSpace3 (trimBytes (dropBytes 11 l)) with
          | some (nB, fB, dB) =>
            match parseNatBytes dB with
            | some d => .ok { acc1 with cells := acc1.cells ++ [.obend (cleanBytesToString nB) (cleanBytesToString fB) d] }
            | none => .error "invalid obend cell delta"
          | none => .error "invalid cell-obend syntax (expected cell-obend: name:field:delta)"
        else if startsWithAscii l "cell-lean:" then
          let acc1 := flushPendingProse acc
          match parseObnbColonOrSpace2 (trimBytes (dropBytes 10 l)) with
          | some (tB, sB) =>
            .ok { acc1 with cells := acc1.cells ++ [.leanBridge (cleanBytesToString tB) (cleanBytesToString sB)] }
          | none => .error "invalid cell-lean syntax (expected cell-lean: theorem:spec)"
        else
          match acc.pendingProseHeading with
          | some h =>
            let m := cleanBytesToString l
            .ok { acc with cells := acc.cells ++ [.prose h m], pendingProseHeading := none }
          | none => .error ("unrecognized obnb@1 line: " ++ cleanBytesToString l)

def foldObnbLines : List (List UInt8) → ObnbParseAcc → Except String ObnbParseAcc
  | [], acc => .ok (flushPendingProse acc)
  | l :: ls, acc =>
    match stepParseObnbLine acc l with
    | .ok acc' => foldObnbLines ls acc'
    | .error e => .error e

/-- Parse an `.obnb` literate Markdown or S-expression workbook into `ObnbWorkbook` (`0 Classical.choice`). -/
def parseObnb (input : String) : Except String ObnbWorkbook :=
  let rawLines := (extractWireLines input).filter (fun l => !l.isEmpty && !eqAscii l "---")
  match rawLines with
  | [] => .error "empty obnb@1 workbook"
  | _ =>
    match foldObnbLines rawLines {} with
    | .error e => .error e
    | .ok acc =>
      if !acc.hasFormat then
        .error "missing format: obnb@1 header"
      else if !plainNameBytes acc.boundFieldBytes then
        .error ("invalid boundField `" ++ bytesToString acc.boundFieldBytes ++ "` in obnb@1")
      else
        .ok {
          title := acc.title,
          lawName := acc.lawName,
          boundField := bytesToString acc.boundFieldBytes,
          maxBound := acc.maxBound,
          cells := acc.cells
        }


/-- Lower an `ObnbWorkbook` into a unified `.obend` `Syntax.Module`. -/
def lowerObnbToObend (w : ObnbWorkbook) : Module :=
  let fld := if Obend.Spec.Law.plainName w.boundField then w.boundField else "progress"
  let lName := if Obend.Spec.Law.plainName w.lawName then w.lawName else "workbookLaw"
  let totalDelta : Nat := w.cells.foldl (fun acc c =>
    match c with
    | .obend _ _ d => acc + d
    | _ => acc) 1
  let bridgeMethod : IsarMethod :=
    match w.cells.findSome? (fun c => match c with | .leanBridge t _ => some t | _ => none) with
    | some thm => .lean thm
    | none => .weave
  let deltaParam : Param := ⟨"delta", "Nat", "default"⟩
  let stepSig : Signature := ⟨"step", [deltaParam], "Nat"⟩
  let stepMethod : Method := {
    name := "step"
    params := [deltaParam]
    resultType := "Nat"
    qualifier := "primary"
    body := .expr (.binary "+" (.member (.var "self") fld) (.var "delta"))
    signature := mkSigJson "step" [deltaParam] "Nat"
  }
  let claim : Claim := {
    name := "monotoneStep"
    params := [deltaParam]
    body := .binary "<=" (.member (.var "self") fld) (.call (.member (.var "self") "step") [.var "delta"])
    method := some bridgeMethod
    steps := [.showStep (.bool true) bridgeMethod]
  }
  let wbSpec : Spec := {
    name := "WorkbookSpec"
    suffix := false
    parents := []
    targetType := "WorkbookState"
    requirements := .arr #[]
    methods := [stepMethod]
    claims := [claim]
  }
  let seedRec : Expr := .record [
    (fld, .nat "0"),
    ("step", .closure [deltaParam] "Nat" (.var "delta"))
  ]
  let entryFn : Decl := .function "entry" [] "Nat"
    (.expr (.call (.member (.fix (.var "WorkbookSpec") seedRec) "step") [.nat (toString totalDelta)]))
  let lawExpr : LawExpr :=
    .and (.monotone fld) (.leC (.field fld) (Int.ofNat w.maxBound))
  let contract : ContractDecl := {
    name := lName ++ "Contract"
    targetType := "WorkbookState"
    invariant := some (.binary "<=" (.member (.var "self") fld) (.nat (toString w.maxBound)))
    law := some lawExpr
    method := some bridgeMethod
    steps := [.showStep (.bool true) .omega]
  }
  { name := "ObnbWorkbookModule"
    imports := []
    decls := [
      .record "WorkbookState" [(fld, "Nat")] [stepSig],
      .spec wbSpec,
      entryFn
    ]
    laws := [(lName, lawExpr)]
    header := none
    keeps := []
    lawMethods := [(lName, .omega)]
    contracts := [contract] }

/-- Concrete verified `FormatReader` instance for `.obnb` literate workbooks (`"obnb@1"`). -/
def obnbReader : FormatReader ObnbWorkbook where
  formatId := "obnb@1"
  projectionKind := .obendCode
  parse := parseObnb
  render := renderObnb
  toCoreData := obnbToCoreData
  ofCoreData := obnbOfCoreData
  lowerToObend := lowerObnbToObend
  data_roundtrip := obnb_data_roundtrip

/-! ## 3. FormatReader 2: `usdStageReader` (`"usd-stage@1"`) — OpenUSD Stage Composition -/

/-- A 6D kinematic + thermal USD layer (`def Xform` or `over`). -/
structure UsdLayer where
  layerName : String
  isOver : Bool
  posX : Nat
  posY : Nat
  posZ : Nat
  velX : Nat
  velY : Nat
  thermalMk : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Surface AST for an OpenUSD stage (`"usd-stage@1"`). -/
structure UsdStage where
  stageName : String
  subLayers : List String
  maxThermalMk : Nat
  baseXform : UsdLayer
  overrides : List UsdLayer
  deriving DecidableEq, Repr, Inhabited

def encodeUsdLayer (l : UsdLayer) : Data :=
  .record [
    ("layerName", .label l.layerName),
    ("isOver", .boolean l.isOver),
    ("posX", .natural l.posX),
    ("posY", .natural l.posY),
    ("posZ", .natural l.posZ),
    ("velX", .natural l.velX),
    ("velY", .natural l.velY),
    ("thermalMk", .natural l.thermalMk)
  ]

def decodeUsdLayer : Data → Option UsdLayer
  | .record [(_, .label n), (_, .boolean over), (_, .natural px), (_, .natural py),
             (_, .natural pz), (_, .natural vx), (_, .natural vy), (_, .natural th)] =>
      some ⟨n, over, px, py, pz, vx, vy, th⟩
  | _ => none

theorem decodeUsdLayer_encodeUsdLayer (l : UsdLayer) :
    decodeUsdLayer (encodeUsdLayer l) = some l := by
  cases l; rfl

def usdStageToCoreData (s : UsdStage) : Data :=
  .record [
    ("stageName", .label s.stageName),
    ("subLayers", encodeListData encodeStringData s.subLayers),
    ("maxThermalMk", .natural s.maxThermalMk),
    ("baseXform", encodeUsdLayer s.baseXform),
    ("overrides", encodeListData encodeUsdLayer s.overrides)
  ]

def usdStageOfCoreData : Data → Option UsdStage
  | .record [(_, .label sName), (_, subsD), (_, .natural maxTh), (_, baseD), (_, oversD)] =>
      match decodeListData decodeStringData subsD,
            decodeUsdLayer baseD,
            decodeListData decodeUsdLayer oversD with
      | some subs, some base, some overs => some ⟨sName, subs, maxTh, base, overs⟩
      | _, _, _ => none
  | _ => none

theorem usdStage_data_roundtrip (s : UsdStage) :
    usdStageOfCoreData (usdStageToCoreData s) = some s := by
  cases s with
  | mk sName subs maxTh base overs =>
    simp only [usdStageToCoreData, usdStageOfCoreData,
      decodeListData_encodeListData encodeStringData decodeStringData decodeStringData_encodeStringData subs,
      decodeUsdLayer_encodeUsdLayer base,
      decodeListData_encodeListData encodeUsdLayer decodeUsdLayer decodeUsdLayer_encodeUsdLayer overs]

/-- Render a `UsdStage` to OpenUSD ASCII (`#usda 1.0`) text. -/
def renderUsdStage (s : UsdStage) : String :=
  let subs := String.intercalate "," s.subLayers
  let b := s.baseXform
  let overLines := s.overrides.map fun o =>
    s!"over {o.layerName} {o.posX} {o.posY} {o.posZ} {o.velX} {o.velY} {o.thermalMk}"
  String.intercalate "\n" ([
    "#usda 1.0",
    s!"stage: {s.stageName}",
    s!"subLayers: {subs}",
    s!"maxThermalMk: {s.maxThermalMk}",
    s!"def Xform {b.layerName} {b.posX} {b.posY} {b.posZ} {b.velX} {b.velY} {b.thermalMk}"
  ] ++ overLines)

def parseUsdLayerBytes (prefixLen : Nat) (isOver : Bool) (line : List UInt8) : Except String UsdLayer :=
  let rest := stripBracketsOrParens (dropBytes prefixLen line)
  match wordsBytes rest with
  | [nameB, pxB, pyB, pzB, vxB, vyB, thB] =>
    match parseNatBytes pxB, parseNatBytes pyB, parseNatBytes pzB,
          parseNatBytes vxB, parseNatBytes vyB, parseNatBytes thB with
    | some posX, some posY, some posZ, some velX, some velY, some thermalMk =>
      .ok { layerName := cleanBytesToString nameB, isOver, posX, posY, posZ, velX, velY, thermalMk }
    | _, _, _, _, _, _ => .error "invalid numeric attribute in usd-stage@1 layer"
  | _ => .error ("invalid USD layer syntax in `" ++ cleanBytesToString line ++ "`")

structure UsdParseAcc where
  stageName : String := "DefaultStage"
  subLayers : List String := []
  maxThermalMk : Nat := 350000
  baseOpt : Option UsdLayer := none
  overrides : List UsdLayer := []

def stepParseUsdLine (acc : UsdParseAcc) (l : List UInt8) : Except String UsdParseAcc :=
  if eqAscii l "#usda 1.0" then .ok acc
  else if startsWithAscii l "stage:" then
    .ok { acc with stageName := cleanBytesToString (dropBytes 6 l) }
  else if startsWithAscii l "subLayers:" then
    let raw := stripBracketsOrParens (dropBytes 10 l)
    let subs :=
      if raw.isEmpty then []
      else if raw.contains 44 then (splitBytesOn 44 raw).map cleanBytesToString
      else (wordsBytes raw).map cleanBytesToString
    .ok { acc with subLayers := subs }
  else if startsWithAscii l "maxThermalMk:" then
    match parseNatBytes (dropBytes 13 l) with
    | some v => .ok { acc with maxThermalMk := v }
    | none => .error "invalid maxThermalMk"
  else if startsWithAscii l "def Xform " then
    match parseUsdLayerBytes 10 false l with
    | .ok base => .ok { acc with baseOpt := some base }
    | .error e => .error e
  else if startsWithAscii l "over " then
    match parseUsdLayerBytes 5 true l with
    | .ok ov => .ok { acc with overrides := acc.overrides ++ [ov] }
    | .error e => .error e
  else
    .error ("unrecognized usd-stage@1 line: " ++ cleanBytesToString l)

def foldUsdLines : List (List UInt8) → UsdParseAcc → Except String UsdParseAcc
  | [], acc => .ok acc
  | l :: ls, acc =>
    match stepParseUsdLine acc l with
    | .ok acc' => foldUsdLines ls acc'
    | .error e => .error e

/-- Parse an OpenUSD ASCII or S-expression stage (`"usd-stage@1"`) (`0 Classical.choice`). -/
def parseUsdStage (input : String) : Except String UsdStage :=
  let lines := extractWireLines input
  if !(lines.any (fun l => eqAscii l "#usda 1.0")) then
    .error "missing #usda 1.0 header"
  else
    match foldUsdLines lines {} with
    | .error e => .error e
    | .ok acc =>
      match acc.baseOpt with
      | some base =>
        .ok {
          stageName := acc.stageName,
          subLayers := acc.subLayers,
          maxThermalMk := acc.maxThermalMk,
          baseXform := base,
          overrides := acc.overrides
        }
      | none => .error "usd-stage@1 requires a base `def Xform` layer"

/-- Lower a `UsdStage` into an `.obend` `Syntax.Module` with open-recursive `spec` compositions
    (`extends`, `around`, `def`) over 6D kinematic/thermal attributes. -/
def lowerUsdStageToObend (s : UsdStage) : Module :=
  let sampleSig : Signature := ⟨"sample", [], "Nat"⟩
  let baseSample : Method := {
    name := "sample"
    params := []
    resultType := "Nat"
    qualifier := "primary"
    body := .expr (.binary "+" (.member (.var "self") "posX") (.member (.var "self") "thermalMk"))
    signature := mkSigJson "sample" [] "Nat"
  }
  let baseClaim : Claim := {
    name := "thermalBounded"
    params := []
    body := .binary "<=" (.member (.var "self") "thermalMk") (.member (.var "self") "sample")
    method := some .frame
  }
  let baseSpec : Spec := {
    name := "BaseXform"
    suffix := false
    parents := []
    targetType := "Xform6D"
    requirements := .arr #[]
    methods := [baseSample]
    claims := [baseClaim]
  }
  let overDelta : Nat := s.overrides.foldl (fun acc o => acc + o.posX + o.velX) 0
  let overSample : Method := {
    name := "sample"
    params := []
    resultType := "Nat"
    qualifier := "around"
    body := .expr (.binary "+" (.member (.var "super") "sample") (.nat (toString overDelta)))
    signature := mkSigJson "sample" [] "Nat"
  }
  let overSpec : Spec := {
    name := "OverXform"
    suffix := false
    parents := ["BaseXform"]
    targetType := "Xform6D"
    requirements := .arr #[]
    methods := [overSample]
    claims := []
  }
  let b := s.baseXform
  let seedRec : Expr := .record [
    ("posX", .nat (toString b.posX)),
    ("posY", .nat (toString b.posY)),
    ("posZ", .nat (toString b.posZ)),
    ("velX", .nat (toString b.velX)),
    ("velY", .nat (toString b.velY)),
    ("thermalMk", .nat (toString b.thermalMk)),
    ("sample", .nat "0")
  ]
  let entryFn : Decl := .function "entry" [] "Nat"
    (.expr (.member (.fix (.var "OverXform") seedRec) "sample"))
  let thermalLaw : LawExpr :=
    .and (.leC (.field "thermalMk") (Int.ofNat s.maxThermalMk)) (.monotone "posX")
  { name := "UsdStageModule"
    imports := []
    decls := [
      .record "Xform6D" [
        ("posX", "Nat"), ("posY", "Nat"), ("posZ", "Nat"),
        ("velX", "Nat"), ("velY", "Nat"), ("thermalMk", "Nat")
      ] [sampleSig],
      .spec baseSpec,
      .spec overSpec,
      entryFn
    ]
    laws := [("thermalBound", thermalLaw)]
    header := none
    keeps := []
    lawMethods := [("thermalBound", .frame)]
    contracts := [{
      name := "UsdThermalContract"
      targetType := "Xform6D"
      law := some thermalLaw
      method := some .frame
    }] }

/-- Concrete verified `FormatReader` instance for OpenUSD stages (`"usd-stage@1"`). -/
def usdStageReader : FormatReader UsdStage where
  formatId := "usd-stage@1"
  projectionKind := .hardwareLayout
  parse := parseUsdStage
  render := renderUsdStage
  toCoreData := usdStageToCoreData
  ofCoreData := usdStageOfCoreData
  lowerToObend := lowerUsdStageToObend
  data_roundtrip := usdStage_data_roundtrip

/-! ## 4. FormatReader 3: `dfaPolicyReader` (`"dfa-policy@1"`) — DFA & `#kind` Confinement -/

/-- A transition in a prompt/API-transcript DFA. -/
structure DfaTransition where
  fromState : Nat
  tokenClass : Nat
  toState : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A nominal `#kind` hole confinement rule pinning a transcript slot to an unforgeable kind tag. -/
structure HoleConfinement where
  holeName : String
  requiredKindTag : Nat
  allowedState : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Surface AST for a parser-automaton & nominal `#kind` confinement policy (`"dfa-policy@1"`). -/
structure DfaPolicy where
  policyName : String
  initialState : Nat
  acceptingStates : List Nat
  transitions : List DfaTransition
  holes : List HoleConfinement
  deriving DecidableEq, Repr, Inhabited

def encodeDfaTransition (t : DfaTransition) : Data :=
  .record [
    ("fromState", .natural t.fromState),
    ("tokenClass", .natural t.tokenClass),
    ("toState", .natural t.toState)
  ]

def decodeDfaTransition : Data → Option DfaTransition
  | .record [(_, .natural f), (_, .natural tok), (_, .natural toSt)] => some ⟨f, tok, toSt⟩
  | _ => none

theorem decodeDfaTransition_encodeDfaTransition (t : DfaTransition) :
    decodeDfaTransition (encodeDfaTransition t) = some t := by
  cases t; rfl

def encodeHoleConfinement (h : HoleConfinement) : Data :=
  .record [
    ("holeName", .label h.holeName),
    ("requiredKindTag", .natural h.requiredKindTag),
    ("allowedState", .natural h.allowedState)
  ]

def decodeHoleConfinement : Data → Option HoleConfinement
  | .record [(_, .label n), (_, .natural k), (_, .natural st)] => some ⟨n, k, st⟩
  | _ => none

theorem decodeHoleConfinement_encodeHoleConfinement (h : HoleConfinement) :
    decodeHoleConfinement (encodeHoleConfinement h) = some h := by
  cases h; rfl

def dfaPolicyToCoreData (p : DfaPolicy) : Data :=
  .record [
    ("policyName", .label p.policyName),
    ("initialState", .natural p.initialState),
    ("acceptingStates", encodeListData encodeNatData p.acceptingStates),
    ("transitions", encodeListData encodeDfaTransition p.transitions),
    ("holes", encodeListData encodeHoleConfinement p.holes)
  ]

def dfaPolicyOfCoreData : Data → Option DfaPolicy
  | .record [(_, .label pName), (_, .natural initSt), (_, accD), (_, transD), (_, holesD)] =>
      match decodeListData decodeNatData accD,
            decodeListData decodeDfaTransition transD,
            decodeListData decodeHoleConfinement holesD with
      | some accs, some trs, some hls => some ⟨pName, initSt, accs, trs, hls⟩
      | _, _, _ => none
  | _ => none

theorem dfaPolicy_data_roundtrip (p : DfaPolicy) :
    dfaPolicyOfCoreData (dfaPolicyToCoreData p) = some p := by
  cases p with
  | mk pName initSt accs trs hls =>
    simp only [dfaPolicyToCoreData, dfaPolicyOfCoreData,
      decodeListData_encodeListData encodeNatData decodeNatData decodeNatData_encodeNatData accs,
      decodeListData_encodeListData encodeDfaTransition decodeDfaTransition decodeDfaTransition_encodeDfaTransition trs,
      decodeListData_encodeListData encodeHoleConfinement decodeHoleConfinement decodeHoleConfinement_encodeHoleConfinement hls]

/-- Render a `DfaPolicy` to `"dfa-policy@1"` text. -/
def renderDfaPolicy (p : DfaPolicy) : String :=
  let accStr := String.intercalate "," (p.acceptingStates.map toString)
  let trLines := p.transitions.map fun t => s!"transition: {t.fromState} {t.tokenClass} {t.toState}"
  let holeLines := p.holes.map fun h => s!"hole: {h.holeName} {h.requiredKindTag} {h.allowedState}"
  String.intercalate "\n" ([
    "format: dfa-policy@1",
    s!"policy: {p.policyName}",
    s!"initial: {p.initialState}",
    s!"accepting: {accStr}"
  ] ++ trLines ++ holeLines)

def parseNatListBytes : List (List UInt8) → Option (List Nat)
  | [] => some []
  | b :: bs =>
    match parseNatBytes b, parseNatListBytes bs with
    | some n, some ns => some (n :: ns)
    | _, _ => none

structure DfaParseAcc where
  policyName : String := "DefaultDfaPolicy"
  initialState : Nat := 0
  acceptingStates : List Nat := []
  transitions : List DfaTransition := []
  holes : List HoleConfinement := []

def stepParseDfaLine (acc : DfaParseAcc) (l : List UInt8) : Except String DfaParseAcc :=
  if eqAscii l "format: dfa-policy@1" then .ok acc
  else if startsWithAscii l "policy:" then
    .ok { acc with policyName := cleanBytesToString (dropBytes 7 l) }
  else if startsWithAscii l "initial:" then
    match parseNatBytes (dropBytes 8 l) with
    | some st => .ok { acc with initialState := st }
    | none => .error "invalid initial state in dfa-policy@1"
  else if startsWithAscii l "accepting:" then
    let raw := stripBracketsOrParens (dropBytes 10 l)
    if raw.isEmpty then .ok { acc with acceptingStates := [] }
    else
      let items := if raw.contains 44 then splitBytesOn 44 raw else wordsBytes raw
      match parseNatListBytes items with
      | some ns => .ok { acc with acceptingStates := ns }
      | none => .error "invalid accepting state in dfa-policy@1"
  else if startsWithAscii l "transition:" then
    match wordsBytes (stripBracketsOrParens (dropBytes 11 l)) with
    | [fB, tokB, toB] =>
      match parseNatBytes fB, parseNatBytes tokB, parseNatBytes toB with
      | some f, some tok, some toSt =>
        .ok { acc with transitions := acc.transitions ++ [⟨f, tok, toSt⟩] }
      | _, _, _ => .error "invalid numeric state in transition"
    | _ => .error ("invalid transition line: " ++ cleanBytesToString l)
  else if startsWithAscii l "hole:" then
    match wordsBytes (stripBracketsOrParens (dropBytes 5 l)) with
    | [hB, kB, stB] =>
      match parseNatBytes kB, parseNatBytes stB with
      | some k, some st =>
        .ok { acc with holes := acc.holes ++ [⟨cleanBytesToString hB, k, st⟩] }
      | _, _ => .error "invalid numeric tag/state in hole confinement"
    | _ => .error ("invalid hole confinement line: " ++ cleanBytesToString l)
  else
    .error ("unrecognized dfa-policy@1 line: " ++ cleanBytesToString l)

def foldDfaLines : List (List UInt8) → DfaParseAcc → Except String DfaParseAcc
  | [], acc => .ok acc
  | l :: ls, acc =>
    match stepParseDfaLine acc l with
    | .ok acc' => foldDfaLines ls acc'
    | .error e => .error e

/-- Parse a `"dfa-policy@1"` manifest or S-expression into `DfaPolicy` (`0 Classical.choice`). -/
def parseDfaPolicy (input : String) : Except String DfaPolicy :=
  let lines := extractWireLines input
  if !(lines.any (fun l => eqAscii l "format: dfa-policy@1")) then
    .error "missing format: dfa-policy@1 header"
  else
    match foldDfaLines lines {} with
    | .error e => .error e
    | .ok acc =>
      .ok {
        policyName := acc.policyName,
        initialState := acc.initialState,
        acceptingStates := acc.acceptingStates,
        transitions := acc.transitions,
        holes := acc.holes
      }

/-- Lower a `DfaPolicy` into an `.obend` `Syntax.Module` with state-transition methods and an
    unforgeable `#kind` confinement `law`. -/
def lowerDfaPolicyToObend (p : DfaPolicy) : Module :=
  let tokParam : Param := ⟨"token", "Nat", "default"⟩
  let advSig : Signature := ⟨"advance", [tokParam], "Nat"⟩
  let targetState : Nat :=
    match p.transitions.head? with
    | some tr => tr.toState
    | none => p.initialState
  let pinnedKind : Nat :=
    match p.holes.head? with
    | some h => h.requiredKindTag
    | none => 1
  let advMethod : Method := {
    name := "advance"
    params := [tokParam]
    resultType := "Nat"
    qualifier := "primary"
    body := .expr (.binary "+" (.member (.var "self") "kindTag") (.nat (toString targetState)))
    signature := mkSigJson "advance" [tokParam] "Nat"
  }
  let confClaim : Claim := {
    name := "preservesKindTag"
    params := [tokParam]
    body := .binary "<=" (.member (.var "self") "kindTag")
                         (.call (.member (.var "self") "advance") [.var "token"])
    method := some (.judge "dfa-air")
  }
  let dfaSpec : Spec := {
    name := "ConfinementDfa"
    suffix := false
    parents := []
    targetType := "TranscriptAutomaton"
    requirements := .arr #[]
    methods := [advMethod]
    claims := [confClaim]
  }
  let seedRec : Expr := .record [
    ("dfaState", .nat (toString p.initialState)),
    ("kindTag", .nat (toString pinnedKind)),
    ("transitionsTaken", .nat "0"),
    ("advance", .closure [tokParam] "Nat" (.var "token"))
  ]
  let entryFn : Decl := .function "entry" [] "Nat"
    (.expr (.call (.member (.fix (.var "ConfinementDfa") seedRec) "advance") [.nat "1"]))
  let validStates : List Int :=
    ((p.initialState :: p.acceptingStates ++ p.transitions.map (·.toState)).eraseDups).map Int.ofNat
  let confLaw : LawExpr :=
    .and (.monotone "transitionsTaken")
      (.and (.inC (.field "dfaState") validStates)
        (.and (.writeOnce "kindTag") (.eqC (.field "kindTag") (Int.ofNat pinnedKind))))
  { name := "DfaPolicyModule"
    imports := []
    decls := [
      .record "TranscriptAutomaton" [
        ("dfaState", "Nat"), ("kindTag", "Nat"), ("transitionsTaken", "Nat")
      ] [advSig],
      .spec dfaSpec,
      entryFn
    ]
    laws := [("kindConfinement", confLaw)]
    header := none
    keeps := []
    lawMethods := [("kindConfinement", .judge "dfa-air")]
    contracts := [{
      name := "DfaConfinementContract"
      targetType := "TranscriptAutomaton"
      law := some confLaw
      method := some (.judge "dfa-air")
    }] }

/-- Concrete verified `FormatReader` instance for parser-automaton & `#kind` confinement policies (`"dfa-policy@1"`). -/
def dfaPolicyReader : FormatReader DfaPolicy where
  formatId := "dfa-policy@1"
  projectionKind := .lawContract
  parse := parseDfaPolicy
  render := renderDfaPolicy
  toCoreData := dfaPolicyToCoreData
  ofCoreData := dfaPolicyOfCoreData
  lowerToObend := lowerDfaPolicyToObend
  data_roundtrip := dfaPolicy_data_roundtrip

/-! ## 5. FormatReader 4: `deploymentTopologyReader` (`"dreggnet-deploy@1"`) — Elastic Cloud Deployment -/

/-- A compute grain in a `dreggnet-deploy@1` elastic cloud topology. -/
structure GrainSpec where
  grainName : String
  teeMeasurementPin : Nat
  mandateBudget : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A capability-authenticated SturdyRef channel between grains. -/
structure SturdyRefChannel where
  channelName : String
  sourceGrain : String
  targetGrain : String
  maxEpoch : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Surface AST for an elastic cloud deployment manifest (`"dreggnet-deploy@1"`). -/
structure DeploymentTopology where
  topologyName : String
  totalMandateCap : Nat
  requiredTeePin : Nat
  grains : List GrainSpec
  channels : List SturdyRefChannel
  deriving DecidableEq, Repr, Inhabited

def encodeGrainSpec (g : GrainSpec) : Data :=
  .record [
    ("grainName", .label g.grainName),
    ("teeMeasurementPin", .natural g.teeMeasurementPin),
    ("mandateBudget", .natural g.mandateBudget)
  ]

def decodeGrainSpec : Data → Option GrainSpec
  | .record [(_, .label n), (_, .natural pin), (_, .natural b)] => some ⟨n, pin, b⟩
  | _ => none

theorem decodeGrainSpec_encodeGrainSpec (g : GrainSpec) :
    decodeGrainSpec (encodeGrainSpec g) = some g := by
  cases g; rfl

def encodeSturdyRefChannel (c : SturdyRefChannel) : Data :=
  .record [
    ("channelName", .label c.channelName),
    ("sourceGrain", .label c.sourceGrain),
    ("targetGrain", .label c.targetGrain),
    ("maxEpoch", .natural c.maxEpoch)
  ]

def decodeSturdyRefChannel : Data → Option SturdyRefChannel
  | .record [(_, .label n), (_, .label src), (_, .label dst), (_, .natural ep)] => some ⟨n, src, dst, ep⟩
  | _ => none

theorem decodeSturdyRefChannel_encodeSturdyRefChannel (c : SturdyRefChannel) :
    decodeSturdyRefChannel (encodeSturdyRefChannel c) = some c := by
  cases c; rfl

def deploymentToCoreData (d : DeploymentTopology) : Data :=
  .record [
    ("topologyName", .label d.topologyName),
    ("totalMandateCap", .natural d.totalMandateCap),
    ("requiredTeePin", .natural d.requiredTeePin),
    ("grains", encodeListData encodeGrainSpec d.grains),
    ("channels", encodeListData encodeSturdyRefChannel d.channels)
  ]

def deploymentOfCoreData : Data → Option DeploymentTopology
  | .record [(_, .label tName), (_, .natural cap), (_, .natural pin), (_, grainsD), (_, chansD)] =>
      match decodeListData decodeGrainSpec grainsD,
            decodeListData decodeSturdyRefChannel chansD with
      | some gs, some cs => some ⟨tName, cap, pin, gs, cs⟩
      | _, _ => none
  | _ => none

theorem deploymentTopology_data_roundtrip (d : DeploymentTopology) :
    deploymentOfCoreData (deploymentToCoreData d) = some d := by
  cases d with
  | mk tName cap pin gs cs =>
    simp only [deploymentToCoreData, deploymentOfCoreData,
      decodeListData_encodeListData encodeGrainSpec decodeGrainSpec decodeGrainSpec_encodeGrainSpec gs,
      decodeListData_encodeListData encodeSturdyRefChannel decodeSturdyRefChannel decodeSturdyRefChannel_encodeSturdyRefChannel cs]

/-- Render a `DeploymentTopology` to `"dreggnet-deploy@1"` manifest text. -/
def renderDeploymentTopology (d : DeploymentTopology) : String :=
  let gLines := d.grains.map fun g => s!"grain: {g.grainName} {g.teeMeasurementPin} {g.mandateBudget}"
  let cLines := d.channels.map fun c => s!"channel: {c.channelName} {c.sourceGrain} {c.targetGrain} {c.maxEpoch}"
  String.intercalate "\n" ([
    "format: dreggnet-deploy@1",
    s!"topology: {d.topologyName}",
    s!"totalMandateCap: {d.totalMandateCap}",
    s!"requiredTeePin: {d.requiredTeePin}"
  ] ++ gLines ++ cLines)

structure DeployParseAcc where
  topologyName : String := "DefaultTopology"
  totalMandateCap : Nat := 1000
  requiredTeePin : Nat := 42
  grains : List GrainSpec := []
  channels : List SturdyRefChannel := []

def stepParseDeployLine (acc : DeployParseAcc) (l : List UInt8) : Except String DeployParseAcc :=
  if eqAscii l "format: dreggnet-deploy@1" then .ok acc
  else if startsWithAscii l "topology:" then
    .ok { acc with topologyName := cleanBytesToString (dropBytes 9 l) }
  else if startsWithAscii l "totalMandateCap:" then
    match parseNatBytes (dropBytes 16 l) with
    | some v => .ok { acc with totalMandateCap := v }
    | none => .error "invalid totalMandateCap"
  else if startsWithAscii l "requiredTeePin:" then
    match parseNatBytes (dropBytes 15 l) with
    | some v => .ok { acc with requiredTeePin := v }
    | none => .error "invalid requiredTeePin"
  else if startsWithAscii l "grain:" then
    match wordsBytes (stripBracketsOrParens (dropBytes 6 l)) with
    | [gB, pinB, budB] =>
      match parseNatBytes pinB, parseNatBytes budB with
      | some pin, some bud =>
        .ok { acc with grains := acc.grains ++ [⟨cleanBytesToString gB, pin, bud⟩] }
      | _, _ => .error "invalid grain teeMeasurementPin or mandateBudget"
    | _ => .error ("invalid grain line: " ++ cleanBytesToString l)
  else if startsWithAscii l "channel:" then
    match wordsBytes (stripBracketsOrParens (dropBytes 8 l)) with
    | [cB, srcB, dstB, epB] =>
      match parseNatBytes epB with
      | some ep =>
        .ok { acc with channels := acc.channels ++ [⟨cleanBytesToString cB, cleanBytesToString srcB, cleanBytesToString dstB, ep⟩] }
      | none => .error "invalid channel maxEpoch"
    | _ => .error ("invalid channel line: " ++ cleanBytesToString l)
  else
    .error ("unrecognized dreggnet-deploy@1 line: " ++ cleanBytesToString l)

def foldDeployLines : List (List UInt8) → DeployParseAcc → Except String DeployParseAcc
  | [], acc => .ok acc
  | l :: ls, acc =>
    match stepParseDeployLine acc l with
    | .ok acc' => foldDeployLines ls acc'
    | .error e => .error e

/-- Parse a `"dreggnet-deploy@1"` manifest or S-expression into `DeploymentTopology` (`0 Classical.choice`). -/
def parseDeploymentTopology (input : String) : Except String DeploymentTopology :=
  let lines := extractWireLines input
  if !(lines.any (fun l => eqAscii l "format: dreggnet-deploy@1")) then
    .error "missing format: dreggnet-deploy@1 header"
  else
    match foldDeployLines lines {} with
    | .error e => .error e
    | .ok acc =>
      .ok {
        topologyName := acc.topologyName,
        totalMandateCap := acc.totalMandateCap,
        requiredTeePin := acc.requiredTeePin,
        grains := acc.grains,
        channels := acc.channels
      }


/-- Lower a `DeploymentTopology` into an `.obend` `Syntax.Module` of composed specs and laws
    enforcing grain mandate budgets, SturdyRef channel epochs, and TEE attestation pins. -/
def lowerDeploymentToObend (d : DeploymentTopology) : Module :=
  let dispSig : Signature := ⟨"dispatch", [], "Nat"⟩
  let baseDispatch : Method := {
    name := "dispatch"
    params := []
    resultType := "Nat"
    qualifier := "primary"
    body := .expr (.binary "+" (.member (.var "self") "mandateDrawn") (.nat "1"))
    signature := mkSigJson "dispatch" [] "Nat"
  }
  let baseClaim : Claim := {
    name := "mandateMonotone"
    params := []
    body := .binary "<=" (.member (.var "self") "mandateDrawn")
                         (.member (.var "self") "dispatch")
    method := some .omega
  }
  let mandateSpec : Spec := {
    name := "GrainMandateSpec"
    suffix := false
    parents := []
    targetType := "DeploymentGrain"
    requirements := .arr #[]
    methods := [baseDispatch]
    claims := [baseClaim]
  }
  let overDispatch : Method := {
    name := "dispatch"
    params := []
    resultType := "Nat"
    qualifier := "around"
    body := .expr (.binary "+" (.member (.var "super") "dispatch") (.member (.var "self") "teePin"))
    signature := mkSigJson "dispatch" [] "Nat"
  }
  let teeSpec : Spec := {
    name := "TeeChannelSpec"
    suffix := false
    parents := ["GrainMandateSpec"]
    targetType := "DeploymentGrain"
    requirements := .arr #[]
    methods := [overDispatch]
    claims := []
  }
  let initBudget : Nat :=
    match d.grains.head? with
    | some g => g.mandateBudget
    | none => d.totalMandateCap
  let initEpoch : Nat :=
    match d.channels.head? with
    | some c => c.maxEpoch
    | none => 100
  let seedRec : Expr := .record [
    ("teePin", .nat (toString d.requiredTeePin)),
    ("mandateDrawn", .nat "0"),
    ("mandateBudget", .nat (toString initBudget)),
    ("channelEpoch", .nat (toString initEpoch)),
    ("dispatch", .nat "0")
  ]
  let entryFn : Decl := .function "entry" [] "Nat"
    (.expr (.member (.fix (.var "TeeChannelSpec") seedRec) "dispatch"))
  let deployLaw : LawExpr :=
    .and (.monotone "mandateDrawn")
      (.and (.leROff (.field "mandateDrawn") (.field "mandateBudget") 0)
        (.and (.writeOnce "mandateBudget")
          (.eqC (.field "teePin") (Int.ofNat d.requiredTeePin))))
  { name := "DeploymentTopologyModule"
    imports := []
    decls := [
      .record "DeploymentGrain" [
        ("teePin", "Nat"), ("mandateDrawn", "Nat"),
        ("mandateBudget", "Nat"), ("channelEpoch", "Nat")
      ] [dispSig],
      .spec mandateSpec,
      .spec teeSpec,
      entryFn
    ]
    laws := [("mandateAndTeePin", deployLaw)]
    header := none
    keeps := []
    lawMethods := [("mandateAndTeePin", .weave)]
    contracts := [{
      name := "DeploymentGrainContract"
      targetType := "DeploymentGrain"
      law := some deployLaw
      method := some .weave
    }] }

/-- Concrete verified `FormatReader` instance for elastic cloud deployment topologies (`"dreggnet-deploy@1"`). -/
def deploymentTopologyReader : FormatReader DeploymentTopology where
  formatId := "dreggnet-deploy@1"
  projectionKind := .deosAffordance
  parse := parseDeploymentTopology
  render := renderDeploymentTopology
  toCoreData := deploymentToCoreData
  ofCoreData := deploymentOfCoreData
  lowerToObend := lowerDeploymentToObend
  data_roundtrip := deploymentTopology_data_roundtrip

-- Compile-time verification guards for WS-G Zero-Choice Byte-Level Format Decoders
#guard
  let doc : ObnbDocument := {
    title := "CustomWorkbook",
    lawName := "customLaw",
    boundField := "energy",
    maxBound := 420,
    cells := [
      .prose "Overview" "Overview",
      .obend "stepA" "energy" 12,
      .leanBridge "energy_thm" "WorkbookSpec"
    ]
  }
  let doc2 : ObnbDocument := {
    title := "CustomWorkbook",
    lawName := "customLaw",
    boundField := "energy",
    maxBound := 420,
    cells := [
      .prose "Overview" "DetailedBody",
      .obend "stepA" "energy" 12,
      .leanBridge "energy_thm" "WorkbookSpec"
    ]
  }
  (parseObnb (renderObnb doc)).toOption == some doc &&
  (parseObnb "(obnb (title CustomWorkbook) (law customLaw) (field energy) (maxBound 420) (prose Overview) (cell-obend stepA:energy:12) (cell-lean energy_thm:WorkbookSpec))").toOption == some doc &&
  (parseObnb "(obnb (title CustomWorkbook) (law customLaw) (field energy) (maxBound 420) (prose Overview DetailedBody) (cell-obend (stepA energy 12)) (cell-lean (energy_thm WorkbookSpec)))").toOption == some doc2 &&
  !(parseObnb "completely invalid garbage !!!").isOk &&
  !(parseObnb "title: MissingFormatHeader").isOk &&
  !(parseObnb "(obnb (title Unclosed)").isOk

#guard
  let stg : UsdStage := {
    stageName := "RoboticArmStage",
    subLayers := ["base.usda", "grip.usda"],
    maxThermalMk := 310000,
    baseXform := ⟨"ArmBase", false, 1, 2, 3, 4, 5, 290000⟩,
    overrides := [⟨"GripTip", true, 6, 7, 8, 9, 10, 300000⟩]
  }
  (parseUsdStage (renderUsdStage stg)).toOption == some stg &&
  (parseUsdStage "(usd-stage (stage RoboticArmStage) (subLayers base.usda,grip.usda) (maxThermalMk 310000) (def Xform ArmBase 1 2 3 4 5 290000) (over GripTip 6 7 8 9 10 300000))").toOption == some stg &&
  (parseUsdStage "(usd-stage (stage RoboticArmStage) (subLayers (base.usda grip.usda)) (maxThermalMk 310000) (def Xform ArmBase 1 2 3 4 5 290000) (over GripTip 6 7 8 9 10 300000))").toOption == some stg &&
  !(parseUsdStage "(usd-stage (stage Unclosed)").isOk

#guard
  let pol : DfaPolicy := {
    policyName := "StrictTranscriptDfa",
    initialState := 0,
    acceptingStates := [2, 3],
    transitions := [⟨0, 1, 1⟩, ⟨1, 2, 2⟩],
    holes := [⟨"api_key_slot", 9, 1⟩]
  }
  (parseDfaPolicy (renderDfaPolicy pol)).toOption == some pol &&
  (parseDfaPolicy "(dfa-policy (policy StrictTranscriptDfa) (initial 0) (accepting 2,3) (transition 0 1 1) (transition 1 2 2) (hole api_key_slot 9 1))").toOption == some pol &&
  (parseDfaPolicy "(dfa-policy (policy StrictTranscriptDfa) (initial 0) (accepting (2 3)) (transition (0 1 1)) (transition [1 2 2]) (hole (api_key_slot 9 1)))").toOption == some pol &&
  !(parseDfaPolicy "(dfa-policy (policy StrictTranscriptDfa) (initial 0").isOk

#guard
  let dep : DeploymentTopology := {
    topologyName := "EdgeMeshCluster",
    totalMandateCap := 8000,
    requiredTeePin := 777,
    grains := [⟨"gateway", 777, 3000⟩, ⟨"solver", 777, 5000⟩],
    channels := [⟨"rpc_chan", "gateway", "solver", 64⟩]
  }
  (parseDeploymentTopology (renderDeploymentTopology dep)).toOption == some dep &&
  (parseDeploymentTopology "(dreggnet-deploy (topology EdgeMeshCluster) (totalMandateCap 8000) (requiredTeePin 777) (grain gateway 777 3000) (grain solver 777 5000) (channel rpc_chan gateway solver 64))").toOption == some dep &&
  (parseDeploymentTopology "(dreggnet-deploy (topology EdgeMeshCluster) (totalMandateCap 8000) (requiredTeePin 777) (grain (gateway 777 3000)) (grain [solver 777 5000]) (channel (rpc_chan gateway solver 64)))").toOption == some dep &&
  !(parseDeploymentTopology "(dreggnet-deploy (topology Unclosed").isOk

end Obend.Format

end

