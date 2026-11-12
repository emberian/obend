module
/-
# `Obend.Tactic.DocsCensus` — `Obend.Intention` & `Obend.Slot` Markdown Governance Gate

Instantiates `Obend.Intention` and `Obend.Slot` (`lean/Obend/Intention.lean`, `lean/Obend/Slot.lean`)
over `DocEnvWorld := Lean.Environment × RepoFsSnapshot` so that every root architecture
markdown document (`README.md`, `AMBITION.md`, `THESIS.md`, `DESIGN.md`, `PLAN.md`,
`HARDWARE.md`, `METATHEORY.md`, `GROUNDING.md`, `PHYSICAL.md`, `SILICON-ELABORATOR.md`,
`QUALIFICATION-AND-SILICON-LEAN.md`, `DEOS-CONTRACTS-CONSENSUS.md`, `NEXT-MATHEMATICA.md`)
is governed by a `Slot` whose `supports` pin:
1. every Lean module or directory path (`lean/Obend/...`, `Obend/.../*.lean`, and backticked
   relative `.lean` / repo paths) cited in the doc,
2. every review path (`review/*.md`) cited in the doc,
3. every `Obend.<Sub>` subsystem root cited in the doc,
4. every backticked `Obend.*` theorem, definition, type, or module constant cited in the doc
   (verified against `Lean.Environment`),
5. every backticked bare `snake_case` or qualified `Upper.member` identifier, resolved
   against `Lean.Environment` constants and modules, and
6. every fenced `inductive <Name>` constructor block (`| ctor ...`), verified against an
   `InductiveVal` in `Lean.Environment` owning every listed constructor.
-/

public import Lean
public meta import Lean
public import Obend.Slot
public meta import Obend.Slot
public import Obend.Intention
public meta import Obend.Intention

@[expose] public section

namespace Obend.Tactic.DocsCensus

open Lean Elab Command
open Obend.Slot

/-- All thirteen root architecture and specification markdown documents governed by `DocEnvWorld`
slots (pinning file paths, `Obend.*` names, bare/qualified identifiers, and fenced `inductive`
constructor blocks). -/
def canonicalGovernedDocs : List String :=
  [ "README.md"
  , "AMBITION.md"
  , "THESIS.md"
  , "DESIGN.md"
  , "PLAN.md"
  , "HARDWARE.md"
  , "METATHEORY.md"
  , "GROUNDING.md"
  , "PHYSICAL.md"
  , "SILICON-ELABORATOR.md"
  , "QUALIFICATION-AND-SILICON-LEAN.md"
  , "DEOS-CONTRACTS-CONSENSUS.md"
  , "NEXT-MATHEMATICA.md"
  ]

/-- All thirteen top-level root markdown documents. -/
def topLevelMarkdownDocs : List String :=
  canonicalGovernedDocs

/-- Characters permitted inside a candidate module path or dotted identifier token. -/
def isTokenChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '/' || c == '.'

/-- Characters permitted inside a `review/*.md` or repo-relative path token (including `-`). -/
def isReviewPathChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '/' || c == '.'

/-- Characters permitted inside a dotted Lean constant identifier (`Obend.Foo.bar'`). -/
def isLeanIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.'

/-- Characters permitted inside a single Lean constructor or declaration identifier. -/
def isSimpleIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

/-- Generic tokenizer splitting `cs` into maximal runs satisfying `pred`. -/
def tokenizeCharsBy (pred : Char → Bool) (cs : List Char) (cur : List Char) (acc : List (List Char)) :
    List (List Char) :=
  match cs with
  | [] =>
      match cur with
      | [] => acc.reverse
      | _ => (cur.reverse :: acc).reverse
  | c :: rest =>
      if pred c then
        tokenizeCharsBy pred rest (c :: cur) acc
      else
        match cur with
        | [] => tokenizeCharsBy pred rest [] acc
        | _ => tokenizeCharsBy pred rest [] (cur.reverse :: acc)

/-- Split a character list into contiguous tokens of `isTokenChar` characters. -/
def tokenizeChars (cs : List Char) (cur : List Char) (acc : List (List Char)) : List (List Char) :=
  tokenizeCharsBy isTokenChar cs cur acc

/-- Split a `List Char` on a separator character `sep`. -/
def splitCharsOn (sep : Char) (cs : List Char) (cur : List Char) (acc : List String) : List String :=
  match cs with
  | [] => (String.ofList cur.reverse :: acc).reverse
  | c :: rest =>
      if c == sep then
        splitCharsOn sep rest [] (String.ofList cur.reverse :: acc)
      else
        splitCharsOn sep rest (c :: cur) acc

/-- Pure prefix test on `List Char`. -/
def charsStartsWith (pre : List Char) (cs : List Char) : Bool :=
  match pre, cs with
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, c :: rest => (p == c) && charsStartsWith ps rest

/-- Pure suffix test on `List Char`. -/
def charsEndsWith (suf : List Char) (cs : List Char) : Bool :=
  charsStartsWith suf.reverse cs.reverse

/-- Pure substring test on `List Char`. -/
def charsContainsSublist (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | cs@(_ :: rest) => charsStartsWith needle cs || charsContainsSublist needle rest

/-- Strip trailing `.` and `/` characters from a character list. -/
def stripTrailingDotChars (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '.')).reverse

/-- Strip `#L...` or `:line` anchors and trailing `.` / `/` from a backticked path span. -/
def stripPathAnchorChars (cs : List Char) : List Char :=
  let noHash := cs.takeWhile (· != '#')
  let noColon := noHash.takeWhile (· != ':')
  (noColon.reverse.dropWhile (fun c => c == '.' || c == '/')).reverse

/-- Join a list of path components with `"/"` (`@[expose]`-friendly for kernel reduction). -/
def joinWithSlash : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ "/" ++ joinWithSlash rest

/-- Join a list of dotted components with `"."`. -/
def joinWithDot : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ "." ++ joinWithDot rest

/-- Extract normalized `Obend/.../*.lean` relative paths from a single token character list. -/
def tokenCharsToObendLeanPath? (raw : List Char) : Option String :=
  let tok := stripTrailingDotChars raw
  if !charsEndsWith ['.','l','e','a','n'] tok then
    none
  else
    let parts := splitCharsOn '/' tok [] []
    let tail := parts.dropWhile (· != "Obend")
    match tail with
    | "Obend" :: rest =>
        if !rest.isEmpty && tail.all (fun p => p != "" && p != "." && p != "..") then
          some (joinWithSlash tail)
        else
          none
    | _ => none

/-- Extract all `Obend/.../*.lean` file paths referenced in markdown text `content`. -/
def extractObendLeanPaths (content : String) : List String :=
  (tokenizeChars content.toList [] []).filterMap tokenCharsToObendLeanPath?

/-- Extract inline single-backtick spans (never crossing a newline `\n` or triple-backtick fence)
from a character list, structurally recursive on the input `List Char`. -/
def extractInlineBacktickSpansAux : List Char → Bool → Option (List Char) → List (List Char) → List (List Char)
  | [], _, _, acc => acc.reverse
  | '\n' :: rest, _, _, acc =>
      extractInlineBacktickSpansAux rest false none acc
  | _ :: rest, true, _, acc =>
      extractInlineBacktickSpansAux rest true none acc
  | '`' :: '`' :: '`' :: rest, false, none, acc =>
      extractInlineBacktickSpansAux rest true none acc
  | '`' :: rest, false, none, acc =>
      extractInlineBacktickSpansAux rest false (some []) acc
  | '`' :: rest, false, some cur, acc =>
      extractInlineBacktickSpansAux rest false none (cur.reverse :: acc)
  | c :: rest, false, some cur, acc =>
      extractInlineBacktickSpansAux rest false (some (c :: cur)) acc
  | _ :: rest, false, none, acc =>
      extractInlineBacktickSpansAux rest false none acc

/-- Extract all inline backticked character spans from `content`. -/
def extractInlineBacktickSpans (content : String) : List (List Char) :=
  extractInlineBacktickSpansAux content.toList false none []

/-- Extract backticked `lean/Obend/...` or `Obend/...` module/directory paths (including directory
or module stems without `.lean` and relative `<Sub>/.../*.lean` paths). -/
def spanToBacktickObendPath? (sp : List Char) : Option String :=
  if sp.any (fun c => c == ' ' || c == '*' || c == '<' || c == '>' || c == '{' || c == '}') then
    none
  else
    let clean := stripPathAnchorChars sp
    if clean.isEmpty || !clean.all isReviewPathChar then
      none
    else
      let parts := splitCharsOn '/' clean [] []
      if parts.any (fun p => p == "" || p == "." || p == "..") then
        none
      else
        match parts with
        | "lean" :: "Obend" :: rest =>
            if rest.isEmpty then none else some (joinWithSlash ("Obend" :: rest))
        | "Obend" :: rest =>
            if rest.isEmpty then none else some (joinWithSlash ("Obend" :: rest))
        | "Obend.lean" :: [] =>
            some "Obend.lean"
        | "lean" :: "Obend.lean" :: [] =>
            some "Obend.lean"
        | head :: rest =>
            if !rest.isEmpty && charsEndsWith ['.','l','e','a','n'] clean &&
               head != "lean" && head != "tests" && head != "crates" then
              some (joinWithSlash ("Obend" :: head :: rest))
            else
              none
        | [] => none

/-- Extract all backticked `lean/Obend/...` and `Obend/...` paths from `content`. -/
def extractBacktickObendPaths (content : String) : List String :=
  (extractInlineBacktickSpans content).filterMap spanToBacktickObendPath?

/-- Extract normalized `review/*.md` relative paths from a single token character list. -/
def tokenCharsToReviewMdPath? (raw : List Char) : Option String :=
  let tok := stripTrailingDotChars raw
  if !charsEndsWith ['.','m','d'] tok then
    none
  else
    let parts := splitCharsOn '/' tok [] []
    let tail := parts.dropWhile (· != "review")
    match tail with
    | ["review", file] =>
        if file != ".md" && file != "" && file != "." && file != ".." then
          some ("review/" ++ file)
        else
          none
    | _ => none

/-- Extract all `review/*.md` file paths referenced in markdown text `content`. -/
def extractReviewMdPaths (content : String) : List String :=
  (tokenizeCharsBy isReviewPathChar content.toList [] []).filterMap tokenCharsToReviewMdPath?

/-- Extract the top-level subsystem root `<Sub>` from a dotted `Obend.<Sub>...` token. -/
def tokenCharsToObendDottedRoot? (raw : List Char) : Option String :=
  let tok := stripTrailingDotChars raw
  if charsStartsWith ['O','b','e','n','d','.'] tok &&
     !tok.contains '/' &&
     !charsEndsWith ['.','l','e','a','n'] tok then
    match splitCharsOn '.' tok [] [] with
    | "Obend" :: sub :: _ =>
        if sub != "" then some sub else none
    | _ => none
  else
    none

/-- Extract all dotted `Obend.<Sub>...` subsystem roots referenced in markdown text `content`. -/
def extractObendDottedRoots (content : String) : List String :=
  (tokenizeChars content.toList [] []).filterMap tokenCharsToObendDottedRoot?

/-- Convert a candidate token inside backticks to a normalized `Obend.*` constant/module string. -/
def tokenCharsToObendConst? (raw : List Char) : Option String :=
  let tok := stripTrailingDotChars raw
  if charsStartsWith ['O','b','e','n','d','.'] tok &&
     !charsEndsWith ['.','l','e','a','n'] tok then
    let parts := splitCharsOn '.' tok [] []
    match parts with
    | "Obend" :: sub :: _ =>
        if sub != "" && parts.all (fun p => p != "" && p != "*" && p != "+") then
          some (joinWithDot parts)
        else
          none
    | _ => none
  else
    none

/-- Extract all backticked `Obend.*` constant or module names from markdown text `content`. -/
def extractBacktickObendConsts (content : String) : List String :=
  let spans := extractInlineBacktickSpans content
  spans.foldl (fun acc sp =>
    let toks := (tokenizeCharsBy isLeanIdentChar sp [] []).filterMap tokenCharsToObendConst?
    acc ++ toks) []

/-! ## Fenced `inductive <Name>` Constructor Block Extraction -/

/-- Trim leading spaces, tabs, and carriage returns from a `List Char`. -/
def dropLeadingWs : List Char → List Char :=
  List.dropWhile (fun c => c == ' ' || c == '\t' || c == '\r')

/-- Strip a `--` line comment from a character list. -/
def stripLineComment : List Char → List Char
  | [] => []
  | '-' :: '-' :: _ => []
  | c :: rest => c :: stripLineComment rest

/-- Extract constructor names from a `|`-prefixed line inside an `inductive` declaration
(supports both one-per-line `| hole (idx : Nat)` and inline `| erased | affine | linear`). -/
def parseCtorSegments (segs : List String) : List String :=
  segs.filterMap fun seg =>
    let cs := dropLeadingWs seg.toList
    let ident := cs.takeWhile isSimpleIdentChar
    match ident with
    | [] => none
    | c :: _ =>
        if c.isAlpha || c == '_' then some (String.ofList ident) else none

/-- Parse fenced markdown blocks for `inductive <Name>` declarations and their `| <ctor>` arms. -/
def extractFencedInductiveBlocksAux :
    List String → Bool → Bool → Option (String × List String) → List (String × List String) →
      List (String × List String)
  | [], _, _, cur, acc =>
      let acc' := match cur with
        | some (nm, ctors) => if ctors.isEmpty then acc else (nm, ctors) :: acc
        | none => acc
      acc'.reverse
  | line :: rest, inFence, inComment, cur, acc =>
      let trimmed := dropLeadingWs line.toList
      if charsStartsWith ['`','`','`'] trimmed then
        let acc' := match cur with
          | some (nm, ctors) => if ctors.isEmpty then acc else (nm, ctors) :: acc
          | none => acc
        extractFencedInductiveBlocksAux rest (!inFence) false none acc'
      else if !inFence then
        extractFencedInductiveBlocksAux rest false false none acc
      else if inComment then
        let stillComment := !charsContainsSublist ['-','/'] trimmed
        extractFencedInductiveBlocksAux rest true stillComment cur acc
      else if charsStartsWith ['/','-'] trimmed then
        let stillComment := !charsContainsSublist ['-','/'] (trimmed.drop 2)
        extractFencedInductiveBlocksAux rest true stillComment cur acc
      else
        let uncommented := dropLeadingWs (stripLineComment trimmed)
        if uncommented.isEmpty then
          extractFencedInductiveBlocksAux rest true false cur acc
        else if charsStartsWith ['i','n','d','u','c','t','i','v','e',' '] uncommented then
          let acc' := match cur with
            | some (nm, ctors) => if ctors.isEmpty then acc else (nm, ctors) :: acc
            | none => acc
          let afterKw := dropLeadingWs (uncommented.drop 10)
          let nameChars := afterKw.takeWhile isLeanIdentChar
          let indName := String.ofList (stripTrailingDotChars nameChars)
          if indName.isEmpty then
            extractFencedInductiveBlocksAux rest true false none acc'
          else
            -- Also check if single-line `inductive Foo := | a | b` or `where | a | b` has `|` on same line
            let afterName := afterKw.drop nameChars.length
            let inlineCtors :=
              match afterName.dropWhile (· != '|') with
              | '|' :: tail => parseCtorSegments (splitCharsOn '|' tail [] [])
              | _ => []
            extractFencedInductiveBlocksAux rest true false (some (indName, inlineCtors)) acc'
        else
          match cur with
          | none =>
              extractFencedInductiveBlocksAux rest true false none acc
          | some (indName, ctors) =>
              match uncommented with
              | '|' :: '>' :: _ =>
                  extractFencedInductiveBlocksAux rest true false (some (indName, ctors)) acc
              | '|' :: '|' :: _ =>
                  extractFencedInductiveBlocksAux rest true false (some (indName, ctors)) acc
              | '|' :: tail =>
                  let newCtors := parseCtorSegments (splitCharsOn '|' tail [] [])
                  extractFencedInductiveBlocksAux rest true false (some (indName, ctors ++ newCtors)) acc
              | _ =>
                  if charsStartsWith ['d','e','r','i','v','i','n','g'] uncommented ||
                     charsStartsWith ['s','t','r','u','c','t','u','r','e',' '] uncommented ||
                     charsStartsWith ['d','e','f',' '] uncommented ||
                     charsStartsWith ['t','h','e','o','r','e','m',' '] uncommented ||
                     charsStartsWith ['a','b','b','r','e','v',' '] uncommented ||
                     charsStartsWith ['n','a','m','e','s','p','a','c','e',' '] uncommented ||
                     charsStartsWith ['e','n','d'] uncommented then
                    let acc' := if ctors.isEmpty then acc else (indName, ctors) :: acc
                    extractFencedInductiveBlocksAux rest true false none acc'
                  else
                    extractFencedInductiveBlocksAux rest true false (some (indName, ctors)) acc

/-- Extract `(inductiveName, constructorNames)` pairs from fenced code blocks in `content`. -/
def extractFencedInductiveBlocks (content : String) : List (String × List String) :=
  let lines := splitCharsOn '\n' content.toList [] []
  extractFencedInductiveBlocksAux lines false false none []

/-- Convert a dotted `Obend.*` string into a hierarchical `Lean.Name`. -/
def stringToLeanName (s : String) : Lean.Name :=
  (splitCharsOn '.' s.toList [] []).foldl Lean.Name.str Lean.Name.anonymous

/-- Deduplicate a list while preserving first-seen order. -/
def dedupList {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs =>
      let rest := dedupList xs
      if rest.contains x then rest else x :: rest

/-! ## `Obend.Intention` & `Obend.Slot` Instantiation over `DocEnvWorld` -/

/-- Snapshot of repository filesystem state for pure `Obend.Intention` and `Obend.Slot` evaluation. -/
structure RepoFsSnapshot where
  /-- Markdown specification files `(relPath, content)` present on disk. -/
  docs        : List (String × String)
  /-- Existing `Obend/...` module or directory relative paths under `lean/`. -/
  leanPaths   : List String
  /-- Existing `review/*.md` ledger/review relative paths at repo root. -/
  reviewPaths : List String
  /-- Existing top-level `Obend.<Sub>` subsystem names (`Obend/<Sub>.lean` or `Obend/<Sub>/`). -/
  subsystems  : List String
  deriving DecidableEq, Repr

/-- Combined world `(Lean.Environment × RepoFsSnapshot)` against which documentation slots and
intentions are resolved and verified. -/
abbrev DocEnvWorld := Lean.Environment × RepoFsSnapshot

/-- A support fact cited by a markdown specification document pin in `DocEnvWorld`:
    1. `docExists docPath`: the markdown document itself exists on disk.
    2. `leanPathExists relPath`: the cited `Obend/...` module or directory path exists on disk.
    3. `reviewPathExists relPath`: the cited `review/*.md` path exists on disk.
    4. `subsystemExists sub`: the cited `Obend.<Sub>` subsystem root exists on disk.
    5. `constExists constName`: the backticked `Obend.*` constant or module exists in `Lean.Environment`.
    6. `inductiveCtorsExist indName ctors`: if `indName` names an inductive in `Lean.Environment`,
       every `ctor ∈ ctors` is a constructor of `indName`. -/
inductive DocFact where
  | docExists (docPath : String)
  | leanPathExists (relPath : String)
  | reviewPathExists (relPath : String)
  | subsystemExists (sub : String)
  | constExists (constName : Lean.Name)
  | inductiveCtorsExist (indName : Lean.Name) (ctors : List String)
  deriving DecidableEq, Repr

/-- Evaluate whether a `DocFact` support holds in `w : DocEnvWorld`. -/
def holdsDocFact (w : DocEnvWorld) : DocFact → Bool
  | .docExists doc => w.2.docs.any (fun p => p.1 == doc)
  | .leanPathExists p => w.2.leanPaths.contains p
  | .reviewPathExists p => w.2.reviewPaths.contains p
  | .subsystemExists s => w.2.subsystems.contains s
  | .constExists n =>
      w.1.contains n ||
      w.1.header.moduleNames.contains n ||
      match n with
      | .str (.str .anonymous "Obend") sub => w.2.subsystems.contains sub
      | _ => false
  | .inductiveCtorsExist indName ctors =>
      match w.1.find? indName with
      | some (.inductInfo iv) =>
          let actual := iv.ctors.filterMap fun c =>
            match c.components.reverse with
            | last :: _ => some last.toString
            | [] => none
          ctors.all (fun c => actual.contains c)
      | _ => false

/-- A pinned markdown document selection carrying its target path and extracted `DocFact` supports. -/
structure DocPin where
  docPath  : String
  supports : List DocFact
  deriving DecidableEq, Repr

/-- Extract the complete deduplicated support list of `DocFact`s cited by `docPath` with `content`. -/
def extractDocSupports (docPath : String) (content : String) : List DocFact :=
  let allLeanPaths := dedupList (extractObendLeanPaths content ++ extractBacktickObendPaths content)
  let leanFacts := allLeanPaths.map DocFact.leanPathExists
  let reviewFacts := (dedupList (extractReviewMdPaths content)).map DocFact.reviewPathExists
  let subFacts := (dedupList (extractObendDottedRoots content)).map DocFact.subsystemExists
  let constFacts := (dedupList (extractBacktickObendConsts content)).map
    (fun c => DocFact.constExists (stringToLeanName c))
  let indFacts := (extractFencedInductiveBlocks content).filterMap fun (nm, ctors) =>
    if charsStartsWith ['O','b','e','n','d','.'] nm.toList then
      some (DocFact.inductiveCtorsExist (stringToLeanName nm) ctors)
    else
      none
  DocFact.docExists docPath :: (leanFacts ++ reviewFacts ++ subFacts ++ constFacts ++ indFacts)

/-- Construct the candidate `DocPin` for `docPath` from `w : DocEnvWorld`. -/
def candidateDocPin (w : DocEnvWorld) (docPath : String) : DocPin :=
  let content := (w.2.docs.find? (fun p => p.1 == docPath)).map Prod.snd |>.getD ""
  { docPath := docPath, supports := extractDocSupports docPath content }

/-- Resolve a markdown document reference `docPath` in `w : DocEnvWorld`:
    returns `.ok pin` iff every support fact in `pin.supports` holds in `w`. -/
def resolveDoc (w : DocEnvWorld) (docPath : String) : Except String DocPin :=
  let pin := candidateDocPin w docPath
  if _h : pin.supports.all (holdsDocFact w) = true then
    .ok pin
  else
    let dead := pin.supports.filter (fun f => !holdsDocFact w f)
    .error s!"doc '{docPath}' has {dead.length} dead supports: {reprStr dead}"

theorem resolveDoc_ref (w : DocEnvWorld) (docPath : String) (pin : DocPin)
    (h : resolveDoc w docPath = .ok pin) :
    pin.docPath = docPath := by
  unfold resolveDoc at h
  dsimp only at h
  split at h
  · injection h with hpin
    rw [← hpin]
    rfl
  · cases h

theorem resolveDoc_holds (w : DocEnvWorld) (docPath : String) (pin : DocPin)
    (h : resolveDoc w docPath = .ok pin) :
    ∀ f ∈ pin.supports, holdsDocFact w f = true := by
  unfold resolveDoc at h
  dsimp only at h
  split at h
  · rename_i hall
    injection h with hpin
    rw [← hpin]
    exact List.all_eq_true.1 hall
  · cases h

/-- **`docIntention`**: `Obend.Intention` governing markdown specification documents over `DocEnvWorld`. -/
def docIntention : Obend.Intention DocEnvWorld String DocPin DocFact String where
  ref := DocPin.docPath
  supports := DocPin.supports
  holds := holdsDocFact
  resolve := resolveDoc
  resolve_ref := resolveDoc_ref
  resolve_holds := resolveDoc_holds

/-- **`docSlot`**: the `Obend.Slot.Slot` governing markdown document `docPath`. -/
def docSlot (docPath : String) : Slot DocFact DocPin :=
  docIntention.slot docPath

/-- A document slot is usable at `w : DocEnvWorld` iff every `DocFact` support holds. -/
theorem docSlot_usable_iff (w : DocEnvWorld) (docPath : String) :
    (docSlot docPath).usable (holdsDocFact w) (candidateDocPin w docPath) = true ↔
      ∀ f ∈ (candidateDocPin w docPath).supports, holdsDocFact w f = true :=
  have hr : docIntention.ref (candidateDocPin w docPath) = docPath := rfl
  (docIntention.current_iff_usable hr w).symm.trans
    (docIntention.current_iff w (candidateDocPin w docPath))

/-- A document pin is stale at `w : DocEnvWorld` iff reading `docSlot docPath` returns `.blocked`
naming the exact missing files, constants, or constructors. -/
theorem docSlot_stale_iff_blocked (w : DocEnvWorld) (docPath : String) :
    docIntention.current w (candidateDocPin w docPath) = false ↔
      (docSlot docPath).read (holdsDocFact w) (some (candidateDocPin w docPath)) =
        .blocked (candidateDocPin w docPath)
          ((candidateDocPin w docPath).supports.filter fun f => !holdsDocFact w f) :=
  docIntention.stale_iff_blocked rfl w

/-! ## Filesystem Resolution & `#check_docs_census` / `#docs_census` Elaborators -/

/-- Resolve a repository-root relative path whether invoked from `lean/` or the repo root. -/
def resolveRepoFile (relPath : String) : IO (Option System.FilePath) := do
  let candidates : List System.FilePath :=
    [ System.FilePath.mk relPath
    , System.FilePath.mk ("../" ++ relPath)
    ]
  for c in candidates do
    if ← c.pathExists then
      return some c
  return none

/-- Verify that a relative `Obend/...` path (`.lean` module or directory/module stem) exists under `lean/`. -/
def obendLeanPathExists (relObendPath : String) : IO Bool := do
  let baseCandidates : List System.FilePath :=
    [ System.FilePath.mk relObendPath
    , System.FilePath.mk ("lean/" ++ relObendPath)
    , System.FilePath.mk ("../lean/" ++ relObendPath)
    ]
  let stemCandidates : List System.FilePath :=
    if charsEndsWith ['.','l','e','a','n'] relObendPath.toList then []
    else
      [ System.FilePath.mk (relObendPath ++ ".lean")
      , System.FilePath.mk ("lean/" ++ relObendPath ++ ".lean")
      , System.FilePath.mk ("../lean/" ++ relObendPath ++ ".lean")
      ]
  for c in baseCandidates ++ stemCandidates do
    if ← c.pathExists then
      return true
  return false

/-- Verify that a relative `review/*.md` path exists at the repository root. -/
def reviewMdPathExists (relReviewPath : String) : IO Bool := do
  return (← resolveRepoFile relReviewPath).isSome

/-- Verify that a dotted `Obend.<Sub>` subsystem root corresponds to an existing `.lean` module or directory. -/
def obendSubsystemExists (sub : String) : IO Bool := do
  let fileRel := s!"Obend/{sub}.lean"
  let dirRel := s!"Obend/{sub}"
  let candidates : List System.FilePath :=
    [ System.FilePath.mk fileRel
    , System.FilePath.mk ("lean/" ++ fileRel)
    , System.FilePath.mk ("../lean/" ++ fileRel)
    , System.FilePath.mk dirRel
    , System.FilePath.mk ("lean/" ++ dirRel)
    , System.FilePath.mk ("../lean/" ++ dirRel)
    ]
  for c in candidates do
    if ← c.pathExists then
      return true
  return false

/-- Result summary of running the top-level markdown documentation census. -/
structure CensusReport where
  docsChecked   : Nat
  pathsChecked  : Nat
  rootsChecked  : Nat
  missingDocs   : List String
  missingPaths  : List (String × String)
  missingRoots  : List (String × String)
  deriving DecidableEq, Repr

/-- Pure check that a `CensusReport` has zero missing documents, paths, or subsystem roots. -/
def CensusReport.isClean (r : CensusReport) : Bool :=
  r.missingDocs.isEmpty && r.missingPaths.isEmpty && r.missingRoots.isEmpty

theorem censusReport_isClean_iff (r : CensusReport) :
    r.isClean = true ↔
      r.missingDocs = [] ∧ r.missingPaths = [] ∧ r.missingRoots = [] := by
  simp [CensusReport.isClean, List.isEmpty_iff, and_assoc]

/-- Run the path and subsystem documentation census across `docs`. -/
def runDocsCensus (docs : List String := topLevelMarkdownDocs) : IO CensusReport := do
  let mut pathsChecked := 0
  let mut rootsChecked := 0
  let mut missingDocs : List String := []
  let mut missingPaths : List (String × String) := []
  let mut missingRoots : List (String × String) := []
  for doc in docs do
    match ← resolveRepoFile doc with
    | none =>
        missingDocs := missingDocs ++ [doc]
    | some path =>
        let content ← IO.FS.readFile path
        let paths := dedupList (extractObendLeanPaths content ++ extractBacktickObendPaths content)
        let reviews := extractReviewMdPaths content
        let roots := extractObendDottedRoots content
        for p in paths do
          pathsChecked := pathsChecked + 1
          unless ← obendLeanPathExists p do
            if !missingPaths.contains (doc, p) then
              missingPaths := missingPaths ++ [(doc, p)]
        for rv in reviews do
          pathsChecked := pathsChecked + 1
          unless ← reviewMdPathExists rv do
            if !missingPaths.contains (doc, rv) then
              missingPaths := missingPaths ++ [(doc, rv)]
        for r in roots do
          rootsChecked := rootsChecked + 1
          unless ← obendSubsystemExists r do
            if !missingRoots.contains (doc, r) then
              missingRoots := missingRoots ++ [(doc, r)]
  return {
    docsChecked := docs.length
    pathsChecked := pathsChecked
    rootsChecked := rootsChecked
    missingDocs := missingDocs
    missingPaths := missingPaths
    missingRoots := missingRoots
  }

/-! ## Meta-Phase Snapshot Builder & `#check_docs_census` / `#docs_census` Commands -/

meta def metaCanonicalGovernedDocs : List String :=
  [ "README.md"
  , "AMBITION.md"
  , "THESIS.md"
  , "DESIGN.md"
  , "PLAN.md"
  , "HARDWARE.md"
  , "METATHEORY.md"
  , "GROUNDING.md"
  , "PHYSICAL.md"
  , "SILICON-ELABORATOR.md"
  , "QUALIFICATION-AND-SILICON-LEAN.md"
  , "DEOS-CONTRACTS-CONSENSUS.md"
  , "NEXT-MATHEMATICA.md"
  ]

meta def metaTopLevelMarkdownDocs : List String :=
  metaCanonicalGovernedDocs

/-- Every root architecture document is directly governed; none are downgraded to warning-only. -/
meta def metaReportedDocs : List String := []

meta def metaIsTokenChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '/' || c == '.'

meta def metaIsReviewPathChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '/' || c == '.'

meta def metaIsLeanIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.'

meta def metaIsSimpleIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

meta def metaTokenizeCharsBy (pred : Char → Bool) (cs : List Char) (cur : List Char)
    (acc : List (List Char)) : List (List Char) :=
  match cs with
  | [] =>
      match cur with
      | [] => acc.reverse
      | _ => (cur.reverse :: acc).reverse
  | c :: rest =>
      if pred c then
        metaTokenizeCharsBy pred rest (c :: cur) acc
      else
        match cur with
        | [] => metaTokenizeCharsBy pred rest [] acc
        | _ => metaTokenizeCharsBy pred rest [] (cur.reverse :: acc)

meta def metaTokenizeChars (cs : List Char) (cur : List Char) (acc : List (List Char)) : List (List Char) :=
  metaTokenizeCharsBy metaIsTokenChar cs cur acc

meta def metaSplitCharsOn (sep : Char) (cs : List Char) (cur : List Char) (acc : List String) : List String :=
  match cs with
  | [] => (String.ofList cur.reverse :: acc).reverse
  | c :: rest =>
      if c == sep then
        metaSplitCharsOn sep rest [] (String.ofList cur.reverse :: acc)
      else
        metaSplitCharsOn sep rest (c :: cur) acc

meta def metaCharsStartsWith (pre : List Char) (cs : List Char) : Bool :=
  match pre, cs with
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, c :: rest => (p == c) && metaCharsStartsWith ps rest

meta def metaCharsEndsWith (suf : List Char) (cs : List Char) : Bool :=
  metaCharsStartsWith suf.reverse cs.reverse

meta def metaCharsContainsSublist (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | cs@(_ :: rest) => metaCharsStartsWith needle cs || metaCharsContainsSublist needle rest

meta def metaStripTrailingDotChars (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '.')).reverse

meta def metaStripPathAnchorChars (cs : List Char) : List Char :=
  let noHash := cs.takeWhile (· != '#')
  let noColon := noHash.takeWhile (· != ':')
  (noColon.reverse.dropWhile (fun c => c == '.' || c == '/')).reverse

meta def metaJoinWithSlash : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ "/" ++ metaJoinWithSlash rest

meta def metaJoinWithDot : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ "." ++ metaJoinWithDot rest

meta def metaTokenCharsToObendLeanPath? (raw : List Char) : Option String :=
  let tok := metaStripTrailingDotChars raw
  if !metaCharsEndsWith ['.','l','e','a','n'] tok then
    none
  else
    let parts := metaSplitCharsOn '/' tok [] []
    let tail := parts.dropWhile (· != "Obend")
    match tail with
    | "Obend" :: rest =>
        if !rest.isEmpty && tail.all (fun p => p != "" && p != "." && p != "..") then
          some (metaJoinWithSlash tail)
        else
          none
    | _ => none

meta def metaExtractObendLeanPaths (content : String) : List String :=
  (metaTokenizeChars content.toList [] []).filterMap metaTokenCharsToObendLeanPath?

meta def metaExtractInlineBacktickSpansAux :
    List Char → Bool → Option (List Char) → List (List Char) → List (List Char)
  | [], _, _, acc => acc.reverse
  | '\n' :: rest, _, _, acc =>
      metaExtractInlineBacktickSpansAux rest false none acc
  | _ :: rest, true, _, acc =>
      metaExtractInlineBacktickSpansAux rest true none acc
  | '`' :: '`' :: '`' :: rest, false, none, acc =>
      metaExtractInlineBacktickSpansAux rest true none acc
  | '`' :: rest, false, none, acc =>
      metaExtractInlineBacktickSpansAux rest false (some []) acc
  | '`' :: rest, false, some cur, acc =>
      metaExtractInlineBacktickSpansAux rest false none (cur.reverse :: acc)
  | c :: rest, false, some cur, acc =>
      metaExtractInlineBacktickSpansAux rest false (some (c :: cur)) acc
  | _ :: rest, false, none, acc =>
      metaExtractInlineBacktickSpansAux rest false none acc

meta def metaSpanToBacktickObendPath? (sp : List Char) : Option String :=
  if sp.any (fun c => c == ' ' || c == '*' || c == '<' || c == '>' || c == '{' || c == '}') then
    none
  else
    let clean := metaStripPathAnchorChars sp
    if clean.isEmpty || !clean.all metaIsReviewPathChar then
      none
    else
      let parts := metaSplitCharsOn '/' clean [] []
      if parts.any (fun p => p == "" || p == "." || p == "..") then
        none
      else
        match parts with
        | "lean" :: "Obend" :: rest =>
            if rest.isEmpty then none else some (metaJoinWithSlash ("Obend" :: rest))
        | "Obend" :: rest =>
            if rest.isEmpty then none else some (metaJoinWithSlash ("Obend" :: rest))
        | "Obend.lean" :: [] =>
            some "Obend.lean"
        | "lean" :: "Obend.lean" :: [] =>
            some "Obend.lean"
        | head :: rest =>
            if !rest.isEmpty && metaCharsEndsWith ['.','l','e','a','n'] clean &&
               head != "lean" && head != "tests" && head != "crates" then
              some (metaJoinWithSlash ("Obend" :: head :: rest))
            else
              none
        | [] => none

meta def metaExtractBacktickObendPaths (content : String) : List String :=
  let spans := metaExtractInlineBacktickSpansAux content.toList false none []
  spans.filterMap metaSpanToBacktickObendPath?

/-- Extract repo-relative backticked paths rooted at `crates/` or `lean/tests/` so broken crate
or test file citations are also caught at compile time. -/
meta def metaSpanToBacktickRepoPath? (sp : List Char) : Option String :=
  if sp.any (fun c => c == ' ' || c == '*' || c == '<' || c == '>' || c == '{' || c == '}') then
    none
  else
    let clean := metaStripPathAnchorChars sp
    if clean.isEmpty || !clean.all metaIsReviewPathChar then
      none
    else
      let parts := metaSplitCharsOn '/' clean [] []
      if parts.any (fun p => p == "" || p == "." || p == "..") then
        none
      else
        match parts with
        | "crates" :: rest =>
            if rest.isEmpty then none else some (metaJoinWithSlash ("crates" :: rest))
        | "lean" :: "tests" :: rest =>
            if rest.isEmpty then none else some (metaJoinWithSlash ("lean" :: "tests" :: rest))
        | _ => none

meta def metaExtractBacktickRepoPaths (content : String) : List String :=
  let spans := metaExtractInlineBacktickSpansAux content.toList false none []
  spans.filterMap metaSpanToBacktickRepoPath?

meta def metaTokenCharsToReviewMdPath? (raw : List Char) : Option String :=
  let tok := metaStripTrailingDotChars raw
  if !metaCharsEndsWith ['.','m','d'] tok then
    none
  else
    let parts := metaSplitCharsOn '/' tok [] []
    let tail := parts.dropWhile (· != "review")
    match tail with
    | ["review", file] =>
        if file != ".md" && file != "" && file != "." && file != ".." then
          some ("review/" ++ file)
        else
          none
    | _ => none

meta def metaExtractReviewMdPaths (content : String) : List String :=
  (metaTokenizeCharsBy metaIsReviewPathChar content.toList [] []).filterMap metaTokenCharsToReviewMdPath?

meta def metaTokenCharsToObendDottedRoot? (raw : List Char) : Option String :=
  let tok := metaStripTrailingDotChars raw
  if metaCharsStartsWith ['O','b','e','n','d','.'] tok &&
     !tok.contains '/' &&
     !metaCharsEndsWith ['.','l','e','a','n'] tok then
    match metaSplitCharsOn '.' tok [] [] with
    | "Obend" :: sub :: _ =>
        if sub != "" then some sub else none
    | _ => none
  else
    none

meta def metaExtractObendDottedRoots (content : String) : List String :=
  (metaTokenizeChars content.toList [] []).filterMap metaTokenCharsToObendDottedRoot?

meta def metaTokenCharsToObendConst? (raw : List Char) : Option String :=
  let tok := metaStripTrailingDotChars raw
  if metaCharsStartsWith ['O','b','e','n','d','.'] tok &&
     !metaCharsEndsWith ['.','l','e','a','n'] tok then
    let parts := metaSplitCharsOn '.' tok [] []
    match parts with
    | "Obend" :: sub :: _ =>
        if sub != "" && parts.all (fun p => p != "" && p != "*" && p != "+") then
          some (metaJoinWithDot parts)
        else
          none
    | _ => none
  else
    none

meta def metaExtractBacktickObendConsts (content : String) : List String :=
  let spans := metaExtractInlineBacktickSpansAux content.toList false none []
  spans.foldl (fun acc sp =>
    let toks := (metaTokenizeCharsBy metaIsLeanIdentChar sp [] []).filterMap metaTokenCharsToObendConst?
    acc ++ toks) []

meta def metaDropLeadingWs : List Char → List Char :=
  List.dropWhile (fun c => c == ' ' || c == '\t' || c == '\r')

meta def metaStripLineComment : List Char → List Char
  | [] => []
  | '-' :: '-' :: _ => []
  | c :: rest => c :: metaStripLineComment rest

meta def metaParseCtorSegments (segs : List String) : List String :=
  segs.filterMap fun seg =>
    let cs := metaDropLeadingWs seg.toList
    let ident := cs.takeWhile metaIsSimpleIdentChar
    match ident with
    | [] => none
    | c :: _ =>
        if c.isAlpha || c == '_' then some (String.ofList ident) else none

meta def metaExtractFencedInductiveBlocksAux :
    List String → Bool → Bool → Option (String × List String) → List (String × List String) →
      List (String × List String)
  | [], _, _, cur, acc =>
      let acc' := match cur with
        | some (nm, ctors) => if ctors.isEmpty then acc else (nm, ctors) :: acc
        | none => acc
      acc'.reverse
  | line :: rest, inFence, inComment, cur, acc =>
      let trimmed := metaDropLeadingWs line.toList
      if metaCharsStartsWith ['`','`','`'] trimmed then
        let acc' := match cur with
          | some (nm, ctors) => if ctors.isEmpty then acc else (nm, ctors) :: acc
          | none => acc
        metaExtractFencedInductiveBlocksAux rest (!inFence) false none acc'
      else if !inFence then
        metaExtractFencedInductiveBlocksAux rest false false none acc
      else if inComment then
        let stillComment := !metaCharsContainsSublist ['-','/'] trimmed
        metaExtractFencedInductiveBlocksAux rest true stillComment cur acc
      else if metaCharsStartsWith ['/','-'] trimmed then
        let stillComment := !metaCharsContainsSublist ['-','/'] (trimmed.drop 2)
        metaExtractFencedInductiveBlocksAux rest true stillComment cur acc
      else
        let uncommented := metaDropLeadingWs (metaStripLineComment trimmed)
        if uncommented.isEmpty then
          metaExtractFencedInductiveBlocksAux rest true false cur acc
        else if metaCharsStartsWith ['i','n','d','u','c','t','i','v','e',' '] uncommented then
          let acc' := match cur with
            | some (nm, ctors) => if ctors.isEmpty then acc else (nm, ctors) :: acc
            | none => acc
          let afterKw := metaDropLeadingWs (uncommented.drop 10)
          let nameChars := afterKw.takeWhile metaIsLeanIdentChar
          let indName := String.ofList (metaStripTrailingDotChars nameChars)
          if indName.isEmpty then
            metaExtractFencedInductiveBlocksAux rest true false none acc'
          else
            let afterName := afterKw.drop nameChars.length
            let inlineCtors :=
              match afterName.dropWhile (· != '|') with
              | '|' :: tail => metaParseCtorSegments (metaSplitCharsOn '|' tail [] [])
              | _ => []
            metaExtractFencedInductiveBlocksAux rest true false (some (indName, inlineCtors)) acc'
        else
          match cur with
          | none =>
              metaExtractFencedInductiveBlocksAux rest true false none acc
          | some (indName, ctors) =>
              match uncommented with
              | '|' :: '>' :: _ =>
                  metaExtractFencedInductiveBlocksAux rest true false (some (indName, ctors)) acc
              | '|' :: '|' :: _ =>
                  metaExtractFencedInductiveBlocksAux rest true false (some (indName, ctors)) acc
              | '|' :: tail =>
                  let newCtors := metaParseCtorSegments (metaSplitCharsOn '|' tail [] [])
                  metaExtractFencedInductiveBlocksAux rest true false (some (indName, ctors ++ newCtors)) acc
              | _ =>
                  if metaCharsStartsWith ['d','e','r','i','v','i','n','g'] uncommented ||
                     metaCharsStartsWith ['s','t','r','u','c','t','u','r','e',' '] uncommented ||
                     metaCharsStartsWith ['d','e','f',' '] uncommented ||
                     metaCharsStartsWith ['t','h','e','o','r','e','m',' '] uncommented ||
                     metaCharsStartsWith ['a','b','b','r','e','v',' '] uncommented ||
                     metaCharsStartsWith ['n','a','m','e','s','p','a','c','e',' '] uncommented ||
                     metaCharsStartsWith ['e','n','d'] uncommented then
                    let acc' := if ctors.isEmpty then acc else (indName, ctors) :: acc
                    metaExtractFencedInductiveBlocksAux rest true false none acc'
                  else
                    metaExtractFencedInductiveBlocksAux rest true false (some (indName, ctors)) acc

meta def metaExtractFencedInductiveBlocks (content : String) : List (String × List String) :=
  let lines := metaSplitCharsOn '\n' content.toList [] []
  metaExtractFencedInductiveBlocksAux lines false false none []

/-- Backticked `snake_case` tokens that are tactics or Lean commands legitimately cited in docs. -/
meta def metaBareIdentAllowlist : List String :=
  [ "obend_law", "obend_unfold", "obend_split", "obend_tooth", "native_decide", "bv_decide",
    "norm_num", "eq_def", "f.eq_def", "decide_kernel", "import_obend", "obend_decl",
    "assert_axioms_tree", "assert_compiled", "docs_census", "check_docs_census",
    "census_environment", "always_ff", "always_comb", "no_sorry_ax" ]

/-- Non-Obend stdlib namespace roots excluded from `Upper.member` qualified-identifier checks. -/
meta def metaStdlibPrefixes : List String :=
  [ "Lean", "Std", "IO", "System", "List", "Array", "ByteArray", "String", "Substring",
    "Option", "Except", "BitVec", "Nat", "Int", "Bool", "Char", "UInt8", "UInt16",
    "UInt32", "UInt64", "USize", "Float", "Json", "Task", "Mutex", "Promise" ]

/-- File extensions excluded from `Upper.ext` qualified-identifier checks (`Cargo.toml`, `Replay.lean`). -/
meta def metaFileExtensions : List String :=
  [ "lean", "md", "rs", "toml", "lock", "json", "c", "h", "py", "sh", "so", "dylib", "a",
    "v", "sv", "wgsl", "vcd", "stl", "ngc", "obend", "obnb", "txt", "bin", "pcf", "asc", "il" ]

/-- A bare or qualified identifier worth resolving against `Lean.Environment`:
1. `snake_case` tokens `[a-z][A-Za-z0-9']*(_[A-Za-z0-9']+)+` (optionally dotted), or
2. qualified `Upper.member` tokens (`Replay.World`, `Term.hole`, `Quantity.linear`) that are not
   filenames (`Foo.lean`) or Lean stdlib namespaces (`List.map`). -/
meta def metaBareIdentToken? (raw : List Char) : Option String :=
  let tok := metaStripTrailingDotChars raw
  if tok.isEmpty then none
  else
    let parts := metaSplitCharsOn '.' tok [] []
    if parts.any (fun p => p.isEmpty || !p.toList.all metaIsSimpleIdentChar) then
      none
    else
      match parts, parts.getLast? with
      | _, none => none
      | first :: _ :: _, some last =>
          let fc := first.toList
          let lc := last.toList
          match fc, lc with
          | f0 :: _, l0 :: _ =>
              if first == "Obend" || metaStdlibPrefixes.contains first || metaFileExtensions.contains last then
                none
              else if l0.isLower && lc.contains '_' then
                some (String.ofList tok)
              else if f0.isUpper && (l0.isAlpha || l0 == '_') then
                some (String.ofList tok)
              else
                none
          | _, _ => none
      | [_], some last =>
          let lc := last.toList
          match lc with
          | c :: _ =>
              if c.isLower && lc.contains '_' then some (String.ofList tok) else none
          | [] => none
      | [], _ => none

meta def metaExtractBareIdents (content : String) : List String :=
  let spans := metaExtractInlineBacktickSpansAux content.toList false none []
  spans.foldl (fun acc sp =>
    if sp.any (fun c => c == ' ' || c == '(' || c == ':' || c == '/' || c == '-' || c == '@') then acc
    else
      match metaBareIdentToken? sp with
      | some t => if (t.splitOn ".").head? == some "Obend" then acc else acc ++ [t]
      | none => acc) []

meta def metaStringToLeanName (s : String) : Lean.Name :=
  (metaSplitCharsOn '.' s.toList [] []).foldl Lean.Name.str Lean.Name.anonymous

meta def metaDedupList {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs =>
      let rest := metaDedupList xs
      if rest.contains x then rest else x :: rest

meta def metaResolveRepoFile (relPath : String) : IO (Option System.FilePath) := do
  let candidates : List System.FilePath :=
    [ System.FilePath.mk relPath
    , System.FilePath.mk ("../" ++ relPath)
    ]
  for c in candidates do
    if ← c.pathExists then
      return some c
  return none

meta def metaObendLeanPathExists (relObendPath : String) : IO Bool := do
  let baseCandidates : List System.FilePath :=
    [ System.FilePath.mk relObendPath
    , System.FilePath.mk ("lean/" ++ relObendPath)
    , System.FilePath.mk ("../lean/" ++ relObendPath)
    ]
  let stemCandidates : List System.FilePath :=
    if metaCharsEndsWith ['.','l','e','a','n'] relObendPath.toList then []
    else
      [ System.FilePath.mk (relObendPath ++ ".lean")
      , System.FilePath.mk ("lean/" ++ relObendPath ++ ".lean")
      , System.FilePath.mk ("../lean/" ++ relObendPath ++ ".lean")
      ]
  for c in baseCandidates ++ stemCandidates do
    if ← c.pathExists then
      return true
  return false

meta def metaReviewMdPathExists (relReviewPath : String) : IO Bool := do
  return (← metaResolveRepoFile relReviewPath).isSome

meta def metaObendSubsystemExists (sub : String) : IO Bool := do
  let fileRel := s!"Obend/{sub}.lean"
  let dirRel := s!"Obend/{sub}"
  let candidates : List System.FilePath :=
    [ System.FilePath.mk fileRel
    , System.FilePath.mk ("lean/" ++ fileRel)
    , System.FilePath.mk ("../lean/" ++ fileRel)
    , System.FilePath.mk dirRel
    , System.FilePath.mk ("lean/" ++ dirRel)
    , System.FilePath.mk ("../lean/" ++ dirRel)
    ]
  for c in candidates do
    if ← c.pathExists then
      return true
  return false

meta def metaRunDocsCensus (docs : List String := metaTopLevelMarkdownDocs) :
    IO (Nat × Nat × Nat × List String × List (String × String) × List (String × String)) := do
  let mut pathsChecked := 0
  let mut rootsChecked := 0
  let mut missingDocs : List String := []
  let mut missingPaths : List (String × String) := []
  let mut missingRoots : List (String × String) := []
  for doc in docs do
    match ← metaResolveRepoFile doc with
    | none =>
        missingDocs := missingDocs ++ [doc]
    | some path =>
        let content ← IO.FS.readFile path
        let paths := metaDedupList (metaExtractObendLeanPaths content ++ metaExtractBacktickObendPaths content)
        let repoPaths := metaDedupList (metaExtractBacktickRepoPaths content)
        let reviews := metaExtractReviewMdPaths content
        let roots := metaExtractObendDottedRoots content
        for p in paths do
          pathsChecked := pathsChecked + 1
          unless ← metaObendLeanPathExists p do
            if !missingPaths.contains (doc, p) then
              missingPaths := missingPaths ++ [(doc, p)]
        for rp in repoPaths do
          pathsChecked := pathsChecked + 1
          if (← metaResolveRepoFile rp).isNone then
            if !missingPaths.contains (doc, rp) then
              missingPaths := missingPaths ++ [(doc, rp)]
        for rv in reviews do
          pathsChecked := pathsChecked + 1
          unless ← metaReviewMdPathExists rv do
            if !missingPaths.contains (doc, rv) then
              missingPaths := missingPaths ++ [(doc, rv)]
        for r in roots do
          rootsChecked := rootsChecked + 1
          unless ← metaObendSubsystemExists r do
            if !missingRoots.contains (doc, r) then
              missingRoots := missingRoots ++ [(doc, r)]
  return (docs.length, pathsChecked, rootsChecked, missingDocs, missingPaths, missingRoots)

/-- Trailing-component suffixes (length 1, 2, and 3) of every constant and imported `Obend` module
in `env`, so bare and qualified tokens (`lower_sound`, `Replay.World`, `Doc.Structured`) resolve
against the environment. -/
meta def metaConstantSuffixes (env : Lean.Environment) : Std.HashSet String := Id.run do
  let mut set : Std.HashSet String := {}
  for (constant, _) in env.constants.map₁.toList do
    if constant.isInternal then continue
    match constant.components.reverse with
    | c1 :: rest =>
      set := set.insert c1.toString
      if let c2 :: rest2 := rest then
        set := set.insert (c2.toString ++ "." ++ c1.toString)
        if let c3 :: _ := rest2 then
          set := set.insert (c3.toString ++ "." ++ c2.toString ++ "." ++ c1.toString)
    | [] => pure ()
  for modName in env.header.moduleNames.toList do
    match modName.components.reverse with
    | c1 :: rest =>
      set := set.insert c1.toString
      if let c2 :: rest2 := rest then
        set := set.insert (c2.toString ++ "." ++ c1.toString)
        if let c3 :: _ := rest2 then
          set := set.insert (c3.toString ++ "." ++ c2.toString ++ "." ++ c1.toString)
    | [] => pure ()
  return set

/-- Map from inductive full/suffix names (`Obend.Core.Term.Term`, `Term.Term`, `Term`, `Quantity`)
to the constructor lists of matching `InductiveVal` declarations in `env`. -/
meta def metaInductiveCtorIndex (env : Lean.Environment) : Std.HashMap String (List (List String)) := Id.run do
  let mut idx : Std.HashMap String (List (List String)) := {}
  for (constant, cinfo) in env.constants.map₁.toList do
    if constant.isInternal then continue
    match cinfo with
    | .inductInfo iv =>
        let ctors := iv.ctors.filterMap fun c =>
          match c.components.reverse with
          | last :: _ => some last.toString
          | [] => none
        let mut keys : List String := [constant.toString]
        match constant.components.reverse with
        | c1 :: rest =>
            if !keys.contains c1.toString then keys := keys ++ [c1.toString]
            if let c2 :: rest2 := rest then
              let k2 := c2.toString ++ "." ++ c1.toString
              if !keys.contains k2 then keys := keys ++ [k2]
              if let c3 :: _ := rest2 then
                let k3 := c3.toString ++ "." ++ c2.toString ++ "." ++ c1.toString
                if !keys.contains k3 then keys := keys ++ [k3]
        | [] => pure ()
        for k in keys do
          let prev := idx.getD k []
          idx := idx.insert k (ctors :: prev)
    | _ => pure ()
  return idx

/-- Evaluate an `Obend.Slot.Slot` (`Slot String String`) for each markdown document in `docs`
against `(env : Lean.Environment)` and the live repository filesystem snapshot. -/
meta def metaRunSlotDocsCensus (env : Lean.Environment) (docs : List String := metaCanonicalGovernedDocs) :
    IO (Nat × Nat × Nat × List (String × List String)) := do
  let suffixes := metaConstantSuffixes env
  let indIdx := metaInductiveCtorIndex env
  let mut totalPaths := 0
  let mut totalConsts := 0
  let mut blockedSlots : List (String × List String) := []
  for doc in docs do
    match ← metaResolveRepoFile doc with
    | none =>
        blockedSlots := blockedSlots ++ [(doc, [s!"docExists:{doc}"])]
    | some path =>
        let content ← IO.FS.readFile path
        let leanPaths := metaDedupList (metaExtractObendLeanPaths content ++ metaExtractBacktickObendPaths content)
        let repoPaths := metaDedupList (metaExtractBacktickRepoPaths content)
        let reviewPaths := metaDedupList (metaExtractReviewMdPaths content)
        let subs := metaDedupList (metaExtractObendDottedRoots content)
        let consts := metaDedupList (metaExtractBacktickObendConsts content)
        let bare := metaDedupList (metaExtractBareIdents content)
        let indBlocks := metaExtractFencedInductiveBlocks content
        totalPaths := totalPaths + leanPaths.length + repoPaths.length + reviewPaths.length
        totalConsts := totalConsts + consts.length + bare.length + indBlocks.length
        let mut holdsMap : List (String × Bool) := [(s!"doc:{doc}", true)]
        let mut supportKeys : List String := [s!"doc:{doc}"]
        for p in leanPaths do
          let k := s!"leanPath:{p}"
          let ok ← metaObendLeanPathExists p
          if !supportKeys.contains k then
            supportKeys := supportKeys ++ [k]
            holdsMap := holdsMap ++ [(k, ok)]
        for rp in repoPaths do
          let k := s!"repoPath:{rp}"
          let ok := (← metaResolveRepoFile rp).isSome
          if !supportKeys.contains k then
            supportKeys := supportKeys ++ [k]
            holdsMap := holdsMap ++ [(k, ok)]
        for rv in reviewPaths do
          let k := s!"reviewPath:{rv}"
          let ok ← metaReviewMdPathExists rv
          if !supportKeys.contains k then
            supportKeys := supportKeys ++ [k]
            holdsMap := holdsMap ++ [(k, ok)]
        for s in subs do
          let k := s!"subsystem:{s}"
          let ok ← metaObendSubsystemExists s
          if !supportKeys.contains k then
            supportKeys := supportKeys ++ [k]
            holdsMap := holdsMap ++ [(k, ok)]
        for c in consts do
          let k := s!"const:{c}"
          let n := metaStringToLeanName c
          let subOk ← match metaSplitCharsOn '.' c.toList [] [] with
            | ["Obend", sub] => metaObendSubsystemExists sub
            | _ => pure false
          let ok := env.contains n || env.header.moduleNames.contains n || suffixes.contains c || subOk
          if !supportKeys.contains k then
            supportKeys := supportKeys ++ [k]
            holdsMap := holdsMap ++ [(k, ok)]
        for b in bare do
          let k := s!"ident:{b}"
          let n := metaStringToLeanName b
          let ok := metaBareIdentAllowlist.contains b || env.contains n || suffixes.contains b
          if !supportKeys.contains k then
            supportKeys := supportKeys ++ [k]
            holdsMap := holdsMap ++ [(k, ok)]
        for (indName, ctors) in indBlocks do
          let candidates := indIdx.getD indName []
          for ctor in ctors do
            let k := s!"ctor:{indName}.{ctor}"
            let ok := candidates.any (fun actual => actual.contains ctor)
            if !supportKeys.contains k then
              supportKeys := supportKeys ++ [k]
              holdsMap := holdsMap ++ [(k, ok)]
          let blockKey := s!"inductive:{indName}"
          let blockOk := candidates.any (fun actual => ctors.all (fun c => actual.contains c))
          if !supportKeys.contains blockKey then
            supportKeys := supportKeys ++ [blockKey]
            holdsMap := holdsMap ++ [(blockKey, blockOk)]
        let slot : Obend.Slot.Slot String String := {
          supports := fun _ => supportKeys
          judge := fun cand => cand == doc
        }
        let holdsFn (f : String) : Bool :=
          match holdsMap.find? (fun p => p.1 == f) with
          | some (_, b) => b
          | none => false
        match slot.read holdsFn (some doc) with
        | .usable _ _ => pure ()
        | .blocked _ dead =>
            blockedSlots := blockedSlots ++ [(doc, dead)]
        | .rejected _ =>
            blockedSlots := blockedSlots ++ [(doc, ["rejected"])]
        | .empty =>
            blockedSlots := blockedSlots ++ [(doc, ["empty"])]
  return (docs.length, totalPaths, totalConsts, blockedSlots)

/-- `#check_docs_census` — compile-time gate verifying that all thirteen root markdown
documents exist and every `lean/Obend/...`, `Obend/.../*.lean`, backticked repo path,
`review/*.md` path, and `Obend.<Sub>.*` subsystem referenced in them resolves cleanly. -/
elab "#check_docs_census" : command => do
  let (docsChecked, pathsChecked, rootsChecked, missingDocs, missingPaths, missingRoots) ← liftIO metaRunDocsCensus
  unless missingDocs.isEmpty && missingPaths.isEmpty && missingRoots.isEmpty do
    throwError m!"#check_docs_census FAIL: missingDocs={missingDocs}, missingPaths={missingPaths}, missingRoots={missingRoots}"
  logInfo m!"#check_docs_census: {docsChecked} markdown docs verified; {pathsChecked} path references and {rootsChecked} Obend.* subsystem references resolve cleanly (0 stale references)."

/-- `#docs_census` — `Obend.Intention` + `Obend.Slot` compile-time gate over `DocEnvWorld`
verifying that all thirteen root architecture markdown docs have `.usable` slots with zero missing
files, zero missing `Obend.*` or bare/qualified identifiers, and zero hallucinated `inductive`
constructors in `Lean.Environment`. -/
elab "#docs_census" : command => do
  let env ← getEnv
  let (_, _, _, reported) ← liftIO (metaRunSlotDocsCensus env metaReportedDocs)
  unless reported.isEmpty do
    logWarning m!"#docs_census: {reported.length} reported doc(s) cite names the environment does not have: {reported}"
  let (docsChecked, totalPaths, totalConsts, blockedSlots) ← liftIO (metaRunSlotDocsCensus env)
  unless blockedSlots.isEmpty do
    throwError m!"#docs_census FAIL: {blockedSlots.length} governed doc slot(s) blocked on missing files, modules, identifiers, or inductive constructors: {blockedSlots}"
  logInfo m!"#docs_census: {docsChecked} governed markdown docs usable ({totalPaths} path supports, {totalConsts} constant/identifier/inductive supports, none dead)."

/-! ## Environment Snapshot Export (`#census_environment`) -/

/-- The package's constant names, sorted. -/
meta def metaEnvironmentNames (env : Lean.Environment) : Array String := Id.run do
  let mut names : Array String := #[]
  for (constant, _) in env.constants.map₁.toList do
    if constant.isInternal || constant.isInternalDetail then continue
    if constant.components.any (fun c => c == `_tooth || c == `_native) then continue
    let some idx := env.getModuleIdxFor? constant | continue
    let some module := env.header.moduleNames[idx]? | continue
    unless module.getRoot == `Obend do continue
    names := names.push constant.toString
  return names.qsort (fun a b => a < b)

/-- Write the environment to `path`; returns the number of constant names written. -/
meta def metaWriteEnvironment (env : Lean.Environment) (path : String) : IO Nat := do
  let names := metaEnvironmentNames env
  let modules := (env.header.moduleNames.filter (·.getRoot == `Obend)).size
  if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
  let header := s!"# environment: {names.size} constants of {modules} Obend modules, written by #census_environment (Obend/Tactic/DocsCensus.lean); a backticked name resolves as one of these or as the last one or two components of one\n# tactics and commands a document may cite (metaBareIdentAllowlist)\n"
  let allow := String.join (metaBareIdentAllowlist.map (· ++ "\n"))
  IO.FS.writeFile path (header ++ allow ++ String.join (names.toList.map (· ++ "\n")))
  return names.size

/-- `#census_environment "PATH"`: write the names the loaded environment has for vaults to
resolve cites against. -/
elab "#census_environment " path:str : command => do
  let env ← getEnv
  let n ← liftIO (metaWriteEnvironment env path.getString)
  logInfo m!"#census_environment: {n} names written to {path.getString}"

set_option maxRecDepth 20000 in
theorem extractObendLeanPaths_sample :
    extractObendLeanPaths "Obend/Leaf/Futamura.lean lean/Obend/Spec/CrossPackage.lean" =
      ["Obend/Leaf/Futamura.lean", "Obend/Spec/CrossPackage.lean"] := rfl

set_option maxRecDepth 20000 in
theorem extractBacktickObendPaths_sample :
    extractBacktickObendPaths "See `lean/Obend/Core/Term.lean` and `lean/Obend/Hardware/Gpu`." =
      ["Obend/Core/Term.lean", "Obend/Hardware/Gpu"] := rfl

set_option maxRecDepth 20000 in
theorem extractFencedInductiveBlocks_sample :
    extractFencedInductiveBlocks
      "```lean\ninductive Quantity where\n  | erased | affine | linear | unrestricted\ninductive Reuse where\n  | once\n  | reusable\n```" =
      [("Quantity", ["erased", "affine", "linear", "unrestricted"]),
       ("Reuse", ["once", "reusable"])] := rfl

set_option maxRecDepth 20000 in
example :
    extractReviewMdPaths "See review/DECISIONS-LEDGER.md and review/DECISIONS-20261031.md." =
      ["review/DECISIONS-LEDGER.md", "review/DECISIONS-20261031.md"] := rfl

set_option maxRecDepth 20000 in
theorem extractObendDottedRoots_sample :
    extractObendDottedRoots "Obend.Leaf.Futamura Obend.Spec.CrossPackage" =
      ["Leaf", "Spec"] := rfl

set_option maxRecDepth 20000 in
example :
    extractBacktickObendConsts "Check `Obend.Run.HyperLaw.oracle7Judge` and `Obend.Core.Nominal.kinded_refuses`." =
      ["Obend.Run.HyperLaw.oracle7Judge", "Obend.Core.Nominal.kinded_refuses"] := rfl

end Obend.Tactic.DocsCensus

end
