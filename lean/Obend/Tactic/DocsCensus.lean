module
/-
# `Obend.Tactic.DocsCensus` — `Obend.Intention` & `Obend.Slot` Markdown Governance Gate

Instantiates `Obend.Intention` and `Obend.Slot` (`lean/Obend/Intention.lean`, `lean/Obend/Slot.lean`)
over `DocEnvWorld := Lean.Environment × RepoFsSnapshot` so that every canonical markdown
specification document (`AMBITION.md`, `README.md`, `PLAN.md`, `METATHEORY.md`,
`SILICON-ELABORATOR.md`, `QUALIFICATION-AND-SILICON-LEAN.md`) is
governed by a real `Slot` whose `supports` pin:
1. every Lean module path (`lean/Obend/.../*.lean` / `Obend/.../*.lean`) cited in the doc,
2. every review/ledger path (`review/*.md`) cited in the doc,
3. every `Obend.<Sub>` subsystem root cited in the doc, and
4. every backticked `Obend.*` theorem, definition, type, or module constant cited in the doc
   (verified against `Lean.Environment` via `env.contains constName`), and
5. (2026-11-04) every backticked bare identifier (`lower_sound`, `Interval.add_mem`), resolved
   exactly or as the trailing components of a constant; a small allowlist covers tactic names.
   The governed set is the root documents; the frontier and hardware documents are reported only.
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

/-- The six founding and synthesis markdown documents governed by full `DocEnvWorld` slots
(pinning `.lean` paths, `review/*.md` paths, and backticked `Obend.*` constants in `Lean.Environment`).
`review/DECISIONS-LEDGER.md` was listed until 2026-11-04; it is an untracked file of a suspended
lane, not a source of truth, and a clean checkout does not have it. -/
def canonicalGovernedDocs : List String :=
  [ "AMBITION.md"
  , "README.md"
  , "PLAN.md"
  , "METATHEORY.md"
  , "SILICON-ELABORATOR.md"
  , "QUALIFICATION-AND-SILICON-LEAN.md"
  ]

/-- The ten top-level specification markdown documents. -/
def topLevelMarkdownDocs : List String :=
  [ "AMBITION.md"
  , "README.md"
  , "DESIGN.md"
  , "PLAN.md"
  , "METATHEORY.md"
  , "PHYSICAL.md"
  , "SILICON-ELABORATOR.md"
  , "QUALIFICATION-AND-SILICON-LEAN.md"
  , "NEXT-MATHEMATICA.md"
  , "DEOS-CONTRACTS-CONSENSUS.md"
  ]

/-- Characters permitted inside a candidate module path or dotted identifier token. -/
def isTokenChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '/' || c == '.'

/-- Characters permitted inside a `review/*.md` path token (including hyphens `-`). -/
def isReviewPathChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '/' || c == '.'

/-- Characters permitted inside a dotted Lean constant identifier (`Obend.Foo.bar'`). -/
def isLeanIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.'

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

/-- Strip trailing `.` characters from a character list. -/
def stripTrailingDotChars (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '.')).reverse

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
  /-- Existing `Obend/.../*.lean` module relative paths under `lean/`. -/
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
    2. `leanPathExists relPath`: the cited `Obend/.../*.lean` module path exists on disk.
    3. `reviewPathExists relPath`: the cited `review/*.md` ledger/review path exists on disk.
    4. `subsystemExists sub`: the cited `Obend.<Sub>` subsystem root exists on disk.
    5. `constExists constName`: the backticked `Obend.*` constant or module exists in `Lean.Environment`. -/
inductive DocFact where
  | docExists (docPath : String)
  | leanPathExists (relPath : String)
  | reviewPathExists (relPath : String)
  | subsystemExists (sub : String)
  | constExists (constName : Lean.Name)
  deriving DecidableEq, Repr

/-- Evaluate whether a `DocFact` support holds in `w : DocEnvWorld`.
    For `.constExists n`, checks `w.1.contains n` (a theorem/definition/type constant in
    `Lean.Environment`), `w.1.header.moduleNames.contains n` (an imported module in
    `Lean.Environment`), or a 2-component `Obend.<Sub>` subsystem root. -/
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

/-- A pinned markdown document selection carrying its target path and extracted `DocFact` supports. -/
structure DocPin where
  docPath  : String
  supports : List DocFact
  deriving DecidableEq, Repr

/-- Extract the complete deduplicated support list of `DocFact`s cited by `docPath` with `content`. -/
def extractDocSupports (docPath : String) (content : String) : List DocFact :=
  let leanFacts := (dedupList (extractObendLeanPaths content)).map DocFact.leanPathExists
  let reviewFacts := (dedupList (extractReviewMdPaths content)).map DocFact.reviewPathExists
  let subFacts := (dedupList (extractObendDottedRoots content)).map DocFact.subsystemExists
  let constFacts := (dedupList (extractBacktickObendConsts content)).map
    (fun c => DocFact.constExists (stringToLeanName c))
  DocFact.docExists docPath :: (leanFacts ++ reviewFacts ++ subFacts ++ constFacts)

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
naming the exact missing files or missing `Obend.*` constants. -/
theorem docSlot_stale_iff_blocked (w : DocEnvWorld) (docPath : String) :
    docIntention.current w (candidateDocPin w docPath) = false ↔
      (docSlot docPath).read (holdsDocFact w) (some (candidateDocPin w docPath)) =
        .blocked (candidateDocPin w docPath)
          ((candidateDocPin w docPath).supports.filter fun f => !holdsDocFact w f) :=
  docIntention.stale_iff_blocked rfl w

/-! ## Filesystem Resolution & Legacy `#check_docs_census` / Full `#docs_census` Elaborators -/

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

/-- Verify that a relative `Obend/.../*.lean` path exists under `lean/`. -/
def obendLeanPathExists (relObendPath : String) : IO Bool := do
  let candidates : List System.FilePath :=
    [ System.FilePath.mk relObendPath
    , System.FilePath.mk ("lean/" ++ relObendPath)
    , System.FilePath.mk ("../lean/" ++ relObendPath)
    ]
  for c in candidates do
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
        let paths := extractObendLeanPaths content
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
  [ "AMBITION.md"
  , "README.md"
  , "DESIGN.md"
  , "PLAN.md"
  , "METATHEORY.md"
  , "THESIS.md"
  , "GROUNDING.md"
  ]

meta def metaIsTokenChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '/' || c == '.'

meta def metaIsReviewPathChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '/' || c == '.'

meta def metaIsLeanIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.'

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

meta def metaStripTrailingDotChars (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '.')).reverse

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

/-- Documents whose bare identifiers are resolved and reported, without failing the build: the
design frontiers that name planned theorems and the hardware/RTL documents that name Verilog
signals, RPC methods and CLI flags in backticks. -/
meta def metaReportedDocs : List String :=
  [ "PHYSICAL.md"
  , "SILICON-ELABORATOR.md"
  , "QUALIFICATION-AND-SILICON-LEAN.md"
  , "NEXT-MATHEMATICA.md"
  , "DEOS-CONTRACTS-CONSENSUS.md"
  ]

/-- Backticked snake_case tokens that are not Lean constants but are legitimately written in
backticks: tactics and commands this tree defines, Lean tactics, and `f.eq_def`. -/
meta def metaBareIdentAllowlist : List String :=
  [ "obend_law", "obend_unfold", "obend_split", "obend_tooth", "native_decide", "bv_decide",
    "norm_num", "eq_def", "f.eq_def", "decide_kernel", "import_obend", "obend_decl",
    "assert_axioms_tree", "assert_compiled", "docs_census", "always_ff", "always_comb" ]

/-- A bare identifier worth resolving: `[a-z][A-Za-z0-9]*(_[A-Za-z0-9]+)+`, optionally dotted
(`Foo.bar_baz`), optionally primed. Anything else in backticks (paths, flags, prose) is not. -/
meta def metaBareIdentToken? (raw : List Char) : Option String :=
  let tok := metaStripTrailingDotChars raw
  if tok.isEmpty then none
  else
    let parts := metaSplitCharsOn '.' tok [] []
    match parts.getLast? with
    | none => none
    | some last =>
      let lc := last.toList
      match lc with
      | [] => none
      | c :: _ =>
        if !(c.isLower) then none
        else if !(lc.contains '_') then none
        else if !(lc.all fun ch => ch.isAlphanum || ch == '_' || ch == '\'') then none
        else if parts.any (·.isEmpty) then none
        else some (String.ofList tok)

meta def metaExtractBareIdents (content : String) : List String :=
  let spans := metaExtractInlineBacktickSpansAux content.toList false none []
  spans.foldl (fun acc sp =>
    -- a span that is one token, not a phrase with spaces or operators
    if sp.any (fun c => c == ' ' || c == '(' || c == ':' || c == '/' || c == '-' || c == '@') then acc
    else
      match metaBareIdentToken? sp with
      | some t => if (t.splitOn ".").head? == some "Obend" then acc else acc ++ [t]
      | none => acc) []

meta def metaTopLevelMarkdownDocs : List String :=
  [ "AMBITION.md"
  , "README.md"
  , "DESIGN.md"
  , "PLAN.md"
  , "METATHEORY.md"
  , "PHYSICAL.md"
  , "SILICON-ELABORATOR.md"
  , "QUALIFICATION-AND-SILICON-LEAN.md"
  , "NEXT-MATHEMATICA.md"
  , "DEOS-CONTRACTS-CONSENSUS.md"
  ]

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
  let candidates : List System.FilePath :=
    [ System.FilePath.mk relObendPath
    , System.FilePath.mk ("lean/" ++ relObendPath)
    , System.FilePath.mk ("../lean/" ++ relObendPath)
    ]
  for c in candidates do
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
        let paths := metaExtractObendLeanPaths content
        let reviews := metaExtractReviewMdPaths content
        let roots := metaExtractObendDottedRoots content
        for p in paths do
          pathsChecked := pathsChecked + 1
          unless ← metaObendLeanPathExists p do
            if !missingPaths.contains (doc, p) then
              missingPaths := missingPaths ++ [(doc, p)]
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

/-- Every constant name's trailing-component suffixes of length 1 and 2 (`lower_sound`,
`Lower.lower_sound`), so a bare token in a document resolves the way a reader resolves it. -/
meta def metaConstantSuffixes (env : Lean.Environment) : Std.HashSet String := Id.run do
  let mut set : Std.HashSet String := {}
  for (constant, _) in env.constants.map₁.toList do
    if constant.isInternal then continue
    match constant.components.reverse with
    | last :: rest =>
      set := set.insert last.toString
      if let penult :: _ := rest then
        set := set.insert (penult.toString ++ "." ++ last.toString)
    | [] => pure ()
  return set

/-- Evaluate an `Obend.Slot.Slot` (`Slot String String`) for each markdown document in `docs`
against `(env : Lean.Environment)` and the live repository filesystem snapshot. -/
meta def metaRunSlotDocsCensus (env : Lean.Environment) (docs : List String := metaCanonicalGovernedDocs) :
    IO (Nat × Nat × Nat × List (String × List String)) := do
  let suffixes := metaConstantSuffixes env
  let mut totalPaths := 0
  let mut totalConsts := 0
  let mut blockedSlots : List (String × List String) := []
  for doc in docs do
    match ← metaResolveRepoFile doc with
    | none =>
        blockedSlots := blockedSlots ++ [(doc, [s!"docExists:{doc}"])]
    | some path =>
        let content ← IO.FS.readFile path
        let leanPaths := metaDedupList (metaExtractObendLeanPaths content)
        let reviewPaths := metaDedupList (metaExtractReviewMdPaths content)
        let subs := metaDedupList (metaExtractObendDottedRoots content)
        let consts := metaDedupList (metaExtractBacktickObendConsts content)
        let bare := metaDedupList (metaExtractBareIdents content)
        totalPaths := totalPaths + leanPaths.length + reviewPaths.length
        totalConsts := totalConsts + consts.length + bare.length
        let mut holdsMap : List (String × Bool) := [(s!"doc:{doc}", true)]
        let mut supportKeys : List String := [s!"doc:{doc}"]
        for p in leanPaths do
          let k := s!"leanPath:{p}"
          let ok ← metaObendLeanPathExists p
          supportKeys := supportKeys ++ [k]
          holdsMap := holdsMap ++ [(k, ok)]
        for rv in reviewPaths do
          let k := s!"reviewPath:{rv}"
          let ok ← metaReviewMdPathExists rv
          supportKeys := supportKeys ++ [k]
          holdsMap := holdsMap ++ [(k, ok)]
        for s in subs do
          let k := s!"subsystem:{s}"
          let ok ← metaObendSubsystemExists s
          supportKeys := supportKeys ++ [k]
          holdsMap := holdsMap ++ [(k, ok)]
        for c in consts do
          let k := s!"const:{c}"
          let n := metaStringToLeanName c
          let subOk ← match metaSplitCharsOn '.' c.toList [] [] with
            | ["Obend", sub] => metaObendSubsystemExists sub
            | _ => pure false
          let ok := env.contains n || env.header.moduleNames.contains n || subOk
          supportKeys := supportKeys ++ [k]
          holdsMap := holdsMap ++ [(k, ok)]
        -- Bare identifiers (`lower_sound`, `Interval.add_mem`): the exact name, or a constant whose
        -- trailing components are the token (`Obend.Lower.lower_sound`). Until 2026-11-04 only
        -- `Obend.`-prefixed tokens were checked, and 113 cited theorem names dangled unseen.
        for b in bare do
          let k := s!"ident:{b}"
          let n := metaStringToLeanName b
          let ok := metaBareIdentAllowlist.contains b || env.contains n || suffixes.contains b
          supportKeys := supportKeys ++ [k]
          holdsMap := holdsMap ++ [(k, ok)]
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

/-- `#check_docs_census` — compile-time gate verifying that all top-level markdown
documents exist and every `Obend/.../*.lean` path, `review/*.md` path, and `Obend.<Sub>.*`
subsystem referenced in them resolves to an existing file or subsystem. -/
elab "#check_docs_census" : command => do
  let (docsChecked, pathsChecked, rootsChecked, missingDocs, missingPaths, missingRoots) ← liftIO metaRunDocsCensus
  unless missingDocs.isEmpty && missingPaths.isEmpty && missingRoots.isEmpty do
    throwError m!"#check_docs_census FAIL: missingDocs={missingDocs}, missingPaths={missingPaths}, missingRoots={missingRoots}"
  logInfo m!"#check_docs_census: {docsChecked} markdown docs verified; {pathsChecked} path references and {rootsChecked} Obend.* subsystem references resolve cleanly (0 stale references)."

/-- `#docs_census` — `Obend.Intention` + `Obend.Slot` compile-time gate over `DocEnvWorld`
verifying that all governed markdown docs (`AMBITION.md`, `README.md`, `PLAN.md`, `METATHEORY.md`,
`SILICON-ELABORATOR.md`, `QUALIFICATION-AND-SILICON-LEAN.md`) have
`.usable` slots with 0 missing `.lean`/`review/*.md` files and 0 missing `Obend.*` constants in
`Lean.Environment`. -/
elab "#docs_census" : command => do
  let env ← getEnv
  let (_, _, _, reported) ← liftIO (metaRunSlotDocsCensus env metaReportedDocs)
  unless reported.isEmpty do
    logWarning m!"#docs_census: {reported.length} reported (non-governed) doc(s) cite names the environment does not have: {reported}"
  let (docsChecked, totalPaths, totalConsts, blockedSlots) ← liftIO (metaRunSlotDocsCensus env)
  unless blockedSlots.isEmpty do
    throwError m!"#docs_census FAIL: {blockedSlots.length} governed doc slot(s) blocked on missing files, modules or constants (paths, `Obend.*` names and bare identifiers in backticks are all supports): {blockedSlots}"
  logInfo m!"#docs_census: {docsChecked} governed markdown docs usable ({totalPaths} path supports, {totalConsts} constant and identifier supports, none dead)."

/-! ## The environment, written for the vaults (2026-11-04)

`#census_environment PATH` writes the names a document may cite, one per line: every constant of
the package (a module under `Obend`; not internal; no `_tooth` or `_native` component, as
`Obend.AssertAxioms.theoremCensus` reads them) and the tactics and commands of
`metaBareIdentAllowlist`, sorted; lines starting with `#` are provenance. A vault whose kind page
says `environment: PATH` reads it as the set a backticked name resolves against
(`Obend.Vault.Page.backtickNames`, `unresolvedNames`), by this module's rule for a bare identifier: a
full name, or the last one or two components of one (`metaConstantSuffixes`). The census writes it
to `.lake/build/census/environment.txt` (`Obend/Census.lean`, tier 2, the whole tree);
`tests/decisions/Environment.lean` writes the tier-1 library's to the same path. -/

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

/-- Write the environment to `path`; the number of constant names written. -/
meta def metaWriteEnvironment (env : Lean.Environment) (path : String) : IO Nat := do
  let names := metaEnvironmentNames env
  let modules := (env.header.moduleNames.filter (·.getRoot == `Obend)).size
  if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
  let header := s!"# environment: {names.size} constants of {modules} Obend modules, written by #census_environment (Obend/Tactic/DocsCensus.lean); a backticked name resolves as one of these or as the last one or two components of one\n# tactics and commands a document may cite (metaBareIdentAllowlist)\n"
  let allow := String.join (metaBareIdentAllowlist.map (· ++ "\n"))
  IO.FS.writeFile path (header ++ allow ++ String.join (names.toList.map (· ++ "\n")))
  return names.size

/-- `#census_environment "PATH"`: write the names the loaded environment has for the vaults to
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

-- `#check_docs_census` and `#docs_census` are run by `Obend/Census.lean` (tier 2, before a merge), not
-- here: a library build (`lake build`, tier 1) does not read the root documents, and a stale document
-- must stop a merge, not the library (2026-11-04).

end Obend.Tactic.DocsCensus

end
