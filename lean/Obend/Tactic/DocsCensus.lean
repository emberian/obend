/-
# `Obend.Tactic.DocsCensus` — Compile-Time Top-Level Markdown Census Gate

Provides pure path/identifier extractors and the `#check_docs_census` command
elaborator, verifying at compile time that all 7 top-level architecture and
metatheory documents (`DESIGN.md`, `PLAN.md`, `METATHEORY.md`, `PHYSICAL.md`,
`SILICON-ELABORATOR.md`, `NEXT-MATHEMATICA.md`, `DEOS-CONTRACTS-CONSENSUS.md`)
reference only existing `lean/Obend/.../*.lean` modules and valid `Obend.*`
subsystems.
-/

import Lean

namespace Obend.Tactic.DocsCensus

open Lean Elab Command

/-- The 7 canonical top-level markdown specification documents. -/
def topLevelMarkdownDocs : List String :=
  [ "DESIGN.md"
  , "PLAN.md"
  , "METATHEORY.md"
  , "PHYSICAL.md"
  , "SILICON-ELABORATOR.md"
  , "NEXT-MATHEMATICA.md"
  , "DEOS-CONTRACTS-CONSENSUS.md"
  ]

/-- Characters permitted inside a candidate module path or dotted identifier token. -/
def isTokenChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '/' || c == '.'

/-- Split a character list into contiguous tokens of `isTokenChar` characters. -/
def tokenizeChars (cs : List Char) (cur : List Char) (acc : List (List Char)) : List (List Char) :=
  match cs with
  | [] =>
      match cur with
      | [] => acc.reverse
      | _ => (cur.reverse :: acc).reverse
  | c :: rest =>
      if isTokenChar c then
        tokenizeChars rest (c :: cur) acc
      else
        match cur with
        | [] => tokenizeChars rest [] acc
        | _ => tokenizeChars rest [] (cur.reverse :: acc)

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
          some (String.intercalate "/" tail)
        else
          none
    | _ => none

/-- Extract all `Obend/.../*.lean` file paths referenced in markdown text `content`. -/
def extractObendLeanPaths (content : String) : List String :=
  (tokenizeChars content.toList [] []).filterMap tokenCharsToObendLeanPath?

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

/-- Run the documentation census across all 7 top-level markdown files. -/
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
        let roots := extractObendDottedRoots content
        for p in paths do
          pathsChecked := pathsChecked + 1
          unless ← obendLeanPathExists p do
            if !missingPaths.contains (doc, p) then
              missingPaths := missingPaths ++ [(doc, p)]
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

/-- `#check_docs_census` — compile-time gate verifying that all 7 top-level markdown
documents exist and every `Obend/.../*.lean` path and `Obend.<Sub>.*` identifier
referenced in them resolves to an existing file or subsystem in `lean/Obend/`. -/
elab "#check_docs_census" : command => do
  let report ← liftIO runDocsCensus
  unless report.isClean do
    throwError m!"#check_docs_census FAIL: missingDocs={report.missingDocs}, missingPaths={report.missingPaths}, missingRoots={report.missingRoots}"
  logInfo m!"#check_docs_census: {report.docsChecked} markdown docs verified; {report.pathsChecked} Obend/*.lean path references and {report.rootsChecked} Obend.* namespace references resolve cleanly (0 stale references)."

set_option maxRecDepth 20000 in
theorem extractObendLeanPaths_sample :
    extractObendLeanPaths "Obend/Leaf/Futamura.lean lean/Obend/Spec/CrossPackage.lean" =
      ["Obend/Leaf/Futamura.lean", "Obend/Spec/CrossPackage.lean"] := rfl

set_option maxRecDepth 20000 in
theorem extractObendDottedRoots_sample :
    extractObendDottedRoots "Obend.Leaf.Futamura Obend.Spec.CrossPackage" =
      ["Leaf", "Spec"] := rfl

#check_docs_census

end Obend.Tactic.DocsCensus
