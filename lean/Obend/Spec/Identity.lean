module
/-
# Obend.Spec.Identity — the identity of the front end compiled into this program

`identity` is SHA-256 (lowercase hex) of `manifest`, which lists the SHA-256 of every source file
that decides what the front end emits: the law fragment, the AST, the parser, the proposal types,
the annotated core, the linearizer, the contract, the elaborator, the front-end driver and the
SHA-256 used for fingerprints. The manifest is computed while THIS module is elaborated, from the
files on disk next to it. Every listed file is imported here, so editing any of them changes its
module trace and rebuilds this one: the constant cannot go stale against the compiled code. Anyone
can recompute it with `sha256sum` (the manifest format is one `NAME SHA256` line per file under a
header line). Any edit to a listed file, comments included, is a new identity.

A capture (`Obend.Spec.Capture`) names the front end that made it and a preview refuses a capture
made by another. Ported from minidregg `Compiler/ObjectiveBendFrontEndIdentity.lean` (commit
092027a2), whose manifest header `DREGG/OBJECTIVE-BEND/FRONT-END/v1` is kept; the file list is this
tree's split of Mini's modules, so the identity differs from Mini's by construction.
-/
public import Obend.Spec.Law
public import Obend.Spec.Syntax
public import Obend.Spec.Parse
public import Obend.Spec.Types
public import Obend.Spec.Annotated
public import Obend.Spec.C4
public import Obend.Spec.Contract
public import Obend.Spec.Elaborate
public import Obend.Spec.FrontEnd
public import Obend.Spec.Sha256
meta import Obend.Spec.Sha256
@[expose] public section
namespace Obend.Spec.Identity
open Lean Elab Term
set_option autoImplicit false

/-- The fingerprinted sources, in manifest order (paths relative to this file's directory). -/
meta def sources : List String :=
  ["Law.lean", "Syntax.lean", "Parse.lean", "Types.lean", "Annotated.lean", "C4.lean", "Contract.lean",
   "Elaborate.lean", "FrontEnd.lean", "Sha256.lean"]

def manifestHeader : String := "DREGG/OBJECTIVE-BEND/FRONT-END/v1"

/-- The manifest text, read at elaboration time. -/
elab "obend_front_end_manifest%" : term => do
  let some dir := (System.FilePath.mk (← getFileName)).parent
    | throwError "front-end identity: no directory for {← getFileName}"
  -- Keep the header as an expression dependency rather than splicing it into the literal.
  let mut text := "\n"
  for name in sources do
    let bytes ← IO.FS.readBinFile (dir / name)
    text := text ++ name ++ " " ++ Sha256.hex bytes ++ "\n"
  return mkApp2 (mkConst ``String.append) (mkConst ``manifestHeader) (mkStrLit text)

def manifest : String := obend_front_end_manifest%

/-- The identity: the hash of the manifest (a few hundred bytes, hashed at run time). -/
def identity : String := Sha256.hexString manifest

end Obend.Spec.Identity

end
