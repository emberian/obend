/-
The two-page vault round trip (Obend.Doc). Run from `lean/`, after `lake build Obend.Doc`:

    lake env lean tests/doc/RoundTrip.lean

It reads `tests/doc/vault/*.md` into pages and cites under the deployed hash (cSHAKE256), checks
that each page's source and its rendering at the view it was read in are the file byte for byte,
moves Beta on and checks that Alpha's following cites read behind, and merges two concurrent edits
of Alpha into a conflict whose section alternatives are the two edits. It fails loudly on any
mismatch.
-/
import Obend.Doc
import Obend.Digest.Class

open Obend.Doc Obend.Slot

def H : Obend.Digest.HashBytes.Hash := Obend.Digest.Digest.hash []

def check (what : String) (ok : Bool) : IO Unit :=
  if ok then IO.println s!"ok   {what}" else throw (IO.userError s!"FAIL {what}")

#eval show IO Unit from do
  let alpha ← IO.FS.readFile "tests/doc/vault/Alpha.md"
  let beta ← IO.FS.readFile "tests/doc/vault/Beta.md"
  let V : Vault := [("Alpha", alpha), ("Beta", beta)]
  let W := V.read H
  let some A := W.current 1 | throw (IO.userError "no Alpha")
  let some B := W.current 2 | throw (IO.userError "no Beta")
  check "Alpha: source is the file" (A.source == alpha)
  check "Beta: source is the file" (B.source == beta)
  check "Alpha: rendered at its view is the file" (renderAt H W 1 == alpha)
  check "Beta: rendered at its view is the file" (renderAt H W 2 == beta)
  let cites := A.atoms.filterMap fun e => match e.2 with
    | .cite n c => some (e.1, n, c)
    | _ => none
  check "Alpha: two cites of Beta, Gamma stays text" (cites.map (·.2.1) == ["Beta", "Beta"])
  check "Alpha: every cite verifies under cSHAKE256"
    (cites.all fun (_, _, c) => (citeFacts c).all (holds H W))
  -- Beta moves on: a second version with one more line.
  let tail := (B.atoms.map (·.1)).foldl max 0
  let B' := B.apply [.add 100 (.text "A new line.\n") tail]
  let W' : World := fun p => if p = 2 then W 2 ++ [B'] else W p
  check "Beta moved: renders its new line" (renderAt H W' 2 == beta ++ "A new line.\n")
  let behind := (alpha.replace "[[Beta]]" "[[Beta]]{behind}")
  check "Beta moved: Alpha's following cites read behind" (renderAt H W' 1 == behind)
  -- A pinned cite of Beta's first version stays usable.
  match cites.head? with
  | some (a, n, c) =>
    let pin := { c with mode := .pinned }
    check "pinned cite of Beta v0 still verifies after the move"
      ((citeFacts pin).all (holds H W'))
    check "following cite run is usable before the move"
      ((sectionAt 1 (a - 1)).usable (holds H W) ⟨1, a, .cite n c⟩)
    check "following cite run reads blocked on `current` after the move"
      (match (sectionAt 1 (a - 1)).read (holds H W') (some ⟨1, a, .cite n c⟩) with
        | .blocked _ d => d == [.current c]
        | _ => false)
  | none => throw (IO.userError "no cite")
  -- Two authors insert a line between Alpha's heading and its blank line, concurrently.
  let ours := A.apply (Patch.insert 200 (.text "Ours.\n") 1 2)
  let theirs := A.apply (Patch.insert 300 (.text "Theirs.\n") 1 2)
  let M := Graph.merge ours theirs
  let WM : World := fun p => if p = 1 then W 1 ++ [M] else W p
  check "merge: a conflict after the heading"
    (M.heads 1 == [200, 300])
  let alts := (sectionAt 1 1).alternatives (holds H WM) (posted WM 1 1)
  check "merge: the section's alternatives are the two heads, as runs"
    (alts.map (·.atom) == M.heads 1)
  check "merge: nothing selected reads empty"
    (match (sectionAt 1 1).read (holds H WM) none with | .empty => true | _ => false)
  let marked := alpha.replace "# Alpha\n" "# Alpha\n<<<<<<<\nOurs.\n=======\nTheirs.\n>>>>>>>\n"
  check "merge: rendered with the conflict between the heading and the rest"
    (renderAt H WM 1 == marked)
  -- Resolving it: order the two (Connect), and the page is clean again.
  let R := M.apply [.connect 200 300]
  check "resolved by Connect: one head, both lines, in order"
    (R.heads 1 == [200] && R.source == alpha.replace "# Alpha\n" "# Alpha\nOurs.\nTheirs.\n")
