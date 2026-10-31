/-
The two-page vault round trip (Obend.Doc). Run from `lean/`, after `lake build Obend.Doc`:

    lake env lean tests/doc/RoundTrip.lean

It reads `tests/doc/vault/*.md` into pages and cites under the deployed hash (cSHAKE256), checks
that each page's source and its rendering at the view it was read in are the file byte for byte,
moves Beta on and checks that only Alpha's embed reads behind (its identity links and its block
reference do not, rule (b)), rewrites Beta's marked line and checks that the block reference then
reads behind, checks Beta's backlinks and their maintenance, and merges two concurrent edits
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
  check "Alpha: four cites of Beta, Gamma stays text"
    (cites.map (·.2.1) == ["Beta", "Beta", "Beta", "Beta#^answer"])
  check "Alpha: two identity links, an embed, a block reference"
    (cites.map (·.2.2.span) == [.identity, .identity, .page, .block "answer"])
  check "Alpha: every cite holds under cSHAKE256"
    (cites.all fun (_, _, c) => (citeFacts c).all (holds H W))
  let some (ea, en, ec) := cites.find? (·.2.2.span == .page) | throw (IO.userError "no embed")
  let some (ba, bn, bc) := cites.find? (·.2.2.span == .block "answer") | throw (IO.userError "no block")
  let some (ia, inm, ic) := cites.head? | throw (IO.userError "no link")
  -- Beta moves on: a second version with one more line.
  let tail := (B.atoms.map (·.1)).foldl max 0
  let B' := B.apply [.add 100 (.text "A new line.\n") tail]
  let W' : World := fun p => if p = 2 then W 2 ++ [B'] else W p
  check "Beta moved: renders its new line" (renderAt H W' 2 == beta ++ "A new line.\n")
  check "Beta moved: only the embed reads behind"
    (renderAt H W' 1 == alpha.replace "![[Beta]]" "![[Beta]]{behind}")
  check "the identity link is usable after the move"
    ((sectionAt 1 (ia - 1)).usable (holds H W') ⟨1, ia, .cite inm ic⟩)
  check "the block reference is usable after the move: its bytes did not change"
    ((sectionAt 1 (ba - 1)).usable (holds H W') ⟨1, ba, .cite bn bc⟩)
  check "a pinned embed of Beta v0 still verifies after the move"
    ((citeFacts { ec with mode := .pinned }).all (holds H W'))
  check "the embed's run is usable before the move"
    ((sectionAt 1 (ea - 1)).usable (holds H W) ⟨1, ea, .cite en ec⟩)
  check "the embed's run reads blocked on `current` after the move"
    (match (sectionAt 1 (ea - 1)).read (holds H W') (some ⟨1, ea, .cite en ec⟩) with
      | .blocked _ d => d == [.current ec]
      | _ => false)
  check "re-cited at the new version, the embed holds"
    ((citeFacts (recite H W' ec)).all (holds H W'))
  -- Beta rewrites its marked line: now the block reference is behind too.
  let some (la, _) := B'.atoms.find? (fun e => match e.2 with
      | .text t => (t.splitOn "^answer").length > 1
      | _ => false) | throw (IO.userError "no marked line")
  let B'' := B'.apply [.delete la, .add 101 (.text "The answer is 42. ^answer\n") la, .connect 101 100]
  let W'' : World := fun p => if p = 2 then W' 2 ++ [B''] else W p
  check "Beta's marked line rewritten: renders it"
    (renderAt H W'' 2 == (beta.replace "forty-two" "42") ++ "A new line.\n")
  check "now the block reference reads behind as well"
    (renderAt H W'' 1 == (alpha.replace "![[Beta]]" "![[Beta]]{behind}").replace "[[Beta#^answer]]"
      "[[Beta#^answer]]{behind}")
  -- Backlinks: the reverse index of cites.
  let bl := backlinks W [1, 2] 2
  check "Beta's backlinks are Alpha's four cites" (bl.map (·.atom) == cites.map (·.1))
  check "Alpha's backlinks are Beta's one link" ((backlinks W [1, 2] 1).map (·.source) == [2])
  let A' := A.apply [.delete ea]
  let WA : World := fun p => if p = 1 then W 1 ++ [A'] else W p
  check "Alpha drops its embed: the maintained index is the recomputed one"
    ((Index.post (backlinks W [1, 2]) 1 A' 2).map (·.atom) == (backlinks WA [1, 2] 2).map (·.atom) &&
      (backlinks WA [1, 2] 2).length == 3)
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
