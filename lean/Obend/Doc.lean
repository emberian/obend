module
/-
# Obend.Doc — pages, patches, merge, sections and cites (DESIGN §5)

TRUST: Lean core, `Obend.Slot` and the byte vocabulary of `Obend.Digest.HashBytes` only; no axiom beyond Lean's three, no `sorry`, no
`native_decide`. Every statement about a concrete page is checked by `decide` in the kernel.

* `Obend.Doc.Graph` — a page's state: atoms with stable identities and an alive/dead status, order
  edges, the order `Before` and its decided form.
* `Obend.Doc.Patch` — `Add | Delete | Connect | SetField`, `apply`, `compose`, `invert`;
  `apply_compose`, `apply_invert`, `apply_frame`.
* `Obend.Doc.Merge` — patch-morphisms (`Le`), the merge as pushout with its universal property
  (`merge_isPushout`, `pushout_unique`, `no_cocone`), files as the plain category with Mimram–Di
  Giusto's diagram (3) having no pushout there (`Teeth.files_no_pushout`), and the linearization
  whose conflicts are the antichains of heads (`content`, `walk_conflict`).
* `Obend.Doc.Section` — worlds of page histories, a section as `Slot Fact Run`, a cite as a
  support; `section_alternatives`, `conflict_is_section` (a merge conflict is the section's
  alternatives under an `empty` read), `pinned_cite_stays`, `identity_cite_stays`,
  `following_cite_stays` and `following_cite_behind` (rule (b): a following byte cite is current
  while the bytes it quotes are unchanged), `recite_holds`.
* `Obend.Doc.Render` — markdown read into a page as one patch (`[[P]]` cites P's identity, `![[P]]`
  embeds its text, `[[P#^b]]` quotes its block `b`),
  a vault read into a world, a page rendered at a view (`renderAt`, `renderAt_fresh`). The vault
  round trip is `lean/tests/doc/RoundTrip.lean`.
* `Obend.Doc.Backlinks` — the authenticated reverse index of cites (`mem_backlinks`), maintained
  on every posted version (`post_correct`), and all a move needs re-judged (`usable_unmoved`).
-/
public import Obend.Doc.Graph
public import Obend.Doc.Patch
public import Obend.Doc.Merge
public import Obend.Doc.Section
public import Obend.Doc.Render
public import Obend.Doc.Backlinks
