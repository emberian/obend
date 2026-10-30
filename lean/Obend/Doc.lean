module
/-
# Obend.Doc — pages, patches, merge, sections and cites (DESIGN §5)

TRUST: Lean core and `Obend.Slot` only; no axiom beyond Lean's three, no `sorry`, no
`native_decide`. Every statement about a concrete page is checked by `decide` in the kernel.

* `Obend.Doc.Graph` — a page's state: atoms with stable identities and an alive/dead status, order
  edges, the order `Before` and its decided form.
* `Obend.Doc.Patch` — `Add | Delete | Connect | SetField`, `apply`, `compose`, `invert`;
  `apply_compose`, `apply_invert`, `apply_frame`.
-/
public import Obend.Doc.Graph
public import Obend.Doc.Patch
