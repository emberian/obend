module
/-
# Obend.Leaf.Futamura — a retired name (2026-11-04)

The module that carried this name claimed first, second and third Futamura projections. The
first was `dataPinSpecialize (.app f a)` under the specialization slot and is now
`Obend.Leaf.Static.staticApply` with `staticApply_slot_sound`. The second and third specialized a
three-arm arithmetic function (`quoteMixTerm`) and the `apply` combinator (`quoteBookMixTerm`,
`quoteMetaCogenTerm`) with the Lean-side folder `dataPinSpecialize`; no specializer was ever a
`Core4` term and nothing was self-applied. Those definitions and theorems (`futamura2*`,
`futamura3*`, `cogenBookInCore`, `futamura2BookCompiler`, `inCoreBookCompiler`, `encodePinsOnly`,
`encodeStagedBookTerm`, `runStagedCompiler`, `specializeBookInCore`, `data_pin_flatten_sound`) are
gone, not renamed (`review/EXPERT-compiler-runtime-20261103.md` §2.1; the decision is in
`review/DECISIONS-20261031.md`, 2026-11-04).

What remains is the folder and the book specializer, in `Obend.Leaf.Static`, under the namespace
`Obend.Leaf.Static`. This file only re-exports that module so that `import Obend.Leaf.Futamura`
still resolves; it declares nothing, so `open Obend.Leaf.Futamura` is an error by design. When the
last importer has moved to `Obend.Leaf.Static`, delete this file.
-/
public import Obend.Leaf.Static
