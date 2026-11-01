# Report: lane Leaf (Claude Opus, 2026-11-01)

Placed by the root from the lane's closing report. Commits `da7af0b..dfc26d6` (`136f435` Lean,
`dfc26d6` docs). Verified on hbox: tier 1, tier 2 (census clean), `obend`, `tests/run-leaf.py` 13/13,
`run-logic.py` 20/20. No `Term` constructor added; no former theorem removed or restated.

## What landed
| item | where | state |
|---|---|---|
| `Joins`: `Ahead` up to a base of closed unfolding pairs; `bequiv_of_joins` | `Obend/Leaf/UpTo.lean` | proved |
| flattening: `flatRow`, `flatObject`, `flatten_sound`, `flatten_object` | `Obend/Leaf/Flatten.lean` | proved; tooth |
| the book: slots, one definition per slot (method or thunk cell), dispatcher `Book.link`, `book_sound`, `emit_slot`, `emit_of_digest`/`emit_of_address`, `emit_typed` (by construction) | `Obend/Leaf/Emit.lean` | proved |
| the specialization slot: `machine_usable`, `book_usable_sound`, `specialize_choice`, `moved_pin_blocks`, `specialize_integrity` (existing slot theorems applied) | `Obend/Leaf/Specialize.lean` | proved; tooth |
| `ReviewMember` end to end: book computes 7, machine 7 on book and object; `Override` blocks the book by the object's pin and the machine answers 3; `Augmented +2n` blocks by object and layer pins, machine 9; `obend emit`/`obend specialize` | `Teeth/Leaf/{ReviewTeeth,MachineSeven}`, CLI | 13/13, kernel teeth |
| refinement against BendTT's `Eval` | §5 | stated, not done |

`flatten_sound (C) (hc : C.closedB) m : get C.flatten m ≈b get C.object m` is the compilation
theorem: `self` is the vtable, each `super.p` is read statically from `providesLast` on the prefix.
`Ahead` cannot relate an object to its flattening (each is recursive in itself), hence `Joins`.
`book_sound : get (emit C).link m ≈b get C.object m`.

## Decisions, with critique
- `Joins` duplicates `Ahead`'s simulation (~450 lines); merging (`Ahead := Joins ⊥`) touches every
  user of `Ahead`'s constructors: a parsimony item.
- `flatten_sound` assumes `C.closedB`; deriving the flattening's closedness from the object's is a
  scoping lemma not done.
- Pins carry a layer's name, fields and shape, not its term: compose-step metadata embeds the
  package knot, so adding `Override` moved `Twice`'s and `Augmented`'s metadata though nothing they
  compute changed; the vtable has no reflection, so metadata is not a support.
- One definition per slot with `self` a parameter is not BendTT's shape (§5).
- Typing preservation (the checker accepts each emitted body at its type) is not proved.

## 5. Refinement against `bendtt.lean`
`bendtt.lean` (bend `4f99f4c1`) builds unmodified at Lean 4.35 (11 s); the obstacle is that it is a
plain file with root names and library modules import only modules. Translation: `Nat` to unary,
`+` to `Nat.add`, `ifZero` to `Mat`, records to right-nested `Sig`/`Tup` in slot order, `self.m` to
a projection, `λ` to `Lam` with quantities. The live check forces one self-recursive
`dispatch(fuel, slot, args)` whose arms are the method bodies (Q2 copies require `Data`; defs call
only earlier defs or themselves on a descending column). Statement: fuel-indexed adequacy between
CBN `Evaluates` and CBV `Eval` for pure members, composed with `book_sound`; an interaction-tree
simulation through the runner's adapter for activities. Order: translation and pure adequacy first.

## Decision (taken by Claude under standing approval)
BendTT enters as a pinned plain file by commit and hash, with the refinement theorem in a tier-2
plain file (works today); move into the library when upstream adds a `module` header. The attested
alternative is refused: the refinement is the point.

## Follow-up (`53ce2b4`): the residual-`super` check Gemini asked for
`Obend/Leaf/Residual.lean`: `superOnlyProjected` (every `super` is `get super p` with `p` in the
flattened row beneath) and `vtable_clean`: under that check plus `cleanRow` (no body writes a record
literal of a suffix row's shape itself), the resolved vtable contains no residual `super` row.
Through `resolve_rename`, `resolve_subst_clean`, `resolve_clean`, `flatRow_clean`. Teeth:
`ReviewMember` passes both checks (`review_no_residual`); a layer passing `super` first-class fails the
check and its row literal does remain (`leak_refused_and_residual`). The BendTT translation runs both
checks first. `cleanRow` is not yet checked for all Elaborate output. Note: when C2's `Term.split`
lands, Leaf's traversals (`resolve`, `ahead_resolve`, `selfReads`, `recordBad`, `superOnlyProjected`)
each need a `split` case.

## Addendum: the kind's brand (after C1, 2026-11-01)

C1 writes a `#kind` brand on every record built at a kind, so the elaborated ReviewMember row is
`[#kind, review, twice]` and the emitter gave the brand slot 0 (`run-leaf` 9/13 on `5f425a5`).

Decision: **the brand is book metadata, not a slot.** It is one constant per kind, the same for
every instance and independent of `self`, so a slot and a dispatch per read is pure cost, and its
identity is static (it belongs beside the content address, as Gemini's argument says of
reflection). `Book` is now its entries in row order (`BookItem.slot` | `BookItem.static`):
`emitItems` makes the brand a static entry and numbers the slots over the rest (`slotted`);
`Book.defs`, `Book.slots`, `Book.statics` read them off. The dispatcher (`Book.link`) answers
the static entry from the book's own record, so the row the checker sees is unchanged and
`book_sound` is stated, unchanged, for every member of the row, `#kind` included: `link_ahead`
covers a static entry by reflexivity. `emit_slot` now says the `k`-th definition serves the
`k`-th member of the slot table, the row without its static members (`emitItems_defs`). Reads of
`self.#kind` map to no slot (the dispatcher serves them statically).

`flatRow` is unchanged and keeps the brand: it is a member of every flattened row, so
`super.#kind` resolves like any member, and the flattened object and the linked book have the
row type the nominal checker compares (`Core/Nominal`), brand included. The brand is in
`Composition.code` as a field, so a re-branded composition moves the object's pin.

Teeth: `brand_static` (a branded ReviewMember: slots `[review, twice]`, statics `[#kind]`, the
dispatcher answers the brand), `brand_sound` (`book_sound` at `#kind`). `obend emit` prints
`static #kind` and writes `statics` in the book file; `run-leaf` 14/14.
