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
