module
/- The behaviour theorem for collecting the Core4 heap at a yield (design B4/T5), and
the typing transfer. Definitions: `Obend.Core.Collect`.

The relation is a renaming simulation. `Related f D s t` says `t` is `s` renamed by `f`
on a domain `D` that contains the roots and everything past `s`'s heap and is closed
under the heap: same control, same stack, and every `D`-cell of `s` is, renamed, the
`f`-image cell of `t`; `f` is injective on `D` and shifts the addresses past the heap.
Cells outside `D` (the garbage) are unconstrained. Because `f` and `D` never change,
lockstep allocation needs no extension of the renaming: both machines allocate at their
heap ends and `f` maps one end to the other.

* `related_collect`: `Related (collectRenaming s) (liveDomain s) s (collect s)`.
* `related_stepRaw`, `related_resume`, `related_runBounded` (outcomes agree unless the
  original ran out of heap, under any limits that give the related state the original's
  room, `RoomFor`), `related_runBounded_exact` (exact, capacity included, when
  the collected run is charged the heap it freed), `related_forceWith`,
  `related_materializeWith`, `related_completeWith`, `related_yieldedPlanWith` (the
  extracted Data and remaining budget agree), `related_segment` (the shape of the
  kernel's `runSegment`), `Related.trans` (collecting at every yield stays related to
  never collecting).
* `typed_related` / `typed_collect`: `StateTyping` (heap, control, stack typing and the
  lexical, busy and final-stack invariants) transfers at `collectTypes`.
* Inhabitants: a typed state with a garbage cell (`garbageTyping`) and a closed program
  that yields with a garbage cell (`yieldingTerm`), whose Plan extracts to the same
  encoded Data before and after collection. -/
public import Obend.Core.Proofs.Collect.Mark
public import Obend.Core.Proofs.Collect.Compact
public import Obend.Core.Proofs.Collect.Rename
public import Obend.Core.Proofs.Collect.Lockstep
public import Obend.Core.Proofs.Collect.Runs
public import Obend.Core.Proofs.Collect.Extract
public import Obend.Core.Proofs.Collect.Segment
public import Obend.Core.Proofs.Collect.Typing
public import Obend.Core.Proofs.Collect.Statements
