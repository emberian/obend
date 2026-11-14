module
/- Tooth of the join's reading (`Obend.Core.Proofs.Splice`, lane C2, 2026-11-01): with `+` in
place of `max`, a program that uses its `affine` hypothesis once on each branch is counted twice and
refused, so the join must be `max` at `affine`, and one rule serves every quantity. -/
public import Obend.Core.Proofs.Splice
public import Obend.Tactic.Tooth
import all Obend.Core.Proofs.Splice
import all Obend.Core.Proofs.BidirectionalCompleteness
import all Obend.Core.Ty

namespace Obend.Core.Proofs.JoinReading
open Obend.Core.Ty

#tooth affine_join_needs_max by mutation joinUses := fun x y => addUses x y

end Obend.Core.Proofs.JoinReading
