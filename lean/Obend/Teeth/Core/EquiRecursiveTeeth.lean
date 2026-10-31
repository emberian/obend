module
public import Obend.Core.Check
public meta import Obend.Core.Check
open Obend.Core.Ty Obend.Core.Check
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
#guard sameType ⟨[(0, .natural)], [], []⟩
  (.arrow .reusable .unrestricted (.variable 0) .boolean)
  (.arrow .reusable .unrestricted .natural .boolean)
#guard !sameType {} .natural .boolean
#guard sameType {} (.field "b" .boolean (.field "a" .natural .emptyRow))
  (.field "a" .natural (.field "b" .boolean .emptyRow))
#guard sameType ⟨[(0, .natural)], [], []⟩
  (.field "a" .boolean (.field "a" (.variable 0) .emptyRow))
  (.field "a" .boolean .emptyRow)
#guard !sameType {} (.field "a" .boolean (.field "a" (.custody 7) .emptyRow))
  (.field "a" .boolean .emptyRow)
#guard !sameType ⟨[(0, .field "a" .natural (.variable 0))], [], []⟩
  (.variable 0) (.field "a" .natural .emptyRow)
#guard sameType ⟨[(0, .arrow .once .linear .natural (.variable 0)),
  (1, .arrow .once .linear .natural (.variable 2)),
  (2, .arrow .once .linear .natural (.variable 1))], [], []⟩ (.variable 0) (.variable 1)
#guard !sameType ⟨[(0, .natural)], [], [0]⟩ (.variable 0) .natural
