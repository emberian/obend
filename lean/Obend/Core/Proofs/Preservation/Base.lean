module
/- Preservation, shared lemmas: weakening, the typing/usage algebra, value and stack
inversions, source decompositions every constructor's case uses. No dispatcher here:
the per-constructor case modules import this, the umbrella imports them. -/
public import Obend.Core.Proofs.Preservation.Base.Weaken
public import Obend.Core.Proofs.Preservation.Base.Heads
public import Obend.Core.Proofs.Preservation.Base.Values
public import Obend.Core.Proofs.Preservation.Base.Insert
public import Obend.Core.Proofs.Preservation.Base.Reusable
public import Obend.Core.Proofs.Preservation.Base.Focus
