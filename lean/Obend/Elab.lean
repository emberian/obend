module
-- The elaborator over Core4: executable annotation preparation, type-directed coercions, the
-- checker's work measure, and the front end's gate (preparation, then `checkAgainst`). The
-- proofs (`Obend.Elab.Proofs.*`) are built by `lake build Obend`; nothing imports them.
public import Obend.Elab.Work
public import Obend.Elab.Prepare
public import Obend.Elab.Coerce
public import Obend.Elab.Gate
