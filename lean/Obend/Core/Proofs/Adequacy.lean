module
/- Source/graph correspondence for the new partial lazy edition. All running
and finished raw transitions preserve the concrete graph relation. Every
normally finished closed computation, through rawRun or runBounded at any
limits, has an independent source evaluation to the same ground observation.
This module does not yet inhabit Representation: administrative progress and
source-to-machine completeness remain separate substantive obligations. -/
public import Obend.Core.Proofs.Adequacy.Defs
public import Obend.Core.Proofs.Adequacy.Source
public import Obend.Core.Proofs.Adequacy.Scoped
public import Obend.Core.Proofs.Adequacy.Meaning
public import Obend.Core.Proofs.Adequacy.Graph
public import Obend.Core.Proofs.Adequacy.Origins
public import Obend.Core.Proofs.Adequacy.CasesEval
public import Obend.Core.Proofs.Adequacy.CasesReturn
public import Obend.Core.Proofs.Adequacy.CasesControl
public import Obend.Core.Proofs.Adequacy.StepRaw
public import Obend.Core.Proofs.Adequacy.Run
public import Obend.Core.Proofs.Adequacy.Examples
public import Obend.Core.Proofs.Adequacy.Reach
public import Obend.Core.Proofs.Adequacy.Birth
public import Obend.Core.Proofs.Adequacy.Safety
public import Obend.Core.Proofs.Adequacy.SafetyRaw
public import Obend.Core.Proofs.Adequacy.Progress
public import Obend.Core.Proofs.Adequacy.Sound
