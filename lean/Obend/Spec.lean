module
/-
# Obend.Spec — the `.obend` front end: source text to a checked Core4 term

The one front end of Objective Bend, ported from minidregg (commit 092027a2:
`Compiler/ObjectiveBend{Parse,Law,Elaborate,C4,Contract,TermWire,FrontEnd,...}.lean`,
`Host/ObjectiveBend{FrontEnd,Preview}.lean`). It turns `.obend` source into the `Obend.Core.Term`
the demand machine runs, plus a typing proposal that the proof-producing checker
(`Obend.Core.Check.check`) accepts with a derivation or refuses.

## Trust boundary (minidregg docs/OBJECTIVE-BEND-FRONTEND.md, "Trust boundary", in its words)

Trusted, with no theorem: the parser (`Obend.Spec.Parse`), the elaborator and its typing
proposal's choices (`Obend.Spec.Elaborate`), the C4 implementation (`Obend.Spec.C4`). There is no
surface semantics, so nothing states that the core means what the source means.

What is proved of the output (`Obend.Spec.Proofs.*`): `accepted_typed`, `accepted_never_refused`,
`accepted_execution_semantics` (inhabited by `accept_inhabited`): a program the front end accepts is
closed, has the checker's derivation, is never refused by the bounded demand machine, and a
finished run of it extracts THE deep source evaluation of its term; `decode_json` and
`decodePacket_term`: the checker's decoder inverts the front end's rendering, so a receiver types
the front end's own term, never a parse of published bytes; the composition contract's laws
(`run_append`, `run_assoc`, `checkLayer_ok`, `discharge_ok`); `Specification<T>` closed under
`compose` (`composeTy_closed`, `compose_wrapper_typed`); the C4 vectors and the ordered-presentation
invariance on 4000 seeded DAGs (compiled). The port is held byte-identical in behaviour to Mini's
front end on Mini's own cohorts by `tests/run-obend-source.py` (REPORT-SPEC-20261030.md).
-/
public import Obend.Spec.Law
public import Obend.Spec.LawCompile
public import Obend.Spec.Syntax
public import Obend.Spec.Parse
public import Obend.Spec.Types
public import Obend.Spec.Annotated
public import Obend.Spec.C4
public import Obend.Spec.Contract
public import Obend.Spec.Elaborate
public import Obend.Spec.Sha256
public import Obend.Spec.FrontEnd
public import Obend.Spec.DataWire
public import Obend.Spec.Identity
public import Obend.Spec.Ecosystem
public import Obend.Spec.Capture
public import Obend.Spec.Preview
