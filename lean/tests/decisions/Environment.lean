/-
The environment, written from the library behind the `obend` binary (`Obend.Main`'s imports): the
file `review/ledger/_kind.md` and the decisions walkthroughs name as `environment:`, against which
`obend open` resolves the backticked names a page cites (`Obend/Tactic/DocsCensus.lean`,
`#census_environment`; `Obend/Vault/Page.lean`, "Names cited in backticks"). The census writes the
same file over the whole tree, apps and teeth included (`lake build Obend.Census`, tier 2); this
file writes it in the time of loading the binary's modules, which `lake build obend` has built
(the umbrella `Obend` pulls the applications and does not build at HEAD, 2026-11-04):

    cd lean && lake env lean tests/decisions/Environment.lean

`tests/decisions/walkthrough.py` runs it when the file is missing.
-/
import Obend.Main
import Obend.Tactic.DocsCensus

#census_environment ".lake/build/census/environment.txt"
