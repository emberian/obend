module
/-
# Obend.Judge — the judgment class and the certificate registry

`review/GENERALIZATION-20261031.md` G2; `review/VISION-CLAUDE-20261031.md` §6.2, §9.1;
`astra/ASTRA-VISION-20261031.md` §4.1, §8.A.

- `Obend.Judge.Class`: `Judge Obj Cert`, graded by `Nat` (`check`, `sound`, `refuted`, `complete` on a fragment,
  `mono`), `Verdict = ok | refused Clause Path | uncovered`, `Judge.deepen`, `Regime`, `TrustBase`,
  `Format` (with `checkBytes_sound` and a planted bad certificate), `Translation`.
- `Obend.Judge.Instances`: the bidirectional checker (the typing judge; `judge_iff_check` ties it to
  the slot's `Core4.judge`), the law machine probe, `coerce`, C4's
  validated linearization and the protocol envelope, as judges.
- `Obend.Judge.Lrat`: LRAT, the one foreign format end to end; `Obend.Judge.Identity`: conditional
  Boolean identities encoded into CNF with `encode_sound`; `Obend.Judge.Certified`: the 8-bit
  no-carry identity proved by the kernel's run of the checker on CaDiCaL's certificate.

`registry` is the formats a node accepts certificates in.
-/
public import Obend.Judge.Class
public import Obend.Judge.Instances
public import Obend.Judge.Lrat
public import Obend.Judge.Identity
public import Obend.Judge.Certified
public import Obend.Judge.AutomataConfinement
public import Obend.Judge.TranscriptPolicy
public import Obend.Judge.Clearing
public import Obend.Judge.RealAnalysis
public import Obend.Analysis.Hybrid
public import Obend.Analysis.SosLyapunov
public import Obend.Analysis.Format
public import Obend.Lower.Judge
public import Obend.Hardware.Judge
public import Obend.Law.Contract
public import Obend.Logic.Obligation
public import Obend.Elab.AutoCert
public import Obend.Elab.Workbook

public section
namespace Obend.Judge

/-- Registered `Format` for `"drex-clearing@1"` (backed by `drexClearingJudge`). -/
@[expose] def drexClearingFormat : Format :=
  { Obend.Logic.clearingFormat with name := "drex-clearing" }

/-- Registered `Format` for `"interval-bound@1"` (backed by `intervalJudge`). -/
@[expose] def intervalBoundFormat : Format :=
  { Obend.Elab.AutoCert.intervalFormat with name := "interval-bound" }

/-- Registered `Format` for `"groebner-ideal@1"` (backed by `groebnerJudge`). -/
@[expose] def groebnerIdealFormat : Format :=
  { Obend.Elab.AutoCert.groebnerFormat with name := "groebner-ideal" }

/-- **The one registry.** Every format a node, a session (`Obend.FFI.Bridge.sessionJudgeFormats`)
or a turn witness (`Obend.Vault.checkTurnWitness`) accepts is listed here, by name and version.
A format belongs here only if its decoders READ their input: a decoder that accepts any string
(as the 2026-11-03 `real-analysis@1` draft did, mapping every non-empty query to the trivial SOS
goal `1 ≥ 0`) makes every witness naming it pass, so it was removed on 2026-11-04. -/
@[expose] def registry : List Format :=
  [ Lrat.format
  , drexClearingFormat
  , Obend.Logic.clearingFormat
  , intervalBoundFormat
  , Obend.Elab.AutoCert.intervalFormat
  , Obend.Elab.AutoCert.taylorModelFormat
  , groebnerIdealFormat
  , Obend.Elab.AutoCert.groebnerFormat
  , Obend.Logic.worldCarryFormat
  , Obend.Logic.claimFormat
  , Obend.Elab.Workbook.workbookTransportFormat
  , dfaFormat
  , cfgCompactFormat
  , dclutchHoardFormat
  , tlsnTranscriptFormat
  , Obend.Analysis.hybridFlowpipeFormat
  , Obend.Analysis.sosLyapunovFormat
  , Obend.Analysis.format
  , Obend.Lower.format
  ] ++ Obend.Hardware.Judge.hardwareFormats

/-- Look a format up by name and version. -/
@[expose] def Format.find? (name version : String) : Option Format :=
  registry.find? fun F => F.name == name && F.version == version

end Obend.Judge
end
