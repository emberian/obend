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

public section
namespace Obend.Judge

/-- The registered formats. -/
def registry : List Format := [Lrat.format]

/-- Look a format up by name and version. -/
def Format.find? (name version : String) : Option Format :=
  registry.find? fun F => F.name == name && F.version == version

end Obend.Judge
end
