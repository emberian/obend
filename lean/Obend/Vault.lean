module
/-
# Obend.Vault — `obend open ~/vault`: a directory of markdown as pages, with a world beside it

DESIGN §5's day one. Every `.md` is a page, every wikilink a cite (`[[P]]` of P's identity, `![[P]]`
of its text, `[[P#^b]]` of its block `b`), every `law:` line of a page's frontmatter a law, every
folder a kind whose `_kind.md` laws are ancestors of every page in it. The vault stays markdown;
the world in `.obend/` keeps each page's versions, its cites with their commitments, its laws (as
its frontmatter lines), the members and their grants.

* `Obend.Vault.Page` — frontmatter, measures, the rendering with sections, the patch a changed file
  is (`editPatch`), a member's proposal (`postPatch`), a selection (`selectPatch`).
* `Obend.Vault.Law` — the judge: a page's laws and its kinds', compiled (`Obend.Spec.LawCompile`),
  combined (`Obend.Law.effective`), run; `judge_admits`, `judge_refuses`; what would pass.
* `Obend.Vault.Store` — the world beside the vault and each command: `openVault` (`open_idem`:
  twice is a no-op), `mergePage` (`mergePage_pushout`), `postAs`, `selectIn` (`select_keeps`,
  `select_needs_grant`), `reciteIn`.
* `Obend.Vault.Json` — the world as JSON (`.obend/world.json` before the log; the log's turns and
  checkpoint now).
* `Obend.Vault.Log` — the log is truth: records, their bytes, `replay`, `state_eq_replay_log`,
  `recover_eq_replay_prefix`, `checkpoint_is_cache`, the log as Pillar 1's well-linked chain.
* `Obend.Vault.Replay` — the deployed entry's turns (opens, posts, merges, resolutions, forms, ledger
  rows) and step, the instance of `Obend.Vault.Log`; forms, their receipts and the merges' conflicts
  are part of the world it replays.
* `Obend.Vault.Form` — a captured membrane as a form: holes for data, a residual, a fill as a
  proposal the kernel judges through `commit` (`admit_no_amplification`, `eval_fill_eq_subst_residual`,
  `admit_conserves_total`).
* `Obend.Vault.FormCheck` — each judgment a fill of a form makes, as a term with the state's changing
  fields and the request open, checked once at capture and kept in the world: the judge runs that
  term filled (`judge_runs_checked`), typed by the one check (`kept_typed`), none re-checked
  (`rechecked_zero`).
* `Obend.Vault.Transport` — a form out in the world, carried across changes of its context:
  consumer-relative equality (value, support, authority; `effect_fresh_display_fresh`), the fresh
  capture and what it admits (`admitsAt_recapture`, `judge_recapture_iff`), a continuity contract and
  `transport_sound`, standing grants with revocation winning the merge (`merge_revocation_wins`,
  `handoff_no_absence`), and the identity of a proposal's intent.
* `Obend.Vault.Retention` — the right to forget a prefix of the log under a declared contract: the
  compacted log and its reading (`state_eq_replay_compacted`, `recover_eq_replay_prefix_compacted`,
  `recoverLog_plain`); at the deployed machine, `forget_sound`, `forget_refused_when_needed`,
  `late_correction_refused`.
* `Obend.Vault.Cost` — what a command cost, counted by the binary and said with `OBEND_COST`.
* `Obend.Vault.LogBytes` — the log read at offsets into its bytes and written as bytes, each proved its
  list twin (`encode_bytes_eq`, `parseFromAt_eq`, `parseLogAt_eq`, `holdsAt_eq`).
* `Obend.Vault.Cli` — `obend open`, `status`, `merge`, `member`, `post`, `select`, `recite`, `log`,
  the forms' `capture`, `abstract`, `form`, `fill`, `reshare`, `judge`, and their transport's `offer`,
  `grant`, `revoke`, `grants`, `transport`, `obligations`, `confirm`, and `forget`, `fork`, and the
  vault's reasons (`Obend.Reasons`): `reasons observe`, `assume`, `withdraw`, `explain`, `defeat`,
  `propose`, `admit`, `status`, `why`, and a fill's `--because`, which the judge admits only while it
  is supported.
* `Obend.Vault.Branch` — offline branches with a base, merged at the tip: the pushout of the two
  sides' disjoint writes (`merge_is_pushout`), clashes kept as conflict states, consent from every
  page in a write's cone (`landed_consents`), authority read where every revocation is visible
  (`settled_at_tip`). Its walkthrough is `lean/tests/vault/Branch.lean`.
* `Obend.Vault.Merge` — `obend merge`: two vault stores read as branches of their base and merged by
  `Branch.merge`, a page both sides wrote merged by `mergePage`; the tip keeps the store and judges
  every write by the store's own write (`tip_lands_iff_store_lands`); conflicts are kept in the store
  and resolved by `obend branch resolve`.

The acceptance test is `lean/tests/vault/WALKTHROUGH.md`, executed by `lean/tests/vault/walkthrough.py`;
the forms' is `lean/tests/vault/FORMS.md`, executed by the same with `--doc`, and planted by
`lean/tests/vault/forms_planted.py`; `lean/tests/vault/CRASH.md` (`crash.py`) stops `obend` in the
middle of a write and opens the vault again; `lean/tests/vault/TRANSPORT.md` carries a form across
seven perturbations of its context; `lean/tests/vault/RETAIN.md` forgets a prefix of the log.
-/
public import Obend.Vault.Page
public import Obend.Vault.Law
public import Obend.Vault.Store
public import Obend.Vault.Json
public import Obend.Vault.Log
public import Obend.Vault.Replay
public import Obend.Vault.Transport
public import Obend.Vault.Retention
public import Obend.Vault.Cost
public import Obend.Vault.LogBytes
public import Obend.Vault.Hyperedge
public import Obend.Vault.Escrow
public import Obend.Vault.Affordance
public import Obend.Vault.Projection
public import Obend.Vault.Mandate
public import Obend.Vault.Rehydration
public import Obend.Vault.Form
public import Obend.Vault.FormCheck
public import Obend.Vault.CheckedCarry
public import Obend.Vault.ChunkedWorld
public import Obend.Vault.HardwareProjection
public import Obend.Vault.PhysicalProjection
public import Obend.Vault.UnifiedDeos
public import Obend.Vault.SwarmLedgerSeams
public import Obend.Vault.Branch
public import Obend.Vault.BranchCli
public import Obend.Vault.Merge
public import Obend.Vault.Cli
