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
  twice is a no-op), `mergeFrom` (`mergePage_pushout`), `postAs`, `selectIn` (`select_keeps`,
  `select_needs_grant`), `reciteIn`.
* `Obend.Vault.Json` — `.obend/world.json`.
* `Obend.Vault.Form` — a captured membrane as a form: holes for data, a residual, a fill as a
  proposal the kernel judges through `commit` (`admit_no_amplification`, `eval_fill_eq_subst_residual`,
  `admit_conserves_total`).
* `Obend.Vault.Cli` — `obend open`, `status`, `merge`, `member`, `post`, `select`, `recite`, and the
  forms' `capture`, `abstract`, `form`, `fill`, `reshare`, `judge`.
* `Obend.Vault.Branch` — offline branches with a base, merged at the tip: the pushout of the two
  sides' disjoint writes (`merge_is_pushout`), clashes kept as conflict states, consent from every
  page in a write's cone (`landed_consents`), authority read where every revocation is visible
  (`settled_at_tip`). Its walkthrough is `lean/tests/vault/Branch.lean`.

The acceptance test is `lean/tests/vault/WALKTHROUGH.md`, executed by `lean/tests/vault/walkthrough.py`;
the forms' is `lean/tests/vault/FORMS.md`, executed by the same with `--doc`, and planted by
`lean/tests/vault/forms_planted.py`.
-/
public import Obend.Vault.Page
public import Obend.Vault.Law
public import Obend.Vault.Store
public import Obend.Vault.Json
public import Obend.Vault.Hyperedge
public import Obend.Vault.Escrow
public import Obend.Vault.Affordance
public import Obend.Vault.Projection
public import Obend.Vault.Mandate
public import Obend.Vault.Rehydration
public import Obend.Vault.Form
public import Obend.Vault.Carry
public import Obend.Vault.DragonsExchange
public import Obend.Vault.HardwareProjection
public import Obend.Vault.PhysicalProjection
public import Obend.Vault.SovereignEngine
public import Obend.Vault.Branch
public import Obend.Vault.BranchCli
public import Obend.Vault.Cli
