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
* `Obend.Vault.Cli` — `obend open`, `status`, `merge`, `member`, `post`, `select`, `recite`.

The acceptance test is `lean/tests/vault/WALKTHROUGH.md`, executed by `lean/tests/vault/walkthrough.py`.
-/
public import Obend.Vault.Page
public import Obend.Vault.Law
public import Obend.Vault.Store
public import Obend.Vault.Json
