# Decisions ledger, 2026-10-29 to 10-31

Every decision a lane or reviewer addressed to Ember, with who took it and on what authority.
"Standing approval" is Ember's "let's raise our ambition and I approve. go forward as you like"
(10-31). Anything marked TAKEN BY CLAUDE is reversible; the cost of reversing is stated.

## Decided by Ember

| decision | choice | where |
|---|---|---|
| Align the checker with declarative typing, with solvers where completeness is out of reach | yes | `review/CHECKER-COMPLETENESS-REPORT`, Argon's answer, `METATHEORY.md` §6 |
| Type agreement descends into types, equi-recursively (option c) | yes | `REPORT-EQUIREC-20261031.md` |
| Stored selection: incumbent-first default, chooser override, policies per slot | yes, after Astra's analysis | `astra/ASTRA-SELECTION-20261031.md`, `Obend/Slot/Selection.lean` |
| No per-theorem axiom lists; one crawling census | yes | `393eb2b`, memory `feedback-no-manual-axiom-lists` |
| Statements may be restructured for compositionality | yes | ProofEng lane |
| The 15 choice-free `#print axioms` pins stay: they pin something nonstandard (a choice-free set), which the census cannot state | yes | `lean/docs/REPORT-PROOFENG-20261031.md` |
| Modularity first: Lean modules and typeclasses from day one | yes | `REPORT-20261030.md` |
| Build our own thing; depend on Bend, never fork it | yes | `DESIGN.md` §7 |

| `quote` is a kernel function on held terms and `splice` a turn; no new `Term` constructor; program-level quote on values refused | yes (2026-11-01) | `review/QUOTE-ORIENTATION-20261101.md` §3, §8 |
| `linear` separates from `affine` in the checker: exact discharge enforced in the kernel | yes (2026-11-01) | gates T7; `review/ALGEBRAIC-SUBTYPING-20261031.md` §5.1 |
| Nominal kinds (the kind cell; every instance tagged; the kind's law an ancestor; dispatch by kind) | yes (2026-11-01) | `lean/docs/REPORT-EXTENDS-20261031.md` |
| REFLECTION's open question: the intensional fixed point is inside the knot with the description a term (Löb's rule) | taken by Claude from the literature, 2026-11-01 | `review/QUOTE-ORIENTATION-20261101.md` §2.6, §8 |

## Taken by Claude under standing approval (reversible)

| decision | what was taken | cost to reverse |
|---|---|---|
| **What a wikilink is** (Doc lane) | (c): `[[Beta]]` cites identity only; `![[Beta]]` and `[[Beta#^id]]` are byte cites; a byte cite stays current while its bytes are unchanged (rule b). The LawDoc brief says "Ember chose (c)"; that was my reading of standing approval, not a choice you made. | `Cite` and `Vault.read` in `Obend/Doc/{Section,Render}.lean`; theorem shapes unchanged; the Vault lane is building on it now |
| Lost reply with no ending (Runner) | (b): an `abandon` event, obligation kept, run ended | one constructor, one spec clause, one proof case |
| Initial plan choices rechecked at dispatch (Runner) | citations added to `Cfg.init`, default none | small |
| Package law at adoption and relaw (LawDoc) | (b) adoption judged with old = new state; (c) relaw of a package law refused, change is by upgrade | two compiler arms and two theorems |
| Front end grant (Elab) | (b) `checkWork` replaces `typeFuel`; cohorts re-pinned at 43,237 | revert one commit; cohorts back to 4096 |
| Inherited refusal carries `{by, reason}` in its own verdict type (Law) | kept the richer verdict | a kernel judging by effective laws must accept it; alternatives were unnamed reason or a Core4 label-join primitive |
| Journal supports are the transitive meaning closure (lane B) | kept | two one-line changes to the flat scheme |
| `Accepted`'s constructor public; wire theorems in a proof module (lane C, D21) | kept | none; Kimi's D5 argument covers it |
| Public constructors on execution evidence (lane A, D5) | kept, closed by Kimi's review | none |

## Still open

| item | where it is written | size |
|---|---|---|
| `World` has no version non-return law: pins may alternate and a stale justification can come back true (Kimi §2; lane A's D15 deliberately left nano's forward-only law out) | `Obend/Slot/World.lean` has `holds_congr`, `retired_dead`, `retired_step` only | one field plus the collision stance; the runner's `Legal` does not depend on it |
| `@[expose]`-all per definitional module is a migration expedient (Kimi §3) | `REPORT-20261030.md` §2 | a tightening pass, measured by the one-edit rebuild check |
| Rename `slot_repair` (a bundle of reading and permanence lemmas) and `Integrity.transition` | Kimi §1; runner report §9 | names only |
| Journal baseline `env-b3ddd73.jsonl` (8.9 MB) is committed; ignore or keep | lane B D6 | one `.gitignore` line |
| Runner: decision authority beyond the `.me` chooser; per-slot selection descriptor; versioned candidate domain; richer "nothing admissible" diagnostics; leases and hysteresis | `REPORT-RUNNER-20261031.md` §8–9; Astra selection §8 | a lane |
| Runner adapter: reference-tree statement, depth deepening, ticks, response typing, plan authority through Law, holes in emitted plans | `REPORT-RUNNER-20261031.md` §10 | a lane |
| Elab: open-template check still `Check.check`; `#tooth` on `prepare_checks` fails on a compiler-generated dependency; seed-with-extra-members not wired | `REPORT-ELAB-20261031.md` | small each |
| Law: machine-to-`Admits` connection; `c3_tree_is_chain`; `keeps` typing | `REPORT-LAW-20261030.md` | medium |
| The template elaborator by Simple-sub with emitted coercions | `review/ALGEBRAIC-SUBTYPING-20261031.md` §3–4; `METATHEORY.md` §5.5 | a lane, next after Extends |
| `≈b` via Iris-Lean; Leaf emitter and refinement against `bendtt.lean` | `METATHEORY.md` §2, §5.6 | two lanes |
| minidregg, nanodregg, delvetalk `require obend` and delete their twins | `SHIP.md` §3 | a lane per tree; the reason the library exists |
| Carry between package versions | `SHIP.md` §4.6 | a lane |
| Papers never fetched: Moran–Sands 1999, Brandt–Henglein 1998, Leijen 2005, Ducournau 1994, Cardelli 1986, Birgisson 2014 | `review/PRIOR-ART-20261030.md` | Anna's key |
| `respectTransparency` debt from the 4.35 bump | `REPORT-LEAN435-20261031.md` | in the ProofEng lane now |

## In flight

ProofEng (speed, restructuring, waterfall); Extends (cross-package `extends`, intentions as slots,
laws across packages, orthogonal protocols); Vault (`obend open`).

## Plan for the open items (2026-10-31, launched)

| item | lane | brief |
|---|---|---|
| World non-return law; renames; runner authority and descriptor; adapter gaps | SlotRun (opus) | `lean/docs/LANE-SLOTRUN-BRIEF-20261031.md` |
| machine-to-`Admits`; `c3_tree_is_chain`; `keeps` typing; laws reach the runner | LawFinish (opus) | `lean/docs/LANE-LAWFINISH-BRIEF-20261031.md` |
| the trees consuming `obend` | Adoption study (opus, read-only) | `review/ADOPTION-BRIEF-20261031.md` |
| `≈b`, `mix_assoc`, Iris-Lean usability | Equiv study and spike (opus) | `review/EQUIV-BRIEF-20261031.md` |
| the six unfetched papers | Papers (sonnet) | `review/PAPERS-BRIEF-20261031.md` |
| expose-all tightening | after ProofEng lands (same files) | queued |
| Elab leftovers; Simple-sub template elaborator; carry | after Extends lands (Spec files) | queued |
| Leaf emitter and refinement | after the Equiv spike and the runner adapter | queued |
