# REPORT 2026-10-30 — `Obend.Doc`: the patch algebra and the page

Lane Doc (Claude Opus 5.5), acting on `LANE-DOC-BRIEF-20261030.md`, in its own worktree on branch
`doc-lane`, rebased on `origin/dev` and pushed to `dev` after each step. Tags as in the trees:
**MEASURED** (a command run here, output read), **READ** (a file opened), **INFERRED** (my
reasoning). breadstuffs, minidregg and the paper were read only.

## 1. What landed (commits on `dev`)

| commit | what |
|---|---|
| `f2be76f` | `Obend.Doc.Graph` (the page graph, the order `Before`, the decided order `beforeB` with its closure certificate), `Obend.Doc.Patch` (the four operations and their duals, `apply`, `compose`, `invert`), root `Obend.Doc`, imported by `Obend`. |
| `b6ab6b4` | `Obend.Doc.Merge`: patch-morphisms, the merge as a pushout with its universal property, files as the plain category, Mimram–Di Giusto's diagram (3) with no pushout among files, the linearization with conflicts. |
| `640c909` | `Obend.Doc.Section`: worlds of page histories, `sectionAt p x : Slot Fact Run`, cites as supports, the conflict-is-the-section theorem, pinned and following cites when the source moves. |
| `afe0bd7` | `Obend.Doc.Render`: markdown read into a page as one patch, a vault into a world, a page rendered at a view; `lean/tests/doc/` with the two-page vault round trip. |
| (this commit) | this report. |

**MEASURED:** `LEAN_NUM_THREADS=2 lake build Obend.Doc` green, 11 jobs, no warnings in `Obend/Doc`.
`#print axioms` on the 21 named theorems below: `propext`, `Quot.sound`, `Classical.choice` at
most (`no_cocone` uses none). No `sorry`, no `native_decide`, no `axiom`. Every `#tooth` in the
five files reports a rejected stored proof. `lake env lean tests/doc/RoundTrip.lean` (from `lean/`):
16 of 16 checks `ok`. A full `lake build Obend` was not run in the worktree: `Obend.Doc` imports
only `Obend.Slot`, `Obend.Tactic.Tooth` and `Obend.Digest.HashBytes`, and the one shared file
touched is the import line added to `Obend.lean`.

## 2. The theorems

**Patch** (`Obend/Doc/Patch.lean`).
- `apply_compose : G.apply (compose p q) = (G.apply p).apply q`, as equality of graphs.
- `apply_invert : Patch.Effective G p → ((G.apply p).apply (invert p)).Same G ∧
  Patch.Effective (G.apply p) (invert p)`. `Same` is equality of every observation (`label`,
  `isDead`, `edge`), so this is the round trip on every atom, edge and tombstone, and it runs the
  other way too. `Effective` is the RCCS condition the Rust names in a comment (each operation
  changes what it targets); the teeth refute the round trip when it is dropped (connect an existing
  edge, invert, the edge is gone).
- `apply_frame`: an atom the patch does not touch keeps its content and status. With
  `apply_invert`, the round trip is the patch's business only on the atoms it touches.
- `invert_invert`, `step_dual`, `Same.apply` (a patch's effect depends only on observations).

**Merge** (`Obend/Doc/Merge.lean`). The morphism `G ⊑ H` (`Le`): contents, tombstones and edges
carried. Stable identities make hom-sets subsingletons, so a pushout is a least upper bound, and
the commuting square and the mediating arrow's uniqueness hold because the category is thin.
- `le_apply`: an authored patch is a morphism from the page it acts on.
- `merge_isPushout : Compatible A B → IsPushout A B (merge A B)` (above both; below every page
  above both). `pushout_unique`: two pushouts are the same page (`Le.antisymm`: morphisms both ways
  are `Same`). `empty_le`: the empty page is initial.
- `no_cocone : ¬ Compatible A B → ¬ ∃ Q, A ⊑ Q ∧ B ⊑ Q`. `compatible_of_addressed`,
  `merge_patches`: under content-addressed identities the merge of two authored patches from one
  page is their pushout.
- `merge_comm`, `merge_self` (as pages); `Le.before` (morphisms carry the order).
- `File`: live runs totally and strictly ordered, the objects of `L`. `Teeth.files_no_pushout`:
  diagram (3) (`a c b ← a b → a d b`) has **no pushout among files**: any file above both orders
  `c`,`d` one way and is then not below the file ordering them the other way.
  `Teeth.merge_antichain`: its merge is the pushout among pages, `c` and `d` live and unordered,
  not a file. `file_pushout`: a merge that is a file is the pushout among files.
- `walk_conflict`: where the page has two or more heads at `x`, the walk emits a `conflict` whose
  alternatives are exactly those heads.

**Section** (`Obend/Doc/Section.lean`). `sectionAt p x : Slot Fact Run`; supports of a run are
`live`, `head p x`, and its cite's facts (`verifies`; and `current` when following).
- `section_alternatives`: the slot's `alternatives` at `x` are the page's `heads` at `x` as runs,
  less any cite run whose cite fails.
- `conflict_is_section`: where the walk shows a conflict, the section's read with no selection is
  `empty`, and its `alternatives` are the conflict's alternatives as runs.
- `pinned_cite_stays`: a pinned cite run usable in its section before its source page moves is
  usable after. `following_cite_behind`: a following one, current before, reads
  `blocked r d` with `current c ∈ d` after. `recite_holds`: re-citing the current version makes
  its facts hold. All for every byte hash `H`.

**Render** (`Obend/Doc/Render.lean`). `renderAt_fresh`: where every cite of the page holds, its
rendering at the view is its source.

**Order** (`Obend/Doc/Graph.lean`). `beforeB_sound` (every graph), `beforeB_complete` and
`beforeB_iff` (where `Closed G (cone G a)`), `not_before_of_closed` (certified negatives).

**Teeth.** Each file has a `Teeth` namespace of `decide` statements on concrete pages and at
least one `#tooth`: `compose := fun p _ => p`, `invert := id`, `touches := []`,
`merge := fun A _ => A`, `File := True`, `citeFacts` swapped each way, `posted := []`,
`viewAtom := ""`. The round trip of a two-page vault, a following cite going `{behind}` after
its source moves, and the section of diagram (3)'s merge (`[c, d]`, read `empty`) are also
`decide` statements in the kernel.

## 3. Decisions (each with a critique and a meta-critique)

**D1. The cocompletion with stable identities: a thin category.** *Alternative:* Mimram–Di
Giusto's morphisms as data (partial injective maps), the free cocompletion characterised and
proved equivalent (their Theorem 20). *Why:* Pijul's model and dregg-doc's both name atoms once,
so a patch is determined by the identities it touches; the brief asks for the universal property
for *this* representation. *Critique:* the universal property of a least upper bound is a small
theorem; the freeness of the cocompletion is not proved, and "finitely cocomplete" here holds
only over compatible pages. *Meta-critique:* incompatibility is not a gap in the category but a
property of the identity discipline (`no_cocone`), which is why the decision for Ember (§5) is
about identities, not about categories.

**D2. Morphisms carry edges, not the transitive order.** *Why:* the merge is then plain union and
`Le` decidable by inspection of lists. *Critique:* two pages with one order and different edge
presentations (a transitive edge stored or not) are not isomorphic; Mimram–Di Giusto's objects
are transitive relations. *Meta-critique:* the order-carrying variant is one lemma away
(`Le.before` already gives it in one direction), but every proof of §2 would change; I did not
do it.

**D3. Two departures from the Rust, each for a theorem.** `SetField` carries an atom identity and
a superseding write is the patch `supersede` (assign, and tombstone the live assignments), so
fields are monotone and inside the pushout; the Rust needs a base-reading three-way merge for
them. And the dual of `Add` removes the atom (`unadd`), where the Rust's only disconnects it,
leaving it alive and unreachable: with that, `apply_invert` is equality of every observation.
*Critique:* the Rust's `merge_three_way` behaviour (a fast-forward of a superseding write lands
cleanly) is reproduced only if the superseding side tombstones the base value, which `supersede`
does; there is no theorem saying so. *Meta-critique:* a field-merge tooth would have cost ten
lines.

**D4. A certified order, not a proved-complete one.** `beforeB` walks a cone to depth `|edges|`;
its completeness for every graph is a pigeonhole argument I did not write. Every negative order
fact used (`files_no_pushout`, `merge_antichain`) carries a `Closed` certificate checked by
`decide`. *Critique:* the linearization and `heads` use `beforeB` directly, so on a page whose
cone is not closed at that depth they could show a false conflict. *Meta-critique:* no such page
exists (the depth bound is sufficient), but that is INFERRED, not proved.

**D5. `Add` orders after only; insertion is `Patch.insert`.** As in the Rust, `Add id c after`
stores `after → id` and nothing else, so a run added after a line is unordered against that
line's existing successor: a conflict, with the rest of the page as the other alternative.
`Patch.insert id c after before` adds the second edge. MEASURED on the vault: two authors' bare
`Add`s after Alpha's heading made a three-way conflict containing the whole page; with `insert`,
the two-alternative conflict a reader expects. The reader writes chains, so a page read from
disk is a file.

**D6. Following-cite currency is version equality.** `current c` holds iff `c.version` is the
source's latest. *Critique:* an edit anywhere in the source puts every following cite of it
behind, including ones whose cited bytes did not change. See §5.

**D7. Ranges are in bytes of the source text**, conflicts rendered with git's markers. The
commitment is over UTF-8 bytes (`utf8`, written out because `String.toUTF8` does not reduce in a
`module`; REPORT-20261030 §2.5). The round-trip vault has non-ASCII text and passes.

## 4. Not done, and why

- **The markdown round trip as a theorem.** `source (read md) = md` holds on the vault and on the
  `decide` teeth; the general statement needs the walk of a chain graph proved linear, which
  needs D4's completeness. Not attempted.
- **Embeds** (`![[Page]]`, a section whose selected candidate is the cite: a transclusion that
  renders the quoted bytes), **backlinks** (the reverse index of cites), **provenance/blame**
  (the Rust's `Author` on a patch) and **`obend open <vault>`** (SHIP §3 item 4's CLI): none
  started. The vault reader is the piece `open` would call.
- **Resolution patches as slot selections.** A conflict is the section (`conflict_is_section`);
  selecting a candidate in the slot does not yet write the patch (tombstone the others, or
  `Connect`) that resolves the conflict in the graph. The round-trip test resolves by `Connect`
  directly.

## 5. The one decision for Ember

**What a wikilink is.** Today `[[Beta]]` reads as a *following* cite of Beta's whole text at the
version read (D6). So any edit to Beta puts every link to it `{behind}` until each is re-cited
(`recite`). That is DESIGN §5's following cite taken literally, and wrong for a vault, where most
links are references, not quotes. Three choices:
(a) keep it: every link is a quote of the whole page, and a vault-wide `recite` on open makes the
noise go away;
(b) a following cite is current when its *range's bytes* are unchanged at the latest version,
not when its version is: re-justified automatically, `behind` only when what it quotes changed
(whole-page links are still behind on every edit);
(c) `[[Beta]]` is a cite of the page's identity only, with no bytes (current while the page
exists), and byte cites are `![[Beta]]` embeds and block references (`[[Beta#^id]]`, a range).
I would take (c) with (b)'s currency for the byte cites: it keeps DESIGN §5's pinned/following
distinction for quotes, where it means something. It changes `Cite` (range optional) and
`Vault.read`, not any theorem's shape.
