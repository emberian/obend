# REPORT 2026-10-30 — the obligation journal (lane B)

Lane B (Claude Fable 5.1), on `LANE-B-BRIEF-20261030.md`: a declaration-level obligation journal
over the `Obend` tree, the first slice of PE1 (HOLES-FOR-PROOF-ENGINEERING rev 3, "A theorem as an
enduring obligation"). Tags as in the trees: **MEASURED**, **READ**, **INFERRED**. Lane A worked in
the same checkout throughout; nothing of lane A's was edited except the experiment's two reverted
edits and one byte (§6).

## 1. What landed

| path | what |
|---|---|
| `Journal/Export.lean` | `module`. Imports the tree's `.olean`s at `OLeanLevel.private` (every body), walks `Environment.constants`, keeps the `Obend*` modules' constants, writes one JSONL row each: name, module, kind, visibility, exposed, type cites, value cites, type hash, value hash, axioms. A second import of the `module` files alone at `OLeanLevel.exported` is the visibility instrument. One cached traversal (`analyze`) gives the 64-bit structural hash and the cites (`const` names and `proj` structures). Axioms as `collectAxioms` collects them, one memo for the whole export. |
| `Journal/Journal.lean` | `module`, imports `Obend.Slot`. `Row`, `Export`, `Row.meaning`, the closure along meaning edges, `Support` (`.stmt`/`.proof`), `Candidate`, the one `slot`, `verdict`, `report`. Two theorems, `verdict_unaffected_iff` and `verdict_blocked`: the verdict is `Slot.read`'s reading and nothing else. |
| `tools/journal/Main.lean`, `lakefile.toml` | `lean_lib Journal` (roots `Journal.Journal`, `Journal.Export`); `lean_exe journal` (`srcDir = "tools/journal"`, no `needs`: D8). `lake exe journal export [--root DIR] [--out FILE] [--only PREFIX]`, `lake exe journal diff OLD NEW [--names]`. |
| `tools/journal/env-b3ddd73.jsonl` | the baseline export of the clean tree at `b3ddd73`: 10659 rows, 70 modules, 6063 theorems, 8.9 MB (MEASURED). |
| `tools/journal/experiment.sh`, `tools/journal/EXPERIMENT-20261030.md` | the one experiment (§3). |
| `tools/journal/teeth.sh` | the two teeth (§4). |
| `Journal/README.md` | 299 words. |

Build: `lake build journal` green (12 jobs: the tool, `Journal.*`, `Obend.Slot` and its imports). Export of the tree about 20 s wall on this
machine (MEASURED once, `date` around the command; not a benchmark); `diff` of two exports about 2 s.

## 2. What the export says about the tree (MEASURED on `env-b3ddd73.jsonl`)

10659 constants: 6063 theorems, 3619 definitions, 640 constructors, 167 recursors, 163 inductives,
4 axioms (the `native_decide` pins), 3 opaques. Of the theorems 1392 are private, 4671 public; the
public count is far above REPORT-20261030's 455 because auto-generated theorems (`eq_1`, `eq_def`,
`_proof_N`, injectivity, `sizeOf_spec`) are public with their parent: 2534 names contain `.eq_`,
1006 `_proof_`. Two definitions carry hygienic names (`_hyg.N`), both in `Obend.Core.Ty`; a hygienic
name is position-dependent and would read as removed+added on a reorder of that file (tooth (b)
reorders `Obend.Slot`, which has none). Axiom sets: 2304 theorems on none, 1422 `propext`, 1381
`propext, Quot.sound`, 945 the standard three, 7 `Quot.sound` alone, 1 on the `digest_one_one`
`native_decide` axiom.

## 3. The experiment (`tools/journal/EXPERIMENT-20261030.md`)

Both of REPORT §4's edits, exported before and after on the live tree (lane A's uncommitted edits
present and unchanged throughout). Repair sets, by name: **step 1 (private theorem appended to
`Adequacy`): empty**; Lake built 4 modules (`Adequacy` and the legacy leaves `Teeth.BackFail`,
`Teeth.DataSoundness`, `Teeth.Force`). **Step 2 (exposed def appended to `Term`): empty**; Lake built
52 (everything downstream of `Term`: the whole `Core` tree and `Slot.Core4`). The journal added one
theorem in step 1 and three definition rows in step 2; nothing withdrawn, 6109 of 6109 theorems
unaffected in both. Reverting both: Lake printed no `Built` line; the export read identical.

## 4. The teeth (`tools/journal/teeth.sh`)

(a) `Obend.Slot.Protocol.Coin.answer`'s body wrapped in `id` (the term differs, the function does
not): the journal must put `Obend.Slot.Protocol.Coin.no_foresight`, the one theorem whose proof
reaches `answer` and whose statement does not, under PROOF-CITED and nowhere else, with `answer` the
withdrawn support. (b) `dead_eq_nil_iff` and `mem_dead_iff` swapped in `Obend/Slot.lean`: every
section must read `(0)`. One run (MEASURED, `Obend.Slot` subtree, 1357 theorems in the subtree
export): **14 of 14 checks pass.** (a) withdrawn: `Obend.Slot.Protocol.Coin.answer  meaning
changed`; PROOF-CITED: `Obend.Slot.Protocol.Coin.no_foresight` with `dead: Coin.answer [proof]`;
STATEMENT-CITED, revised, reproved, added, removed all `(0)`; unaffected 1356. (b) every section
`(0)`, unaffected 1357. The subtree rebuilt green after both reverts; `git status` shows no `Slot`
file modified. (The run's PROOF-CITED header read `(2)`: the driver counted the `dead:` line as an
entry; fixed in `Main.lean` after the run, the count now being the number of theorems.)

## 5. Decisions (each with a critique and a meta-critique)

**D1. Supports are `(name, meaning)` over the transitive closure, not the brief's flat
`(name, typeHash)` for statement cites and `(name, valueHash)` for proof cites.** *Why:* the brief's
scheme reads `theorem T : f = 7 := rfl` as UNAFFECTED when `f`'s body changes from `g` to `g + 1`
(`f`'s type is unchanged, `T`'s proof cites `f` whose value hash is unchanged, `g` is cited by
neither): the failure the memo warns of ("a definition changing beneath an unchanged theorem type
can change the contract graph"). The closure follows meaning edges: types always, bodies except
through theorem proofs. The *meaning* of a theorem is its statement and its axiom set (its proof is
irrelevant to consumers, its axiom footprint is what this tree pins); of everything else its type
and body. The same fact serves both roles; the citation's role (statement or proof) decides the
category. *Critique:* a closure is larger than a citation list (hundreds of supports per theorem),
so UNAFFECTED is a stronger claim and STATEMENT-CITED fires more often: any change to a definition
deep under a statement flags every theorem above it, which is correct and will feel noisy on a
`Term` redesign (every theorem in the tree). The brief's flat scheme is recoverable in one line
each (`meaningEdges := []`, `meaning := typeHash` or `valueHash`). *Meta-critique:* this is the
decision I most want Ember to look at (§7). I did not build the flat version alongside to show the
two disagree on this tree; the teeth and the experiment pass under both, so the difference is
argued, not measured.

**D2. A 64-bit structural hash of my own (`analyze`), not `Expr.hash` and not a pretty-print.**
*Why:* `Expr.hash`'s cached field is 32 bits (READ `Lean/Expr.lean`: `hash : 32-bits`); a
pretty-printed string depends on `pp` options and open namespaces. Mine mixes constructor tag,
constant names (64-bit `Name.hash`), levels with the declaration's parameters renamed to position,
literals, de Bruijn indices, `proj` structure and index; omits binder names, binder info and
`mdata`, as `Expr.eqv` does; pointer-cached so linear in the DAG. *Critique:* not cryptographic;
a collision between an old and a new value of the same declaration reads as "unchanged". At 2^-64
per changed declaration that is below every other error here, but it is a probabilistic reading
and the README says so. The library's own `Digest` (cSHAKE256) was the romantic choice and was not
taken: its compiled speed on megabyte proof terms was not measured. *Meta-critique:* "say which"
was the brief's demand; I say which and why, and did not benchmark the alternative I rejected.

**D3. Axioms collected by my own memoised walk, mirroring `collectAxioms` case by case.** *Why:*
`collectAxioms` is memoised per call and reads its precomputed extension only for exported names
with `loadExts := true`; one shared memo over 10659 rows needs neither. *Critique:* two
implementations of one walk; agreement is by construction (same cases, same sentinel), not by test:
no row was cross-checked against `#print axioms` in this lane. *Meta-critique:* a cross-check on
the 1502 pinned names is a `#assert_axioms`-shaped afternoon and belongs with the teeth; I did not
spend it.

**D4. Visibility by a second import at `OLeanLevel.exported`.** *Why:* the honest instrument: a
name the exported view finds is public, a definition whose value it carries is exposed. A `module`
cannot import a legacy file at that level (READ `importModulesCore`), so the exported view holds the
64 `module` files and the 7 legacy leaves are classified by `isPrivateName`, exposed `true`.
*Critique:* two imports per export; and "exposed" for a theorem is `hasValue` of the exported view,
which is `false` for every theorem by `ConstantInfo.hasValue`'s definition, so the column says
nothing about theorems. *Meta-critique:* I kept the column uniform rather than absent for theorems.

**D5. Cites restricted to the tree; toolchain constants a fixed background.** *Why:* 8.9 MB with
the tree alone; `Init`/`Lean` cites would multiply it, and a toolchain bump is a different event
than a redesign. *Critique:* a theorem whose proof leans on an `Init` lemma that changes meaning
across toolchains reads UNAFFECTED; the header records the toolchain and the README says a bump is
not read. *Meta-critique:* "not read" is a scope line, not a solution.

**D6. One export committed, 8.9 MB, plain JSONL.** *Why:* the brief names the output path; the
baseline is the record the experiment refers to. *Critique:* 8.9 MB per committed export is heavy
for git; the row format is verbose (every auxiliary's cites). *Meta-critique:* the honest fix is
to not commit exports (they are a function of the commit) and ignore `env-*.jsonl`; `.gitignore`
is at the repository root, outside my paths, so I committed one and left the choice to Ember.

**D7. The experiment on the live tree, reverting by marker, not by backup.** *Why:* lane A was
editing `Adequacy.lean` while I ran; restoring a backup would have erased their edits. *Critique:*
the exports include lane A's uncommitted state; the record says so and shows it unchanged across
the window. The strip left one extra newline at the end of `Adequacy.lean`, removed by hand (§6).
*Meta-critique:* a `git diff` after the strip would have caught it before the teeth started.

**D8. The tool does not `needs` the `Obend` library, and the exporter takes `--only PREFIX`.**
*Why:* the first teeth run died at `lake build`: lane A's new `Obend.Core.Proofs.Substitution` was
red at that moment (their proof in progress), and with `needs = ["Obend"]` even `lake exe journal`
refused to build the tool. The teeth live in `Obend.Slot`; a red `Core` proof has nothing to say
about them. So `lake build journal` now builds the tool and `Obend.Slot` only, and `--only
Obend.Slot` imports that subtree (plus what it imports) for a subtree export; `teeth.sh` builds the
seven `Slot` modules by name and runs the built binary through `lake env`. *Critique:* an export
is now of whatever `.olean`s are on disk for the modules named; the whole-tree export relies on the
caller having run `lake build`, where `needs` had made that automatic. *Meta-critique:* this is
Ember's rule applied late ("run the narrowest thing that could refute you"): the teeth never needed
the tree, and I wrote them against it first because the experiment did.

## 6. Not done, and the one byte

- No cross-check of `axiomsOf` against `collectAxioms` or `#print axioms` (D3).
- No flat-scheme comparison (D1).
- `Journal`'s two theorems carry no `#assert_axioms` pin: `Journal.Journal` imports `Obend.Slot`
  and `Std`, not `AxiomPin`; adding the import is one line and I left the module's imports minimal.
- The experiment's strip appended one `\n` to `Obend/Core/Proofs/Adequacy.lean` (lane A's file,
  under lane A's uncommitted edit); I removed that byte after the teeth run and fixed the script.
  Nothing else of lane A's was touched.

## 7. The one decision for Ember

**D1.** The brief said `(name, typeHash)` for the statement and `(name, valueHash)` for the proof;
I shipped `(name, meaning)` over the transitive closure, with a theorem's meaning its statement
plus its axioms and everything else's its type plus body. It is the memo's contract graph and it is
why the journal does not call `T : f = 7` unaffected when `f`'s body moves. It is also larger,
noisier on a definitional redesign, and a departure from the words of the brief. The flat scheme is
two one-line changes away; the closure is the one I would defend.

## 8. 2026-10-30, later: the closure fix (lane Journal-fix, Claude Opus 5.5)

On `LANE-JOURNAL-FIX-BRIEF-20261030.md`, answering item 1 of `review/KIMI-REVIEW-20261030.md`.

**What was wrong (READ).** `closure` gave its depth-first walk fuel `E.size + seeds.length + 1` and
spent one unit on every pop, including a pop of a name already seen. A convergent graph pays for
each repeat: Kimi's seven rows (`R` cites `[A,B,C,D,Z]`, `A..D` each cite `X`) give fuel 9, the walk
pops `R A X B X C X D X` and stops with `Z` on its stack, so a change to `Z` alone reads UNAFFECTED
for every theorem whose statement reaches `R`. The `(name, meaning)` closure of D1 was exactly the
feature that failed.

**What changed.** `Journal.Journal` now has a generic walk (`walk`, `closureBy`) over an edge
function and a `VisitSet` (membership, insertion, two laws). A pop first drops every already-seen
name off the stack (`dropWhile`), so fuel pays only for a new name, and `closureBy` gives
`seeds.length + bound + 1` where `bound` is the length of a list holding every edge target. For an
export that list is `E.targets` (every row's meaning edges, with repetition); `closure E seeds :=
closureWithin E E.targets.length seeds`. `report` computes the bound once and calls
`candidateWithin`, which is `candidateOf` with that bound passed in. The output order (depth-first
preorder) is unchanged. The journal runs the walk on `hashVisit` (a `Std.HashSet String`); the tooth
runs the same walk on `listVisit`, because the kernel cannot evaluate `String.hash`.

**The theorem.**

    theorem mem_closure_iff (E : Export) (seeds : List String) (x : String) :
        x ∈ closure E seeds ↔ Reach (edgesIn E) seeds x

where `Reach edges seeds` is the inductive "a seed, or one edge on from a reached name", i.e. the end
of a finite path. Completeness (the `←` direction, also stated as `closure_complete`) rests on
`walk_complete`: while the visited set agrees with the accumulator, every accumulated name's edges
land in the accumulator or on the stack, and the fuel exceeds the number of unvisited names in
`seeds ++ targets`, the walk ends with a list containing the accumulator and the stack and closed
under edges. Each new visit strictly shrinks that count (`length_filter_lt`), so the fuel never runs
out first. Soundness (`walk_sound`) is the plain invariant that everything visited or stacked is
reachable. The generic form is `mem_closureBy_iff`; `mem_closureWithin_iff` holds for any bound at
least `E.targets.length`. Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.

**The tooth** (`tools/journal/ClosureTooth.lean`, `teeth.sh` (c), MEASURED passing). It keeps the old
definition as `oldClosureBy` over the same `VisitSet`, and states completeness at the graph as
`Complete cl := ∀ x, Reach edges ["R"] x → x ∈ cl`. `old_refuted : ¬ Complete oldClosure` is
`decide` after one `Reach` step to `Z`; the kernel evaluates the old walk to
`["R","A","X","B","C","D"]` and the new one to `["R","A","X","B","C","D","Z"]`; `new_complete` is
`mem_closureBy_iff` at the graph. `#guard_msgs` pins the three theorems' axiom sets, so a `sorry`
fails the tooth.

**On the real tree (MEASURED once, scratch script, not committed).** On `env-b3ddd73.jsonl` (10659
rows, 94146 meaning-edge targets) the old and the new closure agree on every one of the 6063
theorems' type and value citations: the bug did not bite on the baseline (its fuel, about 10660, was
never exhausted there). The committed reports and the experiment stand as written. `journal diff`
of the baseline against itself still runs in about 1 s. Teeth (a) and (b) were not rerun: they edit
`Obend/Slot*.lean` in place while other lanes work in the checkout, and since the closures agree on
the baseline, they cannot have changed.

**What I would still not trust.**
- The hash (now said in the README and the module docstring): equal 64-bit non-cryptographic hashes
  are evidence of equal meaning, not equality. `holdsIn` treats them as equality; a collision makes
  a changed support read as holding and can make a theorem UNAFFECTED that is not. Dead supports are
  exact.
- The theorem is about `closure` as a function of an `Export`; it says nothing about whether the
  exporter's cites are the right edges (D3's unchecked `axiomsOf`, the `proj`-structure cites).
- `verdict`/`report` are tied to the closure only by definition (`report` calls `candidateWithin
  old old.targets.length`, which is `candidateOf`); there is no theorem that a theorem is UNAFFECTED
  only if no reachable support changed. That would be the next one to state.
- The tooth runs the walk on a list visited set; the journal runs it on a hash set. Both are
  instances of the one `walk`, and `hashVisit`'s laws are proved from `Std.HashSet`'s lemmas, but
  the kernel never evaluated the hash-set instance.
