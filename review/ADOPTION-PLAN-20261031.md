# Adoption plan: minidregg, nanodregg and delvetalk consuming `obend`

Written 2026-10-31 by Claude (Opus) for the brief `review/ADOPTION-BRIEF-20261031.md`. This was a
read-only study. In the three trees nothing was edited, built, checked out, stashed or fetched. Their
sources were read with `cat`, `git show <rev>:<path>` and `git log`. For nanodregg, the `.lean` files at
`2dcc9ea` were exported with `git archive` into a scratch directory. obend was read at `0f8ec22`.

Each claim is tagged. **READ** means a file or a `git` record was opened. **MEASURED** means a script
was run over the sources here and its output was read; the scripts are name censuses, not builds.
**INFERRED** means it is my reasoning. Nothing in this document was built or run under Lean.

## 0. Verdict

- **nanodregg is the first real adoption, starting with `Obend.Slot`.** Its five slot and protocol
  files are obend's, word for word, modulo namespace and the 4.35 proof fixes (MEASURED, §3.2).
  Five consumer files would change. Before it can start, three things have to happen. Ember has to
  amend GATES-1 (no package dependencies) and the `gates/tree.py` and `gates/closure.py` grammars.
  `Obend.Slot` has to stop importing `Lean`. And nano has to make the 4.30 → 4.35 bump with
  `warningAsError` on.
- **The first green `require obend` build should be delvetalk's leaves**, as a pipe-cleaner. It needs
  no decision from Ember. Seven of its leaf files are byte-identical to Mini at its fork point: cSHAKE Spec/Fast/Core,
  HashBytes, Sha256, AxiomPin and AssertCompiled. An eighth, AssertAxioms, differs by 2 lines
  (MEASURED, §4.2). Its toolchain gap is the smallest (4.34.1 → 4.35). Two of its leaves break at 4.35
  anyway: `AssertAxioms` and `AssertCompiled` name `Lean.ofReduceBool`, which is gone at 4.35. obend's
  copies of both are already the fixed ones.
- **delvetalk's core is not a swap.** Its edition is a semantic fork: hosted text primitives, a new
  `unary` Term constructor, three-place `primitiveTypes`, and native data (READ, §4.3). Adopting
  `Obend.Core` drops those features unless obend's Core4 gains a primitive extension point. That is a
  design decision for Ember, not a migration step.
- **nanodregg's laws are not a swap either.** `Obend.Law` re-derives nano's law library over Core4. It
  is not a port: labels instead of bytes, no packages, and `Evaluates` instead of nano's `BigStep`
  (READ, REPORT-LAW). Nano's deployed laws are terms of nano's own `Lang`, and their ids commit to
  the expanded terms. SHIP §3's line that nano "deletes … the Std law generators it ports" does not
  hold today.
- **minidregg should go last, or not at all, and that is for Ember to decide.** The port is
  faithful: nothing that obend took from Mini has changed in Mini since the copy (READ). But
  `require obend` forces the whole tree to 4.35: 1646 files, 605K lines, and Mathlib pinned at the
  4.30 rev `1c2b90b1`. That is a Mathlib 4.30 → 4.35 migration across 140 files that import Mathlib,
  plus every 4.35 breakage class over 605K lines. The demo shuts down on 11 November 2026 (READ, Mini
  `README.md:16`).

## 1. What holds for every tree

### 1.1 The require

obend is the `lean/` subdirectory of `github.com/emberian/obend`, and its package is named `obend`
(READ, `lean/lakefile.toml`). Lake's git dependency carries `subDir`
(READ, `Lake/Config/Dependency.lean:74` at v4.35.0), so a tree writes:

```toml
[[require]]
name = "obend"
git = "https://github.com/emberian/obend"
rev = "<adoption sha>"
subDir = "lean"
```

obend has no packages of its own (READ, `lake-manifest.json`), so the only coupling is the toolchain.
A consumer builds only the `Obend.*` modules it imports (INFERRED, Lake builds the import closure).
obend's `Census` and `Journal` are not part of that closure.

### 1.2 Toolchains and what the 4.35 bump costs

| tree | toolchain | lines of Lean | deprecated `if_pos`… uses | names removed at 4.35 | other |
|---|---|---|---|---|---|
| obend | v4.35.0 | — | (left as warnings) | fixed | |
| minidregg | v4.30.0 + Mathlib `1c2b90b1` | 604,896 in 1646 files | 1788 in 289 files | `ofReduceBool`… in 6 files | 65 files use `native_decide`; 2800 `simpa` |
| nanodregg | v4.30.0, no packages | 179,784 at `2dcc9ea` | 957 in 133 files | none | `warningAsError := true` |
| delvetalk | v4.34.1, no packages | 18,139 in 69 files | 27 in 6 files | 3 files (its Assert/AxiomPin leaves) | |

The counts are MEASURED by `grep` over `git ls-files`; nano's are taken at `2dcc9ea`.

`REPORT-LEAN435-20261031.md` names three classes of breakage. Here is where each class began, READ
from the toolchain sources in `~/.elan`:

1. **The new `do` elaborator.** The default flipped at 4.33 (per the report).
2. **`backward.isDefEq.respectTransparency` defaults to `true`, and `if_pos` and its relatives are
   deprecated.** Both are already true at **v4.34.1** (`Lean/Meta/ExprDefEq.lean:47`,
   `Init/Core.lean:1184`).
3. **`Lean.ofReduceBool` and its relatives exist at 4.34.1 and are gone at 4.35.0** (grep of
   `Init/`). The simp-set changes are not localized to a version here.

What that means for each tree (INFERRED):
- **delvetalk** has already paid classes 1 and 2. Its 4.35 cost is the removed names, which live
  only in leaves that adoption deletes, plus whatever the simp changes do to its 41 theorems outside
  `spec/bend`.
- **nanodregg and minidregg** pay all three classes. obend paid them across 211 files with about 30
  edits (the report's table). Scaling by theorem density, nano is on the order of 10× obend's edit
  count and Mini 40× or more, before Mathlib.
- **nano's `warningAsError` makes its 957 deprecated uses build errors.** obend left its own as
  warnings. nano's `leanOptions` apply to nano's modules only, so obend's warnings do not reach nano
  (INFERRED, Lake applies `leanOptions` per package).

### 1.3 Visibility of module files

obend is all `module` files (READ, `lean/README.md`).
- **Definitional modules** are `@[expose] public section` throughout. That covers every module
  under `Spec`, `Law`, `Slot`, `Elab` and Core's definitional modules (READ, the file heads and
  `MODGRAPH-20261031.md`).
- **Proof modules** make a theorem public only if another obend module cites it.

A tree's non-`module` file that imports obend sees only public declarations (INFERRED, from the
module system; the census comment in `Obend/AssertAxioms.lean:13` says a non-exposed theorem
"arrives as an axiom"). So:

- **Mini cites 15 theorems that are private in obend** (MEASURED, a name census of the theorems in
  the moved files, cited by Mini files outside the moved set and non-public in obend):

  | theorem | obend module | Mini files that cite it |
  |---|---|---|
  | `addrValid_of_lexical` | Forcing/Extract | ObjectiveReferenceLift, ObjectiveResumeContract |
  | `yieldedPlan_heapForces` | Forcing/Extract | ObjectiveResumeContract |
  | `chain_checkpoint` | Forcing/Converse | ObjectiveResumeContract |
  | `node_malformed_of_chain` | Forcing/BackFail | ObjectiveReferenceLift |
  | `collect_heap_le`, `collect_resume_segment` | Proofs/Collect | ObjectiveResumeContract |
  | `deepEvaluates_unique` | Proofs/DataSoundness | ObjectiveBendAdmissionSemantics, Host/ObjectiveInvocationQuote |
  | `rawRun_add` | Proofs/Completeness | Assurance/ObjectiveZkStepTariff |
  | `rawRun_boolean_sound`, `rawRun_label_sound`, `rawRun_natural_sound` | Proofs/Adequacy | Assurance/ObjectiveBendProofSource (and ZkStepTariff) |
  | `runBounded_yields_outside`, `typed_checkpoint` | Proofs/Force | ObjectiveResumeContract |
  | `state_roundTrip` | Proofs/CheckpointRoundTrip | ObjectiveActivityWire, ObjectiveResumeContract |
  | `typed_runBounded_no_refusal` | Proofs/Preservation | ObjectiveBendAdmissionSemantics |

  The census also matched `here` and `foldlM_invariant`. Both are probably Mini's own names that
  collide (INFERRED). The fix is in obend: make these theorems `public`. No statement changes.
- **nanodregg cites no theorem that is private in obend** (MEASURED, the same census; the one hit,
  `locality`, is a Kernel name that collides).
- **The queued "expose-all tightening" (`DECISIONS-20261031.md`, plan table) will move this surface
  again.** A tree should pin a rev from after that change, not before it.

### 1.4 Other obend-side facts every tree meets

- **The per-theorem `#assert_axioms` is gone.** `Obend/AxiomPin.lean` was deleted at `393eb2b`, and
  only `#assert_axioms_tree` and `#assert_compiled` remain (READ). Mini uses `#assert_axioms` or
  `#assert_compiled` in 486 files and delvetalk in 10 (MEASURED). **Each tree keeps its own
  `AxiomPin`**; there is no counterpart.
- **`Obend.Slot` imports `Lean`.** It has `public import Obend.Tactic.Tooth` for the `#tooth` line
  beside `slot_repair` (`Obend/Slot.lean:25,160`), and `Tactic/Tooth` does `public import Lean`
  (READ). This matters for nano (§3.4).
- **cSHAKE and `@[csimp]`.** Lean's csimp table is keyed by the replaced constant, and a later entry
  overwrites an earlier one (`map.insert`). The rewrite applies only "in functions defined after the
  theorem" (READ, `Lean/Compiler/CSimpAttr.lean` at v4.35.0). So a tree's own `@[csimp]` on
  `Obend.Digest.Cshake256.cshake256Bytes` reattaches its native kernel for the tree's own code. It
  does not reach code obend compiled. Today the only such code is `Obend.Core.Digest.deployed` and
  `digest`, which Mini never calls (READ, grep). SHIP §3's one-line `@[csimp]` is therefore correct
  for Mini's hot paths (Kernel, Pred, Kmac) as things stand. It stops being correct once obend
  compiles a hashing function that a tree calls (INFERRED). obend's `Seam` already carries its own
  `@[csimp]`, so the tree's theorem needs a different name.
- **`lean/README.md` still says "Lean `v4.30.0`"** (READ). This is stale, and a consumer reads that
  file first.

### 1.5 obend-side preparation (before any tree moves)

- **P1.** Tag an adoption rev from after ProofEng, Extends and the expose-all tightening. Extends is
  in flight on `Spec` files. The tightening is queued.
- **P2.** Make the 15 theorems in §1.3 `public`.
- **P3.** Make `Obend.Slot` (and `Slot.Protocol` and the slot proof modules) import only `Init`:
  move the `#tooth` line into a sibling teeth module.
- **P4.** Fix the README toolchain line.
- **P5.** For Mini only, and only if Mini goes ahead: decide whether obend's `Digest` instance stays
  fixed. A host-supplied kernel would need `deployed` to go through an instance the host can replace
  (INFERRED).

## 2. minidregg

### 2.1 State (READ)

- **HEAD.** `3d4805768` (2026-10-31), on `main`. 15 untracked files, none of them in the moved set.
- **Nothing obend took has changed since the copy.** Two commits since `092027a24` (the Spec copy,
  2026-10-29). Neither touches `Theory/ObjectiveBend*`, `Compiler/ObjectiveBend*`,
  `Host/ObjectiveBend*`, `Compiler/Sha256`, `Theory/{HashBytes,Sp800185*,Assert*,AxiomPin}`, `Pred/`
  or `Kernel/Objective*`. The last change to `Theory/ObjectiveBend*` is `aaf73ce1a` (2026-10-27),
  before the Core copy `57d28e7` (2026-10-29 12:53 -0400).
- **No module diverged since the copy.**

### 2.2 Module map

The map comes from a declaration-name census (MEASURED). Each Mini file is listed against the obend
file that holds most of its names, with the count matched over the count declared. Namespaces map
`Minidregg.Theory.ObjectiveBend<X>` → `Obend.Core.<Y>` and
`Minidregg.Compiler.ObjectiveBend<X>` → `Obend.Spec.<Y>` (READ).

**Core.** `Theory/ObjectiveBend*`: 46 files and 26,781 lines, all deleted.

| Mini | obend |
|---|---|
| OpenRecursion | `Obend.Core.Term` (46/46); **`Term` gained `hole (n) (σ)`** (READ, diff) |
| Types | `Obend.Core.Ty` (42/42; the `Ty` inductive is unchanged; +148 lines of agreement) |
| Typing | **split** into `Obend.Core.Check` (38), `Obend.Core.Packet` (27, the typed-core wire and receipt) and `Obend.Core.Proofs.CheckTeeth` (96, the `decide` teeth), at `0d2a64b`. `check` keeps its signature `(source) (context) (fuel)` (READ `Check.lean:886`) |
| DemandMachine, DemandMachineFast, DemandData, DemandCapacity, DemandCollect, DemandInvariant, DemandTyping, Checkpoint, Extensions, Interaction, Digest | `Obend.Core.{Machine, MachineFast, Data, Capacity, Collect, Invariant, MachineTyping, Checkpoint, Extensions, Interaction, Digest}` (all names matched) |
| DemandAdequacy, DemandCompleteness, DemandCollectProofs, DemandSettleProofs, DemandForceProofs, DemandDataSoundness, DemandDataBudget, DemandPreservation (+ `/Base`, `/Cases/*` ×6), Templates, StepCases, CheckpointRoundTrip, LedgerPoles, DigestChecks | `Obend.Core.Proofs.{Adequacy, Completeness, Collect, Settle, Force, DataSoundness, DataBudget (legacy leaf), Preservation (+ `.Base`, `.Cases.*`), Templates, StepCases, CheckpointRoundTrip, LedgerPoles, DigestChecks}` |
| DemandForcing{Agree, Back, BackFail, Chain, Converse, Demand, Extract, Nest, Pend, Run, Segment, Switch} | `Obend.Core.Proofs.Forcing.*`, the same twelve |
| teeth inside the above that evaluate `Array.map`/`String.toUTF8` | `Obend.Core.Teeth.*` (seven legacy leaves) |

**Digest and axioms.**

| Mini | obend |
|---|---|
| `Theory/Sp800185Cshake256Spec`, `Fast`; `Theory/HashBytes` | `Obend.Digest.Cshake256.Spec`, `.Fast`; `Obend.Digest.HashBytes` (namespace `Minidregg.Compiler.Sp800185Cshake256` → `Obend.Digest.Cshake256`) |
| `Theory/Sp800185Cshake256Native` | **stays in Mini.** It holds the `@[extern "mini_cshake256_32"]` kernel. Its `@[csimp]` retargets `Obend.Digest.Cshake256.cshake256Bytes` (§1.4); obend's `Seam` is the Lean-only twin |
| `Theory/Sp800185Cshake256Core` | becomes a Mini shim: `import Obend.Digest.Cshake256` + Native |
| `Theory/Sp800185Cshake256Conformance` | stays (the KATs of the Rust kernel); no counterpart |
| `Theory/AssertAxioms`, `AssertCompiled` | `Obend.AssertAxioms`, `Obend.AssertCompiled`. These are the 4.35 versions: `isCompilerTrust` reads the `_native` axioms, and the by-name `isCoreReduceAxiom` is removed |
| `Theory/AxiomPin` | **no counterpart** (deleted in obend at `393eb2b`); stays in Mini |

**Front end.** Compiler and Host files, 5,775 lines deleted.

| Mini | obend |
|---|---|
| Compiler/ObjectiveBendParse | `Obend.Spec.Parse` (101/101) |
| Compiler/ObjectiveBendElaborate | **split** into `Obend.Spec.Elaborate` (100), `Obend.Spec.Syntax` (27), `Obend.Spec.Types` (17) and `Obend.Spec.Annotated` (`retarget`, `depth`, …) |
| Compiler/ObjectiveBendC4, C4Vectors, Contract, SpecificationClosure, FrontEndAdequacy | `Obend.Spec.C4`, `Obend.Spec.Proofs.C4Vectors`, `Obend.Spec.Contract` + `Proofs.Contract`, `Obend.Spec.Proofs.SpecificationClosure`, `Obend.Spec.Proofs.FrontEndAdequacy` |
| Compiler/ObjectiveBendLaw | `Obend.Spec.Law`: syntax, parser and `denote` (moved there from `Kernel/ObjectLaw`). **`compile`, `packageLaw`, `LawRef.slot` and `compile_sound` (the `Pred` half) have no counterpart** (READ, `Obend/Spec/Law.lean:10`). They stay in Mini as a residual module over `Obend.Spec.Law.LawExpr` |
| Compiler/ObjectiveBendFrontEnd | `Obend.Spec.FrontEnd` (`lower`, `accept`). `Accepted.packetTerm` is now a theorem in the legacy leaf `Obend.Spec.Proofs.TermWire`, not a field. `r.accepted.packetTerm` still resolves by dot notation if the leaf is imported (READ `TermWire.lean:295`) |
| Compiler/ObjectiveBendTermWire, DataWire, FrontEndIdentity, Sha256 | `Obend.Spec.Proofs.TermWire` (legacy leaf), `Obend.Spec.DataWire`, `Obend.Spec.Identity`, `Obend.Spec.Sha256` |
| Host/ObjectiveBendFrontEnd, Preview | `Obend.Spec.Capture` (31/38), `Obend.Spec.Preview`; the CLI parts go to `Obend.Main` |

**Stays in Mini and imports obend.** These are consumers, not twins:
- Compiler/ObjectiveBend{CDiffGen, CombinedResult, EmitC, EmitCRun, GenericResult, LawCodec,
  NativePlanData, PlanAdapter, Publication, QuoteRequest, ResultAdapter, SourceArtifact} (3,103
  lines; Publication's `replay_inhabited` was never ported).
- Host/ObjectiveBendFrontEndMain.
- `Kernel/Objective*`: 32 files.
- `Kernel/ObjectLaw*`, `Pred/Core`, `Theory/Hyperdocument*`. obend's `Doc` is a new construction,
  not a port of these (MEASURED: name overlap ≤ 2).

### 2.3 Consumers whose imports or names change (MEASURED)

**Imports.** 56 files outside the moved set import a moved module, out of 109 files with such an
import. The importers outside the moved set:
- **Kernel (13):** ObjectiveActivity, ObjectiveActivityWire, ObjectiveBend{AdmissionSemantics,
  ArtifactSource, NativeAdmission, NativeInput, PreparedOutput}, ObjectiveReferenceLift,
  ObjectiveResumeContract, ObjectiveWorkAccount, ObjectLaw, ObjectRecord, ObjectStateType.
- **Compiler (14):** eleven of the twelve staying ObjectiveBend files (all but QuoteRequest),
  ObjectiveDemandStateEquality, ObjectiveDemandStorage, ObjectiveInvocationLayout.
- **Host (6):** Main, ObjectiveActivityJson, ObjectiveInvocationQuote, ObjectivePackageAuthor,
  SeatJson, ObjectiveBendFrontEndMain.
- **The rest:** Assurance/ObjectiveBendProofSource, Fixtures/NativeAcceptedFixtureProjection,
  Theory/ObjectiveTermEquality, `Theory.lean`, `Minidregg.lean`, `ObjectiveProofs.lean` (which
  becomes obend's build), 5 `tests/objective-bend-source/*.lean`, 3 `tests/objective-native/*.lean`,
  5 `examples/objective-bend-world/*.lean`, `world/automatafl/Run.lean`, 2 `scripts/*.lean` and
  `native/objective-emit/fastmachine/MachineRun.lean`.

**Qualified names.** 56 files outside the moved set spell a moved namespace in full, 206 times.
Most of these are `Minidregg.Theory.ObjectiveBendDemandMachine`, `…DemandData`, `…OpenRecursion`
and `…Typing`.

**Exhaustive matches on `Term`.** 11 files need a `hole` arm (MEASURED, a match listing
`prototype`): Assurance/ObjectiveZkRefinementAudit, Compiler/ObjectiveBend{CDiffGen, EmitC},
Compiler/ObjectiveDemand{Code, PackedCode, StateCodec, StateEquality, Storage},
Kernel/ObjectStateType, Kernel/ObjectiveActivityUpgrade and Theory/ObjectiveTermEquality.

**Import-boundary rows.** `scripts/check-import-boundary.sh` admits only listed libraries per row
(READ). Every row that imports obend needs an `Obend` column: Theory, Pred, Kernel, Compiler, Host
and Assurance.

### 2.4 Definitions renamed or restructured that Mini uses

- **`Term.hole`, a new constructor at position 1.** obend's checkpoint wire gives it the new tag 23
  (READ `Checkpoint.lean:60`). Hole-free checkpoints should encode byte-for-byte as before
  (INFERRED: the existing tags are unchanged). Mini's own codecs must refuse or encode a hole.
- **The `Typing` → `Check`/`Packet`/`CheckTeeth` split and the `Elaborate` →
  `Syntax`/`Types`/`Annotated`/`Elaborate` split.** A consumer's `open` lines and qualified names are
  spread across four namespaces.
- **Type agreement and equi-recursion.** Branch joins convert through `agree` (`281bdac..89bd283`),
  and `Invariant` changed by 266 lines. A Mini proof that reasoned about `check` by unfolding will
  see a different body (INFERRED; no name census can show this).
- **`checkWork` replaces `typeFuel`, in the front end's grant only** (READ, REPORT-SPEC "Deviation").
  Mini spells `typeFuel` in 20 `.lean` files. It is also on the wire: the Rust client
  (`native/resource-client/src/bend.rs`), four acceptance scripts, `check-preview.ts`,
  `docs/tutorial/run.ts`. Core's `check` still takes fuel, so Kernel code calling `check` is
  unaffected. Only a switch to `Obend.Spec.Preview`/`accept` changes the request key. The cohort
  limit becomes `checkWork 43237`.
- **The front-end identity rotates.** `Obend.Spec.Identity` fingerprints obend's sources, and Mini's
  published packages name the identity (READ `FrontEndIdentity.lean:57`). Every package published
  before the switch names a different front end (INFERRED). This is moot after 11-11 if the demo
  world is erased.
- **cSHAKE.** Mini's Native seam retargets obend's `cshake256Bytes` (§1.4).
- **AxiomPin.** Mini keeps its own (§1.4).
- **Visibility.** 15 theorems must become public in obend first (§1.3).

### 2.5 Toolchain

4.30.0 → 4.35.0. Mathlib's tag `v4.35.0` exists at `56a00585` (MEASURED, `git ls-remote`). The
whole tree has to cross: 1646 files, 140 that import Mathlib directly, Selvage and Assurance
included. This is by far the largest cost in the plan, and none of it buys an obend theorem
(INFERRED).

### 2.6 Order inside Mini

This applies only if Ember chooses to migrate.

1. Bump Mini to 4.35 and Mathlib `v4.35.0` with no obend involved, as its own lane on hbox under
   `swarm-build`. Gate: the umbrella and the census are green, with the statement census unchanged.
2. Add `require obend`. Swap the digest and axiom leaves first: Spec/Fast/HashBytes/Assert* deleted,
   Core shimmed, Native retargeted. **First green build:** `lake build Theory Pred` with
   `Sp800185Cshake256Conformance` passing. That proves the Rust kernel is still what compiled Mini
   code runs.
3. Delete `Theory/ObjectiveBend*` and repoint the Kernel and Compiler consumers. Gate: Kernel,
   Compiler and Host build, and the 15 publicized theorems are cited.
4. Delete the front-end Compiler/Host files and keep the `Pred` half of `ObjectiveBendLaw`. Gate:
   `tests/objective-bend-source` cohorts and the tutorial.
5. Retire the `ObjectiveProofs` library.

### 2.7 Theorems lost and gained

**Lost: none of the moved statements** (READ, the census of `REPORT-20261030` and
`REPORT-SPEC-20261030`). Every one of the 1417 Core theorem names and 53 of the 54 front-end
statements survive. The 54th, `replay_inhabited`, stays in Mini's Publication. What Mini loses is
the local `ObjectiveProofs` gate, and the per-theorem axiom pins on the moved files (obend's census
replaces them).

**Gained:**
- `check_msubst`, `check_mono` and fuel-free `checked_msubst`.
- The bidirectional checker, equi-recursive agreement and conditional checker completeness, with
  its obstructions.
- The hole extension.
- The rest of obend's theorems: Law (273), Slot (195), Doc (115), Run (85), Elab (87), all MEASURED
  by `theorem` count. Mini cites none of these today.

## 3. nanodregg

### 3.1 State (READ)

- **The local checkout is not the source.** It is detached at `80c622a` (2026-10-27 00:32), with 15
  modified files (Protocol/*, Web/*, docs). That is **82 commits behind `origin/main` `2dcc9ea`**
  (2026-10-27 14:25), which is the commit obend ported from.
- **No branch has moved `Lang/Contextual` or the law files past `2dcc9ea`.** `fable-obs-meter`
  touches `Lang/Wire` only, and `origin/drain/pretty` is a WIP `Lang/Pretty`. No module diverged
  since the copy.
- **The working tree is stale for this purpose.** `80c622a` differs from `2dcc9ea` in
  `Lang/Contextual`, `Lang/Std` and the law files: 10 files, +503/−570. A migration lane works from a
  fresh clone of `origin/main`, never this working tree.
- **The lakefile is `lakefile.lean`, not `lakefile.toml`.**

### 3.2 Module map (MEASURED)

The diff counts are differing non-blank lines after the namespace is substituted; module headers
and comments were stripped.

| nano @ 2dcc9ea | obend | diff |
|---|---|---|
| `Lang/Contextual/Protocol` (629) | `Obend.Slot.Protocol` | 21 lines: doc paths + the 4.35 `List.mem_cons_self` fix in the negotiation `Resp` proof |
| `Lang/Contextual/Slot` (274) | `Obend.Slot` | 11 lines: docs + one `#tooth slot_repair` |
| `Lang/Proofs/Contextual/Protocol` (815) | `Obend.Slot.Proofs.Protocol` | 26 lines |
| `Lang/Proofs/Contextual/Negotiation` (260) | `Obend.Slot.Proofs.Negotiation` | 21 lines (the 4.35 `cases`/`injection` fix) |
| `Lang/Proofs/Contextual/ProtocolTyping` (131) | `Obend.Slot.Proofs.ProtocolTyping` | 8 lines |
| `Lang/Contextual/LangInstance` + `Lang/Proofs/Contextual/LangInstance` | **restructured.** Nano's `structure CalculusData` (with `check : Ctx → Tm → Ty → Bool`) and `structure CalculusLaws` (unconditional `check_complete`, `msubst_lemma`, the strengthening laws) become obend's `class Calculus Tm` (with `Typed`, `msubst` and the rest, no `check`) plus `class Decides R Tm [Graded R]` (a graded `check`, `check_mono`, `Covered`, `Prepares`, and `check_complete` conditional on `Covered`) (READ `Slot/Calculus.lean`). Nano's instance becomes `instance : Calculus Lang.Term` and `instance : Decides Nat Lang.Term`, with `check` ignoring the grade, `Covered := True` and `Prepares := Eq`. The strengthening and msubst laws stay nano theorems; obend has no laws structure. The leaf has no deployed importer (READ, its header) |
| `Lang/{Law, Claim, Std, Std*}`, `Lang/Proofs/{Std*, Claim, Law*}` (≈ 40 files) | **no counterpart.** `Obend.Law` re-derives these over Core4 (`Std` 32/64 names shared, `Proofs.Std` 32/92, `Claim` 7/15). It is not a port of nano's `Lang`; its deviations are listed in REPORT-LAW. Kept |
| `Lang/HoleDecl`, `Subst`, `LiveHoles`, `StdHole*`, `Journey/Contextual*` | no counterpart; kept |

The slot statements are unchanged: no theorem of the five files is missing from obend (MEASURED,
0 absent). The namespaces map `Nanodregg.Lang.Contextual.Slot` → `Obend.Slot` (so
`Slot.interp` → `Obend.Slot.interp`, `Slot.Slot` → `Obend.Slot.Slot`) and
`Nanodregg.Lang.Contextual.Protocol` → `Obend.Slot.Protocol`.

### 3.3 Consumers that change their imports (MEASURED at 2dcc9ea)

- `Hosting/Resident/Run.lean`. This is the deployed `resident` executable. It has
  `import Lang.Contextual.Slot`, eleven `open Nanodregg.Lang.Contextual.Protocol in` lines, and
  `Lang.Contextual.Slot.interp`.
- `Hosting/Resident/Trace.lean`: `Protocol.fold`.
- `Hosting/Proofs/ResidentRun.lean`: `open`, `Prot.call`, `Slot.interp` and `Protocol.fold` in a
  `simp only`.
- `Hosting/Proofs/ResidentSlots.lean`: `open … Slot`, `slot_repair`.
- `Web/Sim/Resident.lean`: the testground, compiled to wasm.

Nothing imports `Lang.Law`, `Lang.Claim` or `Lang.Std` under a changed name, because those stay.

### 3.4 What blocks nano before any file moves

- **GATES-1** (`decisions/gates.md`, 2026-10-16): "`lakefile` requires nothing. … `import Lean`
  only inside `Census/`" (READ). `gates/tree.py` reads the lakefile "with a strict grammar and
  refuses any top-level form it does not know" (closure C0). `gates/closure.py` C2 refuses "an
  import that is neither a tree module nor Init/Std" (READ). Ember's ruling is needed. The narrowest
  amendment: one named package, obend at a pinned rev, admitted by C0 and C2, with its closure
  required to be `Init`-only.
- **`Obend.Slot` pulls in `Lean`** through `Obend.Tactic.Tooth` (§1.4). That breaks GATES-1's
  "`import Lean` only in Census". It also breaks the testground: `testground/build/build.sh` copies
  the tree's IR C from `$root/.lake/build/ir/` and classifies closure modules as tree or `L`
  (READ, lines 43–52). obend's C lives under `.lake/packages/obend/.lake/build/ir/`, and a `Lean`
  closure would bring the elaborator's C into the wasm (INFERRED). **P3 fixes the import. build.sh
  needs a third class for package modules.**
- **4.35 with `warningAsError`.** 957 deprecated uses in 133 files become errors (§1.2). Nano
  pays all three classes over 180K lines. This is a deployed system, so the gate is nano's own
  `standing.sh`: the sims, the rows, `kernel-sim`, `host-sim`, `ledger-sim` and `hosting-sim`. A
  full `lake build` is not that gate.

### 3.5 Order inside nano

1. On a fresh clone of `origin/main`, bump to 4.35 with no obend involved, and clear the
   deprecations. Gate: the bare `lake build` is green under `warningAsError` and `standing.sh` ends
   `ALL PASS`.
2. GATES amendment and grammar edits (after Ember's ruling). Add `require obend` at the post-P3
   rev.
3. **First green build:** `lake build Lang Hosting Web`, with the five Contextual files deleted and
   the five consumers repointed. Then the `resident` binary, `hosting-sim`, and testground's
   `build.sh` with the package class.
4. Restate LangInstance against `Calculus`/`Decides`. This is the point where nano gains
   `slotOf_usable` and `resolve_checks` for its own `Lang`.
5. Laws: no step until Ember decides whether nano's deployed term language should ever be Core4
   (§6).

### 3.6 Theorems lost and gained

**Lost:** none (the slot statements are verbatim). `CalculusLaws` as a record is lost; its fields
remain nano theorems.

**Gained:**
- `Obend.Slot.Calculus`: `slotOf_usable`, `resolve_checks` and `admit`, at nano's `Lang`.
- `Obend.Slot.World` and `Integrity` (CONTEXTUAL INTEGRITY ∧ REPAIR over every World, and the floor
  refuted), `Slot.Repair`'s compatibility condition, and `PolySlot`. All of these can be used by
  Hosting's resident proofs if nano wants them.
- The `#tooth` mutation teeth, if nano admits `Lean` in a proofs-only module.

## 4. delvetalk

### 4.1 State (READ)

- **HEAD.** `625da35e` (2026-10-09, "checkpoint"), on `main`. 16 modified files: conformance
  Python, protocol READMEs and scripts. No `.lean` file is modified.
- **Dormant for three weeks.**
- **The fork's origin.** `spec/bend/origin.json` names Mini `dcab86da8` (2026-10-08). Its scope
  says "historical source attribution only … the independently maintained local fork".
- **Toolchain.** 4.34.1, no packages. The libraries `Theory`, `Compiler` and `Pred` all have
  `srcDir = "spec/bend"`.

### 4.2 Module map (MEASURED: diff against Mini at `dcab86da8`, then the name census against obend)

| delvetalk `spec/bend/` | vs Mini@dcab86da | obend |
|---|---|---|
| Theory/Sp800185Cshake256{Spec, Fast, Core}, Theory/HashBytes | identical | `Obend.Digest.Cshake256.{Spec, Fast}`, `Obend.Digest.Cshake256`, `Obend.Digest.HashBytes` |
| Compiler/Sha256 | identical | `Obend.Spec.Sha256` (10/10). It imports `Lean` in obend |
| Theory/AssertAxioms, AssertCompiled | 2 lines / identical | `Obend.AssertAxioms`, `Obend.AssertCompiled`, the 4.35-fixed versions |
| Theory/AxiomPin | identical | **no counterpart** (gone at `393eb2b`); keep |
| Compiler/ObjectiveBend{C4, Contract, Law} | identical | `Obend.Spec.{C4, Contract, Law}`. Law keeps only syntax and denote; delvetalk's `compile`/`packageLaw` over `Pred` stay |
| Pred/Core, Pred/HashEqDigest | identical | **no counterpart** (obend has no `Pred`); keep |
| Theory/ObjectiveBendTypes | identical | `Obend.Core.Ty` |
| Theory/ObjectiveBendOpenRecursion | **53 lines differ**: `textConcat/Take/Drop/Span/Break` in `Primitive`, `UnaryPrimitive (natText, textLength, sha256Text)`, `Term.unary`, `textPrefixScan` over `String.Legacy.Iterator`, `Step.unary*`, `Yields.unary` | `Obend.Core.Term` has none of these, and has `hole`. **Diverged at `bf9a288a` (2026-10-09)** |
| Theory/ObjectiveBendTyping | **115 lines**: three-place `primitiveTypes`, `unaryTypes`, `PartialTyping.unary`, `recastCallable` | `Obend.Core.Check` (which has its own agreement and equi-recursion); diverged |
| Theory/ObjectiveBendDemand{Machine, MachineFast, Data} | **61, 83 and 264 lines**: text step costs, `forceHosted*`, native materialisation (`materializeNative`, `NativeExtraction`) | `Obend.Core.{Machine, MachineFast, Data}`; diverged |
| Theory/ObjectiveBend{FiniteData, FiniteDataTyping, NativeDataSimulation} | not upstream | no counterpart |
| Compiler/ObjectiveBend{Elaborate, Parse, TermWire, DataWire, FrontEnd} | **250, 56, 22, 16 and 5 lines**: text, nullary results, finite-sum defaults, re-exports | `Obend.Spec.*`; diverged |

### 4.3 Consumers that change imports (MEASURED)

**Through the leaves only.** `profiles/{MessagesCore, ProgramDigest, ResidentStore, RetainedRoots}`
use `Compiler.Sha256`.

**Through the core:**
- `spec/Delvetalk/{Core, FrontEnd, Generics, Package, PackageData, PackageDataAdmission, Reflection, Typed}`.
- `profiles/{WorldCore, SourceReflection}`.
- `conformance/NativeDataProbe`.

There are also the Python, C and JS cross-check engines (`scripts/crosscheck.py`), which agree with
the Lean edition on a shared fragment (READ `spec/README.md`).

### 4.4 Order inside delvetalk, and the first green `require obend` build

1. **Leaves, which need no decision.**
   - Bump to 4.35.
   - Add `require obend` (subDir `lean`).
   - Delete Theory/{Sp800185Cshake256Spec, Fast, Core, HashBytes, AssertAxioms, AssertCompiled} and
     Compiler/Sha256: seven files, 1,546 lines.
   - Repoint Pred/HashEqDigest, OpenRecursion's `sha256Text` and the four profiles. The namespaces
     change `Minidregg.Compiler.Sp800185Cshake256` → `Obend.Digest.Cshake256`,
     `Minidregg.Theory.HashBytes` → `Obend.Digest.HashBytes` and
     `Minidregg.Compiler.Sha256` → `Obend.Spec.Sha256`.
   - Keep AxiomPin.

   **The first green build:** `LEAN_NUM_THREADS=1 lake build` (the default target and every lib),
   then `python3 scripts/crosscheck.py --engines lean python` byte-equal to before. The axiom
   leaves would be red at 4.35 regardless (§1.2), so this step pays for itself.
2. **Core, only after Ember decides on text** (§6). If Core4 gains the text primitives, or a
   primitive parameter, delvetalk deletes OpenRecursion, Types, Typing, Machine, MachineFast and
   Data and keeps FiniteData and NativeData as extensions. If it does not, delvetalk keeps its core,
   and `require obend` stays at the leaves plus `Spec.{C4, Contract, Law}`. Those three are
   identical to Mini, but they are tied to delvetalk's diverged `Elaborate` through shared types
   (INFERRED), so they move with the core.

### 4.5 Theorems lost and gained

**Leaves:** nothing lost.

**Core swap without text:**
- **Lost:** every theorem about `unary`, the text primitives, `recastCallable`, `FiniteData` and
  `NativeDataSimulation`. Delvetalk's `spec/bend` has 426 theorems (MEASURED); the share about text
  and native data is not separated here.
- **Gained:** all of obend Core's metatheory (1,967 theorems, MEASURED by `theorem` count): adequacy,
  preservation, completeness, forcing, settle. delvetalk's fork never carried Mini's proof files.
  Its `spec/README.md` says "completeness of inspection is not established."

## 5. Across the trees

| step | tree | what | needs Ember? | gate |
|---|---|---|---|---|
| 0 | obend | P1–P4 (P5 only if Mini goes) | no | `lake build`, census unchanged |
| 1 | delvetalk | the leaves; **the first green `require obend`** | permission to edit delvetalk | default build + crosscheck byte-equal |
| 2 | nanodregg | 4.35 alone, on a fresh `origin/main` clone | no | `warningAsError` build + `standing.sh` |
| 3 | nanodregg | GATES-1 amendment, `require obend`, the five slot files deleted | **yes (GATES-1)** | `lake build Lang Hosting Web`, `resident`, `hosting-sim`, testground |
| 4 | nanodregg | LangInstance as `Calculus`/`Decides` | no | the new instance's theorems |
| 5 | delvetalk | core, or not | **yes (text in Core4)** | crosscheck, all four engines |
| 6 | minidregg | §2.6, or retire | **yes (migrate at all, before or after 11-11)** | umbrella + census + cohorts |

Step 1 comes before step 3, even though nano has the bigger payoff. Step 1 exercises every piece of
`require obend` machinery (subDir, the toolchain, module importers, the 4.35 axiom tooling) on 69
files, with nothing deployed behind it. Step 3 can then be judged on the gate questions alone.

## 6. Decisions for Ember

1. **nanodregg's GATES-1.** Admit one pinned package, obend, whose imported closure is `Init`-only?
   The alternative is that nano keeps its twin of the slot. That is a twin of 2,100 lines that are
   identical today and will drift.
2. **delvetalk's text.** Should Core4 gain hosted text (five binary primitives, three unary
   primitives, `Term.unary`)? Or a primitive extension point? Or should delvetalk keep a forked
   core and adopt only the leaves?
3. **minidregg.** Migrate at all? If so, before or after 11-11? The cost is a Mathlib and toolchain
   migration of a 605K-line tree; the deletion is about 34K lines of twin.
4. **nanodregg's laws.** Should nano's deployed term language ever become Core4? If not, `SHIP.md`
   §3 should stop saying nano deletes its Std generators. Note that `Obend.Law` has no bytes and no
   packages.
5. **`SHIP.md` §3 on cSHAKE.** The one-line `@[csimp]` is right for Mini's own code and wrong for
   anything obend compiles. Should `Digest.deployed` go through a replaceable instance (P5)?
