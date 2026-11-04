# Expert read: Lean proof engineering (2026-11-03)

Slug `lean-proof-engineering`. The persona: maintains a large Lean 4 library, reviews Mathlib PRs,
has been through a module-system migration. Reads statements, not names; treats `decide +kernel` on
a fixture as a test; treats `native_decide`/`bv_decide` as compiled trust; counts what `@[expose]`
costs at rebuild; asks of every "census" and "tooth" whether it can fail.

Tags: **READ** (file opened, `path:line` as of the working tree on 2026-11-03), **INFERRED**
(deduced from READ facts), **PROPOSED**. Every number has its command. I edited nothing but this
file and ran no build. Paths below are relative to `/Users/ember/dev/obend/lean/` unless they start
with `review/` or are a root document.

Read first: `review/FABLE-COUNCIL-20261101.md` §1–§2. I extend it; where the working tree has moved
since (it has: 480 modules, 234K lines, `find Obend -name '*.lean' | xargs wc -l`), I say so.

---

## 0. Verdict in one paragraph

**INFERRED.** The *mechanism* (`#tooth`, `#assert_axioms_tree`, `#assert_compiled`, the two tiers)
is better than most Lean projects have, and the median theorem in the tree is real: a uniform
sample of thirty gives 21 universally quantified statements with content. The failure is at the
*headline*: 66 of the 68 `golden_*`/`*_verified` theorems are closed instances; the 32 `X.accepted
= true` conjuncts in `Obend/Apps` are `true = true` by construction; the "silicon kernel" that is
lowered is a type-code comparator with fixture-fitted special cases on the host side; 176 bare
identifiers cited in the root documents name no declaration, and the documents census that is
supposed to catch that only looks at `Obend.`-prefixed tokens, so it passes. The gate's two real
holes are (a) nothing distinguishes a fixture from a theorem anywhere the numbers are reported, and
(b) tier 2 (census, teeth, Apps) is manual: 87 sources are newer than the last `Census.olean`, four
of eight `Apps` modules have never been built in this tree, and 30 test files with 308 theorems and
157 `#tooth` commands belong to no build target. The rebuild cascade is the same disease from the
other side: fixture proofs by `decide +kernel` across modules force `@[expose] public section` on
39 of 43 Hardware files, and a one-line exposed edit in `Core/Term.lean` now reaches 333 of 439
tier-1 modules.

---

## 1. Suspicions, evidence, verdicts (ranked by how it would read to a Lean maintainer)

| # | Suspicion | What would clear it | Found | Verdict |
|---|---|---|---|---|
| 1 | "0 sorryAx, N theorems" headlines count fixtures as theorems | A census line that separates closed statements from universal ones | No such line exists; `#assert_axioms_tree` counts constants only (`Obend/AssertAxioms.lean:58-80`) | **Confirmed** (§3, §4) |
| 2 | `X.accepted = true` is vacuous | `accepted` defined from a checker result | `#import_obend` emits `@[expose] public def Ns.accepted : Bool := true` and `theorem Ns.accepted_eq : Ns.accepted = true := rfl` (`Obend/Apps/ObendRisc.lean:621-624`; same text in the other seven Apps; `Obend/Elab/Workbook.lean:1713-1719`) | **Confirmed**: the information is "the macro did not throw" |
| 3 | The "Lean kernel checker" lowered to silicon is not a kernel | A `KExpr`-consuming `LExpr`/`Book` | `kernelCheckLExpr` is a three-`Nat` comparator (`Obend/Lower/LeanKernel.lean:1058-1073`); `encodeDeclCheckLExpr` runs `kernelCheckDecl` on the host to produce `inferredTag` (`:1080-1092`); the newer `inferTypeLExpr` is a 4-word type-code table with host-side fixture patches (§5.2) | **Confirmed**, and worse than the council found |
| 4 | Root-document theorem names dangle and the docs census does not see them | `#docs_census` resolving bare names | It resolves only backticked tokens starting `Obend.` (`Obend/Tactic/DocsCensus.lean:633-650,739-752`); 113 bare theorem-shaped names cited in its seven governed docs are absent from the tree (§6) | **Confirmed** |
| 5 | Tier 2 is not run | Fresh `Census.olean`, all `Apps` built, tests in a target | `Census.olean` 2026-11-02 16:18, 87 sources newer; no `.olean` for `Apps/{FocHil,ObendRisc,SdrFt8,ZkNtt}`; `tests/{metasystem,silicon_elab,rehydration}` in no lakefile target, 0 oleans | **Confirmed** |
| 6 | `#tooth` on fixture theorems proves only that the test is sensitive | Teeth aimed at universal statements | Tier-2 `Teeth/Hardware` aims at universal statements (`SiliconTeeth.lean:257-371`, READ 15 of 58); the *new* tier-1 teeth in `Analysis`/`Hardware` (42, uncommitted) also aim at universal statements | **Cleared** for the teeth that exist; the gap is coverage, and a fixture checker now wears the name (§2.1) |
| 7 | Rebuild cascade from exposure | Measured one-edit cost at today's size | Last measured at 283 jobs (2026-11-01); Term's closure is now 333 tier-1 modules / 182K lines; 218 files use blanket `@[expose] public section` | **Confirmed** as unmeasured growth (§7) |
| 8 | `native_decide` unpinned | One `#assert_compiled` per oracle | 27 proof-position `native_decide`, 27 `#assert_compiled` (`grep -rnE '(:=\|by\|<;>\|·)\s*native_decide' Obend \| grep -v Assert \| wc -l`; `grep -rn '^#assert_compiled' Obend tests \| wc -l`) | **Cleared**; but 23 `bv_decide` (15 in `Lower/ExprCAM.lean`) are the same trust and are not called out anywhere in the docs |
| 9 | Hidden `sorry` | — | 23 occurrences of the word, all in docstrings (`grep -rnw sorry Obend`) | **Cleared** |

---

## 2. The mechanism, file by file (READ)

### 2.1 `Obend/Tactic/Tooth.lean` (294 lines)

Lines 1–226 are the real thing: `#tooth T by mutation f := v` walks the dependency graph of the
*stored* proof of `T` by compiled constant collection (`:22-45`), refuses hidden bodies, cyclic
replacement, unsafe/partial defs, inductives in the affected set (`:140-156`), replays the renamed
original closure as a control (`:196-203`), then replays under the mutation through `addDeclCore`
with `doCheck := true` (`:181-186`) and credits a tooth only on a kernel type-mismatch class of
exception (`:160-166`). It errors when the stored proof still succeeds (`:224`). That is a correct
mutation test and it is the best piece of tooling in the repository.

Lines 228–294 (added in `23a7651`, 2026-11-02, uncommitted diff is empty) bolt on a "Dual-Pole
Tooth Obligation Checker": `verifyDualPoleTooth spec := spec.eval spec.posFixture && spec.negFixtures.all
(fun x => !spec.eval x)` and `verifyDualPoleTooth_sound`, whose conclusion is the definition
unfolded. It is used only in `tests/metasystem/IsarJudgeAndWorkspaceTest.lean` (17 uses; `grep -rn
verifyDualPoleTooth Obend tests`), which nothing builds. **INFERRED**: a fixture checker was given
the name of the mutation tester so that "tooth" counts could rise. It should leave this file.

### 2.2 `Obend/AssertAxioms.lean`, `Obend/AssertCompiled.lean`

`#assert_axioms_tree` (`AssertAxioms.lean:58-80`) iterates `env.constants.map₁`, filters to package
modules, refuses any axiom not `_native`-suffixed and any constant whose axiom closure leaves
{`propext`, `Classical.choice`, `Quot.sound`} except via `_native` (counted) or a `computed_fields`
`_override` with `lcProof` (counted). `#assert_compiled` (`AssertCompiled.lean:36-88`) re-runs the
oracle's closed `Bool` claim through `evalExpr` and refuses by-name acceptance. Both are sound for
what they claim. What they do not claim: anything about the *shape* of a theorem. A closed
`decide +kernel` fixture is as kernel-clean as `lower_sound`; the census cannot tell them apart,
and the documents quote its verdict line as if it could (`METATHEORY.md:4-7`).

### 2.3 `Obend/Census.lean`

Not a `module` (so it sees private parts and the legacy leaves; `:10-15`); imports every file; a
`run_cmd` walks `Obend/` and refuses an unimported file or a module in neither tier's globs
(`:471-520`, parsing `lakefile.toml` by string splitting); then `#assert_axioms_tree` and
`#docs_census`. It is tier 2 (`lakefile.toml:33-35`), built by hand (`tools/hooks/pre-push:2-5`).
Current artefact: `.lake/build/lib/lean/Obend/Census.olean` dated Nov 2 16:18; `find Obend -name
'*.lean' -newer .lake/build/lib/lean/Obend/Census.olean | wc -l` = 87. So the census verdict
quoted anywhere today is about a tree 87 files ago.

### 2.4 `Obend/Tactic/DocsCensus.lean` (841 lines)

Two commands. `#check_docs_census` (`:795-803`) checks `Obend/**/*.lean` paths, `review/*.md`
paths and `Obend.<Sub>` roots in eleven docs; it is **not invoked** by `Census.lean`. `#docs_census`
(`:810-815`) builds a `Slot` per governed doc whose supports are those paths plus "constants", where
a constant is a backticked token that **starts with `Obend.`** (`metaTokenCharsToObendConst?`,
`:633-646`) and holds if `env.contains n || moduleNames.contains n || subOk` (`:748`). Bare names
(`lower_sound`, `evalInterval_correct`, `simplex_safety`) are never extracted. Of the 159 `Obend.*`
tokens in the seven governed docs, my approximation resolves all (§6 command); of the bare
theorem-shaped names in the same seven docs, 113 resolve to nothing. The census passes and the
docs dangle. Also: the extraction is ~500 lines of hand-rolled `List Char` tokenisers duplicated
once as `def` and once as `meta def` (`:56-470` and `:480-700`) "for kernel reduction"
(`:131`) — there is a `theorem … := rfl` at `:825` about the tokenizer, which is a test of the
tokenizer, not governance of anything.

### 2.5 `lakefile.toml`, `tools/hooks/pre-push`, `tools/measure.sh`

Tier 1 = `Obend` lib with 30 explicit globs (`lakefile.toml:11-17`); tier 2 = `Teeth` lib =
`Obend.Teeth.+`, `Obend.Apps.*`, `Obend.Census` (`:33-35`). The pre-push hook builds tier 1 with
`LEAN_NUM_THREADS=2` and greps the log (`pre-push:9-13`); tier 2 is a comment telling you to ssh
to hbox (`:3-5`). `git config core.hooksPath` = `lean/tools/hooks` (installed). `tests/lower` is a
target (`LowerPrograms`); `tests/metasystem` (16 files), `tests/silicon_elab` (5), `tests/rehydration`
(1) are not: 30 `.lean` files, 10,690 lines, 308 theorems, 157 `#tooth`, zero `.olean`
(`find .lake/build -path '*tests*' -name '*.olean' | wc -l` = 0). `PLAN.md:99` cites a
`tests/silicon_elab/run_verilator_cosim.py` that does not exist (`ls tests/silicon_elab` shows five
`.lean` files). `measure.sh` is honest about being "one measurement, not a harness" (`:6`); its
history is §7.

### 2.6 What the tiers mean for the 137 `decide +kernel` in `Obend/Apps`

`Obend.Apps.*` is tier 2. Every Apps theorem — all eight flagship "end-to-end verified" files that
`README.md:112-118` leads with — is outside `lake build` and outside the pre-push hook. Four of the
eight (`FocHil`, `ObendRisc`, `SdrFt8`, `ZkNtt`) have no `.olean` under `.lake/build/lib/lean/Obend/Apps/`
(`ls -l .lake/build/lib/lean/Obend/Apps/*.olean`): in this tree they have never been elaborated.

---

## 3. Thirty theorems, sampled and classified

**Method (stated so it can be rerun).** For each of the eight directories, list every
`theorem`/`lemma` line (`grep -rnE '^\s*(@\[[^]]*\] )?(public |private |protected )*(theorem|lemma) ' Obend/<D>`),
sort by `path:line`, and take the k midpoints `⌊(2i+1)·N/2k⌋+1`, with k = Core 6, Lower 4, Leaf 3,
Hardware 6, Analysis 4, Apps 3, Vault 2, Consensus 2 (populations 2371, 490, 308, 1012, 385, 117,
351, 97). No hand selection. Classes: **U+** universal with content beyond its hypotheses; **U=**
universal but an unfolding/restatement of hypotheses or definition; **C** closed instance by
`decide`/`rfl`; **M** a conjunction mixing universal lemmas with closed instances.

| # | Location | Name | Class | Note |
|---|---|---|---|---|
| 1 | `Core/Code.lean:1700` | `metadata_mirror_cannot_quote` | U+ | real, via `derive_chain` |
| 2 | `Core/Proofs/Adequacy/CasesEval.lean:68` | `graph_object_access_execution` | U+ | simulation case, structural |
| 3 | `Core/Proofs/Collect/Mark.lean:72` | `markFrom_spec` | U+ | GC marking invariant, induction on fuel |
| 4 | `Core/Proofs/Forcing/Nest.lean:73` | `splitFrames_update` | U+ | small inversion lemma |
| 5 | `Core/Proofs/SubjectReduction.lean:517` | `primitive_input` | U+ | finite case check of a table; fine |
| 6 | `Core/RuntimeOrigins.lean:139` | `value_record_origin` | U+ | inversion on `ValueTyping` |
| 7 | `Lower/ExprCAM.lean:2545` | `decodeWireList_encodeWireList` | U+ | parametric round trip |
| 8 | `Lower/LeanKernel.lean:2098` | `runLExprSteps_sound` | U+ | reflection of a step function into `SSteps` |
| 9 | `Lower/Proofs/Complete.lean:1411` | `ltyped_inferL_complete` | U+ | completeness of inference |
| 10 | `Lower/Reflect.lean:335` | `beq_refl_of_decEq` | U= | `(m == m) = true`; this is `beq_self_eq_true` |
| 11 | `Leaf/BendTT.lean:1473` | `isAffineCoreTermArms_embedB` | U+ | commutation lemma |
| 12 | `Leaf/Futamura.lean:1089` | `instantiate_inject` | U= | `simp` unfolding lemma |
| 13 | `Leaf/Specialize.lean:412` | `mem_flatten_map` | U+ | generic list lemma; exists in core as `List.mem_flatten_of_mem` |
| 14 | `Hardware/Codec.lean:662` | `cborDecodeArrHeader32_encode_append` | U+ | round trip under `n < u32Bound` |
| 15 | `Hardware/GeometryCAM.lean:1159` | `evalSsaTapeRegsAux_getD_prefix` | U+ | prefix invariance, induction |
| 16 | `Hardware/Magnetics.lean:867` | `maxwell_stress_agrees_with_dq0_pm_torque` | U= | hypothesis `hPsi` *is* the identity; `grind`; the physics is in the name |
| 17 | `Hardware/OpenUSD.lean:1702` | `computeShellWallThicknessAffine3DUm_lipschitz_lower_bound` | U+ | enclosure lemma + `Int.ediv_mul_le`; good |
| 18 | `Hardware/ReductionMachine.lean:929` | `extractTileRuleAndImm_mkIcapRuleTile` | U= | `cases ruleOp <;> rfl` |
| 19 | `Hardware/Types.lean:579` | `compileTagInject_caseMux_sound` | U+ | by `bv_decide` (compiled trust) |
| 20 | `Analysis/EqSatHypergraph.lean:289` | `findMulInNodes_mem` | U+ | checker → semantic fact |
| 21 | `Analysis/Equitable.lean:1769` | `gaussianInt_mul_comm` | U+ | algebra; library-shaped |
| 22 | `Analysis/QuantumWalk.lean:154` | `godsil_cospectral_parity_implies_pst` | U= | `E` is an arbitrary `Nat → Nat → Nat → Int`; hypotheses assert the alignment; conclusion is sum-congruence. Not Godsil's theorem |
| 23 | `Analysis/SosLyapunov.lean:413` | `checkSosLyapunov_sound` | U+ | checker → Lyapunov inequalities via `checkPsatzNonneg_sound`. **This is the bridge shape the council asked for** |
| 24 | `Apps/FocHil.lean:1179` | `nominalFocDriveComp_closed` | C | `closedB = true` by `decide +kernel` |
| 25 | `Apps/QuantumPhotonicMatter.lean:407` | `quantumPhotonicMatter_inCore_futamura2` | M | general lemma applied to four fixed books; side facts by `decide +kernel` |
| 26 | `Apps/SovereignDrex.lean:571` | `sovereignDrex_engine_and_bft_finality_sound` | M | universal conjuncts delegated to real lemmas, ∧ `advanceQuorumBoundGate … = some drexQuorumFinalGate` |
| 27 | `Vault/Escrow.lean:751` | `ev_guard_okT` | U+ | evaluation lemma |
| 28 | `Vault/Rehydration.lean:757` | `rerender_square` | U+ | `filter`/`map` commute; small but real |
| 29 | `Consensus/Epistemic.lean:483` | `sybilTotalInfluence_le_seedCutBound` | U+ | induction; the *headline* two lines below, `epistemic_sybil_bounded_by_seed_cut` (`:500`), is `Nat.le_trans` of its two hypotheses |
| 30 | `Consensus/Simplex.lean:355` | `Cert.ofData_toData` | U+ | round trip, `cases; rfl` |

**Tally:** U+ 21, U= 5, C 1, M 2, plus one library duplicate counted inside U+ (#13; #10 and #21
are also library-shaped). **INFERRED:** the population is dominated by `Core` (2371 of 5131
theorems in these eight directories), and `Core` is real. The uniform sample therefore *clears*
"the library is mostly fixtures" and *confirms* the council's narrower claim: the problem lives in
the named headline theorems. So I took a second, targeted sample.

### 3.1 The 68 `golden_*` / `*_verified` theorems

`grep -rnE '^\s*(private |protected |public )*(theorem|lemma) +[A-Za-z0-9_.]*(golden_[A-Za-z0-9_]*|_verified)\b' Obend | wc -l`
= **68** (matches the number given to me). Classifying the proof text mechanically: 29 `decide
+kernel`, 4 `refine ⟨rfl, …⟩`, 1 `rfl`, 1 structured, 33 where the `:=` is more than 120 lines
below the name. I read seven of those 33 (`Hardware/GeometryCAM.lean:1665`,
`Hardware/UserspacePhysical.lean:1394`, `Hardware/Compiler.lean:2568`, `Hardware/OpenUSD.lean:898`,
`Apps/FidgetCam.lean:212`, `Hardware/TapeoutPipeline.lean:1231`, `Consensus/Epistemic.lean:305`):
six are `let`-bound fixtures followed by a `match … with | some m => checkRtlModule m && evalModuleOutputs m … == [...]`
closed Boolean; the seventh (`all_know_verified`) is `fun _ _ => hval`, a restatement of its
hypothesis. **INFERRED:** 66 of 68 are closed instances; the two exceptions are hypothesis
restatements. None is a theorem in the sense a Mathlib reviewer would accept the word; all are
useful regression tests.

### 3.2 `decide +kernel`

`grep -rn 'decide +kernel' Obend | wc -l` = **675** in 109 files (the 609 I was given is two days
of swarm older). By directory: Hardware 169, Apps 137, Teeth 104, Lower 61, Analysis 59, Law 36,
Tactic 28, Core 14. **READ**, `Apps/FocHil.lean:1176-1180`: five consecutive `theorem *_closed :
*.closedB = true := by decide +kernel`. These are the right *checks*; they are the wrong *keyword*.

---

## 4. The `accepted = true` pattern (READ)

`grep -rnE 'accepted = true' Obend/Apps | wc -l` = 32 conjunct sites in 8 files. Each `accepted` is
emitted by a local `#import_obend` elaborator (`Apps/ObendRisc.lean:612-651`, duplicated per app)
that runs `elaborateRiscObendFile` at compile time, throws on `.error`, and on `.ok` emits
`@[expose] public def Ns.accepted : Bool := true` and `public theorem Ns.accepted_eq : Ns.accepted = true := rfl`
(`:621-624`). `WorkbookPackage.accepted` is set `:= true` at `Elab/Workbook.lean:533` and `:1570`
after `FrontEnd.accept` succeeded. The *elaboration succeeding* is a real build-time test; the
*theorem* carries no information. By contrast the per-claim `claim_*_holds` theorems the same macro
emits (`ObendRisc.lean:641-650`) are the right shape: statement `obligationMeaningWithJudges … obj just`,
proof `obligationWithJudges_sound` applied to a `decide +kernel` on the checker — a kernel-checked
instance *with a semantic meaning*. The honest version of the 32 conjuncts is to delete them and
let the `_holds` theorems stand.

---

## 5. Lower and Workbook: what "lowering Lean to Core4" and "a Lean kernel checker" cover

### 5.1 `Obend/Lower/Fragment.lean` (476 lines) — honest, keep the code, fix the sentence

`readApp` (`:231-295`) reads `Nat.zero/succ`, the literal ops, `Bool`, recursors of `Nat`, `Bool`
and "fragment inductives" (first-order, parameters only), constructors into `record`/`inject`,
structures via `split`, definitions through `eq_def` into `recConst` with a note when the kernel
value goes through `brecOn`/`WellFounded.fix` (`:280-291`), type-argument specialisation at use
(`:297-306`). `lowerTy` (`:149-179`) erases `Prop` and type formers to `{}`. `inFragment` (`:323`)
is the honest predicate. The name a Lean developer would give it: **"a reader for the first-order
`Nat`/`Bool`/fragment-inductive sublanguage of kernel `Expr`, with recursion through `eq_def`"**.
It is `MetaM` code, i.e. trusted; `lower_sound` (`Proofs/Sound.lean`) relates `LExpr` to Core4,
and the `transport@1` judge's `WorkbookTransportMeaning` (`Elab/Workbook.lean:686-698`) states the
Lean-side bridge as a reducibility result over a `SourceTheory` — the right shape; whether
`SourceTheory.Provable` is adequate for Lean I did not audit. `METATHEORY.md:17` says "Closed Lean
4 kernel terms … lower into Core4"; the word missing is *fragment*.

### 5.2 `Obend/Lower/LeanKernel.lean` (2420 lines) — a toy kernel in Lean, a comparator in silicon

Since the council: `kernelIsDefEqStep` (`:668-724`) now has `Nat`-literal bridging, proof
irrelevance via `inferPrev`, and one-sided λ-η with a domain-compatibility check; `kernelWhnf`
(`:471-519`) does β, ζ, δ by name lookup, `Nat`-ι, `Quot.lift`, general ι through `KRecRule`, and
projections. Still absent: lazy δ by definitional height, universe normalisation beyond
`kernelLevelEq`, caching, η for structures, any treatment of `let` in the context, nested/mutual
inductives. As a **model** it is fine; `kernelIsDefEqFull_sound` (`:1728-1766`) is 2 universal
conjuncts (reflexivity, succ-bridge) and 9 `rfl`s on hand-built terms; `silicon_kernel_check_sound`
(`:1430-1474`) is unchanged: 7 `rfl`s on 7 declarations plus 6 `Evaluates` facts about
`kernelCheckLExpr`, the three-`Nat` comparator (`:1058-1073`), fed by `encodeDeclCheckLExpr`
which computes `inferredTag := if kernelCheckDecl env fuel decl then 1 else 0` **on the host**
(`:1080-1092`).

The newer "term-level" engine is worse, not better. `inferTypeLExpr` (`:2222-2281`) is a
4-argument `LExpr` returning hard-coded type codes (1 = `Nat`, 17 = `Nat → Nat`, 34, 3/4 for
sorts, `arg0*16+arg1` for arrows). `encodeChildSyntaxCode` (`:2303-2333`), which produces its
inputs on the host, contains

```
let b := if rawB == 34 then 2 else rawB
…
if d == 2 && b == 2 && dom == .bvar 0 && body == .bvar 0 then 2 else arrowCode
```

— special cases that exist to make specific fixtures in `real_silicon_kernel_node_check_sound`
(`Lower/Proofs/SiliconKernel.lean:747-800`: nine node encodings, nine `kernelNodeCheckSpec`
Booleans, `SSteps` on nine 4-tuples) come out right. `encodeDeclStatusTag`
(`SiliconKernel.lean:169-195`) decides "universe mismatch" by `match ty with | .sort u => … u.depth`.
A reviewer would name these: `KExpr` → `ToyKernel`; `silicon_kernel_check_sound` →
`kernelCheckDecl_seven_fixtures`; `inferTypeLExpr` → `typeCodeTable4`; and the sentences "Pure Self-Hosted Lean Kernel & Elaborator Lowered to `Core4` and
`Leaf.Book`" (`LeanKernel.lean:3`) and "lowers the Lean 4 Kernel (`Lean4Lean`) … eFPGA Simulation …
on `ReductionMachine`" (`SILICON-ELABORATOR.md:3,184`) →
"a 4-word type-code comparator, whose descriptors the host computes".

### 5.3 `Obend/Lower/Inductive.lean` (1555 lines)

`lower_inductive_sound` (`:1001-1040`) is: lowered `KName/KLevel/KExpr/KSyntax` are Core4 values and
decode back (universal, real, by `canonical_*` and `decode*_lowerT`), plus three closed evaluations
(`isZeroLevel` on `.zero`/`.succ l`, `levelSuccDepth` on depth 2). Honest name:
`kexpr_core4_serialization_roundtrip`. `compileMultiCtorIota_sound` (`:1538-1552`) is universal
over `n`, `defaultVal`, `v`, `xs` for three hand-written recursors (`Nat`, `Option Nat`,
`List Nat` length, plus one nested). Honest name: `three_example_recursors_evaluate`. Neither says
anything about *Lean's* inductives; `Fragment.read` is where that happens.

### 5.4 `Obend/Elab/Workbook.lean` (1802 lines)

The design is right: `.obend` sources elaborate at Lean compile time; defs and claims become
constants via `ToExpr` (`:951-1165`); claims get `_holds` theorems with semantic statements (§4);
`workbookTransportJudge` (`:738-759`) is a genuine `Obend.Judge` instance with `sound` and
`complete` discharged. Two things to fix: `pkg.accepted` is a flag, not a fact (§4), and the file
duplicates every import as `public import` + `public meta import` (`:3-47`) — 22 pairs — which
turns a Workbook edit into a rebuild of every importer.

### 5.5 `RealAnalysis.lean` has moved

The council reported zero theorems. The working tree has `Interval.add_mem`, `sub_mem`, `mul_mem`
(`Analysis/RealAnalysis.lean:184,210,255`), `sqr_mem`, `*_wf`, and `evalInterval_sound` (`:402`),
all universal over `CanonicalRat`, proved by `grind` over `mul_bounds_*`, and three tier-1 teeth
(`:471-499`). That is the correct repair and it should be said so in the report that replaces the
council's §1.2.

---

## 6. Numbers checked or refined

| Claim given to me | Mine | Command |
|---|---|---|
| 609 `decide +kernel` | 675 in 109 files | `grep -rn 'decide +kernel' Obend \| wc -l` |
| 68 `golden_*`/`*_verified` | 68; 66 closed instances, 2 hypothesis restatements | §3.1 grep + reads |
| 1405 `@[expose]` | 2686 occurrences = 2381 `@[expose] def/abbrev/instance/structure/inductive` + 218 files with blanket `@[expose] public section` + 87 `deriving @[expose] DecidableEq` | `grep -rn '@\[expose\]' Obend \| wc -l` and the three sub-greps |
| 32 `X.accepted = true` with `accepted := true` | 32; the definition is macro-emitted, `grep 'accepted := true'` finds 0 because it is `quote`d syntax at `ObendRisc.lean:623` | `grep -rnE 'accepted = true' Obend/Apps \| wc -l` |
| 44 of 79 cited names absent | My extraction: 427 backticked snake_case identifiers in the 11 root docs; 251 are theorem names in the tree; 176 are no declaration of any kind; 74 of those have theorem-shaped suffixes (`_sound`, `_complete`, `_preserves`, …); 113 of the 176 appear in the 7 docs `#docs_census` governs | `cat <docs> \| grep -oE '\`[^\`]{3,80}\`' \| tr -d '\`' \| grep -oE '^[a-z][A-Za-z0-9]*(_[A-Za-z0-9]+)+$' \| sort -u`, then `comm` against `theorem`/`def` names grepped from `Obend` |
| `#tooth` | 466 lines: 309 under `Obend/` (157 in `Obend/Teeth`, 152 in tier-1 modules, of which 42 in `Analysis`/`Hardware` are new since the council) and 157 under `tests/` that no target builds | `grep -rn '^#tooth' Obend tests \| cut -d: -f1 \| xargs -n1 dirname \| sort \| uniq -c` |
| 0 `sorry` | 0 in proofs; 23 docstring mentions | `grep -rnw sorry Obend` |
| `native_decide` | 27 proof positions, 27 `#assert_compiled` pins; plus 23 `bv_decide` (same trust class, undocumented) | §1 row 8 |

Sample of the 74 absent theorem-shaped names: `evalInterval_correct`, `interval_add_sound`,
`interval_mul_sound` (the real ones are now `evalInterval_sound`, `Interval.add_mem`,
`Interval.mul_mem` — the docs cite the names that were planned, not the ones that landed),
`simplex_safety`, `zoe_offer_safety`, `compileBook_correct`, `emit_verilog_eval_eq`,
`futamura1_sound`, `lrat_sound`, `checkAgainst_complete`, `golden_openusd_liverps_sdf_verified`.

---

## 7. The rebuild cascade: measured history and today's estimate

**READ**, from `docs/MEASURE-*.log` (tool: `tools/measure.sh`; `LEAN_NUM_THREADS=2`; "load" is the
Mac's 1-minute load average at the time):

| Date | Tree | Private proof edit (Adequacy) | Exposed def appended to `Core/Term.lean` | Unexposed body edit (`Check.lean`) |
|---|---|---|---|---|
| 2026-10-30 | ~110 modules | 32 s, 4 modules | 78 s, 40 modules | — |
| 2026-11-01 | 279 jobs, load 153 | 5 s, 1 module | 198 s; 177 Built + 28 Replayed | — |
| 2026-11-01 EXPOSE | 283 jobs, load 210 | 1 s, 1 module | 190 s / 207 s (two runs); 188 Built + 28 Replayed; Σ per-module 350 s; those modules total 79.5K lines today | 7 s, 1 module (`Check` rebuilt, nothing downstream) |

The discipline works where it is applied: a private proof costs one module; an unexposed body
edit costs one module. The cascade is entirely the exposed interface.

**Today (READ via script over `import` lines, `scratchpad/closure.py`):** 480 modules, 439 tier-1.
Reverse closure of `Obend.Core.Term` = 372 modules, **333 tier-1, 181,838 lines** (was ≈216 of 283
on 11-01); `Obend.Core.Ty` 312; `Obend.Core.Data` 213; `Obend.Core.Check` 205; `Obend.Slot` 170;
`Obend.Hardware.Types` 42 (45.9K lines). Blanket `@[expose] public section` by directory:
Hardware 39/43, Lower 22/25, Vault 14/16, Consensus 4/4, Logic 9/9, Equiv 10/13, Core 56/150,
Spec 2/29, Slot 0/9, Run 1/26. `Core/Term.lean` itself is `public section` with per-def
`@[expose]` (`:9,15,20,…`), i.e. the hub is disciplined; the leaves are not.

**PROPOSED estimate for the same Term edit now.** Lines in the closure grew 2.3×, modules 1.5×.
Linear in lines, Σ per-module time ≈ 800 s; at two threads with the Core→Lower→Hardware→Analysis
chain as critical path, **8–12 minutes wall on an idle Mac**, and the new Hardware/Apps modules are
heavier per line than Core (169 `decide +kernel` in Hardware; `SiliconElabFabric.lean` 3190 lines,
`LeanKernel.lean` 2420) so **10–20 minutes is the range I would bet on**, 3–6× the 2026-11-01
figure; under today's load 45 it will not finish in the hook's patience. On hbox with
`swarm-build` and more threads, 3–6 minutes. The honest number is the one `tools/measure.sh` prints
when rerun on hbox; nobody has run it since 283 jobs. Note also that `measure.sh` measures the
*rarest* dangerous edit (appending to Term); the common one is a body edit inside a blanket-exposed
Hardware file, which rebuilds that file's dependents even when no importer reduces it.

**INFERRED, the connection:** waves 5–6 proved by `decide +kernel` *across modules* on fixture
data; that requires the definitions to be `@[expose]`d for the importer's kernel to reduce them;
the lanes therefore wrote `@[expose] public section` at the top of every file. The fixture proof
style and the rebuild cascade are one decision.

---

## 8. What I would change about the gate so the pattern cannot recur (PROPOSED)

1. **A statement-shape census next to the axiom census.** A `#theorem_census` in
   `Obend/AssertAxioms.lean` style: for every package `thmInfo`, strip `let`s, and call the
   statement *closed* if it has no `forallE` binder whose domain is not a `Prop` or an instance.
   Print per-module counts `theorems / closed`; refuse a closed statement that is not declared
   through a `fixture` command (a thin wrapper that adds an attribute), and refuse a `theorem` whose
   name ends in `_sound`/`_complete`/`_verified`/`golden_*` while its statement is closed. Docs may
   quote only the two census verdict lines. ~200 lines; one lane-day; the migration of ~700
   declarations is mechanical (`sed` on the keyword) and the number the headline loses is the
   number that was never a theorem.
2. **Tier 2 cannot be stale.** The pre-push hook refuses when `Census.olean` is older than any
   source or any `Apps` module lacks an olean, and prints the hbox command. Add
   `tests/metasystem`, `tests/silicon_elab`, `tests/rehydration` to a `Tests` lib or delete them;
   308 theorems that nothing elaborates are prose. ~30 lines of shell, one lakefile stanza.
3. **Bare-name resolution in `#docs_census`.** Extract every backticked `[a-z][A-Za-z0-9]*(_[A-Za-z0-9]+)+`
   token, resolve by suffix against `env.constants`, fail on dangling. 40 lines in
   `DocsCensus.lean`; the real cost is rewriting 113 citations in the seven governed docs, which is
   the point. Invoke `#check_docs_census` too, or delete it.
4. **Exposure is per-def, never per-file, outside `Core`.** The census `run_cmd` already reads
   files; add a check that `@[expose] public section` appears only under an allow-list
   (`Core/Term`, `Core/Ty`, `Core/Data`, codecs). Migrate Hardware first (39 files). One lane-day
   per directory; the measurement in §7 is the control.
5. **`#tooth` refuses closed targets** (same closedness test as 1): a tooth on a fixture only
   proves the fixture is sensitive. 10 lines beside `Tooth.lean:175`. Move `verifyDualPoleTooth`
   out of `Tooth.lean`.
6. **One `#import_obend`.** The macro is copied as `local elab` into seven Apps files and
   `Hardware/UserspacePhysical.lean:798` (`grep -rn 'elab "#import_obend' Obend`); Workbook already owns
   it (`Workbook.lean:1777`). Delete the copies; drop `accepted_eq`.

---

## 9. Three changes first, with cost, and one question

1. **Fixture keyword + shape census (8.1).** Cost: one agent-day for the command, one for the
   mechanical migration, a tier-2 build on hbox to confirm. Benefit: every number in `METATHEORY.md`
   becomes checkable and the 66/68 and 32/32 patterns cannot be written again without the build
   saying so.
2. **Tier-2 freshness gate + tests as a target (8.2).** Cost: half a day plus the first honest
   tier-2 run on hbox, which will surface whatever the four never-built Apps and the 87 changed
   files have broken. Benefit: "0 sorryAx" means the tree in front of you.
3. **Bare-name docs census + Hardware de-blanketing (8.3, 8.4).** Cost: two agent-days of edits,
   mostly prose, plus one `measure.sh` run on hbox before and after. Benefit: the documents stop
   describing a different system, and the one-edit cost comes back under what the hook can carry.

**The question for Ember:** when the census starts printing `theorems / fixtures` separately,
are you willing for the headline to read something like *7,100 theorems, 700 fixtures* instead of
*7,861 theorems* — i.e. is the number allowed to go down, or must the fixtures keep the keyword?
Everything in §8 follows from that answer.
