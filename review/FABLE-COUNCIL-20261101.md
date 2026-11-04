# Council Critique — Objective Bend, 2026-11-01
### Claude Fable 5.1, for the Multimodel Council (with Gemini 4 Argon and GPT-6 Astra)

Every claim is tagged. **READ** means I opened the file and the statement is what the text says
(file:line as of commit `7c699ca` plus the uncommitted working tree). **INFERRED** means a
conclusion drawn from several READ facts. **PROPOSED** means a design I am recommending. Where
I give a number, I give the command that produced it so anyone can rerun it. I modified no
Lean or Rust file.

---

## 0. Method

I read `COUNCIL-BRIEF-20261101.md`, then all twelve top-level documents (`AMBITION`, `THESIS`,
`DESIGN`, `PLAN`, `PHYSICAL`, `NEXT-MATHEMATICA`, `SILICON-ELABORATOR`, `METATHEORY`,
`GROUNDING`, `DEOS-CONTRACTS-CONSENSUS`, `README`, `TEST_READY`), then the Lean tree
(`lean/Obend/`, 452 files, ~162K lines by `find … | xargs wc`), the Rust host
(`hardware/rust-ffi/src/lib.rs`, `crates/obend-{ffi,gui,node,sandbox}`), the hardware
simulation directory, the test runners, the census, the teeth, and the git history. For every
subsystem the brief names I read the theorem *statements* and the definitions they quantify
over, not the docstrings. I also ran a mechanical check of whether the theorem names the
documents cite exist in the tree (§2.2).

The short version: the spine of this repository (Core4, Slot, Fold, Receipt, Lower, Leaf, Law,
Impact, the Vault hyperedge) is real, carefully proved, and worth building on. Waves 5–6
(Analysis numerics, Hardware physics/CAD/quantum, Silicon Elaborator, GUI bridge) are mostly
*tests wearing theorem clothing*, their documentation describes a system that does not exist,
and their integration into the spine is nominal. Argon's audit is accurate on every point I
could check and still understates the problem by about an order of magnitude, because Argon
audited individual theorems and the real failure is structural.

---

## 1. Headline verdict

1. **READ.** The kernel-adjacent layers are genuine metatheory: `Obend/Core/Term.lean` (the
   open-recursive calculus with `mix`/`fix`/`prototype`/`split`), `Obend/Slot.lean`
   (`Slot.read`, `read_blocked_exact`, `permanent_blocked_forever`), `Obend/Fold.lean`
   (`Admission` with `step_of_reads`), `Obend/Receipt.lean` (`dated_sound` with the
   `∨ Collision H` disjunct), `Obend/Lower/Proofs/{Sound,Checks,Complete}.lean`
   (`lower_sound`, `lower_checks`, `lower_complete_ltyped_nat` by reducibility),
   `Obend/Leaf/{Flatten,Specialize}.lean` (`flatten_sound`, `specialize_choice`,
   `moved_pin_blocks`), `Obend/Law/Contract.lean` (`Narrows`, `CellContract` with
   `inductive_preserves` as a *field*), `Obend/Vault/Hyperedge.lean` (`no_toctou`,
   `vaultTurn_disjoint_commutes`), `Obend/Analysis/Impact.lean`. These are universally
   quantified, their hypotheses are the right ones, and their proofs are structural.

2. **READ.** `Obend/Analysis/RealAnalysis.lean` — the rational interval arithmetic that
   `Flowpipe`, `TaylorModel`, `Hybrid`, `Diff.DualInterval`, the `QuantumWalk` Schrödinger
   flowpipes and the `real-analysis@1`/`intervalJudge` all rest on — contains **zero theorems**
   (`grep -n "^theorem" Obend/Analysis/RealAnalysis.lean` is empty; a tree-wide grep for any
   theorem mentioning `evalInterval`, `Interval.mul`, `Interval.add`, or `Interval.sqr` is
   also empty). `evalInterval_correct`, `Interval.add_correct`, `Interval.mul_correct`,
   `interval_add_sound`, `interval_mul_sound`, cited in `DESIGN.md` §6.3, `PLAN.md` WS 18,
   and `METATHEORY.md` §3, do not exist. Every "validated numerics" theorem in the tree is a
   `decide +kernel` on a concrete example. The validated-numerics pillar of "the next
   Mathematica" is currently unverified arithmetic plus examples.

3. **READ.** Of 140 theorem/definition names cited in the design documents that I checked
   mechanically, **59 do not exist anywhere in `lean/Obend/`** — not as declarations, not in
   comments (§2.2 has the list and the script). `DESIGN.md` §1 describes a `Core4` term
   language (`pi q A B`, `sigma`, `jElim`, `brand`, `quo`, `ind/ctor/matchE`, `slot`,
   `quote/unquote`, files `Core/Syntax.lean`, `Core/Quantity.lean`, `Core/Eval.lean`,
   `Judge/Accepts.lean`, `Judge/Proofs/OneChecker.lean`) that is not the term language in
   `Obend/Core/Term.lean:22-58` and whose files do not exist. `DESIGN.md` §8 names twelve
   `Obend/Hardware/` modules (`RTL`, `Sim`, `Verify`, `Verilog`, `TechMap`, `STA`, `Place`,
   `Route`, `PDK`, `GDSII`, `Multiphysics`, `MixedSignal`); **none exist**. The documents are
   a separate artifact from the code.

4. **INFERRED.** The single biggest architectural threat is not any one fake theorem. It is
   that each wave lands *beside* the spine instead of *through* it, in direct violation of the
   project's own rule ("Nothing lands beside; everything replaces", `AMBITION.md` §"What we
   hold to"). There are now two interval arithmetics, two law languages, two flowpipes, two
   OpenUSD models, at least four disjoint judge registries, two "kernels", and an "automaton"
   that is the RTL module under another name. The value proposition — one `Judge`, one
   `Slot`, one `Fold`, every domain a certificate producer checked by the kernel — is being
   diluted by every wave that reimplements a private mini-kernel. §2.3 itemizes the
   duplicates with file:line.

5. **INFERRED.** The second threat is the proof style of waves 5–6: 281 `decide +kernel`
   proofs tree-wide (`grep -rn "decide +kernel" Obend | wc -l`), 37 theorems named
   `golden_*`/`*_verified`, and a pattern where the universally quantified part of a
   "theorem" is a one-line consequence of its hypotheses and the impressive part is a
   concrete numeric instance (`6 = 6`, `tOuterJacket − tLcInSlot = 224000`,
   `kernelCheckDecl stdKernelEnv 8 validIdNatDecl = true`). These are tests. They are
   valuable as tests. They are being reported as theorems, in METATHEORY tables, with
   "0 sorryAx" as the headline, and that reporting is what the council was convened to stop.

6. **INFERRED.** The third threat is that the "certificate" boundary — the whole point of
   "a kernel that never trusts a search it did not run" — has been hollowed at the edges:
   hardware certificate decoders select golden presets by a `"mode"` string
   (`Obend/Hardware/Judge.lean:440,593,670,747,830`; `decodeRtlSynthCert` at :134 picks a
   module by `dagOk`/`cdcOk` flags); the "cryptographic" decider receipt is
   `sha256("{declName}:{format}:ok")`, which anyone can compute
   (`Obend/Law/Contract.lean:290-297`); the GUI "Pop Out to Lean 4" emits
   `theorem cell_N_law : True := by obend_law` (`Obend/FFI/Bridge.lean:647-658`), the server
   redefines `obend_law` as `first | decide +kernel | decide | omega | trivial` and declares
   success when stdout lacks the substring `error:` (`crates/obend-gui/src/server.rs:3920-3985`),
   and "Weave Certificate" is a one-leaf Merkle hash of the bytes with no proof checked
   (`Bridge.lean:661-676`). The view-affordance endpoint derives the law-dial mode from
   `hash % 3` (`Bridge.lean:~640`). A stranger who clicks these buttons is being shown a
   receipt for nothing.

What follows is the evidence and then the blueprint.

---

## 2. Overall project critique

### 2.1 What is real, and why it matters (READ)

I want to be precise about what is good, because the blueprint in §4 builds on it and
because the burst documentation makes it hard to tell the solid parts from the painted ones.

- **Core4 as it actually is.** `Obend/Core/Term.lean:22-58`: `hole n σ`, `bound`, `lam`,
  `app`, `mix`, `fix`, `specification`, `prototype`, `reflect`, `metadata`, `project`,
  `nat`, `boolean`, `label`, `binary`, `extend`, `record`, `get`, `ifZero`, `inject`, `case`,
  `ifBool`, `perform`, `done`, `split`. Quantities are `erased | affine | linear |
  unrestricted` on arrow types (`Obend/Core/Ty.lean:8-9,314-317`). This is the minidregg
  Core4 of `GROUNDING.md` §2 plus `hole` (CMTT closures) and `split`. It is a good calculus
  for the thesis: lazy open recursion, contextual holes, a consuming destructor. The
  150-file `Obend/Core/` directory (47K lines) is where the real metatheory lives
  (adequacy, subject reduction, conservation, bidirectional completeness, equi-recursive
  rows, filtered streams, splice). I did not audit it line by line; its theorem statements
  are universally quantified and its provenance (minidregg, nanodregg) is traceable.

- **Slot / Fold / Receipt.** `Obend/Slot.lean:37-60` defines a slot as `supports : Cand →
  List Fact` and `judge : Cand → Bool`; `read_blocked_exact` says a blocked read names
  exactly the dead supports. `Obend/Fold.lean:35-48` is a small, honest abstraction:
  `Admission` with `step_of_reads` (a non-moving row's step depends only on the facts it
  reads). `Obend/Receipt.lean:459-479` `dated_sound` has the exact shape the AMBITION
  promises: either the receipt's verdict and post-state are what re-execution gives, *or*
  you have exhibited a collision in `H`. This is the correct way to state hash-dependent
  soundness without axioms.

- **Lower.** `Obend/Lower/Fragment.lean:199-330` is a real reader of Lean kernel `Expr`
  into `LExpr` (`Obend/Lower/Syntax.lean:52-76`): `Nat`/`Bool` recursors, fragment
  inductives via their recursors, structures via `split`, recursion through `f.eq_def` into
  `recConst`, specialization of type arguments at use. `lower_sound`
  (`Proofs/Sound.lean:281`) is by simulation with an `AheadChain`; `lower_checks`
  (`Proofs/Checks.lean:378`) goes through `annotated_complete`; `lower_complete_ltyped_nat`
  (`Proofs/Complete.lean:865`) is a reducibility argument. This is the best-engineered
  bridge in the repo and the one the Silicon Elaborator should actually run through (§3.3,
  §4 P7).

- **Leaf.** `flatten_sound` (`Leaf/Flatten.lean:355`) is `.get C.flatten m ≈b .get C.object
  m` under `C.closedB`, via `BEquiv`; `specSlot` (`Leaf/Specialize.lean:99`) is literally a
  `Slot LeafPin Candidate` with `supports := Candidate.supports`, and `moved_pin_blocks`
  (`:147`) is `read_blocked_exact` applied. This is the project's own rule obeyed: the
  compiler's deoptimization *is* a slot read, no new mechanism.

- **Law/Contract.** `Narrows` (`Law/Contract.lean:57`) is `∀ old new req, Admits law₂ … →
  Admits law₁ …`; `CellContract` (`:72`) carries `inductive_preserves` and `step_sound` as
  *proof fields*; `cellContract_trace_sound` (`:115`) is the induction. The concrete
  contracts in `Flowpipe.lean:152`, `OpenUSD.lean:853`, `Simplex.lean:611` discharge these
  fields with real (short) Core4 evaluation proofs. This is the right design.

- **Vault/Hyperedge.** `no_toctou` (`Vault/Hyperedge.lean:307`) is exactly the PlanBinding
  theorem minidregg promised: if the read pins cover the written cells and hold in both
  stores, validity is store-independent and the post-store agrees. `vaultTurn_disjoint_commutes`
  (`:398`) is real.

- **Consensus combinatorics.** `honest_quorum_intersection` and `qc_same_view_unique`
  (`Consensus/Simplex.lean:243-291`) are correct and cleanly proved with list-filter
  counting.

- **Clearing.** `weak_duality`, `certifies_epsilon_optimal`, `judge_certifies_epsilon_optimal`
  (`Judge/Clearing.lean:240-300`) are a genuine (small) primal-dual certificate check.

- **Teeth and census.** `Obend/Tactic/Tooth.lean` is a real mutation-testing command that
  replays the stored proof's dependency closure under a mutated definition; `Obend/Census.lean`
  refuses modules in neither build tier and runs `#assert_axioms_tree`. The *mechanism* is
  excellent. Its *application* is uneven (§2.5).

### 2.2 The documents describe a different system (READ)

I ran the following against the tree (zsh; `${=names}` forces word-splitting):

```
for n in ${=names}; do grep -rqE "(theorem|def|lemma|abbrev|instance) +$n( |$|:)" Obend --include='*.lean' || echo "MISSING: $n"; done
```

over 140 identifiers lifted from `AMBITION.md`, `THESIS.md`, `DESIGN.md`, `PLAN.md`,
`METATHEORY.md`, `PHYSICAL.md`, `NEXT-MATHEMATICA.md`, `SILICON-ELABORATOR.md`, and
`DEOS-CONTRACTS-CONSENSUS.md`. Result: **59 missing**. A second pass confirmed that 17
sampled missing names occur in *no* `.lean` file at all, not even in a comment. The missing
set includes, grouped by the document that cites them:

- Core/Judge: `one_checker`, `one_checker_to_rule_them_all`, `checkAgainst_complete`,
  `c4_monotonic`, `frontEnd_adequate`, `contextual_integrity`, `incumbent_kept`,
  `quote_captures_no_slots`, `brand_distinct_non_conv`, `lrat_sound`, `certified_sound`,
  `impact_complete`, `transportTheorem`, `reflectTerm_sound`, `byLoweredLean_sound`,
  `rerender_iff_in_support`.
- Vault/Ledger/Consensus: `suggestMultiField_admits`, `zoe_offer_safety`, `seat_offer_safety`,
  `book_transfer_conserves`, `book_split_conserves`, `drex_clearing_optimal_and_conserving`,
  `vaultTurn_wide_pullback_sound`, `vaultTurn_conserves_linear_slots`,
  `cellContract_step_inductive`, `relaw_preserves_forever_crown`,
  `blinded_projection_non_forgeable`, `grain_confinement_sound`,
  `powerbox_attenuation_monotonic`, `mandate_bounds_turn`, `simplex_safety`,
  `simplex_no_skip_and_fin`, `simplex_accountable_safety`,
  `simplex_bounded_liveness_after_gst`, `epistemic_sybil_bounded_by_seed_cut`,
  `disjoint_turns_commute`, `collapse_sound`, `collapse_preserves_accepts`.
- Hardware: `compileBook_correct`, `synth_lut_sound`, `retime_preserves_stream`,
  `pnr_judge_sound`, `drc_clean_iff`, `waferSpace_signoff_sound`, `thermal_prima_passive`,
  `scharfetter_gummel_flux_conserving`, `mzi_unitary_power_conserved`, `emit_verilog_eval_eq`.
- Analysis: `banach_contraction_enclosure`, `interval_add_sound`, `hasDeriv_chain`,
  `grad_sound`, `evalInterval_correct`, `schrodinger_unitary_flowpipe_verified`,
  `taylorModel_eliminates_wrapping_effect`, `bouncingBall_hybrid_trajectory_certified`.
- Leaf/Lower: `futamura1_sound`, `futamura3_cogen_deterministic`,
  `discrTree_futamura2_lut_sound`.

Some of these have near-synonyms in the tree (`qc_same_view_unique` for `simplex_safety`;
`exit_recovery_all`/`payout_exact` for `zoe_offer_safety`; the `inductive_preserves` field for
`cellContract_step_inductive`). Most do not. Three further facts complete the picture:

- `DESIGN.md:3`, `AMBITION.md`, `METATHEORY.md:3-5`, and the council brief give the module
  count as 408+, 437, and 320+, and the constant count as 52,368, 62,167+, and 65,842. The
  tree has 452 `.lean` files under `Obend/`.
- `Obend/Judge.lean:14` cites `review/GENERALIZATION-20261031.md` and
  `review/VISION-CLAUDE-20261031.md`; `Obend/Slot.lean:24` cites `review/KIMI-REVIEW-20261030.md`.
  None are in `review/` (`find . -name "VISION-CLAUDE*"` is empty). The review directory
  that the code cites has been emptied and the code was not updated.
- `PLAN.md` marks WS 18–33 **COMPLETE** in bold, each with a theorem list. At least one
  named theorem per workstream in WS 18, 19, 20, 21, 23, 25, 28, 29 does not exist.

**INFERRED.** This is not sloppiness in a few places; it is the signature of documents
written *before* the code as a specification for generating agents, then re-labelled as a
ledger of what landed, without a reconciliation pass. GROUNDING.md's own rule ("Every claim
names the file it came from … Nothing here was built or run") was the right one and was
abandoned on 2026-10-31, the day of 255 commits and +326K lines (`git log --since=2026-10-28
--shortstat`). The repo's authority on what is proved must become the *environment*, read by a
tool, never prose (§4 P0).

### 2.3 "Two of everything": the integration debt, itemized (READ unless marked)

The brief asks whether the subsystems "reinforce one another". Here is where they do not,
with the exact pairs:

| Concept | Instance A | Instance B | Status of the seam |
|---|---|---|---|
| Interval arithmetic | `Obend/Hardware/Accelerators.lean:179` `FloatInterval` over `Int` (misnamed; no floats), with proved `frep_interval_enclosure_sound` in `GeometryCAM.lean:249` | `Obend/Analysis/RealAnalysis.lean:73` `Interval` over `Rat`, **no theorems** | Disjoint. The proved one is the integer one nobody downstream in Analysis uses. |
| Flowpipe | `Obend/Analysis/Flowpipe.lean:50-70` rational `stepFlowpipe1D` with `remainderPad` as input | `Obend/Analysis/Hybrid.lean:350-420` a second, `Int`-only `stepHybrid`/`runFlowpipeTube` for the `hybridFlowpipeFormat` judge, hard-coded to mode `"thermostat"`, envelope `[15,35]` | Disjoint. The judge does not call the Flowpipe module it is named after. |
| Law language | `Obend/Spec/Law.lean:48-61` `LawExpr` (12 constructors: `eqC`, `leC`, `inC`, `eqR`, `leR`, `leROff`, `monotone`, `writeOnce`, `not/and/or/implies`) judged by `denote` on Vault pages (`Vault/Store.lean:320` `kind_law_inherited`) | `Obend/Law/Contract.lean` `CellContract` over arbitrary Core4 `Term`s | The Tier-1 discharge `checkLawDialPreserves` (`Contract.lean:195`) takes `LawExpr`, but a `CellContract` holds `Term`s; no function or theorem relates a `LawExpr` to the `Term` it is supposed to certify. `checkContractCert` (`:364`) returns `CertVerdict` and is referenced by no other file and has no soundness theorem; `cellContractOfProofs` (`:402`) requires real proofs. The "4-tier discharge" and the `CellContract` never meet. |
| OpenUSD | `Obend/Hardware/GeometryCAM.lean:849-1003` (`UsdArcKind`, `UsdOpinion`, `resolveLiverpsStack`, `UsdSdfModifier`, `UsdTimeSample`) | `Obend/Hardware/OpenUSD.lean` (`SdfPath` relocates, `AffineForm1D/3D`, `UsdPhysicalState`, `UsdTimeTrack`) | Disjoint (Argon). Neither has `SdfLayer`, `PrimSpec`, `PcpPrimIndex`, `UsdPrim`, or `xformOp` (`grep -c` = 0 in both). |
| Judge registries | `Obend/Judge.lean:32-37` `registry := [Lrat.format, dfaFormat, cfgCompactFormat, dclutchHoardFormat]` | `Obend/Hardware/Judge.lean:1040-1052` `hardwareFormats` (12); `Obend/Analysis/Format.lean` `impact@1`; `Obend/Lower/Judge.lean` `transport@1`/`lower@1`; `Judge/RealAnalysis.lean` `intervalJudge`, `sosJudge`; `Analysis/Groebner.lean:299` `positivstellensatzJudge`; `Analysis/Hybrid.lean:501` `hybridFlowpipeFormat` | `Format.find?` consults only the first list (`grep -rn "hardwareFormats\|Judge.registry" Obend` finds no cross-use). There is no one registry. |
| Certificates vs Vault turns | `Obend/Judge/Clearing.lean` primal-dual judge | `Obend/Vault/Hyperedge.lean` `ValidAt` (`:223`) checks `Admits C.law` by Core4 evaluation only | `grep -rl Clearing Obend/Vault Obend/Fold` is empty. The DEOS diagram "LP solver → compact receipt → `Judge.acceptsCited` inside a `VaultTurn`" is not implemented: no turn ever consults a certificate format. |
| Kernels | `Obend/Core` Core4 with `Check.checkAgainst` | `Obend/Lower/LeanKernel.lean` `KExpr` kernel: `kernelWhnf`, `kernelIsDefEq` (`:480-508`, structural equality after whnf), `kernelCheckDecl` (`:587`) | What is *lowered* to Core4/Book/tile is `kernelCheckLExpr` (`:803-817`), a function of three `Nat` tags `(sorryFlag, expectedTag, inferredTag)` that returns `1` iff `sorryFlag == 0 && expectedTag == inferredTag`; `encodeDeclCheckLExpr` (`:825-837`) computes `inferredTag` by running `kernelCheckDecl` *in Lean* first. The silicon "kernel" is a comparator fed by the host. |
| Automaton vs RTL | `Obend/Hardware/ReductionMachine.lean:95-131` `compileBookToAutomaton` = `compileBookDefsSat` with wires relabelled as `AutomatonTile`s; `evalAutomatonPacket` = `evalWireTable` | `compileBookToRtlSat` | `automaton_simulates_book` (`:140-160`) is `⟨rfl, rfl, rfl⟩` after unfolding. No NoC, no credits, no flits, no tile grid appear in any definition the theorem mentions. |
| Hardware judge "certificates" | `BinaryHwCert` (`Codec.lean:365`): `domain` + six untyped `Int`s `p0..p5` | per-domain `check…` functions that interpret `p0..p5` positionally | A 39-byte frame whose meaning is a convention in each checker; fine as wire format, but it is not a certificate *of* anything the kernel can relate to a model. |

**INFERRED.** Each row is a place where a generating agent could not see (or was not told
to use) the foundation and built a mirror — exactly the "Ground-truth-first, or they build a
MIRROR" lesson in the user's own briefing notes. The remedy is not to audit each mirror but
to make the spine the only place a thing can land (§4 P1–P3).

### 2.4 Theorem-shaped tests (READ)

Representative cases, so the pattern is unambiguous:

- `Obend/Analysis/TaylorModel.lean:160-198`: `tmExp dom lagrangeRem`, `tmSin`, `tmCos`,
  `tmLn1p`, `tmSqrt1p` take the remainder **as an argument**. The "certified" variants
  (`:224-228`) plug in `lagrangeRemExp4 dom := (1/40)·dom^5`, a rational constant chosen in a
  docstring ("where e^ξ ≤ 3"). There is no `exp` in a Mathlib-free library, so nothing
  relates these coefficients to the exponential function. The theorem
  `taylorModel_transcendental_enclosure_sound` (`:246-275`) then proves, by `decide +kernel`,
  that evaluating the polynomial `[1,1,1/2,1/6,1/24]` at `0` gives an interval containing `1`,
  that `[0,1,0,-1/6,0,1/120]` at `0` contains `0`, and that `sin²+cos²` of the two
  *polynomials* has coefficients `[1,0,0,0,0]`. True; not about transcendental functions.
- `Obend/Analysis/Flowpipe.lean:117-137` `flowpipe_step_encloses_euler`: one specific
  `[28,30]` box, three Euler points, `verifyTrajectorySafety … 3 … = true` and a runaway
  `= false`, all `decide +kernel`. `flowpipe_safety_admits_contract` (`:184`) conjoins this
  concrete fact with the genuine (and trivially general) `cellContract_trace_sound`.
- `Obend/Analysis/TaylorModel.lean:333-347` `taylorModel_picard_sound`: `picardLinearCoeffs 4
  1 (-1) 0 4 = [1,-1,1/2,-1/6,1/24]`, `evalTaylorPolyAt … (1/2) = 233/384`, and that one
  specific contracted box is narrower than one specific naive box. The claimed
  `taylorModel_eliminates_wrapping_effect` does not exist.
- `Obend/Analysis/Diff.lean:317-330` `interval_mean_value_enclosure`: one polynomial at
  `x = 3,4,5`. (`evalDual_fst_eq_eval`, `symbolicDeriv_agrees_with_dual` at `:104,:199` *are*
  universal and good — the rational forward/reverse AD is the one proven piece of Analysis.)
- `Obend/Analysis/Groebner.lean:192-227`: the universal part is `checkIdealMembership_sound`,
  i.e. "if the checker returned true, the expansion existed and the subtraction was zero" —
  a restatement of the checker; the rest is a 2-variable example discharged by `obend_law`.
  `stengle_positivstellensatz_sound` (`:325`) likewise: universal part is "if accepted, the
  SOS weights were non-negative". Neither says anything about ideals or real varieties:
  there is no `Poly` evaluation semantics in the statement, so "ideal membership" is a name.
- `Obend/Hardware/FluidThermal.lean:272-330`: the LC Drives model is
  `T = T_in + P·(R_1 + … + R_k)`; `lc_drives_in_slot_cooler_than_outer_jacket` says removing a
  positive resistance lowers `T` (`omega`); `lc_drives_potsdam_dyno_comparison_verified` is
  `decide` on `50000 + 8000·(2+5+12+18) = 346000` and the "224 °C" in `PHYSICAL.md` §4.2 is
  `346000 − 122000`. The numbers were typed in.
- `Obend/Hardware/Accelerators.lean:110-125` `ozaki_base13_2limb_product_exact` is
  `(a₀+13a₁)(b₀+13b₁) = a₀b₀ + 13(a₀b₁+a₁b₀) + 169a₁b₁`; `amd_gpu_mfma_dot4_exact` (`:304`)
  is that an instruction defined as a 4-term dot computes a 4-term dot;
  `systolic_tpu_eq_dsp58_cascade_eq_kulisch_dot` (`:372`) is three folds over `Int` lists
  being the same fold. None is wrong. `PHYSICAL.md` §5 sells them as "bit-exact
  high-precision multiphysics inner products with zero intermediate rounding error" on FP4
  tensor cores; there is no FP4, no rounding, no float anywhere in the file.
- `Obend/Lower/Proofs/SelfAccelerate.lean:155-173` `lc_drives_thermal_self_accelerates_6stage`:
  the "six stages" are one `LExpr` computing `50 + 8·9 = 122`, lowered (real `lower_sound`),
  emitted to a book (real `lean_to_book`), compiled to an RTL wire, "compiled to AMD GPU" by
  `compileRtlExprToAmdGpu` (an `Int`-register straight-line interpreter, `Accelerators.lean:222`),
  and then `runSystolicMacChain 50 [8,8,8] [2,4,3] = 122` by `rfl`. Stages 1–3 are the spine
  working; stages 4–6 are evaluating `122` three more ways.
- `Obend/Vault/PhysicalProjection.lean:277-331`: `physical_projection_deterministic` is
  `subst; rfl` (f x = f x); `physical_projection_doc_noninterference` is a list `lookup` on
  a cons with a different key. `HardwareProjection.lean:394-515` is the same five times.
- `Obend/Consensus/Finality.lean`: a 4-element enum with `rank`, `le_total`, and sixteen
  `by decide` lemmas about which of four tiers admits which of four operations. Correct and
  content-free; it does not mention `VaultTurn`, `Simplex`, or `Fold` except through
  `turnCommitTier : List FinalityTier → FinalityTier` (`:233`, a fold of `min`).
- `Obend/Hardware/ReductionMachine.lean:366-391` `dpr_preserves_neighbor_tiles_and_packets`:
  the three DPR phases are each `if t.tileId == target then … else t` (`dprPhase1Isolate`
  etc.); the theorem is `simp [hNeighbor]`. `dpr_specialized_tile_executes_new_book`
  (`:445`) is the `then` branch plus a `decide` on one tile mapping `10 ↦ 37`.

I estimate (INFERRED, from reading every theorem statement in `Analysis/`, `Hardware/
{QuantumMatter,GeometryCAM,OpenUSD,OpenHypergraph,Accelerators,FluidThermal,Kinematics,
Magnetics,PowerElectronics,Mechanics,ReductionMachine}`, `Lower/{LeanKernel,ExprCAM,
DiscrTreeLUT,MetaUnify,Proofs/SelfAccelerate,Proofs/SiliconKernel}`, `Vault/{Physical,
Hardware}Projection`, `Consensus/Finality`) that **well under a quarter of the wave 5–6
theorems have a universally quantified statement whose content exceeds its hypotheses**, and
that the ones which do are mostly algebraic identities over `Int` (`omega`/`ring`-shaped),
which is fine, and should be labelled as such.

### 2.5 The gate was not applied to the new waves (READ)

`#tooth` counts by directory (`grep -rn "^#tooth" Obend/Teeth tests | cut -d: -f1 | …`):
`Teeth/Hardware` 58, `Teeth/Core` 19, `Teeth/Law` 12, `Teeth/Lower` 11, `Teeth/Spec` 9,
`Teeth/` (Vault) 8, `Teeth/Tactic` 5, `Teeth/Leaf` 3, `Teeth/Logic` 2, `Teeth/Equiv` 2;
`tests/metasystem` 25, `tests/rehydration` 22, `tests/silicon_elab` 21. **Analysis: 0.
Consensus: 0.** The 58 hardware teeth target `Silicon`, `Process`, `Fabric`, `HDL` — the
first-wave modules from 2026-10-30. None targets `QuantumMatter`, `GeometryCAM`, `OpenUSD`,
`OpenHypergraph`, `Accelerators`, `Kinematics`, `Magnetics`, `FluidThermal`, or
`PowerElectronics`. `AMBITION.md` says "the crawling tree census and mutation teeth are the
gate." The census was applied (0 sorry is real); the teeth were not, and a `decide +kernel`
theorem about a concrete example cannot be toothed meaningfully anyway — mutating the
definition changes the number and the theorem fails, which proves only that the test runs.

`native_decide` appears 44 times (`grep -rn native_decide Obend | wc -l`), concentrated in
`Spec/Proofs/SpecificationClosure.lean` (14), `C4Vectors.lean` (6), and the digest checks.
`AssertCompiled.lean` tracks this honestly. Fine; just note that "0 custom axioms" is
"0 custom axioms plus 44 compiled-trust pins", which the census line already says.

### 2.6 The objects are missing from the domains (READ / INFERRED)

The thesis (`THESIS.md` §1) is that domain knowledge should be open-recursive `self`/`super`
prototypes with laws judged at the point of use. In `Obend/Hardware/` (39 files, 22K lines)
and `Obend/Analysis/` (15 files, 5.6K lines), the domain models are ordinary Lean `structure`s
and `def`s. The only places a physical object is a Core4 prototype are
`lean/tests/obend-source/world/physical/{LcDrivesStatorUsd,Cnc5AxisMill}.obend` and
`Obend/Hardware/UserspacePhysical.lean`, which flattens them and compiles the flattened book
to RTL. That is the correct shape and there are two of them. `PHYSICAL.md` §2.1's LIVERPS
table maps `Local/SubLayers` to `Term.mix` and cites `liverps_local_dominates_nonlocal`;
that theorem (`GeometryCAM.lean:908`) is about `UsdOpinion` records ordered by an enum
`UsdArcKind.strength`, and mentions no `Term`. The "exact correspondence" is a table, not a
theorem. The post-Mathematica claim is untested until a domain library is written *as
objects* and the theorems are about `fix spec seed` (§4 P12).

---

## 3. Audit of Argon's report

### 3.1 What Argon nailed (READ, each confirmed)

| Argon's item | Confirmation |
|---|---|
| I.1 `compileEquitableToPhotonicArray` never checks coupler κ against `Q` | `QuantumMatter.lean:229-241`: checks `checkEquitablePartition`, handshake, residual `= 0`, `1 ≤ evalSymmetrizedCouplingSq quotientEntry j (j+1)`, and DRC. No term mentions `spec.couplers[j]` against `quotientEntry`. The golden arrays (`:245-266`) use `[couplerPythagorean80_60, coupler3dB, couplerPythagorean80_60]` for both SOI and SiN. |
| I.2 discrete `H^k` not `e^{-iHt}`; `6 = 6` | `Equitable.lean:540-563` `iterateVecOp`; `QuantumWalk.lean:555-574`: the universal part is `(iterateVecOp … k … v = targetAmp ↔ iterateVecOp … k w0 (part v) = targetAmp)`, an `Iff` between two sides already proved equal by `equitable_intertwining_power`; the concrete part is `fullWalk3 = 6 ∧ quotWalk3 = 6`. |
| I.2 no `matMulEntry = partitionedMatVec` bijection lemma | `grep "matMulEntry.*partitionedMatVec"` empty; `partitionedMatVec` (`Equitable.lean:453`) sums over `cellOf j` for `j ∈ cellIndices` with no disjointness/cover hypothesis anywhere. |
| I.3 hand-authored projectors; `r²−3r+1` hard-coded | `QuantumWalk.lean:389-396` `checkP4IrrationalRatioObstruction` builds the polynomial inline and only reduces mod `r − 1`; `p3AlgebraicProj*` are literal `PolyMatrix` rows. |
| I.4 `0 ↔ 3` coupling; Majorana as adjacency | `QuantumMatter.lean:109-118` `let c03 := evalDirectionalCoupler2x2 t kappa m01.1 m23.2`; `:415-446` four literal 4×4 `Int` matrices; `symmetry_preserving_noise_zero_leakage` (`:508-569`) takes `hBlockH : Q 1 0 = 0`, `hBlockDH : dQ 1 0 = 0`, `hEvenInit : w 1 = 0` and the "zero leakage" conjunct is `simp [Int.mul_zero, Int.zero_mul, Int.add_zero]`. |
| I.5 `remainderPad : Interval` unverified; Schrödinger ODEs hard-coded 2D/4D | `Flowpipe.lean:38-42` `OdeSystem.remainderPad`; `QuantumWalk.lean:600-620` `schrodingerEigenmodeOde`, `schrodingerK2CoupledOde` literal `fields`. |
| II.1 split OpenUSD; `wallThicknessUm : Int` | `OpenUSD.lean:687-696`; the invariant is `decide (minWallUm ≤ st.wallThicknessUm ∧ …)` on the integer field. |
| II.2 no `FRepExpr.neg`; `.csgDiff` prunes only `.left` | `GeometryCAM.lean:55-69` constructors; `:482-505` `csgDiff` arm matches `.left` only. Rust `prune_tape_for_interval` (`hardware/rust-ffi/src/lib.rs:891-999`) emits `MinUnion { out, lhs: only, rhs: only }` placeholders (`:985-991`). |
| II.3 static `fSwept` | `GeometryCAM.lean:655-690`: `fSwept : FRepExpr` parameter; `Kinematics.lean` is never imported by the CAM section. |
| III.1 single-op optic; combinational RTL | `OpenHypergraph.lean:864-902` one `match op` producing a fixed 9-wire graph; `compileHypergraphToRtl` (`:1016-1026`) `regs := []`. |
| III.2 `"fib"` name match; call-argument discard | `Compiler.lean:943`: `if d.member == "fib" \|\| modName == "fib" then some { (compileNatRec2StateSat d.member 0 0 1) with name := modName }` — the Fibonacci coefficients are also literal; `:1700-1715` `compileTermPipelined` `.app (.get (.bound idx) member) arg` compiles `arg`, discards it (`some _`), returns `.regRead slotIdx`. |
| III.3 string-mode formats | `Hardware/Judge.lean`: 7 `"mode"` reads (`:440,593,670,747,830` + 2), `decodeRtlSynthCert` (`:134-152`) chooses one of three literal modules by `dagOk`/`cdcOk` flags; `decodeWaferSpaceCert` (`:438-446`) ignores everything but `"mode"`. |

Argon's audit is accurate. I found no item in it that the code contradicts.

### 3.2 Where Argon understated (READ unless marked)

1. **The Flowpipe problem is not a missing remainder bound; it is a missing interval
   semantics.** With zero theorems in `RealAnalysis.lean`, even a correctly derived
   `remainderPad` would land on an unproved `Interval.mul`. Everything in `Analysis/` that is
   called "validated" is validated by the author's belief that the four-corner product is
   right. (It probably is; that is not the point of a verified library.)

2. **The Bool checkers and the universal theorems never meet.** `checkEquitablePartition`
   (`Equitable.lean:344-355`) is what the matter compiler and all golden theorems call;
   `equitable_intertwining_power` takes `hEqAll : ∀ u j, j ∈ cellIndices → cellRowSum H
   (cellOf j) u = Q (part u) j`. No theorem of the form `checkEquitablePartition … = true →
   hEqAll` exists (`grep "checkEquitablePartition.*→"` empty). So the sentence "the compiler
   certifies the intertwining" is not provable from the tree as it stands. The same gap
   exists for every hardware `check…` (`checkWaferSpaceSignoff`, `checkPhotonicArrayMatterDrc`,
   `checkCandidateManufacturingSafe`): the checker *is* the specification; there is no model
   it is checked against.

3. **The Silicon Elaborator, which Argon did not audit, is the largest claims-to-reality gap
   in the repository.** `SILICON-ELABORATOR.md` and `PLAN.md` WS 23–28 claim a
   "pure Lean 4 kernel checker (`whnf`, `isDefEq`, `inferType`, general inductive ι,
   `Quot.lift`) compiled to `ReductionMachine` eFPGA tiles". What exists:
   - `kernelIsDefEq` (`LeanKernel.lean:480-508`) is structural equality after fuel-bounded
     `whnf`. No η, no proof irrelevance, no `Nat` literal ↔ `Nat.succ` bridging, no lazy
     delta by definitional height, no universe normalization beyond `kernelLevelEq`, no
     caching. It would reject most of `Init`.
   - `silicon_kernel_check_sound` (`:1175-1200`) proves seven `rfl`s on hand-built
     declarations (`validIdNatDecl`, `invalidSorryDecl`, …) and six `Evaluates` facts about
     `kernelCheckLExpr`, which is the three-tag comparator described in §2.3. The
     "lowered kernel check" never sees a `KExpr`.
   - `tests/silicon_elab/run_verilator_cosim.py` drives tags `0..3` and two 64-bit words
     through a LUT for five cycles. It is a real Verilator run of a real emitted module. The
     module is a tag comparator plus `4*lut_arg+2`.
   - The honest statement of what WS 23–28 achieved: a toy kernel in Lean (real, useful as a
     model), a packed-word hash-consing structure (`ExprCAM.lean`, with real round-trip
     proofs), a Miller-pattern unifier model (`MetaUnify.lean`), and a pipeline that can
     lower *small first-order* `LExpr`s to RTL. The claim that any of the kernel runs on the
     fabric is false today. The path that would make it true exists (§4 P7) and goes through
     `Fragment.read`, which already handles recursors and `eq_def`.

4. **`automaton_simulates_book` is a definitional identity.** See §2.3. The 3-phase DPR
   "protocol" has no protocol: no draining of in-flight work, no fence semantics beyond a
   Boolean, no clock. `SILICON-ELABORATOR.md` §5.3 presents a table "`Slot` ↔ `AutomatonTile`,
   `moved_pin_blocks` ↔ `SlotGuardReg` comparator"; `ReductionMachine.lean` imports neither
   `Leaf.Specialize` nor `Obend.Slot` (`:32-34` imports `Leaf.Emit`, `Lower.Lower`,
   `Hardware.Compiler`). The isomorphism is asserted in prose.

5. **Simplex is combinatorics plus a counter contract, not a consensus proof.** The quorum
   lemmas are real. There is no honest-node step relation over `State` (`Simplex.lean:151`),
   no theorem that two `FinCert`s at one height agree *as a consequence of the protocol
   rules*, no liveness, and no `SlashingReceipt` type in Lean (it exists only in
   `crates/obend-node/src/lib.rs`). `simplexCellContractOf f` (`:611`) enforces
   `2f+1 ≤ certSigners ∧ old.view ≤ new.view` where `certSigners` is a **count** field of the
   state, not a set of signers checked for distinctness or membership — a Byzantine proposer
   writes `certSigners := 3`. The `nodup` field on `QuorumCert` (`:97-101`) is the right idea
   and is unused by the contract.

6. **`EpistemicConsensus` is a deterministic argmin.** `Epistemic.lean:107-170`: `betterCert`
   by `(cost, digest)` lexicographic, `selectWinner` = filter valid then `pickBest`. The
   theorems are that the winner is a member, is valid, and that the choice is order-insensitive
   for pairs. The `EpistemicFrame`/`Knows`/`DistKnows` section (`:277-315`) is a two-line
   modal-logic skeleton. `epistemic_sybil_bounded_by_seed_cut` does not exist; there is no
   trust graph, no weight, no cut.

7. **The Tier-1 "sound" discharge is bounded enumeration with no soundness theorem.**
   `checkLawDialPreserves` (`Contract.lean:195-214`) enumerates `candidateValues` = each
   constant in the law `± {−1,0,1,2}` plus `solveLawWitness`, and returns `.valid` if no
   counterexample is found. Returning `.valid` establishes nothing about `∀ old new`. No
   theorem connects `CertVerdict.valid` to `CellContract.inductive_preserves`
   (`grep "theorem.*checkContractCert"` empty). The docstring says "Soundly verify".

8. **The decider receipt's "cryptographic authentication" is a public formula.**
   `Contract.lean:290-297`: `expectedDigest := sha256 "{declName}:{format}:ok"`, compared to
   the receipt's `digest`. There is no key, so there is no authentication; any party can
   mint a `.valid` receipt for any `declName`. If the intent is "bind the receipt to the
   claim", the thing to hash is the *certificate content* and the check is to re-run the
   judge on it (as `verifyClaim` does for `rewrite@1` in the branch above).

9. **The GUI bridge proves `True`.** Detailed in §1.6. In addition the standalone preamble
   in `server.rs:3920-3926` *redefines* `obend_split` as `split <;> try rfl <;> try
   contradiction` and `poly_ring` as `try omega`, so even a user who pastes a real theorem
   into the pop-out box gets different tactics than the Lean file `Obend/Tactic/Weave.lean`
   defines. The genuine bridge is `Obend/Elab/Workbook.lean` (`#import_obend`, `#obend_decl`,
   uncommitted changes in the working tree), which elaborates `.obend` at Lean compile time and
   emits real constants; it is not wired to the GUI.

10. **The Rust "solvers" have no inputs.** `hardware/rust-ffi/src/lib.rs`:
    `solve_femm_mesh()` (`:586`), `build_stator_frep_tape()` (`:834`),
    `eval_octree_frep_pruned()` (`:1012`), `evolve_physical_design()` (`:1159`) take no
    arguments. They are demos that produce a fixed `BinaryTapeCert`/report. `PHYSICAL.md`
    §7.5 calls them "Implements iterative 2D FEMM Newton-Raphson … 80-candidate Pareto
    optimization". `crates/obend-node/src/lib.rs:1221` `solve_primal_dual_clearing` is a
    uniform-price single crossing (midpoint of best bid/ask unit prices, then proportional
    fill), not an LP; that is a fine clearing rule, but "primal-dual LP solver" is the wrong
    name, and the Lean `weak_duality` it is paired with is for a one-commodity market.

11. **Projection "blinding" is one level deep.** `Vault/Projection.lean:164-250`: `cellBlind`
    hashes one cell; `projectedCommits` is a list of per-cell commits; `BlindedOpening` is an
    index into that list. There is no Merkle tree, so `verify_blinded_opening_complete` is
    about list indexing under a `Bounded H`. The doc's "Merkle multiproofs of the unredacted
    Vault root" is `Receipt/Merkle.lean` (real) applied nowhere in Projection.

12. **OpenUSD's `AffineForm3D` is real and good** (`OpenUSD.lean:159-680`: `enclosesAt`
    lemmas for every `FRepExpr` constructor, `evalFRepAffine3D_encloses_point` at `:674`) —
    and it is the second interval-like structure in Hardware that `Analysis/` does not use.

### 3.3 Conceptual sins Argon did not name (INFERRED from the READ facts above)

- **S1 — Prophecy as ledger.** Documents written as generation prompts were promoted to
  status reports. The repo's own `GROUNDING.md` discipline ("every claim names the file")
  was the cure and was dropped.
- **S2 — No checker ⇒ theorem bridges.** A Bool checker without a `check = true → P`
  theorem is a specification, not a verifier. The pattern is uniform across Equitable,
  Hardware judges, and the Contract tiers.
- **S3 — Numerics with no number.** A Mathlib-free library cannot *state* `exp x ∈ I`. The
  team chose (correctly, per the user's own modularity principle) to avoid Mathlib in tier 1,
  then wrote transcendental "enclosures" anyway. The way out is a typeclass interface for
  the analytic model with the Taylor-remainder axioms as *fields* (not axioms), instantiated
  in a leaf (§4 P1).
- **S4 — Many registries, no judge in the turn.** The thesis says every domain is a
  certificate producer and the Vault turn is where certificates are checked. Today
  `ValidAt` evaluates Core4 laws only; no `Format` is consulted by any turn.
- **S5 — Physics by identity.** The multiphysics modules state algebraic identities about
  `Int` quantities with physical names (`P·ΣR`, hoop stress `ρω²r²`, `(a₀+13a₁)(b₀+13b₁)`).
  Nothing is wrong, and nothing in them could be wrong, which is the problem: a law of
  physics that cannot be refuted by the formalization is not being formalized. A genuine
  multiphysics theorem relates a *discretization* to a *continuous* statement under a
  mesh/step bound, which requires S3 first.
- **S6 — The gate is unevenly applied** (§2.5).
- **S7 — Objects absent from the domains** (§2.6).
- **S8 — Names over substance in the hardware stack.** `FloatInterval` has no floats;
  `AutomatonNetwork` has no network; "A* maze routing", "Leiserson–Saxe", "STA", "GDSII"
  are cited in DESIGN with module names that do not exist; `RtlExpr` is 64-bit only, no
  widths, no `emitModuleSV` theorem (`HDL.lean:325` is a `def` with no theorem referencing
  it), and the Z3 "LEC" files in `hardware/sim/*.smt2` are hand-written for two tiny
  circuits (`lec_check.smt2:1-25`) rather than generated from `RtlModule`s.

---

## 4. Blueprint for the next wave (PROPOSED)

Ordered so that each step makes the next one checkable. P0–P3 are the structural
corrections; P4–P9 are the domain upgrades Argon and the brief asked for, now anchored to
the spine; P10–P12 are process.

**P0 — The environment is the only ledger.**
- Add a `lake exe docs-census` (sibling of `journal`) that extracts every backticked
  identifier and every `` `Obend/…/X.lean` `` path from `*.md`, resolves identifiers against
  the built `Environment` and paths against the filesystem, and fails the pre-push hook on
  any miss. Run it once; the 59 missing names and 12 missing modules become either code or
  deleted prose.
- Rewrite `DESIGN.md` §1 from `Obend/Core/Term.lean` and `Core/Ty.lean`; rewrite §8 from
  `ls Obend/Hardware`. Delete every "COMPLETE" stamp in `PLAN.md`; replace with a table
  generated from the obligation journal (`lean/Journal`) listing, per workstream, the
  universally quantified theorems and the example theorems separately.
- One count, computed: modules, constants, theorems, `decide +kernel` theorems, `#tooth`s,
  `native_decide`s, per directory, emitted by the census and pasted nowhere else.

**P1 — One interval semantics, with a real-number interface.**
- Make `Obend/Analysis/RealAnalysis.Interval` the only interval type. Prove, once:
  `Interval.add_mem`, `mul_mem`, `sqr_mem`, `neg_mem`, and
  `evalInterval_sound : (∀ x iv, (x, iv) ∈ env → ρ x ∈ iv) → evalPoint ρ e = some v →
  ∃ I, evalInterval env e = some I ∧ v ∈ I`. Replace `FloatInterval` in
  `Accelerators/GeometryCAM/OpenUSD` by `Interval` instantiated at `Int` via a typeclass
  `[OrderedRing α]`-style parameter (the tree already has its own `Int` lemmas; the generic
  statement is cheaper than the duplicate).
- Define `class AnalyticModel (R : Type) [OrderedField R] where exp sin cos ln1p sqrt1p : R → R;
  exp_taylor : ∀ n x, |x| ≤ 1 → |exp x − Σ_{k<n} x^k/k!| ≤ 3·|x|^n/n!; …`. State
  `tmExp_sound {R} [AnalyticModel R] : x ∈ dom → exp x ∈ evalTaylorModelPoint (tmExpCertified dom) x`.
  Instantiate `AnalyticModel ℝ` in a *tier-3* leaf that imports Mathlib (outside the
  `Obend` library globs, like `Teeth`), or constructively via Cauchy reals later. No axiom
  enters tier 1; the obligation is a visible typeclass parameter, which is the project's own
  stated discipline ("resources are not meanings … declared and fail by name").
- Flowpipe: delete `remainderPad` as an input. Derive it: with `DualInterval` from
  `Diff.lean` compute an interval Jacobian bound `L` of the vector field over an a-priori
  box `X̃`; take the Picard a-priori enclosure `X̃ ⊇ X₀ + [0,h]·F(X̃)` (verified by the
  checker), remainder `h²·L·‖F(X̃)‖/2`-shaped, and prove `flowpipe_step_sound` against a
  `class OdeModel` solution interface the same way. Hybrid.lean's integer `stepHybrid`
  (`:350-420`) is deleted and the judge calls `Flowpipe` on `Rat`.
- Groebner/Positivstellensatz: give `Poly` an evaluation `Poly.eval : (Nat → R) → R` and
  state `checkIdealMembership_sound' : check = true → ∀ ρ, (∀ g ∈ gens, g.eval ρ = 0) →
  target.eval ρ = 0` and `positivstellensatz_sound' : check = .ok → ¬ ∃ ρ, (∀ f ∈ strictPos,
  0 < f.eval ρ) ∧ (∀ g ∈ nonneg, 0 ≤ g.eval ρ) ∧ (∀ h ∈ eqs, h.eval ρ = 0)`. These are
  provable now, over any ordered commutative ring, with no transcendental machinery.

**P2 — Every checker gets its bridge theorem.** Template: for each `def checkX : … → Bool`
that any judge, compiler, or golden theorem relies on, a theorem `checkX_sound : checkX a =
true → SpecX a` where `SpecX` is the hypothesis form the universal theorems consume.
Concretely first: `checkEquitablePartition_sound` (→ `hCells ∧ hEqAll` of
`equitable_intertwining_power`, with `cellOf j := cellMembers (range dim) part j` and the
missing disjoint-cover lemma `partitionedMatVec_eq_matVec`), then the hardware
`checkPhotonicArrayMatterDrc`, `checkWaferSpaceSignoff`, `checkCandidateManufacturingSafe`
against explicit `Spec…` propositions, then `checkLawDialPreserves` either gets
`= .valid → ∀ old new …` (it cannot, as written) or is renamed `searchLawDialCounterexample`
and its `.valid` becomes `.noCounterexampleFound`.

**P3 — One registry, consulted by the turn.**
- `Obend.Judge.registry := coreFormats ++ Hardware.hardwareFormats ++ Analysis.formats ++
  Lower.formats`, with a census assertion that every `instance : Judge _ _` in the tree is
  reachable from a registered `Format`.
- `VaultTurn` gains `witnesses : List (String × ByteArray × ByteArray)` (format tag, object
  bytes, cert bytes). `ValidAt` gains `∀ w ∈ turn.witnesses, ∃ F, Format.find? w.tag = some F
  ∧ F.checkBytes r w.obj w.cert = .ok`, and `CellContract.law` may *cite* a witness by tag
  (a Core4 `label`) so that `Admits` can depend on it. Then the DEOS diagram is true: a
  clearing receipt is checked by `drex-clearing@1` *inside* the turn, and `no_toctou` extends
  to witnesses because `checkBytes` is pure.
- Delete every `"mode"`/`"preset"` decoder. A `Format.decodeCert` must be a total decoder of
  the certificate *type* from JSON or CBOR; `bad` must be a decoded instance.

**P4 — Quantum stack, done the way Argon suggests and anchored to P1/P2.**
- Polynomial intertwining: from `equitable_intertwining_power`, derive by linearity
  `∀ p : List Int, evalPolyOp H p (S w) = S (evalPolyOp Q p w)`; this is what every Krylov
  / truncated-Taylor propagator uses, and it is provable today.
- Continuous time: once `tmExp` is sound (P1), a matrix Taylor model for `e^{-iHt}` on the
  quotient with remainder `(‖Q‖t)^n/n!` gives a *validated* propagator enclosure; PST is then
  "the enclosure of `|U(τ)_{v,u}|²` contains 1 and excludes everything below 1−ε". That is a
  theorem about a photonic array, and it is what `compileEquitableToPhotonicArray` should
  certify.
- Spectral synthesis: Faddeev–LeVerrier over `Rat` for the characteristic polynomial; the
  splitting field as `ℚ[α]/⟨m⟩` via the existing `PolyMatrix.mulMod`/`polyReduceFuel`;
  Lagrange–Sylvester projectors `P_i = Π_{j≠i}(Q − λ_j)/(λ_i − λ_j)` computed, not typed;
  `checkSpectralDecomposition_sound : check = true → Σ P_i = I ∧ Σ λ_i P_i = Q ∧ P_i P_j = δ_{ij} P_i`
  mod `m`. Replace `p3AlgebraicProj*` literals and `checkP4IrrationalRatioObstruction` by
  instances of this.
- Majorana: a Clifford algebra `Cl₄` as `List (Finset (Fin 4) × Int)` with the
  anticommuting product, `P := −γ₁γ₂γ₃γ₄`, and the theorem `commutes P H → H` is
  block-diagonal in the parity eigenbasis; `majoranaTetronHamiltonian` becomes
  `toMatrix (i·γ₁γ₂ + i·γ₃γ₄)`, and "symmetry-preserving noise has zero leakage" is a
  corollary with `[ΔH, P] = 0` as the hypothesis instead of `Q 1 0 = 0`.
- Matter compiler: `synthesizeCouplers : (Q : Nat → Nat → Int) → List CouplerSpec` solving
  `κ_j² : κ_{j+1}² = Q_{j,j+1}Q_{j+1,j} : Q_{j+1,j+2}Q_{j+2,j+1}` by exact rationals, with
  `compile_sound : compile = true → ∀ j, couplerKappaSq (couplers[j]) · Q_{j+1,j+2}Q_{j+2,j+1}
  = couplerKappaSq (couplers[j+1]) · Q_{j,j+1}Q_{j+1,j}`. Replace `evalPhotonicArray4Mesh2Step`'s
  `c03` by a planar Clements mesh: layers alternate `(0,1),(2,3)` and `(1,2)`; the
  power-conservation theorem then holds per layer by `directionalCoupler_conserves_optical_power`
  (`Photonics.lean:188`, real) composed.

**P5 — Geometry/CAM.**
- Make the SSA tape the canonical form in Lean: `inductive TapeOp | const | var | add r r |
  … | neg r | min r r | max r r`, `evalTape : List TapeOp → ℤ³ → ℤ`, `pruneTape B tape`
  with `Choice` recording, `compactTape` (backward liveness), theorems `evalTape (compactTape
  (pruneTape B t)) p = evalTape t p` for `p ∈ B` and `(compactTape t).length ≤ t.length`.
  `FRepExpr → List TapeOp` by one `toTape` with `toTape_sound`. Then the Rust
  `prune_tape_for_interval` has a Lean twin and `BinaryTapeCert` carries something the kernel
  re-evaluates (`evalEvolutionCandidatePeakTemp` already does this for one metric).
- Swept volume: `sweep (tool : FRepExpr) (path : List (SE3 × SE3))` = `min` over segment
  endpoints of the transformed tool *minus* a segment-Lipschitz pad `L·‖Δ‖` where `L` comes
  from the interval gradient of `tool` (P1's `DualInterval`) and `‖Δ‖` from `Kinematics`'
  jerk-limited profile; theorem: the continuous sweep's SDF is bounded below by the
  discrete one minus the pad. `voxel_no_gouge_sound` then quantifies over *time*.
- One OpenUSD: delete `GeometryCAM.lean:849-1003`. Model `SdfLayer := List PrimSpec`,
  `PrimSpec := {path : SdfPath, opinions : List (UsdArcKind × Term)}`, and define
  `composePrim : List SdfLayer → SdfPath → Term` by folding `Term.mix` in LIVERPS strength
  order with `Term.fix … seed` for `specializes`. Then prove the table rows about `Term`:
  `liverps_local_dominates : (composePrim …).get m ≈b (upperLayer …).get m` when `m` is
  authored locally, via `flatten_sound`. `xformOp` stacks as a `List (SE3)` folded into
  the `FRepExpr` by an affine-transform constructor (`.xform M a`, with the affine-arithmetic
  enclosure lemma added to `evalFRepAffine3D_enclosesAt`).

**P6 — Hypergraphs and the compiler.**
- Functorial reverse AD: `adjoint : StrictOpenHypergraph → StrictOpenHypergraph` built by
  mapping each edge `op` to its cotangent edges (the per-op tables already in
  `compileOpticToHypergraph`) and *reversing the wavefront order* from `layerHypergraph`;
  `adjoint_sound : evalHypergraphComb (adjoint g) (fwdEnv ++ cotangentEnv) = reverse-mode
  gradient` by induction on the layering using `layerHypergraph_sound` (`:518`, real).
- Pipelining: `compileHypergraphToRtlPipelined` inserts one `RegSpec` per wavefront stage;
  theorem: the `k`-cycle register trace equals `evalLayeredStagesSync` prefix
  (`evalLayeredStagesSync_eq_evalLayeredStages` at `:440` is the lemma to lift).
- `Compiler.lean:943`: replace the `"fib"` branch by `extractTwoStateLinearRec : LeafDef →
  Option (c₀ c₁ a b : BitVec 64)` recognising `acc' = a·acc + b·prev` structurally, with
  `compileNatRec2StateSat_sound` quantified over the extracted coefficients. Fix the
  `.app (.get self m) arg` arm to bind `arg` to a fresh wire and pass it through the slot's
  input port (the multi-arg port compiler at `:1357` already has the machinery).

**P7 — The Silicon Elaborator, honestly.**
- The thesis path exists and is unused: `kernelCheckDecl : KEnv → Nat → KConstInfo → Bool`
  is a structurally recursive Lean function over the recursive inductives in
  `Lower/Inductive.lean`. Run it through `Obend.Lower.Fragment.read` (it handles recursors,
  structures, and `eq_def`), obtain `⌜kernelCheckDecl⌝ : LExpr`, and prove by `lower_sound`
  that `Evaluates (lowerT (.app ⌜kernelCheckDecl⌝ ⌜(env, fuel, decl)⌝)) (.boolean b) ↔
  kernelCheckDecl env fuel decl = b`. If `read` refuses, the refusal names the Lean construct
  to add to the fragment — that is the real Stage-1 work the roadmap described. Until that
  lands, retitle `silicon_kernel_check_sound` as `declCheck_tag_comparator_lowers` and remove
  "Silicon Lean Kernel" from `PLAN.md`.
- `kernelIsDefEq`: port Lean4Lean's skeleton — lazy δ by definitional height, η for `lam`
  and structures, proof irrelevance (`inferType` to `Sort 0`), `Nat` literal/`succ`/binop
  reduction, level normalization. Measure against real `.olean` declarations via the
  existing `fromLeanExpr` (`Inductive.lean:394`) on `Init.Prelude` and report accept/reject
  counts in METATHEORY as numbers, not adjectives.

**P8 — ReductionMachine as a machine.** Define `Tile := {rules : List Rule, inbox : Queue
Flit, credits : Nat}`, `Router` with XY dimension-order and credit counters, `Network :=
Grid Tile × Grid Router`, and `step : Network → Network`; define `simulates : Network → Book
→ Prop` as a simulation relation and prove `automaton_simulates_book` by it. DPR becomes an
instance of `specSlot`: `Candidate.tile (bitstream) (supports := env pins)`, and the DPR
theorems become `specialize_choice`/`moved_pin_blocks` instantiated — the table in
`SILICON-ELABORATOR.md` §5.3 should be *theorems named in the code*, each row one.

**P9 — Consensus as a state machine.** Honest-node transition relation over `State`
(propose at `leader`, vote once per view (`castVote_already_voted`), finalize on `2f+1`),
adversary as any message injection by nodes in `faulty`; prove `fin_cert_unique_per_height`
from `qc_same_view_unique`, prove `no_skip_and_fin` the same way, define `SlashingReceipt`
in Lean as two conflicting signed votes by the same node and prove `accountable : conflict →
∃ r : SlashingReceipt, f+1 ≤ r.signers.length`, and decode it in `obend-node` from the Lean
`Data` encoding (the `Cert.toData/ofData?` pattern at `:337-358` is already there). Make
`simplexCellContractOf f` check a `signers : List NodeId` with `Nodup` and membership in the
committee, not a count. Attach `FinalityTier` to `VaultTurn` by a theorem (`commit at tier t
→ the turn's witnesses include a cert of tier ≥ t`), not by a lattice in isolation.

**P10 — Teeth parity and theorem hygiene.**
- Rule: a `theorem` must have at least one universally quantified variable whose instance
  the proof does not compute; otherwise it is `example` or `#guard`. Move the 37
  `golden_*`/`*_verified` and the remaining concrete `decide +kernel` facts to
  `Obend/Teeth/**/Examples.lean` (tier 2). They remain valuable regression tests.
- Every universally quantified theorem in a new module ships one `#tooth`. Census emits
  `(theorems, examples, teeth)` per directory; pre-push refuses a directory whose new
  theorems have zero teeth.

**P11 — GUI/FFI truthfulness.** Pop-out must call `Obend.Lower.Reflect.reflectTerm` /
`Workbook` on the cell's actual obligation and emit a Lean file against the built oleans
(`LEAN_PATH` to `.lake/build/lib`, which `server.rs` already locates), never a `: True`
stub; weave must decode a `TransportCert`, run `transport@1` (`Lower/Judge.lean`), and store
the *receipt's* digest; affordances must come from `Vault.Law.suggestMultiField` (the
Bellman–Ford repair exists in Lean at `Vault/Law.lean` and is re-implemented in Rust at
`server.rs` — delete the Rust copy and call Lean). Until then, label the buttons "demo".

**P12 — Put the objects back.** Choose three domain examples — the LC Drives stator
(`LcDrivesStatorUsd.obend` already exists), the `MS350` phase leg, the `Q₃` photonic array —
and make the *canonical* definition the `.obend` prototype with `#law`s; use
`Workbook.#import_obend` to bring them into Lean; state the domain theorems about
`fix (compose …) seed` objects via `flatten_sound`. Measure: number of domain theorems
whose subject is a Core4 object. Today it is two files. If the number does not rise, the
"post-Mathematica objects" thesis is not being tested by the domain work at all, and the
domain work should pause.

---

## 5. On process (INFERRED)

`git log` shows 255 commits on 2026-10-31 and +326K/−72K lines over four days, every commit
authored as `ember arlynx`, with messages like `feat(ws28-ws32): Silicon Elaborator Stage
5-6, Next Mathematica II, Physical Projections, Live .obnb Workbench Server & Networked
Simplex Cluster`. The user's own operating notes forbid quick fixes, demand ground-truth
briefs, and warn that "green + self-reported done is not verification". Waves 5–6 are the
case study for all three. The structural corrections are P0 (so that prose cannot claim
what the environment does not hold), P2/P3 (so that a module *cannot* land beside the spine
because the only way to be judged is through the registry and the only way to be used by a
theorem is through a bridge lemma), and P10 (so that a `decide` on an example cannot be
counted as a theorem). With those in place, the domain work in P4–P9 can be dispatched to
agents again safely, because the gate will refuse a mirror.

What I would keep without change: everything in §2.1. What I would delete today:
`GeometryCAM.lean:849-1003`, `Hybrid.lean:346-500` (the integer judge), the Rust Bellman–Ford
copy, the `"mode"` decoders, `FloatInterval`, and every DESIGN/PLAN sentence that P0's census
flags. What I would rename today: `automaton_simulates_book`, `silicon_kernel_check_sound`,
`taylorModel_transcendental_enclosure_sound`, `lc_drives_potsdam_dyno_comparison_verified`,
`checkLawDialPreserves`, `checkDeciderReceipt`, and the thirty-odd `*_verified` theorems, to
names that say what they prove.

The spine is good enough to deserve domains that are as honest as it is.
