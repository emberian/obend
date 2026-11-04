# Gemini swarm handoff, 2026-11-03 (suspended 01:25)

Written by Claude from the Antigravity record: `~/.gemini/antigravity-cli/{history.jsonl, conversation_summaries.db, conversations/<id>.db, brain/<id>/.system_generated/tasks/*.log}`, the brain plans under `brain/57348b27-…/`, the working tree at HEAD `07c04c1`, and read-only looks at bb2. Lane ids below are Antigravity conversation ids (first 8 hex); each lane is a thin dispatcher (depth 1, ~6 steps) plus one or two workers (depth 2). Times are Mac local (PST); bb2 logs are UTC.

Note: review/ is in `.gitignore` (line 46), so this file, `review/DECISIONS-LEDGER.md` and `review/DECISIONS-20261031.md` (both written by lane S-2) are not tracked.

## 1. What was running: Wave 5, not Wave 4

The roadmap being executed at suspension was **not** `wave4_grounded_northstar_roadmap.md`. That wave ran 16:18-00:12 and is mostly in HEAD. After ember's 22:58 turn, the root:

1. wrote `brain/…/expert_sus_audit_suite.md` (23:15): six "sitting next to the veteran" chairs (FPGA/RTL, kernel/PL, validated numerics, CAD/CAM, BFT/crypto/markets, runtime/FFI/GUI), plus a seventh founding-lineage chair;
2. ran seven read-only `DomainVeteranAuditor` chairs, 23:15-23:32 (`483ee818` C1, `b0b172ff` C2, `56d99a07` C3, `2d11da6a` C4, `ff105d1c` C5, `07bf5468` C6, `b86d7dfd` C7). All finished.
3. synthesized them into `brain/…/whole_system_synthesis_plan.md` (23:36): 80+ findings, plus an 8-lane "Wave 5 Synthesis" remediation plan (S-1 … S-8, §3 of that file);
4. launched S-1 … S-8 between 23:37 and 00:11. All eight were running at 01:25. The root's last status (step 3422, about 01:22) says all eight were "actively executing… zero stalled". Only S-2's first worker had reported.

So the "expert sus" suite ember asked for at 22:58 **was** executed by Gemini as chairs C1-C7. The Claude panel now doing expert reviews duplicates that, unless it is meant as an independent read. The chairs' findings live only in `whole_system_synthesis_plan.md` §2 (the chair transcripts are in the conversation dbs above).

### 1a. Wave 4 lanes (for completeness; launched 16:18, 4C at 17:33)

| lane | dispatcher → workers | last state |
|---|---|---|
| WS-4A-1 | `01e64124` → `8e2dffae`, `bdff63d2` | done before 17:59 checkpoint; in HEAD |
| WS-4A-2 (AutoCert) | `547ef5be` → `8590af8f` (reported done), `7f4a5eaa` (reviewer) | `7f4a5eaa` **never reported**. Last words (≈00:12): "Running `lake build` and `AutoCertTest.lean` on `bb2` (`task-222`); waiting for completion." The task-222 log reached `[229/230] Built Obend.Elab.Workbook`, and the test never ran. Its files were then taken over by S-3, S-5 and S-2. |
| WS-4A-3 (Zone-4 FSM) | `122363f4` → `a5cf9f00`, `eb15c556` | `eb15c556` reported done 21:13 ("All 13 functional/soundness/RTL defects … fixed and verified (`0 sorryAx` on `bb2` + Verilator 5.050 …)"). Its files were then reworked by S-5 and S-3. |
| WS-4A-4 (HAL) | `61b0c3fa` → `6654077d`, `bbe08612` | done before checkpoint |
| WS-4B-1 (#silicon_check) | `ec6d3218` → `7d9100a3`, `a4d82d04` | done before checkpoint |
| WS-4B-2 (obend-risc, zk-ntt) | `2085951c` → `afa53cbd`, `85fc7ebd` | `85fc7ebd` **never reported**. It was resumed after quota ("ensure `z3 -smt2 zk_ntt_lec.smt2` completes `unsat` in `< 2s`") and died at ≈00:12 on an API error, mid-edit of `Apps/ZkNtt.lean` (last action: "Restore f before a in findZkSelfGetCtx and use fuel 4096", then a `lake env lean Obend/Apps/ZkNtt.lean` on the Mac). |
| WS-4B-3 (foc-hil, sdr-ft8) | `cc1f2fe0` → `716b5d30`, `e4685f5c` | `e4685f5c` reported done 21:17 (sdr_ft8_lec.smt2 "unsat in 1.34s") |
| WS-4B-4 (fidget-cam, drex, QPM) | `b88da603` → `3e2c1c0f`, `696921df` | `696921df` reported done 23:01: "All 3 flagships … elaborate cleanly through unmodified `Obend.Spec.FrontEnd` + `obend` CLI … pass Verilator + Z3 QF_BV LEC" |
| WS-4C-1 (obend-node cluster) | `08548ec0` → `a5996c13`, `d7136960` | `d7136960` reported done 23:43: "All 25 unit tests and 2 integration tests in `obend-node` … passed … on `bb2:~/obend`" |
| WS-4C-2 (GUI telemetry/PIDE) | `1b08fcd4` → `5a9a2d77`, `16f7fcd5` | `16f7fcd5` reported done 00:03: "All 31 unit/CLI/HTTP integration tests in `crates/obend-gui` pass … 7 headless Chrome … PNG screenshots … visually inspected" |

### 1b. Wave 5 lanes (the suspended wave)

Every S-lane was told to sync its own files into **the shared checkout `bb2:~/obend`** (rsync, no `--delete`) and build there. That is what stalled the wave. S-1's in-progress `Core/Code.lean` and `Leaf/Specialize.lean` were red on bb2, and every lane downstream of Core or Leaf (S-4, S-5, S-7) spent its last half hour on builds that failed in someone else's file. S-5 even hand-compiled HEAD's `Specialize.lean` into a stray `.olean` on bb2 to get past it.

| lane | ids | owned files (from its brief) | last state, own words where recoverable |
|---|---|---|---|
| **S-1** Core4 purification, Equiv, Leaf | `f04a9486` → `21bb23bb` (297 steps) | Core/{Term,Check,Code,Nominal,Bidirectional,MachineFast}, Core/Proofs/*, Spec/Elaborate, Equiv/{Behaviour,Quote,Cost}, Leaf/{Emit,Specialize,Futamura,BendTT}, stdlib/core/Word64.obend | **Mid-flight, red.** Last words: "Synced Specialize.lean, Futamura.lean, and BendTT.lean to `bb2` and launched the `Obend.Leaf` build." That build (task-296.log, 01:25) fails: `Specialize.lean:791:64 Tactic rfl failed … termRedexWeight (Term.rename x (Term.bound i))` (×4) and `:913:4 omega could not prove the goal`. S-7's 01:23 log also shows `BendTT` failing `emitBendNetToC_wf`. Design note: it did **not** revert the 8 bit-level primitives (the plan said "Revert `Core.Term.Primitive` to the 10 pure mathematical primitives"). Its brief told it to keep them for downstream compatibility, so it added `isPureCore4`/`Word64Prim` classification on top. "Core4 does not grow" is still violated. That is ember's call. |
| **S-2** lineage, garden, G5 HyperLaw, census | `2331d1a4` → `95d292cc` (done), `78401c36` (reviewer, 42 steps) | the 6 root docs, review/DECISIONS-LEDGER.md, Doc/{Section,Render,Structured}, Vault/{Store,Cli}, Journal/Journal, Run/HyperLaw (new), Run.lean, Census, Tactic/DocsCensus, Main | `95d292cc` **reported done** at 01:20: "All owned modules (`Obend.Run.HyperLaw`, `Obend.Run`, `Obend.Doc.Section`, `Obend.Doc.Render`, `Obend.Doc.Structured`, `Obend.Vault.Page`, `Obend.Vault.Store`, `Obend.Vault.Cli`, `Journal.Journal`, and `Obend.Tactic.DocsCensus`) compiled and passed their `#tooth` and `#check_docs_census` checks on `bb2` with `0 sorryAx`, though full `Obend.Census` and `obend` executable linking await concurrent Wave-5 sibling lanes…". It also edited `Vault/Page.lean`, which is outside its list. The reviewer `78401c36` had just started `lake build Obend.Census obend` on bb2 (one of the three ssh). It rewrote AMBITION.md (+84 −117), restoring "What we hold to" and "What this is not" in a four-realm framing. |
| **S-3** Contract judge, LCNF/LeanKernel, AutoCert, Workbook | `4b30034f` → `b1a9a738` (453 steps) | Law/Contract, Logic/Obligation, Judge.lean, Judge/Class, Elab/{AutoCert,Workbook}, Lower/{LCNF,LeanKernel,Inductive,Fragment}, tests/metasystem/AutoCertTest | **Mid-flight, never built.** Its 9 files are the only dirty files whose bb2 copy differs from the Mac copy, so it had not synced yet. Its own next step: "Finish `lean/Obend/Lower/LeanKernel.lean` (lines 866–2421): Add `@[expose]` …", then update AutoCertTest, then sync and verify. |
| **S-4** validated numerics, multiphysics | `379e5f08` → `066e2d38` (542 steps) | Analysis/{RealAnalysis,TaylorModel,Flowpipe,Hybrid,SosLyapunov,Groebner,QuantumWalk}, Judge/RealAnalysis, Hardware/{Physics,FluidThermal,Photonics,RF,Analog,DigitalTwin,PCB,QuantumMatter} | **Mid-flight.** Analysis files and RF edited. FluidThermal, Photonics, Physics, Analog, PCB and QuantumMatter were **not yet touched** (none is dirty). Its last bb2 build (task-499/506) failed upstream in S-1's `Core/Code.lean:754 Not a definitional equality … primitiveRules`. Its final `lake build Obend.Hardware.RF` is one of the three ssh. |
| **S-5** silicon fabric, macros, LEC, STA, AWS F2 | `db6a2e7c` → `9b496be8` (598 steps) | Lower/{ExprCAM,SiliconElabFabric}, Tactic/SiliconElab, Hardware/{Types,HDL,Compiler,Synth,Retiming,PlaceRoute,Silicon,TapeoutPipeline,WaferSpace,Judge,VerilateRunner,ReductionMachine}, hardware/sim, hardware/aws-f2, crates/obend-fpga-hal, apps/silicon-kernel-verilator, Apps/SiliconKernelVerilator | **Mid-flight, red.** Compaction summary: HDL, Compiler, Synth, Retiming, Silicon and WaferSpace "compiled cleanly on bb2". `verilator --lint-only -Wall` was clean on both .sv files and `verify_silicon_kernel.sh` PASSED (on the Mac). `cargo test -p obend-fpga-hal` gave 6 passed. Its last build (task-585, 01:24): **`TapeoutPipeline.lean:304 'numVertices' is not a field of structure SyncGraph`** … `:1265 decide failed`. Judge, ExprCAM, SiliconElabFabric, SiliconElab and SiliconKernelVerilator were blocked by the missing `Specialize.olean`. |
| **S-6** OpenUSD, CNC, flagship co-processors | `1bfba8d1` → `e34f39b8` (479 steps) | Hardware/OpenUSD, hardware/rust-ffi, stdlib/physical, tests/obend-source/world/physical, Apps/{ObendRisc,ZkNtt,FocHil,SdrFt8,FidgetCam,QuantumPhotonicMatter,UserspacePhysical}, apps/{obend-risc,zk-ntt,foc-hil,sdr-ft8,fidget-cam,quantum-photonic-matter} | **Mid-flight.** Done: OpenUSD, Cnc5AxisMill, fidget-cam .obend/.sv/.tb/.smt2, FidgetCam.lean (−359 +173) and rust-ffi. It also edited `Hardware/UserspacePhysical.lean`, which is outside its list (its brief named `Apps/UserspacePhysical`). Its own next step: "Fix the 2 minor issues in `OpenUSD.lean` … verify `OpenUSD` + `UserspacePhysical` on `bb2`". It ran `verify_fidget_cam.sh` on bb2: obend check accepted (result 6704), then "`verilator: command not found`". When suspended it was reading `Apps/ObendRisc.lean`, about to rework obend-risc, zk-ntt, foc-hil and sdr-ft8. Those were not started. |
| **S-7** BFT, sandbox, Vault, DReX | `276f23ae` → `cd421d17` (674 steps) | crates/obend-node, crates/obend-sandbox, Consensus/{Finality,SovereignFinality,Epistemic,Simplex}, Ledger/Seat, Vault/{Affordance,Projection,Rehydration,Carry,Hyperedge,SovereignEngine,DragonsExchange,Escrow}, Judge/Clearing, Lower/PolicyToGrain, Apps/SovereignDrex, apps/sovereign-drex | **Mid-flight, Rust green, Lean unverified.** task-659 (01:22) gave `cargo test -p obend-sandbox -p obend-node` with 28+2+17+5 passed and 0 failed. task-665 (01:23) was the Lean build, blocked at `Obend.Leaf.Specialize` (S-1). Its own remaining step was the sovereign-drex .obend offer-safety functions, `SovereignDrex.lean`, and portable verilator/z3 paths in `verify_sovereign_drex.sh`. Those files are dirty (+7 each), so it had started them. |
| **S-8** C-FFI shared lib, PIDE GUI | `35796ac1` → `4c50cab1` (505 steps) | lean/lakefile.toml, lean/c/obend_bridge.c, FFI/Bridge, crates/obend-ffi, crates/obend-gui | **Mid-flight, 2 red tests.** task-494 (01:23): `workbench_server_test` 13 passed, **2 failed** (`…revoke_freeze_and_noninterference`, `test_s8_deliverable_4_viewport_xml_escaping_no_nested_svg_and_cnc_xy_toolpath`). Its own next step: "Fix the 2 remaining test items", then re-render the headless Chrome PNGs and inspect them. `Bridge.lean` now gates on `t.contains "sorry" \|\| t.contains "admit" …`, which is a prose-scanning gate of the kind the plan set out to delete. |

### 1c. The three bb2 builds

`pgrep -fl lake` on bb2 at 09:36 UTC returned nothing. The remote `lake` processes have exited, and their four `sshd-session: build@notty` sessions (09:25 UTC) are idle. The three `ssh bb2 …` on the Mac (pids 46023, 46198, 46204, started 01:24:47-01:25:17) are still there. Most likely they are blocked writing output to the suspended harness's pipes. Their output was never written to a file, so here is what is known:

- `lake build Obend.Leaf.Specialize Obend.Leaf.Futamura Obend.Leaf.BendTT` (S-1): its output is task-296.log (`brain/21bb23bb-…/.system_generated/tasks/`). **Failed**, `Specialize.lean:791` rfl ×4 and `:913` omega. No `Specialize.olean` exists on bb2.
- `lake build Obend.Hardware.RF` (S-4): not logged. `Hardware/RF.olean` does not exist on bb2 and `RF.trace` is from 11-02 10:35 UTC, so the build produced nothing. The likely cause is the S-1 upstream failure, the same as S-4's previous attempt.
- `lake build Obend.Census obend` (S-2 reviewer): not logged. `Census.olean` on bb2 is from 11-02 20:19 UTC, older than the rsynced `Census.lean`. Not built. Census imports every module, so it cannot go green until S-1, S-3 and S-5 are green.

All three are moot. Leave them to die with the harness.

State of `bb2:~/obend` itself: git HEAD `8f9f822` (two commits behind the Mac), 249 dirty files, the Wave 5 working copies rsynced over it, and a hand-made `Specialize.olean`/traces from S-5's workaround. It is a lane scratch tree and cannot verify anything. Do not build commits there. Do not seed another tree from its `.lake` either. Lanes wrote `.olean`/`.c` files there by hand (`lean … -o … -c`) outside lake's traces. A HEAD export seeded with a copy of that `.lake` built `Obend.Apps.QuantumPhotonicMatter`, then failed to link `obend` with `undefined symbol: l_Obend_Hardware_HDL_instDecidableEqRtlExpr_decEq` (`ReductionMachine.c.o` compiled against a different `HDL`).

## 2. The 150 dirty files, by lane

Method: last mtime against lane windows, `TargetFile` edit calls in each worker's db, the ownership lists in each brief, and the diffs. 141 of the 150 are byte-identical to `bb2:~/obend`. The 9 that differ are S-3's 8 files plus `Apps/ZkNtt.lean`.

**A. Wave 4, reported done, untouched by Wave 5 (separable)**
- WS-4B-4 / QPM (`696921df`): `apps/quantum-photonic-matter/{ClementsKrawtchoukArray,MajoranaTetronSyndromes,QuantumPhotonicTop,ThermoOpticCrosstalkComp}.obend`, `package.json` (new), `verilator/{quantum_photonic_coproc_top.sv,quantum_photonic_lec.smt2,quantum_photonic_tb.cpp,verify_quantum_photonic.sh}`, `lean/Obend/Apps/QuantumPhotonicMatter.lean`. Internally consistent: package.json uses sealed `./X.obend` imports, laws only in the entry module, emitted SV without a hand-written header.
- WS-4B-3 (`e4685f5c`): `apps/sdr-ft8/verilator/sdr_ft8_lec.smt2`.
- `Cargo.lock` (+2): catches up to HEAD's `obend-gui`/`obend-node` Cargo.toml, which already depend on `obend-fpga-hal`.

**B. Wave 4, never reported (half-written)**
- WS-4B-2 reviewer (`85fc7ebd`): `apps/zk-ntt/{GoldilocksField,NttButterflyRadix2,SumcheckRoundPoly,ZkNttSumcheckTop}.obend`, `apps/zk-ntt/verilator/{zk_ntt_coproc.sv,verify_zk_ntt.sh,zk_ntt_tb.cpp,zk_ntt_lec.smt2}`, `apps/obend-risc/ComposedRiscCpu.obend`, `lean/Obend/Apps/{ObendRisc,ZkNtt}.lean`. It died mid-edit of ZkNtt.lean, and the bb2 copy of ZkNtt differs. In Wave 5 these all belong to S-6, which had not reached them.
- WS-4A-2 reviewer (`7f4a5eaa`): `lean/Obend/Spec/FrontEnd.lean`, `lean/tests/metasystem/AutoCertTest.lean` (23:29-23:33). Its other files (Hardware/Judge, Elab/AutoCert, Elab/Workbook, Tactic/DocsCensus) were edited on top by S-5, S-3 and S-2.

**C. Wave 4 done, but Wave 5 edited on top (entangled)**
- WS-4C-1 (`d7136960`) → S-7: `crates/obend-node/src/{judge_witness.rs (new), silicon_bridge.rs}`, `crates/obend-node/tests/sovereign_drex_cluster.rs` (new), then S-7 changed `lib.rs`, `net.rs` and `src/sovereign_drex_cluster.rs` (new). S-7's cargo tests at 01:22 cover the union.
- WS-4C-2 (`16f7fcd5`) → S-8: `crates/obend-gui/src/{fpga.rs,apps.rs}`, `tests/fpga_and_apps_test.rs` (new); `server.rs` holds both lanes' edits.
- WS-4A-3 (`eb15c556`) → S-5/S-3: ExprCAM, ReductionMachine, SiliconElabFabric, LeanKernel, Inductive.
- WS-4B-4 → S-6/S-7: `apps/fidget-cam/*`, `apps/sovereign-drex/*.obend`, `verify_sovereign_drex.sh`, `Apps/{FidgetCam,SovereignDrex}.lean`; `apps/sovereign-drex/verilator/sovereign_drex_batch_top.sv` (18:10, emitted) pairs with the `.obend` S-7 changed at 01:16.

**D. Wave 5, by lane** (all mid-flight except S-2a)
- S-1: `stdlib/core/Word64.obend` (new), `lean/Obend/Core/{Term,Check,Code,Nominal,Bidirectional,MachineFast}.lean`, `Core/Proofs/TickCost.lean`, `Equiv/{Behaviour,Quote,Cost}.lean`, `Leaf/{Specialize,Futamura,BendTT}.lean`. **Red** (Specialize, BendTT).
- S-2: `AMBITION.md`, `PLAN.md`, `README.md`, `METATHEORY.md`, `SILICON-ELABORATOR.md`, `QUALIFICATION-AND-SILICON-LEAN.md`, `lean/Obend/{Census,Main,Run}.lean`, `Run/HyperLaw.lean` (new), `Doc/{Section,Render}.lean`, `Vault/Page.lean`, `Tactic/DocsCensus.lean`, `lean/Journal/Journal.lean`. Reported done. Doc and README changes are small reconciliations (counts 479→480, theorem names), apart from the AMBITION rewrite.
- S-3: `lean/Obend/{Judge,Law/Contract,Logic/Obligation,Elab/AutoCert,Elab/Workbook,Lower/LCNF,Lower/LeanKernel,Lower/Inductive}.lean`. **Unbuilt, unsynced.**
- S-4: `lean/Obend/Analysis/{RealAnalysis,TaylorModel,Flowpipe,Hybrid,SosLyapunov,Groebner,QuantumWalk}.lean`, `Judge/RealAnalysis.lean`, `Hardware/RF.lean`. Half done (6 of the 8 Hardware files untouched).
- S-5: `lean/Obend/Lower/{ExprCAM,SiliconElabFabric}.lean`, `Tactic/SiliconElab.lean`, `Hardware/{HDL,Compiler,Synth,Retiming,Silicon,TapeoutPipeline,WaferSpace,Judge,VerilateRunner,ReductionMachine}.lean`, `hardware/sim/silicon_elab_top.sv`, `hardware/aws-f2/{cl_obend_shell_bridge.sv,synth_cl_obend.tcl}`, `crates/obend-fpga-hal/src/{aws_f2_backend,regs,sim_backend}.rs`, `apps/silicon-kernel-verilator/{verify_silicon_kernel.sh (new), verilator/{Makefile,sim_main.cpp,silicon_elab_top.sv}}`. **Red** (TapeoutPipeline); 5 modules unbuilt.
- S-6: `lean/Obend/Hardware/{OpenUSD,UserspacePhysical}.lean`, `hardware/rust-ffi/{Cargo.toml,src/lib.rs}`, `stdlib/physical/Cnc5AxisMill.obend`, `lean/tests/obend-source/world/physical/{Cnc5AxisMill,LcDrivesStatorUsd}.obend`, `apps/fidget-cam/{4 .obend, verilator/3 files}`, `lean/Obend/Apps/FidgetCam.lean`. Half done.
- S-7: `crates/obend-node/src/{lib,net,sovereign_drex_cluster}.rs`, `crates/obend-sandbox/src/{bwrap,grain}.rs`, `lean/Obend/Consensus/{Finality,SovereignFinality,Epistemic}.lean`, `Ledger/Seat.lean`, `Vault/{Projection,Rehydration,Carry,SovereignEngine,DragonsExchange,Escrow}.lean`, `Judge/Clearing.lean`, `Lower/PolicyToGrain.lean`, `Apps/SovereignDrex.lean`, `apps/sovereign-drex/{4 .obend, verilator/verify_sovereign_drex.sh}`. Rust green, Lean unverified.
- S-8: `lean/lakefile.toml`, `lean/c/obend_bridge.c`, `lean/Obend/FFI/Bridge.lean`, `crates/obend-ffi/{build.rs,src/sys.rs,tests/challenger_cabi_edges.rs,tests/ffi_integration.rs}`, `crates/obend-gui/src/{lib,server,viewport}.rs`, `crates/obend-gui/tests/workbench_server_test.rs` (+430). Two red tests.

Cross-lane couplings to watch:
- S-1 changes Core/Code, Check, Term and Leaf, which everything imports, so nothing downstream can be verified until S-1 is green or set aside.
- S-3 (Workbook is the one importer) and S-6 (`elabImportAppObend` in `Hardware/UserspacePhysical`) were consolidating `#import_obend` toward **two different homes**.

## 3. Queued after this wave, and asks no lane picked up

The synthesis plan ends at the Wave 5 lane table. Its flowchart's last box is "Targeted DeepCoder Remediation Waves". Nothing concrete was queued after S-1 … S-8.

Asks from 11-02 (ember, and the two Claude notes ember relayed) that no lane took:
- **Theorem-hygiene census** (Claude 18:03, item 2): report parameterless `decide`/`rfl`/`native_decide` theorems as examples per directory and move them to tier 2. No lane. S-2 made the docs census resolve names, not this.
- **Measure the one-edit cascade** at ~480 modules and publish the number (Claude 18:03, item 4). The founding build gates ("clean build under two minutes, a Check edit within twenty modules", Claude 23:14) were also not taken. Wave 5 did strip `@[expose] public section` in many files, which bears on this, but nothing measures it.
- **The Verilated .sv must be emitted by the build, with a byte-equality check against the committed file** (Claude 18:03, item 3). S-6 item 3 covers emitting four of the cores from their books, but it had not started them, and no lane owns the byte-equality gate.
- **CBOR, not JSON** for wire formats (ember 11-01 01:56, relayed 23:14). No lane.
- **The GUI promise versus the GUI** (wgpu in AMBITION, an HTTP serde server in the crate). No lane. S-8 deepened the HTTP workbench.
- **The paper** (deleted in 8f8c022, "nothing in its place"). No lane.
- **The README in ember's voice** (17:50-17:53: "that isn't my voice … we can rewrite it pretty much entirely"). Not done. S-2 only reconciled counts and names in Gemini's README.
- **"Core4 does not grow"**: the plan said revert the 8 bit primitives, and S-1's brief said keep them. Nobody asked ember.
- **Stalls on stragglers** (ember 17:30). The Wave 5 layout recreated exactly that: one shared bb2 tree, and every lane waiting on S-1.
- 21:05 "TCM … datapacket routing" and 21:06 "do we have an AST on the chip" were answered in-turn by the root, not as lane work (the turns are in the root db, steps ≈3300).

## 4. Recommended pickup order

1. **Commit now, after a clean-tree check** (no ember decision needed). Group A: QPM (10 files) as one commit, `sdr_ft8_lec.smt2` as one, `Cargo.lock` as one. Verify each against a HEAD checkout on bb2 in a private path, not `~/obend`. QPM: `swarm-build lake build Obend.Apps.QuantumPhotonicMatter`. LECs: z3 `unsat`. Verilator testbenches cannot run on bb2 (no verilator or z3 installed there).
2. **Finish, then commit, per lane, in dependency order.** S-1 first: it is red, and its Core/Leaf edits gate S-3, S-4, S-5 and S-7. Then S-5 (TapeoutPipeline red), S-3 (never built), S-4, S-7 (Lean side), S-6, S-8 (two tests). S-2's Lean files (HyperLaw, Doc, Journal, Page, Run, Main) can be verified against HEAD on their own; `Census`/`DocsCensus` only once the tree is green. Each lane needs its own clean build tree. Do not reuse the shared `bb2:~/obend`.
3. **Revert or redo, since nothing in them is recoverable as-is**: WS-4B-2's reviewer edits (zk-ntt, obend-risc, ObendRisc.lean, ZkNtt.lean). It died mid-edit, never verified, and S-6 owns these next. Better to resume `85fc7ebd`'s task than to keep its partial state blind. WS-4A-2's reviewer (`Spec/FrontEnd.lean`, `AutoCertTest.lean`) is small; fold it into S-3's verification rather than reverting.
4. **Wait for ember**:
   - the AMBITION.md rewrite and any README/PLAN/METATHEORY prose (voice);
   - "Core4 does not grow" against S-1's keep-and-classify;
   - one importer: Workbook (S-3) or UserspacePhysical (S-6);
   - whether the Claude expert panel replaces or reviews Gemini's chairs C1-C7;
   - whether Wave 5 resumes under Gemini at all. If it does, give each lane its own bb2 worktree.

Applied on 11-03: see §5.

## 5. Pickup log
Item 1 is done. All three commits are unsigned (1Password refused).

- `6c0cf5a` Cargo.lock. Checked on bb2 with `cargo metadata --locked --offline`: it fails with HEAD's lock and passes with this one.
- `3a0dc0b` `apps/sdr-ft8/verilator/sdr_ft8_lec.smt2`. z3: unsat in 1.0s.
- `dd865d6` quantum-photonic-matter (10 files). Checked on bb2 in a clean export of `07c04c1` with a fresh `.lake`:
  - `swarm-build lake build Obend.Apps.QuantumPhotonicMatter obend`: 536 jobs, 0 errors, 0 sorry.
  - The `.sv` is byte-identical to `emitModuleSV quantumPhotonicCoprocTopRtlModule`.
  - `obend check`/`run --package` accepted, result 23598.
  - z3: unsat.
  - The Verilator testbench was not run (no verilator on bb2).
  - The commit message states what these checks do not show: the RtlModule is a hand-written Lean wire table, and the `.smt2` is a hand-written miter.

Warm clean tree for the next pickup: `bb2:~/claude-verify-20261103/obend`. It is not a git repo; its content equals `dd865d6`, and its `.lake` was built from scratch. To verify one lane, rsync that lane's files over a copy of it, never over `~/obend`.

Not started: item 2 (S-1 first).

## Adjudications

Each lane records, for the dirty files it owns, whether it kept or reverted them and why.

### language-user lane (2026-11-04), files it owns

- `AMBITION.md` (S-2 rewrite, +201/-): **replaced**. The S-2 text was the four-realm brochure; rewritten in the research frame per ember's 2026-11-04 answer (`review/DECISIONS-20261031.md`), "What this is not" restored from `26f3ce8`, counts out.
- `README.md` (S-2, counts 479→480 and two names): **replaced** by a draft in the same frame (marked as a draft for ember to voice); the counts and the quickstart commands the binary lacks are gone.
- `lean/Obend/Main.lean` (S-2: `packageOfSpec` auto-detects `.obend` files, directories and JSON specs; `--package` optional): **kept**. It is the mechanism that lets `obend check apps/NAME` check the 16 import-using programs; built and run on bb2 (see `review/EXPERT-language-user-20261103.md` §What landed). Added on top: a single file with imports is refused naming `obend check DIR`; `judge`/`admit`/`check DIR` in the usage text.
- `lean/Obend/Doc/Render.lean`, `lean/Obend/Doc/Section.lean` and their pair `lean/Obend/Vault/Page.lean` (S-2: heading transclusion `![[P#Heading]]`, `renderTranscludedAt`, `atomText` for fields and cells): **kept** as a set (Page.lean is not this lane's file but Section.lean's `atomText_eq` in Page.lean does not build without it). Added on top: `[[P|alias]]` display text in `target`.
- `lean/tests/obend-source/world/physical/{Cnc5AxisMill,LcDrivesStatorUsd}.obend` (S-6: mirrors of the `stdlib/physical` versions): **kept**; `run-obend-source.py` passes with them (161/161 preview cohort).
- `crates/obend-gui/src/{apps,fpga,lib,server,viewport}.rs`, `tests/workbench_server_test.rs` (+3,972/-718, S-8 and WS-4C-2), `tests/fpga_and_apps_test.rs` (new): **reverted to HEAD**. On bb2 with the stub FFI the dirty tree failed 5 tests (3 `verified` assertions on the Lean bridge, the S-8 membranes and viewport deliverables); HEAD with this lane's `main.rs` passes all GUI targets (`cargo test -p obend-gui`: 7+6+1+10 ok). The diff is saved as `obend-gui-S8.patch` with the new test file beside it in this lane's scratchpad and is byte-identical to `bb2:~/obend` per §2; nothing in it was consumed by a workflow and the council's §1.6 finding about the bridge stands.

## Adjudications

### fpga-silicon lane (2026-11-04)

Base for the lane build is HEAD `85e6fd5` (bb2 `~/claude-verify-20261103/obend`); a "keep" below means the dirty
file was carried into the lane and built, a "revert" means `git checkout HEAD --` on the Mac. Every reverted
file's dirty content survives byte-identical in `bb2:~/obend` (handoff §2), so nothing is lost by reverting.

| file | call | why |
|---|---|---|
| `lean/Obend/Hardware/HDL.lean` | keep, then extended | S-5's transitive-wire CDC (`checkRegCdcWithWires`, `cdcSafe_no_unsynchronized_crossing_withWires`) is a real fix; the lane added port widths, per-domain clocks and the two-flop gate on top |
| `lean/Obend/Hardware/Judge.lean` | revert, then patched | S-5's +311 (reset-kind/extra-port wire format) was unbuilt; HEAD needed only the `OutputPort` constructor updates for the new `width` field |
| `lean/Obend/Hardware/VerilateRunner.lean` | revert, then rewritten | the dirty +659 was the second `silicon_elab_top` string literal; both literals are gone now |
| `lean/Obend/Lower/SiliconElabFabric.lean` | revert, then one-line fix | the dirty +1290 (`hwCamIsDefEq`, projection telescopes, `#tooth`) depends on the dirty `Lower/ExprCAM` + `LeanKernel` (S-3, not this lane); HEAD did not build either (`let .constEntry … ← … ` with no fallback, line 375) and is fixed with `| none` |
| `lean/Obend/Hardware/{Compiler,Synth,Retiming,Silicon,ReductionMachine,WaferSpace,TapeoutPipeline}.lean` | revert | S-5 export-attribute shuffles and the derive-LVS-from-BELs additions; the latter is the "LVS passes by construction" pattern the expert report names (§3.9); `Silicon.lean`'s DSP C-register fix looks right and should be re-applied by whoever next touches it |
| `lean/Obend/Hardware/RF.lean` | revert | S-4 half-done; not on the bitstream path |
| `lean/Obend/Hardware/OpenUSD.lean` | revert | S-6 half-done; now the CAD lane's file (panel diff §2), left at HEAD for them |
| `lean/Obend/Hardware/UserspacePhysical.lean` | revert | S-6's `elabImportAppObend` consolidates `#import_obend` into the wrong home; ember chose `Elab/Workbook` |
| `hardware/sim/silicon_elab_top.sv`, `hardware/aws-f2/*` | deleted | duplicates / unbuildable interface (`hardware/README.md`) |
| `hardware/rust-ffi/{Cargo.toml,src/lib.rs}` | keep, unverified | S-6 octree fix + `[workspace]`; physics lane's area, not built by this lane |
| `crates/obend-fpga-hal/src/{aws_f2_backend,regs,sim_backend}.rs` | superseded | F2 backend removed; `SimBackend` renamed `MockBackend` and documented as a software model |
| `apps/zk-ntt/verilator/{zk_ntt_coproc.sv,zk_ntt_tb.cpp,zk_ntt_lec.smt2,verify_zk_ntt.sh}` | keep, relabelled | WS-4B-2's canonicalisation (`gl_canon`) is an improvement; the `.sv` is now headed "hand-written reference RTL" and the `.smt2` "hand-written property check" |
| `apps/sovereign-drex/verilator/sovereign_drex_batch_top.sv` | keep, pending byte gate | emitted-style replacement of a hand-written file; `verify_sovereign_drex.sh` now compares it with `obend-emit-sv drex` |
| `apps/sovereign-drex/verilator/verify_sovereign_drex.sh` | keep | binary path fix |
| `apps/fidget-cam/verilator/{fidget_impeller_voxel_cam.sv,fidget_voxel_tb.cpp,fidget_cam_lec.smt2}` | revert | paired with the dirty `Apps/FidgetCam.lean` (CAD lane / Apps gate); the byte gate re-syncs the `.sv` when that lands |
| `apps/silicon-kernel-verilator/verilator/{silicon_elab_top.sv,sim_main.cpp}` | superseded | the `.sv` is now the emitter's text; the harness reads a Lean-generated golden |
| `apps/silicon-kernel-verilator/verilator/Makefile` | keep | portable verilator lookup |
| `SILICON-ELABORATOR.md`, `QUALIFICATION-AND-SILICON-LEAN.md` | keep, then rewritten | S-2's name fixes, then §1.4, §1.5, §2.2, §3 rewritten to describe what exists |
| `lean/tests/m5/{HardwareProjectionTest,Milestone5Challenger1StressTest}.lean` | not dirty; one-token edits | `OutputPort` gained a defaulted `width`; `⟨name, expr⟩` became `{ name, expr }` |

## Adjudications (compiler-runtime lane, 2026-11-04)

Dirty files this lane owns or was asked to read, from Gemini's S-1 and S-3 lanes; each call is
keep or revert against `85e6fd5`, with the reason. "Revert" means `git checkout HEAD -- <file>`
in the shared tree; nothing of Gemini's was kept elsewhere.

| file | Gemini's change | call | why |
|---|---|---|---|
| `lean/Obend/Leaf/BendTT.lean` | `@[expose]` per def; +400 lines: affine reducer, interaction-net list emitter, C99 string emitter | **deleted** (whole module) | Bend is retired (decision 2026-11-04); the emitters produced text nothing could run (`EXPERT-compiler-runtime` §2.2); S-7's log had it red at `emitBendNetToC_wf` |
| `lean/Obend/Leaf/Futamura.lean` | `@[expose]` per def; +300 lines: `termRedexWeight` monotonicity (§12) | **replaced** | rebuilt from HEAD as `Obend/Leaf/Static.lean` without the self-application sections; the weight section depended on Gemini's red `Specialize.lean` additions and measured a syntactic rank, not a cost |
| `lean/Obend/Leaf/Specialize.lean` | `@[expose]` per def; +294 lines `termRedexWeight`, `checkSpecCostMonotone` | **revert** | red on bb2 at `:791` (rfl ×4) and `:913` (omega) in S-1's own last build; the measure is a `max` of constructor ranks and cannot see the duplication the folder causes, so it is not a cost gate. Header rewritten afterwards (pins are whole-term equality decided before the run) |
| `lean/Obend/Core/Code.lean` | `pureCore4PrimitiveRules`/`word64TargetPrimitiveRules` split, `checkerEdition` bumped to 2026-11-03 C3, primitive clause in `version_fixes_codecs`, dropped `import all Core.Check` | **revert** | the split was the premise of the "revert to 10 primitives" plan Ember declined; bumping the checker edition changes every quotation's `encodingVersion` for a partition nothing consumes |
| `lean/Obend/Core/Term.lean` | +162: `Primitive.isPureCore4`, `Word64Prim`, `purePrimitiveResult`, `Term.isPureCore4`, `add64`…`qmul32Nonneg`, `core4_pure_primitives_count = 10` | **revert** | same premise; a second primitive evaluator beside `primitiveResult` is "two of everything" in the one file that must not grow; the counting theorems are fixtures. Primitives stay as decided |
| `lean/Obend/Core/Nominal.lean` | +98: re-exports of the Term.lean section under a `Word64` kind | **revert** | depends on the Term.lean section |
| `lean/Obend/Core/Check.lean`, `Bidirectional.lean`, `MachineFast.lean` | `@[expose] public section` → `public section` with per-def `@[expose]`; `import all Core.Check` dropped | **revert** | no theorem content; unbuilt in combination with anything; the exposure set is what `module` consumers and the `#print axioms` guards in `MachineFast` were tuned against. Worth doing deliberately later, one file per build |
| `lean/Obend/Core/Proofs/TickCost.lean` | `cost_indexed_completeness` renamed `fragment_cost_indexed_completeness` with a scope note; `GeneralCostIndexedCompleteness` stated as an open `Prop`; alias kept | **keep** | honest and correct: the bound is on `InFragment` only and the general statement is open (`EXPERT-compiler-runtime` §2.5). Built green in `~/lane-compiler` |
| `lean/Obend/Equiv/Behaviour.lean` | `REquiv` (`≈r`) named as the reflective equivalence, `BEquiv` an `abbrev` of it; per-def `@[expose]` | **keep** | `Quote.lean` already said Behaviour's `≈b` is the reflective one; the name now agrees. Built green with every importer (Leaf, Lower, Teeth) |
| `lean/Obend/Equiv/Quote.lean` | `PureBEquiv := Observed .b`, `requiv_implies_pureBEquiv`, strictness example; per-def `@[expose]` | **keep** | the ladder stated with its own names; built green |
| `lean/Obend/Equiv/Cost.lean` | per-def `@[expose]` only | **keep** | built green |
| `lean/Obend/Lower/LCNF.lean` | +250: `evalLcnfLetValue`/`evalLcnfCode` scalar interpreter, `isClosedDecisionCode`, `evalLcnfCode_simulates_core4`, three `sample*_runs_42` theorems | **revert** | red on bb2: `:778` `induction` on the nested inductive `LcnfCode`, `:853` max recursion. Also fixture theorems of the kind the 2026-11-04 decision stops. **Consequence for the `Lower/Inductive.lean` owner**: that file's dirty `export` list (`:1035-1046`) names these LCNF symbols and will not build against HEAD LCNF; revert those lines or the whole file |
| `lean/Obend/Tactic/SiliconElab.lean` | S-5's `gateDecl` removal and telemetry (+125/−63) | **keep, then fixed** | kept as the base; on top: `#silicon_check` refuses outside the Zone-4 fragment, the fixed `scaleAdd 10` probe is gone, `selfHostTypePreservationInfo` is `selfHostIdentityProofInfo` (it was `λ P h. h`) |
| `METATHEORY.md` | header counts bumped (480 modules, 66,000+, 120+ teeth), §2.6 and §2.7 prose | **keep header untouched, rows rewritten** | the Leaf/Lower rows are this lane's and were rewritten; the headline counts are the frame lane's and the 2026-11-04 decision says they go |

Not adjudicated here (not this lane's): `lean/Obend/Lower/{ExprCAM,Inductive,LeanKernel,PolicyToGrain,SiliconElabFabric}.lean`, `lean/Obend/Spec/FrontEnd.lean`, `lean/tests/metasystem/AutoCertTest.lean`, `lean/Obend/Hardware/UserspacePhysical.lean`. `UserspacePhysical`, `SiliconElabFabric` and `MetaUnify` receive mechanical edits from this lane's cross-lane patch (below) only where they named deleted Leaf symbols.

## Adjudications (lean-proof-engineering lane, 2026-11-04)

Base is HEAD `85e6fd5`. "Revert" means the dirty content was not carried into the commit; it survives
byte-identical in `bb2:~/obend` (§2) and, where noted, in this lane's scratchpad.

| file | Gemini's change | call | why |
|---|---|---|---|
| `lean/Obend/Elab/Workbook.lean` | S-3: contract check moved after the defs (`checkContractIsarCertWithBook`), full `workbookSourceDigest`, blanket `@[expose]` narrowed to per-def | **revert, then patched from HEAD** | `checkContractIsarCertWithBook` lives only in the dirty `Spec/FrontEnd.lean` (WS-4A-2, not landed); the first bb2 build of the importer failed on it. The digest completion and the exposure narrowing are worth re-applying deliberately once FrontEnd lands; a copy of S-3's patched file is at this lane's scratchpad `dirty/Workbook-S3-patched.lean` |
| `lean/Obend/Hardware/UserspacePhysical.lean` | S-6: `elabImportAppObend`, the app elaborator in the wrong home | **revert** (already done by the fpga lane), then the four `#import_obend` and two `#import_obend_source` calls re-pointed at `Obend.Elab.Workbook` | ember's decision: Workbook is the one importer |
| `lean/Obend/Apps/{FidgetCam,SovereignDrex}.lean` | S-6 / S-7 app content on top of their importer copies | **committed from HEAD + importer change**; the dirty content stays in the working tree with the same importer change applied, for the CAD/physics lanes that own the files | the commit must be consistent with the `.obend` files HEAD has; the lanes' `.obend` edits are theirs to land |
| `lean/Obend/Apps/{ObendRisc,ZkNtt}.lean` | WS-4B-2 reviewer, died mid-edit (SoC snapshots, Goldilocks specs, `topologicalSort*Book`) | **committed from HEAD + importer change**; dirty content left in the working tree with the importer change applied | handoff §4.3 says these are unrecoverable as-is; the fpga lane owns them next |
| `lean/Obend/Census.lean` | S-2: Apps/Teeth imports, tier-2 glob parsing, `#docs_census` | **kept**, then the `run_cmd` rewritten | the per-directory classification replaces the verdict counts (decision 2026-11-04) |
| `lean/Obend/Tactic/DocsCensus.lean` | S-2: `Slot`/`Intention` instantiation over `DocEnvWorld`, `review/*.md` paths | **kept**, then extended | bare identifiers are now supports; the governed set is the root documents (the Gemini `review/DECISIONS-LEDGER.md` is out: not a source of truth per the record note) |
| `lean/lakefile.toml` | S-8: `Obend.Apps.*` moved to the `Teeth` library, `defaultFacets` | **kept**, then the `Tests` library added | exactly "Apps leaves tier 1"; `tests/{metasystem,silicon_elab,rehydration}` get a target |
| `lean/tests/metasystem/AutoCertTest.lean` | WS-4A-2 reviewer: cross-term SOS, Groebner forged-basis refusal, closed-book RTL synth checks | **kept** | first elaborated by the `Tests` target on bb2 (see the lane report for the result) |
| `PLAN.md`, `METATHEORY.md` | S-2: counts bumped, names reconciled | **kept as base**; every count line removed | decision 2026-11-04 |
| `lean/tests/obend-source/world/physical/*.obend` | S-6 mirrors | adjudicated by the language-user lane (kept) | — |
