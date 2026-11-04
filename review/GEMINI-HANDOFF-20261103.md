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
| `lean/Obend/Lower/LeanKernel.lean` | +218/−83: per-def `@[expose]`; `KLevel.mkIMax` distributes over `max`, `KLevel.equivComm` (commutative `max`) inside `kernelLevelEq`; `extractCtorArgsWithLevels`; `reduceQuotLift?` requires the kernel's three-argument `Quot.mk`; `.proj` typed through the constructor telescope (`inferProjFieldType?`) and reduced with the `numParams` offset; strict positivity (`checkInductiveStrictPositivity`, `checkCtorStrictPositivity`) in `kernelCheckDecl` | **keep** (2026-11-04 evening, on the coordinator's routing) | the kernel brought closer to Lean's, no new fixtures; red once at `kernelWhnf_quot_lift_sound`, whose first conjunct asserted the erased `Quot.mk a` spine reduces: rewritten to say it is not a redex; and 52 definitions after line 860 (`stdKernelEnv`, the fixtures, the lowered-kernel `LExpr`s) lacked the per-def `@[expose]`, so every `rfl` in `SiliconKernel` failed: exposed. Built on bb2 with its tier-1 reverse closure, `SiliconKernelVerilator` and `obend`; four `silicon_elab` tests elaborate |
| `lean/Obend/Tactic/SiliconElab.lean` | S-5's `gateDecl` removal and telemetry (+125/−63) | **keep, then fixed** | kept as the base; on top: `#silicon_check` refuses outside the Zone-4 fragment, the fixed `scaleAdd 10` probe is gone, `selfHostTypePreservationInfo` is `selfHostIdentityProofInfo` (it was `λ P h. h`) |
| `METATHEORY.md` | header counts bumped (480 modules, 66,000+, 120+ teeth), §2.6 and §2.7 prose | **keep header untouched, rows rewritten** | the Leaf/Lower rows are this lane's and were rewritten; the headline counts are the frame lane's and the 2026-11-04 decision says they go |

Not adjudicated here (not this lane's): `lean/Obend/Lower/{ExprCAM,Inductive,PolicyToGrain,SiliconElabFabric}.lean` (`LeanKernel.lean` was routed to this lane later the same day; its row is above. `tests/silicon_elab/SiliconRealismTest.lean` is red at HEAD independently of it: it passes `ctx` as the third argument of `kernelIsDefEqFull`, whose signature has had `ctx` last since `23a7651`), `lean/Obend/Spec/FrontEnd.lean`, `lean/tests/metasystem/AutoCertTest.lean`, `lean/Obend/Hardware/UserspacePhysical.lean`. `UserspacePhysical`, `SiliconElabFabric` and `MetaUnify` receive mechanical edits from this lane's cross-lane patch (below) only where they named deleted Leaf symbols.

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

## Adjudications (distributed-security lane, 2026-11-04)

Base is HEAD `85e6fd5`; built in `bb2:~/lane-security` (HEAD plus this lane's files). "Kept" means the
dirty content is carried into this lane's commits, after the fixes named; "revert" means it is not.
The dirty content survives in `bb2:~/obend` (§2).

| file | Gemini's change | call | why |
|---|---|---|---|
| `lean/Obend/Consensus/{Finality,SovereignFinality}.lean` | S-7: `QuorumBoundFinalityGate` gets `Nodup` signers drawn from a `committee`; two restating theorems | **kept** | builds; a signer list beside the count-based contract, which the report (S4) names as "two of everything"; the signers are still `Nat`s |
| `lean/Obend/Consensus/Epistemic.lean` | S-7: `clearedMatchedVolume`, `computeDualityGap`, `checkClearing` for the race's `isValid`; refined interval certs | **kept** | builds against HEAD's `Judge/Clearing`; makes the race validity call the judge instead of a price range |
| `lean/Obend/Vault/{Projection,Rehydration,Escrow,DragonsExchange}.lean` | S-7: `capMask` in the blinded commitment; `@[expose]` and `cellId` on sturdyrefs; guarded step contracts with real invariants; obligation-backed ring settlement | **kept**, then `Projection`'s two `¬ Collision H` theorems and `Rehydration.chain_tamper_evident` restated up to a collision | they build; the restatements are this lane's brief |
| `lean/Obend/Vault/Carry.lean` | S-7: forever-crown cells cannot be named-dropped; dropped cells revoke their sturdyrefs; `migrate` decoder; ledger decoded from cells | **kept with two fixes**: the destruct proof's last conjunct needed `List.append_assoc`; the `.integer` arms used a `Data` constructor that does not exist at HEAD (S-1's dirty `Core/Data`) and were removed | never built by its lane |
| `lean/Obend/Vault/SovereignEngine.lean` | S-7: `wellFormed_sound` bounded by `maxTokens`; `applyTurnToVaultCells`; balance-bound check in `checkOracleTurnValidAt` | **kept with two fixes** (`compilePolicyToGrainProg_refuses_excess_tokens` opened from `Obend.Lower`; `payload` is not a `VaultCell` field, it is `content`), then the `¬ Collision H` theorem restated | **depends on the dirty `lean/Obend/Lower/PolicyToGrain.lean`** (the lemma and the `h_len` argument), which this lane does not own and did not commit; whoever owns `Lower/` must keep it or these two proofs regress |
| `lean/Obend/Vault/Hyperedge.lean` | clean at HEAD | **extended**: `witnessLeg`, `VaultTurn.ofWitnessLegs`, `checkTurnWitness_sound`, `ofWitnessLegs_witness_clause` | the constructor the Bridge commits through |
| `lean/Obend/FFI/Bridge.lean` | S-8: ground evaluation of claims, membrane affordance query, a char-level prose gate (`checkObligationPropHolds`) in front of `cellWeaveCertCore`, pending proposal from a weave | **kept the claim and membrane work; replaced the receipt/weave half**: `admittedRoots` became `committedRoots` written only by `turnCommitCore`; `verifyReceiptCore` takes a full Merkle frame and opens it; the prose gate and `isValidCertObligation` are deleted; a weave is a judge witness checked by `Obend.Judge.registry`; every commit builds a `VaultTurn` through `ofWitnessLegs` | the panel-diff was right that S-8 added self-admission after the first review (payload admitted on propose, bare root accepted, text gate); all three are gone (`verifyReceiptCore_sound`, `turnProposeCore_committedRoots_unchanged`) |
| `lean/c/obend_bridge.c` | S-8: `pthread_once` global init with thread-local attach, abort on failed module init | **kept**, then `obend_ensure_lean_thread` exported for the Rust pool | the frame lane's segfault diagnosis: Rust called `lean_initialize_thread` before the runtime existed |
| `crates/obend-ffi/{build.rs,src/sys.rs,tests/*}` | S-8: elan fallback for the sysroot; stub session mirroring admitted roots and the prose gate; tests asserting the admitted-root behaviour | **build.rs kept**; **stub rewritten** (committed roots, one-leaf frame check, weave refused: the stub has no registry); **tests rewritten** to the committed-receipt semantics and `tests/receipt_session_binding.rs` added | the stub mirrored the backdoor |
| `crates/obend-node/src/{lib,net,silicon_bridge}.rs`, `src/{judge_witness,sovereign_drex_cluster}.rs` (new), `tests/sovereign_drex_cluster.rs` (new) | WS-4C-1 then S-7: witness registry (Rust reimplementation of four judges), DReX cluster, fast-path acks pinned to a committee, WAL entries for slashing and DPR | **kept**, then this lane's changes on top: `SimulatorKeypair` (was `ValidatorKeypair`), `simulator_seed`, `commit_payload`/`kernel_receipt_check` instead of `propose; commit; verify(x)`, the `Propose`/`FinalizationCertificate`/`apply_finalized_block` chain rules, length-prefixed `VaultTurn::digest`, delegation debits the parent, simulator headers | Rust was green at 01:22; the crate is a simulator by decision |
| `crates/obend-sandbox/src/{bwrap,grain}.rs` | S-7: fail-closed `allow_unsandboxed_fallback`, `is_fallback` in the receipt digest, bounded Seatbelt read set, `EvalCellStep` refuses unauthorized `slot:` reads, `ScanTokens` refuses excess tokens | **kept** | the right direction on every point; the Seatbelt profile is still permissive (`mach-lookup`, `process*`) and the metering values are formulas, recorded in the report (S9), not fixed here |
| `lean/Obend/Judge.lean` | an S-lane: one unified `registry`, with `realAnalysisFormat` whose decoders accept any string, and entries `groundFormat`, `lawProbeFormat` (exist nowhere), `autoSosLyapunovFormat` (dirty `Elab/AutoCert` only), `Obend.Law.Contract.contractCertFormat` (wrong name, dirty `Contract` only), `Obend.Elab.AutoCert.{rtlSynth,hwSynth}Format` (wrong namespace; already in `hardwareFormats`) | **kept the unification; removed those six entries and the real-analysis decoders** | the registry is now the witness seam (`Bridge.sessionJudgeFormats`), so a decoder that reads nothing is a universal witness |
| `lean/Obend/Law/Contract.lean` | S-7 or WS: `checkGoalBoundedSound` over 8 × 8 × 2 samples, `ContractGoalDenote`, a "soundness theorem" restating it, `contractCertFormat`, propositional-term checks | **revert to HEAD**, then on HEAD: the `.byLrat` tier refused outright (`checkContractCert_byLrat_refused`; the default base CNF `[[1],[-1]]` was unsatisfiable alone), `mkGoalBoundLratCnf`/`verifyGoalCnfEncoding` deleted, `checkGoalPropositionalUnsat` documented as a filter | the dirty file never built (eight proof errors at this toolchain) and its "soundness theorem" was the finding; HEAD's version carries no such claim |
| `lean/Obend/Judge/Clearing.lean` | S-7: integer-tick crossing test in `hasCrossingPair` / `priceInCrossingInterval` | **kept**, then `duplicateAccount` refusal, `firstDuplicateAccount?`, `judge_ok_accounts_nodup` | fills are per-account net flow, so one order per account per batch is the condition under which `Order.fill` is an order's fill |
| `lean/Obend/Ledger/Seat.lean` | S-7: `safeAt` sums duplicate asset keys; `safeAt_refuses_duplicate_key_double_count` | **kept** | builds; closes a double-count |
| `apps/sovereign-drex/*.obend`, `verilator/{sovereign_drex_batch_top.sv,verify_sovereign_drex.sh}` | S-7 / WS-4B-4: offer-safety check functions, regenerated top, portable tool paths | **kept** | `obend check --package apps/sovereign-drex/package.json` accepts; `verilator --lint-only` clean |
| `lean/Obend/Run/HyperLaw.lean` (untracked) | S-2 | **kept untracked, not committed by this lane** | imported by `Obend/Run.lean` (S-2's dirty file, the frame/census lane's); it travels with that commit |

Not adjudicated here: `lean/Obend/Lower/PolicyToGrain.lean` (needed by `SovereignEngine`, see above), `lean/Obend/Elab/AutoCert.lean`, `lean/Obend/Core/*`.
- (second round, `48727bb`, `f3b832e`) Files outside this lane's list it edited because the change did not build or hold without them: `lean/Obend/Spec/Proofs/LawCompile.lean` (the `monotone` proof and teeth, first round), `lean/Obend/Spec/{Syntax,FrontEnd,Workspace}.lean` (module laws), `lean/Obend/Vault/{Page,Json,Law}.lean` (dangling measure, tombs, kind doc). None was dirty from a suspended lane except `Vault/Page.lean` (S-2, kept, above).

## Adjudications (physics lane, 2026-11-04)

Method: each dirty file I own was read in full (the expert review was written against the working tree),
diffed against HEAD, rsynced unchanged into a clean copy of `bb2:~/claude-verify-20261103/obend`
(`~/lane-physics`) and built there before any edit of mine; what did not build was repaired or cut, and the
call recorded here.

| file | lane | call | why |
|---|---|---|---|
| `lean/Obend/Analysis/RealAnalysis.lean` | S-4 | **keep** | adds `Interval.add/sub/mul/sqr_mem`, `evalInterval_sound`, three `#tooth`s: the universal interval soundness the council found missing. Built. |
| `lean/Obend/Analysis/TaylorModel.lean` | S-4 | **keep, §5 "arbitrary-order series" cut** | `TaylorModel.Models`, `add/sub/scale/mul_models`, `evalTaylorModelRange_encloses` are real and kept. The series section (`expPartialSum`, `expTailCoeff`, `halfPowRat`, `invFactFrom5`, `powRat_mem_unit`, …, 160 lines) never compiled (`decide` on `Rat`, `grind` on `CanonicalRat.mk` numerals: 8 errors) and the `AnalyticModel` instance depended on it; the instance is now `partialSumAnalyticModel` with polynomial stand-ins, and the header no longer says "verified transcendental". Built. |
| `lean/Obend/Analysis/Flowpipe.lean` | S-4 | **keep** | `picard_step_encloses_trajectory`, `verifyPicardAPriori_encloses`, `evalLieDerivSum_sound` are universal. Built. |
| `lean/Obend/Analysis/Hybrid.lean` | S-4 | **keep, one repair** | `hybridFlowpipe_bad_refused` stated via `Judge.check` had no `Decidable` instance (`:583`); restated via `checkHybridFlowpipe`, which the format's `bad_refused` accepts by defeq. Built. |
| `lean/Obend/Analysis/QuantumWalk.lean` | S-4 | **keep** | `@[expose]` plumbing and the matrix-Taylor section with teeth. Built. |
| `lean/Obend/Analysis/SosLyapunov.lean` | S-4 | **keep, one repair** | `computeSymbolicAlgJacobianDet` used the product of the diagonal partials for ≥3 constraints (panel diff); replaced by a Laplace-expansion determinant (`polyMatrixDet`, `symbolicAlgJacobian`). Built. |
| `lean/Obend/Analysis/Groebner.lean` | S-4 | **keep** | `@[expose]` plumbing. Built. |
| `lean/Obend/Judge/RealAnalysis.lean` | S-4 | **keep** | `insertNormalizedTerm` (monomials normalized before insertion), `Poly.eval` semantics, `sosCheck_sound`. Built. |
| `lean/Obend/Hardware/RF.lean` | S-4 | **keep** | `evalQuadratureImagePower` sums amplitude and phase imbalance in quadrature (the linear sum cancelled for opposite-sign errors). Built. |
| `lean/Obend/Elab/AutoCert.lean` | S-3 (on WS-4A-2) | **keep as base; rewritten where it lied** | S-3's `given`-hypothesis parsing is kept. The `[0,1]` default for unconstrained claim variables, the golden-object substitutions for `none`/`.bool true`, the Taylor and SOS claim extractors (the surface has no transcendental functions or Lyapunov specs) and `rtl-synth` on non-`true` propositions are removed; claim objects are read from the `ClaimObj`'s Core4 body (`claimIntervalObjOf?`, `claimGroebnerQueryOf?`) and the formats carry `bindsClaim`. Built. |
| `lean/Obend/Logic/Obligation.lean` | S-3 | **keep as base; two proofs never compiled** | `obligationWithJudges_sound` (`rfl` for the binding) and `obligationWithJudges_mono` (`rw` into a `match` whose pattern variables shadow `F`/`objStr`) were red in S-3's version; fixed. `externalClaimBound` now takes the `Judge.Format` and defers to `F.bindsClaim` (panel diff A C2-5). The toothed fixture had become an `example`; the `#tooth` needs a name, so it is a `theorem` again with a note. Built. |
| `stdlib/physical/Cnc5AxisMill.obend` | S-6 | **reverted to HEAD** | S-6's change (Abbe sign `+`→`−`, new `commandedAxisUm`) is right, but `lean/Obend/Hardware/UserspacePhysical.lean:690-700` (S-6's, not mine) still `decide`s the old outputs (`10024`, five wires) and goes red with it. The two must land together from the S-6 owner; the language-user lane kept the test mirror `lean/tests/obend-source/world/physical/Cnc5AxisMill.obend`, so the mirror and `stdlib/` now differ until then. |

Not dirty but changed by this lane: `lean/Obend/Judge/Class.lean` gains one defaulted field
(`bindsClaim : Term → Nat → String → Bool := fun _ _ _ => false`) and imports `Obend.Core.Term`; every
existing `Format` compiles unchanged and is "unbound" until it says how its objects state a claim.
`lean/Obend/Teeth/Hardware/SiliconTeeth.lean:503-507` (one tooth retargeted to `evalIpmTorqueTwiceMicroNm`)
and `lean/tests/metasystem/{AutoCertTest,CoupledPhysicalTest,CoupledMultiphysicsTest}.lean` (fixtures
follow the renames and the fail-closed extractor) were edited for the same reason.

## Adjudications (cad-cam lane, 2026-11-04)

Method: each dirty file the lane owns was read against HEAD before any edit; builds in `bb2:~/lane-cad`
(git HEAD of 11-04 plus this lane's files). Report: `review/EXPERT-cad-cam-20261104.md`.

| file | lane | call | why |
|---|---|---|---|
| `apps/fidget-cam/BaseImpellerBody.obend` | S-6 | **reverted, then rewritten** | S-6 added `evalHubBladeFRep = x²+y²+z² + thickness` on `Nat` (not a signed field; no subtraction, so nothing is ever inside) and a sample at `(8,0,4)`. The module is now the hub's parameters (`6db42e8`). |
| `apps/fidget-cam/CoolingChannelOverride.obend` | S-6 | **reverted, then rewritten** | Same pattern (`evalCoolingBoreFRep`, a sum of squares plus the bore radius). Now the bore's parameters and the 2.0 mm minimum wall. |
| `apps/fidget-cam/MountingBossAssembly.obend` | S-6 | **reverted, then rewritten** | `evalTcpmRotaryKinematicsUm = aDeg·offset + cDeg·2 + tape length` is not kinematics. Now the lug's parameters. |
| `apps/fidget-cam/ImpellerPartTop.obend` | S-6 | **reverted, then rewritten** | `evaluateImpeller5AxisPointUm` summed four fields and two angles; the Lipschitz pad changed 72→64 to match a fixture. Now the process parameters; the package entry is `toolOffset`. |
| `lean/Obend/Apps/FidgetCam.lean` | S-6 body, gate import block | **gate's import block kept; S-6 body replaced** | S-6's no-gouge theorem put one tool at the origin against a box 6 mm away; its wall theorem probed two planes at one point and called `computeCertifiedShellWallThicknessUm` with a list the HEAD signature does not take (red). Replaced by `fidget_bore_wall_sound`, `fidget_toolpath_no_gouge`, `fidget_post_rotarySafe` (`6db42e8`). No `local elab "#import_obend"` was present. |
| `stdlib/physical/Cnc5AxisMill.obend` | S-6 | **left to the physics lane's call above** | Not in this lane's brief; the physics lane reverted it. |
| `lean/tests/metasystem/OpenUsdAndSsaTapeTest.lean` | proof-engineering (fixtures→examples) | **kept; §2.3 rewritten** | Its wall section called the deleted probe-point functions; it now tests `checkWall_sound` (`cf3efad`). `:359` is red for a reason outside this lane: `Hardware/Judge.lean`'s `extractNatField_token_boundary_and_decoders_verified` changed its statement. |

Not dirty but changed by this lane: `Hardware/{GeometryCAM,OpenUSD,Kinematics,PCB}.lean` (`cf3efad`,
`5a74100`, `0da8645`), which also carried the proof-engineering lane's fixture→`example` edits, and
`PHYSICAL.md` §2 and §3.1 (`023cdc4`; the physics lane's §4 hunk is left in the tree).
- (third round, `ffb8772` and the laws-over-links commit) Files outside the lane's list it edited because the change did not hold without them: `lean/Obend/Doc/Patch.lean` (`Patch.deletes`/`adds` and the two `apply` theorems the measures rest on), `lean/Obend/Vault/Cli.lean` (the open's report of a repeated refusal). `lean/Obend/Vault/Hyperedge.lean` (security lane) is imported by `Vault/Store.lean` now and not edited; the lane tree builds against HEAD's copy, which lacks the dirty copy's `ofWitnessLegs`, so nothing here depends on the dirty additions.
- (fourth round, `47e6adc`, `bd160a6`) Outside the lane's list: `lean/Obend/Elab/Workbook.lean` (one line: the `ToExpr LawRef` case for `labelConst`); `lean/Obend/Spec/Proofs/LawCompile.lean` carries another lane's uncommitted `tally_run_agrees` → `example` hunk, kept out of these commits and left in the tree as found. `Vault/Hyperedge.lean` (security lane) is used (`admitFootprint`), not edited.

## Fixture triage edits in files other lanes hold dirty (lean-proof-engineering lane, 2026-11-04)

The triage commit carries HEAD's text of these files plus the triage edit; the working tree carries the
owning lane's content plus the same edit (`-- fixture kept` lines, `theorem`→`example`, deletions). Nothing
to re-apply; commit the file as it stands. Two sites exist only in the dirty copy (TaylorModel:929, RealAnalysis:975)
and stay in place as kept examples there. `Obend/Teeth/Analysis/Fixtures.lean` in the working tree follows the
analysis lane's uncommitted `tmUnitaryNormSq` signature; it lands with that change, not before.

| file | kept | to Teeth | deleted |
|---|---|---|---|
| `lean/Obend/Analysis/Flowpipe.lean` | 1 | 0 | 0 |
| `lean/Obend/Analysis/Format.lean` | 2 | 1 | 0 |
| `lean/Obend/Analysis/Hybrid.lean` | 4 | 0 | 1 |
| `lean/Obend/Analysis/QuantumWalk.lean` | 1 | 3 | 0 |
| `lean/Obend/Analysis/SosLyapunov.lean` | 2 | 0 | 1 |
| `lean/Obend/Analysis/TaylorModel.lean` | 3 | 1 | 0 |
| `lean/Obend/Core/Code.lean` | 2 | 0 | 0 |
| `lean/Obend/Core/Proofs/CheckCompletenessObstruction.lean` | 1 | 0 | 0 |
| `lean/Obend/Core/Proofs/CheckerTransport.lean` | 3 | 0 | 0 |
| `lean/Obend/Core/PrototypeProvenance.lean` | 5 | 0 | 0 |
| `lean/Obend/Elab/AutoCert.lean` | 5 | 0 | 0 |
| `lean/Obend/Hardware/Codec.lean` | 0 | 0 | 2 |
| `lean/Obend/Hardware/CurrentLoop.lean` | 2 | 0 | 0 |
| `lean/Obend/Hardware/DigitalTwin.lean` | 1 | 0 | 1 |
| `lean/Obend/Hardware/FabuBlox.lean` | 2 | 0 | 2 |
| `lean/Obend/Hardware/Magnetics.lean` | 0 | 0 | 1 |
| `lean/Obend/Hardware/PowerElectronics.lean` | 1 | 1 | 2 |
| `lean/Obend/Hardware/Retiming.lean` | 0 | 1 | 0 |
| `lean/Obend/Judge/Certified.lean` | 2 | 0 | 0 |
| `lean/Obend/Judge/LayeredCost.lean` | 2 | 0 | 1 |
| `lean/Obend/Judge/RealAnalysis.lean` | 0 | 1 | 0 |
| `lean/Obend/Law/Proofs/Inherit.lean` | 2 | 2 | 0 |
| `lean/Obend/Logic/Obligation.lean` | 2 | 0 | 0 |
| `lean/Obend/Logic/Turn.lean` | 1 | 0 | 0 |
| `lean/Obend/Lower/ExprCAM.lean` | 1 | 0 | 1 |
| `lean/Obend/Spec/Proofs/LawCompile.lean` | 1 | 0 | 0 |
| `lean/Obend/Spec/Proofs/PackageLaw.lean` | 0 | 1 | 0 |
| `lean/Obend/Teeth/Core/CollectYield.lean` | 1 | 0 | 1 |
| `lean/Obend/Vault/PhysicalProjection.lean` | 1 | 0 | 0 |

Apps (classified, applied by their owners): FPGA successor, `Obend/Apps/ObendRisc.lean:517`
`obendRiscCpuRtlModule_firmware_sim_sound` is a deletion (the 21-cycle CPU run the ledger names); physics successor,
`Obend/Apps/QuantumPhotonicMatter.lean` must `import Obend.Teeth.Hardware.CliffordKernel` for `majoranaBraid_artin_relation`
(moved there, over budget). The remaining Apps fixtures are kept where they are (already tier 2); their own
`*_rtl_and_amd_gpu_verified` end-to-end runs are the apps' content, not fixtures of the library.

Two tier-2 tests red for other lanes after this lane's tier-2 pass (2026-11-04): compiler successor,
`tests/silicon_elab/SiliconRealismTest.lean` lines 234-243 and 365 (`compileTermPipelined` /
`compileTermPipelinedDiscardArg` take a `List RtlExpr` the test does not pass) and 370 (a `RtlAluOp`
match missing `ashr`, `slt`, `qmul32`); physics successor, `tests/metasystem/QuantumCliffordClementsTest.lean`
lines 329 and 341 (`cliffordParityQuotient` is `Nat → Nat → IntMatrix` now). The `kernelIsDefEqFull`
call sites and the Clifford import are done.

## What the lean-proof-engineering lane landed (2026-11-04, evening)

| commit | what | verified |
|---|---|---|
| `459e517` | the last tier-1 import of the deleted `Obend.Leaf.BendTT` (UserspacePhysical) | bb2, `lake build` on a180c75 |
| `c18ca36` | the documents census runs from `Obend/Census.lean` (tier 2), not inside `DocsCensus` at its build | same build |
| `7aee61d` | the compiler lane's cross-lane patch for UserspacePhysical, Stdlib, DiscrTreeLUT, four tests | bb2 gate |
| `4b6c60f` | `tools/build.sh tier1|tier2` with the 60 s / 600 s budget from Lake's timings; the hook through it; `Obend.Stdlib` to tier 2; the census heartbeat baseline and tier-2 globs | bb2: tier 1 green, QuantumMatter named over budget |
| `92132ed` | the fixture triage applied (158 kept with reasons, 34 to `Teeth/*/Fixtures.lean`, 32 deleted); the Clifford theorems to `Teeth/Hardware/CliffordKernel.lean`; the census table | bb2: tier 1 green within budget (QuantumMatter 50 s); Stdlib and 39 Teeth modules within tier 2 |
| `cafd87c` | the theorem classification (`theoremCensus`) and the identifier-resolving documents census (`#docs_census`) | bb2: AssertAxioms and DocsCensus build; a reduced census runs the three commands; the full census waits on the Apps |

Rules kept: named-file commits through a temporary index (the shared index held other lanes' staged
files), unsigned (1Password refused), one build at a time in `bb2:~/lane-gate`, every job with a PID
file. Not done: a full tier-2 run (`Obend.Census Teeth Tests`), because the census imports every Apps
module and `Obend/Apps/ZkNtt.lean` elaborates for hours; the budget gate will fail it at 600 s once it
can be run at all.
- (fifth round, `9de897f`, `b8fa08b`) All files in the lane's list (`Vault/{Store,Page,Law}.lean`, `tests/decisions`, `README.md`, `crates/obend-gui`). `crates/obend-gui/build.rs` was rewritten to obend-node's form at the security lane's request (rpaths from `DEP_OBEND_BRIDGE_*`); verified to compile and pass its CLI test under the stub on bb2 only. The shared index held another lane's staged deletion (`apps/zk-ntt/verilator/zk_ntt_lec.smt2`); these commits went through a temporary index and left it as found. `Vault/PhysicalProjection.lean` is dirty from another lane and untouched.
- (sixth round, `31b213a`, `7609e89`, `a61d805`) Outside the lane's list: `lean/Obend/Tactic/DocsCensus.lean` and `lean/Obend/Census.lean` (gate lane: the `#census_environment` emitter and its one call, appended after `cafd87c`, nothing of theirs changed); `lean/Obend/Analysis/{Worlds,Replay}.lean` (one argument each: the store's environment passed to `ownerWrite`/`commit`, else a replay would count every cite unresolved); `lean/Obend/Doc/Render.lean` (the lexer's inline-code arm). `review/DECISIONS-20261031.md` gains three frontmatter lines (`kind: ledger`); `review/.obend/world.json` is committed as the ledger's world. A misordered commit `02fbb3c` was dropped by moving the ref before anything landed on it; the shared index was left as found except that the four new files were added to it equal to HEAD, so they do not show as staged deletions.

## Adjudications (device-physics lane, 2026-11-04)

Method: `bb2:~/lane-device` is the verify tree with HEAD of 11-04 overlaid (`git archive HEAD lean`); only this
lane's modules, their importers and the tier-2 modules that cite them were built (`swarm-build lake build
<modules>`, `LEAN_NUM_THREADS=4`, `SWARM_MEM_MAX=16G`). Report: `review/EXPERT-device-physics-20261104.md`.

| file | lane | call | why |
|---|---|---|---|
| `lean/Obend/Hardware/FabuBlox.lean` | proof-engineering (fixture triage) | **keep** | one line, `unstripped_resist_high_temp_refused` theorem → `example`; carried into this lane's rewrite of the file. |

Changed by this lane outside its three files, all mechanical and all from one rename (`Hardware/Physics.lean`
→ `Hardware/ThermalPassivity.lean`, what the surviving three sections are): `Hardware/Codec.lean` (import and two
qualified names), `Obend/Hardware.lean` and `Obend/Census.lean` (the rename; the five `Device/` modules added),
`Hardware/TapeoutPipeline.lean` and `Hardware/Judge.lean` (an import and `open` of `Physics` that nothing used),
`Teeth/Hardware/SiliconTeeth.lean` (tooth 27, which mutated the three-cell PDD, now mutates `Device.WaferState.anneal`
against `anneal_var_mono`), `tests/metasystem/SiliconSpineTest.lean` §3 (the bundle keeps the two surviving
statements) and `tests/metasystem/PhysicalSiliconSpineTest.lean` §3.3 (deleted with the RC monotonicity theorems).
`TcadBridge.lean` keeps `extractTcadCornerEnvelope`, `extractTcadCornerEnvelope_valid`, `checkEnvelopeTimingSignoff`
and its theorem because `TapeoutPipeline` stage 7 reads them; the three integer formulas they need moved into it
from the deleted `Physics` §7 under a section that says what they are.

Added to the sibling's namespace `Obend.Analysis.Interval` (for dot notation, from `Device/Enclosure.lean` and
`Device/DriftDiffusion.lean`): `powNat`, `invPos`, `divPos?`, `roundOut`, `sqrIterRound`, `within`, `scale`,
`absMax`, `widenRel`, each with its membership lemma. The physics lane may lift them into `RealAnalysis.lean`.

Seen red at HEAD on bb2, not this lane's: `Obend/Teeth/Analysis/Fixtures.lean:143` (`Function expected`,
`schrodingerEigenmodeOde`), which stops `Obend.Census`; the Mac working tree carries an uncommitted three-line
edit of that file by another lane.

### Pickup, physics lane, 2026-11-04 14:10 (Mac)

Landed `3c9066b 3ae4e5e 6ad68e1 8123df8 5c4186c 016c3b7 888cf9b 164d5cf` (named files, explicit paths).
Confirming build on bb2 at HEAD `6bdea10` plus these files, `CliffordKernel` present (`~/lane-logs/build-o.log`):
green, Apps.FocHil/SdrFt8/QuantumPhotonicMatter included. Tests (`test6-*`): `CoupledMultiphysicsTest` green;
`AutoCertTest` red only at `:580` `#check_docs_census` (`DESIGN.md` cites the deleted `Obend/Leaf/BendTT.lean`,
`review/DECISIONS-LEDGER.md` lacks a doc entry; neither file is this lane's); `QuantumCliffordClementsTest`
red at `:329-341`: `cliffordParityQuotient : Nat → Nat → IntMatrix` (`Hardware/QuantumMatter.lean:934`, HEAD)
is passed where `checkEquitablePartition`/`perturbedQuotient` take `Nat → Nat → Int`; both files are clean at
HEAD and untouched by this lane's commits, so it is the gate lane's (`92132ed` rewired that test).
`Teeth/Analysis/Fixtures.lean:143` (device lane's report) is fixed in `164d5cf`. QuantumMatter: 103.2 s before
`92132ed`'s move, 50.8 s after, measured alone on bb2.
