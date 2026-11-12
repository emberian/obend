# Silicon Elaborator and Hardware-Lowered Kernel Checking

`Obend.Lower` (`lean/Obend/Lower/`) and `Obend.Tactic.SiliconElab` (`lean/Obend/Tactic/SiliconElab.lean`) formalize a self-contained Lean kernel and elaboration fragment (`LeanKernel`), lower it into `Obend.Core.Term` / `Obend.Leaf.Book` definitions, compile kernel gate and specialization tiles to synchronous RTL (`RtlModule`) and reconfigurable `AutomatonTile` meshes, and drive a De Bruijn-criterion proof-producing `silicon_simp` tactic.

---

## 1. `Obend.Lower.LeanKernel`: Total Kernel and Elaboration Fragment

`lean/Obend/Lower/LeanKernel.lean` models kernel declarations, environments, discrimination-tree indexing, and small-step reduction inside Lean 4:

- **Kernel Environment (`KConstInfo`, `KInductDecl`, `KRecRule`, `KEnv`)**: Represents axioms, definitions, theorems, inductive types, and recursor computation rules over de Bruijn kernel expressions (`KExpr` / `LExpr`).
- **Elaboration Indexing (`MacroRule`, `DiscrTreeKey`, `SimpRule`, `ClassInstance`)**: Models discrimination-tree lookup (`lean/Obend/Lower/DiscrTreeLUT.lean`), first-order metavariable unification (`lean/Obend/Lower/MetaUnify.lean`), and 88-bit content-addressable expression tables (`HwExprCAM`, `packNodeWord88`, `unpackNodeWord88` in `lean/Obend/Lower/ExprCAM.lean`).
- **Verified Reduction & Fail-Closed Eta/DefEq**:
  - `stepLExpr?_sound` and `runLExprSteps_sound` prove that executable single-step and bounded reduction implement the relational small-step semantics `SStep`.
  - `etaDomCompat_fail_closed_sound` proves that domain-incompatible lambda eta comparisons fail closed rather than equating distinct binder domains.

---

## 2. Lowering Lean Expressions to `Obend` Books (`lean/Obend/Lower`)

The lowering pipeline (`lean/Obend/Lower/Lower.lean`, `lean/Obend/Lower/LCNF.lean`, `lean/Obend/Lower/Inductive.lean`, `lean/Obend/Lower/Reflect.lean`) compiles Lean expressions into `Obend.Core.Term` and `Obend.Leaf.Book`:

- **Book Packaging (`lean/Obend/Lower/Proofs/Book.lean`)**: `leanComposition` wraps lowered terms into closed `Obend.Logic.Composition` prototypes; `book_member` and `lean_to_book` prove member lookup equivalence through `Obend.Leaf.emit`.
- **Semantic Preservation (`lean/Obend/Lower/Proofs/Sound.lean`, `lean/Obend/Lower/Proofs/Complete.lean`, `lean/Obend/Lower/Proofs/Subst.lean`)**: Establishes substitution commutation and operational agreement between source `LExpr` reduction and lowered `Obend.Core.Term` execution.
- **Certificate Judge (`lean/Obend/Lower/Judge.lean`)**: Registers lowering equivalence verification in `Obend.Judge.registry` (`Obend.Lower.format`).

---

## 3. Five-Stage Silicon Kernel Gate, Glitch-Free DPR, and RTL Emission

`lean/Obend/Lower/Proofs/SiliconKernel.lean` and `lean/Obend/Lower/SiliconElabFabric.lean` lower kernel declaration gating, residual specialization, and interaction-net reduction to 64-bit hardware datapaths:

1. **Five-Stage Verified Kernel Gate (`lean/Obend/Lower/Proofs/SiliconKernel.lean`)**:
   - `kernelGateLExpr`, `kernelGateBook`, and `kernelGateTile` lower `kernelDeclStatusTag` / `kernelCheckDecl` through `Obend.Leaf.Book` into both `RtlModule` (`compileBookToRtlSat`) and `AutomatonNetwork` (`compileBookToAutomaton`).
   - `silicon_kernel_5stage_check_sound` universally proves across every `(env : KEnv)`, `fuel`, and `(decl : KConstInfo)` that all five stages (`LExpr` `SSteps` → `Core4` `Evaluates` → `Leaf.Book` `Halts` → `RtlModule` → `AutomatonNetwork`) accept (`1` / `1#64`) iff `kernelCheckDecl env fuel decl = true` and fail closed (`0` / `0#64`) on `sorryAx` or ill-typed declarations.
   - `silicon_elab_residual_dpr_specialize_sound` and `silicon_elab_env_mutation_fallback_sound` prove glitch-free 3-phase `ICAP` Dynamic Partial Reconfiguration (`runTileGlitchFreeDpr` with `expectedCrc64` / `computedCrc64` verification, guarded by `#tooth` mutation `dprPhase2IgnoreCrc` in `lean/Obend/Teeth/Hardware/SiliconTeeth.lean`) and 1-step `specSlot` fallback to `Candidate.machine` when an upstream `Environment` pin mutates.
   - `silicon_kernel_inet_beta_agrees` proves that 1-cycle hardware interaction-net $\beta$-reduction (`reduceActivePair`) agrees with `kernelWhnf` and `Evaluates`.
2. **SystemVerilog Fabric Emission (`lean/Obend/Lower/SiliconElabFabric.lean`)**:
   - `emitSiliconElabFabricSV` emits synthesizable SystemVerilog for the 4-zone CAM/NoC/LUT/kernel fabric (`admitSimpTheoremDpr_glitch_free_sound`), paired with Verilator co-simulation harnesses in `lean/Obend/Apps/SiliconKernelVerilator.lean`.

---

## 4. `#silicon_check` and Proof-Producing `silicon_simp` (`lean/Obend/Tactic/SiliconElab.lean`)

`Obend.Tactic.SiliconElab` (`lean/Obend/Tactic/SiliconElab.lean`) connects live Lean 4 declarations and tactic goals directly to the 4-zone Silicon Elaborator model:

- **`#silicon_check` (`runSiliconCheckTelemetry`)**: Reflects a Lean declaration and its dependency cone (`extractLeanConstInfoBounded`, `leanExprHasSorry`), interns terms into 88-bit `HwExprCAM` words (`packNodeWord88` / `unpackNodeWord88`), runs Zone-1 WHNF and Zone-4 kernel verification (`stepZone4KernelCheck`), and fails closed on `sorryAx` or out-of-fragment constants.
- **De Bruijn-Criterion `silicon_simp` (`SiliconSimpRule`, `leanExprToKPattern`, `extractSiliconSimpRule?`)**: Indexes equational and `Iff` rewrite rules in `DiscrTrieNode` (Zone 3), matches subterms via `MetaUnify` (Zone 2) and `HwExprCAM` WHNF handles (Zone 1), and reconstructs an explicit kernel-checked `Lean.Expr` equality/equivalence proof term verified by `Lean.Meta.check` with zero fallback to host `simp`, `omega`, or `decide`.
