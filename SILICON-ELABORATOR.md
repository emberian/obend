# Silicon Elaborator and Hardware-Lowered Kernel Checking

`Obend.Lower` (`lean/Obend/Lower/`) and `Obend.Tactic.SiliconElab` (`lean/Obend/Tactic/SiliconElab.lean`) formalize a self-contained Lean kernel and elaboration fragment (`LeanKernel`), lower it into `Obend.Core.Term` / `Obend.Leaf.Book` definitions, and compile core definitional-equality and node-checking engines to synchronous RTL (`RtlModule`).

---

## 1. `Obend.Lower.LeanKernel`: Total Kernel and Elaboration Fragment

`lean/Obend/Lower/LeanKernel.lean` models kernel declarations, environments, discrimination-tree indexing, and small-step reduction inside Lean 4:

- **Kernel Environment (`KConstInfo`, `KInductDecl`, `KRecRule`, `KEnv`)**: Represents axioms, definitions, theorems, inductive types, and recursor computation rules over de Bruijn kernel expressions (`KExpr` / `LExpr`).
- **Elaboration Indexing (`MacroRule`, `DiscrTreeKey`, `SimpRule`, `ClassInstance`)**: Models discrimination-tree lookup (`lean/Obend/Lower/DiscrTreeLUT.lean`), first-order metavariable unification (`lean/Obend/Lower/MetaUnify.lean`), and content-addressable expression tables (`lean/Obend/Lower/ExprCAM.lean`).
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

## 3. Silicon Kernel Node Checking and RTL Emission

`lean/Obend/Lower/Proofs/SiliconKernel.lean` and `lean/Obend/Lower/SiliconElabFabric.lean` lower kernel node-checking and definitional-equality steps all the way to 64-bit hardware datapaths:

1. **Lowered Kernel Node RTL (`lean/Obend/Lower/Proofs/SiliconKernel.lean`)**:
   - `stepCamDefEqNodeLExpr` and `stepCamDefEqNodeBook` lower CAM-backed definitional-equality node evaluation into an `Obend.Leaf.Book` and synthesize the corresponding `RtlModule` (`evalLoweredDefEqNodeRtl`).
   - `real_silicon_kernel_node_check_sound` proves that the synthesized RTL datapath agrees bit-accurately with the kernel specification and rejects corrupted proof nodes.
   - Adversarial mutation witnesses (`mkNodeInputEnvSwappedArgs`, `kernelNodeCheckSpecAlwaysAccept`, `evalLoweredNodeCheckRtlAlwaysAccept`) ensure `#tooth` checks catch swapped ports or trivialized accept paths (`lean/Obend/Teeth/Hardware/SiliconTeeth.lean`).
2. **SystemVerilog Fabric Emission (`lean/Obend/Lower/SiliconElabFabric.lean`)**:
   - `emitSiliconElabFabricSV` emits synthesizable SystemVerilog for the CAM/LUT elaboration datapath, paired with Verilator co-simulation harnesses in `lean/Obend/Apps/SiliconKernelVerilator.lean`.

---

## 4. Self-Hosted Kernel Check Milestone (`lean/Obend/Tactic/SiliconElab.lean`)

`Obend.Tactic.SiliconElab` (`lean/Obend/Tactic/SiliconElab.lean`) exercises `LeanKernel` on reflected kernel declarations (`SiliconCheckTelemetry`):

- Accepts valid reflected declarations (`selfHostKernelCheckDeclInfo`, `selfHostBottomUpCamInferInfo`, `selfHostIdentityProofInfo`).
- Rejects ill-typed mutated proofs (`selfHostMutatedBadProofInfo`) and nested `sorryAx` terms (`selfHostSorryProofInfo`, `deepNestedSorryLeanConstInfo`).
- `silicon_self_hosting_milestone_sound` packages both positive acceptance of well-typed self-hosted kernel declarations and fail-closed rejection of mutated or `sorry`-tainted constants into a single kernel-checked theorem.
