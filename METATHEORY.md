# Metatheory

Obend's metatheory connects surface elaboration, graded/linear row typing, contextual equivalence, open-recursive specialization, non-monotonic justification, durable vault replay, and hardware lowering inside Lean 4 (`lean/Obend`).

---

## 1. Bidirectional Typing, Graded Linearity, and Machine Safety

### 1.1 Soundness and Erasure (`lean/Obend/Core/Check.lean`, `lean/Obend/Core/Bidirectional.lean`)

- **Extrinsic Erasure**: `AnnotatedTerm` pairs an unannotated `Obend.Core.Term.Term` with path-indexed lambda `Annotations` and equi-recursive row `Assumptions`. `checked_erasure` establishes that bidirectional checking indexes directly over the erased runtime term.
- **Bidirectional Soundness**: `checkAgainst_sound` proves that `checkAgainst` and `infer` (`lean/Obend/Core/Bidirectional.lean`) construct valid `PartialTyping`, `FieldsTyping`, and `ArmsTyping` derivations. `elaborate_refuses_hole` guarantees that no unfilled `Term.hole` passes full checking.
- **Linear and Reusable Capture Discipline**: `Quantity` (`erased`, `affine`, `linear`, `unrestricted`) and `Reuse` (`once`, `reusable`) enforce exact resource accounting (`Quantity.fits`, `branchesAgree`). `reusable_lambda_capture_rule` prevents `Reuse.reusable` closures from capturing `linear` or `affine` context bindings, and `computation_not_shareable` ensures delimited `Ty.computation` plans cannot be duplicated.

### 1.2 Row Polymorphism and Equi-Recursive Bounds

- **Finite Canonical Rows (`lean/Obend/Core/Ty.lean`, `lean/Obend/Core/FiniteRowLaws.lean`)**: `Ty.canonical` sorts distinct fields canonically (`Ty.canonical_canonical`, `Ty.shareableUnder_canonical`), discharging row commutativity and shadowing laws (`finite_field_commute`, `finite_field_shadow`, `semantic_field_shadow`).
- **Amadio–Cardelli Equi-Recursive Rows (`lean/Obend/Core/Check.lean`, `lean/Obend/Core/EquiRecursiveAgreement.lean`, `lean/Obend/Core/FiniteBisimulation.lean`)**: Bounded cycle-detecting row traversal (`lookupV`, `isRowV`) terminates via `unvisited_lt` and agrees with relational coinductive row membership (`lookupV_iff`, `isRowV_iff`).

### 1.3 Subject Reduction and Bounded Machine Adequacy

- **Preservation (`lean/Obend/Core/Proofs/SubjectReduction.lean`, `lean/Obend/Core/Proofs/Aggregate.lean`, `lean/Obend/Core/Proofs/Preservation.lean`)**: Small-step reduction preserves graded typing (`step_preserves_typing`, `steps_preserve_typing`, `split_accounts`, `custody_conserved`). Across the heap-and-frame machine (`lean/Obend/Core/Machine.lean`), `typed_stepRaw_preserved` and `checked_runBounded_no_refusal` prove that closed checked terms never fault with missing-field, wrong-tag, or internal machine refusals.
- **Garbage Collection Preservation (`lean/Obend/Core/Collect.lean`, `lean/Obend/Core/Proofs/Collect.lean`)**: Mark-compact heap collection preserves reachability, typing, and lockstep machine evaluation (`lean/Obend/Core/Proofs/Collect/Lockstep.lean`, `lean/Obend/Core/Proofs/Collect/Typing.lean`).

---

## 2. Observational Equivalence, Improvement, and `Leaf` Specialization

### 2.1 Contextual Equivalence and Sands Improvement (`lean/Obend/Equiv`)

- **Behavioral Equivalence (`lean/Obend/Equiv/Behaviour.lean`)**: Contextual equivalence `≈b` (`BEquiv`) and `≈r` (`REquiv`) form congruences preserving terminating observations (`BEquiv.sameRuns`). Prototype composition `Term.mix` is proved associative up to `≈b` (`mix_assoc`) even though it is not weak-head associative (`mix_assoc_not_weak_head`).
- **Cost Improvement (`lean/Obend/Equiv/Improvement.lean`)**: `Sim`, `EvalImproves`, and `SandsImproves` formalize Sands' improvement preorder: call-by-value beta-reduction on settled arguments strictly improves step counts (`beta_value_improves_cost`, `beta_demanded_evalImproves`).

### 2.2 Prototype Flattening and Futamura Book Specialization (`lean/Obend/Leaf`)

- **Flattening (`lean/Obend/Leaf/Flatten.lean`, `lean/Obend/Leaf/Residual.lean`)**: `flatten_object` and `flatten_sound` establish behavioral equivalence (`≈b`) between flattened vtables and dynamic prototype objects for every closed `Composition`, while `vtable_clean` and `no_residual_super` eliminate all dynamic super-chain traversals.
- **Book Emission & Pin Specialization (`lean/Obend/Leaf/Emit.lean`, `lean/Obend/Leaf/Static.lean`, `lean/Obend/Leaf/Specialize.lean`)**: `emit_sound` and `book_sound` prove behavioral equivalence between emitted `Book` definitions and flattened compositions. Cross-package pin specialization (`specializeBook_eq_foldBook_bindBookPins`, `link_bequiv_specializeBook`, `specializeBook_member_sound`) is guarded by `specSlot`, which blocks stale books whenever an upstream pin changes (`moved_pin_blocks`, `specialized_moved_pin_blocks`).

---

## 3. Non-Monotonic Justification, Vault Durability, and Genealogy

### 3.1 Van Gelder Alternating Fixpoint (`lean/Obend/Reasons.lean`)

`Obend.Reasons` models stratified and unstratified defeasible rules via Van Gelder's alternating operator `rounds` (`gamma` composed twice):
- `gamma_least` and `rounds_least` establish least-fixpoint existence (`wf`), yielding a three-valued `Status` (`supported`, `undefined`, `unsupported`).
- `no_conclusion_from_cycles` ensures positive self-referential loops never manufacture `supported` status.
- `survives_one_support`, `defeat_only_by_evidence`, and `action_needs_support` guarantee that justified conclusions persist under redundant support removal and can only be defeated by concrete counter-evidence.

### 3.2 Vault Replay, Membranes, Transport, and Retention (`lean/Obend/Vault`)

- **Replay & Crash Recovery (`lean/Obend/Vault/Replay.lean`)**: `state_eq_replay_log`, `recover_eq_replay_prefix`, `checkpoint_is_cache`, and `obligations_survive_crash` tie live state and open obligations to deterministic log folding.
- **Membrane Non-Amplification (`lean/Obend/Vault/Form.lean`, `lean/Obend/Vault/FormCheck.lean`)**: `eval_fill_eq_subst_residual`, `residual_reads_nothing_known`, `admit_no_amplification`, `admit_conserves_total`, and `rechecked_zero` prove privacy, conservation, and single-pass check reuse.
- **Capability Handoff & Compaction (`lean/Obend/Vault/Transport.lean`, `lean/Obend/Vault/Retention.lean`, `lean/Obend/Vault/Merge.lean`)**: `handoff_no_absence` and `merge_revocation_wins` eliminate custody gaps and stale authority during cross-vault transport; `state_eq_replay_compacted` preserves replay semantics across right-to-forget log compaction; `mergeVault_agrees` reconciles divergent vault prefixes.

### 3.3 Judge Succession and Löb Floor Accounting (`lean/Obend/Judge/Genealogy.lean`)

`Obend.Judge.Genealogy` formalizes how a node upgrades its own active judges (`Habitat`, `Gate`, `Method`, `LobCost`):
- `succession_sound` and `succession_sound_meaning` ensure every admitted successor judge preserves the floor invariants of its habitat (`run_floors`, `run_noninterference`).
- `lob_labelled` and `lob_cost_necessary` prove that any step extending logical strength beyond evaluation reduction must explicitly record a `LobCost` trust-extension label rather than claiming self-proof inside the weaker theory.

---

## 4. Falsifiability: `#tooth` Mutation Gates and Axiom Auditing

Soundness theorems over vacuously false preconditions or trivialized checkers provide no assurance unless tested against adversarial mutations:
- **`#tooth` (`lean/Obend/Tactic/Tooth.lean`)**: Re-elaborates a target theorem after substituting a mutated definition (such as replacing a checker with `fun _ _ => Verdict.ok` or swapping wire operand order) inside an isolated temporary environment, succeeding only if the kernel **rejects** the proof under the mutation. Suites across `lean/Obend/Teeth/` exercise `#tooth` across `Core`, `Leaf`, `Law`, `Lower`, `Hardware`, and `Vault`.
- **Axiom and Compiler-Trust Census (`lean/Obend/AssertAxioms.lean`, `lean/Obend/AssertCompiled.lean`)**: Inspects the transitive dependency cone of exported theorems via `Lean.collectAxioms`, enforcing the `no_sorry_ax` floor and isolating any compiled-decision trust (`isCompilerTrust`) for explicit re-execution under `#assert_compiled`.
