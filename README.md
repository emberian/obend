# Obend

Obend is a formally verified programming language, local-first vault and decentralized operating-system (`DeOS`/`Polis`) substrate, dual-track cryptographic proof spine, corrigibility and judgment registry, and Lean-to-silicon/GPU compilation stack implemented in Lean 4 (`lean/Obend`) with a thin Rust host workspace (`crates/`).

Every layer — from Obsidian-compatible markdown vaults (`obend open`, frontmatter laws, member proposals, offline pushout `obend merge`, and double-entry books), open-recursive C4 `specification`/`compose` elaboration, extrinsic resource-graded `Core4` row typing, and choice-free realizability repair (`Obend/Category`, `Obend/Repair`) to hash/lattice dual-track commitments (`Obend/Crypto`), 256-bucket chunked vault replay welded to stateless Verkle commitments (`Obend/Vault/ChunkedWorld.lean`, `Obend/Vault/VerkleSnapshotBridge.lean`), `svenvs` constitutional corrigibility (`Obend/Judge/SvenvsCorrigibility.lean`), 5-stage silicon kernel hardware specialization (`silicon_simp`), FABulous FPGA bitstreams, and RDNA2 GPU binary validation — is defined as an executable model in Lean 4 and paired with kernel-checked soundness and refusal proofs (`0 sorry`, `0` custom axioms).

---

## Quickstart: Markdown Digital Gardens, Offline Merge, Double-Entry Books & Proofs

Once `obend` is built on your Linux build host (`lean/.lake/build/bin/obend`; see **Remote Build & Verification Discipline** below), three end-to-end workflows run out of the box without modifying how your files live on disk:

### 1. Obsidian-Style Markdown Vault (`obend open`), Frontmatter Laws & Offline `obend merge`

`obend open` reads any folder of plain markdown notes (`[[Beta]]` wikilinks, `![[Beta]]` embeds, and `[[Beta#^answer]]` block quotes) and maintains a hash-chained world beside them in `.obend/` without altering your note format. Frontmatter `law` clauses refuse invalid edits constructively — naming the violated clause and a passing value while leaving your file text intact — and offline forks merge back by directed atom-graph pushout (full walkthrough: `lean/tests/vault/WALKTHROUGH.md`):

```bash
mkdir garden && cd garden
cat > Alpha.md <<'EOF'
# Alpha

Links to [[Beta]] and quotes its answer: [[Beta#^answer]].
EOF
cat > Beta.md <<'EOF'
---
law short: new.words <= 20
---
# Beta

Beta answers [[Alpha]].
The answer is forty-two. ^answer
EOF

obend open
obend status

# A write exceeding 20 words is refused naming the clause and passing bound; Beta.md keeps your text:
cp Beta.md ../Beta.saved
printf 'And here is a long digression that goes on and on past twenty words easily now.\n' >> Beta.md
obend open || true
# -> Beta: refused by its law short: `new.words <= 20` does not hold; words = 20 would pass (this write has words = 26)
mv ../Beta.saved Beta.md

# Invite a member who may propose candidate sections without overwriting the owner:
obend member add scout --grant post:Alpha
printf '# Alpha\n\nScout candidate paragraph.\n' > ../proposal.md
obend post Alpha ../proposal.md --as scout
# -> Alpha: section 1: 2 candidates (owner, scout); keep one with: obend select Alpha 1 N
obend select Alpha 1 1

# Copy the vault offline, edit both copies independently, and merge by pushout:
cp -R . ../laptop
printf '\nOffline note from laptop.\n' >> ../laptop/Alpha.md
(cd ../laptop && obend open)
printf '\nDesk note before merge.\n' >> Alpha.md
obend open
obend merge ../laptop
```

### 2. Double-Entry Markdown Ledger & Third-Party Receipt Verification

Adding account pages, document templates (`invoices/_kind.md`), and a law-governed register (`register/_kind.md`) turns any markdown vault into an auditable double-entry book whose postings (`posting@1`) and period trial balances (`trial-balance@1`) emit standalone receipts verifiable with `obend verify` without access to the vault (full walkthrough: `lean/tests/ledger/WALKTHROUGH.md`):

```bash
mkdir -p accounts invoices register
printf -- '---\ncode: 1100\n---\n# Receivables\n' > accounts/Receivables.md
printf -- '---\ncode: 4000\n---\n# Revenue\n' > accounts/Revenue.md
cat > invoices/_kind.md <<'EOF'
---
amount: 0
period: 0
---
- debit [[accounts/Receivables]] amount
- credit [[accounts/Revenue]] amount
EOF
cat > register/_kind.md <<'EOF'
---
law balanced: new.debits == new.credits
---
Double-entry register.
EOF
printf -- '---\nkind: invoices\namount: 500\nperiod: 11\n---\nConsulting invoice.\n' > invoices/INV-1.md

obend open
obend ledger post invoices/INV-1
obend ledger status
obend report trial-balance 11
obend verify .obend/receipts/P-0001.json
```

### 3. Open-Recursive `.obend` Specifications, Claims & Standalone `rewrite@1` Proofs

Open-recursive `spec` / `compose` / `fix` packages typecheck with `obend check`, evaluate with `obend run`, discharge equational `claim` obligations into standalone `rewrite@1` JSON certificates with `obend prove`, and re-check with zero producer state via `obend verify`:

```bash
mkdir -p ../pkg
cat > ../pkg/Review.obend <<'EOF'
edition ObjectiveBend 1
record Review:
  review(value: Nat) -> Nat
  twice(value: Nat) -> Nat
spec Base for Review:
  def review(value: Nat) -> Nat:
    value + 1
spec Twice for Review:
  requires review(value: Nat) -> Nat
  def twice(value: Nat) -> Nat:
    self.review(self.review(value))
  claim repeated(value: Nat): self.twice(value) == self.review(self.review(value))
spec Augmented for Review:
  def review(value: Nat) -> Nat:
    super.review(value) + 1
def buildReview(seed: Review) -> Review:
  fix(compose(Base, Twice, Augmented), seed)
def twiceOfThree() -> Nat:
  buildReview({review: fn(value: Nat) -> Nat: value, twice: fn(value: Nat) -> Nat: value}).twice(3n)
EOF

obend check ../pkg
obend run ../pkg twiceOfThree
obend prove --package ../pkg Review.Twice.repeated --object twiceOfThree --out ../receipt.json
obend verify ../receipt.json
```

---

## Architecture Overview

| Layer | Lean Modules / Host Crates | Primary Guarantees |
| :--- | :--- | :--- |
| **Open-Recursive C4 & Resource-Graded `Core4`** | `lean/Obend/Spec/C4.lean`, `lean/Obend/Spec/Proofs/SpecificationClosure.lean`, `lean/Obend/Core/Term.lean`, `lean/Obend/Core/Ty.lean`, `lean/Obend/Core/Check.lean`, `lean/Obend/Core/RangeSafe.lean`, `lean/Obend/Core/Machine.lean`, `lean/Obend/Intention.lean`, `lean/Obend/Slot.lean`, `lean/Obend/Slot/SupportSheaf.lean`, `lean/Obend/Logic/SuperRefines.lean`, `lean/Obend/Leaf/Flatten.lean`, `lean/Obend/Leaf/Emit.lean`, `lean/Obend/Leaf/LinkSpecialize.lean` | Open-recursive `specification` / `compose` closure (`compose_typed`, `compose_step_typed`), vertical `super` claim refinement (`superClaim_sound`), extrinsic linear/graded (`Quantity`, `Reuse`) bidirectional checking (`checkAgainst_sound`), range-safe modular arithmetic (`Obend.Core.RangeSafe`), demand-machine preservation (`step_preserves_typing`, `checked_runBounded_no_refusal`), coalgebraic delta-lens `SupportSheaf` transport (`disjoint_transport_sound`), prototype flattening (`flatten_sound`, `book_sound`), and `GPaco` whole-book link specialization (`gpaco_clo_upToStep_sound`, `moved_pin_blocks`). |
| **Compositional Refinement & Scar-Free Repair** | `lean/Obend/Category/OpenSystem.lean`, `lean/Obend/Category/Refines.lean`, `lean/Obend/Category/GradedLogic.lean`, `lean/Obend/Paco/GPaco.lean`, `lean/Obend/Repair/AlgConfig.lean`, `lean/Obend/Repair/CoalgConfig.lean`, `lean/Obend/Repair/QuotAssembly.lean`, `lean/Obend/Tactic/Compositional.lean` | Port-Hamiltonian open-system passivity (`skew_gyrator_power_cancels`), step-indexed Galois simulation refinement (`sim_preserves_galois`), ordered-monoid graded Hoare logic (`frame_triple`), Hur-style `paco`/`gpaco` and Pous companion coinduction (`coind_ok`), ornamented polynomial initial-algebra transport (`unary_bin_add_coherence`), and choice-free, `Quot.sound`-free realizability assembly lifts (`liftHom_spec_mk`, `doubleModQuotHom_tracker_reduces_rfl`). |
| **Dual-Track 2026 Cryptographic Spine** | `lean/Obend/Crypto/Transcript.lean`, `lean/Obend/Crypto/Multilinear.lean`, `lean/Obend/Crypto/Sumcheck.lean`, `lean/Obend/Crypto/PCS.lean`, `lean/Obend/Crypto/DualSpine.lean`, `lean/Obend/Crypto/SameOpening.lean`, `lean/Obend/Judge/Computational.lean` | Domain-separated Fiat–Shamir transcripts over `cSHAKE256`, multilinear sumcheck reductions, 0-axiom game-based `ComputationalJudge` reductions (`dualAssumption_sound`), dual-track Canopy Merkle + Ajtai MSIS polynomial commitments (`dualPCS_sound_of_either`, `canopyAjtaiDualPCS_sound_of_hash_or_sis`), and cross-domain `SameOpening` clearing certificates (`verifySameOpening_sound`). |
| **Patch-Graph Documents** | `lean/Obend/Doc/Graph.lean`, `lean/Obend/Doc/Merge.lean`, `lean/Obend/Doc/Section.lean`, `lean/Obend/Doc/Structured.lean` | Pijul-style directed atom graphs (`IsPushout`), commutative 3-way cell merges (`mergeKeyedCells3_commutative`), citation drift refusal (`SourceMoves`), and lossless structured `.obnb` cell round-trips (`projection_preservation`, `stale_pin_invalidates`). |
| **Sharded DeOS Vault, Markets & Consensus** | `lean/Obend/Vault/Replay.lean`, `lean/Obend/Vault/ChunkedWorld.lean`, `lean/Obend/Vault/VerkleSnapshotBridge.lean`, `lean/Obend/Vault/UnifiedDeos.lean`, `lean/Obend/Vault/CheckedCarry.lean`, `lean/Obend/Vault/SwarmLedgerSeams.lean`, `lean/Obend/Vault/Form.lean`, `lean/Obend/Vault/Transport.lean`, `lean/Obend/Vault/Retention.lean`, `lean/Obend/Ledger/Floors.lean`, `lean/Obend/Ledger/Book.lean`, `lean/Obend/Ledger/Seat.lean`, `lean/Obend/Judge/Netting.lean`, `lean/Obend/Consensus/Finality.lean`, `lean/Obend/Consensus/SimplexProtocol.lean`, `lean/Obend/Consensus/SimplexTrace.lean` | Hash-chained log replay (`state_eq_replay_log`, `checkpoint_is_cache`), 256-bucket O(1) incremental world manifests (`dig_eq_unbe_logHashArray`), COW chunked Verkle commitments and torn-write WAL recovery (`lean/Obend/Vault/VerkleSnapshotBridge.lean`), unified DeOS multi-asset conservation, ZoE seat floors, and crash-safe finality (`unifiedDeos_ledger_and_turn_sound`, `unifiedDeos_fastpath_and_simplex_finality_sound`), multilateral netting (`settleNetting_agrees_with_gross`), Swarm/LawDial seam synthesis (`synthesizePassingDelta_complete`), and `cSHAKE256`-bound Simplex BFT trace verification (`finalized_consistent`, `checkTrace_sound`). |
| **Corrigibility, Equilibrium & Durable Execution** | `lean/Obend/Judge.lean`, `lean/Obend/Judge/Genealogy.lean`, `lean/Obend/Judge/SvenvsCorrigibility.lean`, `lean/Obend/Run/VaultDurableBridge.lean`, `lean/Obend/Run/HyperLaw.lean`, `lean/Obend/Reasons.lean`, `lean/Obend/Reasons/UnifiedEquilibrium.lean` | Graded `Judge` registry (`Obend.Judge.registry`), self-judged succession (`succession_sound`, `lob_cost_necessary`), 3-tier `svenvs` constitutional corrigibility and proof-carrying actions (`pca_enveloped_safe`, `pca_strictly_subsumes_static_shield`), segmented OBL1 durable execution and linear capability-carrying plans (`transfer_conserves_custody_exact`), 2-safety non-interference (`checkHyperLaw2NonInterference_sound`), and unified Van Gelder / Gelfond-Lifschitz equilibrium semantics (`gamma_least`, `checkGLEquilibrium_sound`, `stratified_unique_glStable`). |
| **Certified Silicon, FPGAs, GPUs & Multiphysics** | `lean/Obend/Lower/ExprCAM.lean`, `lean/Obend/Lower/SiliconElabFabric.lean`, `lean/Obend/Lower/Proofs/SiliconKernel.lean`, `lean/Obend/Tactic/SiliconElab.lean`, `lean/Obend/Hardware/Square.lean`, `lean/Obend/Hardware/Fabulous/Mac8.lean`, `lean/Obend/Hardware/Gpu/Memory.lean`, `lean/Obend/Hardware/Gpu/Rdna2/Certified.lean`, `lean/Obend/Analysis/TaylorModel.lean`, `lean/Obend/Analysis/Flowpipe.lean`, `lean/Obend/Analysis/Hybrid.lean`, `lean/Obend/Apps/FocHil.lean` | 6-bit-typecode 64-bit `ExprCAM` + 5-stage `SiliconElabFabric` kernel gate (`silicon_kernel_5stage_check_sound`), DPR `silicon_simp` hardware specialization (`silicon_elab_residual_dpr_specialize_sound`), `rtl_eq_gpu` hypergraph lowering, FABulous MAC8 bitstream readback (`mac8_fabric_realizes_module`), Vulkan scope gluing (`allowed_iff_glues`), RDNA2 binary validation (`certifyDump_sound`), Stockham Goldilocks NTT (`encoded_dft_of_uploads`), Picard/Taylor/hybrid ODE flowpipes (`taylorModel_picard_sound`, `flowpipe_safety_admits_contract`, `verifyFlowpipe_sound`), and FOC-HIL motor control RTL (`obend-emit-sv`). |
| **Executable Vertical Trailblazers** | `lean/Obend/Trailblaze/Obligations.lean`, `lean/Obend/Trailblaze/Polis.lean`, `lean/Obend/Trailblaze/LeanFpga.lean`, `lean/Obend/Trailblaze/ZkStripe.lean`, `lean/Obend/Trailblaze/ClusterGov.lean`, `lean/Obend/Trailblaze/CathedralApex.lean` | End-to-end vertical composition theorems spanning Blum memory checking + seL4 Microkit SPSC isolation (`apex_polis_deos_turn_safe`), Lean-to-FPGA Rung 2..5 FABulous + DPR isolation (`apex_lean_fpga_rung2_to_rung5`), `ZkStripe` VPA call-tree audit (`apex_zkstripe_calltree_audit`), Ozaki schedule-invariant AI cluster steps (`ozaki_closes_schedule_covert_channel`), and the unified Cathedral composition (`apex_cathedral_zkstripe_to_clustergov_sound`). |
| **FFI Bridge & Rust Host** | `lean/Obend/FFI/Bridge.lean`, `crates/obend-ffi`, `crates/obend-sandbox`, `crates/obend-gui` | Single-threaded thread-affine (`!Send + !Sync`) C ABI backed by `Obend.Vault.Replay.Session`, `.obend` elaboration via `Obend.Spec`, `Obend.Judge.registry` witness verification, Linux `bwrap` / macOS Seatbelt SBPL sandboxing, and streaming `.vcd`, `.stl`, `.ngc` parsers. |

---

## Repository Layout

- `lean/Obend/` — Verified Lean 4 core (`Core`, `Intention`, `Slot`, `Leaf`), categorical & realizability repair spine (`Category`, `Repair`), dual-track cryptography (`Crypto`), front-end (`Spec`, `Elab`, `Law`), document graph (`Doc`), durable sharded vault & markets (`Vault`, `Reasons`, `Ledger`, `Consensus`, `Run`), certificate & corrigibility registry (`Judge`), Lean-to-silicon lowering (`Lower`), hardware/GPU/multiphysics (`Hardware`, `Analysis`, `Apps`), and vertical compositions (`Trailblaze`).
- `lean/c/obend_bridge.c` — Thin C ABI shim exporting `lean/Obend/FFI/Bridge.lean` entrypoints into `libobend_Obend.so` with explicit single-threaded Lean heap affinity (`m_rc > 0`).
- `crates/obend-ffi/` — Safe `!Send + !Sync` Rust bindings over the Lean C ABI (`ObendSession`, `Receipt`), linking directly against the compiled Lean shared library.
- `crates/obend-sandbox/` — Confinement primitives (`LaunchGate`, `GrainExecutor`, `CpuMeter`, Linux `bwrap`, macOS Seatbelt SBPL) for untrusted external solvers and toolchains.
- `crates/obend-gui/` — Streaming `.vcd` waveform, `.stl` mesh, and `.ngc` G-code parsers alongside an interactive PIDE client over `obend-ffi`.
- `quarry/obend-apex.toml` — Whole-system compositional assurance manifest audited by `obb apex check`.

---

## Remote Build & Verification Discipline

> **Never run `lake` or `lean` on macOS laptops.** All Lean builds, tier-2 teeth/census runs, and shared-library FFI link checks execute on dedicated Linux build hosts (`bb2` / `hbox`), orchestrated via `obb` (`obb broker`, `obb lint`, `obb cone`, `obb apex check`, `obb pipeline check`).

On a Linux build host (`bb2` or `hbox`), build Tier 1, executables, and Tier 2 (`Obend.Census`, `Teeth`, `Tests`) from `lean/`:

```bash
cd lean
lake build Obend obend obend-emit-sv
lake build Obend.Census Teeth Tests
```

Run the CLI walkthroughs and Rust workspace test suite on the Linux build host against `libobend_Obend.so`:

```bash
python3 lean/tests/vault/walkthrough.py --doc lean/tests/reasons/REASONS.md
python3 lean/tests/vault/walkthrough.py --doc lean/tests/vault/SWARM.md
cargo test --workspace
```

Run static architectural, cone, pipeline, and whole-system apex checks via `obb`:

```bash
obb cone
obb lint
obb apex check --manifest quarry/obend-apex.toml
obb pipeline check --require-sealed
```

Compile-time metatheoretic and documentation integrity gates live in `lean/Obend/AssertAxioms.lean` (`#assert_axioms_tree`), `lean/Obend/AssertCompiled.lean` (`#assert_compiled`), `lean/Obend/Tactic/Tooth.lean` (`#tooth`), and `lean/Obend/Tactic/DocsCensus.lean` (`#check_docs_census`, `#docs_census`, `#census_environment`).

---

## Documentation Map

- `AMBITION.md` — System scope and unifying architectural principles.
- `THESIS.md` — Contextual `Intention` and `Slot` discipline, categorical open-system refinement, and scar-free realizability repair.
- `DESIGN.md` — Technical design across `Core.Term`, `Core.Ty`, rows, `Slot`/`Leaf`, `Doc`, `Vault`, `Reasons`, `Ledger`, `Judge`, `Hardware`/`Gpu`, and `FFI`.
- `METATHEORY.md` — Soundness theorems, step-indexed Galois refinement, `QuotAssembly`, Van Gelder / Gelfond-Lifschitz equilibria, Dual-Track PCS, and `#tooth` falsifiability.
- `GROUNDING.md` — Byte-level wire codecs, `cSHAKE256` digests, 256-bucket `ChunkedWorld`, Dual-Track commitments, `glEquilibriumJudge`, and silicon/device models.
- `PLAN.md` — Converged subsystem boundaries, dataflow pipelines, `silicon_simp` / `FOC-HIL` targets, and remote verification gates.
- `HARDWARE.md` — RTL, Yosys LEC, HVM lowering, FABulous MAC8 bitstreams, `FOC-HIL` (`foc-hil`), Square hypergraphs, WGSL, Vulkan memory scopes, RDNA2 binary validation, and Goldilocks NTT.
- `PHYSICAL.md` — Certified interval/Taylor/SOS/hybrid ODE analysis, `devsim-dd1d@1` Sky130 diode drift-diffusion, `cam-gouge@1` CNC toolpath verification, and SDR FT8 receiver proofs.
- `SILICON-ELABORATOR.md` — 6-bit-typecode `ExprCAM`, 5-stage `SiliconElabFabric`, and DPR `silicon_simp` hardware specialization (`Obend.Lower.Proofs.SiliconKernel`).
- `QUALIFICATION-AND-SILICON-LEAN.md` — Trust base qualification, `#tooth` falsifiability, `#assert_axioms_tree`, and `#docs_census`.
- `DEOS-CONTRACTS-CONSENSUS.md` — Durable `Vault` state, `Form` membranes, `Transport`, `Retention`, `Reasons`, `Ledger`, `Judge.Genealogy`, and `SimplexProtocol` / `SimplexTrace`.
- `NEXT-MATHEMATICA.md` — Structured `.obnb` documents, `Doc.Structured` lossless projections, certified symbolic algebra (`AutoCert`), and interactive FFI sessions.
