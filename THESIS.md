# Objective Bend: the thesis, what the research supports, and what is proved

Stated 2026-10-29; revised 2026-11-01 after landing `C1`, `C2`, `Sound`, `OneChecker`, `Demand`/`Ticks`,
`Impact`, `Logic`, `Leaf`/`BendTT`, `Lower`, `LawDial`, `Ledger`, and `Hardware` (52,368 constants
across 622 build jobs in `lean/`, zero `sorryAx`, zero custom axioms). Status words: **PROVED** (a
kernel-checked theorem in `lean/`), **SUPPORTED** (mechanized on a core fragment with the full
extension underway), **OPEN** (next frontier).

## 1. The core thesis, stated so it can be wrong

Bend's pitch is: laws + proofs + a fast compiler, and the thing that makes all three possible is
*affinity* (BendTT: live code may not copy a function; that is what lets `Type : Type` and negative
datatypes stay consistent, lets a `match` free its node, and makes fork-join parallelism free).
"LAWS.bend is AGENTS.md backed by proof."

The thesis of this repository is that **for the thing people want out of Bend—a shared world where
AI and humans build mathematics, software, contracts, and hardware together under rules that cannot
be broken—affinity is the wrong load-bearing wall at the top, and Faré's lazy open-recursive object
model + contextual truth-maintenance slots is the right one, with affine BendTT and hardware tiles
serving as the compiled leaf target.** Specifically:

1. **Core4 gives a reusable `self` a non-affine source semantics on purpose, and compiles late
   binding away at the leaf boundary.** `fix spec seed ⟶ spec (fix spec seed) seed` hands one
   `self` to every layer and uses it as many times as there are methods. Where a composition is
   closed, `Obend/Leaf` flattens `self` and `super` statically into a vtable and emits a first-order
   `Book` and a `BendTT` net with zero runtime vtable or `super` records left behind.
   **PROVED**: `late_binding` (`Obend/Logic/LateBinding.lean`), `flatten_sound` (`Obend/Leaf/Flatten.lean`),
   `vtable_clean` (`Obend/Leaf/Residual.lean`), `book_sound` (`Obend/Leaf/Emit.lean`), and
   `book_to_bendtt_sound` (`Obend/Leaf/BendTT.lean`).
2. **Laziness is necessary for partial objects and compositional specs, and its two-stage demand
   cost is bounded within a small constant of clairvoyant call-by-value.** `{good=7, bad=self.bad}.good`
   must be 7; a law or view over an object other people are still specifying is a partial
   specification. Lazy *selection* of demanded work and parallel/hardware *execution* of demanded
   leaves do not conflict.
   **PROVED**: Call-by-name reference semantics equals the call-by-need demand machine
   (`Obend/Core/Proofs`); Xia's least-demand theorems (`demand_is_least`), `mix_assoc_cost` within a
   factor of 8, and `ticks_within_fragment` at constant 4 (`16` ticks for a literal, `19 + 6d` for a
   chase; [`Obend/Equiv/Demand.lean`](lean/Obend/Equiv/Demand.lean), [`Obend/Core/Proofs/TickCost.lean`](lean/Obend/Core/Proofs/TickCost.lean)).
3. **The right "linearity" for a law and inheritance system is Faré's C4 linearization; Girard's
   resource linearity belongs to custody and conserved ledgers.** LTUO §7.3.5.2: every ancestor's
   contribution is counted *once and only once* in the C4-linearized composition. Meanwhile, true
   single-use resource custody is enforced by `Quantity.linear` in the bidirectional checker and
   conserved across reductions and double-entry ledger folds.
   **PROVED**: Structural C4 linearization (`Obend/Spec/C4.lean`), nominal `#kind` branding
   (`kinded_refuses`, `kinds_never_agree` in `Obend/Core/Nominal.lean`), linear step conservation
   (`step_conserves_linear` in `Obend/Core/Proofs/Conservation.lean`), source subject reduction
   (`Obend/Core/Proofs/SubjectReduction.lean`), aggregate `split` accounting (`Obend/Core/Proofs/Aggregate.lean`),
   and ledger conservation (`conserved`, `net_conserved`, `vault_conserved` in `Obend/Ledger/`).
4. **Laws are judged at the point of use, inherit along C4, and synthesize constructive repairs when
   refused.** What users and agents need is a judge on every write that names the refusing ancestor
   and clause, plus a solver that tells a refused caller what multi-field change would be admitted.
   **PROVED**: `judge_sound`/`judge_complete`, `legal_law_admitted`, `package_never_widens`,
   `judgeEffective_names`, `chain_keeps` (`Obend/Law`), difference-constraint witness synthesis
   (`solveLawWitness_sound` in `Obend/Spec/LawDial.lean`), and constructive Vault repair suggestions
   (`suggestMultiField_admits` in `Obend/Vault/Law.lean`).
5. **Extensible, contextual theories are all instances of one object: the `Slot` (`Obend.Slot`) and
   its boundary reference, the `Intention` (`Obend.Intention`).** CMTT for contextual typing,
   ATMS/Doyle for withdrawable supports, incumbent-first selection with chooser override, and exact
   stale-pin blocking (`stale_iff_blocked`).
   **PROVED**: `Obend.Slot` (`Integrity.contextual`), `Obend.Intention` (unifying package parents,
   document cites, and `KindPin`s with `resolve`/`recite`/`renew`), `Obend.Analysis.Impact`
   (`read3_sound`, `impact_complete`), and `Obend.Run.Fork` (`stitch_atomic`).

## 2. The extended thesis: "The Next Mathematica," DeOS, Simplex, and the Silicon Elaborator

6. **The symbolic core of a system that reasons over heterogeneous domains is a certificate-checking
   fold over quoted terms, not a monolithic rewriter.** Rewriters, SAT/SMT solvers, LP market
   clearers, e-graphs, and real-analytic (`tauceti`/interval/SOS) engines are untrusted producers;
   the kernel holds terms as version-bound data (`quote` / `Code Ψ A θ`), runs a small registry of
   total `Judge`s, and emits cSHAKE256 Merkle-dated receipts (`∨ HashBytes.Collision H`).
   **PROVED**: `Obend/Core/Code.lean` (`encodingVersion_binds`, `import_roundtrip`, `import_complete`,
   `splice_typed`), `Obend/Equiv/Quote.lean` (`≈q ⊆ ≈r ⊆ ≈b`, `rewrite_sound_below`),
   `Obend/Judge.lean` (`Lrat`, `Certified`, `trial-balance@1`, `impact@1`, `lower@1`, `transport@1`,
   and 10 `Hardware` formats), and `Obend/Receipt.lean` (`dated_sound`, `accepts_cited_sound`).
7. **Syntactic `keeps` is only Tier 0; real smart-contract and notebook specifications require
   inductive `CellContract`s, `Narrows` forever-crowns, and fluid bidirectional Lean 4 reflection.**
   Because `Claim.checkKeeps` demands raw AST identity (`isGuardCond`), it rejects compiled surface
   laws and non-inductive invariants (`keeps_tooth`). Superseding `keeps` with semantic 2-state
   inductive `CellContract`s (`Holds inv old → Admits law old new req → Holds inv new`) and piping
   `Leaf.Flatten` into `Lower.Transport.lowerTerm` lets any `Obend` prototype method or law pop out
   into Lean 4 (`obend_unfold`, `obend_law`, `obend_split`, `obend_tooth`) and weave back as a
   support-pinned `TransportedSlot` certificate (`byLoweredLean`).
   **PROVED** for first-order `Lower` (`lower_sound`, `lower_checks`, `lower_complete_ltyped_nat`,
   `transportTheorem`, `readTheoremDecider` in `Obend/Lower/`); **IN PROGRESS** across arbitrary
   flattened prototypes and `CellContract` in Phase 1 (`NEXT-MATHEMATICA.md`).
8. **Confluent laws (`LawDial.free`) and contended multi-cell turns (`Simplex` BFT) belong to one
   4-tier finality ladder, and distributed proof/EDA search is `EpistemicConsensus`.** Monotone
   per-field bounds (`DialVerdict.free`) close under pointwise `max` (`joinData`) and merge in
   0.5 RTT without coordination, whereas non-confluent disjunctions/sums (`demoOr_not_confluent`)
   require atomic wide-pullback `VaultTurn` hyperedges ordered in 1 RTT (single-owner/disjoint
   footprint) or 2 RTT (contended `GenericSimplex` BFT). Conversely, when multiple agents race to
   prove a `ClaimObj`, clear an order book, or place-and-route a circuit, any valid certificate
   suffices and canonical cost+digest tie-breaking (`EpistemicConsensus`) achieves agreement without
   BFT rounds.
   **PROVED**: `dial_free_confluent` and `demoOr_not_confluent` (`Obend/Spec/LawDial.lean`), plus
   `GenericSimplex`, `Hyperedge`, `Seat`, `CertifiedClearing`, and `EpistemicConsensus` in
   `~/dev/minidregg`, now being absorbed into `Obend/{Vault,Ledger,Judge,Consensus}` (`DEOS-CONTRACTS-CONSENSUS.md`).
9. **A compiler's assumptions are supports, its deoptimization is slot repair, and on an eFPGA that
   slot is glitch-free Dynamic Partial Reconfiguration (`ICAP` DPR)—enabling a Silicon Lean
   Elaborator.** In `Obend/Leaf/Specialize.lean`, `specSlot` holds `[Candidate.book name C, Candidate.machine]`:
   the specialized `Book` runs while its layer/object pins hold (`book_usable_sound`) and falls back
   to `.machine` the instant a pin changes (`specialize_choice`, `moved_pin_blocks`). In
   `Obend/Hardware/ReductionMachine.lean`, that exact `Book` compiles to hardware `AutomatonTile`s
   (`automaton_simulates_book`) hot-swapped via a 3-phase glitch-free `ICAP` DPR protocol
   (`dpr_preserves_neighbor_tiles_and_packets`, `dpr_specialized_tile_executes_new_book`). Extending
   `Obend/Lower/Fragment.lean` with recursive inductives (`Lean.Expr`, `Lean.Level`, `Lean.Syntax`)
   allows Lean's kernel (`Lean4Lean`), partial evaluator (`Leaf.Flatten`, giving the 2nd and 3rd
   Futamura projections), and elaborator passes to lower through `Core4` and `Leaf.Book` directly
   into reconfigurable FPGA tiles and custom ASICs (`SILICON-ELABORATOR.md`).
   **PROVED**: `specSlot` (`Obend/Leaf/Specialize.lean`), 4-stage `Lean-lite → Core4 → Book → RTL`
   (`Obend/Lower/Proofs/Hardware.lean`), and `AutomatonNetwork` + Glitch-Free DPR
   (`Obend/Hardware/ReductionMachine.lean`).

## 3. What would refute it

- A member who cannot extend a stranger's package without reading or copying it (tested by
  `tests/obend-source/stranger/`).
- A law refusal that fails to name the refusing ancestor/clause or fails to synthesize a passing
  delta when one exists in the `LawDial` fragment (tested by `suggestMultiField_admits`).
- A theorem in `lean/` that still compiles when the definition it claims to guard is mutated (refuted
  mechanically by `#tooth` across `Obend/Teeth/`).
- A receipt accepted by `obend verify` whose openings omit a read fact, whose trust claims `checked`
  for an unrun check, or whose root mismatches without exhibiting a `cSHAKE256` collision (refuted
  by `dated_sound`, `accepts_cited_sound`, and the 32 forgery tests in `tests/run-receipts.py`).
- A specialized software `Book` or reconfigured eFPGA `AutomatonTile` that either diverges from the
  demand machine while its `specSlot` pins hold, or glitches neighboring tiles during `ICAP`
  reconfiguration (refuted by `book_usable_sound`, `automaton_simulates_book`, and
  `dpr_preserves_neighbor_tiles_and_packets`).
