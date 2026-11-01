# Objective Bend

Objects anyone can extend without forking, laws judged on every write, documents that remember why
they say what they say, a bidirectional bridge to Lean 4 and real mathematical analysis, a
proof-carrying smart contract and DeOS surface substrate, and a verified compilation spine from
Lean and Core4 all the way to self-reconfiguring eFPGA tiles and open-foundry ASICs. Built to
become the symbolic, analytic, and physical core of what comes after Mathematica.
[`AMBITION.md`](AMBITION.md) says where this goes.

## The idea in a paragraph

A specification is a layer that sees the whole it will become (`self`) and the thing it extends
(`super`); anyone may add a layer later without reading or copying yours; `fix` closes the stack
lazily, so a partial object is still a value you can inspect, extend and judge. Laws are lines
people can read, judged at the moment someone tries to change something, inheritable along the C4
precedence list from the nominal kind of thing you made and from the packages you extend; a refusal
tells you which ancestor and clause said no and—via constructive difference-constraint synthesis—what
multi-field edit would pass. Decisions that are not ready stay open as slots with their
justifications, which can be withdrawn and repaired. Every admission is a re-executed check of a
certificate the kernel did not search for, every receipt says in which regime its answer was
established (`∨ HashBytes.Collision H`), and specialized leaf books—in software, in BendTT, or on
a dynamically reconfigured FPGA tile—run while their pinned supports hold and deoptimize to the
demand machine the instant a pin moves.

```
record Review:
  review(value: Nat) -> Nat
  twice(value: Nat) -> Nat

spec Base for Review:
  def review(value: Nat) -> Nat:
    value + 1n

spec Twice for Review:
  requires review(value: Nat) -> Nat
  def twice(value: Nat) -> Nat:
    self.review(self.review(value))

spec Augmented for Review:
  def review(value: Nat) -> Nat:
    super.review(value) + 1n

def twiceOfThree() -> Nat:
  fix(compose(Base, Twice, Augmented), {}).twice(3n)
```

```
$ obend run Review.obend twiceOfThree
result: 7
```

## What is here

Everything lives in [`lean/`](lean/), a Mathlib-free Lean 4.35 library: **408+ modules, 52,368
package constants across 622 build jobs, zero `sorryAx`, and zero custom axioms**, enforced by a
whole-tree filesystem/environment census ([`Obend/Census.lean`](lean/Obend/Census.lean)) and
kernel proof-mutation suites (`#tooth`) that verify every headline theorem fails when its
underlying definition is faulted. Full theorem-by-theorem accounting is in [`METATHEORY.md`](METATHEORY.md).

| library | what it is |
|---|---|
| `Core` | the Core4 calculus (lazy open recursion, reflection, activities, record `split` destructor) with call-by-name reference semantics and a call-by-need demand machine proved equal to it; one bidirectional checker (`checkAgainst`) complete on a stated fragment; `#kind` nominal record branding (`Nominal`); linear resource conservation (`step_conserves_linear`) and source subject reduction (`SubjectReduction`); version-bound portable checked-code quotation (`Code Ψ A θ`, `encodingVersion_binds`) |
| `Spec`, `Elab` | the `.obend` front end, cross-package `package … extends …` over C4 linearization, orthogonal protocols, surface law compiler (`LawCompile`), and the law confluence/repair dial (`LawDial`: `dial_free_confluent` join-semilattice closure and Bellman-Ford `solveLawWitness_sound` multi-field witness synthesis) |
| `Law` | laws by occasion as closed terms, judged by re-executing a machine probe (`judge_sound`/`judge_complete`), inheriting along the C4 ancestry with the refusing ancestor named (`judgeEffective_names`), `keeps` invariant claims (`chain_keeps`), and inductive proof-carrying `CellContract`s with `Narrows` forever-crowns |
| `Slot`, `Intention`, `Kind` | deferred decisions (`Slot`): candidates, withdrawable supports, `Integrity.contextual`, incumbent-first selection with chooser override; nominal `Kind` cells with C4 lineage pins (`kind_stale_iff_blocked`); one unified `Intention` module across package parents, wikilink cites, and kind pins (`resolve`/`recite`/`renew`) |
| `Fold`, `Judge`, `Receipt` | the audited fold (`Fold.Admission`, `receipt_sufficient`); the certificate `Judge` registry (`Format`, `bidirectional`, `Lrat`, `Certified`, `trial-balance@1`, `impact@1`, `lower@1`, `transport@1`, and 10 `Hardware` signoff formats); cSHAKE256 Merkle-dated `Receipt`s (`dated_sound`, `accepts_cited_sound`, `blind` multiproofs, and the 3-position disclosure dial) |
| `Run` | the guarded runner (`refines`), capability-gated reflective mirrors (`Run/Reflect`: `forged_descriptor_refused`), the shared-World ledger (`joint_reachable_ticket_exclusive`), durable recovery (`Run/Durable`), and atomic offline fork-and-stitch (`Run/Fork`: `stitch_atomic`, `runner_judges_escalation`) |
| `Logic` | program logic over open-recursive compositions: `late_binding` (`T1`), `rewrite_sound` (`T2`), `claim_frame` (`T3`: proofs survive unrelated layer overrides), ground evaluation, obligation slots, and notebook derivation turns (`Logic/Turn`) |
| `Leaf` | the prototype-flattening compiler (`flatten_sound`, `Residual.vtable_clean`: every `super` row partially evaluated away), first-order `Book` emitter (`book_sound`), specialization slot (`Specialize`: `specSlot`, `book_usable_sound`, `specialize_choice`, `moved_pin_blocks`), and `BendTT` compilation (`book_to_bendtt_sound`) |
| `Lower` | bidirectional Lean-lite ↔ Core4 bridge: `Fragment.read` (structural and well-founded recursion via `f.eq_def`), `lower_sound`, `lower_checks`, Tait–Girard converse simulation (`lower_complete_ltyped_nat`), outward reflection (`Transport.lowerTerm`, `transportTheorem`, `readTheoremDecider`), and 4-stage `Lean → Core4 → Book → RTL` compilation (`Proofs/Hardware`: `lower_to_rtl_sat_sound`, `lean_small_to_book_to_rtl`) |
| `Doc`, `Vault` | pages as graphs, patches, Pijul pushout merge (`merge_isPushout`) with conflicts as first-class section slots, identity and byte cites, backlinks, C4 `_kind.md` vault inheritance, constructive law repair (`Vault/Law`: `suggestMultiField_admits`), and `.obnb` structured `Content.cell` projections |
| `Ledger` | double-entry streaming accounting as an audited fold (`ledgerFold`, `conserved`, `net_conserved`, `closed_forever`, `reversal_cancels`, `stitch_twice_refused`), trial-balance coverage judge (`trial-balance@1`), conserved multi-asset `Book`, ZoE `Seat`s, and certified DrEX LP clearing |
| `Analysis`, `Journal` | static admissibility setups and change-impact cones (`read3_sound`, `impact_complete`), trace replay, non-omission coverage (`Coverage`), and the whole-repo proof dependency journal (`lean/Journal`) |
| `Hardware` | 26-module verified silicon, multiphysics, photonics, PCB, RF/DSP, and agentic CAD/EDA stack (`HDL`, `Types`, `Rules` ORAAT, `FSM`, `Compiler` whole-book & sequential `Nat.rec`, `ReductionMachine` distributed slot-reduction automaton & glitch-free `ICAP` eFPGA Dynamic Partial Reconfiguration, `Synth` `LUT2`/`LUT3`/`CARRY8`, `Retiming` Leiserson–Saxe, `PlaceRoute` bitstream judge, `FabuBlox` cleanroom & RIE/ALD physics, `DRC`, `Analog` Prouhet–Thue–Morse 2D curvature cancellation & SAR ADC, `WaferSpace` `gf180mcuD`/`sky130A`/`ihpSg13g2` signoff, `Thermal` Brokaw bandgap & RC PRIMA, `Datasheet`, `Circuits`, `RF` Tayloe SDR & Class-E PA, `Physics` Scharfetter–Gummel PDD, `Photonics` MZI/MRR, `PCB` IPC-2152 & serpentine skew, `DSP` CORDIC/CIC/FIR/ULA, `AgenticEDA`), backed by 32 `#tooth` mutation checks and Verilator/Z3/C++20 co-simulation (`32/32`) |

## Reading

- [`AMBITION.md`](AMBITION.md) — the destination: "The Next Mathematica," DeOS, proof-carrying smart contracts, Futamura staging, and the Silicon Lean Elaborator.
- [`THESIS.md`](THESIS.md) — the eleven claims stated so they can be wrong, and what is proved of each.
- [`DESIGN.md`](DESIGN.md) — the architecture as built and as expanding across all 12 subsystems.
- [`METATHEORY.md`](METATHEORY.md) — the mechanized theorems, the proof tools, and the remaining frontier.
- [`PLAN.md`](PLAN.md) — the workstreams, gates, and lane reports.
- [`NEXT-MATHEMATICA.md`](NEXT-MATHEMATICA.md) — the 5-phase blueprint unifying `Obend`, `minidregg`, and `Dregg2`/`DeOS` with Lean 4 tactic reflection, `.obnb` structured cells, and the thin Rust GUI/FFI.
- [`SILICON-ELABORATOR.md`](SILICON-ELABORATOR.md) — the design for Futamura-specializing the Lean 4 kernel (`Lean4Lean`) and elaborator (`Lean.Elab`) through `Obend/Lower` → `Obend/Leaf` → `Obend/Hardware` onto dynamically reconfigurable eFPGA tiles (`ReductionMachine`) and custom ASICs.
- [`DEOS-CONTRACTS-CONSENSUS.md`](DEOS-CONTRACTS-CONSENSUS.md) — the design for proof-carrying smart contract Vaults (`CellContract`, `VaultTurn`, `Book`, `Seat`, `Clearing`), DeOS capability surfaces (`GatedAffordance`, `FogOfWar`, `Mandate`, Sandstorm grains), and the 4-tier finality ladder (`LawDial` CRDT → `Simplex` BFT → `EpistemicConsensus`).
- [`GROUNDING.md`](GROUNDING.md) — lineage, prior-tree synthesis (`minidregg`, `nanodregg`, `breadstuffs`/`Dregg2`/`DeOS`), and architectural decision history.

## Who

Ember ([ember.software](https://ember.software)), with Claude, Gemini, Astra and Kimi doing a great
deal of the reading, arguing and typing. Faré's work is the object foundation; Victor Taelin's Bend
is the affine leaf we stand on. AGPL-3.0.
