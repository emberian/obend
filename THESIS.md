# Thesis: Contextual Intentions, Graded Slots, and Residual Membranes

A persistent system must simultaneously support **late binding** (overriding open-recursive prototypes, merging concurrent document edits, delegating scoped capabilities, upgrading judges) and **static certainty** (fast specialized code, cached type checks, valid Merkle receipts, non-amplifying authority).

Obend resolves the tension between late binding and static certainty through three tightly coupled abstractions:

1. **`Obend.Slot.Slot`** (`lean/Obend/Slot.lean`) — fine-grained support tracking and exact staleness diagnosis.
2. **`Obend.Intention`** (`lean/Obend/Intention.lean`) — world-indexed resolution and renewal of pinned selections.
3. **Residual Membranes & Checked Carry (`Obend.Vault.Form`, `Obend.Vault.CheckedCarry`)** (`lean/Obend/Vault/Form.lean`, `lean/Obend/Vault/FormCheck.lean`, `lean/Obend/Vault/CheckedCarry.lean`) — partial evaluation of authorization laws into self-contained residual obligations and rerooting-safe capability plans.

---

## 1. `Slot` and `Intention`: Explicit Support Footprints

In `lean/Obend/Slot.lean`, a `Slot Fact Cand` pairs a boolean acceptance predicate `judge : Cand → Bool` with a footprint function `supports : Cand → List Fact`:

- A candidate `c` is usable under `holds : Fact → Bool` iff `judge c = true` and every `f ∈ supports c` holds (`usable_iff`).
- Reading a slot (`Slot.read`) returns a four-valued `Reading Fact Cand`:
  - `usable c sup` — `c` passes `judge` and every `f ∈ sup` holds (`read_usable_supports`).
  - `blocked c dead` — `c` passes `judge`, and `dead` is the exact non-empty list of falsified support facts (`read_blocked_exact`, `mem_dead_iff`).
  - `rejected c` — `c` fails `judge`.
  - `empty` — no candidate is supplied.

`Obend.Intention W Ref Pin Fact Err` (`lean/Obend/Intention.lean`) lifts `Slot` over an evolving world `w : W`:
- `resolve : W → Ref → Except Err Pin` produces a pin whose reference matches (`resolve_fill`) and whose supports all hold in `w`.
- `current_iff_usable` and `stale_iff_blocked` connect world evolution directly to `Slot.read`: a pin remains valid across any world transition that preserves its finite `supports` (`stays`), and when invalidated, `renew` re-establishes currency (`renew_repairs`).

In `lean/Obend/Slot/World.lean`, monotonic world reachability (`Reaches`) yields permanent non-revival guarantees when a permanently falsified fact blocks a candidate (`blocked_forever`, `stale_blocked_forever`), while demonstrating why returning pins require collision-resistant identity rather than linear version numbers (`pin_returns`, `collision_needed`, `no_exact_order`).

---

## 2. Five Instantiations of One Discipline

| Domain | Module | Pin / Candidate | Support Facts & Refusal Theorem |
| :--- | :--- | :--- | :--- |
| **Open-Recursive Specialization** | `lean/Obend/Leaf/Specialize.lean`, `lean/Obend/Leaf/Static.lean` | `Candidate` (`book` vs `machine`) in `specSlot` | `LeafPin` member digests; `moved_pin_blocks` and `specialized_moved_pin_blocks` block specialized vtables the instant an overridden field moves, falling back cleanly to `machine_usable`. |
| **Protocol & Effect Envelopes** | `lean/Obend/Slot/Protocol.lean`, `lean/Obend/Judge/Instances.lean` | Indexed interaction trees `Prot S Hole A i` | Token/fact/obligation views (`View`, `Envelope`); `checkProt_sound` and `checkProt_complete` decide protocol admissibility. |
| **Document Citations & Cells** | `lean/Obend/Doc/Section.lean`, `lean/Obend/Doc/Structured.lean` | `Cite` spans and `StructuredCell` projections | Content atoms and `(String × ByteArray)` footprint pins; `SourceMoves` flags drifted transclusions and `stale_pin_invalidates` invalidates cached cell receipts. |
| **Capability Transport & Rerooting** | `lean/Obend/Vault/Transport.lean`, `lean/Obend/Vault/CheckedCarry.lean` | Scoped `Issue` / `Grants` / `CarryRequest` across vaults | Fresh display/effect pins (`recapture`); `transport_continues_iff`, `handoff_no_absence`, `merge_revocation_wins`, `live_capability_survives_rerooting`, and `fresh_revoked_capability_refused` prevent capability gaps or amplification. |
| **Architecture Docs Census** | `lean/Obend/Tactic/DocsCensus.lean` | `DocPin` over `DocEnvWorld` in `docIntention` | File paths, `Obend.*` constants, bare/qualified identifiers, and fenced `inductive` constructors; `docSlot_stale_iff_blocked` fails `#docs_census` on any drifted symbol or constructor. |

---

## 3. Residual Membranes and Single-Pass Checking

When a collaborator submits a turn against a vault page whose full state they are not permitted to read, `Obend.Vault.Form` (`lean/Obend/Vault/Form.lean`) avoids both ambient authority and blind trust:

1. **Partial Evaluation into a Membrane**: `NExpr.peval` partially evaluates page laws against known private state, producing a residual `Form` whose remaining free holes correspond exclusively to the proposer's disclosed parameters (`eval_subst_peval`, `eval_fill_eq_subst_residual`).
2. **Zero Information Leakage & Zero Amplification**: The residual expression reads nothing from hidden fields (`residual_reads_nothing_known`, `capture_hidden_absent`, `hidden_change_invisible_through_form`). Admitting a proposal or fill cannot amplify authority (`admit_no_amplification`, `admitFill_no_amplification`), leaves hidden fields untouched (`admit_hidden_untouched`), and conserves written and total quantities (`admit_conserves_written`, `admit_conserves_total`).
3. **Checked Once (`FormCheck`)**: `Obend.Vault.Form` in `lean/Obend/Vault/FormCheck.lean` and `lean/Obend/Vault/FormCheckCache.lean` compiles residual checks to `Obend.Core.Term` (`coreTerm_evaluates`), types every slot (`judged_typed`, `kept_typed`), and classifies `CheckUnit` keys so previously verified units incur zero redundant re-checks (`rechecked_zero`).

---

## 4. Defeasible Justification Without Self-Supporting Cycles

Static proofs establish that a transition satisfies a law; operational governance also requires tracking *why* an assertion or standing authorization remains in force as facts arrive or are retracted.

`lean/Obend/Reasons.lean` and `lean/Obend/Run/HyperLaw.lean` formalize both 3-valued well-founded justification and 2-valued modal stable equilibria over the same Gelfond–Lifschitz reduct operator `gamma`:
- Every atom receives a three-valued `Status` (`supported`, `undefined`, `unsupported`) computed by the least fixpoint of the two-step monotone operator `rounds` (`gamma_least`, `rounds_least`, `wf`).
- Positive cycles cannot bootstrap support (`no_conclusion_from_cycles`), an assertion survives as long as at least one valid derivation holds (`survives_one_support`), and established support can only be defeated by new counter-evidence (`defeat_only_by_evidence`, `action_needs_support`).
- For unstratified modal `□` equilibrium certificates (`gl-equilibrium@1`), `glEquilibriumJudge` (`gamma_same_iff_stableEquilibrium`, `checkGLEquilibrium_sound`) verifies exact `gamma` fixpoints while refusing self-defeating rules (`self_defeating_modal_refused_on_p`).
- Coupled with `Obend.Vault.Replay` (`justified_needs_support`, `forget_keeps_reasons`) and `Obend.Vault.UnifiedDeos` (`authorizedBy_worldReasonsCaveat_supported`), every live vault action rests on a cycle-free, replayable chain of evidence.
