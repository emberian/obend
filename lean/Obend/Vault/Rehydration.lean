module
/-
# Obend.Vault.Rehydration — Rehydratable Membranes, Derived Liveness Confinement Readouts, Functorial Rerender Square & 3D Reactive Affordances

Mechanizes the full **Rehydratable Membranes** featural architecture (`WS 33`), absorbing
`breadstuffs/docs/desktop-os-research/REHYDRATABLE-SURFACES.md`, `Dregg2/Deos/Rehydration.lean`,
`Dregg2/Deos/Rerender.lean`, `Dregg2/Deos/Reactive.lean`, and `starbridge-web-surface/src/rehydrate.rs`
cleanly onto `Obend.Vault.Affordance`, `Obend.Vault.Projection`, `Obend.Vault.Mandate`, and `Obend.Receipt`:

1. **Pillar 1 — The Derived `Rehydration` Liveness-Type as a Confinement Readout**:
   - `AttestedRoot` (`root`, `v4Complete`, `quorum`, `AttestedRoot.holds`), `Interaction` (`.attested ar | .ambient`),
     `Interaction.isWitnessed`, `InteractionLog`, `confined log`.
   - `inductive Rehydration | Live | ReplayedDeterministic | ReconstructedApproximate` and
     `classify (log : InteractionLog) (reachable : Bool) : Rehydration`.
   - Keystone Theorems: `replayedDeterministic_iff_confined`, `reconstructedApproximate_iff_unconfined`,
     `invalidAttestation_not_replayed`.
   - Replay Chain & Coverage Payoff: `rootOf`, `witnessedRoots`, `witnessChainOf`, `wellLinked`,
     `confined_chain_covers_log`, `unconfined_chain_drops_interactions`, `ambient_chain_drops_the_reach`,
     and `replayedDeterministic_replays`.
2. **Pillar 2 — `Sturdyref`, Per-Viewer `Membrane`, and Chained Multi-Hop Reshare Attenuation (`Membrane.reshare`)**:
   - `MembraneViewer` (`held : List Auth`, `permits : String → Bool`, `activeNames : List String`),
     `membraneShows`, `projectMembrane`.
   - Keystone Theorems: `membrane_two_viewers_distinct`, `membrane_authority_monotone`.
   - Chained Reshare Attenuation & `Sturdyref`: `Membrane.reshare` (`reshare`), `amplifying_reshare_refused`,
     `reshare_chain_attenuates`, `Sturdyref φ`, and `rehydrateSturdyref`.
3. **Pillar 3 — The Functorial Rerender Square & Frustum-Snapshot Per-Viewer Re-Expansion**:
   - `projectFor`, `stepContent`, `rerender_deterministic`, `rerender_idempotent`,
     `rerender_square` (The Commuting Square), `rerender_after_step_authorized`,
     `Snapshot φ`, `snapshot`, `rehydrate`, `snapshot_roundtrip`, `snapshot_roundtrip_attenuated`,
     and `snapshot_reexpansion_monotone`.
4. **Pillar 4 — 3-Dimensional `ReactiveAffordance` (`TransitionGate` + `[openHeight, closeHeight]` Window + `Membrane`)**:
   - `TransitionGate` (`pre`, `post`, `link : Data → Data → Bool`), `transitionOK`, `transitionOK_iff`.
   - `ReactiveAffordance φ`, `inWindow`, `reactiveOK`, `fireReactive`.
   - Keystone & 6 Cross-Polarity Teeth: `fireReactive_iff`, `fireReactive_all_pass`,
     `fireReactive_cap_fail_refuses`, `fireReactive_transition_fail_refuses`,
     `fireReactive_window_fail_refuses`, `fireReactive_wrong_old_refuses`,
     `fireReactive_after_deadline_refuses`, `fireReactive_window_reactive`,
     `fireReactive_carries_real_effect`, and `fireReactive_binds_attested_root`.
-/
public import Obend.Vault.Affordance
public import Obend.Vault.Projection
public import Obend.Vault.Mandate
public import Obend.Receipt
public import Obend.Slot
public import Obend.Slot.Protocol
public import Obend.Law.Contract
public import Obend.Law.Proofs.Claim
public import Obend.Law.Proofs.Std
public import Obend.Tactic.Tooth

public section

namespace Obend.Vault.Rehydration

open Obend.Core.Data (Data)
open Obend.Vault.Affordance (Auth fireGate fireGate_iff_subset fireGate_refl fireGate_trans
  CellAffordance FireCtx FiredSurface AffordanceIntent fire)

set_option autoImplicit false

variable {φ : Type}

/-! ## Pillar 1 — The Derived `Rehydration` Liveness-Type as a Confinement Readout -/

/-- **`AttestedRoot`** — the attestation a cap-gated cross-cell interaction carries:
    a state commitment `root` plus the two structural soundness flags (`v4Complete` and `quorum`). -/
structure AttestedRoot where
  root       : Nat
  v4Complete : Bool
  quorum     : Bool
deriving DecidableEq, Repr

/-- **`AttestedRoot.holds`** — the root structurally holds iff both `v4Complete` and `quorum` hold. -/
@[expose] def AttestedRoot.holds (ar : AttestedRoot) : Bool :=
  ar.v4Complete && ar.quorum

theorem attestedRoot_holds_iff (ar : AttestedRoot) :
    ar.holds = true ↔ (ar.v4Complete = true ∧ ar.quorum = true) := by
  unfold AttestedRoot.holds
  rw [Bool.and_eq_true]

/-- **`Interaction`** — one external interaction a context made: either an attested turn
    carrying an `AttestedRoot`, or an ambient reach outside the membrane. -/
inductive Interaction where
  | attested (ar : AttestedRoot)
  | ambient
deriving DecidableEq, Repr

/-- **`Interaction.isWitnessed`** — an interaction is a genuine witness iff it is an `.attested`
    interaction whose root structurally holds (`ar.holds = true`). -/
@[expose] def Interaction.isWitnessed : Interaction → Bool
  | .attested ar => ar.holds
  | .ambient     => false

/-- **`InteractionLog`** — the context's ordered external interaction trace. -/
abbrev InteractionLog := List Interaction

/-- **`confined log`** — every interaction in `log` was witnessed inside the membrane. -/
@[expose] def confined (log : InteractionLog) : Bool :=
  log.all Interaction.isWitnessed

/-- **`Rehydration`** — the derived liveness-type carried on every reacquisition. -/
inductive Rehydration where
  | Live
  | ReplayedDeterministic
  | ReconstructedApproximate
deriving DecidableEq, Repr

/-- Whether a `Rehydration` liveness-type is faithful by construction (`Live` or `ReplayedDeterministic`). -/
@[expose] def Rehydration.isFaithful : Rehydration → Bool
  | .Live                    => true
  | .ReplayedDeterministic   => true
  | .ReconstructedApproximate => false

/-- **`classify log reachable`** — derives the `Rehydration` liveness-type from the context's
    `InteractionLog` and whether live source contexts are reachable. -/
@[expose] def classify (log : InteractionLog) (reachable : Bool) : Rehydration :=
  if reachable then .Live
  else if confined log then .ReplayedDeterministic
  else .ReconstructedApproximate

theorem classify_live (log : InteractionLog) :
    classify log true = .Live := rfl

/-- **KEYSTONE (`replayedDeterministic_iff_confined`)**:
    For a non-`Live` context (`reachable = false`), `classify log false = .ReplayedDeterministic`
    if and only if `confined log = true`. -/
theorem replayedDeterministic_iff_confined (log : InteractionLog) :
    classify log false = .ReplayedDeterministic ↔ confined log = true := by
  unfold classify
  cases hc : confined log <;> simp

/-- **DUAL KEYSTONE (`reconstructedApproximate_iff_unconfined`)**:
    For a non-`Live` context (`reachable = false`), `classify log false = .ReconstructedApproximate`
    if and only if `confined log = false`. -/
theorem reconstructedApproximate_iff_unconfined (log : InteractionLog) :
    classify log false = .ReconstructedApproximate ↔ confined log = false := by
  unfold classify
  cases hc : confined log <;> simp

theorem attestedRoot_not_holds_of_false (ar : AttestedRoot) (hbad : ar.holds = false) :
    ¬ (ar.v4Complete = true ∧ ar.quorum = true) := by
  intro h
  have htrue : ar.holds = true := (attestedRoot_holds_iff ar).mpr h
  rw [hbad] at htrue
  contradiction

/-- **ANTI-GHOST TOOTH (`invalidAttestation_not_replayed`)**:
    If any `.attested ar` in `log` fails `ar.holds` (`ar.holds = false`), then a non-`Live`
    classification cannot be `.ReplayedDeterministic`. -/
theorem invalidAttestation_not_replayed (log : InteractionLog) (ar : AttestedRoot)
    (hbad : ar.holds = false) (hmem : Interaction.attested ar ∈ log) :
    classify log false ≠ .ReplayedDeterministic := by
  intro heq
  have hconf : confined log = true := (replayedDeterministic_iff_confined log).mp heq
  have hwit : (Interaction.attested ar).isWitnessed = true :=
    List.all_eq_true.mp hconf _ hmem
  have hparts : ar.v4Complete = true ∧ ar.quorum = true :=
    (attestedRoot_holds_iff ar).mp hwit
  exact attestedRoot_not_holds_of_false ar hbad hparts

/-- Structural flag form of `invalidAttestation_not_replayed`: if either `ar.v4Complete = false`
    or `ar.quorum = false` for any `.attested ar ∈ log`, then `classify log false ≠ .ReplayedDeterministic`. -/
theorem invalidAttestation_not_replayed_of_flags (log : InteractionLog) (ar : AttestedRoot)
    (hbad : ar.v4Complete = false ∨ ar.quorum = false) (hmem : Interaction.attested ar ∈ log) :
    classify log false ≠ .ReplayedDeterministic := by
  apply invalidAttestation_not_replayed log ar _ hmem
  unfold AttestedRoot.holds
  rcases hbad with hv4 | hq
  · rw [hv4, Bool.false_and]
  · rw [hq, Bool.and_false]

/-! ### Replay Receipt Chain & Coverage Payoff -/

/-- The fixed genesis sentinel pinning the oldest receipt in a chain. -/
@[expose] def genesisSentinel : Nat := 0

/-- Per-turn witnessed receipt record in the append-only persistence chain. -/
structure WitnessReceipt where
  prevHash    : Nat
  oldCommit   : Nat
  newCommit   : Nat
  effectsHash : Nat
deriving DecidableEq, Repr

/-- Append-only receipt chain, newest-first. -/
abbrev ReceiptChain := List WitnessReceipt

/-- **`wellLinked H c`** — structural append-only link discipline: reading `c` newest-first,
    every receipt's `prevHash` equals `H` of its immediate predecessor, and genesis pins `genesisSentinel`. -/
@[expose] def wellLinked (H : WitnessReceipt → Nat) : ReceiptChain → Prop
  | []             => True
  | [g]            => g.prevHash = genesisSentinel
  | r :: p :: rest => r.prevHash = H p ∧ wellLinked H (p :: rest)

theorem wellLinked_append {H : WitnessReceipt → Nat} {r head : WitnessReceipt} {tail : ReceiptChain}
    (hwl : wellLinked H (head :: tail)) (hlink : r.prevHash = H head) :
    wellLinked H (r :: head :: tail) :=
  ⟨hlink, hwl⟩

theorem genesis_is_last {H : WitnessReceipt → Nat} (HFresh : ∀ p, H p ≠ genesisSentinel)
    {r : WitnessReceipt} {tail : ReceiptChain}
    (hwl : wellLinked H (r :: tail)) (hgen : r.prevHash = genesisSentinel) : tail = [] := by
  cases tail with
  | nil => rfl
  | cons p rest =>
    have hlink : r.prevHash = H p := hwl.1
    exact absurd (hgen ▸ hlink).symm (HFresh p)

/-- **`chain_tamper_evident_or`** — two well-linked chains sharing the same head receipt are
identical, or the receipt hash failed (`Bad`; at a real hash, its collision). This is the
spine's form (`Obend.Receipt.chain_binds_or`): `Function.Injective H` holds of no fixed-width
hash of an infinite type, so `chain_tamper_evident` below says nothing at `deployed`. -/
theorem chain_tamper_evident_or {H : WitnessReceipt → Nat} {Bad : Prop}
    (HBind : ∀ a b, H a = H b → a = b ∨ Bad) (HFresh : ∀ p, H p ≠ genesisSentinel) :
    ∀ (c d : ReceiptChain), wellLinked H c → wellLinked H d →
      c.head? = d.head? → c = d ∨ Bad := by
  intro c
  induction c with
  | nil =>
    intro d _ _ hhead
    cases d with
    | nil => exact .inl rfl
    | cons => simp at hhead
  | cons r ctail ih =>
    intro d hc hd hhead
    cases d with
    | nil => simp at hhead
    | cons s dtail =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      cases ctail with
      | nil =>
        have hgen : r.prevHash = genesisSentinel := hc
        rw [genesis_is_last HFresh hd hgen]
        exact .inl rfl
      | cons cp crest =>
        have hcp : r.prevHash = H cp := hc.1
        cases dtail with
        | nil =>
          have hgen : r.prevHash = genesisSentinel := hd
          exact absurd (hgen ▸ hcp).symm (HFresh cp)
        | cons dp drest =>
          have hdp : r.prevHash = H dp := hd.1
          rcases HBind cp dp (hcp.symm.trans hdp) with hheads | bad
          · have hctail : wellLinked H (cp :: crest) := hc.2
            have hdtail : wellLinked H (dp :: drest) := hd.2
            rcases ih (dp :: drest) hctail hdtail (by simp [hheads]) with htails | bad
            · rw [htails]
              exact .inl rfl
            · exact .inr bad
          · exact .inr bad

/-- The outright reading: `chain_tamper_evident_or` at `Bad := False`. -/
theorem chain_tamper_evident {H : WitnessReceipt → Nat}
    (HInj : Function.Injective H) (HFresh : ∀ p, H p ≠ genesisSentinel) :
    ∀ (c d : ReceiptChain), wellLinked H c → wellLinked H d →
      c.head? = d.head? → c = d := by
  intro c d hc hd hhead
  rcases chain_tamper_evident_or (Bad := False) (fun a b e => .inl (HInj e)) HFresh c d hc hd hhead with
    he | f
  · exact he
  · exact f.elim

/-- Pure constructor for a receipt linking onto `prevDigest`. -/
@[expose] def mkReceipt (prevDigest oldC newC effH : Nat) : WitnessReceipt :=
  { prevHash := prevDigest, oldCommit := oldC, newCommit := newC, effectsHash := effH }

/-- Fold a turn-log into a newest-first well-linked receipt chain. -/
@[expose] def replayFold (H : WitnessReceipt → Nat) : ReceiptChain → List (Nat × Nat × Nat) → ReceiptChain
  | acc, [] => acc
  | acc, (oldC, newC, effH) :: rest =>
      let prevDigest := match acc with
        | []      => genesisSentinel
        | hd :: _ => H hd
      replayFold H (mkReceipt prevDigest oldC newC effH :: acc) rest

theorem replayFold_wellLinked (H : WitnessReceipt → Nat) :
    ∀ (acc : ReceiptChain) (turns : List (Nat × Nat × Nat)),
      wellLinked H acc → wellLinked H (replayFold H acc turns)
  | acc, [], hacc => hacc
  | acc, (oldC, newC, effH) :: rest, hacc => by
      unfold replayFold
      apply replayFold_wellLinked
      cases acc with
      | nil => exact rfl
      | cons hd tl => exact wellLinked_append hacc rfl

/-- The receipt chain induced by a list of witnessed roots. -/
@[expose] def witnessChain (H : WitnessReceipt → Nat) (roots : List Nat) : ReceiptChain :=
  replayFold H [] (roots.map (fun r => (r, r, 0)))

/-- **`rootOf i`** — extracts the attested state root iff `i` is a structurally valid witness. -/
@[expose] def rootOf : Interaction → Option Nat
  | .attested ar => if ar.holds then some ar.root else none
  | .ambient     => none

theorem rootOf_isSome_iff_witnessed (i : Interaction) :
    (rootOf i).isSome = i.isWitnessed := by
  cases i with
  | ambient => rfl
  | attested ar => cases h : ar.holds <;> simp [rootOf, Interaction.isWitnessed, h]

/-- **`witnessedRoots log`** — the roots a context's interaction log actually replays from. -/
@[expose] def witnessedRoots (log : InteractionLog) : List Nat :=
  log.filterMap rootOf

/-- **`witnessChainOf H log`** — the receipt chain induced by the witnessed roots of `log`. -/
@[expose] def witnessChainOf (H : WitnessReceipt → Nat) (log : InteractionLog) : ReceiptChain :=
  witnessChain H (witnessedRoots log)

theorem witnessChain_wellLinked (H : WitnessReceipt → Nat) (roots : List Nat) :
    wellLinked H (witnessChain H roots) :=
  replayFold_wellLinked H [] _ trivial

theorem witnessChainOf_wellLinked (H : WitnessReceipt → Nat) (log : InteractionLog) :
    wellLinked H (witnessChainOf H log) :=
  witnessChain_wellLinked H (witnessedRoots log)

theorem replayFold_length (H : WitnessReceipt → Nat) :
    ∀ (acc : ReceiptChain) (turns : List (Nat × Nat × Nat)),
      (replayFold H acc turns).length = acc.length + turns.length
  | acc, [] => by simp [replayFold]
  | acc, (oldC, newC, effH) :: rest => by
      unfold replayFold
      rw [replayFold_length H _ rest]
      simp [List.length_cons]
      omega

theorem witnessChainOf_length (H : WitnessReceipt → Nat) (log : InteractionLog) :
    (witnessChainOf H log).length = (witnessedRoots log).length := by
  unfold witnessChainOf witnessChain
  rw [replayFold_length]
  simp

theorem witnessedRoots_length_le (log : InteractionLog) :
    (witnessedRoots log).length ≤ log.length := by
  unfold witnessedRoots
  induction log with
  | nil => simp
  | cons i rest ih =>
    rw [List.filterMap_cons]
    cases hr : rootOf i with
    | none   => simp only [List.length_cons]; omega
    | some r => simp only [List.length_cons]; omega

theorem confined_witnessedRoots_length (log : InteractionLog) (hconf : confined log = true) :
    (witnessedRoots log).length = log.length := by
  induction log with
  | nil => rfl
  | cons i rest ih =>
    unfold confined at hconf
    rw [List.all_cons, Bool.and_eq_true] at hconf
    cases i with
    | ambient => exact absurd hconf.1 (by decide)
    | attested ar =>
      have har : ar.holds = true := hconf.1
      have hrest : confined rest = true := hconf.2
      have hroot : rootOf (Interaction.attested ar) = some ar.root := by
        simp only [rootOf, har, ite_true]
      unfold witnessedRoots at ih ⊢
      rw [List.filterMap_cons, hroot, List.length_cons, List.length_cons, ih hrest]

/-- **THE COVERAGE PAYOFF (`confined_chain_covers_log`)**:
    When `confined log = true`, the replayed receipt chain has one receipt per logged interaction. -/
theorem confined_chain_covers_log (H : WitnessReceipt → Nat) (log : InteractionLog)
    (hconf : confined log = true) :
    (witnessChainOf H log).length = log.length := by
  rw [witnessChainOf_length, confined_witnessedRoots_length log hconf]

theorem witnessedRoots_cons_of_none {i : Interaction} (hnone : rootOf i = none)
    (rest : InteractionLog) : witnessedRoots (i :: rest) = witnessedRoots rest := by
  unfold witnessedRoots
  rw [List.filterMap_cons, hnone]

theorem witnessedRoots_cons_le (i : Interaction) (rest : InteractionLog) :
    (witnessedRoots (i :: rest)).length ≤ (witnessedRoots rest).length + 1 := by
  unfold witnessedRoots
  rw [List.filterMap_cons]
  cases rootOf i <;> simp

theorem rootOf_eq_none_of_unwitnessed {i : Interaction} (hi : i.isWitnessed = false) :
    rootOf i = none := by
  have hsome := rootOf_isSome_iff_witnessed i
  rw [hi] at hsome
  cases hr : rootOf i with
  | none   => rfl
  | some r => rw [hr] at hsome; simp at hsome

theorem unconfined_witnessedRoots_shorter :
    ∀ (log : InteractionLog), confined log = false → (witnessedRoots log).length < log.length
  | [], h => by simp [confined] at h
  | i :: rest, h => by
    cases hi : Interaction.isWitnessed i with
    | false =>
      rw [witnessedRoots_cons_of_none (rootOf_eq_none_of_unwitnessed hi) rest, List.length_cons]
      have := witnessedRoots_length_le rest
      omega
    | true =>
      have hrest : confined rest = false := by
        unfold confined at h
        rw [List.all_cons, hi, Bool.true_and] at h
        exact h
      have hih := unconfined_witnessedRoots_shorter rest hrest
      have hle := witnessedRoots_cons_le i rest
      simp only [List.length_cons]
      omega

/-- **THE REFUTATION (`unconfined_chain_drops_interactions`)**:
    An unconfined trace replays to a strictly shorter receipt chain than `log.length`. -/
theorem unconfined_chain_drops_interactions (H : WitnessReceipt → Nat) (log : InteractionLog)
    (hunconf : confined log = false) :
    (witnessChainOf H log).length < log.length := by
  rw [witnessChainOf_length]
  exact unconfined_witnessedRoots_shorter log hunconf

theorem confined_append_ambient (pre post : InteractionLog) :
    confined (pre ++ Interaction.ambient :: post) = false := by
  unfold confined
  induction pre with
  | nil => rfl
  | cons i rest ih =>
    simp [List.all_cons, ih]

/-- **AMBIENT REACH DROPS INTERACTIONS (`ambient_chain_drops_the_reach`)**:
    Any log containing `.ambient` loses at least that interaction from its replay chain. -/
theorem ambient_chain_drops_the_reach (H : WitnessReceipt → Nat) (pre post : InteractionLog) :
    (witnessChainOf H (pre ++ Interaction.ambient :: post)).length
      < (pre ++ Interaction.ambient :: post).length :=
  unconfined_chain_drops_interactions H _ (confined_append_ambient pre post)

/-- **THE REPLAY PAYOFF (`replayedDeterministic_replays`)**:
    A `ReplayedDeterministic` context replays to a chain that is both tamper-evident
    (`witnessChainOf H log = other`) and complete (`(witnessChainOf H log).length = log.length`),
    consuming `hrepl`. -/
theorem replayedDeterministic_replays
    {H : WitnessReceipt → Nat} (HInj : Function.Injective H) (HFresh : ∀ p, H p ≠ genesisSentinel)
    (log : InteractionLog)
    (hrepl : classify log false = .ReplayedDeterministic)
    (other : ReceiptChain)
    (hother : wellLinked H other)
    (hhead : (witnessChainOf H log).head? = other.head?) :
    witnessChainOf H log = other ∧ (witnessChainOf H log).length = log.length :=
  have hconf : confined log = true := (replayedDeterministic_iff_confined log).mp hrepl
  ⟨chain_tamper_evident HInj HFresh (witnessChainOf H log) other
      (witnessChainOf_wellLinked H log) hother hhead,
   confined_chain_covers_log H log hconf⟩

/-! ## Pillar 2 — `Sturdyref`, Per-Viewer `Membrane`, and Chained Multi-Hop Reshare Attenuation (`Membrane.reshare`) -/

/-- A surface of interactive cell affordances. -/
abbrev AffordanceSurface (φ : Type) := List (CellAffordance φ)

/-- **`MembraneViewer`** — a membrane viewer holding capability rights `held` and a witness-graph
    projection predicate `permits : String → Bool` over affordance names, plus optional `activeNames`
    for finite domain checks. -/
structure MembraneViewer where
  held        : List Auth
  permits     : String → Bool
  activeNames : List String := []

abbrev Viewer := MembraneViewer

/-- **`membraneShows viewer aff`** — true iff the viewer's capabilities authorize `aff.required`
    AND the viewer's witness-graph projection permits `aff.name`. -/
@[expose] def membraneShows (viewer : MembraneViewer) (aff : CellAffordance φ) : Bool :=
  fireGate aff.required viewer.held && viewer.permits aff.name

/-- **`projectMembrane viewer affs`** — filters an affordance surface by `membraneShows viewer`. -/
@[expose] def projectMembrane (viewer : MembraneViewer) (affs : List (CellAffordance φ)) : List (CellAffordance φ) :=
  affs.filter (fun aff => membraneShows viewer aff)

theorem mem_projectMembrane (v : MembraneViewer) (affs : List (CellAffordance φ)) (aff : CellAffordance φ) :
    aff ∈ projectMembrane v affs ↔ (aff ∈ affs ∧ membraneShows v aff = true) := by
  unfold projectMembrane
  rw [List.mem_filter]

/-- **MEMBRANE KEYSTONE (`membrane_two_viewers_distinct`)**:
    Two viewers with identical `held` authority (`v₁.held = v₂.held`) both pass the capability gate
    for `aff`, yet different witness-graph `permits` projections see distinct surfaces
    (`projectMembrane v₁ affs ≠ projectMembrane v₂ affs`), with `aff ∈ projectMembrane v₁ affs`
    and `aff ∉ projectMembrane v₂ affs`. -/
theorem membrane_two_viewers_distinct (v₁ v₂ : MembraneViewer) (affs : List (CellAffordance φ))
    (aff : CellAffordance φ) (hmem : aff ∈ affs)
    (hheld : v₁.held = v₂.held)
    (hcap  : fireGate aff.required v₁.held = true)
    (hp1   : v₁.permits aff.name = true)
    (hp2   : v₂.permits aff.name = false) :
    aff ∈ projectMembrane v₁ affs ∧
    aff ∉ projectMembrane v₂ affs ∧
    projectMembrane v₁ affs ≠ projectMembrane v₂ affs := by
  have hcap2 : fireGate aff.required v₂.held = true := hheld ▸ hcap
  have hin : aff ∈ projectMembrane v₁ affs := by
    rw [mem_projectMembrane]
    refine ⟨hmem, ?_⟩
    unfold membraneShows
    rw [hcap, hp1]
    rfl
  have hout : aff ∉ projectMembrane v₂ affs := by
    rw [mem_projectMembrane]
    intro hcontra
    have hshows : membraneShows v₂ aff = true := hcontra.2
    unfold membraneShows at hshows
    rw [hcap2, hp2] at hshows
    exact absurd hshows (by decide)
  refine ⟨hin, hout, ?_⟩
  intro heq
  rw [heq] at hin
  exact hout hin

/-- **MEMBRANE AUTHORITY MONOTONICITY (`membrane_authority_monotone`)**:
    If `v₁.held ⊆ v₂.held` and `v₁.permits = v₂.permits`, then `projectMembrane v₁ affs ⊆ projectMembrane v₂ affs`. -/
theorem membrane_authority_monotone {v₁ v₂ : MembraneViewer}
    (h12 : v₁.held ⊆ v₂.held) (hperm : v₁.permits = v₂.permits)
    (affs : List (CellAffordance φ)) :
    projectMembrane v₁ affs ⊆ projectMembrane v₂ affs := by
  intro aff ha
  rw [mem_projectMembrane] at ha ⊢
  refine ⟨ha.1, ?_⟩
  have hshows : membraneShows v₁ aff = true := ha.2
  unfold membraneShows at hshows ⊢
  rw [Bool.and_eq_true] at hshows
  rw [fireGate_trans h12 hshows.1, ← hperm, hshows.2]
  rfl

/-- Pointwise generalization of `membrane_authority_monotone` when `v₁.permits` implies `v₂.permits`. -/
theorem membrane_monotone_both {v₁ v₂ : MembraneViewer}
    (h12 : v₁.held ⊆ v₂.held)
    (hperm : ∀ n, v₁.permits n = true → v₂.permits n = true)
    (affs : List (CellAffordance φ)) :
    projectMembrane v₁ affs ⊆ projectMembrane v₂ affs := by
  intro aff ha
  rw [mem_projectMembrane] at ha ⊢
  refine ⟨ha.1, ?_⟩
  have hshows : membraneShows v₁ aff = true := ha.2
  unfold membraneShows at hshows ⊢
  rw [Bool.and_eq_true] at hshows ⊢
  exact ⟨fireGate_trans h12 hshows.1, hperm aff.name hshows.2⟩

/-- Decidable check that `child` permits are a subset of `parent` permits on `activeNames`. -/
@[expose] def permitsSubsetOn (activeNames : List String) (child parent : String → Bool) : Bool :=
  activeNames.all (fun n => !child n || parent n)

theorem permitsSubsetOn_iff (activeNames : List String) (child parent : String → Bool) :
    permitsSubsetOn activeNames child parent = true ↔
      ∀ n ∈ activeNames, child n = true → parent n = true := by
  unfold permitsSubsetOn
  rw [List.all_eq_true]
  constructor
  · intro hall n hn hc
    have h := hall n hn
    rw [hc] at h
    simpa using h
  · intro himp n hn
    cases hc : child n with
    | false => rfl
    | true =>
      have hp := himp n hn hc
      simp [hp]

/-- **Chained Reshare Attenuation (`Membrane.reshare`)**:
    Checks `fireGate delegateTarget.held holderMembrane.held` and projection subset on active names,
    returning `some` of the attenuated viewer (preserving the cumulative `activeNames` scope across
    hops so downstream delegations cannot evade upstream active-name checks) iff the hop is a
    genuine attenuation, and `none` on any amplification attempt. -/
@[expose] def Membrane.reshare (holderMembrane : MembraneViewer) (delegateTarget : MembraneViewer) :
    Option MembraneViewer :=
  if fireGate delegateTarget.held holderMembrane.held &&
     permitsSubsetOn (holderMembrane.activeNames ++ delegateTarget.activeNames)
       delegateTarget.permits holderMembrane.permits then
    some {
      held        := delegateTarget.held
      permits     := fun n => holderMembrane.permits n && delegateTarget.permits n
      activeNames := holderMembrane.activeNames ++ delegateTarget.activeNames
    }
  else
    none

abbrev reshare := Membrane.reshare

theorem reshare_isSome_iff (holderMembrane delegateTarget : MembraneViewer) :
    (Membrane.reshare holderMembrane delegateTarget).isSome = true ↔
      (fireGate delegateTarget.held holderMembrane.held = true ∧
       permitsSubsetOn (holderMembrane.activeNames ++ delegateTarget.activeNames)
         delegateTarget.permits holderMembrane.permits = true) := by
  unfold Membrane.reshare
  cases h1 : fireGate delegateTarget.held holderMembrane.held <;>
  cases h2 : permitsSubsetOn (holderMembrane.activeNames ++ delegateTarget.activeNames)
    delegateTarget.permits holderMembrane.permits <;> simp

/-- **ANTI-AMPLIFICATION TOOTH (`amplifying_reshare_refused`)**:
    Any reshare attempt where `delegateTarget.held` exceeds `holderMembrane.held`
    (`fireGate delegateTarget.held holderMembrane.held = false`) is refused (`none`). -/
theorem amplifying_reshare_refused (holderMembrane delegateTarget : MembraneViewer)
    (hamp : fireGate delegateTarget.held holderMembrane.held = false) :
    Membrane.reshare holderMembrane delegateTarget = none := by
  unfold Membrane.reshare
  simp [hamp]

/-- Any reshare attempt that amplifies `permits` on active names is refused (`none`). -/
theorem amplifying_permits_reshare_refused (holderMembrane delegateTarget : MembraneViewer)
    (hamp : permitsSubsetOn (holderMembrane.activeNames ++ delegateTarget.activeNames)
              delegateTarget.permits holderMembrane.permits = false) :
    Membrane.reshare holderMembrane delegateTarget = none := by
  unfold Membrane.reshare
  simp [hamp]

/-- Every admitted single-hop reshare attenuates `held`, enforces `permitsSubsetOn` on
    `holder.activeNames ++ delegate.activeNames`, preserves `holder.activeNames ⊆ m.activeNames`,
    attenuates `m.permits`, and attenuates `projectMembrane` on every affordance surface. -/
theorem reshare_some_attenuates {holder delegate m : MembraneViewer}
    (h : Membrane.reshare holder delegate = some m) :
    m.held ⊆ holder.held ∧
    (∀ n ∈ holder.activeNames ++ delegate.activeNames,
      delegate.permits n = true → holder.permits n = true) ∧
    holder.activeNames ⊆ m.activeNames ∧
    (∀ n, m.permits n = true → holder.permits n = true) ∧
    (∀ (affs : List (CellAffordance φ)), projectMembrane m affs ⊆ projectMembrane holder affs) := by
  unfold Membrane.reshare at h
  split at h
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    simp only [Option.some.injEq] at h
    subst h
    have hsub : delegate.held ⊆ holder.held := (fireGate_iff_subset _ _).mp hcond.1
    have hact : ∀ n ∈ holder.activeNames ++ delegate.activeNames,
        delegate.permits n = true → holder.permits n = true :=
      (permitsSubsetOn_iff _ _ _).mp hcond.2
    have hnames : holder.activeNames ⊆ holder.activeNames ++ delegate.activeNames :=
      List.subset_append_left _ _
    have hp : ∀ n, (holder.permits n && delegate.permits n) = true → holder.permits n = true := by
      intro n hn
      rw [Bool.and_eq_true] at hn
      exact hn.1
    refine ⟨hsub, hact, hnames, hp, fun affs =>
      membrane_monotone_both
        (v₁ := { held := delegate.held, permits := fun n => holder.permits n && delegate.permits n,
                 activeNames := holder.activeNames ++ delegate.activeNames })
        (v₂ := holder) hsub hp affs⟩
  · contradiction

/-- **CHAINED MULTI-HOP RESHARE ATTENUATION (`reshare_chain_attenuates`)**:
    Across a multi-hop delegation chain $A \to B \to C$ (`Membrane.reshare mA reqB = some mB` and
    `Membrane.reshare mB reqC = some mC`), authority, active-name `permits`, and projected surfaces
    strictly attenuate transitively down the chain: `mC.held ⊆ mB.held ⊆ mA.held`,
    `∀ n ∈ mA.activeNames, reqC.permits n = true → mA.permits n = true`, and
    `projectMembrane mC affs ⊆ projectMembrane mB affs ⊆ projectMembrane mA affs`. -/
theorem reshare_chain_attenuates {mA reqB mB reqC mC : MembraneViewer}
    (hAB : Membrane.reshare mA reqB = some mB)
    (hBC : Membrane.reshare mB reqC = some mC)
    (affs : List (CellAffordance φ)) :
    mC.held ⊆ mB.held ∧
    mB.held ⊆ mA.held ∧
    mC.held ⊆ mA.held ∧
    (∀ n ∈ mA.activeNames, reqC.permits n = true → mA.permits n = true) ∧
    projectMembrane mC affs ⊆ projectMembrane mB affs ∧
    projectMembrane mB affs ⊆ projectMembrane mA affs ∧
    projectMembrane mC affs ⊆ projectMembrane mA affs := by
  have ⟨hB_held, _, hB_names, hB_perm, hB_proj⟩ := reshare_some_attenuates (φ := φ) hAB
  have ⟨hC_held, hC_act, _, _, hC_proj⟩ := reshare_some_attenuates (φ := φ) hBC
  have hC_on_A : ∀ n ∈ mA.activeNames, reqC.permits n = true → mA.permits n = true := by
    intro n hn hreqC
    have hnB : n ∈ mB.activeNames ++ reqC.activeNames :=
      List.mem_append_left _ (hB_names hn)
    exact hB_perm n (hC_act n hnB hreqC)
  refine ⟨hC_held, hB_held, List.Subset.trans hC_held hB_held, hC_on_A,
          hC_proj affs, hB_proj affs, List.Subset.trans (hC_proj affs) (hB_proj affs)⟩

/-- **MULTI-HOP DELAYED AMPLIFICATION REFUSAL (`reshare_chain_blocks_delayed_permits_amplification`)**:
    Even if an intermediate delegate `reqB` and downstream delegate `reqC` declare `activeNames = []`,
    `mB` retains `mA.activeNames`, so any attempt by `reqC` to amplify `permits` on a name `n ∈ mA.activeNames`
    where `mA.permits n = false` is refused (`Membrane.reshare mB reqC = none`). -/
theorem reshare_chain_blocks_delayed_permits_amplification {mA reqB mB reqC : MembraneViewer}
    (hAB : Membrane.reshare mA reqB = some mB)
    {n : String} (hn : n ∈ mA.activeNames)
    (hA_deny : mA.permits n = false)
    (hC_amp : reqC.permits n = true) :
    Membrane.reshare mB reqC = none := by
  cases hBC : Membrane.reshare mB reqC with
  | none => rfl
  | some mC =>
    have ⟨_, _, _, hC_on_A, _, _, _⟩ :=
      reshare_chain_attenuates (φ := Unit) hAB hBC []
    have hA_allow : mA.permits n = true := hC_on_A n hn hC_amp
    rw [hA_deny] at hA_allow
    contradiction

/-- **`Sturdyref φ`** — a persistable capability handle into the witness-graph packaging
    a cell URI/id, ground-truth `AffordanceSurface φ`, `InteractionLog`, publisher membrane
    `lineage`, and source reachability. -/
structure Sturdyref (φ : Type) where
  uri       : String
  surface   : AffordanceSurface φ
  log       : InteractionLog
  lineage   : MembraneViewer
  reachable : Bool := false
  cellId    : String := ""

/-- The derived `Rehydration` liveness-type of a `Sturdyref`. -/
@[expose] def Sturdyref.liveness (sr : Sturdyref φ) : Rehydration :=
  classify sr.log sr.reachable

/-- **`rehydrateSturdyref sr viewer`** — rehydrates a `Sturdyref` for `viewer`, returning the
    per-viewer membrane-attenuated surface paired with its derived `Rehydration` liveness-type. -/
@[expose] def rehydrateSturdyref (sr : Sturdyref φ) (viewer : MembraneViewer) :
    AffordanceSurface φ × Rehydration :=
  (projectMembrane viewer (projectMembrane sr.lineage sr.surface), sr.liveness)

theorem rehydrateSturdyref_liveness_iff_confined (sr : Sturdyref φ) (viewer : MembraneViewer)
    (hreach : sr.reachable = false) :
    (rehydrateSturdyref sr viewer).2 = .ReplayedDeterministic ↔ confined sr.log = true := by
  unfold rehydrateSturdyref Sturdyref.liveness
  dsimp only
  rw [hreach]
  exact replayedDeterministic_iff_confined sr.log

theorem rehydrateSturdyref_attenuates_both (sr : Sturdyref φ) (viewer : MembraneViewer)
    (aff : CellAffordance φ) (hmem : aff ∈ (rehydrateSturdyref sr viewer).1) :
    aff ∈ sr.surface ∧ membraneShows viewer aff = true ∧ membraneShows sr.lineage aff = true := by
  unfold rehydrateSturdyref at hmem
  dsimp only at hmem
  rw [mem_projectMembrane, mem_projectMembrane] at hmem
  exact ⟨hmem.1.1, hmem.2, hmem.1.2⟩

theorem rehydrateSturdyref_reshare_monotone {mA reqB mB : MembraneViewer}
    (sr : Sturdyref φ) (hAB : Membrane.reshare mA reqB = some mB) :
    (rehydrateSturdyref sr mB).1 ⊆ (rehydrateSturdyref sr mA).1 := by
  have ⟨_, _, _, _, hproj⟩ := reshare_some_attenuates (φ := φ) hAB
  exact hproj (projectMembrane sr.lineage sr.surface)

/-! ## Pillar 3 — The Functorial Rerender Square & Frustum-Snapshot Per-Viewer Re-Expansion -/

/-- **`projectFor held affs`** — per-viewer capability projection filtering affordances by `fireGate`. -/
@[expose] def projectFor (held : List Auth) (affs : List (CellAffordance φ)) : List (CellAffordance φ) :=
  affs.filter (fun aff => fireGate aff.required held)

theorem projectFor_monotone {held₁ held₂ : List Auth} (h12 : held₁ ⊆ held₂)
    (affs : List (CellAffordance φ)) :
    projectFor held₁ affs ⊆ projectFor held₂ affs := by
  intro aff ha
  unfold projectFor at ha ⊢
  rw [List.mem_filter] at ha ⊢
  exact ⟨ha.1, fireGate_trans h12 ha.2⟩

theorem projectFor_all_fireable (held : List Auth) (affs : List (CellAffordance φ))
    (aff : CellAffordance φ) (fc : FireCtx φ) (hmem : aff ∈ projectFor held affs) :
    (fire aff held fc).isSome = true := by
  unfold projectFor at hmem
  rw [List.mem_filter] at hmem
  unfold fire
  simp [hmem.2]

/-- **`rerender_deterministic`** — `projectFor` is a pure, referentially transparent function. -/
theorem rerender_deterministic (held : List Auth) (affs : List (CellAffordance φ)) :
    projectFor held affs = projectFor held affs := rfl

/-- **`rerender_idempotent`** — re-projecting an already-projected surface for the same viewer is a no-op. -/
theorem rerender_idempotent (held : List Auth) (affs : List (CellAffordance φ)) :
    projectFor held (projectFor held affs) = projectFor held affs := by
  unfold projectFor
  rw [List.filter_filter]
  simp

/-- **`stepContent f affs`** — a content state-step rewriting each affordance's `effect` by `f`
    while leaving its `required` gate and `name` unchanged. -/
@[expose] def stepContent (f : φ → φ) (affs : List (CellAffordance φ)) : List (CellAffordance φ) :=
  affs.map (fun a => { a with effect := f a.effect })

theorem stepContent_gate (f : φ → φ) (a : CellAffordance φ) :
    ({ a with effect := f a.effect } : CellAffordance φ).required = a.required := rfl

/-- **`rerender_square` (THE COMMUTING SQUARE)**:
    Re-rendering after a content update equals updating the rendered surface:
    `projectFor held (stepContent f affs) = stepContent f (projectFor held affs)`. -/
theorem rerender_square (f : φ → φ) (held : List Auth) (affs : List (CellAffordance φ)) :
    projectFor held (stepContent f affs) = stepContent f (projectFor held affs) := by
  unfold projectFor stepContent
  rw [List.filter_map]
  congr 1

/-- The commuting square also holds across the full 2-dimensional `projectMembrane` filter. -/
theorem rerender_membrane_square (f : φ → φ) (v : MembraneViewer) (affs : List (CellAffordance φ)) :
    projectMembrane v (stepContent f affs) = stepContent f (projectMembrane v affs) := by
  unfold projectMembrane stepContent
  rw [List.filter_map]
  congr 1

/-- **`rerender_after_step_authorized` (BUTTON STABILITY)**:
    A viewer authorized to fire `a` before a content step remains authorized to fire its
    re-rendered successor. -/
theorem rerender_after_step_authorized (f : φ → φ) (held : List Auth) (a : CellAffordance φ)
    (hfire : fireGate a.required held = true) :
    fireGate ({ a with effect := f a.effect } : CellAffordance φ).required held = true := by
  rw [stepContent_gate]
  exact hfire

/-- **`rerender_monotone`** — granting more authority yields a superset rendered surface. -/
theorem rerender_monotone {held₁ held₂ : List Auth} (h12 : held₁ ⊆ held₂)
    (affs : List (CellAffordance φ)) :
    projectFor held₁ affs ⊆ projectFor held₂ affs :=
  projectFor_monotone h12 affs

/-- **`Snapshot φ`** — a frustum-snapshot holding the ground-truth interactive component. -/
structure Snapshot (φ : Type) where
  component : List (CellAffordance φ)
deriving DecidableEq, Repr

/-- **`snapshot affs`** — capture a frustum-snapshot of `affs`. -/
@[expose] def snapshot (affs : List (CellAffordance φ)) : Snapshot φ :=
  ⟨affs⟩

/-- **`rehydrate snap held`** — re-expand a frustum-snapshot for a viewer holding `held`. -/
@[expose] def rehydrate (snap : Snapshot φ) (held : List Auth) : List (CellAffordance φ) :=
  projectFor held snap.component

/-- **`snapshot_roundtrip` (RE-EXPANSION FIDELITY)**:
    Capturing a snapshot and rehydrating it for `held` recovers `projectFor held affs` exactly. -/
theorem snapshot_roundtrip (held : List Auth) (affs : List (CellAffordance φ)) :
    rehydrate (snapshot affs) held = projectFor held affs := rfl

/-- **`snapshot_roundtrip_attenuated` (PER-VIEWER RE-EXPANSION)**:
    Two viewers re-expand the same snapshot into their own respective confined surfaces. -/
theorem snapshot_roundtrip_attenuated (held₁ held₂ : List Auth) (affs : List (CellAffordance φ)) :
    rehydrate (snapshot affs) held₁ = projectFor held₁ affs ∧
    rehydrate (snapshot affs) held₂ = projectFor held₂ affs :=
  ⟨rfl, rfl⟩

/-- **`snapshot_reexpansion_monotone`**:
    Re-expanding a snapshot is monotone in viewer authority. -/
theorem snapshot_reexpansion_monotone {held₁ held₂ : List Auth} (h12 : held₁ ⊆ held₂)
    (snap : Snapshot φ) :
    rehydrate snap held₁ ⊆ rehydrate snap held₂ :=
  rerender_monotone h12 snap.component

/-! ## Pillar 4 — 3-Dimensional `ReactiveAffordance` (`TransitionGate` + `[openHeight, closeHeight]` Window + `Membrane`) -/

/-- A decidable relational predicate over `(old, new)` cell states (`Obend.Core.Data.Data`). -/
abbrev TransitionPred := Data → Data → Bool

/-- **`TransitionGate`** — packages `pre` (old-state guard), `post` (new-state guard), and
    `link` (relational bridge reading both `old` and `new`). -/
structure TransitionGate where
  pre  : Data → Bool
  post : Data → Bool
  link : Data → Data → Bool

/-- **`transitionOK tg old new`** — true iff `pre old`, `post new`, and `link old new` all hold. -/
@[expose] def transitionOK (tg : TransitionGate) (old new : Data) : Bool :=
  tg.pre old && tg.post new && tg.link old new

/-- **`transitionOK_iff`** — decomposes `transitionOK` into its three boolean conjuncts. -/
theorem transitionOK_iff (tg : TransitionGate) (old new : Data) :
    transitionOK tg old new = true ↔
      (tg.pre old = true ∧ tg.post new = true ∧ tg.link old new = true) := by
  unfold transitionOK
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- **`ReactiveAffordance φ`** — a `CellAffordance φ` paired with a relational `TransitionGate`
    and an inclusive `[openHeight, closeHeight]` turn-height window. -/
structure ReactiveAffordance (φ : Type) where
  aff         : CellAffordance φ
  gate        : TransitionGate
  openHeight  : Nat
  closeHeight : Nat

/-- **`inWindow ra height`** — true iff `ra.openHeight ≤ height` and `height ≤ ra.closeHeight`. -/
@[expose] def inWindow (ra : ReactiveAffordance φ) (height : Nat) : Bool :=
  decide (ra.openHeight ≤ height) && decide (height ≤ ra.closeHeight)

/-- **`inWindow_iff`** — bridges `inWindow` to the arithmetic inequalities `openHeight ≤ height ≤ closeHeight`. -/
theorem inWindow_iff (ra : ReactiveAffordance φ) (height : Nat) :
    inWindow ra height = true ↔ (ra.openHeight ≤ height ∧ height ≤ ra.closeHeight) := by
  unfold inWindow
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- **`reactiveOK ra held height old new`** — the 3-dimensional reactive gate:
    capability gate AND relational transition gate AND temporal height window. -/
@[expose] def reactiveOK (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat) (old new : Data) : Bool :=
  fireGate ra.aff.required held && transitionOK ra.gate old new && inWindow ra height

theorem reactiveOK_iff (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat) (old new : Data) :
    reactiveOK ra held height old new = true ↔
      (fireGate ra.aff.required held = true ∧
       transitionOK ra.gate old new = true ∧
       inWindow ra height = true) := by
  unfold reactiveOK
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- **`fireReactive ra held height old new fc`** — dispatches `ra.aff` via `Obend.Vault.Affordance.fire`
    iff `reactiveOK ra held height old new` holds. -/
@[expose] def fireReactive (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat) (old new : Data)
    (fc : FireCtx φ) : Option (AffordanceIntent φ) :=
  if reactiveOK ra held height old new then
    fire ra.aff held fc
  else
    none

/-- **THE 3D REACTIVE KEYSTONE (`fireReactive_iff`)**:
    `fireReactive` commits (`isSome = true`) if and only if the capability gate passes,
    the relational transition gate passes, and `height` lies within `[ra.openHeight, ra.closeHeight]`. -/
theorem fireReactive_iff (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat) (old new : Data)
    (fc : FireCtx φ) :
    (fireReactive ra held height old new fc).isSome = true ↔
      (fireGate ra.aff.required held = true ∧
       transitionOK ra.gate old new = true ∧
       ra.openHeight ≤ height ∧
       height ≤ ra.closeHeight) := by
  unfold fireReactive
  by_cases hok : reactiveOK ra held height old new = true
  · have ⟨hcap, htr, hwin⟩ := (reactiveOK_iff ra held height old new).mp hok
    have ⟨hlo, hhi⟩ := (inWindow_iff ra height).mp hwin
    unfold fire
    simp [hok, hcap, htr, hlo, hhi]
  · simp only [hok, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, false_iff]
    intro ⟨hcap, htr, hlo, hhi⟩
    have hwin : inWindow ra height = true := (inWindow_iff ra height).mpr ⟨hlo, hhi⟩
    have hok' : reactiveOK ra held height old new = true :=
      (reactiveOK_iff ra held height old new).mpr ⟨hcap, htr, hwin⟩
    exact hok hok'

/-- **POSITIVE TOOTH (`fireReactive_all_pass`)**:
    When capabilities, transition, and window all pass, `fireReactive` commits. -/
theorem fireReactive_all_pass (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Data) (fc : FireCtx φ)
    (hcap : fireGate ra.aff.required held = true)
    (htr  : transitionOK ra.gate old new = true)
    (hwin : inWindow ra height = true) :
    (fireReactive ra held height old new fc).isSome = true := by
  have ⟨hlo, hhi⟩ := (inWindow_iff ra height).mp hwin
  exact (fireReactive_iff ra held height old new fc).mpr ⟨hcap, htr, hlo, hhi⟩

/-- **CAPABILITY TOOTH (`fireReactive_cap_fail_refuses`)**:
    When `fireGate ra.aff.required held = false`, `fireReactive` refuses (`none`). -/
theorem fireReactive_cap_fail_refuses (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Data) (fc : FireCtx φ) (hcap : fireGate ra.aff.required held = false) :
    fireReactive ra held height old new fc = none := by
  unfold fireReactive reactiveOK
  simp [hcap]

/-- **TRANSITION FAILURE TOOTH (`fireReactive_transition_fail_refuses`)**:
    When `transitionOK ra.gate old new = false`, `fireReactive` refuses (`none`). -/
theorem fireReactive_transition_fail_refuses (ra : ReactiveAffordance φ) (held : List Auth)
    (height : Nat) (old new : Data) (fc : FireCtx φ) (htr : transitionOK ra.gate old new = false) :
    fireReactive ra held height old new fc = none := by
  unfold fireReactive reactiveOK
  simp [htr]

/-- **WINDOW FAILURE TOOTH (`fireReactive_window_fail_refuses`)**:
    When `inWindow ra height = false`, `fireReactive` refuses (`none`). -/
theorem fireReactive_window_fail_refuses (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Data) (fc : FireCtx φ) (hwin : inWindow ra height = false) :
    fireReactive ra held height old new fc = none := by
  unfold fireReactive reactiveOK
  simp [hwin]

/-- **THE TRANSITION TOOTH (`fireReactive_wrong_old_refuses`)**:
    Reaching the same valid destination `new` (`ra.gate.post new = true`) from a `wrongOld` that
    violates the relational `link` (`ra.gate.link wrongOld new = false`) is refused (`none`),
    even when capabilities and the height window both pass. -/
theorem fireReactive_wrong_old_refuses (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (wrongOld new : Data) (fc : FireCtx φ)
    (hpost : ra.gate.post new = true)
    (hcap  : fireGate ra.aff.required held = true)
    (hwin  : inWindow ra height = true)
    (hlink : ra.gate.link wrongOld new = false) :
    fireReactive ra held height wrongOld new fc = none := by
  unfold fireReactive reactiveOK transitionOK
  rw [hcap, hwin, hpost, hlink]
  simp

/-- **THE DEADLINE TOOTH (`fireReactive_after_deadline_refuses`)**:
    Past `ra.closeHeight` (`ra.closeHeight < height`), `fireReactive` auto-refuses (`none`). -/
theorem fireReactive_after_deadline_refuses (ra : ReactiveAffordance φ) (held : List Auth)
    (height : Nat) (old new : Data) (fc : FireCtx φ) (hlate : ra.closeHeight < height) :
    fireReactive ra held height old new fc = none := by
  apply fireReactive_window_fail_refuses
  unfold inWindow
  have hdec : decide (height ≤ ra.closeHeight) = false := by
    rw [decide_eq_false_iff_not]
    exact Nat.not_le.mpr hlate
  rw [hdec, Bool.and_false]

/-- **BEFORE-OPEN TOOTH (`fireReactive_before_open_refuses`)**:
    Before `ra.openHeight` (`height < ra.openHeight`), `fireReactive` auto-refuses (`none`). -/
theorem fireReactive_before_open_refuses (ra : ReactiveAffordance φ) (held : List Auth)
    (height : Nat) (old new : Data) (fc : FireCtx φ) (hearly : height < ra.openHeight) :
    fireReactive ra held height old new fc = none := by
  apply fireReactive_window_fail_refuses
  unfold inWindow
  have hdec : decide (ra.openHeight ≤ height) = false := by
    rw [decide_eq_false_iff_not]
    exact Nat.not_le.mpr hearly
  rw [hdec, Bool.false_and]

/-- **TEMPORAL HTMX REACTIVITY (`fireReactive_window_reactive`)**:
    For a fixed authorized viewer and qualifying state transition, the affordance fires inside
    `[openHeight, closeHeight]` (`h₁`) and is dark outside it (`h₂`). -/
theorem fireReactive_window_reactive (ra : ReactiveAffordance φ) (held : List Auth)
    (h₁ h₂ : Nat) (old new : Data) (fc : FireCtx φ)
    (hcap : fireGate ra.aff.required held = true)
    (htr  : transitionOK ra.gate old new = true)
    (hin  : inWindow ra h₁ = true)
    (hout : inWindow ra h₂ = false) :
    (fireReactive ra held h₁ old new fc).isSome = true ∧
    (fireReactive ra held h₂ old new fc).isSome = false := by
  refine ⟨fireReactive_all_pass ra held h₁ old new fc hcap htr hin, ?_⟩
  rw [fireReactive_window_fail_refuses ra held h₂ old new fc hout]
  rfl

/-- **EFFECT INTEGRITY (`fireReactive_carries_real_effect`)**:
    When `fireReactive` commits, the resulting intent carries `ra.aff.effect` verbatim. -/
theorem fireReactive_carries_real_effect (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Data) (fc : FireCtx φ) (intent : AffordanceIntent φ)
    (h : fireReactive ra held height old new fc = some intent) :
    intent.surface.firedEffect = ra.aff.effect := by
  unfold fireReactive fire at h
  split at h
  · split at h
    · cases h; rfl
    · contradiction
  · contradiction

/-- **ATTESTED ROOT BINDING (`fireReactive_binds_attested_root`)**:
    When `fireReactive` commits, the resulting surface binds `fc.postCommit`. -/
theorem fireReactive_binds_attested_root (ra : ReactiveAffordance φ) (held : List Auth) (height : Nat)
    (old new : Data) (fc : FireCtx φ) (intent : AffordanceIntent φ)
    (h : fireReactive ra held height old new fc = some intent) :
    intent.surface.boundRoot = fc.postCommit := by
  unfold fireReactive fire at h
  split at h
  · split at h
    · cases h; rfl
    · contradiction
  · contradiction

/-! ## Concrete Golden Witnesses & Non-Vacuity Teeth across All 4 Pillars -/

/-- Demo hash function for concrete receipt-chain replay checks. -/
@[expose] def demoReceiptHash (r : WitnessReceipt) : Nat :=
  r.prevHash + r.oldCommit + r.newCommit + r.effectsHash + 1

/-- A genuine attested root (both `v4Complete` and `quorum` hold). -/
@[expose] def goodRoot : AttestedRoot := { root := 42, v4Complete := true, quorum := true }

/-- A structurally invalid attested root (complete, but missing quorum). -/
@[expose] def badRoot : AttestedRoot := { root := 42, v4Complete := true, quorum := false }

/-- A confined interaction log of two genuine attested turns. -/
@[expose] def confinedLog : InteractionLog := [.attested goodRoot, .attested goodRoot]

/-- An unconfined interaction log containing an ambient reach outside the membrane. -/
@[expose] def ambientLog : InteractionLog := [.attested goodRoot, .ambient]

/-- An unconfined interaction log containing a structurally invalid attestation. -/
@[expose] def forgedLog : InteractionLog := [.attested goodRoot, .attested badRoot]

theorem replayedDeterministic_replays_satisfiable :
    classify confinedLog false = .ReplayedDeterministic ∧
    (witnessChainOf demoReceiptHash confinedLog).length = confinedLog.length ∧
    confinedLog.length = 2 := by
  refine ⟨rfl, rfl, rfl⟩

theorem replays_coverage_needs_confinement :
    classify ambientLog false ≠ .ReplayedDeterministic ∧
    (witnessChainOf demoReceiptHash ambientLog).length < ambientLog.length ∧
    classify forgedLog false ≠ .ReplayedDeterministic ∧
    (witnessChainOf demoReceiptHash forgedLog).length < forgedLog.length := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Lookup a natural number field inside a `Core.Data.record`. -/
@[expose] def lookupNatField (key : String) : Data → Option Nat
  | .record fields =>
    match fields.lookup key with
    | some (.natural n) => some n
    | _                 => none
  | _ => none

/-- Council vote transition gate on `Core.Data`: status remains `1` (PENDING) and tally increments by `1`. -/
@[expose] def voteTransitionGate : TransitionGate where
  pre  := fun d => lookupNatField "status" d == some 1
  post := fun d => lookupNatField "status" d == some 1
  link := fun old new =>
    match lookupNatField "tally" old, lookupNatField "tally" new with
    | some a, some b => b == a + 1
    | _,      _      => false

/-- Council resolve transition gate on `Core.Data`: status moves `1 → 2` (PENDING → RESOLVED)
    and tally crosses the quorum threshold `3`. -/
@[expose] def resolveTransitionGate : TransitionGate where
  pre  := fun d => lookupNatField "status" d == some 1
  post := fun d => lookupNatField "status" d == some 2
  link := fun old new =>
    match lookupNatField "tally" old, lookupNatField "tally" new with
    | some a, some b => decide (a < 3) && decide (3 ≤ b)
    | _,      _      => false

/-- Demo effect type for reactive council affordances. -/
inductive CouncilEffect where
  | castBallot (proposalId : Nat)
  | resolveProposal (proposalId : Nat)
  | inspectTally (proposalId : Nat)
deriving DecidableEq, Repr

@[expose] def councilEffectDigest : CouncilEffect → Nat
  | .castBallot n      => 3 * n
  | .resolveProposal n => 3 * n + 1
  | .inspectTally n    => 3 * n + 2

@[expose] def demoFireCtx : FireCtx CouncilEffect where
  effectDigest := councilEffectDigest
  prevDigest   := 9
  preCommit    := 100
  postCommit   := 110

@[expose] def voteAff : CellAffordance CouncilEffect :=
  { required := [.write], effect := .castBallot 1, name := "vote" }

@[expose] def resolveAff : CellAffordance CouncilEffect :=
  { required := [.grant], effect := .resolveProposal 1, name := "resolve" }

@[expose] def tallyViewAff : CellAffordance CouncilEffect :=
  { required := [.read], effect := .inspectTally 1, name := "tally" }

@[expose] def voteReactiveBtn : ReactiveAffordance CouncilEffect :=
  { aff := voteAff, gate := voteTransitionGate, openHeight := 10, closeHeight := 20 }

@[expose] def resolveReactiveBtn : ReactiveAffordance CouncilEffect :=
  { aff := resolveAff, gate := resolveTransitionGate, openHeight := 10, closeHeight := 30 }

@[expose] def statePend0 : Data := .record [("status", .natural 1), ("tally", .natural 0)]
@[expose] def statePend1 : Data := .record [("status", .natural 1), ("tally", .natural 1)]
@[expose] def statePend2 : Data := .record [("status", .natural 1), ("tally", .natural 2)]
@[expose] def stateResolved3 : Data := .record [("status", .natural 2), ("tally", .natural 3)]

@[expose] def councilSurface : AffordanceSurface CouncilEffect :=
  [voteAff, resolveAff, tallyViewAff]

@[expose] def chairViewer : MembraneViewer where
  held        := [.read, .write, .grant]
  permits     := fun n => n == "vote" || n == "resolve" || n == "tally"
  activeNames := ["vote", "resolve", "tally"]

@[expose] def memberViewer : MembraneViewer where
  held        := [.read, .write]
  permits     := fun n => n == "vote" || n == "tally"
  activeNames := ["vote", "tally"]

@[expose] def trusteeViewer : MembraneViewer where
  held        := [.read]
  permits     := fun n => n == "tally"
  activeNames := ["tally"]

@[expose] def guestViewer : MembraneViewer where
  held        := [.read]
  permits     := fun _ => false
  activeNames := []

@[expose] def councilSturdyref : Sturdyref CouncilEffect where
  uri       := "dregg://council/proposal-1"
  surface   := councilSurface
  log       := confinedLog
  lineage   := chairViewer
  reachable := false

@[expose] def bumpProposalId : CouncilEffect → CouncilEffect
  | .castBallot n      => .castBallot (n + 1)
  | .resolveProposal n => .resolveProposal (n + 1)
  | .inspectTally n    => .inspectTally (n + 1)

/-! ### Cross-Vault Bridges (`Obend.Vault.Mandate`, `Obend.Vault.Projection`, `Obend.Receipt`) -/

/-- Translate `Obend.Vault.Mandate.Auth` to `Obend.Vault.Affordance.Auth`. -/
@[expose] def authOfMandateAuth : Obend.Vault.Mandate.Auth → Auth
  | .read    => .read
  | .write   => .write
  | .grant   => .grant
  | .call    => .call
  | .reply   => .reply
  | .reset   => .reset
  | .control => .control
  | .notify  => .notify

/-- Derive a `MembraneViewer` from an `Obend.Vault.Mandate.Mandate`, a cell-to-name lookup,
    and an optional list of `activeNames`. -/
@[expose] def viewerOfMandate (m : Obend.Vault.Mandate.Mandate) (cellOfName : String → Nat)
    (activeNames : List String := []) : MembraneViewer where
  held        := m.rights.map authOfMandateAuth
  permits     := fun name => m.cells.contains (cellOfName name)
  activeNames := activeNames

/-- An `Obend.Vault.Mandate` attenuation induces a monotone `projectMembrane` inclusion. -/
theorem viewerOfMandate_attenuates {m_child m_parent : Obend.Vault.Mandate.Mandate}
    (hatten : Obend.Vault.Mandate.attenuates m_child m_parent)
    (cellOfName : String → Nat)
    (activeNames : List String := [])
    (affs : List (CellAffordance φ)) :
    projectMembrane (viewerOfMandate m_child cellOfName activeNames) affs ⊆
    projectMembrane (viewerOfMandate m_parent cellOfName activeNames) affs := by
  rcases hatten with ⟨hrights, _, hcells, _, _, _⟩
  apply membrane_monotone_both
  · intro a ha
    simp only [viewerOfMandate, List.mem_map] at ha ⊢
    obtain ⟨r, hr, rfl⟩ := ha
    exact ⟨r, hrights hr, rfl⟩
  · intro n hn
    simp only [viewerOfMandate, List.contains_iff_mem] at hn ⊢
    exact hcells hn

/-- Translate `Obend.Vault.Projection.Auth` to `Obend.Vault.Affordance.Auth`. -/
@[expose] def authOfProjectionAuth : Obend.Vault.Projection.Auth → Auth
  | .read    => .read
  | .write   => .write
  | .grant   => .grant
  | .call    => .call
  | .reply   => .reply
  | .reset   => .reset
  | .control => .control
  | .notify  => .notify

/-- Translate `Obend.Vault.Affordance.Auth` to `Obend.Vault.Projection.Auth`. -/
@[expose] def authToProjectionAuth : Auth → Obend.Vault.Projection.Auth
  | .read    => .read
  | .write   => .write
  | .grant   => .grant
  | .call    => .call
  | .reply   => .reply
  | .reset   => .reset
  | .control => .control
  | .notify  => .notify

theorem authToProjectionAuth_left_inv (a : Obend.Vault.Projection.Auth) :
    authToProjectionAuth (authOfProjectionAuth a) = a := by
  cases a <;> rfl

theorem authOfProjectionAuth_left_inv (a : Auth) :
    authOfProjectionAuth (authToProjectionAuth a) = a := by
  cases a <;> rfl

/-- Rehydrate a blinded vault cell list (`Obend.Vault.Projection.VaultCell`) for a viewer `v`,
    returning the per-viewer blinded projection paired with the derived `Rehydration` liveness-type. -/
def rehydrateVaultCells (H : Obend.Digest.HashBytes.Hash)
    (v : List Obend.Vault.Projection.Auth)
    (cells : List Obend.Vault.Projection.VaultCell)
    (log : InteractionLog) (reachable : Bool) :
    List Obend.Vault.Projection.ProjectedCell × Rehydration :=
  (Obend.Vault.Projection.projectVault H v cells, classify log reachable)

/-- **Blinded Vault Rehydration Root Invariance (`rehydrateVaultCells_root_invariant`)**:
    Rehydrating a vault cell list for any viewer `v` preserves the unredacted Merkle root bit-for-bit
    (`Obend.Vault.Projection.projectVault_mapRoot_eq`). -/
theorem rehydrateVaultCells_root_invariant (H : Obend.Digest.HashBytes.Hash)
    (v : List Obend.Vault.Projection.Auth)
    (cells : List Obend.Vault.Projection.VaultCell)
    (log : InteractionLog) (reachable : Bool) :
    Obend.Receipt.Merkle.mapRoot H
      ((rehydrateVaultCells H v cells log reachable).1.map (Obend.Vault.Projection.projectedCommit H)) =
    Obend.Receipt.Merkle.mapRoot H (Obend.Vault.Projection.vaultCommits H cells) :=
  Obend.Vault.Projection.projectVault_mapRoot_eq H v cells

/-- **Fog-of-War Non-Interference on Rehydrated Vault Cells (`rehydrateVaultCells_fog_noninterference`)**:
    Two vaults that agree on all cells visible to `v` produce identical visible projections
    (`Obend.Vault.Projection.fog_of_war_noninterference`). -/
theorem rehydrateVaultCells_fog_noninterference
    (v : List Obend.Vault.Projection.Auth)
    (s₁ s₂ : List Obend.Vault.Projection.VaultCell)
    (hagree : Obend.Vault.Projection.agreeOn v s₁ s₂) :
    Obend.Vault.Projection.visibleTo v s₁ = Obend.Vault.Projection.visibleTo v s₂ :=
  Obend.Vault.Projection.fog_of_war_noninterference v s₁ s₂ hagree

/-- Convert an `AttestedRoot` into an `Obend.Receipt.Trust` support entry:
    structurally holding roots map to `.checked`, while incomplete/unquorumed roots fall back to `.attested`. -/
def trustOfAttestedRoot (ar : AttestedRoot) : Obend.Receipt.Trust :=
  if ar.holds then
    .checked "dregg-v4-quorum" "4.0" .kernel
  else
    .attested "unverified-claim" (toString ar.root)

theorem trustOfAttestedRoot_checked_iff (ar : AttestedRoot) :
    trustOfAttestedRoot ar = .checked "dregg-v4-quorum" "4.0" .kernel ↔ ar.holds = true := by
  unfold trustOfAttestedRoot
  cases h : ar.holds <;> simp

/-- Map an `Interaction` to a named `Obend.Receipt.Trust` support entry. -/
def trustOfInteraction : Interaction → String × Obend.Receipt.Trust
  | .attested ar => ("dregg-interaction", trustOfAttestedRoot ar)
  | .ambient     => ("dregg-interaction", .attested "ambient-reach" "unwitnessed")

theorem trustOfInteraction_checked_iff_witnessed (i : Interaction) :
    (trustOfInteraction i).2 = .checked "dregg-v4-quorum" "4.0" .kernel ↔ i.isWitnessed = true := by
  cases i with
  | ambient => simp [trustOfInteraction, Interaction.isWitnessed]
  | attested ar =>
    simp [trustOfInteraction, Interaction.isWitnessed, trustOfAttestedRoot_checked_iff]

/-- Map an `InteractionLog` to an `Obend.Receipt` support trust list. -/
def logTrustList (log : InteractionLog) : List (String × Obend.Receipt.Trust) :=
  log.map trustOfInteraction

/-- **Confinement ↔ Checked Support Ceiling (`confined_iff_no_attested_support`)**:
    An `InteractionLog` is confined iff every entry in its `Obend.Receipt` support list is
    `.checked "dregg-v4-quorum" "4.0" .kernel` (with zero `.attested` fallback entries). -/
theorem confined_iff_no_attested_support (log : InteractionLog) :
    confined log = true ↔
      ∀ c ∈ logTrustList log, c.2 = .checked "dregg-v4-quorum" "4.0" .kernel := by
  unfold confined logTrustList
  rw [List.all_eq_true]
  constructor
  · intro hall c hc
    rw [List.mem_map] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact (trustOfInteraction_checked_iff_witnessed i).mpr (hall i hi)
  · intro hall i hi
    have hc := hall (trustOfInteraction i) (List.mem_map_of_mem hi)
    exact (trustOfInteraction_checked_iff_witnessed i).mp hc

/-- **End-to-End Master Soundness Theorem (`rehydration_master_sound`)**:
    Conjoins concrete positive and negative poles across all four pillars of the Rehydratable
    Membranes architecture. -/
example :
    -- Pillar 1: Derived liveness-type & replay coverage
    classify confinedLog false = .ReplayedDeterministic ∧
    classify ambientLog false = .ReconstructedApproximate ∧
    classify forgedLog false = .ReconstructedApproximate ∧
    classify ambientLog true = .Live ∧
    (witnessChainOf demoReceiptHash confinedLog).length = 2 ∧
    (witnessChainOf demoReceiptHash ambientLog).length = 1 ∧
    (witnessChainOf demoReceiptHash forgedLog).length = 1 ∧
    -- Pillar 2: Per-viewer Membrane, Reshare Attenuation, and Sturdyref Rehydration
    (projectMembrane trusteeViewer councilSurface).length = 1 ∧
    (projectMembrane guestViewer councilSurface).length = 0 ∧
    (Membrane.reshare chairViewer memberViewer).isSome = true ∧
    (Membrane.reshare memberViewer chairViewer).isNone = true ∧
    (rehydrateSturdyref councilSturdyref memberViewer).1.length = 2 ∧
    (rehydrateSturdyref councilSturdyref memberViewer).2 = .ReplayedDeterministic ∧
    -- Pillar 3: Functorial Rerender Square & Frustum-Snapshot Re-expansion
    projectFor [.read, .write] (stepContent bumpProposalId councilSurface) =
      stepContent bumpProposalId (projectFor [.read, .write] councilSurface) ∧
    (rehydrate (snapshot councilSurface) [.read]).length = 1 ∧
    (rehydrate (snapshot councilSurface) [.read, .write, .grant]).length = 3 ∧
    -- Pillar 4: 3D ReactiveAffordance (Cap + TransitionGate + Height Window)
    (fireReactive voteReactiveBtn [.read, .write] 15 statePend0 statePend1 demoFireCtx).isSome = true ∧
    (fireReactive voteReactiveBtn [.read, .write] 15 statePend1 statePend1 demoFireCtx).isNone = true ∧
    (fireReactive voteReactiveBtn [.read, .write] 25 statePend0 statePend1 demoFireCtx).isNone = true ∧
    (fireReactive voteReactiveBtn [.read] 15 statePend0 statePend1 demoFireCtx).isNone = true ∧
    (fireReactive resolveReactiveBtn [.read, .grant] 22 statePend2 stateResolved3 demoFireCtx).isSome = true ∧
    (fireReactive resolveReactiveBtn [.read, .grant] 22 stateResolved3 stateResolved3 demoFireCtx).isNone = true := by
  decide

/-! ## Pillar 5 — Inner-System Seam Weld: `FrozenMembrane` / `LiveMembrane` `Core.Data` Codecs, `Obend.Slot` Protocol & `Obend.Law.CellContract` -/

open Obend.Core.Term (Term)
open Obend.Spec.Law (LawExpr LawRef Facts)
open Obend.Law (CellContract Holds Admits law3 okT leNat eqNat andT natT
  admits_iff guard_ok subst_guard subst_binary subst_get subst_bound lawEnv)

/-- Encode an `Auth` capability token as `Obend.Core.Data`. -/
@[expose] def Auth.toData : Auth → Data
  | .read    => .label "read"
  | .write   => .label "write"
  | .grant   => .label "grant"
  | .call    => .label "call"
  | .reply   => .label "reply"
  | .reset   => .label "reset"
  | .control => .label "control"
  | .notify  => .label "notify"

/-- Decode an `Auth` capability token from `Obend.Core.Data`. -/
@[expose] def Auth.ofData? : Data → Option Auth
  | .label "read"    => some .read
  | .label "write"   => some .write
  | .label "grant"   => some .grant
  | .label "call"    => some .call
  | .label "reply"   => some .reply
  | .label "reset"   => some .reset
  | .label "control" => some .control
  | .label "notify"  => some .notify
  | _                => none

theorem Auth.ofData_toData (a : Auth) : Auth.ofData? (Auth.toData a) = some a := by
  cases a <;> rfl

/-- Encode a list of `Auth` capability tokens as `Obend.Core.Data`. -/
@[expose] def authListToData : List Auth → Data
  | [] => .variant "nil" (.record [])
  | a :: rest => .variant "cons" (.record [("head", Auth.toData a), ("tail", authListToData rest)])

/-- Decode a list of `Auth` capability tokens from `Obend.Core.Data`. -/
@[expose] def authListOfData? : Data → Option (List Auth)
  | .variant "nil" (.record []) => some []
  | .variant "cons" (.record [("head", h), ("tail", t)]) => do
    let a ← Auth.ofData? h
    let rest ← authListOfData? t
    pure (a :: rest)
  | _ => none

theorem authListOfData_toData (xs : List Auth) :
    authListOfData? (authListToData xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp [authListToData, authListOfData?, Auth.ofData_toData, ih]

/-- Encode a `Rehydration` liveness classification as `Obend.Core.Data`. -/
@[expose] def Rehydration.toData : Rehydration → Data
  | .Live                     => .label "Live"
  | .ReplayedDeterministic    => .label "ReplayedDeterministic"
  | .ReconstructedApproximate => .label "ReconstructedApproximate"

/-- Decode a `Rehydration` liveness classification from `Obend.Core.Data`. -/
@[expose] def Rehydration.ofData? : Data → Option Rehydration
  | .label "Live"                     => some .Live
  | .label "ReplayedDeterministic"    => some .ReplayedDeterministic
  | .label "ReconstructedApproximate" => some .ReconstructedApproximate
  | _                                 => none

theorem Rehydration.ofData_toData (r : Rehydration) :
    Rehydration.ofData? (Rehydration.toData r) = some r := by
  cases r <;> rfl

instance : Inhabited Rehydration := ⟨.Live⟩

/-- **`FrozenMembrane`** — serialized membrane state carrying a monotonically advancing `epoch`,
    an immutable capability boundary digest `capDigest`, a dependency digest `depDigest`, and
    the held `Auth` capability tokens. -/
structure FrozenMembrane where
  surfaceId : String
  epoch     : Nat
  capDigest : Nat
  depDigest : Nat
  heldCaps  : List Auth
  deriving DecidableEq, Repr, Inhabited

/-- **`LiveMembrane`** — rehydrated runtime membrane state coupling the surface metadata, epoch,
    capability/dependency digests, active `Auth` capabilities, and derived `Rehydration` liveness. -/
structure LiveMembrane where
  surfaceId  : String
  epoch      : Nat
  capDigest  : Nat
  depDigest  : Nat
  activeCaps : List Auth
  liveness   : Rehydration
  deriving DecidableEq, Repr, Inhabited

/-- Deterministic `Obend.Core.Data` encoding of `FrozenMembrane`. -/
@[expose] def FrozenMembrane.toData (fm : FrozenMembrane) : Data :=
  .record
    [ ("surfaceId", .label fm.surfaceId)
    , ("epoch", .natural fm.epoch)
    , ("capDigest", .natural fm.capDigest)
    , ("depDigest", .natural fm.depDigest)
    , ("heldCaps", authListToData fm.heldCaps) ]

/-- Deterministic `Obend.Core.Data` decoding of `FrozenMembrane`. -/
@[expose] def FrozenMembrane.ofData? : Data → Option FrozenMembrane
  | .record
      [ ("surfaceId", .label surfaceId)
      , ("epoch", .natural epoch)
      , ("capDigest", .natural capDigest)
      , ("depDigest", .natural depDigest)
      , ("heldCaps", heldCapsData) ] => do
    let heldCaps ← authListOfData? heldCapsData
    pure { surfaceId, epoch, capDigest, depDigest, heldCaps }
  | _ => none

/-- Exact roundtrip theorem for `FrozenMembrane.toData` / `FrozenMembrane.ofData?`. -/
theorem FrozenMembrane.ofData_toData (fm : FrozenMembrane) :
    FrozenMembrane.ofData? fm.toData = some fm := by
  cases fm
  simp [FrozenMembrane.toData, FrozenMembrane.ofData?, authListOfData_toData]

/-- Deterministic `Obend.Core.Data` encoding of `LiveMembrane`. -/
@[expose] def LiveMembrane.toData (lm : LiveMembrane) : Data :=
  .record
    [ ("surfaceId", .label lm.surfaceId)
    , ("epoch", .natural lm.epoch)
    , ("capDigest", .natural lm.capDigest)
    , ("depDigest", .natural lm.depDigest)
    , ("activeCaps", authListToData lm.activeCaps)
    , ("liveness", Rehydration.toData lm.liveness) ]

/-- Deterministic `Obend.Core.Data` decoding of `LiveMembrane`. -/
@[expose] def LiveMembrane.ofData? : Data → Option LiveMembrane
  | .record
      [ ("surfaceId", .label surfaceId)
      , ("epoch", .natural epoch)
      , ("capDigest", .natural capDigest)
      , ("depDigest", .natural depDigest)
      , ("activeCaps", activeCapsData)
      , ("liveness", livenessData) ] => do
    let activeCaps ← authListOfData? activeCapsData
    let liveness ← Rehydration.ofData? livenessData
    pure { surfaceId, epoch, capDigest, depDigest, activeCaps, liveness }
  | _ => none

/-- Exact roundtrip theorem for `LiveMembrane.toData` / `LiveMembrane.ofData?`. -/
theorem LiveMembrane.ofData_toData (lm : LiveMembrane) :
    LiveMembrane.ofData? lm.toData = some lm := by
  cases lm
  simp [LiveMembrane.toData, LiveMembrane.ofData?, authListOfData_toData, Rehydration.ofData_toData]

/-- Dependency and capability boundary facts checked by the inner `Obend.Slot` protocol. -/
inductive MembraneFact where
  | depDigestValid (digest : Nat)
  | capBoundaryHolds (cap : Auth)
  deriving DecidableEq, Repr, Inhabited

/-- Slot payload bundling a `FrozenMembrane` with its required capability boundary and serialized `Data`. -/
structure MembranePayload where
  frozen       : FrozenMembrane
  requiredCaps : List Auth
  encoded      : Data
  deriving DecidableEq, Repr

/-- Construct a `MembranePayload` for a `FrozenMembrane` and required capability boundary. -/
@[expose] def membranePayload (fm : FrozenMembrane) (requiredCaps : List Auth) : MembranePayload :=
  { frozen := fm, requiredCaps := requiredCaps, encoded := fm.toData }

/-- Slot envelope pairing a `MembranePayload` with its expected dependency digest and support facts. -/
structure MembraneEnvelope where
  payload           : MembranePayload
  expectedDepDigest : Nat
  supports          : List MembraneFact
  deriving DecidableEq, Repr

/-- Construct a `MembraneEnvelope` over a `FrozenMembrane`. -/
@[expose] def membraneEnvelope (fm : FrozenMembrane) (expectedDepDigest : Nat) (requiredCaps : List Auth) :
    MembraneEnvelope :=
  { payload := membranePayload fm requiredCaps
  , expectedDepDigest := expectedDepDigest
  , supports := .depDigestValid fm.depDigest :: requiredCaps.map .capBoundaryHolds }

/-- Canonical 8-bit capability mask (`0..255`) over all `Auth` variants. -/
@[expose] def authCapBitmask (caps : List Auth) : Nat :=
  (if decide (.read ∈ caps) then 1 else 0) +
  (if decide (.write ∈ caps) then 2 else 0) +
  (if decide (.grant ∈ caps) then 4 else 0) +
  (if decide (.call ∈ caps) then 8 else 0) +
  (if decide (.reply ∈ caps) then 16 else 0) +
  (if decide (.reset ∈ caps) then 32 else 0) +
  (if decide (.control ∈ caps) then 64 else 0) +
  (if decide (.notify ∈ caps) then 128 else 0)

/-- Compute the canonical capability digest binding `caps` (`computeCapDigest [.read, .write] = 101`). -/
@[expose] def computeCapDigest (caps : List Auth) : Nat :=
  let mask := authCapBitmask caps
  if mask == 0 then 0 else 98 + mask

/-- Inner `Obend.Slot.Slot` over `FrozenMembrane`:
    - `supports`: requires `.depDigestValid fm.depDigest` and `.capBoundaryHolds cap` for every required capability,
    - `judge`: checks that `fm.depDigest == expectedDepDigest`, `fm.capDigest == computeCapDigest fm.heldCaps`,
      `fm.capDigest != 0`, and `fireGate requiredCaps fm.heldCaps`. -/
@[expose] def membraneSlot (expectedDepDigest : Nat) (requiredCaps : List Auth) :
    Obend.Slot.Slot MembraneFact FrozenMembrane where
  supports fm := .depDigestValid fm.depDigest :: requiredCaps.map .capBoundaryHolds
  judge fm :=
    fm.depDigest == expectedDepDigest &&
    fm.capDigest == computeCapDigest fm.heldCaps &&
    fm.capDigest != 0 &&
    fireGate requiredCaps fm.heldCaps

theorem membraneSlot_rejected_of_bad_depDigest
    (settled : MembraneFact → Bool) (expectedDepDigest : Nat) (requiredCaps : List Auth)
    (fm : FrozenMembrane) (h_bad : (fm.depDigest == expectedDepDigest) = false) :
    (membraneSlot expectedDepDigest requiredCaps).read settled (some fm) = .rejected fm := by
  simp [Obend.Slot.Slot.read, membraneSlot, h_bad]

theorem membraneSlot_rejected_of_bad_capDigest
    (settled : MembraneFact → Bool) (expectedDepDigest : Nat) (requiredCaps : List Auth)
    (fm : FrozenMembrane) (h_bad : (fm.capDigest == computeCapDigest fm.heldCaps) = false) :
    (membraneSlot expectedDepDigest requiredCaps).read settled (some fm) = .rejected fm := by
  simp [Obend.Slot.Slot.read, membraneSlot, h_bad]

theorem membraneSlot_rejected_of_missing_cap
    (settled : MembraneFact → Bool) (expectedDepDigest : Nat) (requiredCaps : List Auth)
    (fm : FrozenMembrane) (h_cap : fireGate requiredCaps fm.heldCaps = false) :
    (membraneSlot expectedDepDigest requiredCaps).read settled (some fm) = .rejected fm := by
  simp [Obend.Slot.Slot.read, membraneSlot, h_cap]

/-- Rehydrate a `FrozenMembrane` into a `LiveMembrane` using an `InteractionLog` and reachability flag. -/
@[expose] def rehydrateMembrane (fm : FrozenMembrane) (log : InteractionLog) (reachable : Bool) : LiveMembrane :=
  { surfaceId  := fm.surfaceId
  , epoch      := fm.epoch
  , capDigest  := fm.capDigest
  , depDigest  := fm.depDigest
  , activeCaps := fm.heldCaps
  , liveness   := classify log reachable }

/-- Rehydrate and advance a `FrozenMembrane` by `epochDelta`, preserving `capDigest`, `depDigest`, and `heldCaps`. -/
@[expose] def rehydrateAndStep (fm : FrozenMembrane) (epochDelta : Nat) : FrozenMembrane :=
  { fm with epoch := fm.epoch + epochDelta }

/-- Rehydrate and advance into a `LiveMembrane` by `epochDelta`. -/
@[expose] def rehydrateLiveAndStep (fm : FrozenMembrane) (log : InteractionLog) (reachable : Bool) (epochDelta : Nat) :
    LiveMembrane :=
  { (rehydrateMembrane fm log reachable) with epoch := fm.epoch + epochDelta }

/-- Relational `LawExpr` governing membrane rehydration transitions:
    1. `epoch` advances monotonically (`LawExpr.monotone "epoch"`),
    2. `capDigest` is preserved across steps (`LawExpr.writeOnce "capDigest"`). -/
@[expose] def membraneRehydrationLaw : LawExpr :=
  (LawExpr.monotone "epoch").and (LawExpr.writeOnce "capDigest")

/-- Constructive record field lookup avoiding `BEq String` (`Classical.choice`) in Lean 4.35. -/
@[expose] def fieldOfFieldList (field : String) : List (String × Data) → Option Int
  | [] => none
  | (k, v) :: rest =>
    if decide (k = field) then
      match v with
      | .natural n => some (Int.ofNat n)
      | .boolean b => some (if b then 1 else 0)
      | _          => none
    else
      fieldOfFieldList field rest

@[expose] def fieldOfData (field : String) : Data → Option Int
  | .record fields => fieldOfFieldList field fields
  | _ => none

/-- Constructive `LawRef` reader avoiding `BEq String` (`Classical.choice`) in Lean 4.35. -/
@[expose] def readLawRef (_facts : Facts) (state : Data) : LawRef → Option Int
  | .field name => fieldOfData name state
  | _           => none

/-- Constructive `LawExpr` evaluator avoiding `BEq Int` and `BEq String` (`Classical.choice`) in Lean 4.35. -/
@[expose] def evalLawExpr (facts : Facts) (old : Option Data) (new : Data) : LawExpr → Bool
  | .eqC ref value => decide (readLawRef facts new ref = some value)
  | .leC ref value =>
    match readLawRef facts new ref with
    | some x => decide (x ≤ value)
    | none   => false
  | .inC ref values =>
    match readLawRef facts new ref with
    | some x => values.any (fun v => decide (v = x))
    | none   => false
  | .eqR left right =>
    match readLawRef facts new left, readLawRef facts new right with
    | some x, some y => decide (x = y)
    | _, _           => false
  | .leR left right =>
    match readLawRef facts new left, readLawRef facts new right with
    | some x, some y => decide (x ≤ y)
    | _, _           => false
  | .leROff left right offset =>
    match readLawRef facts new left, readLawRef facts new right with
    | some x, some y => decide (x ≤ y + offset)
    | _, _           => false
  | .monotone field =>
    match old.bind (fieldOfData field), fieldOfData field new with
    | some before, some after => decide (before ≤ after)
    | _, _                    => false
  | .writeOnce field =>
    match old.bind (fieldOfData field) with
    | none        => false
    | some before => decide (fieldOfData field new = some before)
  | .not body => !(evalLawExpr facts old new body)
  | .and left right => evalLawExpr facts old new left && evalLawExpr facts old new right
  | .or left right => evalLawExpr facts old new left || evalLawExpr facts old new right
  | .implies premise conclusion => !(evalLawExpr facts old new premise) || evalLawExpr facts old new conclusion

/-- Evaluate `membraneRehydrationLaw` across a `FrozenMembrane` state transition,
    requiring `computeCapDigest old.heldCaps == computeCapDigest new.heldCaps` so `heldCaps`
    cannot be mutated across steps without changing `capDigest`. -/
@[expose] def evalMembraneRehydrationLaw (facts : Facts) (old new : FrozenMembrane) : Bool :=
  evalLawExpr facts (some old.toData) new.toData membraneRehydrationLaw &&
    decide (computeCapDigest old.heldCaps = computeCapDigest new.heldCaps)

/-- **Bridge Theorem (`rehydrate_satisfies_law`)**:
    Every `rehydrateAndStep` transition satisfies `membraneRehydrationLaw` (`epoch` is monotonic
    and `capDigest` and `heldCaps` digest are preserved). -/
theorem rehydrate_satisfies_law (facts : Facts) (fm : FrozenMembrane) (epochDelta : Nat) :
    evalMembraneRehydrationLaw facts fm (rehydrateAndStep fm epochDelta) = true := by
  change
    ((decide (Int.ofNat fm.epoch ≤ Int.ofNat (fm.epoch + epochDelta)) &&
      decide (some (Int.ofNat fm.capDigest) = some (Int.ofNat fm.capDigest))) &&
      decide (computeCapDigest fm.heldCaps = computeCapDigest fm.heldCaps)) = true
  have h1 : decide (Int.ofNat fm.epoch ≤ Int.ofNat (fm.epoch + epochDelta)) = true :=
    decide_eq_true (Int.ofNat_le.mpr (Nat.le_add_right fm.epoch epochDelta))
  have h2 : decide (some (Int.ofNat fm.capDigest) = some (Int.ofNat fm.capDigest)) = true :=
    decide_eq_true rfl
  have h3 : decide (computeCapDigest fm.heldCaps = computeCapDigest fm.heldCaps) = true :=
    decide_eq_true rfl
  rw [h1, h2, h3, Bool.and_true, Bool.and_true]

/-- Concrete facts and fixtures for `#tooth` refutation probes on `membraneRehydrationLaw`. -/
@[expose] def demoMembraneFacts : Facts := ⟨none, none, 1, 1⟩

@[expose] def demoFrozenBase : FrozenMembrane :=
  { surfaceId := "council-surface"
  , epoch     := 5
  , capDigest := 101
  , depDigest := 202
  , heldCaps  := [.read, .write] }

@[expose] def demoFrozenTamperedDigest : FrozenMembrane :=
  { demoFrozenBase with capDigest := 999 }

@[expose] def demoFrozenRegressedEpoch : FrozenMembrane :=
  { demoFrozenBase with epoch := 3 }

/-- Refutation theorem: a tampered capability digest (`101 → 999`) is rejected by `membraneRehydrationLaw`. -/
theorem membrane_tampered_digest_rejected :
    evalMembraneRehydrationLaw demoMembraneFacts demoFrozenBase demoFrozenTamperedDigest = false := rfl

/-- Refutation theorem: even if `capDigest = 0`, tampering it to `999` is rejected by `membraneRehydrationLaw`. -/
example :
    evalMembraneRehydrationLaw demoMembraneFacts
      { demoFrozenBase with capDigest := 0 }
      { demoFrozenBase with capDigest := 999 } = false := rfl

/-- Refutation theorem: a regressed epoch (`5 → 3`) is rejected by `membraneRehydrationLaw`. -/
theorem membrane_regressed_epoch_rejected :
    evalMembraneRehydrationLaw demoMembraneFacts demoFrozenBase demoFrozenRegressedEpoch = false := rfl

#tooth membrane_tampered_digest_rejected by mutation
  membraneRehydrationLaw := LawExpr.monotone "epoch"

#tooth membrane_regressed_epoch_rejected by mutation
  membraneRehydrationLaw := LawExpr.writeOnce "capDigest"

theorem ok_ne_refused_membrane (h : ("ok" : String) = "refused") : False := by
  have hlen : ("ok" : String).utf8ByteSize = ("refused" : String).utf8ByteSize :=
    congrArg String.utf8ByteSize h
  exact absurd hlen (by decide)

theorem guard_ok_membrane {c rest w : Term} {why : String}
    (h : Obend.Core.Term.Evaluates (Obend.Law.guard c why rest) (.inject "ok" w)) :
    Obend.Core.Term.Evaluates c (.boolean true) ∧
      Obend.Core.Term.Evaluates rest (.inject "ok" w) := by
  rcases Obend.Law.ifBool_inv h with ⟨b, hc, hr⟩
  cases b with
  | false =>
    dsimp at hr
    have hval := Obend.Law.evaluates_value (.inject "refused" (.label why)) hr
    injection hval with htag _
    exact False.elim (ok_ne_refused_membrane htag)
  | true =>
    exact ⟨hc, hr⟩

/-- Core4 state invariant for a membrane cell: `s.capDigest == expectedCapDigest`. -/
def membraneInvariant (expectedCapDigest : Nat) : Term :=
  .lam (eqNat (.get (.bound 0) "capDigest") (natT expectedCapDigest))

theorem subst_membraneInvariant (d : Nat) (σ : Nat → Term) :
    (membraneInvariant d).substitute σ = membraneInvariant d := by
  simp [membraneInvariant, eqNat, natT, Term.substitute, subst_binary, subst_get, subst_bound]
  rfl

/-- Core4 step relation body enforcing `old.epoch ≤ new.epoch` and `old.capDigest == new.capDigest`. -/
def membraneStepBody : Term :=
  Obend.Law.guard
    (andT
      (leNat (.get (.bound 2) "epoch") (.get (.bound 1) "epoch"))
      (eqNat (.get (.bound 2) "capDigest") (.get (.bound 1) "capDigest")))
    "membrane_step_violation"
    okT

/-- Core4 3-argument relational step law (`old`, `new`, `req`) for membrane rehydration. -/
def membraneStepRel : Term :=
  law3 membraneStepBody

/-- Core4 transition law combining `membraneInvariant` preservation with `membraneStepBody`. -/
def membraneTransitionLaw (expectedCapDigest : Nat) : Term :=
  law3
    (Obend.Law.guard
      (.app (membraneInvariant expectedCapDigest) (.bound 1))
      "cap_digest_mismatch"
      membraneStepBody)

/-- Parameterized `Obend.Law.CellContract` for a membrane cell with capability digest `expectedCapDigest`. -/
def membraneCellContractOf (expectedCapDigest : Nat) : CellContract where
  law := membraneTransitionLaw expectedCapDigest
  invariant := membraneInvariant expectedCapDigest
  stepRel := membraneStepRel
  inductive_preserves := by
    intro old new req _h_old h_adm
    rw [membraneTransitionLaw, admits_iff] at h_adm
    rcases h_adm with ⟨w, hw⟩
    rw [subst_guard] at hw
    have h_ok := guard_ok_membrane hw
    have h_cond := h_ok.1
    simp [subst_membraneInvariant, subst_bound, lawEnv] at h_cond
    exact h_cond
  step_sound := by
    intro old new req _h_old h_adm
    rw [membraneTransitionLaw, admits_iff] at h_adm
    rcases h_adm with ⟨w, hw⟩
    rw [subst_guard] at hw
    have h_ok := guard_ok_membrane hw
    rw [membraneStepRel, admits_iff]
    exact ⟨w, h_ok.2⟩

/-- Default `Obend.Law.CellContract` instance for `demoFrozenBase` (`capDigest = 101`). -/
def membraneCellContract : CellContract :=
  membraneCellContractOf demoFrozenBase.capDigest

end Obend.Vault.Rehydration

end
