module
/-
# Obend.Vault.Hyperedge — multi-cell wide-pullback turns, footprint pins, and contract invariants

Absorbs `minidregg/Kernel/Turn.lean` (Hyperedge, legs_agree, binary_balanced, binding_is_proper)
and `minidregg/Theory/PlanBinding.lean` (Footprint pins, admit, no_toctou, disjoint commutativity).

Key components:
1. `Hyperedge`: Abstract categorical wide-pullback turn over incidences `ι` with shared apex agreement.
2. `Hyperedge.legs_agree`: Pairwise agreement theorem avoiding O(N²) hypotheses.
3. `FootprintPin` & `PlanBinding.admit`: TOCTOU-free pre-state pin checking.
4. `VaultTurn`: Multi-cell wide-pullback turn carrying read pins, cell deltas, occasion data,
   cone condition (`agree`), and multi-asset conservation (`balanced`).
5. `VaultTurn.legs_agree`: Shared apex pullback agreement theorem for vault turns.
6. `no_toctou`: Preservation theorem proving that pinned turn validity and write effects are
   identical between authoring store `s₀` and admission store `s`.
7. `vaultTurn_disjoint_commutes`: Commutativity theorem for turns with disjoint write footprints.
8. `VaultTurn.post_invariants_hold` & `VaultTurn.post_step_sound`: Full integration with
   `Obend.Law.Contract.CellContract`.
-/
public import Obend.Law.Contract
public import Obend.Core.Data
public import Obend.Core.Term

@[expose] public section

namespace Obend.Vault

open Obend.Law
open Obend.Core.Data
open Obend.Core.Term

set_option autoImplicit false

/-! ## 1. Abstract Categorical Wide-Pullback Hyperedge -/

/-- **The turn as an abstract wide pullback.**
    `ι` indexes incidences. `step` is the transition function;
    `turnId i` reads incidence `i`'s post-step apex id;
    `halfEdge i` reads its signed balance contribution. -/
structure Hyperedge
    (ι : Type)
    (Carrier : Type) (Turn : Type)
    (TurnId : Type) (Bal : Type)
    [DecidableEq TurnId] [Zero Bal] [Add Bal]
    (step : Carrier → Turn → Carrier)
    (turnId : ι → Carrier → TurnId)
    (halfEdge : ι → Carrier → Turn → Bal)
    (incidences : List ι) where
  x : ι → Carrier
  t : Turn
  tid : TurnId
  agree : ∀ (i : ι), turnId i (step (x i) t) = tid
  balanced : (incidences.map (fun i => halfEdge i (x i) t)).foldl (· + ·) 0 = 0

/-- **`legs_agree` — Shared Apex Pullback Agreement Theorem.**
    Every pair of incidences shares an apex id as a THEOREM, avoiding O(N²) pairwise hypotheses. -/
theorem Hyperedge.legs_agree
    {ι Carrier Turn TurnId Bal : Type} [DecidableEq TurnId] [Zero Bal] [Add Bal]
    {step : Carrier → Turn → Carrier} {turnId : ι → Carrier → TurnId} {halfEdge : ι → Carrier → Turn → Bal}
    {incidences : List ι}
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge incidences) (i j : ι) :
    turnId i (step (H.x i) H.t) = turnId j (step (H.x j) H.t) :=
  (H.agree i).trans (H.agree j).symm

/-- **Binary Slice**: For a 2-incidence edge `[i₁, i₂]`, balanced is exactly `h₁ + h₂ = 0`. -/
theorem Hyperedge.binary_balanced
    {ι Carrier Turn TurnId Bal : Type} [DecidableEq TurnId] [Zero Bal] [Add Bal]
    {step : Carrier → Turn → Carrier} {turnId : ι → Carrier → TurnId} {halfEdge : ι → Carrier → Turn → Bal}
    {i₁ i₂ : ι}
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge [i₁, i₂])
    (h_zero : ∀ (b : Bal), (0 : Bal) + b = b) :
    halfEdge i₁ (H.x i₁) H.t + halfEdge i₂ (H.x i₂) H.t = 0 := by
  have hb := H.balanced
  simp only [List.map, List.foldl] at hb
  rw [h_zero] at hb
  exact hb

/-- **`binding_is_proper`**: Cone agreement does not entail balance conservation.
    The conservation aggregate is genuine data, not derivable from the cone. -/
theorem Hyperedge.binding_is_proper :
    ∃ (x : Unit → Int) (t : Int) (tid : Int)
      (step : Int → Int → Int) (turnId : Unit → Int → Int) (halfEdge : Unit → Int → Int → Int)
      (incidences : List Unit),
      (∀ (i : Unit), turnId i (step (x i) t) = tid) ∧
      (incidences.map (fun i => halfEdge i (x i) t)).foldl (· + ·) 0 ≠ 0 := by
  refine ⟨fun _ => 0, 0, 0, fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 1, [()], ?_, ?_⟩
  · intro _; rfl
  · simp

/-! ## 2. Concrete Obend Vault Store and Footprints -/

abbrev VaultStore := String → Option Data

def emptyStore : VaultStore := fun _ => none

def updateStore (s : VaultStore) (cell : String) (val : Option Data) : VaultStore :=
  fun c => if c == cell then val else s c

structure FootprintPin where
  cell : String
  observed : Option Data
  digest : Option ByteArray := none

abbrev Footprint := List FootprintPin

def Footprint.cells (fp : Footprint) : List String :=
  fp.map FootprintPin.cell

def Footprint.Holds (store : VaultStore) (fp : Footprint) : Prop :=
  ∀ p ∈ fp, store p.cell = p.observed

inductive Refusal where
  | footprintStale (cell : String) (expected current : Option Data)
  | contractViolation (cell : String) (reason : String)
  | widePullbackMismatch (cell : String) (cellTid apexTid : ByteArray)
  | unbalancedConservation (asset : String) (netSum : Int)

def Footprint.firstStale? (store : VaultStore) : Footprint → Option (String × Option Data × Option Data)
  | [] => none
  | p :: rest =>
      match store p.cell, p.observed with
      | none, none => Footprint.firstStale? store rest
      | some d1, some d2 =>
          if Obend.Law.termEq d1.term d2.term then
            Footprint.firstStale? store rest
          else
            some (p.cell, p.observed, store p.cell)
      | _, _ => some (p.cell, p.observed, store p.cell)

def admitFootprint (store : VaultStore) (fp : Footprint) : Except Refusal Unit :=
  match Footprint.firstStale? store fp with
  | none => .ok ()
  | some (cell, exp, cur) => .error (.footprintStale cell exp cur)

theorem holds_of_pin_agrees {s₀ s : VaultStore} {fp : Footprint}
    (h₀ : Footprint.Holds s₀ fp) (h : Footprint.Holds s fp) (p : FootprintPin) (hp : p ∈ fp) :
    s₀ p.cell = s p.cell := by
  rw [h₀ p hp, h p hp]

/-! ## 3. Cell Deltas & VaultTurn Structure -/

structure CellDelta where
  cell : String
  preState : Data
  postState : Data
  touchedFields : List String := []
  halfEdges : List (String × Int) := []
  cert : Option ContractCert := none

/-- Compute the net balance change for a specific asset in a single cell delta. -/
def deltaAsset (d : CellDelta) (asset : String) : Int :=
  match d.halfEdges.find? (·.1 == asset) with
  | some (_, amount) => amount
  | none => 0

/-- Sum asset balance adjustments across all cell deltas. -/
def sumAssetDelta (writeCells : List CellDelta) (asset : String) : Int :=
  (writeCells.map (fun d => deltaAsset d asset)).foldl (· + ·) 0

/-- Request payload delivered to a cell contract under a turn. -/
def turnRequest (turnId : ByteArray) (occasion : Data) (cell : String) : Data :=
  .record [
    ("turn", .record [("id", .label ((String.fromUTF8? turnId).getD "")), ("cell", .label cell)]),
    ("occasion", occasion)
  ]

/-- Leg turn ID projected by a cell delta. -/
def legTurnId (d : CellDelta) : ByteArray :=
  match d.cert with
  | some (.byLoweredDecider _ _ r) => r
  | _ => ByteArray.empty

/-- Multi-cell wide-pullback turn structure. -/
structure VaultTurn where
  turnId : ByteArray
  readPins : Footprint
  writeCells : List CellDelta
  occasion : Data
  agree : ∀ d ∈ writeCells, legTurnId d = turnId
  balanced : ∀ (asset : String), sumAssetDelta writeCells asset = 0

def VaultTurn.writeFootprint (turn : VaultTurn) : List String :=
  turn.writeCells.map CellDelta.cell

def VaultTurn.readFootprint (turn : VaultTurn) : List String :=
  turn.readPins.map FootprintPin.cell

def VaultTurn.accessFootprint (turn : VaultTurn) : List String :=
  (turn.readFootprint ++ turn.writeFootprint).eraseDups

/-- **Shared Apex Pullback Agreement Theorem for `VaultTurn`**.
    Any two mutating cell deltas in the turn agree on their projected turn ID without O(N²) checks. -/
theorem VaultTurn.legs_agree (turn : VaultTurn) {d₁ d₂ : CellDelta}
    (h₁ : d₁ ∈ turn.writeCells) (h₂ : d₂ ∈ turn.writeCells) :
    legTurnId d₁ = legTurnId d₂ :=
  (turn.agree d₁ h₁).trans (turn.agree d₂ h₂).symm

/-! ## 4. Turn Application & TOCTOU-Free Preservation -/

/-- Apply a turn to a vault store. -/
def applyTurn (s : VaultStore) (turn : VaultTurn) : VaultStore :=
  fun c =>
    match turn.writeCells.find? (fun d => d.cell == c) with
    | some d => some d.postState
    | none => s c

/-- Turn validity at a store against a contract registry. -/
def ValidAt (s : VaultStore) (turn : VaultTurn) (contracts : String → Option CellContract) : Prop :=
  Footprint.Holds s turn.readPins ∧
  (∀ d ∈ turn.writeCells, s d.cell = some d.preState) ∧
  (∀ d ∈ turn.writeCells, ∀ C, contracts d.cell = some C →
    Holds C.invariant d.preState ∧
    Admits C.law d.preState d.postState (turnRequest turn.turnId turn.occasion d.cell))

/-- Frame property: applyTurn leaves untouched cells untouched. -/
theorem applyTurn_frame (s : VaultStore) (turn : VaultTurn) (c : String)
    (h_out : turn.writeCells.find? (fun d => d.cell == c) = none) :
    applyTurn s turn c = s c := by
  simp [applyTurn, h_out]

/-- Update property: applyTurn updates written cells to their postState. -/
theorem applyTurn_write (s : VaultStore) (turn : VaultTurn) (d : CellDelta)
    (h_find : turn.writeCells.find? (fun x => x.cell == d.cell) = some d) :
    applyTurn s turn d.cell = some d.postState := by
  simp [applyTurn, h_find]

/-- **TOCTOU-Free Footprint Pin Preservation Theorem (`no_toctou`)**.
    If a turn's accessed cells are covered by footprint pins that hold at both
    authored store `s₀` and admission store `s`:
    1. Turn validity at `s` is logically equivalent to validity at `s₀`.
    2. Written cells receive identical post-states regardless of whether executed on `s₀` or `s`.
    3. Unwritten cells strictly preserve their store value from `s`. -/
theorem no_toctou (s₀ s : VaultStore) (turn : VaultTurn) (contracts : String → Option CellContract)
    (h_cover : ∀ d ∈ turn.writeCells, ∃ p ∈ turn.readPins, p.cell = d.cell ∧ p.observed = some d.preState)
    (h_fp_s0 : Footprint.Holds s₀ turn.readPins)
    (h_fp_s : Footprint.Holds s turn.readPins) :
    (ValidAt s₀ turn contracts ↔ ValidAt s turn contracts) ∧
    (∀ c, applyTurn s turn c =
      match turn.writeCells.find? (fun d => d.cell == c) with
      | some _ => applyTurn s₀ turn c
      | none => s c) := by
  have h_cell_agree : ∀ d ∈ turn.writeCells, s₀ d.cell = s d.cell := by
    intro d hd
    obtain ⟨p, hp_mem, hp_cell, hp_obs⟩ := h_cover d hd
    have h0 := h_fp_s0 p hp_mem
    have hs := h_fp_s p hp_mem
    rw [hp_cell] at h0 hs
    rw [h0, hs]
  have h_pre_s0 : ∀ d ∈ turn.writeCells, s₀ d.cell = some d.preState := by
    intro d hd
    obtain ⟨p, hp_mem, hp_cell, hp_obs⟩ := h_cover d hd
    have h0 := h_fp_s0 p hp_mem
    rw [hp_cell] at h0
    rw [h0, hp_obs]
  have h_pre_s : ∀ d ∈ turn.writeCells, s d.cell = some d.preState := by
    intro d hd
    obtain ⟨p, hp_mem, hp_cell, hp_obs⟩ := h_cover d hd
    have hs := h_fp_s p hp_mem
    rw [hp_cell] at hs
    rw [hs, hp_obs]
  have h_valid_iff : ValidAt s₀ turn contracts ↔ ValidAt s turn contracts := by
    constructor
    · intro ⟨_, _, h_contracts⟩
      exact ⟨h_fp_s, h_pre_s, h_contracts⟩
    · intro ⟨_, _, h_contracts⟩
      exact ⟨h_fp_s0, h_pre_s0, h_contracts⟩
  refine ⟨h_valid_iff, fun c => ?_⟩
  simp only [applyTurn]
  split
  · rfl
  · rfl

/-! ## 5. Disjoint Commutativity Theorem -/

theorem mem_of_find?_some {α : Type} {p : α → Bool} {l : List α} {a : α} :
    l.find? p = some a → a ∈ l ∧ p a = true := by
  intro h
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.find?] at h
    split at h
    · rename_i hpx
      cases h
      exact ⟨List.Mem.head xs, hpx⟩
    · rename_i _
      have ⟨h_mem, h_pa⟩ := ih h
      exact ⟨List.Mem.tail x h_mem, h_pa⟩

def DisjointTurns (T₁ T₂ : VaultTurn) : Prop :=
  (∀ d ∈ T₁.writeCells, T₂.writeCells.find? (fun x => x.cell == d.cell) = none) ∧
  (∀ d ∈ T₂.writeCells, T₁.writeCells.find? (fun x => x.cell == d.cell) = none)

theorem find?_cell_eq {cells : List CellDelta} {c : String} {d : CellDelta}
    (h : cells.find? (fun x => x.cell == c) = some d) : d.cell = c := by
  have ⟨_, h_pa⟩ := mem_of_find?_some h
  simp only [beq_iff_eq] at h_pa
  exact h_pa

/-- **Disjoint Turn Commutativity (`vaultTurn_disjoint_commutes`)**.
    Turns with disjoint write footprints commute: applying them in either order
    reaches the exact same vault store. -/
theorem vaultTurn_disjoint_commutes (s : VaultStore) (T₁ T₂ : VaultTurn)
    (h_disj : DisjointTurns T₁ T₂) :
    applyTurn (applyTurn s T₁) T₂ = applyTurn (applyTurn s T₂) T₁ := by
  funext c
  simp only [applyTurn]
  cases h1 : T₁.writeCells.find? (fun d => d.cell == c) with
  | some d1 =>
    have h_c1 : d1.cell = c := find?_cell_eq h1
    have ⟨hd1_mem, _⟩ := mem_of_find?_some h1
    have h2_none := h_disj.1 d1 hd1_mem
    rw [h_c1] at h2_none
    rw [h2_none]
  | none =>
    cases h2 : T₂.writeCells.find? (fun d => d.cell == c) with
    | some _ =>
      rfl
    | none =>
      rfl

/-! ## 6. Integration with CellContract -/

/-- **Post-State Inductive Invariance Theorem**.
    Under an admitted VaultTurn, every mutated cell's post-state satisfies
    its active contract invariant. -/
theorem VaultTurn.post_invariants_hold (turn : VaultTurn) (s : VaultStore)
    (contracts : String → Option CellContract) (h_valid : ValidAt s turn contracts) :
    ∀ d ∈ turn.writeCells, ∀ C, contracts d.cell = some C →
      Holds C.invariant d.postState := by
  intro d hd C hC
  obtain ⟨_, _, h_contracts⟩ := h_valid
  have ⟨h_inv, h_adm⟩ := h_contracts d hd C hC
  exact C.inductive_preserves d.preState d.postState (turnRequest turn.turnId turn.occasion d.cell) h_inv h_adm

/-- **Post-State Step Soundness Theorem**.
    Under an admitted VaultTurn, every cell transition satisfies its contract step specification. -/
theorem VaultTurn.post_step_sound (turn : VaultTurn) (s : VaultStore)
    (contracts : String → Option CellContract) (h_valid : ValidAt s turn contracts) :
    ∀ d ∈ turn.writeCells, ∀ C, contracts d.cell = some C →
      Admits C.stepRel d.preState d.postState (turnRequest turn.turnId turn.occasion d.cell) := by
  intro d hd C hC
  obtain ⟨_, _, h_contracts⟩ := h_valid
  have ⟨h_inv, h_adm⟩ := h_contracts d hd C hC
  exact C.step_sound d.preState d.postState (turnRequest turn.turnId turn.occasion d.cell) h_inv h_adm

/-- **Turn Relaw Preservation**.
    If a turn transition updates a cell's active contract law from `C.law` to `newLaw`
    with a certificate proving `Narrows newLaw C.law`, the updated contract inherits
    both inductive invariant preservation and step soundness. -/
def VaultTurn.relaw_sound (C : CellContract) (newLaw : Term) (h_nar : Narrows newLaw C.law) :
    CellContract :=
  cellContract_relaw_sound C newLaw h_nar

end Obend.Vault
