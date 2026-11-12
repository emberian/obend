module
/-
# Obend.Vault.Hyperedge — multi-cell wide-pullback turns, footprint pins, and contract invariants

Absorbs `minidregg/Kernel/Turn.lean` (Hyperedge, legs_agree, binary_balanced, binding_is_proper)
and `minidregg/Theory/PlanBinding.lean` (Footprint pins, admit, no_toctou, disjoint commutativity).

Remediated for Milestone 2 Iteration 2:
1. Critical Finding 1: Added `nodup_cells : (writeCells.map CellDelta.cell).Nodup` to `VaultTurn`.
   Proved `VaultTurn.find?_mem`, adapted `applyTurn_write`, and proved `VaultTurn.store_post_invariants_hold`.
2. Major Finding 3: Updated `DisjointTurns` to enforce Bernstein Independence over access footprints.
   Proved `admits_after_disjoint` and `disjoint_both_orders`.
3. Minor Finding 6: Removed unused `digest` field from `FootprintPin`.
-/
public import Obend.Law.Contract
public import Obend.Core.Data
public import Obend.Core.Term
public import Obend.Judge.Class
public import Obend.Tactic.Tooth

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

/-- FootprintPin binds the observed value of a cell at authoring time.
    (Remediated: removed unused `digest` field). -/
structure FootprintPin where
  cell : String
  observed : Option Data

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
  | duplicateWriteCell (cell : String)

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

/-- Executable check for duplicate write cells during turn admission. -/
def firstDuplicateCell? : List String → Option String
  | [] => none
  | c :: rest =>
      if rest.any (· == c) then some c
      else firstDuplicateCell? rest

def checkNodupCells (cells : List String) : Except Refusal Unit :=
  match firstDuplicateCell? cells with
  | none => .ok ()
  | some c => .error (.duplicateWriteCell c)

theorem holds_of_pin_agrees {s₀ s : VaultStore} {fp : Footprint}
    (h₀ : Footprint.Holds s₀ fp) (h : Footprint.Holds s fp) (p : FootprintPin) (hp : p ∈ fp) :
    s₀ p.cell = s p.cell := by
  rw [h₀ p hp, h p hp]

/-! ## 3. Cell Deltas & VaultTurn Structure -/

/-- A signed asset balance adjustment `(asset, delta)` attached to a `CellDelta`. -/
abbrev HalfEdge := String × Int

/-- Lightweight turn-ID tag attached to a `CellDelta` leg (e.g. by lowered form/move compilers). -/
inductive LegTurnTag where
  | byLoweredDecider (label : String) (pins : List FootprintPin) (turnId : ByteArray)

structure CellDelta where
  cell : String
  preState : Data
  postState : Data
  touchedFields : List String := []
  halfEdges : List HalfEdge := []
  boundTurnId : ByteArray := ByteArray.empty
  cert : Option LegTurnTag := none

/-- Compute the net balance change for a specific asset in a single cell delta. -/
def deltaAsset (d : CellDelta) (asset : String) : Int :=
  match d.halfEdges.find? (·.1 == asset) with
  | some (_, amount) => amount
  | none => 0

/-- Alias for `deltaAsset`: the reported half-edge balance delta for `asset` in `d`. -/
abbrev cellAssetDelta (d : CellDelta) (asset : String) : Int :=
  deltaAsset d asset

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
  | none => d.boundTurnId

/-- External judge witness cited by a `VaultTurn`. -/
structure TurnWitness where
  formatName : String
  version : String
  grade : Nat
  objBytes : String
  certBytes : String
  deriving Repr, DecidableEq

/-- Multi-cell wide-pullback turn structure.
    Remediated: includes `nodup_cells` ensuring uniqueness of mutated cells
    and `witnesses` for external `Judge.Format` certificates. -/
structure VaultTurn where
  turnId : ByteArray
  readPins : Footprint
  writeCells : List CellDelta
  occasion : Data
  witnesses : List TurnWitness := []
  agree : ∀ d ∈ writeCells, legTurnId d = turnId
  balanced : ∀ (asset : String), sumAssetDelta writeCells asset = 0
  nodup_cells : (writeCells.map CellDelta.cell).Nodup := by decide

def VaultTurn.writeFootprint (turn : VaultTurn) : List String :=
  turn.writeCells.map CellDelta.cell

def VaultTurn.readFootprint (turn : VaultTurn) : List String :=
  turn.readPins.map FootprintPin.cell

def VaultTurn.accessFootprint (turn : VaultTurn) : List String :=
  (turn.readFootprint ++ turn.writeFootprint).eraseDups

theorem VaultTurn.writeFootprint_nodup (turn : VaultTurn) :
    turn.writeFootprint.Nodup :=
  turn.nodup_cells

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

/-- Look up a registered `Obend.Judge.Format` by `(formatName, version)`. -/
def findJudgeFormat : List Obend.Judge.Format → String → String → Option Obend.Judge.Format
  | [], _, _ => none
  | F :: rest, name, ver =>
    if F.name == name && F.version == ver then some F
    else findJudgeFormat rest name ver

/-- Executable check that a single `TurnWitness` is accepted by its registered `Obend.Judge.Format`. -/
def checkTurnWitness (formats : List Obend.Judge.Format) (w : TurnWitness) : Bool :=
  match findJudgeFormat formats w.formatName w.version with
  | some F =>
    match F.checkBytes w.grade w.objBytes w.certBytes with
    | .ok => true
    | _ => false
  | none => false

/-- Turn validity at a store against a contract registry and judge format registry
    (verifying footprint pins, pre-states, contract invariants/laws, and all cited `TurnWitness`es). -/
def ValidAt (s : VaultStore) (turn : VaultTurn)
    (contracts : String → Option CellContract)
    (formats : List Obend.Judge.Format := []) : Prop :=
  Footprint.Holds s turn.readPins ∧
  (∀ d ∈ turn.writeCells, s d.cell = some d.preState) ∧
  (∀ d ∈ turn.writeCells, ∀ C, contracts d.cell = some C →
    Holds C.invariant d.preState ∧
    Admits C.law d.preState d.postState (turnRequest turn.turnId turn.occasion d.cell)) ∧
  (∀ w ∈ turn.witnesses, ∃ F,
    findJudgeFormat formats w.formatName w.version = some F ∧
    F.checkBytes w.grade w.objBytes w.certBytes = .ok)

/-- Soundness of witness verification in `ValidAt`: every cited witness
    decodes to a valid `(o, c)` pair satisfying `F.judge.Meaning o c`. -/
theorem ValidAt.witness_sound {s : VaultStore} {turn : VaultTurn}
    {contracts : String → Option CellContract} {formats : List Obend.Judge.Format}
    (h_valid : ValidAt s turn contracts formats)
    {w : TurnWitness} (hw : w ∈ turn.witnesses) :
    ∃ F, findJudgeFormat formats w.formatName w.version = some F ∧
      ∃ (o : F.Obj) (c : F.Cert),
        F.decodeObj w.objBytes = .ok o ∧
        F.decodeCert w.certBytes = .ok c ∧
        F.judge.Meaning o c := by
  obtain ⟨_, _, _, h_wit⟩ := h_valid
  obtain ⟨F, hF, hchk⟩ := h_wit w hw
  exact ⟨F, hF, F.checkBytes_sound hchk⟩

/-- `checkTurnWitness` decides the witness clause of `ValidAt`: an accepted witness names a
registered format that accepts its bytes. -/
theorem checkTurnWitness_sound {formats : List Obend.Judge.Format} {w : TurnWitness}
    (h : checkTurnWitness formats w = true) :
    ∃ F, findJudgeFormat formats w.formatName w.version = some F ∧
      F.checkBytes w.grade w.objBytes w.certBytes = .ok := by
  unfold checkTurnWitness at h
  split at h
  · rename_i F hF
    split at h
    · rename_i hok
      exact ⟨F, hF, hok⟩
    · cases h
  · cases h

/-! ### 3b. Constructing turns

`VaultTurn` carries three proof fields. `VaultTurn.ofWitnessLegs` is the constructor a host uses:
each write leg's contract certificate carries the turn id (so `agree` holds by construction), the
legs report no half-edges (so `balanced` holds), and the write cells are checked duplicate-free.
`Obend.FFI.Bridge.turnCommitCore` builds every committed turn through it, with the woven judge
witnesses in `witnesses`, and checks them with `checkTurnWitness`. -/

/-- A write leg bound to the turn apex `tid` (`legTurnId_witnessLeg`). -/
def witnessLeg (tid : ByteArray) (cell : String) (pre post : Data) : CellDelta :=
  { cell := cell, preState := pre, postState := post,
    boundTurnId := tid }

theorem legTurnId_witnessLeg (tid : ByteArray) (cell : String) (pre post : Data) :
    legTurnId (witnessLeg tid cell pre post) = tid := rfl

theorem deltaAsset_witnessLeg (tid : ByteArray) (cell : String) (pre post : Data) (asset : String) :
    deltaAsset (witnessLeg tid cell pre post) asset = 0 := rfl

/-- A write leg before it is bound to a turn: the cell, its pre-state, and its post-state. -/
abbrev WitnessLegSpec := String × Data × Data

/-- The write legs of a turn `tid` over `legs`. -/
def witnessLegs (tid : ByteArray) (legs : List WitnessLegSpec) : List CellDelta :=
  legs.map fun l => witnessLeg tid l.1 l.2.1 l.2.2

theorem foldl_deltaAsset_witnessLegs (tid : ByteArray) (asset : String) :
    ∀ (legs : List WitnessLegSpec) (acc : Int),
      ((legs.map fun l => witnessLeg tid l.1 l.2.1 l.2.2).map (fun d => deltaAsset d asset)).foldl
        (· + ·) acc = acc
  | [], _ => rfl
  | l :: rest, acc => by
    rw [List.map_cons, List.map_cons, List.foldl_cons, deltaAsset_witnessLeg, Int.add_zero]
    exact foldl_deltaAsset_witnessLegs tid asset rest acc

theorem sumAssetDelta_witnessLegs (tid : ByteArray) (legs : List WitnessLegSpec) (asset : String) :
    sumAssetDelta (witnessLegs tid legs) asset = 0 :=
  foldl_deltaAsset_witnessLegs tid asset legs 0

/-- **The turn constructor.** `none` exactly when two legs name one cell. -/
def VaultTurn.ofWitnessLegs (tid : ByteArray) (readPins : Footprint) (legs : List WitnessLegSpec)
    (occasion : Data) (witnesses : List TurnWitness) : Option VaultTurn :=
  if h : (legs.map (·.1)).Nodup then
    some
      { turnId := tid
        readPins := readPins
        writeCells := witnessLegs tid legs
        occasion := occasion
        witnesses := witnesses
        agree := by
          intro d hd
          simp only [witnessLegs, List.mem_map] at hd
          obtain ⟨l, _, rfl⟩ := hd
          rfl
        balanced := fun asset => sumAssetDelta_witnessLegs tid legs asset
        nodup_cells := by
          show ((witnessLegs tid legs).map CellDelta.cell).Nodup
          simp only [witnessLegs, List.map_map]
          exact h }
  else
    none

theorem VaultTurn.ofWitnessLegs_fields {tid : ByteArray} {readPins : Footprint}
    {legs : List WitnessLegSpec} {occasion : Data} {witnesses : List TurnWitness} {turn : VaultTurn}
    (h : VaultTurn.ofWitnessLegs tid readPins legs occasion witnesses = some turn) :
    turn.turnId = tid ∧ turn.readPins = readPins ∧ turn.writeCells = witnessLegs tid legs ∧
      turn.witnesses = witnesses := by
  unfold VaultTurn.ofWitnessLegs at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- A constructed turn whose witnesses all pass `checkTurnWitness` satisfies the witness clause
of `ValidAt`. -/
theorem VaultTurn.ofWitnessLegs_witness_clause {formats : List Obend.Judge.Format}
    {tid : ByteArray} {readPins : Footprint} {legs : List WitnessLegSpec} {occasion : Data}
    {witnesses : List TurnWitness} {turn : VaultTurn}
    (h : VaultTurn.ofWitnessLegs tid readPins legs occasion witnesses = some turn)
    (hall : turn.witnesses.all (checkTurnWitness formats) = true) :
    ∀ w ∈ turn.witnesses, ∃ F,
      findJudgeFormat formats w.formatName w.version = some F ∧
      F.checkBytes w.grade w.objBytes w.certBytes = .ok := by
  have ⟨_, _, _, hwit⟩ := VaultTurn.ofWitnessLegs_fields h
  rw [hwit] at hall ⊢
  intro w hw
  exact checkTurnWitness_sound (List.all_eq_true.mp hall w hw)

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

theorem find?_none_of_not_mem {cells : List CellDelta} {c : String}
    (h : c ∉ cells.map CellDelta.cell) :
    cells.find? (fun d => d.cell == c) = none := by
  cases hfind : cells.find? (fun d => d.cell == c) with
  | none => rfl
  | some d =>
    have ⟨hmem, hcond⟩ := mem_of_find?_some hfind
    simp only [beq_iff_eq] at hcond
    subst hcond
    have hmap : d.cell ∈ cells.map CellDelta.cell := List.mem_map_of_mem hmem
    contradiction

theorem find?_some_of_nodup {cells : List CellDelta} {d : CellDelta}
    (hnd : (cells.map CellDelta.cell).Nodup) (hd : d ∈ cells) :
    cells.find? (fun x => x.cell == d.cell) = some d := by
  induction cells with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have ⟨hx_not_mem, hxs_nd⟩ := hnd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd_tail
    · simp only [List.find?, beq_self_eq_true]
    · simp only [List.find?]
      by_cases h : x.cell == d.cell
      · simp only [beq_iff_eq] at h
        have hd_cell_mem : d.cell ∈ xs.map CellDelta.cell := List.mem_map_of_mem hd_tail
        rw [h] at hx_not_mem
        contradiction
      · simp only [h]
        exact ih hxs_nd hd_tail

/-- Frame property: applyTurn leaves untouched cells untouched. -/
theorem applyTurn_frame (s : VaultStore) (turn : VaultTurn) (c : String)
    (h_out : turn.writeCells.find? (fun d => d.cell == c) = none) :
    applyTurn s turn c = s c := by
  simp [applyTurn, h_out]

/-- Frame property from writeFootprint non-membership. -/
theorem applyTurn_frame_of_not_mem (s : VaultStore) (turn : VaultTurn) (c : String)
    (h_out : c ∉ turn.writeFootprint) :
    applyTurn s turn c = s c :=
  applyTurn_frame s turn c (find?_none_of_not_mem h_out)

/-- Under `nodup_cells`, every delta in `writeCells` is uniquely found by `find?`. -/
theorem VaultTurn.find?_mem (turn : VaultTurn) {d : CellDelta}
    (hd : d ∈ turn.writeCells) :
    turn.writeCells.find? (fun x => x.cell == d.cell) = some d :=
  find?_some_of_nodup turn.nodup_cells hd

/-- Strengthened update property: applyTurn updates written cells to their postState. -/
theorem applyTurn_write (s : VaultStore) (turn : VaultTurn) (d : CellDelta)
    (hd : d ∈ turn.writeCells) :
    applyTurn s turn d.cell = some d.postState := by
  simp only [applyTurn, turn.find?_mem hd]

/-- **TOCTOU-Free Footprint Pin Preservation Theorem (`no_toctou`)**.
    If a turn's accessed cells are covered by footprint pins that hold at both
    authored store `s₀` and admission store `s`:
    1. Turn validity (including all cited judge witnesses) at `s` is logically equivalent to validity at `s₀`.
    2. Written cells receive identical post-states regardless of whether executed on `s₀` or `s`.
    3. Unwritten cells strictly preserve their store value from `s`. -/
theorem no_toctou (s₀ s : VaultStore) (turn : VaultTurn)
    (contracts : String → Option CellContract)
    (formats : List Obend.Judge.Format := [])
    (h_cover : ∀ d ∈ turn.writeCells, ∃ p ∈ turn.readPins, p.cell = d.cell ∧ p.observed = some d.preState)
    (h_fp_s0 : Footprint.Holds s₀ turn.readPins)
    (h_fp_s : Footprint.Holds s turn.readPins) :
    (ValidAt s₀ turn contracts formats ↔ ValidAt s turn contracts formats) ∧
    (∀ c, applyTurn s turn c =
      if c ∈ turn.writeFootprint then applyTurn s₀ turn c else s c) := by
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
  have h_valid_iff : ValidAt s₀ turn contracts formats ↔ ValidAt s turn contracts formats := by
    constructor
    · intro ⟨_, _, h_contracts, h_wit⟩
      exact ⟨h_fp_s, h_pre_s, h_contracts, h_wit⟩
    · intro ⟨_, _, h_contracts, h_wit⟩
      exact ⟨h_fp_s0, h_pre_s0, h_contracts, h_wit⟩
  refine ⟨h_valid_iff, fun c => ?_⟩
  split
  · rename_i hc
    have ⟨d, hd_mem, hd_cell⟩ : ∃ d ∈ turn.writeCells, d.cell = c := by
      simp only [VaultTurn.writeFootprint, List.mem_map] at hc
      exact hc
    subst hd_cell
    rw [applyTurn_write s turn d hd_mem, applyTurn_write s₀ turn d hd_mem]
  · rename_i hc
    exact applyTurn_frame_of_not_mem s turn c hc

/-! ## 5. Bernstein Independence and Disjoint Commutativity -/

/-- Bernstein Independence for VaultTurns:
    Neither turn writes to any cell in the other turn's access footprint
    (covering both read pins and write cells). -/
def DisjointTurns (T₁ T₂ : VaultTurn) : Prop :=
  (∀ c ∈ T₁.writeFootprint, c ∉ T₂.accessFootprint) ∧
  (∀ c ∈ T₂.writeFootprint, c ∉ T₁.accessFootprint)

theorem mem_eraseDups {α : Type} [DecidableEq α] {l : List α} {a : α} :
    a ∈ l.eraseDups ↔ a ∈ l := List.mem_eraseDups

theorem mem_accessFootprint (turn : VaultTurn) (c : String) :
    c ∈ turn.accessFootprint ↔ c ∈ turn.readFootprint ∨ c ∈ turn.writeFootprint := by
  simp only [VaultTurn.accessFootprint, mem_eraseDups, List.mem_append]

theorem disjoint_write_write {T₁ T₂ : VaultTurn} (h_disj : DisjointTurns T₁ T₂)
    {d : CellDelta} (hd : d ∈ T₁.writeCells) :
    T₂.writeCells.find? (fun x => x.cell == d.cell) = none := by
  have hd_cell : d.cell ∈ T₁.writeFootprint := List.mem_map_of_mem hd
  have h_not_acc := h_disj.1 d.cell hd_cell
  rw [mem_accessFootprint] at h_not_acc
  have h_not_w : d.cell ∉ T₂.writeFootprint := fun hw => h_not_acc (Or.inr hw)
  exact find?_none_of_not_mem h_not_w

theorem disjoint_read_write {T₁ T₂ : VaultTurn} (h_disj : DisjointTurns T₁ T₂)
    {p : FootprintPin} (hp : p ∈ T₂.readPins) :
    p.cell ∉ T₁.writeFootprint := by
  intro h_in
  have h_not_acc := h_disj.1 p.cell h_in
  rw [mem_accessFootprint] at h_not_acc
  apply h_not_acc
  left
  exact List.mem_map_of_mem hp

theorem disjoint_write_write' {T₁ T₂ : VaultTurn} (h_disj : DisjointTurns T₁ T₂)
    {d : CellDelta} (hd : d ∈ T₂.writeCells) :
    d.cell ∉ T₁.writeFootprint := by
  intro h_in
  have h_not_acc := h_disj.1 d.cell h_in
  rw [mem_accessFootprint] at h_not_acc
  apply h_not_acc
  right
  exact List.mem_map_of_mem hd

/-- **Disjoint Turn Commutativity (`vaultTurn_disjoint_commutes`)**.
    Turns satisfying Bernstein independence commute: applying them in either order
    reaches the exact same vault store. -/
theorem vaultTurn_disjoint_commutes (s : VaultStore) (T₁ T₂ : VaultTurn)
    (h_disj : DisjointTurns T₁ T₂) :
    applyTurn (applyTurn s T₁) T₂ = applyTurn (applyTurn s T₂) T₁ := by
  funext c
  simp only [applyTurn]
  cases h1 : T₁.writeCells.find? (fun d => d.cell == c) with
  | some d1 =>
    have ⟨hd1_mem, hd1_eq⟩ := mem_of_find?_some h1
    simp only [beq_iff_eq] at hd1_eq
    subst hd1_eq
    have h2_none := disjoint_write_write h_disj hd1_mem
    rw [h2_none]
  | none =>
    cases h2 : T₂.writeCells.find? (fun d => d.cell == c) with
    | some _ =>
      rfl
    | none =>
      rfl

/-- **Admissibility Preservation Under Disjoint Execution**.
    After executing an independent turn T₁, turn T₂ remains fully valid. -/
theorem admits_after_disjoint (s : VaultStore) (T₁ T₂ : VaultTurn)
    (contracts : String → Option CellContract)
    (formats : List Obend.Judge.Format := [])
    (h_disj : DisjointTurns T₁ T₂)
    (h_valid : ValidAt s T₂ contracts formats) :
    ValidAt (applyTurn s T₁) T₂ contracts formats := by
  obtain ⟨h_pins, h_pre, h_contracts, h_wit⟩ := h_valid
  refine ⟨?_, ?_, h_contracts, h_wit⟩
  · intro p hp
    have hp_cell_not_mem := disjoint_read_write h_disj hp
    rw [applyTurn_frame_of_not_mem s T₁ p.cell hp_cell_not_mem]
    exact h_pins p hp
  · intro d hd
    have hd_cell_not_mem := disjoint_write_write' h_disj hd
    rw [applyTurn_frame_of_not_mem s T₁ d.cell hd_cell_not_mem]
    exact h_pre d hd

/-- **Both Orders Admitted Under Disjoint Execution**.
    Two turns satisfying Bernstein independence that are admitted at store `s`
    are each admitted after the other has been applied. -/
theorem disjoint_both_orders (s : VaultStore) (T₁ T₂ : VaultTurn)
    (contracts : String → Option CellContract)
    (formats : List Obend.Judge.Format := [])
    (h_disj : DisjointTurns T₁ T₂)
    (h₁ : ValidAt s T₁ contracts formats)
    (h₂ : ValidAt s T₂ contracts formats) :
    ValidAt (applyTurn s T₁) T₂ contracts formats ∧
    ValidAt (applyTurn s T₂) T₁ contracts formats := by
  have h_disj_symm : DisjointTurns T₂ T₁ := ⟨h_disj.2, h_disj.1⟩
  exact ⟨admits_after_disjoint s T₁ T₂ contracts formats h_disj h₂,
         admits_after_disjoint s T₂ T₁ contracts formats h_disj_symm h₁⟩

/-! ## 6. Integration with CellContract -/

/-- **Post-State Inductive Invariance Theorem**.
    Under an admitted VaultTurn, every mutated cell's post-state satisfies
    its active contract invariant. -/
theorem VaultTurn.post_invariants_hold (turn : VaultTurn) (s : VaultStore)
    (contracts : String → Option CellContract)
    (formats : List Obend.Judge.Format := [])
    (h_valid : ValidAt s turn contracts formats) :
    ∀ d ∈ turn.writeCells, ∀ C, contracts d.cell = some C →
      Holds C.invariant d.postState := by
  intro d hd C hC
  obtain ⟨_, _, h_contracts, _⟩ := h_valid
  have ⟨h_inv, h_adm⟩ := h_contracts d hd C hC
  exact C.inductive_preserves d.preState d.postState (turnRequest turn.turnId turn.occasion d.cell) h_inv h_adm

/-- **Post-State Step Soundness Theorem**.
    Under an admitted VaultTurn, every cell transition satisfies its contract step specification. -/
theorem VaultTurn.post_step_sound (turn : VaultTurn) (s : VaultStore)
    (contracts : String → Option CellContract)
    (formats : List Obend.Judge.Format := [])
    (h_valid : ValidAt s turn contracts formats) :
    ∀ d ∈ turn.writeCells, ∀ C, contracts d.cell = some C →
      Admits C.stepRel d.preState d.postState (turnRequest turn.turnId turn.occasion d.cell) := by
  intro d hd C hC
  obtain ⟨_, _, h_contracts, _⟩ := h_valid
  have ⟨h_inv, h_adm⟩ := h_contracts d hd C hC
  exact C.step_sound d.preState d.postState (turnRequest turn.turnId turn.occasion d.cell) h_inv h_adm

/-- **Store-Level Invariance**: Under `nodup_cells`, every mutated cell in the resulting
    store actually contains `d.postState` and satisfies the contract invariant. -/
theorem VaultTurn.store_post_invariants_hold (turn : VaultTurn) (s : VaultStore)
    (contracts : String → Option CellContract)
    (formats : List Obend.Judge.Format := [])
    (h_valid : ValidAt s turn contracts formats) :
    ∀ d ∈ turn.writeCells, ∀ C, contracts d.cell = some C →
      applyTurn s turn d.cell = some d.postState ∧ Holds C.invariant d.postState := by
  intro d hd C hC
  refine ⟨applyTurn_write s turn d hd, turn.post_invariants_hold s contracts formats h_valid d hd C hC⟩

/-- **Turn Relaw Preservation**.
    If a turn transition updates a cell's active contract law from `C.law` to `newLaw`
    with a certificate proving `Narrows newLaw C.law`, the updated contract inherits
    both inductive invariant preservation and step soundness. -/
def VaultTurn.relaw_sound (C : CellContract) (newLaw : Term) (h_nar : Narrows newLaw C.law) :
    CellContract :=
  cellContract_relaw_sound C newLaw h_nar

/-! ## 7. State-Derived Balanced Deltas & Total State Balance Conservation (`WS-F`) -/

/-- Canonical cell identifier alias on `CellDelta`. -/
def CellDelta.cellId (d : CellDelta) : String :=
  d.cell

/-- Extract an integer balance field `balanceField` from a cell state `Data`. -/
def extractFieldInt (balanceField : String) : Data → Int
  | .record fs =>
    match fs.find? (·.1 == balanceField) with
    | some (_, .natural n) => (n : Int)
    | some (_, .variant "neg" (.natural n)) => -(n : Int)
    | some (_, .variant "pos" (.natural n)) => (n : Int)
    | _ => 0
  | _ => 0

/-- Net sum of `d.halfEdges` entries for `balanceField` (falling back to entries keyed by `d.cellId`
    when no entry is explicitly keyed by `balanceField`). -/
def CellDelta.netHalfEdgeSum (d : CellDelta) (balanceField : String) : Int :=
  let byAsset := d.halfEdges.filter (fun (k, _) => k == balanceField)
  let matching := if byAsset.isEmpty then d.halfEdges.filter (fun (k, _) => k == d.cellId) else byAsset
  matching.foldl (fun acc (_, v) => acc + v) 0

/-- Verify that the net sum of `d.halfEdges` (and `deltaAsset d balanceField`) for `d.cellId`
    equals `extractFieldInt balanceField d.postState - extractFieldInt balanceField d.preState`. -/
def CellDelta.accountingConsistent (d : CellDelta) (balanceField : String) : Bool :=
  let stateDiff := extractFieldInt balanceField d.postState - extractFieldInt balanceField d.preState
  decide (deltaAsset d balanceField = stateDiff) &&
  decide (d.netHalfEdgeSum balanceField = stateDiff)

/-- Total pre-state balance across a list of `CellDelta`s for `balanceField`. -/
def sumPreStateBalance (cells : List CellDelta) (balanceField : String) : Int :=
  (cells.map (fun d => extractFieldInt balanceField d.preState)).foldl (· + ·) 0

/-- Total post-state balance across a list of `CellDelta`s for `balanceField`. -/
def sumPostStateBalance (cells : List CellDelta) (balanceField : String) : Int :=
  (cells.map (fun d => extractFieldInt balanceField d.postState)).foldl (· + ·) 0

theorem foldl_add_shift (xs : List Int) (init : Int) :
    xs.foldl (· + ·) init = init + xs.foldl (· + ·) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl]
    rw [ih (init + x), ih (0 + x)]
    omega

theorem sumAssetDelta_eq_post_sub_pre (cells : List CellDelta) (balanceField : String)
    (h_acc : ∀ d ∈ cells, d.accountingConsistent balanceField = true) :
    sumAssetDelta cells balanceField =
      sumPostStateBalance cells balanceField - sumPreStateBalance cells balanceField := by
  induction cells with
  | nil => rfl
  | cons d rest ih =>
    have hd : d.accountingConsistent balanceField = true := h_acc d (List.Mem.head rest)
    have hrest : ∀ x ∈ rest, x.accountingConsistent balanceField = true :=
      fun x hx => h_acc x (List.Mem.tail d hx)
    unfold CellDelta.accountingConsistent at hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    unfold sumAssetDelta sumPostStateBalance sumPreStateBalance at ih ⊢
    simp only [List.map, List.foldl]
    rw [foldl_add_shift (rest.map (fun x => deltaAsset x balanceField)) (0 + deltaAsset d balanceField)]
    rw [foldl_add_shift (rest.map (fun x => extractFieldInt balanceField x.postState))
        (0 + extractFieldInt balanceField d.postState)]
    rw [foldl_add_shift (rest.map (fun x => extractFieldInt balanceField x.preState))
        (0 + extractFieldInt balanceField d.preState)]
    have ih' := ih hrest
    omega

/-- **State-Derived Total Balance Conservation Theorem (`turn_conserves_total_state_balance`)**:
    For any `VaultTurn` whose deltas are `accountingConsistent` for `balanceField`
    (and whose hyperedge satisfies `turn.balanced`), the total post-state balance
    `sumPostStateBalance turn.writeCells balanceField` across all touched cells
    equals the total pre-state balance `sumPreStateBalance turn.writeCells balanceField`. -/
theorem turn_conserves_total_state_balance (turn : VaultTurn) (balanceField : String)
    (h_acc : ∀ d ∈ turn.writeCells, d.accountingConsistent balanceField = true) :
    sumPostStateBalance turn.writeCells balanceField =
      sumPreStateBalance turn.writeCells balanceField := by
  have h_diff := sumAssetDelta_eq_post_sub_pre turn.writeCells balanceField h_acc
  have h_bal := turn.balanced balanceField
  omega

/-! ## 8. State-to-HalfEdge Conservation Binding (`ASTRA-COUNCIL:363–370`) -/

/-- Extract the integer/natural balance of `asset` (or `"balance_" ++ asset`) from a
    `Data.record` cell state payload, defaulting to `0` if absent or non-numeric. -/
def extractCellAssetBalance (d : Data) (asset : String) : Int :=
  match d with
  | .record fs =>
    match fs.find? (·.1 == asset) with
    | some (_, .natural n) => (n : Int)
    | some (_, .variant "neg" (.natural n)) => -(n : Int)
    | some (_, .variant "pos" (.natural n)) => (n : Int)
    | _ =>
      match fs.find? (·.1 == "balance_" ++ asset) with
      | some (_, .natural n) => (n : Int)
      | some (_, .variant "neg" (.natural n)) => -(n : Int)
      | some (_, .variant "pos" (.natural n)) => (n : Int)
      | _ => 0
  | _ => 0

/-- Actual state-level balance change for `asset` across `d.preState → d.postState`. -/
def cellStateBalanceDelta (d : CellDelta) (asset : String) : Int :=
  extractCellAssetBalance d.postState asset - extractCellAssetBalance d.preState asset

/-- Derive canonical `HalfEdge` entries directly from the `preState`/`postState` balance diffs
    of `d` across `assets`. -/
def deriveHalfEdgesFromState (d : CellDelta) (assets : List String) : List HalfEdge :=
  assets.map (fun a => (a, cellStateBalanceDelta d a))

/-- Boolean checker verifying that for every `a ∈ assets`, the reported half-edge delta
    `cellAssetDelta d a` equals the actual state balance delta `cellStateBalanceDelta d a`. -/
def checkDeltaMatchesStateBalances (assets : List String) (d : CellDelta) : Bool :=
  assets.all (fun a => cellAssetDelta d a == cellStateBalanceDelta d a)

/-- Whole-turn boolean checker verifying that every modified cell in `turn.writeCells`
    binds its `halfEdges` faithfully to its `preState`/`postState` balance changes. -/
def checkTurnStateBalancesBound (assets : List String) (turn : VaultTurn) : Bool :=
  turn.writeCells.all (checkDeltaMatchesStateBalances assets)

theorem checkDeltaMatchesStateBalances_iff (assets : List String) (d : CellDelta) :
    checkDeltaMatchesStateBalances assets d = true ↔
      ∀ a ∈ assets, cellAssetDelta d a = cellStateBalanceDelta d a := by
  unfold checkDeltaMatchesStateBalances
  rw [List.all_eq_true]
  constructor
  · intro h a ha
    exact beq_iff_eq.1 (h a ha)
  · intro h a ha
    exact beq_iff_eq.2 (h a ha)

theorem checkTurnStateBalancesBound_iff (assets : List String) (turn : VaultTurn) :
    checkTurnStateBalancesBound assets turn = true ↔
      ∀ d ∈ turn.writeCells, ∀ a ∈ assets, cellAssetDelta d a = cellStateBalanceDelta d a := by
  unfold checkTurnStateBalancesBound
  rw [List.all_eq_true]
  constructor
  · intro h d hd a ha
    exact (checkDeltaMatchesStateBalances_iff assets d).1 (h d hd) a ha
  · intro h d hd
    exact (checkDeltaMatchesStateBalances_iff assets d).2 (h d hd)

theorem sumAssetDelta_eq_sumStateBalanceDelta (cells : List CellDelta) (a : String)
    (h_match : ∀ d ∈ cells, cellAssetDelta d a = cellStateBalanceDelta d a) :
    sumAssetDelta cells a =
      (cells.map (fun d => extractCellAssetBalance d.postState a - extractCellAssetBalance d.preState a)).foldl (· + ·) 0 := by
  unfold sumAssetDelta
  congr 1
  apply List.map_congr_left
  intro d hd
  exact h_match d hd

theorem sumStateBalanceDelta_eq_post_sub_pre (cells : List CellDelta) (a : String) :
    (cells.map (fun d => extractCellAssetBalance d.postState a - extractCellAssetBalance d.preState a)).foldl (· + ·) 0 =
      (cells.map (fun d => extractCellAssetBalance d.postState a)).foldl (· + ·) 0 -
        (cells.map (fun d => extractCellAssetBalance d.preState a)).foldl (· + ·) 0 := by
  induction cells with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map, List.foldl]
    rw [foldl_add_shift (rest.map (fun x => extractCellAssetBalance x.postState a - extractCellAssetBalance x.preState a))
        (0 + (extractCellAssetBalance d.postState a - extractCellAssetBalance d.preState a))]
    rw [foldl_add_shift (rest.map (fun x => extractCellAssetBalance x.postState a))
        (0 + extractCellAssetBalance d.postState a)]
    rw [foldl_add_shift (rest.map (fun x => extractCellAssetBalance x.preState a))
        (0 + extractCellAssetBalance d.preState a)]
    omega

/-- **Universal State-Level Asset Conservation Theorem (`stateBoundTurn_conserves_actual_state_balances`)**:
    For any `turn : VaultTurn`, `assets : List String`, and `a ∈ assets`, if `turn.balanced`
    (`sumAssetDelta turn.writeCells a = 0`) and `checkTurnStateBalancesBound assets turn = true`,
    then:
    1. The sum of actual state balance changes across all modified cells is identically zero:
       `∑_{d ∈ turn.writeCells} (extractCellAssetBalance d.postState a - extractCellAssetBalance d.preState a) = 0`, and
    2. Equivalently, the total post-state balance equals the total pre-state balance:
       `∑_{d ∈ turn.writeCells} extractCellAssetBalance d.postState a = ∑_{d ∈ turn.writeCells} extractCellAssetBalance d.preState a`. -/
theorem stateBoundTurn_conserves_actual_state_balances
    (turn : VaultTurn) (assets : List String) (a : String)
    (ha : a ∈ assets)
    (hbound : checkTurnStateBalancesBound assets turn = true) :
    (turn.writeCells.map (fun d => extractCellAssetBalance d.postState a - extractCellAssetBalance d.preState a)).foldl (· + ·) 0 = 0 ∧
    (turn.writeCells.map (fun d => extractCellAssetBalance d.postState a)).foldl (· + ·) 0 =
      (turn.writeCells.map (fun d => extractCellAssetBalance d.preState a)).foldl (· + ·) 0 := by
  have h_cell : ∀ d ∈ turn.writeCells, cellAssetDelta d a = cellStateBalanceDelta d a :=
    fun d hd => (checkTurnStateBalancesBound_iff assets turn).1 hbound d hd a ha
  have h_eq := sumAssetDelta_eq_sumStateBalanceDelta turn.writeCells a h_cell
  have h_bal := turn.balanced a
  have h_zero : (turn.writeCells.map (fun d => extractCellAssetBalance d.postState a - extractCellAssetBalance d.preState a)).foldl (· + ·) 0 = 0 := by
    omega
  have h_sub := sumStateBalanceDelta_eq_post_sub_pre turn.writeCells a
  refine ⟨h_zero, ?_⟩
  omega

/-- Concrete `CellDelta` attempting to mint +900 `"USDC"` in `postState` (from `100` to `1000`)
    while hiding the inflation behind `halfEdges := []`. -/
def unreportedInflationDelta : CellDelta where
  cell := "vault_alice"
  preState := .record [("USDC", .natural 100)]
  postState := .record [("USDC", .natural 1000)]
  halfEdges := []

/-- **Unreported State Inflation Refusal (`unreported_state_inflation_refused`)**:
    A `CellDelta` that increases `"USDC"` in `postState` from `100` to `1000` while supplying
    `halfEdges := []` trivially passes naive `halfEdges` summation (`sumAssetDelta = 0`),
    but has actual state delta `+900` and is deterministically rejected (`= false`) by
    `checkDeltaMatchesStateBalances`. -/
theorem unreported_state_inflation_refused :
    sumAssetDelta [unreportedInflationDelta] "USDC" = 0 ∧
    cellStateBalanceDelta unreportedInflationDelta "USDC" = 900 ∧
    checkDeltaMatchesStateBalances ["USDC"] unreportedInflationDelta = false := by
  decide

#tooth unreported_state_inflation_refused by mutation
  checkDeltaMatchesStateBalances := fun _ _ => true

#tooth stateBoundTurn_conserves_actual_state_balances by mutation
  checkTurnStateBalancesBound := fun _ _ => true

/-- **Derived Half-Edges Match State Balances (`deriveHalfEdgesFromState_sound`)**:
    When `d.halfEdges` is populated via `deriveHalfEdgesFromState d assets` for a duplicate-free
    asset list `assets`, `checkDeltaMatchesStateBalances assets` is guaranteed to return `true`. -/
theorem find?_map_deriveHalfEdges {assets : List String} (h_nodup : assets.Nodup)
    (d : CellDelta) {a : String} (ha : a ∈ assets) :
    (deriveHalfEdgesFromState d assets).find? (·.1 == a) = some (a, cellStateBalanceDelta d a) := by
  induction assets with
  | nil => cases ha
  | cons x rest ih =>
    have ⟨hx_not_mem, hrest_nodup⟩ := List.nodup_cons.1 h_nodup
    simp only [deriveHalfEdgesFromState, List.map_cons, List.find?_cons]
    cases ha with
    | head =>
      simp
    | tail _ hmem =>
      have hne : (x == a) = false := by
        cases hxa : x == a with
        | false => rfl
        | true =>
          have heq : x = a := beq_iff_eq.1 hxa
          subst heq
          exact False.elim (hx_not_mem hmem)
      simp only [hne]
      exact ih hrest_nodup hmem

theorem deriveHalfEdgesFromState_matches (d : CellDelta) (assets : List String)
    (h_nodup : assets.Nodup) :
    checkDeltaMatchesStateBalances assets { d with halfEdges := deriveHalfEdgesFromState d assets } = true := by
  rw [checkDeltaMatchesStateBalances_iff]
  intro a ha
  unfold cellAssetDelta deltaAsset
  simp only [find?_map_deriveHalfEdges h_nodup d ha]
  rfl

#tooth deriveHalfEdgesFromState_matches by mutation
  deriveHalfEdgesFromState := fun _ _ => []

end Obend.Vault

