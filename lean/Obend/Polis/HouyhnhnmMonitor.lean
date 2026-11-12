module
/-
# Obend.Polis.HouyhnhnmMonitor — Reflective Artifact Probe Tower & Virtualizable Machine Monitor

Combines two coupled Houyhnhnm supervision layers in one scar-free module:
1. **Recursive Physical Artifact Probe Tower (`MonitoredSubsystem`, `wrapMonitor`, `monitorTower`)**:
   - Every monitor records its verdict beside the inner artifact so an outer layer re-probes
     both the inner physical state and the monitor's honesty (`wrapMonitor_detects_forged_verdict`,
     `wrapMonitor_tower_sound`, `tower_catches_false_none`).
2. **Virtualizable Pin-Interposing `Core.Machine` Bridge (`VirtualizedPolicy`, `SpeculativeBranch`,
   `stepVirtualizedMachine`, `runVirtualizedTrace`)**:
   - Intercepts yielded `Core.Machine` plans (`Control.yielded planAddr`), routing authorized pins
     to real responses while routing unauthorized or uncohered pins to **honeypot**, **speculative
     fork**, or **frozen-to-monitor** actions — never leaking a catchable ambient `EPERM` bit into
     `Core.Term` (`virtualized_full_abstraction_no_eperm_leak`), isolating unmerged speculative
     branches from parent state (`quarantined_branch_preserves_parent`), and recording deterministic
     `MonitorBlame` provenance across multi-turn traces (`ValidMonitorTrace`).
-/
public import Obend.Core.Digest
public import Obend.Core.Term

public section
namespace Obend.Polis.HouyhnhnmMonitor

open Obend.Core.Term

set_option autoImplicit false

/-! ## 1. Physical Artifact Probe & Recursive Monitor Tower -/

abbrev Digest := ByteArray
inductive HealthClaim where
  | healthy (stateRoot : Digest)
  | recovered (epoch : Nat) (stateRoot : Digest)
  | degraded
  deriving DecidableEq
inductive DivergenceKind where
  | divergentArtifact (claimed observed : HealthClaim)
  | recoveryNotHolding
  | silentHeartbeat
  deriving DecidableEq

structure MonitoredSubsystem (State Artifact : Type) where
  selfClaim : State → HealthClaim
  extractArtifact : State → Artifact
  probeArtifact : Artifact → HealthClaim

@[expose] def compareClaims (claimed observed : HealthClaim) : Option DivergenceKind :=
  if claimed = observed then none else some (.divergentArtifact claimed observed)

def auditSubsystem {S A : Type} (m : MonitoredSubsystem S A) (s : S) : HealthClaim :=
  m.probeArtifact (m.extractArtifact s)

@[expose] def detectDivergence {S A : Type} (m : MonitoredSubsystem S A) (s : S) :
    Option DivergenceKind := compareClaims (m.selfClaim s) (auditSubsystem m s)

theorem monitor_catches_false_claim {S A : Type} (m : MonitoredSubsystem S A) (s : S)
    (h : m.probeArtifact (m.extractArtifact s) ≠ m.selfClaim s) :
    detectDivergence m s = some (.divergentArtifact (m.selfClaim s)
      (m.probeArtifact (m.extractArtifact s))) := by
  simp [detectDivergence, compareClaims, auditSubsystem, Ne.symm h]

theorem monitor_catches_false_recovery {S A : Type} (m : MonitoredSubsystem S A)
    (s : S) (epoch : Nat) (root : Digest) (hc : m.selfClaim s = .recovered epoch root)
    (hp : m.probeArtifact (m.extractArtifact s) ≠ .recovered epoch root) :
    detectDivergence m s = some (.divergentArtifact (.recovered epoch root)
      (m.probeArtifact (m.extractArtifact s))) := by
  simpa [hc] using monitor_catches_false_claim m s (by simpa [hc] using hp)

/-- An untrusted monitor stores its last verdict beside the inner state. -/
structure MonitorSubsystem (S : Type) where
  inner : S
  recorded : Option DivergenceKind

structure MonitorArtifact (A : Type) where
  inner : A
  innerClaim : HealthClaim
  recorded : Option DivergenceKind

/-- Healthy means the recorded verdict agrees with a fresh physical probe. Even a
monitor claiming to have found a fault must substantiate that verdict. -/
@[expose] def probeMonitor {S A : Type} (m : MonitoredSubsystem S A)
    (a : MonitorArtifact A) : HealthClaim :=
  if a.recorded = compareClaims a.innerClaim (m.probeArtifact a.inner)
  then .healthy ByteArray.empty else .degraded

@[expose] def wrapMonitor {S A : Type} (m : MonitoredSubsystem S A) :
    MonitoredSubsystem (MonitorSubsystem S) (MonitorArtifact A) where
  selfClaim := fun _ => .healthy ByteArray.empty
  extractArtifact := fun s => ⟨m.extractArtifact s.inner, m.selfClaim s.inner, s.recorded⟩
  probeArtifact := probeMonitor m

theorem wrapMonitor_detects_forged_verdict {S A : Type} (m : MonitoredSubsystem S A)
    (s : MonitorSubsystem S) (h : s.recorded ≠ detectDivergence m s.inner) :
    detectDivergence (wrapMonitor m) s =
      some (.divergentArtifact (.healthy ByteArray.empty) .degraded) := by
  simp [detectDivergence, auditSubsystem] at h ⊢
  simp only [wrapMonitor, probeMonitor, h, ite_false]
  rfl

/-- Each level retains the actual inner artifact, rather than only its report. -/
@[expose] def TowerState (S : Type) : Nat → Type
  | 0 => S
  | n + 1 => MonitorSubsystem (TowerState S n)
@[expose] def TowerArtifact (A : Type) : Nat → Type
  | 0 => A
  | n + 1 => MonitorArtifact (TowerArtifact A n)
def monitorTower {S A : Type} (m : MonitoredSubsystem S A) :
    (n : Nat) → MonitoredSubsystem (TowerState S n) (TowerArtifact A n)
  | 0 => m
  | n + 1 => wrapMonitor (monitorTower m n)

/-- Universal adjacent-layer law: instantiate k at any depth below n. -/
theorem wrapMonitor_tower_sound {S A : Type} (m : MonitoredSubsystem S A)
    (k : Nat) (s : TowerState S (k + 1))
    (h : s.recorded ≠ detectDivergence (monitorTower m k) s.inner) :
    detectDivergence (monitorTower m (k + 1)) s =
      some (.divergentArtifact (.healthy ByteArray.empty) .degraded) :=
  wrapMonitor_detects_forged_verdict _ _ h

theorem tower_catches_false_none {S A : Type} (m : MonitoredSubsystem S A)
    (k : Nat) (s : TowerState S k)
    (h : auditSubsystem (monitorTower m k) s ≠ (monitorTower m k).selfClaim s) :
    detectDivergence (monitorTower m (k + 1)) ⟨s, none⟩ =
      some (.divergentArtifact (.healthy ByteArray.empty) .degraded) := by
  apply wrapMonitor_detects_forged_verdict
  rw [monitor_catches_false_claim _ _ h]
  intro h; cases h

/-! ## 2. Regime-Polymorphic Virtualizable Pin-Interposing Guest Monitor & Speculative Isolation -/

/-- Structured blame record emitted exclusively to the outer monitor/sponsor (never injected as an
    ambient `EPERM` exception inside the guest `Core.Term`). -/
inductive MonitorBlame where
  | budgetTicksExhausted (usedTicks : Nat)
  | heapOrStackCapacityExceeded (heapSize stackDepth : Nat)
  | machineRefused (reasonTag : String)
  | machineBlackhole (addr : Nat)
  | unauthorizedPinFreeze (capTag : Nat) (reifiedPlan : Term)
  | incoherentHoleTrap (holeId : Nat)
  | reificationFailed (errTag : String)
  deriving Repr

/-- Regime-neutral bounded execution outcome for any guest carrier `G`
    (instantiated over `Core.Term` below and over `Core.Machine.State` + `MachineReify` in
    `Obend.Metatheory.SponsorAndMigration`). -/
inductive GuestOutcome (G : Type) where
  | finished (value : Term) (state : G)
  | suspendedTicks (usedTicks : Nat) (state : G)
  | suspendedCapacity (heapSize stackDepth : Nat) (state : G)
  | divergent (addr : Nat) (state : G)
  | refusedHole (holeId : Nat) (state : G)
  | refusedOther (reasonTag : String) (state : G)
  | yielded (planTerm : Term) (state : G)
  | reificationError (errTag : String) (state : G)
  deriving Repr

/--Bounded execution & checkpoint-resumption interface for a virtualizable guest carrier `G`. -/
structure GuestRunner (G : Type) where
  runSlice : Nat → G → GuestOutcome G
  resumeGuest : Term → G → Option G

/-- Canonical direct `Core.Term` guest runner (values finish, `.perform plan` yields, `.hole id _`
    traps cleanly to supervisor). -/
@[expose] def termDirectRunner : GuestRunner Term where
  runSlice ticks tm :=
    if ticks = 0 then .suspendedTicks 0 tm
    else match tm with
      | .perform plan => .yielded plan tm
      | .hole holeId _ => .refusedHole holeId tm
      | .nat _ | .boolean _ | .label _ | .lam _ | .record _ | .inject _ _
      | .specification _ _ | .prototype _ _ => .finished tm tm
      | _ => .suspendedTicks 1 tm
  resumeGuest resp tm :=
    match tm with
    | .perform _ => some resp
    | _ => none

/-- How a parent Houyhnhnm monitor interposes on a yielded guest `perform plan`:
    - `deliverReal capId response`: guest holds `capId` and receives real closed `response`
      (routed to `honeypotEffects` if `cell.inHoneypot = true` so synthetic history never taints
      `committedEffects`),
    - `deliverHoneypot syntheticResponse`: guest lacks real authority; switches `inHoneypot := true`
      permanently and resumes with an indistinguishable well-typed synthetic `Term` (zero `EPERM` leak!),
    - `forkSpeculative branchId syntheticResponse`: clones guest state into a speculative branch
      while keeping parent commitment state untouched until single-use audited merge,
    - `freezeToSupervisor capTag`: suspends the guest cleanly into `frozenPlan?` for higher
      tower intervention (zero guest-visible error code). -/
inductive PinInterposition where
  | deliverReal (capId : Nat) (response : Term)
  | deliverHoneypot (syntheticResponse : Term)
  | forkSpeculative (branchId : Nat) (syntheticResponse : Term)
  | freezeToSupervisor (capTag : Nat)
  deriving Repr

/-- Speculative / honeypot child branch isolated from the committed parent `WorldRoot`. -/
structure SpeculativeBranch (G : Type) where
  branchId       : Nat
  guestState     : G
  emittedEffects : List (Nat × Term)
  quarantined    : Bool
  blame?         : Option MonitorBlame
  deriving Repr

/-- Live virtualized monitor state wrapping a guest carrier `G`, its held capability IDs,
    irreversible `inHoneypot` taint bit, committed world effects, isolated honeypot effects,
    speculative branches, and recorded `MonitorBlame` log. -/
structure VirtualizedCell (G : Type) where
  cellId           : Nat
  heldCaps         : List Nat
  tickSlice        : Nat
  guest            : G
  inHoneypot       : Bool := false
  committedEffects : List (Nat × Term)
  honeypotEffects  : List (Nat × Term) := []
  branches         : List (SpeculativeBranch G)
  frozenPlan?      : Option Term
  blameLog         : List MonitorBlame
  deriving Repr

/-- Execute one bounded metered slice of `cell.guest` under `runner : GuestRunner G` and
    `policy : Term → PinInterposition`:
    - Enforces `heldCaps` confinement on `.deliverReal` (`capId ∈ cell.heldCaps`), downgrading any
      unheld real-delivery attempt to `.unauthorizedPinFreeze capId` with deterministic blame!
    - Permanently sets `inHoneypot := true` on `.deliverHoneypot`, ensuring no subsequent turn can
      ever append effects computed from synthetic responses to `committedEffects`! -/
@[expose] def stepVirtualizedCell {G : Type} (runner : GuestRunner G)
    (policy : Term → PinInterposition) (cell : VirtualizedCell G) : VirtualizedCell G :=
  match runner.runSlice cell.tickSlice cell.guest with
  | .finished _ finalSt =>
      { cell with guest := finalSt }
  | .suspendedTicks used pausedSt =>
      { cell with
        guest := pausedSt
        blameLog := .budgetTicksExhausted used :: cell.blameLog }
  | .suspendedCapacity hSz sSz pausedSt =>
      { cell with
        guest := pausedSt
        blameLog := .heapOrStackCapacityExceeded hSz sSz :: cell.blameLog }
  | .divergent addr divSt =>
      { cell with
        guest := divSt
        blameLog := .machineBlackhole addr :: cell.blameLog }
  | .refusedHole holeId refSt =>
      { cell with
        guest := refSt
        blameLog := .incoherentHoleTrap holeId :: cell.blameLog }
  | .refusedOther tag refSt =>
      { cell with
        guest := refSt
        blameLog := .machineRefused tag :: cell.blameLog }
  | .reificationError errTag yieldedSt =>
      { cell with
        guest := yieldedSt
        blameLog := .reificationFailed errTag :: cell.blameLog }
  | .yielded planTerm yieldedSt =>
      match policy planTerm with
      | .deliverReal capId response =>
          if cell.heldCaps.contains capId then
            match runner.resumeGuest response yieldedSt with
            | some nextSt =>
                if cell.inHoneypot then
                  { cell with
                    guest := nextSt
                    honeypotEffects := (capId, planTerm) :: cell.honeypotEffects }
                else
                  { cell with
                    guest := nextSt
                    committedEffects := (capId, planTerm) :: cell.committedEffects }
            | none => cell
          else
            { cell with
              guest := yieldedSt
              frozenPlan? := some planTerm
              blameLog := .unauthorizedPinFreeze capId planTerm :: cell.blameLog }
      | .deliverHoneypot syntheticResponse =>
          match runner.resumeGuest syntheticResponse yieldedSt with
          | some nextSt => { cell with guest := nextSt, inHoneypot := true }
          | none => { cell with inHoneypot := true }
      | .forkSpeculative branchId syntheticResponse =>
          let forkedGuest := (runner.resumeGuest syntheticResponse yieldedSt).getD yieldedSt
          let br : SpeculativeBranch G :=
            { branchId := branchId
              guestState := forkedGuest
              emittedEffects := []
              quarantined := false
              blame? := none }
          { cell with
            guest := yieldedSt
            branches := br :: cell.branches.filter (fun b => b.branchId != branchId) }
      | .freezeToSupervisor capTag =>
          { cell with
            guest := yieldedSt
            frozenPlan? := some planTerm
            blameLog := .unauthorizedPinFreeze capTag planTerm :: cell.blameLog }

/-- Audit and commit or quarantine a speculative branch present in `cell.branches` by `branchId`:
    - Unknown branch IDs are ignored (`cell` unchanged).
    - Accepted branches in non-honeypot cells commit their effects once and are **consumed**
      (removed from `cell.branches`, preventing double-commit replay).
    - Rejected, quarantined, honeypot-tainted, or capability-escalating branches are marked
      `quarantined := true` and NEVER touch `committedEffects` or `guest`! -/
@[expose] def commitOrQuarantineBranch {G : Type} (auditOk : SpeculativeBranch G → Bool)
    (cell : VirtualizedCell G) (branchId : Nat) : VirtualizedCell G :=
  match cell.branches.find? (fun b => b.branchId == branchId) with
  | none => cell
  | some br =>
      let restBranches := cell.branches.filter (fun b => b.branchId != branchId)
      if !cell.inHoneypot && auditOk br && !br.quarantined &&
          br.emittedEffects.all (fun e => cell.heldCaps.contains e.1) then
        { cell with
          guest := br.guestState
          committedEffects := br.emittedEffects ++ cell.committedEffects
          branches := restBranches }
      else
        { cell with branches := { br with quarantined := true } :: restBranches }

/-- Unified transition action on a `VirtualizedCell G` (either stepping the guest or resolving a
    speculative branch). -/
inductive MonitorAction (G : Type) where
  | stepGuest (policy : Term → PinInterposition)
  | resolveBranch (auditOk : SpeculativeBranch G → Bool) (branchId : Nat)

@[expose] def applyMonitorAction {G : Type} (runner : GuestRunner G)
    (act : MonitorAction G) (cell : VirtualizedCell G) : VirtualizedCell G :=
  match act with
  | .stepGuest pol => stepVirtualizedCell runner pol cell
  | .resolveBranch auditOk bid => commitOrQuarantineBranch auditOk cell bid

/-- Multi-turn inductive trace of virtualized monitor transitions (covering both guest slices and
    branch commit/quarantine resolutions). -/
inductive ValidMonitorTrace {G : Type} (runner : GuestRunner G) :
    VirtualizedCell G → List (MonitorAction G) → VirtualizedCell G → Prop where
  | nil (c : VirtualizedCell G) : ValidMonitorTrace runner c [] c
  | cons {c : VirtualizedCell G} (act : MonitorAction G)
      {rest : List (MonitorAction G)} {cFinal : VirtualizedCell G} :
      ValidMonitorTrace runner (applyMonitorAction runner act c) rest cFinal →
      ValidMonitorTrace runner c (act :: rest) cFinal

/-! ## 3. Confinement, Persistent Honeypot Isolation & Multi-Turn Monitor Safety Theorems -/

/-- **Single-Step Capability Confinement**: every effect appended to `committedEffects` by
    `stepVirtualizedCell` carries a capability ID present in `cell.heldCaps`, and `heldCaps`
    never grows. -/
theorem stepVirtualizedCell_cap_confined {G : Type} (runner : GuestRunner G)
    (pol : Term → PinInterposition) (cell : VirtualizedCell G) :
    (stepVirtualizedCell runner pol cell).heldCaps = cell.heldCaps ∧
    (cell.inHoneypot = true →
      (stepVirtualizedCell runner pol cell).inHoneypot = true ∧
      (stepVirtualizedCell runner pol cell).committedEffects = cell.committedEffects) ∧
    (∀ eff ∈ (stepVirtualizedCell runner pol cell).committedEffects,
      eff ∈ cell.committedEffects ∨ eff.1 ∈ cell.heldCaps) := by
  have hUnchanged : ∀ eff ∈ cell.committedEffects,
      eff ∈ cell.committedEffects ∨ eff.1 ∈ cell.heldCaps := fun _ h => .inl h
  unfold stepVirtualizedCell
  cases hrun : runner.runSlice cell.tickSlice cell.guest with
  | finished _ _ | suspendedTicks _ _ | suspendedCapacity _ _ _
  | divergent _ _ | refusedHole _ _ | refusedOther _ _ | reificationError _ _ =>
    exact ⟨rfl, fun h => ⟨h, rfl⟩, hUnchanged⟩
  | yielded planTerm yieldedSt =>
    simp only
    cases hp : pol planTerm with
    | deliverReal capId response =>
      simp only
      cases hcap : cell.heldCaps.contains capId with
      | false => exact ⟨rfl, fun h => ⟨h, rfl⟩, hUnchanged⟩
      | true =>
        cases hres : runner.resumeGuest response yieldedSt with
        | none => exact ⟨rfl, fun h => ⟨h, rfl⟩, hUnchanged⟩
        | some nextSt =>
          cases hhp : cell.inHoneypot with
          | true =>
            dsimp only
            exact ⟨rfl, fun _ => ⟨rfl, rfl⟩, hUnchanged⟩
          | false =>
            dsimp only
            refine ⟨rfl, ?_, ?_⟩
            · intro h; cases h
            · intro eff heff
              rcases List.mem_cons.1 heff with rfl | hold
              · exact .inr (List.contains_iff_mem.1 hcap)
              · exact .inl hold
    | deliverHoneypot syn =>
      simp only
      cases runner.resumeGuest syn yieldedSt <;> exact ⟨rfl, fun _ => ⟨rfl, rfl⟩, hUnchanged⟩
    | forkSpeculative bid syn => exact ⟨rfl, fun h => ⟨h, rfl⟩, hUnchanged⟩
    | freezeToSupervisor tag => exact ⟨rfl, fun h => ⟨h, rfl⟩, hUnchanged⟩

theorem commitOrQuarantineBranch_cap_confined {G : Type}
    (auditOk : SpeculativeBranch G → Bool) (cell : VirtualizedCell G) (bid : Nat) :
    (commitOrQuarantineBranch auditOk cell bid).heldCaps = cell.heldCaps ∧
    (cell.inHoneypot = true →
      (commitOrQuarantineBranch auditOk cell bid).inHoneypot = true ∧
      (commitOrQuarantineBranch auditOk cell bid).committedEffects = cell.committedEffects) ∧
    (∀ eff ∈ (commitOrQuarantineBranch auditOk cell bid).committedEffects,
      eff ∈ cell.committedEffects ∨ eff.1 ∈ cell.heldCaps) := by
  have hUnchanged : ∀ eff ∈ cell.committedEffects,
      eff ∈ cell.committedEffects ∨ eff.1 ∈ cell.heldCaps := fun _ h => .inl h
  unfold commitOrQuarantineBranch
  cases hf : cell.branches.find? (fun b => b.branchId == bid) with
  | none => exact ⟨rfl, fun h => ⟨h, rfl⟩, hUnchanged⟩
  | some br =>
    dsimp only
    cases hCond : (!cell.inHoneypot && auditOk br && !br.quarantined &&
        br.emittedEffects.all (fun e => cell.heldCaps.contains e.1)) with
    | false =>
      exact ⟨rfl, fun h => ⟨h, rfl⟩, hUnchanged⟩
    | true =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
        List.contains_iff_mem] at hCond
      obtain ⟨⟨⟨hNoHp, _⟩, _⟩, hAllHeld⟩ := hCond
      refine ⟨rfl, ?_, ?_⟩
      · intro hHp; rw [hNoHp] at hHp; cases hHp
      · intro eff heff
        rcases List.mem_append.1 heff with hNew | hOld
        · exact .inr (hAllHeld eff hNew)
        · exact .inl hOld

/-- **Multi-Turn Capability Confinement & Irreversible Honeypot Isolation (`monitorTrace_cap_confined`)**:
    Across any multi-turn `ValidMonitorTrace` (interleaving guest slices and branch commits):
    1. `heldCaps` never grows and every committed effect lies in `c₀.heldCaps`.
    2. Once `c₀.inHoneypot = true` (after any `.deliverHoneypot`), `committedEffects` is frozen
       permanently (`cFinal.committedEffects = c₀.committedEffects`) — synthetic honeypot state
       can NEVER taint real committed world effects in future turns! -/
theorem monitorTrace_cap_confined {G : Type} {runner : GuestRunner G}
    {c₀ cFinal : VirtualizedCell G} {acts : List (MonitorAction G)}
    (hTrace : ValidMonitorTrace runner c₀ acts cFinal)
    (hInit : ∀ eff ∈ c₀.committedEffects, eff.1 ∈ c₀.heldCaps) :
    cFinal.heldCaps = c₀.heldCaps ∧
    (c₀.inHoneypot = true → cFinal.inHoneypot = true ∧ cFinal.committedEffects = c₀.committedEffects) ∧
    (∀ eff ∈ cFinal.committedEffects, eff.1 ∈ c₀.heldCaps) := by
  induction hTrace with
  | nil c => exact ⟨rfl, fun h => ⟨h, rfl⟩, hInit⟩
  | @cons c act rest cEnd _ ih =>
    have hAct : (applyMonitorAction runner act c).heldCaps = c.heldCaps ∧
        (c.inHoneypot = true →
          (applyMonitorAction runner act c).inHoneypot = true ∧
          (applyMonitorAction runner act c).committedEffects = c.committedEffects) ∧
        (∀ eff ∈ (applyMonitorAction runner act c).committedEffects,
          eff ∈ c.committedEffects ∨ eff.1 ∈ c.heldCaps) := by
      cases act with
      | stepGuest pol => exact stepVirtualizedCell_cap_confined runner pol c
      | resolveBranch aud bid => exact commitOrQuarantineBranch_cap_confined aud c bid
    obtain ⟨hcaps, hhpStep, hstep⟩ := hAct
    have hNext : ∀ eff ∈ (applyMonitorAction runner act c).committedEffects,
        eff.1 ∈ (applyMonitorAction runner act c).heldCaps := by
      intro eff heff; rw [hcaps]
      rcases hstep eff heff with hold | hnew
      · exact hInit eff hold
      · exact hnew
    obtain ⟨hFinalCaps, hFinalHp, hFinalEff⟩ := ih hNext
    refine ⟨hFinalCaps.trans hcaps, fun hHp₀ => ?_, fun eff heff => hcaps ▸ hFinalEff eff heff⟩
    obtain ⟨hHpMid, hEffMid⟩ := hhpStep hHp₀
    obtain ⟨hHpEnd, hEffEnd⟩ := hFinalHp hHpMid
    exact ⟨hHpEnd, hEffEnd.trans hEffMid⟩

/-- **Guest-Carrier Honeypot Indistinguishability + Permanent Isolation
    (`virtualized_honeypot_indistinguishable_to_guest`)**:
    1. Inside `G`, `.deliverReal capId resp` (`capId ∈ heldCaps`) and `.deliverHoneypot resp`
       produce the **exact same resumed guest state** (zero ambient `EPERM` or sandbox bit in `G`).
    2. In the outer `VirtualizedCell`, `.deliverHoneypot` leaves `committedEffects` untouched AND
       sets `inHoneypot = true`, permanently isolating all future turns from `committedEffects`! -/
theorem virtualized_honeypot_indistinguishable_to_guest {G : Type} (runner : GuestRunner G)
    (cell : VirtualizedCell G) (capId : Nat) (resp : Term) (yieldedSt : G) (planTerm : Term)
    (hCap : cell.heldCaps.contains capId = true)
    (hRun : runner.runSlice cell.tickSlice cell.guest = GuestOutcome.yielded planTerm yieldedSt) :
    (stepVirtualizedCell runner (fun _ => .deliverReal capId resp) cell).guest =
      (stepVirtualizedCell runner (fun _ => .deliverHoneypot resp) cell).guest ∧
    (stepVirtualizedCell runner (fun _ => .deliverHoneypot resp) cell).committedEffects =
      cell.committedEffects ∧
    (stepVirtualizedCell runner (fun _ => .deliverHoneypot resp) cell).inHoneypot = true := by
  simp only [stepVirtualizedCell, hRun, hCap, ite_true]
  cases runner.resumeGuest resp yieldedSt <;> cases cell.inHoneypot <;> simp

/-- **Quarantined / Unheld Speculative Branch Isolation & Single-Use Consumption
    (`quarantined_branch_preserves_parent`)**:
    1. Any rejected, quarantined, honeypot-tainted, or capability-unheld branch leaves `cell.guest`
       and `cell.committedEffects` untouched.
    2. Once a branch `bid` is committed, `bid` is removed from `branches`, so replaying `bid` a
       second time leaves `committedEffects` unchanged (zero double-commit)! -/
theorem quarantined_branch_preserves_parent {G : Type}
    (auditOk : SpeculativeBranch G → Bool) (cell : VirtualizedCell G) (bid : Nat) :
    ((∀ br, cell.branches.find? (fun b => b.branchId == bid) = some br →
        cell.inHoneypot = true ∨ auditOk br = false ∨ br.quarantined = true ∨
        br.emittedEffects.all (fun e => cell.heldCaps.contains e.1) = false) →
      (commitOrQuarantineBranch auditOk cell bid).guest = cell.guest ∧
      (commitOrQuarantineBranch auditOk cell bid).committedEffects = cell.committedEffects) ∧
    (∀ br, cell.branches.find? (fun b => b.branchId == bid) = some br →
      !cell.inHoneypot && auditOk br && !br.quarantined &&
        br.emittedEffects.all (fun e => cell.heldCaps.contains e.1) →
      (commitOrQuarantineBranch auditOk (commitOrQuarantineBranch auditOk cell bid) bid).committedEffects =
        (commitOrQuarantineBranch auditOk cell bid).committedEffects) := by
  refine ⟨fun hRej => ?_, fun br hFind hAcc => ?_⟩
  · unfold commitOrQuarantineBranch
    cases hf : cell.branches.find? (fun b => b.branchId == bid) with
    | none => exact ⟨rfl, rfl⟩
    | some br =>
      dsimp only
      have hFalse : (!cell.inHoneypot && auditOk br && !br.quarantined &&
          br.emittedEffects.all (fun e => cell.heldCaps.contains e.1)) = false := by
        rcases hRej br hf with h1 | h2 | h3 | h4
        · simp [h1]
        · simp [h2]
        · simp [h3]
        · rw [h4]; simp
      rw [hFalse]; exact ⟨rfl, rfl⟩
  · have hOnce : commitOrQuarantineBranch auditOk cell bid =
        { cell with
          guest := br.guestState
          committedEffects := br.emittedEffects ++ cell.committedEffects
          branches := cell.branches.filter (fun b => b.branchId != bid) } := by
      unfold commitOrQuarantineBranch; rw [hFind]; dsimp only; rw [hAcc]; rfl
    rw [hOnce]
    have hGone : (cell.branches.filter (fun b => b.branchId != bid)).find? (fun b => b.branchId == bid) = none := by
      rw [List.find?_eq_none]
      intro b hb; rw [List.mem_filter] at hb
      have hne : b.branchId ≠ bid := bne_iff_ne.1 hb.2
      exact beq_false_of_ne hne ▸ Bool.false_ne_true
    unfold commitOrQuarantineBranch; simp [hGone]

/-- Bridge a `VirtualizedCell G` into `MonitoredSubsystem` so the outer `monitorTower` audits whether
    the cell's `committedEffects` all lie inside `heldCaps` and `blameLog` is un-forged. -/
def virtualizedCellMonitor {G : Type} :
    MonitoredSubsystem (VirtualizedCell G) (List Nat × List (Nat × Term)) where
  selfClaim c :=
    if c.blameLog.isEmpty then .healthy ByteArray.empty else .degraded
  extractArtifact c := (c.heldCaps, c.committedEffects)
  probeArtifact art :=
    if art.2.all (fun eff => art.1.contains eff.1) then .healthy ByteArray.empty else .degraded

end Obend.Polis.HouyhnhnmMonitor
end
