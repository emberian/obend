module
public import Obend.Core.Digest

public section
namespace Obend.Polis.HouyhnhnmMonitor

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

end Obend.Polis.HouyhnhnmMonitor
