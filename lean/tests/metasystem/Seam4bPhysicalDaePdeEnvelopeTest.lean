import Obend.Hardware.SafePhysicalShield
import Obend.Hardware.CircuitDae
import Obend.Hardware.CurrentLoop
import Obend.Hardware.SwitchedCapRf
import Obend.Apps.SdrFt8Rx
import Obend.Analysis.HyperbolicPdeCert
import Obend.Hardware.Device.DriftDiffusion
import Obend.ClusterGov.PhysicalEnvelope
import Obend.Tactic.Tooth
import Obend.AssertAxioms

namespace Obend.Tests.Seam4bPhysicalDaePdeEnvelope
open Obend Obend.Analysis Obend.Hardware.CircuitDae Obend.Hardware.CurrentLoop
open Obend.Hardware.SafePhysicalShield Obend.Hardware.Device Obend.Analysis.HyperbolicPde
set_option autoImplicit false
set_option maxRecDepth 100000
set_option Elab.async false

-- Repeating a valid step illegally resets the physical state between samples.
def teleport : MnaDaeProblem := { rcDiodeRectifierMnaProblem with
  trace := [rcDiodeRectifierBeStep, rcDiodeRectifierBeStep] }
theorem teleport_refused : checkMnaDaeProblem 2 teleport rcDiodeRectifierMnaCert =
    .refused .badTraceDimsOrContinuity [] := by decide +kernel
example : ∀ cert, ¬ MnaDaeMeaning teleport cert :=
  checkMnaDaeProblem_refuted teleport_refused (by decide +kernel)
theorem jagged_refused :
    checkMnaDaeProblem 1 { rcDiodeRectifierMnaProblem with spec :=
      { rcDiodeRectifierMnaSpec with matC := [[1], [0, 2]] } } rcDiodeRectifierMnaCert =
        .refused .badMatrixDims [] ∧
    checkMnaDaeProblem 1 { rcDiodeRectifierMnaProblem with spec :=
      { rcDiodeRectifierMnaSpec with matG := [[2, -1], [-1]] } } rcDiodeRectifierMnaCert =
        .refused .badMatrixDims [] ∧
    checkMnaDaeProblem 1 { rcDiodeRectifierMnaProblem with spec :=
      { rcDiodeRectifierMnaSpec with matB := [[1, 0], [0]] } } rcDiodeRectifierMnaCert =
        .refused .badMatrixDims [] := by decide +kernel
example : checkMnaDaeProblem 1 rcDiodeRectifierMnaProblem rcDiodeRectifierMnaCert = .ok := by decide +kernel
-- A genuine connected two-step, zero-current trace is accepted.
def connected : MnaDaeProblem := ⟨currentLoopMnaSpec, .trapezoidal,
  [currentLoopMnaStep 0 0, currentLoopMnaStep 0 0]⟩
def connectedCert : MnaDaeCert := ⟨[⟨1, [1]⟩], [⟨2, [1]⟩]⟩
example : checkMnaDaeProblem 2 connected connectedCert = .ok := by decide +kernel
example : checkMnaDaeProblem 1 { connected with trace :=
    [⟨1/100, [0], [0], [], [], [], 0⟩] } connectedCert =
      .refused .badTraceDimsOrContinuity [] := by decide +kernel

theorem saturation_checks :
    checkCurrentLoopNoSaturation 32 100 false 400 50 (-10) 10 (-20) 20 = true ∧
    checkCurrentLoopNoSaturation 64 100 true 1717986918 214748365 (-10) 10 (-20) 20 = true ∧
    checkCurrentLoopNoSaturation 8 100 false 400 50 (-10) 10 (-20) 20 = false ∧
    checkCurrentLoopNoSaturation 32 10 false 400 50 (-10) 10 (-20) 20 = false := by decide +kernel
example : CurrentLoopNoSaturation 32 100 false 400 50 7 12 :=
  checkCurrentLoopNoSaturation_sound 32 100 false 400 50 (-10) 10 (-20) 20
    saturation_checks.1 7 12 (by decide) (by decide)
example : InterSampleFlow mkCurrentLoopShieldSpec 1 1 (currentLoopShieldFlow 2 1) :=
  currentLoopInterSampleFlow_sound 1 1 2 (by decide +kernel)
example : currentLoopShieldFlow 2 1 (1/100) = 136/67 := by decide +kernel
example : mnaStepResidual currentLoopMnaSpec .trapezoidal (currentLoopMnaStep 2 1) = [0] :=
  currentLoopMnaStep_residual 2 1
example : Obend.ClusterGov.PhysicalEnvelope.currentLoopEnvelopeHome
    (Obend.ClusterGov.PhysicalEnvelope.currentLoopEnvelopeStep 0
      (Obend.ClusterGov.PhysicalEnvelope.currentLoopEnvelopeRecovery 0)) := by
  apply Obend.ClusterGov.PhysicalEnvelope.currentLoopEnvelope_recovery_home
  unfold Obend.ClusterGov.PhysicalEnvelope.currentLoopEnvelopeSafe
  decide +kernel

theorem fvm_obj_roundtrip :
    (decodeHyperbolicFvmObj (encodeHyperbolicFvmObj maxwellSystem)).toOption = some maxwellSystem := by decide +kernel
theorem fvm_cert_roundtrip :
    (decodeHyperbolicFvmCert (encodeHyperbolicFvmCert maxwellCert)).toOption = some maxwellCert := by decide +kernel
example : Judge.Verdict.isOk (hyperbolicFvmFormat.checkBytes 0 (encodeHyperbolicFvmObj maxwellSystem)
    (encodeHyperbolicFvmCert maxwellCert)) = true := by decide +kernel
private theorem except_eq_ok {α : Type} {e : Except String α} {a : α}
    (h : e.toOption = some a) : e = .ok a := by
  cases e with
  | error _ => cases h
  | ok b => exact congrArg Except.ok (Option.some.inj h)
private def qfObjWire : String := r#"{"si":{"tempK":300,"epsR":{"num":119,"den":10},"eps0":{"num":5533867383,"den":62500000000000000000000},"q":{"num":801088317,"den":5000000000000000000000000000},"kB":{"num":1380649,"den":100000000000000000000000000000},"nc":28600000000000000000,"nv":31000000000000000000,"egEv":{"num":5621,"den":5000}},"ctN":{"muMin":65,"muMax":1330,"nRef":85000000000000000,"alphaNum":18,"alphaDen":25},"ctP":{"muMin":{"num":477,"den":10},"muMax":495,"nRef":63000000000000000,"alphaNum":19,"alphaDen":25},"tauN":{"num":1,"den":100000},"tauP":{"num":1,"den":100000},"background":10000000000000000,"recipe":[],"xCm":[0,{"num":1,"den":100000},{"num":1,"den":50000}],"areaCm2":1,"biasV":0,"tolRel":{"num":1,"den":10000000},"mobDelta":{"num":1,"den":1000000},"dealGroveTol":{"num":1,"den":1000000000}}"#
private theorem qfObjWire_chars : encodeDdSpecChars badSpec = qfObjWire.toList := by
  conv => rhs; unfold qfObjWire; rw [String.toList_ofList]
  decide +kernel
private def qfCertWire : String := r#"{"base":{"recipeCert":[],"ni":{"num":2684970255583047,"den":250000},"doping":[10000000000000000,10000000000000000,10000000000000000],"total":[10000000000000000,10000000000000000,10000000000000000],"psi":[{"num":3553132882203481,"den":10000000000000000},{"num":3553132882203481,"den":10000000000000000},{"num":3553132882203481,"den":10000000000000000}],"n":[{"num":1000000000001153450443737,"den":100000000},{"num":1000000000001153450443737,"den":100000000},{"num":1000000000001153450443737,"den":100000000}],"p":[{"num":1153450443737,"den":100000000},{"num":1153450443737,"den":100000000},{"num":1153450443737,"den":100000000}],"rN":[{"num":10709973045653989,"den":50000000000000000},{"num":10709973045653989,"den":50000000000000000},{"num":10709973045653989,"den":50000000000000000}],"rP":[{"num":2468886826717447,"den":10000000000000000},{"num":2468886826717447,"den":10000000000000000},{"num":2468886826717447,"den":10000000000000000}],"currentA":0},"phiN":[0,0,0],"phiP":[0,0,0]}"#
private theorem qfCertWire_chars : encodeDdQuasiFermiChars slabQuasiFermi = qfCertWire.toList := by
  conv => rhs; unfold qfCertWire; rw [String.toList_ofList]
  decide +kernel
private theorem qf_obj_option : (decodeDdSpec (encodeDdSpec badSpec)).toOption = some badSpec := by
  conv => lhs; rw [decodeDdSpec_encode_eq, qfObjWire_chars]; unfold qfObjWire; rw [String.toList_ofList]
  decide +kernel
theorem qf_obj_roundtrip : decodeDdSpec (encodeDdSpec badSpec) = .ok badSpec :=
  except_eq_ok (e := decodeDdSpec (encodeDdSpec badSpec)) (a := badSpec) qf_obj_option
private theorem qf_cert_option :
    (decodeDdQuasiFermiSolution (encodeDdQuasiFermiSolution slabQuasiFermi)).toOption = some slabQuasiFermi := by
  conv => lhs; rw [decodeDdQuasiFermi_encode_eq, qfCertWire_chars]; unfold qfCertWire; rw [String.toList_ofList]
  decide +kernel
theorem qf_cert_roundtrip :
    decodeDdQuasiFermiSolution (encodeDdQuasiFermiSolution slabQuasiFermi) = .ok slabQuasiFermi :=
  except_eq_ok (e := decodeDdQuasiFermiSolution (encodeDdQuasiFermiSolution slabQuasiFermi))
    (a := slabQuasiFermi) qf_cert_option
private theorem format_accepts_decoded (F : Judge.Format) (r : Nat) (obj cert : String)
    (o : F.Obj) (c : F.Cert) (ho : F.decodeObj obj = .ok o) (hc : F.decodeCert cert = .ok c)
    (hj : F.judge.check r o c = .ok) : F.checkBytes r obj cert = .ok := by
  unfold Judge.Format.checkBytes
  simp only [ho, hc, hj, Judge.Verdict.map]
example : Judge.Verdict.isOk (devsimQfermiFormat.checkBytes 0 (encodeDdSpec badSpec)
    (encodeDdQuasiFermiSolution slabQuasiFermi)) = true :=
  congrArg Judge.Verdict.isOk (format_accepts_decoded devsimQfermiFormat 0
    (encodeDdSpec badSpec) (encodeDdQuasiFermiSolution slabQuasiFermi) badSpec slabQuasiFermi
    qf_obj_roundtrip qf_cert_roundtrip slabQuasiFermi_accepted)
example : devsimQfermiFormat.name = "devsim-qfermi" ∧ devsimQfermiFormat.version = "1" := by decide +kernel
example : (decodeHyperbolicFvmObj "{}").toOption = none ∧
    (decodeDdQuasiFermiSolution "{}").toOption = none := by decide +kernel

#tooth Obend.Hardware.CircuitDae.checkMnaDaeProblem_sound by
  mutation Obend.Hardware.CircuitDae.checkMnaSpecDims := fun _ => true
#tooth Obend.Hardware.CircuitDae.checkMnaDaeProblem_sound by
  mutation Obend.Hardware.CircuitDae.checkMnaTrace := fun _ _ _ => true
#tooth Obend.Hardware.CurrentLoop.checkCurrentLoopNoSaturation_sound by
  mutation Obend.Hardware.CurrentLoop.checkCurrentLoopNoSaturation := fun _ _ _ _ _ _ _ _ _ => true
#tooth Obend.Hardware.SafePhysicalShield.currentLoopInterSampleFlow_sound by
  mutation Obend.Hardware.SafePhysicalShield.currentLoopShieldFlow := fun i _ t => i + 1000*t
#tooth Obend.Hardware.SafePhysicalShield.currentLoopMnaStep_residual by
  mutation Obend.Hardware.SafePhysicalShield.currentLoopMnaStep := fun i u =>
    ⟨1/100, [i], [i + 1], [currentLoopShieldVoltage u], [], [], 0⟩
#tooth Obend.ClusterGov.PhysicalEnvelope.currentLoopPhysicalEnvelope_corrigibility_safe by
  mutation Obend.ClusterGov.PhysicalEnvelope.currentLoopEnvelopeStep := fun i _ => i + 10
#tooth Obend.Apps.SdrFt8Rx.sdr_rf_frontEnd_composition by
  mutation Obend.Hardware.SwitchedCapRf.compositeAliasPower := fun _ _ _ _ _ => 100
#tooth Obend.Analysis.HyperbolicPde.check_sound by
  mutation Obend.Analysis.HyperbolicPde.check := fun _ _ => .ok
#tooth Obend.Hardware.Device.checkDdQuasiFermi_sound by
  mutation Obend.Hardware.Device.checkDdQuasiFermi := fun _ _ => .ok

#assert_axioms_tree
end Obend.Tests.Seam4bPhysicalDaePdeEnvelope
