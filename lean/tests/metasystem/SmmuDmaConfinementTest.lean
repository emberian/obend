module
/-
# SmmuDmaConfinementTest — Golden `OBEND.SHE.SMMU_MANIFEST/v1` vectors, refusal suite, & `#tooth` kills
-/
public import Obend.OS.SmmuDmaConfinement
import all Obend.OS.SmmuDmaConfinement
import all Obend.OS.Sel4MicrokitKernelCore
import all Obend.OS.Sel4MicrokitKernel
import all Obend.Polis.SandboxDomainTags
import all Obend.AssertAxioms
import Obend.Tactic.Tooth

public section
namespace Obend.Tests.SmmuDmaConfinementTest

open Obend
open Obend.OS.Sel4MicrokitKernel
open Obend.OS.SmmuDmaConfinement

set_option autoImplicit false

/-! ## 1. Cross-Language Golden Test Vector #1 (`OBEND.SHE.SMMU_MANIFEST/v1`) -/

def toHex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[x.toNat / 16]!, digits[x.toNat % 16]!])

-- Exact 216-byte preimage length and 32-byte cSHAKE256 digest shared with `crates/obend-sel4-verifier`.
#guard canonicalSmmuManifest.preimage.length == 216

#guard (smmuManifestDigest canonicalSmmuManifest).data.toList ==
  [0xbc, 0x53, 0x8f, 0x6d, 0x7a, 0x5e, 0xf1, 0x80,
   0x33, 0x2e, 0xf0, 0xcd, 0x6c, 0xc8, 0xa1, 0x73,
   0x95, 0x55, 0x10, 0x9d, 0x68, 0x9d, 0x37, 0xa7,
   0xc8, 0x88, 0x6b, 0x10, 0x80, 0xd7, 0x23, 0x0e]

#guard toHex (smmuManifestDigest canonicalSmmuManifest) ==
  "bc538f6d7a5ef180332ef0cd6cc8a1739555109d689d37a7c8886b1080d7230e"

example : canonicalSmmuManifest.Fit := by
  refine ⟨by decide, by decide, ?_⟩
  intro pt hpt
  simp only [canonicalSmmuManifest, List.mem_cons, List.not_mem_nil, or_false] at hpt
  rcases hpt with rfl | rfl | rfl <;> decide

/-! ## 2. Stage-2 Translation (`4 KiB` & `2 MiB`) & Adversarial DMA Non-Interference Vectors -/

-- Authorized `IngressNic` write to `0x8000_0100` translates to `0x6084_6100`; read is refused!
#guard (translateStage2Dma canonicalSmmuManifest 0x10 0x80000100 64 .dmaWrite).toOption == some 0x60846100
#guard match translateStage2Dma canonicalSmmuManifest 0x10 0x80000100 64 .dmaRead with
  | .error (.permissionFault 0x10 .dmaRead .writeOnly) => true | _ => false

-- Authorized `EgressNic` read from `0x8002_0020` translates to `0x6084_9020`; write is refused!
#guard (translateStage2Dma canonicalSmmuManifest 0x30 0x80020020 128 .dmaRead).toOption == some 0x60849020
#guard match translateStage2Dma canonicalSmmuManifest 0x30 0x80020020 128 .dmaWrite with
  | .error (.permissionFault 0x30 .dmaWrite .readOnly) => true | _ => false

-- Unmapped peripheral StreamID (e.g. rogue PCIe function `0x99`) faults under `FaultOnUnmappedStream`.
#guard match translateStage2Dma canonicalSmmuManifest 0x99 0x80000000 16 .dmaRead with
  | .error (.faultOnUnmappedStream 0x99) => true | _ => false
#guard match translateStage2Dma canonicalSmmuManifest wildcardStreamId 0x80000000 16 .dmaWrite with
  | .error (.invalidStreamId s) => s == wildcardStreamId | _ => false

-- `2 MiB` hugepage DisplayScanout + CameraCsi2 manifest fixture.
def hugePageDisplayCameraConfig : ChokepointSmmuConfig where
  manifest :=
    { arch := .riscvIommu
      defaultDeny := true
      rootserverPhysStart := 0x60000000
      rootserverPhysEnd := 0x60200000
      dmaPoolBase := 0x60200000
      dmaPoolSize := 0x00600000
      protectedRanges :=
        [ { classTag := .commitPrivate, basePaddr := 0x60100000, size := 0x1000 }
        , { classTag := .kernelPageTable, basePaddr := 0x60000000, size := 0x10000 }
        ]
      streams :=
        [ { streamId := 0x40
            role := .displayScanout
            ownerPd := .txEgress
            regions :=
              [ { iova := 0x90000000
                  paddr := 0x60200000
                  size := 0x00200000
                  granule := .huge2MiB
                  perm := .readOnly
                  kind := .displayFramebuffer } ] }
        , { streamId := 0x50
            role := .cameraCsi2
            ownerPd := .ingress
            regions :=
              [ { iova := 0x90400000
                  paddr := 0x60400000
                  size := 0x00200000
                  granule := .huge2MiB
                  perm := .writeOnly
                  kind := .cameraRing } ] }
        ] }
  partition :=
    { rootServerBootSpan := (0x60000000, 0x60200000)
      ingressRingFrames := [0x60400]
      commitPrivateFrames := [0x60100]
      kernelAndCodeFrames := [0x60000]
      persistFrames := []
      egressOutboxFrames := [] }

#guard (verifyChokepointSmmuConfig hugePageDisplayCameraConfig).toOption == some ()
#guard (translateStage2Dma hugePageDisplayCameraConfig.manifest 0x40 0x901abcde 256 .dmaRead).toOption ==
  some 0x603abcde
#guard match translateStage2Dma hugePageDisplayCameraConfig.manifest 0x50 0x90400000 64 .dmaRead with
  | .error (.permissionFault 0x50 .dmaRead .writeOnly) => true | _ => false

-- Adversarial multi-device DMA burst check: secret bytes in `commitPrivateFrames` (`0x6030_0000`)
-- and finalized outbox bytes (`0x6084_9000`) survive untouched, and DMA reads cannot distinguish secrets!
def adversarialBurst : List PeripheralDmaOp :=
  [ .write 0x10 0x80000000 (ByteArray.mk #[0xaa, 0xbb])
  , .write 0x30 0x80020000 (ByteArray.mk #[0xff, 0xff])
  , .write 0x99 0x60300000 (ByteArray.mk #[0xde, 0xad])
  , .read 0x20 0x60300000 4
  , .read 0x30 0x80020000 2
  ]

def memSecretA (pa : Nat) : UInt8 :=
  if pa == 0x60300000 then 0x11 else if pa == 0x60849000 then 0x77 else 0x00

def memSecretB (pa : Nat) : UInt8 :=
  if pa == 0x60300000 then 0xee else if pa == 0x60849000 then 0x77 else 0x00

#guard
  let (m1, obs1) := execStage2DmaBurst canonicalSmmuManifest memSecretA adversarialBurst
  let (m2, obs2) := execStage2DmaBurst canonicalSmmuManifest memSecretB adversarialBurst
  m1 0x60300000 == 0x11 && m2 0x60300000 == 0xee &&
    m1 0x60849000 == 0x77 && m1 0x60846000 == 0xaa && obs1 == obs2

/-! ## 3. `smmuChokepointJudge` Acceptance, Fuel Monotonicity, & Planted-Fault Refusals -/

#guard smmuChokepointCheck 5 canonicalSmmuQuery canonicalSmmuCert == .ok
#guard smmuChokepointCheck 4 canonicalSmmuQuery canonicalSmmuCert == .uncovered

-- 1. `defaultDeny := false` -> `.defaultDenyDisabled` (refuting)
def badNoDefaultDeny : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config := { canonicalSmmuConfig with
      manifest := { canonicalSmmuManifest with defaultDeny := false } } }
#guard smmuChokepointCheck 10 badNoDefaultDeny canonicalSmmuCert ==
  .refused .defaultDenyDisabled []

-- 2. Root-server + DMA pool `>= 10 MiB` -> `.spanExceedsBudget` (refuting)
def badSpanBudget : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config := { canonicalSmmuConfig with
      manifest := { canonicalSmmuManifest with dmaPoolSize := 0x00500000 } } }
#guard smmuChokepointCheck 10 badSpanBudget canonicalSmmuCert ==
  .refused .spanExceedsBudget []

-- 3. Wildcard `0xFFFF_FFFF` StreamID -> `.wildcardStreamId` (refuting)
def badWildcardStream : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config := { canonicalSmmuConfig with
      manifest := { canonicalSmmuManifest with
        streams := { streamId := wildcardStreamId, role := .ingressNic, ownerPd := .ingress,
                     regions := [] } :: canonicalSmmuManifest.streams } } }
#guard smmuChokepointCheck 10 badWildcardStream canonicalSmmuCert ==
  .refused .wildcardStreamId []

-- 4. Unaligned IOVA (`0x8000_0123`) -> `.unalignedOrOutOfPoolRegion` (refuting)
def badUnalignedRegion : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config := { canonicalSmmuConfig with
      manifest := { canonicalSmmuManifest with
        streams :=
          [ { streamId := 0x10, role := .ingressNic, ownerPd := .ingress,
              regions := [ { iova := 0x80000123, paddr := 0x60846000, size := 0x1000,
                             granule := .page4KiB, perm := .writeOnly, kind := .ingressRing } ] } ] } } }
#guard smmuChokepointCheck 10 badUnalignedRegion canonicalSmmuCert ==
  .refused .unalignedOrOutOfPoolRegion []

-- 5. Stream overlapping `commit-pd` private verification frame -> `.overlappingCommitFrame` (refuting)
def badOverlappingCommit : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config :=
      { manifest := canonicalSmmuManifest
        partition := { canonicalSmmuConfig.partition with commitPrivateFrames := [0x60846] } } }
#guard smmuChokepointCheck 10 badOverlappingCommit canonicalSmmuCert ==
  .refused .overlappingCommitFrame []

-- 6. `EgressNic` granted writable Stage-2 access to finalized outbox -> `.writableCodeOrOutbox` (refuting)
def badWritableOutbox : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config := { canonicalSmmuConfig with
      manifest := { canonicalSmmuManifest with
        streams :=
          [ { streamId := 0x30, role := .egressNic, ownerPd := .txEgress,
              regions := [ { iova := 0x80020000, paddr := 0x60849000, size := 0x1000,
                             granule := .page4KiB, perm := .readWrite, kind := .egressOutboxRing } ] } ] } } }
#guard smmuChokepointCheck 10 badWritableOutbox canonicalSmmuCert ==
  .refused .writableCodeOrOutbox []

-- 7. `CameraCsi2` granted DMA read permission -> `.forbiddenRoleRegionPerm` (refuting)
def badCameraReadPerm : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config := { canonicalSmmuConfig with
      manifest := { canonicalSmmuManifest with
        streams :=
          [ { streamId := 0x50, role := .cameraCsi2, ownerPd := .ingress,
              regions := [ { iova := 0x80030000, paddr := 0x6084a000, size := 0x1000,
                             granule := .page4KiB, perm := .readWrite, kind := .cameraRing } ] } ] } } }
#guard smmuChokepointCheck 10 badCameraReadPerm canonicalSmmuCert ==
  .refused .forbiddenRoleRegionPerm []

-- 8. Tampered 32-byte certificate digest -> `.certDigestMismatch` (non-refuting: `refutes = false`)
#guard smmuChokepointCheck 10 canonicalSmmuQuery ⟨ByteArray.mk (Array.replicate 32 0)⟩ ==
  .refused .certDigestMismatch []
#guard smmuRefusalRefutes .overlappingCommitFrame == true
#guard smmuRefusalRefutes .wildcardStreamId == true
#guard smmuRefusalRefutes .writableCodeOrOutbox == true
#guard smmuRefusalRefutes .spanExceedsBudget == true
#guard smmuRefusalRefutes .certDigestMismatch == false

/-! ## 4. Universal `#tooth` Mutation-Sensitivity Kills (8 Kills ≥ 6 Required) -/

#tooth unmapped_stream_dma_faults by
  mutation translateStage2Dma := fun _ _ iova _ _ => .ok iova

#tooth translateStage2Dma_skip_implies_contract_violation by
  mutation translateStage2Dma := fun _ sid _ _ _ => .error (.faultOnUnmappedStream sid)

#tooth verifyChokepointSmmuConfig_sound by
  mutation verifyChokepointSmmuConfig := fun _ => .ok ()

#tooth dma_burst_preserves_private_pd_frames by
  mutation execStage2DmaOp := fun _ mem op =>
    match op with
    | .read _ iova len => (mem, some (readPhys mem iova len))
    | .write _ iova payload => (writePhys mem iova payload, none)

#tooth smmuManifestPreimage_injective by
  mutation encodeSmmuStreams := fun _ => []

#tooth smmuManifestDigest_binds by
  mutation smmuManifestDigest := fun _ => ByteArray.empty

#tooth smmuChokepointCheck_sound by
  mutation smmuChokepointCheck := fun _ _ _ => .ok

#tooth smmuChokepointCheck_refuted by
  mutation smmuChokepointCheck := fun _ _ _ => .refused .overlappingCommitFrame []

/-! ## 5. Kernel Axiom, Closed-Theorem, & `0 Classical.choice` Computational Audit -/

private partial def auditComputationalChoice (e : Lean.Expr) :
    StateRefT Lean.NameSet Lean.Meta.MetaM Unit := do
  if (← Lean.Meta.isProof e) || (← Lean.Meta.isType e) then return
  match e with
  | .const name _ =>
      if name == ``Classical.choice then throwError "Computational choice: {name}"
      if (← get).contains name then return
      modify (·.insert name)
      unless (← Lean.collectAxioms name).contains ``Classical.choice do return
      let info ← Lean.getConstInfo name
      if info matches .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ then return
      match info.value? with
      | some body => auditComputationalChoice body
      | none => throwError "Cannot inspect choice-dependent computational body: {name}"
  | .app f a => auditComputationalChoice f; auditComputationalChoice a
  | .lam name ty body bi =>
      Lean.Meta.withLocalDecl name bi ty fun x => auditComputationalChoice (body.instantiate1 x)
  | .letE name ty val body _ =>
      auditComputationalChoice val
      Lean.Meta.withLetDecl name ty val fun x => auditComputationalChoice (body.instantiate1 x)
  | .mdata _ body => auditComputationalChoice body
  | .proj _ _ body => auditComputationalChoice body
  | _ => pure ()

run_cmd do
  let env ← Lean.getEnv
  let ownModules := [`Obend.OS.SmmuDmaConfinement]
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless ownModules.contains mod do continue
    let axs ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms name)
    if axs.contains ``sorryAx then
      throwError "sorryAx dependency in {name}"
    if axs.toList.any Obend.AssertAxioms.isCompilerTrust then
      throwError "Compiler trust dependency in {name}"
    if info matches .axiomInfo _ then
      throwError "Custom axiom declaration in owned module: {name}"
    let outside := axs.toList.filter (!Obend.AssertAxioms.standard.contains ·)
    unless outside.isEmpty do
      throwError "Non-standard axioms in {name}: {outside}"
    if info matches .defnInfo _ | .opaqueInfo _ then
      if !Lean.isMarkedMeta env name && axs.contains ``Classical.choice then
        Lean.Elab.Command.liftTermElabM do
          let root := Lean.mkConst name (info.levelParams.map Lean.Level.param)
          try
            let _ ← (auditComputationalChoice root).run {}
            pure ()
          catch e => throwError "{name}: {e.toMessageData}"
    if name.isInternal || name.isInternalDetail then continue
    if name.components.getLast? == some `sizeOf_spec then continue
    if info matches .thmInfo _ then
      if ← Lean.Elab.Command.liftTermElabM (Obend.AssertAxioms.closedStatement info.type) then
        throwError "Closed theorem in owned module: {name}"
  Lean.logInfo "SHE Pillar 1 SmmuDmaConfinement audit passed: 0 custom axioms, 0 sorryAx, 0 compiler-trust, 0 closed library theorems, 0 computational choice."

#print axioms unmapped_stream_dma_faults
#print axioms translateStage2Dma_skip_implies_contract_violation
#print axioms verifyChokepointSmmuConfig_sound
#print axioms dma_burst_preserves_private_pd_frames
#print axioms smmu_verifier_loop_dma_safe
#print axioms smmuManifestPreimage_injective
#print axioms smmuManifestDigest_binds
#print axioms smmuChokepointCheck_sound
#print axioms smmuChokepointCheck_refuted

end Obend.Tests.SmmuDmaConfinementTest
end
