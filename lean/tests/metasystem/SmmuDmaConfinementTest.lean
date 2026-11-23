module
/-
# SmmuDmaConfinementTest — Golden `OBEND.SHE.SMMU_MANIFEST/v1` vectors, Hardware STE/DDT/PTE/CmdQ
  bit-layouts, Multi-Page 4-level Stage-2 radix walker & IOTLB epoch tests, & 23 `#tooth` kills
-/
public import Obend.OS.SmmuRadixTables
public import Obend.OS.SmmuDmaConfinement
import all Obend.OS.SmmuRadixTables
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

private local instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e₁, .error e₂ => e₁ == e₂
    | _, _ => false

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

/-! ## 2. Locked Hardware STE, RISC-V DDTE, 64-Bit Stage-2 Descriptor & 128-Bit Command Vectors -/

-- Exact 512-bit (`8 × UInt64`) Armv8 SMMUv3 STE golden layout locked with Rust `iommu_microkit_confinement.rs`:
#guard SmmuV3Ste.packStage2 1 0x60152000 ==
  ⟨0x000000000000000d, 0x0000000000000000, 0x040d009000000001, 0x0000000060152000, 0, 0, 0, 0⟩
#guard decodeSmmuV3Ste (SmmuV3Ste.packStage2 1 0x60152000) == some (.stage2 1 0x60152000)
#guard decodeSmmuV3Ste (SmmuV3Ste.packStage2 0x0c01 0x60153000) == some (.stage2 0x0c01 0x60153000)
#guard decodeSmmuV3Ste SmmuV3Ste.abort == some .abort
-- Non-zero `EATS[93:92]` (`w1` bit 28) and `Config=0b100` untranslated bypass are refused!
#guard decodeSmmuV3Ste { SmmuV3Ste.packStage2 1 0x60152000 with w1 := (1 : UInt64) <<< 28 } == none
#guard decodeSmmuV3Ste { SmmuV3Ste.packStage2 1 0x60152000 with w0 := (1 : UInt64) ||| ((0b100 : UInt64) <<< 1) } == none

-- Exact 256-bit (`4 × UInt64`) RISC-V IOMMU Base-Format DDTE (`Sv48x4`, `16 KiB`-aligned `PPN[1:0]=0`) golden layout:
#guard RiscvDdtEntry.packSv48x4 1 0x60154000 == ⟨0x0000000000000001, 0x9000100000060154, 0, 0⟩
#guard decodeRiscvDdtEntry (RiscvDdtEntry.packSv48x4 1 0x60154000) == some (.sv48x4 1 0x60154000)
#guard decodeRiscvDdtEntry RiscvDdtEntry.abort == some .abort
#guard decodeRiscvDdtEntry { RiscvDdtEntry.packSv48x4 1 0x60154000 with tc := 3 } == none
-- Non-16KiB-aligned `Sv48x4` PPN (`0x60152000`, `PPN[1:0] = 0b10 != 0`) is rejected by both wire decoder & checked packer!
#guard decodeRiscvDdtEntry ⟨1, 0x9000100000060152, 0, 0⟩ == none
#guard RiscvDdtEntry.packSv48x4Checked 7 0x60152000 == none
#guard RiscvDdtEntry.packSv48x4Checked 0 0x60154000 == none
#guard RiscvDdtEntry.packSv48x4Checked 1 0x60154000 == some (RiscvDdtEntry.packSv48x4 1 0x60154000)
#guard SmmuV3Ste.packStage2Checked 0 0x60152000 == none
#guard SmmuV3Ste.packStage2Checked 1 0x60152100 == none
#guard SmmuV3Ste.packStage2Checked 1 0x60152000 == some (SmmuV3Ste.packStage2 1 0x60152000)

-- Exact 64-bit Armv8 Stage-2 Table, L3 4KiB Page, and L2 2MiB Block descriptor bit-layouts:
#guard encodeStage2TableDesc 0x60153000 == 0x0000000060153003
#guard decodeStage2TableDesc 0x0000000060153003 == some 0x60153000
#guard encodeStage2Page4KDesc 0x60846000 .writeOnly == 0x0040000060846483
#guard decodeStage2L3Desc 0x0040000060846483 == some (0x60846000, .writeOnly)
#guard encodeStage2Block2MDesc 0x60200000 .readOnly == 0x0040000060200441
#guard decodeStage2L2Desc 0x0040000060200441 == some (.inr (0x60200000, .readOnly))
-- Executable Stage-2 PTE (`XN != 0b10`) or `AF = 0` is refused!
#guard decodeStage2L3Desc ((0x0040000060846483 : UInt64) ||| ((1 : UInt64) <<< 53)) == none
#guard decodeStage2L3Desc ((0x0040000060846483 : UInt64) &&& ~~~((1 : UInt64) <<< 10)) == none
#guard encodeStage2TableDescChecked 0x60153100 == none
#guard encodeStage2TableDescChecked 0x60153000 == some 0x0000000060153003
#guard encodeStage2Block2MDescChecked 0x60201000 .readOnly == none
#guard encodeStage2Block2MDescChecked 0x60200000 .readOnly == some 0x0040000060200441
#guard encodeStage2Page4KDescChecked 0x60846004 .writeOnly == none
#guard encodeStage2Page4KDescChecked 0x60846000 .writeOnly == some 0x0040000060846483

-- Exact 128-bit SMMUv3 Command Queue (`CMD_CFGI_STE`, `CMD_TLBI_S2_IPA`, `CMD_TLBI_S12_VMALL`, `CMD_SYNC`)
-- bit-layouts per Arm IHI 0070 §4.3.1 / §4.4.3.1–2 (`VMID[47:32]`, `[63:48]` & `[31:8]` RES0):
#guard encodeSmmuCmd (.cfgiSte 0x10 false) == some (0x0000001000000003, 0)
#guard decodeSmmuCmd (0x0000001000000003, 0) == some (.cfgiSte 0x10 false)
#guard encodeSmmuCmd (.tlbiS2Ipa 1 0x80000000 false) == some (0x000000010000002a, 0x0000000080000000)
#guard decodeSmmuCmd (0x000000010000002a, 0x0000000080000000) == some (.tlbiS2Ipa 1 0x80000000 false)
#guard encodeSmmuCmd (.tlbiS12Vmall 1) == some (0x0000000100000028, 0)
#guard decodeSmmuCmd (0x0000000100000028, 0) == some (.tlbiS12Vmall 1)
-- Non-zero RES0 bits `[63:48]` or unaligned IPA in `CMD_TLBI_S2_IPA` are refused!
#guard decodeSmmuCmd (0x000100010000002a, 0x0000000080000000) == none
#guard encodeSmmuCmd (.tlbiS2Ipa 1 0x80000004 false) == none
#guard encodeSmmuCmd .sync == some (0x46, 0)
#guard decodeSmmuCmd (0x46, 0) == some .sync

/-! ## 3. Multi-Page 4-Level Stage-2 Radix Arena Walk (`4 KiB` & `2 MiB`) & IOTLB Epoch Safety -/

#guard (translateStage2Dma canonicalSmmuManifest 0x10 0x80000100 64 .dmaWrite).toOption == some 0x60846100
#guard match translateStage2Dma canonicalSmmuManifest 0x10 0x80000100 64 .dmaRead with
  | .error (.permissionFault 0x10 .dmaRead .writeOnly) => true | _ => false
#guard (translateStage2Dma canonicalSmmuManifest 0x30 0x80020020 128 .dmaRead).toOption == some 0x60849020
#guard match translateStage2Dma canonicalSmmuManifest 0x30 0x80020020 128 .dmaWrite with
  | .error (.permissionFault 0x30 .dmaWrite .readOnly) => true | _ => false
#guard match translateStage2Dma canonicalSmmuManifest 0x99 0x80000000 16 .dmaRead with
  | .error (.faultOnUnmappedStream 0x99) => true | _ => false
#guard match translateStage2Dma canonicalSmmuManifest wildcardStreamId 0x80000000 16 .dmaWrite with
  | .error (.invalidStreamId s) => s == wildcardStreamId | _ => false

def hugePageDisplayCameraConfig : ChokepointSmmuConfig where
  manifest :=
    { arch := .armSmmuV3
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
#guard (verifyChokepointSmmuConfig { hugePageDisplayCameraConfig with
  manifest := { hugePageDisplayCameraConfig.manifest with arch := .riscvIommu } }).toOption == some ()
#guard (translateStage2Dma hugePageDisplayCameraConfig.manifest 0x40 0x901abcde 256 .dmaRead).toOption ==
  some 0x603abcde
-- Armv8 SMMUv3 radix compiler refuses `.riscvIommu` manifests (`Sv48x4` uses distinct 16KiB-root PTEs!):
#guard compileManifestToRadixArena { hugePageDisplayCameraConfig.manifest with arch := .riscvIommu } 0x60000000 16 ==
  .error .armSmmuV3Required
-- `leaf = true` `CMD_TLBI_S2_IPA` at interior `4 KiB` IPA (`0x90001000`) evicts a cached `2 MiB` block (`0x90000000..0x90200000`)!
#guard (runSmmuCmds ⟨[], [], [⟨0x40, 0x40, 0x90000000, 0x60200000, .huge2MiB, .readOnly, 0⟩]⟩
  [.tlbiS2Ipa 0x40 0x90001000 true, .sync]).iotlb.isEmpty

-- Compile `hugePageDisplayCameraConfig` AND `canonicalRadixSmmuConfig` into concrete 4-level radix
-- page-table arenas and verify multi-page `walkSmmuV3Stage2 == translateStage2Dma` + mechanical eviction!
#guard
  match compileManifestToRadixArena hugePageDisplayCameraConfig.manifest 0x60000000 16 with
  | .error _ => false
  | .ok arena =>
    walkSmmuV3Stage2 arena 0x40 0x90000800 0x180000 .dmaRead == .ok 0x60200800 &&
      walkSmmuV3Stage2 arena 0x40 0x901ff800 0x1000 .dmaRead ==
        .error (.zeroOrUnmappedIova 0x40 0x901ff800 0x1000) &&
      walkSmmuV3Stage2 arena 0x50 0x90400000 64 .dmaRead ==
        .error (.permissionFault 0x50 .dmaRead .writeOnly) &&
      walkSmmuV3Stage2 arena 0x77 0x90000000 64 .dmaRead ==
        .error (.faultOnUnmappedStream 0x77)

#guard
  match compileManifestToRadixArena canonicalRadixSmmuConfig.manifest 0x60310000 32 with
  | .error _ => false
  | .ok arena =>
    let multiPageOk :=
      walkSmmuV3Stage2 arena 0x20 0x80010400 0x1800 .dmaWrite == .ok 0x60847400 &&
      walkSmmuV3Stage2 arena 0x20 0x80010000 0x2000 .dmaRead == .ok 0x60847000
    let crossBoundaryRefused :=
      walkSmmuV3Stage2 arena 0x10 0x80000fc0 128 .dmaWrite ==
        .error (.zeroOrUnmappedIova 0x10 0x80000fc0 128)
    let (r0, tlb1) := translateWithIotlb [] arena 0 0x10 0x80000040 64 .dmaWrite
    -- Arm IHI 0070 §4.3.1: `CMD_CFGI_STE + CMD_SYNC` alone invalidates STE config cache, NOT IOTLB!
    let afterCfgiOnly := runSmmuCmds ⟨[], [], tlb1⟩ [.cfgiSte 0x10 false, .sync]
    -- Raw 128-bit command queue words (`CFGI_STE`, `SYNC`, `TLBI_S2_IPA` w/ VMID at `[47:32]`, `SYNC`) evict IOTLB!
    let afterRawTlbiSync := runRawSmmuCmds ⟨[], [], tlb1⟩
      [(0x0000001000000003, 0), (0x46, 0), (0x000000100000002a, 0x0000000080000000), (0x46, 0)]
    let st0 : SmmuEpochState := ⟨0, canonicalRadixSmmuConfig, 0x60310000, 32, arena, tlb1⟩
    let oldReg : Stage2DmaRegion := ⟨0x80000000, 0x60846000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩
    let refusedSpoofVmid := unmapOrReassignDmaRegion st0 0x10 0x99 oldReg reassignedRadixSmmuConfig
      0x60310000 32 [.cfgiSte 0x10 false, .sync, .tlbiS2Ipa 0x99 0x80000000 false, .sync]
    let refusedCfgiOnly := unmapOrReassignDmaRegion st0 0x10 0x10 oldReg reassignedRadixSmmuConfig
      0x60310000 32 [.cfgiSte 0x10 false, .sync]
    let refusedNoSync := unmapOrReassignDmaRegion st0 0x10 0x10 oldReg reassignedRadixSmmuConfig
      0x60310000 32 [.cfgiSte 0x10 false, .sync, .tlbiS2Ipa 0x10 0x80000000 false]
    let refusedNoMidSync := unmapOrReassignDmaRegion st0 0x10 0x10 oldReg reassignedRadixSmmuConfig
      0x60310000 32 [.cfgiSte 0x10 false, .tlbiS2Ipa 0x10 0x80000000 false, .sync]
    let refusedTlbiBeforeCfgi := unmapOrReassignDmaRegion st0 0x10 0x10 oldReg reassignedRadixSmmuConfig
      0x60310000 32 [.tlbiS2Ipa 0x10 0x80000000 false, .sync, .cfgiSte 0x10 false, .sync]
    let coalescableManifest : SmmuManifest :=
      { canonicalRadixSmmuConfig.manifest with streams :=
          [ ⟨0x10, .ingressNic, .ingress,
              [ ⟨0x80000000, 0x60846000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩
              , ⟨0x80001000, 0x60847000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩ ]⟩ ] }
    let refusedCoalescable := compileManifestToRadixArena coalescableManifest 0x60310000 32
    let badCrossStreamCfg : ChokepointSmmuConfig :=
      { reassignedRadixSmmuConfig with manifest :=
          { reassignedRadixSmmuConfig.manifest with streams :=
              reassignedRadixSmmuConfig.manifest.streams.take 1 } }
    let refusedCrossStream := unmapOrReassignDmaRegion st0 0x10 0x10 oldReg badCrossStreamCfg
      0x60310000 32 [.cfgiSte 0x10 false, .sync, .tlbiS2Ipa 0x10 0x80000000 false, .sync]
    let refusedShiftedArenaNoVmall := unmapOrReassignDmaRegion st0 0x10 0x10 oldReg reassignedRadixSmmuConfig
      0x60318000 24 [.cfgiSte 0x10 false, .sync, .tlbiS2Ipa 0x10 0x80000000 false, .sync]
    let acceptedShiftedArenaSynced := unmapOrReassignDmaRegion st0 0x10 0x10 oldReg reassignedRadixSmmuConfig
      0x60318000 24 [.cfgiSte 0x10 false, .cfgiSte 0x20 false, .cfgiSte 0x30 false, .sync,
        .tlbiS12Vmall 0x20, .tlbiS12Vmall 0x30, .tlbiS2Ipa 0x10 0x80000000 false, .sync]
    let acceptedSynced := unmapOrReassignDmaRegion st0 0x10 0x10 oldReg reassignedRadixSmmuConfig
      0x60310000 32 [.cfgiSte 0x10 false, .sync, .tlbiS2Ipa 0x10 0x80000000 false, .sync]
    let newReg1 : Stage2DmaRegion := ⟨0x80000000, 0x6084a000, 0x1000, .page4KiB, .writeOnly, .ingressRing⟩
    let trace2Turns := runSmmuEpochTrace st0 (fun pa => if pa == 0x60300000 then 0x5a else 0)
      [ .reconfig 0x10 0x10 oldReg reassignedRadixSmmuConfig 0x60310000 32
          [.cfgiSte 0x10 false, .sync, .tlbiS2Ipa 0x10 0x80000000 false, .sync]
          [.write 0x10 0x80000000 (ByteArray.mk #[0x11])]
      , .reconfig 0x10 0x10 newReg1 canonicalRadixSmmuConfig 0x60318000 24
          [.cfgiSte 0x10 false, .cfgiSte 0x20 false, .cfgiSte 0x30 false, .sync,
           .tlbiS12Vmall 0x20, .tlbiS12Vmall 0x30, .tlbiS2Ipa 0x10 0x80000000 false, .sync]
          [.write 0x10 0x80000000 (ByteArray.mk #[0x22])] ]
    let trace2Ok := match trace2Turns with
      | none => false
      | some (st2, mem2, obs2) => st2.epoch == 2 && mem2 0x60300000 == 0x5a && mem2 0x60846000 == 0x22 && obs2.length == 2
    let epoch1HitOk := match acceptedSynced with
      | .error _ => false
      | .ok st1 =>
        st1.iotlb.isEmpty &&
          (translateWithIotlb st1.iotlb st1.arena st1.epoch 0x10 0x80000040 64 .dmaWrite).1 == .ok 0x6084a040
    multiPageOk && crossBoundaryRefused &&
      r0 == .ok 0x60846040 && tlb1.length == 1 && afterCfgiOnly.iotlb.length == 1 &&
      (match afterRawTlbiSync with | some q => q.iotlb.isEmpty | none => false) &&
      refusedSpoofVmid == .error .invalidOldStreamVmid &&
      refusedCfgiOnly == .error .missingTlbiOrSync &&
      refusedNoSync == .error .missingTlbiOrSync &&
      refusedNoMidSync == .error .missingTlbiOrSync &&
      refusedTlbiBeforeCfgi == .error .missingTlbiOrSync &&
      refusedShiftedArenaNoVmall == .error .missingTlbiOrSync &&
      acceptedShiftedArenaSynced.isOk && trace2Ok &&
      refusedCoalescable == .error .invalidStreams &&
      refusedCrossStream == .error .unannouncedCrossStreamMutation && epoch1HitOk

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

/-! ## 4. `smmuChokepointJudge` Acceptance, Fuel Monotonicity, & Planted-Fault Refusals -/

#guard smmuChokepointCheck 5 canonicalSmmuQuery canonicalSmmuCert == .ok
#guard smmuChokepointCheck 4 canonicalSmmuQuery canonicalSmmuCert == .uncovered

def badNoDefaultDeny : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config := { canonicalSmmuConfig with
      manifest := { canonicalSmmuManifest with defaultDeny := false } } }
#guard smmuChokepointCheck 10 badNoDefaultDeny canonicalSmmuCert ==
  .refused .defaultDenyDisabled []

def badSpanBudget : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config := { canonicalSmmuConfig with
      manifest := { canonicalSmmuManifest with dmaPoolSize := 0x00500000 } } }
#guard smmuChokepointCheck 10 badSpanBudget canonicalSmmuCert ==
  .refused .spanExceedsBudget []

def badWildcardStream : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config := { canonicalSmmuConfig with
      manifest := { canonicalSmmuManifest with
        streams := { streamId := wildcardStreamId, role := .ingressNic, ownerPd := .ingress,
                     regions := [] } :: canonicalSmmuManifest.streams } } }
#guard smmuChokepointCheck 10 badWildcardStream canonicalSmmuCert ==
  .refused .wildcardStreamId []

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

def badOverlappingCommit : SmmuManifestQuery :=
  { canonicalSmmuQuery with
    config :=
      { manifest := canonicalSmmuManifest
        partition := { canonicalSmmuConfig.partition with commitPrivateFrames := [0x60846] } } }
#guard smmuChokepointCheck 10 badOverlappingCommit canonicalSmmuCert ==
  .refused .overlappingCommitFrame []

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

#guard smmuChokepointCheck 10 canonicalSmmuQuery ⟨ByteArray.mk (Array.replicate 32 0)⟩ ==
  .refused .certDigestMismatch []
#guard smmuRefusalRefutes .overlappingCommitFrame == true
#guard smmuRefusalRefutes .wildcardStreamId == true
#guard smmuRefusalRefutes .writableCodeOrOutbox == true
#guard smmuRefusalRefutes .spanExceedsBudget == true
#guard smmuRefusalRefutes .certDigestMismatch == false

/-! ## 5. Universal `#tooth` Mutation-Sensitivity Kills (23 Kills ≥ 10 Required) -/

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

#tooth ste_eats_nonzero_refused by
  mutation decodeSmmuV3Ste := fun ste => some (.stage2 1 ste.w3)

#tooth decodeRiscvDdtEntry_packSv48x4 by
  mutation sv48x4RootAlign := 8192

#tooth decodeSmmuCmd_encodeSmmuCmd by
  mutation encodeSmmuCmd := fun _ => none

#tooth walkSmmuV3Stage2_agrees_on_region by
  mutation walkSmmuV3Stage2 := fun _ sid _ _ _ => .error (.faultOnUnmappedStream sid)

-- Surgical multi-page contiguity mutation: skipping subsequent L3 page checks breaks cross-page refusal!
#tooth walkSmmuV3Stage2_cross_page_escape_refused by
  mutation checkContigPages := fun _ _ _ _ _ _ _ => true

-- Surgical multi-page contiguity mutation: skipping subsequent L3 page checks breaks multi-page refinement!
#tooth walkSmmuV3Stage2_refines_spec by
  mutation checkContigPages := fun _ _ _ _ _ _ _ => true

#tooth dma_cannot_write_smmu_tables by
  mutation execSmmuV3HardwareDmaOp := fun _ mem op =>
    match op with
    | .read _ iova len => (mem, some (readPhys mem iova len))
    | .write _ iova payload => (writePhys mem iova payload, none)

#tooth reconfig_without_tlbi_sync_refused by
  mutation unmapOrReassignDmaRegion := fun st _ _ _ _ _ _ _ => .ok st

#tooth tlbi_sync_evicts_cached_entry by
  mutation cmdEvictsEntry := fun _ _ => false

-- Surgical `CMD_CFGI_STE -> CMD_SYNC -> CMD_TLBI_*` ordering mutation: skipping `cmdsAfterCfgi` breaks eviction!
#tooth reconfigQueueValidB_evicts_unmapped_region by
  mutation cmdsAfterCfgi := fun cmds _ => some cmds

-- Surgical `CMD_TLBI_S2_IPA` coverage mutation: skipping per-page `TLBI_S2_IPA` check breaks eviction!
#tooth reconfigQueueValidB_evicts_unmapped_region by
  mutation syncedCoversRegionTlbi := fun _ _ _ => true

-- Surgical `CMD_TLBI_S2_IPA` coverage mutation: skipping `TLBI_S2_IPA` breaks `tlbi_synced_reconfig_dma_safe`!
#tooth tlbi_synced_reconfig_dma_safe by
  mutation syncedCoversRegionTlbi := fun _ _ _ => true

-- Surgical `onlyOldRegChangedB` mutation: ignoring unannounced region edits breaks `tlbi_synced_reconfig_dma_safe`!
#tooth tlbi_synced_reconfig_dma_safe by
  mutation onlyOldRegChangedB := fun _ _ _ _ => true

#tooth tlbi_synced_reconfig_dma_safe by
  mutation execIotlbHardwareDmaOp := fun _ _ iotlb mem op =>
    match op with
    | .read _ iova len => (mem, iotlb, some (readPhys mem iova len))
    | .write _ iova payload => (writePhys mem iova payload, iotlb, none)

#tooth validSmmuEpochTrace_dma_safe by
  mutation unmapOrReassignDmaRegion := fun st _ _ _ cfg' ab' mf' _ =>
    .ok ⟨st.epoch + 1, cfg', ab', mf', st.arena, st.iotlb⟩

/-! ## 6. Kernel Axiom, Closed-Theorem, & `0 Classical.choice` Computational Audit -/

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
  let ownModules := [`Obend.OS.SmmuRadixTables, `Obend.OS.SmmuDmaConfinement]
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
      throwError "Custom axiom declaration in {mod}: {name}"
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
        throwError "Closed theorem in {mod}: {name}"
  Lean.logInfo "SHE Pillar 1 SmmuRadixTables + SmmuDmaConfinement audit passed: 0 custom axioms, 0 sorryAx, 0 compiler-trust, 0 closed library theorems, 0 computational choice."

#print axioms unmapped_stream_dma_faults
#print axioms translateStage2Dma_skip_implies_contract_violation
#print axioms verifyChokepointSmmuConfig_sound
#print axioms dma_burst_preserves_private_pd_frames
#print axioms smmu_verifier_loop_dma_safe
#print axioms smmuManifestPreimage_injective
#print axioms smmuManifestDigest_binds
#print axioms smmuChokepointCheck_sound
#print axioms smmuChokepointCheck_refuted
#print axioms decodeSmmuCmd_encodeSmmuCmd
#print axioms walkSmmuV3Stage2_agrees_on_region
#print axioms walkSmmuV3Stage2_cross_page_escape_refused
#print axioms walkSmmuV3Stage2_refines_spec
#print axioms dma_cannot_write_smmu_tables
#print axioms reconfigQueueValidB_evicts_unmapped_region
#print axioms reconfig_without_tlbi_sync_refused
#print axioms tlbi_synced_reconfig_dma_safe
#print axioms validSmmuEpochTrace_dma_safe

end Obend.Tests.SmmuDmaConfinementTest
end
