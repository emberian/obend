module
/-
# Obend.Hardware.AwsF2Shell — AWS EC2 F2 (`VU47P`) shell, `FABulous` BAR0 hot-swap, RapidWright macros, EDA signoff judges
1. `cl_ports.vh` shell wrapper (`xcvu47p-fsvh2892-2-e`): duplicate-free port bindings, exact core port correspondence, wired `u_core`.
2. Embedded `FABulous` eFPGA PCIe BAR0 hot-swap controller (`f2FabulousOverlayStep`), 256-bit frame digest binding.
3. Pre-placed UltraScale+ / RapidWright locked macro and `XDC` emitter over verified `PnrCertificate` coordinates.
4. Untrusted signoff judges `"vivado-sta@1"` and `"openpdk-drc-sta@1"` with token-wire byte codecs (`vivadoStaByteJudge`, `openpdkDrcStaByteJudge`).
-/
public import Obend.Core.Digest
public import Obend.Judge.Class
public import Obend.Category.Refines
public import Obend.Hardware.Process
public import Obend.Hardware.HDL
public import Obend.Hardware.Synth
public import Obend.Hardware.PlaceRoute
public import Obend.Hardware.DRC
public import Obend.Hardware.DprStutter
public section
namespace Obend.Hardware.AwsF2Shell
open Obend.Category Obend.Hardware.Process Obend.Hardware.HDL
open Obend.Hardware.Synth Obend.Hardware.PlaceRoute Obend.Hardware.DRC Obend.Hardware.DprStutter
set_option autoImplicit false

/-! ## 1. Authentic AWS EC2 F2 (`xcvu47p-fsvh2892-2-e`) `cl_ports.vh` Shell Interface & Wrapper -/
@[expose] def awsF2TargetDevice : String := "xcvu47p-fsvh2892-2-e"
@[expose] def awsF2MainClockPeriodPs : Nat := 4000
inductive SlrId where | slr0 | slr1 | slr2 deriving DecidableEq, Repr, Inhabited
def SlrId.toIndex : SlrId → Nat | .slr0 => 0 | .slr1 => 1 | .slr2 => 2
def SlrId.toString : SlrId → String | .slr0 => "SLR0" | .slr1 => "SLR1" | .slr2 => "SLR2"
def slrDistance (a b : SlrId) : Nat :=
  let ia := a.toIndex; let ib := b.toIndex
  if ia ≤ ib then ib - ia else ia - ib
inductive F2PortDir where | shToCl | clToSh deriving DecidableEq, Repr
inductive F2InterfaceGroup where
  | clkReset | flrMgmt | dmaPcisAxi4 | pcimAxi4
  | oclAxi4LiteBar0 | sdaAxi4LiteBar4 | appPfIrq | hbmAxi4 | hbmApb
  deriving DecidableEq, Repr
structure F2ShellPortSpec where
  name : String
  dir : F2PortDir
  width : Nat
  group : F2InterfaceGroup
  activeLow : Bool := false
  deriving DecidableEq, Repr
/-- Canonical AWS EC2 F2 HDK v2 `cl_ports.vh` port table (`xcvu47p-fsvh2892-2-e`). -/
def canonicalAwsF2ClPorts : List F2ShellPortSpec :=
  [ ⟨"clk_main_a0", .shToCl, 1, .clkReset, false⟩, ⟨"rst_main_n", .shToCl, 1, .clkReset, true⟩, ⟨"clk_hbm_ref", .shToCl, 1, .clkReset, false⟩
  , ⟨"sh_cl_flr_assert", .shToCl, 1, .flrMgmt, false⟩, ⟨"cl_sh_flr_done", .clToSh, 1, .flrMgmt, false⟩, ⟨"sh_cl_dma_pcis_awid", .shToCl, 16, .dmaPcisAxi4, false⟩
  , ⟨"sh_cl_dma_pcis_awaddr", .shToCl, 64, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_awlen", .shToCl, 8, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_awsize", .shToCl, 3, .dmaPcisAxi4, false⟩
  , ⟨"sh_cl_dma_pcis_awvalid", .shToCl, 1, .dmaPcisAxi4, false⟩, ⟨"cl_sh_dma_pcis_awready", .clToSh, 1, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_wdata", .shToCl, 512, .dmaPcisAxi4, false⟩
  , ⟨"sh_cl_dma_pcis_wstrb", .shToCl, 64, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_wlast", .shToCl, 1, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_wvalid", .shToCl, 1, .dmaPcisAxi4, false⟩
  , ⟨"cl_sh_dma_pcis_wready", .clToSh, 1, .dmaPcisAxi4, false⟩, ⟨"cl_sh_dma_pcis_bid", .clToSh, 16, .dmaPcisAxi4, false⟩, ⟨"cl_sh_dma_pcis_bresp", .clToSh, 2, .dmaPcisAxi4, false⟩
  , ⟨"cl_sh_dma_pcis_bvalid", .clToSh, 1, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_bready", .shToCl, 1, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_arid", .shToCl, 16, .dmaPcisAxi4, false⟩
  , ⟨"sh_cl_dma_pcis_araddr", .shToCl, 64, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_arlen", .shToCl, 8, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_arsize", .shToCl, 3, .dmaPcisAxi4, false⟩
  , ⟨"sh_cl_dma_pcis_arvalid", .shToCl, 1, .dmaPcisAxi4, false⟩, ⟨"cl_sh_dma_pcis_arready", .clToSh, 1, .dmaPcisAxi4, false⟩, ⟨"cl_sh_dma_pcis_rid", .clToSh, 16, .dmaPcisAxi4, false⟩
  , ⟨"cl_sh_dma_pcis_rdata", .clToSh, 512, .dmaPcisAxi4, false⟩, ⟨"cl_sh_dma_pcis_rresp", .clToSh, 2, .dmaPcisAxi4, false⟩, ⟨"cl_sh_dma_pcis_rlast", .clToSh, 1, .dmaPcisAxi4, false⟩
  , ⟨"cl_sh_dma_pcis_rvalid", .clToSh, 1, .dmaPcisAxi4, false⟩, ⟨"sh_cl_dma_pcis_rready", .shToCl, 1, .dmaPcisAxi4, false⟩, ⟨"cl_sh_dma_wr_full", .clToSh, 1, .dmaPcisAxi4, false⟩
  , ⟨"cl_sh_dma_rd_full", .clToSh, 1, .dmaPcisAxi4, false⟩, ⟨"cl_sh_pcim_awid", .clToSh, 16, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_awaddr", .clToSh, 64, .pcimAxi4, false⟩
  , ⟨"cl_sh_pcim_awlen", .clToSh, 8, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_awsize", .clToSh, 3, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_awvalid", .clToSh, 1, .pcimAxi4, false⟩
  , ⟨"sh_cl_pcim_awready", .shToCl, 1, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_wdata", .clToSh, 512, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_wstrb", .clToSh, 64, .pcimAxi4, false⟩
  , ⟨"cl_sh_pcim_wlast", .clToSh, 1, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_wvalid", .clToSh, 1, .pcimAxi4, false⟩, ⟨"sh_cl_pcim_wready", .shToCl, 1, .pcimAxi4, false⟩
  , ⟨"sh_cl_pcim_bid", .shToCl, 16, .pcimAxi4, false⟩, ⟨"sh_cl_pcim_bresp", .shToCl, 2, .pcimAxi4, false⟩, ⟨"sh_cl_pcim_bvalid", .shToCl, 1, .pcimAxi4, false⟩
  , ⟨"cl_sh_pcim_bready", .clToSh, 1, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_arid", .clToSh, 16, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_araddr", .clToSh, 64, .pcimAxi4, false⟩
  , ⟨"cl_sh_pcim_arlen", .clToSh, 8, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_arsize", .clToSh, 3, .pcimAxi4, false⟩, ⟨"cl_sh_pcim_arvalid", .clToSh, 1, .pcimAxi4, false⟩
  , ⟨"sh_cl_pcim_arready", .shToCl, 1, .pcimAxi4, false⟩, ⟨"sh_cl_pcim_rid", .shToCl, 16, .pcimAxi4, false⟩, ⟨"sh_cl_pcim_rdata", .shToCl, 512, .pcimAxi4, false⟩
  , ⟨"sh_cl_pcim_rresp", .shToCl, 2, .pcimAxi4, false⟩, ⟨"sh_cl_pcim_rlast", .shToCl, 1, .pcimAxi4, false⟩, ⟨"sh_cl_pcim_rvalid", .shToCl, 1, .pcimAxi4, false⟩
  , ⟨"cl_sh_pcim_rready", .clToSh, 1, .pcimAxi4, false⟩, ⟨"ocl_cl_awaddr", .shToCl, 32, .oclAxi4LiteBar0, false⟩, ⟨"ocl_cl_awvalid", .shToCl, 1, .oclAxi4LiteBar0, false⟩
  , ⟨"cl_ocl_awready", .clToSh, 1, .oclAxi4LiteBar0, false⟩, ⟨"ocl_cl_wdata", .shToCl, 32, .oclAxi4LiteBar0, false⟩, ⟨"ocl_cl_wstrb", .shToCl, 4, .oclAxi4LiteBar0, false⟩
  , ⟨"ocl_cl_wvalid", .shToCl, 1, .oclAxi4LiteBar0, false⟩, ⟨"cl_ocl_wready", .clToSh, 1, .oclAxi4LiteBar0, false⟩, ⟨"cl_ocl_bresp", .clToSh, 2, .oclAxi4LiteBar0, false⟩
  , ⟨"cl_ocl_bvalid", .clToSh, 1, .oclAxi4LiteBar0, false⟩, ⟨"ocl_cl_bready", .shToCl, 1, .oclAxi4LiteBar0, false⟩, ⟨"ocl_cl_araddr", .shToCl, 32, .oclAxi4LiteBar0, false⟩
  , ⟨"ocl_cl_arvalid", .shToCl, 1, .oclAxi4LiteBar0, false⟩, ⟨"cl_ocl_arready", .clToSh, 1, .oclAxi4LiteBar0, false⟩, ⟨"cl_ocl_rdata", .clToSh, 32, .oclAxi4LiteBar0, false⟩
  , ⟨"cl_ocl_rresp", .clToSh, 2, .oclAxi4LiteBar0, false⟩, ⟨"cl_ocl_rvalid", .clToSh, 1, .oclAxi4LiteBar0, false⟩, ⟨"ocl_cl_rready", .shToCl, 1, .oclAxi4LiteBar0, false⟩
  , ⟨"sda_cl_awaddr", .shToCl, 32, .sdaAxi4LiteBar4, false⟩, ⟨"sda_cl_awvalid", .shToCl, 1, .sdaAxi4LiteBar4, false⟩, ⟨"cl_sda_awready", .clToSh, 1, .sdaAxi4LiteBar4, false⟩
  , ⟨"sda_cl_wdata", .shToCl, 32, .sdaAxi4LiteBar4, false⟩, ⟨"sda_cl_wstrb", .shToCl, 4, .sdaAxi4LiteBar4, false⟩, ⟨"sda_cl_wvalid", .shToCl, 1, .sdaAxi4LiteBar4, false⟩
  , ⟨"cl_sda_wready", .clToSh, 1, .sdaAxi4LiteBar4, false⟩, ⟨"cl_sda_bresp", .clToSh, 2, .sdaAxi4LiteBar4, false⟩, ⟨"cl_sda_bvalid", .clToSh, 1, .sdaAxi4LiteBar4, false⟩
  , ⟨"sda_cl_bready", .shToCl, 1, .sdaAxi4LiteBar4, false⟩, ⟨"sda_cl_araddr", .shToCl, 32, .sdaAxi4LiteBar4, false⟩, ⟨"sda_cl_arvalid", .shToCl, 1, .sdaAxi4LiteBar4, false⟩
  , ⟨"cl_sda_arready", .clToSh, 1, .sdaAxi4LiteBar4, false⟩, ⟨"cl_sda_rdata", .clToSh, 32, .sdaAxi4LiteBar4, false⟩, ⟨"cl_sda_rresp", .clToSh, 2, .sdaAxi4LiteBar4, false⟩
  , ⟨"cl_sda_rvalid", .clToSh, 1, .sdaAxi4LiteBar4, false⟩, ⟨"sda_cl_rready", .shToCl, 1, .sdaAxi4LiteBar4, false⟩, ⟨"cl_sh_apppf_irq_req", .clToSh, 16, .appPfIrq, false⟩
  , ⟨"sh_cl_apppf_irq_ack", .shToCl, 16, .appPfIrq, false⟩, ⟨"cl_hbm_axi4_awaddr", .clToSh, 1088, .hbmAxi4, false⟩, ⟨"cl_hbm_axi4_wdata", .clToSh, 8192, .hbmAxi4, false⟩
  , ⟨"cl_hbm_axi4_rdata", .shToCl, 8192, .hbmAxi4, false⟩, ⟨"cl_hbm_axi4_ch_enable", .clToSh, 32, .hbmAxi4, false⟩, ⟨"hbm_apb_paddr_0", .clToSh, 22, .hbmApb, false⟩
  , ⟨"hbm_apb_pwdata_0", .clToSh, 32, .hbmApb, false⟩, ⟨"hbm_apb_prdata_0", .shToCl, 32, .hbmApb, false⟩, ⟨"hbm_apb_paddr_1", .clToSh, 22, .hbmApb, false⟩
  , ⟨"hbm_apb_pwdata_1", .clToSh, 32, .hbmApb, false⟩, ⟨"hbm_apb_prdata_1", .shToCl, 32, .hbmApb, false⟩, ⟨"cl_sh_hbm_stat_int", .clToSh, 8, .hbmApb, false⟩ ]
def isForbiddenFictionalOrIcapPort (portName : String) : Bool :=
  portName == "sh_pcis_h2c_tdata" || portName == "sh_pcis_h2c_tvalid" ||
  portName == "sh_pcis_h2c_tready" || portName == "cl_pcis_c2h_tdata" ||
  portName == "cl_pcis_c2h_tvalid" || portName == "sh_pcis_c2h_tready" ||
  portName == "icap_clk" || portName == "icap_csib" ||
  portName == "icap_rdwrb" || portName == "icap_i" || portName == "icap_o"
structure F2PortBinding where
  shellPortName : String
  clSignalName : String
  dir : F2PortDir
  width : Nat
  activeLow : Bool := false
  deriving DecidableEq, Repr
structure F2WrapperConfig where
  clModuleName : String
  targetDevice : String := awsF2TargetDevice
  rstActiveLow : Bool := true
  usesCustomerIcap : Bool := false
  hbmChannelsUsed : Nat := 32
  portBindings : List F2PortBinding
  deriving DecidableEq, Repr
def findAwsF2ShellPort? (nm : String) : List F2ShellPortSpec → Option F2ShellPortSpec
  | [] => none
  | p :: rest => if p.name == nm then some p else findAwsF2ShellPort? nm rest
private theorem findAwsF2ShellPort_mem {nm : String} {ports : List F2ShellPortSpec} {spec : F2ShellPortSpec}
    (hFind : findAwsF2ShellPort? nm ports = some spec) : spec ∈ ports ∧ spec.name = nm := by
  induction ports with
  | nil => cases hFind
  | cons p rest ih =>
    unfold findAwsF2ShellPort? at hFind; split at hFind
    · rename_i hEq; injection hFind with hSpec; subst hSpec
      exact ⟨List.Mem.head _, beq_iff_eq.mp hEq⟩
    · obtain ⟨hMem, hNm⟩ := ih hFind; exact ⟨List.Mem.tail _ hMem, hNm⟩
def checkSingleF2PortBinding (b : F2PortBinding) : Bool :=
  (!isForbiddenFictionalOrIcapPort b.shellPortName) &&
  match findAwsF2ShellPort? b.shellPortName canonicalAwsF2ClPorts with
  | none => false
  | some spec => (spec.dir == b.dir) && (spec.width == b.width) && (spec.activeLow == b.activeLow)
/-- Device, reset polarity, ICAP and HBM gates, every binding canonical in `cl_ports.vh`, and no shell port
or CL signal bound twice (a doubly bound shell port is a multi-driver net or an ambiguous tap). -/
@[expose] def validateF2WrapperPortBinding (cfg : F2WrapperConfig) : Bool :=
  (cfg.targetDevice == awsF2TargetDevice) && cfg.rstActiveLow && (!cfg.usesCustomerIcap) &&
  decide (cfg.hbmChannelsUsed ≤ 32) && (!cfg.portBindings.isEmpty) &&
  cfg.portBindings.all checkSingleF2PortBinding &&
  decide (cfg.portBindings.map (·.shellPortName)).Nodup && decide (cfg.portBindings.map (·.clSignalName)).Nodup
def defaultAwsF2WrapperConfig : F2WrapperConfig where
  clModuleName := "cl_obend_f2"
  portBindings :=
    [ { shellPortName := "clk_main_a0",           clSignalName := "clk",            dir := .shToCl, width := 1 }
    , { shellPortName := "rst_main_n",            clSignalName := "rst_n",          dir := .shToCl, width := 1, activeLow := true }
    , { shellPortName := "sh_cl_flr_assert",      clSignalName := "flr_in",         dir := .shToCl, width := 1 }
    , { shellPortName := "cl_sh_flr_done",        clSignalName := "flr_done",       dir := .clToSh, width := 1 }
    , { shellPortName := "sh_cl_dma_pcis_wdata",  clSignalName := "dma_pcis_wdata", dir := .shToCl, width := 512 }
    , { shellPortName := "cl_sh_dma_pcis_rdata",  clSignalName := "dma_pcis_rdata", dir := .clToSh, width := 512 }
    , { shellPortName := "sh_cl_dma_pcis_awaddr", clSignalName := "a",              dir := .shToCl, width := 64 }
    , { shellPortName := "sh_cl_dma_pcis_araddr", clSignalName := "b",              dir := .shToCl, width := 64 }
    , { shellPortName := "cl_sh_pcim_awaddr",     clSignalName := "y",              dir := .clToSh, width := 64 }
    , { shellPortName := "ocl_cl_awaddr",         clSignalName := "bar0_awaddr",    dir := .shToCl, width := 32 }
    , { shellPortName := "ocl_cl_wdata",          clSignalName := "bar0_wdata",     dir := .shToCl, width := 32 }
    , { shellPortName := "cl_ocl_rdata",          clSignalName := "bar0_rdata",     dir := .clToSh, width := 32 }
    , { shellPortName := "cl_hbm_axi4_ch_enable", clSignalName := "hbm_ch_en",      dir := .clToSh, width := 32 } ]
example : validateF2WrapperPortBinding defaultAwsF2WrapperConfig = true := by decide +kernel
theorem validateF2WrapperPortBinding_sound (cfg : F2WrapperConfig)
    (hValid : validateF2WrapperPortBinding cfg = true) :
    cfg.targetDevice = awsF2TargetDevice ∧ cfg.rstActiveLow = true ∧
    cfg.usesCustomerIcap = false ∧ cfg.hbmChannelsUsed ≤ 32 ∧ cfg.portBindings ≠ [] ∧
    (cfg.portBindings.map (·.shellPortName)).Nodup ∧ (cfg.portBindings.map (·.clSignalName)).Nodup ∧
    ∀ b ∈ cfg.portBindings,
      isForbiddenFictionalOrIcapPort b.shellPortName = false ∧
      ∃ spec ∈ canonicalAwsF2ClPorts,
        spec.name = b.shellPortName ∧ spec.dir = b.dir ∧
        spec.width = b.width ∧ spec.activeLow = b.activeLow := by
  simp only [validateF2WrapperPortBinding, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_true_eq, List.all_eq_true] at hValid
  rcases hValid with ⟨⟨⟨⟨⟨⟨⟨hDev, hRst⟩, hNoIcap⟩, hHbm⟩, hNonEmpty⟩, hAll⟩, hNdS⟩, hNdC⟩
  have hNeNil : cfg.portBindings ≠ [] := by intro hNil; rw [hNil] at hNonEmpty; cases hNonEmpty
  refine ⟨hDev, hRst, hNoIcap, hHbm, hNeNil, hNdS, hNdC, fun b hb => ?_⟩
  have hbOk := hAll b hb; unfold checkSingleF2PortBinding at hbOk
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hbOk
  rcases hbOk with ⟨hNotForb, hMatch⟩
  cases hFind : findAwsF2ShellPort? b.shellPortName canonicalAwsF2ClPorts with
  | none => rw [hFind] at hMatch; cases hMatch
  | some spec =>
    rw [hFind] at hMatch; simp only [Bool.and_eq_true, beq_iff_eq] at hMatch
    obtain ⟨hMem, hNm⟩ := findAwsF2ShellPort_mem hFind
    exact ⟨hNotForb, spec, hMem, hNm, hMatch.1.1, hMatch.1.2, hMatch.2⟩
theorem fictional_pcis_stream_port_refused (cfg : F2WrapperConfig) (clSig : String) (d : F2PortDir) (w : Nat) :
    validateF2WrapperPortBinding
      { cfg with portBindings := { shellPortName := "sh_pcis_h2c_tdata", clSignalName := clSig, dir := d, width := w } :: cfg.portBindings } = false ∧
    validateF2WrapperPortBinding { cfg with usesCustomerIcap := true } = false := by
  refine ⟨?_, ?_⟩
  · unfold validateF2WrapperPortBinding checkSingleF2PortBinding isForbiddenFictionalOrIcapPort; simp
  · unfold validateF2WrapperPortBinding; simp
/-- First binding of direction `d` whose CL-side signal is `nm`. -/
def findF2Binding? (d : F2PortDir) (nm : String) : List F2PortBinding → Option F2PortBinding
  | [] => none
  | b :: rest => if b.dir == d && b.clSignalName == nm then some b else findF2Binding? d nm rest
private theorem findF2Binding_mem {d : F2PortDir} {nm : String} {bs : List F2PortBinding} {b : F2PortBinding}
    (hFind : findF2Binding? d nm bs = some b) : b ∈ bs ∧ b.dir = d ∧ b.clSignalName = nm := by
  induction bs with
  | nil => cases hFind
  | cons p rest ih =>
    unfold findF2Binding? at hFind; split at hFind
    · rename_i hEq; injection hFind with hB; subst hB
      simp only [Bool.and_eq_true, beq_iff_eq] at hEq; exact ⟨List.Mem.head _, hEq.1, hEq.2⟩
    · obtain ⟨hMem, hRest⟩ := ih hFind; exact ⟨List.Mem.tail _ hMem, hRest⟩
/-- The shell port a core port `nm` of direction `d` is wired to (`validateF2CorePortBindings` makes it resolve). -/
def boundF2ShellPort (cfg : F2WrapperConfig) (d : F2PortDir) (nm : String) : String :=
  match findF2Binding? d nm cfg.portBindings with | some b => b.shellPortName | none => "/* unbound */"
/-- Core port `nm` (direction `d`, width `w`) has a binding of exactly that width; an output may not drive
`cl_sh_flr_done`, which the wrapper itself assigns. -/
def checkF2CorePort (cfg : F2WrapperConfig) (d : F2PortDir) (nm : String) (w : Nat) : Bool :=
  match findF2Binding? d nm cfg.portBindings with
  | some b => (b.width == w) && (d != .clToSh || b.shellPortName != "cl_sh_flr_done")
  | none => false
/-- A core's input ports as `(name, width)` in declaration order. -/
def coreInputPorts (m : RtlModule) : List (String × Nat) := m.inputNames.zipIdx.map fun p => (p.1, inputWidth m p.2)
theorem coreInputPorts_names (m : RtlModule) : (coreInputPorts m).map (·.1) = m.inputNames := by
  simp [coreInputPorts, List.map_map, Function.comp_def, List.zipIdx_map_fst]
/-- The wrapper validates, the core passes the emission gate `checkRtlModuleW` and has at most one clock domain
(the wrapper supplies `clk_main_a0` only), port names are distinct from each other and from `clk`/`rst`, and every
core input (output) has an `.shToCl` (`.clToSh`) binding of its exact width. -/
def validateF2CorePortBindings (cfg : F2WrapperConfig) (coreMod : RtlModule) : Bool :=
  validateF2WrapperPortBinding cfg && checkRtlModuleW coreMod && decide ((moduleDomains coreMod).length ≤ 1) &&
  decide ("clk" :: "rst" :: (coreMod.inputNames ++ coreMod.outputs.map (·.name))).Nodup &&
  (coreInputPorts coreMod).all (fun p => checkF2CorePort cfg .shToCl p.1 p.2) &&
  coreMod.outputs.all (fun o => checkF2CorePort cfg .clToSh o.name o.width)
example : validateF2CorePortBindings defaultAwsF2WrapperConfig
    { name := "core", inputNames := ["a", "b"], wires := [], regs := [], outputs := [{ name := "y", expr := .inputPort 0 }] } = true := by
  decide +kernel
private theorem checkF2CorePort_sound {cfg : F2WrapperConfig} {d : F2PortDir} {nm : String} {w : Nat}
    (h : checkF2CorePort cfg d nm w = true) :
    ∃ b ∈ cfg.portBindings, b.dir = d ∧ b.clSignalName = nm ∧ b.width = w ∧
      (d = .clToSh → b.shellPortName ≠ "cl_sh_flr_done") ∧ boundF2ShellPort cfg d nm = b.shellPortName := by
  unfold checkF2CorePort at h; unfold boundF2ShellPort
  cases hF : findF2Binding? d nm cfg.portBindings with
  | none => rw [hF] at h; cases h
  | some b =>
    rw [hF] at h; simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hM, hD, hN⟩ := findF2Binding_mem hF
    exact ⟨b, hM, hD, hN, h.1, fun hd hs => by simp [hd, hs] at h, rfl⟩
theorem validateF2CorePortBindings_sound (cfg : F2WrapperConfig) (coreMod : RtlModule)
    (hValid : validateF2CorePortBindings cfg coreMod = true) :
    validateF2WrapperPortBinding cfg = true ∧ checkRtlModuleW coreMod = true ∧ (moduleDomains coreMod).length ≤ 1 ∧
    ("clk" :: "rst" :: (coreMod.inputNames ++ coreMod.outputs.map (·.name))).Nodup ∧
    (∀ p ∈ coreInputPorts coreMod, ∃ b ∈ cfg.portBindings, b.dir = .shToCl ∧ b.clSignalName = p.1 ∧
      b.width = p.2 ∧ boundF2ShellPort cfg .shToCl p.1 = b.shellPortName) ∧
    (∀ o ∈ coreMod.outputs, ∃ b ∈ cfg.portBindings, b.dir = .clToSh ∧ b.clSignalName = o.name ∧
      b.width = o.width ∧ b.shellPortName ≠ "cl_sh_flr_done" ∧ boundF2ShellPort cfg .clToSh o.name = b.shellPortName) := by
  simp only [validateF2CorePortBindings, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hValid
  rcases hValid with ⟨⟨⟨⟨⟨hW, hRtl⟩, hDom⟩, hNd⟩, hIn⟩, hOut⟩
  refine ⟨hW, hRtl, hDom, hNd, fun p hp => ?_, fun o ho => ?_⟩
  · obtain ⟨b, hM, hD, hN, hWd, _, hB⟩ := checkF2CorePort_sound (hIn p hp); exact ⟨b, hM, hD, hN, hWd, hB⟩
  · obtain ⟨b, hM, hD, hN, hWd, hFlr, hB⟩ := checkF2CorePort_sound (hOut o ho); exact ⟨b, hM, hD, hN, hWd, hFlr rfl, hB⟩
/-- Named port connections of the `u_core` instance: `clk`/`rst` (the single-domain ports `emitModuleSV` emits),
then every core input and output tied to its bound shell port. -/
def f2CoreConnections (cfg : F2WrapperConfig) (coreMod : RtlModule) : List String :=
  ["    .clk(clk_main_a0)", "    .rst(rst_core_sync)"] ++
  (coreInputPorts coreMod).map (fun p => "    ." ++ p.1 ++ "(" ++ boundF2ShellPort cfg .shToCl p.1 ++ ")") ++
  coreMod.outputs.map (fun o => "    ." ++ o.name ++ "(" ++ boundF2ShellPort cfg .clToSh o.name ++ ")")
/-- The core module's SystemVerilog, then the CL wrapper module instantiating it as `u_core` on the shell ports. -/
def emitAwsF2ClWrapperSV (cfg : F2WrapperConfig) (coreMod : RtlModule) : Option String :=
  if validateF2CorePortBindings cfg coreMod then
    some (emitModuleSV coreMod ++ ("\n// Verified AWS EC2 F2 Custom Logic Shell Wrapper (" ++ cfg.targetDevice ++ ")\n" ++
      ("module " ++ cfg.clModuleName ++ " (\n  `include \"cl_ports.vh\"\n);\n" ++
       "  wire rst_core_sync = ~rst_main_n;\n  assign cl_sh_flr_done = sh_cl_flr_assert;\n" ++
       "  " ++ coreMod.name ++ " u_core (\n" ++ String.intercalate ",\n" (f2CoreConnections cfg coreMod) ++ "\n  );\n" ++
       "endmodule\n")))
  else none
/-- **The emitted wrapper instantiates the wired core.** An emitted text is the core module followed by the CL
module, whose body before `endmodule` is the `u_core` instance; every core input and output is connected, by name,
to a canonical `cl_ports.vh` shell port of the same direction and width. -/
theorem emitAwsF2ClWrapperSV_instantiates_wired_core (cfg : F2WrapperConfig) (coreMod : RtlModule) (sv : String)
    (hEmit : emitAwsF2ClWrapperSV cfg coreMod = some sv) :
    validateF2CorePortBindings cfg coreMod = true ∧
    (∃ glue : String, sv = emitModuleSV coreMod ++ (glue ++
      ("module " ++ cfg.clModuleName ++ " (\n  `include \"cl_ports.vh\"\n);\n" ++
       "  wire rst_core_sync = ~rst_main_n;\n  assign cl_sh_flr_done = sh_cl_flr_assert;\n" ++
       "  " ++ coreMod.name ++ " u_core (\n" ++ String.intercalate ",\n" (f2CoreConnections cfg coreMod) ++ "\n  );\n" ++
       "endmodule\n"))) ∧
    (∀ p ∈ coreInputPorts coreMod, ∃ b ∈ cfg.portBindings, ∃ spec ∈ canonicalAwsF2ClPorts,
      spec.name = b.shellPortName ∧ spec.dir = .shToCl ∧ spec.width = p.2 ∧ b.clSignalName = p.1 ∧
      ("    ." ++ p.1 ++ "(" ++ b.shellPortName ++ ")") ∈ f2CoreConnections cfg coreMod) ∧
    (∀ o ∈ coreMod.outputs, ∃ b ∈ cfg.portBindings, ∃ spec ∈ canonicalAwsF2ClPorts,
      spec.name = b.shellPortName ∧ spec.dir = .clToSh ∧ spec.width = o.width ∧ b.clSignalName = o.name ∧
      ("    ." ++ o.name ++ "(" ++ b.shellPortName ++ ")") ∈ f2CoreConnections cfg coreMod) := by
  unfold emitAwsF2ClWrapperSV at hEmit
  split at hEmit
  · rename_i hV; injection hEmit with hSv; subst hSv
    obtain ⟨hW, _, _, _, hIn, hOut⟩ := validateF2CorePortBindings_sound cfg coreMod hV
    have hCanon := (validateF2WrapperPortBinding_sound cfg hW).2.2.2.2.2.2.2
    refine ⟨hV, ⟨_, rfl⟩, fun p hp => ?_, fun o ho => ?_⟩
    · obtain ⟨b, hM, hD, hN, hWd, hB⟩ := hIn p hp
      obtain ⟨_, spec, hS, hSn, hSd, hSw, _⟩ := hCanon b hM
      refine ⟨b, hM, spec, hS, hSn, hSd.trans hD, hSw.trans hWd, hN, ?_⟩
      rw [← hB]; unfold f2CoreConnections
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    · obtain ⟨b, hM, hD, hN, hWd, _, hB⟩ := hOut o ho
      obtain ⟨_, spec, hS, hSn, hSd, hSw, _⟩ := hCanon b hM
      refine ⟨b, hM, spec, hS, hSn, hSd.trans hD, hSw.trans hWd, hN, ?_⟩
      rw [← hB]; unfold f2CoreConnections
      exact List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩)
  · cases hEmit

/-! ## 2. Embedded `FABulous` eFPGA PCIe BAR0 Hot-Swap Controller (`f2FabulousOverlayStep`) -/
def packU64LE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, v => UInt8.ofNat (v % 256) :: packU64LE k (v / 256)
def unpackU64LE : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * unpackU64LE rest
def packU64Bytes (v : Nat) : List UInt8 := packU64LE 8 v
private theorem unpackU64LE_packU64LE : ∀ (k v : Nat), v < 256 ^ k → unpackU64LE (packU64LE k v) = v
  | 0, v, hv => by simp [Nat.pow_zero] at hv; subst hv; rfl
  | k + 1, v, hv => by
    have hpow : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ ..
    have hq : v / 256 < 256 ^ k := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ hv)
    have ih := unpackU64LE_packU64LE k (v / 256) hq
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    simp only [packU64LE, unpackU64LE, UInt8.toNat_ofNat', h8, ih]
    omega
private theorem packU64LE_length : ∀ (k v : Nat), (packU64LE k v).length = k
  | 0, _ => rfl
  | k + 1, v => by simp [packU64LE, packU64LE_length k]
private theorem packU64Bytes_length (v : Nat) : (packU64Bytes v).length = 8 := packU64LE_length 8 v
private theorem packU64Bytes_injective {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hEq : packU64Bytes a = packU64Bytes b) : a = b := by
  have hPow : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have h := congrArg unpackU64LE hEq
  rwa [packU64Bytes, packU64Bytes, unpackU64LE_packU64LE 8 a (hPow ▸ ha),
       unpackU64LE_packU64LE 8 b (hPow ▸ hb)] at h
def serializeTileFrameListBytes : List TileFrame → List UInt8
  | [] => []
  | f :: rest => packU64Bytes f.payload.toNat ++ packU64Bytes f.crc.toNat ++ serializeTileFrameListBytes rest
private theorem list_append_eq_of_len_eq {α : Type} {l₁ l₂ r₁ r₂ : List α}
    (hLen : l₁.length = l₂.length) (hEq : l₁ ++ r₁ = l₂ ++ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ with | nil => exact ⟨rfl, hEq⟩ | cons _ _ => simp at hLen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hLen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
      simp only [List.cons_append, List.cons.injEq] at hEq
      obtain ⟨hxs, hrs⟩ := ih hLen hEq.2
      rw [hEq.1, hxs]; exact ⟨rfl, hrs⟩
private theorem serializeTileFrameListBytes_injective :
    ∀ (xs ys : List TileFrame),
      xs.length = ys.length → serializeTileFrameListBytes xs = serializeTileFrameListBytes ys → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, hLen, _ => by simp at hLen
  | _ :: _, [], hLen, _ => by simp at hLen
  | x :: xs, y :: ys, hLen, hBytes => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    dsimp only [serializeTileFrameListBytes] at hBytes
    rw [List.append_assoc, List.append_assoc] at hBytes
    obtain ⟨hPayEq, hRest1⟩ := list_append_eq_of_len_eq (by rw [packU64Bytes_length, packU64Bytes_length]) hBytes
    obtain ⟨hCrcEq, hTail⟩ := list_append_eq_of_len_eq (by rw [packU64Bytes_length, packU64Bytes_length]) hRest1
    have hp : x.payload = y.payload := BitVec.eq_of_toNat_eq (packU64Bytes_injective x.payload.isLt y.payload.isLt hPayEq)
    have hc : x.crc = y.crc := BitVec.eq_of_toNat_eq (packU64Bytes_injective x.crc.isLt y.crc.isLt hCrcEq)
    have hxy : x = y := by cases x; cases y; simp_all
    rw [hxy, serializeTileFrameListBytes_injective xs ys hLen hTail]
def serializeTileFramesBytes (frames : Array TileFrame) : List UInt8 :=
  packU64Bytes frames.size ++ serializeTileFrameListBytes frames.toList
example : (#[] : Array TileFrame).size < 2 ^ 64 := by decide
theorem serializeTileFramesBytes_injective {f₁ f₂ : Array TileFrame}
    (h1 : f₁.size < 2 ^ 64) (h2 : f₂.size < 2 ^ 64)
    (hEq : serializeTileFramesBytes f₁ = serializeTileFramesBytes f₂) : f₁ = f₂ := by
  unfold serializeTileFramesBytes at hEq
  obtain ⟨hSzBytes, hBody⟩ := list_append_eq_of_len_eq (by rw [packU64Bytes_length, packU64Bytes_length]) hEq
  have hSz : f₁.size = f₂.size := packU64Bytes_injective h1 h2 hSzBytes
  exact Array.ext' (serializeTileFrameListBytes_injective f₁.toList f₂.toList (by simpa using hSz) hBody)
def digestTileFrames256 (H : Obend.Digest.HashBytes.Hash) (frames : Array TileFrame) : BitVec 256 :=
  BitVec.ofNat 256 (Obend.Digest.HashBytes.ofBE (H (serializeTileFramesBytes frames)))
/-- **256-Bit Bitstream Digest Commitment Binding (`serializeTileFramesBytes_binding`, `0 Classical`)**. -/
theorem serializeTileFramesBytes_binding
    (H : Obend.Digest.HashBytes.Hash) (f₁ f₂ : Array TileFrame)
    (h1 : f₁.size < 2 ^ 64) (h2 : f₂.size < 2 ^ 64)
    (hW1 : Obend.Digest.HashBytes.ofBE (H (serializeTileFramesBytes f₁)) < 2 ^ 256)
    (hW2 : Obend.Digest.HashBytes.ofBE (H (serializeTileFramesBytes f₂)) < 2 ^ 256)
    (hDig : digestTileFrames256 H f₁ = digestTileFrames256 H f₂) :
    f₁ = f₂ ∨ Obend.Digest.HashBytes.Collision H := by
  if hSame : f₁ = f₂ then exact Or.inl hSame
  else
    right
    have hBytesNe : serializeTileFramesBytes f₁ ≠ serializeTileFramesBytes f₂ :=
      fun hBytesEq => hSame (serializeTileFramesBytes_injective h1 h2 hBytesEq)
    have hToNat := congrArg BitVec.toNat hDig
    simp only [digestTileFrames256, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW1, Nat.mod_eq_of_lt hW2] at hToNat
    exact ⟨serializeTileFramesBytes f₁, serializeTileFramesBytes f₂, hBytesNe, hToNat⟩
inductive F2OverlayPhase where | active | frozenIsolated | quarantined deriving DecidableEq, Repr, Inhabited
structure F2FabulousOverlayState where
  fabric : DprFabric
  overlayPhase : F2OverlayPhase
  stagedFrames : Array TileFrame
  expectedDigest256 : BitVec 256
  bar0CyclesSpent : Nat
  deriving DecidableEq, Repr, Inhabited
inductive F2Bar0Action where
  | rstMainLow
  | bar0FreezeIsolate
  | bar0WriteExpectedDigest (dig : BitVec 256)
  | bar0StreamFrames (frames : Array TileFrame)
  | bar0AuthenticateCommit
  | datapathCompute
  deriving DecidableEq, Repr
def bar0HotSwapCycles (numTiles : Nat) : Nat := 4 + 32 + 32 * numTiles + 8
@[expose] def bar0HotSwapLatencyNs (numTiles : Nat) : Nat := 4 * bar0HotSwapCycles numTiles
/-- Step the embedded `FABulous` eFPGA BAR0 hot-swap controller by one transaction / clock edge. -/
@[expose] def f2FabulousOverlayStep
    (H : Obend.Digest.HashBytes.Hash) (st : F2FabulousOverlayState) (act : F2Bar0Action) :
    F2FabulousOverlayState :=
  let nextNeighbors := tickNeighbors st.fabric.inputs (observedBoundaryPort st.fabric) st.fabric.neighbors
  match act with
  | .rstMainLow =>
    let clamped := if st.fabric.phase = .active then observedBoundaryPort st.fabric else st.fabric.clampedOut
    { fabric := { st.fabric with
        phase := .isolateClamped, clampedOut := clamped, pending := none,
        targetRegs := st.fabric.targetRegs.map (fun _ => false), neighbors := nextNeighbors }
    , overlayPhase := .frozenIsolated, stagedFrames := #[], expectedDigest256 := 0#256, bar0CyclesSpent := 0 }
  | .bar0FreezeIsolate =>
    let fab1 := administer st.fabric .isolateClamped
    { st with fabric := { fab1 with neighbors := nextNeighbors },
              overlayPhase := .frozenIsolated, stagedFrames := #[], bar0CyclesSpent := 4 }
  | .bar0WriteExpectedDigest dig =>
    if st.fabric.phase = .active then
      { st with fabric := { st.fabric with neighbors := nextNeighbors } }
    else
      { st with fabric := { st.fabric with neighbors := nextNeighbors },
                expectedDigest256 := dig, bar0CyclesSpent := st.bar0CyclesSpent + 32 }
  | .bar0StreamFrames frames =>
    if st.fabric.phase = .active then
      { st with fabric := { st.fabric with neighbors := nextNeighbors } }
    else
      let fab1 := administer st.fabric (.loadFrames frames)
      { st with fabric := { fab1 with neighbors := nextNeighbors },
                stagedFrames := frames, bar0CyclesSpent := st.bar0CyclesSpent + 32 * frames.size }
  | .bar0AuthenticateCommit =>
    if st.fabric.phase = .active then
      { st with fabric := { st.fabric with neighbors := nextNeighbors } }
    else if digestTileFrames256 H st.stagedFrames == st.expectedDigest256 then
      match decodeTileFrames st.fabric.activeTiles.size st.stagedFrames with
      | some decoded =>
        let fabOk : DprFabric :=
          { st.fabric with
            phase := .active, activeTiles := decoded, sram := st.stagedFrames,
            pending := none, neighbors := nextNeighbors }
        { st with fabric := fabOk, overlayPhase := .active, bar0CyclesSpent := st.bar0CyclesSpent + 8 }
      | none =>
        let fabQuar : DprFabric :=
          { st.fabric with phase := .isolateClamped, pending := none, neighbors := nextNeighbors }
        { st with fabric := fabQuar, overlayPhase := .quarantined, bar0CyclesSpent := st.bar0CyclesSpent + 8 }
    else
      let fabQuar : DprFabric :=
        { st.fabric with phase := .isolateClamped, pending := none, neighbors := nextNeighbors }
      { st with fabric := fabQuar, overlayPhase := .quarantined, bar0CyclesSpent := st.bar0CyclesSpent + 8 }
  | .datapathCompute =>
    let fab1 := administer st.fabric .compute
    { st with fabric := { fab1 with neighbors := nextNeighbors } }
def runF2Bar0Schedule (H : Obend.Digest.HashBytes.Hash) (st : F2FabulousOverlayState) :
    List F2Bar0Action → F2FabulousOverlayState
  | [] => st
  | a :: rest => runF2Bar0Schedule H (f2FabulousOverlayStep H st a) rest
structure F2OverlayEvent where
  action : F2Bar0Action
  inputs : Array Bool
  boundary : Bool
def f2OverlayStepSys (H : Obend.Digest.HashBytes.Hash) :
    StepSystem F2FabulousOverlayState F2OverlayEvent NeighborState where
  observe s := s.fabric.neighbors
  step s ev s' :=
    ev.inputs = s.fabric.inputs ∧ ev.boundary = observedBoundaryPort s.fabric ∧
    s' = f2FabulousOverlayStep H s ev.action
def f2NeighborStepSys : StepSystem NeighborState F2OverlayEvent NeighborState where
  observe := id
  step n ev n' := n' = tickNeighbors ev.inputs ev.boundary n
private theorem observedBoundaryPort_of_ne_active (s : DprFabric) (h : s.phase ≠ .active) :
    observedBoundaryPort s = s.clampedOut := by
  have hEq : ({ s with sram := s.sram } : DprFabric) = s := by cases s; rfl
  have h1 := (clampedPortStable s s.sram h).1
  rwa [hEq] at h1
private theorem f2FabulousOverlayStep_neighbors
    (H : Obend.Digest.HashBytes.Hash) (st : F2FabulousOverlayState) (act : F2Bar0Action) :
    (f2FabulousOverlayStep H st act).fabric.neighbors =
      tickNeighbors st.fabric.inputs (observedBoundaryPort st.fabric) st.fabric.neighbors := by
  cases act <;> unfold f2FabulousOverlayStep <;> dsimp only
  all_goals repeat (first | rfl | split)
def F2OverlayIsolationInv (st : F2FabulousOverlayState) : Prop :=
  st.overlayPhase ≠ .active →
    st.fabric.phase ≠ .active ∧ observedBoundaryPort st.fabric = st.fabric.clampedOut
example : F2OverlayIsolationInv (default : F2FabulousOverlayState) := fun h => absurd rfl h
theorem f2FabulousOverlayStep_preserves_isolationInv
    (H : Obend.Digest.HashBytes.Hash) (st : F2FabulousOverlayState) (act : F2Bar0Action)
    (hInv : F2OverlayIsolationInv st) :
    F2OverlayIsolationInv (f2FabulousOverlayStep H st act) := by
  unfold F2OverlayIsolationInv at hInv ⊢
  cases act with
  | rstMainLow =>
    intro _; unfold f2FabulousOverlayStep; dsimp only
    exact ⟨by simp, observedBoundaryPort_of_ne_active _ (by simp)⟩
  | bar0FreezeIsolate =>
    intro _; unfold f2FabulousOverlayStep administer; dsimp only
    split
    · exact ⟨by simp, observedBoundaryPort_of_ne_active _ (by simp)⟩
    · rename_i hNotAct; exact ⟨hNotAct, observedBoundaryPort_of_ne_active _ hNotAct⟩
  | bar0WriteExpectedDigest dig =>
    unfold f2FabulousOverlayStep; dsimp only
    split
    · rename_i hAct; intro hOv; exact absurd hAct (hInv hOv).1
    · rename_i hNotAct; intro _; exact ⟨hNotAct, observedBoundaryPort_of_ne_active _ hNotAct⟩
  | bar0StreamFrames frames =>
    unfold f2FabulousOverlayStep administer; dsimp only
    split
    · rename_i hAct; intro hOv; exact absurd hAct (hInv hOv).1
    · split
      · intro _; exact ⟨by simp, observedBoundaryPort_of_ne_active _ (by simp)⟩
      · intro _; exact ⟨by simp, observedBoundaryPort_of_ne_active _ (by simp)⟩
  | bar0AuthenticateCommit =>
    unfold f2FabulousOverlayStep; dsimp only
    split
    · rename_i hAct; intro hOv; exact absurd hAct (hInv hOv).1
    · split
      · split
        · intro hOv; exact absurd rfl hOv
        · intro _; exact ⟨by simp, observedBoundaryPort_of_ne_active _ (by simp)⟩
      · intro _; exact ⟨by simp, observedBoundaryPort_of_ne_active _ (by simp)⟩
  | datapathCompute =>
    unfold f2FabulousOverlayStep administer; dsimp only
    split
    · rename_i hAct; intro hOv; exact absurd hAct (hInv hOv).1
    · rename_i hNotAct; intro _; exact ⟨hNotAct, observedBoundaryPort_of_ne_active _ hNotAct⟩
/-- **Multi-Turn Arbitrary-Trace Safety (`f2OverlayTrace_sound`)**. -/
theorem f2OverlayTrace_sound
    (H : Obend.Digest.HashBytes.Hash) {s₀ sₙ : F2FabulousOverlayState} {trace : List F2OverlayEvent}
    (hTrace : StepTrace (f2OverlayStepSys H) s₀ trace sₙ) (hInitInv : F2OverlayIsolationInv s₀) :
    StepTrace f2NeighborStepSys s₀.fabric.neighbors trace sₙ.fabric.neighbors ∧
    F2OverlayIsolationInv sₙ := by
  induction hTrace with
  | nil s => exact ⟨.nil _, hInitInv⟩
  | @cons s₁ s₂ s₃ ev rest hStep _ ih =>
    rcases hStep with ⟨hIn, hBnd, rfl⟩
    obtain ⟨hNeighborRest, hFinalInv⟩ := ih (f2FabulousOverlayStep_preserves_isolationInv H s₁ ev.action hInitInv)
    refine ⟨StepTrace.cons (s₂ := (f2FabulousOverlayStep H s₁ ev.action).fabric.neighbors) ?_ hNeighborRest, hFinalInv⟩
    change (f2FabulousOverlayStep H s₁ ev.action).fabric.neighbors = tickNeighbors ev.inputs ev.boundary s₁.fabric.neighbors
    rw [hIn, hBnd]; exact f2FabulousOverlayStep_neighbors H s₁ ev.action
example (H : Obend.Digest.HashBytes.Hash) :
    let s₀ : F2FabulousOverlayState := default
    let ev : F2OverlayEvent := { action := .bar0FreezeIsolate, inputs := s₀.fabric.inputs, boundary := observedBoundaryPort s₀.fabric }
    StepTrace (f2OverlayStepSys H) s₀ [ev] (f2FabulousOverlayStep H s₀ .bar0FreezeIsolate) ∧ F2OverlayIsolationInv s₀ :=
  ⟨.cons ⟨rfl, rfl, rfl⟩ (.nil _), fun h => absurd rfl h⟩
/-- **Master PCIe BAR0 `FABulous` Hot-Swap Theorem (`f2_pcie_fabulous_hotswap_stutter_safe`)**. -/
theorem f2_pcie_fabulous_hotswap_stutter_safe (H : Obend.Digest.HashBytes.Hash) :
    StutterSimulates f2NeighborStepSys (f2OverlayStepSys H)
      (fun n s => n = s.fabric.neighbors) 1 (0 : Nat) ∧
    (∀ numTiles : Nat, numTiles ≤ 380 → bar0HotSwapLatencyNs numTiles < 50000) ∧
    (∀ (st : F2FabulousOverlayState) (newTiles : Array TechmappedTile) (inp regs : Array Bool),
      st.fabric.phase = .active →
      newTiles.size = st.fabric.activeTiles.size →
      let frames := encodeTileFrames newTiles
      let dig := digestTileFrames256 H frames
      let swapped := runF2Bar0Schedule H st
        [.bar0FreezeIsolate, .bar0WriteExpectedDigest dig, .bar0StreamFrames frames, .bar0AuthenticateCommit]
      swapped.overlayPhase = .active ∧
      swapped.fabric.phase = .active ∧
      swapped.fabric.activeTiles = newTiles ∧
      swapped.bar0CyclesSpent = bar0HotSwapCycles newTiles.size ∧
      (∀ spec : TechmappedFabric, verifyDecodedAgainstTechmap newTiles spec = true →
        (evalDecodedFabric swapped.fabric.activeTiles inp regs).toList =
          evalTechmappedSpec spec inp regs)) ∧
    (∀ (st : F2FabulousOverlayState) (frames : Array TileFrame) (badDig : BitVec 256),
      st.fabric.phase = .active →
      (digestTileFrames256 H frames ≠ badDig ∨ decodeTileFrames st.fabric.activeTiles.size frames = none) →
      let rejected := runF2Bar0Schedule H st
        [.bar0FreezeIsolate, .bar0WriteExpectedDigest badDig, .bar0StreamFrames frames, .bar0AuthenticateCommit]
      rejected.overlayPhase = .quarantined ∧
      rejected.fabric.phase = .isolateClamped ∧
      rejected.fabric.activeTiles = st.fabric.activeTiles ∧
      observedBoundaryPort rejected.fabric = rejected.fabric.clampedOut) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, ?_, ?_⟩
    · intro n s hEq; subst hEq; exact ObsMetric.dist_self _
    · rintro n s s' ev rfl ⟨hIn, hBnd, rfl⟩
      refine ⟨1, (f2FabulousOverlayStep H s ev.action).fabric.neighbors, by decide, by decide, .succ ?_ (.zero _), rfl⟩
      change (f2FabulousOverlayStep H s ev.action).fabric.neighbors = tickNeighbors ev.inputs ev.boundary s.fabric.neighbors
      rw [hIn, hBnd]; exact f2FabulousOverlayStep_neighbors H s ev.action
  · intro numTiles hLe; dsimp [bar0HotSwapLatencyNs, bar0HotSwapCycles]; omega
  · intro st newTiles inp regs hAct hSz; dsimp only
    let frames := encodeTileFrames newTiles
    let dig := digestTileFrames256 H frames
    have hDec : decodeTileFrames st.fabric.activeTiles.size frames = some newTiles := by
      rw [← hSz]; exact decodeTileFrames_encodeTileFrames newTiles
    have hStreamSz : frames.size = newTiles.size := by simp [frames, encodeTileFrames]
    let s1 := f2FabulousOverlayStep H st .bar0FreezeIsolate
    have hs1 : s1.fabric.phase = .isolateClamped ∧ s1.fabric.activeTiles = st.fabric.activeTiles ∧
        s1.bar0CyclesSpent = 4 := by simp [s1, f2FabulousOverlayStep, administer, hAct]
    let s2 := f2FabulousOverlayStep H s1 (.bar0WriteExpectedDigest dig)
    have hs2 : s2.fabric.phase = .isolateClamped ∧ s2.fabric.activeTiles = st.fabric.activeTiles ∧
        s2.expectedDigest256 = dig ∧ s2.bar0CyclesSpent = 4 + 32 := by
      simp [s2, f2FabulousOverlayStep, hs1.1, hs1.2.1, hs1.2.2]
    let s3 := f2FabulousOverlayStep H s2 (.bar0StreamFrames frames)
    have hs3 : s3.fabric.phase = .loadFrames ∧ s3.fabric.activeTiles = st.fabric.activeTiles ∧
        s3.stagedFrames = frames ∧ s3.expectedDigest256 = dig ∧
        s3.bar0CyclesSpent = 4 + 32 + 32 * newTiles.size := by
      simp [s3, f2FabulousOverlayStep, administer, hs2.1, hs2.2.1, hs2.2.2.1, hs2.2.2.2, hDec, hStreamSz]
    let s4 := f2FabulousOverlayStep H s3 .bar0AuthenticateCommit
    have hRun : runF2Bar0Schedule H st
        [.bar0FreezeIsolate, .bar0WriteExpectedDigest dig, .bar0StreamFrames frames, .bar0AuthenticateCommit] = s4 := rfl
    rw [hRun]
    have hs4 : s4.overlayPhase = .active ∧ s4.fabric.phase = .active ∧
        s4.fabric.activeTiles = newTiles ∧ s4.bar0CyclesSpent = bar0HotSwapCycles newTiles.size := by
      simp [s4, f2FabulousOverlayStep, hs3.1, hs3.2.1, hs3.2.2.1, hs3.2.2.2.1, hs3.2.2.2.2,
        dig, hDec, bar0HotSwapCycles]
    rw [hs4.1, hs4.2.1, hs4.2.2.1, hs4.2.2.2]
    refine ⟨rfl, rfl, rfl, rfl, fun spec hv => ?_⟩
    exact (evalDecodedFabric_eq_techmapped newTiles.size frames newTiles spec inp regs
      (decodeTileFrames_encodeTileFrames newTiles) hv).2
  · intro st frames badDig hAct hBad; dsimp only
    let s1 := f2FabulousOverlayStep H st .bar0FreezeIsolate
    have hs1 : s1.fabric.phase = .isolateClamped ∧ s1.fabric.activeTiles = st.fabric.activeTiles := by
      simp [s1, f2FabulousOverlayStep, administer, hAct]
    let s2 := f2FabulousOverlayStep H s1 (.bar0WriteExpectedDigest badDig)
    have hs2 : s2.fabric.phase = .isolateClamped ∧ s2.fabric.activeTiles = st.fabric.activeTiles ∧
        s2.expectedDigest256 = badDig := by simp [s2, f2FabulousOverlayStep, hs1.1, hs1.2]
    let s3 := f2FabulousOverlayStep H s2 (.bar0StreamFrames frames)
    have hs3 : s3.fabric.phase ≠ .active ∧ s3.fabric.activeTiles = st.fabric.activeTiles ∧
        s3.stagedFrames = frames ∧ s3.expectedDigest256 = badDig := by
      simp only [s3, f2FabulousOverlayStep, administer, hs2.1, hs2.2.1, hs2.2.2, reduceCtorEq, ↓reduceIte]
      cases decodeTileFrames st.fabric.activeTiles.size frames <;> simp
    let s4 := f2FabulousOverlayStep H s3 .bar0AuthenticateCommit
    have hRun : runF2Bar0Schedule H st
        [.bar0FreezeIsolate, .bar0WriteExpectedDigest badDig, .bar0StreamFrames frames, .bar0AuthenticateCommit] = s4 := rfl
    rw [hRun]
    have hs4 : s4.overlayPhase = .quarantined ∧ s4.fabric.phase = .isolateClamped ∧
        s4.fabric.activeTiles = st.fabric.activeTiles := by
      unfold s4 f2FabulousOverlayStep; dsimp only
      simp only [hs3.1, ↓reduceIte, hs3.2.1, hs3.2.2.1, hs3.2.2.2]
      rcases hBad with hNeDig | hNone
      · simp [beq_eq_false_iff_ne.mpr hNeDig]
      · rw [hNone]; split <;> exact ⟨rfl, rfl, rfl⟩
    exact ⟨hs4.1, hs4.2.1, hs4.2.2,
           observedBoundaryPort_of_ne_active s4.fabric (by rw [hs4.2.1]; simp)⟩

/-! ## 3. Pre-Placed UltraScale+ / RapidWright Locked Macro & `XDC` Emitter -/
inductive Vu47pSiteKind where | sliceL | dsp48e2 | uram288 deriving DecidableEq, Repr
def Vu47pSiteKind.prefixStr : Vu47pSiteKind → String
  | .sliceL => "SLICE" | .dsp48e2 => "DSP48E2" | .uram288 => "URAM288"
inductive UltraScaleBelPin where
  | lut6 (slot : Fin 8) | ff (slot : Fin 8) | dspAlu | uramBase
  deriving DecidableEq, Repr
def slotChar (s : Fin 8) : Char :=
  match s.val with
  | 0 => 'A' | 1 => 'B' | 2 => 'C' | 3 => 'D'
  | 4 => 'E' | 5 => 'F' | 6 => 'G' | _ => 'H'
def UltraScaleBelPin.toBelName : UltraScaleBelPin → String
  | .lut6 s => String.ofList [slotChar s, '6', 'L', 'U', 'T']
  | .ff s => String.ofList [slotChar s, 'F', 'F']
  | .dspAlu => "DSP_ALU"
  | .uramBase => "URAM288_BASE"
private theorem slotChar_injective {s₁ s₂ : Fin 8} (h : slotChar s₁ = slotChar s₂) : s₁ = s₂ := by
  rcases s₁ with ⟨v₁, hv₁⟩; rcases s₂ with ⟨v₂, hv₂⟩
  have h1 : v₁ = 0 ∨ v₁ = 1 ∨ v₁ = 2 ∨ v₁ = 3 ∨ v₁ = 4 ∨ v₁ = 5 ∨ v₁ = 6 ∨ v₁ = 7 := by omega
  have h2 : v₂ = 0 ∨ v₂ = 1 ∨ v₂ = 2 ∨ v₂ = 3 ∨ v₂ = 4 ∨ v₂ = 5 ∨ v₂ = 6 ∨ v₂ = 7 := by omega
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | cases h
theorem UltraScaleBelPin.toBelName_injective {p₁ p₂ : UltraScaleBelPin}
    (h : p₁.toBelName = p₂.toBelName) : p₁ = p₂ := by
  have hL := congrArg String.toList h
  cases p₁ <;> cases p₂ <;> simp [UltraScaleBelPin.toBelName] at hL <;> try rfl
  · exact congrArg UltraScaleBelPin.lut6 (slotChar_injective hL)
  · exact congrArg UltraScaleBelPin.ff (slotChar_injective hL)
def slrOfTileY (tileY : Nat) : SlrId :=
  if tileY < 86 then .slr0 else if tileY < 172 then .slr1 else .slr2
structure RapidWrightCellPlacement where
  cellId : Nat
  cellName : String
  slr : SlrId
  siteKind : Vu47pSiteKind
  siteX : Nat
  siteY : Nat
  belPin : UltraScaleBelPin
  lutInit : Nat
  isLocFixed : Bool := true
  isBelFixed : Bool := true
  deriving DecidableEq, Repr
def RapidWrightCellPlacement.siteName (p : RapidWrightCellPlacement) : String :=
  p.siteKind.prefixStr ++ "_X" ++ toString p.siteX ++ "Y" ++ toString p.siteY
def RapidWrightCellPlacement.belName (p : RapidWrightCellPlacement) : String := p.belPin.toBelName
def RapidWrightCellPlacement.physKey (p : RapidWrightCellPlacement) :
    Vu47pSiteKind × Nat × Nat × UltraScaleBelPin :=
  (p.siteKind, p.siteX, p.siteY, p.belPin)
def mapPlacedCellToRapidWright (bc : BelCell) (pc : PlacedCell) : RapidWrightCellPlacement :=
  let subSlot : Fin 8 := ⟨pc.belSlot % 8, by omega⟩
  match bc.kind with
  | .dspMul _ =>
    { cellId := pc.cellId, cellName := bc.dstName, slr := slrOfTileY pc.tileY,
      siteKind := .dsp48e2, siteX := pc.tileX * 256 + pc.belSlot, siteY := pc.tileY,
      belPin := .dspAlu, lutInit := pc.lutInit }
  | .ff _ _ =>
    { cellId := pc.cellId, cellName := bc.dstName, slr := slrOfTileY pc.tileY,
      siteKind := .sliceL, siteX := pc.tileX * 32 + pc.belSlot / 8, siteY := pc.tileY,
      belPin := .ff subSlot, lutInit := pc.lutInit }
  | _ =>
    { cellId := pc.cellId, cellName := bc.dstName, slr := slrOfTileY pc.tileY,
      siteKind := .sliceL, siteX := pc.tileX * 32 + pc.belSlot / 8, siteY := pc.tileY,
      belPin := .lut6 subSlot, lutInit := pc.lutInit }
def zipMapRapidWright : List BelCell → List PlacedCell → List RapidWrightCellPlacement
  | bc :: bcs, pc :: pcs => mapPlacedCellToRapidWright bc pc :: zipMapRapidWright bcs pcs
  | _, _ => []
@[expose] def mapPnrCertToRapidWright (net : BelNetlist) (cert : PnrCertificate) :
    List RapidWrightCellPlacement :=
  zipMapRapidWright net.cells cert.placedCells
private theorem zipMapRapidWright_length (bcs : List BelCell) (pcs : List PlacedCell)
    (hEq : pcs.length = bcs.length) : (zipMapRapidWright bcs pcs).length = pcs.length := by
  induction bcs generalizing pcs with
  | nil => cases pcs <;> simp at hEq ⊢; rfl
  | cons bc rest ih =>
    cases pcs with
    | nil => simp at hEq
    | cons pc prest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hEq
      simp [zipMapRapidWright, ih prest hEq]
private theorem zipMapRapidWright_getElem (bcs : List BelCell) (pcs : List PlacedCell)
    (hEq : pcs.length = bcs.length) (i : Nat) (hi : i < (zipMapRapidWright bcs pcs).length) :
    (zipMapRapidWright bcs pcs)[i]'hi =
      mapPlacedCellToRapidWright
        (bcs[i]'(by have := zipMapRapidWright_length bcs pcs hEq; omega))
        (pcs[i]'(by have := zipMapRapidWright_length bcs pcs hEq; omega)) := by
  induction bcs generalizing pcs i with
  | nil => cases pcs <;> simp [zipMapRapidWright] at hEq hi
  | cons bc rest ih =>
    cases pcs with
    | nil => simp [zipMapRapidWright] at hi
    | cons pc prest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hEq
      cases i with
      | zero => rfl
      | succ k =>
        simp only [zipMapRapidWright, List.length_cons] at hi
        exact ih prest hEq k (by omega)
@[expose] def checkPlacedBelSlotsBounded (cells : List PlacedCell) : Bool :=
  cells.all (fun c => decide (c.belSlot < 256))
private theorem checkPlacedBelSlotsBounded_getElem {cells : List PlacedCell}
    (hB : checkPlacedBelSlotsBounded cells = true) (i : Nat) (hi : i < cells.length) :
    cells[i].belSlot < 256 := by
  simp only [checkPlacedBelSlotsBounded, List.all_eq_true, decide_eq_true_eq] at hB
  exact hB cells[i] (List.getElem_mem hi)
example : checkPnrCertificate validAdderBelNetlist corner7nm_SS 5000 validAdderPnrCert = true ∧
    checkPlacedBelSlotsBounded validAdderPnrCert.placedCells = true := by decide +kernel
/-- **Universal RapidWright Locked-Placement Collision Freedom (`rapidWrightPlacement_collision_free`)**. -/
theorem rapidWrightPlacement_collision_free
    (net : BelNetlist) (corner : ProcessCorner) (clockPeriodPs : Nat) (cert : PnrCertificate)
    (hPnr : checkPnrCertificate net corner clockPeriodPs cert = true)
    (hSlots : checkPlacedBelSlotsBounded cert.placedCells = true) :
    let rw := mapPnrCertToRapidWright net cert
    rw.length = net.cells.length ∧
    (∀ p ∈ rw, p.isLocFixed = true ∧ p.isBelFixed = true) ∧
    (∀ (i j : Nat) (hi : i < rw.length) (hj : j < rw.length),
      i ≠ j → rw[i].physKey ≠ rw[j].physKey) := by
  obtain ⟨_, hLenEq, hInj, _, _, _⟩ := checkPnrCertificate_sound net corner clockPeriodPs cert hPnr
  have hRwLen : (mapPnrCertToRapidWright net cert).length = cert.placedCells.length :=
    zipMapRapidWright_length net.cells cert.placedCells hLenEq
  refine ⟨hRwLen.trans hLenEq, ?_, ?_⟩
  · intro p hp
    rcases List.mem_iff_getElem.mp hp with ⟨k, hk, rfl⟩
    dsimp only [mapPnrCertToRapidWright] at hk ⊢
    rw [zipMapRapidWright_getElem net.cells cert.placedCells hLenEq k hk]
    unfold mapPlacedCellToRapidWright; split <;> exact ⟨rfl, rfl⟩
  · intro i j hi hj hNe hKeyEq
    have hiPcs : i < cert.placedCells.length := by omega
    have hjPcs : j < cert.placedCells.length := by omega
    have hNeLoc := hInj i j hiPcs hjPcs hNe
    have hSlotI := checkPlacedBelSlotsBounded_getElem hSlots i hiPcs
    have hSlotJ := checkPlacedBelSlotsBounded_getElem hSlots j hjPcs
    dsimp only [mapPnrCertToRapidWright] at hi hj hKeyEq
    rw [zipMapRapidWright_getElem net.cells cert.placedCells hLenEq i hi,
        zipMapRapidWright_getElem net.cells cert.placedCells hLenEq j hj] at hKeyEq
    apply hNeLoc
    dsimp only [cellLocation]
    unfold mapPlacedCellToRapidWright at hKeyEq
    dsimp only [RapidWrightCellPlacement.physKey] at hKeyEq
    split at hKeyEq
    · split at hKeyEq
      · dsimp only at hKeyEq ⊢
        rcases Prod.mk.inj hKeyEq with ⟨_, h1⟩
        rcases Prod.mk.inj h1 with ⟨hX, h2⟩
        rcases Prod.mk.inj h2 with ⟨hY, _⟩
        have hTX : cert.placedCells[i].tileX = cert.placedCells[j].tileX := by omega
        have hBS : cert.placedCells[i].belSlot = cert.placedCells[j].belSlot := by omega
        rw [hTX, hY, hBS]
      · dsimp only at hKeyEq; cases (Prod.mk.inj hKeyEq).1
      · dsimp only at hKeyEq; cases (Prod.mk.inj hKeyEq).1
    · split at hKeyEq
      · dsimp only at hKeyEq; cases (Prod.mk.inj hKeyEq).1
      · dsimp only at hKeyEq ⊢
        rcases Prod.mk.inj hKeyEq with ⟨_, h1⟩
        rcases Prod.mk.inj h1 with ⟨hX, h2⟩
        rcases Prod.mk.inj h2 with ⟨hY, hPin⟩
        have hSub : cert.placedCells[i].belSlot % 8 = cert.placedCells[j].belSlot % 8 :=
          congrArg Fin.val (UltraScaleBelPin.ff.inj hPin)
        have hTX : cert.placedCells[i].tileX = cert.placedCells[j].tileX := by omega
        have hBS : cert.placedCells[i].belSlot = cert.placedCells[j].belSlot := by omega
        rw [hTX, hY, hBS]
      · dsimp only at hKeyEq; cases (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hKeyEq).2).2).2
    · split at hKeyEq
      · dsimp only at hKeyEq; cases (Prod.mk.inj hKeyEq).1
      · dsimp only at hKeyEq; cases (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hKeyEq).2).2).2
      · dsimp only at hKeyEq ⊢
        rcases Prod.mk.inj hKeyEq with ⟨_, h1⟩
        rcases Prod.mk.inj h1 with ⟨hX, h2⟩
        rcases Prod.mk.inj h2 with ⟨hY, hPin⟩
        have hSub : cert.placedCells[i].belSlot % 8 = cert.placedCells[j].belSlot % 8 :=
          congrArg Fin.val (UltraScaleBelPin.lut6.inj hPin)
        have hTX : cert.placedCells[i].tileX = cert.placedCells[j].tileX := by omega
        have hBS : cert.placedCells[i].belSlot = cert.placedCells[j].belSlot := by omega
        rw [hTX, hY, hBS]
@[expose] def emitRapidWrightMacroJson (macroName : String) (pblockName : String)
    (cells : List RapidWrightCellPlacement) : String :=
  let entries := cells.map (fun c =>
    "    {\"cell\":\"" ++ c.cellName ++ "\",\"slr\":\"" ++ c.slr.toString ++
    "\",\"site\":\"" ++ c.siteName ++ "\",\"bel\":\"" ++ c.belName ++
    "\",\"lutInit\":" ++ toString c.lutInit ++ ",\"isLocFixed\":true,\"isBelFixed\":true}")
  "{\n  \"schema\": \"obend.rapidwright.hardmacro.v1\",\n  \"device\": \"" ++ awsF2TargetDevice ++
  "\",\n  \"macroName\": \"" ++ macroName ++ "\",\n  \"pblock\": \"" ++ pblockName ++
  "\",\n  \"containRouting\": true,\n  \"cells\": [\n" ++ String.intercalate ",\n" entries ++ "\n  ]\n}\n"
@[expose] def emitUltraScalePblockXdc (pblockName : String) (slr : SlrId)
    (cells : List RapidWrightCellPlacement) : String :=
  let header :=
    "create_pblock " ++ pblockName ++ "\n" ++
    "resize_pblock [get_pblocks " ++ pblockName ++ "] -add {" ++ slr.toString ++ "}\n" ++
    "set_property CONTAIN_ROUTING 1 [get_pblocks " ++ pblockName ++ "]\n" ++
    "set_property IS_SOFT 0 [get_pblocks " ++ pblockName ++ "]\n"
  let locks := cells.map (fun c =>
    "set_property BEL " ++ c.belName ++ " [get_cells {" ++ c.cellName ++ "}]\n" ++
    "set_property LOC " ++ c.siteName ++ " [get_cells {" ++ c.cellName ++ "}]\n" ++
    "set_property IS_BEL_FIXED 1 [get_cells {" ++ c.cellName ++ "}]\n" ++
    "set_property IS_LOC_FIXED 1 [get_cells {" ++ c.cellName ++ "}]")
  header ++ String.intercalate "\n" locks ++ "\n"

/-! ## 4. Untrusted EDA Signoff Ingestion `Judge`s (`"vivado-sta@1"` & `"openpdk-drc-sta@1"`) -/
def vivadoPostRouteStaFormatId : String := "vivado-sta@1"
structure VivadoPostRoutePath where
  pathName : String
  srcSlr : SlrId
  dstSlr : SlrId
  setupArrivalSsPs : Nat
  setupSlackReportedSsPs : Int
  holdArrivalFfPs : Nat
  holdReqFfPs : Nat
  holdSlackReportedFfPs : Int
  ttArrivalPs : Nat
  deriving DecidableEq, Repr
structure VivadoStaSignoffObj where
  targetDevice : String := awsF2TargetDevice
  clockPeriodPs : Nat := awsF2MainClockPeriodPs
  clockUncertaintyPs : Nat := 35
  sllCrossingPenaltyPs : Nat := 680
  paths : List VivadoPostRoutePath
  deriving DecidableEq, Repr
structure VivadoStaCert where
  worstSetupSlackPs : Int
  worstHoldSlackPs : Int
  maxSlrCrossings : Nat
  deriving DecidableEq, Repr
inductive VivadoStaRefusal where
  | unsupportedDevice | emptyTimingPaths | setupViolationSS
  | holdViolationFF | ttCornerViolation | certSummaryMismatch
  deriving DecidableEq, Repr
def vivadoStaRefutes : VivadoStaRefusal → Bool
  | .certSummaryMismatch => false | _ => true
def VivadoStaMeaning (o : VivadoStaSignoffObj) (c : VivadoStaCert) : Prop :=
  o.targetDevice = awsF2TargetDevice ∧ o.paths ≠ [] ∧
  0 ≤ c.worstSetupSlackPs ∧ 0 ≤ c.worstHoldSlackPs ∧
  ∀ p ∈ o.paths,
    p.setupArrivalSsPs + o.clockUncertaintyPs +
      slrDistance p.srcSlr p.dstSlr * o.sllCrossingPenaltyPs ≤ o.clockPeriodPs ∧
    0 ≤ p.setupSlackReportedSsPs ∧ c.worstSetupSlackPs ≤ p.setupSlackReportedSsPs ∧
    p.holdReqFfPs + o.clockUncertaintyPs ≤ p.holdArrivalFfPs ∧
    0 ≤ p.holdSlackReportedFfPs ∧ c.worstHoldSlackPs ≤ p.holdSlackReportedFfPs ∧
    p.ttArrivalPs + o.clockUncertaintyPs +
      slrDistance p.srcSlr p.dstSlr * o.sllCrossingPenaltyPs ≤ o.clockPeriodPs ∧
    slrDistance p.srcSlr p.dstSlr ≤ c.maxSlrCrossings
def checkVivadoSetupSS (o : VivadoStaSignoffObj) (p : VivadoPostRoutePath) : Bool :=
  decide (p.setupArrivalSsPs + o.clockUncertaintyPs +
    slrDistance p.srcSlr p.dstSlr * o.sllCrossingPenaltyPs ≤ o.clockPeriodPs) &&
  decide (0 ≤ p.setupSlackReportedSsPs)
def checkVivadoHoldFF (o : VivadoStaSignoffObj) (p : VivadoPostRoutePath) : Bool :=
  decide (p.holdReqFfPs + o.clockUncertaintyPs ≤ p.holdArrivalFfPs) &&
  decide (0 ≤ p.holdSlackReportedFfPs)
def checkVivadoTtCorner (o : VivadoStaSignoffObj) (p : VivadoPostRoutePath) : Bool :=
  decide (p.ttArrivalPs + o.clockUncertaintyPs +
    slrDistance p.srcSlr p.dstSlr * o.sllCrossingPenaltyPs ≤ o.clockPeriodPs)
def checkVivadoCertBounds (c : VivadoStaCert) (p : VivadoPostRoutePath) : Bool :=
  decide (c.worstSetupSlackPs ≤ p.setupSlackReportedSsPs) &&
  decide (c.worstHoldSlackPs ≤ p.holdSlackReportedFfPs) &&
  decide (slrDistance p.srcSlr p.dstSlr ≤ c.maxSlrCrossings)
def checkVivadoStaSignoff (grade : Nat) (o : VivadoStaSignoffObj) (c : VivadoStaCert) :
    Obend.Judge.Verdict VivadoStaRefusal :=
  if grade < o.paths.length + 1 then .uncovered
  else if !(o.targetDevice == awsF2TargetDevice) then .refused .unsupportedDevice []
  else if o.paths.isEmpty then .refused .emptyTimingPaths []
  else if !(o.paths.all (checkVivadoSetupSS o)) then .refused .setupViolationSS [0]
  else if !(o.paths.all (checkVivadoHoldFF o)) then .refused .holdViolationFF [1]
  else if !(o.paths.all (checkVivadoTtCorner o)) then .refused .ttCornerViolation [2]
  else if !(decide (0 ≤ c.worstSetupSlackPs) && decide (0 ≤ c.worstHoldSlackPs) &&
            o.paths.all (checkVivadoCertBounds c)) then .refused .certSummaryMismatch [3]
  else .ok
/-- Verified `Obend.Judge` instance for untrusted Vivado UltraScale+ post-route STA (`"vivado-sta@1"`). -/
@[instance_reducible] instance vivadoPostRouteStaJudge :
    Obend.Judge VivadoStaSignoffObj VivadoStaCert where
  Clause := VivadoStaRefusal
  Meaning := VivadoStaMeaning
  check := checkVivadoStaSignoff
  refutes := vivadoStaRefutes
  Fragment := fun o => o.paths.length ≤ 4096
  sound := by
    intro r o c hOk; unfold checkVivadoStaSignoff at hOk
    split at hOk; · cases hOk
    split at hOk; · cases hOk
    rename_i _ hDevB
    split at hOk; · cases hOk
    rename_i hNotEmpty
    split at hOk; · cases hOk
    rename_i hSetupB
    split at hOk; · cases hOk
    rename_i hHoldB
    split at hOk; · cases hOk
    rename_i hTtB
    split at hOk; · cases hOk
    rename_i hCertB
    simp only [Bool.not_eq_true', Bool.eq_false_iff, Classical.not_not, beq_iff_eq,
      Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hDevB hSetupB hHoldB hTtB hCertB
    have hNeNil : o.paths ≠ [] := by intro hNil; rw [hNil] at hNotEmpty; simp at hNotEmpty
    refine ⟨hDevB, hNeNil, hCertB.1.1, hCertB.1.2, fun p hp => ?_⟩
    have hs := hSetupB p hp; have hh := hHoldB p hp; have ht := hTtB p hp; have hc := hCertB.2 p hp
    simp only [checkVivadoSetupSS, checkVivadoHoldFF, checkVivadoTtCorner, checkVivadoCertBounds,
      Bool.and_eq_true, decide_eq_true_eq] at hs hh ht hc
    exact ⟨hs.1, hs.2, hc.1.1, hh.1, hh.2, hc.1.2, ht, hc.2⟩
  refuted := by
    intro r o c k p hRef hRefutes c' hMean; unfold checkVivadoStaSignoff at hRef
    split at hRef; · cases hRef
    split at hRef
    · rename_i hBadDev; injection hRef with hk _; subst hk
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hBadDev; exact hBadDev hMean.1
    · split at hRef
      · rename_i hEmp; injection hRef with hk _; subst hk
        rw [List.isEmpty_iff] at hEmp; exact hMean.2.1 hEmp
      · split at hRef
        · rename_i hBadSetup; injection hRef with hk _; subst hk
          simp only [Bool.not_eq_true', List.all_eq_false] at hBadSetup
          rcases hBadSetup with ⟨pt, hMem, hNotS⟩
          have hP := hMean.2.2.2.2 pt hMem
          simp only [checkVivadoSetupSS, Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hNotS
          exact hNotS.elim (fun h1 => h1 hP.1) (fun h2 => h2 hP.2.1)
        · split at hRef
          · rename_i hBadHold; injection hRef with hk _; subst hk
            simp only [Bool.not_eq_true', List.all_eq_false] at hBadHold
            rcases hBadHold with ⟨pt, hMem, hNotH⟩
            have hP := hMean.2.2.2.2 pt hMem
            simp only [checkVivadoHoldFF, Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hNotH
            exact hNotH.elim (fun h1 => h1 hP.2.2.2.1) (fun h2 => h2 hP.2.2.2.2.1)
          · split at hRef
            · rename_i hBadTt; injection hRef with hk _; subst hk
              simp only [Bool.not_eq_true', List.all_eq_false] at hBadTt
              rcases hBadTt with ⟨pt, hMem, hNotT⟩
              have hP := hMean.2.2.2.2 pt hMem
              simp only [checkVivadoTtCorner, decide_eq_true_eq] at hNotT
              exact hNotT hP.2.2.2.2.2.2.1
            · split at hRef
              · injection hRef with hk _; subst hk; cases hRefutes
              · cases hRef
  complete := by
    intro o _ ⟨c, hMean⟩; refine ⟨c, o.paths.length + 1, ?_⟩
    rcases hMean with ⟨hDev, hNeNil, hWns0, hWhs0, hPaths⟩
    unfold checkVivadoStaSignoff
    have hNotLt : ¬ (o.paths.length + 1 < o.paths.length + 1) := Nat.lt_irrefl _
    have hNotEmp : o.paths.isEmpty = false := by
      cases hL : o.paths with | nil => exact absurd hL hNeNil | cons _ _ => rfl
    have hSetupAll : o.paths.all (checkVivadoSetupSS o) = true := by
      rw [List.all_eq_true]; intro p hp; simp [checkVivadoSetupSS, (hPaths p hp).1, (hPaths p hp).2.1]
    have hHoldAll : o.paths.all (checkVivadoHoldFF o) = true := by
      rw [List.all_eq_true]; intro p hp; simp [checkVivadoHoldFF, (hPaths p hp).2.2.2.1, (hPaths p hp).2.2.2.2.1]
    have hTtAll : o.paths.all (checkVivadoTtCorner o) = true := by
      rw [List.all_eq_true]; intro p hp; simp [checkVivadoTtCorner, (hPaths p hp).2.2.2.2.2.2.1]
    have hCertAll : o.paths.all (checkVivadoCertBounds c) = true := by
      rw [List.all_eq_true]; intro p hp
      simp [checkVivadoCertBounds, (hPaths p hp).2.2.1, (hPaths p hp).2.2.2.2.2.1, (hPaths p hp).2.2.2.2.2.2.2]
    simp [hNotLt, hDev, hNotEmp, hSetupAll, hHoldAll, hTtAll, hWns0, hWhs0, hCertAll]
  mono := by
    intro r r' o c hLe hDecided; unfold checkVivadoStaSignoff at hDecided ⊢
    split at hDecided
    · exact absurd rfl hDecided
    · rename_i hNotLt; have hNotLt' : ¬ (r' < o.paths.length + 1) := by omega
      simp only [hNotLt, hNotLt', ↓reduceIte]
def sampleVivadoStaObj : VivadoStaSignoffObj where
  paths :=
    [ { pathName := "slr0_to_slr1_reg", srcSlr := .slr0, dstSlr := .slr1,
        setupArrivalSsPs := 2950, setupSlackReportedSsPs := 335,
        holdArrivalFfPs := 190, holdReqFfPs := 110, holdSlackReportedFfPs := 45,
        ttArrivalPs := 2400 } ]
def sampleVivadoStaCert : VivadoStaCert where
  worstSetupSlackPs := 335
  worstHoldSlackPs := 45
  maxSlrCrossings := 1
example : vivadoPostRouteStaJudge.Fragment sampleVivadoStaObj ∧
    vivadoPostRouteStaJudge.check 8 sampleVivadoStaObj sampleVivadoStaCert = .ok := by
  refine ⟨?_, ?_⟩
  · change sampleVivadoStaObj.paths.length ≤ 4096; decide +kernel
  · change checkVivadoStaSignoff 8 sampleVivadoStaObj sampleVivadoStaCert = .ok; decide +kernel
def openPdkSignoffFormatId : String := "openpdk-drc-sta@1"
inductive OpenPdkNode where | sky130 | asap7 deriving DecidableEq, Repr
structure LayerDrcRule where
  layerId : Nat
  layerName : String
  minWidthNm : Nat
  minSpacingNm : Nat
  deriving DecidableEq, Repr
structure ViaEnclosureRule where
  viaLayerId : Nat
  metalLayerId : Nat
  minEnclosureNm : Nat
  deriving DecidableEq, Repr
structure OpenPdkRuleDeck where
  node : OpenPdkNode
  nodeNm : Nat
  layerRules : List LayerDrcRule
  viaRules : List ViaEnclosureRule
  deriving DecidableEq, Repr
def sky130PdkDeck : OpenPdkRuleDeck where
  node := .sky130
  nodeNm := 130
  layerRules :=
    [ { layerId := 0, layerName := "li1",  minWidthNm := 170, minSpacingNm := 170 }
    , { layerId := 1, layerName := "met1", minWidthNm := 140, minSpacingNm := 140 }
    , { layerId := 2, layerName := "met2", minWidthNm := 140, minSpacingNm := 140 }
    , { layerId := 3, layerName := "met3", minWidthNm := 300, minSpacingNm := 300 } ]
  viaRules :=
    [ { viaLayerId := 10, metalLayerId := 1, minEnclosureNm := 55 }
    , { viaLayerId := 11, metalLayerId := 2, minEnclosureNm := 55 } ]
def asap7PdkDeck : OpenPdkRuleDeck where
  node := .asap7
  nodeNm := 7
  layerRules :=
    [ { layerId := 1, layerName := "M1", minWidthNm := 18, minSpacingNm := 18 }
    , { layerId := 2, layerName := "M2", minWidthNm := 18, minSpacingNm := 18 }
    , { layerId := 3, layerName := "M3", minWidthNm := 24, minSpacingNm := 24 } ]
  viaRules :=
    [ { viaLayerId := 10, metalLayerId := 1, minEnclosureNm := 4 }
    , { viaLayerId := 11, metalLayerId := 2, minEnclosureNm := 4 } ]
structure OpenStaCornerSummary where
  pathGroup : String
  ffWnsPs : Int
  ffWhsPs : Int
  ttWnsPs : Int
  ttWhsPs : Int
  ssWnsPs : Int
  ssWhsPs : Int
  deriving DecidableEq, Repr
structure OpenPdkSignoffObj where
  deck : OpenPdkRuleDeck
  netlistPins : List String
  defPorts : List String
  metalShapes : List (Nat × LayoutBox2D)
  viaCuts : List (LayoutBox2D × LayoutBox2D)
  cornerReports : List OpenStaCornerSummary
  deriving DecidableEq, Repr
structure OpenPdkSignoffCert where
  pinToDefIdx : List Nat
  defToPinIdx : List Nat
  minWnsPs : Int
  minWhsPs : Int
  deriving DecidableEq, Repr
inductive OpenPdkRefusal where
  | emptyReportsOrLayout | multiCornerStaViolation | metalWidthOrLayerViolation
  | metalSpacingViolation | viaEnclosureViolation | pinDefCountMismatch
  | bijectionOrSlackCertInvalid
  deriving DecidableEq, Repr
def openPdkRefutes : OpenPdkRefusal → Bool
  | .bijectionOrSlackCertInvalid => false | _ => true
def lookupLayerRule? (layerId : Nat) : List LayerDrcRule → Option LayerDrcRule
  | [] => none
  | r :: rest => if r.layerId == layerId then some r else lookupLayerRule? layerId rest
def lookupViaRule? (viaLayerId metalLayerId : Nat) : List ViaEnclosureRule → Option ViaEnclosureRule
  | [] => none
  | r :: rest =>
    if (r.viaLayerId == viaLayerId) && (r.metalLayerId == metalLayerId) then some r
    else lookupViaRule? viaLayerId metalLayerId rest
def MetalShapeWidthSafe (deck : OpenPdkRuleDeck) (b : LayoutBox2D) : Prop :=
  b.xMinNm < b.xMaxNm ∧ b.yMinNm < b.yMaxNm ∧
  ∃ r : LayerDrcRule,
    lookupLayerRule? b.layerId deck.layerRules = some r ∧
    r.minWidthNm ≤ b.xMaxNm - b.xMinNm ∧ r.minWidthNm ≤ b.yMaxNm - b.yMinNm
def MetalPairSpacingSafe (deck : OpenPdkRuleDeck) (s₁ s₂ : Nat × LayoutBox2D) : Prop :=
  s₁.2.layerId = s₂.2.layerId → s₁.1 ≠ s₂.1 →
  ∃ r : LayerDrcRule,
    lookupLayerRule? s₁.2.layerId deck.layerRules = some r ∧
    (s₁.2.xMaxNm + max r.minSpacingNm 1 ≤ s₂.2.xMinNm ∨
     s₂.2.xMaxNm + max r.minSpacingNm 1 ≤ s₁.2.xMinNm ∨
     s₁.2.yMaxNm + max r.minSpacingNm 1 ≤ s₂.2.yMinNm ∨
     s₂.2.yMaxNm + max r.minSpacingNm 1 ≤ s₁.2.yMinNm)
def ViaCutEnclosureSafe (deck : OpenPdkRuleDeck) (vp : LayoutBox2D × LayoutBox2D) : Prop :=
  vp.1.xMinNm < vp.1.xMaxNm ∧ vp.1.yMinNm < vp.1.yMaxNm ∧
  vp.2.xMinNm < vp.2.xMaxNm ∧ vp.2.yMinNm < vp.2.yMaxNm ∧
  ∃ vr : ViaEnclosureRule,
    lookupViaRule? vp.1.layerId vp.2.layerId deck.viaRules = some vr ∧
    vp.2.xMinNm + vr.minEnclosureNm ≤ vp.1.xMinNm ∧
    vp.1.xMaxNm + vr.minEnclosureNm ≤ vp.2.xMaxNm ∧
    vp.2.yMinNm + vr.minEnclosureNm ≤ vp.1.yMinNm ∧
    vp.1.yMaxNm + vr.minEnclosureNm ≤ vp.2.yMaxNm
def OpenPdkSignoffMeaning (o : OpenPdkSignoffObj) (c : OpenPdkSignoffCert) : Prop :=
  o.cornerReports ≠ [] ∧ o.metalShapes ≠ [] ∧ o.netlistPins.length = o.defPorts.length ∧
  0 ≤ c.minWnsPs ∧ 0 ≤ c.minWhsPs ∧
  (∀ cr ∈ o.cornerReports,
    0 ≤ cr.ffWnsPs ∧ 0 ≤ cr.ffWhsPs ∧ 0 ≤ cr.ttWnsPs ∧ 0 ≤ cr.ttWhsPs ∧ 0 ≤ cr.ssWnsPs ∧ 0 ≤ cr.ssWhsPs ∧
    c.minWnsPs ≤ cr.ffWnsPs ∧ c.minWnsPs ≤ cr.ttWnsPs ∧ c.minWnsPs ≤ cr.ssWnsPs ∧
    c.minWhsPs ≤ cr.ffWhsPs ∧ c.minWhsPs ≤ cr.ttWhsPs ∧ c.minWhsPs ≤ cr.ssWhsPs) ∧
  (∀ s ∈ o.metalShapes, MetalShapeWidthSafe o.deck s.2) ∧
  (∀ s₁ ∈ o.metalShapes, ∀ s₂ ∈ o.metalShapes, MetalPairSpacingSafe o.deck s₁ s₂) ∧
  (∀ vp ∈ o.viaCuts, ViaCutEnclosureSafe o.deck vp) ∧
  c.pinToDefIdx.length = o.netlistPins.length ∧ c.defToPinIdx.length = o.defPorts.length ∧
  (∀ i : Nat, i < o.netlistPins.length →
    ∃ j : Nat, j < o.defPorts.length ∧
      c.pinToDefIdx[i]? = some j ∧ c.defToPinIdx[j]? = some i ∧ o.netlistPins[i]? = o.defPorts[j]?)
def checkCornerNonneg (cr : OpenStaCornerSummary) : Bool :=
  decide (0 ≤ cr.ffWnsPs) && decide (0 ≤ cr.ffWhsPs) &&
  decide (0 ≤ cr.ttWnsPs) && decide (0 ≤ cr.ttWhsPs) &&
  decide (0 ≤ cr.ssWnsPs) && decide (0 ≤ cr.ssWhsPs)
def checkCornerCertFloor (c : OpenPdkSignoffCert) (cr : OpenStaCornerSummary) : Bool :=
  decide (c.minWnsPs ≤ cr.ffWnsPs) && decide (c.minWnsPs ≤ cr.ttWnsPs) && decide (c.minWnsPs ≤ cr.ssWnsPs) &&
  decide (c.minWhsPs ≤ cr.ffWhsPs) && decide (c.minWhsPs ≤ cr.ttWhsPs) && decide (c.minWhsPs ≤ cr.ssWhsPs)
def checkShapeWidthB (deck : OpenPdkRuleDeck) (s : Nat × LayoutBox2D) : Bool :=
  decide (s.2.xMinNm < s.2.xMaxNm) && decide (s.2.yMinNm < s.2.yMaxNm) &&
  match lookupLayerRule? s.2.layerId deck.layerRules with
  | none => false
  | some r => decide (r.minWidthNm ≤ s.2.xMaxNm - s.2.xMinNm) && decide (r.minWidthNm ≤ s.2.yMaxNm - s.2.yMinNm)
def checkShapePairSpacingB (deck : OpenPdkRuleDeck) (s₁ s₂ : Nat × LayoutBox2D) : Bool :=
  if !(s₁.2.layerId == s₂.2.layerId) || (s₁.1 == s₂.1) then true
  else match lookupLayerRule? s₁.2.layerId deck.layerRules with
    | none => false
    | some r =>
      let sep := max r.minSpacingNm 1
      decide (s₁.2.xMaxNm + sep ≤ s₂.2.xMinNm) || decide (s₂.2.xMaxNm + sep ≤ s₁.2.xMinNm) ||
      decide (s₁.2.yMaxNm + sep ≤ s₂.2.yMinNm) || decide (s₂.2.yMaxNm + sep ≤ s₁.2.yMinNm)
def checkViaCutB (deck : OpenPdkRuleDeck) (vp : LayoutBox2D × LayoutBox2D) : Bool :=
  decide (vp.1.xMinNm < vp.1.xMaxNm) && decide (vp.1.yMinNm < vp.1.yMaxNm) &&
  decide (vp.2.xMinNm < vp.2.xMaxNm) && decide (vp.2.yMinNm < vp.2.yMaxNm) &&
  match lookupViaRule? vp.1.layerId vp.2.layerId deck.viaRules with
  | none => false
  | some vr =>
    decide (vp.2.xMinNm + vr.minEnclosureNm ≤ vp.1.xMinNm) &&
    decide (vp.1.xMaxNm + vr.minEnclosureNm ≤ vp.2.xMaxNm) &&
    decide (vp.2.yMinNm + vr.minEnclosureNm ≤ vp.1.yMinNm) &&
    decide (vp.1.yMaxNm + vr.minEnclosureNm ≤ vp.2.yMaxNm)
def checkPinBijectionAt (o : OpenPdkSignoffObj) (c : OpenPdkSignoffCert) (i : Nat) : Bool :=
  match c.pinToDefIdx[i]? with
  | none => false
  | some j => decide (j < o.defPorts.length) && (c.defToPinIdx[j]? == some i) && (o.netlistPins[i]? == o.defPorts[j]?)
def checkOpenPdkCertValid (o : OpenPdkSignoffObj) (c : OpenPdkSignoffCert) : Bool :=
  decide (0 ≤ c.minWnsPs) && decide (0 ≤ c.minWhsPs) &&
  o.cornerReports.all (checkCornerCertFloor c) &&
  (c.pinToDefIdx.length == o.netlistPins.length) &&
  (c.defToPinIdx.length == o.defPorts.length) &&
  (List.range o.netlistPins.length).all (checkPinBijectionAt o c)
def openPdkRequiredGrade (o : OpenPdkSignoffObj) : Nat :=
  o.cornerReports.length + o.metalShapes.length + o.viaCuts.length + o.netlistPins.length + 1
def checkOpenPdkSignoff (grade : Nat) (o : OpenPdkSignoffObj) (c : OpenPdkSignoffCert) :
    Obend.Judge.Verdict OpenPdkRefusal :=
  if grade < openPdkRequiredGrade o then .uncovered
  else if o.cornerReports.isEmpty || o.metalShapes.isEmpty then .refused .emptyReportsOrLayout []
  else if !(o.cornerReports.all checkCornerNonneg) then .refused .multiCornerStaViolation [0]
  else if !(o.metalShapes.all (checkShapeWidthB o.deck)) then .refused .metalWidthOrLayerViolation [1]
  else if !(o.metalShapes.all (fun s₁ => o.metalShapes.all (checkShapePairSpacingB o.deck s₁))) then
    .refused .metalSpacingViolation [2]
  else if !(o.viaCuts.all (checkViaCutB o.deck)) then .refused .viaEnclosureViolation [3]
  else if !(o.netlistPins.length == o.defPorts.length) then .refused .pinDefCountMismatch [4]
  else if !(checkOpenPdkCertValid o c) then .refused .bijectionOrSlackCertInvalid [5]
  else .ok
private theorem checkShapeWidthB_iff (deck : OpenPdkRuleDeck) (s : Nat × LayoutBox2D) :
    checkShapeWidthB deck s = true ↔ MetalShapeWidthSafe deck s.2 := by
  unfold checkShapeWidthB MetalShapeWidthSafe
  cases lookupLayerRule? s.2.layerId deck.layerRules with
  | none => simp
  | some r => simp [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
private theorem checkShapePairSpacingB_iff (deck : OpenPdkRuleDeck) (s₁ s₂ : Nat × LayoutBox2D) :
    checkShapePairSpacingB deck s₁ s₂ = true ↔ MetalPairSpacingSafe deck s₁ s₂ := by
  unfold checkShapePairSpacingB MetalPairSpacingSafe
  by_cases hLayer : s₁.2.layerId = s₂.2.layerId
  · by_cases hNet : s₁.1 = s₂.1
    · simp [hLayer, hNet]
    · have hCond : (!(s₁.2.layerId == s₂.2.layerId) || (s₁.1 == s₂.1)) = false := by simp [hLayer, hNet]
      rw [hCond]; simp only [Bool.false_eq_true, ↓reduceIte]
      cases hLook : lookupLayerRule? s₁.2.layerId deck.layerRules with
      | none =>
        constructor
        · intro hF; cases hF
        · intro hImp; obtain ⟨r, hr, _⟩ := hImp hLayer hNet; cases hr
      | some r =>
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · intro hOr _ _
          rcases hOr with ((h1 | h2) | h3) | h4
          · exact ⟨r, rfl, Or.inl h1⟩
          · exact ⟨r, rfl, Or.inr (Or.inl h2)⟩
          · exact ⟨r, rfl, Or.inr (Or.inr (Or.inl h3))⟩
          · exact ⟨r, rfl, Or.inr (Or.inr (Or.inr h4))⟩
        · intro hImp
          obtain ⟨r', hr', hDisj⟩ := hImp hLayer hNet; injection hr' with hEqR; subst hEqR
          rcases hDisj with h1 | h2 | h3 | h4
          · exact Or.inl (Or.inl (Or.inl h1))
          · exact Or.inl (Or.inl (Or.inr h2))
          · exact Or.inl (Or.inr h3)
          · exact Or.inr h4
  · have hCond : (!(s₁.2.layerId == s₂.2.layerId) || (s₁.1 == s₂.1)) = true := by
      simp [beq_eq_false_iff_ne.mpr hLayer]
    rw [hCond]; simp [hLayer]
private theorem checkViaCutB_iff (deck : OpenPdkRuleDeck) (vp : LayoutBox2D × LayoutBox2D) :
    checkViaCutB deck vp = true ↔ ViaCutEnclosureSafe deck vp := by
  unfold checkViaCutB ViaCutEnclosureSafe
  cases lookupViaRule? vp.1.layerId vp.2.layerId deck.viaRules with
  | none => simp
  | some vr => simp [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
/-- Verified `Obend.Judge` instance for OpenROAD / OpenSTA / Sky130 / ASAP7 signoff (`"openpdk-drc-sta@1"`). -/
@[instance_reducible] instance openPdkSignoffJudge :
    Obend.Judge OpenPdkSignoffObj OpenPdkSignoffCert where
  Clause := OpenPdkRefusal
  Meaning := OpenPdkSignoffMeaning
  check := checkOpenPdkSignoff
  refutes := openPdkRefutes
  Fragment := fun o => openPdkRequiredGrade o ≤ 16384
  sound := by
    intro r o c hOk; unfold checkOpenPdkSignoff at hOk
    split at hOk; · cases hOk
    split at hOk; · cases hOk
    rename_i _ hNotEmp
    split at hOk; · cases hOk
    rename_i hStaB
    split at hOk; · cases hOk
    rename_i hWidthB
    split at hOk; · cases hOk
    rename_i hSpaceB
    split at hOk; · cases hOk
    rename_i hViaB
    split at hOk; · cases hOk
    rename_i hPinLenB
    split at hOk; · cases hOk
    rename_i hCertB
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, List.isEmpty_eq_false_iff] at hNotEmp
    simp only [Bool.not_eq_true', Bool.eq_false_iff, Classical.not_not, List.all_eq_true,
      beq_iff_eq] at hStaB hWidthB hSpaceB hViaB hPinLenB hCertB
    unfold checkOpenPdkCertValid at hCertB
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range] at hCertB
    rcases hCertB with ⟨⟨⟨⟨⟨hMinWns, hMinWhs⟩, hFloor⟩, hP2D⟩, hD2P⟩, hBij⟩
    refine ⟨hNotEmp.1, hNotEmp.2, hPinLenB, hMinWns, hMinWhs, ?_,
      fun s hs => (checkShapeWidthB_iff o.deck s).mp (hWidthB s hs),
      fun s₁ hs₁ s₂ hs₂ => (checkShapePairSpacingB_iff o.deck s₁ s₂).mp (hSpaceB s₁ hs₁ s₂ hs₂),
      fun vp hvp => (checkViaCutB_iff o.deck vp).mp (hViaB vp hvp), hP2D, hD2P, ?_⟩
    · intro cr hCr
      have h1 := hStaB cr hCr; have h2 := hFloor cr hCr
      simp only [checkCornerNonneg, checkCornerCertFloor, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
      exact ⟨h1.1.1.1.1.1, h1.1.1.1.1.2, h1.1.1.1.2, h1.1.1.2, h1.1.2, h1.2,
             h2.1.1.1.1.1, h2.1.1.1.1.2, h2.1.1.1.2, h2.1.1.2, h2.1.2, h2.2⟩
    · intro i hi
      have hBi := hBij i hi; unfold checkPinBijectionAt at hBi
      cases hLookup : c.pinToDefIdx[i]? with
      | none => rw [hLookup] at hBi; cases hBi
      | some j =>
        rw [hLookup] at hBi; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hBi
        exact ⟨j, hBi.1.1, rfl, hBi.1.2, hBi.2⟩
  refuted := by
    intro r o c k p hRef hRefutes c' hMean; unfold checkOpenPdkSignoff at hRef
    split at hRef; · cases hRef
    split at hRef
    · rename_i hEmp; injection hRef with hk _; subst hk
      simp only [Bool.or_eq_true, List.isEmpty_iff] at hEmp
      exact hEmp.elim (fun h1 => hMean.1 h1) (fun h2 => hMean.2.1 h2)
    · split at hRef
      · rename_i hBadSta; injection hRef with hk _; subst hk
        simp only [Bool.not_eq_true', List.all_eq_false] at hBadSta
        rcases hBadSta with ⟨cr, hMem, hNotOk⟩
        have hM := hMean.2.2.2.2.2.1 cr hMem
        exact hNotOk (by simp [checkCornerNonneg, hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2.1])
      · split at hRef
        · rename_i hBadW; injection hRef with hk _; subst hk
          simp only [Bool.not_eq_true', List.all_eq_false] at hBadW
          rcases hBadW with ⟨s, hs, hNotW⟩
          exact hNotW ((checkShapeWidthB_iff o.deck s).mpr (hMean.2.2.2.2.2.2.1 s hs))
        · split at hRef
          · rename_i hBadS; injection hRef with hk _; subst hk
            rw [Bool.not_eq_true', List.all_eq_false] at hBadS
            rcases hBadS with ⟨s₁, hs₁, hNotAll2⟩
            rw [Bool.not_eq_true, List.all_eq_false] at hNotAll2
            rcases hNotAll2 with ⟨s₂, hs₂, hNotPair⟩
            exact absurd ((checkShapePairSpacingB_iff o.deck s₁ s₂).mpr (hMean.2.2.2.2.2.2.2.1 s₁ hs₁ s₂ hs₂)) hNotPair
          · split at hRef
            · rename_i hBadV; injection hRef with hk _; subst hk
              simp only [Bool.not_eq_true', List.all_eq_false] at hBadV
              rcases hBadV with ⟨vp, hvp, hNotV⟩
              exact hNotV ((checkViaCutB_iff o.deck vp).mpr (hMean.2.2.2.2.2.2.2.2.1 vp hvp))
            · split at hRef
              · rename_i hBadLen; injection hRef with hk _; subst hk
                simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hBadLen
                exact hBadLen hMean.2.2.1
              · split at hRef
                · injection hRef with hk _; subst hk; cases hRefutes
                · cases hRef
  complete := by
    intro o _ ⟨c, hMean⟩; refine ⟨c, openPdkRequiredGrade o, ?_⟩
    rcases hMean with ⟨hCrNe, hShNe, hPinEq, hMinWns, hMinWhs, hCorners, hWidths, hSpaces, hVias, hP2D, hD2P, hBij⟩
    unfold checkOpenPdkSignoff
    have hNotLt : ¬ (openPdkRequiredGrade o < openPdkRequiredGrade o) := Nat.lt_irrefl _
    have hEmpF : (o.cornerReports.isEmpty || o.metalShapes.isEmpty) = false := by
      simp [List.isEmpty_eq_false_iff, hCrNe, hShNe]
    have hStaT : o.cornerReports.all checkCornerNonneg = true := by
      rw [List.all_eq_true]; intro cr hCr; have hM := hCorners cr hCr
      simp [checkCornerNonneg, hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2.1]
    have hWidthT : o.metalShapes.all (checkShapeWidthB o.deck) = true := by
      rw [List.all_eq_true]; intro s hs; exact (checkShapeWidthB_iff o.deck s).mpr (hWidths s hs)
    have hSpaceT : o.metalShapes.all (fun s₁ => o.metalShapes.all (checkShapePairSpacingB o.deck s₁)) = true := by
      rw [List.all_eq_true]; intro s₁ hs₁; rw [List.all_eq_true]; intro s₂ hs₂
      exact (checkShapePairSpacingB_iff o.deck s₁ s₂).mpr (hSpaces s₁ hs₁ s₂ hs₂)
    have hViaT : o.viaCuts.all (checkViaCutB o.deck) = true := by
      rw [List.all_eq_true]; intro vp hvp; exact (checkViaCutB_iff o.deck vp).mpr (hVias vp hvp)
    have hCertT : checkOpenPdkCertValid o c = true := by
      unfold checkOpenPdkCertValid
      have hFloorT : o.cornerReports.all (checkCornerCertFloor c) = true := by
        rw [List.all_eq_true]; intro cr hCr; have hM := hCorners cr hCr
        simp [checkCornerCertFloor, hM.2.2.2.2.2.2.1, hM.2.2.2.2.2.2.2.1, hM.2.2.2.2.2.2.2.2.1,
          hM.2.2.2.2.2.2.2.2.2.1, hM.2.2.2.2.2.2.2.2.2.2.1, hM.2.2.2.2.2.2.2.2.2.2.2]
      have hBijT : (List.range o.netlistPins.length).all (checkPinBijectionAt o c) = true := by
        rw [List.all_eq_true]; intro i hi; rw [List.mem_range] at hi
        obtain ⟨j, hj, h1, h2, h3⟩ := hBij i hi
        simp [checkPinBijectionAt, h1, hj, h2, h3]
      simp [hMinWns, hMinWhs, hFloorT, hP2D, hD2P, hBijT]
    simp [hNotLt, hEmpF, hStaT, hWidthT, hSpaceT, hViaT, hPinEq, hCertT]
  mono := by
    intro r r' o c hLe hDecided; unfold checkOpenPdkSignoff at hDecided ⊢
    split at hDecided
    · exact absurd rfl hDecided
    · rename_i hNotLt; have hNotLt' : ¬ (r' < openPdkRequiredGrade o) := by omega
      simp only [hNotLt, hNotLt', ↓reduceIte]
def sampleSky130SignoffObj : OpenPdkSignoffObj where
  deck := sky130PdkDeck
  netlistPins := ["clk", "rst_n", "y_out"]
  defPorts := ["rst_n", "y_out", "clk"]
  metalShapes :=
    [ (0, { layerId := 1, xMinNm := 0, yMinNm := 0, xMaxNm := 200, yMaxNm := 200 })
    , (1, { layerId := 1, xMinNm := 400, yMinNm := 0, xMaxNm := 600, yMaxNm := 200 }) ]
  viaCuts :=
    [ ( { layerId := 10, xMinNm := 60, yMinNm := 60, xMaxNm := 130, yMaxNm := 130 }
      , { layerId := 1, xMinNm := 0, yMinNm := 0, xMaxNm := 200, yMaxNm := 200 } ) ]
  cornerReports :=
    [ { pathGroup := "reg2reg", ffWnsPs := 420, ffWhsPs := 45,
        ttWnsPs := 290, ttWhsPs := 60, ssWnsPs := 115, ssWhsPs := 85 } ]
def sampleSky130SignoffCert : OpenPdkSignoffCert where
  pinToDefIdx := [2, 0, 1]
  defToPinIdx := [1, 2, 0]
  minWnsPs := 115
  minWhsPs := 45
example : openPdkSignoffJudge.Fragment sampleSky130SignoffObj ∧
    openPdkSignoffJudge.check 20 sampleSky130SignoffObj sampleSky130SignoffCert = .ok := by
  refine ⟨?_, ?_⟩
  · change openPdkRequiredGrade sampleSky130SignoffObj ≤ 16384; decide +kernel
  · change checkOpenPdkSignoff 20 sampleSky130SignoffObj sampleSky130SignoffCert = .ok; decide +kernel
/-- **Geometric Disjointness Corollary (`openPdkSignoff_same_layer_disjoint`)**. -/
theorem openPdkSignoff_same_layer_disjoint
    {r : Nat} {o : OpenPdkSignoffObj} {c : OpenPdkSignoffCert}
    (hOk : openPdkSignoffJudge.check r o c = .ok)
    {n₁ n₂ : Nat} {b₁ b₂ : LayoutBox2D}
    (h₁ : (n₁, b₁) ∈ o.metalShapes) (h₂ : (n₂, b₂) ∈ o.metalShapes)
    (hLayer : b₁.layerId = b₂.layerId) (hDiffNet : n₁ ≠ n₂) :
    ∀ x y : Nat, ¬ (b₁.containsPoint x y ∧ b₂.containsPoint x y) := by
  have hMean : OpenPdkSignoffMeaning o c := openPdkSignoffJudge.sound hOk
  obtain ⟨rule, _, hSep⟩ := hMean.2.2.2.2.2.2.2.1 (n₁, b₁) h₁ (n₂, b₂) h₂ hLayer hDiffNet
  dsimp only at hSep
  intro x y ⟨hp1, hp2⟩
  dsimp [LayoutBox2D.containsPoint] at hp1 hp2
  have hPos : 1 ≤ max rule.minSpacingNm 1 := Nat.le_max_right _ _
  rcases hSep with hL | hR | hB | hT <;> omega

/-! ## 5. Token-wire byte codecs for `"vivado-sta@1"` and `"openpdk-drc-sta@1"`

The wire is whitespace-separated tokens: decimal naturals, integers with an optional `-`, names without
whitespace, and lists as a count followed by that many items. A decoder accepts only a wire it consumes whole. -/

def wireTokens : List Char → List Char → List (List Char)
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | c :: cs, cur =>
    if c == ' ' || c == '\n' then (if cur.isEmpty then wireTokens cs [] else cur.reverse :: wireTokens cs [])
    else wireTokens cs (c :: cur)
def tokNatGo : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc => if c.isDigit then tokNatGo cs (acc * 10 + (c.toNat - 48)) else none
def tokNat (t : List Char) : Option Nat := if t.isEmpty then none else tokNatGo t 0
def tokInt : List Char → Option Int
  | '-' :: t => (tokNat t).map fun n => -(n : Int)
  | t => (tokNat t).map Int.ofNat
abbrev WireRd (α : Type) := StateT (List (List Char)) Option α
def rdNat : WireRd Nat := fun ts => match ts with | t :: ts => (tokNat t).map (·, ts) | [] => none
def rdInt : WireRd Int := fun ts => match ts with | t :: ts => (tokInt t).map (·, ts) | [] => none
def rdStr : WireRd String := fun ts => match ts with | t :: ts => some (String.ofList t, ts) | [] => none
def rdMany {α : Type} (item : WireRd α) : Nat → WireRd (List α)
  | 0 => pure []
  | n + 1 => do let x ← item; let xs ← rdMany item n; pure (x :: xs)
def rdList {α : Type} (item : WireRd α) : WireRd (List α) := do let n ← rdNat; rdMany item n
def runWireRd {α : Type} (what : String) (r : WireRd α) (s : String) : Except String α :=
  match r (wireTokens s.toList []) with
  | some (x, []) => .ok x
  | _ => .error ("malformed " ++ what ++ " token wire")
/-- An accepted wire is one the reader consumed to its last token. -/
theorem runWireRd_consumes_all {α : Type} (what : String) (r : WireRd α) (s : String) (x : α)
    (h : runWireRd what r s = .ok x) : r (wireTokens s.toList []) = some (x, []) := by
  unfold runWireRd at h; split at h
  · rename_i y hEq; injection h with hxy; rw [hEq, hxy]
  · cases h
def wireOfTokens (ts : List String) : String := " ".intercalate ts
def rdSlr : WireRd SlrId := do
  match (← rdNat) with | 0 => pure .slr0 | 1 => pure .slr1 | 2 => pure .slr2 | _ => failure
def rdVivadoPath : WireRd VivadoPostRoutePath := do
  pure ⟨← rdStr, ← rdSlr, ← rdSlr, ← rdNat, ← rdInt, ← rdNat, ← rdNat, ← rdInt, ← rdNat⟩
def decodeVivadoStaObj : String → Except String VivadoStaSignoffObj :=
  runWireRd "vivado-sta object" do pure ⟨← rdStr, ← rdNat, ← rdNat, ← rdNat, ← rdList rdVivadoPath⟩
def decodeVivadoStaCert : String → Except String VivadoStaCert :=
  runWireRd "vivado-sta certificate" do pure ⟨← rdInt, ← rdInt, ← rdNat⟩
def encodeVivadoStaObj (o : VivadoStaSignoffObj) : String :=
  wireOfTokens ([o.targetDevice, toString o.clockPeriodPs, toString o.clockUncertaintyPs,
    toString o.sllCrossingPenaltyPs, toString o.paths.length] ++ o.paths.flatMap fun p =>
      [p.pathName, toString p.srcSlr.toIndex, toString p.dstSlr.toIndex, toString p.setupArrivalSsPs,
       toString p.setupSlackReportedSsPs, toString p.holdArrivalFfPs, toString p.holdReqFfPs,
       toString p.holdSlackReportedFfPs, toString p.ttArrivalPs])
def encodeVivadoStaCert (c : VivadoStaCert) : String :=
  wireOfTokens [toString c.worstSetupSlackPs, toString c.worstHoldSlackPs, toString c.maxSlrCrossings]
/-- Registered byte format `"vivado-sta@1"`; the planted report has a fast-corner hold violation. -/
def vivadoStaByteJudge : Obend.Judge.Format where
  name := "vivado-sta"
  version := "1"
  Obj := VivadoStaSignoffObj
  Cert := VivadoStaCert
  judge := vivadoPostRouteStaJudge
  decodeObj := decodeVivadoStaObj
  decodeCert := decodeVivadoStaCert
  trust := .kernel
  regime := .decidable
  bad := ({ paths := [⟨"hold_short", .slr0, .slr0, 2950, 335, 100, 110, 45, 2400⟩] }, sampleVivadoStaCert)
  badGrade := 8
  bad_refused := ⟨.holdViolationFF, [1], by
    change checkVivadoStaSignoff 8 { paths := [⟨"hold_short", .slr0, .slr0, 2950, 335, 100, 110, 45, 2400⟩] } _ = _
    decide +kernel⟩
def rdBox : WireRd LayoutBox2D := do pure ⟨← rdNat, ← rdNat, ← rdNat, ← rdNat, ← rdNat⟩
def rdLayerRule : WireRd LayerDrcRule := do pure ⟨← rdNat, ← rdStr, ← rdNat, ← rdNat⟩
def rdViaRule : WireRd ViaEnclosureRule := do pure ⟨← rdNat, ← rdNat, ← rdNat⟩
def rdCorner : WireRd OpenStaCornerSummary := do pure ⟨← rdStr, ← rdInt, ← rdInt, ← rdInt, ← rdInt, ← rdInt, ← rdInt⟩
def rdShape : WireRd (Nat × LayoutBox2D) := do pure (← rdNat, ← rdBox)
def rdViaCut : WireRd (LayoutBox2D × LayoutBox2D) := do pure (← rdBox, ← rdBox)
def rdPdkDeck : WireRd OpenPdkRuleDeck := do
  let node : OpenPdkNode ← (do match (← rdNat) with | 0 => pure .sky130 | 1 => pure .asap7 | _ => failure)
  pure ⟨node, ← rdNat, ← rdList rdLayerRule, ← rdList rdViaRule⟩
def decodeOpenPdkSignoffObj : String → Except String OpenPdkSignoffObj :=
  runWireRd "openpdk-drc-sta object" do
    pure ⟨← rdPdkDeck, ← rdList rdStr, ← rdList rdStr, ← rdList rdShape, ← rdList rdViaCut, ← rdList rdCorner⟩
def decodeOpenPdkSignoffCert : String → Except String OpenPdkSignoffCert :=
  runWireRd "openpdk-drc-sta certificate" do pure ⟨← rdList rdNat, ← rdList rdNat, ← rdInt, ← rdInt⟩
def boxTokens (b : LayoutBox2D) : List String :=
  [toString b.layerId, toString b.xMinNm, toString b.yMinNm, toString b.xMaxNm, toString b.yMaxNm]
def listTokens {α : Type} (item : α → List String) (xs : List α) : List String :=
  toString xs.length :: xs.flatMap item
def encodeOpenPdkSignoffObj (o : OpenPdkSignoffObj) : String :=
  wireOfTokens ([(match o.deck.node with | .sky130 => "0" | .asap7 => "1"), toString o.deck.nodeNm] ++
    listTokens (fun r => [toString r.layerId, r.layerName, toString r.minWidthNm, toString r.minSpacingNm]) o.deck.layerRules ++
    listTokens (fun r => [toString r.viaLayerId, toString r.metalLayerId, toString r.minEnclosureNm]) o.deck.viaRules ++
    listTokens (fun s => [s]) o.netlistPins ++ listTokens (fun s => [s]) o.defPorts ++
    listTokens (fun s => toString s.1 :: boxTokens s.2) o.metalShapes ++
    listTokens (fun v => boxTokens v.1 ++ boxTokens v.2) o.viaCuts ++
    listTokens (fun c => [c.pathGroup, toString c.ffWnsPs, toString c.ffWhsPs, toString c.ttWnsPs,
      toString c.ttWhsPs, toString c.ssWnsPs, toString c.ssWhsPs]) o.cornerReports)
def encodeOpenPdkSignoffCert (c : OpenPdkSignoffCert) : String :=
  wireOfTokens (listTokens (fun n => [toString n]) c.pinToDefIdx ++ listTokens (fun n => [toString n]) c.defToPinIdx ++
    [toString c.minWnsPs, toString c.minWhsPs])
/-- The clean Sky130 layout with its second `met1` shape moved to 50 nm from the first (rule: 140 nm). -/
def sky130SpacingViolationObj : OpenPdkSignoffObj :=
  { sampleSky130SignoffObj with
    metalShapes := [(0, ⟨1, 0, 0, 200, 200⟩), (1, ⟨1, 250, 0, 450, 200⟩)] }
/-- Registered byte format `"openpdk-drc-sta@1"`; the planted layout violates `met1` spacing. -/
def openpdkDrcStaByteJudge : Obend.Judge.Format where
  name := "openpdk-drc-sta"
  version := "1"
  Obj := OpenPdkSignoffObj
  Cert := OpenPdkSignoffCert
  judge := openPdkSignoffJudge
  decodeObj := decodeOpenPdkSignoffObj
  decodeCert := decodeOpenPdkSignoffCert
  trust := .kernel
  regime := .decidable
  bad := (sky130SpacingViolationObj, sampleSky130SignoffCert)
  badGrade := 20
  bad_refused := ⟨.metalSpacingViolation, [2], by
    change checkOpenPdkSignoff 20 sky130SpacingViolationObj sampleSky130SignoffCert = _; decide +kernel⟩
/-- Accepted `"vivado-sta@1"` bytes decode to a report and summary for which the STA meaning holds. -/
theorem vivadoStaByteJudge_sound {r : Nat} {obj cert : String} (h : vivadoStaByteJudge.checkBytes r obj cert = .ok) :
    ∃ o c, decodeVivadoStaObj obj = .ok o ∧ decodeVivadoStaCert cert = .ok c ∧ VivadoStaMeaning o c :=
  vivadoStaByteJudge.checkBytes_sound h
/-- Accepted `"openpdk-drc-sta@1"` bytes decode to a layout and certificate for which the signoff meaning holds. -/
theorem openpdkDrcStaByteJudge_sound {r : Nat} {obj cert : String} (h : openpdkDrcStaByteJudge.checkBytes r obj cert = .ok) :
    ∃ o c, decodeOpenPdkSignoffObj obj = .ok o ∧ decodeOpenPdkSignoffCert cert = .ok c ∧ OpenPdkSignoffMeaning o c :=
  openpdkDrcStaByteJudge.checkBytes_sound h
end Obend.Hardware.AwsF2Shell
end
