/* verilator lint_off UNUSED */
/* verilator lint_off DECLFILENAME */
/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off UNSIGNED */
// =============================================================================
// AWS EC2 F2 (`xcvu47p-fsvh2892-2-e`) Custom Logic Shell Bridge (`cl_obend_shell_bridge`)
// =============================================================================
// Bridges:
//   1. `sh_ocl_*` 32-bit BAR0 AXI4-Lite CSR Aperture (`0x0000..0x04FF`):
//      - `0x0000..0x00FF`: `OBEND_MAGIC` ("OBENDF20" = 64'h3032_4644_4E45_424F),
//        `OBEND_VERSION_CAPS`, `OBEND_CTRL` (`AP_START`, `AP_DONE`, `SOFT_RST`,
//        `STEP_ONCE`, `DPR_ISOLATE_EN`), `OBEND_CYCLE_COUNT`, `DMA_TX_RING`, `DMA_RX_RING`
//      - `0x0100..0x03FF`: `OBEND_IN_PORT[0..31]`, `OBEND_OUT_PORT[0..31]`,
//        `OBEND_STATE_SNAP[0..31]` (`always_ff` state readback), `OBEND_DPR_SLOT_GUARD_PIN`
//      - `0x0400..0x04FF`: `SILICON_CTRL_STATUS`, `TARGET_EXPR_H`, `TARGET_TYPE_H`,
//        `TARGET_DECL_SYM`, `FUEL_BUDGET`, `RESULT_STATUS`, `PERF_CYCLES`,
//        `PERF_CAM_HITS`, `PERF_CAM_ALLOCS`, `PERF_BYPASS_CNT`, `PERF_NOC_FLITS`,
//        `PERF_LUT_HITS`, `ZONE3_MATCH_THM`
//   2. `sh_pcis_*` 512-bit AXI4-Stream DMA (`OBCAMv1` wire frame `\0OBCAMV1` =
//      64'h3156_4D41_4342_4F00 + ICAP DPR frame beats)
//   3. Instantiates `silicon_elab_top` (4-zone Silicon Elaborator Fabric + ICAP DPR)
//      and the compiled `.obend` physical cores (`cleanroom_tcad_stack`,
//      `lc_drives_userspace_stator`, `cnc_5axis_userspace_mill`).
// =============================================================================

`include "../sim/cleanroom_tcad_stack.sv"
`include "../sim/lc_drives_userspace_stator.sv"
`include "../sim/cnc_5axis_userspace_mill.sv"
`include "../sim/silicon_elab_top.sv"

module cl_obend_shell_bridge (
  input  logic         clk_main_a0,
  input  logic         rst_main_n,

  // AWS F2 Shell OCL BAR0 AXI4-Lite Slave Interface (`0x0000..0x04FF`)
  input  logic         sh_ocl_awvalid,
  input  logic [31:0]  sh_ocl_awaddr,
  output logic         ocl_sh_awready,
  input  logic         sh_ocl_wvalid,
  input  logic [31:0]  sh_ocl_wdata,
  input  logic [3:0]   sh_ocl_wstrb,
  output logic         ocl_sh_wready,
  output logic         ocl_sh_bvalid,
  output logic [1:0]   ocl_sh_bresp,
  input  logic         sh_ocl_bready,
  input  logic         sh_ocl_arvalid,
  input  logic [31:0]  sh_ocl_araddr,
  output logic         ocl_sh_arready,
  output logic         ocl_sh_rvalid,
  output logic [31:0]  ocl_sh_rdata,
  output logic [1:0]   ocl_sh_rresp,
  input  logic         sh_ocl_rready,

  // AWS F2 Shell PCIS 512-bit AXI4-Stream H2C (Host-to-Card) & C2H (Card-to-Host) DMA
  input  logic         sh_pcis_h2c_tvalid,
  output logic         pcis_sh_h2c_tready,
  input  logic [511:0] sh_pcis_h2c_tdata,
  input  logic [63:0]  sh_pcis_h2c_tkeep,
  input  logic         sh_pcis_h2c_tlast,

  output logic         pcis_sh_c2h_tvalid,
  input  logic         sh_pcis_c2h_tready,
  output logic [511:0] pcis_sh_c2h_tdata,
  output logic [63:0]  pcis_sh_c2h_tkeep,
  output logic         pcis_sh_c2h_tlast
);

  localparam logic [63:0] OBEND_MAGIC_CONST   = 64'h3032_4644_4E45_424F; // "OBENDF20"
  localparam logic [63:0] OBEND_VER_CAPS      = 64'h0001_0004_0020_0200; // v1, 4 zones, 32 ports, 512b DMA
  localparam logic [63:0] OBCAMV1_WIRE_MAGIC  = 64'h3156_4D41_4342_4F00; // "\0OBCAMV1"

  logic clk, rst;
  assign clk = clk_main_a0;
  assign rst = !rst_main_n || ctrl_soft_rst;

  // Control & BAR0 Register File
  logic [31:0] reg_ctrl;
  logic [63:0] reg_cycle_count;
  logic [63:0] reg_dma_tx_ring;
  logic [63:0] reg_dma_rx_ring;
  logic [63:0] reg_in_port  [0:31];
  logic [63:0] reg_out_port [0:31];
  logic [63:0] reg_state_snap [0:31];
  logic [31:0] reg_dpr_slot_guard_pin;
  logic [63:0] reg_dpr_expected_digest;
  logic [63:0] reg_dpr_computed_digest;
  logic [63:0] reg_dpr_frame_word;
  logic        reg_dpr_load_we;

  // Zone 4 / Silicon Elaborator CSRs (`0x0400..0x04FF`)
  logic [31:0] reg_silicon_ctrl;
  logic [31:0] reg_target_expr_h;
  logic [31:0] reg_target_type_h;
  logic [31:0] reg_target_decl_sym;
  logic [31:0] reg_fuel_budget;

  logic ctrl_ap_start, ctrl_soft_rst, ctrl_step_once, ctrl_dpr_isolate_en;
  assign ctrl_ap_start       = reg_ctrl[0] || reg_silicon_ctrl[0];
  assign ctrl_soft_rst       = reg_ctrl[2];
  assign ctrl_step_once      = reg_ctrl[3];
  assign ctrl_dpr_isolate_en = reg_ctrl[4];

  // Outputs from Silicon Elaborator Top
  logic        elab_ap_done, elab_ap_idle;
  logic [31:0] elab_result_status;
  logic [31:0] elab_perf_cycles, elab_perf_cam_hits, elab_perf_cam_allocs;
  logic [31:0] elab_perf_bypass_cnt, elab_perf_noc_flits, elab_perf_lut_hits;
  logic [31:0] elab_zone3_match_thm;
  logic        elab_dpr_commit_ok, elab_dpr_fallback_active;

  // Outputs from Compiled `.obend` Physical Cores
  logic [63:0] tcad_oxide, tcad_vth, tcad_idrain, tcad_gdelay, tcad_cdelay;
  logic [63:0] stator_mass, stator_cam, stator_rth, stator_sdf, stator_temp;
  logic [63:0] mill_slag, mill_defl, mill_abbe, mill_cmd, mill_vol;

  cleanroom_tcad_stack u_cl_tcad (
    .clk(clk),
    .rst(rst),
    .arg(reg_in_port[0]),
    .out_oxideEotPicometers(tcad_oxide),
    .out_vthMilliV(tcad_vth),
    .out_drainCurrentUa(tcad_idrain),
    .out_gateDelayPs(tcad_gdelay),
    .out_calibratedDelayPs(tcad_cdelay)
  );

  lc_drives_userspace_stator u_cl_stator (
    .clk(clk),
    .rst(rst),
    .arg(reg_in_port[1]),
    .out_massKg(stator_mass),
    .out_camSurfaceErrorUm(stator_cam),
    .out_thermalResistance(stator_rth),
    .out_sdfMargin(stator_sdf),
    .out_peakWindingTemp(stator_temp)
  );

  cnc_5axis_userspace_mill u_cl_mill (
    .clk(clk),
    .rst(rst),
    .arg(reg_in_port[2]),
    .out_servoLagUm(mill_slag),
    .out_endMillDeflectionUm(mill_defl),
    .out_abbeAngularDriftUm(mill_abbe),
    .out_commandedAxisAt10mmUm(mill_cmd),
    .out_totalVolumetricErrorUm(mill_vol)
  );

  silicon_elab_top u_cl_silicon_elab (
    .clk(clk),
    .rst(rst),
    .ap_start(ctrl_ap_start),
    .dpr_isolate_en(ctrl_dpr_isolate_en),
    .dpr_load_we(reg_dpr_load_we),
    .dpr_frame_word(reg_dpr_frame_word),
    .dpr_expected_digest(reg_dpr_expected_digest),
    .dpr_computed_digest(reg_dpr_computed_digest),
    .dpr_moved_pin(reg_dpr_slot_guard_pin[0]),
    .target_expr_h(reg_target_expr_h),
    .target_type_h(reg_target_type_h),
    .target_decl_sym(reg_target_decl_sym),
    .fuel_budget(reg_fuel_budget),
    .ap_done(elab_ap_done),
    .ap_idle(elab_ap_idle),
    .result_status(elab_result_status),
    .perf_cycles(elab_perf_cycles),
    .perf_cam_hits(elab_perf_cam_hits),
    .perf_cam_allocs(elab_perf_cam_allocs),
    .perf_bypass_cnt(elab_perf_bypass_cnt),
    .perf_noc_flits(elab_perf_noc_flits),
    .perf_lut_hits(elab_perf_lut_hits),
    .zone3_match_thm(elab_zone3_match_thm),
    .dpr_commit_ok(elab_dpr_commit_ok),
    .dpr_fallback_active(elab_dpr_fallback_active)
  );

  // 512-bit AXI4-Stream Skid Buffer for H2C DMA (`OBCAMv1` frames)
  logic         h2c_skid_valid, h2c_skid_ready;
  logic [511:0] h2c_skid_data;

  obend_macro_axis_skid #(.DATA_BITS(512)) u_pcis_h2c_skid (
    .clk(clk),
    .rst(rst),
    .s_valid(sh_pcis_h2c_tvalid),
    .s_ready(pcis_sh_h2c_tready),
    .s_data(sh_pcis_h2c_tdata),
    .m_valid(h2c_skid_valid),
    .m_ready(h2c_skid_ready),
    .m_data(h2c_skid_data)
  );

  assign h2c_skid_ready = 1'b1;

  // Map outputs & state snapshot registers
  always_comb begin
    for (int i = 0; i < 32; i++) begin
      reg_out_port[i]   = 64'd0;
      reg_state_snap[i] = 64'd0;
    end
    reg_out_port[0]  = tcad_oxide;
    reg_out_port[1]  = tcad_vth;
    reg_out_port[2]  = tcad_idrain;
    reg_out_port[3]  = tcad_gdelay;
    reg_out_port[4]  = tcad_cdelay;
    reg_out_port[5]  = stator_mass;
    reg_out_port[6]  = stator_cam;
    reg_out_port[7]  = stator_rth;
    reg_out_port[8]  = stator_sdf;
    reg_out_port[9]  = stator_temp;
    reg_out_port[10] = mill_slag;
    reg_out_port[11] = mill_defl;
    reg_out_port[12] = mill_abbe;
    reg_out_port[13] = mill_cmd;
    reg_out_port[14] = mill_vol;

    reg_state_snap[0] = tcad_oxide;
    reg_state_snap[1] = tcad_vth;
    reg_state_snap[2] = tcad_idrain;
    reg_state_snap[3] = tcad_gdelay;
    reg_state_snap[4] = tcad_cdelay;
  end

  // AXI4-Lite Write & Read FSM + 512-bit `OBCAMv1` H2C Header Decoder
  assign ocl_sh_awready = 1'b1;
  assign ocl_sh_wready  = 1'b1;
  assign ocl_sh_bresp   = 2'b00;
  assign ocl_sh_arready = 1'b1;
  assign ocl_sh_rresp   = 2'b00;

  always_ff @(posedge clk) begin
    if (!rst_main_n) begin
      reg_ctrl                <= 32'd0;
      reg_cycle_count         <= 64'd0;
      reg_dma_tx_ring         <= 64'd0;
      reg_dma_rx_ring         <= 64'd0;
      reg_dpr_slot_guard_pin  <= 32'd0;
      reg_dpr_expected_digest <= 64'd0;
      reg_dpr_computed_digest <= 64'd0;
      reg_dpr_frame_word      <= 64'd0;
      reg_dpr_load_we         <= 1'b0;
      reg_silicon_ctrl        <= 32'd0;
      reg_target_expr_h       <= 32'd1;
      reg_target_type_h       <= 32'd1;
      reg_target_decl_sym     <= 32'd1;
      reg_fuel_budget         <= 32'd1024;
      ocl_sh_bvalid           <= 1'b0;
      ocl_sh_rvalid           <= 1'b0;
      ocl_sh_rdata            <= 32'd0;
      pcis_sh_c2h_tvalid      <= 1'b0;
      pcis_sh_c2h_tdata       <= 512'd0;
      pcis_sh_c2h_tkeep       <= 64'hFFFF_FFFF_FFFF_FFFF;
      pcis_sh_c2h_tlast       <= 1'b1;
      for (int i = 0; i < 32; i++) begin
        reg_in_port[i] <= 64'd0;
      end
    end else begin
      reg_cycle_count <= reg_cycle_count + 64'd1;
      reg_dpr_load_we <= 1'b0;

      // Decode 512-bit AXI4-Stream H2C beat when `OBCAMv1` magic matches
      if (h2c_skid_valid) begin
        if (h2c_skid_data[63:0] == OBCAMV1_WIRE_MAGIC) begin
          reg_target_expr_h   <= h2c_skid_data[95:64];
          reg_target_type_h   <= h2c_skid_data[127:96];
          reg_target_decl_sym <= h2c_skid_data[159:128];
          reg_fuel_budget     <= h2c_skid_data[191:160];
          reg_silicon_ctrl    <= 32'd1;
        end else if (ctrl_dpr_isolate_en) begin
          reg_dpr_frame_word      <= h2c_skid_data[63:0];
          reg_dpr_expected_digest <= h2c_skid_data[127:64];
          reg_dpr_computed_digest <= h2c_skid_data[191:128];
          reg_dpr_load_we         <= 1'b1;
        end
      end

      // AXI4-Lite Write Channel
      if (sh_ocl_awvalid && sh_ocl_wvalid) begin
        ocl_sh_bvalid <= 1'b1;
        case (sh_ocl_awaddr[11:0])
          12'h010: reg_ctrl               <= sh_ocl_wdata;
          12'h020: reg_dma_tx_ring[31:0]  <= sh_ocl_wdata;
          12'h024: reg_dma_tx_ring[63:32] <= sh_ocl_wdata;
          12'h028: reg_dma_rx_ring[31:0]  <= sh_ocl_wdata;
          12'h02C: reg_dma_rx_ring[63:32] <= sh_ocl_wdata;
          12'h030: reg_dpr_slot_guard_pin <= sh_ocl_wdata;
          12'h400: reg_silicon_ctrl       <= sh_ocl_wdata;
          12'h404: reg_target_expr_h      <= sh_ocl_wdata;
          12'h408: reg_target_type_h      <= sh_ocl_wdata;
          12'h40C: reg_target_decl_sym    <= sh_ocl_wdata;
          12'h410: reg_fuel_budget        <= sh_ocl_wdata;
          default: begin
            if (sh_ocl_awaddr[11:0] >= 12'h100 && sh_ocl_awaddr[11:0] < 12'h200) begin
              logic [4:0] port_idx;
              port_idx = sh_ocl_awaddr[7:3];
              if (sh_ocl_awaddr[2])
                reg_in_port[port_idx][63:32] <= sh_ocl_wdata;
              else
                reg_in_port[port_idx][31:0]  <= sh_ocl_wdata;
            end
          end
        endcase
      end else if (sh_ocl_bready) begin
        ocl_sh_bvalid <= 1'b0;
      end

      // AXI4-Lite Read Channel
      if (sh_ocl_arvalid) begin
        ocl_sh_rvalid <= 1'b1;
        case (sh_ocl_araddr[11:0])
          12'h000: ocl_sh_rdata <= OBEND_MAGIC_CONST[31:0];
          12'h004: ocl_sh_rdata <= OBEND_MAGIC_CONST[63:32];
          12'h008: ocl_sh_rdata <= OBEND_VER_CAPS[31:0];
          12'h00C: ocl_sh_rdata <= OBEND_VER_CAPS[63:32];
          12'h010: ocl_sh_rdata <= {26'd0, elab_dpr_fallback_active, ctrl_dpr_isolate_en, ctrl_step_once, ctrl_soft_rst, elab_ap_done, ctrl_ap_start};
          12'h018: ocl_sh_rdata <= reg_cycle_count[31:0];
          12'h01C: ocl_sh_rdata <= reg_cycle_count[63:32];
          12'h020: ocl_sh_rdata <= reg_dma_tx_ring[31:0];
          12'h024: ocl_sh_rdata <= reg_dma_tx_ring[63:32];
          12'h028: ocl_sh_rdata <= reg_dma_rx_ring[31:0];
          12'h02C: ocl_sh_rdata <= reg_dma_rx_ring[63:32];
          12'h030: ocl_sh_rdata <= reg_dpr_slot_guard_pin;
          12'h400: ocl_sh_rdata <= {29'd0, elab_dpr_fallback_active, elab_ap_done, ctrl_ap_start};
          12'h404: ocl_sh_rdata <= reg_target_expr_h;
          12'h408: ocl_sh_rdata <= reg_target_type_h;
          12'h40C: ocl_sh_rdata <= reg_target_decl_sym;
          12'h410: ocl_sh_rdata <= reg_fuel_budget;
          12'h414: ocl_sh_rdata <= elab_result_status;
          12'h418: ocl_sh_rdata <= elab_perf_cycles;
          12'h41C: ocl_sh_rdata <= elab_perf_cam_hits;
          12'h420: ocl_sh_rdata <= elab_perf_cam_allocs;
          12'h424: ocl_sh_rdata <= elab_perf_bypass_cnt;
          12'h428: ocl_sh_rdata <= elab_perf_noc_flits;
          12'h42C: ocl_sh_rdata <= elab_perf_lut_hits;
          12'h430: ocl_sh_rdata <= elab_zone3_match_thm;
          default: begin
            if (sh_ocl_araddr[11:0] >= 12'h100 && sh_ocl_araddr[11:0] < 12'h200) begin
              logic [4:0] idx;
              idx = sh_ocl_araddr[7:3];
              ocl_sh_rdata <= sh_ocl_araddr[2] ? reg_in_port[idx][63:32] : reg_in_port[idx][31:0];
            end else if (sh_ocl_araddr[11:0] >= 12'h200 && sh_ocl_araddr[11:0] < 12'h300) begin
              logic [4:0] idx;
              idx = sh_ocl_araddr[7:3];
              ocl_sh_rdata <= sh_ocl_araddr[2] ? reg_out_port[idx][63:32] : reg_out_port[idx][31:0];
            end else if (sh_ocl_araddr[11:0] >= 12'h300 && sh_ocl_araddr[11:0] < 12'h400) begin
              logic [4:0] idx;
              idx = sh_ocl_araddr[7:3];
              ocl_sh_rdata <= sh_ocl_araddr[2] ? reg_state_snap[idx][63:32] : reg_state_snap[idx][31:0];
            end else begin
              ocl_sh_rdata <= 32'hDEAD_BEEF;
            end
          end
        endcase
      end else if (sh_ocl_rready) begin
        ocl_sh_rvalid <= 1'b0;
      end

      // C2H 512-bit telemetry response beat on completion
      if (elab_ap_done && !pcis_sh_c2h_tvalid) begin
        pcis_sh_c2h_tvalid <= 1'b1;
        pcis_sh_c2h_tdata  <= {
          224'd0,
          elab_zone3_match_thm,
          elab_perf_lut_hits,
          elab_perf_noc_flits,
          elab_perf_bypass_cnt,
          elab_perf_cam_allocs,
          elab_perf_cam_hits,
          elab_perf_cycles,
          elab_result_status,
          OBCAMV1_WIRE_MAGIC
        };
      end else if (sh_pcis_c2h_tready && pcis_sh_c2h_tvalid) begin
        pcis_sh_c2h_tvalid <= 1'b0;
      end
    end
  end

endmodule
