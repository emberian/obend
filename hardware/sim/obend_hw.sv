// Verified by Obend.Hardware.dspMac_latency_4 (4-cycle reset-free DSP48E2/DSP58/ASIC MAC)
(* use_dsp = "yes", keep_hierarchy = "soft" *)
module obend_dsp_mac4 #(
  parameter int W = 64
) (
  input  logic         clk,
  input  logic [W-1:0] a_in,
  input  logic [W-1:0] b_in,
  input  logic [W-1:0] c_in,
  output logic [W-1:0] p_out
);
  logic [W-1:0] a1, b1, a2, b2, c2, mreg, c3, preg;
  always_ff @(posedge clk) begin
    a1   <= a_in;
    b1   <= b_in;
    a2   <= a1;
    b2   <= b1;
    c2   <= c_in;
    mreg <= a2 * b2;
    c3   <= c2;
    preg <= mreg + c3;
  end
  assign p_out = preg;
endmodule

// Verified by Obend.Hardware.bootSweep_clears_all & bypassRAM_exact_latest_write
(* keep_hierarchy = "soft" *)
module obend_boot_sweep_ram #(
  parameter int ADDR_W = 4,
  parameter int DATA_W = 64,
  parameter int DEPTH  = 16
) (
  input  logic              clk,
  input  logic              rst_n,
  output logic              boot_done,
  input  logic              rd_en,
  input  logic [ADDR_W-1:0] rd_addr,
  output logic [DATA_W-1:0] rd_data,
  input  logic              wr_en,
  input  logic [ADDR_W-1:0] wr_addr,
  input  logic [DATA_W-1:0] wr_data
);
  // Physical unreset SRAM / URAM288 array (never cleared by rst_n!)
  (* ram_style = "ultra" *)
  logic [DATA_W-1:0] mem [0:DEPTH-1];
  logic [DATA_W-1:0] ram_dout;

  // Hardware Boot Zero-Sweep FSM (CtrlReg with sync reset)
  logic [ADDR_W:0] boot_cursor;
  assign boot_done = boot_cursor[ADDR_W];

  wire eff_wr_en               = (!boot_done) ? 1'b1 : wr_en;
  wire [ADDR_W-1:0] eff_wr_addr = (!boot_done) ? boot_cursor[ADDR_W-1:0] : wr_addr;
  wire [DATA_W-1:0] eff_wr_data = (!boot_done) ? '0 : wr_data;

  // RAW collision detector & physical read gating (prevents RDW bitline contention)
  wire collision  = boot_done && rd_en && wr_en && (rd_addr == wr_addr);
  wire phys_rd_en = boot_done && rd_en && !collision;

  logic              bypass_active;
  logic [DATA_W-1:0] bypass_data;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      boot_cursor   <= '0;
      bypass_active <= 1'b0;
    end else begin
      if (!boot_done)
        boot_cursor <= boot_cursor + 1'b1;
      bypass_active <= collision;
    end
  end

  // Unreset datapath & SRAM macro process (UG901 / ASIC ICG compliant)
  always_ff @(posedge clk) begin
    if (eff_wr_en)
      mem[eff_wr_addr] <= eff_wr_data;
    if (phys_rd_en)
      ram_dout <= mem[rd_addr];
    if (collision)
      bypass_data <= wr_data;
  end

  assign rd_data = bypass_active ? bypass_data : ram_dout;
endmodule

// Verified by Obend.Hardware.stepSkid_queue_conserved (0-comb-tready 2-slot AXI4-Stream Skid Buffer)
(* keep_hierarchy = "soft" *)
module obend_axis_skid #(
  parameter int W = 64
) (
  input  logic         clk,
  input  logic         rst_n,
  input  logic         s_axis_tvalid,
  output logic         s_axis_tready,
  input  logic [W-1:0] s_axis_tdata,
  output logic         m_axis_tvalid,
  input  logic         m_axis_tready,
  output logic [W-1:0] m_axis_tdata
);
  logic         p_valid, s_valid;
  logic [W-1:0] p_data,  s_data;

  assign s_axis_tready = !s_valid;
  assign m_axis_tvalid = p_valid;
  assign m_axis_tdata  = p_data;

  wire accept = s_axis_tvalid && s_axis_tready;
  wire drain  = p_valid && m_axis_tready;

  // Control registers (with synchronous reset)
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      p_valid <= 1'b0;
      s_valid <= 1'b0;
    end else if (s_valid) begin
      if (drain) begin
        p_valid <= 1'b1;
        s_valid <= 1'b0;
      end
    end else begin
      if (!p_valid || drain) begin
        p_valid <= accept;
        s_valid <= 1'b0;
      end else begin
        p_valid <= 1'b1;
        s_valid <= accept;
      end
    end
  end

  // Datapath registers (NO reset -> maps to compact ASIC DFFQ + ICG clock gate / FPGA FDRE)
  always_ff @(posedge clk) begin
    if (s_valid) begin
      if (drain)
        p_data <= s_data;
    end else begin
      if ((!p_valid || drain) && accept)
        p_data <= s_axis_tdata;
      else if (p_valid && !drain && accept)
        s_data <= s_axis_tdata;
    end
  end
endmodule

// Verified by Obend.Hardware.pipe2_x_free & slr_crossing_has_laguna_pair
(* keep_hierarchy = "soft" *)
module obend_laguna_pipe2 #(
  parameter int W = 64
) (
  input  logic         clk,
  input  logic [W-1:0] d_in,
  output logic [W-1:0] d_out
);
  (* dont_touch = "true", shreg_extract = "no" *) logic [W-1:0] tx_reg;
  (* dont_touch = "true", shreg_extract = "no" *) logic [W-1:0] rx_reg;
  always_ff @(posedge clk) begin
    tx_reg <= d_in;
    rx_reg <= tx_reg;
  end
  assign d_out = rx_reg;
endmodule

// Verified by Obend.Hardware.chip_computes_demand & chip_never_valid_of_divergent
(* keep_hierarchy = "soft" *)
module obend_chain4_chip (
  input  logic        clk,
  input  logic        rst_n,
  output logic [63:0] csr_afi_digest,
  output logic [3:0] slot_valid,
  output logic [63:0] slot_val [0:3]
);
  assign csr_afi_digest = 64'd3405691582;

  // Control registers (CtrlReg: synchronous reset to 0)
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      slot_valid <= '0;
    end else begin
      slot_valid[0] <= 1'b1;
      slot_valid[1] <= slot_valid[1] | slot_valid[0];
      slot_valid[2] <= slot_valid[2] | slot_valid[1];
      slot_valid[3] <= slot_valid[3] | slot_valid[3];
    end
  end

  // Datapath registers (DataReg: NO reset! Clock-gated by (!slot_valid[i] && dep_valid))
  always_ff @(posedge clk) begin
    if (!slot_valid[0]) slot_val[0] <= 64'd42;
    if (!slot_valid[1] && slot_valid[0]) slot_val[1] <= slot_val[0];
    if (!slot_valid[2] && slot_valid[1]) slot_val[2] <= slot_val[1];
    if (!slot_valid[3] && slot_valid[3]) slot_val[3] <= slot_val[3];
  end
endmodule
