`include "obend_hw.sv"
`include "obend_silicon_process.sv"
`include "obend_efpga_fabric.sv"

module tb_top (
  input  logic        clk,
  input  logic        rst_n,
  // 1. DSP MAC ports
  input  logic [63:0] dsp_a,
  input  logic [63:0] dsp_b,
  input  logic [63:0] dsp_c,
  output logic [63:0] dsp_p,
  // 2. Boot-Sweep + RAW-Bypassed URAM/SRAM ports
  output logic        ram_boot_done,
  input  logic        ram_rd_en,
  input  logic [3:0]  ram_rd_addr,
  output logic [63:0] ram_rd_data,
  input  logic        ram_wr_en,
  input  logic [3:0]  ram_wr_addr,
  input  logic [63:0] ram_wr_data,
  // 3. AXI4-Stream Skid Buffer ports
  input  logic        s_tvalid,
  output logic        s_tready,
  input  logic [63:0] s_tdata,
  output logic        m_tvalid,
  input  logic        m_tready,
  output logic [63:0] m_tdata,
  // 4. Demand Wave Chip ports
  output logic [63:0] csr_afi_digest,
  output logic [3:0]  slot_valid,
  output logic [63:0] slot_val_0,
  output logic [63:0] slot_val_1,
  output logic [63:0] slot_val_2,
  output logic [63:0] slot_val_3,
  // 5. eFPGA 64-bit BLE Bitstream Adder ports
  input  logic [63:0] efpga_a,
  input  logic [63:0] efpga_b,
  output logic [63:0] efpga_sum,
  // 6. ReviewMember.obend 2-stage Pipeline ports
  input  logic [63:0] rev_x,
  input  logic [63:0] rev_base,
  output logic [63:0] rev_twice,
  output logic        rev_claim_ok,
  // 7. Hardware Ledger Co-Processor ports
  output logic        led_boot_done,
  input  logic        led_row_valid,
  input  logic        led_row_is_close,
  input  logic [3:0]  led_row_doc_id,
  input  logic [63:0] led_row_period,
  input  logic [63:0] led_row_debit,
  input  logic [63:0] led_row_credit,
  output logic        led_row_accepted,
  output logic [1:0]  led_refusal_code,
  output logic [63:0] led_closed_through,
  output logic [63:0] led_total_debits,
  output logic [63:0] led_total_credits,
  // 8. 2x2 eFPGA Mesh + Frame Loader (TwiceReview.obend) ports
  input  logic        mesh_cfg_wr_en,
  input  logic        mesh_cfg_lock_cmd,
  input  logic [1:0]  mesh_cfg_tile_id,
  input  logic [2:0]  mesh_cfg_mux_a,
  input  logic [2:0]  mesh_cfg_mux_b,
  input  logic [1:0]  mesh_cfg_alu_op,
  input  logic [63:0] mesh_cfg_imm,
  output logic        mesh_cfg_locked,
  input  logic [63:0] mesh_in_00,
  output logic [63:0] mesh_out_01,
  // 9. Hardware Merkle-View Receipt Verifier Engine ports
  input  logic [63:0] mrk_dated_root,
  input  logic [1:0]  mrk_leaf_pos,
  input  logic [63:0] mrk_leaf_val,
  input  logic [63:0] mrk_sib_0,
  input  logic [63:0] mrk_sib_1,
  input  logic        mrk_law_ok,
  output logic [63:0] mrk_climbed_root,
  output logic        mrk_accepted,
  // 10. DeosCounter.obend + Vault.Law Capability-Guarded Register Bank ports
  input  logic        deos_cmd_valid,
  input  logic [1:0]  deos_cmd_op,
  input  logic [63:0] deos_cmd_arg,
  input  logic        deos_has_cred,
  output logic [63:0] deos_count,
  output logic [63:0] deos_cfg_tag,
  output logic        deos_accepted
);
  logic [63:0] slot_val [0:3];
  assign slot_val_0 = slot_val[0];
  assign slot_val_1 = slot_val[1];
  assign slot_val_2 = slot_val[2];
  assign slot_val_3 = slot_val[3];
  assign led_boot_done = rst_n;

  obend_dsp_mac4 u_dsp (
    .clk(clk), .a_in(dsp_a), .b_in(dsp_b), .c_in(dsp_c), .p_out(dsp_p)
  );

  obend_boot_sweep_ram #(.ADDR_W(4), .DATA_W(64), .DEPTH(16)) u_ram (
    .clk(clk), .rst_n(rst_n), .boot_done(ram_boot_done),
    .rd_en(ram_rd_en), .rd_addr(ram_rd_addr), .rd_data(ram_rd_data),
    .wr_en(ram_wr_en), .wr_addr(ram_wr_addr), .wr_data(ram_wr_data)
  );

  obend_axis_skid #(.W(64)) u_skid (
    .clk(clk), .rst_n(rst_n),
    .s_axis_tvalid(s_tvalid), .s_axis_tready(s_tready), .s_axis_tdata(s_tdata),
    .m_axis_tvalid(m_tvalid), .m_axis_tready(m_tready), .m_axis_tdata(m_tdata)
  );

  obend_chain4_chip u_wave (
    .clk(clk), .rst_n(rst_n),
    .csr_afi_digest(csr_afi_digest), .slot_valid(slot_valid), .slot_val(slot_val)
  );

  obend_efpga_adder64 u_efpga_add (
    .a(efpga_a), .b(efpga_b), .sum(efpga_sum)
  );

  obend_review_member_pipe u_rev_pipe (
    .clk(clk), .x_in(rev_x), .base_in(rev_base),
    .twice_out(rev_twice), .claim_repeated_ok(rev_claim_ok)
  );

  obend_ledger_coproc u_ledger (
    .clk(clk), .rst_n(rst_n),
    .row_valid(led_row_valid), .row_is_close(led_row_is_close),
    .row_doc_id(led_row_doc_id), .row_period(led_row_period),
    .row_debit(led_row_debit), .row_credit(led_row_credit),
    .row_accepted(led_row_accepted), .refusal_code(led_refusal_code),
    .closed_through_out(led_closed_through),
    .total_debits_out(led_total_debits), .total_credits_out(led_total_credits)
  );

  obend_efpga_mesh_2x2 u_mesh (
    .clk(clk), .rst_n(rst_n),
    .cfg_wr_en(mesh_cfg_wr_en), .cfg_lock_cmd(mesh_cfg_lock_cmd),
    .cfg_tile_id(mesh_cfg_tile_id), .cfg_mux_a_in(mesh_cfg_mux_a),
    .cfg_mux_b_in(mesh_cfg_mux_b), .cfg_alu_op_in(mesh_cfg_alu_op),
    .cfg_imm_in(mesh_cfg_imm), .cfg_locked(mesh_cfg_locked),
    .mesh_in_00(mesh_in_00), .mesh_out_01(mesh_out_01)
  );

  obend_merkle_receipt_engine u_merkle (
    .dated_root(mrk_dated_root), .leaf_pos(mrk_leaf_pos),
    .leaf_val(mrk_leaf_val), .sib_0(mrk_sib_0), .sib_1(mrk_sib_1),
    .law_ok(mrk_law_ok), .climbed_root(mrk_climbed_root),
    .receipt_accepted(mrk_accepted)
  );

  obend_deos_vault_guard u_deos (
    .clk(clk), .rst_n(rst_n),
    .cmd_valid(deos_cmd_valid), .cmd_op(deos_cmd_op),
    .cmd_arg(deos_cmd_arg), .has_proof_cred(deos_has_cred),
    .count_out(deos_count), .cfg_tag_out(deos_cfg_tag),
    .last_accepted_out(deos_accepted)
  );
endmodule
