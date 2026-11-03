module obend_risc_cpu (
  input  logic        clk,
  input  logic        rst,
  input  logic [63:0] imem_rdata,
  input  logic [63:0] dmem_rdata,
  output logic [63:0] imem_addr,
  output logic [63:0] dmem_addr,
  output logic [63:0] dmem_wdata,
  output logic [63:0] dmem_we,
  output logic [63:0] pc_out,
  output logic [63:0] mstatus_out,
  output logic [63:0] mepc_out,
  output logic [63:0] mcause_out,
  output logic [63:0] cycle_cnt_out,
  output logic [63:0] x1_out,
  output logic [63:0] x2_out,
  output logic [63:0] x3_out,
  output logic [63:0] x4_out,
  output logic [63:0] x5_out,
  output logic [63:0] x6_out,
  output logic [63:0] x7_out,
  output logic [63:0] x8_out,
  output logic [63:0] x9_out,
  output logic [63:0] x10_out,
  output logic [63:0] x11_out,
  output logic [63:0] x12_out,
  output logic [63:0] x13_out,
  output logic [63:0] x14_out,
  output logic [63:0] x15_out
);
  logic [63:0] w_0; // opcode
  logic [63:0] w_1; // rd
  logic [63:0] w_2; // funct3
  logic [63:0] w_3; // rs1
  logic [63:0] w_4; // rs2
  logic [63:0] w_5; // imm12
  logic [63:0] w_6; // funct7
  logic [63:0] w_7; // rs1_val
  logic [63:0] w_8; // rs2_val
  logic [63:0] w_9; // is_trap
  logic [63:0] w_10; // is_mret
  logic [63:0] w_11; // is_custom_ext
  logic [63:0] w_12; // base_alu_rhs
  logic [63:0] w_13; // base_alu_out
  logic [63:0] w_14; // custom_ext_out
  logic [63:0] w_15; // wb_val
  logic [63:0] w_16; // wb_en
  logic [63:0] w_17; // next_pc
  logic [63:0] w_18; // dmem_addr_w
  logic [63:0] w_19; // dmem_we_w
  logic [63:0] pc;
  logic [63:0] mstatus;
  logic [63:0] mepc;
  logic [63:0] mcause;
  logic [63:0] cycle_cnt;
  logic [63:0] x1;
  logic [63:0] x2;
  logic [63:0] x3;
  logic [63:0] x4;
  logic [63:0] x5;
  logic [63:0] x6;
  logic [63:0] x7;
  logic [63:0] x8;
  logic [63:0] x9;
  logic [63:0] x10;
  logic [63:0] x11;
  logic [63:0] x12;
  logic [63:0] x13;
  logic [63:0] x14;
  logic [63:0] x15;
  always_comb begin
    w_0 = (imem_rdata & 64'd127);
    w_1 = ((imem_rdata >> 64'd7) & 64'd31);
    w_2 = ((imem_rdata >> 64'd12) & 64'd7);
    w_3 = ((imem_rdata >> 64'd15) & 64'd31);
    w_4 = ((imem_rdata >> 64'd20) & 64'd31);
    w_5 = ((imem_rdata >> 64'd20) & 64'd4095);
    w_6 = ((imem_rdata >> 64'd25) & 64'd127);
    w_7 = (((w_3 == 64'd1 ? 64'd1 : 64'd0) != 64'd0) ? x1 : (((w_3 == 64'd2 ? 64'd1 : 64'd0) != 64'd0) ? x2 : (((w_3 == 64'd3 ? 64'd1 : 64'd0) != 64'd0) ? x3 : (((w_3 == 64'd4 ? 64'd1 : 64'd0) != 64'd0) ? x4 : (((w_3 == 64'd5 ? 64'd1 : 64'd0) != 64'd0) ? x5 : (((w_3 == 64'd6 ? 64'd1 : 64'd0) != 64'd0) ? x6 : (((w_3 == 64'd7 ? 64'd1 : 64'd0) != 64'd0) ? x7 : (((w_3 == 64'd8 ? 64'd1 : 64'd0) != 64'd0) ? x8 : (((w_3 == 64'd9 ? 64'd1 : 64'd0) != 64'd0) ? x9 : (((w_3 == 64'd10 ? 64'd1 : 64'd0) != 64'd0) ? x10 : (((w_3 == 64'd11 ? 64'd1 : 64'd0) != 64'd0) ? x11 : (((w_3 == 64'd12 ? 64'd1 : 64'd0) != 64'd0) ? x12 : (((w_3 == 64'd13 ? 64'd1 : 64'd0) != 64'd0) ? x13 : (((w_3 == 64'd14 ? 64'd1 : 64'd0) != 64'd0) ? x14 : (((w_3 == 64'd15 ? 64'd1 : 64'd0) != 64'd0) ? x15 : 64'd0)))))))))))))));
    w_8 = (((w_4 == 64'd1 ? 64'd1 : 64'd0) != 64'd0) ? x1 : (((w_4 == 64'd2 ? 64'd1 : 64'd0) != 64'd0) ? x2 : (((w_4 == 64'd3 ? 64'd1 : 64'd0) != 64'd0) ? x3 : (((w_4 == 64'd4 ? 64'd1 : 64'd0) != 64'd0) ? x4 : (((w_4 == 64'd5 ? 64'd1 : 64'd0) != 64'd0) ? x5 : (((w_4 == 64'd6 ? 64'd1 : 64'd0) != 64'd0) ? x6 : (((w_4 == 64'd7 ? 64'd1 : 64'd0) != 64'd0) ? x7 : (((w_4 == 64'd8 ? 64'd1 : 64'd0) != 64'd0) ? x8 : (((w_4 == 64'd9 ? 64'd1 : 64'd0) != 64'd0) ? x9 : (((w_4 == 64'd10 ? 64'd1 : 64'd0) != 64'd0) ? x10 : (((w_4 == 64'd11 ? 64'd1 : 64'd0) != 64'd0) ? x11 : (((w_4 == 64'd12 ? 64'd1 : 64'd0) != 64'd0) ? x12 : (((w_4 == 64'd13 ? 64'd1 : 64'd0) != 64'd0) ? x13 : (((w_4 == 64'd14 ? 64'd1 : 64'd0) != 64'd0) ? x14 : (((w_4 == 64'd15 ? 64'd1 : 64'd0) != 64'd0) ? x15 : 64'd0)))))))))))))));
    w_9 = ((w_0 == 64'd115 ? 64'd1 : 64'd0) & (w_5 == 64'd0 ? 64'd1 : 64'd0));
    w_10 = ((w_0 == 64'd115 ? 64'd1 : 64'd0) & (w_5 == 64'd770 ? 64'd1 : 64'd0));
    w_11 = (w_0 == 64'd43 ? 64'd1 : 64'd0);
    w_12 = (((w_0 == 64'd19 ? 64'd1 : 64'd0) != 64'd0) ? w_5 : w_8);
    w_13 = (((w_2 == 64'd0 ? 64'd1 : 64'd0) != 64'd0) ? (w_7 + w_12) : (((w_2 == 64'd1 ? 64'd1 : 64'd0) != 64'd0) ? (w_7 - w_12) : (((w_2 == 64'd2 ? 64'd1 : 64'd0) != 64'd0) ? (w_7 * w_12) : (w_7 + w_12))));
    w_14 = (((w_2 == 64'd0 ? 64'd1 : 64'd0) != 64'd0) ? ((w_7 * w_8) + w_6) : (((w_2 == 64'd1 ? 64'd1 : 64'd0) != 64'd0) ? ((w_7 * 64'd4294967295) + w_8) : (w_7 + (w_8 << 64'd1))));
    w_15 = ((w_9 != 64'd0) ? (pc + 64'd4) : ((w_11 != 64'd0) ? w_14 : (((w_0 == 64'd3 ? 64'd1 : 64'd0) != 64'd0) ? dmem_rdata : (((w_0 == 64'd111 ? 64'd1 : 64'd0) != 64'd0) ? (pc + 64'd4) : w_13))));
    w_16 = (((((w_9 | w_11) | (w_0 == 64'd19 ? 64'd1 : 64'd0)) | (w_0 == 64'd51 ? 64'd1 : 64'd0)) | (w_0 == 64'd3 ? 64'd1 : 64'd0)) | (w_0 == 64'd111 ? 64'd1 : 64'd0));
    w_17 = ((w_9 != 64'd0) ? 64'd64 : ((w_10 != 64'd0) ? mepc : (((w_0 == 64'd99 ? 64'd1 : 64'd0) != 64'd0) ? (((w_7 == w_8 ? 64'd1 : 64'd0) != 64'd0) ? (pc + (w_6 << 64'd2)) : (pc + 64'd4)) : (((w_0 == 64'd111 ? 64'd1 : 64'd0) != 64'd0) ? (pc + (w_5 << 64'd2)) : (pc + 64'd4)))));
    w_18 = (((w_0 == 64'd35 ? 64'd1 : 64'd0) != 64'd0) ? (w_7 + w_6) : (w_7 + w_5));
    w_19 = ((w_9 != 64'd0) ? 64'd0 : (((w_0 == 64'd35 ? 64'd1 : 64'd0) != 64'd0) ? 64'd1 : 64'd0));
    imem_addr = pc;
    dmem_addr = w_18;
    dmem_wdata = w_8;
    dmem_we = w_19;
    pc_out = pc;
    mstatus_out = mstatus;
    mepc_out = mepc;
    mcause_out = mcause;
    cycle_cnt_out = cycle_cnt;
    x1_out = x1;
    x2_out = x2;
    x3_out = x3;
    x4_out = x4;
    x5_out = x5;
    x6_out = x6;
    x7_out = x7;
    x8_out = x8;
    x9_out = x9;
    x10_out = x10;
    x11_out = x11;
    x12_out = x12;
    x13_out = x13;
    x14_out = x14;
    x15_out = x15;
  end
  // Synchronous-reset control registers
  always_ff @(posedge clk) begin
    if (rst) begin
      pc <= 64'd0;
      mstatus <= 64'd0;
      mepc <= 64'd0;
      mcause <= 64'd0;
      cycle_cnt <= 64'd0;
      x1 <= 64'd0;
      x2 <= 64'd0;
      x3 <= 64'd0;
      x4 <= 64'd0;
      x5 <= 64'd0;
      x6 <= 64'd0;
      x7 <= 64'd0;
      x8 <= 64'd0;
      x9 <= 64'd0;
      x10 <= 64'd0;
      x11 <= 64'd0;
      x12 <= 64'd0;
      x13 <= 64'd0;
      x14 <= 64'd0;
      x15 <= 64'd0;
    end else begin
      pc <= w_17;
      mstatus <= ((w_9 != 64'd0) ? 64'd24 : ((w_10 != 64'd0) ? 64'd8 : mstatus));
      mepc <= ((w_9 != 64'd0) ? (pc + 64'd4) : mepc);
      mcause <= ((w_9 != 64'd0) ? 64'd11 : mcause);
      cycle_cnt <= (cycle_cnt + 64'd1);
      x1 <= (((w_16 & (w_1 == 64'd1 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x1);
      x2 <= (((w_16 & (w_1 == 64'd2 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x2);
      x3 <= (((w_16 & (w_1 == 64'd3 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x3);
      x4 <= (((w_16 & (w_1 == 64'd4 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x4);
      x5 <= (((w_16 & (w_1 == 64'd5 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x5);
      x6 <= (((w_16 & (w_1 == 64'd6 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x6);
      x7 <= (((w_16 & (w_1 == 64'd7 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x7);
      x8 <= (((w_16 & (w_1 == 64'd8 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x8);
      x9 <= (((w_16 & (w_1 == 64'd9 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x9);
      x10 <= (((w_16 & (w_1 == 64'd10 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x10);
      x11 <= (((w_16 & (w_1 == 64'd11 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x11);
      x12 <= (((w_16 & (w_1 == 64'd12 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x12);
      x13 <= (((w_16 & (w_1 == 64'd13 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x13);
      x14 <= (((w_16 & (w_1 == 64'd14 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x14);
      x15 <= (((w_16 & (w_1 == 64'd15 ? 64'd1 : 64'd0)) != 64'd0) ? w_15 : x15);
    end
  end
endmodule
