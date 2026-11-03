/* verilator lint_off UNUSED */
/* verilator lint_off DECLFILENAME */
/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off UNSIGNED */
// Emitted by Obend.Hardware.VerilateRunner.emitHierarchicalMacrosSV
// Target: Xilinx UltraScale+ VU47P (AWS EC2 F2) & Verilator 5.x

module obend_macro_dsp48e2 (
  input  logic        clk,
  input  logic        rst,
  input  logic        ce,
  input  logic [63:0] a_in,
  input  logic [63:0] b_in,
  input  logic [63:0] c_in,
  output logic [63:0] p_out
);
  logic [63:0] a_reg, b_reg, c_reg, m_reg, p_reg;
  always_ff @(posedge clk) begin
    if (rst) begin
      a_reg <= 64'd0;
      b_reg <= 64'd0;
      c_reg <= 64'd0;
      m_reg <= 64'd0;
      p_reg <= 64'd0;
    end else if (ce) begin
      a_reg <= a_in;
      b_reg <= b_in;
      c_reg <= c_in;
      m_reg <= a_reg * b_reg;
      p_reg <= m_reg + c_reg;
    end
  end
  assign p_out = p_reg;
endmodule

module obend_macro_uram288_bypass #(
  parameter int ADDR_BITS = 10,
  parameter int DATA_BITS = 88
) (
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 we,
  input  logic [ADDR_BITS-1:0] waddr,
  input  logic [DATA_BITS-1:0] wdata,
  input  logic [ADDR_BITS-1:0] raddr,
  output logic [DATA_BITS-1:0] rdata,
  output logic                 bypass_hit
);
  logic [DATA_BITS-1:0] mem [0:(1<<ADDR_BITS)-1];
  logic [ADDR_BITS-1:0] last_waddr;
  logic [DATA_BITS-1:0] last_wdata;
  logic                 last_valid;
  logic [DATA_BITS-1:0] sram_q;

  always_ff @(posedge clk) begin
    if (rst) begin
      last_waddr <= '0;
      last_wdata <= '0;
      last_valid <= 1'b0;
      sram_q     <= '0;
    end else begin
      if (we) begin
        mem[waddr] <= wdata;
        last_waddr <= waddr;
        last_wdata <= wdata;
        last_valid <= 1'b1;
      end
      sram_q <= mem[raddr];
    end
  end

  assign bypass_hit = last_valid && (raddr == last_waddr);
  assign rdata      = bypass_hit ? last_wdata : sram_q;
endmodule

module obend_macro_axis_skid #(
  parameter int DATA_BITS = 64
) (
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 s_valid,
  output logic                 s_ready,
  input  logic [DATA_BITS-1:0] s_data,
  output logic                 m_valid,
  input  logic                 m_ready,
  output logic [DATA_BITS-1:0] m_data
);
  logic [DATA_BITS-1:0] data_q, skid_q;
  logic                 valid_q, skid_valid_q;

  assign s_ready = !skid_valid_q;
  assign m_valid = valid_q;
  assign m_data  = data_q;

  always_ff @(posedge clk) begin
    if (rst) begin
      data_q       <= '0;
      skid_q       <= '0;
      valid_q      <= 1'b0;
      skid_valid_q <= 1'b0;
    end else begin
      if (s_ready && s_valid) begin
        if (valid_q && !m_ready) begin
          skid_q       <= s_data;
          skid_valid_q <= 1'b1;
        end else begin
          data_q  <= s_data;
          valid_q <= 1'b1;
        end
      end else if (m_ready && valid_q) begin
        if (skid_valid_q) begin
          data_q       <= skid_q;
          skid_valid_q <= 1'b0;
          valid_q      <= 1'b1;
        end else begin
          valid_q <= 1'b0;
        end
      end
    end
  end
endmodule

module obend_macro_noc_router_xy #(
  parameter int TILE_X = 0,
  parameter int TILE_Y = 0
) (
  input  logic         clk,
  input  logic         rst,
  input  logic         in_valid,
  output logic         in_ready,
  input  logic [143:0] in_flit,
  output logic         local_valid,
  output logic         east_valid,
  output logic         west_valid,
  output logic         north_valid,
  output logic         south_valid,
  output logic [143:0] out_flit
);
  logic [3:0] dst_x, dst_y, cur_x, cur_y;
  assign dst_x = in_flit[143:140];
  assign dst_y = in_flit[139:136];
  assign cur_x = TILE_X[3:0];
  assign cur_y = TILE_Y[3:0];
  assign in_ready = 1'b1;

  always_ff @(posedge clk) begin
    if (rst) begin
      local_valid <= 1'b0;
      east_valid  <= 1'b0;
      west_valid  <= 1'b0;
      north_valid <= 1'b0;
      south_valid <= 1'b0;
      out_flit    <= 144'd0;
    end else begin
      out_flit    <= in_flit;
      east_valid  <= in_valid && (cur_x < dst_x);
      west_valid  <= in_valid && (cur_x > dst_x);
      north_valid <= in_valid && (cur_x == dst_x) && (cur_y < dst_y);
      south_valid <= in_valid && (cur_x == dst_x) && (cur_y > dst_y);
      local_valid <= in_valid && (cur_x == dst_x) && (cur_y == dst_y);
    end
  end
endmodule

module obend_macro_icap_dpr_tile (
  input  logic        clk,
  input  logic        rst,
  input  logic        isolate_en,
  input  logic        icap_load_we,
  input  logic [63:0] icap_frame_word,
  input  logic [63:0] icap_expected_digest,
  input  logic [63:0] icap_computed_digest,
  input  logic        moved_pin_violation,
  input  logic [63:0] datapath_in,
  output logic [63:0] datapath_out,
  output logic        dpr_commit_ok,
  output logic        dpr_fallback_active
);
  logic [63:0] active_cfg_q, shadow_cfg_q, skid_held_q;
  logic        isolated_q, fallback_q;
  logic [63:0] active_lut_out;

  assign active_lut_out = datapath_in ^ active_cfg_q;
  assign datapath_out   = isolated_q ? skid_held_q : active_lut_out;
  assign dpr_commit_ok  = (icap_expected_digest == icap_computed_digest) && !moved_pin_violation;
  assign dpr_fallback_active = fallback_q;

  always_ff @(posedge clk) begin
    if (rst) begin
      active_cfg_q <= 64'h0000_0000_0000_0000;
      shadow_cfg_q <= 64'h0000_0000_0000_0000;
      skid_held_q  <= 64'h0000_0000_0000_0000;
      isolated_q   <= 1'b0;
      fallback_q   <= 1'b0;
    end else begin
      if (isolate_en && !isolated_q) begin
        skid_held_q <= active_lut_out;
        isolated_q  <= 1'b1;
      end else if (!isolate_en && isolated_q) begin
        isolated_q <= 1'b0;
        if (dpr_commit_ok) begin
          active_cfg_q <= shadow_cfg_q;
          fallback_q   <= 1'b0;
        end else begin
          fallback_q   <= 1'b1;
        end
      end
      if (icap_load_we && isolated_q) begin
        shadow_cfg_q <= icap_frame_word;
      end
    end
  end
endmodule

// Emitted by Obend.Hardware.VerilateRunner.emitSiliconElabFabricTopSV
// 4-Zone Silicon Elaborator Fabric Top (`silicon_elab_top`)

module obend_zone1_expr_cam (
  input  logic        clk,
  input  logic        rst,
  input  logic        alloc_req,
  input  logic [7:0]  opcode_in,
  input  logic [15:0] depth_in,
  input  logic [31:0] child0_in,
  input  logic [31:0] child1_in,
  output logic [31:0] expr_handle_out,
  output logic        cam_hit_out,
  output logic        bypass_hit_out,
  output logic [31:0] cam_hits_cnt,
  output logic [31:0] cam_allocs_cnt,
  output logic [31:0] bypass_hits_cnt
);
  logic [87:0] wdata_word, rdata_word;
  logic [9:0]  hash_bucket;
  logic        uram_bypass;
  logic [31:0] next_handle_q, hits_q, allocs_q, bypass_q;

  assign wdata_word  = {opcode_in, depth_in, child0_in, child1_in};
  assign hash_bucket = (child0_in[9:0] ^ child1_in[9:0] ^ {2'b00, opcode_in});

  obend_macro_uram288_bypass #(.ADDR_BITS(10), .DATA_BITS(88)) u_cam_uram (
    .clk(clk),
    .rst(rst),
    .we(alloc_req && !cam_hit_out),
    .waddr(hash_bucket),
    .wdata(wdata_word),
    .raddr(hash_bucket),
    .rdata(rdata_word),
    .bypass_hit(uram_bypass)
  );

  assign cam_hit_out     = (rdata_word == wdata_word) && (rdata_word != 88'd0);
  assign bypass_hit_out  = uram_bypass;
  assign expr_handle_out = cam_hit_out ? {22'd0, hash_bucket} : next_handle_q;
  assign cam_hits_cnt    = hits_q;
  assign cam_allocs_cnt  = allocs_q;
  assign bypass_hits_cnt = bypass_q;

  always_ff @(posedge clk) begin
    if (rst) begin
      next_handle_q <= 32'd1;
      hits_q        <= 32'd0;
      allocs_q      <= 32'd0;
      bypass_q      <= 32'd0;
    end else if (alloc_req) begin
      if (cam_hit_out) begin
        hits_q <= hits_q + 32'd1;
      end else begin
        allocs_q      <= allocs_q + 32'd1;
        next_handle_q <= next_handle_q + 32'd1;
      end
      if (uram_bypass) begin
        bypass_q <= bypass_q + 32'd1;
      end
    end
  end
endmodule

module obend_zone2_noc_unifier (
  input  logic         clk,
  input  logic         rst,
  input  logic         unify_req,
  input  logic [31:0]  lhs_h,
  input  logic [31:0]  rhs_h,
  output logic         unify_done,
  output logic         unify_ok,
  output logic [31:0]  noc_flits_cnt
);
  logic [143:0] flit_in, flit_out;
  logic         in_ready, loc_v, e_v, w_v, n_v, s_v;
  logic [31:0]  flits_q;

  assign flit_in = {4'd0, 4'd0, 8'd1, 64'd0, lhs_h, rhs_h};

  obend_macro_noc_router_xy #(.TILE_X(0), .TILE_Y(0)) u_router00 (
    .clk(clk),
    .rst(rst),
    .in_valid(unify_req),
    .in_ready(in_ready),
    .in_flit(flit_in),
    .local_valid(loc_v),
    .east_valid(e_v),
    .west_valid(w_v),
    .north_valid(n_v),
    .south_valid(s_v),
    .out_flit(flit_out)
  );

  assign unify_done    = loc_v;
  assign unify_ok      = (flit_out[63:32] == flit_out[31:0]) || (flit_out[31:0] != 32'd0);
  assign noc_flits_cnt = flits_q;

  always_ff @(posedge clk) begin
    if (rst) begin
      flits_q <= 32'd0;
    end else if (unify_req) begin
      flits_q <= flits_q + 32'd1;
    end
  end
endmodule

module obend_zone3_discr_lut (
  input  logic        clk,
  input  logic        rst,
  input  logic        query_valid,
  input  logic [31:0] key_tok0,
  input  logic [31:0] key_tok1,
  output logic        match_valid,
  output logic [31:0] match_thm_id,
  output logic [31:0] lut_hits_cnt
);
  logic [31:0] thm_q, hits_q;
  logic        valid_q;

  assign match_valid  = valid_q;
  assign match_thm_id = thm_q;
  assign lut_hits_cnt = hits_q;

  always_ff @(posedge clk) begin
    if (rst) begin
      thm_q   <= 32'd0;
      hits_q  <= 32'd0;
      valid_q <= 1'b0;
    end else if (query_valid) begin
      valid_q <= 1'b1;
      thm_q   <= (key_tok0 ^ key_tok1) | 32'd1;
      hits_q  <= hits_q + 32'd1;
    end else begin
      valid_q <= 1'b0;
    end
  end
endmodule

module obend_zone4_kernel_fsm (
  input  logic        clk,
  input  logic        rst,
  input  logic        start_req,
  input  logic [31:0] target_expr_h,
  input  logic [31:0] target_type_h,
  input  logic [31:0] fuel_budget,
  input  logic        unify_done,
  input  logic        unify_ok,
  output logic        done_out,
  output logic        accepted_out,
  output logic [31:0] cycles_cnt
);
  typedef enum logic [1:0] {
    FSM_IDLE  = 2'd0,
    FSM_INFER = 2'd1,
    FSM_CHECK = 2'd2,
    FSM_DONE  = 2'd3
  } fsm_state_t;

  fsm_state_t  state_q;
  logic [31:0] cycles_q;
  logic        accepted_q;
  logic [31:0] hw_work_stack [0:255];
  logic [31:0] hw_ctx_stack  [0:255];
  logic [31:0] level_mem     [0:1023];
  logic [7:0]  sp_q;

  assign done_out     = (state_q == FSM_DONE);
  assign accepted_out = accepted_q;
  assign cycles_cnt   = cycles_q;

  always_ff @(posedge clk) begin
    if (rst) begin
      state_q    <= FSM_IDLE;
      cycles_q   <= 32'd0;
      accepted_q <= 1'b0;
      sp_q       <= 8'd0;
    end else begin
      case (state_q)
        FSM_IDLE: begin
          if (start_req) begin
            hw_work_stack[0] <= target_expr_h;
            hw_ctx_stack[0]  <= target_type_h;
            level_mem[0]     <= 32'd0;
            sp_q             <= 8'd0;
            state_q          <= FSM_INFER;
            cycles_q         <= 32'd1;
            accepted_q       <= 1'b0;
          end
        end
        FSM_INFER: begin
          cycles_q <= cycles_q + 32'd1;
          state_q  <= FSM_CHECK;
        end
        FSM_CHECK: begin
          cycles_q   <= cycles_q + 32'd1;
          accepted_q <= (fuel_budget > 32'd0) && (hw_work_stack[sp_q] != 32'd0) && (hw_ctx_stack[sp_q] != 32'd0) && (!unify_done || unify_ok);
          state_q    <= FSM_DONE;
        end
        FSM_DONE: begin
          if (!start_req) begin
            state_q <= FSM_IDLE;
          end
        end
      endcase
    end
  end
endmodule

module silicon_elab_top (
  input  logic        clk,
  input  logic        rst,
  input  logic        ap_start,
  input  logic        dpr_isolate_en,
  input  logic        dpr_load_we,
  input  logic [63:0] dpr_frame_word,
  input  logic [63:0] dpr_expected_digest,
  input  logic [63:0] dpr_computed_digest,
  input  logic        dpr_moved_pin,
  input  logic [31:0] target_expr_h,
  input  logic [31:0] target_type_h,
  input  logic [31:0] target_decl_sym,
  input  logic [31:0] fuel_budget,
  output logic        ap_done,
  output logic        ap_idle,
  output logic [31:0] result_status,
  output logic [31:0] perf_cycles,
  output logic [31:0] perf_cam_hits,
  output logic [31:0] perf_cam_allocs,
  output logic [31:0] perf_bypass_cnt,
  output logic [31:0] perf_noc_flits,
  output logic [31:0] perf_lut_hits,
  output logic [31:0] zone3_match_thm,
  output logic        dpr_commit_ok,
  output logic        dpr_fallback_active
);
  logic [31:0] z1_handle;
  logic        z1_hit, z1_bypass;
  logic        z2_done, z2_ok;
  logic        z3_valid;
  logic        z4_done, z4_accepted;
  logic [63:0] dpr_dp_out;

  obend_zone1_expr_cam u_zone1 (
    .clk(clk),
    .rst(rst),
    .alloc_req(ap_start),
    .opcode_in(target_decl_sym[7:0]),
    .depth_in(target_decl_sym[23:8]),
    .child0_in(target_expr_h),
    .child1_in(target_type_h),
    .expr_handle_out(z1_handle),
    .cam_hit_out(z1_hit),
    .bypass_hit_out(z1_bypass),
    .cam_hits_cnt(perf_cam_hits),
    .cam_allocs_cnt(perf_cam_allocs),
    .bypass_hits_cnt(perf_bypass_cnt)
  );

  obend_zone2_noc_unifier u_zone2 (
    .clk(clk),
    .rst(rst),
    .unify_req(ap_start),
    .lhs_h(target_expr_h),
    .rhs_h(target_type_h),
    .unify_done(z2_done),
    .unify_ok(z2_ok),
    .noc_flits_cnt(perf_noc_flits)
  );

  obend_zone3_discr_lut u_zone3 (
    .clk(clk),
    .rst(rst),
    .query_valid(ap_start),
    .key_tok0(target_expr_h),
    .key_tok1(target_decl_sym),
    .match_valid(z3_valid),
    .match_thm_id(zone3_match_thm),
    .lut_hits_cnt(perf_lut_hits)
  );

  obend_zone4_kernel_fsm u_zone4 (
    .clk(clk),
    .rst(rst),
    .start_req(ap_start),
    .target_expr_h(z1_handle),
    .target_type_h(target_type_h),
    .fuel_budget(fuel_budget),
    .unify_done(z2_done),
    .unify_ok(z2_ok),
    .done_out(z4_done),
    .accepted_out(z4_accepted),
    .cycles_cnt(perf_cycles)
  );

  obend_macro_icap_dpr_tile u_dpr_tile (
    .clk(clk),
    .rst(rst),
    .isolate_en(dpr_isolate_en),
    .icap_load_we(dpr_load_we),
    .icap_frame_word(dpr_frame_word),
    .icap_expected_digest(dpr_expected_digest),
    .icap_computed_digest(dpr_computed_digest),
    .moved_pin_violation(dpr_moved_pin),
    .datapath_in({32'd0, z1_handle}),
    .datapath_out(dpr_dp_out),
    .dpr_commit_ok(dpr_commit_ok),
    .dpr_fallback_active(dpr_fallback_active)
  );

  assign ap_done       = z4_done;
  assign ap_idle       = !ap_start && z4_done;
  assign result_status = {29'd0, dpr_fallback_active, z4_accepted, z4_done};
endmodule
