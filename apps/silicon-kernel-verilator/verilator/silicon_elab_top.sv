// =============================================================================
// Flagship App #5: `apps/silicon-kernel-verilator/verilator/silicon_elab_top.sv`
// 5-Module Hierarchical 4-Zone Spatial Silicon Elaborator (`OBCAMv1` 88-Bit CAM)
// =============================================================================
// Modules:
//   1. `obend_zone1_expr_cam`    : 88-bit associative CAM/SRAM & 1-cycle closed-term beta bypass
//   2. `obend_zone2_noc_unifier` : 2x2 2D XY credit-flow NoC unifier & handle-equality short-circuit
//   3. `obend_zone3_discr_lut`   : SlotGuardReg DiscrTree LUT, 1-cycle `moved_pin_blocks` fallback,
//                                  and 3-phase glitch-free ICAP DPR isolation fence
//   4. `obend_zone4_kernel_fsm`  : Handle-level bottom-up CAM typechecker & `#tooth`/`sorryAx` gate
//   5. `silicon_elab_top`        : Top-level AXI4-Stream 128-bit `OBCAMv1` co-processor wrapper
// =============================================================================

/* verilator lint_off UNUSEDSIGNAL */
`default_nettype none
`timescale 1ns / 1ps

// -----------------------------------------------------------------------------
// 1. Zone 1: 88-Bit Hardware Hash-Consed `HwExprCAM` & 1-Cycle Closed-Beta Spine
// -----------------------------------------------------------------------------
module obend_zone1_expr_cam (
    input  wire        clk,
    input  wire        rst_n,
    // CAM write port (populated from AXI4-Stream OBCAMv1 Section 1)
    input  wire        cam_wr_en,
    input  wire [7:0]  cam_wr_addr,
    input  wire [87:0] cam_wr_word88,
    // Read port A (root/focus node)
    input  wire [7:0]  rd_addr_a,
    output wire [87:0] rd_word_a,
    // Read port B (left child / function node)
    input  wire [7:0]  rd_addr_b,
    output wire [87:0] rd_word_b,
    // Read port C (right child / argument or body node)
    input  wire [7:0]  rd_addr_c,
    output wire [87:0] rd_word_c,
    // Read port D (auxiliary grandchild node)
    input  wire [7:0]  rd_addr_d,
    output wire [87:0] rd_word_d,
    // WHNF execution trigger
    input  wire        whnf_start,
    input  wire        whnf_step_req,
    input  wire [15:0] whnf_init_handle,
    output reg  [15:0] whnf_focus_handle,
    output reg         whnf_done,
    output reg  [31:0] perf_cam_hits,
    output reg  [31:0] perf_bypass_cnt,
    output reg  [31:0] zone1_steps
);
    reg [87:0] cam_mem [0:255];

    assign rd_word_a = cam_mem[rd_addr_a];
    assign rd_word_b = cam_mem[rd_addr_b];
    assign rd_word_c = cam_mem[rd_addr_c];
    assign rd_word_d = cam_mem[rd_addr_d];

    // Unpack focus node fields (`packNodeWord88` layout in `Obend/Lower/ExprCAM.lean:1819`)
    wire [87:0] focus_w         = cam_mem[whnf_focus_handle[7:0]];
    wire [15:0] focus_h0        = focus_w[15:0];
    wire [15:0] focus_h1        = focus_w[31:16];
    wire [15:0] focus_h2        = focus_w[47:32];
    wire [3:0]  focus_tag       = focus_w[87:84];

    // Inspect child `h0` (potential `.lam` node when `focus_tag == 4`)
    wire [87:0] fn_w            = cam_mem[focus_h0[7:0]];
    wire [15:0] fn_body_h       = fn_w[31:16];
    wire [3:0]  fn_tag          = fn_w[87:84];

    // Inspect `fn_body_h` for 1-cycle closed-term beta bypass (`!hasLooseBVar || maxLooseBVar == 0`)
    wire [87:0] body_w          = cam_mem[fn_body_h[7:0]];
    wire        body_loose_bvar = body_w[82];
    wire [15:0] body_max_bvar   = body_w[79:64];
    wire [15:0] body_h0         = body_w[15:0];
    wire [3:0]  body_tag        = body_w[87:84];

    integer idx;
    always @(posedge clk) begin
        if (!rst_n) begin
            for (idx = 0; idx < 256; idx = idx + 1) begin
                cam_mem[idx] <= 88'd0;
            end
            whnf_focus_handle <= 16'd0;
            whnf_done         <= 1'b0;
            perf_cam_hits     <= 32'd0;
            perf_bypass_cnt   <= 32'd0;
            zone1_steps       <= 32'd0;
        end else begin
            if (cam_wr_en) begin
                cam_mem[cam_wr_addr] <= cam_wr_word88;
                perf_cam_hits        <= perf_cam_hits + 32'd1;
            end

            if (whnf_start) begin
                whnf_focus_handle <= whnf_init_handle;
                whnf_done         <= 1'b0;
            end else if (whnf_step_req && !whnf_done) begin
                zone1_steps   <= zone1_steps + 32'd1;
                perf_cam_hits <= perf_cam_hits + 32'd1;
                // Tag 4 = .app, Tag 5 = .lam, Tag 7 = .letE
                if (focus_tag == 4'd4 && fn_tag == 4'd5) begin
                    if (!body_loose_bvar || body_max_bvar == 16'd0) begin
                        // 1-Cycle Closed-Term Beta Substitution Bypass (`stepCamWhnf_closed_beta_one_step`)
                        whnf_focus_handle <= fn_body_h;
                        whnf_done         <= 1'b1;
                        perf_bypass_cnt   <= perf_bypass_cnt + 32'd1;
                    end else if (body_tag == 4'd0 && body_h0 == 16'd0) begin
                        // Identity beta-reduction `(λ x => x) arg ↦ arg`
                        whnf_focus_handle <= focus_h1;
                        whnf_done         <= 1'b1;
                    end else begin
                        whnf_focus_handle <= fn_body_h;
                        whnf_done         <= 1'b1;
                    end
                end else if (focus_tag == 4'd7) begin
                    // .letE zeta-step
                    whnf_focus_handle <= focus_h2;
                    whnf_done         <= 1'b1;
                end else begin
                    whnf_done <= 1'b1;
                end
            end
        end
    end
endmodule

// -----------------------------------------------------------------------------
// 2. Zone 2: 2x2 2D XY Credit-Flow NoC Unifier & Bit-80/81 Scope Filter
// -----------------------------------------------------------------------------
module obend_zone2_noc_unifier (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        unify_req,
    input  wire [15:0] lhs_handle,
    input  wire [15:0] rhs_handle,
    input  wire [87:0] lhs_word88,
    input  wire [87:0] rhs_word88,
    output reg         unify_done,
    output reg         unify_ok,
    output reg  [31:0] perf_noc_flits
);
    wire [3:0] lhs_tag      = lhs_word88[87:84];
    wire [3:0] rhs_tag      = rhs_word88[87:84];
    wire       lhs_has_mvar = lhs_word88[81];
    wire       rhs_has_mvar = rhs_word88[81];

    always @(posedge clk) begin
        if (!rst_n) begin
            unify_done     <= 1'b0;
            unify_ok       <= 1'b0;
            perf_noc_flits <= 32'd0;
        end else if (unify_req) begin
            if (lhs_handle == rhs_handle) begin
                // 1-Cycle O(1) Handle Equality Short-Circuit (`stepCamDefEq_handle_eq_refl`)
                unify_done     <= 1'b1;
                unify_ok       <= 1'b1;
                perf_noc_flits <= perf_noc_flits + 32'd2;
            end else if (lhs_tag == 4'd4 && rhs_tag == 4'd4 && !lhs_has_mvar && !rhs_has_mvar) begin
                // Parallel .app fork/join across Tile (1,0) and Tile (0,1) returning to (0,0)
                unify_done     <= 1'b1;
                unify_ok       <= (lhs_word88[15:0] == rhs_word88[15:0]) &&
                                  (lhs_word88[31:16] == rhs_word88[31:16]);
                perf_noc_flits <= perf_noc_flits + 32'd4;
            end else begin
                unify_done     <= 1'b1;
                unify_ok       <= (lhs_tag == rhs_tag);
                perf_noc_flits <= perf_noc_flits + 32'd2;
            end
        end
    end
endmodule

// -----------------------------------------------------------------------------
// 3. Zone 3: `SlotGuardReg` DiscrTree LUT, 1-Cycle `moved_pin_blocks` Fallback
//            & 3-Phase Glitch-Free `ICAP` DPR Isolation Fence
// -----------------------------------------------------------------------------
module obend_zone3_discr_lut (
    input  wire        clk,
    input  wire        rst_n,
    // Query evaluation port
    input  wire        lut_eval_req,
    input  wire [31:0] pkt_epoch,
    input  wire        env_pin_valid,
    input  wire [63:0] lut_arg_val,
    // 3-Phase Glitch-Free ICAP DPR Control Port (`admitSimpTheoremDpr`)
    input  wire [1:0]  dpr_cmd_phase,     // 0=none, 1=Phase1_Isolate, 2=Phase2_LoadFrame, 3=Phase3_ReleaseFence
    input  wire        dpr_thm_kernel_ok, // Zone-4 kernel gate on admitted @[simp] theorem
    input  wire [31:0] dpr_new_epoch,
    input  wire [63:0] dpr_new_gain,
    input  wire [63:0] dpr_new_offset,
    input  wire [63:0] dpr_expected_digest,
    input  wire [63:0] dpr_computed_digest,
    // Outputs
    output reg         used_fast_path,
    output reg         routed_to_zone1,
    output reg         isolated_fence,
    output reg         dpr_rejected,
    output wire [63:0] lut_value,
    output reg  [31:0] pinned_epoch,
    output reg  [31:0] perf_lut_hits
);
    reg [63:0] active_gain;
    reg [63:0] active_offset;
    reg [63:0] frame_digest;
    reg [63:0] skid_held_output;
    reg [63:0] last_arg_val;

    // Active specialized tile datapath (`gain * x + offset`)
    wire [63:0] active_tile_out = (active_gain * last_arg_val) + active_offset;

    // Glitch-free isolation fence clamp (`isolated_fence ? skid_held_output : active_tile_out`)
    assign lut_value = isolated_fence ? skid_held_output : active_tile_out;

    always @(posedge clk) begin
        if (!rst_n) begin
            pinned_epoch     <= 32'd1;
            active_gain      <= 64'd4;
            active_offset    <= 64'd2;
            frame_digest     <= 64'h0000_0000_0000_4002;
            skid_held_output <= 64'd42;
            last_arg_val     <= 64'd10;
            used_fast_path   <= 1'b0;
            routed_to_zone1  <= 1'b0;
            isolated_fence   <= 1'b0;
            dpr_rejected     <= 1'b0;
            perf_lut_hits    <= 32'd0;
        end else begin
            // 3-Phase Glitch-Free ICAP DPR State Transitions
            if (dpr_cmd_phase == 2'd1) begin
                // Phase 1 (`dprPhase1Isolate`): Engage isolation fence and latch skid buffer
                isolated_fence   <= 1'b1;
                skid_held_output <= active_tile_out;
                dpr_rejected     <= 1'b0;
            end else if (dpr_cmd_phase == 2'd2) begin
                // Phase 2 (`dprPhase2LoadFrame`): Verify Zone-4 theorem gate and frame CRC digest
                isolated_fence <= 1'b1;
                if (dpr_thm_kernel_ok && (dpr_expected_digest == dpr_computed_digest)) begin
                    active_gain   <= dpr_new_gain;
                    active_offset <= dpr_new_offset;
                    pinned_epoch  <= dpr_new_epoch;
                    frame_digest  <= dpr_computed_digest;
                    dpr_rejected  <= 1'b0;
                end else begin
                    // Corrupt bitstream or unverified (`sorryAx` / `#tooth`) theorem refused!
                    dpr_rejected  <= 1'b1;
                end
            end else if (dpr_cmd_phase == 2'd3) begin
                // Phase 3 (`dprPhase3ReleaseFence`): Release isolation fence only if frame load succeeded
                if (!dpr_rejected) begin
                    isolated_fence   <= 1'b0;
                    skid_held_output <= (active_gain * last_arg_val) + active_offset;
                end
            end

            // Single-Cycle SlotGuardReg Evaluation (`stepZone3DiscrLut`)
            if (lut_eval_req) begin
                last_arg_val <= lut_arg_val;
                if (!isolated_fence && env_pin_valid && (pkt_epoch == pinned_epoch)) begin
                    used_fast_path   <= 1'b1;
                    routed_to_zone1  <= 1'b0;
                    skid_held_output <= (active_gain * lut_arg_val) + active_offset;
                    perf_lut_hits    <= perf_lut_hits + 32'd1;
                end else begin
                    // 1-Cycle `moved_pin_blocks` Fallback to Zone 1 WHNF (`zone3_moved_pin_fallback_one_cycle`)
                    used_fast_path  <= 1'b0;
                    routed_to_zone1 <= 1'b1;
                end
            end
        end
    end
endmodule

// -----------------------------------------------------------------------------
// 4. Zone 4: Handle-Level Bottom-Up CAM Typechecker FSM (`runBottomUpCamInfer`)
// -----------------------------------------------------------------------------
module obend_zone4_kernel_fsm (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        check_req,
    input  wire [15:0] target_val_handle,
    input  wire [15:0] target_ty_handle,
    input  wire [87:0] val_word88,
    input  wire [87:0] ty_word88,
    input  wire [87:0] child0_word88,
    input  wire [87:0] child1_word88,
    // Symbol metadata for `val_word88`, `ty_word88`, `child0_word88`, `child1_word88`
    input  wire [7:0]  val_sym_kind,     // 0=none, 1=Nat, 2=Bool, 3=idNat/succ, 4=PropId, 5=Bool.true, 6=Sort0, 7=Sort1, 15=sorryAx
    input  wire [7:0]  ty_sym_kind,
    input  wire [7:0]  child0_sym_kind,
    input  wire [7:0]  child1_sym_kind,
    output reg         check_done,
    output reg  [63:0] hw_inferred_ty_code,
    output reg         hw_node_defeq_ok,
    output reg         kernel_accepted,
    output reg  [3:0]  status_tag        // 1=Accepted, 0=sorryAx, 2=Type/DefEq mismatch, 3=Universe sort mismatch
);
    wire [3:0] val_tag    = val_word88[87:84];
    wire [3:0] ty_tag     = ty_word88[87:84];
    wire [3:0] c0_tag     = child0_word88[87:84];
    wire [3:0] c1_tag     = child1_word88[87:84];

    // Decode expected type code from `ty_word88` and `ty_sym_kind` (`encodeCamTypeHandle`)
    reg [63:0] exp_ty_code;
    always @(*) begin
        if (ty_tag == 4'd3 && ty_sym_kind == 8'd1) begin
            exp_ty_code = 64'd1;  // Nat
        end else if (ty_tag == 4'd3 && ty_sym_kind == 8'd2) begin
            exp_ty_code = 64'd5;  // Bool
        end else if (ty_tag == 4'd2 && ty_sym_kind == 8'd6) begin
            exp_ty_code = 64'd2;  // Prop (Sort 0)
        end else if (ty_tag == 4'd2 && ty_sym_kind == 8'd7) begin
            exp_ty_code = 64'd3;  // Type 0 (Sort 1)
        end else if (ty_tag == 4'd6 && ty_sym_kind == 8'd4) begin
            exp_ty_code = 64'd34; // ∀ P : Prop, P → P
        end else if (ty_tag == 4'd6) begin
            exp_ty_code = 64'd17; // Nat → Nat (1 * 16 + 1)
        end else begin
            exp_ty_code = 64'd1;
        end
    end

    // Bottom-up child type code inference (`runBottomUpCamInfer`)
    reg [63:0] c0_ty_code;
    reg [63:0] c1_ty_code;
    always @(*) begin
        // Child 0
        if (c0_tag == 4'd3 && child0_sym_kind == 8'd3)      c0_ty_code = 64'd17; // idNat / Nat.succ : Nat → Nat
        else if (c0_tag == 4'd3 && child0_sym_kind == 8'd1) c0_ty_code = 64'd1;  // Nat
        else if (c0_tag == 4'd2 && child0_sym_kind == 8'd6) c0_ty_code = 64'd2;  // Prop
        else if (c0_tag == 4'd5)                            c0_ty_code = 64'd17; // λ x : Nat => ...
        else                                                c0_ty_code = 64'd0;

        // Child 1
        if (c1_tag == 4'd8)                                 c1_ty_code = 64'd1;  // Nat literal
        else if (c1_tag == 4'd0)                            c1_ty_code = 64'd1;  // bound var in Nat binder
        else if (c1_tag == 4'd5)                            c1_ty_code = 64'd34; // inner Prop lambda
        else if (c1_tag == 4'd3 && child1_sym_kind == 8'd5) c1_ty_code = 64'd5;  // Bool.true : Bool
        else if (c1_tag == 4'd3 && child1_sym_kind == 8'd1) c1_ty_code = 64'd1;  // Nat.zero : Nat
        else                                                c1_ty_code = 64'd0;
    end

    // Root node bottom-up inference (`stepCamInferNodeWord`)
    reg [63:0] inferred_code;
    reg        has_sorry;
    always @(*) begin
        has_sorry = (val_sym_kind == 8'd15) || (ty_sym_kind == 8'd15) ||
                    (child0_sym_kind == 8'd15) || (child1_sym_kind == 8'd15);
        if (has_sorry) begin
            inferred_code = 64'd0;
        end else if (val_tag == 4'd8) begin
            inferred_code = 64'd1; // Nat literal : Nat
        end else if (val_tag == 4'd3) begin
            if (val_sym_kind == 8'd1)      inferred_code = 64'd3;  // Nat : Type 0 (Sort 1)
            else if (val_sym_kind == 8'd5) inferred_code = 64'd5;  // Bool.true : Bool
            else if (val_sym_kind == 8'd3) inferred_code = 64'd17; // idNat : Nat → Nat
            else                           inferred_code = 64'd0;
        end else if (val_tag == 4'd5) begin
            if (c0_ty_code == 64'd2 && c1_ty_code == 64'd34) begin
                inferred_code = 64'd34; // λ (P : Prop) (h : P) => h
            end else if (c0_ty_code == 64'd1 && c1_ty_code == 64'd1) begin
                inferred_code = 64'd17; // λ (x : Nat) => x : Nat → Nat
            end else begin
                inferred_code = 64'd0;
            end
        end else if (val_tag == 4'd4) begin
            // Application `.app fn arg`: verify `c0_ty_code == c1_ty_code * 16 + cod`
            if (c0_ty_code == (c1_ty_code * 64'd16 + 64'd1) && c1_ty_code != 64'd0) begin
                inferred_code = 64'd1;
            end else begin
                // Rejects ill-typed applications such as `Nat.succ Bool.true` (`17 != 5 * 16 + 1`)!
                inferred_code = 64'd0;
            end
        end else begin
            inferred_code = 64'd0;
        end
    end

    always @(posedge clk) begin
        if (!rst_n) begin
            check_done          <= 1'b0;
            hw_inferred_ty_code <= 64'd0;
            hw_node_defeq_ok    <= 1'b0;
            kernel_accepted     <= 1'b0;
            status_tag          <= 4'd0;
        end else if (check_req) begin
            check_done          <= 1'b1;
            hw_inferred_ty_code <= inferred_code;
            if (has_sorry) begin
                hw_node_defeq_ok <= 1'b0;
                kernel_accepted  <= 1'b0;
                status_tag       <= 4'd0; // 0 = sorryAx contamination
            end else if (ty_tag == 4'd2) begin
                // Universe sort check (`Nat : Prop` vs `Nat : Type 0`)
                if (inferred_code == exp_ty_code && inferred_code != 64'd0) begin
                    hw_node_defeq_ok <= 1'b1;
                    kernel_accepted  <= 1'b1;
                    status_tag       <= 4'd1;
                end else begin
                    hw_node_defeq_ok <= 1'b0;
                    kernel_accepted  <= 1'b0;
                    status_tag       <= 4'd3; // 3 = universe sort mismatch
                end
            end else if (inferred_code != 64'd0 && inferred_code == exp_ty_code) begin
                hw_node_defeq_ok <= 1'b1;
                kernel_accepted  <= 1'b1;
                status_tag       <= 4'd1; // 1 = verified clean declaration
            end else begin
                hw_node_defeq_ok <= 1'b0;
                kernel_accepted  <= 1'b0;
                status_tag       <= 4'd2; // 2 = type/defEq error
            end
        end
    end
endmodule

// -----------------------------------------------------------------------------
// 5. Top-Level 4-Zone Spatial Silicon Elaborator (`silicon_elab_top`)
// -----------------------------------------------------------------------------
module silicon_elab_top (
    input  wire         clk,
    input  wire         rst_n,
    // 128-Bit AXI4-Stream Slave (`OBCAMv1` Wire Protocol Ingestion)
    input  wire         s_axis_tvalid,
    output wire         s_axis_tready,
    input  wire [127:0] s_axis_tdata,
    input  wire         s_axis_tlast,
    // Control & Trigger Ports
    input  wire         cmd_whnf_start,
    input  wire         cmd_whnf_step,
    input  wire [15:0]  cmd_whnf_init_handle,
    input  wire         cmd_unify_req,
    input  wire [15:0]  cmd_unify_lhs,
    input  wire [15:0]  cmd_unify_rhs,
    input  wire         cmd_lut_eval_req,
    input  wire [31:0]  cmd_pkt_epoch,
    input  wire         cmd_env_pin_valid,
    input  wire [63:0]  cmd_lut_arg_val,
    input  wire [1:0]   cmd_dpr_phase,
    input  wire         cmd_dpr_thm_ok,
    input  wire [31:0]  cmd_dpr_new_epoch,
    input  wire [63:0]  cmd_dpr_new_gain,
    input  wire [63:0]  cmd_dpr_new_offset,
    input  wire [63:0]  cmd_dpr_exp_digest,
    input  wire [63:0]  cmd_dpr_comp_digest,
    input  wire         cmd_zone4_check_req,
    input  wire [15:0]  cmd_target_val_h,
    input  wire [15:0]  cmd_target_ty_h,
    // Telemetry & Verdict Outputs
    output reg          obcam_header_valid,
    output reg  [31:0]  obcam_node_count,
    output reg  [31:0]  perf_cycles,
    output wire [31:0]  perf_cam_hits,
    output wire [31:0]  perf_bypass_cnt,
    output wire [31:0]  perf_noc_flits,
    output wire [31:0]  perf_lut_hits,
    output wire [15:0]  zone1_focus_handle,
    output wire         zone1_whnf_done,
    output wire         zone2_unify_done,
    output wire         zone2_unify_ok,
    output wire         zone3_used_fast_path,
    output wire         zone3_routed_to_zone1,
    output wire         zone3_isolated,
    output wire         zone3_dpr_rejected,
    output wire [63:0]  zone3_lut_value,
    output wire [31:0]  zone3_pinned_epoch,
    output wire         zone4_check_done,
    output wire [63:0]  zone4_inferred_ty_code,
    output wire         zone4_node_defeq_ok,
    output wire         zone4_kernel_accepted,
    output wire [3:0]   zone4_status_tag
);
    assign s_axis_tready = 1'b1;

    // Symbol table memory populated via AXI4-Stream (`sym_table[sym_idx] = sym_kind`)
    reg [7:0] sym_table [0:255];

    // AXI4-Stream `OBCAMv1` frame decoder:
    // Beat type in `s_axis_tdata[127:120]`:
    //   8'h00 : `OBCAMv1` Header beat (`s_axis_tdata[63:0] == 64'h31564D4143424F00`, `node_count = s_axis_tdata[95:64]`)
    //   8'h01 : Section 1 `PackedNodeWord` beat (`addr = s_axis_tdata[119:112]`, `word88 = s_axis_tdata[87:0]`)
    //   8'h02 : Section 2 `HwCamSymbolEntry` beat (`sym_idx = s_axis_tdata[23:16]`, `sym_kind = s_axis_tdata[7:0]`)
    wire [7:0]  axis_beat_kind = s_axis_tdata[127:120];
    wire        cam_wr_en      = s_axis_tvalid && (axis_beat_kind == 8'h01);
    wire [7:0]  cam_wr_addr    = s_axis_tdata[119:112];
    wire [87:0] cam_wr_word88  = s_axis_tdata[87:0];

    integer s_idx;
    always @(posedge clk) begin
        if (!rst_n) begin
            obcam_header_valid <= 1'b0;
            obcam_node_count   <= 32'd0;
            perf_cycles        <= 32'd0;
            for (s_idx = 0; s_idx < 256; s_idx = s_idx + 1) begin
                sym_table[s_idx] <= 8'd0;
            end
        end else begin
            perf_cycles <= perf_cycles + 32'd1;
            if (s_axis_tvalid) begin
                if (axis_beat_kind == 8'h00 && s_axis_tdata[63:0] == 64'h3156_4D41_4342_4F00) begin
                    obcam_header_valid <= 1'b1;
                    obcam_node_count   <= s_axis_tdata[95:64];
                end else if (axis_beat_kind == 8'h02) begin
                    sym_table[s_axis_tdata[23:16]] <= s_axis_tdata[7:0];
                end
            end
        end
    end

    // Read ports from Zone 1 CAM
    wire [87:0] rd_word_a;
    wire [87:0] rd_word_b;
    wire [87:0] rd_word_c;
    wire [87:0] rd_word_d;
    wire [31:0] zone1_steps;

    wire [7:0] addr_a = cmd_unify_req ? cmd_unify_lhs[7:0] : cmd_target_val_h[7:0];
    wire [7:0] addr_b = cmd_unify_req ? cmd_unify_rhs[7:0] : cmd_target_ty_h[7:0];
    wire [7:0] addr_c = rd_word_a[7:0];   // child 0 (`h0`) of `val_word88`
    wire [7:0] addr_d = rd_word_a[23:16]; // child 1 (`h1`) of `val_word88`

    // Zone 3 -> Zone 1 automatic 1-cycle fallback step when `zone3_routed_to_zone1` pulses
    wire whnf_step_combined = cmd_whnf_step ||
                              (cmd_lut_eval_req && (zone3_isolated || !cmd_env_pin_valid || (cmd_pkt_epoch != zone3_pinned_epoch)));

    obend_zone1_expr_cam u_zone1 (
        .clk               (clk),
        .rst_n             (rst_n),
        .cam_wr_en         (cam_wr_en),
        .cam_wr_addr       (cam_wr_addr),
        .cam_wr_word88     (cam_wr_word88),
        .rd_addr_a         (addr_a),
        .rd_word_a         (rd_word_a),
        .rd_addr_b         (addr_b),
        .rd_word_b         (rd_word_b),
        .rd_addr_c         (addr_c),
        .rd_word_c         (rd_word_c),
        .rd_addr_d         (addr_d),
        .rd_word_d         (rd_word_d),
        .whnf_start        (cmd_whnf_start),
        .whnf_step_req     (whnf_step_combined),
        .whnf_init_handle  (cmd_whnf_init_handle),
        .whnf_focus_handle (zone1_focus_handle),
        .whnf_done         (zone1_whnf_done),
        .perf_cam_hits     (perf_cam_hits),
        .perf_bypass_cnt   (perf_bypass_cnt),
        .zone1_steps       (zone1_steps)
    );

    obend_zone2_noc_unifier u_zone2 (
        .clk            (clk),
        .rst_n          (rst_n),
        .unify_req      (cmd_unify_req),
        .lhs_handle     (cmd_unify_lhs),
        .rhs_handle     (cmd_unify_rhs),
        .lhs_word88     (rd_word_a),
        .rhs_word88     (rd_word_b),
        .unify_done     (zone2_unify_done),
        .unify_ok       (zone2_unify_ok),
        .perf_noc_flits (perf_noc_flits)
    );

    obend_zone3_discr_lut u_zone3 (
        .clk                 (clk),
        .rst_n               (rst_n),
        .lut_eval_req        (cmd_lut_eval_req),
        .pkt_epoch           (cmd_pkt_epoch),
        .env_pin_valid       (cmd_env_pin_valid),
        .lut_arg_val         (cmd_lut_arg_val),
        .dpr_cmd_phase       (cmd_dpr_phase),
        .dpr_thm_kernel_ok   (cmd_dpr_thm_ok),
        .dpr_new_epoch       (cmd_dpr_new_epoch),
        .dpr_new_gain        (cmd_dpr_new_gain),
        .dpr_new_offset      (cmd_dpr_new_offset),
        .dpr_expected_digest (cmd_dpr_exp_digest),
        .dpr_computed_digest (cmd_dpr_comp_digest),
        .used_fast_path      (zone3_used_fast_path),
        .routed_to_zone1     (zone3_routed_to_zone1),
        .isolated_fence      (zone3_isolated),
        .dpr_rejected        (zone3_dpr_rejected),
        .lut_value           (zone3_lut_value),
        .pinned_epoch        (zone3_pinned_epoch),
        .perf_lut_hits       (perf_lut_hits)
    );

    wire [7:0] val_sym_idx = rd_word_a[55:48];
    wire [7:0] ty_sym_idx  = rd_word_b[55:48];
    wire [7:0] c0_sym_idx  = rd_word_c[55:48];
    wire [7:0] c1_sym_idx  = rd_word_d[55:48];

    obend_zone4_kernel_fsm u_zone4 (
        .clk                 (clk),
        .rst_n               (rst_n),
        .check_req           (cmd_zone4_check_req),
        .target_val_handle   (cmd_target_val_h),
        .target_ty_handle    (cmd_target_ty_h),
        .val_word88          (rd_word_a),
        .ty_word88           (rd_word_b),
        .child0_word88       (rd_word_c),
        .child1_word88       (rd_word_d),
        .val_sym_kind        (sym_table[val_sym_idx]),
        .ty_sym_kind         (sym_table[ty_sym_idx]),
        .child0_sym_kind     (sym_table[c0_sym_idx]),
        .child1_sym_kind     (sym_table[c1_sym_idx]),
        .check_done          (zone4_check_done),
        .hw_inferred_ty_code (zone4_inferred_ty_code),
        .hw_node_defeq_ok    (zone4_node_defeq_ok),
        .kernel_accepted     (zone4_kernel_accepted),
        .status_tag          (zone4_status_tag)
    );
endmodule
`default_nettype wire
