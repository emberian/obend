// Emitted & Verified SystemVerilog for Flagship App #2:
// Closed-Loop 20 kHz FOC Motor Drive & 6-Level SiC FCML Inverter Controller
// Corresponds to Obend.Apps.FocHil.focHilSequentialRtlModule + FocDriveTop.obend
`timescale 1ns / 1ps

module foc_drive_top (
    input  logic        clk,
    input  logic        rst,
    // 20 kHz control strobe (1 cycle pulse every 50 us = 500 physics steps)
    input  logic        ctrl_tick_en,
    // Measured stator currents & references in milli-Amperes (signed 32-bit)
    input  logic signed [31:0] id_ref_ma,
    input  logic signed [31:0] iq_ref_ma,
    input  logic signed [31:0] id_meas_ma,
    input  logic signed [31:0] iq_meas_ma,
    // Electrical speed (rad/s) for cross-coupling decoupling
    input  logic signed [31:0] omega_e_rads,
    // 6-level SiC FCML flying-capacitor voltage unbalance in milli-Volts
    input  logic signed [31:0] cap_err_mv,
    // Direct in-slot stator winding temperature in degrees Celsius
    input  logic [31:0]        winding_temp_c,
    // Live mid-run ICAP DPR partial reconfiguration control signals
    input  logic               dpr_isolate_en,
    input  logic               dpr_high_bw_sel,
    // Synthesized d/q voltage commands in milli-Volts (Zero-Order Hold at 20 kHz)
    output logic signed [31:0] vd_cmd_mv,
    output logic signed [31:0] vq_cmd_mv,
    // Active Lyapunov flying-capacitor balancing command in milli-Volts
    output logic signed [31:0] cap_bal_mv,
    // 6-level phase-shifted PWM duty command (0..1000 permille)
    output logic [31:0]        fcml_duty_permille,
    // Hardware 1-cycle over-temperature / over-current safety barrier outputs
    output logic               fault_trip,
    output logic               pwm_gate_en,
    // Diagnostic telemetry ports for VCD trace verification
    output logic signed [31:0] dbg_int_d_mv,
    output logic signed [31:0] dbg_int_q_mv,
    output logic [31:0]        dbg_ctrl_tick_count
);

    // LC Drives 4-pole-pair salient IPM parameters:
    // Ld = 150 uH, Lq = 380 uH, psi_PM = 180 mWb
    localparam signed [63:0] LD_UH       = 64'sd150;
    localparam signed [63:0] LQ_UH       = 64'sd380;
    localparam signed [63:0] PSI_PM_MWB  = 64'sd180;
    localparam signed [63:0] INT_MAX_MV  = 64'sd600000;
    localparam signed [63:0] INT_MIN_MV  = -64'sd600000;
    localparam signed [63:0] VBUS_MAX_MV = 64'sd800000;

    // Stateful always_ff registers (matching Obend.Apps.FocHil.focHilSequentialRtlModule)
    logic signed [31:0] int_d;
    logic signed [31:0] int_q;
    logic signed [31:0] fcml_cap_err;
    logic               thermal_trip_latch;
    logic signed [31:0] skid_vd_hold;
    logic signed [31:0] skid_vq_hold;
    logic [31:0]        ctrl_tick_count;

    // Sign-extended 64-bit datapath signals
    logic signed [63:0] id_err_64;
    logic signed [63:0] iq_err_64;
    logic signed [63:0] id_meas_64;
    logic signed [63:0] iq_meas_64;
    logic signed [63:0] omega_e_64;
    logic signed [63:0] cap_err_64;

    assign id_err_64  = {{32{id_ref_ma[31]}}, id_ref_ma} - {{32{id_meas_ma[31]}}, id_meas_ma};
    assign iq_err_64  = {{32{iq_ref_ma[31]}}, iq_ref_ma} - {{32{iq_meas_ma[31]}}, iq_meas_ma};
    assign id_meas_64 = {{32{id_meas_ma[31]}}, id_meas_ma};
    assign iq_meas_64 = {{32{iq_meas_ma[31]}}, iq_meas_ma};
    assign omega_e_64 = {{32{omega_e_rads[31]}}, omega_e_rads};
    assign cap_err_64 = {{32{cap_err_mv[31]}}, cap_err_mv};

    // Open-recursive .obend layer gains:
    // Layer 0 (Nominal20kHzFocDrive): Kp = 400 mOhm, Ki = 20 mOhm/tick
    // Layer 1 (IcapDprHighBandwidthFocOverride): Kp = 480 mOhm, Ki = 25 mOhm/tick
    logic signed [63:0] kp_gain_milli;
    logic signed [63:0] ki_gain_milli;
    assign kp_gain_milli = dpr_high_bw_sel ? 64'sd480 : 64'sd400;
    assign ki_gain_milli = dpr_high_bw_sel ? 64'sd25  : 64'sd20;

    // Cross-coupling decoupling + stator IR drop feed-forward (in mV):
    // v_d_ff = -omega_e * L_q * i_q
    // v_q_ff =  omega_e * L_d * i_d + omega_e * psi_PM
    logic signed [63:0] vd_ff_64;
    logic signed [63:0] vq_ff_64;

    assign vd_ff_64 = -((omega_e_64 * LQ_UH * iq_meas_64) / 64'sd1000000);
    assign vq_ff_64 = ((omega_e_64 * LD_UH * id_meas_64) / 64'sd1000000)
                      + (omega_e_64 * PSI_PM_MWB);

    // Proportional terms (in mV)
    logic signed [63:0] prop_d_64;
    logic signed [63:0] prop_q_64;

    assign prop_d_64 = (id_err_64 * kp_gain_milli) / 64'sd1000;
    assign prop_q_64 = (iq_err_64 * kp_gain_milli) / 64'sd1000;

    // Next integral accumulator states with anti-windup saturation
    logic signed [63:0] int_d_64;
    logic signed [63:0] int_q_64;
    logic signed [63:0] int_d_cand;
    logic signed [63:0] int_q_cand;
    logic signed [63:0] int_d_sat;
    logic signed [63:0] int_q_sat;

    assign int_d_64   = {{32{int_d[31]}}, int_d};
    assign int_q_64   = {{32{int_q[31]}}, int_q};
    assign int_d_cand = int_d_64 + ((id_err_64 * ki_gain_milli) / 64'sd1000);
    assign int_q_cand = int_q_64 + ((iq_err_64 * ki_gain_milli) / 64'sd1000);

    assign int_d_sat = (int_d_cand > INT_MAX_MV) ? INT_MAX_MV :
                       ((int_d_cand < INT_MIN_MV) ? INT_MIN_MV : int_d_cand);
    assign int_q_sat = (int_q_cand > INT_MAX_MV) ? INT_MAX_MV :
                       ((int_q_cand < INT_MIN_MV) ? INT_MIN_MV : int_q_cand);

    // Active d/q voltage commands (using int_d_sat / int_q_sat)
    logic signed [63:0] vd_active_raw;
    logic signed [63:0] vq_active_raw;
    logic signed [31:0] vd_active_mv;
    logic signed [31:0] vq_active_mv;

    assign vd_active_raw = prop_d_64 + int_d_sat + vd_ff_64;
    assign vq_active_raw = prop_q_64 + int_q_sat + vq_ff_64;

    assign vd_active_mv = (vd_active_raw > VBUS_MAX_MV) ? 32'sd800000 :
                          ((vd_active_raw < -VBUS_MAX_MV) ? -32'sd800000 : vd_active_raw[31:0]);
    assign vq_active_mv = (vq_active_raw > VBUS_MAX_MV) ? 32'sd800000 :
                          ((vq_active_raw < -VBUS_MAX_MV) ? -32'sd800000 : vq_active_raw[31:0]);

    // Immediate combinational + write-once latched 155 C over-temperature trip
    logic overtemp_now;
    assign overtemp_now = (winding_temp_c >= 32'd155);

    // Sequential always_ff block: PI accumulators, FCML balancer, DPR skid buffer, and thermal latch
    always_ff @(posedge clk) begin
        if (rst) begin
            int_d              <= 32'sd0;
            int_q              <= 32'sd0;
            fcml_cap_err       <= 32'sd15000;
            thermal_trip_latch <= 1'b0;
            skid_vd_hold       <= 32'sd0;
            skid_vq_hold       <= 32'sd0;
            ctrl_tick_count    <= 32'd0;
        end else begin
            // Write-once 1-cycle hardware over-temperature latch (monotone safety barrier)
            thermal_trip_latch <= thermal_trip_latch | overtemp_now;

            if (ctrl_tick_en) begin
                ctrl_tick_count <= ctrl_tick_count + 32'd1;
                if (dpr_isolate_en) begin
                    // During live ICAP DPR bitstream swap: freeze integrators & hold ZOH skid outputs
                    int_d        <= int_d;
                    int_q        <= int_q;
                    fcml_cap_err <= fcml_cap_err;
                    skid_vd_hold <= skid_vd_hold;
                    skid_vq_hold <= skid_vq_hold;
                end else if (!thermal_trip_latch && !overtemp_now) begin
                    int_d        <= int_d_sat[31:0];
                    int_q        <= int_q_sat[31:0];
                    // Lyapunov active balancing contraction step (gain = 800 permille)
                    fcml_cap_err <= 32'((cap_err_64 * 64'sd800) / 64'sd1000);
                    skid_vd_hold <= vd_active_mv;
                    skid_vq_hold <= vq_active_mv;
                end
            end
        end
    end

    // Glitch-free 20 kHz ZOH + DPR isolation & 1-cycle gate-kill outputs
    assign fault_trip  = thermal_trip_latch | overtemp_now;
    assign pwm_gate_en = ~fault_trip;

    assign vd_cmd_mv   = fault_trip ? 32'sd0 : skid_vd_hold;
    assign vq_cmd_mv   = fault_trip ? 32'sd0 : skid_vq_hold;
    assign cap_bal_mv  = fcml_cap_err;

    // 6-level SiC FCML phase-shifted PWM duty permille (500 = 0V neutral, 0..1000 across +/-800V bus)
    logic signed [63:0] vq_cmd_64;
    logic signed [63:0] duty_signed;
    assign vq_cmd_64   = {{32{vq_cmd_mv[31]}}, vq_cmd_mv};
    assign duty_signed = 64'sd500 + ((vq_cmd_64 * 64'sd500) / VBUS_MAX_MV);
    assign fcml_duty_permille = fault_trip ? 32'd0 :
                                ((duty_signed > 64'sd1000) ? 32'd1000 :
                                ((duty_signed < 64'sd0)    ? 32'd0    : duty_signed[31:0]));

    assign dbg_int_d_mv        = int_d;
    assign dbg_int_q_mv        = int_q;
    assign dbg_ctrl_tick_count = ctrl_tick_count;

endmodule
