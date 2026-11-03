// Emitted & Verified SystemVerilog for Flagship App #3:
// All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver
// Corresponds to Obend.Apps.SdrFt8.sdrFt8SequentialRtlModule + SdrFt8Top.obend
// Closed-loop datapath:
//   Tayloe I/Q Combiner -> 3-Stage Hogenauer CIC + Folded Symmetric FIR
//   -> 4-Stage 4-Quadrant Vectoring CORDIC (atan2 + hypot)
//   -> Stateful always_ff \Delta\phi[m] = \phi[m] - \phi[m-1] FT8 8-FSK Discriminator
`timescale 1ns / 1ps

module sdr_ft8_top (
    input  logic        clk,
    input  logic        rst,
    input  logic        sample_valid,
    // R = 64 Hogenauer CIC decimation strobe
    input  logic        decim_strobe,
    // End-of-preamble initial CORDIC phase reference strobe
    input  logic        phase_ref_strobe,
    // FT8 symbol clock strobe (79 symbols across the 16,384-sample capture window)
    input  logic        symbol_strobe,
    // 16-bit signed Tayloe quadrature Real-branch (i_mix_mv, q_mix_mv) &
    // Quadrature-branch (i_quad_mv, q_quad_mv) channels (in mV / LSBs):
    //   Desired USB (+1250 Hz): I and Hilbert-Q are in-phase (+A_sig, +A_sig)
    //   Unwanted +40 dB LSB image (-1250 Hz): I and Hilbert-Q are anti-phase (+A_img, -A_img)
    input  logic signed [31:0] i_mix_mv,
    input  logic signed [31:0] q_mix_mv,
    input  logic signed [31:0] i_quad_mv,
    input  logic signed [31:0] q_quad_mv,
    // Calibrated I/Q gain trim in permille (500 = matched 0.0 dB / 0.0 deg calibration)
    input  logic signed [31:0] iq_gain_i_permille,
    input  logic signed [31:0] iq_gain_q_permille,
    // Tayloe Hartley/Weaver sideband outputs
    output logic signed [63:0] desired_usb_mv,
    output logic signed [63:0] desired_usb_q_mv,
    output logic signed [63:0] image_cancel_mv,
    // Stateful 3-stage CIC + Folded Symmetric FIR outputs
    output logic signed [63:0] cic_stage3_out,
    output logic signed [63:0] folded_fir_out,
    // 4-stage unrolled CORDIC magnitude, atan2 angle, and stateful \Delta\phi FT8 outputs
    output logic signed [31:0] cordic_mag_out,
    output logic signed [31:0] cordic_atan2_mrad,
    output logic signed [63:0] delta_phase_mrad,
    output logic [2:0]         ft8_tone_bin,
    output logic               ft8_symbol_valid,
    output logic [31:0]        dbg_symbol_count
);

    // 1. Programmable Tayloe I/Q Gain Calibration & Hartley/Weaver Image-Rejection Combiner
    logic signed [63:0] i_mix_64,  q_mix_64;
    logic signed [63:0] i_quad_64, q_quad_64;
    logic signed [63:0] gain_i_64, gain_q_64;
    logic signed [63:0] i_cal_64,  q_cal_64;
    logic signed [63:0] iq_cal_64, qq_cal_64;

    assign i_mix_64  = {{32{i_mix_mv[31]}}, i_mix_mv};
    assign q_mix_64  = {{32{q_mix_mv[31]}}, q_mix_mv};
    assign i_quad_64 = {{32{i_quad_mv[31]}}, i_quad_mv};
    assign q_quad_64 = {{32{q_quad_mv[31]}}, q_quad_mv};
    assign gain_i_64 = {{32{iq_gain_i_permille[31]}}, iq_gain_i_permille};
    assign gain_q_64 = {{32{iq_gain_q_permille[31]}}, iq_gain_q_permille};

    assign i_cal_64  = (i_mix_64  * gain_i_64) / 64'sd500;
    assign q_cal_64  = (q_mix_64  * gain_q_64) / 64'sd500;
    assign iq_cal_64 = (i_quad_64 * gain_i_64) / 64'sd500;
    assign qq_cal_64 = (q_quad_64 * gain_q_64) / 64'sd500;

    // When gain_i == gain_q == 500, the +40 dB LSB image cancels identically to 0,
    // while desired USB doubles coherently. Under gain mismatch, leaked LSB jammer enters
    // desired_usb_mv / desired_usb_q_mv and corrupts downstream CORDIC FT8 demodulation.
    assign desired_usb_mv   = i_cal_64  + q_cal_64;
    assign desired_usb_q_mv = iq_cal_64 + qq_cal_64;
    assign image_cancel_mv  = i_cal_64  - q_cal_64;

    // 2. Stateful always_ff 3-Stage Hogenauer CIC Integrators & Comb + Folded Symmetric FIR
    logic signed [63:0] cic_int1, cic_int2, cic_int3;
    logic signed [63:0] cic_comb_d1, fir_tap_d1;

    logic signed [63:0] cic_int1_next, cic_int2_next, cic_int3_next, comb_diff;
    assign cic_int1_next = cic_int1 + desired_usb_mv;
    assign cic_int2_next = cic_int2 + cic_int1_next;
    assign cic_int3_next = cic_int3 + cic_int2_next;
    assign comb_diff     = cic_int3 - cic_comb_d1;

    // Folded symmetric FIR pre-adds symmetric taps before single * 256 multiply
    assign cic_stage3_out = comb_diff;
    assign folded_fir_out = (comb_diff + fir_tap_d1) * 64'sd256;

    // 4-tap folded symmetric linear-phase baseband channel FIR [1, 3, 3, 1] on (desired_usb_mv, desired_usb_q_mv)
    // Pre-adds outer taps (x[n] + x[n-3]) and inner taps (x[n-1] + x[n-2]) to halve multipliers
    logic signed [63:0] bb_i_d1, bb_i_d2, bb_i_d3;
    logic signed [63:0] bb_q_d1, bb_q_d2, bb_q_d3;
    logic signed [63:0] fir_i_out, fir_q_out;

    assign fir_i_out = (desired_usb_mv   + bb_i_d3) + 64'sd3 * (bb_i_d1 + bb_i_d2);
    assign fir_q_out = (desired_usb_q_mv + bb_q_d3) + 64'sd3 * (bb_q_d1 + bb_q_d2);

    // 3. 4-Stage Unrolled 4-Quadrant Vectoring CORDIC (atan2 + hypot) on (fir_i_out, fir_q_out)
    // Angle LUT in milliradians matching Obend.Hardware.DSP.goldenCordic4Stages: [785, 464, 245, 124]
    logic signed [63:0] cx0, cy0, cz0;
    logic signed [63:0] cx1, cy1, cz1;
    logic signed [63:0] cx2, cy2, cz2;
    logic signed [63:0] cx3, cy3, cz3;
    logic signed [63:0] cx4, cy4, cz4;

    // Quadrant folding into right half-plane (cx0 >= 0) with +/- pi (+/- 3142 mrad) offset
    assign cx0 = (fir_i_out >= 64'sd0) ? fir_i_out : -fir_i_out;
    assign cy0 = (fir_i_out >= 64'sd0) ? fir_q_out : -fir_q_out;
    assign cz0 = (fir_i_out >= 64'sd0) ? 64'sd0 :
                 ((fir_q_out >= 64'sd0) ? 64'sd3142 : -64'sd3142);

    // Stage 0 (shift = 0, atan(2^0) = 785 mrad = 45.0 deg)
    assign cx1 = (cy0 >= 64'sd0) ? (cx0 + cy0) : (cx0 - cy0);
    assign cy1 = (cy0 >= 64'sd0) ? (cy0 - cx0) : (cy0 + cx0);
    assign cz1 = (cy0 >= 64'sd0) ? (cz0 + 64'sd785) : (cz0 - 64'sd785);

    // Stage 1 (shift = 1, atan(2^-1) = 464 mrad = 26.6 deg)
    assign cx2 = (cy1 >= 64'sd0) ? (cx1 + (cy1 >>> 1)) : (cx1 - (cy1 >>> 1));
    assign cy2 = (cy1 >= 64'sd0) ? (cy1 - (cx1 >>> 1)) : (cy1 + (cx1 >>> 1));
    assign cz2 = (cy1 >= 64'sd0) ? (cz1 + 64'sd464) : (cz1 - 64'sd464);

    // Stage 2 (shift = 2, atan(2^-2) = 245 mrad = 14.0 deg)
    assign cx3 = (cy2 >= 64'sd0) ? (cx2 + (cy2 >>> 2)) : (cx2 - (cy2 >>> 2));
    assign cy3 = (cy2 >= 64'sd0) ? (cy2 - (cx2 >>> 2)) : (cy2 + (cx2 >>> 2));
    assign cz3 = (cy2 >= 64'sd0) ? (cz2 + 64'sd245) : (cz2 - 64'sd245);

    // Stage 3 (shift = 3, atan(2^-3) = 124 mrad = 7.1 deg)
    assign cx4 = (cy3 >= 64'sd0) ? (cx3 + (cy3 >>> 3)) : (cx3 - (cy3 >>> 3));
    assign cy4 = (cy3 >= 64'sd0) ? (cy3 - (cx3 >>> 3)) : (cy3 + (cx3 >>> 3));
    assign cz4 = (cy3 >= 64'sd0) ? (cz3 + 64'sd124) : (cz3 - 64'sd124);

    assign cordic_mag_out    = cx4[31:0];
    assign cordic_atan2_mrad = cz4[31:0];

    // 4. Stateful always_ff \Delta\phi[m] = (\phi[m] - \phi[m-1]) mod 2*pi FT8 8-FSK Discriminator
    // Tone k in {0..7} maps to \Delta\phi_k = (k + 1) * 600 mrad (decision half-width = 300 mrad)
    logic signed [63:0] prev_phase_mrad;
    logic signed [63:0] latched_delta_phase_mrad;
    logic [2:0]         latched_tone_bin;
    logic               symbol_valid_reg;
    logic [31:0]        symbol_count_reg;

    logic signed [63:0] raw_diff_mrad;
    logic signed [63:0] wrapped_delta_1;
    logic signed [63:0] wrapped_delta_mrad;
    logic signed [63:0] tone_idx_calc;
    logic [2:0]         comb_tone_bin;

    assign raw_diff_mrad      = cz4 - prev_phase_mrad;
    assign wrapped_delta_1    = (raw_diff_mrad < 64'sd0) ? (raw_diff_mrad + 64'sd6283) : raw_diff_mrad;
    assign wrapped_delta_mrad = (wrapped_delta_1 >= 64'sd6283) ? (wrapped_delta_1 - 64'sd6283) : wrapped_delta_1;
    assign tone_idx_calc      = (wrapped_delta_mrad < 64'sd300) ? 64'sd0 :
                                ((wrapped_delta_mrad - 64'sd300) / 64'sd600);
    assign comb_tone_bin      = (tone_idx_calc > 64'sd7) ? 3'd7 : tone_idx_calc[2:0];

    always_ff @(posedge clk) begin
        if (rst) begin
            cic_int1                 <= 64'sd0;
            cic_int2                 <= 64'sd0;
            cic_int3                 <= 64'sd0;
            cic_comb_d1              <= 64'sd0;
            fir_tap_d1               <= 64'sd0;
            bb_i_d1                  <= 64'sd0;
            bb_i_d2                  <= 64'sd0;
            bb_i_d3                  <= 64'sd0;
            bb_q_d1                  <= 64'sd0;
            bb_q_d2                  <= 64'sd0;
            bb_q_d3                  <= 64'sd0;
            prev_phase_mrad          <= 64'sd0;
            latched_delta_phase_mrad <= 64'sd0;
            latched_tone_bin         <= 3'd0;
            symbol_valid_reg         <= 1'b0;
            symbol_count_reg         <= 32'd0;
        end else if (sample_valid) begin
            // 3-stage CIC integrators & baseband symmetric FIR delay lines
            cic_int1 <= cic_int1_next;
            cic_int2 <= cic_int2_next;
            cic_int3 <= cic_int3_next;

            bb_i_d1  <= desired_usb_mv;
            bb_i_d2  <= bb_i_d1;
            bb_i_d3  <= bb_i_d2;
            bb_q_d1  <= desired_usb_q_mv;
            bb_q_d2  <= bb_q_d1;
            bb_q_d3  <= bb_q_d2;

            if (decim_strobe) begin
                cic_comb_d1 <= cic_int3;
                fir_tap_d1  <= comb_diff;
            end

            if (phase_ref_strobe) begin
                prev_phase_mrad  <= cz4;
                symbol_valid_reg <= 1'b0;
            end else if (symbol_strobe) begin
                prev_phase_mrad          <= cz4;
                latched_delta_phase_mrad <= wrapped_delta_mrad;
                latched_tone_bin         <= comb_tone_bin;
                symbol_valid_reg         <= 1'b1;
                symbol_count_reg         <= symbol_count_reg + 32'd1;
            end else begin
                symbol_valid_reg         <= 1'b0;
            end
        end else begin
            symbol_valid_reg <= 1'b0;
        end
    end

    assign delta_phase_mrad = latched_delta_phase_mrad;
    assign ft8_tone_bin     = latched_tone_bin;
    assign ft8_symbol_valid = symbol_valid_reg;
    assign dbg_symbol_count = symbol_count_reg;

endmodule
