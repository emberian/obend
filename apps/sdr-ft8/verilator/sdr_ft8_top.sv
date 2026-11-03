// Emitted & Verified SystemVerilog for Flagship App #3:
// All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver
// Corresponds to Obend.Apps.SdrFt8.sdrFt8SequentialRtlModule + SdrFt8Top.obend
`timescale 1ns / 1ps

module sdr_ft8_top (
    input  logic        clk,
    input  logic        rst,
    input  logic        sample_valid,
    // R = 64 Hogenauer CIC decimation strobe
    input  logic        decim_strobe,
    // FT8 symbol clock strobe (79 symbols across the 16,384-sample capture window)
    input  logic        symbol_strobe,
    // 16-bit signed Tayloe quadrature I and 90-deg Hilbert Q baseband channels (in mV / LSBs)
    // Desired USB (+1250 Hz): i_mix_mv and q_mix_mv are in-phase (+A, +A)
    // Unwanted LSB image (-1250 Hz): i_mix_mv and q_mix_mv are anti-phase (+A_img, -A_img)
    input  logic signed [31:0] i_mix_mv,
    input  logic signed [31:0] q_mix_mv,
    // 4-stage CORDIC baseband I/Q phasor inputs and unwrapped phase (in mrad)
    input  logic signed [31:0] cordic_x_in,
    input  logic signed [31:0] cordic_y_in,
    input  logic signed [31:0] cordic_phase_mrad,
    // Calibrated I/Q gain trim in permille (500 = matched 0.0 dB / 0.0 deg calibration)
    input  logic signed [31:0] iq_gain_i_permille,
    input  logic signed [31:0] iq_gain_q_permille,
    // Tayloe Hartley/Weaver sideband outputs
    output logic signed [63:0] desired_usb_mv,
    output logic signed [63:0] image_cancel_mv,
    // Stateful 3-stage CIC + Folded Symmetric FIR output
    output logic signed [63:0] cic_stage3_out,
    output logic signed [63:0] folded_fir_out,
    // 4-stage unrolled CORDIC magnitude & stateful delta-phase FT8 8-FSK discriminator outputs
    output logic signed [31:0] cordic_mag_out,
    output logic signed [63:0] delta_phase_mrad,
    output logic [2:0]         ft8_tone_bin,
    output logic               ft8_symbol_valid,
    output logic [31:0]        dbg_symbol_count
);

    // Sign-extended 64-bit Tayloe I/Q mixer channels with programmable gain calibration
    logic signed [63:0] i_mix_64;
    logic signed [63:0] q_mix_64;
    logic signed [63:0] gain_i_64;
    logic signed [63:0] gain_q_64;
    logic signed [63:0] i_cal_64;
    logic signed [63:0] q_cal_64;

    assign i_mix_64  = {{32{i_mix_mv[31]}}, i_mix_mv};
    assign q_mix_64  = {{32{q_mix_mv[31]}}, q_mix_mv};
    assign gain_i_64 = {{32{iq_gain_i_permille[31]}}, iq_gain_i_permille};
    assign gain_q_64 = {{32{iq_gain_q_permille[31]}}, iq_gain_q_permille};

    assign i_cal_64  = (i_mix_64 * gain_i_64) / 64'sd500;
    assign q_cal_64  = (q_mix_64 * gain_q_64) / 64'sd500;

    // Hartley/Weaver quadrature sideband combiner:
    // For desired USB (+f_audio): i_cal_64 == +s, q_cal_64 == +s => desired_usb_mv = 2*s
    // For unwanted LSB image (-f_audio): i_cal_64 == +img, q_cal_64 == -img => cancels to 0!
    assign desired_usb_mv  = i_cal_64 + q_cal_64;
    assign image_cancel_mv = i_cal_64 - q_cal_64;

    // Stateful always_ff 3-stage Hogenauer CIC integrator registers (B_out = 16 + 3*6 = 34 <= 64 bits)
    logic signed [63:0] cic_int1;
    logic signed [63:0] cic_int2;
    logic signed [63:0] cic_int3;

    // Stateful always_ff CIC comb & Folded Symmetric FIR delay-line registers
    logic signed [63:0] cic_comb_d1;
    logic signed [63:0] fir_tap_d1;

    // Stateful always_ff CORDIC previous-symbol phase register \phi[n-1] for \Delta\phi[n] = \phi[n] - \phi[n-1]
    logic signed [63:0] prev_phase_mrad;
    logic signed [63:0] latched_delta_phase_mrad;
    logic [2:0]         latched_tone_bin;
    logic               symbol_valid_reg;
    logic [31:0]        symbol_count_reg;

    // Combinational next-state wires for 3-stage CIC integrators
    logic signed [63:0] cic_int1_next;
    logic signed [63:0] cic_int2_next;
    logic signed [63:0] cic_int3_next;
    logic signed [63:0] comb_diff;

    assign cic_int1_next = cic_int1 + desired_usb_mv;
    assign cic_int2_next = cic_int2 + cic_int1_next;
    assign cic_int3_next = cic_int3 + cic_int2_next;
    assign comb_diff     = cic_int3 - cic_comb_d1;

    // Folded symmetric FIR output: pre-adds symmetric taps (comb_diff + fir_tap_d1) before * 256
    assign cic_stage3_out = comb_diff;
    assign folded_fir_out = (comb_diff + fir_tap_d1) * 64'sd256;

    // 4-Stage Unrolled Vectoring CORDIC (atan2 / hypot) pipeline on (cordic_x_in, cordic_y_in)
    logic signed [63:0] cx0, cy0;
    logic signed [63:0] cx1, cy1;
    logic signed [63:0] cx2, cy2;
    logic signed [63:0] cx3, cy3;
    logic signed [63:0] cx4, cy4;

    assign cx0 = (cordic_x_in >= 0) ? {{32{cordic_x_in[31]}}, cordic_x_in} : -{{32{cordic_x_in[31]}}, cordic_x_in};
    assign cy0 = {{32{cordic_y_in[31]}}, cordic_y_in};

    // Stage 0 (shift = 0, +/- 45.0 deg)
    assign cx1 = (cy0 >= 0) ? (cx0 + cy0) : (cx0 - cy0);
    assign cy1 = (cy0 >= 0) ? (cy0 - cx0) : (cy0 + cx0);
    // Stage 1 (shift = 1, +/- 26.6 deg)
    assign cx2 = (cy1 >= 0) ? (cx1 + (cy1 >>> 1)) : (cx1 - (cy1 >>> 1));
    assign cy2 = (cy1 >= 0) ? (cy1 - (cx1 >>> 1)) : (cy1 + (cx1 >>> 1));
    // Stage 2 (shift = 2, +/- 14.0 deg)
    assign cx3 = (cy2 >= 0) ? (cx2 + (cy2 >>> 2)) : (cx2 - (cy2 >>> 2));
    assign cy3 = (cy2 >= 0) ? (cy2 - (cx2 >>> 2)) : (cy2 + (cx2 >>> 2));
    // Stage 3 (shift = 3, +/- 7.1 deg)
    assign cx4 = (cy3 >= 0) ? (cx3 + (cy3 >>> 3)) : (cx3 - (cy3 >>> 3));
    assign cy4 = (cy3 >= 0) ? (cy3 - (cx3 >>> 3)) : (cy3 + (cx3 >>> 3));

    assign cordic_mag_out = cx4[31:0];

    // Instantaneous phase difference \Delta\phi[n] = \phi[n] - \phi[n-1] (in mrad)
    // FT8 8-FSK tone bin k in {0..7} maps to \Delta\phi_k = (k + 1) * 125 mrad
    logic signed [63:0] phase_in_64;
    logic signed [63:0] raw_delta_phase;
    logic signed [63:0] tone_idx_calc;
    logic [2:0]         comb_tone_bin;

    assign phase_in_64     = {{32{cordic_phase_mrad[31]}}, cordic_phase_mrad};
    assign raw_delta_phase = phase_in_64 - prev_phase_mrad;
    // Nearest-neighbor 8-FSK bin discriminator: round((raw_delta_phase - 125) / 125)
    assign tone_idx_calc   = (raw_delta_phase - 64'sd63) / 64'sd125;
    assign comb_tone_bin   = (tone_idx_calc < 64'sd0) ? 3'd0 :
                             ((tone_idx_calc > 64'sd7) ? 3'd7 : tone_idx_calc[2:0]);

    // Sequential always_ff block: 3-stage CIC, folded FIR delay line, and \Delta\phi FT8 discriminator
    always_ff @(posedge clk) begin
        if (rst) begin
            cic_int1                 <= 64'sd0;
            cic_int2                 <= 64'sd0;
            cic_int3                 <= 64'sd0;
            cic_comb_d1              <= 64'sd0;
            fir_tap_d1               <= 64'sd0;
            prev_phase_mrad          <= 64'sd0;
            latched_delta_phase_mrad <= 64'sd0;
            latched_tone_bin         <= 3'd0;
            symbol_valid_reg         <= 1'b0;
            symbol_count_reg         <= 32'd0;
        end else if (sample_valid) begin
            // 3-stage CIC integrators run at full oversampled rate
            cic_int1 <= cic_int1_next;
            cic_int2 <= cic_int2_next;
            cic_int3 <= cic_int3_next;

            // CIC comb & folded FIR delay line update on R = 64 decimation strobe
            if (decim_strobe) begin
                cic_comb_d1 <= cic_int3;
                fir_tap_d1  <= comb_diff;
            end

            // Stateful \Delta\phi[n] = \phi[n] - \phi[n-1] 8-FSK FT8 symbol discriminator
            if (symbol_strobe) begin
                prev_phase_mrad          <= phase_in_64;
                latched_delta_phase_mrad <= raw_delta_phase;
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
