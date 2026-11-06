// HAND-WRITTEN wiring only (no logic): the emitted tuning NCO and two copies of the emitted CIC (I and
// Q) on the 12 kHz sample clock, and the emitted FT8 discriminator on the decimated clock. Every
// submodule is generated from Lean (sdr_nco_mix.sv from Obend.Apps.SdrFt8Rx.sdrNcoModule,
// sdr_cic3_r64.sv from sdrCicModule, sdr_ft8_disc.sv from sdrFt8DiscModule) and LEC'd against its
// RtlModule by verify_sdr_ft8.sh.
`timescale 1ns / 1ps
module sdr_ft8_rx_top (
    input  logic        clk,
    input  logic        dclk,
    input  logic        rst,
    input  logic [15:0] i_in,
    input  logic [15:0] q_in,
    input  logic [31:0] phase_inc,
    input  logic        decim_strobe,
    input  logic        acc_clr,
    input  logic        acc_en,
    input  logic        sym_latch,
    output logic [15:0] nco_i,
    output logic [15:0] nco_q,
    output logic [33:0] i_cic,
    output logic [33:0] q_cic,
    output logic [2:0]  tone_bin,
    output logic        tone_oob,
    output logic [31:0] angle_urad
);
    sdr_nco_mix nco (.clk(clk), .rst(rst), .i_in(i_in), .q_in(q_in), .phase_inc(phase_inc), .out_i(nco_i), .out_q(nco_q));
    sdr_cic3_r64 cic_i (.clk(clk), .rst(rst), .x_in(nco_i), .decim_strobe(decim_strobe), .cic_out(i_cic));
    sdr_cic3_r64 cic_q (.clk(clk), .rst(rst), .x_in(nco_q), .decim_strobe(decim_strobe), .cic_out(q_cic));
    sdr_ft8_disc disc (.clk(dclk), .rst(rst), .i_cic(i_cic), .q_cic(q_cic), .acc_clr(acc_clr),
                       .acc_en(acc_en), .sym_latch(sym_latch), .tone_bin(tone_bin), .tone_oob(tone_oob),
                       .angle_urad(angle_urad));
endmodule
