// HAND-WRITTEN reference RTL (2026-11-04). This file is NOT produced by Obend.Hardware.HDL.emitModuleSV:
// the emitter cannot express signed or narrower-than-64-bit ports, localparams, functions or division.
// The Lean module of the same name (Obend.Apps.ZkNtt.zkNttPipelinedRtlModule / zkSumcheckRoundRtlModule) is a separate, smaller model (64-bit .mul datapaths that never reduce mod the Goldilocks prime);
// no theorem in the tree relates it to this file. The Verilator testbench beside it exercises this file
// against a C++ reference, not against Lean. See review/EXPERT-fpga-silicon-20261103.md §3.1.
module zk_ntt_coproc (
  input  logic        clk,
  input  logic        rst,
  // Inputs for Goldilocks Radix-2 Butterfly + 4-stage reset-free pipeline
  input  logic [63:0] u_in,
  input  logic [63:0] v_in,
  input  logic [63:0] w_in,
  input  logic [63:0] r_in,
  input  logic [63:0] bias_in,
  // Inputs for Stateful Multilinear Sumcheck Round Polynomial Accumulator
  input  logic        sc_clear,
  input  logic        sc_enable,
  input  logic [63:0] sc_f0_in,
  input  logic [63:0] sc_f1_in,
  input  logic [63:0] sc_r_in,
  // Combinational & 4-stage pipelined Goldilocks butterfly outputs
  output logic [63:0] goldilocks_even_out,
  output logic [63:0] goldilocks_odd_out,
  output logic [63:0] pipe4_even_out,
  output logic [63:0] pipe4_odd_out,
  output logic [63:0] pipe4_folded_out,
  output logic [63:0] pipe4_acc_out,
  // Stateful Sumcheck round polynomial outputs (mod Goldilocks prime P)
  output logic [63:0] sc_g0_out,
  output logic [63:0] sc_g1_out,
  output logic [63:0] sc_g2_out,
  output logic [63:0] sc_round_claim_out,
  output logic [63:0] sc_folded_out
);
  localparam logic [63:0] GOLDILOCKS_P = 64'hFFFFFFFF00000001;

  // Canonicalize any 64-bit word into [0, P - 1] (since 2^64 < 2*P, at most one subtraction suffices)
  function automatic logic [63:0] gl_canon(input logic [63:0] x);
    begin
      gl_canon = (x >= GOLDILOCKS_P) ? (x - GOLDILOCKS_P) : x;
    end
  endfunction

  // Canonical Goldilocks modular addition: (a + b) mod P in [0, P - 1] across all 64-bit inputs
  function automatic logic [63:0] gl_add(input logic [63:0] a, input logic [63:0] b);
    logic [63:0] ca;
    logic [63:0] cb;
    logic [64:0] s;
    begin
      ca = gl_canon(a);
      cb = gl_canon(b);
      s  = {1'b0, ca} + {1'b0, cb};
      if (s >= {1'b0, GOLDILOCKS_P})
        gl_add = s[63:0] - GOLDILOCKS_P;
      else
        gl_add = s[63:0];
    end
  endfunction

  // Canonical Goldilocks modular subtraction: (a - b) mod P in [0, P - 1] across all 64-bit inputs
  function automatic logic [63:0] gl_sub(input logic [63:0] a, input logic [63:0] b);
    logic [63:0] ca;
    logic [63:0] cb;
    begin
      ca = gl_canon(a);
      cb = gl_canon(b);
      if (ca >= cb)
        gl_sub = ca - cb;
      else
        gl_sub = GOLDILOCKS_P - (cb - ca);
    end
  endfunction

  // Goldilocks 128-to-64 shift/mask modular reduction using 2^64 == 2^32 - 1 (mod P) and 2^96 == -1 (mod P)
  function automatic logic [63:0] gl_reduce128(input logic [63:0] lo_raw, input logic [63:0] hi_raw);
    logic [63:0] lo;
    logic [63:0] hi_lo32;
    logic [63:0] hi_hi32;
    logic [63:0] term_mid;
    logic [63:0] t1;
    begin
      lo          = gl_canon(lo_raw);
      hi_lo32     = {32'd0, hi_raw[31:0]};
      hi_hi32     = {32'd0, hi_raw[63:32]};
      // hi_lo32 * (2^32 - 1) == (hi_lo32 << 32) - hi_lo32 < 2^64 - 2^32 < P
      term_mid    = (hi_lo32 << 32) - hi_lo32;
      t1          = gl_add(lo, term_mid);
      gl_reduce128 = gl_sub(t1, hi_hi32);
    end
  endfunction

  // Canonical Goldilocks 64x64 modular multiplication: (a * b) mod P in [0, P - 1]
  function automatic logic [63:0] gl_mul(input logic [63:0] a, input logic [63:0] b);
    logic [63:0]  ca;
    logic [63:0]  cb;
    logic [127:0] prod;
    begin
      ca     = gl_canon(a);
      cb     = gl_canon(b);
      prod   = {64'd0, ca} * {64'd0, cb};
      gl_mul = gl_reduce128(prod[63:0], prod[127:64]);
    end
  endfunction

  // 1. Goldilocks Radix-2 Butterfly (Cooley-Tukey: u + w*v mod P, u - w*v mod P)
  logic [63:0] gl_vw;
  always_comb begin
    gl_vw               = gl_mul(v_in, w_in);
    goldilocks_even_out = gl_add(u_in, gl_vw);
    goldilocks_odd_out  = gl_sub(u_in, gl_vw);
  end

  // 2. 4-Stage Reset-Free Pipelined Datapath (matching compileHypergraphToRtlPipelined zkNttOptHypergraph)
  // Stage 1..4 reset-free registers (no reset clause so Verilated::randReset(2) tests pipeline flushing)
  logic [63:0] s1_u, s1_r, s1_bias, s1_vw, s1_even;
  logic [63:0] s2_r, s2_bias, s2_even, s2_odd;
  logic [63:0] s3_r, s3_bias, s3_even, s3_diff;
  logic [63:0] s4_even, s4_odd, s4_folded, s4_acc;

  always_ff @(posedge clk) begin
    // Stage 1 (Layer 0): .mul [v, w] -> vw and fused .mac [v, w, u] -> even
    s1_u      <= u_in;
    s1_r      <= r_in;
    s1_bias   <= bias_in;
    s1_vw     <= (v_in * w_in);
    s1_even   <= (u_in + (v_in * w_in));

    // Stage 2 (Layer 1): .sub [u, vw] -> odd
    s2_r      <= s1_r;
    s2_bias   <= s1_bias;
    s2_even   <= s1_even;
    s2_odd    <= (s1_u - s1_vw);

    // Stage 3 (Layer 2): .sub [odd, even] -> diff
    s3_r      <= s2_r;
    s3_bias   <= s2_bias;
    s3_even   <= s2_even;
    s3_diff   <= (s2_odd - s2_even);

    // Stage 4 (Layer 3): fused .mac [r, diff, even] -> folded and .mac [bias, r, diff] -> acc
    s4_even   <= s3_even;
    s4_odd    <= (s3_even + s3_diff);
    s4_folded <= (s3_even + (s3_r * s3_diff));
    s4_acc    <= (s3_diff + (s3_bias * s3_r));
  end

  always_comb begin
    pipe4_even_out   = s4_even;
    pipe4_odd_out    = s4_odd;
    pipe4_folded_out = s4_folded;
    pipe4_acc_out    = s4_acc;
  end

  // 3. Stateful always_ff Multilinear Sumcheck Round Polynomial Accumulator (mod Goldilocks P)
  logic [63:0] acc_g0, acc_g1, acc_g2, last_folded;
  logic [63:0] sc_g2_term, sc_diff, sc_folded_comb;

  always_comb begin
    sc_g2_term         = gl_sub(gl_add(sc_f1_in, sc_f1_in), sc_f0_in);
    sc_diff            = gl_sub(sc_f1_in, sc_f0_in);
    sc_folded_comb     = gl_add(sc_f0_in, gl_mul(sc_r_in, sc_diff));
    sc_g0_out          = acc_g0;
    sc_g1_out          = acc_g1;
    sc_g2_out          = acc_g2;
    sc_round_claim_out = gl_add(acc_g0, acc_g1);
    sc_folded_out      = last_folded;
  end

  always_ff @(posedge clk) begin
    if (rst || sc_clear) begin
      acc_g0      <= 64'd0;
      acc_g1      <= 64'd0;
      acc_g2      <= 64'd0;
      last_folded <= 64'd0;
    end else if (sc_enable) begin
      acc_g0      <= gl_add(acc_g0, sc_f0_in);
      acc_g1      <= gl_add(acc_g1, sc_f1_in);
      acc_g2      <= gl_add(acc_g2, sc_g2_term);
      last_folded <= sc_folded_comb;
    end
  end
endmodule
