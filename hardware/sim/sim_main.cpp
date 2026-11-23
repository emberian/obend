// Cycle-accurate Verilator differential harness for `hardware/sim/tb_top.sv`:
// Drives multi-cycle vectors through the 4 emitted dark-RTL vault modules + `obend_retimed_mac2`
// and asserts exact cycle-by-cycle pin equality against their Lean specifications:
//   1. `pipelined_risc_core_5stage` (`Obend.Hardware.PipelinedRisc`): closed-loop 45-cycle sum-of-array
//      loop (`[10,20,30,40,50] = 150`, exercising load-use stalls, MEM/WB->EX & EX/MEM->EX bypasses,
//      and taken BNE branch squashes) + 75-cycle Fibonacci(10) = 55 loop + r0 write-ignore attack,
//      checking all 15 output pins on every single clock cycle against the exact `PipeState` model!
//   2. `pipelined_gl_butterfly_4stage` (`Obend.Hardware.PipelinedZkCrypto`): 16 back-to-back streaming
//      Goldilocks radix-2 butterflies at II=1 + 4 drain bubbles, checked cycle-by-cycle against exact
//      128-bit `(u + v*w) mod p` and `(u - v*w) mod p` (`p = 0xFFFFFFFF00000001`).
//   3. `gf2_64_wiedemann_tower_mul` (`Obend.Hardware.PipelinedZkCrypto`): 16 Wiedemann GF(2^64) pairs
//      (including field inverses `a * a^-1 = 1` and defining relation), checking both combinational
//      `tower64_mul_out` and 2-stage pipelined `tower64_pipe_out` / `tower64_pipe_valid` every cycle.
//   4. `obend_ospc_tile0` (`Obend.Hardware.OspcProver.ospcTileDatapathRtl 0`): 81-bit `FaceIdeal4`
//      cubical boundary non-collapse (`(x_0=0) join (x_0=1) != top`), `meet`/`implies`, and write-first
//      synchronous `ExprCAM` BRAM readout (`cam_q` / `out_cam_hit` / `out_cam_word`) every cycle.
//   5. `obend_retimed_mac2`: 2-stage retimed 64-bit MAC with wrap-around corner.

#include "Vtb_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <vector>

static vluint64_t main_time = 0;
double sc_time_stamp() { return static_cast<double>(main_time); }

static uint64_t g_mismatches = 0;

static void check_eq(const char* ctx, const char* pin, uint64_t cyc, uint64_t got, uint64_t exp) {
  if (got != exp) {
    std::fprintf(stderr, "MISMATCH [%s] cyc=%llu pin=%s: got=0x%llx (%llu) exp=0x%llx (%llu)\n",
                 ctx, static_cast<unsigned long long>(cyc), pin,
                 static_cast<unsigned long long>(got), static_cast<unsigned long long>(got),
                 static_cast<unsigned long long>(exp), static_cast<unsigned long long>(exp));
    g_mismatches++;
  }
}

static void zero_all_inputs(Vtb_top* dut) {
  dut->risc_imem_rdata = 0; dut->risc_dmem_rdata = 0;
  dut->risc_rf_rdata1 = 0;  dut->risc_rf_rdata2 = 0;
  dut->bfly_u_in = 0; dut->bfly_v_in = 0; dut->bfly_w_in = 0; dut->bfly_in_valid = 0;
  dut->gf64_a_in = 0; dut->gf64_b_in = 0; dut->gf64_in_valid = 0;
  dut->ospc_op_sel = 0; dut->ospc_in_lo64 = 0; dut->ospc_in_hi17 = 0;
  dut->ospc_cam_we = 0; dut->ospc_cam_addr = 0; dut->ospc_cam_wdata = 0;
  dut->ospc_cam_qtag = 0; dut->ospc_cam_q_in = 0;
  dut->mac_in_a = 0; dut->mac_in_b = 0; dut->mac_in_c = 0;
}

static void pulse_reset(Vtb_top* dut, VerilatedVcdC* tfp) {
  zero_all_inputs(dut);
  dut->rst = 1;
  for (int i = 0; i < 2; ++i) {
    dut->clk = 0; dut->eval(); if (tfp) tfp->dump(main_time); main_time += 5;
    dut->clk = 1; dut->eval(); if (tfp) tfp->dump(main_time); main_time += 5;
  }
  dut->rst = 0;
  dut->clk = 0;
  dut->eval();
}

// ============================================================================
// 1. Reference Model for `Obend.Hardware.PipelinedRisc` (`pipelined_risc_core_5stage`)
// ============================================================================
enum RiscOp : uint8_t {
  OP_NOP = 0, OP_ADD = 1, OP_SUB = 2, OP_AND = 3, OP_OR = 4, OP_XOR = 5,
  OP_SLT = 6, OP_ADDI = 7, OP_LD = 8, OP_ST = 9, OP_BEQ = 10, OP_BNE = 11, OP_JAL = 12
};

struct RiscInstr {
  uint8_t op = OP_NOP;
  uint8_t rd = 0, rs1 = 0, rs2 = 0;
  int64_t imm = 0;
};

static uint64_t encode_instr(RiscInstr ins) {
  uint64_t low20 = static_cast<uint64_t>(ins.op & 0xF) |
                   (static_cast<uint64_t>(ins.rd & 0x1F) << 4) |
                   (static_cast<uint64_t>(ins.rs1 & 0x1F) << 9) |
                   (static_cast<uint64_t>(ins.rs2 & 0x1F) << 14);
  return (static_cast<uint64_t>(ins.imm) << 20) | low20;
}

static RiscInstr mk_r(uint8_t op, uint8_t rd, uint8_t rs1, uint8_t rs2) { return {op, rd, rs1, rs2, 0}; }
static RiscInstr mk_i(uint8_t op, uint8_t rd, uint8_t rs1, int64_t imm) { return {op, rd, rs1, 0, imm}; }
static RiscInstr mk_sb(uint8_t op, uint8_t rs1, uint8_t rs2, int64_t imm) { return {op, 0, rs1, rs2, imm}; }

static bool op_writes_reg(uint8_t op) { return (op >= 1 && op <= 8) || op == 12; }

struct PipeRef {
  uint64_t fetch_pc = 0;
  bool if_valid = false; uint64_t if_pc = 0; RiscInstr if_ins{};
  bool ex_valid = false; uint64_t ex_pc = 0; RiscInstr ex_ins{}; uint64_t ex_v1 = 0, ex_v2 = 0;
  bool em_valid = false; uint8_t em_rd = 0; bool em_rw = false, em_ld = false, em_st = false;
  uint64_t em_alu = 0, em_store = 0;
  bool wb_valid = false; uint8_t wb_rd = 0; bool wb_rw = false; uint64_t wb_val = 0;
  std::array<uint64_t, 32> regs{};
  std::map<uint64_t, uint64_t> dmem;

  uint64_t rf_after_wb(uint8_t r) const {
    if (r == 0) return 0;
    if (wb_valid && wb_rw && wb_rd != 0 && wb_rd == r) return wb_val;
    return regs[r];
  }
  uint64_t dmem_read(uint64_t addr) const {
    auto it = dmem.find(addr);
    return (it == dmem.end()) ? 0ULL : it->second;
  }
  uint64_t fwd(uint8_t rs, uint64_t id_val) const {
    if (em_valid && em_rw && !em_ld && em_rd != 0 && em_rd == rs) return em_alu;
    if (wb_valid && wb_rw && wb_rd != 0 && wb_rd == rs) return wb_val;
    return id_val;
  }
  static uint64_t alu(uint64_t pc, RiscInstr ins, uint64_t v1, uint64_t v2) {
    switch (ins.op) {
      case OP_ADD:  return v1 + v2;
      case OP_SUB:  return v1 - v2;
      case OP_AND:  return v1 & v2;
      case OP_OR:   return v1 | v2;
      case OP_XOR:  return v1 ^ v2;
      case OP_SLT:  return (static_cast<int64_t>(v1) < static_cast<int64_t>(v2)) ? 1ULL : 0ULL;
      case OP_ADDI: case OP_LD: case OP_ST: return v1 + static_cast<uint64_t>(ins.imm);
      case OP_JAL:  return pc + 4ULL;
      default:      return 0ULL;
    }
  }
  static bool br_cond(RiscInstr ins, uint64_t v1, uint64_t v2) {
    if (ins.op == OP_BEQ) return v1 == v2;
    if (ins.op == OP_BNE) return v1 != v2;
    if (ins.op == OP_JAL) return true;
    return false;
  }
};

static void run_risc_program(
    Vtb_top* dut, VerilatedVcdC* tfp, const char* label,
    const std::vector<RiscInstr>& prog, PipeRef ref, uint64_t cycles) {
  pulse_reset(dut, tfp);
  dut->risc_imem_rdata = 0;

  auto fetch_imem = [&](uint64_t pc) -> RiscInstr {
    if (pc % 4 != 0) return {};
    size_t idx = static_cast<size_t>(pc / 4);
    return (idx < prog.size()) ? prog[idx] : RiscInstr{};
  };

  for (uint64_t cyc = 0; cyc < cycles; ++cyc) {
    dut->clk = 0;
    dut->eval();

    // Drive IMEM, DMEM, and WB-forwarded RegFile read ports from DUT's registered addresses:
    RiscInstr fetched = fetch_imem(dut->risc_imem_addr);
    dut->risc_imem_rdata = encode_instr(fetched);
    dut->risc_dmem_rdata = ref.dmem_read(dut->risc_dmem_addr);
    uint8_t ra1 = static_cast<uint8_t>(dut->risc_rf_raddr1 & 0x1F);
    uint8_t ra2 = static_cast<uint8_t>(dut->risc_rf_raddr2 & 0x1F);
    uint64_t wb_en_dut = dut->risc_wb_en;
    uint8_t wb_rd_dut = static_cast<uint8_t>(dut->risc_wb_rd & 0x1F);
    uint64_t wb_data_dut = dut->risc_wb_data;
    dut->risc_rf_rdata1 = (ra1 == 0) ? 0ULL :
      ((wb_en_dut != 0 && wb_rd_dut != 0 && wb_rd_dut == ra1) ? wb_data_dut : ref.regs[ra1]);
    dut->risc_rf_rdata2 = (ra2 == 0) ? 0ULL :
      ((wb_en_dut != 0 && wb_rd_dut != 0 && wb_rd_dut == ra2) ? wb_data_dut : ref.regs[ra2]);
    dut->eval();

    // Compute exact expected combinational outputs from `PipeRef`:
    uint64_t f1 = ref.ex_valid ? ref.fwd(ref.ex_ins.rs1, ref.ex_v1) : 0ULL;
    uint64_t f2 = ref.ex_valid ? ref.fwd(ref.ex_ins.rs2, ref.ex_v2) : 0ULL;
    uint64_t exp_alu = ref.ex_valid ? PipeRef::alu(ref.ex_pc, ref.ex_ins, f1, f2) : 0ULL;
    bool squash = ref.ex_valid && PipeRef::br_cond(ref.ex_ins, f1, f2);
    bool stall = ref.ex_valid && ref.if_valid && (ref.ex_ins.op == OP_LD) && (ref.ex_ins.rd != 0) &&
                 (ref.ex_ins.rd == ref.if_ins.rs1 || ref.ex_ins.rd == ref.if_ins.rs2);

    check_eq(label, "imem_addr",  cyc, dut->risc_imem_addr,  ref.fetch_pc);
    check_eq(label, "rf_raddr1",  cyc, dut->risc_rf_raddr1,  ref.if_valid ? ref.if_ins.rs1 : 0ULL);
    check_eq(label, "rf_raddr2",  cyc, dut->risc_rf_raddr2,  ref.if_valid ? ref.if_ins.rs2 : 0ULL);
    check_eq(label, "ex_fwd1",    cyc, dut->risc_ex_fwd1,    f1);
    check_eq(label, "ex_fwd2",    cyc, dut->risc_ex_fwd2,    f2);
    check_eq(label, "ex_alu_out", cyc, dut->risc_ex_alu_out, exp_alu);
    check_eq(label, "stall_out",  cyc, dut->risc_stall_out,  stall ? 1ULL : 0ULL);
    check_eq(label, "flush_out",  cyc, dut->risc_flush_out,  squash ? 1ULL : 0ULL);
    check_eq(label, "dmem_addr",  cyc, dut->risc_dmem_addr,  ref.em_valid ? ref.em_alu : 0ULL);
    check_eq(label, "dmem_wdata", cyc, dut->risc_dmem_wdata, ref.em_valid ? ref.em_store : 0ULL);
    check_eq(label, "dmem_we",    cyc, dut->risc_dmem_we,    (ref.em_valid && ref.em_st) ? 1ULL : 0ULL);
    check_eq(label, "wb_valid",   cyc, dut->risc_wb_valid,   ref.wb_valid ? 1ULL : 0ULL);
    check_eq(label, "wb_en",      cyc, dut->risc_wb_en,      (ref.wb_valid && ref.wb_rw) ? 1ULL : 0ULL);
    check_eq(label, "wb_rd",      cyc, dut->risc_wb_rd,      ref.wb_valid ? ref.wb_rd : 0ULL);
    check_eq(label, "wb_data",    cyc, dut->risc_wb_data,    ref.wb_valid ? ref.wb_val : 0ULL);

    if (tfp) tfp->dump(main_time);
    main_time += 5;

    // Step `PipeRef` by 1 clock edge (exact mirror of `PipelinedRiscCore.stepPipeline`):
    PipeRef nxt = ref;
    if (ref.wb_valid && ref.wb_rw && ref.wb_rd != 0) nxt.regs[ref.wb_rd] = ref.wb_val;
    if (ref.em_valid && ref.em_st) nxt.dmem[ref.em_alu] = ref.em_store;
    if (ref.em_valid) {
      nxt.wb_valid = true; nxt.wb_rd = ref.em_rd; nxt.wb_rw = ref.em_rw;
      nxt.wb_val = ref.em_ld ? ref.dmem_read(ref.em_alu) : ref.em_alu;
    } else {
      nxt.wb_valid = false; nxt.wb_rd = 0; nxt.wb_rw = false; nxt.wb_val = 0;
    }
    if (ref.ex_valid) {
      nxt.em_valid = true; nxt.em_rd = ref.ex_ins.rd; nxt.em_rw = op_writes_reg(ref.ex_ins.op);
      nxt.em_ld = (ref.ex_ins.op == OP_LD); nxt.em_st = (ref.ex_ins.op == OP_ST);
      nxt.em_alu = exp_alu; nxt.em_store = f2;
    } else {
      nxt.em_valid = false; nxt.em_rd = 0; nxt.em_rw = false; nxt.em_ld = false; nxt.em_st = false;
      nxt.em_alu = 0; nxt.em_store = 0;
    }
    if (squash || stall || !ref.if_valid) {
      nxt.ex_valid = false; nxt.ex_pc = 0; nxt.ex_ins = {}; nxt.ex_v1 = 0; nxt.ex_v2 = 0;
    } else {
      nxt.ex_valid = true; nxt.ex_pc = ref.if_pc; nxt.ex_ins = ref.if_ins;
      nxt.ex_v1 = (ref.if_ins.rs1 == 0) ? 0ULL : nxt.regs[ref.if_ins.rs1];
      nxt.ex_v2 = (ref.if_ins.rs2 == 0) ? 0ULL : nxt.regs[ref.if_ins.rs2];
    }
    if (squash) {
      nxt.if_valid = false; nxt.if_pc = 0; nxt.if_ins = {};
      nxt.fetch_pc = ref.ex_pc + static_cast<uint64_t>(ref.ex_ins.imm);
    } else if (stall) {
      nxt.if_valid = ref.if_valid; nxt.if_pc = ref.if_pc; nxt.if_ins = ref.if_ins;
      nxt.fetch_pc = ref.fetch_pc;
    } else {
      nxt.if_valid = true; nxt.if_pc = ref.fetch_pc; nxt.if_ins = fetch_imem(ref.fetch_pc);
      nxt.fetch_pc = ref.fetch_pc + 4ULL;
    }
    ref = nxt;

    dut->clk = 1;
    dut->eval();
    if (tfp) tfp->dump(main_time);
    main_time += 5;
  }

  if (std::string(label) == "risc64_sum_array") {
    check_eq(label, "final_dmem[64]", cycles, ref.dmem_read(64), 150ULL);
    check_eq(label, "final_r3",       cycles, ref.regs[3],       150ULL);
  } else if (std::string(label) == "risc64_fib10") {
    check_eq(label, "final_dmem[64]", cycles, ref.dmem_read(64), 55ULL);
    check_eq(label, "final_r1",       cycles, ref.regs[1],       55ULL);
  } else if (std::string(label) == "risc64_r0_double_writer") {
    check_eq(label, "final_r0",       cycles, ref.regs[0],       0ULL);
    check_eq(label, "final_r2",       cycles, ref.regs[2],       16ULL);
    check_eq(label, "final_r3",       cycles, ref.regs[3],       1ULL);
  }
}

// ============================================================================
// 2. Reference Arithmetic for Goldilocks (`p = 2^64 - 2^32 + 1`) & Wiedemann GF(2^64)
// ============================================================================
static constexpr __uint128_t GL_P = static_cast<__uint128_t>(0xFFFFFFFF00000001ULL);

static uint64_t gl_even(uint64_t u, uint64_t v, uint64_t w) {
  __uint128_t prod = (static_cast<__uint128_t>(v) * static_cast<__uint128_t>(w)) % GL_P;
  return static_cast<uint64_t>((static_cast<__uint128_t>(u) % GL_P + prod) % GL_P);
}

static uint64_t gl_odd(uint64_t u, uint64_t v, uint64_t w) {
  __uint128_t prod = (static_cast<__uint128_t>(v) * static_cast<__uint128_t>(w)) % GL_P;
  return static_cast<uint64_t>((static_cast<__uint128_t>(u) % GL_P + GL_P - prod) % GL_P);
}

static uint64_t tower_mul_omega(int k, uint64_t u) {
  if (k == 0) return u & 1ULL;
  int half = 1 << (k - 1);
  uint64_t mask = (half == 64) ? ~0ULL : ((1ULL << half) - 1ULL);
  uint64_t u0 = u & mask;
  uint64_t u1 = (u >> half) & mask;
  return u1 | ((u0 ^ tower_mul_omega(k - 1, u1)) << half);
}

static uint64_t tower_mul(int k, uint64_t a, uint64_t b) {
  if (k == 0) return (a & b) & 1ULL;
  int half = 1 << (k - 1);
  uint64_t mask = (half == 64) ? ~0ULL : ((1ULL << half) - 1ULL);
  uint64_t a0 = a & mask, a1 = (a >> half) & mask;
  uint64_t b0 = b & mask, b1 = (b >> half) & mask;
  uint64_t p0 = tower_mul(k - 1, a0, b0);
  uint64_t p1 = tower_mul(k - 1, a1, b1);
  uint64_t p01 = tower_mul(k - 1, a0 ^ a1, b0 ^ b1);
  uint64_t lo = p0 ^ p1;
  uint64_t hi = (p01 ^ lo) ^ tower_mul_omega(k - 1, p1);
  return lo | (hi << half);
}

static uint64_t tower_inv(int k, uint64_t a) {
  if (k == 0) return a & 1ULL;
  int half = 1 << (k - 1);
  uint64_t mask = (half == 64) ? ~0ULL : ((1ULL << half) - 1ULL);
  uint64_t a0 = a & mask, a1 = (a >> half) & mask;
  uint64_t a0s = a0 ^ tower_mul_omega(k - 1, a1);
  uint64_t d = tower_inv(k - 1, tower_mul(k - 1, a0, a0s) ^ tower_mul(k - 1, a1, a1));
  return tower_mul(k - 1, d, a0s) | (tower_mul(k - 1, d, a1) << half);
}

int main(int argc, char** argv) {
  Verilated::commandArgs(argc, argv);
  Verilated::randReset(2);
  Verilated::traceEverOn(true);
  Vtb_top* dut = new Vtb_top;
  VerilatedVcdC* tfp = new VerilatedVcdC;
  dut->trace(tfp, 99);
  tfp->open("sim_tb_top.vcd");

  auto tick_edge = [&]() {
    dut->clk = 0; dut->eval(); if (tfp) tfp->dump(main_time); main_time += 5;
    dut->clk = 1; dut->eval(); if (tfp) tfp->dump(main_time); main_time += 5;
  };

  // --------------------------------------------------------------------------
  // Suite 1: 5-Stage 64-Bit RISC Core (`pipelined_risc_core_5stage`)
  // --------------------------------------------------------------------------
  {
    // 1A. Sum-of-array `[10, 20, 30, 40, 50] = 150` (load-use stall + MEM/WB->EX + EX/MEM->EX + taken BNE):
    std::vector<RiscInstr> sum_prog = {
      mk_i(OP_ADDI, 1, 0, 0),    // pc 0:  ptr = 0
      mk_i(OP_ADDI, 2, 0, 40),   // pc 4:  end = 40
      mk_i(OP_ADDI, 3, 0, 0),    // pc 8:  sum = 0
      mk_i(OP_LD,   4, 1, 0),    // pc 12: val = dmem[ptr]
      mk_r(OP_ADD,  3, 3, 4),    // pc 16: sum += val (1-cycle load-use stall!)
      mk_i(OP_ADDI, 1, 1, 8),    // pc 20: ptr += 8
      mk_sb(OP_BNE, 1, 2, -12),  // pc 24: if ptr != 40 goto 12 (taken branch squash!)
      mk_sb(OP_ST,  0, 3, 64)    // pc 28: dmem[64] = sum = 150
    };
    PipeRef sum_init;
    sum_init.dmem[0] = 10; sum_init.dmem[8] = 20; sum_init.dmem[16] = 30;
    sum_init.dmem[24] = 40; sum_init.dmem[32] = 50;
    run_risc_program(dut, tfp, "risc64_sum_array", sum_prog, sum_init, 50);

    // 1B. Fibonacci(10) = 55 loop:
    std::vector<RiscInstr> fib_prog = {
      mk_i(OP_ADDI, 1, 0, 0),    // a = 0
      mk_i(OP_ADDI, 2, 0, 1),    // b = 1
      mk_i(OP_ADDI, 3, 0, 10),   // n = 10
      mk_r(OP_ADD,  4, 1, 2),    // next = a + b
      mk_r(OP_ADD,  1, 0, 2),    // a = b
      mk_r(OP_ADD,  2, 0, 4),    // b = next
      mk_i(OP_ADDI, 3, 3, -1),   // n = n - 1
      mk_sb(OP_BNE, 3, 0, -16),  // if n != 0 goto 12
      mk_sb(OP_ST,  0, 1, 64)    // dmem[64] = F(10) = 55
    };
    run_risc_program(dut, tfp, "risc64_fib10", fib_prog, PipeRef{}, 80);

    // 1C. Double-writer priority (`EX/MEM` over stale `MEM/WB`) + `r0` write-ignore attack:
    std::vector<RiscInstr> r0_dw_prog = {
      mk_i(OP_ADDI, 1, 0, 5),
      mk_i(OP_ADDI, 1, 1, 10),
      mk_i(OP_ADDI, 2, 1, 1),    // r2 = 16 (not stale 6)
      mk_i(OP_ADDI, 0, 0, 99),   // attempt to corrupt r0
      mk_i(OP_ADDI, 3, 0, 1)     // r3 = r0 + 1 = 1
    };
    run_risc_program(dut, tfp, "risc64_r0_double_writer", r0_dw_prog, PipeRef{}, 14);
  }

  // --------------------------------------------------------------------------
  // Suite 2 & 3: Streaming 4-Stage Goldilocks Butterfly + 2-Stage GF(2^64) Karatsuba
  // --------------------------------------------------------------------------
  {
    pulse_reset(dut, tfp);
    struct GlVec { uint64_t u, v, w; };
    const std::vector<GlVec> gl16 = {
      {0ULL,                  1ULL,                  1ULL},
      {1ULL,                  0xFFFFFFFF00000000ULL, 0xFFFFFFFF00000000ULL},
      {0xFFFFFFFF00000000ULL, 0x0000000100000000ULL, 0x0000000100000000ULL},
      {0xFFFFFFFF00000001ULL, 0x123456789ABCDEF0ULL, 0xFEDCBA9876543210ULL},
      {0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL},
      {0x00000000FFFFFFFFULL, 0xFFFFFFFF00000000ULL, 0x00000000FFFFFFFFULL},
      {0x8000000000000000ULL, 0x8000000000000000ULL, 0x0000000000000002ULL},
      {0x0123456789ABCDEFULL, 0x1111111122222222ULL, 0x3333333344444444ULL},
      {0xCAFEBABEDEADBEEFULL, 0x0F0E0D0C0B0A0908ULL, 0x8070605040302010ULL},
      {0x000000000000002AULL, 0xFFFFFFFF00000000ULL, 0x0000000000000007ULL},
      {0x7FFFFFFF80000001ULL, 0x7FFFFFFF80000002ULL, 0x7FFFFFFF80000003ULL},
      {0xFFFFFFFF00000005ULL, 0xFFFFFFFF00000009ULL, 0xFFFFFFFF0000000BULL},
      {0xAAAAAAAAAAAAAAAAULL, 0x5555555555555555ULL, 0xC3C3C3C3C3C3C3C3ULL},
      {0x0000000200000003ULL, 0xFFFFFFFE00000004ULL, 0xFFFFFFFD00000005ULL},
      {0x9999999988888888ULL, 0x7777777766666666ULL, 0x5555555544444444ULL},
      {0xDEADC0DECAFE1234ULL, 0xFEEDFACE13579BDFULL, 0x2468ACE0FDB97531ULL}
    };

    const std::vector<uint64_t> gf_samples = {
      0x0000000000000001ULL, 0x0000000000000002ULL, 0x0123456789ABCDEFULL, 0xFEDCBA9876543210ULL,
      0xFFFFFFFFFFFFFFFFULL, 0x8000000000000001ULL, 0xDEADBEEFCAFEBABEULL, 0x5A5A5A5AA5A5A5A5ULL
    };
    std::vector<std::pair<uint64_t, uint64_t>> gf16;
    for (uint64_t a : gf_samples) gf16.push_back({a, tower_inv(6, a)});
    for (size_t i = 0; i < 8; ++i) gf16.push_back({gf_samples[i], gf_samples[7 - i]});

    for (size_t cyc = 0; cyc < 20; ++cyc) {
      bool bfly_v = (cyc < 16);
      GlVec gv = bfly_v ? gl16[cyc] : GlVec{0xDEADULL, 0xBEEFULL, 0xCAFEULL};
      dut->bfly_u_in = gv.u; dut->bfly_v_in = gv.v; dut->bfly_w_in = gv.w;
      dut->bfly_in_valid = bfly_v ? 1 : 0;

      bool gf_v = (cyc < 16);
      auto gp = gf_v ? gf16[cyc] : std::pair<uint64_t, uint64_t>{0ULL, 0ULL};
      dut->gf64_a_in = gp.first; dut->gf64_b_in = gp.second;
      dut->gf64_in_valid = gf_v ? 1 : 0;

      dut->clk = 0;
      dut->eval();

      // Combinational GF(2^64) output settles immediately on cycle `cyc`:
      uint64_t exp_comb = tower_mul(6, gp.first, gp.second);
      check_eq("gf2_64_comb", "tower64_mul_out", cyc, dut->gf64_mul_out, exp_comb);
      if (cyc < 8) check_eq("gf2_64_inv", "a * a^-1 == 1", cyc, dut->gf64_mul_out, 1ULL);

      // Clock edge advances pipeline stages by 1:
      tick_edge();

      // After `cyc + 1` clock edges:
      // - Goldilocks Stage 4 holds input `cyc - 3` (valid iff `3 <= cyc && cyc - 3 < 16`):
      if (cyc < 3) {
        check_eq("gl_bfly4", "out_valid_warmup", cyc, dut->bfly_out_valid, 0ULL);
      } else {
        size_t src = cyc - 3;
        if (src < 16) {
          check_eq("gl_bfly4", "out_valid", cyc, dut->bfly_out_valid, 1ULL);
          check_eq("gl_bfly4", "out_even",  cyc, dut->bfly_out_even,  gl_even(gl16[src].u, gl16[src].v, gl16[src].w));
          check_eq("gl_bfly4", "out_odd",   cyc, dut->bfly_out_odd,   gl_odd(gl16[src].u, gl16[src].v, gl16[src].w));
        } else {
          check_eq("gl_bfly4", "out_valid_drain", cyc, dut->bfly_out_valid, 0ULL);
        }
      }

      // - GF(2^64) Stage 2 holds input `cyc - 1` (valid iff `1 <= cyc && cyc - 1 < 16`):
      if (cyc < 1) {
        check_eq("gf2_64_pipe2", "pipe_valid_warmup", cyc, dut->gf64_pipe_valid, 0ULL);
      } else {
        size_t src = cyc - 1;
        if (src < 16) {
          check_eq("gf2_64_pipe2", "pipe_valid", cyc, dut->gf64_pipe_valid, 1ULL);
          check_eq("gf2_64_pipe2", "pipe_out",   cyc, dut->gf64_pipe_out,   tower_mul(6, gf16[src].first, gf16[src].second));
        } else {
          check_eq("gf2_64_pipe2", "pipe_valid_drain", cyc, dut->gf64_pipe_valid, 0ULL);
        }
      }
    }
  }

  // --------------------------------------------------------------------------
  // Suite 4: OSPC Tile 0 (`FaceIdeal4` 81-Bit Ternary 4-Cube + Write-First `ExprCAM`)
  // --------------------------------------------------------------------------
  {
    pulse_reset(dut, tfp);
    std::array<uint64_t, 256> cam_ram{};

    // Compute `varEq0(0)` and `varEq1(0)` over `{0, 1, *}^4` (81 ternary points, interior at bit 80):
    uint64_t v0_lo = 0, v1_lo = 0;
    uint32_t v0_hi = 0, v1_hi = 0;
    for (int idx = 0; idx < 81; ++idx) {
      int coord0 = idx % 3;
      if (coord0 == 0) {
        if (idx < 64) v0_lo |= (1ULL << idx); else v0_hi |= (1U << (idx - 64));
      } else if (coord0 == 1) {
        if (idx < 64) v1_lo |= (1ULL << idx); else v1_hi |= (1U << (idx - 64));
      }
    }

    auto step_ospc = [&](uint64_t cyc, uint8_t op_sel, uint64_t in_lo, uint32_t in_hi,
                         uint8_t we, uint8_t addr, uint64_t wdata, uint64_t qtag) {
      dut->ospc_op_sel = op_sel & 3;
      dut->ospc_in_lo64 = in_lo;
      dut->ospc_in_hi17 = in_hi & 0x1FFFFU;
      dut->ospc_cam_we = we & 1;
      dut->ospc_cam_addr = addr;
      dut->ospc_cam_wdata = wdata;
      dut->ospc_cam_qtag = qtag;
      dut->clk = 0;
      dut->eval();

      // Drive write-first BRAM readout `cam_q_in` from DUT's `cam_bank_*` outputs (`ospcTileDatapathInputs 0`):
      uint8_t raddr = dut->ospc_cam_bank_raddr;
      uint8_t bwe   = dut->ospc_cam_bank_we & 1;
      uint8_t waddr = dut->ospc_cam_bank_waddr;
      uint64_t bwdata = dut->ospc_cam_bank_wdata;
      check_eq("ospc_tile0", "cam_bank_raddr", cyc, raddr, addr);
      check_eq("ospc_tile0", "cam_bank_we",    cyc, bwe,   we & 1);
      dut->ospc_cam_q_in = (bwe && waddr == raddr) ? bwdata : cam_ram[raddr];
      dut->eval();
      if (bwe) cam_ram[waddr] = bwdata;
      tick_edge();
    };

    // Cycle 0: load `varEq0(0)` (`op_sel = 3`), write `0xCAFE000100020003` into `cam_bank[7]`:
    step_ospc(0, 3, v0_lo, v0_hi, 1, 7, 0xCAFE000100020003ULL, 0xCAFE000100020003ULL);
    check_eq("ospc_tile0", "load_lo64", 0, dut->ospc_out_face_lo64, v0_lo);
    check_eq("ospc_tile0", "load_hi17", 0, dut->ospc_out_face_hi17, v0_hi);
    check_eq("ospc_tile0", "cam_word",  0, dut->ospc_out_cam_word,  0xCAFE000100020003ULL);

    // Cycle 1: join `varEq1(0)` (`op_sel = 2`), read `cam_bank[7]` without write (`we = 0`):
    step_ospc(1, 2, v1_lo, v1_hi, 0, 7, 0ULL, 0xCAFE000100020003ULL);
    dut->ospc_in_lo64 = ~0ULL; dut->ospc_in_hi17 = 0x1FFFFU;
    dut->ospc_cam_qtag = 0xCAFE000100020003ULL;
    dut->eval();
    check_eq("ospc_tile0", "join_lo64",        1, dut->ospc_out_face_lo64, v0_lo | v1_lo);
    check_eq("ospc_tile0", "join_hi17",        1, dut->ospc_out_face_hi17, v0_hi | v1_hi);
    // Interior `(*,*,*,*)` at bit 16 of `hi17` MUST remain 0 (`faceIdeal4_boundary_ne_top`!):
    check_eq("ospc_tile0", "interior_excluded", 1, (dut->ospc_out_face_hi17 >> 16) & 1U, 0ULL);
    check_eq("ospc_tile0", "entails_top",       1, dut->ospc_out_entails, 1ULL);
    check_eq("ospc_tile0", "cam_hit_true",      1, dut->ospc_out_cam_hit, 1ULL);

    // Check non-entailment when `arg = varEq0(0)` (`(x_0=0 | x_0=1)` does NOT imply `x_0=0`):
    dut->ospc_in_lo64 = v0_lo; dut->ospc_in_hi17 = v0_hi;
    dut->ospc_cam_qtag = 0xDEADBEEFULL;
    dut->eval();
    check_eq("ospc_tile0", "not_entails_v0", 1, dut->ospc_out_entails, 0ULL);
    check_eq("ospc_tile0", "cam_hit_false",  1, dut->ospc_out_cam_hit, 0ULL);

    // Cycle 2: meet with `varEq0(0)` (`op_sel = 1`) recovers `varEq0(0)`, which entails `varEq0(0)`:
    step_ospc(2, 1, v0_lo, v0_hi, 0, 7, 0ULL, 0xCAFE000100020003ULL);
    dut->ospc_in_lo64 = v0_lo; dut->ospc_in_hi17 = v0_hi;
    dut->eval();
    check_eq("ospc_tile0", "meet_lo64",  2, dut->ospc_out_face_lo64, v0_lo);
    check_eq("ospc_tile0", "meet_hi17",  2, dut->ospc_out_face_hi17, v0_hi);
    check_eq("ospc_tile0", "entails_v0", 2, dut->ospc_out_entails,   1ULL);
  }

  // --------------------------------------------------------------------------
  // Suite 5: 2-Stage Retimed 64-Bit MAC (`obend_retimed_mac2`)
  // --------------------------------------------------------------------------
  {
    dut->mac_in_a = 7ULL; dut->mac_in_b = 9ULL; dut->mac_in_c = 11ULL;
    tick_edge(); tick_edge();
    check_eq("retimed_mac2", "7*9+11", 0, dut->mac_out_y, 74ULL);

    dut->mac_in_a = 0xFFFFFFFFULL; dut->mac_in_b = 0x100000001ULL; dut->mac_in_c = 1ULL;
    tick_edge(); tick_edge();
    check_eq("retimed_mac2", "wrap_u64", 1, dut->mac_out_y, 0ULL);
  }

  tfp->close();
  delete tfp;
  delete dut;
  std::printf("VERILATE_PASS module=tb_top mismatches=%llu\n",
              static_cast<unsigned long long>(g_mismatches));
  return (g_mismatches == 0) ? 0 : 1;
}
