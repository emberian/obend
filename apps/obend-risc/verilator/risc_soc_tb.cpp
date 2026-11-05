#include "Vobend_risc_cpu.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <cstdint>
#include <fstream>
#include <map>
#include <sstream>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::randReset(2);
    Verilated::traceEverOn(true);

    const char* hex_path = (argc > 1) ? argv[1] : "../firmware/test_prog.hex";
    const char* vcd_path = (argc > 2) ? argv[2] : "obend_risc_trace.vcd";

    std::vector<uint64_t> imem(64, 0x00000013ULL);
    std::vector<uint64_t> dmem(64, 0ULL);

    std::ifstream hex_file(hex_path);
    if (!hex_file.is_open()) {
        std::cerr << "[FATAL] Failed to open firmware hex file: " << hex_path << std::endl;
        return 1;
    }
    std::string line;
    size_t idx = 0;
    while (std::getline(hex_file, line) && idx < imem.size()) {
        if (line.empty() || line[0] == '#') continue;
        uint64_t word = 0;
        std::stringstream ss;
        ss << std::hex << line;
        ss >> word;
        imem[idx++] = word;
    }
    std::cout << "[ObendRisc] Loaded " << idx << " instruction words from " << hex_path << std::endl;

    Vobend_risc_cpu* top = new Vobend_risc_cpu;
    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open(vcd_path);

    vluint64_t sim_time = 0;
    auto tick = [&]() {
        uint64_t i_idx = (top->pc_out >> 2) & 63ULL;
        top->imem_rdata = imem[i_idx];
        uint64_t d_idx = top->dmem_addr & 63ULL;
        top->dmem_rdata = dmem[d_idx];

        top->clk = 0;
        top->eval();
        tfp->dump(sim_time++);

        // Re-evaluate combinational outputs (imem_addr -> dmem_addr -> dmem_rdata) before posedge
        i_idx = (top->imem_addr >> 2) & 63ULL;
        top->imem_rdata = imem[i_idx];
        top->eval();
        d_idx = top->dmem_addr & 63ULL;
        top->dmem_rdata = dmem[d_idx];
        top->eval();

        if (!top->rst && top->dmem_we != 0ULL) {
            dmem[top->dmem_addr & 63ULL] = top->dmem_wdata;
        }

        top->clk = 1;
        top->eval();
        tfp->dump(sim_time++);
    };

    // =========================================================================
    // Phase A: Firmware Verification (test_prog.hex, 21 retirement cycles)
    // =========================================================================
    top->rst = 1;
    top->imem_rdata = 0;
    top->dmem_rdata = 0;
    tick();
    tick();
    top->rst = 0;

    bool saw_trap_entry = false;
    bool saw_csrrs_mcause = false;
    bool saw_mret_restore = false;

    for (int cycle = 0; cycle < 21; ++cycle) {
        uint64_t cur_pc = top->pc_out;
        uint64_t cur_inst = imem[(cur_pc >> 2) & 63ULL];
        tick();

        std::printf(
            "[Cycle %2d] PC=0x%02llx INST=0x%08llx -> nextPC=0x%02llx mstatus=%llu mepc=0x%02llx mcause=%llu x8=%llu x9=%llu x10=%llu x14=%llu x15=%llu\n",
            cycle,
            (unsigned long long)cur_pc,
            (unsigned long long)cur_inst,
            (unsigned long long)top->pc_out,
            (unsigned long long)top->mstatus_out,
            (unsigned long long)top->mepc_out,
            (unsigned long long)top->mcause_out,
            (unsigned long long)top->x8_out,
            (unsigned long long)top->x9_out,
            (unsigned long long)top->x10_out,
            (unsigned long long)top->x14_out,
            (unsigned long long)top->x15_out);

        if (cycle == 8) {
            // Cycle 8 retired standard ECALL (0x00000073) at PC=0x20:
            // verify jump to MTVEC=0x50, mepc=0x24, mcause=11, mstatus=24, and x9 unclobbered (0)
            if (top->pc_out == 0x50ULL && top->mepc_out == 0x24ULL &&
                top->mcause_out == 11ULL && top->mstatus_out == 24ULL && top->x9_out == 0ULL) {
                saw_trap_entry = true;
            }
        }
        if (cycle == 9) {
            // Cycle 9 retired CSRRS x9, mcause, x0 (0x342024F3) at PC=0x50: verify x9 == 11
            if (top->x9_out == 11ULL) {
                saw_csrrs_mcause = true;
            }
        }
        if (cycle == 11) {
            // Cycle 11 retired MRET (0x30200073) at PC=0x58: verify return to MEPC=0x24, mstatus=8, x10=42
            if (top->pc_out == 0x24ULL && top->mstatus_out == 8ULL && top->x10_out == 42ULL) {
                saw_mret_restore = true;
            }
        }
    }

    // Verify 8-element Fibonacci sequence in x1..x8
    const uint64_t expected_fib[8] = {1, 1, 2, 3, 5, 8, 13, 21};
    const uint64_t actual_fib[8] = {
        top->x1_out, top->x2_out, top->x3_out, top->x4_out,
        top->x5_out, top->x6_out, top->x7_out, top->x8_out
    };
    // Lean golden (obend-emit-sv golden-risc, from runRiscFirmwareSocCycles 21): every architectural
    // register, the CSRs and the data memory after the same 21 cycles must agree bit for bit.
    {
        const char* golden_path = (argc > 3) ? argv[3] : "risc_golden.txt";
        std::ifstream gin(golden_path);
        if (!gin.is_open()) {
            std::cerr << "[FAIL] cannot open Lean golden " << golden_path << " (run obend-emit-sv golden-risc)" << std::endl;
            return 1;
        }
        std::map<std::string, uint64_t> golden;
        std::string line;
        while (std::getline(gin, line)) {
            if (line.empty() || line[0] == '#') continue;
            size_t eq = line.find('=');
            if (eq == std::string::npos) continue;
            golden[line.substr(0, eq)] = std::stoull(line.substr(eq + 1));
        }
        const uint64_t hw_regs[36] = {
            top->pc_out, top->mstatus_out, top->mepc_out, top->mcause_out, top->cycle_cnt_out,
            top->x1_out, top->x2_out, top->x3_out, top->x4_out, top->x5_out, top->x6_out, top->x7_out,
            top->x8_out, top->x9_out, top->x10_out, top->x11_out, top->x12_out, top->x13_out, top->x14_out,
            top->x15_out, top->x16_out, top->x17_out, top->x18_out, top->x19_out, top->x20_out, top->x21_out,
            top->x22_out, top->x23_out, top->x24_out, top->x25_out, top->x26_out, top->x27_out, top->x28_out,
            top->x29_out, top->x30_out, top->x31_out };
        const char* names[36] = { "pc", "mstatus", "mepc", "mcause", "cycle_cnt",
            "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15",
            "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29",
            "x30", "x31" };
        size_t compared = 0;
        for (int k = 0; k < 36; ++k) {
            auto it = golden.find(names[k]);
            if (it == golden.end()) { std::cerr << "[FAIL] golden lacks " << names[k] << std::endl; return 1; }
            if (it->second != hw_regs[k]) {
                std::cerr << "[FAIL] Lean golden mismatch on " << names[k] << ": lean=" << it->second
                          << " verilator=" << hw_regs[k] << std::endl;
                return 1;
            }
            compared++;
        }
        for (int a = 0; a < 64; ++a) {
            auto it = golden.find("dmem" + std::to_string(a));
            if (it == golden.end()) { std::cerr << "[FAIL] golden lacks dmem" << a << std::endl; return 1; }
            if (it->second != dmem[a]) {
                std::cerr << "[FAIL] Lean golden mismatch on dmem[" << a << "]: lean=" << it->second
                          << " verilator=" << dmem[a] << std::endl;
                return 1;
            }
            compared++;
        }
        std::cout << "[PASS] Phase A matches the Lean golden (" << compared << " values, 21 cycles)" << std::endl;
    }

    for (int i = 0; i < 8; ++i) {
        if (actual_fib[i] != expected_fib[i]) {
            std::cerr << "[FAIL] Fibonacci mismatch at x" << (i + 1)
                      << ": expected " << expected_fib[i] << ", got " << actual_fib[i] << std::endl;
            return 1;
        }
    }

    if (!saw_trap_entry || !saw_csrrs_mcause || !saw_mret_restore) {
        std::cerr << "[FAIL] CSR trap/csrrs/mret verification failed (trap="
                  << saw_trap_entry << ", csrrs=" << saw_csrrs_mcause
                  << ", mret=" << saw_mret_restore << ")" << std::endl;
        return 1;
    }

    // Verify 4 CustomSimdZkExt MAC instructions in x11..x14
    if (top->x11_out != 105ULL || top->x12_out != 212ULL ||
        top->x13_out != 639ULL || top->x14_out != 1282ULL) {
        std::cerr << "[FAIL] CustomSimdZkExt MAC register mismatch: x11=" << top->x11_out
                  << " x12=" << top->x12_out << " x13=" << top->x13_out
                  << " x14=" << top->x14_out << std::endl;
        return 1;
    }

    // Verify final checksum in x15, dmem[0]=1345, non-zero S-type SW dmem[8]=1282, and LW readback x9=1282
    if (top->x15_out != 1345ULL || dmem[0] != 1345ULL || dmem[8] != 1282ULL || top->x9_out != 1282ULL) {
        std::cerr << "[FAIL] Final checksum/load-store mismatch: x15=" << top->x15_out
                  << " dmem[0]=" << dmem[0] << " dmem[8]=" << dmem[8]
                  << " x9=" << top->x9_out << std::endl;
        return 1;
    }
    std::cout << "[PASS] Phase A (test_prog.hex): Fib8=21, ECALL/CSRRS/MRET x10=42, "
              << "CustomSimdZkExt MAC4=1282, dmem[0]=1345, dmem[8]=x9=1282" << std::endl;

    // =========================================================================
    // Phase B: Adversarial Signed RV64I/M, Negative S/B-Type & Dual-Trap Torture
    // =========================================================================
    std::fill(imem.begin(), imem.end(), 0x00000013ULL);
    std::fill(dmem.begin(), dmem.end(), 0ULL);

    // 0x00: addi x1, x0, -5         (0xFFB00093 -> x1 = -5 = 0xFFFFFFFFFFFFFFFB)
    // 0x04: addi x2, x0, 12         (0x00C00113 -> x2 = 12)
    // 0x08: sub  x3, x1, x2         (0x402081B3 -> x3 = -17 = 0xFFFFFFFFFFFFFFEF)
    // 0x0C: mul  x4, x1, x2         (0x02208233 -> x4 = -60 = 0xFFFFFFFFFFFFFFC4)
    // 0x10: slt  x5, x1, x2         (0x0020A2B3 -> x5 = 1, signed -5 < 12)
    // 0x14: sltu x6, x1, x2         (0x0020B333 -> x6 = 0, unsigned 0xFFF..FB > 12)
    // 0x18: srai x7, x4, 2          (0x40225393 -> x7 = -15 = 0xFFFFFFFFFFFFFFF1)
    // 0x1C: addi x8, x0, 32         (0x02000413 -> x8 = 32)
    // 0x20: sw   x4, -8(x8)         (0xFE442C23 -> dmem[24] = -60, negative S-type imm_s = -8)
    // 0x24: lw   x9, -8(x8)         (0xFF842483 -> x9 = -60, negative I-type imm_i = -8)
    // 0x28: addi x10, x0, 3         (0x00300513 -> x10 = 3 loop counter)
    // 0x2C: addi x10, x10, -1       (0xFFF50513 -> loop body: x10--)
    // 0x30: bne  x10, x0, -4        (0xFE051EE3 -> backward B-type branch to 0x2C!)
    // 0x34: ecall                   (0x00000073 -> Trap #1: mepc=0x38, jump to 0x50)
    // 0x38: ecall                   (0x00000073 -> Trap #2: mepc=0x3C, jump to 0x50)
    // 0x3C: addi x12, x11, 100      (0x06458613 -> x12 = 2 + 100 = 102 after 2 traps)
    // 0x50: addi x11, x11, 1        (0x00158593 -> MTVEC handler increments trap counter x11)
    // 0x54: mret                    (0x30200073 -> return to mepc)
    imem[0]  = 0xFFB00093ULL;
    imem[1]  = 0x00C00113ULL;
    imem[2]  = 0x402081B3ULL;
    imem[3]  = 0x02208233ULL;
    imem[4]  = 0x0020A2B3ULL;
    imem[5]  = 0x0020B333ULL;
    imem[6]  = 0x40225393ULL;
    imem[7]  = 0x02000413ULL;
    imem[8]  = 0xFE442C23ULL;
    imem[9]  = 0xFF842483ULL;
    imem[10] = 0x00300513ULL;
    imem[11] = 0xFFF50513ULL;
    imem[12] = 0xFE051EE3ULL;
    imem[13] = 0x00000073ULL;
    imem[14] = 0x00000073ULL;
    imem[15] = 0x06458613ULL;
    imem[20] = 0x00158593ULL;
    imem[21] = 0x30200073ULL;
    // Control flow and the upper register file (fixed 2026-11-04: JAL target, BLTU/BGEU, x16..x31):
    // 0x40: jal  x16, +0x20         (0x0200086F -> pc = 0x60, x16 = 0x44)
    // 0x44: addi x17, x0, 7         (0x00700893 -> reached only through the JALR return)
    // 0x48: jal  x0, 0              (0x0000006F -> self-loop; pc parks at 0x48)
    // 0x60: addi x31, x0, -1        (0xFFF00F93 -> x31 = all ones)
    // 0x64: bltu x16, x31, +8       (0x01F86463 -> 0x44 <u 2^64-1: taken, skips 0x68)
    // 0x68: addi x18, x0, 99        (0x06300913 -> skipped, x18 stays 0)
    // 0x6C: bgeu x16, x31, +8       (0x01F87463 -> not taken)
    // 0x70: addi x19, x0, 5         (0x00500993 -> x19 = 5)
    // 0x74: blt  x31, x16, +8       (0x010FC463 -> -1 <s 0x44: taken, skips 0x78)
    // 0x78: addi x20, x0, 77        (0x04D00A13 -> skipped, x20 stays 0)
    // 0x7C: bge  x31, x16, +8       (0x010FD463 -> not taken)
    // 0x80: add  x21, x31, x16      (0x010F8AB3 -> x21 = 0x43)
    // 0x84: jalr x22, 0(x16)        (0x00080B67 -> pc = 0x44, x22 = 0x88)
    imem[16] = 0x0200086FULL;
    imem[17] = 0x00700893ULL;
    imem[18] = 0x0000006FULL;
    imem[24] = 0xFFF00F93ULL;
    imem[25] = 0x01F86463ULL;
    imem[26] = 0x06300913ULL;
    imem[27] = 0x01F87463ULL;
    imem[28] = 0x00500993ULL;
    imem[29] = 0x010FC463ULL;
    imem[30] = 0x04D00A13ULL;
    imem[31] = 0x010FD463ULL;
    imem[32] = 0x010F8AB3ULL;
    imem[33] = 0x00080B67ULL;

    top->rst = 1;
    tick();
    tick();
    top->rst = 0;

    // 11 setup + 6 loop (3x (addi -1 + bne)) + 2*(ecall + handler addi + mret) + 1 final addi = 24 cycles,
    // then 11 more for the control-flow block (jal, 8 at 0x60.., jalr, the addi at 0x44, the self-loop);
    // 40 cycles leaves the pc parked at 0x48.
    for (int cycle = 0; cycle < 40; ++cycle) {
        tick();
    }

    const uint64_t neg5  = 0xFFFFFFFFFFFFFFFBULL;
    const uint64_t neg17 = 0xFFFFFFFFFFFFFFEFULL;
    const uint64_t neg60 = 0xFFFFFFFFFFFFFFC4ULL;
    const uint64_t neg15 = 0xFFFFFFFFFFFFFFF1ULL;

    if (top->x1_out != neg5 || top->x2_out != 12ULL || top->x3_out != neg17 ||
        top->x4_out != neg60 || top->x5_out != 1ULL || top->x6_out != 0ULL ||
        top->x7_out != neg15 || dmem[24] != neg60 || top->x9_out != neg60 ||
        top->x10_out != 0ULL || top->x11_out != 2ULL || top->x12_out != 102ULL ||
        top->mepc_out != 0x3CULL ||
        top->x16_out != 0x44ULL || top->x17_out != 7ULL || top->x18_out != 0ULL || top->x19_out != 5ULL ||
        top->x20_out != 0ULL || top->x21_out != 0x43ULL || top->x22_out != 0x88ULL ||
        top->x31_out != 0xFFFFFFFFFFFFFFFFULL || top->pc_out != 0x48ULL) {
        std::cerr << "[FAIL] Phase B ISA torture mismatch:"
                  << " x1=0x" << std::hex << top->x1_out
                  << " x3=0x" << top->x3_out
                  << " x4=0x" << top->x4_out
                  << " x5=" << std::dec << top->x5_out
                  << " x6=" << top->x6_out
                  << " x7=0x" << std::hex << top->x7_out
                  << " dmem[24]=0x" << dmem[24]
                  << " x9=0x" << top->x9_out
                  << " x10=" << std::dec << top->x10_out
                  << " x11=" << top->x11_out
                  << " x12=" << top->x12_out
                  << " mepc=0x" << std::hex << top->mepc_out
                  << " x16=0x" << top->x16_out << " x17=" << std::dec << top->x17_out
                  << " x18=" << top->x18_out << " x19=" << top->x19_out << " x20=" << top->x20_out
                  << " x21=0x" << std::hex << top->x21_out << " x22=0x" << top->x22_out
                  << " x31=0x" << top->x31_out << " pc=0x" << top->pc_out << std::dec << std::endl;
        return 1;
    }
    std::cout << "[PASS] Phase B (ISA Torture): neg ADDI/SUB/MUL/SLT/SLTU/SRAI, neg S-type SW/LW, "
              << "backward BNE loop, back-to-back ECALL/MRET, JAL/JALR, BLTU/BGEU/BLT/BGE and x16..x31 verified!" << std::endl;

    tfp->close();
    delete tfp;
    delete top;
    return 0;
}
