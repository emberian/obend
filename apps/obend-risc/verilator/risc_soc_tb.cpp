#include "Vobend_risc_cpu.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <cstdint>
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

    std::vector<uint64_t> imem(64, 0ULL);
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

        // Re-evaluate combinational outputs before posedge
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

    // Apply synchronous reset for 2 cycles
    top->rst = 1;
    top->imem_rdata = 0;
    top->dmem_rdata = 0;
    tick();
    tick();
    top->rst = 0;

    bool saw_trap_entry = false;
    bool saw_mret_restore = false;

    // Execute 18 architectural retirement cycles
    for (int cycle = 0; cycle < 18; ++cycle) {
        uint64_t cur_pc = top->pc_out;
        uint64_t cur_inst = imem[(cur_pc >> 2) & 63ULL];
        tick();

        std::printf(
            "[Cycle %2d] PC=0x%02llx INST=0x%08llx -> nextPC=0x%02llx mstatus=%llu mepc=0x%02llx mcause=%llu x8=%llu x10=%llu x14=%llu x15=%llu\n",
            cycle,
            (unsigned long long)cur_pc,
            (unsigned long long)cur_inst,
            (unsigned long long)top->pc_out,
            (unsigned long long)top->mstatus_out,
            (unsigned long long)top->mepc_out,
            (unsigned long long)top->mcause_out,
            (unsigned long long)top->x8_out,
            (unsigned long long)top->x10_out,
            (unsigned long long)top->x14_out,
            (unsigned long long)top->x15_out);

        if (cycle == 8) {
            // Cycle 8 retired ECALL at PC=0x20: verify trap entry to MTVEC=0x40
            if (top->pc_out == 0x40ULL && top->mepc_out == 0x24ULL &&
                top->mcause_out == 11ULL && top->mstatus_out == 24ULL && top->x9_out == 0x24ULL) {
                saw_trap_entry = true;
            }
        }
        if (cycle == 10) {
            // Cycle 10 retired MRET at PC=0x44: verify return to MEPC=0x24 and mstatus=8
            if (top->pc_out == 0x24ULL && top->mstatus_out == 8ULL && top->x10_out == 42ULL) {
                saw_mret_restore = true;
            }
        }
    }

    tfp->close();

    // Verify 8-element Fibonacci sequence in x1..x8
    const uint64_t expected_fib[8] = {1, 1, 2, 3, 5, 8, 13, 21};
    const uint64_t actual_fib[8] = {
        top->x1_out, top->x2_out, top->x3_out, top->x4_out,
        top->x5_out, top->x6_out, top->x7_out, top->x8_out
    };
    for (int i = 0; i < 8; ++i) {
        if (actual_fib[i] != expected_fib[i]) {
            std::cerr << "[FAIL] Fibonacci mismatch at x" << (i + 1)
                      << ": expected " << expected_fib[i] << ", got " << actual_fib[i] << std::endl;
            return 1;
        }
    }

    if (!saw_trap_entry || !saw_mret_restore) {
        std::cerr << "[FAIL] CSR trap/mret verification failed (saw_trap="
                  << saw_trap_entry << ", saw_mret=" << saw_mret_restore << ")" << std::endl;
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

    // Verify final checksum in x15 and dmem[0]
    if (top->x15_out != 1345ULL || dmem[0] != 1345ULL) {
        std::cerr << "[FAIL] Final checksum mismatch: x15=" << top->x15_out
                  << " dmem[0]=" << dmem[0] << " (expected 1345)" << std::endl;
        return 1;
    }

    std::cout << "[PASS] ObendRisc 3-layer sequential CPU verified: "
              << "Fib8=21, CSR Trap/MRET x10=42, CustomSimdZkExt MAC4=1282, dmem[0]=1345" << std::endl;

    delete tfp;
    delete top;
    return 0;
}
