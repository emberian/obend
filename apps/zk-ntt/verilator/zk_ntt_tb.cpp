#include "Vzk_ntt_coproc.h"
#include "goldilocks_ref.hpp"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <vector>

using namespace goldilocks_ref;

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::randReset(2);
    Verilated::traceEverOn(true);

    const char* vcd_path = (argc > 1) ? argv[1] : "zk_ntt_trace.vcd";

    Vzk_ntt_coproc* top = new Vzk_ntt_coproc;
    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open(vcd_path);

    vluint64_t sim_time = 0;
    auto tick = [&]() {
        top->clk = 0;
        top->eval();
        tfp->dump(sim_time++);
        top->clk = 1;
        top->eval();
        tfp->dump(sim_time++);
    };

    // Reset stateful Sumcheck accumulator & flush 4-stage resetFree pipeline
    top->rst       = 1;
    top->u_in      = 0;
    top->v_in      = 0;
    top->w_in      = 0;
    top->r_in      = 0;
    top->bias_in   = 0;
    top->sc_clear  = 0;
    top->sc_enable = 0;
    top->sc_f0_in  = 0;
    top->sc_f1_in  = 0;
    top->sc_r_in   = 0;
    for (int i = 0; i < 4; ++i) tick();
    top->rst = 0;

    // =========================================================================
    // 1. Verify 256-Point Goldilocks NTT & INTT (INTT(NTT(x)) == x) on Hardware
    // =========================================================================
    const uint64_t omega_256 = primitive_root_256();
    const uint64_t omega_inv = inv_mod(omega_256);
    const uint64_t n_inv     = inv_mod(256ULL);

    // Verify primitive 256-th root properties
    if (pow_mod(omega_256, 128ULL) != GOLDILOCKS_P - 1ULL ||
        pow_mod(omega_256, 256ULL) != 1ULL) {
        std::cerr << "[FAIL] Invalid 256-th root of unity in Goldilocks field" << std::endl;
        return 1;
    }

    std::vector<uint64_t> orig(256);
    for (size_t i = 0; i < 256; ++i) {
        orig[i] = ((i + 1ULL) * 0x0123456789ABCDEFULL + 17ULL) % GOLDILOCKS_P;
    }

    auto run_hw_ntt_256 = [&](const std::vector<uint64_t>& input, uint64_t root) {
        std::vector<uint64_t> a(256);
        for (size_t i = 0; i < 256; ++i) {
            a[bit_reverse_8(i)] = input[i];
        }
        for (size_t len = 2; len <= 256; len <<= 1) {
            size_t half = len >> 1;
            uint64_t w_step = pow_mod(root, 256ULL / len);
            for (size_t i = 0; i < 256; i += len) {
                uint64_t w = 1ULL;
                for (size_t j = 0; j < half; ++j) {
                    top->u_in    = a[i + j];
                    top->v_in    = a[i + j + half];
                    top->w_in    = w;
                    top->r_in    = (j + 1ULL);
                    top->bias_in = (i + 1ULL);
                    top->eval();

                    uint64_t hw_even = top->goldilocks_even_out;
                    uint64_t hw_odd  = top->goldilocks_odd_out;

                    // Cross-check every single butterfly against __uint128_t Goldilocks reference
                    uint64_t ref_vw   = mul_mod(a[i + j + half], w);
                    uint64_t ref_even = add_mod(a[i + j], ref_vw);
                    uint64_t ref_odd  = sub_mod(a[i + j], ref_vw);
                    if (hw_even != ref_even || hw_odd != ref_odd) {
                        std::cerr << "[FAIL] Goldilocks butterfly mismatch at len=" << len
                                  << " i=" << i << " j=" << j << std::endl;
                        std::exit(1);
                    }

                    a[i + j]        = hw_even;
                    a[i + j + half] = hw_odd;
                    w = mul_mod(w, w_step);
                }
            }
        }
        return a;
    };

    std::vector<uint64_t> ntt_hw  = run_hw_ntt_256(orig, omega_256);
    std::vector<uint64_t> ntt_ref = ntt_256_ref(orig, omega_256);
    for (size_t i = 0; i < 256; ++i) {
        if (ntt_hw[i] != ntt_ref[i]) {
            std::cerr << "[FAIL] Forward 256-point NTT mismatch at index " << i << std::endl;
            return 1;
        }
    }

    std::vector<uint64_t> intt_unscaled = run_hw_ntt_256(ntt_hw, omega_inv);
    for (size_t i = 0; i < 256; ++i) {
        // Use hardware butterfly multiplier (u=0, v=intt_unscaled[i], w=n_inv) to scale by 256^-1 mod P
        top->u_in = 0ULL;
        top->v_in = intt_unscaled[i];
        top->w_in = n_inv;
        top->eval();
        uint64_t recovered = top->goldilocks_even_out;
        if (recovered != orig[i]) {
            std::cerr << "[FAIL] INTT(NTT(x)) != x at index " << i
                      << ": expected " << orig[i] << ", got " << recovered << std::endl;
            return 1;
        }
    }
    std::cout << "[PASS] 256-point Goldilocks NTT & INTT verified (2048 butterflies, 0 bit mismatches)" << std::endl;

    // =========================================================================
    // 2. Verify 4-Stage resetFree Pipelined RTL vs 64-Bit AMD VOP64 GPU Assembly
    // =========================================================================
    for (uint64_t t = 0; t < 64; ++t) {
        uint64_t u    = 50ULL + t * 13ULL;
        uint64_t v    = 6ULL  + t * 7ULL;
        uint64_t w    = 7ULL  + t * 3ULL;
        uint64_t r    = 3ULL  + (t & 7ULL);
        uint64_t bias = 29ULL + t;

        top->u_in    = u;
        top->v_in    = v;
        top->w_in    = w;
        top->r_in    = r;
        top->bias_in = bias;
        // Clock 4 cycles through the 4-stage resetFree pipeline
        for (int s = 0; s < 4; ++s) tick();

        uint64_t vop64_out = emulate_amd_vop64_butterfly_fold(u, v, w, r);
        if (top->pipe4_folded_out != vop64_out) {
            std::cerr << "[FAIL] 4-stage resetFree RTL vs AMD VOP64 mismatch at vector " << t
                      << ": RTL=" << top->pipe4_folded_out << " VOP64=" << vop64_out << std::endl;
            return 1;
        }
    }
    std::cout << "[PASS] 4-stage resetFree pipelined RTL matches 64-bit AMD VOP64 assembly across 64 vectors" << std::endl;

    // =========================================================================
    // 3. Verify 8-Round Multilinear Sumcheck Protocol on Stateful always_ff RTL
    // =========================================================================
    std::vector<uint64_t> table(256);
    uint64_t claimed_sum = 0ULL;
    for (size_t i = 0; i < 256; ++i) {
        table[i]    = ((i * 37ULL + 101ULL) * (i + 5ULL)) % GOLDILOCKS_P;
        claimed_sum = add_mod(claimed_sum, table[i]);
    }

    for (int round = 0; round < 8; ++round) {
        size_t half = table.size() >> 1;
        uint64_t r_challenge = (round * 19ULL + 7ULL) % GOLDILOCKS_P;

        // Clear stateful round accumulator
        top->sc_clear  = 1;
        top->sc_enable = 0;
        tick();
        top->sc_clear  = 0;

        std::vector<uint64_t> next_table(half);
        for (size_t j = 0; j < half; ++j) {
            uint64_t f0 = table[2 * j];
            uint64_t f1 = table[2 * j + 1];

            top->sc_enable = 1;
            top->sc_f0_in  = f0;
            top->sc_f1_in  = f1;
            top->sc_r_in   = r_challenge;
            tick();

            next_table[j] = top->sc_folded_out;
            uint64_t ref_fold = add_mod(f0, mul_mod(r_challenge, sub_mod(f1, f0)));
            if (next_table[j] != ref_fold) {
                std::cerr << "[FAIL] Sumcheck fold mismatch at round " << round << " pair " << j << std::endl;
                return 1;
            }
        }
        top->sc_enable = 0;

        uint64_t g0 = top->sc_g0_out;
        uint64_t g1 = top->sc_g1_out;
        uint64_t round_claim = top->sc_round_claim_out;

        if (round_claim != claimed_sum) {
            std::cerr << "[FAIL] Sumcheck round " << round << " consistency check failed: "
                      << "g(0)+g(1)=" << round_claim << " != claimed_sum=" << claimed_sum << std::endl;
            return 1;
        }

        // Verifier updates claim to g_k(r_k) = g(0) + r_k * (g(1) - g(0)) mod P
        claimed_sum = add_mod(g0, mul_mod(r_challenge, sub_mod(g1, g0)));
        table = next_table;

        std::printf("[Sumcheck Round %d] pairs=%3zu g(0)=0x%016llx g(1)=0x%016llx claim_ok=1 next_claim=0x%016llx\n",
                    round, half,
                    (unsigned long long)g0,
                    (unsigned long long)g1,
                    (unsigned long long)claimed_sum);
    }

    if (table.size() != 1 || table[0] != claimed_sum) {
        std::cerr << "[FAIL] Final Sumcheck oracle check failed: table[0]=" << table[0]
                  << " != claimed_sum=" << claimed_sum << std::endl;
        return 1;
    }
    std::cout << "[PASS] 8-round multilinear Sumcheck protocol verified (final oracle value = 0x"
              << std::hex << table[0] << std::dec << ")" << std::endl;

    tfp->close();
    delete tfp;
    delete top;
    return 0;
}
