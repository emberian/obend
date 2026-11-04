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
    // 0. Adversarial Goldilocks Boundary & Non-Canonical Input Torture Suite
    //    (Covers Z3-found boundary cases: non-canonical inputs >= P, UINT64_MAX,
    //     P - 1, 0 - (P - 1), and 128-bit hi_hi32 borrow edge cases)
    // =========================================================================
    struct BoundaryVec {
        uint64_t u;
        uint64_t v;
        uint64_t w;
    };
    const BoundaryVec boundary_vecs[] = {
        {0xFFFFFFFF00000003ULL, 2ULL, 1ULL},                           // u >= P (u - vw == P if uncanonicalized!)
        {0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL}, // all UINT64_MAX (2^64 - 1)
        {GOLDILOCKS_P - 1ULL,   GOLDILOCKS_P - 1ULL,   GOLDILOCKS_P - 1ULL},   // all P - 1
        {GOLDILOCKS_P,          GOLDILOCKS_P,          GOLDILOCKS_P},          // exact P
        {0ULL,                  GOLDILOCKS_P - 1ULL,   1ULL},                  // underflow borrow 0 - (P - 1) == 1
        {1ULL,                  0xFFFFFFFF00000000ULL, 0xFFFFFFFF00000000ULL}, // (P-1)^2 == 1 -> even=2, odd=0
        {GOLDILOCKS_P - 2ULL,   0xFFFFFFFFULL,         0x100000001ULL},        // 2^64 - 1 == P - 1 + 2^32 - 1
        {0x00000000FFFFFFFFULL, 0xFFFFFFFF00000005ULL, 0xFFFFFFFF00000007ULL}  // non-canonical v, w > P
    };
    for (size_t k = 0; k < sizeof(boundary_vecs) / sizeof(boundary_vecs[0]); ++k) {
        top->u_in = boundary_vecs[k].u;
        top->v_in = boundary_vecs[k].v;
        top->w_in = boundary_vecs[k].w;
        top->eval();

        uint64_t ref_vw   = mul_mod(boundary_vecs[k].v, boundary_vecs[k].w);
        uint64_t ref_even = add_mod(boundary_vecs[k].u, ref_vw);
        uint64_t ref_odd  = sub_mod(boundary_vecs[k].u, ref_vw);
        if (top->goldilocks_even_out >= GOLDILOCKS_P ||
            top->goldilocks_odd_out >= GOLDILOCKS_P ||
            top->goldilocks_even_out != ref_even ||
            top->goldilocks_odd_out != ref_odd) {
            std::cerr << "[FAIL] Adversarial Goldilocks boundary mismatch at case " << k
                      << ": got even=0x" << std::hex << top->goldilocks_even_out
                      << " (ref=0x" << ref_even << "), odd=0x" << top->goldilocks_odd_out
                      << " (ref=0x" << ref_odd << ")" << std::dec << std::endl;
            return 1;
        }
    }
    std::cout << "[PASS] Adversarial 64/128-bit Goldilocks boundary torture vectors verified ("
              << (sizeof(boundary_vecs) / sizeof(boundary_vecs[0])) << "/8)" << std::endl;

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
        orig[i] = add_mod(GOLDILOCKS_P - 1ULL - (i * 13ULL),
                          mul_mod(i + 1ULL, 0x9E3779B97F4A7C15ULL));
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
    // 2. Verify Streaming 4-Stage resetFree Pipelined RTL vs 64-Bit AMD VOP64 GPU Assembly
    //    (Includes both the canonical concrete vector (50,6,7,3,29) AND full 64-bit streaming vectors!)
    // =========================================================================
    std::vector<uint64_t> u_stream(64), v_stream(64), w_stream(64), r_stream(64), b_stream(64);
    u_stream[0] = 50ULL; v_stream[0] = 6ULL; w_stream[0] = 7ULL; r_stream[0] = 3ULL; b_stream[0] = 29ULL;
    for (size_t t = 1; t < 64; ++t) {
        u_stream[t] = 0x9E3779B97F4A7C15ULL * (t + 1ULL) + 50ULL;
        v_stream[t] = 0xBF58476D1CE4E5B9ULL * (t + 3ULL) + 6ULL;
        w_stream[t] = 0x94D049BB133111EBULL * (t + 5ULL) + 7ULL;
        r_stream[t] = 0xD6E8FEB86659FD93ULL * (t + 7ULL) + 3ULL;
        b_stream[t] = 0xA24BAED4963EE407ULL * (t + 11ULL) + 29ULL;
    }

    // Stream 64 vectors at 1 vector / clock cycle (II = 1) with 4-cycle pipeline latency!
    for (size_t cyc = 0; cyc < 64 + 3; ++cyc) {
        size_t in_idx = (cyc < 64) ? cyc : 63;
        top->u_in    = u_stream[in_idx];
        top->v_in    = v_stream[in_idx];
        top->w_in    = w_stream[in_idx];
        top->r_in    = r_stream[in_idx];
        top->bias_in = b_stream[in_idx];
        tick();

        if (cyc >= 3) {
            size_t out_idx = cyc - 3;
            uint64_t vop64_out = emulate_amd_vop64_butterfly_fold(
                u_stream[out_idx], v_stream[out_idx], w_stream[out_idx], r_stream[out_idx]);
            uint64_t exp_even = u_stream[out_idx] + (v_stream[out_idx] * w_stream[out_idx]);
            uint64_t exp_odd  = u_stream[out_idx] - (v_stream[out_idx] * w_stream[out_idx]);
            uint64_t exp_acc  = (exp_odd - exp_even) + (b_stream[out_idx] * r_stream[out_idx]);
            if (top->pipe4_folded_out != vop64_out ||
                top->pipe4_even_out != exp_even ||
                top->pipe4_odd_out != exp_odd ||
                top->pipe4_acc_out != exp_acc) {
                std::cerr << "[FAIL] Streaming II=1 4-stage resetFree RTL vs AMD VOP64 mismatch at vector "
                          << out_idx << ": RTL=0x" << std::hex << top->pipe4_folded_out
                          << " VOP64=0x" << vop64_out << std::dec << std::endl;
                return 1;
            }
        }
    }
    std::cout << "[PASS] Streaming II=1 4-stage resetFree pipelined RTL matches 64-bit AMD VOP64 assembly across 64 full-width vectors" << std::endl;

    // =========================================================================
    // 3. Verify 8-Round Multilinear Sumcheck Protocol on Stateful always_ff RTL
    //    with Full-Width Elements Near P - 1 (Exercising 65-Bit Carries & Borrows Every Cycle)
    // =========================================================================
    std::vector<uint64_t> table(256);
    uint64_t claimed_sum = 0ULL;
    for (size_t i = 0; i < 256; ++i) {
        // Full 64-bit Goldilocks field elements > 2^63 so every round wraps mod P multiple times
        table[i]    = sub_mod(GOLDILOCKS_P - 17ULL,
                              mul_mod(i + 1ULL, 0x7FEDBCA987654321ULL));
        claimed_sum = add_mod(claimed_sum, table[i]);
    }

    for (int round = 0; round < 8; ++round) {
        size_t half = table.size() >> 1;
        uint64_t r_challenge = sub_mod(GOLDILOCKS_P - 29ULL,
                                       mul_mod(static_cast<uint64_t>(round + 1), 0x13579BDF2468ACE1ULL));

        // Clear stateful round accumulator
        top->sc_clear  = 1;
        top->sc_enable = 0;
        tick();
        top->sc_clear  = 0;

        uint64_t ref_g2 = 0ULL;
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
            ref_g2 = add_mod(ref_g2, sub_mod(add_mod(f1, f1), f0));
            if (next_table[j] != ref_fold) {
                std::cerr << "[FAIL] Sumcheck fold mismatch at round " << round << " pair " << j << std::endl;
                return 1;
            }
        }
        top->sc_enable = 0;

        uint64_t g0 = top->sc_g0_out;
        uint64_t g1 = top->sc_g1_out;
        uint64_t g2 = top->sc_g2_out;
        uint64_t round_claim = top->sc_round_claim_out;

        if (round_claim != claimed_sum || g2 != ref_g2 ||
            sub_mod(g1, g0) != sub_mod(g2, g1)) {
            std::cerr << "[FAIL] Sumcheck round " << round << " consistency/extrapolation check failed: "
                      << "g(0)+g(1)=" << round_claim << " claimed_sum=" << claimed_sum
                      << " g(2)=" << g2 << " ref_g2=" << ref_g2 << std::endl;
            return 1;
        }

        // Verifier updates claim to g_k(r_k) = g(0) + r_k * (g(1) - g(0)) mod P
        claimed_sum = add_mod(g0, mul_mod(r_challenge, sub_mod(g1, g0)));
        table = next_table;

        std::printf("[Sumcheck Round %d] pairs=%3zu g(0)=0x%016llx g(1)=0x%016llx g(2)=0x%016llx claim_ok=1 next_claim=0x%016llx\n",
                    round, half,
                    (unsigned long long)g0,
                    (unsigned long long)g1,
                    (unsigned long long)g2,
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
