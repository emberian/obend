// apps/zk-ntt/verilator/zk_ntt_tb.cpp
//
// Verilator harness for `zk_ntt_coproc`, emitted by `obend-emit-sv zk` from
// Obend.Apps.ZkNtt.zkNttCoprocRtlModule. Three checks:
//   0. the butterfly on the carry/borrow corners against the __uint128_t reference (goldilocks_ref.hpp);
//   1. a 256-point NTT and its inverse, every butterfly through the hardware and cross-checked;
//   2. the 8-round multilinear sumcheck: the hardware accumulates g(0), g(1), g(2) over each pair,
//      absorbs them into its transcript register, and folds with the challenge it derived. The
//      harness keeps its own transcript (transcript_absorb) and the verifier's claim, checks the
//      hardware challenge equals its own, and checks every round against the Lean golden
//      (`obend-emit-sv golden-zk`, argv[2]) that ran the same protocol on the Nat model.
// No challenge is supplied from outside: the only inputs are the pairs and three strobes.

#include "Vzk_ntt_coproc.h"
#include "goldilocks_ref.hpp"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>

using namespace goldilocks_ref;

namespace {
std::map<std::string, uint64_t> readGolden(const char* path) {
    std::ifstream in(path);
    if (!in.is_open()) {
        std::cerr << "[FAIL] cannot open Lean golden " << path << " (run obend-emit-sv golden-zk)" << std::endl;
        std::exit(1);
    }
    std::map<std::string, uint64_t> g;
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        size_t eq = line.find('=');
        if (eq == std::string::npos) continue;
        g[line.substr(0, eq)] = std::stoull(line.substr(eq + 1));
    }
    return g;
}
uint64_t need(const std::map<std::string, uint64_t>& g, const std::string& k) {
    auto it = g.find(k);
    if (it == g.end()) { std::cerr << "[FAIL] golden lacks " << k << std::endl; std::exit(1); }
    return it->second;
}
}  // namespace

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::randReset(2);
    Verilated::traceEverOn(true);

    const char* vcd_path = (argc > 1) ? argv[1] : "zk_ntt_trace.vcd";
    const char* golden_path = (argc > 2) ? argv[2] : "zk_ntt_golden.txt";
    auto golden = readGolden(golden_path);

    Vzk_ntt_coproc* top = new Vzk_ntt_coproc;
    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open(vcd_path);

    vluint64_t sim_time = 0;
    auto tick = [&]() {
        top->clk = 0;
        top->eval();
        if (sim_time < 8192) tfp->dump(sim_time);
        sim_time++;
        top->clk = 1;
        top->eval();
        if (sim_time < 8192) tfp->dump(sim_time);
        sim_time++;
    };

    top->rst = 1;
    top->u_in = 0; top->v_in = 0; top->w_in = 0;
    top->sc_clear = 0; top->sc_enable = 0; top->sc_absorb = 0;
    top->sc_f0_in = 0; top->sc_f1_in = 0;
    tick();
    tick();
    top->rst = 0;
    top->eval();
    if (top->sc_transcript_out != TRANSCRIPT_IV || top->sc_transcript_out != need(golden, "iv")) {
        std::cerr << "[FAIL] transcript reset value: hw=0x" << std::hex << top->sc_transcript_out << std::dec << std::endl;
        return 1;
    }

    // 0. Boundary vectors: non-canonical inputs, 2^64 - 1, p - 1, (p-1)^2 = 1, borrows.
    struct BoundaryVec { uint64_t u, v, w; };
    const BoundaryVec boundary_vecs[] = {
        {0xFFFFFFFF00000003ULL, 2ULL, 1ULL},
        {0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL},
        {GOLDILOCKS_P - 1ULL, GOLDILOCKS_P - 1ULL, GOLDILOCKS_P - 1ULL},
        {GOLDILOCKS_P, GOLDILOCKS_P, GOLDILOCKS_P},
        {0ULL, GOLDILOCKS_P - 1ULL, 1ULL},
        {1ULL, 0xFFFFFFFF00000000ULL, 0xFFFFFFFF00000000ULL},
        {GOLDILOCKS_P - 2ULL, 0xFFFFFFFFULL, 0x100000001ULL},
        {0x00000000FFFFFFFFULL, 0xFFFFFFFF00000005ULL, 0xFFFFFFFF00000007ULL}
    };
    for (size_t k = 0; k < sizeof(boundary_vecs) / sizeof(boundary_vecs[0]); ++k) {
        top->u_in = boundary_vecs[k].u;
        top->v_in = boundary_vecs[k].v;
        top->w_in = boundary_vecs[k].w;
        top->eval();
        uint64_t ref_vw = mul_mod(boundary_vecs[k].v, boundary_vecs[k].w);
        uint64_t ref_even = add_mod(boundary_vecs[k].u, ref_vw);
        uint64_t ref_odd = sub_mod(boundary_vecs[k].u, ref_vw);
        if (top->goldilocks_even_out >= GOLDILOCKS_P || top->goldilocks_odd_out >= GOLDILOCKS_P ||
            top->goldilocks_even_out != ref_even || top->goldilocks_odd_out != ref_odd) {
            std::cerr << "[FAIL] boundary case " << k << ": even=0x" << std::hex << top->goldilocks_even_out
                      << " (ref 0x" << ref_even << ") odd=0x" << top->goldilocks_odd_out
                      << " (ref 0x" << ref_odd << ")" << std::dec << std::endl;
            return 1;
        }
    }
    std::cout << "[PASS] 8 boundary vectors" << std::endl;

    // 1. 256-point NTT and INTT, every butterfly on the hardware.
    const uint64_t omega_256 = primitive_root_256();
    const uint64_t omega_inv = inv_mod(omega_256);
    const uint64_t n_inv = inv_mod(256ULL);
    if (pow_mod(omega_256, 128ULL) != GOLDILOCKS_P - 1ULL || pow_mod(omega_256, 256ULL) != 1ULL) {
        std::cerr << "[FAIL] not a primitive 256-th root" << std::endl;
        return 1;
    }
    std::vector<uint64_t> orig(256);
    for (size_t i = 0; i < 256; ++i)
        orig[i] = add_mod(GOLDILOCKS_P - 1ULL - (i * 13ULL), mul_mod(i + 1ULL, 0x9E3779B97F4A7C15ULL));

    uint64_t butterflies = 0;
    auto run_hw_ntt_256 = [&](const std::vector<uint64_t>& input, uint64_t root) {
        std::vector<uint64_t> a(256);
        for (size_t i = 0; i < 256; ++i) a[bit_reverse_8(i)] = input[i];
        for (size_t len = 2; len <= 256; len <<= 1) {
            size_t half = len >> 1;
            uint64_t w_step = pow_mod(root, 256ULL / len);
            for (size_t i = 0; i < 256; i += len) {
                uint64_t w = 1ULL;
                for (size_t j = 0; j < half; ++j) {
                    top->u_in = a[i + j];
                    top->v_in = a[i + j + half];
                    top->w_in = w;
                    top->eval();
                    uint64_t hw_even = top->goldilocks_even_out;
                    uint64_t hw_odd = top->goldilocks_odd_out;
                    uint64_t ref_vw = mul_mod(a[i + j + half], w);
                    if (hw_even != add_mod(a[i + j], ref_vw) || hw_odd != sub_mod(a[i + j], ref_vw)) {
                        std::cerr << "[FAIL] butterfly mismatch len=" << len << " i=" << i << " j=" << j << std::endl;
                        std::exit(1);
                    }
                    a[i + j] = hw_even;
                    a[i + j + half] = hw_odd;
                    w = mul_mod(w, w_step);
                    butterflies++;
                }
            }
        }
        return a;
    };
    std::vector<uint64_t> ntt_hw = run_hw_ntt_256(orig, omega_256);
    std::vector<uint64_t> ntt_ref = ntt_256_ref(orig, omega_256);
    for (size_t i = 0; i < 256; ++i)
        if (ntt_hw[i] != ntt_ref[i]) { std::cerr << "[FAIL] NTT index " << i << std::endl; return 1; }
    std::vector<uint64_t> intt_unscaled = run_hw_ntt_256(ntt_hw, omega_inv);
    for (size_t i = 0; i < 256; ++i) {
        top->u_in = 0ULL; top->v_in = intt_unscaled[i]; top->w_in = n_inv;
        top->eval();
        if (top->goldilocks_even_out != orig[i]) { std::cerr << "[FAIL] INTT(NTT(x)) index " << i << std::endl; return 1; }
    }
    std::cout << "[PASS] 256-point NTT and INTT (" << butterflies << " butterflies)" << std::endl;

    // 2. 8-round sumcheck with the hardware transcript.
    std::vector<uint64_t> table(256);
    uint64_t claimed = 0ULL;
    for (size_t i = 0; i < 256; ++i) {
        table[i] = sub_mod(GOLDILOCKS_P - 17ULL, mul_mod(i + 1ULL, 0x7FEDBCA987654321ULL));
        claimed = add_mod(claimed, table[i]);
    }
    if (claimed != need(golden, "claim0")) { std::cerr << "[FAIL] claim0 differs from the Lean golden" << std::endl; return 1; }
    uint64_t transcript = TRANSCRIPT_IV;
    uint64_t pair_ticks = 0;
    for (int round = 0; round < 8; ++round) {
        size_t half = table.size() >> 1;
        top->sc_clear = 1; top->sc_enable = 0; top->sc_absorb = 0;
        tick();
        top->sc_clear = 0;
        uint64_t ref_g0 = 0, ref_g1 = 0, ref_g2 = 0;
        for (size_t j = 0; j < half; ++j) {
            uint64_t f0 = table[2 * j], f1 = table[2 * j + 1];
            top->sc_enable = 1; top->sc_f0_in = f0; top->sc_f1_in = f1;
            tick();
            pair_ticks++;
            ref_g0 = add_mod(ref_g0, f0);
            ref_g1 = add_mod(ref_g1, f1);
            ref_g2 = add_mod(ref_g2, sub_mod(add_mod(f1, f1), f0));
        }
        top->sc_enable = 0;
        top->eval();
        if (top->sc_pair_cnt_out != half) { std::cerr << "[FAIL] pair count round " << round << std::endl; return 1; }
        uint64_t g0 = top->sc_g0_out, g1 = top->sc_g1_out, g2 = top->sc_g2_out;
        uint64_t round_claim = top->sc_round_claim_out;
        if (g0 != ref_g0 || g1 != ref_g1 || g2 != ref_g2) {
            std::cerr << "[FAIL] accumulators round " << round << std::endl; return 1;
        }
        // prover's messages go into the transcript; the challenge comes out of it
        top->sc_absorb = 1;
        tick();
        top->sc_absorb = 0;
        top->eval();
        transcript = transcript_absorb(transcript, g0, g1, g2);
        uint64_t r = top->sc_challenge_out;
        if (r != transcript || top->sc_transcript_out != transcript) {
            std::cerr << "[FAIL] round " << round << ": hardware challenge 0x" << std::hex << r
                      << " != transcript 0x" << transcript << std::dec << std::endl;
            return 1;
        }
        // verifier: g(0) + g(1) must be the running claim; the degree-1 check g(2) = 2 g(1) - g(0)
        if (round_claim != claimed || sub_mod(g1, g0) != sub_mod(g2, g1)) {
            std::cerr << "[FAIL] round " << round << " claim/consistency" << std::endl; return 1;
        }
        std::string rk = "round" + std::to_string(round);
        if (g0 != need(golden, rk + "_g0") || g1 != need(golden, rk + "_g1") || g2 != need(golden, rk + "_g2") ||
            r != need(golden, rk + "_challenge") || need(golden, rk + "_claim_ok") != 1ULL) {
            std::cerr << "[FAIL] round " << round << " differs from the Lean golden" << std::endl; return 1;
        }
        claimed = add_mod(g0, mul_mod(r, sub_mod(g1, g0)));
        if (claimed != need(golden, rk + "_next_claim")) {
            std::cerr << "[FAIL] round " << round << " next claim differs from the Lean golden" << std::endl; return 1;
        }
        // fold with the registered challenge (combinational on the pair inputs)
        std::vector<uint64_t> next_table(half);
        for (size_t j = 0; j < half; ++j) {
            uint64_t f0 = table[2 * j], f1 = table[2 * j + 1];
            top->sc_f0_in = f0; top->sc_f1_in = f1;
            top->eval();
            uint64_t ref_fold = add_mod(f0, mul_mod(r, sub_mod(f1, f0)));
            if (top->sc_folded_out != ref_fold) {
                std::cerr << "[FAIL] fold round " << round << " pair " << j << std::endl; return 1;
            }
            next_table[j] = top->sc_folded_out;
        }
        table = next_table;
        std::printf("[round %d] pairs=%3zu g0=0x%016llx g1=0x%016llx g2=0x%016llx r=0x%016llx next_claim=0x%016llx\n",
                    round, half, (unsigned long long)g0, (unsigned long long)g1, (unsigned long long)g2,
                    (unsigned long long)r, (unsigned long long)claimed);
    }
    if (table.size() != 1 || table[0] != claimed || table[0] != need(golden, "final") ||
        claimed != need(golden, "final_claim")) {
        std::cerr << "[FAIL] final oracle check: table[0]=0x" << std::hex << table[0] << " claim=0x" << claimed
                  << std::dec << std::endl;
        return 1;
    }
    std::cout << "[PASS] 8-round sumcheck with the hardware transcript (" << pair_ticks
              << " pair cycles; challenges, accumulators and claims match the Lean golden)" << std::endl;

    tfp->close();
    delete tfp;
    delete top;
    return 0;
}
