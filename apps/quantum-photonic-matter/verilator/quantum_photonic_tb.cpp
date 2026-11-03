// Flagship App #8: Quantum Photonic & Topological Matter Co-Processor Verilator Testbench
// (`apps/quantum-photonic-matter/verilator/quantum_photonic_tb.cpp`)
//
// Cycle-accurate Verilator simulation of the Lean-emitted `quantum_photonic_coproc_top.sv`
// (`emitModuleSV quantumPhotonicCoprocTopRtlModule`):
// 1. `.obend` open-recursive datapath agreement (`QuantumPhotonicTop.obend`, `ClementsKrawtchoukArray.obend`):
//    - `coprocAdjointOpsAt25 = 8869` (`25 * 4 + 8769`),
//    - `coprocBudgetAt6 = 132` (`(6 * 16 + 4) + 32`),
//    - `krawtchoukMacsAt16 = 3206` (`16 * 4 + 3142`),
//    - `krawtchoukFidelityAt4 = 2004` (`(4 * 250 + 4) + 1000`),
//    - CMT directional coupler lengths L_0 = 1571 nm, L_1 = 2721 nm, L_2 = 3142 nm.
// 2. 1-WL Quotient DPR Guard & 1-Cycle Symmetry-Breaking Fallback (`quotientHypergraph_moved_pin_blocks`):
//    - Under symmetric 4-lane catgrad weights `(5, 5, 7, 7)` and Q_3 shell weights `(3, 4, 3)`,
//      `out_dpr_quotient_usable == 1`, `out_active_hypergraph_wires == 12` (2x compression vs 24),
//      `out_active_q3_modes == 4` (2x compression vs 8), and degree-4 scaled Krawtchouk Taylor
//      amplitude `out_q3_pst_shell3_imag_scaled == 9287743200` (exact 64-bit match with Lean!).
//    - When an `.obend` layer override moves `w1` (`5 -> 99`) or `shell_w01` (`3 -> 5`),
//      `out_dpr_quotient_usable` drops to 0 in 1 cycle and falls back to 24 wires / 8 modes.
// 3. 4x4 Faddeev-LeVerrier Exact Thermo-Optic Crosstalk Cancellation (`compensateThermalCrosstalk_exact_4x4`):
//    - Verifies `G_th * adj(G_th) * v == 8769 * v` across 16 signed 4-channel phase vectors.
// 4. Genuine 3-Stage Complex Spinor Majorana Braiding (`T_01 T_12 T_01 == T_12 T_01 T_12`) &
//    Chiral Fermion-Parity Cooling (`spinorChiralParity = diag(1, 1, -1, -1)`, `parityCoolingJumpOp 0`):
//    - Verifies 3-stage Artin braid equality AND 2-stage non-Abelian non-commutativity (`T_12 T_01 != T_01 T_12`),
//    - Verifies `L_cool(0)` is dark on even-parity codewords `(z0, z1, 0, 0)` and maps odd-parity
//      poisoned states `(0, 0, z2, z3) -> (z2, z3, 0, 0)` into the +1 code space in 1 cycle.

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include "Vquantum_photonic_coproc_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

static void tick(Vquantum_photonic_coproc_top* top, VerilatedVcdC* tfp, uint64_t& sim_time) {
    top->clk = 0;
    top->eval();
    if (tfp) tfp->dump(sim_time++);
    top->clk = 1;
    top->eval();
    if (tfp) tfp->dump(sim_time++);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    Vquantum_photonic_coproc_top* top = new Vquantum_photonic_coproc_top;
    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open("quantum_photonic_trace.vcd");

    uint64_t sim_time = 0;

    // Active-high synchronous reset (`emitModuleSV` convention)
    top->rst = 1;
    top->in_batch_vectors = 25ULL;
    top->in_syndrome_rounds = 6ULL;
    top->in_krawtchouk_batch_size = 16ULL;
    top->in_pst_step_index = 4ULL;
    top->in_t_num = 157ULL;
    top->in_t_den = 100ULL;
    top->in_pin_w0 = 5ULL;
    top->in_pin_w1 = 5ULL;
    top->in_pin_w2 = 7ULL;
    top->in_pin_w3 = 7ULL;
    top->in_pin_shell_w01 = 3ULL;
    top->in_pin_shell_w12 = 4ULL;
    top->in_pin_shell_w23 = 3ULL;
    top->in_target_v0 = static_cast<uint64_t>(int64_t{10});
    top->in_target_v1 = static_cast<uint64_t>(int64_t{-5});
    top->in_target_v2 = static_cast<uint64_t>(int64_t{7});
    top->in_target_v3 = static_cast<uint64_t>(int64_t{3});
    top->in_tetron_psi0_re = 3ULL;
    top->in_tetron_psi0_im = 0ULL;
    top->in_tetron_psi1_re = 2ULL;
    top->in_tetron_psi1_im = 0ULL;
    top->in_tetron_psi2_re = 0ULL;
    top->in_tetron_psi2_im = 0ULL;
    top->in_tetron_psi3_re = 0ULL;
    top->in_tetron_psi3_im = 0ULL;
    top->in_braid_enable = 0ULL;

    tick(top, tfp, sim_time);
    top->rst = 0;
    top->in_braid_enable = 1ULL;
    top->eval();

    // 1. Check `.obend` open-recursive outputs against Lean theorems
    assert(top->out_wl_compressed_shells == 4ULL);
    assert(top->out_faddeev_crosstalk_det == 8769ULL);
    assert(top->out_cmt_krawtchouk_len0_nm == 1571ULL);
    assert(top->out_cmt_krawtchouk_len1_nm == 2721ULL);
    assert(top->out_cmt_krawtchouk_len2_nm == 3142ULL);
    assert(top->out_quotient_reverse_adjoint_ops == 8869ULL);
    assert(top->out_coproc_cycle_budget == 132ULL);
    assert(top->out_krawtchouk_adjoint_macs == 3206ULL);
    assert(top->out_pst_transfer_fidelity_ppm == 2004ULL);

    // 2. Check symmetric 1-WL quotient & exact 64-bit Q_3 Taylor PST amplitude (9287743200)
    assert(top->out_dpr_quotient_usable == 1ULL);
    assert(top->out_dpr_fallback_full == 0ULL);
    assert(top->out_active_hypergraph_wires == 12ULL);
    assert(top->out_active_q3_modes == 4ULL);
    assert(top->out_q3_pst_shell3_imag_scaled == 9287743200ULL);
    assert(top->out_q3_pst_antipodal_enclosed == 1ULL);

    // 3. Sweep 16 complex spinor states & crosstalk vectors + 2 DPR symmetry-break injections
    uint32_t crosstalk_vectors_checked = 0;
    uint32_t even_states_dark = 0;
    uint32_t odd_states_cooled = 0;
    uint32_t nonabelian_witnesses = 0;
    uint32_t dpr_fallbacks_triggered = 0;

    for (int i = 0; i < 16; ++i) {
        int64_t v0 = static_cast<int64_t>(i * 3 - 10);
        int64_t v1 = static_cast<int64_t>(7 - i * 2);
        int64_t v2 = static_cast<int64_t>(i * 5 + 1);
        int64_t v3 = static_cast<int64_t>(-4 + i);
        top->in_target_v0 = static_cast<uint64_t>(v0);
        top->in_target_v1 = static_cast<uint64_t>(v1);
        top->in_target_v2 = static_cast<uint64_t>(v2);
        top->in_target_v3 = static_cast<uint64_t>(v3);

        // Alternate between even-parity codewords `{0, 1}` and odd-parity poisoned states `{2, 3}` over Z[i]^4
        int64_t a_re = static_cast<int64_t>(i + 1);
        int64_t a_im = static_cast<int64_t>(2 - i);
        int64_t b_re = static_cast<int64_t>(i * 2 - 3);
        int64_t b_im = static_cast<int64_t>(i + 4);
        if (i % 2 == 0) {
            top->in_tetron_psi0_re = static_cast<uint64_t>(a_re);
            top->in_tetron_psi0_im = static_cast<uint64_t>(a_im);
            top->in_tetron_psi1_re = static_cast<uint64_t>(b_re);
            top->in_tetron_psi1_im = static_cast<uint64_t>(b_im);
            top->in_tetron_psi2_re = 0ULL;
            top->in_tetron_psi2_im = 0ULL;
            top->in_tetron_psi3_re = 0ULL;
            top->in_tetron_psi3_im = 0ULL;
        } else {
            top->in_tetron_psi0_re = 0ULL;
            top->in_tetron_psi0_im = 0ULL;
            top->in_tetron_psi1_re = 0ULL;
            top->in_tetron_psi1_im = 0ULL;
            top->in_tetron_psi2_re = static_cast<uint64_t>(a_re);
            top->in_tetron_psi2_im = static_cast<uint64_t>(a_im);
            top->in_tetron_psi3_re = static_cast<uint64_t>(b_re);
            top->in_tetron_psi3_im = static_cast<uint64_t>(b_im);
        }

        // Inject catgrad channel weight override `w1 = 99` on step 6 and Q_3 shell override `w01 = 5` on step 12
        top->in_pin_w1 = (i == 6) ? 99ULL : 5ULL;
        top->in_pin_shell_w01 = (i == 12) ? 5ULL : 3ULL;

        top->eval();

        assert(top->out_crosstalk_exact_match == 1ULL);
        assert(static_cast<int64_t>(top->out_channel_y0) == 8769LL * v0);
        assert(static_cast<int64_t>(top->out_channel_y1) == 8769LL * v1);
        assert(static_cast<int64_t>(top->out_channel_y2) == 8769LL * v2);
        assert(static_cast<int64_t>(top->out_channel_y3) == 8769LL * v3);
        crosstalk_vectors_checked++;

        assert(top->out_artin_braid_verified == 1ULL);
        assert(top->out_braid_nonabelian_witness == 1ULL);
        nonabelian_witnesses++;
        assert(top->out_cooled_in_even_codespace == 1ULL);

        if (i % 2 == 0) {
            assert(top->out_input_even_parity == 1ULL);
            assert(top->out_input_odd_parity == 0ULL);
            assert(top->out_cool_jump_psi0_re == 0ULL && top->out_cool_jump_psi0_im == 0ULL);
            assert(top->out_cool_jump_psi1_re == 0ULL && top->out_cool_jump_psi1_im == 0ULL);
            assert(top->out_cool_jump_psi2_re == 0ULL && top->out_cool_jump_psi2_im == 0ULL);
            assert(top->out_cool_jump_psi3_re == 0ULL && top->out_cool_jump_psi3_im == 0ULL);
            even_states_dark++;
        } else {
            assert(top->out_input_even_parity == 0ULL);
            assert(top->out_input_odd_parity == 1ULL);
            assert(top->out_cool_jump_psi0_re == static_cast<uint64_t>(a_re));
            assert(top->out_cool_jump_psi0_im == static_cast<uint64_t>(a_im));
            assert(top->out_cool_jump_psi1_re == static_cast<uint64_t>(b_re));
            assert(top->out_cool_jump_psi1_im == static_cast<uint64_t>(b_im));
            assert(top->out_cool_jump_psi2_re == 0ULL && top->out_cool_jump_psi2_im == 0ULL);
            assert(top->out_cool_jump_psi3_re == 0ULL && top->out_cool_jump_psi3_im == 0ULL);
            odd_states_cooled++;
        }

        if (i == 6 || i == 12) {
            assert(top->out_dpr_quotient_usable == 0ULL);
            assert(top->out_dpr_fallback_full == 1ULL);
            assert(top->out_active_hypergraph_wires == 24ULL);
            assert(top->out_active_q3_modes == 8ULL);
            dpr_fallbacks_triggered++;
        } else {
            assert(top->out_dpr_quotient_usable == 1ULL);
            assert(top->out_dpr_fallback_full == 0ULL);
            assert(top->out_active_hypergraph_wires == 12ULL);
            assert(top->out_active_q3_modes == 4ULL);
        }

        tick(top, tfp, sim_time);
    }

    assert(top->out_stabilized_syndrome_epochs == 16ULL);
    assert(top->out_dpr_fallback_events == 2ULL);

    tfp->close();
    delete tfp;
    delete top;

    std::printf(
        "PASS [quantum_photonic_tb]: wl_wires=12/24 q3_taylor_amp=9287743200 "
        "crosstalk_det=8769_vectors=%u artin3_nonabelian=%u even_dark=%u odd_cooled=%u dpr_fallbacks=%u\n",
        crosstalk_vectors_checked,
        nonabelian_witnesses,
        even_states_dark,
        odd_states_cooled,
        dpr_fallbacks_triggered);
    return 0;
}
