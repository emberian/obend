// =============================================================================
// Flagship App #5: `apps/silicon-kernel-verilator/verilator/sim_main.cpp`
// C++17 Verilator Co-Simulation Harness for `silicon_elab_top.sv`
// =============================================================================
// Exercises & verifies:
//   1. AXI4-Stream 128-bit `OBCAMv1` frame ingestion (magic `0x31564D4143424F00`
//      + 88-bit `PackedNodeWord` table matching `packNodeWord88` in `ExprCAM.lean`).
//   2. Zone 1: 1-cycle closed-term beta-reduction bypass on `(λ _ : Nat => 42) 7`.
//   3. Zone 2: 1-cycle handle-equality reflexivity & parallel `.app` NoC flit fork/join.
//   4. Zone 3: Epoch-1 `DiscrTreeLUT` fast hit (`4 * 10 + 2 = 42`) and 1-cycle
//      `moved_pin_blocks` fallback to Zone 1 on environment pin mutation (`epoch 2`).
//   5. Live Mid-Stream 3-Phase Glitch-Free `ICAP` DPR Hot-Swap (`admitSimpTheoremDpr`):
//      - Phase 1 (`ISOLATE`): clamps `zone3_lut_value == 42` while `zone3_isolated == 1`.
//      - Corrupt CRC / `sorryAx` theorem rejection test (`zone3_dpr_rejected == 1`).
//      - Phase 2 (`LOAD_FRAME`): loads Epoch-2 (`gain = 6, offset = 10, digest = 0x600A`).
//      - Phase 3 (`RELEASE_FENCE`): releases fence and evaluates `6 * 10 + 10 = 70` in 1 cycle.
//   6. Zone 4: Hardware bottom-up CAM typechecker accepting `validIdNatDecl`,
//      `validPropIdDecl`, and `validApplyId42Decl` (`status_tag == 1`), and refusing
//      `#tooth`-mutated ill-typed applications (`status_tag == 2`), `invalidMismatchDecl`
//      (`status_tag == 2`), `invalidUniverseDecl` (`status_tag == 3`), and `invalidSorryDecl`
//      (`status_tag == 0`).
//   7. Dumps `silicon_elab_wave.vcd` waveform trace.
// =============================================================================

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>

#include "Vsilicon_elab_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

namespace {

struct PackedNodeDesc {
    uint8_t  tag;
    uint16_t h0;
    uint16_t h1;
    uint16_t h2;
    uint16_t symIdx;
    uint16_t maxLooseBVar;
    bool     hasFVar;
    bool     hasMVar;
    bool     hasLooseBVar;
};

// Pack a `PackedNodeDesc` into 88-bit layout (`w[0..2]`) matching `packNodeWord88` in `ExprCAM.lean:1819`
void packNode88ToAxisBeat(uint8_t addr, const PackedNodeDesc& d, VlWide<4>& beat) {
    uint64_t lo64 = (uint64_t(d.h0)) |
                    (uint64_t(d.h1) << 16) |
                    (uint64_t(d.h2) << 32) |
                    (uint64_t(d.symIdx) << 48);
    uint8_t flags = (d.hasFVar ? 1u : 0u) |
                    (d.hasMVar ? 2u : 0u) |
                    (d.hasLooseBVar ? 4u : 0u) |
                    ((d.tag & 0xFu) << 4);
    uint64_t hi64 = (uint64_t(d.maxLooseBVar)) |
                    (uint64_t(flags) << 16) |
                    (uint64_t(addr) << 48) |
                    (uint64_t(0x01u) << 56); // beat_kind = 0x01 (PackedNodeWord)
    beat[0] = static_cast<uint32_t>(lo64 & 0xFFFFFFFFull);
    beat[1] = static_cast<uint32_t>((lo64 >> 32) & 0xFFFFFFFFull);
    beat[2] = static_cast<uint32_t>(hi64 & 0xFFFFFFFFull);
    beat[3] = static_cast<uint32_t>((hi64 >> 32) & 0xFFFFFFFFull);
}

void packObcamHeaderBeat(uint32_t nodeCount, VlWide<4>& beat) {
    const uint64_t magic = 0x31564D4143424F00ull; // "\0OBCAMV1"
    uint64_t hi64 = uint64_t(nodeCount) | (uint64_t(0x00u) << 56);
    beat[0] = static_cast<uint32_t>(magic & 0xFFFFFFFFull);
    beat[1] = static_cast<uint32_t>((magic >> 32) & 0xFFFFFFFFull);
    beat[2] = static_cast<uint32_t>(hi64 & 0xFFFFFFFFull);
    beat[3] = static_cast<uint32_t>((hi64 >> 32) & 0xFFFFFFFFull);
}

void packSymbolBeat(uint8_t symIdx, uint8_t symKind, VlWide<4>& beat) {
    uint64_t lo64 = uint64_t(symKind) | (uint64_t(symIdx) << 16);
    uint64_t hi64 = (uint64_t(0x02u) << 56); // beat_kind = 0x02 (HwCamSymbolEntry)
    beat[0] = static_cast<uint32_t>(lo64 & 0xFFFFFFFFull);
    beat[1] = 0u;
    beat[2] = 0u;
    beat[3] = static_cast<uint32_t>((hi64 >> 32) & 0xFFFFFFFFull);
}

class SiliconElabHarness {
public:
    Vsilicon_elab_top* top;
    VerilatedVcdC*     tfp;
    uint64_t           sim_time = 0;

    explicit SiliconElabHarness(const char* vcd_path) {
        top = new Vsilicon_elab_top;
        tfp = new VerilatedVcdC;
        top->trace(tfp, 99);
        tfp->open(vcd_path);
        clearCommands();
        top->rst_n = 0;
    }

    ~SiliconElabHarness() {
        if (tfp) {
            tfp->close();
            delete tfp;
        }
        delete top;
    }

    void clearCommands() {
        top->s_axis_tvalid        = 0;
        top->s_axis_tlast         = 0;
        top->s_axis_tdata[0]      = 0;
        top->s_axis_tdata[1]      = 0;
        top->s_axis_tdata[2]      = 0;
        top->s_axis_tdata[3]      = 0;
        top->cmd_whnf_start       = 0;
        top->cmd_whnf_step        = 0;
        top->cmd_whnf_init_handle = 0;
        top->cmd_unify_req        = 0;
        top->cmd_unify_lhs        = 0;
        top->cmd_unify_rhs        = 0;
        top->cmd_lut_eval_req     = 0;
        top->cmd_pkt_epoch        = 1;
        top->cmd_env_pin_valid    = 1;
        top->cmd_lut_arg_val      = 10;
        top->cmd_dpr_phase        = 0;
        top->cmd_dpr_thm_ok       = 0;
        top->cmd_dpr_new_epoch    = 2;
        top->cmd_dpr_new_gain     = 6;
        top->cmd_dpr_new_offset   = 10;
        top->cmd_dpr_exp_digest   = 0x600Aull;
        top->cmd_dpr_comp_digest  = 0x600Aull;
        top->cmd_zone4_check_req  = 0;
        top->cmd_target_val_h     = 0;
        top->cmd_target_ty_h      = 0;
    }

    void tick() {
        top->clk = 0;
        top->eval();
        tfp->dump(sim_time++);
        top->clk = 1;
        top->eval();
        tfp->dump(sim_time++);
    }

    void reset() {
        top->rst_n = 0;
        tick();
        tick();
        top->rst_n = 1;
        tick();
    }

    void sendAxisBeat(const VlWide<4>& beat, bool last = false) {
        top->s_axis_tvalid   = 1;
        top->s_axis_tlast    = last ? 1 : 0;
        top->s_axis_tdata[0] = beat[0];
        top->s_axis_tdata[1] = beat[1];
        top->s_axis_tdata[2] = beat[2];
        top->s_axis_tdata[3] = beat[3];
        tick();
        top->s_axis_tvalid   = 0;
        top->s_axis_tlast    = 0;
    }
};

} // namespace

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::randReset(2);
    Verilated::traceEverOn(true);

    const char* vcd_path = (argc > 1) ? argv[1] : "silicon_elab_wave.vcd";
    SiliconElabHarness sim(vcd_path);
    sim.reset();

    // =========================================================================
    // Step 1: Stream `OBCAMv1` Frame over 128-Bit AXI4-Stream
    // =========================================================================
    VlWide<4> beat;
    packObcamHeaderBeat(16, beat);
    sim.sendAxisBeat(beat, false);
    assert(sim.top->obcam_header_valid == 1);
    assert(sim.top->obcam_node_count == 16);

    // Populate Section 2: `HwCamSymbolEntry` table
    // sym 1: Nat, sym 2: Bool, sym 3: idNat/Nat.succ, sym 4: PropId, sym 5: Bool.true,
    // sym 6: Sort 0 (Prop), sym 7: Sort 1 (Type 0), sym 15: sorryAx
    packSymbolBeat(1,  1,  beat); sim.sendAxisBeat(beat);
    packSymbolBeat(2,  2,  beat); sim.sendAxisBeat(beat);
    packSymbolBeat(3,  3,  beat); sim.sendAxisBeat(beat);
    packSymbolBeat(4,  4,  beat); sim.sendAxisBeat(beat);
    packSymbolBeat(5,  5,  beat); sim.sendAxisBeat(beat);
    packSymbolBeat(6,  6,  beat); sim.sendAxisBeat(beat);
    packSymbolBeat(7,  7,  beat); sim.sendAxisBeat(beat);
    packSymbolBeat(15, 15, beat); sim.sendAxisBeat(beat);

    // Populate Section 1: 88-Bit `PackedNodeWord` Table (`HwExprCAM`)
    // Handle 0 : `.const "Nat" []` (tag=3, symIdx=1)
    // Handle 1 : `.bvar 0` (tag=0, h0=0, hasLooseBVar=true, maxLooseBVar=1)
    // Handle 2 : `.lam Nat (.bvar 0)` (tag=5, h0=0, h1=1, closed) -> `validIdNatDecl` value
    // Handle 3 : `.forallE Nat Nat` (tag=6, h0=0, h1=0, closed) -> `Nat -> Nat` type
    // Handle 4 : `.lit 42` (tag=8, h0=42, closed)
    // Handle 5 : `.lit 7` (tag=8, h0=7, closed)
    // Handle 6 : `.lam Nat 42` (tag=5, h0=0, h1=4, closed)
    // Handle 7 : `.app (.lam Nat 42) 7` (tag=4, h0=6, h1=5, closed) -> closed beta redex!
    // Handle 8 : `.const "idNat" []` (tag=3, symIdx=3)
    // Handle 9 : `.app idNat 42` (tag=4, h0=8, h1=4, closed) -> `validApplyId42Decl` value
    // Handle 10: `.sort 0` (`Prop`, tag=2, symIdx=6)
    // Handle 11: `.lam Prop (.lam (.bvar 0) (.bvar 0))` (tag=5, h0=10, h1=2, closed) -> `validPropIdDecl` value
    // Handle 12: `.forallE Prop (P -> P)` (tag=6, h0=10, h1=3, symIdx=4) -> `validPropIdDecl` type
    // Handle 13: `.const "Bool.true" []` (tag=3, symIdx=5) -> `invalidMismatchDecl` value
    // Handle 14: `.app idNat Bool.true` (tag=4, h0=8, h1=13) -> `#tooth` mutated `invalidBadAppDecl`
    // Handle 15: `.const "sorryAx" [0]` (tag=3, symIdx=15) -> `invalidSorryDecl` value
    const PackedNodeDesc nodes[] = {
        /* 0  */ {3, 0,  0,  0, 1,  0, false, false, false},
        /* 1  */ {0, 0,  0,  0, 0,  1, false, false, true },
        /* 2  */ {5, 0,  1,  0, 0,  0, false, false, false},
        /* 3  */ {6, 0,  0,  0, 0,  0, false, false, false},
        /* 4  */ {8, 42, 0,  0, 0,  0, false, false, false},
        /* 5  */ {8, 7,  0,  0, 0,  0, false, false, false},
        /* 6  */ {5, 0,  4,  0, 0,  0, false, false, false},
        /* 7  */ {4, 6,  5,  0, 0,  0, false, false, false},
        /* 8  */ {3, 0,  0,  0, 3,  0, false, false, false},
        /* 9  */ {4, 8,  4,  0, 0,  0, false, false, false},
        /* 10 */ {2, 0,  0,  0, 6,  0, false, false, false},
        /* 11 */ {5, 10, 2,  0, 0,  0, false, false, false},
        /* 12 */ {6, 10, 3,  0, 4,  0, false, false, false},
        /* 13 */ {3, 0,  0,  0, 5,  0, false, false, false},
        /* 14 */ {4, 8,  13, 0, 0,  0, false, false, false},
        /* 15 */ {3, 0,  0,  0, 15, 0, false, false, false}
    };
    for (uint8_t i = 0; i < 16; ++i) {
        packNode88ToAxisBeat(i, nodes[i], beat);
        sim.sendAxisBeat(beat, i == 15);
    }

    // =========================================================================
    // Step 2: Zone 1 1-Cycle Closed-Term Beta-Reduction Bypass
    //         `(λ _ : Nat => 42) 7` (handle 7) -> handle 4 (`42`) in 1 cycle!
    // =========================================================================
    sim.top->cmd_whnf_start       = 1;
    sim.top->cmd_whnf_init_handle = 7;
    sim.tick();
    sim.top->cmd_whnf_start       = 0;

    sim.top->cmd_whnf_step        = 1;
    sim.tick();
    sim.top->cmd_whnf_step        = 0;
    assert(sim.top->zone1_whnf_done == 1);
    assert(sim.top->zone1_focus_handle == 4);
    assert(sim.top->perf_bypass_cnt == 1);

    // =========================================================================
    // Step 3: Zone 2 1-Cycle Handle Equality & Parallel `.app` NoC Unification
    // =========================================================================
    sim.top->cmd_unify_req = 1;
    sim.top->cmd_unify_lhs = 9;
    sim.top->cmd_unify_rhs = 9;
    sim.tick();
    assert(sim.top->zone2_unify_done == 1);
    assert(sim.top->zone2_unify_ok == 1);

    // Parallel `.app` decomposition on handle 9 vs handle 14 (mismatch on arg 4 vs 13)
    sim.top->cmd_unify_lhs = 9;
    sim.top->cmd_unify_rhs = 14;
    sim.tick();
    sim.top->cmd_unify_req = 0;
    assert(sim.top->zone2_unify_done == 1);
    assert(sim.top->zone2_unify_ok == 0);
    assert(sim.top->perf_noc_flits == 6);

    // =========================================================================
    // Step 4: Zone 3 Epoch-1 `DiscrTreeLUT` Fast Hit vs. 1-Cycle `moved_pin_blocks`
    //         Fallback to Zone 1 on Pin Mutation
    // =========================================================================
    // 4a. Epoch 1 fast hit (`4 * 10 + 2 = 42`)
    sim.top->cmd_lut_eval_req  = 1;
    sim.top->cmd_pkt_epoch     = 1;
    sim.top->cmd_env_pin_valid = 1;
    sim.top->cmd_lut_arg_val   = 10;
    sim.tick();
    sim.top->cmd_lut_eval_req  = 0;
    assert(sim.top->zone3_used_fast_path == 1);
    assert(sim.top->zone3_routed_to_zone1 == 0);
    assert(sim.top->zone3_lut_value == 42);
    assert(sim.top->perf_lut_hits == 1);
    const uint64_t epoch1_lut_hw = sim.top->zone3_lut_value;

    // 4b. Re-arm Zone 1 on closed beta redex (handle 7), then mutate pin (`pkt_epoch = 2` while `pinned_epoch == 1`):
    //     Verifies 1-cycle `moved_pin_blocks` fallback to Zone 1 WHNF (`zone3_routed_to_zone1 == 1` AND Zone 1 steps to handle 4)!
    sim.top->cmd_whnf_start       = 1;
    sim.top->cmd_whnf_init_handle = 7;
    sim.tick();
    sim.top->cmd_whnf_start       = 0;

    sim.top->cmd_lut_eval_req  = 1;
    sim.top->cmd_pkt_epoch     = 2; // Stale epoch pin!
    sim.top->cmd_env_pin_valid = 1;
    sim.top->cmd_lut_arg_val   = 10;
    sim.tick();
    sim.top->cmd_lut_eval_req  = 0;
    assert(sim.top->zone3_used_fast_path == 0);
    assert(sim.top->zone3_routed_to_zone1 == 1);
    assert(sim.top->zone1_focus_handle == 4);
    assert(sim.top->perf_bypass_cnt == 2);
    const bool moved_pin_fallback_hw =
        (sim.top->zone3_used_fast_path == 0) &&
        (sim.top->zone3_routed_to_zone1 == 1) &&
        (sim.top->zone1_focus_handle == 4);

    // =========================================================================
    // Step 5: Live Mid-Stream 3-Phase Glitch-Free `ICAP` DPR Hot-Swap of Zone 3
    //         (`admitSimpTheoremDpr`: Epoch 1 `4*x+2` -> Epoch 2 `6*x+10`)
    // =========================================================================
    // First verify `validPropIdDecl` (handle 11 : handle 12) in Zone 4
    sim.top->cmd_zone4_check_req = 1;
    sim.top->cmd_target_val_h    = 11;
    sim.top->cmd_target_ty_h     = 12;
    sim.tick();
    sim.top->cmd_zone4_check_req = 0;
    assert(sim.top->zone4_check_done == 1);
    assert(sim.top->zone4_inferred_ty_code == 34);
    assert(sim.top->zone4_kernel_accepted == 1);
    assert(sim.top->zone4_status_tag == 1);

    // Phase 1 (`dprPhase1Isolate`): Engage isolation fence; verify output is clamped to `42`
    sim.top->cmd_dpr_phase = 1;
    sim.tick();
    assert(sim.top->zone3_isolated == 1);
    assert(sim.top->zone3_lut_value == 42);

    // Negative DPR test 5a: attempt Phase 2 with corrupt CRC digest (`0xDEAD != 0x600A`)
    sim.top->cmd_dpr_phase       = 2;
    sim.top->cmd_dpr_thm_ok      = 1;
    sim.top->cmd_dpr_new_epoch   = 2;
    sim.top->cmd_dpr_new_gain    = 6;
    sim.top->cmd_dpr_new_offset  = 10;
    sim.top->cmd_dpr_exp_digest  = 0x600Aull;
    sim.top->cmd_dpr_comp_digest = 0xDEADull;
    sim.tick();
    assert(sim.top->zone3_isolated == 1);
    assert(sim.top->zone3_dpr_rejected == 1);
    assert(sim.top->zone3_lut_value == 42); // Still clamped glitch-free!

    // Negative DPR test 5b: attempt Phase 2 with unverified `#tooth`/`sorryAx` theorem (`cmd_dpr_thm_ok = 0`)
    sim.top->cmd_dpr_phase       = 2;
    sim.top->cmd_dpr_thm_ok      = 0;
    sim.top->cmd_dpr_new_epoch   = 2;
    sim.top->cmd_dpr_new_gain    = 6;
    sim.top->cmd_dpr_new_offset  = 10;
    sim.top->cmd_dpr_exp_digest  = 0x600Aull;
    sim.top->cmd_dpr_comp_digest = 0x600Aull;
    sim.tick();
    assert(sim.top->zone3_isolated == 1);
    assert(sim.top->zone3_dpr_rejected == 1);
    assert(sim.top->zone3_lut_value == 42); // Still clamped glitch-free!

    // Valid Phase 2 (`dprPhase2LoadFrame`): load Epoch-2 bitstream (`gain = 6, offset = 10, digest = 0x600A`)
    sim.top->cmd_dpr_phase       = 2;
    sim.top->cmd_dpr_thm_ok      = 1;
    sim.top->cmd_dpr_new_epoch   = 2;
    sim.top->cmd_dpr_new_gain    = 6;
    sim.top->cmd_dpr_new_offset  = 10;
    sim.top->cmd_dpr_exp_digest  = 0x600Aull;
    sim.top->cmd_dpr_comp_digest = 0x600Aull;
    sim.tick();
    assert(sim.top->zone3_isolated == 1);
    assert(sim.top->zone3_dpr_rejected == 0);
    assert(sim.top->zone3_lut_value == 42); // Clamped to `skidHeldOutput` during frame write!
    const bool dpr_clamped_during_write =
        (sim.top->zone3_isolated == 1) && (sim.top->zone3_lut_value == 42);

    // Phase 3 (`dprPhase3ReleaseFence`): release isolation fence
    sim.top->cmd_dpr_phase = 3;
    sim.tick();
    sim.top->cmd_dpr_phase = 0;
    assert(sim.top->zone3_isolated == 0);
    assert(sim.top->zone3_pinned_epoch == 2);
    assert(sim.top->zone3_lut_value == 70);

    // Evaluate Epoch-2 packet (`6 * 10 + 10 = 70`) in 1 cycle!
    sim.top->cmd_lut_eval_req  = 1;
    sim.top->cmd_pkt_epoch     = 2;
    sim.top->cmd_env_pin_valid = 1;
    sim.top->cmd_lut_arg_val   = 10;
    sim.tick();
    sim.top->cmd_lut_eval_req  = 0;
    assert(sim.top->zone3_used_fast_path == 1);
    assert(sim.top->zone3_routed_to_zone1 == 0);
    assert(sim.top->zone3_lut_value == 70);
    assert(sim.top->perf_lut_hits == 2);
    const uint64_t epoch2_lut_hw = sim.top->zone3_lut_value;
    const bool dpr_glitch_free_clamped_hw =
        dpr_clamped_during_write && (epoch2_lut_hw == 70);

    // =========================================================================
    // Step 6: Zone 4 Hardware Kernel Gate — Positive & `#tooth` / `sorryAx` Refusal Poles
    // =========================================================================
    // 6a. `validIdNatDecl` (handle 2 : handle 3 -> accepted, code 17, status_tag 1)
    sim.top->cmd_zone4_check_req = 1;
    sim.top->cmd_target_val_h    = 2;
    sim.top->cmd_target_ty_h     = 3;
    sim.tick();
    assert(sim.top->zone4_inferred_ty_code == 17);
    assert(sim.top->zone4_node_defeq_ok == 1);
    assert(sim.top->zone4_kernel_accepted == 1);
    assert(sim.top->zone4_status_tag == 1);

    // 6b. `validApplyId42Decl` (handle 9 : handle 0 -> accepted, code 1, status_tag 1)
    sim.top->cmd_target_val_h = 9;
    sim.top->cmd_target_ty_h  = 0;
    sim.tick();
    assert(sim.top->zone4_inferred_ty_code == 1);
    assert(sim.top->zone4_node_defeq_ok == 1);
    assert(sim.top->zone4_kernel_accepted == 1);
    assert(sim.top->zone4_status_tag == 1);

    // 6c. `#tooth`-Mutated Ill-Typed Application `idNat Bool.true` (`invalidBadAppDecl`, handle 14 : handle 0 -> REFUSED, status_tag 2)
    sim.top->cmd_target_val_h = 14;
    sim.top->cmd_target_ty_h  = 0;
    sim.tick();
    assert(sim.top->zone4_inferred_ty_code == 0);
    assert(sim.top->zone4_node_defeq_ok == 0);
    assert(sim.top->zone4_kernel_accepted == 0);
    assert(sim.top->zone4_status_tag == 2);
    const bool tooth_mutant_refused_hw =
        (sim.top->zone4_kernel_accepted == 0) && (sim.top->zone4_status_tag == 2);

    // 6d. Type Mismatch `Bool.true : Nat` (`invalidMismatchDecl`, handle 13 : handle 0 -> REFUSED, status_tag 2)
    sim.top->cmd_target_val_h = 13;
    sim.top->cmd_target_ty_h  = 0;
    sim.tick();
    assert(sim.top->zone4_inferred_ty_code == 5);
    assert(sim.top->zone4_node_defeq_ok == 0);
    assert(sim.top->zone4_kernel_accepted == 0);
    assert(sim.top->zone4_status_tag == 2);

    // 6e. Universe Sort Mismatch `Nat : Prop` (`invalidUniverseDecl`, handle 0 : handle 10 -> REFUSED, status_tag 3)
    sim.top->cmd_target_val_h = 0;
    sim.top->cmd_target_ty_h  = 10;
    sim.tick();
    assert(sim.top->zone4_inferred_ty_code == 3);
    assert(sim.top->zone4_node_defeq_ok == 0);
    assert(sim.top->zone4_kernel_accepted == 0);
    assert(sim.top->zone4_status_tag == 3);

    // 6f. `sorryAx` Contamination (`invalidSorryDecl`, handle 15 : handle 12 -> REFUSED, status_tag 0)
    sim.top->cmd_target_val_h = 15;
    sim.top->cmd_target_ty_h  = 12;
    sim.tick();
    sim.top->cmd_zone4_check_req = 0;
    assert(sim.top->zone4_inferred_ty_code == 0);
    assert(sim.top->zone4_node_defeq_ok == 0);
    assert(sim.top->zone4_kernel_accepted == 0);
    assert(sim.top->zone4_status_tag == 0);
    const bool sorry_refused_hw =
        (sim.top->zone4_kernel_accepted == 0) && (sim.top->zone4_status_tag == 0);

    std::printf(
        "{\"status\":\"PASS\",\"cycles\":%u,\"cam_hits\":%u,\"beta_bypasses\":%u,"
        "\"noc_flits\":%u,\"lut_hits\":%u,\"epoch1_lut\":%llu,\"epoch2_lut\":%llu,"
        "\"moved_pin_fallback_1cycle\":%s,\"dpr_glitch_free_clamped\":%s,"
        "\"tooth_mutant_refused\":%s,\"sorry_refused\":%s,\"vcd\":\"%s\"}\n",
        sim.top->perf_cycles,
        sim.top->perf_cam_hits,
        sim.top->perf_bypass_cnt,
        sim.top->perf_noc_flits,
        sim.top->perf_lut_hits,
        static_cast<unsigned long long>(epoch1_lut_hw),
        static_cast<unsigned long long>(epoch2_lut_hw),
        moved_pin_fallback_hw ? "true" : "false",
        dpr_glitch_free_clamped_hw ? "true" : "false",
        tooth_mutant_refused_hw ? "true" : "false",
        sorry_refused_hw ? "true" : "false",
        vcd_path);

    return 0;
}
