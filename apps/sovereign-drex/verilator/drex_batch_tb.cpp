// Objective Bend Flagship App #7 (`apps/sovereign-drex/verilator/drex_batch_tb.cpp`)
// Verilator C++ testbench for 4-Validator Sovereign `DReX` + `K-CARRY` Batch Clearing & Live Upgrade.

#include "Vsovereign_drex_batch_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <cassert>
#include <cstdint>
#include <iostream>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    Vsovereign_drex_batch_top* dut = new Vsovereign_drex_batch_top;
    VerilatedVcdC* tfp = new VerilatedVcdC;
    dut->trace(tfp, 99);
    tfp->open("sovereign_drex_trace.vcd");

    vluint64_t sim_time = 0;
    auto tick = [&]() {
        dut->clk = 0;
        dut->eval();
        tfp->dump(sim_time++);
        dut->clk = 1;
        dut->eval();
        tfp->dump(sim_time++);
    };

    dut->rst_n = 0;
    dut->in_lot_count = 0;
    dut->in_epoch_id = 0;
    dut->in_validator_votes = 0;
    dut->in_carry_upgrade_en = 0;
    dut->in_old_cbdc_total = 1000000;
    dut->in_delta_debit = 0;
    dut->in_delta_credit = 0;
    dut->in_seat_cbdc_after = 0;
    dut->in_seat_want_floor = 0;
    dut->in_forever_crown_drop_req = 0;
    tick();
    dut->rst_n = 1;

    // 1. Verify Epoch 1 BaseSovereignDrexSpec batch clearing (3-of-4 BFT quorum: V0, V1, V2)
    dut->in_lot_count = 8;
    dut->in_epoch_id = 3;
    dut->in_validator_votes = 0b0111; // 3 of 4 validators
    dut->in_carry_upgrade_en = 0;
    dut->in_old_cbdc_total = 1000000;
    dut->in_delta_debit = 50000;
    dut->in_delta_credit = 50000;
    dut->in_seat_cbdc_after = 95000;
    dut->in_seat_want_floor = 75000;
    dut->in_forever_crown_drop_req = 0;
    tick();

    assert(dut->out_validator_quorum == 3ULL);
    assert(dut->out_vote_count == 3ULL);
    assert(dut->out_quorum_reached == 1);
    assert(dut->out_protected_welfare_crown == 1000ULL);
    assert(dut->out_settled_cbdc_liquidity == 100000ULL);
    assert(dut->out_batch_settlement_cbdc == 5000ULL); // 8 * 500 + 1000
    assert(dut->out_finality_commit_tag == 195ULL);    // 3 * 64 + 3
    assert(dut->out_carry_pin_digest == 102ULL);       // 3 * 32 + 6
    assert(dut->out_new_cbdc_total == 1000000ULL);
    assert(dut->out_turn_admitted == 1);

    // 2. Verify Live K-CARRY Pin Upgrade (`in_carry_upgrade_en = 1`) at Epoch 3 & 5
    dut->in_carry_upgrade_en = 1;
    dut->in_validator_votes = 0b1111; // 4 of 4 validators
    tick();
    assert(dut->out_settled_cbdc_liquidity == 125000ULL);
    assert(dut->out_batch_settlement_cbdc == 5000ULL); // drexSettlementAt8 = 5000
    assert(dut->out_finality_commit_tag == 227ULL);    // drexFinalityTagAt3 = 227
    assert(dut->out_protected_welfare_crown == 1000ULL);
    assert(dut->out_new_cbdc_total == 1000000ULL);
    assert(dut->out_turn_admitted == 1);

    dut->in_lot_count = 12;
    dut->in_epoch_id = 5;
    tick();
    assert(dut->out_batch_settlement_cbdc == 7000ULL); // sovereignClearedAt12 = 7000
    assert(dut->out_carry_pin_digest == 182ULL);       // sovereignDigestAt5 = 182
    assert(dut->out_turn_admitted == 1);

    // 3. Verify Adversarial Refusal Cases (Fail-Closed Guards):
    // 3a. Under-quorum (only 2 of 4 validators vote)
    dut->in_validator_votes = 0b0011;
    tick();
    assert(dut->out_quorum_reached == 0);
    assert(dut->out_turn_admitted == 0);
    dut->in_validator_votes = 0b1111;

    // 3b. Unreported state-balance inflation (credit != debit)
    dut->in_delta_debit = 50000;
    dut->in_delta_credit = 1000000;
    tick();
    assert(dut->out_turn_admitted == 0);
    assert(dut->out_new_cbdc_total == 1000000ULL); // Total supply unchanged on refused turn!
    dut->in_delta_credit = 50000;

    // 3c. Agoric/Zoe offer-safety violation (seat balance < want floor)
    dut->in_seat_cbdc_after = 60000;
    dut->in_seat_want_floor = 75000;
    tick();
    assert(dut->out_turn_admitted == 0);
    dut->in_seat_cbdc_after = 95000;

    // 3d. Attempted drop of "forever" welfare-credit crown cell
    dut->in_forever_crown_drop_req = 1;
    tick();
    assert(dut->out_turn_admitted == 0);
    dut->in_forever_crown_drop_req = 0;

    // 4. Sweep 32 consecutive epochs of valid 3-of-4 batch clears
    int admitted_batches = 0;
    for (uint64_t ep = 1; ep <= 32; ++ep) {
        dut->in_epoch_id = ep;
        dut->in_lot_count = ep * 2;
        dut->in_validator_votes = (ep % 2 == 0) ? 0b1110 : 0b1011;
        dut->in_delta_debit = ep * 1000;
        dut->in_delta_credit = ep * 1000;
        tick();
        assert(dut->out_turn_admitted == 1);
        assert(dut->out_new_cbdc_total == 1000000ULL);
        assert(dut->out_protected_welfare_crown == 1000ULL);
        admitted_batches++;
    }

    tfp->close();
    delete tfp;
    delete dut;

    std::cout << "[sovereign-drex] Verilator 4-Validator DReX + K-CARRY Verification PASSED\n"
              << "  validators=4 quorum=3 admitted_batches=" << admitted_batches
              << " adversarial_refusals=4 welfare_crown=1000 cbdc_supply_conserved=1000000\n";
    return 0;
}
