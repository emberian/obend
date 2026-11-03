// Objective Bend Flagship App #7 (`apps/sovereign-drex/verilator/drex_batch_tb.cpp`)
// Verilator C++ testbench for 4-Validator Sovereign `DReX` + `K-CARRY` Batch Clearing & Live Upgrade.
//
// Exercises the exact Lean-emitted `sovereign_drex_batch_top.sv` (`emitModuleSV sovereignDrexBatchTopRtlModule`):
// 1. Base Epoch 1..2 batch clearing (`in_carry_upgrade_en = 0`) with 3-of-4 BFT quorum (`0b0111`)
//    and exact `BatchClearing.obend` base pin digest `epoch * 32 + 4` (`36`, `68`).
// 2. Live `K-CARRY` hot-upgrade (`in_carry_upgrade_en = 1`) at Epoch 3:
//    - Stale-pin transaction (`in_tx_pin_digest = 100 = 3 * 32 + 4`) deterministically REFUSED
//      (`out_pin_fresh_ok == 0`, `out_turn_admitted == 0`),
//    - Fresh-pin transaction (`in_tx_pin_digest = 118 = (3 * 32 + 6) + 16`) ADMITTED with
//      `out_settled_cbdc_liquidity == 125000`, `out_finality_commit_tag == 227` (`drexFinalityTagAt3`).
// 3. Validator crash + durable WAL replay anti-double-execution test:
//    - Replaying already-committed Epoch 3 (`in_epoch_id = 3`) or out-of-order Epoch 2 is REFUSED
//      (`out_epoch_monotone_ok == 0`, `out_turn_admitted == 0`, `out_wal_committed_count` unchanged).
// 4. Adversarial fail-closed refusals at Epoch 5 (`carry_pin_digest = 182`, `sovereignDigestAt5`):
//    - Under-quorum (`2 of 4` votes),
//    - Unreported state-balance inflation (`credit != debit`),
//    - Agoric/Zoe offer-safety violation (`seat_cbdc_after < seat_want_floor`),
//    - Attempted drop of `"forever"` welfare-credit crown (`in_forever_crown_drop_req = 1`),
//    followed by valid Epoch 5 commit (`out_batch_settlement_cbdc == 7000`, `sovereignClearedAt12`).
// 5. Strictly monotone 32-epoch sweep (`ep = 6..37`) with rotating 3-of-4 validator quorums.

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

    // Active-high synchronous reset (`emitModuleSV` convention)
    dut->rst = 1;
    dut->in_lot_count = 0;
    dut->in_epoch_id = 0;
    dut->in_validator_votes = 0;
    dut->in_carry_upgrade_en = 0;
    dut->in_old_cbdc_total = 1000000ULL;
    dut->in_delta_debit = 0;
    dut->in_delta_credit = 0;
    dut->in_seat_cbdc_after = 0;
    dut->in_seat_want_floor = 0;
    dut->in_forever_crown_drop_req = 0;
    dut->in_tx_pin_digest = 0;
    tick();
    dut->rst = 0;

    uint32_t admitted_batches = 0;
    uint32_t adversarial_refusals = 0;

    // 1. Base Epoch 1 & Epoch 2 batch clearing (`in_carry_upgrade_en = 0`, base pin = ep*32 + 4)
    for (uint64_t ep = 1; ep <= 2; ++ep) {
        dut->in_lot_count = 8;
        dut->in_epoch_id = ep;
        dut->in_validator_votes = 0b0111; // 3 of 4 validators (V0, V1, V2)
        dut->in_carry_upgrade_en = 0;
        dut->in_old_cbdc_total = 1000000ULL;
        dut->in_delta_debit = 50000ULL;
        dut->in_delta_credit = 50000ULL;
        dut->in_seat_cbdc_after = 95000ULL;
        dut->in_seat_want_floor = 75000ULL;
        dut->in_forever_crown_drop_req = 0;
        dut->in_tx_pin_digest = ep * 32ULL + 4ULL;
        dut->eval();

        assert(dut->out_validator_quorum == 3ULL);
        assert(dut->out_vote_count == 3ULL);
        assert(dut->out_quorum_reached == 1ULL);
        assert(dut->out_protected_welfare_crown == 1000ULL);
        assert(dut->out_settled_cbdc_liquidity == 100000ULL);
        assert(dut->out_batch_settlement_cbdc == 5000ULL);
        assert(dut->out_finality_commit_tag == ep * 64ULL + 3ULL);
        assert(dut->out_carry_pin_digest == ep * 32ULL + 4ULL);
        assert(dut->out_pin_fresh_ok == 1ULL);
        assert(dut->out_epoch_monotone_ok == 1ULL);
        assert(dut->out_new_cbdc_total == 1000000ULL);
        assert(dut->out_turn_admitted == 1ULL);
        tick();
        admitted_batches++;
        assert(dut->out_wal_committed_count == admitted_batches);
        assert(dut->out_last_committed_epoch == ep);
    }

    // 2a. Live K-CARRY Hot-Upgrade at Epoch 3: Stale-Pin Refusal (`100` != upgraded `118`)
    dut->in_lot_count = 8;
    dut->in_epoch_id = 3;
    dut->in_carry_upgrade_en = 1;
    dut->in_validator_votes = 0b1111; // 4 of 4 validators
    dut->in_tx_pin_digest = 100ULL;   // Stale pre-upgrade base pin (3 * 32 + 4 = 100)
    dut->eval();
    assert(dut->out_carry_pin_digest == 118ULL); // (3 * 32 + 6) + 16 = 118
    assert(dut->out_pin_fresh_ok == 0ULL);
    assert(dut->out_turn_admitted == 0ULL);
    tick();
    adversarial_refusals++;
    assert(dut->out_wal_committed_count == admitted_batches);
    assert(dut->out_last_committed_epoch == 2ULL);

    // 2b. Live K-CARRY Hot-Upgrade at Epoch 3: Fresh-Pin Admission (`118`)
    dut->in_tx_pin_digest = 118ULL;
    dut->eval();
    assert(dut->out_settled_cbdc_liquidity == 125000ULL);
    assert(dut->out_batch_settlement_cbdc == 5000ULL); // drexSettlementAt8 = 5000
    assert(dut->out_finality_commit_tag == 227ULL);    // drexFinalityTagAt3 = 227
    assert(dut->out_pin_fresh_ok == 1ULL);
    assert(dut->out_epoch_monotone_ok == 1ULL);
    assert(dut->out_turn_admitted == 1ULL);
    tick();
    admitted_batches++;
    assert(dut->out_wal_committed_count == admitted_batches);
    assert(dut->out_last_committed_epoch == 3ULL);

    // 3. Validator Crash / Durable WAL Replay Test:
    // Re-presenting already-committed Epoch 3 (and older Epoch 2) must achieve ZERO double-execution!
    dut->in_epoch_id = 3;
    dut->in_tx_pin_digest = 118ULL;
    dut->eval();
    assert(dut->out_epoch_monotone_ok == 0ULL);
    assert(dut->out_turn_admitted == 0ULL);
    tick();
    adversarial_refusals++;
    assert(dut->out_wal_committed_count == admitted_batches);
    assert(dut->out_last_committed_epoch == 3ULL);

    dut->in_epoch_id = 2;
    dut->in_tx_pin_digest = 86ULL;
    dut->eval();
    assert(dut->out_epoch_monotone_ok == 0ULL);
    assert(dut->out_turn_admitted == 0ULL);
    tick();
    adversarial_refusals++;
    assert(dut->out_wal_committed_count == admitted_batches);

    // 4. Adversarial Fail-Closed Refusal Suite at Epoch 5 (`sovereignDigestAt5 = 182`)
    dut->in_lot_count = 12;
    dut->in_epoch_id = 5;
    dut->in_tx_pin_digest = 182ULL;

    // 4a. Under-quorum (only 2 of 4 validators vote)
    dut->in_validator_votes = 0b0011;
    dut->eval();
    assert(dut->out_quorum_reached == 0ULL);
    assert(dut->out_turn_admitted == 0ULL);
    tick();
    adversarial_refusals++;
    dut->in_validator_votes = 0b1111;

    // 4b. Unreported state-balance inflation (credit != debit)
    dut->in_delta_debit = 50000ULL;
    dut->in_delta_credit = 1000000ULL;
    dut->eval();
    assert(dut->out_turn_admitted == 0ULL);
    assert(dut->out_new_cbdc_total == 1000000ULL);
    tick();
    adversarial_refusals++;
    dut->in_delta_credit = 50000ULL;

    // 4c. Agoric/Zoe offer-safety violation (seat balance < want floor)
    dut->in_seat_cbdc_after = 60000ULL;
    dut->in_seat_want_floor = 75000ULL;
    dut->eval();
    assert(dut->out_turn_admitted == 0ULL);
    tick();
    adversarial_refusals++;
    dut->in_seat_cbdc_after = 95000ULL;

    // 4d. Attempted drop of "forever" welfare-credit crown cell
    dut->in_forever_crown_drop_req = 1;
    dut->eval();
    assert(dut->out_turn_admitted == 0ULL);
    tick();
    adversarial_refusals++;
    dut->in_forever_crown_drop_req = 0;

    // 4e. Admit valid Epoch 5 after all adversarial attempts were rejected
    dut->eval();
    assert(dut->out_batch_settlement_cbdc == 7000ULL); // sovereignClearedAt12 = 7000
    assert(dut->out_carry_pin_digest == 182ULL);       // sovereignDigestAt5 = 182
    assert(dut->out_turn_admitted == 1ULL);
    tick();
    admitted_batches++;
    assert(dut->out_wal_committed_count == admitted_batches);
    assert(dut->out_last_committed_epoch == 5ULL);

    // 5. Sweep 32 consecutive strictly monotone epochs (6..37) of valid 3-of-4 batch clears
    for (uint64_t ep = 6; ep <= 37; ++ep) {
        dut->in_epoch_id = ep;
        dut->in_lot_count = ep * 2ULL;
        dut->in_validator_votes = (ep % 2 == 0) ? 0b1110 : 0b1011;
        dut->in_delta_debit = ep * 1000ULL;
        dut->in_delta_credit = ep * 1000ULL;
        dut->in_tx_pin_digest = (ep * 32ULL + 6ULL) + 16ULL;
        dut->eval();
        assert(dut->out_turn_admitted == 1ULL);
        assert(dut->out_new_cbdc_total == 1000000ULL);
        assert(dut->out_protected_welfare_crown == 1000ULL);
        tick();
        admitted_batches++;
        assert(dut->out_wal_committed_count == admitted_batches);
        assert(dut->out_last_committed_epoch == ep);
    }

    tfp->close();
    delete tfp;
    delete dut;

    std::cout << "[sovereign-drex] Verilator 4-Validator DReX + K-CARRY + WAL Anti-Replay PASSED\n"
              << "  validators=4 quorum=3 admitted_batches=" << admitted_batches
              << " adversarial_refusals=" << adversarial_refusals
              << " welfare_crown=1000 cbdc_supply_conserved=1000000\n";
    return 0;
}
