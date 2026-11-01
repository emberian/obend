#include "Vtb_top.h"
#include "verilated.h"
#include <cassert>
#include <cstdio>
#include <vector>

static void tick(Vtb_top* top) {
  top->clk = 0;
  top->eval();
  top->clk = 1;
  top->eval();
}

static uint64_t hw_mix64(uint64_t l, uint64_t r) {
  uint64_t s = l + (r * 0x9E3779B97F4A7C15ULL);
  return s ^ (s >> 17);
}

int main(int argc, char** argv) {
  Verilated::commandArgs(argc, argv);
  // Randomize all unreset flip-flops and SRAM words to adversarial garbage!
  Verilated::randReset(2);
  Vtb_top* top = new Vtb_top;

  // Reset pulse (1 cycle)
  top->rst_n = 0;
  top->dsp_a = 0; top->dsp_b = 0; top->dsp_c = 0;
  top->ram_rd_en = 0; top->ram_rd_addr = 0;
  top->ram_wr_en = 0; top->ram_wr_addr = 0; top->ram_wr_data = 0;
  top->s_tvalid = 0; top->s_tdata = 0; top->m_tready = 0;
  top->efpga_a = 0; top->efpga_b = 0;
  top->rev_x = 0; top->rev_base = 0;
  top->led_row_valid = 0; top->led_row_is_close = 0;
  top->led_row_doc_id = 0; top->led_row_period = 0;
  top->led_row_debit = 0; top->led_row_credit = 0;
  top->mesh_cfg_wr_en = 0; top->mesh_cfg_lock_cmd = 0;
  top->mesh_cfg_tile_id = 0; top->mesh_cfg_mux_a = 0;
  top->mesh_cfg_mux_b = 0; top->mesh_cfg_alu_op = 0;
  top->mesh_cfg_imm = 0; top->mesh_in_00 = 0;
  top->mrk_dated_root = 0; top->mrk_leaf_pos = 0;
  top->mrk_leaf_val = 0; top->mrk_sib_0 = 0;
  top->mrk_sib_1 = 0; top->mrk_law_ok = 0;
  top->deos_cmd_valid = 0; top->deos_cmd_op = 0;
  top->deos_cmd_arg = 0; top->deos_has_cred = 0;
  tick(top);
  top->rst_n = 1;
  top->eval();

  // Check Cycle 0 after reset: wave chip valid bits must be 0000
  assert(top->slot_valid == 0b0000);
  assert(top->csr_afi_digest == 0xCAFEBABEULL);

  // Feed DSP inputs at cycle 0: a0 = 7, b0 = 9
  top->dsp_a = 7; top->dsp_b = 9; top->dsp_c = 999;
  tick(top); // Cycle 1

  // Wave 1: slot 0 ("a" = 42) becomes valid! slots 1,2,3 still invalid.
  assert(top->slot_valid == 0b0001);
  assert(top->slot_val_0 == 42);

  // Feed DSP c1 = 100 at cycle 1 (so a0 * b0 + c1 = 7 * 9 + 100 = 163 after 4 cycles!)
  top->dsp_a = 0; top->dsp_b = 0; top->dsp_c = 100;
  tick(top); // Cycle 2

  // Wave 2: slot 1 ("b" = self.a = 42) becomes valid!
  assert(top->slot_valid == 0b0011);
  assert(top->slot_val_0 == 42);
  assert(top->slot_val_1 == 42);

  top->dsp_c = 0;
  tick(top); // Cycle 3

  // Wave 3: slot 2 ("c" = self.b = 42) becomes valid! slot 3 ("bad" = self.bad) stays 0!
  assert(top->slot_valid == 0b0111);
  assert(top->slot_val_2 == 42);

  tick(top); // Cycle 4
  // DSP MAC 4-cycle pipeline output ready: 7 * 9 + 100 = 163!
  uint64_t dsp_p_cyc4 = top->dsp_p;
  assert(dsp_p_cyc4 == 163);
  assert(top->slot_valid == 0b0111); // "bad" still 0!

  // Wait remaining 12 cycles for the 16-word URAM Boot Zero-Sweep FSM to finish
  for (int i = 4; i < 16; i++) {
    assert(top->ram_boot_done == 0);
    tick(top);
    assert(top->slot_valid == 0b0111); // "bad" never becomes valid!
  }
  assert(top->ram_boot_done == 1);

  // Verify every URAM address 0..15 was swept to 0 despite Verilated::randReset(2) garbage!
  for (int addr = 0; addr < 16; addr++) {
    top->ram_rd_en = 1;
    top->ram_rd_addr = addr;
    top->ram_wr_en = 0;
    tick(top);
    assert(top->ram_rd_data == 0ULL);
  }

  // Test simultaneous same-address Read-During-Write (RDW) collision & RAW forwarding bypass!
  top->ram_rd_en = 1;
  top->ram_rd_addr = 5;
  top->ram_wr_en = 1;
  top->ram_wr_addr = 5;
  top->ram_wr_data = 0x123456789ABCDEF0ULL;
  tick(top);
  // Next cycle must return the exact newly written value via the bypass mux!
  assert(top->ram_rd_data == 0x123456789ABCDEF0ULL);

  // And reading address 5 again on the next cycle (with wr_en = 0) reads it from the physical RAM array!
  top->ram_wr_en = 0;
  top->ram_rd_en = 1;
  top->ram_rd_addr = 5;
  tick(top);
  assert(top->ram_rd_data == 0x123456789ABCDEF0ULL);

  // Test 2-slot AXI4-Stream Skid Buffer under adversarial backpressure stalls
  std::vector<uint64_t> sent, rcvd;
  uint64_t next_val = 1000;
  for (int cyc = 0; cyc < 40; cyc++) {
    bool s_val = (cyc < 25) && ((cyc % 3) != 2);
    bool m_rdy = ((cyc % 4) == 0) || (cyc > 30);
    top->s_tvalid = s_val;
    top->s_tdata  = next_val;
    top->m_tready = m_rdy;
    top->eval();
    if (top->s_tvalid && top->s_tready) {
      sent.push_back(next_val++);
    }
    if (top->m_tvalid && top->m_tready) {
      rcvd.push_back(top->m_tdata);
    }
    tick(top);
  }
  assert(sent == rcvd && !sent.empty());

  // 5. Test 64-bit eFPGA Bitstream-Configured BLE Adder (FABulous / fabublox tile model)
  uint64_t test_pairs[5][2] = {
    {0ULL, 0ULL},
    {0xFFFFFFFFFFFFFFFFULL, 1ULL},
    {0x123456789ABCDEF0ULL, 0x0FEDCBA987654321ULL},
    {42ULL, 999999999ULL},
    {0x8000000000000000ULL, 0x8000000000000000ULL}
  };
  for (int i = 0; i < 5; i++) {
    top->efpga_a = test_pairs[i][0];
    top->efpga_b = test_pairs[i][1];
    top->eval();
    assert(top->efpga_sum == (test_pairs[i][0] + test_pairs[i][1]));
  }

  // 6. Test ReviewMember.obend 2-stage Hardware Pipeline (twice(x) == x + (base + base))
  top->rev_x = 1000ULL;
  top->rev_base = 333ULL;
  tick(top); // Stage 1 latches bump_s1 = 1333
  tick(top); // Stage 2 latches twice_out = 1666 and claim_repeated_ok = 1
  assert(top->rev_twice == 1666ULL);
  assert(top->rev_claim_ok == 1);

  // 7. Test Streaming Hardware Ledger Co-Processor (Obend/Ledger/Register.lean in Silicon)
  assert(top->led_boot_done == 1);
  assert(top->led_closed_through == 0ULL);
  assert(top->led_total_debits == 0ULL);
  assert(top->led_total_credits == 0ULL);

  // Row A: Valid post (doc_id=7, period=1, debit=500, credit=500) -> ACCEPTED
  top->led_row_valid = 1;
  top->led_row_is_close = 0;
  top->led_row_doc_id = 7;
  top->led_row_period = 1;
  top->led_row_debit = 500;
  top->led_row_credit = 500;
  top->eval();
  assert(top->led_row_accepted == 1);
  assert(top->led_refusal_code == 0);
  tick(top);
  assert(top->led_total_debits == 500ULL);
  assert(top->led_total_credits == 500ULL);

  // Row B: Duplicate doc_id=7 (period=1, debit=200, credit=200) -> REFUSED (3 = postedTwice)
  top->led_row_doc_id = 7;
  top->led_row_period = 1;
  top->led_row_debit = 200;
  top->led_row_credit = 200;
  top->eval();
  assert(top->led_row_accepted == 0);
  assert(top->led_refusal_code == 3);
  tick(top);
  assert(top->led_total_debits == 500ULL);

  // Row C: Unbalanced post (doc_id=8, period=1, debit=250, credit=999) -> REFUSED (2 = unbalanced)
  top->led_row_doc_id = 8;
  top->led_row_period = 1;
  top->led_row_debit = 250;
  top->led_row_credit = 999;
  top->eval();
  assert(top->led_row_accepted == 0);
  assert(top->led_refusal_code == 2);
  tick(top);
  assert(top->led_total_debits == 500ULL);

  // Row D: Close period 2 -> ACCEPTED (closed_through becomes 2)
  top->led_row_is_close = 1;
  top->led_row_period = 2;
  top->eval();
  assert(top->led_row_accepted == 1);
  tick(top);
  assert(top->led_closed_through == 2ULL);

  // Row E: Post into closed period 2 (doc_id=9, period=2, debit=100, credit=100) -> REFUSED (1 = closedPeriod)
  top->led_row_is_close = 0;
  top->led_row_doc_id = 9;
  top->led_row_period = 2;
  top->led_row_debit = 100;
  top->led_row_credit = 100;
  top->eval();
  assert(top->led_row_accepted == 0);
  assert(top->led_refusal_code == 1);
  tick(top);
  assert(top->led_total_debits == 500ULL);
  assert(top->led_total_credits == 500ULL);
  top->led_row_valid = 0;

  // 8. Test 2x2 eFPGA Mesh + Frame Loader (TwiceReview.obend synthesized bitstream)
  assert(top->mesh_cfg_locked == 0);
  // Frame 0: Tile 00 (NW) -> muxA = 0 (localIn), aluOp = 1 (addImm), imm = 1
  top->mesh_cfg_wr_en = 1; top->mesh_cfg_lock_cmd = 0;
  top->mesh_cfg_tile_id = 0; top->mesh_cfg_mux_a = 0; top->mesh_cfg_mux_b = 0;
  top->mesh_cfg_alu_op = 1; top->mesh_cfg_imm = 1ULL;
  tick(top);
  // Frame 1: Tile 10 (NE) -> muxA = 4 (westIn), aluOp = 1 (addImm), imm = 1
  top->mesh_cfg_tile_id = 1; top->mesh_cfg_mux_a = 4;
  tick(top);
  // Frame 2: Tile 01 (SW) -> muxA = 2 (eastIn), aluOp = 1 (addImm), imm = 1
  top->mesh_cfg_tile_id = 2; top->mesh_cfg_mux_a = 2;
  tick(top);
  // Frame 3: Tile 11 (SE) -> muxA = 1 (northIn), aluOp = 1 (addImm), imm = 1 + LOCK!
  top->mesh_cfg_tile_id = 3; top->mesh_cfg_mux_a = 1; top->mesh_cfg_lock_cmd = 1;
  tick(top);
  top->mesh_cfg_wr_en = 0; top->mesh_cfg_lock_cmd = 0;
  assert(top->mesh_cfg_locked == 1);

  // Verify TwiceReview.twiceOfThree() == 7
  top->mesh_in_00 = 3ULL;
  top->eval();
  uint64_t twice_of_three = top->mesh_out_01;
  assert(twice_of_three == 7ULL);

  // Verify adversarial config write after cfg_locked == 1 is ignored!
  top->mesh_cfg_wr_en = 1; top->mesh_cfg_tile_id = 0; top->mesh_cfg_imm = 999999ULL;
  tick(top);
  top->mesh_cfg_wr_en = 0;
  top->mesh_in_00 = 3ULL;
  top->eval();
  assert(top->mesh_out_01 == 7ULL);

  // 9. Test Hardware Merkle-View Receipt Verifier Engine (Obend/Receipt/Merkle.lean)
  uint64_t leaves[4] = {101ULL, 202ULL, 303ULL, 404ULL};
  uint64_t h01 = hw_mix64(leaves[0], leaves[1]);
  uint64_t h23 = hw_mix64(leaves[2], leaves[3]);
  uint64_t root4 = hw_mix64(h01, h23);

  top->mrk_dated_root = root4;
  top->mrk_law_ok = 1;
  for (int pos = 0; pos < 4; pos++) {
    top->mrk_leaf_pos = pos;
    top->mrk_leaf_val = leaves[pos];
    top->mrk_sib_0 = (pos % 2 == 0) ? leaves[pos + 1] : leaves[pos - 1];
    top->mrk_sib_1 = (pos < 2) ? h23 : h01;
    top->eval();
    assert(top->mrk_climbed_root == root4);
    assert(top->mrk_accepted == 1);

    // Tamper with leaf value -> must be rejected!
    top->mrk_leaf_val = leaves[pos] + 1;
    top->eval();
    assert(top->mrk_accepted == 0);
  }

  // 10. Test DeosCounter.obend + Vault.Law Capability-Guarded Register Bank
  // a) inc(50) -> count = 50, accepted = 1
  top->deos_cmd_valid = 1; top->deos_cmd_op = 0; top->deos_cmd_arg = 50ULL; top->deos_has_cred = 0;
  tick(top);
  assert(top->deos_count == 50ULL && top->deos_accepted == 1);

  // b) dec(15) -> count = 35, accepted = 1
  top->deos_cmd_op = 1; top->deos_cmd_arg = 15ULL;
  tick(top);
  assert(top->deos_count == 35ULL && top->deos_accepted == 1);

  // c) reset WITHOUT proof credential -> REFUSED, count stays 35!
  top->deos_cmd_op = 2; top->deos_has_cred = 0;
  tick(top);
  assert(top->deos_count == 35ULL && top->deos_accepted == 0);

  // d) writeTag(0xBEEF) first time -> ACCEPTED (writeOnce initializes tag)
  top->deos_cmd_op = 3; top->deos_cmd_arg = 0xBEEFULL;
  tick(top);
  assert(top->deos_cfg_tag == 0xBEEFULL && top->deos_accepted == 1);

  // e) writeTag(0xDEAD) second time -> REFUSED by Vault.Law writeOnce! tag stays 0xBEEF!
  top->deos_cmd_op = 3; top->deos_cmd_arg = 0xDEADULL;
  tick(top);
  assert(top->deos_cfg_tag == 0xBEEFULL && top->deos_accepted == 0);

  // f) reset WITH proof credential -> ACCEPTED, count becomes 0!
  top->deos_cmd_op = 2; top->deos_has_cred = 1;
  tick(top);
  assert(top->deos_count == 0ULL && top->deos_accepted == 1);

  printf("ALL 10 VERILATOR 5.050 SILICON, eFPGA FABRIC & VAULT/MERKLE SUITES PASSED!\n");
  printf("  1. Wave Chip (evalDemand): slot_valid=0b%x, a=%llu, b=%llu, c=%llu (divergent 'bad' valid=0)\n",
         top->slot_valid, (unsigned long long)top->slot_val_0,
         (unsigned long long)top->slot_val_1, (unsigned long long)top->slot_val_2);
  printf("  2. DSP48E2/58 4-Stage Reset-Free MAC: 7 * 9 + 100 = %llu\n", (unsigned long long)dsp_p_cyc4);
  printf("  3. URAM288 Boot Zero-Sweep + RAW Collision Bypass: 16/16 words zeroed, RDW bypass=0x%llx\n",
         (unsigned long long)top->ram_rd_data);
  printf("  4. AXI4-Stream 2-Slot Skid Buffer: %zu/%zu words transferred losslessly under stalls\n",
         rcvd.size(), sent.size());
  printf("  5. eFPGA (FABulous/fabublox) 64-Tile Bitstream Adder: 5/5 64-bit vectors exact (LUT2+CARRY mux)\n");
  printf("  6. ReviewMember.obend 2-Stage Silicon Pipeline: twice(1000,333)=%llu, claim_repeated_ok=%d\n",
         (unsigned long long)top->rev_twice, top->rev_claim_ok);
  printf("  7. Streaming Ledger Co-Processor: debits=%llu, credits=%llu, closedThrough=%llu, refusals={1,2,3} exact\n",
         (unsigned long long)top->led_total_debits, (unsigned long long)top->led_total_credits,
         (unsigned long long)top->led_closed_through);
  printf("  8. 2x2 eFPGA Mesh + Frame Loader (TwiceReview.obend): twiceOfThree=%llu, post-lock immutable=PASS\n",
         (unsigned long long)twice_of_three);
  printf("  9. Merkle-View Receipt Verifier (Obend/Receipt/Merkle.lean): 4/4 openings accepted, 4/4 tampered rejected\n");
  printf(" 10. DeosCounter.obend + Vault.Law Guard: uncred reset=REFUSED(count=35), writeOnce=0x%llx, cred reset=%llu\n",
         (unsigned long long)top->deos_cfg_tag, (unsigned long long)top->deos_count);
  delete top;
  return 0;
}
