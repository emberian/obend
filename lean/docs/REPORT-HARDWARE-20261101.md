# Report: lane Hardware (Antigravity, 2026-11-01)

Verified FPGA (Xilinx UltraScale+ `VU9P` / Versal `VH1582`), eFPGA (FABulous / fabublox), and ASIC
(`7nm` FinFET / `16nm` FinFET / `130nm` SkyWater CMOS) compilation, physical floorplanning, and
silicon-process stack for Objective Bend. Verified in the Lean 4 kernel (`0 sorry`, 6 `#tooth`
kernel mutation checks), **Z3** (`lec_check.smt2` `unsat`, `lec_fabric.smt2` `unsat`), and
**Verilator 5.050** (`tests/run-hardware.py` 14/14 across 15 SystemVerilog modules and 10
cycle-accurate silicon co-simulation suites under `--x-assign unique --x-initial unique` and
`Verilated::randReset(2)`).

## What landed
| item | where | state |
|---|---|---|
| Bit-exact packing & phase erasure (`unpackVal_packVal`, `packVal_unpackVal`, `lowerTy_prototype_erases_cold_spine`, `lowerTy_custody_zero_bits`) | `Obend/Hardware/Silicon.lean` | proved |
| Reset-free silicon macros: `stepDataReg` (`SRLC32E` / `DFFQ`+`ICG`), 2-stage Laguna crossing `pipe2_x_free`, 4-stage `DSP48E2`/`DSP58` MAC `dspMac_latency_4`, `URAM288`/`SRAM` Boot Zero-Sweep `bootSweep_clears_all`, RDW collision bypass `bypassRAM_exact_latest_write`, 2-slot AXI4-Stream skid buffer `stepSkid_wf` & `stepSkid_queue_conserved` | `Obend/Hardware/Silicon.lean` | proved; 3 teeth |
| Multi-SLR & ASIC floorplanning (`Coord`, `checkChannelHop`, `comb_channel_is_tile_local`, `slr_crossing_has_laguna_pair`) | `Obend/Hardware/Silicon.lean` | proved; refusal pole |
| Demand-driven wave chip refinement (`chip_lookup_iff_chase`, `chip_computes_demand`, `chip_never_valid_of_divergent`) | `Obend/Hardware/Silicon.lean` | proved |
| Gate-level BEL mapping (`LUT2`/`LUT6` + `CARRY8`: `lut2_xor_sound`, `lut2_and_sound`, `carryBel_eq_fullAdderSpec`) | `Obend/Hardware/Process.lean` | proved; tooth + Z3 |
| Configurable eFPGA BLE tile & 9-bit bitstream synthesis (`evalEfpgaTile`, `compileTileBitstream`, `efpga_bitstream_fullAdder_sound`, `efpga_bitstream_and_sound`) | `Obend/Hardware/Process.lean` | proved; Verilator |
| Multi-node PVT static timing signoff (`corner7nm_SS` 500 MHz, `corner16nm_SS` 400 MHz, `corner130nm_SS` 200 MHz; `timingSignoff_sound`, `obend_multi_process_timing_signoff`) | `Obend/Hardware/Process.lean` | proved; refusal pole |
| `ReviewMember.obend` 2-stage silicon pipeline (`reviewMember_silicon_claim_holds`) & streaming `Obend.Ledger` co-processor (`hwLedger_period_monotone`, `hwLedger_closed_refused`, `hwLedger_balanced_conserved`, `hwLedger_twice_refused`) | `Obend/Hardware/Process.lean` | proved; Z3 + Verilator |
| Linear & affine wire-fanout typechecker (`linear_or_affine_zero_forks`, `quantityOnce_accepted_and_duplicated_refused`) | `Obend/Hardware/Fabric.lean` | proved; refusal pole |
| 2x2 multi-tile eFPGA mesh + sequential Frame Loader with hardware lock (`frameLoader_immutable_when_locked`, `efpga_mesh_twiceReview_sound`) | `Obend/Hardware/Fabric.lean` | proved; Z3 + Verilator |
| Hardware Merkle-View Receipt verifier (`hwMerkle_climb_complete`) & `DeosCounter.obend` + `Vault.Law` register bank (`deosHw_reset_without_cred_preserves_count`, `deosHw_writeOnce_immutable`) | `Obend/Hardware/Fabric.lean` | proved; tooth + Z3 + Verilator |
| 3-tier Hardware Specialization Slot (`HwCandidate`: `.bitstream` -> `.book` -> `.machine`; `hwBitstream_usable_sound`, `hwMoved_pin_blocks_bitstream`) | `Obend/Hardware/Fabric.lean`, `Teeth/Hardware/SiliconTeeth.lean` | proved; tooth |
| Standalone RTL / XDC / TCL / OpenLane / SMT emitters & 10-suite Verilator + Z3 test runner | `hardware/`, `tests/run-hardware.py` | 14/14 passing |

## Decisions, with critique
- **Control-reset vs. datapath-enable separation**: Only control valid bits (`slot_valid`,
  `m_valid`, `s_valid`, `boot_done`, `cfg_locked`) receive synchronous reset. All wide datapaths
  (`SRLC32E` / `DFFQ`), `DSP48E2` / `DSP58` internal pipeline registers (`A1/B1`, `A2/B2/C2`,
  `MREG/C3`, `PREG`), and `URAM288` / `RAMB36E2` / ASIC `1R1W` SRAM arrays are modeled with
  arbitrary power-on state (`∀ st₀`, `∀ mem₀`) and verified under `Verilated::randReset(2)`.
  Connecting a reset net to FPGA `SRLC32E` or `DSP48E2` inference templates either blocks packing
  or forces high-fanout synchronous reset routing trees that fail timing above 350 MHz.
- **Hardware Boot Zero-Sweep + RAW Collision Bypass for URAM/SRAM**: FPGA `URAM288` and ASIC SRAM
  macros have no reset pin for the memory array and exhibit Read-During-Write (`RDW`) bitline
  contention when simultaneous read and write hit the same address. We wrap every RAM instance in a
  verified `DEPTH`-cycle Boot Zero-Sweep FSM (`bootSweep_clears_all`) and a 1-cycle RAW forwarding
  bypass that suppresses physical `rdEn` on collision (`bypassRAM_exact_latest_write`).
- **3-tier Hardware Specialization Slot (`HwCandidate`)**: Rather than inventing a separate
  invalidation protocol for FPGA/eFPGA bitstreams, `HwCandidate` reuses `Obend.Slot` and
  `Obend.Leaf.Specialize` with candidate order `[.bitstream, .book, .machine]`. `.bitstream`
  requires both `C.closedB` and PVT static timing closure (`checkTimingSignoff corner periodPs
  critPath`). When target timing fails (e.g. 500 MHz on 130nm Sky130 CMOS,
  `sky130_overclock_rejects_bitstream_keeps_book`), `.bitstream` is refused and `.book` is selected;
  when a layer or object pin moves (`override_blocks_bitstream`), both `.bitstream` and `.book` are
  blocked by name and `.machine` is selected.

## What is not proved
- The gate-level BEL (`evalCarryBel`) and 2x2 eFPGA mesh (`evalMesh2x2Snake`) are proved for fixed
  datapath widths (`BitVec 64`) and concrete compositions (`ReviewMember.obend`,
  `TwiceReview.obend`), rather than a general compiler pass from arbitrary recursive `Obend.Core.Term`
  into multi-tile place-and-route graphs.
- Static timing analysis (`checkTimingSignoff`) uses Manhattan tile-hop and carry-chain linear delay
  bounds per PVT corner (`corner7nm_SS`, `corner16nm_SS`, `corner130nm_SS`) rather than parasitic RC
  SPEF extraction after physical routing.
