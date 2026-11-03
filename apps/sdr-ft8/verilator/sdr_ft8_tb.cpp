// Verilator Co-Simulation Testbench for Flagship App #3:
// All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver (16,384 IQ Samples, 79 FT8 Symbols)
// Verifies BOTH:
//   1. Negative Pole (Uncalibrated Tayloe I/Q mismatch: 500 vs 450 permille):
//      +40 dB LSB image jammer leaks into baseband (IRR ~ 20 dB < 30 dB) and corrupts
//      closed-loop CORDIC FT8 symbol recovery (< 25 / 79 symbols), proving Tayloe image
//      cancellation, folded FIR, and 4-stage CORDIC atan2 are genuinely in the demod loop!
//   2. Positive Pole (Calibrated 4-Phase Tayloe Override: 500 vs 500 permille):
//      >= 60 dB IRR against +40 dB LSB jammer, 21 / 21 Costas 7x7 sync symbols, and
//      79 / 79 (100.0%) full FT8 frame symbol recovery!
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "Vsdr_ft8_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "iq_synthesizer.hpp"

struct SdrRunResult {
    double               irr_db            = 0.0;
    uint64_t             cic_decim_count   = 0;
    int64_t              max_folded_fir    = 0;
    int32_t              min_cordic_mag    = 100000000;
    size_t               costas_matched    = 0;
    size_t               matched_symbols   = 0;
    std::vector<uint8_t> decoded_symbols{};
};

static SdrRunResult run_sdr_pass(Vsdr_ft8_top* dut,
                                 VerilatedVcdC* tfp,
                                 uint64_t& sim_time_ps,
                                 const obend::sdr_ft8::Ft8IqSynthesizer& synth,
                                 const std::vector<obend::sdr_ft8::SdrIqSample>& stream,
                                 int32_t gain_i_permille,
                                 int32_t gain_q_permille,
                                 bool record_vcd) {
    auto tick_clock = [&](bool dump_vcd) {
        dut->clk = 0;
        dut->eval();
        if (record_vcd && dump_vcd && tfp) tfp->dump(sim_time_ps);
        sim_time_ps += 50000;

        dut->clk = 1;
        dut->eval();
        if (record_vcd && dump_vcd && tfp) tfp->dump(sim_time_ps);
        sim_time_ps += 50000;
    };

    // Synchronous reset
    dut->rst                = 1;
    dut->sample_valid       = 0;
    dut->decim_strobe       = 0;
    dut->phase_ref_strobe   = 0;
    dut->symbol_strobe      = 0;
    dut->i_mix_mv           = 0;
    dut->q_mix_mv           = 0;
    dut->i_quad_mv          = 0;
    dut->q_quad_mv          = 0;
    dut->iq_gain_i_permille = gain_i_permille;
    dut->iq_gain_q_permille = gain_q_permille;
    tick_clock(true);
    dut->rst = 0;

    SdrRunResult res{};
    res.decoded_symbols.reserve(obend::sdr_ft8::Ft8IqSynthesizer::NUM_FT8_SYMBOLS);

    double input_lsb_image_power_sum   = 0.0;
    double output_image_leak_power_sum = 0.0;

    for (size_t n = 0; n < stream.size(); ++n) {
        const auto& s = stream[n];

        dut->sample_valid       = 1;
        dut->decim_strobe       = s.decim_strobe ? 1 : 0;
        dut->phase_ref_strobe   = s.phase_ref_strobe ? 1 : 0;
        dut->symbol_strobe      = s.symbol_strobe ? 1 : 0;
        dut->i_mix_mv           = s.i_mix_mv;
        dut->q_mix_mv           = s.q_mix_mv;
        dut->i_quad_mv          = s.i_quad_mv;
        dut->q_quad_mv          = s.q_quad_mv;
        dut->iq_gain_i_permille = gain_i_permille;
        dut->iq_gain_q_permille = gain_q_permille;

        const bool dump_vcd = (n < 512) || s.decim_strobe || s.phase_ref_strobe || s.symbol_strobe;
        tick_clock(dump_vcd);

        // Expected desired-only USB output under current gain trim:
        // ((gain_i + gain_q) / 1000.0) * s.usb_only_mv
        const double gain_sum_ratio = static_cast<double>(gain_i_permille + gain_q_permille) / 1000.0;
        const double expected_usb_out = gain_sum_ratio * static_cast<double>(s.usb_only_mv);
        const double actual_usb_out   = static_cast<double>(static_cast<int64_t>(dut->desired_usb_mv));
        const double img_leak         = actual_usb_out - expected_usb_out;

        // Input LSB jammer reference in combiner scale (2 * lsb_interferer_mv)
        const double ref_lsb_in = 2.0 * static_cast<double>(s.lsb_interferer_mv);
        input_lsb_image_power_sum  += ref_lsb_in * ref_lsb_in;
        output_image_leak_power_sum += img_leak * img_leak;

        if (s.decim_strobe) {
            ++res.cic_decim_count;
            const int64_t fir_val = static_cast<int64_t>(dut->folded_fir_out);
            res.max_folded_fir = std::max(res.max_folded_fir, std::abs(fir_val));
        }

        // Track minimum 4-stage CORDIC envelope magnitude once the 4-tap baseband FIR pipeline fills (n >= 4)
        if (n >= 4 && n < obend::sdr_ft8::Ft8IqSynthesizer::PREAMBLE_SAMPLES +
                          obend::sdr_ft8::Ft8IqSynthesizer::NUM_FT8_SYMBOLS *
                          obend::sdr_ft8::Ft8IqSynthesizer::SAMPLES_PER_SYMBOL) {
            const int32_t cmag = static_cast<int32_t>(dut->cordic_mag_out);
            res.min_cordic_mag = std::min(res.min_cordic_mag, cmag);
        }

        if (dut->ft8_symbol_valid) {
            res.decoded_symbols.push_back(static_cast<uint8_t>(dut->ft8_tone_bin & 0x7));
        }
    }

    const double eff_leak_power = std::max(output_image_leak_power_sum, 1.0e-6);
    res.irr_db = 10.0 * std::log10(input_lsb_image_power_sum / eff_leak_power);

    for (size_t k = 0; k < res.decoded_symbols.size() && k < synth.truth_symbols.size(); ++k) {
        if (res.decoded_symbols[k] == synth.truth_symbols[k]) {
            ++res.matched_symbols;
            if (k < 7 || (k >= 36 && k < 43) || (k >= 72 && k < 79)) {
                ++res.costas_matched;
            }
        }
    }
    return res;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    auto* dut = new Vsdr_ft8_top;
    auto* tfp = new VerilatedVcdC;
    dut->trace(tfp, 99);
    tfp->open("sdr_ft8_trace.vcd");

    obend::sdr_ft8::Ft8IqSynthesizer synth;
    const auto stream = synth.generate_stream();

    uint64_t sim_time_ps = 0;

    // Pass 1 (Negative Pole): Uncalibrated 10% Tayloe I/Q mismatch (500 vs 450 permille)
    const SdrRunResult uncal = run_sdr_pass(dut, nullptr, sim_time_ps, synth, stream, 500, 450, false);

    // Reset VCD timestamp and run Pass 2 (Positive Pole): Calibrated Tayloe (500 vs 500 permille)
    sim_time_ps = 0;
    const SdrRunResult cal = run_sdr_pass(dut, tfp, sim_time_ps, synth, stream, 500, 500, true);

    tfp->close();

    std::printf("=== Flagship App #3: 40m Tayloe IQ FT8 SDR Transceiver Summary ===\n");
    std::printf("  Total 16-bit IQ samples    : %zu\n", stream.size());
    std::printf("  CIC R=64 decimation ticks  : %llu / 256\n",
                static_cast<unsigned long long>(cal.cic_decim_count));
    std::printf("  Uncalibrated (500/450) IRR : %.2f dB (< 30.0 dB), FT8 symbols = %zu / 79 (jammed)\n",
                uncal.irr_db, uncal.matched_symbols);
    std::printf("  Calibrated   (500/500) IRR : %.2f dB (req >= 60.0 dB against +40 dB LSB jammer)\n",
                cal.irr_db);
    std::printf("  Costas 7x7 sync recovery   : %zu / 21 symbols\n", cal.costas_matched);
    std::printf("  Full FT8 frame recovery    : %zu / 79 symbols (100.0%%)\n", cal.matched_symbols);
    std::printf("  Folded symmetric FIR peak  : %lld\n", static_cast<long long>(cal.max_folded_fir));
    std::printf("  4-stage CORDIC min hypot   : %d (req > 1000)\n", cal.min_cordic_mag);

    const bool uncal_corrupted_ok = (uncal.irr_db < 30.0) && (uncal.matched_symbols < 25);
    const bool all_ok = (stream.size() == 16384) &&
                        (cal.cic_decim_count == 256) &&
                        uncal_corrupted_ok &&
                        (cal.irr_db >= 60.0) &&
                        (cal.costas_matched == 21) &&
                        (cal.matched_symbols == 79) &&
                        (cal.max_folded_fir > 0) &&
                        (cal.min_cordic_mag > 1000);

    delete tfp;
    delete dut;

    if (!all_ok) {
        std::fprintf(stderr, "ERROR: SDR FT8 Verilator verification failed one or more assertions!\n");
        return 1;
    }
    std::printf("ALL SDR FT8 VERIFICATION CHECKS PASSED.\n");
    return 0;
}
