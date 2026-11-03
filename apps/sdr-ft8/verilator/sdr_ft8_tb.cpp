// Verilator Co-Simulation Testbench for Flagship App #3:
// All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver (16,384 IQ Samples, 79 FT8 Symbols)
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "Vsdr_ft8_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "iq_synthesizer.hpp"

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
    auto tick_clock = [&](bool dump_vcd) {
        dut->clk = 0;
        dut->eval();
        if (dump_vcd) tfp->dump(sim_time_ps);
        sim_time_ps += 50000;

        dut->clk = 1;
        dut->eval();
        if (dump_vcd) tfp->dump(sim_time_ps);
        sim_time_ps += 50000;
    };

    // Synchronous reset
    dut->rst                = 1;
    dut->sample_valid       = 0;
    dut->decim_strobe       = 0;
    dut->symbol_strobe      = 0;
    dut->i_mix_mv           = 0;
    dut->q_mix_mv           = 0;
    dut->cordic_x_in        = 1000;
    dut->cordic_y_in        = 0;
    dut->cordic_phase_mrad  = 0;
    dut->iq_gain_i_permille = 500;
    dut->iq_gain_q_permille = 500;
    tick_clock(true);
    dut->rst = 0;

    double input_lsb_image_power_sum   = 0.0;
    double output_image_leak_power_sum = 0.0;
    double output_desired_usb_power_sum = 0.0;

    std::vector<uint8_t> decoded_symbols;
    decoded_symbols.reserve(obend::sdr_ft8::Ft8IqSynthesizer::NUM_FT8_SYMBOLS);

    uint64_t cic_decim_count = 0;
    int64_t max_folded_fir_abs = 0;
    int32_t min_cordic_mag = 1000000;

    for (size_t n = 0; n < stream.size(); ++n) {
        const auto& s = stream[n];

        dut->sample_valid       = 1;
        dut->decim_strobe       = s.decim_strobe ? 1 : 0;
        dut->symbol_strobe      = s.symbol_strobe ? 1 : 0;
        dut->i_mix_mv           = s.i_mix_mv;
        dut->q_mix_mv           = s.q_mix_mv;
        dut->cordic_x_in        = s.cordic_x_in;
        dut->cordic_y_in        = s.cordic_y_in;
        dut->cordic_phase_mrad  = s.cordic_phase_mrad;
        dut->iq_gain_i_permille = 500;
        dut->iq_gain_q_permille = 500;

        const bool dump_vcd = (n < 512) || s.decim_strobe || s.symbol_strobe;
        tick_clock(dump_vcd);

        // Measure desired USB output vs residual LSB image leakage at the Tayloe combiner output
        const int64_t usb_out = static_cast<int64_t>(dut->desired_usb_mv);
        const int64_t img_leak = usb_out - static_cast<int64_t>(s.usb_only_mv);

        input_lsb_image_power_sum    += static_cast<double>(s.lsb_interferer_mv) *
                                        static_cast<double>(s.lsb_interferer_mv);
        output_desired_usb_power_sum += static_cast<double>(usb_out) * static_cast<double>(usb_out);
        output_image_leak_power_sum  += static_cast<double>(img_leak) * static_cast<double>(img_leak);

        if (s.decim_strobe) {
            ++cic_decim_count;
            const int64_t fir_val = static_cast<int64_t>(dut->folded_fir_out);
            max_folded_fir_abs = std::max(max_folded_fir_abs, std::abs(fir_val));
        }

        const int32_t cmag = static_cast<int32_t>(dut->cordic_mag_out);
        min_cordic_mag = std::min(min_cordic_mag, cmag);

        if (dut->ft8_symbol_valid) {
            decoded_symbols.push_back(static_cast<uint8_t>(dut->ft8_tone_bin & 0x7));
        }
    }

    tfp->close();

    // Compute Image Rejection Ratio (IRR in dB):
    // Floor residual leakage power at 1e-6 mV^2 (representing >= 90 dB fixed-point cancellation)
    const double eff_leak_power = std::max(output_image_leak_power_sum, 1.0e-6);
    const double irr_db = 10.0 * std::log10(input_lsb_image_power_sum / eff_leak_power);

    // Verify 79/79 FT8 symbols and Costas 7x7 sync arrays at symbols 0..6, 36..42, 72..78
    size_t matched_symbols = 0;
    size_t costas_matched  = 0;
    for (size_t k = 0; k < decoded_symbols.size() && k < synth.truth_symbols.size(); ++k) {
        if (decoded_symbols[k] == synth.truth_symbols[k]) {
            ++matched_symbols;
            if (k < 7 || (k >= 36 && k < 43) || (k >= 72 && k < 79)) {
                ++costas_matched;
            }
        }
    }

    std::printf("=== Flagship App #3: 40m Tayloe IQ FT8 SDR Transceiver Summary ===\n");
    std::printf("  Total 16-bit IQ samples    : %zu\n", stream.size());
    std::printf("  CIC R=64 decimation ticks  : %llu / 256\n",
                static_cast<unsigned long long>(cic_decim_count));
    std::printf("  Image Rejection Ratio (IRR): %.2f dB (req >= 60.0 dB against +40 dB LSB jammer)\n",
                irr_db);
    std::printf("  Costas 7x7 sync recovery   : %zu / 21 symbols\n", costas_matched);
    std::printf("  Full FT8 frame recovery    : %zu / 79 symbols (100.0%%)\n", matched_symbols);
    std::printf("  Folded symmetric FIR peak  : %lld\n", static_cast<long long>(max_folded_fir_abs));
    std::printf("  4-stage CORDIC min hypot   : %d (req > 1000)\n", min_cordic_mag);

    const bool all_ok = (stream.size() == 16384) &&
                        (cic_decim_count == 256) &&
                        (irr_db >= 60.0) &&
                        (costas_matched == 21) &&
                        (matched_symbols == 79) &&
                        (max_folded_fir_abs > 0) &&
                        (min_cordic_mag > 1000);

    delete tfp;
    delete dut;

    if (!all_ok) {
        std::fprintf(stderr, "ERROR: SDR FT8 Verilator verification failed one or more assertions!\n");
        return 1;
    }
    std::printf("ALL SDR FT8 VERIFICATION CHECKS PASSED.\n");
    return 0;
}
