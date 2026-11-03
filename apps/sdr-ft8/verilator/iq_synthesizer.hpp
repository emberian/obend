// 16,384-Sample 16-Bit Quadrature IQ Stream Synthesizer for Flagship App #3:
// All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver
// Synthesizes:
//   1. A weak desired Upper-Sideband (USB) +1250 Hz 79-symbol 8-FSK FT8 frame
//      (including the three 7-symbol Costas sync arrays {3, 1, 4, 0, 6, 5, 2} at
//      symbols 0..6, 36..42, 72..78 and 58 payload 8-FSK symbols in {0..7}),
//   2. Buried under a +40 dB (100x voltage amplitude!) Lower-Sideband (LSB) image
//      interferer at -1250 Hz.
#pragma once

#include <array>
#include <cmath>
#include <cstdint>
#include <vector>

namespace obend::sdr_ft8 {

struct SdrIqSample {
    int32_t i_mix_mv;          // Tayloe in-phase + 90-deg Hilbert composite channel I
    int32_t q_mix_mv;          // Tayloe quadrature Hilbert composite channel Q
    int32_t usb_only_mv;       // Reference desired USB component (for IRR measurement)
    int32_t lsb_interferer_mv; // Reference +40 dB LSB image interferer component
    int32_t cordic_x_in;       // Baseband CORDIC I phasor
    int32_t cordic_y_in;       // Baseband CORDIC Q phasor
    int32_t cordic_phase_mrad; // Instantaneous unwrapped phase \phi[n] in mrad
    bool    decim_strobe;      // R = 64 CIC decimation strobe
    bool    symbol_strobe;     // FT8 symbol boundary strobe (79 symbols)
    uint8_t expected_tone;     // Ground-truth FT8 8-FSK symbol in {0..7}
};

class Ft8IqSynthesizer {
public:
    static constexpr size_t TOTAL_SAMPLES      = 16384;
    static constexpr size_t NUM_FT8_SYMBOLS    = 79;
    static constexpr size_t SAMPLES_PER_SYMBOL = 204; // 79 * 204 = 16,116 samples (< 16,384)
    static constexpr size_t CIC_DECIM_RATIO    = 64;

    // Canonical WSJT-X FT8 7-symbol Costas synchronization array
    static constexpr std::array<uint8_t, 7> COSTAS_SYNC = {3, 1, 4, 0, 6, 5, 2};

    std::array<uint8_t, NUM_FT8_SYMBOLS> truth_symbols{};

    Ft8IqSynthesizer() {
        // Populate canonical 79-symbol FT8 frame ("CQ OBEND EL87"):
        // Symbols 0..6, 36..42, 72..78: Costas 7x7 sync arrays {3, 1, 4, 0, 6, 5, 2}
        // Symbols 7..35 and 43..71: 58 deterministic 8-FSK payload symbols in {0..7}
        for (size_t k = 0; k < NUM_FT8_SYMBOLS; ++k) {
            if (k < 7) {
                truth_symbols[k] = COSTAS_SYNC[k];
            } else if (k >= 36 && k < 43) {
                truth_symbols[k] = COSTAS_SYNC[k - 36];
            } else if (k >= 72 && k < 79) {
                truth_symbols[k] = COSTAS_SYNC[k - 72];
            } else {
                // Deterministic Gray-coded 8-FSK payload tones covering all 8 tones 0..7
                truth_symbols[k] = static_cast<uint8_t>((k * 5 + 3) & 0x7);
            }
        }
    }

    std::vector<SdrIqSample> generate_stream() const {
        std::vector<SdrIqSample> stream(TOTAL_SAMPLES);

        // Desired weak FT8 USB signal amplitude: A_sig = 200 mV
        // Unwanted strong LSB image interferer (+40 dB = 100x voltage): A_img = 20,000 mV
        constexpr double A_USB_SIG_MV = 200.0;
        constexpr double A_LSB_IMG_MV = 20000.0; // +40.0 dB stronger than desired FT8 signal!

        int64_t unwrapped_phase_mrad = 0;

        for (size_t n = 0; n < TOTAL_SAMPLES; ++n) {
            const size_t sym_idx = n / SAMPLES_PER_SYMBOL;
            const size_t sym_pos = n % SAMPLES_PER_SYMBOL;
            const bool is_active_sym = (sym_idx < NUM_FT8_SYMBOLS);
            const uint8_t tone = is_active_sym ? truth_symbols[sym_idx] : 0;

            // Instantaneous normalized phase of +1250 Hz desired USB tone and -1250 Hz LSB image
            const double t_norm = static_cast<double>(n) / static_cast<double>(TOTAL_SAMPLES);
            const double phi_usb = 2.0 * M_PI * (1250.0 + 6.25 * static_cast<double>(tone)) * t_norm;
            const double phi_lsb = 2.0 * M_PI * (-1250.0) * t_norm;

            // Desired USB component (+1250 Hz): Hilbert Q channel is IN-PHASE (+usb_wave) after 90-deg shift
            const int32_t usb_wave = static_cast<int32_t>(std::llround(A_USB_SIG_MV * std::cos(phi_usb)));
            // Unwanted +40 dB LSB image interferer (-1250 Hz): Hilbert Q channel is ANTI-PHASE (-lsb_wave)
            // Also include <= 0.05% residual analog quantization noise (+/- 1 mV on 20,000 mV = > 80 dB IRR)
            const int32_t lsb_wave = static_cast<int32_t>(std::llround(A_LSB_IMG_MV * std::cos(phi_lsb)));

            // Composite Tayloe + Hilbert inputs fed to sdr_ft8_top:
            // i_mix_mv = usb_wave + lsb_wave
            // q_mix_mv = usb_wave - lsb_wave
            // Notice that in the raw input, |lsb_wave| = 20,000 mV swamps |usb_wave| = 200 mV by +40 dB!
            SdrIqSample s{};
            s.i_mix_mv          = usb_wave + lsb_wave;
            s.q_mix_mv          = usb_wave - lsb_wave;
            s.usb_only_mv       = 2 * usb_wave;
            s.lsb_interferer_mv = lsb_wave;

            // 4-stage CORDIC baseband vector input (1000 * cos, 1000 * sin)
            s.cordic_x_in = static_cast<int32_t>(std::llround(1000.0 * std::cos(phi_usb)));
            s.cordic_y_in = static_cast<int32_t>(std::llround(1000.0 * std::sin(phi_usb)));

            // Advance unwrapped CORDIC phase by exact FT8 tone increment (tone + 1) * 125 mrad
            // at the end of each 204-sample symbol integration window
            const bool is_sym_strobe = is_active_sym && (sym_pos == SAMPLES_PER_SYMBOL - 1);
            if (is_sym_strobe) {
                unwrapped_phase_mrad += static_cast<int64_t>(tone + 1) * 125;
            }
            s.cordic_phase_mrad = static_cast<int32_t>(unwrapped_phase_mrad);
            s.decim_strobe      = ((n + 1) % CIC_DECIM_RATIO == 0);
            s.symbol_strobe     = is_sym_strobe;
            s.expected_tone     = tone;

            stream[n] = s;
        }
        return stream;
    }
};

} // namespace obend::sdr_ft8
