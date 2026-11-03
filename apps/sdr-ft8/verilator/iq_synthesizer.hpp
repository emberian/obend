// 16,384-Sample 16-Bit Quadrature IQ Stream Synthesizer for Flagship App #3:
// All-Digital 40m (7.074 MHz) Tayloe IQ FT8 SDR Transceiver
// Synthesizes ONLY raw RF-mixed 4-phase Tayloe quadrature channels (NO pre-computed
// ground-truth phase inputs):
//   1. A weak desired Upper-Sideband (USB) +1250 Hz 79-symbol continuous-phase 8-FSK
//      FT8 frame (including the three 7-symbol Costas sync arrays {3, 1, 4, 0, 6, 5, 2}
//      at symbols 0..6, 36..42, 72..78 and 58 payload 8-FSK symbols in {0..7}),
//   2. Buried under a +40 dB (100x voltage amplitude!) Lower-Sideband (LSB) image
//      interferer at -1250 Hz.
#pragma once

#include <array>
#include <cmath>
#include <cstdint>
#include <vector>

namespace obend::sdr_ft8 {

struct SdrIqSample {
    int32_t i_mix_mv;          // Tayloe real-branch I channel (usb_cos + lsb_cos)
    int32_t q_mix_mv;          // Tayloe real-branch Hilbert Q channel (usb_cos - lsb_cos)
    int32_t i_quad_mv;         // Tayloe quad-branch I channel (usb_sin + lsb_sin)
    int32_t q_quad_mv;         // Tayloe quad-branch Hilbert Q channel (usb_sin - lsb_sin)
    int32_t usb_only_mv;       // Reference desired USB real component (for IRR measurement)
    int32_t lsb_interferer_mv; // Reference +40 dB LSB image interferer component (for IRR measurement)
    bool    decim_strobe;      // R = 64 CIC decimation strobe (256 ticks across 16,384 samples)
    bool    phase_ref_strobe;  // Latches initial CORDIC phase reference at end of 16-sample preamble
    bool    symbol_strobe;     // FT8 symbol boundary strobe (79 symbols x 200 samples)
    uint8_t expected_tone;     // Testbench-only ground-truth FT8 8-FSK symbol in {0..7} (NOT fed to RTL!)
};

class Ft8IqSynthesizer {
public:
    static constexpr size_t TOTAL_SAMPLES      = 16384;
    static constexpr size_t PREAMBLE_SAMPLES   = 16;
    static constexpr size_t NUM_FT8_SYMBOLS    = 79;
    static constexpr size_t SAMPLES_PER_SYMBOL = 200; // 16 + 79 * 200 = 15,816 samples (< 16,384)
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
                truth_symbols[k] = static_cast<uint8_t>((k * 5 + 3) & 0x7);
            }
        }
    }

    std::vector<SdrIqSample> generate_stream() const {
        std::vector<SdrIqSample> stream(TOTAL_SAMPLES);

        // Desired weak FT8 USB signal amplitude: A_sig = 200 mV
        // Unwanted strong LSB image interferer (+40 dB = 100x voltage): A_img = 20,000 mV
        constexpr double A_USB_SIG_MV = 200.0;
        constexpr double A_LSB_IMG_MV = 20000.0;

        double phi_usb = 0.0;
        double phi_lsb = 0.0;

        for (size_t n = 0; n < TOTAL_SAMPLES; ++n) {
            bool is_ref_strobe = (n == PREAMBLE_SAMPLES - 1);
            bool is_active_sym = false;
            bool is_sym_strobe = false;
            uint8_t tone = 0;

            if (n >= PREAMBLE_SAMPLES) {
                const size_t rel = n - PREAMBLE_SAMPLES;
                const size_t sym_idx = rel / SAMPLES_PER_SYMBOL;
                const size_t sym_pos = rel % SAMPLES_PER_SYMBOL;
                if (sym_idx < NUM_FT8_SYMBOLS) {
                    is_active_sym = true;
                    tone = truth_symbols[sym_idx];
                    // Continuous-phase 8-FSK: tone k in {0..7} advances phase by
                    // (k + 1) * 0.600 rad across the 200-sample symbol window
                    const double dphi_usb = (static_cast<double>(tone + 1) * 0.600) /
                                            static_cast<double>(SAMPLES_PER_SYMBOL);
                    phi_usb += dphi_usb;
                    is_sym_strobe = (sym_pos == SAMPLES_PER_SYMBOL - 1);
                }
            }

            // Strong -1250 Hz LSB image interferer rotates backwards at -2.300 rad / symbol
            phi_lsb -= 2.300 / static_cast<double>(SAMPLES_PER_SYMBOL);

            const int32_t usb_cos = static_cast<int32_t>(std::llround(A_USB_SIG_MV * std::cos(phi_usb)));
            const int32_t usb_sin = static_cast<int32_t>(std::llround(A_USB_SIG_MV * std::sin(phi_usb)));
            const int32_t lsb_cos = static_cast<int32_t>(std::llround(A_LSB_IMG_MV * std::cos(phi_lsb)));
            const int32_t lsb_sin = static_cast<int32_t>(std::llround(A_LSB_IMG_MV * std::sin(phi_lsb)));

            // Composite 4-phase Tayloe + 90-deg Hilbert outputs fed into sdr_ft8_top:
            // Desired USB (+f_audio): I and Hilbert-Q are IN-PHASE (+usb, +usb)
            // Unwanted +40 dB LSB image (-f_audio): I and Hilbert-Q are ANTI-PHASE (+lsb, -lsb)
            SdrIqSample s{};
            s.i_mix_mv          = usb_cos + lsb_cos;
            s.q_mix_mv          = usb_cos - lsb_cos;
            s.i_quad_mv         = usb_sin + lsb_sin;
            s.q_quad_mv         = usb_sin - lsb_sin;
            s.usb_only_mv       = 2 * usb_cos;
            s.lsb_interferer_mv = lsb_cos;
            s.decim_strobe      = ((n + 1) % CIC_DECIM_RATIO == 0);
            s.phase_ref_strobe  = is_ref_strobe;
            s.symbol_strobe     = is_sym_strobe;
            s.expected_tone     = tone;

            stream[n] = s;
        }
        return stream;
    }
};

} // namespace obend::sdr_ft8
