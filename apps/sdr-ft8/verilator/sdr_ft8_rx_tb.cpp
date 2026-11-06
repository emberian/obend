// The real-signal gate of apps/sdr-ft8: a public FT8 recording through the emitted receive RTL.
//
//   sdr_ft8_rx_tb <recording.wav> <ft8_target.txt>
//
// 1. Front end (stands in for the Tayloe quadrature sampler): the recording's analytic signal (FFT
//    Hilbert transform), scaled to 16-bit I/Q with per-component peak 16384. This part is C++, not RTL.
// 2. RTL: the emitted tuning NCO (sdr_nco_mix.sv: 32-bit phase accumulator, octant fold, Q30
//    polynomial cos/sin, complex mix by exp(-j 2 pi f0 t)) so tone 0 of the target sits at 0 Hz; two
//    copies of the emitted CIC (sdr_cic3_r64.sv, N=3, R=64, M=1, 34-bit registers) on the 12 kHz clock;
//    the emitted discriminator (sdr_ft8_disc.sv: lag-2 conjugate product over each symbol, 12-stage
//    CORDIC, slicer) on the 187.5 Hz clock.
// 3. Checks: every decimated CIC output, I and Q, equals the exact CIC output computed here from the
//    impulse-response formula of Obend.Hardware.Cic.cicOut_eq_movingSum (triple moving sum of length 64,
//    sampled every 64 samples); and the 79 tone decisions equal the 79 channel tones of the reference
//    decode's message. Exit 1 on any difference.
#include <cmath>
#include <complex>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

#include "Vsdr_ft8_rx_top.h"
#include "verilated.h"

using cd = std::complex<double>;

static std::vector<int16_t> read_wav_mono16(const char* path) {
    std::ifstream f(path, std::ios::binary);
    if (!f) { std::fprintf(stderr, "cannot open %s\n", path); std::exit(2); }
    std::vector<char> b((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
    if (b.size() < 44 || std::memcmp(b.data(), "RIFF", 4) || std::memcmp(b.data() + 8, "WAVE", 4)) {
        std::fprintf(stderr, "%s: not a RIFF/WAVE file\n", path); std::exit(2);
    }
    size_t p = 12; uint16_t fmt = 0, ch = 0, bits = 0; uint32_t rate = 0;
    while (p + 8 <= b.size()) {
        uint32_t len; std::memcpy(&len, b.data() + p + 4, 4);
        if (!std::memcmp(b.data() + p, "fmt ", 4)) {
            std::memcpy(&fmt, b.data() + p + 8, 2); std::memcpy(&ch, b.data() + p + 10, 2);
            std::memcpy(&rate, b.data() + p + 12, 4); std::memcpy(&bits, b.data() + p + 22, 2);
        } else if (!std::memcmp(b.data() + p, "data", 4)) {
            if (fmt != 1 || ch != 1 || bits != 16 || rate != 12000) {
                std::fprintf(stderr, "%s: want PCM mono 16-bit 12000 Hz\n", path); std::exit(2);
            }
            std::vector<int16_t> s(len / 2);
            std::memcpy(s.data(), b.data() + p + 8, s.size() * 2);
            return s;
        }
        p += 8 + len + (len & 1);
    }
    std::fprintf(stderr, "%s: no data chunk\n", path); std::exit(2);
}

static void fft(std::vector<cd>& a, bool inverse) {
    const size_t n = a.size();
    for (size_t i = 1, j = 0; i < n; ++i) {
        size_t bit = n >> 1;
        for (; j & bit; bit >>= 1) j ^= bit;
        j ^= bit;
        if (i < j) std::swap(a[i], a[j]);
    }
    for (size_t len = 2; len <= n; len <<= 1) {
        const double ang = 2 * M_PI / double(len) * (inverse ? 1 : -1);
        const cd wl(std::cos(ang), std::sin(ang));
        for (size_t i = 0; i < n; i += len) {
            cd w(1);
            for (size_t k = 0; k < len / 2; ++k) {
                cd u = a[i + k], v = a[i + k + len / 2] * w;
                a[i + k] = u + v; a[i + k + len / 2] = u - v;
                w *= wl;
            }
        }
    }
    if (inverse) for (auto& x : a) x /= double(n);
}

struct Target { double f0 = 0; long s0 = 0; std::string tones, message; };

static Target read_target(const char* path) {
    std::ifstream f(path); std::string line; Target t;
    while (std::getline(f, line)) {
        if (line.empty() || line[0] == '#') continue;
        std::istringstream ss(line); std::string k; ss >> k;
        if (k == "f0_hz") ss >> t.f0;
        else if (k == "s0") ss >> t.s0;
        else if (k == "tones") ss >> t.tones;
        else if (k == "message") { std::getline(ss, t.message); if (!t.message.empty() && t.message[0] == ' ') t.message.erase(0, 1); }
    }
    if (t.tones.size() != 79 || t.f0 <= 0) { std::fprintf(stderr, "%s: incomplete target\n", path); std::exit(2); }
    return t;
}

static int64_t sext34(uint64_t v) { v &= (1ULL << 34) - 1; return (v & (1ULL << 33)) ? int64_t(v) - (int64_t(1) << 34) : int64_t(v); }

// cicOut 64 1 3 x m = stages (movingSum 64) 3 x (m * 64): three moving sums of length 64 (zero history).
static std::vector<int64_t> exact_cic(const std::vector<int64_t>& x, size_t outputs) {
    std::vector<int64_t> y = x;
    for (int s = 0; s < 3; ++s) {
        std::vector<int64_t> cum(y.size() + 1, 0), ms(y.size() + 1, 0);
        for (size_t n = 0; n < y.size(); ++n) cum[n + 1] = cum[n] + y[n];
        // movingSum D y n = cum n - cum (n - D) (n >= D), cum n otherwise; defined for n = 0..len
        for (size_t n = 0; n <= y.size(); ++n) ms[n] = cum[n] - (n >= 64 ? cum[n - 64] : 0);
        y = ms;
    }
    std::vector<int64_t> out(outputs);
    for (size_t m = 0; m < outputs; ++m) out[m] = (m * 64 < y.size()) ? y[m * 64] : 0;
    return out;
}

int main(int argc, char** argv) {
    if (argc < 3) { std::fprintf(stderr, "usage: %s recording.wav ft8_target.txt\n", argv[0]); return 64; }
    Verilated::commandArgs(argc, argv);
    const auto pcm = read_wav_mono16(argv[1]);
    const Target tg = read_target(argv[2]);

    // 1. Front end: analytic signal, scaled to per-component peak 16384.
    size_t N = 1; while (N < pcm.size()) N <<= 1;
    std::vector<cd> a(N, 0.0);
    for (size_t i = 0; i < pcm.size(); ++i) a[i] = double(pcm[i]);
    fft(a, false);
    for (size_t k = 1; k < N / 2; ++k) a[k] *= 2.0;
    for (size_t k = N / 2 + 1; k < N; ++k) a[k] = 0.0;
    fft(a, true);
    double peak = 0;
    for (size_t n = 0; n < pcm.size(); ++n) peak = std::max({peak, std::fabs(a[n].real()), std::fabs(a[n].imag())});
    const double scale = 16384.0 / peak;
    // Decimation phase: the strobe fires on cycles 0, 64, 128, ... from reset, the CIC output after the
    // strobe at cycle 64*m includes CIC inputs up to cycle 64*m - 3, and the NCO's output register delays
    // a sample by one cycle. Prepending P zeros makes decimated output m0 + 30k end two samples before
    // symbol k: P = 64*m0 - s0 - 2 with m0 = ceil((s0+2)/64).
    const long m0 = (tg.s0 + 2 + 63) / 64;
    const long P = 64 * m0 - tg.s0 - 2;
    std::vector<int64_t> ai(P, 0), aq(P, 0);
    for (size_t n = 0; n < pcm.size(); ++n) {
        ai.push_back(std::lround(a[n].real() * scale));
        aq.push_back(std::lround(a[n].imag() * scale));
    }
    for (long n = 0; n < 64 * 4; ++n) { ai.push_back(0); aq.push_back(0); }
    const uint32_t phaseInc = uint32_t(std::llround(tg.f0 / 12000.0 * 4294967296.0) & 0xffffffffLL);
    std::printf("front end: %zu samples, scale %.6f, %ld zeros prepended, NCO phase_inc %u (%.6f Hz), symbol 0 at decimated sample %ld\n",
                pcm.size(), scale, P, phaseInc, double(phaseInc) * 12000.0 / 4294967296.0, m0);

    // 2. RTL.
    auto* dut = new Vsdr_ft8_rx_top;
    auto tick = [&]() { dut->clk = 0; dut->eval(); dut->clk = 1; dut->eval(); };
    auto dtick = [&]() { dut->dclk = 0; dut->eval(); dut->dclk = 1; dut->eval(); };
    dut->clk = 0; dut->dclk = 0; dut->rst = 1; dut->i_in = 0; dut->q_in = 0; dut->decim_strobe = 0;
    dut->phase_inc = phaseInc;
    dut->acc_clr = 0; dut->acc_en = 0; dut->sym_latch = 0;
    tick(); dtick();
    dut->rst = 0;

    const size_t nDec = ai.size() / 64;
    std::vector<int64_t> xi, xq;  // the CIC's inputs, cycle by cycle (the NCO's output register)
    std::vector<int64_t> ciRtl, cqRtl;
    std::string decided;
    std::vector<int> oob, angles;
    for (size_t n = 0; n < nDec * 64; ++n) {
        dut->i_in = uint16_t(int16_t(ai[n]));
        dut->q_in = uint16_t(int16_t(aq[n]));
        dut->decim_strobe = (n % 64 == 0);
        xi.push_back(int16_t(dut->nco_i));
        xq.push_back(int16_t(dut->nco_q));
        tick();
        if (n % 64 != 0) continue;
        const long m = long(n / 64);
        ciRtl.push_back(sext34(dut->i_cic));
        cqRtl.push_back(sext34(dut->q_cic));
        // Discriminator controls for this decimated sample.
        const long r = m - m0;
        const long j = ((r % 30) + 30) % 30, k = (r >= 0) ? r / 30 : -1;
        dut->acc_clr = (r >= 0 && k < 79 && j == 4);
        dut->acc_en = (r >= 0 && k < 79 && j >= 4);
        dut->sym_latch = (r >= 30 && j == 0 && k <= 79);
        dtick();
        if (dut->sym_latch) {
            decided.push_back(char('0' + dut->tone_bin));
            oob.push_back(dut->tone_oob);
            angles.push_back(int32_t(dut->angle_urad));
        }
    }
    const auto refI = exact_cic(xi, nDec), refQ = exact_cic(xq, nDec);
    size_t cicChecked = 0, cicBad = 0;
    int64_t cicMax = 0;
    for (size_t m = 0; m < nDec; ++m) {
        ++cicChecked;
        if (ciRtl[m] != refI[m] || cqRtl[m] != refQ[m]) {
            if (cicBad < 5) std::printf("  CIC MISMATCH at m=%zu: RTL (%lld, %lld) exact (%lld, %lld)\n", m,
                                        (long long)ciRtl[m], (long long)cqRtl[m], (long long)refI[m], (long long)refQ[m]);
            ++cicBad;
        }
        cicMax = std::max({cicMax, std::llabs(ciRtl[m]), std::llabs(cqRtl[m])});
    }
    dut->final();
    delete dut;

    // 3. Report.
    std::printf("CIC: %zu decimated outputs x 2 channels, RTL vs exact cicOut: %zu mismatches; max |output| %lld (< 2^33 = %lld)\n",
                cicChecked, cicBad, (long long)cicMax, (long long)(int64_t(1) << 33));
    size_t match = 0, oobCount = 0;
    double maxErr = 0;
    for (size_t k = 0; k < decided.size() && k < 79; ++k) {
        if (decided[k] == tg.tones[k]) ++match;
        oobCount += oob[k];
        maxErr = std::max(maxErr, std::fabs(angles[k] - 418879.0 * (tg.tones[k] - '0')));
    }
    std::printf("reference tones (%s):\n  %s\n", tg.message.c_str(), tg.tones.c_str());
    std::printf("RTL tone decisions:\n  %s\n", decided.c_str());
    std::printf("tones: %zu/79 match, %zu flagged out of band, max |angle - k*2pi/15| = %.0f urad (slicer half-width 209438)\n",
                match, oobCount, maxErr);
    const bool ok = cicBad == 0 && decided.size() == 79 && match == 79;
    std::printf(ok ? "[PASS] the recording's target signal through the emitted RTL yields the reference message's 79 tones\n"
                   : "[FAIL] sdr_ft8_rx gate\n");
    return ok ? 0 : 1;
}
