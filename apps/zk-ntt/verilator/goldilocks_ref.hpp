#pragma once

#include <cstdint>
#include <vector>

namespace goldilocks_ref {

static constexpr uint64_t GOLDILOCKS_P   = 0xFFFFFFFF00000001ULL;
static constexpr uint64_t GOLDILOCKS_EPS = 0x00000000FFFFFFFFULL;

inline uint64_t add_mod(uint64_t a, uint64_t b) {
    __uint128_t s = static_cast<__uint128_t>(a % GOLDILOCKS_P) +
                    static_cast<__uint128_t>(b % GOLDILOCKS_P);
    return static_cast<uint64_t>(s % GOLDILOCKS_P);
}

inline uint64_t sub_mod(uint64_t a, uint64_t b) {
    uint64_t am = a % GOLDILOCKS_P;
    uint64_t bm = b % GOLDILOCKS_P;
    return (am >= bm) ? (am - bm) : (am + GOLDILOCKS_P - bm);
}

inline uint64_t mul_mod(uint64_t a, uint64_t b) {
    __uint128_t p = static_cast<__uint128_t>(a % GOLDILOCKS_P) *
                    static_cast<__uint128_t>(b % GOLDILOCKS_P);
    return static_cast<uint64_t>(p % GOLDILOCKS_P);
}

inline uint64_t pow_mod(uint64_t base, uint64_t exp) {
    uint64_t res = 1ULL;
    uint64_t cur = base % GOLDILOCKS_P;
    uint64_t e   = exp;
    while (e > 0) {
        if (e & 1ULL) res = mul_mod(res, cur);
        cur = mul_mod(cur, cur);
        e >>= 1ULL;
    }
    return res;
}

inline uint64_t inv_mod(uint64_t a) {
    return pow_mod(a, GOLDILOCKS_P - 2ULL);
}

// Primitive 256-th root of unity in F_p^* (where g = 7 is a multiplicative generator of F_p^*)
inline uint64_t primitive_root_256() {
    return pow_mod(7ULL, (GOLDILOCKS_P - 1ULL) / 256ULL);
}

inline size_t bit_reverse_8(size_t x) {
    size_t r = 0;
    for (int i = 0; i < 8; ++i) {
        r = (r << 1) | ((x >> i) & 1U);
    }
    return r;
}

// Reference 256-point Cooley-Tukey Radix-2 NTT over Goldilocks field using __uint128_t
inline std::vector<uint64_t> ntt_256_ref(const std::vector<uint64_t>& in, uint64_t omega) {
    std::vector<uint64_t> a(256);
    for (size_t i = 0; i < 256; ++i) {
        a[bit_reverse_8(i)] = in[i] % GOLDILOCKS_P;
    }
    for (size_t len = 2; len <= 256; len <<= 1) {
        size_t half = len >> 1;
        uint64_t w_step = pow_mod(omega, 256ULL / len);
        for (size_t i = 0; i < 256; i += len) {
            uint64_t w = 1ULL;
            for (size_t j = 0; j < half; ++j) {
                uint64_t u = a[i + j];
                uint64_t v = mul_mod(a[i + j + half], w);
                a[i + j]        = add_mod(u, v);
                a[i + j + half] = sub_mod(u, v);
                w = mul_mod(w, w_step);
            }
        }
    }
    return a;
}

// Reference 64-bit AMD VOP64 instruction sequence emulator matching Obend.Lower.compileRtlExprToAmdGpu
// for zkNttButterflyFoldRtlExpr: (u + v * w) + r * ((u - v * w) - (u + v * w))
// The Fiat-Shamir transcript step of SumcheckRoundPoly.obend / Obend.Apps.ZkNtt.transcriptAbsorbSpec:
// (((t + g0) * 2^32 + g1) * 2^32 + g2 + 0x5A17)^7 in F_p. A fixed permutation binding the challenge
// to the three round messages; not a cryptographic hash.
static constexpr uint64_t TRANSCRIPT_ALPHA = 0x100000000ULL;
static constexpr uint64_t TRANSCRIPT_CONST = 0x5A17ULL;
static constexpr uint64_t TRANSCRIPT_IV    = 0x4F42454E44ULL;

inline uint64_t transcript_absorb(uint64_t t, uint64_t g0, uint64_t g1, uint64_t g2) {
    uint64_t s  = add_mod(mul_mod(add_mod(mul_mod(add_mod(t, g0), TRANSCRIPT_ALPHA), g1), TRANSCRIPT_ALPHA),
                          add_mod(g2, TRANSCRIPT_CONST));
    uint64_t s2 = mul_mod(s, s);
    uint64_t s4 = mul_mod(s2, s2);
    return mul_mod(mul_mod(s4, s2), s);
}

} // namespace goldilocks_ref
