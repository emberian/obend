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
inline uint64_t emulate_amd_vop64_butterfly_fold(uint64_t u, uint64_t v, uint64_t w, uint64_t r) {
    uint64_t vgpr[16] = {0};
    // v_mov_b64 v0, u ; v_mov_b64 v1, v ; v_mov_b64 v2, w
    vgpr[0] = u;
    vgpr[1] = v;
    vgpr[2] = w;
    // v_mul_lo_u64 v3, v1, v2
    vgpr[3] = vgpr[1] * vgpr[2];
    // v_add_u64 v4, v0, v3  (even)
    vgpr[4] = vgpr[0] + vgpr[3];
    // v_sub_u64 v5, v0, v3  (odd)
    vgpr[5] = vgpr[0] - vgpr[3];
    // v_sub_u64 v6, v5, v4  (diff)
    vgpr[6] = vgpr[5] - vgpr[4];
    // v_mov_b64 v7, r
    vgpr[7] = r;
    // v_mad_u64_u32 / v_mul + v_add -> v8 = v4 + v7 * v6
    vgpr[8] = vgpr[4] + (vgpr[7] * vgpr[6]);
    return vgpr[8];
}

} // namespace goldilocks_ref
