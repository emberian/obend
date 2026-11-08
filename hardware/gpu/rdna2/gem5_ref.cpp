// gem5_ref.cpp: the lane arithmetic of gem5's Vega execute() bodies, ported, as the differential reference
// for Obend.Hardware.Gpu.Rdna2.Semantics (hardware/gpu/rdna2/gem5_ref.py drives it; the vectors land in
// gem5_vectors.tsv). Each case copies the expression of the named body from
// github.com/gem5/gem5 stable (9d368896ce119c17e1289dcbb18f33624724b843) src/arch/amdgpu/vega/insts/*.cc,
// line numbers and instruction symbols refer to that revision; the operand model is gem5's: a destination ScalarOperand starts zeroed
// (operand.hh:401, std::memset) and setBit writes one lane's bit, so lanes with EXEC clear leave 0 in a
// mask result; VecOperand writes only lanes with execMask set. Registers follow the fixed assignment of
// gem5_ref.py (sources v0, v1 / v[0:1], v[2:3], s[0:1], s[2:3]; destinations v4 / v[4:5], s[4:5]).
//
//   gem5_ref <seed> <trials>   reads "name hexwords" lines on stdin, writes one TSV row per trial per line:
//   name  hexwords  exec vcc scc  s0..s7  v0..v5[64]  ->  exec vcc scc pc  s0..s7  v0..v5[64]  skip
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

typedef uint32_t VecElemU32; typedef uint64_t VecElemU64; typedef int64_t VecElemI64;
static const int NumVecElemPerVecReg = 64;

struct State {
    uint64_t exec, vcc; bool scc; uint32_t s[8]; uint32_t v[6][64]; uint64_t pc;
};

// gem5 base/bitfield.hh: bits(val, first, last) and bits(val, bit)
static inline uint64_t bits(uint64_t val, int first, int last) { int nbits = first - last + 1; return (val >> last) & ((1ULL << nbits) - 1); }
static inline uint64_t bits(uint64_t val, int bit) { return bits(val, bit, bit); }
static inline void setBit(uint64_t &m, int lane, int b) { if (b) m |= (1ULL << lane); else m &= ~(1ULL << lane); }
static inline int64_t sext16(uint64_t x) { return (int64_t)(int16_t)(x & 0xffff); }

static uint64_t rng_state;
static uint64_t rnd() { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }
// values that exercise the carries: small, near 2^32, random
static uint32_t rnd32() { switch (rnd() % 4) { case 0: return (uint32_t)(rnd() % 8); case 1: return 0xffffffffu - (uint32_t)(rnd() % 8); default: return (uint32_t)rnd(); } }

// The effect of one instruction on the state, per the gem5 body named; returns the fields the Lean model
// is known to differ in (RDNA2 departures), empty when none.
static std::string execute(const std::string &name, State &st, int nwords) {
    State in = st;
    uint64_t execm = in.exec;
    st.pc = in.pc + nwords;                                    // every non-branch advances by its width
    auto src0 = [&](int l) { return in.v[0][l]; };
    auto src1 = [&](int l) { return in.v[1][l]; };
    auto src2 = [&](int l) { return in.v[2][l]; };
    auto src0_64 = [&](int l) { return (uint64_t)in.v[0][l] | ((uint64_t)in.v[1][l] << 32); };
    auto src1_64 = [&](int l) { return (uint64_t)in.v[2][l] | ((uint64_t)in.v[3][l] << 32); };
    uint64_t s01 = (uint64_t)in.s[0] | ((uint64_t)in.s[1] << 32);
    uint64_t s23 = (uint64_t)in.s[2] | ((uint64_t)in.s[3] << 32);
    uint64_t sdst = 0;                                          // a fresh ScalarOperandU64 is zeroed
    auto vdst = [&](int l, uint32_t x) { st.v[4][l] = x; };
    auto vdst64 = [&](int l, uint64_t x) { st.v[4][l] = (uint32_t)x; st.v[5][l] = (uint32_t)(x >> 32); };
    auto writeS45 = [&](uint64_t x) { st.s[4] = (uint32_t)x; st.s[5] = (uint32_t)(x >> 32); };
    #define LANES for (int lane = 0; lane < NumVecElemPerVecReg; ++lane) if (bits(execm, lane))
    if (name == "V_ADD_CO_U32") {                               // vop3.cc:1325 Inst_VOP3__V_ADD_CO_U32
        LANES { vdst(lane, src0(lane) + src1(lane)); setBit(sdst, lane, ((VecElemU64)src0(lane) + (VecElemU64)src1(lane)) >= 0x100000000ULL ? 1 : 0); }
        st.vcc = sdst;                                          // SDST = vcc in the asm text
    } else if (name == "V_SUB_CO_U32") {                        // vop3.cc:1414 Inst_VOP3__V_SUB_CO_U32
        LANES { vdst(lane, src0(lane) - src1(lane)); setBit(sdst, lane, src1(lane) > src0(lane) ? 1 : 0); }
        st.vcc = sdst;
    } else if (name == "V_ADD_CO_CI_U32") {                     // vop3.cc:1469 Inst_VOP3__V_ADDC_CO_U32 (twin), carry-in s[2:3], carry-out s[4:5]
        uint64_t vcc = s23;
        LANES { vdst(lane, src0(lane) + src1(lane) + bits(vcc, lane)); setBit(sdst, lane, ((VecElemU64)src0(lane) + (VecElemU64)src1(lane) + (VecElemU64)bits(vcc, lane)) >= 0x100000000 ? 1 : 0); }
        writeS45(sdst);
    } else if (name == "V_SUB_CO_CI_U32") {                     // vop3.cc:1523 Inst_VOP3__V_SUBB_CO_U32 (twin)
        uint64_t vcc = s23;
        LANES { vdst(lane, src0(lane) - src1(lane) - bits(vcc, lane)); setBit(sdst, lane, (src1(lane) + bits(vcc, lane)) > src0(lane) ? 1 : 0); }
        writeS45(sdst);
    } else if (name == "V_ADD_CO_CI_U32_E32") {                 // vop2.cc:1343 Inst_VOP2__V_ADDC_CO_U32 (twin): VCC in and out
        uint64_t vcc = in.vcc;
        LANES { vdst(lane, src0(lane) + src1(lane) + bits(vcc, lane)); setBit(sdst, lane, ((VecElemU64)src0(lane) + (VecElemU64)src1(lane) + (VecElemU64)bits(vcc, lane, lane)) >= 0x100000000 ? 1 : 0); }
        st.vcc = sdst;
    } else if (name == "V_SUB_CO_CI_U32_E32") {                 // vop2.cc:1392 Inst_VOP2__V_SUBB_CO_U32 (twin)
        uint64_t vcc = in.vcc;
        LANES { vdst(lane, src0(lane) - src1(lane) - bits(vcc, lane)); setBit(sdst, lane, (src1(lane) + bits(vcc, lane)) > src0(lane) ? 1 : 0); }
        st.vcc = sdst;
    } else if (name == "V_ADD_NC_U32") {                        // vop2.cc:2081 Inst_VOP2__V_ADD_U32 (twin: Vega's name)
        LANES { vdst(lane, src0(lane) + src1(lane)); }
    } else if (name == "V_MOV_B32") {                           // vop1.cc Inst_VOP1__V_MOV_B32: vdst[lane] = src[lane]
        LANES { vdst(lane, src0(lane)); }
    } else if (name == "V_AND_B32") {                           // vop2.cc:832
        LANES { vdst(lane, src0(lane) & src1(lane)); }
    } else if (name == "V_OR_B32") {                            // vop2.cc:860
        LANES { vdst(lane, src0(lane) | src1(lane)); }
    } else if (name == "V_LSHLREV_B32") {                       // vop2.cc:760
        LANES { vdst(lane, src1(lane) << bits(src0(lane), 4, 0)); }
    } else if (name == "V_LSHL_ADD_U32") {                      // vop3.cc:7280
        LANES { vdst(lane, (src0(lane) << bits(src1(lane), 4, 0)) + src2(lane)); }
    } else if (name == "V_ADD3_U32") {                          // vop3.cc:7368
        LANES { vdst(lane, src0(lane) + src1(lane) + src2(lane)); }
    } else if (name == "V_AND_OR_B32") {                        // vop3.cc:7457
        LANES { vdst(lane, (src0(lane) & src1(lane)) | src2(lane)); }
    } else if (name == "V_MUL_LO_U32") {                        // vop3.cc:8694
        LANES { VecElemI64 s0 = (VecElemI64)src0(lane); VecElemI64 s1 = (VecElemI64)src1(lane); vdst(lane, (VecElemU32)((s0 * s1) & 0xffffffffLL)); }
    } else if (name == "V_MUL_HI_U32") {                        // vop3.cc:8738
        LANES { VecElemI64 s0 = (VecElemI64)src0(lane); VecElemI64 s1 = (VecElemI64)src1(lane); vdst(lane, (VecElemU32)(((s0 * s1) >> 32) & 0xffffffffLL)); }
    } else if (name == "V_LSHLREV_B64") {                       // vop3.cc:9069: src0 count (v0), src1 pair v[2:3]
        LANES { vdst64(lane, src1_64(lane) << bits(src0(lane), 5, 0)); }
    } else if (name == "V_LSHRREV_B64") {                       // vop3.cc:9113
        LANES { vdst64(lane, src1_64(lane) >> bits(src0(lane), 5, 0)); }
    } else if (name == "V_CNDMASK_B32") {                       // vop3.cc:57 Inst_VOP3__V_CNDMASK_B32, mask s[2:3]
        uint64_t vcc = s23;
        LANES { vdst(lane, bits(vcc, lane) ? src1(lane) : src0(lane)); }
    } else if (name == "V_CNDMASK_B32_E32") {                   // vop2.cc:57 Inst_VOP2__V_CNDMASK_B32, mask VCC
        uint64_t vcc = in.vcc;
        LANES { vdst(lane, bits(vcc, lane) ? src1(lane) : src0(lane)); }
    } else if (name == "V_CMP_LE_U32") {                        // vop3_cmp.cc:6060, result s[4:5]
        LANES { setBit(sdst, lane, src0(lane) <= src1(lane) ? 1 : 0); }
        writeS45(sdst);
    } else if (name == "V_CMP_GT_U32") {                        // vop3_cmp.cc:6102
        LANES { setBit(sdst, lane, src0(lane) > src1(lane) ? 1 : 0); }
        writeS45(sdst);
    } else if (name == "V_CMP_LE_U32_E32") {                    // vopc.cc:5057, result VCC
        LANES { setBit(sdst, lane, src0(lane) <= src1(lane) ? 1 : 0); }
        st.vcc = sdst;
    } else if (name == "V_CMP_GT_U32_E32") {                    // vopc.cc:5092
        LANES { setBit(sdst, lane, src0(lane) > src1(lane) ? 1 : 0); }
        st.vcc = sdst;
    } else if (name == "V_CMPX_GT_U32_E32") {                   // vopc.cc:5650: Vega writes VCC and EXEC; RDNA2 writes EXEC only (manual 12.9) -> VCC skipped
        LANES { setBit(sdst, lane, src0(lane) > src1(lane) ? 1 : 0); }
        st.exec = sdst; st.vcc = sdst;
        return "vcc";
    } else if (name == "V_CMP_LT_U64") {                        // vop3_cmp.cc:7232, v[0:1] < v[2:3]
        LANES { setBit(sdst, lane, src0_64(lane) < src1_64(lane) ? 1 : 0); }
        writeS45(sdst);
    } else if (name == "V_CMP_NE_I64") {                        // vop3_cmp.cc:7094
        LANES { setBit(sdst, lane, (int64_t)src0_64(lane) != (int64_t)src1_64(lane) ? 1 : 0); }
        writeS45(sdst);
    } else if (name == "S_MOV_B32") {                           // sop1.cc Inst_SOP1__S_MOV_B32: sdst = src.rawData(), s4 = s0
        st.s[4] = in.s[0];
    } else if (name == "S_MOV_B64") {                           // sop1.cc:79
        writeS45(s01);
    } else if (name == "S_MOVK_I32") {                          // sopk.cc:55: sdst = sext<16>(SIMM16); the text carries 0x8123
        st.s[4] = (uint32_t)(int32_t)sext16(0x8123);
    } else if (name == "S_AND_B64") {                           // sop2.cc:478
        uint64_t d = s01 & s23; writeS45(d); st.scc = d ? 1 : 0;
    } else if (name == "S_CBRANCH_EXECZ") {                     // sopp.cc:398: if exec none, pc = pc + simm16*4 + 4 (bytes); the text carries 5
        if (in.exec == 0) st.pc = in.pc + 1 + 5;
    } else if (name == "S_ENDPGM") {                            // sopp.cc Inst_SOPP__S_ENDPGM: the wave ends; no register effect
    } else if (name == "S_WAITCNT") {                           // sopp.cc Inst_SOPP__S_WAITCNT: no architectural effect in gem5's model either
    } else if (name == "V_READFIRSTLANE_B32") {              // vop1.cc Inst_VOP1__V_READFIRSTLANE_B32::execute
        int lane = 0;
        if (execm) { while (!bits(execm, lane)) ++lane; }
        st.s[4] = src0(lane);
    } else if (name == "V_MIN_U32") {                         // vop2.cc Inst_VOP2__V_MIN_U32::execute
        LANES { vdst(lane, std::min(src0(lane), src1(lane))); }
    } else if (name == "V_LSHRREV_B32") {                     // vop3.cc Inst_VOP3__V_LSHRREV_B32::execute
        LANES { vdst(lane, src1(lane) >> bits(src0(lane), 4, 0)); }
    } else if (name == "V_ADD_LSHL_U32") {                    // vop3.cc Inst_VOP3__V_ADD_LSHL_U32::execute
        LANES { vdst(lane, (src0(lane) + src1(lane)) << bits(src2(lane), 4, 0)); }
    } else if (name == "V_CMP_GE_U32") {                      // vopc.cc Inst_VOPC__V_CMP_GE_U32::execute
        LANES { setBit(sdst, lane, src0(lane) >= src1(lane)); }
        st.vcc = sdst;
    } else if (name == "S_ADD_U32" || name == "S_ADDC_U32") { // sop2.cc Inst_SOP2__S_ADD_U32::execute and Inst_SOP2__S_ADDC_U32::execute
        uint64_t ci = name == "S_ADDC_U32" ? in.scc : 0;
        st.s[4] = in.s[0] + in.s[1] + ci;
        st.scc = ((uint64_t)in.s[0] + (uint64_t)in.s[1] + ci) >= 0x100000000ULL;
    } else if (name == "S_SUB_I32") {                         // sop2.cc Inst_SOP2__S_SUB_I32::execute; unsigned storage preserves bit-pattern without C++ signed-overflow UB
        st.s[4] = in.s[0] - in.s[1];
        st.scc = bits(in.s[0],31) != bits(in.s[1],31) && bits(in.s[0],31) != bits(st.s[4],31);
    } else if (name == "S_MAX_U32") {                         // sop2.cc Inst_SOP2__S_MAX_U32::execute
        st.s[4] = std::max(in.s[0], in.s[1]); st.scc = in.s[0] > in.s[1];
    } else if (name == "S_XOR_B32") {                         // sop2.cc Inst_SOP2__S_XOR_B32::execute
        st.s[4] = in.s[0] ^ in.s[1]; st.scc = st.s[4] != 0;
    } else if (name == "S_MUL_I32") {                         // sop2.cc Inst_SOP2__S_MUL_I32::execute; widen before multiplying to avoid the upstream expression's C++ signed-overflow UB
        int64_t product = (int64_t)(int32_t)in.s[0] * (int64_t)(int32_t)in.s[1];
        st.s[4] = (uint64_t)product & 0xffffffffULL;
    } else if (name == "S_MUL_HI_U32") {                      // sop2.cc Inst_SOP2__S_MUL_HI_U32::execute
        st.s[4] = ((uint64_t)in.s[0] * (uint64_t)in.s[1]) >> 32;
    } else if (name == "S_OR_B64") {                          // sop2.cc Inst_SOP2__S_OR_B64::execute
        uint64_t d = s01 | s23; writeS45(d); st.scc = d != 0;
    } else if (name == "S_ANDN2_B64") {                       // sop2.cc Inst_SOP2__S_ANDN2_B64::execute
        uint64_t d = s01 & ~s23; writeS45(d); st.scc = d != 0;
    } else if (name == "S_CSELECT_B64") {                     // sop2.cc Inst_SOP2__S_CSELECT_B64::execute
        writeS45(in.scc ? s01 : s23);
    } else if (name == "S_BFM_B64") {                         // sop2.cc Inst_SOP2__S_BFM_B64::execute
        writeS45(((1ULL << bits(in.s[0],5,0)) - 1) << bits(in.s[1],5,0));
    } else if (name == "S_AND_SAVEEXEC_B64") {                 // sop1.cc Inst_SOP1__S_AND_SAVEEXEC_B64::execute
        writeS45(in.exec); st.exec = s01 & in.exec; st.scc = st.exec != 0;
    } else if (name == "S_CMP_EQ_I32") {                      // sopc.cc Inst_SOPC__S_CMP_EQ_I32::execute
        st.scc = in.s[0] == in.s[1];
    } else if (name == "S_BRANCH") {                          // sopp.cc Inst_SOPP__S_BRANCH::execute
        st.pc = in.pc + 1 + 5;
    } else if (name == "S_CBRANCH_SCC0") {                    // sopp.cc Inst_SOPP__S_CBRANCH_SCC0::execute
        if (!in.scc) st.pc = in.pc + 1 + 5;
    } else if (name == "S_OR_B32") {                           // sop2.cc Inst_SOP2__S_OR_B32::execute
        st.s[4] = in.s[0] | in.s[1]; st.scc = st.s[4] != 0;
    } else if (name == "S_CMP_LG_I32") {                      // sopc.cc Inst_SOPC__S_CMP_LG_I32::execute
        st.scc = in.s[0] != in.s[1];
    } else if (name == "S_CMP_GE_U32") {                      // sopc.cc Inst_SOPC__S_CMP_GE_U32::execute
        st.scc = in.s[0] >= in.s[1];
    } else if (name == "S_GETPC_B64") {                       // sop1.cc Inst_SOP1__S_GETPC_B64::execute: gem5 PC is bytes, this harness PC is dwords
        writeS45(4 * in.pc + 4);
    } else if (name == "S_CBRANCH_SCC1") {                    // sopp.cc Inst_SOPP__S_CBRANCH_SCC1::execute
        if (in.scc) st.pc = in.pc + 1 + 5;
    } else if (name == "V_CMP_GT_U64") {                      // vopc.cc Inst_VOPC__V_CMP_GT_U64::execute
        LANES { setBit(sdst, lane, src0_64(lane) > src1_64(lane)); }
        st.vcc = sdst;
    } else if (name == "V_SUBREV_CO_U32") {                   // vop3.cc Inst_VOP3__V_SUBREV_CO_U32::execute
        LANES { vdst(lane, src1(lane) - src0(lane)); setBit(sdst, lane, src0(lane) > src1(lane)); }
        writeS45(sdst);
    } else if (name == "S_AND_B32") {                          // sop2.cc:447
        st.s[4] = in.s[0] & in.s[1]; st.scc = st.s[4] != 0;
    } else if (name == "S_LSHL_B32") {                         // sop2.cc:943
        st.s[4] = in.s[0] << bits(in.s[1], 4, 0); st.scc = st.s[4] != 0;
    } else if (name == "S_BFM_B32") {                          // sop2.cc:1132: SCC unchanged
        st.s[4] = ((1u << bits(in.s[0], 4, 0)) - 1) << bits(in.s[1], 4, 0);
    } else if (name == "S_NOR_B64") {                          // sop2.cc:850
        uint64_t d = ~(s01 | s23); writeS45(d); st.scc = d != 0;
    } else if (name == "S_CMP_LT_U32") {                       // sopc.cc:323
        st.scc = in.s[0] < in.s[1];
    } else if (name == "S_CMPK_LT_U32") {                      // sopk.cc:367: SIMM16 zero-extended; the text carries 0x8123
        st.scc = in.s[0] < 0x8123u;
    } else if (name == "S_MULK_I32") {                         // sopk.cc:452: sdst = sdst * sext<16>(SIMM16)
        st.s[4] = (uint32_t)((int32_t)in.s[4] * (int32_t)sext16(0x8123));
    } else if (name == "V_CMP_LT_U32") {                       // vopc.cc:4987
        LANES { setBit(sdst, lane, src0(lane) < src1(lane)); }
        st.vcc = sdst;
    } else if (name == "V_CMP_EQ_I32") {                       // vopc.cc:4758
        LANES { setBit(sdst, lane, src0(lane) == src1(lane)); }
        st.vcc = sdst;
    } else if (name == "V_CMP_NE_I32") {                       // vopc.cc:4863
        LANES { setBit(sdst, lane, src0(lane) != src1(lane)); }
        st.vcc = sdst;
    } else if (name == "V_CMPX_EQ_I32" || name == "V_CMPX_NE_I32" || name == "V_CMPX_LE_U32") {
        // vopc.cc:5296, 5407, 5613: Vega writes VCC and EXEC; RDNA2 writes EXEC only (manual 12.9) -> VCC skipped
        LANES { setBit(sdst, lane, name == "V_CMPX_EQ_I32" ? src0(lane) == src1(lane)
                                  : name == "V_CMPX_NE_I32" ? src0(lane) != src1(lane) : src0(lane) <= src1(lane)); }
        st.exec = sdst; st.vcc = sdst;
        return "vcc";
    } else if (name == "V_MAX_U32") {                          // vop2.cc:658
        LANES { vdst(lane, std::max(src0(lane), src1(lane))); }
    } else if (name == "V_SUB_NC_U32") {                       // vop2.cc:2152 Inst_VOP2__V_SUB_U32 (Vega's name)
        LANES { vdst(lane, src0(lane) - src1(lane)); }
    } else if (name == "V_SUBREV_NC_U32") {                    // vop2.cc:2187 Inst_VOP2__V_SUBREV_U32 (Vega's name)
        LANES { vdst(lane, src1(lane) - src0(lane)); }
    } else if (name == "V_SUBREV_CO_CI_U32_E32") {             // vop2.cc:1440 Inst_VOP2__V_SUBBREV_CO_U32: VCC in and out
        uint64_t vcc = in.vcc;
        LANES { vdst(lane, src1(lane) - src0(lane) - bits(vcc, lane)); setBit(sdst, lane, (src0(lane) + bits(vcc, lane)) > src1(lane) ? 1 : 0); }
        st.vcc = sdst;
    } else if (name == "V_MUL_U32_U24") {                      // vop2.cc:417
        LANES { vdst(lane, (uint32_t)(bits(src0(lane), 23, 0) * bits(src1(lane), 23, 0))); }
    } else if (name == "V_LSHL_OR_B32") {                      // vop3.cc:7412
        LANES { vdst(lane, (src0(lane) << bits(src1(lane), 4, 0)) | src2(lane)); }
    } else if (name == "V_MBCNT_LO_U32_B32" || name == "V_MBCNT_HI_U32_B32") {  // vop3.cc:8975, 9023
        LANES { uint64_t tm = (1ULL << lane) - 1ULL;
                uint32_t m = name == "V_MBCNT_LO_U32_B32" ? (uint32_t)bits(tm, 31, 0) : (uint32_t)bits(tm, 63, 32);
                vdst(lane, (uint32_t)__builtin_popcount(src0(lane) & m) + src1(lane)); }
    } else if (name == "S_NOP") {                             // sopp.cc Inst_SOPP__S_NOP::execute: delay only
    } else {
        std::cerr << "no reference for " << name << "\n"; exit(2);
    }
    return "";
}

static std::string hex64(uint64_t x) { char b[20]; snprintf(b, sizeof b, "%016llx", (unsigned long long)x); return b; }
static std::string hex32(uint32_t x) { char b[12]; snprintf(b, sizeof b, "%08x", x); return b; }

int main(int argc, char **argv) {
    if (argc != 3) { std::cerr << "gem5_ref <seed> <trials>\n"; return 2; }
    rng_state = strtoull(argv[1], nullptr, 10) * 0x9E3779B97F4A7C15ULL + 1;
    int trials = atoi(argv[2]);
    std::string line;
    while (std::getline(std::cin, line)) {
        std::istringstream is(line);
        std::string name, w; is >> name; std::vector<std::string> words; while (is >> w) words.push_back(w);
        for (int t = 0; t < trials; ++t) {
            State st;
            st.exec = (t == 0) ? ~0ULL : (t == 1 ? 0 : rnd());
            st.vcc = rnd(); st.scc = rnd() & 1; st.pc = 0;
            for (int i = 0; i < 8; ++i) st.s[i] = rnd32();
            for (int r = 0; r < 6; ++r) for (int l = 0; l < 64; ++l) st.v[r][l] = rnd32();
            // Explicit high-lane and scalar carry/overflow boundaries supplement random states.
            if (name == "V_READFIRSTLANE_B32" && t == 2) st.exec = 1ULL << 32;
            if (name == "V_READFIRSTLANE_B32" && t == 3) st.exec = 1ULL << 63;
            if ((name == "S_ADD_U32" || name == "S_ADDC_U32") && t == 2) { st.s[0] = 0xffffffff; st.s[1] = 0; st.scc = true; }
            if ((name == "S_ADD_U32" || name == "S_ADDC_U32") && t == 3) { st.s[0] = 0xffffffff; st.s[1] = 1; st.scc = false; }
            if (name == "S_SUB_I32" && t == 2) { st.s[0] = 0x80000000; st.s[1] = 1; }
            if (name == "S_SUB_I32" && t == 3) { st.s[0] = 0x7fffffff; st.s[1] = 0xffffffff; }
            State in = st;
            std::string skip = execute(name, st, (int)words.size());
            std::ostringstream o;
            o << name << "\t"; for (size_t i = 0; i < words.size(); ++i) o << (i ? " " : "") << words[i];
            auto dump = [&](const State &x, bool out) {
                o << "\t" << hex64(x.exec) << " " << hex64(x.vcc) << " " << (x.scc ? 1 : 0); if (out) o << " " << x.pc;
                o << "\t"; for (int i = 0; i < 8; ++i) o << (i ? " " : "") << hex32(x.s[i]);
                o << "\t"; for (int r = 0; r < 6; ++r) { if (r) o << ";"; for (int l = 0; l < 64; ++l) o << (l ? "," : "") << hex32(x.v[r][l]); }
            };
            dump(in, false); dump(st, true);
            o << "\t" << (skip.empty() ? "-" : skip);
            std::cout << o.str() << "\n";
        }
    }
    return 0;
}
