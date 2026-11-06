#!/usr/bin/env python3
"""Differential vectors for Obend.Hardware.Gpu.Rdna2.Semantics against gem5's Vega execute() bodies.

    python3 -I gem5_ref.py OUT.tsv [--llvm-mc PATH] [--seed N] [--trials N]

Assembles each twin instruction below with llvm-mc (gfx1031, wave64) in the fixed register assignment
gem5_ref.cpp expects, compiles gem5_ref.cpp, and writes its rows: for random register states (EXEC all
ones, all zeros, then random), the state after the instruction per the ported gem5 body. The Lean replay
(`obend-rdna2 gem5 OUT.tsv`, `Obend.Teeth.Hardware.Rdna2Runs`) decodes the same words, runs `step` from
the same state and compares every register, except the fields the row's last column names as a known
RDNA2 departure from Vega.
"""
import os
import subprocess
import sys
import tempfile

# (model name as the Lean step sees it, asm text in the fixed assignment, gem5 twin)
TWINS = [
    ("V_ADD_CO_U32", "v_add_co_u32 v4, vcc, v0, v1", "Inst_VOP3__V_ADD_CO_U32"),
    ("V_SUB_CO_U32", "v_sub_co_u32 v4, vcc, v0, v1", "Inst_VOP3__V_SUB_CO_U32"),
    ("V_ADD_CO_CI_U32", "v_add_co_ci_u32_e64 v4, s[4:5], v0, v1, s[2:3]", "Inst_VOP3__V_ADDC_CO_U32"),
    ("V_SUB_CO_CI_U32", "v_sub_co_ci_u32_e64 v4, s[4:5], v0, v1, s[2:3]", "Inst_VOP3__V_SUBB_CO_U32"),
    ("V_ADD_CO_CI_U32_E32", "v_add_co_ci_u32_e32 v4, vcc, v0, v1, vcc", "Inst_VOP2__V_ADDC_CO_U32"),
    ("V_SUB_CO_CI_U32_E32", "v_sub_co_ci_u32_e32 v4, vcc, v0, v1, vcc", "Inst_VOP2__V_SUBB_CO_U32"),
    ("V_ADD_NC_U32", "v_add_nc_u32_e32 v4, v0, v1", "Inst_VOP2__V_ADD_U32"),
    ("V_MOV_B32", "v_mov_b32_e32 v4, v0", "Inst_VOP1__V_MOV_B32"),
    ("V_AND_B32", "v_and_b32_e32 v4, v0, v1", "Inst_VOP2__V_AND_B32"),
    ("V_OR_B32", "v_or_b32_e32 v4, v0, v1", "Inst_VOP2__V_OR_B32"),
    ("V_LSHLREV_B32", "v_lshlrev_b32_e32 v4, v0, v1", "Inst_VOP2__V_LSHLREV_B32"),
    ("V_LSHL_ADD_U32", "v_lshl_add_u32 v4, v0, v1, v2", "Inst_VOP3__V_LSHL_ADD_U32"),
    ("V_ADD3_U32", "v_add3_u32 v4, v0, v1, v2", "Inst_VOP3__V_ADD3_U32"),
    ("V_AND_OR_B32", "v_and_or_b32 v4, v0, v1, v2", "Inst_VOP3__V_AND_OR_B32"),
    ("V_MUL_LO_U32", "v_mul_lo_u32 v4, v0, v1", "Inst_VOP3__V_MUL_LO_U32"),
    ("V_MUL_HI_U32", "v_mul_hi_u32 v4, v0, v1", "Inst_VOP3__V_MUL_HI_U32"),
    ("V_LSHLREV_B64", "v_lshlrev_b64 v[4:5], v0, v[2:3]", "Inst_VOP3__V_LSHLREV_B64"),
    ("V_LSHRREV_B64", "v_lshrrev_b64 v[4:5], v0, v[2:3]", "Inst_VOP3__V_LSHRREV_B64"),
    ("V_CNDMASK_B32", "v_cndmask_b32_e64 v4, v0, v1, s[2:3]", "Inst_VOP3__V_CNDMASK_B32"),
    ("V_CNDMASK_B32_E32", "v_cndmask_b32_e32 v4, v0, v1, vcc", "Inst_VOP2__V_CNDMASK_B32"),
    ("V_CMP_LE_U32", "v_cmp_le_u32_e64 s[4:5], v0, v1", "Inst_VOP3__V_CMP_LE_U32"),
    ("V_CMP_GT_U32", "v_cmp_gt_u32_e64 s[4:5], v0, v1", "Inst_VOP3__V_CMP_GT_U32"),
    ("V_CMP_LE_U32_E32", "v_cmp_le_u32_e32 vcc, v0, v1", "Inst_VOPC__V_CMP_LE_U32"),
    ("V_CMP_GT_U32_E32", "v_cmp_gt_u32_e32 vcc, v0, v1", "Inst_VOPC__V_CMP_GT_U32"),
    ("V_CMPX_GT_U32_E32", "v_cmpx_gt_u32_e32 v0, v1", "Inst_VOPC__V_CMPX_GT_U32"),
    ("V_CMP_LT_U64", "v_cmp_lt_u64_e64 s[4:5], v[0:1], v[2:3]", "Inst_VOP3__V_CMP_LT_U64"),
    ("V_CMP_NE_I64", "v_cmp_ne_i64_e64 s[4:5], v[0:1], v[2:3]", "Inst_VOP3__V_CMP_NE_I64"),
    ("S_MOV_B32", "s_mov_b32 s4, s0", "Inst_SOP1__S_MOV_B32"),
    ("S_MOV_B64", "s_mov_b64 s[4:5], s[0:1]", "Inst_SOP1__S_MOV_B64"),
    ("S_MOVK_I32", "s_movk_i32 s4, 0x8123", "Inst_SOPK__S_MOVK_I32"),
    ("S_AND_B64", "s_and_b64 s[4:5], s[0:1], s[2:3]", "Inst_SOP2__S_AND_B64"),
    ("S_CBRANCH_EXECZ", "s_cbranch_execz 5", "Inst_SOPP__S_CBRANCH_EXECZ"),
    ("S_ENDPGM", "s_endpgm", "Inst_SOPP__S_ENDPGM"),
    ("S_WAITCNT", "s_waitcnt vmcnt(0)", "Inst_SOPP__S_WAITCNT"),
]


def main() -> int:
    args = sys.argv[1:]
    out = args[0]
    llvm_mc = "/usr/lib/llvm-19/bin/llvm-mc"
    seed, trials = 1, 6
    i = 1
    while i < len(args):
        if args[i] == "--llvm-mc":
            llvm_mc = args[i + 1]; i += 2
        elif args[i] == "--seed":
            seed = int(args[i + 1]); i += 2
        elif args[i] == "--trials":
            trials = int(args[i + 1]); i += 2
        else:
            raise SystemExit(__doc__)
    here = os.path.dirname(os.path.abspath(__file__))
    lines = []
    for name, asm, twin in TWINS:
        r = subprocess.run([llvm_mc, "-triple=amdgcn-amd-amdhsa", "-mcpu=gfx1031", "-mattr=+wavefrontsize64", "--show-encoding"],
                           input=asm + "\n", capture_output=True, text=True, check=True)
        enc = [ln for ln in r.stdout.splitlines() if "encoding:" in ln][0].split("encoding:")[1].strip().strip("[]")
        bs = [int(b, 16) for b in enc.split(",")]
        words = ["%08x" % (bs[k] | bs[k + 1] << 8 | bs[k + 2] << 16 | bs[k + 3] << 24) for k in range(0, len(bs), 4)]
        lines.append(f"{name} {' '.join(words)}")
    with tempfile.TemporaryDirectory() as tmp:
        exe = os.path.join(tmp, "gem5_ref")
        subprocess.run(["g++", "-O1", "-std=c++17", "-o", exe, os.path.join(here, "gem5_ref.cpp")], check=True)
        r = subprocess.run([exe, str(seed), str(trials)], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True)
    header = ("# Differential vectors: gem5's Vega execute() bodies (hardware/gpu/rdna2/gem5_ref.cpp, each case cites its\n"
              "# file:line) on random register states; written by gem5_ref.py (seed %d, %d trials per instruction, words\n"
              "# from llvm-mc gfx1031 wave64). Columns: name, dwords, exec vcc scc, s0..s7, v0..v5 per lane, then the\n"
              "# same after the instruction with pc, then the fields the RDNA2 model is known to differ in (or -).\n"
              "# Twins:\n" % (seed, trials))
    header += "".join(f"#   {name}: {asm}  <-  {twin}\n" for name, asm, twin in TWINS)
    open(out, "w").write(header + r.stdout)
    print(f"{len(TWINS)} instructions x {trials} trials -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
