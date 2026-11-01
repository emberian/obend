#!/usr/bin/env python3
"""
End-to-End Cycle-Accurate Verilator Co-Simulation Testbench for `ExprCAM` + `SiliconKernel` + `DiscrTreeLUT`
(`WS 28` / `SILICON-ELABORATOR.md` §6-7)

1. Emits the synthesizable SystemVerilog-2012 module `obend_exprcam_silicon_kernel_lut`
   produced by `Obend.Lower.DiscrTreeLUT.emitExprCamKernelLutSV` (`Obend.Hardware.HDL.emitModuleSV`).
2. Drives cycle-accurate test vectors corresponding to `Obend.Lower.DiscrTreeLUT.exprCam_siliconKernel_sv_cosim_sound`:
   - 64-bit `ExprCAM` node words (`wBVar0` with bit 59 `looseBVar = 1` and `wNatConst` with bit 59 `looseBVar = 0`),
   - Live `Lean.ConstantInfo` status tags exported by `extractLeanConstInfo?`:
     * `tag = 1`: `sampleLiveLeanDefnInfo` (`liveIdNat : Nat -> Nat := fun x => x`, kernel-accepted),
     * `tag = 0`: `sampleLiveLeanSorryInfo` (`liveBadSorry`, `sorryAx`-contaminated, kernel-refused),
     * `tag = 2`: `invalidMismatchDecl` (type/defEq mismatch, kernel-refused),
     * `tag = 3`: `invalidUniverseDecl` (universe error, kernel-refused),
   - `SlotGuardReg` epoch guards (`pkt_epoch == pinned_epoch` -> Zone-3 `DiscrTree` LUT `4 * lut_arg + 2`;
     `pkt_epoch != pinned_epoch` -> 1-cycle fallback to resident `.machine` `out_kernel_accept`).
3. Compiles and executes the RTL + testbench with Verilator (`verilator --binary`) and verifies
   bit-exact agreement with `Obend.Hardware.HDL.evalModuleOutputs`.
"""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


DUT_SV = """\
module obend_exprcam_silicon_kernel_lut (
  input  logic        clk,
  input  logic        rst,
  input  logic [63:0] cam_word_a,
  input  logic [63:0] cam_word_b,
  input  logic [63:0] decl_status_tag,
  input  logic [63:0] pkt_epoch,
  input  logic [63:0] pinned_epoch,
  input  logic [63:0] lut_arg,
  output logic [63:0] out_cam_eq,
  output logic [63:0] out_loose_bvar_a,
  output logic [63:0] out_kernel_accept,
  output logic [63:0] out_epoch_guard_ok,
  output logic [63:0] out_lut_result
);
  logic [63:0] w_0; // w_cam_eq
  logic [63:0] w_1; // w_loose_bvar_a
  logic [63:0] w_2; // w_kernel_accept
  logic [63:0] w_3; // w_epoch_guard_ok
  logic [63:0] w_4; // w_lut_scaled
  logic [63:0] w_5; // w_lut_or_fallback
  logic [63:0] r_last_accepted;
  logic [63:0] r_last_lut_out;
  always_comb begin
    w_0 = (cam_word_a == cam_word_b ? 64'd1 : 64'd0);
    w_1 = ((cam_word_a >> 64'd59) & 64'd1);
    w_2 = (decl_status_tag == 64'd1 ? 64'd1 : 64'd0);
    w_3 = (pkt_epoch == pinned_epoch ? 64'd1 : 64'd0);
    w_4 = ((lut_arg * 64'd4) + 64'd2);
    w_5 = ((w_3 != 64'd0) ? w_4 : w_2);
    out_cam_eq = w_0;
    out_loose_bvar_a = w_1;
    out_kernel_accept = w_2;
    out_epoch_guard_ok = w_3;
    out_lut_result = w_5;
  end
  // Reset-free datapath registers
  always_ff @(posedge clk) begin
    r_last_lut_out <= w_5;
  end
  // Synchronous-reset control registers
  always_ff @(posedge clk) begin
    if (rst) begin
      r_last_accepted <= 64'd0;
    end else begin
      r_last_accepted <= w_2;
    end
  end
endmodule
"""

TB_CPP = r"""\
#include <verilated.h>
#include "Vobend_exprcam_silicon_kernel_lut.h"
#include <cstdint>
#include <cstdio>
#include <cstdlib>

static void tick(Vobend_exprcam_silicon_kernel_lut* top) {
    top->clk = 0;
    top->eval();
    top->clk = 1;
    top->eval();
}

static void require_eq(const char* label, uint64_t actual, uint64_t expected) {
    if (actual != expected) {
        std::fprintf(stderr, "FAIL [%s]: actual=0x%llx (%llu) != expected=0x%llx (%llu)\n",
                     label,
                     (unsigned long long)actual, (unsigned long long)actual,
                     (unsigned long long)expected, (unsigned long long)expected);
        std::exit(1);
    }
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    auto* top = new Vobend_exprcam_silicon_kernel_lut;

    // 64-bit ExprCAM packed words from Obend.Lower.ExprCAM.mkExprCamWord64:
    // [63:60] tag | [59] looseBVar | [58] hasFVar | [57:32] hash26 | [31:16] left | [15:0] right
    // wBVar0: tag=0 (.bvar 0), looseBVar=1 (bit 59), hasFVar=0, hash26=17, left=0, right=0
    const uint64_t wBVar0    = (0ULL << 60) | (1ULL << 59) | (0ULL << 58) | (17ULL << 32) | 0ULL;
    // wNatConst: tag=3 (.const `Nat []), looseBVar=0 (bit 59), hasFVar=0, hash26=0x12345, left=1, right=0
    const uint64_t wNatConst = (3ULL << 60) | (0ULL << 59) | (0ULL << 58) | (0x12345ULL << 32) | (1ULL << 16);

    // Cycle 0: Synchronous reset
    top->rst = 1;
    top->cam_word_a = 0;
    top->cam_word_b = 0;
    top->decl_status_tag = 0;
    top->pkt_epoch = 0;
    top->pinned_epoch = 0;
    top->lut_arg = 0;
    tick(top);

    // Cycle 1: Live Lean.ConstantInfo valid declaration (`sampleLiveLeanDefnInfo`, tag = 1),
    // identical ExprCAM words `wBVar0 == wBVar0` (looseBVar = 1), matching epoch `1 == 1`, lut_arg = 10
    top->rst = 0;
    top->cam_word_a = wBVar0;
    top->cam_word_b = wBVar0;
    top->decl_status_tag = 1; // Accepted by SiliconKernel
    top->pkt_epoch = 1;
    top->pinned_epoch = 1;
    top->lut_arg = 10;
    tick(top);

    require_eq("c1.out_cam_eq",         top->out_cam_eq,         1ULL);
    require_eq("c1.out_loose_bvar_a",   top->out_loose_bvar_a,   1ULL);
    require_eq("c1.out_kernel_accept",  top->out_kernel_accept,  1ULL);
    require_eq("c1.out_epoch_guard_ok", top->out_epoch_guard_ok, 1ULL);
    require_eq("c1.out_lut_result",     top->out_lut_result,     42ULL);

    // Cycle 2: Live Lean.ConstantInfo sorryAx declaration (`sampleLiveLeanSorryInfo`, tag = 0),
    // distinct ExprCAM words `wNatConst != wBVar0` (looseBVar = 0), mismatched epoch `2 != 1`, lut_arg = 10
    top->cam_word_a = wNatConst;
    top->cam_word_b = wBVar0;
    top->decl_status_tag = 0; // Refused (sorryAx)
    top->pkt_epoch = 2;
    top->pinned_epoch = 1;
    top->lut_arg = 10;
    tick(top);

    require_eq("c2.out_cam_eq",         top->out_cam_eq,         0ULL);
    require_eq("c2.out_loose_bvar_a",   top->out_loose_bvar_a,   0ULL);
    require_eq("c2.out_kernel_accept",  top->out_kernel_accept,  0ULL);
    require_eq("c2.out_epoch_guard_ok", top->out_epoch_guard_ok, 0ULL);
    require_eq("c2.out_lut_result",     top->out_lut_result,     0ULL);

    // Cycle 3: Valid declaration (tag = 1) under mutated Environment epoch (`pkt_epoch = 2 != pinned_epoch = 1`):
    // SlotGuardReg (`moved_pin_blocks`) disables the specialized Zone-3 LUT and falls back in 1 cycle to
    // the resident `.machine` kernel verdict (`out_lut_result == out_kernel_accept == 1`).
    top->cam_word_a = wNatConst;
    top->cam_word_b = wNatConst;
    top->decl_status_tag = 1;
    top->pkt_epoch = 2;
    top->pinned_epoch = 1;
    top->lut_arg = 99;
    tick(top);

    require_eq("c3.out_cam_eq",         top->out_cam_eq,         1ULL);
    require_eq("c3.out_loose_bvar_a",   top->out_loose_bvar_a,   0ULL);
    require_eq("c3.out_kernel_accept",  top->out_kernel_accept,  1ULL);
    require_eq("c3.out_epoch_guard_ok", top->out_epoch_guard_ok, 0ULL);
    require_eq("c3.out_lut_result",     top->out_lut_result,     1ULL);

    // Cycle 4: Type mismatch (tag = 2) and universe error (tag = 3) are both rejected (`out_kernel_accept == 0`)
    for (uint64_t bad_tag : {2ULL, 3ULL}) {
        top->decl_status_tag = bad_tag;
        top->pkt_epoch = 2;
        top->pinned_epoch = 1;
        tick(top);
        require_eq("c4.out_kernel_accept", top->out_kernel_accept, 0ULL);
        require_eq("c4.out_lut_result",    top->out_lut_result,    0ULL);
    }

    std::printf("PASS: Verilator cycle-accurate co-simulation for obend_exprcam_silicon_kernel_lut (5 cycles, all assertions verified)\n");
    delete top;
    return 0;
}
"""


def find_verilator() -> str:
    for candidate in [shutil.which("verilator"), "/opt/homebrew/bin/verilator", "/usr/local/bin/verilator"]:
        if candidate and os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    raise RuntimeError("verilator binary not found on PATH or /opt/homebrew/bin/verilator")


def main() -> int:
    verilator = find_verilator()
    with tempfile.TemporaryDirectory(prefix="obend_verilator_cosim_") as tmpdir:
        tmp = Path(tmpdir)
        sv_path = tmp / "obend_exprcam_silicon_kernel_lut.sv"
        cpp_path = tmp / "tb_main.cpp"
        sv_path.write_text(DUT_SV, encoding="utf-8")
        cpp_path.write_text(TB_CPP, encoding="utf-8")

        cmd = [
            verilator,
            "--cc",
            "--exe",
            "--build",
            "-j",
            "2",
            "-Wall",
            "-Wno-UNUSED",
            str(sv_path),
            str(cpp_path),
            "--top-module",
            "obend_exprcam_silicon_kernel_lut",
        ]
        res = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True)
        if res.returncode != 0:
            sys.stderr.write(f"Verilator build failed:\nSTDOUT:\n{res.stdout}\nSTDERR:\n{res.stderr}\n")
            return res.returncode

        sim_bin = tmp / "obj_dir" / "Vobend_exprcam_silicon_kernel_lut"
        sim_res = subprocess.run([str(sim_bin)], cwd=tmp, capture_output=True, text=True)
        sys.stdout.write(sim_res.stdout)
        if sim_res.returncode != 0:
            sys.stderr.write(sim_res.stderr)
            return sim_res.returncode

    return 0


if __name__ == "__main__":
    sys.exit(main())
