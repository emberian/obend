#!/usr/bin/env python3
"""The hardware & silicon verification + co-simulation suite (Obend.Hardware), in Verilator + Z3.

  * Z3 QF_BV safety barrier property sheets (`apps/foc-hil/verilator/foc_drive_props.smt2`,
    `apps/sdr-ft8/verilator/sdr_ft8_props.smt2`) prove `unsat`.
  * Yosys + Z3 logic equivalence (`hardware/lec/lec.sh`) across the 5 compiler-emitted SystemVerilog
    modules in `hardware/sim/` (`cleanroom_tcad_stack`, `cnc_5axis_userspace_mill`,
    `lc_drives_userspace_stator`, `obend_retimed_mac2`, `obend_width_probe`) when `yosys` and
    `obend-emit-sv` are present.
  * Verilator `-Wall` lint + cycle-accurate simulation (`Verilated::randReset(2)`, VCD trace) of
    `hardware/sim/tb_top.sv` + `sim_main.cpp` and standalone multi-clock `obend_width_probe.sv`.
  * Obend CLI Hardware Judge receipts (`hw-pnr-bitstream@1`, `hw-retime-sta@1`, `datasheet-fit@1`,
    `agentic-eda-swap@1`), binary RFC 8949 CBOR (`hw-binary-cbor@1` Tag 0x0BED + variable-length
    0x9A `hw-binary-tape-cbor@1`), sequential `obend lower` FSM synthesis, and live compiler-emitted
    SystemVerilog (`obend hardware emit-sv`) co-simulation when `.lake/build/bin/obend` is built.

usage: python3 tests/run-hardware.py
exit 0 when every check holds, 1 otherwise; a summary line last.
"""
import glob, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
REPO = os.path.dirname(LEAN)
HW_SIM = os.path.join(REPO, "hardware", "sim")
LEC_SH = os.path.join(REPO, "hardware", "lec", "lec.sh")

Z3 = shutil.which("z3") or "/opt/homebrew/bin/z3"
VERILATOR = shutil.which("verilator") or "/opt/homebrew/bin/verilator"
CXX = shutil.which("c++") or "/usr/bin/c++"
YOSYS = os.environ.get("YOSYS_BIN") or shutil.which("yosys") or "/Users/ember/tools/oss-cad-suite/bin/yosys"


def discover_verilator_include():
    env_root = os.environ.get("VERILATOR_ROOT")
    if env_root and os.path.isdir(os.path.join(env_root, "include")):
        return os.path.join(env_root, "include")
    try:
        r = subprocess.run([VERILATOR, "--getenv", "VERILATOR_ROOT"], capture_output=True, text=True)
        root = r.stdout.strip()
        if r.returncode == 0 and root:
            for cand in [os.path.join(root, "include"), os.path.join(root, "share", "verilator", "include")]:
                if os.path.isdir(cand):
                    return cand
    except OSError:
        pass
    matches = sorted(glob.glob("/opt/homebrew/Cellar/verilator/*/share/verilator/include"))
    if matches:
        return matches[-1]
    return "/usr/share/verilator/include"


VL_INC = discover_verilator_include()
DARWIN_LDFLAGS = (
    ["-Wl,-U,__Z15vl_time_stamp64v,-U,__Z13sc_time_stampv,-U,_vlog_startup_routines"]
    if sys.platform == "darwin"
    else []
)

failures = []
count = 0


def check(name, ok, detail=""):
    global count
    count += 1
    if not ok:
        failures.append(name)
        print(f"FAIL {name}: {detail}")
    else:
        print(f"ok   {name}")


with tempfile.TemporaryDirectory(prefix="obend_run_hw_") as work_dir:
    # 1. Z3 QF_BV Safety Property Sheets (FOC-HIL & SDR-FT8)
    foc_props = os.path.join(REPO, "apps", "foc-hil", "verilator", "foc_drive_props.smt2")
    r_foc_props = subprocess.run([Z3, "-smt2", foc_props], capture_output=True, text=True)
    check("z3 foc_drive_props.smt2: 1-cycle gate-kill, write-once latch & anti-windup safety (unsat)",
          r_foc_props.returncode == 0 and r_foc_props.stdout.strip() == "unsat",
          r_foc_props.stdout + r_foc_props.stderr)

    sdr_props = os.path.join(REPO, "apps", "sdr-ft8", "verilator", "sdr_ft8_props.smt2")
    r_sdr_props = subprocess.run([Z3, "-smt2", sdr_props], capture_output=True, text=True)
    check("z3 sdr_ft8_props.smt2: SDR-FT8 datapath & slicer property sheet (unsat)",
          r_sdr_props.returncode == 0 and r_sdr_props.stdout.strip() == "unsat",
          r_sdr_props.stdout + r_sdr_props.stderr)

    # 2. SMT-LIB Sharing Reducer Unit Tests
    r_smt_share = subprocess.run(
        [sys.executable, os.path.join(REPO, "hardware", "lec", "test_smt_share.py")],
        capture_output=True, text=True,
    )
    check("hardware/lec/test_smt_share.py: UNROLL equality sharing & check-sat-using fallback",
          r_smt_share.returncode == 0, r_smt_share.stdout + r_smt_share.stderr)

    # 3. Verilator -Wall Lint & Harness on Compiler-Emitted hardware/sim Modules
    r_lint_tb = subprocess.run(
        [VERILATOR, "--lint-only", "-Wall", "-Wno-DECLFILENAME", "-Wno-UNUSED",
         "--top-module", "tb_top", f"-I{HW_SIM}", os.path.join(HW_SIM, "tb_top.sv")],
        capture_output=True, text=True,
    )
    check("verilator -Wall lint: hardware/sim/tb_top.sv (4 compiler-emitted modules)",
          r_lint_tb.returncode == 0, r_lint_tb.stdout + r_lint_tb.stderr)

    r_lint_wp = subprocess.run(
        [VERILATOR, "--lint-only", "-Wall", "--top-module", "obend_width_probe",
         os.path.join(HW_SIM, "obend_width_probe.sv")],
        capture_output=True, text=True,
    )
    check("verilator -Wall lint: hardware/sim/obend_width_probe.sv (narrow widths & dual clock domains)",
          r_lint_wp.returncode == 0, r_lint_wp.stdout + r_lint_wp.stderr)

    obj_dir = os.path.join(work_dir, "obj_sim")
    r_build_tb = subprocess.run(
        [VERILATOR, "-Wall", "-Wno-DECLFILENAME", "-Wno-UNUSED",
         "--cc", "--exe", "--build", "--trace", "-j", "0",
         "-CFLAGS", "-std=c++20 -Wno-unused-variable",
         "--Mdir", obj_dir, "--top-module", "tb_top", f"-I{HW_SIM}",
         os.path.join(HW_SIM, "tb_top.sv"), os.path.join(HW_SIM, "sim_main.cpp"),
         "-o", "Vtb_top"],
        capture_output=True, text=True,
    )
    check("verilator --build --trace: hardware/sim/tb_top C++ simulation binary compiled",
          r_build_tb.returncode == 0, r_build_tb.stdout + r_build_tb.stderr)

    if r_build_tb.returncode == 0:
        r_sim = subprocess.run([os.path.join(obj_dir, "Vtb_top")], cwd=work_dir, capture_output=True, text=True)
        out = r_sim.stdout + r_sim.stderr
        check("verilator sim: cleanroom_tcad_stack, lc_drives_userspace_stator, cnc_5axis_userspace_mill & obend_retimed_mac2 exact",
              r_sim.returncode == 0 and "VERILATE_PASS module=tb_top mismatches=0" in out, out)

    # 4. Yosys + Z3 LEC on hardware/sim Modules (when obend-emit-sv and yosys are available)
    EMIT_SV_BIN = os.environ.get("OBEND_EMIT_SV") or os.path.join(LEAN, ".lake", "build", "bin", "obend-emit-sv")
    if os.path.exists(EMIT_SV_BIN) and os.path.exists(YOSYS):
        for target, stem, extra in [
            ("tcad", "cleanroom_tcad_stack", []),
            ("mill", "cnc_5axis_userspace_mill", []),
            ("stator", "lc_drives_userspace_stator", []),
            ("mac2", "obend_retimed_mac2", ["--no-eqy", "64x64 variable multiply"]),
            ("width-probe", "obend_width_probe", []),
        ]:
            lec_env = {**os.environ, "OBEND_EMIT_SV": EMIT_SV_BIN}
            r_lec = subprocess.run(
                [LEC_SH, target, os.path.join(HW_SIM, f"{stem}.sv"), os.path.join(HW_SIM, f"{stem}_lec.smt2"), *extra],
                cwd=HW_SIM, env=lec_env, capture_output=True, text=True,
            )
            check(f"yosys+z3 LEC ({target}): {stem}.sv == Lean RtlModule + planted mutation sat",
                  r_lec.returncode == 0 and f"LEC {stem}: unsat" in r_lec.stdout,
                  r_lec.stdout + r_lec.stderr)

    # 5. Obend CLI Hardware Judge Receipts, Binary CBOR, Lowering & Live emit-sv Co-Simulation
    OBEND_BIN = os.environ.get("OBEND_BIN") or os.path.join(LEAN, ".lake", "build", "bin", "obend")
    if os.path.exists(OBEND_BIN):
        pnr_receipt = os.path.join(work_dir, "pnr_receipt.json")
        r_pnr = subprocess.run([OBEND_BIN, "hardware", "verify-pnr", "--mode", "valid", "--out", pnr_receipt], capture_output=True, text=True)
        r_pnr_ver = subprocess.run([OBEND_BIN, "verify", pnr_receipt], capture_output=True, text=True)
        r_pnr_bad = subprocess.run([OBEND_BIN, "hardware", "verify-pnr", "--mode", "collision"], capture_output=True, text=True)
        check("obend hardware verify-pnr + obend verify (hw-pnr-bitstream@1 valid & collision refused)",
              r_pnr.returncode == 0 and r_pnr_ver.returncode == 0 and r_pnr_bad.returncode == 3,
              r_pnr.stdout + r_pnr_ver.stdout + r_pnr_bad.stderr)

        r_ret = subprocess.run([OBEND_BIN, "hardware", "verify-retime", "--lag1", "1"], capture_output=True, text=True)
        r_ret_bad = subprocess.run([OBEND_BIN, "hardware", "verify-retime", "--lag1", "3"], capture_output=True, text=True)
        check("obend hardware verify-retime (hw-retime-sta@1 lag=1 accepted & lag=3 refused)",
              r_ret.returncode == 0 and r_ret_bad.returncode == 3,
              r_ret.stdout + r_ret_bad.stderr)

        ds_receipt = os.path.join(work_dir, "datasheet_receipt.json")
        r_ds = subprocess.run([OBEND_BIN, "hardware", "datasheet-check", "--mode", "calibrated", "--out", ds_receipt], capture_output=True, text=True)
        r_ds_ver = subprocess.run([OBEND_BIN, "verify", ds_receipt], capture_output=True, text=True)
        r_ds_bad = subprocess.run([OBEND_BIN, "hardware", "datasheet-check", "--mode", "74ls_to_74hc_direct"], capture_output=True, text=True)
        check("obend hardware datasheet-check + obend verify (datasheet-fit@1 calibrated & 74LS->74HC direct refused)",
              r_ds.returncode == 0 and r_ds_ver.returncode == 0 and r_ds_bad.returncode == 3,
              r_ds.stdout + r_ds_ver.stdout + r_ds_bad.stderr)

        eda_receipt = os.path.join(work_dir, "eda_vault_receipt.json")
        r_eda = subprocess.run([OBEND_BIN, "hardware", "eda-vault-check", "--mode", "golden", "--out", eda_receipt], capture_output=True, text=True)
        r_eda_ver = subprocess.run([OBEND_BIN, "verify", eda_receipt], capture_output=True, text=True)
        r_eda_bad = subprocess.run([OBEND_BIN, "hardware", "eda-vault-check", "--mode", "overbudget"], capture_output=True, text=True)
        check("obend hardware eda-vault-check + obend verify (agentic-eda-swap@1 Vault smart-contract golden & overbudget refused)",
              r_eda.returncode == 0 and r_eda_ver.returncode == 0 and r_eda_bad.returncode == 3,
              r_eda.stdout + r_eda_ver.stdout + r_eda_bad.stderr)

        lean_bin = shutil.which("lean") or os.path.expanduser("~/.elan/bin/lean")
        sysroot = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.35.0")
        if os.path.exists(lean_bin):
            r_sr = subprocess.run([lean_bin, "--print-prefix"], capture_output=True, text=True)
            if r_sr.returncode == 0 and r_sr.stdout.strip():
                sysroot = r_sr.stdout.strip()

        seq_sv_path = os.path.join(work_dir, "lean_sumTo_seq_rtl.sv")
        lower_env = {**os.environ, "LEAN_SYSROOT": sysroot}
        r_seq = subprocess.run([OBEND_BIN, "lower", "sumTo", "--arg", "10", "--rtl", seq_sv_path],
                               cwd=LEAN, env=lower_env, capture_output=True, text=True)
        check("obend lower sumTo --arg 10 --rtl (sequential Nat.rec FSM synthesis & 10-cycle simulation sumTo 10 = 55)",
              r_seq.returncode == 0 and "sequential module lean_sumTo_seq_rtl verified" in r_seq.stdout and "rtl: sumTo 10 = 55 (cycles=10, done=1)" in r_seq.stdout,
              r_seq.stdout + r_seq.stderr)

        fib_sv_path = os.path.join(work_dir, "lean_fib_seq_rtl.sv")
        r_fib = subprocess.run([OBEND_BIN, "lower", "fib", "--arg", "10", "--rtl", fib_sv_path],
                               cwd=LEAN, env=lower_env, capture_output=True, text=True)
        check("obend lower fib --arg 10 --rtl (2-state tuple Nat.rec FSM synthesis & 10-cycle simulation fib 10 = 55)",
              r_fib.returncode == 0 and "sequential module lean_fib_seq_rtl verified" in r_fib.stdout and "rtl: fib 10 = 55 (cycles=10, done=1)" in r_fib.stdout,
              r_fib.stdout + r_fib.stderr)

        # 6. Binary RFC 8949 CBOR (hw-binary-cbor@1, Tag 0x0BED) + .obnb Core.Data + Rust FFI Interop Checks
        cbor_bin_path = os.path.join(work_dir, "hw_cert.cbor")
        obnb_cell_path = os.path.join(work_dir, "hw_cell.obnb")
        for dom in ["pnr", "photonics", "pcb", "dpr", "eda", "magnetics"]:
            r_cbor = subprocess.run(
                [OBEND_BIN, "hardware", "verify-cbor", "--domain", dom, "--out-bin", cbor_bin_path, "--out-obnb", obnb_cell_path],
                capture_output=True, text=True,
            )
            check(f"obend hardware verify-cbor --domain {dom} (39-byte RFC 8949 CBOR Tag 0x0BED + .obnb Core.Data cell)",
                  r_cbor.returncode == 0 and f"verified (hw-binary-cbor@1, domain={dom}, bytes=39, decidable, kernel)" in r_cbor.stdout,
                  r_cbor.stdout + r_cbor.stderr)

        r_cbor_bad = subprocess.run(
            [OBEND_BIN, "hardware", "verify-cbor", "--domain", "pnr", "--mode", "corrupt"],
            capture_output=True, text=True,
        )
        check("obend hardware verify-cbor --mode corrupt (refused by hw-binary-cbor@1 on real decoded parameters)",
              r_cbor_bad.returncode == 3, r_cbor_bad.stdout + r_cbor_bad.stderr)

        tape_cbor_path = os.path.join(work_dir, "hw_femm_tape.cbor")
        r_tape = subprocess.run(
            [OBEND_BIN, "hardware", "verify-cbor", "--domain", "magnetics", "--mode", "tape", "--out-bin", tape_cbor_path],
            capture_output=True, text=True,
        )
        check("obend hardware verify-cbor --domain magnetics --mode tape (variable-length 0x9A CBOR FEMM tape)",
              r_tape.returncode == 0 and "verified (hw-binary-cbor@1, domain=magnetics," in r_tape.stdout,
              r_tape.stdout + r_tape.stderr)

        RUST_HOST_BIN = os.path.join(REPO, "hardware", "rust-ffi", "target", "debug", "obend_hw_host")
        if os.path.exists(RUST_HOST_BIN):
            rust_cbor_path = os.path.join(work_dir, "rust_femm.cbor")
            r_rust_emit = subprocess.run(
                [RUST_HOST_BIN, "emit-cbor", "--domain", "magnetics", "--out", rust_cbor_path],
                capture_output=True, text=True,
            )
            r_lean_ver_rust = subprocess.run(
                [OBEND_BIN, "hardware", "verify-cbor", "--domain", "magnetics", "--in-bin", rust_cbor_path, "--out-obnb", obnb_cell_path],
                capture_output=True, text=True,
            )
            r_rust_obnb = subprocess.run(
                [RUST_HOST_BIN, "inspect-obnb", "--in", obnb_cell_path],
                capture_output=True, text=True,
            )
            check("Rust FFI <-> Lean Kernel binary CBOR + .obnb Core.Data round-trip (zero JSON)",
                  r_rust_emit.returncode == 0 and r_lean_ver_rust.returncode == 0 and r_rust_obnb.returncode == 0
                  and "Variant(\"hardwareSchematic\"" in r_rust_obnb.stdout,
                  r_rust_emit.stdout + r_lean_ver_rust.stdout + r_rust_obnb.stdout)

            femm_cbor_path = os.path.join(work_dir, "rust_solve-femm.cbor")
            r_rcmd = subprocess.run(
                [RUST_HOST_BIN, "solve-femm", "--out", femm_cbor_path],
                capture_output=True, text=True,
            )
            r_lver = subprocess.run(
                [OBEND_BIN, "hardware", "verify-cbor", "--domain", "magnetics", "--in-bin", femm_cbor_path, "--out-obnb", obnb_cell_path],
                capture_output=True, text=True,
            )
            check("Rust solve-femm -> variable-length RFC 8949 CBOR -> obend hardware verify-cbor (magnetics)",
                  r_rcmd.returncode == 0 and r_lver.returncode == 0
                  and "verified (hw-binary-cbor@1, domain=magnetics," in r_lver.stdout,
                  r_rcmd.stdout + r_rcmd.stderr + r_lver.stdout + r_lver.stderr)

            with open(femm_cbor_path, "rb") as f:
                valid_tape_bytes = f.read()
            trunc_cbor_path = os.path.join(work_dir, "rust_tape_trunc.cbor")
            with open(trunc_cbor_path, "wb") as f:
                f.write(valid_tape_bytes[:-1])
            trail_cbor_path = os.path.join(work_dir, "rust_tape_trail.cbor")
            with open(trail_cbor_path, "wb") as f:
                f.write(valid_tape_bytes + b"\x00")
            r_l_trunc = subprocess.run([OBEND_BIN, "hardware", "verify-cbor", "--domain", "magnetics", "--in-bin", trunc_cbor_path], capture_output=True, text=True)
            r_l_trail = subprocess.run([OBEND_BIN, "hardware", "verify-cbor", "--domain", "magnetics", "--in-bin", trail_cbor_path], capture_output=True, text=True)
            r_r_trunc = subprocess.run([RUST_HOST_BIN, "decode-cbor", "--in", trunc_cbor_path], capture_output=True, text=True)
            r_r_trail = subprocess.run([RUST_HOST_BIN, "decode-cbor", "--in", trail_cbor_path], capture_output=True, text=True)
            check("variable-length 0x9A CBOR adversarial framing (truncated & trailing garbage rejected by Lean & Rust)",
                  r_l_trunc.returncode == 3 and r_l_trail.returncode == 3
                  and r_r_trunc.returncode == 3 and r_r_trail.returncode == 3,
                  r_l_trunc.stderr + r_l_trail.stderr + r_r_trunc.stderr + r_r_trail.stderr)

        # 7. Userspace .obend Physical Engineering Suite (LcDrivesStatorUsd.obend & Cnc5AxisMill.obend)
        for ob_name, entry_name, expected_val in [
            ("LcDrivesStatorUsd.obend", "lcDrivesInSlotPeakTemp8kW", "result: 122"),
            ("Cnc5AxisMill.obend", "compensatedCommandSample", "result: 9976"),
        ]:
            ob_path = os.path.join(HERE, "obend-source", "world", "physical", ob_name)
            r_ob_chk = subprocess.run([OBEND_BIN, "check", ob_path], capture_output=True, text=True)
            r_ob_run = subprocess.run([OBEND_BIN, "run", ob_path, entry_name], capture_output=True, text=True)
            check(f"obend check + run world/physical/{ob_name} {entry_name} (userspace OpenUSD/CAM #law contracts & {expected_val})",
                  r_ob_chk.returncode == 0 and r_ob_run.returncode == 0 and expected_val in r_ob_run.stdout,
                  r_ob_chk.stdout + r_ob_chk.stderr + r_ob_run.stdout + r_ob_run.stderr)

        # 8. Live Compiler-Emitted SystemVerilog (emit-sv) + Verilator (-Wall) C++ Co-Simulation
        stator_sv = os.path.join(work_dir, "lc_drives_userspace_stator.sv")
        mill_sv = os.path.join(work_dir, "cnc_5axis_userspace_mill.sv")
        r_emit_stator = subprocess.run(
            [OBEND_BIN, "hardware", "emit-sv", "--module", "lc_drives_stator", "--out", stator_sv],
            capture_output=True, text=True,
        )
        r_emit_mill = subprocess.run(
            [OBEND_BIN, "hardware", "emit-sv", "--module", "cnc_5axis_mill", "--out", mill_sv],
            capture_output=True, text=True,
        )
        check("obend hardware emit-sv: synthesized SystemVerilog-2012 emitted for lc_drives_stator & cnc_5axis_mill",
              r_emit_stator.returncode == 0 and r_emit_mill.returncode == 0
              and os.path.exists(stator_sv) and os.path.exists(mill_sv),
              r_emit_stator.stdout + r_emit_stator.stderr + r_emit_mill.stdout + r_emit_mill.stderr)

        if os.path.exists(VERILATOR):
            up_tb_sv = os.path.join(work_dir, "userspace_phys_tb.sv")
            with open(up_tb_sv, "w") as f:
                f.write("""/* verilator lint_off UNUSED */
/* verilator lint_off DECLFILENAME */
module userspace_phys_tb (
  input  logic        clk,
  input  logic        rst,
  input  logic [63:0] stator_arg,
  input  logic [63:0] mill_arg,
  output logic [63:0] out_massKg,
  output logic [63:0] out_camSurfaceErrorUm,
  output logic [63:0] out_thermalResistance,
  output logic [63:0] out_sdfMargin,
  output logic [63:0] out_peakWindingTemp,
  output logic [63:0] out_servoLagUm,
  output logic [63:0] out_endMillDeflectionUm,
  output logic [63:0] out_abbeAngularDriftUm,
  output logic [63:0] out_commandedAxisAt10mmUm,
  output logic [63:0] out_totalVolumetricErrorUm
);
  lc_drives_userspace_stator u_stator (
    .clk(clk),
    .rst(rst),
    .arg(stator_arg),
    .out_massKg(out_massKg),
    .out_camSurfaceErrorUm(out_camSurfaceErrorUm),
    .out_thermalResistance(out_thermalResistance),
    .out_sdfMargin(out_sdfMargin),
    .out_peakWindingTemp(out_peakWindingTemp)
  );
  cnc_5axis_userspace_mill u_mill (
    .clk(clk),
    .rst(rst),
    .arg(mill_arg),
    .out_servoLagUm(out_servoLagUm),
    .out_endMillDeflectionUm(out_endMillDeflectionUm),
    .out_abbeAngularDriftUm(out_abbeAngularDriftUm),
    .out_commandedAxisAt10mmUm(out_commandedAxisAt10mmUm),
    .out_totalVolumetricErrorUm(out_totalVolumetricErrorUm)
  );
endmodule
""")

            up_main_cpp = os.path.join(work_dir, "userspace_phys_main.cpp")
            with open(up_main_cpp, "w") as f:
                f.write("""#include <cstdio>
#include <cstdlib>
#include "Vuserspace_phys_tb.h"
#include "verilated.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Vuserspace_phys_tb top;
    top.clk = 0;
    top.rst = 0;
    top.stator_arg = 8ULL;
    top.mill_arg = 6ULL;
    top.eval();
    top.clk = 1;
    top.eval();
    std::printf(
        "userspace_phys_sv: massKg=%llu camErr=%llu rTh=%llu sdfMargin=%llu peakWindingTemp=%llu | cmdAxis=%llu totalVolErr=%llu\\n",
        static_cast<unsigned long long>(top.out_massKg),
        static_cast<unsigned long long>(top.out_camSurfaceErrorUm),
        static_cast<unsigned long long>(top.out_thermalResistance),
        static_cast<unsigned long long>(top.out_sdfMargin),
        static_cast<unsigned long long>(top.out_peakWindingTemp),
        static_cast<unsigned long long>(top.out_commandedAxisAt10mmUm),
        static_cast<unsigned long long>(top.out_totalVolumetricErrorUm)
    );
    if (top.out_peakWindingTemp != 122ULL || top.out_sdfMargin != 24ULL ||
        top.out_commandedAxisAt10mmUm != 10024ULL || top.out_totalVolumetricErrorUm != 26ULL) {
        return 1;
    }
    return 0;
}
""")

            up_obj_dir = os.path.join(work_dir, "obj_userspace_phys")
            r_up_ver = subprocess.run([
                VERILATOR, "--cc", "--exe", "--build", "-j", "0",
                "-CFLAGS", "-std=c++20 -Wno-unused-variable",
                "--top-module", "userspace_phys_tb",
                "-sv", "-Wall",
                f"-I{work_dir}",
                stator_sv, mill_sv, up_tb_sv, up_main_cpp,
                "--Mdir", up_obj_dir, "-o", "sim_userspace_phys",
            ], capture_output=True, text=True)
            check("verilator (-Wall): compiler-emitted lc_drives_userspace_stator.sv & cnc_5axis_userspace_mill.sv build",
                  r_up_ver.returncode == 0, r_up_ver.stdout + r_up_ver.stderr)

            if r_up_ver.returncode == 0:
                r_up_sim = subprocess.run([os.path.join(up_obj_dir, "sim_userspace_phys")], capture_output=True, text=True)
                check("verilator co-sim: compiler-emitted SV matches Lean kernel (peakWindingTemp=122, sdfMargin=24, cmdAxis=10024, totalVolErr=26)",
                      r_up_sim.returncode == 0
                      and "peakWindingTemp=122" in r_up_sim.stdout and "sdfMargin=24" in r_up_sim.stdout
                      and "cmdAxis=10024" in r_up_sim.stdout and "totalVolErr=26" in r_up_sim.stdout,
                      r_up_sim.stdout + r_up_sim.stderr)

print(f"\nrun-hardware: {count - len(failures)}/{count} passed")
sys.exit(1 if failures else 0)
