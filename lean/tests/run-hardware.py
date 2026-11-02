#!/usr/bin/env python3
"""The hardware & silicon co-simulation suite end to end (Obend.Hardware), in Verilator 5.050 + Z3.

  * Z3 gate-level & fabric logic equivalence / security checks (`lec_check.smt2`, `lec_fabric.smt2`)
    prove `unsat` (zero counterexamples across 64-bit inputs) for:
      - 64-bit adder mapped onto `LUT2(4'h6)` + `CARRY8` fast-carry muxes vs `(bvadd a b)`,
      - `ReviewMember.obend` 2-stage pipeline (`twice_s2 == spec_s2`),
      - 2x2 eFPGA mesh configured with `TwiceReview.obend` bitstream (`out_01 == v + 4`),
      - `DeosCounter.obend` + `Vault.Law` `writeOnce` hardware register guard.
  * Verilator 5.050 cycle-accurate co-simulation (`--x-assign unique --x-initial unique`,
    `Verilated::randReset(2)`) across 15 SystemVerilog modules and 10 hardware suites:
      1. Demand Wave Chip (`evalDemand` on 4-slot chain + divergent `bad = self.bad`),
      2. 4-Stage Reset-Free `DSP48E2`/`DSP58` MAC (`7 * 9 + 100 = 163`),
      3. Unreset `URAM288`/SRAM Boot Zero-Sweep FSM + RAW Collision Bypass,
      4. 2-Slot Zero-Combinational-`TREADY` AXI4-Stream Skid Buffer under backpressure stalls,
      5. 64-Bit eFPGA (FABulous / fabublox) Bitstream-Configured BLE Adder,
      6. `ReviewMember.obend` 2-Stage Silicon Pipeline (`twice(1000,333) = 1666`, `claim_repeated_ok = 1`),
      7. Streaming `Obend.Ledger` Co-Processor (trial-balance conservation + refusal codes `{1,2,3}`),
      8. 2x2 eFPGA Mesh + Frame Loader (`TwiceReview.obend`: `twiceOfThree = 7`, post-lock immutability),
      9. Hardware Merkle-View Receipt Verifier (`Obend.Receipt.Merkle`: 4/4 openings accepted, 4/4 tampered rejected),
     10. `DeosCounter.obend` + `Vault.Law` Guard (uncredentialed reset refused, `writeOnce` enforced, credentialed reset zeros count).

usage: python3 tests/run-hardware.py
exit 0 when every check holds, 1 otherwise; a summary line last.
"""
import os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
REPO = os.path.dirname(LEAN)
HW_SIM = os.path.join(REPO, "hardware", "sim")

Z3 = "/opt/homebrew/bin/z3"
VERILATOR = "/opt/homebrew/bin/verilator"
CXX = "/usr/bin/c++"
VL_INC = "/opt/homebrew/Cellar/verilator/5.050/share/verilator/include"

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


# 1. Z3 Gate-Level BEL + ReviewMember LEC Check
r_lec1 = subprocess.run([Z3, os.path.join(HW_SIM, "lec_check.smt2")], capture_output=True, text=True)
check("z3 lec_check.smt2: LUT2+CARRY8 64b adder & ReviewMember pipeline equivalence (unsat)",
      r_lec1.returncode == 0 and r_lec1.stdout.strip() == "unsat", r_lec1.stdout + r_lec1.stderr)

# 2. Z3 2x2 eFPGA TwiceReview + Vault.Law writeOnce LEC Check
r_lec2 = subprocess.run([Z3, os.path.join(HW_SIM, "lec_fabric.smt2")], capture_output=True, text=True)
check("z3 lec_fabric.smt2: 2x2 eFPGA TwiceReview mesh & Vault.Law writeOnce security (unsat)",
      r_lec2.returncode == 0 and r_lec2.stdout.strip() == "unsat", r_lec2.stdout + r_lec2.stderr)

# 3. Z3 Compiler (compileBookToRtl), Synth (CARRY8 sub) & FabuBlox Facility OS Safety Check
r_lec3 = subprocess.run([Z3, os.path.join(HW_SIM, "lec_compiler_fabublox.smt2")], capture_output=True, text=True)
check("z3 lec_compiler_fabublox.smt2: compileBookToRtl, CARRY8 sub & FabuBlox Facility OS (unsat)",
      r_lec3.returncode == 0 and r_lec3.stdout.strip() == "unsat", r_lec3.stdout + r_lec3.stderr)

# 4. Z3 Types Slice Lenses, Leiserson-Saxe Retiming, Analog ABBA Common-Centroid & 4-bit SAR ADC Check
r_lec4 = subprocess.run([Z3, os.path.join(HW_SIM, "lec_ams_waferspace.smt2")], capture_output=True, text=True)
check("z3 lec_ams_waferspace.smt2: Types slices, Retiming MAC, ABBA centroid & 4b SAR ADC (unsat)",
      r_lec4.returncode == 0 and r_lec4.stdout.strip() == "unsat", r_lec4.stdout + r_lec4.stderr)

# 5. Z3 QF_NRA Real Multiphysics, Bandgap Zero-TC, 74LS/74HCT Calibration & RF Conjugate Match Check
r_lec5 = subprocess.run([Z3, os.path.join(HW_SIM, "lec_multiphysics_rf.smt2")], capture_output=True, text=True)
check("z3 lec_multiphysics_rf.smt2: QF_NRA RF conjugate match, Bandgap zero-TC, 74LS fit & Tayloe I/Q (unsat)",
      r_lec5.returncode == 0 and r_lec5.stdout.strip() == "unsat", r_lec5.stdout + r_lec5.stderr)

# 6. Verilator 5.050 RTL Elaboration & Lint Check
obj_dir = os.path.join(HW_SIM, "obj_dir")
r_verilate = subprocess.run([
    VERILATOR, "--cc", "--exe", "--top-module", "tb_top",
    "-sv", "-Wall", "-Wno-DECLFILENAME", "-Wno-UNUSED",
    "--x-assign", "unique", "--x-initial", "unique",
    f"-I{HW_SIM}",
    os.path.join(HW_SIM, "tb_top.sv"),
    os.path.join(HW_SIM, "sim_main.cpp"),
    "--Mdir", obj_dir,
], capture_output=True, text=True)
check("verilator 5.050: 15-module SystemVerilog elaboration with -Wall & X-randomization",
      r_verilate.returncode == 0, r_verilate.stdout + r_verilate.stderr)

# 7. C++ Compilation & Execution of Verilated Silicon Model
sim_bin = os.path.join(obj_dir, "sim_obend")
vtb_cpps = [
    os.path.join(obj_dir, f)
    for f in sorted(os.listdir(obj_dir))
    if f.startswith("Vtb_top") and f.endswith(".cpp") and f != "Vtb_top__ALL.cpp"
]
r_cxx = subprocess.run([
    CXX, "-Os", "-std=c++20",
    f"-I{obj_dir}", f"-I{VL_INC}", f"-I{VL_INC}/vltstd",
    "-Wl,-U,__Z15vl_time_stamp64v,-U,__Z13sc_time_stampv,-U,_vlog_startup_routines",
    os.path.join(HW_SIM, "sim_main.cpp"),
    *vtb_cpps,
    os.path.join(VL_INC, "verilated.cpp"),
    os.path.join(VL_INC, "verilated_threads.cpp"),
    "-o", sim_bin,
], capture_output=True, text=True)
check("c++ build: Verilator cycle-accurate simulation binary compiled",
      r_cxx.returncode == 0, r_cxx.stdout + r_cxx.stderr)

r_sim = subprocess.run([sim_bin], capture_output=True, text=True)
out = r_sim.stdout + r_sim.stderr
check("sim suite 1: Demand Wave Chip (slot_valid=0b7, divergent bad=0)",
      r_sim.returncode == 0 and "1. Wave Chip (evalDemand): slot_valid=0b7, a=42, b=42, c=42" in out, out)
check("sim suite 2: 4-Stage Reset-Free DSP48E2/58 MAC (7 * 9 + 100 = 163)",
      "2. DSP48E2/58 4-Stage Reset-Free MAC: 7 * 9 + 100 = 163" in out, out)
check("sim suite 3: URAM288 Boot Zero-Sweep + RAW Collision Bypass",
      "3. URAM288 Boot Zero-Sweep + RAW Collision Bypass: 16/16 words zeroed, RDW bypass=0x123456789abcdef0" in out, out)
check("sim suite 4: 2-Slot AXI4-Stream Skid Buffer lossless under stalls",
      "4. AXI4-Stream 2-Slot Skid Buffer: 7/7 words transferred losslessly under stalls" in out, out)
check("sim suite 5: 64-Tile eFPGA (FABulous/fabublox) Bitstream Adder",
      "5. eFPGA (FABulous/fabublox) 64-Tile Bitstream Adder: 5/5 64-bit vectors exact" in out, out)
check("sim suite 6: ReviewMember.obend 2-Stage Silicon Pipeline (claim_repeated_ok=1)",
      "6. ReviewMember.obend 2-Stage Silicon Pipeline: twice(1000,333)=1666, claim_repeated_ok=1" in out, out)
check("sim suite 7: Streaming Ledger Co-Processor conservation & refusal codes",
      "7. Streaming Ledger Co-Processor: debits=500, credits=500, closedThrough=2, refusals={1,2,3} exact" in out, out)
check("sim suite 8: 2x2 eFPGA Mesh + Frame Loader (TwiceReview: twiceOfThree=7, lock immutable)",
      "8. 2x2 eFPGA Mesh + Frame Loader (TwiceReview.obend): twiceOfThree=7, post-lock immutable=PASS" in out, out)
check("sim suite 9: Hardware Merkle-View Receipt Verifier (4/4 accepted, 4/4 tampered rejected)",
      "9. Merkle-View Receipt Verifier (Obend/Receipt/Merkle.lean): 4/4 openings accepted, 4/4 tampered rejected" in out, out)
check("sim suite 10: DeosCounter.obend + Vault.Law Capability-Guarded Register Bank",
      "10. DeosCounter.obend + Vault.Law Guard: uncred reset=REFUSED(count=35), writeOnce=0xbeef, cred reset=0" in out, out)

# 8. C++20 Continuous-Time Multiphysics (Electro-Thermal RK4, SN74LS00 Datasheet, Pt100 INA & 40m FT8 RF)
mp_bin = os.path.join(obj_dir, "multiphysics_sim")
r_mp_cxx = subprocess.run([
    CXX, "-Os", "-std=c++20",
    os.path.join(HW_SIM, "multiphysics_sim.cpp"),
    "-o", mp_bin,
], capture_output=True, text=True)
check("c++ build: Continuous-time multiphysics & RF simulator compiled",
      r_mp_cxx.returncode == 0, r_mp_cxx.stdout + r_mp_cxx.stderr)

r_mp = subprocess.run([mp_bin], capture_output=True, text=True)
mp_out = r_mp.stdout + r_mp.stderr
check("multiphysics suite A: Electro-Thermal RK4 BJT + Schmitt TSD (Tj=84.2 C, trip=150 C, recover=130 C, chatter=0)",
      r_mp.returncode == 0 and "A. Electro-Thermal RK4 + Schmitt TSD: ballasted Tj=84.2 C, TSD trip=150.0 C, recover=130.0 C, chatter=0, Vbg=1.220 V" in mp_out, mp_out)
check("multiphysics suite B: SN74LS00 Totem-Pole NAND Datasheet Fit (VOL=0.34 V, VOH=3.38 V, L_inf=14.2 mV)",
      "B. SN74LS00 Datasheet Calibration: VOL=0.34 V, VOH=3.38 V, tpLH=9.2 ns, tpHL=8.4 ns, L_inf=14.2 mV <= 25.0 mV" in mp_out, mp_out)
check("multiphysics suite C: Pt100 RTD Bridge + 3-Op-Amp INA (CMRR=100 dB, 60Hz hum=5.0 uV, err=0.013 C)",
      "C. Pt100 Bridge + 3-Op-Amp INA: CMRR=100 dB, 60Hz hum=5.0 uV < 10 uV, max temp err=0.013 C < 0.05 C" in mp_out, mp_out)
check("multiphysics suite D: 40m (7.074 MHz FT8) Ham Radio Transceiver (VSWR=1.002, IRR=52.4 dB, Harmonics=-58.6 dBc)",
      "D. 40m (7.074 MHz FT8) RF Transceiver: Zin=50.0+j0.0 Ohm, VSWR=1.002, Tayloe IRR=52.4 dB, Friis NF=1.84 dB, Harmonics=-58.6 dBc" in mp_out, mp_out)

# 9. Obend CLI Hardware, FabuBlox, wafer.space, Datasheet-Fit & RF Transceiver Judge Receipt Checks
OBEND_BIN = os.path.join(LEAN, ".lake", "build", "bin", "obend")
if os.path.exists(OBEND_BIN):
    pnr_receipt = os.path.join(obj_dir, "pnr_receipt.json")
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

    ws_receipt = os.path.join(obj_dir, "waferspace_receipt.json")
    r_ws = subprocess.run([OBEND_BIN, "hardware", "waferspace-signoff", "--mode", "golden", "--out", ws_receipt], capture_output=True, text=True)
    r_ws_ver = subprocess.run([OBEND_BIN, "verify", ws_receipt], capture_output=True, text=True)
    r_ws_bad = subprocess.run([OBEND_BIN, "hardware", "waferspace-signoff", "--mode", "bad_antenna"], capture_output=True, text=True)
    check("obend hardware waferspace-signoff + obend verify (waferspace-signoff@1 GF180MCU golden & antenna refused)",
          r_ws.returncode == 0 and r_ws_ver.returncode == 0 and r_ws_bad.returncode == 3,
          r_ws.stdout + r_ws_ver.stdout + r_ws_bad.stderr)

    fb_receipt = os.path.join(obj_dir, "fabublox_receipt.json")
    r_fb = subprocess.run([OBEND_BIN, "fabublox", "check", "--recipe", "damascene", "--out", fb_receipt], capture_output=True, text=True)
    r_fb_ver = subprocess.run([OBEND_BIN, "verify", fb_receipt], capture_output=True, text=True)
    r_fb_bad = subprocess.run([OBEND_BIN, "fabublox", "check", "--recipe", "post_cu_anneal"], capture_output=True, text=True)
    check("obend fabublox check + obend verify (fabublox-run@1 damascene & post-Cu contamination refused)",
          r_fb.returncode == 0 and r_fb_ver.returncode == 0 and r_fb_bad.returncode == 3,
          r_fb.stdout + r_fb_ver.stdout + r_fb_bad.stderr)

    if os.path.getmtime(OBEND_BIN) >= os.path.getmtime(os.path.join(LEAN, "Obend", "Hardware", "Cli.lean")):
        ds_receipt = os.path.join(obj_dir, "datasheet_receipt.json")
        r_ds = subprocess.run([OBEND_BIN, "hardware", "datasheet-check", "--mode", "calibrated", "--out", ds_receipt], capture_output=True, text=True)
        r_ds_ver = subprocess.run([OBEND_BIN, "verify", ds_receipt], capture_output=True, text=True)
        r_ds_bad = subprocess.run([OBEND_BIN, "hardware", "datasheet-check", "--mode", "74ls_to_74hc_direct"], capture_output=True, text=True)
        check("obend hardware datasheet-check + obend verify (datasheet-fit@1 calibrated & 74LS->74HC direct refused)",
              r_ds.returncode == 0 and r_ds_ver.returncode == 0 and r_ds_bad.returncode == 3,
              r_ds.stdout + r_ds_ver.stdout + r_ds_bad.stderr)

        rf_receipt = os.path.join(obj_dir, "rf_receipt.json")
        r_rf = subprocess.run([OBEND_BIN, "hardware", "rf-signoff", "--mode", "ft8_40m_golden", "--out", rf_receipt], capture_output=True, text=True)
        r_rf_ver = subprocess.run([OBEND_BIN, "verify", rf_receipt], capture_output=True, text=True)
        r_rf_bad = subprocess.run([OBEND_BIN, "hardware", "rf-signoff", "--mode", "unfiltered_pa_harmonics"], capture_output=True, text=True)
        check("obend hardware rf-signoff + obend verify (rf-transceiver-signoff@1 40m FT8 golden & unfiltered PA refused)",
              r_rf.returncode == 0 and r_rf_ver.returncode == 0 and r_rf_bad.returncode == 3,
              r_rf.stdout + r_rf_ver.stdout + r_rf_bad.stderr)

        pic_receipt = os.path.join(obj_dir, "photonics_receipt.json")
        r_pic = subprocess.run([OBEND_BIN, "hardware", "photonics-signoff", "--mode", "golden", "--out", pic_receipt], capture_output=True, text=True)
        r_pic_ver = subprocess.run([OBEND_BIN, "verify", pic_receipt], capture_output=True, text=True)
        r_pic_bad = subprocess.run([OBEND_BIN, "hardware", "photonics-signoff", "--mode", "tight_bend"], capture_output=True, text=True)
        check("obend hardware photonics-signoff + obend verify (photonics-pic-signoff@1 SiEPIC SOI golden & tight bend refused)",
              r_pic.returncode == 0 and r_pic_ver.returncode == 0 and r_pic_bad.returncode == 3,
              r_pic.stdout + r_pic_ver.stdout + r_pic_bad.stderr)

        pcb_receipt = os.path.join(obj_dir, "pcb_receipt.json")
        r_pcb = subprocess.run([OBEND_BIN, "hardware", "pcb-signoff", "--mode", "golden", "--out", pcb_receipt], capture_output=True, text=True)
        r_pcb_ver = subprocess.run([OBEND_BIN, "verify", pcb_receipt], capture_output=True, text=True)
        r_pcb_bad = subprocess.run([OBEND_BIN, "hardware", "pcb-signoff", "--mode", "skew_mismatch"], capture_output=True, text=True)
        check("obend hardware pcb-signoff + obend verify (pcb-board-signoff@1 Rogers+FR4 golden & skew mismatch refused)",
              r_pcb.returncode == 0 and r_pcb_ver.returncode == 0 and r_pcb_bad.returncode == 3,
              r_pcb.stdout + r_pcb_ver.stdout + r_pcb_bad.stderr)

        eda_receipt = os.path.join(obj_dir, "eda_vault_receipt.json")
        r_eda = subprocess.run([OBEND_BIN, "hardware", "eda-vault-check", "--mode", "golden", "--out", eda_receipt], capture_output=True, text=True)
        r_eda_ver = subprocess.run([OBEND_BIN, "verify", eda_receipt], capture_output=True, text=True)
        r_eda_bad = subprocess.run([OBEND_BIN, "hardware", "eda-vault-check", "--mode", "overbudget"], capture_output=True, text=True)
        check("obend hardware eda-vault-check + obend verify (agentic-eda-swap@1 Vault smart-contract golden & overbudget refused)",
              r_eda.returncode == 0 and r_eda_ver.returncode == 0 and r_eda_bad.returncode == 3,
              r_eda.stdout + r_eda_ver.stdout + r_eda_bad.stderr)

        seq_sv_path = os.path.join(obj_dir, "lean_sumTo_seq_rtl.sv")
        lower_env = {**os.environ, "LEAN_SYSROOT": os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.35.0")}
        r_seq = subprocess.run([OBEND_BIN, "lower", "sumTo", "--arg", "10", "--rtl", seq_sv_path],
                               cwd=LEAN, env=lower_env, capture_output=True, text=True)
        check("obend lower sumTo --arg 10 --rtl (sequential Nat.rec FSM synthesis & 10-cycle simulation sumTo 10 = 55)",
              r_seq.returncode == 0 and "sequential module lean_sumTo_seq_rtl verified" in r_seq.stdout and "rtl: sumTo 10 = 55 (cycles=10, done=1)" in r_seq.stdout,
              r_seq.stdout + r_seq.stderr)

        fib_sv_path = os.path.join(obj_dir, "lean_fib_seq_rtl.sv")
        r_fib = subprocess.run([OBEND_BIN, "lower", "fib", "--arg", "10", "--rtl", fib_sv_path],
                               cwd=LEAN, env=lower_env, capture_output=True, text=True)
        check("obend lower fib --arg 10 --rtl (2-state tuple Nat.rec FSM synthesis & 10-cycle simulation fib 10 = 55)",
              r_fib.returncode == 0 and "sequential module lean_fib_seq_rtl verified" in r_fib.stdout and "rtl: fib 10 = 55 (cycles=10, done=1)" in r_fib.stdout,
              r_fib.stdout + r_fib.stderr)

        # 10. Binary RFC 8949 CBOR (hw-binary-cbor@1, Tag 0x0BED) + .obnb Core.Data + Rust FFI Interop Checks
        cbor_bin_path = os.path.join(obj_dir, "hw_cert.cbor")
        obnb_cell_path = os.path.join(obj_dir, "hw_cell.obnb")
        for dom in ["pnr", "photonics", "dpr", "eda", "magnetics", "fluid", "power", "mechanics"]:
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

        RUST_HOST_BIN = os.path.join(REPO, "hardware", "rust-ffi", "target", "debug", "obend_hw_host")
        if os.path.exists(RUST_HOST_BIN):
            rust_cbor_path = os.path.join(obj_dir, "rust_femm.cbor")
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

            # Variable-length CBOR certificates from Rust high-speed solvers (solve-femm, prune-octree, evolve)
            for cmd_name, dom_arg in [
                ("solve-femm", "magnetics"),
                ("prune-octree", "mechanics"),
                ("evolve", "fluid"),
            ]:
                var_cbor_path = os.path.join(obj_dir, f"rust_{cmd_name}.cbor")
                r_rcmd = subprocess.run(
                    [RUST_HOST_BIN, cmd_name, "--out", var_cbor_path],
                    capture_output=True, text=True,
                )
                r_lver = subprocess.run(
                    [OBEND_BIN, "hardware", "verify-cbor", "--domain", dom_arg, "--in-bin", var_cbor_path, "--out-obnb", obnb_cell_path],
                    capture_output=True, text=True,
                )
                check(f"Rust {cmd_name} -> variable-length RFC 8949 CBOR -> obend hardware verify-cbor ({dom_arg})",
                      r_rcmd.returncode == 0 and r_lver.returncode == 0
                      and f"verified (hw-binary-cbor@1, domain={dom_arg}," in r_lver.stdout,
                      r_rcmd.stdout + r_rcmd.stderr + r_lver.stdout + r_lver.stderr)

            # Adversarial variable-length 0x9A CBOR checks (truncated stream & trailing garbage bytes)
            femm_cbor_path = os.path.join(obj_dir, "rust_solve-femm.cbor")
            with open(femm_cbor_path, "rb") as f:
                valid_tape_bytes = f.read()
            trunc_cbor_path = os.path.join(obj_dir, "rust_tape_trunc.cbor")
            with open(trunc_cbor_path, "wb") as f:
                f.write(valid_tape_bytes[:-1])
            trail_cbor_path = os.path.join(obj_dir, "rust_tape_trail.cbor")
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

        # 11. Userspace .obend Physical Engineering Suite (LcDrivesStatorUsd.obend & Cnc5AxisMill.obend)
        for ob_name, entry_name, expected_val in [
            ("LcDrivesStatorUsd.obend", "lcDrivesInSlotPeakTemp8kW", "result: 122"),
            ("Cnc5AxisMill.obend", "compensatedCommandSample", "result: 10024"),
        ]:
            ob_path = os.path.join(HERE, "obend-source", "world", "physical", ob_name)
            r_ob_chk = subprocess.run([OBEND_BIN, "check", ob_path], capture_output=True, text=True)
            r_ob_run = subprocess.run([OBEND_BIN, "run", ob_path, entry_name], capture_output=True, text=True)
            check(f"obend check + run world/physical/{ob_name} {entry_name} (userspace OpenUSD/CAM #law contracts & {expected_val})",
                  r_ob_chk.returncode == 0 and r_ob_run.returncode == 0 and expected_val in r_ob_run.stdout,
                  r_ob_chk.stdout + r_ob_chk.stderr + r_ob_run.stdout + r_ob_run.stderr)

        # 12. Live Compiler-Emitted SystemVerilog (emit-sv) + Verilator 5.050 (-Wall) C++ Co-Simulation
        stator_sv = os.path.join(obj_dir, "lc_drives_userspace_stator.sv")
        mill_sv = os.path.join(obj_dir, "cnc_5axis_userspace_mill.sv")
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

        up_tb_sv = os.path.join(obj_dir, "userspace_phys_tb.sv")
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

        up_main_cpp = os.path.join(obj_dir, "userspace_phys_main.cpp")
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

        up_obj_dir = os.path.join(obj_dir, "obj_userspace_phys")
        r_up_ver = subprocess.run([
            VERILATOR, "--cc", "--exe", "--top-module", "userspace_phys_tb",
            "-sv", "-Wall",
            f"-I{obj_dir}",
            stator_sv, mill_sv, up_tb_sv, up_main_cpp,
            "--Mdir", up_obj_dir,
        ], capture_output=True, text=True)
        check("verilator 5.050 (-Wall): compiler-emitted lc_drives_userspace_stator.sv & cnc_5axis_userspace_mill.sv elaboration",
              r_up_ver.returncode == 0, r_up_ver.stdout + r_up_ver.stderr)

        if r_up_ver.returncode == 0:
            up_bin = os.path.join(up_obj_dir, "sim_userspace_phys")
            up_cpps = [
                os.path.join(up_obj_dir, f)
                for f in sorted(os.listdir(up_obj_dir))
                if f.startswith("Vuserspace_phys_tb") and f.endswith(".cpp") and f != "Vuserspace_phys_tb__ALL.cpp"
            ]
            r_up_cxx = subprocess.run([
                CXX, "-Os", "-std=c++20",
                f"-I{up_obj_dir}", f"-I{VL_INC}", f"-I{VL_INC}/vltstd",
                "-Wl,-U,__Z15vl_time_stamp64v,-U,__Z13sc_time_stampv,-U,_vlog_startup_routines",
                up_main_cpp,
                *up_cpps,
                os.path.join(VL_INC, "verilated.cpp"),
                os.path.join(VL_INC, "verilated_threads.cpp"),
                "-o", up_bin,
            ], capture_output=True, text=True)
            r_up_sim = subprocess.run([up_bin], capture_output=True, text=True) if r_up_cxx.returncode == 0 else r_up_cxx
            check("verilator co-sim: compiler-emitted SV matches Lean kernel (peakWindingTemp=122, sdfMargin=24, cmdAxis=10024, totalVolErr=26)",
                  r_up_cxx.returncode == 0 and r_up_sim.returncode == 0
                  and "peakWindingTemp=122" in r_up_sim.stdout and "sdfMargin=24" in r_up_sim.stdout
                  and "cmdAxis=10024" in r_up_sim.stdout and "totalVolErr=26" in r_up_sim.stdout,
                  r_up_cxx.stdout + r_up_cxx.stderr + r_up_sim.stdout + r_up_sim.stderr)

print(f"\nrun-hardware: {count - len(failures)}/{count} passed")
sys.exit(1 if failures else 0)
