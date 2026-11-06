#!/usr/bin/env python3
"""Extract our stages' final ISA from a RADV_DEBUG=shaders,shaderstats dump (hardware/gpu/verify_gpu.sh stage 4).

    isa_extract.py DUMP PLAN_JSON OUT "adapter line"

The dump holds one record per shader RADV compiled while obend-gpu-run ran a graph: wgpu's own internal
shaders, created with the device, then ours, one per stage in dispatch order. A candidate record is not
internal and has the plan's workgroup size; the last `stages` candidates are ours. The script requires at
least that many candidates, each of ours ending in `s_endpgm` with at least one 64-bit buffer store
unless the plan assigns zero threads to that stage, and
records the store count per stage (the emitter writes one kernel per hyperedge and one store per element
path; the compiler is free to merge). It writes OUT with each stage's disassembly, every instruction line
keeping the machine-code dwords RADV printed after `;` (rung G2 decodes them: `isa_check.sh`,
`Obend.Hardware.Gpu.Rdna2`), and the resource line RADV reports with `shaderstats` (VGPRs, SGPRs, LDS,
scratch, code size: rung G5's grade). It exits 1 if anything does not match.
Constant pools are retained as non-instruction `.data BYTE_OFFSET HEX...` records;
their offsets include ACO's unprinted end-of-code markers.
"""
import json
import re
import sys

STATS = (("VGPRs", "VGPRs"), ("SGPRs", "SGPRs"), ("LDS size", "LDS"), ("Scratch size", "scratch"), ("Code size", "code"))
REPEATED = re.compile(r"^\t\(then repeated ([0-9]+) times\)$")
HEX_LINE = re.compile(r"^\t(.*?)\s*;\s*((?:[0-9a-f]{8}\s*)+)$")
DATA_LINE = re.compile(r"^\[([0-9]+)\] ((?:[0-9a-f]{8}(?: |$))+)\s*$")


def main() -> int:
    dump_path, plan_path, out_path, adapter = sys.argv[1:5]
    plan = json.load(open(plan_path))
    text = open(dump_path, errors="replace").read()
    wg = f"workgroup_size: {plan['workgroupSize']}, 1, 1"
    candidates = []
    for rec in text.split("shader: MESA_SHADER_COMPUTE")[1:]:
        if "internal: false" not in rec or wg not in rec or "disasm:" not in rec:
            continue
        stats = {}
        for key, label in STATS:
            m = re.search(rf"^{re.escape(key)}: (\d+)$", rec, re.M)
            if m:
                stats[label] = int(m.group(1))
        assembly = rec.split("disasm:", 1)[1]
        data = []
        if "/* constant data */" in assembly:
            pool = assembly.split("/* constant data */", 1)[1].strip().split("\n\n")[0]
            next_offset = 0
            for line in pool.splitlines():
                m = DATA_LINE.fullmatch(line)
                if not m or int(m.group(1)) != next_offset:
                    print(f"[FAIL] {plan['graph']}: malformed or discontinuous constant data: {line!r}", file=sys.stderr)
                    return 1
                words = m.group(2).split()
                data.append((next_offset, words))
                next_offset += 4 * len(words)
        candidates.append((assembly.split("\n\n")[0], stats, data))
    stages = plan["stages"]
    if len(candidates) < len(stages):
        print(f"[FAIL] {plan['graph']}: {len(candidates)} candidate shaders in the dump for {len(stages)} stages", file=sys.stderr)
        return 1
    ours = candidates[len(candidates) - len(stages):]
    out = [f"# {plan['graph']}: RADV's final ISA for each stage, on {adapter}",
           "# Extracted by hardware/gpu/isa_extract.py from RADV_DEBUG=shaders,shaderstats; do not edit.",
           "# Each instruction line ends in `; <dwords>`, the machine code as RADV printed it; labels and text are LLVM's.", ""]
    for k, (stage, (dis, stats, data)) in enumerate(zip(stages, ours)):
        lines = []
        for ln in dis.strip("\n").split("\n"):
            if ln.startswith("\t"):
                # Mesa aco_print_asm.cpp suppresses identical consecutive instructions:
                # repeat_count counts ADDITIONAL copies of the preceding binary words.
                # https://gitlab.freedesktop.org/mesa/mesa/-/blob/mesa-24.2.8/src/amd/compiler/aco_print_asm.cpp
                repeated = REPEATED.fullmatch(ln)
                if repeated:
                    if not lines or not HEX_LINE.match(lines[-1]):
                        print(f"[FAIL] {plan['graph']} stage {k}: repeat without preceding instruction", file=sys.stderr)
                        return 1
                    lines.extend([lines[-1]] * int(repeated.group(1)))
                    continue
                m = HEX_LINE.match(ln)
                if not m:
                    print(f"[FAIL] {plan['graph']} stage {k}: instruction line without machine code: {ln!r}", file=sys.stderr)
                    return 1
                lines.append(f"\t{m.group(1)}\t; {' '.join(m.group(2).split())}")
            else:
                lines.append(ln)
        stores = sum(1 for ln in lines if "buffer_store_dwordx2" in ln)
        if "s_endpgm" not in dis:
            print(f"[FAIL] {plan['graph']} stage {k}: no s_endpgm", file=sys.stderr)
            return 1
        if stores == 0 and stage["threads"] != 0:
            print(f"[FAIL] {plan['graph']} stage {k}: no 64-bit store in the final ISA", file=sys.stderr)
            return 1
        missing = [label for _, label in STATS if label not in stats]
        if missing:
            print(f"[FAIL] {plan['graph']} stage {k}: shaderstats missing {missing} (run with RADV_DEBUG=shaders,shaderstats)", file=sys.stderr)
            return 1
        code_bytes = sum(4 * len(m.group(2).split()) for ln in lines if (m := HEX_LINE.match(ln)))
        if data:
            if code_bytes != stats["code"]:
                print(f"[FAIL] {plan['graph']} stage {k}: constant pool needs exact executable size: {code_bytes} != {stats['code']}", file=sys.stderr)
                return 1
            # Mesa ACO's emit_program appends five UMR end-of-code marker dwords
            # after exec_size, then fixes PC-relative addresses and appends constant_data.
            # They are omitted by print_asm. This is RADV's compute-shader layout;
            # retain absolute byte offsets so the ISA model uses the actual addresses.
            # https://chromium.googlesource.com/external/gitlab.freedesktop.org/mesa/mesa/+/26b942c30668a1899cbc220c0d4aa58fbca8fb5f/src/amd/compiler/aco_assembler.cpp
            for offset, words in data:
                lines.append(f".data {code_bytes + 20 + offset} {' '.join(words)}")
        insns = sum(1 for ln in lines if ln.startswith("\t"))
        res = ", ".join(f"{label}: {stats[label]}" for _, label in STATS)
        out.append(f"## stage {k} ({stage['file']}): {stage['threads']} threads, {insns} instructions, {stores} 64-bit stores; {res}")
        out.extend(lines)
        out.append("")
        print(f"    stage {k}: {stage['threads']} threads -> {insns} instructions, {stores} stores; VGPRs {stats['VGPRs']}, LDS {stats['LDS']}")
    open(out_path, "w").write("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
