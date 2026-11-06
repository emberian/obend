#!/usr/bin/env python3
"""Extract our stages' final ISA from a RADV_DEBUG=shaders,shaderstats dump (hardware/gpu/verify_gpu.sh stage 4).

    isa_extract.py DUMP PLAN_JSON OUT "adapter line"

The dump holds one record per shader RADV compiled while obend-gpu-run ran a graph: wgpu's own internal
shaders, created with the device, then ours, one per stage in dispatch order. A candidate record is not
internal and has the plan's workgroup size; the last `stages` candidates are ours. The script requires at
least that many candidates, each of ours ending in `s_endpgm` with at least one buffer store, and
records the store count per stage (the emitter writes one kernel per hyperedge and one store per element
path; the compiler is free to merge or split widths). It writes OUT with each stage's disassembly, every instruction line
keeping the machine-code dwords RADV printed after `;` (rung G2 decodes them: `isa_check.sh`,
`Obend.Hardware.Gpu.Rdna2`), and the resource line RADV reports with `shaderstats` (VGPRs, SGPRs, LDS,
scratch, code size: rung G5's grade). Repeated-instruction shorthand is expanded,
and the decoded dword byte count must equal RADV's Code size. It exits 1 on mismatch.
"""
import json
import re
import sys

STATS = (("VGPRs", "VGPRs"), ("SGPRs", "SGPRs"), ("LDS size", "LDS"), ("Scratch size", "scratch"), ("Code size", "code"))
REPEAT_LINE = re.compile(r"^\t\(then repeated (\d+) times\)$")
STORE = re.compile(r"^\tbuffer_store_dword(?:x([234]))?\b")
HEX_LINE = re.compile(r"^\t(.*?)\s*;\s*((?:[0-9a-f]{8}\s*)+)$")


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
        candidates.append((rec.split("disasm:", 1)[1].split("\n\n")[0], stats))
    stages = plan["stages"]
    if len(candidates) < len(stages):
        print(f"[FAIL] {plan['graph']}: {len(candidates)} candidate shaders in the dump for {len(stages)} stages", file=sys.stderr)
        return 1
    ours = candidates[len(candidates) - len(stages):]
    out = [f"# {plan['graph']}: RADV's final ISA for each stage, on {adapter}",
           "# Extracted by hardware/gpu/isa_extract.py from RADV_DEBUG=shaders,shaderstats; do not edit.",
           "# Each instruction line ends in `; <dwords>`, the machine code as RADV printed it; labels and text are LLVM's.", ""]
    for k, (stage, (dis, stats)) in enumerate(zip(stages, ours)):
        lines = []
        for ln in dis.strip("\n").split("\n"):
            repeat = REPEAT_LINE.match(ln)
            if repeat:
                if not lines or not HEX_LINE.match(lines[-1]):
                    print(f"[FAIL] {plan['graph']} stage {k}: repetition without preceding machine instruction", file=sys.stderr)
                    return 1
                lines.extend([lines[-1]] * int(repeat.group(1)))
                continue
            if ln.startswith("\t"):
                m = HEX_LINE.match(ln)
                if not m:
                    print(f"[FAIL] {plan['graph']} stage {k}: instruction line without machine code: {ln!r}", file=sys.stderr)
                    return 1
                lines.append(f"\t{m.group(1)}\t; {' '.join(m.group(2).split())}")
            else:
                lines.append(ln)
        store_widths = [4 * int(m.group(1) or 1) for ln in lines if (m := STORE.match(ln))]
        stores = len(store_widths)
        if "s_endpgm" not in dis:
            print(f"[FAIL] {plan['graph']} stage {k}: no s_endpgm", file=sys.stderr)
            return 1
        if stores == 0:
            print(f"[FAIL] {plan['graph']} stage {k}: no buffer store in the final ISA", file=sys.stderr)
            return 1
        missing = [label for _, label in STATS if label not in stats]
        if missing:
            print(f"[FAIL] {plan['graph']} stage {k}: shaderstats missing {missing} (run with RADV_DEBUG=shaders,shaderstats)", file=sys.stderr)
            return 1
        byte_count = sum(4 * len(ln.split(";", 1)[1].split()) for ln in lines if ln.startswith("\t"))
        if byte_count != stats["code"]:
            print(f"[FAIL] {plan['graph']} stage {k}: extracted {byte_count} machine-code bytes, RADV reports {stats['code']}", file=sys.stderr)
            return 1
        insns = sum(1 for ln in lines if ln.startswith("\t"))
        res = ", ".join(f"{label}: {stats[label]}" for _, label in STATS)
        store_label = f"{stores} 64-bit stores" if all(w == 8 for w in store_widths) else f"{stores} buffer stores ({sum(store_widths)} static bytes)"
        out.append(f"## stage {k} ({stage['file']}): {stage['threads']} threads, {insns} instructions, {store_label}; {res}")
        out.extend(lines)
        out.append("")
        print(f"    stage {k}: {stage['threads']} threads -> {insns} instructions, {stores} stores; VGPRs {stats['VGPRs']}, LDS {stats['LDS']}")
    open(out_path, "w").write("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
