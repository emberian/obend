#!/usr/bin/env python3
"""Extract our stages' final ISA from a RADV_DEBUG=shaders dump (hardware/gpu/verify_gpu.sh stage 4).

    isa_extract.py DUMP PLAN_JSON OUT "adapter line"

The dump holds one record per shader RADV compiled while obend-gpu-run ran a graph: wgpu's own internal
shaders, created with the device, then ours, one per stage in dispatch order. A candidate record is not
internal and has the plan's workgroup size; the last `stages` candidates are ours. The script requires at
least that many candidates, each of ours ending in `s_endpgm` with at least one 64-bit buffer store, and
records the store count per stage (the emitter writes one kernel per hyperedge and one store per element
path; the compiler is free to merge). It writes OUT with each stage's disassembly (encodings stripped) and
exits 1 if anything does not match.
"""
import json
import re
import sys


def main() -> int:
    dump_path, plan_path, out_path, adapter = sys.argv[1:5]
    plan = json.load(open(plan_path))
    text = open(dump_path, errors="replace").read()
    wg = f"workgroup_size: {plan['workgroupSize']}, 1, 1"
    candidates = []
    for rec in text.split("shader: MESA_SHADER_COMPUTE")[1:]:
        if "internal: false" not in rec or wg not in rec or "disasm:" not in rec:
            continue
        candidates.append(rec.split("disasm:", 1)[1].split("\n\n")[0])
    stages = plan["stages"]
    if len(candidates) < len(stages):
        print(f"[FAIL] {plan['graph']}: {len(candidates)} candidate shaders in the dump for {len(stages)} stages", file=sys.stderr)
        return 1
    ours = candidates[len(candidates) - len(stages):]
    out = [f"# {plan['graph']}: RADV's final ISA for each stage, on {adapter}",
           "# Extracted by hardware/gpu/isa_extract.py from RADV_DEBUG=shaders; do not edit.", ""]
    for k, (stage, dis) in enumerate(zip(stages, ours)):
        lines = [re.sub(r"\s*;\s*[0-9a-f]{8}(\s+[0-9a-f]{8})*\s*$", "", ln) for ln in dis.strip("\n").split("\n")]
        stores = sum(1 for ln in lines if "buffer_store_dwordx2" in ln)
        if "s_endpgm" not in dis:
            print(f"[FAIL] {plan['graph']} stage {k}: no s_endpgm", file=sys.stderr)
            return 1
        if stores == 0:
            print(f"[FAIL] {plan['graph']} stage {k}: no 64-bit store in the final ISA", file=sys.stderr)
            return 1
        insns = sum(1 for ln in lines if ln.startswith("\t"))
        out.append(f"## stage {k} ({stage['file']}): {stage['threads']} threads, {insns} instructions, {stores} 64-bit stores")
        out.extend(lines)
        out.append("")
        print(f"    stage {k}: {stage['threads']} threads -> {insns} instructions, {stores} stores")
    open(out_path, "w").write("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
