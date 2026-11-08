#!/usr/bin/env python3
"""Exact uint64 collectives oracle and device-resident/NumPy benchmark.

Run on the designated GPU host, with GPU access coordinated by the lane lead.
Artifacts come from obend-emit-gpu collective; the only handwritten shader is
the explicitly labeled copy bandwidth baseline, executed by the same runner.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import time

import numpy as np

OPS = {"add": (np.add, 0), "mul": (np.multiply, 1),
       "band": (np.bitwise_and, (1 << 64) - 1), "bor": (np.bitwise_or, 0)}
WARMUPS = 3
MIN_FREE = 20 * 1024 ** 3
SEED = 0xC011EC71


def space(path, extra=0):
    free = shutil.disk_usage(path).free
    if free < MIN_FREE + extra:
        raise RuntimeError(f"stop writes: {free} free bytes; require 20 GiB plus {extra} bytes")


def json_write(path, value):
    space(path.parent)
    path.write_text(json.dumps(value, indent=2) + "\n")


def data(n, op, variant=0):
    """Bit-sensitive deterministic inputs; multiplication stays odd, not all-zero.

    AND/OR have sparse bit events spread over the whole input so scans do not
    saturate after a few random words. A second small fixture uses random bits.
    """
    rng = np.random.default_rng(SEED + variant)
    xs = rng.bit_generator.random_raw(n).astype("<u8", copy=False)
    if op == "mul":
        xs |= np.uint64(1)
    elif op in ("band", "bor") and variant == 0:
        xs.fill(OPS[op][1])
        for k in range(min(47, n)):
            pos = k * n // min(47, n)
            bit = np.uint64(1 << ((k * 17) % 64))
            xs[pos] = ~bit if op == "band" else bit
    if variant and n:
        edge = np.array([0, 1, 0xffffffff, 0x100000000, 0x7fffffffffffffff,
                         0x8000000000000000, 0xffffffffffffffff], dtype=np.uint64)
        xs[:min(n, len(edge))] = edge[:min(n, len(edge))]
    return xs


def numpy_kernel(xs, lengths, name, mode):
    """Return output and a preallocated NumPy operation with exact word semantics."""
    if sum(lengths) != xs.size or any(n < 0 for n in lengths):
        raise ValueError("segment lengths do not partition the input")
    op, identity = OPS[name]
    identity = np.uint64(identity)
    out = np.empty(len(lengths) if mode == "reduce" else xs.size, dtype="<u8")
    regular = bool(lengths) and lengths[0] > 0 and all(n == lengths[0] for n in lengths)

    def one(a, b, axis=0):
        if mode == "reduce":
            op.reduce(a, axis=axis, dtype=np.uint64, initial=identity, out=b)
        elif mode == "inclusive":
            op.accumulate(a, axis=axis, dtype=np.uint64, out=b)
        elif a.shape[axis]:
            if axis == 1:
                b[:, 0] = identity
                op.accumulate(a[:, :-1], axis=1, dtype=np.uint64, out=b[:, 1:])
            else:
                b[0] = identity
                op.accumulate(a[:-1], dtype=np.uint64, out=b[1:])

    if regular:
        rows = xs.reshape(len(lengths), lengths[0])
        target = out if mode == "reduce" else out.reshape(rows.shape)
        def run():
            one(rows, target, axis=1)
    else:
        offsets = np.cumsum([0] + lengths, dtype=np.int64)
        def run():
            for i, (a, b) in enumerate(zip(offsets[:-1], offsets[1:])):
                if mode == "reduce":
                    # reduceat is deliberately not used: repeated offsets are not empty slices there.
                    out[i] = op.reduce(xs[a:b], dtype=np.uint64, initial=identity)
                else:
                    one(xs[a:b], out[a:b])
    return out, run


def cpu_times(run, repetitions):
    for _ in range(WARMUPS):
        run()
    samples = []
    for _ in range(repetitions):
        start = time.perf_counter_ns()
        run()
        samples.append((time.perf_counter_ns() - start) / 1000)
    ordered = sorted(samples)
    return {"samples": repetitions, "warmups": WARMUPS,
            "us_median": ordered[(repetitions - 1) * 50 // 100],
            "us_p10": ordered[(repetitions - 1) * 10 // 100],
            "us_p90": ordered[(repetitions - 1) * 90 // 100], "samples_us": samples}


def command(argv, log):
    print("running", " ".join(map(str, argv)), flush=True)
    space(log.parent)
    with log.open("w") as stream:
        result = subprocess.run(list(map(str, argv)), stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"command exited {result.returncode}: see {log}")
    return log.read_text()


def write_copy(directory, n):
    groups = max(1, (n + 63) // 64)
    groups_x = 32768 if groups > 65535 else groups
    # This has exactly the ordinary runner's three bindings and dispatch geometry.
    shader = f"""// Handwritten u64 copy baseline; not a source lowering result.
@group(0) @binding(0) var<storage, read_write> w: array<vec2<u32>>;
@group(0) @binding(1) var<storage, read> c: array<vec2<u32>>;
@group(0) @binding(2) var<storage, read> ix: array<u32>;
@compute @workgroup_size(64)
fn main(@builtin(workgroup_id) g: vec3<u32>, @builtin(local_invocation_id) l: vec3<u32>) {{
  let i = (g.x + g.y * {groups_x}u) * 64u + l.x;
  if (i < {n}u) {{ w[{n}u + i] = w[i]; }}
}}
"""
    space(directory)
    (directory / "stage_0.wgsl").write_text(shader)
    json_write(directory / "plan.json", {"graph": f"copy-u64-{n}", "words": 2 * n,
        "workgroupSize": 64, "wireBase": [0, n], "wireLen": [n, n], "consts": [],
        "tables": [], "inputs": [0], "outputs": [1],
        "stages": [{"file": "stage_0.wgsl", "threads": n,
                    "logicalReadBytes": 8 * n, "logicalWriteBytes": 8 * n}]})


def fixture(directory, index, xs, expected):
    files = []
    for kind, values in [("input", xs), ("expected", expected)]:
        path = directory / f"{index}-{kind}.u64le"
        space(directory, values.nbytes)
        values.astype("<u8", copy=False).tofile(path)
        files.append(path)
    return {"index": index, "inputs": [files[0].name], "expected": [files[1].name]}, files


def gpu_record(text, bench):
    validation = re.search(r"^(.+): (\d+) vectors, (\d+) dispatches, 0 disagree, [0-9.]+ ms per vector, on (.+)$", text, re.M)
    if validation is None:
        raise RuntimeError("runner did not report complete exact validation")
    record = {"vectors_checked": int(validation[2]), "dispatches": int(validation[3]), "adapter": validation[4]}
    if bench:
        lines = [line for line in text.splitlines() if line.startswith("BENCH\t")]
        if len(lines) != 1:
            raise RuntimeError("expected exactly one device timestamp report")
        fields = lines[0].split("\t")
        if int(fields[2]) != bench:
            raise RuntimeError("runner sample count differs from requested count")
        record.update({key: value for key, value in (field.split("=", 1) for field in fields[4:])})
        if record.get("final_output") != "exact":
            raise RuntimeError("benchmark output was not validated exactly")
        for key in ["gpu_us_median", "gpu_us_p10", "gpu_us_p90", "host_batch_amortized_us"]:
            record[key] = float(record[key])
    return record


def run_case(args, name, lengths, op, mode, timed, copy=False):
    directory = args.out / name
    space(args.out)
    directory.mkdir()
    n = sum(lengths)
    spec = {"op": op, "mode": mode, "segments": lengths, "tileLog": args.tile_log}
    json_write(directory / "spec.json", spec)
    if copy:
        write_copy(directory, n)
    else:
        command([args.emitter, "collective", directory / "spec.json", "--out", directory, "--artifacts-only"], directory / "emit.log")
    plan = json.loads((directory / "plan.json").read_text())
    manifests, files, hashes = [], [], []
    for variant in range(1 if timed or copy else 2):
        xs = data(n, op, variant)
        if copy:
            expected = np.empty_like(xs)
            def run():
                np.copyto(expected, xs)
        else:
            expected, run = numpy_kernel(xs, lengths, op, mode)
        run()
        manifest, created = fixture(directory, f"seed-{variant}", xs, expected)
        manifests.append(manifest)
        files.extend(created)
        hashes.append({"variant": variant, "input_sha256": hashlib.sha256(memoryview(xs)).hexdigest(),
                       "expected_sha256": hashlib.sha256(memoryview(expected)).hexdigest()})
    json_write(directory / "vectors.json", {"format": "u64le", "vectors": manifests})
    repetitions = args.gpu_repeats if timed and plan["stages"] else 0
    argv = [args.runner, directory, "--adapter", args.adapter]
    if repetitions:
        argv.extend(["--bench", repetitions])
    gpu = gpu_record(command(argv, directory / "gpu.log"), repetitions)
    result = {"name": name, "kind": "handwritten-copy-baseline" if copy else "source-collective",
        "op": op, "mode": mode, "elements": n, "segments": len(lengths),
        "segment_length": lengths[0] if lengths and len(set(lengths)) == 1 else None,
        "tile_log": args.tile_log, "gpu": gpu, "fixture_hashes": hashes,
        "binary_fixtures_retained": args.keep_fixtures,
        "device_word_bytes": plan["words"] * 8, "shader_bytes": sum((directory / s["file"]).stat().st_size for s in plan["stages"]),
        "plan_bytes": (directory / "plan.json").stat().st_size,
        "logical_device_read_bytes": sum(s.get("logicalReadBytes", 0) for s in plan["stages"]),
        "logical_device_write_bytes": sum(s.get("logicalWriteBytes", 0) for s in plan["stages"])}
    if timed:
        result["numpy"] = cpu_times(run, args.cpu_repeats)
        if repetitions and n:
            result["gpu"]["billion_input_words_per_second"] = n / gpu["gpu_us_median"] / 1000
            result["gpu"]["logical_GB_per_second"] = (result["logical_device_read_bytes"] + result["logical_device_write_bytes"]) / gpu["gpu_us_median"] / 1000
    json_write(directory / "result.json", result)
    if not args.keep_fixtures:
        # Only these exact binary files were created by this invocation in its fresh output directory.
        for path in files:
            path.unlink()
    print(json.dumps(result), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emitter", type=Path, required=True)
    parser.add_argument("--runner", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True, help="new directory; never overwrite an existing run")
    parser.add_argument("--adapter", required=True)
    parser.add_argument("--suite", choices=["all", "correctness", "benchmark", "copy"], default="all")
    parser.add_argument("--sizes", type=int, nargs="+", default=[16, 20, 24], help="log2 input lengths")
    parser.add_argument("--ops", nargs="+", choices=list(OPS), default=["add"], help="timed collective monoids")
    parser.add_argument("--correctness-ops", nargs="+", choices=list(OPS), default=list(OPS))
    parser.add_argument("--modes", nargs="+", choices=["inclusive", "exclusive", "reduce"], default=["inclusive", "exclusive", "reduce"])
    parser.add_argument("--tile-log", type=int, default=8)
    parser.add_argument("--gpu-repeats", type=int, default=31)
    parser.add_argument("--cpu-repeats", type=int, default=31)
    parser.add_argument("--keep-fixtures", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.gpu_repeats <= 1024 or args.cpu_repeats < 1:
        parser.error("GPU repeats must be1..1024 and CPU repeats positive")
    if any(log < 5 or log > 24 for log in args.sizes):
        parser.error("benchmark sizes must be log2 lengths in5..24")
    args.emitter, args.runner = args.emitter.resolve(), args.runner.resolve()
    args.out = args.out.resolve()
    space(args.out.parent)
    args.out.mkdir()
    cpu = platform.processor()
    if Path("/proc/cpuinfo").exists():
        cpu = next((x.split(":", 1)[1].strip() for x in Path("/proc/cpuinfo").read_text().splitlines() if x.startswith("model name")), cpu)
    report = {"recorded_at": datetime.now(timezone.utc).isoformat(), "host": platform.node(), "cpu": cpu,
        "numpy": np.__version__, "python": platform.python_version(), "platform": platform.platform(),
        "gpu_environment": {k: os.environ[k] for k in ("VK_ICD_FILENAMES", "VK_DRIVER_FILES", "WGPU_BACKEND") if k in os.environ},
        "seed": SEED, "gpu_samples": args.gpu_repeats, "cpu_samples": args.cpu_repeats, "warmups": WARMUPS,
        "timed_ops": args.ops, "correctness_ops": args.correctness_ops,
        "gpu_scope": "device timestamps first pass begin to last pass end; all dispatches/barriers; reset copies before every interval; compilation/upload/readback excluded",
        "cpu_scope": "perf_counter_ns around same NumPy uint64 operation with preallocated output and warm input; Python dispatch included; allocation and fixture IO excluded",
        "host_batch_scope": "GPU submission through final query/output mapping, including warmups and reset copies, divided by all repetitions; command recording/initial upload excluded",
        "copy_scope": "handwritten WGSL vec2<u32> copy through same runner; NumPy copyto preallocated array; not a source compiler correctness claim",
        "cases": []}
    json_write(args.out / "results.json", report)
    todo = []
    if args.suite in ("all", "correctness"):
        small = [("irregular", [0, 1, 3, 0, 31, 32, 33, 255, 256, 257, 0]),
                 ("empty", [0, 0, 0]), ("no-segments", []),
                 ("pruned-mixed", [0] + [1]*257 + [65536, 0, 257, 2, 0])]
        for name, lengths in small:
            for op in args.correctness_ops:
                for mode in args.modes:
                    todo.append((f"{name}-{op}-{mode}", lengths, op, mode, False, False))
        for label, lengths in [("single", [1 << 16]), ("short32", [32] * (1 << 11))]:
            for op in args.correctness_ops:
                # The timed cases also validate all elements; avoid duplicate add runs at 2^16.
                if args.suite == "all" and 16 in args.sizes and op in args.ops:
                    continue
                for mode in args.modes:
                    todo.append((f"check-{label}-16-{op}-{mode}", lengths, op, mode, False, False))
    if args.suite != "correctness":
        for log in args.sizes:
            n = 1 << log
            todo.append((f"copy-u64-{log}", [n], "add", "inclusive", True, True))
            if args.suite == "copy":
                continue
            for label, lengths in [("single", [n]), ("short32", [32] * (n // 32))]:
                for op in args.ops:
                    for mode in args.modes:
                        todo.append((f"{label}-{log}-{op}-{mode}", lengths, op, mode, True, False))
    for case in todo:
        report["cases"].append(run_case(args, *case))
        json_write(args.out / "results.json", report)


if __name__ == "__main__":
    main()
