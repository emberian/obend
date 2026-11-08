#!/usr/bin/env python3
"""Independent NumPy uint64 check and production CPU baseline for the SOAC gate.

The full pipeline computes the same 25 outputs as SoacPrograms. It includes output
allocation and Python dispatch; the GPU runner measures submission through completion,
excluding shader compilation and transfers. These scopes are reported, not equated.
"""
import argparse
from datetime import datetime, timezone
import json
import platform
import re
import statistics
import time
from pathlib import Path

import numpy as np

CASES = {
    "soac-boundaries": [0, 1, 3, 0, 2, 2, 0],
    "soac-empty": [0, 0, 0],
    "soac-no-segments": [],
    "soac-single-65536": [65536],
    "soac-segments-64x1024": [1024] * 64,
}
OPS = [(np.add, 0), (np.multiply, 1), (np.bitwise_and, (1 << 64) - 1), (np.bitwise_or, 0)]


def wire(text):
    return np.array([] if text == "-" else [int(x) % (1 << 64) for x in text.split(",")], dtype=np.uint64)


def scan(op, identity, xs, exclusive=False, axis=0):
    result = op.accumulate(xs, axis=axis, dtype=np.uint64)
    if exclusive and xs.shape[axis]:
        result = np.roll(result, 1, axis=axis)
        if axis == 0:
            result[0] = identity
        else:
            result[:, 0] = identity
    return result


def pipeline(xs, lengths):
    xs = np.add(xs, xs)
    offsets = np.cumsum([0] + lengths)
    regular = bool(lengths) and lengths[0] > 0 and len(set(lengths)) == 1
    outputs = []
    for op, identity in OPS:
        outputs.extend([
            np.atleast_1d(op.reduce(xs, initial=np.uint64(identity), dtype=np.uint64)),
            scan(op, identity, xs),
            scan(op, identity, xs, True),
        ])
        if regular:
            rows = xs.reshape(len(lengths), lengths[0])
            outputs.extend([
                op.reduce(rows, axis=1, initial=np.uint64(identity), dtype=np.uint64),
                scan(op, identity, rows, axis=1).reshape(-1),
                scan(op, identity, rows, True, axis=1).reshape(-1),
            ])
        else:
            segments = [xs[a:b] for a, b in zip(offsets, offsets[1:])]
            outputs.append(np.array([op.reduce(v, initial=np.uint64(identity), dtype=np.uint64) for v in segments], dtype=np.uint64))
            for exclusive in (False, True):
                outputs.append(np.concatenate([scan(op, identity, v, exclusive) for v in segments]) if segments else np.array([], dtype=np.uint64))
    outputs.append(np.add.accumulate(xs, dtype=np.uint64)[::-1].copy())
    return outputs


def median_us(fn, repeats):
    for _ in range(10):
        fn()
    samples = []
    for _ in range(repeats):
        start = time.perf_counter_ns()
        fn()
        samples.append((time.perf_counter_ns() - start) / 1000)
    return statistics.median(samples)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("graphs", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--gpu-log", type=Path)
    parser.add_argument("--repeats", type=int, default=101)
    args = parser.parse_args()
    gpu = {}
    if args.gpu_log:
        for match in re.finditer(r"^(soac-[^:]+): (\d+) vectors, (\d+) dispatches, 0 disagree, ([0-9.]+) ms per vector, on (.+)$", args.gpu_log.read_text(), re.MULTILINE):
            name, vectors, dispatches, ms, adapter = match.groups()
            gpu[name] = {"gpu_full_pipeline_ms": float(ms), "gpu_vectors": int(vectors),
                         "gpu_dispatches": int(dispatches), "gpu_adapter": adapter}
    cpu = platform.processor()
    if Path("/proc/cpuinfo").exists():
        cpu = next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("model name")), cpu)
    report = {"recorded_at": datetime.now(timezone.utc).isoformat(), "cpu": cpu, "numpy": np.__version__, "python": platform.python_version(), "host": platform.node(),
              "machine": platform.machine(), "platform": platform.platform(), "repeats": args.repeats,
              "cpu_timing_scope": "median compute including allocations and Python dispatch; warm inputs",
              "gpu_timing_scope": "runner submission to completion; excludes shader compilation and transfers",
              "schedule": "emitted GPU plan; dispatch counts recorded per case",
              "cases": {}}
    for name, lengths in CASES.items():
        vectors = []
        for line in (args.graphs / name / "expected.tsv").read_text().splitlines():
            idx, inputs, expected = line.split("\t")
            xs = wire(inputs)
            wants = [wire(w) for w in expected.split(";")]
            got = pipeline(xs, lengths)
            assert len(got) == len(wants)
            for k, (a, b) in enumerate(zip(got, wants)):
                if not np.array_equal(a, b):
                    raise SystemExit(f"{name} vector {idx} output {k}: NumPy disagrees")
            vectors.append(xs)
        xs = vectors[0]
        report["cases"][name] = {"elements": len(xs), "segments": len(lengths), "vectors_checked": len(vectors),
            "numpy_full_pipeline_us": median_us(lambda: pipeline(xs, lengths), args.repeats),
            "numpy_sum_cumsum_us": median_us(lambda: (np.sum(xs, dtype=np.uint64), np.cumsum(xs, dtype=np.uint64)), args.repeats)}
        report["cases"][name].update(gpu.get(name, {}))
    text = json.dumps(report, indent=2) + "\n"
    if args.out:
        args.out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
