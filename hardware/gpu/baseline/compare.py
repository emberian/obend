#!/usr/bin/env python3
"""Join measured Plonky3 TSV with runner BENCH records, preserving timing boundaries."""
import argparse
from pathlib import Path
import re

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--cpu', required=True, type=Path)
ap.add_argument('gpu_logs', nargs='+', type=Path)
args = ap.parse_args()
cpu = {}
for line in args.cpu.read_text().splitlines():
    cols = line.split('\t')
    if len(cols) == 7 and cols[0].isdigit():
        cpu[int(cols[1])] = float(cols[4])
print('# CPU median / GPU device median is a compute-only ratio, not end-to-end speedup.')
print('# GPU host batch amortized time includes warmups, GPU resets and final readback; CPU excludes input clone.')
print('graph\tn\tcpu_median_us\tgpu_device_median_us\tgpu_host_batch_amortized_us\tcpu_over_gpu_device')
found = 0
for path in args.gpu_logs:
    for line in path.read_text().splitlines():
        if not line.startswith('BENCH\t'):
            continue
        cols = line.split('\t')
        m = re.search(r'(\d+)$', cols[1])
        if not m or int(m.group(1)) not in cpu:
            raise SystemExit(f'{path}: cannot match graph {cols[1]!r} to CPU size')
        n = int(m.group(1))
        metrics = dict(c.split('=',1) for c in cols[4:])
        gpu = float(metrics['gpu_us_median'])
        if gpu <= 0:
            raise SystemExit(f'{path}: nonpositive GPU device time')
        print(f"{cols[1]}\t{n}\t{cpu[n]:.3f}\t{gpu:.3f}\t{float(metrics['host_batch_amortized_us']):.3f}\t{cpu[n]/gpu:.3f}")
        found += 1
if not found:
    raise SystemExit('No BENCH measurements found; comparison unavailable')
