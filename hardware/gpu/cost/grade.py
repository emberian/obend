#!/usr/bin/env python3
"""Resource observation + occupancy/traffic estimate, not a shader resource predictor.

Consumes isa_extract.py's actual RADV stats, with explicit wave size (never inferred
from workgroup size). RDNA2 occupancy follows Mesa 24.2.8 radv_get_max_waves.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re

HEADER = re.compile(r'^## stage (\d+) \(([^)]+)\): (\d+) threads, .*; VGPRs: (\d+), SGPRs: (\d+), LDS: (\d+), scratch: (\d+), code: (\d+)$', re.M)


def align(n, a):
    return (n + a - 1) // a * a


def occupancy(vgprs, lds_bytes, workgroup_size, wave_size):
    # gfx1031: 512 physical wave64 VGPRs per SIMD, 16 wave slots;
    # 128 KiB LDS/WGP, four SIMD/WGP, 1024-byte LDS allocation blocks.
    allocated = align(vgprs, 16 if wave_size == 32 else 8)
    vgpr_limit = (512 * (64 // wave_size) // allocated) if allocated else 16
    waves_per_group = math.ceil(workgroup_size / wave_size)
    lds_per_wave = align(lds_bytes, 1024) // waves_per_group
    lds_limit = math.ceil(32768 / lds_per_wave) if lds_per_wave else 16
    waves = min(16, vgpr_limit, lds_limit)
    return dict(allocated_vgprs=allocated, vgpr_wave_limit=vgpr_limit,
                lds_wave_limit=lds_limit, mesa_waves_per_simd=waves,
                mesa_max_waves=waves * (wave_size // 32))


def traffic_upper(body, threads):
    """Static requested bytes upper bound for acyclic ISA, not DRAM transactions.

    Count all vector buffer/global paths as if each invocation executed all of
    them. Branches therefore overcount. Backward branches/unknown memory ops
    refuse the bound. Descriptor scalar loads, LDS and scratch are separate.
    """
    labels = {m.group(1): m.start() for m in re.finditer(r'^(\w+):', body, re.M)}
    for branch in re.finditer(r'\bs_(?:cbranch_\w+|branch)\s+(\w+)', body):
        if labels.get(branch.group(1), -1) <= branch.start():
            return dict(requested_bytes_upper=None, traffic_reason='backward/unknown branch; dynamic loop count required')
    reads = writes = 0
    for line in body.splitlines():
        m = re.match(r'\s*((?:buffer|global)_(?:load|store)_\w+)\b', line)
        if not m:
            if re.match(r'\s*(?:flat_|buffer_atomic|global_atomic)', line):
                return dict(requested_bytes_upper=None, traffic_reason='unsupported memory instruction')
            continue
        op = m.group(1)
        size = re.search(r'_(?:load|store)_(?:dword(x[234])?|([us]?byte|[us]?short))$', op)
        if not size:
            return dict(requested_bytes_upper=None, traffic_reason='unsupported memory width: ' + op)
        width = int(size.group(1)[1:]) * 4 if size.group(1) else (1 if size.group(2) and 'byte' in size.group(2) else 2 if size.group(2) else 4)
        if '_load_' in op:
            reads += width
        else:
            writes += width
    return dict(requested_read_bytes_upper=reads * threads,
                requested_write_bytes_upper=writes * threads,
                requested_bytes_upper=(reads + writes) * threads,
                traffic_reason='acyclic vector buffer instructions × active invocations; paths overcount; excludes descriptors/LDS/scratch; not DRAM bytes')


def grade(plan, isa, wave_size):
    if 'RADV NAVI22' not in isa and 'gfx1031' not in isa:
        raise ValueError('resource model requires a recorded gfx1031/RADV NAVI22 device')
    matches = list(HEADER.finditer(isa))
    if len(matches) != len(plan['stages']):
        raise ValueError('ISA stage count does not match dispatch plan')
    stages = []
    for i, (m, stage) in enumerate(zip(matches, plan['stages'])):
        k, filename, threads, vgprs, sgprs, lds, scratch, code = m.groups()
        if int(k) != i or filename != stage['file'] or int(threads) != stage['threads']:
            raise ValueError(f'stage {i}: ISA/plan identity mismatch')
        body = isa[m.end():matches[i+1].start() if i+1 < len(matches) else len(isa)]
        stats = dict(vgprs=int(vgprs), sgprs=int(sgprs), lds_bytes=int(lds),
                     scratch_bytes_per_wave=int(scratch), code_bytes=int(code))
        workgroup = plan['workgroupSize']
        logical = {}
        if 'logicalReadBytes' in stage and 'logicalWriteBytes' in stage:
            if any(type(stage[k]) is not int or stage[k] < 0 for k in ('logicalReadBytes', 'logicalWriteBytes')):
                raise ValueError('logical traffic must be nonnegative integer bytes')
            logical = dict(logical_read_bytes=stage['logicalReadBytes'],
                           logical_write_bytes=stage['logicalWriteBytes'],
                           logical_traffic_source='emitter dispatch model; not DRAM traffic')
        stages.append(dict(stage=i, file=filename, threads=int(threads),
                           workgroups=max(1, math.ceil(int(threads)/workgroup)),
                           **stats, **occupancy(int(vgprs), int(lds), workgroup, wave_size),
                           **traffic_upper(body, int(threads)), **logical))
    bounds = [s['requested_bytes_upper'] for s in stages]
    return dict(schema='obend-radv-resource-grade-v1', device='gfx1031/RADV Mesa 24.2.8',
                graph=plan['graph'], wave_size=wave_size, dispatches=len(stages),
                wire_buffer_bytes=plan['words'] * 8,
                code_bytes=sum(s['code_bytes'] for s in stages),
                requested_bytes_upper=sum(bounds) if all(b is not None for b in bounds) else None,
                logical_bytes=sum(s['logical_read_bytes'] + s['logical_write_bytes'] for s in stages) if all('logical_read_bytes' in s for s in stages) else None,
                isa_sha256=hashlib.sha256(isa.encode()).hexdigest(), stages=stages,
                limitations='Compiler-reported allocations are observations. Occupancy is Mesa static estimate, not measured residency or timing. SGPRs do not limit occupancy on gfx10+. Scratch/code size are recorded, not converted into fabricated runtime penalties.')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('plan', type=Path)
    ap.add_argument('isa', type=Path)
    ap.add_argument('--wave-size', required=True, type=int, choices=[32,64])
    args = ap.parse_args()
    print(json.dumps(grade(json.loads(args.plan.read_text()), args.isa.read_text(), args.wave_size), indent=2))

if __name__ == '__main__':
    main()
