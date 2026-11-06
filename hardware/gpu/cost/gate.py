#!/usr/bin/env python3
"""Compile/run real ordinary and LDS-pressure shaders; require changed compiler stats.

Usage: gate.py --runner /path/to/obend-gpu-run --work /new/output/directory
No synthetic stats edits. Both shaders implement y[i] = x[i] + 1 exactly.
The planted variant forces 32 KiB workgroup memory via input-dependent reads.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from grade import grade

BASE = '''@group(0) @binding(0) var<storage, read_write> w : array<vec2<u32>>;
@group(0) @binding(1) var<storage, read> c : array<vec2<u32>>;
@group(0) @binding(2) var<storage, read> ix : array<u32>;
fn addOne(x : vec2<u32>) -> vec2<u32> {
  return vec2<u32>(x.x + 1u, x.y + select(0u, 1u, x.x == 0xffffffffu));
}
'''
SIMPLE = BASE + '''@compute @workgroup_size(64)
fn main(@builtin(local_invocation_id) lid : vec3<u32>) {
  w[64u + lid.x] = addOne(w[lid.x]);
}
'''
PLANTED = BASE + '''var<workgroup> tile : array<vec2<u32>, 4096>;
@compute @workgroup_size(64)
fn main(@builtin(local_invocation_id) lid : vec3<u32>) {
  let t = lid.x;
  let x = w[t];
  for (var j = 0u; j < 64u; j = j + 1u) { tile[t + j * 64u] = x; }
  workgroupBarrier();
  // Each lane reads a dynamic slot owned by the next lane, preventing
  // compiler scalar replacement while preserving the same output function.
  let next = (t + 1u) % 64u;
  let chosen = w[next].x & 63u;
  w[64u + next] = addOne(tile[next + chosen * 64u]);
}
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runner', required=True, type=Path)
    ap.add_argument('--work', required=True, type=Path)
    args = ap.parse_args()
    ancestor = args.work.parent
    while not ancestor.exists():
        ancestor = ancestor.parent
    if shutil.disk_usage(ancestor).free < 20 * 1024**3:
        raise RuntimeError('STOP: less than 20 GiB free')
    args.work.mkdir(parents=True, exist_ok=False)
    gpu = Path(__file__).resolve().parents[1]
    results = []
    for name, src in [('ordinary', SIMPLE), ('lds-pressure', PLANTED)]:
        folder = args.work/name
        folder.mkdir()
        plan = dict(graph='cost-'+name, words=128, workgroupSize=64, wireBase=[0,64],
                    wireLen=[64,64], consts=[], tables=[], inputs=[0], outputs=[1],
                    stages=[dict(file='stage_0.wgsl', threads=64)])
        (folder/'plan.json').write_text(json.dumps(plan))
        (folder/'stage_0.wgsl').write_text(src)
        vectors = [[i*71+19 for i in range(64)], [2**32-1+i*917 for i in range(64)]]
        (folder/'expected.tsv').write_text(''.join(f'{k}\t'+','.join(map(str,v))+'\t'+','.join(str(x+1) for x in v)+'\n' for k,v in enumerate(vectors)))
        env = dict(os.environ, RADV_DEBUG='shaders,shaderstats', MESA_SHADER_CACHE_DISABLE='true',
                   VK_ICD_FILENAMES='/usr/share/vulkan/icd.d/radeon_icd.x86_64.json')
        run = subprocess.run([str(args.runner.resolve()), str(folder), '--adapter', 'radv'], env=env, text=True, capture_output=True)
        (folder/'run.txt').write_text(run.stdout)
        (folder/'radv.txt').write_text(run.stderr)
        if run.returncode:
            raise RuntimeError(f'{name} failed correctness/runtime: {run.stdout}\n{run.stderr[-4000:]}')
        record = run.stderr.split('shader: MESA_SHADER_COMPUTE')[-1]
        # Mesa 24.2.8 does not print wave_size. ACO's allocated VCC register
        # class does: s2 is the 64-lane mask, s1 the 32-lane mask.
        masks = set(re.findall(r'\bs([12]): %\d+:vcc\b', record))
        if len(masks) != 1:
            raise RuntimeError('ambiguous/missing ACO VCC mask width; refusing guessed wave size')
        wave_size = 32 * int(next(iter(masks)))
        subprocess.run([sys.executable, str(gpu/'isa_extract.py'), str(folder/'radv.txt'), str(folder/'plan.json'), str(folder/'isa.txt'), run.stdout.strip().splitlines()[-1]], check=True)
        result = grade(plan, (folder/'isa.txt').read_text(), wave_size)
        observed = re.search(r'^Subgroups per SIMD: (\d+)$', record, re.M)
        if observed is None or int(observed.group(1)) != result['stages'][0]['mesa_max_waves']:
            raise RuntimeError('occupancy prediction disagrees with RADV Subgroups per SIMD')
        result['radv_subgroups_per_simd'] = int(observed.group(1))
        result['wave_size_evidence'] = 'ACO VCC allocation register class s' + next(iter(masks))
        result['shader_sha256'] = hashlib.sha256(src.encode()).hexdigest()
        # Headers include the graph name and statistics, so hashing the whole
        # extracted file cannot establish that the actual instructions changed.
        words = re.findall(r'^\t.*?;\s*((?:[0-9a-f]{8}\s*)+)$',
                           (folder/'isa.txt').read_text(), re.M)
        machine_code = bytes.fromhex(''.join(''.join(row.split()) for row in words))
        if not machine_code:
            raise RuntimeError('no machine-code dwords extracted')
        result['machine_code_sha256'] = hashlib.sha256(machine_code).hexdigest()
        (folder/'grade.json').write_text(json.dumps(result, indent=2)+'\n')
        results.append(result)
    a,b = [r['stages'][0] for r in results]
    if b['lds_bytes'] <= a['lds_bytes'] or b['mesa_waves_per_simd'] >= a['mesa_waves_per_simd']:
        raise RuntimeError('real LDS plant did not raise reported LDS and lower predicted residency')
    if results[0]['machine_code_sha256'] == results[1]['machine_code_sha256']:
        raise RuntimeError('plant did not change machine code')
    print(f"PASS: real shader LDS {a['lds_bytes']} -> {b['lds_bytes']} bytes; Mesa waves/SIMD {a['mesa_waves_per_simd']} -> {b['mesa_waves_per_simd']}; both exact vectors passed")

if __name__ == '__main__':
    main()
