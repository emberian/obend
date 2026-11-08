#!/usr/bin/env python3
"""Exercise runner batching against an in-place reset-sensitive shader and CLI limits."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--runner', required=True, type=Path)
ap.add_argument('--adapter', default='radv')
args = ap.parse_args()
runner = args.runner.resolve()
fixture = Path(__file__).resolve().parent/'batch-reset-check'
# 132 repetitions include three warmups, spanning the 128-pass command-buffer limit.
subprocess.run([str(runner), str(fixture), '--adapter', args.adapter, '--bench', '129'], check=True)
for n in ['0', '1025', '18446744073709551615']:
    r = subprocess.run([str(runner), str(fixture), '--bench', n], capture_output=True, text=True)
    assert r.returncode == 2 and 'sample count' in r.stderr, (n, r.stderr)
for name, mutate, samples in [
    ('empty', lambda p: p.update(stages=[]), '1'),
    ('dispatch-bound', lambda p: p.update(stages=p['stages']*65), '1024'),
    ('reset-memory-bound', lambda p: p.update(words=512*1024*1024//8+1), '1'),
]:
    with tempfile.TemporaryDirectory(prefix='obend-batch-test-') as tmp:
        folder = Path(tmp)
        plan = json.loads((fixture/'plan.json').read_text())
        mutate(plan)
        (folder/'plan.json').write_text(json.dumps(plan))
        (folder/'expected.tsv').write_text((fixture/'expected.tsv').read_text())
        r = subprocess.run([str(runner), str(folder), '--bench', samples], capture_output=True, text=True)
        assert r.returncode == 1 and 'benchmark' in r.stderr, (name, r.stdout, r.stderr)
print('PASS: reset-sensitive batch and sample/stage/dispatch/memory limits')
