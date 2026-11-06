#!/usr/bin/env bash
# External catgrad -> serialized OpenHypergraph -> Lean ArrayGraph -> real GPU.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
EMIT=${EMIT:-$ROOT/lean/.lake/build/bin/obend-emit-gpu}
RUN=${RUN:-$ROOT/hardware/gpu/runner/target/release/obend-gpu-run}
OUT=${CATGRAD_GATE_OUT:-$(mktemp -d "${TMPDIR:-/tmp}/obend-catgrad-gate.XXXXXX")}
mkdir -p "$OUT"
"$HERE/run_oracle.sh" "$OUT/mlp.json"
cmp "$HERE/mlp.json" "$OUT/mlp.json"
"$EMIT" catgrad "$OUT/mlp.json" --out "$OUT/good"
python3 - "$HERE/SHA256SUMS" "$OUT/good" <<'PY_HASH'
import hashlib, pathlib, sys
manifest, root = map(pathlib.Path, sys.argv[1:])
for line in manifest.read_text().splitlines():
    expected, name = line.split()
    actual = hashlib.sha256((root/name).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"artifact changed: {name}: {actual} != {expected}")
print('shader/plan/vector artifact digests match')
PY_HASH
"$RUN" "$OUT/good" "$@"
for plant in addAsSub swapMux; do
  "$EMIT" catgrad "$OUT/mlp.json" --out "$OUT/$plant" --plant "$plant"
  if "$RUN" "$OUT/$plant" "$@" > "$OUT/$plant.log" 2>&1; then
    echo "FAIL: planted $plant survived" >&2; exit 1
  fi
  if ! grep -q 'vectors disagree' "$OUT/$plant.log"; then
    cat "$OUT/$plant.log"; echo 'FAIL: planted run failed before value comparison' >&2; exit 1
  fi
  echo "caught planted $plant"
done
# The upstream U32 backend returns word-valued comparisons and accepts every
# nonzero U32 condition. Keep those semantics, wrapping scalar arithmetic and
# their compositions tied to the external interpreter, rather than assuming Bool.
"$EMIT" catgrad "$OUT/scalar-ops.json" --out "$OUT/scalar-ops"
"$RUN" "$OUT/scalar-ops" "$@"
for plant in addAsSub swapMux; do
  "$EMIT" catgrad "$OUT/scalar-ops.json" --out "$OUT/scalar-$plant" --plant "$plant"
  if "$RUN" "$OUT/scalar-$plant" "$@" > "$OUT/scalar-$plant.log" 2>&1; then
    echo "FAIL: scalar boundary planted $plant survived" >&2; exit 1
  fi
  if ! grep -q 'vectors disagree' "$OUT/scalar-$plant.log"; then
    cat "$OUT/scalar-$plant.log"; echo 'FAIL: scalar plant failed before value comparison' >&2; exit 1
  fi
  echo "caught scalar boundary planted $plant"
done
# Named refusal and independent-oracle disagreement must both happen before shader emission.
python3 - "$OUT" <<'PY'
import json, pathlib, sys
p = pathlib.Path(sys.argv[1]); source = json.loads((p/'mlp.json').read_text())
for name in ['unsupported','float','oracle_fault','shape','linear']:
    d = json.loads(json.dumps(source))
    if name == 'unsupported': d['term']['hypergraph']['edges'][0] = {'Arr':{'Tensor':{'Map':'Exp'}}}
    elif name == 'float': d['inputTypes'][0]['dtype'] = 'F32'
    elif name == 'shape': d['inputTypes'][0]['shape'] = [1,1568]
    elif name == 'linear': d['term']['hypergraph']['adjacency'][1]['sources'] = [0]
    else: d['vectors'][0]['outputs'][0][0] += 1
    (p/(name+'.json')).write_text(json.dumps(d))
PY
for spec in 'unsupported:Tensor.Map.Exp' 'float:unsupported catgrad dtype F32' 'oracle_fault:catgrad interpreter/model disagreement' 'shape:MatMul: contraction dimensions disagree' 'linear:multiple reads require explicit Copy'; do
  name=${spec%%:*}; diagnostic=${spec#*:}
  if "$EMIT" catgrad "$OUT/$name.json" --out "$OUT/$name" > "$OUT/$name.log" 2>&1; then
    echo "FAIL: $name accepted" >&2; exit 1
  fi
  grep -q "$diagnostic" "$OUT/$name.log"
  test ! -e "$OUT/$name/plan.json"
  echo "refused $name by name"
done
echo "PASS catgrad MLP gate; artifacts and timing logs in $OUT"
