#!/usr/bin/env bash
# Source book files and source-program fixtures, checked on the actual GPU.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
EMIT=${OBEND_EMIT_GPU:-$ROOT/lean/.lake/build/bin/obend-emit-gpu}
RUN=${OBEND_GPU_RUN:-$HERE/runner/target/release/obend-gpu-run}
OBEND=${OBEND_BIN:-$ROOT/lean/.lake/build/bin/obend}
OUT=${SOURCE_GATE_OUT:-$(mktemp -d "${TMPDIR:-/tmp}/obend-source-gate.XXXXXX")}
mkdir -p "$OUT"
[[ -x "$OBEND" ]] || { echo "FAIL: required obend executable not found: $OBEND" >&2; exit 1; }
# Match verify_gpu.sh's Linux driver selection; GPU_ICD=any leaves the caller's choice alone.
RADEON_ICD=/usr/share/vulkan/icd.d/radeon_icd.x86_64.json
if [[ "$(uname -s)" == Linux && -r "$RADEON_ICD" && "${GPU_ICD:-radv}" != any ]]; then
  export VK_ICD_FILENAMES="$RADEON_ICD"
fi
"$EMIT" leaf-example --out "$OUT/example"
"$EMIT" leaf "$OUT/example/example.book.json" run "$OUT/example/inputs.json" --out "$OUT/book"
# An independent Python word-arithmetic oracle checks the file workflow's expected output.
check_affine() {
python3 - "$1" <<'PY'
import pathlib, sys
mask = (1 << 64) - 1
def signed(x):
    x &= mask
    return x - (1 << 64) if x >= 1 << 63 else x
for line in pathlib.Path(sys.argv[1]).read_text().splitlines():
    _, inputs, outputs = line.split('\t')
    xs = [int(v) for v in inputs.split(',')]
    ys = [int(v) for v in outputs.split(',')]
    assert ys == [signed(3*x + 5) for x in xs], (xs,ys)
print('book expected values agree with independent modular-integer oracle')
PY
}
check_affine "$OUT/book/expected.tsv"
"$RUN" "$OUT/book" "$@"
"$EMIT" leaf "$OUT/example/example.book.json" run "$OUT/example/inputs.json" --out "$OUT/book-plant" --plant addAsSub
if "$RUN" "$OUT/book-plant" "$@" > "$OUT/book-plant.log" 2>&1; then
  echo 'FAIL: planted book shader survived' >&2; exit 1
fi
if grep -Eq 'Validation Error|wgpu error|panicked|failed to create' "$OUT/book-plant.log"; then
  cat "$OUT/book-plant.log"; echo 'FAIL: plant failed before value comparison' >&2; exit 1
fi
grep -q 'vectors disagree' "$OUT/book-plant.log"
echo 'caught planted book addAsSub by output comparison'
# Start from literal Objective Bend surface text, using the ordinary source driver.
SURFACE="$HERE/source/Affine.obend"
SURFACE_INPUTS="$HERE/source/Affine.inputs.json"
"$OBEND" check "$SURFACE" > "$OUT/surface-check.log"
"$OBEND" run "$SURFACE" small > "$OUT/surface-small.log"
"$OBEND" run "$SURFACE" boundary > "$OUT/surface-boundary.log"
grep -qx 'status: finished' "$OUT/surface-small.log"
grep -qx 'result: 26' "$OUT/surface-small.log"
grep -qx 'status: finished' "$OUT/surface-boundary.log"
grep -qx 'result: 2' "$OUT/surface-boundary.log"
"$OBEND" emit "$SURFACE" --object affine --out "$OUT/surface.book.json" --call run 7 > "$OUT/surface-emit.log"
"$EMIT" leaf "$OUT/surface.book.json" run "$SURFACE_INPUTS" --out "$OUT/surface"
check_affine "$OUT/surface/expected.tsv"
"$RUN" "$OUT/surface" "$@"
"$EMIT" leaf "$OUT/surface.book.json" run "$SURFACE_INPUTS" --out "$OUT/surface-plant" --plant addAsSub
if "$RUN" "$OUT/surface-plant" "$@" > "$OUT/surface-plant.log" 2>&1; then
  echo 'FAIL: planted surface-source shader survived' >&2; exit 1
fi
if grep -Eq 'Validation Error|wgpu error|panicked|failed to create' "$OUT/surface-plant.log"; then
  cat "$OUT/surface-plant.log"; echo 'FAIL: surface plant failed before value comparison' >&2; exit 1
fi
grep -q 'vectors disagree' "$OUT/surface-plant.log"
echo 'surface source run, book emission and GPU agree; caught planted addAsSub by output comparison'
# Includes shifts at 63,64,65,2^32,2^63 and signed Q8-to-Q16 squaring.
mapfile -t SOURCES < <("$EMIT" list | grep '^source-leaf-')
[[ ${#SOURCES[@]} -gt 0 ]]
for source in "${SOURCES[@]}"; do
  "$EMIT" "$source" --out "$OUT/$source"
  "$RUN" "$OUT/$source" "$@"
done
printf '[[0],[1,2]]\n' > "$OUT/wrong-shape.json"
printf '{}\n' > "$OUT/bad-book.json"
refuse() {
  local name=$1 diagnostic=$2
  shift 2
  if "$EMIT" leaf "$@" --out "$OUT/$name" > "$OUT/$name.log" 2>&1; then
    echo "FAIL: accepted $name" >&2; exit 1
  fi
  grep -q "$diagnostic" "$OUT/$name.log"
  test ! -e "$OUT/$name/plan.json"
  echo "refused $name before emission"
}
refuse missing-member 'unknown Leaf member' "$OUT/example/example.book.json" absent "$OUT/example/inputs.json"
refuse wrong-shape 'input array shapes differ' "$OUT/example/example.book.json" run "$OUT/wrong-shape.json"
refuse bad-book 'composition' "$OUT/bad-book.json" run "$OUT/example/inputs.json"
echo "PASS source book GPU gate; retained artifacts in $OUT"
