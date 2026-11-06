#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
CATGRAD=${CATGRAD:-$HOME/hellas/catgrad}
OPEN_HYPERGRAPHS=${OPEN_HYPERGRAPHS:-$HOME/hellas/open-hypergraphs}
BUILD=${CATGRAD_ORACLE_BUILD:-$(mktemp -d "${TMPDIR:-/tmp}/obend-catgrad-oracle.XXXXXX")}
mkdir -p "$BUILD"
python3 - "$HERE" "$CATGRAD" "$OPEN_HYPERGRAPHS" "$BUILD" <<'PY'
import pathlib, sys
here, catgrad, oh, build = map(pathlib.Path, sys.argv[1:])
s = (here/'oracle/Cargo.toml.in').read_text()
for key, value in [('CATGRAD',catgrad),('OPEN_HYPERGRAPHS',oh),('SOURCE',here/'oracle')]:
    s = s.replace('@'+key+'@', str(value.resolve()))
(build/'Cargo.toml').write_text(s)
original = (catgrad/'catgrad/examples/hidden.rs').read_text()
assert original.count('nn::Sigmoid.call(builder, [x])') == 2
adapted = original.replace('nn::Sigmoid.call(builder, [x])', 'integer_clip(builder, x)').replace('Dtype::F32', 'Dtype::U32')
adapted += """
fn integer_clip(builder: &Builder, x: Var) -> Var {
    let sh = shape(builder, x.clone());
    let cap = constant(builder, 600u32, &sh);
    let under = lt(builder, x.clone(), cap.clone());
    where_cond(builder, under, x, cap)
}
"""
(build/'upstream_hidden.rs').write_text(adapted)
(build/'upstream_hidden_original.rs').write_text(original)

PY
cp "$HERE/oracle/Cargo.lock" "$BUILD/Cargo.lock"
source_revision() {
  if [[ -f "$1/.obend-source-revision" ]]; then cat "$1/.obend-source-revision";
  else git -C "$1" rev-parse HEAD; fi
}
printf 'catgrad source: '; source_revision "$CATGRAD"
printf 'open-hypergraphs source: '; source_revision "$OPEN_HYPERGRAPHS"
cargo run --locked --release --manifest-path "$BUILD/Cargo.toml" -- "${1:-$HERE/mlp.json}"
