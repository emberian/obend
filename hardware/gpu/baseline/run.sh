#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
avail=$(df -Pk . | awk 'NR==2 {print $4}')
(( avail >= 20 * 1024 * 1024 )) || { echo 'STOP: less than 20 GiB free' >&2; exit 1; }
export CARGO_BUILD_JOBS=2
export RUSTFLAGS='-C target-cpu=native'
cargo build --release --locked
printf '# measured_utc=%s\n' "$(date -u +%FT%TZ)"
lscpu | sed -n '/Model name:/p'
rustc --version
printf '# RUSTFLAGS=%s\n' "$RUSTFLAGS"
RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} target/release/obend-p3-baseline
