#!/usr/bin/env bash
# Reproducible remote `hbox` build script for `rustc_guest.wasm` (`AGENTS.md` §1: zero macOS rustc!).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REMOTE_HOST="${OBEND_REMOTE_HOST:-hbox}"
REMOTE_DIR="~/.cache/obb-worktrees/w10-wasm-guest"

ssh "${REMOTE_HOST}" "mkdir -p ${REMOTE_DIR}"
scp -q "${SCRIPT_DIR}/guest.rs" "${REMOTE_HOST}:${REMOTE_DIR}/guest.rs"
ssh "${REMOTE_HOST}" "SWARM_MEM_MAX=12G timeout --kill-after=10s 600s rustc -D warnings --edition 2021 --crate-type cdylib -C opt-level=s -C panic=abort -C strip=debuginfo --target wasm32-unknown-unknown ${REMOTE_DIR}/guest.rs -o ${REMOTE_DIR}/rustc_guest.wasm"
scp -q "${REMOTE_HOST}:${REMOTE_DIR}/rustc_guest.wasm" "${SCRIPT_DIR}/rustc_guest.wasm"
ssh "${REMOTE_HOST}" "rm -rf ${REMOTE_DIR}"

BYTES="$(wc -c < "${SCRIPT_DIR}/rustc_guest.wasm" | tr -d ' ')"
if [ "${BYTES}" -ge 32768 ]; then
  echo "ERROR: rustc_guest.wasm (${BYTES} bytes) exceeds 32 KiB fixture cap" >&2
  exit 1
fi
echo "Built ${SCRIPT_DIR}/rustc_guest.wasm (${BYTES} bytes < 32768 B)"
