#!/usr/bin/env bash
# run_all.sh — Top-level test runner for Obend E2E Test Suite (Tiers 1-4).
# Supports local execution or remote execution on bb2 (dregg-build2) via swarm-build.
#
# Usage:
#   ./tests/e2e/run_all.sh                # Run all 4 tiers locally
#   ./tests/e2e/run_all.sh --tier 1       # Run only Tier 1
#   ./tests/e2e/run_all.sh --remote       # Sync and run on bb2 via SWARM_MEM_MAX=16G swarm-build
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"

REMOTE=0
TIER_ARG=""
EXTRA_ARGS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --remote|--bb2)
      REMOTE=1
      shift
      ;;
    --tier)
      TIER_ARG="--tier $2"
      shift 2
      ;;
    *)
      EXTRA_ARGS+=("$1")
      shift
      ;;
  esac
done

if [[ "$REMOTE" -eq 1 ]]; then
  echo "==> Synchronizing tests/ to bb2:~/obend/repo/tests/ ..."
  ssh -o BatchMode=yes bb2 "mkdir -p ~/obend/repo/tests/e2e"
  rsync -avz --delete "$REPO_ROOT/tests/e2e/" "build@bb2:~/obend/repo/tests/e2e/"

  echo "==> Executing E2E test suite on bb2 via SWARM_MEM_MAX=16G swarm-build ..."
  ssh -o BatchMode=yes bb2 "cd ~/obend/repo && SWARM_MEM_MAX=16G /usr/local/bin/swarm-build python3 tests/e2e/runner.py $TIER_ARG ${EXTRA_ARGS[*]:-}"
  exit $?
else
  echo "==> Executing E2E test suite locally ..."
  cd "$REPO_ROOT"
  python3 tests/e2e/runner.py $TIER_ARG ${EXTRA_ARGS[*]:-}
  exit $?
fi
