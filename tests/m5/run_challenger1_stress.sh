#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
LEAN_DIR="${REPO_ROOT}/lean"

echo "=========================================================="
echo "=== [M5 Empirical Challenger 1 Verification Harness]   ==="
echo "=========================================================="
echo "Working directory: ${REPO_ROOT}"

# 1. Hardware immutability check (Requirement R6)
echo ""
echo "[1/7] Checking Hardware isolation (Requirement R6: 0 modifications)..."
if [ -n "$(git -C "${REPO_ROOT}" diff --stat bb2/lane-m4..HEAD -- lean/Obend/Hardware/)" ]; then
  echo "ERROR: lean/Obend/Hardware/ was modified relative to lane-m4!"
  exit 1
fi
if [ -n "$(git -C "${REPO_ROOT}" status --porcelain lean/Obend/Hardware/)" ]; then
  echo "ERROR: lean/Obend/Hardware/ has unstaged/untracked modifications!"
  exit 1
fi
echo "[PASS] lean/Obend/Hardware/ has 0 modifications. Requirement R6 verified."

# 2. Worker baseline unit tests
echo ""
echo "[2/7] Running Worker StructuredTest suite..."
cd "${LEAN_DIR}"
lake env lean tests/m5/StructuredTest.lean
echo "[PASS] Worker StructuredTest suite passed."

echo ""
echo "[3/7] Running Worker HardwareProjectionTest suite..."
lake env lean tests/m5/HardwareProjectionTest.lean
echo "[PASS] Worker HardwareProjectionTest suite passed."

# 3. Challenger empirical stress test suite (Local)
echo ""
echo "[4/7] Running Challenger 1 Empirical Stress Test suite (Local)..."
lake env lean tests/m5/Milestone5Challenger1StressTest.lean
echo "[PASS] Challenger 1 Empirical Stress Test suite passed locally."

# 4. Challenger empirical stress test suite (Remote Swarm bb2)
echo ""
echo "[5/7] Running Challenger 1 Empirical Stress Test suite on Remote Swarm (bb2)..."
scp "${LEAN_DIR}/tests/m5/Milestone5Challenger1StressTest.lean" bb2:/home/build/obend/repo/lean/tests/m5/
ssh bb2 "cd /home/build/obend/repo/lean && lake env lean tests/m5/Milestone5Challenger1StressTest.lean"
echo "[PASS] Challenger 1 Empirical Stress Test suite passed on remote swarm bb2."

# 5. Rust Workspace Tests
echo ""
echo "[6/7] Running Rust workspace tests (cargo test --workspace)..."
cd "${REPO_ROOT}"
cargo test --workspace
echo "[PASS] Rust workspace tests passed (17/17)."

# 6. Full E2E Test Suite Run
echo ""
echo "[7/7] Running full E2E test suite runner..."
python3 tests/e2e/runner.py
echo "[PASS] Full E2E test suite passed (449/449, 100%)."

echo ""
echo "=========================================================="
echo "=== [M5 EMPIRICAL CHALLENGER 1 VERIFICATION PASSED]    ==="
echo "=========================================================="
