#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
LEAN_DIR="${REPO_ROOT}/lean"

echo "=========================================================="
echo "=== [M4 Challenger 2: Adversarial & Stress Harness] ==="
echo "=========================================================="
echo "Working directory: ${REPO_ROOT}"

# 1. Hardware boundary check (Requirement R6)
echo ""
echo "[1/4] Checking Hardware isolation (zero modifications rule)..."
if [ -n "$(git -C "${REPO_ROOT}" diff --stat lane-m3..HEAD -- lean/Obend/Hardware/)" ]; then
  echo "ERROR: lean/Obend/Hardware/ was modified relative to lane-m3!"
  exit 1
fi
if [ -n "$(git -C "${REPO_ROOT}" status --porcelain lean/Obend/Hardware/)" ]; then
  echo "ERROR: lean/Obend/Hardware/ has unstaged/untracked modifications!"
  exit 1
fi
echo "[PASS] lean/Obend/Hardware/ has 0 modifications."

# 2. Challenger 2 Stress Test Suite
echo ""
echo "[2/4] Running Challenger 2 Empirical Stress Test Suite..."
cd "${LEAN_DIR}"
lake env lean --run tests/m4/Milestone4Challenger2Test.lean
echo "[PASS] Challenger 2 Empirical Stress Test Suite succeeded."

# 3. Worker Milestone 4 and Adversarial Suites
echo ""
echo "[3/4] Running Worker Functional and Adversarial Suites..."
lake env lean --run tests/m4/Milestone4Test.lean
lake env lean --run tests/m4/Milestone4AdversarialTest.lean
lake env lean tests/m4/Milestone4Axioms.lean
echo "[PASS] Worker suites and axiom hygiene verified."

# 4. Full Census build check
echo ""
echo "[4/4] Verifying library build of Obend.Consensus and Obend.Fold.Collapse..."
lake build Obend.Consensus Obend.Fold.Collapse
echo "[PASS] Library targets built cleanly."

echo ""
echo "=========================================================="
echo "=== [M4 Challenger 2 Stress Harness: ALL PASSED] ==="
echo "=========================================================="
