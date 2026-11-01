#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
LEAN_DIR="${REPO_ROOT}/lean"

echo "=========================================================="
echo "=== [M4 Empirical Challenger 1 Verification Harness]  ==="
echo "=========================================================="
echo "Working directory: ${REPO_ROOT}"

# 1. Hardware immutability check (Requirement R6)
echo ""
echo "[1/7] Checking Hardware isolation (zero modifications rule)..."
if [ -n "$(git -C "${REPO_ROOT}" diff --stat lane-m3..HEAD -- lean/Obend/Hardware/)" ]; then
  echo "ERROR: lean/Obend/Hardware/ was modified relative to lane-m3!"
  exit 1
fi
if [ -n "$(git -C "${REPO_ROOT}" status --porcelain lean/Obend/Hardware/)" ]; then
  echo "ERROR: lean/Obend/Hardware/ has unstaged/untracked modifications!"
  exit 1
fi
echo "[PASS] lean/Obend/Hardware/ has 0 modifications."

# 2. Worker baseline unit tests
echo ""
echo "[2/7] Running Worker Milestone4Test suite..."
cd "${LEAN_DIR}"
lake env lean --run tests/m4/Milestone4Test.lean
echo "[PASS] Worker Milestone4Test suite completed successfully."

# 3. Worker adversarial test suite
echo ""
echo "[3/7] Running Worker Milestone4AdversarialTest suite..."
lake env lean --run tests/m4/Milestone4AdversarialTest.lean
echo "[PASS] Worker Milestone4AdversarialTest suite completed successfully."

# 4. Axiom hygiene verification
echo ""
echo "[4/7] Verifying axiom hygiene for Milestone 4..."
lake env lean tests/m4/Milestone4Axioms.lean
echo "[PASS] All Milestone 4 metatheorems rely strictly on standard Lean core axioms [propext, Classical.choice, Quot.sound] with 0 sorries."

# 5. Challenger empirical stress test suite
echo ""
echo "[5/7] Running Challenger Milestone4ChallengerTest suite..."
lake env lean --run tests/m4/Milestone4ChallengerTest.lean
echo "[PASS] Challenger Milestone4ChallengerTest suite completed successfully."

# 6. Library build check
echo ""
echo "[6/7] Building library tier 1 (Obend.Consensus & Obend.Fold.Collapse)..."
lake build Obend.Consensus Obend.Fold.Collapse
echo "[PASS] Milestone 4 consensus and library build complete."

# 7. E2E Test Suite Run
echo ""
echo "[7/7] Running full E2E test suite runner..."
cd "${REPO_ROOT}"
python3 tests/e2e/runner.py
echo "[PASS] Full E2E test suite passed 100%."

echo ""
echo "=========================================================="
echo "=== [M4 EMPIRICAL CHALLENGER VERIFICATION PASSED]      ==="
echo "=========================================================="
