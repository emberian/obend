#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
LEAN_DIR="${REPO_ROOT}/lean"

echo "=========================================================="
echo "=== [M4 Empirical Challenger & Adversarial Runner] ==="
echo "=========================================================="
echo "Working directory: ${REPO_ROOT}"

# 1. Hardware immutability check (Requirement R6)
echo ""
echo "[1/5] Checking Hardware isolation (zero modifications rule)..."
if [ -n "$(git -C "${REPO_ROOT}" diff --stat lane-m3..HEAD -- lean/Obend/Hardware/)" ]; then
  echo "ERROR: lean/Obend/Hardware/ was modified relative to lane-m3!"
  exit 1
fi
if [ -n "$(git -C "${REPO_ROOT}" status --porcelain lean/Obend/Hardware/)" ]; then
  echo "ERROR: lean/Obend/Hardware/ has unstaged/untracked modifications!"
  exit 1
fi
echo "[PASS] lean/Obend/Hardware/ has 0 modifications."

# 2. Worker baseline test suite
echo ""
echo "[2/5] Running Worker Milestone4Test suite..."
cd "${LEAN_DIR}"
lake env lean --run tests/m4/Milestone4Test.lean
echo "[PASS] Worker Milestone4Test suite completed successfully."

# 3. Adversarial test suite
echo ""
echo "[3/5] Running Milestone4AdversarialTest suite..."
lake env lean --run tests/m4/Milestone4AdversarialTest.lean
echo "[PASS] Milestone4AdversarialTest suite completed successfully."

# 4. Axiom hygiene verification
echo ""
echo "[4/5] Verifying axiom hygiene for Milestone 4..."
lake env lean tests/m4/Milestone4Axioms.lean
echo "[PASS] All Milestone 4 metatheorems rely strictly on standard Lean core axioms [propext, Classical.choice, Quot.sound] with 0 sorries."

# 5. Census and Full Build Check
echo ""
echo "[5/5] Building library tier 1..."
lake build Obend.Consensus Obend.Fold.Collapse
echo "[PASS] Milestone 4 consensus and library build complete."

echo ""
echo "=========================================================="
echo "=== [M4 Empirical Challenger Verification PASSED] ==="
echo "=========================================================="
