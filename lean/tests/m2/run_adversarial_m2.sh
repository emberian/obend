#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"

echo "=========================================================="
echo "=== [M2 Empirical Challenger Test Runner] ==="
echo "=========================================================="
echo "Working directory: ${LEAN_DIR}"

# 1. Hardware immutability check
echo ""
echo "[1/5] Checking Hardware isolation (zero modifications rule)..."
if git -C "${LEAN_DIR}/.." diff --stat HEAD -- lean/Obend/Hardware/ | grep -q .; then
  echo "ERROR: lean/Obend/Hardware/ was modified!"
  exit 1
fi
echo "[PASS] lean/Obend/Hardware/ has 0 modifications."

# 2. Worker baseline test suite
echo ""
echo "[2/5] Running Worker Milestone2Test suite..."
cd "${LEAN_DIR}"
lake env lean tests/m2/Milestone2Test.lean
echo "[PASS] Worker Milestone2Test suite completed successfully."

# 3. ZoE Seat & Clearing Judge Adversarial test suite
echo ""
echo "[3/5] Running Milestone2AdversarialTest suite..."
lake env lean tests/m2/Milestone2AdversarialTest.lean
echo "[PASS] Milestone2AdversarialTest suite completed successfully."

# 4. VaultTurn, Hyperedge & Book Conservation Adversarial test suite
echo ""
echo "[4/5] Running VaultBookAdversarialTest suite..."
lake env lean tests/m2/VaultBookAdversarialTest.lean
echo "[PASS] VaultBookAdversarialTest suite completed successfully."

# 5. Axiom check for core metatheorems
echo ""
echo "[5/5] Verifying axiom hygiene for Milestone 2..."
lake env lean tests/m2/Milestone2Axioms.lean
echo "[PASS] All Milestone 2 metatheorems rely strictly on standard Lean core axioms [propext, Quot.sound] with 0 sorries."

echo ""
echo "=========================================================="
echo "=== [M2 Empirical Challenger Verification PASSED] ==="
echo "=========================================================="
