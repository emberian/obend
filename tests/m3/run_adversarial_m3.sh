#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
LEAN_DIR="${REPO_ROOT}/lean"

echo "=========================================================="
echo "=== [M3 Empirical Challenger & Adversarial Runner] ==="
echo "=========================================================="
echo "Working directory: ${REPO_ROOT}"

# 1. Hardware immutability check
echo ""
echo "[1/6] Checking Hardware isolation (zero modifications rule)..."
if git -C "${REPO_ROOT}" diff --stat HEAD -- lean/Obend/Hardware/ | grep -q .; then
  echo "ERROR: lean/Obend/Hardware/ was modified!"
  exit 1
fi
echo "[PASS] lean/Obend/Hardware/ has 0 modifications."

# 2. Worker baseline test suite
echo ""
echo "[2/6] Running Worker Milestone3Test suite..."
cd "${LEAN_DIR}"
lake env lean tests/m3/Milestone3Test.lean
echo "[PASS] Worker Milestone3Test suite completed successfully."

# 3. Adversarial test suite
echo ""
echo "[3/6] Running Milestone3AdversarialTest suite..."
lake env lean tests/m3/Milestone3AdversarialTest.lean
echo "[PASS] Milestone3AdversarialTest suite completed successfully."

# 4. Axiom hygiene verification
echo ""
echo "[4/6] Verifying axiom hygiene for Milestone 3..."
lake env lean tests/m3/Milestone3Axioms.lean
echo "[PASS] All Milestone 3 metatheorems rely strictly on standard Lean core axioms [propext, Classical.choice, Quot.sound] with 0 sorries."

# 5. Rust Sandbox Crate Tests
echo ""
echo "[5/6] Running cargo test in crates/obend-sandbox..."
cd "${REPO_ROOT}/crates/obend-sandbox"
cargo test
echo "[PASS] crates/obend-sandbox cargo test passed cleanly."

# 6. Bubblewrap and Launch-Gate protocol verification
echo ""
echo "[6/6] Verifying deploy/grain-host launcher protocol handshakes..."
cd "${REPO_ROOT}"
gate_proto=$(./deploy/grain-host/bwrap --launch-gate-protocol)
if [[ "${gate_proto}" != "obend-grain-launch-gate-v1" ]]; then
  echo "ERROR: bwrap --launch-gate-protocol mismatch: ${gate_proto}"
  exit 1
fi
ctrl_proto=$(./deploy/grain-host/bwrap --controller-manager-protocol)
if [[ "${ctrl_proto}" != "obend-controller-manager-v1" ]]; then
  echo "ERROR: bwrap --controller-manager-protocol mismatch: ${ctrl_proto}"
  exit 1
fi
echo "[PASS] deploy/grain-host launcher protocols verified."

echo ""
echo "=========================================================="
echo "=== [M3 Empirical Challenger Verification PASSED] ==="
echo "=========================================================="
