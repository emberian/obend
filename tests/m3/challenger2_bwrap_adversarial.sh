#!/usr/bin/env bash
# Challenger 2: Adversarial Stress Test Harness for deploy/grain-host/bwrap
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
BWRAP="${REPO_ROOT}/deploy/grain-host/bwrap"

PASS_COUNT=0
FAIL_COUNT=0

assert_eq() {
  local desc="$1"
  local expected="$2"
  local actual="$3"
  if [[ "$expected" == "$actual" ]]; then
    echo "[PASS] $desc"
    PASS_COUNT=$((PASS_COUNT + 1))
  else
    echo "[FAIL] $desc: expected '$expected', got '$actual'"
    FAIL_COUNT=$((FAIL_COUNT + 1))
  fi
}

echo "=========================================================="
echo "=== [Challenger 2: Grain-Host Bwrap Adversarial Probes] ==="
echo "=========================================================="

# 1. Protocol handshakes
out=$("$BWRAP" --launch-gate-protocol 2>&1)
assert_eq "Handshake: launch-gate protocol returns obend-grain-launch-gate-v1" "obend-grain-launch-gate-v1" "$out"

out=$("$BWRAP" --controller-manager-protocol 2>&1)
assert_eq "Handshake: controller-manager protocol returns obend-controller-manager-v1" "obend-controller-manager-v1" "$out"

# Setup temporary test directories
TEST_TMP=$(mktemp -d /tmp/obend-challenger-test-XXXXXX)
trap 'rm -rf "$TEST_TMP"' EXIT

WORKSPACE="${TEST_TMP}/workspace"
RUNTIME="${TEST_TMP}/runtime"
SECRET_DIR="${TEST_TMP}/secret_controller_state"
mkdir -p "$WORKSPACE" "$RUNTIME" "$SECRET_DIR"

touch "${SECRET_DIR}/custody.key"
touch "${SECRET_DIR}/task.cfg"
touch "${SECRET_DIR}/host.cfg"

export OBEND_GRAIN_STATE_DIR="${SECRET_DIR}"
export OBEND_GRAIN_CUSTODY_KEY="${SECRET_DIR}/custody.key"
export OBEND_GRAIN_TASK_CONFIG="${SECRET_DIR}/task.cfg"
export OBEND_GRAIN_HOST_CONFIG="${SECRET_DIR}/host.cfg"
export OBEND_GRAIN_UNIT="obend-grain-t1-o1"

# 2. Secret Leak Defense: Mounting controller state directory must exit with code 77
set +e
"$BWRAP" --workspace "$SECRET_DIR" --runtime-root "$RUNTIME" --network none -- /agent/bin/obend >/dev/null 2>&1
rc=$?
set -e
assert_eq "Secret Leak Defense: mounting exact secret dir as workspace rejected with code 77" "77" "$rc"

# Secret Leak Defense: Mounting an ancestor directory containing secrets must exit with code 77
set +e
"$BWRAP" --workspace "$TEST_TMP" --runtime-root "$RUNTIME" --network none -- /agent/bin/obend >/dev/null 2>&1
rc=$?
set -e
assert_eq "Secret Leak Defense: mounting ancestor of secret state as workspace rejected with code 77" "77" "$rc"

# 3. Path Traversal Attacks in Target Program: Must exit with code 64
set +e
"$BWRAP" --workspace "$WORKSPACE" --runtime-root "$RUNTIME" --network none -- /agent/../etc/passwd >/dev/null 2>&1
rc=$?
set -e
assert_eq "Path Traversal: /agent/../etc/passwd rejected with code 64" "64" "$rc"

set +e
"$BWRAP" --workspace "$WORKSPACE" --runtime-root "$RUNTIME" --network none -- /bin/sh >/dev/null 2>&1
rc=$?
set -e
assert_eq "Path Boundary: non-/agent path rejected with code 64" "64" "$rc"

# 4. Unit Name Format Attacks: Must exit with code 64
set +e
OBEND_GRAIN_UNIT="obend-evil-unit" "$BWRAP" --workspace "$WORKSPACE" --runtime-root "$RUNTIME" --network none -- /agent/bin/obend >/dev/null 2>&1
rc=$?
set -e
assert_eq "Unit Name: unformatted unit rejected with code 64" "64" "$rc"

set +e
OBEND_GRAIN_UNIT="obend-grain-t1" "$BWRAP" --workspace "$WORKSPACE" --runtime-root "$RUNTIME" --network none -- /agent/bin/obend >/dev/null 2>&1
rc=$?
set -e
assert_eq "Unit Name: missing operation index rejected with code 64" "64" "$rc"

# 5. Runtime Max Sec Exceeded: Must exit with code 64
set +e
OBEND_GRAIN_RUNTIME_MAX_SEC="1801" "$BWRAP" --workspace "$WORKSPACE" --runtime-root "$RUNTIME" --network none -- /agent/bin/obend >/dev/null 2>&1
rc=$?
set -e
assert_eq "Runtime Max: runtime_max_sec > 1800 rejected with code 64" "64" "$rc"

set +e
OBEND_GRAIN_RUNTIME_MAX_SEC="0" "$BWRAP" --workspace "$WORKSPACE" --runtime-root "$RUNTIME" --network none -- /agent/bin/obend >/dev/null 2>&1
rc=$?
set -e
assert_eq "Runtime Max: runtime_max_sec = 0 rejected with code 64" "64" "$rc"

# 6. Network parameter validation: Must exit with code 64
set +e
"$BWRAP" --workspace "$WORKSPACE" --runtime-root "$RUNTIME" --network promiscuous -- /agent/bin/obend >/dev/null 2>&1
rc=$?
set -e
assert_eq "Network Mode: invalid network mode rejected with code 64" "64" "$rc"

# 7. Non-existent workspace: Must exit with code 64
set +e
"$BWRAP" --workspace "${TEST_TMP}/nonexistent" --runtime-root "$RUNTIME" --network none -- /agent/bin/obend >/dev/null 2>&1
rc=$?
set -e
assert_eq "Workspace Validation: non-existent workspace rejected with code 64" "64" "$rc"

echo "=========================================================="
echo "=== [Grain-Host Bwrap Adversarial Summary: ${PASS_COUNT} Passed, ${FAIL_COUNT} Failed] ==="
echo "=========================================================="

if [[ $FAIL_COUNT -gt 0 ]]; then
  exit 1
fi
