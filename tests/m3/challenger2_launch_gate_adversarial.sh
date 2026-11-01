#!/usr/bin/env bash
# Challenger 2: Adversarial Stress Test Harness for deploy/grain-host/launch-gate
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
LAUNCH_GATE="${REPO_ROOT}/deploy/grain-host/launch-gate"

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
echo "=== [Challenger 2: Launch-Gate Adversarial Probes] ==="
echo "=========================================================="

TEST_TMP=$(mktemp -d /tmp/obend-launch-test-XXXXXX)
trap 'rm -rf "$TEST_TMP"' EXIT

# 1. Reject non-0700 state directory
chmod 0755 "$TEST_TMP"
set +e
out=$("$LAUNCH_GATE" init "$TEST_TMP" "obend-grain-t1-o1" 2>&1)
rc=$?
set -e
assert_eq "State Dir Permissions: 0755 directory rejected" "1" "$rc"

# Fix directory to 0700
chmod 0700 "$TEST_TMP"

# 2. Reject malformed unit names
set +e
out=$("$LAUNCH_GATE" init "$TEST_TMP" "evil-unit-name" 2>&1)
rc=$?
set -e
assert_eq "Unit Validation: evil unit name rejected" "1" "$rc"

set +e
out=$("$LAUNCH_GATE" init "$TEST_TMP" "obend-grain-t1" 2>&1)
rc=$?
set -e
assert_eq "Unit Validation: missing operation index rejected" "1" "$rc"

# 3. Successful gate init
out=$("$LAUNCH_GATE" init "$TEST_TMP" "obend-grain-t1-o1" 2>&1)
assert_eq "Init: armed obend-grain-t1-o1" "armed obend-grain-t1-o1" "$out"

# Check permissions of the created .gate file (must be 0600)
perm=$(stat -c "%a" "${TEST_TMP}/obend-grain-t1-o1.gate" 2>/dev/null || stat -f "%Lp" "${TEST_TMP}/obend-grain-t1-o1.gate" 2>/dev/null)
assert_eq "Gate File Permissions: mode 0600 enforced" "600" "$perm"

# 4. Double init attack rejected
set +e
out=$("$LAUNCH_GATE" init "$TEST_TMP" "obend-grain-t1-o1" 2>&1)
rc=$?
set -e
assert_eq "Double Init Attack: rejected" "1" "$rc"

# 5. One-shot execution: launch-gate run transitions to started
out=$("$LAUNCH_GATE" run "$TEST_TMP" "obend-grain-t1-o1" -- /bin/echo "running worker" 2>&1)
assert_eq "Run: executes target binary" "running worker" "$out"

# Verify gate file content contains 'started'
first_line=$(head -n 1 "${TEST_TMP}/obend-grain-t1-o1.gate")
assert_eq "State Transition: gate state is 'started'" "started" "$first_line"

# 6. Replay attack: launch-gate run on already started gate must fail
set +e
out=$("$LAUNCH_GATE" run "$TEST_TMP" "obend-grain-t1-o1" -- /bin/echo "replay worker" 2>&1)
rc=$?
set -e
assert_eq "Replay Attack: run on started gate rejected" "1" "$rc"

# 7. Fence transition
out=$("$LAUNCH_GATE" fence "$TEST_TMP" "obend-grain-t1-o2" 2>&1)
assert_eq "Fence: fenced obend-grain-t1-o2" "fenced obend-grain-t1-o2" "$out"

# 8. Execution on fenced gate must fail
set +e
out=$("$LAUNCH_GATE" run "$TEST_TMP" "obend-grain-t1-o2" -- /bin/echo "fenced worker" 2>&1)
rc=$?
set -e
assert_eq "Fenced Gate: run on fenced gate rejected" "1" "$rc"

echo "=========================================================="
echo "=== [Launch-Gate Adversarial Summary: ${PASS_COUNT} Passed, ${FAIL_COUNT} Failed] ==="
echo "=========================================================="

if [[ $FAIL_COUNT -gt 0 ]]; then
  exit 1
fi
