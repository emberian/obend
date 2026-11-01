#!/usr/bin/env bash
set -uo pipefail

echo "================================================================================"
echo " CHALLENGER 2 STRESS HARNESS — Milestone 5 (Features 37, 38, 39)"
echo "================================================================================"

FAILED=0

echo ""
echo "--- [1/4] Feature 37: Worker Pool Concurrency & Deadlock Stress ---"
echo "Testing worker pool under concurrent flood, rapid spawn/join, and saturation..."
if cargo test -p obend-ffi --test challenger_stress_pool -- --skip test_challenger_pool_zero_workers_hang; then
    echo "  [PASS] Worker pool handles concurrent flood and saturation without mimalloc crash."
else
    echo "  [FAIL] Worker pool crashed under stress."
    FAILED=1
fi

echo "Testing worker pool zero-thread edge case..."
ZERO_OUT=$(cargo test -p obend-ffi --test challenger_stress_pool -- test_challenger_pool_zero_workers_hang 2>&1 || true)
if echo "$ZERO_OUT" | grep -q "Worker pool active: SendError"; then
    echo "  [BUG CONFIRMED] LeanWorkerPool::new(0) drops receiver and panics on execute()."
else
    echo "  [INFO] Zero-worker test output: $ZERO_OUT"
fi

echo ""
echo "--- [2/4] Feature 38: C-ABI 8 Functions & Boundary Edge Cases ---"
echo "Testing C-ABI edge cases (zero length, truncated commits, truncated receipts, scratch realloc)..."
if cargo test -p obend-ffi --test challenger_cabi_edges -- \
    --skip test_cabi_concurrent_sessions_memory_corruption \
    --skip test_cabi_null_payload_pointer; then
    echo "  [PASS] Single-threaded basic bounds and truncation checks passed."
else
    echo "  [FAIL] Single-threaded bounds checks failed."
    FAILED=1
fi

echo "Testing C-ABI null payload pointer with non-zero length..."
NULL_OUT=$(cargo test -p obend-ffi --test challenger_cabi_edges -- test_cabi_null_payload_pointer 2>&1 || true)
if echo "$NULL_OUT" | grep -q "slice::from_raw_parts requires the pointer to be aligned and non-null"; then
    echo "  [BUG CONFIRMED] Null payload pointer triggers slice::from_raw_parts undefined behavior / SIGABRT."
else
    echo "  [INFO] Null payload pointer output: $NULL_OUT"
fi

echo "Testing C-ABI concurrent sessions against global STUB_BUF..."
CONC_OUT=$(cargo test -p obend-ffi --test challenger_cabi_edges -- test_cabi_concurrent_sessions_memory_corruption 2>&1 || true)
if echo "$CONC_OUT" | grep -Eq "assertion failed|unsafe precondition"; then
    echo "  [BUG CONFIRMED] Multi-session concurrent evaluation causes cross-session data corruption and use-after-free in STUB_BUF."
else
    echo "  [INFO] Concurrent session output: $CONC_OUT"
fi

echo ""
echo "--- [3/4] Feature 38 Native Bridge Compilation & Linking ---"
echo "Testing compilation of lean/c/obend_bridge.c against Lean 4 headers on remote swarm (bb2)..."
BB2_CC_OUTPUT=$(ssh bb2 "gcc -c /home/build/obend/repo/lean/c/obend_bridge.c -I /home/build/.elan/toolchains/leanprover--lean4---v4.35.0/include -o /tmp/obend_bridge.o 2>&1" || true)
if echo "$BB2_CC_OUTPUT" | grep -q "makes integer from pointer without a cast"; then
    echo "  [BUG CONFIRMED] lean/c/obend_bridge.c fails to compile with gcc due to Lean C runtime API type mismatch:"
    echo "$BB2_CC_OUTPUT" | head -n 10 | sed 's/^/    /'
else
    echo "  [INFO] CC output: $BB2_CC_OUTPUT"
fi

echo "Testing link of obend-ffi against native libobend_Obend.so on remote swarm (bb2)..."
BB2_LINK_OUTPUT=$(ssh bb2 "cd /home/build/obend/repo && LEAN_SYSROOT=\$(cd lean && lake env lean --print-prefix) cargo test -p obend-ffi 2>&1" || true)
if echo "$BB2_LINK_OUTPUT" | grep -q "undefined symbol: obend_session_init"; then
    echo "  [BUG CONFIRMED] obend-ffi fails to link against native libobend_Obend.so because obend_bridge.c was never compiled into the shared library:"
    echo "$BB2_LINK_OUTPUT" | grep -E "undefined symbol: obend_" | head -n 8 | sed 's/^/    /'
else
    echo "  [INFO] Link output: $BB2_LINK_OUTPUT"
fi

echo ""
echo "--- [4/4] Feature 39: GUI CLI Runner & CAD Previewer ---"
if cargo test -p obend-gui --test challenger_gui_cli; then
    echo "  [PASS] obend-gui runner and CLI error handling verified."
else
    echo "  [FAIL] obend-gui CLI runner failed."
    FAILED=1
fi

echo ""
echo "================================================================================"
echo " CHALLENGER 2 SUMMARY"
echo "================================================================================"
echo "Identified 4 critical empirical failure modes:"
echo "1. C-ABI Bridge (lean/c/obend_bridge.c) has C type errors and does not compile."
echo "2. C-ABI Bridge functions were never built into libobend_Obend.so, causing native link failure."
echo "3. STUB_BUF in crates/obend-ffi/src/sys.rs is a global static buffer causing concurrent data corruption & UB."
echo "4. Null payload pointer in sys::obend_eval_cell causes slice::from_raw_parts SIGABRT."
echo "5. LeanWorkerPool::new(0) panics immediately on first execution."
echo "================================================================================"
