#!/usr/bin/env python3
"""Unified E2E Test Suite Runner for 'The Next Mathematica in Obend'.

Runs Tiers 1-4 covering all 39 features, produces execution summaries,
and exports results adhering to PROJECT.md and TEST_INFRA.md.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from common import REGISTRY, TestStatus
from tier1_features.test_tier1 import run_all_tier1
from tier2_boundaries.test_tier2 import run_all_tier2
from tier3_pairwise import test_tier3
from tier4_workloads import test_tier4


def main() -> int:
    parser = argparse.ArgumentParser(description="Obend E2E Test Suite Runner")
    parser.add_argument("--tier", type=int, choices=[1, 2, 3, 4], help="Run only specific tier")
    parser.add_argument("--json-out", type=str, help="Export results to JSON file")
    parser.add_argument("--verbose", action="store_true", help="Print detailed test case output")
    args = parser.parse_args()

    print("=" * 80)
    print(" OBEND E2E TEST SUITE RUNNER — The Next Mathematica in Obend")
    print(" 39 Features across Tiers 1–4 (Minimum Threshold: 449 Tests)")
    print("=" * 80)

    start_time = time.perf_counter()

    tiers_to_run = [args.tier] if args.tier else [1, 2, 3, 4]

    for t in tiers_to_run:
        print(f"\n[RUNNING TIER {t}] ...")
        t_start = time.perf_counter()
        if t == 1:
            run_all_tier1()
        elif t == 2:
            run_all_tier2()
        elif t == 3:
            test_tier3.run_all_tier3()
        elif t == 4:
            test_tier4.run_all_tier4()
        t_elapsed = (time.perf_counter() - t_start) * 1000.0
        print(f"[TIER {t} COMPLETE] Elapsed: {t_elapsed:.2f} ms")

    total_time = (time.perf_counter() - start_time) * 1000.0
    summary = REGISTRY.summary()

    print("\n" + "=" * 80)
    print(" EXECUTION RESULTS SUMMARY")
    print("=" * 80)
    print(f" Total Tests Run    : {summary['total']}")
    print(f" Tests Passed       : {summary['passed']}")
    print(f" Tests Failed       : {summary['failed']}")
    print(f" Tests Skipped      : {summary['skipped']}")
    print(f" Overall Pass Rate  : {summary['pass_rate']:.2f}%")
    print(f" Total Elapsed Time : {total_time:.2f} ms")
    print("-" * 80)
    print(" Tier Breakdown:")
    for tier, stats in sorted(summary["tier_counts"].items()):
        print(f"   Tier {tier}: {stats['passed']}/{stats['total']} passed (failed: {stats['failed']})")
    print("-" * 80)
    print(" Feature Coverage (Tiers 1-4):")
    features_covered = len([f for f, count in summary["feature_counts"].items() if count > 0])
    print(f"   Active Feature IDs Covered: {features_covered}")
    print("=" * 80)

    if summary["failed"] > 0:
        print("\nFAILURES:")
        for r in REGISTRY.results:
            if r.status == TestStatus.FAILED:
                print(f"  FAILED [{r.test_id}] ({r.feature_id}): {r.name}")
                if r.error_message:
                    print(f"    Error: {r.error_message}")

    if args.json_out:
        with open(args.json_out, "w") as f:
            json.dump(summary, f, indent=2)
        print(f"\nWrote summary JSON to {args.json_out}")

    return 0 if summary["failed"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
