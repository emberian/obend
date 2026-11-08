#!/usr/bin/env python3
"""Narrow regression gate for the vault performance measurements (no Lean build needed)."""
import csv
import os
import tempfile
import unittest

import large
import walkthrough


class Coverage(unittest.TestCase):
    def row(self, commands="open", step="1", **cost):
        return dict(walkthrough="vault/WORKSHOP", step=step, line=22, commands=commands,
                    **dict(dict.fromkeys(walkthrough.MEASURES, 100), **cost))

    def test_changed_commands_cannot_disappear(self):
        self.assertIn("commands changed", walkthrough.compare([self.row("open,judge")], [self.row()])[0])

    def test_added_step_cannot_disappear(self):
        self.assertIn("missing baseline", walkthrough.compare([self.row(step="2")], [self.row()])[0])

    def test_absent_baseline_cannot_pass(self):
        self.assertIn("missing baseline", walkthrough.compare([self.row()], [])[0])

    def test_regression_checked_when_commands_match(self):
        self.assertEqual(walkthrough.compare([self.row()], [self.row()]), [])
        self.assertIn("read 100 -> 10000", walkthrough.compare([self.row(read=10000)], [self.row()])[0])


class GitBaseline(unittest.TestCase):
    def test_same_markdown_tree_and_noop(self):
        with tempfile.TemporaryDirectory(prefix="obend-cost-git-") as work:
            os.mkdir(os.path.join(work, "acct"))
            page = os.path.join(work, "acct", "P.md")
            with open(page, "w") as f:
                f.write("first\n")
            os.mkdir(os.path.join(work, ".obend"))
            with open(os.path.join(work, ".obend", "checkpoint"), "w") as f:
                f.write("not markdown\n")
            large.git_init(work)
            first = large.git_measure(work)
            self.assertEqual(first["git_changed_files"], 1)
            self.assertGreater(first["git_commit_ms"], 0)
            self.assertEqual(large.git(work, "ls-files").stdout, "acct/P.md\n")
            same = large.git_measure(work)
            self.assertEqual(same["git_changed_files"], 0)
            self.assertEqual(same["git_commit_ms"], 0)
            with open(page, "w") as f:
                f.write("second\n")
            changed = large.git_measure(work)
            self.assertEqual(changed["git_changed_files"], 1)
            self.assertEqual(large.git(work, "show", "HEAD:acct/P.md").stdout, "second\n")

    def test_every_measurement_retained_and_log_segments_counted(self):
        with tempfile.TemporaryDirectory(prefix="obend-cost-record-") as work:
            old = large.WORK
            large.WORK = work
            try:
                cost = ["cost: read 101 bytes, wrote 202 bytes, 3 ms, replayed 4 records, checkpoint 5 bytes [open]"]
                large.record_measurement(work, ("open",), 3.5, 0, cost, {})
                large.record_measurement(work, ("open",), 4.5, 1, cost, {})
                with open(os.path.join(work, "measurements.tsv")) as f:
                    rows = list(csv.DictReader(f, delimiter="\t"))
                self.assertEqual([r["exit"] for r in rows], ["0", "1"])
                self.assertEqual(rows[0]["read"], "101")
                segments = os.path.join(work, ".obend", "log-segments", "generation")
                os.makedirs(segments)
                for path, data in [(os.path.join(work, ".obend", "log"), b"manifest"),
                                   (os.path.join(segments, "0"), b"123"),
                                   (os.path.join(segments, "1"), b"4567")]:
                    with open(path, "wb") as f:
                        f.write(data)
                self.assertEqual(large.log_bytes(work), 15)
                with open(os.path.join(work, ".obend", "checkpoint"), "wb") as f:
                    f.write(b"obend-checkpoint 1 17 130 200 99 0\n{world}")
                self.assertEqual(large.records(work), (17, 200))
            finally:
                large.WORK = old


if __name__ == "__main__":
    unittest.main()
