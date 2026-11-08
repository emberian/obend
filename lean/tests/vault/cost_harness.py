#!/usr/bin/env python3
"""Narrow regression gate for the vault performance measurements (no Lean build needed)."""
import csv
import copy
import io
import json
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch
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


class Samples(unittest.TestCase):
    def row(self, **values):
        return dict(dict(walkthrough="vault/SAMPLE", step=1, line=1, commands="open",
                         read=1, wrote=2, ms=100, replayed=3, checkpoint=4), **values)

    def test_median_time_and_worst_other_metrics_without_mutation(self):
        samples = [[self.row(ms=100, read=9000)], [self.row(ms=900, wrote=9000)],
                   [self.row(ms=200, replayed=9000, checkpoint=9000)]]
        original = copy.deepcopy(samples)
        aggregate = walkthrough.aggregate_costs(samples)
        self.assertEqual(aggregate, [self.row(ms=200, read=9000, wrote=9000,
                                            replayed=9000, checkpoint=9000)])
        self.assertEqual(samples, original)
        base = self.row(step="1")
        failures = walkthrough.compare(aggregate, [base])
        self.assertEqual(len(failures), 4)
        self.assertFalse(any(": ms " in failure for failure in failures))

    def test_every_identity_and_coverage_difference_rejected(self):
        rows = [self.row(), self.row(step=2, line=5)]
        variants = [rows[:1], rows + [self.row(step=3)], rows[::-1],
                    [self.row(commands="judge"), rows[1]],
                    [self.row(walkthrough="vault/OTHER"), rows[1]],
                    [self.row(line=2), rows[1]], [rows[0], rows[0]]]
        for changed in variants:
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                walkthrough.aggregate_costs([rows, changed, rows])

    def test_sample_count_and_single_sample(self):
        for invalid in ["0", "2", "-1", "4", "3.0", "bad", None]:
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                walkthrough.cost_sample_count(invalid)
        for valid in ["1", "3", "5"]:
            self.assertEqual(walkthrough.cost_sample_count(valid), int(valid))
        self.assertEqual(walkthrough.aggregate_costs([[self.row()]]), [self.row()])
        with self.assertRaises(ValueError):
            walkthrough.aggregate_costs([])


class SampleRunner(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="obend-cost-samples-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.doc = self.root / "SAMPLE.md"
        self.doc.write_text("```sh\ntest ! -e marker || exit 3\ntouch marker\nobend sample\n```\n\n"
                            "```text\nsame\n```\n")
        self.cost = self.root / "COST.tsv"
        self.baseline = self.root / "BASELINE.tsv"
        self.name = os.path.splitext(os.path.relpath(self.doc, os.path.dirname(walkthrough.HERE)))[0]
        self.patch = patch.multiple(walkthrough, BIN=str(self.bin), COST=str(self.cost),
                                    BASELINE=str(self.baseline))
        self.patch.start()
        self.addCleanup(self.patch.stop)
        self.fake_binary()

    def fake_binary(self, bad_output=0, bad_coverage=0):
        binary = self.bin / "obend"
        binary.write_text("#!/usr/bin/env python3\n"
                          "import os\nfrom pathlib import Path\n"
                          "parent = Path.cwd().parent.name\n"
                          "sample = int(parent.split('-')[1]) if parent.startswith('sample-') else 1\n"
                          "ms = [100, 999, 200][sample - 1]\n"
                          "read = [1, 7, 3][sample - 1]\n"
                          f"command = 'different' if sample == {bad_coverage} else 'open'\n"
                          "with open(os.environ['OBEND_COST'], 'a') as log:\n"
                          "    log.write(f'cost: read {read} bytes, wrote 2 bytes, {ms} ms, "
                          "replayed 3 records, checkpoint 4 bytes [{command}]\\n')\n"
                          f"print('wrong' if sample == {bad_output} else 'same')\n")
        binary.chmod(0o755)

    def invoke(self, work, *options):
        output = io.StringIO()
        argv = ["walkthrough.py", "--doc", str(self.doc), "--work", str(work), *options]
        with patch("sys.argv", argv), redirect_stdout(output):
            try:
                walkthrough.main()
            except SystemExit as error:
                return error.code, output.getvalue()
        return 0, output.getvalue()

    def assert_evidence(self, work):
        for number in range(1, 4):
            sample = work / f"sample-{number:03d}"
            self.assertTrue((sample / "fixture" / "marker").exists())
            for filename in ["output.log", "cost-raw.log", "COST.tsv", "steps.jsonl"]:
                self.assertTrue((sample / filename).exists(), filename)
            steps = [json.loads(line) for line in (sample / "steps.jsonl").read_text().splitlines()]
            self.assertEqual(len(steps), 1)
            self.assertEqual(steps[0]["exit"], 0)

    def test_three_fresh_fixtures_record_aggregate_and_compare_once(self):
        work = self.root / "record"
        code, output = self.invoke(work, "--cost-samples", "3", "--cost-baseline")
        self.assertEqual(code, 0, output)
        self.assertIn("median ms and maximum other metrics", output)
        self.assert_evidence(work)
        rows = walkthrough.read_tsv(str(self.baseline))
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["ms"], "200")
        self.assertEqual(rows[0]["read"], "7")
        self.assertEqual(walkthrough.read_tsv(str(work / "aggregate.tsv")), rows)
        with patch.object(walkthrough, "compare", wraps=walkthrough.compare) as comparison:
            code, output = self.invoke(self.root / "compare", "--cost-samples", "3")
        self.assertEqual(code, 0, output)
        comparison.assert_called_once()
        self.assertEqual(comparison.call_args.args[0][0]["ms"], 200)

    def test_one_failed_sample_blocks_baseline_and_all_samples_run(self):
        self.fake_binary(bad_output=2)
        self.baseline.write_text("unchanged baseline\n")
        work = self.root / "failed"
        code, output = self.invoke(work, "--cost-samples", "3", "--cost-baseline")
        self.assertEqual(code, 1, output)
        self.assertIn("output differs", output)
        self.assertEqual(self.baseline.read_text(), "unchanged baseline\n")
        self.assert_evidence(work)

    def test_changed_cost_commands_refuse_aggregation_and_baseline(self):
        self.fake_binary(bad_coverage=2)
        self.baseline.write_text("unchanged baseline\n")
        work = self.root / "coverage"
        code, output = self.invoke(work, "--cost-samples", "3", "--cost-baseline")
        self.assertEqual(code, 1, output)
        self.assertIn("aggregation refused", output)
        self.assertEqual(self.baseline.read_text(), "unchanged baseline\n")
        self.assertFalse((work / "aggregate.tsv").exists())
        self.assertFalse(self.cost.exists())
        self.assert_evidence(work)

    def test_record_rejected_before_work_or_document_mutation(self):
        original = self.doc.read_text()
        work = self.root / "record-refused"
        code, _ = self.invoke(work, "--cost-samples", "3", "--record")
        self.assertIn("--record cannot", code)
        self.assertFalse(work.exists())
        self.assertEqual(self.doc.read_text(), original)

    def test_default_one_sample_keeps_original_fixture_layout(self):
        work = self.root / "single"
        code, output = self.invoke(work, "--cost-baseline")
        self.assertEqual(code, 0, output)
        self.assertTrue((work / "marker").exists())
        self.assertFalse((work / "sample-001").exists())
        self.assertNotIn("sampling", output)
        self.assertEqual(walkthrough.read_tsv(str(self.baseline))[0]["ms"], "100")


class GitBaseline(unittest.TestCase):
    def test_tightening_preserves_body_and_already_valid_balance(self):
        text = "---\nbalance: 100\n---\n# Account\nbalance: 100\nCandidate A → Candidate B\n"
        self.assertEqual(large.clamp_balance(text, 95), text.replace("balance: 100", "balance: 95", 1))
        self.assertEqual(large.clamp_balance(text, 100), text)

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
