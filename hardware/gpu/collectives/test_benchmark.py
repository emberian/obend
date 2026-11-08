"""Small independent scalar checks of the NumPy oracle and fixture contract."""
import json
from pathlib import Path
import tempfile
import unittest

import numpy as np

import benchmark as b


class OracleTests(unittest.TestCase):
    def test_all_monoids_modes_regular_irregular_and_empty(self):
        mask = (1 << 64) - 1
        functions = {"add": lambda a, x: (a + x) & mask,
                     "mul": lambda a, x: (a * x) & mask,
                     "band": lambda a, x: a & x, "bor": lambda a, x: a | x}
        for lengths in ([3, 3], [0, 1, 0, 5, 0], [0, 0], [], [1] * 6):
            for op, fn in functions.items():
                xs = b.data(sum(lengths), op, variant=1)
                for mode in ("inclusive", "exclusive", "reduce"):
                    output, run = b.numpy_kernel(xs, lengths, op, mode)
                    run()
                    expected, offset = [], 0
                    for n in lengths:
                        acc = b.OPS[op][1]
                        for x in xs[offset:offset + n]:
                            if mode == "exclusive":
                                expected.append(acc)
                            acc = fn(acc, int(x))
                            if mode == "inclusive":
                                expected.append(acc)
                        if mode == "reduce":
                            expected.append(acc)
                        offset += n
                    self.assertEqual(output.tolist(), expected, (lengths, op, mode))
                    # Every call fully overwrites outputs, as required by the CPU timing scope.
                    output.fill(0xdeadbeef)
                    run()
                    self.assertEqual(output.tolist(), expected)

    def test_binary_fixture_preserves_bits_and_empty(self):
        with tempfile.TemporaryDirectory(prefix="obend-collectives-test-") as temp:
            directory = Path(temp)
            xs = np.array([0, 1 << 63, (1 << 64) - 1], dtype="<u8")
            manifest, files = b.fixture(directory, "bits", xs, np.array([], dtype="<u8"))
            self.assertEqual(np.fromfile(files[0], dtype="<u8").tolist(), xs.tolist())
            self.assertEqual(files[1].stat().st_size, 0)
            self.assertEqual(len(manifest["expected"]), 1)

    def test_copy_dispatch_uses_same_two_dimensional_index(self):
        with tempfile.TemporaryDirectory(prefix="obend-collectives-test-") as temp:
            directory = Path(temp)
            b.write_copy(directory, 1 << 24)
            plan = json.loads((directory / "plan.json").read_text())
            self.assertEqual(plan["words"], 1 << 25)
            self.assertEqual(plan["stages"][0]["threads"], 1 << 24)
            self.assertIn("g.y * 32768u", (directory / "stage_0.wgsl").read_text())

    def test_runner_report_requires_final_exact_check(self):
        prefix = "test: 1 vectors, 2 dispatches, 0 disagree, 1.000 ms per vector, on Adapter\n"
        suffix = "BENCH\ttest\t31\t2\tgpu_us_median=1\tgpu_us_p10=1\tgpu_us_p90=2\thost_batch_amortized_us=3\tfinal_output=exact\n"
        self.assertEqual(b.gpu_record(prefix + suffix, 31)["gpu_us_median"], 1)
        with self.assertRaises(RuntimeError):
            b.gpu_record(prefix, 31)
        with self.assertRaises(RuntimeError):
            b.gpu_record(prefix + suffix.replace("final_output=exact", "final_output=skipped"), 31)


if __name__ == "__main__":
    unittest.main()
