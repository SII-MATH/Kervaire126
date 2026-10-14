#!/usr/bin/env python3
"""Regression checks for refusal of unsupported or uncertified row proofs."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("replay-lowstem.py")

class ReplayTests(unittest.TestCase):
    def run_case(self, root, row, certificate_only=False):
        output = Path(root) / str(row)
        args = [sys.executable, str(SCRIPT), "--row", str(row),
                "--output-dir", str(output)]
        if certificate_only:
            args.append("--certificate-only")
        return subprocess.run(args, capture_output=True, text=True), output

    def test_supported_algebra_and_missing_math_are_distinct(self):
        with tempfile.TemporaryDirectory() as root:
            result, output = self.run_case(root, 152098)
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertIn("actual DifferentialStatement not generated", result.stderr)
            report = json.loads((output / "benchmark.json").read_text())
            self.assertFalse(report["actual_row_proof_generated"])
            self.assertTrue(report["unresolved"])
            self.assertEqual([len(c["trace"]) for c in report["certificates"]], [1, 3])
            lean = (output / "GeneratedProductWitnesses.lean").read_text()
            self.assertNotIn("DifferentialStatement", lean)
            self.assertNotIn("sorry", lean)
            self.assertNotIn("axiom ", lean)

    def test_second_record_uses_same_generator(self):
        with tempfile.TemporaryDirectory() as root:
            result, output = self.run_case(root, 152095, certificate_only=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads((output / "benchmark.json").read_text())
            self.assertEqual(report["target"]["id"], 152095)
            self.assertFalse(report["actual_row_proof_generated"])
            self.assertIn("namespace Replay152095", (output / "GeneratedProductWitnesses.lean").read_text())

    def test_seed_and_trial_do_not_become_proved_conclusions(self):
        with tempfile.TemporaryDirectory() as root:
            for row in [5487, 152097, 999999999]:
                result, output = self.run_case(root, row, certificate_only=True)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("REFUSED", result.stderr)
                self.assertFalse((output / "GeneratedProductWitnesses.lean").exists())

if __name__ == "__main__":
    unittest.main()
