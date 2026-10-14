#!/usr/bin/env python3
"""Check actual-object generation and rejection at the uncertified boundary."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("replay-certified.py")


class CertifiedReplayTests(unittest.TestCase):
    def run_case(self, root, row):
        output = Path(root) / str(row)
        result = subprocess.run([sys.executable, str(SCRIPT), "--row", str(row),
                                 "--output-dir", str(output)], capture_output=True, text=True)
        return result, output

    def test_actual_statements_keep_their_inputs_and_proof_status(self):
        with tempfile.TemporaryDirectory() as root:
            for row in [5432, 5434]:
                result, output = self.run_case(root, row)
                self.assertEqual(result.returncode, 0, result.stderr)
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["row"]["id"], row)
                self.assertFalse(report["lean_checked"])
                self.assertFalse(report["db_derivation_replayed"])
                lean = (output / "GeneratedReplay.lean").read_text()
                self.assertIn("KIP126.Challenge2.DifferentialStatement P rawRow", lean)
                self.assertIn("LiteratureInterface", lean)
                self.assertIn("LinE2Presentation", lean)
                self.assertNotIn("by sorry", lean)
                self.assertNotIn("axiom ", lean)

    def test_uncertified_seed_and_derivation_are_refused(self):
        with tempfile.TemporaryDirectory() as root:
            for row in [5487, 152097, 152098, 999999999]:
                result, output = self.run_case(root, row)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("REFUSED", result.stderr)
                self.assertFalse((output / "GeneratedReplay.lean").exists())


if __name__ == "__main__":
    unittest.main()
