#!/usr/bin/env python3
"""Negative checks for the complete fixed native matrix/Lean input boundary."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("branch_check",
    Path(__file__).with_name("check-branch-d2-coordinates.py"))
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


class BranchInputs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.snapshot = json.loads((check.ROOT / check.SNAPSHOT).read_text())
        cls.slices = {key: cls.snapshot["candidate_coverage"][key] for key, _ in check.DEGREES}
        cls.lean = (check.ROOT / check.LEAN).read_text()

    def test_known_zero_is_distinct_from_index_zero_and_unknown(self):
        self.assertEqual(check.coordinates("", 4), [])
        self.assertEqual(check.coordinates("0", 4), [0])
        for value in (None, "-1", "[NULL]", "?", "01", "0,", "1,1", "3,1", "4"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                check.coordinates(value, 4)

    def test_complete_literals_match_snapshot(self):
        check.check_contract(self.slices, self.snapshot, self.lean)

    def test_unknown_d2_in_both_snapshots_still_fails(self):
        snapshot = copy.deepcopy(self.snapshot)
        snapshot["candidate_coverage"]["incoming"]["basis"][4]["d2"] = None
        slices = {key: snapshot["candidate_coverage"][key] for key, _ in check.DEGREES}
        with self.assertRaisesRegex(ValueError, "unknown, not zero"):
            check.check_contract(slices, snapshot, self.lean)

    def test_missing_native_dimension_fails(self):
        slices = copy.deepcopy(self.slices)
        slices["incoming"]["basis_dimension"] = 4
        slices["incoming"]["basis"].pop()
        with self.assertRaisesRegex(ValueError, "complete native dimensions"):
            check.check_contract(slices, self.snapshot, self.lean)

    def test_changed_lean_column_or_missing_zero_column_fails(self):
        for text in (self.lean.replace('(5721, some "2")', '(5721, some "3")'),
                     self.lean.replace(', (5604, some "")', ''),
                     self.lean.replace('(5722, some "")', '(5722, none)')):
            with self.subTest(text=text[-40:]), self.assertRaisesRegex(ValueError, "Lean native columns"):
                check.check_contract(self.slices, self.snapshot, text)

    def test_unrecognized_lean_expression_fails(self):
        text = self.lean.replace('(5604, some "")', '(5604, Option.some "")')
        with self.assertRaisesRegex(ValueError, "unsupported Lean row expression"):
            check.check_contract(self.slices, self.snapshot, text)

    def test_matrix_or_basis_identity_changes_fail(self):
        snapshot = copy.deepcopy(self.snapshot)
        snapshot["candidate_coverage"]["outgoing_matrix_rows"][2][3] = 0
        with self.assertRaisesRegex(ValueError, "snapshot matrix"):
            check.check_contract(self.slices, snapshot, self.lean)
        for text in (self.lean.replace('[5854, 5855, 5856, 5857]', '[5854, 5855, 5857, 5856]'),
                     self.lean.replace('(18, 146)', '(18, 145)')):
            with self.assertRaises(ValueError):
                check.check_contract(self.slices, self.snapshot, text)

    def test_wrong_archive_is_not_an_alternate_baseline(self):
        with tempfile.TemporaryDirectory() as tmp:
            archive = Path(tmp) / "kervaire_database.rar"
            archive.write_bytes(b"not the fixed same-version archive")
            with self.assertRaisesRegex(ValueError, "fixed archive size/checksum mismatch"):
                check.checked_archive(check.ROOT, archive)


if __name__ == "__main__":
    unittest.main()
