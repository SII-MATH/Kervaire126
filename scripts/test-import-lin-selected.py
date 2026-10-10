#!/usr/bin/env python3
"""Fail-closed regression checks for the result importer (standard library only)."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "importer", Path(__file__).resolve().parents[1] /
    "KIP126/LinProgram/Translate/import-selected.py")
importer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(importer)


class ImportBoundaryTests(unittest.TestCase):
    def test_route_raw_override_still_requires_pinned_input(self):
        selector = Path(importer.__file__).with_name("select-route.py")
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "proofs.db").write_bytes(b"not the pinned database")
            result = subprocess.run(
                [sys.executable, "-B", str(selector), "--check", "--raw-dir", tmp],
                capture_output=True, text=True, check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("hash mismatch: proofs.db", result.stderr)

    def test_null_empty_and_index_zero_are_distinct(self):
        self.assertEqual(importer.indices(""), [])
        self.assertEqual(importer.indices("0"), [0])
        for text in (None, "[NULL]", "?", "-1", "1,1", "2,1", "0,", "1;2"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                importer.indices(text)

    def test_unknown_trial_inverse_and_other_spectra_are_rejected(self):
        row = dict(name="S0", depth=0, reason="D", r=3, s=6, t=132,
                   stem=126, x="0", dx="3")
        importer.accepted_log(row)
        for change in (dict(dx=None), dict(dx=""), dict(x=""), dict(depth=1),
                       dict(reason="T"), dict(reason="TI"), dict(reason="DI"),
                       dict(reason=None), dict(name="Cnu"), dict(r=999),
                       dict(r=1), dict(stem=125)):
            # r=999 is a sentinel, even though its target string may be nonempty.
            with self.subTest(change=change), self.assertRaises(ValueError):
                importer.accepted_log({**row, **change})

    def test_bad_hash_is_not_accepted_as_a_new_version(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "proofs.db"
            path.write_bytes(b"not the pinned database")
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                importer.pinned(path)

    def test_monomials_fail_closed(self):
        gens = {0: {}, 1: {}}
        self.assertEqual(importer.monomial("0,2,1,1", gens), [(0, 2), (1, 1)])
        for text in ("0", "0,0", "2,1", "1,1,0,1", "0,1,0,2", "-1,2"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                importer.monomial(text, gens)

    def test_bulk_join_rejects_missing_and_mismatched_rows(self):
        entry = dict(name="example", origin="proofs.db/log", paper="fixture",
            record=dict(id=7, reason="D", s=1, t=64, r=2, x="0", dx="0"),
            source_degree=[1, 64], target_degree=[3, 65])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            directory = root / "KIP126/LinProgram/Generated/Differentials"
            directory.mkdir(parents=True)
            with self.assertRaisesRegex(ValueError, "absent"):
                importer.generate({}, [dict(entry)], root)
            shard = directory / "Shard000.lean"
            shard.write_text('⟨7, "D", 1, 64, 2, [0], [1]⟩')
            with self.assertRaisesRegex(ValueError, "disagrees"):
                importer.generate({}, [dict(entry)], root)
            shard.write_text('⟨7, "D", 1, 64, 2, [0], [0]⟩')
            output = importer.generate({}, [dict(entry)], root)
            self.assertIn("differential_of_lookup 0 0", output["Proofs.lean"])
            self.assertNotIn("axiom example", output["Proofs.lean"])


if __name__ == "__main__":
    unittest.main()
