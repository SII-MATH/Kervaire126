#!/usr/bin/env python3
"""Negative checks for native payload, witnesses, and proof-status boundaries."""
import copy
import csv
import importlib.util
import io
import json
import shutil
import sqlite3
from pathlib import Path
import tempfile
import unittest
from unittest import mock

SCRIPT = Path(__file__).with_name("native-contract.py")
SPEC = importlib.util.spec_from_file_location("native_contract", SCRIPT)
NATIVE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(NATIVE)


class NativeContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.expected = NATIVE.rebuild()
        cls.lowstem = NATIVE.load_lowstem()
        _, data, _ = cls.lowstem.pinned("S0_AdamsE2_relations.csv")
        cls.relations = list(csv.DictReader(io.StringIO(data.decode("utf-16"))))

    def test_committed_snapshot_is_reproducible(self):
        NATIVE.check_snapshot(NATIVE.DEFAULT_OUTPUT.read_text(), self.expected)

    def test_changed_coordinate_cannot_keep_the_same_native_target(self):
        changed = copy.deepcopy(self.expected)
        changed["naturality"]["target_log"]["dx"] = "1"
        with self.assertRaisesRegex(ValueError, "snapshot differs"):
            NATIVE.check_snapshot(NATIVE.rendered(changed), self.expected)

    def test_changed_source_log_transcription_is_rejected(self):
        naturality = self.expected["naturality"]
        source, target = naturality["source_candidate_log"], naturality["target_log"]
        text = (NATIVE.LIN / "Raw/Naturality.lean").read_text()
        original = NATIVE.raw_log_declaration("sourceCandidate245130", source)
        for before, after in (("name := some \"Ceta\"", "name := some \"S0\""),
                              ("info := none", "info := some \"\""),
                              ("r := some 3", "r := some (1 + 2)")):
            changed = text.replace(original, original.replace(before, after))
            with self.assertRaisesRegex(ValueError, "sourceCandidate245130 transcription differs"):
                NATIVE.check_raw_naturality_declarations(changed, source, target)

    def test_cw_source_transcription_preserves_null_and_native_reason(self):
        trace = json.loads((NATIVE.ROOT /
            "KIP126/LinProgram/Generated/Provenance/row462481-trace.json").read_text())
        rows = {row["id"]: row for row in trace["adjacent_context"]["branch_rows"]}
        cw, source, target = [rows[i] for i in (462479, 462480, 462481)]
        text = (NATIVE.LIN / "Raw/NaturalityHighStem.lean").read_text()
        NATIVE.check_raw_high_stem_declarations(text, cw, source, target)
        original = NATIVE.raw_log_declaration("source462479Full", cw)
        for before, after in (("reason := some \"D\"", "reason := some \"N\""),
                              ("info := none", "info := some \"\""),
                              ("x := some \"1\"", "x := some \"\""),
                              ("t := some 144", "t := some 140")):
            changed = text.replace(original, original.replace(before, after))
            with self.subTest(before=before), self.assertRaisesRegex(
                    ValueError, "source462479Full transcription differs"):
                NATIVE.check_raw_high_stem_declarations(changed, cw, source, target)

    def test_changed_polynomial_fails_witness_identity(self):
        witness = copy.deepcopy(self.expected["algebra"]["product_witnesses"][1])
        witness["output"][0][0][1] += 1
        with self.assertRaisesRegex(ValueError, "polynomial witness identity failed"):
            NATIVE.validate_product_witness(witness, self.relations, self.lowstem)

    def test_changed_native_map_metadata_fails_pinned_hash(self):
        config = NATIVE.pinned_map_catalogue(self.lowstem)
        mapping = next(m for m in config["maps"] if m["name"] == "Ceta__S0")
        # Still covers the same degrees, so the semantic shift check alone
        # would accept this change. The input hash must reject it first.
        mapping["t_max"] += 1
        with tempfile.TemporaryDirectory(prefix="lin-map-mutation-") as temporary:
            raw = Path(temporary)
            (raw / "manifest.json").write_bytes((self.lowstem.RAW / "manifest.json").read_bytes())
            (raw / "ss.json").write_text(json.dumps(config))
            with mock.patch.object(self.lowstem, "RAW", raw):
                with self.assertRaisesRegex(ValueError, "pinned input mismatch: ss.json"):
                    NATIVE.pinned_map_catalogue(self.lowstem)

    def test_changed_suspension_fails_native_degree_contract(self):
        naturality = self.expected["naturality"]
        mapping = {**naturality["native_map"], "sus": 1}
        with self.assertRaisesRegex(ValueError, "map suspension"):
            NATIVE.validate_naturality(naturality["source_candidate_log"], naturality["target_log"], mapping)

    def test_naturality_output_can_be_next_naturality_source(self):
        extra = self.expected["additional_missing_trace"]
        source, target = extra["source_candidate_log"], extra["target_log"]
        mapping = self.expected["naturality"]["native_map"]
        self.assertEqual(source["reason"], "N")
        NATIVE.validate_naturality(source, target, mapping)
        for changed in ({**source, "reason": "T"}, {**source, "depth": 1}):
            with self.assertRaisesRegex(ValueError, "unsupported source"):
                NATIVE.validate_naturality(changed, target, mapping)
        self.assertFalse(extra["actual_row_certified"])

    def test_recovered_trace_keeps_exact_source_and_unproved_obligations(self):
        extra = self.expected["additional_missing_trace"]
        source, target = extra["source_candidate_log"], extra["target_log"]
        trace = json.loads((NATIVE.ROOT / extra["native_trace"]["path"]).read_text())
        mapping = self.expected["naturality"]["native_map"]
        NATIVE.validate_recovered_trace(trace, source, target, mapping)
        changed = copy.deepcopy(trace)
        for row in changed["adjacent_context"]["branch_rows"]:
            if row["id"] == source["id"]:
                row["reason"] = "D"
        with self.assertRaisesRegex(ValueError, "trace source differs"):
            NATIVE.validate_recovered_trace(changed, source, target, mapping)
        changed = {**trace, "remaining_propositions": []}
        with self.assertRaisesRegex(ValueError, "erased actual-model obligations"):
            NATIVE.validate_recovered_trace(changed, source, target, mapping)

    def test_nonempty_incomplete_trace_premises_cannot_be_rebaselined(self):
        extra = self.expected["additional_missing_trace"]
        expected_bytes = (NATIVE.ROOT / extra["native_trace"]["path"]).read_bytes()
        trace = json.loads(expected_bytes)
        for remaining in (["placeholder"], [trace["remaining_propositions"][4]]):
            changed = {**trace, "remaining_propositions": remaining}
            changed_bytes = (json.dumps(changed, ensure_ascii=False, indent=2) + "\n").encode()
            with self.subTest(remaining=remaining), self.assertRaisesRegex(
                    ValueError, "fixed-input reconstruction"):
                NATIVE.check_recovered_trace_snapshot(changed_bytes, expected_bytes)

    def test_missing_trace_and_obligations_cannot_be_erased(self):
        swapped_targets = list(reversed(self.expected["algebra"]["fixed_quotient_statement_declarations"]))
        for section, key, value in (("naturality", "remaining_premises", []),
                                    ("algebra", "actual_row_certified", True),
                                    ("algebra", "fixed_quotient_statement_declarations", swapped_targets)):
            changed = copy.deepcopy(self.expected)
            changed[section][key] = value
            with self.assertRaisesRegex(ValueError, "snapshot differs"):
                NATIVE.check_snapshot(NATIVE.rendered(changed), self.expected)
        self.assertTrue(self.expected["naturality"]["remaining_premises"])
        self.assertTrue(self.expected["naturality"]["missing_trace"])
        self.assertFalse(self.expected["contract"]["actual_certification"])
        self.assertEqual(self.expected["contract"]["generated_proof_status"], "unverified")

    def check_map_slice(self, ceta_path, map_path):
        naturality = self.expected["naturality"]
        sphere_path, _, _ = self.lowstem.pinned("S0_AdamsSS_t261.db")
        with NATIVE.connect(ceta_path) as ceta, NATIVE.connect(map_path) as maps, NATIVE.connect(sphere_path) as sphere:
            return NATIVE.native_ceta_map_slice(
                ceta, maps, sphere, naturality["source_candidate_log"], naturality["target_log"],
                naturality["native_map"], self.lowstem)

    def test_recovered_map_slice_preserves_native_module_coordinates(self):
        data = self.expected["naturality"]["native_data_map"]
        self.assertEqual(data["generator_images"], [{"id": 1, "map": "0,1"}])
        for side, source_id, monomial in (("source", 69, "7,1,1"), ("target", 80, "8,1,1")):
            degree_slice = data["degree_slices"][side]
            self.assertEqual(degree_slice["source_basis"][0]["id"], source_id)
            self.assertEqual(degree_slice["source_basis"][0]["mon"], monomial)
            self.assertEqual(degree_slice["matrix_rows"], [[1]])
            self.assertEqual(degree_slice["mapped_coordinates"], [0])
        self.assertEqual(data["proof_status"], "unverified-data-extraction")
        self.assertFalse(self.expected["contract"]["actual_certification"])

    def test_changed_database_map_is_rejected_by_hash_and_coordinates(self):
        ceta_path, _, _ = self.lowstem.pinned("Ceta_AdamsSS_t200.db")
        map_name = "map_AdamsSS_Ceta_to_S0_t200.db"
        map_path, _, _ = self.lowstem.pinned(map_name)
        with tempfile.TemporaryDirectory(prefix="lin-native-db-mutation-") as temporary:
            raw = Path(temporary)
            changed = raw / map_name
            shutil.copyfile(map_path, changed)
            with sqlite3.connect(changed) as db:
                db.execute("UPDATE map_AdamsE2_Ceta_to_S0 SET map='' WHERE id=1")
            (raw / "manifest.json").write_bytes((self.lowstem.RAW / "manifest.json").read_bytes())
            with mock.patch.object(self.lowstem, "RAW", raw):
                with self.assertRaisesRegex(ValueError, "pinned input mismatch"):
                    self.lowstem.pinned(map_name)
            with self.assertRaisesRegex(ValueError, "native map coordinates disagree"):
                self.check_map_slice(ceta_path, changed)

    def test_changed_source_basis_or_map_schema_is_rejected(self):
        ceta_path, _, _ = self.lowstem.pinned("Ceta_AdamsSS_t200.db")
        map_path, _, _ = self.lowstem.pinned("map_AdamsSS_Ceta_to_S0_t200.db")
        with tempfile.TemporaryDirectory(prefix="lin-native-schema-mutation-") as temporary:
            changed_source, changed_map = Path(temporary) / "source.db", Path(temporary) / "map.db"
            shutil.copyfile(ceta_path, changed_source)
            with sqlite3.connect(changed_source) as db:
                db.execute("UPDATE Ceta_AdamsE2_basis SET mon='8,1,1' WHERE id=69")
            with self.assertRaisesRegex(ValueError, "source module monomial degree mismatch"):
                self.check_map_slice(changed_source, map_path)
            shutil.copyfile(map_path, changed_map)
            with sqlite3.connect(changed_map) as db:
                db.execute("ALTER TABLE map_AdamsE2_Ceta_to_S0 ADD COLUMN unrecognized TEXT")
            with self.assertRaisesRegex(ValueError, "native table schema changed"):
                self.check_map_slice(ceta_path, changed_map)

    def test_archive_member_cannot_change_with_same_source_version(self):
        manifest = json.loads((self.lowstem.RAW / "manifest.json").read_text())
        entry = next(f for f in manifest["files"] if f["path"] == "Ceta_AdamsSS_t200.db")
        entry["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "canonical source artifact"):
            NATIVE.validate_ceta_archive_origin(manifest)
        entry["extracted_from"]["member"] = "other-version/Ceta_AdamsSS_t200.db"
        with self.assertRaisesRegex(ValueError, "fixed archive member"):
            NATIVE.validate_ceta_archive_origin(manifest)

    def test_unknown_and_zero_encodings_remain_distinct(self):
        self.assertEqual(NATIVE.coordinates(""), [])
        for text in (None, "-1", "[NULL]", "1,1", "2,1"):
            with self.assertRaises(ValueError):
                NATIVE.coordinates(text)
        self.assertIsNone(self.expected["naturality"]["source_candidate_log"]["info"])
        self.assertEqual(self.expected["algebra"]["target_log"]["dx"], "")


if __name__ == "__main__":
    unittest.main()
