#!/usr/bin/env python3
"""Focused regression tests for :mod:`check_source_inventory`."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_source_inventory import (  # noqa: E402
    HASH_CHUNK_SIZE,
    InventoryValidator,
    _sha256_file,
    validate_inventory,
)


ROOT = SCRIPT_DIR.parent
INVENTORY = ROOT / "docs/external-inputs.json"


class SourceInventoryTests(unittest.TestCase):
    def read_inventory(self) -> dict:
        return json.loads(INVENTORY.read_text(encoding="utf-8"))

    def validate_document(self, document: dict) -> list[str]:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "inventory.json"
            path.write_text(json.dumps(document), encoding="utf-8")
            return validate_inventory(ROOT, path)

    def test_checked_in_inventory_metadata_is_valid(self) -> None:
        self.assertEqual(validate_inventory(ROOT), [])

    def test_duplicate_id_is_rejected(self) -> None:
        document = self.read_inventory()
        document["sources"][1]["id"] = document["sources"][0]["id"]
        errors = self.validate_document(document)
        self.assertTrue(any("duplicate source id" in error for error in errors))

    def test_status_bib_key_must_be_declared(self) -> None:
        document = self.read_inventory()
        browder = next(source for source in document["sources"] if source["id"] == "browder")
        browder["citation_keys"] = ["NotBrowder"]
        errors = self.validate_document(document)
        self.assertTrue(any("bib_key" in error and "absent" in error for error in errors))

    def test_status_acquisition_fields_have_a_grammar(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            status_path = root / "source-status.json"
            status_path.write_text(
                json.dumps({"bib_key": "Browder", "open_pdf": {}, "plain_text": "extracted "}),
                encoding="utf-8",
            )
            validator = InventoryValidator(root, root / "unused.json")
            validator._check_status_file(
                status_path,
                {"doi": None},
                "sources[0]",
                ["Browder"],
            )
            errors = validator.errors
        self.assertTrue(any("open_pdf" in error and "status string" in error for error in errors))
        self.assertTrue(any("plain_text" in error and "unknown status" in error for error in errors))

    def test_artifact_path_and_hash_are_checked(self) -> None:
        document = self.read_inventory()
        browder = next(source for source in document["sources"] if source["id"] == "browder")
        artifact = next(item for item in browder["artifacts"] if item["kind"] == "pdf")
        artifact["path"] = "../outside.pdf"
        errors = self.validate_document(document)
        self.assertTrue(any("relative path" in error for error in errors))

        document = self.read_inventory()
        browder = next(source for source in document["sources"] if source["id"] == "browder")
        artifact = next(item for item in browder["artifacts"] if item["kind"] == "pdf")
        artifact["path"] = "Source/Browder/\x00paper.pdf"
        errors = self.validate_document(document)
        self.assertTrue(any("control characters" in error for error in errors))

        document = self.read_inventory()
        browder = next(source for source in document["sources"] if source["id"] == "browder")
        artifact = next(item for item in browder["artifacts"] if item["kind"] == "pdf")
        artifact["path"] = "Source/Browder"
        errors = self.validate_document(document)
        self.assertTrue(any("inside source directory" in error for error in errors))

        document = self.read_inventory()
        browder = next(source for source in document["sources"] if source["id"] == "browder")
        artifact = next(item for item in browder["artifacts"] if item["kind"] == "pdf")
        artifact["sha256"] = "0" * 64
        errors = self.validate_document(document)
        self.assertTrue(any("hash mismatch" in error for error in errors))

        document = self.read_inventory()
        browder = next(source for source in document["sources"] if source["id"] == "browder")
        artifact = next(item for item in browder["artifacts"] if item["kind"] == "pdf")
        artifact["path"] = "Source/Browder/\ud800.pdf"
        errors = self.validate_document(document)
        self.assertTrue(any("cannot resolve path" in error for error in errors))

        document = self.read_inventory()
        browder = next(source for source in document["sources"] if source["id"] == "browder")
        artifact = next(item for item in browder["artifacts"] if item["kind"] == "pdf")
        artifact["kind"] = "citation"
        errors = self.validate_document(document)
        self.assertTrue(any("requires kind" in error for error in errors))

    def test_sha256_helper_reads_large_files_incrementally(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "large.bin"
            payload = b"KIP126" * (HASH_CHUNK_SIZE // 6 + 17)
            path.write_bytes(payload)
            self.assertEqual(_sha256_file(path), hashlib.sha256(payload).hexdigest())

    def test_artifact_symlink_cannot_escape_source_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_directory = root / "source"
            other_directory = root / "other"
            source_directory.mkdir()
            other_directory.mkdir()
            (other_directory / "file.txt").write_text("outside", encoding="utf-8")
            (source_directory / "link.txt").symlink_to("../other/file.txt")
            validator = InventoryValidator(root, root / "unused.json")
            validator._check_artifacts(
                {
                    "directory": "source",
                    "artifacts": [
                        {
                            "path": "source/link.txt",
                            "kind": "text",
                            "required": True,
                            "sha256": "0" * 64,
                        }
                    ],
                },
                "sources[0]",
                True,
                None,
            )
            errors = validator.errors
        self.assertTrue(any("resolves outside source directory" in error for error in errors))

    def test_artifact_symlink_loop_returns_diagnostic(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_directory = root / "source"
            source_directory.mkdir()
            (source_directory / "loop.txt").symlink_to("loop.txt")
            validator = InventoryValidator(root, root / "unused.json")
            path = validator._safe_path("source/loop.txt", "sources[0].artifacts[0].path")
            errors = validator.errors
        self.assertIsNone(path)
        self.assertTrue(any("cannot resolve path" in error for error in errors))

    def test_source_of_record_artifacts_are_required(self) -> None:
        document = self.read_inventory()
        aim = next(source for source in document["sources"] if source["id"] == "aim_paper")
        artifact = next(item for item in aim["artifacts"] if item["path"] == "MainPaper/main.tex")
        artifact["required"] = False
        errors = self.validate_document(document)
        self.assertTrue(any("source-of-record artifact" in error and "required=true" in error for error in errors))

    def test_malformed_source_fields_return_diagnostics(self) -> None:
        document = self.read_inventory()
        browder = next(source for source in document["sources"] if source["id"] == "browder")
        browder["citation_keys"] = 42
        errors = self.validate_document(document)
        self.assertTrue(any("citation_keys" in error and "array" in error for error in errors))

    def test_non_object_status_file_returns_diagnostics(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / "source"
            directory.mkdir()
            (directory / "source-status.json").write_text("[]", encoding="utf-8")
            validator = InventoryValidator(root, root / "unused.json")
            validator._check_availability(
                {
                    "status_class": "partial",
                    "status_file": "source/source-status.json",
                    "availability": {
                        "metadata": False,
                        "pdf": False,
                        "text": False,
                        "source": False,
                    },
                },
                "sources[0]",
                "browder",
                "source",
            )
            errors = validator.errors
        self.assertTrue(any("status file must contain an object" in error for error in errors))

    def test_schema_version_requires_json_integer(self) -> None:
        for invalid_version in (True, 1.0):
            document = self.read_inventory()
            document["schema_version"] = invalid_version
            errors = self.validate_document(document)
            self.assertTrue(any("schema_version" in error for error in errors))

    def test_bibtex_comment_is_not_a_citation_entry(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            citation = root / "citation.bib"
            citation.write_text("% @article{Fake,\n", encoding="utf-8")
            validator = InventoryValidator(root, root / "unused.json")
            validator._check_citation_file(citation, "sources[0]", ["Fake"])
            errors = validator.errors
        self.assertTrue(any("citation key 'Fake'" in error for error in errors))

    def test_invalid_utf8_inventory_returns_diagnostics(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "inventory.json"
            path.write_bytes(b"\xff\xfe")
            errors = validate_inventory(ROOT, path)
        self.assertTrue(any("cannot decode file" in error for error in errors))

    def test_oversized_json_integer_returns_diagnostics(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "inventory.json"
            path.write_text('{"schema_version": ' + "9" * 5000 + "}", encoding="utf-8")
            errors = validate_inventory(ROOT, path)
        self.assertTrue(any("invalid JSON value" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
