#!/usr/bin/env python3
"""Focused regression tests for :mod:`check_source_inventory`."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

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

    def test_registered_lin_configuration_retains_source_and_hash_boundary(self) -> None:
        document = self.read_inventory()
        machine = next(s for s in document["sources"] if s["id"] == "lwx_machine")
        artifact = next(a for a in machine["artifacts"] if a["path"] == "KIP126/LinProgram/Raw/ss.json")
        artifact["sha256"] = "0" * 64
        errors = self.validate_document(document)
        self.assertTrue(any("ss.json" in error and "hash mismatch" in error for error in errors))

        machine["artifacts"].remove(artifact)
        browder = next(s for s in document["sources"] if s["id"] == "browder")
        browder["artifacts"].append(artifact)
        errors = self.validate_document(document)
        self.assertTrue(any("inside source directory" in error for error in errors))

    def test_lin_configuration_exception_rejects_other_raw_paths(self) -> None:
        document = self.read_inventory()
        machine = next(s for s in document["sources"] if s["id"] == "lwx_machine")
        artifact = next(a for a in machine["artifacts"] if a["path"] == "KIP126/LinProgram/Raw/ss.json")
        artifact["path"] = "KIP126/LinProgram/Raw/other.json"
        artifact["required"] = False
        errors = self.validate_document(document)
        self.assertTrue(any("inside source directory" in error for error in errors))

    def test_lin_configuration_symlink_cannot_escape_raw_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            raw = root / "KIP126/LinProgram/Raw"
            raw.mkdir(parents=True)
            outside = root / "outside.json"
            outside.write_text("{}", encoding="utf-8")
            (raw / "ss.json").symlink_to(outside)
            validator = InventoryValidator(root, root / "unused.json")
            validator._check_artifacts(
                {"id": "lwx_machine", "directory": "Source/LWXMachine", "artifacts": [{
                    "path": "KIP126/LinProgram/Raw/ss.json", "kind": "machine_artifact",
                    "required": True, "sha256": hashlib.sha256(b"{}").hexdigest(),
                }]}, "sources[0]", False, None,
            )
            self.assertTrue(any("resolves outside source directory" in e for e in validator.errors))

    def lfs_fixture(self, root):
        relative = "KIP126/LinProgram/Raw/Ceta_AdamsSS_t200.db"
        path = root / relative
        path.parent.mkdir(parents=True)
        payload = b"fixed native database fixture"
        oid = hashlib.sha256(payload).hexdigest()
        artifact = {"path": relative, "kind": "machine_artifact", "required": True,
                    "sha256": oid, "storage": "git-lfs", "size": len(payload)}
        path.write_text(f"version https://git-lfs.github.com/spec/v1\noid sha256:{oid}\nsize {len(payload)}\n")
        source = {"id": "lwx_machine", "directory": "Source/LWXMachine", "artifacts": [artifact]}
        return path, payload, artifact, source

    def test_registered_archive_lfs_pointer_retains_exact_digest(self) -> None:
        for mutation in (None, "hash", "size"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                old, _, artifact, source = self.lfs_fixture(root)
                relative = "Source/LWXMachine/kervaire_database.rar"
                path = root / relative
                path.parent.mkdir(parents=True)
                old.rename(path)
                artifact["path"] = relative
                if mutation == "hash":
                    artifact["sha256"] = "0" * 64
                elif mutation == "size":
                    artifact["size"] += 1
                validator = InventoryValidator(root, root / "unused.json")
                with mock.patch("check_source_inventory.subprocess.run", return_value=SimpleNamespace(returncode=1)):
                    validator._check_artifacts(source, "sources[0]", False, None)
                if mutation is None:
                    self.assertEqual(validator.errors, [])
                    self.assertEqual(validator.lfs_pointer_only_count, 1)
                else:
                    self.assertTrue(any("Git LFS pointer" in e for e in validator.errors))

    def test_pointer_only_is_metadata_and_not_verified_content(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            _, _, _, source = self.lfs_fixture(root)
            validator = InventoryValidator(root, root / "unused.json")
            with mock.patch("check_source_inventory.subprocess.run", return_value=SimpleNamespace(returncode=1)):
                validator._check_artifacts(source, "sources[0]", False, None)
            self.assertEqual(validator.errors, [])
            self.assertEqual(validator.lfs_pointer_only_count, 1)
            self.assertEqual(validator.lfs_cached_payload_count, 0)

    def test_lfs_pointer_oid_size_and_grammar_are_checked(self) -> None:
        for mutation in ("oid", "size", "grammar"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                path, _, artifact, source = self.lfs_fixture(root)
                text = path.read_text()
                if mutation == "oid":
                    text = text.replace(artifact["sha256"], "0" * 64)
                elif mutation == "size":
                    text = text.replace(f"size {artifact['size']}", "size 1")
                else:
                    text += "unrecognized extension\n"
                path.write_text(text)
                validator = InventoryValidator(root, root / "unused.json")
                validator._check_artifacts(source, "sources[0]", False, None)
                self.assertTrue(any("Git LFS pointer" in e for e in validator.errors))
                self.assertEqual(validator.lfs_pointer_only_count, 0)
                self.assertEqual(validator.lfs_cached_payload_count, 0)

    def test_cached_lfs_payload_is_checked_by_actual_size_and_hash(self) -> None:
        for mutation in (None, "size", "hash"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                _, payload, artifact, source = self.lfs_fixture(root)
                common = root / "common-git"
                oid = artifact["sha256"]
                cached = common / "lfs/objects" / oid[:2] / oid[2:4] / oid
                cached.parent.mkdir(parents=True)
                cached.write_bytes(payload if mutation is None else payload[:-1] if mutation == "size" else b"x" * len(payload))
                validator = InventoryValidator(root, root / "unused.json")
                with mock.patch("check_source_inventory.subprocess.run", return_value=SimpleNamespace(returncode=0, stdout=str(common))):
                    validator._check_artifacts(source, "sources[0]", False, None)
                self.assertEqual(validator.lfs_pointer_only_count, 0)
                if mutation is None:
                    self.assertEqual(validator.errors, [])
                    self.assertEqual(validator.lfs_cached_payload_count, 1)
                else:
                    self.assertTrue(any("cached Git LFS payload hash/size mismatch" in e for e in validator.errors))
                    self.assertEqual(validator.lfs_cached_payload_count, 0)

    def test_lin_database_exception_does_not_allow_nearby_paths_or_symlink_escapes(self) -> None:
        for mutation in ("nearby", "symlink"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                path, payload, artifact, source = self.lfs_fixture(root)
                if mutation == "nearby":
                    artifact["path"] = "KIP126/LinProgram/Raw/Ceta_AdamsSS_t201.db"
                    path.rename(root / artifact["path"])
                else:
                    outside = root / "cached.db"
                    outside.write_bytes(payload)
                    path.unlink()
                    path.symlink_to(outside)
                validator = InventoryValidator(root, root / "unused.json")
                validator._check_artifacts(source, "sources[0]", False, None)
                self.assertTrue(any("source directory" in e for e in validator.errors))

    def test_naturality_batch_snapshots_keep_exact_path_and_hash_boundaries(self) -> None:
        for batch in ("Batch21", "Batch40"):
            for filename in ("Ceta_Adams_res.db", "map_Adams_res_Ceta__S0.db"):
                for mutation in (None, "hash", "nearby", "symlink"):
                    with self.subTest(batch=batch, filename=filename, mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                        root = Path(temporary)
                        old, payload, artifact, source = self.lfs_fixture(root)
                        relative = f"KIP126/LinProgram/Raw/Naturality/{batch}/" + filename
                        path = root / relative
                        path.parent.mkdir(parents=True)
                        old.rename(path)
                        artifact["path"] = relative
                        if mutation == "hash":
                            artifact["sha256"] = "0" * 64
                        elif mutation == "nearby":
                            other = relative.replace(f"{batch}/", "Batch41/")
                            (root / other).parent.mkdir(parents=True)
                            path.rename(root / other)
                            artifact["path"] = other
                        elif mutation == "symlink":
                            outside = root / "outside.db"
                            outside.write_bytes(payload)
                            path.unlink()
                            path.symlink_to(outside)
                        validator = InventoryValidator(root, root / "unused.json")
                        with mock.patch("check_source_inventory.subprocess.run", return_value=SimpleNamespace(returncode=1)):
                            validator._check_artifacts(source, "sources[0]", False, None)
                        if mutation is None:
                            self.assertEqual(validator.errors, [])
                            self.assertEqual(validator.lfs_pointer_only_count, 1)
                        elif mutation == "hash":
                            self.assertTrue(any("Git LFS pointer" in e for e in validator.errors))
                        else:
                            self.assertTrue(any("source directory" in e for e in validator.errors))

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
