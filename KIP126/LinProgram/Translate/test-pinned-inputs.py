#!/usr/bin/env python3
"""The native replay loader must validate pointer metadata AND payload bytes."""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location("replay_lowstem", Path(__file__).with_name("replay-lowstem.py"))
REPLAY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REPLAY)


class PinnedInputTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="lin-pinned-input-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.raw = self.root / "Raw"
        self.raw.mkdir()
        self.common = self.root / "common-git"
        self.payload = b"fixed native loader byte fixture"
        self.digest = hashlib.sha256(self.payload).hexdigest()
        self.name = "selected.db"
        self.path = self.raw / self.name
        self.pointer = (f"version https://git-lfs.github.com/spec/v1\n"
                        f"oid sha256:{self.digest}\nsize {len(self.payload)}\n")
        (self.raw / "manifest.json").write_text(json.dumps({"files": [{
            "path": self.name, "sha256": self.digest, "size": len(self.payload),
        }]}))
        self.path.write_text(self.pointer)
        self.cached = self.common / "lfs/objects" / self.digest[:2] / self.digest[2:4] / self.digest
        self.cached.parent.mkdir(parents=True)
        self.cached.write_bytes(self.payload)
        raw_patch = mock.patch.object(REPLAY, "RAW", self.raw)
        raw_patch.start()
        self.addCleanup(raw_patch.stop)
        git_patch = mock.patch.object(REPLAY.subprocess, "check_output", return_value=str(self.common) + "\n")
        self.git = git_patch.start()
        self.addCleanup(git_patch.stop)

    def test_physical_input_checks_payload_bytes(self):
        self.path.write_bytes(self.payload)
        self.assertEqual(REPLAY.pinned(self.name), (self.path, self.payload, self.digest))
        self.git.assert_not_called()
        self.path.write_bytes(b"x" * len(self.payload))
        with self.assertRaisesRegex(ValueError, "pinned input mismatch"):
            REPLAY.pinned(self.name)

    def test_valid_pointer_loads_verified_cache_bytes(self):
        self.assertEqual(REPLAY.pinned(self.name), (self.cached, self.payload, self.digest))
        self.git.assert_called_once()

    def test_wrong_pointer_size_is_rejected_before_cache_lookup(self):
        self.path.write_text(self.pointer.replace(f"size {len(self.payload)}", "size 1"))
        with self.assertRaisesRegex(ValueError, "pointer OID/size mismatch"):
            REPLAY.pinned(self.name)
        self.git.assert_not_called()

    def test_wrong_pointer_oid_is_rejected_before_cache_lookup(self):
        self.path.write_text(self.pointer.replace(self.digest, "0" * 64))
        with self.assertRaisesRegex(ValueError, "pointer OID/size mismatch"):
            REPLAY.pinned(self.name)
        self.git.assert_not_called()

    def test_malformed_and_path_injection_pointers_cannot_construct_cache_paths(self):
        for text in (self.pointer + "extra field\n", self.pointer.rstrip("\n"),
                     self.pointer.replace(self.digest, "../../outside.db"),
                     self.pointer.replace(self.digest, "/tmp/outside.db"),
                     self.pointer.replace(self.digest, self.digest.upper())):
            with self.subTest(pointer=text):
                self.path.write_text(text)
                with self.assertRaisesRegex(ValueError, "malformed Git LFS pointer"):
                    REPLAY.pinned(self.name)
        self.git.assert_not_called()

    def test_missing_payload_never_accepts_pointer_metadata_as_input(self):
        self.cached.unlink()
        with self.assertRaisesRegex(FileNotFoundError, "missing pinned Git LFS payload"):
            REPLAY.pinned(self.name)

    def test_cached_payload_checks_size_and_hash_after_pointer_validation(self):
        for data in (self.payload[:-1], b"x" * len(self.payload)):
            with self.subTest(payload=data):
                self.cached.write_bytes(data)
                with self.assertRaisesRegex(ValueError, "pinned input mismatch"):
                    REPLAY.pinned(self.name)


if __name__ == "__main__":
    unittest.main()
