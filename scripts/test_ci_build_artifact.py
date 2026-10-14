"""Offline tests: no GitHub requests and no Lean builds."""

import copy
import contextlib
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import urllib.request
import warnings
import zipfile

from scripts import ci_build_artifact as artifact


class FakeGitHub:
    def __init__(self, archive, identity):
        self.archive = archive
        self.downloads = []
        self.workflow = {"id": 42, "path": artifact.WORKFLOW}
        self.pulls = [{"merged_at": "2026-01-01", "merge_commit_sha": "merged",
                       "base": {"ref": "develop", "repo": {"full_name": "owner/repo"}},
                       "head": {"sha": "head", "repo": {"full_name": "owner/repo"}}}]
        self.run = {"id": 123, "run_attempt": 2, "workflow_id": 42,
                    "path": artifact.WORKFLOW, "repository": {"full_name": "owner/repo"},
                    "head_repository": {"full_name": "owner/repo"}, "event": "pull_request",
                    "status": "completed", "conclusion": "success", "head_sha": "head"}
        self.artifact = {"id": 456, "name": artifact.artifact_name(identity),
                         "expired": False, "digest": "sha256:" + artifact.sha256(archive)}

    def get(self, path):
        if path == "/repos/owner/repo/actions/workflows/ci.yml":
            return self.workflow
        if path == "/repos/owner/repo/commits/merged/pulls?per_page=100":
            return self.pulls
        if path == "/repos/owner/repo/actions/workflows/42/runs?event=pull_request&status=success&head_sha=head&per_page=100":
            return {"workflow_runs": [self.run]}
        if path == "/repos/owner/repo/actions/runs/123/artifacts?per_page=100":
            return {"artifacts": [self.artifact]}
        raise AssertionError("unexpected API call: " + path)

    def download(self, path, target):
        if path != "/repos/owner/repo/actions/artifacts/456/zip":
            raise AssertionError("unexpected download: " + path)
        self.downloads.append(path)
        shutil.copyfile(self.archive, target)


class ArtifactTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.build = self.root / ".lake/build"
        self.build.mkdir(parents=True)
        (self.build / "old").write_text("keep until validated")
        self.dependency = self.root / ".lake/packages/dependency"
        self.dependency.mkdir(parents=True)
        (self.dependency / "source").write_text("never replace")
        self.identity = {"schema": artifact.SCHEMA, "input_fingerprint": "a" * 64,
                         "toolchain_sha256": "b" * 64, "manifest_sha256": "c" * 64,
                         "os": "Linux", "arch": "X64"}
        self.env = {"GITHUB_REPOSITORY": "owner/repo", "GITHUB_SHA": "merged",
                    "GITHUB_EVENT_NAME": "push", "GITHUB_REF_NAME": "develop",
                    "GITHUB_RUN_ID": "123", "GITHUB_RUN_ATTEMPT": "2",
                    "GITHUB_OUTPUT": str(self.root / "outputs")}
        self.inputs = patch.object(artifact, "inputs", return_value=self.identity).start()
        self.addCleanup(patch.stopall)
        self.archive = self.root / "artifact.zip"
        self.make_archive()
        self.api = FakeGitHub(self.archive, self.identity)

    def make_archive(self, metadata_changes=None, members=None, zip_names=None):
        tar_path = self.root / "test.tar.gz"
        with tarfile.open(tar_path, "w:gz") as tar:
            if members is None:
                members = [(".lake/build/lib/lean/Main.olean", tarfile.REGTYPE, b"certified", 0o640),
                           (".lake/build/lib/lean/Main.olean.private", tarfile.REGTYPE, b"private", 0o644),
                           (".lake/build/lib/lean/Main.trace", tarfile.REGTYPE, b"trace", 0o644),
                           (".lake/build/ir/Main.c", tarfile.REGTYPE, b"generated", 0o644)]
            for name, kind, contents, mode in members:
                info = tarfile.TarInfo(name)
                info.type = kind
                info.mode = mode
                info.size = len(contents) if kind == tarfile.REGTYPE else 0
                info.linkname = "../../escape"
                tar.addfile(info, io.BytesIO(contents))
        metadata = dict(self.identity, repository="owner/repo", run_id="123", run_attempt="2",
                        archive_sha256=artifact.sha256(tar_path))
        metadata.update(metadata_changes or {})
        with zipfile.ZipFile(self.archive, "w") as archive:
            archive.writestr("metadata.json", json.dumps(metadata))
            archive.write(tar_path, "project-build.tar.gz")
            for name in zip_names or []:
                with warnings.catch_warnings():
                    warnings.simplefilter("ignore", UserWarning)
                    archive.writestr(name, "extra")
        if hasattr(self, "api"):
            self.api.artifact["digest"] = "sha256:" + artifact.sha256(self.archive)

    def restore(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return artifact.restore(self.root, self.env, "Linux", "X64", self.api)

    def assert_original(self):
        self.assertEqual((self.build / "old").read_text(), "keep until validated")
        self.assertEqual((self.dependency / "source").read_text(), "never replace")

    def test_valid_streamed_restore_preserves_all_products_and_modes(self):
        self.assertTrue(self.restore())
        self.assertFalse((self.build / "old").exists())
        output = self.build / "lib/lean/Main.olean"
        self.assertEqual(output.read_bytes(), b"certified")
        self.assertEqual(output.stat().st_mode & 0o777, 0o640)
        self.assertTrue((self.build / "lib/lean/Main.olean.private").is_file())
        self.assertTrue((self.build / "lib/lean/Main.trace").is_file())
        self.assertTrue((self.build / "ir/Main.c").is_file())
        self.assertEqual((self.dependency / "source").read_text(), "never replace")
        self.assertEqual((self.root / "outputs").read_text(), "restored=true\n")

    def test_all_metadata_fields_are_compared(self):
        for field in dict(self.identity, repository="", run_id="", run_attempt="", archive_sha256=""):
            with self.subTest(field=field):
                self.make_archive({field: "wrong"})
                self.assertFalse(self.restore())
                self.assert_original()

    def test_forks_wrong_base_unmerged_and_unrelated_merges_are_rejected(self):
        valid = copy.deepcopy(self.api.pulls[0])
        variants = []
        for field, value in [("merged_at", None), ("merge_commit_sha", "other")]:
            pr = copy.deepcopy(valid)
            pr[field] = value
            variants.append(pr)
        for section, field, value in [("head", "repo", {"full_name": "fork/repo"}),
                                      ("base", "repo", {"full_name": "other/repo"}),
                                      ("base", "ref", "main")]:
            pr = copy.deepcopy(valid)
            pr[section][field] = value
            variants.append(pr)
        for pr in variants:
            with self.subTest(pr=pr):
                self.api.pulls = [pr]
                self.assertFalse(self.restore())
                self.assertFalse(self.api.downloads)
                self.assert_original()

    def test_unsuccessful_or_different_workflow_runs_are_rejected(self):
        valid = copy.deepcopy(self.api.run)
        for field, value in [("conclusion", "failure"), ("status", "in_progress"),
                             ("workflow_id", 7), ("path", ".github/workflows/evil.yml"),
                             ("head_sha", "other"), ("event", "push"),
                             ("repository", {"full_name": "other/repo"}),
                             ("head_repository", {"full_name": "fork/repo"})]:
            with self.subTest(field=field):
                self.api.run = dict(valid, **{field: value})
                self.assertFalse(self.restore())
                self.assertFalse(self.api.downloads)
                self.assert_original()

    def test_wrong_artifact_name_expiry_and_digest_are_rejected(self):
        valid = self.api.artifact.copy()
        for field, value in [("name", "other"), ("expired", True), ("digest", "sha256:bad")]:
            with self.subTest(field=field):
                self.api.artifact = dict(valid, **{field: value})
                self.assertFalse(self.restore())
                self.assert_original()

    def test_tar_escape_links_devices_and_duplicates_are_rejected(self):
        for name, kind in [("../escape", tarfile.REGTYPE), ("/tmp/escape", tarfile.REGTYPE),
                           (".lake/packages/escape", tarfile.REGTYPE),
                           (".lake/build/../../escape", tarfile.REGTYPE),
                           (".lake/build\\escape", tarfile.REGTYPE),
                           (".lake/build/link", tarfile.SYMTYPE),
                           (".lake/build/link", tarfile.LNKTYPE),
                           (".lake/build/device", tarfile.CHRTYPE),
                           (".lake/build/pipe", tarfile.FIFOTYPE)]:
            with self.subTest(name=name, kind=kind):
                self.make_archive(members=[(name, kind, b"evil", 0o644)])
                self.assertFalse(self.restore())
                self.assert_original()
        member = (".lake/build/duplicate", tarfile.REGTYPE, b"evil", 0o644)
        self.make_archive(members=[member, member])
        self.assertFalse(self.restore())
        self.assert_original()

    def test_zip_unexpected_and_duplicate_entries_are_rejected(self):
        for name in ["../escape", "metadata.json", "unexpected"]:
            with self.subTest(name=name):
                self.make_archive(zip_names=[name])
                self.assertFalse(self.restore())
                self.assert_original()

    def test_input_changes_during_download_do_not_replace_current_build(self):
        self.inputs.side_effect = [self.identity, dict(self.identity, input_fingerprint="changed")]
        self.assertFalse(self.restore())
        self.assert_original()

    def test_extraction_size_limit_keeps_existing_build(self):
        with patch.object(artifact, "MAX_BYTES", 3):
            self.assertFalse(self.restore())
        self.assert_original()

    def test_zip_symlink_is_rejected(self):
        with zipfile.ZipFile(self.archive) as original:
            contents = {name: original.read(name) for name in original.namelist()}
        with zipfile.ZipFile(self.archive, "w") as archive:
            for name, data in contents.items():
                info = zipfile.ZipInfo(name)
                info.external_attr = (0o120777 if name == "metadata.json" else 0o100644) << 16
                archive.writestr(info, data)
        self.api.artifact["digest"] = "sha256:" + artifact.sha256(self.archive)
        self.assertFalse(self.restore())
        self.assert_original()

    def test_failed_publication_rolls_back_existing_build(self):
        original_rename = Path.rename
        def fail_new_publication(path, target):
            if path.name == "new":
                raise OSError("simulated rename failure")
            return original_rename(path, target)
        with patch.object(Path, "rename", fail_new_publication):
            self.assertFalse(self.restore())
        self.assert_original()

    def test_api_failure_is_optional_and_outputs_false(self):
        self.api.get = lambda path: (_ for _ in ()).throw(OSError("network unavailable"))
        self.assertFalse(self.restore())
        self.assert_original()
        self.assertEqual((self.root / "outputs").read_text(), "restored=false\n")

    def test_only_main_and_develop_pushes_may_restore(self):
        for event, branch in [("pull_request", "develop"), ("workflow_dispatch", "main"), ("push", "topic")]:
            self.env.update(GITHUB_EVENT_NAME=event, GITHUB_REF_NAME=branch)
            self.assertFalse(self.restore())
            self.assertFalse(self.api.downloads)

    def test_existing_symlink_is_not_followed(self):
        shutil.rmtree(self.build)
        self.build.symlink_to(self.dependency, target_is_directory=True)
        self.assertFalse(self.restore())
        self.assertTrue(self.build.is_symlink())
        self.assertEqual((self.dependency / "source").read_text(), "never replace")

    def test_pack_transfers_only_project_build_and_rejects_symlinks(self):
        output = self.root / "packed"
        artifact.pack(self.root, output, self.env, "Linux", "X64")
        with tarfile.open(output / "project-build.tar.gz") as tar:
            self.assertEqual(tar.getnames(), [".lake/build", ".lake/build/old"])
        metadata = json.loads((output / "metadata.json").read_text())
        self.assertEqual(metadata["archive_sha256"], artifact.sha256(output / "project-build.tar.gz"))
        (self.build / "link").symlink_to(self.dependency / "source")
        with self.assertRaises(ValueError):
            artifact.pack(self.root, output, self.env, "Linux", "X64")

    def test_pack_rejects_input_change(self):
        self.inputs.side_effect = [self.identity, dict(self.identity, input_fingerprint="changed")]
        with self.assertRaisesRegex(ValueError, "inputs changed"):
            artifact.pack(self.root, self.root / "packed", self.env, "Linux", "X64")

    def test_redirect_does_not_forward_token_to_storage(self):
        request = urllib.request.Request("https://api.github.com/archive", headers={"Authorization": "Bearer secret"})
        handler = artifact.SafeRedirect()
        target = handler.redirect_request(request, None, 302, "Found", {}, "https://storage.example/artifact")
        self.assertFalse(target.has_header("Authorization"))
        same = handler.redirect_request(request, None, 302, "Found", {}, "https://api.github.com/next")
        self.assertEqual(same.get_header("Authorization"), "Bearer secret")
        with self.assertRaises(ValueError):
            handler.redirect_request(request, None, 302, "Found", {}, "http://storage.example/artifact")


class FingerprintTests(unittest.TestCase):
    def test_whole_tracked_tree_includes_workflow_scripts_paths_and_deletions(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, stderr=subprocess.DEVNULL)
            git("init")
            git("config", "user.name", "CI test")
            git("config", "user.email", "ci@example.invalid")
            for name in ["lean-toolchain", "lake-manifest.json", "lakefile.lean", ".github/workflows/ci.yml", "scripts/build.py"]:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(name)
            git("add", ".")
            git("commit", "-m", "initial")
            before = artifact.fingerprint(root)
            self.assertEqual(before, hashlib.sha256(git("ls-tree", "-r", "-z", "HEAD")).hexdigest())
            for name in ["lakefile.lean", ".github/workflows/ci.yml", "scripts/build.py"]:
                (root / name).write_text("changed")
                with self.assertRaises(subprocess.CalledProcessError):
                    artifact.inputs(root, "Linux", "X64")
                git("add", ".")
                git("commit", "-m", "change input")
                after = artifact.fingerprint(root)
                self.assertNotEqual(before, after)
                before = after
            git("mv", "scripts/build.py", "scripts/renamed.py")
            git("commit", "-m", "rename")
            self.assertNotEqual(before, artifact.fingerprint(root))
            before = artifact.fingerprint(root)
            git("rm", "scripts/renamed.py")
            git("commit", "-m", "remove")
            self.assertNotEqual(before, artifact.fingerprint(root))


if __name__ == "__main__":
    unittest.main()
