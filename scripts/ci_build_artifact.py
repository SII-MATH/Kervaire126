#!/usr/bin/env python3
"""Transfer project Lake products between a successful PR and its merge build.

This is an optional optimization: callers must still run the normal Lake build.
Only the project build tree is transferred, never dependency sources or Git state.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import subprocess
import tarfile
import tempfile
import urllib.parse
import urllib.request
import zipfile

SCHEMA = "lean-project-build/v1"
MAX_BYTES = 20 * 1024**3
MAX_MEMBERS = 1_000_000
WORKFLOW = ".github/workflows/ci.yml"


def sha256(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        while data := stream.read(1024 * 1024):
            digest.update(data)
    return digest.hexdigest()


def fingerprint(root):
    return hashlib.sha256(subprocess.check_output(
        ["git", "ls-tree", "-r", "-z", "HEAD"], cwd=root)).hexdigest()


def inputs(root, runner_os, arch):
    # A commit-tree key must describe the actual checked-out tracked inputs.
    subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=root, check=True)
    return {"schema": SCHEMA, "input_fingerprint": fingerprint(root),
            "toolchain_sha256": sha256(root / "lean-toolchain"),
            "manifest_sha256": sha256(root / "lake-manifest.json"),
            "os": runner_os, "arch": arch}


def artifact_name(identity):
    return f"lean-build-v1-{identity['input_fingerprint']}-{identity['os']}-{identity['arch']}"


def pack(root, output, env, runner_os, arch):
    identity = inputs(root, runner_os, arch)
    metadata = dict(identity, repository=env["GITHUB_REPOSITORY"],
                    run_id=str(env["GITHUB_RUN_ID"]),
                    run_attempt=str(env["GITHUB_RUN_ATTEMPT"]))
    build = root / ".lake/build"
    if (root / ".lake").is_symlink() or build.is_symlink() or not build.is_dir():
        raise ValueError("project build must be an existing ordinary directory")
    output.mkdir(parents=True, exist_ok=True)
    if output.resolve().is_relative_to(build.resolve()):
        raise ValueError("artifact output cannot be inside the project build")
    archive = output / "project-build.tar.gz"
    with tarfile.open(archive, "w:gz", compresslevel=1) as tar:
        # Add explicitly: tarfile's recursive mode can encode hard links.
        size = 0
        count = 0
        for directory, dirs, files in os.walk(build, followlinks=False):
            for path in [Path(directory)] + [Path(directory) / f for f in sorted(files)]:
                info = tar.gettarinfo(str(path), str(path.relative_to(root)))
                if not (info.isdir() or info.isreg()):
                    raise ValueError(f"unsupported build entry: {path}")
                size += info.size
                count += 1
                if size > MAX_BYTES or count > MAX_MEMBERS:
                    raise ValueError("project build exceeds artifact size limit")
                if info.isreg():
                    with path.open("rb") as stream:
                        tar.addfile(info, stream)
                else:
                    tar.addfile(info)
            for directory_name in dirs:
                if (Path(directory) / directory_name).is_symlink():
                    raise ValueError("symbolic links are not supported in project builds")
            dirs.sort()
    if inputs(root, runner_os, arch) != identity:
        raise ValueError("tracked inputs changed while packing")
    metadata["archive_sha256"] = sha256(archive)
    (output / "metadata.json").write_text(json.dumps(metadata, sort_keys=True) + "\n")


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if urllib.parse.urlsplit(newurl).scheme != "https":
            raise ValueError("artifact redirect must use HTTPS")
        result = super().redirect_request(req, fp, code, msg, headers, newurl)
        if result and urllib.parse.urlsplit(newurl).netloc != "api.github.com":
            result.remove_header("Authorization")
        return result


def copy_limited(source, target, limit):
    total = 0
    while data := source.read(1024 * 1024):
        total += len(data)
        if total > limit:
            raise ValueError("artifact exceeds size limit")
        target.write(data)


class GitHub:
    def __init__(self, token):
        if not token:
            raise ValueError("GitHub read token is missing")
        self.token = token
        self.opener = urllib.request.build_opener(SafeRedirect())

    def open(self, path):
        if not path.startswith("/repos/"):
            raise ValueError("invalid GitHub API path")
        return self.opener.open(urllib.request.Request(
            "https://api.github.com" + path,
            headers={"Authorization": "Bearer " + self.token,
                     "Accept": "application/vnd.github+json",
                     "X-GitHub-Api-Version": "2022-11-28"}), timeout=60)

    def get(self, path):
        with self.open(path) as stream:
            data = stream.read(16 * 1024**2 + 1)
            if len(data) > 16 * 1024**2:
                raise ValueError("GitHub API response too large")
            return json.loads(data)

    def download(self, path, target):
        with self.open(path) as stream, target.open("wb") as output:
            copy_limited(stream, output, MAX_BYTES + 64 * 1024**2)


def candidates(api, repository, commit, branch, name):
    base = "/repos/" + repository
    workflow = api.get(base + "/actions/workflows/ci.yml")
    if workflow.get("path") != WORKFLOW:
        raise ValueError("CI workflow path does not match")
    pulls = api.get(base + f"/commits/{urllib.parse.quote(commit, safe='')}/pulls?per_page=100")
    for pr in pulls:
        if not (pr.get("merged_at") and pr.get("merge_commit_sha") == commit
                and pr.get("base", {}).get("ref") == branch
                and pr.get("base", {}).get("repo", {}).get("full_name") == repository
                and pr.get("head", {}).get("repo", {}).get("full_name") == repository):
            continue
        head = pr["head"]["sha"]
        query = urllib.parse.urlencode({"event": "pull_request", "status": "success",
                                        "head_sha": head, "per_page": 100})
        runs = api.get(base + f"/actions/workflows/{int(workflow['id'])}/runs?{query}")
        for run in runs["workflow_runs"]:
            if not (run.get("workflow_id") == workflow["id"]
                    and run.get("path") == WORKFLOW
                    and run.get("repository", {}).get("full_name") == repository
                    and run.get("head_repository", {}).get("full_name") == repository
                    and run.get("event") == "pull_request" and run.get("status") == "completed"
                    and run.get("conclusion") == "success" and run.get("head_sha") == head):
                continue
            artifacts = api.get(base + f"/actions/runs/{int(run['id'])}/artifacts?per_page=100")
            for artifact in artifacts["artifacts"]:
                if artifact.get("name") == name and not artifact.get("expired", True):
                    yield run, artifact


def unpack_zip(download, staging):
    with zipfile.ZipFile(download) as archive:
        entries = archive.infolist()
        expected = {"metadata.json", "project-build.tar.gz"}
        if len(entries) != 2 or {entry.filename for entry in entries} != expected:
            raise ValueError("artifact ZIP must contain exactly metadata and project archive")
        for entry in entries:
            mode = entry.external_attr >> 16
            if entry.is_dir() or (stat.S_IFMT(mode) not in (0, stat.S_IFREG)):
                raise ValueError("artifact ZIP contains a non-regular entry")
            limit = 64 * 1024 if entry.filename == "metadata.json" else MAX_BYTES + 32 * 1024**2
            if entry.file_size > limit:
                raise ValueError("artifact ZIP entry exceeds size limit")
            with archive.open(entry) as source, (staging / entry.filename).open("wb") as target:
                copy_limited(source, target, limit)


def unpack_tar(archive, staging):
    seen = set()
    size = 0
    directories = []
    with tarfile.open(archive, "r|gz") as tar:
        for member in tar:
            path = PurePosixPath(member.name)
            if (path.is_absolute() or ".." in path.parts or "\\" in member.name
                    or path.parts[:2] != (".lake", "build")
                    or not (member.isdir() or member.isreg()) or member.size < 0 or path in seen):
                raise ValueError("unsafe or duplicate path in project archive")
            seen.add(path)
            size += member.size
            if size > MAX_BYTES or len(seen) > MAX_MEMBERS:
                raise ValueError("project archive exceeds extraction limit")
            target = staging.joinpath(*path.parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                directories.append((target, member.mode & 0o777))
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(member) as source, target.open("xb") as output:
                    copy_limited(source, output, member.size)
                target.chmod(member.mode & 0o777)
                os.utime(target, (member.mtime, member.mtime))
    for directory, mode in reversed(directories):
        directory.chmod(mode)
    if not (staging / ".lake/build").is_dir():
        raise ValueError("project build directory is absent")


def install_build(root, staged):
    lake = root / ".lake"
    build = lake / "build"
    if lake.is_symlink() or build.is_symlink() or (build.exists() and not build.is_dir()):
        raise ValueError("existing Lake build path is not an ordinary directory")
    lake.mkdir(exist_ok=True)
    # Stage on the destination filesystem, so publication uses directory renames.
    with tempfile.TemporaryDirectory(prefix=".ci-build-", dir=lake) as temporary:
        temporary = Path(temporary)
        shutil.move(str(staged), str(temporary / "new"))
        previous = build.exists()
        if previous:
            build.rename(temporary / "old")
        try:
            (temporary / "new").rename(build)
        except BaseException:
            if previous:
                (temporary / "old").rename(build)
            raise


def restore(root, env, runner_os, arch, api=None):
    restored = False
    try:
        if env.get("GITHUB_EVENT_NAME") != "push" or env.get("GITHUB_REF_NAME") not in {"main", "develop"}:
            raise ValueError("artifact restore is limited to main/develop push builds")
        repository = env["GITHUB_REPOSITORY"]
        identity = inputs(root, runner_os, arch)
        api = api or GitHub(env.get("GITHUB_TOKEN"))
        for run, artifact in candidates(api, repository, env["GITHUB_SHA"],
                                        env["GITHUB_REF_NAME"], artifact_name(identity)):
            with tempfile.TemporaryDirectory(prefix="lean-artifact-", dir=env.get("RUNNER_TEMP")) as temporary:
                staging = Path(temporary)
                download = staging / "artifact.zip"
                api.download(f"/repos/{repository}/actions/artifacts/{int(artifact['id'])}/zip", download)
                digest = artifact.get("digest")
                if digest is not None and digest != "sha256:" + sha256(download):
                    raise ValueError("downloaded artifact digest does not match GitHub")
                unpack_zip(download, staging)
                expected = dict(identity, repository=repository, run_id=str(run["id"]),
                                run_attempt=str(run["run_attempt"]),
                                archive_sha256=sha256(staging / "project-build.tar.gz"))
                if json.loads((staging / "metadata.json").read_text()) != expected:
                    raise ValueError("artifact metadata does not match this build and successful run")
                unpack_tar(staging / "project-build.tar.gz", staging)
                if inputs(root, runner_os, arch) != identity:
                    raise ValueError("tracked inputs changed while restoring")
                install_build(root, staging / ".lake/build")
                restored = True
                print(f"Restored project build from successful PR run {run['id']}; Lake will recheck it.")
                break
        if not restored:
            print("::warning::No matching successful same-repository PR artifact; continuing normal build.")
    except Exception as error:
        print(f"::warning::Project build artifact was not restored: {error}; continuing normal build.")
    finally:
        if env.get("GITHUB_OUTPUT"):
            with open(env["GITHUB_OUTPUT"], "a") as output:
                output.write(f"restored={str(restored).lower()}\n")
    return restored


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("fingerprint")
    for name in ("pack", "restore"):
        command = commands.add_parser(name)
        command.add_argument("--os", default=os.environ.get("RUNNER_OS", "Linux"))
        command.add_argument("--arch", default=os.environ.get("RUNNER_ARCH", "X64"))
        if name == "pack":
            command.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path.cwd()
    if args.command == "fingerprint":
        print(fingerprint(root))
    elif args.command == "pack":
        pack(root, args.output, os.environ, args.os, args.arch)
    else:
        restore(root, os.environ, args.os, args.arch)


if __name__ == "__main__":
    main()
