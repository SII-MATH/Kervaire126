#!/usr/bin/env python3
"""Verify or restore one captured repository into a new destination."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def run(*args, **kwargs):
    return subprocess.run(args, check=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, **kwargs).stdout


def status_map(repo):
    entries = run('git', '-C', str(repo), 'status', '--porcelain=v1', '-z',
        '--untracked-files=all').split(b'\0')
    result = {}
    i = 0
    while i < len(entries):
        entry = entries[i]
        i += 1
        if not entry:
            continue
        code, path = entry[:2].decode(), entry[3:].decode()
        result[path] = code
        if 'R' in code or 'C' in code:
            i += 1
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', choices=['KIP126', 'KIP-base'])
    parser.add_argument('--destination', type=Path)
    parser.add_argument('--verify-only', action='store_true')
    args = parser.parse_args()
    if bool(args.destination) == args.verify_only:
        parser.error('Choose either --verify-only or --destination PATH')
    if args.destination and args.destination.exists():
        parser.error('Destination already exists; choose a new path')

    root = Path(__file__).resolve().parent / args.repository
    manifest = json.loads((root / 'manifest.json').read_text())
    for item in manifest['artifacts'] + manifest['history']['parts_in_order']:
        path = root / item['path']
        if path.stat().st_size != item['size'] or digest(path) != item['sha256']:
            raise RuntimeError('Artifact verification failed: ' + item['path'])

    with tarfile.open(root / 'worktree-changes.tar.gz', 'r:gz') as archive:
        members = {m.name: m for m in archive.getmembers()}
        expected = {r['path'] for r in manifest['files'] if r['kind'] != 'deleted'}
        if set(members) != expected:
            raise RuntimeError('Archive inventory differs from manifest')
        for record in manifest['files']:
            if record['kind'] == 'file':
                data = archive.extractfile(members[record['path']]).read()
                if hashlib.sha256(data).hexdigest() != record['sha256']:
                    raise RuntimeError('Archived file differs: ' + record['path'])
            elif record['kind'] == 'symlink' and members[record['path']].linkname != record['target']:
                raise RuntimeError('Archived symlink differs: ' + record['path'])

    with tempfile.TemporaryDirectory(prefix='kervaire-backup-verify-') as tmp:
        bundle = Path(tmp) / 'history.bundle'
        with bundle.open('wb') as output:
            for item in manifest['history']['parts_in_order']:
                with (root / item['path']).open('rb') as part:
                    shutil.copyfileobj(part, output)
        if digest(bundle) != manifest['history']['sha256']:
            raise RuntimeError('Reassembled history differs from manifest')
        mirror = Path(tmp) / 'history.git'
        run('git', 'clone', '--mirror', str(bundle), str(mirror))
        run('git', '-C', str(mirror), 'fsck', '--full', '--no-reflogs')
        captured = {r['ref']: r['commit'] for r in manifest['local_refs']}
        restored = dict(line.split(' ', 1) for line in run('git', '-C', str(mirror),
            'for-each-ref', '--format=%(refname) %(objectname)', 'refs/heads',
            'refs/tags').decode().splitlines())
        if restored != captured:
            raise RuntimeError('History refs differ from manifest')
        if args.verify_only:
            print(args.repository + ': all archive hashes, files, branch tips and Git history verified')
            return

        destination = args.destination.resolve()
        run('git', 'clone', '--no-checkout', '--branch', manifest['current_branch'],
            str(bundle), str(destination))
        for ref, commit in captured.items():
            run('git', '-C', str(destination), 'update-ref', ref, commit)
        run('git', '-C', str(destination), '-c', 'filter.lfs.required=false',
            '-c', 'filter.lfs.smudge=', '-c', 'filter.lfs.process=',
            'checkout', manifest['current_branch'])
        staged = root / 'staged-changes.patch'
        if staged.stat().st_size:
            run('git', '-C', str(destination), 'apply', '--cached', '--binary', str(staged))
        with tarfile.open(root / 'worktree-changes.tar.gz', 'r:gz') as archive:
            archive.extractall(destination, filter='data')
        for record in manifest['files']:
            path = destination / record['path']
            if record['kind'] == 'deleted' and (path.exists() or path.is_symlink()):
                path.unlink()
            elif record['kind'] == 'file':
                if digest(path) != record['sha256']:
                    raise RuntimeError('Restored file differs: ' + record['path'])
                os.chmod(path, record['mode'])
            elif record['kind'] == 'symlink' and os.readlink(path) != record['target']:
                raise RuntimeError('Restored symlink differs: ' + record['path'])
        run('git', '-C', str(destination), 'remote', 'set-url', 'origin', manifest['source_remote'])
        expected_status = {r['path']: r['git_status'] for r in manifest['files']}
        actual_status = status_map(destination)
        if actual_status != expected_status:
            raise RuntimeError('Restored Git status differs: ' + repr({
                'unexpected': {p: s for p, s in actual_status.items() if expected_status.get(p) != s},
                'missing': {p: s for p, s in expected_status.items() if actual_status.get(p) != s}}))
        print(args.repository + ': restored ' + str(len(expected_status)) +
            ' changed/untracked files and ' + str(len(captured)) + ' local refs to ' + str(destination))


if __name__ == '__main__':
    main()
