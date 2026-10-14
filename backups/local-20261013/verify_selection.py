#!/usr/bin/env python3
"""Check coverage of the captured paths and the selected source snapshot."""
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath


def check(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    archive = Path(__file__).resolve().parent
    root = archive.parents[1]
    report = json.loads((archive / 'selection.json').read_text())
    captured = {}
    for repository in ('KIP126', 'KIP-base'):
        manifest = json.loads((archive / 'history' / repository / 'manifest.json').read_text())
        for item in manifest['files']:
            captured[repository, item['path']] = item.get('sha256')
    entries = report['entries']
    keys = [(entry['repository'], entry['path']) for entry in entries]
    check(len(set(keys)) == len(keys), 'Duplicate selection entries')
    check(set(keys) == set(captured), 'Captured path coverage differs')
    check(len(keys) == report['captured_changed_paths'] == 121, 'Unexpected path count')
    hashes = {}
    for entry in entries:
        key = entry['repository'], entry['path']
        check(entry['source_sha256'] == captured[key], f'Capture digest differs: {key}')
        check(entry['disposition'], f'Missing disposition: {key}')
        if entry['decision'] is not None:
            check(entry['decision'] in report['decisions'], f'Unknown decision: {key}')
        expected_recovery = f"history/{entry['repository']}/worktree-changes.tar.gz"
        check(entry['recovery'] == expected_recovery, f'Incorrect recovery archive: {key}')
        check((archive / expected_recovery).is_file(), f'Missing recovery archive: {key}')
        for selected in entry['selected']:
            relative = PurePosixPath(selected['path'])
            check(not relative.is_absolute() and '..' not in relative.parts,
                  f'Unsafe selected path: {relative}')
            path = root / relative
            check(path.is_file(), f'Missing selected source: {relative}')
            if relative not in hashes:
                hashes[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
            check(hashes[relative] == selected['sha256'], f'Selected snapshot changed: {relative}')
    for decision in report['decisions'].values():
        for selected in decision['selected']:
            check((root / selected).is_file(), f'Missing decision target: {selected}')
    branch_paths = 0
    for audit in report.get('branch_audits', []):
        manifest = json.loads((archive / 'history' / audit['repository'] / 'manifest.json').read_text())
        refs = {item['ref']: item['commit'] for item in manifest['local_refs']}
        check(refs.get('refs/heads/' + audit['branch']) == audit['tip'], 'Branch tip differs')
        for item in audit['paths']:
            relative = PurePosixPath(item['path'])
            check(not relative.is_absolute() and '..' not in relative.parts,
                  f'Unsafe branch path: {relative}')
            path = root / relative
            check(path.is_file(), f'Missing current branch implementation: {relative}')
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            check(digest == item['selected_sha256'], f'Branch selection changed: {relative}')
            branch_paths += 1
    migration_sources = report.get('interface_migration', {}).get('source_snapshots', [])
    for item in migration_sources:
        relative = PurePosixPath(item['path'])
        check(not relative.is_absolute() and '..' not in relative.parts,
              f'Unsafe migration source path: {relative}')
        path = root / relative
        check(path.is_file(), f'Missing migration source: {relative}')
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        check(digest == item['sha256'], f'Migration snapshot changed: {relative}')
    print(f'All {len(keys)} captured paths accounted for; {len(hashes)} selected source hashes match.')
    print(f'Local-only branch audit: {branch_paths} current Lean files verified.')
    if migration_sources:
        print(f'Interface migration snapshot: {len(migration_sources)} source hashes match.')
    print(json.dumps(dict(Counter(entry['disposition'] for entry in entries)), sort_keys=True))
    print('Snapshot integrity only: this does not establish proof completion or semantic absorption.')


if __name__ == '__main__':
    main()
