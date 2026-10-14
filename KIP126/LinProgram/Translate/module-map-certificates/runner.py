#!/usr/bin/env python3
"""Isolated, hash-checked DAG replay of the complete native Ceta certificates.

Generated jobs use direct Lean after one targeted external Lake freshness check.
No native_decide, inferred success, or unverified olean adoption.
Only successful direct Lean invocations receive reusable receipts. Hashes cover
generated sources, every transitive external olean, compiler, source inputs and
dependency receipts. Completion includes the final theorem and axiom audit.
"""
import argparse
import concurrent.futures
import fcntl
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import shutil
import sys
import time

SCHEMA = 'lin-native-ceta-runner/v2-fixed-inputs'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(4 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()

def fingerprint(value):
    return hashlib.sha256(encoded(value)).hexdigest()

def atomic(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.new')
    temp.write_bytes(encoded(value))
    temp.replace(path)

def module_path(name, suffix):
    return Path(name.replace('.', '/') + suffix)

def module_artifacts(obj):
    return [p for p in [obj.with_suffix('.ilean'), obj.with_suffix('.ir'),
                       *sorted(obj.parent.glob(obj.name + '*'))] if p.is_file()]

def environment(root, output):
    def lake(*args):
        return subprocess.check_output(['lake', 'env', *args], cwd=root, text=True).strip()
    lean = Path(lake('which', 'lean')).resolve()
    base = lake('printenv', 'LEAN_PATH')
    paths = [(root / p).resolve() for p in base.split(':') if p]
    paths.append(lean.parent.parent / 'lib/lean')
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join(map(str, [output / 'build/lib/lean', *paths]))
    return lean, list(dict.fromkeys(paths)), env

def resolve_module(paths, name):
    """Lean commits to the first root containing a module's first component."""
    first = name.split('.')[0]
    for root in paths:
        if (root / first).is_dir() or (root / (first + '.olean')).is_file():
            obj = root / module_path(name, '.olean')
            require(obj.is_file(), 'namespace shadowing hides dependency: ' + name)
            return obj
    raise ValueError('missing external module: ' + name)

def refresh_external(root, jobs, output):
    names = set(jobs)
    direct = sorted({i for j in jobs.values() for i in j['imports'] if i not in names
                     and i.split('.')[0] not in {'Lean', 'Init', 'Std', 'Lake'}})
    command = ['lake', 'build', *('+' + n + ':olean' for n in direct)]
    log = output / 'logs/freshness.log'
    with log.open('w') as f:
        result = subprocess.run(command, cwd=root, stdout=f, stderr=subprocess.STDOUT)
    require(result.returncode == 0, 'external dependency freshness failed: ' + str(log))
    return {'command': command, 'log': str(log), 'exit_code': result.returncode}

def external_snapshot(root, lean, paths, jobs):
    names = set(jobs)
    pending = {i for j in jobs.values() for i in j['imports'] if i not in names}
    modules, files = {}, {}
    while pending:
        name = pending.pop()
        if name in modules:
            continue
        obj = resolve_module(paths, name)
        metadata = obj.with_suffix('.ilean')
        require(metadata.is_file(), 'cannot fingerprint import closure without ilean: ' + name)
        info = json.loads(metadata.read_text())
        imports = [i[0] if isinstance(i, list) else i for i in info['directImports']]
        artifacts = module_artifacts(obj)
        modules[name] = {'olean': str(obj), 'imports': imports,
                         'artifact_suffixes': [p.name[len(obj.stem):] for p in artifacts]}
        for p in artifacts:
            files[str(p)] = digest(p)
        local_source = root / module_path(name, '.lean')
        if local_source.is_file():
            files[str(local_source)] = digest(local_source)
        pending.update(i for i in imports if i not in names and i not in modules)
    files[str(lean)] = digest(lean)
    for lib in sorted((lean.parent.parent / 'lib/lean').glob('*.so')):
        files[str(lib)] = digest(lib)
    return {'modules': modules, 'files': files, 'lean_version': subprocess.check_output(
        [str(lean), '--version'], text=True).strip()}

def verify_files(files):
    for name, expected in files.items():
        require(Path(name).is_file() and digest(name) == expected,
                'source/dependency changed during replay: ' + name)

def frozen_copy(source, target, expected):
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        require(not target.is_symlink() and digest(target) == expected,
                'existing frozen input is altered: ' + str(target))
        return
    temp = target.with_suffix(target.suffix + '.copying')
    shutil.copyfile(source, temp)
    require(digest(temp) == expected, 'input changed while freezing: ' + str(source))
    temp.chmod(0o444)
    temp.replace(target)

def freeze_inputs(output, external, jobs):
    extkey = fingerprint(external)
    library = output / 'frozen' / extkey / 'lib/lean'
    frozen = {}
    for name, module in external['modules'].items():
        obj = Path(module['olean'])
        for source in module_artifacts(obj):
            if source.is_file():
                suffix = source.name[len(obj.stem):]
                target = library / module_path(name, suffix)
                expected = external['files'][str(source)]
                frozen_copy(source, target, expected)
                frozen[str(target)] = expected
    sourcekey = fingerprint({n: j['sha256'] for n, j in jobs.items()})
    source_root = output / 'frozen-sources' / sourcekey
    for name, job in jobs.items():
        target = source_root / module_path(name, '.lean')
        frozen_copy(output / job['source'], target, job['sha256'])
        frozen[str(target)] = job['sha256']
    return library, source_root, frozen

def bind_overlay(output, jobs, external, library):
    """No regular or misdirected external olean may shadow the frozen closure."""
    overlay = output / 'build/lib/lean'
    owned = {str(module_path(n, '.olean')) for n in jobs}
    expected = {}
    for name in external['modules']:
        if name.startswith('KIP126.'):
            obj = library / module_path(name, '.olean')
            for p in module_artifacts(obj):
                if p.is_file():
                    expected[str(p.relative_to(library))] = p
    # Permit migration only from the exact original object recorded in the hash
    # snapshot. All other legacy shadowing is rejected, never silently adopted.
    originals = {str(module_path(n, '.olean')): Path(m['olean']).resolve()
                 for n, m in external['modules'].items()}
    for p in overlay.rglob('*.olean'):
        rel = str(p.relative_to(overlay))
        if rel in owned:
            continue
        require(p.is_symlink(), 'unowned regular olean in overlay: ' + str(p))
        if rel in expected:
            require(p.resolve() == expected[rel].resolve() or p.resolve() == originals.get(rel),
                    'misdirected overlay symlink: ' + str(p))
        else:
            # Old broad mirrors may contain unneeded modules. Remove those links
            # so they cannot provide an unrecorded import to the new run.
            p.unlink()
    for rel, target in expected.items():
        p = overlay / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        if p.is_symlink():
            p.unlink()
        require(not p.exists(), 'unowned regular artifact in overlay: ' + str(p))
        p.symlink_to(target)
    verify_resolution(overlay, library, external)
    return overlay

def verify_resolution(overlay, library, external):
    for name, module in external['modules'].items():
        actual = resolve_module([overlay, library], name)
        expected_obj = library / module_path(name, '.olean')
        require(actual.resolve() == expected_obj.resolve(), 'actual Lean dependency shadowed: ' + name)
        expected_suffixes = set(module.get('artifact_suffixes', ['.olean']))
        for suffix in expected_suffixes | {'.ir', '.olean', '.olean.private', '.olean.server', '.ilean'}:
            sidecar = actual.parent / (actual.stem + suffix)
            wanted = expected_obj.parent / (expected_obj.stem + suffix)
            require(sidecar.is_file() == (suffix in expected_suffixes),
                    'artifact presence differs from frozen dependency: ' + name + suffix)
            if suffix in expected_suffixes:
                require(sidecar.resolve() == wanted.resolve(),
                        'actual Lean artifact shadowed: ' + name + suffix)

def verify_owned_family(target):
    require(target.is_file() and not target.is_symlink(), 'missing or aliased generated olean: ' + str(target))
    extras = [p for p in module_artifacts(target) if p != target]
    require(not extras, 'unexpected generated module sidecars: ' + str(extras))

def clean_owned_partials(output, jobs):
    for name in jobs:
        require(re.fullmatch(r'(?:[A-Za-z_][A-Za-z0-9_]*\.)*[A-Za-z_][A-Za-z0-9_]*', name),
                'invalid Lean module name in plan: ' + name)
        partial = output / 'build/lib/lean' / module_path(name, '.pending.olean')
        for artifact in module_artifacts(partial):
            artifact.unlink()

def selected_jobs(jobs, targets):
    result = set()
    def visit(name):
        require(name in jobs, 'unknown target: ' + name)
        if name not in result:
            result.add(name)
            for dep in jobs[name]['dependencies']:
                visit(dep)
    for target in targets or [n for n, j in jobs.items() if j['kind'] == 'audit']:
        visit(target)
    return result

def validate_complete_plan(output, manifest, jobs):
    """A self-declared set of jobs is never the full native-map contract.

    The same-package generator reauthenticates the original entities and every
    witness, and compares the entire expected manifest and Lean sources. Fixed
    final/audit/block names also fail closed before that potentially costly
    check. Do not select the checker program from untrusted manifest metadata.
    """
    contracts = {
        'lin-native-complete-ceta-certificate-build/v2-repository-support':
            ('CetaToSphere', 'generate.py', 150, 76569, 887),
        'lin-native-complete-cw-certificate-build/v2-repository-support':
            ('CWToCeta', 'generate-cw.py', 136, 69263, 844),
    }
    schema = manifest.get('schema')
    require(schema in contracts, 'unsupported complete native certificate schema')
    family, generator_name, block_count, relation_count, generator_count = contracts[schema]
    base = 'KIP126.LinProgram.Certificates.ModuleMaps.' + family
    final, audit = base + '.Proofs', base + '.Checks'
    blocks = {base + f'.Relations{i:03d}' for i in range(block_count)}
    require(manifest.get('source_blocks') == block_count and
            manifest.get('all_relation_count') == relation_count and
            manifest.get('generator_count') == generator_count,
            'complete original native coverage metadata differs')
    require({n for n, j in jobs.items() if j['kind'] == 'final'} == {final},
            'complete native plan must contain its fixed final theorem module')
    require({n for n, j in jobs.items() if j['kind'] == 'audit'} == {audit},
            'complete native plan must contain its fixed final audit module')
    require({n for n, j in jobs.items() if j['kind'] == 'relations'} == blocks,
            'complete native plan must contain every original relation block')
    require(set(jobs[final]['dependencies']) == blocks,
            'final theorem must depend on every original relation block')
    require(final in jobs[audit]['dependencies'], 'final audit must import the final theorem')
    require(selected_jobs(jobs, [audit]) == set(jobs),
            'every planned module must be in the final audit dependency closure')
    package = Path(__file__).resolve().parent
    root = Path(manifest['source_root'])
    command = [sys.executable, str(package / generator_name), '--root', str(root),
               '--output-dir', str(output), '--witness',
               str(output / manifest['auxiliary_witness']['path']), '--check']
    if family == 'CWToCeta':
        shared = manifest.get('shared_source_root')
        require(isinstance(shared, str) and shared, 'missing shared Ceta source identity')
        command += ['--shared-ceta', shared]
    log = output / 'logs/complete-plan-check.log'
    with log.open('w') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    require(result.returncode == 0,
            'independent complete native plan reconstruction failed: ' + str(log))
    return {'schema': schema, 'final': final, 'audit': audit,
            'source_blocks': block_count, 'all_relation_count': relation_count,
            'generator': str(package / generator_name)}

def job_keys(jobs, external_key, input_key):
    keys = {}
    active = set()
    def key(name):
        if name in keys:
            return keys[name]
        require(name not in active, 'cycle in build graph')
        active.add(name)
        job = jobs[name]
        keys[name] = fingerprint({'schema': SCHEMA, 'source': job['sha256'],
            'dependencies': [(d, key(d)) for d in job['dependencies']],
            'external_closure': external_key, 'fixed_inputs': input_key})
        active.remove(name)
        return keys[name]
    for name in jobs:
        key(name)
    return keys

def reusable(receipt, key, target):
    return (receipt.get('schema') == SCHEMA and receipt.get('key') == key and
            receipt.get('exit_code') == 0 and target.is_file() and
            not target.is_symlink() and receipt.get('olean_sha256') == digest(target))

def compile_job(name, job, key, lean, env, root, output, source_root, dependency_hashes,
                runtime_hashes, fixed_library_hashes, library, external):
    target = output / 'build/lib/lean' / module_path(name, '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    partial = target.with_suffix('.pending.olean')
    if partial.exists():
        partial.unlink()
    log = output / 'logs' / (name + '.log')
    start = time.monotonic()
    source = source_root / module_path(name, '.lean')
    actual_inputs = {str(source): job['sha256'], **dependency_hashes, **runtime_hashes,
                     **fixed_library_hashes}
    for dep in dependency_hashes:
        verify_owned_family(Path(dep))
    verify_resolution(output / 'build/lib/lean', library, external)
    verify_files(actual_inputs)
    command = [str(lean), '--root=' + str(source_root), '-o', str(partial), str(source)]
    peak = 0
    with log.open('w') as stream:
        p = subprocess.Popen(command, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
        atomic(output / 'running' / (name + '.json'), {'pid': p.pid, 'module': name,
            'started_at': time.time(), 'log': str(log), 'command': command})
        while p.poll() is None:
            try:
                for line in Path(f'/proc/{p.pid}/status').read_text().splitlines():
                    if line.startswith('VmRSS:'):
                        peak = max(peak, int(line.split()[1]))
            except FileNotFoundError:
                pass
            time.sleep(0.5)
        elapsed = time.monotonic() - start
        stream.write(f'\nEXIT={p.returncode} ELAPSED={elapsed:.2f} PEAK_RSS_KB={peak}\n')
    (output / 'running' / (name + '.json')).unlink(missing_ok=True)
    result = {'schema': SCHEMA, 'module': name, 'key': key, 'exit_code': p.returncode,
              'elapsed_seconds': elapsed, 'peak_rss_kb': peak, 'log': str(log),
              'finished_at': time.time(), 'source_sha256': job['sha256']}
    if p.returncode == 0:
        require(partial.is_file(), 'Lean succeeded without output: ' + name)
        # Read-only permissions alone do not prevent the owner replacing a file.
        # Rehash the entire actual frozen library, this job's source, generated
        # dependencies and compiler runtime before publishing a reusable receipt.
        verify_files(actual_inputs)
        verify_resolution(output / 'build/lib/lean', library, external)
        for dep in dependency_hashes:
            verify_owned_family(Path(dep))
        partial.chmod(0o444)
        partial.replace(target)
        result['olean_sha256'] = digest(target)
        result['fixed_source_root'] = str(source_root)
        result['actual_input_fingerprint'] = fingerprint(actual_inputs)
        result['actual_input_file_count'] = len(actual_inputs)
        result['generated_dependency_hashes'] = dependency_hashes
        atomic(output / 'receipts' / (name + '.json'), result)
    else:
        partial.unlink(missing_ok=True)
    return result

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', type=Path, required=True)
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--target', action='append', default=[])
    ap.add_argument('--status', action='store_true')
    args = ap.parse_args()
    output = args.output_dir.resolve()
    if args.status:
        prior = json.loads((output / 'status.json').read_text())
        current = digest(output / 'manifest.json')
        print(json.dumps({'historical_run': prior, 'current_manifest_sha256': current,
            'matches_current_manifest': current == prior.get('manifest_sha256'),
            'note': 'A completed result certifies its recorded fixed snapshot; this command does not rerun Lean.'}, sort_keys=True))
        return
    require(1 <= args.jobs <= 4, 'jobs must be between 1 and 4')
    with (output / 'runner.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return run_locked(args, output)

def run_locked(args, output):
    manifest_hash = digest(output / 'manifest.json')
    atomic(output / 'status.json', {'schema': SCHEMA, 'phase': 'checking',
        'runner_pid': os.getpid(), 'updated_at': time.time(), 'manifest_sha256': manifest_hash,
        'complete_native_quotient_map_certified': False,
        'actual_spectrum_map_comparison_certified': False})
    manifest = json.loads((output / 'manifest.json').read_text())
    root = Path(manifest['source_root'])
    jobs = {j['module']: j for j in manifest['jobs']}
    require(len(jobs) == len(manifest['jobs']), 'duplicate modules')
    clean_owned_partials(output, jobs)
    for name, job in jobs.items():
        require(digest(output / job['source']) == job['sha256'], 'generated source drift: ' + name)
        require(set(job['dependencies']) == set(job['imports']) & set(jobs), 'dependency graph drift')
    inputs = {str(root / p): h for p, h in manifest['pinned_source_hashes'].items()}
    w = manifest['auxiliary_witness']
    inputs[str(output / w['path'])] = w['sha256']
    if 'generation_inputs' in manifest:
        for p, h in manifest['generation_inputs'].items():
            path = Path(p) if Path(p).is_absolute() else root / p
            inputs[str(path)] = h
    else:  # Compatibility with the reviewed original Ceta run.
        inputs[str(output / 'generate.py')] = manifest['generator_sha256']
        inputs[str(output / 'templates/Support.lean')] = manifest['support_template_sha256']
    inputs[str(Path(__file__).resolve())] = digest(Path(__file__).resolve())
    verify_files(inputs)
    selected = selected_jobs(jobs, args.target)
    (output / 'logs').mkdir(exist_ok=True)
    print('Independently reconstructing the complete fixed native plan', flush=True)
    complete_plan = validate_complete_plan(output, manifest, jobs)
    print('Refreshing only direct external mathematical imports (serial Lake preflight)', flush=True)
    freshness = refresh_external(root, jobs, output)
    atomic(output / 'freshness.json', freshness)
    lean, paths, env = environment(root, output)
    print('Fingerprinting transitive external Lean dependencies', flush=True)
    external = external_snapshot(root, lean, paths, jobs)
    atomic(output / 'external-dependencies.json', external)
    print('Freezing byte-verified external objects and generated sources', flush=True)
    library, source_root, frozen = freeze_inputs(output, external, jobs)
    atomic(output / 'fixed-inputs.json', {'external_key': fingerprint(external),
        'source_root': str(source_root), 'library': str(library), 'files': frozen})
    overlay = bind_overlay(output, jobs, external, library)
    verify_files(inputs)
    env['LEAN_PATH'] = str(overlay) + ':' + str(library)
    runtime = {p: h for p, h in external['files'].items()
               if p == str(lean) or p.endswith('.so')}
    fixed_library_hashes = {p: h for p, h in frozen.items()
                            if Path(p).is_relative_to(library)}
    keys = job_keys(jobs, fingerprint(external), fingerprint(inputs))
    for part in ['logs', 'receipts', 'running']:
        (output / part).mkdir(exist_ok=True)
    done, failures, pending = set(), [], set(selected)
    start = time.time()
    # These generated sources are legacy non-module Lean files. Their only
    # output is .olean; stale IR/private/server sidecars are never inputs.
    for name in jobs:
        target = output / 'build/lib/lean' / module_path(name, '.olean')
        for artifact in module_artifacts(target):
            if artifact != target:
                artifact.unlink()
    for name in jobs:  # Generator writes topological order.
        if name not in pending or not set(jobs[name]['dependencies']) <= done:
            continue
        rp = output / 'receipts' / (name + '.json')
        target = output / 'build/lib/lean' / module_path(name, '.olean')
        if rp.is_file() and reusable(json.loads(rp.read_text()), keys[name], target):
            done.add(name)
            pending.remove(name)
    resumed = len(done)
    # Stale owned artifacts never stand in for a dependency which has not earned
    # a valid receipt in this run's exact input graph.
    for name in selected - done:
        target = output / 'build/lib/lean' / module_path(name, '.olean')
        target.unlink(missing_ok=True)
    print(f'Validated {resumed} reusable modules; {len(pending)} selected modules remain', flush=True)
    active = {}
    def status(phase):
        atomic(output / 'status.json', {'schema': SCHEMA, 'phase': phase,
            'runner_pid': os.getpid(), 'started_at': start, 'updated_at': time.time(),
            'manifest_sha256': manifest_hash, 'external_key': fingerprint(external),
            'fixed_source_root': str(source_root), 'fixed_library': str(library),
            'selected': len(selected), 'total_modules': len(jobs), 'resumed': resumed,
            'success': len(done), 'pending': len(pending), 'running': list(active.values()),
            'failed': failures, 'full_plan': selected == set(jobs),
            'validated_complete_plan': complete_plan,
            'complete_native_quotient_map_certified': phase == 'complete' and selected == set(jobs)
                and {complete_plan['final'], complete_plan['audit']} <= done,
            'actual_spectrum_map_comparison_certified': False})
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or active:
            if not failures:
                ready = [n for n in jobs if n in pending and set(jobs[n]['dependencies']) <= done]
                # Close source blocks as soon as their authentic ring bridges exist.
                # This changes scheduling only; the final target always selects all.
                priority = {'support': 0, 'data': 0, 'images': 0, 'audit': 1,
                            'final': 1, 'relations': 2, 'sphere_relations': 3,
                            'sphere_chunk': 4, 'module_relations': 3}
                ready.sort(key=lambda n: priority.get(jobs[n]['kind'], 5))
                for name in ready[:args.jobs - len(active)]:
                    require(digest(output / jobs[name]['source']) == jobs[name]['sha256'],
                            'source changed before compilation: ' + name)
                    dep_hashes = {}
                    ancestors = selected_jobs(jobs, jobs[name]['dependencies']) if jobs[name]['dependencies'] else set()
                    for dep in ancestors:
                        receipt = json.loads((output / 'receipts' / (dep + '.json')).read_text())
                        obj = output / 'build/lib/lean' / module_path(dep, '.olean')
                        require(not obj.is_symlink(), 'generated dependency became symlink: ' + dep)
                        dep_hashes[str(obj)] = receipt['olean_sha256']
                    f = pool.submit(compile_job, name, jobs[name], keys[name], lean, env,
                        root, output, source_root, dep_hashes, runtime, fixed_library_hashes,
                        library, external)
                    active[f] = name
                    pending.remove(name)
            status('running' if not failures else 'failed')
            if not active:
                require(bool(failures) or not pending, 'dependency graph is stuck')
                break
            finished, _ = concurrent.futures.wait(active, timeout=10,
                return_when=concurrent.futures.FIRST_COMPLETED)
            for f in finished:
                name = active.pop(f)
                try:
                    result = f.result()
                except Exception as e:
                    result = {'module': name, 'exit_code': -1, 'error': repr(e)}
                with (output / 'progress.jsonl').open('ab') as stream:
                    stream.write(encoded(result))
                print(json.dumps(result, sort_keys=True), flush=True)
                if result['exit_code'] == 0:
                    done.add(name)
                else:
                    failures.append(result)
            if failures and not active:
                break
    if not failures and not pending:
        verify_files(inputs)
        verify_files(frozen)
        require(digest(output / 'manifest.json') == manifest_hash,
                'manifest changed during replay')
        require(validate_complete_plan(output, manifest, jobs) == complete_plan,
                'complete native contract changed during replay')
        for name in selected:
            require(digest(output / jobs[name]['source']) == jobs[name]['sha256'],
                    'source changed after compilation: ' + name)
            target = output / 'build/lib/lean' / module_path(name, '.olean')
            verify_owned_family(target)
            receipt = json.loads((output / 'receipts' / (name + '.json')).read_text())
            require(reusable(receipt, keys[name], target), 'completed output/receipt changed: ' + name)
        status('complete')
        print('Selected replay complete; final status: ' + str(output / 'status.json'), flush=True)
    else:
        status('failed')
        raise SystemExit(1)

def entrypoint():
    try:
        main()
    except Exception as error:
        if '--output-dir' in sys.argv:
            output = Path(sys.argv[sys.argv.index('--output-dir') + 1]).resolve()
            path = output / 'status.json'
            if path.is_file():
                prior = json.loads(path.read_text())
                if prior.get('runner_pid') == os.getpid():
                    prior.update(phase='failed', updated_at=time.time(), error=repr(error),
                        complete_native_quotient_map_certified=False)
                    atomic(path, prior)
        raise

if __name__ == '__main__':
    entrypoint()
