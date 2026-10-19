#!/usr/bin/env python3
"""Rebuild supplemental augmentation certificates for the original 96 native rows.

The full input package is verified by its pinned producer in read-only --check
mode. This separate producer never edits the core package, never substitutes
zero for a missing/NULL database field, and never claims composition or actual
Adams d2 certification. Generated Lean still requires kernel checking.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lean_module import lean_module

sys.dont_write_bytecode = True
SEMANTIC = '088958541d91f6a987c825ab94a3266001cf94e6eccdf19757ac9b39d92c69fa'
CORE_GENERATOR_SHA = '5965d2e47562f56f491c6f82be97fbb01788ad87bebfd1d64bfa07ea33e1b0ae'
DATABASES = {
    'S0_Adams_res.db': '808235c2575ca647100975c5bab4a577bd0aa2c718dbbf1521ff60e1ddc3b1ba',
    'S0_Adams_d2.db': 'b97e88747fbbd348961282afd46780a05062d9501c98d6def79efed79176570b',
}
BASE_IDS = (0, 524288)
NONZERO = {1572869: [4], 1572875: [5], 2097163: [11], 2621452: [13],
           3145733: [5], 3145734: [6], 3670020: [7], 4194320: [16]}
CORE_MODULE = 'KIP126.LinProgram.Certificates.Secondary.Seed5487.FullInput'
MODULE = 'KIP126.LinProgram.Certificates.Secondary.Seed5487.Augmentation'
NAMESPACE = 'KIP126.Computation.Secondary.Seed5487.Full.Augmentation'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def nat_list(values):
    return '[' + ','.join(map(str, values)) + ']'


def parse_record(value):
    require(isinstance(value, str), 'NULL/non-text d2_h is not a recorded zero')
    if value == '':
        return []
    require(re.fullmatch(r'(0|[1-9][0-9]*)(,(0|[1-9][0-9]*))*', value),
            'd2_h must be an exact comma-separated natural-number list')
    return [int(v) for v in value.split(',')]


def validate_records(rows, records):
    """Do not normalize, sort, cancel, or otherwise change the recorded lists."""
    absent, result = [], []
    for row in rows:
        rid = row['id']
        actual = [t['v'] for t in row['f'] if t['sq'] == [0] * 8]
        if rid not in records:
            absent.append(rid)
            require(rid in BASE_IDS and row['f'] == [],
                    'missing d2_h record is not an explicit base definition')
            result.append({'id': rid, 'status': 'unrecorded-explicit-base',
                           'recorded': None, 'raw_d2_h': None,
                           'base_definition': 'initialLift' + str(rid),
                           'base_augmentation': []})
        else:
            recorded = parse_record(records[rid])
            require(actual == recorded, 'native lift augmentation differs at row ' + str(rid))
            result.append({'id': rid, 'status': 'recorded', 'recorded': recorded,
                           'raw_d2_h': records[rid]})
    require(tuple(absent) == BASE_IDS, 'the two unrecorded base identities changed')
    require(sum(r['status'] == 'recorded' for r in result) == 94, 'not all 94 records retained')
    require({r['id']: r['recorded'] for r in result if r['recorded']} == NONZERO,
            'the complete eight nonzero recorded lists changed')
    return result


def render(records):
    files, jobs = {}, []
    prefix = ['', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '',
              'namespace ' + NAMESPACE, 'open MilnorCertificates', '']
    def emit(suffix, lines, kind):
        module = MODULE + '.' + suffix
        path = 'src/' + module.replace('.', '/') + '.lean'
        content = lean_module('\n'.join(lines) + '\n').encode()
        files[path] = content
        imports = [line[7:] for line in lines if line.startswith('import ')]
        jobs.append({'module': module, 'source': path, 'sha256': sha(content), 'kind': kind,
                     'imports': imports, 'dependencies': [x for x in imports if x.startswith(MODULE + '.')],
                     'original_ids': [r['id'] for r in records]})
    lines = ['import ' + CORE_MODULE, 'import KIP126.LinProgram.Certificates.Secondary.Augmentation'] + prefix
    lines += ['/-- Exactly the 94 physically present database records; empty lists are recorded zeros.',
              'The missing base records are deliberately absent. -/',
              'def augmentationRecords : List (Nat × List Nat) := [']
    present = [r for r in records if r['status'] == 'recorded']
    lines += ['  (' + str(r['id']) + ',' + nat_list(r['recorded']) + ')' +
              (',' if i + 1 < len(present) else '') for i, r in enumerate(present)]
    lines += [']', '',
              'def recordedAugmentation (id : Nat) : Option (List Nat) :=',
              '  (augmentationRecords.find? (fun entry => entry.1 == id)).map (·.2)', '',
              '/-- Unrecorded rows retain their precise base identity and initial lift definition. -/',
              'def IsExplicitBase (row : NativeRow) : Prop :=',
              '  (row.id = 0 ∧ row.f = initialLift0) ∨',
              '  (row.id = 524288 ∧ row.f = initialLift524288)', '',
              '/-- The recorded list is checked exactly; absence is a separate, explicit base case. -/',
              'def RowAugmentationCertified (row : NativeRow) : Prop :=',
              '  match recordedAugmentation row.id with',
              '  | some recorded => augmentationTerms 8 row.f = recorded',
              '  | none => IsExplicitBase row ∧ augmentationTerms 8 row.f = []', '',
              'end ' + NAMESPACE]
    emit('Data', lines, 'augmentation_data')
    lines = ['import ' + MODULE + '.Data'] + prefix
    for r in records:
        row = 'row' + str(r['id'])
        values = r['recorded'] if r['status'] == 'recorded' else []
        option = 'some ' + nat_list(values) if r['status'] == 'recorded' else 'none'
        lines += [f'theorem {row}_record : recordedAugmentation {row}.id = {option} := by',
                  '  decide +kernel', '',
                  f'theorem {row}_augmentation : augmentationTerms 8 {row}.f = {nat_list(values)} := by',
                  '  decide +kernel', '',
                  f'theorem {row}_augmentation_certified : RowAugmentationCertified {row} := by',
                  f'  rw [RowAugmentationCertified, {row}_record]']
        if r['status'] == 'recorded':
            lines += [f'  exact {row}_augmentation', '']
        else:
            side = 'Or.inl' if r['id'] == 0 else 'Or.inr'
            lines += [f'  exact ⟨{side} ⟨rfl, rfl⟩, {row}_augmentation⟩', '']
    lines += ['theorem allNativeRows_augmentation_certified :',
              '    ∀ row ∈ nativeRows, RowAugmentationCertified row := by',
              '  intro row h',
              '  simp only [nativeRows, List.mem_cons, List.not_mem_nil, or_false] at h',
              '  rcases h with ' + ' | '.join('h' for _ in records)]
    lines += [f"  · subst row; exact row{r['id']}_augmentation_certified" for r in records]
    lines += ['', 'theorem allNativeRows_recorded_augmentation (row : NativeRow)',
              '    (h : row ∈ nativeRows) (recorded : List Nat)',
              '    (hr : recordedAugmentation row.id = some recorded) :',
              '    augmentationTerms 8 row.f = recorded := by',
              '  simpa only [RowAugmentationCertified, hr] using allNativeRows_augmentation_certified row h', '',
              'theorem allNativeRows_recorded_coefficient (row : NativeRow)',
              '    (h : row ∈ nativeRows) (recorded : List Nat)',
              '    (hr : recordedAugmentation row.id = some recorded) (target : Nat) :',
              '    expressionCoefficient row.f target (unitMonomial 8) =',
              '      augmentationCoefficient recorded target :=',
              '  augmentation_eq_of_terms 8 row.f recorded',
              '    (allNativeRows_recorded_augmentation row h recorded hr) target', '',
              'theorem allNativeRows_unrecorded_base (row : NativeRow)',
              '    (h : row ∈ nativeRows) (hr : recordedAugmentation row.id = none) :',
              '    IsExplicitBase row ∧ augmentationTerms 8 row.f = [] := by',
              '  simpa only [RowAugmentationCertified, hr] using allNativeRows_augmentation_certified row h', '',
              'theorem allNativeRows_unrecorded_coefficient (row : NativeRow)',
              '    (h : row ∈ nativeRows) (hr : recordedAugmentation row.id = none) (target : Nat) :',
              '    IsExplicitBase row ∧ expressionCoefficient row.f target (unitMonomial 8) = false := by',
              '  obtain ⟨hb, ha⟩ := allNativeRows_unrecorded_base row h hr',
              '  refine ⟨hb, ?_⟩',
              '  simpa [augmentationCoefficient] using augmentation_eq_of_terms 8 row.f [] ha target', '',
              'end ' + NAMESPACE]
    emit('Proofs', lines, 'all_original_augmentations')
    names = ['allNativeRows_augmentation_certified', 'allNativeRows_recorded_augmentation',
             'allNativeRows_recorded_coefficient', 'allNativeRows_unrecorded_base',
             'allNativeRows_unrecorded_coefficient']
    lines = ['import ' + MODULE + '.Proofs', 'import Lean.Elab.Command', '',
             'open Lean Elab Command in', 'run_cmd do', '  let env ← getEnv',
             '  for mod in env.allImportedModuleNames do',
             '    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||',
             '        (`KIP126.Def).isPrefixOf mod then',
             '      throwError "augmentation certificate imported an actual-model dependency: {mod}"',
             '  for name in [' + ', '.join('`' + NAMESPACE + '.' + n for n in names) + '] do',
             '    for ax in (← Lean.collectAxioms name) do',
             '      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do',
             '        throwError "unexpected augmentation axiom: {name}: {ax}"'] + prefix
    lines += ['example : nativeRows.map (·.id) = ' + nat_list([r['id'] for r in records]) + ' := by decide',
              'example : nativeRows.length = 96 := by decide',
              'example : augmentationRecords.length = 94 := by decide',
              'example : (nativeRows.filter (fun row => (recordedAugmentation row.id).isNone)).map (·.id) =',
              '    [0, 524288] := by decide +kernel', '', 'end ' + NAMESPACE]
    lines += ['#print axioms ' + NAMESPACE + '.' + n for n in names]
    emit('Checks', lines, 'augmentation_axiom_audit')
    return files, jobs



def reject_symlink_ancestors(path):
    """Check lexical ancestors before resolve can hide an output-path symlink."""
    for candidate in (path, *path.parents):
        require(not candidate.is_symlink(), 'symlink in generated output path: ' + str(candidate))


def validate_output_paths(output, names):
    """Preflight every generated target before writing any member of the package.

    Unrelated build overlays are not outputs of this producer and may retain
    their own symlinks. Only generated files and their full ancestor paths are
    required to be unaliased directories/regular files.
    """
    reject_symlink_ancestors(output)
    require(not output.exists() or output.is_dir(), 'output root is not a directory')
    for name in names:
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts,
                'generated output must be a relative child: ' + name)
        target = output / relative
        reject_symlink_ancestors(target)
        require(not target.exists() or target.is_file(),
                'generated output target is not a regular file: ' + str(target))
        for parent in target.parents:
            require(not parent.exists() or parent.is_dir(),
                    'generated output ancestor is not a directory: ' + str(parent))


def write_output_atomic(output, name, data):
    """Replace the directory entry, never mutate an existing file's hardlinks."""
    target = output / name
    target.parent.mkdir(parents=True, exist_ok=True)
    validate_output_paths(output, [name])
    fd, temporary_name = tempfile.mkstemp(prefix='.' + target.name + '.',
                                         suffix='.tmp', dir=target.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(data)
        validate_output_paths(output, [name])
        os.replace(temporary, target)
    finally:
        temporary.unlink(missing_ok=True)


def run(args):
    reject_symlink_ancestors(args.output_dir.absolute())
    root, core, output = args.root.resolve(), args.full_input_dir.resolve(), args.output_dir.resolve()
    require(core != output and core not in output.parents and output not in core.parents,
            'supplemental output must be disjoint from the full input package')
    generator = root / 'KIP126/LinProgram/Translate/secondary-seed5487-certificates/generate.py'
    require(sha(generator.read_bytes()) == CORE_GENERATOR_SHA, 'pinned core generator drift')
    dbdir = root / 'KIP126/LinProgram/Raw/Secondary/Seed5487'
    paths = {name: dbdir / name for name in DATABASES}
    if args.resolution_db:
        paths['S0_Adams_res.db'] = args.resolution_db.resolve()
    if args.secondary_db:
        paths['S0_Adams_d2.db'] = args.secondary_db.resolve()
    for name, digest in DATABASES.items():
        require(sha(paths[name].read_bytes()) == digest, 'original database drift: ' + name)
    raw_witness = (core / 'witness.json').read_bytes()
    rows = json.loads(raw_witness)['generators']
    require(len(rows) == 96 and sha(canonical(rows)) == SEMANTIC, 'wrong complete native closure')
    raw_manifest = (core / 'manifest.json').read_bytes()
    full_manifest = json.loads(raw_manifest)
    require(full_manifest['schema'] == 'seed5487-complete-native-certification-sources/v1', 'wrong core schema')
    require(full_manifest['auxiliary_witness'] == {'path': 'witness.json', 'sha256': sha(raw_witness)},
            'core witness identity mismatch')
    full_jobs = [j for j in full_manifest['jobs'] if j['module'] == CORE_MODULE]
    require(len(full_jobs) == 1, 'FullInput must occur exactly once in the core plan')
    full_job = full_jobs[0]
    full_source = core / full_job['source']
    require(sha(full_source.read_bytes()) == full_job['sha256'], 'FullInput source drift')
    support = root / 'KIP126/LinProgram/Certificates/Secondary/Augmentation.lean'
    tracked = [generator, Path(__file__).resolve(), root / 'KIP126/LinProgram/Translate/lean_module.py', support, core / 'witness.json',
               core / 'manifest.json', full_source, *paths.values()]
    input_hashes = {str(p): sha(p.read_bytes()) for p in tracked}
    connection = sqlite3.connect('file:' + str(paths['S0_Adams_d2.db']) + '?mode=ro', uri=True)
    try:
        records = dict(connection.execute('SELECT id,d2_h FROM S0_Adams_d2'))
    finally:
        connection.close()
    values = validate_records(rows, records)
    subprocess.run([sys.executable, str(generator), '--root', str(root), '--witness', str(core / 'witness.json'),
                    '--output-dir', str(core), '--resolution-db', str(paths['S0_Adams_res.db']),
                    '--secondary-db', str(paths['S0_Adams_d2.db']), '--check'], check=True)
    files, jobs = render(values)
    files['records.json'] = canonical(values)
    manifest = {'schema': 'seed5487-native-augmentation-sources/v1', 'source_root': str(root),
                'full_input_dir': str(core), 'full_input_manifest_sha256': sha(raw_manifest),
                'full_input_module': CORE_MODULE, 'full_input_source_sha256': full_job['sha256'],
                'native_rows_semantic_sha256': SEMANTIC, 'source_input_hashes': input_hashes,
                'source_databases': {n: {'path': str(paths[n]), 'sha256': h} for n, h in DATABASES.items()},
                'recorded_rows': 94, 'explicit_unrecorded_base_ids': list(BASE_IDS),
                'native_row_ids': [r['id'] for r in rows], 'nonzero_recorded': NONZERO,
                'jobs': jobs, 'files': {name: sha(data) for name, data in files.items()},
                'augmentation_kernel_certified': False,
                'full_native_96_composition_certified': False,
                'secondary_associator_certified': False, 'actual_d2_certified': False,
                'missing_record_policy': 'reject except the two explicit unrecorded base definitions',
                'null_field_policy': 'reject; only present empty text denotes a recorded zero'}
    files['manifest.json'] = canonical(manifest)
    require(input_hashes == {str(p): sha(p.read_bytes()) for p in tracked}, 'input changed during generation')
    validate_output_paths(output, files)
    if args.check:
        for name, data in files.items():
            require((output / name).is_file() and (output / name).read_bytes() == data,
                    'supplemental replay mismatch: ' + name)
        actual = {str(p.relative_to(output)) for p in (output / 'src').rglob('*.lean')}
        require(actual == {p for p in files if p.endswith('.lean')}, 'extra or missing supplemental Lean source')
    else:
        require(not (output / 'src').exists() or
                {str(p.relative_to(output)) for p in (output / 'src').rglob('*.lean')} <= set(files),
                'unexpected existing supplemental sources')
        for name, data in files.items():
            write_output_atomic(output, name, data)
    print(json.dumps({'checked': args.check, 'modules': len(jobs), 'native_rows': 96,
                      'recorded': 94, 'explicit_unrecorded_bases': list(BASE_IDS),
                      'nonzero_recorded': len(NONZERO), 'lean_bytes': sum(len(v) for k, v in files.items() if k.endswith('.lean')),
                      'augmentation_kernel_certified': False, 'actual_d2_certified': False}, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--full-input-dir', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--resolution-db', type=Path)
    parser.add_argument('--secondary-db', type=Path)
    parser.add_argument('--check', action='store_true')
    run(parser.parse_args())


if __name__ == '__main__':
    main()
