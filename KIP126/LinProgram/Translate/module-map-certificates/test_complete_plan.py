#!/usr/bin/env python3
"""Reject self-declared complete plans before freshness or compilation.

Fixtures are deliberately not mathematical proofs. The empty-plan and lone
precheck cases exercise the real runner entry point that previously promoted
those plans. The complete-shaped toy plan must also survive independent source
reconstruction; topology and row counts alone are insufficient.
"""
import copy
from contextlib import redirect_stdout
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch


PACKAGE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('complete_plan_runner', PACKAGE / 'runner.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
BASE = 'KIP126.LinProgram.Certificates.ModuleMaps.CetaToSphere'


class CompletePlanBoundary(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.root = self.directory / 'repository'
        self.output = self.directory / 'output'
        self.root.mkdir()
        self.output.mkdir()
        (self.output / 'logs').mkdir()
        witness = self.output / 'witness.jsonl'
        witness.write_bytes(b'untrusted toy input')
        self.blocks = [BASE + f'.Relations{i:03d}' for i in range(150)]
        self.final, self.audit = BASE + '.Proofs', BASE + '.Checks'
        self.manifest = {
            'schema': 'lin-native-complete-ceta-certificate-build/v2-repository-support',
            'source_root': str(self.root), 'source_blocks': 150,
            'all_relation_count': 76569, 'generator_count': 887,
            'pinned_source_hashes': {}, 'generation_inputs': {},
            'auxiliary_witness': {'path': witness.name, 'sha256': runner.digest(witness)},
            'jobs': [self.job(n, 'relations', []) for n in self.blocks] + [
                self.job(self.final, 'final', self.blocks),
                self.job(self.audit, 'audit', [self.final]),
            ],
        }

    def tearDown(self):
        self.temporary.cleanup()

    def job(self, name, kind, dependencies):
        source = self.output / 'src' / runner.module_path(name, '.lean')
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(''.join(f'import {n}\n' for n in dependencies) +
                          'example : True := True.intro\n')
        return {'module': name, 'kind': kind, 'source': str(source.relative_to(self.output)),
                'sha256': runner.digest(source), 'imports': list(dependencies),
                'dependencies': list(dependencies)}

    def assert_entry_rejects(self, manifest):
        runner.atomic(self.output / 'manifest.json', manifest)
        runner.atomic(self.output / 'status.json', {
            'phase': 'complete', 'complete_native_quotient_map_certified': True,
        })
        with patch.object(sys, 'argv', ['runner', '--output-dir', str(self.output)]), \
                patch.object(runner, 'refresh_external') as freshness, \
                patch.object(runner, 'compile_job') as compile_job:
            with self.assertRaises(ValueError):
                runner.entrypoint()
        freshness.assert_not_called()
        compile_job.assert_not_called()
        state = json.loads((self.output / 'status.json').read_text())
        self.assertEqual(state['phase'], 'failed')
        self.assertFalse(state['complete_native_quotient_map_certified'])
        self.assertFalse(state['actual_spectrum_map_comparison_certified'])
        self.assertFalse((self.output / 'receipts').exists())

    def test_empty_plan_cannot_become_complete(self):
        self.manifest['jobs'] = []
        self.assert_entry_rejects(self.manifest)

    def test_one_genuine_trivial_precheck_cannot_become_complete(self):
        self.manifest['jobs'] = [self.job('OnlyPrecheck', 'audit', [])]
        self.assert_entry_rejects(self.manifest)

    def test_missing_final_or_audit_is_rejected(self):
        for missing in (self.final, self.audit):
            with self.subTest(missing=missing):
                manifest = copy.deepcopy(self.manifest)
                manifest['jobs'] = [j for j in manifest['jobs'] if j['module'] != missing]
                for job in manifest['jobs']:
                    job['imports'] = [n for n in job['imports'] if n != missing]
                    job['dependencies'] = [n for n in job['dependencies'] if n != missing]
                self.assert_entry_rejects(manifest)

    def test_missing_formal_zero_or_other_relation_block_is_rejected(self):
        manifest = copy.deepcopy(self.manifest)
        missing = self.blocks[0]
        manifest['jobs'] = [j for j in manifest['jobs'] if j['module'] != missing]
        for job in manifest['jobs']:
            job['imports'] = [n for n in job['imports'] if n != missing]
            job['dependencies'] = [n for n in job['dependencies'] if n != missing]
        self.assert_entry_rejects(manifest)

    def test_relabeled_kind_is_rejected(self):
        self.manifest['jobs'][0]['kind'] = 'data'
        self.assert_entry_rejects(self.manifest)

    def test_final_must_import_every_source_block(self):
        self.manifest['jobs'][-2]['imports'] = self.blocks[1:]
        self.manifest['jobs'][-2]['dependencies'] = self.blocks[1:]
        self.assert_entry_rejects(self.manifest)

    def test_audit_must_import_final(self):
        self.manifest['jobs'][-1]['imports'] = []
        self.manifest['jobs'][-1]['dependencies'] = []
        self.assert_entry_rejects(self.manifest)

    def test_disconnected_jobs_are_rejected(self):
        self.manifest['jobs'].append(self.job('UnrelatedProof', 'data', []))
        self.assert_entry_rejects(self.manifest)

    def test_schema_and_native_counts_are_fixed(self):
        for field, value in [('schema', 'unrecognized'), ('source_blocks', 149),
                             ('all_relation_count', 76568), ('generator_count', 886)]:
            with self.subTest(field=field):
                manifest = copy.deepcopy(self.manifest)
                manifest[field] = value
                self.assert_entry_rejects(manifest)

    def test_expected_topology_still_requires_independent_reconstruction(self):
        with patch.object(runner.subprocess, 'run', return_value=SimpleNamespace(returncode=1)) as run:
            self.assert_entry_rejects(self.manifest)
        command = run.call_args.args[0]
        self.assertEqual(command[1], str(PACKAGE / 'generate.py'))
        self.assertIn('--check', command)
        self.assertIn(str(self.root), command)

    def test_reconstruction_checker_is_selected_by_code_not_manifest(self):
        self.manifest['generator'] = '/bin/true'
        self.manifest['check_command'] = ['/bin/true']
        jobs = {j['module']: j for j in self.manifest['jobs']}
        with patch.object(runner.subprocess, 'run', return_value=SimpleNamespace(returncode=1)) as run:
            with self.assertRaisesRegex(ValueError, 'independent complete native plan'):
                runner.validate_complete_plan(self.output, self.manifest, jobs)
        self.assertEqual(run.call_args.args[0][1], str(PACKAGE / 'generate.py'))

    def exercise_mock_replay(self, targets):
        runner.atomic(self.output / 'manifest.json', self.manifest)
        # Only temporary fixture outputs are simulated. These are not Lean
        # receipts and can never be imported into a production run.
        def compile_fixture(name, job, key, lean, env, root, output, *unused):
            target = output / 'build/lib/lean' / runner.module_path(name, '.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(b'unit-test fixture, not a Lean artifact')
            receipt = {'schema': runner.SCHEMA, 'module': name, 'key': key,
                       'exit_code': 0, 'olean_sha256': runner.digest(target)}
            runner.atomic(output / 'receipts' / (name + '.json'), receipt)
            return receipt
        args = ['runner', '--output-dir', str(self.output)]
        for target in targets:
            args += ['--target', target]
        with patch.object(sys, 'argv', args), \
                patch.object(runner.subprocess, 'run', return_value=SimpleNamespace(returncode=0)) as rebuild, \
                patch.object(runner, 'refresh_external', return_value={}), \
                patch.object(runner, 'environment', return_value=(Path('/bin/true'), [], {})), \
                patch.object(runner, 'external_snapshot', return_value={'modules': {}, 'files': {}}), \
                patch.object(runner, 'compile_job', side_effect=compile_fixture), \
                redirect_stdout(io.StringIO()):
            runner.entrypoint()
        self.assertEqual(rebuild.call_count, 2)
        return json.loads((self.output / 'status.json').read_text())

    def test_full_contract_mock_requires_final_and_audit_receipts(self):
        state = self.exercise_mock_replay([])
        self.assertEqual(state['phase'], 'complete')
        self.assertTrue(state['complete_native_quotient_map_certified'])
        self.assertEqual(state['success'], 152)
        for name in (self.final, self.audit):
            self.assertTrue((self.output / 'receipts' / (name + '.json')).is_file())
        self.assertFalse(state['actual_spectrum_map_comparison_certified'])

    def test_valid_full_contract_with_subset_target_stays_uncertified(self):
        state = self.exercise_mock_replay([self.blocks[0]])
        self.assertEqual(state['phase'], 'complete')
        self.assertEqual(state['success'], 1)
        self.assertFalse(state['full_plan'])
        self.assertFalse(state['complete_native_quotient_map_certified'])
        self.assertFalse(state['actual_spectrum_map_comparison_certified'])


if __name__ == '__main__':
    unittest.main()
