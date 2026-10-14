#!/usr/bin/env python3
"""Fail-closed regression tests for the fixed complete secondary replay adapter.

The 328-module fixture has the real cardinalities and dependency shape, but toy
sources and a mocked generator/compiler. It tests orchestration and receipts,
not mathematics. No test invokes Lake, Lean, or the native source databases.
Set SECONDARY_RUNNER_ENGINE to test a relocated draft against the pinned engine.
"""
from contextlib import ExitStack, redirect_stdout
import copy
import fcntl
import importlib.util
import io
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

PACKAGE = Path(__file__).resolve().parent
ADAPTER_PATH = PACKAGE / 'replay.py'
if not ADAPTER_PATH.is_file():
    ADAPTER_PATH = PACKAGE / 'run-secondary-seed5487-complete.py'
ENGINE_PATH = Path(os.environ.get('SECONDARY_RUNNER_ENGINE',
                                 str(PACKAGE.parent / 'module-map-certificates/runner.py')))


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


adapter = load_module('secondary_adapter_test', ADAPTER_PATH)


class CompleteFixture(unittest.TestCase):
    def setUp(self):
        self.engine = load_module('fixed_engine_test', ENGINE_PATH)
        self.assertEqual(self.engine.digest(ENGINE_PATH), adapter.ENGINE_SHA)
        temporary = tempfile.TemporaryDirectory(prefix='secondary-adapter-test-')
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.root = self.directory / 'repository'
        self.output = self.directory / 'output'
        self.package = self.directory / 'secondary-certificates'
        for path in (self.root, self.output / 'logs', self.package):
            path.mkdir(parents=True)
        for name in ('generate.py', 'replay.py'):
            (self.package / name).write_text('# deliberately non-executable fixture\n')
        (self.output / 'witness.json').write_text('untrusted fixture witness')
        self.row_ids = [(i // 8 << 19) + i % 8 for i in range(96)]
        self.degrees = [d for d in range(1, 41) if d != 38]
        self.jobs = {}
        self.input = adapter.BASE + '.FullInput'
        self.products = adapter.BASE + '.Full.Products'
        self.plans = adapter.BASE + '.Full.Plans'
        self.spec = adapter.BASE + '.Full.CompositionSpec'
        self.blocks = [adapter.BASE + f'.Full.Compositions{i:03d}' for i in range(12)]
        self.table_names = []
        self.product_names = []
        self.add_job(self.input, 'full_native_input', [], self.row_ids)
        next_product = 0
        for degree_index, degree in enumerate(self.degrees):
            table = adapter.BASE + f'.Full.Degree{degree:03d}'
            self.table_names.append(table)
            self.add_job(table, 'complete_original_rank_coproduct_table', [], [degree])
            for block in range(7 if degree_index < 37 else 6):
                name = adapter.BASE + f'.Full.ProductsD{degree:03d}B{block:03d}'
                remaining_blocks = 271 - len(self.product_names)
                count = (15839 - next_product + remaining_blocks - 1) // remaining_blocks
                ids = list(range(next_product, next_product + count))
                next_product += count
                self.product_names.append(name)
                self.add_job(name, 'original_product_certificates', [table], ids)
        self.assertEqual(next_product, 15839)
        self.add_job(self.products, 'full_certified_product_chunks', self.product_names,
                     list(range(15839)))
        self.add_job(self.plans, 'all_original_composition_plans', [], self.row_ids)
        self.add_job(self.spec, 'composition_spec', [self.input, self.products, self.plans], self.row_ids)
        for i, name in enumerate(self.blocks):
            self.add_job(name, 'complete_composition_rows', [self.spec], self.row_ids[i*8:(i+1)*8])
        self.add_job(adapter.FINAL, 'final', self.blocks, self.row_ids)
        self.add_job(adapter.AUDIT, 'audit', [adapter.FINAL], self.row_ids)
        self.assertEqual(len(self.jobs), 328)
        self.manifest = {
            'schema': 'seed5487-complete-native-certification-sources/v1',
            'source_root': str(self.root),
            'bindings': {'native_row_count': 96, 'rank': 8,
                         'native_rows_semantic_sha256': adapter.SEMANTIC},
            'complete_native_row_ids': self.row_ids,
            'complete_product_ids': list(range(15839)),
            'products_per_chunk': 64, 'direct_products': False,
            'pinned_source_hashes': {},
            'source_databases': {name: {'path': str(self.root / name), 'sha256': digest}
                                 for name, digest in adapter.DATABASES.items()},
            'generation_inputs': {str(self.package / name): self.engine.digest(self.package / name)
                                  for name in ('generate.py', 'replay.py')},
            'auxiliary_witness': {'path': 'witness.json',
                                  'sha256': self.engine.digest(self.output / 'witness.json')},
        }

    def add_job(self, name, kind, dependencies, ids):
        path = self.output / 'src' / self.engine.module_path(name, '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(''.join(f'import {n}\n' for n in dependencies) +
                        'example : True := True.intro\n')
        self.jobs[name] = {
            'module': name, 'source': str(path.relative_to(self.output)),
            'sha256': self.engine.digest(path), 'kind': kind, 'artifact_kind': kind,
            'imports': list(dependencies), 'dependencies': list(dependencies),
            'original_ids': list(ids),
        }

    def contract(self):
        return adapter.contract(self.engine, self.output, self.manifest, self.jobs, self.package)

    def reject(self, message):
        with patch.object(adapter.subprocess, 'run') as generator:
            with self.assertRaisesRegex(ValueError, message):
                self.contract()
            generator.assert_not_called()

    def disconnect(self, name):
        self.jobs.pop(name)
        for job in self.jobs.values():
            job['dependencies'] = [n for n in job['dependencies'] if n != name]
            job['imports'] = [n for n in job['imports'] if n != name]


class Contracts(CompleteFixture):
    def test_full_328_module_plan_requires_same_package_regeneration(self):
        with patch.object(adapter.subprocess, 'run', return_value=SimpleNamespace(returncode=0)) as gen:
            result = self.contract()
        self.assertEqual(result['native_rows'], 96)
        self.assertEqual(result['ordered_products'], 15839)
        self.assertEqual(result['final'], adapter.FINAL)
        self.assertEqual(result['audit'], adapter.AUDIT)
        command = gen.call_args.args[0]
        self.assertEqual(command, [sys.executable, str(self.package / 'generate.py'),
            '--root', str(self.root), '--output-dir', str(self.output),
            '--witness', str(self.output / 'witness.json'), '--check',
            '--resolution-db', str(self.root / 'S0_Adams_res.db'),
            '--secondary-db', str(self.root / 'S0_Adams_d2.db')])

    def test_empty_plan(self):
        self.jobs = {}
        self.reject('missing fixed full composition theorem or audit')

    def test_lone_precheck(self):
        self.jobs = {adapter.AUDIT: self.jobs[adapter.AUDIT]}
        self.reject('missing fixed full composition theorem or audit')

    def test_wrong_schema(self):
        self.manifest['schema'] = 'lin-native-complete-ceta-certificate-build/v2-repository-support'
        self.reject('unsupported complete secondary source schema')

    def test_fixed_input_bindings(self):
        for field, value in [('rank', 5), ('native_row_count', 95),
                             ('native_rows_semantic_sha256', 'wrong')]:
            with self.subTest(field=field):
                old = self.manifest['bindings'][field]
                self.manifest['bindings'][field] = value
                self.reject('wrong fixed native secondary input')
                self.manifest['bindings'][field] = old

    def test_omitted_and_duplicate_row_ids(self):
        for ids in (self.row_ids[:-1], self.row_ids[:-1] + [self.row_ids[0]]):
            self.manifest['complete_native_row_ids'] = ids
            self.reject('all 96 distinct native row IDs')

    def test_omitted_and_reordered_product_universe(self):
        for ids in (list(range(15838)), list(reversed(range(15839)))):
            self.manifest['complete_product_ids'] = ids
            self.reject('all 15839 original ordered products')

    def test_missing_final_or_audit(self):
        for name in (adapter.FINAL, adapter.AUDIT):
            job = self.jobs.pop(name)
            self.reject('missing fixed full composition theorem or audit')
            self.jobs[name] = job

    def test_final_must_depend_on_all_twelve_row_blocks(self):
        self.jobs[adapter.FINAL]['dependencies'].pop()
        self.reject('final theorem must use every complete eight-row block')

    def test_audit_must_consume_final(self):
        self.jobs[adapter.AUDIT]['dependencies'] = self.blocks
        self.reject('final audit must consume the full theorem')

    def test_disconnected_generated_module(self):
        self.add_job(adapter.BASE + '.Full.Unused', 'data', [], [])
        self.reject('every generated product and composition')

    def test_missing_original_row_with_unchanged_manifest(self):
        self.jobs[self.blocks[-1]]['original_ids'].pop()
        self.reject('composition blocks do not cover exactly all original rows')

    def test_duplicate_row_with_unchanged_manifest(self):
        self.jobs[self.blocks[-1]]['original_ids'][-1] = self.row_ids[0]
        self.reject('composition blocks do not cover exactly all original rows')

    def test_missing_or_duplicate_original_product(self):
        ids = self.jobs[self.product_names[-1]]['original_ids']
        last = ids.pop()
        self.reject('product blocks omit or duplicate an original product')
        ids.append(0)
        self.reject('product blocks omit or duplicate an original product')
        ids[-1] = last

    def test_reclassified_product_cannot_disappear(self):
        self.jobs[self.product_names[0]]['artifact_kind'] = 'precheck'
        self.reject('product blocks omit or duplicate an original product')

    def test_partial_table_family_rejected_even_if_reachable(self):
        self.disconnect(self.table_names[-1])
        self.reject('all 39 complete original-rank degree tables')

    def test_duplicate_table_degree(self):
        self.jobs[self.table_names[-1]]['original_ids'] = [1]
        self.reject('all 39 complete original-rank degree tables')

    def test_table_free_mode_is_not_this_contract(self):
        self.manifest['direct_products'] = True
        self.reject('requires the complete shared-table production plan')

    def test_changed_product_partition(self):
        self.manifest['products_per_chunk'] = 32
        self.reject('unsupported complete product partition')

    def test_fixed_databases_required(self):
        database = self.manifest['source_databases'].pop('S0_Adams_d2.db')
        self.reject('both fixed native databases')
        self.manifest['source_databases']['S0_Adams_d2.db'] = database
        database['sha256'] = 'wrong'
        self.reject('both original digests')

    def test_each_generation_tool_is_hash_pinned(self):
        for name in ('generate.py', 'replay.py'):
            with self.subTest(name=name):
                source = str(self.package / name)
                digest = self.manifest['generation_inputs'].pop(source)
                self.reject('missing or altered fixed replay tool')
                self.manifest['generation_inputs'][source] = digest

    def test_structurally_complete_plan_still_needs_successful_regeneration(self):
        with patch.object(adapter.subprocess, 'run', return_value=SimpleNamespace(returncode=1)):
            with self.assertRaisesRegex(ValueError, 'independent full source regeneration failed'):
                self.contract()

    def test_status_never_promotes_actual_d2_or_associator(self):
        for flag in (False, True):
            state = adapter.translate_status({'complete_native_quotient_map_certified': flag,
                'actual_spectrum_map_comparison_certified': True,
                'secondary_associator_certified': True, 'actual_d2_certified': True})
            self.assertIs(state['full_native_96_composition_certified'], flag)
            self.assertIs(state['secondary_associator_certified'], False)
            self.assertIs(state['actual_d2_certified'], False)
            self.assertNotIn('complete_native_quotient_map_certified', state)
            self.assertNotIn('actual_spectrum_map_comparison_certified', state)

    def test_receipts_are_not_rewritten(self):
        receipt = {'module': 'M', 'exit_code': 0, 'olean_sha256': 'abc'}
        self.assertIs(adapter.translate_status(receipt), receipt)

    def test_configuration_preserves_freezing_and_receipt_implementation(self):
        names = ['freeze_inputs', 'frozen_copy', 'compile_job', 'verify_files',
                 'reusable', 'verify_owned_family', 'selected_jobs', 'run_locked', 'entrypoint']
        before = {name: getattr(self.engine, name) for name in names}
        adapter.configure(self.engine, self.package)
        for name in names:
            self.assertIs(getattr(self.engine, name), before[name])


class ReplayBoundary(CompleteFixture):
    def setUp(self):
        super().setUp()
        adapter.configure(self.engine, self.package)
        self.manifest['jobs'] = list(self.jobs.values())
        self.engine.atomic(self.output / 'manifest.json', self.manifest)
        self.engine.atomic(self.output / 'status.json', {
            'phase': 'complete', 'full_native_96_composition_certified': True,
            'secondary_associator_certified': True, 'actual_d2_certified': True})
        self.compiled = []
        self.fail_module = None
        self.mutate_after = None

    def fake_process(self, command, **kwargs):
        source = Path(command[-1])
        name = next(n for n in self.jobs if str(source).endswith(str(self.engine.module_path(n, '.lean'))))
        self.compiled.append(name)
        target = Path(command[command.index('-o') + 1])
        target.write_bytes(('MOCK PROCESS OUTPUT, NOT A PROOF: ' + name).encode())
        if self.mutate_after:
            action, self.mutate_after = self.mutate_after, None
            action()
        code = 1 if name == self.fail_module else 0
        return SimpleNamespace(pid=os.getpid(), returncode=code, poll=lambda: code)

    def invoke(self, *extra, generator_codes=(0, 0)):
        with ExitStack() as stack:
            stack.enter_context(redirect_stdout(io.StringIO()))
            stack.enter_context(patch.object(sys, 'argv',
                ['replay', '--output-dir', str(self.output), '--jobs', '1', *extra]))
            gen = stack.enter_context(patch.object(adapter.subprocess, 'run',
                side_effect=[SimpleNamespace(returncode=n) for n in generator_codes]))
            stack.enter_context(patch.object(self.engine, 'refresh_external', return_value={'mock': True}))
            stack.enter_context(patch.object(self.engine, 'environment', return_value=(Path('/bin/false'), [], {})))
            stack.enter_context(patch.object(self.engine, 'external_snapshot',
                                            return_value={'files': {}, 'modules': {}}))
            stack.enter_context(patch.object(self.engine.subprocess, 'Popen', side_effect=self.fake_process))
            stack.enter_context(patch.object(self.engine.subprocess, 'check_output',
                                            side_effect=AssertionError('unexpected real environment probe')))
            self.engine.entrypoint()
            return gen.call_count

    def state(self):
        return json.loads((self.output / 'status.json').read_text())

    def assert_uncertified(self):
        state = self.state()
        self.assertIs(state['full_native_96_composition_certified'], False)
        self.assertIs(state['secondary_associator_certified'], False)
        self.assertIs(state['actual_d2_certified'], False)

    def test_full_run_and_exact_receipt_resume_require_both_reconstruction_checks(self):
        # Existing output without a receipt must not be adopted.
        target = self.output / 'build/lib/lean' / self.engine.module_path(self.input, '.olean')
        target.parent.mkdir(parents=True)
        target.write_bytes(b'unreceipted precheck output')
        self.assertEqual(self.invoke(), 2)
        self.assertEqual(set(self.compiled), set(self.jobs))
        state = self.state()
        self.assertEqual(state['phase'], 'complete')
        self.assertTrue(state['full_native_96_composition_certified'])
        self.assertFalse(state['secondary_associator_certified'])
        self.assertFalse(state['actual_d2_certified'])
        self.assertEqual(state['success'], 328)
        self.assertEqual(state['resumed'], 0)
        self.compiled.clear()
        self.assertEqual(self.invoke(), 2)
        self.assertEqual(self.compiled, [])
        self.assertEqual(self.state()['resumed'], 328)
        self.assertTrue(self.state()['full_native_96_composition_certified'])

    def test_final_theorem_without_audit_target_does_not_certify(self):
        self.assertEqual(self.invoke('--target', adapter.FINAL), 2)
        self.assertEqual(len(self.compiled), 327)
        self.assertNotIn(adapter.AUDIT, self.compiled)
        self.assertEqual(self.state()['phase'], 'complete')
        self.assert_uncertified()

    def test_one_table_target_remains_partial(self):
        self.invoke('--target', self.table_names[0])
        self.assertEqual(self.compiled, [self.table_names[0]])
        self.assert_uncertified()

    def test_failed_final_audit_cannot_certify(self):
        self.fail_module = adapter.AUDIT
        with self.assertRaises(SystemExit):
            self.invoke()
        self.assertEqual(self.state()['phase'], 'failed')
        self.assertFalse((self.output / 'receipts' / (adapter.AUDIT + '.json')).exists())
        self.assert_uncertified()

    def test_second_source_reconstruction_failure_cannot_certify(self):
        with self.assertRaisesRegex(ValueError, 'independent full source regeneration failed'):
            self.invoke(generator_codes=(0, 1))
        self.assertEqual(len(self.compiled), 328)
        self.assertEqual(self.state()['phase'], 'failed')
        self.assert_uncertified()

    def test_witness_drift_after_compilation_starts_cannot_certify(self):
        self.mutate_after = lambda: (self.output / 'witness.json').write_text('changed input')
        with self.assertRaisesRegex(ValueError, 'source/dependency changed during replay'):
            self.invoke('--target', self.table_names[0])
        self.assert_uncertified()

    def test_manifest_drift_after_compilation_starts_cannot_certify(self):
        self.mutate_after = lambda: (self.output / 'manifest.json').write_text('{}')
        with self.assertRaisesRegex(ValueError, 'manifest changed during replay'):
            self.invoke('--target', self.table_names[0])
        self.assert_uncertified()

    def test_preflight_failure_replaces_old_complete_even_on_repeat(self):
        for _ in range(2):
            with self.assertRaisesRegex(ValueError, 'independent full source regeneration failed'):
                self.invoke(generator_codes=(1,))
            self.assertEqual(self.compiled, [])
            self.assertEqual(self.state()['phase'], 'failed')
            self.assert_uncertified()

    def test_empty_plan_rejected_before_environment_or_compiler(self):
        self.manifest['jobs'] = []
        self.engine.atomic(self.output / 'manifest.json', self.manifest)
        with self.assertRaisesRegex(ValueError, 'missing fixed full composition theorem or audit'):
            self.invoke(generator_codes=())
        self.assertEqual(self.compiled, [])
        self.assert_uncertified()

    def test_existing_run_lock_prevents_second_run(self):
        before = (self.output / 'status.json').read_bytes()
        with (self.output / 'runner.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with patch.object(sys, 'argv', ['replay', '--output-dir', str(self.output)]), \
                    patch.object(self.engine, 'run_locked') as run:
                with self.assertRaises(BlockingIOError):
                    self.engine.main()
                run.assert_not_called()
        self.assertEqual((self.output / 'status.json').read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
