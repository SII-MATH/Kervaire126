#!/usr/bin/env python3
"""Exercise portable replay entry points without treating mock output as proof."""
import fcntl
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


PACKAGE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, PACKAGE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


runner = load('portable_runner', 'runner.py')
ceta = load('portable_ceta_entry', 'replay-ceta.py')


class PortableReplayBoundary(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.root = self.directory / 'repository'
        self.output = self.directory / 'output'
        self.root.mkdir()
        self.output.mkdir()

    def tearDown(self):
        self.temporary.cleanup()

    def make_plan(self, relative):
        generator = self.root / 'tools/generate.py'
        generator.parent.mkdir()
        generator.write_bytes(b'pinned generator')
        witness = self.output / 'witness.jsonl'
        witness.write_bytes(b'untrusted test witness')
        source = self.output / 'src/Fake/C.lean'
        source.parent.mkdir(parents=True)
        source.write_text('example : True := True.intro\n')
        name = str(generator.relative_to(self.root)) if relative else str(generator)
        manifest = {
            'source_root': str(self.root),
            'pinned_source_hashes': {},
            'auxiliary_witness': {'path': witness.name, 'sha256': runner.digest(witness)},
            'generation_inputs': {name: runner.digest(generator)},
            'jobs': [{
                'module': 'Fake.C', 'source': 'src/Fake/C.lean',
                'sha256': runner.digest(source), 'imports': [], 'dependencies': [],
                'kind': 'audit',
            }],
        }
        runner.atomic(self.output / 'manifest.json', manifest)
        runner.atomic(self.output / 'status.json', {
            'phase': 'complete', 'complete_native_quotient_map_certified': True,
        })
        return generator

    def assert_generation_drift_rejected(self, relative):
        generator = self.make_plan(relative)
        generator.write_bytes(b'changed generator after preparation')
        args = ['runner', '--output-dir', str(self.output)]
        with patch.object(sys, 'argv', args), \
                patch.object(runner, 'refresh_external') as freshness, \
                patch.object(runner, 'compile_job') as compile_job:
            with self.assertRaisesRegex(ValueError, 'source/dependency changed'):
                runner.entrypoint()
        freshness.assert_not_called()
        compile_job.assert_not_called()
        state = json.loads((self.output / 'status.json').read_text())
        self.assertEqual(state['phase'], 'failed')
        self.assertFalse(state['complete_native_quotient_map_certified'])
        self.assertFalse(state['actual_spectrum_map_comparison_certified'])
        self.assertFalse((self.output / 'receipts').exists())

    def test_absolute_generation_input_drift_stops_before_freshness(self):
        self.assert_generation_drift_rejected(relative=False)

    def test_relative_generation_input_drift_stops_before_freshness(self):
        self.assert_generation_drift_rejected(relative=True)

    def test_ceta_entry_refuses_live_lock_without_changing_inputs(self):
        manifest = self.output / 'manifest.json'
        manifest.write_bytes(b'live source manifest must remain unchanged')
        witness = self.output / 'witness/CetaToSphere.jsonl'
        witness.parent.mkdir()
        witness.write_bytes(b'live witness must remain unchanged')
        before = {p: p.read_bytes() for p in (manifest, witness)}
        for mode in ([], ['--prepare-only'], ['--check']):
            with self.subTest(mode=mode), (self.output / 'runner.lock').open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                args = ['replay-ceta', '--root', str(self.root),
                        '--output-dir', str(self.output), *mode]
                with patch.object(sys, 'argv', args), patch.object(ceta, 'run') as run:
                    with self.assertRaises(BlockingIOError):
                        ceta.main()
                run.assert_not_called()
                self.assertEqual({p: p.read_bytes() for p in before}, before)

    def test_check_keeps_rebuilder_read_only_and_never_starts_lean(self):
        manifest = self.output / 'manifest.json'
        manifest.write_text(json.dumps({
            'complete_native_quotient_map_certified': False,
            'actual_model_comparison_certified': False,
        }))
        before = manifest.read_bytes()
        args = ['replay-ceta', '--root', str(self.root),
                '--output-dir', str(self.output), '--check']
        with patch.object(sys, 'argv', args), patch.object(ceta, 'run') as run:
            ceta.main()
        self.assertEqual(run.call_count, 2)
        rebuild, generate = [call.args[0] for call in run.call_args_list]
        self.assertEqual(Path(rebuild[1]).name, 'rebuild-witness.py')
        self.assertIn('--manifest', rebuild)
        self.assertIn('--check', rebuild)
        self.assertEqual(Path(generate[1]).name, 'generate.py')
        self.assertIn('--check', generate)
        self.assertEqual(manifest.read_bytes(), before)

    def test_prepare_refuses_certification_promotion_before_runner(self):
        manifest = self.output / 'manifest.json'
        manifest.write_text(json.dumps({
            'complete_native_quotient_map_certified': True,
            'actual_model_comparison_certified': False,
        }))
        args = ['replay-ceta', '--root', str(self.root), '--output-dir', str(self.output)]
        with patch.object(sys, 'argv', args), patch.object(ceta, 'run') as run:
            with self.assertRaisesRegex(ValueError, 'must not promote'):
                ceta.main()
        self.assertEqual(run.call_count, 2)
        self.assertTrue(all(Path(call.args[0][1]).name != 'runner.py'
                            for call in run.call_args_list))


if __name__ == '__main__':
    unittest.main()
