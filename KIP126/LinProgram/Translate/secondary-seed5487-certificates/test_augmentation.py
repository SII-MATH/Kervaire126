#!/usr/bin/env python3
"""Boundary regressions for the separate all-96 augmentation producer."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
GENERATOR = Path(os.environ.get('SECONDARY_AUGMENTATION_GENERATOR', HERE / 'augmentation.py'))
ROOT = Path(os.environ.get('KIP126_ROOT', HERE.parents[3]))
CORE = Path(os.environ['SECONDARY_FULL_INPUT_DIR']) if 'SECONDARY_FULL_INPUT_DIR' in os.environ else None
spec = importlib.util.spec_from_file_location('augmentation_producer', GENERATOR)
gen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen)


class AugmentationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        global CORE
        if CORE is None:
            temporary = tempfile.TemporaryDirectory(prefix='secondary-augmentation-core-')
            cls.addClassCleanup(temporary.cleanup)
            CORE = Path(temporary.name) / 'core'
            witness = Path(temporary.name) / 'witness.json'
            raw = ROOT / 'KIP126/LinProgram/Raw/Secondary/Seed5487'
            subprocess.run([sys.executable, '-B', str(ROOT / 'KIP126/LinProgram/Translate/extract-secondary-witness.py'),
                '--resolution', str(raw / 'S0_Adams_res.db'), '--secondary', str(raw / 'S0_Adams_d2.db'),
                '--output', str(witness)], check=True, capture_output=True)
            subprocess.run([sys.executable, '-B', str(HERE / 'generate.py'), '--root', str(ROOT),
                '--witness', str(witness), '--output-dir', str(CORE),
                '--resolution-db', str(raw / 'S0_Adams_res.db'),
                '--secondary-db', str(raw / 'S0_Adams_d2.db')], check=True, capture_output=True)
        cls.rows = json.loads((CORE / 'witness.json').read_text())['generators']
        db = ROOT / 'KIP126/LinProgram/Raw/Secondary/Seed5487/S0_Adams_d2.db'
        con = sqlite3.connect('file:' + str(db) + '?mode=ro', uri=True)
        cls.records = dict(con.execute('SELECT id,d2_h FROM S0_Adams_d2'))
        con.close()

    def args(self, out, **kwargs):
        values = dict(root=ROOT, full_input_dir=CORE, output_dir=out,
                      resolution_db=None, secondary_db=None, check=False)
        values.update(kwargs)
        return argparse.Namespace(**values)

    def test_all_96_and_exact_eight_nonzero(self):
        records = gen.validate_records(self.rows, self.records)
        self.assertEqual(len(records), 96)
        self.assertEqual([r['id'] for r in records if r['status'] != 'recorded'], [0, 524288])
        self.assertEqual({r['id']: r['recorded'] for r in records if r['recorded']}, gen.NONZERO)

    def test_present_empty_is_zero(self):
        self.assertEqual(gen.parse_record(''), [])
        self.assertEqual(gen.parse_record('4,4,0'), [4, 4, 0])

    def test_null_is_not_zero(self):
        bad = dict(self.records); bad[524289] = None
        with self.assertRaisesRegex(ValueError, 'NULL'):
            gen.validate_records(self.rows, bad)

    def test_missing_nonbase_is_rejected(self):
        bad = dict(self.records); del bad[524289]
        with self.assertRaisesRegex(ValueError, 'missing d2_h'):
            gen.validate_records(self.rows, bad)

    def test_base_cannot_be_relabeled_recorded_zero(self):
        bad = dict(self.records); bad[0] = ''
        with self.assertRaisesRegex(ValueError, 'unrecorded base'):
            gen.validate_records(self.rows, bad)

    def test_record_order_or_duplicates_not_normalized(self):
        bad = dict(self.records); bad[1572869] = '4,4,4'
        with self.assertRaisesRegex(ValueError, 'differs'):
            gen.validate_records(self.rows, bad)

    def test_malformed_record_rejected(self):
        for bad in (' ', '4,', '-1', '04', '4;5'):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                gen.parse_record(bad)

    def test_original_db_drift_rejected_before_core_execution(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp); bad = p / 'bad.db'; bad.write_bytes(b'drift')
            with patch.object(gen.subprocess, 'run') as run:
                for field in ('resolution_db', 'secondary_db'):
                    with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'database drift'):
                        gen.run(self.args(p / 'out', **{field: bad}))
                run.assert_not_called()

    def test_no_write_inside_core(self):
        with self.assertRaisesRegex(ValueError, 'disjoint'):
            gen.run(self.args(CORE / 'supplement'))

    def test_core_failure_prevents_generation(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'out'
            with patch.object(gen.subprocess, 'run', side_effect=subprocess.CalledProcessError(1, 'core')) as run:
                with self.assertRaises(subprocess.CalledProcessError):
                    gen.run(self.args(out))
                self.assertIn('--check', run.call_args.args[0])
            self.assertFalse(out.exists())

    def test_fullinput_drift_rejected_before_core_execution(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp); core = p / 'core'; core.mkdir()
            for f in ('manifest.json', 'witness.json'):
                shutil.copyfile(CORE / f, core / f)
            m = json.loads((core / 'manifest.json').read_text())
            job = next(j for j in m['jobs'] if j['module'] == gen.CORE_MODULE)
            source = core / job['source']; source.parent.mkdir(parents=True); source.write_text('tampered')
            with patch.object(gen.subprocess, 'run') as run:
                with self.assertRaisesRegex(ValueError, 'FullInput source drift'):
                    gen.run(self.args(p / 'out', full_input_dir=core))
                run.assert_not_called()

    def test_full_replay_is_read_only_and_tamper_rejected(self):
        with tempfile.TemporaryDirectory(prefix='secondary-augmentation-test-') as tmp:
            out = Path(tmp) / 'out'
            gen.run(self.args(out))
            files = list(out.rglob('*'))
            before = {str(p.relative_to(out)): (p.stat().st_mtime_ns, gen.sha(p.read_bytes()))
                      for p in files if p.is_file()}
            gen.run(self.args(out, check=True))
            after = {str(p.relative_to(out)): (p.stat().st_mtime_ns, gen.sha(p.read_bytes()))
                     for p in files if p.is_file()}
            self.assertEqual(before, after)
            m = json.loads((out / 'manifest.json').read_text())
            self.assertEqual(len(m['jobs']), 3)
            for flag in ('augmentation_kernel_certified', 'full_native_96_composition_certified',
                         'secondary_associator_certified', 'actual_d2_certified'):
                self.assertFalse(m[flag])
            proof = next(out.rglob('Proofs.lean'))
            self.assertNotIn('def nativeRows', proof.read_text())
            self.assertEqual(proof.read_text().count('_augmentation_certified : RowAugmentationCertified'), 96)
            proof.write_text(proof.read_text().replace('row4194320.f = [16]', 'row4194320.f = []'))
            with self.assertRaisesRegex(ValueError, 'replay mismatch'):
                gen.run(self.args(out, check=True))


    def test_late_output_symlink_rejected_before_any_write(self):
        # records.json comes after all Lean sources in the emission order.
        # A complete preflight must reject it before writing any of those.
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp); out = p / 'out'; out.mkdir()
            victim = p / 'core-witness'; victim.write_bytes(b'protected core bytes')
            (out / 'records.json').symlink_to(victim)
            with patch.object(gen.subprocess, 'run'):
                with self.assertRaisesRegex(ValueError, 'symlink in generated output path'):
                    gen.run(self.args(out))
            self.assertEqual(victim.read_bytes(), b'protected core bytes')
            self.assertFalse((out / 'src').exists())
            self.assertFalse((out / 'manifest.json').exists())

    def test_generated_source_ancestor_symlink_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp); out = p / 'out'; out.mkdir()
            victim = p / 'core-sources'; victim.mkdir()
            (out / 'src').symlink_to(victim, target_is_directory=True)
            with patch.object(gen.subprocess, 'run'):
                with self.assertRaisesRegex(ValueError, 'symlink in generated output path'):
                    gen.run(self.args(out))
            self.assertEqual(list(victim.iterdir()), [])
            self.assertFalse((out / 'records.json').exists())

    def test_output_ancestor_symlink_rejected_before_resolve(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp); victim = p / 'outside'; victim.mkdir()
            alias = p / 'alias'; alias.symlink_to(victim, target_is_directory=True)
            with patch.object(gen.subprocess, 'run') as run:
                with self.assertRaisesRegex(ValueError, 'symlink in generated output path'):
                    gen.run(self.args(alias / 'out'))
                run.assert_not_called()
            self.assertEqual(list(victim.iterdir()), [])

    def test_existing_hardlink_replaced_without_modifying_other_link(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp); out = p / 'out'; out.mkdir()
            victim = p / 'core-witness'; victim.write_bytes(b'protected core bytes')
            target = out / 'records.json'; os.link(victim, target)
            with patch.object(gen.subprocess, 'run'):
                gen.run(self.args(out))
            self.assertEqual(victim.read_bytes(), b'protected core bytes')
            self.assertNotEqual(target.stat().st_ino, victim.stat().st_ino)
            self.assertEqual(len(json.loads(target.read_bytes())), 96)
            self.assertEqual(list(out.rglob('*.tmp')), [])


if __name__ == '__main__':
    unittest.main()
