#!/usr/bin/env python3
"""Trust-boundary regressions for complete secondary source generation."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('generate-secondary-seed5487-complete.py')
if not SCRIPT.exists():
    SCRIPT = Path(__file__).with_name('generate.py')
ROOT = Path(os.environ.get('SECONDARY_ROOT', Path(__file__).resolve().parents[4]))
WITNESS = Path(os.environ['SECONDARY_WITNESS']) if 'SECONDARY_WITNESS' in os.environ else None


class CompleteGeneratorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='secondary-complete-test-')
        cls.directory = Path(cls.temp.name)
        cls.witness = WITNESS or cls.directory / 'witness.json'
        if WITNESS is None:
            raw = ROOT / 'KIP126/LinProgram/Raw/Secondary/Seed5487'
            subprocess.run([sys.executable, str(ROOT / 'KIP126/LinProgram/Translate/extract-secondary-witness.py'),
                '--resolution', str(raw / 'S0_Adams_res.db'), '--secondary', str(raw / 'S0_Adams_d2.db'),
                '--output', str(cls.witness)], check=True, capture_output=True)
        cls.good = cls.directory / 'good'
        result = cls.invoke(cls.good)
        if result.returncode:
            raise RuntimeError(result.stderr)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    @classmethod
    def invoke(cls, output, *extra, root=ROOT, witness=WITNESS):
        return subprocess.run([sys.executable, str(SCRIPT), '--root', str(root),
                               '--witness', str(witness or cls.witness), '--output-dir', str(output), *extra],
                              capture_output=True, text=True,
                              env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})

    def copy_output(self, label):
        target = self.directory / label
        shutil.copytree(self.good, target)
        return target

    def test_full_replay_is_read_only_and_exact(self):
        before = {p.relative_to(self.good): p.stat().st_mtime_ns
                  for p in self.good.rglob('*') if p.is_file()}
        result = self.invoke(self.good, '--check')
        self.assertEqual(result.returncode, 0, result.stderr)
        after = {p.relative_to(self.good): p.stat().st_mtime_ns
                 for p in self.good.rglob('*') if p.is_file()}
        self.assertEqual(before, after)

    def test_complete_coverage_and_no_certification_promotion(self):
        manifest = json.loads((self.good / 'manifest.json').read_bytes())
        self.assertEqual(manifest['complete_product_ids'], list(range(15839)))
        self.assertEqual(len(manifest['complete_native_row_ids']), 96)
        chunks = [j for j in manifest['jobs'] if j['kind'] == 'original_product_certificates']
        self.assertEqual(sorted(i for j in chunks for i in j['original_ids']), list(range(15839)))
        self.assertEqual(len(chunks), 271)
        self.assertEqual(sum(j['kind'] == 'complete_original_rank_coproduct_table'
                             for j in manifest['jobs']), 39)
        for flag in ('full_native_96_composition_certified', 'secondary_associator_certified',
                     'actual_d2_certified'):
            self.assertFalse(manifest[flag])
        jobs = {j['module']: j for j in manifest['jobs']}
        audits = [j['module'] for j in jobs.values() if j['kind'] == 'audit']
        self.assertEqual(len(audits), 1)
        seen = set()
        def visit(name):
            if name not in seen:
                seen.add(name)
                for dependency in jobs[name]['dependencies']:
                    visit(dependency)
        visit(audits[0])
        self.assertEqual(seen, set(jobs))
        row_ids = [rid for job in jobs.values() if job['kind'] == 'complete_composition_rows'
                   for rid in job['original_ids']]
        self.assertEqual(row_ids, manifest['complete_native_row_ids'])

    def test_dropped_original_row_rejected(self):
        witness = json.loads(self.witness.read_bytes())
        witness['generators'].pop()
        path = self.directory / 'missing-row.json'
        path.write_text(json.dumps(witness))
        output = self.directory / 'bad-closure'
        result = self.invoke(output, witness=path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('wrong whole native closure', result.stderr)
        self.assertFalse(output.exists())

    def test_native_database_drift_rejected(self):
        witness = json.loads(self.witness.read_bytes())
        source = next(Path(p) for p in witness['input_hashes'] if p.endswith('S0_Adams_d2.db'))
        path = self.directory / 'modified.db'
        path.write_bytes(source.read_bytes() + b'changed')
        output = self.directory / 'bad-db'
        result = self.invoke(output, '--secondary-db', str(path))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('original database drift', result.stderr)
        self.assertFalse(output.exists())

    def test_changed_product_proof_source_rejected(self):
        output = self.copy_output('changed-proof')
        path = next((output / 'src').rglob('ProductsD*.lean'))
        path.write_text(path.read_text().replace('by decide +kernel', 'by sorry', 1))
        result = self.invoke(output, '--check')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('generated output drift', result.stderr)

    def test_extra_generated_module_rejected(self):
        output = self.copy_output('extra-module')
        (output / 'src/Untracked.lean').write_text('example : True := True.intro\n')
        result = self.invoke(output, '--check')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('unexpected or missing generated Lean source', result.stderr)

    def test_canonical_source_link_drift_rejected(self):
        root = self.directory / 'false-link-root'
        for name in ('KIP126/LinProgram/Translate/extract-secondary-witness.py',
                     'KIP126/LinProgram/Generated/Provenance/seed5487-next.json', 'docs/external-inputs.json',
                     'Source/LWXMachine/source-code.zip'):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, path)
        path = root / 'docs/external-inputs.json'
        inventory = json.loads(path.read_bytes())
        source = next(s for s in inventory['sources'] if s['id'] == 'lwx_machine')
        archive = next(a for a in source['artifacts'] if a['path'] == 'Source/LWXMachine/source-code.zip')
        archive['reproduction']['existing_extraction_and_rebuild_record'] = 'unrelated.json'
        path.write_text(json.dumps(inventory))
        output = self.directory / 'bad-link'
        result = self.invoke(output, root=root)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('canonical archive/reproduction linkage drift', result.stderr)
        self.assertFalse(output.exists())


if __name__ == '__main__':
    unittest.main()
