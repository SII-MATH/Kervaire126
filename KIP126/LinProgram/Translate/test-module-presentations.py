#!/usr/bin/env python3
"""Regression checks for complete native input shape and generated-byte identity."""
import argparse
import copy
import importlib.util
from pathlib import Path
import sqlite3
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('module_presentations', Path(__file__).with_name('generate-module-presentations.py'))
M = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(M)
ROOT = Path(__file__).resolve().parents[3]
OUTPUT = None


class ModulePresentationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.modules = M.read_inputs(ROOT, ROOT/'Source/LWXMachine/kervaire_database.rar')
        cls.outputs = M.build_outputs(cls.modules)
        native = M.load(ROOT, 'module_test_native', 'native-contract.py')
        path, _, _ = native.load_lowstem().pinned('S0_AdamsSS_t261.db')
        with native.connect(path) as db:
            cls.ring = {r['id']:dict(r) for r in db.execute('SELECT * FROM S0_AdamsE2_generators ORDER BY id')}

    def validate_changed(self, change):
        data = copy.deepcopy(self.modules[0])
        change(data)
        with self.assertRaises(ValueError):
            M.validate_module(data['object'], data['generators'], data['relations'], data['native_version'], self.ring)

    def test_complete_checked_output(self):
        M.check_outputs(OUTPUT or ROOT/'KIP126/LinProgram/Generated/Modules', self.outputs)

    def test_missing_generator(self):
        self.validate_changed(lambda d:d['generators'].pop())

    def test_missing_relation(self):
        self.validate_changed(lambda d:d['relations'].pop())

    def test_changed_generator_order(self):
        self.validate_changed(lambda d:d['generators'][0].update(id=1))

    def test_changed_relation_rowid(self):
        self.validate_changed(lambda d:d['relations'][0].update(sqlite_rowid=2))

    def test_null_or_empty_relation(self):
        for value in (None, ''):
            with self.subTest(value=value):
                self.validate_changed(lambda d:d['relations'][0].update(rel=value))

    def test_out_of_range_module_generator(self):
        self.validate_changed(lambda d:d['relations'][0].update(rel='1,1,887'))

    def test_out_of_range_sphere_generator(self):
        self.validate_changed(lambda d:d['relations'][0].update(rel='2914,1,0'))

    def test_invalid_exponent_or_repeated_generator(self):
        for code in ('0,0,0', '0,1,0,1,0'):
            with self.subTest(code=code):
                self.validate_changed(lambda d:d['relations'][0].update(rel=code))

    def test_changed_relation_degree(self):
        self.validate_changed(lambda d:d['relations'][0].update(t=199))

    def test_changed_native_limit(self):
        def change(d):
            next(r for r in d['native_version'] if r['name']=='t_max')['value']=199
        self.validate_changed(change)

    def test_nullable_generator_metadata_is_retained(self):
        cw = self.modules[1]
        r = cw['generators'][240]
        self.assertEqual((r['id'],r['repr'],r['s'],r['t']), (240,7864488,15,137))
        self.assertIsNone(r['name']); self.assertIsNone(r['cell']); self.assertIsNone(r['cell_coeff'])
        self.assertEqual(sum(r['name'] is None for r in cw['generators']),607)
        M.validate_module(cw['object'],cw['generators'],cw['relations'],cw['native_version'],self.ring)
        self.assertIn('⟨240, none, 7864488, 15, 137, none, none⟩',self.outputs['CWNuEta.lean'].decode())

    def test_no_extra_empty_relation_or_truncated_family(self):
        for module in self.modules:
            cs = M.chunks(module['relations'],M.CHUNK_SIZE)
            self.assertEqual([r for c in cs for r in c],module['relations'])
            self.assertTrue(all(r['rel'] for c in cs for r in c))
            self.assertEqual(len(module['generators']),module['generator_count'])
            self.assertEqual(len(module['relations']),module['relation_count'])

    def test_strict_schema_rejects_extra_field(self):
        db=sqlite3.connect(':memory:')
        db.execute('CREATE TABLE version (id INTEGER PRIMARY KEY, name TEXT, value, extra TEXT)')
        with self.assertRaisesRegex(ValueError,'schema changed'):
            M.schema(db,'version',M.VERSION_SCHEMA)
        db.close()

    def test_check_rejects_modified_lean_and_json(self):
        for name in ('Ceta.lean','Ceta.json'):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp); (p/name).write_bytes(self.outputs[name]+b' ')
                with self.assertRaisesRegex(ValueError,'output differs'):
                    M.check_outputs(p,{name:self.outputs[name]})


if __name__=='__main__':
    parser=argparse.ArgumentParser(add_help=False)
    parser.add_argument('--root',type=Path,default=ROOT)
    parser.add_argument('--output-dir',type=Path)
    args,rest=parser.parse_known_args();ROOT=args.root.resolve();OUTPUT=args.output_dir
    unittest.main(argv=[__file__]+rest)
