#!/usr/bin/env python3
"""Negative boundary tests for the complete pinned native graph exporter."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('module_maps', Path(__file__).with_name('generate-module-maps.py'))
M = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(M)
_parents = Path(__file__).resolve().parents
ROOT = _parents[3] if len(_parents) > 3 else Path.cwd()
OUTPUT = None


class ModuleMapTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        archive = ROOT/'Source/LWXMachine/kervaire_database.rar'
        cls.graphs = M.read_inputs(ROOT, archive)
        cls.outputs = M.build_outputs(cls.graphs)
        cls.reader = M.load(ROOT, 'map_tests_modules', 'generate-module-presentations.py')
        cls.modules = {m['object']: m for m in cls.reader.read_inputs(ROOT, archive)}
        cls.native = M.load(ROOT, 'map_tests_native', 'native-contract.py')
        path, _, _ = cls.native.load_lowstem().pinned('S0_AdamsSS_t261.db')
        with cls.native.connect(path) as db:
            cls.ring = {r['id']:dict(r) for r in db.execute('SELECT * FROM S0_AdamsE2_generators ORDER BY id')}

    def changed(self, mutate, which=0):
        graph = copy.deepcopy(self.graphs[which]); mutate(graph)
        with self.assertRaises(ValueError):
            M.validate_graph(M.SPECS[which], graph['native_catalogue'], graph['native_version'],
                             graph['rows'], self.modules, self.ring)

    def test_complete_reconstruction(self):
        for graph, count in zip(self.graphs, (887, 844)):
            self.assertEqual([r['id'] for r in graph['rows']], list(range(count)))
            self.assertFalse(graph['mathematical_map_certified'])
            self.assertFalse(graph['actual_model_comparison_certified'])
        if OUTPUT:
            M.check_outputs(OUTPUT, self.outputs)

    def test_missing_extra_duplicate_reordered_ids(self):
        mutations = [lambda d:d['rows'].pop(),
                     lambda d:d['rows'].append({'id':887, 'map':''}),
                     lambda d:d['rows'][1].update(id=0),
                     lambda d:d['rows'].reverse(),
                     lambda d:d['rows'][0].update(id=False)]
        for i, mutation in enumerate(mutations):
            with self.subTest(case=i): self.changed(mutation)

    def test_missing_extra_fields(self):
        for mutation in (lambda d:d['rows'][0].pop('map'),
                         lambda d:d['rows'][0].update(extra='')):
            self.changed(mutation)

    def test_null_unknown_are_not_empty_zero(self):
        for which in (0, 1):
            for value in (None, '?', 'unknown', '-1', '4294967295', ' ', ';', '0,1;'):
                with self.subTest(which=which, value=value):
                    self.changed(lambda d:d['rows'][1].update(map=value), which)

    def test_empty_zero_is_preserved(self):
        for graph in self.graphs:
            self.assertEqual(graph['rows'][0], {'id':0, 'map':''})
            self.assertIn('⟨0, ""⟩', self.outputs[graph['lean_module_name']+'.lean'].decode())
            self.assertIn("imageCodes[i.val]'", self.outputs[graph['lean_module_name']+'.lean'].decode())
            self.assertNotIn('getD', self.outputs[graph['lean_module_name']+'.lean'].decode())

    def test_wrong_word_parity(self):
        self.changed(lambda d:d['rows'][1].update(map='0'))
        self.changed(lambda d:d['rows'][1].update(map='0,1'), 1)

    def test_sphere_generator_range(self):
        self.changed(lambda d:d['rows'][1].update(map='2914,1'))
        self.changed(lambda d:d['rows'][1].update(map='2914,1,0'), 1)

    def test_target_module_generator_range(self):
        self.changed(lambda d:d['rows'][1].update(map='887'), 1)

    def test_exponent_and_coefficient_order(self):
        for value in ('0,0', '0,201', '0,4294967295', '0,-1', '0,01',
                      '0,1,0,1', '1,1,0,1'):
            with self.subTest(value=value):
                self.changed(lambda d:d['rows'][1].update(map=value))

    def test_changed_term_degree(self):
        self.changed(lambda d:d['rows'][1].update(map='1,1'))
        self.changed(lambda d:d['rows'][1].update(map='0,2,0'), 1)

    def test_changed_catalogue_fields(self):
        for field, value in (('sus',3), ('from','S0'), ('to','CW_nu_eta'),
                             ('t_max',199), ('path','other.db'), ('type',None)):
            with self.subTest(field=field):
                self.changed(lambda d:d['native_catalogue'].update({field:value}))
        self.changed(lambda d:d['native_catalogue'].update(extra='field'))

    def test_complete_version_metadata(self):
        for field, value in (('version',4), ('filtration',1), ('suspension',3),
                             ('t_max',199), ('from','S0'), ('to','Ceta'), ('change notes',None)):
            with self.subTest(field=field):
                self.changed(lambda d:next(r for r in d['native_version'] if r['name']==field).update(value=value))
        self.changed(lambda d:d['native_version'].pop())
        self.changed(lambda d:d['native_version'][0].update(value=True))
        self.changed(lambda d:next(r for r in d['native_version'] if r['name']=='timestamp').update(value=None), 1)

    def test_source_target_degrees_from_same_inputs(self):
        modules = copy.deepcopy(self.modules)
        for source in ('Ceta', 'CW_nu_eta'):
            changed = copy.deepcopy(modules)
            changed[source]['generators'][1]['t'] += 1
            index = 0 if source == 'Ceta' else 1; graph = self.graphs[index]
            with self.assertRaises(ValueError):
                M.validate_graph(M.SPECS[index],graph['native_catalogue'],graph['native_version'],graph['rows'],changed,self.ring)
        changed = copy.deepcopy(modules); changed['Ceta']['generators'][0]['t'] += 1
        graph = self.graphs[1]
        with self.assertRaises(ValueError):
            M.validate_graph(M.SPECS[1],graph['native_catalogue'],graph['native_version'],graph['rows'],changed,self.ring)

    def test_wrong_sphere_coefficient_degrees(self):
        ring = copy.deepcopy(self.ring); ring[0]['t'] += 1; graph = self.graphs[0]
        with self.assertRaises(ValueError):
            M.validate_graph(M.SPECS[0],graph['native_catalogue'],graph['native_version'],graph['rows'],self.modules,ring)

    def test_strict_database_schema_and_table_set(self):
        for ddl in ('CREATE TABLE map_AdamsE2_Ceta_to_S0 (id INTEGER PRIMARY KEY, map TEXT, extra TEXT)',
                    'CREATE TABLE map_AdamsE2_Ceta_to_S0 (id INTEGER PRIMARY KEY, map BLOB)'):
            with tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp)/'map.db'
                with sqlite3.connect(path) as db:
                    db.execute(M.VERSION_SCHEMA); db.execute(ddl)
                with self.assertRaises(ValueError):
                    M.read_database(self.native,self.reader,path,M.SPECS[0])
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'map.db'
            with sqlite3.connect(path) as db:
                db.execute(M.VERSION_SCHEMA)
                db.execute('CREATE TABLE map_AdamsE2_Ceta_to_S0 (id INTEGER PRIMARY KEY, map TEXT)')
                db.execute('CREATE TABLE extra (x TEXT)')
            with self.assertRaises(ValueError):
                M.read_database(self.native,self.reader,path,M.SPECS[0])

    def test_canonical_raw_archive_identity(self):
        canonical = json.loads((ROOT/'docs/external-inputs.json').read_text())
        source = next(s for s in canonical['sources'] if s['id']=='lwx_machine')
        graph = self.graphs[1]; filename=graph['native_catalogue']['path']
        _,raw,digest = self.native.load_lowstem().pinned(filename)
        path='KIP126/LinProgram/Raw/'+filename
        for mutate in (lambda a:a.update(sha256='0'*64), lambda a:a.update(size=0),
                       lambda a:a['extracted_from'].update(member='kervaire-49/other.db'),
                       lambda a:a['extracted_from'].update(archive_checksum='md5:'+'0'*32)):
            changed=copy.deepcopy(source); artifact=next(a for a in changed['artifacts'] if a['path']==path); mutate(artifact)
            with self.assertRaises(ValueError):
                M.validate_map_pin(changed,filename,raw,digest,graph['provenance']['archive'])
        changed=copy.deepcopy(source); changed['artifacts']=[a for a in changed['artifacts'] if a['path']!=path]
        with self.assertRaises(ValueError):
            M.validate_map_pin(changed,filename,raw,digest,graph['provenance']['archive'])

    def test_no_mathematical_certification_promotion(self):
        for field in ('mathematical_map_certified','actual_model_comparison_certified'):
            changed=copy.deepcopy(self.graphs); changed[0][field]=True
            with self.assertRaises(ValueError): M.build_outputs(changed)

    def test_canonical_generated_graph_bindings(self):
        M.check_registered_outputs(ROOT, self.outputs)
        registry = json.loads((ROOT/'docs/external-inputs.json').read_text())
        for change in ('hash', 'certification'):
            changed = copy.deepcopy(registry)
            source = next(s for s in changed['sources'] if s['id']=='lwx_machine')
            artifact = next(a for a in source['artifacts'] if a['path'].endswith('map_AdamsSS_CW_nu_eta_to_Ceta_t200.db'))
            derived = artifact['derived_outputs']
            if change == 'hash':
                derived['complete_module_map_graph'][0]['sha256'] = '0'*64
            else:
                derived['mathematical_map_certified'] = True
            with self.subTest(change=change), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp); (root/'docs').mkdir()
                (root/'docs/external-inputs.json').write_text(json.dumps(changed))
                with self.assertRaises(ValueError): M.check_registered_outputs(root, self.outputs)

    def test_rebuild_rejects_modified_or_missing_outputs(self):
        for name in self.outputs:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                path=Path(tmp)
                with self.assertRaises(ValueError): M.check_outputs(path,{name:self.outputs[name]})
                (path/name).write_bytes(self.outputs[name]+b' ')
                with self.assertRaises(ValueError): M.check_outputs(path,{name:self.outputs[name]})


if __name__ == '__main__':
    parser=argparse.ArgumentParser(add_help=False)
    parser.add_argument('--root',type=Path,default=ROOT)
    parser.add_argument('--output-dir',type=Path)
    args,rest=parser.parse_known_args();ROOT=args.root.resolve();OUTPUT=args.output_dir
    unittest.main(argv=[__file__]+rest)
