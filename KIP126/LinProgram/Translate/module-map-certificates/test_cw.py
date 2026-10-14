#!/usr/bin/env python3
"""Regression checks for CW witness semantics and entry-point boundaries."""
import copy
import fcntl
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

PACKAGE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('cw_rebuild', PACKAGE / 'rebuild-cw-witness.py')
cw = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cw)


class Low:
    @staticmethod
    def mon(code):
        values = list(map(int, code.split(','))) if code else []
        return tuple(zip(values[::2], values[1::2]))

    @staticmethod
    def mul(left, right):
        values = dict(left)
        for variable, exponent in right:
            values[variable] = values.get(variable, 0) + exponent
        return tuple(sorted(values.items()))

    @staticmethod
    def quotient(value, divisor):
        values = dict(value)
        for variable, exponent in divisor:
            values[variable] -= exponent
        return tuple((v, e) for v, e in sorted(values.items()) if e)


class WitnessSemantics(unittest.TestCase):
    def rules(self, ring=(), module=()):
        return (cw.NativeRules([{'sqlite_rowid': i, 'rel': code} for i, code in ring], False, Low),
                cw.NativeRules([{'sqlite_rowid': i, 'rel': code} for i, code in module], True, Low))

    def test_empty_image_is_zero(self):
        self.assertEqual(cw.substitute('0,1,0', {0: cw.polynomial('', True, Low)}, Low), set())

    def test_null_image_rejected(self):
        with self.assertRaises(ValueError):
            cw.polynomial(None, True, Low)

    def test_missing_source_image_rejected(self):
        with self.assertRaises(ValueError):
            cw.substitute('0', {}, Low)

    def test_native_module_generator_zero_is_not_zero_vector(self):
        self.assertEqual(cw.polynomial('0', True, Low), {((), 0)})

    def test_source_duplicates_cancel(self):
        self.assertEqual(cw.substitute('0;0', {0: {((), 4)}}, Low), set())

    def test_map_duplicates_cancel(self):
        self.assertEqual(cw.polynomial('0,1,4;0,1,4', True, Low), set())

    def test_exact_module_relation(self):
        ring, module = self.rules(module=[(8, '0,1,3')])
        trace = cw.reduce_image({(((0, 1),), 3)}, ring, module, Low)
        self.assertEqual(trace, [{'kind': 'module', 'rowid': 8, 'multiplier': [], 'module_generator': None}])

    def test_ring_relation_retains_target_coordinate(self):
        ring, module = self.rules(ring=[(9, '0,1')])
        trace = cw.reduce_image({(((0, 2),), 7)}, ring, module, Low)
        self.assertEqual(trace, [{'kind': 'ring', 'rowid': 9, 'multiplier': ((0, 1),), 'module_generator': 7}])

    def test_module_relation_does_not_move_between_coordinates(self):
        ring, module = self.rules(module=[(8, '0,1,3')])
        with self.assertRaises(ValueError):
            cw.reduce_image({(((0, 1),), 4)}, ring, module, Low)

    def test_module_relation_precedes_ring_reduction(self):
        ring, module = self.rules(ring=[(1, '0,1')], module=[(9, '0,1,3')])
        trace = cw.reduce_image({(((0, 2),), 3)}, ring, module, Low)
        self.assertEqual(trace[0]['kind'], 'module')

    def test_noncontiguous_original_ids(self):
        _, module = self.rules(module=[(3, '0,2,4'), (9, '0,1,4')])
        self.assertEqual(module.divisor(((0, 3),), 4), (3, ((0, 1),)))

    def test_reduction_cycle_rejected(self):
        ring, module = self.rules(module=[(1, '0,1,4;1,1,4'), (2, '1,1,4;0,1,4')])
        with self.assertRaisesRegex(ValueError, 'terminate'):
            cw.reduce_image({(((0, 1),), 4)}, ring, module, Low)


class EntryBoundaries(unittest.TestCase):
    def run_entry(self, *args):
        return subprocess.run([sys.executable, str(PACKAGE / 'replay-cw.py'), *map(str, args)],
                              capture_output=True, text=True)

    def test_live_runner_lock_prevents_input_regeneration(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            with (output / 'runner.lock').open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                result = self.run_entry('--root', output, '--output-dir', output, '--prepare-only')
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('BlockingIOError', result.stderr)
                self.assertEqual({p.name for p in output.iterdir()}, {'runner.lock'})

    def test_missing_check_output_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_entry('--root', directory, '--output-dir', directory, '--check')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('requires existing generated output', result.stderr)

    def test_missing_shared_ceta_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_entry('--root', directory, '--output-dir', directory,
                                    '--shared-ceta', Path(directory) / 'absent', '--prepare-only')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('existing generated manifest', result.stderr)




spec = importlib.util.spec_from_file_location('cw_generator', PACKAGE / 'generate-cw.py')
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)

class GeneratorWitnessTests(unittest.TestCase):
 def setUp(self):
  self.source={'relations':[{'sqlite_rowid':1,'rel':'0,1,1','s':2,'t':6},{'sqlite_rowid':2,'rel':'0','s':0,'t':0}]}
  self.target={'relations':[{'sqlite_rowid':1,'rel':'0,1,3'}]}
  self.graph={'rows':[{'id':0,'map':''},{'id':1,'map':'3'}]}
  self.sphere=[{'sqlite_rowid':1,'rel':'0,1'}]
  self.rows=[{'source_relation_rowid':1,'source_degree':[2,6],'terms':[{'kind':'module','rowid':1,'multiplier':[],'module_generator':None}]}]
 def check(self):return g.check_witnesses(self.source,self.target,self.graph,self.sphere,self.rows,Low)
 def reject(self,mut):
  mut();self.assertRaises((ValueError,TypeError,KeyError),self.check)
 def test_valid_and_empty_image(self):
  _,details,stats=self.check();self.assertEqual(details[2],([],[]));self.assertEqual(stats['formal_zero_relations'],1)
 def test_missing_nonzero(self):self.reject(lambda:self.rows.clear())
 def test_extra_zero_witness(self):self.reject(lambda:self.rows.append({**copy.deepcopy(self.rows[0]),'source_relation_rowid':2}))
 def test_duplicate(self):self.reject(lambda:self.rows.append(copy.deepcopy(self.rows[0])))
 def test_unknown_source(self):self.reject(lambda:self.rows[0].update(source_relation_rowid=3))
 def test_bool_source(self):self.reject(lambda:self.rows[0].update(source_relation_rowid=True))
 def test_bad_degree(self):self.reject(lambda:self.rows[0].update(source_degree=[2,7]))
 def test_bool_degree(self):self.reject(lambda:self.rows[0].update(source_degree=[True,6]))
 def test_unknown_fields(self):self.reject(lambda:self.rows[0].update(extra=1))
 def test_unknown_kind(self):self.reject(lambda:self.rows[0]['terms'][0].update(kind='trace'))
 def test_unknown_relation(self):self.reject(lambda:self.rows[0]['terms'][0].update(rowid=99))
 def test_module_slot(self):self.reject(lambda:self.rows[0]['terms'][0].update(module_generator=0))
 def test_ring_missing_slot(self):self.reject(lambda:self.rows[0]['terms'][0].update(kind='ring'))
 def test_outside_target(self):self.reject(lambda:self.rows[0]['terms'][0].update(kind='ring',module_generator=887))
 def test_unknown_scalar(self):self.reject(lambda:self.rows[0]['terms'][0].update(multiplier=[[2914,1]]))
 def test_bad_exponent(self):self.reject(lambda:self.rows[0]['terms'][0].update(multiplier=[[0,201]]))
 def test_zero_exponent(self):self.reject(lambda:self.rows[0]['terms'][0].update(multiplier=[[0,0]]))
 def test_unordered_scalar(self):self.reject(lambda:self.rows[0]['terms'][0].update(multiplier=[[1,1],[0,1]]))
 def test_wrong_combination(self):self.reject(lambda:self.rows[0]['terms'][0].update(multiplier=[[1,1]]))
 def test_ring_slot_semantics(self):
  self.rows[0]['terms'][0].update(kind='ring',module_generator=3);self.check()
  self.reject(lambda:self.rows[0]['terms'][0].update(module_generator=4))
 def test_null_not_empty(self):self.reject(lambda:self.graph['rows'][0].update(map=None))


if __name__ == '__main__':
    unittest.main()
