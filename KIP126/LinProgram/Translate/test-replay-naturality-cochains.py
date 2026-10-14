#!/usr/bin/env python3
"""Exercise native combination decoding and the fixed larger replay boundary."""
import copy
import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


batch = load('test_cochain_batch', 'replay-naturality-batch.py')
cochains = load('test_cochain_replay', 'replay-naturality-cochains.py')
native = load('test_cochain_native', 'native-contract.py')


class CochainEncodingTests(unittest.TestCase):
    def test_map_h_preserves_unsorted_native_support_semantics(self):
        self.assertEqual(batch.map_h_coordinates('11,10'), [10, 11])
        self.assertEqual(batch.map_h_coordinates(''), [])

    def test_log_coordinate_contract_still_requires_sorted_support(self):
        with self.assertRaises(ValueError):
            native.coordinates('11,10')

    def test_unknown_duplicate_or_malformed_map_h_is_rejected(self):
        for value in (None, '[NULL]', '10,10', '-1', '1,', ' 1', False):
            with self.assertRaises(ValueError):
                batch.map_h_coordinates(value)


class CompleteCochainReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bundle = cochains.rebuild()

    def test_full_requested_records_and_full_retained_families(self):
        b = self.bundle
        self.assertEqual(b['selection']['complete_selected_ids'], list(range(2, 261)))
        self.assertEqual([e['native_basis_id'] for e in b['entries']], list(range(2, 261)))
        self.assertEqual((len(b['ceta_generators']), len(b['sphere_generators'])), (261, 155))
        self.assertEqual(len(b['map_columns']), 155)

    def test_archived_source_and_target_combinations_are_not_singletonized(self):
        b = self.bundle
        self.assertEqual(sum(len(e['sources']) > 1 for e in b['entries']), 12)
        self.assertEqual(sum(len(e['targets']) > 1 for e in b['entries']), 1)
        self.assertEqual(b['entries'][104], dict(sources=[63, 64, 65], targets=[], native_basis_id=106))
        self.assertEqual(b['entries'][102], dict(sources=[64], targets=[43, 44], native_basis_id=104))

    def test_dropping_a_source_term_changes_the_checked_native_equation(self):
        entry = self.bundle['entries'][104]
        def evaluate(indices):
            return [j for j, ts in enumerate(self.bundle['map_columns'])
                    if sum(t['generator'] in indices and not any(t['powers']) for t in ts) % 2]
        self.assertEqual(evaluate(entry['sources']), [])
        self.assertNotEqual(evaluate(entry['sources'][:-1]), [])

    def test_complete_bundle_rejects_removed_source_terms_and_false_as_zero(self):
        for mutate in (lambda b: b['entries'][104]['sources'].pop(),
                       lambda b: b['entries'][0].update(native_basis_id=False),
                       lambda b: b['entries'].pop()):
            altered = copy.deepcopy(self.bundle)
            mutate(altered)
            with self.assertRaises(ValueError):
                batch.validate_candidate(altered, self.bundle)

    def test_raw_map_h_remains_available_and_unknown_is_not_inferred(self):
        record = next(r for r in self.bundle['native_map_h_records'] if r['id'] == 2097158)
        self.assertEqual(record['map_h'], '11,10')
        self.assertFalse(self.bundle['proof_boundary']['actual_differential'])
        self.assertFalse(self.bundle['proof_boundary']['resolution_exactness'])
        self.assertIn('not a Lean proof', self.bundle['proof_boundary']['full_chain_equations'])


if __name__ == '__main__':
    unittest.main()
