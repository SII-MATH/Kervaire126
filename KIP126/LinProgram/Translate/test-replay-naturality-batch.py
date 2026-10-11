#!/usr/bin/env python3
"""Fixed-goal, provenance and unknown-value regressions for the 82-row replay."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('naturality_batch', Path(__file__).with_name('replay-naturality-batch.py'))
BATCH = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BATCH)


class BatchReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.words, cls.selected, cls.all_ceta, cls.sphere = BATCH.rebuild_words()
        cls.cochains = BATCH.rebuild_cochains(cls.words, cls.selected, cls.all_ceta, cls.sphere)

    def test_complete_original_window_and_matrices(self):
        ids = self.words['selection']['complete_selected_ids']
        self.assertEqual(ids, list(range(2, 84)))
        self.assertEqual(self.words['summary'], {'direct-singleton': 36, 'relation-reduced': 1, 'zero': 45})
        actual = sorted(i for m in self.words['complete_degree_matrices'] for i in m['source_ids'])
        self.assertEqual(actual, ids)
        self.assertEqual(len(self.cochains['map_columns']), 48)
        self.assertEqual(len(self.cochains['ceta_generators']), 84)
        self.assertEqual(len(self.cochains['old_new_repr_data_matches']), 132)

    def test_all_four_outputs_reconstruct(self):
        outputs = {'Batch21.json': BATCH.render_json(self.words), 'Batch21.lean': BATCH.render_words(self.words),
                   'CochainBatch21.json': BATCH.render_json(self.cochains),
                   'CochainBatch21.lean': BATCH.render_cochains(self.cochains)}
        for name, text in outputs.items():
            self.assertEqual((BATCH.DEFAULT_OUTPUT / name).read_text(), text)

    def test_changed_word_goal_witness_or_scope_is_rejected(self):
        mutations = [lambda b: b['entries'][0]['source'].__setitem__('t', 3),
                     lambda b: b['entries'][2].__setitem__('coordinates', []),
                     lambda b: b['entries'][41]['witness'][0].__setitem__('relation', 1),
                     lambda b: b['relation_codes'].__setitem__(0, '2,3'),
                     lambda b: b['proof_boundary'].__setitem__('actual_map_comparison', True),
                     lambda b: b['proof_boundary'].__setitem__('historical_premise_edge_certified', True)]
        for mutation in mutations:
            candidate = copy.deepcopy(self.words)
            mutation(candidate)
            with self.assertRaisesRegex(ValueError, 'differs'):
                BATCH.validate_candidate(candidate, self.words)

    def test_cochain_matrix_or_claim_mutation_is_rejected(self):
        for mutate in (lambda b: b['map_columns'].__setitem__(1, []),
                       lambda b: b['entries'][2].__setitem__('targets', []),
                       lambda b: b['proof_boundary'].__setitem__('resolution_exactness', True),
                       lambda b: b['old_new_repr_data_matches'][0].__setitem__('chain_id', 1)):
            candidate = copy.deepcopy(self.cochains)
            mutate(candidate)
            with self.assertRaisesRegex(ValueError, 'differs'):
                BATCH.validate_candidate(candidate, self.cochains)

    def test_full_id_list_cannot_shrink_reorder_or_duplicate(self):
        ids = self.words['selection']['complete_selected_ids']
        for candidate in (ids[:-1], list(reversed(ids)), ids[:-1] + [ids[0]]):
            with self.assertRaisesRegex(ValueError, 'differs'):
                BATCH.validate_candidate(candidate, ids)

    def test_json_types_duplicates_and_nonfinite_values_are_rejected(self):
        candidate = copy.deepcopy(self.words)
        candidate['proof_boundary']['actual_map_comparison'] = 0
        with self.assertRaisesRegex(ValueError, 'differs'):
            BATCH.validate_candidate(candidate, self.words)
        for text in ('{"x":1,"x":2}', '{"x":NaN}'):
            with self.assertRaises(ValueError):
                BATCH.load_json(text)

    def test_mutated_input_bytes_fail_canonical_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'Adams.json'
            path.write_bytes((BATCH.ROOT / BATCH.CHAIN_INPUTS['config']).read_bytes() + b' ')
            with self.assertRaisesRegex(ValueError, 'canonical input mismatch'):
                BATCH.authenticated(BATCH.CHAIN_INPUTS['config'], path)

    def test_null_generator_image_is_not_zero(self):
        native = BATCH.load('native-contract.py', 'naturality_test_native')
        low = native.load_lowstem()
        with self.assertRaisesRegex(ValueError, 'NULL image'):
            BATCH.map_word('1', {1: {'s': 1, 't': 3}}, {1: None}, {}, low)

    def test_missing_chain_generator_is_not_zero(self):
        decoder = BATCH.load('extract-secondary-witness.py', 'naturality_test_decoder')
        with self.assertRaisesRegex(ValueError, 'missing, not zero'):
            BATCH.indexed_terms(frozenset({(decoder.ZERO, 3)}), 1, {}, [], decoder, 3)

    def test_unsupported_reduction_is_not_zero(self):
        native = BATCH.load('native-contract.py', 'naturality_test_reduce')
        low = native.load_lowstem()
        with self.assertRaisesRegex(ValueError, 'no supported'):
            BATCH.reduce_to_basis({((0, 1),)}, [], [], low)


if __name__ == '__main__':
    unittest.main()
