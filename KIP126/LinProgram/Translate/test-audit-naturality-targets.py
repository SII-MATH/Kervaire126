#!/usr/bin/env python3
"""Regression tests for target/premise boundaries, not mathematical proofs."""
import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


audit = load('audit_targets', 'audit-naturality-targets.py')
importer = load('import_targets', 'import-proofs.py')


class TargetBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.source = dict(id=10, depth=0, name='Ceta', reason='D', s=2, t=19,
                           stem=17, r=3, x='0,2', dx='1', info=None)
        self.target = dict(id=20, s=2, t=17, r=3)

    def test_nonadjacent_matching_degree_is_candidate(self):
        eq = audit.normalized_source(self.source, importer)
        self.assertTrue(audit.is_prior_candidate(self.source, eq, self.target))

    def test_adjacent_wrong_degree_is_not_candidate(self):
        row = dict(self.source, id=19, t=20, stem=18)
        self.assertFalse(audit.is_prior_candidate(row, audit.normalized_source(row, importer), self.target))

    def test_later_log_is_not_historical_source_candidate(self):
        row = dict(self.source, id=21)
        self.assertFalse(audit.is_prior_candidate(row, audit.normalized_source(row, importer), self.target))

    def test_unknown_or_branch_source_is_not_zero(self):
        for delta in (dict(dx=None), dict(dx='[NULL]'), dict(depth=1), dict(reason=None)):
            self.assertIsNone(audit.normalized_source(dict(self.source, **delta), importer))

    def test_inverse_log_has_normalized_degrees(self):
        eq = audit.normalized_source(dict(self.source, reason='DI', s=5, t=21, stem=16), importer)
        self.assertEqual(eq['source'], dict(degree=[2, 19], coordinates=[0, 2]))
        self.assertEqual(eq['target'], dict(degree=[5, 21], coordinates=[1]))

    def test_combination_images_cancel_over_F2(self):
        self.assertEqual(audit.sum_images([dict(id=7), dict(id=8)],
            {7: dict(coordinates=[0, 2]), 8: dict(coordinates=[1, 2])}), [0, 1])

    def test_missing_image_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unknown, not zero'):
            audit.sum_images([dict(id=7)], {})

    def test_coordinates_are_local_to_degree(self):
        rows = {(2, 19): [dict(id=69)]}
        self.assertEqual(audit.selected_records(dict(degree=[2, 19], coordinates=[0]), rows), [dict(id=69)])
        for coordinates in ([1], [0, 0], [-1], [False]):
            with self.assertRaises(ValueError):
                audit.selected_records(dict(degree=[2, 19], coordinates=coordinates), rows)

    def test_empty_vector_remains_known_zero(self):
        eq = audit.normalized_source(dict(self.source, dx=''), importer)
        self.assertEqual(eq['target']['coordinates'], [])
        self.assertEqual(audit.sum_images([], {}), [])

    def test_known_zero_target_above_native_bound_retains_full_degree(self):
        row = dict(self.source, s=28, t=196, stem=168, r=19, dx='')
        eq = audit.normalized_source(row, importer)
        self.assertEqual(eq['target'], dict(degree=[47, 214], coordinates=[]))
        self.assertIsNone(audit.normalized_source(dict(row, dx='0'), importer))

    def test_remaining_premises_retain_actual_source_and_same_P(self):
        eq = audit.normalized_source(self.source, importer)
        obligations = audit.remaining_propositions(eq, self.target)
        self.assertEqual(obligations[0]['source']['coordinates'], [0, 2])
        self.assertEqual(obligations[0]['page'], 3)
        self.assertIn('presentation P', obligations[1]['statement'])


if __name__ == '__main__':
    unittest.main()
