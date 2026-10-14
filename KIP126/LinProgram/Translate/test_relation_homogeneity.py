"""Adversarial checks for the all-relations homogeneity exporter."""
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('relation_homogeneity', Path(__file__).with_name('generate-relation-homogeneity.py'))
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


class RelationHomogeneityTests(unittest.TestCase):
    def test_weighted_degree_not_ordinary_exponent_sum(self):
        MOD.validate_relations([(1, 2), (2, 4)], ['0,2;1,1'])

    def test_changed_single_term_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'inhomogeneous'):
            MOD.validate_relations([(1, 2), (2, 4)], ['0,1;1,1'])

    def test_both_coordinates_are_checked(self):
        with self.assertRaisesRegex(ValueError, 'inhomogeneous'):
            MOD.validate_relations([(1, 4), (2, 4)], ['0,1;1,1'])

    def test_unpaired_exponent_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'odd exponent'):
            MOD.validate_relations([(1, 2)], ['0,1,0'])

    def test_unknown_generator_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'generator index'):
            MOD.validate_relations([(1, 2)], ['1,1'])

    def test_negative_generator_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'generator index'):
            MOD.validate_relations([(1, 2)], ['-1,1'])

    def test_negative_exponent_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'negative exponent'):
            MOD.validate_relations([(1, 2)], ['0,-1'])

    def test_no_artificial_degree_cutoff(self):
        MOD.validate_relations([(1, 2), (2, 4)], ['0,132;1,66'])


if __name__ == '__main__':
    unittest.main()
