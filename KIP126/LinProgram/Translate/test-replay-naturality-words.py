#!/usr/bin/env python3
"""Coverage and rejection checks for the fixed full native word exporter."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('naturality_words_tested', HERE / 'replay-naturality-words.py')
words = importlib.util.module_from_spec(spec)
spec.loader.exec_module(words)


class WordCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bundle = words.rebuild()
        cls.low = words.batch.load('native-contract.py', 'word_tests_native').load_lowstem()

    def test_complete_native_selection_and_all_shards(self):
        selection = self.bundle['selection']
        self.assertEqual(selection['count'], 15951)
        self.assertEqual([e['source']['id'] for e in self.bundle['entries']], selection['complete_selected_ids'])
        self.assertEqual(len(set(selection['complete_selected_ids'])), 15951)
        self.assertEqual(self.bundle['unresolved'], [])
        self.assertEqual([ident for shard in self.bundle['shards'] for ident in shard['selected_source_ids']],
                         selection['complete_selected_ids'])
        self.assertEqual(self.bundle['summary']['zero_outputs'], 8126)
        self.assertEqual(self.bundle['summary']['multi_coordinate_outputs'], 544)
        self.assertFalse(self.bundle['proof_boundary']['actual_map_comparison'])

    def test_missing_reordered_duplicated_or_boolean_source_ids_rejected(self):
        ids = self.bundle['selection']['complete_selected_ids']
        candidates = [ids[:-1], [ids[1], ids[0]] + ids[2:], ids[:-1] + [ids[0]], [False] + ids[1:]]
        for candidate in candidates:
            with self.subTest(candidate_length=len(candidate)), self.assertRaises(ValueError):
                words.batch.validate_candidate(candidate, ids)

    def test_edited_witness_target_relation_and_status_rejected(self):
        idx = next(i for i, e in enumerate(self.bundle['entries']) if e['reduction_steps'] > 1)
        mutations = [
            lambda b: b['entries'][idx]['witness'].clear(),
            lambda b: b['entries'][idx]['targets'].clear(),
            lambda b: b['relation_codes'].__setitem__(0, '0,1'),
            lambda b: b['entries'][idx].__setitem__('status', 'zero'),
            lambda b: b['proof_boundary'].__setitem__('actual_map_comparison', True),
        ]
        for mutate in mutations:
            candidate = copy.deepcopy(self.bundle)
            mutate(candidate)
            with self.assertRaises(ValueError):
                words.batch.validate_candidate(candidate, self.bundle)

    def test_original_manifest_byte_corruption_rejected(self):
        path_name = 'KIP126/LinProgram/Raw/manifest.json'
        with tempfile.TemporaryDirectory() as temp:
            candidate = Path(temp) / 'manifest.json'
            candidate.write_bytes((words.ROOT / path_name).read_bytes() + b'\n')
            with self.assertRaisesRegex(ValueError, 'canonical input mismatch'):
                words.batch.authenticated(path_name, candidate)

    def test_duplicate_json_key_rejected(self):
        with self.assertRaisesRegex(ValueError, 'duplicate JSON field'):
            words.batch.load_json('{"relation":1,"relation":2}')

    def test_single_and_multiple_original_relations(self):
        relations = [dict(rowid=1, rel='0,1;1,1'), dict(rowid=2, rel='1,1;2,1')]
        reducer = words.Reducer(relations, self.low)
        initial, middle, target = (self.low.polynomial(code) for code in ('0,1', '1,1', '2,1'))
        output, witness = reducer.reduce(initial, middle)
        self.assertEqual(output, middle)
        self.assertEqual(len(witness), 1)
        output, witness = reducer.reduce(initial, target)
        self.assertEqual(output, target)
        self.assertEqual(len(witness), 2)
        with self.assertRaisesRegex(ValueError, 'step bound'):
            reducer.reduce(initial, target, max_steps=1)
        with self.assertRaisesRegex(ValueError, 'does not reproduce'):
            reducer.verify(initial, target, witness[:-1])

    def test_unsupported_or_cyclic_reductions_not_replaced_by_zero(self):
        initial, target = (self.low.polynomial(code) for code in ('0,1', '2,1'))
        with self.assertRaisesRegex(ValueError, 'no original leading relation'):
            words.Reducer([], self.low).reduce(initial, target)
        cyclic = [dict(rowid=1, rel='0,1;1,1'), dict(rowid=2, rel='1,1;0,1')]
        with self.assertRaisesRegex(ValueError, 'cycle'):
            words.Reducer(cyclic, self.low).reduce(initial, target)

    def test_unknown_map_image_not_replaced_by_zero(self):
        generators = {0: dict(s=0, t=2)}
        with self.assertRaisesRegex(ValueError, 'missing module generator/image'):
            words.batch.map_word('0', generators, {}, {}, self.low)
        with self.assertRaisesRegex(ValueError, 'NULL image'):
            words.batch.map_word('0', generators, {0: None}, {}, self.low)
        self.assertEqual(words.batch.map_word('0', generators, {0: ''}, {}, self.low)[2], set())

    def test_all_original_relation_locators_and_shard_reindexings(self):
        records = self.bundle['relation_records']
        for record in records:
            index = record['csv_record_index']
            self.assertEqual(record['csv_line_number'], index + 2)
            if index >= 3:
                self.assertEqual(record['chunk_index'] * 1024 + record['chunk_line_index'] + 3, index)
        for shard in self.bundle['shards']:
            rows = self.bundle['entries'][shard['offset']:shard['offset'] + shard['count']]
            expected = sorted({t['relation'] for e in rows for t in e['witness']})
            self.assertEqual(shard['relation_indices'], expected)
            for entry in rows:
                for term in entry['witness']:
                    self.assertEqual(records[term['relation']]['rowid'], term['original_relation_rowid'])

    def test_generated_outputs_match_fresh_rebuild(self):
        expected = words.outputs(self.bundle)
        self.assertEqual(set(expected), {p.name for p in words.DEFAULT_OUTPUT.iterdir() if p.is_file()})
        for name, content in expected.items():
            self.assertEqual((words.DEFAULT_OUTPUT / name).read_text(), content, name)


if __name__ == '__main__':
    unittest.main()
