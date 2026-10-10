"""DAG corruption and proof-status semantics regression checks."""
import json
from pathlib import Path
import tempfile
import unittest

from scripts.blueprint_frontier import make_report


class FrontierTests(unittest.TestCase):
    def report(self, source, manifest=None, issues=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'blueprint/src').mkdir(parents=True)
            (root / 'blueprint/src/content.tex').write_text(source)
            if manifest is not None:
                (root / 'docs').mkdir()
                (root / 'docs/external-inputs.json').write_text(json.dumps(manifest))
            return make_report(root, issues)

    def node(self, label, deps='', flags=r'\notready', lean='KIP126.example', env='definition'):
        return (rf'\begin{{{env}}}\label{{{label}}}\lean{{{lean}}}\uses{{{deps}}}'
                + flags + rf'\end{{{env}}}')

    def test_frontier_requires_completed_dependencies_and_target(self):
        source = self.node('done', flags=r'\leanok') + self.node('todo', 'done')
        source += self.node('blocked', 'todo') + self.node('missing', lean='')
        report = self.report(source)
        self.assertEqual([r['label'] for r in report['groups']['frontier']], ['todo'])
        self.assertEqual(report['groups']['frontier'][0]['potential_dependents'], 1)
        self.assertEqual([r['label'] for r in report['groups']['blocked']], ['blocked'])
        self.assertEqual([r['label'] for r in report['groups']['without_lean_target']], ['missing'])

    def test_unknown_dependencies_and_disconnected_cycles_fail_closed(self):
        for source, error in [(self.node('one', 'absent'), 'unknown dependencies'),
                              (self.node('one', 'two') + self.node('two', 'one'), 'cycle')]:
            with self.subTest(error=error), self.assertRaisesRegex(ValueError, error):
                self.report(source)

    def test_proof_dependencies_and_proof_status_are_not_erased(self):
        source = self.node('base') + self.node('claim', flags=r'\leanok', env='theorem')
        source += r'\begin{proof}\uses{base}\notready\end{proof}'
        report = self.report(source)
        self.assertEqual(report['completed_by_blueprint_markers'], 0)
        self.assertEqual(report['groups']['blocked'][0]['dependencies'], ['base'])

    def test_aliases_and_duplicate_labels(self):
        source = self.node('one', flags=r'\label{alias}\leanok') + self.node('two', 'alias')
        row = self.report(source)['groups']['frontier'][0]
        self.assertEqual(row['dependencies'], ['one'])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            self.report(self.node('one') + self.node('one'))

    def test_external_inputs_do_not_satisfy_dependencies_or_become_frontier(self):
        source = self.node('external') + self.node('consumer', 'external')
        manifest = {'rows': [{'blueprint_labels': ['external'], 'sources': ['paper'],
                             'locator': 'Theorem 1', 'proof_status': 'external-statement-unproved'}]}
        report = self.report(source, manifest)
        self.assertEqual(report['groups']['frontier'], [])
        self.assertEqual(report['groups']['external_inputs'][0]['source_locators'][0]['locator'], 'Theorem 1')
        self.assertEqual(report['groups']['blocked'][0]['label'], 'consumer')

    def test_internal_evidence_and_data_use_targets_and_dependencies(self):
        for prefix in ('evidence:', 'data:'):
            with self.subTest(prefix=prefix):
                source = self.node('done', flags=r'\leanok')
                source += self.node(prefix + 'ready', 'done')
                source += self.node(prefix + 'blocked', prefix + 'ready')
                source += self.node(prefix + 'missing', lean='')
                manifest = {'rows': [{
                    'blueprint_labels': [prefix + 'ready'], 'sources': ['paper'],
                    'locator': 'Theorem 2', 'proof_status': 'internal-application-obligation'}]}
                groups = self.report(source, manifest)['groups']
                self.assertEqual(groups['external_inputs'], [])
                self.assertEqual([r['label'] for r in groups['frontier']], [prefix + 'ready'])
                self.assertEqual([r['label'] for r in groups['blocked']], [prefix + 'blocked'])
                self.assertEqual([r['label'] for r in groups['without_lean_target']], [prefix + 'missing'])
                self.assertEqual(groups['frontier'][0]['source_locators'][0]['locator'], 'Theorem 2')

    def test_external_status_and_locators_follow_node_aliases(self):
        source = self.node('primary', flags=r'\label{external-alias}\notready')
        source += self.node('consumer', 'external-alias')
        manifest = {'rows': [
            {'blueprint_labels': ['external-alias'], 'sources': ['paper'],
             'locator': 'Theorem 1', 'proof_status': 'external-statement-unproved'},
            {'blueprint_labels': ['primary', 'external-alias'], 'sources': ['paper'],
             'locator': 'Theorem 1'}]}
        groups = self.report(source, manifest)['groups']
        self.assertEqual(groups['frontier'], [])
        self.assertEqual(groups['blocked'][0]['dependencies'], ['primary'])
        self.assertEqual(groups['external_inputs'][0]['label'], 'primary')
        self.assertEqual(groups['external_inputs'][0]['source_locators'], [
            {'sources': ['paper'], 'locator': 'Theorem 1'}])

    def test_notready_overrides_completion(self):
        report = self.report(self.node('one', flags=r'\leanok\notready'))
        self.assertEqual(report['completed_by_blueprint_markers'], 0)

    def test_issue_mapping_uses_exact_label_and_output_is_deterministic(self):
        source = self.node('def:one')
        issues = [{'number': 1, 'url': 'https://example.com/1', 'body': 'def:one-more'},
                  {'number': 2, 'url': 'https://example.com/2', 'body': '`def:one`'}]
        report = self.report(source, issues=issues)
        self.assertEqual(report['groups']['frontier'][0]['issues'][0]['number'], 2)
        self.assertEqual(len(report['groups']['frontier'][0]['issues']), 1)
        self.assertEqual(report, self.report(source, issues=issues))

    def test_ranking_counts_distinct_dependents_in_diamond(self):
        source = self.node('root') + self.node('a', 'root') + self.node('b', 'root') + self.node('c', 'a,b')
        self.assertEqual(self.report(source)['groups']['frontier'][0]['potential_dependents'], 3)


if __name__ == "__main__":
    unittest.main()
