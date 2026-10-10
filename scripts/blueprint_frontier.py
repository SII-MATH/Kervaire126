#!/usr/bin/env python3
"""Project the active Blueprint DAG into a reproducible scheduling frontier."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

try:
    from .check_external_inputs import blueprint_nodes, blueprint_text
    from .check_source_inventory import strip_unescaped_percent_comments
except ImportError:
    from check_external_inputs import blueprint_nodes, blueprint_text
    from check_source_inventory import strip_unescaped_percent_comments

MATH = 'theorem|proposition|lemma|corollary|definition'
TOKEN = re.compile(r'\\(?:(begin|end)\s*\{(' + MATH + r'|proof)\}|'
                   r'(label|lean|uses|proves)\s*\{([^}]+)\}|'
                   r'(leanok|mathlibok|notready)\b)')


def parse(root: Path) -> dict:
    # Reuse the provenance auditor's active-input/conditional validation.
    _, expected = blueprint_nodes(root)
    text = blueprint_text(root)
    nodes, aliases, stack = {}, {}, []
    last = None
    for match in TOKEN.finditer(text):
        action, env, command, value, flag = match.groups()
        if action == 'begin':
            if env == 'proof':
                if last is None:
                    raise ValueError('proof has no preceding mathematical node')
                item = {'env': env, 'target': last, 'flags': set()}
            else:
                item = {'env': env, 'labels': [], 'lean': set(), 'deps': set(),
                        'flags': set(), 'proof_flags': None}
            stack.append(item)
        elif action == 'end':
            if not stack or stack[-1]['env'] != env:
                raise ValueError(f'unbalanced frontier environment: {env}')
            item = stack.pop()
            if env == 'proof':
                item['target']['proof_flags'] = item['flags']
            else:
                if not item['labels']:
                    raise ValueError(f'unlabelled mathematical node: {env}')
                label = item['labels'][0]
                nodes[label] = item
                for alias in item['labels']:
                    aliases[alias] = label
                last = item
        elif stack:
            item = stack[-1]
            target = item['target'] if item['env'] == 'proof' else item
            if flag:
                item['flags'].add(flag)
            elif command == 'label' and item['env'] != 'proof':
                item['labels'].append(value.strip())
            elif command == 'lean':
                target['lean'].update(x.strip() for x in value.split(',') if x.strip())
            elif command == 'uses':
                target['deps'].update(x.strip() for x in value.split(',') if x.strip())
            elif command == 'proves':
                if item['env'] != 'proof' or value.strip() not in aliases:
                    raise ValueError(f'unknown proof target: {value}')
                item['target'] = nodes[aliases[value.strip()]]
    if stack:
        raise ValueError('unclosed frontier environment')
    if set(aliases) != set(expected):
        raise ValueError('frontier node coverage differs from provenance parser')
    for label, node in nodes.items():
        unknown = node['deps'] - aliases.keys()
        if unknown:
            raise ValueError(f'{label}: unknown dependencies: {sorted(unknown)}')
        node['deps'] = {aliases[x] for x in node['deps']}
        flags = node['flags']
        proof = node['proof_flags']
        node['complete'] = ('notready' not in flags and
                            (proof is None or 'notready' not in proof) and
                            ('mathlibok' in flags or
                             ('leanok' in flags and (proof is None or
                              ('leanok' in proof and 'notready' not in proof)))))
    # Reject even disconnected cycles; an empty frontier must not hide corruption.
    active, done = set(), set()
    def visit(label):
        if label in active:
            raise ValueError(f'Blueprint dependency cycle at {label}')
        if label in done:
            return
        active.add(label)
        for dep in sorted(nodes[label]['deps']):
            visit(dep)
        active.remove(label)
        done.add(label)
    for label in sorted(nodes):
        visit(label)
    return nodes


def metadata(root):
    manifest = root / 'docs/external-inputs.json'
    locators, external = {}, set()
    if not manifest.exists():
        return locators, external
    document = json.loads(manifest.read_text())
    def walk(value):
        if isinstance(value, dict):
            labels = value.get('blueprint_labels', [])
            for label in labels:
                if value.get('locator') or value.get('sources'):
                    locators.setdefault(label, []).append({
                        'sources': value.get('sources', []),
                        'locator': value.get('locator', '')})
                if value.get('proof_status') == 'external-statement-unproved':
                    external.add(label)
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)
    walk(document)
    return locators, external


def make_report(root: Path, issues: list | None = None) -> dict:
    nodes = parse(root)
    locators, external = metadata(root)
    locations = {}
    for path in sorted((root / 'blueprint/src').rglob('*.tex')):
        text = strip_unescaped_percent_comments(path.read_text())
        for match in re.finditer(r'\\label\s*\{([^}]+)\}', text):
            locations[match[1]] = {'file': str(path.relative_to(root)),
                                  'line': text[:match.start()].count('\n') + 1}
    issues = issues or []
    reverse = {label: set() for label in nodes}
    for label, node in nodes.items():
        for dep in node['deps']:
            reverse[dep].add(label)
    def descendants(label):
        found, pending = set(), list(reverse[label])
        while pending:
            x = pending.pop()
            if x not in found:
                found.add(x)
                pending.extend(reverse[x])
        return found
    groups = {k: [] for k in ['frontier', 'external_inputs', 'open_questions',
                              'without_lean_target', 'blocked']}
    for label, node in sorted(nodes.items()):
        if node['complete']:
            continue
        # Source status belongs to the manifest, not to a label's spelling.
        if any(alias in external for alias in node['labels']):
            category = 'external_inputs'
        elif label.startswith(('question:', 'ques:')):
            category = 'open_questions'
        elif not node['lean']:
            category = 'without_lean_target'
        elif all(nodes[dep]['complete'] for dep in node['deps']):
            category = 'frontier'
        else:
            category = 'blocked'
        # Match exact stable labels, not arbitrary title substrings.
        linked = [dict(number=i['number'], url=i['url']) for i in issues
                  if any(re.search(r'(?<![\w:-])' + re.escape(alias) + r'(?![\w:-])',
                                   i.get('body', '') + '\n' + i.get('title', ''))
                         for alias in node['labels'])]
        source_locators = []
        for alias in node['labels']:
            for locator in locators.get(alias, []):
                if locator not in source_locators:
                    source_locators.append(locator)
        groups[category].append({
            'label': label, 'aliases': node['labels'][1:],
            'lean': sorted(node['lean']), 'dependencies': sorted(node['deps']),
            'unfinished_dependencies': sorted(d for d in node['deps'] if not nodes[d]['complete']),
            'potential_dependents': len(descendants(label)),
            'blueprint': locations.get(label), 'source_locators': source_locators,
            'issues': sorted(linked, key=lambda i: i['number']),
        })
    for rows in groups.values():
        rows.sort(key=lambda x: (-x['potential_dependents'], x['label']))
    return {'schema': 1, 'node_count': len(nodes),
            'completed_by_blueprint_markers': sum(n['complete'] for n in nodes.values()),
            'ranking': 'distinct transitive dependents, descending; label, ascending',
            'groups': groups}


def markdown(report, limit=50):
    lines = ['## Blueprint formalization frontier', '',
             'Generated scheduling view; Blueprint markers are not an independent proof audit.',
             'External inputs are review work, not asserted or certified facts.', '',
             f"Nodes: {report['node_count']}; complete by explicit Blueprint markers: "
             f"{report['completed_by_blueprint_markers']}.", '',
             'Rank: distinct transitive dependents (potential reach), then stable label.', '']
    for category, rows in report['groups'].items():
        lines += [f'### {category} ({len(rows)})', '']
        for row in rows[:limit]:
            source = row['blueprint']
            location = f"{source['file']}:{source['line']}" if source else 'location unavailable'
            issues = ', '.join(f"[#{i['number']}]({i['url']})" for i in row['issues']) or 'unassigned'
            citations = '; '.join(', '.join(x['sources']) + ': ' + x['locator']
                                  for x in row['source_locators']) or 'see Blueprint statement/source references'
            lines += [f"- **{row['label']}** — potential dependents: {row['potential_dependents']}; {issues}",
                      f"  - Lean targets: {', '.join(row['lean']) or 'not assigned'}",
                      f"  - Direct dependencies: {', '.join(row['dependencies']) or 'none'}",
                      f"  - Blueprint: {location}", f"  - Source: {citations}"]
        if len(rows) > limit:
            lines += [f'- {len(rows) - limit} further entries in frontier.json.']
        if not rows:
            lines += ['No entries.']
        lines += ['']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--issues', type=Path)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    report = make_report(args.root.resolve(), json.loads(args.issues.read_text()) if args.issues else [])
    # Nothing is published or written until graph validation has succeeded.
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / 'frontier.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    (args.output_dir / 'frontier.md').write_text(markdown(report, limit=50))
    (args.output_dir / 'preview.md').write_text(markdown(report, limit=5))
    print(json.dumps({k: len(v) for k, v in report['groups'].items()}, sort_keys=True))


if __name__ == '__main__':
    main()
