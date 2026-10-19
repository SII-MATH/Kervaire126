#!/usr/bin/env python3
"""Rebuild untrusted complete Ceta relation-image witnesses from pinned entities.
This produces F2 ring-ideal combinations, not a C++ trace or actual map proof.
The production Lean generator independently replays every emitted combination.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import time


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load(root, name, filename):
    path = root / 'KIP126/LinProgram/Translate' / filename
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class NativeRingRules:
    """The least native relation row whose recorded leading monomial divides."""
    def __init__(self, rows, low):
        self.low = low
        self.roots = {}
        self.polynomials = {}
        self.leading = {}
        self.exact = {}
        self.memo = {}
        for row in rows:
            rid = row['sqlite_rowid']
            terms = row['rel'].split(';')
            lead = low.mon(terms[0])
            value = set()
            for term in terms:
                value.symmetric_difference_update({low.mon(term)})
            self.leading[rid] = lead
            self.polynomials[rid] = value
            self.exact.setdefault(frozenset(value), rid)
            node = self.roots
            for pair in lead:
                node = node.setdefault(pair, {})
            node.setdefault(None, rid)

    def divisor(self, monomial):
        if monomial in self.memo:
            return self.memo[monomial]
        best = None
        def visit(node, start):
            nonlocal best
            if None in node and (best is None or node[None] < best):
                best = node[None]
            for index in range(start, len(monomial)):
                generator, exponent = monomial[index]
                for power in range(1, exponent + 1):
                    child = node.get((generator, power))
                    if child is not None:
                        visit(child, index + 1)
        visit(self.roots, 0)
        answer = None if best is None else (best, self.low.quotient(monomial, self.leading[best]))
        self.memo[monomial] = answer
        return answer


def rebuild(root):
    native = load(root, 'ceta_rebuild_native', 'native-contract.py')
    module_export = load(root, 'ceta_rebuild_modules', 'generate-module-presentations.py')
    map_export = load(root, 'ceta_rebuild_maps', 'generate-module-maps.py')
    low = native.load_lowstem()
    archive = root / 'Source/LWXMachine/kervaire_database.rar'
    modules = module_export.read_inputs(root, archive)
    module_export.check_outputs(root / 'KIP126/LinProgram/Generated/Modules', module_export.build_outputs(modules))
    graphs = map_export.read_inputs(root, archive)
    graph_outputs = map_export.build_outputs(graphs)
    map_export.check_outputs(root / 'KIP126/LinProgram/Generated/ModuleMaps', graph_outputs)
    map_export.check_registered_outputs(root, graph_outputs)
    ceta = next(m for m in modules if m['object'] == 'Ceta')
    graph = next(g for g in graphs if g['native_name'] == 'Ceta__S0')
    require(ceta['generator_count'] == 887 and ceta['relation_count'] == 76569, 'complete Ceta contract changed')
    require([r['id'] for r in graph['rows']] == list(range(887)), 'incomplete original graph')
    path, _, _ = low.pinned('S0_AdamsSS_t261.db')
    db = native.connect(path)
    rows = [dict(r) for r in db.execute('SELECT rowid AS sqlite_rowid,* FROM S0_AdamsE2_relations ORDER BY rowid')]
    db.close()
    require(len(rows) == 231848, 'original complete sphere presentation changed')
    rules = NativeRingRules(rows, low)
    images = {}
    for row in graph['rows']:
        value = set()
        for term in row['map'].split(';') if row['map'] else []:
            value.symmetric_difference_update({low.mon(term)})
        images[row['id']] = value
    total_steps = 0
    witnessed = 0
    formal_zero = 0
    for row in ceta['relations']:
        original = set()
        for term in row['rel'].split(';'):
            word = list(map(int, term.split(',')))
            require(len(word) % 2 == 1 and word[-1] in images, 'invalid native module word')
            coefficient = tuple(zip(word[:-1:2], word[1:-1:2]))
            for image in images[word[-1]]:
                original.symmetric_difference_update({low.mul(coefficient, image)})
        if not original:
            formal_zero += 1
            continue
        pending = set(original)
        trace = []
        exact = rules.exact.get(frozenset(original))
        if exact is not None:
            trace.append({'kind': 'ring', 'rowid': exact, 'multiplier': [], 'module_generator': None})
            pending.clear()
        else:
            seen = set()
            while pending:
                state = frozenset(pending)
                require(state not in seen and len(trace) < 10000, 'reduction failed to terminate')
                seen.add(state)
                found = None
                for monomial in sorted(pending, reverse=True):
                    found = rules.divisor(monomial)
                    if found is not None:
                        break
                require(found is not None, 'no native leading divisor at source row ' + str(row['sqlite_rowid']))
                rid, factor = found
                pending.symmetric_difference_update({low.mul(factor, monomial) for monomial in rules.polynomials[rid]})
                trace.append({'kind': 'ring', 'rowid': rid, 'multiplier': factor, 'module_generator': None})
        # Check the emitted finite identity separately from the reduction state.
        residue = set(original)
        for step in trace:
            residue.symmetric_difference_update({low.mul(tuple(step['multiplier']), monomial)
                for monomial in rules.polynomials[step['rowid']]})
        require(not residue, 'auxiliary ring-ideal identity failed')
        payload = {'source_relation_rowid': row['sqlite_rowid'], 'source_degree': [row['s'], row['t']], 'terms': trace}
        yield (json.dumps(payload, separators=(',', ':')) + '\n').encode()
        witnessed += 1
        total_steps += len(trace)
    require(witnessed == 75347 and formal_zero == 1222 and total_steps == 167453,
            'complete fixed witness contract changed')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--manifest', type=Path, help='Optional existing certificate manifest for byte-identity verification')
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    start = time.monotonic()
    manifest = json.loads(args.manifest.read_text()) if args.manifest else None
    if manifest is not None:
        require(manifest['all_relation_count'] == 76569 and manifest['generator_count'] == 887, 'wrong certificate manifest')
    rebuilt = b''.join(rebuild(args.root.resolve()))
    digest = hashlib.sha256(rebuilt).hexdigest()
    if manifest is not None:
        require(digest == manifest['auxiliary_witness']['sha256'], 'rebuilt witness differs from fixed certificate input')
    if args.check:
        require(args.output.is_file() and args.output.read_bytes() == rebuilt, 'existing witness bytes differ')
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(rebuilt)
    print(json.dumps({'sha256': digest, 'bytes': len(rebuilt), 'source_relations': 76569,
        'nonzero_witnesses': 75347, 'formal_zero_relations': 1222, 'steps': 167453,
        'elapsed_seconds': round(time.monotonic() - start, 2),
        'status': 'untrusted auxiliary witnesses; no Lean or actual-model certification'}, sort_keys=True))


if __name__ == '__main__':
    main()
