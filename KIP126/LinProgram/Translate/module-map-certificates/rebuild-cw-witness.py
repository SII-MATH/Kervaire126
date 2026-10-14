#!/usr/bin/env python3
"""Rebuild auxiliary CW-to-Ceta relation witnesses from pinned native entities.

These finite polynomial combinations are untrusted inputs to the existing Lean
checker. Python success certifies neither a quotient map nor an actual spectrum
map. No prior audit JSON, reduction log, or generated witness is an input.
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
    spec = importlib.util.spec_from_file_location(
        name, root / 'KIP126/LinProgram/Translate' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def module_term(code):
    require(type(code) is str and bool(code), 'module term must be known and nonempty')
    word = list(map(int, code.split(',')))
    require(len(word) % 2 == 1, 'invalid native module word')
    return tuple(zip(word[:-1:2], word[1:-1:2])), word[-1]


def polynomial(code, module, low):
    require(type(code) is str, 'native image must be a known string, including explicit empty zero')
    value = set()
    for term in code.split(';') if code else []:
        value.symmetric_difference_update({module_term(term) if module else (low.mon(term), None)})
    return value


class NativeRules:
    """Choose the least original row whose recorded leading term divides."""
    def __init__(self, rows, module, low):
        self.low, self.module = low, module
        self.roots, self.polynomials, self.leading = {}, {}, {}
        self.exact, self.memo = {}, {}
        for row in rows:
            rid, code = row['sqlite_rowid'], row['rel']
            lead = module_term(code.split(';')[0]) if module else (low.mon(code.split(';')[0]), None)
            value = polynomial(code, module, low)
            require(rid not in self.leading and lead in value, 'invalid original leading relation')
            self.leading[rid], self.polynomials[rid] = lead, value
            self.exact.setdefault(frozenset(value), rid)
            node = self.roots.setdefault(lead[1], {})
            for pair in lead[0]:
                node = node.setdefault(pair, {})
            node.setdefault(None, rid)

    def divisor(self, monomial, generator=None):
        key = monomial, generator
        if key in self.memo:
            return self.memo[key]
        best = None

        def visit(node, start):
            nonlocal best
            if None in node and (best is None or node[None] < best):
                best = node[None]
            for index in range(start, len(monomial)):
                variable, exponent = monomial[index]
                for power in range(1, exponent + 1):
                    child = node.get((variable, power))
                    if child is not None:
                        visit(child, index + 1)

        if generator in self.roots:
            visit(self.roots[generator], 0)
        answer = None if best is None else (best, self.low.quotient(monomial, self.leading[best][0]))
        self.memo[key] = answer
        return answer


def substitute(code, images, low):
    result = set()
    for coefficient, generator in polynomial(code, True, low):
        require(generator in images, 'source generator has no native image')
        for image_coefficient, target_generator in images[generator]:
            result.symmetric_difference_update({(low.mul(coefficient, image_coefficient), target_generator)})
    return result


def reduce_image(original, ring, module, low):
    pending, trace = set(original), []
    exact = module.exact.get(frozenset(original))
    if exact is not None:
        trace.append({'kind': 'module', 'rowid': exact, 'multiplier': [], 'module_generator': None})
        pending.clear()
    seen = set()
    while pending:
        state = frozenset(pending)
        require(state not in seen and len(trace) < 10000, 'native reduction failed to terminate')
        seen.add(state)
        found = None
        for monomial, generator in sorted(pending, key=lambda item: (item[1], item[0]), reverse=True):
            found = module.divisor(monomial, generator)
            if found is not None:
                kind, rules = 'module', module
            else:
                found = ring.divisor(monomial)
                kind, rules = 'ring', ring
            if found is not None:
                break
        require(found is not None, 'no original leading relation divides the image')
        rid, factor = found
        pending.symmetric_difference_update({(low.mul(factor, coefficient), slot if kind == 'module' else generator)
            for coefficient, slot in rules.polynomials[rid]})
        trace.append({'kind': kind, 'rowid': rid, 'multiplier': factor,
                      'module_generator': generator if kind == 'ring' else None})
    # Replay the emitted identity independently of the reduction state.
    residue = set(original)
    for step in trace:
        rules = module if step['kind'] == 'module' else ring
        residue.symmetric_difference_update({(low.mul(tuple(step['multiplier']), coefficient),
            slot if step['kind'] == 'module' else step['module_generator'])
            for coefficient, slot in rules.polynomials[step['rowid']]})
    require(not residue, 'auxiliary module-ideal identity failed')
    return trace


def rebuild(root):
    native = load(root, 'cw_rebuild_native', 'native-contract.py')
    module_export = load(root, 'cw_rebuild_modules', 'generate-module-presentations.py')
    map_export = load(root, 'cw_rebuild_maps', 'generate-module-maps.py')
    low = native.load_lowstem()
    archive = root / 'Source/LWXMachine/kervaire_database.rar'
    modules = module_export.read_inputs(root, archive)
    module_export.check_outputs(root / 'KIP126/LinProgram/Generated/Modules', module_export.build_outputs(modules))
    graphs = map_export.read_inputs(root, archive)
    graph_outputs = map_export.build_outputs(graphs)
    map_export.check_outputs(root / 'KIP126/LinProgram/Generated/ModuleMaps', graph_outputs)
    map_export.check_registered_outputs(root, graph_outputs)
    source = next(m for m in modules if m['object'] == 'CW_nu_eta')
    target = next(m for m in modules if m['object'] == 'Ceta')
    graph = next(g for g in graphs if g['native_name'] == 'CW_nu_eta__Ceta')
    require((source['generator_count'], source['relation_count'], target['generator_count'],
             target['relation_count']) == (844, 69263, 887, 76569), 'complete native module contract changed')
    require([r['id'] for r in graph['rows']] == list(range(844)), 'incomplete original CW graph')
    path, _, _ = low.pinned('S0_AdamsSS_t261.db')
    db = native.connect(path)
    rows = [dict(r) for r in db.execute('SELECT rowid AS sqlite_rowid,* FROM S0_AdamsE2_relations ORDER BY rowid')]
    db.close()
    require(len(rows) == 231848, 'complete original sphere presentation changed')
    ring, module = NativeRules(rows, False, low), NativeRules(target['relations'], True, low)
    images = {r['id']: polynomial(r['map'], True, low) for r in graph['rows']}
    total_steps, witnessed, formal_zero = 0, 0, 0
    for row in source['relations']:
        original = substitute(row['rel'], images, low)
        if not original:
            formal_zero += 1
            continue
        trace = reduce_image(original, ring, module, low)
        payload = {'source_relation_rowid': row['sqlite_rowid'],
                   'source_degree': [row['s'], row['t']], 'terms': trace}
        yield (json.dumps(payload, separators=(',', ':')) + '\n').encode()
        witnessed += 1
        total_steps += len(trace)
    require((witnessed, formal_zero, total_steps) == (67929, 1334, 238883),
            'complete fixed CW witness contract changed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, help='Optional existing manifest for byte-identity verification')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    start = time.monotonic()
    manifest = json.loads(args.manifest.read_text()) if args.manifest else None
    if manifest is not None:
        require((manifest['all_relation_count'], manifest['generator_count'], manifest['target_generator_count'])
                == (69263, 844, 887), 'wrong CW certificate manifest')
    rebuilt = b''.join(rebuild(args.root.resolve()))
    digest = hashlib.sha256(rebuilt).hexdigest()
    if manifest is not None:
        require(digest == manifest['auxiliary_witness']['sha256'], 'rebuilt witness differs from fixed certificate input')
    if args.check:
        require(args.output.is_file() and args.output.read_bytes() == rebuilt, 'existing witness bytes differ')
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(rebuilt)
    print(json.dumps({'sha256': digest, 'bytes': len(rebuilt), 'source_relations': 69263,
        'nonzero_witnesses': 67929, 'formal_zero_relations': 1334, 'steps': 238883,
        'elapsed_seconds': round(time.monotonic() - start, 2),
        'status': 'untrusted auxiliary witnesses; no Lean or actual-model certification'}, sort_keys=True))


if __name__ == '__main__':
    main()
