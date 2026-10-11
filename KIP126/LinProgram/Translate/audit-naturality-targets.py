#!/usr/bin/env python3
"""Reconstruct the 408 fixed Ceta__S0 targets and genuine logged candidates.

This is a target/premise inventory. Exact native map matching is not a proof of
the source differential, a historical dependency edge, or actual Adams data.
No inverse image is invented and no neighbouring log is accepted by position.
"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
LIN = ROOT / 'KIP126/LinProgram'
OUTPUT = LIN / 'Generated/Naturality/Targets200.json'


def load(filename, name):
    import importlib.util
    spec = importlib.util.spec_from_file_location(name, LIN / 'Translate' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def require(condition, message):
    if not condition:
        raise ValueError(message)


def normalized_source(row, importer):
    """Use the established logger direction convention, without proving it."""
    if row['depth'] != 0 or row['name'] != 'Ceta':
        return None
    if row['reason'] not in importer.FORWARD | importer.INVERSE:
        return None
    r = row['r']
    if type(r) is not int or not 2 <= r < 999:
        return None
    x, dx = importer.coordinates(row['x']), importer.coordinates(row['dx'])
    if x is None or dx is None:
        return None
    s, t = row['s'], row['t']
    if row['reason'] in importer.INVERSE:
        s, t = s - r, t - r + 1
    if not (0 <= s and 2 <= t <= 200 and (t + r - 1 <= 200 or dx == [])):
        return None
    require(row['stem'] == row['t'] - row['s'], 'bad source bidegree')
    return dict(spectrum='Ceta', page=r,
                source=dict(degree=[s, t], coordinates=x),
                target=dict(degree=[s + r, t + r - 1], coordinates=dx))


def is_prior_candidate(raw, source, target):
    return (raw['id'] < target['id'] and source['page'] == target['r'] and
            source['source']['degree'] == [target['s'], target['t'] + 2])


def selected_records(part, catalogue):
    degree = tuple(part['degree'])
    rows = catalogue.get(degree, [])
    coordinates = part['coordinates']
    require(coordinates == sorted(set(coordinates)), 'noncanonical coordinates')
    require(all(type(i) is int and 0 <= i < len(rows) for i in coordinates),
            'coordinate outside original degree catalogue')
    return [rows[i] for i in coordinates]


def sum_images(records, images):
    result = set()
    for row in records:
        require(row['id'] in images, 'missing word image is unknown, not zero')
        result.symmetric_difference_update(images[row['id']]['coordinates'])
    return sorted(result)


def remaining_propositions(source, target):
    a, b = source['source'], source['target']
    return [
        dict(kind='actual-source-differential', spectrum='Ceta', page=source['page'],
             source=a, target=b,
             statement='Prove this Ceta differential on the chosen actual model; the log and staircase only record it.'),
        dict(kind='actual-native-map-comparison', map='Ceta__S0',
             statement='Identify both finite native map values with the actual top-cell map under the same Ceta/sphere comparisons and fixed sphere presentation P.'),
        dict(kind='page-representatives', page=target['r'],
             statement='Prove both native E2 coordinate vectors represent the stated classes on this page and that the page map preserves them.'),
        dict(kind='native-foundations',
             statement='Certify native resolution, comparison, exactness and the chain lift; preserve the full Ceta relation hypotheses before invoking quotient descent.'),
    ]


def rebuild():
    batch = load('replay-naturality-batch.py', 'target_batch')
    scale = load('replay-naturality-words.py', 'target_scale')
    importer = load('import-proofs.py', 'target_importer')
    native = load('native-contract.py', 'target_native')
    low = native.load_lowstem()
    # Regenerate from authenticated original tables: never trust a previous
    # generated bundle, total delivery, or a search-result cache as an input.
    words = scale.rebuild()
    if isinstance(words, tuple):
        words = words[0]
    images = {entry['source']['id']: entry for entry in words['entries']}
    require(len(images) == 15951, 'incomplete original native word image graph')
    _, manifest_bytes, manifest_id = batch.authenticated('KIP126/LinProgram/Raw/manifest.json')
    pinned = {r['path']: r for r in batch.load_json(manifest_bytes.decode())['files']}
    paths, identities = {}, list(words['inputs'])
    for name in ('proofs.db', 'Ceta_AdamsSS_t200.db', 'S0_AdamsSS_t261.db'):
        path, data, digest = low.pinned(name)
        require(digest == pinned[name]['sha256'] and len(data) == pinned[name]['size'],
                'native source disagrees with authenticated manifest: ' + name)
        paths[name] = path
        identity = dict(path='KIP126/LinProgram/Raw/' + name, size=len(data), sha256=digest)
        if identity not in identities:
            identities.append(identity)
    require(manifest_id in identities, 'native manifest identity omitted')
    with native.connect(paths['proofs.db']) as logs:
        selected = []
        index = 0
        for raw in logs.execute("SELECT * FROM log WHERE depth=0 AND name='S0' ORDER BY id"):
            row = dict(raw)
            disposition, interpreted = importer.classify(row)
            if interpreted is not None:
                if row['reason'] == 'N' and row['info'] == 'Ceta__S0':
                    selected.append((row, dict(shard=index // importer.SHARD_SIZE,
                                               offset=index % importer.SHARD_SIZE)))
                index += 1
        all_source_logs = [dict(r) for r in logs.execute(
            "SELECT * FROM log WHERE depth=0 AND name='Ceta' ORDER BY id")]
        log_schema = [dict(r) for r in logs.execute('PRAGMA table_xinfo(log)')]
    require(index == 10907 and len(selected) == 408, 'fixed importer target selection changed')
    candidates, source_dispositions = defaultdict(list), Counter()
    for row in all_source_logs:
        equation = normalized_source(row, importer)
        source_dispositions['supported-known-finite' if equation is not None else 'uninterpreted'] += 1
        if equation is not None:
            candidates[(equation['page'], *equation['source']['degree'])].append((row, equation))
    with native.connect(paths['Ceta_AdamsSS_t200.db']) as ceta, native.connect(paths['S0_AdamsSS_t261.db']) as sphere:
        ceta_rows = batch.catalogue(ceta, 'Ceta', 200)
        sphere_rows = batch.catalogue(sphere, 'S0', 261)
        staircase = [dict(r) for r in ceta.execute('SELECT * FROM Ceta_AdamsE2_ss ORDER BY id')]
    by_ceta, by_sphere = defaultdict(list), defaultdict(list)
    for row in ceta_rows:
        by_ceta[(row['s'], row['t'])].append(row)
    for row in sphere_rows:
        by_sphere[(row['s'], row['t'])].append(row)
    stair_index = defaultdict(list)
    for row in staircase:
        stair_index[row['s'], row['t'], row['base'], row['diff'], row['level']].append(row)
    entries, used_words, statuses = [], set(), Counter()
    for target, location in selected:
        target_eq = native.equation(target)
        target_rows = {side: selected_records(target_eq[side], by_sphere) for side in ('source', 'target')}
        s, t, r = target['s'], target['t'], target['r']
        matched, comparisons = [], []
        for raw, eq in candidates[(r, s, t + 2)]:
            if not is_prior_candidate(raw, eq, target):
                continue
            endpoint_results = {}
            for side in ('source', 'target'):
                source_rows = selected_records(eq[side], by_ceta)
                used_words.update(row['id'] for row in source_rows)
                coords = sum_images(source_rows, images)
                endpoint_results[side] = dict(
                    ceta_basis_ids=[row['id'] for row in source_rows],
                    native_mapped_coordinates=coords,
                    desired_coordinates=target_eq[side]['coordinates'],
                    exact_E2_coordinate_match=coords == target_eq[side]['coordinates'])
            exact = all(e['exact_E2_coordinate_match'] for e in endpoint_results.values())
            if exact:
                matched.append(raw['id'])
            xs = ','.join(map(str, eq['source']['coordinates']))
            ys = ','.join(map(str, eq['target']['coordinates']))
            ds, dt = eq['target']['degree']
            comparisons.append(dict(raw_log=raw, equation=eq,
                endpoint_images=endpoint_results,
                comparison='exact-native-E2-match' if exact else 'requires-page-representative-or-source-comparison',
                reciprocal_staircase_records=dict(
                    outgoing=stair_index[s, t + 2, xs, ys, 10000 - r],
                    incoming=stair_index[ds, dt, ys, xs, r]),
                native_vector_maximum_t=max([0] + [eq[side]['degree'][1] for side in ('source', 'target') if eq[side]['coordinates']]),
                actual_source_differential_proved=False,
                historical_premise_edge_certified=False,
                remaining_propositions=remaining_propositions(eq, target)))
        status = ('one-exact-recorded-candidate' if len(matched) == 1 else
                  'multiple-exact-recorded-candidates' if matched else
                  'recorded-candidates-need-page-comparison' if comparisons else
                  'no-supported-earlier-source-record')
        statuses[status] += 1
        vector_bound = min([c['native_vector_maximum_t'] for c in comparisons if c['raw_log']['id'] in matched], default=None)
        entries.append(dict(raw_log=target, exported_lean_location=location, equation=target_eq,
            sphere_endpoint_basis={side: [batch.basis_record(row) for row in rows] for side, rows in target_rows.items()},
            required_ceta_degrees=dict(source=[s, t + 2], target=[s + r, t + r + 1]),
            chain_data_requirement=dict(
                formal_endpoint_scope=dict(ceta_maximum_t=t + r + 1, sphere_maximum_t=t + r - 1),
                nonzero_coordinate_requirement=dict(ceta_maximum_t=vector_bound,
                    sphere_maximum_t=max(0, vector_bound - 2) if vector_bound is not None else None,
                    exact_candidate_ids_at_this_bound=[c['raw_log']['id'] for c in comparisons if c['raw_log']['id'] in matched and c['native_vector_maximum_t'] == vector_bound],
                    meaning='minimum native vector bound among exact recorded candidates; unknown without one; no actual source proof inferred'),
                explicit_zero_target=(target_eq['target']['coordinates'] == []),
                covered_by_pinned_Batch21=(vector_bound is not None and vector_bound <= 21)),
            native_target_degree_above_table=(t + r + 1 > 200),
            least_exact_candidate_vector_bound=vector_bound,
            recorded_source_candidates=comparisons, exact_candidate_ids=matched, status=status,
            historical_source_row_id=None, historical_premise_edge_certified=False,
            actual_certification=False))
    current = [row['raw_log']['id'] for row in entries if row['chain_data_requirement']['covered_by_pinned_Batch21']]
    require(current == [245131], 'Batch21 endpoint coverage changed')
    relevant_words = [images[i] for i in sorted(used_words)]
    windows, vector_windows = {}, {}
    for limit in (21, 40, 60, 100, 150, 200):
        group = [e for e in entries if e['chain_data_requirement']['formal_endpoint_scope']['ceta_maximum_t'] <= limit]
        windows[str(limit)] = dict(target_count=len(group), target_ids=[e['raw_log']['id'] for e in group],
            with_exact_native_source_candidate=sum(bool(e['exact_candidate_ids']) for e in group))
        vector_group = [e for e in entries if e['least_exact_candidate_vector_bound'] is not None and e['least_exact_candidate_vector_bound'] <= limit]
        vector_windows[str(limit)] = dict(target_count=len(vector_group), target_ids=[e['raw_log']['id'] for e in vector_group],
            meaning='exact recorded candidate map values only; source differential and actual comparison remain unproved')
    return dict(schema_version=1, kind='fixed-native-Ceta-top-cell-naturality-target-inventory',
        canonical_registry='docs/external-inputs.json', inputs=identities,
        selection=dict(map='Ceta__S0', spectrum='S0', count=len(entries),
            filter='import-proofs.py classify on depth=0 S0 rows; retain reason=N, info=Ceta__S0',
            complete_selected_ids=[e['raw_log']['id'] for e in entries]),
        source_candidate_selection=dict(known_finite_supported_root_Ceta_logs=True,
            source_degree='(s,t+2)', target_degree='(s+r,t+r+1)',
            same_page=True, strictly_earlier_log_id=True,
            native_degree_coverage='source t<=200; nonempty target t<=200; known empty targets retain their full degree even above 200',
            adjacency_used_as_evidence=False, invented_inverse_images=False,
            dispositions=dict(source_dispositions)),
        log_schema=log_schema, native_map=words['native_map'], entries=entries,
        word_image_certificates=relevant_words, relation_codes=words['relation_codes'],
        relation_records=words['relation_records'],
        summary=dict(targets=len(entries), candidate_equations=sum(len(e['recorded_source_candidates']) for e in entries),
            referenced_word_images=len(relevant_words), statuses=dict(sorted(statuses.items())),
            formal_degree_windows=windows, nonzero_coordinate_windows=vector_windows, Batch21_covered_target_ids=current,
            formal_target_above_native_table_ids=[e['raw_log']['id'] for e in entries if e['native_target_degree_above_table']]),
        proof_boundary=dict(native_word_reconstruction='deterministic polynomial witness search; Lean verification is separate',
            missing_exact_match='May require E_r boundary/representative reduction; it is not a disproof.',
            source_record='A recorded source candidate is not a proved differential.',
            historical_dependency='The original log has no source-ID or premise-edge field; no historical edge is certified.',
            actual_model_comparison=False, actual_differential=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = rebuild()
    data = json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False) + '\n'
    if args.check:
        require(args.output.read_text() == data, 'target inventory differs from fixed-input reconstruction')
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(data)
    print(json.dumps({k: v for k, v in result['summary'].items() if not k.endswith('_windows')}, ensure_ascii=False, sort_keys=True))


if __name__ == '__main__':
    main()
