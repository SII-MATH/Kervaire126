#!/usr/bin/env python3
"""Replay every original Ceta basis record with 2 <= t <= 21.

Pinned native words and new bounded chain data are different inputs. Polynomial
certificates and cochain augmentations do not identify either with actual Ext,
prove resolution exactness, descend the whole quotient, or prove a differential.
"""
import argparse
from collections import Counter, defaultdict
import csv
import io
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
LIN = ROOT / 'KIP126/LinProgram'
DEFAULT_OUTPUT = LIN / 'Generated/Naturality'
RAW_INPUTS = ('S0_AdamsSS_t261.db', 'Ceta_AdamsSS_t200.db',
              'map_AdamsSS_Ceta_to_S0_t200.db', 'ss.json', 'S0_AdamsE2_relations.csv')
CHAIN_INPUTS = {
    'ceta': 'KIP126/LinProgram/Raw/Naturality/Batch21/Ceta_Adams_res.db',
    'map': 'KIP126/LinProgram/Raw/Naturality/Batch21/map_Adams_res_Ceta__S0.db',
    'sphere': 'KIP126/LinProgram/Raw/Secondary/Seed5487/S0_Adams_res.db',
    'config': 'Source/LWXMachine/Adams.json',
}
LIMIT = 21


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(filename, name):
    spec = importlib.util.spec_from_file_location(name, LIN / 'Translate' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'), allow_nan=False)


def load_json(text):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicate JSON field: ' + key)
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError('nonfinite JSON value')))


def authenticated(path_name, override=None):
    """Canonical artifact identity, with strict worktree-aware LFS resolution."""
    registry = load_json((ROOT / 'docs/external-inputs.json').read_text())
    records = [a for source in registry['sources'] for a in source.get('artifacts', [])
               if a.get('path') == path_name]
    require(len(records) == 1, 'input must have exactly one canonical artifact: ' + path_name)
    entry = records[0]
    path = override if override is not None else ROOT / path_name
    data = path.read_bytes()
    if data.startswith(b'version https://git-lfs.github.com/spec/v1'):
        pointer = re.fullmatch(rb'version https://git-lfs.github.com/spec/v1\noid sha256:([0-9a-f]{64})\nsize ([0-9]+)\n', data)
        require(pointer is not None, 'malformed LFS pointer: ' + path_name)
        digest, size = pointer[1].decode(), int(pointer[2])
        require(digest == entry['sha256'] and size == entry['size'], 'LFS identity mismatch: ' + path_name)
        common = Path(subprocess.check_output(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'], cwd=ROOT, text=True).strip())
        path = common / 'lfs/objects' / digest[:2] / digest[2:4] / digest
        data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    require(digest == entry['sha256'] and ('size' not in entry or len(data) == entry['size']), 'canonical input mismatch: ' + path_name)
    return path, data, dict(path=path_name, size=len(data), sha256=digest)


def basis_record(row):
    return dict(id=row['id'], s=row['s'], t=row['t'], local_index=row['local_index'], code=row['mon'])


def catalogue(db, prefix, bound):
    rows = [dict(row) for row in db.execute(f'SELECT * FROM {prefix}_AdamsE2_basis WHERE t<=? ORDER BY id', (bound,))]
    counters = Counter()
    for row in rows:
        degree = row['s'], row['t']
        row['local_index'] = counters[degree]
        counters[degree] += 1
    require(len({row['id'] for row in rows}) == len(rows), 'duplicate basis record')
    return rows


def polynomial_list(poly):
    return [[i for i, a in monomial for _ in range(a)] for monomial in sorted(poly)]


def map_word(code, module_generators, images, ring_generators, low):
    require(type(code) is str and re.fullmatch(r'[0-9]+(?:,[0-9]+)*', code), 'invalid module word')
    numbers = list(map(int, code.split(',')))
    require(len(numbers) % 2 == 1, 'module word does not terminate in a generator')
    generator = numbers[-1]
    require(generator in module_generators and generator in images, 'missing module generator/image')
    coefficient = low.mon(','.join(map(str, numbers[:-1])))
    degree = [module_generators[generator][k] for k in ('s', 't')]
    for i, exponent in coefficient:
        require(i in ring_generators, 'unknown coefficient variable')
        for j, k in enumerate(('s', 't')):
            degree[j] += exponent * ring_generators[i][k]
    image = images[generator]
    require(type(image) is str, 'NULL image is unknown, not zero')
    image_poly = low.polynomial(image) if image else set()
    for term in image_poly:
        actual = [0, 0]
        for i, exponent in term:
            require(i in ring_generators, 'unknown image variable')
            for j, k in enumerate(('s', 't')):
                actual[j] += exponent * ring_generators[i][k]
        require(actual == [module_generators[generator]['s'], module_generators[generator]['t'] - 2], 'inhomogeneous generator image')
    return generator, coefficient, {low.mul(coefficient, term) for term in image_poly}, degree


def reduce_to_basis(poly, targets, relations, low):
    """Find direct equality or a single monomial multiple of an original relation.

    No target or relation is encoded in the search. Unsupported reductions fail;
    they are never accepted as zero or replaced by a smaller quotient.
    """
    indices = {low.mon(row['mon']): row for row in targets}
    require(len(indices) == len(targets), 'duplicate target monomial')
    if all(m in indices for m in poly):
        return sorted((indices[m] for m in poly), key=lambda r: r['local_index']), [], None
    for relation in relations:
        relation_poly = low.polynomial(relation['rel'])
        multipliers = sorted({low.quotient(m, lead) for m in poly for lead in relation_poly if low.divides(lead, m)})
        for multiplier in multipliers:
            rhs = poly.symmetric_difference({low.mul(multiplier, term) for term in relation_poly})
            if all(m in indices for m in rhs):
                result = sorted((indices[m] for m in rhs), key=lambda r: r['local_index'])
                return result, polynomial_list({multiplier}), relation
    raise ValueError('no supported original-relation certificate for target degree')


def rebuild_words():
    native = load('native-contract.py', 'naturality_native_contract')
    low = native.load_lowstem()
    native.validate_ceta_archive_origin(load_json((LIN / 'Raw/manifest.json').read_text()))
    _, manifest_bytes, manifest_identity = authenticated('KIP126/LinProgram/Raw/manifest.json')
    pinned_manifest = load_json(manifest_bytes.decode())
    pinned_entries = {entry['path']: entry for entry in pinned_manifest['files']}
    paths, identities, payloads = {}, [manifest_identity], {}
    registry = load_json((ROOT / 'docs/external-inputs.json').read_text())
    separately_registered = {a['path'] for source in registry['sources'] for a in source.get('artifacts', [])}
    for name in RAW_INPUTS:
        path, data, digest = low.pinned(name)
        entry = pinned_entries[name]
        require(digest == entry['sha256'] and len(data) == entry['size'], 'native and authenticated Raw manifest disagree')
        identity = dict(path='KIP126/LinProgram/Raw/' + name, size=len(data), sha256=digest)
        if identity['path'] in separately_registered:
            _, separately_checked, _ = authenticated(identity['path'])
            require(data == separately_checked, 'native and canonical artifact disagree')
        paths[name], payloads[name] = path, data
        identities.append(identity)
    configuration = load_json(payloads['ss.json'].decode())
    mappings = [row for row in configuration['maps'] if row['name'] == 'Ceta__S0']
    require(len(mappings) == 1, 'ambiguous native map')
    mapping = mappings[0]
    require((mapping['from'], mapping['to'], mapping['sus'], mapping['type']) == ('Ceta', 'S0', 2, 'top_cell'), 'native map contract changed')
    with native.connect(paths['Ceta_AdamsSS_t200.db']) as ceta, native.connect(paths['S0_AdamsSS_t261.db']) as sphere, native.connect(paths['map_AdamsSS_Ceta_to_S0_t200.db']) as maps:
        all_sources = catalogue(ceta, 'Ceta', LIMIT)
        selected = [row for row in all_sources if row['t'] >= 2]
        targets = catalogue(sphere, 'S0', LIMIT - 2)
        by_degree = defaultdict(list)
        for row in targets:
            by_degree[row['s'], row['t']].append(row)
        module_generators = {row['id']: dict(row) for row in ceta.execute('SELECT * FROM Ceta_AdamsE2_generators ORDER BY id')}
        ring_generators = {row['id']: dict(row) for row in sphere.execute('SELECT * FROM S0_AdamsE2_generators ORDER BY id')}
        images = {row['id']: row['map'] for row in maps.execute('SELECT * FROM map_AdamsE2_Ceta_to_S0 ORDER BY id')}
        require(set(module_generators) == set(images), 'native map graph is incomplete')
        relations = [dict(row) for row in sphere.execute('SELECT rowid,rel,s,t FROM S0_AdamsE2_relations WHERE t<=? ORDER BY rowid', (LIMIT - 2,))]
        metadata = [dict(row) for row in maps.execute('SELECT * FROM version ORDER BY id')]
        md = {row['name']: row['value'] for row in metadata}
        require((md.get('from'), md.get('to'), md.get('filtration'), md.get('suspension'), md.get('t_max')) == ('Ceta', 'S0', 0, 2, mapping['t_max']), 'map database metadata mismatch')
    require(len(selected) == 82, 'fixed degree window no longer contains 82 original records')
    entries, used_relations, statuses = [], [], Counter()
    for row in selected:
        generator, coefficient, poly, degree = map_word(row['mon'], module_generators, images, ring_generators, low)
        require(degree == [row['s'], row['t']], 'source monomial degree mismatch')
        target_degree = row['s'], row['t'] - 2
        basis = by_degree[target_degree]
        reduced, multiplier, relation = reduce_to_basis(poly, basis, [r for r in relations if r['s'] <= target_degree[0] and r['t'] <= target_degree[1]], low)
        witness = []
        if relation is not None:
            if relation not in used_relations:
                used_relations.append(relation)
            witness = [dict(relation=used_relations.index(relation), multiplier=multiplier)]
        status = 'relation-reduced' if witness else ('zero' if not reduced else 'direct-singleton')
        statuses[status] += 1
        entries.append(dict(source=basis_record(row), source_repr=row['repr'], generator_id=generator,
                            generator_image=images[generator], substituted_polynomial=polynomial_list(poly),
                            target_s=target_degree[0], target_t=target_degree[1],
                            targets=[basis_record(r) for r in reduced], target_reprs=[r['repr'] for r in reduced],
                            coordinates=[r['local_index'] for r in reduced], witness=witness, status=status))
    csv_relations = list(csv.DictReader(io.StringIO(payloads['S0_AdamsE2_relations.csv'].decode('utf-16'))))
    for relation in used_relations:
        matches = [i for i, row in enumerate(csv_relations) if
                   row['rel'] == relation['rel'] and int(row['s']) == relation['s'] and
                   int(row['stem']) + int(row['s']) == relation['t']]
        require(len(matches) == 1, 'used database relation lacks unique original CSV membership')
        relation['csv_record_index'] = matches[0]
        relation['csv_line_number'] = matches[0] + 2
        relation['csv_path'] = 'KIP126/LinProgram/Raw/S0_AdamsE2_relations.csv'
    matrices = []
    for s, t in sorted({(entry['source']['s'], entry['source']['t']) for entry in entries}):
        columns = [entry for entry in entries if (entry['source']['s'], entry['source']['t']) == (s, t)]
        rows = by_degree[s, t - 2]
        matrices.append(dict(source_degree=[s, t], target_degree=[s, t - 2],
                             source_ids=[e['source']['id'] for e in columns], target_basis=[basis_record(r) for r in rows],
                             columns=[e['coordinates'] for e in columns],
                             rows=[[int(r['local_index'] in e['coordinates']) for e in columns] for r in rows]))
    bundle = dict(schema_version=1, kind='fixed-native-Ceta-top-cell-word-batch',
                  canonical_registry='docs/external-inputs.json', inputs=identities, native_map=mapping,
                  selection=dict(spectrum='Ceta', minimum_t=2, maximum_t=LIMIT,
                                 complete_selected_ids=[r['id'] for r in selected], count=len(selected)),
                  relation_codes=[r['rel'] for r in used_relations], relation_records=used_relations,
                  entries=entries, complete_degree_matrices=matrices, summary=dict(sorted(statuses.items())),
                  proof_boundary=dict(word_equalities='finite certificate inputs; kernel checking is separate',
                                      source_basis_identity='authenticated transcription, not a basis theorem',
                                      quotient_descent='requires all 76569 original Ceta relation equations',
                                      actual_map_comparison=False, actual_differential=False,
                                      historical_premise_edge_certified=False))
    return bundle, selected, all_sources, targets


def chain_rows(native, decoder, path, prefix, cutoff):
    with native.connect(path) as db:
        raw = [dict(row) for row in db.execute(f'SELECT id,s,t,diff FROM {prefix}_Adams_res_generators WHERE t<=? ORDER BY id', (cutoff,))]
    result = []
    for row in raw:
        require(type(row['diff']) is bytes and len(row['diff']) % 8 == 0, 'unknown or malformed resolution differential')
        require(row['id'] >> 19 == row['s'], 'resolution LocId filtration mismatch')
        terms = decoder.decode(row['diff'])
        result.append(dict(id=row['id'], s=row['s'], t=row['t'], local_id=row['id'] % (1 << 19), decoded=terms))
    return result


def indexed_terms(decoded, filtration, index, rows, decoder, total_degree):
    result = []
    for powers, local in sorted(decoded):
        global_id = (filtration << 19) + local
        require(global_id in index, 'referenced chain generator is missing, not zero')
        j = index[global_id]
        require(rows[j]['s'] == filtration and decoder.degree(powers) + rows[j]['t'] == total_degree,
                'chain term has inconsistent filtration or internal degree')
        result.append(dict(powers=list(powers), generator=j))
    return result


def rebuild_cochains(word_bundle, selected, all_native_ceta, native_sphere, chain_dir=None):
    native = load('native-contract.py', 'naturality_chain_native')
    decoder = load('extract-secondary-witness.py', 'naturality_chain_decode')
    paths, identities = {}, []
    for key, path_name in CHAIN_INPUTS.items():
        override = chain_dir / Path(path_name).name if chain_dir is not None else None
        paths[key], _, identity = authenticated(path_name, override)
        identities.append(identity)
    config = load_json(paths['config'].read_text())
    native_configuration = {
        'S0': config['CW_complexes']['S0'],
        'Ceta': config['CW_complexes']['Ceta'],
        'Ceta__S0': config['maps']['Ceta__S0'],
    }
    require(canonical(native_configuration) == canonical({
        'S0': {'cells': [0], 'cells_gen': [0], 'operations': []},
        'Ceta': {'cells': [0, 2], 'cells_gen': [0], 'operations': [[0, 2]]},
        'Ceta__S0': {'from': 'Ceta', 'images': [2], 'sus': 2, 'to': 'S0'},
    }), 'official cohomology-module/initial-map configuration changed')
    ceta = chain_rows(native, decoder, paths['ceta'], 'Ceta', LIMIT)
    sphere = chain_rows(native, decoder, paths['sphere'], 'S0', LIMIT - 2)
    require(len(ceta) == 84 and len(sphere) == 48, 'fixed chain family cardinality changed')
    ci, si = {r['id']: i for i, r in enumerate(ceta)}, {r['id']: i for i, r in enumerate(sphere)}
    cd, sd = [], []
    for records, index, out in ((ceta, ci, cd), (sphere, si, sd)):
        for row in records:
            if row['s'] == 0:
                require(not row['decoded'], 'nonzero differential at initial term needs an augmentation model')
                out.append([])
            else:
                out.append(indexed_terms(row['decoded'], row['s'] - 1, index, records, decoder, row['t']))
    with native.connect(paths['map']) as db:
        map_rows = [dict(row) for row in db.execute('SELECT id,map,map_h FROM map_Adams_res_Ceta__S0 ORDER BY id')]
        map_version = [dict(row) for row in db.execute('SELECT * FROM version ORDER BY id')]
    metadata = {row['name']: row['value'] for row in map_version}
    require(len(metadata) == len(map_version), 'duplicate chain-map version metadata')
    expected_metadata = {'version': 3, 'from': 'Ceta', 'to': 'S0', 'filtration': 0,
                         'suspension': 2, 't_max': LIMIT}
    for key, value in expected_metadata.items():
        require(key in metadata and type(metadata[key]) is type(value) and metadata[key] == value,
                'chain-map metadata changed: ' + key)
    if 'verified' in metadata:
        require(type(metadata['verified']) is int and metadata['verified'] == LIMIT,
                'unexpected native verified-bound metadata')
    require([r['id'] for r in map_rows] == [r['id'] for r in sphere], 'map must contain every and only the 48 selected sphere columns')
    columns, map_terms = [], []
    for row, source in zip(map_rows, sphere):
        require(type(row['map']) is bytes and len(row['map']) % 8 == 0, 'NULL/malformed chain image is not zero')
        require(type(row['map_h']) is str, 'NULL chain augmentation is unknown')
        decoded = decoder.decode(row['map'])
        columns.append(indexed_terms(decoded, source['s'], ci, ceta, decoder, source['t'] + 2))
        expected = sorted(v for powers, v in decoded if powers == decoder.ZERO)
        require(native.coordinates(row['map_h']) == expected, 'stored map_h disagrees with decoded augmentation')
        map_terms.append(decoded)
    # Independent full Milnor products check the finite chain equations. This
    # Python result is explicitly separate from the Lean augmentation theorem.
    cd_by_s, sd_by_s, q_by_s = defaultdict(dict), defaultdict(dict), defaultdict(dict)
    for rows, out in ((ceta, cd_by_s), (sphere, sd_by_s)):
        for row in rows:
            out[row['s']][row['local_id']] = row['decoded']
    for row, terms in zip(sphere, map_terms):
        q_by_s[row['s']][row['local_id']] = terms
    for rows, diffs in ((ceta, cd_by_s), (sphere, sd_by_s)):
        for row in rows:
            if row['s'] >= 2:
                require(not decoder.compose(row['decoded'], diffs[row['s'] - 1]), 'resolution d squared fails')
    for row, terms in zip(sphere, map_terms):
        if row['s'] >= 1:
            require(decoder.compose(terms, cd_by_s[row['s']]) ==
                    decoder.compose(row['decoded'], q_by_s[row['s'] - 1]), 'finite chain-map equation fails')
    require(all(any(p != 0 for p in term['powers']) for diff in cd + sd for term in diff),
            'selected differential has nonzero augmentation')
    # This validates recorded integer identities, not actual Ext identification.
    comparison_rows = []
    for old, records, index, label in ((all_native_ceta, ceta, ci, 'Ceta'), (native_sphere, sphere, si, 'S0')):
        require(len(old) == len(records), 'old/new bounded generator counts disagree')
        seen = set()
        for row in old:
            require(type(row['repr']) is str and re.fullmatch(r'[0-9]+', row['repr']), 'native representative is not a singleton cochain')
            ident = int(row['repr'])
            require(ident in index and ident not in seen, 'old/new repr is absent or repeated')
            seen.add(ident)
            current = records[index[ident]]
            require((row['s'], row['t']) == (current['s'], current['t']), 'old/new repr degree mismatch')
            comparison_rows.append(dict(spectrum=label, native_basis_id=row['id'], native_repr=row['repr'],
                                        chain_index=index[ident], chain_id=ident, s=row['s'], t=row['t']))
    entries = []
    for row, word_entry in zip(selected, word_bundle['entries']):
        source = ci[int(row['repr'])]
        targets = [j for j, terms in enumerate(columns)
                   if sum(term['generator'] == source and not any(term['powers']) for term in terms) % 2]
        expected = sorted(si[int(rep)] for rep in word_entry['target_reprs'])
        require(targets == expected, 'native word result and chain cochain augmentation disagree')
        entries.append(dict(source=source, targets=targets, native_basis_id=row['id']))
    fields = lambda rows: [dict(id=r['id'], s=r['s'], t=r['t']) for r in rows]
    return dict(schema_version=1, kind='bounded-native-top-cell-cochain-augmentation-batch',
                canonical_registry='docs/external-inputs.json', inputs=word_bundle['inputs'] + identities,
                selection=word_bundle['selection'], sphere_generators=fields(sphere), ceta_generators=fields(ceta),
                sphere_differentials=sd, ceta_differentials=cd, map_columns=columns,
                map_database_version=map_version, native_configuration=native_configuration, entries=entries,
                old_new_repr_data_matches=comparison_rows,
                summary=dict(selected_entries=len(entries), sphere_generators=len(sphere), ceta_generators=len(ceta),
                             zero_images=sum(not r['targets'] for r in entries),
                             nonempty_target_vectors=sum(bool(r['targets']) for r in entries),
                             finite_chain_equations_python_checked=True,
                             all_differential_terms_positive=True),
                proof_boundary=dict(augmentation_equalities='finite certificate inputs; kernel checking is separate',
                                    full_chain_equations='checked independently in Python; not a Lean proof',
                                    native_verified_field='native progress metadata only, never proof evidence',
                                    old_new_repr_match='integer IDs and degrees agree; not a mathematical basis comparison',
                                    resolution_exactness=False, augmentation_to_actual_cohomology=False,
                                    actual_top_cell_comparison=False, actual_differential=False))


def render_json(bundle):
    return json.dumps(bundle, ensure_ascii=False, indent=2, allow_nan=False) + '\n'


def lean_basis(row):
    return '⟨' + ', '.join(str(row[k]) for k in ('id', 's', 't', 'local_index')) + ', ' + json.dumps(row['code']) + '⟩'


def lean_list(values):
    return '[' + ', '.join(values) + ']'


def render_words(bundle):
    lines = ['import KIP126.LinProgram.Certificates.Naturality.BatchMapCertificate', '',
             '/-! Generated from authenticated original tables. Input records are not actual-map proofs. -/',
             'namespace KIP126.LinModule.RawData.NaturalityBatch21',
             'open KIP126.LinModule.BatchMapCertificate', '',
             'def relationCodes : List String := ' + lean_list([json.dumps(r) for r in bundle['relation_codes']]), '',
             'def entries : List Entry := [']
    for i, entry in enumerate(bundle['entries']):
        terms = ['⟨' + str(term['relation']) + ', ' + str(term['multiplier']) + '⟩' for term in entry['witness']]
        lines.append('  { source := ' + lean_basis(entry['source']) + ', targetS := ' + str(entry['target_s']) +
                     ', targetT := ' + str(entry['target_t']) + ', targets := ' + lean_list([lean_basis(t) for t in entry['targets']]) +
                     ', witness := ' + lean_list(terms) + ' }' + (',' if i + 1 < len(bundle['entries']) else ''))
    lines += [']', '', 'end KIP126.LinModule.RawData.NaturalityBatch21']
    return '\n'.join(lines) + '\n'


def render_cochains(bundle):
    fin = lambda value: '⟨' + str(value) + ', by decide⟩'
    lines = ['import KIP126.LinProgram.Certificates.Naturality.CochainMapCertificate', '',
             '/-! Generated bounded chain terms. Matching original repr integers does not prove basis identification. -/',
             'namespace KIP126.LinModule.RawData.NaturalityCochainBatch21',
             'open KIP126.LinModule.CochainMapCertificate', '']
    def vector(name, typ, values):
        lines.append('def ' + name + ' : ' + typ + ' := ![')
        for i, value in enumerate(values):
            lines.append('  ' + value + (',' if i + 1 < len(values) else ''))
        lines.extend([']', ''])
    for key, name, size in [('sphere_generators', 'sphereGenerators', 48), ('ceta_generators', 'cetaGenerators', 84)]:
        vector(name, f'Fin {size} → GeneratorRecord', ['⟨' + ', '.join(str(row[k]) for k in ('id', 's', 't')) + '⟩' for row in bundle[key]])
    for key, name, source, target in [('sphere_differentials', 'sphereDifferentials', 48, 48),
                                      ('ceta_differentials', 'cetaDifferentials', 84, 84),
                                      ('map_columns', 'mapColumns', 48, 84)]:
        values = [lean_list(['⟨' + str(term['powers']) + ', ' + fin(term['generator']) + '⟩' for term in terms]) for terms in bundle[key]]
        vector(name, f'Fin {source} → List (Term {target})', values)
    vector('entries', 'Fin 82 → Entry 48 84', ['⟨' + fin(e['source']) + ', ' + lean_list([fin(i) for i in e['targets']]) + ', ' + str(e['native_basis_id']) + '⟩' for e in bundle['entries']])
    lines.append('end KIP126.LinModule.RawData.NaturalityCochainBatch21')
    return '\n'.join(lines) + '\n'


def validate_candidate(candidate, expected):
    # Canonical JSON equality is deliberately type-sensitive (False != 0).
    if canonical(candidate) != canonical(expected):
        raise ValueError('batch certificate differs from reconstruction of every fixed input and selected record')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument('--chain-dir', type=Path, help='development override; bytes still must match canonical artifacts')
    parser.add_argument('--certificate', type=Path, help='validate full word/cochain JSON, or the complete selected-ID list')
    parser.add_argument('--check', action='store_true', help='compare generated outputs without modifying them')
    args = parser.parse_args()
    words, selected, all_ceta, sphere = rebuild_words()
    cochains = rebuild_cochains(words, selected, all_ceta, sphere, args.chain_dir)
    if args.certificate:
        candidate = load_json(args.certificate.read_text())
        if isinstance(candidate, list):
            expected = words['selection']['complete_selected_ids']
        elif isinstance(candidate, dict) and candidate.get('kind') == cochains['kind']:
            expected = cochains
        else:
            expected = words
        validate_candidate(candidate, expected)
    outputs = {'Batch21.json': render_json(words), 'Batch21.lean': render_words(words),
               'CochainBatch21.json': render_json(cochains), 'CochainBatch21.lean': render_cochains(cochains)}
    for name, contents in outputs.items():
        path = args.output_dir / name
        if args.check:
            require(path.read_text() == contents, 'generated output differs: ' + name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents)
    print(json.dumps(dict(selected=words['selection']['count'], words=words['summary'], cochains=cochains['summary'],
                          actual_certification=False, mode='checked' if args.check else 'generated'), sort_keys=True))


if __name__ == '__main__':
    main()
