#!/usr/bin/env python3
"""Export all 15,951 fixed Ceta__S0 native words with 2 <= t <= 200.

Search is untrusted: every proposed original-relation combination is multiplied
out independently before emission, and Lean checks its quotient equation. This
does not prove a catalogue is a basis, quotient descent, or an actual Adams map.
"""
import argparse
from collections import Counter, defaultdict
import csv
from functools import lru_cache
import importlib.util
import io
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
LIN = ROOT / 'KIP126/LinProgram'
DEFAULT_OUTPUT = LIN / 'Generated/Naturality/Words200'
LIMIT = 200
SHARD_SIZE = 128


def load_batch():
    spec = importlib.util.spec_from_file_location('naturality_word_batch', LIN / 'Translate/replay-naturality-batch.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


batch = load_batch()
require = batch.require


@lru_cache(maxsize=32768)
def divisors(monomial):
    return tuple(tuple((g, e) for (g, _), e in zip(monomial, powers) if e)
                 for powers in itertools.product(*(range(a + 1) for _, a in monomial)))


class Reducer:
    """Deterministic original-relation reduction; no ideal enlargement.

    First try all single monomial multiples capable of cancelling a selected
    non-catalogue term. Otherwise repeatedly cancel a non-catalogue term with
    the first divisible original leading term, in original record order.
    Termination is checked per request, not presumed from a Groebner claim.
    """
    def __init__(self, relations, low):
        self.low = low
        self.relations = {r['rowid']: r for r in relations}
        require(len(self.relations) == len(relations), 'duplicate original relation id')
        self.polys = {}
        self.term_index = defaultdict(list)
        self.lead_index = defaultdict(list)
        for rel in relations:
            rid = rel['rowid']
            poly = low.polynomial(rel['rel'])
            lead = low.mon(rel['rel'].split(';')[0])
            require(lead in poly, 'original leading term cancels within its relation')
            self.polys[rid] = poly
            self.lead_index[lead].append(rid)
            for term in sorted(poly):
                self.term_index[term].append(rid)

    def verify(self, initial, result, witness):
        actual = set(initial)
        for rid, multiplier in witness:
            require(rid in self.polys, 'unknown original relation in witness')
            actual.symmetric_difference_update(self.low.mul(multiplier, term) for term in self.polys[rid])
        require(actual == result, 'relation combination does not reproduce claimed output')

    def reduce(self, initial, basis, max_steps=10000):
        poly = set(initial)
        if all(m in basis for m in poly):
            return poly, []
        bad = min(m for m in poly if m not in basis)
        for divisor in divisors(bad):
            multiplier = self.low.quotient(bad, divisor)
            for rid in self.term_index.get(divisor, ()):
                result = poly.symmetric_difference(self.low.mul(multiplier, term) for term in self.polys[rid])
                if all(m in basis for m in result):
                    witness = [(rid, multiplier)]
                    self.verify(initial, result, witness)
                    return result, witness
        witness, seen = [], set()
        while any(m not in basis for m in poly):
            require(len(witness) < max_steps, 'original-relation reduction exceeded explicit step bound')
            state = frozenset(poly)
            require(state not in seen, 'original-relation reduction cycle')
            seen.add(state)
            bad = min(m for m in poly if m not in basis)
            candidates = [rid for divisor in divisors(bad) for rid in self.lead_index.get(divisor, ())]
            require(bool(candidates), 'no original leading relation reduces the remaining non-catalogue term')
            rid = min(candidates)
            lead = self.low.mon(self.relations[rid]['rel'].split(';')[0])
            multiplier = self.low.quotient(bad, lead)
            poly.symmetric_difference_update(self.low.mul(multiplier, term) for term in self.polys[rid])
            witness.append((rid, multiplier))
        self.verify(initial, poly, witness)
        return poly, witness


def fixed_inputs():
    native = batch.load('native-contract.py', 'naturality_words_native')
    low = native.load_lowstem()
    _, manifest_bytes, identity = batch.authenticated('KIP126/LinProgram/Raw/manifest.json')
    manifest = batch.load_json(manifest_bytes.decode())
    native.validate_ceta_archive_origin(manifest)
    records = {row['path']: row for row in manifest['files']}
    require(len(records) == len(manifest['files']), 'duplicate native manifest entry')
    registry = batch.load_json((ROOT / 'docs/external-inputs.json').read_text())
    registered = {a['path'] for source in registry['sources'] for a in source.get('artifacts', [])}
    paths, payloads, identities = {}, {}, [identity]
    for name in batch.RAW_INPUTS:
        path, data, digest = low.pinned(name)
        require(digest == records[name]['sha256'] and len(data) == records[name]['size'],
                'native manifest and authenticated payload disagree: ' + name)
        path_name = 'KIP126/LinProgram/Raw/' + name
        if path_name in registered:
            _, other, _ = batch.authenticated(path_name)
            require(other == data, 'canonical artifact and native manifest disagree: ' + name)
        paths[name], payloads[name] = path, data
        identities.append(dict(path=path_name, sha256=digest, size=len(data)))
    return native, low, paths, payloads, identities


def rebuild():
    native, low, paths, payloads, identities = fixed_inputs()
    configuration = batch.load_json(payloads['ss.json'].decode())
    maps = [r for r in configuration['maps'] if r['name'] == 'Ceta__S0']
    require(len(maps) == 1, 'ambiguous native Ceta__S0 map')
    mapping = maps[0]
    require((mapping['from'], mapping['to'], mapping['sus'], mapping['type'], mapping['t_max']) ==
            ('Ceta', 'S0', 2, 'top_cell', LIMIT), 'native Ceta__S0 contract changed')
    with native.connect(paths['Ceta_AdamsSS_t200.db']) as ceta, native.connect(paths['S0_AdamsSS_t261.db']) as sphere, native.connect(paths['map_AdamsSS_Ceta_to_S0_t200.db']) as maps:
        all_sources = batch.catalogue(ceta, 'Ceta', LIMIT)
        selected = [r for r in all_sources if r['t'] >= 2]
        targets = batch.catalogue(sphere, 'S0', LIMIT - 2)
        module_generators = {r['id']: dict(r) for r in ceta.execute('SELECT * FROM Ceta_AdamsE2_generators ORDER BY id')}
        ring_generators = {r['id']: dict(r) for r in sphere.execute('SELECT * FROM S0_AdamsE2_generators ORDER BY id')}
        images = {r['id']: r['map'] for r in maps.execute('SELECT * FROM map_AdamsE2_Ceta_to_S0 ORDER BY id')}
        require(set(images) == set(module_generators), 'native map graph is incomplete')
        relations = [dict(r) for r in sphere.execute('SELECT rowid,rel,s,t FROM S0_AdamsE2_relations WHERE t<=? ORDER BY rowid', (LIMIT - 2,))]
        metadata = [dict(r) for r in maps.execute('SELECT * FROM version ORDER BY id')]
        md = {r['name']: r['value'] for r in metadata}
        require(len(md) == len(metadata), 'duplicate map metadata field')
        require((md.get('from'), md.get('to'), md.get('filtration'), md.get('suspension'), md.get('t_max')) ==
                ('Ceta', 'S0', 0, 2, LIMIT), 'native database map contract changed')
        require(ceta.execute('SELECT COUNT(*) FROM Ceta_AdamsE2_basis').fetchone()[0] == len(all_sources),
                'source database has records beyond the fixed full window')
    require(len(all_sources) == 15953 and len(selected) == 15951, 'fixed complete Ceta catalogue size changed')
    by_degree = defaultdict(dict)
    for row in targets:
        monomial = low.mon(row['mon'])
        degree = row['s'], row['t']
        require(monomial not in by_degree[degree], 'duplicate target catalogue monomial')
        by_degree[degree][monomial] = row
    reducer = Reducer(relations, low)
    entries, used_ids, statuses, lengths = [], set(), Counter(), Counter()
    for row in selected:
        generator, coefficient, poly, degree = batch.map_word(row['mon'], module_generators, images, ring_generators, low)
        require(degree == [row['s'], row['t']], 'source word degree mismatch')
        target_s, target_t = row['s'], row['t'] - 2
        basis = by_degree[target_s, target_t]
        reduced, steps = reducer.reduce(poly, basis)
        output = sorted((basis[m] for m in reduced), key=lambda r: r['local_index'])
        # Aggregate equal relation multiples over F_2 without changing the ideal.
        multipliers = defaultdict(set)
        for rid, multiplier in steps:
            multipliers[rid].symmetric_difference_update({multiplier})
        witness = [(rid, m) for rid in sorted(multipliers) for m in sorted(multipliers[rid])]
        reducer.verify(poly, reduced, witness)
        used_ids.update(rid for rid, _ in witness)
        status = ('relation-reduced' if witness else 'zero' if not output else
                  'direct-singleton' if len(output) == 1 else 'direct-sum')
        statuses[status] += 1
        lengths[len(steps)] += 1
        entries.append(dict(source=batch.basis_record(row), source_repr=row['repr'], generator_id=generator,
                            generator_image=images[generator], substituted_polynomial=batch.polynomial_list(poly),
                            target_s=target_s, target_t=target_t, targets=[batch.basis_record(r) for r in output],
                            target_reprs=[r['repr'] for r in output], coordinates=[r['local_index'] for r in output],
                            witness=[dict(original_relation_rowid=rid, multiplier=batch.polynomial_list(multipliers[rid]))
                                     for rid in sorted(multipliers) if multipliers[rid]],
                            reduction_steps=len(steps), status=status))
    relation_records = [dict(reducer.relations[rid]) for rid in sorted(used_ids)]
    by_key = {(r['rel'], r['s'], r['t']): r for r in relation_records}
    require(len(by_key) == len(relation_records), 'ambiguous original relation identity')
    matches = Counter()
    for index, row in enumerate(csv.DictReader(io.StringIO(payloads['S0_AdamsE2_relations.csv'].decode('utf-16')))):
        key = row['rel'], int(row['s']), int(row['stem']) + int(row['s'])
        if key in by_key:
            matches[key] += 1
            record = by_key[key]
            record.update(csv_record_index=index, csv_line_number=index + 2,
                          csv_path='KIP126/LinProgram/Raw/S0_AdamsE2_relations.csv',
                          chunk_index=(index - 3) // 1024 if index >= 3 else None,
                          chunk_line_index=(index - 3) % 1024 if index >= 3 else None)
    require(len(matches) == len(by_key) and all(n == 1 for n in matches.values()),
            'used relation lacks unique exact original CSV membership')
    relation_index = {r['rowid']: i for i, r in enumerate(relation_records)}
    for entry in entries:
        for term in entry['witness']:
            term['relation'] = relation_index[term['original_relation_rowid']]
    shards = []
    for offset in range(0, len(entries), SHARD_SIZE):
        rows = entries[offset:offset + SHARD_SIZE]
        indices = sorted({term['relation'] for row in rows for term in row['witness']})
        shards.append(dict(index=len(shards), name=f'Shard{len(shards):03}', offset=offset, count=len(rows),
                           selected_source_ids=[row['source']['id'] for row in rows], relation_indices=indices))
    return dict(schema_version=1, kind='complete-fixed-native-Ceta-top-cell-word-certificates',
                canonical_registry='docs/external-inputs.json', inputs=identities, native_map=mapping,
                selection=dict(spectrum='Ceta', minimum_t=2, maximum_t=LIMIT,
                               complete_selected_ids=[r['id'] for r in selected], count=len(selected),
                               excluded_below_minimum_t=[batch.basis_record(r) for r in all_sources if r['t'] < 2]),
                relation_codes=[r['rel'] for r in relation_records], relation_records=relation_records,
                entries=entries, shards=shards, unresolved=[],
                summary=dict(status_counts=dict(sorted(statuses.items())),
                             zero_outputs=sum(not r['targets'] for r in entries),
                             singleton_outputs=sum(len(r['targets']) == 1 for r in entries),
                             multi_coordinate_outputs=sum(len(r['targets']) > 1 for r in entries),
                             distinct_original_relations=len(relation_records),
                             reduction_step_counts={str(k): lengths[k] for k in sorted(lengths)},
                             maximum_reduction_steps=max(lengths), shard_size=SHARD_SIZE, shard_count=len(shards)),
                proof_boundary=dict(word_equalities='proposed certificates; Lean kernel checking is separate',
                                    source_basis_identity='authenticated transcription, not a basis theorem',
                                    target_basis_identity='catalogue membership is separate from being a basis',
                                    quotient_descent='requires all 76569 original Ceta relation equations',
                                    chain_data_extended=False, actual_map_comparison=False,
                                    actual_differential=False, historical_premise_edge_certified=False))


def render_relations(bundle):
    return '\n'.join(['import KIP126.LinProgram.Certificates.Naturality.BatchMapCertificate', '',
                      '/-! Generated original relation codes. Original CSV membership is proved separately. -/',
                      'namespace KIP126.LinModule.RawData.NaturalityWords200', '',
                      'def relationCodes : List String := ' + batch.lean_list([json.dumps(s) for s in bundle['relation_codes']]), '',
                      'end KIP126.LinModule.RawData.NaturalityWords200', ''])


def render_shard(bundle, shard):
    indices = shard['relation_indices']
    local_index = {global_index: i for i, global_index in enumerate(indices)}
    rows = bundle['entries'][shard['offset']:shard['offset'] + shard['count']]
    ns = 'KIP126.LinModule.RawData.NaturalityWords200.' + shard['name']
    lines = ['import KIP126.LinProgram.Generated.Naturality.Words200.Relations', '',
             '/-! Generated fixed native word certificates. No assertion about an actual spectrum map. -/',
             'namespace ' + ns, 'open KIP126.LinModule.BatchMapCertificate', '',
             'def relationIndices : List Nat := ' + str(indices),
             'def relationCodes : List String := ' + batch.lean_list([json.dumps(bundle['relation_codes'][i]) for i in indices]), '',
             'def entries : List Entry := [']
    for i, entry in enumerate(rows):
        terms = ['⟨' + str(local_index[t['relation']]) + ', ' + str(t['multiplier']) + '⟩' for t in entry['witness']]
        lines.append('  { source := ' + batch.lean_basis(entry['source']) + ', targetS := ' + str(entry['target_s']) +
                     ', targetT := ' + str(entry['target_t']) + ', targets := ' + batch.lean_list([batch.lean_basis(t) for t in entry['targets']]) +
                     ', witness := ' + batch.lean_list(terms) + ' }' + (',' if i + 1 < len(rows) else ''))
    return '\n'.join(lines + [']', '', 'end ' + ns, ''])


def outputs(bundle):
    result = {'Manifest.json': batch.render_json(bundle), 'Relations.lean': render_relations(bundle)}
    result.update({shard['name'] + '.lean': render_shard(bundle, shard) for shard in bundle['shards']})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument('--certificate', type=Path, help='validate a complete manifest or the complete selected source-ID list')
    parser.add_argument('--check', action='store_true', help='compare exact generated outputs without writing')
    args = parser.parse_args()
    bundle = rebuild()
    if args.certificate:
        candidate = batch.load_json(args.certificate.read_text())
        expected = bundle['selection']['complete_selected_ids'] if isinstance(candidate, list) else bundle
        batch.validate_candidate(candidate, expected)
    generated = outputs(bundle)
    if args.check:
        require({p.name for p in args.output_dir.iterdir() if p.is_file()} == set(generated),
                'unexpected or missing generated word-certificate files')
    for name, content in generated.items():
        path = args.output_dir / name
        if args.check:
            require(path.read_text() == content, 'generated word-certificate output differs: ' + name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print(json.dumps(dict(selected=bundle['selection']['count'], **bundle['summary'],
                          actual_certification=False, mode='checked' if args.check else 'generated'), sort_keys=True))


if __name__ == '__main__':
    main()
