#!/usr/bin/env python3
"""Freeze selected rows of the actual seed5487 closure as explicit Lean data.

The generator is untrusted. Lean proves coefficient identities from its literal
output; this script separately checks the selected raw input and provenance.
Use --witness with extract-secondary-witness.py output to verify extraction from
the complete 96-generator snapshot. --check performs no writes.
"""
import argparse
import hashlib
import json
from pathlib import Path

import sys as _module_sys
from pathlib import Path as _ModulePath
_module_sys.path.insert(0, str(_ModulePath(__file__).resolve().parent))
from lean_module import lean_module, module_output

ROOT = Path(__file__).resolve().parents[3]
DEST = ROOT / 'KIP126/LinProgram/Certificates/Secondary/Seed5487'
EXPECTED = '088958541d91f6a987c825ab94a3266001cf94e6eccdf19757ac9b39d92c69fa'
SELECTED = 'ee919f10abe5f5beeb3213b6529e598198c217555aeccfb415d838e13a2218c8'
CLOSURE_IDS = '353a86fc9dc8a69e60f674d62dbf14ebface2bd29f2fa530dc0ef0804dc74f52'
REBUILD_AUDIT = ROOT / 'KIP126/LinProgram/Generated/Provenance/seed5487-next.json'
IDS = [0, 524288, 524289, 1048577, 1572866, 2097152, 3145729]


def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':')).encode()


def module(terms):
    return '[' + ', '.join('⟨[' + ', '.join(map(str, a['sq'])) + '], ' + str(a['v']) + '⟩'
                           for a in terms) + ']'


@module_output
def render(data):
    text = ['import KIP126.LinProgram.Certificates.Secondary.Data', '',
            '/-! Deterministically generated selected extracted rows. The d/f columns are',
            'native; d_f/f_d/associator are auxiliary expressions proposed by the extractor.',
            'See source.json for the complete closure fingerprint and exact input scope.',
            'No imported status is used as a mathematical hypothesis. -/', '',
            'namespace KIP126.Computation.Secondary.Seed5487', '']
    for r in data['selected_generators']:
        text.append(f"def row{r['id']} : NativeRow where")
        text.extend(f'  {k} := {r[k]}' for k in ('id', 's', 'v', 't'))
        text.extend(f'  {k} := {module(r[k])}' for k in ('d', 'f', 'd_f', 'f_d', 'associator'))
        text.append('')
    text += ['end KIP126.Computation.Secondary.Seed5487', '']
    return '\n'.join(text)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_source_chain(audit, rendered_input):
    """Connect the fixed fixture and existing rebuild record to the sole source manifest."""
    inventory = json.loads((ROOT / 'docs/external-inputs.json').read_text())
    sources = [s for s in inventory['sources'] if s['id'] == 'lwx_machine']
    require(len(sources) == 1, 'canonical LWX source must be unique')
    archive_path = 'Source/LWXMachine/source-code.zip'
    archives = [a for a in sources[0]['artifacts'] if a['path'] == archive_path]
    require(len(archives) == 1, 'fixed source archive is absent or duplicated in the canonical manifest')
    artifact = archives[0]
    original = audit['source_archive']
    payload = (ROOT / archive_path).read_bytes()
    require(len(payload) == artifact['size'] == original['bytes'] and
            hashlib.sha256(payload).hexdigest() == artifact['sha256'] == original['sha256'],
            'canonical archive bytes differ from the fixed rebuild source')
    require(hashlib.md5(payload).hexdigest() == original['md5'] and
            artifact['downloaded_from']['checksum'] == 'md5:' + original['md5'],
            'canonical archive checksum differs from the recorded source')
    require(artifact['reproduction']['existing_extraction_and_rebuild_record'] ==
            str(REBUILD_AUDIT.relative_to(ROOT)), 'canonical rebuild-record link changed')
    derived = artifact['derived_outputs']
    selected = derived['selected_witness']
    require(selected['path'] == str((DEST / 'source.json').relative_to(ROOT)) and
            selected['sha256'] == hashlib.sha256((DEST / 'source.json').read_bytes()).hexdigest(),
            'selected fixture does not match the canonical derivation link')
    require(selected['complete_96_row_semantic_sha256'] == EXPECTED and
            selected['selected_row_semantic_sha256'] == SELECTED and
            selected['selected_row_count'] == len(IDS) and
            selected['closure_ids_sha256'] == CLOSURE_IDS,
            'canonical semantic fingerprints differ from the fixed fixture')
    require(derived['fixed_input']['path'] == str((DEST / 'Input.lean').relative_to(ROOT)) and
            derived['fixed_input']['sha256'] == hashlib.sha256(rendered_input.encode()).hexdigest(),
            'generated Lean input differs from its canonical derivation link')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--witness', type=Path)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    data = json.loads((DEST / 'source.json').read_text())
    # Reuse the existing extraction/rebuild record; the canonical source
    # acquisition manifest remains docs/external-inputs.json.
    audit = json.loads(REBUILD_AUDIT.read_text())
    recorded = audit['independent_extraction']
    closure = data['source_closure_ids']
    require(data['schema'] == 'lin-secondary-seed5487-selected/v1', 'unexpected fixture schema')
    require(data['source_witness_semantic_sha256'] == recorded['chain_semantic_sha256'] == EXPECTED,
            'full-witness fingerprint differs from the fixed rebuild record')
    require(data['selected_generator_count'] == len(IDS) and
            data['selected_semantic_sha256'] == SELECTED, 'selected count or metadata fingerprint changed')
    require(hashlib.sha256(canonical(data['selected_generators'])).hexdigest() == SELECTED,
            'selected payload fingerprint changed')
    require(len(closure) == len(set(closure)) == 96, 'closure must contain 96 distinct IDs')
    require(hashlib.sha256(canonical(closure)).hexdigest() == CLOSURE_IDS,
            'fixed closure ID fingerprint changed')
    require(closure == [r['id'] for r in audit['closed_chain_summary']],
            'closure IDs differ from the existing extraction record')
    require(data['input_hashes'] == recorded['input_hashes'],
            'fixture database digests differ from the existing rebuild record')
    for key in ('target_id', 'comparison_target_id', 'source_v'):
        require(data[key] == recorded[key], f'fixture seed endpoint changed: {key}')
    require([r['id'] for r in data['selected_generators']] == IDS, 'selected row IDs changed')
    for r in data['selected_generators']:
        require(r['id'] == (r['s'] << 19) + r['v'], 'row ID does not encode its native degree/index')
        require(r['id'] in closure, 'selected row is outside the closure')
        for field in ('d', 'f', 'd_f', 'f_d', 'associator'):
            for a in r[field]:
                require(set(a) == {'sq', 'v'} and len(a['sq']) == 8, 'invalid native term shape')
                require(all(type(n) is int and n >= 0 for n in a['sq']), 'invalid native exponent')
                require(type(a['v']) is int and a['v'] >= 0, 'invalid native generator index')
    if args.witness:
        witness = json.loads(args.witness.read_text())
        rows = witness['generators']
        require(hashlib.sha256(canonical(rows)).hexdigest() == EXPECTED,
                'complete 96-row semantic fingerprint changed')
        require(witness['chain_semantic_sha256'] == EXPECTED and witness['closure_generators'] == 96,
                'witness metadata does not match its fixed payload')
        require([r['id'] for r in rows] == closure, 'witness closure IDs changed')
        require([r for r in rows if r['id'] in IDS] == data['selected_generators'],
                'selected records differ from the full witness')
        for key in ('target_id', 'comparison_target_id', 'source_v',
                    'augmentation', 'comparison_augmentation'):
            require(witness[key] == recorded[key], f'witness seed endpoint changed: {key}')
        by_id = {row['id']: row for row in rows}
        require(len(data['direct_dependency_occurrences']) == 2,
                'both native target-lift dependencies must be retained')
        require([item['root_id'] for item in data['direct_dependency_occurrences']] ==
                [data['target_id'], data['comparison_target_id']], 'dependency endpoints changed')
        for item in data['direct_dependency_occurrences']:
            root = by_id[item['root_id']]
            require(item['field'] == 'f' and item['image_id'] == 3145729,
                    'unexpected direct dependency kind or image')
            require(root['f'][item['term_index']] == item['term'],
                    'direct dependency differs from the original target lift')
            require(((root['s'] - 2) << 19) + item['term']['v'] == item['image_id'],
                    'direct dependency uses the wrong homological degree')
        original_hashes = witness['input_hashes']
        hashes = {Path(k).name: v for k, v in original_hashes.items()}
        require(len(hashes) == len(original_hashes) == 2 and set(hashes) == set(data['input_hashes']),
                'witness must name exactly the two recorded database inputs')
        require(all(isinstance(v, str) and len(v) == 64 and
                    all(c in '0123456789abcdef' for c in v) for v in hashes.values()),
                'invalid witness database digest')
        if hashes != data['input_hashes']:
            print('recomputed database bytes differ from the recorded rebuild (timestamps may differ); '
                  'the complete 96-row semantic payload is identical')
        else:
            print('database digests match the recorded local rebuild')
        print('seed5487: complete 96-row witness, selected records, closure IDs and seed endpoints match')
    else:
        print('seed5487: selected payload and fixed metadata checked only; '
              'checking the complete 96-row source requires --witness')
    result = render(data)
    check_source_chain(audit, result)
    output = DEST / 'Input.lean'
    if args.check:
        require(output.read_text() == result, 'generated Lean differs from fixed input')
    else:
        output.write_text(result)



if __name__ == '__main__':
    main()
