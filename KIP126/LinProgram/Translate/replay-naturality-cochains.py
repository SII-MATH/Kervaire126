#!/usr/bin/env python3
"""Replay the enlarged t<=40 finite native cochain family.

The complete native generator graph and original-relation witnesses are rebuilt
from fixed inputs. Chain payloads are separately authenticated. Full Steenrod
chain equations are checked in Python; Lean proves finite augmentation facts.
No native basis, resolution, or actual-model identification follows from this.
"""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
LIN = ROOT / 'KIP126/LinProgram'
OUTPUT = LIN / 'Generated/Naturality'
LIMIT = 40
COUNTS = (261, 155)
CHAIN_INPUTS = {
    'ceta': 'KIP126/LinProgram/Raw/Naturality/Batch40/Ceta_Adams_res.db',
    'map': 'KIP126/LinProgram/Raw/Naturality/Batch40/map_Adams_res_Ceta__S0.db',
    'sphere': 'KIP126/LinProgram/Raw/Secondary/Seed5487/S0_Adams_res.db',
    'config': 'Source/LWXMachine/Adams.json',
}


def load(filename, name):
    import importlib.util
    spec = importlib.util.spec_from_file_location(name, LIN / 'Translate' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rebuild(chain_dir=None):
    batch = load('replay-naturality-batch.py', 'cochain_batch')
    words = load('replay-naturality-words.py', 'cochain_words').rebuild()
    native = load('native-contract.py', 'cochain_native')
    low = native.load_lowstem()
    ceta_path, _, _ = low.pinned('Ceta_AdamsSS_t200.db')
    sphere_path, _, _ = low.pinned('S0_AdamsSS_t261.db')
    with native.connect(ceta_path) as ceta, native.connect(sphere_path) as sphere:
        all_sources = batch.catalogue(ceta, 'Ceta', LIMIT)
        targets = batch.catalogue(sphere, 'S0', LIMIT - 2)
    selected = [row for row in all_sources if row['t'] >= 2]
    words['entries'] = [entry for entry in words['entries'] if entry['source']['t'] <= LIMIT]
    batch.require([row['id'] for row in selected] == [e['source']['id'] for e in words['entries']],
                  'selected original native IDs are incomplete or reordered')
    batch.require(len(selected) == 259, 'fixed t40 request count changed')
    words['selection'] = dict(spectrum='Ceta', minimum_t=2, maximum_t=LIMIT,
                             complete_selected_ids=[row['id'] for row in selected], count=len(selected))
    result = batch.rebuild_cochains(words, selected, all_sources, targets, chain_dir,
        limit=LIMIT, chain_inputs=CHAIN_INPUTS, expected_counts=COUNTS, combination_entries=True)

    map_override = chain_dir / 'map_Adams_res_Ceta__S0.db' if chain_dir is not None else None
    map_path, _, _ = batch.authenticated(CHAIN_INPUTS['map'], map_override)
    with native.connect(map_path) as db:
        result['native_map_h_records'] = [dict(row) for row in db.execute(
            'SELECT id,map_h FROM map_Adams_res_Ceta__S0 ORDER BY id')]
    result['augmentation_columns'] = [[term['generator'] for term in terms if not any(term['powers'])]
                                      for terms in result['map_columns']]
    result['summary']['source_combinations'] = sum(len(e['sources']) > 1 for e in result['entries'])
    result['summary']['target_combinations'] = sum(len(e['targets']) > 1 for e in result['entries'])
    result['proof_boundary']['old_new_repr_match'] = 'Every term has a retained chain ID and recorded degree; no basis theorem or mathematical old/new comparison is inferred.'
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=OUTPUT)
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--chain-dir', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    batch = load('replay-naturality-batch.py', 'cochain_renderer')
    result = rebuild(args.chain_dir)
    if args.certificate:
        batch.validate_candidate(batch.load_json(args.certificate.read_text()), result)
    files = {'CochainBatch40.json': batch.render_json(result),
             'CochainBatch40.lean': batch.render_cochains(result)}
    for name, content in files.items():
        path = args.output_dir / name
        if args.check:
            batch.require(path.read_text() == content, 'finite cochain output changed: ' + name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    import json
    print(json.dumps(result['summary'], sort_keys=True))


if __name__ == '__main__':
    main()
