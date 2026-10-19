#!/usr/bin/env python3
"""Export both complete fixed native map graphs, never mathematical certification.

Rebuild from the authenticated v126.3.cw49 archive and the canonical pinned
raw inputs. No derived audit report, polynomial reduction, relation certificate,
actual Ext comparison or default image for a missing generator is used.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tempfile

import sys as _module_sys
from pathlib import Path as _ModulePath
_module_sys.path.insert(0, str(_ModulePath(__file__).resolve().parent))
from lean_module import lean_module, module_output

OUTPUT_PREFIX = 'KIP126/LinProgram/Generated/ModuleMaps'
SPECS = (
    ('Ceta__S0', 'CetaToSphere', 'Ceta', 'S0', 887, 2),
    ('CW_nu_eta__Ceta', 'CWToCeta', 'CW_nu_eta', 'Ceta', 844, 4),
)
VERSION_SCHEMA = 'CREATE TABLE version (id INTEGER PRIMARY KEY, name TEXT, value)'
MAP_FIELDS = ('id', 'map')
VERSION_FIELDS = ('id', 'name', 'value')
DATA_LEAN = '''/-! Lossless complete native map graph rows. An empty image is the
recorded zero string; absent and SQL NULL images are rejected by the exporter.
These records do not assert that the graph descends to any quotient module. -/
namespace KIP126.LinModule.RawData.Maps

structure ImageRow where
  id : Nat
  image : String
  deriving Repr, DecidableEq, Inhabited

end KIP126.LinModule.RawData.Maps
'''


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':'))+'\n').encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(root, name, filename):
    path = root/'KIP126/LinProgram/Translate'/filename
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def expected_catalogue(spec):
    name, _, source, target, _, suspension = spec
    result = dict(name=name, **{'from': source, 'to': target},
                  path=f'map_AdamsSS_{source}_to_{target}_t200.db', sus=suspension, t_max=200)
    if name == 'Ceta__S0':
        result['type'] = 'top_cell'
    return result


def expected_versions(spec):
    name, _, source, target, _, suspension = spec
    rows = [(0, 'version', 3),
            (1, 'change notes', 'Add fil,from,to in version table of maps.'),
            (446174262, 'from', source), (651971502, 'filtration', 0),
            (817812698, 't_max', 200), (1585932889, 'suspension', suspension),
            (1713085477, 'to', target)]
    if name == 'CW_nu_eta__Ceta':
        rows.append((1954841564, 'timestamp', 1690291275))
    return [dict(zip(VERSION_FIELDS, r)) for r in rows]


def validate_catalogue(spec, catalogue):
    require(catalogue == expected_catalogue(spec), spec[0]+': complete native map catalogue changed')


def validate_versions(spec, versions):
    require(all(tuple(row) == VERSION_FIELDS for row in versions), spec[0]+': version field contract changed')
    require(versions == expected_versions(spec), spec[0]+': complete native version rows changed')
    # Equality alone would admit Python bool in place of an integer.
    for row in versions:
        require(type(row['id']) is int and type(row['name']) is str, spec[0]+': invalid version field type')
        require(type(row['value']) is type(next(r['value'] for r in expected_versions(spec)
                                               if r['id'] == row['id'])), spec[0]+': invalid version value type')


def validate_image(code, target, ring, target_generators, expected_degree):
    require(type(code) is str, 'NULL or absent image is unknown, not the empty zero string')
    if code == '':
        return 0
    terms = code.split(';')
    for term in terms:
        require(re.fullmatch(r'(?:0|[1-9][0-9]*)(?:,(?:0|[1-9][0-9]*))*', term),
                'unknown or malformed native map term')
        values = list(map(int, term.split(',')))
        if target == 'S0':
            require(len(values) % 2 == 0, 'sphere image has an odd coefficient word')
            pairs = list(zip(values[::2], values[1::2])); base = (0, 0)
        else:
            require(len(values) % 2 == 1, 'module image lacks its final generator ID')
            generator = values[-1]
            require(generator in target_generators, 'target module generator ID outside complete range')
            pairs = list(zip(values[:-1:2], values[1:-1:2]))
            base = tuple(target_generators[generator][k] for k in ('s', 't'))
        require(all(i in ring and 0 < exponent <= 200 for i, exponent in pairs),
                'sphere generator ID or positive exponent outside native range')
        require([i for i, _ in pairs] == sorted(set(i for i, _ in pairs)),
                'unordered or repeated sphere coefficient generator')
        degree = tuple(base[k] + sum(ring[i][('s', 't')[k]]*exponent for i, exponent in pairs)
                       for k in (0, 1))
        require(degree == expected_degree, 'image term does not have the native shifted bidegree')
    return len(terms)


def validate_graph(spec, catalogue, versions, rows, modules, ring):
    validate_catalogue(spec, catalogue)
    validate_versions(spec, versions)
    name, _, source, target, count, suspension = spec
    require(source in modules and (target == 'S0' or target in modules), 'source/target missing from same module inputs')
    source_rows = modules[source]['generators']
    require(len(source_rows) == count and [r['id'] for r in source_rows] == list(range(count)),
            name+': complete same-source generator family changed')
    require(list(ring) == list(range(2914)), 'same complete sphere coefficient family changed')
    target_generators = {} if target == 'S0' else {r['id']: r for r in modules[target]['generators']}
    if target != 'S0':
        require(list(target_generators) == list(range(modules[target]['generator_count'])),
                name+': complete same-target generator family changed')
    require(all(tuple(row) == MAP_FIELDS for row in rows), name+': map field contract changed')
    require(len(rows) == count and all(type(row['id']) is int for row in rows) and
            [row['id'] for row in rows] == list(range(count)), name+': missing, duplicate, extra or reordered map ID')
    for row, source_row in zip(rows, source_rows):
        require(0 <= source_row['t'] <= 200, name+': source outside recorded map range')
        # Native filtration is exactly zero, as verified against the full version rows.
        expected_degree = (source_row['s'], source_row['t']-suspension)
        validate_image(row['map'], target, ring, target_generators, expected_degree)


def read_database(native, module_reader, path, spec):
    table = f'map_AdamsE2_{spec[2]}_to_{spec[3]}'
    with native.connect(path) as db:
        require({r['name'] for r in db.execute("SELECT name FROM sqlite_master WHERE type='table'")} ==
                {'version', table}, spec[0]+': native table set changed')
        schemas = {'version': module_reader.schema(db, 'version', VERSION_SCHEMA),
                   table: module_reader.schema(db, table, f'CREATE TABLE {table} (id INTEGER PRIMARY KEY, map TEXT)')}
        versions = [dict(r) for r in db.execute('SELECT * FROM version ORDER BY id')]
        rows = [dict(r) for r in db.execute(f'SELECT * FROM {table} ORDER BY id')]
    return schemas, versions, rows


def validate_map_pin(source, filename, raw, digest, archive_metadata):
    path = 'KIP126/LinProgram/Raw/'+filename
    matches = [a for a in source['artifacts'] if a['path'] == path]
    require(len(matches) == 1, 'map absent or duplicated in canonical source manifest: '+filename)
    artifact = matches[0]
    require(artifact['kind'] == 'machine_artifact' and artifact['required'] is True and
            artifact['sha256'] == digest == sha(raw) and artifact['size'] == len(raw),
            'canonical/raw map identity mismatch: '+filename)
    require(artifact['extracted_from'] == dict(record='Source/LWXMachine/zenodo-record.json',
            archive='kervaire_database.rar', archive_size=archive_metadata['size'],
            archive_checksum=archive_metadata['checksum'], member='kervaire-49/'+filename),
            'canonical same-archive map provenance mismatch: '+filename)


def read_inputs(root, archive):
    module_reader = load(root, 'map_module_presentations', 'generate-module-presentations.py')
    native = load(root, 'map_native_contract', 'native-contract.py')
    low = native.load_lowstem()
    # This existing reader calls checked_archive and validates every generator
    # and every relation of both source/target modules against the same S0 CSV/DB.
    module_list = module_reader.read_inputs(root, archive)
    modules = {m['object']: m for m in module_list}
    sources = [s for s in json.loads((root/'docs/external-inputs.json').read_text())['sources']
               if s['id'] == 'lwx_machine']
    require(len(sources) == 1, 'missing or duplicate canonical machine source')
    catalogue = native.pinned_map_catalogue(low)
    sphere_path, _, _ = low.pinned('S0_AdamsSS_t261.db')
    with native.connect(sphere_path) as sphere:
        ring = {r['id']: dict(r) for r in sphere.execute('SELECT * FROM S0_AdamsE2_generators ORDER BY id')}
    result = []
    with tempfile.TemporaryDirectory(prefix='complete-native-maps-') as tmp:
        for spec in SPECS:
            matches = [m for m in catalogue['maps'] if m['name'] == spec[0]]
            require(len(matches) == 1, spec[0]+': missing or duplicate catalogue entry')
            native_map = matches[0]; validate_catalogue(spec, native_map)
            filename = native_map['path']; member = 'kervaire-49/'+filename
            raw = subprocess.check_output(['unrar', 'p', '-inul', str(archive), member])
            # Both maps must be registered in Raw and the canonical source
            # manifest. A missing pin fails closed before any graph is decoded.
            _, pinned, digest = low.pinned(filename)
            require(raw == pinned, spec[0]+': authenticated archive/pinned map mismatch')
            validate_map_pin(sources[0], filename, raw, digest, module_list[0]['provenance']['archive'])
            path = Path(tmp)/filename; path.write_bytes(raw)
            schemas, versions, rows = read_database(native, module_reader, path, spec)
            validate_graph(spec, native_map, versions, rows, modules, ring)
            provenance = dict(module_list[0]['provenance'])
            provenance['pinned_entities'] = provenance['pinned_entities'] + [
                {'path': 'KIP126/LinProgram/Raw/'+filename, 'size': len(raw), 'sha256': digest}]
            provenance['map_archive_member'] = dict(member=member, size=len(raw), sha256=sha(raw))
            provenance['scope'] = 'Complete native graph only; no relation certificate, quotient descent, graded map, actual Ext comparison, or differential claim.'
            result.append(dict(schema='lin-native-complete-module-map/v1', native_name=spec[0],
                lean_module_name=spec[1], native_catalogue=native_map, native_schemas=schemas,
                native_version=versions, source=spec[2], target=spec[3], generator_count=spec[4],
                filtration=0, suspension=spec[5], t_max=200, rows=rows,
                same_module_inputs=[dict(object=m['object'], generator_count=m['generator_count'],
                    relation_count=m['relation_count'], generator_rows_sha256=sha(canonical(m['generators'])),
                    relation_rows_sha256=sha(canonical(m['relations']))) for m in module_list],
                mathematical_map_certified=False, actual_model_comparison_certified=False,
                provenance=provenance))
    return result


@module_output
def render_lean(graph):
    name = graph['lean_module_name']; quote = lambda s: json.dumps(s, ensure_ascii=False)
    lines = ['import KIP126.LinProgram.Generated.ModuleMaps.Data', '',
             '/-! Complete v126.3.cw49 native graph, in original source ID order.',
             'Reproduce with Translate/generate-module-maps.py. Empty strings are',
             'recorded zeros. This data does not certify quotient descent or an actual map. -/',
             'namespace KIP126.LinModule.RawData.Maps.'+name, '',
             f'def sourceName : String := {quote(graph["source"])}',
             f'def targetName : String := {quote(graph["target"])}',
             f'def sourceGeneratorCount : Nat := {graph["generator_count"]}',
             f'def filtration : Int := {graph["filtration"]}',
             f'def suspension : Int := {graph["suspension"]}',
             f'def tMax : Nat := {graph["t_max"]}', '', 'def rows : Array ImageRow := #[',
             ',\n'.join(f'  ⟨{r["id"]}, {quote(r["map"])}⟩' for r in graph['rows'])+']', '',
             'def imageCodes : Array String := rows.map ImageRow.image', '',
             'set_option maxRecDepth 16384 in',
             'theorem imageCodes_size : imageCodes.size = sourceGeneratorCount := by',
             '  simp only [imageCodes, Array.size_map]',
             '  rfl', '',
             '/-- Total on the complete source family; missing IDs never default to zero. -/',
             'def imageCode (i : Fin sourceGeneratorCount) : String :=',
             '  imageCodes[i.val]\'(by simpa only [imageCodes_size] using i.isLt)', '',
             'end KIP126.LinModule.RawData.Maps.'+name, '']
    return '\n'.join(lines).encode()


def build_outputs(graphs):
    require([g['native_name'] for g in graphs] == [s[0] for s in SPECS], 'complete graph set/order changed')
    outputs = {'Data.lean': lean_module(DATA_LEAN).encode()}
    for graph in graphs:
        require(graph['mathematical_map_certified'] is False and graph['actual_model_comparison_certified'] is False,
                'data exporter cannot assert mathematical map certification')
        name = graph['lean_module_name']
        outputs[name+'.json'] = canonical(graph)
        outputs[name+'.lean'] = render_lean(graph)
    outputs['manifest.json'] = canonical(dict(schema='lin-native-complete-module-map-export/v1',
        generator='KIP126/LinProgram/Translate/generate-module-maps.py',
        source_manifest='docs/external-inputs.json', source_id='lwx_machine', release='v126.3.cw49',
        mathematical_map_certified=False, actual_model_comparison_certified=False,
        outputs=[dict(path=OUTPUT_PREFIX+'/'+name, size=len(data), sha256=sha(data))
                 for name, data in sorted(outputs.items())]))
    return outputs


def check_outputs(output_dir, outputs):
    for name, expected in outputs.items():
        path = output_dir/name
        require(path.is_file() and path.read_bytes() == expected,
                'generated native map output differs from authenticated reconstruction: '+str(path))


def check_registered_outputs(root, outputs):
    registry = json.loads((root/'docs/external-inputs.json').read_text())
    source = next(s for s in registry['sources'] if s['id'] == 'lwx_machine')
    for spec in SPECS:
        path = 'KIP126/LinProgram/Raw/'+expected_catalogue(spec)['path']
        artifact = next(a for a in source['artifacts'] if a['path'] == path)
        derived = artifact.get('derived_outputs', {})
        names = [spec[1]+'.json', spec[1]+'.lean', 'Data.lean', 'manifest.json']
        expected = [dict(path=OUTPUT_PREFIX+'/'+name, size=len(outputs[name]),
                         sha256=sha(outputs[name])) for name in names]
        require(derived.get('complete_module_map_graph') == expected,
                'canonical derived native map identity mismatch: '+spec[0])
        require(derived.get('mathematical_map_certified') is False and
                derived.get('actual_model_comparison_certified') is False,
                'canonical native map graph cannot promote certification')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    fallback = Path(__file__).resolve().parents
    parser.add_argument('--root', type=Path, default=fallback[3] if len(fallback) > 3 else Path.cwd())
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--output-dir', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args(); root = args.root.resolve()
    require(args.check or args.output_dir is not None, 'generation requires explicit --output-dir')
    output_dir = args.output_dir or root/OUTPUT_PREFIX
    outputs = build_outputs(read_inputs(root, args.archive or root/'Source/LWXMachine/kervaire_database.rar'))
    if args.check:
        check_outputs(output_dir, outputs)
        check_registered_outputs(root, outputs)
    else:
        output_dir.mkdir(parents=True, exist_ok=True)
        for name, content in outputs.items():
            (output_dir/name).write_bytes(content)
    print(('Verified' if args.check else 'Generated')+' full native map graphs: Ceta 887 IDs and CW_nu_eta 844 IDs.')
    print('Mathematical map certification: false; actual model comparison: false.')
    for name, content in sorted(outputs.items()):
        print(f'{name}: {len(content)} bytes; sha256={sha(content)}')


if __name__ == '__main__':
    main()
