#!/usr/bin/env python3
"""Rebuild all 96 native rows and every product certificate source.

This deterministic producer is untrusted. Generated Lean theorems must be
kernel checked; generator success never certifies an actual Adams differential.
--check reconstructs every output in memory and performs no writes.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path
import sqlite3
import sys

import sys as _module_sys
from pathlib import Path as _ModulePath
_module_sys.path.insert(0, str(_ModulePath(__file__).resolve().parent.parent))
from lean_module import lean_module, module_output

sys.dont_write_bytecode = True

SEMANTIC = '088958541d91f6a987c825ab94a3266001cf94e6eccdf19757ac9b39d92c69fa'
DATABASES = {
    'S0_Adams_res.db': '808235c2575ca647100975c5bab4a577bd0aa2c718dbbf1521ff60e1ddc3b1ba',
    'S0_Adams_d2.db': 'b97e88747fbbd348961282afd46780a05062d9501c98d6def79efed79176570b',
}
EXTRACTOR_SHA = '7e84ccd4dba6a81362885403f99f9fb558385a5268eb2e71c4feb0bdf0482bdf'
ARCHIVE_SHA = 'dd784541626f4d693c35f3ca84d4a67e83758ac463aabe58ab6c9cc92be22a15'
LEAN_ROOT = 'KIP126.LinProgram.Certificates.Secondary.Seed5487'
NAMESPACE = 'KIP126.Computation.Secondary.Seed5487.Full'


def monomial(value):
    return '[' + ','.join(map(str, value)) + ']'


def polynomial(value):
    return '[' + ','.join(monomial(m) for m in value) + ']'


def expression(value):
    return '[' + ','.join('⟨' + monomial(t['sq']) + ',' + str(t['v']) + '⟩' for t in value) + ']'


@lru_cache(maxsize=None)
def degree_basis(rank, degree):
    if rank == 0:
        return ((),) if degree == 0 else ()
    weight = 2 ** rank - 1
    return tuple(m + (e,) for e in range(degree // weight + 1)
                 for m in degree_basis(rank - 1, degree - e * weight))


def tensor_multiply(left, right):
    return tuple((tuple(x + y for x, y in zip(a[0], b[0])),
                  tuple(x + y for x, y in zip(a[1], b[1]))) for a in left for b in right)


def fast_power(rank, terms, n):
    if n == 0:
        return (((0,) * rank, (0,) * rank),)
    squared = tuple((tuple(2 * x for x in a), tuple(2 * x for x in b))
                    for a, b in fast_power(rank, terms, n // 2))
    return squared if n % 2 == 0 else tensor_multiply(squared, terms)


def fast_coproduct(rank, m):
    acc = (((0,) * rank, (0,) * rank),)
    for j in range(rank):
        k = j + 1
        generator = tuple((tuple(2 ** i if a + 1 == k - i else 0 for a in range(rank)),
                           tuple(1 if a + 1 == i else 0 for a in range(rank)))
                          for i in range(k + 1))
        acc = tensor_multiply(acc, fast_power(rank, generator, m[j]))
    return acc


def table_literal(rank, degree):
    return '[' + ',\n  '.join('(' + monomial(m) + ',[' +
                              ','.join('(' + monomial(a) + ',' + monomial(b) + ')'
                                       for a, b in fast_coproduct(rank, m)) + '])'
                              for m in degree_basis(rank, degree)) + ']'


@module_output
def encode_lean(lines):
    return ('\n'.join(lines) + '\n').encode()


def lean_path(module):
    return 'src/' + module.replace('.', '/') + '.lean'


def balanced_provider(lo=0, hi=248, indent=2):
    if hi - lo == 1:
        return [' ' * indent + f'certifiedProductTable certifiedProductChunk{lo:03d} (id - {lo * 64})']
    mid = (lo + hi) // 2
    return ([' ' * indent + f'if id < {mid * 64} then'] +
            balanced_provider(lo, mid, indent + 2) + [' ' * indent + 'else'] +
            balanced_provider(mid, hi, indent + 2))


def balanced_provider_sound(lo=0, hi=248, indent=2):
    if hi - lo == 1:
        return [' ' * indent + 'exact certifiedProductTable_sound _ _ _ h']
    mid = (lo + hi) // 2
    name = f'h{lo}_{hi}'
    return ([' ' * indent + f'by_cases {name} : id < {mid * 64}',
             ' ' * indent + f'· rw [if_pos {name}] at h'] +
            balanced_provider_sound(lo, mid, indent + 2) +
            [' ' * indent + f'· rw [if_neg {name}] at h'] +
            balanced_provider_sound(mid, hi, indent + 2))


def render_compositions(rows, emit, lean_root, namespace):
    if len(rows) != 96 or len({row['id'] for row in rows}) != 96:
        raise ValueError('the complete original 96-row family is required')
    spec = lean_root + '.Full.CompositionSpec'
    prefix = ['', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '',
              'namespace ' + namespace, 'open MilnorCertificates', '']
    lines = ['import ' + lean_root + '.FullInput', 'import ' + lean_root + '.Full.Products',
             'import ' + lean_root + '.Full.Plans'] + prefix
    lines += ['def productTable (id : Nat) : Option ProductEntry :='] + balanced_provider()
    lines += ['', 'theorem productTable_sound (id : Nat) (entry : ProductEntry)',
              '    (h : productTable id = some entry) :',
              '    IsMilnorProductAll 8 [entry.left] [entry.right] entry.output := by',
              '  unfold productTable at h'] + balanced_provider_sound()
    lines += ['',
        '/-- Original complete composition, plus a separate auxiliary-expression parity identity.',
        'This is a statement about the native module expressions, not an actual Adams differential',
        'or an independently established secondary associator construction. -/',
        'def RowCompositionCertified (row : NativeRow) : Prop :=',
        '  compose 8 (differentialImages (row.s - 1)) row.d = some (fun _ _ => false) ∧',
        '  compose 8 (differentialImages (row.s - 2)) row.f =',
        '    some (fun target m => expressionCoefficient row.d_f target m.val) ∧',
        '  compose 8 (liftImages (row.s - 1)) row.d =',
        '    some (fun target m => expressionCoefficient row.f_d target m.val) ∧',
        '  ∀ target m, expressionCoefficient row.d_f target m =',
        '    xor (expressionCoefficient row.f_d target m) (expressionCoefficient row.associator target m)', '',
        'end ' + namespace,
    ]
    emit(spec, lines, 'composition_spec', [row['id'] for row in rows])
    blocks = []
    for block, start in enumerate(range(0, 96, 8)):
        selected = rows[start:start+8]
        module = lean_root + f'.Full.Compositions{block:03d}'
        blocks.append(module)
        lines = ['import ' + spec] + prefix
        for row in selected:
            rid = row['id']; r = f'row{rid}'
            for kind in ('dd', 'df', 'fd'):
                image = 'liftImages' if kind == 'fd' else 'differentialImages'
                delta = 2 if kind == 'df' else 1
                source = 'f' if kind == 'df' else 'd'
                expected = '[]' if kind == 'dd' else r + '.' + ('d_f' if kind == 'df' else 'f_d')
                target = 'some (fun _ _ => false)' if kind == 'dd' else f'some (fun target m => expressionCoefficient {expected} target m.val)'
                args = f'productTable ({image} ({r}.s - {delta})) {r}.{source} {r}_{kind}Paths {expected}'
                lines += [f'theorem {r}_{kind}_check : indexedCompositionCheck {args} = true := by',
                          '  decide +kernel', '',
                          f'theorem {r}_{kind}_compose :',
                          f'    compose 8 ({image} ({r}.s - {delta})) {r}.{source} =',
                          '      ' + target + ' :=',
                          f'  indexedCompositionCheck_sound 8 {args} productTable_sound {r}_{kind}_check', '']
            lines += [f'theorem {r}_auxiliary_parity_check :',
                      f'    fastExpressionEqCheck {r}.d_f ({r}.f_d ++ {r}.associator) = true := by',
                      '  decide +kernel', '',
                      f'theorem {r}_auxiliary_parity (target : Nat) (m : Monomial) :',
                      f'    expressionCoefficient {r}.d_f target m =',
                      f'      xor (expressionCoefficient {r}.f_d target m)',
                      f'        (expressionCoefficient {r}.associator target m) := by',
                      f'  simpa only [expressionCoefficient_append] using',
                      f'    fastExpressionEqCheck_sound {r}.d_f ({r}.f_d ++ {r}.associator)',
                      f'      {r}_auxiliary_parity_check target m', '',
                      f'theorem {r}_composition_certified : RowCompositionCertified {r} :=',
                      f'  ⟨{r}_dd_compose, {r}_df_compose, {r}_fd_compose, {r}_auxiliary_parity⟩', '']
        lines += ['end ' + namespace]
        emit(module, lines, 'complete_composition_rows', [row['id'] for row in selected])
    module = lean_root + '.Full.Compositions'
    lines = ['import ' + block for block in blocks] + prefix
    lines += ['theorem allNativeRows_composition_certified :',
              '    ∀ row ∈ nativeRows, RowCompositionCertified row := by',
              '  intro row h',
              '  simp only [nativeRows, List.mem_cons, List.not_mem_nil, or_false] at h',
              '  rcases h with ' + ' | '.join('h' for _ in rows)]
    lines += [f"  · subst row; exact row{row['id']}_composition_certified" for row in rows]
    lines += ['', 'theorem allNativeRows_dd_zero (row : NativeRow) (h : row ∈ nativeRows) :',
              '    compose 8 (differentialImages (row.s - 1)) row.d = some (fun _ _ => false) :=',
              '  (allNativeRows_composition_certified row h).1', '',
              'theorem allNativeRows_df (row : NativeRow) (h : row ∈ nativeRows) :',
              '    compose 8 (differentialImages (row.s - 2)) row.f =',
              '      some (fun target m => expressionCoefficient row.d_f target m.val) :=',
              '  (allNativeRows_composition_certified row h).2.1', '',
              'theorem allNativeRows_fd (row : NativeRow) (h : row ∈ nativeRows) :',
              '    compose 8 (liftImages (row.s - 1)) row.d =',
              '      some (fun target m => expressionCoefficient row.f_d target m.val) :=',
              '  (allNativeRows_composition_certified row h).2.2.1', '',
              '/-- Equality of the recorded auxiliary expressions only. -/',
              'theorem allNativeRows_auxiliary_parity (row : NativeRow) (h : row ∈ nativeRows)',
              '    (target : Nat) (m : Monomial) :',
              '    expressionCoefficient row.d_f target m =',
              '      xor (expressionCoefficient row.f_d target m) (expressionCoefficient row.associator target m) :=',
              '  (allNativeRows_composition_certified row h).2.2.2 target m', '',
              'end ' + namespace]
    emit(module, lines, 'all_original_compositions', [row['id'] for row in rows])
    audit = lean_root + '.Full.CompositionChecks'
    names = ('allNativeRows_composition_certified', 'allNativeRows_dd_zero',
             'allNativeRows_df', 'allNativeRows_fd', 'allNativeRows_auxiliary_parity')
    lines = ['import ' + module, 'import Lean.Elab.Command', '',
             'open Lean Elab Command in', 'run_cmd do', '  let env ← getEnv',
             '  for mod in env.allImportedModuleNames do',
             '    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||',
             '        (`KIP126.Def).isPrefixOf mod then',
             '      throwError "complete secondary certificate imported an actual-model dependency: {mod}"',
             '  let logical := [``propext, ``Classical.choice, ``Quot.sound]',
             '  for decl in [' + ', '.join('``' + namespace + '.' + name for name in names) + '] do',
             '    for ax in (← collectAxioms decl) do',
             '      unless logical.contains ax do',
             '        throwError "unexpected axiom in complete secondary certificate {decl}: {ax}"', '',
             'namespace ' + namespace, '',
             'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '',
             'example : nativeRows.length = 96 := by decide',
             'example : nativeRows.map (·.id) = [' + ','.join(str(row['id']) for row in rows) + '] := by decide',
             'example : certifiedProductCount = 15839 := by decide', '']
    lines += ['#print axioms ' + name for name in names]
    lines += ['', 'end ' + namespace]
    emit(audit, lines, 'complete_composition_axiom_audit', [row['id'] for row in rows])


def render_lean(rows, products, path_rows, block_size, product_import, indexed_import,
                table_import, direct_products):
    files, jobs = {}, []
    def emit(module, lines, kind, ids=None):
        payload = encode_lean(lines)
        path = lean_path(module)
        files[path] = payload
        imports = [line.split(' ', 1)[1] for line in lines if line.startswith('import ')]
        jobs.append({'module': module, 'source': path, 'sha256': sha(payload),
                     'kind': kind, 'imports': imports, 'original_ids': ids or []})
    input_module = LEAN_ROOT + '.FullInput'
    lines = ['import KIP126.LinProgram.Certificates.Secondary.Data', '',
             '/-! Complete 96-row transcription. Native d/f are database columns;',
             'd_f/f_d/associator are auxiliary proposed expressions, not assumed identities.',
             'The two missing initial f records have explicit base definitions below.',
             'Every other absent image is rejected. No actual Adams comparison is asserted. -/', '',
             'set_option maxRecDepth 100000', '', 'namespace ' + NAMESPACE, '',
             '/-- Explicit initial lift definition for the degree-zero generator. -/',
             'def initialLift0 : ModuleExpression := []', '',
             '/-- Explicit initial lift definition at s=1,v=0, absent from the native f table. -/',
             'def initialLift524288 : ModuleExpression := []', '']
    for row in rows:
        lines.append(f"def row{row['id']} : NativeRow where")
        lines.extend(f'  {key} := {row[key]}' for key in ('id', 's', 'v', 't'))
        for key in ('d', 'f', 'd_f', 'f_d', 'associator'):
            value = f"initialLift{row['id']}" if key == 'f' and row['id'] in (0, 524288) else expression(row[key])
            lines.append(f'  {key} := {value}')
        lines.append('')
    lines += ['def nativeRows : List NativeRow :=',
              '  [' + ','.join(f"row{r['id']}" for r in rows) + ']', '',
              '/-- Only original stage/local-generator pairs are available. -/',
              'def nativeRow? : Nat → Nat → Option NativeRow']
    lines += [f"  | {r['s']}, {r['v']} => some row{r['id']}" for r in rows]
    lines += ['  | _, _ => none', '',
              'def differentialImages (s v : Nat) : Option ModuleExpression :=',
              '  (nativeRow? s v).map (·.d)', '',
              'def liftImages (s v : Nat) : Option ModuleExpression :=',
              '  (nativeRow? s v).map (·.f)', '', 'end ' + NAMESPACE]
    emit(input_module, lines, 'full_native_input', [r['id'] for r in rows])
    grouped = {}
    for product in products:
        grouped.setdefault(product['degree'], []).append(product)
    product_modules = []
    for degree, group in sorted(grouped.items()):
        table_module = LEAN_ROOT + f'.Full.Degree{degree:03d}'
        if not direct_products:
            basis = degree_basis(8, degree)
            stem = f'degree{degree:03d}'
            lines = ['import ' + table_import, '', 'set_option maxRecDepth 100000',
                     'set_option maxHeartbeats 0', '', 'namespace ' + NAMESPACE,
                     'open MilnorCertificates', '',
                     f'def {stem}Basis : List Monomial := ' + polynomial(basis), '',
                     f'theorem {stem}Basis_eq : {stem}Basis = degreeBasis 8 {degree} := by',
                     '  apply eq_of_beq', '  decide +kernel', '']
            for i, m in enumerate(basis):
                terms = '[' + ','.join('(' + monomial(a) + ',' + monomial(b) + ')'
                                        for a, b in fast_coproduct(8, m)) + ']'
                lines += [f'def {stem}Row{i:03d} : List TensorMonomial := ' + terms, '',
                          f'theorem {stem}Row{i:03d}_eq : {stem}Row{i:03d} = fastCoproduct 8 ' + monomial(m) + ' := by',
                          '  apply eq_of_beq', '  decide +kernel', '']
            lines += [f'def {stem}Rows : List (Monomial × List TensorMonomial) :=',
                      '  [' + ','.join('(' + monomial(m) + f',{stem}Row{i:03d})'
                                     for i, m in enumerate(basis)) + ']', '',
                      f'theorem {stem}Rows_complete : {stem}Rows =',
                      f'    (degreeBasis 8 {degree}).map (fun m => (m, fastCoproduct 8 m)) := by',
                      f'  rw [← {stem}Basis_eq]',
                      f'  simp only [{stem}Rows, {stem}Basis, List.map_cons, List.map_nil, ' +
                      ','.join(f'{stem}Row{i:03d}_eq' for i in range(len(basis))) + ']', '',
                      f'def {stem}Table : HomogeneousCoproductTable 8 {degree} :=',
                      f'  ⟨{stem}Rows, {stem}Rows_complete⟩', '', 'end ' + NAMESPACE]
            emit(table_module, lines, 'complete_original_rank_coproduct_table', [degree])
        for index, start in enumerate(range(0, len(group), block_size)):
            chosen = group[start:start + block_size]
            module = LEAN_ROOT + f'.Full.ProductsD{degree:03d}B{index:03d}'
            product_modules.append(module)
            lines = ['import ' + (product_import if direct_products else table_module), '', 'set_option maxRecDepth 100000',
                     'set_option maxHeartbeats 0', '', 'namespace ' + NAMESPACE,
                     'open MilnorCertificates', '']
            for p in chosen:
                stem = f"product{p['id']:05d}"
                checker = f'fastSingletonProductCheck_sound 8' if direct_products else f'fastSingletonProductCheckWithTable_sound degree{degree:03d}Table'
                lines += [f'def {stem}Left : Monomial := ' + monomial(p['left']),
                          f'def {stem}Right : Monomial := ' + monomial(p['right']),
                          f'def {stem}Output : Polynomial := ' + polynomial(p['output']), '',
                          f'theorem {stem}_certified :',
                          f'    IsMilnorProductAll 8 [{stem}Left] [{stem}Right] {stem}Output :=',
                          f'  {checker} {stem}Left {stem}Right',
                          f'    {stem}Output (by decide +kernel)', '']
            lines += ['end ' + NAMESPACE]
            emit(module, lines, 'original_product_certificates', [p['id'] for p in chosen])
    module = LEAN_ROOT + '.Full.Products'
    lines = ['import ' + indexed_import] + ['import ' + m for m in product_modules]
    lines += ['', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '', 'namespace ' + NAMESPACE, '',
              '/-- Original lexicographic product IDs, in complete groups of at most 64.',
              'Each entry carries its genuine checked product theorem. -/']
    chunk_names = []
    for i, start in enumerate(range(0, len(products), 64)):
        name = f'certifiedProductChunk{i:03d}'
        chunk_names.append(name)
        lines += [f'def {name} : Array (CertifiedProductEntry 8) := #[']
        chosen = products[start:start+64]
        lines += [f"  ⟨⟨product{p['id']:05d}Left, product{p['id']:05d}Right, product{p['id']:05d}Output⟩, product{p['id']:05d}_certified⟩" +
                  (',' if j+1 < len(chosen) else '') for j, p in enumerate(chosen)]
        lines += [']', '']
    lines += ['def certifiedProductCount : Nat :=',
              '  [' + ','.join(name + '.size' for name in chunk_names) + '].sum', '',
              'end ' + NAMESPACE]
    emit(module, lines, 'full_certified_product_chunks', [p['id'] for p in products])
    module = LEAN_ROOT + '.Full.Plans'
    lines = ['import ' + indexed_import, '', 'set_option maxRecDepth 100000',
             'set_option maxHeartbeats 0', '', 'namespace ' + NAMESPACE, '']
    for row in path_rows:
        for kind in ('dd', 'df', 'fd'):
            literal = '[' + ','.join(f"⟨{p['product_id']},{p['target']}⟩" for p in row[kind]) + ']'
            lines += [f"def row{row['id']}_{kind}Paths : List IndexedPath :=", '  ' + literal, '']
    lines += ['end ' + NAMESPACE]
    emit(module, lines, 'all_original_composition_plans', [r['id'] for r in rows])
    render_compositions(rows, emit, LEAN_ROOT, NAMESPACE)
    return files, jobs


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def sha(value):
    return hashlib.sha256(value).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--witness', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--resolution-db', type=Path)
    parser.add_argument('--secondary-db', type=Path)
    parser.add_argument('--products-per-chunk', type=int, default=64)
    parser.add_argument('--product-import', default='KIP126.LinProgram.Certificates.Secondary.Milnor.Products')
    parser.add_argument('--indexed-import', default='KIP126.LinProgram.Certificates.Secondary.IndexedExpansion')
    parser.add_argument('--table-import', default='KIP126.LinProgram.Certificates.Secondary.Milnor.ProductTables')
    parser.add_argument('--direct-products', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    args.root = args.root.resolve()
    require(1 <= args.products_per_chunk <= 256, 'chunk size outside supported range')
    raw = args.witness.read_bytes()
    witness = json.loads(raw)
    rows = witness['generators']
    require(len(rows) == 96 and sha(canonical(rows)) == SEMANTIC, 'wrong whole native closure')
    helper = args.root / 'KIP126/LinProgram/Translate/extract-secondary-witness.py'
    require(sha(helper.read_bytes()) == EXTRACTOR_SHA, 'fixed extractor source drift')
    audit = json.loads((args.root / 'KIP126/LinProgram/Generated/Provenance/seed5487-next.json').read_bytes())
    require(audit['independent_extraction']['input_hashes'] == DATABASES and
            audit['independent_extraction']['chain_semantic_sha256'] == SEMANTIC,
            'source rebuild record does not bind the same complete native closure')
    archive = args.root / 'Source/LWXMachine/source-code.zip'
    require(sha(archive.read_bytes()) == ARCHIVE_SHA == audit['source_archive']['sha256'],
            'fixed original source archive drift')
    inventory = json.loads((args.root / 'docs/external-inputs.json').read_bytes())
    sources = [source for source in inventory['sources'] if source['id'] == 'lwx_machine']
    require(len(sources) == 1, 'canonical source must be unique')
    records = [a for a in sources[0]['artifacts'] if a['path'] == 'Source/LWXMachine/source-code.zip']
    require(len(records) == 1, 'canonical source archive artifact must be unique')
    artifact = records[0]
    require(artifact['sha256'] == ARCHIVE_SHA and artifact['size'] == archive.stat().st_size and
            artifact['reproduction']['existing_extraction_and_rebuild_record'] ==
            'KIP126/LinProgram/Generated/Provenance/seed5487-next.json', 'canonical archive/reproduction linkage drift')
    derived = artifact['derived_outputs']
    require(derived['selected_witness']['complete_96_row_semantic_sha256'] == SEMANTIC,
            'canonical complete closure semantic linkage drift')
    for key, expected_path in [('selected_witness', 'KIP126/LinProgram/Certificates/Secondary/Seed5487/source.json'),
                                ('fixed_input', 'KIP126/LinProgram/Certificates/Secondary/Seed5487/Input.lean')]:
        require(derived[key]['path'] == expected_path and
                derived[key]['sha256'] == sha((args.root / expected_path).read_bytes()),
                'canonical existing selected derivation drift: ' + key)
    spec = importlib.util.spec_from_file_location('secondary_full_product_source', helper)
    ext = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ext)
    paths = {Path(p).name: Path(p) for p in witness['input_hashes']}
    require(set(paths) == set(DATABASES), 'exactly two original databases are required')
    if args.resolution_db:
        paths['S0_Adams_res.db'] = args.resolution_db
    if args.secondary_db:
        paths['S0_Adams_d2.db'] = args.secondary_db
    for name, digest in DATABASES.items():
        require(sha(paths[name].read_bytes()) == digest, 'original database drift: ' + name)
    connections = {name: sqlite3.connect('file:' + str(path.resolve()) + '?mode=ro', uri=True)
                   for name, path in paths.items()}
    native_d = {r[0]: (r[1], r[2], ext.decode(r[3])) for r in connections['S0_Adams_res.db'].execute(
        'SELECT id,s,t,diff FROM S0_Adams_res_generators')}
    native_f = {r[0]: ext.decode(r[1]) for r in connections['S0_Adams_d2.db'].execute(
        'SELECT id,d2 FROM S0_Adams_d2')}
    for connection in connections.values():
        connection.close()
    by_stage = {(r['s'], r['v']): r for r in rows}
    require(len(by_stage) == 96, 'duplicate original row')
    absent = []
    for row in rows:
        rid = row['id']
        require(rid == (row['s'] << 19) + row['v'], 'native ID mismatch')
        require(rid in native_d and native_d[rid][:2] == (row['s'], row['t']), 'missing native d row')
        require(ext.terms(native_d[rid][2]) == row['d'], 'native differential mismatch')
        if rid in native_f:
            require(ext.terms(native_f[rid]) == row['f'], 'native lift mismatch')
        else:
            absent.append(rid)
            require(rid in (0, 524288) and row['f'] == [], 'unprovided lift cannot become zero')
        for field in ('d', 'f', 'd_f', 'f_d', 'associator'):
            require(all(len(term['sq']) == 8 for term in row[field]), 'rank changed')
    require(absent == [0, 524288], 'base-lift exception set changed')
    path_rows = []
    all_pairs = set()
    kind_pairs = {kind: set() for kind in ('dd', 'df', 'fd')}
    for row in rows:
        item = {'id': row['id'], 's': row['s'], 'v': row['v'], 't': row['t']}
        for kind, field, shift, second in [('dd', 'd', 1, 'd'), ('df', 'f', 2, 'd'), ('fd', 'd', 1, 'f')]:
            paths_for_row = []
            for first in row[field]:
                key = (row['s'] - shift, first['v'])
                require(key in by_stage, 'missing original intermediate image')
                for next_term in by_stage[key][second]:
                    pair = (tuple(first['sq']), tuple(next_term['sq']))
                    paths_for_row.append((pair, next_term['v']))
                    all_pairs.add(pair)
                    kind_pairs[kind].add(pair)
            item[kind] = paths_for_row
        path_rows.append(item)
    pairs = sorted(all_pairs)
    pair_ids = {pair: index for index, pair in enumerate(pairs)}
    products = []
    for index, (left, right) in enumerate(pairs):
        degree = ext.degree(left) + ext.degree(right)
        output = ext.product(left, right)
        require(all(c == 1 and len(m) == 8 and ext.degree(m) == degree for m, c in output),
                'invalid F2 product output')
        products.append({'id': index, 'left': left, 'right': right,
                         'output': [m for m, _ in output], 'degree': degree,
                         'sufficient_small_rank': (degree + 1).bit_length() - 1})
    for row, item in zip(rows, path_rows):
        for kind, field in [('dd', None), ('df', 'd_f'), ('fd', 'f_d')]:
            result = set()
            indexed = []
            for pair, target in item[kind]:
                index = pair_ids[pair]
                indexed.append({'product_id': index, 'target': target})
                for monomial in products[index]['output']:
                    result.symmetric_difference_update({(tuple(monomial), target)})
            expected = {(tuple(term['sq']), term['v']) for term in row[field]} if field else set()
            require(result == expected, 'proposed composition differs at row ' + str(row['id']))
            item[kind] = indexed
        def expression(field):
            return {(tuple(term['sq']), term['v']) for term in row[field]}
        require(expression('d_f') == expression('f_d') ^ expression('associator'),
                'auxiliary expression parity differs')
    bindings = {'native_row_count': 96, 'rank': 8, 'native_rows_semantic_sha256': SEMANTIC,
                'database_sha256': DATABASES, 'witness_file_sha256': sha(raw),
                'original_source_archive_sha256': ARCHIVE_SHA,
                'canonical_original_link_sha256': sha(canonical({
                    'path': artifact['path'], 'sha256': artifact['sha256'], 'size': artifact['size'],
                    'rebuild_record': artifact['reproduction']['existing_extraction_and_rebuild_record'],
                    'selected_witness': derived['selected_witness'], 'fixed_input': derived['fixed_input']})),
                'extractor_source_sha256': sha(helper.read_bytes()),
                'generator_source_sha256': sha(Path(__file__).read_bytes())}
    product_data = {'schema': 'seed5487-complete-products/untrusted-v1',
                    'bindings': bindings, 'products': products,
                    'kernel_certified': False, 'actual_d2_certified': False}
    product_bytes = canonical(product_data)
    plan = {'schema': 'seed5487-complete-compositions/untrusted-v1', 'bindings': bindings,
            'products_sha256': sha(product_bytes), 'rows': path_rows,
            'expected_expressions': {'dd': 'zero', 'df': 'native-rows.d_f', 'fd': 'native-rows.f_d'},
            'explicit_base_lift_definitions': [{'id': rid, 'f': [], 'native_record_present': False}
                                               for rid in absent],
            'missing_other_image_policy': 'reject; never substitute zero',
            'kernel_certified': False, 'secondary_associator_certified': False,
            'actual_d2_certified': False}
    degree_counts = Counter(p['degree'] for p in products)
    def basis_count(degree):
        ways = [1] + [0] * degree
        for k in range(1, (degree + 1).bit_length()):
            weight = (1 << k) - 1
            for value in range(weight, degree + 1):
                ways[value] += ways[value - weight]
        return ways[degree]
    basis_counts = {degree: basis_count(degree) for degree in sorted(degree_counts)}
    summary = {'bindings': bindings, 'distinct_products': len(products),
               'path_counts': {kind: sum(len(row[kind]) for row in path_rows) for kind in kind_pairs},
               'distinct_products_by_kind': {kind: len(values) for kind, values in kind_pairs.items()},
               'product_output_terms': sum(len(p['output']) for p in products),
               'zero_products': sum(not p['output'] for p in products),
               'max_product_output_terms': max(len(p['output']) for p in products),
               'products_by_degree': degree_counts, 'exact_degree_basis_counts': basis_counts,
               'coefficient_tests': sum(n * basis_counts[d] for d, n in degree_counts.items()),
               'kernel_certified': False, 'actual_d2_certified': False}
    output = args.output_dir.resolve()
    files = {'witness.json': raw, 'native-rows.json': canonical(rows), 'products.json': product_bytes,
             'plan.json': canonical(plan), 'summary.json': canonical(summary)}
    lean_files, jobs = render_lean(rows, products, path_rows, args.products_per_chunk,
                                   args.product_import, args.indexed_import,
                                   args.table_import, args.direct_products)
    generated_modules = {job['module'] for job in jobs}
    for job in jobs:
        job['dependencies'] = sorted(set(job['imports']) & generated_modules)
        job['artifact_kind'] = job['kind']
        if job['kind'] == 'all_original_compositions':
            job['kind'] = 'final'
        elif job['kind'] == 'complete_composition_axiom_audit':
            job['kind'] = 'audit'
    source_names = ['Source/LWXMachine/source-code.zip', 'docs/external-inputs.json',
                    'KIP126/LinProgram/Generated/Provenance/seed5487-next.json',
                    'KIP126/LinProgram/Translate/extract-secondary-witness.py',
                    'KIP126/LinProgram/Translate/lean_module.py',
                    'KIP126/LinProgram/Certificates/Secondary/Seed5487/source.json',
                    'KIP126/LinProgram/Certificates/Secondary/Seed5487/Input.lean']
    pinned_source_hashes = {name: sha((args.root / name).read_bytes()) for name in source_names}
    pinned_source_hashes.update({str(paths[name].resolve()): digest for name, digest in DATABASES.items()})
    generation_inputs = {str(Path(__file__).resolve()): sha(Path(__file__).read_bytes())}
    replay_entry = Path(__file__).resolve().with_name('replay.py')
    if replay_entry.is_file():
        generation_inputs[str(replay_entry)] = sha(replay_entry.read_bytes())
    files.update(lean_files)
    manifest = {'schema': 'seed5487-complete-native-certification-sources/v1',
                'source_root': str(args.root), 'pinned_source_hashes': pinned_source_hashes,
                'auxiliary_witness': {'path': 'witness.json', 'sha256': sha(raw)},
                'generation_inputs': generation_inputs,
                'source_databases': {name: {'path': str(paths[name].resolve()), 'sha256': digest}
                                     for name, digest in DATABASES.items()},
                'bindings': bindings, 'products_per_chunk': args.products_per_chunk,
                'product_import': args.product_import, 'indexed_import': args.indexed_import,
                'table_import': args.table_import, 'direct_products': args.direct_products,
                'jobs': jobs, 'complete_native_row_ids': [r['id'] for r in rows],
                'complete_product_ids': [p['id'] for p in products],
                'full_native_96_composition_certified': False,
                'secondary_associator_certified': False, 'actual_d2_certified': False,
                'files': {name: {'sha256': sha(payload), 'bytes': len(payload)}
                          for name, payload in files.items()}}
    files['manifest.json'] = canonical(manifest)
    for name, payload in files.items():
        target = output / name
        if args.check:
            require(target.is_file() and target.read_bytes() == payload, 'generated output drift: ' + name)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(payload)
    if args.check:
        actual_sources = {str(path.relative_to(output)) for path in (output / 'src').rglob('*.lean')}
        require(actual_sources == set(lean_files), 'unexpected or missing generated Lean source')
    print(json.dumps({'output': str(output), 'products': len(products),
                      'path_counts': summary['path_counts'],
                      'coefficient_tests': summary['coefficient_tests'],
                      'lean_modules': len(jobs), 'lean_bytes': sum(map(len, lean_files.values())),
                      'total_bytes': sum(map(len, files.values())),
                      'manifest_sha256': sha(files['manifest.json']),
                      'checked': args.check,
                      'kernel_certified': False, 'actual_d2_certified': False}, indent=2))


if __name__ == '__main__':
    main()
