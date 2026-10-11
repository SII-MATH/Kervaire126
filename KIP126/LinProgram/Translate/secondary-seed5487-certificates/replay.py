#!/usr/bin/env python3
"""Replay the complete native 96-row secondary certificate using the fixed DAG engine.

The mathematical contract and status vocabulary differ from a native quotient map.
The underlying freezing, dependency resolution, kernel invocation and receipt checks
are reused without editing the module-map runner or its live production inputs.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ENGINE_SHA = '32a7e7fc0076c0b96c435981096950ceec695f839b41ae422ef77535bd1127a6'
SEMANTIC = '088958541d91f6a987c825ab94a3266001cf94e6eccdf19757ac9b39d92c69fa'
DATABASES = {
    'S0_Adams_res.db': '808235c2575ca647100975c5bab4a577bd0aa2c718dbbf1521ff60e1ddc3b1ba',
    'S0_Adams_d2.db': 'b97e88747fbbd348961282afd46780a05062d9501c98d6def79efed79176570b',
}
BASE = 'KIP126.LinProgram.Certificates.Secondary.Seed5487'
FINAL = BASE + '.Full.Compositions'
AUDIT = BASE + '.Full.CompositionChecks'


def contract(engine, output, manifest, jobs, package):
    require = engine.require
    require(manifest.get('schema') == 'seed5487-complete-native-certification-sources/v1',
            'unsupported complete secondary source schema')
    bindings = manifest.get('bindings', {})
    require(bindings.get('native_row_count') == 96 and bindings.get('rank') == 8 and
            bindings.get('native_rows_semantic_sha256') == SEMANTIC,
            'wrong fixed native secondary input')
    row_ids = manifest.get('complete_native_row_ids', [])
    require(len(row_ids) == len(set(row_ids)) == 96,
            'all 96 distinct native row IDs are required')
    require(manifest.get('complete_product_ids') == list(range(15839)),
            'all 15839 original ordered products are required')
    require({n for n,j in jobs.items() if j['kind'] == 'final'} == {FINAL} and
            {n for n,j in jobs.items() if j['kind'] == 'audit'} == {AUDIT},
            'missing fixed full composition theorem or audit')
    blocks = {BASE + f'.Full.Compositions{i:03d}' for i in range(12)}
    require(set(jobs[FINAL]['dependencies']) == blocks,
            'final theorem must use every complete eight-row block')
    require(AUDIT in jobs and FINAL in jobs[AUDIT]['dependencies'],
            'final audit must consume the full theorem')
    require(engine.selected_jobs(jobs, [AUDIT]) == set(jobs),
            'every generated product and composition must be in the full audit closure')
    ordered_ids = [rid for name in sorted(blocks) for rid in jobs[name].get('original_ids', [])]
    require(ordered_ids == row_ids, 'composition blocks do not cover exactly all original rows')
    product_jobs = [j for j in jobs.values()
                    if j.get('artifact_kind', j['kind']) == 'original_product_certificates']
    product_ids = [pid for j in product_jobs for pid in j.get('original_ids', [])]
    require(len(product_ids) == 15839 and sorted(product_ids) == list(range(15839)),
            'product blocks omit or duplicate an original product')
    require(len(product_jobs) == 271 and manifest.get('products_per_chunk') == 64,
            'unsupported complete product partition')
    table_jobs = [j for j in jobs.values()
                  if j.get('artifact_kind', j['kind']) == 'complete_original_rank_coproduct_table']
    degrees = [d for j in table_jobs for d in j.get('original_ids', [])]
    require(len(table_jobs) == 39 and sorted(degrees) == [d for d in range(1, 41) if d != 38],
            'all 39 complete original-rank degree tables are required')
    require(not manifest.get('direct_products', False),
            'this replay requires the complete shared-table production plan')
    root = Path(manifest['source_root'])
    command = [sys.executable, str(package / 'generate.py'), '--root', str(root),
               '--output-dir', str(output), '--witness',
               str(output / manifest['auxiliary_witness']['path']), '--check']
    databases = manifest.get('source_databases', {})
    require(set(databases) == {'S0_Adams_res.db', 'S0_Adams_d2.db'},
            'both fixed native databases are required for source regeneration')
    require(all(isinstance(databases[n], dict) and databases[n].get('sha256') == digest
                and isinstance(databases[n].get('path'), str) for n, digest in DATABASES.items()),
            'native database bindings must retain both original digests')
    generation_inputs = {str((root / p).resolve()): h
                         for p, h in manifest.get('generation_inputs', {}).items()}
    for name in ('generate.py', 'replay.py'):
        source = (package / name).resolve()
        require(generation_inputs.get(str(source)) == engine.digest(source),
                'missing or altered fixed replay tool: ' + name)
    command += ['--resolution-db', databases['S0_Adams_res.db']['path'],
                '--secondary-db', databases['S0_Adams_d2.db']['path']]
    log = output / 'logs/complete-plan-check.log'
    with log.open('w') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    require(result.returncode == 0,
            'independent full source regeneration failed: ' + str(log))
    return {'schema': manifest['schema'], 'final': FINAL, 'audit': AUDIT,
            'native_rows': 96, 'ordered_products': 15839,
            'generator': str(package / 'generate.py')}


def translate_status(value):
    if not isinstance(value, dict) or 'complete_native_quotient_map_certified' not in value:
        return value
    result = dict(value)
    result['full_native_96_composition_certified'] = result.pop('complete_native_quotient_map_certified')
    result.pop('actual_spectrum_map_comparison_certified', None)
    result['secondary_associator_certified'] = False
    result['actual_d2_certified'] = False
    return result


def configure(engine, package):
    engine.SCHEMA = 'lin-secondary-seed5487-runner/v1-fixed-inputs'
    engine.validate_complete_plan = lambda output, manifest, jobs: contract(
        engine, output, manifest, jobs, package)
    original_atomic = engine.atomic
    engine.atomic = lambda path, value: original_atomic(path, translate_status(value))


def main():
    package = Path(__file__).resolve().parent
    helper = package.parent / 'module-map-certificates/runner.py'
    # Import exactly the engine already reviewed for fixed inputs and full receipts.
    import hashlib
    if hashlib.sha256(helper.read_bytes()).hexdigest() != ENGINE_SHA:
        raise ValueError('reviewed fixed-input replay engine changed')
    spec = importlib.util.spec_from_file_location('secondary_fixed_dag_engine', helper)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    configure(engine, package)
    engine.entrypoint()


if __name__ == '__main__':
    main()
