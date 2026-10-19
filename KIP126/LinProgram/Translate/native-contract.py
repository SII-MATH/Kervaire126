#!/usr/bin/env python3
"""Rebuild fixed native targets and auxiliary witnesses, never proof status.

The snapshot is derived data, not another source registry. Raw input identities
come from Raw/manifest.json; docs/external-inputs.json remains authoritative.
The existing low-stem extractor supplies the two polynomial witnesses. This
script checks their identities and archived relation membership independently,
and preserves the full nullable Raw.LogRow payload for the naturality target.
No database, literature binding, mathematical model, or Lean file is modified.
"""
import argparse
import csv
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
LIN = ROOT / "KIP126/LinProgram"
DEFAULT_OUTPUT = LIN / "Generated/NativeContract/manifest.json"
LOG_FIELDS = ("id", "depth", "reason", "name", "stem", "s", "t", "r", "x", "dx", "info")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_lowstem():
    spec = importlib.util.spec_from_file_location("lin_replay_lowstem", LIN / "Translate/replay-lowstem.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def pinned_map_catalogue(lowstem):
    # ss.json shares the existing Raw manifest/LFS/hash boundary. Parse exactly
    # the checked bytes, rather than reopening an unverified configuration.
    _, data, _ = lowstem.pinned("ss.json")
    return json.loads(data)


def connect(path):
    db = sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True)
    db.row_factory = sqlite3.Row
    db.execute("PRAGMA query_only=ON")
    return db


def raw_row(db, row_id):
    row = db.execute("SELECT * FROM log WHERE id=?", (row_id,)).fetchone()
    require(row is not None, f"missing log {row_id}")
    result = dict(row)
    require(tuple(result) == LOG_FIELDS, "Raw.LogRow column contract changed")
    return result


def raw_log_declaration(name, row):
    """Render the deliberately simple, complete Raw.LogRow transcription."""
    require(tuple(row) == LOG_FIELDS, "Raw.LogRow column contract changed")
    integer_fields = {"id", "depth", "stem", "s", "t", "r"}
    lines = [f"def {name} : LogRow where"]
    for field in LOG_FIELDS:
        value = row[field]
        if field == "id":
            require(type(value) is int, "native log id is not an integer")
            encoded = str(value)
        elif value is None:
            encoded = "none"
        elif field in integer_fields:
            require(type(value) is int, f"native log {field} is not an integer")
            encoded = f"some {value}" if value >= 0 else f"some ({value})"
        else:
            require(type(value) is str, f"native log {field} is not text")
            encoded = "some " + json.dumps(value, ensure_ascii=False)
        lines.append(f"  {field} := {encoded}")
    return "\n".join(lines)


def check_raw_naturality_declarations(text, source, target):
    # This checks the source candidate as well as the exported target. A Lean
    # theorem about the latter cannot establish the former's transcription.
    for name, row in (("sourceCandidate245130", source), ("target245131", target)):
        pattern = rf"(?ms)^def {re.escape(name)} : LogRow where\n.*?(?=\n\n|\Z)"
        blocks = re.findall(pattern, text)
        require(len(blocks) == 1 and blocks[0] == raw_log_declaration(name, row),
                f"Raw.Naturality.{name} transcription differs from pinned log {row['id']}")


def check_raw_high_stem_declarations(text, cw, source, target):
    """Keep all eleven fields for the complete fixed CW-to-Ceta-to-S0 chain."""
    for name, row in (("source462479Full", cw), ("source462480Full", source),
                      ("output462481Full", target)):
        pattern = rf"(?ms)^def {re.escape(name)} : LogRow where\n.*?(?=\n\n|\Z)"
        require(re.findall(pattern, text) == [raw_log_declaration(name, row)],
                f"Raw.NaturalityHighStem.{name} transcription differs from pinned log")


def coordinates(text):
    require(isinstance(text, str), "SQL NULL is not an empty coordinate vector")
    if text == "":
        return []
    require(re.fullmatch(r"[0-9]+(?:,[0-9]+)*", text), "unknown or malformed coordinate vector")
    result = list(map(int, text.split(",")))
    require(result == sorted(set(result)), "noncanonical coordinate vector")
    return result


def equation(row):
    require(isinstance(row["r"], int) and 2 <= row["r"] < 999, "not a finite-page equation")
    require(row["stem"] == row["t"] - row["s"], "inconsistent native bidegree")
    return {
        "spectrum": row["name"], "page": row["r"],
        "source": {"degree": [row["s"], row["t"]], "coordinates": coordinates(row["x"])},
        "target": {"degree": [row["s"] + row["r"], row["t"] + row["r"] - 1],
                   "coordinates": coordinates(row["dx"])},
    }


def validate_naturality(source, target, mapping):
    require(source["id"] + 1 == target["id"], "source candidate is not adjacent to target log")
    # An N output can itself be the source of another N step. These tags
    # only validate this fixed native chain; neither tag supplies a proof.
    require(source["reason"] in {"D", "N"} and source["depth"] == 0, "unsupported source candidate")
    require(target["reason"] == "N" and target["depth"] == 0, "not a root naturality log")
    require(mapping["name"] == target["info"], "naturality info does not name this map")
    require(mapping["from"] == source["name"] and mapping["to"] == target["name"],
            "map endpoints disagree with native logs")
    require(source["r"] == target["r"], "naturality page changed")
    require(mapping["type"] == "top_cell", "unsupported native map kind")
    require(source["s"] == target["s"] and source["t"] - mapping["sus"] == target["t"],
            "map suspension does not match the native source and target degrees")
    require(source["t"] + source["r"] - 1 <= mapping["t_max"], "source target exceeds map range")
    equation(source)
    equation(target)


def check_recovered_trace_snapshot(actual, reconstructed):
    require(actual == reconstructed,
            "recovered trace differs from fixed-input reconstruction; raw context or remaining premises changed")


def validate_recovered_trace(trace, source, target, mapping):
    """Bind the derived context to authenticated rows without treating it as a proof."""
    validate_naturality(source, target, mapping)
    require(trace["target"] == target, "recovered trace target differs from pinned log")
    rows = trace["adjacent_context"]["branch_rows"]
    sources = [row for row in rows if row["id"] == source["id"]]
    require(sources == [source], "recovered trace source differs from pinned log")
    require(trace["maps"]["ceta_to_sphere"]["native_map"] == mapping,
            "recovered trace map differs from pinned catalogue")
    require(bool(trace["remaining_propositions"]), "recovered trace erased actual-model obligations")


def validate_product_witness(certificate, relation_rows, lowstem):
    """Check an F2 polynomial identity without trusting reduction success."""
    def normalized(terms):
        result = set()
        for term in terms:
            code = ",".join(str(n) for pair in term for n in pair)
            result.symmetric_difference_update({lowstem.mon(code)})
        return result

    remainder = normalized(certificate["input"])
    remainder.symmetric_difference_update(normalized(certificate["output"]))
    locations = {}
    for ordinal, row in enumerate(relation_rows):
        locations.setdefault(row["rel"], []).append((ordinal, row))
    trace = []
    for item in certificate["trace"]:
        code = item["relation"]
        require(code in locations, "witness relation absent from pinned CSV")
        factor = lowstem.mon(",".join(str(n) for pair in item["factor"] for n in pair))
        for term in lowstem.polynomial(code):
            remainder.symmetric_difference_update({lowstem.mul(factor, term)})
        ordinal, row = locations[code][0]
        trace.append({**item, "csv_ordinal_zero_based": ordinal,
                      "relation_degree": [int(row["s"]), int(row["s"]) + int(row["stem"])]})
    require(not remainder, "auxiliary polynomial witness identity failed")
    return {**certificate, "trace": trace}


def sphere_coordinates(db, row):
    result = {}
    for side, native in equation(row).items():
        if side not in {"source", "target"}:
            continue
        s, t = native["degree"]
        rows = [dict(r) for r in db.execute(
            "SELECT * FROM S0_AdamsE2_basis WHERE s=? AND t=? ORDER BY id", (s, t))]
        require(rows, "missing sphere degree, even if coordinates are empty")
        chosen = []
        for index in native["coordinates"]:
            require(index < len(rows), "coordinate outside recorded sphere basis")
            chosen.append({**rows[index], "local_index": index})
        result[side] = chosen
    return result


def bulk_lookup(row):
    pattern = re.compile(r'⟨(\d+), "([^"]+)", (\d+), (\d+), (\d+), (\[[^\]]*\]), (\[[^\]]*\])⟩')
    matches = []
    for path in sorted((LIN / "Generated/Differentials").glob("Shard*.lean")):
        for offset, fields in enumerate(pattern.findall(path.read_text())):
            rid, reason, s, t, r, x, dx = fields
            if int(rid) == row["id"]:
                require((reason, int(s), int(t), int(r), json.loads(x), json.loads(dx)) ==
                        (row["reason"], row["s"], row["t"], row["r"],
                         coordinates(row["x"]), coordinates(row["dx"])),
                        "generated differential payload differs from native log")
                matches.append({"shard": int(path.stem[5:]), "offset": offset})
    require(len(matches) == 1, "native target has no unique generated differential row")
    return matches[0]


def validate_ceta_archive_origin(manifest):
    """The added inputs come from the already registered cw49 archive."""
    canonical = json.loads((ROOT / "docs/external-inputs.json").read_text())
    machine = next(s for s in canonical["sources"] if s["id"] == "lwx_machine")
    artifacts = {a["path"]: a for a in machine["artifacts"]}
    record_path = "Source/LWXMachine/zenodo-record.json"
    record_bytes = (ROOT / record_path).read_bytes()
    require(hashlib.sha256(record_bytes).hexdigest() == artifacts[record_path]["sha256"],
            "registered Zenodo record hash mismatch")
    record = json.loads(record_bytes)
    require(record["id"] == 14875701 and record["metadata"]["version"] == manifest["version"],
            "Ceta archive source version changed")
    archive = next(f for f in record["files"] if f["key"] == "kervaire_database.rar")
    for name in ("Ceta_AdamsSS_t200.db", "map_AdamsSS_Ceta_to_S0_t200.db"):
        entry = next(f for f in manifest["files"] if f["path"] == name)
        require(entry["extracted_from"] == {
            "record": "Source/LWXMachine/zenodo-record.json",
            "archive": archive["key"], "archive_size": archive["size"],
            "archive_checksum": archive["checksum"], "member": "kervaire-49/" + name,
        }, "Ceta input no longer identifies the fixed archive member")
        registered = artifacts["KIP126/LinProgram/Raw/" + name]
        require(all(registered[field] == entry[field] for field in ("size", "sha256", "extracted_from")),
                "Ceta Raw input disagrees with canonical source artifact")


def checked_schema(db, table, columns):
    schema = db.execute("SELECT sql FROM sqlite_master WHERE type='table' AND name=?", (table,)).fetchone()
    require(schema is not None, f"missing native table: {table}")
    actual = [dict(row) for row in db.execute(f'PRAGMA table_info("{table}")')]
    require([(row["name"], row["type"]) for row in actual] == columns,
            f"native table schema changed: {table}")
    return schema[0]


def native_ceta_map_slice(ceta, maps, sphere, source, target, mapping, lowstem):
    """Selected raw coordinate matrices, not actual Adams map comparisons.

    The observed map table stores images of MODULE GENERATORS. Extend these
    stored polynomials formally S0-linearly to the selected basis monomials.
    Only direct matches with the recorded target monomials are supported; a
    required quotient reduction is refused rather than silently assumed.
    """
    schemas = {
        "Ceta_AdamsE2_basis": checked_schema(ceta, "Ceta_AdamsE2_basis", [
            ("id", "INTEGER"), ("mon", "TEXT"), ("repr", "TEXT"),
            ("s", "SMALLINT"), ("t", "SMALLINT"), ("d2", "TEXT")]),
        "Ceta_AdamsE2_generators": checked_schema(ceta, "Ceta_AdamsE2_generators", [
            ("id", "INTEGER"), ("name", "TEXT"), ("repr", "SMALLINT"),
            ("s", "SMALLINT"), ("t", "SMALLINT"), ("cell", "SMALLINT"), ("cell_coeff", "TEXT")]),
        "Ceta_AdamsE2_ss": checked_schema(ceta, "Ceta_AdamsE2_ss", [
            ("id", "INTEGER"), ("s", "SMALLINT"), ("t", "SMALLINT"),
            ("base", "TEXT"), ("diff", "TEXT"), ("level", "SMALLINT")]),
        "map_AdamsE2_Ceta_to_S0": checked_schema(maps, "map_AdamsE2_Ceta_to_S0", [
            ("id", "INTEGER"), ("map", "TEXT")]),
        "source_version": checked_schema(ceta, "version", [
            ("id", "INTEGER"), ("name", "TEXT"), ("value", "")]),
        "map_version": checked_schema(maps, "version", [
            ("id", "INTEGER"), ("name", "TEXT"), ("value", "")]),
    }
    source_version = [dict(row) for row in ceta.execute("SELECT * FROM version ORDER BY id")]
    map_version = [dict(row) for row in maps.execute("SELECT * FROM version ORDER BY id")]
    metadata = {row["name"]: row["value"] for row in map_version}
    require(len(metadata) == len(map_version), "duplicate map version metadata")
    require((metadata.get("from"), metadata.get("to"), metadata.get("filtration"),
             metadata.get("suspension"), metadata.get("t_max")) ==
            (mapping["from"], mapping["to"], 0, mapping["sus"], mapping["t_max"]),
            "map database metadata disagrees with ss.json")
    validate_naturality(source, target, mapping)
    source_equation, target_equation = equation(source), equation(target)
    used_module_generators, used_images, used_ring_generators = {}, {}, {}

    def ring_degree(monomial):
        s, t = 0, 0
        for generator, exponent in monomial:
            row = sphere.execute("SELECT * FROM S0_AdamsE2_generators WHERE id=?", (generator,)).fetchone()
            require(row is not None, "unknown S0 coefficient generator")
            used_ring_generators[generator] = dict(row)
            s += row["s"] * exponent
            t += row["t"] * exponent
        return s, t

    slices = {}
    for side in ("source", "target"):
        source_degree = source_equation[side]["degree"]
        target_degree = target_equation[side]["degree"]
        source_basis = [dict(row) for row in ceta.execute(
            "SELECT * FROM Ceta_AdamsE2_basis WHERE s=? AND t=? ORDER BY id", source_degree)]
        target_basis = [dict(row) for row in sphere.execute(
            "SELECT * FROM S0_AdamsE2_basis WHERE s=? AND t=? ORDER BY id", target_degree)]
        require(source_basis and target_basis, "selected map source or target degree is absent")
        for rows in (source_basis, target_basis):
            for index, row in enumerate(rows):
                require(row["id"] == rows[0]["id"] + index, "noncontiguous native local basis")
                row["local_index"] = index
        target_indices = {lowstem.mon(row["mon"]): row["local_index"] for row in target_basis}
        require(len(target_indices) == len(target_basis), "duplicate target basis monomial")
        columns = []
        for row in source_basis:
            code = row["mon"]
            require(isinstance(code, str) and re.fullmatch(r"[0-9]+(?:,[0-9]+)*", code),
                    "malformed native module monomial")
            numbers = list(map(int, code.split(",")))
            require(len(numbers) % 2 == 1, "native module monomial must end with a module generator")
            generator = numbers[-1]
            coefficient = lowstem.mon(",".join(map(str, numbers[:-1])))
            g = ceta.execute("SELECT * FROM Ceta_AdamsE2_generators WHERE id=?", (generator,)).fetchone()
            image = maps.execute("SELECT * FROM map_AdamsE2_Ceta_to_S0 WHERE id=?", (generator,)).fetchone()
            require(g is not None and image is not None, "missing native module generator or image")
            used_module_generators[generator], used_images[generator] = dict(g), dict(image)
            cs, ct = ring_degree(coefficient)
            require([cs + g["s"], ct + g["t"]] == source_degree, "source module monomial degree mismatch")
            require(isinstance(image["map"], str), "SQL NULL generator image is unknown, not zero")
            polynomial = lowstem.polynomial(image["map"]) if image["map"] else set()
            for term in polynomial:
                require(ring_degree(term) == (g["s"], g["t"] - mapping["sus"]),
                        "native generator image degree mismatch")
            value = {lowstem.mul(coefficient, term) for term in polynomial}
            require(all(term in target_indices for term in value),
                    "native map image requires an unsupported target-basis reduction")
            columns.append(sorted(target_indices[term] for term in value))
        result = set()
        for index in source_equation[side]["coordinates"]:
            require(index < len(columns), "source log coordinate outside native basis")
            result.symmetric_difference_update(columns[index])
        require(sorted(result) == target_equation[side]["coordinates"],
                "native map coordinates disagree with naturality target log")
        slices[side] = {
            "source_degree": source_degree, "target_degree": target_degree,
            "source_basis": source_basis, "target_basis": target_basis,
            "columns_as_target_coordinates": columns,
            "matrix_rows": [[int(j in column) for column in columns] for j in range(len(target_basis))],
            "source_log_coordinates": source_equation[side]["coordinates"],
            "mapped_coordinates": sorted(result),
        }
    outgoing = [dict(row) for row in ceta.execute(
        "SELECT * FROM Ceta_AdamsE2_ss WHERE s=? AND t=? AND base=? AND diff=? AND level=?",
        (source["s"], source["t"], source["x"], source["dx"], 10000 - source["r"]))]
    incoming = [dict(row) for row in ceta.execute(
        "SELECT * FROM Ceta_AdamsE2_ss WHERE s=? AND t=? AND base=? AND diff=? AND level=?",
        (source["s"] + source["r"], source["t"] + source["r"] - 1,
         source["dx"], source["x"], source["r"]))]
    require(len(outgoing) == len(incoming) == 1, "source log lacks reciprocal native staircase rows")
    return {
        "scope": "selected native data map only; no actual Adams map comparison or source differential proof",
        "schema": schemas, "source_database_version": source_version, "map_database_version": map_version,
        "module_generators": [used_module_generators[i] for i in sorted(used_module_generators)],
        "generator_images": [used_images[i] for i in sorted(used_images)],
        "coefficient_generators": [used_ring_generators[i] for i in sorted(used_ring_generators)],
        "degree_slices": slices, "source_staircase": {"outgoing": outgoing[0], "incoming": incoming[0]},
        "interpretation": "formal S0-linear extension of stored module-generator images; direct target monomial matches only",
        "proof_status": "unverified-data-extraction",
    }


def rebuild():
    lowstem = load_lowstem()
    config = pinned_map_catalogue(lowstem)
    paths, raw_bytes = {}, {}
    # Reuse the existing manifest and Git-worktree-aware LFS resolver.
    manifest = json.loads((LIN / "Raw/manifest.json").read_text())
    validate_ceta_archive_origin(manifest)
    for entry in manifest["files"]:
        paths[entry["path"]], data, _ = lowstem.pinned(entry["path"])
        if entry["path"].endswith(".csv"):
            raw_bytes[entry["path"]] = data
    relation_rows = list(csv.DictReader(io.StringIO(raw_bytes["S0_AdamsE2_relations.csv"].decode("utf-16"))))
    with tempfile.TemporaryDirectory(prefix="lin-native-contract-") as temporary:
        output = Path(temporary)
        run = subprocess.run([sys.executable, str(LIN / "Translate/replay-lowstem.py"),
                              "--row", "152098", "--certificate-only", "--output-dir", str(output)],
                             capture_output=True, text=True)
        require(run.returncode == 0, f"existing low-stem extractor failed: {run.stderr}")
        replay = json.loads((output / "benchmark.json").read_text())
        witness_hash = hashlib.sha256((output / "GeneratedProductWitnesses.lean").read_bytes()).hexdigest()
    require(replay["status"] == "polynomial-certificates-only" and
            replay["actual_row_proof_generated"] is False, "extractor crossed proof boundary")
    products = [validate_product_witness(c, relation_rows, lowstem) for c in replay["certificates"]]
    require(len(products) == 2, "expected the two row152098 auxiliary product witnesses")
    with connect(paths["proofs.db"]) as db, connect(paths["S0_AdamsSS_t261.db"]) as sphere:
        source, target, extra = [raw_row(db, i) for i in (245130, 245131, 462481)]
        check_raw_naturality_declarations((LIN / "Raw/Naturality.lean").read_text(), source, target)
        require(replay["target"] == raw_row(db, 152098) and replay["trial"] == raw_row(db, 152097),
                "low-stem extractor lost raw log payload")
        mapping = [m for m in config["maps"] if m["name"] == target["info"]]
        require(len(mapping) == 1, "missing or ambiguous native map declaration")
        mapping = mapping[0]
        validate_naturality(source, target, mapping)
        modules = [m for m in config["modules"] if m["name"] == mapping["from"]]
        require(len(modules) == 1, "missing or ambiguous native source module")
        selected = json.loads((LIN / "Generated/Selected/records.json").read_text())
        selected_extra = [r for r in selected["results"] if r["record"]["id"] == extra["id"]]
        require(len(selected_extra) == 1 and selected_extra[0]["record"] == extra,
                "selected row462481 payload differs from native log")
        extra_coordinates = sphere_coordinates(sphere, extra)
        require(extra_coordinates["source"] == selected_extra[0]["source_basis"] and
                extra_coordinates["target"] == selected_extra[0]["target_basis"],
                "selected row462481 coordinates differ from pinned sphere database")
        natural_coordinates = sphere_coordinates(sphere, target)
        with connect(paths["Ceta_AdamsSS_t200.db"]) as ceta, connect(paths["map_AdamsSS_Ceta_to_S0_t200.db"]) as maps:
            native_map_data = native_ceta_map_slice(ceta, maps, sphere, source, target, mapping, lowstem)
        extra_source = raw_row(db, 462480)
        trace_path = ROOT / "KIP126/LinProgram/Generated/Provenance/row462481-trace.json"
        trace_bytes = trace_path.read_bytes()
        # Reconstruct the entire context from authenticated inputs. Merely
        # rehashing a modified derived JSON would let a nonempty but incomplete
        # obligations list become the new baseline.
        with tempfile.TemporaryDirectory(prefix="lin-recovered-context-") as temporary:
            rebuilt_trace = Path(temporary) / "row462481-trace.json"
            run = subprocess.run([sys.executable, "-B",
                str(LIN / "Translate/extract-row462481-trace.py"),
                "--output", str(rebuilt_trace)], capture_output=True, text=True)
            require(run.returncode == 0, f"native context reconstruction failed: {run.stderr}")
            check_recovered_trace_snapshot(trace_bytes, rebuilt_trace.read_bytes())
        extra_trace = json.loads(trace_bytes)
        validate_recovered_trace(extra_trace, extra_source, extra, mapping)
        raw_high_stem = (LIN / "Raw/NaturalityHighStem.lean").read_text()
        cw_source = raw_row(db, 462479)
        check_raw_high_stem_declarations(raw_high_stem, cw_source, extra_source, extra)
        cw_maps = [m for m in config["maps"] if m["name"] == extra_source["info"]]
        require(len(cw_maps) == 1, "missing or ambiguous native CW map declaration")
        require(cw_maps[0]["sus"] == 4, "CW-to-Ceta contract requires shift four")
        require((cw_maps[0]["from"], cw_maps[0]["to"]) ==
                (cw_source["name"], extra_source["name"]), "CW map endpoints changed")
        require(cw_source["r"] == extra_source["r"] and
                cw_source["s"] == extra_source["s"] and
                cw_source["t"] - cw_maps[0]["sus"] == extra_source["t"],
                "CW map degrees changed")
        natural_lookup, extra_lookup = bulk_lookup(target), bulk_lookup(extra)
    archive_inputs = []
    for role, name in (("source_page_database", modules[0]["path"]), ("map_matrix_database", mapping["path"])):
        archive_inputs.append({"role": role, "path_named_by_ss_json": name,
                               "present_in_raw": (LIN / "Raw" / name).is_file(),
                               "pinned_by_raw_manifest": name in paths,
                               "selected_rows_extracted": True})
    return {
        "schema_version": 1,
        "kind": "rebuildable-native-target-and-witness-snapshot",
        "provenance": {"canonical_registry": "docs/external-inputs.json",
                       "pinned_inputs": "KIP126/LinProgram/Raw/manifest.json",
                       "checked_raw_inputs": list(paths),
                       "native_map_catalogue": "KIP126/LinProgram/Raw/ss.json"},
        "contract": {
            "raw_log_type": "KIP126.Computation.LinProofs.Raw.LogRow",
            "raw_columns": list(LOG_FIELDS), "coordinate_index_base": 0,
            "degrees": "s is Adams filtration; t is internal degree; stem=t-s; d_r:(s,t)->(s+r,t+r-1)",
            "sql_null": "unknown or absent, preserved as null",
            "empty_coordinate_string": "known zero vector",
            "minus_one_or_bracket_null": "unknown sentinel, never an empty vector",
            "finite_page_range": "2 <= r < 999; 999,1000,1001 are not finite differential pages",
            "target_policy": "native coordinates determine the statement; auxiliary witnesses do not change it",
            "generated_proof_status": "unverified",
            "actual_certification": False,
        },
        "algebra": {
            "target_log": replay["target"], "retained_trial_log": replay["trial"],
            "native_row_equation": equation(replay["target"]),
            "diagnostic_equations": replay["parsed_steps"],
            "data_algebra": "KIP126.LinE2.E2",
            "product_witnesses": products,
            "witness_declarations": ["Replay152098.productWitness0", "Replay152098.productWitness1"],
            "fixed_quotient_statement_declarations": [
                {"product_witness_index": 0,
                 "declaration": "KIP126.LinE2.ReplayProducts.native_source_product_zero"},
                {"product_witness_index": 1,
                 "declaration": "KIP126.LinE2.ReplayProducts.native_target_product"},
            ],
            "generated_lean_sha256": witness_hash,
            "status": "unverified-auxiliary-witnesses",
            "actual_row_certified": False,
            "remaining_actual_row_obligations": [
                "Prove the source coordinate [1] at S0 (4,42) reaches E4 through the same presentation.",
                "Prove the source multiplier [0] at S0 (1,2) reaches E4 and has d4=0.",
                "Construct actual E4 multiplication and prove the Leibniz equation on all required representatives.",
                "Prove exhaustive actual d4 candidates for the source, with the retained trial's complete context.",
                "Prove S0 (9,47) coordinate [0] is not in the actual B3 space, including certified earlier boundaries.",
            ],
        },
        "naturality": {
            "source_candidate_log": source, "target_log": target,
            "raw_transcription": "KIP126/LinProgram/Raw/Naturality.lean",
            "raw_declarations": {
                "source": "KIP126.Computation.LinProofs.Raw.Naturality.sourceCandidate245130",
                "target": "KIP126.Computation.LinProofs.Raw.Naturality.target245131",
                "output": "KIP126.Computation.LinProofs.Raw.Naturality.output245131",
            },
            "conditional_statement_declaration": "KIP126.Interface.Solution.LinProgram.Naturality.row245131_native",
            "general_conditional_statement_declaration": "KIP126.Interface.Solution.LinProgram.Naturality.row245131",
            "fixed_sphere_coordinate_declarations": [
                "KIP126.LinE2.NaturalityCoordinates.source",
                "KIP126.LinE2.NaturalityCoordinates.target",
                "KIP126.Interface.Solution.LinProgram.NaturalityCoordinates.source_hasCoordinates",
                "KIP126.Interface.Solution.LinProgram.NaturalityCoordinates.target_hasCoordinates",
            ],
            "constructed_top_cell_declaration": "KIP126.Interface.Solution.LinProgram.Naturality.topCell",
            "conditional_top_cell_naturality_declaration": "KIP126.Interface.Solution.LinProgram.Naturality.row245130_topCell",
            "generic_double_desuspension_declaration": "KIP126.Classical.Adams.Suspension.TowerComparison.hasDifferential_desuspendTwice",
            "fixed_double_desuspension_declaration": "KIP126.Interface.Solution.LinProgram.Naturality.doubleDesuspensionCompatible",
            "source_equation": equation(source), "target_equation": equation(target),
            "source_candidate_relation": "adjacent log only; an actual source-to-target trace still needs witnesses",
            "native_map": mapping, "native_source_module": modules[0],
            "sphere_coordinates": natural_coordinates, "bulk_lookup": natural_lookup,
            "status": "unverified-conditional-replay-target", "actual_row_certified": False,
            "archive_inputs": archive_inputs,
            "native_data_map": native_map_data,
            "missing_trace": [
                "The complete derivation of source log245130 is not replayed; reciprocal source staircase rows are recorded results.",
                "Stored module-generator images and the two raw coordinate matrices are not comparisons with the actual topCell and fixed tower desuspensions.",
            ],
            "remaining_premises": [
                "Identify KIP126.Interface.Solution.LinProgram.Naturality.CetaCoordinates at (2,19)[0] and (5,21)[0] with the now-pinned Ceta basis rows id69 and id80 in native_data_map; extracted records and a supplied coordinate function alone do not prove that actual identification.",
                "Prove KIP126.Interface.Solution.LinProgram.Naturality.SourceEquation coordinates: HasDifferential cetaSequence 3 (2,19) (5,21) (coordinates 2 19 0) (coordinates 5 21 0); the source D log alone is not a proof.",
                "Prove row245131 premise source_first: the existing shifted-sphere classicalSuspension desuspends the actual topCell image of coordinates 2 19 0 to x1 at (2,18).",
                "Prove row245131 premise target_first: that same shifted-sphere classicalSuspension desuspends the actual topCell image of coordinates 5 21 0 to y1 at (5,20).",
                "Prove row245131 premise source_second: the existing sphere classicalSuspension desuspends x1 at (2,18) to P.comparison 2 17 KIP126.LinE2.NaturalityCoordinates.source.",
                "Prove row245131 premise target_second: that same sphere classicalSuspension desuspends y1 at (5,20) to P.comparison 5 19 KIP126.LinE2.NaturalityCoordinates.target.",
            ],
        },
        "additional_missing_trace": {
            "target_log": extra, "native_equation": equation(extra),
            "selected_record_snapshot": "KIP126/LinProgram/Generated/Selected/records.json",
            "sphere_coordinates": extra_coordinates, "bulk_lookup": extra_lookup,
            "source_candidate_log": extra_source,
            "native_trace": {
                "path": str(trace_path.relative_to(ROOT)),
                "sha256": hashlib.sha256(trace_bytes).hexdigest(),
                "kind": "derived-native-context; not an independent source registry or mathematical proof",
                "replay": "python3 -B KIP126/LinProgram/Translate/extract-row462481-trace.py --check",
            },
            "status": "recovered-native-context-with-unproved-actual-source-and-comparisons",
            "actual_row_certified": False,
            "missing": "The native source N462480, complete local branch context and map-coordinate preimages are extracted. The actual Ceta source differential, actual top-cell coordinate comparisons and upstream CW branch interpretation remain unproved.",
            "remaining_premises": extra_trace["remaining_propositions"],
        },
        "replay_commands": [
            "python3 KIP126/LinProgram/Translate/native-contract.py --check",
            "python3 -B KIP126/LinProgram/Translate/extract-row462481-trace.py --check",
            "python3 KIP126/LinProgram/Translate/replay-lowstem.py --row 152098 --certificate-only --output-dir /tmp/lin-native-products",
            "lake env lean /tmp/lin-native-products/GeneratedProductWitnesses.lean",
        ],
    }


def rendered(snapshot):
    return json.dumps(snapshot, ensure_ascii=False, indent=2) + "\n"


def check_snapshot(actual, expected):
    require(actual == rendered(expected), "native contract snapshot differs; review native payload, witnesses, and remaining premises")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the committed snapshot without writing")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    snapshot = rebuild()
    if args.check:
        check_snapshot(args.output.read_text(), snapshot)
        print("Native contract snapshot matches pinned inputs and extracted witnesses; proof status remains unverified.")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered(snapshot))
        print(f"Wrote {args.output}; proof status remains unverified.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, sqlite3.Error) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        raise SystemExit(2)
