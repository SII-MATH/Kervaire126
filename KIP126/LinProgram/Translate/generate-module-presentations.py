#!/usr/bin/env python3
"""Reproduce complete native Ceta and CW_nu_eta module presentations.

Read-only pinned SQLite/RAR inputs; explicit output directory or --check.
Every original module generator and relation is retained. The recorded t_max
is metadata, never an instruction to impose additional zero relations.
The coefficient algebra is the existing KIP126.LinE2.E2. No actual Ext,
cofiber, page, basis, module-map or differential comparison is asserted.
"""
import argparse
import csv
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
import subprocess

import sys as _module_sys
from pathlib import Path as _ModulePath
_module_sys.path.insert(0, str(_ModulePath(__file__).resolve().parent))
from lean_module import lean_module, module_output

CHUNK_SIZE = 512
GENERATOR_CHUNK_SIZE = 64
OBJECTS = (("Ceta", "Ceta", 887, 76569), ("CW_nu_eta", "CWNuEta", 844, 69263))
GENERATOR_FIELDS = ("id", "name", "repr", "s", "t", "cell", "cell_coeff")
RELATION_FIELDS = ("sqlite_rowid", "rel", "s", "t")
VERSION_SCHEMA = "CREATE TABLE version (id INTEGER PRIMARY KEY, name TEXT, value)"
DATA_LEAN = '''/-! Lossless native module catalogue records. These are finite data,
not actual Ext modules or assertions that unrecorded degrees vanish. -/
namespace KIP126.LinModule.RawData

structure GeneratorRow where
  id : Nat
  name : Option String
  repr : Nat
  s : Nat
  t : Nat
  cell : Option Nat
  cellCoeff : Option String
  deriving Repr, DecidableEq, Inhabited

structure RelationRow where
  sqliteRowid : Nat
  code : String
  s : Nat
  t : Nat
  deriving Repr, DecidableEq, Inhabited

end KIP126.LinModule.RawData
'''


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("utf-8")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(root, name, filename):
    path = root / "KIP126/LinProgram/Translate" / filename
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def schema(db, table, expected):
    row = db.execute("SELECT sql FROM sqlite_master WHERE name=? AND type='table'", (table,)).fetchone()
    require(row is not None and row[0] == expected, f"native schema changed: {table}")
    return expected


def module_schemas(db, name):
    result = {"version": schema(db, "version", VERSION_SCHEMA)}
    table = name + "_AdamsE2_generators"
    result[table] = schema(db, table, f"CREATE TABLE {table} (id INTEGER PRIMARY KEY, name TEXT UNIQUE, repr SMALLINT, s SMALLINT, t SMALLINT, cell SMALLINT, cell_coeff TEXT)")
    table = name + "_AdamsE2_relations"
    result[table] = schema(db, table, f"CREATE TABLE {table} (rel TEXT, s SMALLINT, t SMALLINT)")
    return result


def nat(value):
    return type(value) is int and value >= 0


def validate_module(name, generators, relations, version, ring):
    _, _, expected_generators, expected_relations = next(x for x in OBJECTS if x[0] == name)
    require(len(generators) == expected_generators and len(relations) == expected_relations,
            name + ": complete generator/relation count changed")
    require(all(tuple(r) == GENERATOR_FIELDS for r in generators), name + ": generator field contract changed")
    require(all(tuple(r) == RELATION_FIELDS for r in relations), name + ": relation field contract changed")
    require([r["id"] for r in generators] == list(range(len(generators))), name + ": generator IDs/order changed")
    require([r["sqlite_rowid"] for r in relations] == list(range(1, len(relations)+1)), name + ": relation rowids/order changed")
    require(all(tuple(r) == ("id", "name", "value") for r in version), name + ": version fields changed")
    metadata = {r["name"]: r["value"] for r in version}
    require(len(metadata) == len(version), name + ": duplicate version metadata")
    require(metadata.get("version") == 3 and metadata.get("t_max") == 200, name + ": native version or range changed")
    require(nat(metadata.get("d2_t_max")) and metadata["d2_t_max"] <= metadata["t_max"], name + ": invalid d2 range")
    for row in generators:
        require(all(nat(row[k]) for k in ("id", "repr", "s", "t")), name + ": invalid generator number")
        require(row["t"] <= metadata["t_max"], name + ": generator outside native range")
        require(row["name"] is None or isinstance(row["name"], str), name + ": invalid optional name")
        require(row["cell"] is None or nat(row["cell"]), name + ": invalid optional cell")
        require(row["cell_coeff"] is None or isinstance(row["cell_coeff"], str), name + ": invalid optional cell coefficient")
    for row in relations:
        require(nat(row["s"]) and nat(row["t"]) and row["t"] <= metadata["t_max"], name + ": invalid relation degree")
        code = row["rel"]
        require(isinstance(code, str) and bool(code), name + ": missing/empty relation is not zero")
        for term in code.split(";"):
            require(re.fullmatch(r"(?:0|[1-9][0-9]*)(?:,(?:0|[1-9][0-9]*))*", term), name + ": malformed module monomial")
            values = list(map(int, term.split(",")))
            require(len(values) % 2 == 1, name + ": module monomial lacks final generator")
            g = values[-1]
            pairs = list(zip(values[:-1:2], values[1:-1:2]))
            require(g < len(generators), name + ": module generator outside complete range")
            require(all(i in ring and e > 0 for i, e in pairs), name + ": invalid sphere generator/exponent")
            require([i for i, _ in pairs] == sorted(set(i for i, _ in pairs)), name + ": unordered/repeated coefficient generator")
            degree = tuple(generators[g][k] + sum(ring[i][k]*e for i, e in pairs) for k in ("s", "t"))
            require(degree == (row["s"], row["t"]), name + ": relation is not homogeneous in the original S0 degrees")
    return metadata


def read_inputs(root, archive):
    native = load(root, "module_native_contract", "native-contract.py")
    branch = load(root, "module_branch_source", "check-branch-d2-coordinates.py")
    low = native.load_lowstem()
    cw_bytes, archive_metadata = branch.checked_archive(root, archive)
    raw = {}; paths = {}; entities = []
    for name in ("S0_AdamsSS_t261.db", "Ceta_AdamsSS_t200.db", "CW_nu_eta_AdamsSS_t200.db", "ss.json",
                 "S0_AdamsE2_generators.csv", "S0_AdamsE2_relations.csv"):
        path, content, digest = low.pinned(name)
        paths[name] = path; raw[name] = content
        entities.append({"path": "KIP126/LinProgram/Raw/"+name,
                         "size": len(content), "sha256": digest})
    # Compare with the same authenticated archive, not an independently selected
    # module/ring release. Only transient extraction occurs outside the repo.
    for name in ("S0_AdamsSS_t261.db", "Ceta_AdamsSS_t200.db", "ss.json"):
        content = subprocess.check_output(["unrar", "p", "-inul", str(archive), "kervaire-49/"+name])
        require(content == raw[name], "same-archive/pinned entity mismatch: "+name)
    require(raw["CW_nu_eta_AdamsSS_t200.db"] == cw_bytes, "same-archive/pinned entity mismatch: CW_nu_eta_AdamsSS_t200.db")
    catalogue = json.loads(raw["ss.json"])
    provenance = {
        "canonical_manifest": "docs/external-inputs.json",
        "raw_manifest": "KIP126/LinProgram/Raw/manifest.json",
        "source_id": "lwx_machine", "release": "v126.3.cw49",
        "archive": {"path": branch.ARCHIVE, "record": "Source/LWXMachine/zenodo-record.json", **archive_metadata},
        "pinned_entities": entities,
        "archived_module_entities": [
            {"member": "kervaire-49/Ceta_AdamsSS_t200.db", "size": len(raw["Ceta_AdamsSS_t200.db"]), "sha256": sha(raw["Ceta_AdamsSS_t200.db"])},
            {"member": branch.MEMBER, "size": len(cw_bytes), "sha256": sha(cw_bytes)}],
        "coefficient_algebra": "KIP126.LinE2.E2",
        "scope": "Complete archived module generator/relation tables over the existing sphere algebra; native t_max is metadata only. No additional high-degree zero relations, actual Ext comparison, or actual map/differential claim."}
    with native.connect(paths["S0_AdamsSS_t261.db"]) as sphere:
        schema(sphere, "S0_AdamsE2_generators", "CREATE TABLE S0_AdamsE2_generators (id INTEGER PRIMARY KEY, name TEXT UNIQUE, repr SMALLINT, s SMALLINT, t SMALLINT)")
        schema(sphere, "S0_AdamsE2_relations", "CREATE TABLE S0_AdamsE2_relations (rel TEXT, s SMALLINT, t SMALLINT)")
        ring = {r["id"]: dict(r) for r in sphere.execute("SELECT * FROM S0_AdamsE2_generators ORDER BY id")}
        require(list(ring) == list(range(2914)), "existing complete S0 generator family changed")
        for kind in ("generators", "relations"):
            rows = list(csv.DictReader(io.StringIO(raw["S0_AdamsE2_"+kind+".csv"].decode("utf-16"))))
            if kind == "generators":
                actual = [tuple(r) for r in sphere.execute("SELECT id,name,s,t FROM S0_AdamsE2_generators ORDER BY id")]
                expected = [(int(r["id"]), r["name"], int(r["s"]), int(r["s"])+int(r["stem"])) for r in rows]
            else:
                actual = [tuple(r) for r in sphere.execute("SELECT rel,s,t FROM S0_AdamsE2_relations ORDER BY rowid")]
                expected = [(r["rel"], int(r["s"]), int(r["s"])+int(r["stem"])) for r in rows]
            require(actual == expected, "complete existing S0 CSV/database mismatch: "+kind)
    results = []
    for name, lean_name, _, _ in OBJECTS:
        path = paths[name+"_AdamsSS_t200.db"]
        with native.connect(path) as db:
            schemas = module_schemas(db, name)
            generators = [dict(r) for r in db.execute(f"SELECT * FROM {name}_AdamsE2_generators ORDER BY id")]
            relations = [dict(r) for r in db.execute(f"SELECT rowid AS sqlite_rowid,* FROM {name}_AdamsE2_relations ORDER BY rowid")]
            version = [dict(r) for r in db.execute("SELECT * FROM version ORDER BY id")]
        metadata = validate_module(name, generators, relations, version, ring)
        objects = [o for o in catalogue["modules"] if o["name"] == name]
        require(len(objects) == 1 and objects[0]["over"] == "S0" and objects[0]["path"] == name+"_AdamsSS_t200.db", "native module/coefficient catalogue changed")
        results.append({"schema": "lin-native-complete-module-presentation/v1",
            "object": name, "lean_module_name": lean_name, "native_catalogue": objects[0],
            "native_schemas": schemas, "native_version": version, "t_max": metadata["t_max"],
            "d2_t_max": metadata["d2_t_max"], "generator_count": len(generators),
            "relation_count": len(relations), "generators": generators, "relations": relations,
            "provenance": provenance})
    return results


def q(value):
    return json.dumps(value, ensure_ascii=False)


def opt(value):
    return "none" if value is None else "some " + (q(value) if isinstance(value, str) else str(value))


def chunks(values, size):
    return [values[i:i+size] for i in range(0, len(values), size)]


@module_output
def render_lean(module):
    name = module["lean_module_name"]
    lines = ["import KIP126.LinProgram.Generated.Modules.Data", "",
        "/-! Complete fixed v126.3.cw49 native module data. Reproduce with",
        "Translate/generate-module-presentations.py. Original order and NULL metadata",
        "are retained. tMax is a recorded input limit, not a zero-relation rule.",
        "This catalogue supplies no actual Ext, map, or differential comparison. -/",
        f"namespace KIP126.LinModule.RawData.{name}", "",
        f"def generatorCount : Nat := {module['generator_count']}",
        f"def relationCount : Nat := {module['relation_count']}",
        f"def tMax : Nat := {module['t_max']}",
        f"def d2TMax : Nat := {module['d2_t_max']}",
        f"def generatorChunkSize : Nat := {GENERATOR_CHUNK_SIZE}",
        f"def relationChunkSize : Nat := {CHUNK_SIZE}", ""]
    gc = chunks(module["generators"], GENERATOR_CHUNK_SIZE)
    for i, values in enumerate(gc):
        rows = [f"⟨{r['id']}, {opt(r['name'])}, {r['repr']}, {r['s']}, {r['t']}, {opt(r['cell'])}, {opt(r['cell_coeff'])}⟩" for r in values]
        lines += [f"def generatorChunk{i} : Array GeneratorRow := #[", "  "+",\n  ".join(rows)+"]", ""]
    lines += ["def generatorChunks : Array (Array GeneratorRow) :=", "  #["+", ".join(f"generatorChunk{i}" for i in range(len(gc)))+"]", "",
        "def generatorRow (i : Nat) : Option GeneratorRow := do",
        "  let chunk ← generatorChunks[i / generatorChunkSize]?",
        "  chunk[i % generatorChunkSize]?", "",
        "def generatorRows : List GeneratorRow :=",
        "  generatorChunks.toList.flatMap Array.toList", ""]
    rc = chunks(module["relations"], CHUNK_SIZE)
    for i, values in enumerate(rc):
        lines += [f"def relationChunk{i} : List String :=", "  ["+",\n   ".join(q(r["rel"]) for r in values)+"]", "",
            f"def relationDegreeChunk{i} : Array (Nat × Nat) :=", "  #["+", ".join(f"({r['s']}, {r['t']})" for r in values)+"]", ""]
    lines += ["def relationChunks : Array (List String) :=", "  #["+", ".join(f"relationChunk{i}" for i in range(len(rc)))+"]", "",
        "def relationDegreeChunks : Array (Array (Nat × Nat)) :=", "  #["+", ".join(f"relationDegreeChunk{i}" for i in range(len(rc)))+"]", "",
        "/-- All original relation strings, without extra empty or truncation relations. -/",
        "def relations : List String := relationChunks.toList.flatten", "",
        "def relationCodeRow (i : Nat) : Option String := do",
        "  let chunk ← relationChunks[i / relationChunkSize]?",
        "  chunk[i % relationChunkSize]?", "",
        "/-- Zero-based lookup retaining the original one-based SQLite rowid. -/",
        "def relationRow (i : Nat) : Option RelationRow := do",
        "  let code ← relationCodeRow i",
        "  let chunk ← relationDegreeChunks[i / relationChunkSize]?",
        "  let degree ← chunk[i % relationChunkSize]?",
        "  pure ⟨i + 1, code, degree.1, degree.2⟩", "",
        f"end KIP126.LinModule.RawData.{name}", ""]
    return "\n".join(lines).encode("utf-8")


def build_outputs(modules):
    outputs = {"Data.lean": lean_module(DATA_LEAN).encode("utf-8")}
    for module in modules:
        name = module["lean_module_name"]
        outputs[name+".json"] = canonical(module)
        outputs[name+".lean"] = render_lean(module)
    manifest = {"schema": "lin-native-complete-module-export/v1",
        "generator": "KIP126/LinProgram/Translate/generate-module-presentations.py",
        "source_manifest": "docs/external-inputs.json", "source_id": "lwx_machine",
        "scope": "Complete fixed algebra input only; no actual mathematical certification.",
        "outputs": [{"path": "KIP126/LinProgram/Generated/Modules/"+path, "size": len(data), "sha256": sha(data)} for path, data in sorted(outputs.items())],
        "objects": [{"native_name": m["object"], "lean_namespace": "KIP126.LinModule.RawData."+m["lean_module_name"],
                     "generator_count": m["generator_count"], "relation_count": m["relation_count"],
                     "t_max": m["t_max"], "adds_high_degree_zero_relations": False,
                     "generator_rows_sha256": sha(canonical(m["generators"])),
                     "relation_rows_sha256": sha(canonical(m["relations"]))} for m in modules]}
    outputs["manifest.json"] = canonical(manifest)
    return outputs


def check_outputs(output_dir, outputs):
    for name, expected in outputs.items():
        path = output_dir/name
        require(path.is_file() and path.read_bytes() == expected,
                "generated module output differs from complete authenticated reconstruction: "+str(path))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--archive", type=Path, help="local copy of the SAME fixed RAR")
    parser.add_argument("--output-dir", type=Path, help="explicit generation or check directory")
    parser.add_argument("--check", action="store_true", help="read-only byte-exact regeneration check")
    args = parser.parse_args(); root = args.root.resolve()
    require(args.check or args.output_dir is not None, "generation requires explicit --output-dir")
    output_dir = args.output_dir or root/"KIP126/LinProgram/Generated/Modules"
    archive = args.archive or root/"Source/LWXMachine/kervaire_database.rar"
    modules = read_inputs(root, archive)
    outputs = build_outputs(modules)
    if args.check:
        check_outputs(output_dir, outputs)
    else:
        output_dir.mkdir(parents=True, exist_ok=True)
        for name, content in outputs.items():
            (output_dir/name).write_bytes(content)
    print(("Verified" if args.check else "Generated")+" complete Ceta 887/76569 and CW_nu_eta 844/69263 module catalogues.")
    print("Same fixed sphere coefficient algebra; no added truncation relations or actual-model certification.")
    for name, content in sorted(outputs.items()):
        print(f"{name}: {len(content)} bytes; sha256={sha(content)}")


if __name__ == "__main__":
    main()
