#!/usr/bin/env python3
"""Import selected v126.3.cw49 results, NOT their machine proofs.

Read-only SQLite access; no network, dependency updates, or database writes.
Selection is editorial (paper section 7); all coordinates and monomials come
from the pinned databases. Unknown/trial/inverse rows fail closed.
Adapted from KIPBase/SphereAdamsProofs.generate.py at 639057b.
Reuses the existing bulk table axiom; does not introduce per-row axioms.
"""
import argparse
import csv
import hashlib
import json
from collections import defaultdict
from pathlib import Path
import re
import sqlite3

HASHES = {
    "proofs.db": "3a460683c023ee2d8f7e8f904ecef9044a474d88bb7184731e54978ba7dac248",
    "S0_AdamsSS_t261.db": "518a2ed86af6d4f7bcdc5db135ab6252bd50df34492ae208663aa1c140a820ed",
    "S0_AdamsE2_generators.csv": "3c4e45a1e28837e651e729bee14e7c62a99f797bc650d69e8a79aec13a762c72",
    "S0_AdamsE2_relations.csv": "8b4b67d6fb3c9a3a264813ea780340e73b1a66290c8616d3308ae1fc19f3add5",
    "S0_AdamsE2_basis.csv": "6a337964ad3ac02b729a46fd839dced7cb6764d14d4cea413163987eba8de871",
}
# These select records, not their computed answers. No row count is inferred
# from the team's informal "eight": one of those eight is a Cnu result.
SELECTION = [
    (5990, "d2_x_125_8", "Fact 7.13(2)"),
    (5541, "d2_h6", "Lemma 7.16, classical Toda bracket argument"),
    (153768, "d3_h4_x_109_12", "Lemma 7.14(1)"),
    (462481, "d3_h0Sq_x_123_13_2", "Lemma 7.14(2)"),
    (929469, "d3_x_126_4", "Lemma 7.16"),
    (2671068, "d7_x_123_11_combination", "Lemma 7.14(2)"),
]
LOG_SCHEMA = ("CREATE TABLE log (id INTEGER PRIMARY KEY, depth TINYINT, reason TEXT, "
              "name TEXT, stem SMALLINT as (t-s), s SMALLINT, t SMALLINT, r SMALLINT, "
              "x TEXT, dx TEXT, info TEXT)")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pinned(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    actual = digest.hexdigest()
    require(actual == HASHES[path.name], f"SHA-256 mismatch: {path}")


def connect(path):
    db = sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True)
    db.row_factory = sqlite3.Row
    db.execute("PRAGMA query_only=ON")
    return db


def indices(text):
    require(isinstance(text, str), "NULL means unknown, not zero")
    if text == "":
        return []
    require(re.fullmatch(r"[0-9]+(?:,[0-9]+)*", text), "invalid coordinate encoding")
    result = list(map(int, text.split(",")))
    require(result == sorted(set(result)), "noncanonical coordinate vector")
    return result


def accepted_log(row):
    require(row["name"] == "S0", "not a sphere Adams record")
    # A deliberately small forward-reason allowlist; extending it requires
    # checking the upstream logging semantics, especially inverse rows.
    require(row["depth"] == 0 and row["reason"] in {"d2", "D", "N"},
            "not an accepted forward conclusion (trial/hint/inverse/unsupported)")
    require(2 <= row["r"] < 999, "not an ordinary finite-page differential")
    require(row["stem"] == row["t"] - row["s"], "inconsistent degree")
    require(indices(row["x"]) and indices(row["dx"]), "expected known nonzero vectors")


def monomial(text, generators):
    if not text:
        return []
    require(re.fullmatch(r"[0-9]+(?:,[0-9]+)*", text), "invalid monomial")
    ns = list(map(int, text.split(",")))
    require(len(ns) % 2 == 0, "odd monomial encoding")
    pairs = list(zip(ns[::2], ns[1::2]))
    require([i for i, _ in pairs] == sorted(set(i for i, _ in pairs)), "monomial order")
    require(all(i in generators and e > 0 for i, e in pairs), "invalid generator/power")
    return pairs


def import_rows(proofs, sphere, csv_dir, include_table):
    require(proofs.execute("SELECT sql FROM sqlite_master WHERE name='log'").fetchone()[0]
            == LOG_SCHEMA, "unexpected proofs.db schema")
    csv_rows = {}
    for kind in ("generators", "relations", "basis"):
        with (csv_dir / f"S0_AdamsE2_{kind}.csv").open(encoding="utf-16", newline="") as f:
            csv_rows[kind] = list(csv.DictReader(f))
    gens = {r["id"]: dict(r) for r in sphere.execute("SELECT * FROM S0_AdamsE2_generators ORDER BY id")}
    require([(r["id"], r["name"], r["s"], r["t"]) for r in gens.values()] ==
            [(int(r["id"]), r["name"], int(r["s"]), int(r["stem"]) + int(r["s"]))
             for r in csv_rows["generators"]], "database/CSV generator mismatch")
    rels = sphere.execute("SELECT rel,s,t FROM S0_AdamsE2_relations ORDER BY rowid").fetchall()
    require([tuple(r) for r in rels] ==
            [(r["rel"], int(r["s"]), int(r["stem"]) + int(r["s"])) for r in csv_rows["relations"]],
            "database/CSV relations mismatch")
    basis = defaultdict(list)
    db_basis = []
    for row in sphere.execute("SELECT * FROM S0_AdamsE2_basis ORDER BY id"):
        row = dict(row)
        key = (row["s"], row["t"])
        # Upstream utility.cpp exports index = id - min(id) at this degree.
        j = len(basis[key])
        require(not j or row["id"] == basis[key][0]["id"] + j, "noncontiguous local basis")
        row["local_index"] = j
        pairs = monomial(row["mon"], gens)
        require(tuple(sum(gens[i][k] * e for i, e in pairs) for k in ("s", "t")) == key,
                "basis monomial degree mismatch")
        basis[key].append(row)
        db_basis.append((j, row["mon"], *key, row["d2"]))
    require(db_basis == [(int(r["index"]), r["mon"], int(r["s"]),
                         int(r["stem"]) + int(r["s"]),
                         None if r["d2"] == "[NULL]" else r["d2"]) for r in csv_rows["basis"]],
            "database/CSV local basis or d2 mismatch")

    def decorate(row, name, paper, origin):
        s, t, r = row["s"], row["t"], row["r"]
        sx, tx = s + r, t + r - 1
        xs, ys = indices(row["x"]), indices(row["dx"])
        require(xs and ys and tx <= 261, "empty/out-of-range selected result")
        def resolve(key, coords):
            require(all(i < len(basis[key]) for i in coords), "unknown local basis index")
            return [basis[key][i] for i in coords]
        source, target = resolve((s, t), xs), resolve((sx, tx), ys)
        outgoing = [dict(z) for z in sphere.execute(
            "SELECT * FROM S0_AdamsE2_ss WHERE s=? AND t=? AND base=? AND diff=? AND level=?",
            (s, t, row["x"], row["dx"], 10000 - r))]
        incoming = [dict(z) for z in sphere.execute(
            "SELECT * FROM S0_AdamsE2_ss WHERE s=? AND t=? AND base=? AND diff=? AND level=?",
            (sx, tx, row["dx"], row["x"], r))]
        require(len(outgoing) == len(incoming) == 1, "missing/ambiguous reciprocal SS result")
        if r == 2:
            total = set()
            for x in source:
                total.symmetric_difference_update(indices(x["d2"]))
            require(sorted(total) == ys, "d2 column disagrees with selected result")
        return dict(name=name, paper=paper, origin=origin, record=row,
                    source_basis=source, target_basis=target,
                    outgoing_ss=outgoing[0], incoming_ss=incoming[0],
                    source_degree=[s, t], target_degree=[sx, tx])

    results = []
    for row_id, name, paper in SELECTION:
        row = proofs.execute("SELECT * FROM log WHERE id=?", (row_id,)).fetchone()
        require(row is not None, f"missing log.id={row_id}")
        row = dict(row)
        accepted_log(row)
        results.append(decorate(row, name, paper, "proofs.db/log"))
    if include_table:
        # This is explicitly NOT a proofs.db log record. Its answer is read
        # from the d2 column, and checked against both final SS rows.
        b = sphere.execute("SELECT * FROM S0_AdamsE2_basis WHERE id=513").fetchone()
        require(b is not None, "missing selected basis row")
        b = dict(b)
        local = b["id"] - basis[(b["s"], b["t"])][0]["id"]
        row = dict(id=b["id"], name="S0", s=b["s"], t=b["t"], r=2,
                   stem=b["t"]-b["s"], x=str(local), dx=b["d2"], reason="basis.d2")
        results.append(decorate(row, "d2_h0Pow6_h6", "Lemma 7.16, classical Toda bracket argument",
                                "S0_AdamsSS_t261.db/S0_AdamsE2_basis"))
    return gens, results


def generate(gens, results, root):
    """Join selected DB rows to the existing bulk shards; never guess offsets."""
    locations = {}
    for path in sorted((root / "KIP126/LinProgram/Generated/Differentials").glob("Shard*.lean")):
        shard = int(path.stem[5:])
        rows = re.findall(r'⟨(\d+), "([^"]+)", (\d+), (\d+), (\d+), (\[[^\]]*\]), (\[[^\]]*\])⟩', path.read_text())
        for offset, (rid, reason, s, t, r, x, dx) in enumerate(rows):
            require(int(rid) not in locations, "duplicate bulk log id")
            locations[int(rid)] = (shard, offset, dict(id=int(rid), reason=reason,
                s=int(s), t=int(t), r=int(r), x=json.loads(x), dx=json.loads(dx)))
    lines = ["import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differentials.Proofs", "",
        "/-! Generated by KIP126/LinProgram/Translate/import-selected.py. Six selected sphere log results",
        "on the existing fixed Adams object. These theorems use sphereTable_sound;",
        "they neither replay the computations nor assert later-page nonvanishing.",
        "Coordinates, monomials, reciprocal SS records and hashes:",
        "KIP126/LinProgram/Generated/Selected/records.json.",
        "The separate basis.d2 record 513 is metadata only; its stronger paper",
        "statement remains SphereDifferentialFacts.d2_h0Six_h6. -/", "",
        "namespace KIP126.Computation.LinProofs.Selected", "",
        "set_option maxRecDepth 4096", ""]
    for entry in results:
        row = entry["record"]
        if entry["origin"] != "proofs.db/log":
            entry["bulk_lookup"] = None
            continue
        expected = {k: row[k] for k in ("id", "reason", "s", "t", "r")}
        expected.update(x=indices(row["x"]), dx=indices(row["dx"]))
        require(row["id"] in locations, "selected result absent from bulk export")
        shard, offset, actual = locations[row["id"]]
        require(actual == expected, "selected result disagrees with bulk export")
        entry["bulk_lookup"] = dict(shard=shard, offset=offset)
        literal = f'⟨{row["id"]}, "{row["reason"]}", {row["s"]}, {row["t"]}, {row["r"]}, {expected["x"]}, {expected["dx"]}⟩'
        lines += [f'/-- {entry["paper"]}; proofs.db/log.id={row["id"]}.',
            f'CSV (s,t,index): {entry["source_degree"]} {expected["x"]} → {entry["target_degree"]} {expected["dx"]}. -/',
            f'theorem {entry["name"]} : DifferentialStatement {literal} :=',
            f'  differential_of_lookup {shard} {offset} _ (by rfl)', ""]
    lines += ["end KIP126.Computation.LinProofs.Selected", ""]
    return {"Proofs.lean": "\n".join(lines), "records.json": json.dumps(dict(
        dataset="Zenodo 14875701 / v126.3.cw49", sha256=HASHES,
        trust="Results only, not proof replay. Six equalities use the existing sphereTable_sound. "
              "Nonzero later-page targets and the seventh table-only result are not derived.",
        results=results), ensure_ascii=False, indent=2) + "\n"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proofs-db", type=Path, required=True)
    parser.add_argument("--sphere-db", type=Path, required=True)
    parser.add_argument("--csv-dir", type=Path, required=True)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for path in [args.proofs_db, args.sphere_db] + [args.csv_dir / f"S0_AdamsE2_{kind}.csv"
            for kind in ("generators", "relations", "basis")]:
        pinned(path)
    proofs, sphere = connect(args.proofs_db), connect(args.sphere_db)
    try:
        gens, results = import_rows(proofs, sphere, args.csv_dir, True)
    finally:
        proofs.close()
        sphere.close()
    outputs = {
        "Proofs.lean": args.root /
            "KIP126/Main/Solution/Computation/LinProgram/Interpretation/Selected/Proofs.lean",
        "records.json": args.root / "KIP126/LinProgram/Generated/Selected/records.json",
    }
    for name, content in generate(gens, results, args.root).items():
        path = outputs[name]
        if args.check:
            require(path.read_text() == content, f"stale generated file: {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("Validated six bulk log results and one separate basis.d2 result against reciprocal SS records.")


if __name__ == "__main__":
    main()
