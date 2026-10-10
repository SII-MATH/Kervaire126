#!/usr/bin/env python3
"""Stream ALL rows of the pinned proofs.db; export a conservative typed fragment.

No row is silently dropped: the manifest counts each disposition. --raw-output
optionally retains every original column as JSONL (including nulls and info).
Lean shards currently interpret closed S0 finite-page differential equalities.
They do NOT interpret speculative branches, permanence sentinels, extensions,
unknown values, or non-sphere objects. Generation is mechanical, not a proof.
"""
import argparse
from collections import Counter
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import sqlite3
import subprocess
import tempfile
import unittest

DB_SHA256 = "3a460683c023ee2d8f7e8f904ecef9044a474d88bb7184731e54978ba7dac248"
BASIS_SHA256 = "6a337964ad3ac02b729a46fd839dced7cb6764d14d4cea413163987eba8de871"
FORWARD = {"d2", "D", "N", "G", "XX", "XY", "Syn"}
INVERSE = {"DI", "GI"}
COLUMNS = ("id", "depth", "reason", "name", "stem", "s", "t", "r", "x", "dx", "info")
SHARD_SIZE = 128
NAMESPACE = "KIP126.Computation.LinProofs"
DATA_MODULE = "KIP126.LinProgram.Interpretation.Differentials.Data"
GENERATED_MODULE = "KIP126.LinProgram.Generated.Differentials"


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def coordinates(value):
    if value is None or value == "[NULL]":
        return None
    if value == "":
        return []
    if not re.fullmatch(r"[0-9]+(,[0-9]+)*", value):
        raise ValueError(f"invalid coordinate encoding: {value!r}")
    values = list(map(int, value.split(",")))
    if values != sorted(set(values)):
        raise ValueError(f"noncanonical F2 coordinates: {value!r}")
    return values


def classify(row):
    if row["depth"] != 0:
        return "branch-not-unconditional", None
    if row["name"] != "S0":
        return "other-spectrum-or-extension", None
    if row["reason"] not in FORWARD | INVERSE:
        return "unsupported-reason", None
    r = row["r"]
    if r is None or not 2 <= r < 999:
        return "sentinel-or-unsupported-page", None
    x, dx = coordinates(row["x"]), coordinates(row["dx"])
    if x is None or dx is None:
        return "unknown-value", None
    s, t = row["s"], row["t"]
    if row["reason"] in INVERSE:
        s, t = s - r, t - r + 1
    if not (0 <= s and 0 <= t and t + r - 1 <= 261):
        return "outside-fixed-E2-range", None
    return "exported-sphere-differential", dict(
        id=row["id"], reason=row["reason"], s=s, t=t, r=r, x=x, dx=dx)


def read_basis(archive=None, *, basis_csv=None):
    if basis_csv is not None:
        data = basis_csv.read_bytes()
    else:
        data = subprocess.run(["unrar", "p", "-inul", str(archive),
                               "kervaire_csv/S0_AdamsE2_basis.csv"],
                              check=True, stdout=subprocess.PIPE).stdout
    if hashlib.sha256(data).hexdigest() != BASIS_SHA256:
        raise ValueError("basis CSV does not match the existing LinE2.RawData")
    result = set()
    for row in csv.DictReader(io.StringIO(data.decode("utf-16"))):
        s = int(row["s"])
        key = (s, int(row["stem"]) + s, int(row["index"]))
        if key in result:
            raise ValueError(f"duplicate basis address {key}")
        result.add(key)
    return result


def lean_row(row):
    nums = lambda xs: "[" + ", ".join(map(str, xs)) + "]"
    return (f'  ⟨{row["id"]}, {json.dumps(row["reason"])}, '
            f'{row["s"]}, {row["t"]}, {row["r"]}, '
            f'{nums(row["x"])}, {nums(row["dx"])}⟩')


def export(db, archive, output, raw_output=None, check=False, query_ids=(), *,
           basis_csv=None):
    if digest(db) != DB_SHA256:
        raise ValueError("proofs.db SHA-256 mismatch; review a new version explicitly")
    basis = read_basis(archive, basis_csv=basis_csv)
    # mode=ro prevents accidental creation or modification of the source database.
    con = sqlite3.connect(db.resolve().as_uri() + "?mode=ro", uri=True)
    if [r[1] for r in con.execute("pragma table_xinfo(log)")] != list(COLUMNS):
        raise ValueError("unexpected proofs.db schema")
    dispositions, reasons = Counter(), Counter()
    selected, total, first_id, last_id = [], 0, None, None
    raw = raw_output.open("x", encoding="utf-8") if raw_output else None
    try:
        for values in con.execute("select " + ",".join(COLUMNS) + " from log order by id"):
            row = dict(zip(COLUMNS, values))
            total += 1
            first_id = row["id"] if first_id is None else first_id
            if last_id is not None and row["id"] <= last_id:
                raise ValueError("non-increasing row IDs")
            last_id = row["id"]
            if row["stem"] is not None and row["stem"] != row["t"] - row["s"]:
                raise ValueError(f"inconsistent degree at row {last_id}")
            if raw:
                raw.write(json.dumps(row, ensure_ascii=False) + "\n")
            reasons[str(row["reason"])] += 1
            disposition, item = classify(row)
            dispositions[disposition] += 1
            if item is not None:
                for indices, s, t in [(item["x"], item["s"], item["t"]),
                                      (item["dx"], item["s"] + item["r"],
                                       item["t"] + item["r"] - 1)]:
                    for index in indices:
                        if (s, t, index) not in basis:
                            raise ValueError(f"row {last_id}: missing basis address {(s,t,index)}")
                selected.append(item)
    finally:
        con.close()
        if raw:
            raw.close()
    files = {}
    chunks = [selected[i:i + SHARD_SIZE] for i in range(0, len(selected), SHARD_SIZE)]
    for i, chunk in enumerate(chunks):
        files[f"Shard{i:03d}.lean"] = (
            f"import {DATA_MODULE}\n\n"
            f"-- Generated by KIP126/LinProgram/Translate/import-proofs.py; source SHA-256: {DB_SHA256}\n"
            f"namespace {NAMESPACE}.RawData\n\n"
            f"def shard{i} : Array DifferentialRow := #[\n" +
            ",\n".join(map(lean_row, chunk)) +
            f"\n]\n\nend {NAMESPACE}.RawData\n")
    files["Table.lean"] = (
        "".join(f"import {GENERATED_MODULE}.Shard{i:03d}\n" for i in range(len(chunks))) +
        f"\nnamespace {NAMESPACE}.RawData\n\n"
        f'def databaseSha256 : String := "{DB_SHA256}"\n'
        f"def sourceRowCount : Nat := {total}\n"
        f"def differentialRowCount : Nat := {len(selected)}\n\n"
        "/-- Lookup is shard-local so kernel checks need not unfold the whole table. -/\n"
        "def lookup (shard offset : Nat) : Option DifferentialRow :=\n  match shard with\n" +
        "".join(f"  | {i} => shard{i}[offset]?\n" for i in range(len(chunks))) +
        f"  | _ => none\n\nend {NAMESPACE}.RawData\n")
    manifest = dict(version="v126.3.cw49", source="https://zenodo.org/records/14875701",
                    archive_md5="f4c5a97a96a822092ce1ceb57c0a9d43",
                    database_sha256=DB_SHA256, basis_csv_sha256=BASIS_SHA256,
                    source_rows=total, first_id=first_id, last_id=last_id,
                    dispositions=dict(sorted(dispositions.items())),
                    reasons=dict(sorted(reasons.items())), shard_size=SHARD_SIZE,
                    exported_rows=len(selected), shards=len(chunks),
                    files_sha256={k: hashlib.sha256(v.encode()).hexdigest()
                                  for k, v in sorted(files.items())})
    files["manifest.json"] = json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"
    expected = set(files)
    existing = ({p.name for p in output.iterdir()} if output.exists() else set())
    if existing - expected:
        raise ValueError(f"unexpected/stale output files (not removed): {existing - expected}")
    if check:
        for name, content in files.items():
            if not (output / name).exists() or (output / name).read_text() != content:
                raise ValueError(f"generated output differs: {name}")
    else:
        output.mkdir(parents=True, exist_ok=True)
        for name, content in files.items():
            (output / name).write_text(content)
    print(json.dumps({k: v for k, v in manifest.items() if k != "files_sha256"}, indent=2))
    by_id = {row["id"]: (i, row) for i, row in enumerate(selected)}
    for query in query_ids:
        if query not in by_id:
            print(json.dumps(dict(query_id=query, admitted=False)))
        else:
            i, row = by_id[query]
            print(json.dumps(dict(query_id=query, admitted=True,
                                  shard=i // SHARD_SIZE, offset=i % SHARD_SIZE, row=row)))


class DecoderTests(unittest.TestCase):
    def row(self, **changes):
        return dict(dict(id=1, depth=0, reason="D", name="S0", s=1, t=64,
                         r=2, x="0", dx="0"), **changes)

    def test_empty_is_zero_not_unknown(self):
        self.assertEqual(coordinates(""), [])
        self.assertIsNone(coordinates(None))
        self.assertIsNone(coordinates("[NULL]"))

    def test_malformed_rejected(self):
        for text in ["-1", "1,1", "2,0", "a", "0,"]:
            with self.assertRaises(ValueError):
                coordinates(text)

    def test_branch_rejected(self):
        self.assertIsNone(classify(self.row(depth=1))[1])

    def test_inverse_degrees(self):
        item = classify(self.row(reason="DI", s=3, t=65))[1]
        self.assertEqual((item["s"], item["t"]), (1, 64))

    def test_sentinel_unknown_other_spectrum(self):
        for changes in [dict(r=999), dict(dx=None), dict(name="Cnu"),
                        dict(reason="T"), dict(reason=None)]:
            self.assertIsNone(classify(self.row(**changes))[1])

    def test_bad_database_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            db = Path(tmp) / "bad.db"
            db.touch()
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                export(db, Path(tmp), Path(tmp) / "out")

    def test_bad_direct_basis_csv_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            basis_csv = Path(tmp) / "S0_AdamsE2_basis.csv"
            basis_csv.write_bytes(b"not the pinned basis CSV")
            with self.assertRaisesRegex(ValueError, "basis CSV does not match"):
                read_basis(basis_csv=basis_csv)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("database", nargs="?", type=Path)
    basis_source = parser.add_mutually_exclusive_group()
    basis_source.add_argument("--e2-archive", type=Path)
    basis_source.add_argument("--e2-basis-csv", type=Path)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[3] /
                        "KIP126/LinProgram/Generated/Differentials")
    parser.add_argument("--raw-output", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--query-id", type=int, action="append", default=[],
                        help="report shard/offset and decoded row for this original database ID")
    args = parser.parse_args()
    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(DecoderTests)
        if not unittest.TextTestRunner().run(suite).wasSuccessful():
            raise SystemExit(1)
    if args.database:
        if not args.e2_archive and not args.e2_basis_csv:
            parser.error("--e2-archive or --e2-basis-csv is required with database")
        export(args.database, args.e2_archive, args.output_dir, args.raw_output, args.check,
               args.query_id, basis_csv=args.e2_basis_csv)
    elif not args.self_test:
        parser.error("supply database or --self-test")


if __name__ == "__main__":
    main()
