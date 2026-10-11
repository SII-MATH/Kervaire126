#!/usr/bin/env python3
"""Check the native 5 -> 4 -> 4 matrix input; no spectral-sequence certification.

The existing canonical Zenodo record authenticates the local archive. Extract
only its fixed CW_nu_eta member into a temporary directory and compare every
basis row at the three degrees with the derived snapshot and Lean literals.
No network, source registry, archive mutation, or database write is performed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SNAPSHOT = "KIP126/LinProgram/Generated/Provenance/row462481-trace.json"
LEAN = "KIP126/LinProgram/Certificates/BranchD2Coordinates.lean"
ARCHIVE = "Source/LWXMachine/kervaire_database.rar"
MEMBER = "kervaire-49/CW_nu_eta_AdamsSS_t200.db"
DEGREES = (("incoming", (16, 145)), ("target", (18, 146)),
           ("outgoing_target", (20, 147)))
BASIS_SCHEMA = ("CREATE TABLE CW_nu_eta_AdamsE2_basis (id INTEGER PRIMARY KEY, "
                "mon TEXT, repr TEXT, s SMALLINT, t SMALLINT, d2 TEXT)")
SS_SCHEMA = ("CREATE TABLE CW_nu_eta_AdamsE2_ss (id INTEGER PRIMARY KEY, "
             "s SMALLINT, t SMALLINT, base TEXT, diff TEXT, level SMALLINT)")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def coordinates(raw, dimension):
    require(isinstance(raw, str), "NULL/absent d2 is unknown, not zero")
    if raw == "":
        return []
    require(re.fullmatch(r"(?:0|[1-9][0-9]*)(?:,(?:0|[1-9][0-9]*))*", raw),
            "unknown or malformed d2 coordinates")
    result = list(map(int, raw.split(",")))
    require(result == sorted(set(result)), "duplicate or unsorted d2 coordinates")
    require(all(i < dimension for i in result), "d2 coordinate out of range")
    return result


def checked_archive(root, archive):
    canonical = json.loads((root / "docs/external-inputs.json").read_text())
    source = next(s for s in canonical["sources"] if s["id"] == "lwx_machine")
    record_path = "Source/LWXMachine/zenodo-record.json"
    artifact = next(a for a in source["artifacts"] if a["path"] == record_path)
    record_bytes = (root / record_path).read_bytes()
    require(hashlib.sha256(record_bytes).hexdigest() == artifact["sha256"],
            "canonical Zenodo record SHA-256 mismatch")
    record = json.loads(record_bytes)
    require(record["id"] == 14875701 and record["metadata"]["version"] == "v126.3.cw49",
            "wrong native dataset version")
    entry = next(f for f in record["files"] if f["key"] == "kervaire_database.rar")
    # The archive checksum is already used by the registered Ceta input; it
    # is not promoted from the new derived snapshot to a trust baseline.
    origin = next(a for a in source["artifacts"]
                  if a["path"] == "KIP126/LinProgram/Raw/Ceta_AdamsSS_t200.db")["extracted_from"]
    require(origin["record"] == record_path and origin["archive"] == entry["key"]
            and origin["archive_size"] == entry["size"]
            and origin["archive_checksum"] == entry["checksum"],
            "archive identity differs from registered same-source input")
    size, md5, sha = 0, hashlib.md5(), hashlib.sha256()
    with archive.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            size += len(block)
            md5.update(block)
            sha.update(block)
    require(size == entry["size"] and "md5:" + md5.hexdigest() == entry["checksum"],
            "fixed archive size/checksum mismatch")
    data = subprocess.check_output(["unrar", "p", "-inul", str(archive), MEMBER])
    return data, dict(size=size, sha256=sha.hexdigest(), checksum=entry["checksum"],
                      zenodo_record_sha256=artifact["sha256"])


def read_slices(db):
    for table, expected in (("CW_nu_eta_AdamsE2_basis", BASIS_SCHEMA),
                            ("CW_nu_eta_AdamsE2_ss", SS_SCHEMA)):
        row = db.execute("SELECT sql FROM sqlite_master WHERE name=?", (table,)).fetchone()
        require(row is not None and row[0] == expected, f"unexpected native schema: {table}")
    result = {}
    for key, degree in DEGREES:
        basis = [dict(row, local_index=i) for i, row in enumerate(db.execute(
            "SELECT * FROM CW_nu_eta_AdamsE2_basis WHERE s=? AND t=? ORDER BY id", degree))]
        staircase = [dict(row) for row in db.execute(
            "SELECT * FROM CW_nu_eta_AdamsE2_ss WHERE s=? AND t=? ORDER BY id", degree)]
        result[key] = dict(spectrum="CW_nu_eta", degree=list(degree),
                           basis_dimension=len(basis), basis=basis, staircase=staircase)
    return result


def literal(text, name, type_text):
    pattern = rf"^def {re.escape(name)} : {re.escape(type_text)} :=[ \t]*([^\n]*(?:\n[ \t]+[^\n]*)*)"
    matches = re.findall(pattern, text, re.MULTILINE)
    require(len(matches) == 1, f"missing/ambiguous Lean literal: {name}")
    return matches[0].strip()


def raw_rows_literal(text, name):
    body = literal(text, name, "List (Nat × Option String)")
    token = r'\(([0-9]+), (none|some "[0-9,]*")\)'
    require(re.fullmatch(r'\[\s*' + token + r'(?:\s*,\s*' + token + r')*\s*\]', body),
            f"unsupported Lean row expression: {name}")
    result = []
    for rowid, raw in re.findall(token, body):
        result.append((int(rowid), None if raw == "none" else json.loads(raw[5:])))
    return result


def check_contract(slices, snapshot, lean):
    coverage = snapshot["candidate_coverage"]
    require([slices[k]["basis_dimension"] for k, _ in DEGREES] == [5, 4, 4],
            "complete native dimensions changed")
    for key, _ in DEGREES:
        require(coverage[key] == slices[key], f"snapshot native rows differ: {key}")
    incoming = [coordinates(r["d2"], 4) for r in slices["incoming"]["basis"]]
    outgoing = [coordinates(r["d2"], 4) for r in slices["target"]["basis"]]
    require(incoming == [[1, 3], [], [], [], []] and outgoing == [[], [2], [], [2]],
            "fixed matrix columns changed")
    require(coverage["dimensions"] == [5, 4, 4]
            and coverage["incoming_d2_columns"] == incoming
            and coverage["outgoing_d2_columns"] == outgoing, "snapshot columns differ")
    for key, columns in (("incoming", incoming), ("outgoing", outgoing)):
        require(coverage[key + "_matrix_rows"] ==
                [[int(i in col) for col in columns] for i in range(4)],
                f"snapshot matrix differs: {key}")
    for name, key in (("rawIncoming", "incoming"), ("rawOutgoing", "target")):
        require(raw_rows_literal(lean, name) == [(r["id"], r["d2"]) for r in slices[key]["basis"]],
                f"Lean native columns differ: {name}")
    for name, degree in (("incomingDegree", (16, 145)), ("middleDegree", (18, 146)),
                         ("outgoingDegree", (20, 147))):
        require(literal(lean, name, "ℕ × ℕ") == str(degree), f"Lean degree differs: {name}")
    require(literal(lean, "outgoingBasisIds", "List Nat") ==
            str([r["id"] for r in slices["outgoing_target"]["basis"]]),
            "Lean outgoing basis ids differ")
    require(literal(lean, "rawRepresentatives", "List (Option String)") ==
            '[some "", some "0", some "2", some "0,2"]', "Lean representatives differ")
    require(coverage["quotient_representatives"] == [[], [0], [2], [0, 2]],
            "snapshot representatives differ")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--archive", type=Path, help="local copy of the SAME fixed archive")
    args = parser.parse_args()
    root = args.root.resolve()
    data, metadata = checked_archive(root, args.archive or root / ARCHIVE)
    snapshot = json.loads((root / SNAPSHOT).read_text())
    archive = snapshot["provenance"]["existing_data_archive"]
    require(all(archive[k] == v for k, v in metadata.items()), "snapshot archive provenance differs")
    member = next(a for a in snapshot["provenance"]["additional_existing_archived_inputs"]
                  if a["member"] == MEMBER)
    require(member["bytes"] == len(data) and member["sha256"] == hashlib.sha256(data).hexdigest(),
            "snapshot member differs from authenticated archive")
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "native.db"
        path.write_bytes(data)
        db = sqlite3.connect(path.as_uri() + "?mode=ro", uri=True)
        db.row_factory = sqlite3.Row
        db.execute("PRAGMA query_only=ON")
        try:
            slices = read_slices(db)
        finally:
            db.close()
    check_contract(slices, snapshot, (root / LEAN).read_text())
    print("Verified full native 5 -> 4 -> 4 matrix rows and Lean input against the fixed archive; "
          "no actual Adams-page comparison or candidate coverage is certified.")


if __name__ == "__main__":
    main()
