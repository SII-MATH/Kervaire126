#!/usr/bin/env python3
"""Read-only check of two R10 product-boundary witnesses in pinned Lin CSV.

Usage: python3 scripts/check-near126-product-boundaries.py ARCHIVE.rar
       python3 scripts/check-near126-product-boundaries.py --self-test

Checks exact CSV hashes, local-degree basis indices, three d2 columns, and
explicit F2 polynomial certificates using archived relations. Outputs JSON;
does not modify the archive, generate Lean axioms, or prove that the archived
d2 agrees with the fixed sphere's Adams differential. CSV notation source:
Source/LWXMachine/source/ms.tex, notation nt:basis (lines 137--153).
"""

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess

HASHES = {
    "generators": "3c4e45a1e28837e651e729bee14e7c62a99f797bc650d69e8a79aec13a762c72",
    "relations": "8b4b67d6fb3c9a3a264813ea780340e73b1a66290c8616d3308ae1fc19f3add5",
    "basis": "6a337964ad3ac02b729a46fd839dced7cb6764d14d4cea413163987eba8de871",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def monomial(code):
    if not code:
        return ()
    ns = list(map(int, code.split(",")))
    require(len(ns) % 2 == 0, "not a ring monomial")
    powers = {}
    for i, e in zip(ns[::2], ns[1::2]):
        require(i >= 0 and e > 0, "invalid generator or exponent")
        powers[i] = powers.get(i, 0) + e
    return tuple(sorted(powers.items()))


def polynomial(code):
    result = set()
    for part in code.split(";"):
        result.symmetric_difference_update({monomial(part)})
    return frozenset(result)


def multiply(m, poly):
    result = set()
    for term in poly:
        powers = dict(m)
        for i, e in term:
            powers[i] = powers.get(i, 0) + e
        result.symmetric_difference_update({tuple(sorted(powers.items()))})
    return frozenset(result)


def verify_certificate(product, image, relations, certificate):
    total = frozenset()
    for multiplier, relation in certificate:
        require(relation in relations, f"relation absent: {relation}")
        total ^= multiply(monomial(multiplier), polynomial(relation))
    require(polynomial(product) ^ image == total, "polynomial certificate mismatch")


def self_test():
    require(polynomial("2,1;2,1") == frozenset(), "F2 cancellation failed")
    require(monomial("2,1,2,2") == ((2, 3),), "exponent addition failed")
    rel = "2,1,79,1;0,1,89,1"
    verify_certificate("2,1,69,1,79,1", polynomial("0,1,69,1,89,1"),
                       {rel}, [("69,1", rel)])
    try:
        verify_certificate("2,1,69,1,79,1", frozenset(), {rel}, [("69,1", rel)])
    except ValueError:
        pass
    else:
        raise ValueError("tampered target was accepted")
    print("4 certificate self-tests passed")


def check(archive):
    rows = {}
    for kind, expected in HASHES.items():
        member = f"kervaire_csv/S0_AdamsE2_{kind}.csv"
        raw = subprocess.run(["unrar", "p", "-inul", str(archive), member],
                             check=True, stdout=subprocess.PIPE).stdout
        require(hashlib.sha256(raw).hexdigest() == expected, f"hash mismatch: {member}")
        rows[kind] = list(csv.DictReader(io.StringIO(raw.decode("utf-16"))))
    generators = {int(row["id"]): row for row in rows["generators"]}
    names = {0: "h_0", 2: "h_2", 18: "h_5", 69: "h_6", 79: "Md_0",
             188: "x_{91,11}", 419: "x_{126,10}", 427: "x_{126,11}"}
    for i, name in names.items():
        require(generators[i]["name"] == name, f"generator name mismatch: {i}")

    def degree(m):
        return tuple(sum(e * int(generators[i][k]) for i, e in m) for k in ("stem", "s"))

    basis, by_monomial = {}, {}
    for row in rows["basis"]:
        key = (int(row["stem"]), int(row["s"]), int(row["index"]))
        require(key not in basis, f"duplicate local index: {key}")
        m = monomial(row["mon"])
        require(degree(m) == key[:2], f"basis degree mismatch: {key}")
        require(m not in by_monomial, f"duplicate monomial: {m}")
        basis[key] = row
        by_monomial[m] = row
    relations = {row["rel"]: n + 1 for n, row in enumerate(rows["relations"])}
    cases = [
        ("P*h2", "2,1,69,1,79,1", ["419,1"],
         [("69,1", "2,1,79,1;0,1,89,1")]),
        ("Q*h2", "2,1,18,1,188,1", ["427,1", "0,1,419,1"],
         [("", "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1"),
          ("", "0,1,426,1;0,4,391,1"),
          ("", "0,2,69,1,89,1;0,5,375,1")]),
    ]
    results = []
    for name, product, source_codes, certificate in cases:
        target_degree = degree(monomial(product))
        image, witnesses = frozenset(), []
        for code in source_codes:
            row = by_monomial[monomial(code)]
            stem, s = int(row["stem"]), int(row["s"])
            require((stem - 1, s + 2) == target_degree, "d2 degree mismatch")
            d2 = row["d2"].strip()
            require("NULL" not in d2, "unknown d2 is not a zero differential")
            indices = list(map(int, d2.split(","))) if d2 else []
            require(len(indices) == len(set(indices)), "duplicate d2 index")
            targets = [basis[(stem - 1, s + 2, i)]["mon"] for i in indices]
            for target in targets:
                image ^= polynomial(target)
            witnesses.append({"source_mon": code, "source_stem_s": [stem, s],
                              "source_local_index": int(row["index"]),
                              "d2_local_indices": indices, "target_mons": targets})
        verify_certificate(product, image, relations, certificate)
        results.append({"product": name, "product_mon": product,
                        "target_s_t": [target_degree[1], sum(target_degree)],
                        "d2_witnesses": witnesses,
                        "relation_certificate": [
                            {"multiplier": m, "relation": rel,
                             "csv_data_row_1based": relations[rel]}
                            for m, rel in certificate]})
    return {"schema": "kip126.near126.product-boundaries.v1",
            "csv_sha256": HASHES,
            "checks": "pinned bytes, generator names, degrees, d2 rows, F2 ideal certificates",
            "not_checked": "agreement with sphereAdamsData.d; Lean proof; full R10 exhaustion",
            "witnesses": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", nargs="?", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    if args.archive:
        print(json.dumps(check(args.archive), indent=2))
    elif not args.self_test:
        parser.error("supply an archive or --self-test")


if __name__ == "__main__":
    main()
