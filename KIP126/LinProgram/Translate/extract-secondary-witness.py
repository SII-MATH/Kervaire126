#!/usr/bin/env python3
"""Recover a bounded secondary-resolution witness; never certify actual Adams d2.

The two SQLite inputs are produced by the exact archived Adams program.
Multiplication is checked independently by the Milnor coproduct matrix formula.
This produces mathematical-algebra data for a future Lean checker. It is not
itself a Lean certificate or a comparison with the fixed sphere sequence.
"""
import argparse
from collections import defaultdict
from functools import lru_cache
import hashlib
import json
from math import comb
from pathlib import Path
import sqlite3
import struct
import time

ZERO = (0,) * 8
COUNTS = defaultdict(int)


def trim(exponents):
    return tuple(exponents) + (0,) * (8 - len(exponents))


def degree(exponents):
    return sum(n * ((1 << (i + 1)) - 1) for i, n in enumerate(exponents))


def decode(blob):
    """Archived little-endian MMod encoding: 37 exponent, 9 weight, 18 v bits."""
    result = set()
    for (word,) in struct.iter_unpack('<Q', blob or b''):
        exponents = [0] * 8
        index = 0
        for j in range(1, 10):
            for i in range(j - 1, -1, -1):
                if index < 37 and word & (1 << (36 - index)):
                    exponents[j - i - 1] += 1 << i
                index += 1
        result.symmetric_difference_update({(tuple(exponents), (~word & ((1 << 64) - 1)) >> 46)})
    return frozenset(result)


@lru_cache(maxsize=None)
def product(left, right, modulus=2):
    """Dualize delta(xi_n)=sum xi_i^(2^j) tensor xi_j, also over Z/4.

    Entries m_(i,j) satisfy left_i=sum_j 2^j*m_(i,j) and
    right_j=sum_i m_(i,j). Output exponent n_k=sum_(i+j=k)m_(i,j).
    Each diagonal contributes its ordinary multinomial coefficient.
    """
    COUNTS['distinct_products'] += 1
    total_degree = degree(left) + degree(right)
    size = min(8, total_degree.bit_length())
    cells = [(i, j) for i in range(1, size + 1)
             for j in range(1, size - i + 1)]
    remainder_left, remainder_right = list(left), list(right)
    matrix = {}
    result = defaultdict(int)

    def visit(position):
        if position < len(cells):
            i, j = cells[position]
            weight = 1 << j
            for value in range(min(remainder_left[i - 1] // weight,
                                   remainder_right[j - 1]) + 1):
                matrix[i, j] = value
                remainder_left[i - 1] -= weight * value
                remainder_right[j - 1] -= value
                visit(position + 1)
                remainder_left[i - 1] += weight * value
                remainder_right[j - 1] += value
            return
        COUNTS['matrices'] += 1
        exponents, coefficient = [], 1
        for k in range(1, size + 1):
            diagonal = ([remainder_left[k - 1], remainder_right[k - 1]] +
                        [matrix[i, k - i] for i in range(1, k)])
            exponent = sum(diagonal)
            remainder = exponent
            for value in diagonal:
                coefficient = coefficient * comb(remainder, value) % modulus
                remainder -= value
            exponents.append(exponent)
        if coefficient:
            key = trim(exponents)
            result[key] = (result[key] + coefficient) % modulus

    visit(0)
    return tuple((word, c) for word, c in sorted(result.items()) if c)


def contract(exponents, *factors):
    output = list(exponents)
    for i, k in factors:
        if i == 0:
            continue
        if output[i - 1] < 1 << k:
            return None
        output[i - 1] -= 1 << k
    return tuple(output)


def compose(module, images):
    result = set()
    for left, v in module:
        for right, w in images[v]:
            for word, _ in product(left, right):
                result.symmetric_difference_update({(word, w)})
    return frozenset(result)


def obstruction(dg, diffs, s):
    """The explicit secondary associator `ddd`, independently using matrix products."""
    result = set()
    for q, v in dg:
        q1 = contract(q, (1, 0))
        if q1 is None:
            continue
        mod4 = defaultdict(int)
        for r, w in diffs[s - 1][v]:
            for a, z in diffs[s - 2][w]:
                for word, coefficient in product(r, a, 4):
                    mod4[word, z] = (mod4[word, z] + coefficient) % 4
        for (word, z), coefficient in mod4.items():
            if coefficient not in (0, 2):
                raise ValueError('secondary lift composition is not two-torsion')
            if coefficient == 2:
                for word1, _ in product(q1, word):
                    result.symmetric_difference_update({(word1, z)})

    size = min(8, max((degree(q) for q, _ in dg), default=0).bit_length())
    for m in range(1, size + 1):
        for n in range(1, m + 1):
            partial = set()
            for q, v in dg:
                for n1 in range(1, n + 1):
                    for m1 in range(n1):
                        q1 = contract(q, (m - m1, m1), (n - n1, n1))
                        if q1 is None:
                            continue
                        for r, w in diffs[s - 1][v]:
                            for a, z in diffs[s - 2][w]:
                                for k in range(m1 + 1):
                                    r1 = contract(r, (m1 - k, k), (n1 - k, k))
                                    a1 = contract(a, (k + 1, 0))
                                    if r1 is None or a1 is None:
                                        continue
                                    for ra, _ in product(r1, a1):
                                        for qra, _ in product(q1, ra):
                                            partial.symmetric_difference_update({(qra, z)})
            outer = [0] * 8
            outer[m - 1] += 1
            outer[n - 1] += 1
            for word, z in partial:
                for output, _ in product(tuple(outer), word):
                    result.symmetric_difference_update({(output, z)})
    return frozenset(result)


def read_tables(resolution_path, secondary_path):
    connections = [sqlite3.connect(f'file:{p.resolve()}?mode=ro', uri=True)
                   for p in (resolution_path, secondary_path)]
    diffs, lifts, degrees = defaultdict(dict), defaultdict(dict), {}
    for ident, s, t, blob in connections[0].execute(
            'select id,s,t,diff from S0_Adams_res_generators order by id'):
        v = ident % (1 << 19)
        if ident >> 19 != s:
            raise ValueError('inconsistent LocId filtration')
        diffs[s][v], degrees[s, v] = decode(blob), t
    for ident, blob, augmentation in connections[1].execute(
            'select id,d2,d2_h from S0_Adams_d2 order by id'):
        s, v = ident >> 19, ident % (1 << 19)
        lifts[s][v] = decode(blob)
        actual = sorted(w for word, w in lifts[s][v] if word == ZERO)
        expected = [int(w) for w in augmentation.split(',')] if augmentation else []
        if actual != expected:
            raise ValueError('stored d2_h disagrees with augmentation of lift')
    for v in diffs[1]:
        lifts[1][v] = frozenset()
    for c in connections:
        c.close()
    return diffs, lifts, degrees


def terms(module):
    return [{'sq': list(word), 'v': v} for word, v in sorted(module)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--resolution', required=True, type=Path)
    parser.add_argument('--secondary', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--target-id', type=int, default=4194320)
    parser.add_argument('--comparison-target-id', type=int, default=4194319)
    parser.add_argument('--source-v', type=int, default=16)
    args = parser.parse_args()
    start = time.perf_counter()
    diffs, lifts, degrees = read_tables(args.resolution, args.secondary)
    root = args.target_id >> 19, args.target_id % (1 << 19)
    other = args.comparison_target_id >> 19, args.comparison_target_id % (1 << 19)
    if (other[0], degrees[other]) != (root[0], degrees[root]):
        raise ValueError('comparison target is in another bidegree')
    closure, pending = set(), [root, other]
    while pending:
        key = pending.pop()
        if key in closure:
            continue
        closure.add(key)
        s, v = key
        for _, w in diffs[s][v]:
            pending.append((s - 1, w))
        for _, w in lifts[s].get(v, ()):
            pending.append((s - 2, w))
    rows = []
    for s, v in sorted(closure):
        dg, lift = diffs[s][v], lifts[s].get(v, frozenset())
        t = degrees[s, v]
        for word, w in dg:
            if degree(word) + degrees[s - 1, w] != t:
                raise ValueError('inhomogeneous resolution differential')
        for word, w in lift:
            if degree(word) + degrees[s - 2, w] != t - 1:
                raise ValueError('inhomogeneous secondary lift')
        if s >= 2 and compose(dg, diffs[s - 1]):
            raise ValueError(f'd squared is nonzero at {(s, v)}')
        if s >= 3:
            left = compose(lift, diffs[s - 2])
            fd = compose(dg, lifts[s - 1])
            assoc = obstruction(dg, diffs, s)
            if left != fd.symmetric_difference(assoc):
                raise ValueError(f'secondary chain equation failed at {(s, v)}')
        else:
            left, fd, assoc = frozenset(), frozenset(), frozenset()
        rows.append(dict(id=(s << 19) + v, s=s, v=v, t=t, d=terms(dg),
                         f=terms(lift), d_f=terms(left), f_d=terms(fd),
                         associator=terms(assoc)))
    augmentation = sorted(w for word, w in lifts[root[0]][root[1]] if word == ZERO)
    other_augmentation = sorted(w for word, w in lifts[other[0]][other[1]] if word == ZERO)
    if args.source_v not in augmentation:
        raise ValueError('selected source is absent from target lift augmentation')
    if args.source_v in other_augmentation:
        raise ValueError('selected source also has the comparison target coefficient')
    output = dict(status='independent-Python-chain-equations-checked; not-a-Lean-proof',
                  target_id=args.target_id, source_v=args.source_v,
                  augmentation=augmentation, comparison_target_id=args.comparison_target_id,
                  comparison_augmentation=other_augmentation,
                  closure_generators=len(rows),
                  chain_semantic_sha256=hashlib.sha256(
                      json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
                  input_hashes={str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in (args.resolution, args.secondary)},
                  runtime_seconds=time.perf_counter() - start,
                  operation_counts=dict(COUNTS), generators=rows,
                  remaining=['Prove the checker sound in Lean for the Steenrod algebra.',
                             'Certify resolution exactness, minimality and basis identification.',
                             'Construct secondary Steenrod comparison to the actual sphere d2.',
                             'Relate secondary augmentation to original CSV coordinates.'])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({k: v for k, v in output.items() if k != 'generators'}, indent=2))


if __name__ == '__main__':
    main()
