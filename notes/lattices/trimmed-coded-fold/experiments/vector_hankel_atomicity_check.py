#!/usr/bin/env python3
"""CVP-M10 finite Hankel atomicity: small exact regressions, not a proof.

All arithmetic is exact in F_16 = F_2[X]/(X^4+X+1).  The tests include
vector moments, genuine matrix blocks, an F_4 scalar family with roots in
F_16, boundary spikes, and a repeated-root sequence rejected by Frobenius.
The mathematical proof is docs/VECTOR_HANKEL_ATOMICITY.md.
"""

import argparse
import itertools
import json
from pathlib import Path


def raw_mul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 16:
            a ^= 0b10011
    return result


MUL = tuple(tuple(raw_mul(a, b) for b in range(16)) for a in range(16))
INV = (0,) + tuple(next(b for b in range(1, 16) if MUL[a][b] == 1)
                   for a in range(1, 16))
SQUARE = tuple(MUL[a][a] for a in range(16))
F4 = tuple(a for a in range(16) if SQUARE[SQUARE[a]] == a)
assert len(F4) == 4


def rank(rows):
    matrix = [list(row) for row in rows]
    if not matrix:
        return 0
    count = 0
    for col in range(len(matrix[0])):
        pivot = next((row for row in range(count, len(matrix))
                      if matrix[row][col]), None)
        if pivot is None:
            continue
        matrix[count], matrix[pivot] = matrix[pivot], matrix[count]
        inv = INV[matrix[count][col]]
        matrix[count] = [MUL[x][inv] for x in matrix[count]]
        for row in range(count + 1, len(matrix)):
            scale = matrix[row][col]
            if scale:
                matrix[row] = [x ^ MUL[scale][y]
                               for x, y in zip(matrix[row], matrix[count])]
        count += 1
        if count == len(matrix):
            break
    return count


def hankel_rank(moment, k, length, m, n):
    return rank([[moment[a + b][i * n + j]
                  for b in range(length + 1) for j in range(n)]
                 for a in range(k) for i in range(m)])


def binary_matrix(value, size):
    return tuple((value >> i) & 1 for i in range(size))


def atomic_prefixes(roots, max_atoms, size, length):
    coefficients = [binary_matrix(value, size)
                    for value in range(1, 1 << size)]
    zero = tuple((0,) * size for _ in range(length + 1))
    best = {zero: 0}
    powers = {}
    for alpha in roots:
        powers[alpha] = [1]
        for _ in range(length):
            powers[alpha].append(MUL[powers[alpha][-1]][alpha])
    for count in range(1, max_atoms + 1):
        for support in itertools.combinations(roots, count):
            for coeff in itertools.product(coefficients, repeat=count):
                prefix = []
                for e in range(length + 1):
                    values = [0] * size
                    for alpha, vector in zip(support, coeff):
                        for i, bit in enumerate(vector):
                            if bit:
                                values[i] ^= powers[alpha][e]
                    prefix.append(tuple(values))
                key = tuple(prefix)
                best[key] = min(best.get(key, count), count)
    return best


def exhaust_binary(k, length, m, n):
    size = m * n
    choices = [binary_matrix(v, size) for v in range(1 << size)]
    roots = F4 if k == 3 else (0, 1)
    oracle = atomic_prefixes(roots, k - 1, size, length)
    counts = {"enumerated": 0, "frobenius": 0, "low_rank": 0,
              "rank_histogram": [0] * k}
    for moment in itertools.product(choices, repeat=k + length):
        counts["enumerated"] += 1
        if any(moment[2 * e] != moment[e] for e in range(k)):
            continue
        counts["frobenius"] += 1
        t = hankel_rank(moment, k, length, m, n)
        if t >= k:
            continue
        assert length >= max(t, 2 * t - 2)
        counts["low_rank"] += 1
        counts["rank_histogram"][t] += 1
        assert oracle.get(moment[:length + 1], k) <= t, (moment, t)
    return counts


def exhaust_f4_scalar():
    k, length = 3, 4
    oracle = atomic_prefixes(tuple(range(16)), 2, 1, length)
    counts = {"enumerated": 0, "frobenius": 0, "low_rank": 0,
              "rank_histogram": [0] * k}
    for values in itertools.product(F4, repeat=k + length):
        counts["enumerated"] += 1
        if any(values[2 * e] != SQUARE[values[e]] for e in range(k)):
            continue
        counts["frobenius"] += 1
        moment = tuple((v,) for v in values)
        t = hankel_rank(moment, k, length, 1, 1)
        if t >= k:
            continue
        counts["low_rank"] += 1
        counts["rank_histogram"][t] += 1
        assert oracle.get(moment[:length + 1], k) <= t, (moment, t)
    return counts


def multiply2(a, b):
    return tuple(MUL[a[2 * i]][b[j]] ^ MUL[a[2 * i + 1]][b[2 + j]]
                 for i in range(2) for j in range(2))


def charpoly2(a):
    return (MUL[a[0]][a[3]] ^ MUL[a[1]][a[2]], a[0] ^ a[3], 1)


def characteristic_check():
    total = 0
    for a in itertools.product(F4, repeat=4):
        polynomial_squared = tuple(SQUARE[x] for x in charpoly2(a))
        assert charpoly2(multiply2(a, a)) == polynomial_squared
        assert charpoly2(tuple(SQUARE[x] for x in a)) == polynomial_squared
        total += 1
    return total


def hostile_examples():
    k, length = 3, 4
    spike = tuple((int(e == k + length - 1),)
                  for e in range(k + length))
    assert hankel_rank(spike, k, length, 1, 1) == 1
    assert all(spike[2 * e] == spike[e] for e in range(k))
    assert all(entry == (0,) for entry in spike[:length + 1])
    # Positive Hankel rank need not equal the atom count of the prefix.
    assert atomic_prefixes(F4, 2, 1, length)[spike[:length + 1]] == 0

    repeated_root = tuple((e & 1,) for e in range(k + length))
    assert hankel_rank(repeated_root, k, length, 1, 1) == 2
    assert repeated_root[2] != repeated_root[1]
    assert repeated_root[:length + 1] not in atomic_prefixes(F4, 2, 1, length)
    return {"boundary_spike_rank": 1, "boundary_spike_prefix_atoms": 0,
            "repeated_root_rank": 2, "repeated_root_frobenius_rejected": True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    certificate = {
        "schema": "cvp.vector-hankel-atomicity.v1",
        "claim": "finite component regressions; symbolic proof required",
        "binary_vector_k3_L4": exhaust_binary(3, 4, 2, 1),
        "binary_vector_k3_L2": exhaust_binary(3, 2, 2, 1),
        "binary_matrix_k2_L2": exhaust_binary(2, 2, 2, 2),
        "f4_scalar_k3_L4": exhaust_f4_scalar(),
        "f4_characteristic_polynomial_matrices": characteristic_check(),
        "hostile_examples": hostile_examples(),
    }
    encoded = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end="")
    print("PASS: cvp.vector-hankel-atomicity.v1")


if __name__ == "__main__":
    main()

