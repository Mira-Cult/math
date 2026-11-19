#!/usr/bin/env python3
"""Finite controls for integer_forest_logsobolev.md.

No numerical enumeration proves a universal entropy inequality. Fourier
numerators, positivity, pairwise factorization, forest recognition, Parseval,
and scalar-certificate comparisons below are exact integers/rationals.
Logarithmic evaluations are numerical diagnostics only.

Default: all ternary functions on 1,2,3 bits; constructed integer product-block functions; random positive integer-factor tensors. The optional complete 4-bit
ternary scan is in scan_ternary_integer_forests.c (3**16 cases):
  cc -O3 scan_ternary_integer_forests.c -lm -o "$TMPDIR/fei-ternary-scan"
  "$TMPDIR/fei-ternary-scan" 4
"""
from fractions import Fraction
from itertools import product
from math import log, log2
import random


def fwht(values):
    a = list(values)
    width = 1
    while width < len(a):
        for start in range(0, len(a), 2 * width):
            for offset in range(width):
                i, j = start + offset, start + offset + width
                u, v = a[i], a[j]
                a[i], a[j] = u + v, u - v
        width *= 2
    return a


def forest_edges(magnitudes):
    """Exact recognition of strictly positive pairwise forest tensors."""
    if not all(magnitudes):
        return None
    n = len(magnitudes).bit_length() - 1
    assert 1 << n == len(magnitudes)
    parent = list(range(n))
    edges = []

    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i

    for i in range(n):
        for j in range(i + 1, n):
            ij = (1 << i) | (1 << j)
            numerator = magnitudes[0] * magnitudes[ij]
            denominator = magnitudes[1 << i] * magnitudes[1 << j]
            for s in range(1 << n):
                if s & ij:
                    continue
                if (magnitudes[s] * magnitudes[s | ij] * denominator
                        != magnitudes[s | (1 << i)]
                        * magnitudes[s | (1 << j)] * numerator):
                    return None
            if numerator != denominator:
                u, v = root(i), root(j)
                if u == v:
                    return None
                parent[u] = v
                edges.append((i, j))
    return edges


def statistics(values):
    w = fwht(values)
    n = len(values).bit_length() - 1
    assert sum(a * a for a in w) == len(values) * sum(x * x for x in values)
    edges = forest_edges([abs(a) for a in w])
    if edges is None:
        return None
    mass = sum(a * a for a in w)
    energy = sum(s.bit_count() * a * a for s, a in enumerate(w))
    raw = sum(a * a * (2 * n - log2(a * a)) for a in w)
    normalized = raw - mass * (2 * n - log2(mass))
    return raw / energy, normalized / energy, w, edges


def exact_certificates():
    assert 2 ** 128 <= 3 ** 81  # U=3 versus the scalar maximum at U=4.
    t = Fraction(7, 25)
    assert 2 * (t + t ** 3 / 3) > Fraction(9, 16)  # c_0 < d.
    assert 16 ** 4 > 8 * 9 ** 4  # d > 3/4, hence C_F < 8.
    assert 16 ** 8 > 9 ** 9  # Raw constant four counterexample.
    assert fwht([1, 1, 1, 0]) == [3, 1, 1, -1]
    print("exact scalar/normalization/counterexample certificates: PASS")


def exhaustive_ternary():
    expected = {1: 4, 2: 48, 3: 704}
    for n in range(1, 4):
        count = 0
        maximum = (0.0, None)
        for values in product((-1, 0, 1), repeat=1 << n):
            info = statistics(values)
            if info is None:
                continue
            count += 1
            if info[0] > maximum[0]:
                maximum = info[0], values
            assert info[0] <= 6 / log2(Fraction(16, 9)) + 1e-10
        assert count == expected[n], (n, count, expected[n])
        print(f"n={n}: exact ternary cases={3 ** (1 << n)}, "
              f"positive forests={count}; numerical max raw ratio={maximum[0]:.12f}")


def factor_controls():
    rng = random.Random(20261116)
    kappa = 9 / (32 * log(2))
    count = 0
    for n in range(1, 8):
        for trial in range(200):
            # Includes cyclic factor graphs: the analytic estimate needs
            # integer factors, whereas forest structure is only sufficient
            # to produce such a factorization for an arbitrary integer tensor.
            edges = [(i, j) for i in range(n) for j in range(i + 1, n)
                     if rng.randrange(4) == 0]
            unary = [[rng.randrange(1, 6) for _ in range(2)] for i in range(n)]
            pair = [[rng.randrange(1, 6) for _ in range(4)] for e in edges]
            a = []
            for s in range(1 << n):
                value = 1
                for i in range(n):
                    value *= unary[i][(s >> i) & 1]
                for (i, j), pot in zip(edges, pair):
                    value *= pot[((s >> i) & 1) + 2 * ((s >> j) & 1)]
                a.append(value)
            z = sum(x * x for x in a)
            meanlog = sum(x * x * log2(x) for x in a) / z
            influence = sum(s.bit_count() * x * x for s, x in enumerate(a)) / z
            divergence = n - log2(z) + 2 * meanlog
            gradient = sum((a[s] - a[s ^ (1 << i)]) ** 2
                           for i in range(n) for s in range(1 << n)) / 4
            rhs = kappa * sum(x * x * log(x) for x in a)
            assert gradient <= rhs + 1e-8 * max(1, rhs)
            assert divergence <= 2 * kappa * meanlog + 1e-9
            assert n - meanlog <= 3 / log2(Fraction(16, 9)) * influence + 1e-9
            count += 1
    print(f"integer-factor numerical diagnostics: {count} tensors through 7 bits; PASS")


def sampled_integer_functions():
    rng = random.Random(412)
    for trial in range(500):
        values = [rng.randrange(1, 4)]
        for block in range(1 + trial % 3):
            while True:
                local = [rng.randrange(-3, 4) for _ in range(4)]
                if all(fwht(local)):
                    break
            values = [x * y for x in values for y in local]
        info = statistics(values)
        assert info is not None
        assert info[0] <= 6 / log2(Fraction(16, 9)) + 1e-10
    print("integer-valued product-block functions: 500 through 6 bits; numerical bound PASS")


if __name__ == "__main__":
    exact_certificates()
    exhaustive_ternary()
    factor_controls()
    sampled_integer_functions()
