#!/usr/bin/env python3
"""Exact certificates and constructive checks for bounded-treewidth spectra.

Python standard library only. Universal claims are proved in the manuscript;
the census and seeded examples are finite checks, never extrapolations.
"""

from itertools import combinations, permutations, product
from math import gcd
from random import Random


def walsh(values):
    values = list(values)
    step = 1
    while step < len(values):
        for start in range(0, len(values), 2 * step):
            for j in range(start, start + step):
                a, b = values[j], values[j + step]
                values[j], values[j + step] = a + b, a - b
        step *= 2
    return values


def project(mask, bits):
    return sum(((mask >> bit) & 1) << j for j, bit in enumerate(bits))


def interaction_graph(values, n):
    """Positive-tensor conditional independence, using exact products."""
    assert len(values) == 1 << n and min(values) > 0
    edges = set()
    for i, j in combinations(range(n), 2):
        ib, jb = 1 << i, 1 << j
        if any(values[s] * values[s | ib | jb]
               != values[s | ib] * values[s | jb]
               for s in range(1 << n) if not s & (ib | jb)):
            edges.add((i, j))
    return edges


def elimination_width(n, edges, order):
    adjacent = [set() for _ in range(n)]
    for a, b in edges:
        adjacent[a].add(b)
        adjacent[b].add(a)
    active = set(range(n))
    width = 0
    for i in order:
        neighbors = adjacent[i] & active
        width = max(width, len(neighbors))
        for a, b in combinations(neighbors, 2):
            adjacent[a].add(b)
            adjacent[b].add(a)
        active.remove(i)
    return width


def small_best_order(n, edges):
    assert n <= 4
    return min((elimination_width(n, edges, order), order)
               for order in permutations(range(n)))


def integer_bag_factors(values, n, edges, order):
    """Construct Lemma 3 by primitive positive gcd fibers, then reconstruct."""
    original = list(values)
    assert len(values) == 1 << n and min(values) > 0
    adjacent = [set() for _ in range(n)]
    for a, b in edges:
        adjacent[a].add(b)
        adjacent[b].add(a)
    remaining = list(range(n))
    factors = []
    width = 0
    for i in order:
        pos = remaining.index(i)
        later = [j for j in remaining if j != i]
        neighbors = sorted(adjacent[i] & set(later))
        width = max(width, len(neighbors))
        positions = [later.index(j) for j in neighbors]
        table = [None] * (1 << (len(neighbors) + 1))
        residual = []
        for s in range(1 << len(later)):
            low = s & ((1 << pos) - 1)
            base = low | ((s >> pos) << (pos + 1))
            a, b = values[base], values[base | (1 << pos)]
            common = gcd(a, b)
            residual.append(common)
            bag = project(s, positions) << 1
            for bit, entry in enumerate((a // common, b // common)):
                index = bag | bit
                assert table[index] is None or table[index] == entry
                table[index] = entry
        assert all(isinstance(a, int) and a >= 1 for a in table)
        factors.append(([i] + neighbors, table))
        for a, b in combinations(neighbors, 2):
            adjacent[a].add(b)
            adjacent[b].add(a)
        values, remaining = residual, later
    assert len(values) == 1 and not remaining
    scalar = values[0]
    assert scalar >= 1
    for s, value in enumerate(original):
        rebuilt = scalar
        for bits, table in factors:
            rebuilt *= table[project(s, bits)]
        assert rebuilt == value
    return scalar, factors, width


def exact_raw_fourteen(A, n):
    """Compare H_raw <=14 I by exponentiating to an integer inequality."""
    Z = sum(a * a for a in A)
    influence_numerator = sum(s.bit_count() * a * a
                              for s, a in enumerate(A))
    exponent = 2 * n * Z - 14 * influence_numerator
    if exponent <= 0:
        return
    left = 1
    for a in A:
        left *= pow(a, 2 * a * a)
    assert left >= 1 << exponent


def scalar_certificates():
    expected = [4294967296, 905567907, 337051, 221, 16, 2726,
                8322616057, 2832420683990347645540,
                475348068689013873737817172053634531194]
    for u, floor in enumerate(expected, 1):
        y = u * u
        left = pow(2, 16 * (y - 1)) * pow(u, 27 * y)
        right = pow(y + 1, 16 * (y + 1))
        assert right // left == floor and right >= left
    assert 10 ** 5 > 2 ** 16
    assert 23 ** 16 > 2 ** 15 * 12 ** 16
    assert 23 ** 6 > 4 * 12 ** 7
    return len(expected)


def small_function_census():
    boolean_total = positive = width_two = 0
    for n in range(5):
        size = 1 << n
        for truth in range(1 << size):
            A = [abs(a) for a in walsh(
                1 - 2 * ((truth >> x) & 1) for x in range(size))]
            boolean_total += 1
            if not all(A):
                continue
            positive += 1
            edges = interaction_graph(A, n)
            width, order = small_best_order(n, edges)
            if width <= 2:
                scalar, factors, actual = integer_bag_factors(A, n, edges, order)
                assert actual == width
                assert all(len(bits) <= 3 for bits, _ in factors)
                exact_raw_fourteen(A, n)
                width_two += 1
    ternary_total = ternary_positive = 0
    for n in range(4):
        for truth in product((-1, 0, 1), repeat=1 << n):
            ternary_total += 1
            A = list(map(abs, walsh(truth)))
            if not all(A):
                continue
            ternary_positive += 1
            edges = interaction_graph(A, n)
            width, order = small_best_order(n, edges)
            assert width <= 2
            integer_bag_factors(A, n, edges, order)
            exact_raw_fourteen(A, n)
    return dict(boolean_total=boolean_total, boolean_positive=positive,
                boolean_width_two=width_two, ternary_total=ternary_total,
                ternary_positive=ternary_positive)


def random_junction_trees():
    rng = Random(20261116)
    count = 0
    # Signed prime-valuation potentials test a nontrivial reparameterization:
    # input local factors may be fractions although the full tensor is integer.
    for width in (1, 2, 3):
        for _ in range(100):
            n = rng.randrange(width + 1, 10)
            bags = [list(range(i, min(n, i + width + 1))) for i in range(n)]
            tables = [[rng.randrange(-2, 3) for _ in range(1 << len(b))]
                      for b in bags]
            other = [[rng.randrange(-1, 2) for _ in range(1 << len(b))]
                     for b in bags]
            E = [sum(t[project(s, b)] for b, t in zip(bags, tables))
                 for s in range(1 << n)]
            F = [sum(t[project(s, b)] for b, t in zip(bags, other))
                 for s in range(1 << n)]
            emin, fmin = min(E), min(F)
            A = [2 ** (a - emin) * 3 ** (b - fmin) for a, b in zip(E, F)]
            edges = {tuple(e) for b in bags for e in combinations(b, 2)}
            _, factors, actual = integer_bag_factors(A, n, edges, range(n))
            assert actual == width
            assert all(len(b) <= width + 1 for b, _ in factors)
            count += 1
    return count


def exact_obstructions():
    for M in range(1, 13):
        A = []
        for s in range(8):
            cuts = sum(((s >> i) ^ (s >> j)) & 1
                       for i, j in combinations(range(3), 2))
            v = 2 - cuts
            amplitude = 2 ** (M * v)
            A.append(amplitude)
            equalities = 3 - cuts
            assert 2 ** M * amplitude == 2 ** (M * equalities)
        Z = sum(a * a for a in A)
        assert Z == 2 * 16 ** M + 6
        assert Z & (Z - 1)  # not even a power of two
        integer_bag_factors(A, 3, {(0, 1), (0, 2), (1, 2)}, range(3))
    # E=xy; after minimizing coordinate orientations B=4/7+8/7<2.
    weights = [1, 1, 1, 4]
    assert sum(weights) == 7
    assert 4 + 2 * (2 + 2) == 12 < 14
    return 12


if __name__ == '__main__':
    certificates = scalar_certificates()
    census = small_function_census()
    random_cases = random_junction_trees()
    defects = exact_obstructions()
    print(dict(scalar_certificates=certificates, **census,
               seeded_junction_trees=random_cases,
               triangle_defect_examples=defects, seed=20261116))
    print('PASS: exact arithmetic, integer bag reconstruction, and finite census.')
