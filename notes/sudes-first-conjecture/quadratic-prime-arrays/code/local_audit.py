#!/usr/bin/env python3
"""Exact finite controls for local_arithmetic.md; not a prime-array solver."""
from __future__ import annotations

import argparse
import itertools
import random


def square_lines(n: int):
    return ([[i * n + j for j in range(n)] for i in range(n)]
            + [[i * n + j for i in range(n)] for j in range(n)]
            + [[i * n + i for i in range(n)],
               [i * n + n - 1 - i for i in range(n)]])


def odd_residue_square(n: int, k: int) -> list[int]:
    """n odd; total number of ones is n*(n//2)+k, 1<=k<n."""
    if n < 3 or n % 2 != 1 or not 1 <= k < n:
        raise ValueError("outside the proved odd-square range")
    m = n // 2
    a = [[int(1 <= (j - i) % n <= m) for j in range(n)] for i in range(n)]
    q = next(t for t in (k, k - 1) if t % 3 != -n % 3)
    indices = [t for t in range(n) if t != m][:q]
    for t in indices:
        a[t][t] = 1
    if q < k:
        v = next(t for t in range(n) if t != m and t not in indices)
        i, j = (m, v) if not a[m][v] else (v, m)
        a[i][j] = 1
    return list(itertools.chain.from_iterable(a))


def residue_square(n: int, count: int) -> list[int]:
    """All n>=40, n^2/4<=count<=3n^2/4; zero-free mod3 line sums."""
    if n < 40 or not n * n <= 4 * count <= 3 * n * n:
        raise ValueError("outside the proved all-order range")
    r = n % 3
    width = r or 3
    size = n - width
    blocks = size // 3
    a = [[0] * n for _ in range(n)]
    protected: set[tuple[int, int]] = set()

    if r:
        for i in range(n):
            for j in range(n):
                if i >= size or j >= size:
                    a[i][j] = 1
        for i in range(size):
            j = n - 1 - i
            if 0 <= j < size:
                protected.add((i // 3, j // 3))
        for bi, bj in protected:
            for i in range(3 * bi, 3 * bi + 3):
                for j in range(3 * bj, 3 * bj + 3):
                    a[i][j] = 1
        base = sum(map(sum, a))
        choices = (0, 1, 3, 4) if r == 1 else (0, 2, 3, 5)
        h, g = next((h, g) for h in choices for g in choices
                    if (base - r * (h + g) - count) % 9 == 0)
        for i in range(r, r + h):
            for j in range(size, n):
                a[i][j] = 0
        for j in range(r, r + g):
            for i in range(size, n):
                a[i][j] = 0
    else:
        for i in range(size):
            pattern = (1, 1, 0) if i // 3 == 0 else (1, 0, 0)
            for j in range(3):
                a[i][size + j] = pattern[j]
                a[size + j][i] = pattern[j]
        for i, j in ((0, 0), (1, 2), (2, 1)):
            a[size + i][size + j] = 1
        base = sum(map(sum, a))
        extra, toggles = next((e, t) for e in range(3) for t in range(3)
                              if (base + e + 3 * t - count) % 9 == 0)
        for i, j in ((0, 1), (1, 0))[:extra]:
            a[size + i][size + j] = 1
        for group in range(1, toggles + 1):
            for i in range(3 * group, 3 * group + 3):
                a[i][size + 1] = 1

    base = sum(map(sum, a))
    if (count - base) % 9:
        raise AssertionError("bad residue template")
    needed = (count - base) // 9
    free = [(i, j) for i in range(blocks) for j in range(blocks)
            if (i, j) not in protected]
    if not 0 <= needed <= len(free):
        raise AssertionError("capacity invoice failed")
    for bi, bj in free[:needed]:
        for i in range(3 * bi, 3 * bi + 3):
            for j in range(3 * bj, 3 * bj + 3):
                a[i][j] = 1
    return list(itertools.chain.from_iterable(a))


def validate_square(a: list[int], n: int, count: int) -> None:
    assert len(a) == n * n and set(a) <= {0, 1} and sum(a) == count
    assert all((2 * sum(a[j] for j in line) - n) % 3
               for line in square_lines(n))


def repeated_direction(points: set[tuple[int, int]], axis: int, bound: int,
                       wanted: int) -> tuple[int, list[tuple[tuple[int, int], tuple[int, int]]]]:
    by_row: dict[int, list[int]] = {}
    for p in points:
        by_row.setdefault(p[1 - axis], []).append(p[axis])
    edges: dict[int, list[tuple[tuple[int, int], tuple[int, int]]]] = {}
    for row, values in by_row.items():
        values.sort()
        for x, y in zip(values, values[1:]):
            gap = y - x
            if gap <= bound:
                u = (x, row) if axis == 0 else (row, x)
                v = (y, row) if axis == 0 else (row, y)
                edges.setdefault(gap, []).append((u, v))
    for gap, candidate in sorted(edges.items(), key=lambda x: (-len(x[1]), x[0])):
        used = set()
        match = []
        # Sorting from the increasing-coordinate end yields maximum matching
        # on each fixed-gap path, unlike arbitrary-edge greedy matching.
        for u, v in sorted(candidate, key=lambda e: (e[0][1-axis], e[0][axis])):
            if u not in used and v not in used:
                used.update((u, v))
                match.append((u, v))
        if len(match) >= wanted:
            return gap, match[:wanted]
    if wanted == 0:
        return 1, []
    raise AssertionError("proved matching count not found")


def two_direction_seeds(points: set[tuple[int, int]], side: int):
    m = len(points)
    if m < 8 * side:
        raise ValueError("density hypothesis fails")
    bound = (8 * side * side + m - 1) // m
    wanted = m // (16 * bound)
    g1, h = repeated_direction(points, 0, bound, wanted)
    used = {p for pair in h for p in pair}
    g2, v = repeated_direction(points - used, 1, bound, wanted)
    assert all(p not in used for pair in v for p in pair)
    return (g1, g2), h, v


def self_test() -> None:
    count = 0
    for n in range(3, 50, 2):
        for k in range(1, n):
            a = odd_residue_square(n, k)
            validate_square(a, n, n * (n // 2) + k)
            count += 1
    for n in range(40, 85):
        lo = (n * n + 3) // 4
        hi = 3 * n * n // 4
        cases = set(range(lo, lo + 18)) | set(range(hi - 17, hi + 1))
        cases |= set(range(n * n // 2 - 9, n * n // 2 + 9))
        for k in sorted(cases):
            a = residue_square(n, k)
            validate_square(a, n, k)
            count += 1
    rng = random.Random(20261102)
    for side in (32, 48, 64):
        for _ in range(5):
            points = {(i, j) for i in range(side) for j in range(side)
                      if rng.randrange(4) != 0}
            (g1, g2), h, v = two_direction_seeds(points, side)
            for axis, gap, pairs in ((0, g1, h), (1, g2, v)):
                assert len({p for pair in pairs for p in pair}) == 2 * len(pairs)
                for x, y in pairs:
                    assert x in points and y in points
                    assert y[axis] - x[axis] == gap and x[1-axis] == y[1-axis]
            count += 1
    # All four routing identities use units, independently of the modulus.
    for ring, triples in (
        ("G", [((0, -1), (1, 0), (1, 1)), ((0, 1), (1, 0), (1, -1))]),
        ("E", [((0, 1), (1, 1), (1, 0)), ((1, 0), (1, 1), (0, 1))]),
    ):
        for u, v, delta in triples:
            norm = lambda z: z[0]**2 + z[1]**2 - (z[0]*z[1] if ring == "E" else 0)
            assert norm(u) == norm(v) == 1
            assert tuple(v[j] - u[j] for j in range(2)) == delta
            count += 1
    print(f"PASS {count} local controls; no prime-target or asymptotic controller claim")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    self_test()
