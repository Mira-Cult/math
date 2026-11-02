#!/usr/bin/env python3
"""Exact producer utilities for the frozen Gaussian and Eisenstein pools.

The checker deliberately imports none of this module. Integer arithmetic only.
"""
from __future__ import annotations

import itertools
import math


def rational_prime(p: int) -> bool:
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    return all(p % d for d in range(3, math.isqrt(p) + 1, 2))


def norm(z: tuple[int, int], ring: str) -> int:
    a, b = z
    return a * a + b * b if ring == "gaussian" else a * a - a * b + b * b


def element_prime(z: tuple[int, int], ring: str) -> bool:
    a, b = z
    q = norm(z, ring)
    if rational_prime(q):
        return True
    if ring == "gaussian":
        p = abs(a or b)
        return (a == 0 or b == 0) and p % 4 == 3 and rational_prime(p)
    if a == 0 or b == 0 or a == b:
        p = max(abs(a), abs(b))
        return p % 3 == 2 and rational_prime(p)
    return False


def canonical_pool(ring: str, count: int) -> list[tuple[int, int]]:
    if ring not in ("gaussian", "eisenstein") or count < 1:
        raise ValueError("invalid ring/count")
    bound = 16
    while True:
        result = []
        limit = 2 * math.isqrt(bound) + 2
        for a in range(1, limit + 1):
            for b in range(a if ring == "eisenstein" else math.isqrt(bound) + 1):
                z = (a, b)
                q = norm(z, ring)
                if q <= bound and q != (2 if ring == "gaussian" else 3) and element_prime(z, ring):
                    result.append(z)
        result.sort(key=lambda z: (norm(z, ring), z[0], z[1]))
        if len(result) >= count:
            return result[:count]
        bound *= 2


def full_lines(n: int, dimension: int) -> list[tuple[int, ...]]:
    """Build signed-coordinate lines, normalize to cell sets, deduplicate."""
    if n < 1 or dimension not in (2, 3):
        raise ValueError("invalid order/dimension")
    cells = list(itertools.product(range(n), repeat=dimension))
    lookup = {c: j for j, c in enumerate(cells)}
    lines = set()
    for pattern in itertools.product(range(n + 2), repeat=dimension):
        if all(x < n for x in pattern):
            continue
        line = []
        for t in range(n):
            coord = tuple(x if x < n else t if x == n else n - 1 - t for x in pattern)
            line.append(lookup[coord])
        lines.add(tuple(sorted(line)))
    return sorted(lines)


def primality_record(z: tuple[int, int], ring: str) -> dict:
    if not element_prime(z, ring):
        raise ValueError("not prime")
    q = norm(z, ring)
    if rational_prime(q):
        return {"kind": "rational-prime-norm", "rational_prime": q,
                "trial_division_through": math.isqrt(q)}
    p = math.isqrt(q)
    return {"kind": "inert-rational-associate", "rational_prime": p,
            "trial_division_through": math.isqrt(p)}


def certificate(ring: str, n: int, dimension: int, array: list[tuple[int, int]],
                provenance: dict) -> dict:
    pool = canonical_pool(ring, n ** dimension)
    if sorted(pool) != sorted(array):
        raise ValueError("wrong pool")
    result = {"format": "quadratic-prime-array-v1", "ring": ring, "n": n,
              "dimension": dimension, "family": "full-signed-coordinate-lines",
              "coordinates": list(map(list, itertools.product(range(n), repeat=dimension))),
              "pool": list(map(list, pool)), "array": list(map(list, array)),
              "provenance": provenance, "entry_primality": [], "lines": []}
    result["entry_primality"] = [primality_record(z, ring) for z in pool]
    for line in full_lines(n, dimension):
        z = tuple(sum(array[j][c] for j in line) for c in range(2))
        result["lines"].append({"cells": list(line), "sum": list(z),
                                "norm": norm(z, ring), "primality": primality_record(z, ring)})
    return result
