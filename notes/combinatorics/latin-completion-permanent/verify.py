#!/usr/bin/env python3
"""Exact finite checks, independent Latin enumeration and generic permanents.

Run from any directory. Python 3.10+, standard library only. Prints JSON;
--output FILE also writes the same reproducible report (no timings).
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product
import json
from pathlib import Path
import random

from construct import ALPHABET, construct


def permanent(matrix):
    """Generic exact column-subset recursion; no Latin/gadget identities used."""
    n = len(matrix)
    assert all(len(row) == n for row in matrix)
    rows = sorted((tuple((j, value) for j, value in enumerate(row) if value)
                   for row in matrix), key=len)

    @lru_cache(None)
    def visit(i, occupied):
        if i == n:
            return Fraction(1)
        return sum((value * visit(i + 1, occupied | (1 << j))
                    for j, value in rows[i] if not occupied & (1 << j)), Fraction(0))

    return visit(0, 0)


def ryser(matrix):
    """Second generic exact algorithm, used on matrices of order at most 16."""
    n = len(matrix)
    total = Fraction(0)
    for mask in range(1 << n):
        term = Fraction(1)
        for row in matrix:
            term *= sum((row[j] for j in range(n) if mask & (1 << j)), Fraction(0))
            if not term:
                break
        total += (-1 if (n - mask.bit_count()) % 2 else 1) * term
    return total


@lru_cache(None)
def all_latin(n):
    """Enumerate row permutations and filter columns, independently of the compiler."""
    complete = []
    rows = []
    choices = tuple(permutations(range(n)))

    def visit():
        if len(rows) == n:
            complete.append(tuple(rows))
            return
        for row in choices:
            if all(row[j] not in {previous[j] for previous in rows} for j in range(n)):
                rows.append(row)
                visit()
                rows.pop()

    visit()
    return tuple(complete)


def completion_count(grid):
    return sum(all(value is None or square[i][j] == value
                   for i, row in enumerate(grid) for j, value in enumerate(row))
               for square in all_latin(len(grid)))


def cyclic(q):
    p = [[Fraction(0) for _ in range(q)] for _ in range(q)]
    for a in range(q):
        p[a][(a + 1) % q] = 1 if a < q - 1 else -1
    d = [[int(a == b) + p[a][b] for b in range(q)] for a in range(q)]
    b = [[int(a == c) - p[a][c] for c in range(q)] for a in range(q)]
    return p, d, b


def multiply(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def run():
    report = {"arithmetic": "exact integers and fractions", "schema_version": 1}
    for q in range(1, 9):
        p, d, b = cyclic(q)
        h = [[permanent([[d[i][j] for j in range(q) if j != s]
                         for i in range(q) if i != t]) for t in range(q)] for s in range(q)]
        identity = [[Fraction(a == c) for c in range(q)] for a in range(q)]
        powers = [[Fraction(0) for _ in range(q)] for _ in range(q)]
        power = identity
        for _ in range(q):
            powers = [[powers[a][c] + power[a][c] for c in range(q)] for a in range(q)]
            power = multiply(power, p)
        assert permanent(d) == 0
        assert h == powers
        assert multiply(b, h) == [[2 * x for x in row] for row in identity]
        assert power == [[-x for x in row] for row in identity]
    report["cyclic_identity_q_1_through_8"] = "passed"

    cache = {}
    comparisons = 0

    def check(grid):
        nonlocal comparisons
        result = construct(grid)
        assert set(result.entries.values()) <= ALPHABET
        assert all(0 <= i < result.order and 0 <= j < result.order for i, j in result.entries)
        assert all(result.entries.values())
        meta = result.metadata
        if meta["outcome"] == "residual":
            h, t = meta["h"], meta["t"]
            assert result.order == t + 2 * h
            assert len(result.entries) == 5 * t + h
            assert sum(v == 1 for v in result.entries.values()) == 4 * t
            assert all(len(block["symbols"]) >= 2 for block in meta["blocks"])
        key = result.order, tuple(sorted(result.entries.items()))
        if key not in cache:
            cache[key] = permanent(result.dense())
        count = completion_count(grid)
        assert cache[key] == count, (grid, result.as_json(), cache[key], count)
        comparisons += 1
        return {"count": count, "matrix_order": result.order,
                "nonzeros": len(result.entries), "outcome": meta["outcome"],
                **({"h": meta["h"], "t": meta["t"]} if "h" in meta else {})}

    exhaustive = []
    for n in (1, 2):
        cases = 0
        for values in product((None, *range(n)), repeat=n * n):
            grid = [list(values[i * n:(i + 1) * n]) for i in range(n)]
            check(grid)
            cases += 1
        exhaustive.append({"n": n, "grids": cases})
    report["exhaustive_grids"] = exhaustive

    examples = {
        "complete_order_one": [[0]],
        "empty_order_one": [[None]],
        "duplicate_row_clues": [[0, 0], [None, None]],
        "duplicate_column_clues": [[0, None], [0, None]],
        "consistent_but_infeasible": [[0, None], [None, 1]],
        "singleton_chain": [[0, None], [None, None]],
        "empty_order_two": [[None, None], [None, None]],
        "two_missing_order_three_rows": [[0, 1, 2], [None] * 3, [None] * 3],
        "order_four_intercalate": [[None, None, 2, 3], [None, None, 3, 2],
                                    [2, 3, 0, 1], [3, 2, 1, 0]],
    }
    report["examples"] = {name: check(grid) for name, grid in examples.items()}
    for name in ("empty_order_two", "order_four_intercalate"):
        result = construct(examples[name])
        assert ryser(result.dense()) == report["examples"][name]["count"]
    report["second_permanent_algorithm"] = {"algorithm": "Ryser inclusion-exclusion",
                                            "cases": ["empty_order_two", "order_four_intercalate"]}

    # Every erasure pattern of a fixed order-three square is considered.
    # Large matrices are explicitly excluded from generic permanent evaluation.
    square = [[(i + j) % 3 for j in range(3)] for i in range(3)]
    evaluated = skipped = 0
    for mask in range(1 << 9):
        grid = [[square[i][j] if mask & (1 << (3 * i + j)) else None
                 for j in range(3)] for i in range(3)]
        if construct(grid).order > 28:
            skipped += 1
            continue
        check(grid)
        evaluated += 1
    report["order_three_erasures"] = {"considered": 512, "evaluated": evaluated,
                                      "not_evaluated_above_order_28": skipped}

    rng = random.Random(20261108)
    tested = skipped = 0
    for n in (3, 4):
        for _ in range(120):
            grid = [[None if rng.random() < 0.55 else rng.randrange(n)
                     for _ in range(n)] for _ in range(n)]
            if construct(grid).order > 28:
                skipped += 1
                continue
            check(grid)
            tested += 1
    report["seeded_random_grids"] = {"seed": 20261108, "considered": 240,
                                     "evaluated": tested, "not_evaluated_above_order_28": skipped}
    empty_three = construct([[None] * 3 for _ in range(3)])
    assert (empty_three.order, len(empty_three.entries)) == (45, 144)
    report["empty_order_three"] = {"matrix_order": 45, "nonzeros": 144,
                                   "independent_latin_count": len(all_latin(3)),
                                   "permanent_evaluated": False}

    invalid = [[], [[None, None]], [[0], [0]], [[1]], [[-1]], [[True]], [[0.0]], [["0"]]]
    for grid in invalid:
        try:
            construct(grid)
        except ValueError:
            pass
        else:
            raise AssertionError(("Invalid input accepted", grid))
    report["malformed_inputs_rejected"] = len(invalid)
    report["completion_permanent_comparisons"] = comparisons
    report["distinct_matrices_evaluated"] = len(cache)
    report["independent_latin_enumeration"] = {str(n): len(all_latin(n)) for n in (1, 2, 3, 4)}
    report["status"] = "passed"
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(run(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
