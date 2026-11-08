#!/usr/bin/env python3
"""Exact sparse Latin-completion permanent generator (Python 3.10+).

Input: a square JSON array, with null holes and integer symbols 0,...,n-1.
Output: a sparse matrix. Missing coordinates are zero; weights are strings
so that 1/2 remains exact. This constructs the matrix, not its permanent.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path

ALPHABET = frozenset((Fraction(-1), Fraction(0), Fraction(1, 2), Fraction(1)))


@dataclass
class Construction:
    order: int
    entries: dict[tuple[int, int], Fraction]
    metadata: dict

    def dense(self) -> list[list[Fraction]]:
        result = [[Fraction(0) for _ in range(self.order)] for _ in range(self.order)]
        for (i, j), value in self.entries.items():
            result[i][j] = value
        return result

    def as_json(self) -> dict:
        return {
            "order": self.order,
            "entries": [[i, j, str(value)] for (i, j), value in sorted(self.entries.items())],
            "metadata": self.metadata,
        }


def validate_grid(grid: list[list[int | None]]) -> None:
    """Reject malformed representations; contradictory in-range clues are valid inputs."""
    if not isinstance(grid, list) or not grid:
        raise ValueError("Expected a nonempty square array.")
    n = len(grid)
    if any(not isinstance(row, list) or len(row) != n for row in grid):
        raise ValueError("Expected a square array.")
    if any(value is not None and (type(value) is not int or not 0 <= value < n)
           for row in grid for value in row):
        raise ValueError("Symbols must be null or integers from 0 through n-1.")


def residual(grid: list[list[int | None]]) -> dict:
    """Compute all cell, row-symbol and column-symbol requirements from scratch."""
    n = len(grid)
    symbols = set(range(n))
    row_used = [{value for value in row if value is not None} for row in grid]
    col_used = [{grid[i][j] for i in range(n) if grid[i][j] is not None} for j in range(n)]
    if any(len(row_used[i]) != sum(value is not None for value in grid[i]) for i in range(n)):
        return {"contradiction": "duplicate row clue"}
    if any(len(col_used[j]) != sum(grid[i][j] is not None for i in range(n)) for j in range(n)):
        return {"contradiction": "duplicate column clue"}
    cells = [(i, j) for i in range(n) for j in range(n) if grid[i][j] is None]
    row_slots = [(i, k) for i in range(n) for k in sorted(symbols - row_used[i])]
    col_slots = [(j, k) for j in range(n) for k in sorted(symbols - col_used[j])]
    candidates = {(i, j): sorted(symbols - row_used[i] - col_used[j]) for i, j in cells}
    if any(not values for values in candidates.values()):
        return {"contradiction": "empty cell requirement"}
    row_support = {(i, k) for (i, j), values in candidates.items() for k in values}
    col_support = {(j, k) for (i, j), values in candidates.items() for k in values}
    if any(slot not in row_support for slot in row_slots):
        return {"contradiction": "empty row-symbol requirement"}
    if any(slot not in col_support for slot in col_slots):
        return {"contradiction": "empty column-symbol requirement"}
    assert len(cells) == len(row_slots) == len(col_slots)
    return {"cells": cells, "row_slots": row_slots, "col_slots": col_slots,
            "candidates": candidates}


def construct(grid: list[list[int | None]]) -> Construction:
    """Return M with per(M) equal to the labeled Latin completion count."""
    validate_grid(grid)
    work = [row[:] for row in grid]
    forced = []
    original_holes = sum(value is None for row in grid for value in row)
    while True:
        state = residual(work)
        if "contradiction" in state:
            return Construction(1, {}, {"outcome": "zero", "reason": state["contradiction"],
                                       "original_holes": original_holes, "forced": forced})
        if not state["cells"]:
            return Construction(1, {(0, 0): Fraction(1)},
                                {"outcome": "one", "h": 0, "t": 0,
                                 "original_holes": original_holes, "forced": forced})
        singleton = next(((i, j, values[0]) for (i, j), values in state["candidates"].items()
                          if len(values) == 1), None)
        if singleton is None:
            break
        i, j, k = singleton
        work[i][j] = k
        forced.append([i, j, k])

    h = len(state["cells"])
    t = sum(len(values) for values in state["candidates"].values())
    row_index = {slot: index for index, slot in enumerate(state["row_slots"])}
    col_index = {slot: index for index, slot in enumerate(state["col_slots"])}
    entries = {}

    def put(i: int, j: int, value: int | Fraction) -> None:
        assert (i, j) not in entries, "Unexpected overlapping entries"
        entries[i, j] = Fraction(value)

    offset = h
    blocks = []
    for (i, j), values in state["candidates"].items():
        q = len(values)
        assert q >= 2
        blocks.append({"cell": [i, j], "symbols": values, "offset": offset})
        for a, k in enumerate(values):
            b = (a + 1) % q
            sign = 1 if a < q - 1 else -1
            # Internal D_q = I_q + P_q.
            put(offset + a, offset + a, 1)
            put(offset + a, offset + b, sign)
            # External row to internal column: B_q = I_q - P_q.
            put(row_index[i, k], offset + a, 1)
            put(row_index[i, k], offset + b, -sign)
            # Internal row to external column with the same symbol label.
            put(offset + a, col_index[j, k], 1)
        offset += q
    assert offset == h + t
    for index in range(h):
        put(offset + index, offset + index, Fraction(1, 2))
    assert len(entries) == 5 * t + h
    assert sum(value == 1 for value in entries.values()) == 4 * t
    assert sum(value == -1 for value in entries.values()) == t
    assert sum(value == Fraction(1, 2) for value in entries.values()) == h
    assert set(entries.values()) <= ALPHABET
    return Construction(t + 2 * h, entries,
                        {"outcome": "residual", "h": h, "t": t,
                         "original_holes": original_holes, "forced": forced,
                         "external_rows": [list(slot) for slot in state["row_slots"]],
                         "external_columns": [list(slot) for slot in state["col_slots"]],
                         "blocks": blocks})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON square, null for holes, symbols 0,...,n-1")
    args = parser.parse_args()
    print(json.dumps(construct(json.loads(args.input.read_text())).as_json(), indent=2))


if __name__ == "__main__":
    main()
