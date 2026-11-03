#!/usr/bin/env python3
"""Exact finite controls for controller.md's integral tensor correction.

This checks the new correction of a bounded zero-margin integer residual,
after the real tensor solution has been rounded. It does not numerically
approximate the spectral right inverse or prove a prime-array theorem.
Only Python's standard library is used. The seed and inputs are reproducible.
"""

from __future__ import annotations

import argparse
from collections import deque
from fractions import Fraction
from hashlib import sha256
import json
from math import ceil
from random import Random


def integral_flow(n: int, edges: list[tuple[int, int]],
                  demand: list[int], expansion: Fraction) -> list[int]:
    """Find the capacity-bounded integral flow promised by Lemma IF.

    Divergence is positive at an oriented edge's first endpoint. The calling
    control uses complete graphs, whose expansion is at least n/2. The
    algorithm itself detects an infeasible cut instead of assuming success.
    """
    if len(demand) != n or sum(demand) != 0:
        raise ValueError("flow demand does not have total zero")
    cap = ceil(Fraction(max(map(abs, demand), default=0), 1) / expansion)
    source, sink = n, n + 1
    adjacency: list[list[list[int]]] = [[] for _ in range(n + 2)]

    def add_arc(a: int, b: int, capacity: int) -> int:
        index = len(adjacency[a])
        adjacency[a].append([b, capacity, len(adjacency[b])])
        adjacency[b].append([a, 0, index])
        return index

    references = []
    for a, b in edges:
        references.append((a, add_arc(a, b, cap), b, add_arc(b, a, cap)))
    target = 0
    for vertex, amount in enumerate(demand):
        if amount > 0:
            add_arc(source, vertex, amount)
            target += amount
        elif amount < 0:
            add_arc(vertex, sink, -amount)

    attained = 0
    while attained < target:
        parent: list[tuple[int, int] | None] = [None] * (n + 2)
        parent[source] = (-1, -1)
        queue = deque([source])
        while queue and parent[sink] is None:
            a = queue.popleft()
            for index, (b, residual_capacity, _) in enumerate(adjacency[a]):
                if residual_capacity > 0 and parent[b] is None:
                    parent[b] = (a, index)
                    queue.append(b)
        if parent[sink] is None:
            raise ValueError("a cut has insufficient flow capacity")
        augment = target - attained
        b = sink
        while b != source:
            entry = parent[b]
            assert entry is not None
            a, index = entry
            augment = min(augment, adjacency[a][index][1])
            b = a
        b = sink
        while b != source:
            entry = parent[b]
            assert entry is not None
            a, index = entry
            edge = adjacency[a][index]
            edge[1] -= augment
            adjacency[b][edge[2]][1] += augment
            b = a
        attained += augment

    flow = [(cap - adjacency[a][j][1]) - (cap - adjacency[b][k][1])
            for a, j, b, k in references]
    divergence = [0] * n
    for (a, b), amount in zip(edges, flow):
        divergence[a] += amount
        divergence[b] -= amount
    if divergence != demand or any(abs(x) > cap for x in flow):
        raise AssertionError("flow output failed exact divergence/capacity replay")
    return flow


def check_margins(matrix: list[list[int]]) -> int:
    n = len(matrix)
    if n < 2 or any(len(row) != n for row in matrix):
        raise ValueError("residual is not an n by n matrix with n at least two")
    if any(sum(row) != 0 for row in matrix):
        raise ValueError("residual row margin is nonzero")
    if any(sum(matrix[i][j] for i in range(n)) != 0 for j in range(n)):
        raise ValueError("residual column margin is nonzero")
    return n


def correct_residual(matrix: list[list[int]], edges: list[tuple[int, int]],
                     expansion: Fraction) -> tuple[list[list[int]], int]:
    """Apply both integer flow stages and return the proved coefficient cap."""
    n = check_margins(matrix)
    delta = max(abs(x) for row in matrix for x in row)
    first_cap = ceil(Fraction(delta, 1) / expansion)
    columns = [integral_flow(n, edges, [matrix[i][j] for i in range(n)],
                             expansion) for j in range(n)]
    intermediate = [[columns[j][edge] for j in range(n)]
                    for edge in range(len(edges))]
    for row in intermediate:
        # The subtracted vector is a circulation, since the residual has
        # zero row sums. This is the exact, explicitly paid anchoring step.
        row[-1] -= sum(row)
    if any(sum(row) != 0 for row in intermediate):
        raise AssertionError("anchored intermediate has a nonzero row sum")
    if any(abs(x) > (n - 1) * first_cap
           for row in intermediate for x in row):
        raise AssertionError("anchored intermediate exceeds its proved cap")
    correction = [integral_flow(n, edges, row, expansion)
                  for row in intermediate]
    cap = ceil(Fraction((n - 1) * first_cap, 1) / expansion)
    return correction, cap


def independent_replay(matrix: list[list[int]], edges: list[tuple[int, int]],
                       correction: list[list[int]], cap: int) -> None:
    """Recompute B C B^T without using the flow's intermediate variables."""
    n, m = len(matrix), len(edges)
    if len(correction) != m or any(len(row) != m for row in correction):
        raise ValueError("correction shape does not match the edge product")
    if any(abs(x) > cap for row in correction for x in row):
        raise ValueError("correction exceeds its stated coefficient cap")
    left = [[0] * m for _ in range(n)]
    for edge, (a, b) in enumerate(edges):
        for f, value in enumerate(correction[edge]):
            left[a][f] += value
            left[b][f] -= value
    result = [[0] * n for _ in range(n)]
    for i, row in enumerate(left):
        for f, (a, b) in enumerate(edges):
            result[i][a] += row[f]
            result[i][b] -= row[f]
    if result != matrix:
        raise ValueError("independent tensor replay leaves a nonzero residual")


def make_residual(n: int, rng: Random) -> list[list[int]]:
    """Generate a bounded integer residual with exact zero margins.

    Rejection enforces the rounded-tensor bound Delta^2/2, using the actual
    complete-graph maximum degree Delta=n-1. Finite random trials are only
    test input generation, not evidence that this rejection always succeeds.
    """
    bound = (n - 1) ** 2 // 2
    for _ in range(10000):
        matrix = [[rng.randrange(-1, 2) for _ in range(n - 1)]
                  for _ in range(n - 1)]
        for row in matrix:
            row.append(-sum(row))
        matrix.append([-sum(matrix[i][j] for i in range(n - 1))
                       for j in range(n)])
        if max(abs(x) for row in matrix for x in row) <= bound:
            return matrix
    raise RuntimeError("finite input-generation budget exhausted")


def rejects(action) -> None:
    try:
        action()
    except ValueError:
        return
    raise AssertionError("negative control was accepted")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20261102)
    parser.add_argument("--cases", type=int, default=12)
    parser.add_argument("--min-order", type=int, default=3)
    parser.add_argument("--max-order", type=int, default=18)
    args = parser.parse_args()
    if args.cases < 1 or not 3 <= args.min_order <= args.max_order:
        parser.error("positive case count and 3 <= min-order <= max-order required")
    rng = Random(args.seed)
    digest = sha256()
    count = 0
    first_fixture = None
    for n in range(args.min_order, args.max_order + 1):
        edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
        # A size-s cut in K_n has s(n-s) edges. For s <= n/2 this
        # is at least (n/2)s, giving this exact certified lower bound.
        expansion = Fraction(n, 2)
        degree = n - 1
        uniform_cap = ceil(Fraction((n - 1)
                                   * ceil(Fraction(degree * degree, 2) / expansion),
                                   1) / expansion)
        for _ in range(args.cases):
            matrix = make_residual(n, rng)
            correction, cap = correct_residual(matrix, edges, expansion)
            independent_replay(matrix, edges, correction, cap)
            if cap > uniform_cap:
                raise AssertionError("correction cap exceeds Theorem IT's cap")
            digest.update(json.dumps([matrix, correction, cap],
                                     separators=(",", ":")).encode())
            count += 1
            if first_fixture is None:
                first_fixture = (matrix, edges, expansion, correction, cap)

    assert first_fixture is not None
    matrix, edges, expansion, correction, cap = first_fixture
    bad_row = [row[:] for row in matrix]
    bad_row[0][0] += 1
    bad_row[1][0] -= 1
    rejects(lambda: correct_residual(bad_row, edges, expansion))
    bad_column = [row[:] for row in matrix]
    bad_column[0][0] += 1
    bad_column[0][1] -= 1
    rejects(lambda: correct_residual(bad_column, edges, expansion))
    bad_residual = [row[:] for row in matrix]
    for i, j, value in [(0, 0, 1), (0, 1, -1), (1, 0, -1), (1, 1, 1)]:
        bad_residual[i][j] += value
    rejects(lambda: independent_replay(bad_residual, edges, correction, cap))
    bad_correction = [row[:] for row in correction]
    bad_correction[0][0] += 1
    rejects(lambda: independent_replay(matrix, edges, bad_correction, cap + 1))
    print(json.dumps({"exact_tensor_corrections": count,
                      "orders": [args.min_order, args.max_order],
                      "seed": args.seed,
                      "negative_controls_rejected": 4,
                      "fixture_sha256": digest.hexdigest(),
                      "status": "all exact identities and capacity bounds passed",
                      "scope": "bounded residual correction, not the analytic theorem"},
                     sort_keys=True))


if __name__ == "__main__":
    main()
