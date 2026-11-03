#!/usr/bin/env python3
"""Deterministic exact checks of the new signed-line incidence interfaces.

The line generator here enumerates fixed/forward/reversed coordinate words,
independently of signed_incidence.line_sets.  Smith certificates are replayed
as elementary unimodular operations.  Finite checks do not prove asymptotic
prime supplies or a prescribed-pool permutation theorem.
"""

from copy import deepcopy
from itertools import product
from random import Random

import signed_incidence as si


def independent_lines(n):
    result = set()
    for word in product(range(n + 2), repeat=3):
        if max(word) < n:
            continue
        cells = []
        for t in range(n):
            x, y, z = [t if symbol == n else n - 1 - t if symbol == n + 1 else symbol
                       for symbol in word]
            cells.append(x * n * n + y * n + z)
        result.add(frozenset(cells))
    return result


def independent_face(n, a, b, sign, level):
    return frozenset(
        x * n * n + y * n + z
        for x, y, z in product(range(n), repeat=3)
        if (x, y, z)[3 - a - b] == level and
        (x, y, z)[b] == ((x, y, z)[a] if sign == 1 else n - 1 - (x, y, z)[a])
    )


def independent_body(n, sy, sz):
    return frozenset(
        x * n * n + y * n + z
        for x, y, z in product(range(n), repeat=3)
        if y == (x if sy == 1 else n - 1 - x) and
        z == (x if sz == 1 else n - 1 - x)
    )


def nonzero_image(values, edges):
    if isinstance(values, dict):
        out = {edge: sum(value for cell, value in values.items() if cell in edge)
               for edge in edges}
    else:
        out = {edge: sum(values[cell] for cell in edge) for edge in edges}
    return {edge: value for edge, value in out.items() if value}


def expect_value_error(function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except ValueError:
        return
    raise AssertionError("negative control was accepted")


def check_geometry_and_generators():
    face_checks = 0
    for n in (3, 5, 7, 9, 11, 13):
        independent = independent_lines(n)
        assert independent == set(si.line_sets(n).values())
        assert len(independent) == 3 * n * n + 6 * n + 4
        if n < 11:
            continue
        for a, b, sign in si.face_families():
            family_edges = [independent_face(n, a, b, sign, level) for level in range(n)]
            for u, v in product(range(n), repeat=2):
                if u == v:
                    continue
                pairs = si.face_cuboid(n, a, b, sign, u, v)
                values = si.cuboid(pairs, n)
                assert len(values) == 8 and set(values.values()) == {-1, 1}
                assert nonzero_image(values, independent) == {family_edges[u]: 1, family_edges[v]: -1}
                face_checks += 1
        for sy, sz in product((1, -1), repeat=2):
            values = si.apply_plan(n, si.pure_body_plan(n, sy, sz))
            assert nonzero_image(values, independent) == {independent_body(n, sy, sz): 1}
    expect_value_error(si.face_cuboid, 9, 0, 1, 1, 0, 1)
    expect_value_error(si.face_cuboid, 11, 0, 1, 1, 0.5, 1)
    expect_value_error(si.cuboid, ((0, 1), (0, 1), (0, 1.5)), 11)
    print(f"geometry: six independent orders; {face_checks} isolated face transfers; eight pure bodies")


def check_flows_and_corrections():
    n = 11
    complete = [(i, j) for i in range(n) for j in range(i + 1, n)]
    demand = [3] * 5 + [-3] * 5 + [0]
    result = si.integer_edge_flow(demand, complete, 1)
    assert max(map(abs, result)) <= 1
    path = [(i, i + 1) for i in range(4)]
    assert si.integer_edge_flow([3, 0, 0, 0, -3], path, 3) == [3] * 4
    expect_value_error(si.integer_edge_flow, [3, 0, 0, 0, -3], path, 2)
    expect_value_error(si.integer_edge_flow, [1, -1, 1, -1], [(0, 2), (1, 3)], 100)
    expect_value_error(si.integer_edge_flow, [1, -1], [(0, 0)], 1)
    rng = Random(20261102)
    targets = {key: 0 for key in si.extra_keys(n)}
    for a, b, sign in si.face_families():
        vector = [rng.randrange(-7, 8) for _ in range(n - 1)]
        vector.append(-sum(vector))
        for level, value in enumerate(vector):
            targets[("face", a, b, sign, level)] = value
    for sy, sz in product((1, -1), repeat=2):
        targets[("body", sy, sz)] = rng.randrange(-7, 8)
    bound = (max(abs(value) for key, value in targets.items() if key[0] == "face") +
             sum(abs(value) for key, value in targets.items() if key[0] == "body"))
    for graph, capacity in ((None, None), (complete, (bound + 4) // 5)):
        plan = si.extra_correction_plan(n, targets, graph, capacity)
        observed = si.line_sums(si.apply_plan(n, plan), n)
        assert {key: observed[key] for key in si.extra_keys(n)} == targets
        assert not any(value for key, value in observed.items() if key[0] == "axis")
        assert len(plan) <= 4 + 6 * (n - 1 if graph is None else len(graph))
        # The four body terms have their own exact coefficients. Every
        # remaining face term satisfies the stated path/graph coefficient bound.
        body_count = sum(bool(value) for key, value in targets.items() if key[0] == "body")
        face_bound = (n // 2) * bound if graph is None else capacity
        assert all(abs(coefficient) <= face_bound for coefficient, _ in plan[body_count:])
    print("capacity: path and bounded graph corrections; cut and malformed-graph negative controls")


def check_lifts_and_residues():
    n = 11
    rng = Random(110006)
    independent = independent_lines(n)
    for residue, modulus in ((0, 1), (1, 2), (5, 6)):
        source = [residue + modulus * rng.randrange(-4, 5) for _ in range(n ** 3)]
        targets = si.line_sums(source, n)
        # This makes the target differ from the supplied known preimage.
        targets[("body", 1, -1)] += 7 * modulus
        targets[("face", 0, 2, -1, 2)] += 3 * modulus
        targets[("face", 0, 2, -1, 9)] -= 3 * modulus
        assert si.compatible_targets(targets, n)
        lift = si.integer_full_lift(targets, n, residue, modulus)
        assert all(value % modulus == residue % modulus for value in lift)
        expected = {si.line_sets(n)[key]: value for key, value in targets.items() if value}
        assert nonzero_image(lift, independent) == expected
        changed = dict(targets)
        changed[("face", 1, 2, 1, 0)] += 1
        assert not si.compatible_targets(changed, n)
        expect_value_error(si.integer_full_lift, changed, n)
        if modulus > 1:
            changed = dict(targets)
            changed[("body", 1, 1)] += 1
            expect_value_error(si.integer_full_lift, changed, n, residue, modulus)
    for modulus in (2, 4, 6, 10, 30):
        demands = {key: 2 * rng.randrange(-15, 16) for key in si.extra_keys(n)}
        for a, b, sign in si.face_families():
            key = ("face", a, b, sign, n - 1)
            demands[key] = (-sum(demands[("face", a, b, sign, level)] for level in range(n - 1))
                            + modulus * rng.randrange(-3, 4))
        plan = si.residue_cuboid_plan(n, demands, modulus)
        assert all(0 < coefficient < modulus // 2 for coefficient, _ in plan)
        assert sum(coefficient for coefficient, _ in plan) <= (6 * n - 2) * (modulus // 2 - 1)
        observed = si.line_sums([2 * value for value in si.apply_plan(n, plan)], n)
        assert all((observed[key] - value) % modulus == 0 for key, value in demands.items())
        assert not any(value for key, value in observed.items() if key[0] == "axis")
    bad = {key: 0 for key in si.extra_keys(n)}
    bad[("body", 1, 1)] = 1
    expect_value_error(si.residue_cuboid_plan, n, bad, 6)
    bad[("body", 1, 1)] = 0
    bad[("face", 0, 1, 1, 0)] = 2
    expect_value_error(si.residue_cuboid_plan, n, bad, 6)
    print("lifts: unrestricted and mod2/mod6 entries; five even moduli; incompatible-target controls")


def independent_kernel_matrix(n, keys):
    center = n // 2
    endpoints = [i for i in range(n) if i != center]
    columns = []
    for i, j, k in product(endpoints, repeat=3):
        corners = []
        for bx, by, bz in product((0, 1), repeat=3):
            point = (center if bx else i, center if by else j, center if bz else k)
            corners.append((point, (-1) ** (bx + by + bz)))
        column = []
        for key in keys:
            value = 0
            for point, coefficient in corners:
                if key[0] == "face":
                    _, a, b, sign, level = key
                    hit = (point[3 - a - b] == level and
                           point[b] == (point[a] if sign == 1 else n - 1 - point[a]))
                else:
                    _, sy, sz = key
                    hit = (point[1] == (point[0] if sy == 1 else n - 1 - point[0]) and
                           point[2] == (point[0] if sz == 1 else n - 1 - point[0]))
                if hit:
                    value += coefficient
            column.append(value)
        columns.append(column)
    return [list(row) for row in zip(*columns)]


def n5_invariants(keys, target):
    values = dict(zip(keys, target))
    for a, b, sign in si.face_families():
        values[("face", a, b, sign, 2)] = -sum(
            values[("face", a, b, sign, level)] for level in (0, 1, 3, 4))
    body = sum(value for key, value in values.items() if key[0] == "body")
    center = sum(values[("face", a, b, sign, 2)] for a, b, sign in si.face_families())
    weighted = [sum((level - 2) ** 2 * values[("face", a, b, sign, level)]
                    for sign in (1, -1) for level in range(5))
                for a, b in ((0, 1), (0, 2), (1, 2))]
    return (body - 7 * center) % 15, (weighted[0] - weighted[1]) % 5, (weighted[0] - weighted[2]) % 5


def check_smith_and_small_orders():
    expected = {3: (8, [3, 3, 3, 6]), 5: (28, [5, 5, 15]),
                7: (40, []), 9: (52, []), 11: (64, [])}
    rng = Random(535375)
    summaries = []
    for n, (rank, factors) in expected.items():
        keys, matrix = si.axis_kernel_extra_matrix(n)
        assert matrix == independent_kernel_matrix(n, keys)
        certificate = si.smith_certificate(matrix)
        assert si.verify_smith_certificate(matrix, certificate)
        assert len(certificate["diagonal"]) == rank
        assert [x for x in certificate["diagonal"] if x != 1] == factors
        summaries.append((n, 3 * n * n - 3 * n + 1 + rank, factors))
        for column in (0, len(matrix[0]) // 2, len(matrix[0]) - 1):
            assert si.smith_image_membership([row[column] for row in matrix], certificate)
        broken = deepcopy(certificate)
        broken["diagonal"][0] += 1
        assert not si.verify_smith_certificate(matrix, broken)
        broken = deepcopy(certificate)
        broken["operations"].append(("ra", 0, 0, 1))
        assert not si.verify_smith_certificate(matrix, broken)
        if n != 5:
            continue
        for column in zip(*matrix):
            assert n5_invariants(keys, column) == (0, 0, 0)
        unit = [int(key == ("body", 1, 1)) for key in keys]
        assert not si.smith_image_membership(unit, certificate)
        assert si.smith_image_membership([15 * x for x in unit], certificate)
        # General finite targets: compare the three displayed congruences with
        # the independent transformed divisibility criterion.
        for _ in range(200):
            target = [rng.randrange(-8, 9) for _ in keys]
            assert si.smith_image_membership(target, certificate) == (n5_invariants(keys, target) == (0, 0, 0))
        # Deliberately project varied targets onto the congruence kernel, so
        # this check contains many actual positive membership cases.
        for _ in range(50):
            target = [rng.randrange(-8, 9) for _ in keys]
            _, wx, wy = n5_invariants(keys, target)
            target[keys.index(("face", 0, 2, 1, 3))] += wx
            target[keys.index(("face", 1, 2, 1, 3))] += wy
            remainder, _, _ = n5_invariants(keys, target)
            target[keys.index(("body", -1, -1))] -= remainder
            assert n5_invariants(keys, target) == (0, 0, 0)
            assert si.smith_image_membership(target, certificate)
    print(f"Smith replay (n, full rank, nonunit factors): {summaries}")
    print("order five: exact basis congruences; forbidden unit/allowed 15 body; 250 membership comparisons")


def check_prime_target_integration():
    from signed_targets_controls import produce, verify

    certificate = produce(11, 6)
    verify(certificate)
    by_edge = {frozenset(record["cells"]): record["target"]
               for record in certificate["line_targets"]}
    targets = {key: by_edge[edge] for key, edge in si.line_sets(11).items()}
    lift = si.integer_full_lift(targets, 11, entry_residue=1, entry_modulus=2)
    assert all(value % 2 for value in lift)
    assert sum(lift) == certificate["target_total"]
    assert nonzero_image(lift, independent_lines(11)) == by_edge
    print(f"prime-target integration: 433 exact sums; 1331 odd integer entries; total {sum(lift)}; numeric lift only")


def main():
    check_geometry_and_generators()
    check_flows_and_corrections()
    check_lifts_and_residues()
    check_smith_and_small_orders()
    check_prime_target_integration()
    print("All signed-incidence controls passed; no prescribed-pool permutation inferred.")


if __name__ == "__main__":
    main()
