#!/usr/bin/env python3
"""Exact finite controls for hyper4_axis.md, not prime-hypercube certificates.

The physical fixture is a permutation of the exact first n**4 odd primes.
It checks actual grouped-pair swaps and every full signed-line effect. Its
target sums are not asserted prime. The separate numeric tests check the five
preservation passes and integral tensor rounding; they are explicitly not
physical-permutation certificates.

Run: python3 -B code/hyper4_axis_controls.py
Optional recovery artifact: --certificate PATH (JSON, independently replayable
with --verify PATH). No third-party packages are required.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
import math
import random
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

from incidence import _inverse, _tree_inverse, graph_incidence


def integer(value):
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError("exact integer required")
    return value


def flat(point, n):
    answer = 0
    for value in point:
        answer = answer * n + value
    return answer


def unflat(value, n, dimension=4):
    point = [0] * dimension
    for axis in reversed(range(dimension)):
        point[axis], value = value % n, value // n
    return tuple(point)


def full_lines(n):
    """Producer: subsets of varying coordinates, first sign normalized."""
    if n == 1:
        return [tuple([0])]
    result = []
    for rank in range(1, 5):
        for axes in itertools.combinations(range(4), rank):
            fixed_axes = tuple(axis for axis in range(4) if axis not in axes)
            for signs in itertools.product((1, -1), repeat=rank - 1):
                for fixed in itertools.product(range(n), repeat=4 - rank):
                    edge = []
                    for t in range(n):
                        point = [0] * 4
                        for axis, value in zip(fixed_axes, fixed):
                            point[axis] = value
                        for axis, sign in zip(axes, (1,) + signs):
                            point[axis] = t if sign == 1 else n - 1 - t
                        edge.append(flat(point, n))
                    result.append(tuple(sorted(edge)))
    if len(result) != len(set(result)):
        raise AssertionError("producer created a duplicate full line")
    return sorted(result)


def independent_full_lines(n):
    """Checker: all four coordinate words, fixed / forward / reflected."""
    choices = list(range(n)) + ["t", "r"]
    edges = set()
    for word in itertools.product(choices, repeat=4):
        if not any(value in ("t", "r") for value in word):
            continue
        cells = []
        for t in range(n):
            point = tuple(t if value == "t" else n - 1 - t if value == "r" else value for value in word)
            cells.append(flat(point, n))
        edges.add(tuple(sorted(set(cells))))
    return sorted(edges)


def varying_axes(line, n):
    points = [unflat(cell, n) for cell in line]
    return tuple(axis for axis in range(4) if len({point[axis] for point in points}) > 1)


def sieve_pool(count):
    bound = max(64, count * 20)
    while True:
        bits = bytearray(b"\1") * (bound + 1)
        bits[:2] = b"\0\0"
        for p in range(2, math.isqrt(bound) + 1):
            if bits[p]:
                bits[p * p : bound + 1 : p] = b"\0" * (((bound - p * p) // p) + 1)
        values = [p for p in range(3, bound + 1, 2) if bits[p]]
        if len(values) >= count:
            return values[:count]
        bound *= 2


def independent_trial_pool(count):
    primes = [2]
    candidate = 3
    while len(primes) <= count:
        good = True
        for prime in primes:
            if prime * prime > candidate:
                break
            if candidate % prime == 0:
                good = False
                break
        if good:
            primes.append(candidate)
        candidate += 2
    return primes[1:]


def orbit(value, n):
    return min(value, n - 1 - value)


def stage_cells(stage, n):
    axes = tuple(stage["axes"])
    pairs = stage["endpoints"]
    point = tuple(stage["point"])
    if len(point) != 4 or len(axes) != len(pairs) or len(set(axes)) != len(axes):
        raise ValueError("malformed stage shape")
    if any(not 0 <= integer(axis) < 4 for axis in axes):
        raise ValueError("axis out of range")
    if any(not 0 <= integer(value) < n for value in point):
        raise ValueError("coordinate out of range")
    for pair in pairs:
        if len(pair) != 2 or pair[0] == pair[1] or any(not 0 <= integer(v) < n for v in pair):
            raise ValueError("distinct valid endpoints required")
    cells = {}
    for bits in itertools.product((0, 1), repeat=len(axes)):
        vertex = list(point)
        for axis, pair, bit in zip(axes, pairs, bits):
            vertex[axis] = pair[bit]
        cells[flat(vertex, n)] = (-1) ** sum(bits)
    if len(cells) != 2 ** len(axes):
        raise ValueError("hidden within-stage support collision")
    return cells


def free_axes(stage):
    level, axes = stage["level"], tuple(stage["axes"])
    allowed = {0: {(3,)}, 1: {(2,)}, 2: {(0,), (1,)}, 3: {(0, 1)}, 4: {(0, 1, 2)}}
    if level not in allowed or axes not in allowed[level]:
        raise ValueError("shape does not implement its claimed correction level")
    if level == 0:
        return (0, 1, 2)
    if level == 1:
        return (0, 1)
    if level == 2:
        return (1,) if axes == (0,) else (0,)
    return (2,) if level == 3 else (3,)


def legal_orbits(stage, n):
    free = free_axes(stage)
    axes = tuple(stage["axes"])
    native = {orbit(value, n) for pair in stage["endpoints"] for value in pair}
    forbidden = native | {orbit(stage["point"][axis], n) for axis in range(4) if axis not in free and axis not in axes}
    chosen = [orbit(stage["point"][axis], n) for axis in free]
    if any(value in forbidden for value in chosen) or len(set(chosen)) != len(chosen):
        return False
    return stage["level"] > 1 or all(value != n // 2 for value in chosen)


def pack_fixture(n=11, length=3):
    """A small mixed fixture, not the asymptotic degree-64 packing algorithm."""
    if n != 11 or length > 3:
        raise ValueError("the recorded recovery fixture uses n=11 and length<=3")
    specifications = [
        (0, (3,), ((0, 10),), (0, 0, 0, 0)),
        (1, (2,), ((0, 10),), (0, 0, 0, 7)),
        (2, (0,), ((0, 1),), (0, 0, 5, 6)),
        (2, (1,), ((0, 1),), (0, 0, 6, 5)),
        (3, (0, 1), ((0, 1), (0, 2)), (0, 0, 0, 8)),
        (4, (0, 1, 2), ((0, 1), (0, 2), (0, 3)), (0, 0, 0, 0)),
    ]
    used, stages = set(), []
    for bundle, (level, axes, endpoints, point) in enumerate(specifications):
        template = {"level": level, "axes": list(axes), "endpoints": [list(p) for p in endpoints], "point": list(point), "bundle": bundle}
        free = free_axes(template)
        seen = {axis: set() for axis in free}
        for stage_number in range(length):
            found = False
            for values in itertools.product(range(n), repeat=len(free)):
                if any(value in seen[axis] for axis, value in zip(free, values)):
                    continue
                stage = copy.deepcopy(template)
                for axis, value in zip(free, values):
                    stage["point"][axis] = value
                if not legal_orbits(stage, n):
                    continue
                cells = set(stage_cells(stage, n))
                if cells & used:
                    continue
                stage["stage_number"] = stage_number
                stages.append(stage)
                used.update(cells)
                for axis, value in zip(free, values):
                    seen[axis].add(value)
                found = True
                break
            if not found:
                raise AssertionError("finite fixture packing exhausted")
    return {"n": n, "stages": stages}


def verify_geometry(geometry, lines=None):
    n = integer(geometry["n"])
    if n < 3 or n % 2 == 0:
        raise ValueError("odd order at least three required")
    lines = independent_full_lines(n) if lines is None else lines
    line_sets = [(set(line), varying_axes(line, n)) for line in lines]
    used, bundles = set(), defaultdict(list)
    for stage in geometry["stages"]:
        cells = set(stage_cells(stage, n))
        if used & cells:
            raise ValueError("different stages share a support cell")
        if not legal_orbits(stage, n):
            raise ValueError("orbit avoidance restriction violated")
        used.update(cells)
        bundles[stage["bundle"]].append((stage, cells))
        for line, axes in line_sets:
            if len(axes) == 4 and cells & line:
                raise ValueError("axis stage touches a protected full diagonal")
    maximum_intersection = 0
    for stages in bundles.values():
        template = stages[0][0]
        for stage, _ in stages:
            if stage["level"] != template["level"] or stage["axes"] != template["axes"] or stage["endpoints"] != template["endpoints"]:
                raise ValueError("inconsistent reservoir type")
        for axis in free_axes(template):
            labels = [stage["point"][axis] for stage, _ in stages]
            if len(labels) != len(set(labels)):
                raise ValueError("whole-reservoir transverse label is reused")
        for line, axes in line_sets:
            if len(axes) < 2:
                continue
            hits = [len(line & cells) for _, cells in stages]
            if sum(value > 0 for value in hits) > 1 or sum(hits) > 2:
                raise ValueError("whole-reservoir extra-line range contract fails")
            maximum_intersection = max(maximum_intersection, sum(hits))
    return {"stage_count": len(geometry["stages"]), "bundle_count": len(bundles), "reserved_cells": len(used), "maximum_extra_bundle_intersection": maximum_intersection}


def make_certificate():
    geometry = pack_fixture()
    n = geometry["n"]
    pool = sieve_pool(n**4)
    available = set(pool)
    gap = 6
    pairs = []
    for p in pool:
        if p % gap == 1 and p in available and p + gap in available:
            pairs.append((p, p + gap))
            available.remove(p)
            available.remove(p + gap)
    required = sum(2 ** (len(stage["axes"]) - 1) for stage in geometry["stages"])
    if len(pairs) < required:
        raise AssertionError("finite exact pool lacks the requested pair matching")
    chosen = iter(pairs[:required])
    values = [None] * n**4
    used_primes = set()
    for stage in geometry["stages"]:
        stage["gap"] = gap
        stage["switches"] = []
        axes = stage["axes"]
        for bits in itertools.product((0, 1), repeat=len(axes) - 1):
            low, high = next(chosen)
            used_primes.update((low, high))
            vertices = []
            for final_bit in (0, 1):
                point = list(stage["point"])
                for axis, endpoints, bit in zip(axes, stage["endpoints"], bits + (final_bit,)):
                    point[axis] = endpoints[bit]
                vertices.append(flat(point, n))
            first, second = vertices
            values[first], values[second] = (low, high) if sum(bits) % 2 == 0 else (high, low)
            stage["switches"].append(vertices)
    remaining = iter(p for p in pool if p not in used_primes)
    for index, value in enumerate(values):
        if value is None:
            values[index] = next(remaining)
    return {"kind": "physical-axis-controller-control-not-prime-arrangement", "version": 1, "n": n, "entry_order": "lexicographic", "initial_values": values, "declared_lines": [list(line) for line in full_lines(n)], "stages": geometry["stages"]}


def verify_certificate(certificate):
    if certificate.get("kind") != "physical-axis-controller-control-not-prime-arrangement" or certificate.get("version") != 1:
        raise ValueError("unrecognized controller certificate")
    n = integer(certificate["n"])
    if certificate.get("entry_order") != "lexicographic":
        raise ValueError("lexicographic entry order required")
    values = certificate["initial_values"]
    if len(values) != n**4 or any(isinstance(value, bool) or not isinstance(value, int) for value in values):
        raise ValueError("invalid entry array")
    expected_pool = independent_trial_pool(n**4)
    if sorted(values) != expected_pool:
        raise ValueError("the exact prescribed odd prime pool must occur once")
    independent = independent_full_lines(n)
    declared = [tuple(line) for line in certificate["declared_lines"]]
    if any(list(line) != sorted(set(line)) for line in declared) or len(declared) != len(set(declared)) or sorted(declared) != independent:
        raise ValueError("omitted, duplicated, or incorrect full signed line")
    geometry_summary = verify_geometry(certificate, independent)
    endpoints_used = set()
    for stage in certificate["stages"]:
        delta = {cell: coefficient * integer(stage["gap"]) for cell, coefficient in stage_cells(stage, n).items()}
        if stage["gap"] <= 0 or stage["gap"] % 2:
            raise ValueError("positive even actual gap required")
        observed = {}
        if len(stage["switches"]) != 2 ** (len(stage["axes"]) - 1):
            raise ValueError("wrong equal-gap pair multiplicity")
        for pair in stage["switches"]:
            if len(pair) != 2 or pair[0] == pair[1] or any(not 0 <= integer(cell) < n**4 for cell in pair):
                raise ValueError("malformed physical pair")
            left, right = pair
            if left in endpoints_used or right in endpoints_used:
                raise ValueError("a physical endpoint or prime pair is reused")
            endpoints_used.update(pair)
            if abs(values[right] - values[left]) != stage["gap"]:
                raise ValueError("claimed common gap differs from actual prime values")
            observed[left] = values[right] - values[left]
            observed[right] = values[left] - values[right]
        if observed != delta:
            raise ValueError("actual pair orientation does not implement checkerboard")
    return {"certificate": certificate, "lines": independent, "expected_pool": expected_pool, "geometry_summary": geometry_summary}


def apply_switches(certificate, mask):
    if len(mask) != len(certificate["stages"]) or any(value not in (0, 1) for value in mask):
        raise ValueError("one Boolean choice per stage required")
    values = certificate["initial_values"][:]
    for stage, selected in zip(certificate["stages"], mask):
        if selected:
            for first, second in stage["switches"]:
                values[first], values[second] = values[second], values[first]
    return values


def verify_switch_result(context, mask, after):
    certificate, lines = context["certificate"], context["lines"]
    n, before = certificate["n"], certificate["initial_values"]
    if sorted(after) != context["expected_pool"]:
        raise ValueError("switch output ceased to be the prescribed pool permutation")
    expected = defaultdict(int)
    for selected, stage in zip(mask, certificate["stages"]):
        if selected:
            for cell, sign in stage_cells(stage, n).items():
                expected[cell] += sign * stage["gap"]
    if any(after[cell] - before[cell] != expected[cell] for cell in range(n**4)):
        raise ValueError("physical output differs from the stated tensor increments")
    for line in lines:
        observed = sum(after[cell] for cell in line) - sum(before[cell] for cell in line)
        if observed != sum(expected[cell] for cell in line):
            raise ValueError("a signed-line image does not match actual swaps")
    return True


def verify_signed_reference_change(context, reference, target):
    """Actual swaps relative to a nonzero reference give both signs."""
    certificate, lines = context["certificate"], context["lines"]
    before = apply_switches(certificate, reference)
    after = apply_switches(certificate, target)
    if sorted(before) != context["expected_pool"] or sorted(after) != context["expected_pool"]:
        raise AssertionError("reference orientation is not a pool permutation")
    expected = defaultdict(int)
    for old, new, stage in zip(reference, target, certificate["stages"]):
        for cell, sign in stage_cells(stage, certificate["n"]).items():
            expected[cell] += (new - old) * sign * stage["gap"]
    assert any(value < 0 for value in expected.values())
    assert any(value > 0 for value in expected.values())
    for line in lines:
        assert sum(after[cell] - before[cell] for cell in line) == sum(expected[cell] for cell in line)


def sparse_axis_image(delta, n):
    result = [defaultdict(int) for _ in range(4)]
    for cell, value in delta.items():
        point = unflat(cell, n)
        for axis in range(4):
            result[axis][point[:axis] + point[axis + 1 :]] += value
    return [{point: value for point, value in image.items() if value} for image in result]


def assert_stage_contract(stage, n):
    delta = stage_cells(stage, n)
    image = sparse_axis_image(delta, n)
    level = stage["level"]
    preserved = {0: (3,), 1: (2,), 2: tuple(stage["axes"]), 3: (0, 1), 4: (0, 1, 2)}[level]
    if any(image[axis] for axis in preserved):
        raise AssertionError("physical shape violates its exact preservation contract")
    if level >= 1:
        slices = defaultdict(int)
        for cell, value in delta.items():
            slices[unflat(cell, n)[3]] += value
        assert not any(slices.values())
    if level >= 2:
        planes = defaultdict(int)
        for cell, value in delta.items():
            planes[unflat(cell, n)[2:]] += value
        assert not any(planes.values())


def tensor_apply(matrix, values, size, rank, axis):
    output_size = len(matrix)
    shape = [size] * rank
    if not values:
        return {}
    # Other axes retain the sizes of the supplied sparse/dense dictionary.
    shape = [max(point[d] for point in values) + 1 for d in range(rank)]
    shape[axis] = output_size
    result = {}
    for point in itertools.product(*(range(length) for length in shape)):
        total = 0
        for index in range(len(matrix[0])):
            source = list(point)
            source[axis] = index
            total += matrix[point[axis]][index] * values[tuple(source)]
        result[point] = total
    return result


def tensor_product_apply(matrix, values, rank):
    result = values
    for axis in range(rank):
        result = tensor_apply(matrix, result, len(matrix[0]), rank, axis)
    return result


def check_zero_margins(values, n, rank, modulus=None):
    expected = set(itertools.product(range(n), repeat=rank))
    if set(values) != expected:
        raise ValueError("complete tensor with exact declared shape required")
    for value in values.values():
        integer(value)
    for axis in range(rank):
        margins = defaultdict(int)
        for point, value in values.items():
            margins[point[:axis] + point[axis + 1 :]] += value
        if any(value % modulus if modulus else value for value in margins.values()):
            raise ValueError("tensor has a nonzero coordinate marginal")


def exact_tensor_graph_lift(values, n, rank, edges):
    """Exact rational inverse, independent nearest rounding, integer tree repair."""
    if rank not in (2, 3):
        raise ValueError("control implements rank two and three")
    check_zero_margins(values, n, rank)
    incidence = graph_incidence(n, edges)
    laplacian = [[sum(incidence[i][e] * incidence[j][e] for e in range(len(edges))) for j in range(n)] for i in range(n)]
    inverse = _inverse([[Fraction(laplacian[i][j]) + Fraction(1, n) for j in range(n)] for i in range(n)])
    right_inverse = [[sum(incidence[v][e] * inverse[v][j] for v in range(n)) for j in range(n)] for e in range(len(edges))]
    real = tensor_product_apply(right_inverse, values, rank)
    rounded = {point: math.floor(value + Fraction(1, 2)) for point, value in real.items()}
    applied = tensor_product_apply(incidence, rounded, rank)
    residual = {point: values[point] - applied[point] for point in values}
    tree = _tree_inverse(n, edges)
    repair = tensor_product_apply(tree, residual, rank)
    result = {point: rounded[point] + repair[point] for point in rounded}
    if any(value.denominator != 1 for value in result.values() if isinstance(value, Fraction)):
        raise AssertionError("tree repair introduced denominators")
    result = {point: int(value) for point, value in result.items()}
    if tensor_product_apply(incidence, result, rank) != values:
        raise AssertionError("tensor coefficients failed exact reconstruction")
    norm = max(sum(abs(value) for value in row) for row in right_inverse)
    degree = max(sum(abs(value) for value in row) for row in incidence)
    bound = norm**rank * max(abs(value) for value in values.values()) + Fraction(1, 2) + Fraction((degree * n) ** rank, 2 ** (rank + 1))
    if max(map(abs, result.values())) > bound:
        raise AssertionError("rounding/tree coefficient bound failed")
    return result, norm, bound


def path_tensor_coefficients(values, n, rank, modulus=None):
    check_zero_margins(values, n, rank, modulus)
    result = {}
    for edge in itertools.product(range(n - 1), repeat=rank):
        value = sum(values[point] for point in itertools.product(*(range(index + 1) for index in edge)))
        result[edge] = value % modulus if modulus else value
    return result


def axis_targets(values, n):
    return [dict(image) for image in sparse_axis_image(dict(enumerate(values)), n)]


def total_on(values, n, fixed):
    return sum(value for cell, value in enumerate(values) if all(unflat(cell, n)[axis] == coordinate for axis, coordinate in fixed.items()))


def numeric_five_pass_control(n, rng):
    """Compatible numeric demands; no claim that intermediate arrays are pools."""
    original = sieve_pool(n**4)
    target_values = original[:]
    rng.shuffle(target_values)
    targets = axis_targets(target_values, n)
    current = original[:]
    path = [(i, i + 1) for i in range(n - 1)]

    def change(axes, endpoints, point, amount):
        stage = {"axes": axes, "endpoints": endpoints, "point": point}
        for cell, sign in stage_cells(stage, n).items():
            current[cell] += sign * amount

    demands = [total_on(target_values, n, {3: w}) - total_on(current, n, {3: w}) for w in range(n)]
    assert sum(demands) == 0
    for w in range(n - 1):
        change([3], [path[w]], [0, 0, 0, 0], sum(demands[: w + 1]))
    assert axis_targets(current, n)[3] == axis_targets(original, n)[3]
    assert all(total_on(current, n, {3: w}) == total_on(target_values, n, {3: w}) for w in range(n))

    for w in range(n):
        demands = [total_on(target_values, n, {2: z, 3: w}) - total_on(current, n, {2: z, 3: w}) for z in range(n)]
        assert sum(demands) == 0
        before_z = axis_targets(current, n)[2]
        for z in range(n - 1):
            change([2], [path[z]], [0, 0, 0, w], sum(demands[: z + 1]))
        assert axis_targets(current, n)[2] == before_z
    assert all(total_on(current, n, {2: z, 3: w}) == total_on(target_values, n, {2: z, 3: w}) for z in range(n) for w in range(n))

    for z, w in itertools.product(range(n), repeat=2):
        for changed_axis, native_axis in ((0, 1), (1, 0)):
            old = axis_targets(current, n)
            demands = []
            for coordinate in range(n):
                index = (coordinate, z, w)
                demands.append(targets[native_axis][index] - old[native_axis][index])
            assert sum(demands) == 0
            for edge in range(n - 1):
                change([changed_axis], [path[edge]], [0, 0, z, w], sum(demands[: edge + 1]))
            assert axis_targets(current, n)[changed_axis] == old[changed_axis]
    assert axis_targets(current, n)[:2] == targets[:2]

    for w in range(n):
        old = axis_targets(current, n)
        matrix = {(x, y): targets[2][x, y, w] - old[2][x, y, w] for x, y in itertools.product(range(n), repeat=2)}
        for (a, b), coefficient in path_tensor_coefficients(matrix, n, 2).items():
            change([0, 1], [path[a], path[b]], [0, 0, 0, w], coefficient)
        assert axis_targets(current, n)[:2] == targets[:2]
    assert axis_targets(current, n)[:3] == targets[:3]

    old = axis_targets(current, n)
    tensor = {point: targets[3][point] - old[3][point] for point in itertools.product(range(n), repeat=3)}
    for edge, coefficient in path_tensor_coefficients(tensor, n, 3).items():
        change([0, 1, 2], [path[index] for index in edge], [0, 0, 0, 0], coefficient)
    assert axis_targets(current, n) == targets
    assert sum(current) == sum(original) and all(value % 2 for value in current)


def expect_rejection(call):
    try:
        call()
    except (ValueError, AssertionError):
        return
    raise AssertionError("negative control was accepted")


def verify_exponent_schedule(exponents, delta=Fraction(1, 5), extra=Fraction(79, 100)):
    if len(exponents) != 5 or any(left >= right for left, right in zip(exponents, exponents[1:])):
        raise ValueError("five strictly increasing correction exponents required")
    if exponents[0] <= Fraction(1, 2) or exponents[-1] >= 1:
        raise ValueError("completion noise and sparse occupancy do not fit")
    if extra < exponents[-1] or extra - delta >= exponents[0]:
        raise ValueError("joint macro midpoint error is not below the target scale")
    if 3 + exponents[-1] >= 4 - delta:
        raise ValueError("global deletions can exhaust a midpoint residue class")
    if exponents[-1] + 4 <= 3 or exponents[-2] + 4 <= 2:
        raise ValueError("integer tensor rounding cost does not fit")
    return {"axis_exponents": [str(value) for value in exponents], "extra_exponent": str(extra), "delta_exponent": str(delta), "fresh_class_power_slack": str(1 - delta - exponents[-1]), "joint_centering_power_slack": str(exponents[0] - extra + delta)}


def planned_union_controls():
    """Exhaust the projection-union load counts, retaining parallel edges."""
    n = 7
    edges = [(i, (i + 1) % n) for i in range(n)] * 2
    degrees = [sum(vertex in edge for edge in edges) for vertex in range(n)]
    frame_lines = set()
    for word in itertools.product(list(range(n)) + ["t", "r"], repeat=3):
        if not any(value in ("t", "r") for value in word):
            continue
        frame_lines.add(tuple(sorted(tuple(t if value == "t" else n - 1 - t if value == "r" else value for value in word) for t in range(n))))
    results = []
    for rank in (1, 2, 3):
        multiplicity = defaultdict(int)
        for selected in itertools.product(edges, repeat=rank):
            for fixed in itertools.product(range(n), repeat=3 - rank):
                for vertex in itertools.product(*selected):
                    multiplicity[vertex + fixed] += 1
        for point in itertools.product(range(n), repeat=3):
            assert multiplicity[point] == math.prod(degrees[point[axis]] for axis in range(rank))
        maximum = max(sum(multiplicity[point] for point in line) for line in frame_lines)
        assert maximum <= n * max(degrees) ** rank
        results.append({"rank": rank, "n": n, "degree_with_parallel_edges": max(degrees), "projected_signed_lines": len(frame_lines), "maximum_planned_union_load_per_stage": maximum, "proved_bound": n * max(degrees) ** rank})
    return results


def complete_grid_control():
    gap = 6
    weights = [gap] * 8 + [24, 30, 60, 96]
    reachable = {0: ()}
    for index, weight in enumerate(weights):
        additions = {total + weight: chosen + (index,) for total, chosen in reachable.items()}
        reachable.update(additions)
    total = sum(weights)
    if set(reachable) != set(range(0, total + gap, gap)):
        raise AssertionError("constructed complete-sequence interval has a hole")
    reference = gap * (total // (2 * gap))
    capacity = min(reference, total - reference)
    for correction in range(-capacity, capacity + gap, gap):
        selection = reachable[reference + correction]
        assert len(selection) == len(set(selection))
        assert sum(weights[index] for index in selection) - reference == correction
    return {"stage_count": len(weights), "gap": gap, "signed_capacity": capacity, "certified_grid_points": len(reachable)}


def run_checks():
    rng = random.Random(20261102)
    counts = {}
    for n, expected in ((1, 1), (3, 272), (5, 888), (11, 6960)):
        produced, independent = full_lines(n), independent_full_lines(n)
        assert produced == independent and len(produced) == expected
        counts[str(n)] = expected

    certificate = make_certificate()
    context = verify_certificate(certificate)
    stage_count = len(certificate["stages"])
    masks = [[0] * stage_count, [1] * stage_count]
    masks.extend([int(i == chosen) for i in range(stage_count)] for chosen in range(stage_count))
    masks.extend([rng.randrange(2) for _ in range(stage_count)] for _ in range(32))
    for mask in masks:
        verify_switch_result(context, mask, apply_switches(certificate, mask))
    for stage in certificate["stages"]:
        assert_stage_contract(stage, certificate["n"])
    reference = [index % 2 for index in range(stage_count)]
    verify_signed_reference_change(context, reference, [1 - value for value in reference])
    for chosen in range(stage_count):
        reference, target = [0] * stage_count, [0] * stage_count
        reference[chosen] = 1
        verify_signed_reference_change(context, reference, target)

    # Exceptional native endpoints are allowed; the fresh transverse orbit is
    # the actual exclusion. These fixtures retain centers and shared endpoints.
    exceptional, exceptional_maximum_intersection = 0, 0
    for endpoints in (((5, 4), (5, 3), (5, 2)), ((0, 10), (0, 10), (0, 10)), ((0, 1), (0, 2), (0, 3))):
        for w in range(11):
            stage = {"level": 4, "axes": [0, 1, 2], "endpoints": [list(pair) for pair in endpoints], "point": [0, 0, 0, w], "bundle": 0}
            if legal_orbits(stage, 11):
                checked = verify_geometry({"n": 11, "stages": [stage]}, context["lines"])
                exceptional_maximum_intersection = max(exceptional_maximum_intersection, checked["maximum_extra_bundle_intersection"])
                assert_stage_contract(stage, 11)
                exceptional += 1
    assert exceptional_maximum_intersection == 2

    tensor_cases = []
    residue_cases = 0
    for n in (3, 5):
        edges = [(i, i + 1) for i in range(n - 1)] + [(n - 1, 0)]
        graph = graph_incidence(n, edges)
        for rank in (2, 3):
            seed = {point: rng.randrange(-20, 21) for point in itertools.product(range(len(edges)), repeat=rank)}
            demand = tensor_product_apply(graph, seed, rank)
            coefficients, norm, bound = exact_tensor_graph_lift(demand, n, rank, edges)
            assert tensor_product_apply(graph, coefficients, rank) == demand
            tensor_cases.append({"n": n, "rank": rank, "graph_edges": len(edges), "inverse_row_norm": str(norm), "coefficient_bound": str(bound), "maximum_coefficient": max(map(abs, coefficients.values()))})
            for modulus in (2, 3, 4, 5, 6, 12):
                reduced = {point: value % modulus for point, value in demand.items()}
                path_coefficients = path_tensor_coefficients(reduced, n, rank, modulus)
                path = graph_incidence(n, [(i, i + 1) for i in range(n - 1)])
                rebuilt = tensor_product_apply(path, path_coefficients, rank)
                assert all((rebuilt[point] - reduced[point]) % modulus == 0 for point in reduced)
                assert all(0 <= value < modulus for value in path_coefficients.values())
                residue_cases += 1
            damaged = dict(demand)
            damaged[(0,) * rank] += 1
            expect_rejection(lambda: exact_tensor_graph_lift(damaged, n, rank, edges))
            expect_rejection(lambda: path_tensor_coefficients(damaged, n, rank, 12))
            expect_rejection(lambda: exact_tensor_graph_lift(demand, n, rank, [(0, 0)] + edges))
            expect_rejection(lambda: exact_tensor_graph_lift(demand, n, rank, [(0, 1)]))

    for n in (3, 5):
        for _ in range(4):
            numeric_five_pass_control(n, rng)

    negative_names = []
    for name in ("duplicate_entry", "out_of_pool_prime", "omitted_line", "duplicate_line", "wrong_diagonal", "shared_support", "reused_pair", "wrong_gap", "wrong_orientation", "forbidden_transverse_orbit", "falsely_independent_bundle"):
        damaged = copy.deepcopy(certificate)
        if name == "duplicate_entry":
            damaged["initial_values"][0] = damaged["initial_values"][1]
        elif name == "out_of_pool_prime":
            damaged["initial_values"][0] = independent_trial_pool(damaged["n"] ** 4 + 1)[-1]
        elif name == "omitted_line":
            damaged["declared_lines"].pop()
        elif name == "duplicate_line":
            damaged["declared_lines"][-1] = damaged["declared_lines"][0][:]
        elif name == "wrong_diagonal":
            damaged["declared_lines"][-1][0] = 1
        elif name == "shared_support":
            damaged["stages"][1] = copy.deepcopy(damaged["stages"][0])
        elif name == "reused_pair":
            damaged["stages"][-1]["switches"][1] = damaged["stages"][-1]["switches"][0][:]
        elif name == "wrong_gap":
            damaged["stages"][-1]["gap"] += 2
        elif name == "wrong_orientation":
            first, second = damaged["stages"][-1]["switches"][0]
            damaged["initial_values"][first], damaged["initial_values"][second] = damaged["initial_values"][second], damaged["initial_values"][first]
        elif name == "forbidden_transverse_orbit":
            damaged["stages"][-1]["point"][3] = 0
        elif name == "falsely_independent_bundle":
            # Declare two physically different stages to share a reservoir
            # while reusing a transverse label; cellwise randomness cannot
            # certify this missing whole-bundle range contract.
            damaged["stages"][-1]["point"][3] = damaged["stages"][-2]["point"][3]
        expect_rejection(lambda: verify_certificate(damaged))
        negative_names.append(name)

    # An individual pair flip is not a checkerboard stage, despite preserving
    # all pool entries. The physical verifier rejects it independently of the
    # declared orientation metadata.
    after = certificate["initial_values"][:]
    first, second = certificate["stages"][-1]["switches"][0]
    after[first], after[second] = after[second], after[first]
    expect_rejection(lambda: verify_switch_result(context, [0] * stage_count, after))
    negative_names.append("independent_pair_flip_breaks_bundle")

    # Fixed-difference graphs need matchings, not merely repeated edges.
    chain_edges = [(6 * i, 6 * (i + 1)) for i in range(256)]
    matching, used = [], set()
    for edge in chain_edges:
        if not used.intersection(edge):
            matching.append(edge)
            used.update(edge)
    assert len(matching) >= 40
    assert math.gcd(6, 10) == 2 and 2 not in {0, 6, 10, 16}
    negative_names.append("gcd_does_not_supply_complete_grid")

    # Independent individual stages have a sum-sized native range. Balanced
    # complementary subsets do not. This numeric control isolates the reason
    # cellwise/stagewise independence cannot be used in the centering proof.
    weights = [2] * 50 + [100] * 4
    first = [1] * 25 + [0] * 25 + [1, 1, 0, 0]
    complement = [1 - value for value in first]
    assert sum(a * b for a, b in zip(weights, first)) == 250
    assert sum(a * b for a, b in zip(weights, complement)) == 250
    assert sum(weights) > max(weights)
    schedule = [Fraction(15 + index, 25) for index in range(5)]
    schedule_summary = verify_exponent_schedule(schedule)
    expect_rejection(lambda: verify_exponent_schedule(schedule, extra=Fraction(4, 5)))
    expect_rejection(lambda: verify_exponent_schedule(schedule[:-1] + [schedule[-2]]))
    expect_rejection(lambda: verify_exponent_schedule(schedule, delta=Fraction(1, 4)))
    negative_names.extend(["stagewise_independence_has_larger_native_range", "centering_boundary_exponent", "collapsed_last_correction_scales", "depleted_midpoint_window"])
    union_summary = planned_union_controls()
    grid_summary = complete_grid_control()

    digest = hashlib.sha256(json.dumps(certificate, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"status": "passed", "scope": "finite physical controller and exact numeric interfaces; no prime-line arrangement assertion", "line_counts": counts, "physical_pool_count": certificate["n"] ** 4, "physical_patterns": len(masks), "signed_reference_changes": stage_count + 1, "geometry": context["geometry_summary"], "exceptional_native_endpoint_cases": exceptional, "exceptional_maximum_extra_intersection": exceptional_maximum_intersection, "planned_union_controls": union_summary, "complete_grid_control": grid_summary, "tensor_lifts": tensor_cases, "composite_ring_prefix_controls": residue_cases, "numeric_five_pass_controls": 8, "schedule": schedule_summary, "negative_controls": negative_names, "certificate_sha256": digest}, certificate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, help="write the checked physical controller certificate")
    parser.add_argument("--verify", type=Path, help="independently replay an existing physical controller certificate")
    args = parser.parse_args()
    if args.verify:
        certificate = json.loads(args.verify.read_text())
        context = verify_certificate(certificate)
        masks = [[1] * len(certificate["stages"])]
        for mask in masks:
            verify_switch_result(context, mask, apply_switches(certificate, mask))
        print(json.dumps({"status": "passed", "scope": "physical controller certificate only", **context["geometry_summary"]}, sort_keys=True, indent=2))
        return
    summary, certificate = run_checks()
    if args.certificate:
        args.certificate.write_text(json.dumps(certificate, sort_keys=True, indent=2) + "\n")
    print(json.dumps(summary, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
