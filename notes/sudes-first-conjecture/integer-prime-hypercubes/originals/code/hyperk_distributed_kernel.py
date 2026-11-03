#!/usr/bin/env python3
"""Exact author controls for the distributed-kernel synthesis.

These sparse integer and rational checks are not prime-array certificates,
an asymptotic probability experiment, or an independent review.  The selector
producer is imported from its frozen author source; signed-line images below
are independently generated from equal/reflected coordinate tests.

Python 3.11+, standard library only.  Run with --self-test.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import comb

from hyperk_incidence import (
    _chosen_divisor,
    integer_lift,
    line_keys,
    marker_data,
    order,
)
from hyperk_kernel_research import local_projector, pure_selector, selector_invoices

Tensor = dict[tuple[int, ...], int | Fraction]


def tidy(tensor: Tensor) -> Tensor:
    return {point: value for point, value in tensor.items() if value}


def add(left: Tensor, right: Tensor, scalar=1) -> Tensor:
    result = defaultdict(int, left)
    for point, value in right.items():
        result[point] += scalar * value
    return tidy(dict(result))


def tensor_product(factors, dimension: int) -> Tensor:
    assert sorted(i for coords, _ in factors for i in coords) == list(range(dimension))
    answer = {(None,) * dimension: 1}
    for coords, tensor in factors:
        result = {}
        for point, value in answer.items():
            for local, coefficient in tensor.items():
                other = list(point)
                for i, entry in zip(coords, local):
                    assert other[i] is None
                    other[i] = entry
                other = tuple(other)
                assert other not in result
                result[other] = value * coefficient
        answer = result
    return tidy(answer)


def signature(tensor: Tensor, dimension: int) -> Tensor:
    """Literal signed-equality line sums, including every central incidence."""
    result = defaultdict(int)
    for varying_count in range(1, dimension + 1):
        for varying in combinations(range(dimension), varying_count):
            fixed = tuple(i for i in range(dimension) if i not in varying)
            for tail in product((-1, 1), repeat=varying_count - 1):
                signs = (1,) + tail
                for point, value in tensor.items():
                    parameter = point[varying[0]]
                    if all(point[i] == sign * parameter
                           for i, sign in zip(varying, signs)):
                        result[varying, signs, tuple(point[i] for i in fixed)] += value
    return tidy(dict(result))


def pairable(tensor: Tensor, dimension: int) -> bool:
    if any(value not in (-1, 1) for value in tensor.values()):
        return False
    for axis in range(dimension):
        fibers = defaultdict(lambda: [0, 0])
        for point, value in tensor.items():
            fixed = tuple(point[i] for i in range(dimension) if i != axis)
            fibers[fixed][0 if value > 0 else 1] += 1
        if any(positive != negative for positive, negative in fibers.values()):
            return False
    return True


def rooted_selector(dimension: int, root: int, auxiliary_start: int) -> Tensor:
    """PS with its distinguished root changed and all auxiliaries fixed."""
    assert root != 0
    if dimension == 1:
        return {(root,): 1}
    template, alphabet = pure_selector(dimension)
    auxiliaries = set(range(auxiliary_start, auxiliary_start + alphabet - 1))
    assert abs(root) not in auxiliaries
    return {
        tuple(root if value == 1 else auxiliary_start + value - 2 for value in point): sign
        for point, sign in template.items()
    }


def rooted_difference(dimension: int, first: int, second: int,
                      auxiliary_start: int) -> Tensor:
    assert first != second
    return add(rooted_selector(dimension, first, auxiliary_start),
               rooted_selector(dimension, second, auxiliary_start), -1)


def central_template(dimension: int, auxiliary_start: int) -> Tensor:
    if dimension == 0:
        return {(): 1}
    raw = local_projector(tuple((0, i + 1) for i in range(dimension)))
    return {
        tuple(0 if value == 0 else (1 if value > 0 else -1)
              * (auxiliary_start + abs(value) - 1) for value in point): sign
        for point, sign in raw.items()
    }


def central_alphabet(dimension: int) -> int:
    alphabets, _ = selector_invoices(dimension)
    return dimension + sum(comb(dimension, b) * 2 ** (b - 1) * alphabets[b]
                           for b in range(2, dimension + 1))


def lift(dimension: int, zero_coordinates, blocks, endpoints,
         auxiliary_start: int = 1000) -> Tensor:
    """One fixed-palette signed-partition lift, with explicit orbit checks."""
    assert len(blocks) == len(endpoints)
    zero_coordinates = tuple(zero_coordinates)
    coordinates = list(zero_coordinates)
    coordinates += [i for block, signs in blocks for i in block]
    assert sorted(coordinates) == list(range(dimension))
    endpoint_orbits = [set(map(abs, pair)) for pair in endpoints]
    assert all(0 not in values for values in endpoint_orbits)
    assert all(not (endpoint_orbits[i] & endpoint_orbits[j])
               for i in range(len(blocks)) for j in range(i))
    factors = []
    if zero_coordinates:
        factors.append((zero_coordinates, central_template(len(zero_coordinates), auxiliary_start)))
    next_auxiliary = auxiliary_start + central_alphabet(len(zero_coordinates))
    alphabets, _ = selector_invoices(dimension)
    for (block, signs), (first, second) in zip(blocks, endpoints):
        assert signs[0] == 1 and len(block) == len(signs)
        local = rooted_difference(len(block), first, second, next_auxiliary)
        if len(block) > 1:
            used = set(range(next_auxiliary, next_auxiliary + alphabets[len(block)] - 1))
            assert all(not (used & values) for values in endpoint_orbits)
            next_auxiliary += alphabets[len(block)] - 1
        reflected = {tuple(sign * value for sign, value in zip(signs, point)): coefficient
                     for point, coefficient in local.items()}
        factors.append((tuple(block), reflected))
    return tensor_product(factors, dimension)


def point_type(point):
    """Exact zero block and signed equality partition of one cell."""
    zeros = tuple(i for i, value in enumerate(point) if value == 0)
    groups = defaultdict(list)
    for i, value in enumerate(point):
        if value:
            groups[abs(value)].append(i)
    blocks = []
    for coords in groups.values():
        root = point[coords[0]]
        signs = tuple(1 if point[i] == root else -1 for i in coords)
        blocks.append((tuple(coords), signs))
    return zeros, tuple(sorted(blocks))


def refines_type(point, original_zeros, original_blocks) -> bool:
    """No new zero and no merger across the old block/orbit groups."""
    if any(point[i] == 0 for block, _ in original_blocks for i in block):
        return False
    groups = [tuple(original_zeros)] + [tuple(block) for block, _ in original_blocks]
    orbit_sets = [{abs(point[i]) for i in group if point[i]} for group in groups]
    return all(not (orbit_sets[i] & orbit_sets[j])
               for i in range(len(groups)) for j in range(i))


def native_restriction(tensor: Tensor, zeros, blocks) -> Tensor:
    result = {}
    desired = tuple(zeros), tuple(blocks)
    for point, value in tensor.items():
        if point_type(point) == desired:
            result[tuple(point[block[0]] for block, _ in blocks)] = value
    return result


def generic_cube(endpoints) -> Tensor:
    return tensor_product([((i,), {(u,): 1, (v,): -1})
                           for i, (u, v) in enumerate(endpoints)], len(endpoints))


def exact_constants(dimension: int):
    """AF invoices; finite algebra only, not a threshold evaluation."""
    alphabets, supports = selector_invoices(dimension)
    alphabets[1] = supports[1] = 1
    central_support = [1]
    for z in range(1, dimension + 1):
        central_support.append(2 * central_support[z - 1] + sum(
            comb(z - 1, b - 1) * 2 ** (b - 1) * supports[b]
            * central_support[z - b] for b in range(2, z + 1)))
    palette_size = central_alphabet(dimension) + dimension * max(
        alphabets[b] - 1 for b in range(1, dimension + 1))
    palette_count = 2 * dimension + 1
    forbidden_orbits = palette_size + 2 * dimension
    graph_degree = 2 * (forbidden_orbits + 1) + 1
    support = max(central_support) * (2 * max(supports.values())) ** dimension
    type_counts = [1]
    for size in range(1, dimension + 1):
        type_counts.append(type_counts[size - 1] + sum(
            comb(size - 1, block - 1) * 2 ** (block - 1) * type_counts[size - block]
            for block in range(1, size + 1)))
    types = type_counts[dimension]
    assert types <= (2 * dimension + 1) ** dimension
    frame_count = palette_count * types * (1 + graph_degree) ** dimension
    point_degree = palette_count * types * (dimension * graph_degree) ** dimension
    # Keep this exact integer factored: at d=6 its decimal expansion is
    # needlessly enormous, whereas factor/base/exponent are fully checkable.
    coefficient = (2 * types, 1 + 2 * support, types)
    threshold = max(palette_count * palette_size + 2 * dimension + 2,
                    2 ** (dimension + 1) * dimension ** 2, 3 ** dimension)
    return dict(P=palette_size, H=palette_count, F=forbidden_orbits,
                Delta=graph_degree, S=support, T=types, A=frame_count,
                B=point_degree, C=coefficient, M=threshold)


def run_self_test():
    counts = Counter()
    for dimension in range(1, 5):
        for roots in ((1, 2), (-1, 2), (1, -1)):
            difference = rooted_difference(dimension, *roots, 100)
            assert not signature(difference, dimension)
            assert pairable(difference, dimension)
            assert all(any(value in roots for value in point)
                       for point in difference)
            q = rooted_selector(dimension, roots[0], 100)
            body = {point: value for point, value in q.items()
                    if len(set(point)) == 1}
            assert body == {(roots[0],) * dimension: 1}
            counts["rooted_difference_signatures"] += 1
    for dimension in range(1, 4):
        central = central_template(dimension, 100)
        assert central[(0,) * dimension] == 1
        assert not signature(central, dimension)
        assert pairable(central, dimension)
        assert all(sum(value == 0 for value in point) < dimension
                   for point in central if any(point))
        counts["central_kernel_signatures"] += 1

    cases = [
        (2, (), (((0, 1), (1, 1)),), ((1, 2),)),
        (3, (), (((0, 1), (1, -1)), ((2,), (1,))), ((1, -1), (2, 3))),
        (4, (), (((0, 1), (1, 1)), ((2, 3), (1, -1))), ((1, 2), (3, -4))),
        (5, (0,), (((1, 2), (1, -1)), ((3, 4), (1, 1))), ((1, 2), (3, 4))),
        (6, (0, 1), (((2, 3), (1, 1)), ((4, 5), (1, -1))), ((1, -1), (2, -3))),
        (6, (), (((0, 1, 2), (1, -1, 1)), ((3, 4, 5), (1, 1, -1))),
         ((1, 2), (3, -4))),
    ]
    for dimension, zeros, blocks, endpoints in cases:
        lifted = lift(dimension, zeros, blocks, endpoints)
        assert not signature(lifted, dimension)
        assert pairable(lifted, dimension)
        assert all(refines_type(point, zeros, blocks) for point in lifted)
        assert native_restriction(lifted, zeros, blocks) == generic_cube(endpoints)
        assert all(len({abs(value) for value in point if value}) > len(blocks)
                   for point in lifted if point_type(point) != (tuple(zeros), tuple(blocks)))
        counts["stratum_lifts"] += 1

    # A finite degree-three graph fixture checks actual support incidence.
    # No expansion or robust-deletion assertion is made about this fixture.
    m = 7
    edges = []
    for value in range(1, m + 1):
        successor = 1 + value % m
        edges.extend([(value, successor), (-value, -successor), (value, -value)])
    incidence = Counter()
    blocks = (((0, 1), (1, 1)), ((2, 3), (1, -1)))
    frame = []
    for first in edges:
        for second in edges:
            if set(map(abs, first)) & set(map(abs, second)):
                continue
            template = lift(4, (), blocks, (first, second))
            frame.append(template)
            incidence.update(template.keys())
    assert max(incidence.values()) <= (4 * 3) ** 2
    counts["fixed_frame_templates"] = len(frame)
    counts["fixed_frame_max_point_degree"] = max(incidence.values())

    # Monic KG lifting over composite rings.  Entrywise representatives are
    # deliberately not integral kernel tensors; the lift repairs them.
    dimension, n = 2, 9
    values = order(n)
    blocks, labels, _, _ = marker_data(dimension)
    standard = [point for point in product(values, repeat=dimension)
                if _chosen_divisor(dimension, point, blocks, labels) is None]
    zero_targets = dict.fromkeys(line_keys(dimension, n), 0)
    initial = integer_lift(dimension, n, zero_targets,
                           {point: (7 * i + 3) % 17 - 8 for i, point in enumerate(standard)})
    assert not signature(tidy(initial), dimension)
    for modulus in (2, 3, 4, 6, 8, 9, 12):
        representatives = {point: value % modulus for point, value in initial.items()}
        assert all(value % modulus == 0
                   for value in signature(tidy(representatives), dimension).values())
        lifted = integer_lift(dimension, n, zero_targets,
                              {point: representatives[point] for point in standard})
        assert not signature(tidy(lifted), dimension)
        assert all((lifted[point] - representatives[point]) % modulus == 0
                   for point in initial)
        assert signature(tidy(representatives), dimension), "test lost nonintegral-kernel witness"
        counts["composite_ring_lifts"] += 1

    # Rounding template coefficients leaves an exactly integral kernel residual.
    ab = rooted_difference(2, 1, 2, 100)
    bc = rooted_difference(2, 2, 3, 100)
    ac = rooted_difference(2, 1, 3, 100)
    assert add(add(ab, bc), ac, -1) == {}
    coefficients = [Fraction(16, 3), Fraction(-5, 3), Fraction(8, 3)]
    templates = [ab, bc, ac]
    exact = {}
    rounded = {}
    load = Counter()
    for coefficient, template in zip(coefficients, templates):
        exact = add(exact, template, coefficient)
        rounded = add(rounded, template, round(coefficient))
        load.update(template.keys())
    assert all(value.denominator == 1 for value in exact.values())
    residual = add(exact, rounded, -1)
    assert not signature(residual, 2)
    assert max(map(abs, residual.values()), default=0) <= Fraction(max(load.values()), 2)
    counts["coefficient_rounding_controls"] += 1

    # Negative controls reject shortcuts used by earlier incomplete routes.
    generic_part = {point: value for point, value in ab.items()
                    if point[0] and point[1] and abs(point[0]) != abs(point[1])}
    assert signature(generic_part, 2), "restriction before clearing coarser strata was accepted"
    counts["negative_controls"] += 1
    fractional = tensor_product([
        ((0,), {(1,): 1, (2,): -1}),
        ((1,), {(3,): Fraction(2, 5), (4,): Fraction(2, 5), (5,): Fraction(-4, 5)})
    ], 2)
    assert not signature(fractional, 2)
    entry_rounded = tidy({point: round(value) for point, value in fractional.items()})
    assert signature(entry_rounded, 2), "entrywise rounding was accepted as kernel preserving"
    counts["negative_controls"] += 1
    assert not pairable({point: 2 * value for point, value in ab.items()}, 2)
    counts["negative_controls"] += 1
    try:
        lift(4, (), (((0, 1), (1, 1)), ((2, 3), (1, 1))), ((1, 2), (2, 3)))
    except AssertionError:
        counts["negative_controls"] += 1
    else:
        raise AssertionError("overlapping endpoint orbit groups were accepted")

    for dimension in range(1, 7):
        constants = exact_constants(dimension)
        assert constants["H"] > 2 * dimension
        assert constants["M"] >= constants["H"] * constants["P"] + 2 * dimension + 2
        assert constants["M"] >= 2 ** (dimension + 1) * dimension ** 2
        factor, base, exponent = constants["C"]
        assert factor == 2 * constants["T"] and base > 1 and exponent == constants["T"]
        counts["symbolic_dimension_invoices"] += 1
    assert exact_constants(5)["T"] == 648
    assert exact_constants(6)["T"] == 4088
    return dict(sorted(counts.items()))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    if not arguments.self_test:
        parser.error("choose --self-test")
    print(run_self_test())
