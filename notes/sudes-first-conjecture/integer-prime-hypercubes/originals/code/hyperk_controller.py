#!/usr/bin/env python3
"""Exact fixed-dimensional controller controls; not an asymptotic prover.

Run from any directory with Python 3.11+:
    python3 -B hyperk_controller.py
Only standard-library modules are used. Physical fixtures are partial prime
trades. Numeric flow fixtures check algebra, not disjoint physical realization.
"""

from collections import defaultdict
from copy import deepcopy
from itertools import combinations, product
from math import isqrt
from random import Random
import argparse
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def interval(n):
    require(type(n) is int and n >= 1 and n % 2 == 1, "odd positive order")
    return tuple(range(-(n // 2), n // 2 + 1))


def block_directions(k):
    for size in range(1, k + 1):
        for varying in combinations(range(k), size):
            for signs in product((-1, 1), repeat=size - 1):
                yield varying, (1,) + signs


def line_key(varying, signs, point):
    varying = tuple(varying)
    return varying, tuple(signs), tuple(
        (i, point[i]) for i in range(len(point)) if i not in varying
    )


def sparse_signature(delta, k):
    """All nonzero full signed-line images from point incidences alone."""
    out = defaultdict(int)
    for point, coefficient in delta.items():
        require(len(point) == k, "cell dimension")
        for varying, signs in block_directions(k):
            parameter = point[varying[0]]
            if all(point[i] == sign * parameter for i, sign in zip(varying, signs)):
                out[line_key(varying, signs, point)] += coefficient
    return {line: value for line, value in out.items() if value}


def enumerate_lines_independently(k, n):
    """Enumerate cell sets using direction words, then recover labels."""
    labels = interval(n)
    output = {}
    seen = set()
    for direction in product((-1, 0, 1), repeat=k):
        moving = tuple(i for i, sign in enumerate(direction) if sign)
        if not moving or direction[moving[0]] != 1:
            continue
        static = tuple(i for i, sign in enumerate(direction) if not sign)
        for fixed in product(labels, repeat=len(static)):
            fixed_map = dict(zip(static, fixed))
            cells = tuple(
                tuple(direction[i] * t if direction[i] else fixed_map[i]
                      for i in range(k))
                for t in labels
            )
            cell_set = frozenset(cells)
            if cell_set in seen:
                continue
            seen.add(cell_set)
            key = moving, tuple(direction[i] for i in moving), tuple(zip(static, fixed))
            output[key] = cells
    expected = 1 if n == 1 else ((n + 2) ** k - n ** k) // 2
    require(len(output) == expected, "line inventory")
    return output


def tensor(factors):
    """Sparse product of point masses and differences, with exact signs."""
    out = {(): 1}
    for entries in factors:
        require(1 <= len(entries) <= 2, "factor size")
        require(len(set(entries)) == len(entries), "repeated factor endpoint")
        updated = {}
        for prefix, value in out.items():
            for bit, label in enumerate(entries):
                updated[prefix + (label,)] = value * (-1 if bit else 1)
        out = updated
    return out


def formula_signature(factors):
    """Equation SIG evaluated separately from sparse point incidence."""
    k = len(factors)
    vectors = [{x: (-1 if j else 1) for j, x in enumerate(f)} for f in factors]
    output = {}
    for varying, signs in block_directions(k):
        parameters = set()
        for i, sign in zip(varying, signs):
            parameters.update(sign * value for value in vectors[i])
        scalar = sum(
            _prod(vectors[i].get(sign * t, 0) for i, sign in zip(varying, signs))
            for t in parameters
        )
        if not scalar:
            continue
        fixed = tuple(i for i in range(k) if i not in varying)
        for values in product(*(factors[i] for i in fixed)):
            point = [0] * k
            for i, value in zip(fixed, values):
                point[i] = value
            coefficient = scalar * _prod(vectors[i][v] for i, v in zip(fixed, values))
            output[line_key(varying, signs, point)] = coefficient
    return output


def _prod(values):
    value = 1
    for x in values:
        value *= x
    return value


def prime_trial(value):
    if type(value) is not int or value < 2:
        return False
    return all(value % divisor for divisor in range(2, isqrt(value) + 1))


def first_odd_primes(count):
    primes = []
    candidate = 3
    while len(primes) < count:
        if all(candidate % p for p in primes if p * p <= candidate):
            primes.append(candidate)
        candidate += 2
    return primes


def matched_pairs(pool, gap, number):
    prime_set = set(pool)
    used = set()
    pairs = []
    for p in pool:
        if p not in used and p + gap in prime_set and p + gap not in used:
            pairs.append((p, p + gap))
            used.update(pairs[-1])
            if len(pairs) == number:
                return pairs
    raise ValueError("insufficient equal-gap fixture pairs")


def physical_certificate(factors, n, gap=6):
    k = len(factors)
    active = [i for i, values in enumerate(factors) if len(values) == 2]
    require(active, "a nonconstant stage is required")
    pair_axis = active[-1]
    delta = tensor(factors)
    low_cells = sorted(point for point in delta if point[pair_axis] == factors[pair_axis][0])
    pair_values = matched_pairs(first_odd_primes(max(200, 16 * len(low_cells))), gap, len(low_cells))
    assignments = []
    pair_records = []
    for a, (p, q) in zip(low_cells, pair_values):
        b = list(a)
        b[pair_axis] = factors[pair_axis][1]
        b = tuple(b)
        lower_first = delta[a] == 1
        assignments.extend(((list(a), p if lower_first else q),
                            (list(b), q if lower_first else p)))
        pair_records.append((list(a), list(b)))
    certificate = {
        "kind": "partial-prime-controller",
        "dimension": k,
        "order": n,
        "gap": gap,
        "factors": [list(f) for f in factors],
        "assignments": assignments,
        "switch_pairs": pair_records,
    }
    verify_physical(certificate)
    return certificate


def verify_physical(certificate):
    require(certificate.get("kind") == "partial-prime-controller", "partial trade is not an arrangement")
    k, n, gap = (certificate[key] for key in ("dimension", "order", "gap"))
    require(type(k) is int and k >= 2, "dimension")
    labels = set(interval(n))
    require(type(gap) is int and gap > 0 and gap % 2 == 0, "positive even gap")
    factors = tuple(tuple(f) for f in certificate["factors"])
    require(len(factors) == k, "factor dimension")
    expected = tensor(factors)
    before = {}
    values = set()
    for cell, value in certificate["assignments"]:
        point = tuple(cell)
        require(len(point) == k and all(x in labels for x in point), "cell outside array")
        require(point not in before, "duplicate cell")
        require(value not in values and prime_trial(value) and value > 2, "entry duplicate or nonprime")
        before[point] = value
        values.add(value)
    require(set(before) == set(expected), "wrong stage support")
    # An independent count of all odd primes up to the largest entry proves
    # membership in the exact first n^k odd-prime pool, without materializing it.
    max_entry = max(values)
    entry_rank = sum(prime_trial(x) for x in range(3, max_entry + 1, 2))
    require(entry_rank <= n ** k, "entry outside prescribed pool")
    after = dict(before)
    touched = set()
    for left, right in certificate["switch_pairs"]:
        a, b = tuple(left), tuple(right)
        require(a != b and a in before and b in before, "invalid pair cells")
        require(a not in touched and b not in touched, "pair endpoints reused")
        require(abs(before[a] - before[b]) == gap, "inconsistent pair gap")
        touched.update((a, b))
        after[a], after[b] = after[b], after[a]
    require(touched == set(before), "omitted stage pair")
    actual = {point: after[point] - before[point] for point in before}
    require(actual == {point: gap * sign for point, sign in expected.items()}, "wrong checkerboard orientation")
    require(set(after.values()) == values, "entry permutation")
    require(sparse_signature(actual, k) ==
            {line: gap * value for line, value in formula_signature(factors).items()},
            "full signed-line image")
    return actual


def generic_axis_stage(k, d, kind, stage_number=0):
    """Diagnostic stage in centered coordinates; d is one-based."""
    require(2 <= d <= k, "stage dimension")
    if kind == "aggregate":
        require(d >= 3, "aggregate has at least two free inner coordinates")
        native = (0, 1)
        outer = tuple(2 + j for j in range(k - d))
        start = k + 3 + stage_number * (d - 1)
        factors = [(start + i,) for i in range(d - 1)] + [native]
        factors += [(x,) for x in outer]
    elif kind == "tensor":
        # Centers, opposite endpoints, and repeated coordinate-orbit values
        # deliberately occur in the native graph footprint.
        factors = [((0, 1) if i % 3 == 0 else
                    ((1, -1) if i % 3 == 1 else (1, 2)))
                   for i in range(d - 1)]
        factors += [(k + 3 + stage_number,)]
        factors += [(2 + j,) for j in range(k - d)]
    else:
        raise ValueError("unknown stage kind")
    return tuple(factors)


def majority_stage(k, varying, signs, stage_number=0):
    """Generic selector times graph-product footprint on its complement."""
    require(len(varying) == len(signs) and signs[0] == 1, "normalized native signs")
    r = len(varying)
    start = 2 * k + 5 + stage_number * (r + 1)
    factors = [None] * k
    for offset, (axis, sign) in enumerate(zip(varying, signs)):
        factors[axis] = (sign * start, sign * (start + offset + 1))
    for offset, axis in enumerate(i for i in range(k) if i not in varying):
        factors[axis] = ((0, 1) if offset % 2 == 0 else (1, -1))
    return tuple(factors)


def axis_signature(delta, k):
    return {line: value for line, value in sparse_signature(delta, k).items()
            if len(line[0]) == 1}


def axis_sums(array, k):
    out = [defaultdict(int) for _ in range(k)]
    for point, value in array.items():
        for direction in range(k):
            key = tuple(point[i] for i in range(k) if i != direction)
            out[direction][key] += value
    return [dict(values) for values in out]


def section_total(array, fixed):
    return sum(value for point, value in array.items()
               if all(point[i] == v for i, v in fixed.items()))


def add_tensor(array, factors, scalar):
    for point, sign in tensor(factors).items():
        array[point] += scalar * sign


def prefix_coefficients(values, labels, rank, modulus=None):
    """Integral path-product inverse; valid over composite residue rings."""
    result = {}
    for edges in product(range(len(labels) - 1), repeat=rank):
        total = sum(values[point]
                    for point in product(*(labels[:i + 1] for i in edges)))
        result[edges] = total if modulus is None else total % modulus
    return result


def numeric_axis_control(k, n, seed, gap=None):
    """Checks all 2k-3 levels algebraically; supports may overlap here.

    With gap, correct only residues using actual stage multipliers 2 mod gap.
    Without gap, perform exact integer correction. Neither is a physical
    disjoint-controller fixture; intermediate values may cease to be prime.
    """
    labels = interval(n)
    cells = list(product(labels, repeat=k))
    pool = first_odd_primes(len(cells))
    rng = Random(seed)
    start, desired = pool[:], pool[:]
    rng.shuffle(start)
    rng.shuffle(desired)
    array, target = dict(zip(cells, start)), dict(zip(cells, desired))
    target_axes = axis_sums(target, k)
    ring = None if gap is None else gap // 2
    require(gap is None or type(gap) is int and gap > 0 and gap % 2 == 0, "residue gap")
    passed_levels = 0

    def divided(value):
        if gap is None:
            return value
        require(value % 2 == 0, "odd divided discrepancy")
        return value // 2

    def scalar(value):
        return value if gap is None else 2 * (value % ring)

    def same(left, right):
        return left == right if gap is None else (left - right) % gap == 0

    for d in range(k - 1, 1, -1):
        for outer in product(labels, repeat=k - d - 1):
            fixed = dict(zip(range(d + 1, k), outer))
            demands = {}
            for x in labels:
                f = fixed | {d: x}
                demands[(x,)] = divided(section_total(target, f) - section_total(array, f))
            for (edge,), coefficient in prefix_coefficients(demands, labels, 1, ring).items():
                factors = [(labels[0],)] * d + [(labels[edge], labels[edge + 1])]
                factors += [(x,) for x in outer]
                add_tensor(array, factors, scalar(coefficient))
            for x in labels:
                f = fixed | {d: x}
                require(same(section_total(array, f), section_total(target, f)), "aggregate recurrence")
        passed_levels += 1

    for outer in product(labels, repeat=k - 2):
        for varied, native in ((0, 1), (1, 0)):
            actual = axis_sums(array, k)[native]
            demands = {}
            for x in labels:
                point = [labels[0]] * k
                point[varied] = x
                point[2:] = outer
                key = tuple(point[i] for i in range(k) if i != native)
                demands[(x,)] = divided(target_axes[native][key] - actual[key])
            for (edge,), coefficient in prefix_coefficients(demands, labels, 1, ring).items():
                factors = [(labels[0],), (labels[0],)] + [(x,) for x in outer]
                factors[varied] = (labels[edge], labels[edge + 1])
                add_tensor(array, factors, scalar(coefficient))
    current = axis_sums(array, k)
    for native in (0, 1):
        require(all(same(value, target_axes[native][point]) for point, value in current[native].items()),
                "horizontal recurrence")
    passed_levels += 1

    for d in range(2, k):
        for outer in product(labels, repeat=k - d - 1):
            actual = axis_sums(array, k)[d]
            demands = {point: divided(target_axes[d][point + outer] - actual[point + outer])
                       for point in product(labels, repeat=d)}
            for axis in range(d):
                for fixed in product(labels, repeat=d - 1):
                    total = 0
                    for x in labels:
                        point = fixed[:axis] + (x,) + fixed[axis:]
                        total += demands[point]
                    require(total == 0 if ring is None else total % ring == 0, "tensor compatibility")
            for edges, coefficient in prefix_coefficients(demands, labels, d, ring).items():
                factors = [(labels[e], labels[e + 1]) for e in edges]
                factors += [(labels[0],)] + [(x,) for x in outer]
                add_tensor(array, factors, scalar(coefficient))
        current = axis_sums(array, k)
        for native in range(d + 1):
            require(all(same(value, target_axes[native][point]) for point, value in current[native].items()),
                    "higher tensor recurrence")
        passed_levels += 1
    require(passed_levels == 2 * k - 3, "wrong level count")
    require(sum(array.values()) == sum(pool), "total conservation")
    return passed_levels


def expect_rejection(callback):
    try:
        callback()
    except (ValueError, KeyError, TypeError):
        return
    raise AssertionError("negative control incorrectly accepted")


def run_checks():
    report = {"scope": "finite controller controls, not the all-signed-lines theorem"}
    rng = Random(20261102)
    signature_cases = 0
    line_counts = {}
    # Independently enumerate every line at feasible orders, including k=5,6.
    for k, n in ((2, 3), (2, 5), (3, 3), (3, 5), (4, 3), (5, 3), (6, 3)):
        lines = enumerate_lines_independently(k, n)
        line_counts[f"k{k}-n{n}"] = len(lines)
        labels = interval(n)
        for _ in range(8):
            factors = []
            for _axis in range(k):
                if rng.randrange(3) == 0:
                    factors.append((rng.choice(labels),))
                else:
                    a, b = rng.sample(labels, 2)
                    factors.append((a, b))
            delta = tensor(factors)
            direct = {line: sum(delta.get(point, 0) for point in cells)
                      for line, cells in lines.items()}
            direct = {line: value for line, value in direct.items() if value}
            require(direct == sparse_signature(delta, k) == formula_signature(factors), "independent signature")
            signature_cases += 1

    physical_cases = 0
    whole_bundles = 0
    example = None
    for k in range(2, 7):
        for d in range(2, k + 1):
            for kind in ("tensor", "aggregate"):
                if kind == "aggregate" and d == 2:
                    continue
                factors = generic_axis_stage(k, d, kind)
                m = max(abs(x) for factor in factors for x in factor)
                n = 2 * m + 1
                certificate = physical_certificate(factors, n)
                physical_cases += 1
                example = certificate
                signature = formula_signature(factors)
                require(not any(len(line[0]) == k for line in signature), "full body moved")
                if kind == "tensor":
                    require(not any(line[0][0] < d - 1 for line in signature if len(line[0]) == 1),
                            "older axis moved")
                else:
                    require(not any(line[0] == (d - 1,) for line in signature), "transfer axis moved")
                # A nonaxis signed line cannot meet two stages of this bundle.
                touched = defaultdict(set)
                for stage in range(3):
                    points = tensor(generic_axis_stage(k, d, kind, stage))
                    for point in points:
                        for varying, signs in block_directions(k):
                            if len(varying) == 1:
                                continue
                            t = point[varying[0]]
                            if all(point[i] == sign * t for i, sign in zip(varying, signs)):
                                touched[line_key(varying, signs, point)].add(stage)
                require(all(len(stages) <= 1 for stages in touched.values()), "whole-reservoir freshness")
                whole_bundles += 1

        # The complete 2^k tensor uses 2^(k-1) real equal-gap prime pairs.
        factors = tuple((1, i + 2) for i in range(k))
        certificate = physical_certificate(factors, 2 * (k + 1) + 1)
        physical_cases += 1
        image = formula_signature(factors)
        require(not any(len(line[0]) == 1 for line in image), "full checkerboard changes axis")
        bodies = {line: value for line, value in image.items() if len(line[0]) == k}
        require(len(bodies) == 1 and next(iter(bodies.values())) == 1, "unit body selector")

    numerical_cases = 0
    level_counts = {}
    for k in range(2, 7):
        level_counts[str(k)] = numeric_axis_control(k, 3, 8100 + k)
        numerical_cases += 1
        for gap in (2, 6, 12, 30):
            numeric_axis_control(k, 3, 8200 + k, gap)
            numerical_cases += 1

    majority_cases = 0
    majority_physical = 0
    majority_bundle_cases = 0
    for k in range(2, 7):
        seen_sizes = set()
        for varying, signs in block_directions(k):
            r = len(varying)
            if r <= k // 2 or r < 2:
                continue
            factors = majority_stage(k, varying, signs)
            image = sparse_signature(tensor(factors), k)
            require(image == formula_signature(factors), "majority full signature")
            native = {line: value for line, value in image.items()
                      if line[0] == varying and line[1] == signs}
            require(native, "missing majority native image")
            for line in image:
                require(len(line[0]) != 1, "majority stage changes an axis")
                if len(line[0]) >= r:
                    require(line[0] == varying and line[1] == signs, "majority triangular preservation")
            fixed = tuple(i for i in range(k) if i not in varying)
            footprint = tensor(tuple(factors[i] for i in fixed))
            actual_native = {tuple(v for _, v in line[2]): value for line, value in native.items()}
            require(actual_native == footprint, "majority native tensor")
            majority_cases += 1
            if r not in seen_sizes:
                seen_sizes.add(r)
                m = max(abs(x) for factor in factors for x in factor)
                verify_physical(physical_certificate(factors, 2 * m + 1))
                majority_physical += 1
                touched = defaultdict(set)
                for stage in range(3):
                    stage_factors = majority_stage(k, varying, signs, stage)
                    for point in tensor(stage_factors):
                        for moving, pattern in block_directions(k):
                            t = point[moving[0]]
                            if all(point[i] == sign * t for i, sign in zip(moving, pattern)):
                                key = line_key(moving, pattern, point)
                                if moving == varying and pattern == signs:
                                    continue
                                touched[key].add(stage)
                require(all(len(stages) <= 1 for stages in touched.values()),
                        "majority nonnative whole-reservoir freshness")
                majority_bundle_cases += 1

    # Below the strict majority boundary a complementary family can move.
    # This is a counterexample to extending the preservation contract blindly.
    factors = ((10, 11), (10, 12), (10, 13), (1, 2), (1, 3), (1, 4))
    below = formula_signature(factors)
    require(any(line[0] == (3, 4, 5) for line in below), "missing complementary spill counterexample")

    negatives = 0
    corruptions = []
    c = deepcopy(example)
    c["kind"] = "full-prime-arrangement"
    corruptions.append(c)
    c = deepcopy(example)
    c["assignments"][1] = (c["assignments"][1][0], c["assignments"][0][1])
    corruptions.append(c)
    c = deepcopy(example)
    c["assignments"][0] = (c["assignments"][0][0], 9)
    corruptions.append(c)
    c = deepcopy(example)
    c["gap"] += 2
    corruptions.append(c)
    c = deepcopy(example)
    c["switch_pairs"].append(c["switch_pairs"][0])
    corruptions.append(c)
    c = deepcopy(example)
    c["switch_pairs"].pop()
    corruptions.append(c)
    c = deepcopy(example)
    next(factor for factor in c["factors"] if len(factor) == 2).reverse()
    corruptions.append(c)
    c = deepcopy(example)
    c["assignments"].append(c["assignments"][0])
    corruptions.append(c)
    for corrupted in corruptions:
        expect_rejection(lambda corrupted=corrupted: verify_physical(corrupted))
        negatives += 1
    expect_rejection(lambda: tensor(((1, 1), (2, 3))))
    negatives += 1
    # Reusing a common center is not a unit body selector.
    center_image = formula_signature(((0, 1), (0, 2), (0, 3), (0, 4)))
    require(sum(len(line[0]) == 4 for line in center_image) == 8, "central selector counterexample")
    # Identical pair factors give coefficient 2 at even rank and 0 at odd rank.
    for k in (3, 4, 5, 6):
        image = formula_signature(tuple((1, 2) for _ in range(k)))
        key = tuple(range(k)), (1,) * k, ()
        require(image.get(key, 0) == 1 + (-1) ** k, "repeated-pair counterexample")

    report.update({
        "independent_line_counts": line_counts,
        "complete_signature_cases": signature_cases,
        "actual_partial_prime_trade_cases": physical_cases,
        "whole_reservoir_intersection_cases": whole_bundles,
        "numeric_recurrence_and_composite_residue_cases": numerical_cases,
        "majority_complete_signature_cases": majority_cases,
        "majority_actual_partial_prime_trade_cases": majority_physical,
        "majority_whole_reservoir_cases": majority_bundle_cases,
        "nonmajority_complementary_spill_counterexamples": 1,
        "level_counts_by_dimension": level_counts,
        "rejected_corruptions": negatives,
        "central_and_repeated_pair_negative_patterns": 5,
    })
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", type=Path, help="independently replay a retained partial trade")
    parser.add_argument("--write-physical", type=Path, help="write one genuine partial hypercuboid trade")
    parser.add_argument("--dimension", type=int, default=5)
    args = parser.parse_args()
    require(not (args.verify and args.write_physical), "choose one certificate mode")
    if args.verify:
        certificate = json.loads(args.verify.read_text())
        changed = verify_physical(certificate)
        print(json.dumps({"kind": "partial-prime-controller", "changed_cells": len(changed),
                          "verified": True, "full_arrangement": False}, sort_keys=True))
    elif args.write_physical:
        k = args.dimension
        require(k >= 2, "dimension")
        factors = tuple((1, i + 2) for i in range(k))
        certificate = physical_certificate(factors, 2 * (k + 1) + 1)
        args.write_physical.write_text(json.dumps(certificate, sort_keys=True, indent=2) + "\n")
        print(json.dumps({"kind": certificate["kind"], "path": str(args.write_physical),
                          "dimension": k, "pairs": len(certificate["switch_pairs"]),
                          "full_arrangement": False}, sort_keys=True))
    else:
        print(json.dumps(run_checks(), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
