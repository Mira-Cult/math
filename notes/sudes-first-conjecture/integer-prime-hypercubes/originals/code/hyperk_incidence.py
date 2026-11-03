#!/usr/bin/env python3
"""Dimension-parametric integer incidence for full signed-coordinate lines.

This is an integer-array diagnostic, not a prime-permutation constructor.
The all-k proof is hyperk_incidence.md.  Smith certificates are finite data;
the inherited Smith checker replays only visibly unimodular operations.
Coordinates in this module are centered, and the center is not reflected
as a free two-element orbit.
"""

from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json
from math import comb, gcd, lcm
from pathlib import Path

from signed_incidence import smith_certificate, verify_smith_certificate
from signed_kernel_certificate import unit_pivot_precondition


def order(n):
    if type(n) is not int or n < 3 or n % 2 != 1:
        raise ValueError("odd integer n>=3 required")
    return tuple(range(-(n // 2), n // 2 + 1))


def dimension(k):
    if type(k) is not int or k < 1:
        raise ValueError("positive integer dimension required")
    return tuple(range(k))


def signed_blocks(k, minimum=1):
    coordinates = dimension(k)
    for size in range(minimum, k + 1):
        for block in combinations(coordinates, size):
            for tail in product((1, -1), repeat=size - 1):
                yield block, (1,) + tail


def complement(k, block):
    return tuple(i for i in dimension(k) if i not in block)


def line_keys(k, n):
    values = order(n)
    for block, signs in signed_blocks(k):
        for fixed in product(values, repeat=k - len(block)):
            yield block, signs, fixed


def line_cells(k, n, key):
    block, signs, fixed = key
    if (not block or tuple(sorted(set(block))) != tuple(block)
            or any(i not in dimension(k) for i in block)
            or len(signs) != len(block) or signs[0] != 1
            or any(s not in (-1, 1) for s in signs)
            or len(fixed) != k - len(block)):
        raise ValueError("malformed canonical line key")
    values = order(n)
    if any(c not in values for c in fixed):
        raise ValueError("fixed coordinate outside the cube")
    result = []
    for t in values:
        point = [None] * k
        for i, s in zip(block, signs):
            point[i] = s * t
        for i, c in zip(complement(k, block), fixed):
            point[i] = c
        result.append(tuple(point))
    return tuple(result)


def line_sets(k, n):
    return {key: frozenset(line_cells(k, n, key)) for key in line_keys(k, n)}


def independent_line_sets(k, n):
    """Geometry from fixed/forward/reversed words, without signed_blocks."""
    values = order(n)
    symbols = [("fixed", x) for x in values] + [("moving", 1), ("moving", -1)]
    found = set()
    for word in product(symbols, repeat=k):
        if all(kind == "fixed" for kind, _ in word):
            continue
        cells = frozenset(tuple(value if kind == "fixed" else value * t
                                for kind, value in word) for t in values)
        found.add(cells)
    return found


def point_lines(point):
    k = len(point)
    for block, signs in signed_blocks(k):
        t = point[block[0]]
        if all(point[i] == s * t for i, s in zip(block, signs)):
            yield block, signs, tuple(point[i] for i in complement(k, block))


def line_sums(k, n, array, complete=True):
    values = order(n)
    out = dict.fromkeys(line_keys(k, n), 0) if complete else {}
    for cell, value in array.items():
        if len(cell) != k or any(x not in values for x in cell) or type(value) is not int:
            raise ValueError("invalid integer array entry")
        if value:
            for key in point_lines(cell):
                out[key] = out.get(key, 0) + value
    return out if complete else {key: value for key, value in out.items() if value}


def partition_pairs(k):
    blocks = list(signed_blocks(k))
    for i, left in enumerate(blocks):
        for right in blocks[i + 1:]:
            if set(left[0]).isdisjoint(right[0]):
                yield left, right


def partition_residuals(k, n, targets):
    """Every displayed two-block identity, including dependent equations."""
    values = order(n)
    if set(targets) != set(line_keys(k, n)) or any(type(v) is not int for v in targets.values()):
        raise ValueError("one integer target for every canonical line is required")
    for left, right in partition_pairs(k):
        b, sigma = left
        c, tau = right
        remaining = complement(k, b + c)
        for fixed in product(values, repeat=len(remaining)):
            base = dict(zip(remaining, fixed))
            lhs = rhs = 0
            for t in values:
                point = dict(base)
                point.update(zip(c, (s * t for s in tau)))
                lhs += targets[(b, sigma, tuple(point[i] for i in complement(k, b)))]
                point = dict(base)
                point.update(zip(b, (s * t for s in sigma)))
                rhs += targets[(c, tau, tuple(point[i] for i in complement(k, c)))]
            yield (left, right, fixed), lhs - rhs


def compatible(k, n, targets):
    return all(value == 0 for _, value in partition_residuals(k, n, targets))


def axis_kernel_matrix(k, n):
    """Integral anchored basis -> noncentral coordinates of extra targets.

    Central target entries are recovered from zero coordinate margins.
    This does not discard any integer information after axes are lifted.
    """
    nonzero = tuple(x for x in order(n) if x)
    rows = [(block, signs, fixed) for block, signs in signed_blocks(k, 2)
            for fixed in product(nonzero, repeat=k - len(block))]
    row_index = {key: i for i, key in enumerate(rows)}
    columns = list(product(nonzero, repeat=k))
    matrix = [[0] * len(columns) for _ in rows]
    for j, u in enumerate(columns):
        for block, signs in signed_blocks(k, 2):
            alpha = (-1) ** len(block) + int(all(u[i] == s * u[block[0]]
                                                       for i, s in zip(block, signs)))
            if alpha:
                fixed = tuple(u[i] for i in complement(k, block))
                matrix[row_index[(block, signs, fixed)]][j] = alpha
    return rows, columns, matrix


def cuboid(pairs):
    if any(len(pair) != 2 or pair[0] == pair[1] for pair in pairs):
        raise ValueError("distinct endpoint pairs required")
    return {tuple(pair[bit] for pair, bit in zip(pairs, bits)): (-1) ** sum(bits)
            for bits in product((0, 1), repeat=len(pairs))}


def cuboid_signature(pairs):
    """Complete contraction formula, separate from point_lines enumeration."""
    k = len(pairs)
    factors = [{a: 1, b: -1} for a, b in pairs]
    result = {}
    for block, signs in signed_blocks(k):
        possible = {s * endpoint for i, s in zip(block, signs) for endpoint in pairs[i]}
        alpha = sum(_product(factors[i].get(s * t, 0) for i, s in zip(block, signs))
                    for t in possible)
        if alpha:
            remaining = complement(k, block)
            for fixed in product(*(pairs[i] for i in remaining)):
                value = alpha * _product(factors[i][x] for i, x in zip(remaining, fixed))
                if value:
                    result[(block, signs, fixed)] = value
    return result


def _product(values):
    answer = 1
    for value in values:
        answer *= value
    return answer


def marker_data(k):
    """Exact integer provisional weights, scaled by lcm(1,...,k)."""
    blocks = tuple(signed_blocks(k))
    scale = lcm(*range(1, k + 1))
    labels = {block: i + 1 for i, block in enumerate(blocks)}
    positive = {}
    for (block, signs), a in labels.items():
        for i, s in zip(block, signs):
            positive[i, s * a] = scale // len(block)
    return blocks, labels, positive, scale


def verify_marker_weights(k):
    blocks, labels, positive, scale = marker_data(k)
    occupied = set()
    worst_gap = None
    for key in blocks:
        block, signs = key
        a = labels[key]
        designated = {(i, s * a) for i, s in zip(block, signs)}
        if occupied & designated:
            raise AssertionError("leading monomials are not coprime")
        occupied.update(designated)
        for t in range(-len(blocks), len(blocks) + 1):
            weight = sum(positive.get((i, s * t), -k * scale)
                         for i, s in zip(block, signs))
            if t == a:
                assert weight == scale
            else:
                assert weight < scale
                gap = scale - weight
                worst_gap = gap if worst_gap is None else min(worst_gap, gap)
    assert worst_gap >= scale // k
    return {"k": k, "signed_blocks": len(blocks), "sufficient_odd_order": 3 ** k,
            "weight_scale": scale, "minimum_scaled_gap": worst_gap,
            "rewrite_depth_bound": k * k * (k + 1)}


def _chosen_divisor(k, cell, blocks, labels):
    for key in blocks:
        block, signs = key
        a = labels[key]
        if all(cell[i] == s * a for i, s in zip(block, signs)):
            return key
    return None


def integer_lift(k, n, targets, standard_values=None):
    """Exact monic integer lift; deliberately not a bounded physical lift.

    Arbitrary standard_values parametrizes the full integer array kernel.
    Requires the sufficient marker threshold, not just a low-dimensional
    rank computation.  The recursion never divides by n or a modulus.
    """
    if n < 3 ** k:
        raise ValueError("monic lift requires odd n>=3^k")
    values = order(n)
    if not compatible(k, n, targets):
        raise ValueError("broken partition compatibility")
    blocks, labels, positive, scale = marker_data(k)
    boundary = {} if standard_values is None else dict(standard_values)
    for cell, value in boundary.items():
        if (len(cell) != k or any(x not in values for x in cell)
                or _chosen_divisor(k, cell, blocks, labels) is not None
                or type(value) is not int):
            raise ValueError("boundary values must be integer standard cells")

    @lru_cache(None)
    def evaluate(cell):
        chosen = _chosen_divisor(k, cell, blocks, labels)
        if chosen is None:
            return boundary.get(cell, 0)
        block, signs = chosen
        a = labels[chosen]
        fixed = tuple(cell[i] for i in complement(k, block))
        answer = targets[(block, signs, fixed)]
        for t in values:
            if t != a:
                changed = list(cell)
                for i, s in zip(block, signs):
                    changed[i] = s * t
                answer -= evaluate(tuple(changed))
        return answer

    return {cell: evaluate(cell) for cell in product(values, repeat=k)}


def congruence_lift(k, n, targets, residue, modulus):
    if type(modulus) is not int or modulus < 1 or type(residue) is not int:
        raise ValueError("integer residue and positive modulus required")
    if any((value - n * residue) % modulus for value in targets.values()):
        raise ValueError("target residues do not permit entry residues")
    reduced = {key: (value - n * residue) // modulus for key, value in targets.items()}
    lifted = integer_lift(k, n, reduced)
    return {cell: modulus * value + residue for cell, value in lifted.items()}


def kernel_basis_vector(k, n, standard_cell):
    targets = dict.fromkeys(line_keys(k, n), 0)
    result = integer_lift(k, n, targets, {tuple(standard_cell): 1})
    return {cell: value for cell, value in result.items() if value}


def stable_kernel_polynomials(maximum):
    """Coefficient lists in ascending powers of n, via I11."""
    polynomials = [[1]]
    for k in range(maximum):
        out = [0] + polynomials[k][:]
        for j in range(k + 1):
            multiplier = comb(k, j) * 2 ** j
            for degree, coefficient in enumerate(polynomials[k - j]):
                out[degree] -= multiplier * coefficient
        polynomials.append(out)
    return polynomials


def polynomial_value(coefficients, n):
    return sum(value * n ** degree for degree, value in enumerate(coefficients))


def stable_rank(k, n):
    return n ** k - polynomial_value(stable_kernel_polynomials(k)[k], n)


def pure_selector_parameters(b):
    if type(b) is not int or b < 2:
        raise ValueError("pure selector needs b>=2")
    alpha = (1,) * (b - 1) + (-(b - 1),)
    maximum = b - 1
    common = lcm(*range(1, maximum + 1))
    p, q = common + 1, 2 * common + 1
    for size in range(1, b):
        for subset in combinations(range(b), size):
            coefficient = sum(alpha[i] for i in subset)
            assert 0 < abs(coefficient) <= maximum
            assert gcd(coefficient, p) == gcd(coefficient, q) == 1
    assert sum(alpha) == 0 and 2 * p - q == 1
    return {"dimension": b, "alpha": alpha, "lcm": common, "p": p, "q": q,
            "positive_labels": 2 * p + q,
            "pairs": 2 * p ** (b - 1) + q ** (b - 1),
            "support_cells": 4 * p ** (b - 1) + 2 * q ** (b - 1)}


def pure_selector(b, pair_coordinate=None):
    """Finite signed numeric template, two p copies minus one q copy.

    Returns sparse cell values and disjoint (+cell,-cell) pairs along
    pair_coordinate. It does not supply equal-gap prime entries.
    """
    parameters = pure_selector_parameters(b)
    if parameters["support_cells"] > 1000000:
        raise ValueError("enumeration budget exceeded; use exact parameter certificate")
    coordinate = b - 1 if pair_coordinate is None else pair_coordinate
    if type(coordinate) is not int or not 0 <= coordinate < b:
        raise ValueError("invalid pair coordinate")
    alpha = parameters["alpha"]
    remaining = tuple(i for i in range(b) if i != coordinate)
    array, pairs, offset = {}, [], 0
    for size, sign in [(parameters["p"], 1), (parameters["p"], 1),
                       (parameters["q"], -1)]:
        inverse = pow(alpha[coordinate], -1, size)
        for fixed in product(range(size), repeat=b - 1):
            total = sum(alpha[i] * x for i, x in zip(remaining, fixed))
            ends = []
            for target in (0, 1):
                cell = [None] * b
                for i, x in zip(remaining, fixed):
                    cell[i] = offset + x + 1
                cell[coordinate] = offset + ((target - total) * inverse) % size + 1
                cell = tuple(cell)
                assert cell not in array
                array[cell] = sign * (1 if target == 0 else -1)
                ends.append(cell)
            pairs.append(tuple(ends if sign == 1 else reversed(ends)))
        offset += size
    assert len(array) == parameters["support_cells"]
    assert len(pairs) == parameters["pairs"]
    assert len(set(cell for pair in pairs for cell in pair)) == len(array)
    return array, pairs, parameters


def smith_diagnostic(k, n):
    rows, columns, matrix = axis_kernel_matrix(k, n)
    conditioned, prefix = unit_pivot_precondition(matrix)
    suffix = smith_certificate(conditioned)
    certificate = {"shape": suffix["shape"], "diagonal": suffix["diagonal"],
                   "operations": prefix + suffix["operations"]}
    assert verify_smith_certificate(matrix, certificate)
    certificate.update({"kind": "hyperk-incidence-smith", "k": k, "n": n,
                        "full_line_count": ((n + 2) ** k - n ** k) // 2,
                        "full_rank": n ** k - (n - 1) ** k + len(certificate["diagonal"]),
                        "not_an_arrangement": True})
    return certificate


def verify_diagnostic(certificate):
    if (certificate.get("kind") != "hyperk-incidence-smith"
            or certificate.get("not_an_arrangement") is not True):
        return False
    k, n = certificate["k"], certificate["n"]
    _, _, matrix = axis_kernel_matrix(k, n)
    if certificate.get("full_line_count") != ((n + 2) ** k - n ** k) // 2:
        return False
    if certificate.get("full_rank") != n ** k - (n - 1) ** k + len(certificate["diagonal"]):
        return False
    return verify_smith_certificate(matrix, certificate)


def _structured_targets(k, n):
    out = {}
    for key in line_keys(k, n):
        fixed_labels = tuple(sorted({abs(x) for x in key[2]})) or (0,)
        out[key] = 1 + 2 * sum((i + 1) * (x + 3) ** 2 for i, x in enumerate(fixed_labels))
    return out


def self_test():
    geometric_cases = [(2, 3), (2, 5), (3, 3), (3, 5), (4, 3), (5, 3), (6, 3)]
    for k, n in geometric_cases:
        canonical = line_sets(k, n)
        independent = independent_line_sets(k, n)
        count = ((n + 2) ** k - n ** k) // 2
        assert len(canonical) == len(set(canonical.values())) == len(independent) == count
        assert set(canonical.values()) == independent
        assert set(list(canonical.values())[1:]) != independent  # omitted-line negative control
        target = _structured_targets(k, n)
        assert compatible(k, n, target)
        broken = dict(target)
        axis = next(key for key in broken if len(key[0]) == 1)
        broken[axis] += 2
        assert not compatible(k, n, broken)
    weights = [verify_marker_weights(k) for k in range(1, 7)]
    expected = {
        2: [-1, -2, 1], 3: [1, -3, -3, 1],
        4: [9, 4, -6, -4, 1], 5: [23, 45, 10, -10, -5, 1],
        6: [-25, 138, 135, 20, -15, -6, 1],
    }
    polynomials = stable_kernel_polynomials(6)
    for k, coefficients in expected.items():
        assert polynomials[k] == coefficients, (k, polynomials[k])
    for k in range(2, 7):
        n = 2 * (k + 2) + 1
        for pairs in [tuple((1, i + 2) for i in range(k)),
                      tuple(((-1) ** i, (-1) ** i * (i + 2)) for i in range(k)),
                      tuple((0, i + 1) for i in range(k))]:
            expected_signature = cuboid_signature(pairs)
            actual = line_sums(k, n, cuboid(pairs), complete=False)
            assert expected_signature == actual
            corrupted = dict(expected_signature)
            if corrupted:
                first = next(iter(corrupted))
                corrupted[first] += 1
                assert corrupted != actual
        pure_selector_parameters(k)
    for b in (2, 3, 4):
        for paired in range(b):
            selector, pairs, parameters = pure_selector(b, paired)
            n = 2 * parameters["positive_labels"] + 1
            body = (tuple(range(b)), (1,) * b, ())
            assert line_sums(b, n, selector, complete=False) == {body: 1}
            assert all(selector[plus] == 1 and selector[minus] == -1
                       and all(plus[i] == minus[i] for i in range(b) if i != paired)
                       for plus, minus in pairs)
    for k, n in [(2, 9), (3, 27)]:
        target = _structured_targets(k, n)
        lifted = integer_lift(k, n, target)
        assert line_sums(k, n, lifted) == target
        congruent_target = {key: n * 3 + n * value for key, value in target.items()}
        congruent = congruence_lift(k, n, congruent_target, 3, n)
        assert all(value % n == 3 % n for value in congruent.values())
        assert line_sums(k, n, congruent) == congruent_target
    for standard in [(0, 0), (-4, 3), (3, -3)]:
        vector = kernel_basis_vector(2, 9, standard)
        assert not line_sums(2, 9, vector, complete=False)
        assert len(vector) <= 3 ** 4
        assert vector[standard] == 1
    try:
        kernel_basis_vector(2, 9, (3, 3))
    except ValueError:
        pass
    else:
        raise AssertionError("a nonstandard cell was falsely accepted as a kernel pivot")
    smith_results = []
    for k, n in [(2, 3), (3, 3), (4, 3), (5, 3), (6, 3)]:
        retained = Path(__file__).resolve().parent.parent / "inputs" / f"hyperk-incidence-k{k}-n{n}.json"
        certificate = json.loads(retained.read_text()) if retained.exists() else smith_diagnostic(k, n)
        assert verify_diagnostic(certificate)
        smith_results.append({"k": k, "n": n, "full_rank": certificate["full_rank"],
                              "nonunit_factors": dict(Counter(x for x in certificate["diagonal"] if x > 1))})
        corrupted = dict(certificate)
        corrupted["diagonal"] = list(certificate["diagonal"])
        corrupted["diagonal"][-1] += 1
        assert not verify_diagnostic(corrupted)
    return {"geometry_cases": geometric_cases, "marker_cases": weights,
            "lift_cases": [[2, 9], [3, 27]], "smith_cases": smith_results,
            "pure_selector_dimensions": [2, 3, 4], "status": "PASS",
            "scope": "integer incidence and finite diagnostics, not prime arrangements"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("self-test")
    marker = sub.add_parser("markers")
    marker.add_argument("k", type=int)
    selector = sub.add_parser("selector")
    selector.add_argument("k", type=int)
    smith = sub.add_parser("smith")
    smith.add_argument("k", type=int)
    smith.add_argument("n", type=int)
    smith.add_argument("--output", type=Path)
    verify = sub.add_parser("verify")
    verify.add_argument("path", type=Path)
    args = parser.parse_args()
    if args.command == "self-test":
        result = self_test()
    elif args.command == "markers":
        result = verify_marker_weights(args.k)
    elif args.command == "selector":
        result = pure_selector_parameters(args.k)
    elif args.command == "smith":
        result = smith_diagnostic(args.k, args.n)
        if args.output:
            args.output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
            result = {"k": args.k, "n": args.n, "full_rank": result["full_rank"],
                      "nonunit_factors": dict(Counter(x for x in result["diagonal"] if x > 1)),
                      "output": str(args.output)}
    else:
        certificate = json.loads(args.path.read_text())
        if not verify_diagnostic(certificate):
            raise SystemExit("invalid incidence certificate")
        result = {"status": "PASS", "k": certificate["k"], "n": certificate["n"],
                  "full_rank": certificate["full_rank"]}
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
