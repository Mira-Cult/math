#!/usr/bin/env python3
"""Exact subset rank-sampling and interpolation component regressions.

These finite tests supplement the proof in docs/TRIMMED_CODED_FOLD.md.
They do not implement or formally verify the asymptotic GapCVP compiler.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from check_packed_two_level_fold import BinaryField, Quad


def polynomial_value(coeff, x, field):
    value = 0
    for c in reversed(coeff):
        value = field.mul(value, x) ^ c
    return value


def matrix_rank(values, rows, cols, multiplication):
    if not any(values):
        return 0
    # All enumerated shapes have at most two rows or at most two columns.
    for i, j in itertools.combinations(range(rows), 2):
        for a, b in itertools.combinations(range(cols), 2):
            if (multiplication[values[i * cols + a]][values[j * cols + b]]
                    ^ multiplication[values[i * cols + b]][values[j * cols + a]]):
                return 2
    return 1


def rank_family(field, extension, degree, alphabet, shape, subset_sizes):
    polynomials = list(itertools.product(alphabet, repeat=degree + 1))
    samples = [tuple(polynomial_value(p, x, field) for x in range(field.size))
               for p in polynomials]
    targets = [polynomial_value(p, extension.z, extension) for p in polynomials]
    subsets = [s for size in subset_sizes
               for s in itertools.combinations(range(field.size), size)]
    mf = [[field.mul(x, y) for y in range(field.size)] for x in range(field.size)]
    me = [[extension.mul(x, y) for y in range(extension.size)]
          for x in range(extension.size)]
    rows, cols = shape
    cases = matrices = equality = 0
    minimum_slack = None
    for selection in itertools.product(range(len(polynomials)), repeat=rows * cols):
        ranks = [matrix_rank([samples[p][x] for p in selection], rows, cols, mf)
                 for x in range(field.size)]
        target_rank = matrix_rank([targets[p] for p in selection], rows, cols, me)
        for subset in subsets:
            charge = sum(ranks[x] for x in subset)
            slack = charge - (len(subset) - degree) * target_rank
            assert slack >= 0, (selection, subset, ranks, target_rank)
            minimum_slack = slack if minimum_slack is None else min(minimum_slack, slack)
            equality += slack == 0
            cases += 1
        matrices += 1
    return dict(base_field=field.size, extension_field=extension.size,
                degree=degree, coefficient_alphabet=list(alphabet), shape=list(shape),
                subset_sizes=list(subset_sizes), matrices=matrices,
                subset_rank_checks=cases, equality_cases=equality,
                minimum_slack=minimum_slack)


def interpolation_basis(points, field):
    basis = []
    for i, a in enumerate(points):
        polynomial, denominator = [1], 1
        for j, b in enumerate(points):
            if i == j:
                continue
            product = [0] * (len(polynomial) + 1)
            for k, c in enumerate(polynomial):
                product[k] ^= field.mul(c, b)
                product[k + 1] ^= c
            polynomial = product
            denominator = field.mul(denominator, a ^ b)
        inverse = field.inv(denominator)
        basis.append([field.mul(c, inverse) for c in polynomial])
    return basis


def interpolate(values, basis, field):
    result = [0] * len(basis)
    for y, p in zip(values, basis):
        for j, c in enumerate(p):
            result[j] ^= field.mul(y, c)
    return result


def interpolation_checks():
    accepted = rejected = 0
    for degree, field in [(1, BinaryField(2, 7)), (2, BinaryField(3, 11))]:
        extension = Quad(field)
        for points in itertools.combinations(range(field.size), 2 * degree):
            basis = interpolation_basis(points, field)
            # Exhaust coefficients in the degree-one case. In degree two use
            # the complete binary basis of the allowed polynomial space.
            if degree == 1:
                inputs = list(itertools.product(range(field.size), repeat=2))
            else:
                inputs = []
                for j in range(degree + 1):
                    for bit in range(field.degree):
                        p = [0] * (degree + 1)
                        p[j] = 1 << bit
                        inputs.append(tuple(p))
            for p in inputs:
                values = [polynomial_value(p, x, field) for x in points]
                recovered = interpolate(values, basis, field)
                assert recovered[:len(p)] == list(p)
                assert not any(recovered[len(p):])
                assert polynomial_value(recovered, extension.z, extension) == \
                    polynomial_value(p, extension.z, extension)
                accepted += 1
            if degree == 2:
                p = [0, 0, 0, 1]
                values = [polynomial_value(p, x, field) for x in points]
                recovered = interpolate(values, basis, field)
                assert recovered[3] == 1  # Emitted high-degree equation rejects it.
                rejected += 1

    field, points, p = BinaryField(2, 7), (0, 1), [1, 1]
    extension = Quad(field)
    values = [polynomial_value(p, x, field) for x in points]
    new_interpolant = interpolate(values, interpolation_basis(points, field), field)
    zero_extended = values + [0, 0]
    old_interpolant = interpolate(zero_extended,
                                 interpolation_basis(tuple(range(4)), field), field)
    assert new_interpolant == p
    assert any(old_interpolant[2:])
    new_value = polynomial_value(new_interpolant, extension.z, extension)
    old_value = polynomial_value(old_interpolant, extension.z, extension)
    assert new_value != old_value
    return dict(allowed_polynomials=accepted, rejected_degree_three_words=rejected,
                recompile_example=dict(field=4, selected_points=list(points),
                    measured_values=values, selected_interpolant=new_interpolant,
                    zero_extended_full_interpolant=old_interpolant,
                    selected_extension_value=new_value,
                    zero_extended_extension_value=old_value))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    f4, f8 = BinaryField(2, 7), BinaryField(3, 11)
    families = [
        rank_family(f4, Quad(f4), 1, range(4), (2, 2), (2, 3, 4)),
        rank_family(f4, Quad(f4), 1, range(2), (2, 3), (2, 3, 4)),
        rank_family(f4, Quad(f4), 1, range(2), (3, 2), (2, 3, 4)),
        rank_family(f8, Quad(f8), 2, range(2), (2, 2), (4,)),
    ]
    certificate = dict(schema='cvp.trimmed-sampling.v1', status='PASS',
                       scope='Exact finite component regressions, not a formal proof.',
                       rank_families=families, interpolation=interpolation_checks())
    data = (json.dumps(certificate, indent=2, sort_keys=True) + '\n').encode()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(data)
    print(json.dumps(dict(status='PASS',
        rank_checks=sum(x['subset_rank_checks'] for x in families),
        sha256=hashlib.sha256(data).hexdigest()), sort_keys=True))


if __name__ == '__main__':
    main()
