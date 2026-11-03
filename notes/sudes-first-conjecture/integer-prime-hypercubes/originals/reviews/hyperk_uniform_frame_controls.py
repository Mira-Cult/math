#!/usr/bin/env python3
"""Nonauthor exact controls of UF at c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb.

Author: /root/incidence_review. Usage: this file EXACT_ARCHIVE_ROOT.
Finite controls do not prove the dimension-parametric probability theorem.
"""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations, product
from pathlib import Path
from random import Random
import json
import sys


REVISION = "c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb"
HASHES = {
    "manuscripts/hyperk_full_controller.md": "38de54de8b5e5d751e9d700f689b9417b610019d56e170d47f209c86e2adbec6",
    "code/hyperk_full_controller.py": "ac6503a6d9db1282fc2dcf471e57a9e53f73959c7354f5d6c70edc9368a9cf65",
    "manuscripts/hyperk_incidence.md": "fd2ab35b539415ac65a132b7fddfb6acaa87b5af65f579f9eb64f27cc7e403d8",
    "code/hyperk_incidence.py": "8b2bbd2e88fdbfeb5461f6b85e1bd39626df8d4b6caa0818816aff99bd47283e",
    "manuscripts/hyperk_kernel_research.md": "c4dc2db4da2e502f0bc8d564e44c2f504b13e9e0fae7ae77b780cfdb70838f44",
    "code/hyperk_kernel_research.py": "4c96f78d90110752293dc798059f87c091b7d6578ea63c0734cc3541d3d2cc34",
    "code/hyperk_controller.py": "150d0d1b3d49bb4c8c134e8cd93622b3cabdc9dd14bd3d11d7f5f3eeb3112965",
}


def clean(a):
    return {x: z for x, z in a.items() if z}


def addto(a, b, multiplier=1):
    for x, z in b.items():
        a[x] += multiplier * z


def signed_blocks(d, minimum=1):
    for word in product((-1, 0, 1), repeat=d):
        block = tuple(i for i, s in enumerate(word) if s)
        if len(block) >= minimum and word[block[0]] == 1:
            yield block, tuple(word[i] for i in block)


def signature(a, d):
    sums = defaultdict(int)
    for block, signs in signed_blocks(d):
        for x, z in a.items():
            if all(x[i] == s * x[block[0]] for i, s in zip(block, signs)):
                sums[block, signs, tuple(x[i] for i in range(d) if i not in block)] += z
    return clean(sums)


def active(x, labels):
    return tuple(block for block, a in labels.items()
                 if all(x[i] == s * a for i, s in zip(*block)))


def change(x, block, t):
    y = list(x)
    for i, s in zip(*block):
        y[i] = s * t
    return tuple(y)


def independent_columns(d, n, labels):
    """Last-divisor division; all possible active-divisor transitions audited."""
    values = tuple(range(-(n // 2), n // 2 + 1))
    cells = tuple(product(values, repeat=d))
    marked = set(labels.values())
    checks = strict = 0
    for x in cells:
        old = active(x, labels)
        covered = [i for block, _ in old for i in block]
        assert len(covered) == len(set(covered))
        for block in old:
            for t in values:
                if t == labels[block]:
                    continue
                new = active(change(x, block, t), labels)
                assert len(new) <= len(old)
                if abs(t) not in marked:
                    assert len(new) < len(old)
                    strict += 1
                checks += 1

    @lru_cache(None)
    def nf(x):
        choices = active(x, labels)
        if not choices:
            return {x: 1}, 0, 0
        block = choices[-1]
        out, depth, nonmarkers = defaultdict(int), 0, 0
        for t in values:
            if t == labels[block]:
                continue
            polynomial, child_depth, child_nonmarkers = nf(change(x, block, t))
            addto(out, polynomial, -1)
            depth = max(depth, 1 + child_depth)
            nonmarkers = max(nonmarkers, int(abs(t) not in marked) + child_nonmarkers)
        assert depth <= d * d * (d + 1)
        assert nonmarkers <= len(choices)
        return clean(out), depth, nonmarkers

    columns = defaultdict(dict)
    for x in cells:
        for v, z in nf(x)[0].items():
            columns[v][x] = z
    return dict(columns), checks, strict


def exact_moments_and_variances(frozen):
    d, n = 2, 9
    cells = tuple(product(range(-4, 5), repeat=d))
    index = {x: i for i, x in enumerate(cells)}
    bases = []
    incoming = Counter()
    checks = strict = 0
    for injection in permutations(range(1, 5)):
        producer = frozen.NormalForm(d, n, injection)
        columns, checked, decreases = independent_columns(d, n, producer.labels)
        assert columns == producer.columns()
        for column in columns.values():
            assert not signature(column, d)
            incoming.update(column.keys())
        bases.append(columns)
        checks += checked
        strict += decreases
    unused_producer = frozen.NormalForm(2, 11, (5, 2, 4, 1))
    unused_columns, unused_checks, unused_strict = independent_columns(2, 11, unused_producer.labels)
    assert unused_columns == unused_producer.columns()
    count, size = len(bases), len(cells)
    means = [[0] * size for _ in cells]  # Each row is a column's mean numerator.
    second_left = [[0] * size for _ in cells]
    squared = [0] * size
    support_cap = coefficient_cap = 0
    for basis in bases:
        for v, column in basis.items():
            j = index[v]
            support_cap = max(support_cap, len(column))
            coefficient_cap = max(coefficient_cap, max(map(abs, column.values())))
            for x, a in column.items():
                i = index[x]
                means[j][i] += a
                squared[j] += a * a
                for y, b in column.items():
                    second_left[i][index[y]] += a * b
    covariance_left = [[count * second_left[i][j] - sum(v[i] * v[j] for v in means)
                        for j in range(size)] for i in range(size)]
    right = [Q(count * squared[j] - sum(x * x for x in means[j]), count * count)
             for j in range(size)]
    left_psd_upper = max(Q(sum(map(abs, row)), count) for row in second_left)
    left_covariance_row_bound = max(Q(sum(map(abs, row)), count * count)
                                   for row in covariance_left)
    G = Q(max(incoming.values()), count)
    assert max(right) <= support_cap * coefficient_cap ** 2
    assert left_psd_upper <= support_cap * coefficient_cap ** 2 * G
    # Abar fixes EVERY basis column, not just one test demand.
    for column in bases[0].values():
        for x in cells:
            result = sum(means[index[v]][index[x]] * z for v, z in column.items())
            assert result == count * column.get(x, 0)
    # A map can fix a selected demand while failing uniform reconstruction.
    roots = list(bases[0])
    v0, v1 = roots[:2]
    one_demand_operator = lambda a: clean({x: a.get(v0, 0) * z for x, z in bases[0][v0].items()})
    assert one_demand_operator(bases[0][v0]) == bases[0][v0]
    assert one_demand_operator(bases[0][v1]) != bases[0][v1]

    rng, T = Random(2026110301), 4096
    sample = [[0] * size for _ in cells]
    for v in cells:
        multiplicities = Counter(rng.randrange(count) for _ in range(T))
        for b, multiplicity in multiplicities.items():
            for x, z in bases[b].get(v, {}).items():
                sample[index[x]][index[v]] += multiplicity * z
    delta = [[count * sample[i][j] - T * means[j][i] for j in range(size)]
             for i in range(size)]
    norm_inf = Q(max(sum(map(abs, row)) for row in delta), T * count)
    norm_one = Q(max(sum(abs(delta[i][j]) for i in range(size)) for j in range(size)), T * count)
    assert norm_inf * norm_one < 1
    # Both variance sums are essential in general: independently signed e_0 e_j^*.
    left_probe = [[Q(0)] * 8 for _ in range(8)]
    right_probe = [[Q(0)] * 8 for _ in range(8)]
    for j in range(8):
        for sign in (-1, 1):
            matrix = [[0] * 8 for _ in range(8)]
            matrix[0][j] = sign
            for row in range(8):
                for col in range(8):
                    left_probe[row][col] += Q(sum(matrix[row][t] * matrix[col][t] for t in range(8)), 2)
                    right_probe[row][col] += Q(sum(matrix[t][row] * matrix[t][col] for t in range(8)), 2)
    assert all(left_probe[i][j] == (8 if i == j == 0 else 0) for i in range(8) for j in range(8))
    assert all(right_probe[i][j] == int(i == j) for i in range(8) for j in range(8))
    return {"d": d, "n": n, "all_marker_injections": count,
            "all_divisor_transitions": checks, "strict_nonmarker_decreases": strict,
            "unused_noncentral_orbit_case": {"n": 11, "transitions": unused_checks, "strict_decreases": unused_strict},
            "all_basis_vectors_fixed_by_mean": len(bases[0]),
            "max_expected_incoming_support": str(G),
            "right_variance_diagonal_norm": str(max(right)),
            "left_variance_absolute_row_bound": str(left_covariance_row_bound),
            "left_PSD_upper_absolute_row_bound": str(left_psd_upper),
            "fixed_sample_T": T, "fixed_sample_spectral_square_bound": str(norm_inf * norm_one),
            "one_variance_only_negative_control": {"left": 8, "right": 1}}


def exact_physical_expectation():
    """Exhaust every marker and every permitted auxiliary choice at d=1,n=9."""
    values, positives = tuple(range(-4, 5)), tuple(range(1, 5))
    expected = defaultdict(Q)
    column_cases = 0
    for v in values:
        for a in positives:
            if v == a:
                continue
            allowed = [b for b in positives if b not in {abs(v), a}]
            for b in allowed:
                probability = Q(1, 4 * len(allowed))
                for root in (v, a):
                    for x in (root, b):
                        expected[x] += probability
                column_cases += 1
    # The two templates share an anchor: count is 2 or 0, not two independent coins.
    q = Q(1, 3)
    actual_variance = 4 * q * (1 - q)
    false_independent_variance = 2 * q * (1 - q)
    assert actual_variance > false_independent_variance
    assert sum(expected.values()) == 32  # Eight expected nonzero KG columns, four incidences each.
    return {"d": 1, "n": 9, "auxiliary_outcomes": column_cases,
            "expected_template_incidence_by_cell": {str(x): str(expected[x]) for x in values},
            "shared_anchor_count_variance": str(actual_variance),
            "incorrect_independent_template_variance": str(false_independent_variance)}


def tensor(factors, d):
    out = {}
    for entries in product(*(tuple(a.items()) for _, a in factors)):
        point, z = [None] * d, 1
        for (coords, _), (x, coefficient) in zip(factors, entries):
            for i, t in zip(coords, x):
                assert point[i] is None
                point[i] = t
            z *= coefficient
        assert None not in point and tuple(point) not in out
        out[tuple(point)] = z
    return clean(out)


def partitions(d):
    blocks = tuple(signed_blocks(d, 2))
    yield ()
    for size in range(1, d // 2 + 1):
        for pi in combinations(blocks, size):
            covered = [i for block, _ in pi for i in block]
            if len(covered) == len(set(covered)):
                yield pi


def own_physicalize(column, d, frozen, offset):
    excluded = {abs(t) for x in column for t in x}
    cursor = offset

    def labels(count):
        nonlocal cursor
        out = []
        while len(out) < count:
            if cursor not in excluded:
                out.append(cursor)
                excluded.add(cursor)
            cursor += 1
        return out

    anchors = labels(d)
    selectors = {}
    for block, signs in signed_blocks(d, 2):
        q, count = frozen.pure_selector(len(block))
        alphabet = labels(count)
        selectors[block, signs] = {
            tuple(s * alphabet[t - 1] for s, t in zip(signs, x)): z for x, z in q.items()}
    templates = []
    for root, coefficient in column.items():
        out = {}
        for pi in partitions(d):
            if not all(all(root[i] == s * root[block[0]] for i, s in zip(block, signs))
                       for block, signs in pi):
                continue
            covered = {i for block, _ in pi for i in block}
            factors = [(block, selectors[block, signs]) for block, signs in pi]
            factors += [((i,), {(root[i],): 1, (anchors[i],): -1})
                        for i in range(d) if i not in covered]
            term = tensor(factors, d)
            assert set(out).isdisjoint(term)
            out.update({x: (-1) ** len(pi) * z for x, z in term.items()})
        assert set(out.values()) <= {-1, 1} and not signature(out, d)
        for i in range(d):
            fibers = defaultdict(lambda: [0, 0])
            for x, z in out.items():
                fibers[tuple(x[j] for j in range(d) if j != i)][z < 0] += 1
            assert all(positive == negative for positive, negative in fibers.values())
        templates.append((coefficient, out))
    recovered = defaultdict(int)
    for coefficient, template in templates:
        addto(recovered, template, coefficient)
    assert clean(recovered) == column
    return templates


def physicalization_and_rounding(frozen):
    d, n, standard = 3, 27, (0, 0, 0)
    form = frozen.NormalForm(d, n, tuple(range(1, 14)))
    values = tuple(range(-13, 14))

    @lru_cache(None)
    def coefficient(x):
        divisors = active(x, form.labels)
        if not divisors:
            return int(x == standard)
        block = divisors[-1]
        return -sum(coefficient(change(x, block, t)) for t in values if t != form.labels[block])

    column = clean({x: coefficient(x) for x in product(values, repeat=d)})
    assert column == form.one_column(standard)
    assert not signature(column, d) and max(map(abs, column.values())) == 3
    first = own_physicalize(column, d, frozen, 40)
    second = own_physicalize(column, d, frozen, 400)
    real_image, rounded, degrees = defaultdict(Q), defaultdict(int), Counter()
    for integer_coefficient, template in first + second:
        c = Q(integer_coefficient, 2)
        addto(real_image, template, c)
        rounded_c = (c + Q(1, 2)).numerator // (c + Q(1, 2)).denominator
        addto(rounded, template, rounded_c)
        degrees.update(template.keys())
    assert clean(real_image) == column
    remainder = defaultdict(int, column)
    addto(remainder, rounded, -1)
    remainder = clean(remainder)
    assert all(type(z) is int for z in remainder.values())
    assert not signature(remainder, d)
    assert max(map(abs, remainder.values()), default=0) <= Q(max(degrees.values()), 2)
    # Entrywise rounding does not preserve even the one-dimensional kernel.
    bad = [Q(49, 100), Q(49, 100), Q(-98, 100)]
    assert sum(bad) == 0 and sum(round(x) for x in bad) != 0
    return {"d": d, "KG_support": len(column), "KG_max_coefficient": 3,
            "unit_templates_per_physicalization": len(first),
            "rounded_remainder_norm": max(map(abs, remainder.values()), default=0),
            "rounding_pointdegree_bound": str(Q(max(degrees.values()), 2))}


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: hyperk_uniform_frame_controls.py EXACT_ARCHIVE_ROOT")
    problem = Path(sys.argv[1]).resolve() / "problems/prime-arrays-beyond-square"
    for path, digest in HASHES.items():
        assert sha256((problem / path).read_bytes()).hexdigest() == digest, path
    sys.path.insert(0, str(problem / "code"))
    import hyperk_full_controller as frozen
    results = {"revision": REVISION, "python": sys.version.split()[0],
               "variance_and_uniformity": exact_moments_and_variances(frozen),
               "physical_expectation": exact_physical_expectation(),
               "physicalization_rounding": physicalization_and_rounding(frozen), "status": "PASS"}
    print(json.dumps(results, sort_keys=True))


if __name__ == "__main__":
    main()
