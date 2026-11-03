#!/usr/bin/env python3
"""Reviewer-owned controls of frozen incidence revision 5692d37633ef4b509e8429cddf4ed762e7235d08.

Author: /root/incidence_review, a nonauthor of the reviewed source.
Run with the root of a git archive of that revision as its sole argument.
Finite diagnostics only; no prime arrangement or all-k proof certification.
"""

from collections import Counter
from copy import deepcopy
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
from random import Random
import sys


FROZEN = "5692d37633ef4b509e8429cddf4ed762e7235d08"
HASHES = {
    "manuscripts/hyperk_incidence.md": "fd2ab35b539415ac65a132b7fddfb6acaa87b5af65f579f9eb64f27cc7e403d8",
    "code/hyperk_incidence.py": "8b2bbd2e88fdbfeb5461f6b85e1bd39626df8d4b6caa0818816aff99bd47283e",
    "code/signed_incidence.py": "aeabf8bc33a9e3816f58f0467e101e5af4fa070c95c8feda77fa1ada4fa69bd3",
    "code/signed_kernel_certificate.py": "b6de0cdcac1d7a99b1cbbb259f4e451875e996dea426bb78a2381f35018850f4",
    "inputs/hyperk-incidence-k2-n3.json": "357877230eab7c8d9b466ef850328fc89187c8f9598d7e703e9539162144ae3c",
    "inputs/hyperk-incidence-k3-n3.json": "b49805b8649dcb1e70e669123538d47ee90aa7e76a7141f6c97a4f940fedc3e7",
    "inputs/hyperk-incidence-k4-n3.json": "055e42623d46600d28e10cdfd638afe46d95f341991b05ff5d3614613a8ce4da",
    "inputs/hyperk-incidence-k5-n3.json": "77e162ddb094afdba6a5b9d87deecc41f446f6907c15ef5075cdcb17cea9e73a",
    "inputs/hyperk-incidence-k6-n3.json": "f244dae242e0385fd61183ad114aa27b5362fb393328f34190e191bb66a992b6",
}


def direct_geometry(k, n):
    """Independent moving/fixed-word geometry, retaining canonical keys."""
    values = tuple(range(-(n // 2), n // 2 + 1))
    result = {}
    for mask in range(1, 1 << k):
        moving = tuple(i for i in range(k) if mask & (1 << i))
        fixed_indices = tuple(i for i in range(k) if i not in moving)
        for signs in product((-1, 1), repeat=len(moving)):
            if signs[0] < 0:
                continue
            for fixed in product(values, repeat=len(fixed_indices)):
                cells = []
                for t in values:
                    x = dict(zip(fixed_indices, fixed))
                    x.update({i: s * t for i, s in zip(moving, signs)})
                    cells.append(tuple(x[i] for i in range(k)))
                result[moving, signs, fixed] = tuple(cells)
    return result


def direct_sums(geometry, array):
    return {key: sum(array.get(x, 0) for x in cells) for key, cells in geometry.items()}


def nonsymmetric_targets(h, k, n, rng):
    """Axis targets from an arbitrary array; proper diagonal lists reshuffled freely."""
    geometry = direct_geometry(k, n)
    values = tuple(range(-(n // 2), n // 2 + 1))
    seed_array = {x: rng.randrange(-7, 8) for x in product(values, repeat=k)}
    y = direct_sums(geometry, seed_array)
    if k == 3:
        for block, signs in h.signed_blocks(k, 2):
            if len(block) != 2:
                continue
            keys = [(block, signs, (t,)) for t in values]
            total = sum(y[key] for key in keys)
            for key in keys[:-1]:
                y[key] = rng.randrange(-200, 201)
            y[keys[-1]] = total - sum(y[key] for key in keys[:-1])
    for key in y:
        if len(key[0]) == k:
            y[key] = rng.randrange(-500, 501)
    assert h.compatible(k, n, y)
    assert len({y[key] for key in y if len(key[0]) == k}) > 1
    return geometry, y


def reverse_divisor_lift(h, k, n, y):
    """Use the LAST available leading divisor, unlike the author's first."""
    blocks, labels, _, _ = h.marker_data(k)
    values = tuple(range(-(n // 2), n // 2 + 1))

    @lru_cache(None)
    def value(x):
        for block, signs in reversed(blocks):
            a = labels[block, signs]
            if not all(x[i] == s * a for i, s in zip(block, signs)):
                continue
            fixed = tuple(x[i] for i in range(k) if i not in block)
            total = y[block, signs, fixed]
            for t in values:
                if t == a:
                    continue
                changed = list(x)
                for i, s in zip(block, signs):
                    changed[i] = s * t
                total -= value(tuple(changed))
            return total
        return 0

    return {x: value(x) for x in product(values, repeat=k)}


def lift_controls(h):
    rng = Random(20261102)
    results = []
    for k, n in ((2, 9), (3, 27)):
        geometry, y = nonsymmetric_targets(h, k, n, rng)
        lift = h.integer_lift(k, n, y)
        assert direct_sums(geometry, lift) == y
        alternate = reverse_divisor_lift(h, k, n, y)
        assert alternate == lift
        residue, modulus = -4, n
        transformed = {key: n * residue + modulus * target for key, target in y.items()}
        congruent = h.congruence_lift(k, n, transformed, residue, modulus)
        assert direct_sums(geometry, congruent) == transformed
        assert all((x - residue) % modulus == 0 for x in congruent.values())
        bad = dict(transformed)
        body = next(key for key in bad if len(key[0]) == k)
        bad[body] += 1
        assert h.compatible(k, n, bad)  # Bodies participate in no PC relation.
        try:
            h.congruence_lift(k, n, bad, residue, modulus)
        except ValueError:
            pass
        else:
            raise AssertionError("incompatible entry residues accepted")
        results.append({"k": k, "n": n, "lines": len(geometry), "sup_lift": max(map(abs, lift.values()))})
    return results


def full_smith_controls(h, problem):
    """Independent full matrices; inherited reduction and independently inspected replay."""
    results = []
    for k, n in ((2, 3), (3, 3), (4, 3)):
        geometry = direct_geometry(k, n)
        cells = list(product(range(-1, 2), repeat=k))
        matrix = [[int(x in row) for x in cells] for row in geometry.values()]
        conditioned, prefix = h.unit_pivot_precondition(matrix)
        certificate = h.smith_certificate(conditioned)
        certificate["operations"] = prefix + certificate["operations"]
        assert h.verify_smith_certificate(matrix, certificate)
        retained = json.loads((problem / f"inputs/hyperk-incidence-k{k}-n3.json").read_text())
        assert len(certificate["diagonal"]) == retained["full_rank"]
        nonunits = Counter(x for x in certificate["diagonal"] if x > 1)
        assert nonunits == Counter(x for x in retained["diagonal"] if x > 1)
        for operation in (["ra", 0, 0, 1], ["ca", 0, 0, 1], ["rs", -1, 0], ["unknown", 0]):
            corrupted = deepcopy(certificate)
            corrupted["operations"].append(operation)
            assert not h.verify_smith_certificate(matrix, corrupted)
        corrupted = deepcopy(certificate)
        corrupted["diagonal"][-1] += 1
        assert not h.verify_smith_certificate(matrix, corrupted)
        mislabeled = deepcopy(retained)
        mislabeled["not_an_arrangement"] = False
        assert not h.verify_diagnostic(mislabeled)
        results.append({"k": k, "n": n, "rank": len(certificate["diagonal"]), "nonunits": dict(nonunits)})
    return results


def kernel_controls(h):
    k, n = 2, 11  # Contains unused positive orbit 5, as well as the center.
    geometry = direct_geometry(k, n)
    blocks, labels, _, _ = h.marker_data(k)
    markers = {s * a for a in labels.values() for s in (-1, 1)}
    pivots = []
    for x in product(range(-5, 6), repeat=k):
        if not any(all(x[i] == s * labels[block, signs] for i, s in zip(block, signs))
                   for block, signs in blocks):
            pivots.append(x)
    assert len(pivots) == n ** k - h.stable_rank(k, n)
    for v in pivots:
        vector = h.kernel_basis_vector(k, n, v)
        assert all(value == 0 for value in direct_sums(geometry, vector).values())
        assert all(vector.get(u, 0) == int(u == v) for u in pivots)
        assert all(all(x[i] == v[i] or x[i] in markers for i in range(k)) for x in vector)
    return {"k": k, "n": n, "checked_basis_vectors": len(pivots)}


def relabeled_selector_control(h):
    b = 3
    array, pairs, parameters = h.pure_selector(b, 0)
    alphabet = [3, 17, 2, 20, 8, 12, 5, 1, 19, 7, 10]
    assert len(alphabet) == parameters["positive_labels"]
    relabel = dict(enumerate(alphabet, 1))
    signs = (1, -1, -1)
    move = lambda x: tuple(s * relabel[t] for s, t in zip(signs, x))
    transformed = {move(x): value for x, value in array.items()}
    geometry = direct_geometry(b, 41)
    actual = {key: value for key, value in direct_sums(geometry, transformed).items() if value}
    assert actual == {(tuple(range(b)), signs, ()): 1}
    for plus, minus in pairs:
        a, z = move(plus), move(minus)
        assert transformed[a] == 1 and transformed[z] == -1
        assert a[1:] == z[1:] and a[0] != z[0]
    broken = dict(transformed)
    first = next(iter(broken))
    broken[first] *= -1
    assert {key: value for key, value in direct_sums(geometry, broken).items() if value} != actual
    return {"dimension": b, "n": 41, "body_signs": signs, "support": len(transformed)}


def compatible_rounding_control():
    """Exact-fraction MF fixture with a nonsaturated image lattice."""
    # A has row size n=2. Its image is {(a,b,c): a+b+c even}.
    image = lambda z: (z[0] + z[1], z[0] + z[2], z[1] + z[2])
    lift = lambda v: ((v[0] + v[1] - v[2]) / 2,
                      (v[0] + v[2] - v[1]) / 2,
                      (v[1] + v[2] - v[0]) / 2)
    close = lambda v: image(tuple(round(z) for z in lift(v)))
    v = (Fraction(3, 5), Fraction(2, 5), Fraction(2, 5))
    assert sum(round(x) for x in v) % 2 == 1
    assert sum(close(v)) % 2 == 0
    demands = [image(z) for z in [(3, -2, 1), (-4, 3, 1), (1, 1, -3), (0, -2, 1)]]
    assert tuple(map(sum, zip(*demands))) == (0, 0, 0)
    # Cycle edges i -> i+1; prefix flow has divergence demands; subtract its mean.
    p, delta, n = 4, 2, 2
    prefix, partial = [], [0, 0, 0]
    for demand in demands:
        partial = [a + b for a, b in zip(partial, demand)]
        prefix.append(tuple(partial))
    means = [Fraction(sum(f[j] for f in prefix), p) for j in range(3)]
    real = [tuple(Fraction(x) - mean for x, mean in zip(f, means)) for f in prefix]
    rounded = [close(f) for f in real]
    assert all(max(abs(a - b) for a, b in zip(f, g)) <= Fraction(n, 2)
               for f, g in zip(real, rounded))
    residual = [tuple(d - f + g for d, f, g in zip(demands[i], rounded[i], rounded[i-1]))
                for i in range(p)]
    assert all(sum(r) % 2 == 0 for r in residual)
    assert all(max(map(abs, r)) <= Fraction(delta * n, 2) for r in residual)
    correction, partial = [], [0, 0, 0]
    for r in residual[:-1]:
        partial = [a + b for a, b in zip(partial, r)]
        correction.append(tuple(partial))
    correction.append((0, 0, 0))
    assert max(abs(x) for f in correction for x in f) <= Fraction(delta * p * n, 4)
    final = [tuple(a + b for a, b in zip(f, c)) for f, c in zip(rounded, correction)]
    assert all(sum(f) % 2 == 0 for f in final)
    assert [tuple(a - b for a, b in zip(final[i], final[i-1])) for i in range(p)] == demands
    return {"lattice_index": 2, "vertices": p, "rounding_bound": n / 2,
            "repair_bound": delta * p * n / 4}


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: hyperk_incidence_controls.py ARCHIVE_ROOT")
    problem = Path(sys.argv[1]).resolve() / "problems/prime-arrays-beyond-square"
    for relative, digest in HASHES.items():
        assert sha256((problem / relative).read_bytes()).hexdigest() == digest, relative
    sys.path.insert(0, str(problem / "code"))
    import hyperk_incidence as h
    result = {"revision": FROZEN, "python": sys.version.split()[0],
              "source_hashes": "PASS", "lift": lift_controls(h),
              "full_matrix_smith": full_smith_controls(h, problem),
              "kernel": kernel_controls(h), "selector": relabeled_selector_control(h),
              "compatible_rounding": compatible_rounding_control(), "status": "PASS"}
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
