#!/usr/bin/env python3
"""All-fixed-dimension signed-line target controls, not array certificates.

All primality and exact-pool checks are finite.  The producer uses a sieve;
the target checker trial-divides independently.  No finite test certifies the
asymptotic prime-counting hypotheses, eventual incidence saturation, or an
arrangement of the pool.  Standard library only, Python >=3.11.
"""
from __future__ import annotations

import argparse
import copy
from collections import Counter
from fractions import Fraction
from functools import reduce
from itertools import combinations, product
import json
from math import comb, gcd, isqrt
from pathlib import Path
import random
from typing import Iterable


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def nozero_weight(r: int, s: int) -> int:
    """Number of r-tuples on a fixed set of s nonzero absolute labels."""
    return sum((-1) ** (s - j) * comb(s, j) * (2 * j) ** r
               for j in range(s + 1))


def zero_weight(r: int, s: int) -> int:
    """Number of r-tuples on {0} plus a fixed set of s nonzero labels."""
    return sum((-1) ** (s - j) * comb(s, j)
               * ((1 + 2 * j) ** r - (2 * j) ** r)
               for j in range(s + 1))


def label_weight(r: int, labels: tuple[int, ...]) -> int:
    require(r >= 1 and 1 <= len(labels) <= r, "invalid weight domain")
    require(tuple(sorted(set(labels))) == labels and labels[0] >= 0,
            "labels must be a nonempty ordinary sorted set")
    return zero_weight(r, len(labels) - 1) if 0 in labels else nozero_weight(r, len(labels))


def v2(r: int) -> int:
    require(r > 0, "positive valuation input required")
    return (r & -r).bit_length() - 1


def reserve_gcd(r: int) -> int:
    require(r >= 1, "positive tensor degree required")
    return 2 if r % 2 else 2 ** min(r, 2 + v2(r))


def weight_classes(r: int) -> list[tuple[bool, int, int]]:
    return ([(False, s, nozero_weight(r, s)) for s in range(1, r + 1)]
            + [(True, s, zero_weight(r, s)) for s in range(r)])


def all_label_sets(r: int, m: int) -> list[tuple[int, ...]]:
    return [S for size in range(1, min(r, m + 1) + 1)
            for S in combinations(range(m + 1), size)]


def nearest_in_class(x: Fraction, residue: int, modulus: int) -> int:
    require(modulus >= 1, "positive modulus required")
    residue %= modulus
    t = (x - residue) / modulus
    floor = t.numerator // t.denominator
    return min((residue + modulus * floor, residue + modulus * (floor + 1)),
               key=lambda z: (abs(Fraction(z) - x), z))


def centered_finish(r: int, m: int, mu: Fraction, residual: int) -> tuple[int, ...]:
    """Exact integral K16, with invalid parity/congruence rejected."""
    require(r >= 1 and m >= 1, "positive r,m required")
    if r == 1:
        require((residual - 2 * m) % 4 == 0, "wrong one-list residue")
        return (residual // 2,)
    a, b, D = 2 ** r, 3 ** r - 2 ** r - 1, reserve_gcd(r)
    require((residual - (a + b) * m) % (2 * D) == 0,
            "wrong two-list residue")
    A, B = a // D, b // D
    H = (residual - (a + b) * m) // (2 * D)
    v_residue = 0 if A == 1 else (pow(B, -1, A) * H) % A
    v = nearest_in_class((m * mu - m) / 2, v_residue, A)
    S_b = m + 2 * v
    require((residual - b * S_b) % a == 0, "internal integral failure")
    S_a = (residual - b * S_b) // a
    require(S_a % 2 == m % 2 and S_b % 2 == m % 2, "internal parity failure")
    require(a * S_a + b * S_b == residual, "internal exact-sum failure")
    return S_a, S_b


# A canonical line is (varying coordinate tuple, normalized signs, fixed values).
# Fixed values are listed in increasing order of the complementary coordinates.
Line = tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]


def canonical_lines(k: int, n: int) -> list[Line]:
    require(k >= 2 and n >= 3 and n % 2, "k>=2, odd n>=3 required")
    I = range(-(n // 2), n // 2 + 1)
    ans = []
    for size in range(1, k + 1):
        for varying in combinations(range(k), size):
            for tail in product((-1, 1), repeat=size - 1):
                signs = (1,) + tail
                for fixed in product(I, repeat=k - size):
                    ans.append((varying, signs, fixed))
    return ans


def cells_of_line(k: int, n: int, line: Line) -> frozenset[tuple[int, ...]]:
    varying, signs, fixed = line
    comp = tuple(j for j in range(k) if j not in varying)
    ans = []
    for t in range(-(n // 2), n // 2 + 1):
        cell = [0] * k
        for j, sign in zip(varying, signs):
            cell[j] = sign * t
        for j, value in zip(comp, fixed):
            cell[j] = value
        ans.append(tuple(cell))
    return frozenset(ans)


def independent_line_sets(k: int, n: int) -> set[frozenset[tuple[int, ...]]]:
    """Independent coordinate-function enumeration, then geometric deduplication."""
    m = n // 2
    I = tuple(range(-m, m + 1))
    choices = tuple((0, a) for a in I) + ((1, 0), (-1, 0))
    ans = set()
    for functions in product(choices, repeat=k):
        if all(slope == 0 for slope, _ in functions):
            continue
        cells = frozenset(tuple(slope * t + intercept for slope, intercept in functions)
                          for t in I)
        ans.add(cells)
    return ans


def line_label_from_cells(cells: frozenset[tuple[int, ...]]) -> tuple[int, ...]:
    require(bool(cells), "empty cell set")
    k = len(next(iter(cells)))
    fixed_values = []
    for j in range(k):
        values = {c[j] for c in cells}
        if len(values) == 1:
            fixed_values.append(abs(next(iter(values))))
    return tuple(sorted(set(fixed_values))) or (0,)


def line_value(line: Line, q: dict[tuple[int, ...], int]) -> int:
    return q[tuple(sorted(set(abs(v) for v in line[2]))) or (0,)]


def normalize_line(varying: tuple[int, ...], signs: tuple[int, ...],
                   fixed_by_coordinate: dict[int, int], k: int) -> Line:
    require(bool(varying) and len(varying) == len(signs), "bad varying block")
    orientation = signs[0]
    normal = tuple(orientation * s for s in signs)
    fixed = tuple(fixed_by_coordinate[j] for j in range(k) if j not in varying)
    return varying, normal, fixed


def check_partitions(k: int, n: int, values: dict[Line, int]) -> int:
    """All disjoint nonempty block partitions, not only axis marginals."""
    I = tuple(range(-(n // 2), n // 2 + 1))
    masks = range(1, 1 << k)
    checked = 0
    for mask_a in masks:
        A = tuple(i for i in range(k) if mask_a >> i & 1)
        for mask_b in range(mask_a + 1, 1 << k):
            if mask_a & mask_b:
                continue
            B = tuple(i for i in range(k) if mask_b >> i & 1)
            C = tuple(i for i in range(k) if not (mask_a | mask_b) >> i & 1)
            for sign_a_tail in product((-1, 1), repeat=len(A) - 1):
                sign_a = (1,) + sign_a_tail
                for sign_b_tail in product((-1, 1), repeat=len(B) - 1):
                    sign_b = (1,) + sign_b_tail
                    for fixed in product(I, repeat=len(C)):
                        base = dict(zip(C, fixed))
                        left = right = 0
                        for t in I:
                            cb = dict(base)
                            cb.update((j, s * t) for j, s in zip(B, sign_b))
                            ca = dict(base)
                            ca.update((j, s * t) for j, s in zip(A, sign_a))
                            left += values[normalize_line(A, sign_a, cb, k)]
                            right += values[normalize_line(B, sign_b, ca, k)]
                        require(left == right, "broken signed partition identity")
                        checked += 1
    return checked


def is_prime_trial(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    return all(value % divisor for divisor in range(3, isqrt(value) + 1, 2))


def sieve(bound: int) -> list[int]:
    flags = bytearray(b"\x01") * (bound + 1)
    if bound >= 0:
        flags[0] = 0
    if bound >= 1:
        flags[1] = 0
    for p in range(2, isqrt(bound) + 1):
        if flags[p]:
            flags[p * p:bound + 1:p] = b"\x00" * ((bound - p * p) // p + 1)
    return [i for i in range(2, bound + 1) if flags[i]]


def first_odd_primes_sieve(count: int) -> list[int]:
    bound = max(32, count * 8)
    while True:
        primes = sieve(bound)[1:]
        if len(primes) >= count:
            return primes[:count]
        bound *= 2


def first_odd_primes_trial(count: int) -> list[int]:
    ans = []
    candidate = 3
    while len(ans) < count:
        if is_prime_trial(candidate):
            ans.append(candidate)
        candidate += 2
    return ans


def floor_power_three_fifths(x: Fraction) -> int:
    lo, hi = 0, 1
    while hi ** 5 * x.denominator ** 3 <= x.numerator ** 3:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** 5 * x.denominator ** 3 <= x.numerator ** 3:
            lo = mid
        else:
            hi = mid
    return lo


def list_sums(primes: list[int], length: int, center: Fraction) -> dict[int, tuple[int, ...]]:
    """A finite search aid; this does not implement or claim FL at small n."""
    if length == 1:
        return {p: (p,) for p in primes}
    ans = {}
    anchors = sorted(primes, key=lambda p: (abs(p - center), p))[:3]
    for anchor in anchors:
        prefix = (anchor,) * (length - 2)
        prefix_sum = sum(prefix)
        for i, p in enumerate(primes):
            for q in primes[i:]:
                ans.setdefault(prefix_sum + p + q, prefix + (p, q))
    return ans


def make_certificate(k: int, n: int) -> dict:
    require(k >= 2 and n >= 3 and n % 2, "k>=2 and odd n>=3 required")
    r, m = k - 1, n // 2
    pool = first_odd_primes_sieve(n ** k)
    T = sum(pool)
    mu = Fraction(T, n ** r)
    radius = floor_power_three_fifths(mu)
    primes = [p for p in sieve(int(mu + radius) + 1) if abs(p - mu) <= radius and p > 2]
    require(bool(primes), "no finite prime candidates in target window")
    lower = max((p for p in primes if p <= mu), default=0)
    upper = min((p for p in primes if p >= mu), default=0)
    require(lower and upper, "no finite bracket primes")
    q = {}
    discrepancy = Fraction(0)
    labels = all_label_sets(r, m)
    bulk = [S for S in labels if S != (0,)
            and not (len(S) == 1 and S[0] != 0)
            and not (r >= 2 and len(S) == 2 and S[0] == 0)]
    for S in bulk:
        p = lower if discrepancy >= 0 else upper
        q[S] = p
        discrepancy += label_weight(r, S) * (p - mu)
    bulk_sum = sum(label_weight(r, S) * p for S, p in q.items())
    sums = list_sums(primes, m, mu)
    a, D = 2 ** r, reserve_gcd(r)
    b = 3 ** r - 2 ** r - 1 if r >= 2 else 0
    center_residue = (T - bulk_sum - (a + b) * m) % (2 * D)
    centers = sorted((p for p in primes if p % (2 * D) == center_residue),
                     key=lambda p: (abs(p - mu), p))
    found = None
    for p0 in centers:
        residual = T - bulk_sum - p0
        if r == 1:
            if residual % a == 0 and residual // a in sums:
                found = (p0, sums[residual // a], ())
                break
        else:
            for S_b in sorted(sums, key=lambda z: (abs(z - m * mu), z)):
                rest = residual - b * S_b
                if rest % a == 0 and rest // a in sums:
                    found = (p0, sums[rest // a], sums[S_b])
                    break
            if found:
                break
    require(found is not None, "finite search failed (not an impossibility claim)")
    p0, list_a, list_b = found
    q[(0,)] = p0
    for j, p in enumerate(list_a, 1):
        q[(j,)] = p
    for j, p in enumerate(list_b, 1):
        q[(0, j)] = p
    return {
        "kind": "signed-line-prime-target-vector",
        "dimension": k,
        "order": n,
        "pool": "exact-first-n^k-odd-primes",
        "pool_total": T,
        "line_count": ((n + 2) ** k - n ** k) // 2,
        "rule": "ordinary-set-of-absolute-fixed-labels; empty-uses-{0}",
        "q": [{"labels": list(S), "prime": q[S]} for S in sorted(q)],
        "scope": "prime targets satisfying all two-block partitions; not an integer lift or arrangement",
    }


def check_certificate(cert: dict, independent_geometry: bool = True) -> dict:
    require(cert.get("kind") == "signed-line-prime-target-vector", "wrong certificate kind")
    k, n = cert["dimension"], cert["order"]
    require(type(k) is int and type(n) is int and k >= 2 and n >= 3 and n % 2,
            "invalid dimension/order")
    require(cert.get("pool") == "exact-first-n^k-odd-primes", "wrong pool specification")
    require(cert.get("rule") == "ordinary-set-of-absolute-fixed-labels; empty-uses-{0}",
            "wrong full-line target rule")
    r, m = k - 1, n // 2
    pool = first_odd_primes_trial(n ** k)
    T = sum(pool)
    require(cert["pool_total"] == T, "incorrect exact pool total")
    q = {}
    for item in cert["q"]:
        S = tuple(item["labels"])
        require(all(type(x) is int for x in S), "nonintegral label")
        require(S not in q, "duplicate label set")
        p = item["prime"]
        require(type(p) is int and p > 2 and is_prime_trial(p), "composite/nonodd target")
        q[S] = p
    require(set(q) == set(all_label_sets(r, m)), "omitted or invalid label set")
    total = sum(label_weight(r, S) * p for S, p in q.items())
    require(total == T, "wrong weighted target total")
    denominator = n ** r
    # |p-T/denominator| <= (T/denominator)^(3/5), exactly.
    require(all(abs(p * denominator - T) ** 5 <= T ** 3 * denominator ** 2
                for p in q.values()), "target outside declared mu^(3/5) window")
    lines = canonical_lines(k, n)
    expected_count = ((n + 2) ** k - n ** k) // 2
    require(len(lines) == expected_count == cert["line_count"], "incorrect line count")
    values = {line: line_value(line, q) for line in lines}
    if independent_geometry:
        sets = {cells_of_line(k, n, L) for L in lines}
        independently = independent_line_sets(k, n)
        require(len(sets) == len(lines), "duplicate canonical line")
        require(sets == independently, "incomplete/signed geometric enumeration")
        require(all(q[line_label_from_cells(cells)]
                    == values[line] for line in lines
                    for cells in (cells_of_line(k, n, line),)),
                "fixed-label decoding disagrees")
    require(all(sum(value for line, value in values.items() if line[0] == (axis,)) == T
                for axis in range(k)), "incorrect directional total")
    checked = check_partitions(k, n, values)
    return {"dimension": k, "order": n, "pool_size": n ** k,
            "pool_total": T, "target_variables": len(q), "lines": len(lines),
            "partition_identities": checked,
            "certificate_kind": cert["kind"], "integer_lift_checked": False,
            "arrangement_checked": False}


def rejected(action) -> None:
    try:
        action()
    except (ValueError, KeyError, TypeError):
        return
    raise AssertionError("negative control was incorrectly accepted")


def self_test() -> dict:
    weights = 0
    for r in range(1, 8):
        for m in range(1, 4):
            actual = Counter(tuple(sorted(set(abs(t) for t in coords)))
                             for coords in product(range(-m, m + 1), repeat=r))
            expected = {S: label_weight(r, S) for S in all_label_sets(r, m)}
            assert actual == expected
            assert sum(expected.values()) == (2 * m + 1) ** r
            weights += len(expected)
    for r in range(1, 65):
        classes = weight_classes(r)
        values = [w for zero, s, w in classes if not (zero and s == 0)]
        assert reduce(gcd, values) == reserve_gcd(r)
        assert all(w <= (2 * r) ** r for _, _, w in classes)
        if r >= 2:
            assert gcd(2 ** r, 3 ** r - 2 ** r - 1) == reserve_gcd(r)
    assert [nozero_weight(3, 1), zero_weight(3, 1), nozero_weight(3, 2),
            zero_weight(3, 2), nozero_weight(3, 3)] == [8, 18, 48, 24, 48]
    rng = random.Random(20261102)
    arithmetic = 0
    for r in range(1, 65):
        a = 2 ** r
        b = 3 ** r - 2 ** r - 1 if r >= 2 else 0
        D = reserve_gcd(r)
        for _ in range(50):
            m = rng.randrange(1, 100)
            mu = Fraction(rng.randrange(1, 10 ** 8), rng.randrange(1, 200))
            R = nearest_in_class((a + b) * m * mu + rng.randrange(-10000, 10000),
                                 (a + b) * m, 2 * D)
            totals = centered_finish(r, m, mu, R)
            assert totals[0] % 2 == m % 2
            if r >= 2:
                S_a, S_b = totals
                assert S_b % 2 == m % 2
                assert a * S_a + b * S_b == R
                assert abs(S_b - m * mu) <= a // D
                eps = (a + b) * m * mu - R
                assert abs(S_a - m * mu) <= abs(eps) / a + b // D
            else:
                assert a * totals[0] == R
            rejected(lambda r=r, m=m, mu=mu, R=R: centered_finish(r, m, mu, R + 2))
            arithmetic += 1
    geometries = []
    for k, n in [(2, 3), (3, 3), (4, 3), (5, 3), (6, 3), (2, 5), (3, 5), (4, 5)]:
        lines = canonical_lines(k, n)
        sets = {cells_of_line(k, n, L) for L in lines}
        assert len(lines) == len(sets) == ((n + 2) ** k - n ** k) // 2
        assert sets == independent_line_sets(k, n)
        q = {S: rng.randrange(-1000, 1000) for S in all_label_sets(k - 1, n // 2)}
        values = {L: line_value(L, q) for L in lines}
        identities = check_partitions(k, n, values)
        corrupt = dict(values)
        axis_line = next(L for L in lines if len(L[0]) == 1)
        corrupt[axis_line] += 1
        rejected(lambda: check_partitions(k, n, corrupt))
        if k >= 4:
            corrupt = dict(values)
            pair_line = next(L for L in lines if len(L[0]) == 2)
            corrupt[pair_line] += 1
            rejected(lambda: check_partitions(k, n, corrupt))
        if k == 4:
            # A zero-margin perturbation preserves every axis value and the
            # pair-family marginals, but breaks a complementary-pair trace.
            corrupt = dict(values)
            native = (0, 1)
            for x, y in product((0, 1), repeat=2):
                corrupt[(native, (1, 1), (x, y))] += (-1) ** (x + y)
            for x in range(-(n // 2), n // 2 + 1):
                assert sum(corrupt[(native, (1, 1), (x, y))]
                           - values[(native, (1, 1), (x, y))]
                           for y in range(-(n // 2), n // 2 + 1)) == 0
                assert sum(corrupt[(native, (1, 1), (y, x))]
                           - values[(native, (1, 1), (y, x))]
                           for y in range(-(n // 2), n // 2 + 1)) == 0
            assert sum(corrupt[(native, (1, 1), (t, t))]
                       - values[(native, (1, 1), (t, t))]
                       for t in range(-(n // 2), n // 2 + 1)) == 2
            rejected(lambda: check_partitions(k, n, corrupt))
        # Missing negative slopes loses required diagonals, even at small order.
        unsigned = {cells_of_line(k, n, L) for L in lines if all(s == 1 for s in L[1])}
        assert unsigned < sets
        geometries.append({"k": k, "n": n, "lines": len(lines), "partitions": identities})
    certificates = []
    for k, n in [(2, 3), (3, 3), (4, 3), (5, 3), (6, 3), (4, 5), (5, 5), (6, 5)]:
        cert = make_certificate(k, n)
        certificates.append(check_certificate(cert))
        corruptions = []
        bad = copy.deepcopy(cert); bad["pool_total"] += 2; corruptions.append(bad)
        bad = copy.deepcopy(cert); bad["q"][0]["prime"] = 9; corruptions.append(bad)
        bad = copy.deepcopy(cert); bad["q"].pop(); corruptions.append(bad)
        bad = copy.deepcopy(cert); bad["q"].append(copy.deepcopy(bad["q"][0])); corruptions.append(bad)
        bad = copy.deepcopy(cert); bad["line_count"] -= 1; corruptions.append(bad)
        bad = copy.deepcopy(cert); bad["rule"] = "unsigned-lines-only"; corruptions.append(bad)
        bad = copy.deepcopy(cert); bad["kind"] = "prime-array-arrangement"; corruptions.append(bad)
        for bad in corruptions:
            rejected(lambda bad=bad: check_certificate(bad, independent_geometry=False))
    return {"weight_entries_checked": weights, "gcd_dimensions_checked": 64,
            "exact_centered_completions": arithmetic, "geometry": geometries,
            "target_certificates": certificates,
            "negative_target_certificates_rejected": 7 * len(certificates),
            "status": "finite controls only; no asymptotic or arrangement certification"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("self-test")
    make = sub.add_parser("make")
    make.add_argument("dimension", type=int)
    make.add_argument("order", type=int)
    make.add_argument("output", type=Path)
    check = sub.add_parser("check")
    check.add_argument("input", type=Path)
    args = parser.parse_args()
    if args.command == "self-test":
        print(json.dumps(self_test(), indent=2))
    elif args.command == "make":
        cert = make_certificate(args.dimension, args.order)
        result = check_certificate(cert)
        args.output.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps(check_certificate(json.loads(args.input.read_text(encoding="utf-8"))), indent=2))


if __name__ == "__main__":
    main()
