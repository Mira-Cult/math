#!/usr/bin/env python3
"""Reviewer controls for PQ1/PF1, bound to an immutable scientific source.

The public adaptation reads bundled originals and checks their frozen digests.  The principal
independent oracles use primitive integer factorization, binary Frobenius/gcd,
Mobius inversion, and direct full signed-line enumeration.  They are finite
regressions supporting the proof review, not substitutes for the tail proofs.
"""

from __future__ import annotations

from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import gcd, isqrt
from pathlib import Path
import json
import subprocess
import types


SCIENCE = "e0cf4e8808f21c0633326f70f42a870086836320"
PREFIX = "problems/prime-array-consolidation/"
EXPECTED = {
    "manuscripts/polynomial_bound_transfer.md":
        "269829f323333396a8b6abd9db422bf142f7d3c869a0789c1eba2d0f94d5d739",
    "code/polynomial_bound_transfer.py":
        "a055792d25dc13567b15aa14eaab454b66eef100b22199c70f74cacbdc647e3c",
}


def load_candidate():
    root = Path(__file__).resolve().parents[1] / "originals"
    raw = {}
    for relative, digest in EXPECTED.items():
        name = PREFIX + relative
        raw[relative] = (root / {"manuscripts/polynomial_bound_transfer.md": "transfer.md",
                                 "code/polynomial_bound_transfer.py": "polynomial_bound_transfer.py"}[relative]).read_bytes()
        assert sha256(raw[relative]).hexdigest() == digest
    candidate = types.ModuleType("frozen_polynomial_candidate")
    exec(compile(raw["code/polynomial_bound_transfer.py"],
                 f"{SCIENCE}:polynomial_bound_transfer.py", "exec"),
         candidate.__dict__)
    return candidate


def mobius(value):
    parity = 0
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            value //= divisor
            parity ^= 1
            if value % divisor == 0:
                return 0
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        parity ^= 1
    return -1 if parity else 1


def mobius_shell(size):
    cumulative = 0
    degree = 0
    while cumulative < size:
        degree += 1
        previous = cumulative
        numerator = sum(mobius(d) * (1 << (degree // d))
                        for d in range(1, degree + 1) if degree % d == 0)
        assert numerator % degree == 0
        cumulative += numerator // degree
    return degree, previous, cumulative


def binary_mod(a, b):
    assert b
    while a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def binary_gcd(a, b):
    while b:
        a, b = b, binary_mod(a, b)
    return a


def binary_square_mod(a, modulus):
    square = 0
    shift = 0
    while a:
        if a & 1:
            square |= 1 << (2 * shift)
        shift += 1
        a >>= 1
    return binary_mod(square, modulus)


def frobenius_irreducible(f):
    """Rabin's criterion, independent of the producer's trial divisors."""
    degree = f.bit_length() - 1
    if degree < 1:
        return False
    if degree == 1:
        return True
    x = binary_mod(2, f)
    power = x
    prime_divisors = [p for p in range(2, degree + 1)
                      if degree % p == 0
                      and all(p % q for q in range(2, isqrt(p) + 1))]
    check_degrees = {degree // p for p in prime_divisors}
    for j in range(1, degree + 1):
        power = binary_square_mod(power, f)
        if j in check_degrees and binary_gcd(power ^ x, f) != 1:
            return False
    return power == x


def factorized_window(s, lower, multiplier):
    """Enumerate primitive linear factors and retain exact window members."""
    upper = lower + s
    root_bound = F(2, multiplier)
    assert lower == s * multiplier * multiplier
    outputs = set()
    for a in range(lower, upper + 1):
        for u in range(1, isqrt(a) + 1):
            if a % u:
                continue
            w = a // u
            vmax = (root_bound * u).__floor__()
            for v in range(-vmax, vmax + 1):
                if not v or gcd(u, abs(v)) != 1:
                    continue
                zmax = s // abs(v)
                for z in range(-zmax, zmax + 1):
                    if not z:
                        continue
                    b, c = u * z + v * w, v * z
                    if abs(b) <= s:
                        assert 0 < abs(c) <= s
                        outputs.add((a, b, c))
    return outputs


def window_oracle(candidate):
    rows = []
    author_rows = candidate.independent_window_oracle()
    for case, author in zip(((8, 32, 2), (16, 64, 2), (36, 324, 3)),
                            author_rows):
        s, lower, multiplier = case
        factored = factorized_window(*case)
        discriminants = set()
        examined = 0
        for a in range(lower, lower + s + 1):
            for b in range(-s, s + 1):
                for c in range(-s, s + 1):
                    if c == 0:
                        continue
                    examined += 1
                    disc = b * b - 4 * a * c
                    if disc >= 0 and isqrt(disc)**2 == disc:
                        discriminants.add((a, b, c))
        assert factored == discriminants
        assert len(factored) == author["nonzero_constant_reducibles"]
        m = isqrt(lower + s)
        bound = F(2, multiplier) * (
            4 * s * s * sum((F(1, j) for j in range(1, m + 1)), F())
            + 6 * s * m + m * (m + 1))
        assert len(factored) <= bound
        rows.append({"s": s, "examined": examined,
                     "factorization_and_discriminant_count": len(factored)})
    return rows


def all_signed_lines(n, d):
    for direction in product((-1, 0, 1), repeat=d):
        varying = [i for i in range(d) if direction[i]]
        if not varying or direction[varying[0]] != 1:
            continue
        fixed = [i for i in range(d) if not direction[i]]
        for constants in product(range(1, n + 1), repeat=len(fixed)):
            base = dict(zip(fixed, constants))
            cells = []
            for t in range(1, n + 1):
                cells.append(tuple(base[i] if not direction[i]
                                   else t if direction[i] > 0 else n + 1 - t
                                   for i in range(d)))
            yield tuple(varying), frozenset(cells)


def geometry_oracle():
    reports = []
    cases = [(9, 2), (11, 2), (5, 3), (7, 3), (7, 4),
             (9, 3), (9, 4), (9, 5)]
    for n, d in cases:
        a = tuple(range(1, d + 1))
        b = tuple(range(n - d + 1, n + 1))
        incident = {a: [], b: []}
        line_count = 0
        for varying, cells in all_signed_lines(n, d):
            line_count += 1
            for center in (a, b):
                if center in cells:
                    assert len(varying) == 1
                    incident[center].append(cells)
        assert line_count == ((n + 2)**d - n**d) // 2
        assert len(incident[a]) == len(incident[b]) == d
        astar = set().union(*incident[a])
        bstar = set().union(*incident[b])
        crossings = astar & bstar
        assert len(crossings) == (2 if d == 2 else 0)
        assert all(b not in cells for cells in incident[a])
        assert all(a not in cells for cells in incident[b])
        expected_used = 4 * n - 4 if d == 2 else 2 + 2 * d * (n - 1)
        assert len(astar | bstar) == expected_used
        reports.append({"n": n, "D": d, "all_lines_enumerated": line_count,
                        "guaranteed_lines": 2 * d, "crossings": len(crossings)})
    # This too-small endpoint has extra signed lines, not just the axes.
    a = (1, 2, 3, 4)
    extra = sum(a in cells and len(varying) >= 2
                for varying, cells in all_signed_lines(5, 4))
    assert extra > 0
    return reports, extra


def shell_and_invoice_oracle(candidate):
    cumulative = 0
    shells = []
    for degree in range(1, 13):
        count = sum(frobenius_irreducible(p)
                    for p in range(1 << degree, 1 << (degree + 1)))
        expected = sum(mobius(k) * (1 << (degree // k))
                       for k in range(1, degree + 1) if degree % k == 0) // degree
        assert count == expected
        cumulative += count
        assert mobius_shell(cumulative) == (
            degree, cumulative - count, cumulative)
        assert candidate.binary_shell(cumulative)["highest_degree"] == degree
        shells.append({"degree": degree, "frobenius_count": count})
    checked = 0
    for n in range(5, 62, 2):
        for d in range(2, min(8, (n + 1) // 2) + 1):
            row = candidate.binary_invoice(n, d)
            m, before, total = mobius_shell(n**d)
            assert row["highest_degree"] == m
            assert row["previous_complete_shell_total"] == before
            assert row["complete_shell_total"] == total
            w = 1 << (m - 1)
            if d == 2:
                k = 4 + 2 * (n % 4 == 3)
                core = (n * n - 2 * k - 1)**2 - (15 if k == 4 else 40) * w
                padding = (n - 2)**4 - 6 * w
                expected = core > 0 and n - k - 1 >= 0 and (
                    n - k - 1 == 0 or padding > 0)
                assert row["core_square"] - row["strict_core_requirement"] == core
                assert row["padding_square"] - row["strict_padding_requirement_when_needed"] == padding
                if n >= 9:
                    assert expected
            else:
                left = n**d - 2 - 2 * d * (n - 1)
                coefficient = 6 if n % 4 == 1 else 15
                expected = left > 0 and left * left > coefficient * w
                assert expected
                assert row["remaining_after_conservative_allocations"] == left
            assert row["sufficient_subsystem_invoice_passes"] == expected
            assert row["full_array_asserted"] is False
            checked += 1
    return shells, checked


def exact_controls(d, x):
    """Separate rational-power evaluation of the pre-controller budgets."""
    t = F(7 * x + 11 * d + 60, 10)
    u = 12 + F(7 * (d + 3) * x, 15)
    a = F(261, 10) + F(91 * d * x, 30)
    r = (3**d - 1) // 2
    n = 1 << x
    return (
        x >= 10,
        d * x >= 51,
        F(8 * a * a, t)**3 <= n**(2 * d - 3),
        n >= 128 * t,
        F(64 * 1808 * r)**6 <= n**(2 * d - 3),
        (F(8, 7) * 896 * 2_800_000 * r * u)**12 * t**15
        <= n**(4 * d - 3),
        F(n, 4096) >= 28 + F(11, 5) * d
        + (F(7, 2) + F(14, 15) * d) * x,
    )


def cutoff_oracle(candidate):
    dimensions = list(range(2, 31)) + [50, 100, 1000]
    rows = []
    compared = 0
    for d in dimensions:
        x = 10
        while not all(exact_controls(d, x)):
            assert tuple(candidate.cutoff_controls(d, x).values()) == exact_controls(d, x)
            compared += 1
            x += 1
        assert candidate.minimal_exponent(d) == x
        for offset in (0, 1, 2, 20):
            assert all(exact_controls(d, x + offset))
            assert tuple(candidate.cutoff_controls(d, x + offset).values()) == exact_controls(d, x + offset)
            compared += 1
        rows.append({"D": d, "least_controller_exponent": x})
    return rows, compared


def conditional_oracle():
    rows = []
    for n in (3, 5):
        pool = []
        p = 2
        while len(pool) < n * n:
            if frobenius_irreducible(p):
                pool.append(p)
            p += 1
        total = success = 0
        for rest in combinations(pool[1:], n - 1):
            value = 2
            for p in rest:
                value ^= p
            total += 1
            if frobenius_irreducible(value):
                assert value == 2 and 3 not in rest
                success += 1
        assert (n * n - 1) * success <= total
        rows.append({"n": n, "conditional_subsets": total, "successes": success})
    return rows


def main():
    candidate = load_candidate()
    windows = window_oracle(candidate)
    geometry, negative = geometry_oracle()
    shells, invoice_count = shell_and_invoice_oracle(candidate)
    cutoffs, control_count = cutoff_oracle(candidate)
    result = {
        "science": SCIENCE, "source_sha256": EXPECTED,
        "factorization_oracle": windows,
        "full_line_geometry_oracle": geometry,
        "too_small_geometry_extra_lines": negative,
        "frobenius_shell_oracle": shells,
        "independent_mobius_invoices": invoice_count,
        "exact_budget_comparisons": control_count,
        "linear_scan_exponents": cutoffs,
        "conditional_binary_oracle": conditional_oracle(),
        "status": "all independent finite controls passed",
        "scope": "proof-review regressions; no full large array constructed",
    }
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
