#!/usr/bin/env python3
"""Exact arithmetic regressions for the coded-fold uniform parameter schedule.

Large L values are virtual ceil(log2(source length)); no source, extension
field, or affine table is instantiated. These tests check parameter arithmetic,
not source soundness or the proof of asymptotic termination.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def ceil_log2(a: int) -> int:
    assert a >= 1
    return (a - 1).bit_length()


def base_parameters(L: int, eps: Fraction) -> tuple[int, int, int]:
    assert L >= 1 and 0 < eps < Fraction(1, 2)
    g = L.bit_length()
    h = 1
    while (2 * h) ** 2 * g <= L:
        h *= 2
    h = max(2, h)
    d = ceil_div(L, h - 1)
    cap = ceil_div(2 * h * (eps.numerator + eps.denominator), eps.numerator)
    return h, d, cap


def q_exponent(h: int, d: int, r: int) -> int:
    # q is the least power of two >=16h(2r+4)s, with s=2^d.
    return d + 5 + (h.bit_length() - 1) + ceil_log2(r + 2)


def passes(L: int, eps: Fraction, h: int, d: int, r: int) -> bool:
    lam = 1 - 2 * eps
    A, B = lam.numerator, lam.denominator
    k = q_exponent(h, d, r)
    j = h.bit_length() - 1
    shift = L + 10 + j + (h + 1 + r) * k
    margin = r * d * B - 7 * B - A * shift
    return margin >= pow(k, A).bit_length()


def select_r(L: int, eps: Fraction) -> tuple[int, int, int, int | None]:
    """First passing candidate in the exact bounded search, skipping q plateaus."""
    h, d, cap = base_parameters(L, eps)
    lam = 1 - 2 * eps
    A, B = lam.numerator, lam.denominator
    j = h.bit_length() - 1
    plateau = 2  # ceil(log2(r+2)) for the first candidates r=1,2.
    while True:
        lo = max(1, (1 << (plateau - 1)) - 1)
        hi = min(cap, (1 << plateau) - 2)
        if lo > cap:
            return h, d, cap, None
        k = d + 5 + j + plateau
        coefficient = d * B - A * k
        if coefficient <= 0:
            # Subsequent q exponents only increase, so they cannot work either.
            return h, d, cap, None
        threshold = (
            7 * B
            + A * (L + 10 + j + (h + 1) * k)
            + pow(k, A).bit_length()
        )
        candidate = max(lo, ceil_div(threshold, coefficient))
        if candidate <= hi:
            assert passes(L, eps, h, d, candidate)
            return h, d, cap, candidate
        plateau += 1


def direct_passes(L: int, eps: Fraction, h: int, d: int, r: int) -> bool:
    lam = 1 - 2 * eps
    A, B = lam.numerator, lam.denominator
    k = q_exponent(h, d, r)
    j = h.bit_length() - 1
    dbar = k << (L + 10 + j + (h + 1 + r) * k)
    return (1 << (r * d * B)) > (128**B) * (dbar**A)


def check_field_bounds(L: int, h: int, d: int, r: int) -> None:
    k = q_exponent(h, d, r)
    assert (h - 1) * d >= L
    # Inner: q >= 2(h-1)Delta.
    assert k - d >= ceil_log2(2 * (h - 1) * (2 * r + 4))
    # Outer: q^h >= 32h 2^L (2r+4)s > 2(n-1)Delta.
    assert h * k - L - d >= ceil_log2(32 * h * (2 * r + 4))
    assert h * k > L  # Q>N>=the number of source monomials.


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    direct_checks = 0
    for eps in [Fraction(1, 3), Fraction(1, 4), Fraction(1, 10)]:
        for L in range(1, 97):
            h, d, cap = base_parameters(L, eps)
            for r in range(1, min(cap, 16) + 1):
                assert passes(L, eps, h, d, r) == direct_passes(L, eps, h, d, r)
                direct_checks += 1

    exhaustive_search_checks = 0
    for eps in [Fraction(1, 3), Fraction(1, 4), Fraction(1, 10), Fraction(1, 100)]:
        for L in list(range(1, 257)) + [1024, 4096, 16384]:
            h, d, cap, chosen = select_r(L, eps)
            brute = next((r for r in range(1, cap + 1) if passes(L, eps, h, d, r)), None)
            assert chosen == brute
            exhaustive_search_checks += 1

    cases = []
    field_bound_checks = 0
    for eps in [Fraction(1, 3), Fraction(1, 4), Fraction(1, 10), Fraction(1, 100), Fraction(1, 1000)]:
        for L in [8, 16, 64, 256, 1024, 4096, 16384, 65536, 2**20, 2**24, 2**28, 2**36]:
            h, d, cap, chosen = select_r(L, eps)
            item = {"epsilon": str(eps), "log2_source_length_ceiling": L,
                    "h": h, "log2_s": d, "search_cap": cap, "r": chosen}
            if chosen is not None:
                check_field_bounds(L, h, d, chosen)
                field_bound_checks += 1
                k = q_exponent(h, d, chosen)
                shift = L + 10 + h.bit_length() - 1 + (h + 1 + chosen) * k
                rank_degree_upper = Fraction(shift + k.bit_length(), L)
                item.update({"log2_q": k,
                             "rank_degree_upper": str(rank_degree_upper),
                             "rank_degree_upper_display": float(rank_degree_upper),
                             "exact_gap_passes": True})
            cases.append(item)

    cutoff_checks = 0
    for eps in [Fraction(1, 3), Fraction(1, 4), Fraction(1, 10), Fraction(1, 100), Fraction(1, 1000)]:
        cutoff_fraction = (Fraction(256, 1) / eps) ** 4
        cutoff_integer = ceil_div(cutoff_fraction.numerator, cutoff_fraction.denominator)
        L0 = 1 << ceil_log2(cutoff_integer)
        for L in [L0, 2 * L0, 4 * L0]:
            h, d, cap = base_parameters(L, eps)
            assert passes(L, eps, h, d, cap)
            h2, d2, cap2, chosen = select_r(L, eps)
            assert (h, d, cap) == (h2, d2, cap2) and chosen is not None
            check_field_bounds(L, h, d, chosen)
            cutoff_checks += 1

    result = {
        "schema": "cvp.coded-fold-uniform-schedule.v1",
        "claim_scope": "Exact finite parameter arithmetic only; no compiler soundness proof is replaced.",
        "direct_integer_comparisons": direct_checks,
        "exhaustive_search_comparisons": exhaustive_search_checks,
        "selected_field_bound_checks": field_bound_checks,
        "conservative_cutoff_checks": cutoff_checks,
        "cases": cases,
    }
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    digest = hashlib.sha256(encoded.encode()).hexdigest()
    print(f"PASS: {result['schema']}")
    print(f"direct={direct_checks}, bounded_search={exhaustive_search_checks}, "
          f"field_bounds={field_bound_checks}, cutoffs={cutoff_checks}")
    print(digest)


if __name__ == "__main__":
    main()
