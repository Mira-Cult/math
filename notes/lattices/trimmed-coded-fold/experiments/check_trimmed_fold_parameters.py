#!/usr/bin/env python3
"""Exact finite arithmetic for CVP-M10's trimmed sampling schedule.

No large source instance, field, affine table, or lattice is instantiated.
The mathematical compiler proof and asymptotic analysis are separate.
Displayed degrees refer to virtual power-of-two source sizes N=2**L.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt
from pathlib import Path

from check_coded_fold_uniform_schedule import q_exponent, select_r


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def ceil_log2(a: int) -> int:
    assert a >= 1
    return (a - 1).bit_length()


def ceil_sqrt_ratio(numerator: int, denominator: int) -> int:
    """Least z>=0 with z*z*denominator>=numerator, using integers only."""
    assert numerator >= 0 and denominator > 0
    z = isqrt(numerator // denominator)
    return z + (z * z * denominator < numerator)


def base_parameters(L: int, eps: Fraction) -> tuple[int, int]:
    assert L >= 1 and 0 < eps < Fraction(1, 2)
    lam = 1 - 2 * eps
    G = L.bit_length()
    W = max(1, L // G).bit_length()
    constant_floor = 4 * lam / eps
    square = 2 * lam * L / (eps * W)
    r = max(
        2,
        ceil_div(constant_floor.numerator, constant_floor.denominator),
        ceil_sqrt_ratio(square.numerator, square.denominator),
    )
    return W, r


@dataclass(frozen=True)
class Trial:
    L: int
    r: int
    k: int
    h: int
    b: int

    @property
    def d(self) -> int:
        return self.k - self.b

    @property
    def rank_shift(self) -> int:
        return 2 * self.L + 14 + (self.r + 2) * self.k

    @property
    def rank_bits_upper(self) -> int:
        return self.rank_shift + (self.h * self.k).bit_length()


def trial_parameters(L: int, r: int, k: int) -> Trial:
    assert L >= 1 and r >= 1 and 1 <= k <= L
    h = 1 << ceil_log2(max(2, ceil_div(L + 4, k) + 1))
    b = ceil_log2(4 * (h - 1) * (r + 2))
    return Trial(L, r, k, h, b)


def exact_margin(trial: Trial, eps: Fraction) -> int:
    lam = 1 - 2 * eps
    A, B = lam.numerator, lam.denominator
    coefficient = trial.r * (B - A) - 2 * A
    threshold = (
        7 * B
        + A * (2 * trial.L + 14)
        + trial.r * B * trial.b
        + pow(trial.h * trial.k, A).bit_length()
    )
    return coefficient * trial.k - threshold


def passes(trial: Trial, eps: Fraction) -> bool:
    return trial.d >= 1 and exact_margin(trial, eps) >= 0


def select_parameters(L: int, eps: Fraction) -> tuple[int, int, Trial | None]:
    W, r = base_parameters(L, eps)
    if not passes(trial_parameters(L, r, L), eps):
        return W, r, None
    lo, hi = 1, L
    while lo < hi:
        mid = (lo + hi) // 2
        if passes(trial_parameters(L, r, mid), eps):
            hi = mid
        else:
            lo = mid + 1
    result = trial_parameters(L, r, lo)
    assert passes(result, eps)
    return W, r, result


def direct_passes(trial: Trial, eps: Fraction) -> bool:
    if trial.d < 1:
        return False
    lam = 1 - 2 * eps
    A, B = lam.numerator, lam.denominator
    dstar = (trial.h * trial.k) << trial.rank_shift
    return (1 << (trial.r * trial.d * B)) > 128**B * dstar**A


def check_field_bounds(trial: Trial) -> None:
    """Symbolic exponent checks; suitable for arbitrarily large virtual L."""
    assert trial.d >= 1
    assert trial.h >= 2 and trial.h & (trial.h - 1) == 0
    assert (trial.h - 1) * trial.k >= trial.L + 4
    assert 4 * (trial.h - 1) * (trial.r + 2) <= 1 << trial.b
    # These are exactly T<=q and q**(h-1)>=8ell; R<8ell*q follows from h>=2.


def check_direct_rank_and_gap(trial: Trial, eps: Fraction) -> None:
    """Instantiate integer sizes only, not any field or matrix."""
    ell = 1 << (trial.L + 1)
    q, s = 1 << trial.k, 1 << trial.d
    n = 4 * trial.h * ell
    delta = (2 * trial.r + 4) * s
    T, R = 2 * (trial.h - 1) * delta, 2 * (n - 1) * delta
    assert T <= q and R < q**trial.h and (1 << trial.L) < q**trial.h
    C = 16 * trial.h * ell * trial.k
    m_code = ceil_log2(2 * C)
    M = 16 * ceil_div(C, m_code) * m_code
    assert C <= M <= 32 * C
    D = M * R * T * q**trial.r
    Dstar = (trial.h * trial.k) << trial.rank_shift
    assert D <= Dstar
    K = s**trial.r
    lam = 1 - 2 * eps
    assert K**lam.denominator > 128**lam.denominator * D**lam.numerator
    rho = isqrt(M * R * T - 1) + 1
    assert M * R * T <= rho**2 <= 4 * M * R * T


def check_pointwise_saving(L: int, h: int, d: int, r: int) -> None:
    """Exact old-grid/new-grid ratio at identical parameters, with M canceled."""
    k = q_exponent(h, d, r)
    q, s = 1 << k, 1 << d
    ell = 1 << (L + 1)
    n = 4 * h * ell
    delta = (2 * r + 4) * s
    T, R = 2 * (h - 1) * delta, 2 * (n - 1) * delta
    assert T <= q and R <= q**h
    assert q ** (h + 1) > T * R * 4 * (16 * h * (2 * r + 4)) ** (h - 1)


def comparison_case(L: int, eps: Fraction) -> dict:
    W, r, selected = select_parameters(L, eps)
    item = {
        "epsilon": str(eps),
        "virtual_log2_source_size": L,
        "W": W,
        "r": r,
        "trimmed_search_succeeded": selected is not None,
    }
    if selected is not None:
        check_field_bounds(selected)
        degree = Fraction(selected.rank_bits_upper, L)
        item["optimized_trimmed"] = {
            "h": selected.h,
            "log2_q": selected.k,
            "log2_s": selected.d,
            "radix_loss_bits": selected.b,
            "log2_K": selected.r * selected.d,
            "log2_rank_upper": selected.rank_bits_upper,
            "rank_degree_upper": str(degree),
            "rank_degree_upper_display": float(degree),
            "exact_gap_margin_integer": exact_margin(selected, eps),
        }
    old_h, old_d, old_cap, old_r = select_r(L, eps)
    item["old_search_succeeded"] = old_r is not None
    if old_r is not None:
        old_k = q_exponent(old_h, old_d, old_r)
        # C=hk 2**(L+5), so C<=M<=32C supplies a five-bit interval.
        old_shift = L + 10 + (old_h + 1 + old_r) * old_k
        old_upper = old_shift + (old_h * old_k).bit_length()
        old_lower = old_shift - 5 + (old_h * old_k).bit_length() - 1
        # n/2<=n-1<n gives these independent same-parameter trimmed bounds.
        poly_factor = old_h**2 * old_k * (old_h - 1) * (old_r + 2) ** 2
        trim_shift = 2 * L + 17 + 2 * old_d + old_r * old_k
        trim_upper = trim_shift + poly_factor.bit_length()
        trim_lower = trim_shift - 6 + poly_factor.bit_length() - 1
        base = 16 * old_h * (2 * old_r + 4)
        pointwise_saving_bits = 2 + (old_h - 1) * (base.bit_length() - 1)
        item["old_full_grid"] = {
            "h": old_h,
            "r": old_r,
            "search_cap": old_cap,
            "log2_q": old_k,
            "log2_s": old_d,
            "log2_rank_upper": old_upper,
            "rank_degree_upper_display": float(Fraction(old_upper, L)),
        }
        item["trimmed_at_identical_old_parameters"] = {
            "log2_rank_upper": trim_upper,
            "rank_degree_upper_display": float(Fraction(trim_upper, L)),
            "pointwise_log2_rank_saving_lower": pointwise_saving_bits,
        }
        if selected is not None:
            item["optimized_vs_old_full_log2_rank_saving_lower"] = (
                old_lower - selected.rank_bits_upper
            )
            item["optimized_vs_old_trimmed_log2_rank_saving_lower"] = (
                trim_lower - selected.rank_bits_upper
            )
    return item


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    direct_checks = 0
    for eps in [Fraction(1, 3), Fraction(1, 4), Fraction(1, 10)]:
        for L in range(1, 97):
            _, r = base_parameters(L, eps)
            for k in sorted({1, max(1, L // 3), max(1, 2 * L // 3), L}):
                trial = trial_parameters(L, r, k)
                assert passes(trial, eps) == direct_passes(trial, eps)
                direct_checks += 1

    search_checks = 0
    monotonic_steps = 0
    direct_rank_checks = 0
    for eps in [Fraction(1, 3), Fraction(1, 4), Fraction(1, 10),
                Fraction(1, 100), Fraction(49, 100)]:
        for L in list(range(1, 257)) + [512, 1024, 4096]:
            _, r, selected = select_parameters(L, eps)
            trials = [trial_parameters(L, r, k) for k in range(1, L + 1)]
            brute = next((trial for trial in trials if passes(trial, eps)), None)
            assert selected == brute
            last_margin = None
            last_pass = False
            lam = 1 - 2 * eps
            for trial in trials:
                margin = exact_margin(trial, eps)
                if last_margin is not None:
                    assert margin - last_margin >= 5 * lam.numerator
                    monotonic_steps += 1
                now_pass = passes(trial, eps)
                assert not last_pass or now_pass
                last_margin, last_pass = margin, now_pass
            search_checks += 1
            if selected is not None and L <= 128:
                check_field_bounds(selected)
                check_direct_rank_and_gap(selected, eps)
                direct_rank_checks += 1

    pointwise_checks = 0
    for L in [3, 8, 16, 32, 64, 128]:
        for h in [2, 4, 8, 16, 64]:
            d = max(1, ceil_div(L, h - 1))
            for r in [1, h, 3 * h + 1]:
                check_pointwise_saving(L, h, d, r)
                pointwise_checks += 1
    example_bound = 4 * (16 * 64 * (2 * 513 + 4)) ** 63
    assert example_bound > 10**380

    cutoff_checks = 0
    for eps in [Fraction(1, 3), Fraction(1, 4), Fraction(1, 10),
                Fraction(1, 100), Fraction(1, 1000), Fraction(49, 100)]:
        cutoff = (Fraction(256) / eps) ** 4
        L0 = 1 << ceil_log2(ceil_div(cutoff.numerator, cutoff.denominator))
        for L in [L0, 2 * L0, 4 * L0]:
            _, r, selected = select_parameters(L, eps)
            assert selected is not None
            assert passes(trial_parameters(L, r, L), eps)
            check_field_bounds(selected)
            cutoff_checks += 1

    cases = []
    for eps in [Fraction(1, 3), Fraction(1, 4), Fraction(1, 10),
                Fraction(1, 100), Fraction(1, 1000), Fraction(49, 100)]:
        for L in [8, 16, 64, 256, 1024, 4096, 16384, 65536,
                  2**20, 2**24, 2**28, 2**36]:
            cases.append(comparison_case(L, eps))

    result = {
        "schema": "cvp.trimmed-fold-parameters.v1",
        "claim_scope": "Exact finite arithmetic only; no soundness/asymptotic proof is replaced.",
        "display_convention": "Rank degrees use virtual power-of-two source sizes N=2^L.",
        "direct_integer_comparisons": direct_checks,
        "exhaustive_search_comparisons": search_checks,
        "monotonic_margin_steps": monotonic_steps,
        "direct_field_rank_gap_checks": direct_rank_checks,
        "pointwise_grid_saving_checks": pointwise_checks,
        "conservative_cutoff_checks": cutoff_checks,
        "h64_r513_pointwise_saving_lower_exact": str(example_bound),
        "h64_r513_pointwise_saving_exceeds_10_to_380": True,
        "cases": cases,
    }
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(f"PASS: {result['schema']}")
    print(f"direct={direct_checks}, searches={search_checks}, "
          f"monotonic_steps={monotonic_steps}, direct_rank={direct_rank_checks}, "
          f"savings={pointwise_checks}, cutoffs={cutoff_checks}")
    print(hashlib.sha256(encoded.encode()).hexdigest())


if __name__ == "__main__":
    main()
