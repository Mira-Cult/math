#!/usr/bin/env python3
"""Exact controls for the source-derived polynomial cutoff improvements.

Canonical proof: ../manuscripts/polynomial_bound_transfer.md.
Q2 output is a sufficient existence bound, not a constructed array.
F2 output certifies only the exceptional-line subsystem resource invoice.
All theorem controls use integers/Fractions, never floating-point logarithms.
The small independent oracles use trial polynomial division and discriminants.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import combinations
import json
from math import factorial, isqrt


C1 = 113
C3 = 2_800_000
SOURCE_SCIENCE = "3ea1a0389c2165a71d5abedf6b4c036f8b9f0166"
SOURCE_AUXILIARY = "158baa7c6122abde0b0aee42abb502477c04088f"


def ceil_log2(value: int) -> int:
    if value < 1:
        raise ValueError("positive integer required")
    return (value - 1).bit_length()


def exp_partial(value: F, degree: int) -> F:
    """Positive Taylor partial sum, a rigorous lower bound for exp(value)."""
    if value < 0 or degree < 0:
        raise ValueError("nonnegative arguments required")
    return sum((value**j / factorial(j) for j in range(degree + 1)), F(0))


def universal_controls() -> dict[str, bool]:
    height = 1 << 15
    density_error = (
        F(4861, 6750)
        + (F(12151, 225) + 40 * 16) / height
        + F(16, height * height)
    )
    controls = {
        "prefix_density_at_least_13_over_16": density_error < F(3, 4),
        "residual_density_margin": F(2 * 256 + 1, 256**2) < F(1, 80),
        "dense_fiber_gap": F(1, 4) * F(1, 2) * F(1, 10)
        * F(1, 2) * F(4, 25) == F(1, 1000),
        "one_dimensional_integral_constant":
            F(4 * 22, 7) * F(256_000, 255) < C1**2,
        "max_norm_three_dimensional_integral_constant":
            F(2304 * 22, 7) * F(256_000, 255)**3 < C3**2,
        "exponential_remainder_constant": F(255, 1_024_000) > F(1, 4096),
        "root_constant_seven": 7**4 > 2**11,
        "log_two_below_seven_tenths": exp_partial(F(7, 10), 4) > 2,
        "log_three_below_eleven_tenths": exp_partial(F(11, 10), 5) > 3,
        "log_384_below_six": exp_partial(F(6), 12) > 384,
        "log_8704_below_ten": exp_partial(F(10), 10) > 8704,
        "binary_square_analytic_endpoint": 47**8 < 2**45 and 43**2 > 1800,
        "binary_higher_dimensional_endpoint": 11**2 < 2**7
        and 11**3 > 320 * F(7, 2),
    }
    if not all(controls.values()):
        raise AssertionError(controls)
    return controls


def cutoff_controls(dimension: int, exponent: int) -> dict[str, bool]:
    """The six conditions PQ-C at n=2**exponent, plus their domain."""
    if dimension < 2 or exponent < 0:
        raise ValueError("dimension >=2 and exponent >=0 required")
    d, x = dimension, exponent
    incidence = (3**d - 1) // 2
    t = F(7 * x + 11 * d + 60, 10)
    u = F(180 + 7 * (d + 3) * x, 15)
    a = F(783 + 91 * d * x, 30)
    power = 1 << x
    tail = 28 + F(11, 5) * d + (F(7, 2) + F(14, 15) * d) * x
    return {
        "monotonicity_and_sampling_domain": x >= 10,
        "canonical_height_at_least_two_to_fifteen": d * x >= 51,
        "actual_means_fit_window":
            (8 * a * a)**3 <= t**3 * (1 << ((2 * d - 3) * x)),
        "leading_coefficient_dominates_window": power >= 128 * t,
        "zero_constant_term_budget":
            (64 * 16 * C1 * incidence)**6 <= (1 << ((2 * d - 3) * x)),
        "nonzero_rational_root_budget":
            (1024 * C3 * incidence * u)**12 * t**15
            <= (1 << ((4 * d - 3) * x)),
        "fourier_exponential_budget": F(power, 4096) >= tail,
    }


def minimal_exponent(dimension: int) -> int:
    """Smallest integer exponent passing this sufficient controller.

    This does not assert the smallest valid existence cutoff. Monotonicity
    of these conditions on x>=10 is proved in the manuscript.
    """
    if dimension < 2:
        raise ValueError("dimension must be at least two")
    low = 10
    high = max(120, 24 + 2 * ceil_log2(dimension + 1))
    if not all(cutoff_controls(dimension, high).values()):
        raise AssertionError("proved uniform upper endpoint failed")
    while low < high:
        mid = (low + high) // 2
        if all(cutoff_controls(dimension, mid).values()):
            high = mid
        else:
            low = mid + 1
    return low


def q2_report(dimension: int) -> dict[str, object]:
    exponent = minimal_exponent(dimension)
    return {
        "dimension": dimension,
        "new_sufficient_cutoff": f"2^{exponent}",
        "previous_reviewed_sufficient_cutoff": f"2^{1024 * (dimension + 1)}",
        "controller_exponent": exponent,
        "controls": cutoff_controls(dimension, exponent),
        "predecessor_failed_conditions": [
            key for key, passed in cutoff_controls(dimension, exponent - 1).items()
            if not passed
        ],
        "conclusion": "all signed-line sums irreducible over Q; both order parities",
        "primitive_Z_conclusion": False,
        "efficient_constructor_claimed": False,
    }


def binary_shell(size: int) -> dict[str, int]:
    """Count full shells via 2**m=sum_{d|m} d*I(d), not Mobius inversion."""
    if size < 1:
        raise ValueError("positive prefix size required")
    counts = [0]
    total = 0
    degree = 0
    while total < size:
        degree += 1
        numerator = (1 << degree) - sum(
            d * counts[d] for d in range(1, degree) if degree % d == 0
        )
        if numerator % degree:
            raise AssertionError("shell count must be integral")
        counts.append(numerator // degree)
        previous = total
        total += counts[-1]
    return {
        "highest_degree": degree,
        "previous_complete_shell_total": previous,
        "complete_shell_total": total,
        "used_in_final_shell": size - previous,
        "affine_coset_order": 1 << (degree - 1),
    }


def binary_invoice(order: int, dimension: int) -> dict[str, object]:
    """Sufficient physical allocation invoice, never a full-array verifier."""
    if order < 1 or dimension < 2:
        raise ValueError("order positive and dimension >=2 required")
    n, d = order, dimension
    size = n**d
    shell = binary_shell(size)
    ambient = shell["affine_coset_order"]
    geometry = n >= max(5, 2 * d - 1) and n % 2 == 1
    if d == 2:
        k = 4 if n % 4 == 1 else 6
        core_budget = 15 if k == 4 else 40
        before_second_core = size - 2 - (2 * k - 1)
        remaining = size - 4 * n + 4
        padding_blocks = n - k - 1
        core = before_second_core > 0 and before_second_core**2 > core_budget * ambient
        padding = padding_blocks >= 0 and (
            padding_blocks == 0 or (remaining > 0 and remaining**2 > 6 * ambient)
        )
        arithmetic = core and padding
        details: dict[str, object] = {
            "core_size_parameter": k,
            "before_second_core": before_second_core,
            "core_square": before_second_core**2,
            "strict_core_requirement": core_budget * ambient,
            "zero_four_padding_blocks": padding_blocks,
            "remaining_after_all_allocations": remaining,
            "padding_square": remaining**2,
            "strict_padding_requirement_when_needed": 6 * ambient,
            "core_condition": core,
            "padding_condition": padding,
        }
    else:
        budget = 6 if n % 4 == 1 else 15
        remaining = size - 2 - 2 * d * (n - 1)
        arithmetic = remaining > 0 and remaining**2 > budget * ambient
        details = {
            "remaining_after_conservative_allocations": remaining,
            "remaining_square": remaining**2,
            "strict_requirement": budget * ambient,
            "zero_set_budget_constant": budget,
        }
    return {
        "order": n,
        "dimension": d,
        "pool_size": size,
        **shell,
        **details,
        "geometry_condition": geometry,
        "arithmetic_condition": arithmetic,
        "sufficient_subsystem_invoice_passes": geometry and arithmetic,
        "guaranteed_line_count": 2 * d,
        "full_array_asserted": False,
    }


def gf2_remainder(dividend: int, divisor: int) -> int:
    if divisor < 1:
        raise ValueError("positive polynomial divisor required")
    while dividend and dividend.bit_length() >= divisor.bit_length():
        dividend ^= divisor << (dividend.bit_length() - divisor.bit_length())
    return dividend


def trial_binary_irreducible(polynomial: int) -> bool:
    """Independent small oracle: try every monic potential proper factor."""
    degree = polynomial.bit_length() - 1
    if degree < 1:
        return False
    for d in range(1, degree // 2 + 1):
        for divisor in range(1 << d, 1 << (d + 1)):
            if gf2_remainder(polynomial, divisor) == 0:
                return False
    return True


def trial_binary_pool(size: int) -> list[int]:
    pool: list[int] = []
    candidate = 2
    while len(pool) < size:
        if trial_binary_irreducible(candidate):
            pool.append(candidate)
        candidate += 1
    return pool


def xor(values: tuple[int, ...]) -> int:
    result = 0
    for value in values:
        result ^= value
    return result


def independent_window_oracle() -> list[dict[str, int]]:
    """Count reducibles using integer discriminants, not factor enumeration."""
    results = []
    for s, amin, multiplier in [(8, 32, 2), (16, 64, 2), (36, 324, 3)]:
        maximum = amin + s
        assert s * s >= maximum and amin == s * multiplier * multiplier
        root_bound = F(2, multiplier)
        m = isqrt(maximum)
        harmonic = sum((F(1, u) for u in range(1, m + 1)), F(0))
        upper = root_bound * (4 * s * s * harmonic + 6 * s * m + m * (m + 1))
        count = 0
        tested = 0
        for a in range(amin, maximum + 1):
            for b in range(-s, s + 1):
                for c in range(-s, s + 1):
                    if c == 0:
                        continue
                    tested += 1
                    discriminant = b * b - 4 * a * c
                    count += discriminant >= 0 and isqrt(discriminant)**2 == discriminant
        assert count <= upper
        results.append({"s": s, "minimum_leading": amin,
                        "tested": tested, "nonzero_constant_reducibles": count,
                        "rational_bound_numerator": upper.numerator,
                        "rational_bound_denominator": upper.denominator})
    return results


def self_test() -> dict[str, object]:
    controls = universal_controls()
    expected = {2: 120, 3: 67, 4: 47, 5: 37, 6: 31, 10: 21, 100: 24, 1000: 27}
    for d, exponent in expected.items():
        assert minimal_exponent(d) == exponent
        assert all(cutoff_controls(d, exponent).values())
        assert not all(cutoff_controls(d, exponent - 1).values())
    for d in range(2, 101):
        exponent = minimal_exponent(d)
        for delta in (0, 1, 7):
            assert all(cutoff_controls(d, exponent + delta).values())
    square_cases = [binary_invoice(n, 2) for n in range(9, 47, 2)]
    small_higher = [binary_invoice(n, d) for n in (5, 7, 9)
                    for d in range(3, (n + 1) // 2 + 1)]
    assert all(row["sufficient_subsystem_invoice_passes"]
               for row in square_cases + small_higher)
    for n, d in [(3, 2), (5, 2), (7, 2), (4, 3), (5, 4)]:
        assert not binary_invoice(n, d)["sufficient_subsystem_invoice_passes"]
    # A failed sufficient invoice is not a nonexistence claim (5/7 squares exist).
    shell_oracle = []
    cumulative = 0
    for degree in range(1, 10):
        count = sum(trial_binary_irreducible(f)
                    for f in range(1 << degree, 1 << (degree + 1)))
        cumulative += count
        exact = binary_shell(cumulative)
        assert exact["highest_degree"] == degree
        assert exact["complete_shell_total"] == cumulative
        shell_oracle.append({"degree": degree, "count": count})
    conditional_oracle = []
    for n in (3, 5):
        pool = trial_binary_pool(n * n)
        assert pool[:2] == [2, 3]
        for f in pool[2:]:
            assert f & 1 and f.bit_count() % 2 == 1
        total = successes = 0
        for rest in combinations(pool[1:], n - 1):
            total += 1
            line_sum = 2 ^ xor(rest)
            success = trial_binary_irreducible(line_sum)
            if success:
                assert 3 not in rest and line_sum == 2
                successes += 1
        assert (len(pool) - 1) * successes <= total
        conditional_oracle.append({"order": n, "subsets_conditioned_on_X": total,
                                   "successful": successes})
    return {
        "universal_controls": controls,
        "q2_expected_exponents": expected,
        "q2_dimension_sweep": "2..100; accepted exponents and +1,+7",
        "binary_square_band": square_cases,
        "binary_small_higher_dimensional_cases": small_higher,
        "independent_shell_oracle": shell_oracle,
        "independent_conditional_oracle": conditional_oracle,
        "independent_nonzero_root_window_oracle": independent_window_oracle(),
        "status": "all exact controls and small independent oracles passed",
        "scope": "no large array generated; F2 invoices concern only exceptional lines",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    q2 = commands.add_parser("q2", help="derive sufficient Q2 cutoff exponents")
    q2.add_argument("--dimensions", nargs="+", type=int, default=[2, 3, 4, 5, 6, 10, 100, 1000])
    binary = commands.add_parser("f2", help="check one exceptional-subsystem invoice")
    binary.add_argument("--order", type=int, required=True)
    binary.add_argument("--dimension", type=int, default=2)
    commands.add_parser("test", help="run exact controls and independent tiny oracles")
    args = parser.parse_args()
    if args.command == "q2":
        result = {"universal_controls": universal_controls(),
                  "dimensions": [q2_report(d) for d in args.dimensions]}
    elif args.command == "f2":
        result = binary_invoice(args.order, args.dimension)
    else:
        result = self_test()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
